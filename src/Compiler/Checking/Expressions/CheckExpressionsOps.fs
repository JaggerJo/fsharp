// Copyright (c) Microsoft Corporation. All Rights Reserved. See License.txt in the project root for license information.

module internal FSharp.Compiler.CheckExpressionsOps

open Internal.Utilities.Collections
open Internal.Utilities.Library
open Internal.Utilities.Library.Extras
open FSharp.Compiler.CheckBasics
open FSharp.Compiler.ConstraintSolver
open FSharp.Compiler.DiagnosticsLogger
open FSharp.Compiler.Features
open FSharp.Compiler.NameResolution
open FSharp.Compiler.PatternMatchCompilation
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Range
open FSharp.Compiler.Syntax
open FSharp.Compiler.TypedTree
open FSharp.Compiler.TypedTreeBasics
open FSharp.Compiler.TypedTreeOps
open FSharp.Compiler.SyntaxTreeOps

let TryAllowFlexibleNullnessInControlFlow isFirst (g: TcGlobals.TcGlobals) ty =
    match isFirst, g.checkNullness, GetTyparTyIfSupportsNull g ty with
    | true, true, ValueSome tp -> tp.SetSupportsNullFlex(true)
    | _ -> ()

let CopyAndFixupTypars g traitCtxt m rigid tpsorig =
    FreshenAndFixupTypars g traitCtxt m rigid [] [] tpsorig

let FreshenPossibleForallTy g traitCtxt m rigid ty =
    let origTypars, tau = tryDestForallTy g ty

    if isNil origTypars then
        [], [], [], tau
    else
        // tps may be have been equated to other tps in equi-recursive type inference and units-of-measure type inference. Normalize them here
        let origTypars = NormalizeDeclaredTyparsForEquiRecursiveInference g origTypars
        let tps, renaming, tinst = CopyAndFixupTypars g traitCtxt m rigid origTypars
        origTypars, tps, tinst, instType renaming tau

/// simplified version of TcVal used in calls to BuildMethodCall (typrelns.fs)
/// this function is used on typechecking step for making calls to provided methods and on optimization step (for the same purpose).
let LightweightTcValForUsingInBuildMethodCall g traitCtxt (vref: ValRef) vrefFlags (vrefTypeInst: TTypes) m =
    let v = vref.Deref
    let vTy = vref.Type
    // byref-typed values get dereferenced
    if isByrefTy g vTy then
        mkAddrGet m vref, destByrefTy g vTy
    else
        match v.LiteralValue with
        | Some literalConst ->
            let _, _, _, tau = FreshenPossibleForallTy g traitCtxt m TyparRigidity.Flexible vTy
            Expr.Const(literalConst, m, tau), tau

        | None ->
            // Instantiate the value
            let tau =
                // If we have got an explicit instantiation then use that
                let _, tps, tpTys, tau =
                    FreshenPossibleForallTy g traitCtxt m TyparRigidity.Flexible vTy

                if tpTys.Length <> vrefTypeInst.Length then
                    error (Error(FSComp.SR.tcTypeParameterArityMismatch (tps.Length, vrefTypeInst.Length), m))

                instType (mkTyparInst tps vrefTypeInst) tau

            let exprForVal = Expr.Val(vref, vrefFlags, m)
            let exprForVal = mkTyAppExpr m (exprForVal, vTy) vrefTypeInst
            exprForVal, tau

//-------------------------------------------------------------------------
// Helpers dealing with pattern match compilation
//-------------------------------------------------------------------------

let CompilePatternForMatch
    (cenv: TcFileState)
    (env: TcEnv)
    mExpr
    mMatch
    warnOnUnused
    actionOnFailure
    (inputVal, generalizedTypars, inputExprOpt)
    clauses
    inputTy
    resultTy
    =
    let g = cenv.g

    let dtree, targets, joins =
        CompilePattern
            g
            env.DisplayEnv
            cenv.amap
            (LightweightTcValForUsingInBuildMethodCall g env.TraitContext)
            cenv.infoReader
            mExpr
            mMatch
            warnOnUnused
            actionOnFailure
            (inputVal, generalizedTypars, inputExprOpt)
            clauses
            inputTy
            resultTy

    mkAndSimplifyMatch DebugPointAtBinding.NoneAtInvisible mExpr mMatch resultTy dtree targets
    |> mkLetsBind mMatch joins

/// Invoke pattern match compilation
let CompilePatternForMatchClauses (cenv: TcFileState) env mExpr mMatch warnOnUnused actionOnFailure inputExprOpt inputTy resultTy tclauses =
    // Avoid creating a dummy in the common cases where we are about to bind a name for the expression
    // CLEANUP: avoid code duplication with code further below, i.e.all callers should call CompilePatternForMatch
    match tclauses with
    | [ MatchClause(TPat_as(pat1, PatternValBinding(asVal, GeneralizedType(generalizedTypars, _)), _), None, TTarget(vs, targetExpr, _), m2) ] ->
        let vs2 = ListSet.remove valEq asVal vs

        let expr =
            CompilePatternForMatch
                cenv
                env
                mExpr
                mMatch
                warnOnUnused
                actionOnFailure
                (asVal, generalizedTypars, None)
                [ MatchClause(pat1, None, TTarget(vs2, targetExpr, None), m2) ]
                inputTy
                resultTy

        asVal, expr
    | _ ->
        let matchValueTmp, _ = mkCompGenLocal mExpr "matchValue" inputTy

        let expr =
            CompilePatternForMatch
                cenv
                env
                mExpr
                mMatch
                warnOnUnused
                actionOnFailure
                (matchValueTmp, [], inputExprOpt)
                tclauses
                inputTy
                resultTy

        matchValueTmp, expr

/// Constrain two types to be equal within this type checking context
let inline UnifyTypes (cenv: TcFileState) (env: TcEnv) m expectedTy actualTy =

    AddCxTypeEqualsType
        env.eContextInfo
        env.DisplayEnv
        cenv.css
        m
        (tryNormalizeMeasureInType cenv.g expectedTy)
        (tryNormalizeMeasureInType cenv.g actualTy)

// Converts 'a..b' to a call to the '(..)' operator in FSharp.Core
// Converts 'a..b..c' to a call to the '(.. ..)' operator in FSharp.Core
//
// NOTE: we could eliminate these more efficiently in LowerComputedCollections.fs, since
//    [| 1..4 |]
// becomes [| for i in (..) 1 4 do yield i |]
// instead of generating the array directly from the ranges
let RewriteRangeExpr synExpr =
    match synExpr with
    // a..b..c (parsed as (a..b)..c )
    | SynExpr.IndexRange(Some(SynExpr.IndexRange(Some synExpr1, _, Some synStepExpr, _, _, _)), _, Some synExpr2, _m1, _m2, mWhole) ->
        let mWhole = mWhole.MakeSynthetic()
        Some(mkSynTrifix mWhole ".. .." synExpr1 synStepExpr synExpr2)
    // a..b
    | SynExpr.IndexRange(Some synExpr1, mOperator, Some synExpr2, _m1, _m2, mWhole) ->
        let otherExpr =
            let mWhole = mWhole.MakeSynthetic()

            match mkSynInfix mOperator synExpr1 ".." synExpr2 with
            | SynExpr.App(a, b, c, d, _) -> SynExpr.App(a, b, c, d, mWhole)
            | _ -> failwith "impossible"

        Some otherExpr
    | _ -> None

/// Check if a computation or sequence expression is syntactically free of 'yield' (though not yield!)
let YieldFree (_cenv: TcFileState) expr =
    let rec YieldFree expr =
        match expr with
        | SynExpr.Sequential(expr1 = expr1; expr2 = expr2) -> YieldFree expr1 && YieldFree expr2

        | SynExpr.IfThenElse(thenExpr = thenExpr; elseExpr = elseExprOpt) -> YieldFree thenExpr && Option.forall YieldFree elseExprOpt

        | SynExpr.TryWith(tryExpr = body; withCases = clauses) ->
            YieldFree body
            && clauses |> List.forall (fun (SynMatchClause(resultExpr = res)) -> YieldFree res)

        | SynExpr.Match(clauses = clauses)
        | SynExpr.MatchBang(clauses = clauses) -> clauses |> List.forall (fun (SynMatchClause(resultExpr = res)) -> YieldFree res)

        | SynExpr.For(doBody = body)
        | SynExpr.TryFinally(tryExpr = body)
        | SynExpr.LetOrUse({ Body = body })
        | SynExpr.While(doExpr = body)
        | SynExpr.WhileBang(doExpr = body)
        | SynExpr.ForEach(bodyExpr = body) -> YieldFree body
        | SynExpr.YieldOrReturn(flags = (true, _)) -> false

        | _ -> true

    YieldFree expr

let inline IsSimpleSemicolonSequenceElement expr cenv acceptDeprecated =
    match expr with
    | SynExpr.IfThenElse _ when acceptDeprecated && YieldFree cenv expr -> true
    | SynExpr.IfThenElse _
    | SynExpr.TryWith _
    | SynExpr.Match _
    | SynExpr.For _
    | SynExpr.ForEach _
    | SynExpr.TryFinally _
    | SynExpr.YieldOrReturnFrom _
    | SynExpr.YieldOrReturn _
    | SynExpr.LetOrUse _
    | SynExpr.Do _
    | SynExpr.MatchBang _
    | SynExpr.While _
    | SynExpr.WhileBang _ -> false
    | _ -> true

[<TailCall>]
let rec TryGetSimpleSemicolonSequenceOfComprehension expr acc cenv acceptDeprecated =
    match expr with
    | SynExpr.Sequential(isTrueSeq = true; expr1 = e1; expr2 = e2) ->
        if IsSimpleSemicolonSequenceElement e1 cenv acceptDeprecated then
            TryGetSimpleSemicolonSequenceOfComprehension e2 (e1 :: acc) cenv acceptDeprecated
        else
            ValueNone
    | _ ->
        if IsSimpleSemicolonSequenceElement expr cenv acceptDeprecated then
            ValueSome(List.rev (expr :: acc))
        else
            ValueNone

/// Determine if a syntactic expression inside 'seq { ... }' or '[...]' counts as a "simple sequence
/// of semicolon separated values". For example [1;2;3].
/// 'acceptDeprecated' is true for the '[ ... ]' case, where we allow the syntax '[ if g then t else e ]' but ask it to be parenthesized
[<return: Struct>]
let (|SimpleSemicolonSequence|_|) cenv acceptDeprecated cexpr =
    TryGetSimpleSemicolonSequenceOfComprehension cexpr [] cenv acceptDeprecated

let elimFastIntegerForLoop (spFor, spTo, id, start: SynExpr, dir, finish: SynExpr, innerExpr, m: range) =
    let mOp = (unionRanges start.Range finish.Range).MakeSynthetic()

    let pseudoEnumExpr =
        if dir then
            mkSynInfix mOp start ".." finish
        else
            mkSynTrifix mOp ".. .." start (SynExpr.Const(SynConst.Int32 -1, mOp)) finish

    SynExpr.ForEach(spFor, spTo, SeqExprOnly false, true, mkSynPatVar None id, pseudoEnumExpr, innerExpr, m)

let mkSeqEmpty (cenv: TcFileState) env m genTy =
    // We must discover the 'zero' of the monadic algebra being generated in order to compile failing matches.
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy g genResultTy)
    mkCallSeqEmpty g m genResultTy

let mkSeqUsing (cenv: TcFileState) (env: TcEnv) m resourceTy genTy resourceExpr lam =
    let g = cenv.g
    AddCxTypeMustSubsumeType ContextInfo.NoContext env.DisplayEnv cenv.css m NoTrace g.system_IDisposableNull_ty resourceTy
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)
    mkCallSeqUsing cenv.g m resourceTy genResultTy resourceExpr lam

let mkSeqAppend (cenv: TcFileState) env m genTy e1 e2 =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)

    let e1 =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g genResultTy) (tyOfExpr cenv.g e1) e1

    let e2 =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g genResultTy) (tyOfExpr cenv.g e2) e2

    mkCallSeqAppend cenv.g m genResultTy e1 e2

let mkSeqDelay (cenv: TcFileState) env m genTy lam =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)
    mkCallSeqDelay cenv.g m genResultTy (mkUnitDelayLambda cenv.g m lam)

let mkSeqCollect (cenv: TcFileState) env m enumElemTy genTy lam enumExpr =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)

    let enumExpr =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g enumElemTy) (tyOfExpr cenv.g enumExpr) enumExpr

    mkCallSeqCollect cenv.g m enumElemTy genResultTy lam enumExpr

let mkSeqFromFunctions (cenv: TcFileState) env m genTy e1 e2 =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)

    let e2 =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g genResultTy) (tyOfExpr cenv.g e2) e2

    mkCallSeqGenerated cenv.g m genResultTy e1 e2

let mkSeqFinally (cenv: TcFileState) env m genTy e1 e2 =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)

    let e1 =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g genResultTy) (tyOfExpr cenv.g e1) e1

    mkCallSeqFinally cenv.g m genResultTy e1 e2

let mkSeqTryWith (cenv: TcFileState) env m genTy origSeq exnFilter exnHandler =
    let g = cenv.g
    let genResultTy = NewInferenceType g
    UnifyTypes cenv env m genTy (mkSeqTy cenv.g genResultTy)

    let origSeq =
        mkCoerceIfNeeded cenv.g (mkSeqTy cenv.g genResultTy) (tyOfExpr cenv.g origSeq) origSeq

    mkCallSeqTryWith cenv.g m genResultTy origSeq exnFilter exnHandler

let inline mkSeqExprMatchClauses (pat, vspecs) innerExpr =
    [ MatchClause(pat, None, TTarget(vspecs, innerExpr, None), pat.Range) ]

let compileSeqExprMatchClauses (cenv: TcFileState) env inputExprMark (pat: Pattern, vspecs) innerExpr inputExprOpt bindPatTy genInnerTy =
    let patMark = pat.Range
    let tclauses = mkSeqExprMatchClauses (pat, vspecs) innerExpr

    CompilePatternForMatchClauses
        cenv
        env
        inputExprMark
        patMark
        false
        ThrowIncompleteMatchException
        inputExprOpt
        bindPatTy
        genInnerTy
        tclauses

let inline mkOptionalParamTyBasedOnAttribute (g: TcGlobals.TcGlobals) tyarg attribs =
    if
        g.langVersion.SupportsFeature(LanguageFeature.SupportValueOptionsAsOptionalParameters)
        && findSynAttribute "StructAttribute" attribs
    then
        mkValueOptionTy g tyarg
    else
        mkOptionTy g tyarg

//-------------------------------------------------------------------------
// Struct byref capture fix for object expressions
//-------------------------------------------------------------------------

/// When a struct instance method creates an object expression that captures constructor
/// parameters, those captures go through 'this' which is a byref. This would create
/// illegal byref fields in the closure class. This function detects such captures and
/// extracts them to local bindings before the object expression.
///
/// Returns: (shouldTransform, structCaptures, methodParamStamps)
let AnalyzeObjExprStructCaptures
    (enclosingStructTyconRefOpt: TyconRef option)
    (ctorCall: Expr)
    (overrides: ObjExprMethod list)
    (extraImpls: (TType * ObjExprMethod list) list)
    : bool * Val list * Set<Stamp> =

    // Collect free variables from an expression
    let collectFreeVars expr =
        (freeInExpr CollectLocals expr).FreeLocals |> Zset.elements

    // Collect all method parameters (bound variables) from object expression methods
    // These should NOT be treated as struct instance captures
    let methodParams =
        [
            for TObjExprMethod(_, _, _, paramGroups, _, _) in overrides do
                for paramGroup in paramGroups do
                    for v in paramGroup do
                        yield v
            for (_, methods) in extraImpls do
                for TObjExprMethod(_, _, _, paramGroups, _, _) in methods do
                    for paramGroup in paramGroups do
                        for v in paramGroup do
                            yield v
        ]
        |> List.map (fun v -> v.Stamp)
        |> Set.ofList

    let allFreeVars =
        [
            yield! collectFreeVars ctorCall
            for TObjExprMethod(_, _, _, _, body, _) in overrides do
                yield! collectFreeVars body
            for (_, methods) in extraImpls do
                for TObjExprMethod(_, _, _, _, body, _) in methods do
                    yield! collectFreeVars body
        ]
        |> List.distinctBy (fun v -> v.Stamp)

    // Filter to struct instance captures:
    // - We're in a struct context (enclosingStructTyconRefOpt is Some)
    // - The value is NOT a method parameter of the object expression
    // - The value is NOT a module binding
    // - The value is NOT a member or module binding (excludes property getters, etc.)
    // - The value is NOT a constructor
    let structCaptures =
        match enclosingStructTyconRefOpt with
        | None -> []
        | Some _ ->
            allFreeVars
            |> List.filter (fun v ->
                not v.IsModuleBinding
                && not v.IsMemberOrModuleBinding
                && not (Set.contains v.Stamp methodParams)
                && v.LogicalName <> ".ctor")

    let shouldTransform = not (List.isEmpty structCaptures)
    (shouldTransform, structCaptures, methodParams)

/// Transform an object expression to avoid byref captures from struct instance state.
/// Creates local bindings for captured values and remaps references in the object expression.
let TransformObjExprForStructByrefCaptures
    (g: TcGlobals.TcGlobals)
    (mWholeExpr: Text.range)
    (structCaptures: Val list)
    (objtyR: TType)
    (baseValOpt: Val option)
    (ctorCall: Expr)
    (overrides: ObjExprMethod list)
    (extraImpls: (TType * ObjExprMethod list) list)
    (realObjTy: TType)
    : Expr =

    // Create local bindings for each captured value to avoid byref captures
    let localBindings =
        structCaptures
        |> List.map (fun v ->
            let local, _localExpr =
                mkCompGenLocal mWholeExpr (v.LogicalName + "$captured") v.Type

            let readExpr = exprForVal mWholeExpr v
            (v, local, readExpr))

    // Build remap: original val -> local val
    let remap =
        localBindings
        |> List.fold
            (fun (r: Remap) (orig, local, _) ->
                { r with
                    valRemap = r.valRemap.Add orig (mkLocalValRef local)
                })
            Remap.Empty

    // Helper to remap an object expression method
    let remapMethod (TObjExprMethod(slotSig, attrs, mtps, paramGroups, body, range)) =
        TObjExprMethod(slotSig, attrs, mtps, paramGroups, remapExpr g CloneAll remap body, range)

    // Remap all parts of the object expression
    let ctorCall' = remapExpr g CloneAll remap ctorCall
    let overrides' = overrides |> List.map remapMethod

    let extraImpls' =
        extraImpls |> List.map (fun (ty, ms) -> (ty, ms |> List.map remapMethod))

    // Build the object expression with remapped references
    let objExpr =
        mkObjExpr (objtyR, baseValOpt, ctorCall', overrides', extraImpls', mWholeExpr)

    let objExpr = mkCoerceIfNeeded g realObjTy objtyR objExpr

    // Wrap with let bindings: let x$captured = x in ...
    localBindings
    |> List.foldBack (fun (_, local, valueExpr) body -> mkLet DebugPointAtBinding.NoneAtInvisible mWholeExpr local valueExpr body)
    <| objExpr

//-------------------------------------------------------------------------
// Polymorphic variants (experimental)
//
// Every polymorphic variant value is represented at runtime by 'polyVariantReprTy', the tag paired with
// the boxed payload. A tag pattern becomes a synthesized partial active pattern over that representation.
// Once all clauses of a match are checked, each position the match tests tags at is either open - some
// unguarded clause has a wildcard there, so the scrutinee must carry at least the tags tested - or closed,
// so it carries at most those tags. The tag patterns at a closed position are fused into one total
// active pattern, which lets the match compiler see that the match is complete.
//-------------------------------------------------------------------------

/// Marks the name of a synthesized active pattern case that tests a polymorphic variant tag
let private polyVariantCaseName (tag: string) = "`" + tag

/// Reinterpret a reference to another reference type, emitting no code
let private mkPolyVariantRetype (e: Expr) ty m = mkAsmExpr ([], [], [ e ], [ ty ], m)

let private mkPolyVariantBox (g: TcGlobals.TcGlobals) payloadTy e m =
    mkAsmExpr ([ AbstractIL.IL.I_box(AbstractIL.IL.mkILTyvarTy 0us) ], [ payloadTy ], [ e ], [ g.obj_ty_noNulls ], m)

let private mkPolyVariantUnbox payloadTy e m =
    mkAsmExpr ([ AbstractIL.IL.I_unbox_any(AbstractIL.IL.mkILTyvarTy 0us) ], [ payloadTy ], [ e ], [ payloadTy ], m)

let mkPolyVariantConstruction (g: TcGlobals.TcGlobals) m variantTy tag payloadTy payloadExpr =
    let reprExpr =
        mkRefTupled g m [ mkString g m tag; mkPolyVariantBox g payloadTy payloadExpr m ] [ g.string_ty; g.obj_ty_noNulls ]

    mkPolyVariantRetype reprExpr variantTy m

/// Build 'fun (v: variantTy) -> body v tagExpr payloadExpr' where the last two read the tag and the boxed payload of v
let private mkPolyVariantDestructor (g: TcGlobals.TcGlobals) m variantTy bodyTy body =
    let reprTy = polyVariantReprTy g
    let v, vExpr = mkCompGenLocal m "variant" variantTy
    let r, rExpr = mkCompGenLocal m "repr" reprTy
    let tupInfo = TupInfo.Const false

    let tagExpr =
        mkTupleFieldGet g (tupInfo, rExpr, [ g.string_ty; g.obj_ty_noNulls ], 0, m)

    let payloadExpr =
        mkTupleFieldGet g (tupInfo, rExpr, [ g.string_ty; g.obj_ty_noNulls ], 1, m)

    let bodyExpr =
        mkCompGenLet m r (mkPolyVariantRetype vExpr reprTy m) (body vExpr tagExpr payloadExpr)

    mkLambda m v (bodyExpr, bodyTy)

let private mkTagTest (g: TcGlobals.TcGlobals) m tagExpr tag =
    mkCallEqualsOperator g m g.string_ty tagExpr (mkString g m tag)

let mkPolyVariantTagPattern (g: TcGlobals.TcGlobals) m variantTy tag payloadTy subPat =
    let resTy = mkOptionTy g payloadTy

    let apExpr =
        mkPolyVariantDestructor g m variantTy resTy (fun _ tagExpr payloadExpr ->
            mkCond
                DebugPointAtBinding.NoneAtInvisible
                m
                resTy
                (mkTagTest g m tagExpr tag)
                (mkSome g payloadTy (mkPolyVariantUnbox payloadTy payloadExpr m) m)
                (mkNone g payloadTy m))

    let apinfo = PrettyNaming.APInfo(false, [ polyVariantCaseName tag, m ], m)
    TPat_query((apExpr, [ payloadTy ], ActivePatternReturnKind.RefTypeWrapper, None, 0, apinfo), subPat, m)

/// The pattern #T subPat: any tag of the exact variant type T, with subPat matching the value at T
let mkPolyVariantTypePattern (g: TcGlobals.TcGlobals) m scrutTy variantTy subPat =
    let tags =
        match tryDestPolyVariantTy g variantTy with
        | ValueSome(struct (tags, _)) -> tags
        | ValueNone -> []

    let resTy = mkOptionTy g variantTy

    let apExpr =
        mkPolyVariantDestructor g m scrutTy resTy (fun vExpr tagExpr _ ->
            let isTagOfType =
                match tags with
                | [] -> mkFalse g m
                | _ -> tags |> List.map (mkTagTest g m tagExpr) |> List.reduce (mkLazyOr g m)

            mkCond
                DebugPointAtBinding.NoneAtInvisible
                m
                resTy
                isTagOfType
                (mkSome g variantTy (mkPolyVariantRetype vExpr variantTy m) m)
                (mkNone g variantTy m))

    TPat_query(
        (apExpr, [ variantTy ], ActivePatternReturnKind.RefTypeWrapper, None, 0, PrettyNaming.APInfo(false, [ "#", m ], m)),
        subPat,
        m
    )

/// The total pattern that views a value whose tag is known to be one of T at the exact variant type T
let private mkPolyVariantNarrowPattern m scrutTy variantTy subPat =
    let v, vExpr = mkCompGenLocal m "variant" scrutTy
    let apExpr = mkLambda m v (mkPolyVariantRetype vExpr variantTy m, variantTy)

    TPat_query(
        (apExpr, [ variantTy ], ActivePatternReturnKind.RefTypeWrapper, None, 0, PrettyNaming.APInfo(true, [ "#", m ], m)),
        subPat,
        m
    )

let private (|PolyVariantTypePattern|_|) g pat =
    match pat with
    | TPat_query((apExpr, [ variantTy ], _, None, 0, PrettyNaming.APInfo(false, [ "#", _ ], _)), subPat, m) ->
        Some(domainOfFunTy g (tyOfExpr g apExpr), variantTy, subPat, m)
    | _ -> None

let private (|PolyVariantTagPattern|_|) g pat =
    match pat with
    | TPat_query((apExpr, [ payloadTy ], _, None, 0, PrettyNaming.APInfo(false, [ name, _ ], _)), subPat, m) when
        name.StartsWith("`", System.StringComparison.Ordinal)
        ->
        let variantTy = domainOfFunTy g (tyOfExpr g apExpr)
        Some(variantTy, name.Substring 1, payloadTy, subPat, m)
    | _ -> None

[<NoEquality; NoComparison>]
type private PolyVariantSite =
    {
        Path: string list
        VariantTy: TType
        Tag: string
        PayloadTy: TType
        Range: range
    }

/// Visit the tag patterns, the wildcards and the other refutable tests of a pattern, each with its position as a path from the root, innermost first
let rec private visitPolyVariantPositions
    g
    path
    pat
    (onSite: PolyVariantSite -> unit)
    (onWild: string list -> unit)
    (onTest: string list -> unit)
    =
    let visit path p =
        visitPolyVariantPositions g path p onSite onWild onTest

    let visitAll prefix pats =
        pats |> List.iteri (fun i p -> visit ($"%s{prefix}%d{i}" :: path) p)

    match pat with
    | PolyVariantTagPattern g (variantTy, tag, payloadTy, subPat, m) ->
        onSite
            {
                Path = path
                VariantTy = variantTy
                Tag = tag
                PayloadTy = payloadTy
                Range = m
            }

        onTest path
        visit (polyVariantCaseName tag :: path) subPat
    | PolyVariantTypePattern g (scrutTy, variantTy, subPat, m) ->
        match tryDestPolyVariantTy g variantTy with
        | ValueSome(struct (tags, payloadTys)) ->
            for tag, payloadTy in List.zip tags payloadTys do
                onSite
                    {
                        Path = path
                        VariantTy = scrutTy
                        Tag = tag
                        PayloadTy = payloadTy
                        Range = m
                    }
        | ValueNone -> ()

        onTest path
        visit ("#" :: path) subPat
    | TPat_wild _ -> onWild path
    | TPat_as(p, _, _) -> visit path p
    | TPat_disjs(ps, _)
    | TPat_conjs(ps, _) -> ps |> List.iter (visit path)
    | TPat_query(_, p, _) ->
        onTest path
        visit ("ap" :: path) p
    | TPat_tuple(_, ps, _, _) -> visitAll "t" ps
    | TPat_unioncase(ucref, _, ps, _) ->
        onTest path
        visitAll ucref.CaseName ps
    | TPat_exnconstr(_, ps, _) ->
        onTest path
        visitAll "exn" ps
    | TPat_array(ps, _, _) ->
        onTest path
        visitAll "arr" ps
    | TPat_recd(_, _, ps, _) -> visitAll "fld" ps
    | TPat_isinst(_, _, pOpt, _) ->
        onTest path
        pOpt |> Option.iter (visit ("isinst" :: path))
    | TPat_const(Const.Unit, _) -> ()
    | TPat_const _
    | TPat_null _
    | TPat_error _ -> onTest path

/// Replace the tag patterns at the given closed positions by cases of one total active pattern per position
let rec private closePolyVariantPositions g path (closed: Map<string list, string -> Pattern -> range -> Pattern>) pat =
    let recurse p path =
        closePolyVariantPositions g path closed p

    let mapAll prefix pats =
        pats |> List.mapi (fun i p -> recurse p ($"%s{prefix}%d{i}" :: path))

    match pat with
    | PolyVariantTagPattern g (_, tag, _, subPat, m) ->
        let subPat = recurse subPat (polyVariantCaseName tag :: path)

        match closed.TryFind path with
        | Some mkCase -> mkCase tag subPat m
        | None ->
            match pat with
            | TPat_query(q, _, m) -> TPat_query(q, subPat, m)
            | _ -> pat
    | PolyVariantTypePattern g (scrutTy, variantTy, subPat, m) ->
        let subPat = recurse subPat ("#" :: path)

        match closed.TryFind path, tryDestPolyVariantTy g variantTy with
        | Some mkCase, ValueSome(struct (tags, _)) ->
            let anyTagOfType = TPat_disjs([ for tag in tags -> mkCase tag (TPat_wild m) m ], m)

            TPat_conjs([ anyTagOfType; mkPolyVariantNarrowPattern m scrutTy variantTy subPat ], m)
        | _ ->
            match pat with
            | TPat_query(q, _, m) -> TPat_query(q, subPat, m)
            | _ -> pat
    | TPat_as(p, b, m) -> TPat_as(recurse p path, b, m)
    | TPat_disjs(ps, m) -> TPat_disjs(ps |> List.map (fun p -> recurse p path), m)
    | TPat_conjs(ps, m) -> TPat_conjs(ps |> List.map (fun p -> recurse p path), m)
    | TPat_query(q, p, m) -> TPat_query(q, recurse p ("ap" :: path), m)
    | TPat_tuple(tupInfo, ps, tys, m) -> TPat_tuple(tupInfo, mapAll "t" ps, tys, m)
    | TPat_unioncase(ucref, tinst, ps, m) -> TPat_unioncase(ucref, tinst, mapAll ucref.CaseName ps, m)
    | TPat_exnconstr(tcref, ps, m) -> TPat_exnconstr(tcref, mapAll "exn" ps, m)
    | TPat_array(ps, ty, m) -> TPat_array(mapAll "arr" ps, ty, m)
    | TPat_recd(tcref, tinst, ps, m) -> TPat_recd(tcref, tinst, mapAll "fld" ps, m)
    | TPat_isinst(srcTy, tgtTy, Some p, m) -> TPat_isinst(srcTy, tgtTy, Some(recurse p ("isinst" :: path)), m)
    | TPat_wild _
    | TPat_isinst(_, _, None, _)
    | TPat_const _
    | TPat_null _
    | TPat_error _ -> pat

/// The most cases a total active pattern can have, the size of the largest Choice type
let private maxActivePatternCases = 7

/// Build the total active pattern that splits a value of a closed polymorphic variant type into its tags, and return
/// the function building the pattern for one tag. Beyond 7 tags the last case passes the value on to a further
/// total active pattern over the remaining tags.
let rec private mkPolyVariantTotalPattern (g: TcGlobals.TcGlobals) m variantTy (tagsAndTys: (string * TType) list) =
    let direct, rest =
        if tagsAndTys.Length <= maxActivePatternCases then
            tagsAndTys, []
        else
            List.splitAt (maxActivePatternCases - 1) tagsAndTys

    let restCaseName = "`..."

    let caseNames =
        [ for tag, _ in direct -> polyVariantCaseName tag ]
        @ (if rest.IsEmpty then [] else [ restCaseName ])

    let resTys = List.map snd direct @ (if rest.IsEmpty then [] else [ variantTy ])
    let n = resTys.Length
    let apinfo = PrettyNaming.APInfo(true, [ for name in caseNames -> name, m ], m)
    let resTy = apinfo.ResultType g m resTys ActivePatternReturnKind.RefTypeWrapper

    let apExpr =
        mkPolyVariantDestructor g m variantTy resTy (fun vExpr tagExpr payloadExpr ->
            let mkResult i =
                let result =
                    if i < direct.Length then
                        mkPolyVariantUnbox (List.item i resTys) payloadExpr m
                    else
                        vExpr

                if n = 1 then
                    result
                else
                    mkUnionCaseExpr (mkChoiceCaseRef g m n i, resTys, [ result ], m)

            // The last case needs no test: the type allows no other tags
            let rec build i =
                if i = n - 1 then
                    mkResult i
                else
                    mkCond
                        DebugPointAtBinding.NoneAtInvisible
                        m
                        resTy
                        (mkTagTest g m tagExpr (fst (List.item i direct)))
                        (mkResult i)
                        (build (i + 1))

            build 0)

    // Give the active pattern an identity, so the match compiler evaluates it once and knows its cases are complete
    let identityVal, _ = mkCompGenLocal m "polyVariantTags" (mkFunTy g variantTy resTy)
    let identity = Some(mkLocalValRef identityVal, [])

    let mkQuery idx subPat mCase =
        TPat_query((apExpr, resTys, ActivePatternReturnKind.RefTypeWrapper, identity, idx, apinfo), subPat, mCase)

    let mkRestCase =
        if rest.IsEmpty then
            None
        else
            Some(mkPolyVariantTotalPattern g m variantTy rest)

    fun (tag: string) subPat mCase ->
        match List.tryFindIndex (fun (directTag, _) -> directTag = tag) direct, mkRestCase with
        | Some idx, _ -> mkQuery idx subPat mCase
        | None, Some mkRestCase -> mkQuery (n - 1) (mkRestCase tag subPat mCase) mCase
        | None, None -> failwith "mkPolyVariantTotalPattern: tag not in the closed row"

/// Decide, for each position a match tests polymorphic variant tags at, whether the scrutinee's tags are open or closed there.
/// Constrain the scrutinee types accordingly and fuse the tag patterns at closed positions.
let CheckPolyVariantMatchClauses (cenv: TcFileState) (env: TcEnv) (clauses: MatchClause list) =
    let g = cenv.g
    let sites = ResizeArray<PolyVariantSite>()
    let wilds = ResizeArray<string list>()

    // Paths are stored innermost first, so an ancestor of a position is a suffix of its path
    let isAncestorOrSelf (ancestor: string list) (path: string list) =
        ancestor.Length <= path.Length
        && List.skip (path.Length - ancestor.Length) path = ancestor

    for MatchClause(pat, guardOpt, _, _) in clauses do
        let clauseWilds = ResizeArray()
        let clauseTests = ResizeArray()
        visitPolyVariantPositions g [] pat sites.Add clauseWilds.Add clauseTests.Add

        // A wildcard leaves the positions at and below it open only if the clause catches everything that reaches it:
        // no guard, and no tests other than those on the way to the wildcard.
        if guardOpt.IsNone then
            for wild in clauseWilds do
                if
                    clauseTests
                    |> Seq.forall (fun test -> test.Length < wild.Length && isAncestorOrSelf test wild)
                then
                    wilds.Add wild

    if sites.Count = 0 then
        clauses
    else
        let isCovered (path: string list) =
            wilds |> Seq.exists (fun wild -> isAncestorOrSelf wild path)

        let mutable closed = Map.empty

        for KeyValue(path, pathSites) in sites |> Seq.groupBy _.Path |> Map.ofSeq do
            let pathSites = List.ofSeq pathSites
            let first = List.head pathSites

            let tagsAndTys =
                pathSites
                |> List.fold
                    (fun acc site ->
                        if List.exists (fun (tag, _) -> tag = site.Tag) acc then
                            acc
                        else
                            (site.Tag, site.PayloadTy) :: acc)
                    []
                |> List.rev

            if isCovered path then
                for site in pathSites do
                    AddCxTypeHasPolymorphicVariantTag env.DisplayEnv cenv.css site.Range NoTrace site.VariantTy site.Tag site.PayloadTy true
            else
                AddCxTypeIsPolymorphicVariantClosed env.DisplayEnv cenv.css first.Range NoTrace first.VariantTy (List.map fst tagsAndTys)

                closed <- closed.Add(path, mkPolyVariantTotalPattern g first.Range first.VariantTy tagsAndTys)

        if closed.IsEmpty then
            clauses
        else
            clauses
            |> List.map (fun (MatchClause(pat, guardOpt, target, m)) ->
                MatchClause(closePolyVariantPositions g [] closed pat, guardOpt, target, m))

/// Decide whether the polymorphic variant tags of a lone pattern, such as that of a 'let' binding, are open or closed
let CheckPolyVariantPattern (cenv: TcFileState) (env: TcEnv) (pat: Pattern) =
    let m = pat.Range

    match CheckPolyVariantMatchClauses cenv env [ MatchClause(pat, None, TTarget([], mkUnit cenv.g m, None), m) ] with
    | [ MatchClause(pat, _, _, _) ] -> pat
    | _ -> pat

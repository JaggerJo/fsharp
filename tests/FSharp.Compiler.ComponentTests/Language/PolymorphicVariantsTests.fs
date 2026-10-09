// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Experimental OCaml-style polymorphic variants
module Language.PolymorphicVariantsTests

open FSharp.Test.Compiler
open Xunit

/// Each source with a line of the signature inferred for it
let inferenceCases: obj[] seq =
    [
        "let circle = `Circle 1.0", "val circle: 'a when 'a: [> `Circle of float ]"
        "let red = `Red", "val red: 'a when 'a: [> `Red ]"
        "let shapes = [ `Circle 1.0; `Rect (2.0, 3.0) ]", "val shapes: 'a list when 'a: [> `Circle of float | `Rect of float * float ]"

        """
let area shape =
    match shape with
    | `Circle r -> System.Math.PI * r * r
    | `Rect (w, h) -> w * h""",
        "val area: shape: 'a -> float when 'a: [< `Circle of float | `Rect of float * float ]"

        """
let isRound shape =
    match shape with
    | `Circle _ -> true
    | _ -> false""",
        "val isRound: shape: 'a -> bool when 'a: [> `Circle of 'b ]"

        """
let f x = match x with `A -> 1 | `B -> 2
let g y = f y + (match y with `A -> 0 | _ -> 1)""",
        "val g: y: 'a -> int when 'a: [< `A | `B > `A ]"

        """
let guarded x =
    match x with
    | `A n when n > 0 -> n
    | `A _ -> 0
    | `B -> -1""",
        "val guarded: x: 'a -> int when 'a: [< `A of int | `B ]"

        """
let both a b =
    match a, b with
    | `On, `On -> 1
    | `On, `Off -> 2
    | `Off, _ -> 3""",
        "val both: a: 'a -> b: 'b -> int when 'a: [< `Off | `On ] and 'b: [< `Off | `On ]"

        """
let describe = function
    | `Num n -> string n
    | `Neg (`Num n) -> "-" + string n
    | `Neg _ -> "-?"
""",
        "when 'a: [< `Neg of 'c | `Num of 'b ] and 'c: [> `Num of 'd ]"

        "let lam = fun (`Wrap x) -> x + 1", "val lam: 'a -> int when 'a: [< `Wrap of int ]"
        "let sorted = List.sort [ `B 2; `A 3; `A 1 ]", "val sorted: [ `A of int | `B of int ] list"

        "type Rgba = [ `Red | `Green | `Alpha of byte ]", "type Rgba = [ `Alpha of byte | `Green | `Red ]"
        "type Color = [ `Red | `Green ]\ntype Rgba = [ Color | `Alpha of byte ]", "type Rgba = [ `Alpha of byte | `Green | `Red ]"
        "let anyRed (c: [> `Red ]) = c", "val anyRed: c: 'a -> 'a when 'a: [> `Red ]"
        "let primary (c: [< `Red | `Green ]) = 1", "val primary: c: 'a -> int when 'a: [< `Green | `Red ]"
        "let mixed (c: [< `Red | `Green > `Red ]) = 1", "val mixed: c: 'a -> int when 'a: [< `Green | `Red > `Red ]"
        "let keepRed<'r when 'r: [> `Red ]> (x: 'r) : 'r = x", "val keepRed: x: 'r -> 'r when 'r: [> `Red ]"

        """
type Color = [ `Red | `Green ]
let describe x =
    match x with
    | #Color -> "color"
    | `Alpha a -> string a""",
        "val describe: x: 'a -> string when 'a: [< `Alpha of 'b | `Green | `Red ]"
    ]
    |> Seq.map (fun (source, expected) -> [| box source; box expected |])

[<Theory; MemberData(nameof inferenceCases)>]
let ``Inferred types`` (source: string, expected: string) =
    let signature =
        FSharp $"module M\n%s{source}"
        |> withLangVersionPreview
        |> printSignaturesWith 400

    Assert.Contains(expected, signature)

module Diagnostics =

    [<Fact>]
    let ``A #T pattern binds at T`` () =
        FSharp """
module M
type Shape = [ `Circle of float | `Rect of float * float ]
let area (s: Shape) = match s with `Circle r -> r | `Rect (w, h) -> w * h
let withSquares x =
    match x with
    | #Shape as s -> area s
    | `Square side -> side * side
let r = withSquares (`Square 2.0)
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldSucceed
        |> withDiagnostics []

    [<Fact>]
    let ``An exact variant type upcasts to one with more tags`` () =
        FSharp """
module M
type Color = [ `Red | `Green ]
type Rgba = [ Color | `Alpha of byte ]
let red : Color = `Red
let colors : Rgba list = [ red :> Rgba; `Alpha 3uy ]
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldSucceed
        |> withDiagnostics []

    [<Theory>]
    [<InlineData("(`Alpha 1uy : Rgba) :> Color")>]
    [<InlineData("(`Red : Color) :> [ `Red of int | `Green ]")>]
    let ``An upcast must keep every tag and payload`` (coercion: string) =
        FSharp $"""
module M
type Color = [ `Red | `Green ]
type Rgba = [ Color | `Alpha of byte ]
let bad = {coercion}
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldFail
        |> withErrorCode 193

    [<Fact>]
    let ``A closed match over more tags than a Choice type has is complete`` () =
        FSharp """
module M
let day x =
    match x with
    | `Mon -> 1 | `Tue -> 2 | `Wed -> 3 | `Thu -> 4 | `Fri -> 5 | `Sat -> 6 | `Sun -> 7
    | `Holiday name -> String.length name | `Leap -> 29 | `Other n -> n
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldSucceed
        |> withDiagnostics []

    [<Fact>]
    let ``Only exact variant types can be included`` () =
        FSharp """
module M
type T = [ int | `A ]
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldFail
        |> withErrorCode 3926

    [<Fact>]
    let ``A required tag must be allowed`` () =
        FSharp """
module M
let f (x: [< `A | `B > `C ]) = 1
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldFail
        |> withErrorCode 3927


    [<Fact>]
    let ``A closed type rejects other tags`` () =
        FSharp """
module M
let area shape =
    match shape with
    | `Circle r -> r
    | `Rect (w, h) -> w * h
let bad = area `Triangle
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldFail
        |> withSingleDiagnostic (Error 1, Line 7, Col 16, Line 7, Col 25, "The tag '`Triangle' is used here, but this polymorphic variant type allows at most `Circle | `Rect.")

    [<Fact>]
    let ``A tag carries one payload type`` () =
        FSharp """
module M
let bad = [ `Circle 1.0; `Circle "big" ]
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldFail
        |> withErrorCode 1

    [<Fact>]
    let ``A closed match is complete`` () =
        FSharp """
module M
let toInt x =
    match x with
    | `Zero -> 0
    | `One -> 1
let (`Pair (p, q)) = `Pair (1, "one")
"""
        |> withLangVersionPreview
        |> typecheck
        |> shouldSucceed
        |> withDiagnostics []

    [<Fact>]
    let ``Polymorphic variants need the preview language version`` () =
        FSharp """
module M
let red = `Red
"""
        |> withLangVersion "latest"
        |> typecheck
        |> shouldFail
        |> withErrorCode 3350

module Signatures =

    let private implementation =
        """
module M
let area shape =
    match shape with
    | `Circle r -> r
    | `Rect (w, h) -> w * h
"""

    let private checkAgainst signature =
        Fsi signature
        |> withAdditionalSourceFile (FsSource implementation)
        |> withLangVersionPreview
        |> compile

    [<Fact>]
    let ``A signature may give a stricter row`` () =
        checkAgainst """
module M
val area: shape: 'a -> int when 'a: [< `Circle of int ]
"""
        |> shouldSucceed

    [<Fact>]
    let ``A signature may not give a looser row`` () =
        checkAgainst """
module M
val area: shape: 'a -> int when 'a: [< `Circle of int | `Rect of int * int | `Tri ]
"""
        |> shouldFail
        |> withErrorCode 340

module Runtime =

    [<Fact>]
    let ``Tags and payloads round trip`` () =
        FSharp """
module M

let area shape =
    match shape with
    | `Circle r -> r * r * 3.0
    | `Rect (w, h) -> w * h

let isRound shape =
    match shape with
    | `Circle _ -> true
    | _ -> false

let both a b =
    match a, b with
    | `On, `On -> 1
    | `On, `Off -> 2
    | `Off, _ -> 3

let describe = function
    | `Num n -> string n
    | `Neg (`Num n) -> "-" + string n
    | `Neg _ -> "-?"

let check name actual expected =
    if actual <> expected then failwith $"%s{name}: expected %A{expected}, got %A{actual}"

[<EntryPoint>]
let main _ =
    check "area" (List.sumBy area [ `Circle 1.0; `Rect (2.0, 3.0) ]) 9.0
    check "isRound" [ isRound (`Circle 2.0); isRound `Square ] [ true; false ]
    check "both" [ both `On `On; both `On `Off; both `Off `On ] [ 1; 2; 3 ]
    let day x =
        match x with
        | `Mon -> 1 | `Tue -> 2 | `Wed -> 3 | `Thu -> 4 | `Fri -> 5 | `Sat -> 6 | `Sun -> 7
        | `Holiday (name: string) -> name.Length | `Leap -> 29 | `Other n -> n

    check "many tags" (List.map day [ `Mon; `Sun; `Holiday "xmas"; `Leap; `Other 42 ]) [ 1; 7; 4; 29; 42 ]
    check "equality" [ `A 1 = `A 1; `A 1 = `A 2; `A 1 = `B ] [ true; false; false ]
    check "ordering" (List.sort [ `B 2; `A 3; `A 1 ] |> List.map (function `A n -> n | `B n -> -n)) [ 1; 3; -2 ]
    check "describe" [ describe (`Num 3); describe (`Neg (`Num 4)); describe (`Neg `Zero) ] [ "3"; "-4"; "-?" ]
    0
"""
        |> withLangVersionPreview
        |> asExe
        |> compileExeAndRun
        |> shouldSucceed

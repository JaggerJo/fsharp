module Program

[<EntryPoint>]
let main _ =
    printfn "%s" (Colours.describe Colours.red)
    printfn "%s" (Colours.describe (`Rgb (1, 2, 3)))
    printfn "%d" (Colours.paint `Green)
    0

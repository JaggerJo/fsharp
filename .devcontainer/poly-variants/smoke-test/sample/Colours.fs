module Colours

let describe colour =
    match colour with
    | `Red -> "red"
    | `Rgb (r, g, b) -> $"rgb({r}, {g}, {b})"

let red = `Red

let paint (colour: [ `Red | `Green ]) =
    match colour with
    | `Red -> 1
    | `Green -> 2

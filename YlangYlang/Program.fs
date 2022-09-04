open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer



[<EntryPoint>]
let main argv =
    let fileText = readFile "Test.yl"

    let matchers =
        [ intMatcher
          whitespaceMatcher
          stringMatcher ]

    justKeepLexing matchers fileText


    |> printfn "%A"

    0

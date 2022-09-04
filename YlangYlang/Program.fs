open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer
open Lexer.Matchers



[<EntryPoint>]
let main argv =
    let fileText = readFile "Test.yl"


    justKeepLexing allMatchersInOrder fileText
    |> printfn "%A"

    0

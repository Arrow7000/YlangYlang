open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer
open Lexer.Matchers
open Parsing


[<EntryPoint>]
let main argv =
    let fileText = readFile "Test.yl"


    justKeepLexing allMatchersInOrder fileText
    |> Result.map parser
    |> printfn "%A"

    0

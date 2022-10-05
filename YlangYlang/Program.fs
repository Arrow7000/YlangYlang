open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer
open Lexer.Matchers
open ExpressionParsing


[<EntryPoint>]
let main argv =
    let fileText = readFile "Expression.yl"


    justKeepLexing allMatchersInOrder fileText
    |> Result.map (
        tee (fun thing -> printfn "%A" <| List.map (fun t -> t.token) thing)
        >> Parser.run parseSingleLineExpression
    )
    |> printfn "%A"

    0

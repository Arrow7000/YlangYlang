open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer
open ExpressionParsing


[<EntryPoint>]
let main argv =
    let fileText = readFile "Expression.yl"

    tokeniseString fileText
    |> Result.map (
        tee (fun thing -> printfn "%A" <| List.map (fun t -> t.token) thing)
        >> Parser.run parseExpression
        >> formatErrors
    )
    |> printfn "%A"

    0

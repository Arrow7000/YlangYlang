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
        tee (List.map (fun t -> t.token) >> printfn "%A")
        >> Parser.run parseExpression
        >> DebugHelpers.formatErrors
    )
    |> printfn "%A"

    0

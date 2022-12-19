open FileHelpers


[<EntryPoint>]
let main argv =
    let fileText = readFile "Expression.yl"

    Lexer.tokeniseString fileText
    |> Result.map (
        tee (List.map (fun t -> t.token) >> printfn "%A")
        >> Parser.run ExpressionParsing.parseExpression
        >> DebugHelpers.formatErrors
    )
    |> printfn "%A"

    0

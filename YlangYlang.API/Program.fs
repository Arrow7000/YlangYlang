open FileHelpers


[<EntryPoint>]
let main argv =
    let fileText = readFileSync "Expression.yl"

    Lexer.tokeniseString fileText
    |> Result.map (
        tee (List.map (fun t -> t.token) >> printfn "%A")
        >> ExpressionParsing.run ExpressionParsing.parseEntireModule
        >> DebugHelpers.formatErrors
        >> Result.map (fun r -> r.parseResult)
    )
    |> printfn "%A"

    0

open FileHelpers
open SyntaxTree
open Thoth.Json.Net
open Errors

/// Sadly this doesn't work unless we write specialised versions for every possible concrete type https://github.com/thoth-org/Thoth.Json/issues/169
let cstNodeEncoder : Encoder<CstNode<'a>> =
    fun (cstNode : CstNode<'a>) ->
        printfn "Calling CstNode encoder"
        Encode.Auto.generateEncoder () cstNode.node


let cstNodeDecoder : Decoder<CstNode<'a>> = fun _ -> failwithf "Not implemented"

let cstCoder = Extra.empty |> Extra.withCustom cstNodeEncoder cstNodeDecoder


let toJson result = Encode.Auto.toString (2, value = result, extra = cstCoder)



[<EntryPoint>]
let main argv =
    let fileText = readFileSync "Expression.yl"

    Lexer.tokeniseString fileText
    |> Result.mapError LexingError
    |> Result.bind (
        ExpressionParsing.run ExpressionParsing.parseExpression
        >> Parser.toResult
        >> Result.mapError ParsingError
    )
    |> Result.map (TypeChecker.inferTypeFromExpr TypedSyntaxTree.Ctx.empty)
    |> printfn "%A"

    0

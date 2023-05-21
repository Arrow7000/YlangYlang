﻿open FileHelpers
open ConcreteSyntaxTree
open Thoth.Json.Net


/// Sadly this doesn't work unless we write specialised versions for every possible concrete type https://github.com/thoth-org/Thoth.Json/issues/169
let cstNodeEncoder : Encoder<CstNode<'a>> =
    fun (cstNode : CstNode<'a>) ->
        printfn "Calling CstNode encoder"
        Encode.Auto.generateEncoder () cstNode.node


//type CstNode<'a> = { node : 'a; source : int list }


//printfn ".FullName: %A"
//<| typeof<CstNode<'a>>.FullName


//printfn "IsGenericType: %A"
//<| typeof<CstNode<'a>>.IsGenericType

//printfn "IsGenericTypeDefinition: %A"
//<| typeof<CstNode<'a>>.IsGenericTypeDefinition

//printfn "GetGenericTypeDefinition: %A"
//<| typeof<CstNode<int>>.GetGenericTypeDefinition ()

//printfn "GetGenericTypeDefinition.FullName: %A"
//<| (typeof<CstNode<int>>.GetGenericTypeDefinition ())
//    .FullName

let cstNodeDecoder : Decoder<CstNode<'a>> = fun _ -> failwithf "Not implemented"

let cstCoder =
    Extra.empty
    |> Extra.withCustom cstNodeEncoder cstNodeDecoder


let toJson result =
    Encode.Auto.toString (2, value = result, extra = cstCoder)



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
    //|> toJson
    |> printfn "%A"

    0
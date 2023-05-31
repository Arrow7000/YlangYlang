module ExpressionParsingTests

open Expecto
open Lexer
open SyntaxTree
open ConcreteSyntaxTree
open Parser
open ExpressionParsing
open System.Diagnostics


/// So that we don't have to reproduce the contextStack implementation details before we actuals with expecteds
//let private stripContexts (ctx : ParseContext<'token, 'ctx, 'err>) = { ctx with contextStack = List.empty }
let private stripContexts result =
    { result with parsingContext = { result.parsingContext with contextStack = List.empty } }

let private makeSuccess tokensParsed v =
    blankParseCtx
    |> makeParseResultWithCtx (ParsingSuccess v)
    |> fun result -> { result with parsingContext = { result.parsingContext with prevTokens = tokensParsed } }


let makeBlankCstNode node = makeCstNode node List.empty
let stripTokens cstNode = { cstNode with source = List.empty }


let private makeNumberExpression =
    NumberPrimitive
    >> Primitive
    >> ExplicitValue
    >> SingleValueExpression


[<Tests>]
let testSimpleExpression =
    (fun _ ->
        (tokeniseString "-4.6")
        |> Result.map (run parseDelimExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res.parseResult
                    (ParsingSuccess
                     <| makeNumberExpression (FloatLiteral -4.6))
                    "Parse single value expression")
    |> testCase "Parse single value expression"



[<Tests>]
let testOperatorExpression =
    (fun _ ->
        let tokens = tokeniseString "-4.6  ++ \"test\" "

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run parseCompoundExpressions)
            |> fun (tokens', res') ->
                Expect.equal
                    (stripContexts res')
                    (CompoundExpression (
                        Operator (
                            makeNumberExpression (FloatLiteral -4.6)
                            |> makeBlankCstNode,
                            NEL.make (
                                makeBlankCstNode AppendOp,
                                makeBlankCstNode (
                                    SingleValueExpression (ExplicitValue (Primitive (StringPrimitive "test")))
                                )
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse operator expression")
    |> testCase "Parse operator expression"


[<Tests>]
let testParensExpressionWithSimpleExpressions =
    (fun _ ->
        let tokens = tokeniseString "(  34) "

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (Parser.run parseExpression)
            |> fun (tokens', res') ->
                Expect.equal
                    res'.parseResult
                    (ParsingSuccess (ParensedExpression (makeNumberExpression (IntLiteral 34))))
                    "Parse parenthesised simple expression")
    |> testCase "Parse parenthesised simple expression"

[<Tests>]
let testNestedParensExpressionWithSimpleExpression =
    (fun _ ->
        let tokens = tokeniseString "( (  34) ) "

        tokens
        |> Result.map (Parser.run ExpressionParsing.parseExpression)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res.parseResult
                    (ParsingSuccess (ParensedExpression (ParensedExpression (makeNumberExpression (IntLiteral 34)))))
                    "Parse nested parenthesised simple expression")
    |> testCase "Parse nested parenthesised simple expression"

[<Tests>]
let testCompoundExpression =
    (fun _ ->
        let tokens = tokeniseString "(  34 + -4.6   ) "

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run parseCompoundExpressions)
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (
                        CompoundExpression (
                            Operator (
                                makeBlankCstNode (makeNumberExpression (IntLiteral 34)),
                                NEL.make (
                                    makeBlankCstNode PlusOp,
                                    makeBlankCstNode (makeNumberExpression (FloatLiteral -4.6))
                                )
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse parenthesised single operator expression")
    |> testCase "Parse parenthesised single operator expression"

[<Tests>]
let testParensExpressionWithMultiOperators =
    (fun _ ->
        let tokens = tokeniseString "(  34 + -4.6 / 7 ) "

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run parseCompoundExpressions)
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (
                        CompoundExpression (
                            Operator (
                                makeBlankCstNode (makeNumberExpression (IntLiteral 34)),
                                NEL.make (
                                    makeBlankCstNode PlusOp,
                                    makeBlankCstNode (
                                        CompoundExpression (
                                            Operator (
                                                makeBlankCstNode (makeNumberExpression (FloatLiteral -4.6)),
                                                NEL.make (
                                                    makeBlankCstNode DivOp,
                                                    makeBlankCstNode (makeNumberExpression (IntLiteral 7))
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"

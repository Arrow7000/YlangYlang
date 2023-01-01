module ExpressionParsingTests

open Expecto
open Lexer
open ConcreteSyntaxTree
open Parser
open ExpressionParsing
open System.Diagnostics
open Expecto.Logging

let private stripContexts ctx : ExpressionParserResult<'a> = { ctx with contextStack = List.empty }

let private makeSuccess tokensParsed v =
    blankParseCtx
    |> makeParseResultWithCtx (ParsingSuccess v)
    |> fun ctx -> { ctx with prevTokens = tokensParsed }


let private makeNumberExpression =
    NumberPrimitive
    >> Primitive
    >> ExplicitValue
    >> Expression.SingleValueExpression


[<Tests>]
let testSimpleExpression =
    (fun _ ->
        (tokeniseString "-4.6")
        |> Result.map (Parser.run parseSingleValueExpressions)
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
            |> split (Parser.run parseCompoundExpressions)
            |> fun (tokens', res') ->
                Expect.equal
                    (stripContexts res')
                    (Expression.CompoundExpression (
                        CompoundExpression.Operator (
                            makeNumberExpression (FloatLiteral -4.6),
                            (AppendOp,
                             Expression.SingleValueExpression (ExplicitValue (Primitive (StringPrimitive "test"))))
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
        |> Result.map (Parser.run parseExpression)
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
            |> split (Parser.run parseCompoundExpressions)
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (
                        Expression.CompoundExpression (
                            CompoundExpression.Operator (
                                makeNumberExpression (IntLiteral 34),
                                (PlusOp, makeNumberExpression (FloatLiteral -4.6))
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
            |> split (Parser.run parseCompoundExpressions)
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (
                        Expression.CompoundExpression (
                            CompoundExpression.Operator (
                                makeNumberExpression (IntLiteral 34),
                                (PlusOp,
                                 (Expression.CompoundExpression (
                                     CompoundExpression.Operator (
                                         makeNumberExpression (FloatLiteral -4.6),
                                         (DivOp, makeNumberExpression (IntLiteral 7))
                                     )
                                 )))
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"

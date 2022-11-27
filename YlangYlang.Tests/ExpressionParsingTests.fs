module ExpressionParsingTests

open Expecto
open Lexer
open ConcreteSyntaxTree
open Parser
open ExpressionParsing


let private makeSuccess v =
    blankParseCtx
    |> makeParseResultWithCtx (ParsingSuccess v)

let private makeNumberSingleExpression n =
    ExplicitValue (Primitive (NumberPrimitive n))

let private makeNumberExpression =
    makeNumberSingleExpression
    >> Expression.SingleValueExpression


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
                     <| makeNumberSingleExpression (FloatLiteral -4.6))
                    "Parse single value expression")
    |> testCase "Parse single value expression"




let testOperatorExpression =
    (fun _ ->
        (tokeniseString "-4.6  ++ \"test\" ")
        |> Result.map (Parser.run parseCompoundExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    (Expression.CompoundExpression (
                        CompoundExpression.Operator (
                            makeNumberExpression (FloatLiteral -4.6),
                            (AppendOp,
                             Expression.SingleValueExpression (ExplicitValue (Primitive (StringPrimitive "test"))))
                        )
                     )
                     |> makeSuccess)
                    "Parse operator expression")
    |> testCase "Parse operator expression"



let testParensExpressionWithSimpleExpressions =
    (fun _ ->
        (tokeniseString "(  34) ")
        |> Result.map (Parser.run parseSingleValueExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res.parseResult
                    (ParsingSuccess
                     <| makeNumberSingleExpression (IntLiteral 34))
                    "Parse parenthesised simple expression")
    |> testCase "Parse parenthesised simple expression"


let testNestedParensExpressionWithSimpleExpression =
    (fun _ ->
        (tokeniseString "( (  34) ) ")
        |> Result.map (Parser.run parseSingleValueExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res.parseResult
                    (ParsingSuccess
                     <| makeNumberSingleExpression (IntLiteral 34))
                    "Parse nested parenthesised simple expression")
    |> testCase "Parse nested parenthesised simple expression"

let testParensExpressionWithMultiOperators =
    (fun _ ->
        (tokeniseString "(  34 + -4.6 / 7 ) ")
        |> Result.map (Parser.run parseCompoundExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    ((Expression.CompoundExpression (
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
                     ))
                     |> makeSuccess)
                    //res.parseResult
                    //(ParsingSuccess (
                    //    Expression.CompoundExpression (
                    //        CompoundExpression.Operator (
                    //            makeNumberExpression (IntLiteral 34),
                    //            (PlusOp,
                    //             (Expression.CompoundExpression (
                    //                 CompoundExpression.Operator (
                    //                     makeNumberExpression (FloatLiteral -4.6),
                    //                     (DivOp, makeNumberExpression (IntLiteral 7))
                    //                 )
                    //             )))
                    //        )
                    //    )
                    //))
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"


[<Tests>]
let tests =
    testList
        "Expression parsing"
        [ testParensExpressionWithMultiOperators
          testSimpleExpression
          testOperatorExpression
          testParensExpressionWithSimpleExpressions
          testNestedParensExpressionWithSimpleExpression ]

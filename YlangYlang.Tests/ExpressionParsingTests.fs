module ExpressionParsingTests

open Expecto
open Lexer
open ConcreteSyntaxTree
open Parser
open ExpressionParsing


let private makeSuccess v = ParsingSuccess (v, List.empty)

let private makeNumberSingleExpression n =
    ExplicitValue (Primitive (NumberPrimitive n))

let private makeNumberExpression =
    makeNumberSingleExpression
    >> SingleValueExpression


let testSimpleExpression =
    (fun _ ->
        (tokeniseString "-4.6")
        |> Result.map (Parser.run parseSingleValueExpressions)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    (makeNumberSingleExpression (FloatLiteral -4.6)
                     |> makeSuccess)
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
                    (CompoundExpression (
                        Operator (
                            makeNumberExpression (FloatLiteral -4.6),
                            (AppendOp, SingleValueExpression (ExplicitValue (Primitive (StringPrimitive "test"))))
                        )
                     )
                     |> makeSuccess)
                    "Parse operator expression")
    |> testCase "Parse operator expression"



let testParensExpressionWithSimpleExpressions =
    (fun _ ->
        (tokeniseString "(  34) ")
        |> Result.map (Parser.run parseParensExpression)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    (makeNumberExpression (IntLiteral 34)
                     |> makeSuccess)
                    "Parse parenthesised simple expression")
    |> testCase "Parse parenthesised simple expression"

let testParensExpressionWithMultiOperators =
    (fun _ ->
        (tokeniseString "(  34 + -4.6 / 7 ) ")
        |> Result.map (Parser.run parseParensExpression)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    (CompoundExpression (
                        Operator (
                            makeNumberExpression (IntLiteral 34),
                            (PlusOp,
                             (CompoundExpression (
                                 Operator (
                                     makeNumberExpression (FloatLiteral -4.6),
                                     (DivOp, makeNumberExpression (IntLiteral 7))
                                 )
                             )))
                        )
                     )
                     |> makeSuccess)
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"

let f = testFixture

[<Tests>]
let tests =
    testList
        "Expression parsing"
        [ testParensExpressionWithMultiOperators
          testSimpleExpression
          testOperatorExpression
          testParensExpressionWithSimpleExpressions ]

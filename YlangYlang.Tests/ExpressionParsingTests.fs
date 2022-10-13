module ExpressionParsingTests

open Expecto
open Lexer
open ConcreteSyntaxTree
open Parser
open ExpressionParsing


let private makeSuccess v = ParsingSuccess (v, List.empty)

let private makeNumberExpression n =
    SingleValueExpression (ExplicitValue (Primitive (NumberPrimitive n)))


let testParensExpression =
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
let tests = testList "Expression parsing" [ testParensExpression ]

module ExpressionParsingTests

open Expecto
open Lexer
open ParserTypes
open Parser
open ExpressionParsing


let private makeSuccess v = ParsingSuccess (v, List.empty)



let testParensExpression =
    (fun _ ->
        (tokeniseString "(  34 + -4.6 / 7 ) ")
        |> Result.map (Parser.run parseParensExpression)
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res
                    (Operator (
                        NumberPrimitive (IntLiteral 34),
                        NEL.consFromList
                            (PlusOp, NumberPrimitive (FloatLiteral -4.6))
                            [ DivOp, NumberPrimitive (IntLiteral 7) ]
                     )
                     |> makeSuccess)
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"

let f = testFixture

[<Tests>]
let tests = testList "Expression parsing" [ testParensExpression ]

module ExpressionParsing


open System.Numerics
open Lexer
open ConcreteSyntaxTree
open ParserStates
open Parser


let private parseChoosePrimitiveLiteral chooser =
    matchSingleToken (function
        | Token.PrimitiveLiteral prim ->
            match chooser prim with
            | Some x -> Some x
            | None -> None
        | _ -> None)
    |> setLabel "primitive literal"



let inline negate (n : ^a) = n * -LanguagePrimitives.GenericOne

let parseUnaryNegationOpInt : Parser<uint -> int> =
    parseToken (Token.Operator Operator.MinusOp) (int >> negate)


let parseUnaryNegationOpFloat : Parser<float -> float> =
    parseToken (Token.Operator Operator.MinusOp) negate




let parseUint =
    parseChoosePrimitiveLiteral (function
        | UintLiteral n -> Some n
        | _ -> None)

let parseInt : Parser<NumberLiteralValue> =
    fork parseUnaryNegationOpInt (succeed int) (fun op -> succeed op |= parseUint |> map IntLiteral)
    |> setLabel "int"



let parseUfloat =
    parseChoosePrimitiveLiteral (function
        | UfloatLiteral n -> Some n
        | _ -> None)
    |> setLabel "ufloat"


let parseFloat : Parser<NumberLiteralValue> =
    fork parseUnaryNegationOpFloat (succeed id) (fun op -> succeed op |= parseUfloat |> map FloatLiteral)
    |> setLabel "float"



let parseUnit =
    matchSingleToken (function
        | Token.Unit -> Some UnitPrimitive
        | _ -> None)
    |> setLabel "unit"


let parsePrimitiveLiteral =
    oneOf [ either parseInt parseFloat |> map NumberPrimitive
            parseChoosePrimitiveLiteral (function
                | StringLiteral str -> StringPrimitive str |> Some
                | CharLiteral c -> CharPrimitive c |> Some
                | _ -> None)

            parseUnit ]
    |> setLabel "primitive literal"





let parseOperator =
    matchSingleToken (function
        | Token.Operator op -> Some op
        | _ -> None)
    |> setLabel "operator"



let parseSingleParam =
    matchSingleToken (function
        | ValueIdentifier str -> Some <| Named str
        | Underscore -> Some <| Ignored
        | _ -> None)

let parseParamList =
    oneOrMore (parseSingleParam |. spaces)
    |> setLabel "param list"



let parseIdentifier =
    matchSingleToken (function
        | Token.ValueIdentifier n -> Some <| IdentifierName n
        | _ -> None)
    |> setLabel "identifier"








/// Create a parser and a version of the parser also matching a parenthesised version of the parser
let rec parensifyParser parser =
    either
        parser
        (succeed id |. symbol ParensOpen |. spaces
         |= lazyParser (fun _ -> parensifyParser parser)
         |. spaces
         |. symbol ParensClose)
    |. spaces



#nowarn "40"

let rec parseLambda =
    succeed (fun params_ body -> { params_ = params_; body = body })
    |. symbol Backslash
    |. spaces
    |= parseParamList
    |. spaces
    |. symbol Token.Arrow
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |. spaces
    |> setLabel "lambda"



and singleAssignment =
    succeed (fun name params' (expr : Expression) ->
        { name = name
          value =
            match params' with
            | [] -> expr
            | head :: tail ->
                ({ params_ = NEL.consFromList head tail
                   body = expr })
                |> Function
                |> ExplicitValue
                |> SingleValueExpression })
    |= parseIdentifier
    |= (repeat (parseSingleParam |. spaces))
    |. spaces
    |. symbol Token.AssignmentEquals
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |. spaces
    |> setLabel "single let assignment"




and assignmentList =
    succeed (fun letBindings expr -> LetExpression (letBindings, expr))
    |. symbol LetKeyword
    |. spaces
    |= oneOrMore singleAssignment
    |. spaces
    |. symbol InKeyword
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |> setLabel "let bindings assignment list"



and parseSingleValueExpressions : Parser<SingleValueExpression> =
    parensifyParser (
        oneOf [ parseIdentifier |> map Identifier
                parseLambda |> map (Function >> ExplicitValue)
                parsePrimitiveLiteral
                |> map (Primitive >> ExplicitValue)
                assignmentList ]
    )
    |> setLabel "single value expression"






and parseCompoundExpressions =
    parensifyParser (
        succeed (fun (expr : SingleValueExpression) opExprOpt ->
            match opExprOpt with
            | Some (opOpt, expr') ->
                match opOpt with
                | Some op ->
                    Operator (SingleValueExpression expr, (op, expr'))
                    |> CompoundExpression

                | None ->
                    FunctionApplication (SingleValueExpression expr, expr')
                    |> CompoundExpression

            | None -> SingleValueExpression expr)
        |= parseSingleValueExpressions
        |. spaces
        |= opt (
            succeed (fun opOpt expr -> opOpt, expr)
            |= opt parseOperator
            |. spaces
            |= lazyParser (fun _ -> parseExpression)
            |. spaces
        )
    )
    |> setLabel "compound expression"



and parseExpression =
    succeed id

    |= parseBlock parseCompoundExpressions
    |. spaces

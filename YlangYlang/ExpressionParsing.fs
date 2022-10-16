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





and parseSingleValueExpressions : Parser<SingleValueExpression> =
    oneOf [ parseIdentifier |> map Identifier
            parseLambda |> map (Function >> ExplicitValue)
            parsePrimitiveLiteral
            |> map (Primitive >> ExplicitValue) ]
    |> setLabel "single value expression"







and parseCompoundExpressions =
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
    |> setLabel "compound expression"

/// This has to be separate because this returns a full expression
and parseParensExpression =
    (succeed id

     |. symbol ParensOpen
     |. spaces
     |= parseUntilToken ParensClose (lazyParser (fun _ -> parseExpression))
     |. spaces
     |. symbol ParensClose
     |. spaces)
    |> setLabel "parenthesised expression"


and parseExpression =
    succeed id
    |= parseBlock (either parseParensExpression parseCompoundExpressions)
    |. spaces




//    | head :: rest ->
//        match head.token with
//        | Whitespace _ -> singleLineExpressionParser stateCtx rest

//        | ParensOpen ->
//            singleLineExpressionParser
//                { stateCtx with
//                    isParens = Parens stateCtx.isParens
//                    state = ExpressionParsingState.Start }
//                rest

//        | ParensClose ->
//            match stateCtx.isParens with
//            | Parens innerParens -> { stateCtx with isParens = innerParens } // i.e. unnest a level
//            | NoParens -> onlyUpdateState (SyntaxError UnexpectedClosingParens)

//        | Token.Operator MinusOp ->

//            singleLineExpressionParser (onlyUpdateState MinusOperator) rest


//        | Token.PrimitiveLiteral literal ->
//            match stateCtx.state with
//            | MinusOperator ->
//                literalTokenToParsingValue true literal
//                |> PrimitiveLiteral
//                |> onlyUpdateState

//            | _ ->
//                literalTokenToParsingValue false literal
//                |> PrimitiveLiteral
//                |> onlyUpdateState

//        | _ -> onlyUpdateState <| UnexpectedToken head





///// Only making this parse one-line expressions to begin with for simplicity.
///// `isInImmediateParens` parameter is so that we can determine whether the contents should be parsed as a tuple, which need to be wrapped in parentheses
//let expressionParser (tokensLeft : TknCtx list) =
//    let (thisLineTokens, remainingTokens) =
//        tokensLeft
//        |> List.takeWhilePartition (fun tokenCtx ->
//            match tokenCtx.token with
//            | Whitespace list -> not <| List.contains NewLine list
//            | _ -> true)


//    let stateWithCtx =
//        singleLineExpressionParser
//            { isParens = NoParens
//              state = ExpressionParsingState.Start }
//            thisLineTokens

//    // I'm pretty sure we don't need to check whether we're in parens cos we should have already done it inside singleLineExpressionParser
//    stateWithCtx.state

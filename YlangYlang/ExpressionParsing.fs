module ExpressionParsing


open System.Numerics
open Lexer
open ParserTypes
open ParserStates
open Parser


//let private literalTokenToParsingValue isPrecededByMinus (primitiveLiteral : PrimitiveLiteral) =
//    match primitiveLiteral with
//    | PrimitiveLiteral.UintLiteral num ->
//        num
//        |> int
//        |> if isPrecededByMinus then (*) -1 else id
//        |> IntLiteral
//        |> NumberPrimitive
//    | PrimitiveLiteral.UfloatLiteral num -> FloatLiteral num |> NumberPrimitive
//    | StringLiteral str -> StringPrimitive str
//    | CharLiteral c -> CharPrimitive c


let private parseChoosePrimitiveLiteral chooser =
    matchSingleToken (function
        | Token.PrimitiveLiteral prim ->
            match chooser prim with
            | Some x -> Some x
            | None -> None
        | _ -> None)

//let private parseChooseOperator chooser =
//    matchSingleToken (function
//        | Token.Operator op->
//            match op with
//            | Some x -> Some x
//            | None -> None
//        | _ -> None)

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


let parseUfloat =
    parseChoosePrimitiveLiteral (function
        | UfloatLiteral n -> Some n
        | _ -> None)

let parseFloat : Parser<NumberLiteralValue> =
    fork parseUnaryNegationOpFloat (succeed id) (fun op -> succeed op |= parseUfloat |> map FloatLiteral)



let parseUnit =
    matchSingleToken (function
        | Token.Unit -> Some UnitPrimitive
        | _ -> None)

let parsePrimitiveLiteral =
    oneOf [ either parseInt parseFloat |> map NumberPrimitive

            parseChoosePrimitiveLiteral (function
                | StringLiteral str -> StringPrimitive str |> Some
                | CharLiteral c -> CharPrimitive c |> Some
                | _ -> None)

            parseUnit ]




let parseOperator =
    matchSingleToken (function
        | Token.Operator op -> Some op
        | _ -> None)


let parseSingleParam =
    matchSingleToken (function
        | ValueIdentifier str -> Some <| Named str
        | Underscore -> Some <| Ignored
        | _ -> None)

let parseParamList = oneOrMore (parseSingleParam |. spaces)



//let parseOperatorExpression

let rec parseLambda =
    succeed (fun params_ body -> { params_ = params_; body = body })
    |. symbol Backslash
    |. spaces
    |= parseParamList
    |. spaces
    |. symbol Token.Arrow
    |. spaces
    |= lazyParser (fun _ -> parseSingleLineExpression)
    |. spaces

and parseOperatorExpression =
    succeed (fun left op right -> Expression.Operator (op, left, right))
    |. lookAhead (fun t ->
        match t.token with
        | Token.Operator op -> true
        | t -> false)
    |= lazyParser (fun _ -> parseSingleLineExpression)
    |. spaces
    |= parseOperator
    |. spaces
    |= lazyParser (fun _ -> parseSingleLineExpression)
    |. spaces

and parseSingleLineExpression =
    oneOf [ parseLambda |> map (Function >> ExplicitValue)
            parseOperatorExpression
            parsePrimitiveLiteral
            |> map (Primitive >> ExplicitValue) ]
//|. isEnd






////let rec singleLineExpressionParser ctx (state : ExpressionParsingState) (tokens : TokenWithContext list) =
//let rec singleLineExpressionParser (stateCtx : ExpressionParsingStateWithContext) (tokens : TokenWithContext list) =
//    let onlyUpdateState state = { stateCtx with state = state }

//    match tokens with
//    | [] ->
//        match stateCtx.isParens with
//        | Parens innerParens ->
//            { isParens = innerParens
//              state = SyntaxError ExpectingClosingParens }
//        | NoParens -> stateCtx

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

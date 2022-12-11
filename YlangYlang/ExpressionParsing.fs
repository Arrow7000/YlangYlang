module ExpressionParsing


open System.Numerics
open Lexer
open ConcreteSyntaxTree
open ParserStates
open Parser


type Context =
    | PrimitiveLiteral
    | Int
    | Float
    | StringOrCharLiteral
    | Unit
    | Operator
    | ParamList
    | Identifier
    | Lambda
    | SingleLetAssignment
    | LetBindingsAssignmentList
    | SingleValueExpression
    | CompoundExpression
    | WholeExpression
    | ParensExpression
    | NonParensExpression
    | Whitespace


/// Aka the problem
type ParserError =
    | ExpectedToken of Token
    | ExpectedString of string
    | NoParsersLeft
    | TokenNotValidHere of Token
    | PredicateDidntMatch

    /// but there were yet more tokens
    | ExpectedEndOfExpression

    /// but there were no tokens left
    | UnexpectedEndOfExpression of expected : Token option
    | MultipleErrors of ParserError list




type ExpressionParser<'a> = Parser<'a, TokenWithContext, Context, ParserError>

type ExpressionParserResult<'a> = ParseResultWithContext<'a, TokenWithContext, Context, ParserError>









let parseExpectedToken (err : ParserError) chooser : ExpressionParser<'a> =
    parseSingleToken err (fun t ->
        match chooser t.token with
        | Some x -> Ok x
        | None -> Error err)




let symbol (token : Token) =
    parseExpectedToken (ExpectedToken token) (fun t -> if t = token then Some () else None)






let spaces : ExpressionParser<unit> =
    let err = ExpectedString "whitespace"

    repeat (
        parseExpectedToken err (function
            | Token.Whitespace _ -> Some ()
            | _ -> None)
        |> addCtxToStack Whitespace
    )
    |> ignore


type PartitionedTokens =
    { includedTokens : TokenWithContext list
      tokensLeft : TokenWithContext list }

let getTilLineBreak (tokens : TokenWithContext list) =
    let rec traverser tokensGatheredSoFar tokensLeft =
        match tokensLeft with
        | [] ->
            { includedTokens = tokensGatheredSoFar
              tokensLeft = tokensLeft }
        | head :: rest ->
            match head.token with
            | Token.Whitespace char ->
                match char with
                | NewLineChar ->
                    { includedTokens = tokensGatheredSoFar
                      tokensLeft = tokensLeft }
                | Space -> traverser (head :: tokensGatheredSoFar) rest
            | _ -> traverser (head :: tokensGatheredSoFar) rest

    traverser List.empty tokens



let getBlock (tokens : TokenWithContext list) : PartitionedTokens =
    match tokens with
    | [] ->
        { includedTokens = List.empty
          tokensLeft = List.empty }

    | blockHead :: _ ->
        let rec traverser tokensGathered tokensLeft =
            match tokensLeft with
            | [] ->
                { includedTokens = tokensGathered
                  tokensLeft = List.empty }

            | head :: rest ->
                match head.token with
                | Token.Whitespace _ -> traverser (tokensGathered @ [ head ]) rest
                | _ ->
                    if head.startLine <> blockHead.startLine // to ensure we're skipping the blockHead itself
                       && head.startCol <= blockHead.startCol then
                        { includedTokens = tokensGathered
                          tokensLeft = head :: rest }

                    else
                        traverser (tokensGathered @ [ head ]) rest

        traverser List.empty tokens

///// Parse a block at a time. Takes an expression parser as input.
//let parseBlock (blockParser : ExpressionParser<'a>) : ExpressionParser<'a> =
//    Parser (fun record ->
//        let partitioned = getBlock record.tokensLeft

//        let result =
//            runWithCtx
//                blockParser
//                { prevTokens = record.prevTokens
//                  tokensLeft = partitioned.includedTokens
//                  contextStack = record.contextStack }

//        match result.parseResult with
//        | ParsingSuccess s ->
//            { parseResult = ParsingSuccess s
//              prevTokens = result.prevTokens @ partitioned.includedTokens
//              tokensLeft = result.tokensLeft @ partitioned.tokensLeft
//              contextStack = record.contextStack }
//        | NoParsingMatch x -> replaceParseResultWithCtx (NoParsingMatch x) result)


/// `end` is a keyword in F# so have to use `isEnd`
let isEnd : ExpressionParser<unit> =
    parseSimple (fun tokensLeft ->
        match tokensLeft with
        | [] -> Ok (), List.empty
        | _ -> Error ExpectedEndOfExpression, List.empty)


//Parser (fun { tokensLeft = tokensLeft } ->
//    match tokensLeft with
//    | [] -> makeParseResultWithCtx (ParsingSuccess ()) blankParseCtx
//    | _ -> makeParseResultWithCtx (NoParsingMatch [ ExpectedEndOfExpression ]) blankParseCtx)







let private parseChoosePrimitiveLiteral chooser =
    parseExpectedToken (ExpectedString "primitive literal") (function
        | Token.PrimitiveLiteral prim ->
            match chooser prim with
            | Some x -> Some x
            | None -> None
        | _ -> None)



let inline negate (n : ^a) = n * -LanguagePrimitives.GenericOne

let parseUnaryNegationOpInt : ExpressionParser<uint -> int> =
    let token = Token.Operator Operator.MinusOp

    parseExpectedToken (ExpectedToken token) (function
        | Token.Operator Operator.MinusOp -> Some (int >> negate)
        | _ -> None)


let parseUnaryNegationOpFloat : ExpressionParser<float -> float> =
    let token = Token.Operator Operator.MinusOp

    parseExpectedToken (ExpectedToken token) (function
        | Token.Operator Operator.MinusOp -> Some negate
        | _ -> None)




let parseUint =
    parseChoosePrimitiveLiteral (function
        | UintLiteral n -> Some n
        | _ -> None)

let parseInt : ExpressionParser<NumberLiteralValue> =
    fork parseUnaryNegationOpInt (succeed int) (fun op -> succeed op |= parseUint |> map IntLiteral)
    |> addCtxToStack Int



let parseUfloat =
    parseChoosePrimitiveLiteral (function
        | UfloatLiteral n -> Some n
        | _ -> None)


let parseFloat =
    fork parseUnaryNegationOpFloat (succeed id) (fun op -> (succeed op |= parseUfloat) |> map FloatLiteral)
    |> addCtxToStack Float



let parseUnit : ExpressionParser<PrimitiveLiteralValue> =
    parseExpectedToken (ExpectedToken Token.Unit) (function
        | Token.Unit -> Some UnitPrimitive
        | _ -> None)
    |> addCtxToStack Unit



let parsePrimitiveLiteral =
    oneOf [ parseFloat |> map NumberPrimitive
            parseInt |> map NumberPrimitive
            parseChoosePrimitiveLiteral (function
                | StringLiteral str -> StringPrimitive str |> Some
                | CharLiteral c -> CharPrimitive c |> Some
                | _ -> None)
            |> addCtxToStack StringOrCharLiteral

            parseUnit ]
    |> addCtxToStack PrimitiveLiteral





let parseOperator =
    parseExpectedToken (ExpectedString "operator") (function
        | Token.Operator op -> Some op
        | _ -> None)
    |> addCtxToStack Operator



let parseSingleParam =
    parseExpectedToken (ExpectedString "single param") (function
        | ValueIdentifier str -> Some <| Named str
        | Underscore -> Some <| Ignored
        | _ -> None)

let parseParamList =
    oneOrMore (parseSingleParam |. spaces)
    |> addCtxToStack ParamList



let parseIdentifier =
    parseExpectedToken (ExpectedString "identifier") (function
        | Token.ValueIdentifier n -> Some <| IdentifierName n
        | _ -> None)
    |> addCtxToStack Identifier






#nowarn "40"


/// Create a parser and a version of the parser also matching a parenthesised version of the parser
let rec parensifyParser parser =
    either
        (succeed id

         |. symbol ParensOpen
         |. spaces
         |= lazyParser (fun _ -> parensifyParser parser)
         |. spaces
         |. symbol ParensClose
         |> addCtxToStack ParensExpression)
        (parser |> addCtxToStack NonParensExpression)
    |. spaces




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
    |> addCtxToStack Lambda



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
                |> Expression.SingleValueExpression })
    |= parseIdentifier
    |= (repeat (parseSingleParam |. spaces))
    |. spaces
    |. symbol Token.AssignmentEquals
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |. spaces
    |> addCtxToStack SingleLetAssignment




and parseLetBindingsList =
    succeed (fun letBindings expr -> LetExpression (letBindings, expr))
    |. symbol LetKeyword
    |. spaces
    |= oneOrMore singleAssignment
    |. spaces
    |. symbol InKeyword
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |> addCtxToStack LetBindingsAssignmentList



and parseSingleValueExpressions : ExpressionParser<SingleValueExpression> =
    parensifyParser (
        oneOf [ parseIdentifier
                |> map SingleValueExpression.Identifier

                parseLambda |> map (Function >> ExplicitValue)

                parsePrimitiveLiteral
                |> map (Primitive >> ExplicitValue)

                parseLetBindingsList ]
        |> addCtxToStack SingleValueExpression
    )






and parseCompoundExpressions =
    parensifyParser (
        succeed (fun (expr : SingleValueExpression) opExprOpt ->
            match opExprOpt with
            | Some (opOpt, expr') ->
                match opOpt with
                | Some op ->
                    CompoundExpression.Operator (Expression.SingleValueExpression expr, (op, expr'))
                    |> Expression.CompoundExpression

                | None ->
                    FunctionApplication (Expression.SingleValueExpression expr, expr')
                    |> Expression.CompoundExpression

            | None -> Expression.SingleValueExpression expr)
        |= parseSingleValueExpressions
        |. spaces
        |= opt (
            succeed (fun opOpt expr -> opOpt, expr)
            |= opt parseOperator
            |. spaces
            |= lazyParser (fun _ -> parseExpression)
            |. spaces
        )
        |. spaces
        |> addCtxToStack CompoundExpression
    )



and parseExpression : ExpressionParser<Expression> =
    succeed id

    |. spaces
    //|= parseBlock parseCompoundExpressions
    |= parseCompoundExpressions
    |. spaces
    //|. isEnd // Only add this back in once we're only trying to parse a block at a time!
    |> addCtxToStack WholeExpression






/// Get the actual constituent string from the `TokenWithContext`s
let private formatTokensAsText (tokens : TokenWithContext list) =
    tokens
    |> List.fold (fun str token -> str + String.ofSeq token.chars) ""


/// Get a nicer formatted version of the `OneOrMultipleErrs`
let rec private makeErrsStringly errs =
    match errs with
    | OneErr err ->
        One
            {| err = err.err
               prevTokens = formatTokensAsText err.prevTokens
               contextStack = List.rev err.contextStack |}
    | MultipleErrs errs' -> Multiple (List.map makeErrsStringly errs')


/// Return a result with either the success result, or a friendlier formatted error data
let formatErrors (res : ExpressionParserResult<_>) =
    match res.parseResult with
    | NoParsingMatch errs -> Error <| makeErrsStringly errs
    | ParsingSuccess s -> Ok s

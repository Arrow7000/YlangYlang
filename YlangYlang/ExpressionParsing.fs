module ExpressionParsing


open System.Numerics
open Lexer
open ConcreteSyntaxTree
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
    | Whitespace


/// Aka the problem
type ParserError =
    | ExpectedToken of Token
    | ExpectedString of string
    | NoParsersLeft
    | TokenNotValidHere of Token
    | PredicateDidntMatch

    /// but there were yet more tokens
    | ExpectedEndOfExpression of Token list

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


type BlockInclusion =
    | IncludeSameCol
    | OnlyIncludeIndenteds


let getBlock (inclusion : BlockInclusion) (tokens : TokenWithContext list) : TokenWithContext list =
    match tokens with
    | [] -> List.empty

    | blockHead :: _ ->
        let rec traverser tokensGathered tokensLeft =
            match tokensLeft with
            | [] -> tokensGathered

            | head :: rest ->
                match head.token with
                | Token.Whitespace _ -> traverser (tokensGathered @ [ head ]) rest
                | _ ->
                    let comparisonOp =
                        match inclusion with
                        | IncludeSameCol -> (<=)
                        | OnlyIncludeIndenteds -> (<)


                    if head.startLine = blockHead.startLine
                       || comparisonOp blockHead.startCol head.startCol then
                        traverser (tokensGathered @ [ head ]) rest

                    else
                        tokensGathered

        traverser List.empty tokens



let private parseSameColBlock parser =
    splitParser
        (fun ctx ->
            let includedTokens = getBlock IncludeSameCol ctx.tokensLeft

            printfn "\nIncluded in sameCol block: %A" (includedTokens |> List.map (fun t -> t.token))

            includedTokens)
        parser

/// Parse a block at a time. Takes an expression parser as input.
let private parseIndentedColBlock parser =
    splitParser
        (fun ctx ->
            let includedTokens = getBlock OnlyIncludeIndenteds ctx.tokensLeft

            printfn "\nIncluded in indented block: %A" (includedTokens |> List.map (fun t -> t.token))

            includedTokens)
        parser

/// `end` is a keyword in F# so have to use `isEnd`
let isEnd : ExpressionParser<unit> =
    parseSimple (fun tokensLeft ->
        match tokensLeft with
        | [] -> Ok (), List.empty
        | _ -> Error (ExpectedEndOfExpression (tokensLeft |> List.map (fun t -> t.token))), List.empty)








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



let parseAssignmentValue =
    parseExpectedToken (ExpectedString "single param") (function
        | ValueIdentifier str -> Some <| Named str
        | Underscore -> Some <| Ignored
        | _ -> None)

let parseParamList =
    oneOrMore (parseAssignmentValue |. spaces)
    |> addCtxToStack ParamList



let parseIdentifier =
    parseExpectedToken (ExpectedString "identifier") (function
        | Token.ValueIdentifier n -> Some <| IdentifierName n
        | _ -> None)
    |> addCtxToStack Identifier


let parseDotGetter : ExpressionParser<IdentifierName> =
    parseExpectedToken (ExpectedString "dot accessed field") (function
        | DotGetter field -> Some field
        | _ -> None)




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
         |> map ParensedExpression
         |> addCtxToStack ParensExpression)
        parser
    |. spaces




let rec parseLambda =
    succeed (fun params_ body -> { params_ = params_; body = body })
    |. symbol Backslash
    |. commit
    |. spaces
    |= parseParamList
    |. spaces
    |. symbol Token.Arrow
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |. spaces
    |> addCtxToStack Lambda



and singleAssignment =
    parseIndentedColBlock (
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
        |= parseAssignmentValue
        |. spaces
        |= repeat (parseAssignmentValue |. spaces)
        |. spaces
        |. symbol Token.AssignmentEquals
        |. spaces
        |= lazyParser (fun _ -> parseExpression)
        |. spaces
    )
    |> addCtxToStack SingleLetAssignment



/// @TODO: need to ensure that it's ok for the in to be on the same indentation level as the let
/// @TODO: also, for some reason it only looks for one assignment and then throws an error if it doesn't find an in keyword right after... not sure why. I think it's because there's something wrong with the blockParser, that it doesn't really work correctly, cos of how it handles whitespace and so on.
and parseLetBindingsList =
    (succeed (fun letBindings expr -> LetExpression (letBindings, expr))
     |. symbol LetKeyword
     |. commit
     |. spaces
     |= oneOrMore singleAssignment
     |. spaces
     |. symbol InKeyword
     |. spaces
     |= lazyParser (fun _ -> parseExpression)
     |> addCtxToStack LetBindingsAssignmentList)


and parseRecordKeyValue =
    succeed (fun key expression -> (key, expression))

    |= parseIdentifier
    |. spaces
    |. symbol Colon
    |. spaces
    |= parseExpression


and parseRecord =
    sequence
        { symbol = symbol
          startToken = BracesOpen
          endToken = BracesClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseRecordKeyValue)
          supportsTrailingSeparator = false }




and parseSingleValueExpressions : ExpressionParser<Expression> =
    parensifyParser (
        oneOf [ parseLambda |> map (Function >> ExplicitValue)

                parseLetBindingsList

                parseRecord
                |> map (Record >> Compound >> ExplicitValue)

                parseIdentifier
                |> map SingleValueExpression.Identifier


                parsePrimitiveLiteral
                |> map (Primitive >> ExplicitValue) ]
        |> map Expression.SingleValueExpression
        |> addCtxToStack SingleValueExpression
    )



/// Parses valid expression suffixes and returns a function that, given a 'preceding' expression, generates a compound expression
and parseSuffixes : ExpressionParser<Expression -> CompoundExpression> =
    succeed (fun suffixExpr ->
        fun precedingExpression ->
            match suffixExpr with
            | Left field -> DotAccess (precedingExpression, field)
            | Right (opOpt, expr') ->
                (match opOpt with
                 | Some op -> CompoundExpression.Operator (precedingExpression, (op, expr'))

                 | None -> FunctionApplication (precedingExpression, expr')))

    |= either
        (parseDotGetter |> map Left)
        (succeed (fun opOpt expr -> Right (opOpt, expr))
         |. spaces
         |= opt parseOperator
         |. spaces
         |= lazyParser (fun _ -> parseExpression)
         |. spaces)

and parseCompoundExpressions : ExpressionParser<Expression> =
    parensifyParser (
        succeed (fun expr dotGetterOrOtherExprOpt ->
            match dotGetterOrOtherExprOpt with
            | Some suffixExpr ->
                (match suffixExpr with
                 | Left field -> DotAccess (expr, field)

                 | Right (opOpt, expr') ->
                     (match opOpt with
                      | Some op -> CompoundExpression.Operator (expr, (op, expr'))

                      | None -> FunctionApplication (expr, expr')))
                |> Expression.CompoundExpression

            | None -> expr)
        |= parseSingleValueExpressions

        |= opt (
            (either
                (parseDotGetter |> map Left)

                (succeed (fun opOpt expr -> Right (opOpt, expr))
                 |. spaces
                 |= opt parseOperator
                 |. spaces
                 |= lazyParser (fun _ -> parseExpression)
                 |. spaces))
        )
        |. spaces
    )
    |> addCtxToStack CompoundExpression



and parseExpression : ExpressionParser<Expression> =
    succeed id

    |. spaces
    |= parseCompoundExpressions
    |. spaces
    |> addCtxToStack WholeExpression


/// Just a simple re-export for easier running
let run = Parser.run

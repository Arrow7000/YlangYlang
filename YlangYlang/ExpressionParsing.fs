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
    | Suffix


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


type SuffixType =
    | NoEnd
    | DotEnd of fieldName : string
    | FuncAppEnd of Expression
    | OpEnd of (Operator * Expression)





#nowarn "40"


let parseExpectedToken (err : ParserError) chooser : ExpressionParser<'a> =
    parseSingleToken err (fun t ->
        match chooser t.token with
        | Some x -> Ok x
        | None -> Error err)




let symbol (token : Token) =
    parseExpectedToken (ExpectedToken token) (fun t -> if t = token then Some () else None)




let whitespaceToken =
    let err = ExpectedString "whitespace"

    parseExpectedToken err (function
        | Token.Whitespace _ -> Some ()
        | _ -> None)
    |> addCtxToStack Whitespace

/// Chomps through any - or no - whitespace
let spaces : ExpressionParser<unit> = repeat whitespaceToken |> ignore

/// Chomps through at least one whitespace token
let atLeastOneSpaces : ExpressionParser<unit> = oneOrMore whitespaceToken |> ignore

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

            //printfn "\nIncluded in sameCol block: %A" (includedTokens |> List.map (fun t -> t.token))

            includedTokens)
        parser

/// Parse a block at a time. Takes an expression parser as input.
let private parseIndentedColBlock parser =
    splitParser
        (fun ctx ->
            let includedTokens = getBlock OnlyIncludeIndenteds ctx.tokensLeft

            //printfn "\nIncluded in indented block: %A" (includedTokens |> List.map (fun t -> t.token))

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
    fork parseUnaryNegationOpInt (succeed int) (fun op -> parseUint |> map (op >> IntLiteral))
    |> addCtxToStack Int



let parseUfloat =
    parseChoosePrimitiveLiteral (function
        | UfloatLiteral n -> Some n
        | _ -> None)


let parseFloat =
    succeed (fun opOpt num ->
        (match opOpt with
         | Some op -> op num
         | None -> num)
        |> FloatLiteral)
    |= opt parseUnaryNegationOpFloat
    |= parseUfloat
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

let parseIdentifier =
    parseExpectedToken (ExpectedString "identifier") (function
        | Token.ValueIdentifier n -> Some <| IdentifierName n
        | _ -> None)
    |> addCtxToStack Identifier


let parensedParser parser =
    succeed id

    |. symbol ParensOpen
    |. spaces
    |= parser
    |. spaces
    |. symbol ParensClose
    |> addCtxToStack ParensExpression


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




let parseSimpleParam =
    parseExpectedToken (ExpectedString "single param") (function
        | ValueIdentifier str -> Some <| Named str
        | Underscore -> Some <| Ignored
        | Token.Unit -> Some AssignmentPattern.Unit
        | _ -> None)

/// Parses `as <identifier>` aliases and returns the alias
let parseAlias =
    succeed id

    |. spaces
    |. symbol AsKeyword
    |. spaces
    |= parseIdentifier

let parseRecordDestructuringParam =
    sequence
        { symbol = symbol
          startToken = BracesOpen
          endToken = BracesClose
          separator = Comma
          spaces = spaces
          item = parseIdentifier
          supportsTrailingSeparator = false }
    |> map DestructuredRecord

let rec parseTupleDestructuredParam = // : ExpressionParser<AssignmentPattern list> =
    let parseTupleItem = lazyParser (fun _ -> parseDelimitedParam)

    succeed (fun first second rest -> DestructuredTuple (first :: second :: rest))
    |. symbol ParensOpen
    |. spaces
    |= parseTupleItem
    |. spaces
    |. symbol Comma
    |. spaces
    |= parseTupleItem
    |. spaces
    |= repeat (
        succeed id

        |. symbol Comma
        |. spaces
        |= parseTupleItem
        |. spaces
    )
    |. symbol ParensClose
    |. spaces

and parseConsDestructuredParam =
    succeed (fun nel last -> DestructuredCons (NEL.appendList [ last ] nel))
    |= oneOrMore (
        lazyParser (fun _ -> parseTopLevelParam)
        |. spaces
        |. symbol (Lexer.Operator Operator.ConsOp)
        |. spaces
    )
    |= lazyParser (fun _ -> parseTopLevelParam)
    |. spaces

and parseTypeVariantDestructuredParam =
    let typeNameParser =
        parseExpectedToken (ExpectedString "type name") (function
            | Token.ModuleSegmentsOrQualifiedTypeOrVariant strings -> Some strings
            | Token.TypeNameOrVariantOrTopLevelModule str -> Some (NEL.make str)
            | _ -> None)

    succeed (fun typeName params' -> DestructuredTypeVariant (typeName, params'))
    |. symbol ParensOpen
    |. spaces
    |= typeNameParser
    |. spaces
    |= repeat (lazyParser (fun _ -> parseTopLevelParam) |. spaces)
    |. symbol ParensClose
    |. spaces

and parseInherentlyDelimitedParam =
    either parseRecordDestructuringParam parseTupleDestructuredParam

and parseNotInherentlyDelimitedParam =
    either parseConsDestructuredParam parseTypeVariantDestructuredParam

and parseDelimitedParam =
    succeed (fun pattern aliasOpt ->
        match aliasOpt with
        | Some alias -> Aliased (pattern, alias)
        | None -> pattern)

    |= oneOf [ parseSimpleParam

               succeed DestructuredPattern
               |= either parseNotInherentlyDelimitedParam parseInherentlyDelimitedParam

               parensedParser (lazyParser <| fun _ -> parseDelimitedParam) ]
    |. spaces
    |= opt parseAlias


// @TODO: looks like cons sequences aren't being parsed properly
and parseTopLevelParam =
    oneOf [ parseSimpleParam

            parensedParser parseDelimitedParam

            succeed DestructuredPattern
            |= parseInherentlyDelimitedParam

            parensedParser (lazyParser (fun _ -> parseTopLevelParam)) ]










let parseParamList =
    oneOrMore (parseTopLevelParam |. spaces)
    |> addCtxToStack ParamList





let parseDotGetter : ExpressionParser<IdentifierName> =
    parseExpectedToken (ExpectedString "dot accessed field") (function
        | DotGetter field -> Some field
        | _ -> None)





let combineEndParser expr end' : Expression =
    match end' with
    | NoEnd -> expr
    | DotEnd fieldName ->
        DotAccess (expr, fieldName)
        |> Expression.CompoundExpression

    | FuncAppEnd paramExpr ->
        FunctionApplication (expr, paramExpr)
        |> Expression.CompoundExpression

    | OpEnd (op, operand) ->
        CompoundExpression.Operator (expr, (op, operand))
        |> Expression.CompoundExpression








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



and singleLetAssignment =
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
        |= parseTopLevelParam
        |. spaces
        |= repeat (parseTopLevelParam |. spaces)
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
     |= oneOrMore singleLetAssignment
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
    |= lazyParser (fun _ -> parseExpression)


and parseRecord =
    sequence
        { symbol = symbol
          startToken = BracesOpen
          endToken = BracesClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseRecordKeyValue)
          supportsTrailingSeparator = false }


and parseList =
    sequence
        { symbol = symbol
          startToken = BracketsOpen
          endToken = BracketsClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseExpression)
          supportsTrailingSeparator = false }


and parseTuple =
    sequence
        { symbol = symbol
          startToken = ParensOpen
          endToken = ParensClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseExpression)
          supportsTrailingSeparator = false }


and parseSingleValueExpressions : ExpressionParser<Expression> =
    oneOf [ parseLambda |> map (Function >> ExplicitValue)

            parseLetBindingsList

            parseIdentifier
            |> map SingleValueExpression.Identifier

            parseRecord
            |> map (Record >> Compound >> ExplicitValue)

            parseList
            |> map (List >> Compound >> ExplicitValue)

            parseTuple
            |> map (Tuple >> Compound >> ExplicitValue)


            parsePrimitiveLiteral
            |> map (Primitive >> ExplicitValue) ]
    |> map Expression.SingleValueExpression
    |> addCtxToStack SingleValueExpression



and groupParser =
    either
        (succeed combineEndParser
         |= parseSingleValueExpressions
         |= endParser)
        (parensedParser (lazyParser (fun _ -> parseExpression))
         |> map ParensedExpression)


and startParser = either parseSingleValueExpressions groupParser


and endParser =
    succeed (Option.defaultValue NoEnd)
    |= opt (
        either
            (parseDotGetter |> map DotEnd)
            (succeed (fun opMaybe expr ->
                match opMaybe with
                | Some op -> OpEnd (op, expr)
                | None -> FuncAppEnd expr)
             |. spaces
             |= opt parseOperator
             |. spaces
             |= lazyParser (fun _ -> parseExpression))
    )
    |. spaces

and parseCompoundExpressions : ExpressionParser<Expression> =
    succeed combineEndParser
    |= startParser
    |= endParser
    |. spaces
    |> addCtxToStack CompoundExpression




and parseExpression : ExpressionParser<Expression> =
    succeed id

    |. spaces
    |= parseCompoundExpressions
    |. spaces
    |> addCtxToStack WholeExpression


/// Just a simple re-export for easier running
let run = Parser.run

module ExpressionParsing


open System.Numerics
open Lexer
open ConcreteSyntaxTree
open Parser


type ParamContext =
    | TopLevelParam
    | SimpleParam
    | DelimitedParam
    | InherentlyDelimitedParam
    | NotInherentlyDelimitedParam
    | ParensedParam
    | ParamAlias
    | RecordParam
    | TupleParam
    | ConsParam
    | TypeParam

type Context =
    | PrimitiveLiteral
    | Int
    | Float
    | StringOrCharLiteral
    | Unit
    | Operator
    | ParamList
    | SingleParam of ParamContext
    | Identifier
    | Lambda
    | Record
    | List
    | ParensedOrTuple
    | SingleLetAssignment
    | ValueDeclaration
    | LetBindingsAssignmentList
    | SingleValueExpression
    | CompoundExpression
    | WholeExpression
    | ParensExpression
    | Whitespace
    | Suffix



type ParserError =
    | ExpectedToken of Token
    | ExpectedString of string
    | NoParsersLeft
    | TokenNotValidHere of Token
    | PredicateDidntMatch

    /// but there were yet more tokens
    | ExpectedEndOfExpression of tokensLeft : Token list

    /// but there were no tokens left
    | UnexpectedEndOfExpression of expected : Token option
    | MultipleErrors of ParserError list




type ExpressionParser<'a> = Parser<'a, TokenWithContext, Context, ParserError>

type ExpressionParserResult<'a> = ParseResultWithContext<'a, TokenWithContext, Context, ParserError>


type OpOrFunctionApplication =
    | Operator of (Operator * Expression)
    | FunctionApplication of NEL<Expression> * OpOrFunctionApplication option




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

/// Ensure no tokens were left unparsed.
/// `end` is a keyword in F# so have to use `isEnd`
let ensureEnd : ExpressionParser<unit> =
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
    |> addCtxToStack Context.Operator

let parseIdentifier =
    parseExpectedToken (ExpectedString "identifier") (function
        | Token.Identifier ident -> Some ident
        | _ -> None)
    |> addCtxToStack Identifier

let parseSingleValueIdentifier =
    parseExpectedToken (ExpectedString "single value identifier") (function
        | Token.Identifier (SingleValueIdentifier ident) -> Some ident
        | _ -> None)

let parseSingleValueOrTypeIdentifier : ExpressionParser<UnqualIdentifier> =
    parseExpectedToken (ExpectedString "single value or type identifier") (function
        | Token.Identifier (Identifier.SingleValueIdentifier ident) -> Some (UnqualIdentifier.ValueIdentifier ident)
        | Token.Identifier (Identifier.TypeNameOrVariantOrTopLevelModule ident) ->
            Some (UnqualIdentifier.TypeIdentifier ident)
        | _ -> None)

let parensedParser parser =
    succeed id

    |. symbol ParensOpen
    |. spaces
    |= parser
    |. spaces
    |. symbol ParensClose
    |. spaces


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



let typeNameParser =
    parseExpectedToken (ExpectedString "type name") (function
        | Token.Identifier (ModuleSegmentsOrQualifiedTypeOrVariant ident) -> Some (QualifiedType ident)
        | Token.Identifier (TypeNameOrVariantOrTopLevelModule ident) -> Some (UnqualType ident)
        | _ -> None)


let parseSimpleParam =
    either
        (parseExpectedToken (ExpectedString "single param") (function
            | Token.Identifier (SingleValueIdentifier str) -> Some <| Named str
            | Underscore -> Some <| Ignored
            | Token.Unit -> Some AssignmentPattern.Unit
            | _ -> None))

        (typeNameParser
         |> map (fun typeName ->
             // @TODO: allow for using type fields also, not just a data-less type variant constructor
             DestructuredTypeVariant (typeName, List.empty)
             |> DestructuredPattern))

    |> addCtxToStack (SingleParam SimpleParam)


/// Parses `as <identifier>` aliases and returns the alias
let parseAlias =
    succeed id

    |. spaces
    |. symbol AsKeyword
    |. spaces
    |= parseSingleValueIdentifier
    |> addCtxToStack (SingleParam ParamAlias)

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
    |> addCtxToStack (SingleParam RecordParam)

let rec parseTupleDestructuredParam : ExpressionParser<DestructuredPattern> =
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
    |> addCtxToStack (SingleParam TupleParam)

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
    |> addCtxToStack (SingleParam ConsParam)

and parseTypeVariantDestructuredParam =
    succeed (fun typeName params' -> DestructuredTypeVariant (typeName, params'))
    |= typeNameParser
    |. spaces
    |= repeat (lazyParser (fun _ -> parseTopLevelParam) |. spaces)
    |. spaces
    |> addCtxToStack (SingleParam TypeParam)

and parseInherentlyDelimitedParam =
    either parseRecordDestructuringParam parseTupleDestructuredParam
    |> addCtxToStack (SingleParam InherentlyDelimitedParam)

and parseNotInherentlyDelimitedParam =
    either parseConsDestructuredParam parseTypeVariantDestructuredParam
    |> addCtxToStack (SingleParam NotInherentlyDelimitedParam)



and parseDelimitedParam =
    succeed (fun pattern aliasOpt ->
        match aliasOpt with
        | Some alias -> Aliased (pattern, alias)
        | None -> pattern)

    |= oneOf [ parseNotInherentlyDelimitedParam
               |> map DestructuredPattern

               parseInherentlyDelimitedParam
               |> map DestructuredPattern

               parseSimpleParam

               parensedParser (lazyParser <| fun _ -> parseDelimitedParam)
               |> addCtxToStack (SingleParam ParensedParam) ]
    |. spaces
    |= opt parseAlias
    |> addCtxToStack (SingleParam DelimitedParam)

and parseTopLevelParam =
    oneOf [ parseSimpleParam

            parensedParser parseDelimitedParam

            succeed DestructuredPattern
            |= parseInherentlyDelimitedParam ]
    |> addCtxToStack (SingleParam TopLevelParam)










let parseParamList =
    oneOrMore (parseTopLevelParam |. spaces)
    |> addCtxToStack ParamList





let parseDotGetter : ExpressionParser<NEL<UnqualValueIdentifier>> =
    parseExpectedToken (ExpectedString "dot accessed field") (function
        | DotFieldPath fields -> Some fields
        | _ -> None)





let rec combineEndParser expr opAndFuncParam : Expression =
    match opAndFuncParam with
    | Some (Operator (op, operandExpr)) ->
        CompoundExpression.Operator (expr, op, operandExpr)
        |> Expression.CompoundExpression
    | Some (FunctionApplication (paramExprList, nestedEndExprOpt)) ->
        let firstExpr =
            CompoundExpression.FunctionApplication (expr, paramExprList)
            |> Expression.CompoundExpression

        combineEndParser firstExpr nestedEndExprOpt
    | None -> expr



let infixOpDeclarationParser =
    let associativityParser =
        parseExpectedToken (ExpectedString "associativity signifier") (function
            | Token.Identifier (SingleValueIdentifier (UnqualValueIdentifier str)) ->
                match str with
                | "left" -> Some Left
                | "right" -> Some Right
                | "non" -> Some Non
                | _ -> None
            | _ -> None)

    succeed (fun assoc precedence op ident ->
        { name = op
          associativity = assoc
          precedence = int precedence
          value = ident })

    |. symbol InfixKeyword
    |. spaces
    |= associativityParser
    |. spaces
    |= parseUint
    |. spaces
    |. symbol ParensOpen
    |= parseOperator
    |. symbol ParensClose
    |. spaces
    |. symbol AssignmentEquals
    |. spaces
    |= parseIdentifier



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
    |> addCtxToStack Lambda



and singleLetAssignment =
    parseIndentedColBlock (
        succeed (fun name params' (expr : Expression) ->
            { bindPattern = name
              value =
                match params' with
                | [] -> expr
                | head :: tail ->
                    ({ params_ = NEL.new_ head tail
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
    succeed (fun letBindings expr -> LetExpression (letBindings, expr))
    |. symbol LetKeyword
    |. commit
    |. spaces
    |= oneOrMore singleLetAssignment
    |. spaces
    |. symbol InKeyword
    |. commit
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |> addCtxToStack LetBindingsAssignmentList


and parseRecordKeyValue =
    succeed (fun key expression -> (key, expression))
    |= parseSingleValueIdentifier
    |. spaces
    |. symbol AssignmentEquals
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
    |> addCtxToStack Record

and parseList =
    sequence
        { symbol = symbol
          startToken = BracketsOpen
          endToken = BracketsClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseExpression)
          supportsTrailingSeparator = false }
    |> addCtxToStack List


and parseTupleOrParensedExpr =
    let parseTupleItem = lazyParser (fun _ -> parseExpression)

    succeed (fun first more ->
        match more with
        | [] -> ParensedExpression first
        | head :: rest ->
            CompoundValues.Tuple (first, NEL.new_ head rest)
            |> Compound
            |> ExplicitValue
            |> Expression.SingleValueExpression)
    |. symbol ParensOpen
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
    |> addCtxToStack ParensedOrTuple



and parseSingleValueExpressions : ExpressionParser<Expression> =
    succeed Expression.SingleValueExpression
    |= oneOf [ parseLambda |> map (Function >> ExplicitValue)

               parseLetBindingsList

               parseIdentifier
               |> map SingleValueExpression.Identifier

               parseRecord
               |> map (CompoundValues.Record >> Compound >> ExplicitValue)

               parseList
               |> map (CompoundValues.List >> Compound >> ExplicitValue)

               parsePrimitiveLiteral
               |> map (Primitive >> ExplicitValue) ]
    |> addCtxToStack SingleValueExpression



and startParser =
    succeed (fun expr dotFieldsOpt ->
        match dotFieldsOpt with
        | Some dotFields ->
            DotAccess (expr, dotFields)
            |> Expression.CompoundExpression

        | None -> expr)
    |= oneOf [ parseSingleValueExpressions
               parseTupleOrParensedExpr
               parseControlFlowExpression ]
    |= opt parseDotGetter


and endParser =
    succeed id
    |= either
        (succeed (fun op expr -> Operator (op, expr))
         |= parseOperator
         |. spaces
         |= lazyParser (fun _ -> parseExpression))

        (succeed (fun params' endOpt -> FunctionApplication (params', endOpt))
         |= oneOrMore (startParser |. spaces)
         |. spaces
         |= opt (lazyParser <| fun _ -> endParser))
    |. spaces



and parseIfExpression =
    let parseExpr = lazyParser (fun _ -> parseExpression)

    succeed (fun condition ifTrue ifFalse -> IfExpression (condition, ifTrue, ifFalse))
    |. symbol IfKeyword
    |. commit
    |. spaces
    |= parseExpr
    |. spaces
    |. symbol ThenKeyword
    |. commit
    |. spaces
    |= parseExpr
    |. spaces
    |. symbol ElseKeyword
    |. commit
    |. spaces
    |= parseExpr


and parseCaseMatch =
    let parseExpr = lazyParser (fun _ -> parseExpression)

    succeed (fun exprToMatch branches -> CaseMatch (exprToMatch, branches))
    |. symbol CaseKeyword
    |. commit
    |. spaces
    |= parseExpr
    |. spaces
    |. symbol OfKeyword
    |. commit
    |. spaces
    |= oneOrMore (
        parseIndentedColBlock (
            succeed (fun assignment expr -> (assignment, expr))
            |= parseDelimitedParam
            |. spaces
            |. symbol Lexer.Arrow
            |. spaces
            |= parseExpr
            |. spaces
        )
    )


and parseControlFlowExpression =
    either parseIfExpression parseCaseMatch
    |> map ControlFlowExpression

and parseCompoundExpressions : ExpressionParser<Expression> =
    succeed combineEndParser

    |= startParser
    |. spaces
    |= opt endParser
    |. spaces
    |> addCtxToStack CompoundExpression




and parseExpression : ExpressionParser<Expression> =
    succeed id

    |. spaces
    |= parseCompoundExpressions
    |. spaces
    |> addCtxToStack WholeExpression




let parseValueDeclaration =
    parseIndentedColBlock (
        succeed (fun name params' (expr : Expression) ->
            { valueName = name
              value =
                match params' with
                | [] -> expr
                | head :: tail ->
                    ({ params_ = NEL.new_ head tail
                       body = expr })
                    |> Function
                    |> ExplicitValue
                    |> Expression.SingleValueExpression })
        |= parseSingleValueIdentifier
        |. spaces
        |= repeat (parseTopLevelParam |. spaces)
        |. spaces
        |. symbol Token.AssignmentEquals
        |. spaces
        |= lazyParser (fun _ -> parseExpression)
        |. spaces
    )
    |> addCtxToStack SingleLetAssignment









let parseTypeExpression = () // how to do this...















(* Parse module *)

let parseModuleName : ExpressionParser<QualifiedModuleOrTypeIdentifier> =
    parseExpectedToken (ExpectedString "module name") (function
        | Token.Identifier (ModuleSegmentsOrQualifiedTypeOrVariant path) -> Some path
        | Token.Identifier (TypeNameOrVariantOrTopLevelModule ident) ->
            Some (QualifiedModuleOrTypeIdentifier <| NEL.make ident)
        | _ -> None)

let parseModuleAlias : ExpressionParser<UnqualTypeOrModuleIdentifier> =
    parseExpectedToken (ExpectedString "module name") (function
        | Token.Identifier (TypeNameOrVariantOrTopLevelModule ident) -> Some ident
        | _ -> None)

let exposingAllParser =
    symbol ParensOpen
    |. spaces
    |. symbol DoubleDot
    |. spaces
    |. symbol ParensClose

let parseModuleDeclaration : ExpressionParser<ModuleDeclaration> =
    let explicitExportItem =
        succeed (fun ident exposedAll ->
            { name = ident
              exposeVariants = Option.isSome exposedAll })
        |= parseSingleValueOrTypeIdentifier
        |. spaces
        |= opt exposingAllParser
        |. spaces

    let explicitExports =
        succeed (fun firsts last -> firsts @ [ last ])
        |. symbol ParensOpen
        |. spaces
        |= repeat (
            explicitExportItem
            |. spaces
            |. symbol Comma
            |. spaces
        )
        |= explicitExportItem
        |. symbol ParensClose



    succeed (fun moduleName exports ->
        { moduleName = moduleName
          exposing =
            match exports with
            | None -> ExportExposings.ExposeAll
            | Some exports' -> ExportExposings.ExplicitExposeds exports'

        })
    |. symbol ModuleKeyword
    |. spaces
    |= parseModuleName
    |. spaces
    |. symbol ExposingKeyword
    |. spaces
    |= either (succeed None |. exposingAllParser) (succeed Some |= explicitExports)


let parseImport =
    succeed (fun moduleName alias exposeMode ->
        { moduleName = moduleName
          alias = alias
          exposingMode = exposeMode |> Option.defaultValue NoExposeds })
    |. symbol ImportKeyWord
    |. spaces
    |= parseModuleName
    |= opt (
        succeed id

        |. spaces
        |. symbol AsKeyword
        |. spaces
        |= parseModuleAlias
    )
    |= opt (
        succeed id

        |. spaces
        |. symbol ExposingKeyword
        |. spaces
        |= either
            (succeed ExposeAll |. exposingAllParser)
            (succeed (fun first others -> NEL.new_ first others |> ExplicitExposeds)
             |. symbol ParensOpen
             |. spaces
             |= parseSingleValueOrTypeIdentifier
             |= repeat (
                 succeed id

                 |. spaces
                 |. symbol Comma
                 |. spaces
                 |= parseSingleValueOrTypeIdentifier
             )
             |. spaces
             |. symbol ParensClose)
    )









let parseEntireModule =
    succeed (fun moduleDeclaration imports values ->
        { moduleDecl = moduleDeclaration
          imports = imports
          valueDeclarations = values })
    |. spaces
    |= parseModuleDeclaration
    |. spaces
    |= repeat (parseImport |. spaces)
    |. spaces
    |= repeat (parseValueDeclaration |. spaces)
    |. ensureEnd








/// Just a simple re-export for easier running
let run : ExpressionParser<'a> -> TokenWithContext list -> ExpressionParserResult<'a> =
    Parser.run

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

/// @TODO: use more of these in the actual parsers, now that we pop ctx's off the stack after the completion of a parser
[<RequireQualifiedAccess>]
type ParsingCtx =
    | ModuleDeclaration
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
    | DelimitedExpressions
    | CompoundExpression
    | WholeExpression
    | ParensExpression
    | Whitespace
    | Suffix

type PCtx = ParsingCtx


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




type ExpressionParser<'a> = Parser<'a, TokenWithSource, ParsingCtx, ParserError>

type ExpressionParserResult<'a> = ParseResultWithContext<'a, TokenWithSource, ParsingCtx, ParserError>


type OperatorSuffix = NEL<Operator * Expression>

type private OpOrFunctionApplication =
    | Operator of OperatorSuffix
    | FunctionApplication of NEL<Expression> * OperatorSuffix option




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
    |> addCtxToStack PCtx.Whitespace

/// Chomps through any - or no - whitespace
let spaces : ExpressionParser<unit> = repeat whitespaceToken |> ignore

/// Chomps through at least one whitespace token
let atLeastOneSpaces : ExpressionParser<unit> = oneOrMore whitespaceToken |> ignore

type PartitionedTokens =
    { includedTokens : TokenWithSource list
      tokensLeft : TokenWithSource list }


let getTilLineBreak (tokens : TokenWithSource list) =
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


let getBlock (inclusion : BlockInclusion) (tokens : TokenWithSource list) : TokenWithSource list =
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
    |> addCtxToStack PCtx.Int



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
    |> addCtxToStack PCtx.Float



let parseUnit : ExpressionParser<PrimitiveLiteralValue> =
    parseExpectedToken (ExpectedToken Token.Unit) (function
        | Token.Unit -> Some UnitPrimitive
        | _ -> None)
    |> addCtxToStack PCtx.Unit



let parsePrimitiveLiteral =
    oneOf [ parseFloat |> map NumberPrimitive
            parseInt |> map NumberPrimitive
            parseChoosePrimitiveLiteral (function
                | StringLiteral str -> StringPrimitive str |> Some
                | CharLiteral c -> CharPrimitive c |> Some
                | _ -> None)
            |> addCtxToStack PCtx.StringOrCharLiteral

            parseUnit ]
    |> addCtxToStack PCtx.PrimitiveLiteral





let parseOperator =
    parseExpectedToken (ExpectedString "operator") (function
        | Token.Operator op -> Some op
        | _ -> None)
    |> addCtxToStack ParsingCtx.Operator

let parseIdentifier =
    parseExpectedToken (ExpectedString "identifier") (function
        | Token.Identifier ident -> Some ident
        | _ -> None)
    |> addCtxToStack PCtx.Identifier

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
         |> addCtxToStack PCtx.ParensExpression)
        parser
    |. spaces



let parseModuleAliasOrUnqualTypeName : ExpressionParser<UnqualTypeOrModuleIdentifier> =
    parseExpectedToken (ExpectedString "module name") (function
        | Token.Identifier (TypeNameOrVariantOrTopLevelModule ident) -> Some ident
        | _ -> None)




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

        // This just parses a single type variant without any data, because the latter would require being delimited, and is therefore parsed elsewhere
        (typeNameParser
         |> map (fun typeName ->
             DestructuredTypeVariant (typeName, List.empty)
             |> DestructuredPattern))

    |> addCtxToStack (PCtx.SingleParam SimpleParam)


/// Parses `as <identifier>` aliases and returns the alias
let parseAlias =
    succeed id

    |. spaces
    |. symbol AsKeyword
    |. spaces
    |= parseSingleValueIdentifier
    |> addCtxToStack (PCtx.SingleParam ParamAlias)

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
    |> addCtxToStack (PCtx.SingleParam RecordParam)

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
    |> addCtxToStack (PCtx.SingleParam TupleParam)

and parseConsDestructuredParam =
    succeed (fun nel last -> DestructuredCons (NEL.appendList [ last ] nel))
    |= oneOrMore (
        lazyParser (fun _ -> parseTopLevelParam)
        |. spaces
        |. symbol (Lexer.Operator Operator.ConsOp)
        |. spaces
    )
    |= lazyParser (fun _ -> parseTopLevelParam)
    |> addCtxToStack (PCtx.SingleParam ConsParam)

and parseTypeVariantDestructuredParam =
    succeed (fun typeName params' -> DestructuredTypeVariant (typeName, params'))
    |= typeNameParser
    |. spaces
    |= repeat (lazyParser (fun _ -> parseTopLevelParam) |. spaces)
    |> addCtxToStack (PCtx.SingleParam TypeParam)

and parseInherentlyDelimitedParam =
    either parseRecordDestructuringParam parseTupleDestructuredParam
    |> addCtxToStack (PCtx.SingleParam InherentlyDelimitedParam)

and parseNotInherentlyDelimitedParam =
    either parseConsDestructuredParam parseTypeVariantDestructuredParam
    |> addCtxToStack (PCtx.SingleParam NotInherentlyDelimitedParam)



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
               |> addCtxToStack (PCtx.SingleParam ParensedParam) ]
    |. spaces
    |= opt parseAlias
    |> addCtxToStack (PCtx.SingleParam DelimitedParam)

and parseTopLevelParam =
    oneOf [ parseSimpleParam

            parensedParser parseDelimitedParam

            succeed DestructuredPattern
            |= parseInherentlyDelimitedParam ]
    |> addCtxToStack (PCtx.SingleParam TopLevelParam)










let parseParamList =
    oneOrMore (parseTopLevelParam |. spaces)
    |> addCtxToStack PCtx.ParamList



let parseDotGetter =
    parseExpectedToken (ExpectedString "dot getter function") (function
        | DotFieldPath fields ->
            match fields with
            | NEL.NEL (first, []) -> Some first
            | _ -> None
        | _ -> None)

let parseDotFieldPath : ExpressionParser<NEL<UnqualValueIdentifier>> =
    parseExpectedToken (ExpectedString "dot accessed fields") (function
        | DotFieldPath fields -> Some fields
        | _ -> None)


let rec private combineEndParser expr opAndFuncParam : Expression =
    match opAndFuncParam with
    | Some (Operator opAndOperandNel) ->
        CompoundExpression.Operator (expr, opAndOperandNel)
        |> CompoundExpression
    | Some (FunctionApplication (paramExprList, nestedEndExprOpt)) ->
        let firstExpr =
            CompoundExpression.FunctionApplication (expr, paramExprList)
            |> CompoundExpression

        combineEndParser firstExpr (Option.map Operator nestedEndExprOpt)
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
    |> addCtxToStack PCtx.Lambda



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
                    |> SingleValueExpression })
        |= parseTopLevelParam
        |. spaces
        |= repeat (parseTopLevelParam |. spaces)
        |. spaces
        |. symbol Token.AssignmentEquals
        |. spaces
        |= lazyParser (fun _ -> parseExpression)
        |. spaces
        |. ensureEnd // this ensures that the next let binding can't start more indented than this assignment did
    )
    |> addCtxToStack PCtx.SingleLetAssignment



and parseLetBindingsList =
    succeed (fun letBindings expr -> LetExpression (letBindings, expr))
    |. symbol LetKeyword
    |. commit
    |. spaces
    // this `parseSameColBlock` ensures that successive let bindings can't start on a lower indentation than the first let binding
    |= parseSameColBlock (oneOrMore singleLetAssignment)
    |. spaces
    |. symbol InKeyword
    |. commit
    |. spaces
    |= lazyParser (fun _ -> parseExpression)
    |> addCtxToStack PCtx.LetBindingsAssignmentList


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
          item = parseRecordKeyValue
          supportsTrailingSeparator = false }
    |> addCtxToStack PCtx.Record


and parseExtendedRecord =
    succeed (fun recordToExtend firstField otherFields ->
        RecordExtension (recordToExtend, NEL.new_ firstField otherFields))
    |. symbol BracesOpen
    |. spaces
    |= parseSingleValueIdentifier
    |. spaces
    |. symbol PipeChar
    |. spaces
    |= parseRecordKeyValue
    |. spaces
    |= repeat (
        succeed id |. spaces |. symbol Comma
        |= parseRecordKeyValue
        |. spaces
    )
    |. symbol BracesClose


and parseList =
    sequence
        { symbol = symbol
          startToken = BracketsOpen
          endToken = BracketsClose
          separator = Comma
          spaces = spaces
          item = lazyParser (fun _ -> parseExpression)
          supportsTrailingSeparator = false }
    |> addCtxToStack PCtx.List


and parseTupleOrParensedExpr =
    let parseTupleItem = lazyParser (fun _ -> parseExpression)

    succeed (fun first more ->
        match more with
        | [] -> ParensedExpression first
        | head :: rest ->
            Tuple (first, NEL.new_ head rest)
            |> Compound
            |> ExplicitValue
            |> SingleValueExpression)
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
    |> addCtxToStack PCtx.ParensedOrTuple



and parseDelimExpressions =
    succeed (fun expr dotFieldsOpt ->
        match dotFieldsOpt with
        | Some dotFields -> DotAccess (expr, dotFields) |> CompoundExpression

        | None -> expr)
    |= (either
            (succeed SingleValueExpression
             |= oneOf [ parseIdentifier |> map Identifier

                        parseRecord
                        |> map (Record >> Compound >> ExplicitValue)

                        parseExtendedRecord
                        |> map (Compound >> ExplicitValue)

                        parseList
                        |> map (List >> Compound >> ExplicitValue)

                        parsePrimitiveLiteral
                        |> map (Primitive >> ExplicitValue)

                        parseDotGetter |> map (DotGetter >> ExplicitValue) ])
            parseTupleOrParensedExpr)
    |= opt parseDotFieldPath
    |> addCtxToStack PCtx.DelimitedExpressions


and private parseFuncAppSuffix =
    succeed (fun params' opSuffix -> FunctionApplication (params', opSuffix))

    |= oneOrMore (parseDelimExpressions |. spaces)
    |. spaces
    |= opt parseOperatorSuffix

and parseOperatorSuffix =
    oneOrMore (
        succeed (fun op operand -> (op, operand))

        |= parseOperator
        |. spaces
        |= lazyParser (fun _ -> parseExpression)
    )



and startParser = parseDelimExpressions

and private endParser =
    either (parseOperatorSuffix |> map Operator) parseFuncAppSuffix



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
    |> addCtxToStack PCtx.CompoundExpression




and parseExpression : ExpressionParser<Expression> =
    succeed id

    |. spaces
    |= oneOf [ parseCompoundExpressions

               parseControlFlowExpression
               |> map SingleValueExpression

               parseLetBindingsList |> map SingleValueExpression

               parseLambda
               |> map (Function >> ExplicitValue >> SingleValueExpression) ]
    |> addCtxToStack PCtx.WholeExpression




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
                    |> SingleValueExpression })
        |= parseSingleValueIdentifier
        |. spaces
        |= repeat (parseTopLevelParam |. spaces)
        |. spaces
        |. symbol Token.AssignmentEquals
        |. commit
        |. spaces
        |= lazyParser (fun _ -> parseExpression)
    )
    |> addCtxToStack PCtx.SingleLetAssignment






(* Parse type expressions *)

let rec parseKeyAndValueType =
    succeed (fun key value -> key, value)
    |= parseSingleValueIdentifier
    |. spaces
    |. symbol Colon
    |. spaces
    |= lazyParser (fun _ -> parseTypeExpression)

and parseRecordType =
    succeed (fun keyVals -> { fields = Map.ofList keyVals })
    |. symbol BracesOpen
    |. spaces
    |= repeat parseKeyAndValueType
    |. spaces
    |. symbol BracesClose

and parseTupleTypeOrParensed =
    let parseMentionableType = lazyParser (fun _ -> parseTypeExpression)

    succeed (fun first others ->
        match others with
        | [] -> MentionableType.Parensed first
        | head :: rest -> MentionableType.Tuple { types = first, NEL.new_ head rest })
    |. symbol ParensOpen
    |. spaces
    |= parseMentionableType
    |. spaces
    |= repeat (
        succeed id

        |. symbol Comma
        |. spaces
        |= parseMentionableType
        |. spaces
    )
    |. symbol ParensClose

and parseInherentlyDelimType =
    oneOf [ parseRecordType |> map MentionableType.Record

            parseTupleTypeOrParensed

            parseSingleValueIdentifier
            |> map MentionableType.GenericTypeVar

            parseUnit |> map (always UnitType)

            typeNameParser
            |> map (fun typeName -> ReferencedType (typeName, List.empty)) ]

and parseTypeReference =
    succeed (fun typeName typeParams -> ReferencedType (typeName, typeParams))
    |= typeNameParser
    |= repeat (
        succeed id

        |. spaces
        |= parseInherentlyDelimType
    )

and parseTypePrimitive = either parseTypeReference parseInherentlyDelimType

and parseTypeExpression =
    succeed (fun prim toType ->
        match toType with
        | [] -> prim
        | head :: rest -> Arrow (prim, NEL.new_ head rest))
    |= parseTypePrimitive
    |= repeat (
        succeed id
        |. spaces
        |. symbol Lexer.Arrow
        |. spaces
        |= parseTypePrimitive
    )






let parseAliasDeclaration =
    succeed (fun ident generics expr -> Alias (ident, generics, expr))
    |. symbol AliasKeyword
    |. spaces
    |= parseModuleAliasOrUnqualTypeName
    |= repeat (succeed id |. spaces |= parseSingleValueIdentifier)
    |. spaces
    |. symbol AssignmentEquals
    |. spaces
    |= parseTypeExpression


let parseNewTypeDeclaration =
    let parseVariant =
        succeed (fun ident typeParams -> { label = ident; contents = typeParams })
        |= parseModuleAliasOrUnqualTypeName
        |= repeat (
            succeed id

            |. spaces
            |= parseInherentlyDelimType
        )

    succeed (fun ident generics firstVariant otherVariants -> Sum (ident, generics, NEL.new_ firstVariant otherVariants))
    |= parseModuleAliasOrUnqualTypeName
    |= repeat (succeed id |. spaces |= parseSingleValueIdentifier)
    |. spaces
    |. symbol AssignmentEquals
    |. spaces
    |= parseVariant
    |= repeat (
        succeed id

        |. spaces
        |. symbol PipeChar
        |. spaces
        |= parseVariant
    )


let parseTypeDeclaration =
    parseIndentedColBlock (
        succeed id

        |. symbol TypeKeyword
        |. commit
        |. spaces
        |= either parseAliasDeclaration parseNewTypeDeclaration
    )






let parseTypeDeclarations =
    succeed id

    |= repeat (succeed id |. spaces |= parseTypeDeclaration)
    |. spaces







(* Parse module *)

let parseModuleName : ExpressionParser<QualifiedModuleOrTypeIdentifier> =
    parseExpectedToken (ExpectedString "module name") (function
        | Token.Identifier (ModuleSegmentsOrQualifiedTypeOrVariant path) -> Some path
        | Token.Identifier (TypeNameOrVariantOrTopLevelModule ident) ->
            Some (QualifiedModuleOrTypeIdentifier <| NEL.make ident)
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
            | Some exports' -> ExportExposings.ExplicitExposeds exports' })
    |. symbol ModuleKeyword
    |. commit
    |. spaces
    |= parseModuleName
    |. spaces
    |. symbol ExposingKeyword
    |. commit
    |. spaces
    |= either (succeed None |. exposingAllParser) (succeed Some |= explicitExports)


let parseImport =
    succeed (fun moduleName alias exposeMode ->
        { moduleName = moduleName
          alias = alias
          exposingMode = exposeMode |> Option.defaultValue NoExposeds })
    |. symbol ImportKeyWord
    |. commit
    |. spaces
    |= parseModuleName
    |= opt (
        succeed id

        |. spaces
        |. symbol AsKeyword
        |. spaces
        |= parseModuleAliasOrUnqualTypeName
    )
    |= opt (
        succeed id

        |. spaces
        |. symbol ExposingKeyword
        |. commit
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






type TypeOrValueDeclaration =
    | TypeDeclaration of TypeDeclaration
    | ValueDeclaration of ValueDeclaration


let parseDeclarations =
    either (parseValueDeclaration |> map ValueDeclaration) (parseTypeDeclaration |> map TypeDeclaration)


let parseEntireModule =
    succeed (fun moduleDeclaration imports declarations ->
        let (typeDeclarations, valueDeclarations) =
            List.typedPartition
                (function
                | TypeDeclaration t -> Choice1Of2 t
                | ValueDeclaration v -> Choice2Of2 v)
                declarations

        { moduleDecl = moduleDeclaration
          imports = imports
          typeDeclarations = typeDeclarations
          valueDeclarations = valueDeclarations })
    |. spaces
    |= parseModuleDeclaration
    |. spaces
    |= repeat (parseImport |. spaces)
    |. spaces
    |= repeat (parseDeclarations |. spaces)
    |. ensureEnd








/// Just a simple re-export for easier running
let run : ExpressionParser<'a> -> TokenWithSource list -> ExpressionParserResult<'a> =
    Parser.run

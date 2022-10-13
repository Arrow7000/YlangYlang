module ParserStates

open Lexer
open ConcreteSyntaxTree




type SyntaxError =
    | ExpectingClosingParens
    | UnexpectedClosingParens



(*
should probably do the following:
    - group in parens first
    - group by operators next
    - lists? records? other grouped things?
    - then i think just go from left to right treating everything like function application
*)
type ExpressionParsingState =
    | Start
    | PrimitiveLiteral of PrimitiveLiteralValue
    | InParens of ExpressionParsingState
    | MinusOperator // for unary negation; might need to stick this in a substate for parsing davka just literals
    | LambdaExpression of FunctionValue
    //| OperatorEncountered of (PrimitiveLiteralValue * Operator)
    //| OperatorExpression of (PrimitiveLiteralValue * Operator * PrimitiveLiteralValue) // and subsequently make these able to be recursive so we can have full expressions with operators instead of only primitive literals


    // The error states
    | SyntaxError of SyntaxError
    | UnexpectedToken of TokenWithContext


/// To represent a natural number of parens depth
type ParensCons =
    | NoParens // we are not currently in any level of parens
    | Parens of ParensCons // We are in parens

// I wonder if we can somehow combine the parens cons thingy and internalise it into the state itself
type ExpressionParsingStateWithContext =
    { isParens : ParensCons
      state : ExpressionParsingState }










(*
@TODO: yet to cover
- destructurings of tuples, records and single-case sum type variants
*)

type TypeExportExposeMode =
    | OpenParens
    | Dots


type ExportsListParsingState =
    //| Start
    | TypeExport of IdentifierName
    | TypeExportExposeMode of TypeExportExposeMode
    | ValueExport of IdentifierName
    | Comma

type ExportExposingState =
    | OpenParens
    // actually might need to have additional parsing state DU types for these so we can keep track of exactly where we are in the parsing step, including commas, and so on
    | ExposeAll
    | Explicits of (ValueOrTypeExport list * ExportsListParsingState)
//| Exports of ExportExposingMode // can just keep accumulating in the explicit case
//| CloseParens of ExportExposingMode



type ImportState =
    | Start
    | Import
    | ModuleName of ModuleName
    // optional
    | As of ModuleName
    | ModuleAlias of
        {| moduleName : ModuleName
           localAlias : IdentifierName |}
    // also optional
    | Exposing of
        {| moduleName : ModuleName
           localAlias : IdentifierName
           state : ExportExposingMode |} // accumulate in the explicit case

type MentionableTypeParsingState =
    | Start
    | End // @TODO: this is not a real end, it's just a placeholder for now
// | And the rest...

type SumVariantParsingState =
    | Start
    | VariantName of string
    // probably need to add another state for parsing mentionable types
    | SumVariantTypeParams of
        {| variantName : string
           typeParams : MentionableType list
           state : MentionableTypeParsingState |}

type SumTypeParsingState =
    | Start
    | ParsingVariants of
        {| variants : VariantCase list
           state : SumVariantParsingState |}


type TypeDeclarationParsingState =
    | Type
    | Alias of isAlias : bool
    | TypeName of
        {| isAlias : bool
           typeName : IdentifierName |}
    | TypeParams of
        {| isAlias : bool
           typeName : IdentifierName
           typeParams : IdentifierName list |}
    | Equals of
        {| isAlias : bool
           typeName : IdentifierName
           typeParams : IdentifierName list |}
    | SumTypeParsingState of SumTypeParsingState

// not sure if we need an End state here and elsewhere? or whether it can be inferred from just moving on to the next legal token that wouldn't make sense in this context
type ParsingArrowListState =
    | Start
    | MentionableTypeParsingState of MentionableTypeParsingState
    | Arrow of MentionableType list

type ValueTypeDeclaration =
    | Name of IdentifierName
    | Colon of IdentifierName
    | ArrowList of
        {| valueName : IdentifierName
           paramsTypes : NEL<MentionableType>
           currentState : MentionableTypeParsingState |} // @TODO: probably need to chuck in a lil mentionable type parser state carrier


type ValueDeclarationParsingState =
    | Name of IdentifierName // either for the value itself or the type, we don't know yet
    // optional
    | ValueTypeDeclaration of ValueTypeDeclaration
    // NameValue is for when we've already got the type declaration of the value, and now we're carrying that forward into the actual value declaration
    | NameValue of
        {| valueName : IdentifierName
           paramsTypes : NEL<MentionableType> |}
    | Params of
        {| valueName : IdentifierName
           params_ : IdentifierName list |}
    | Equals of
        {| valueName : IdentifierName
           params_ : IdentifierName list |}
    | Body of ExpressionParsingState'

// @TODO: implement these two
//and MentionableTypeParsingState = | TBD // ...
and ExpressionParsingState' = | NotSureYet // ... point to the other one further down later









type TypeOrValueParsingState =
    | TypeParsing of TypeDeclarationParsingState
    | ValueParsing of ValueDeclarationParsingState

type ValueAndTypeDeclarations =
    { typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

// This file is about parsing the token list into a concrete syntax tree
// after parsing the entire file is done we can construct a full YlModule record!
type FileParsingState =
    | Start
    | ModuleDeclaration
    | ModuleName of ModuleName
    | Exposing of ModuleName
    | ExposingList of
        {| moduleName : ModuleName
           exposing : ExportExposingState |}
    //exports : Exports
    | Imports of
        {| moduleName : ModuleName
           exports : Exports
           imports : Import list
           importState : ImportState |}
    | ValueAndTypeDeclarations of
        {| moduleName : ModuleName
           exports : Exports
           imports : Import list
           types : TypeDeclaration list
           values : ValueDeclaration list
           currentState : TypeOrValueParsingState |}

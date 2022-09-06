module Parsing



open Lexer
open ParserTypes



type ExposingState =
    | OpenParens
    // actually might need to have additional parsing state DU types for these so we can keep track of exactly where we are in the parsing step, including commas, and so on
    | Exports of ExportExposingMode // can just keep accumulating in the explicit case
    | CloseParens of ExportExposingMode



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



type SumTypeParsingState = FirstVariant of {| variantName : IdentifierName |}

type TypeParsingState =
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

and ValueTypeDeclaration =
    | Name of IdentifierName
    | Colon of IdentifierName
    | ArrowList of
        {| valueName : IdentifierName
           paramsTypes : NEL<MentionableType>
           currentState : MentionableTypeParsingState |} // @TODO: probably need to chuck in a lil mentionable type parser state carrier


and ValueParsingState =
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
    | Body of ExpressionParsingState

// @TODO: implement these two
and MentionableTypeParsingState = | TBD // ...
and ExpressionParsingState = | NotSureYet // ...

type TypeOrValueParsingState =
    | TypeParsing of TypeParsingState
    | ValueParsing of ValueParsingState

type ValueAndTypeDeclarations =
    { typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

// This file is about parsing the token list into a concrete syntax tree
// after parsing the entire file is done we can construct a full YlModule record!
type FileParsingState =
    | Start
    | ModuleDeclaration
    | ModuleName of ModuleName
    | Exposing of
        {| moduleName : ModuleName
           exposing : ExposingState |}
    | Imports of
        {| moduleName : ModuleName
           exposing : ExposingState
           imports : ImportState |}
    | ValueAndTypeDeclarations of
        {| moduleName : ModuleName
           exposing : ExposingState
           imports : ImportState
           currentState : TypeOrValueParsingState |}

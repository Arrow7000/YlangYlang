﻿module Parsing



open Lexer
open ParserTypes



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
    | Body of ExpressionParsingState

// @TODO: implement these two
//and MentionableTypeParsingState = | TBD // ...
and ExpressionParsingState = | NotSureYet // ...



//and PrimitiveParsingState =











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

// @TODO: finish all the various states for when parsing is interrupted mid-state
let areYouDoneParsing state =
    match state with
    | ValueAndTypeDeclarations contents ->
        let everythingSoFar =
            { YlModule.moduleName = contents.moduleName
              exports = contents.exports
              imports = contents.imports
              typeDeclarations = contents.types
              valueDeclarations = contents.values }

        match contents.currentState with
        | TypeParsing parsingState ->
            match parsingState with
            | SumTypeParsingState stps ->
                match stps with
                | ParsingVariants contents ->
                    match contents.state with
                    | SumVariantTypeParams tp ->
                        match tp.state with
                        | End -> Ok everythingSoFar
                        | _ -> Error "Still in the middle of parsing"
                    | _ -> Error "Still in the middle of parsing"
                | _ -> Error "Still in the middle of parsing"
            | _ -> Error "Still in the middle of parsing"
        | _ -> Error "Still in the middle of parsing"
    | _ -> Error "Still in the middle of parsing"


//| Imports contents ->
//    Ok {
//        YlModule.moduleName = contents.moduleName
//        exports = contents.exports
//        imports = contents.imports
//        typeDeclarations = contents.types
//        valueDeclarations = contents.values
//    }

//type ParsingResult<'a> = Result<'a, string> // string for now


//let rec parser (tokens : TokenWithContext list) =
//    let rec subParser (tokensLeft : TokenWithContext list) state =
//        match tokensLeft with
//        | [] -> areYouDoneParsing state
//        //match state with
//        //|    ValueAndTypeDeclarations contents ->
//        //        Ok {
//        //            YlModule.moduleName = contents.moduleName
//        //            exports = contents.exports
//        //            imports = contents.imports
//        //            typeDeclarations = contents.types
//        //            valueDeclarations = contents.values
//        //        }
//        //| Imports contents ->
//        //    Ok {
//        //        YlModule.moduleName = contents.moduleName
//        //        exports = contents.exports
//        //        imports = contents.imports
//        //        typeDeclarations = contents.types
//        //        valueDeclarations = contents.values
//        //    }
//        //
//        // @TODO:  do the thing!
//        //| _ -> Error "fill in the rest"
//        | tokenCtx :: rest ->
//            match tokenCtx.token with
//            | Whitespace _ -> subParser rest state
//            | _ ->
//                match state with
//                | Start ->
//                    match tokenCtx.token with
//                    | ModuleKeyword ->
//                        if tokenCtx.startCol = uint 0 then
//                            //Error "fill in the rest"
//                            subParser rest ModuleDeclaration
//                        else
//                            Error "Module declaration should be at the start of the line"
//                    | _ -> Error $"Module declaration has to be the first thing in the file!"

//                | ModuleDeclaration ->
//                    match tokenCtx.token with
//                    | TypeNameOrVariantOrTopLevelModule str ->
//                        NEL.make str
//                        |> FileParsingState.ModuleName
//                        |> subParser rest

//                    | ModuleSegmentsOrQualifiedTypeOrVariant list ->
//                        list
//                        |> FileParsingState.ModuleName
//                        |> subParser rest
//                    | _ -> Error "Expected a module name next"
//                | ModuleName name ->
//                    match tokenCtx.token with
//                    | ExposingKeyword -> subParser rest (Exposing name)
//                    | _ -> Error "Expecting the exposing keyword next"
//                | Exposing name ->
//                    match tokenCtx.token with
//                    | ParensOpen ->
//                        ExposingList
//                            {| moduleName = name
//                               exposing = OpenParens |}
//                        |> subParser rest
//                    | _ -> Error "Expecting opening parenthesis next"
//                | ExposingList subState ->
//                    match subState.exposing with
//                    | ExportExposingState.OpenParens ->
//                        let exportTypeResult =
//                            match tokenCtx.token with
//                            | DoubleDot -> Ok ExposeAll
//                            | TypeNameOrVariantOrTopLevelModule str ->
//                                Explicits ([ ValueOrTypeExport.ValueExport str ], ValueExport str)
//                                |> Ok
//                            | ValueIdentifier str ->
//                                Explicits ([ ValueOrTypeExport.TypeExport str ], TypeExport str)
//                                |> Ok
//                            | _ -> Error "Expecting either a .. or a list of explicit exports"

//                        match exportTypeResult with
//                        | Error e -> Error e
//                        | Ok exportType ->

//                            ExposingList
//                                {| moduleName = subState.moduleName
//                                   exposing = Exports exportType |}
//                            |> subParser rest
//                    | ExposeAll ->
//                        match exports with
//                        | ExposeAll ->
//                            match tokenCtx.token with
//                            | ParensClose ->
//                                Imports
//                                    {| moduleName = subState.moduleName
//                                       exports = ExportAll
//                                       imports = List.empty
//                                       importState = ImportState.Start |}
//                                |> subParser rest
//                            | _ -> Error "Was expecting to see a closing parenthesis now"
//                        | Explicits list ->
//                            match tokenCtx.token with
//                            | ParensClose ->
//                                Imports
//                                    {| moduleName = subState.moduleName
//                                       exports = ExportExplicits list
//                                       imports = List.empty
//                                       importState = ImportState.Start |}
//                                |> subParser rest
//                            | TypeNameOrVariantOrTopLevelModule str ->
//                                // @TODO: parse the parentheses and double dots for exposing sum type variants also
//                                Error "TODO: implement parse exposing sum type variants"
//                            | ValueIdentifier str ->
//                                let newList = list @ [ ValueExport str ]

//                                ExposingList
//                                    {| subState with
//                                        exposing = Exports (ExplicitExposeds newList) |}
//                                |> subParser rest
//                            | _ -> Error "Was expecting to see ... something"


//                //| _ -> Error "Expecting to see the module's exports in parentheses"


//                //subParser rest (Exposing {|moduleName = name; exports = |})
//                | _ -> Error "fill in the rest"

//    subParser tokens Start

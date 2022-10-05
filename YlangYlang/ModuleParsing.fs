module ModuleParsing


open Lexer
open ParserTypes
open ParserStates
open ExpressionParsing


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

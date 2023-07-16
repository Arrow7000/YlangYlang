module TypedNameResolution


open Lexer

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open QualifiedSyntaxTree.Names
open System







type NamesMaps =
    { typeDeclarations : T.TypeDeclarations
      typeConstructors : T.TypeConstructors
      typeParams : T.TypeParams
      values : T.ValueDeclarations
      valueTypes : T.ValueTypeDeclarations
      infixOperators : T.InfixOps }


//let getTypeDeclarations names : TypeDeclarations = names.typeDeclarations
//let getTypeConstructors names : TypeConstructors = names.typeConstructors
//let getTypeParams names : Q.ResolvedTypeParams = names.typeParams
//let getValues names : ValueDeclarations = names.values


let empty : NamesMaps =
    { typeDeclarations = Map.empty
      typeConstructors = Map.empty
      typeParams = Map.empty
      values = Map.empty
      valueTypes = Map.empty
      infixOperators = Map.empty }



let findTypeDeclaration (name : UpperIdent) { typeDeclarations = nameMap } = Map.tryFind name nameMap

let findTypeConstructor (name : UpperIdent) { typeConstructors = nameMap } = Map.tryFind name nameMap

let findTypeParam (name : LowerIdent) ({ typeParams = nameMap } : NamesMaps) = Map.tryFind name nameMap


(* @TODO: hmm it's actually a bit problematic to make both the value and value type annotation getters be non-nullable, because it's possible that only a value or only a type annotation has been declared, in which case one of these *will* fail... *)

let findValue (name : LowerIdent) ({ values = nameMap } : NamesMaps) = Map.tryFind name nameMap






/// This constructs the base names map for a module - to be used as a foundation for adding any declared names in any sub-scopes on
let makeNamesMapFromAllModuleTopLevelDeclarations (ylModule : T.YlModule) : NamesMaps =
    let getConstructorFromType
        (typeName : UpperIdent)
        (type_ : T.TypeDeclaration)
        : (UpperIdent * T.VariantConstructor) list =
        match type_.typeDeclaration with
        | T.Sum variants ->
            variants
            |> NEL.map (fun variant ->
                variant.label,
                { T.VariantConstructor.variantCase = variant
                  T.VariantConstructor.typeParamsMap = type_.typeParamsMap
                  T.VariantConstructor.typeParamsList = type_.typeParamsList
                  T.VariantConstructor.allVariants = variants
                  T.VariantConstructor.typeName = typeName })
            |> NEL.toList
        | T.Alias _ -> List.empty


    let constructors : T.TypeConstructors =
        ylModule.types
        |> Map.toList
        |> List.collect (fun (typeName, types) ->
            SOD.map (getConstructorFromType typeName) types
            |> SOD.toList
            |> List.collect id)
        |> NameResolution.makeSodMapFromList


    { typeDeclarations = ylModule.types
      typeConstructors = constructors
      typeParams = Map.empty
      values =
        ylModule.values
        |> Map.map (fun _ values -> SOD.map T.TopLevelName values)
      valueTypes = ylModule.valueTypes
      infixOperators =
        ylModule.infixOperators
        |> Map.map (fun _ infixOps -> SOD.map S.UserDefined infixOps) }



(* Functions to roll together to provide the dicts for sub-nodes *)

//let addTopLevelValues (values : Map<LowerIdent, SOD<T.TypedExpr>>) (names : NamesMaps) =
//    { names with
//        values =
//            values
//            |> Map.map (fun _ values -> SOD.map T.TopLevelName values)
//            |> NameResolution.combineTwoReferenceMaps names.values }

let addLetBindings (bindings : T.LetDeclarationNames) (names : NamesMaps) =
    { names with
        values =
            bindings
            |> Map.map (fun _ values -> SOD.map T.LocalName values)
            |> NameResolution.combineTwoReferenceMaps names.values }



//let addInfixOps (infixOperators : Map<LowerIdent, SOD<Cst.InfixOpDeclaration>>) (names : NamesMaps) =
//    { names with
//        infixOperators =
//            infixOperators
//            |> Map.map (fun _ values -> SOD.map S.UserDefined values)
//            |> NameResolution.combineTwoReferenceMaps names.infixOperators }


let addTypeParams (typeParams : T.TypeParams) (names : NamesMaps) =
    { names with typeParams = NameResolution.combineTwoReferenceMaps typeParams names.typeParams }


/// Also suitable for pattern match branches
let addFunctionParams (params_ : T.FunctionOrCaseMatchParam) (names : NamesMaps) =
    { names with
        values =
            params_.namesMap
            |> Map.map (fun _ param_ -> SOD.map T.Param param_)
            |> NameResolution.combineTwoReferenceMaps names.values }












//let addModuleDeclarations
//    (moduleName : QualifiedModuleOrTypeIdentifier)
//    (declarations : Cst.Declaration list)
//    (names : NamesMaps)
//    : NamesMaps =
//    declarations
//    |> List.fold
//        (fun namesMap decl ->
//            match decl with
//            | S.ImportDeclaration import -> failwith "@TODO: cross-module resolution is not supported yet"
//            | S.TypeDeclaration (resolved, typeName, typeDecl) ->
//                match typeDecl.typeDeclaration with
//                | T.Alias alias ->
//                    { namesMap with
//                        typeDeclarations = Map.add resolved (typeName.node, typeDecl) namesMap.typeDeclarations }

//                | T.Sum variants ->
//                    { namesMap with
//                        typeParams = Map.merge typeDecl.typeParamsMap namesMap.typeParams

//                        typeDeclarations = Map.add resolved (typeName.node, typeDecl) namesMap.typeDeclarations

//                        typeConstructors =
//                            variants
//                            |> NEL.map (fun variant ->
//                                fst variant.node.label,
//                                (typeName.node,
//                                 { variantCase = variant.node
//                                   typeParamsMap = typeDecl.typeParamsMap
//                                   typeParamsList = typeDecl.typeParamsList
//                                   allVariants = NEL.map S.getNode variants
//                                   fullTypeName =
//                                     resolved,
//                                     FullyQualifiedUpperIdent (NameResolution.reifyModuleName moduleName, typeName.node) }))
//                            |> NEL.toList
//                            |> Map.ofList }

//            | S.ValueDeclaration (resolved, value) ->
//                { namesMap with values = Map.add resolved (TopLevelName value) namesMap.values }


//            | S.ValueTypeAnnotation (resolved, ann) ->
//                let ident = ann.valueName.node
//                { namesMap with valueTypes = Map.add resolved (ident, ann) namesMap.valueTypes })
//        names











let getInferredTypeFromLowercaseName (lowerCaseName : T.LowerCaseName) : T.TypeJudgment =
    match lowerCaseName with
    | T.Param param_ -> Ok param_.inferredType
    | T.LocalName local -> local.assignedExpression.inferredType
    | T.TopLevelName top -> top.inferredType

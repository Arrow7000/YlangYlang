module TypedNameResolution


open Lexer

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open QualifiedSyntaxTree.Names
open System





type VariantConstructor =
    { typeParamsList : ResolvedTypeParam list
      typeParamsMap : Q.ResolvedTypeParams
      variantCase : T.VariantCase
      allVariants : NEL<T.VariantCase>
      fullTypeName : ResolvedType * FullyQualifiedUpperIdent
    //typeName : ResolvedType * UpperIdent
     }





type LowerCaseName =
    | LocalName of
        {| ident : LowerIdent
           tokens : TokenWithSource list
           destructurePath : PathToDestructuredName
           assignedExpression : T.TypedExpr |}
    | Param of T.Param
    | TopLevelName of T.ValueDeclaration


/// @TODO: we probably want to have a way of keeping track of what the name (both locally referenced and fully qualified) of the type is
type ResolvedTypeDeclarations = Map<ResolvedType, UpperIdent * T.TypeDeclaration>

type ResolvedTypeConstructors = Map<ResolvedTypeConstructor, UpperIdent * VariantConstructor>

type ResolvedValueDeclarations = Map<ResolvedValue, LowerCaseName>

type ResolvedValueTypeDeclarations = Map<ResolvedValue, LowerIdent * T.ValueAnnotation>



type NamesMaps =
    { typeDeclarations : ResolvedTypeDeclarations
      typeConstructors : ResolvedTypeConstructors
      typeParams : Q.ResolvedTypeParams
      values : ResolvedValueDeclarations
      valueTypes : ResolvedValueTypeDeclarations }



let addLetBindings (bindings : T.LetDeclarationNames) (names : NamesMaps) =
    { names with
        values =
            bindings
            |> Map.map (fun _ value ->
                LocalName
                    {| ident = value.ident
                       tokens = value.tokens
                       destructurePath = value.destructurePath
                       assignedExpression = value.assignedExpression |})
            |> Map.merge names.values }



let getTypeDeclarations names : ResolvedTypeDeclarations = names.typeDeclarations
let getTypeConstructors names : ResolvedTypeConstructors = names.typeConstructors
let getTypeParams names : Q.ResolvedTypeParams = names.typeParams
let getValues names : ResolvedValueDeclarations = names.values


let empty : NamesMaps =
    { typeDeclarations = Map.empty
      typeConstructors = Map.empty
      typeParams = Map.empty
      values = Map.empty
      valueTypes = Map.empty }



let findTypeDeclaration (name : ResolvedType) { typeDeclarations = nameMap } = Map.find name nameMap

let findTypeConstructor (name : ResolvedTypeConstructor) { typeConstructors = nameMap } = Map.find name nameMap

let findTypeParam (name : ResolvedTypeParam) ({ typeParams = nameMap } : NamesMaps) = Map.find name nameMap


(* @TODO: hmm it's actually a bit problematic to make both the value and value type annotation getters be non-nullable, because it's possible that only a value or only a type annotation has been declared, in which case one of these *will* fail... *)

let findValue (name : ResolvedValue) ({ values = nameMap } : NamesMaps) = Map.find name nameMap






let addModuleDeclarations
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (declarations : T.Declaration list)
    (names : NamesMaps)
    : NamesMaps =
    declarations
    |> List.fold
        (fun namesMap decl ->
            match decl with
            | T.ImportDeclaration import -> failwith "@TODO: cross-module resolution is not supported yet"
            | T.TypeDeclaration (resolved, typeName, typeDecl) ->
                match typeDecl.typeDeclaration with
                | T.Alias alias ->
                    { namesMap with
                        typeDeclarations = Map.add resolved (typeName.node, typeDecl) namesMap.typeDeclarations }

                | T.Sum variants ->
                    { namesMap with
                        typeParams = Map.merge typeDecl.typeParamsMap namesMap.typeParams

                        typeDeclarations = Map.add resolved (typeName.node, typeDecl) namesMap.typeDeclarations

                        typeConstructors =
                            variants
                            |> NEL.map (fun variant ->
                                fst variant.node.label,
                                (typeName.node,
                                 { variantCase = variant.node
                                   typeParamsMap = typeDecl.typeParamsMap
                                   typeParamsList = typeDecl.typeParamsList
                                   allVariants = NEL.map S.getNode variants
                                   fullTypeName =
                                     resolved,
                                     FullyQualifiedUpperIdent (NameResolution.reifyModuleName moduleName, typeName.node) }))
                            |> NEL.toList
                            |> Map.ofList }

            | T.ValueDeclaration (resolved, value) ->
                { namesMap with values = Map.add resolved (TopLevelName value) namesMap.values }


            | T.ValueTypeAnnotation (resolved, ann) ->
                let ident = ann.valueName.node
                { namesMap with valueTypes = Map.add resolved (ident, ann) namesMap.valueTypes })
        names






let addResolvedTypeParams (typeParams : Q.ResolvedTypeParams) (names : NamesMaps) =
    { names with typeParams = Map.merge typeParams names.typeParams }


let addFunctionParams (params_ : T.FunctionOrCaseMatchParams) (names : NamesMaps) =
    { names with
        values =
            Map.merge
                (params_.namesMap
                 |> Map.map (fun resolved param_ -> Param param_))
                names.values }








let getInferredTypeFromLowercaseName (lowerCaseName : LowerCaseName) : T.TypeJudgment =
    match lowerCaseName with
    | Param param_ -> Ok param_.inferredType
    | LocalName local -> local.assignedExpression.inferredType
    | TopLevelName top -> top.value.node.inferredType


let getIdentFromLowercaseName (lowerCaseName : LowerCaseName) : LowerIdent =
    match lowerCaseName with
    | Param param_ -> param_.ident
    | LocalName local -> local.ident
    | TopLevelName top -> top.valueName.node

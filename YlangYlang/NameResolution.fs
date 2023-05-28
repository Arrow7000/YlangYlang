module NameResolution

open Lexer
open SyntaxTree

module Cst = ConcreteSyntaxTree
open QualifiedSyntaxTree






/// Type that describes the path to where a given name is declared.
/// @TODO: hmmm how do we capture the fact that a name is the nth parameter of a function...? Maybe we don't need to actually? Because the name itself references it?
type PathToDestructuredName =
    | SimpleName
    | InverseRecord
    | InverseTuple of index : uint * child : PathToDestructuredName
    | InverseCons of index : uint * child : PathToDestructuredName
    | InverseTypeVariant of constructor : TypeOrModuleIdentifier * index : uint * child : PathToDestructuredName






type LowerCaseTopLevel =
    { tokens : TokenWithSource list
      assignedExpression : Cst.Expression
      fullName : FullyQualifiedTopLevelLowerIdent }

type LowerCaseName =
    | LocalName of
        {| tokens : TokenWithSource list
           assignmentPattern : PathToDestructuredName
           assignedExpression : Cst.Expression |}
    | Param of
        {| tokens : TokenWithSource list
           assignmentPattern : PathToDestructuredName |}
    | TopLevelName of LowerCaseTopLevel





type VariantConstructor =
    { typeName : TypeOrModuleIdentifier
      typeDeclaration : Cst.NewTypeDeclaration
      variantParams : Cst.MentionableType list
      fullName : FullyQualifiedUpperIdent }

type TypeDeclaration =
    { typeDecl : Cst.TypeDeclaration
      fullName : FullyQualifiedUpperIdent
      tokens : TokenWithSource list }




type TypeDeclarations = Map<TypeOrModuleIdentifier, SingleOrDuplicate<TokenWithSource list * TypeDeclaration>>

type TypeConstructors = Map<TypeOrModuleIdentifier, SingleOrDuplicate<TokenWithSource list * VariantConstructor>>

type TypeParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list>>

type ValueDeclarations = Map<ValueIdentifier, SingleOrDuplicate<LowerCaseName>>

type ValueTypeDeclarations = Map<ValueIdentifier, SingleOrDuplicate<TokenWithSource list * Cst.MentionableType>>



type NamesInScope =
    { typeDeclarations : TypeDeclarations
      typeConstructors : TypeConstructors
      typeParams : TypeParams
      valueDeclarations : ValueDeclarations
      valueTypeDeclarations : ValueTypeDeclarations }


let getTypeDeclarations names : TypeDeclarations = names.typeDeclarations
let getTypeConstructors names : TypeConstructors = names.typeConstructors
let getTypeParams names : TypeParams = names.typeParams
let getValueDeclarations names : ValueDeclarations = names.valueDeclarations
let getValueTypeDeclarations names : ValueTypeDeclarations = names.valueTypeDeclarations


let private getFromMap name =
    Map.tryFind name
    // @TODO: might need to bubble up that there are duplicates here, to prevent shadowing - but only for things in the same module, top-level declarations are allowed to be duplicated, even if the namespaces are imported wholesale.
    // @TODO: need to look into if explicit imports are allowed if that leads to a name clash.
    >> Option.map SingleOrDuplicate.getFirst


let tryFindTypeDeclaration (name : TypeOrModuleIdentifier) { typeDeclarations = nameMap } = getFromMap name nameMap

let tryFindTypeConstructor (name : TypeOrModuleIdentifier) { typeConstructors = nameMap } = getFromMap name nameMap

let tryFindTypeParam name ({ typeParams = nameMap } : NamesInScope) = getFromMap name nameMap

let tryFindValue (name : ValueIdentifier) { valueDeclarations = nameMap } : LowerCaseName option =
    getFromMap name nameMap

let tryFindValueTypeDeclarations (name : ValueIdentifier) { valueTypeDeclarations = nameMap } = getFromMap name nameMap


let tryFindValueAndTypeDeclaration
    (name : ValueIdentifier)
    { valueDeclarations = vals
      valueTypeDeclarations = types }
    =
    getFromMap name vals, getFromMap name types |> Option.map snd



let empty =
    { typeDeclarations = Map.empty
      typeConstructors = Map.empty
      typeParams = Map.empty
      valueDeclarations = Map.empty
      valueTypeDeclarations = Map.empty }






/// Useful lil' map to roll up all param declarations more easily
type ParamsInScope = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * PathToDestructuredName>>

/// Primarily useful to set sub-destructured params into their sub-path reference paths
let mapResolvedParams f (resolvedParams : ParamsInScope) : ParamsInScope =
    Map.map (fun _ -> SingleOrDuplicate.map (fun (tokens, reference) -> tokens, f reference)) resolvedParams


let addNewParamReference ident path (resolvedParams : ParamsInScope) : ParamsInScope =
    Map.change
        ident.node
        (fun oldValueOpt ->
            let newValueAndPath = ident.source, path

            match oldValueOpt with
            | None -> Some (Single newValueAndPath)
            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList))
        resolvedParams



let reifyModuleName (QualifiedModuleOrTypeIdentifier moduleName) =
    moduleName
    |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
    |> ModulePath

let reifyUpper moduleName (UnqualTypeOrModuleIdentifier topLevelIdent) =
    FullyQualifiedUpperIdent (reifyModuleName moduleName, UpperIdent topLevelIdent)

let reifyLower moduleName (UnqualValueIdentifier topLevelIdent) =
    FullyQualifiedTopLevelLowerIdent (reifyModuleName moduleName, LowerIdent topLevelIdent)

/// This stores a new declared type/value/param/etc in its map...
/// @TODO: but question is... currently it stores it solely in the unqualified form (I think), but it should also store it in its fully qualified, and locally findable form - i.e. if it's been explicitly imported,referenced under a module alias, namespace opened, etc.
/// So hmmm..... maybe we should instead store it under its full namespace *only*, and have separate mappings for the locally accessible versions
let addNewReference (declaredIdent : CstNode<'name>) (value : 'v) (map : Map<'name, SingleOrDuplicate<'v>>) =
    map
    |> Map.change declaredIdent.node (fun oldValueOpt ->
        match oldValueOpt with
        | Some (Single oldRef) -> Some (Duplicate <| TOM.make value oldRef)
        | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons value refList)
        | None -> Some (Single value))

let addNewRefWithTokens
    (ident : CstNode<'name>)
    (value : 'v)
    (map : Map<'name, SingleOrDuplicate<TokenWithSource list * 'v>>)
    =
    addNewReference ident (ident.source, value) map


let addNewTypeParam (name : CstNode<UnqualValueIdentifier>) (names : NamesInScope) =
    { names with typeParams = addNewReference name name.source names.typeParams }

let addNewTypeDeclaration
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (name : CstNode<UnqualTypeOrModuleIdentifier>)
    (value : Cst.TypeDeclaration)
    (names : NamesInScope)
    =
    { names with
        typeDeclarations =
            addNewRefWithTokens
                (mapNode UnqualType name)
                { typeDecl = value
                  fullName = reifyUpper moduleName name.node
                  tokens = name.source }
                names.typeDeclarations }

let addTypeConstructor
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (variantName : CstNode<UnqualTypeOrModuleIdentifier>)
    (variantParams : Cst.MentionableType list)
    (typeName : TypeOrModuleIdentifier)
    (typeDeclaration : Cst.NewTypeDeclaration)
    (names : NamesInScope)
    =
    { names with
        typeConstructors =
            addNewRefWithTokens
                (mapNode UnqualType variantName)
                { typeName = typeName
                  typeDeclaration = typeDeclaration
                  variantParams = variantParams
                  fullName = reifyUpper moduleName variantName.node }
                names.typeConstructors }

let addValue name value names : NamesInScope =
    { names with valueDeclarations = addNewReference name value names.valueDeclarations }

let addValueTypeDeclaration name value names =
    { names with valueTypeDeclarations = addNewRefWithTokens name value names.valueTypeDeclarations }




let combineTwoReferenceMaps map1 map2 =
    let mapFolder
        (acc : Map<'a, SingleOrDuplicate<'b>>)
        (key : 'a)
        (value : SingleOrDuplicate<'b>)
        : Map<'a, SingleOrDuplicate<'b>> =
        Map.change
            key
            (fun oldValueOpt ->
                match oldValueOpt with
                | Some oldVal ->
                    match oldVal, value with
                    | Single oldRef, Single newRef -> Some (Duplicate <| TOM.make newRef oldRef)

                    | Single singleRef, Duplicate duplRefs
                    | Duplicate duplRefs, Single singleRef -> Some (Duplicate <| TOM.cons singleRef duplRefs)

                    | Duplicate a, Duplicate b -> Some (Duplicate <| TOM.append a b)

                | None -> Some value)
            acc

    Map.fold mapFolder map1 map2


let combineReferenceMaps (mapList : Map<'a, SingleOrDuplicate<'b>> seq) : Map<'a, SingleOrDuplicate<'b>> =
    Seq.fold combineTwoReferenceMaps Map.empty mapList



let combineTwoResolvedNamesMaps (names1 : NamesInScope) (names2 : NamesInScope) =
    { typeDeclarations = combineTwoReferenceMaps names1.typeDeclarations names2.typeDeclarations
      typeConstructors = combineTwoReferenceMaps names1.typeConstructors names2.typeConstructors
      typeParams = combineTwoReferenceMaps names1.typeParams names2.typeParams
      valueDeclarations = combineTwoReferenceMaps names1.valueDeclarations names2.valueDeclarations
      valueTypeDeclarations = combineTwoReferenceMaps names1.valueTypeDeclarations names2.valueTypeDeclarations }


let combineResolvedNamesMaps (mapList : NamesInScope seq) =
    let typeDeclarations = Seq.map getTypeDeclarations mapList
    let typeConstructors = Seq.map getTypeConstructors mapList
    let typeParams = Seq.map getTypeParams mapList
    let values = Seq.map getValueDeclarations mapList
    let valueTypeDeclarations = Seq.map getValueTypeDeclarations mapList


    { typeDeclarations = combineReferenceMaps typeDeclarations
      typeConstructors = combineReferenceMaps typeConstructors
      typeParams = combineReferenceMaps typeParams
      valueDeclarations = combineReferenceMaps values
      valueTypeDeclarations = combineReferenceMaps valueTypeDeclarations }









/// This is for straight converting a params map to a values map
let convertParamsToValuesMap (resolvedParams : ParamsInScope) : ValueDeclarations =
    resolvedParams
    |> Map.mapKeyVal (fun key tokensAndValues ->
        UnqualValue key,
        tokensAndValues
        |> SingleOrDuplicate.map (fun (tokens, value) ->
            Param
                {| tokens = tokens
                   assignmentPattern = value |}))



/// Get all the exposed names from a single assignment pattern
let rec resolveParamAssignment (assignmentPattern : CstNode<Cst.AssignmentPattern>) : ParamsInScope =
    match assignmentPattern.node with
    | Named ident ->
        Map.empty
        |> addNewParamReference (makeCstNode ident assignmentPattern.source) SimpleName

    | Ignored -> Map.empty
    | Cst.AssignmentPattern.Unit -> Map.empty
    | Aliased (alias = alias; pattern = pattern) ->
        resolveParamAssignment pattern
        |> addNewParamReference alias SimpleName

    | DestructuredPattern pattern -> resolveDestructuredParam (makeCstNode pattern assignmentPattern.source)



/// We need to recursively go down all the sub-destructurings, because all of those still get exposed to the same scope. Unlike let bindings in sub-expressions which don't get propagated upward.
and resolveDestructuredParam (pattern : CstNode<Cst.DestructuredPattern>) : ParamsInScope =

    let getParamsMapForEach
        (putInPath : PathToDestructuredName -> PathToDestructuredName)
        assignmentPattern
        : ParamsInScope =
        resolveParamAssignment assignmentPattern
        |> mapResolvedParams putInPath


    match pattern.node with
    | DestructuredRecord fieldNames ->
        fieldNames
        |> NEL.fold<_, _> (fun map fieldName -> addNewParamReference fieldName InverseRecord map) Map.empty

    | DestructuredTuple items ->
        let maps =
            items
            |> TOM.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseTuple (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 0u)
            |> fst

        combineReferenceMaps maps

    | DestructuredCons items ->
        let maps =
            items
            |> TOM.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseCons (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 0u)
            |> fst

        combineReferenceMaps maps

    | DestructuredTypeVariant (constructor, params_) ->
        params_
        |> List.mapi (fun i ->
            getParamsMapForEach (fun subPath -> InverseTypeVariant (constructor.node, uint i, subPath)))
        |> combineReferenceMaps










let resolveFuncParams ({ params_ = params_ } : Cst.FunctionValue) : NamesInScope =
    let values =
        params_
        |> NEL.map (
            resolveParamAssignment
            >> Map.mapKeyVal (fun key tokensAndValues ->
                UnqualValue key,
                tokensAndValues
                |> SingleOrDuplicate.map (fun (tokens, path) ->
                    Param
                        {| tokens = tokens
                           assignmentPattern = path |}))
        )
        |> NEL.toList
        |> combineReferenceMaps

    { empty with valueDeclarations = values }


let resolveLetBinding
    ({ bindPattern = bindPattern
       value = value } : Cst.LetBinding)
    : NamesInScope =
    let values =
        resolveParamAssignment bindPattern
        |> Map.mapKeyVal (fun key tokensAndValues ->
            UnqualValue key,
            tokensAndValues
            |> SingleOrDuplicate.map (fun (tokens, path) ->
                LocalName
                    {| tokens = tokens
                       assignmentPattern = path
                       assignedExpression = value.node |}))

    { empty with valueDeclarations = values }


let resolveLetExpression (bindings : CstNode<Cst.LetBinding> nel) =
    bindings
    |> NEL.toList
    |> Seq.map (getNode >> resolveLetBinding)
    |> combineResolvedNamesMaps



let resolveTypeConstructors
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (typeName : CstNode<UnqualTypeOrModuleIdentifier>)
    (typeDeclaration : Cst.TypeDeclaration)
    : NamesInScope =
    match typeDeclaration with
    | Alias aliasDecl ->
        // We're not accounting for record alias constructors just yet
        empty
        |> addNewTypeDeclaration moduleName typeName (Alias aliasDecl)

    | Sum newTypeDecl ->
        newTypeDecl.variants
        |> NEL.fold<_, _>
            (fun map variant ->
                addTypeConstructor
                    moduleName
                    variant.node.label
                    (variant.node.contents |> List.map getNode)
                    (UnqualType typeName.node)
                    newTypeDecl
                    map)
            (addNewTypeDeclaration moduleName typeName (Sum newTypeDecl) empty)





let rec resolveExpressionBindings (expression : Cst.Expression) : NamesInScope =
    match expression with
    | SingleValueExpression expr ->
        match expr with
        | ExplicitValue value ->
            match value with
            | Compound _ -> empty

            | Primitive _ -> empty
            | Function funcVal -> resolveFuncParams funcVal
            | DotGetter _ -> empty
        | UpperIdentifier _ -> empty
        | LowerIdentifier _ -> empty
        | LetExpression (bindings, _) -> resolveLetExpression bindings

        | ControlFlowExpression _ -> empty
    | CompoundExpression _ -> empty
    | ParensedExpression _ -> empty



/// This creates a names map with all the declared types, type constructors, and top level values in scope without going into any of the expressions. That way we can make sure that types and values can references types and values declared further down the file.
let resolveModuleBindings (ylModule : Cst.YlModule) : NamesInScope =
    let moduleName = ylModule.moduleDecl.moduleName.node

    let resolveSingleDeclaration (declaration : CstNode<Cst.Declaration>) =
        match declaration.node with
        | ImportDeclaration _ ->
            // @TODO: I'll need to implement the cross-module name resolution here!
            //empty
            failwithf "@TODO: need to implement cross-module name resolution!"

        | TypeDeclaration (name, decl) -> resolveTypeConstructors moduleName name decl
        | ValueTypeAnnotation { valueName = valueName
                                annotatedType = annotatedType } ->
            empty
            |> addValueTypeDeclaration (mapNode UnqualValue valueName) annotatedType.node

        | ValueDeclaration { valueName = valueName; value = value } ->
            empty
            |> addValue
                (mapNode UnqualValue valueName)
                (TopLevelName
                    { tokens = valueName.source
                      assignedExpression = value.node
                      fullName = reifyLower moduleName valueName.node })

    ylModule.declarations
    |> List.map resolveSingleDeclaration
    |> combineResolvedNamesMaps

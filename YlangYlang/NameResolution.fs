module NameResolution

open Lexer

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree

open QualifiedSyntaxTree.Names
open System








/// This stores a new declared type/value/param/etc in its map...
/// @TODO: but question is... currently it stores it solely in the unqualified form (I think), but it should also store it in its fully qualified, and locally findable form - i.e. if it's been explicitly imported,referenced under a module alias, namespace opened, etc.
/// So hmmm..... maybe we should instead store it under its full namespace *only*, and have separate mappings for the locally accessible versions
let addNewReference (declaredIdent : S.CstNode<'name>) (value : 'v) (map : Map<'name, SingleOrDuplicate<'v>>) =
    map
    |> Map.change declaredIdent.node (fun oldValueOpt ->
        match oldValueOpt with
        | Some (Single oldRef) -> Some (Duplicate <| TOM.make value oldRef)
        | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons value refList)
        | None -> Some (sod.Single value))


let addNewRefWithTokens
    (ident : S.CstNode<'name>)
    (value : 'v)
    (map : Map<'name, SingleOrDuplicate<TokenWithSource list * 'v>>)
    =
    addNewReference ident (ident.source, value) map






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







/// For name resolution when the names have been resolved, so this will use the canonical, fully qualified, name if applicable
module PostResolution =

    open System
    open QualifiedSyntaxTree


    type ResolvedTypeDeclarations = Map<ResolvedTypeName, TypeDecl>

    type ResolvedTypeConstructors = Map<ResolvedTypeConstructor, VariantConstructor>

    type ResolvedTypeParams = Map<ResolvedTypeParam, TokenWithSource list>

    type ResolvedValueDeclarations = Map<ResolvedLower, LowerCaseName>

    //type ResolvedValueTypeDeclarations = Map<ResolvedLower, SingleOrDuplicate<TokenWithSource list * MentionableType>>



    type NamesMaps =
        { typeDeclarations : ResolvedTypeDeclarations
          typeConstructors : ResolvedTypeConstructors
          typeParams : ResolvedTypeParams
          values : ResolvedValueDeclarations
        //valueTypeDeclarations : ResolvedValueTypeDeclarations
         }


    let getTypeDeclarations names : ResolvedTypeDeclarations = names.typeDeclarations
    let getTypeConstructors names : ResolvedTypeConstructors = names.typeConstructors
    let getTypeParams names : ResolvedTypeParams = names.typeParams
    let getValues names : ResolvedValueDeclarations = names.values
    //let getValueTypeDeclarations names : ResolvedValueTypeDeclarations = names.valueTypeDeclarations


    let empty : NamesMaps =
        { typeDeclarations = Map.empty
          typeConstructors = Map.empty
          typeParams = Map.empty
          values = Map.empty
        //valueTypeDeclarations = Map.empty
        }



    let findTypeDeclaration (name : ResolvedTypeName) { typeDeclarations = nameMap } = Map.find name nameMap

    let findTypeConstructor (name : ResolvedTypeConstructor) { typeConstructors = nameMap } = Map.find name nameMap

    let findTypeParam (name : ResolvedTypeParam) ({ typeParams = nameMap } : NamesMaps) = Map.find name nameMap


    (* @TODO: hmm it's actually a bit problematic to make both the value and value type annotation getters be non-nullable, because it's possible that only a value or only a type annotation has been declared, in which case one of these *will* fail... *)

    let findValue (name : ResolvedLower) { values = nameMap } = Map.find name nameMap

//let findValueTypeDeclarations (name : ResolvedLower) { valueTypeDeclarations = nameMap } = getFromMap name nameMap









module PreResolution =

    open SyntaxTree
    module Q = QualifiedSyntaxTree
    open Q.Names

    //type LowerCaseTopLevel =
    //    { tokens : TokenWithSource list
    //      assignedExpression : Cst.Expression
    //      fullName : FullyQualifiedTopLevelLowerIdent
    //    //key : ResolvedLower
    //     }

    //type LowerCaseName =
    //    | LocalName of
    //        {| tokens : TokenWithSource list
    //           assignmentPattern : PathToDestructuredName
    //           assignedExpression : Cst.Expression |}
    //    //key : ResolvedLower
    //    | Param of
    //        {| tokens : TokenWithSource list
    //           assignmentPattern : PathToDestructuredName |}
    //    //key : ResolvedLower
    //    | TopLevelName of LowerCaseTopLevel





    //type TypeDeclaration =
    //    { typeDecl : Cst.TypeDeclaration
    //      fullName : FullyQualifiedUpperIdent
    //      tokens : TokenWithSource list
    //    //key : ResolvedLower
    //     }


    //type VariantConstructor =
    //    { typeName : TypeOrModuleIdentifier
    //      typeDeclaration : Cst.NewTypeDeclaration
    //      variantParams : Cst.MentionableType list
    //      fullName : FullyQualifiedUpperIdent
    //      tokens : TokenWithSource list
    //    //key : ResolvedLower
    //     }


    //type TypeParam =
    //    { tokens : TokenWithSource list
    //      key : ResolvedLower }



    type TypeDeclarations = Map<TypeOrModuleIdentifier, SingleOrDuplicate<Q.TypeDecl * ResolvedTypeName>>

    type TypeConstructors =
        Map<TypeOrModuleIdentifier, SingleOrDuplicate<Q.VariantConstructor * ResolvedTypeConstructor>>

    type TypeParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * ResolvedTypeParam>>

    type ValueDeclarations = Map<ValueIdentifier, SingleOrDuplicate<Q.LowerCaseName * ResolvedLower>>

    type ValueTypeDeclarations =
        Map<ValueIdentifier, SingleOrDuplicate<TokenWithSource list * Q.MentionableType * ResolvedLower>>



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

    let tryFindValue (name : ValueIdentifier) { valueDeclarations = nameMap } = getFromMap name nameMap

    let tryFindValueTypeDeclarations (name : ValueIdentifier) { valueTypeDeclarations = nameMap } =
        getFromMap name nameMap


    let tryFindValueAndTypeDeclaration
        (name : ValueIdentifier)
        { valueDeclarations = vals
          valueTypeDeclarations = types }
        =
        getFromMap name vals,
        getFromMap name types
        |> Option.map (fun (_, t, _) -> t)



    let empty : NamesInScope =
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
                | None -> Some (sod.Single newValueAndPath)
                | Some (Single oldRef) ->
                    oldRef
                    |> TOM.make newValueAndPath
                    |> Duplicate
                    |> Some
                | Some (Duplicate refList) ->
                    refList
                    |> TOM.cons newValueAndPath
                    |> Duplicate
                    |> Some)
            resolvedParams



    let reifyModuleName (QualifiedModuleOrTypeIdentifier moduleName) : ModulePath =
        moduleName
        |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
        |> ModulePath

    let reifyUpper moduleName (UnqualTypeOrModuleIdentifier topLevelIdent) : FullyQualifiedUpperIdent =
        FullyQualifiedUpperIdent (reifyModuleName moduleName, UpperIdent topLevelIdent)

    let reifyLower moduleName (UnqualValueIdentifier topLevelIdent) : FullyQualifiedTopLevelLowerIdent =
        FullyQualifiedTopLevelLowerIdent (reifyModuleName moduleName, LowerIdent topLevelIdent)




    let private makeResolvedTypeName () = Guid.NewGuid () |> ResolvedTypeName

    let private makeResolvedTypeConstructor () =
        Guid.NewGuid () |> ResolvedTypeConstructor

    let private makeResolvedLower () = Guid.NewGuid () |> ResolvedLower
    let private makeResolvedTypeParam () = Guid.NewGuid () |> ResolvedTypeParam



    let addNewTypeParam (name : CstNode<UnqualValueIdentifier>) (names : NamesInScope) =
        { names with typeParams = addNewReference name (name.source, makeResolvedTypeParam ()) names.typeParams }

    let addNewTypeDeclaration
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (name : CstNode<UnqualTypeOrModuleIdentifier>)
        (value : Cst.TypeDeclaration)
        (names : NamesInScope)
        =
        { names with
            typeDeclarations =
                addNewReference
                    (mapNode UnqualType name)
                    ({ Q.TypeDecl.typeDecl = value
                       Q.TypeDecl.fullName = reifyUpper moduleName name.node
                       Q.TypeDecl.tokens = name.source },
                     makeResolvedTypeName ())
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
                addNewReference
                    (mapNode UnqualType variantName)
                    { Q.typeDeclaration = typeDeclaration
                      Q.variantParams = variantParams
                      Q.fullName = reifyUpper moduleName variantName.node
                      Q.tokens = variantName.source }
                    names.typeConstructors }

    let addValue name value names : NamesInScope =
        { names with valueDeclarations = addNewReference name value names.valueDeclarations }

    let addValueTypeDeclaration name value names =
        { names with valueTypeDeclarations = addNewRefWithTokens name value names.valueTypeDeclarations }







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


    /// This is for straight converting a params map to a NamesInScope
    let convertParamsToNamesInScope (resolvedParams : ParamsInScope) : NamesInScope =
        { empty with valueDeclarations = convertParamsToValuesMap resolvedParams }










    (* Make name maps from expressions *)



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




    let convertToPostResolution (names : NamesInScope) : PostResolution.NamesMaps =
        let typeDeclarations = getTypeDeclarations names
        let typeConstructors = getTypeConstructors names
        let typeParams = getTypeParams names
        let values = getValueDeclarations names

        // @TODO: This is technically not quite right, because Elm can actually have multiple shadowed values by the same name if they are defined in different modules, and they can be disambiguated based on their type signature (I think) so technically we should keep the SingleOrDuplicate-ness at this stage too. But for now let's just pretend that we are unambiguously insisting upon only a single reference by the time we come to storing the Guid version of the key.
        { typeDeclarations =
            typeDeclarations
            |> Map.mapKeyVal (fun _ value ->
                let typeDecl, key = sod.getFirst value
                key, typeDecl)

          typeConstructors =
              typeConstructors
              |> Map.mapKeyVal (fun _ value ->
                  let variantCtor, key = sod.getFirst value
                  key, variantCtor)

          typeParams =
              typeParams
              |> Map.mapKeyVal (fun _ value ->
                  let tokens, key = sod.getFirst value
                  key, tokens)

          values =
              values
              |> Map.mapKeyVal (fun _ value ->
                  let lowercase, key = sod.getFirst value
                  key, lowercase) }

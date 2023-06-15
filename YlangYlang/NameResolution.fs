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

    let tryFindTypeParam (name : UnqualValueIdentifier) ({ typeParams = nameMap } : NamesInScope) =
        getFromMap name nameMap

    let tryFindValue (name : ValueIdentifier) ({ valueDeclarations = nameMap } : NamesInScope) = getFromMap name nameMap

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









    (* Convert types/vals from the CST to a resolved AST *)



    //open Lexer
    module S = SyntaxTree
    module C = ConcreteSyntaxTree




    /// This determines whether type variables need to have been declared, or if they can be declared explicitly
    type MentionableTypeContext =
        /// Type variables need to be declared!
        | InTypeDeclaration
        /// Type vars don't need to be declared
        | InValueTypeAnnotation


    let unqualValToRecField (UnqualValueIdentifier str) = RecordFieldName str
    let unqualValToLowerIdent (UnqualValueIdentifier str) = LowerIdent str

    //let unqualTypeToUpperIdent (label : CstNode<UnqualTypeOrModuleIdentifier>) : CstNode<UpperIdent> =
    let unqualTypeToUpperIdent (UnqualTypeOrModuleIdentifier label) = UpperIdent label
    //let getLabel (UnqualTypeOrModuleIdentifier str) = str
    //S.mapNode (getLabel >> UpperIdent) label


    let convertRecordMapFields map =
        Map.mapKeyVal (fun key v -> S.mapNode unqualValToRecField key, v) map





    /// This is for straight converting a params map to a values map
    let convertParamsToValuesMap (resolvedParams : ParamsInScope) : ValueDeclarations =
        resolvedParams
        |> Map.mapKeyVal (fun key tokensAndValues ->
            UnqualValue key,
            tokensAndValues
            |> SingleOrDuplicate.map (fun (tokens, value) ->
                Q.Param
                    {| tokens = tokens
                       assignmentPattern = value |},
                makeResolvedLower ()))


    /// This is for straight converting a params map to a NamesInScope
    let convertParamsToNamesInScope (resolvedParams : ParamsInScope) : NamesInScope =
        { empty with valueDeclarations = convertParamsToValuesMap resolvedParams }


    (* Some helpers for the resolved AST builder *)

    let liftResultFromCstNode (cstNode : S.CstNode<Result<'a, 'b>>) : Result<S.CstNode<'a>, 'b> =
        match cstNode.node with
        | Ok ok -> Ok <| S.makeCstNode ok cstNode.source
        | Error err -> Error err

    let liftOptionFromCstNode (cstNode : S.CstNode<'a option>) : S.CstNode<'a> option =
        match cstNode.node with
        | Some ok -> Some <| S.makeCstNode ok cstNode.source
        | None -> None



    //let private convertTypeOrModuleIdentifierToUpper : TypeOrModuleIdentifier -> UpperIdent =
    //    function
    //    | QualifiedType ident -> ModuleSegmentsOrQualifiedTypeOrVariant ident
    //    | UnqualType ident -> TypeNameOrVariantOrTopLevelModule ident


    let private convertTypeOrModuleIdentifierToIdentifier : TypeOrModuleIdentifier -> Identifier =
        function
        | QualifiedType ident -> ModuleSegmentsOrQualifiedTypeOrVariant ident
        | UnqualType ident -> TypeNameOrVariantOrTopLevelModule ident

    let private convertValueIdentifierToIdentifier : ValueIdentifier -> Identifier =
        function
        | QualifiedValue ident -> QualifiedPathValueIdentifier ident
        | UnqualValue ident -> SingleValueIdentifier ident


    let private moduleNameToModulePath (QualifiedModuleOrTypeIdentifier moduleIdent) : ModulePath =
        moduleIdent
        |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
        |> ModulePath


    let private getModulePath (moduleCtx : C.YlModule) : ModulePath =
        moduleNameToModulePath moduleCtx.moduleDecl.moduleName.node



    let qualifyCstNodeAndLiftResult
        (qualifier : 'a -> Result<'b, Identifier list>)
        (cstNode : S.CstNode<'a>)
        : Result<S.CstNode<'b>, Identifier list> =
        S.mapNode qualifier cstNode
        |> liftResultFromCstNode


    let combineUnresolvedIdents (result : Result<'a, Identifier list nel>) =
        Result.mapError (NEL.toList >> List.concat) result

    /// Lil' helper for qualifying and merging a List of CstNodes, which we're doing pretty often in the code below
    let qualifyListCstNodes (qualifier : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> list) =
        list
        |> Result.traverse (qualifyCstNodeAndLiftResult qualifier)
        |> combineUnresolvedIdents

    /// Lil' helper for qualifying and merging an NEL of CstNodes, which we're doing pretty often in the code below
    let qualifyNelCstNodes (qualifier : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> nel) =
        list
        |> NEL.traverseResult (qualifyCstNodeAndLiftResult qualifier)
        |> combineUnresolvedIdents


    /// Lil' helper for qualifying and merging a TOM of CstNodes, which we're doing pretty often in the code below
    let qualifyTomCstNodes (qualifier : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> tom) =
        list
        |> TOM.traverseResult (qualifyCstNodeAndLiftResult qualifier)
        |> combineUnresolvedIdents



    let rec gatherParams (param : S.CstNode<Q.AssignmentPattern>) : Q.FunctionOrCaseMatchParams =
        match param.node with
        | Q.Named _ -> [ makeResolvedLower (), SimpleName ] |> Map.ofList
        | Q.Ignored -> Map.empty
        | Q.Unit -> Map.empty
        | Q.DestructuredPattern pattern ->
            S.makeCstNode pattern param.source
            |> gatherDestructuredPattern

        | Q.Aliased (pattern, _) ->
            gatherParams pattern
            |> Map.add (makeResolvedLower ()) SimpleName

    and gatherDestructuredPattern (pattern : S.CstNode<Q.DestructuredPattern>) : Q.FunctionOrCaseMatchParams =
        match pattern.node with
        | Q.DestructuredRecord fields ->
            fields
            |> NEL.map (fun _ -> makeResolvedLower (), InverseRecord)
            |> NEL.toList
            |> Map.ofList

        | Q.DestructuredTuple patterns ->
            patterns
            |> TOM.map gatherParams
            |> TOM.toList
            |> List.mapi (fun index params_ ->
                params_
                |> Map.map (fun _ value -> InverseTuple (uint index, value)))
            |> List.fold Map.merge Map.empty

        | Q.DestructuredCons patterns ->
            patterns
            |> TOM.map gatherParams
            |> TOM.toList
            |> List.mapi (fun index params_ ->
                params_
                |> Map.map (fun _ value -> InverseCons (uint index, value)))
            |> List.fold Map.merge Map.empty

        | Q.DestructuredTypeVariant (ctor, params_) ->
            params_
            |> List.map gatherParams
            |> List.mapi (fun index params_ ->
                params_
                |> Map.map (fun _ value -> InverseTypeVariant (ctor.node, uint index, value)))
            |> List.fold Map.merge Map.empty





    /// Note: No need to update `resolvedNames` at every recursion step here because no new names can be declared inside a mentioned type!
    let rec qualifyMentionableType
        (typeCtx : MentionableTypeContext)
        (resolvedNames : NamesInScope)
        (unqual : C.MentionableType)
        : Result<Q.MentionableType, Identifier list> =
        let rec innerFunc mentionableType : Result<Q.MentionableType, Identifier list> =
            match mentionableType with
            | S.UnitType -> Ok Q.UnitType

            | S.GenericTypeVar v ->
                match typeCtx with
                | InTypeDeclaration ->
                    match tryFindTypeParam v resolvedNames with
                    | Some (_, typeParam) -> Q.GenericTypeVar typeParam |> Ok
                    | None -> SingleValueIdentifier v |> List.singleton |> Error
                | InValueTypeAnnotation ->
                    // @TODO: need to do something sensible about generic type vars if we're currently in a value type annotation, where the type params are implicit
                    Q.GenericTypeVar v |> Ok

            | S.Tuple { types = types } ->
                let mappedTypes =
                    types
                    |> TOM.traverseResult (qualifyCstNodeAndLiftResult innerFunc)

                match mappedTypes with
                | Ok okTypes -> Ok <| Q.Tuple { types = okTypes }
                | Error e -> NEL.toList e |> List.concat |> Error
            | S.Record { fields = fields } ->
                let mappedFields =
                    fields
                    |> Map.map (fun _ -> qualifyCstNodeAndLiftResult innerFunc)
                    |> Map.sequenceResult

                match mappedFields with
                | Ok okFields ->
                    Q.Record { fields = convertRecordMapFields okFields }
                    |> Ok
                | Error err ->
                    Map.values err
                    |> Seq.toList
                    |> List.concat
                    |> Error

            | S.ExtendedRecord { fields = fields
                                 extendedAlias = alias } ->
                let mappedFields =
                    fields
                    |> Map.map (fun _ -> qualifyCstNodeAndLiftResult innerFunc)
                    |> Map.sequenceResult

                let extendedType : Result<S.CstNode<TokenWithSource list * ResolvedTypeParam>, Identifier list> =
                    match typeCtx with
                    | InTypeDeclaration ->
                        alias
                        |> S.mapNode (flip tryFindTypeParam resolvedNames)
                        |> liftOptionFromCstNode
                        |> Result.fromOption (
                            alias.node
                            |> SingleValueIdentifier
                            |> List.singleton
                        )

                    | InValueTypeAnnotation ->
                        // @TODO: need to do something sensible about generic type vars if we're currently in a value type annotation, where the type params are implicit
                        alias |> S.mapNode SingleValueIdentifier |> Ok

                match extendedType, mappedFields with
                | Ok extended, Ok okFields ->
                    Q.ExtendedRecord
                        { fields = convertRecordMapFields okFields
                          extendedAlias = S.mapNode snd extended }
                    |> Ok
                | Ok _, Error errMap ->
                    Map.values errMap
                    |> Seq.toList
                    |> List.concat
                    |> Error
                | Error err, Ok _ -> Error err
                | Error aliasErr, Error errMap ->
                    errMap
                    |> Map.values
                    |> Seq.toList
                    |> List.concat
                    |> List.append aliasErr
                    |> Error

            | S.ReferencedType (typeName = typeName; typeParams = typeParams) ->
                let resolvedTypeNameOpt =
                    typeName
                    |> S.getNode
                    |> flip tryFindTypeDeclaration resolvedNames

                let resolvedTypeParams = typeParams |> qualifyListCstNodes innerFunc

                match resolvedTypeNameOpt, resolvedTypeParams with
                | Some (_, resolvedTypeName), Ok resolvedTypeParams' ->
                    Q.ReferencedType (resolvedTypeName, resolvedTypeParams')
                    |> Ok
                | None, Ok _ ->
                    convertTypeOrModuleIdentifierToIdentifier typeName.node
                    |> List.singleton
                    |> Error
                | Some _, Error idents -> Error idents
                | None, Error idents ->
                    (convertTypeOrModuleIdentifierToIdentifier typeName.node
                     :: idents)
                    |> Error

            | S.Arrow (fromType, toTypes) ->
                let resolvedFrom =
                    S.mapNode innerFunc fromType
                    |> liftResultFromCstNode

                let resolvedTos = toTypes |> qualifyNelCstNodes innerFunc

                (resolvedFrom, resolvedTos)
                ||> Result.map2 (fun from tos -> Q.Arrow (from, tos)) (@)


            | S.Parensed parensed -> innerFunc parensed.node


        innerFunc unqual



    and qualifyTypeDeclaration
        (resolvedNames : NamesInScope)
        (declaration : S.TypeDeclaration<TypeOrModuleIdentifier>)
        : Result<Q.TypeDeclaration, Identifier list> =
        match declaration with
        | S.Alias { typeParams = typeParams
                    referent = referent } ->

            let newNamesInScope =
                typeParams
                |> List.fold (flip addNewTypeParam) resolvedNames

            let mentionableType =
                qualifyCstNodeAndLiftResult (qualifyMentionableType InTypeDeclaration newNamesInScope) referent

            mentionableType
            |> Result.map (fun type' ->
                let typeParamsMap =
                    typeParams
                    // @TODO: beware that we have duplication here, because we're constructing a simple type params map with a new Guid, but we're also `addNewTypeParam`ing into a `NamesInScope`. Which is not only duplication, but it also means that we have two separate Guids in the different kinds of names maps referencing the same value.
                    |> List.map (fun cstNode -> makeResolvedTypeParam (), cstNode.source)
                    |> Map.ofList

                Q.Alias
                    { referent = type'
                      typeParams = typeParamsMap })

        | S.Sum newType ->
            qualifyNewTypeDeclaration resolvedNames newType
            |> Result.map Q.Sum


    and qualifyNewTypeDeclaration
        resolvedNames
        { typeParams = typeParams
          variants = variants }
        : Result<Q.NewTypeDeclaration, Identifier list> =

        let resolvedWithTypeParams =
            typeParams
            |> List.fold (flip addNewTypeParam) resolvedNames

        let resolvedVariants =
            variants
            |> qualifyNelCstNodes (fun (variantCase : C.VariantCase) ->
                variantCase.contents
                |> qualifyListCstNodes (qualifyMentionableType InTypeDeclaration resolvedWithTypeParams)
                |> Result.map (fun contents' ->
                    let label = S.mapNode unqualTypeToUpperIdent variantCase.label

                    { Q.label = label
                      Q.contents = contents' }))

        match resolvedVariants with
        | Ok variants' ->
            let typeParamsMap =
                typeParams
                // @TODO: beware that we have duplication here, because we're constructing a simple type params map with a new Guid, but we're also `addNewTypeParam`ing into a `NamesInScope`. Which is not only duplication, but it also means that we have two separate Guids in the different kinds of names maps referencing the same value.
                |> List.map (fun cstNode -> makeResolvedTypeParam (), cstNode.source)
                |> Map.ofList

            { Q.variants = variants'
              Q.typeParams = typeParamsMap }
            |> Ok
        | Error err -> Error err


    and qualifyDestructuredPattern
        (resolvedNames : NamesInScope)
        (destructuredPattern : C.DestructuredPattern)
        : Result<Q.DestructuredPattern, Identifier list> =
        match destructuredPattern with
        | S.DestructuredRecord record ->
            record
            |> NEL.map (S.mapNode unqualValToLowerIdent)
            |> Q.DestructuredRecord
            |> Ok

        | S.DestructuredTuple tuple ->
            tuple
            |> qualifyTomCstNodes (qualifyAssignmentPattern resolvedNames)
            |> Result.map Q.DestructuredTuple

        | S.DestructuredCons pattern ->
            pattern
            |> qualifyTomCstNodes (qualifyAssignmentPattern resolvedNames)
            |> Result.map Q.DestructuredCons

        | S.DestructuredTypeVariant (ctor, params') ->
            let resolvedCtor =
                ctor
                |> S.getNode
                |> (flip tryFindTypeConstructor resolvedNames)
                |> Result.fromOption (
                    convertTypeOrModuleIdentifierToIdentifier ctor.node
                    |> List.singleton
                )
                |> Result.map snd

            let resolvedParams =
                params'
                |> qualifyListCstNodes (qualifyAssignmentPattern resolvedNames)


            (resolvedCtor, resolvedParams)
            ||> Result.map2 (fun ctor' resolvedParams' -> Q.DestructuredTypeVariant (ctor', resolvedParams')) (@)


    and qualifyAssignmentPattern
        (resolvedNames : NamesInScope)
        (assignmentPattern : C.AssignmentPattern)
        : Result<Q.AssignmentPattern, Identifier list> =
        match assignmentPattern with
        | S.Named name -> unqualValToLowerIdent name |> Q.Named |> Ok
        | S.Ignored -> Ok Q.Ignored
        | S.Unit -> Ok Q.Unit

        | S.DestructuredPattern pattern ->
            qualifyDestructuredPattern resolvedNames pattern
            |> Result.map Q.DestructuredPattern

        | S.Aliased (pattern, alias) ->
            qualifyCstNodeAndLiftResult (qualifyAssignmentPattern resolvedNames) pattern
            |> Result.map (fun pattern' -> Q.Aliased (pattern', S.mapNode unqualValToLowerIdent alias))






    and qualifyCompoundExpression (moduleCtx : C.YlModule) resolvedNames compExpr =
        match compExpr with
        | S.List list ->
            list
            |> qualifyListCstNodes (qualifyExpression moduleCtx resolvedNames)
            |> Result.map Q.List

        | S.CompoundValues.Tuple items ->
            items
            |> qualifyTomCstNodes (qualifyExpression moduleCtx resolvedNames)
            |> Result.map Q.CompoundValues.Tuple

        | S.CompoundValues.Record fields ->
            fields
            |> List.map (fun (fieldName, fieldVal) ->
                qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) fieldVal
                |> Result.map (fun qualVal -> S.mapNode unqualValToLowerIdent fieldName, qualVal))
            |> Result.sequenceList
            |> combineUnresolvedIdents
            |> Result.map Q.CompoundValues.Record

        | S.CompoundValues.RecordExtension (extendedRec, fields) ->
            fields
            |> NEL.map (fun (fieldName, fieldVal) ->
                qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) fieldVal
                |> Result.map (fun qualVal -> fieldName, qualVal))
            |> NEL.sequenceResult
            |> combineUnresolvedIdents
            |> Result.map (fun qualFields ->
                let mappedFields =
                    qualFields
                    |> NEL.map (Tuple.mapFst (S.mapNode unqualValToLowerIdent))

                Q.CompoundValues.RecordExtension (S.mapNode unqualValToLowerIdent extendedRec, mappedFields))



    and qualifyExpression
        (moduleCtx : C.YlModule)
        (resolvedNames : NamesInScope)
        (expression : C.Expression)
        : Result<Q.Expression, Identifier list> =
        match expression with
        | S.ParensedExpression expr -> qualifyExpression moduleCtx resolvedNames expr
        | S.SingleValueExpression singleExpr ->
            match singleExpr with
            | S.ExplicitValue expl ->
                match expl with
                | S.Compound comp ->
                    qualifyCompoundExpression moduleCtx resolvedNames comp
                    |> Result.map (
                        Q.Compound
                        >> Q.ExplicitValue
                        >> Q.SingleValueExpression
                    )

                | S.Primitive prim ->
                    Q.Primitive prim
                    |> Q.ExplicitValue
                    |> Q.SingleValueExpression
                    |> Ok

                | S.DotGetter field ->
                    unqualValToLowerIdent field
                    |> Q.DotGetter
                    |> Q.ExplicitValue
                    |> Q.SingleValueExpression
                    |> Ok

                | S.Function ({ params_ = params_; body = body } as funcParams) ->
                    let qualifiedBody =
                        resolveFuncParams resolvedNames funcParams
                        |> Result.bind (fun resolvedFuncNames ->
                            body
                            |> S.mapNode (fun expr ->
                                let combinedResolvedNames =
                                    combineTwoResolvedNamesMaps resolvedFuncNames resolvedNames

                                qualifyExpression moduleCtx combinedResolvedNames expr)
                            |> liftResultFromCstNode)

                    let qualifiedParams =
                        params_
                        |> qualifyNelCstNodes (qualifyAssignmentPattern resolvedNames)

                    (qualifiedBody, qualifiedParams)
                    ||> Result.map2
                            (fun expr params' ->
                                let paramsMap =
                                    NEL.map gatherParams params'
                                    |> NEL.toList
                                    |> List.fold Map.merge Map.empty
                                // @TODO: beware that we have duplication here, because we're constructing a simple params map with a new Guid, but we're also adding them into a `NamesInScope`. Which is not only duplication, but it also means that we have two separate Guids in the different kinds of names maps referencing the same value.

                                Q.Function { body = expr; params_ = paramsMap }
                                |> Q.ExplicitValue
                                |> Q.SingleValueExpression)
                            (@)



            | S.UpperIdentifier upper ->
                match tryFindTypeConstructor upper resolvedNames with
                | Some (variantCtor, resolvedCtor) ->
                    Q.UpperIdentifier (variantCtor.fullName, resolvedCtor)
                    |> Q.SingleValueExpression
                    |> Ok

                | None ->
                    convertTypeOrModuleIdentifierToIdentifier upper
                    |> List.singleton
                    |> Error

            | S.LowerIdentifier lower ->
                match tryFindValue lower resolvedNames with
                | Some (lowerCaseName, resolvedLower) ->
                    match lowerCaseName with
                    | Q.LocalName _
                    | Q.Param _ ->
                        match lower with
                        | QualifiedValue qual ->
                            failwithf
                                "This shouldn't be possible. To fix this we'd need to create another lowercase name resolution map exclusively for qualified value paths"

                        | UnqualValue (UnqualValueIdentifier unqual) ->
                            let lowerName =
                                LowerIdent unqual
                                |> LocalVariableOrParamIdent
                                |> LocalOrParam

                            Q.LowerIdentifier (lowerName, resolvedLower)
                            |> Q.SingleValueExpression
                            |> Ok

                    | Q.TopLevelName topLevel ->
                        Q.LowerIdentifier (TopLevelValue topLevel.fullName, resolvedLower)
                        |> Q.SingleValueExpression
                        |> Ok

                | None ->
                    convertValueIdentifierToIdentifier lower
                    |> List.singleton
                    |> Error

            | S.LetExpression (bindings, expr) ->
                let namesMap =
                    resolveLetExpression moduleCtx resolvedNames bindings
                    |> Result.map (fun letExpr -> combineTwoResolvedNamesMaps letExpr resolvedNames)

                match namesMap with
                | Ok namesMap_ ->
                    let qualBindings : Result<Q.LetDeclarationNames, Identifier list> =
                        bindings
                        |> qualifyNelCstNodes (fun binding ->
                            let qualBinding : Result<S.CstNode<Q.AssignmentPattern>, Identifier list> =

                                qualifyCstNodeAndLiftResult (qualifyAssignmentPattern namesMap_) binding.bindPattern

                            let qualExpr : Result<S.CstNode<Q.Expression>, Identifier list> =
                                qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx namesMap_) binding.value

                            Result.map2
                                (fun binding' expr' ->
                                    makeResolvedLower (),
                                    { Q.tokens = binding'.source
                                      Q.assignmentPattern = binding'.node
                                      Q.assignedExpression = expr'.node })
                                (fun err1 err2 -> err1 @ err2)
                                qualBinding
                                qualExpr)
                        |> Result.map (NEL.toList >> List.map S.getNode >> Map.ofList)

                    let qualExpr =
                        qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx namesMap_) expr
                        |> Result.map S.getNode

                    Result.map2
                        (fun expr' bindings' ->
                            Q.LetExpression (bindings', expr')
                            |> Q.SingleValueExpression)
                        (@)
                        qualExpr
                        qualBindings

                | Error err -> Error err

            | S.ControlFlowExpression controlFlowExpr ->
                match controlFlowExpr with
                | S.IfExpression (cond, ifTrue, ifFalse) ->
                    let qualifyExpr =
                        qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames)

                    let qualCond, qualIfTrue, qualIfFalse =
                        qualifyExpr cond, qualifyExpr ifTrue, qualifyExpr ifFalse

                    Result.map3
                        (fun cond' ifTrue' ifFalse' ->
                            Q.IfExpression (cond', ifTrue', ifFalse')
                            |> Q.ControlFlowExpression
                            |> Q.SingleValueExpression)
                        (@)
                        qualCond
                        qualIfTrue
                        qualIfFalse

                | S.CaseMatch (exprToMatch, branches) ->
                    let qualExpr =
                        qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) exprToMatch

                    //let qualBranches : Result<NEL<S.CstNode<Q.AssignmentPattern> * S.CstNode<Q.Expression>>, Identifier list> =
                    let qualBranches : Result<Q.CaseMatchBranch nel, Identifier list> =
                        branches
                        |> NEL.traverseResult (
                            (fun (assignPattern, branchExpr) ->
                                let paramsMap =
                                    S.mapNode (qualifyAssignmentPattern resolvedNames) assignPattern
                                    |> liftResultFromCstNode
                                    |> Result.map gatherParams

                                let qualBranchExpr =
                                    resolveParamAssignment resolvedNames assignPattern
                                    |> Result.map (fun params_ ->
                                        combineTwoResolvedNamesMaps (convertParamsToNamesInScope params_) resolvedNames)
                                    |> Result.bind (fun branchResolvedNames ->
                                        qualifyCstNodeAndLiftResult
                                            (qualifyExpression moduleCtx branchResolvedNames)
                                            branchExpr)

                                Result.map2
                                    (fun paramsMap_ qualBranch ->
                                        { Q.CaseMatchBranch.matchPattern = paramsMap_
                                          Q.CaseMatchBranch.body = qualBranch })
                                    (@)
                                    paramsMap
                                    qualBranchExpr)
                        )
                        |> combineUnresolvedIdents


                    Result.map2
                        (fun expr branches ->
                            Q.CaseMatch (expr, branches)
                            |> Q.ControlFlowExpression
                            |> Q.SingleValueExpression)
                        (@)
                        qualExpr
                        qualBranches


        | S.CompoundExpression compExpr ->
            match compExpr with
            | S.Operator (left, opSeq) ->
                let qualExpr =
                    qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) left

                let qualOpSeq =
                    opSeq
                    |> NEL.traverseResult (fun (op, opExpr) ->
                        qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) opExpr
                        |> Result.map (Tuple.makePairWithFst op))
                    |> combineUnresolvedIdents


                Result.map2
                    (fun expr opSeq' -> Q.Operator (expr, opSeq') |> Q.CompoundExpression)
                    (@)
                    qualExpr
                    qualOpSeq

            | S.FunctionApplication (func, params') ->
                let qualFunc =
                    qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) func

                let qualParams =
                    params'
                    |> qualifyNelCstNodes (qualifyExpression moduleCtx resolvedNames)

                Result.map2
                    (fun funcExpr paramsExprs ->
                        Q.FunctionApplication (funcExpr, paramsExprs)
                        |> Q.CompoundExpression)
                    (@)
                    qualFunc
                    qualParams

            | S.DotAccess (expr, getter) ->
                let qualExpr =
                    qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) expr

                Result.map
                    (fun expr' ->
                        Q.DotAccess (expr', S.mapNode (NEL.map unqualValToLowerIdent) getter)
                        |> Q.CompoundExpression)
                    qualExpr

    and qualifyModule (ylModule : C.YlModule) : Result<Q.YlModule, Identifier list> =
        match resolveModuleBindings ylModule with
        | Ok resolvedNames ->
            let declarations : Result<S.CstNode<Q.Declaration> list, Identifier list> =
                ylModule.declarations
                |> qualifyListCstNodes (
                    (function
                    | S.TypeDeclaration (name = name; declaration = decl) ->
                        let typeDeclResult = qualifyTypeDeclaration resolvedNames decl

                        match typeDeclResult with
                        | Ok typeDecl -> Q.TypeDeclaration (name, typeDecl) |> Ok
                        | Error err -> Error err
                    | S.ImportDeclaration import -> failwithf "@TODO: Importing other modules is not implemented yet!"
                    | S.ValueTypeAnnotation { valueName = valueName
                                              annotatedType = annotatedType } ->
                        let qualifiedAnnotatedType =
                            qualifyCstNodeAndLiftResult
                                (qualifyMentionableType InValueTypeAnnotation resolvedNames)
                                annotatedType


                        match qualifiedAnnotatedType with
                        | Ok qualified ->
                            Q.ValueTypeAnnotation
                                { valueName = S.mapNode unqualValToLowerIdent valueName
                                  annotatedType = qualified }
                            |> Ok
                        | Error err -> Error err

                    | S.ValueDeclaration { valueName = valueName; value = value } ->
                        let result =
                            qualifyCstNodeAndLiftResult (qualifyExpression ylModule resolvedNames) value

                        match result with
                        | Ok res ->
                            Q.ValueDeclaration
                                { valueName = S.mapNode unqualValToLowerIdent valueName
                                  value = res }
                            |> Ok
                        | Error err -> Error err)
                )

            match declarations with
            | Ok decls ->
                { Q.moduleDecl = ylModule.moduleDecl
                  Q.declarations = decls }
                |> Ok
            | Error err -> Error err

        | Error err -> Error err






    (* Traverse the CST and gather named types/vals *)


    and addNewTypeParam (name : CstNode<UnqualValueIdentifier>) (names : NamesInScope) : NamesInScope =
        { names with typeParams = addNewReference name (name.source, makeResolvedTypeParam ()) names.typeParams }

    and addNewTypeDeclaration
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (name : CstNode<UnqualTypeOrModuleIdentifier>)
        (value : Cst.TypeDeclaration)
        (names : NamesInScope)
        : Result<NamesInScope, Identifier list> =
        qualifyTypeDeclaration names value
        |> Result.map (fun value_ ->
            { names with
                typeDeclarations =
                    addNewReference
                        (mapNode UnqualType name)
                        ({ Q.TypeDecl.typeDecl = value_
                           Q.TypeDecl.fullName = reifyUpper moduleName name.node
                           Q.TypeDecl.tokens = name.source },
                         makeResolvedTypeName ())
                        names.typeDeclarations })

    and addTypeConstructor
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (variantName : CstNode<UnqualTypeOrModuleIdentifier>)
        (variantParams : Cst.MentionableType list)
        (typeName : TypeOrModuleIdentifier)
        (typeDeclaration : Cst.NewTypeDeclaration)
        (names : NamesInScope)
        =
        let qualifiedVariantParams =
            List.map (qualifyMentionableType InTypeDeclaration names) variantParams
            |> Result.sequenceList
            |> combineUnresolvedIdents


        (qualifyNewTypeDeclaration names typeDeclaration, qualifiedVariantParams)
        ||> Result.map2
                (fun typeDecl variants ->
                    { names with
                        typeConstructors =
                            addNewReference
                                (mapNode UnqualType variantName)
                                ({ Q.VariantConstructor.typeDeclaration = typeDecl
                                   Q.VariantConstructor.variantParams = variants
                                   Q.VariantConstructor.fullName = reifyUpper moduleName variantName.node
                                   Q.VariantConstructor.tokens = variantName.source },
                                 makeResolvedTypeConstructor ())
                                names.typeConstructors })
                (@)

    and addValue name value names : NamesInScope =
        { names with valueDeclarations = addNewReference name value names.valueDeclarations }

    and addValueTypeDeclaration name (value : TokenWithSource list * Q.MentionableType * ResolvedLower) names =
        { names with valueTypeDeclarations = addNewReference name value names.valueTypeDeclarations }











































    (* Make name maps from expressions *)



    /// Get all the exposed names from a single assignment pattern
    and resolveParamAssignment
        (names : NamesInScope)
        (assignmentPattern : CstNode<Cst.AssignmentPattern>)
        : Result<ParamsInScope, Identifier list> =
        match assignmentPattern.node with
        | Named ident ->
            Map.empty
            |> addNewParamReference (makeCstNode ident assignmentPattern.source) SimpleName
            |> Ok

        | Ignored -> Ok Map.empty
        | Cst.AssignmentPattern.Unit -> Ok Map.empty
        | Aliased (alias = alias; pattern = pattern) ->
            resolveParamAssignment names pattern
            |> Result.map (addNewParamReference alias SimpleName)

        | DestructuredPattern pattern -> resolveDestructuredParam names (makeCstNode pattern assignmentPattern.source)



    /// We need to recursively go down all the sub-destructurings, because all of those still get exposed to the same scope. Unlike let bindings in sub-expressions which don't get propagated upward.
    and resolveDestructuredParam
        (names : NamesInScope)
        (pattern : CstNode<Cst.DestructuredPattern>)
        : Result<ParamsInScope, Identifier list> =
        let getParamsMapForEach
            (putInPath : PathToDestructuredName -> PathToDestructuredName)
            assignmentPattern
            : Result<ParamsInScope, Identifier list> =
            resolveParamAssignment names assignmentPattern
            |> Result.map (mapResolvedParams putInPath)


        match pattern.node with
        | DestructuredRecord fieldNames ->
            fieldNames
            |> NEL.fold<_, _> (fun map fieldName -> addNewParamReference fieldName InverseRecord map) Map.empty
            |> Ok

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

            Result.sequence maps
            |> Result.map combineReferenceMaps
            |> combineUnresolvedIdents

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

            Result.sequence maps
            |> Result.map combineReferenceMaps
            |> combineUnresolvedIdents

        | DestructuredTypeVariant (constructor, params_) ->
            let resolvedCtorOpt = tryFindTypeConstructor constructor.node names

            match resolvedCtorOpt with
            | Some (_, resolvedCtor) ->
                params_
                |> List.mapi (fun i ->
                    getParamsMapForEach (fun subPath -> InverseTypeVariant (resolvedCtor, uint i, subPath)))
                |> Result.sequence
                |> Result.map combineReferenceMaps
                |> combineUnresolvedIdents

            | None ->
                convertTypeOrModuleIdentifierToIdentifier constructor.node
                |> List.singleton
                |> Error










    and resolveFuncParams
        (names : NamesInScope)
        ({ params_ = params_ } : Cst.FunctionValue)
        : Result<NamesInScope, Identifier list> =
        let values =
            params_
            |> NEL.map (
                resolveParamAssignment names
                >> Result.map (
                    Map.mapKeyVal (fun key tokensAndValues ->
                        UnqualValue key,
                        tokensAndValues
                        |> SingleOrDuplicate.map (fun (tokens, path) ->
                            Q.Param
                                {| tokens = tokens
                                   assignmentPattern = path |},
                            makeResolvedLower ()))
                )
            )
            |> NEL.sequenceResult
            |> Result.map (NEL.toList >> combineReferenceMaps)
            |> combineUnresolvedIdents

        values
        |> Result.map (fun vals -> { empty with valueDeclarations = vals })


    and resolveLetBinding
        (ylModule : Cst.YlModule)
        (names : NamesInScope)
        ({ bindPattern = bindPattern
           value = value } : Cst.LetBinding)
        : Result<NamesInScope, Identifier list> =

        let qualifiedExpr = qualifyExpression ylModule names value.node

        let values =
            (resolveParamAssignment names bindPattern, qualifiedExpr)
            ||> Result.map2
                    (fun resolvedParam resolvedExpr ->
                        resolvedParam
                        |> Map.mapKeyVal (fun key tokensAndValues ->
                            UnqualValue key,
                            tokensAndValues
                            |> SingleOrDuplicate.map (fun (tokens, path) ->
                                Q.LocalName
                                    {| tokens = tokens
                                       assignmentPattern = path
                                       assignedExpression = resolvedExpr |},
                                makeResolvedLower ())))
                    (@)

        values
        |> Result.map (fun vals -> { empty with valueDeclarations = vals })


    and resolveLetExpression (ylModule : Cst.YlModule) (names : NamesInScope) (bindings : CstNode<Cst.LetBinding> nel) =
        bindings
        |> NEL.toList
        |> Seq.map (getNode >> resolveLetBinding ylModule names)
        |> Result.sequence
        |> Result.map combineResolvedNamesMaps
        |> combineUnresolvedIdents




    and resolveTypeConstructors
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (typeName : CstNode<UnqualTypeOrModuleIdentifier>)
        (typeDeclaration : Cst.TypeDeclaration)
        : Result<NamesInScope, Identifier list> =
        match typeDeclaration with
        | Alias aliasDecl ->
            // We're not accounting for record alias constructors just yet
            empty
            |> addNewTypeDeclaration moduleName typeName (Alias aliasDecl)

        | Sum newTypeDecl ->
            newTypeDecl.variants
            |> NEL.fold<_, _>
                (fun map variant ->
                    map
                    |> Result.bind (fun map_ ->
                        addTypeConstructor
                            moduleName
                            variant.node.label
                            (variant.node.contents |> List.map getNode)
                            (UnqualType typeName.node)
                            newTypeDecl
                            map_))
                (addNewTypeDeclaration moduleName typeName (Sum newTypeDecl) empty)




    /// This creates a names map with all the declared types, type constructors, and top level values in scope without going into any of the expressions. That way we can make sure that types and values can references types and values declared further down the file.
    and resolveModuleBindings (ylModule : Cst.YlModule) : Result<NamesInScope, Identifier list> =
        let moduleName = ylModule.moduleDecl.moduleName.node

        /// A quick scan of the module to gather all top level names
        let firstLevelResolution declaration =
            match declaration.node with
            | ImportDeclaration _ ->
                // @TODO: I'll need to implement the cross-module name resolution here!
                //empty
                failwithf "@TODO: need to implement cross-module name resolution!"
            | TypeDeclaration (name, decl) -> resolveTypeConstructors moduleName name decl
            | ValueTypeAnnotation { valueName = valueName
                                    annotatedType = annotatedType } ->

                let qualifiedType = qualifyMentionableType InValueTypeAnnotation annotatedType

                empty
                |> addValueTypeDeclaration
                    (mapNode UnqualValue valueName)
                    (annotatedType.source, annotatedType.node, makeResolvedLower ())
                |> Ok

            | ValueDeclaration { valueName = valueName; value = value } ->
                empty
                |> addValue
                    (mapNode UnqualValue valueName)
                    (Q.TopLevelName
                        { tokens = valueName.source
                          assignedExpression = value.node
                          fullName = reifyLower moduleName valueName.node },
                     makeResolvedLower ())


        let resolveSingleDeclaration (declaration : CstNode<Cst.Declaration>) =
            match declaration.node with
            | ImportDeclaration _ ->
                // @TODO: I'll need to implement the cross-module name resolution here!
                //empty
                failwithf "@TODO: need to implement cross-module name resolution!"

            | TypeDeclaration (name, decl) -> resolveTypeConstructors moduleName name decl
            | ValueTypeAnnotation { valueName = valueName
                                    annotatedType = annotatedType } ->

                let qualifiedType = qualifyMentionableType InValueTypeAnnotation annotatedType

                empty
                |> addValueTypeDeclaration
                    (mapNode UnqualValue valueName)
                    (annotatedType.source, annotatedType.node, makeResolvedLower ())
                |> Ok

            | ValueDeclaration { valueName = valueName; value = value } ->
                empty
                |> addValue
                    (mapNode UnqualValue valueName)
                    (Q.TopLevelName
                        { tokens = valueName.source
                          assignedExpression = value.node
                          fullName = reifyLower moduleName valueName.node },
                     makeResolvedLower ())

        ylModule.declarations
        |> List.map resolveSingleDeclaration
        |> Result.sequenceList
        |> Result.map combineResolvedNamesMaps
        |> combineUnresolvedIdents




//let convertToPostResolution (names : NamesInScope) : PostResolution.NamesMaps =
//    let typeDeclarations = getTypeDeclarations names
//    let typeConstructors = getTypeConstructors names
//    let typeParams = getTypeParams names
//    let values = getValueDeclarations names

//    // @TODO: This is technically not quite right, because Elm can actually have multiple shadowed values by the same name if they are defined in different modules, and they can be disambiguated based on their type signature (I think) so technically we should keep the SingleOrDuplicate-ness at this stage too. But for now let's just pretend that we are unambiguously insisting upon only a single reference by the time we come to storing the Guid version of the key.
//    { typeDeclarations =
//        typeDeclarations
//        |> Map.mapKeyVal (fun _ value ->
//            let typeDecl, key = sod.getFirst value
//            key, typeDecl)

//      typeConstructors =
//          typeConstructors
//          |> Map.mapKeyVal (fun _ value ->
//              let variantCtor, key = sod.getFirst value
//              key, variantCtor)

//      typeParams =
//          typeParams
//          |> Map.mapKeyVal (fun _ value ->
//              let tokens, key = sod.getFirst value
//              key, tokens)

//      values =
//          values
//          |> Map.mapKeyVal (fun _ value ->
//              let lowercase, key = sod.getFirst value
//              key, lowercase) }

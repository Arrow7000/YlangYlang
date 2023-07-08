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
//let addNewReference (declaredIdent : S.CstNode<'name>) (value : 'v) (map : Map<'name, SingleOrDuplicate<'v>>) =
let addNewReference (declaredIdent : 'name) (value : 'v) (map : Map<'name, SingleOrDuplicate<'v>>) =
    map
    |> Map.change declaredIdent (fun oldValueOpt ->
        match oldValueOpt with
        | Some (Single oldRef) -> Some (Duplicate <| TOM.make value oldRef)
        | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons value refList)
        | None -> Some (sod.Single value))


let addNewRefWithTokens (ident : S.CstNode<'name>) (value : 'v) =
    addNewReference ident (ident.source, value)






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




let private makeResolvedTypeName () = Guid.NewGuid () |> ResolvedType

let private makeResolvedTypeConstructor () =
    Guid.NewGuid () |> ResolvedTypeConstructor

let private makeResolvedLower () = Guid.NewGuid () |> ResolvedValue
let private makeResolvedTypeParam () = Guid.NewGuid () |> ResolvedTypeParam





let reifyModuleName (QualifiedModuleOrTypeIdentifier moduleName) : ModulePath =
    moduleName
    |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
    |> ModulePath

let reifyUpper
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (UnqualTypeOrModuleIdentifier topLevelIdent)
    : FullyQualifiedUpperIdent =
    FullyQualifiedUpperIdent (reifyModuleName moduleName, UpperIdent topLevelIdent)

let reifyLower
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (UnqualValueIdentifier topLevelIdent)
    : FullyQualifiedTopLevelLowerIdent =
    FullyQualifiedTopLevelLowerIdent (reifyModuleName moduleName, LowerIdent topLevelIdent)







module PreResolution =

    module Q = QualifiedSyntaxTree


    type VariantConstructor =
        { typeDeclaration : Cst.NewTypeDeclaration
          variantCase : Cst.VariantCase
          fullName : FullyQualifiedUpperIdent }



    type LocalName =
        { tokens : TokenWithSource list
          destructurePath : PathToDestructuredName
          assignedExpression : Cst.Expression }

    type LowerCaseTopLevel =
        { tokens : TokenWithSource list
          assignedExpression : Cst.Expression
          fullName : FullyQualifiedTopLevelLowerIdent }

    type LowerCaseName =
        | LocalName of LocalName
        | Param of Q.Param
        | TopLevelName of LowerCaseTopLevel





    type TypeDeclarations = Map<TypeOrModuleIdentifier, SingleOrDuplicate<Cst.TypeDeclaration * ResolvedType>>

    type TypeConstructors = Map<TypeOrModuleIdentifier, SingleOrDuplicate<VariantConstructor * ResolvedTypeConstructor>>

    type TypeParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * ResolvedTypeParam>>

    type ValueDeclarations = Map<ValueIdentifier, SingleOrDuplicate<LowerCaseName * ResolvedValue>>

    type ValueTypeDeclarations = Map<ValueIdentifier, SingleOrDuplicate<S.CstNode<Cst.MentionableType> * ResolvedValue>>



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
        |> Option.map (fst >> S.getNode)



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


    let addNewParamReference
        (ident : S.CstNode<UnqualValueIdentifier>)
        (path : PathToDestructuredName)
        (resolvedParams : ParamsInScope)
        : ParamsInScope =
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











    (* Convert types/vals from the CST to a resolved AST *)



    //open Lexer
    module S = SyntaxTree
    module C = ConcreteSyntaxTree



    let unqualValToRecField (UnqualValueIdentifier str) = RecordFieldName str
    let unqualValToLowerIdent (UnqualValueIdentifier str) = LowerIdent str
    let lowerIdentToUnqualVal (LowerIdent str) = UnqualValueIdentifier str

    //let unqualTypeToUpperIdent (label : S.CstNode<UnqualTypeOrModuleIdentifier>) : S.CstNode<UpperIdent> =
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
                let ident = unqualValToLowerIdent key

                Param
                    { ident = ident
                      tokens = tokens
                      destructurePath = value },
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

    let private convertValueIdentifierToLowerIdent (UnqualValueIdentifier ident) : LowerIdent = LowerIdent ident


    let private moduleNameToModulePath (QualifiedModuleOrTypeIdentifier moduleIdent) : ModulePath =
        moduleIdent
        |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
        |> ModulePath


    let private getModulePath (moduleCtx : C.YlModule) : ModulePath =
        moduleNameToModulePath moduleCtx.moduleDecl.moduleName.node

    let private convertTypeOrModuleIdentifierToFullyQualified
        (moduleName : QualifiedModuleOrTypeIdentifier)
        : TypeOrModuleIdentifier -> FullyQualifiedUpperIdent =
        function
        | QualifiedType (QualifiedModuleOrTypeIdentifier path) ->
            let (moduleSegments, UnqualTypeOrModuleIdentifier ident) = NEL.peelOffLast path

            let modulePath =
                moduleSegments
                |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)

            FullyQualifiedUpperIdent (ModulePath modulePath, UpperIdent ident)

        | UnqualType (UnqualTypeOrModuleIdentifier ident) ->
            FullyQualifiedUpperIdent (moduleNameToModulePath moduleName, UpperIdent ident)




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

    ///// Lil' helper for qualifying and merging a Map of CstNodes, which we're doing pretty often in the code below
    //let qualifyMapCstNodes (qualifier : 'a -> Result<'b, Identifier list>) (map : Map<'k, SyntaxTree.CstNode<'a>>) =
    //    map
    //    |> Map.map (qualifyCstNodeAndLiftResult qualifier)
    //    |> Map.sequenceResult
    //    |> combineUnresolvedIdents


    let rec gatherParams (pattern : S.CstNode<Q.AssignmentPattern>) : Q.FunctionOrCaseMatchParamMap =
        match pattern.node with
        | Q.Named (resolved, ident) ->
            let param_ : Q.Param =
                { ident = ident
                  tokens = pattern.source
                  destructurePath = SimpleName }

            { paramPattern = pattern.node
              namesMap = Map.add resolved param_ Map.empty }

        | Q.Ignored ->
            { paramPattern = pattern.node
              namesMap = Map.empty }

        | Q.Unit ->
            { paramPattern = pattern.node
              namesMap = Map.empty }

        | Q.DestructuredPattern destructured ->
            { paramPattern = pattern.node
              namesMap =
                S.makeCstNode destructured pattern.source
                |> gatherDestructuredPattern }

        | Q.Aliased (aliased, (resolved, alias)) ->
            let param_ : Q.Param =
                { ident = alias.node
                  tokens = alias.source
                  destructurePath = SimpleName }

            let gatheredFromAlias = gatherParams aliased

            { paramPattern = pattern.node
              namesMap =
                gatheredFromAlias.namesMap
                |> Map.add resolved param_ }




    and gatherDestructuredPattern (pattern : S.CstNode<Q.DestructuredPattern>) : Map<ResolvedValue, Q.Param> =
        /// Adjusts the destructure path of a param to account for the fact that it is contained inside a nested destructuring
        let adjustDestructurePath newPath (param_ : Q.Param) : Q.Param =
            { Q.Param.ident = param_.ident
              Q.Param.tokens = param_.tokens
              Q.Param.destructurePath = newPath }


        match pattern.node with
        | Q.DestructuredRecord fields ->
            fields
            |> NEL.map (fun (resolved, ident) ->
                resolved,
                { Q.Param.ident = ident.node
                  Q.Param.tokens = ident.source
                  Q.Param.destructurePath = InverseRecord })
            |> NEL.toList
            |> Map.ofList

        | Q.DestructuredTuple patterns ->
            TOM.map gatherParams patterns
            |> TOM.mapi (fun index tupleItem ->
                tupleItem.namesMap
                |> Map.map (fun _ param ->
                    adjustDestructurePath (InverseTuple (uint index, param.destructurePath)) param))
            |> TOM.fold<_, _> Map.merge Map.empty


        | Q.DestructuredCons patterns ->
            patterns
            |> TOM.map gatherParams
            |> TOM.mapi (fun index params_ ->
                params_.namesMap
                |> Map.map (fun _ param_ ->
                    adjustDestructurePath (InverseCons (uint index, param_.destructurePath)) param_))
            |> TOM.fold<_, _> Map.merge Map.empty

        | Q.DestructuredTypeVariant (ctor, params_) ->
            params_
            |> List.map gatherParams
            |> List.mapi (fun index params__ ->
                params__.namesMap
                |> Map.map (fun _ param_ ->
                    adjustDestructurePath (InverseTypeVariant (ctor, uint index, param_.destructurePath)) param_))
            |> List.fold Map.merge Map.empty








    /// This gathers all the type params present in a mentionable type recursively. Useful for constructing the implicit map of type parameters for value type annotations.
    let rec gatherTypeParams (typeExpr : C.MentionableType) : LowerIdent set =
        match typeExpr with
        | S.GenericTypeVar unqual ->
            convertValueIdentifierToLowerIdent unqual
            |> Set.singleton

        | S.UnitType -> Set.empty

        | S.Tuple tuple ->
            TOM.map (S.getNode >> gatherTypeParams) tuple.types
            |> TOM.toList
            |> Set.unionMany

        | S.Record record ->
            Map.values record.fields
            |> Seq.map (S.getNode >> gatherTypeParams)
            |> Set.unionMany

        | S.ExtendedRecord extendedRec ->
            Map.values extendedRec.fields
            |> Seq.map (S.getNode >> gatherTypeParams)
            |> Set.unionMany
            |> Set.add (convertValueIdentifierToLowerIdent extendedRec.extendedAlias.node)

        | S.ReferencedType (typeParams = typeParams) ->
            List.map (S.getNode >> gatherTypeParams) typeParams
            |> Set.unionMany

        | S.Arrow (fromType, toTypes) ->
            toTypes
            |> NEL.map (S.getNode >> gatherTypeParams)
            |> NEL.toList
            |> Set.unionMany
            |> Set.union (gatherTypeParams fromType.node)


        | S.Parensed expr -> gatherTypeParams expr.node

    /// Note: No need to update `resolvedNames` at every recursion step here because no new names can be declared inside a mentioned type!
    let rec qualifyMentionableType
        (resolvedNames : NamesInScope)
        (mentionableType : C.MentionableType)
        : Result<Q.MentionableType, Identifier list> =
        let rec innerFunc mentionableType : Result<Q.MentionableType, Identifier list> =
            match mentionableType with
            | S.UnitType -> Ok Q.UnitType

            | S.GenericTypeVar v ->
                match tryFindTypeParam v resolvedNames with
                | Some (_, typeParam) -> Q.GenericTypeVar typeParam |> Ok
                | None -> SingleValueIdentifier v |> List.singleton |> Error

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
                    alias
                    |> S.mapNode (flip tryFindTypeParam resolvedNames)
                    |> liftOptionFromCstNode
                    |> Result.ofOption (
                        alias.node
                        |> SingleValueIdentifier
                        |> List.singleton
                    )

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
                    typeName.node
                    |> flip tryFindTypeDeclaration resolvedNames
                    |> Result.ofOption [ convertTypeOrModuleIdentifierToIdentifier typeName.node ]
                    |> Result.map snd

                let resolvedTypeParams = typeParams |> qualifyListCstNodes innerFunc

                (resolvedTypeNameOpt, resolvedTypeParams)
                ||> Result.map2
                        (fun resolvedTypeName resolvedTypeParams' ->
                            Q.ReferencedType (resolvedTypeName, resolvedTypeParams'))
                        (@)

            | S.Arrow (fromType, toTypes) ->
                let resolvedFrom =
                    S.mapNode innerFunc fromType
                    |> liftResultFromCstNode

                let resolvedTos = toTypes |> qualifyNelCstNodes innerFunc

                (resolvedFrom, resolvedTos)
                ||> Result.map2 (fun from tos -> Q.Arrow (from, tos)) (@)

            | S.Parensed parensed -> innerFunc parensed.node


        innerFunc mentionableType



    and qualifyTypeDeclaration
        (resolvedNames : NamesInScope)
        (declaration : S.TypeDeclaration<TypeOrModuleIdentifier>)
        : Result<Q.TypeDeclaration, Identifier list> =
        match declaration with
        | S.Alias { typeParams = typeParams
                    referent = referent } ->

            let typeParamsMap =
                typeParams
                |> List.map makeNewTypeParam
                |> Map.ofList

            let newResolvedNames =
                typeParamsMap
                |> Map.fold (fun names name value -> addNewTypeParam name value names) resolvedNames

            let mentionableType =
                qualifyCstNodeAndLiftResult (qualifyMentionableType newResolvedNames) referent

            mentionableType
            |> Result.map (fun type' ->
                Q.Alias
                    { referent = type'
                      typeParams =
                        typeParamsMap
                        |> Map.mapKeyVal (fun name (_, resolved) -> resolved, convertValueIdentifierToLowerIdent name) })

        | S.Sum newType ->
            qualifyNewTypeDeclaration resolvedNames newType
            |> Result.map Q.Sum


    and qualifyNewTypeDeclaration
        (resolvedNames : NamesInScope)
        { typeParams = typeParams
          variants = variants }
        : Result<Q.NewTypeDeclaration, Identifier list> =

        let typeParamsMap =
            typeParams
            |> List.map makeNewTypeParam
            |> Map.ofList

        let newResolvedNames =
            typeParamsMap
            |> Map.fold (fun names name value -> addNewTypeParam name value names) resolvedNames

        let resolvedVariants =
            variants
            |> qualifyNelCstNodes (fun (variantCase : C.VariantCase) ->
                variantCase.contents
                |> qualifyListCstNodes (qualifyMentionableType newResolvedNames)
                |> Result.map (fun contents' ->
                    let label = S.mapNode unqualTypeToUpperIdent variantCase.label

                    { Q.label = label
                      Q.contents = contents' }))

        match resolvedVariants with
        | Ok variants' ->
            { Q.variants = NEL.map (fun variant -> makeResolvedTypeConstructor (), variant) variants'
              Q.typeParams =
                typeParamsMap
                |> Map.mapKeyVal (fun name (_, resolved) -> resolved, convertValueIdentifierToLowerIdent name) }
            |> Ok
        | Error err -> Error err



    and qualifyAssignmentPattern
        (resolvedNames : NamesInScope)
        (assignmentPattern : C.AssignmentPattern)
        : Result<Q.AssignmentPattern, Identifier list> =
        match assignmentPattern with
        | S.Named name ->
            Q.Named (makeResolvedLower (), unqualValToLowerIdent name)
            |> Ok
        | S.Ignored -> Ok Q.Ignored
        | S.Unit -> Ok Q.Unit

        | S.DestructuredPattern pattern ->
            qualifyDestructuredPattern resolvedNames pattern
            |> Result.map Q.DestructuredPattern

        | S.Aliased (pattern, alias) ->
            qualifyCstNodeAndLiftResult (qualifyAssignmentPattern resolvedNames) pattern
            |> Result.map (fun pattern' ->
                Q.Aliased (pattern', (makeResolvedLower (), S.mapNode unqualValToLowerIdent alias)))


    and qualifyDestructuredPattern
        (resolvedNames : NamesInScope)
        (destructuredPattern : C.DestructuredPattern)
        : Result<Q.DestructuredPattern, Identifier list> =
        match destructuredPattern with
        | S.DestructuredRecord record ->
            record
            |> NEL.map (
                S.mapNode unqualValToLowerIdent
                >> Tuple.makePairWithFst (makeResolvedLower ())
            )
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
                |> flip tryFindTypeConstructor resolvedNames
                |> Result.ofOption [ convertTypeOrModuleIdentifierToIdentifier ctor.node ]
                |> Result.map snd

            let resolvedParams =
                params'
                |> qualifyListCstNodes (qualifyAssignmentPattern resolvedNames)


            (resolvedCtor, resolvedParams)
            ||> Result.map2 (fun ctor' resolvedParams' -> Q.DestructuredTypeVariant (ctor', resolvedParams')) (@)









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
                |> Result.map (fun qualVal -> S.mapNode unqualValToRecField fieldName, qualVal))
            |> Result.sequenceList
            |> combineUnresolvedIdents
            |> Result.map Q.CompoundValues.Record

        | S.CompoundValues.RecordExtension (extendedRec, fields) ->
            let unqualExendedIdent = UnqualValue extendedRec.node
            let extendedIdent = convertValueIdentifierToIdentifier unqualExendedIdent
            let convertedExtendedRec = tryFindValue unqualExendedIdent resolvedNames

            match convertedExtendedRec with
            | Some (_, resolved) ->
                fields
                |> NEL.map (fun (fieldName, fieldVal) ->
                    qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx resolvedNames) fieldVal
                    |> Result.map (fun qualVal -> fieldName, qualVal))
                |> NEL.sequenceResult
                |> combineUnresolvedIdents
                |> Result.map (fun qualFields ->
                    let mappedFields =
                        qualFields
                        |> NEL.map (Tuple.mapFst (S.mapNode unqualValToRecField))

                    Q.CompoundValues.RecordExtension (
                        S.mapNode (fun unqual -> resolved, unqualValToLowerIdent unqual) extendedRec,
                        mappedFields
                    ))
            | None -> Error [ extendedIdent ]



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
                        addFuncParams resolvedNames funcParams
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
                                let paramsMap = NEL.map gatherParams params'

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
                    | LocalName _
                    | Param _ ->
                        match lower with
                        | QualifiedValue qual ->
                            failwithf
                                "This shouldn't be possible. To fix this we'd need to create another lowercase name resolution map exclusively for qualified value paths"

                        | UnqualValue (UnqualValueIdentifier unqual) ->
                            let lowerName = LowerIdent unqual |> LocalOrParam

                            Q.LowerIdentifier (lowerName, resolvedLower)
                            |> Q.SingleValueExpression
                            |> Ok

                    | TopLevelName topLevel ->
                        Q.LowerIdentifier (TopLevelValue topLevel.fullName, resolvedLower)
                        |> Q.SingleValueExpression
                        |> Ok

                | None ->
                    convertValueIdentifierToIdentifier lower
                    |> List.singleton
                    |> Error

            | S.LetExpression (bindings, expr) ->
                let letBindings =
                    bindings
                    |> qualifyNelCstNodes (fun binding ->
                        addParamAssignment resolvedNames binding.bindPattern
                        |> Result.map (fun paramsMap ->
                            paramsMap
                            |> Map.mapKeyVal (fun unqual values ->
                                unqual,
                                values
                                |> SOD.map (fun (tokens, path) ->
                                    { LocalName.tokens = tokens
                                      LocalName.destructurePath = path
                                      // @TODO: we're actually duplicating the same assigned expression for each name binding. Which means we'll have to duplicate the qualifying of that same expression for each name binding all over again. Would be good if we could ensure we only qualify each expression only once.
                                      LocalName.assignedExpression = binding.value.node },
                                    makeResolvedLower ()))))
                    |> Result.map (
                        NEL.toList
                        >> List.map S.getNode
                        >> combineReferenceMaps
                    )


                let qualifiedLetBindings : Result<Q.LetDeclarationNames, Identifier list> =
                    letBindings
                    |> Result.map (
                        Map.map (fun unqual values ->
                            let localName, resolved = SOD.getFirst values
                            let ident = convertValueIdentifierToLowerIdent unqual

                            qualifyExpression moduleCtx resolvedNames localName.assignedExpression
                            |> Result.map (fun qualifiedExpression ->
                                resolved,
                                { Q.ResolvedLetBinding.ident = ident
                                  Q.ResolvedLetBinding.tokens = localName.tokens
                                  Q.ResolvedLetBinding.destructurePath = localName.destructurePath
                                  Q.ResolvedLetBinding.assignedExpression = qualifiedExpression }))
                    )
                    |> Result.bind (
                        Map.sequenceResult
                        >> Result.mapError (Map.values >> List.concat)
                    )
                    |> Result.map (Map.mapKeyVal (fun _ (resolved, binding) -> resolved, binding))


                let qualExpr =
                    letBindings
                    |> Result.map (
                        Map.mapKeyVal (fun unqual values ->
                            UnqualValue unqual,
                            values
                            |> SOD.map (fun (localNameBinding, resolvedLower) ->
                                (LocalName localNameBinding, resolvedLower)))
                    )
                    |> Result.map (fun bindingsNames ->
                        combineTwoResolvedNamesMaps resolvedNames { empty with valueDeclarations = bindingsNames })
                    |> Result.bind (fun names -> qualifyCstNodeAndLiftResult (qualifyExpression moduleCtx names) expr)
                    |> Result.map S.getNode

                Result.map2
                    (fun expr' bindings' ->
                        Q.LetExpression (bindings', expr')
                        |> Q.SingleValueExpression)
                    (@)
                    qualExpr
                    qualifiedLetBindings

            //| Error err -> Error err

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
                                    addParamAssignment resolvedNames assignPattern
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
        let resolvedNames = resolveModuleBindings ylModule

        let qualifySingleDeclaration (decl : C.Declaration) : Result<Q.Declaration, Identifier list> =
            match decl with
            | S.ImportDeclaration import -> failwithf "@TODO: Importing other modules is not implemented yet!"
            | S.TypeDeclaration (name = name; declaration = decl) ->
                let resolved =
                    tryFindTypeDeclaration (UnqualType name.node) resolvedNames
                    |> Option.map snd
                    |> Result.ofOption [ TypeNameOrVariantOrTopLevelModule name.node ]

                let typeDeclResult = qualifyTypeDeclaration resolvedNames decl

                (resolved, typeDeclResult)
                ||> Result.map2
                        (fun resolved_ typeDecl ->
                            Q.TypeDeclaration (resolved_, S.mapNode unqualTypeToUpperIdent name, typeDecl))
                        (@)

            | S.ValueTypeAnnotation { valueName = valueName
                                      annotatedType = annotatedType } ->

                let theseTypeParams : TypeParams =
                    gatherTypeParams annotatedType.node
                    |> Seq.map (fun ident -> lowerIdentToUnqualVal ident, (List.empty, makeResolvedTypeParam ()))
                    |> Seq.fold (fun map (ident, value) -> addNewReference ident value map) Map.empty

                let combinedTypeParams : TypeParams =
                    combineTwoReferenceMaps theseTypeParams resolvedNames.typeParams

                let newResolvedNames = { resolvedNames with typeParams = combinedTypeParams }

                let resolvedName =
                    tryFindValueTypeDeclarations (UnqualValue valueName.node) newResolvedNames
                    |> Option.map snd
                    |> Result.ofOption [ SingleValueIdentifier valueName.node ]

                let qualifiedAnnotatedType =
                    qualifyCstNodeAndLiftResult (qualifyMentionableType newResolvedNames) annotatedType

                (resolvedName, qualifiedAnnotatedType)
                ||> Result.map2
                        (fun resolved_ qualified ->
                            let implicitParams =
                                theseTypeParams
                                |> Map.mapKeyVal (fun key vals ->
                                    let (_, resolvedParam) = SOD.getFirst vals
                                    resolvedParam, unqualValToLowerIdent key)

                            Q.ValueTypeAnnotation (
                                resolved_,
                                { Q.ValueAnnotation.valueName = S.mapNode unqualValToLowerIdent valueName
                                  Q.ValueAnnotation.gatheredImplicitParams = implicitParams
                                  Q.ValueAnnotation.annotatedType = qualified }
                            ))
                        (@)

            | S.ValueDeclaration { valueName = valueName; value = value } ->
                let result =
                    qualifyCstNodeAndLiftResult (qualifyExpression ylModule resolvedNames) value

                let resolvedName =
                    tryFindValue (UnqualValue valueName.node) resolvedNames
                    |> Option.map snd
                    |> Result.ofOption [ SingleValueIdentifier valueName.node ]

                (resolvedName, result)
                ||> Result.map2
                        (fun resolved res ->
                            Q.ValueDeclaration (
                                resolved,
                                { Q.ValueDeclaration.valueName = S.mapNode unqualValToLowerIdent valueName
                                  Q.ValueDeclaration.value = res }
                            ))
                        (@)


        let declarations : Result<S.CstNode<Q.Declaration> list, Identifier list> =
            qualifyListCstNodes qualifySingleDeclaration ylModule.declarations


        match declarations with
        | Ok decls ->

            let (types, values, valueTypes) =
                decls
                |> List.typedPartition3 (fun decl ->
                    match decl.node with
                    | Q.ImportDeclaration import -> failwithf "@TODO: cross-module imports not yet supported"
                    | Q.TypeDeclaration (resolved, name, typeDecl) -> Choice1Of3 (resolved, name, typeDecl)
                    | Q.ValueDeclaration (resolved, valDecl) -> Choice2Of3 (resolved, valDecl)
                    | Q.ValueTypeAnnotation (resolved, valAnn) -> Choice3Of3 (resolved, valAnn))

            { Q.YlModule.moduleDecl = ylModule.moduleDecl
              Q.YlModule.imports = List.empty // @TODO: actually include the imports here
              Q.YlModule.types =
                types
                |> List.map (fun (res, ident, decl) -> res, (ident.node, decl))
                |> Map.ofList

              Q.YlModule.values =
                  values
                  |> List.map (fun (res, value) -> res, (value.valueName.node, value))
                  |> Map.ofList

              Q.YlModule.valueTypes =
                  valueTypes
                  |> List.map (fun (res, value) -> res, (value.valueName.node, value))
                  |> Map.ofList }
            |> Ok
        | Error err -> Error err







    (* Traverse the CST and gather named types/vals *)

    and makeNewTypeParam (name : S.CstNode<UnqualValueIdentifier>) =
        name.node, (name.source, makeResolvedTypeParam ())


    and makeNewTypeDeclaration (name : UnqualTypeOrModuleIdentifier) =
        UnqualType name, makeResolvedTypeName ()


    and makeTypeConstructor
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (variantName : S.CstNode<UnqualTypeOrModuleIdentifier>)
        (variantCase : Cst.VariantCase)
        (typeDeclaration : Cst.NewTypeDeclaration)
        =
        let variantCtor : VariantConstructor =
            { typeDeclaration = typeDeclaration
              variantCase = variantCase
              fullName = convertTypeOrModuleIdentifierToFullyQualified moduleName (UnqualType variantName.node) }

        UnqualType variantName.node, (variantCtor, makeResolvedTypeConstructor ())

    and makeValue (name : S.CstNode<UnqualValueIdentifier>) =
        UnqualValue name.node, makeResolvedLower ()

    and makeValueTypeDeclaration (name : S.CstNode<UnqualValueIdentifier>) =
        UnqualValue name.node, makeResolvedLower ()






    and addNewTypeParam
        (name : UnqualValueIdentifier)
        (value : (TokenWithSource list * ResolvedTypeParam))
        (names : NamesInScope)
        : NamesInScope =
        { names with typeParams = addNewReference name value names.typeParams }

    and addNewTypeName
        (name : TypeOrModuleIdentifier)
        (value : (Cst.TypeDeclaration * ResolvedType))
        (names : NamesInScope)
        : NamesInScope =
        { names with typeDeclarations = addNewReference name value names.typeDeclarations }


    and addTypeConstructor
        (variantName : TypeOrModuleIdentifier)
        (value : (VariantConstructor * ResolvedTypeConstructor))
        (names : NamesInScope)
        =
        { names with typeConstructors = addNewReference variantName value names.typeConstructors }

    and addValue
        (name : ValueIdentifier)
        (value : (LowerCaseName * ResolvedValue))
        (names : NamesInScope)
        : NamesInScope =
        { names with valueDeclarations = addNewReference name value names.valueDeclarations }

    and addValueTypeDeclaration
        (name : ValueIdentifier)
        (value : (S.CstNode<ConcreteSyntaxTree.MentionableType> * ResolvedValue))
        (names : NamesInScope)
        =
        { names with valueTypeDeclarations = addNewReference name value names.valueTypeDeclarations }











































    (* Make name maps from expressions *)



    /// Get all the exposed names from a single assignment pattern
    and addParamAssignment
        (names : NamesInScope)
        (assignmentPattern : S.CstNode<Cst.AssignmentPattern>)
        : Result<ParamsInScope, Identifier list> =
        match assignmentPattern.node with
        | S.Named ident ->
            Map.empty
            |> addNewParamReference (S.makeCstNode ident assignmentPattern.source) SimpleName
            |> Ok

        | S.Ignored -> Ok Map.empty
        | S.Unit -> Ok Map.empty
        | S.Aliased (alias = alias; pattern = pattern) ->
            addParamAssignment names pattern
            |> Result.map (addNewParamReference alias SimpleName)

        | S.DestructuredPattern pattern -> addDestructuredParam names (S.makeCstNode pattern assignmentPattern.source)



    /// We need to recursively go down all the sub-destructurings, because all of those still get exposed to the same scope. Unlike let bindings in sub-expressions which don't get propagated upward.
    and addDestructuredParam
        (names : NamesInScope)
        (pattern : S.CstNode<Cst.DestructuredPattern>)
        : Result<ParamsInScope, Identifier list> =
        let getParamsMapForEach
            (putInPath : PathToDestructuredName -> PathToDestructuredName)
            assignmentPattern
            : Result<ParamsInScope, Identifier list> =
            addParamAssignment names assignmentPattern
            |> Result.map (mapResolvedParams putInPath)


        match pattern.node with
        | S.DestructuredRecord fieldNames ->
            fieldNames
            |> NEL.fold<_, _> (fun map fieldName -> addNewParamReference fieldName InverseRecord map) Map.empty
            |> Ok

        | S.DestructuredTuple items ->
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

        | S.DestructuredCons items ->
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

        | S.DestructuredTypeVariant (constructor, params_) ->
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










    and addFuncParams
        (names : NamesInScope)
        ({ params_ = params_ } : Cst.FunctionValue)
        : Result<NamesInScope, Identifier list> =
        let values =
            params_
            |> NEL.map (
                addParamAssignment names
                >> Result.map (
                    Map.mapKeyVal (fun key tokensAndValues ->
                        UnqualValue key,
                        tokensAndValues
                        |> SingleOrDuplicate.map (fun (tokens, path) ->
                            Param
                                { ident = unqualValToLowerIdent key
                                  tokens = tokens
                                  destructurePath = path },
                            makeResolvedLower ()))
                )
            )
            |> NEL.sequenceResult
            |> Result.map (NEL.toList >> combineReferenceMaps)
            |> combineUnresolvedIdents

        values
        |> Result.map (fun vals -> { empty with valueDeclarations = vals })


    and addLetBinding
        (names : NamesInScope)
        ({ bindPattern = bindPattern
           value = value } : Cst.LetBinding)
        : Result<NamesInScope, Identifier list> =

        let values : Result<ValueDeclarations, Identifier list> =
            addParamAssignment names bindPattern
            |> Result.map (fun resolvedParam ->
                resolvedParam
                |> Map.mapKeyVal (fun key tokensAndValues ->
                    UnqualValue key,
                    tokensAndValues
                    |> SingleOrDuplicate.map (fun (tokens, path) ->
                        LocalName
                            { destructurePath = path
                              tokens = tokens
                              assignedExpression = value.node },
                        makeResolvedLower ())))

        values
        |> Result.map (fun vals -> { empty with valueDeclarations = vals })


    and addLetExpression (names : NamesInScope) (bindings : S.CstNode<Cst.LetBinding> nel) =
        bindings
        |> NEL.toList
        |> Seq.map (S.getNode >> addLetBinding names)
        |> Result.sequence
        |> Result.map combineResolvedNamesMaps
        |> combineUnresolvedIdents




    and resolveTypeAndConstructors
        (moduleName : QualifiedModuleOrTypeIdentifier)
        (typeName : S.CstNode<UnqualTypeOrModuleIdentifier>)
        (typeDeclaration : Cst.TypeDeclaration)
        : NamesInScope =
        let (name, resolved) = makeNewTypeDeclaration typeName.node
        let withTypeNames = addNewTypeName name (typeDeclaration, resolved) empty

        match typeDeclaration with
        | S.Alias _ ->
            // We're not accounting for record alias constructors just yet
            withTypeNames

        | S.Sum newTypeDecl ->
            newTypeDecl.variants
            |> NEL.fold<_, _>
                (fun map variant ->
                    let (ident, (ctor, resolvedCtor)) =
                        makeTypeConstructor moduleName variant.node.label variant.node newTypeDecl

                    addTypeConstructor ident (ctor, resolvedCtor) map)
                withTypeNames




    /// This creates a names map with all the declared types, type constructors, and top level values in scope without going into any of the expressions. That way we can make sure that types and values can references types and values declared further down the file.
    and resolveModuleBindings (ylModule : Cst.YlModule) : NamesInScope =
        let moduleName = ylModule.moduleDecl.moduleName.node

        /// A quick scan of the module to gather all top level names
        let addSingleDeclaration (declaration : S.CstNode<Cst.Declaration>) =
            match declaration.node with
            | S.ImportDeclaration _ ->
                // @TODO: I'll need to implement the cross-module name resolution here!
                failwithf "@TODO: need to implement cross-module name resolution!"

            | S.TypeDeclaration (name, decl) -> resolveTypeAndConstructors moduleName name decl

            | S.ValueTypeAnnotation { valueName = valueName
                                      annotatedType = annotatedType } ->

                let (ident, resolved) = makeValueTypeDeclaration valueName

                addValueTypeDeclaration ident (annotatedType, resolved) empty

            | S.ValueDeclaration { valueName = valueName; value = value } ->
                let (ident, resolved) = makeValue valueName

                empty
                |> addValue
                    ident
                    (TopLevelName
                        { tokens = valueName.source
                          assignedExpression = value.node
                          fullName = reifyLower moduleName valueName.node },
                     resolved)

        ylModule.declarations
        |> List.map addSingleDeclaration
        |> combineResolvedNamesMaps

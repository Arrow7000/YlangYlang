module MakeQualified

open Lexer
module S = SyntaxTree
module C = ConcreteSyntaxTree

open NameResolution
open QualifiedSyntaxTree


/// This determines whether type variables need to have been declared, or if they can be declared explicitly
type MentionableTypeContext =
    /// Type variables need to be declared!
    | InTypeDeclaration
    /// Type vars don't need to be declared
    | InValueTypeAnnotation

type CstWithUnresolveds<'a> =
    { cst : 'a
      unresolveds : Identifier list }



let liftResultFromCstNode (cstNode : S.CstNode<Result<'a, 'b>>) : Result<S.CstNode<'a>, 'b> =
    match cstNode.node with
    | Ok ok -> Ok <| S.makeCstNode ok cstNode.source
    | Error err -> Error err

let liftOptionFromCstNode (cstNode : S.CstNode<'a option>) : S.CstNode<'a> option =
    match cstNode.node with
    | Some ok -> Some <| S.makeCstNode ok cstNode.source
    | None -> None

let private convertTypeOrModuleIdentifierToIdentifier : TypeOrModuleIdentifier -> Identifier =
    function
    | QualifiedType ident -> ModuleSegmentsOrQualifiedTypeOrVariant ident
    | UnqualType ident -> TypeNameOrVariantOrTopLevelModule ident

let private convertValueIdentifierToIdentifier : ValueIdentifier -> Identifier =
    function
    | QualifiedValue ident -> QualifiedPathValueIdentifier ident
    | UnqualValue ident -> SingleValueIdentifier ident




let qualifyCstNode
    (qualifyThing : 'a -> Result<'b, Identifier list>)
    : S.CstNode<'a> -> Result<S.CstNode<'b>, Identifier list> =
    S.mapNode qualifyThing >> liftResultFromCstNode



let qualifyListCstNodes (qualifyThing : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> list) =
    list
    |> Result.traverse (qualifyCstNode qualifyThing)
    |> Result.mapError (NEL.toList >> List.concat)

/// Lil' helper for qualifying and merging an NEL of CstNodes, which we're doing pretty often in the code below
let qualifyNelCstNodes (qualifyThing : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> nel) =
    list
    |> NEL.traverseResult (qualifyCstNode qualifyThing)
    |> Result.mapError (NEL.toList >> List.concat)


let qualifyTomCstNodes (qualifyThing : 'a -> Result<'b, Identifier list>) (list : SyntaxTree.CstNode<'a> tom) =
    list
    |> TOM.traverseResult (qualifyCstNode qualifyThing)
    |> Result.mapError (NEL.toList >> List.concat)



/// Note: No need to update `resolvedNames` at every recursion step here because no new names can be declared inside a mentioned type!
let qualifyMentionableType
    (typeCtx : MentionableTypeContext)
    (resolvedNames : NamesInScope)
    (unqual : C.MentionableType)
    : Result<MentionableType, Identifier list> =
    let rec innerFunc mentionableType : Result<MentionableType, Identifier list> =
        match mentionableType with
        | S.UnitType -> Ok S.UnitType
        | S.GenericTypeVar v ->

            match typeCtx with
            | InTypeDeclaration ->
                match tryFindTypeParam v resolvedNames with
                | Some _ -> S.GenericTypeVar v |> Ok
                | None -> SingleValueIdentifier v |> List.singleton |> Error
            | InValueTypeAnnotation -> S.GenericTypeVar v |> Ok

        | S.Tuple { types = types } ->
            let mappedTypes =
                types
                |> TOM.traverseResult (qualifyCstNode innerFunc)

            match mappedTypes with
            | Ok okTypes -> Ok <| S.Tuple { types = okTypes }
            | Error e -> NEL.toList e |> List.concat |> Error
        | S.Record { fields = fields } ->
            let mappedFields =
                fields
                |> Map.map (fun _ -> qualifyCstNode innerFunc)
                |> Map.sequenceResult

            match mappedFields with
            | Ok okFields -> Ok <| S.Record { fields = okFields }
            | Error err ->
                Map.values err
                |> Seq.toList
                |> List.concat
                |> Error

        | S.ExtendedRecord { fields = fields
                             extendedAlias = alias } ->
            let mappedFields =
                fields
                |> Map.map (fun _ -> qualifyCstNode innerFunc)
                |> Map.sequenceResult

            match mappedFields with
            | Ok okFields ->
                S.ExtendedRecord
                    { fields = okFields
                      extendedAlias = alias }
                |> Ok
            | Error err ->
                Map.values err
                |> Seq.toList
                |> List.concat
                |> Error

        | S.ReferencedType (typeName = typeName; typeParams = typeParams) ->
            let resolvedTypeName =
                NameResolution.tryFindTypeDeclaration (S.getNode typeName) resolvedNames
                |> Option.map snd

            let resolvedTypeParams = typeParams |> qualifyListCstNodes innerFunc

            match resolvedTypeName, resolvedTypeParams with
            | Some { tokens = tokens; fullName = fullName }, Ok resolvedTypeParams' ->
                S.ReferencedType (S.makeCstNode fullName tokens, resolvedTypeParams')
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

            match resolvedFrom, resolvedTos with
            | Ok first, Ok rest -> S.Arrow (first, rest) |> Ok

            | Error err1, Error err2 -> Error (err1 @ err2)
            | Ok _, Error err
            | Error err, Ok _ -> Error err

        | S.Parensed parensed -> innerFunc parensed.node


    innerFunc unqual



let qualifyTypeDeclaration resolvedNames declaration : Result<TypeDeclaration, Identifier list> =
    match declaration with
    | S.Alias { typeParams = typeParams
                referent = referent } ->

        let resolvedWithTypeParams =
            typeParams
            |> List.fold (flip addNewTypeParam) resolvedNames

        let mentionableType =
            qualifyCstNode (qualifyMentionableType InTypeDeclaration resolvedWithTypeParams) referent

        match mentionableType with
        | Ok type' ->
            S.Alias
                { referent = type'
                  typeParams = typeParams }
            |> Ok
        | Error err -> Error err
    | S.Sum { typeParams = typeParams
              variants = variants } ->

        let resolvedWithTypeParams =
            typeParams
            |> List.fold (flip addNewTypeParam) resolvedNames

        let resolvedVariants =
            variants
            |> qualifyNelCstNodes (fun (variantCase : C.VariantCase) ->
                let contents =
                    variantCase.contents
                    |> qualifyListCstNodes (qualifyMentionableType InTypeDeclaration resolvedWithTypeParams)

                match contents with
                | Ok contents' ->
                    Ok
                        { S.label = variantCase.label
                          S.contents = contents' }
                | Error err -> Error err)

        match resolvedVariants with
        | Ok variants' ->
            S.Sum
                { variants = variants'
                  typeParams = typeParams }
            |> Ok
        | Error err -> Error err


let rec qualifyDestructuredPattern
    (resolvedNames : NamesInScope)
    (destructuredPattern : C.DestructuredPattern)
    : Result<DestructuredPattern, Identifier list> =
    match destructuredPattern with
    | S.DestructuredRecord record -> Ok <| S.DestructuredRecord record
    | S.DestructuredTuple tuple ->
        tuple
        |> qualifyTomCstNodes (qualifyAssignmentPattern resolvedNames)
        |> Result.map S.DestructuredTuple



    | S.DestructuredCons pattern ->
        pattern
        |> qualifyTomCstNodes (qualifyAssignmentPattern resolvedNames)
        |> Result.map S.DestructuredCons

    | S.DestructuredTypeVariant (ctor, params') ->
        let resolvedCtor =
            ctor
            |> S.mapNode (fun ctor' ->
                NameResolution.tryFindTypeConstructor ctor' resolvedNames
                |> Option.map (fun (_, variant) -> variant.fullName))
            |> liftOptionFromCstNode

        let resolvedParams =
            params'
            |> qualifyListCstNodes (qualifyAssignmentPattern resolvedNames)

        match resolvedCtor, resolvedParams with
        | Some resolvedCtor', Ok resolvedParams' ->
            S.DestructuredTypeVariant (resolvedCtor', resolvedParams')
            |> Ok
        | None, Ok _ ->
            convertTypeOrModuleIdentifierToIdentifier ctor.node
            |> List.singleton
            |> Error
        | Some _, Error err -> Error err
        | None, Error err ->
            (convertTypeOrModuleIdentifierToIdentifier ctor.node
             :: err)
            |> Error

and qualifyAssignmentPattern
    (resolvedNames : NamesInScope)
    (assignmentPattern : C.AssignmentPattern)
    : Result<AssignmentPattern, Identifier list> =
    match assignmentPattern with
    | S.Named name -> Ok <| S.Named name
    | S.Ignored -> Ok S.Ignored
    | S.Unit -> Ok S.Unit
    | S.DestructuredPattern pattern ->
        qualifyDestructuredPattern resolvedNames pattern
        |> Result.map S.DestructuredPattern
    | S.Aliased (pattern, alias) ->
        let qualifiedPattern =
            qualifyCstNode (qualifyAssignmentPattern resolvedNames) pattern

        match qualifiedPattern with
        | Ok pattern' -> S.Aliased (pattern', alias) |> Ok
        | Error err -> Error err






let rec qualifyCompoundExpression resolvedNames compExpr =
    match compExpr with
    | S.List list ->
        list
        |> qualifyListCstNodes (qualifyExpression resolvedNames)
        |> Result.map S.List

    | S.CompoundValues.Tuple items ->
        items
        |> qualifyTomCstNodes (qualifyExpression resolvedNames)
        |> Result.map S.CompoundValues.Tuple

    | S.CompoundValues.Record fields ->
        fields
        |> List.map (fun (fieldName, fieldVal) ->
            qualifyCstNode (qualifyExpression resolvedNames) fieldVal
            |> Result.map (fun qualVal -> fieldName, qualVal))
        |> Result.sequence
        |> Result.mapError (NEL.toList >> List.concat)
        |> Result.map S.CompoundValues.Record

    | S.CompoundValues.RecordExtension (extendedRec, fields) ->
        fields
        |> NEL.map (fun (fieldName, fieldVal) ->
            qualifyCstNode (qualifyExpression resolvedNames) fieldVal
            |> Result.map (fun qualVal -> fieldName, qualVal))
        |> NEL.sequenceResult
        |> Result.mapError (NEL.toList >> List.concat)
        |> Result.map (fun qualFields -> S.CompoundValues.RecordExtension (extendedRec, qualFields))



and qualifyExpression (resolvedNames : NamesInScope) (expression : C.Expression) : Result<Expression, Identifier list> =
    match expression with
    | S.ParensedExpression expr -> qualifyExpression resolvedNames expr
    | S.SingleValueExpression singleExpr ->
        match singleExpr with
        | S.ExplicitValue expl ->
            match expl with
            | S.Compound comp ->
                qualifyCompoundExpression resolvedNames comp
                |> Result.map (
                    S.Compound
                    >> S.ExplicitValue
                    >> S.SingleValueExpression
                )

            | S.Primitive prim ->
                S.Primitive prim
                |> S.ExplicitValue
                |> S.SingleValueExpression
                |> Ok

            | S.DotGetter field ->
                S.DotGetter field
                |> S.ExplicitValue
                |> S.SingleValueExpression
                |> Ok

            | S.Function ({ params_ = params_; body = body } as funcParams) ->
                let qualifiedParams =
                    params_
                    |> qualifyNelCstNodes (qualifyAssignmentPattern resolvedNames)

                let resolvedWithFuncParams =
                    resolvedNames
                    |> NameResolution.combineTwoResolvedNamesMaps (resolveFuncParams funcParams)

                let qualified =
                    S.mapNode (qualifyExpression resolvedWithFuncParams) body
                    |> liftResultFromCstNode

                match qualified, qualifiedParams with
                | Ok expr, Ok params' ->
                    S.Function { body = expr; params_ = params' }
                    |> S.ExplicitValue
                    |> S.SingleValueExpression
                    |> Ok
                | Ok _, Error err
                | Error err, Ok _ -> Error err
                | Error err1, Error err2 -> Error (err1 @ err2)

        | S.UpperIdentifier upper ->
            let resolved =
                NameResolution.tryFindTypeConstructor upper resolvedNames
                |> Option.map snd

            match resolved with
            | Some res ->
                S.UpperIdentifier res.fullName
                |> S.SingleValueExpression
                |> Ok
            | None ->
                convertTypeOrModuleIdentifierToIdentifier upper
                |> List.singleton
                |> Error

        | S.LowerIdentifier lower ->
            let resolved = NameResolution.tryFindValue lower resolvedNames

            match resolved with
            | Some res ->
                match res with
                | LocalName _
                | Param _ ->
                    match lower with
                    | QualifiedValue qual ->
                        failwithf
                            "This shouldn't be possible. To fix this we'd need to create another lowercase name resolution map exclusively for qualified value paths"
                    | UnqualValue (UnqualValueIdentifier unqual) ->
                        LowerIdent unqual
                        |> LocalVariableOrParamIdent
                        |> LocalOrParam
                        |> S.LowerIdentifier
                        |> S.SingleValueExpression
                        |> Ok
                | TopLevelName topLevel ->
                    TopLevelValue topLevel.fullName
                    |> S.LowerIdentifier
                    |> S.SingleValueExpression
                    |> Ok

            | None ->
                convertValueIdentifierToIdentifier lower
                |> List.singleton
                |> Error

        | S.LetExpression (bindings, expr) ->
            let namesMap =
                resolvedNames
                |> NameResolution.combineTwoResolvedNamesMaps (NameResolution.resolveLetExpression bindings)

            let qualBindings =
                bindings
                |> qualifyNelCstNodes (fun binding ->
                    let qualBinding =
                        qualifyCstNode (qualifyAssignmentPattern namesMap) binding.bindPattern

                    let qualExpr = qualifyCstNode (qualifyExpression namesMap) binding.value

                    Result.map2
                        (fun binding' expr' ->
                            { S.LetBinding.bindPattern = binding'
                              S.LetBinding.value = expr' })
                        (fun err1 err2 -> err1 @ err2)
                        qualBinding
                        qualExpr)

            let qualExpr = qualifyCstNode (qualifyExpression namesMap) expr

            Result.map2
                (fun expr' bindings' ->
                    S.LetExpression (bindings', expr')
                    |> S.SingleValueExpression)
                (@)
                qualExpr
                qualBindings

        | S.ControlFlowExpression controlFlowExpr ->
            match controlFlowExpr with
            | S.IfExpression (cond, ifTrue, ifFalse) ->
                let qualifyExpr = qualifyCstNode (qualifyExpression resolvedNames)


                let qualCond, qualIfTrue, qualIfFalse =
                    qualifyExpr cond, qualifyExpr ifTrue, qualifyExpr ifFalse

                Result.map3
                    (fun cond' ifTrue' ifFalse' ->
                        S.IfExpression (cond', ifTrue', ifFalse')
                        |> S.ControlFlowExpression
                        |> S.SingleValueExpression)
                    (@)
                    qualCond
                    qualIfTrue
                    qualIfFalse





let qualifyModuleNames (ylModule : C.YlModule) : Result<YlModule, Identifier list> =
    let moduleResolvedNames = resolveModuleBindings ylModule

    let modulePath = reifyModuleName ylModule.moduleDecl.moduleName.node

    let declarations : Result<S.CstNode<Declaration> list, Identifier list> =
        ylModule.declarations
        |> List.map (
            S.mapNode (function
                | S.TypeDeclaration (name = name; declaration = decl) ->
                    let typeDeclResult = qualifyTypeDeclaration moduleResolvedNames decl

                    match typeDeclResult with
                    | Ok typeDecl -> S.TypeDeclaration (name, typeDecl) |> Ok
                    | Error err -> Error err
                | S.ImportDeclaration import -> failwithf "@TODO: Importing other modules is not implemented yet!"
                | S.ValueTypeAnnotation { valueName = valueName
                                          annotatedType = annotatedType } ->
                    let qualifiedAnnotatedType =
                        S.mapNode (qualifyMentionableType InValueTypeAnnotation moduleResolvedNames) annotatedType
                        |> liftResultFromCstNode

                    match qualifiedAnnotatedType with
                    | Ok qualified ->
                        S.ValueTypeAnnotation
                            { valueName = valueName
                              annotatedType = qualified }
                        |> Ok
                    | Error err -> Error err

                | S.ValueDeclaration { valueName = valueName; value = value } ->
                    let result =
                        S.mapNode (qualifyExpression moduleResolvedNames) value
                        |> liftResultFromCstNode

                    match result with
                    | Ok res ->
                        S.ValueDeclaration { valueName = valueName; value = res }
                        |> Ok
                    | Error err -> Error err

            )
            >> liftResultFromCstNode
        )
        |> Result.sequence
        |> Result.mapError (NEL.toList >> List.concat)


    match declarations with
    | Ok decls ->
        { S.moduleDecl = ylModule.moduleDecl
          S.declarations = decls }
        |> Ok
    | Error err -> Error err



//let qualifyValueNames (moduleResolvedNames : ResolvedNames.ResolvedNames) (valueName : UnqualValueIdentifier) : FullyQualifiedTopLevelLowerIdent  =
//    match ResolvedNames.tryFindValue valueName moduleResolvedNames with
//    | Some (_,valOrParam) ->
//        match valOrParam with
//        | Value (pattern, expr) ->
//    | None -> None




//let qualifyDestructuredPattern (moduleCtx : ) (unqual : C.DestructuredPattern) : DestructuredPattern =
//    match unqual with
//    | S.DestructuredRecord content -> S.DestructuredRecord content
//    | S.DestructuredTuple content -> S.DestructuredTuple content
//    | S.DestructuredCons content -> S.DestructuredCons content
//    | S.DestructuredTypeVariant (a,b) -> S.DestructuredTypeVariant (a,b)


//let qualifyAssignmentPattern (moduleCtx : ) (unqual : C.AssignmentPattern) : AssignmentPattern =
//    match unqual with


//let qualifyMentionableType (moduleCtx : ) (unqual : C.MentionableType) : MentionableType =
//    match unqual with


//let qualifyTupleType (moduleCtx : ) (unqual : C.TupleType) : TupleType =
//    match unqual with


//let qualifyRecordType (moduleCtx : ) (unqual : C.RecordType) : RecordType =
//    match unqual with


//let qualifyExtendedRecordType (moduleCtx : ) (unqual : C.ExtendedRecordType) : ExtendedRecordType =
//    match unqual with


//let qualifyVariantCase (moduleCtx : ) (unqual : C.VariantCase) : VariantCase =
//    match unqual with


//let qualifyNewTypeDeclaration (moduleCtx : ) (unqual : C.NewTypeDeclaration) : NewTypeDeclaration =
//    match unqual with


//let qualifyAliasDeclaration (moduleCtx : ) (unqual : C.AliasDeclaration) : AliasDeclaration =
//    match unqual with


//let qualifyTypeDeclaration (moduleCtx : ) (unqual : C.TypeDeclaration) : TypeDeclaration =
//    match unqual with


//let qualifyCompoundValues (moduleCtx : ) (unqual : C.CompoundValues) : CompoundValues =
//    match unqual with


//let qualifyCustomTypeValues (moduleCtx : ) (unqual : C.CustomTypeValues) : CustomTypeValues =
//    match unqual with


//let qualifyFunctionValue (moduleCtx : ) (unqual : C.FunctionValue) : FunctionValue =
//    match unqual with


//let qualifyExplicitValue (moduleCtx : ) (unqual : C.ExplicitValue) : ExplicitValue =
//    match unqual with


//let qualifyLetBinding (moduleCtx : ) (unqual : C.LetBinding) : LetBinding =
//    match unqual with


//let qualifyControlFlowExpression (moduleCtx : ) (unqual : C.ControlFlowExpression) : ControlFlowExpression =
//    match unqual with


//let qualifySingleValueExpression (moduleCtx : ) (unqual : C.SingleValueExpression) : SingleValueExpression =
//    match unqual with


//let qualifyCompoundExpression (moduleCtx : ) (unqual : C.CompoundExpression) : CompoundExpression =
//    match unqual with


//let qualifyExpression (moduleCtx : ) (unqual : C.Expression) : Expression =
//    match unqual with


//let qualifyValueDeclaration (moduleCtx : ) (unqual : C.ValueDeclaration) : ValueDeclaration =
//    match unqual with


//let qualifyValueAnnotation (moduleCtx : ) (unqual : C.ValueAnnotation) : ValueAnnotation =
//    match unqual with

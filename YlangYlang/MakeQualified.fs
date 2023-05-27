module MakeQualified

open Lexer
module S = SyntaxTree
module C = ConcreteSyntaxTree

open NameResolution
open QualifiedSyntaxTree


type CstWithUnresolveds<'a> =
    { cst : 'a
      unresolveds : Identifier list }



let liftResultFromCstNode (cstNode : S.CstNode<Result<'a, 'b>>) : Result<S.CstNode<'a>, 'b> =
    match cstNode.node with
    | Ok ok -> Ok <| S.makeCstNode ok cstNode.source
    | Error err -> Error err







let rec qualifyMentionableType
    (resolvedNames : NamesInScope)
    (unqual : C.MentionableType)
    : Result<MentionableType, Identifier list> =
    let rec innerFunc mentionableType : Result<MentionableType, Identifier list> =
        match mentionableType with
        | S.UnitType -> Ok S.UnitType
        | S.GenericTypeVar v -> Ok <| S.GenericTypeVar v
        | S.Tuple { types = types } ->
            let mappedTypes =
                types
                |> TOM.traverseResult (S.mapNode innerFunc >> liftResultFromCstNode)

            match mappedTypes with
            | Ok okTypes -> Ok <| S.Tuple { types = okTypes }
            | Error e -> NEL.toList e |> List.concat |> Error
        | S.Record { fields = fields } ->
            let mappedFields =
                fields
                |> Map.map (fun _ -> S.mapNode innerFunc >> liftResultFromCstNode)
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
                |> Map.map (fun _ -> S.mapNode innerFunc >> liftResultFromCstNode)
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
                ResolvedNames.tryFindTypeDeclaration (S.getNode typeName) resolvedNames
                |> Option.map snd

            match resolvedTypeName with
            | Some name -> S.ReferencedType ()


    innerFunc unqual



let qualifyModuleNames (ylModule : C.YlModule) : YlModule =
    let moduleResolvedNames = resolveModuleBindings ylModule

    let thisModuleName : FullyQualifiedUpperIdent =
        let (QualifiedModuleOrTypeIdentifier modulePath) =
            S.getNode ylModule.moduleDecl.moduleName

        let moduleStrNel =
            modulePath
            |> NEL.map (fun (UnqualTypeOrModuleIdentifier moduleStr) -> moduleStr)

        FullyQualifiedUpperIdent moduleStrNel

    { moduleDecl = ylModule.moduleDecl
      declarations =
        ylModule.declarations
        |> List.map (fun declaration ->
            match S.getNode declaration with
            | S.TypeDeclaration (name = name; declaration = decl) ->
                match decl with
                | S.Alias { typeParams = typeParams
                            referent = referent } ->
                    match referent with
                    | S.UnitType ->
                        S.TypeDeclaration (
                            name,
                            S.Alias
                                { typeParams = typeParams
                                  referent = S.UnitType }
                        )

        )

    }




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

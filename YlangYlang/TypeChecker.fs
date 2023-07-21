module TypeChecker


open Lexer
open NameResolution
open System


module Cst = ConcreteSyntaxTree
module S = SyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open Q.Names
open TypedSyntaxTree

module NameRes = TypedNameResolution


(*

@TODO list:

- [ ] resolve named values
    - [ ] in local scopes
    - [ ] from other modules
- [ ] infer types of primitives
- [ ] infer types of values referencing primitives
- [ ] infer types of

- [ ] parse type annotations
- [ ] infer types of values or function params by looking at the functions they are getting passed into
    - [ ] and similarly the types of values passed to operators

- [ ] support flagging up type clashes
    - [ ] and have some way of linking that back to a specific token, or even buffer range?

- [ ] support types with type params, e.g. `List a`
- [ ] support narrowing of types with type params while leaving the type params as generic

- [ ] support a parallel, field-name-and-value-based, type inference system to support typed records as extensible, partially typed things, instead of the all or nothing type system of generics vs explicit types specified above

*)




let makeConstraintsFromDefinitive (def : DefinitiveType) : TypeConstraints = TypeConstraints (Some def, Set.empty)

let makeConstraintsFromConstraint (constr : ConstrainType) : TypeConstraints =
    TypeConstraints (None, Set.singleton constr)

let emptyConstraint : TypeConstraints = TypeConstraints (None, Set.empty)










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



let unqualValToRecField (UnqualValueIdentifier str) = RecordFieldName str
let unqualValToLowerIdent (UnqualValueIdentifier str) = LowerIdent str

let unqualValToLowerName (UnqualValueIdentifier str) = LowerIdent str |> LocalLower

let recFieldToLowerIdent (RecordFieldName str) = LowerIdent str
let lowerIdentToUnqualVal (LowerIdent str) = UnqualValueIdentifier str

//let unqualTypeToUpperIdent (label : S.CstNode<UnqualTypeOrModuleIdentifier>) : S.CstNode<UpperIdent> =
let unqualTypeToUpperIdent (UnqualTypeOrModuleIdentifier label) = UpperIdent label
//let getLabel (UnqualTypeOrModuleIdentifier str) = str
//S.mapNode (getLabel >> UpperIdent) label


let convertRecordMapFields map =
    Map.mapKeyVal (fun key v -> S.mapNode unqualValToRecField key, v) map


let lowerIdentToRecFieldName (LowerIdent ident) = RecordFieldName ident

let private convertTypeOrModuleIdentifierToIdentifier : TypeOrModuleIdentifier -> Identifier =
    function
    | QualifiedType ident -> ModuleSegmentsOrQualifiedTypeOrVariant ident
    | UnqualType ident -> TypeNameOrVariantOrTopLevelModule ident


let private convertValueIdentifierToIdentifier : ValueIdentifier -> Identifier =
    function
    | QualifiedValue ident -> QualifiedPathValueIdentifier ident
    | UnqualValue ident -> SingleValueIdentifier ident



let private convertValueIdentifierToLowerName : ValueIdentifier -> LowerNameValue =
    function
    | QualifiedValue (QualifiedValueIdentifier (path, valIdent)) ->
        reifyLower (QualifiedModuleOrTypeIdentifier path) valIdent
        |> FullyQualifiedLower
    | UnqualValue ident -> unqualValToLowerIdent ident |> LocalLower


let private moduleNameToModulePath (QualifiedModuleOrTypeIdentifier moduleIdent) : ModulePath =
    moduleIdent
    |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
    |> ModulePath


let private getModulePath (moduleCtx : Cst.YlModule) : ModulePath =
    moduleNameToModulePath moduleCtx.moduleDecl.moduleName.node




let typeOrModuleIdentToUpperNameVal : Lexer.TypeOrModuleIdentifier -> UpperNameValue =
    function
    | Lexer.QualifiedType (QualifiedModuleOrTypeIdentifier path) ->
        let (moduleSegments, UnqualTypeOrModuleIdentifier ident) = NEL.peelOffLast path

        let modulePath =
            moduleSegments
            |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)

        FullyQualifiedUpperIdent (ModulePath modulePath, UpperIdent ident)
        |> FullyQualifiedUpper

    | Lexer.UnqualType (UnqualTypeOrModuleIdentifier ident) -> UpperIdent ident |> LocalUpper






let concatResultErrListNel (result : Result<'a, 'Err list nel>) : Result<'a, 'Err list> =
    Result.mapError (NEL.toList >> List.concat) result





let makeTypedExpr (judgment : TypeJudgment) (expr : SingleOrCompoundExpr) : TypedExpr =
    { inferredType = judgment; expr = expr }


























/// @TODO: this needs to be fixed now that `Constrained` types no longer just refer to generically typed params, but also to references to concrete values defined elsewhere!
/// Not entirely sure yet how to do this without having to pass in names maps to this function, which I don't want to do, because of the circular definition problem (i.e. in a let bindings list all values can reference all others, even ones defined after itself, so we can't type check each value in isolation but have to "convert" them to type checked values all at once, and the only way we can do that is by allowing a type of an expression to be a reference to "whatever the type of value X is")
let rec unifyTypeConstraints (typeA : TypeConstraints) (typeB : TypeConstraints) : TypeJudgment =
    match typeA, typeB with
    | TypeConstraints (Some defA, cnstrntsA), TypeConstraints (Some defB, cnstrntsB) ->
        unifyDefinitiveTypes defA defB
        |> Result.map (fun unified -> TypeConstraints (Some unified, Set.union cnstrntsA cnstrntsB))

    | TypeConstraints (Some def, cnstrntsA), TypeConstraints (None, cnstrntsB)
    | TypeConstraints (None, cnstrntsA), TypeConstraints (Some def, cnstrntsB) ->
        TypeConstraints (Some def, Set.union cnstrntsA cnstrntsB)
        |> Ok

    | TypeConstraints (None, cnstrntsA), TypeConstraints (None, cnstrntsB) ->
        TypeConstraints (None, Set.union cnstrntsA cnstrntsB)
        |> Ok





/// @TODO: remember to resolve named types to check for unification, e.g. with named alias type and record
and unifyDefinitiveTypes
    (typeA : DefinitiveType)
    (typeB : DefinitiveType)
    : Result<DefinitiveType, DefinitiveType list> =
    match typeA, typeB with
    | DtTuple a, DtTuple b ->
        unifyTypesTom a b
        |> Result.mapError (fun (first, second) -> [ DtTuple first; DtTuple second ])
        |> Result.bind (TOM.sequenceResult >> concatResultErrListNel)
        |> Result.map DtTuple

    | DtList a, DtList b -> unifyTypeConstraints a b |> Result.map DtList

    | DtArrow (fromA, toA), DtArrow (fromB, toB) ->
        let unifiedToTypes =
            unifyTypesNel toA toB
            |> Result.mapError (fun _ ->
                [ DtArrow (fromA, toA)
                  DtArrow (fromB, toB) ])
            |> Result.bind (NEL.sequenceResult >> concatResultErrListNel)

        (unifyTypeConstraints fromA fromB, unifiedToTypes)
        ||> Result.map2
                (fun fromType toTypes_ -> DtArrow (fromType, toTypes_))
                (fun _ _ ->
                    [ DtArrow (fromA, toA)
                      DtArrow (fromB, toB) ])

    | DtNewType (typeRefA, typeParamsA), DtNewType (typeRefB, typeParamsB) ->
        if typeRefA = typeRefB then
            unifyTypesList (List.map snd typeParamsA) (List.map snd typeParamsB)
            |> Result.mapError (fun (first, second) -> [ typeA; typeB ])
            |> Result.bind (Result.sequenceList >> concatResultErrListNel)
            |> Result.map (fun unifiedParams -> DtNewType (typeRefA, List.zip (List.map fst typeParamsA) unifiedParams))

        else
            Error [ typeA; typeB ]

    | DtRecordExact a, DtRecordExact b ->
        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
        |> Result.mapError (fun _ -> [ DtRecordExact a; DtRecordExact b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (Map.values >> List.concat)
        )
        |> Result.map DtRecordExact

    | DtRecordWith a, DtRecordWith b ->
        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
        |> Result.mapError (fun _ -> [ DtRecordWith a; DtRecordWith b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (Map.values >> List.concat)
        )
        |> Result.map DtRecordExact

    | DtUnitType, DtUnitType -> DtUnitType |> Ok
    | DtPrimitiveType a, DtPrimitiveType b ->
        if a = b then
            DtPrimitiveType a |> Ok
        else
            Error [ DtPrimitiveType a
                    DtPrimitiveType b ]

    | _, _ -> Error [ typeA; typeB ]




and addConstraint (newConstraint : ConstrainType) (TypeConstraints (def, cnstrnts)) : TypeConstraints =
    TypeConstraints (def, Set.add newConstraint cnstrnts)


and addDefinitiveType (newDefinitive : DefinitiveType) (TypeConstraints (def, cnstrnts)) : TypeJudgment =
    match def with
    | None ->
        TypeConstraints (Some newDefinitive, cnstrnts)
        |> Ok
    | Some def_ ->
        let unifiedResult = unifyDefinitiveTypes def_ newDefinitive

        unifiedResult
        |> Result.map (fun unified -> TypeConstraints (Some unified, cnstrnts))







/// If lengths are the same, returns a list of that length of the type judgments of trying to merge the type at every index in both lists. If lengths are not the same though, returns an error result of both inferred types lists.
and private listTraverser (onLengthErr : 'Err) (listA : TypeConstraints list) (listB : TypeConstraints list) =
    match listA, listB with
    | [], [] -> Ok []
    | headA :: tailA, headB :: tailB ->
        let unifiedHead = unifyTypeConstraints headA headB

        listTraverser onLengthErr tailA tailB
        |> Result.map (fun unifiedTail -> unifiedHead :: unifiedTail)

    | [], _ :: _
    | _ :: _, [] -> Error onLengthErr



and unifyTypesList
    (listA : TypeConstraints list)
    (listB : TypeConstraints list)
    : Result<TypeJudgment list, TypeConstraints list * TypeConstraints list> =
    listTraverser (listA, listB) listA listB

and unifyTypesNel
    (NEL (headA, tailA) as nelA : TypeConstraints nel)
    (NEL (headB, tailB) as nelB : TypeConstraints nel)
    : Result<TypeJudgment nel, TypeConstraints nel * TypeConstraints nel> =
    listTraverser (nelA, nelB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyTypeConstraints headA headB
        NEL (unifiedHead, unifiedTail))



and unifyTypesTom
    (TOM (headA, neckA, tailA) as listA : TypeConstraints tom)
    (TOM (headB, neckB, tailB) as listB : TypeConstraints tom)
    : Result<TypeJudgment tom, TypeConstraints tom * TypeConstraints tom> =
    listTraverser (listA, listB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyTypeConstraints headA headB
        let unifiedNeck = unifyTypeConstraints neckA neckB
        TOM (unifiedHead, unifiedNeck, unifiedTail))




/// If both judgments are ok it unifies their constraints. Otherwise it adds any concrete types to the errors list, or combines errors.
///
/// @TODO: this should really also include the other `ConstrainType`s that can be resolved and evaluate to definitive types in case some of them are also incompatible with the other constraints
and unifyJudgments (judgmentA : TypeJudgment) (judgmentB : TypeJudgment) =
    match judgmentA, judgmentB with
    | Ok a, Ok b -> unifyTypeConstraints a b

    | Error err, Ok (TypeConstraints (Some t, _))
    | Ok (TypeConstraints (Some t, _)), Error err -> Error (t :: err)

    | Error e, Ok (TypeConstraints (None, _))
    | Ok (TypeConstraints (None, _)), Error e -> Error e

    | Error a, Error b -> Error (a @ b)





let rec mentionableTypeToDefinite (mentionable : Cst.MentionableType) : TypeConstraints =
    match mentionable with
    | S.UnitType -> makeConstraintsFromDefinitive DtUnitType
    | S.GenericTypeVar unqual ->
        unqualValToLowerIdent unqual
        |> ByTypeParam
        |> makeConstraintsFromConstraint

    | S.Tuple { types = types } ->
        types
        |> TOM.map (S.getNode >> mentionableTypeToDefinite)
        |> DtTuple
        |> makeConstraintsFromDefinitive

    | S.Record { fields = fields } ->
        fields
        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
        |> DtRecordExact
        |> makeConstraintsFromDefinitive

    | S.ExtendedRecord { extendedAlias = alias
                         fields = fields } ->

        fields
        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
        |> DtRecordWith
        |> makeConstraintsFromDefinitive

    | S.ReferencedType (typeName, typeParams) ->
        let definiteTypeParams =
            List.map (S.getNode >> mentionableTypeToDefinite) typeParams

        IsOfTypeByName (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
        |> makeConstraintsFromConstraint

    | S.Arrow (fromType, toTypes) ->
        DtArrow (mentionableTypeToDefinite fromType.node, NEL.map (S.getNode >> mentionableTypeToDefinite) toTypes)
        |> makeConstraintsFromDefinitive

    | S.Parensed parensed -> mentionableTypeToDefinite parensed.node





type GatheredInferredNames = Map<LowerIdent, SOD<TypeJudgment>>



let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : TypeJudgment * GatheredInferredNames =
    match pattern with
    | Named ident ->
        let inferredType =
            LocalLower ident
            |> ByValue
            |> makeConstraintsFromConstraint
            |> Ok

        inferredType,
        Map.empty
        |> NameResolution.addNewReference ident inferredType

    | Ignored -> Ok emptyConstraint, Map.empty
    | Unit -> makeConstraintsFromDefinitive DtUnitType |> Ok, Map.empty
    | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured
    | Aliased (pattern_, alias) ->
        let (inferredType, inferredNames) = getInferredTypeFromAssignmentPattern pattern_

        inferredType,
        inferredNames
        |> NameResolution.addNewReference alias inferredType


and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : TypeJudgment * GatheredInferredNames =
    match pattern with
    | DestructuredRecord fieldNames ->
        let inferredType =
            fieldNames
            |> NEL.map (fun recFieldName ->
                recFieldName,
                recFieldToLowerIdent recFieldName
                |> LocalLower
                |> ByValue
                |> makeConstraintsFromConstraint)
            |> NEL.toList
            |> Map.ofList
            |> DtRecordWith
            |> makeConstraintsFromDefinitive
            |> Ok

        inferredType,
        fieldNames
        |> NEL.map (fun ident ->
            let lowerIdent = recFieldToLowerIdent ident

            lowerIdent,
            lowerIdent
            |> LocalLower
            |> ByValue
            |> makeConstraintsFromConstraint
            |> Ok)
        |> NEL.toList
        |> SOD.makeMapFromList

    | DestructuredCons consItems ->
        let gatheredItems =
            consItems
            |> TOM.map getInferredTypeFromAssignmentPattern

        let namesMap =
            gatheredItems
            |> TOM.map snd
            |> TOM.toList
            |> SOD.combineReferenceMaps

        let typeConstraints =
            gatheredItems
            |> TOM.map fst
            |> TOM.fold<_, _> unifyJudgments (Ok emptyConstraint)

        typeConstraints, namesMap

    | DestructuredTuple tupleItems ->
        let gatheredItems =
            tupleItems
            |> TOM.map getInferredTypeFromAssignmentPattern

        let namesMap =
            gatheredItems
            |> TOM.map snd
            |> TOM.toList
            |> SOD.combineReferenceMaps

        let typeConstraints =
            gatheredItems
            |> TOM.map fst
            |> TOM.sequenceResult
            |> Result.map (DtTuple >> makeConstraintsFromDefinitive)
            |> concatResultErrListNel

        typeConstraints, namesMap

    | DestructuredTypeVariant (ctor, params_) ->
        let gatheredItems =
            params_
            |> List.map getInferredTypeFromAssignmentPattern

        let namesMap =
            gatheredItems
            // @TODO: not sure if it's ok to just discard the fst of gatheredItems or not
            |> List.map snd
            |> SOD.combineReferenceMaps

        let typeConstraints =
            ByConstructorType ctor
            |> makeConstraintsFromConstraint
            |> Ok

        typeConstraints, namesMap






let addDefinitiveConstraint (def : DefinitiveType) (expr : TypedExpr) : TypedExpr =
    { expr with
        inferredType =
            expr.inferredType
            |> Result.bind (addDefinitiveType def)
            |> Result.mapError ((@) [ def ]) }

let addTypeConstraints (constr : TypeConstraints) (expr : TypedExpr) : TypedExpr =
    { expr with
        inferredType =
            expr.inferredType
            |> Result.bind (unifyTypeConstraints constr) }

let addConstrainType (constr : ConstrainType) (expr : TypedExpr) : TypedExpr =
    addTypeConstraints (makeConstraintsFromConstraint constr) expr

let addTypeJudgment (judgment : TypeJudgment) (expr : TypedExpr) : TypedExpr =
    { expr with inferredType = unifyJudgments expr.inferredType judgment }








type private FlatOpList<'a> =
    | LastVal of 'a
    | Op of left : 'a * op : T.Operator * right : FlatOpList<'a>


type OpBinaryTree =
    { left : S.CstNode<TypedExpr>
      op : S.CstNode<T.Operator>
      right : S.CstNode<TypedExpr> }


/// Creates a binary tree of operations, correctly constructed according to associativity and precedence
//let createOpBinaryTree (firstExpr : S.CstNode<Q.Expression >) (opExprSeq : (S.CstNode<Q.Operator > * S.CstNode<Q.Expression> ) nel ) : OpBinaryTree =
// associativity: right is like the (::) operator. I.e. we consider everything to the right to be a single expression before appending the left things to it. Otherwise `a :: b :: []` would be parsed as `(a :: b) :: []`, which is wrong.
// associativity: left is the opposite. i.e. `a (op) b (op) c` is equivalent to `(a (op) b) (op) c`






let rec convertAssignmentPattern (pattern : Cst.AssignmentPattern) : AssignmentPattern =
    match pattern with
    | S.Named name -> Named (unqualValToLowerIdent name)
    | S.Ignored -> Ignored
    | S.Unit -> Unit
    | S.DestructuredPattern p ->
        convertDestructuredPattern p
        |> DestructuredPattern
    | S.Aliased (p, alias) -> Aliased (convertAssignmentPattern p.node, unqualValToLowerIdent alias.node)

and convertDestructuredPattern (pattern : Cst.DestructuredPattern) : DestructuredPattern =
    match pattern with
    | S.DestructuredRecord fields ->
        NEL.map (S.getNode >> unqualValToRecField) fields
        |> DestructuredRecord
    | S.DestructuredTuple items ->
        TOM.map (S.getNode >> convertAssignmentPattern) items
        |> DestructuredTuple
    | S.DestructuredCons items ->
        TOM.map (S.getNode >> convertAssignmentPattern) items
        |> DestructuredCons
    | S.DestructuredTypeVariant (ctor, params_) ->
        DestructuredTypeVariant (
            typeOrModuleIdentToUpperNameVal ctor.node,
            List.map (S.getNode >> convertAssignmentPattern) params_
        )




let rec gatherParams (pattern : AssignmentPattern) : FunctionOrCaseMatchParam =
    match pattern with
    | Named ident ->
        let param_ : Param =
            { destructurePath = SimpleName
              inferredType = Ok emptyConstraint }

        { paramPattern = pattern
          namesMap = Map.add ident (SOD.new_ param_) Map.empty
          inferredType = Ok emptyConstraint }

    | Ignored ->
        { paramPattern = pattern
          namesMap = Map.empty
          inferredType = Ok emptyConstraint }

    | Unit ->
        { paramPattern = pattern
          namesMap = Map.empty
          inferredType = makeConstraintsFromDefinitive DtUnitType |> Ok }

    | DestructuredPattern destructured ->
        let (inferredType, _) = getInferredTypeFromDestructuredPattern destructured

        { paramPattern = pattern
          namesMap = gatherDestructuredPattern destructured
          inferredType = inferredType }

    | Aliased (aliased, alias) ->
        let (inferredType, _) = getInferredTypeFromAssignmentPattern aliased

        let param_ : Param =
            { destructurePath = SimpleName
              inferredType = inferredType }

        let gatheredFromAlias = gatherParams aliased

        { paramPattern = pattern
          namesMap =
            gatheredFromAlias.namesMap
            |> NameResolution.addNewReference alias param_
          inferredType = inferredType }




and gatherDestructuredPattern (pattern : DestructuredPattern) : Map<LowerIdent, SOD<Param>> =
    /// Adjusts the destructure path of a param to account for the fact that it is contained inside a nested destructuring
    let adjustDestructurePath (newPath : PathToDestructuredName) (param_ : Param) : Param =
        { param_ with destructurePath = newPath }


    match pattern with
    | DestructuredRecord fields ->
        fields
        |> NEL.map (fun recField ->
            let ident = recFieldToLowerIdent recField

            ident,
            { Param.destructurePath = InverseRecord
              inferredType =
                LocalLower ident
                |> ByValue
                |> makeConstraintsFromConstraint
                |> Ok })
        |> NEL.toList
        |> SOD.makeMapFromList

    | DestructuredTuple patterns ->
        TOM.map gatherParams patterns
        |> TOM.mapi (fun index tupleItem ->
            tupleItem.namesMap
            |> Map.map (fun _ paramsEntries ->
                paramsEntries
                |> SOD.map (fun param -> adjustDestructurePath (InverseTuple (uint index, param.destructurePath)) param)))
        |> TOM.fold<_, _> NameResolution.combineTwoReferenceMaps Map.empty


    | DestructuredCons patterns ->
        patterns
        |> TOM.map gatherParams
        |> TOM.mapi (fun index params_ ->
            params_.namesMap
            |> Map.map (fun _ paramEntries ->
                paramEntries
                |> SOD.map (fun param_ ->
                    adjustDestructurePath (InverseCons (uint index, param_.destructurePath)) param_)))
        |> TOM.fold<_, _> Map.merge Map.empty

    | DestructuredTypeVariant (ctor, params_) ->
        params_
        |> List.map gatherParams
        |> List.mapi (fun index params__ ->
            params__.namesMap
            |> Map.map (fun _ paramEntries ->
                paramEntries
                |> SOD.map (fun param_ ->
                    adjustDestructurePath (InverseTypeVariant (ctor, uint index, param_.destructurePath)) param_)))
        |> List.fold Map.merge Map.empty







let typeOfPrimitiveLiteralValue (primitive : S.PrimitiveLiteralValue) : DefinitiveType =
    match primitive with
    | S.NumberPrimitive num ->
        match num with
        | S.FloatLiteral _ -> DtPrimitiveType Float
        | S.IntLiteral _ -> DtPrimitiveType Int
    | S.CharPrimitive _ -> DtPrimitiveType Char
    | S.StringPrimitive _ -> DtPrimitiveType String
    | S.UnitPrimitive _ -> DtUnitType
    | S.BoolPrimitive _ -> DtPrimitiveType Bool




let rec typeCheckExpression (resolvedNames : NameRes.NamesMaps) (expr : Cst.Expression) : TypedExpr =
    let innerTypeCheck = typeCheckExpression resolvedNames

    match expr with
    | S.SingleValueExpression singleVal ->
        match singleVal with
        | S.ExplicitValue explicit ->
            match explicit with
            | S.Primitive primitive ->
                let type_ =
                    typeOfPrimitiveLiteralValue primitive
                    |> makeConstraintsFromDefinitive
                    |> Ok

                { inferredType = type_
                  expr =
                    Primitive primitive
                    |> ExplicitValue
                    |> SingleValueExpression }


            | S.DotGetter dotGetter ->
                let recFieldName = unqualValToRecField dotGetter

                let type_ =
                    Map.empty
                    |> Map.add recFieldName emptyConstraint
                    |> DtRecordWith
                    |> makeConstraintsFromDefinitive
                    |> Ok

                { inferredType = type_
                  expr =
                    DotGetter recFieldName
                    |> ExplicitValue
                    |> SingleValueExpression }

            | S.Compound compound ->
                match compound with
                | S.List list ->
                    let typedList = List.map (S.getNode >> innerTypeCheck) list

                    let combinedType =
                        typedList
                        |> List.fold
                            (fun state expr ->
                                (state, expr.inferredType)
                                ||> Result.bind2 unifyTypeConstraints (@))
                            (Ok emptyConstraint)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> T.List
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.Tuple tuple ->
                    let typedList = TOM.map (S.getNode >> innerTypeCheck) tuple

                    let combinedType =
                        typedList
                        |> TOM.map (fun expr -> expr.inferredType)
                        |> TOM.sequenceResult
                        |> concatResultErrListNel
                        |> Result.map (DtTuple >> makeConstraintsFromDefinitive)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> CompoundValues.Tuple
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) -> unqualValToRecField key.node, innerTypeCheck value.node)

                    let combinedType =
                        typedList
                        |> List.map (fun (key, expr) ->
                            expr.inferredType
                            |> Result.map (fun inferred -> key, inferred))
                        |> Result.sequenceList
                        |> Result.map Map.ofList
                        |> concatResultErrListNel
                        |> Result.map (DtRecordExact >> makeConstraintsFromDefinitive)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> CompoundValues.Record
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.RecordExtension (extended, additions) ->

                    let typedList =
                        additions
                        |> NEL.map (fun (key, value) -> unqualValToRecField key.node, innerTypeCheck value.node)

                    let typeOfEditedRecord =
                        unqualValToLowerName extended.node
                        |> ByValue
                        |> makeConstraintsFromConstraint

                    let derivedFromFieldsType : TypeJudgment =
                        typedList
                        |> NEL.map (fun (key, expr) ->
                            expr.inferredType
                            |> Result.map (fun inferred -> key, inferred))
                        |> NEL.sequenceResult
                        |> Result.map (NEL.toList >> Map.ofList)
                        |> concatResultErrListNel
                        |> Result.map (DtRecordWith >> makeConstraintsFromDefinitive)

                    let combinedType : TypeJudgment =
                        Result.bind (unifyTypeConstraints typeOfEditedRecord) derivedFromFieldsType

                    { inferredType = combinedType
                      expr =
                        CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

            | S.Function funcVal ->
                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
                let typeOfBody = typeCheckExpression resolvedNames funcVal.body.node

                let funcParams : FunctionOrCaseMatchParam nel =
                    funcVal.params_
                    |> NEL.map (S.getNode >> typeFuncOrCaseMatchParam)

                //let (NEL (firstParamType, restParamTypes)) =
                let funcParamTypes =
                    funcParams
                    |> NEL.traverseResult (fun param_ -> param_.inferredType)
                    |> concatResultErrListNel

                let arrowType : TypeJudgment =
                    (typeOfBody.inferredType, funcParamTypes)
                    ||> Result.map2
                            (fun typeOfBody_ (NEL (firstParamType, restParamTypes)) ->
                                let toTypes =
                                    NEL.new_ typeOfBody_ (List.rev restParamTypes)
                                    |> NEL.reverse<_>

                                DtArrow (firstParamType, toTypes)
                                |> makeConstraintsFromDefinitive)
                            (@)


                let funcVal : FunctionValue =
                    { params_ = funcParams
                      body = typeOfBody }

                { expr =
                    Function funcVal
                    |> ExplicitValue
                    |> SingleValueExpression
                  inferredType = arrowType }


        | S.UpperIdentifier name ->
            let ctorName = typeOrModuleIdentToUpperNameVal name
            let defType = ByConstructorType ctorName

            { expr = UpperIdentifier ctorName |> SingleValueExpression
              inferredType = makeConstraintsFromConstraint defType |> Ok }

        | S.LowerIdentifier name ->
            let lowerNameVal = convertValueIdentifierToLowerName name

            { expr =
                LowerIdentifier lowerNameVal
                |> SingleValueExpression
              inferredType =
                ByValue lowerNameVal
                |> makeConstraintsFromConstraint
                |> Ok }

        | S.LetExpression (declarations, expr) ->
            let typedDeclarations : LetBindings =
                declarations
                |> NEL.map (fun binding -> binding.node.bindPattern.node, binding.node.value.node)
                |> NEL.map (fun (bindPattern, bindValue) ->
                    let param = typeFuncOrCaseMatchParam bindPattern

                    { paramPattern = param.paramPattern
                      namesMap = param.namesMap
                      bindingPatternInferredType = param.inferredType
                      assignedExpression = innerTypeCheck bindValue })

            let bodyExpr = innerTypeCheck expr.node

            { inferredType = bodyExpr.inferredType
              expr =
                LetExpression (typedDeclarations, bodyExpr)
                |> SingleValueExpression }

        | S.ControlFlowExpression controlFlow ->
            match controlFlow with
            | S.IfExpression (cond, ifTrue, ifFalse) ->
                // @TODO: need to add a type constraint that this expression should be of boolean type
                let typedCond = innerTypeCheck cond.node

                let conditionalWithBoolConstraint =
                    addDefinitiveConstraint (DtPrimitiveType Bool) typedCond

                // This is aiming to express the type constraint that both branches of the if expression should have the same type

                let typedIfTrueBranch = innerTypeCheck ifTrue.node
                let typedIfFalseBranch = innerTypeCheck ifFalse.node

                let expressionType : TypeJudgment =
                    match typedIfTrueBranch.inferredType with
                    | Ok typedIfTrue -> Ok typedIfTrue
                    | Error _ -> typedIfFalseBranch.inferredType

                // This should leave whichever one had the original definitive type unchanged, and only add a definitive constraint to the other one
                let unifiedTrue = addTypeJudgment expressionType typedIfTrueBranch
                let unifiedFalse = addTypeJudgment expressionType typedIfFalseBranch


                { inferredType = expressionType
                  expr =
                    IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
                    |> ControlFlowExpression
                    |> SingleValueExpression }


            | S.CaseMatch (exprToMatch, branches) ->
                let typedExprToMatch = innerTypeCheck exprToMatch.node

                let typedBranches =
                    branches
                    |> NEL.map (fun (pattern, branchExpr) ->
                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
                          body = innerTypeCheck branchExpr.node })


                let (matchExprType, branchReturnTypeConstraints) =
                    typedBranches
                    |> NEL.fold<_, _>
                        (fun (patternConstraints, branchConstraints) branch ->
                            unifyJudgments patternConstraints branch.matchPattern.inferredType,
                            unifyJudgments branchConstraints branch.body.inferredType)
                        (typedExprToMatch.inferredType, Ok emptyConstraint)

                { inferredType = branchReturnTypeConstraints
                  expr =
                    CaseMatch (addTypeJudgment matchExprType typedExprToMatch, typedBranches)
                    |> ControlFlowExpression
                    |> SingleValueExpression }

    | S.CompoundExpression compExpr ->
        match compExpr with
        | S.FunctionApplication (funcExpr, params_) ->
            let typedFunc = innerTypeCheck funcExpr.node

            let typedParams = params_ |> NEL.map (S.getNode >> innerTypeCheck)

            let paramRequirementsFromDeFactoParams =
                typedParams
                |> NEL.map (fun e -> e.inferredType)
                |> NEL.sequenceResult
                |> concatResultErrListNel

            let unified =
                paramRequirementsFromDeFactoParams
                |> Result.bind (fun paramRequirements ->
                    let (NEL (firstParam, restParams)) = paramRequirements
                    let restParamsAndReturnType = NEL.fromListAndLast restParams emptyConstraint

                    let funcTypeRequirement = DtArrow (firstParam, restParamsAndReturnType)

                    unifyJudgments
                        typedFunc.inferredType
                        (makeConstraintsFromDefinitive funcTypeRequirement
                         |> Ok))

            { inferredType = unified
              expr =
                FunctionApplication (typedFunc, typedParams)
                |> CompoundExpression }

        | S.DotAccess (dottedExpr, dotSequence) ->
            let rec makeNestedMap (fieldSeq : RecordFieldName list) =
                match fieldSeq with
                | [] -> emptyConstraint
                | head :: rest ->
                    Map.empty
                    |> Map.add head (makeNestedMap rest)
                    |> DtRecordWith
                    |> makeConstraintsFromDefinitive

            let typedExpr = innerTypeCheck dottedExpr.node

            let exprTypeConstraint =
                dotSequence.node
                |> NEL.map unqualValToRecField
                |> NEL.toList
                |> makeNestedMap

            let fullyTypedExpr = addTypeConstraints exprTypeConstraint typedExpr

            { inferredType = fullyTypedExpr.inferredType
              expr =
                DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
                |> CompoundExpression }

//| Q.Operator (left, opSequence) ->









and typeFuncOrCaseMatchParam (param_ : Cst.AssignmentPattern) : FunctionOrCaseMatchParam =
    convertAssignmentPattern param_ |> gatherParams







///// Not _really_ type classes, but the built-in Elm ones
//type TypeClass =
//    /// Includes both Ints and Floats
//    | Number
//    /// Values that can be compared for order or size, e.g. Strings, Ints, Chars
//    | Comparable
//    /// Values that can be appended, e.g. Strings and Lists
//    | Appendable


///// A named generic parameter - as opposed to an implicit generic parameter
//type RigidGeneric = | RigidGeneric of UnqualValueIdentifier


//type GenericParam =
//    /// I.e. an explicit generic type parameter
//    | Rigid of RigidGeneric
//    /// An unspecified type param, which means it's not going to be explicitly linked to another generic param except for due to other type constraints
//    | Flexible of Guid


///// Where did the type constraint come from
//type TypeConstraintReason =
//    /// Parameter or value is destructured upon in a pattern that requires the assigned value to be of a certain type
//    | DestructuredPattern
//    /// Value is passed into a function whose input is of type
//    | IsPassedIntoFunction
//    /// Is used as a function, with a value of a specific type passed to it - note that this doesn't really make sense unless the actual type constraint is
//    | GetsParameterPassedToIt
//    /// The value has an explicit shape, e.g. a type literal, a list literal, tuple literal, record, etc
//    | IsExplicitShape
//    /// The value is either assigned to a named value with a type declaration, or is returned from a function which has a type declaration
//    | ValueIsPassedOrAssignedToValueWithDeclaredType
//    /// Value is used as an operand for the provided operator
//    | IsUsedWithOperator of Operator
//    /// Not really sure if this is the right way to put it, but e.g. even if one item in a list is unconstrained, if a different member of the same list has a type, then all other list members will need to have the same type, ergo the constraint. Similarly if a Set or Dict or custom type with multiple members all have the same type, the type of one constrains them all
//    | IsInHomogenousType


//type SingleTypeConstraint = InferredType<TypeConstraints>

///// Describes a single type constraint due to how a value is used
//and TypeConstraints =
//    /// No constraints whatsoever, this is a param that isn't used at all
//    | Unconstrained
//    | SingleConstraint of SingleTypeConstraint
//    /// @TODO: might be good to make this more specific that it can relate to:
//    /// - multiple generics, which therefore means that generic params `a` and `b` have to match, and any occurrence of `b` is effectively an occurrence of `a`
//    /// - that generic `a` is actually a concrete type `A`, so any `a` is actually concrete type `A`
//    /// - that it has multiple constraints of being generics, "type classes", and/or a concrete type
//    /// Anything else would mean multiple concrete constraints, which are impossible
//    | MultipleConstraints of SingleTypeConstraint tom


//and BuiltInPrimitiveTypes =
//    | Float
//    | Int
//    | String
//    | Char
//    | Bool


///// Represents an inferred type, whether full or partial.
///// It's a generic cos it can be used for multiple different stages of the type checking/inference process
//and InferredType<'TypeInfo> =
//    | Unit
//    | Primitive of BuiltInPrimitiveTypes
//    /// I wonder if it makes sense to have generics as their own inferred type variant, instead of just having generically constrained params just be referenced via a constraint on one or both of the linked things... I think this makes sense here so I'll keep it here for now and we'll see how we go
//    | Generic of GenericParam

//    | Tuple of 'TypeInfo tom
//    | List of 'TypeInfo
//    /// This describes a record with potentially more unknown fields, e.g. when a record is destructured, or extended, or some of its records accessed, whether directly by dot suffix, or with a dot getter function
//    /// @TODO: this might not catch a possible clash, which is having the same name declared multiple times with a different type for each
//    | RecordWith of
//        //extendedRecord : UnqualValueIdentifier option *
//        /// The actual fields accessed or tried to destructure
//        referencedFields : Map<UnqualValueIdentifier, 'TypeInfo>

//    /// This denotes an exact record, e.g. as an explicit type declaration
//    | RecordExact of Map<UnqualValueIdentifier, 'TypeInfo>
//    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : 'TypeInfo list
//    | Arrow of fromType : 'TypeInfo * toType : 'TypeInfo nel





///// Represents a correct type without clashes
//and DefinitiveType =
//    | DtUnitType
//    | DtPrimitiveType of BuiltInPrimitiveTypes
//    /// I.e. could denote a constraint or invariant between multiple parameters.
//    /// Could be bound or unbound.
//    //| DtGeneric of GenericParam
//    | DtTuple of DefinitiveType tom
//    | DtList of DefinitiveType
//    | DtRecordWith of referencedFields : Map<UnqualValueIdentifier, DefinitiveType>
//    | DtRecordExact of Map<UnqualValueIdentifier, DefinitiveType>
//    /// The typeParams of the referenced type should start off as unconstraineds, but then fill out with more definitive types, as the constraints build up
//    | DtReferencedType of typeName : TypeOrModuleIdentifier * typeParams : DefinitiveType list
//    | DtArrow of fromType : DefinitiveType * toType : DefinitiveType






//module TypeCheckingInfo =



//    /// This should be able to be determined based on the ResolvedNames maps and a type expression
//    //type TypedValues = Map<ValueIdentifier, TypeConstraints>
//    type TypedValues = Map<ValueIdentifier, DefinitiveType>

//    /// Don't worry about capturing the location of the type clashes for now
//    type TypeClashes = (DefinitiveType tom) list

//    type ConstrainedOrNot =
//        | NotYetConstrained
//        | Constrained of DefinitiveType

//    type TypeJudgment =
//        | Unified of ConstrainedOrNot
//        | Clashing of DefinitiveType tom
//        | UnresolvedName of Identifier



//    type ConstrainedVars = Map<ValueIdentifier, ConstrainedOrNot>
//    type ConstrainedGenerics = Map<RigidGeneric, TypeJudgment>



//    let combineDefinitiveType
//        (dType1 : DefinitiveType)
//        (dType2 : DefinitiveType)
//        : Result<DefinitiveType, DefinitiveType tom> =
//        match dType1, dType2 with
//        | DtRecordWith fields1, DtRecordWith fields2 ->
//            let combined =
//                Map.fold
//                    (fun combinedMapResult key value ->
//                        match combinedMapResult with
//                        | Ok combinedMap ->

//                            match Map.tryFind key combinedMap with
//                            | None -> Ok (Map.add key value combinedMap)
//                            | Some fieldValueType ->
//                                if fieldValueType = value then
//                                    Ok (Map.add key value combinedMap)
//                                else
//                                    Error (TOM.make dType1 dType2)
//                        | Error e -> Error e)
//                    (Ok fields2)
//                    fields1

//            Result.map DtRecordWith combined
//        | DtRecordWith extendedFields, DtRecordExact exactFields
//        | DtRecordExact exactFields, DtRecordWith extendedFields ->
//            let combined =
//                extendedFields
//                |> Map.fold
//                    (fun exactFieldsResult extendedKey extendedFieldValType ->
//                        match exactFieldsResult with
//                        | Ok exactResult' ->

//                            match Map.tryFind extendedKey exactResult' with
//                            | None -> Error (TOM.make dType1 dType2)
//                            | Some fieldValueType ->
//                                if fieldValueType = extendedFieldValType then
//                                    Ok (Map.add extendedKey extendedFieldValType exactResult')
//                                else
//                                    Error (TOM.make dType1 dType2)
//                        | Error e -> Error e)
//                    (Ok exactFields)

//            Result.map DtRecordExact combined

//    //| DtGeneric generic1, DtGeneric generic2 ->



//    let combineJudgments (judgment1 : TypeJudgment) (judgment2 : TypeJudgment) =
//        match judgment1, judgment2 with
//        | UnresolvedName name, _
//        | _, UnresolvedName name -> UnresolvedName name

//        | Clashing list1, Clashing list2 -> Clashing (TOM.append list1 list2)

//        | Unified NotYetConstrained, x
//        | x, Unified NotYetConstrained -> x

//        | Unified (Constrained type1), Unified (Constrained type2) -> ()



//    let mergeTypeJudgmentMaps (map1 : ConstrainedGenerics) (map2 : ConstrainedGenerics) =
//        map2
//        |> Map.fold
//            (fun combinedMap key newJudgment ->
//                match Map.tryFind key combinedMap with
//                | None -> combinedMap
//                | Some oldJudgment ->
//                    match oldJudgment with
//                    | Unified constrainedOrNot ->
//                        match constrainedOrNot with
//                        | NotYetConstrained -> newJudgment
//                //    | Constrained type_ ->
//                //| Clashing list ->
//                //| UnresolvedName name ->

//                //Map.add key( Clashing (TOM.make   ) )

//                )
//            map1

//    type private TypeCheckingInfo'<'a> =
//        { expressionType : 'a //TypeJudgment
//          constrainedGenerics : ConstrainedGenerics
//          /// Because the names inside the scope don't need to be propagated out of the scope where they live
//          constrainedVarsOutsideScope : ConstrainedVars
//          unresolvedNames : Set<Identifier>
//          typeClashes : TypeClashes }



//    let succeed x =
//        { expressionType = x
//          constrainedGenerics = Map.empty
//          constrainedVarsOutsideScope = Map.empty
//          unresolvedNames = Set.empty
//          typeClashes = List.empty }

//    let bind : ('a -> TypeCheckingInfo'<'b>) -> TypeCheckingInfo'<'a> -> TypeCheckingInfo'<'b> =
//        fun f info ->
//            let result = f info.expressionType

//            { expressionType = result.expressionType
//              constrainedGenerics = Map.merge
//              constrainedVarsOutsideScope =
//                Map.merge info.constrainedVarsOutsideScope result.constrainedVarsOutsideScope
//              unresolvedNames = Set.union info.unresolvedNames result.unresolvedNames
//              typeClashes = info.typeClashes @ result.typeClashes }

//    let join : TypeCheckingInfo'<TypeCheckingInfo'<'a>> -> TypeCheckingInfo'<'a> =
//        fun info -> bind id info

//    let map : ('a -> 'b) -> TypeCheckingInfo'<'a> -> TypeCheckingInfo'<'b> =
//        fun f info ->
//            { expressionType = f info.expressionType
//              constrainedVarsOutsideScope = info.constrainedVarsOutsideScope
//              unresolvedNames = info.unresolvedNames
//              typeClashes = info.typeClashes }

//    let addUnresolved name info =
//        { info with unresolvedNames = Set.add name info.unresolvedNames }

//    type TypeCheckingInfo = TypeCheckingInfo'<TypeJudgment>


//open TypeCheckingInfo

//module Tci = TypeCheckingInfo



//type VariablesConstraints = Map<Identifier, TypeConstraints>


///// Represents inferred type information for the expression, and also any constraints inferred on variables used in the expression.
///// @TODO: This may also need a field for bubbling up which inner variables could not be unified, so as to notify the developer of a type error
//type GleanedInfo =
//    { typeOfExpression : TypeConstraints
//      /// These are the constraints that were deduced from variables used in the expression
//      variablesConstrained : VariablesConstraints

//      /// @TODO: tbh we could probably stick all of the unresolved names in the same list, just in DUs for each type of thing
//      //valueNamesNotResolved : UnqualValueIdentifier list
//      //typeNamesNotResolved : UnqualTypeOrModuleIdentifier list

//      namesNotResolved : Set<Identifier> }

//let emptyGleanedInfo : GleanedInfo =
//    { typeOfExpression = Unconstrained
//      variablesConstrained = Map.empty
//      namesNotResolved = Set.empty }

//let makeGleanedInfo (type_ : TypeConstraints) variables : GleanedInfo =
//    { emptyGleanedInfo with
//        typeOfExpression = type_
//        variablesConstrained = variables }


//let getTypeInfo (gleaned : GleanedInfo) : TypeConstraints = gleaned.typeOfExpression
//let getConstrainedVars (gleaned : GleanedInfo) : VariablesConstraints = gleaned.variablesConstrained





//// Not sure if this is useful yet
////type BuiltInCompoundTypes =
////    | List of MentionableType // or of it makes sense to have these subtypes on the compound type variants yet
////    | Record of (UnqualValueIdentifier * MentionableType) nel
////    | Tuple of TupleType




////let typeOfPrimitiveLiteralValue : Cst.PrimitiveLiteralValue -> DefinitiveType =
////    function
////    | Cst.NumberPrimitive num ->
////        match num with
////        | Cst.FloatLiteral _ -> DtPrimitiveType Float
////        | Cst.IntLiteral _ -> DtPrimitiveType Int
////    | Cst.CharPrimitive _ -> DtPrimitiveType Char
////    | Cst.StringPrimitive _ -> DtPrimitiveType String
////    | Cst.UnitPrimitive _ -> DtUnitType
////    | Cst.BoolPrimitive _ -> DtPrimitiveType Bool




//type UnificationResult =
//    | Unified of DefinitiveType
//    /// I.e. unification requires all these generics to be assignable to each other - I suppose another way of saying that it's a way of denoting equality between generics?
//    | UnificationDependsOnGenerics of DefinitiveType * generics : RigidGeneric nel
//    | IncompatibleConstraints of DefinitiveType tom





//let rec unifier (constraintA : SingleTypeConstraint) (constraintB : SingleTypeConstraint) : UnificationResult =
//    match constraintA, constraintB with
//    | Unit, Unit -> Ok Unit
//    | Generic genA, Generic genB ->
//        match genA, genB with
//        | Rigid r, Flexible _
//        | Flexible _, Rigid r -> Rigid r |> DtGeneric |> Unified
//        | Rigid rA, Rigid rB ->
//            // @TODO: hmmm, need a way to capture here that it *could* be unified, but we just don't know yet until we know what the generic params are
//            //Rigid rA |> Generic |> Ok
//            UnificationDependsOnGenerics (NEL.new_ rA [ rB ])
//        | Flexible a, Flexible _ -> Flexible a |> DtGeneric |> Unified
//    | Primitive pA, Primitive pB ->
//        if pA = pB then
//            DtPrimitiveType pA |> Unified
//        else
//            IncompatibleConstraints (TOM.make (DtPrimitiveType pA) (DtPrimitiveType pB))
//    | Tuple listA, Tuple listB ->
//        //let rec traverseTupleItems a b : UnificationResult =
//        //    match a, b with
//        //    | [], [] -> Flexible (Guid.NewGuid ()) |> DtGeneric |> Unified
//        //    | headA :: restA, headB :: restB ->
//        //        match unifier headA headB with
//        //        | Unified unified ->
//        //            match traverseTupleItems restA restB with
//        //            | Unified unifiedRest ->



//        //                Unified (DtTuple (TOM.make unified (traverseTupleItems restA restB)))
//        //        | UnificationDependsOnGenerics generics -> Error (constraintA, constraintB)
//        //    | [], _ :: _
//        //    | _ :: _, [] -> Error (constraintA, constraintB)

//        match traverseTupleItems (TOM.toList listA) (TOM.toList listB) with
//        | Ok _ -> Tuple listA |> Ok
//        | Error err -> Error err






////| Unit, Unit -> Ok Unit





//let combineSingleConstraints
//    (constraintA : SingleTypeConstraint)
//    (constraintB : SingleTypeConstraint)
//    : TypeConstraints =
//    if constraintA = constraintB then
//        SingleConstraint constraintA
//    else
//        MultipleConstraints (TOM.make constraintA constraintB)



//let combineManySingleConstraints (constraints : SingleTypeConstraint tom) : TypeConstraints =
//    TOM.fold<_, _>
//        (fun typeConstraints singleConstraint ->
//            match typeConstraints with
//            | Unconstrained -> SingleConstraint singleConstraint
//            | SingleConstraint constr -> combineSingleConstraints singleConstraint constr
//            | MultipleConstraints list ->
//                singleConstraint :: TOM.toList list
//                |> Set.ofList
//                |> Set.toList
//                |> function
//                    | [] -> Unconstrained
//                    | [ onlyOne ] -> SingleConstraint onlyOne
//                    | head :: neck :: rest -> MultipleConstraints (TOM.new_ head neck rest))
//        Unconstrained
//        constraints



//let combineTypeConstraints (constraintA : TypeConstraints) (constraintB : TypeConstraints) : TypeConstraints =
//    match constraintA, constraintB with
//    | Unconstrained, constraint_
//    | constraint_, Unconstrained -> constraint_

//    | SingleConstraint a, SingleConstraint b -> combineSingleConstraints a b

//    | SingleConstraint a, MultipleConstraints b
//    | MultipleConstraints b, SingleConstraint a -> combineManySingleConstraints (TOM.cons a b)

//    | MultipleConstraints a, MultipleConstraints b -> combineManySingleConstraints (TOM.append a b)


//let combineConstrainedVars (mapA : VariablesConstraints) (mapB : VariablesConstraints) : VariablesConstraints =
//    Map.map
//        (fun key value ->
//            match Map.tryFind key mapB with
//            | None -> value
//            | Some valueInB -> combineTypeConstraints value valueInB)
//        mapA

//let combineGleanedInfos (cavA : GleanedInfo) (cavB : GleanedInfo) : GleanedInfo =
//    { typeOfExpression = combineTypeConstraints cavA.typeOfExpression cavB.typeOfExpression
//      variablesConstrained = combineConstrainedVars cavA.variablesConstrained cavB.variablesConstrained
//      namesNotResolved = Set.union cavA.namesNotResolved cavB.namesNotResolved }









///// Get the generic names of the parameters for a type declaration
//let private getTypeParams typeDecl =
//    match typeDecl with
//    | Cst.Alias { specifiedTypeParams = params' } -> List.map (Cst.getNode >> RigidGeneric) params'
//    | Cst.Sum { specifiedTypeParams = params' } -> List.map (Cst.getNode >> RigidGeneric) params'




////let rec private getInferredTypeFromMentionableType (mentionableType : Cst.MentionableType) : SingleTypeConstraint =
//let rec private getInferredTypeFromMentionableType (mentionableType : Cst.MentionableType) : DefinitiveType =
//    match mentionableType with
//    | Cst.GenericTypeVar name -> DtGeneric (Rigid (RigidGeneric name))
//    | Cst.UnitType -> DtUnitType
//    | Cst.Tuple { types = types } ->
//        TOM.map (Cst.getNode >> getInferredTypeFromMentionableType) types
//        |> DtTuple
//    | Cst.Record { fields = fields } ->
//        fields
//        |> Map.mapKeyVal (fun fieldName type' -> fieldName.node, getInferredTypeFromMentionableType type'.node)
//        |> DtRecordExact
//    | Cst.ExtendedRecord { fields = fields } ->
//        // @TODO: need to actually figure out the semantics of what it means to have `{ a | otherFields : otherType }`, is a the exact same record as the whole thing? Is it all the fields *except* for `otherFields`? Need to clarify
//        fields
//        |> Map.mapKeyVal (fun fieldName type' -> fieldName.node, getInferredTypeFromMentionableType type'.node)
//        |> DtRecordWith
//    | Cst.ReferencedType (typeName, typeParams) ->
//        DtReferencedType (typeName.node, List.map (Cst.getNode >> getInferredTypeFromMentionableType) typeParams)
//    | Cst.Arrow (fromType, toType) ->

//        let rec foldUpArrowDestType ((NEL (head, rest)) : DefinitiveType nel) : DefinitiveType =
//            match rest with
//            | [] -> head
//            | neck :: tail -> DtArrow (head, foldUpArrowDestType (NEL (neck, tail)))

//        DtArrow (
//            fromType.node
//            |> getInferredTypeFromMentionableType,
//            toType
//            |> NEL.map (Cst.getNode >> getInferredTypeFromMentionableType)
//            |> foldUpArrowDestType
//        )
//    | Cst.Parensed { node = node } -> getInferredTypeFromMentionableType node



////and getTypeConstraints (mentionableType : Cst.MentionableType) : InferredType =
////    Concrete (t, IsExplicitShape) |> SingleConstraint


//#nowarn "40"









//let typeOfPrimitiveLiteralValue : Cst.PrimitiveLiteralValue -> SingleTypeConstraint =
//    function
//    | Cst.NumberPrimitive num ->
//        match num with
//        | Cst.FloatLiteral _ -> Primitive Float
//        | Cst.IntLiteral _ -> Primitive Int
//    | Cst.CharPrimitive _ -> Primitive Char
//    | Cst.StringPrimitive _ -> Primitive String
//    | Cst.UnitPrimitive _ -> Unit
//    | Cst.BoolPrimitive _ -> Primitive Bool



//let rec typeOfExpression : NamesInScope -> Cst.Expression -> TypeCheckingInfo =
//    fun _ _ -> failwithf "Not implemented yet!"


///// @TODO: this should contain the logic to type check resolved named values
//and typeOfNamedValueIdentifier : NamesInScope -> Identifier -> TypeCheckingInfo =
//    fun resolvedNames ident ->
//        match ident with
//        | SingleValueIdentifier name ->
//            match ResolvedNames.tryFindValue name resolvedNames with
//            | Some (_, Value (_, expr)) -> typeOfExpression resolvedNames expr
//            | Some (_, Parameter _) -> Tci.succeed (Tci.Unified NotYetConstrained)
//            //makeGleanedInfo Unconstrained Map.empty
//            | None ->
//                SingleValueIdentifier name
//                |> Tci.UnresolvedName
//                |> Tci.succeed
//                |> Tci.addUnresolved (SingleValueIdentifier name)

//        //{ emptyGleanedInfo with
//        //    typeOfExpression = Unconstrained
//        //    namesNotResolved = Set.singleton (SingleValueIdentifier name) }

//        | TypeNameOrVariantOrTopLevelModule name ->
//            // I.e. it's a type constructor... I think

//            match ResolvedNames.tryFindTypeConstructor (UnqualType name) resolvedNames with
//            | Some (_, variantConstructor) ->
//                let paramsForVariant =
//                    variantConstructor.variantParams
//                    |> List.map getInferredTypeFromMentionableType

//                DtReferencedType (variantConstructor.typeName, paramsForVariant)
//                |> Tci.Constrained
//                |> Tci.Unified
//                |> Tci.succeed

//            //makeGleanedInfo (SingleConstraint inferredType) Map.empty

//            | None ->
//                TypeNameOrVariantOrTopLevelModule name
//                |> Tci.UnresolvedName
//                |> Tci.succeed
//                |> Tci.addUnresolved (TypeNameOrVariantOrTopLevelModule name)

//        //{ emptyGleanedInfo with
//        //    typeOfExpression = Unconstrained
//        //    namesNotResolved = Set.singleton (TypeNameOrVariantOrTopLevelModule name) }


//        | ModuleSegmentsOrQualifiedTypeOrVariant _ -> failwithf "Not implemented yet!"

//        | QualifiedPathValueIdentifier _ -> failwithf "Not implemented yet!"



////and typeOfSingleValueExpression : ResolvedNames -> Cst.SingleValueExpression -> GleanedInfo =
////    fun resolvedNames expr ->
////        match expr with
////        |





////and typeOfExplicitCompoundValue : ResolvedNames -> Cst.CompoundValues -> GleanedInfo =
//and typeOfExplicitCompoundValue : NamesInScope -> Cst.CompoundValues -> TypeCheckingInfo =
//    fun namesInScope compoundValue ->

//        //let rec listFolder items =
//        //    match items with
//        //    | [] -> emptyGleanedInfo
//        //    | head :: tail ->
//        //        let headConstraint = typeOfExpression namesInScope head

//        //        listFolder tail
//        //        |> combineGleanedInfos headConstraint

//        match compoundValue with
//        | Cst.List exprs -> exprs |> List.map Cst.getNode |> listFolder

//        | Cst.CompoundValues.Tuple list ->
//            list
//            |> TOM.map Cst.getNode
//            |> TOM.toList
//            |> listFolder

//        | Cst.CompoundValues.Record keyValList ->
//            let (keyAndValsConstraints, constrainedVars) =
//                keyValList
//                |> List.fold
//                    (fun (keyAndValsConstraints, vars) (key, value) ->
//                        let typeOfValue = typeOfExpression namesInScope value.node
//                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

//                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

//                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
//                    (List.empty, Map.empty)

//            let inferredType = keyAndValsConstraints |> Map.ofList |> RecordExact

//            makeGleanedInfo (SingleConstraint inferredType) constrainedVars

//        | Cst.CompoundValues.RecordExtension (recordToExtend, keyValList) ->
//            let (keyAndValsConstraints, constrainedVars) =
//                keyValList
//                |> NEL.toList
//                |> List.fold
//                    (fun (keyAndValsConstraints, vars) (key, value) ->
//                        let typeOfValue = typeOfExpression namesInScope value.node
//                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

//                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

//                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
//                    (List.empty, Map.empty)

//            let constraints = RecordWith (Map.ofList keyAndValsConstraints)

//            let thisType = SingleConstraint constraints

//            // Need to ensure that we're constraining the record being extended to be the same as the key/val constraints we've got here
//            Map.add (SingleValueIdentifier recordToExtend.node) thisType constrainedVars
//            |> makeGleanedInfo thisType


///// @TODO: hmmmm, this guy kinda needs to be able to bubble up constraints upwards, onto the parameter as a whole, based on the shape of the destructuring that we do to the parameters.
///// I think the way to do this is that each one of these guys needs to bubble up the sub-shapes inside of itself, and thereby informs the caller of this function what this specific assignment pattern is. Whether this function is called by a top level parameter or a destructured part of it doesn't matter, because the consequences of that will just be handled by whatever calls this function.
//let rec typeOfAssignmentPattern resolvedNames (assignmentPattern : Cst.AssignmentPattern) : GleanedInfo =
//    match assignmentPattern with
//    | Cst.Named _ -> makeGleanedInfo Unconstrained Map.empty
//    | Cst.Ignored -> makeGleanedInfo Unconstrained Map.empty
//    | Cst.Unit -> makeGleanedInfo (SingleConstraint Unit) Map.empty
//    | Cst.Aliased (pattern, alias) ->
//        let subType = typeOfAssignmentPattern resolvedNames pattern.node

//        { subType with
//            variablesConstrained =
//                Map.add (SingleValueIdentifier alias.node) subType.typeOfExpression subType.variablesConstrained }
//    | Cst.DestructuredPattern pattern -> typeOfDestructuredPattern resolvedNames pattern


//and typeOfDestructuredPattern (resolvedNames : NamesInScope) (pattern : Cst.DestructuredPattern) : GleanedInfo =
//    match pattern with
//    | Cst.DestructuredRecord fieldNames ->
//        let justTheFieldNames = fieldNames |> NEL.map Cst.getNode

//        let varConstraints : VariablesConstraints =
//            justTheFieldNames
//            |> NEL.map (fun fieldName -> SingleValueIdentifier fieldName, Unconstrained)
//            |> NEL.toList
//            |> Map.ofSeq

//        let extendedRecordType =
//            justTheFieldNames
//            |> NEL.map (fun fieldName -> fieldName, Unconstrained)
//            |> NEL.toList
//            |> Map.ofSeq
//            |> RecordWith

//        makeGleanedInfo (SingleConstraint extendedRecordType) varConstraints

//    | Cst.DestructuredTuple items ->
//        let gleaneds =
//            TOM.map
//                (Cst.getNode
//                 >> typeOfAssignmentPattern resolvedNames)
//                items

//        let combinedVars =
//            gleaneds
//            |> TOM.map getConstrainedVars
//            |> TOM.fold<_, _> combineConstrainedVars Map.empty

//        let inferredType =
//            Tuple (TOM.map getTypeInfo gleaneds)
//            |> SingleConstraint

//        makeGleanedInfo inferredType combinedVars


//    | Cst.DestructuredCons items ->
//        let gleaneds =
//            TOM.map
//                (Cst.getNode
//                 >> typeOfAssignmentPattern resolvedNames)
//                items

//        let combinedVars =
//            gleaneds
//            |> TOM.map getConstrainedVars
//            |> TOM.fold<_, _> combineConstrainedVars Map.empty

//        let constraints =
//            TOM.map getTypeInfo gleaneds
//            |> TOM.fold<_, _> combineTypeConstraints Unconstrained

//        let inferredType = List constraints

//        makeGleanedInfo (SingleConstraint inferredType) combinedVars

//    | Cst.DestructuredTypeVariant (constructor, params_) ->
//        let resolvedConstructor =
//            ResolvedNames.tryFindTypeConstructor constructor.node resolvedNames
//            |> Option.map snd

//        match resolvedConstructor with
//        | Some constructor ->
//            // @TODO: need to ensure here that the number of assignment params from the variant constructor pattern matches that actual number of params in the variant constructor definition!
//            let typesOfParams =
//                params_
//                |> List.map (
//                    Cst.getNode
//                    >> typeOfAssignmentPattern resolvedNames
//                )

//            //let (_, typeOfConstructor) =
//            //    ResolvedNames.findTypeDeclaration constructor.typeName resolvedNames

//            { emptyGleanedInfo with
//                typeOfExpression = typeOfConstructor
//                variablesConstrained = [ constructor.typeName ] }
//        | None ->
//            { emptyGleanedInfo with
//                namesNotResolved =
//                    Set.singleton
//                    <| convertTypeOrModuleIdentifierToIdentifier constructor.node }

////failwithf "Implement this!"



//type AppliedGenericsMap = Map<RigidGeneric, DefinitiveType>

////let applyGenerics (resolvedNames : ResolvedNames)

















//type TypeState =
//    { inferState : TypeConstraints
//      /// The type declaration for the value
//      typeDeclaration : SingleTypeConstraint option }





//type SimpleJudgment<'a> =
//    | SimpleUnconstrained
//    | SimpleUnified of 'a
//    | SimpleConflicting of 'a tom




///// This will probably be used in a nested way for each of the parameters of a type that has type parameters, to achieve gradual typing of its fields
//type TypeJudgment<'a> =
//    /// `unifiedType` will be `None` if the value is unconstrained
//    | Unified of unifiedType : SingleTypeConstraint option
//    /// Conflicts between inferred types
//    | ConflictingInferences of typeDeclaration : SingleTypeConstraint option * inferences : SingleTypeConstraint tom
//    /// Conflict between declared type and the one otherwise unified inferred type
//    | ConflictDeclarationInferences of declaredType : SingleTypeConstraint * unifiedInferredTypes : SingleTypeConstraint
//    /// Conflict both between declared type and also among the inferred types
//    | ConflictDeclarationAndBetweenInferences of
//        declaredType : SingleTypeConstraint *
//        inferredTypes : SingleTypeConstraint tom



///// Dear lord this is a big one - and doesn't even contain the actual unifier logic
///// But, ultimately this is the function that will let us do the type judgment on multiple type constraints!
//let tryUnifyTypes
//    (unifier : SimpleJudgment<SingleTypeConstraint> -> SingleTypeConstraint -> SimpleJudgment<SingleTypeConstraint>)
//    (typeState : TypeState)
//    : TypeJudgment<'a> =
//    match typeState.typeDeclaration with
//    | None ->
//        match typeState.inferState with
//        | Unconstrained -> Unified None
//        | SingleConstraint constr -> Unified (Some constr)
//        | MultipleConstraints constraints ->
//            match TOM.fold<SimpleJudgment<SingleTypeConstraint>, SingleTypeConstraint>
//                      unifier
//                      SimpleUnconstrained
//                      constraints
//                with
//            | SimpleUnconstrained -> Unified None
//            | SimpleUnified unifiedInferredConstraint -> Unified (Some unifiedInferredConstraint)
//            | SimpleConflicting clashes -> ConflictingInferences (None, clashes)

//    | Some declaration ->
//        match typeState.inferState with
//        | Unconstrained -> Unified (Some declaration)
//        | SingleConstraint constr ->
//            match unifier (SimpleUnified constr) declaration with
//            | SimpleUnconstrained -> Unified (Some declaration)
//            | SimpleUnified unified -> Unified (Some unified)
//            | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, constr)

//        | MultipleConstraints constraints ->
//            match TOM.fold<_, _> unifier SimpleUnconstrained constraints with
//            | SimpleUnconstrained -> Unified (Some declaration)
//            | SimpleUnified unifiedInferreds ->
//                match unifier (SimpleUnified unifiedInferreds) declaration with
//                | SimpleUnconstrained -> Unified (Some declaration)
//                | SimpleUnified fullyUnified -> Unified (Some fullyUnified)
//                | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, unifiedInferreds)

//            | SimpleConflicting clashes -> ConflictingInferences (Some declaration, clashes)

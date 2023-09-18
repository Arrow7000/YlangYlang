﻿module TypedSyntaxTree



open QualifiedSyntaxTree.Names

module S = SyntaxTree
module C = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree



type DestructuredPattern =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of RecordFieldName nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of AssignmentPattern tom
    | DestructuredCons of AssignmentPattern tom
    | DestructuredTypeVariant of constructor : UpperNameValue * params' : AssignmentPattern list

/// Named – or ignored – variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of ident : LowerIdent
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of pattern : AssignmentPattern * alias : LowerIdent








/// Represents a generic, undeclared type variable. Used to create type constraints; e.g. between the input type and the output type of `let id x = x`.
type TypeConstraintId = | TypeConstraintId of System.Guid


let makeTypeConstrId () =
    System.Guid.NewGuid () |> TypeConstraintId





type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Bool




/// Represents a correct type without clashes
and DefinitiveType =
    | DtUnitType
    | DtPrimitiveType of BuiltInPrimitiveTypes
    | DtTuple of TypeConstraints tom
    | DtList of TypeConstraints
    /// I think we need to pass in a type param to the extended record, so that not including one is a type error
    | DtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraints>
    | DtRecordExact of Map<RecordFieldName, TypeConstraints>
    /// This guy will only be able to be assigned at the root of a file once we have the types on hand to resolve them and assign
    | DtNewType of typeName : UpperNameValue * typeParams : TypeConstraints list
    | DtArrow of fromType : TypeConstraints * toType : TypeConstraints






/// A constraint based on a reference to a name
///
/// @TODO: maybe we should split out the constraints that can be used in type expressions? That way we never risk including a ByValue constraint in a type expression. But... if we do that then we'd need to have yet another kind of TypeConstraints
and RefConstr =
    /// I.e. must be the same type as this value
    | ByValue of LowerNameValue

    /// This represents a bound variable to outside the scope where it is declared – works both for value and type expressions.
    /// I.e. these can represent invariants between params that a function or type constructor takes.
    | IsBoundVar of TypeConstraintId

    //| HasTypeOfFirstParamOf of TypeConstraintId


    /// I.e. must be the type that this constructor is a variant of; when given constructor params this will look like a `DtArrow`.
    /// Technically if this is present in a TypeConstraints it implies that either the definitive type is a NewType (or still an incomplete Arrow), but that can be merged at the module level once we have names and constructors to resolve.
    | ByConstructorType of ctor : UpperNameValue


    // From here onwards are the constraints that are derived from a type expressions. The ones above are derived from value expressions.

    /// I.e. must be the same type as this type param
    | ByTypeParam of LowerIdent

//| IsOfTypeByName of typeName : UpperNameValue * typeParams : TypeConstraints list


///// A more limited reference constraint, only for value expressions
//and ValRefConstr =
//    | RefByVal of LowerNameValue
//    | BoundRef of TypeConstraintId


/// Contains the definitive constraints that have been inferred so far, plus any other value or type param constraints that have not been evaluated yet.
/// If a `RefConstr` turns out to be incompatible with the existing definitive type, this will be transformed into a `TypeJudgment` with the incompatible definitive types listed in the `Error` case.
and TypeConstraints =
    | Constrained of definitive : DefinitiveType option * otherConstraints : RefConstr set


    /// Makes a new TypeConstraints which is truly empty
    static member empty = Constrained (None, Set.empty)

    /// Makes a new TypeConstraints which is empty of specific, but still has a Guid so as not to lose links required between the thing that is assigned this constraint and anything else it is linked to
    static member makeUnspecific () =
        Constrained (None, Set.singleton (IsBoundVar (makeTypeConstrId ())))

    static member fromDefinitive (def : DefinitiveType) : TypeConstraints = Constrained (Some def, Set.empty)

    static member fromConstraint (constr : RefConstr) : TypeConstraints =
        Constrained (None, Set.singleton constr)

    static member addRefConstraints (constrs : RefConstr set) (Constrained (defOpt, refConstrs)) =
        Constrained (defOpt, Set.union constrs refConstrs)




type Param =
    { //tokens : TokenWithSource list
      destructurePath : PathToDestructuredName }


and TypeError =
    | IncompatibleTypes of DefinitiveType list
    | UnprunedRecursion

    static member fromTypes types = IncompatibleTypes types



/// @TODO: this should really also contain the other `ConstrainType`s, in case some of them also get evaluated to incompatible definitive types
and TypeJudgment = Result<TypeConstraints, TypeError>








/// Basically the same as a T.DefinitiveType but with guids referencing other types in the Acc instead of their own TypeConstraints
type RefDefType =
    | RefDtUnitType
    | RefDtPrimitiveType of BuiltInPrimitiveTypes
    | RefDtTuple of TypeConstraintId tom
    | RefDtList of TypeConstraintId
    | RefDtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraintId>
    | RefDtRecordExact of Map<RecordFieldName, TypeConstraintId>
    | RefDtNewType of typeName : UpperNameValue * typeParams : TypeConstraintId list
    | RefDtArrow of fromType : TypeConstraintId * toType : TypeConstraintId



type AccTypeError = | DefTypeClash of RefDefType * RefDefType


/// Helper type for accumulating type constraints
type Accumulator = Map<RefConstr set, Result<DefinitiveType option, TypeError>>




















(*
    Helpers for the accumulator
*)

type private TypeCheckResult =
    { idOfTypeConstraint : TypeConstraintId
      refDefResultOpt : Result<RefDefType, AccTypeError> option
      refConstraints : RefConstr set }

    static member fromRefDef (constrId : TypeConstraintId) (refDef : RefDefType) =
        TypeCheckResult.fromRefDefOpt constrId (Some refDef)

    static member fromRefDefOpt (constrId : TypeConstraintId) (refDefOpt : RefDefType option) =
        TypeCheckResult.fromRefDefOptAndRefConstrs constrId refDefOpt Set.empty

    static member fromRefDefOptAndRefConstrs
        (constrId : TypeConstraintId)
        (refDefOpt : RefDefType option)
        (refConstrs : RefConstr set)
        =
        TypeCheckResult.fromRefDefResultOptAndRefConstrs constrId (Option.map Ok refDefOpt) refConstrs

    static member fromRefDefResultOptAndRefConstrs
        (constrId : TypeConstraintId)
        (refDefResultOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        =
        { idOfTypeConstraint = constrId
          refDefResultOpt = refDefResultOpt
          refConstraints = refConstrs }


type private AccModificationsToMake =
    { typeConstraintsToRemove : TypeConstraintId set
      accumulatorToSubsume : Accumulator2 }

    static member empty =
        { typeConstraintsToRemove = Set.empty
          accumulatorToSubsume = Accumulator2.empty }

    static member addRefDef key refDef modifs =
        { modifs with
            accumulatorToSubsume =
                { refConstraintsMap =
                    modifs.accumulatorToSubsume.refConstraintsMap
                    |> Map.add key (Some (Ok refDef), Set.empty) } }

    static member fromTcr (tcr : TypeCheckResult) =
        { typeConstraintsToRemove = Set.empty
          accumulatorToSubsume =
            { refConstraintsMap =
                [ tcr.idOfTypeConstraint, (tcr.refDefResultOpt, tcr.refConstraints) ]
                |> Map.ofSeq } }




and private SubTypeCheckResults =
    { accModifications : AccModificationsToMake
      typeCheckResult : TypeCheckResult }


    static member fromTypeCheckResult tcr =
        { accModifications = AccModificationsToMake.fromTcr tcr
          typeCheckResult = tcr }

    static member getAccModifs (stcr : SubTypeCheckResults) = stcr.accModifications

/// Alias for SubTypeCheckResults
and private Stcr = SubTypeCheckResults





/// Attempt at making accumulator working by using two internal maps, one where every single def type gets a guid assigned to it, and every ref constraint gets placed in a set with its others, which points to a guid, which in turn may have a def type assigned to it.
and Accumulator2
// electric boogaloo
 =
    { refConstraintsMap : Map<TypeConstraintId, Result<RefDefType, AccTypeError> option * RefConstr set> }

    static member empty = { refConstraintsMap = Map.empty }



module Accumulator2 =


    let rec convertRefDefToTypeConstraints
        (refDef : RefDefType)
        (acc : Accumulator2)
        : Result<TypeConstraints, AccTypeError> =

        let fromDef = TypeConstraints.fromDefinitive >> Ok

        match refDef with
        | RefDtUnitType -> fromDef DtUnitType
        | RefDtPrimitiveType prim -> DtPrimitiveType prim |> fromDef
        | RefDtList constrId ->
            let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

            match foundTypeResultOpt with
            | Some foundTypeResult ->
                foundTypeResult
                |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                |> Result.map (
                    TypeConstraints.addRefConstraints refConstrs
                    >> DtList
                    >> TypeConstraints.fromDefinitive
                )

            | None -> Constrained (None, refConstrs) |> Ok

        | RefDtTuple constrTom ->
            let resultsTom =
                constrTom
                |> TOM.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                        |> Result.map (TypeConstraints.addRefConstraints refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> TOM.sequenceResult

            match resultsTom with
            | Ok typeConstraints -> DtTuple typeConstraints |> fromDef

            | Error e -> Error (NEL.head e)


        | RefDtNewType (typeName, typeParams) ->
            let resultsTom =
                typeParams
                |> List.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                        |> Result.map (TypeConstraints.addRefConstraints refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Result.sequenceList

            match resultsTom with
            | Ok typeConstraints -> DtNewType (typeName, typeConstraints) |> fromDef

            | Error e -> Error (NEL.head e)


        | RefDtArrow (fromId, toId) ->
            let resultsPair =
                (fromId, toId)
                |> Tuple.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                        |> Result.map (TypeConstraints.addRefConstraints refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Tuple.sequenceResult

            resultsPair
            |> Result.map (DtArrow >> TypeConstraints.fromDefinitive)



        | RefDtRecordExact fields ->
            let resultsMap =
                fields
                |> Map.map (fun _ constrId ->
                    let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                        |> Result.map (TypeConstraints.addRefConstraints refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Map.sequenceResult

            match resultsMap with
            | Ok typeConstraintsMap -> DtRecordExact typeConstraintsMap |> fromDef
            | Error (_, errsNel) -> Error (NEL.head errsNel)


        | RefDtRecordWith fields ->
            let resultsMap =
                fields
                |> Map.map (fun _ constrId ->
                    let foundTypeResultOpt, refConstrs = Map.find constrId acc.refConstraintsMap

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (fun foundType -> convertRefDefToTypeConstraints foundType acc)
                        |> Result.map (TypeConstraints.addRefConstraints refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Map.sequenceResult

            match resultsMap with
            | Ok typeConstraintsMap -> DtRecordWith typeConstraintsMap |> fromDef
            | Error (_, errsNel) -> Error (NEL.head errsNel)





    let private combineAccModifications
        (stcrA : AccModificationsToMake)
        (stcrB : AccModificationsToMake)
        : AccModificationsToMake =
        { typeConstraintsToRemove = Set.union stcrA.typeConstraintsToRemove stcrB.typeConstraintsToRemove
          accumulatorToSubsume =
            { refConstraintsMap =
                Map.merge stcrA.accumulatorToSubsume.refConstraintsMap stcrB.accumulatorToSubsume.refConstraintsMap } }



    let private combineAccModsFromResults a b =
        combineAccModifications a.accModifications b.accModifications

    let private makeModificationsToAcc (modifs : AccModificationsToMake) (acc : Accumulator2) : Accumulator2 =
        { acc with
            refConstraintsMap =
                acc.refConstraintsMap
                |> Map.removeKeys (Set.toList modifs.typeConstraintsToRemove)
                |> Map.merge modifs.accumulatorToSubsume.refConstraintsMap }









    let rec private addRefDefWithRefConstrs
        (refDefOpt : RefDefType option)
        (refConstrs : RefConstr set)
        (acc : Accumulator2)
        : SubTypeCheckResults =
        // Fold through the map, if there's an overlap, combine it with what we've already got, otherwise don't return anything. And then based on whether we've returned something or not, then either we've already chucked the new stuff in, or not.
        acc.refConstraintsMap
        |> Map.fold
            (fun (stcr : SubTypeCheckResults) constrId (refDefResOpt, refConstrs) ->
                let combinedRefConstrs = Set.union stcr.typeCheckResult.refConstraints refConstrs
                let hasOverlap = Set.isNotEmpty combinedRefConstrs

                if hasOverlap then
                    let unifiedRefDefResult : SubTypeCheckResults =
                        unifyRefDefResOpts refDefResOpt stcr.typeCheckResult.refDefResultOpt acc

                    let combinedTcrsAccModifs : AccModificationsToMake =
                        combineAccModsFromResults unifiedRefDefResult stcr

                    let modifsWithThisConstrIdRemoved : AccModificationsToMake =
                        { combinedTcrsAccModifs with
                            typeConstraintsToRemove = Set.add constrId combinedTcrsAccModifs.typeConstraintsToRemove }

                    { typeCheckResult =
                        { unifiedRefDefResult.typeCheckResult with
                            refConstraints =
                                Set.union unifiedRefDefResult.typeCheckResult.refConstraints combinedRefConstrs }
                      accModifications = modifsWithThisConstrIdRemoved }
                else
                    stcr)
            (TypeCheckResult.fromRefDefOptAndRefConstrs (makeTypeConstrId ()) refDefOpt refConstrs
             |> SubTypeCheckResults.fromTypeCheckResult)






    /// This is the function that actually traverses TypeConstraintIds to check if types are actually compatible with one another!
    and private unifyRefDefs (refDefA : RefDefType) (refDefB : RefDefType) (acc : Accumulator2) : SubTypeCheckResults =
        let newKey = makeTypeConstrId ()

        /// Lil helper function that makes a simple SubTypeCheckResults from a simple RefDefType directly – using the type constraint ID made earlier
        let stcrFromRefDef (refDef : RefDefType) =
            TypeCheckResult.fromRefDef newKey refDef
            |> SubTypeCheckResults.fromTypeCheckResult



        /// Returns an error if lists don't have the same length
        let rec zipList combinedSoFar a b : Result<('a * 'b) list, ('a * 'b) list> =
            match a, b with
            | [], [] -> Ok (List.rev combinedSoFar)
            | headA :: tailA, headB :: tailB -> zipList ((headA, headB) :: combinedSoFar) tailA tailB
            | [], _ :: _
            | _ :: _, [] -> Error (List.rev combinedSoFar)




        match refDefA, refDefB with
        | RefDtUnitType, RefDtUnitType -> stcrFromRefDef RefDtUnitType
        | RefDtPrimitiveType primA, RefDtPrimitiveType primB ->
            if primA = primB then
                stcrFromRefDef (RefDtPrimitiveType primA)
            else
                TypeCheckResult.fromRefDefResultOptAndRefConstrs
                    newKey
                    (Some (Error (DefTypeClash (refDefA, refDefB))))
                    Set.empty
                |> SubTypeCheckResults.fromTypeCheckResult

        | RefDtTuple (TOM (headA, neckA, tailA)), RefDtTuple (TOM (headB, neckB, tailB)) ->
            let combinedListResult = zipList List.empty tailA tailB

            match combinedListResult with
            | Ok combinedList ->
                let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedList

                let tomResults =
                    combinedTom
                    |> TOM.map (fun (idA, idB) -> unifyTypeConstraintIds idA idB acc)

                let typeConstraintIdTom =
                    tomResults
                    |> TOM.map (fun stcr -> stcr.typeCheckResult.idOfTypeConstraint)

                let tupleType = RefDtTuple typeConstraintIdTom
                let tcr = TypeCheckResult.fromRefDef newKey tupleType

                let combinedModifs =
                    tomResults
                    |> TOM.fold
                        (fun state stcr -> combineAccModifications stcr.accModifications state)
                        (AccModificationsToMake.fromTcr tcr)


                { typeCheckResult = tcr
                  accModifications = combinedModifs }


        //| Error combinedListSoFar->
        //    combinedListSoFar

        | RefDtList paramA, RefDtList paramB ->
            let unifiedResult = unifyTypeConstraintIds paramA paramB acc

            let listType = RefDtList unifiedResult.typeCheckResult.idOfTypeConstraint
            let tcr = TypeCheckResult.fromRefDef newKey listType

            let combinedModifs =
                AccModificationsToMake.fromTcr tcr
                |> combineAccModifications unifiedResult.accModifications

            { typeCheckResult = tcr
              accModifications = combinedModifs }

        | RefDtRecordExact mapA, RefDtRecordExact mapB ->
            let mergeResults =
                Map.mergeExact (fun k valA valB -> unifyTypeConstraintIds valA valB acc) mapA mapB

            match mergeResults with
            | Ok mergedMap ->
                let mergedAccModifs =
                    Map.map (fun _ -> Stcr.getAccModifs) mergedMap
                    |> Map.fold (fun state _ -> combineAccModifications state) AccModificationsToMake.empty

                let mapType =
                    mergedMap
                    |> Map.map (fun _ v -> v.typeCheckResult.idOfTypeConstraint)
                    |> RefDtRecordExact

                let tcr = TypeCheckResult.fromRefDef newKey mapType

                let combinedModifs =
                    AccModificationsToMake.fromTcr tcr
                    |> combineAccModifications mergedAccModifs

                { typeCheckResult = tcr
                  accModifications = combinedModifs }


        | RefDtRecordWith mapA, RefDtRecordWith mapB ->
            // @TODO: actually the logic here should be different to that of exact maps
            // @TODO: and actually there should also be compatible cases where one is exact and one is "with"


            let mergeResults =
                Map.mergeExact (fun k valA valB -> unifyTypeConstraintIds valA valB acc) mapA mapB

            match mergeResults with
            | Ok mergedMap ->
                let mergedAccModifs =
                    Map.map (fun _ -> Stcr.getAccModifs) mergedMap
                    |> Map.fold (fun state _ -> combineAccModifications state) AccModificationsToMake.empty

                let mapType =
                    mergedMap
                    |> Map.map (fun _ v -> v.typeCheckResult.idOfTypeConstraint)
                    |> RefDtRecordExact

                let tcr = TypeCheckResult.fromRefDef newKey mapType

                let combinedModifs =
                    AccModificationsToMake.fromTcr tcr
                    |> combineAccModifications mergedAccModifs

                { typeCheckResult = tcr
                  accModifications = combinedModifs }



        | RefDtNewType (nameA, typeParamsA), RefDtNewType (nameB, typeParamsB) ->
            if nameA = nameB then
                let zippedLists = zipList List.empty typeParamsA typeParamsB

                match zippedLists with
                | Ok combinedList ->
                    let tomResults =
                        combinedList
                        |> List.map (fun (idA, idB) -> unifyTypeConstraintIds idA idB acc)

                    let typeConstraintIdTom =
                        tomResults
                        |> List.map (fun stcr -> stcr.typeCheckResult.idOfTypeConstraint)

                    let tupleType = RefDtNewType (nameA, typeConstraintIdTom)
                    let tcr = TypeCheckResult.fromRefDef newKey tupleType

                    let combinedModifs =
                        tomResults
                        |> List.fold
                            (fun state stcr -> combineAccModifications stcr.accModifications state)
                            (AccModificationsToMake.fromTcr tcr)


                    { typeCheckResult = tcr
                      accModifications = combinedModifs }
            else
                TypeCheckResult.fromRefDefResultOptAndRefConstrs
                    newKey
                    (Some (Error (DefTypeClash (refDefA, refDefB))))
                    Set.empty
                |> Stcr.fromTypeCheckResult


        | RefDtArrow (fromTypeA, toTypeA), RefDtArrow (fromTypeB, toTypeB) ->
            let unifiedFroms = unifyTypeConstraintIds fromTypeA fromTypeB acc
            let unifiedTos = unifyTypeConstraintIds toTypeA toTypeB acc

            let arrowType =
                RefDtArrow (
                    unifiedFroms.typeCheckResult.idOfTypeConstraint,
                    unifiedTos.typeCheckResult.idOfTypeConstraint
                )

            let tcr = TypeCheckResult.fromRefDef newKey arrowType

            let modifs =
                AccModificationsToMake.fromTcr tcr
                |> combineAccModifications unifiedFroms.accModifications
                |> combineAccModifications unifiedTos.accModifications

            { typeCheckResult = tcr
              accModifications = modifs }

        | _ ->
            // @TODO: Fill in the case where the types are not compatible
            TypeCheckResult.fromRefDefResultOptAndRefConstrs
                newKey
                (Some (Error (DefTypeClash (refDefA, refDefB))))
                Set.empty
            |> Stcr.fromTypeCheckResult



    and private unifyTypeConstraintIds
        (idA : TypeConstraintId)
        (idB : TypeConstraintId)
        (acc : Accumulator2)
        : SubTypeCheckResults =
        let itemA, refConstrsA = Map.find idA acc.refConstraintsMap
        let itemB, refConstrsB = Map.find idB acc.refConstraintsMap
        let combined = unifyRefDefResOpts itemA itemB acc

        { combined with
            typeCheckResult =
                { combined.typeCheckResult with
                    refConstraints =
                        Set.unionMany [ combined.typeCheckResult.refConstraints
                                        refConstrsA
                                        refConstrsB ] } }



    /// Lil helper function that essentially just does the same as above, but handles the non-success cases also
    and private unifyRefDefResOpts
        (refDefResOptA : Result<RefDefType, AccTypeError> option)
        (refDefResOptB : Result<RefDefType, AccTypeError> option)
        (acc : Accumulator2)
        : SubTypeCheckResults =
        let newKey = makeTypeConstrId ()

        match refDefResOptA, refDefResOptB with
        | None, None ->
            TypeCheckResult.fromRefDefOpt newKey None
            |> SubTypeCheckResults.fromTypeCheckResult
        | Some x, None
        | None, Some x ->
            TypeCheckResult.fromRefDefResultOptAndRefConstrs newKey (Some x) Set.empty
            |> SubTypeCheckResults.fromTypeCheckResult

        | Some refDefResA, Some refDefResB ->
            match refDefResA, refDefResB with
            | Ok _, Error e
            | Error e, Ok _
            | Error e, Error _ ->
                TypeCheckResult.fromRefDefResultOptAndRefConstrs newKey (Some (Error e)) Set.empty
                |> SubTypeCheckResults.fromTypeCheckResult

            | Ok refDefA, Ok refDefB -> unifyRefDefs refDefA refDefB acc









    let rec private addDefinitiveType (def : DefinitiveType) (acc : Accumulator2) : SubTypeCheckResults =
        match def with
        | DtUnitType ->
            TypeCheckResult.fromRefDef (makeTypeConstrId ()) RefDtUnitType
            |> SubTypeCheckResults.fromTypeCheckResult

        | DtPrimitiveType prim ->
            TypeCheckResult.fromRefDef (makeTypeConstrId ()) (RefDtPrimitiveType prim)
            |> SubTypeCheckResults.fromTypeCheckResult

        | DtList tc ->
            let resultOfGeneric = addTypeConstraints tc acc
            let listType = RefDtList resultOfGeneric.typeCheckResult.idOfTypeConstraint
            let refDefAddResult = addRefDefWithRefConstrs (Some listType) Set.empty acc

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications = combineAccModsFromResults resultOfGeneric refDefAddResult }

        | DtTuple tom ->
            let resultsTom = TOM.map (fun tc -> addTypeConstraints tc acc) tom

            let tupleType =
                RefDtTuple (
                    resultsTom
                    |> TOM.map (fun result -> result.typeCheckResult.idOfTypeConstraint)
                )

            let refDefAddResult = addRefDefWithRefConstrs (Some tupleType) Set.empty acc

            let combinedModifs =
                resultsTom
                |> TOM.map (fun result -> result.accModifications)
                |> TOM.fold combineAccModifications refDefAddResult.accModifications

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications = combinedModifs }


        | DtArrow (fromType, toType) ->
            let fromResult = addTypeConstraints fromType acc
            let toResult = addTypeConstraints toType acc

            let arrowType =
                RefDtArrow (fromResult.typeCheckResult.idOfTypeConstraint, toResult.typeCheckResult.idOfTypeConstraint)

            let refDefAddResult = addRefDefWithRefConstrs (Some arrowType) Set.empty acc

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications =
                combineAccModsFromResults fromResult toResult
                |> combineAccModifications refDefAddResult.accModifications }

        | DtRecordExact map ->
            let resultsMap = Map.map (fun _ tc -> addTypeConstraints tc acc) map

            let mapType =
                RefDtRecordExact (
                    resultsMap
                    |> Map.map (fun _ result -> result.typeCheckResult.idOfTypeConstraint)
                )

            let refDefAddResult = addRefDefWithRefConstrs (Some mapType) Set.empty acc

            let combinedAccModifs =
                resultsMap
                |> Map.map (fun _ result -> result.accModifications)
                |> Map.fold
                    (fun combined _ accModif -> combineAccModifications accModif combined)
                    AccModificationsToMake.empty

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications = combinedAccModifs }

        | DtRecordWith map ->
            let resultsMap = Map.map (fun _ tc -> addTypeConstraints tc acc) map

            let mapType =
                RefDtRecordWith (
                    resultsMap
                    |> Map.map (fun _ result -> result.typeCheckResult.idOfTypeConstraint)
                )

            let refDefAddResult = addRefDefWithRefConstrs (Some mapType) Set.empty acc

            let combinedAccModifs =
                resultsMap
                |> Map.map (fun _ result -> result.accModifications)
                |> Map.fold
                    (fun combined _ accModif -> combineAccModifications accModif combined)
                    AccModificationsToMake.empty

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications = combinedAccModifs }


        | DtNewType (typeName, constraints) ->
            let resultsList = List.map (fun tc -> addTypeConstraints tc acc) constraints

            let newType =
                RefDtNewType (
                    typeName,
                    resultsList
                    |> List.map (fun result -> result.typeCheckResult.idOfTypeConstraint)
                )

            let refDefAddResult = addRefDefWithRefConstrs (Some newType) Set.empty acc

            let combinedModifs =
                resultsList
                |> List.map (fun result -> result.accModifications)
                |> List.fold combineAccModifications refDefAddResult.accModifications

            { typeCheckResult = refDefAddResult.typeCheckResult
              accModifications = combinedModifs }


    and private addTypeConstraints (Constrained (defOpt, refConstrs)) (acc : Accumulator2) : SubTypeCheckResults =
        let defTypeAddResult =
            match defOpt with
            | Some def -> Some (addDefinitiveType def acc)
            | None -> None

        let refDefTypeOpt, newRefConstrs =
            match defTypeAddResult with
            | None -> None, Set.empty
            | Some defTypeResult ->
                defTypeResult.typeCheckResult.refDefResultOpt
                |> Option.bind Result.toOption,
                defTypeResult.typeCheckResult.refConstraints

        let combinedRefConstrs = Set.union newRefConstrs refConstrs

        addRefDefWithRefConstrs refDefTypeOpt combinedRefConstrs acc






    let addTypeConstraintsToAcc (typeConstraints : TypeConstraints) (acc : Accumulator2) : Accumulator2 =
        let result = addTypeConstraints typeConstraints acc
        makeModificationsToAcc result.accModifications acc



    let addTypeConstraintForName (name : RefConstr) (tc : TypeConstraints) (acc : Accumulator2) =
        let (Constrained (defOpt, refs)) = tc
        let tcWithName = Constrained (defOpt, Set.add name refs)

        addTypeConstraintsToAcc tcWithName acc













module Acc2 = Accumulator2

type RefConstrToTypeConstraintsMap =
    | RefConstrToTypeConstraintsMap of Map<RefConstr, Result<TypeConstraints, AccTypeError> option>



module RefConstrToTypeConstraintsMap =

    /// Makes a new map from an Accumulator2
    let fromAcc2 (acc : Accumulator2) : RefConstrToTypeConstraintsMap =
        Map.values acc.refConstraintsMap
        |> Seq.map (fun (refDefResOpt, refConstrs) ->
            refConstrs,
            refDefResOpt
            |> Option.map (Result.bind (fun refDef -> Acc2.convertRefDefToTypeConstraints refDef acc)))
        |> Seq.collect (fun (refConstrs, refDefResOpt) ->
            Set.toList refConstrs
            |> List.map (fun refConstr -> refConstr, refDefResOpt))
        |> Map.ofSeq
        |> RefConstrToTypeConstraintsMap


    /// Given a reference, get the TypeConstraints that that reference has been inferred to be
    let getTypeConstraintsFromMap
        (refConstr : RefConstr)
        (RefConstrToTypeConstraintsMap map : RefConstrToTypeConstraintsMap)
        : Result<TypeConstraints, AccTypeError> option =
        Map.tryFind refConstr map |> Option.flatten







(* Name dictionaries *)










//type MentionableType =
//    | UnitType
//    | GenericTypeVar of LowerNameValue
//    | Tuple of TupleType
//    | Record of RecordType
//    | ExtendedRecord of ExtendedRecordType
//    | ReferencedType of typeName : UpperNameValue * typeParams : MentionableType list
//    | Arrow of fromType : MentionableType * toType : NEL<MentionableType>
//    | Parensed of MentionableType



///// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
//and TupleType = { types : MentionableType tom }


//and RecordType =
//    { fields : Map<RecordFieldName, MentionableType> }

///// @TODO: as said above at MentionableType, we may need separate versions of this for value type annotations vs for use in type declarations; because in the former free type variables are allowed, but in the latter they are not.
//and ExtendedRecordType =
//    { extendedAlias : LowerIdent // Because it has to be a type param
//      fields : Map<RecordFieldName, MentionableType> }





type VariantCase =
    { label : UpperIdent
      contents : TypeConstraints list }




type TypeDeclarationContent =
    | Sum of variants : NEL<VariantCase>
    | Alias of referent : TypeConstraints








(* Dictionaries of declared names *)

type TypeDeclarations = Map<UpperIdent, SOD<TypeDeclaration>>

and TypeConstructors = Map<UpperNameValue, SOD<VariantConstructor>>

and ValueDeclarations = Map<LowerNameValue, SOD<LowerCaseName>>

and ValueTypeDeclarations = Map<LowerNameValue, SOD<TypeConstraints>>

and TypeParams = Map<LowerIdent, SOD<unit>>

and InfixOps = Map<LowerIdent, SOD<DeclaredInfixOp>>








and DeclaredInfixOp =
    { associativity : S.InfixOpAssociativity
      precedence : int
      /// The value should be a function taking exactly two parameters
      value : TypedExpr }


and VariantConstructor =
    { typeParamsList : LowerIdent list // So as to not lose track of the order of the type params
      typeParamsMap : TypeParams
      variantCase : VariantCase
      allVariants : NEL<VariantCase>
      typeName : UpperIdent }



and LowerCaseName =
    | LocalName of LetBinding
    | Param of Param
    | TopLevelName of TypedExpr // ValueDeclaration -- This really only carried a TypedExpr anyway, so why stick it in a special wrapper record type







and TypeDeclaration =
    { typeParamsMap : TypeParams
      typeParamsList : LowerIdent list
      typeDeclaration : TypeDeclarationContent }







/// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
and LetBinding =
    { paramPattern : AssignmentPattern
      namesMap : Map<LowerIdent, SOD<Param>>
      /// @TODO: hmm not entirely sure what this thing actually describes. Is it the inferred type of the entire binding? Or is it _only_ the inferred shape based on the assignment pattern, which therefore still needs to be unified with the inferred type of the actual assigned expression?
      //bindingPatternInferredType : TypeJudgment

      (*
      @TODO: we need to take into account the assignment pattern here so that we can:
        a) add the type constraints implied by that pattern, and
        b) partially evaluate or slice up the expression so that we're assigning the right sub-expressions to the right names

      Although tbh evaluation of the assigned expression might not be straightforward, so maybe it is best to have something here to represent the fact that:
        a) we've only got one expression we're evaluating per binding (and so not doing the duplicate work of evaluating the expression once for every named value in the assignment pattern), and
        b) for each named value, what path to take in that expression to get the slice of the expression that should be assigned to it, e.g. a tuple, type destructuring, etc.
      *)
      assignedExpression : TypedExpr

    //combinedInferredType : TypeJudgment
     }





and LetBindings = LetBinding nel

/// Represents all the named params in a single function parameter or case match expression
and FunctionOrCaseMatchParam =
    { paramPattern : AssignmentPattern
      namesMap : Map<LowerIdent, SOD<Param>>
    //inferredType : TypeJudgment
     }




and CompoundValues =
    | List of TypedExpr list
    | Tuple of TypedExpr tom
    | Record of (RecordFieldName * TypedExpr) list
    | RecordExtension of recordToExtend : LowerIdent * additions : NEL<RecordFieldName * TypedExpr>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParam nel
      body : TypedExpr }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of S.PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : RecordFieldName




and ControlFlowExpression =
    | IfExpression of condition : TypedExpr * ifTrue : TypedExpr * ifFalse : TypedExpr
    | CaseMatch of exprToMatch : TypedExpr * branches : CaseMatchBranch nel

and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | UpperIdentifier of name : UpperNameValue
    | LowerIdentifier of name : LowerNameValue
    | LetExpression of namedValues : LetBindings * expr : TypedExpr
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : TypedExpr * op : OperatorIdent * right : TypedExpr
    | FunctionApplication of funcExpr : TypedExpr * params' : NEL<TypedExpr>
    | DotAccess of expr : TypedExpr * dotSequence : NEL<RecordFieldName>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParam
      body : TypedExpr }


and SingleOrCompoundExpr =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and TypedExpr = { expr : SingleOrCompoundExpr }



and OperatorIdent =
    | BuiltInOp of Lexer.BuiltInOperator
    | OtherOp of ident : LowerIdent




//and ValueAnnotation =
//    { /// these aren't in the source code, but they're gathered from the type expression implicitly
//      gatheredImplicitParams : TypeParams
//      annotatedType : DefinitiveType }







//and Declaration =
//    | ImportDeclaration of S.ImportDeclaration
//    | TypeDeclaration of name : UpperIdent * declaration : TypeDeclaration
//    | ValueTypeAnnotation of name : LowerIdent * ValueAnnotation
//    | ValueDeclaration of name : LowerIdent * ValueDeclaration


// Representing a whole file/module
and YlModule =
    { moduleDecl : S.ModuleDeclaration
      imports : S.ImportDeclaration list
      types : TypeDeclarations
      valueTypes : ValueTypeDeclarations
      values : Map<LowerIdent, SOD<TypedExpr>>
      infixOperators : Map<LowerIdent, SOD<DeclaredInfixOp>> }

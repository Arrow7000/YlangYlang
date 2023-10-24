module Accumulator
// Should maybe call this TypeUnification or TypeContext or something


open TypedSyntaxTree






/// Basically the same as the AccumulatorAndOwnType
type AccAndTypeId =
    { typeId : AccumulatorTypeId
      acc : Accumulator }


module AccAndTypeId =
    let make accTypeId acc : AccAndTypeId =
        /// @TODO: delete this when testing is complete
        let _ =
            try
                Accumulator.getTypeById accTypeId acc
            with
            | _ -> failwithf "Tried to make an Aati with an ID that's not present in the Acc!"

        { acc = acc; typeId = accTypeId }

    let getId (aati : AccAndTypeId) = aati.typeId
    let getAcc (aati : AccAndTypeId) = aati.acc






module Aati = AccAndTypeId











let private makeAccTypeId () : AccumulatorTypeId =
    System.Guid.NewGuid () |> AccumulatorTypeId




let empty = Accumulator.empty


/// Specifies what needs to be done when a group of RefConstrs are introduced/unified into an Acc
type private UnifyRefConstrsPassResult =
    /// The added refConstrs are not present in the Acc at all, so just create a new entry with only these RefConstrs and call it a day
    | NotCurrentlyInAcc
    /// The added refConstrs overlap with exactly one Acc entry, so all you need to do is replace that ID's existing RefConstrs with this one and call it a day
    | InOneEntry of accId : AccumulatorTypeId * combinedRefConstrs : RefConstr set
    /// The added refConstrs overlap with two or more Acc entries, so the RefDefs need to be unified, and they all need to have their refConstrs set to this unified set
    | InMultipleEntries of accIds : AccumulatorTypeId tom * allUnifiedRefConstrs : RefConstr set








/// Given a set of RefConstrs to add into the Acc, this tells us whether they are either:
///     a) not in the Acc at all – so only one new entry with only these RefConstrs needs to be added
///     b) only present in one entry in the Acc – so we only need to add the combined RefConstrs (the existing ones for that entry + the ones provided here) to the existing entry in the Acc
///     c) present in multiple entries in the Acc – so those RefDefs in those entries need to be unified, and have its RefConstrs set as the union of both all the refConstrs in the unified entries + the ones provided here
let rec private getRefConstrAddOrUnifyInfo
    (refConstrsToAddOrUnify : RefConstr set)
    (acc : Accumulator)
    : UnifyRefConstrsPassResult =
    let toBeMerged =
        acc.refConstraintsMap
        |> Map.choose (fun _ (_, refConstrs) ->
            if Set.hasOverlap refConstrs refConstrsToAddOrUnify then
                let refConstrsUnion = Set.union refConstrs refConstrsToAddOrUnify

                Some refConstrsUnion
            else
                None)
        |> Map.toList

    match toBeMerged with
    | [] -> NotCurrentlyInAcc

    | onlyOne :: [] ->

        let accId, refConstrsUnion = onlyOne
        InOneEntry (accId, refConstrsUnion)

    | head :: neck :: tail ->
        let toBeMergedTom = TOM.new_ head neck tail

        /// This contains all the RefConstrs to put in the new entry
        let fullRefConstrUnion = TOM.map snd toBeMergedTom |> Set.unionMany

        let idsToMerge = TOM.map fst toBeMergedTom

        InMultipleEntries (idsToMerge, fullRefConstrUnion)


/// This returns the Accumulator resulting from unifying the two or more AccIds and RefDefs
///
/// @TODO: I think... unifying RefDefs should never ever need to return the "refConstrs to unify", because since the sets of RefConstrs should be completely disjoint... if we're unifying refdefs all we need to do is store a simple union of the refconstrs and that should never ever have any further ramifications... the only thing is if we're introducing a new refconstr set that combines a bunch of them, that could entail merging more than one thing... but even then, all we need to do then is a snowballing of those RefDefs into a single type result/judgment, but the refconstraints..? they're still only ever going to be a single fucking union. With never any further ramifications after unifying the refdefs... so... i think perhaps this whole symmetric single pass thing has been a bit of a red herring and maybe it's only the refConstr unification that can result in refDefs to unify, but once that's done... the refDef unification can do a simple unification of its own RefConstrs and call it a day... wahoooowww.
let rec private unifyRefDefResOptsTom
    (refDefsWithIds : (AccumulatorTypeId * Result<RefDefType, AccTypeError> option) tom)
    (acc : Accumulator)
    : AccAndTypeId =

    let rec unifyTwoRefDefs
        (a : AccumulatorTypeId * RefDefType)
        (b : AccumulatorTypeId * RefDefType)
        (acc : Accumulator)
        : AccAndTypeId =
        // @TODO: So I think this will be the longer one with the lengthy logic for how to merge two RefDefTypes with all their intricate little details
        let makeOkType : RefDefType -> Result<RefDefType, AccTypeError> option = Ok >> Some

        let makeErrType a' b' : Result<RefDefType, AccTypeError> option = DefTypeClash (a', b') |> Error |> Some


        let accIdA, refDefA = a
        let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

        let accIdB, refDefB = b
        let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd

        let newKey = makeAccTypeId ()
        let accIdsToReplace = Set.ofList [ accIdA; accIdB ]

        /// For this level/pass of unification
        let combinedRefConstrs = Set.union refConstrsA refConstrsB

        /// Returns an error with the lists so far if lists don't have the same length; which will be a list of n pairs, where n is the length of the shorter of the two input lists.
        /// If the lists are not the same length, the Error will contain the combined lists so far. This is useful so that we can do some type checking on those bits that do overlap.
        let zipList listA listB : Result<('a * 'b) list, ('a * 'b) list> =
            let rec zipList_ combinedSoFar a b =
                match a, b with
                | [], [] -> Ok (List.rev combinedSoFar)
                | headA :: tailA, headB :: tailB -> zipList_ ((headA, headB) :: combinedSoFar) tailA tailB
                | [], _ :: _
                | _ :: _, [] -> Error (List.rev combinedSoFar)

            zipList_ List.empty listA listB



        match refDefA, refDefB with
        | RefDtUnitType, RefDtUnitType ->
            let updatedAcc =
                Accumulator.replaceEntries accIdsToReplace newKey (makeOkType RefDtUnitType) combinedRefConstrs acc

            Aati.make newKey updatedAcc


        | RefDtPrimType primA, RefDtPrimType primB ->
            let typeResult =
                if primA = primB then
                    makeOkType (RefDtPrimType primA)
                else
                    makeErrType refDefA refDefB

            let updatedAcc =
                Accumulator.replaceEntries accIdsToReplace newKey typeResult combinedRefConstrs acc

            Aati.make newKey updatedAcc


        | RefDtList paramA, RefDtList paramB ->
            let unifiedInnerResult = unifyTwoAccTypeIds paramA paramB acc

            let listType : RefDefType = RefDtList unifiedInnerResult.typeId

            let updatedAcc =
                Accumulator.replaceEntries
                    accIdsToReplace
                    newKey
                    (makeOkType listType)
                    combinedRefConstrs
                    unifiedInnerResult.acc

            Aati.make newKey updatedAcc


        | RefDtTuple (TOM (headA, neckA, tailA)), RefDtTuple (TOM (headB, neckB, tailB)) ->
            /// This ensures the two lists of AccIds have the same length, it doesn't try to unify them yet
            let combinedListResult = zipList tailA tailB

            match combinedListResult with
            | Ok combinedList ->
                let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedList

                let unifiedAccIdsTom, combinedAcc =
                    combinedTom
                    |> TOM.foldMap
                        (fun state (idA, idB) ->
                            let unifyResult = unifyTwoAccTypeIds idA idB state
                            unifyResult.typeId, unifyResult.acc)
                        acc

                let tupleType = RefDtTuple unifiedAccIdsTom

                Accumulator.replaceEntries accIdsToReplace newKey (makeOkType tupleType) combinedRefConstrs combinedAcc
                |> Aati.make newKey

            | Error combinedListSoFar ->
                let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedListSoFar

                let combinedAcc =
                    combinedTom
                    |> TOM.fold (fun state (idA, idB) -> unifyTwoAccTypeIds idA idB state |> Aati.getAcc) acc

                Accumulator.replaceEntries
                    accIdsToReplace
                    newKey
                    (makeErrType refDefA refDefB)
                    combinedRefConstrs
                    combinedAcc
                |> Aati.make newKey


        | RefDtRecordExact mapA, RefDtRecordExact mapB
        // If one of the records is an exact one then combining it with an extensible one forces the combined expression to be the exact record's type
        | RefDtRecordWith mapA, RefDtRecordExact mapB
        | RefDtRecordExact mapA, RefDtRecordWith mapB ->

            match Map.getOverlap mapA mapB with
            | Map.MapsOverlap.Exact shared ->
                let mergedFields, threadedAcc =
                    shared
                    |> Map.fold
                        (fun (newMap, acc') key (idA, idB) ->
                            let unificationResult = unifyTwoAccTypeIds idA idB acc'
                            Map.add key unificationResult.typeId newMap, unificationResult.acc)
                        (Map.empty, acc)

                let recordType = RefDtRecordExact mergedFields

                Accumulator.replaceEntries accIdsToReplace newKey (makeOkType recordType) combinedRefConstrs threadedAcc
                |> Aati.make newKey


            | _ ->
                Accumulator.replaceEntries accIdsToReplace newKey (makeErrType refDefA refDefB) combinedRefConstrs acc
                |> Aati.make newKey


        | RefDtRecordWith mapA, RefDtRecordWith mapB ->
            let addSingleEntry (mergedMap, acc') fieldName accId = Map.add fieldName accId mergedMap, acc'

            let mergedFields, combinedAcc =
                Map.foldAllEntries
                    addSingleEntry
                    addSingleEntry
                    (fun (mergedMap, acc') fieldName valA valB ->
                        let unifyResult = unifyTwoAccTypeIds valA valB acc'
                        Map.add fieldName unifyResult.typeId mergedMap, unifyResult.acc)
                    mapA
                    mapB
                    (Map.empty, acc)

            let recordType = RefDtRecordWith mergedFields

            Accumulator.replaceEntries accIdsToReplace newKey (makeOkType recordType) combinedRefConstrs combinedAcc
            |> Aati.make newKey


        | RefDtNewType (nameA, typeParamsA), RefDtNewType (nameB, typeParamsB) ->
            if nameA = nameB then
                let zippedLists = zipList typeParamsA typeParamsB

                match zippedLists with
                | Ok combinedList ->
                    let typeConstraintIdList, combinedAcc =
                        combinedList
                        |> List.mapFold
                            (fun state (idA, idB) ->
                                let unifyResult = unifyTwoAccTypeIds idA idB state
                                unifyResult.typeId, unifyResult.acc)
                            acc

                    let newType = RefDtNewType (nameA, typeConstraintIdList)

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeOkType newType)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey

                | Error combinedListSoFar ->
                    let combinedAcc =
                        combinedListSoFar
                        |> List.fold (fun state (idA, idB) -> unifyTwoAccTypeIds idA idB state |> Aati.getAcc) acc

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeErrType refDefA refDefB)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey

            else
                Accumulator.replaceEntries accIdsToReplace newKey (makeErrType refDefA refDefB) combinedRefConstrs acc
                |> Aati.make newKey


        | RefDtArrow (fromTypeA, toTypeA), RefDtArrow (fromTypeB, toTypeB) ->
            let unifiedFroms = unifyTwoAccTypeIds fromTypeA fromTypeB acc
            let unifiedTos = unifyTwoAccTypeIds toTypeA toTypeB unifiedFroms.acc

            let arrowType = RefDtArrow (unifiedFroms.typeId, unifiedTos.typeId)

            Accumulator.replaceEntries accIdsToReplace newKey (makeOkType arrowType) combinedRefConstrs unifiedTos.acc
            |> Aati.make newKey


        | _, _ ->
            // @TODO: Fill in the case where the types are not compatible
            Accumulator.replaceEntries accIdsToReplace newKey (makeErrType refDefA refDefB) combinedRefConstrs acc
            |> Aati.make newKey




    and unifyTwoRefDefResults
        (a : AccumulatorTypeId * Result<RefDefType, AccTypeError>)
        (b : AccumulatorTypeId * Result<RefDefType, AccTypeError>)
        (acc : Accumulator)
        : AccAndTypeId =
        let accIdA, refDefResA = a
        let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

        let accIdB, refDefResB = b
        let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd

        match refDefResA, refDefResB with
        | Ok _, Error e
        | Error e, Ok _
        | Error e, Error _ ->
            let newKey = makeAccTypeId ()
            let accIdsToReplace = Set.ofList [ accIdA; accIdB ]
            let mergedRefConstrs = Set.union refConstrsA refConstrsB

            let updatedAcc =
                Accumulator.replaceEntries accIdsToReplace newKey (Some (Error e)) mergedRefConstrs acc

            Aati.make newKey updatedAcc

        | Ok refDefA, Ok refDefB -> unifyTwoRefDefs (accIdA, refDefA) (accIdB, refDefB) acc



    /// This is the function that should be folded over all the `refDefsWithIds` in the input
    and unifyTwoRefDefResOpts
        (a : AccumulatorTypeId * Result<RefDefType, AccTypeError> option)
        (b : AccumulatorTypeId * Result<RefDefType, AccTypeError> option)
        (acc : Accumulator)
        : AccAndTypeId =

        let accIdA, refDefResOptA = a
        let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

        let accIdB, refDefResOptB = b
        let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd


        let newKey = makeAccTypeId ()
        let accIdsToReplace = Set.ofList [ accIdA; accIdB ]
        let mergedRefConstrs = Set.union refConstrsA refConstrsB

        match refDefResOptA, refDefResOptB with
        | None, None ->
            let updatedAcc =
                Accumulator.replaceEntries accIdsToReplace newKey None mergedRefConstrs acc

            Aati.make newKey updatedAcc

        | Some x, None
        | None, Some x ->
            let updatedAcc =
                Accumulator.replaceEntries accIdsToReplace newKey (Some x) mergedRefConstrs acc

            Aati.make newKey updatedAcc

        | Some refDefResA, Some refDefResB -> unifyTwoRefDefResults (accIdA, refDefResA) (accIdB, refDefResB) acc



    let (TOM (head, neck, tail)) = refDefsWithIds
    let firstResult = unifyTwoRefDefResOpts head neck acc

    tail
    |> List.fold
        (fun state (accId, refDefResOpt) ->
            /// We retrieve the item whose ID is in the state because that's the one that the current item needs to be merged with
            let toMergeWith = Accumulator.getTypeById state.typeId state.acc

            let refDefToMergeWith : Result<RefDefType, AccTypeError> option = fst toMergeWith
            // // I don't think there was anything to do with this set, because this unifyRefDefsSinglePass function should only be responsible for unifying the RefDefs it was given, not the RefConstrs I think.
            //let refConstrsToMergeWith : RefConstr set = snd toMergeWith

            let unifyResult =
                unifyTwoRefDefResOpts (accId, refDefResOpt) (state.typeId, refDefToMergeWith) state.acc


            unifyResult)
        firstResult
















/// Version of unifyRefDefResOptsTom that only needs to be given AccIds, not the RefDefs also
and unifyAccIdsTom (accIds : AccumulatorTypeId tom) (acc : Accumulator) : AccAndTypeId =
    let tom =
        accIds
        |> TOM.map (fun accId -> Accumulator.getRealIdAndType accId acc)
        |> TOM.map (fun (realAccId, (refDefResOpt, _)) -> realAccId, refDefResOpt)

    unifyRefDefResOptsTom tom acc




/// Just a wrapper for unifyRefDefResOptsTom that handles all lists
and unifyManyRefDefResOpts
    (refDefsWithIds : (AccumulatorTypeId * Result<RefDefType, AccTypeError> option) seq)
    (acc : Accumulator)
    : AccAndTypeId =
    match Seq.toList refDefsWithIds with
    | [] ->
        let newKey = makeAccTypeId ()

        { acc with
            refConstraintsMap =
                acc.refConstraintsMap
                |> Map.add newKey (None, Set.empty) }
        |> Aati.make newKey

    | (key, _) :: [] -> Aati.make key acc

    | head :: neck :: tail -> unifyRefDefResOptsTom (TOM.new_ head neck tail) acc





/// This adds RefConstrs for an existing AccId and runs the unification if/when needed
and addRefConstrsForAccId (accId : AccumulatorTypeId) (refConstrs : RefConstr set) (acc : Accumulator) : AccAndTypeId =
    let refConstrInformation = getRefConstrAddOrUnifyInfo refConstrs acc

    /// Add the RefConstrs for the new entry
    let addRefConstrsToEntry combinedRefConstrs =
        Accumulator.replaceEntry accId (fun _ refDef _ -> refDef, combinedRefConstrs) acc
        |> snd

    match refConstrInformation with
    | NotCurrentlyInAcc ->
        // The refConstrs need to be added for the newly added item

        addRefConstrsToEntry refConstrs |> Aati.make accId

    | InOneEntry (existingAccId, combinedRefConstrs) ->
        // Unify the existing and new entries

        addRefConstrsToEntry combinedRefConstrs
        |> unifyTwoAccTypeIds existingAccId accId

    | InMultipleEntries (accIds, combinedRefConstrs) ->
        // Unify the new and existing entries

        addRefConstrsToEntry combinedRefConstrs
        |> unifyAccIdsTom (TOM.cons accId accIds)



/// Adds a new RefDef and its reference constraints into the map (including RefConstr overlap unification)
and addRefDefResOptWithRefConstrs
    (refDefResOpt : Result<RefDefType, AccTypeError> option)
    (refConstrs : RefConstr set)
    (acc : Accumulator)
    : AccAndTypeId =
    let accId, withRefDefAdded = Accumulator.addRefDefResOpt refDefResOpt acc

    addRefConstrsForAccId accId refConstrs withRefDefAdded



and unifyTwoRefDefResOpts
    (accIdA : AccumulatorTypeId)
    (refDefResOptA : Result<RefDefType, AccTypeError> option)
    (accIdB : AccumulatorTypeId)
    (refDefResOptB : Result<RefDefType, AccTypeError> option)
    (acc : Accumulator)
    : AccAndTypeId =
    unifyRefDefResOptsTom (TOM.make (accIdA, refDefResOptA) (accIdB, refDefResOptB)) acc



and unifyTwoAccTypeIds (idA : AccumulatorTypeId) (idB : AccumulatorTypeId) (acc : Accumulator) : AccAndTypeId =
    let itemA, _ = Accumulator.getTypeById idA acc
    let itemB, _ = Accumulator.getTypeById idB acc

    unifyTwoRefDefResOpts idA itemA idB itemB acc


/// Merges two accumulators. No IDs should be lost, refDefs should be unified according to reference constraint overlaps. And resulting combined IDs should be unified also.
///
/// There should be no entities from one Acc referencing IDs in the other.
let rec combine (acc1 : Accumulator) (acc2 : Accumulator) : Accumulator =
    // I think the way to do this is by inserting the items without any dependencies on other AccIds first, e.g. those entries which are None or Unit or PrimitiveType. Once those are done, then get their IDs and we can insert the next batch of types, namely those which reference (only) those IDs we've just inserted (or that reference any IDs we've inserted already, even if those were partly in a previous batch).
    // That way we can add one RefDefType (with accompanying RefConstrs) at a time, whilst still ensuring we never end up in a place where the Acc contains references to AccIds it does not contain!
    // Note: we add the items in acc1 to acc2, as per the convention where the last parameter is the data type being modified

    // @TODO: not sure this works if there are circular dependencies! Probably doesn't. We'll need to look into detecting cyclical deps and importing those as a single unit then.

    /// Is the given refDef one of the allowed ones
    let isRefDefWithAllowedAccIdDep (addedDepAccIds : AccumulatorTypeId set) (refDef : RefDefType) : bool =
        let hasId accId = Set.contains accId addedDepAccIds

        match refDef with
        | RefDtUnitType -> true
        | RefDtPrimType _ -> true
        | RefDtList accId -> hasId accId
        | RefDtTuple accIdTom -> accIdTom |> TOM.map hasId |> TOM.fold (&&) true
        | RefDtRecordWith fields ->
            Map.values fields
            |> Seq.map hasId
            |> Seq.fold (&&) true
        | RefDtRecordExact fields ->
            Map.values fields
            |> Seq.map hasId
            |> Seq.fold (&&) true
        | RefDtNewType (_, typeParams) -> typeParams |> Seq.map hasId |> Seq.fold (&&) true
        | RefDtArrow (fromType, toType) -> hasId fromType && hasId toType


    /// Gets all the AccIds that redirect to a set of other AccIds, recursively
    let rec getAllRedirectsPointingTo (accIds : AccumulatorTypeId set) redirectsMap =
        let thisBatchResults =
            redirectsMap
            |> Map.filter (fun _ dest -> Set.contains dest accIds)
            |> Map.keys
            |> Seq.toList

        match thisBatchResults with
        | [] -> accIds
        | _ ->
            redirectsMap
            |> Map.removeKeys (Set.ofSeq thisBatchResults)
            |> getAllRedirectsPointingTo (Set.union accIds (Set.ofSeq thisBatchResults))



    /// Recursive function that plucks the types from the source Acc and moves them over to the destination Acc one at a time, ensuring it's only moving the ones that either have no dependencies on other AccIds, or whose dependencies have already been moved over!
    /// The base case is when there are no more new entries able to be moved over, which should occur only when the sourceAcc has been plucked empty – and therefore it's probably worth making it throw an error if only one but not both of those conditions are true!
    /// And at the base case, we return the destinationAcc, which should at that point be the fully merged Acc containing all the items from acc1 (and of course acc2 which is what it started out as)
    let rec getItemsWithAllowedDependencies (sourceAcc : Accumulator) (destinationAcc : Accumulator) : Accumulator =
        let addedDepAccIds =
            Set.union
                (Map.keys destinationAcc.refConstraintsMap
                 |> Set.ofSeq)
                (Map.keys destinationAcc.redirectMap |> Set.ofSeq)

        let allDepAccIds =
            getAllRedirectsPointingTo addedDepAccIds destinationAcc.redirectMap

        /// These are the entries whose AccIds they reference are all already in the destAcc so they can be moved over from the sourceAcc
        let entriesAllowedNow =
            sourceAcc.refConstraintsMap
            |> Map.filter (fun _ (refDefResOpt, _) ->
                match refDefResOpt with
                | None -> true
                | Some refDefRes ->
                    match refDefRes with
                    | Ok refDef -> isRefDefWithAllowedAccIdDep allDepAccIds refDef
                    | Error (DefTypeClash (refDefA, refDefB)) ->
                        isRefDefWithAllowedAccIdDep allDepAccIds refDefA
                        && isRefDefWithAllowedAccIdDep allDepAccIds refDefB)


        let noMoreEntriesToAdd = Map.isEmpty entriesAllowedNow
        let sourceAccConstrsAreEmpty = Map.isEmpty sourceAcc.refConstraintsMap

        if noMoreEntriesToAdd && sourceAccConstrsAreEmpty then
            destinationAcc

        else if noMoreEntriesToAdd && not sourceAccConstrsAreEmpty then
            failwith "Shouldn't be possible for there to be no more entries to add but the source Acc to not be empty"

        else if not noMoreEntriesToAdd && sourceAccConstrsAreEmpty then
            failwith "Shouldn't be possible for there to still be entries to add but the source Acc to be empty"

        else
            /// This expects that the thing we're adding does not depend on any AccIds that aren't already in the map
            let addSingleThingToDestMap
                (singleThing : AccumulatorTypeId * (Result<RefDefType, AccTypeError> option * RefConstr set))
                (acc : Accumulator)
                : Accumulator =
                let key, (refDefResOpt, refConstrs) = singleThing

                let _, withRefDefInserted =
                    Accumulator.addRefDefResOptUnderKey key refDefResOpt acc
                    |> Accumulator.replaceEntry key (fun _ rd _ -> rd, refConstrs)

                addRefConstrsForAccId key refConstrs withRefDefInserted
                |> Aati.getAcc


            let updatedDestAcc =
                entriesAllowedNow
                |> Map.toList
                |> List.fold (fun state thisEntry -> addSingleThingToDestMap thisEntry state) destinationAcc


            let updatedSourceAcc =
                { sourceAcc with
                    refConstraintsMap =
                        sourceAcc.refConstraintsMap
                        |> Map.removeKeys (Map.keys entriesAllowedNow) }

            getItemsWithAllowedDependencies updatedSourceAcc updatedDestAcc


    getItemsWithAllowedDependencies acc1 { acc2 with redirectMap = Map.merge acc1.redirectMap acc2.redirectMap }







and combineMany (accs : Accumulator seq) : Accumulator = Seq.fold combine Accumulator.empty accs

/// Combine Accumulators from a seq of `AccAndTypeId`s
and combineAccsFromAatis (aatis : AccAndTypeId seq) =
    Seq.map Aati.getAcc aatis |> combineMany








/// Adds a new entry and unifies RefConstrs as needed
let addRefConstraints (refConstrs : RefConstr set) (acc : Accumulator) : AccAndTypeId =
    addRefDefResOptWithRefConstrs None refConstrs acc





/// @TODO: maybe do this using the more fundamental unifyTypeConstraintIds? idk tho
let unifyManyTypeConstraintIds (ids : AccumulatorTypeId seq) (acc : Accumulator) : AccAndTypeId =
    let refDefsWithIds =
        Seq.map (fun id -> id, Accumulator.getTypeById id acc |> fst) ids

    unifyManyRefDefResOpts refDefsWithIds acc








/// This adds a single extra RefDef constraint onto an existing entry in the Acc
let addRefDefConstraintForAccId
    (refDefResOpt : Result<RefDefType, AccTypeError> option)
    (accId : AccumulatorTypeId)
    (acc : Accumulator)
    : AccAndTypeId =
    let newKey = makeAccTypeId ()

    /// It's not the most efficient way to do it to add a whole new AccId just so we have something to point `unifyTypeConstraintIds` to, but it works and if we really care we can make it more efficient later
    let accWithRefDefAdded =
        { acc with
            refConstraintsMap =
                acc.refConstraintsMap
                |> Map.add newKey (refDefResOpt, Set.empty) }

    accWithRefDefAdded
    |> unifyTwoAccTypeIds newKey accId





/// Adds a new RefDef (without any accompanying reference constraints) into the map
let addRefDefResOpt (refDefResOpt : Result<RefDefType, AccTypeError> option) (acc : Accumulator) =
    addRefDefResOptWithRefConstrs refDefResOpt Set.empty acc







(*
    Conversions to and from TypeConstraints
*)



/// Convert a DefinitiveType to an Acc and get its root AccTypeId. This Acc can then be merged with others.
let rec convertDefinitiveType (def : DefinitiveType) : AccAndTypeId =
    let newKey = makeAccTypeId ()

    /// From a RefDefType
    let makeOkType : RefDefType -> Result<RefDefType, AccTypeError> option = Ok >> Some
    let makeErrType a b : Result<RefDefType, AccTypeError> option = DefTypeClash (a, b) |> Error |> Some

    let makeSingletonAcc (refDefResOpt : Result<RefDefType, AccTypeError> option) : Accumulator =
        { Accumulator.empty with refConstraintsMap = Map.ofList [ newKey, (refDefResOpt, Set.empty) ] }

    //let addToAcc (refDefResOpt : Result<RefDefType, AccTypeError> option) (acc:Accumulator2) : Accumulator2 =


    match def with
    | DtUnitType ->
        makeSingletonAcc (makeOkType RefDtUnitType)
        |> Aati.make newKey

    | DtPrimitiveType prim ->
        makeSingletonAcc (makeOkType (RefDtPrimType prim))
        |> Aati.make newKey

    | DtList tc ->
        let resultOfGeneric = convertTypeConstraints tc
        let listType = RefDtList resultOfGeneric.typeId

        addRefDefResOptWithRefConstrs (makeOkType listType) Set.empty resultOfGeneric.acc


    | DtTuple tom ->
        let resultsTom = TOM.map convertTypeConstraints tom

        let combinedAccs =
            resultsTom
            |> TOM.map Aati.getAcc
            |> TOM.fold combine Accumulator.empty

        let tupleType = RefDtTuple (TOM.map Aati.getId resultsTom)

        addRefDefResOptWithRefConstrs (makeOkType tupleType) Set.empty combinedAccs

    | DtArrow (fromType, toType) ->
        let fromResult = convertTypeConstraints fromType
        let toResult = convertTypeConstraints toType

        let fromAndToAcc = combine fromResult.acc toResult.acc

        let arrowType = RefDtArrow (fromResult.typeId, toResult.typeId)

        let result =
            addRefDefResOptWithRefConstrs (makeOkType arrowType) Set.empty fromAndToAcc

        result

    | DtRecordExact map ->
        let resultsMap = Map.map (fun _ tc -> convertTypeConstraints tc) map

        let mapType = RefDtRecordExact (resultsMap |> Map.map (fun _ -> Aati.getId))

        let combinedAcc =
            resultsMap
            |> Map.fold (fun state _ thisAati -> combine thisAati.acc state) Accumulator.empty

        addRefDefResOptWithRefConstrs (makeOkType mapType) Set.empty combinedAcc

    | DtRecordWith map ->
        let resultsMap = Map.map (fun _ tc -> convertTypeConstraints tc) map

        let mapType = RefDtRecordWith (resultsMap |> Map.map (fun _ -> Aati.getId))

        let combinedAcc =
            resultsMap
            |> Map.fold (fun state _ thisAati -> combine thisAati.acc state) Accumulator.empty

        addRefDefResOptWithRefConstrs (makeOkType mapType) Set.empty combinedAcc

    | DtNewType (typeName, constraints) ->
        let resultsList = List.map convertTypeConstraints constraints

        let combinedAccs = resultsList |> List.map Aati.getAcc |> combineMany

        let newType = RefDtNewType (typeName, List.map Aati.getId resultsList)

        addRefDefResOptWithRefConstrs (makeOkType newType) Set.empty combinedAccs




and convertTypeConstraints (tc : TypeConstraints) : AccAndTypeId =
    let (Constrained (defOpt, refConstrs)) = tc

    let withRefConstrsAdded = addRefConstraints refConstrs Accumulator.empty

    match defOpt with
    | None -> withRefConstrsAdded
    | Some def ->
        let defTypeAcc = convertDefinitiveType def
        let combinedAcc = combine withRefConstrsAdded.acc defTypeAcc.acc

        unifyTwoAccTypeIds defTypeAcc.typeId withRefConstrsAdded.typeId combinedAcc


and convertTypeJudgment (judgment : TypeJudgment) : AccAndTypeId =
    let newKey = makeAccTypeId ()

    match judgment with
    | Ok tc -> convertTypeConstraints tc
    | Error e ->
        { Accumulator.empty with
            refConstraintsMap =
                Map.empty
                |> Map.add newKey (Some (Error e), Set.empty) }
        |> Aati.make newKey














let rec convertRefDefToTypeConstraints
    (refDef : RefDefType)
    (refConstrsToAdd : RefConstr set)
    (acc : Accumulator)
    : Result<TypeConstraints, AccTypeError> =
    let fromDef def =
        TypeConstraints.Constrained (Some def, refConstrsToAdd)
        |> Ok

    /// Just a little helper where foundType is the last param, for easier use in `Result.bind`s
    let convertType refConstrs foundType =
        convertRefDefToTypeConstraints foundType refConstrs acc

    match refDef with
    | RefDtUnitType -> fromDef DtUnitType
    | RefDtPrimType prim -> DtPrimitiveType prim |> fromDef
    | RefDtList constrId ->
        let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

        match foundTypeResultOpt with
        | Some foundTypeResult ->
            foundTypeResult
            |> Result.bind (convertType refConstrs)
            |> Result.map (DtList >> TypeConstraints.fromDefinitive)

        | None -> Constrained (None, refConstrs) |> Ok

    | RefDtTuple constrTom ->
        let resultsTom =
            constrTom
            |> TOM.map (fun constrId ->
                let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                match foundTypeResultOpt with
                | Some foundTypeResult ->
                    foundTypeResult
                    |> Result.bind (convertType refConstrs)
                | None -> Constrained (None, refConstrs) |> Ok)
            |> TOM.sequenceResult

        match resultsTom with
        | Ok typeConstraints -> DtTuple typeConstraints |> fromDef

        | Error e -> Error (NEL.head e)


    | RefDtNewType (typeName, typeParams) ->
        let resultsTom =
            typeParams
            |> List.map (fun constrId ->
                let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                match foundTypeResultOpt with
                | Some foundTypeResult ->
                    foundTypeResult
                    |> Result.bind (convertType refConstrs)
                | None -> Constrained (None, refConstrs) |> Ok)
            |> Result.sequenceList

        match resultsTom with
        | Ok typeConstraints -> DtNewType (typeName, typeConstraints) |> fromDef

        | Error e -> Error (NEL.head e)


    | RefDtArrow (fromId, toId) ->
        let resultsPair =
            (fromId, toId)
            |> Tuple.map (fun constrId ->
                let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                match foundTypeResultOpt with
                | Some foundTypeResult ->
                    foundTypeResult
                    |> Result.bind (convertType refConstrs)
                | None -> Constrained (None, refConstrs) |> Ok)
            |> Tuple.sequenceResult

        resultsPair
        |> Result.map (DtArrow >> TypeConstraints.fromDefinitive)



    | RefDtRecordExact fields ->
        let resultsMap =
            fields
            |> Map.map (fun _ constrId ->
                let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                match foundTypeResultOpt with
                | Some foundTypeResult ->
                    foundTypeResult
                    |> Result.bind (convertType refConstrs)
                | None -> Constrained (None, refConstrs) |> Ok)
            |> Map.sequenceResult

        match resultsMap with
        | Ok typeConstraintsMap -> DtRecordExact typeConstraintsMap |> fromDef
        | Error (_, errsNel) -> Error (NEL.head errsNel)


    | RefDtRecordWith fields ->
        let resultsMap =
            fields
            |> Map.map (fun _ constrId ->
                let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                match foundTypeResultOpt with
                | Some foundTypeResult ->
                    foundTypeResult
                    |> Result.bind (convertType refConstrs)
                | None -> Constrained (None, refConstrs) |> Ok)
            |> Map.sequenceResult

        match resultsMap with
        | Ok typeConstraintsMap -> DtRecordWith typeConstraintsMap |> fromDef
        | Error (_, errsNel) -> Error (NEL.head errsNel)




let convertAccIdToTypeConstraints (accId : AccumulatorTypeId) (acc : Accumulator) : TypeJudgment =
    let foundType, refConstrs = Accumulator.getTypeById accId acc

    match foundType with
    | Some typeResult ->
        match typeResult with
        | Ok refDef -> convertRefDefToTypeConstraints refDef refConstrs acc
        | Error e -> Error e
    | None -> Constrained (None, refConstrs) |> Ok





let addTypeConstraintsToAcc (typeConstraints : TypeConstraints) (acc : Accumulator) : AccAndTypeId =
    let result = convertTypeConstraints typeConstraints
    combine result.acc acc |> Aati.make result.typeId


let addTypeConstraintForName (name : RefConstr) (tc : TypeConstraints) (acc : Accumulator) : AccAndTypeId =
    let (Constrained (defOpt, refs)) = tc
    let tcWithName = Constrained (defOpt, Set.add name refs)

    addTypeConstraintsToAcc tcWithName acc








/// This is mostly for verifying tests and things, to have an easy way to compare a thing to a concrete thing without polluting it with reference constraints and things
let rec convertRefDefToConcreteType
    (refDef : RefDefType)
    (acc : Accumulator)
    : Result<ConcreteOrGeneric, AccTypeError> =
    let convertFromAccId typeId = convertAccTypeIdToConcrete typeId acc

    match refDef with
    | RefDtUnitType -> Ok ConcUnitType
    | RefDtPrimType prim -> ConcPrimType prim |> Ok
    | RefDtList tc -> convertFromAccId tc |> Result.map ConcList
    | RefDtTuple accIds ->
        accIds
        |> TOM.map convertFromAccId
        |> TOM.sequenceResult
        |> Result.mapError NEL.head
        |> Result.map ConcTuple
    | RefDtRecordWith fields ->
        fields
        |> Map.toList
        |> List.map (fun (field, value) ->
            convertFromAccId value
            |> Result.map (fun v -> field, v))
        |> Result.sequenceList
        |> Result.mapError NEL.head
        |> Result.map (Map.ofList >> ConcRecordWith)

    | RefDtRecordExact fields ->
        fields
        |> Map.toList
        |> List.map (fun (field, value) ->
            convertFromAccId value
            |> Result.map (fun v -> field, v))
        |> Result.sequenceList
        |> Result.mapError NEL.head
        |> Result.map (Map.ofList >> ConcRecordExact)

    | RefDtNewType (typeName, typeVars) ->
        let typeVarResults =
            typeVars
            |> List.map convertFromAccId
            |> Result.sequenceList
            |> Result.mapError NEL.head

        typeVarResults
        |> Result.map (fun typeVars' -> ConcNewType (typeName, typeVars'))

    | RefDtArrow (fromType, toType) ->
        (convertFromAccId fromType, convertFromAccId toType)
        ||> Result.map2 (fun from' to' -> ConcArrow (from', to')) always



and convertRefDefOptToConcrete
    (refDefOpt : RefDefType option)
    (acc : Accumulator)
    : Result<ConcreteOrGeneric, AccTypeError> =
    match refDefOpt with
    | Some refDef -> convertRefDefToConcreteType refDef acc

    | None -> Ok Generic



and convertRefDefResOptToConcrete
    (refDefResOpt : Result<RefDefType, AccTypeError> option)
    (acc : Accumulator)
    : Result<ConcreteOrGeneric, AccTypeError> =
    match refDefResOpt with
    | Some (Ok refDef) -> convertRefDefOptToConcrete (Some refDef) acc
    | Some (Error e) -> Error e
    | None -> convertRefDefOptToConcrete None acc

and convertAccTypeIdToConcrete
    (accId : AccumulatorTypeId)
    (acc : Accumulator)
    : Result<ConcreteOrGeneric, AccTypeError> =
    let refDefResOpt, _ = Accumulator.getTypeById accId acc
    convertRefDefResOptToConcrete refDefResOpt acc










let rec convertDefinitiveToConcrete (defType : DefinitiveType) : ConcreteOrGeneric =
    match defType with
    | DtUnitType -> ConcUnitType
    | DtPrimitiveType prim -> ConcPrimType prim
    | DtTuple items -> ConcTuple (TOM.map convertTypeConstraintsToConcrete items)
    | DtList tc -> ConcList (convertTypeConstraintsToConcrete tc)
    | DtRecordWith fields -> ConcRecordWith (Map.map (fun _ tc -> convertTypeConstraintsToConcrete tc) fields)
    | DtRecordExact fields -> ConcRecordExact (Map.map (fun _ tc -> convertTypeConstraintsToConcrete tc) fields)
    | DtNewType (typeName, typeVars) -> ConcNewType (typeName, List.map convertTypeConstraintsToConcrete typeVars)
    | DtArrow (fromType, toType) ->
        ConcArrow (convertTypeConstraintsToConcrete fromType, convertTypeConstraintsToConcrete toType)



and convertTypeConstraintsToConcrete (tc : TypeConstraints) : ConcreteOrGeneric =
    let (Constrained (defOpt, _)) = tc

    match defOpt with
    | Some def -> convertDefinitiveToConcrete def
    | None -> Generic






/// Returns the Acc entry for a given RefConstr if it exists in the Acc
let getEntryByRefConstr
    (refConstr : RefConstr)
    (acc : Accumulator)
    : (AccumulatorTypeId * (RefDefResOpt * RefConstr set)) option =
    acc.refConstraintsMap
    |> Map.tryPick (fun accId (refDefResOpt, refConstrs) ->
        if Set.contains refConstr refConstrs then
            Some (accId, (refDefResOpt, refConstrs))
        else
            None)


let getAccIdByRefConstr (refConstr : RefConstr) (acc : Accumulator) : AccumulatorTypeId option =
    getEntryByRefConstr refConstr acc
    |> Option.map fst











type RefConstrToTypeConstraintsMap =
    | RefConstrToTypeConstraintsMap of Map<RefConstr, Result<TypeConstraints, AccTypeError> option>



module RefConstrToTypeConstraintsMap =

    /// Makes a new map from an Accumulator
    let fromAcc (acc : Accumulator) : RefConstrToTypeConstraintsMap =
        Map.values acc.refConstraintsMap
        |> Seq.map (fun (refDefResOpt, refConstrs) ->
            refConstrs,
            refDefResOpt
            |> Option.map (Result.bind (fun refDef -> convertRefDefToTypeConstraints refDef refConstrs acc)))
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

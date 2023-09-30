module DisjointSetForest




type DisjointSetForest<'T when 'T : comparison> =
    { map : Map<'T, 'T option> }

    static member init (elems : 'T seq) : DisjointSetForest<'T> =
        let root = Seq.min elems
        let nonRoots = Seq.filter ((<>) root) elems

        { map =
            nonRoots
            |> Seq.map (fun elem -> elem, Some root)
            |> Map.ofSeq
            |> Map.add root None }

    static member find (elem : 'T) (dsf : DisjointSetForest<'T>) =
        match Map.tryFind elem dsf.map with
        | None -> None
        | Some found ->
            match found with
            | None -> Some elem
            | Some result -> DisjointSetForest.find result dsf

    /// This also adds the items into the DSF if they're not there yet
    static member union (a : 'T) (b : 'T) (dsf : DisjointSetForest<'T> when 'T : comparison) =
        let rootOfAOpt = DSF.find a dsf
        let rootOfBOpt = DSF.find b dsf

        match rootOfAOpt, rootOfBOpt with
        | None, None ->
            let minItem = min a b
            let maxItem = max a b

            { map =
                dsf.map
                |> Map.add maxItem (Some minItem)
                |> Map.add minItem None }

        | Some rootOfA, None ->
            let minItem = min rootOfA b
            let maxItem = max rootOfA b

            { map =
                dsf.map
                |> Map.add maxItem (Some minItem)
                |> Map.add minItem None }

        | None, Some rootOfB ->
            let minItem = min a rootOfB
            let maxItem = max a rootOfB

            { map =
                dsf.map
                |> Map.add maxItem (Some minItem)
                |> Map.add minItem None }

        | Some rootOfA, Some rootOfB ->
            let minItem = min rootOfA rootOfB
            let maxItem = max rootOfA rootOfB

            { map = dsf.map |> Map.add maxItem (Some minItem) }

    static member addSet (elems : 'T seq) (dsf : DisjointSetForest<'T>) =
        let rootsOrNewElems =
            elems
            |> Seq.map (fun elem ->
                // Get either the root node if elem is in the map, or get the elem itself if it's not
                DSF.find elem dsf |> Option.defaultValue elem)

        /// Get the min item of the whole thing, either the found root nodes, or the elems themselves
        let minItem = Seq.min rootsOrNewElems

        let newMap =
            rootsOrNewElems
            |> Seq.fold
                (fun map elem ->
                    // Add or replace the elems with a reference to the new smallest item, which will therefore be the newest root node for all items in the combined set
                    Map.add elem (Some minItem) map)
                dsf.map
            |> Map.add minItem None

        { map = newMap }


and DSF<'T when 'T : comparison> = DisjointSetForest<'T>













type PointerOrContent<'T, 'U when 'T : comparison> =
    | Pointer of 'T
    | Content of 'U


type DisjointSetForestWithContent<'T, 'U when 'T : comparison and 'U : equality> =
    { map : Map<'T, PointerOrContent<'T, 'U>>

      /// This is just to store a function, it doesn't actually do anything else.
      ///
      /// This is the function that, given two pieces of data and the DSF, returns the unified piece of data plus which (if any) elems now need to be unioned
      unifyDataMany : 'U nel -> 'U * 'T seq }

    static member init
        (unifyDataMany : 'U nel -> 'U * 'T seq)
        (elems : 'T seq)
        (data : 'U)
        : DisjointSetForestWithContent<'T, 'U> =
        let root = Seq.min elems
        let nonRoots = Seq.filter ((<>) root) elems

        { map =
            nonRoots
            |> Seq.map (fun elem -> elem, Pointer root)
            |> Map.ofSeq
            |> Map.add root (Content data)
          unifyDataMany = unifyDataMany }

    static member findRootAndData (elem : 'T) (dsf : DSFC<'T, 'U>) : ('T * 'U) option =
        match Map.tryFind elem dsf.map with
        | None -> None
        | Some found ->
            match found with
            | Content data ->
                // Then this must be the root element of the set
                Some (elem, data)

            | Pointer ptr -> DSFC.findRootAndData ptr dsf


    /// This gives you the root element of the set, so if two elements have the same root element they are in the same set
    static member findSetRoot (elem : 'T) (dsf : DSFC<'T, 'U>) : 'T option =
        DSFC.findRootAndData elem dsf |> Option.map fst


    /// This gives you the data for the set that this element is in
    static member findData (elem : 'T) (dsf : DSFC<'T, 'U>) : 'U option =
        DSFC.findRootAndData elem dsf |> Option.map snd






    static member private unionSetsSingleStepMany
        (elemsToMerge : 'T seq)
        (dsf : DSFC<'T, 'U>)
        : 'U nel * 'T * DSFC<'T, 'U> =

        let findResults =
            elemsToMerge
            |> Seq.map (fun elem -> elem, DSFC.findRootAndData elem dsf)

        let newElems, existingElems =
            findResults
            |> Seq.toList
            |> List.typedPartition (fun (elem, findResult) ->
                match findResult with
                | None -> Choice1Of2 elem
                | Some (rootElem, data) -> Choice2Of2 ({| data = data; rootElem = rootElem |}))

        match newElems, existingElems with
        | _, [] ->
            failwith "At least one of the elements in the sequence we're unioning has to already be present in the DSF" // Because we need at least one data to return

        | newEls, existingHead :: existingRest ->
            let existingNel = NEL.new_ existingHead existingRest

            let minExistingElemAndData = existingNel |> NEL.minBy (fun el -> el.rootElem)
            let minData = minExistingElemAndData.data

            /// Or to insert for the first time tbh
            let allElemsToRedirect =
                NEL.appendList (existingNel |> NEL.map (fun el -> el.rootElem)) newEls

            let minElem = NEL.min<_> allElemsToRedirect

            let newDsf =
                { dsf with
                    map =
                        allElemsToRedirect
                        |> NEL.fold (fun map elem -> Map.add elem (Pointer minElem) map) dsf.map
                        |> Map.add minElem (Content minData) }

            existingNel |> NEL.map (fun el -> el.data), minElem, newDsf




    /// @TODO: implement this! might need to implement a `DSFC.unionSetsManySingleStep` method in the process!
    static member unionSetsMany (elemsToMerge : 'T seq) (dsf : DSFC<'T, 'U>) : DSFC<'T, 'U> =
        let singleStepResult = DSFC.unionSetsSingleStepMany elemsToMerge dsf
        let dataToMerge, rootElem, singleStepUnionedDsf = singleStepResult

        let distinctDatas = NEL.distinct<_> dataToMerge

        match distinctDatas with
        | NEL (onlyData, []) -> { singleStepUnionedDsf with map = dsf.map |> Map.add rootElem (Content onlyData) }

        | _ ->
            let unifiedData, furtherElsToMerge = dsf.unifyDataMany distinctDatas

            let dsfWithUnifiedData =
                { singleStepUnionedDsf with map = dsf.map |> Map.add rootElem (Content unifiedData) }

            match Seq.toList furtherElsToMerge with
            | [] -> dsfWithUnifiedData

            | furtherElsToMerge_ -> DSFC.unionSetsMany furtherElsToMerge_ dsfWithUnifiedData



    static member private addSetSingleStep
        (data : 'U)
        (elemsToMerge : 'T seq)
        (dsf : DSFC<'T, 'U>)
        : 'U nel * 'T * DSFC<'T, 'U> =
        let findResults =
            elemsToMerge
            |> Seq.map (fun elem -> elem, DSFC.findRootAndData elem dsf)

        let newElems, existingElems =
            findResults
            |> Seq.toList
            |> List.typedPartition (fun (elem, findResult) ->
                match findResult with
                | None -> Choice1Of2 elem
                | Some (rootElem, data) -> Choice2Of2 ({| data = data; rootElem = rootElem |}))

        match newElems, existingElems with
        | [], [] -> failwith "There has to be at least one element being added"

        | newElemHead :: newElemTail, [] ->
            let newEls = NEL.new_ newElemHead newElemTail
            let minElem = NEL.min<_> newEls

            let newDsf =
                { dsf with
                    map =
                        newEls
                        |> NEL.fold (fun map elem -> Map.add elem (Pointer minElem) map) dsf.map
                        |> Map.add minElem (Content data) }

            NEL.make data, minElem, newDsf


        | newEls, existingHead :: existingRest ->
            let existingNel = NEL.new_ existingHead existingRest

            /// Or to insert for the first time tbh
            let allElemsToRedirect =
                NEL.appendList (existingNel |> NEL.map (fun el -> el.rootElem)) newEls

            let minElem = NEL.min<_> allElemsToRedirect

            let newDsf =
                { dsf with
                    map =
                        allElemsToRedirect
                        |> NEL.fold (fun map elem -> Map.add elem (Pointer minElem) map) dsf.map
                        |> Map.add minElem (Content data) }

            existingNel
            |> NEL.map (fun el -> el.data)
            |> NEL.cons data,
            minElem,
            newDsf


    static member addSet (data : 'U) (elemsToMerge : 'T seq) (dsf : DSFC<'T, 'U>) : DSFC<'T, 'U> =
        let singleStepResult = DSFC.addSetSingleStep data elemsToMerge dsf
        let dataToMerge, rootElem, singleStepUnionedDsf = singleStepResult

        let distinctDatas = NEL.distinct<_> dataToMerge

        match distinctDatas with
        | NEL (onlyData, []) ->
            { singleStepUnionedDsf with
                map =
                    singleStepUnionedDsf.map
                    |> Map.add rootElem (Content onlyData) }

        | _ ->
            let unifiedData, furtherElsToMerge = dsf.unifyDataMany distinctDatas

            let dsfWithUnifiedData =
                { singleStepUnionedDsf with
                    map =
                        singleStepUnionedDsf.map
                        |> Map.add rootElem (Content unifiedData) }

            match Seq.toList furtherElsToMerge with
            | [] -> dsfWithUnifiedData

            | furtherElsToMerge_ -> DSFC.unionSetsMany furtherElsToMerge_ dsfWithUnifiedData



and DSFC<'T, 'U when 'T : comparison and 'U : equality> = DisjointSetForestWithContent<'T, 'U>

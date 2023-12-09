module DependencyGraphs



(*

    Topologically sorting name bindings & creating strongly connected components

*)



/// When putting items in a topologically sorted list, we need to treat the mutually recursive items like they are one thing, so we store them together
type OneOrMore<'T> =
    | One of 'T
    | More of 'T tom


type private DepsMap<'T, 'Key when 'Key : comparison> = Map<'Key, 'T * 'Key seq>



let makeDependenciesMap (getId : 'T -> 'Key) (getDependencies : 'T -> 'Key seq) (items : 'T seq) : DepsMap<'T, 'Key> =
    items
    |> Seq.map (fun item -> getId item, (item, getDependencies item))
    |> Map.ofSeq



let flipDependenciesMapToDependentsMap (dependenciesMap : DepsMap<'T, 'Key>) : DepsMap<'T, 'Key> =
    let dependentsMap =
        dependenciesMap
        |> Map.toSeq
        |> Seq.fold
            (fun map (key, (_, dependencyIds)) ->
                dependencyIds
                |> Seq.fold
                    (fun map' dependencyId ->
                        match Map.tryFind dependencyId map with
                        | None ->
                            let dependencyItem = Map.find dependencyId dependenciesMap |> fst

                            map' |> Map.add dependencyId (dependencyItem, Seq.singleton key)

                        | Some (item, dependentIds) ->
                            map' |> Map.add dependencyId (item, Seq.append dependentIds [ key ]))
                    map)
            Map.empty

    let withEmptyDependentsAdded =
        dependenciesMap
        |> Map.toSeq
        |> Seq.fold
            (fun map (key, (item, _)) ->
                match Map.tryFind key dependentsMap with
                | None -> map |> Map.add key (item, Seq.empty)
                | Some _ -> map)
            dependentsMap

    withEmptyDependentsAdded










/// Check if node is already in the stack, and if yes, return a record containing both the stack up to this point and the stack from this node onwards. Otherwise return None.
/// @TODO: bug here! since the list here is a *stack* we need to treat it like one, and higher indexed items are *earlier* in the list!
let private checkIfNodeIsAlreadyInStack
    (getId : 'T -> 'Key)
    (stack : 'T list)
    (node : 'T)
    : {| upToHere : 'T list
         afterThisNode : 'T list |} option
    =
    let upToHere, thisNodeOnwardsOpt =
        List.foldBack
            (fun item (upToHere, thisNodeOnwards) ->
                match thisNodeOnwards with
                | Some list -> upToHere, Some (item :: list)
                | None ->
                    if getId item = getId node then
                        upToHere, Some List.empty

                    else
                        item :: upToHere, None)
            stack
            (List.empty, None)

    thisNodeOnwardsOpt
    |> Option.map (fun thisNodeOnwards ->
        {| upToHere = upToHere
           afterThisNode = thisNodeOnwards |})






type private SccState<'T when 'T : comparison> =
    { highestIndex : uint
      highestNode : 'T
      allAccessibleThroughThisNode : 'T set }


let private makeSccState (hi : uint) (hn : 'T) (accessibles : 'T set) : SccState<'T> =
    { highestIndex = hi
      highestNode = hn
      allAccessibleThroughThisNode = accessibles }



let getStronglyConnectedComponents<'T, 'Key when 'Key : comparison and 'T : comparison>
    (getId : 'T -> 'Key)
    (getDependencies : 'T -> 'Key seq)
    (items : 'T seq)
    : OneOrMore<'T> list =
    let dependencyMap = makeDependenciesMap getId getDependencies items
    let dependentsMap = flipDependenciesMapToDependentsMap dependencyMap


    /// This returns at least the node itself if it has no dependents. Otherwise it will return any strongly connected graphs the node is part of, along with the results from the node's dependents
    let rec recurser
        (alreadyGatheredResults : OneOrMore<'T> set)
        (stack : 'T list)
        (node : 'T)
        : SccState<'T> option * OneOrMore<'T> set =
        let nodeId = getId node

        let alreadyProcessedThisNode =
            alreadyGatheredResults
            |> Set.exists (function
                | One item -> item = node
                | More itemsTom -> TOM.exists<_> ((=) node) itemsTom)


        if alreadyProcessedThisNode then
            None, Set.empty

        else

            let childNodes =
                Map.find nodeId dependentsMap
                |> snd
                |> Seq.map (fun key ->
                    match Map.tryFind key dependentsMap with
                    | None -> failwith $"Can't find key {key} in map"
                    | Some (item, _) -> item)


            match checkIfNodeIsAlreadyInStack getId stack node with
            | Some inStackResult ->
                match inStackResult.afterThisNode with
                | [] -> // This node is its own component – albeit it is its own dependent!
                    makeSccState (List.length inStackResult.upToHere |> uint) node Set.empty |> Some, Set.empty

                | head :: tail -> // This node is part of a larger strongly connected component – and it may or may not be dependent on itself, that part doesn't really matter

                    makeSccState (List.length inStackResult.upToHere |> uint) node (Set.add head (Set.ofSeq tail))
                    |> Some,
                    Set.empty

            | None ->

                match Seq.toList childNodes with
                | [] -> // This node is its own component
                    None, One node |> Set.singleton


                | firstChildNode :: otherChildNodes ->

                    let theSccOpts, theCompletedSccs =
                        firstChildNode :: otherChildNodes
                        |> List.mapFold
                            (fun gatheredResults childNode ->
                                let sccStateOpt, completedSccs = recurser gatheredResults (node :: stack) childNode
                                sccStateOpt, Set.union gatheredResults completedSccs)
                            alreadyGatheredResults




                    ///// These are closed, packaged up, ready for returning upwards
                    //let theCompletedSccs : OneOrMore<'T> seq = recursiveResults |> Seq.collect snd

                    /// So if there are SCC states returned here that means that every single one of these must contain at least this node, because otherwise they would only be dependent on themselves, and they would not have been returned as an SCC state. So I *think* that means that pretty much they are all equivalent to each other (because after all that's what an SCC is, every node being reachable from every other node!), so we can just take the one with the highest index and return that as the overall SCC state for this node.
                    ///
                    /// However! We still need to check if the highestIndex/node is actually this node: if no, indeed just pass the state up, but if yes, that means we can close the loop here and just package up the SCC state as another completed SCC.

                    match List.choose id theSccOpts with
                    | [] ->
                        // There are no SCC states returned, so this node is not part of any SCCs, so just return the completed SCCs, as well as this node as its own SCC
                        None, Set.add (One node) theCompletedSccs

                    | headChildScc :: restChildSccs ->
                        let sccNel = NEL.new_ headChildScc restChildSccs

                        let highestIndex, highestNode =
                            sccNel
                            |> NEL.minBy _.highestIndex
                            |> fun sccState -> sccState.highestIndex, sccState.highestNode

                        let isThisTheHighestNode = node = highestNode

                        if isThisTheHighestNode then
                            // Then we close the SCC off here

                            let thisSccNodes =
                                sccNel
                                |> NEL.fold
                                    (fun collectedNodes sccState ->
                                        Set.add sccState.highestNode sccState.allAccessibleThroughThisNode
                                        |> Set.union collectedNodes)
                                    Set.empty

                            match Set.toList thisSccNodes with
                            | [] ->
                                failwith
                                    "There are zero nodes in a strongly connected graph. This should not be possible and likely indicates a bug."

                            | node' :: [] -> None, Set.add (One node') theCompletedSccs


                            | head' :: neck' :: tail' ->
                                let combinedNodesTom = TOM.new_ head' neck' tail'

                                None, Set.add (More combinedNodesTom) theCompletedSccs

                        else
                            // Otherwise we humbly pass the combined information about the SCC that this is part of up to the caller

                            let allAccessibleFromHere : 'T set =
                                sccNel |> NEL.map (_.allAccessibleThroughThisNode >> Set.ofSeq) |> Set.unionMany

                            Some (makeSccState highestIndex highestNode allAccessibleFromHere), theCompletedSccs


    dependencyMap
    |> Map.fold
        (fun alreadyGatheredSccs _ (node, _) ->
            let sccStateOpt, completedSccs = recurser alreadyGatheredSccs List.empty node

            match sccStateOpt with
            | Some _ ->
                failwith "A SCC should not be able to be returned from running the recursor with an empty stack"
            | None -> Set.union alreadyGatheredSccs completedSccs)
        Set.empty
    |> List.ofSeq




/// This requires the the items to form a DAG, otherwise they obviously cannot be sorted topologically
let rec sortTopologically<'T, 'Key when 'Key : comparison and 'T : comparison>
    (dependenciesMap : DepsMap<'T, 'Key>)
    : 'T list =
    if Map.isEmpty dependenciesMap then
        List.empty

    else
        let itemWithoutDeps =
            dependenciesMap
            |> Map.tryPick (fun key (item, deps) ->
                // Need to filter out references to itself because those do not count as a blocking dependency for sorting purposes
                if Seq.filter ((<>) key) deps |> Seq.isEmpty then
                    Some (key, item)
                else
                    None)

        match itemWithoutDeps with
        | None ->
            failwith
                "In a DAG there should always be at least one node without dependencies, so this should not be possible unless the graph is not actually a DAG"

        | Some (key, item) ->
            let newDependenciesMap =
                dependenciesMap
                |> Map.remove key
                |> Map.map (fun _ (item, deps) -> item, Seq.filter ((<>) key) deps)

            item :: sortTopologically newDependenciesMap



/// This takes a list of strongly connected components and sorts them based on their dependencies. This requires the the SCCs to form a DAG, otherwise they obviously cannot be sorted topologically.
let rec sortOneOrMoreTopologically<'T, 'Key when 'Key : comparison and 'T : comparison>
    (getId : 'T -> 'Key)
    (getDependencies : 'T -> 'Key seq)
    (sccs : OneOrMore<'T> seq)
    : OneOrMore<'T> list =

    let oomToSeq : OneOrMore<'T> -> 'T seq =
        function
        | One item -> Seq.singleton item
        | More itemsTom -> itemsTom

    let getIdFromOneOrMore : OneOrMore<'T> -> 'Key set =
        oomToSeq >> Seq.map getId >> Set.ofSeq


    let keyToGroupMapping : Map<'Key, 'Key set> =
        sccs
        |> Seq.collect (fun scc ->
            let keySet = getIdFromOneOrMore scc
            let individualKeys = Set.toList keySet

            individualKeys |> Seq.map (fun singleKey -> singleKey, keySet))
        |> Map.ofSeq

    let getKeyGroup key =
        match Map.tryFind key keyToGroupMapping with
        | None -> failwith $"Couldn't find key {key} in keygroup map"
        | Some v -> v


    let getDependenciesFromOneOrMore (oom : OneOrMore<'T>) : 'Key set seq =
        oomToSeq oom
        |> Seq.collect getDependencies
        |> Seq.map getKeyGroup
        |> Set.ofSeq // to remove duplicates
        |> Set.toSeq

    let dependencyMap : DepsMap<OneOrMore<'T>, 'Key set> =
        makeDependenciesMap getIdFromOneOrMore getDependenciesFromOneOrMore sccs

    sortTopologically dependencyMap

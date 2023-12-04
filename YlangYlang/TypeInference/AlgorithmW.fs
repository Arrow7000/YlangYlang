module AlgorithmW


open TypedSyntaxTree
module T = TypedSyntaxTree
open QualifiedSyntaxTree.Names


module D = DummyLang

module Sacuv = SelfAndConstrainedUnificationVars

///// The keys are local keys, not qualified ones, because circular reference between modules is forbidden so that could never happen
//type ConstraintAccumulatorMap = Map<LowerIdent,    >



/// Make a new unification variable
let private makeNewUniVar () = System.Guid.NewGuid () |> UnificationVarId

/// Make a new type variable
let private makeNewTypeVar () = System.Guid.NewGuid () |> TypeVariableId


/// A recursive dependency group
type RecursiveDepGroup =
    {
        //namesDependedOn : LowerIdent nel
        //ownName : LowerIdent
        //expr : D.Expr
        namesAndExprs : (LowerIdent * D.Expr) nel
        /// Self explanatory: there could be expressions who themselves are not recursive or part of a recursive graph but depend on one or more of the names that *are* recursive
        expressionsDependentOnThisGroup : (LowerIdent * D.Expr) seq
    }

type AllRecursiveDepGroups =
    { groups : RecursiveDepGroup seq
      exprsDependentOnMultipleGroups : (LowerIdent * D.Expr) seq }


/// This is the result of running the 1st type inference strategy: the one that is more powerful because it can infer polytypes, but less flexible because it can't deal with recursively defined names, only those names whose types are annotated explicitly or whose types can be inferred by simply resolving the names in order of which depends on which
type SimpleTypeInferenceResult =
    {
        /// After dependency resolution, here are all the fully resolved and typed expressions that we could type purely by tackling those values 1) which have explicit type annotations 2) whose types can be inferred without needing to resolve the type of any other named value 3) whose types only depend on the types of names we have already typed
        typedNames : TypedLocalNamesMap
        /// Now here is the list of names whose types cannot be inferred simply because their type depends either on their own name (f referencing f) or it depends on the type of another name whose type depends on itself (f referencing g referencing f again)
        recursiveDepsGroups : AllRecursiveDepGroups
    }



/// Gets all the value names referenced in an expression – note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because as far as the higher scopes are concerned those names do not exist.
/// @TODO: this should probably fail for shadowed names, but we'll assume for now that there are no shadowed names
let rec getNamesUsedInExpr (namesToLookOutFor : LowerIdent set) (expr : D.Expr) : LowerIdent set =
    match expr with
    | D.StrVal _ -> Set.empty
    | D.IntVal _ -> Set.empty
    | D.ListVal exprs -> Set.collect (getNamesUsedInExpr namesToLookOutFor) exprs
    | D.TupleVal (first, second) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor first) (getNamesUsedInExpr namesToLookOutFor second)

    | D.LambdaVal (_, body) -> getNamesUsedInExpr namesToLookOutFor body
    | D.NamedVal name ->
        if Set.contains name namesToLookOutFor then
            Set.singleton name
        else
            Set.empty

    | D.LetBindings (bindings, body) ->
        Set.union
            (getNamesUsedInExpr namesToLookOutFor body)
            (bindings
             |> Seq.map (_.assignedExpr >> getNamesUsedInExpr namesToLookOutFor)
             |> Set.unionMany)

    | D.FuncApplication (funcExpr, inputExpr) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor funcExpr) (getNamesUsedInExpr namesToLookOutFor inputExpr)



/// Given a list of names and their assigned expressions, constructs a list of groups of
let constructRecursiveDependencyGraph
    (namesMap : TypedNamesMap)
    (namesAndExprs : (LowerIdent * D.Expr) seq)
    : AllRecursiveDepGroups =
    ()




/// Add a local names map to a global one
let addLocalNamesMap (localNamesMap : TypedLocalNamesMap) (namesMap : TypedNamesMap) : TypedNamesMap =
    localNamesMap
    |> Map.mapKeyVal (fun key v -> LocalLower key, v)
    // @TODO: this should really throw an error if there are any name clashes so we don't get silently overwritten names
    |> Map.merge namesMap



let combineTwoLocalNamesMaps (map1 : TypedLocalNamesMap) (map2 : TypedLocalNamesMap) : TypedLocalNamesMap =
    // @TODO: this should really throw an error if there are any name clashes so we don't get silently overwritten names
    Map.merge map1 map2

let combineMultipleLocalnamesMaps (maps : TypedLocalNamesMap seq) : TypedLocalNamesMap =
    maps |> Seq.fold combineTwoLocalNamesMaps Map.empty


/// Given a list of names and their assigned expressions, this resolves all the names that either have type annotations or that are not recursively defined.
/// It returns the context map of names with their resolved types and returns the list of which names could not yet be resolved either because they are recursively defined, or because they rely on recursively defined names.
let rec resolveAllResolvableNames
    (namesMap : TypedNamesMap)
    (namesAndExprs : D.LetBindingSingle seq)
    : TypedLocalNamesMap * (LowerIdent * D.Expr) seq =
    /// These don't need to be inferred because they already have explicit type annotations.
    /// @TODO: however! we still need to type check them internally
    let namesWithTypeAnnotations : TypedLocalNamesMap =
        namesAndExprs
        |> Seq.choose (fun binding -> binding.typeAnnotation |> Option.map (Tuple.makePair binding.name))
        |> Map.ofSeq

    /// This is the inner recursive function that goes through all the expressions that don't rely on any untyped-yet names and resolves their types.
    /// How do we know when we've exhausted all available expressions and we've hit some islands of recursive values? I suppose if there is no difference between the results of the last run and the next one. Then that gives us a single list of all unresolvable names, but we then still have to group them into mutually recursive groups.
    let rec resolveNamesOfAvailable
        (globalNamesMap : TypedNamesMap)
        (* The accumulatingNamesMap is the new stuff that we're learning about and adding onto with each run of the recursive function *)
        (accumulatingNamesMap : TypedLocalNamesMap)
        (* This should actually be empty, we're only including this for the sake of correctness, to make sure we're never gathering constraints on names we have not seen defined yet, because at this stage of the type resolution process we don't deal with those yet *)
        (accumulatingUnificationVarMap : UnificationVarsMap)
        (namesAndExprsToResolveStill : (LowerIdent * D.Expr) seq)
        : TypedLocalNamesMap * (LowerIdent * D.Expr) seq * UnificationVarsMap =

        match Seq.toList namesAndExprsToResolveStill with
        | [] -> accumulatingNamesMap, Seq.empty, accumulatingUnificationVarMap
        | toResolve ->
            let combinedNamesMap = addLocalNamesMap accumulatingNamesMap globalNamesMap

            let currentNames = namesAndExprsToResolveStill |> Seq.map fst |> Set.ofSeq

            let namesAvailableForResolution, nameNotAvailableForResolution =
                toResolve
                |> List.typedPartition (fun (name, expr) ->
                    let nameDeps = getNamesUsedInExpr currentNames expr

                    if Set.isEmpty nameDeps then
                        /// This expression doesn't reference any names full stop so it's ready for type checking
                        Choice1Of2 (name, expr)

                    else
                        let notYetResolvedNameDeps =
                            nameDeps
                            |> Set.toList
                            |> List.filter (fun name -> Map.containsKey (LocalLower name) combinedNamesMap |> not)
                            |> Set.ofList

                        if Set.isEmpty notYetResolvedNameDeps then
                            // Everything required has been resolved, so ready for type checking!
                            Choice1Of2 (name, expr)

                        else
                            // This expression has at least one reference to a not-yet-typed name, so it's not ready for checking yet
                            Choice2Of2 (name, expr))

            match namesAvailableForResolution with
            | [] ->
                // We can't make any progress so we must've hit some (mutually) recursively defined names – although bear in mind that this could include some values that depend on the recursively defined names but are not themselves recursive or part of a recursive group!
                accumulatingNamesMap, nameNotAvailableForResolution, accumulatingUnificationVarMap

            | _ ->
                let inferredStuff : (LowerIdent * SelfAndConstrainedUnificationVars) list =
                    namesAvailableForResolution
                    |> List.map (fun (name, expr) -> name, inferTypeFromExpr globalNamesMap expr)


                let newlyGleanedNamesMap : TypedLocalNamesMap =
                    inferredStuff
                    |> List.map (fun (name, result) -> name, result.self)
                    |> Map.ofList

                let combinedNewlyGleanedMap : TypedLocalNamesMap =
                    combineTwoLocalNamesMaps newlyGleanedNamesMap accumulatingNamesMap

                let combinedUnificationVarMap : UnificationVarsMap =
                    inferredStuff
                    |> List.map (fun (_, result) -> result.constrained)
                    |> combineUnificationVarMapsList
                    |> combineTwoUnificationVarMaps accumulatingUnificationVarMap

                resolveNamesOfAvailable
                    globalNamesMap
                    combinedNewlyGleanedMap
                    combinedUnificationVarMap
                    nameNotAvailableForResolution


    let gleanedLocalNamesMap, unresolvedBindings, unificationVarMap =
        namesAndExprs
        |> Seq.map (fun binding -> binding.name, binding.assignedExpr)
        |> resolveNamesOfAvailable namesMap namesWithTypeAnnotations Map.empty

    if Map.isEmpty unificationVarMap then
        gleanedLocalNamesMap, unresolvedBindings
    else
        // We should not have come across any any names that are not fully typed at this stage, so this indicates that something has gone wrong
        failwith
            $"{Map.count unificationVarMap} unification variables were seen during the first pass stage of resolving only definitive typed values, which should not be possible"




///// This is stage one of the type inference/resolution algorithm, it gets all available type annotations, infers the types of named values that don't depend on any others, and loops through so that every non-recursive definition is typed.
///// Then what we're left with are the recursive groups which need to be resolved with unification variables. Then those values that depend on the recursive groups can be inferred with the whole algorithm again.
//and resolveSimpleInference
//    (namesMap : TypedNamesMap)
//    (letBindings : D.LetBindingSingle seq)
//    : SimpleTypeInferenceResult =
//    let simpleResults, recursivelyDefinedNameVals =
//        resolveAllResolvableNames namesMap letBindings

//    let combinedNamesMap = addLocalNamesMap simpleResults namesMap

//    { typedNames = simpleResults
//      recursiveDepsGroups = constructRecursiveDependencyGraph combinedNamesMap recursivelyDefinedNameVals }




/// Which entails generalising those unification vars with no constraints and converting them to polytypes, and just concretising everything else – but ofc only for those names and unification vars that are from the current let bindings, not just all of them willy nilly.
and convertUnificationResultsToNormalTypes
    //(namesMap : TypedNamesMap)
    //(localNames : LowerIdent set)
    (localUnificationVars : UnificationVarId set)
    (unificationResult : UnificationVarsMap)
    (typeToCleanUpAndReturn : PolyType_)
    //: TypedLocalNamesMap =
    : SelfAndConstrainedUnificationVars =
    // @TODO: we need to figure out what we want from this function first.
    // I think we want it to do a few things:
    // 1. generalise all the unification vars that are not constrained
    // 2. concretise all the unification vars that are constrained
    // 3. remove all the above unification vars with their concrete types (whether poly or monomorphic) and put their concrete types in the return type
    //
    // – However! we need to decide whether we want this stuff to happen before or after we've inferred stuff from the let expression body, because we still need to be able to glean constraints from the body to the unification variables
    //      – Hm I actually think this should only run after inferring the body, because it's only then that we have all the relevant information, the body is not more special than any other let binding expression body in what it can tell us. So we should just infer the body as normal, and only *then* run this function on the results of that body inference along with everything else, and *then* we can concretise and generalise and shit
    // – So we also still need to decide how we're going to bubble up type errors to higher scopes, seeing as the names and unification variables are removed from being present at higher scopes than they are defined in
    //
    // 4. after swapping out all the concretised and generalised unification variables, replace the value of the things referencing those unification vars from the type to return, and *then* return that sanitised, concretised, and generalised return type from this function ✨

    ()




///// Given only the uniVarIds in the current uniVarsMap, for each of them: check if there are constraints on it. If yes, replace it with the concrete type in the localNamesMap. If not, generalise it so that it is replaced with a new type variable.
///// Then what this function actually returns is a map with the replacements ־ which tbh I think can just be: if Some, replace the option with the thing. If None, replace the option with a new type variable.
//and generaliseUnificationVars
//    (uniVarsMapToConcretiseOrGeneralise : UnificationVarsMap)
//    : Map<UnificationVarId, PolyTypeContents_> =
//    uniVarsMapToConcretiseOrGeneralise
//    |> Map.map (fun _ v ->
//        match v with
//        | Some concrete -> concrete
//        | None -> PolyTypeContents_.TypeVariable (makeNewTypeVar ()))

/////// I *believe* that this is equivalent to... generalising the thing..! But only for those unification vars that are not constrained
////and stripNamesAndUniVarsFromPolyTypeContents (uniVarsMap : UnificationVarsMap) (toSwap: Map<UnificationVarId, PolyTypeContents_>)   (polyTypeContents : PolyTypeContents_) : PolyTypeContents_ = ()
////    //match polyTypeContents with
////    //| PolyTypeContents_.UnificationVar uniVar ->
////    //    match Map.tryFind uniVar uniVarsMap with
////    //    | Some constraints ->
////    //    | None ->
////    //        PolyTypeContents_.TypeVariable typeVarId


//and stripNamesAndUniVarsFromPolyType
//    (uniVarsMap : UnificationVarsMap)
//    (uniVarsToStrip : UnificationVarId set)
//    (polyType : PolyType_)
//    : PolyType_ =
//    ()




/// This returns the fully resolved map of let (and top-level, I suppose) bindings, along with the constraints on unification variables.
///
/// Since in a let bindings expression there can still be more constraints on unification variables, we need the unification variables map to be returned as well, and combine it with the uniVarsMap that we'll return from the body of the let bindings expression, and only _then_ apply those constraints from the unification variables to those names that still only have unification variables assigned to them and not concrete polytypes. But tbh that last part shouldn't require anything more specific or specialised than just unifying the final combined unification vars map with the local names map (also returned from this function), and then concretise the unification vars – and generalise where possible! – into the namesMap.
///
/// @TODO: on second thought, I think it makes more sense to encapsulate the unifying of all the constraints and shit in a dedicated function rather than in the inferTypeExpr function which does a bunch of other stuff also
and resolveAllNames
    (namesMap : TypedNamesMap)
    (letBindings : D.LetBindingSingle seq)
    //(body : D.Expr)
    : TypedLocalNamesMap * UnificationVarsMap =
    //and resolveAllNames (namesMap : TypedNamesMap) (letBindings : D.LetBindingSingle seq) (body : D.Expr) : TypedLocalNamesMap * UnificationVarsMap =
    let makeSingleLetBinding name expr =
        { D.LetBindingSingle.name = name
          D.LetBindingSingle.assignedExpr = expr
          D.LetBindingSingle.typeAnnotation = None }


    let straightforwardlyResolvedNamesMap, recursivelyDefinedNameVals =
        resolveAllResolvableNames namesMap letBindings

    let namesMapAfterFirstPass : TypedNamesMap =
        addLocalNamesMap straightforwardlyResolvedNamesMap namesMap

    let recursiveGroups : AllRecursiveDepGroups =
        constructRecursiveDependencyGraph namesMapAfterFirstPass recursivelyDefinedNameVals


    let resolvedFirstRecursiveGroupsInParallel =
        recursiveGroups.groups
        |> Seq.map (fun group ->
            let nameUniVarAndExprs =
                group.namesAndExprs
                |> NEL.map (fun (name, expr) -> name, makeNewUniVar (), expr)

            let nameToUniVarMap =
                nameUniVarAndExprs
                |> NEL.map (fun (name, uniVar, _) -> name, uniVar)
                |> Map.ofSeq

            let withUnificationVarsAssigned : TypedLocalNamesMap =
                nameToUniVarMap
                |> Map.map (fun _ uniVarId -> PolyTypeContents_.UnificationVar uniVarId |> D.makeEmptyPolyType)

            let addedToMap = addLocalNamesMap withUnificationVarsAssigned namesMapAfterFirstPass

            let groupResult =
                nameUniVarAndExprs
                |> NEL.map (fun (name, uniVar, expr) -> name, uniVar, inferTypeFromExpr addedToMap expr)

            {| results =
                groupResult
                |> NEL.map (fun (name, uniVar, result) ->
                    {| name = name
                       uniVar = uniVar
                       type_ = result.self
                       constrained = result.constrained |})
               dependentExprs = group.expressionsDependentOnThisGroup |})


    /// Now we resolve those expressions that were dependent on the recursive groups, using this same function recursively
    let fullyResolvedGroups : (TypedLocalNamesMap * UnificationVarsMap) seq =
        resolvedFirstRecursiveGroupsInParallel
        |> Seq.map (fun groupResults ->
            let combinedUniVarMap =
                groupResults.results |> NEL.map _.constrained |> combineUnificationVarMapsList

            let combinedNamesMap =
                groupResults.results
                |> NEL.fold
                    (fun state result -> Map.add (LocalLower result.name) result.type_ state)
                    namesMapAfterFirstPass

            let resolvedLocalNamesMap, newUniVarMap =
                groupResults.dependentExprs
                |> Seq.map (fun (name, expr) -> makeSingleLetBinding name expr)
                |> resolveAllNames combinedNamesMap

            resolvedLocalNamesMap, combineTwoUnificationVarMaps combinedUniVarMap newUniVarMap)

    /// And now we resolve those bindings that were dependent on multiple recursive groups
    let remainingBindings =
        let combinedNamesMap =
            fullyResolvedGroups
            |> Seq.map fst
            |> Seq.fold (fun state localMap -> addLocalNamesMap localMap state) namesMapAfterFirstPass

        recursiveGroups.exprsDependentOnMultipleGroups
        |> Seq.map (fun (name, expr) -> makeSingleLetBinding name expr)
        |> resolveAllNames combinedNamesMap

    /// Combine *all* the localnamesmaps from above, including lists of lists and shit
    let combinedLocalNamesMap : TypedLocalNamesMap =
        combineMultipleLocalnamesMaps (
            straightforwardlyResolvedNamesMap
            :: fst remainingBindings
            :: (Seq.map fst fullyResolvedGroups |> Seq.toList)
        )

    /// Combine *all* the unificationvarmaps from above, including lists of lists and shit
    let combinedUnificationVarsMap : UnificationVarsMap =
        (snd remainingBindings
         :: (resolvedFirstRecursiveGroupsInParallel
             |> Seq.collect _.results
             |> Seq.map _.constrained
             |> Seq.toList)
         @ (Seq.map snd fullyResolvedGroups |> Seq.toList))
        |> combineUnificationVarMapsList

    combinedLocalNamesMap, combinedUnificationVarsMap

//let resolvedFromBody = inferTypeFromExpr combinedNamesMap body

//let combinedUnificationVarMap =
//    resolvedFirstRecursiveGroupsInParallel
//    |> Seq.map _.unificationVarsMap
//    |> combineUnificationVarMapsList
//    |> combineTwoUnificationVarMaps resolvedFromBody.constrained

//resolvedFirstRecursiveGroupsInParallel
//|> Seq.map (fun group -> group.dependentExprs)


//let recursiveGroupsResults =
//    recursiveGroups |> Seq.map (resolveInsideOutInference combinedNamesMap)

//let allResults =
//    recursiveGroupsResults
//    |> Seq.map (convertUnificationResultsToNormalTypes combinedNamesMap)

//allResults |> Seq.fold addLocalNamesMap Map.empty


/// @TODO: I think in this function is where I need to strip the names and unification vars initialised here from the polytype and unification vars map that we return
and resolveAllNamesAndBody
    (namesMap : TypedNamesMap)
    (letBindings : D.LetBindingSingle seq)
    (body : D.Expr)
    : SelfAndConstrainedUnificationVars =
    let bindingsNamesMap, uniVarsMap = resolveAllNames namesMap letBindings

    let combinedNamesMap = addLocalNamesMap bindingsNamesMap namesMap

    let bodyResult = inferTypeFromExpr combinedNamesMap body

    let combinedUniVarMap =
        combineTwoUnificationVarMaps uniVarsMap bodyResult.constrained

    let sanitisedType =
        convertUnificationResultsToNormalTypes (Map.keys uniVarsMap |> Set.ofSeq) combinedUniVarMap bodyResult.self

    sanitisedType







and inferTypeFromExpr (namesMap : TypedNamesMap) (expr : D.Expr) : SelfAndConstrainedUnificationVars =
    match expr with
    | D.StrVal _ -> Sacuv.make (D.makeEmptyPolyType D.strType) Map.empty
    | D.IntVal _ -> Sacuv.make (D.makeEmptyPolyType D.intType) Map.empty
    | D.ListVal exprs ->
        match exprs with
        | [] -> Sacuv.make D.listType Map.empty
        | only :: [] ->
            let contentType = inferTypeFromExpr namesMap only
            Sacuv.make (D.listTypeOf contentType.self) contentType.constrained

        | head :: rest ->
            let inferred = NEL.map (inferTypeFromExpr namesMap) (NEL.new_ head rest)

            let combinedUniMap =
                inferred |> NEL.map _.constrained |> combineUnificationVarMapsList

            let unified = inferred |> NEL.map _.self |> unifyManyTypes

            combineTwoUnificationVarMaps combinedUniMap unified.constrained
            |> Sacuv.make (D.listTypeOf unified.self)

    | D.TupleVal (first, second) ->
        let inferredFirst = inferTypeFromExpr namesMap first
        let inferredSecond = inferTypeFromExpr namesMap second

        let uniMap =
            combineTwoUnificationVarMaps inferredFirst.constrained inferredSecond.constrained

        Sacuv.make (D.tupleTypeOf inferredFirst.self inferredSecond.self) uniMap

    | D.LambdaVal (param, body) ->
        /// Make a new unification variable to act as the input parameter for the lambda
        let paramPolyType =
            PolyTypeContents_.UnificationVar (makeNewUniVar ()) |> D.makeEmptyPolyType

        /// Add the new name with its unification variable type into the names map that we inject into the body inferencing function
        let withNewUnificationVarAddedForParam =
            Map.add (LocalLower param) paramPolyType namesMap

        let bodyInferenceResult = inferTypeFromExpr withNewUnificationVarAddedForParam body

        bodyInferenceResult.constrained
        // @TODO: do we need to be generalising the function type if the unification vars are unconstrained?
        // @TODO: 2nd question: *how* do we generalise that then lol? I *think* we do that by replacing constrained unification vars with normal concrete type shapes, and replace them with new "type variables"
        // @TODO: I was thinking that maybe we can just do that by wrapping this function on the outside and doing this replacement automatically for all unification vars, but I don't think I can do that actually because I think there's no way to know in general if said unification vars are present outside of the current scope or not; so we might need to generalise them in those places where we brought them into the world!
        |> Sacuv.make (D.funcTypeOf paramPolyType bodyInferenceResult.self)

    | D.NamedVal name ->
        match Map.tryFind (LocalLower name) namesMap with
        | Some t -> Sacuv.make t Map.empty
        | None ->
            failwith
                $"Couldn't resolve named value \"{name}\"! This is most likely due to it being an undeclared variable (which @TODO we still need to handle gracefully) but if not it might indicate that we're not passing all declared names down in the namesMap"


    | D.LetBindings (bindings, body) -> resolveAllNamesAndBody namesMap bindings body


    | D.FuncApplication (funcExpr, param) ->
        let paramTypeResult = inferTypeFromExpr namesMap param

        let returnType =
            makeNewUniVar () |> PolyTypeContents_.UnificationVar |> D.makeEmptyPolyType

        let inferredFuncResult = inferTypeFromExpr namesMap funcExpr

        let funcRequiredType = D.funcTypeOf paramTypeResult.self returnType
        let funcRequiredResult = unifyTwoTypes funcRequiredType inferredFuncResult.self

        let combinedUnifVarMap =
            [ paramTypeResult.constrained
              inferredFuncResult.constrained
              funcRequiredResult.constrained ]
            |> combineUnificationVarMapsList

        Sacuv.make returnType combinedUnifVarMap





and unifyTwoTypes (type1 : PolyType_) (type2 : PolyType_) : SelfAndConstrainedUnificationVars = ()




and unifyTwoTypeContents
    (type1 : PolyTypeContents_)
    (type2 : PolyTypeContents_)
    : {| self : Result<PolyTypeContents_, UnificationError>
         constrained : UnificationVarsMap |}
    =
    match type1, type2 with
    | PTC.PrimitiveType prim1, PTC.PrimitiveType prim2 ->
        if prim1 = prim2 then
            {| self = Ok type1
               constrained = Map.empty |}

        else
            {| self = UnificationClash (type1, type2) |> Error
               constrained = Map.empty |}


    | PTC.ParametricType (name1, typeParams1), PTC.ParametricType (name2, typeParams2) ->
        if name1 = name2 then
            match List.zipList typeParams1 typeParams2 with
            | Ok combinedTypeParams ->
                let paramsResults, unificationVarMap =
                    combinedTypeParams
                    |> List.mapFold
                        (fun state (param1, param2) ->
                            let unificationResult = unifyTwoTypeContents param1 param2

                            unificationResult.self, combineTwoUnificationVarMaps state unificationResult.constrained)
                        Map.empty

                match Result.sequenceList paramsResults with
                | Ok unifiedParams ->
                    {| self = Ok (PTC.ParametricType (name1, unifiedParams))
                       constrained = unificationVarMap |}

                | Error errs ->
                    {| self = NEL.head errs |> Error
                       constrained = unificationVarMap |}

            | Error _ ->
                {| self = UnificationClash (type1, type2) |> Error
                   constrained = Map.empty |}

        else
            {| self = UnificationClash (type1, type2) |> Error
               constrained = Map.empty |}


    | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
        if uniVar1 = uniVar2 then
            {| self = Ok type1
               constrained = Map.empty |}

        else
            /// Just so we have a consistent ordering so we avoid accidentally creating cycles of unification vars that don't lead anywhere
            let smallerUniVar, biggerUniVar = sortItems uniVar1 uniVar2

            /// The logic here being that we redirect one unification var to the other one. By convention we make the self type be the smaller uniVar, add an entry in the unification map to point it to the bigger one.
            /// The bigger one will keep pointing to whatever it's pointing to in other unification maps, and the smaller one in other maps will be unified with the bigger one, which will result in unifying the bigger one with a concrete type.
            let constrained : UnificationVarsMap =
                Map.singleton smallerUniVar (PTC.UnificationVar biggerUniVar |> Ok |> Some)

            {| self = Ok (PTC.UnificationVar smallerUniVar)
               constrained = constrained |}


    | PTC.TypeVariable typeVar1, PTC.TypeVariable typeVar2 ->
        if typeVar1 = typeVar2 then
            {| self = Ok type1
               constrained = Map.empty |}

        else
            let newUnificationVar1 = makeNewUniVar ()
            let newUnificationVar2 = makeNewUniVar ()

            // @TODO: I'm not sure this is remotely right... are there any risks or assumptions violated by having a circular reference from uniVar to typeVar to uniVar to typeVar like this?
            let uniVarsMap : UnificationVarsMap =
                Map.singleton
                    newUnificationVar1
                    (PTC.InstantiatedTypeVariable (typeVar1, newUnificationVar2) |> Ok |> Some)
                |> Map.add
                    newUnificationVar2
                    (PTC.InstantiatedTypeVariable (typeVar2, newUnificationVar1) |> Ok |> Some)

            ///// We point both type variables to the freshly instantiated unification var
            //let substitutionMap : SubstitutedTypeVars =
            //    Map.singleton typeVar1 newUnificationVar |> Map.add typeVar2 newUnificationVar

            //let constrained : Constraineds = Constraineds.make uniVarsMap substitutionMap

            {| self = Ok (PTC.UnificationVar newUnificationVar1)
               constrained = uniVarsMap |}


    | PTC.UnificationVar uniVar, PTC.PrimitiveType prim
    | PTC.PrimitiveType prim, PTC.UnificationVar uniVar ->
        let uniVarsMap : UnificationVarsMap =
            Map.singleton uniVar (PTC.PrimitiveType prim |> Ok |> Some)

        {| self = Ok (PTC.UnificationVar uniVar)
           constrained = uniVarsMap |}


    | PTC.UnificationVar uniVar, PTC.ParametricType (name, typeParams)
    | PTC.ParametricType (name, typeParams), PTC.UnificationVar uniVar ->
        let uniVarsMap : UnificationVarsMap =
            Map.singleton uniVar (Ok (PTC.ParametricType (name, typeParams)) |> Some)

        {| self = Ok (PTC.UnificationVar uniVar)
           constrained = uniVarsMap |}


    | PTC.UnificationVar uniVar, PTC.TypeVariable typeVar
    | PTC.TypeVariable typeVar, PTC.UnificationVar uniVar ->
        {| self = Ok (PTC.InstantiatedTypeVariable (typeVar, uniVar))
           constrained = Map.empty |}


    | PTC.TypeVariable typeVar, (PTC.PrimitiveType _ as concreteType)
    | (PTC.PrimitiveType _ as concreteType), PTC.TypeVariable typeVar

    | PTC.TypeVariable typeVar, (PTC.ParametricType _ as concreteType)
    | (PTC.ParametricType _ as concreteType), PTC.TypeVariable typeVar ->
        let newUnificationVar = makeNewUniVar ()

        /// Insert the fresh unification var into the unification var map
        let uniVarsMap : UnificationVarsMap =
            Map.singleton newUnificationVar (Some (Ok concreteType))

        {| self = Ok (PTC.InstantiatedTypeVariable (typeVar, newUnificationVar))
           constrained = uniVarsMap |}


    | PTC.PrimitiveType _, PTC.ParametricType _
    | PTC.ParametricType _, PTC.PrimitiveType _ ->
        {| self = UnificationClash (type1, type2) |> Error
           constrained = Map.empty |}


    | PTC.InstantiatedTypeVariable (typeVar1, uniVar1), PTC.InstantiatedTypeVariable (typeVar2, uniVar2) ->
        if typeVar1 = typeVar2 then
            if uniVar1 = uniVar2 then
                {| self = Ok type1
                   constrained = Map.empty |}
            else
                let uniVarMap : UnificationVarsMap =
                    Map.singleton uniVar1 (PTC.InstantiatedTypeVariable (typeVar1, uniVar2) |> Ok |> Some)

                {| self = Ok (PTC.UnificationVar uniVar1)
                   constrained = uniVarMap |}
        else if uniVar1 = uniVar2 then
            {| self = Ok (PTC.UnificationVar uniVar1)
               constrained =
                Map.singleton
                    uniVar1
                    (PTC.InstantiatedTypeVariable (NEL.append typeVar1 typeVar2, uniVar2)
                     |> Ok
                     |> Some) |}
        else
            let uniVarsMap : UnificationVarsMap =
                Map.singleton
                    uniVar1
                    (PTC.InstantiatedTypeVariable (NEL.append typeVar1 typeVar2, uniVar2)
                     |> Ok
                     |> Some)
                |> Map.add uniVar2 None

            {| self = Ok (PTC.UnificationVar uniVar1)
               constrained = uniVarsMap |}

    | PTC.InstantiatedTypeVariable (typeVarNel, uniVar1), PTC.TypeVariable typeVar
    | PTC.TypeVariable typeVar, PTC.InstantiatedTypeVariable (typeVarNel, uniVar1) ->
        if NEL.contains<_> typeVar typeVarNel then
            {| self = Ok (PTC.InstantiatedTypeVariable (typeVarNel, uniVar1))
               constrained = Map.empty |}

        else
            {| self = Ok (PTC.InstantiatedTypeVariable (NEL.cons typeVar typeVarNel, uniVar1))
               constrained = Map.empty |}


    | PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar), PTC.UnificationVar uniVar
    | PTC.UnificationVar uniVar, PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar) ->
        {| self = Ok (PTC.UnificationVar uniVar)
           constrained =
            Map.singleton uniVar (PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar) |> Ok |> Some) |}


    | PTC.InstantiatedTypeVariable (_, uniVar), (PTC.PrimitiveType _ as concreteType)
    | (PTC.PrimitiveType _ as concreteType), PTC.InstantiatedTypeVariable (_, uniVar)

    | PTC.InstantiatedTypeVariable (_, uniVar), (PTC.ParametricType _ as concreteType)
    | (PTC.ParametricType _ as concreteType), PTC.InstantiatedTypeVariable (_, uniVar) ->

        {| self = Ok (PTC.UnificationVar uniVar)
           constrained = Map.singleton uniVar (Ok concreteType |> Some) |}




and unifyTwoTypeContentsResults
    (typeContentResult1 : Result<PolyTypeContents_, UnificationError>)
    (typeContentResult2 : Result<PolyTypeContents_, UnificationError>)
    : {| self : Result<PolyTypeContents_, UnificationError>
         constrained : UnificationVarsMap |}
    =
    match typeContentResult1, typeContentResult2 with
    | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents typeContent1 typeContent2

    | Error e, _
    | _, Error e ->
        {| self = Error e
           constrained = Map.empty |}



and unifyTwoTypeContentsResultsOpts
    (typeOpt1 : Result<PolyTypeContents_, UnificationError> option)
    (typeOpt2 : Result<PolyTypeContents_, UnificationError> option)
    : {| self : Result<PolyTypeContents_, UnificationError> option
         constrained : UnificationVarsMap |}
    =
    match typeOpt1, typeOpt2 with
    | Some type1, Some type2 ->
        let result = unifyTwoTypeContentsResults type1 type2

        {| self = Some result.self
           constrained = result.constrained |}

    | Some type_, None
    | None, Some type_ ->
        {| self = Some type_
           constrained = Map.empty |}

    | None, None ->
        {| self = None
           constrained = Map.empty |}

and unifyTwoTypeContentsOpts
    (typeOpt1 : PolyTypeContents_ option)
    (typeOpt2 : PolyTypeContents_ option)
    : {| self : Result<PolyTypeContents_, UnificationError> option
         constrained : UnificationVarsMap |}
    =
    match typeOpt1, typeOpt2 with
    | Some type1, Some type2 ->
        let result = unifyTwoTypeContents type1 type2

        {| self = Some result.self
           constrained = result.constrained |}

    | None, None ->
        {| self = None
           constrained = Map.empty |}

    | Some type_, None
    | None, Some type_ ->
        {| self = Some (Ok type_)
           constrained = Map.empty |}



and unifyManyTypes (types : PolyType_ nel) : SelfAndConstrainedUnificationVars =
    let (NEL (first, rest)) = types

    let combinedType, combinedUnificationMap =
        rest
        |> List.fold
            (fun (combinedType, combinedUniMap) polyType ->
                let result = unifyTwoTypes combinedType polyType
                result.self, combineTwoUnificationVarMaps combinedUniMap result.constrained)
            (first, Map.empty)

    { self = combinedType
      constrained = combinedUnificationMap }


and combineTwoUnificationVarMaps (map1 : UnificationVarsMap) (map2 : UnificationVarsMap) : UnificationVarsMap =
    /// For those keys which are not shared, just simply add them in
    let singleFolder state uniVar contents = Map.add uniVar contents state

    let folder (state : UnificationVarsMap) (uniVar : UnificationVarId) contents1 contents2 : UnificationVarsMap =
        let unificationResult = unifyTwoTypeContentsResultsOpts contents1 contents2

        // Add the immediate resulting type into the map first
        let directCombinedMap : UnificationVarsMap =
            Map.add uniVar unificationResult.self state

        // And then recursively fold in the other unification map containing the implications of the unification also
        let bothCombined : UnificationVarsMap =
            combineTwoUnificationVarMaps directCombinedMap unificationResult.constrained

        bothCombined


    Map.foldAllEntries singleFolder singleFolder folder map1 map2 Map.empty




and combineUnificationVarMapsList (maps : UnificationVarsMap seq) : UnificationVarsMap =
    maps |> Seq.fold combineTwoUnificationVarMaps Map.empty





//and combineTwoSubstitutedTypeVarMaps (map1 : SubstitutedTypeVars) (map2 : SubstitutedTypeVars) : Constraineds =
//    /// For those type vars which are not shared, just simply add them in
//    let singleFolder (state : Constraineds) typeVar uniVar : Constraineds =
//        { substitutedTypeVars = Map.add typeVar uniVar state.substitutedTypeVars
//          unificationVarsMap = state.unificationVarsMap }


//    let folder
//        (state : Constraineds)
//        (typeVar : TypeVariableId)
//        (uniVar1 : UnificationVarId)
//        (uniVar2 : UnificationVarId)
//        : Constraineds =

//        /// Just so we have a consistent ordering so we avoid accidentally creating cycles of unification vars that don't lead anywhere
//        let smallerUniVar, biggerUniVar = sortItems uniVar1 uniVar2

//        let newSubstitutedTypeVars : SubstitutedTypeVars =
//            state.substitutedTypeVars |> Map.add typeVar smallerUniVar

//        let newUniVarsMap : UnificationVarsMap =
//            match Map.tryFind smallerUniVar state.unificationVarsMap with
//            | Some _ ->
//                failwith
//                    "Unification variable already exists in the accumulated uniVarsMap and I think it shouldn't? idk, @TODO look into this"
//            | None ->
//                state.unificationVarsMap
//                |> Map.add smallerUniVar (PTC.UnificationVar biggerUniVar |> Some)

//        { unificationVarsMap = newUniVarsMap
//          substitutedTypeVars = newSubstitutedTypeVars }


//    Map.foldAllEntries singleFolder singleFolder folder map1 map2 Constraineds.empty



//and combineTwoInstantiatedTypeVarsMaps
//    (map1 : InstantiatedTypeVars)
//    (map2 : InstantiatedTypeVars)
//    : InstantiatedTypeVars =
//    /// For those keys which are not shared, just simply add them in
//    let singleFolder state typeVar uniVar = Map.add typeVar uniVar state

//    let folder
//        (state : InstantiatedTypeVars)
//        (typeVar : TypeVariableId)
//        (uniVar : UnificationVarId)
//        contents2
//        : InstantiatedTypeVars =
//        let unificationResult = unifyTwoTypeContents uniVar contents2

//        // Add the immediate resulting type into the map first
//        let directCombinedMap = Map.add typeVar unificationResult.self state

//        // And then recursively fold in the other unification map containing the implications of the unification also
//        let bothCombined =
//            combineTwoInstantiatedTypeVarsMaps directCombinedMap unificationResult.constrained

//        bothCombined

//    Map.foldAllEntries singleFolder singleFolder folder map1 map2 Map.empty








































//type ContextAndReturnedType =
//    { returnedType : TypeRefId
//      context : TypeContext }

///// Alias for ContextAndReturnedType
//type CART = ContextAndReturnedType

////let rec f _ = snd (g (), None)

////and g _ =


////let private makeNewRefId () = _.returnedType //System.Guid.NewGuid () |> TypeRefId


//module TypeContext =
//    let empty : TypeContext = Map.empty

//    let addForRef (ref : NameOrReference) (t : TypeInferenceResult) (ctx : TypeContext) =
//        ctx
//        |> Map.add
//            ref
//            (match Map.tryFind ref ctx with
//             | Some results -> NEL.cons t results
//             | None -> NEL.make t)


//    let combine (ctxA : TypeContext) (ctxB : TypeContext) : TypeContext = Map.mergeSafe (always NEL.append) ctxA ctxB

//    let combineMany (ctxs : TypeContext seq) : TypeContext = Seq.fold combine empty ctxs


//module ContextAndReturnedType =
//    let make (typeId : TypeRefId) (ctx : TypeContext) : ContextAndReturnedType =
//        { context = ctx; returnedType = typeId }

//    let insertType (t : TypeInferenceResult) (ctx : TypeContext) : CART =
//        let typeId = makeNewRefId ()

//        TypeContext.addForRef (Reference typeId) t ctx |> make typeId

//    let makeNoContext t = make t TypeContext.empty

//    let getTypeId (cart : CART) : TypeRefId = cart.returnedType

//    let getTypes (cart : CART) : TypeInferenceResult nel =
//        let typeId = getTypeId cart

//        match Map.tryFind (Reference typeId) cart.context with
//        | Some t -> t
//        | None -> failwith $"Couldn't find type at ID {typeId}"

//    let getCtx (cart : CART) : TypeContext = cart.context

//    let combineFromCarts (cartA : CART) (cartB : CART) : TypeContext = TypeContext.combine cartA.context cartB.context

//    let combineManyFromCarts (carts : CART seq) : TypeContext = Seq.map getCtx carts |> TypeContext.combineMany




//module Cart = ContextAndReturnedType
//module Ctx = TypeContext


//let rec gatherUnificationVarsConcrete (concrete : ConcreteType) =
//    match concrete with
//    | ConcUnitType -> Set.empty
//    | ConcPrimType _ -> Set.empty
//    | ConcTuple tom -> Set.collect gatherUnificationVars tom
//    | ConcList t -> gatherUnificationVars t
//    | ConcRecordWith fields
//    | ConcRecordExact fields ->
//        Map.fold (fun set _ fieldType -> Set.union (gatherUnificationVars fieldType) set) Set.empty fields

//    | ConcNewType (_, types) -> Set.collect gatherUnificationVars types
//    | ConcArrow (fromType, toType) -> Set.union (gatherUnificationVars fromType) (gatherUnificationVars toType)

///// This gathers all the (unconstrained!) unification variables in a type. Which means that if we find unification vars a, b, and c in a type, then that means we have a `forall a,b,c. {{expr}}`
//and gatherUnificationVars (type_ : TypeForInference) : UnificationVar set =
//    match type_ with
//    | Concrete concrete -> gatherUnificationVarsConcrete concrete
//    | Named _ -> Set.empty
//    | UnificationVarId var -> Set.singleton var
////| SkolemId skolem -> Set.empty



//let rec gatherUnboundNamesConcrete (concrete : ConcreteType) =
//    match concrete with
//    | ConcUnitType -> Set.empty
//    | ConcPrimType _ -> Set.empty
//    | ConcTuple tom -> Set.collect gatherUnboundNames tom
//    | ConcList t -> gatherUnboundNames t
//    | ConcRecordWith fields
//    | ConcRecordExact fields ->
//        Map.fold (fun set _ fieldType -> Set.union (gatherUnboundNames fieldType) set) Set.empty fields
//    | ConcNewType (_, types) -> Set.collect gatherUnboundNames types
//    | ConcArrow (fromType, toType) -> Set.union (gatherUnboundNames fromType) (gatherUnboundNames toType)

///// Collect all the value names that have not yet been eliminated and thus must exist somewhere outside the current scope
//and gatherUnboundNames (type_ : TypeForInference) : RefValueName set =
//    match type_ with
//    | Concrete concrete -> gatherUnboundNamesConcrete concrete
//    | Named name -> Set.singleton name
//    | UnificationVarId _ -> Set.empty










///// To be clear, unlike the previous approach where unification is _mutative_, this one does not actually combine two types mamish, but leaves the original types unchanged, and only returns the new unified type
/////
///// @TODO: might need to return the list of constrained unification vars and what they've been constrained to, so we can bubble those up and replace the univars in the other places that they need to be
//let rec unifyTwoConcreteTypes
//    (typeA : ConcreteType)
//    (typeB : ConcreteType) (* (ctx : TypeContext) *)
//    : TypeInferenceResult =
//    let makeErr a b = Error (TypeClash (a, b))

//    match typeA, typeB with
//    | ConcUnitType, ConcUnitType -> Cart.insertType (Ok (Concrete ConcUnitType)) ctx
//    | ConcPrimType primA, ConcPrimType primB ->
//        if primA = primB then
//            let result = Ok (Concrete (ConcPrimType primA))
//            Cart.insertType result ctx
//        else
//            Cart.insertType (makeErr typeA typeB) ctx

//    | ConcTuple listA, ConcTuple listB ->
//        let (TOM (headA, neckA, tailA)) = listA
//        let (TOM (headB, neckB, tailB)) = listB

//        let zipped = List.zipList tailA tailB

//        match zipped with
//        | Ok zippedTails ->
//            let unifiedHead = unifyTwoTypes headA headB ctx
//            let unifiedNeck = unifyTwoTypes neckA neckB unifiedHead.context

//            let unifiedTail, unifiedTailCtx =
//                List.mapFold
//                    (fun state (a, b) ->
//                        let result = unifyTwoTypes a b state
//                        result.returnedType, result.context)
//                    unifiedNeck.context
//                    zippedTails

//            let unifiedTom =
//                TOM.new_ unifiedHead.returnedType unifiedNeck.returnedType unifiedTail

//            match unifiedTypesTom with
//            | Ok unifiedTypes -> Cart.insertType (Ok (Concrete (ConcTuple unifiedTypes))) unifiedTailCtx
//            | Error errs -> Cart.insertType (Error (NEL.head errs)) unifiedTailCtx

//        | Error _ -> Cart.insertType (makeErr typeA typeB) ctx




//and unifyTwoTypes (typeA : WithUnresolveds) (typeB : WithUnresolveds) (ctx : TypeContext) : CART =
//    // @TODO: no idea if this is anywhere near correct
//    match typeA, typeB with
//    | Concrete concreteA, Concrete concreteB -> unifyTwoConcreteTypes concreteA concreteB ctx
//    | UnificationVarId var, Concrete concrete
//    | Concrete concrete, UnificationVarId var -> Cart.insertType (Ok (Concrete concrete)) ctx

//    | TypeVarId var, Concrete concrete
//    | Concrete concrete, TypeVarId var -> Cart.insertType (Ok (Concrete concrete)) ctx

//    | Concrete concrete, Named _
//    | Named _, Concrete concrete -> Cart.insertType (Ok (Concrete concrete)) ctx

//    | TypeVarId _, TypeVarId var
//    | Named _, TypeVarId var
//    | UnificationVarId _, TypeVarId var
//    | TypeVarId var, Named _
//    | TypeVarId var, UnificationVarId _ -> Cart.insertType (Ok (TypeVarId var)) ctx

//    | Named _, Named name -> Cart.insertType (Ok (Named name)) ctx

//    | UnificationVarId _, UnificationVarId var -> Cart.insertType (Ok (UnificationVarId var)) ctx
//    | Named _, UnificationVarId var
//    | UnificationVarId var, Named _ -> Cart.insertType (Ok (UnificationVarId var)) ctx


////| ConcList _, ConcList _ ->
////| ConcRecordWith _, ConcRecordWith _ ->
////| ConcRecordExact _, ConcRecordExact _ ->
////| ConcNewType _, ConcNewType _ ->
////| ConcArrow _, ConcArrow _ ->
////| Named _, Named _ ->
////| TypeVar _, TypeVar _ ->











///// Get type information based on a single assignment pattern – named values, destructurings, and so on.
///// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
//let getAccumulatorFromParam (param : AssignmentPattern) : CART = failwith "@TODO: implement"


///// This should: from a binding, derive the type + all the names declared/destructured along with their types in the Accumulator - for use in the let expression body (and of course not outside of it)
//let private getAccumulatorFromBinding (binding : LetBinding) : CART = failwith "@TODO: implement"



//let rec getAccumulatorFromExpr (expr : T.Expression) : CART = ()

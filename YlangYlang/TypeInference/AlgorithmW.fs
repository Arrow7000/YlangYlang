module AlgorithmW


open TypedSyntaxTree
module T = TypedSyntaxTree
open QualifiedSyntaxTree.Names



type TypedNamesMap = Map<LowerNameValue, PolyType>
type TypedLocalNamesMap = Map<LowerIdent, PolyType>

///// The keys are local keys, not qualified ones, because circular reference between modules is forbidden so that could never happen
//type ConstraintAccumulatorMap = Map<LowerIdent,    >





/// A recursive dependency group
type RecursiveDepGroup<'expr> =
    {
        namesDependedOn : LowerIdent nel
        ownName : LowerIdent
        expr : 'expr
        /// Self explanatory: there could be expressions who themselves are not recursive or part of a recursive graph but depend on one or more of the names that *are* recursive
        expressionsDependentOnThisGroup : (LowerNameValue * 'expr) list
    }


/// This is the result of running the 1st type inference strategy: the one that is more powerful because it can infer polytypes, but less flexible because it can't deal with recursively defined names, only those names whose types are annotated explicitly or whose types can be inferred by simply resolving the names in order of which depends on which
type SimpleTypeInferenceResult<'expr> =
    {
        /// After dependency resolution, here are all the fully resolved and typed expressions that we could type purely by tackling those values 1) which have explicit type annotations 2) whose types can be inferred without needing to resolve the type of any other named value 3) whose types only depend on the types of names we have already typed
        typedNames : TypedLocalNamesMap
        /// Now here is the list of names whose types cannot be inferred simply because their type depends either on their own name (f referencing f) or it depends on the type of another name whose type depends on itself (f referencing g referencing f again)
        recursiveDepsGroups : RecursiveDepGroup<'expr> list
    }

let getTypeAnnotation (name : LowerNameValue) (namesMap : TypedNamesMap) : PolyType option = Map.tryFind name namesMap


/// Gets all the value names referenced in an expression
let getNamesFromExpr (expr : 'expr) : LowerNameValue set = failwith "@TODO: implement"

/// I believe... this should only work in let expressions?
let getBindingsInExpr (expr : 'expr) : (LowerIdent * 'expr) list = failwith "@TODO: implement"

let constructRecursiveDependencyGraph
    (namesMap : TypedNamesMap)
    (namesAndExprs : (LowerIdent * 'expr) list)
    : RecursiveDepGroup<'expr> list =
    failwith "@TODO: implement"




/// Add a local names map to a global one
let addLocalNamesMap (localNamesMap : TypedLocalNamesMap) (namesMap : TypedNamesMap) : TypedNamesMap =
    localNamesMap
    |> Map.mapKeyVal (fun key v -> LocalLower key, v)
    |> Map.merge namesMap


let rec resolveAllResolvableNames
    (namesMap : TypedNamesMap)
    (namesAndExprs : (LowerIdent * 'expr) list)
    : TypedLocalNamesMap * (LowerIdent * 'expr) list =
    /// These don't need to be inferred because they already have explicit type annotations.
    /// @TODO: however! we still need to type check them internally
    let namesWithTypeAnnotations : TypedLocalNamesMap =
        namesAndExprs
        |> List.choose (fun (name, expr) ->
            getTypeAnnotation (LocalLower name) namesMap |> Option.map (Tuple.makePair name))
        |> Map.ofList

    /// This is the inner recursive function that goes through all the expressions that don't rely on any untyped-yet names and resolves their types.
    /// How do we know when we've exhausted all available expressions and we've hit some islands of recursive values? I suppose if there is no difference between the results of the last run and the next one. Then that gives us a single list of all unresolvable names, but we then still have to group them into mutually recursive groups.
    let rec resolveNamesOfAvailable
        (globalNamesMap : TypedNamesMap)
        (* The accumulatingNamesMap is the new stuff that we're learning about and adding onto with each run of the recursive function *)
        (accumulatingNamesMap : TypedLocalNamesMap)
        (namesAndExprsToResolveStill : (LowerIdent * 'expr) list)
        : TypedLocalNamesMap * (LowerIdent * 'expr) list =

        match namesAndExprsToResolveStill with
        | [] -> accumulatingNamesMap, List.empty
        | _ ->
            let combinedNamesMap = addLocalNamesMap accumulatingNamesMap globalNamesMap

            let namesAvailableForResolution, nameNotAvailableForResolution =
                namesAndExprsToResolveStill
                |> List.typedPartition (fun (name, expr) ->
                    let nameDeps = getNamesFromExpr expr

                    if Set.isEmpty nameDeps then
                        /// This expression doesn't reference any names full stop so it's ready for type checking
                        Choice1Of2 (name, expr)

                    else
                        let notYetResolvedNameDeps =
                            nameDeps
                            |> Set.toList
                            |> List.filter (fun name -> Map.containsKey name combinedNamesMap |> not)
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
                accumulatingNamesMap, nameNotAvailableForResolution

            | _ ->
                let newlyGleanedMap : TypedLocalNamesMap =
                    namesAvailableForResolution
                    |> List.map (fun (name, expr) -> name, simpleResolver globalNamesMap expr)
                    |> Map.ofList

                let combinedNewlyGleanedMap = Map.merge newlyGleanedMap accumulatingNamesMap

                resolveNamesOfAvailable globalNamesMap combinedNewlyGleanedMap nameNotAvailableForResolution


    resolveNamesOfAvailable namesMap namesWithTypeAnnotations namesAndExprs




and simpleResolver (namesMap : TypedNamesMap) (expr : 'expr) : PolyType = ()










and resolveSimpleInference (namesMap : TypedNamesMap) (expr : 'expr) : SimpleTypeInferenceResult<'expr> =
    let letBindings = getBindingsInExpr expr

    let simpleResults, recursivelyDefinedNameVals =
        resolveAllResolvableNames namesMap letBindings

    let combinedNamesMap = addLocalNamesMap simpleResults namesMap

    { typedNames = simpleResults
      recursiveDepsGroups = constructRecursiveDependencyGraph combinedNamesMap recursivelyDefinedNameVals }




and resolveInsideOutInference
    (namesMap : TypedNamesMap)
    (recursiveGroup : RecursiveDepGroup<'expr>)
    : UnificationVarsContext =
    ()

/// Which entails generalising those unification vars with no constraints and converting them to polytypes, and just concretising everything else
and convertUnificationResultsToNormalTypes
    (namesMap : TypedNamesMap)
    (unificationResult : UnificationVarsContext)
    : TypedLocalNamesMap =
    ()
















































type ContextAndReturnedType =
    { returnedType : TypeRefId
      context : TypeContext }

/// Alias for ContextAndReturnedType
type CART = ContextAndReturnedType

//let rec f _ = snd (g (), None)

//and g _ =


//let private makeNewRefId () = _.returnedType //System.Guid.NewGuid () |> TypeRefId


module TypeContext =
    let empty : TypeContext = Map.empty

    let addForRef (ref : NameOrReference) (t : TypeInferenceResult) (ctx : TypeContext) =
        ctx
        |> Map.add
            ref
            (match Map.tryFind ref ctx with
             | Some results -> NEL.cons t results
             | None -> NEL.make t)


    let combine (ctxA : TypeContext) (ctxB : TypeContext) : TypeContext = Map.mergeSafe (always NEL.append) ctxA ctxB

    let combineMany (ctxs : TypeContext seq) : TypeContext = Seq.fold combine empty ctxs


module ContextAndReturnedType =
    let make (typeId : TypeRefId) (ctx : TypeContext) : ContextAndReturnedType =
        { context = ctx; returnedType = typeId }

    let insertType (t : TypeInferenceResult) (ctx : TypeContext) : CART =
        let typeId = makeNewRefId ()

        TypeContext.addForRef (Reference typeId) t ctx |> make typeId

    let makeNoContext t = make t TypeContext.empty

    let getTypeId (cart : CART) : TypeRefId = cart.returnedType

    let getTypes (cart : CART) : TypeInferenceResult nel =
        let typeId = getTypeId cart

        match Map.tryFind (Reference typeId) cart.context with
        | Some t -> t
        | None -> failwith $"Couldn't find type at ID {typeId}"

    let getCtx (cart : CART) : TypeContext = cart.context

    let combineFromCarts (cartA : CART) (cartB : CART) : TypeContext = TypeContext.combine cartA.context cartB.context

    let combineManyFromCarts (carts : CART seq) : TypeContext = Seq.map getCtx carts |> TypeContext.combineMany




module Cart = ContextAndReturnedType
module Ctx = TypeContext


let rec gatherUnificationVarsConcrete (concrete : ConcreteType) =
    match concrete with
    | ConcUnitType -> Set.empty
    | ConcPrimType _ -> Set.empty
    | ConcTuple tom -> Set.collect gatherUnificationVars tom
    | ConcList t -> gatherUnificationVars t
    | ConcRecordWith fields
    | ConcRecordExact fields ->
        Map.fold (fun set _ fieldType -> Set.union (gatherUnificationVars fieldType) set) Set.empty fields

    | ConcNewType (_, types) -> Set.collect gatherUnificationVars types
    | ConcArrow (fromType, toType) -> Set.union (gatherUnificationVars fromType) (gatherUnificationVars toType)

/// This gathers all the (unconstrained!) unification variables in a type. Which means that if we find unification vars a, b, and c in a type, then that means we have a `forall a,b,c. {{expr}}`
and gatherUnificationVars (type_ : TypeForInference) : UnificationVar set =
    match type_ with
    | Concrete concrete -> gatherUnificationVarsConcrete concrete
    | Named _ -> Set.empty
    | UnificationVarId var -> Set.singleton var
//| SkolemId skolem -> Set.empty



let rec gatherUnboundNamesConcrete (concrete : ConcreteType) =
    match concrete with
    | ConcUnitType -> Set.empty
    | ConcPrimType _ -> Set.empty
    | ConcTuple tom -> Set.collect gatherUnboundNames tom
    | ConcList t -> gatherUnboundNames t
    | ConcRecordWith fields
    | ConcRecordExact fields ->
        Map.fold (fun set _ fieldType -> Set.union (gatherUnboundNames fieldType) set) Set.empty fields
    | ConcNewType (_, types) -> Set.collect gatherUnboundNames types
    | ConcArrow (fromType, toType) -> Set.union (gatherUnboundNames fromType) (gatherUnboundNames toType)

/// Collect all the value names that have not yet been eliminated and thus must exist somewhere outside the current scope
and gatherUnboundNames (type_ : TypeForInference) : RefValueName set =
    match type_ with
    | Concrete concrete -> gatherUnboundNamesConcrete concrete
    | Named name -> Set.singleton name
    | UnificationVarId _ -> Set.empty










/// To be clear, unlike the previous approach where unification is _mutative_, this one does not actually combine two types mamish, but leaves the original types unchanged, and only returns the new unified type
///
/// @TODO: might need to return the list of constrained unification vars and what they've been constrained to, so we can bubble those up and replace the univars in the other places that they need to be
let rec unifyTwoConcreteTypes
    (typeA : ConcreteType)
    (typeB : ConcreteType) (* (ctx : TypeContext) *)
    : TypeInferenceResult =
    let makeErr a b = Error (TypeClash (a, b))

    match typeA, typeB with
    | ConcUnitType, ConcUnitType -> Cart.insertType (Ok (Concrete ConcUnitType)) ctx
    | ConcPrimType primA, ConcPrimType primB ->
        if primA = primB then
            let result = Ok (Concrete (ConcPrimType primA))
            Cart.insertType result ctx
        else
            Cart.insertType (makeErr typeA typeB) ctx

    | ConcTuple listA, ConcTuple listB ->
        let (TOM (headA, neckA, tailA)) = listA
        let (TOM (headB, neckB, tailB)) = listB

        let zipped = List.zipList tailA tailB

        match zipped with
        | Ok zippedTails ->
            let unifiedHead = unifyTwoTypes headA headB ctx
            let unifiedNeck = unifyTwoTypes neckA neckB unifiedHead.context

            let unifiedTail, unifiedTailCtx =
                List.mapFold
                    (fun state (a, b) ->
                        let result = unifyTwoTypes a b state
                        result.returnedType, result.context)
                    unifiedNeck.context
                    zippedTails

            let unifiedTom =
                TOM.new_ unifiedHead.returnedType unifiedNeck.returnedType unifiedTail

            match unifiedTypesTom with
            | Ok unifiedTypes -> Cart.insertType (Ok (Concrete (ConcTuple unifiedTypes))) unifiedTailCtx
            | Error errs -> Cart.insertType (Error (NEL.head errs)) unifiedTailCtx

        | Error _ -> Cart.insertType (makeErr typeA typeB) ctx




and unifyTwoTypes (typeA : WithUnresolveds) (typeB : WithUnresolveds) (ctx : TypeContext) : CART =
    // @TODO: no idea if this is anywhere near correct
    match typeA, typeB with
    | Concrete concreteA, Concrete concreteB -> unifyTwoConcreteTypes concreteA concreteB ctx
    | UnificationVarId var, Concrete concrete
    | Concrete concrete, UnificationVarId var -> Cart.insertType (Ok (Concrete concrete)) ctx

    | TypeVarId var, Concrete concrete
    | Concrete concrete, TypeVarId var -> Cart.insertType (Ok (Concrete concrete)) ctx

    | Concrete concrete, Named _
    | Named _, Concrete concrete -> Cart.insertType (Ok (Concrete concrete)) ctx

    | TypeVarId _, TypeVarId var
    | Named _, TypeVarId var
    | UnificationVarId _, TypeVarId var
    | TypeVarId var, Named _
    | TypeVarId var, UnificationVarId _ -> Cart.insertType (Ok (TypeVarId var)) ctx

    | Named _, Named name -> Cart.insertType (Ok (Named name)) ctx

    | UnificationVarId _, UnificationVarId var -> Cart.insertType (Ok (UnificationVarId var)) ctx
    | Named _, UnificationVarId var
    | UnificationVarId var, Named _ -> Cart.insertType (Ok (UnificationVarId var)) ctx


//| ConcList _, ConcList _ ->
//| ConcRecordWith _, ConcRecordWith _ ->
//| ConcRecordExact _, ConcRecordExact _ ->
//| ConcNewType _, ConcNewType _ ->
//| ConcArrow _, ConcArrow _ ->
//| Named _, Named _ ->
//| TypeVar _, TypeVar _ ->











/// Get type information based on a single assignment pattern – named values, destructurings, and so on.
/// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
let getAccumulatorFromParam (param : AssignmentPattern) : CART = failwith "@TODO: implement"


/// This should: from a binding, derive the type + all the names declared/destructured along with their types in the Accumulator - for use in the let expression body (and of course not outside of it)
let private getAccumulatorFromBinding (binding : LetBinding) : CART = failwith "@TODO: implement"



let rec getAccumulatorFromExpr (expr : T.Expression) : CART = ()

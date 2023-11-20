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


/// A recursive dependency group
type RecursiveDepGroup =
    {
        namesDependedOn : LowerIdent nel
        ownName : LowerIdent
        expr : D.Expr
        /// Self explanatory: there could be expressions who themselves are not recursive or part of a recursive graph but depend on one or more of the names that *are* recursive
        expressionsDependentOnThisGroup : (LowerNameValue * D.Expr) seq
    }

type AllRecursiveDepGroups =
    { groups : RecursiveDepGroup seq
      exprsDependentOnMultipleGroups : (LowerNameValue * D.Expr) seq }


/// This is the result of running the 1st type inference strategy: the one that is more powerful because it can infer polytypes, but less flexible because it can't deal with recursively defined names, only those names whose types are annotated explicitly or whose types can be inferred by simply resolving the names in order of which depends on which
type SimpleTypeInferenceResult =
    {
        /// After dependency resolution, here are all the fully resolved and typed expressions that we could type purely by tackling those values 1) which have explicit type annotations 2) whose types can be inferred without needing to resolve the type of any other named value 3) whose types only depend on the types of names we have already typed
        typedNames : TypedLocalNamesMap
        /// Now here is the list of names whose types cannot be inferred simply because their type depends either on their own name (f referencing f) or it depends on the type of another name whose type depends on itself (f referencing g referencing f again)
        recursiveDepsGroups : AllRecursiveDepGroups
    }

//let getTypeAnnotation (name : LowerNameValue) (namesMap : TypedNamesMap) : PolyType_ option = Map.tryFind name namesMap
let getTypeAnnotation (binding : D.LetBindingSingle) = binding.typeAnnotation


/// Gets all the value names referenced in an expression – note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because they are opaque
let getNamesUsedInExpr (namesToLookOutFor : LowerIdent set) (expr : D.Expr) : LowerIdent set =
    failwith "@TODO: implement"

/// I believe... this should only work in let expressions?
let getBindingsInExpr (expr : D.Expr) : (LowerIdent * D.Expr) list = failwith "@TODO: implement"

/// Given a list of names and their assigned expressions, constructs a list of groups of
let constructRecursiveDependencyGraph
    (namesMap : TypedNamesMap)
    (namesAndExprs : (LowerIdent * D.Expr) seq)
    : AllRecursiveDepGroups =
    failwith "@TODO: implement"




/// Add a local names map to a global one
let addLocalNamesMap (localNamesMap : TypedLocalNamesMap) (namesMap : TypedNamesMap) : TypedNamesMap =
    localNamesMap
    |> Map.mapKeyVal (fun key v -> LocalLower key, v)
    |> Map.merge namesMap


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
        |> Seq.choose (fun binding -> getTypeAnnotation binding |> Option.map (Tuple.makePair binding.name))
        |> Map.ofSeq

    /// This is the inner recursive function that goes through all the expressions that don't rely on any untyped-yet names and resolves their types.
    /// How do we know when we've exhausted all available expressions and we've hit some islands of recursive values? I suppose if there is no difference between the results of the last run and the next one. Then that gives us a single list of all unresolvable names, but we then still have to group them into mutually recursive groups.
    let rec resolveNamesOfAvailable
        (globalNamesMap : TypedNamesMap)
        (* The accumulatingNamesMap is the new stuff that we're learning about and adding onto with each run of the recursive function *)
        (accumulatingNamesMap : TypedLocalNamesMap)
        (namesAndExprsToResolveStill : (LowerIdent * D.Expr) seq)
        : TypedLocalNamesMap * (LowerIdent * D.Expr) seq =

        match Seq.toList namesAndExprsToResolveStill with
        | [] -> accumulatingNamesMap, Seq.empty
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
                accumulatingNamesMap, nameNotAvailableForResolution

            | _ ->
                let newlyGleanedMap : TypedLocalNamesMap =
                    namesAvailableForResolution
                    |> List.map (fun (name, expr) -> name, simpleResolver globalNamesMap expr)
                    |> Map.ofList

                let combinedNewlyGleanedMap = Map.merge newlyGleanedMap accumulatingNamesMap

                resolveNamesOfAvailable globalNamesMap combinedNewlyGleanedMap nameNotAvailableForResolution


    namesAndExprs
    |> Seq.map (fun binding -> binding.name, binding.assignedExpr)
    |> resolveNamesOfAvailable namesMap namesWithTypeAnnotations





/// Given an expression that doesn't rely on recursively defined names, it infers the type and returns it, along with any constraints learned about other unification variables.
and simpleResolver = inferTypeFromExpr


/// This is stage one of the type inference/resolution algorithm, it gets all available type annotations, infers the types of named values that don't depend on any others, and loops through so that every non-recursive definition is typed.
/// Then what we're left with are the recursive groups which need to be resolved with unification variables. Then those values that depend on the recursive groups can be inferred with the whole algorithm again.
and resolveSimpleInference
    (namesMap : TypedNamesMap)
    (letBindings : D.LetBindingSingle seq)
    : SimpleTypeInferenceResult =
    let simpleResults, recursivelyDefinedNameVals =
        resolveAllResolvableNames namesMap letBindings

    let combinedNamesMap = addLocalNamesMap simpleResults namesMap

    { typedNames = simpleResults
      recursiveDepsGroups = constructRecursiveDependencyGraph combinedNamesMap recursivelyDefinedNameVals }




and resolveInsideOutInference (namesMap : TypedNamesMap) (recursiveGroup : RecursiveDepGroup) : UnificationVarsContext =
    ()

/// Which entails generalising those unification vars with no constraints and converting them to polytypes, and just concretising everything else
and convertUnificationResultsToNormalTypes
    (namesMap : TypedNamesMap)
    (unificationResult : UnificationVarsContext)
    : TypedLocalNamesMap =
    ()


/// This returns the fully resolved map of let (and top-level, I suppose) bindings, along with the constraints on unification variables.
///
/// Since in a let bindings expression there can still be more constraints on unification variables, we need the unification variables map to be returned as well, and combine it with the uniVarsMap that we'll return from the body of the let bindings expression, and only _then_ apply those constraints from the unification variables to those names that still only have unification variables assigned to them and not concrete polytypes. But tbh that last part shouldn't require anything more specific or specialised than just unifying the final combined unification vars map with the local names map (also returned from this function), and then concretise the unification vars – and generalise where possible! – into the namesMap.
///
/// @TODO: on second thought, I think it makes more sense to encapsulate the unifying of all the constraints and shit in a dedicated function rather than in the inferTypeExpr function which does a bunch of other stuff also
and resolveAllNames
    (namesMap : TypedNamesMap)
    (letBindings : D.LetBindingSingle seq)
    (body : D.Expr)
    : SelfAndConstrainedUnificationVars =
    //and resolveAllNames (namesMap : TypedNamesMap) (letBindings : D.LetBindingSingle seq) (body : D.Expr) : TypedLocalNamesMap * UnificationVarsMap =
    // @TODO: beware of this entire function body, it was written by GitHub Copilot and I haven't checked it yet!

    let simpleResults, recursivelyDefinedNameVals =
        resolveAllResolvableNames namesMap letBindings

    let combinedNamesMap = addLocalNamesMap simpleResults namesMap

    let recursiveGroups =
        constructRecursiveDependencyGraph combinedNamesMap recursivelyDefinedNameVals

    let recursiveGroupsResults =
        recursiveGroups |> Seq.map (resolveInsideOutInference combinedNamesMap)

    let allResults =
        recursiveGroupsResults
        |> Seq.map (convertUnificationResultsToNormalTypes combinedNamesMap)

    allResults |> Seq.fold addLocalNamesMap Map.empty








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
                $"Couldn't resolve named value \"{name}\"! This is most likely due to it being an undeclared variable (which @TODO we still need to handle) but if not it might indicate that we're not passing all declared names down in the namesMap"


    | D.LetBindings (bindings, body) -> resolveAllNames namesMap bindings body


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

and combineTwoUnificationVarMaps (map1 : UnificationVarsMap) (map2 : UnificationVarsMap) : UnificationVarsMap = ()

and combineUnificationVarMapsList (maps : UnificationVarsMap seq) : UnificationVarsMap =
    maps |> Seq.fold combineTwoUnificationVarMaps Map.empty












































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

module AlgorithmW


open TypedSyntaxTree
module T = TypedSyntaxTree
open QualifiedSyntaxTree.Names
module DG = DependencyGraphs















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

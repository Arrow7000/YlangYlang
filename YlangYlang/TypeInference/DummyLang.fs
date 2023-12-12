module DummyLang

open QualifiedSyntaxTree.Names

module DG = DependencyGraphs


/// Represents any concrete type (except records for now)
///
/// Because... I've realised that actually I can represent ~every single fucking type~ [actually not *every* single fucking type, cos records can't be represented this way. But close enough!] this way, and this will let me iterate on the type inference and unification logic *muuuuuuuuch* quicker
type SimpleType =
    /// For types like Int, String, etc.
    | PrimitiveType of name : UpperNameValue
    /// For types like List a, Tuple a b, Map k v, and so on.
    | ParametricType of name : UpperNameValue * paramTypes : SimpleType nel



(*
    This is for the "inside-out" type inference, where inferring polytypes is not possible and all we have is simple unification
*)

type UnificationVarId = | UnificationVarId of System.Guid

///// Unconstrained unification vars can be generalised as soon as they are out of scope, or perhaps rather: as soon as the lowest common ancestor between two occurrences of the same unification variable.
//type SimpleTypeWithUnificationVars =
//    /// If there are no constraints on a thing then we can still generalise! It's only if there are seemingly incompatible constraints that we cannot generalise
//    | Unconstrained
//    | PrimitiveType of name : UpperNameValue
//    | ParametricType of name : UpperNameValue * paramTypes : UnificationVarId

//type UnificationVarOrValName =
//    /// Because if we need to resort to this strategy we should never need to resort to recursive deps across modules because circular references between modules is forbidden, so we should only ever need to use this strategy for local names
//    | ValName of LowerIdent
//    | UnificationVar of UnificationVarId

//type UnificationVarsContext = Map<UnificationVarOrValName, SimpleTypeWithUnificationVars>







///// A skolem represents a concrete type that is simply unknown at this point, so we cannot make any assumptions about it, and there may be no constraints on it; otherwise it would no longer be a skolem but a concrete type
//type SkolemId = | SkolemId of System.Guid


/// This is what a skolem looks like outside the place that it is defined, i.e. the `a` and `b` in `forall a b. {{type expression using a and b}}`
type TypeVariableId = | TypeVariableId of System.Guid

///// So this describes the definition of a polytype *before* it is instantiated. I.e. a `forall a. Maybe a` or a `forall a b. a -> b`. Once we put this into a larger expression we must instantiate these type variables with the concrete types or skolems (if unifying them with known types) or with unification variables (if we're unifying them with types that are not yet known).
/////
///// Note: we don't have a map of the type variables used in the polytype because they can just be inferred by doing a simple recursive scan for which type vars are present in the polytype, so in our implementation they're implicit, even though we can still represent them explicitly. Just this way we avoid the possibility of our internal type referencing type variables that don't exist.
/////
///// Hmmm... actually I think maybe we should add an explicit `forall` representation in there, because otherwise it might be quite hard to know at any point whether this particular type variable is independent from here and *this* is where the implicit `forall` is or if it's actually linked to a different thing in a parent thing. And... yes technically if you're looking inside a `forall` scope that would then be called a skolem, but that's then a matter of perspective, but the underlying thing is the same, so we'd always have the same data thingy for it regardless of whether we were inside or outside the thing.
//type PolyTypeContents =
//    | TypeVariable of TypeVariableId
//    | PrimitiveType of name : UpperNameValue
//    /// The type params have to be *contents* also because they cannot be free variables *inside* of a type expression or type signature. Existential qualifiers ("forall"s) have to appear at the beginning of a type expression.
//    | ParametricType of name : UpperNameValue * typeParams : PolyTypeContents



//type PolyType =
//    { forall : TypeVariableId set
//      typeExpr : PolyTypeContents }


//type PolyTypeOrUnificationVar =
//    | PolyType of PolyType
//    | UnificationVar of SimpleTypeWithUnificationVars

//type PolyTypeWithUnificationVars =
//    | TypeVariable of TypeVariableId
//    | PrimitiveType of name : UpperNameValue
//    /// The type params have to be *contents* also because they cannot be free variables *inside* of a type expression or type signature. Existential qualifiers ("forall"s) have to appear at the beginning of a type expression.
//    | ParametricType of name : UpperNameValue * typeParams : PolyTypeContents
//    | Unconstrained






(*
How do we represent a many-to-many relationship between unification variables and type variables?
Maybe the first question actually should be how do we unify unification variables? Because if we can unify unification variables then we can let multiple of them point towards the same type variable, and also a concrete type.

Basically the problem is that we have the concrete type shapes that need to be able to reference, in addition to of course other concrete types:
- unification variables
- type variables
- an instantiated type variable – so that we can propagate instantiated type variables upwards to the polytype where they were declared

But we also want to be able to represent the fact that multiple unification variables have been unified with each other, that multiple type variables have been unified with each other, and that one or more unification variables _and_ type variables have been unified with each other.
And we want to be able to do that without polluting the internals of the concrete type shapes; which should really only be able to reference either a unification variable, a type variable, or an instantiated type variable (which is what lets us propagate the instantiated type variable upwards to the polytype where it was declared without propagating a whole additional substitution map upwards).
*)



type PolyTypeContents =
    /// Referencing a unification variable. To figure out what this unification var is you'll need to look into your local UnificationVarsMap (see below)
    | UnificationVar of UnificationVarId
    /// Referencing a *type variable* (not a unification variable!), which if it gets replaced we need to somehow propagate the message upwards that all instances of this type variable need to be replaced with the same thing – we only stop propagating that message upwards when we get to the polytype where this type var is declared in
    | TypeVariable of TypeVariableId

    //| InstantiatedTypeVariable of typeVars : TypeVariableId * instantiatedBy : UnificationVarId
    /// A simple unparametric type, like `Int` or `String`
    | PrimitiveType of name : UpperNameValue
    /// Parametric types, like `List a` or `Maybe a`
    | ParametricType of name : UpperNameValue * typeParams : PolyTypeContents list


/// Alias for PolyTypeContents_
type PTC = PolyTypeContents


type PolyType =
    { forall : TypeVariableId list
      typeExpr : PolyTypeContents }




type TypedNamesMap = Map<LowerNameValue, PolyType>
type TypedLocalNamesMap = Map<LowerIdent, PolyType>

//type PolyTypeOrUnificationVarOrValName =
//    | UnificationVar of UnificationVarId
//    | ValName of LowerIdent

/// Map that maps value names to their polytypes but also unification variables to their thingies
//type FullRangeNamesMap = Map<PolyTypeOrUnificationVarOrValName, PolyTypeOrUnificationVar>


type UnificationError = | UnificationClash of PolyTypeContents * PolyTypeContents


type UnificationResult = Result<PolyTypeContents, UnificationError>

/// A unification result or a redirect to another entry. Having multiple unification variables pointing to the same unification result lets us represent multiple unification variables that have been unified with each other. And having a set of type variables pointing to the same unification result lets us represent multiple type variables that have been unified with each other; and thereby also multiple unification variables that have been unified with multiple type variables.
/// FYI having multiple unification variables unified with each other can take the form of multiple uniVars all redirecting to the same one, or multiple uniVars redirecting to each other in a chain, or a combination of both in a kind of tree structure where each entry points to its parent, and the root of the tree is the unification result.
/// Instantiating a type variable with a fresh unification variable is done by following that unification variable's redirect chain until you get to the root entry, and then adding that type variable to the set of type variables in the root.
type UnifResOrRedirect =
    /// Unification result
    | UnifResult of Result<PolyTypeContents, UnificationError> option * TypeVariableId set
    /// Redirect to another unification variable to represent that they are unified with each other
    | UnifRedirect of UnificationVarId


/// THIS is basically the new version of the Accumulator, because it gathers unification constraints on variables, and so every inferExpressionType function will return one of these and so they need to be combined to get the full constraints for each unification variable. Then, with all of the gathered constraints on each unification variable, we can assign that type to the name, and then use that inferred type as the type for that name, and then proceed to see if that inferred type is indeed compatible with all the other uses of that name.
type UnificationVarsMap = Map<UnificationVarId, UnifResOrRedirect>





module UnificationVarsMap =
    let private findByUnificationVar (uniVar : UnificationVarId) (map : UnificationVarsMap) : UnifResOrRedirect =
        match Map.tryFind uniVar map with
        | Some v -> v
        | None ->
            //failwith
            //    $"Couldn't find unification var {uniVar} in map, which should not be possible, every unification variable that is referenced anywhere should exist in the map"
            UnifResult (None, Set.empty)

    let rec findUnificationVarResult
        (uniVar : UnificationVarId)
        (map : UnificationVarsMap)
        : UnificationVarId * (UnificationResult option * TypeVariableId set) =
        match findByUnificationVar uniVar map with
        | UnifRedirect redirectUniVar -> findUnificationVarResult redirectUniVar map
        | UnifResult (res, typeVars) ->
            // Return the result as well as the final unification variable at that location
            uniVar, (res, typeVars)


    type UnificationVarResultWithSteps =
        {
            /// The (reversed) list of steps we took before we got to the final unification var
            hops : UnificationVarId list
            finalUnificationVar : UnificationVarId
            result : UnificationResult option
            typeVars : TypeVariableId set
        }


    /// This gets the unification result, but also includes all the unification variables we encountered during our redirect hops
    let rec findUnificationVarResultWithSteps uniVar map : UnificationVarResultWithSteps =
        match findByUnificationVar uniVar map with
        | UnifRedirect redirectUniVar ->
            let result = findUnificationVarResultWithSteps redirectUniVar map

            { result with
                hops = redirectUniVar :: result.hops }

        | UnifResult (res, typeVars) ->
            { hops = List.empty
              finalUnificationVar = uniVar
              result = res
              typeVars = typeVars }


    let editUnificationVarResult
        (uniVar : UnificationVarId)
        (updater : UnificationResult option -> TypeVariableId set -> UnificationResult option * TypeVariableId set)
        (map : UnificationVarsMap)
        : UnificationVarsMap =
        let finalUnivar, (res, typeVars) = findUnificationVarResult uniVar map

        map |> Map.add finalUnivar (updater res typeVars |> UnifResult)





    /// Represents a single entry in the unification vars map of all the things that are bound to the same constraints, along with the constraint itself
    type CoupledConstraints =
        { finalUniVar : UnificationVarId
          otherUniVars : UnificationVarId set
          result : UnificationResult option
          typeVars : TypeVariableId set }

        member this.allUniVars : UnificationVarId set =
            Set.add this.finalUniVar this.otherUniVars



    /// Gets all the unification variables that have been unified with the given unification variable, via traversing all the redirects
    let getAllJoinedUnificationVars (uniVar : UnificationVarId) (map : UnificationVarsMap) : CoupledConstraints =
        let finalUnivar, (res, typeVars) = findUnificationVarResult uniVar map

        let linkedUnificationVars =
            map
            |> Map.choose (fun key _ ->
                let result = findUnificationVarResultWithSteps key map

                if result.finalUnificationVar = finalUnivar then
                    Some result.hops
                else
                    None)
            |> Map.values
            |> Seq.concat
            |> Set.ofSeq


        { finalUniVar = finalUnivar
          otherUniVars = linkedUnificationVars
          result = res
          typeVars = typeVars }




    let getTypeVarConstraints (typeVar : TypeVariableId) (map : UnificationVarsMap) : CoupledConstraints option =
        let firstContainingTypeVar =
            map
            |> Map.tryPick (fun uniVar redirectOrResult ->
                match redirectOrResult with
                | UnifRedirect _ -> None
                | UnifResult (res, typeVars) ->
                    if Set.contains typeVar typeVars then
                        Some (uniVar, (res, typeVars))
                    else
                        None)

        firstContainingTypeVar
        |> Option.map (fun (uniVar, (res, typeVars)) ->
            let result = getAllJoinedUnificationVars uniVar map

            { finalUniVar = uniVar
              otherUniVars = result.otherUniVars
              typeVars = typeVars
              result = res })




/// @TODO: probably need to make the self property a result of PolyType because there could be unification errors
type SelfAndConstrainedUnificationVars =
    { self : PolyType
      constrained : UnificationVarsMap }





module SelfAndConstrainedUnificationVars =
    let make self constrained : SelfAndConstrainedUnificationVars =
        { self = self
          constrained = constrained }

///// This is a temporary data structure returned from both inferExpressionType and unifyTypes functions to signify which type variables in the nearest parent polytype forall need to be replaced with which concrete types, because if a type variable gets replaced with a particular concrete type we need to replace that type variable in every place it occurs!
//type ConcretisedTypeVars = Map<TypeVariableId, UnificationVarId>



module Types =
    let private makePrimitiveType = PrimitiveType << LocalUpper << UpperIdent
    let private makeParametricType label params_ = ParametricType (LocalUpper (UpperIdent label), params_)

    let private makeNewTypeVarId () = System.Guid.NewGuid () |> TypeVariableId

    /// Makes a new polytype. Pass in as many units as there are type parameter slots for that type.
    let private makeNewParametricType label (typeVarSlots : unit list) =
        let typeVars = typeVarSlots |> List.map makeNewTypeVarId

        { forall = typeVars
          typeExpr = makeParametricType label (List.map TypeVariable typeVars) }

    let makeEmptyPolyType contents =
        { forall = List.empty
          typeExpr = contents }

    let strType : PolyTypeContents = makePrimitiveType "String"
    let intType : PolyTypeContents = makePrimitiveType "Int"

    let listTypeOf (t : PolyType) =
        { forall = t.forall
          typeExpr = makeParametricType "List" [ t.typeExpr ] }

    let listType : PolyType = makeNewParametricType "List" [ () ]

    let tupleTypeOf a b =
        { forall = a.forall @ b.forall
          typeExpr = makeParametricType "Tuple" [ a.typeExpr; b.typeExpr ] }

    let tupleType : PolyType = makeNewParametricType "Tuple " [ (); () ]

    let funcTypeOf from to_ =
        { forall = from.forall @ to_.forall
          typeExpr = makeParametricType "Arrow " [ from.typeExpr; to_.typeExpr ] }

    let funcType : PolyType = makeNewParametricType "Arrow " [ (); () ]





/// Module with a greatly simplified language but still containing all the key elements, so that we can test type inference and resolution with a simpler version before tackling the real thing
module AbstractSyntaxTree =

    type LetBindingSingle =
        { name : LowerIdent
          typeAnnotation : PolyType option
          assignedExpr : Expr }


    and Expr =
        | StrVal of string
        | IntVal of int
        | ListVal of Expr list
        | TupleVal of first : Expr * second : Expr
        | LambdaVal of param : LowerIdent * body : Expr
        | NamedVal of LowerIdent
        | LetBindings of bindings : LetBindingSingle nel * body : Expr
        | FuncApplication of funcExpr : Expr * input : Expr


    let str = StrVal
    let int = IntVal
    let list = ListVal
    let tuple a b = TupleVal (a, b)
    let lambda param body = LambdaVal (LowerIdent param, body)
    let name = NamedVal << LowerIdent

    let letBinding name typeAnnotationOpt expr =
        { name = LowerIdent name
          typeAnnotation = typeAnnotationOpt
          assignedExpr = expr }

    let letBindings bindings body = LetBindings (bindings, body)

    let apply funcExpr inputExpr = FuncApplication (funcExpr, inputExpr)




module Ast = AbstractSyntaxTree

module Sacuv = SelfAndConstrainedUnificationVars



/// Make a new unification variable
let private makeNewUniVar () = System.Guid.NewGuid () |> UnificationVarId

/// Make a new type variable
let private makeNewTypeVar () = System.Guid.NewGuid () |> TypeVariableId






type BindingsResolutionResult =
    {
        inferredTypes : TypedLocalNamesMap
        constrained : UnificationVarsMap
        /// These are the unification variables that were only introduced inside the bindings type resolution function and so can be removed in favour of the things they reference – either a concrete type or a unification variable declared at a higher scope. But if they cannot be swapped out for something to take its place, should be left in because they could then still denote a connection between two or more different values.
        /// So I think in the latter case they probably could be removed (and thereby generalised!) if there is only one occurrence of it in a type context. A type context including a self type, a unification vars map, and an inferred typed local names map.
        unificationVarsIntroducedHere : UnificationVarId set
    }










type private OverlapCheckResult =
    /// This means there was only one unification var left that's been declared higher up, so replace all the uniVars and typeVars with this uniVar
    | SingleUniVarLeft of UnificationVarId
    /// This means there was only one type var left that's been declared higher up, so replace all the uniVars and typeVars with this typeVar
    /// – actually umm I don't think this is true at all, I think in this case we instantiate a fresh unification variable and we point it to this type variable.. but maybe only when there are constraints to be had? Hmm maybe just figuring out what the overlap is only step 1 of figuring out what to do with the map entry, because there's also the fact that there are type constraints attached to it to consider...
    /// And then there's also the somewhat separate concern of being able to propagate type clash errors outwards up the expression tree so that we can become aware of them; in which case maybe we should always propagate things outwards that have unification variables with clashing type constraints attached to them, so that we can become aware of them at the top level?
    /// But tbh either way step 1 of figuring out what to do does still involve figuring out what the overlap is, so even if this type isn't singlehandedly able to tell us all the things we need to do, it's still a necessary first step in doing so, and thus still valuable.
    | SingleTypeVarLeft of TypeVariableId
    | SingleOfEachLeft of uniVar : UnificationVarId * typeVar : TypeVariableId

    /// This means there were multiple unification vars left that have been declared higher up, so replace all the uniVars and typeVars with the "final" uniVar (i.e. the one at the end of the redirect chain containing the actual result)
    | MultipleUniVarsLeft of UnificationVarId tom
    /// This means there were multiple type vars left that have been declared higher up, so I *think* we need to keep these remaining typeVars in the map, ensure we have a unification variable pointing at them (which may necessitate creating a new unification variable if all the others are gone?), and replacing all instances of the uniVars and typeVars with this new uniVar
    | MultipleTypeVarsLeft of TypeVariableId tom

    /// I think replace all the uniVars and typeVars with the one uniVar left here
    | SingleUniVarAndMultipleTypeVarsLeft of UnificationVarId * TypeVariableId tom

    /// ?
    | SingleTypeVarAndMultipleUniVarsLeft of TypeVariableId * UnificationVarId tom

    | MultipleOfBoth of UnificationVarId tom * TypeVariableId tom

    /// So the entire thing can be deleted and its contents swapped out for the uniVars and typeVars in question! Finally! This is the base case methinks.
    | FullOverlap


/// This is really the result of removing the locally declared unification variables and locally scoped type variables from the map, and either replace them with a uniVar or typeVar that is declared at a higher level, or if not: to replace all the instances of a type with the concrete type – or generalise it with a newly declared type variable if there are no constraints on it.
/// This should contain all the information required to replace the uniVars and typeVars for _any_ PolyTypeContents, because we need to do this swapping out for both the self type and all the types in the unificationVarsMap. They have to be exactly the same operation, because both things need to have their uniVars and typeVars swapped out in exactly the same way.
/// Now I'm assuming here that this swapping out should not have any additional effects of collapsing other entries in the uniVarsMap, which I do think is correct, but if it isn't true, then this operation would need to happen in multiple nested steps, which would be f***ing annoying again.
type NormalisationInstruction =
    {
        unificationVarsToReplace : UnificationVarId set
        typeVarsToReplace : TypeVariableId set

        toReplaceWith : Result<PolyTypeContents, UnificationError>
        /// If a new type var is created here we'll declare it here
        newTypeVarOpt : TypeVariableId option
    }


(*

    Type inference

*)




/// Gets all the value names referenced in an expression – note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because as far as the higher scopes are concerned those names do not exist.
/// @TODO: this should probably fail for shadowed names, but we'll assume for now that there are no shadowed names
let rec getNamesUsedInExpr (namesToLookOutFor : LowerIdent set) (expr : Ast.Expr) : LowerIdent set =
    match expr with
    | Ast.StrVal _ -> Set.empty
    | Ast.IntVal _ -> Set.empty
    | Ast.ListVal exprs -> Set.collect (getNamesUsedInExpr namesToLookOutFor) exprs
    | Ast.TupleVal (first, second) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor first) (getNamesUsedInExpr namesToLookOutFor second)

    | Ast.LambdaVal (_, body) -> getNamesUsedInExpr namesToLookOutFor body
    | Ast.NamedVal name ->
        if Set.contains name namesToLookOutFor then
            Set.singleton name
        else
            Set.empty

    | Ast.LetBindings (bindings, body) ->
        Set.union
            (getNamesUsedInExpr namesToLookOutFor body)
            (bindings
             |> Seq.map (_.assignedExpr >> getNamesUsedInExpr namesToLookOutFor)
             |> Set.unionMany)

    | Ast.FuncApplication (funcExpr, inputExpr) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor funcExpr) (getNamesUsedInExpr namesToLookOutFor inputExpr)




let sortBindingsTopologically (namesAndExprs : (LowerIdent * Ast.Expr) seq) : DG.OneOrMore<LowerIdent * Ast.Expr> list =
    let bindingNames = namesAndExprs |> Seq.map fst |> Set.ofSeq
    let getDependencies = snd >> getNamesUsedInExpr bindingNames >> Set.toSeq

    DG.getStronglyConnectedComponents<LowerIdent * Ast.Expr, LowerIdent> fst getDependencies namesAndExprs
    |> DG.sortOneOrMoreTopologically fst getDependencies










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



module TypeInference =



    let rec applyNormalisationInstruction
        (normalisationInstr : NormalisationInstruction)
        (polyTypeContents : PolyTypeContents)
        : PolyTypeContents =
        /// @TODO: handle the error case here still
        let replacement () =
            match normalisationInstr.toReplaceWith with
            | Ok ptc -> ptc
            | Error e -> failwith "@TODO: need to handle the error case here still"

        match polyTypeContents with
        | PTC.UnificationVar uniVar ->
            if Set.contains uniVar normalisationInstr.unificationVarsToReplace then
                replacement ()

            else
                PTC.UnificationVar uniVar

        | TypeVariable typeVar ->
            if Set.contains typeVar normalisationInstr.typeVarsToReplace then
                replacement ()

            else
                TypeVariable typeVar

        | PrimitiveType prim -> PrimitiveType prim
        | ParametricType (name, ptcs) ->
            ParametricType (name, List.map (applyNormalisationInstruction normalisationInstr) ptcs)


    let applyNormalisationInstructionToResult
        (normalisationInstr : NormalisationInstruction)
        (polyTypeContentsResult : UnificationResult)
        : UnificationResult =
        match polyTypeContentsResult with
        | Ok polyTypeContents -> applyNormalisationInstruction normalisationInstr polyTypeContents |> Ok
        | Error e ->
            match e with
            | UnificationClash (a, b) ->
                UnificationClash (
                    applyNormalisationInstruction normalisationInstr a,
                    applyNormalisationInstruction normalisationInstr b
                )
                |> Error



    let applyNormalisationInstructionToResultOpt
        (normalisationInstr : NormalisationInstruction)
        (polyTypeResultOpt : UnificationResult option)
        : UnificationResult option =
        polyTypeResultOpt
        |> Option.map (applyNormalisationInstructionToResult normalisationInstr)



    let applyNorminstrToNormInstr
        (normInstrToApply : NormalisationInstruction)
        (normInstrToBeApplied : NormalisationInstruction)
        : NormalisationInstruction =
        { normInstrToBeApplied with
            toReplaceWith = applyNormalisationInstructionToResult normInstrToApply normInstrToBeApplied.toReplaceWith }


    let applyNormInstrToUniVarsMap
        (normInstr : NormalisationInstruction)
        (map : UnificationVarsMap)
        : UnificationVarsMap =
        map
        |> Map.map (fun _ redirectOrResult ->
            match redirectOrResult with
            | UnifRedirect uniVar -> UnifRedirect uniVar

            | UnifResult (typeResultOpt, typeVars) ->
                UnifResult (applyNormalisationInstructionToResultOpt normInstr typeResultOpt, typeVars))






    /// This also generalises as well as instantiates, because it needs to be able to generalise unification variables that are not constrained, and instantiate them with concrete types if they are constrained.
    let instantiateTypeVarsInPolyTypeContents
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyTypeContents)
        : SelfAndConstrainedUnificationVars =
        (*
            I think what we need to do here is:
            - feed in all the uniVars and typeVars that we want to remove in the map
            - the map tells us which groupings there are
            - for each grouping the map tells us whether there's anything left then or not(!)
            - if there's something left, then leave the actual constrained type in the map, just tightening up all the redirects and no-longer-needed typeVars
                - in this case we'll need to know which uniVars and typeVars were actually removed and which were kept, so that we can replace the removed ones in the self type with the kept ones
            - if there is nothing left for a particular grouping, the map needs to tell us what the constraints were on that removed one, so that we can replace all the uniVars and typeVars in the self type with the concrete constrained type
            *)


        let makeNormalisationInstruction
            (uniVars : UnificationVarId set)
            (typeVars : TypeVariableId set)
            (rplcmnt : UnificationResult)
            (newTypeVarOpt : TypeVariableId option)
            : NormalisationInstruction =
            { unificationVarsToReplace = uniVars
              typeVarsToReplace = typeVars

              toReplaceWith = rplcmnt
              newTypeVarOpt = newTypeVarOpt }


        let matchesForUniVars : UnificationVarsMap.CoupledConstraints set =
            unificationVarsWeCanEliminate
            |> Set.map (fun uniVar -> UnificationVarsMap.getAllJoinedUnificationVars uniVar unificationVarsMap)

        let matchesForTypeVars : UnificationVarsMap.CoupledConstraints set =
            typeVarsToReplace
            |> Set.choose (fun typeVar -> UnificationVarsMap.getTypeVarConstraints typeVar unificationVarsMap)

        /// This should now include all the entries that any of the uniVars and typeVars here touch
        let matchesForBoth : UnificationVarsMap.CoupledConstraints set =
            Set.union matchesForUniVars matchesForTypeVars





        let overlapResults : (UnificationVarsMap.CoupledConstraints * OverlapCheckResult) list =
            matchesForBoth
            |> Set.toList
            |> List.map (fun coupledConstraints ->
                let remainingUniVars =
                    Set.difference coupledConstraints.allUniVars unificationVarsWeCanEliminate

                let remainingTypeVars = Set.difference coupledConstraints.typeVars typeVarsToReplace

                coupledConstraints,
                match Set.toList remainingUniVars, Set.toList remainingTypeVars with
                | [], [] -> FullOverlap

                | uniVar :: [], [] -> SingleUniVarLeft uniVar
                | headUniVar :: neckUniVar :: restUniVars, [] ->
                    MultipleUniVarsLeft (TOM.new_ headUniVar neckUniVar restUniVars)

                | [], typeVar :: [] -> SingleTypeVarLeft typeVar
                | [], headTypeVar :: neckTypeVar :: restTypeVars ->
                    MultipleTypeVarsLeft (TOM.new_ headTypeVar neckTypeVar restTypeVars)

                | uniVar :: [], typeVar :: [] -> SingleOfEachLeft (uniVar, typeVar)

                | uniVar :: [], headTypeVar :: neckTypeVar :: restTypeVars ->
                    SingleUniVarAndMultipleTypeVarsLeft (uniVar, TOM.new_ headTypeVar neckTypeVar restTypeVars)

                | headUniVar :: neckUniVar :: restUniVars, typeVar :: [] ->
                    SingleTypeVarAndMultipleUniVarsLeft (typeVar, TOM.new_ headUniVar neckUniVar restUniVars)

                | headUniVar :: neckUniVar :: restUniVars, headTypeVar :: neckTypeVar :: restTypeVars ->
                    MultipleOfBoth (
                        TOM.new_ headUniVar neckUniVar restUniVars,
                        TOM.new_ headTypeVar neckTypeVar restTypeVars
                    ))


        let getNormalisationInstructionAndAdjustedUniVarsMapKeys
            (constrs : UnificationVarsMap.CoupledConstraints)
            (overlap : OverlapCheckResult)
            (map : UnificationVarsMap)
            : NormalisationInstruction * UnificationVarsMap =

            let makeNormalisationInstruction' : UnificationResult -> TypeVariableId option -> NormalisationInstruction =
                makeNormalisationInstruction constrs.allUniVars constrs.typeVars

            // This `uniVarsMapWithKeysRemoved` still needs to have its values adjusted by the `normalisationInstr`, which we do just below this big match expression
            let normalisationInstr, uniVarsMapWithKeysRemoved =
                match overlap with
                | OverlapCheckResult.SingleUniVarLeft uniVar ->
                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                    map
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add uniVar (UnifResult (constrs.result, Set.empty))

                | OverlapCheckResult.SingleTypeVarLeft typeVar ->
                    let newUniVar = makeNewUniVar ()

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar newUniVar)) None,
                    map
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add newUniVar (UnifResult (constrs.result, Set.singleton typeVar))

                | OverlapCheckResult.SingleOfEachLeft (uniVar, typeVar) ->
                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                    map
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add uniVar (UnifResult (constrs.result, Set.singleton typeVar))

                | OverlapCheckResult.MultipleUniVarsLeft uniVarsLeft ->
                    if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                        let uniVarToPointTo = constrs.finalUniVar

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.empty))

                    else
                        /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                        let (TOM (head, neck, rest)) = uniVarsLeft
                        let uniVarToPointTo = head

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.addBulk (neck :: rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                        |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.empty))


                | OverlapCheckResult.MultipleTypeVarsLeft typeVars ->
                    let newUniVar = makeNewUniVar ()

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar newUniVar)) None,
                    map
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add newUniVar (UnifResult (constrs.result, Set.ofSeq typeVars))

                | OverlapCheckResult.SingleUniVarAndMultipleTypeVarsLeft (uniVar, typeVars) ->
                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                    map
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add uniVar (UnifResult (constrs.result, Set.ofSeq typeVars))


                | OverlapCheckResult.SingleTypeVarAndMultipleUniVarsLeft (typeVar, uniVarsLeft) ->
                    if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                        let uniVarToPointTo = constrs.finalUniVar

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.add constrs.finalUniVar (UnifResult (constrs.result, Set.singleton typeVar))

                    else
                        /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                        let (TOM (head, neck, rest)) = uniVarsLeft
                        let uniVarToPointTo = head

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.addBulk (neck :: rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                        |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.singleton typeVar))


                | OverlapCheckResult.MultipleOfBoth (uniVarsLeft, typeVars) ->
                    if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                        let uniVarToPointTo = constrs.finalUniVar

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.add constrs.finalUniVar (UnifResult (constrs.result, Set.ofSeq typeVars))

                    else
                        /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                        let (TOM (head, neck, rest)) = uniVarsLeft
                        let uniVarToPointTo = head

                        makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                        map
                        |> Map.removeKeys constrs.allUniVars
                        |> Map.addBulk (neck :: rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                        |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.ofSeq typeVars))


                | OverlapCheckResult.FullOverlap ->
                    // So this is the juicy case (I think)!!!
                    // This is the case where we actually put the logic of whether we replace the things referencing these coupled constraints with a concrete type (or type clash error) or if we generalise it with a new type variable if it's `None`!
                    // In other words, this is where we do either substitution or generalisation!!!

                    // @TODO: important! I think we need to arrange the normalisation instructions in a DAG, and then do a topological sort on them so that we can apply each norminstr in order, so that we don't end up doing a replacement containing old uniVars/typeVars after those have already been removed!


                    match constrs.result with
                    | None ->
                        // So we can generalise this bitch

                        let newTypeVar = makeNewTypeVar ()

                        makeNormalisationInstruction' (Ok (PTC.TypeVariable newTypeVar)) (Some newTypeVar),
                        map |> Map.removeKeys constrs.allUniVars

                    | Some result ->
                        match result with
                        | Ok constraint_ ->
                            // so we need to replace the uniVar by this specific constraint
                            makeNormalisationInstruction' (Ok constraint_) None,

                            map |> Map.removeKeys constrs.allUniVars

                        | Error e ->
                            makeNormalisationInstruction' (Error e) None,

                            map |> Map.removeKeys constrs.allUniVars


            let uniVarsWithValuesNormalised =
                applyNormInstrToUniVarsMap normalisationInstr uniVarsMapWithKeysRemoved

            normalisationInstr, uniVarsWithValuesNormalised


        let normalisationInstructions, adjustedUniVarMap =
            overlapResults
            |> List.fold
                (fun (normalisationInstrs, uniVarMap) (coupledConstraints, overlap) ->
                    // @TODO: I think we might need to keep the `NormalisationInstruction`s in the folded state as well, because I think we need to apply each new `NormalisationInstruction` to each preceding one as well, in order for all them to contain the target end state instead of the intermediate states that may be replaced in later `NormalisationInstruction`s.
                    let newNormalInstr, adjustedUniVarMap =
                        getNormalisationInstructionAndAdjustedUniVarsMapKeys coupledConstraints overlap uniVarMap

                    // We need to apply the new normalInstruction to the existing ones so we replace the uniVars and the like that need to be replaced
                    newNormalInstr
                    :: List.map (applyNorminstrToNormInstr newNormalInstr) normalisationInstrs,

                    adjustedUniVarMap)
                (List.empty, unificationVarsMap)


        let newPolyTypeContents : PolyTypeContents =
            normalisationInstructions
            |> Seq.fold (fun state normInstr -> applyNormalisationInstruction normInstr state) type_

        let newTypeVars : TypeVariableId list =
            normalisationInstructions |> List.choose _.newTypeVarOpt

        let newPolyType : PolyType =
            { forall = newTypeVars
              typeExpr = newPolyTypeContents }

        { self = newPolyType
          constrained = adjustedUniVarMap }



    let instantiateTypeVarsInPolyType
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyType)
        : SelfAndConstrainedUnificationVars =
        instantiateTypeVarsInPolyTypeContents
            (Set.ofList type_.forall)
            unificationVarsWeCanEliminate
            unificationVarsMap
            type_.typeExpr








    let rec inferTypeFromExpr (namesMap : TypedNamesMap) (expr : Ast.Expr) : SelfAndConstrainedUnificationVars =
        match expr with
        | Ast.StrVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.strType) Map.empty
        | Ast.IntVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.intType) Map.empty
        | Ast.ListVal exprs ->
            match exprs with
            | [] -> Sacuv.make Types.listType Map.empty
            | only :: [] ->
                let contentType = inferTypeFromExpr namesMap only
                Sacuv.make (Types.listTypeOf contentType.self) contentType.constrained

            | head :: rest ->
                let inferredHead = inferTypeFromExpr namesMap head

                let unifiedType, uniVarsMap, uniVarsAddedHere =
                    List.fold
                        (fun (unifiedTypeSoFar, uniVarsMap, uniVarsAddedHere) expr ->
                            let inferResult = inferTypeFromExpr namesMap expr
                            let unifiedType = unifyTwoTypes unifiedTypeSoFar inferResult.self

                            let combinedUniVarsMaps =
                                combineUnificationVarMapsSeq
                                    [ uniVarsMap; inferResult.constrained; unifiedType.constrained ]

                            unifiedType.self,
                            combinedUniVarsMaps.combined,
                            Set.unionMany [ uniVarsAddedHere; combinedUniVarsMaps.uniVarsAddedHere ])
                        (inferredHead.self, inferredHead.constrained, Set.empty)
                        rest

                instantiateTypeVarsInPolyType uniVarsAddedHere uniVarsMap unifiedType


        | Ast.TupleVal (first, second) ->
            let inferredFirst = inferTypeFromExpr namesMap first
            let inferredSecond = inferTypeFromExpr namesMap second

            let combineResult =
                combineTwoUnificationVarMaps inferredFirst.constrained inferredSecond.constrained

            let type_ = Types.tupleTypeOf inferredFirst.self inferredSecond.self

            instantiateTypeVarsInPolyType combineResult.uniVarsAddedHere combineResult.combined type_


        | Ast.LambdaVal (param, body) ->
            /// Make a new unification variable to act as the input parameter for the lambda
            let newUniVar = makeNewUniVar ()

            let paramPolyType =
                PolyTypeContents.UnificationVar newUniVar |> Types.makeEmptyPolyType

            /// Add the new name with its unification variable type into the names map that we inject into the body inferencing function
            let withNewUnificationVarAddedForParam =
                Map.add (LocalLower param) paramPolyType namesMap

            let bodyInferenceResult = inferTypeFromExpr withNewUnificationVarAddedForParam body



            let funcType = Types.funcTypeOf paramPolyType bodyInferenceResult.self

            instantiateTypeVarsInPolyType (Set.singleton newUniVar) bodyInferenceResult.constrained funcType

        //bodyInferenceResult.constrained
        //// @TODO: do we need to be generalising the function type if the unification vars are unconstrained?
        //// @TODO: 2nd question: *how* do we generalise that then lol? I *think* we do that by replacing constrained unification vars with normal concrete type shapes, and replace them with new "type variables"
        //// @TODO: I was thinking that maybe we can just do that by wrapping this function on the outside and doing this replacement automatically for all unification vars, but I don't think I can do that actually because I think there's no way to know in general if said unification vars are present outside of the current scope or not; so we might need to generalise them in those places where we brought them into the world!
        //|> Sacuv.make (Types.funcTypeOf paramPolyType bodyInferenceResult.self)


        | Ast.NamedVal name ->
            match Map.tryFind (LocalLower name) namesMap with
            | Some t -> Sacuv.make t Map.empty
            | None ->
                failwith
                    $"Couldn't resolve named value \"{name}\"! This is most likely due to it being an undeclared variable (which @TODO we still need to handle gracefully) but if not it might indicate that we're not passing all declared names down in the namesMap"


        | Ast.LetBindings (bindings, body) -> resolveAllNamesAndBody namesMap bindings body


        | Ast.FuncApplication (funcExpr, param) ->
            let paramTypeResult = inferTypeFromExpr namesMap param

            let newUniVar = makeNewUniVar ()

            let returnType =
                PolyTypeContents.UnificationVar newUniVar |> Types.makeEmptyPolyType

            let inferredFuncResult = inferTypeFromExpr namesMap funcExpr

            let funcRequiredType = Types.funcTypeOf paramTypeResult.self returnType
            let funcRequiredResult = unifyTwoTypes funcRequiredType inferredFuncResult.self

            let combinedUnifVarMap =
                [ paramTypeResult.constrained
                  inferredFuncResult.constrained
                  funcRequiredResult.constrained ]
                |> combineUnificationVarMapsSeq

            instantiateTypeVarsInPolyType
                (Set.add newUniVar combinedUnifVarMap.uniVarsAddedHere)
                combinedUnifVarMap.combined
                returnType






    /// The new strategy
    and resolveNamesTopologically
        (namesMap : TypedNamesMap)
        (namesAndExprs : Ast.LetBindingSingle seq)
        : BindingsResolutionResult =

        /// These don't need to be inferred because they already have explicit type annotations.
        /// @TODO: however! we still need to type check them internally
        let namesWithTypeAnnotations : TypedLocalNamesMap =
            namesAndExprs
            |> Seq.choose (fun binding -> binding.typeAnnotation |> Option.map (Tuple.makePair binding.name))
            |> Map.ofSeq



        let orderedBindings =
            namesAndExprs
            |> Seq.map (fun binding -> binding.name, binding.assignedExpr)
            |> sortBindingsTopologically


        let localNamesMap, uniVarsMap, uniVarsAddedHere =
            orderedBindings
            |> List.fold
                (fun (localNamesMap, uniVarsMap, uniVarsAddedHere) stronglyConnectedComponent ->
                    let combinedNamesMap = addLocalNamesMap localNamesMap namesMap

                    match stronglyConnectedComponent with
                    | DG.One (name, expr) ->
                        let isNameUsedRecursively =
                            getNamesUsedInExpr (Set.singleton name) expr |> Set.contains name

                        let newUniVarOpt =
                            if isNameUsedRecursively then
                                Some (makeNewUniVar ())
                            else
                                None

                        let withThisNameUniVarAdded : TypedNamesMap =
                            match newUniVarOpt with
                            | Some newUniVar ->
                                Map.add
                                    (LocalLower name)
                                    (PTC.UnificationVar newUniVar |> Types.makeEmptyPolyType)
                                    combinedNamesMap
                            | None -> combinedNamesMap

                        let inferredType = inferTypeFromExpr withThisNameUniVarAdded expr

                        let withThisBindingAdded : TypedLocalNamesMap =
                            Map.add name inferredType.self localNamesMap

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        let withThisNewUniVarAdded =
                            match newUniVarOpt with
                            | Some newUniVar -> Set.add newUniVar uniVarsAddedHere
                            | None -> uniVarsAddedHere

                        withThisBindingAdded,
                        combinedMapResult.combined,
                        Set.union combinedMapResult.uniVarsAddedHere withThisNewUniVarAdded






                    | DG.More namesAndBindings ->
                        let newUniVars =
                            namesAndBindings |> Seq.map (fun (name, _) -> name, makeNewUniVar ())

                        let withNewUniVarsAdded : TypedNamesMap =
                            newUniVars
                            |> Seq.fold
                                (fun map (name, uniVar) ->
                                    map
                                    |> Map.add
                                        (LocalLower name)
                                        (PTC.UnificationVar uniVar |> Types.makeEmptyPolyType))
                                combinedNamesMap


                        let newLocalNamesMap, newUniVarsMap, uniVarsAddedHere' =
                            namesAndBindings
                            |> Seq.fold
                                (fun (localNamesMap, uniVarsMap, uniVarsAddedHere') (name, expr) ->
                                    let inferredType = inferTypeFromExpr withNewUniVarsAdded expr

                                    let withThisBindingAdded : TypedLocalNamesMap =
                                        Map.add name inferredType.self localNamesMap

                                    let combinedMapResult =
                                        combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                                    withThisBindingAdded,
                                    combinedMapResult.combined,
                                    Set.union uniVarsAddedHere' combinedMapResult.uniVarsAddedHere)
                                (localNamesMap, uniVarsMap, Set.empty)


                        let withThisNewUniVarAdded =
                            Seq.map snd newUniVars
                            |> Set.ofSeq
                            |> Set.union uniVarsAddedHere
                            |> Set.union uniVarsAddedHere'

                        newLocalNamesMap, newUniVarsMap, withThisNewUniVarAdded)
                (namesWithTypeAnnotations, Map.empty, Set.empty)

        { inferredTypes = localNamesMap
          constrained = uniVarsMap
          unificationVarsIntroducedHere = uniVarsAddedHere }





    and resolveAllNamesAndBody
        (namesMap : TypedNamesMap)
        (letBindings : Ast.LetBindingSingle seq)
        (body : Ast.Expr)
        : SelfAndConstrainedUnificationVars =
        let bindingsResolutionResult = resolveNamesTopologically namesMap letBindings

        let combinedNamesMap =
            addLocalNamesMap bindingsResolutionResult.inferredTypes namesMap

        let bodyResult = inferTypeFromExpr combinedNamesMap body

        let combinedUniVarMap =
            combineTwoUnificationVarMaps bindingsResolutionResult.constrained bodyResult.constrained

        let sanitisedType : SelfAndConstrainedUnificationVars =
            instantiateTypeVarsInPolyTypeContents
                (Set.ofSeq bodyResult.self.forall)
                (Set.union bindingsResolutionResult.unificationVarsIntroducedHere combinedUniVarMap.uniVarsAddedHere)
                combinedUniVarMap.combined
                bodyResult.self.typeExpr

        sanitisedType

































    (*

        Type unification

    *)



    ///// Which entails generalising those unification vars with no constraints and converting them to polytypes, and just concretising everything else – but ofc only for those names and unification vars that are from the current let bindings, not just all of them willy nilly.
    //and convertUnificationResultsToNormalTypes
    //    //(namesMap : TypedNamesMap)
    //    //(localNames : LowerIdent set)
    //    (localUnificationVars : UnificationVarId set)
    //    (unificationResult : UnificationVarsMap)
    //    (typeToCleanUpAndReturn : PolyType)
    //    //: TypedLocalNamesMap =
    //    : SelfAndConstrainedUnificationVars =
    //    // @TODO: we need to figure out what we want from this function first.
    //    // I think we want it to do a few things:
    //    // 1. generalise all the unification vars that are not constrained
    //    // 2. concretise all the unification vars that are constrained
    //    // 3. remove all the above unification vars with their concrete types (whether poly or monomorphic) and put their concrete types in the return type
    //    //
    //    // – However! we need to decide whether we want this stuff to happen before or after we've inferred stuff from the let expression body, because we still need to be able to glean constraints from the body to the unification variables
    //    //      – Hm I actually think this should only run after inferring the body, because it's only then that we have all the relevant information, the body is not more special than any other let binding expression body in what it can tell us. So we should just infer the body as normal, and only *then* run this function on the results of that body inference along with everything else, and *then* we can concretise and generalise and shit
    //    // – So we also still need to decide how we're going to bubble up type errors to higher scopes, seeing as the names and unification variables are removed from being present at higher scopes than they are defined in
    //    //
    //    // 4. after swapping out all the concretised and generalised unification variables, replace the value of the things referencing those unification vars from the type to return, and *then* return that sanitised, concretised, and generalised return type from this function ✨

    //    ()



    //and generalisePolyTypeContents
    //    (localUnificationVars : UnificationVarId set)
    //    (unificationVarsMap : UnificationVarsMap)
    //    (typeToCleanUpAndReturn : PolyTypeContents)
    //    : SelfAndConstrainedUnificationVars =
    //    (*
    //    I think what we need to do here is:
    //    - similarly to the function below, clear out any uniVars or typeVars that were declared here and are therefore no longer needed
    //    - if there are still things in the grouping that survive the purge though, then keep that behind in the map
    //    - however if we do manage to completely get rid of a grouping, then for those unification vars that were removed and didn't have any constraints imposed on them, they can be generalised! and thus new type variable IDs can be generated here for them, to be exposed to the outside world for that value!
    //    *)
    //    ()






    and unifyTwoTypes (type1 : PolyType) (type2 : PolyType) : SelfAndConstrainedUnificationVars =
        let unified = unifyTwoTypeContents type1.typeExpr type2.typeExpr

        let combinedTypeVarConstraints =
            type1.forall @ type2.forall
            |> List.map (fun typeVar -> typeVar, UnificationVarsMap.getTypeVarConstraints typeVar unified.constrained)

        match unified.self with
        | Ok unifiedSelf ->
            instantiateTypeVarsInPolyTypeContents
                (List.map fst combinedTypeVarConstraints |> Set.ofList)
                unified.unificationVarsIntroducedHere
                unified.constrained
                unifiedSelf

        | Error e -> failwith "@TODO: implement the error case here"

    // Basically need to get which type variables have been narrowed to a concrete type, which have been married to which other type variables, and which unification variables, elminate those constraints that are only from local unification variables, if the unification variables are local, then only keep their constraints, and either way, eliminate those type variables that have been constrained, because now there are fewer free type variables in the expression. But then again if there are things in the polytype that have been *more* generalised (which tbh I'm not sure how that's possible after unification but whatever) then we'll end up with more free type variables.





    and unifyTwoTypeContents
        (type1 : PolyTypeContents)
        (type2 : PolyTypeContents)
        : {| self : Result<PolyTypeContents, UnificationError>
             unificationVarsIntroducedHere : UnificationVarId set
             constrained : UnificationVarsMap |}
        =
        match type1, type2 with
        | PTC.PrimitiveType prim1, PTC.PrimitiveType prim2 ->
            if prim1 = prim2 then
                {| self = Ok type1
                   unificationVarsIntroducedHere = Set.empty
                   constrained = Map.empty |}

            else
                {| self = UnificationClash (type1, type2) |> Error
                   unificationVarsIntroducedHere = Set.empty
                   constrained = Map.empty |}


        | PTC.ParametricType (name1, typeParams1), PTC.ParametricType (name2, typeParams2) ->
            if name1 = name2 then
                match List.zipList typeParams1 typeParams2 with
                | Ok combinedTypeParams ->
                    let paramsResults, globalResults =
                        combinedTypeParams
                        |> List.mapFold
                            (fun
                                (state :
                                    {| constrained : UnificationVarsMap
                                       unificationVarsIntroducedHere : UnificationVarId set |})
                                (param1, param2) ->
                                let unificationResult = unifyTwoTypeContents param1 param2

                                let combineResult =
                                    combineTwoUnificationVarMaps state.constrained unificationResult.constrained

                                unificationResult.self,
                                {| constrained = combineResult.combined

                                   unificationVarsIntroducedHere =
                                    Set.union
                                        state.unificationVarsIntroducedHere
                                        unificationResult.unificationVarsIntroducedHere
                                    |> Set.union combineResult.uniVarsAddedHere |})
                            {| constrained = Map.empty
                               unificationVarsIntroducedHere = Set.empty |}

                    let unificationVarMap = globalResults.constrained
                    let unificationVarsIntroducedHere = globalResults.unificationVarsIntroducedHere

                    {| self =
                        match Result.sequenceList paramsResults with
                        | Ok unifiedParams -> Ok (PTC.ParametricType (name1, unifiedParams))
                        | Error errs -> NEL.head errs |> Error

                       unificationVarsIntroducedHere = unificationVarsIntroducedHere
                       constrained = unificationVarMap |}


                | Error _ ->
                    {| self = UnificationClash (type1, type2) |> Error
                       unificationVarsIntroducedHere = Set.empty
                       constrained = Map.empty |}

            else
                {| self = UnificationClash (type1, type2) |> Error
                   unificationVarsIntroducedHere = Set.empty
                   constrained = Map.empty |}


        | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
            if uniVar1 = uniVar2 then
                {| self = Ok type1
                   unificationVarsIntroducedHere = Set.empty
                   constrained = Map.empty |}

            else
                /// Just so we have a consistent ordering so we avoid accidentally creating cycles of unification vars that don't lead anywhere
                let smallerUniVar, biggerUniVar = sortItems uniVar1 uniVar2

                /// The logic here being that we redirect one unification var to the other one. By convention we make the self type be the smaller uniVar, add an entry in the unification map to point it to the bigger one.
                /// The bigger one will keep pointing to whatever it's pointing to in other unification maps, and the smaller one in other maps will be unified with the bigger one, which will result in unifying the bigger one with a concrete type.
                let constrained : UnificationVarsMap =
                    Map.singleton smallerUniVar (UnifResult (PTC.UnificationVar biggerUniVar |> Ok |> Some, Set.empty))

                {| self = Ok (PTC.UnificationVar smallerUniVar)
                   unificationVarsIntroducedHere = Set.empty
                   constrained = constrained |}


        | PTC.TypeVariable typeVar1, PTC.TypeVariable typeVar2 ->
            if typeVar1 = typeVar2 then
                {| self = Ok type1
                   unificationVarsIntroducedHere = Set.empty
                   constrained = Map.empty |}

            else
                let newUnificationVar = makeNewUniVar ()

                let uniVarsMap : UnificationVarsMap =
                    Map.singleton newUnificationVar (UnifResult (None, Set.ofSeq [ typeVar1; typeVar2 ]))

                {| self = Ok (PTC.UnificationVar newUnificationVar)
                   unificationVarsIntroducedHere = Set.singleton newUnificationVar
                   constrained = uniVarsMap |}


        | PTC.UnificationVar uniVar, PTC.PrimitiveType prim
        | PTC.PrimitiveType prim, PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.PrimitiveType prim |> Ok |> Some, Set.empty))

            {| self = Ok (PTC.UnificationVar uniVar)
               unificationVarsIntroducedHere = Set.empty
               constrained = uniVarsMap |}


        | PTC.UnificationVar uniVar, PTC.ParametricType (name, typeParams)
        | PTC.ParametricType (name, typeParams), PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.ParametricType (name, typeParams) |> Ok |> Some, Set.empty))

            {| self = Ok (PTC.UnificationVar uniVar)
               unificationVarsIntroducedHere = Set.empty
               constrained = uniVarsMap |}


        | PTC.UnificationVar uniVar, PTC.TypeVariable typeVar
        | PTC.TypeVariable typeVar, PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (None, Set.singleton typeVar))

            {| self = Ok (PTC.UnificationVar uniVar)
               unificationVarsIntroducedHere = Set.empty
               constrained = uniVarsMap |}


        | PTC.TypeVariable typeVar, (PTC.PrimitiveType _ as concreteType)
        | (PTC.PrimitiveType _ as concreteType), PTC.TypeVariable typeVar

        | PTC.TypeVariable typeVar, (PTC.ParametricType _ as concreteType)
        | (PTC.ParametricType _ as concreteType), PTC.TypeVariable typeVar ->
            let newUnificationVar = makeNewUniVar ()

            let uniVarsMap : UnificationVarsMap =
                Map.singleton newUnificationVar (UnifResult (Ok concreteType |> Some, Set.singleton typeVar))

            {| self = Ok (PTC.UnificationVar newUnificationVar)
               unificationVarsIntroducedHere = Set.singleton newUnificationVar
               constrained = uniVarsMap |}


        | PTC.PrimitiveType _, PTC.ParametricType _
        | PTC.ParametricType _, PTC.PrimitiveType _ ->
            {| self = UnificationClash (type1, type2) |> Error
               unificationVarsIntroducedHere = Set.empty
               constrained = Map.empty |}


    //| PTC.InstantiatedTypeVariable (typeVar1, uniVar1), PTC.InstantiatedTypeVariable (typeVar2, uniVar2) ->
    //    if typeVar1 = typeVar2 then
    //        if uniVar1 = uniVar2 then
    //            {| self = Ok type1
    //               constrained = Map.empty |}
    //        else
    //            let uniVarMap : UnificationVarsMap =
    //                Map.singleton uniVar1 (PTC.InstantiatedTypeVariable (typeVar1, uniVar2) |> Ok |> Some)

    //            {| self = Ok (PTC.UnificationVar uniVar1)
    //               constrained = uniVarMap |}
    //    else if uniVar1 = uniVar2 then
    //        {| self = Ok (PTC.UnificationVar uniVar1)
    //           constrained =
    //            Map.singleton
    //                uniVar1
    //                (PTC.InstantiatedTypeVariable (NEL.append typeVar1 typeVar2, uniVar2)
    //                 |> Ok
    //                 |> Some) |}
    //    else
    //        let uniVarsMap : UnificationVarsMap =
    //            Map.singleton
    //                uniVar1
    //                (PTC.InstantiatedTypeVariable (NEL.append typeVar1 typeVar2, uniVar2)
    //                 |> Ok
    //                 |> Some)
    //            |> Map.add uniVar2 None

    //        {| self = Ok (PTC.UnificationVar uniVar1)
    //           constrained = uniVarsMap |}

    //| PTC.InstantiatedTypeVariable (typeVarNel, uniVar1), PTC.TypeVariable typeVar
    //| PTC.TypeVariable typeVar, PTC.InstantiatedTypeVariable (typeVarNel, uniVar1) ->
    //    if NEL.contains<_> typeVar typeVarNel then
    //        {| self = Ok (PTC.InstantiatedTypeVariable (typeVarNel, uniVar1))
    //           constrained = Map.empty |}

    //    else
    //        {| self = Ok (PTC.InstantiatedTypeVariable (NEL.cons typeVar typeVarNel, uniVar1))
    //           constrained = Map.empty |}


    //| PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar), PTC.UnificationVar uniVar
    //| PTC.UnificationVar uniVar, PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar) ->
    //    {| self = Ok (PTC.UnificationVar uniVar)
    //       constrained =
    //        Map.singleton uniVar (PTC.InstantiatedTypeVariable (typeVarNel, instantiatedUniVar) |> Ok |> Some) |}


    //| PTC.InstantiatedTypeVariable (_, uniVar), (PTC.PrimitiveType _ as concreteType)
    //| (PTC.PrimitiveType _ as concreteType), PTC.InstantiatedTypeVariable (_, uniVar)

    //| PTC.InstantiatedTypeVariable (_, uniVar), (PTC.ParametricType _ as concreteType)
    //| (PTC.ParametricType _ as concreteType), PTC.InstantiatedTypeVariable (_, uniVar) ->

    //    {| self = Ok (PTC.UnificationVar uniVar)
    //       constrained = Map.singleton uniVar (Ok concreteType |> Some) |}




    and unifyTwoTypeContentsResults
        (typeContentResult1 : Result<PolyTypeContents, UnificationError>)
        (typeContentResult2 : Result<PolyTypeContents, UnificationError>)
        : {| self : Result<PolyTypeContents, UnificationError>
             unificationVarsIntroducedHere : UnificationVarId set
             constrained : UnificationVarsMap |}
        =
        match typeContentResult1, typeContentResult2 with
        | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents typeContent1 typeContent2

        | Error e, _
        | _, Error e ->
            {| self = Error e
               unificationVarsIntroducedHere = Set.empty
               constrained = Map.empty |}



    and unifyTwoTypeContentsResultsOpts
        (typeOpt1 : Result<PolyTypeContents, UnificationError> option)
        (typeOpt2 : Result<PolyTypeContents, UnificationError> option)
        : {| self : Result<PolyTypeContents, UnificationError> option
             unificationVarsIntroducedHere : UnificationVarId set
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeContentsResults type1 type2

            {| self = Some result.self
               unificationVarsIntroducedHere = result.unificationVarsIntroducedHere
               constrained = result.constrained |}

        | Some type_, None
        | None, Some type_ ->
            {| self = Some type_
               unificationVarsIntroducedHere = Set.empty
               constrained = Map.empty |}

        | None, None ->
            {| self = None
               unificationVarsIntroducedHere = Set.empty
               constrained = Map.empty |}


    and unifyTwoTypeContentsOpts
        (typeOpt1 : PolyTypeContents option)
        (typeOpt2 : PolyTypeContents option)
        : {| self : Result<PolyTypeContents, UnificationError> option
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



    and unifyManyTypes (types : PolyType nel) : SelfAndConstrainedUnificationVars =
        let (NEL (first, rest)) = types

        let combinedType, combinedUnificationMap, uniVarsAddedHere =
            rest
            |> List.fold
                (fun (combinedType, combinedUniMap, uniVars) polyType ->
                    let result = unifyTwoTypes combinedType polyType

                    let combineResult = combineTwoUnificationVarMaps combinedUniMap result.constrained

                    result.self, combineResult.combined, Set.union uniVars combineResult.uniVarsAddedHere)
                (first, Map.empty, Set.empty)

        instantiateTypeVarsInPolyType uniVarsAddedHere combinedUnificationMap combinedType









    and combineTwoUnificationVarMaps
        (map1 : UnificationVarsMap)
        (map2 : UnificationVarsMap)
        : {| combined : UnificationVarsMap
             uniVarsAddedHere : UnificationVarId set |}
        =
        /// For those keys which are not shared, just simply add them in
        let singleFolder
            ((uniVars, uniVarsMap) : UnificationVarId set * UnificationVarsMap)
            (uniVar : UnificationVarId)
            (contents : UnifResOrRedirect)
            : UnificationVarId set * UnificationVarsMap =
            uniVars, Map.add uniVar contents uniVarsMap

        let folder
            ((uniVars, uniVarsMap) : UnificationVarId set * UnificationVarsMap)
            (uniVar : UnificationVarId)
            (contents1 : UnifResOrRedirect)
            (contents2 : UnifResOrRedirect)
            : UnificationVarId set * UnificationVarsMap =
            match contents1, contents2 with
            | UnifRedirect redirect1, UnifRedirect redirect2 ->
                // @TODO: I think we need to follow the redirects for both of these and then unify the results at the end... and then make sure all 3 of these redirects are pointing to that unified result
                let firstRedirectResult = UnificationVarsMap.findUnificationVarResult redirect1 map1

                let secondRedirectResult =
                    UnificationVarsMap.findUnificationVarResult redirect2 map2

                if fst firstRedirectResult = fst secondRedirectResult then
                    // Do they point to the same thing already
                    uniVars, Map.add uniVar (UnifRedirect (fst firstRedirectResult)) uniVarsMap

                else
                    let unifiedResult =
                        unifyTwoTypeContentsResultsOpts
                            (snd firstRedirectResult |> fst)
                            (snd secondRedirectResult |> fst)

                    let combinedTypeVars : TypeVariableId set =
                        Set.union (snd firstRedirectResult |> snd) (snd secondRedirectResult |> snd)

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    Set.union combineResult.uniVarsAddedHere unifiedResult.unificationVarsIntroducedHere,
                    combineResult.combined
                    |> Map.add uniVar (UnifResult (unifiedResult.self, combinedTypeVars))

            | UnifRedirect redirect, UnifResult (res, typeVars) ->
                // @TODO: I think we need to follow the redirect and then unify that redirect result with the result here... and then make sure we have two of the redirects (uniVar and redirect) pointing to that unified result

                let redirectResult = UnificationVarsMap.findUnificationVarResult redirect map1

                if fst redirectResult = uniVar then
                    // The redirect already points to this result
                    uniVars, Map.add uniVar (UnifResult (res, typeVars)) uniVarsMap

                else
                    let unifiedResult = unifyTwoTypeContentsResultsOpts (snd redirectResult |> fst) res

                    let combinedTypeVars : TypeVariableId set =
                        Set.union (snd redirectResult |> snd) typeVars

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    Set.union combineResult.uniVarsAddedHere unifiedResult.unificationVarsIntroducedHere,
                    combineResult.combined
                    |> Map.add uniVar (UnifResult (unifiedResult.self, combinedTypeVars))

            | UnifResult (res, typeVars), UnifRedirect redirect ->
                let redirectResult = UnificationVarsMap.findUnificationVarResult redirect map2

                if fst redirectResult = uniVar then
                    // The redirect already points to this result
                    uniVars, Map.add uniVar (UnifResult (res, typeVars)) uniVarsMap

                else
                    let unifiedResult = unifyTwoTypeContentsResultsOpts (snd redirectResult |> fst) res

                    let combinedTypeVars : TypeVariableId set =
                        Set.union (snd redirectResult |> snd) typeVars

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained


                    Set.union combineResult.uniVarsAddedHere unifiedResult.unificationVarsIntroducedHere,
                    combineResult.combined
                    |> Map.add uniVar (UnifResult (unifiedResult.self, combinedTypeVars))



            | UnifResult (res1, typeVars1), UnifResult (res2, typeVars2) ->
                let unifiedResult = unifyTwoTypeContentsResultsOpts res1 res2

                let combinedTypeVars : TypeVariableId set = Set.union typeVars1 typeVars2

                let combineResult =
                    combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                Set.union combineResult.uniVarsAddedHere unifiedResult.unificationVarsIntroducedHere,
                combineResult.combined
                |> Map.add uniVar (UnifResult (unifiedResult.self, combinedTypeVars))


        let uniVarsAddedHere, combinedMap =
            Map.foldAllEntries singleFolder singleFolder folder map1 map2 (Set.empty, Map.empty)

        {| combined = combinedMap
           uniVarsAddedHere = uniVarsAddedHere |}






    and combineUnificationVarMapsSeq
        (maps : UnificationVarsMap seq)
        : {| combined : UnificationVarsMap
             uniVarsAddedHere : UnificationVarId set |}
        =
        let uniVarsAddedHere, combinedMap =
            maps
            |> Seq.fold
                (fun (newUniVars, map) thisMap ->
                    let combineResult = combineTwoUnificationVarMaps thisMap map
                    Set.union combineResult.uniVarsAddedHere newUniVars, combineResult.combined)
                (Set.empty, Map.empty)

        {| combined = combinedMap
           uniVarsAddedHere = uniVarsAddedHere |}

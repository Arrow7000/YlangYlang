module DummyLang

open QualifiedSyntaxTree.Names

module DG = DependencyGraphs




type UnificationVarId =
    | UnificationVarId of System.Guid

    override this.ToString () =
        let (UnificationVarId id) = this
        "?" + String.trim 8 (string id)







/// This is what a skolem looks like outside the place that it is defined, i.e. the `a` and `b` in `forall a b. {{type expression using a and b}}`
type TypeVariableId =
    | TypeVariableId of System.Guid

    override this.ToString () =
        let (TypeVariableId id) = this
        String.trim 8 (string id)






type PolyTypeContents =
    /// Referencing a unification variable. To figure out what this unification var is you'll need to look into your local UnificationVarsMap (see below)
    | UnificationVar of UnificationVarId
    /// Referencing a *type variable* (not a unification variable!), which if it gets replaced we need to somehow propagate the message upwards that all instances of this type variable need to be replaced with the same thing – we only stop propagating that message upwards when we get to the polytype where this type var is declared in
    | TypeVariable of TypeVariableId
    /// A simple unparametric type, like `Int` or `String`
    | PrimitiveType of name : UpperNameValue
    /// Parametric types, like `List a` or `Maybe a`
    | ParametricType of name : UpperNameValue * typeParams : PolyTypeContents list

    override this.ToString () =
        match this with
        | UnificationVar uniVar -> string uniVar
        | TypeVariable typeVar -> string typeVar
        | PrimitiveType name -> string name
        | ParametricType (name, typeParams) ->
            match name with
            | (LocalUpper (UpperIdent "Arrow")) ->
                match typeParams with
                | [ from; to_ ] -> string from + " -> " + string to_
                | _ -> failwith "Arrow type should have exactly two type params"
            | (LocalUpper (UpperIdent "Tuple")) ->
                match typeParams with
                | [ a; b ] -> "( " + string a + ", " + string b + " )"
                | _ -> failwith "Tuple type should have exactly two type params"
            | _ -> string name + " " + String.concat " " (typeParams |> List.map string)

/// Alias for PolyTypeContents
type PTC = PolyTypeContents


type PolyType =
    { forall : TypeVariableId list
      typeExpr : PolyTypeContents }

    override this.ToString () =
        let bodyStr = string this.typeExpr

        match this.forall with
        | [] -> bodyStr
        | _ :: _ -> "forall " + String.concat " " (this.forall |> List.map string) + ". " + bodyStr


/// The context where we put the names with their type checked types
type TypedNamesMap = Map<LowerNameValue, PolyType>

/// A local context, we return these from functions that type check let bindings and top level declarations
type TypedLocalNamesMap = Map<LowerIdent, PolyType>


type UnificationError =
    | UnificationClash of PolyTypeContents * PolyTypeContents
    | UndefinedName of LowerNameValue

/// Either a unified polytypecontents or a unification error
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
            // If a uniVar doesn't have any constraints yet it may not be in the uniVarsmap, so we just return as if it was in the map with no constraints
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


    type private UnificationVarResultWithSteps =
        {
            /// The (reversed) list of steps we took before we got to the final unification var
            hops : UnificationVarId list
            finalUnificationVar : UnificationVarId
            result : UnificationResult option
            typeVars : TypeVariableId set
        }


    /// This gets the unification result, but also includes all the unification variables we encountered during our redirect hops
    let rec private findUnificationVarResultWithSteps uniVar map : UnificationVarResultWithSteps =
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

        let linkedUnificationVars : UnificationVarId set =
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



/// The result of every type inference or unification: contains the inferred or unified type itself, plus the map of constrained unification variables as gleaned from the inference/unification
type SelfAndConstrainedUnificationVars =
    { self : Result<PolyType, UnificationError>
      constrained : UnificationVarsMap }



module SelfAndConstrainedUnificationVars =
    let make self constrained : SelfAndConstrainedUnificationVars =
        { self = self
          constrained = constrained }


    let map f sacuv =
        { self = f sacuv.self
          constrained = sacuv.constrained }


    /// Bubble up the result-ness of the .self field onto the record as a whole
    let sequenceResult sacuv =
        sacuv.self
        |> Result.map (fun self ->
            {| constrained = sacuv.constrained
               self = self |})




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


    let funcTypeOf from to_ =
        { forall = from.forall @ to_.forall
          typeExpr = makeParametricType "Arrow" [ from.typeExpr; to_.typeExpr ] }






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










/// Represents what's left after we remove unification variables and type variables from the scope where they are declared
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




(*

    Type inference

*)




/// Gets all the value names referenced in an expression – note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because as far as the higher scopes are concerned those names do not exist.
/// @TODO: this should probably fail for shadowed names, but we'll assume for now that there are no shadowed names
let rec private getNamesUsedInExpr (namesToLookOutFor : LowerIdent set) (expr : Ast.Expr) : LowerIdent set =
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




let private sortBindingsTopologically
    (namesAndExprs : (LowerIdent * Ast.Expr) seq)
    : DG.OneOrMore<LowerIdent * Ast.Expr> list =
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






/// Combine multiple polytypes and combine all their type variables in a single polytype forall clause
let liftPolyTypesIntoPtc
    (makePolyTypeFromPtcs : PolyTypeContents list -> PolyTypeContents)
    (polyTypes : PolyType list)
    : PolyType =
    let typeVars = polyTypes |> List.collect _.forall

    { forall = typeVars
      typeExpr = polyTypes |> List.map _.typeExpr |> makePolyTypeFromPtcs }









module TypeInference =

    /// This is really the result of removing the locally declared unification variables and locally scoped type variables from the map, and either replace them with a uniVar or typeVar that is declared at a higher level, or if not: to replace all the instances of a type with the concrete type – or generalise it with a newly declared type variable if there are no constraints on it.
    /// This should contain all the information required to replace the uniVars and typeVars for _any_ PolyTypeContents, because we need to do this swapping out for both the self type and all the types in the unificationVarsMap. They have to be exactly the same operation, because both things need to have their uniVars and typeVars swapped out in exactly the same way.
    /// Now I'm assuming here that this swapping out should not have any additional effects of collapsing other entries in the uniVarsMap, which I do think is correct, but if it isn't true, then this operation would need to happen in multiple nested steps, which would be f***ing annoying again.
    type private TypeReplacement =
        {
            unificationVarsToReplace : UnificationVarId set
            typeVarsToReplace : TypeVariableId set

            toReplaceWith : Result<PolyTypeContents, UnificationError>
            /// If a new type var is created here we'll declare it here
            newTypeVarOpt : TypeVariableId option
        }


    let rec private applyTypeReplacement
        (tr : TypeReplacement)
        (polyTypeContents : PolyTypeContents)
        : PolyTypeContents =
        /// @TODO: handle the error case here still
        let replacement () =
            match tr.toReplaceWith with
            | Ok ptc -> ptc
            | Error e -> failwith "@TODO: need to handle the error case here still"

        match polyTypeContents with
        | PTC.UnificationVar uniVar ->
            if Set.contains uniVar tr.unificationVarsToReplace then
                replacement ()

            else
                PTC.UnificationVar uniVar

        | TypeVariable typeVar ->
            if Set.contains typeVar tr.typeVarsToReplace then
                replacement ()

            else
                TypeVariable typeVar

        | PrimitiveType prim -> PrimitiveType prim
        | ParametricType (name, ptcs) -> ParametricType (name, List.map (applyTypeReplacement tr) ptcs)


    let private applyTypeReplacementToUnificationError tr unifError =
        match unifError with
        | UnificationClash (a, b) -> UnificationClash (applyTypeReplacement tr a, applyTypeReplacement tr b)
        | UndefinedName name -> UndefinedName name

    let private applyTypeReplacementToResult
        (tr : TypeReplacement)
        (polyTypeContentsResult : UnificationResult)
        : UnificationResult =
        match polyTypeContentsResult with
        | Ok polyTypeContents -> applyTypeReplacement tr polyTypeContents |> Ok
        | Error e -> applyTypeReplacementToUnificationError tr e |> Error




    let private applyTypeReplacementToPolyType (normInstr : TypeReplacement) (polyType : PolyType) : PolyType =
        let result = applyTypeReplacement normInstr polyType.typeExpr

        { typeExpr = result
          forall =
            let newForAlls =
                polyType.forall
                |> List.filter (fun typeVar -> Set.contains typeVar normInstr.typeVarsToReplace |> not)

            match normInstr.newTypeVarOpt with
            | Some newTypeVar -> newTypeVar :: newForAlls
            | None -> newForAlls }


    let private applyTypeReplacementToPolyTypeResult
        (tr : TypeReplacement)
        (polyTypeResult : Result<PolyType, UnificationError>)
        : Result<PolyType, UnificationError> =
        match polyTypeResult with
        | Ok polyTypeContents -> applyTypeReplacementToPolyType tr polyTypeContents |> Ok
        | Error e -> applyTypeReplacementToUnificationError tr e |> Error


    let private applyTypeReplacementToPtcResultOpt
        (tr : TypeReplacement)
        (polyTypeResultOpt : UnificationResult option)
        : UnificationResult option =
        polyTypeResultOpt |> Option.map (applyTypeReplacementToResult tr)



    let private applyTypeReplacementToUniVarsMap
        (tr : TypeReplacement)
        (map : UnificationVarsMap)
        : UnificationVarsMap =
        map
        |> Map.map (fun _ redirectOrResult ->
            match redirectOrResult with
            | UnifRedirect uniVar ->
                // @TODO: we should probably remove this from the filter if it's in the set of uniVars to remove – but only do this once I'm sure that no redirect chains will be broken!
                UnifRedirect uniVar

            | UnifResult (typeResultOpt, typeVars) ->
                let newTypeVars : TypeVariableId set =
                    Set.difference typeVars tr.typeVarsToReplace
                    |> match tr.newTypeVarOpt with
                       | Some newTypeVar -> Set.add newTypeVar
                       | None -> id

                UnifResult (applyTypeReplacementToPtcResultOpt tr typeResultOpt, newTypeVars))




    /// Works equally well with TypedNamesMaps and TypedLocalNamesMaps
    let private applyNormInstrToTypedNamesMap
        (tr : TypeReplacement)
        (namesMap : Map<'Name, PolyType>)
        : Map<'Name, PolyType> =
        namesMap |> Map.map (fun _ -> applyTypeReplacementToPolyType tr)


    /// Get the coupled constraints for the provided typeVars and uniVars from the given uniVarsMap
    let getCoupledConstraintsSet
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        : UnificationVarsMap.CoupledConstraints set =
        let matchesForUniVars : UnificationVarsMap.CoupledConstraints set =
            unificationVarsWeCanEliminate
            |> Set.map (fun uniVar -> UnificationVarsMap.getAllJoinedUnificationVars uniVar unificationVarsMap)

        let matchesForTypeVars : UnificationVarsMap.CoupledConstraints set =
            typeVarsToReplace
            |> Set.choose (fun typeVar -> UnificationVarsMap.getTypeVarConstraints typeVar unificationVarsMap)

        // This should now include all the entries that any of the uniVars and typeVars here touch
        Set.union matchesForUniVars matchesForTypeVars




    let private coupledConstraintToTypeReplacement
        (typeVarsWeCanEliminate : TypeVariableId set)
        (uniVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        : {| replacementInstruction : TypeReplacement
             replacedUniVarsMap : UnificationVarsMap |}
        =
        let overlap : OverlapCheckResult =
            //// @TODO: not sure this Set.differencing actually serves any purpose. I think my thinking was that since these will all need to be eliminated anyway we may as well just get rid of them in the same step, but I'm not 100% sure if this makes sense/helps anymore. Same goes for the typeVars version.
            let remainingUniVars = Set.difference constrs.allUniVars uniVarsWeCanEliminate
            let remainingTypeVars = Set.difference constrs.typeVars typeVarsWeCanEliminate


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
                )


        let makeNormalisationInstruction'
            (rplcmnt : UnificationResult)
            (newTypeVarOpt : TypeVariableId option)
            : TypeReplacement =
            { unificationVarsToReplace = constrs.allUniVars
              typeVarsToReplace = constrs.typeVars

              toReplaceWith = rplcmnt
              newTypeVarOpt = newTypeVarOpt }


        let typeReplInstr, uniVarsMapWithKeysRemoved =
            match overlap with
            | OverlapCheckResult.SingleUniVarLeft uniVar ->
                makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                uniVarsMap
                |> Map.removeKeys constrs.allUniVars
                |> Map.add uniVar (UnifResult (constrs.result, Set.empty))

            | OverlapCheckResult.SingleTypeVarLeft typeVar ->
                match constrs.result with
                | Some unificationResult ->
                    makeNormalisationInstruction' unificationResult None,
                    uniVarsMap |> Map.removeKeys constrs.allUniVars

                | None ->
                    makeNormalisationInstruction' (Ok (PTC.TypeVariable typeVar)) None,
                    uniVarsMap |> Map.removeKeys constrs.allUniVars


            | OverlapCheckResult.SingleOfEachLeft (uniVar, typeVar) ->
                makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                uniVarsMap
                |> Map.removeKeys constrs.allUniVars
                |> Map.add uniVar (UnifResult (constrs.result, Set.singleton typeVar))

            | OverlapCheckResult.MultipleUniVarsLeft uniVarsLeft ->
                if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                    let uniVarToPointTo = constrs.finalUniVar

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.empty))

                else
                    /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                    let (TOM (head, neck, rest)) = uniVarsLeft
                    let uniVarToPointTo = head

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.addBulk (neck :: rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                    |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.empty))


            | OverlapCheckResult.MultipleTypeVarsLeft typeVars ->
                let newUniVar = makeNewUniVar ()

                makeNormalisationInstruction' (Ok (PTC.UnificationVar newUniVar)) None,
                uniVarsMap
                |> Map.removeKeys constrs.allUniVars
                |> Map.add newUniVar (UnifResult (constrs.result, Set.ofSeq typeVars))


            | OverlapCheckResult.SingleUniVarAndMultipleTypeVarsLeft (uniVar, typeVars) ->
                makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVar)) None,
                uniVarsMap
                |> Map.removeKeys constrs.allUniVars
                |> Map.add uniVar (UnifResult (constrs.result, Set.ofSeq typeVars))


            | OverlapCheckResult.SingleTypeVarAndMultipleUniVarsLeft (typeVar, uniVarsLeft) ->
                if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                    let uniVarToPointTo = constrs.finalUniVar

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add constrs.finalUniVar (UnifResult (constrs.result, Set.singleton typeVar))

                else
                    /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                    let (TOM (head, neck, rest)) = uniVarsLeft
                    let uniVarToPointTo = head

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.addBulk (neck :: rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                    |> Map.add uniVarToPointTo (UnifResult (constrs.result, Set.singleton typeVar))


            | OverlapCheckResult.MultipleOfBoth (uniVarsLeft, typeVars) ->
                if TOM.contains<_> constrs.finalUniVar uniVarsLeft then
                    let uniVarToPointTo = constrs.finalUniVar

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add constrs.finalUniVar (UnifResult (constrs.result, Set.ofSeq typeVars))

                else
                    /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result
                    let (TOM (head, neck, rest)) = uniVarsLeft
                    let uniVarToPointTo = head

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
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
                    uniVarsMap |> Map.removeKeys constrs.allUniVars

                | Some result ->
                    match result with
                    | Ok constraint_ ->
                        // so we need to replace the uniVar by this specific constraint
                        makeNormalisationInstruction' (Ok constraint_) None,

                        uniVarsMap |> Map.removeKeys constrs.allUniVars

                    | Error e ->
                        makeNormalisationInstruction' (Error e) None,

                        uniVarsMap |> Map.removeKeys constrs.allUniVars

        {| replacementInstruction = typeReplInstr
           replacedUniVarsMap = applyTypeReplacementToUniVarsMap typeReplInstr uniVarsMapWithKeysRemoved |}



    let private replaceCoupledConstraintsInUniVarsMap
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        : UnificationVarsMap =
        coupledConstraintToTypeReplacement typeVarsToReplace unificationVarsWeCanEliminate constrs uniVarsMap
        |> _.replacedUniVarsMap




    /// @TODO: we should use this in `combineTwoUnificationVarMaps` to simplify stuff massively by not needing to pass `.uniVarsAddedHere` out from all over the place
    let instantiateTypeVarsInUniVarsMap
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        : UnificationVarsMap =
        let matchesForBoth =
            getCoupledConstraintsSet typeVarsToReplace unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun varsMap coupledConstraints ->
                replaceCoupledConstraintsInUniVarsMap
                    Set.empty
                    unificationVarsWeCanEliminate
                    coupledConstraints
                    varsMap)
            unificationVarsMap







    let instantiateTypeVarsInUniVarsMapAndLocalNamesMap
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (localNamesMap : TypedLocalNamesMap)
        (unificationVarsMap : UnificationVarsMap)
        : TypedLocalNamesMap * UnificationVarsMap =
        let matchesForBoth =
            getCoupledConstraintsSet typeVarsToReplace unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun (namesMap, varsMap) coupledConstraints ->
                let replacement =
                    coupledConstraintToTypeReplacement
                        Set.empty
                        unificationVarsWeCanEliminate
                        coupledConstraints
                        varsMap

                applyNormInstrToTypedNamesMap replacement.replacementInstruction namesMap,
                replacement.replacedUniVarsMap)
            (localNamesMap, unificationVarsMap)



    let private replaceCoupledConstraintsInTypeAndUniVarsMap
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        (type_ : PolyTypeContents)
        : SelfAndConstrainedUnificationVars =
        let replacement =
            coupledConstraintToTypeReplacement typeVarsToReplace unificationVarsWeCanEliminate constrs uniVarsMap

        let normalisedPtc = applyTypeReplacement replacement.replacementInstruction type_

        let newPolyType : PolyType =
            { forall = Option.toList replacement.replacementInstruction.newTypeVarOpt
              typeExpr = normalisedPtc }

        { self = Ok newPolyType
          constrained = replacement.replacedUniVarsMap }


    /// @TODO: we probably do still need to do this to prevent old uniVars from sticking around... maybe? Unless we only ever add things onto a local names map inside a scope and never pass it up out of a scope, in which case we may not need to? But tbh we do instantiate+replace uniVars and typeVars quite frequently, even not only when passing constraints up a scope, so maybe there is a good chance we'd be using a names map with out of date uniVars/typeVars inside it?
    let private replaceCoupledConstraintsInTypedLocalNamesMap
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (localNamesMap : TypedLocalNamesMap)
        (uniVarsMap : UnificationVarsMap)
        : TypedLocalNamesMap * UnificationVarsMap =
        let replacement =
            coupledConstraintToTypeReplacement typeVarsToReplace unificationVarsWeCanEliminate constrs uniVarsMap

        applyNormInstrToTypedNamesMap replacement.replacementInstruction localNamesMap, replacement.replacedUniVarsMap



    let private replaceCoupledConstraintsInSacuv
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (coupledConstraints : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        (type_ : PolyType)
        : SelfAndConstrainedUnificationVars =
        replaceCoupledConstraintsInTypeAndUniVarsMap
            (Set.ofList type_.forall |> Set.union typeVarsToReplace)
            unificationVarsWeCanEliminate
            coupledConstraints
            uniVarsMap
            type_.typeExpr


    let private replaceCoupledConstraintsInSacuv'
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        (polyTypeResult : Result<PolyType, UnificationError>)
        : SelfAndConstrainedUnificationVars =
        let replacement =
            coupledConstraintToTypeReplacement typeVarsToReplace unificationVarsWeCanEliminate constrs uniVarsMap

        let normalisedPolyType =
            applyTypeReplacementToPolyTypeResult replacement.replacementInstruction polyTypeResult

        { self = normalisedPolyType
          constrained = replacement.replacedUniVarsMap }





    let concretiseAndGeneralise
        (typeVarsToReplace : TypeVariableId set)
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyTypeContents)
        : SelfAndConstrainedUnificationVars =
        let matchesForBoth =
            getCoupledConstraintsSet typeVarsToReplace unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun sacuv coupledConstraints ->
                let replaced =
                    replaceCoupledConstraintsInSacuv'
                        (*
                    @TODO: tests are now failing again with the same un-removed type and uni vars as before looool. I think maybe the way to tackle that is to only really extract and remove the next CoupledConstraints at a time, because otherwise the latterly defined CCs may end up containing out-of-date, already-replaced uni and type vars that we don't want to have sticking around anymore. Soooo maybe instead of a fold over a fixed list of CCs we do a recursive function call over "the next" CC and keep recursing as long as there are still CCs to be found/replaced, and only return the loop when there aren't any?
                    That would be less elegant than I was hoping in this lil refactor/cleanup before making my commit, which is to separate out the creation of the CCs with the application of them into type replacements, but even still we don't need to pass both the removable type and uni vars *and* the CCs all in at the same time, because we only pass in the removables, and then internally based on those removables we generate the first CC, which we use to generate the first TypeReplacement (TR), apply it to any uniVarsMaps and polytypes, and then recurse for the next one. 
                    One problem however which may crop up, is that we do still want to separate out the replaceents-to-make from the data structures we're applying those replacements to, because we may or may not want to apply those same changes to a namesMap, and if all we get is a black box that spits out a replaced version of the uniVarsMap then we don't get the information needd to apply those same changes to the namesMap. Soooo maybe we *do* need to generate a list of TRs first (based on generating only one CC at a time?) and cumulatively updating the destination types in every TR with the lattermost destination type as will happen if you applied every TR in sequence, leaving you with no waifs and stray types in your uniVarsMap/polytype/namesMap? Yeah I think that might be the best way to do it actually...! So perhaps finishing cleaning up this current refactor and then implement the new approach as outlined above :partyparrot:
                    *)
                        //"^see above comment"

                        (sacuv.self
                         |> Result.map (_.forall >> Set.ofList)
                         |> Result.defaultValue Set.empty)
                        unificationVarsWeCanEliminate
                        coupledConstraints
                        sacuv.constrained
                        sacuv.self

                replaced)
            { self = Types.makeEmptyPolyType type_ |> Ok
              constrained = unificationVarsMap }



    let instantiateTypeVarsInPolyType
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyType)
        : SelfAndConstrainedUnificationVars =
        concretiseAndGeneralise
            (Set.ofList type_.forall)
            unificationVarsWeCanEliminate
            unificationVarsMap
            type_.typeExpr


    let instantiateTypeVarsInPolyTypeResult
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : Result<PolyType, UnificationError>)
        : SelfAndConstrainedUnificationVars =
        let matchesForUniVars : UnificationVarsMap.CoupledConstraints set =
            unificationVarsWeCanEliminate
            |> Set.map (fun uniVar -> UnificationVarsMap.getAllJoinedUnificationVars uniVar unificationVarsMap)

        let matchesForTypeVars : UnificationVarsMap.CoupledConstraints set =
            type_
            |> Result.map (_.forall >> Set.ofList)
            |> Result.defaultValue Set.empty
            |> Set.choose (fun typeVar -> UnificationVarsMap.getTypeVarConstraints typeVar unificationVarsMap)

        /// This should now include all the entries that any of the uniVars and typeVars here touch
        let matchesForBoth : UnificationVarsMap.CoupledConstraints set =
            Set.union matchesForUniVars matchesForTypeVars

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun sacuv coupledConstraints ->
                replaceCoupledConstraintsInSacuv'
                    (sacuv.self
                     |> Result.map (_.forall >> Set.ofList)
                     |> Result.defaultValue Set.empty)
                    unificationVarsWeCanEliminate
                    coupledConstraints
                    sacuv.constrained
                    sacuv.self)
            { self = type_
              constrained = unificationVarsMap }












    let rec inferTypeFromExpr (namesMap : TypedNamesMap) (expr : Ast.Expr) : SelfAndConstrainedUnificationVars =
        match expr with
        | Ast.StrVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.strType |> Ok) Map.empty
        | Ast.IntVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.intType |> Ok) Map.empty
        | Ast.ListVal exprs ->
            match exprs with
            | [] -> Sacuv.make (Ok Types.listType) Map.empty
            | only :: [] ->
                let contentType = inferTypeFromExpr namesMap only
                Sacuv.make (contentType.self |> Result.map Types.listTypeOf) contentType.constrained

            | head :: rest ->
                let inferredHead = inferTypeFromExpr namesMap head

                let unified =
                    List.fold
                        (fun unifiedSoFar expr ->
                            let inferResult = inferTypeFromExpr namesMap expr
                            let unifiedType = unifyTwoTypeResults unifiedSoFar.self inferResult.self

                            let combinedUniVarsMaps =
                                combineUnificationVarMapsSeq
                                    [ unifiedSoFar.constrained; inferResult.constrained; unifiedType.constrained ]

                            Sacuv.make unifiedType.self combinedUniVarsMaps)
                        inferredHead
                        rest

                Sacuv.make (Result.map Types.listTypeOf unified.self) unified.constrained


        | Ast.TupleVal (first, second) ->
            let inferredFirst = inferTypeFromExpr namesMap first
            let inferredSecond = inferTypeFromExpr namesMap second

            let combineResult =
                combineTwoUnificationVarMaps inferredFirst.constrained inferredSecond.constrained


            match inferredFirst.self, inferredSecond.self with
            | Ok inferredFirst', Ok inferredSecond' ->
                let type_ = Types.tupleTypeOf inferredFirst' inferredSecond'

                instantiateTypeVarsInPolyType Set.empty combineResult type_

            | Error e, _
            | _, Error e -> Sacuv.make (Error e) combineResult


        | Ast.LambdaVal (param, body) ->
            /// Make a new unification variable to act as the input parameter for the lambda
            let newUniVar = makeNewUniVar ()

            let paramPolyType =
                PolyTypeContents.UnificationVar newUniVar |> Types.makeEmptyPolyType

            /// Add the new name with its unification variable type into the names map that we inject into the body inferencing function
            let withNewUnificationVarAddedForParam =
                Map.add (LocalLower param) paramPolyType namesMap

            let bodyInferenceResult =
                inferTypeFromExpr withNewUnificationVarAddedForParam body
                |> Sacuv.map (Result.map (Types.funcTypeOf paramPolyType))

            let instantiatedType =
                instantiateTypeVarsInPolyTypeResult
                    (Set.singleton newUniVar)
                    bodyInferenceResult.constrained
                    bodyInferenceResult.self

            instantiatedType


        | Ast.NamedVal name ->
            match Map.tryFind (LocalLower name) namesMap with
            | Some t -> Sacuv.make (Ok t) Map.empty
            | None -> Sacuv.make (Error (UndefinedName (LocalLower name))) Map.empty


        | Ast.LetBindings (bindings, body) -> resolveAllLetBindingsAndBody namesMap bindings body


        | Ast.FuncApplication (funcExpr, param) ->
            let paramTypeResult = inferTypeFromExpr namesMap param

            let newUniVar = makeNewUniVar ()

            let returnType =
                PolyTypeContents.UnificationVar newUniVar |> Types.makeEmptyPolyType

            let inferredFuncResult = inferTypeFromExpr namesMap funcExpr

            match paramTypeResult.self, inferredFuncResult.self with
            | Ok paramTypeSelf, Ok inferredFuncSelf ->
                let funcRequiredType = Types.funcTypeOf paramTypeSelf returnType

                let funcRequiredResult = unifyTwoTypes funcRequiredType inferredFuncSelf

                let combinedUnifVarMap =
                    [ paramTypeResult.constrained
                      inferredFuncResult.constrained
                      funcRequiredResult.constrained ]
                    |> combineUnificationVarMapsSeq

                instantiateTypeVarsInPolyType (Set.singleton newUniVar) combinedUnifVarMap returnType

            | Error e, _
            | _, Error e ->
                let combinedUniVarsMaps =
                    combineTwoUnificationVarMaps paramTypeResult.constrained inferredFuncResult.constrained

                instantiateTypeVarsInPolyTypeResult (Set.singleton newUniVar) combinedUniVarsMaps (Error e)




    /// The new strategy
    and resolveNamesTopologically
        (namesMap : TypedNamesMap)
        (namesAndExprs : Ast.LetBindingSingle seq)
        : {| inferredTypes : TypedLocalNamesMap
             constrained : UnificationVarsMap |}
        =

        /// These don't need to be inferred because they already have explicit type annotations.
        /// @TODO: however! we still need to type check them internally and surface any errors to the top level
        let namesWithTypeAnnotations : TypedLocalNamesMap =
            namesAndExprs
            |> Seq.choose (fun binding -> binding.typeAnnotation |> Option.map (Tuple.makePair binding.name))
            |> Map.ofSeq



        let orderedBindings =
            namesAndExprs
            |> Seq.map (fun binding -> binding.name, binding.assignedExpr)
            |> sortBindingsTopologically


        let localNamesMap, uniVarsMap =
            orderedBindings
            |> List.fold
                (fun (localNamesMap, uniVarsMap) stronglyConnectedComponent ->
                    let combinedNamesMap : TypedNamesMap = addLocalNamesMap localNamesMap namesMap

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

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        match inferredType.self with
                        | Ok okSelf ->
                            let withThisBindingAdded : TypedLocalNamesMap = Map.add name okSelf localNamesMap


                            instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                                Set.empty
                                (newUniVarOpt |> Option.toList |> Set.ofList)
                                withThisBindingAdded
                                combinedMapResult

                        | Error e -> localNamesMap, combinedMapResult



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


                        let newLocalNamesMap, newUniVarsMap =
                            namesAndBindings
                            |> Seq.fold
                                (fun (localNamesMap, uniVarsMap) (name, expr) ->
                                    let inferredType = inferTypeFromExpr withNewUniVarsAdded expr

                                    let withThisBindingAdded : TypedLocalNamesMap =
                                        match inferredType.self with
                                        | Ok inferredSelf -> Map.add name inferredSelf localNamesMap
                                        | Error e -> localNamesMap

                                    let combinedMapResult =
                                        combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                                    withThisBindingAdded, combinedMapResult)
                                (localNamesMap, uniVarsMap)

                        instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                            Set.empty
                            (newUniVars |> Seq.map snd |> Set.ofSeq)
                            newLocalNamesMap
                            newUniVarsMap

                )
                (namesWithTypeAnnotations, Map.empty)

        {| inferredTypes = localNamesMap
           constrained = uniVarsMap |}





    and resolveAllLetBindingsAndBody
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
            instantiateTypeVarsInPolyTypeResult Set.empty combinedUniVarMap bodyResult.self

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

        let makeNormInstrToReplaceTypeVarWithUniVar
            (typeVar : TypeVariableId)
            (uniVar : UnificationVarId)
            : TypeReplacement =
            { unificationVarsToReplace = Set.empty
              typeVarsToReplace = Set.singleton typeVar
              toReplaceWith = PTC.UnificationVar uniVar |> Ok
              newTypeVarOpt = None }

        let swapTypeVarWithUniVar
            (typeVar : TypeVariableId)
            (uniVar : UnificationVarId)
            (type_ : PolyTypeContents)
            : PolyTypeContents =
            let normInstr = makeNormInstrToReplaceTypeVarWithUniVar typeVar uniVar
            applyTypeReplacement normInstr type_


        let allTypeVars = type1.forall @ type2.forall

        let typeVarsToUniVar =
            allTypeVars |> List.map (fun typeVar -> typeVar, makeNewUniVar ())

        let replacedType1 =
            typeVarsToUniVar
            |> List.fold (fun type_ (typeVar, uniVar) -> swapTypeVarWithUniVar typeVar uniVar type_) type1.typeExpr

        let replacedType2 =
            typeVarsToUniVar
            |> List.fold (fun type_ (typeVar, uniVar) -> swapTypeVarWithUniVar typeVar uniVar type_) type2.typeExpr


        let unified = unifyTwoTypeContents replacedType1 replacedType2


        match unified.self with
        | Ok okSelf ->
            concretiseAndGeneralise
                (List.map fst typeVarsToUniVar |> Set.ofList)
                (List.map snd typeVarsToUniVar |> Set.ofList)
                unified.constrained
                okSelf.typeExpr

        | Error e ->
            { self = Error e
              constrained = unified.constrained }




    // Basically need to get which type variables have been narrowed to a concrete type, which have been married to which other type variables, and which unification variables, elminate those constraints that are only from local unification variables, if the unification variables are local, then only keep their constraints, and either way, eliminate those type variables that have been constrained, because now there are fewer free type variables in the expression. But then again if there are things in the polytype that have been *more* generalised (which tbh I'm not sure how that's possible after unification but whatever) then we'll end up with more free type variables.





    and unifyTwoTypeContents (type1 : PolyTypeContents) (type2 : PolyTypeContents) : SelfAndConstrainedUnificationVars =
        match type1, type2 with
        | PTC.PrimitiveType prim1, PTC.PrimitiveType prim2 ->
            if prim1 = prim2 then
                { self = type1 |> Types.makeEmptyPolyType |> Ok
                  constrained = Map.empty }

            else
                { self = UnificationClash (type1, type2) |> Error
                  constrained = Map.empty }


        | PTC.ParametricType (name1, typeParams1), PTC.ParametricType (name2, typeParams2) ->
            if name1 = name2 then
                match List.zipList typeParams1 typeParams2 with
                | Ok combinedTypeParams ->
                    let paramsResults, unificationVarMap =
                        combinedTypeParams
                        |> List.mapFold
                            (fun state (param1, param2) ->
                                let unificationResult = unifyTwoTypeContents param1 param2

                                let combineResult = combineTwoUnificationVarMaps state unificationResult.constrained

                                unificationResult.self, combineResult)
                            Map.empty

                    { self =
                        match Result.sequenceList paramsResults with
                        | Ok unifiedParams ->

                            liftPolyTypesIntoPtc (fun p -> PTC.ParametricType (name1, p)) unifiedParams
                            |> Ok
                        | Error errs -> NEL.head errs |> Error

                      constrained = unificationVarMap }


                | Error _ ->
                    { self = UnificationClash (type1, type2) |> Error
                      constrained = Map.empty }

            else
                { self = UnificationClash (type1, type2) |> Error
                  constrained = Map.empty }


        | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
            if uniVar1 = uniVar2 then
                { self = type1 |> Types.makeEmptyPolyType |> Ok
                  constrained = Map.empty }

            else
                /// Just so we have a consistent ordering so we avoid accidentally creating cycles of unification vars that don't lead anywhere
                let smallerUniVar, biggerUniVar = sortItems uniVar1 uniVar2

                /// The logic here being that we redirect one unification var to the other one. By convention we make the self type be the smaller uniVar, add an entry in the unification map to point it to the bigger one.
                /// The bigger one will keep pointing to whatever it's pointing to in other unification maps, and the smaller one in other maps will be unified with the bigger one, which will result in unifying the bigger one with a concrete type.
                let constrained : UnificationVarsMap =
                    Map.singleton smallerUniVar (UnifResult (PTC.UnificationVar biggerUniVar |> Ok |> Some, Set.empty))

                { self = PTC.UnificationVar smallerUniVar |> Types.makeEmptyPolyType |> Ok
                  constrained = constrained }


        | PTC.TypeVariable typeVar1, PTC.TypeVariable typeVar2 ->
            if typeVar1 = typeVar2 then
                { self = type1 |> Types.makeEmptyPolyType |> Ok
                  constrained = Map.empty }

            else
                let newUnificationVar = makeNewUniVar ()

                let uniVarsMap : UnificationVarsMap =
                    Map.singleton newUnificationVar (UnifResult (None, Set.ofSeq [ typeVar1; typeVar2 ]))

                concretiseAndGeneralise
                    Set.empty
                    (Set.singleton newUnificationVar)
                    uniVarsMap
                    (PTC.UnificationVar newUnificationVar)



        | PTC.UnificationVar uniVar, PTC.PrimitiveType prim
        | PTC.PrimitiveType prim, PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.PrimitiveType prim |> Ok |> Some, Set.empty))

            { self = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
              constrained = uniVarsMap }


        | PTC.UnificationVar uniVar, PTC.ParametricType (name, typeParams)
        | PTC.ParametricType (name, typeParams), PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.ParametricType (name, typeParams) |> Ok |> Some, Set.empty))

            { self = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
              constrained = uniVarsMap }


        | PTC.UnificationVar uniVar, PTC.TypeVariable typeVar
        | PTC.TypeVariable typeVar, PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (None, Set.singleton typeVar))

            { self = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
              constrained = uniVarsMap }


        | PTC.TypeVariable typeVar, (PTC.PrimitiveType _ as concreteType)
        | (PTC.PrimitiveType _ as concreteType), PTC.TypeVariable typeVar

        | PTC.TypeVariable typeVar, (PTC.ParametricType _ as concreteType)
        | (PTC.ParametricType _ as concreteType), PTC.TypeVariable typeVar ->
            let newUnificationVar = makeNewUniVar ()

            let uniVarsMap : UnificationVarsMap =
                Map.singleton newUnificationVar (UnifResult (Ok concreteType |> Some, Set.singleton typeVar))

            let instantiated =
                concretiseAndGeneralise
                    Set.empty
                    (Set.singleton newUnificationVar)
                    uniVarsMap
                    (PTC.UnificationVar newUnificationVar)

            instantiated

        | PTC.PrimitiveType _, PTC.ParametricType _
        | PTC.ParametricType _, PTC.PrimitiveType _ ->
            { self = UnificationClash (type1, type2) |> Error
              constrained = Map.empty }



    and unifyTwoTypeContentsResults
        (typeContentResult1 : Result<PolyTypeContents, UnificationError>)
        (typeContentResult2 : Result<PolyTypeContents, UnificationError>)
        : SelfAndConstrainedUnificationVars =
        match typeContentResult1, typeContentResult2 with
        | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents typeContent1 typeContent2

        | Error e, _
        | _, Error e ->
            { self = Error e
              constrained = Map.empty }


    and unifyTwoTypeResults
        (typeResult1 : Result<PolyType, UnificationError>)
        (typeResult2 : Result<PolyType, UnificationError>)
        : SelfAndConstrainedUnificationVars =
        match typeResult1, typeResult2 with
        | Ok type1, Ok type2 -> unifyTwoTypes type1 type2

        | Error e, _
        | _, Error e ->
            { self = Error e
              constrained = Map.empty }




    and unifyTwoTypeResultsOpts
        (typeOpt1 : Result<PolyType, UnificationError> option)
        (typeOpt2 : Result<PolyType, UnificationError> option)
        : {| self : Result<PolyType, UnificationError> option
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeResults type1 type2

            {| self = Some result.self
               constrained = result.constrained |}

        | Some type_, None
        | None, Some type_ ->
            {| self = Some type_
               constrained = Map.empty |}

        | None, None ->
            {| self = None
               constrained = Map.empty |}


    and unifyTwoTypeContentsResultsOpts
        (typeOpt1 : Result<PolyTypeContents, UnificationError> option)
        (typeOpt2 : Result<PolyTypeContents, UnificationError> option)
        : {| self : Result<PolyType, UnificationError> option
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeContentsResults type1 type2

            {| self = Some result.self
               constrained = result.constrained |}

        | Some type_, None
        | None, Some type_ ->
            {| self = Some (Result.map Types.makeEmptyPolyType type_)
               constrained = Map.empty |}

        | None, None ->
            {| self = None
               constrained = Map.empty |}


    and unifyTwoTypeContentsOpts
        (typeOpt1 : PolyTypeContents option)
        (typeOpt2 : PolyTypeContents option)
        : {| self : Result<PolyType, UnificationError> option
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
            {| self = Some (Ok (Types.makeEmptyPolyType type_))
               constrained = Map.empty |}


    and unifyManyTypeContents (types : PolyTypeContents nel) : SelfAndConstrainedUnificationVars =
        let (NEL (first, rest)) = types

        let combinedType, combinedUnificationMap =
            rest
            |> List.fold
                (fun (combinedType, combinedUniMap) polyTypeContents ->
                    let result =
                        unifyTwoTypeResults combinedType (Ok (Types.makeEmptyPolyType polyTypeContents))

                    let combineResult = combineTwoUnificationVarMaps combinedUniMap result.constrained

                    result.self, combineResult)
                (Ok (Types.makeEmptyPolyType first), Map.empty)

        { self = combinedType
          constrained = combinedUnificationMap }


    and unifyManyTypes (types : PolyType nel) : SelfAndConstrainedUnificationVars =
        let (NEL (first, rest)) = types

        let combinedType, combinedUnificationMap =
            rest
            |> List.fold
                (fun (combinedType, combinedUniMap) polyType ->
                    let result = unifyTwoTypeResults combinedType (Ok polyType)

                    let combineResult = combineTwoUnificationVarMaps combinedUniMap result.constrained

                    result.self, combineResult)
                (Ok first, Map.empty)

        Sacuv.make combinedType combinedUnificationMap








    /// Ok what should this function actually do? I think it should:
    /// - combine two unificationVarMaps
    /// - for those which have ether uniVars *or* typeVars in common, unify the values!
    ///     - so we need to check for overlap between the uniVars and typeVars in each iteration of the fold
    ///     - but it's a lil tricky cuz unifying the values actually results in its own uniVarsMap to be outputted, so we need to recursively merge that in to the one that we're accumulating in the fold as we go
    ///
    and combineTwoUnificationVarMaps (map1 : UnificationVarsMap) (map2 : UnificationVarsMap) : UnificationVarsMap =
        let makeTypeVarToUniVarMap (uniVarsMap : UnificationVarsMap) : Map<TypeVariableId, UnificationVarId> =
            uniVarsMap
            |> Map.toList
            |> List.collect (fun (uniVar, value) ->
                match value with
                | UnifResult (_, typeVars) -> typeVars |> Set.toList |> List.map (fun typeVar -> typeVar, uniVar)
                | UnifRedirect _ -> List.empty)
            |> Map.ofList

        /// This should get all the entries in the uniVarsMap that are linked with the input type vars because they have some overlap – although this does require a pre-computed map of typeVar to (final) uniVar. But tbh we could probably just use the `UnificationVarsMap.getTypeVarConstraints` function for that – albeit that one will be slower. So: fine for now but optimise later.
        let getTypeVarsFromMap
            (typeVars : TypeVariableId set)
            (typeVarToUniVarMap : Map<TypeVariableId, UnificationVarId>)
            (uniVarsMap : UnificationVarsMap)
            =
            typeVars
            |> Set.choose (fun typeVar -> Map.tryFind typeVar typeVarToUniVarMap)
            |> Set.map (fun uniVar -> UnificationVarsMap.findUnificationVarResult uniVar uniVarsMap)


        /// I.e. insert a uniVar into the uniVarsMap, ensuring that the natural harmony between the uniVar chains in their rightful order is maintained
        let insertItemIntoUniVarsMapWithoutFuckingUpTheChains
            (newUniVarToInsert : UnificationVarId)
            (itemToInsert : Result<PolyTypeContents, UnificationError> option * TypeVariableId set)
            (uniVarAlreadyInTheMap : UnificationVarId)
            (uniVarsMap : UnificationVarsMap)
            : UnificationVarsMap =
            let result =
                UnificationVarsMap.findUnificationVarResult uniVarAlreadyInTheMap uniVarsMap

            let finalUniVar = fst result

            if finalUniVar = newUniVarToInsert then
                uniVarsMap |> Map.add finalUniVar (UnifResult itemToInsert)

            else
                uniVarsMap
                |> Map.add finalUniVar (UnifResult itemToInsert)
                |> Map.add newUniVarToInsert (UnifRedirect finalUniVar)


        let typeVarsInMapToResult
            (typeVarsInMap : (UnificationVarId * (UnificationResult option * TypeVariableId set)) nel)
            =
            typeVarsInMap
            |> NEL.map (fun (uniVarId, (typeResultOpt, typeVars)) ->
                match typeResultOpt with
                | Some typeRes ->
                    match typeRes with
                    | Ok type_ -> Ok (uniVarId, (Some type_, typeVars))
                    | Error e -> Error (uniVarId, (e, typeVars))
                | None -> Ok (uniVarId, (None, typeVars)))
            |> NEL.sequenceResult










        /// This takes a unified `UnificationResult` thingy, we pass that into here, and then this function actually checks if we need to do another unification based on any typeVars overlap in the uniVarsMap
        let insertSingleItemIntoUniVarsMap
            (uniVar : UnificationVarId)
            (typeResultOpt : UnificationResult option)
            (allCombinedTypeVars : TypeVariableId set)
            (uniVarsMap : UnificationVarsMap)
            : UnificationVarsMap =
            let typeVarToUniVarMap = makeTypeVarToUniVarMap uniVarsMap

            /// The items containing overlap in typeVars with this contents item's type vars
            let typeVarsInMap =
                getTypeVarsFromMap allCombinedTypeVars typeVarToUniVarMap uniVarsMap

            match Set.toList typeVarsInMap with
            | [] -> uniVarsMap |> Map.add uniVar (UnifResult (typeResultOpt, allCombinedTypeVars))
            | head :: tail ->

                let overlappingEntriesList = NEL.new_ head tail |> typeVarsInMapToResult

                match overlappingEntriesList with
                | Ok typesList ->
                    let polyTypeContents = Seq.toList typesList |> List.choose (snd >> fst)

                    match polyTypeContents with
                    | [] ->
                        insertItemIntoUniVarsMapWithoutFuckingUpTheChains
                            uniVar
                            (typeResultOpt, Seq.map (snd >> snd) typesList |> Set.unionMany)
                            (typesList |> NEL.head |> fst)
                            uniVarsMap

                    | head :: tail ->
                        let unifiedResult = unifyManyTypeContents (NEL.new_ head tail)

                        let withItemToInsert =
                            unifyTwoTypeResultsOpts
                                (Some unifiedResult.self)
                                (typeResultOpt |> Option.map (Result.map Types.makeEmptyPolyType))

                        let combinedUniVarsMaps =
                            combineTwoUnificationVarMaps unifiedResult.constrained withItemToInsert.constrained

                        let uniVarsMapWithNewItemInserted =
                            insertItemIntoUniVarsMapWithoutFuckingUpTheChains
                                uniVar
                                (withItemToInsert.self |> Option.map (Result.map _.typeExpr),
                                 Seq.map (snd >> snd) typesList |> Set.unionMany)
                                (typesList |> NEL.head |> fst)
                                combinedUniVarsMaps

                        //combineTwoUnificationVarMaps unifiedResult.constrained uniVarsMapWithNewItemInserted
                        let instantiated =
                            uniVarsMapWithNewItemInserted
                            |> instantiateTypeVarsInUniVarsMap
                                (unifiedResult.self
                                 |> Result.map _.forall
                                 |> Result.defaultValue List.empty
                                 |> Set.ofList)
                                Set.empty

                        instantiated


                | Error e ->
                    let firstErr = NEL.head e

                    insertItemIntoUniVarsMapWithoutFuckingUpTheChains
                        uniVar
                        (Error (snd firstErr |> fst) |> Some, Seq.map (snd >> snd) e |> Set.unionMany)
                        (fst firstErr)
                        uniVarsMap









        /// This function ensures that we not only combine items based on which uniVars they have in common, but also that we correctly unify them based on shared typeVars
        let rec handleSharedTypeVarsSingleFolder
            (uniVarsMap : UnificationVarsMap)
            (uniVar : UnificationVarId)
            (contents : UnifResOrRedirect)
            : UnificationVarsMap =
            match contents with
            | UnifResult (typeResultOpt, typeVars) ->
                insertSingleItemIntoUniVarsMap uniVar typeResultOpt typeVars uniVarsMap
            | UnifRedirect redirectId -> Map.add uniVar (UnifRedirect redirectId) uniVarsMap



        and folder
            (uniVarsMap : UnificationVarsMap)
            (uniVar : UnificationVarId)
            (contents1 : UnifResOrRedirect)
            (contents2 : UnifResOrRedirect)
            : UnificationVarsMap =
            match (contents1, map1), (contents2, map2) with
            | (UnifRedirect redirect1, _), (UnifRedirect redirect2, _) ->
                // @TODO: I think we need to follow the redirects for both of these and then unify the results at the end... and then make sure all 3 of these redirects are pointing to that unified result
                let firstRedirectResult = UnificationVarsMap.findUnificationVarResult redirect1 map1

                let secondRedirectResult =
                    UnificationVarsMap.findUnificationVarResult redirect2 map2

                if fst firstRedirectResult = fst secondRedirectResult then
                    // Do they point to the same thing already
                    Map.add uniVar (UnifRedirect (fst firstRedirectResult)) uniVarsMap

                else
                    let unifiedResult =
                        unifyTwoTypeContentsResultsOpts
                            (snd firstRedirectResult |> fst)
                            (snd secondRedirectResult |> fst)

                    let combinedTypeVars : TypeVariableId set =
                        Set.union (snd firstRedirectResult |> snd) (snd secondRedirectResult |> snd)

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    let newUniVarsMap =
                        combineResult
                        |> Map.add
                            uniVar
                            (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr), combinedTypeVars))

                    insertSingleItemIntoUniVarsMap
                        uniVar
                        (unifiedResult.self |> Option.map (Result.map _.typeExpr))
                        combinedTypeVars
                        newUniVarsMap
                    |> instantiateTypeVarsInUniVarsMap
                        (unifiedResult.self
                         |> Option.map (Result.map _.forall >> Result.defaultValue List.empty)
                         |> Option.defaultValue List.empty
                         |> Set.ofList)
                        Set.empty


            | (UnifRedirect redirect, redirectMap), (UnifResult (res, typeVars), _)
            | (UnifResult (res, typeVars), _), (UnifRedirect redirect, redirectMap) ->
                // @TODO: I think we need to follow the redirect and then unify that redirect result with the result here... and then make sure we have two of the redirects (uniVar and redirect) pointing to that unified result

                let redirectResult =
                    UnificationVarsMap.findUnificationVarResult redirect redirectMap

                if fst redirectResult = uniVar then
                    // The redirect already points to this result
                    Map.add uniVar (UnifResult (res, typeVars)) uniVarsMap

                else
                    let unifiedResult = unifyTwoTypeContentsResultsOpts (snd redirectResult |> fst) res

                    let combinedTypeVars : TypeVariableId set =
                        Set.union (snd redirectResult |> snd) typeVars

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    let newUniVarsMap =
                        combineResult
                        |> Map.add
                            uniVar
                            (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr), combinedTypeVars))

                    insertSingleItemIntoUniVarsMap
                        uniVar
                        (unifiedResult.self |> Option.map (Result.map _.typeExpr))
                        combinedTypeVars
                        newUniVarsMap
                    |> instantiateTypeVarsInUniVarsMap
                        (unifiedResult.self
                         |> Option.map (Result.map _.forall >> Result.defaultValue List.empty)
                         |> Option.defaultValue List.empty
                         |> Set.ofList)
                        Set.empty



            | (UnifResult (res1, typeVars1), _), (UnifResult (res2, typeVars2), _) ->
                let combinedTypeVars : TypeVariableId set = Set.union typeVars1 typeVars2

                let unifiedResult = unifyTwoTypeContentsResultsOpts res1 res2

                let combineResult =
                    combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                let newUniVarsMap =
                    combineResult
                    |> Map.add
                        uniVar
                        (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr), combinedTypeVars))

                insertSingleItemIntoUniVarsMap
                    uniVar
                    (unifiedResult.self |> Option.map (Result.map _.typeExpr))
                    combinedTypeVars
                    newUniVarsMap
                |> instantiateTypeVarsInUniVarsMap
                    (unifiedResult.self
                     |> Option.map (Result.map _.forall >> Result.defaultValue List.empty)
                     |> Option.defaultValue List.empty
                     |> Set.ofList)
                    Set.empty



        Map.foldAllEntries handleSharedTypeVarsSingleFolder handleSharedTypeVarsSingleFolder folder map1 map2 Map.empty







    and combineUnificationVarMapsSeq : UnificationVarsMap seq -> UnificationVarsMap =
        Seq.fold combineTwoUnificationVarMaps Map.empty

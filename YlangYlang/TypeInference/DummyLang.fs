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
    /// A simple unparametric type, like `Int` or `String` or a parametric type, like `List a`, `Maybe a`, `Result e a`
    | ConcreteType of ConcreteType



    override this.ToString () =
        match this with
        | UnificationVar uniVar -> string uniVar
        | TypeVariable typeVar -> string typeVar
        | ConcreteType (ConcType (name, typeParams)) ->
            match name with
            | LocalUpper (UpperIdent "Arrow") ->
                match typeParams with
                | [ from; to_ ] -> string from + " -> " + string to_
                | _ -> failwith "Arrow type should have exactly two type params"
            | LocalUpper (UpperIdent "Tuple") ->
                match typeParams with
                | [ a; b ] -> "( " + string a + ", " + string b + " )"
                | _ -> failwith "Tuple type should have exactly two type params"
            | _ ->
                match typeParams with
                | [] -> string name // I.e. a primitive type
                | first :: rest ->
                    // I.e. a parametric type
                    string name + " " + String.concat " " (first :: rest |> List.map string)

and ConcreteType = | ConcType of name : UpperNameValue * typeParams : PolyTypeContents list



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
    | UnificationClash of ConcreteType * ConcreteType
    | UndefinedName of LowerNameValue

/// Either a unified PolyTypeContents or a unification error
type UnificationResult = Result<PolyTypeContents, UnificationError>

/// A unification result or a redirect to another entry. Having multiple unification variables pointing to the same unification result lets us represent multiple unification variables that have been unified with each other. And having a set of type variables pointing to the same unification result lets us represent multiple type variables that have been unified with each other; and thereby also multiple unification variables that have been unified with multiple type variables.
/// FYI having multiple unification variables unified with each other can take the form of multiple uniVars all redirecting to the same one, or multiple uniVars redirecting to each other in a chain, or a combination of both in a kind of tree structure where each entry points to its parent, and the root of the tree is the unification result.
/// Instantiating a type variable with a fresh unification variable is done by following that unification variable's redirect chain until you get to the root entry, and then adding that type variable to the set of type variables in the root.
type UnifResOrRedirect =
    /// Unification result
    | UnifResult of Result<PolyTypeContents, UnificationError> option
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
            UnifResult None

    let rec findUnificationVarResult
        (uniVar : UnificationVarId)
        (map : UnificationVarsMap)
        : UnificationVarId * UnificationResult option =
        match findByUnificationVar uniVar map with
        | UnifRedirect redirectUniVar -> findUnificationVarResult redirectUniVar map
        | UnifResult res ->
            // Return the result as well as the final unification variable at that location
            uniVar, res


    type private UnificationVarResultWithSteps =
        {
            /// The (reversed) list of steps we took before we got to the final unification var
            hops : UnificationVarId list
            finalUnificationVar : UnificationVarId
            result : UnificationResult option
        }


    /// This gets the unification result, but also includes all the unification variables we encountered during our redirect hops
    let rec private findUnificationVarResultWithSteps uniVar map : UnificationVarResultWithSteps =
        match findByUnificationVar uniVar map with
        | UnifRedirect redirectUniVar ->
            let result = findUnificationVarResultWithSteps redirectUniVar map

            { result with
                hops = redirectUniVar :: result.hops }

        | UnifResult res ->
            { hops = List.empty
              finalUnificationVar = uniVar
              result = res }




    /// Represents a single entry in the unification vars map of all the things that are bound to the same constraints, along with the constraint itself
    type CoupledConstraints =
        { finalUniVar : UnificationVarId
          otherUniVars : UnificationVarId set
          result : UnificationResult option }

        member this.allUniVars : UnificationVarId set =
            Set.add this.finalUniVar this.otherUniVars



    /// Gets all the unification variables that have been unified with the given unification variable, via traversing all the redirects
    let getAllJoinedUnificationVars (uniVar : UnificationVarId) (map : UnificationVarsMap) : CoupledConstraints =
        let finalUnivar, res = findUnificationVarResult uniVar map

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
          result = res }




/// The result of every type inference or unification: contains the inferred or unified type itself, plus the map of constrained unification variables as gleaned from the inference/unification
type SelfAndConstrainedUnificationVars =
    { self : Result<PolyType, UnificationError>
      constrained : UnificationVarsMap }



module SelfAndConstrainedUnificationVars =
    let make self constrained : SelfAndConstrainedUnificationVars =
        { self = self
          constrained = constrained }

    let makeEmpty self : SelfAndConstrainedUnificationVars = { self = self; constrained = Map.empty }

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
    let makeParametricType label params_ = ConcreteType (ConcType (LocalUpper (UpperIdent label), params_))
    let makePrimitiveType label = makeParametricType label List.empty

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
    let boolType : PolyTypeContents = makePrimitiveType "Bool"

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


    let infixOpTypeOf leftType rightType resultType = funcTypeOf (funcTypeOf leftType rightType) resultType




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
        | IfElse of condition : Expr * then_ : Expr * else_ : Expr
        | InfixOp of op : LowerIdent * left : Expr * right : Expr


    let str = StrVal
    let int = IntVal
    let list = ListVal
    let tuple a b = TupleVal (a, b)
    let lambda param body = LambdaVal (LowerIdent param, body)
    let name = NamedVal << LowerIdent
    let ifThenElse cond then_ else_ = IfElse (cond, then_, else_)
    let infixOp op left right = InfixOp (op, left, right)

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







(*

    Type inference

*)




/// Gets all the value names referenced in an expression – note! need to specify that we're only interested in names defined at this scope and higher – internally defined let bindings or parameters should not be bubbled up because as far as the higher scopes are concerned those names do not exist.
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
        let namesBoundHere = bindings |> NEL.map _.name |> Set.ofSeq

        // Because if a name is shadowed here then any references to that name in this scope will be referencing the more closely defined name, not the one from the higher scope
        let withShadowedNamesRemoved =
            namesToLookOutFor
            |> Set.filter (fun name -> Set.contains name namesBoundHere |> not)

        Set.union
            (getNamesUsedInExpr withShadowedNamesRemoved body)
            (bindings
             |> Seq.map (_.assignedExpr >> getNamesUsedInExpr withShadowedNamesRemoved)
             |> Set.unionMany)

    | Ast.FuncApplication (funcExpr, inputExpr) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor funcExpr) (getNamesUsedInExpr namesToLookOutFor inputExpr)

    | Ast.IfElse (cond, then_, else_) ->
        [ cond; then_; else_ ]
        |> List.map (getNamesUsedInExpr namesToLookOutFor)
        |> Set.unionMany

    | Ast.InfixOp (op, left, right) ->
        let exprsNames =
            Set.union (getNamesUsedInExpr namesToLookOutFor left) (getNamesUsedInExpr namesToLookOutFor right)

        if Set.contains op namesToLookOutFor then
            Set.add op exprsNames

        else
            exprsNames



let private sortBindingsTopologically
    (namesAndExprs : (LowerIdent * Ast.Expr) seq)
    : DG.StronglyConnectedGraph<Ast.Expr, LowerIdent> list =
    let bindingNames = namesAndExprs |> Seq.map fst |> Set.ofSeq
    let getDependencies = snd >> getNamesUsedInExpr bindingNames >> Set.toSeq

    DG.getStronglyConnectedComponents<LowerIdent * Ast.Expr, LowerIdent> fst getDependencies namesAndExprs
    |> DG.sortOneOrMoreTopologically fst getDependencies
    |> List.map (DG.SCC.map snd)










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
            toReplaceWith : Result<PolyTypeContents, UnificationError>
            /// If a new type var is created here we'll declare it here
            newTypeVarOpt : TypeVariableId option
        }


    let rec private applyTypeReplacementToConcType
        (tr : TypeReplacement)
        (polyTypeContents : ConcreteType)
        : ConcreteType =
        let (ConcType (name, ptcs)) = polyTypeContents
        ConcType (name, List.map (applyTypeReplacement tr) ptcs)


    and private applyTypeReplacement (tr : TypeReplacement) (polyTypeContents : PolyTypeContents) : PolyTypeContents =
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

        | TypeVariable typeVar -> TypeVariable typeVar
        | ConcreteType concType -> ConcreteType <| applyTypeReplacementToConcType tr concType


    let private applyTypeReplacementToUnificationError
        (tr : TypeReplacement)
        (unifError : UnificationError)
        : UnificationError =
        match unifError with
        | UnificationClash (a, b) ->
            UnificationClash (applyTypeReplacementToConcType tr a, applyTypeReplacementToConcType tr b)
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
            match normInstr.newTypeVarOpt with
            | Some newTypeVar -> newTypeVar :: polyType.forall
            | None -> polyType.forall }


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
        |> Map.choose (fun _ redirectOrResult ->
            match redirectOrResult with
            | UnifRedirect uniVar ->
                if Set.contains uniVar tr.unificationVarsToReplace then
                    None

                else
                    Some (UnifRedirect uniVar)

            | UnifResult typeResultOpt -> UnifResult (applyTypeReplacementToPtcResultOpt tr typeResultOpt) |> Some)




    /// Works equally well with TypedNamesMaps and TypedLocalNamesMaps
    let private applyNormInstrToTypedNamesMap
        (tr : TypeReplacement)
        (namesMap : Map<'Name, PolyType>)
        : Map<'Name, PolyType> =
        namesMap |> Map.map (fun _ -> applyTypeReplacementToPolyType tr)


    /// Get the coupled constraints for the provided typeVars and uniVars from the given uniVarsMap
    let getCoupledConstraintsSet
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        : UnificationVarsMap.CoupledConstraints set =
        unificationVarsWeCanEliminate
        |> Set.map (fun uniVar -> UnificationVarsMap.getAllJoinedUnificationVars uniVar unificationVarsMap)





    let private coupledConstraintToTypeReplacement
        (uniVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        : {| replacementInstruction : TypeReplacement
             replacedUniVarsMap : UnificationVarsMap |}
        =
        let overlap =
            /// We need to eliminate the eliminatable uniVars and typeVars from the coupled constraints, and then we determine what the type replacement instruction should be based on what's left
            //let remainingUniVars =
            Set.difference constrs.allUniVars uniVarsWeCanEliminate


        let makeNormalisationInstruction'
            (rplcmnt : UnificationResult)
            (newTypeVarOpt : TypeVariableId option)
            : TypeReplacement =
            { unificationVarsToReplace = constrs.allUniVars
              toReplaceWith = rplcmnt
              newTypeVarOpt = newTypeVarOpt }


        let typeReplInstr, uniVarsMapWithKeysRemoved =
            match Set.toList overlap with
            | head :: rest ->
                if Set.contains constrs.finalUniVar overlap then
                    let uniVarToPointTo = constrs.finalUniVar

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.add constrs.finalUniVar (UnifResult (constrs.result))

                else
                    /// The uniVar containing the result didn't make the cut so we have to promote one of the other ones to be the one containing the result

                    let uniVarToPointTo = head

                    makeNormalisationInstruction' (Ok (PTC.UnificationVar uniVarToPointTo)) None,
                    uniVarsMap
                    |> Map.removeKeys constrs.allUniVars
                    |> Map.addBulk (rest |> Seq.map (fun uniVar -> uniVar, UnifRedirect uniVarToPointTo))
                    |> Map.add uniVarToPointTo (UnifResult (constrs.result))


            | [] ->
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
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (uniVarsMap : UnificationVarsMap)
        : UnificationVarsMap =
        coupledConstraintToTypeReplacement unificationVarsWeCanEliminate constrs uniVarsMap
        |> _.replacedUniVarsMap




    let instantiateTypeVarsInUniVarsMap
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        : UnificationVarsMap =
        let matchesForBoth =
            getCoupledConstraintsSet unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun varsMap coupledConstraints ->
                replaceCoupledConstraintsInUniVarsMap unificationVarsWeCanEliminate coupledConstraints varsMap)
            unificationVarsMap







    let instantiateTypeVarsInUniVarsMapAndLocalNamesMap
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (localNamesMap : TypedLocalNamesMap)
        (unificationVarsMap : UnificationVarsMap)
        : TypedLocalNamesMap * UnificationVarsMap =
        let matchesForBoth =
            getCoupledConstraintsSet unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun (namesMap, varsMap) coupledConstraints ->
                let replacement =
                    coupledConstraintToTypeReplacement unificationVarsWeCanEliminate coupledConstraints varsMap

                applyNormInstrToTypedNamesMap replacement.replacementInstruction namesMap,
                replacement.replacedUniVarsMap)
            (localNamesMap, unificationVarsMap)




    let private replaceCoupledConstraintsInSacuv'
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (sacuv : SelfAndConstrainedUnificationVars)
        : SelfAndConstrainedUnificationVars =
        let replacement =
            coupledConstraintToTypeReplacement unificationVarsWeCanEliminate constrs sacuv.constrained

        let normalisedPolyType =
            applyTypeReplacementToPolyTypeResult replacement.replacementInstruction sacuv.self

        { self = normalisedPolyType
          constrained = replacement.replacedUniVarsMap }





    let concretiseAndGeneralise
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyTypeContents)
        : SelfAndConstrainedUnificationVars =
        let matchesForBoth =
            getCoupledConstraintsSet unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun sacuv coupledConstraints ->
                let replaced =
                    replaceCoupledConstraintsInSacuv' unificationVarsWeCanEliminate coupledConstraints sacuv

                replaced)
            { self = Types.makeEmptyPolyType type_ |> Ok
              constrained = unificationVarsMap }



    let instantiateTypeVarsInPolyType
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyType)
        : SelfAndConstrainedUnificationVars =
        concretiseAndGeneralise unificationVarsWeCanEliminate unificationVarsMap type_.typeExpr


    let instantiateTypeVarsInPolyTypeResult
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : Result<PolyType, UnificationError>)
        : SelfAndConstrainedUnificationVars =
        let matchesForUniVars : UnificationVarsMap.CoupledConstraints set =
            unificationVarsWeCanEliminate
            |> Set.map (fun uniVar -> UnificationVarsMap.getAllJoinedUnificationVars uniVar unificationVarsMap)


        matchesForUniVars
        |> Set.toList
        |> List.fold
            (fun sacuv coupledConstraints ->
                replaceCoupledConstraintsInSacuv' unificationVarsWeCanEliminate coupledConstraints sacuv)
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
                let inferred = NEL.map (inferTypeFromExpr namesMap) (NEL.new_ head rest)
                let unified = unifyMultipleSacuvs inferred

                unified |> Sacuv.map (Result.map Types.listTypeOf)


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
            let newUniVar : UnificationVarId = makeNewUniVar ()

            let paramPolyType : PolyType =
                PolyTypeContents.UnificationVar newUniVar |> Types.makeEmptyPolyType

            /// Add the new name with its unification variable type into the names map that we inject into the body inferencing function
            let withNewUnificationVarAddedForParam : TypedNamesMap =
                Map.add (LocalLower param) paramPolyType namesMap

            let bodyInferenceResult : SelfAndConstrainedUnificationVars =
                inferTypeFromExpr withNewUnificationVarAddedForParam body
                |> Sacuv.map (Result.map (Types.funcTypeOf paramPolyType))

            let instantiatedType : SelfAndConstrainedUnificationVars =
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


        | Ast.FuncApplication (funcExpr, inputExpr) ->
            let inputType = inferTypeFromExpr namesMap inputExpr


            let funcExprType = inferTypeFromExpr namesMap funcExpr

            match inputType.self, funcExprType.self with
            | Ok inputType_, Ok funcExprType_ ->
                let returnTypeUniVar = makeNewUniVar ()

                let returnType : PolyType =
                    PTC.UnificationVar returnTypeUniVar |> Types.makeEmptyPolyType

                /// This is the type that the function expression should be compatible with: i.e. being able to receive the provided input, and returning the return unification variable – which may or may not get constrained to something concrete based on the function's actual expression
                let funcRequiredType = Types.funcTypeOf inputType_ returnType

                let funcRequiredResult = unifyTwoTypes funcRequiredType funcExprType_

                let combinedUnifVarMap =
                    [ inputType.constrained
                      funcExprType.constrained
                      funcRequiredResult.constrained ]
                    |> combineUnificationVarMapsSeq

                instantiateTypeVarsInPolyType (Set.singleton returnTypeUniVar) combinedUnifVarMap returnType

            | Error e, _
            | _, Error e ->
                let combinedUniVarsMaps =
                    combineTwoUnificationVarMaps inputType.constrained funcExprType.constrained

                Sacuv.make (Error e) combinedUniVarsMaps


        | Ast.IfElse (condition, thenExpr, elseExpr) ->
            let condRequirement = Types.boolType |> Types.makeEmptyPolyType |> Ok

            /// @TODO: so atm we're not actually doing anything with the self type of this, just like we're not doing anything with the inferred type of an expression when it has a type annotation. We need to surface any errors for both those constructs!
            let condType =
                inferTypeFromExpr namesMap condition
                |> unifyTwoSacuvs (Sacuv.makeEmpty condRequirement)

            let thenType = inferTypeFromExpr namesMap thenExpr
            let elseType = inferTypeFromExpr namesMap elseExpr

            let combinedReturnType = unifyTwoSacuvs thenType elseType

            let combinedUniVarsMaps =
                combineTwoUnificationVarMaps condType.constrained combinedReturnType.constrained

            Sacuv.make combinedReturnType.self combinedUniVarsMaps


        | Ast.InfixOp (op, left, right) ->
            // This is effectively just applying the function with the infix op's name to two parameters, so we rewrite it as if it were a simple function application

            let withLeftApplied = Ast.FuncApplication (Ast.NamedVal op, left)
            let withRightApplied = Ast.FuncApplication (withLeftApplied, right)

            inferTypeFromExpr namesMap withRightApplied



    /// The new strategy
    and resolveNamesTopologically
        (namesMap : TypedNamesMap)
        (namesAndExprs : Ast.LetBindingSingle nel)
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

                    // @TODO: we should surface any inference errors instead of just ignoring them and skipping that step in the fold!
                    match stronglyConnectedComponent with
                    | DG.SingleNonRec (name, expr) ->
                        let inferredType = inferTypeFromExpr combinedNamesMap expr

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        match inferredType.self with
                        | Ok okSelf ->
                            let withThisBindingAdded : TypedLocalNamesMap = Map.add name okSelf localNamesMap

                            let result =
                                instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                                    Set.empty
                                    withThisBindingAdded
                                    combinedMapResult

                            result

                        | Error e -> localNamesMap, combinedMapResult

                    | DG.SingleSelfRec (name, expr) ->
                        let newUniVar = makeNewUniVar ()

                        let withThisNameUniVarAdded : TypedNamesMap =
                            Map.add
                                (LocalLower name)
                                (PTC.UnificationVar newUniVar |> Types.makeEmptyPolyType)
                                combinedNamesMap

                        let inferredType = inferTypeFromExpr withThisNameUniVarAdded expr

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        match inferredType.self with
                        | Ok okSelf ->
                            let withThisBindingAdded : TypedLocalNamesMap = Map.add name okSelf localNamesMap

                            let result =
                                instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                                    (Set.singleton newUniVar)
                                    withThisBindingAdded
                                    combinedMapResult

                            result

                        | Error e -> localNamesMap, combinedMapResult



                    | DG.MutualRecursive namesAndBindings ->
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
                            (newUniVars |> Seq.map snd |> Set.ofSeq)
                            newLocalNamesMap
                            newUniVarsMap

                )
                (namesWithTypeAnnotations, Map.empty)

        {| inferredTypes = localNamesMap
           constrained = uniVarsMap |}





    and resolveAllLetBindingsAndBody
        (namesMap : TypedNamesMap)
        (letBindings : Ast.LetBindingSingle nel)
        (body : Ast.Expr)
        : SelfAndConstrainedUnificationVars =
        let bindingsResolutionResult = resolveNamesTopologically namesMap letBindings

        let combinedNamesMap : TypedNamesMap =
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





    and unifyTwoTypes (type1 : PolyType) (type2 : PolyType) : SelfAndConstrainedUnificationVars =

        let rec swapTypeVarWithUniVar typeVar uniVar (polyType : PolyTypeContents) =
            match polyType with
            | UnificationVar id -> UnificationVar id
            | ConcreteType (ConcType (name, typeParams)) ->
                ConcreteType
                <| ConcType (name, List.map (swapTypeVarWithUniVar typeVar uniVar) typeParams)

            | TypeVariable tv ->
                if tv = typeVar then
                    UnificationVar uniVar

                else
                    TypeVariable tv


        let allTypeVars = type1.forall @ type2.forall

        let typeVarsToUniVar =
            allTypeVars |> List.map (fun typeVar -> typeVar, makeNewUniVar ())

        let replacedType1 : PolyTypeContents =
            typeVarsToUniVar
            |> List.fold (fun type_ (typeVar, uniVar) -> swapTypeVarWithUniVar typeVar uniVar type_) type1.typeExpr

        let replacedType2 : PolyTypeContents =
            typeVarsToUniVar
            |> List.fold (fun type_ (typeVar, uniVar) -> swapTypeVarWithUniVar typeVar uniVar type_) type2.typeExpr


        let unified : SelfAndConstrainedUnificationVars =
            unifyTwoTypeContents replacedType1 replacedType2


        match unified.self with
        | Ok okSelf ->
            concretiseAndGeneralise (Set.ofList <| List.map snd typeVarsToUniVar) unified.constrained okSelf.typeExpr

        | Error e ->
            // @TODO: we can probably just concretise and generalise this too by chucking itnto a version of concretiseAndGeneralise that handles Results
            { self = Error e
              constrained = unified.constrained }



    and unifyTwoTypeContents (type1 : PolyTypeContents) (type2 : PolyTypeContents) : SelfAndConstrainedUnificationVars =
        match type1, type2 with
        | PTC.ConcreteType (ConcType (name1, typeParams1) as concType1),
          PTC.ConcreteType (ConcType (name2, typeParams2) as concType2) ->

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
                            liftPolyTypesIntoPtc (fun p -> PTC.ConcreteType <| ConcType (name1, p)) unifiedParams
                            |> Ok
                        | Error errs -> NEL.head errs |> Error

                      constrained = unificationVarMap }


                | Error _ ->
                    { self = UnificationClash (concType1, concType2) |> Error
                      constrained = Map.empty }

            else
                { self = UnificationClash (concType1, concType2) |> Error
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
                    Map.singleton smallerUniVar (UnifResult (PTC.UnificationVar biggerUniVar |> Ok |> Some))

                { self = PTC.UnificationVar smallerUniVar |> Types.makeEmptyPolyType |> Ok
                  constrained = constrained }


        | PTC.UnificationVar uniVar, PTC.ConcreteType (ConcType (name, typeVars))
        | PTC.ConcreteType (ConcType (name, typeVars)), PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.ConcreteType (ConcType (name, typeVars)) |> Ok |> Some))

            { self = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
              constrained = uniVarsMap }


        | PTC.TypeVariable _, _
        | _, PTC.TypeVariable _ -> failwith "All type variables should have been swapped out for unification variables!"



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








    and combineTwoUnificationVarMaps (map1 : UnificationVarsMap) (map2 : UnificationVarsMap) : UnificationVarsMap =
        /// This function ensures that we not only combine items based on which uniVars they have in common, but also that we correctly unify them based on shared typeVars
        let rec singleFolder
            (uniVarsMap : UnificationVarsMap)
            (uniVar : UnificationVarId)
            (contents : UnifResOrRedirect)
            : UnificationVarsMap =
            match contents with
            | UnifResult typeResultOpt -> uniVarsMap |> Map.add uniVar (UnifResult typeResultOpt)
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
                        unifyTwoTypeContentsResultsOpts (snd firstRedirectResult) (snd secondRedirectResult)

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    combineResult
                    |> Map.add uniVar (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr)))
                    |> instantiateTypeVarsInUniVarsMap Set.empty


            | (UnifRedirect redirect, redirectMap), (UnifResult res, _)
            | (UnifResult res, _), (UnifRedirect redirect, redirectMap) ->
                // @TODO: I think we need to follow the redirect and then unify that redirect result with the result here... and then make sure we have two of the redirects (uniVar and redirect) pointing to that unified result

                let redirectResult =
                    UnificationVarsMap.findUnificationVarResult redirect redirectMap

                if fst redirectResult = uniVar then
                    // The redirect already points to this result
                    Map.add uniVar (UnifResult (res)) uniVarsMap

                else
                    let unifiedResult = unifyTwoTypeContentsResultsOpts (snd redirectResult) res

                    let combineResult =
                        combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                    combineResult
                    |> Map.add uniVar (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr)))
                    |> instantiateTypeVarsInUniVarsMap Set.empty



            | (UnifResult res1, _), (UnifResult res2, _) ->
                let unifiedResult = unifyTwoTypeContentsResultsOpts res1 res2

                let combineResult =
                    combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                combineResult
                |> Map.add uniVar (UnifResult (unifiedResult.self |> Option.map (Result.map _.typeExpr)))
                |> instantiateTypeVarsInUniVarsMap Set.empty



        Map.foldAllEntries singleFolder singleFolder folder map1 map2 Map.empty







    and combineUnificationVarMapsSeq : UnificationVarsMap seq -> UnificationVarsMap =
        Seq.fold combineTwoUnificationVarMaps Map.empty


    /// Unify two `SelfAndConstrainedUnificationVars`s
    and unifyTwoSacuvs
        (sacuv1 : SelfAndConstrainedUnificationVars)
        (sacuv2 : SelfAndConstrainedUnificationVars)
        : SelfAndConstrainedUnificationVars =
        let combinedSelf = unifyTwoTypeResults sacuv1.self sacuv2.self

        let combinedUniVarMap =
            combineUnificationVarMapsSeq [ sacuv1.constrained; sacuv2.constrained; combinedSelf.constrained ]

        { self = combinedSelf.self
          constrained = combinedUniVarMap }



    and unifyMultipleSacuvs (sacuvs : SelfAndConstrainedUnificationVars nel) : SelfAndConstrainedUnificationVars =
        let (NEL (head, rest)) = sacuvs
        List.fold unifyTwoSacuvs head rest

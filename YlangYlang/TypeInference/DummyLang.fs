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



//type SkolemId =
//    | SkolemId of System.Guid

//    override this.ToString () =
//        let (SkolemId id) = this
//        String.trim 8 (string id)


/// E.g. `Bool`, `Maybe Int`, `Result Error a`, etc. In other words, a type expression.
///
/// @TODO: need to explain what the difference is between this an a `PolyTypeContents`. I think the difference is that this does not contain any uniVars or typeVars.
type TypeExpr =
    /// This references a type expression in a type declaration, e.g.TypeExpr (Just a)` in `Maybe a = Just a | Nothing`
    | TypeExpr of label : UpperNameValue * params_ : TypeExpr list
    /// This references a type param in the type declaration, e.g. the `a` in the `Just a` in the `Maybe a = Just a | Nothing`
    | Skolem of name : LowerIdent

    override this.ToString () =
        match this with
        | Skolem skolem -> string skolem
        | TypeExpr (label, typeParams) ->
            match label with
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
                | [] -> string label // I.e. a primitive type
                | first :: rest ->
                    // I.e. a parametric type
                    string label + " " + String.concat " " (first :: rest |> List.map string)







type PolyTypeContents =
    /// Referencing a unification variable. To figure out what this unification var is you'll need to look into your local UnificationVarsMap (see below)
    | UnificationVar of UnificationVarId
    /// Referencing a *type variable* (not a unification variable!)
    | TypeVariable of TypeVariableId
    /// This is only available during a type `check` call – may be unified with itself or a uniVar but nothing else!
    | Skolem of name : LowerIdent
    /// A simple unparametric type like `Int` or `String`, or a parametric type like `List a`, `Maybe a`, `Result e a`
    | ConcreteType of ConcreteType


    override this.ToString () =
        match this with
        | UnificationVar uniVar -> string uniVar
        | TypeVariable typeVar -> string typeVar
        | Skolem name -> string name
        | ConcreteType concType -> string concType


and ConcreteType =
    | ConcType of name : UpperNameValue * typeParams : PolyTypeContents list

    override this.ToString () =
        let (ConcType (name, typeParams)) = this

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



/// Alias for PolyTypeContents
type PTC = PolyTypeContents


type PolyType =
    { forall : TypeVariableId list
      typeExpr : PolyTypeContents }

    override this.ToString () =
        let bodyStr = string this.typeExpr

        match this.forall with
        | [] -> bodyStr
        | _ :: _ -> "forall " + String.concat " " (List.map string this.forall) + ". " + bodyStr




type UnificationError =
    | UnificationClash of ConcreteType * ConcreteType
    | UndefinedName of LowerNameValue
    | UndefinedTypeCtor of UpperNameValue
    /// Skolems only unify with themselves, so different skolems can't be unified with each other
    | TriedToUnifyDifferentSkolems of skolem1 : LowerIdent * skolem2 : LowerIdent
    /// Skolems only unify with themselves, not with anything else
    | NarrowedSkolem of skolemName : LowerIdent * narrowedWith : PolyTypeContents

    override this.ToString () =
        match this with
        | UnificationClash (conc1, conc2) -> "Unification clash: `" + string conc1 + "` and `" + string conc2 + "`"
        | UndefinedName name -> "Undefined name: " + string name
        | UndefinedTypeCtor name -> "Undefined type constructor: " + string name
        | TriedToUnifyDifferentSkolems (skolem1, skolem2) ->
            "Tried to unify different skolems: " + string skolem1 + " and " + string skolem2
        | NarrowedSkolem (skolemName, narrowedWith) ->
            "Narrowed skolem: " + string skolemName + " with " + string narrowedWith


    static member makeClash conc1 conc2 =
        // // Uncomment when debugging unexpected type errors
        //failwith ("Unification clash: `" + string conc1 + "` and `" + string conc2 + "`")

        UnificationClash (conc1, conc2)



/// The context where we put the names with their type checked types
type TypedNamesMap = Map<LowerNameValue, Result<PolyType, UnificationError>>

/// This maps from constructor names to the parameters that the variant needs to the signature of the constructor; e.g. `String -> Int -> Maybe (String, Int)`.
/// But it could also be e.g. `None`, which would have as its value the single type expression `Maybe a`
///
///The list represents the parameters for this particular constructor
type CtorNamesMap = Map<UpperNameValue, TypeExpr nel>


type Ctx =
    { ctorNamesMap : CtorNamesMap
      skolemsInScope : LowerIdent set
      typedNamesMap : TypedNamesMap }

    static member empty : Ctx =
        { ctorNamesMap = Map.empty
          skolemsInScope = Set.empty
          typedNamesMap = Map.empty }


/// A local context, we return these from functions that type check let bindings and top level declarations
type TypedLocalNamesMap = Map<LowerIdent, Result<PolyType, UnificationError>>




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



/// @TODO: for the real thing, this should include information about the location of the error, so that we can give a nice error message to the user, ideally with the exact code causing the error, with the relevant parts highlighted
type InnerTypeError =
    /// Although the binding has a type annotation, the value actually has a type error
    | ErrorHiddenByAnnotation of unificationErr : UnificationError

    /// The binding doesn't have an internal type error, but the type doesn't match the declared annotation
    | AnnotationVsInferenceClash of
        typeVars : TypeVariableId list *
        annotated : PolyTypeContents *
        inferred : PolyTypeContents



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
    /// Make without errors
    let make result constrained : SelfAndConstrainedUnificationVars =
        { self = result
          constrained = constrained }


    /// Make with only a self type, no constraineds
    let makeEmpty result : SelfAndConstrainedUnificationVars = make result Map.empty

    let map f sacuv =
        { self = f sacuv.self
          constrained = sacuv.constrained }



///// Bubble up the result-ness of the .self field onto the record as a whole
//let sequenceResult sacuv =
//    sacuv.self
//    |> Result.map (fun self ->
//        {| constrained = sacuv.constrained
//           self = self |})


/// @TODO: is there a specific reason this couldn't just be a `SelfAndConstrainedUnificationVars`?
type TypeUnificationResult =
    { unified : Result<PolyType, UnificationError>
      constrained : UnificationVarsMap }



/// The result of a check call, which is only done if we have an expected type we are checking the expression against
type TypeCheckResult =
    { result : Result<unit, UnificationError>
      constrained : UnificationVarsMap }



module TypeCheckResult =

    let singleton result : TypeCheckResult =
        { result = result
          constrained = Map.empty }

    let make result constrained : TypeCheckResult =
        { result = result
          constrained = constrained }

    let makeOk = make (Ok ())
    let makeErr err = make (Error err)

    let emptyOk : TypeCheckResult = singleton (Ok ())
    let emptyErr e : TypeCheckResult = singleton (Error e)




module Types =
    let makeTypeName = UpperIdent >> LocalUpper

    let strTypeName = makeTypeName "String"
    let intTypeName = makeTypeName "Int"
    let boolTypeName = makeTypeName "Bool"
    let unitTypeName = makeTypeName "Unit"
    let listTypeName = makeTypeName "List"
    let tupleTypeName = makeTypeName "Tuple"
    let arrowTypeName = makeTypeName "Arrow"


    let arrowConCreteType from to_ = ConcType (arrowTypeName, [ from; to_ ])

    let makeParametricType label params_ = ConcreteType (ConcType (label, params_))
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


    let typeVar = TypeVariable

    /// Make a monomorphic type
    let mono contents = makeEmptyPolyType contents


    let strType : PolyTypeContents = makePrimitiveType strTypeName
    let intType : PolyTypeContents = makePrimitiveType intTypeName
    let boolType : PolyTypeContents = makePrimitiveType boolTypeName
    let unitType : PolyTypeContents = makePrimitiveType unitTypeName

    let listTypeOf (t : PolyType) =
        { forall = t.forall
          typeExpr = makeParametricType listTypeName [ t.typeExpr ] }

    let listType : PolyType = makeNewParametricType listTypeName [ () ]

    let tupleTypeOf a b =
        { forall = a.forall @ b.forall
          typeExpr = makeParametricType tupleTypeName [ a.typeExpr; b.typeExpr ] }


    let funcTypeOf from to_ =
        { forall = from.forall @ to_.forall
          typeExpr = makeParametricType arrowTypeName [ from.typeExpr; to_.typeExpr ] }


    let infixOpTypeOf leftType rightType resultType = funcTypeOf (funcTypeOf leftType rightType) resultType




    let listTypeOfExpr inner = TypeExpr (listTypeName, [ inner ])


    (*
    Active patterns for easier matching on the shape of a type expression
    *)

    let (|IsPrimitiveType|_|) (typeName : UpperNameValue) (type_ : TypeExpr) =
        match type_ with
        | TypeExpr (label, []) when label = typeName -> Some ()
        | _ -> None

    let (|IsListOf|_|) (type_ : TypeExpr) =
        match type_ with
        | TypeExpr (label, [ typeParam ]) when label = listTypeName -> Some typeParam
        | TypeExpr (label, _) when label = listTypeName -> failwith "List types should have exactly one type parameter"
        | _ -> None

    let (|IsTupleOf|_|) (type_ : TypeExpr) =
        match type_ with
        | TypeExpr (label, [ a; b ]) when label = tupleTypeName -> Some (a, b)
        | TypeExpr (label, _) when label = tupleTypeName ->
            failwith "Tuple types should have exactly two type parameters"
        | _ -> None

    let (|IsFuncTypeOf|_|) (type_ : TypeExpr) =
        match type_ with
        | TypeExpr (label, [ from; to_ ]) when label = arrowTypeName -> Some (from, to_)
        | TypeExpr (label, _) when label = arrowTypeName ->
            failwith "Function types should have exactly two type parameters"
        | _ -> None










/// Module with a greatly simplified language but still containing all the key elements, so that we can test type inference and resolution with a simpler version before tackling the real thing
module AbstractSyntaxTree =



    type LetBindingSingle =
        { name : LowerIdent
          typeAnnotation : TypeExpr option
          assignedExpr : Expr }


    and Expr =
        | StrVal of string
        | IntVal of int
        | ListVal of Expr list
        | TupleVal of first : Expr * second : Expr
        | LambdaVal of param : LowerIdent * body : Expr
        | NamedVal of LowerIdent
        | TypeCtor of name : UpperIdent
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
    | Ast.NamedVal name ->
        // The heart of this function
        if Set.contains name namesToLookOutFor then
            Set.singleton name
        else
            Set.empty

    | Ast.StrVal _ -> Set.empty
    | Ast.IntVal _ -> Set.empty
    | Ast.ListVal exprs -> Set.collect (getNamesUsedInExpr namesToLookOutFor) exprs
    | Ast.TupleVal (first, second) ->
        Set.union (getNamesUsedInExpr namesToLookOutFor first) (getNamesUsedInExpr namesToLookOutFor second)

    | Ast.LambdaVal (param, body) ->
        // Because if we reference the param name in the body then we're just referencing the param, not the shadowed name from the higher scope
        let withParamRemoved = namesToLookOutFor |> Set.remove param

        getNamesUsedInExpr withParamRemoved body

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
        // This is just syntax sugar for function application

        let withLeftApplied = Ast.FuncApplication (Ast.NamedVal op, left)
        let withRightApplied = Ast.FuncApplication (withLeftApplied, right)

        getNamesUsedInExpr namesToLookOutFor withRightApplied

    | Ast.TypeCtor _ -> Set.empty


let private sortBindingsTopologically
    (namesAndExprs : (LowerIdent * Ast.Expr) seq)
    : DG.StronglyConnectedGraph<Ast.Expr, LowerIdent> list =
    let bindingNames = namesAndExprs |> Seq.map fst |> Set.ofSeq
    let getDependencies = snd >> getNamesUsedInExpr bindingNames >> Set.toSeq

    DG.getStronglyConnectedComponents<LowerIdent * Ast.Expr, LowerIdent> fst getDependencies namesAndExprs
    |> DG.sortOneOrMoreTopologically fst getDependencies
    |> List.map (DG.SCC.map snd)










/// Add a local names map to a global one
let private addLocalNamesMap (localNamesMap : TypedLocalNamesMap) (namesMap : TypedNamesMap) : TypedNamesMap =
    localNamesMap
    |> Map.mapKeyVal (fun key v -> LocalLower key, v)
    // @TODO: this should really throw an error if there are any name clashes so we don't get silently overwritten names
    |> Map.merge namesMap



let private addLocalNamesMapToCtx (localNamesMap : TypedLocalNamesMap) (ctx : Ctx) : Ctx =
    { ctx with
        typedNamesMap = addLocalNamesMap localNamesMap ctx.typedNamesMap }






/// Combine multiple polytypes and combine all their type variables in a single polytype forall clause
let private liftPolyTypesIntoPtc
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
        : Result<ConcreteType, UnificationError> =
        let (ConcType (name, ptcs)) = polyTypeContents

        let replacedTypeParams =
            List.map (applyTypeReplacement tr) ptcs |> Result.sequenceList

        match replacedTypeParams with
        | Ok typeParams -> ConcType (name, typeParams) |> Ok
        | Error e -> Error (NEL.head e)


    and private applyTypeReplacement
        (tr : TypeReplacement)
        (polyTypeContents : PolyTypeContents)
        : Result<PolyTypeContents, UnificationError> =
        match polyTypeContents with
        | PTC.UnificationVar uniVar ->
            if Set.contains uniVar tr.unificationVarsToReplace then
                tr.toReplaceWith

            else
                PTC.UnificationVar uniVar |> Ok

        | TypeVariable typeVar -> TypeVariable typeVar |> Ok
        | ConcreteType concType -> applyTypeReplacementToConcType tr concType |> Result.map ConcreteType
        | PTC.Skolem skolem -> PTC.Skolem skolem |> Ok


    let private applyTypeReplacementToUnificationError
        (tr : TypeReplacement)
        (unifError : UnificationError)
        : UnificationError =
        match unifError with
        | UnificationClash (a, b) ->
            let replacedA = applyTypeReplacementToConcType tr a
            let replacedB = applyTypeReplacementToConcType tr b

            match replacedA, replacedB with
            | Ok replA, Ok replB -> UnificationClash (replA, replB)
            | Error e, _
            | _, Error e -> e

        | UndefinedName name -> UndefinedName name
        | NarrowedSkolem (skolemName, narrowedWith) ->
            let replacedNarrowedWith = applyTypeReplacement tr narrowedWith

            match replacedNarrowedWith with
            | Ok replNarrowedWith -> NarrowedSkolem (skolemName, replNarrowedWith)
            | Error e -> e

        | TriedToUnifyDifferentSkolems (skolem1, skolem2) -> TriedToUnifyDifferentSkolems (skolem1, skolem2)
        | UndefinedTypeCtor name -> UndefinedTypeCtor name


    let private applyTypeReplacementToPtcResult
        (tr : TypeReplacement)
        (polyTypeContentsResult : UnificationResult)
        : UnificationResult =
        match polyTypeContentsResult with
        | Ok polyTypeContents -> applyTypeReplacement tr polyTypeContents
        | Error e -> applyTypeReplacementToUnificationError tr e |> Error







    let private applyTypeReplacementToPolyType
        (normInstr : TypeReplacement)
        (polyType : PolyType)
        : Result<PolyType, UnificationError> =
        let result = applyTypeReplacement normInstr polyType.typeExpr

        match result with
        | Ok result' ->
            Ok
                { typeExpr = result'
                  forall =
                    match normInstr.newTypeVarOpt with
                    | Some newTypeVar -> newTypeVar :: polyType.forall
                    | None -> polyType.forall }
        | Error e -> Error e

    let private applyTypeReplacementToPolyTypeResult
        (tr : TypeReplacement)
        (polyTypeResult : Result<PolyType, UnificationError>)
        : Result<PolyType, UnificationError> =
        match polyTypeResult with
        | Ok polyTypeContents -> applyTypeReplacementToPolyType tr polyTypeContents
        | Error e -> applyTypeReplacementToUnificationError tr e |> Error


    let private applyTypeReplacementToPtcResultOpt
        (tr : TypeReplacement)
        (polyTypeResultOpt : UnificationResult option)
        : UnificationResult option =
        polyTypeResultOpt |> Option.map (applyTypeReplacementToPtcResult tr)



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
        (namesMap : Map<'Name, Result<PolyType, UnificationError>>)
        : Map<'Name, Result<PolyType, UnificationError>> =
        namesMap |> Map.map (fun _ -> applyTypeReplacementToPolyTypeResult tr)


    /// Get the coupled constraints for the provided typeVars and uniVars from the given uniVarsMap
    let private getCoupledConstraintsSet
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




    let private instantiateTypeVarsInUniVarsMap
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







    let private instantiateTypeVarsInUniVarsMapAndLocalNamesMap
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


    let private replaceCoupledConstraintsInTypeUnificationResult
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (constrs : UnificationVarsMap.CoupledConstraints)
        (unifResult : TypeUnificationResult)
        : TypeUnificationResult =
        let replacement =
            coupledConstraintToTypeReplacement unificationVarsWeCanEliminate constrs unifResult.constrained

        let normalisedPolyType =
            applyTypeReplacementToPolyTypeResult replacement.replacementInstruction unifResult.unified

        { unified = normalisedPolyType
          constrained = replacement.replacedUniVarsMap }



    let private concretiseAndGeneraliseSacuv
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


    let private concretiseAndGeneraliseTypeUnificationResult
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyTypeContents)
        : TypeUnificationResult =
        let matchesForBoth =
            getCoupledConstraintsSet unificationVarsWeCanEliminate unificationVarsMap

        matchesForBoth
        |> Set.toList
        |> List.fold
            (fun unifResult coupledConstraints ->
                let replaced =
                    replaceCoupledConstraintsInTypeUnificationResult
                        unificationVarsWeCanEliminate
                        coupledConstraints
                        unifResult

                replaced)
            { unified = Types.makeEmptyPolyType type_ |> Ok
              constrained = unificationVarsMap }


    let private instantiateTypeVarsInPolyType
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (unificationVarsMap : UnificationVarsMap)
        (type_ : PolyType)
        : SelfAndConstrainedUnificationVars =
        concretiseAndGeneraliseSacuv unificationVarsWeCanEliminate unificationVarsMap type_.typeExpr


    let private instantiateTypeVarsInPolyTypeResult
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





    /// Converts a type expression to a PolyTypeContents
    let rec private convertTypeExprToPolyTypeContents (typeExpr : TypeExpr) : PolyTypeContents =
        match typeExpr with
        | TypeExpr (label, params_) ->
            ConcType (label, List.map convertTypeExprToPolyTypeContents params_)
            |> ConcreteType

        | TypeExpr.Skolem name -> PTC.Skolem name


    /// Converts a type expression to a PolyType, automatically generalising any skolems that are not already constrained
    let rec private convertTypeExprToPolyType (constrainedSkolems : LowerIdent set) (typeExpr : TypeExpr) : PolyType =

        let rec traverser (typeExpr : TypeExpr) : PolyTypeContents =
            match typeExpr with
            | TypeExpr (label, params_) -> ConcType (label, List.map traverser params_) |> ConcreteType

            | TypeExpr.Skolem name ->
                if Set.contains name constrainedSkolems then
                    PTC.Skolem name

                else
                    PTC.TypeVariable (makeNewTypeVar ())

        let rec getTypeVars (ptc : PolyTypeContents) : TypeVariableId set =
            match ptc with
            | PTC.TypeVariable tv -> Set.singleton tv
            | PTC.ConcreteType (ConcType (_, params_)) -> Set.collect getTypeVars params_
            | _ -> Set.empty

        let polyTypeContents = traverser typeExpr
        let allNewTypeVars = getTypeVars polyTypeContents

        { forall = Set.toList allNewTypeVars
          typeExpr = polyTypeContents }




    /// Get all the skolems used in a PolyTypeContents
    let rec private getSkolems (ptc : PolyTypeContents) : LowerIdent set =
        match ptc with
        | PTC.Skolem name -> Set.singleton name
        | PTC.TypeVariable _ -> Set.empty
        | PTC.UnificationVar _ -> Set.empty
        | PTC.ConcreteType (ConcType (_, params_)) -> Set.collect getSkolems params_



    let rec private getSkolemsFromTypeExpr
        (unconstrainedSkolems : LowerIdent set)
        (typeExpr : TypeExpr)
        : LowerIdent set =
        match typeExpr with
        | TypeExpr (_, params_) -> Set.collect (getSkolemsFromTypeExpr unconstrainedSkolems) params_
        | TypeExpr.Skolem name -> Set.singleton name



    /// Get all the skolems that are not already constrained because they're in scope
    let private getUnconstrainedSkolems
        (constrainedSkolems : LowerIdent set)
        (ptc : PolyTypeContents)
        : LowerIdent set =
        Set.difference (getSkolems ptc) constrainedSkolems


    /// This takes any non-captured skolems from the type expression and generalises them to type variables
    let private replaceSkolemsInPtcAndMakePolytype
        (constrainedSkolems : LowerIdent set)
        (ptc : PolyTypeContents)
        : PolyType =
        let unconstrainedSkolems = getUnconstrainedSkolems constrainedSkolems ptc

        let skolemToTypeVarsMap : Map<LowerIdent, TypeVariableId> =
            unconstrainedSkolems
            |> Set.map (fun skolem -> skolem, makeNewTypeVar ())
            |> Map.ofSeq


        let rec replaceInPtc (ptc_ : PTC) =
            match ptc_ with
            | PTC.Skolem name ->
                match Map.tryFind name skolemToTypeVarsMap with
                | Some tv -> PTC.TypeVariable tv
                | None -> PTC.Skolem name

            | PTC.TypeVariable tv -> PTC.TypeVariable tv
            | PTC.UnificationVar uv -> PTC.UnificationVar uv
            | PTC.ConcreteType (ConcType (name, params_)) ->
                PTC.ConcreteType (ConcType (name, List.map replaceInPtc params_))

        { forall = Map.values skolemToTypeVarsMap |> Seq.toList
          typeExpr = replaceInPtc ptc }













    //let primitiveTypeExpr label = TypeExpr (label, List.empty)
    //let parametricTypeExpr label typeParams = TypeExpr (label, typeParams)
    let private arrowTypeExpr from to_ = TypeExpr (Types.arrowTypeName, [ from; to_ ])

    let rec private makeArrowTypeFromNel nel =
        let (NEL (head, rest)) = nel

        match rest with
        | [] -> head
        | neck :: tail -> arrowTypeExpr head (makeArrowTypeFromNel (NEL.new_ neck tail))




    /// Represents an extensible base type, where the base type can be extended with more variants
    type BaseType<'T> =
        | Concrete of label : string * typeParams : 'T list
        | UniVar of uniVarId : string


    type OnlyBase = | OnlyBase of BaseType<OnlyBase>


    type WithTypeVar =
        | Base of BaseType<WithTypeVar>
        | TypeVar of string


    type WithSkolem =
        | Base of BaseType<WithSkolem>
        | Skolem of string


    type WithBoth =
        | Base of BaseType<WithBoth>
        | TypeVar of string
        | Skolem of string

    let private handleOnlyBase (onlyBase : OnlyBase) =
        match onlyBase with
        | OnlyBase (Concrete (label, typeParams)) -> ()
        | OnlyBase (UniVar name) -> ()

    let private handleWithSkolem (withSkolem : WithSkolem) =
        match withSkolem with
        | WithSkolem.Base (Concrete (label, typeParams)) -> ()
        | WithSkolem.Base (UniVar name) -> ()
        | WithSkolem.Skolem name -> ()


    let private handleWithTypeVar (withTypeVar : WithTypeVar) =
        match withTypeVar with
        | WithTypeVar.Base (Concrete (label, typeParams)) -> ()
        | WithTypeVar.Base (UniVar name) -> ()
        | WithTypeVar.TypeVar typeVar -> ()


    let private handleWithBoth (withBoth : WithBoth) =
        match withBoth with
        | WithBoth.Base (Concrete (label, typeParams)) -> ()
        | WithBoth.Base (UniVar name) -> ()
        | WithBoth.TypeVar typeVar -> ()
        | WithBoth.Skolem name -> ()






    /// This is needed so we can unify two type expressions, one derived from an expression itself, and one from the type annotation
    let rec private convertTypeExprToPtc (typeExpr : TypeExpr) : PolyTypeContents =
        match typeExpr with
        | TypeExpr (label, params_) -> ConcType (label, List.map convertTypeExprToPtc params_) |> ConcreteType
        | TypeExpr.Skolem name -> PTC.Skolem name






















    /// Given a type annotation of what the expression needs to be, check if the expression indeed has that type. Also ensure that the skolems are not narrowed or unified with anything else, because otherwise the type is actually less general than the one specified in the type annotation, which is wrong.
    let rec private check (ctx : Ctx) (typeAnnotation : TypeExpr) (expr : Ast.Expr) : TypeCheckResult =


        let rec innerCheck (ctx' : Ctx) (typeAnnotation' : TypeExpr) (expr' : Ast.Expr) : TypeCheckResult =

            let expectedType : PolyType =
                convertTypeExprToPolyType ctx'.skolemsInScope typeAnnotation'


            match typeAnnotation', expr' with
            | Types.IsPrimitiveType Types.strTypeName, Ast.StrVal _ -> TypeCheckResult.emptyOk
            | Types.IsPrimitiveType Types.intTypeName, Ast.IntVal _ -> TypeCheckResult.emptyOk

            | Types.IsListOf _, Ast.ListVal [] ->
                // No matter what the type says the list contains, an empty list unifies with anything
                TypeCheckResult.emptyOk

            | Types.IsListOf inner, Ast.ListVal (first :: rest) ->
                let innerResult = innerCheck ctx' inner first

                match innerResult.result with
                | Error _ -> innerResult
                | Ok () ->
                    let listType = Types.listTypeOfExpr inner
                    let restResult = innerCheck ctx' listType (Ast.ListVal rest)

                    tcrCombineUniVarsMap innerResult.constrained restResult


            | Types.IsTupleOf (a, b), Ast.TupleVal (valA, valB) ->
                let resultA = innerCheck ctx' a valA
                let resultB = innerCheck ctx' b valB

                match resultA.result, resultB.result with
                | Error e, _
                | _, Error e -> tcrCombineAndResult resultA.constrained resultB.constrained (Error e)

                | Ok (), Ok () -> tcrCombineAndResult resultA.constrained resultB.constrained (Ok ())


            | Types.IsFuncTypeOf (from, to_), Ast.LambdaVal (param, body) ->
                // @TODO: this approach, where the required type is imposed from the outside, works for now, but won't suffice for the syntax where we can destructure parameters within the lambda expression itself. Because that would mean the parameter value itself can impose a type constraint.

                let fromPolyTypeContents : PolyTypeContents = convertTypeExprToPolyTypeContents from

                let skolemsFromTypeExpr : LowerIdent set =
                    Set.union
                        (getSkolemsFromTypeExpr ctx'.skolemsInScope from)
                        (getSkolemsFromTypeExpr ctx'.skolemsInScope to_)


                let newCtx : Ctx =
                    { ctx' with
                        skolemsInScope = Set.union skolemsFromTypeExpr ctx'.skolemsInScope
                        typedNamesMap =
                            // Add parameter to the names map, with its type taken from the function's type annotation
                            ctx'.typedNamesMap
                            |> Map.add
                                (LocalLower param)
                                (Ok (replaceSkolemsInPtcAndMakePolytype ctx'.skolemsInScope fromPolyTypeContents)) }


                let bodyResult = innerCheck newCtx to_ body
                bodyResult




            | _, Ast.NamedVal name ->
                match Map.tryFind (LocalLower name) ctx'.typedNamesMap with
                | Some (Ok foundType') ->

                    let unified : TypeUnificationResult = unifyTwoTypes expectedType foundType'

                    match unified.unified with
                    | Ok _ -> TypeCheckResult.makeOk unified.constrained
                    | Error e -> TypeCheckResult.makeErr e unified.constrained


                | Some (Error e) -> TypeCheckResult.emptyErr e

                | None -> TypeCheckResult.emptyErr (UndefinedName (LocalLower name))

            | _, Ast.TypeCtor name ->
                match Map.tryFind (LocalUpper name) ctx'.ctorNamesMap with
                | Some ctorArrowOrFinalTypes ->
                    /// E.g. `Maybe a` for the `Nothing` constructor, or `String -> Result e String` for the `Ok` constructor
                    let ctorType = makeArrowTypeFromNel ctorArrowOrFinalTypes

                    let unified =
                        unifyTwoTypeContents (convertTypeExprToPtc ctorType) (convertTypeExprToPtc typeAnnotation')

                    match unified.unified with
                    | Ok _ -> TypeCheckResult.makeOk unified.constrained
                    | Error e -> TypeCheckResult.makeErr e unified.constrained



                | None -> TypeCheckResult.emptyErr (UndefinedTypeCtor (LocalUpper name))


            | _, _ ->
                // Defer to inferred type
                let inferred = inferTypeFromExpr ctx' expr'

                match inferred.self with
                | Ok inferredSelf ->
                    let unified = unifyTwoTypes expectedType inferredSelf

                    TypeCheckResult.make
                        (unified.unified |> Result.map ignore)
                        (combineTwoUnificationVarMaps inferred.constrained unified.constrained)

                | Error e -> TypeCheckResult.makeErr e inferred.constrained


        let newSkolems = getSkolemsFromTypeExpr ctx.skolemsInScope typeAnnotation

        let ctxWithSkolemsAdded =
            { ctx with
                skolemsInScope = Set.union newSkolems ctx.skolemsInScope }

        innerCheck ctxWithSkolemsAdded typeAnnotation expr





    /// Useful for when you only want to return one result, but you need to fold in the unification findings from a separate check or infer result
    and private tcrCombineUniVarsMap (uniVarsMap : UnificationVarsMap) (tcr : TypeCheckResult) : TypeCheckResult =
        { result = tcr.result
          constrained = combineTwoUnificationVarMaps uniVarsMap tcr.constrained }

    and private tcrCombineAndResult uniVarMapA uniVarMapB result =
        { result = result
          constrained = combineTwoUnificationVarMaps uniVarMapA uniVarMapB }



    and inferTypeFromExpr (ctx : Ctx) (expr : Ast.Expr) : SelfAndConstrainedUnificationVars =
        let namesMap = ctx.typedNamesMap

        match expr with
        | Ast.StrVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.strType |> Ok) Map.empty
        | Ast.IntVal _ -> Sacuv.make (Types.makeEmptyPolyType Types.intType |> Ok) Map.empty
        | Ast.ListVal exprs ->
            match exprs with
            | [] -> Sacuv.make (Ok Types.listType) Map.empty
            | only :: [] ->
                let contentType = inferTypeFromExpr ctx only
                Sacuv.make (contentType.self |> Result.map Types.listTypeOf) contentType.constrained

            | head :: rest ->
                let inferred = NEL.map (inferTypeFromExpr ctx) (NEL.new_ head rest)
                let unified = unifyMultipleSacuvs inferred

                unified |> Sacuv.map (Result.map Types.listTypeOf)


        | Ast.TupleVal (first, second) ->
            let inferredFirst = inferTypeFromExpr ctx first
            let inferredSecond = inferTypeFromExpr ctx second

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
            let withNewUnificationVarAddedForParam =
                { ctx with
                    typedNamesMap = Map.add (LocalLower param) (Ok paramPolyType) ctx.typedNamesMap }

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
            let foundType =
                match Map.tryFind (LocalLower name) namesMap with
                | Some t -> t
                | None -> Error (UndefinedName (LocalLower name))

            Sacuv.make foundType Map.empty

        | Ast.LetBindings (bindings, body) -> resolveAllLetBindingsAndBody ctx bindings body


        | Ast.FuncApplication (funcExpr, inputExpr) ->
            let inputType = inferTypeFromExpr ctx inputExpr

            let funcExprType = inferTypeFromExpr ctx funcExpr

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

            let condType =
                inferTypeFromExpr ctx condition
                |> unifyTwoSacuvs (Sacuv.makeEmpty condRequirement)

            let thenType = inferTypeFromExpr ctx thenExpr
            let elseType = inferTypeFromExpr ctx elseExpr

            let combinedReturnType = unifyTwoSacuvs thenType elseType

            let combinedUniVarsMaps =
                combineTwoUnificationVarMaps condType.constrained combinedReturnType.constrained

            Sacuv.make combinedReturnType.self combinedUniVarsMaps


        | Ast.InfixOp (op, left, right) ->
            // This is effectively just applying the function with the infix op's name to two parameters, so we rewrite it as if it were a simple function application

            let withLeftApplied = Ast.FuncApplication (Ast.NamedVal op, left)
            let withRightApplied = Ast.FuncApplication (withLeftApplied, right)

            inferTypeFromExpr ctx withRightApplied


        | Ast.TypeCtor name ->
            match Map.tryFind (LocalUpper name) ctx.ctorNamesMap with
            | Some ctor ->
                let ctorType = makeArrowTypeFromNel ctor
                let polyType = convertTypeExprToPolyType ctx.skolemsInScope ctorType

                Sacuv.make (Ok polyType) Map.empty

            | None -> Sacuv.make (Error (UndefinedTypeCtor (LocalUpper name))) Map.empty



















    and private resolveNamesTopologically
        (ctx : Ctx)
        (namesAndExprs : Ast.LetBindingSingle nel)
        : {| inferredTypes : TypedLocalNamesMap
             constrained : UnificationVarsMap |}
        =
        let (namesWithTypeAnnotations, uniVarsMapFromAnnotateds) : TypedLocalNamesMap * UnificationVarsMap =
            namesAndExprs
            |> Seq.mapFold
                (fun uniVarsMap binding ->
                    match binding.typeAnnotation with
                    | None -> None, uniVarsMap
                    | Some annotation ->
                        let checkResult = check ctx annotation binding.assignedExpr

                        match checkResult.result with
                        | Error e -> Some (binding.name, Error e), checkResult.constrained
                        | Ok () ->
                            let polyType = convertTypeExprToPolyType ctx.skolemsInScope annotation

                            let newUniVarsMap = combineTwoUnificationVarMaps uniVarsMap checkResult.constrained

                            Some (binding.name, Ok polyType), newUniVarsMap)
                Map.empty
            |> Tuple.mapFst (Seq.choose id >> Map.ofSeq)



        let hasTypeAnnotation name namesMap = Map.tryFind name namesMap |> Option.isSome

        /// But only if this isn't already in the map because it has an explicit type annotatino
        let addToLocalNamesMap name okSelf (localNamesMap : TypedLocalNamesMap) =
            if hasTypeAnnotation name localNamesMap then
                localNamesMap

            else
                Map.add name okSelf localNamesMap


        /// But only if this isn't already in the map because it has an explicit type annotatino
        let addToGlobalNamesMap name okSelf (namesMap : TypedNamesMap) =
            if hasTypeAnnotation name namesMap then
                namesMap

            else
                Map.add name okSelf namesMap



        let orderedBindings =
            namesAndExprs
            |> Seq.map (fun binding -> binding.name, binding.assignedExpr)
            |> sortBindingsTopologically

        let localNamesMap, uniVarsMap =
            orderedBindings
            |> List.fold
                (fun (localNamesMap, uniVarsMap) stronglyConnectedComponent ->
                    let combinedNamesMap : Ctx =
                        { ctx with
                            typedNamesMap = addLocalNamesMap localNamesMap ctx.typedNamesMap }

                    // @TODO: we should surface any inference errors instead of just ignoring them and skipping that step in the fold!
                    match stronglyConnectedComponent with
                    | DG.SingleNonRec (name, expr) ->
                        let inferredType = inferTypeFromExpr combinedNamesMap expr

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        let withThisBindingAdded : TypedLocalNamesMap =
                            addToLocalNamesMap name inferredType.self localNamesMap

                        withThisBindingAdded, combinedMapResult

                    | DG.SingleSelfRec (name, expr) ->
                        let newUniVar = makeNewUniVar ()

                        let withThisNameUniVarAdded : Ctx =
                            { ctx with
                                typedNamesMap =
                                    addToGlobalNamesMap
                                        (LocalLower name)
                                        (PTC.UnificationVar newUniVar |> Types.makeEmptyPolyType |> Ok)
                                        combinedNamesMap.typedNamesMap }

                        let inferredType = inferTypeFromExpr withThisNameUniVarAdded expr

                        let combinedMapResult =
                            combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                        let withThisBindingAdded : TypedLocalNamesMap =
                            addToLocalNamesMap name inferredType.self localNamesMap

                        let result =
                            instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                                (Set.singleton newUniVar)
                                withThisBindingAdded
                                combinedMapResult

                        fst result, snd result


                    | DG.MutualRecursive namesAndBindings ->
                        let newUniVars =
                            namesAndBindings |> Seq.map (fun (name, _) -> name, makeNewUniVar ())

                        let withNewUniVarsAdded : Ctx =
                            { ctx with
                                typedNamesMap =
                                    newUniVars
                                    |> Seq.fold
                                        (fun map (name, uniVar) ->
                                            let typeToAdd = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
                                            addToGlobalNamesMap (LocalLower name) typeToAdd map)
                                        combinedNamesMap.typedNamesMap }


                        let newLocalNamesMap, newUniVarsMap =
                            namesAndBindings
                            |> Seq.fold
                                (fun (localNamesMap, uniVarsMap) (name, expr) ->
                                    let inferredType = inferTypeFromExpr withNewUniVarsAdded expr

                                    let withThisBindingAdded : TypedLocalNamesMap =
                                        addToLocalNamesMap name inferredType.self localNamesMap

                                    let combinedMapResult =
                                        combineTwoUnificationVarMaps uniVarsMap inferredType.constrained

                                    withThisBindingAdded, combinedMapResult)
                                (localNamesMap, uniVarsMap)


                        let instantiated =
                            instantiateTypeVarsInUniVarsMapAndLocalNamesMap
                                (newUniVars |> Seq.map snd |> Set.ofSeq)
                                newLocalNamesMap
                                newUniVarsMap

                        fst instantiated, snd instantiated

                )
                (namesWithTypeAnnotations, uniVarsMapFromAnnotateds)

        {| inferredTypes = localNamesMap
           constrained = uniVarsMap |}





    and private resolveAllLetBindingsAndBody
        (ctx : Ctx)
        (letBindings : Ast.LetBindingSingle nel)
        (body : Ast.Expr)
        : SelfAndConstrainedUnificationVars =
        let bindingsResolutionResult = resolveNamesTopologically ctx letBindings

        let combinedNamesMap : Ctx =
            { ctx with
                typedNamesMap = addLocalNamesMap bindingsResolutionResult.inferredTypes ctx.typedNamesMap }

        let bodyResult : SelfAndConstrainedUnificationVars =
            inferTypeFromExpr combinedNamesMap body

        let combinedUniVarMap : UnificationVarsMap =
            combineTwoUnificationVarMaps bindingsResolutionResult.constrained bodyResult.constrained

        Sacuv.make bodyResult.self combinedUniVarMap
































    (*

        Type unification

    *)





    and unifyTwoTypes (type1 : PolyType) (type2 : PolyType) : TypeUnificationResult =


        let rec swapOutTypeVars (typeVarToUniVarMap : Map<TypeVariableId, UnificationVarId>) (ptc : PolyTypeContents) =
            match ptc with
            | UnificationVar id -> UnificationVar id
            | ConcreteType (ConcType (name, typeParams)) ->
                ConcreteType
                <| ConcType (name, List.map (swapOutTypeVars typeVarToUniVarMap) typeParams)
            | PTC.Skolem name -> PTC.Skolem name

            | TypeVariable tv ->
                match Map.tryFind tv typeVarToUniVarMap with
                | Some uniVar -> UnificationVar uniVar
                | None ->
                    failwith
                        "Each type variable should have a unification variable assigned to replace it, so this should not be possible"



        let allTypeVars = type1.forall @ type2.forall

        let typeVarsToUniVar =
            allTypeVars |> List.map (fun typeVar -> typeVar, makeNewUniVar ()) |> Map.ofList

        let replacedType1 : PolyTypeContents =
            swapOutTypeVars typeVarsToUniVar type1.typeExpr

        let replacedType2 : PolyTypeContents =
            swapOutTypeVars typeVarsToUniVar type2.typeExpr


        let unified : TypeUnificationResult =
            unifyTwoTypeContents replacedType1 replacedType2

        match unified.unified with
        | Ok okSelf ->
            concretiseAndGeneraliseTypeUnificationResult
                (Set.ofSeq <| Map.values typeVarsToUniVar)
                unified.constrained
                okSelf.typeExpr

        | Error e ->
            // @TODO: we can probably just concretise and generalise this too by chucking it into a version of concretiseAndGeneralise that handles Results
            { unified = Error e
              constrained = unified.constrained }



    and private unifyTwoTypeContents (type1 : PolyTypeContents) (type2 : PolyTypeContents) : TypeUnificationResult =
        match type1, type2 with
        | PTC.TypeVariable _, _
        | _, PTC.TypeVariable _ -> failwith "All type variables should have been swapped out for unification variables!"

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

                                unificationResult.unified, combineResult)
                            Map.empty

                    { unified =
                        match Result.sequenceList paramsResults with
                        | Ok unifiedParams ->
                            liftPolyTypesIntoPtc (fun p -> PTC.ConcreteType <| ConcType (name1, p)) unifiedParams
                            |> Ok
                        | Error errs -> NEL.head errs |> Error

                      constrained = unificationVarMap }


                | Error _ ->
                    { unified = UnificationError.makeClash concType1 concType2 |> Error
                      constrained = Map.empty }

            else
                { unified = UnificationError.makeClash concType1 concType2 |> Error
                  constrained = Map.empty }


        | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
            if uniVar1 = uniVar2 then
                { unified = type1 |> Types.makeEmptyPolyType |> Ok
                  constrained = Map.empty }

            else
                /// Just so we have a consistent ordering so we avoid accidentally creating cycles of unification vars that don't lead anywhere
                let smallerUniVar, biggerUniVar = sortItems uniVar1 uniVar2

                /// The logic here being that we redirect one unification var to the other one. By convention we make the self type be the smaller uniVar, add an entry in the unification map to point it to the bigger one.
                /// The bigger one will keep pointing to whatever it's pointing to in other unification maps, and the smaller one in other maps will be unified with the bigger one, which will result in unifying the bigger one with a concrete type.
                let constrained : UnificationVarsMap =
                    Map.singleton smallerUniVar (UnifResult (PTC.UnificationVar biggerUniVar |> Ok |> Some))

                { unified = PTC.UnificationVar smallerUniVar |> Types.makeEmptyPolyType |> Ok
                  constrained = constrained }


        | PTC.UnificationVar uniVar, PTC.ConcreteType (ConcType (name, typeVars))
        | PTC.ConcreteType (ConcType (name, typeVars)), PTC.UnificationVar uniVar ->
            let uniVarsMap : UnificationVarsMap =
                Map.singleton uniVar (UnifResult (PTC.ConcreteType (ConcType (name, typeVars)) |> Ok |> Some))

            { unified = PTC.UnificationVar uniVar |> Types.makeEmptyPolyType |> Ok
              constrained = uniVarsMap }

        | PTC.Skolem name1, PTC.Skolem name2 ->
            if name1 = name2 then
                { unified = Types.makeEmptyPolyType (PTC.Skolem name1) |> Ok
                  constrained = Map.empty }

            else
                { unified = TriedToUnifyDifferentSkolems (name1, name2) |> Error
                  constrained = Map.empty }

        | PTC.Skolem name, t
        | t, PTC.Skolem name ->
            { unified = NarrowedSkolem (name, t) |> Error
              constrained = Map.empty }







    and private unifyTwoTypeContentsResults
        (typeContentResult1 : Result<PolyTypeContents, UnificationError>)
        (typeContentResult2 : Result<PolyTypeContents, UnificationError>)
        : TypeUnificationResult =
        match typeContentResult1, typeContentResult2 with
        | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents typeContent1 typeContent2

        | Error e, _
        | _, Error e ->
            { unified = Error e
              constrained = Map.empty }


    and private unifyTwoTypeResults
        (typeResult1 : Result<PolyType, UnificationError>)
        (typeResult2 : Result<PolyType, UnificationError>)
        : TypeUnificationResult =
        match typeResult1, typeResult2 with
        | Ok type1, Ok type2 -> unifyTwoTypes type1 type2

        | Error e, _
        | _, Error e ->
            { unified = Error e
              constrained = Map.empty }




    and private unifyTwoTypeResultsOpts
        (typeOpt1 : Result<PolyType, UnificationError> option)
        (typeOpt2 : Result<PolyType, UnificationError> option)
        : {| unified : Result<PolyType, UnificationError> option
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeResults type1 type2

            {| unified = Some result.unified
               constrained = result.constrained |}

        | Some type_, None
        | None, Some type_ ->
            {| unified = Some type_
               constrained = Map.empty |}

        | None, None ->
            {| unified = None
               constrained = Map.empty |}


    and private unifyTwoTypeContentsResultsOpts
        (typeOpt1 : Result<PolyTypeContents, UnificationError> option)
        (typeOpt2 : Result<PolyTypeContents, UnificationError> option)
        : {| unified : Result<PolyType, UnificationError> option
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeContentsResults type1 type2

            {| unified = Some result.unified
               constrained = result.constrained |}

        | Some type_, None
        | None, Some type_ ->
            {| unified = Some (Result.map Types.makeEmptyPolyType type_)
               constrained = Map.empty |}

        | None, None ->
            {| unified = None
               constrained = Map.empty |}


    and private unifyTwoTypeContentsOpts
        (typeOpt1 : PolyTypeContents option)
        (typeOpt2 : PolyTypeContents option)
        : {| unified : Result<PolyType, UnificationError> option
             constrained : UnificationVarsMap |}
        =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 ->
            let result = unifyTwoTypeContents type1 type2

            {| unified = Some result.unified
               constrained = result.constrained |}

        | None, None ->
            {| unified = None
               constrained = Map.empty |}

        | Some type_, None
        | None, Some type_ ->
            {| unified = Some (Ok (Types.makeEmptyPolyType type_))
               constrained = Map.empty |}



    and private unifyManyTypeContents (types : PolyTypeContents nel) : TypeUnificationResult =
        let (NEL (first, rest)) = types

        let combinedType, combinedUnificationMap =
            rest
            |> List.fold
                (fun (combinedType, combinedUniMap) polyTypeContents ->
                    let result =
                        unifyTwoTypeResults combinedType (Ok (Types.makeEmptyPolyType polyTypeContents))

                    let combineResult = combineTwoUnificationVarMaps combinedUniMap result.constrained

                    result.unified, combineResult)
                (Ok (Types.makeEmptyPolyType first), Map.empty)

        { unified = combinedType
          constrained = combinedUnificationMap }



    and private unifyManyTypes (types : PolyType nel) : TypeUnificationResult =
        let (NEL (first, rest)) = types

        let combinedType, combinedUnificationMap =
            rest
            |> List.fold
                (fun (combinedType, combinedUniMap) polyType ->
                    let result = unifyTwoTypeResults combinedType (Ok polyType)

                    let combineResult = combineTwoUnificationVarMaps combinedUniMap result.constrained

                    result.unified, combineResult)
                (Ok first, Map.empty)

        { unified = combinedType
          constrained = combinedUnificationMap }








    and private combineTwoUnificationVarMaps
        (map1 : UnificationVarsMap)
        (map2 : UnificationVarsMap)
        : UnificationVarsMap =
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
                    |> Map.add uniVar (UnifResult (unifiedResult.unified |> Option.map (Result.map _.typeExpr)))
                    |> instantiateTypeVarsInUniVarsMap Set.empty


            | (UnifRedirect redirect, redirectMap), (UnifResult res, _)
            | (UnifResult res, _), (UnifRedirect redirect, redirectMap) ->
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
                    |> Map.add uniVar (UnifResult (unifiedResult.unified |> Option.map (Result.map _.typeExpr)))
                    |> instantiateTypeVarsInUniVarsMap Set.empty



            | (UnifResult res1, _), (UnifResult res2, _) ->
                let unifiedResult = unifyTwoTypeContentsResultsOpts res1 res2

                let combineResult =
                    combineTwoUnificationVarMaps uniVarsMap unifiedResult.constrained

                combineResult
                |> Map.add uniVar (UnifResult (unifiedResult.unified |> Option.map (Result.map _.typeExpr)))
                |> instantiateTypeVarsInUniVarsMap Set.empty



        Map.foldAllEntries singleFolder singleFolder folder map1 map2 Map.empty







    and private combineUnificationVarMapsSeq : UnificationVarsMap seq -> UnificationVarsMap =
        Seq.fold combineTwoUnificationVarMaps Map.empty


    /// Unify two `SelfAndConstrainedUnificationVars`s
    and private unifyTwoSacuvs
        (sacuv1 : SelfAndConstrainedUnificationVars)
        (sacuv2 : SelfAndConstrainedUnificationVars)
        : SelfAndConstrainedUnificationVars =
        let combinedSelf = unifyTwoTypeResults sacuv1.self sacuv2.self

        let combinedUniVarMap =
            combineUnificationVarMapsSeq [ sacuv1.constrained; sacuv2.constrained; combinedSelf.constrained ]

        { self = combinedSelf.unified
          constrained = combinedUniVarMap }



    and private unifyMultipleSacuvs
        (sacuvs : SelfAndConstrainedUnificationVars nel)
        : SelfAndConstrainedUnificationVars =
        let (NEL (head, rest)) = sacuvs
        List.fold unifyTwoSacuvs head rest

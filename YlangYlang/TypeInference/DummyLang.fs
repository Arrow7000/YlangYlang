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
    /// Referencing a unification variable.
    | UnificationVar of UnificationVariable
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


and UniVarContent =
    { id : UnificationVarId
      constrained : PolyTypeContents option }


and UnificationVariable =
    { content : UniVarContent ref }

    static member getId (uniVar : UnificationVariable) = uniVar.content.Value.id
    static member makeNew (uniVarId : UnificationVarId) = { content = ref { id = uniVarId; constrained = None } }

    override this.ToString () =
        let id = UnificationVariable.getId this

        match this.content.Value.constrained with
        | Some constrained -> $"({string id} : {string constrained})"
        | None -> string id


type UnificationError =
    | UnificationClash of ConcreteType * ConcreteType
    | UndefinedName of LowerNameValue
    | UndefinedTypeCtor of UpperNameValue
    /// Skolems only unify with themselves, so different skolems can't be unified with each other
    | TriedToUnifyDifferentSkolems of skolem1 : LowerIdent * skolem2 : LowerIdent
    /// Skolems only unify with themselves, not with anything else
    | NarrowedSkolem of skolemName : LowerIdent * narrowedWith : PolyTypeContents
    | InfinitelyRecursiveType of unified : UnificationVariable * with_ : PolyTypeContents

    override this.ToString () =
        match this with
        | UnificationClash (conc1, conc2) -> "Unification clash: `" + string conc1 + "` and `" + string conc2 + "`"
        | UndefinedName name -> "Undefined name: " + string name
        | UndefinedTypeCtor name -> "Undefined type constructor: " + string name
        | TriedToUnifyDifferentSkolems (skolem1, skolem2) ->
            "Tried to unify different skolems: " + string skolem1 + " and " + string skolem2
        | NarrowedSkolem (skolemName, narrowedWith) ->
            "Narrowed skolem: " + string skolemName + " with " + string narrowedWith
        | InfinitelyRecursiveType (uniVar, ptc) ->
            "Infinitely recursive type, tried to unify unification variable "
            + string uniVar
            + " with type "
            + string ptc


    static member makeClash conc1 conc2 =
        // // Uncomment when debugging unexpected type errors
        //failwith ("Unification clash: `" + string conc1 + "` and `" + string conc2 + "`")

        UnificationClash (conc1, conc2)







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





/// The context where we put the names with their type checked types
type TypedNamesMap = Map<LowerNameValue, Result<PolyType, UnificationError>>

/// This maps from constructor names to the parameters that the variant needs to the signature of the constructor; e.g. `String -> Int -> Maybe (String, Int)`.
/// But it could also be e.g. `None`, which would have as its value the single type expression `Maybe a`
///
///The list represents the parameters for this particular constructor
type CtorNamesMap = Map<UpperNameValue, TypeExpr nel>



type NewUnificationVarsMap = Map<UnificationVarId, Result<PolyTypeContents, UnificationError> option ref>




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





///// A unification result or a redirect to another entry. Having multiple unification variables pointing to the same unification result lets us represent multiple unification variables that have been unified with each other. And having a set of type variables pointing to the same unification result lets us represent multiple type variables that have been unified with each other; and thereby also multiple unification variables that have been unified with multiple type variables.
///// FYI having multiple unification variables unified with each other can take the form of multiple uniVars all redirecting to the same one, or multiple uniVars redirecting to each other in a chain, or a combination of both in a kind of tree structure where each entry points to its parent, and the root of the tree is the unification result.
///// Instantiating a type variable with a fresh unification variable is done by following that unification variable's redirect chain until you get to the root entry, and then adding that type variable to the set of type variables in the root.
//type UnifResOrRedirect =
//    /// Unification result
//    | UnifResult of Result<PolyTypeContents, UnificationError> option
//    /// Redirect to another unification variable to represent that they are unified with each other
//    | UnifRedirect of UnificationVarId



///// @TODO: for the real thing, this should include information about the location of the error, so that we can give a nice error message to the user, ideally with the exact code causing the error, with the relevant parts highlighted
//type InnerTypeError =
//    /// Although the binding has a type annotation, the value actually has a type error
//    | ErrorHiddenByAnnotation of unificationErr : UnificationError

//    /// The binding doesn't have an internal type error, but the type doesn't match the declared annotation
//    | AnnotationVsInferenceClash of
//        typeVars : TypeVariableId list *
//        annotated : PolyTypeContents *
//        inferred : PolyTypeContents



///// THIS is basically the new version of the Accumulator, because it gathers unification constraints on variables, and so every inferExpressionType function will return one of these and so they need to be combined to get the full constraints for each unification variable. Then, with all of the gathered constraints on each unification variable, we can assign that type to the name, and then use that inferred type as the type for that name, and then proceed to see if that inferred type is indeed compatible with all the other uses of that name.
//type UnificationVarsMap = Map<UnificationVarId, UnifResOrRedirect>





//module UnificationVarsMap =
//    let private findByUnificationVar (uniVar : UnificationVarId) (map : UnificationVarsMap) : UnifResOrRedirect =
//        match Map.tryFind uniVar map with
//        | Some v -> v
//        | None ->
//            // If a uniVar doesn't have any constraints yet it may not be in the uniVarsmap, so we just return as if it was in the map with no constraints
//            UnifResult None

//    let rec findUnificationVarResult
//        (uniVar : UnificationVarId)
//        (map : UnificationVarsMap)
//        : UnificationVarId * UnificationResult option =
//        match findByUnificationVar uniVar map with
//        | UnifRedirect redirectUniVar -> findUnificationVarResult redirectUniVar map
//        | UnifResult res ->
//            // Return the result as well as the final unification variable at that location
//            uniVar, res


//    type private UnificationVarResultWithSteps =
//        {
//            /// The (reversed) list of steps we took before we got to the final unification var
//            hops : UnificationVarId list
//            finalUnificationVar : UnificationVarId
//            result : UnificationResult option
//        }


//    /// This gets the unification result, but also includes all the unification variables we encountered during our redirect hops
//    let rec private findUnificationVarResultWithSteps uniVar map : UnificationVarResultWithSteps =
//        match findByUnificationVar uniVar map with
//        | UnifRedirect redirectUniVar ->
//            let result = findUnificationVarResultWithSteps redirectUniVar map

//            { result with
//                hops = redirectUniVar :: result.hops }

//        | UnifResult res ->
//            { hops = List.empty
//              finalUnificationVar = uniVar
//              result = res }




//    /// Represents a single entry in the unification vars map of all the things that are bound to the same constraints, along with the constraint itself
//    type CoupledConstraints =
//        { finalUniVar : UnificationVarId
//          otherUniVars : UnificationVarId set
//          result : UnificationResult option }

//        member this.allUniVars : UnificationVarId set =
//            Set.add this.finalUniVar this.otherUniVars



//    /// Gets all the unification variables that have been unified with the given unification variable, via traversing all the redirects
//    let getAllJoinedUnificationVars (uniVar : UnificationVarId) (map : UnificationVarsMap) : CoupledConstraints =
//        let finalUnivar, res = findUnificationVarResult uniVar map

//        let linkedUnificationVars : UnificationVarId set =
//            map
//            |> Map.choose (fun key _ ->
//                let result = findUnificationVarResultWithSteps key map

//                if result.finalUnificationVar = finalUnivar then
//                    Some result.hops

//                else
//                    None)
//            |> Map.values
//            |> Seq.concat
//            |> Set.ofSeq


//        { finalUniVar = finalUnivar
//          otherUniVars = linkedUnificationVars
//          result = res }




///// The result of every type inference or unification: contains the inferred or unified type itself, plus the map of constrained unification variables as gleaned from the inference/unification
//type SelfAndConstrainedUnificationVars =
//    { self : Result<PolyType, UnificationError>
//      constrained : UnificationVarsMap }



//module SelfAndConstrainedUnificationVars =
//    /// Make without errors
//    let make result constrained : SelfAndConstrainedUnificationVars =
//        { self = result
//          constrained = constrained }


//    /// Make with only a self type, no constraineds
//    let makeEmpty result : SelfAndConstrainedUnificationVars = make result Map.empty

//    let map f sacuv =
//        { self = f sacuv.self
//          constrained = sacuv.constrained }



/////// Bubble up the result-ness of the .self field onto the record as a whole
////let sequenceResult sacuv =
////    sacuv.self
////    |> Result.map (fun self ->
////        {| constrained = sacuv.constrained
////           self = self |})


///// @TODO: is there a specific reason this couldn't just be a `SelfAndConstrainedUnificationVars`?
//type TypeUnificationResult =
//    { unified : Result<PolyType, UnificationError>
//      constrained : UnificationVarsMap }



///// The result of a check call, which is only done if we have an expected type we are checking the expression against
//type TypeCheckResult =
//    { result : Result<unit, UnificationError>
//      constrained : UnificationVarsMap }



//module TypeCheckResult =

//    let singleton result : TypeCheckResult =
//        { result = result
//          constrained = Map.empty }

//    let make result constrained : TypeCheckResult =
//        { result = result
//          constrained = constrained }

//    let makeOk = make (Ok ())
//    let makeErr err = make (Error err)

//    let emptyOk : TypeCheckResult = singleton (Ok ())
//    let emptyErr e : TypeCheckResult = singleton (Error e)




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



    /// Converts a type expression to a PolyTypeContents
    let rec private convertTypeExprToPolyTypeContents (typeExpr : TypeExpr) : PolyTypeContents =
        match typeExpr with
        | TypeExpr (label, params_) ->
            ConcType (label, List.map convertTypeExprToPolyTypeContents params_)
            |> ConcreteType

        | TypeExpr.Skolem name -> PTC.Skolem name







    let rec private getSkolemsFromTypeExpr (typeExpr : TypeExpr) : LowerIdent set =
        match typeExpr with
        | TypeExpr (_, params_) -> Set.collect getSkolemsFromTypeExpr params_
        | TypeExpr.Skolem name -> Set.singleton name



    /// Converts a type expression to a PolyType, automatically generalising any skolems that are not already constrained
    let rec private convertTypeExprToPolyType (constrainedSkolems : LowerIdent set) (typeExpr : TypeExpr) : PolyType =
        let allSkolems = getSkolemsFromTypeExpr typeExpr
        let unconstrainedSkolems = Set.difference allSkolems constrainedSkolems

        let unconstrSkolemTypeVarMap : Map<LowerIdent, TypeVariableId> =
            unconstrainedSkolems
            |> Set.map (fun skolem -> skolem, makeNewTypeVar ())
            |> Map.ofSeq

        let rec traverser (typeExpr : TypeExpr) : PolyTypeContents =
            match typeExpr with
            | TypeExpr (label, params_) -> ConcType (label, List.map traverser params_) |> ConcreteType

            | TypeExpr.Skolem name ->
                match Map.tryFind name unconstrSkolemTypeVarMap with
                | None -> PTC.Skolem name
                | Some typeVar -> PTC.TypeVariable typeVar


        let rec getTypeVars (ptc : PolyTypeContents) : TypeVariableId set =
            match ptc with
            | PTC.TypeVariable tv -> Set.singleton tv
            | PTC.ConcreteType (ConcType (_, params_)) -> Set.collect getTypeVars params_
            | PTC.Skolem _ -> Set.empty
            | PTC.UnificationVar uniVar ->
                match uniVar.content.Value.constrained with
                | None -> Set.empty
                | Some constrained -> getTypeVars constrained

        let polyTypeContents = traverser typeExpr
        let allNewTypeVars = getTypeVars polyTypeContents

        { forall = Set.toList allNewTypeVars
          typeExpr = polyTypeContents }














    /// This will replace the univars with their constraints and it will generalise unconstrained univars to type variables.
    /// It also returns all type variables from the PTC, whether new from the zonking or already present. This means this polytype can just cleanly replace any polytype that this PTC came from.
    let private zonkPolyTypeContents (uniVars : UnificationVarId set) (ptc : PolyTypeContents) : PolyType =
        let uniVarsToTypeVarsMap : Map<UnificationVarId, TypeVariableId> =
            uniVars |> Set.map (fun uniVarId -> uniVarId, makeNewTypeVar ()) |> Map.ofSeq

        let rec replaceAndGetTypeVars (ptc : PolyTypeContents) : PolyTypeContents * TypeVariableId set =
            match ptc with
            | UnificationVar uniVar ->
                match Map.tryFind uniVar.content.Value.id uniVarsToTypeVarsMap with
                | Some typeVarToReplace ->
                    match uniVar.content.Value.constrained with
                    | None ->
                        // If unconstrained, this will be a free type variable
                        TypeVariable typeVarToReplace, Set.singleton typeVarToReplace

                    | Some constrained ->
                        // If constrained, replace with the constrained concrete type
                        replaceAndGetTypeVars constrained

                | None ->
                    match uniVar.content.Value.constrained with
                    | None ->
                        // I.e. this is not one of the univars we need to zonk, and there are no constraints to recursively zonk on, so we just return the empty univar as is
                        PTC.UnificationVar uniVar, Set.empty

                    | Some constrained ->
                        // If constrained, replace with the constrained concrete type
                        replaceAndGetTypeVars constrained

            | TypeVariable tv -> PTC.TypeVariable tv, Set.singleton tv
            | Skolem name -> PTC.Skolem name, Set.empty
            | ConcreteType (ConcType (name, params_)) ->
                let replacedParams, typeVars = List.map replaceAndGetTypeVars params_ |> List.unzip
                PTC.ConcreteType (ConcType (name, replacedParams)), Set.unionMany typeVars

        let replacedPtc, newTypeVars = replaceAndGetTypeVars ptc

        { forall = Set.toList newTypeVars
          typeExpr = replacedPtc }



    let private zonkPolyTypeContentsResult
        (uniVars : UnificationVarId set)
        (ptcResult : Result<PolyTypeContents, UnificationError>)
        : Result<PolyType, UnificationError> =
        // @TODO we should probably zonk the UnificationError contents also!
        Result.map (zonkPolyTypeContents uniVars) ptcResult


    let private zonkPolyType (unificationVarsWeCanEliminate : UnificationVarId set) (type_ : PolyType) : PolyType =
        // This is fine to replace the whole original polytype because the zonking will include all typevars present in the PTC anyway, so no need to keep hold of the original `forall`s.
        zonkPolyTypeContents unificationVarsWeCanEliminate type_.typeExpr


    // // @TODO the problem with this was that zonking always returns a PolyType, but the various error variants expect more specific things. Maybe that's fine though? Maybe we don't need to zonk this after all, because with the new mutable approach univars contain all their constraint information anyway?
    //let private zonkUnificationErr
    //    (unificationVarsWeCanEliminate : UnificationVarId set)
    //    (err : UnificationError)
    //    : UnificationError =
    //    match err with
    //    | UndefinedName _
    //    | UndefinedTypeCtor _
    //    | TriedToUnifyDifferentSkolems _ -> err
    //    | UnificationClash (a, b) -> zonkConcreteType

    /// @TODO we should probably apply this to the error branch as well
    let private zonkPolyTypeResult
        (unificationVarsWeCanEliminate : UnificationVarId set)
        (type_ : Result<PolyType, UnificationError>)
        : Result<PolyType, UnificationError> =
        Result.map (zonkPolyType unificationVarsWeCanEliminate) type_












    /// Get all the skolems used in a PolyTypeContents
    let rec private getSkolems (ptc : PolyTypeContents) : LowerIdent set =
        match ptc with
        | PTC.Skolem name -> Set.singleton name
        | PTC.TypeVariable _ -> Set.empty
        | PTC.UnificationVar _ -> Set.empty
        | PTC.ConcreteType (ConcType (_, params_)) -> Set.collect getSkolems params_




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


        let rec replaceSkolemsInPtc (ptc_ : PTC) =
            match ptc_ with
            | PTC.Skolem name ->
                match Map.tryFind name skolemToTypeVarsMap with
                | Some tv -> PTC.TypeVariable tv
                | None -> PTC.Skolem name

            | PTC.TypeVariable tv -> PTC.TypeVariable tv
            | PTC.UnificationVar uv -> PTC.UnificationVar uv
            | PTC.ConcreteType (ConcType (name, params_)) ->
                PTC.ConcreteType (ConcType (name, List.map replaceSkolemsInPtc params_))

        // @TODO we should probably be a bit cleverer about this and only return typevars that are actually present in the PTC, so we don't needlessly include typevars that don't make an actual appearance in the PTC
        { forall = Map.values skolemToTypeVarsMap |> Seq.toList
          typeExpr = replaceSkolemsInPtc ptc }













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



















    let rec private check (ctx : Ctx) (typeAnnotation : TypeExpr) (expr : Ast.Expr) : Result<unit, UnificationError> =

        let rec innerCheck
            (ctx' : Ctx)
            (typeAnnotation' : TypeExpr)
            (expr' : Ast.Expr)
            : Result<unit, UnificationError> =

            let expectedType : PolyType =
                convertTypeExprToPolyType ctx'.skolemsInScope typeAnnotation'


            match typeAnnotation', expr' with
            | Types.IsPrimitiveType Types.strTypeName, Ast.StrVal _ -> Ok ()
            | Types.IsPrimitiveType Types.intTypeName, Ast.IntVal _ -> Ok ()

            | Types.IsListOf _, Ast.ListVal [] ->
                // No matter what the type says the list contains, an empty list unifies with anything
                Ok ()

            | Types.IsListOf inner, Ast.ListVal (first :: rest) ->
                let innerResult = innerCheck ctx' inner first

                match innerResult with
                | Error _ -> innerResult
                | Ok () ->
                    let listType = Types.listTypeOfExpr inner
                    let restResult = innerCheck ctx' listType (Ast.ListVal rest)

                    restResult


            | Types.IsTupleOf (a, b), Ast.TupleVal (valA, valB) ->
                let resultA = innerCheck ctx' a valA
                let resultB = innerCheck ctx' b valB

                match resultA, resultB with
                | Error e, _
                | _, Error e -> Error e

                | Ok (), Ok () -> Ok ()


            | Types.IsFuncTypeOf (from, to_), Ast.LambdaVal (param, body) ->
                // @TODO: this approach, where the required type is imposed from the outside, works for now, but won't suffice for the syntax where we can destructure parameters within the lambda expression itself. Because that would mean the parameter value itself can impose a type constraint.

                let fromPolyTypeContents : PolyTypeContents = convertTypeExprToPolyTypeContents from

                let skolemsFromTypeExpr : LowerIdent set =
                    Set.union (getSkolemsFromTypeExpr from) (getSkolemsFromTypeExpr to_)


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

                    let unified = unifyTwoTypes expectedType foundType'

                    unified |> Result.map ignore

                | Some (Error e) -> Error e

                | None -> Error (UndefinedName (LocalLower name))

            | _, Ast.TypeCtor name ->
                match Map.tryFind (LocalUpper name) ctx'.ctorNamesMap with
                | Some ctorArrowOrFinalTypes ->
                    /// E.g. `Maybe a` for the `Nothing` constructor, or `String -> Result e String` for the `Ok` constructor
                    let ctorType = makeArrowTypeFromNel ctorArrowOrFinalTypes

                    let unified =
                        unifyTwoTypeContents (convertTypeExprToPtc ctorType) (convertTypeExprToPtc typeAnnotation')

                    unified |> Result.map ignore



                | None -> Error (UndefinedTypeCtor (LocalUpper name))


            | _, _ ->
                // Defer to inferred type
                let inferred = inferTypeFromExpr ctx' expr'

                match inferred with
                | Ok inferredSelf ->
                    let unified = unifyTwoTypes expectedType inferredSelf
                    unified |> Result.map ignore

                | Error e -> Error e


        let newSkolems = getSkolemsFromTypeExpr typeAnnotation

        let ctxWithSkolemsAdded =
            { ctx with
                skolemsInScope = Set.union newSkolems ctx.skolemsInScope }

        innerCheck ctxWithSkolemsAdded typeAnnotation expr














    /// Goes through a list of let bindings and type infers and checks their values to construct a typed names map of their names and types
    and private resolveNamesTopologically (ctx : Ctx) (namesAndExprs : Ast.LetBindingSingle nel) : TypedLocalNamesMap =
        let namesWithTypeAnnotations : TypedLocalNamesMap =
            namesAndExprs
            |> Seq.map (fun binding ->
                match binding.typeAnnotation with
                | None -> None
                | Some annotation ->
                    let checkResult = check ctx annotation binding.assignedExpr

                    match checkResult with
                    | Error e -> Some (binding.name, Error e)
                    | Ok () ->
                        let polyType = convertTypeExprToPolyType ctx.skolemsInScope annotation

                        Some (binding.name, Ok polyType))

            |> (Seq.choose id >> Map.ofSeq)



        let hasTypeAnnotation name namesMap = Map.tryFind name namesMap |> Option.isSome

        /// But only if this isn't already in the map because it has an explicit type annotation
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


        let localNamesMap =
            orderedBindings
            |> List.fold
                (fun localNamesMap stronglyConnectedComponent ->
                    let combinedNamesMap : Ctx =
                        { ctx with
                            typedNamesMap = addLocalNamesMap localNamesMap ctx.typedNamesMap }

                    match stronglyConnectedComponent with
                    | DG.SingleNonRec (name, expr) ->
                        let inferredType = inferTypeFromExpr combinedNamesMap expr

                        let withThisBindingAdded : TypedLocalNamesMap =
                            addToLocalNamesMap name inferredType localNamesMap

                        withThisBindingAdded

                    | DG.SingleSelfRec (name, expr) ->
                        let newUniVar = makeNewUniVar ()

                        let withThisNameUniVarAdded : Ctx =
                            { ctx with
                                typedNamesMap =
                                    addToGlobalNamesMap
                                        (LocalLower name)
                                        (UnificationVariable.makeNew newUniVar
                                         |> PTC.UnificationVar
                                         |> Types.makeEmptyPolyType
                                         |> Ok)
                                        combinedNamesMap.typedNamesMap }

                        let inferredType =
                            inferTypeFromExpr withThisNameUniVarAdded expr
                            |> zonkPolyTypeResult (Set.singleton newUniVar)

                        let withThisBindingAdded : TypedLocalNamesMap =
                            addToLocalNamesMap name inferredType localNamesMap

                        withThisBindingAdded


                    | DG.MutualRecursive namesAndBindings ->
                        let namesAndBindingsAndUniVars =
                            namesAndBindings
                            |> Seq.map (fun (name, binding) -> name, binding, makeNewUniVar ())

                        let withNewUniVarsAdded : Ctx =
                            { ctx with
                                typedNamesMap =
                                    namesAndBindingsAndUniVars
                                    |> Seq.fold
                                        (fun map (name, _, uniVar) ->
                                            let typeToAdd =
                                                UnificationVariable.makeNew uniVar
                                                |> PTC.UnificationVar
                                                |> Types.makeEmptyPolyType
                                                |> Ok

                                            addToGlobalNamesMap (LocalLower name) typeToAdd map)
                                        combinedNamesMap.typedNamesMap }


                        let newLocalNamesMap : TypedLocalNamesMap =
                            namesAndBindingsAndUniVars
                            |> Seq.fold
                                (fun localNamesMap (name, expr, uniVar) ->
                                    let inferredType =
                                        inferTypeFromExpr withNewUniVarsAdded expr
                                        |> zonkPolyTypeResult (Set.singleton uniVar)

                                    let withThisBindingAdded : TypedLocalNamesMap =
                                        addToLocalNamesMap name inferredType localNamesMap

                                    withThisBindingAdded)
                                localNamesMap

                        newLocalNamesMap)
                namesWithTypeAnnotations


        localNamesMap












    and private resolveAllLetBindingsAndBody
        (ctx : Ctx)
        (letBindings : Ast.LetBindingSingle nel)
        (body : Ast.Expr)
        : Result<PolyType, UnificationError> =
        let bindingsResolutionResult = resolveNamesTopologically ctx letBindings

        let combinedNamesMap : Ctx =
            { ctx with
                typedNamesMap = addLocalNamesMap bindingsResolutionResult ctx.typedNamesMap }

        let bodyResult = inferTypeFromExpr combinedNamesMap body

        bodyResult










    and inferTypeFromExpr (ctx : Ctx) (expr : Ast.Expr) : Result<PolyType, UnificationError> =
        let namesMap = ctx.typedNamesMap

        match expr with
        | Ast.StrVal _ -> Types.makeEmptyPolyType Types.strType |> Ok
        | Ast.IntVal _ -> Types.makeEmptyPolyType Types.intType |> Ok
        | Ast.ListVal exprs ->
            match exprs with
            | [] -> Ok Types.listType
            | only :: [] ->
                let contentType = inferTypeFromExpr ctx only
                contentType |> Result.map Types.listTypeOf

            | head :: rest ->
                let inferred = NEL.map (inferTypeFromExpr ctx) (NEL.new_ head rest)
                let unified = unifyMultipleTypes inferred

                unified |> Result.map Types.listTypeOf


        | Ast.TupleVal (first, second) ->
            let inferredFirst = inferTypeFromExpr ctx first
            let inferredSecond = inferTypeFromExpr ctx second

            match inferredFirst, inferredSecond with
            | Ok inferredFirst', Ok inferredSecond' -> Types.tupleTypeOf inferredFirst' inferredSecond' |> Ok

            | Error e, _
            | _, Error e -> Error e


        | Ast.LambdaVal (param, body) ->
            /// Make a new unification variable to act as the input parameter for the lambda
            let newUniVar : UnificationVarId = makeNewUniVar ()

            let paramPolyType : PolyType =
                UnificationVariable.makeNew newUniVar
                |> PolyTypeContents.UnificationVar
                |> Types.makeEmptyPolyType

            /// Add the new name with its unification variable type into the names map that we inject into the body inferencing function
            let withNewUnificationVarAddedForParam =
                { ctx with
                    typedNamesMap = Map.add (LocalLower param) (Ok paramPolyType) ctx.typedNamesMap }

            let bodyInferenceResult =
                inferTypeFromExpr withNewUnificationVarAddedForParam body
                |> Result.map (Types.funcTypeOf paramPolyType)

            let instantiatedType =
                zonkPolyTypeResult (Set.singleton newUniVar) bodyInferenceResult

            instantiatedType


        | Ast.NamedVal name ->
            match Map.tryFind (LocalLower name) namesMap with
            | Some t -> t
            | None -> Error (UndefinedName (LocalLower name))


        | Ast.LetBindings (bindings, body) -> resolveAllLetBindingsAndBody ctx bindings body


        | Ast.FuncApplication (funcExpr, inputExpr) ->
            let inputType = inferTypeFromExpr ctx inputExpr

            let funcExprType = inferTypeFromExpr ctx funcExpr

            match inputType, funcExprType with
            | Ok inputType_, Ok funcExprType_ ->
                let returnTypeUniVarId = makeNewUniVar ()
                let returnTypeUniVar = UnificationVariable.makeNew returnTypeUniVarId

                let returnType : PolyType =
                    PTC.UnificationVar returnTypeUniVar |> Types.makeEmptyPolyType

                /// This is the type that the function expression should be compatible with: i.e. being able to receive the provided input, and returning the return unification variable – which may or may not get constrained to something concrete based on the function's actual expression
                let funcRequiredType = Types.funcTypeOf inputType_ returnType

                /// So I think this is fine to just discard because we only need to unify this to set the uniVars, not because we need this required func itself
                let funcRequiredResult = unifyTwoTypes funcRequiredType funcExprType_

                let zonked = zonkPolyType (Set.singleton returnTypeUniVarId) returnType

                Ok zonked

            | Error e, _
            | _, Error e -> Error e


        | Ast.IfElse (condition, thenExpr, elseExpr) ->
            let condRequirement = Types.boolType |> Types.makeEmptyPolyType |> Ok

            /// Yeah I think here too we don't need to do anything with the actual result of the condition, because if it's not a Bool then it's just wrong and there's nothing more to do with that
            let condType = unifyTwoTypeResults (inferTypeFromExpr ctx condition) condRequirement

            let thenType = inferTypeFromExpr ctx thenExpr
            let elseType = inferTypeFromExpr ctx elseExpr

            let combinedReturnType = unifyTwoTypeResults thenType elseType

            combinedReturnType


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

                Ok polyType

            | None -> Error (UndefinedTypeCtor (LocalUpper name))




















    (*

        Type unification

    *)



    and unifyTwoTypes (type1 : PolyType) (type2 : PolyType) : Result<PolyType, UnificationError> =
        let allTypeVars = type1.forall @ type2.forall

        let typeVarsToUniVar : Map<TypeVariableId, UnificationVariable> =
            allTypeVars
            |> List.map (fun typeVar ->
                let uniVar = UnificationVariable.makeNew (makeNewUniVar ())

                typeVar, uniVar)
            |> Map.ofList


        let rec swapOutTypeVars (ptc : PolyTypeContents) =
            match ptc with
            | UnificationVar id -> UnificationVar id
            | ConcreteType (ConcType (name, typeParams)) ->
                ConcreteType <| ConcType (name, List.map swapOutTypeVars typeParams)
            | PTC.Skolem name -> PTC.Skolem name

            | TypeVariable tv ->
                match Map.tryFind tv typeVarsToUniVar with
                | Some uniVar -> UnificationVar uniVar
                | None ->
                    failwith
                        "Each type variable should have a unification variable assigned to replace it, so this should not be possible"



        let replacedType1 : PolyTypeContents = swapOutTypeVars type1.typeExpr

        let replacedType2 : PolyTypeContents = swapOutTypeVars type2.typeExpr


        let unified = unifyTwoTypeContents replacedType1 replacedType2

        let allUniVars =
            Map.values typeVarsToUniVar |> Seq.map UnificationVariable.getId |> Set.ofSeq

        let zonked = unified |> zonkPolyTypeContentsResult allUniVars

        zonked







    and private unifyTwoTypeResults
        (typeResult1 : Result<PolyType, UnificationError>)
        (typeResult2 : Result<PolyType, UnificationError>)
        : Result<PolyType, UnificationError> =
        match typeResult1, typeResult2 with
        | Ok type1, Ok type2 -> unifyTwoTypes type1 type2
        | Error e, _
        | _, Error e -> Error e


    and private unifyMultipleTypes
        (typeResults : Result<PolyType, UnificationError> nel)
        : Result<PolyType, UnificationError> =
        let (NEL (head, rest)) = typeResults
        List.fold unifyTwoTypeResults head rest



    and private unifyTwoTypeContents
        (type1 : PolyTypeContents)
        (type2 : PolyTypeContents)
        : Result<PolyTypeContents, UnificationError> =
        match type1, type2 with
        | PTC.TypeVariable _, _
        | _, PTC.TypeVariable _ -> failwith "All type variables should have been swapped out for unification variables!"

        | PTC.ConcreteType (ConcType (name1, typeParams1) as concType1),
          PTC.ConcreteType (ConcType (name2, typeParams2) as concType2) ->

            if name1 = name2 then
                match List.zipList typeParams1 typeParams2 with
                | Ok combinedTypeParams ->
                    let paramsResults =
                        combinedTypeParams
                        |> List.map (fun (param1, param2) -> unifyTwoTypeContents param1 param2)


                    match Result.sequenceList paramsResults with
                    | Ok unifiedParams -> ConcType (name1, unifiedParams) |> PTC.ConcreteType |> Ok
                    | Error errs -> NEL.head errs |> Error

                | Error _ -> UnificationError.makeClash concType1 concType2 |> Error

            else
                UnificationError.makeClash concType1 concType2 |> Error


        | PTC.UnificationVar uniVar1, PTC.UnificationVar uniVar2 ->
            if uniVar1.content.Value.id = uniVar2.content.Value.id then
                Ok (PTC.UnificationVar uniVar1)

            else
                unifyUniVars uniVar1 uniVar2 |> Result.map PTC.UnificationVar



        | PTC.UnificationVar uniVar, PTC.ConcreteType (ConcType (name, typeVars))
        | PTC.ConcreteType (ConcType (name, typeVars)), PTC.UnificationVar uniVar ->

            constrainUniVarInCtx uniVar (PTC.ConcreteType (ConcType (name, typeVars)))
            |> Result.map PTC.UnificationVar


        | PTC.Skolem name1, PTC.Skolem name2 ->
            if name1 = name2 then
                Ok (PTC.Skolem name1)

            else
                TriedToUnifyDifferentSkolems (name1, name2) |> Error


        | PTC.Skolem name, t
        | t, PTC.Skolem name -> NarrowedSkolem (name, t) |> Error








    and private unifyTwoTypeContentsResults
        (typeContentResult1 : Result<PolyTypeContents, UnificationError>)
        (typeContentResult2 : Result<PolyTypeContents, UnificationError>)
        : Result<PolyTypeContents, UnificationError> =
        match typeContentResult1, typeContentResult2 with
        | Ok typeContent1, Ok typeContent2 -> unifyTwoTypeContents typeContent1 typeContent2

        | Error e, _
        | _, Error e -> Error e









    /// Other than the trivial case of unifying a univar with itself, a univar can't be unified with another type containing itself. Otherwise you'd have an infinitely recursive type. So we need to check that that's not what we're doing here.
    ///
    /// Returns true if the univar is indeed somewhere nested inside the PTC resulting in infinite recursive type if we were to try and unify them
    and private occursCheck (univar : UnificationVariable) (ptc : PTC) : bool =
        /// Is the predicate true for any item in the list
        let forAny pred = List.fold (fun state item -> state || pred item) false

        let rec nestedOccursCheck ptc_ =
            match ptc_ with
            | UnificationVar innerUniVar -> innerUniVar.content.Value = univar.content.Value

            | TypeVariable _ -> false
            | PTC.Skolem _ -> false
            | ConcreteType (ConcType (_, innerPtcs)) -> forAny nestedOccursCheck innerPtcs

        match ptc with
        | UnificationVar _ ->
            // I.e. top levels univars being equal to each other is not a problem. It's only nested ones that are a problem.
            false

        | _ -> nestedOccursCheck ptc






    /// Point two univars to the same thing
    and private unifyUniVars
        (univar1 : UnificationVariable)
        (univar2 : UnificationVariable)
        : Result<UnificationVariable, UnificationError> =
        match univar1.content.Value.constrained, univar2.content.Value.constrained with
        | None, None ->

            let combined : UniVarContent =
                { id = univar1.content.Value.id
                  constrained = None }

            univar1.content.Value <- combined
            univar2.content.Value <- combined

            Ok univar1

        | Some ptc, None
        | None, Some ptc ->

            let combined : UniVarContent =
                { id = univar1.content.Value.id
                  constrained = Some ptc }

            univar1.content.Value <- combined
            univar2.content.Value <- combined

            Ok univar1

        | Some result1, Some result2 ->
            if occursCheck univar1 result2 then
                InfinitelyRecursiveType (univar1, result2) |> Error

            elif occursCheck univar2 result1 then
                InfinitelyRecursiveType (univar2, result1) |> Error

            else
                let unifiedResult = unifyTwoTypeContents result1 result2

                match unifiedResult with
                | Ok unified ->

                    let combined : UniVarContent =
                        { id = univar1.content.Value.id
                          constrained = Some unified }

                    univar1.content.Value <- combined
                    univar2.content.Value <- combined

                    Ok univar1

                | Error e -> Error e




    /// Add a constraint to a univar
    and private constrainUniVarInCtx
        (uniVar : UnificationVariable)
        (constraint_ : PolyTypeContents)
        : Result<UnificationVariable, UnificationError> =
        let content = uniVar.content.Value

        match content.constrained with
        | None ->
            uniVar.content.Value <-
                { uniVar.content.Value with
                    constrained = Some constraint_ }

            Ok uniVar

        | Some existingConstraint ->
            if occursCheck uniVar constraint_ then
                InfinitelyRecursiveType (uniVar, constraint_) |> Error

            else

                match unifyTwoTypeContents existingConstraint constraint_ with
                | Ok unified ->
                    uniVar.content.Value <-
                        { uniVar.content.Value with
                            constrained = Some unified }

                    Ok uniVar

                | Error e -> Error e







    and private unifyTwoTypeContentsResultsOpts
        (typeOpt1 : Result<PolyTypeContents, UnificationError> option)
        (typeOpt2 : Result<PolyTypeContents, UnificationError> option)
        : Result<PolyTypeContents, UnificationError> option =
        match typeOpt1, typeOpt2 with
        | Some type1, Some type2 -> unifyTwoTypeContentsResults type1 type2 |> Some

        | Some type_, None
        | None, Some type_ -> Some type_

        | None, None -> None

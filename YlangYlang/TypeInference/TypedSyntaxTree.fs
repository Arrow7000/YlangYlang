module TypedSyntaxTree



open QualifiedSyntaxTree.Names

module S = SyntaxTree
module C = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree





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










type DestructuredPattern =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of RecordFieldName nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of AssignmentPattern tom
    | DestructuredCons of AssignmentPattern tom
    | DestructuredTypeVariant of constructor : UpperNameValue * params' : AssignmentPattern list

/// Named – or ignored – variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of ident : LowerIdent
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of pattern : AssignmentPattern * alias : LowerIdent




















/// Represents a generic, undeclared type variable. Used to create type constraints; e.g. between the input type and the output type of `let id x = x`.
type TypeConstraintId =
    | TypeConstraintId of System.Guid

    override this.ToString () =
        let (TypeConstraintId guid) = this

        (string guid |> String.trim 6) + "..."


let makeTypeConstrId () = System.Guid.NewGuid () |> TypeConstraintId


let private recFieldToStr (RecordFieldName str) = str

let private upperNameValToStr (str : UpperNameValue) =
    // @TODO: stringify the actual underlying names properly
    string str





type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Bool
    | Unit

    override this.ToString () =
        match this with
        | Float -> "Float"
        | Int -> "Int"
        | String -> "String"
        | Char -> "Char"
        | Bool -> "Bool"
        | Unit -> "()"





/// @TODO need to include record types also, both closed or open
and ConcreteType =
    | BuiltInPrims of BuiltInPrimitiveTypes
    | Tuple of PolyTypeContents tom
    | List of PolyTypeContents
    | Arrow of fromType : PolyTypeContents * toType : PolyTypeContents
    | CustomType of typeName : UpperNameValue * typeParams : PolyTypeContents list


    override this.ToString () =
        match this with
        | BuiltInPrims prim -> string prim
        | Tuple ptcs ->
            let commafied = ptcs |> TOM.map string |> String.join ", "
            "(" + commafied + ")"

        | List ptc -> "List " + string ptc
        | Arrow (fromType, toType) -> string fromType + " -> " + string toType
        | CustomType (typeName, typeParams) ->
            upperNameValToStr typeName
            + " "
            + (List.map string typeParams |> String.join " ")


and PolyTypeContents =
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

and PTC = PolyTypeContents




and UniVarContent =
    { id : UnificationVarId
      constrained : PolyTypeContents option }


and UnificationVariable =
    { content : UniVarContent ref }

    static member getId (uniVar : UnificationVariable) = uniVar.content.Value.id

    /// Make a new unconstrained unification variable
    static member makeNewBlank (uniVarId : UnificationVarId) = { content = ref { id = uniVarId; constrained = None } }

    /// Make a new constrained unification variable
    static member makeNewConstr (uniVarId : UnificationVarId) (constr : PolyTypeContents) =
        { content =
            ref
                { id = uniVarId
                  constrained = Some constr } }

    override this.ToString () =
        let id = UnificationVariable.getId this

        match this.content.Value.constrained with
        | Some constrained -> $"({string id} : {string constrained})"
        | None -> string id



/// Alias for ConcreteType
type Conc = ConcreteType







type UnificationError =
    | UnificationClash of ConcreteType * ConcreteType
    | UndefinedName of LowerNameValue
    | UndefinedTypeCtor of UpperNameValue
    /// Skolems only unify with themselves, so different skolems can't be unified with each other
    | TriedToUnifyDifferentSkolems of skolem1 : LowerIdent * skolem2 : LowerIdent
    /// Skolems only unify with themselves, not with anything else
    | NarrowedSkolem of skolemName : LowerIdent * narrowedWith : PolyTypeContents
    | InfinitelyRecursiveType of unified : UnificationVariable * with_ : PolyTypeContents
    | WrongNumberOfTypeParams of typeName : UpperNameValue * expected : uint * actual : uint

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
        | WrongNumberOfTypeParams (typeName, expected, actual) ->
            "Wrong number of type params for type "
            + string typeName
            + ", expected "
            + string expected
            + " but got "
            + string actual


    static member makeClash conc1 conc2 =
        // // Uncomment when debugging unexpected type errors
        //failwith ("Unification clash: `" + string conc1 + "` and `" + string conc2 + "`")

        UnificationClash (conc1, conc2)






/// Alias for PolyTypeContents
//type PTC = PolyTypeContents




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


/// The map of type names to the polytypes that they represent; e.g. `Maybe` -> `forall a. Maybe a`
type TypeNamesMap = Map<UpperNameValue, PolyType>

/// This maps from constructor names to the parameters that the variant needs to the signature of the constructor; e.g. `String -> Int -> Maybe (String, Int)`.
/// But it could also be e.g. `None`, which would have as its value the single type expression `Maybe a`.
/// So after instantiating the type, we'll need to zonk it so we can generalise the unconstrained params.
///
///The list represents the parameters for this particular constructor

type Ctor =
    { forall : TypeVariableId list
      params_ : PolyTypeContents list
      result : PolyTypeContents }

type CtorNamesMap = Map<Lexer.TypeOrModuleIdentifier, Ctor>






type Ctx =
    { typedNamesMap : TypedNamesMap
      skolemsInScope : LowerIdent set
      typeNamesMap : TypeNamesMap
      ctorNamesMap : CtorNamesMap }

    static member empty : Ctx =
        { typeNamesMap = Map.empty
          skolemsInScope = Set.empty
          typedNamesMap = Map.empty
          ctorNamesMap = Map.empty }




/// A local context, we return these from functions that type check let bindings and top level declarations
type TypedLocalNamesMap = Map<LowerIdent, Result<PolyType, UnificationError>>


/// A names map that we infer from an assignment expression. Because assignment expressions do not stand alone but they are referenced in an expression body, they can never be PolyTypes, only PolyTypeContents with uniVars.
type AssignmentNamesMap = Map<LowerIdent, Result<PolyTypeContents, UnificationError>>








































































































































/// Represents a correct type without clashes
type DefinitiveType =
    | DtPrimitiveType of BuiltInPrimitiveTypes
    | DtTuple of TypeConstraints tom
    | DtList of TypeConstraints
    /// I think we need to pass in a type param to the extended record, so that not including one is a type error
    | DtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraints>
    | DtRecordExact of Map<RecordFieldName, TypeConstraints>
    /// This guy will only be able to be assigned at the root of a file once we have the types on hand to resolve them and assign
    | DtNewType of typeName : UpperNameValue * typeParams : TypeConstraints list
    | DtArrow of fromType : TypeConstraints * toType : TypeConstraints


    override this.ToString () =
        match this with
        | DtPrimitiveType prim ->
            match prim with
            | Unit -> "()"
            | Float -> "Float"
            | Int -> "Int"
            | String -> "String"
            | Char -> "Char"
            | Bool -> "Bool"
        | DtTuple tcs ->
            let commafied = tcs |> TOM.map string |> String.join ", "

            "(" + commafied + ")"
        | DtList tc -> "List " + string tc
        | DtRecordWith fields ->
            // @TODO: should add something in here for the thing that's being expanded
            let commafiedFields =
                fields
                |> Map.toList
                |> List.map (fun (key, value) -> recFieldToStr key + " : " + string value)
                |> String.join ", "

            "{ " + commafiedFields + " }"

        | DtRecordExact fields ->
            let commafiedFields =
                fields
                |> Map.toList
                |> List.map (fun (key, value) -> recFieldToStr key + " : " + string value)
                |> String.join ", "

            "{ " + commafiedFields + " }"

        | DtNewType (typeName, typeVars) ->
            upperNameValToStr typeName + " " + (List.map string typeVars |> String.join " ")

        | DtArrow (fromType, toType) -> string fromType + " -> " + string toType




/// A constraint based on a reference to a name
///
/// @TODO: maybe we should split out the constraints that can be used in type expressions? That way we never risk including a ByValue constraint in a type expression. But... if we do that then we'd need to have yet another kind of TypeConstraints
and RefConstr =
    /// I.e. must be the same type as this value
    | ByValue of LowerNameValue

    /// This represents a bound variable to outside the scope where it is declared – works both for value and type expressions.
    /// I.e. these can represent invariants between params that a function or type constructor takes.
    | IsBoundVar of TypeConstraintId

    //| HasTypeOfFirstParamOf of TypeConstraintId


    //| ByConstructorType of ctor : UpperNameValue


    // From here onwards are the constraints that are derived from a type expressions. The ones above are derived from value expressions.

    ///// I.e. must be the same type as this type param
    //| ByTypeParam of LowerIdent

    override this.ToString () =
        match this with
        | ByValue name -> string name
        | IsBoundVar (TypeConstraintId guid) -> string guid |> String.trim 6
//| ByConstructorType ctor -> upperNameValToStr ctor
//| ByTypeParam (LowerIdent str) -> str

//| IsOfTypeByName of typeName : UpperNameValue * typeParams : TypeConstraints list


///// A more limited reference constraint, only for value expressions
//and ValRefConstr =
//    | RefByVal of LowerNameValue
//    | BoundRef of TypeConstraintId


/// Contains the definitive constraints that have been inferred so far, plus any other value or type param constraints that have not been evaluated yet.
/// If a `RefConstr` turns out to be incompatible with the existing definitive type, this will be transformed into a `TypeJudgment` with the incompatible definitive types listed in the `Error` case.
and TypeConstraints =
    | TypeConstraints of definitive : DefinitiveType option * otherConstraints : RefConstr set

    override this.ToString () =
        let (TypeConstraints (defOpt, others)) = this

        let refConstrsStr = others |> Set.toSeq |> Seq.map string |> String.join ", "

        match defOpt with
        | None -> refConstrsStr
        | Some def -> refConstrsStr + " : " + string def


    /// Makes a new TypeConstraints which is truly empty
    static member empty = TypeConstraints (None, Set.empty)

    /// Makes a new TypeConstraints which is empty of specific, but still has a Guid so as not to lose links required between the thing that is assigned this constraint and anything else it is linked to
    static member makeUnspecific () = TypeConstraints (None, Set.singleton (IsBoundVar (makeTypeConstrId ())))

    static member fromDefinitive (def : DefinitiveType) : TypeConstraints = TypeConstraints (Some def, Set.empty)

    static member fromConstraint (constr : RefConstr) : TypeConstraints = TypeConstraints (None, Set.singleton constr)

    static member addRefConstraints (constrs : RefConstr set) (TypeConstraints (defOpt, refConstrs)) =
        TypeConstraints (defOpt, Set.union constrs refConstrs)



    (* Some shorter aliases *)

    static member fromDef = TypeConstraints.fromDefinitive
    static member fromRef = TypeConstraints.fromConstraint
    static member any () = TypeConstraints.makeUnspecific ()








/// I think there is space for yet another version of a concrete type, which is either a concrete type or a generic. And it can hold itself recursively. The benefit being that we don't need to have either a full TC with all the reference constraints, nor a special RefDtType that can't live outside of an Accumulator, but one that can stand on its own, and is exactly as concrete as it can be, with no extraneous information included.
type ConcreteOrGeneric =
    | ConcUnitType
    | ConcPrimType of BuiltInPrimitiveTypes
    | ConcTuple of ConcreteOrGeneric tom
    | ConcList of ConcreteOrGeneric
    /// I think we need to pass in a type param to the extended record, so that not including one is a type error
    | ConcRecordWith of referencedFields : Map<RecordFieldName, ConcreteOrGeneric>
    | ConcRecordExact of Map<RecordFieldName, ConcreteOrGeneric>
    /// This guy will only be able to be assigned at the root of a file once we have the types on hand to resolve them and assign
    | ConcNewType of typeName : UpperNameValue * typeParams : ConcreteOrGeneric list
    | ConcArrow of fromType : ConcreteOrGeneric * toType : ConcreteOrGeneric

    /// The special generic type, i.e. not a concrete type
    /// @TODO: not sure if we want an option for the constraint ID here yet
    | Generic of TypeConstraintId option







type Param =
    { //tokens : TokenWithSource list
      destructurePath : PathToDestructuredName }


and TypeError =
    | IncompatibleTypes of DefinitiveType list
    | UnprunedRecursion

    static member fromTypes types = IncompatibleTypes types





















/// Only to be used as keys and references in Accumulator and RefDefTypes
type AccumulatorTypeId =
    | AccumulatorTypeId of System.Guid

    override this.ToString () =
        let (AccumulatorTypeId guid) = this
        String.trim 6 (string guid) + "..."
















type VariantCase =
    {
        /// @TODO: make this support qualified names too
        label : UpperIdent
        /// Could be empty. Any of these constraint IDs should be declared in the type declaration as type params or else this is not valid.
        ///
        /// @TODO: actually this may not only contain type variables but also proper types, so they will be described by MentionableTypes
        contents : MentionableType list
    }


and UnionType =
    | UnionType of
        typeName : UpperNameValue *
        /// These are the constraints this type declares, to be referenced inside the variant branches
        typeParams : TypeConstraintId list *
        variants : VariantCase nel






/// Maybe we should rename this to TypeExpression or something?
and MentionableType =
    /// Either declared or implicit
    | GenericTypeVar of TypeConstraintId

    // And the concrete type shapes
    | UnitType
    /// Possibly don't need this because it's kind of a special kind of referenced type, but good to have this for now
    | Primitive of BuiltInPrimitiveTypes
    | Tuple of MentionableType tom
    | Record of Map<RecordFieldName, MentionableType>
    | ExtendedRecord of Map<RecordFieldName, MentionableType>
    /// This includes a map of which type constraint IDs (declared in the UnionType and referenced inside its variants) are set to which MentionableTypes – whether concrete or a generic type constraint ID declared in a parent scope
    | ReferencedType of referencedType : UnionType * typeParamsSet : Map<TypeConstraintId, MentionableType>
    | Arrow of fromType : MentionableType * toType : MentionableType












///// Basically the same as a T.DefinitiveType but with guids referencing other types in the Acc instead of their own TypeConstraints
//type RefDefType =
//    | RefDtUnitType
//    | RefDtPrimType of BuiltInPrimitiveTypes
//    | RefDtList of AccumulatorTypeId
//    | RefDtTuple of AccumulatorTypeId tom
//    | RefDtRecordWith of referencedFields : Map<RecordFieldName, AccumulatorTypeId>
//    | RefDtRecordExact of Map<RecordFieldName, AccumulatorTypeId>
//    //| RefDtNewType of typeName : UpperNameValue * typeParams : AccumulatorTypeId list

//    /// Represents a specific instance of a union type, with a mapping from the type's type parameters to specific type constraints.
//    /// These type constraints can start out as completely blank and unconstrained, but can be filled in over time as we learn of more constraints and definitive shapes they must have.
//    /// This way the original type remains the same, unbesmirched, and its specific instantiations that come under restrictions.
//    ///
//    /// @TODO: maybe don't store the whole thing  but only a reference to it with a mapping of type params set
//    | RefDtNewType of type_ : UnionType * typeParamsToSpecifics : Map<TypeConstraintId, AccumulatorTypeId>
//    | RefDtArrow of fromType : AccumulatorTypeId * toType : AccumulatorTypeId


//    override this.ToString () =
//        match this with
//        | RefDtUnitType -> "()"
//        | RefDtPrimType prim ->
//            match prim with
//            | Float -> "Float"
//            | Int -> "Int"
//            | String -> "String"
//            | Char -> "Char"
//            | Bool -> "Bool"
//        | RefDtTuple tcs ->
//            let commafied = tcs |> TOM.map string |> String.join ", "

//            "(" + commafied + ")"

//        | RefDtList tc -> "List " + string tc
//        | RefDtRecordWith fields ->
//            // @TODO: should add something in here for the thing that's being expanded
//            let commafiedFields =
//                fields
//                |> Map.toList
//                |> List.map (fun (key, value) -> recFieldToStr key + " : " + string value)
//                |> String.join ", "

//            "{ " + commafiedFields + " }"

//        | RefDtRecordExact fields ->
//            let commafiedFields =
//                fields
//                |> Map.toList
//                |> List.map (fun (key, value) -> recFieldToStr key + " : " + string value)
//                |> String.join ", "

//            "{ " + commafiedFields + " }"

//        | RefDtNewType (unionType, specifiedTypeParams) ->
//            let (UnionType (typeName, allowedTypeParams, _)) = unionType

//            let typeParams =
//                allowedTypeParams
//                |> List.map (fun typeParam -> Map.tryFind typeParam specifiedTypeParams)

//            upperNameValToStr typeName
//            + " "
//            + (typeParams
//               |> List.map (function
//                   | None -> "_"
//                   | Some typeId -> string typeId)
//               |> String.join " ")

//        | RefDtArrow (fromType, toType) -> string fromType + " -> " + string toType


//type AccTypeError =
//    | DefTypeClash of RefDefType * RefDefType
//    | UnresolvedCtorError of ctorName : UpperNameValue
//    | UnresolvedTypeName of typeName : UpperNameValue
//    /// When a pattern match destructuring doesn't have the correct number of params. The in tells us if there are not enough (in which case it'll be negative) or too many (will be positive)
//    | WrongPatternParamLength of int
//    | DoesntMatchExpectedTypeShape of requiredShape : MentionableType * RefDefType






///// @TODO: this should really also contain the other `ConstrainType`s, in case some of them also get evaluated to incompatible definitive types
//type TypeJudgment = Result<TypeConstraints, AccTypeError>








(* Name dictionaries *)


(*

# Notation

## Type notations

T1,T2,...,Tn => concrete types
T1 a,T2 a,...,Tn a => types with type params
T1 a b T3 => concrete type T1 with 3 type params, the first two being different generics and the third set to concrete type T3
T1 (T2 T3) => concrete type T1 with one type param, currently set to concrete type T2 which in turn has one type param set to concrete type T3


## Value type annotation notation

x : T1 => value x has concrete type T1
x : T1 T2 => value x has concrete type T1 which takes one type parameter, which in this case is set to concrete type T2.
x : a => value x has generic type `a`
f : a -> b => value f has type a -> b, meaning it is a function that given a value of generic type a it returns a value of generic type b
f : a -> a => value f has type a -> a, meaning it is a function that given a value it returns a value of that same type, for any type `a`

f : T1 a -> T1 b => value f is a function from T1 to T1, where T1 takes one type param, and can return a T1 with a different type param
f : T1 a -> T2 a => value f is a function from T1 to T2, where both T1 and T2 take one type param, and returns a T2 with the same type param as was in the T1


## Value expression notation

f x => applying function f to parameter x
f x : T1 => applying function f to parameter x results in a value of type T1


## Inference rule notation

     x
----------- => given fact(s) x we can infer fact(s) y; or phrased differently: if x is true y must also be true
     y

 a, b, c; x, y, z
------------------ => given type facts a, b, and c, and expression facts x, y, and z, we can infer facts n, m, and o. The type facts and expression facts are separated by a semicolon
     n, m, o



# The inference rules


      f x
-----------------
   f : a -> b
=> given the expression `f x` we can infer that f must be a function. We can't infer anything about x because f's type param `a` doesn't impose any constraints on the value it accepts, nor does f say anything about what its return value type is


 f : T1 -> b, f x
----------------------
     x : T1
=> given f only accepts a T1 as input, and we call f with param x, x must be a T1. Nothing else would be valid.


 f : a -> T1
-------------
  f x : T1
=> given f is a function that when given any value returns a T1, the expression f x returns a T1, but it tells us nothing about the type of value x


 f : a -> a, x : T1
--------------------
      f x : T1
=> if a type has the same type param in multiple places, when one of those instances is narrowed to a concrete type, all other instances are substituted with that concrete type, to ensure the invariant holds


 f : a -> b -> a, x : T1
-------------------------
    f x : b -> T1
=> same as the rule above


 x : T1 a, y : T1 T2, f : a -> a -> a; f x y
---------------------------------------------
               f x y : T1 T2
=> this can kinda be derived from the rule above


 f : a -> a -> a, x : (T1, b), y : (c, T2)
-------------------------------------------
              f x y : (T1, T2)
=> type narrowing! This is where unification comes in


 f : Maybe T1 -> a, x : a; f x
----------------------------
         x : Maybe b
NOTE: but the above really only makes sense because we know that you can have values of type Maybe that leave the type param unaffected. This would not be true for example with type Dummy where `type Dummy a = Dummy a`, because in that case if we inferred that x : Dummy _, the only way in which a Dummy would be assignable to `Dummy String` is if it were Dummy String, because there are no values possible for Dummy that are leave the type param unspecified; unlike for example with `None : Maybe a` or `[] : List a`.
But maybe... we leave that for now, and for now we behave as if every type can have values that leave its inner type param unspecified, even if that's not strictly true, e.g. for the aforementioned Dummy type but even for types like `Tuple a b`, for obvious reasons.


 f : (String -> b) -> c, x :








*)






















///// Name of a referenced value
//type RefValueName = | RefValueName of LowerNameValue

///// Allows for directly referencing values in a Ctx
//type TypeRefId = | TypeRefId of System.Guid
/////
//type UnificationVar = | UnificationVar of System.Guid
//type TypeVar = | TypeVar of System.Guid
////type Skolem = | Skolem of System.Guid





//type ConcreteType =
//    | ConcUnitType
//    | ConcPrimType of BuiltInPrimitiveTypes
//    | ConcTuple of TypeForInference tom
//    | ConcList of TypeForInference
//    /// I think we need to pass in a type param to the extended record, so that not including one is a type error
//    | ConcRecordWith of referencedFields : Map<RecordFieldName, TypeForInference>
//    | ConcRecordExact of Map<RecordFieldName, TypeForInference>
//    /// This guy will only be able to be assigned at the root of a file once we have the types on hand to resolve them and assign.
//    /// We initialise this by just making all the type params TypeVars (unification vars)
//    | ConcNewType of typeName : UpperNameValue * typeParams : TypeForInference list

//    | ConcArrow of fromType : TypeForInference * toType : TypeForInference


//and TypeForInference =
//    | Concrete of ConcreteType
//    ///// Same as whatever this name is (although not _exactly_ the same, because the named value could have a type scheme, so the type scheme will then adapt to whatever the context is
//    | Named of RefValueName

//    /// This is basically the `a` in a `forall a. a -> a`. So it needs to be substituted with something else at each instantiation, so that when that thing gets replaced it doesn't replace every instance of the type, but only that specific fresh instance of it.
//    | UnificationVar of UnificationVar

//    /// This is that fresh instantiation of a unification variable, so that if one of these gets replaced with a concrete type, _all_ of the same ID instances get replaced with the same type
//    | TypeVarId of TypeVar


////and WithUnresolveds =
////    /// I think we just throw an error if we try to unify anything with an unresolved name inside of it
////    | Named of RefValueName
////    | UnresolvedTree of TypeForInference


//type TypeErr = | TypeClash of ConcreteType * ConcreteType


//type TypeInferenceResult = Result<TypeForInference, TypeErr>


//type NameOrReference =
//    | Name of RefValueName
//    | Reference of TypeRefId

//type TypeContext = Map<NameOrReference, TypeInferenceResult nel>










///// Commonly used type throughout Accumulator stuff
//type RefDefResOpt = Result<RefDefType, AccTypeError> option

///// FYI this on its own isn't enough to implement type schemes, we also need to distinguish between "these two things are mamish the same and ergo need to be fully unified" and "this thing should constrain this other thing but not the other way around"
//type RefConstraintEntry =
//    /// For concrete types or types constrained by other values
//    | Constrained of RefDefResOpt * RefConstr set
//    /// For types unconstrained by values and not adhering to a concrete shape.
//    ///
//    /// I think we store one of these for every generic that does not have any inherent type constraint on itself. We instantiate one of these for any non-inherently-constrained type or type param, like e.g. the `a` in `None : Maybe a`. Then, depending on the expression it is used in, we either do need to mamish unify the two expressions, or we just impose the constraint from one thing to the other. But either way a generic should never be removed from the Accumulator I don't think, because the `a` in `Maybe.None : Maybe a` is a long lived generic, and it never narrows to anything else, no matter how `None` is used.
//    ///
//    /// It's only for example if we add it into a `[ Just 123, None ]` that the `Maybe a`ness imposes a narrowing on what _uses_ it, so that it can't be used in a `[ 123, None ]` for example, because you can't unify a `Maybe a` with a naked `Int`.
//    ///
//    /// So we still need to do unification, but we're not unifying the constituent elements, only the type of the compound thing gets narrowed to the unification of `None : Maybe a` and `Just 123 : Maybe Int`. But the constraint only propagates one way, from the thing to the larger context that uses the structure, the structure itself doesn't (can't) impose a constraint onto the thing it uses. *Unless*! – and this is an important caveat – when the thing it's used in does have type *requirements*; e.g. we're doing `f a`; that does require `f` to be a `a -> b`, i.e. a concrete function. We can't know anything about the input and output types, and shouldn't make assumptions on what it takes and returns based on what we feed it, because it could be that we just happen to feed it a string but that `f` could equally well accept an `Int`, just because we passed it one thing doesn't mean that's the only thing it accepts.
//    ///
//    /// What other examples of such requirements are there? Well, e.g. things being pattern matched on and things used as conditionals in if expressions. And of course when passed as parameters to functions that do have strict requirements on the type they accept, whether implicitly through destructurings or through type annotations (not implemented yet)
//    | Generic of TypeConstraintId


///// Attempt at making accumulator working by using two internal maps, one where every single def type gets a guid assigned to it, and every ref constraint gets placed in a set with its others, which points to a guid, which in turn may have a def type assigned to it.
//type Accumulator =
//    {
//        refConstraintsMap : Map<AccumulatorTypeId, RefConstraintEntry>

//        /// This stores old ID references so that we don't ever run the risk of an ID ever getting out of date or replaced. This way a reference ID, once made, is reliable.
//        redirectMap : Map<AccumulatorTypeId, AccumulatorTypeId>
//    }

//    static member empty =
//        { refConstraintsMap = Map.empty
//          redirectMap = Map.empty }


//    /// If the input AccId is a redirect, gets the actual live AccId that it points to (even after multiple redirects). Useful for editing the data in the refConstraintsMap
//    static member getRealIdAndType
//        (accId : AccumulatorTypeId)
//        (acc : Accumulator)
//        : AccumulatorTypeId * RefConstraintEntry =
//        match Map.tryFind accId acc.refConstraintsMap with
//        | Some result -> accId, result
//        | None ->
//            match Map.tryFind accId acc.redirectMap with
//            | Some redirectId -> Accumulator.getRealIdAndType redirectId acc
//            | None ->
//                failwith $"It shouldn't be possible to not find an AccId in either the real or redirect maps: {accId}"

//    static member getTypeById (accId : AccumulatorTypeId) (acc : Accumulator) =
//        Accumulator.getRealIdAndType accId acc |> snd

//    static member getRealId (accId : AccumulatorTypeId) (acc : Accumulator) =
//        Accumulator.getRealIdAndType accId acc |> fst


//    /// Use with caution! This literally just replaces entries and sticks the replaced keys in the redirect map. It does *not* unify the new entry with the rest of the reference constraints map!
//    static member replaceEntries
//        (accIdsToReplace : AccumulatorTypeId seq)
//        (newAccId : AccumulatorTypeId)
//        (refDefResOpt : Result<RefDefType, AccTypeError> option)
//        (refConstrs : RefConstr set)
//        (acc : Accumulator)
//        =
//        { refConstraintsMap =
//            Map.removeKeys accIdsToReplace acc.refConstraintsMap
//            |> Map.add newAccId (Constrained (refDefResOpt, refConstrs))

//          redirectMap =
//            acc.redirectMap
//            |> Map.addBulk (accIdsToReplace |> Seq.map (fun accId -> accId, newAccId)) }





//    ///// Warning! It is on the caller to ensure that the refConstrs being added here don't have any overlap with any entries already present in the map, and to unify the entries accordingly if they do.
//    ///// This will replace the entry at the _real_ AccId, so the caller doesn't have to worry about fetching the real AccId first. This function also returns the real AccId for good measure.
//    //static member replaceEntry
//    //    (accId : AccumulatorTypeId)
//    //    (replacer : AccumulatorTypeId
//    //                    -> Result<RefDefType, AccTypeError> option
//    //                    -> RefConstr set
//    //                    -> Result<RefDefType, AccTypeError> option * RefConstr set)
//    //    (acc : Accumulator)
//    //    : AccumulatorTypeId * Accumulator =
//    //    let realAccId, (Constrained (refDefResOpt, refConstrs)) =
//    //        Accumulator.getRealIdAndType accId acc

//    //    let replaced = replacer realAccId refDefResOpt refConstrs

//    //    realAccId,
//    //    { acc with
//    //        refConstraintsMap =
//    //            acc.refConstraintsMap
//    //            |> Map.add realAccId replaced }




//    //static member replaceRefConstrs
//    //    (accId : AccumulatorTypeId)
//    //    (newRefConstrs : RefConstr set)
//    //    (acc : Accumulator)
//    //    : AccumulatorTypeId * Accumulator =
//    //    let realAccId, entry = Accumulator.getRealIdAndType accId acc

//    //    let replaced =
//    //        match entry with
//    //        | Constrained (refDefResOpt, _) -> refDefResOpt, newRefConstrs
//    //        | Generic -> None, newRefConstrs

//    //    realAccId,
//    //    { acc with
//    //        refConstraintsMap =
//    //            acc.refConstraintsMap
//    //            |> Map.add realAccId (Constrained replaced) }


//    static member replaceEntryWithRefDefAndConstrs
//        (accId : AccumulatorTypeId)
//        (replacer : RefConstraintEntry -> RefDefResOpt * RefConstr set)
//        (acc : Accumulator)
//        : AccumulatorTypeId * Accumulator =
//        let realAccId, entry = Accumulator.getRealIdAndType accId acc

//        let replaced = replacer entry

//        realAccId,
//        { acc with
//            refConstraintsMap = acc.refConstraintsMap |> Map.add realAccId (Constrained replaced) }



//    /// Replace the entry without needing to look at its contents
//    ///
//    /// Warning! It is on the caller to ensure that the refConstrs being added here don't have any overlap with any entries already present in the map, and to unify the entries accordingly if they do.
//    /// This will replace the entry at the _real_ AccId, so the caller doesn't have to worry about fetching the real AccId first
//    static member simpleReplaceEntry
//        (accId : AccumulatorTypeId)
//        (refDefResOpt : Result<RefDefType, AccTypeError> option)
//        (refConstrs : RefConstr set)
//        (acc : Accumulator)
//        : Accumulator =
//        Accumulator.replaceEntryWithRefDefAndConstrs accId (fun _ -> refDefResOpt, refConstrs) acc
//        |> snd


//    static member simpleReplaceRefDefEntry
//        (accId : AccumulatorTypeId)
//        (refDefResOpt : Result<RefDefType, AccTypeError> option)
//        (acc : Accumulator)
//        : Accumulator =
//        Accumulator.replaceEntryWithRefDefAndConstrs
//            accId
//            (function
//            | Generic _ -> refDefResOpt, Set.empty
//            | Constrained (_, refConstrs) -> refDefResOpt, refConstrs)
//            acc
//        |> snd


//    /// This can always be added without any further unifications needed 🥳 so it can be a very simple function.
//    /// Of course note that any AccIds referenced in the RefDef being added have to already exist in the Acc.
//    /// It's on the caller to ensure that we are not overwriting an existing entry in the Acc!
//    static member addRefDefResOptUnderKey
//        (key : AccumulatorTypeId)
//        (refDefResOpt : Result<RefDefType, AccTypeError> option)
//        (acc : Accumulator)
//        : Accumulator =
//        { acc with
//            refConstraintsMap = acc.refConstraintsMap |> Map.add key (Constrained (refDefResOpt, Set.empty)) }

//    /// This can always be added without any further unifications needed 🥳 so it can be a very simple function.
//    /// Of course note that any AccIds referenced in the RefDef being added have to already exist in the Acc
//    static member addRefDefResOpt
//        (refDefResOpt : Result<RefDefType, AccTypeError> option)
//        (acc : Accumulator)
//        : AccumulatorTypeId * Accumulator =
//        let newKey = System.Guid.NewGuid () |> AccumulatorTypeId

//        newKey, Accumulator.addRefDefResOptUnderKey newKey refDefResOpt acc


//    static member addGenericUnderKey key acc =
//        let newGeneric = makeTypeConstrId ()

//        { acc with
//            refConstraintsMap = acc.refConstraintsMap |> Map.add key (Generic newGeneric) }


//    static member addGeneric acc =
//        let newKey = System.Guid.NewGuid () |> AccumulatorTypeId
//        Accumulator.addGenericUnderKey newKey acc





//type VariantCase =
//    { label : UpperIdent
//      contents : TypeConstraints list }




type TypeDeclarationContent =
    | Sum of variants : NEL<VariantCase>
    | Alias of referent : TypeConstraints








(* Dictionaries of declared names *)

type TypeDeclarations = Map<UpperIdent, SOD<TypeDeclaration>>

and TypeConstructors = Map<UpperNameValue, SOD<VariantConstructor>>

and ValueDeclarations = Map<LowerNameValue, SOD<LowerCaseName>>

and ValueTypeDeclarations = Map<LowerNameValue, SOD<TypeConstraints>>

and TypeParams = Map<LowerIdent, SOD<unit>>

and InfixOps = Map<LowerIdent, SOD<DeclaredInfixOp>>








and DeclaredInfixOp =
    {
        associativity : S.InfixOpAssociativity
        precedence : int
        /// The value should be a function taking exactly two parameters
        value : Expression
    }


and VariantConstructor =
    { typeParamsList : LowerIdent list // So as to not lose track of the order of the type params
      typeParamsMap : TypeParams
      variantCase : VariantCase
      allVariants : NEL<VariantCase>
      typeName : UpperIdent }



and LowerCaseName =
    | LocalName of LetBinding
    | Param of Param
    | TopLevelName of Expression // ValueDeclaration -- This really only carried a TypedExpr anyway, so why stick it in a special wrapper record type







and TypeDeclaration =
    { typeParamsMap : TypeParams
      typeParamsList : LowerIdent list
      typeDeclaration : TypeDeclarationContent }







/// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
and LetBinding =
    {
        paramPattern : AssignmentPattern
        namesMap : Map<LowerIdent, SOD<Param>>
        /// @TODO: hmm not entirely sure what this thing actually describes. Is it the inferred type of the entire binding? Or is it _only_ the inferred shape based on the assignment pattern, which therefore still needs to be unified with the inferred type of the actual assigned expression?
        //bindingPatternInferredType : TypeJudgment

        (*
      @TODO: we need to take into account the assignment pattern here so that we can:
        a) add the type constraints implied by that pattern, and
        b) partially evaluate or slice up the expression so that we're assigning the right sub-expressions to the right names

      Although tbh evaluation of the assigned expression might not be straightforward, so maybe it is best to have something here to represent the fact that:
        a) we've only got one expression we're evaluating per binding (and so not doing the duplicate work of evaluating the expression once for every named value in the assignment pattern), and
        b) for each named value, what path to take in that expression to get the slice of the expression that should be assigned to it, e.g. a tuple, type destructuring, etc.
      *)
        assignedExpression : Expression

    //combinedInferredType : TypeJudgment
    }





and LetBindings = LetBinding nel

/// Represents all the named params in a single function parameter or case match expression
and FunctionOrCaseMatchParam =
    { paramPattern : AssignmentPattern
      namesMap : Map<LowerIdent, SOD<Param>>
    //inferredType : TypeJudgment
    }




and CompoundValues =
    | List of Expression list
    | Tuple of Expression tom
    | Record of (RecordFieldName * Expression) list
    | RecordExtension of recordToExtend : LowerIdent * additions : NEL<RecordFieldName * Expression>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParam nel
      body : Expression }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of S.PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : RecordFieldName




and ControlFlowExpression =
    | IfExpression of condition : Expression * ifTrue : Expression * ifFalse : Expression
    /// A `case <expr> of` expression with one or more patterns
    | CaseMatch of exprToMatch : Expression * branches : CaseMatchBranch nel

and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | UpperIdentifier of name : UpperNameValue
    | LowerIdentifier of name : LowerNameValue
    | LetExpression of namedValues : LetBindings * expr : Expression
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : Expression * op : OperatorIdent * right : Expression
    | FunctionApplication of funcExpr : Expression * params' : NEL<Expression>
    | DotAccess of expr : Expression * dotSequence : NEL<RecordFieldName>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParam
      body : Expression }


and Expression =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and OperatorIdent =
    | BuiltInOp of Lexer.BuiltInOperator
    | OtherOp of ident : LowerIdent




//and ValueAnnotation =
//    { /// these aren't in the source code, but they're gathered from the type expression implicitly
//      gatheredImplicitParams : TypeParams
//      annotatedType : DefinitiveType }







//and Declaration =
//    | ImportDeclaration of S.ImportDeclaration
//    | TypeDeclaration of name : UpperIdent * declaration : TypeDeclaration
//    | ValueTypeAnnotation of name : LowerIdent * ValueAnnotation
//    | ValueDeclaration of name : LowerIdent * ValueDeclaration


// Representing a whole file/module
and YlModule =
    { moduleDecl : S.ModuleDeclaration
      imports : S.ImportDeclaration list
      types : TypeDeclarations
      valueTypes : ValueTypeDeclarations
      values : Map<LowerIdent, SOD<Expression>>
      infixOperators : Map<LowerIdent, SOD<DeclaredInfixOp>> }

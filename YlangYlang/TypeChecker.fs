module TypeChecker


open Lexer
module Cst = ConcreteSyntaxTree



(*

@TODO list:

- [ ] resolve named values
    - [ ] in local scopes
    - [ ] from other modules
- [ ] infer types of primitives
- [ ] infer types of values referencing primitives
- [ ] infer types of

- [ ] parse type annotations
- [ ] infer types of values or function params by looking at the functions they are getting passed into
    - [ ] and similarly the types of values passed to operators

- [ ] support flagging up type clashes
    - [ ] and have some way of linking that back to a specific token, or even buffer range?

- [ ] support types with type params, e.g. `List a`
- [ ] support narrowing of types with type params while leaving the type params as generic

- [ ] support a parallel, field-name-and-value-based, type inference system to support typed records as extensible, partially typed things, instead of the all or nothing type system of generics vs explicit types specified above

*)


/// Not _really_ type classes, but the built-in Elm ones
type TypeClass =
    /// Includes both Ints and Floats
    | Number
    /// Values that can be compared for order or size, e.g. Strings, Ints, Chars
    | Comparable
    /// Values that can be appended, e.g. Strings and Lists
    | Appendable


/// Describes a single type constraint due to how a value is used
type SingleTypeConstraint<'a> =
    | GenericParam of UnqualValueIdentifier
    //| TypeClass of TypeClass
    /// For records and extended records
    | HasField of fieldName : UnqualValueIdentifier * valueConstraint : TypeConstraints<'a>
    /// We don't know what the type is but we do know that this thing has to be the same as this other thing
    | IsSameAs of UnqualValueIdentifier nel
    /// For specific, concrete types
    | Concrete of 'a


and TypeConstraints<'a> =
    /// No constraints whatsoever, this is a param that isn't used at all
    | Unconstrained
    | SingleConstraint of constraint_ : SingleTypeConstraint<'a>
    /// @TODO: might be good to make this more specific that it can relate to:
    /// - multiple generics, which therefore means that generic params `a` and `b` have to match, and any occurrence of `b` is effectively an occurrence of `a`
    /// - that generic `a` is actually a concrete type `A`, so any `a` is actually concrete type `A`
    /// - that it has multiple constraints of being generics, "type classes", and/or a concrete type
    /// Anything else would mean multiple concrete constraints, which are impossible
    | MultipleConstraints of SingleTypeConstraint<'a> nel


//type ConcreteOrGenericVar<'a> =
//    | Generic of UnqualValueIdentifier
//    | Concrete of 'a


type TypeState<'a> =
    { inferState : TypeConstraints<'a>
      /// The type declaration for the value
      typeDeclaration : SingleTypeConstraint<'a> option }




//type TypeJudgment<'a> =
//    //| NotTypedYet
//    //| GenericWithName of ConcreteOrGenericVar<'a>
//    | SpecificTypeConstraint of ConcreteOrGenericVar<'a>
//    /// Value is declared to be of type, either in an annotation or a parameter of a typed function.
//    /// If declared and inferred type constraints are different generics then that implies that those generics are actually not independent but need to be the same as each other.
//    | Declared of ConcreteOrGenericVar<'a>


type SimpleJudgment<'a> =
    | SimpleUnconstrained
    | SimpleUnified of 'a
    | SimpleConflicting of 'a * 'a nel




/// This will probably be used in a nested way for each of the parameters of a type that has type parameters, to achieve gradual typing of its fields
type TypeJudgment<'a> =
    /// `unifiedType` will be `None` if the value is unconstrained
    | Unified of unifiedType : SingleTypeConstraint<'a> option
    /// Conflicts between inferred types
    | ConflictingInferences of
        typeDeclaration : SingleTypeConstraint<'a> option *
        inferences : (SingleTypeConstraint<'a> * SingleTypeConstraint<'a> nel)
    /// Conflict between declared type and the one otherwise unified inferred type
    | ConflictDeclarationInferences of
        declaredType : SingleTypeConstraint<'a> *
        unifiedInferredTypes : SingleTypeConstraint<'a>
    /// Conflict both between declared type and also among the inferred types
    | ConflictDeclarationAndBetweenInferences of
        declaredType : SingleTypeConstraint<'a> *
        inferredTypes : (SingleTypeConstraint<'a> * SingleTypeConstraint<'a> nel)



/// Dear lord this is a big one - and doesn't even contain the actual unifier logic
/// But, ultimately this is the function that will let us do the type judgment on multiple type constraints!
let tryUnifyTypes
    (unifier : SimpleJudgment<SingleTypeConstraint<'a>>
                   -> SingleTypeConstraint<'a>
                   -> SimpleJudgment<SingleTypeConstraint<'a>>)
    (typeState : TypeState<'a>)
    : TypeJudgment<'a> =
    match typeState.typeDeclaration with
    | None ->
        match typeState.inferState with
        | Unconstrained -> Unified None
        | SingleConstraint constr -> Unified (Some constr)
        | MultipleConstraints constraints ->
            match NEL.fold<SimpleJudgment<SingleTypeConstraint<'a>>, SingleTypeConstraint<'a>>
                      unifier
                      SimpleUnconstrained
                      constraints
                with
            | SimpleUnconstrained -> Unified None
            | SimpleUnified unifiedInferredConstraint -> Unified (Some unifiedInferredConstraint)
            | SimpleConflicting (firstClash, otherClashes) -> ConflictingInferences (None, (firstClash, otherClashes))

    | Some declaration ->
        match typeState.inferState with
        | Unconstrained -> Unified (Some declaration)
        | SingleConstraint constr ->
            match unifier (SimpleUnified constr) declaration with
            | SimpleUnconstrained -> Unified (Some declaration)
            | SimpleUnified unified -> Unified (Some unified)
            | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, constr)

        | MultipleConstraints constraints ->
            match NEL.fold<_, _> unifier SimpleUnconstrained constraints with
            | SimpleUnconstrained -> Unified (Some declaration)
            | SimpleUnified unifiedInferreds ->
                match unifier (SimpleUnified unifiedInferreds) declaration with
                | SimpleUnconstrained -> Unified (Some declaration)
                | SimpleUnified fullyUnified -> Unified (Some fullyUnified)
                | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, unifiedInferreds)

            | SimpleConflicting (firstClash, otherClashes) ->
                ConflictingInferences (Some declaration, (firstClash, otherClashes))







type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    //| Unit
    | Bool


/// Represents a correct type without clashes
type DefinitiveType =
    | UnitType
    | PrimitiveType of BuiltInPrimitiveTypes
    /// I.e. could denote a constraint or invariant between multiple parameters.
    /// Could be bound or unbound.
    | GenericTypeVar of UnqualValueIdentifier
    | Tuple of TupleType
    | List of DefinitiveType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : DefinitiveType list
    | Arrow of fromType : DefinitiveType * toType : DefinitiveType


/// Because these are heterogeneous
and TupleType =
    { types : DefinitiveType * NEL<DefinitiveType> }


and RecordType =
    { fields : Map<UnqualValueIdentifier, DefinitiveType> }


and ExtendedRecordType =
    { extendedAlias : UnqualValueIdentifier
      fields : Map<UnqualValueIdentifier, DefinitiveType> }

and Dt = DefinitiveType


/// Represents an inferred type, whether full or partial
type InferredType =
    | Unit
    | Primitive of BuiltInPrimitiveTypes
    | Tuple of TypeInferenceState * TypeInferenceState nel
    | List of TypeInferenceState
    /// @TODO: this might not catch a possible clash, which is having the same name declared multiple times with a different type for each
    /// @TODO: also, let's do the specific ones first, and the record types with their different, set-like types, later

    | Record of Map<UnqualValueIdentifier, TypeInferenceState>
    | ExtendedRecord of Map<UnqualValueIdentifier, TypeInferenceState>
    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : TypeInferenceState list
    | Arrow of fromType : TypeInferenceState * toType : TypeInferenceState


/// Represents a set of type constraints
and TypeInferenceState = TypeConstraints<InferredType>





type VariablesConstraints = Map<UnqualValueIdentifier, TypeInferenceState>


/// Represents inferred type information for the expression, and also any constraints inferred on variables used in the expression.
/// @TODO: This may also need a field for bubbling up which inner variables could not be unified, so as to notify the developer of a type error
and GleanedInfo =
    { typeOfExpression : TypeInferenceState
      /// These are the constraints that were deduced from variables used in the expression
      variablesConstrained : VariablesConstraints

      valueNamesNotResolved : UnqualValueIdentifier list
      typeNamesNotResolved : UnqualTypeOrModuleIdentifier list

     }

let emptyGleanedInfo : GleanedInfo =
    { typeOfExpression = Unconstrained
      variablesConstrained = Map.empty
      valueNamesNotResolved = List.empty
      typeNamesNotResolved = List.empty }

let makeGleanedInfo (type_ : TypeInferenceState) variables : GleanedInfo =
    { emptyGleanedInfo with
        typeOfExpression = type_
        variablesConstrained = variables }


let getTypeInfo (gleaned : GleanedInfo) : TypeInferenceState = gleaned.typeOfExpression
let getConstrainedVars (gleaned : GleanedInfo) : VariablesConstraints = gleaned.variablesConstrained

// Not sure if this is useful yet
//type BuiltInCompoundTypes =
//    | List of MentionableType // or of it makes sense to have these subtypes on the compound type variants yet
//    | Record of (UnqualValueIdentifier * MentionableType) nel
//    | Tuple of TupleType




let typeOfPrimitiveLiteralValue : Cst.PrimitiveLiteralValue -> DefinitiveType =
    function
    | Cst.NumberPrimitive num ->
        match num with
        | Cst.FloatLiteral _ -> PrimitiveType Float
        | Cst.IntLiteral _ -> PrimitiveType Int
    | Cst.CharPrimitive _ -> PrimitiveType Char
    | Cst.StringPrimitive _ -> PrimitiveType String
    | Cst.UnitPrimitive _ -> UnitType
    | Cst.BoolPrimitive _ -> PrimitiveType Bool




let combineSingleConstraints
    (constraintA : SingleTypeConstraint<'a>)
    (constraintB : SingleTypeConstraint<'a>)
    : TypeConstraints<'a> =
    if constraintA = constraintB then
        SingleConstraint constraintA
    else
        MultipleConstraints (NEL.new_ constraintA [ constraintB ])



let combineManySingleConstraints (constraints : SingleTypeConstraint<'a> nel) : TypeConstraints<'a> =
    NEL.fold<_, _>
        (fun typeConstraints singleConstraint ->
            match typeConstraints with
            | Unconstrained -> SingleConstraint singleConstraint
            | SingleConstraint constr -> combineSingleConstraints singleConstraint constr
            | MultipleConstraints list ->
                singleConstraint :: NEL.toList list
                |> Set.ofList
                |> Set.toList
                |> function
                    | [] -> Unconstrained
                    | [ onlyOne ] -> SingleConstraint onlyOne
                    | head :: rest -> MultipleConstraints (NEL.new_ head rest))
        Unconstrained
        constraints



let combineTypeConstraints
    (constraintA : TypeConstraints<'a>)
    (constraintB : TypeConstraints<'a>)
    : TypeConstraints<'a> =
    match constraintA, constraintB with
    | Unconstrained, constraint_
    | constraint_, Unconstrained -> constraint_

    | SingleConstraint a, SingleConstraint b -> combineSingleConstraints a b

    | SingleConstraint a, MultipleConstraints b
    | MultipleConstraints b, SingleConstraint a -> combineManySingleConstraints (NEL.cons a b)

    | MultipleConstraints a, MultipleConstraints b -> combineManySingleConstraints (NEL.append a b)


let combineConstrainedVars (mapA : VariablesConstraints) (mapB : VariablesConstraints) : VariablesConstraints =
    Map.map
        (fun key value ->
            match Map.tryFind key mapB with
            | None -> value
            | Some valueInB -> combineTypeConstraints value valueInB)
        mapA

let combineGleanedInfos (cavA : GleanedInfo) (cavB : GleanedInfo) : GleanedInfo =
    { typeOfExpression = combineTypeConstraints cavA.typeOfExpression cavB.typeOfExpression
      variablesConstrained = combineConstrainedVars cavA.variablesConstrained cavB.variablesConstrained

      valueNamesNotResolved =
          cavA.valueNamesNotResolved
          @ cavB.valueNamesNotResolved
          |> List.distinct

      typeNamesNotResolved =
          cavA.typeNamesNotResolved
          @ cavB.typeNamesNotResolved
          |> List.distinct }


#nowarn "40"

let rec typeOfExpression : Cst.Expression -> GleanedInfo =
    fun _ -> failwithf "Not implemented yet!"


and typeOfCompoundValue : Cst.CompoundValues -> GleanedInfo =
    let rec listFolder items =
        match items with
        | [] -> emptyGleanedInfo
        | head :: tail ->
            let headConstraint = typeOfExpression head

            combineGleanedInfos headConstraint (listFolder tail)

    function
    | Cst.List exprs -> exprs |> List.map Cst.getNode |> listFolder

    | Cst.CompoundValues.Tuple (first, rest) ->
        let firstConstraint = typeOfExpression first.node

        NEL.toList rest
        |> List.map Cst.getNode
        |> listFolder
        |> combineGleanedInfos firstConstraint

    | Cst.CompoundValues.Record keyValList ->

        let (keyAndValsConstraints, constrainedVars) =
            keyValList
            |> List.fold
                (fun (keyAndValsConstraints, vars) (key, value) ->
                    let typeOfValue = typeOfExpression value.node
                    let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

                    let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

                    (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
                (List.empty, Map.empty)

        makeGleanedInfo
            (keyAndValsConstraints
             |> Map.ofList
             |> Record
             |> Concrete
             |> SingleConstraint)
            constrainedVars

    | Cst.CompoundValues.RecordExtension (recordToExtend, keyValList) ->

        let (keyAndValsConstraints, constrainedVars) =
            keyValList
            |> NEL.toList
            |> List.fold
                (fun (keyAndValsConstraints, vars) (key, value) ->
                    let typeOfValue = typeOfExpression value.node
                    let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

                    let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

                    (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
                (List.empty, Map.empty)

        let thisType =
            keyAndValsConstraints
            |> Map.ofList
            |> ExtendedRecord
            |> Concrete
            |> SingleConstraint

        // Need to ensure that we're constraining the record being extended to be the same as the key/val constraints we've got here
        Map.add recordToExtend.node thisType constrainedVars
        |> makeGleanedInfo thisType


/// @TODO: hmmmm, this guy kinda needs to be able to bubble up constraints upwards, onto the parameter as a whole, based on the shape of the destructuring that we do to the parameters.
/// I think the way to do this is that each one of these guys needs to bubble up the sub-shapes inside of itself, and thereby informs the caller of this function what this specific assignment pattern is. Whether this function is called by a top level parameter or a destructured part of it doesn't matter, because the consequences of that will just be handled by whatever calls this function.
let rec typeOfAssignmentPattern (assignmentPattern : Cst.AssignmentPattern) : GleanedInfo =
    match assignmentPattern with
    | Cst.Named _ -> makeGleanedInfo Unconstrained Map.empty
    | Cst.Ignored -> makeGleanedInfo Unconstrained Map.empty
    | Cst.Unit -> makeGleanedInfo (SingleConstraint (Concrete Unit)) Map.empty
    | Cst.Aliased (pattern, alias) ->
        let subType = typeOfAssignmentPattern pattern.node

        { subType with variablesConstrained = Map.add alias.node subType.typeOfExpression subType.variablesConstrained }
    | Cst.DestructuredPattern pattern -> typeOfDestructuredPattern pattern


and typeOfDestructuredPattern (destructuredPattern : Cst.DestructuredPattern) : GleanedInfo =
    match destructuredPattern with
    | Cst.DestructuredRecord fieldNames ->
        let justTheFieldNames = fieldNames |> NEL.map Cst.getNode

        let varConstraints : VariablesConstraints =
            justTheFieldNames
            |> NEL.map (fun fieldName -> fieldName, Unconstrained)
            |> NEL.toList
            |> Map.ofSeq

        let extendedRecordType =
            justTheFieldNames
            |> NEL.map (fun fieldName -> fieldName, Unconstrained)
            |> NEL.toList
            |> Map.ofSeq
            |> ExtendedRecord

        makeGleanedInfo (SingleConstraint (Concrete extendedRecordType)) varConstraints

    | Cst.DestructuredTuple (first, tail) ->
        let firstGleaned = typeOfAssignmentPattern first.node
        let restGleaned = NEL.map (Cst.getNode >> typeOfAssignmentPattern) tail

        let combinedVars =
            restGleaned
            |> NEL.map getConstrainedVars
            |> NEL.fold<_, _> combineConstrainedVars firstGleaned.variablesConstrained

        let inferredType =
            Tuple (firstGleaned.typeOfExpression, NEL.map getTypeInfo restGleaned)
            |> Concrete
            |> SingleConstraint

        makeGleanedInfo inferredType combinedVars


    | Cst.DestructuredCons (first, tail) ->
        let firstGleaned = typeOfAssignmentPattern first.node
        let restGleaned = NEL.map (Cst.getNode >> typeOfAssignmentPattern) tail

        let combinedVars =
            restGleaned
            |> NEL.map getConstrainedVars
            |> NEL.fold<_, _> combineConstrainedVars firstGleaned.variablesConstrained

        let constraints =
            NEL.map getTypeInfo restGleaned
            |> NEL.fold<_, _> combineTypeConstraints firstGleaned.typeOfExpression

        let inferredType = List constraints |> Concrete |> SingleConstraint

        makeGleanedInfo inferredType combinedVars

    | Cst.DestructuredTypeVariant (constructor, params_) -> failwithf "Implement this!"


//let typeOfFunction (functionValue: Cst.FunctionValue) :InferredTypeAndFoundConstraints =



//let typeOfCompoundLiteralValue =
//    function
//    | List

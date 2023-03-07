module TypeChecker


open Lexer
module Cst = ConcreteSyntaxTree

open NameResolution
open System


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


/// A named generic parameter - as opposed to an implicit generic parameter
type RigidGeneric = | RigidGeneric of UnqualValueIdentifier


type GenericParam =
    /// I.e. an explicit generic type parameter
    | Rigid of RigidGeneric
    /// An unspecified type param, which means it's not going to be explicitly linked to another generic param except for due to other type constraints
    | Flexible of Guid


/// Where did the type constraint come from
type TypeConstraintReason =
    /// Parameter or value is destructured upon in a pattern that requires the assigned value to be of a certain type
    | DestructuredPattern
    /// Value is passed into a function whose input is of type
    | IsPassedIntoFunction
    /// Is used as a function, with a value of a specific type passed to it - note that this doesn't really make sense unless the actual type constraint is
    | GetsParameterPassedToIt
    /// The value has an explicit shape, e.g. a type literal, a list literal, tuple literal, record, etc
    | IsExplicitShape
    /// The value is either assigned to a named value with a type declaration, or is returned from a function which has a type declaration
    | ValueIsPassedOrAssignedToValueWithDeclaredType
    /// Value is used as an operand for the provided operator
    | IsUsedWithOperator of Operator
    /// Not really sure if this is the right way to put it, but e.g. even if one item in a list is unconstrained, if a different member of the same list has a type, then all other list members will need to have the same type, ergo the constraint. Similarly if a Set or Dict or custom type with multiple members all have the same type, the type of one constrains them all
    | IsInHomogenousType


/// Describes a single type constraint due to how a value is used
type SingleTypeConstraint =
    | GenericParam of param : RigidGeneric * reason : TypeConstraintReason
    //| TypeClass of TypeClass
    /// For records and extended records
    | IsRecordsWithFields of
        fieldNamesAndVals : (UnqualValueIdentifier * TypeConstraints) list *
        reason : TypeConstraintReason
    /// We don't know what the type is but we do know that this thing has to be the same as this other thing.
    /// @TODO: I wonder if there is a way of "lifting" this kind of restriction so that it is a single restriction for all the affected values instead of carried separately on each of the affected values
    | IsSameAs of otherGenerics : RigidGeneric nel * reason : TypeConstraintReason
    /// For specific, concrete types
    | Concrete of concreteType : InferredType * reason : TypeConstraintReason


    static member getReason typeConstraint =
        match typeConstraint with
        | GenericParam (reason = reason) -> reason
        | IsRecordsWithFields (reason = reason) -> reason
        | IsSameAs (reason = reason) -> reason
        | Concrete (reason = reason) -> reason



and TypeConstraints =
    /// No constraints whatsoever, this is a param that isn't used at all
    | Unconstrained
    | SingleConstraint of constraint_ : SingleTypeConstraint
    /// @TODO: might be good to make this more specific that it can relate to:
    /// - multiple generics, which therefore means that generic params `a` and `b` have to match, and any occurrence of `b` is effectively an occurrence of `a`
    /// - that generic `a` is actually a concrete type `A`, so any `a` is actually concrete type `A`
    /// - that it has multiple constraints of being generics, "type classes", and/or a concrete type
    /// Anything else would mean multiple concrete constraints, which are impossible
    | MultipleConstraints of SingleTypeConstraint nel




and BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Bool


/// Represents an inferred type, whether full or partial
and InferredType =
    | Unit
    | Primitive of BuiltInPrimitiveTypes
    | Tuple of TypeConstraints tom
    | List of TypeConstraints
    /// This describes a record with potentially more unknown fields, e.g. when a record is destructured, or extended, or some of its records accessed, whether directly by dot suffix, or with a dot getter function
    /// @TODO: this might not catch a possible clash, which is having the same name declared multiple times with a different type for each
    | ExtendedRecord of
        /// The record to extend - in Elm this is restricted to a named identifier, so we don't have to account for arbitrary expressions
        /// but that extended record is only present in extended value declarations, this won't be present when only some fields from a record are accessed, like through dot getters or destructured parameters
        extendedRecord : UnqualValueIdentifier option *
        /// The actual fields accessed or tried to destructure
        referencedFields : Map<UnqualValueIdentifier, TypeConstraints>

    /// This denotes an exact record, e.g. as an explicit type declaration
    | Record of Map<UnqualValueIdentifier, TypeConstraints>
    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : TypeConstraints list
    | Arrow of fromType : TypeConstraints * toType : TypeConstraints





type TypeState =
    { inferState : TypeConstraints
      /// The type declaration for the value
      typeDeclaration : SingleTypeConstraint option }




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
    | SimpleConflicting of 'a tom




/// This will probably be used in a nested way for each of the parameters of a type that has type parameters, to achieve gradual typing of its fields
type TypeJudgment<'a> =
    /// `unifiedType` will be `None` if the value is unconstrained
    | Unified of unifiedType : SingleTypeConstraint option
    /// Conflicts between inferred types
    | ConflictingInferences of typeDeclaration : SingleTypeConstraint option * inferences : SingleTypeConstraint tom
    /// Conflict between declared type and the one otherwise unified inferred type
    | ConflictDeclarationInferences of declaredType : SingleTypeConstraint * unifiedInferredTypes : SingleTypeConstraint
    /// Conflict both between declared type and also among the inferred types
    | ConflictDeclarationAndBetweenInferences of
        declaredType : SingleTypeConstraint *
        inferredTypes : SingleTypeConstraint tom



/// Dear lord this is a big one - and doesn't even contain the actual unifier logic
/// But, ultimately this is the function that will let us do the type judgment on multiple type constraints!
let tryUnifyTypes
    (unifier : SimpleJudgment<SingleTypeConstraint> -> SingleTypeConstraint -> SimpleJudgment<SingleTypeConstraint>)
    (typeState : TypeState)
    : TypeJudgment<'a> =
    match typeState.typeDeclaration with
    | None ->
        match typeState.inferState with
        | Unconstrained -> Unified None
        | SingleConstraint constr -> Unified (Some constr)
        | MultipleConstraints constraints ->
            match NEL.fold<SimpleJudgment<SingleTypeConstraint>, SingleTypeConstraint>
                      unifier
                      SimpleUnconstrained
                      constraints
                with
            | SimpleUnconstrained -> Unified None
            | SimpleUnified unifiedInferredConstraint -> Unified (Some unifiedInferredConstraint)
            | SimpleConflicting clashes -> ConflictingInferences (None, clashes)

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

            | SimpleConflicting clashes -> ConflictingInferences (Some declaration, clashes)









/// Represents a correct type without clashes
type DefinitiveType =
    | DtUnitType
    | DtPrimitiveType of BuiltInPrimitiveTypes
    /// I.e. could denote a constraint or invariant between multiple parameters.
    /// Could be bound or unbound.
    | DtGenericTypeVar of UnqualValueIdentifier
    | DtTuple of TupleType
    | DtList of DefinitiveType
    | DtRecord of RecordType
    | DtExtendedRecord of ExtendedRecordType
    | DtReferencedType of typeName : TypeOrModuleIdentifier * typeParams : DefinitiveType list
    | DtArrow of fromType : DefinitiveType * toType : DefinitiveType


/// Because these are heterogeneous
and TupleType =
    { types : DefinitiveType * NEL<DefinitiveType> }


and RecordType =
    { fields : Map<UnqualValueIdentifier, DefinitiveType> }


and ExtendedRecordType =
    { extendedAlias : UnqualValueIdentifier
      fields : Map<UnqualValueIdentifier, DefinitiveType> }

and Dt = DefinitiveType







type VariablesConstraints = Map<UnqualValueIdentifier, TypeConstraints>


/// Represents inferred type information for the expression, and also any constraints inferred on variables used in the expression.
/// @TODO: This may also need a field for bubbling up which inner variables could not be unified, so as to notify the developer of a type error
and GleanedInfo =
    { typeOfExpression : TypeConstraints
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

let makeGleanedInfo (type_ : TypeConstraints) variables : GleanedInfo =
    { emptyGleanedInfo with
        typeOfExpression = type_
        variablesConstrained = variables }


let getTypeInfo (gleaned : GleanedInfo) : TypeConstraints = gleaned.typeOfExpression
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
        | Cst.FloatLiteral _ -> DtPrimitiveType Float
        | Cst.IntLiteral _ -> DtPrimitiveType Int
    | Cst.CharPrimitive _ -> DtPrimitiveType Char
    | Cst.StringPrimitive _ -> DtPrimitiveType String
    | Cst.UnitPrimitive _ -> DtUnitType
    | Cst.BoolPrimitive _ -> DtPrimitiveType Bool




let combineSingleConstraints
    (constraintA : SingleTypeConstraint)
    (constraintB : SingleTypeConstraint)
    : TypeConstraints =
    if constraintA = constraintB then
        SingleConstraint constraintA
    else
        MultipleConstraints (NEL.new_ constraintA [ constraintB ])



let combineManySingleConstraints (constraints : SingleTypeConstraint nel) : TypeConstraints =
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



let combineTypeConstraints (constraintA : TypeConstraints) (constraintB : TypeConstraints) : TypeConstraints =
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

let rec typeOfExpression : NamesInScope -> Cst.Expression -> GleanedInfo =
    fun _ _ -> failwithf "Not implemented yet!"


/// @TODO: this should contain the logic to type check resolved named values
and typeOfNamedValueIdentifier : NamesInScope -> UnqualValueIdentifier -> GleanedInfo =
    fun _ _ -> failwithf "Not implemented yet!"


and typeOfExplicitCompoundValue : NamesInScope -> Cst.CompoundValues -> GleanedInfo =
    fun namesInScope compoundValue ->

        let rec listFolder items =
            match items with
            | [] -> emptyGleanedInfo
            | head :: tail ->
                let headConstraint = typeOfExpression namesInScope head

                combineGleanedInfos headConstraint (listFolder tail)

        match compoundValue with
        | Cst.List exprs -> exprs |> List.map Cst.getNode |> listFolder

        | Cst.CompoundValues.Tuple (first, rest) ->
            let firstConstraint = typeOfExpression namesInScope first.node

            NEL.toList rest
            |> List.map Cst.getNode
            |> listFolder
            |> combineGleanedInfos firstConstraint

        | Cst.CompoundValues.Record keyValList ->

            let (keyAndValsConstraints, constrainedVars) =
                keyValList
                |> List.fold
                    (fun (keyAndValsConstraints, vars) (key, value) ->
                        let typeOfValue = typeOfExpression namesInScope value.node
                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
                    (List.empty, Map.empty)

            let inferredType = keyAndValsConstraints |> Map.ofList |> Record

            let constraints =
                Concrete (inferredType, IsExplicitShape)
                |> SingleConstraint

            makeGleanedInfo constraints constrainedVars

        | Cst.CompoundValues.RecordExtension (recordToExtend, keyValList) ->

            let (keyAndValsConstraints, constrainedVars) =
                keyValList
                |> NEL.toList
                |> List.fold
                    (fun (keyAndValsConstraints, vars) (key, value) ->
                        let typeOfValue = typeOfExpression namesInScope value.node
                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
                    (List.empty, Map.empty)

            //let extendedType =
            //    SingleValueIdentifier recordToExtend.node
            //    |> Cst.Identifier
            //    |> Cst.SingleValueExpression
            //    |> typeOfExpression namesInScope

            let constraints =
                ExtendedRecord (Some recordToExtend.node, Map.ofList keyAndValsConstraints)


            let thisType = SingleConstraint (Concrete (constraints, IsExplicitShape))

            // Need to ensure that we're constraining the record being extended to be the same as the key/val constraints we've got here
            Map.add recordToExtend.node thisType constrainedVars
            |> makeGleanedInfo thisType


/// @TODO: hmmmm, this guy kinda needs to be able to bubble up constraints upwards, onto the parameter as a whole, based on the shape of the destructuring that we do to the parameters.
/// I think the way to do this is that each one of these guys needs to bubble up the sub-shapes inside of itself, and thereby informs the caller of this function what this specific assignment pattern is. Whether this function is called by a top level parameter or a destructured part of it doesn't matter, because the consequences of that will just be handled by whatever calls this function.
let rec typeOfAssignmentPattern (assignmentPattern : Cst.AssignmentPattern) : GleanedInfo =
    match assignmentPattern with
    | Cst.Named _ -> makeGleanedInfo Unconstrained Map.empty
    | Cst.Ignored -> makeGleanedInfo Unconstrained Map.empty
    | Cst.Unit -> makeGleanedInfo (SingleConstraint (Concrete (Unit, IsExplicitShape))) Map.empty
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
            |> fun map -> ExtendedRecord (None, map)

        let inferredType =
            Concrete (extendedRecordType, DestructuredPattern)
            |> SingleConstraint

        makeGleanedInfo inferredType varConstraints

    | Cst.DestructuredTuple items ->
        let gleaneds = TOM.map (Cst.getNode >> typeOfAssignmentPattern) items

        let combinedVars =
            gleaneds
            |> TOM.map getConstrainedVars
            |> TOM.fold<_, _> combineConstrainedVars Map.empty

        let inferredType =
            Tuple (TOM.map getTypeInfo gleaneds)
            |> fun tupleType -> Concrete (tupleType, DestructuredPattern)
            |> SingleConstraint

        makeGleanedInfo inferredType combinedVars


    | Cst.DestructuredCons items ->
        let gleaneds = TOM.map (Cst.getNode >> typeOfAssignmentPattern) items

        let combinedVars =
            gleaneds
            |> TOM.map getConstrainedVars
            |> TOM.fold<_, _> combineConstrainedVars Map.empty

        let constraints =
            TOM.map getTypeInfo gleaneds
            |> TOM.fold<_, _> combineTypeConstraints Unconstrained

        let inferredType = Concrete (List constraints, DestructuredPattern)

        makeGleanedInfo (SingleConstraint inferredType) combinedVars

    | Cst.DestructuredTypeVariant (constructor, params_) -> failwithf "Implement this!"

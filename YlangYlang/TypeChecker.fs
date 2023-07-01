module TypeChecker


open Lexer
open NameResolution.PostResolution
open System


module Cst = ConcreteSyntaxTree
module S = SyntaxTree
module T = TypedSyntaxTree
module Q = QualifiedSyntaxTree

open Q.Names
open TypedSyntaxTree



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


let makeNewGeneric () = Guid.NewGuid () |> Set.singleton


let lowerIdentToRecFieldName (LowerIdent ident) = RecordFieldName ident


let rec mentionableTypeToDefinite (namesMaps : NamesMaps) (mentionable : Q.MentionableType) : InferredType =
    let innerFunc = mentionableTypeToDefinite namesMaps

    match mentionable with 
    | Q.UnitType -> Constrained DtUnitType
    | Q.GenericTypeVar (ResolvedTypeParam genericTypeVar) -> Unconstrained <| Set.singleton genericTypeVar

    | Q.Tuple { types = types } ->
        types
        |> TOM.map (S.getNode >> innerFunc)
        |> DtTuple
        |> Constrained

    | Q.Record { fields = fields } ->
        fields
        |> Map.mapKeyVal (fun key value -> key.node, innerFunc value.node)
        |> DtRecordExact
        |> Constrained

    | Q.ExtendedRecord { extendedAlias = alias
                         fields = fields } ->

        fields
        |> Map.mapKeyVal (fun key value -> key.node, innerFunc value.node)
        |> DtRecordWith
        |> Constrained

    | Q.ReferencedType (typeName, typeParams) ->
        let definiteTypeParams = List.map (S.getNode >> innerFunc) typeParams

        DtReferencedType (typeName, definiteTypeParams)
        |> Constrained

    | Q.Arrow (fromType, toTypes) ->
        DtArrow (innerFunc fromType.node, NEL.map (S.getNode >> innerFunc) toTypes)
        |> Constrained

    | Q.Parensed parensed -> innerFunc parensed.node
    //| Q.Arrow arrow ->
    //| Q.Parensed parensed ->













let concatResultErrListNel (result : Result<'a, 'Err list nel>) : Result<'a, 'Err list> =
    Result.mapError (NEL.toList >> List.concat) result





let makeTypedExpr (judgment : TypeJudgment) (expr : SingleOrCompoundExpr) : Expression =
    { inferredType = judgment; expr = expr }



/// This is for unifying concrete containers of multiple types... I think. So it's about
let rec unifyInferredTypes (typeA : InferredType) (typeB : InferredType) : TypeJudgment =
    match typeA, typeB with
    | Unconstrained guidsA, Unconstrained guidsB -> Set.union guidsA guidsB |> Unconstrained |> Ok
    | Constrained a, Unconstrained _
    | Unconstrained _, Constrained a -> Constrained a |> Ok
    | Constrained a, Constrained b -> unifyInferredDefinitiveTypes a b



/// @TODO: remember to resolve named types to check for unification, e.g. with named alias type and record
and unifyInferredDefinitiveTypes (typeA : DefinitiveType) (typeB : DefinitiveType) : TypeJudgment =
    match typeA, typeB with
    | DtTuple a, DtTuple b ->
        unifyTypesTom a b
        |> Result.mapError (fun (first, second) -> [ DtTuple first; DtTuple second ])
        |> Result.bind (TOM.sequenceResult >> concatResultErrListNel)
        |> Result.map (DtTuple >> Constrained)

    | DtList a, DtList b ->
        unifyInferredTypes a b
        |> Result.map (DtList >> Constrained)

    | DtArrow (fromA, toA), DtArrow (fromB, toB) ->
        let toTypes =
            unifyTypesNel toA toB
            |> Result.mapError (fun _ ->
                [ DtArrow (fromA, toA)
                  DtArrow (fromB, toB) ])
            |> Result.bind (NEL.sequenceResult >> concatResultErrListNel)

        (unifyInferredTypes fromA fromB, toTypes)
        ||> Result.map2
                (fun fromType toTypes_ -> DtArrow (fromType, toTypes_) |> Constrained)
                (fun _ _ ->
                    [ DtArrow (fromA, toA)
                      DtArrow (fromB, toB) ])

    | DtReferencedType (typeRefA, typeParamsA), DtReferencedType (typeRefB, typeParamsB) ->
        if typeRefA = typeRefB then
            unifyTypesList typeParamsA typeParamsB
            |> Result.mapError (fun (first, second) ->
                [ DtReferencedType (typeRefA, first)
                  DtReferencedType (typeRefB, second) ])
            |> Result.bind (Result.sequenceList >> concatResultErrListNel)
            |> Result.map (fun unifiedParams ->
                DtReferencedType (typeRefA, unifiedParams)
                |> Constrained)

        else
            Error [ typeA; typeB ]

    | DtRecordExact a, DtRecordExact b ->
        Map.mergeExact (fun _ valueA valueB -> unifyInferredTypes valueA valueB) a b
        |> Result.mapError (fun _ -> [ DtRecordExact a; DtRecordExact b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (Map.values >> List.concat)
        )
        |> Result.map (DtRecordExact >> Constrained)

    | DtRecordWith a, DtRecordWith b ->
        Map.mergeExact (fun _ valueA valueB -> unifyInferredTypes valueA valueB) a b
        |> Result.mapError (fun _ -> [ DtRecordWith a; DtRecordWith b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (Map.values >> List.concat)
        )
        |> Result.map (DtRecordExact >> Constrained)

    | DtUnitType, DtUnitType -> DtUnitType |> Constrained |> Ok
    | DtPrimitiveType a, DtPrimitiveType b ->
        if a = b then
            DtPrimitiveType a |> Constrained |> Ok
        else
            Error [ DtPrimitiveType a
                    DtPrimitiveType b ]

    | _, _ -> Error [ typeA; typeB ]








/// If lengths are the same, returns a list of that length of the type judgments of trying to merge the type at every index in both lists. If lengths are not the same though, returns an error result of both inferred types lists.
and private listTraverser onLengthErr listA listB =
    match listA, listB with
    | [], [] -> Ok []
    | headA :: tailA, headB :: tailB ->
        let unifiedHead = unifyInferredTypes headA headB

        listTraverser onLengthErr tailA tailB
        |> Result.map (fun unifiedTail -> unifiedHead :: unifiedTail)

    | [], _ :: _
    | _ :: _, [] -> Error onLengthErr



and unifyTypesList
    (listA : InferredType list)
    (listB : InferredType list)
    : Result<TypeJudgment list, InferredType list * InferredType list> =
    listTraverser (listA, listB) listA listB

and unifyTypesNel
    (NEL (headA, tailA) as nelA : InferredType nel)
    (NEL (headB, tailB) as nelB : InferredType nel)
    : Result<TypeJudgment nel, InferredType nel * InferredType nel> =
    listTraverser (nelA, nelB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyInferredTypes headA headB
        NEL (unifiedHead, unifiedTail))



and unifyTypesTom
    (TOM (headA, neckA, tailA) as listA : InferredType tom)
    (TOM (headB, neckB, tailB) as listB : InferredType tom)
    : Result<TypeJudgment tom, InferredType tom * InferredType tom> =
    listTraverser (listA, listB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyInferredTypes headA headB
        let unifiedNeck = unifyInferredTypes neckA neckB
        TOM (unifiedHead, unifiedNeck, unifiedTail))





and tryUnifyJudgments (judgmentA : TypeJudgment) (judgmentB : TypeJudgment) =
    match judgmentA, judgmentB with
    | Ok a, Ok b -> unifyInferredTypes a b

    | Error err, Ok (Constrained t)
    | Ok (Constrained t), Error err -> Error (t :: err)

    | Error e, Ok (Unconstrained _)
    | Ok (Unconstrained _), Error e -> Error e

    | Error a, Error b -> Error (List.append a b)









let typeOfPrimitiveLiteralValue (primitive : S.PrimitiveLiteralValue) : T.DefinitiveType =
    match primitive with
    | S.NumberPrimitive num ->
        match num with
        | S.FloatLiteral _ -> T.DtPrimitiveType T.Float
        | S.IntLiteral _ -> T.DtPrimitiveType T.Int
    | S.CharPrimitive _ -> T.DtPrimitiveType T.Char
    | S.StringPrimitive _ -> T.DtPrimitiveType T.String
    | S.UnitPrimitive _ -> T.DtUnitType
    | S.BoolPrimitive _ -> T.DtPrimitiveType T.Bool


let rec typeCheckExpression (namesMaps : NamesMaps) (expr : Q.Expression) : Expression =
    let innerTypeCheck = typeCheckExpression namesMaps

    match expr with
    | Q.SingleValueExpression singleVal ->
        match singleVal with
        | Q.ExplicitValue explicit ->
            match explicit with
            | Q.Primitive primitive ->
                let type_ =
                    typeOfPrimitiveLiteralValue primitive
                    |> Constrained
                    |> Ok

                { inferredType = type_
                  expr =
                    Primitive primitive
                    |> ExplicitValue
                    |> SingleValueExpression }


            | Q.DotGetter dotGetter ->
                let recFieldName = lowerIdentToRecFieldName dotGetter

                let type_ =
                    Map.empty
                    |> Map.add recFieldName (Unconstrained <| makeNewGeneric ())
                    |> DtRecordWith
                    |> Constrained
                    |> Ok

                { inferredType = type_
                  expr =

                    DotGetter recFieldName
                    |> ExplicitValue
                    |> SingleValueExpression }

            | Q.Compound compound ->
                match compound with
                | Q.List list ->
                    let typedList = List.map (S.mapNode innerTypeCheck) list

                    let combinedType =
                        typedList
                        |> List.map S.getNode
                        |> List.fold
                            (fun state expr ->
                                (state, expr.inferredType)
                                ||> Result.bind2 (fun stateSoFar inferred -> unifyInferredTypes stateSoFar inferred) (@))
                            (makeNewGeneric () |> Unconstrained |> Ok)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> List
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | Q.CompoundValues.Tuple tuple ->
                    let typedList = TOM.map (S.mapNode innerTypeCheck) tuple

                    let combinedType =
                        typedList
                        |> TOM.map (fun expr -> expr.node.inferredType)
                        |> TOM.sequenceResult
                        |> concatResultErrListNel
                        |> Result.map (DtTuple >> Constrained)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> CompoundValues.Tuple
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | Q.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) -> key, S.mapNode innerTypeCheck value)

                    let combinedType =
                        typedList
                        |> List.map (fun (key, expr) ->
                            expr.node.inferredType
                            |> Result.map (fun inferred -> key.node, inferred))
                        |> Result.sequenceList
                        |> Result.map Map.ofList
                        |> concatResultErrListNel
                        |> Result.map (DtRecordExact >> Constrained)

                    { inferredType = combinedType
                      expr =
                        typedList
                        |> CompoundValues.Record
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | Q.CompoundValues.RecordExtension (extended, record) ->
                    let resolved = extended |> S.getNode |> snd 
                    let resolvedItem = findValue resolved namesMaps


//| Q.Tuple
//| Q.Record
//| Q.RecordExtension

//| Q.Function func ->

//| Q.UpperIdentifier
//| Q.LowerIdentifier
//| Q.LetExpression
//| Q.ControlFlowExpression










///// Not _really_ type classes, but the built-in Elm ones
//type TypeClass =
//    /// Includes both Ints and Floats
//    | Number
//    /// Values that can be compared for order or size, e.g. Strings, Ints, Chars
//    | Comparable
//    /// Values that can be appended, e.g. Strings and Lists
//    | Appendable


///// A named generic parameter - as opposed to an implicit generic parameter
//type RigidGeneric = | RigidGeneric of UnqualValueIdentifier


//type GenericParam =
//    /// I.e. an explicit generic type parameter
//    | Rigid of RigidGeneric
//    /// An unspecified type param, which means it's not going to be explicitly linked to another generic param except for due to other type constraints
//    | Flexible of Guid


///// Where did the type constraint come from
//type TypeConstraintReason =
//    /// Parameter or value is destructured upon in a pattern that requires the assigned value to be of a certain type
//    | DestructuredPattern
//    /// Value is passed into a function whose input is of type
//    | IsPassedIntoFunction
//    /// Is used as a function, with a value of a specific type passed to it - note that this doesn't really make sense unless the actual type constraint is
//    | GetsParameterPassedToIt
//    /// The value has an explicit shape, e.g. a type literal, a list literal, tuple literal, record, etc
//    | IsExplicitShape
//    /// The value is either assigned to a named value with a type declaration, or is returned from a function which has a type declaration
//    | ValueIsPassedOrAssignedToValueWithDeclaredType
//    /// Value is used as an operand for the provided operator
//    | IsUsedWithOperator of Operator
//    /// Not really sure if this is the right way to put it, but e.g. even if one item in a list is unconstrained, if a different member of the same list has a type, then all other list members will need to have the same type, ergo the constraint. Similarly if a Set or Dict or custom type with multiple members all have the same type, the type of one constrains them all
//    | IsInHomogenousType


//type SingleTypeConstraint = InferredType<TypeConstraints>

///// Describes a single type constraint due to how a value is used
//and TypeConstraints =
//    /// No constraints whatsoever, this is a param that isn't used at all
//    | Unconstrained
//    | SingleConstraint of SingleTypeConstraint
//    /// @TODO: might be good to make this more specific that it can relate to:
//    /// - multiple generics, which therefore means that generic params `a` and `b` have to match, and any occurrence of `b` is effectively an occurrence of `a`
//    /// - that generic `a` is actually a concrete type `A`, so any `a` is actually concrete type `A`
//    /// - that it has multiple constraints of being generics, "type classes", and/or a concrete type
//    /// Anything else would mean multiple concrete constraints, which are impossible
//    | MultipleConstraints of SingleTypeConstraint tom


//and BuiltInPrimitiveTypes =
//    | Float
//    | Int
//    | String
//    | Char
//    | Bool


///// Represents an inferred type, whether full or partial.
///// It's a generic cos it can be used for multiple different stages of the type checking/inference process
//and InferredType<'TypeInfo> =
//    | Unit
//    | Primitive of BuiltInPrimitiveTypes
//    /// I wonder if it makes sense to have generics as their own inferred type variant, instead of just having generically constrained params just be referenced via a constraint on one or both of the linked things... I think this makes sense here so I'll keep it here for now and we'll see how we go
//    | Generic of GenericParam

//    | Tuple of 'TypeInfo tom
//    | List of 'TypeInfo
//    /// This describes a record with potentially more unknown fields, e.g. when a record is destructured, or extended, or some of its records accessed, whether directly by dot suffix, or with a dot getter function
//    /// @TODO: this might not catch a possible clash, which is having the same name declared multiple times with a different type for each
//    | RecordWith of
//        //extendedRecord : UnqualValueIdentifier option *
//        /// The actual fields accessed or tried to destructure
//        referencedFields : Map<UnqualValueIdentifier, 'TypeInfo>

//    /// This denotes an exact record, e.g. as an explicit type declaration
//    | RecordExact of Map<UnqualValueIdentifier, 'TypeInfo>
//    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : 'TypeInfo list
//    | Arrow of fromType : 'TypeInfo * toType : 'TypeInfo nel





///// Represents a correct type without clashes
//and DefinitiveType =
//    | DtUnitType
//    | DtPrimitiveType of BuiltInPrimitiveTypes
//    /// I.e. could denote a constraint or invariant between multiple parameters.
//    /// Could be bound or unbound.
//    //| DtGeneric of GenericParam
//    | DtTuple of DefinitiveType tom
//    | DtList of DefinitiveType
//    | DtRecordWith of referencedFields : Map<UnqualValueIdentifier, DefinitiveType>
//    | DtRecordExact of Map<UnqualValueIdentifier, DefinitiveType>
//    /// The typeParams of the referenced type should start off as unconstraineds, but then fill out with more definitive types, as the constraints build up
//    | DtReferencedType of typeName : TypeOrModuleIdentifier * typeParams : DefinitiveType list
//    | DtArrow of fromType : DefinitiveType * toType : DefinitiveType






//module TypeCheckingInfo =



//    /// This should be able to be determined based on the ResolvedNames maps and a type expression
//    //type TypedValues = Map<ValueIdentifier, TypeConstraints>
//    type TypedValues = Map<ValueIdentifier, DefinitiveType>

//    /// Don't worry about capturing the location of the type clashes for now
//    type TypeClashes = (DefinitiveType tom) list

//    type ConstrainedOrNot =
//        | NotYetConstrained
//        | Constrained of DefinitiveType

//    type TypeJudgment =
//        | Unified of ConstrainedOrNot
//        | Clashing of DefinitiveType tom
//        | UnresolvedName of Identifier



//    type ConstrainedVars = Map<ValueIdentifier, ConstrainedOrNot>
//    type ConstrainedGenerics = Map<RigidGeneric, TypeJudgment>



//    let combineDefinitiveType
//        (dType1 : DefinitiveType)
//        (dType2 : DefinitiveType)
//        : Result<DefinitiveType, DefinitiveType tom> =
//        match dType1, dType2 with
//        | DtRecordWith fields1, DtRecordWith fields2 ->
//            let combined =
//                Map.fold
//                    (fun combinedMapResult key value ->
//                        match combinedMapResult with
//                        | Ok combinedMap ->

//                            match Map.tryFind key combinedMap with
//                            | None -> Ok (Map.add key value combinedMap)
//                            | Some fieldValueType ->
//                                if fieldValueType = value then
//                                    Ok (Map.add key value combinedMap)
//                                else
//                                    Error (TOM.make dType1 dType2)
//                        | Error e -> Error e)
//                    (Ok fields2)
//                    fields1

//            Result.map DtRecordWith combined
//        | DtRecordWith extendedFields, DtRecordExact exactFields
//        | DtRecordExact exactFields, DtRecordWith extendedFields ->
//            let combined =
//                extendedFields
//                |> Map.fold
//                    (fun exactFieldsResult extendedKey extendedFieldValType ->
//                        match exactFieldsResult with
//                        | Ok exactResult' ->

//                            match Map.tryFind extendedKey exactResult' with
//                            | None -> Error (TOM.make dType1 dType2)
//                            | Some fieldValueType ->
//                                if fieldValueType = extendedFieldValType then
//                                    Ok (Map.add extendedKey extendedFieldValType exactResult')
//                                else
//                                    Error (TOM.make dType1 dType2)
//                        | Error e -> Error e)
//                    (Ok exactFields)

//            Result.map DtRecordExact combined

//    //| DtGeneric generic1, DtGeneric generic2 ->



//    let combineJudgments (judgment1 : TypeJudgment) (judgment2 : TypeJudgment) =
//        match judgment1, judgment2 with
//        | UnresolvedName name, _
//        | _, UnresolvedName name -> UnresolvedName name

//        | Clashing list1, Clashing list2 -> Clashing (TOM.append list1 list2)

//        | Unified NotYetConstrained, x
//        | x, Unified NotYetConstrained -> x

//        | Unified (Constrained type1), Unified (Constrained type2) -> ()



//    let mergeTypeJudgmentMaps (map1 : ConstrainedGenerics) (map2 : ConstrainedGenerics) =
//        map2
//        |> Map.fold
//            (fun combinedMap key newJudgment ->
//                match Map.tryFind key combinedMap with
//                | None -> combinedMap
//                | Some oldJudgment ->
//                    match oldJudgment with
//                    | Unified constrainedOrNot ->
//                        match constrainedOrNot with
//                        | NotYetConstrained -> newJudgment
//                //    | Constrained type_ ->
//                //| Clashing list ->
//                //| UnresolvedName name ->

//                //Map.add key( Clashing (TOM.make   ) )

//                )
//            map1

//    type private TypeCheckingInfo'<'a> =
//        { expressionType : 'a //TypeJudgment
//          constrainedGenerics : ConstrainedGenerics
//          /// Because the names inside the scope don't need to be propagated out of the scope where they live
//          constrainedVarsOutsideScope : ConstrainedVars
//          unresolvedNames : Set<Identifier>
//          typeClashes : TypeClashes }



//    let succeed x =
//        { expressionType = x
//          constrainedGenerics = Map.empty
//          constrainedVarsOutsideScope = Map.empty
//          unresolvedNames = Set.empty
//          typeClashes = List.empty }

//    let bind : ('a -> TypeCheckingInfo'<'b>) -> TypeCheckingInfo'<'a> -> TypeCheckingInfo'<'b> =
//        fun f info ->
//            let result = f info.expressionType

//            { expressionType = result.expressionType
//              constrainedGenerics = Map.merge
//              constrainedVarsOutsideScope =
//                Map.merge info.constrainedVarsOutsideScope result.constrainedVarsOutsideScope
//              unresolvedNames = Set.union info.unresolvedNames result.unresolvedNames
//              typeClashes = info.typeClashes @ result.typeClashes }

//    let join : TypeCheckingInfo'<TypeCheckingInfo'<'a>> -> TypeCheckingInfo'<'a> =
//        fun info -> bind id info

//    let map : ('a -> 'b) -> TypeCheckingInfo'<'a> -> TypeCheckingInfo'<'b> =
//        fun f info ->
//            { expressionType = f info.expressionType
//              constrainedVarsOutsideScope = info.constrainedVarsOutsideScope
//              unresolvedNames = info.unresolvedNames
//              typeClashes = info.typeClashes }

//    let addUnresolved name info =
//        { info with unresolvedNames = Set.add name info.unresolvedNames }

//    type TypeCheckingInfo = TypeCheckingInfo'<TypeJudgment>


//open TypeCheckingInfo

//module Tci = TypeCheckingInfo



//type VariablesConstraints = Map<Identifier, TypeConstraints>


///// Represents inferred type information for the expression, and also any constraints inferred on variables used in the expression.
///// @TODO: This may also need a field for bubbling up which inner variables could not be unified, so as to notify the developer of a type error
//type GleanedInfo =
//    { typeOfExpression : TypeConstraints
//      /// These are the constraints that were deduced from variables used in the expression
//      variablesConstrained : VariablesConstraints

//      /// @TODO: tbh we could probably stick all of the unresolved names in the same list, just in DUs for each type of thing
//      //valueNamesNotResolved : UnqualValueIdentifier list
//      //typeNamesNotResolved : UnqualTypeOrModuleIdentifier list

//      namesNotResolved : Set<Identifier> }

//let emptyGleanedInfo : GleanedInfo =
//    { typeOfExpression = Unconstrained
//      variablesConstrained = Map.empty
//      namesNotResolved = Set.empty }

//let makeGleanedInfo (type_ : TypeConstraints) variables : GleanedInfo =
//    { emptyGleanedInfo with
//        typeOfExpression = type_
//        variablesConstrained = variables }


//let getTypeInfo (gleaned : GleanedInfo) : TypeConstraints = gleaned.typeOfExpression
//let getConstrainedVars (gleaned : GleanedInfo) : VariablesConstraints = gleaned.variablesConstrained





//// Not sure if this is useful yet
////type BuiltInCompoundTypes =
////    | List of MentionableType // or of it makes sense to have these subtypes on the compound type variants yet
////    | Record of (UnqualValueIdentifier * MentionableType) nel
////    | Tuple of TupleType




////let typeOfPrimitiveLiteralValue : Cst.PrimitiveLiteralValue -> DefinitiveType =
////    function
////    | Cst.NumberPrimitive num ->
////        match num with
////        | Cst.FloatLiteral _ -> DtPrimitiveType Float
////        | Cst.IntLiteral _ -> DtPrimitiveType Int
////    | Cst.CharPrimitive _ -> DtPrimitiveType Char
////    | Cst.StringPrimitive _ -> DtPrimitiveType String
////    | Cst.UnitPrimitive _ -> DtUnitType
////    | Cst.BoolPrimitive _ -> DtPrimitiveType Bool




//type UnificationResult =
//    | Unified of DefinitiveType
//    /// I.e. unification requires all these generics to be assignable to each other - I suppose another way of saying that it's a way of denoting equality between generics?
//    | UnificationDependsOnGenerics of DefinitiveType * generics : RigidGeneric nel
//    | IncompatibleConstraints of DefinitiveType tom





//let rec unifier (constraintA : SingleTypeConstraint) (constraintB : SingleTypeConstraint) : UnificationResult =
//    match constraintA, constraintB with
//    | Unit, Unit -> Ok Unit
//    | Generic genA, Generic genB ->
//        match genA, genB with
//        | Rigid r, Flexible _
//        | Flexible _, Rigid r -> Rigid r |> DtGeneric |> Unified
//        | Rigid rA, Rigid rB ->
//            // @TODO: hmmm, need a way to capture here that it *could* be unified, but we just don't know yet until we know what the generic params are
//            //Rigid rA |> Generic |> Ok
//            UnificationDependsOnGenerics (NEL.new_ rA [ rB ])
//        | Flexible a, Flexible _ -> Flexible a |> DtGeneric |> Unified
//    | Primitive pA, Primitive pB ->
//        if pA = pB then
//            DtPrimitiveType pA |> Unified
//        else
//            IncompatibleConstraints (TOM.make (DtPrimitiveType pA) (DtPrimitiveType pB))
//    | Tuple listA, Tuple listB ->
//        //let rec traverseTupleItems a b : UnificationResult =
//        //    match a, b with
//        //    | [], [] -> Flexible (Guid.NewGuid ()) |> DtGeneric |> Unified
//        //    | headA :: restA, headB :: restB ->
//        //        match unifier headA headB with
//        //        | Unified unified ->
//        //            match traverseTupleItems restA restB with
//        //            | Unified unifiedRest ->



//        //                Unified (DtTuple (TOM.make unified (traverseTupleItems restA restB)))
//        //        | UnificationDependsOnGenerics generics -> Error (constraintA, constraintB)
//        //    | [], _ :: _
//        //    | _ :: _, [] -> Error (constraintA, constraintB)

//        match traverseTupleItems (TOM.toList listA) (TOM.toList listB) with
//        | Ok _ -> Tuple listA |> Ok
//        | Error err -> Error err






////| Unit, Unit -> Ok Unit





//let combineSingleConstraints
//    (constraintA : SingleTypeConstraint)
//    (constraintB : SingleTypeConstraint)
//    : TypeConstraints =
//    if constraintA = constraintB then
//        SingleConstraint constraintA
//    else
//        MultipleConstraints (TOM.make constraintA constraintB)



//let combineManySingleConstraints (constraints : SingleTypeConstraint tom) : TypeConstraints =
//    TOM.fold<_, _>
//        (fun typeConstraints singleConstraint ->
//            match typeConstraints with
//            | Unconstrained -> SingleConstraint singleConstraint
//            | SingleConstraint constr -> combineSingleConstraints singleConstraint constr
//            | MultipleConstraints list ->
//                singleConstraint :: TOM.toList list
//                |> Set.ofList
//                |> Set.toList
//                |> function
//                    | [] -> Unconstrained
//                    | [ onlyOne ] -> SingleConstraint onlyOne
//                    | head :: neck :: rest -> MultipleConstraints (TOM.new_ head neck rest))
//        Unconstrained
//        constraints



//let combineTypeConstraints (constraintA : TypeConstraints) (constraintB : TypeConstraints) : TypeConstraints =
//    match constraintA, constraintB with
//    | Unconstrained, constraint_
//    | constraint_, Unconstrained -> constraint_

//    | SingleConstraint a, SingleConstraint b -> combineSingleConstraints a b

//    | SingleConstraint a, MultipleConstraints b
//    | MultipleConstraints b, SingleConstraint a -> combineManySingleConstraints (TOM.cons a b)

//    | MultipleConstraints a, MultipleConstraints b -> combineManySingleConstraints (TOM.append a b)


//let combineConstrainedVars (mapA : VariablesConstraints) (mapB : VariablesConstraints) : VariablesConstraints =
//    Map.map
//        (fun key value ->
//            match Map.tryFind key mapB with
//            | None -> value
//            | Some valueInB -> combineTypeConstraints value valueInB)
//        mapA

//let combineGleanedInfos (cavA : GleanedInfo) (cavB : GleanedInfo) : GleanedInfo =
//    { typeOfExpression = combineTypeConstraints cavA.typeOfExpression cavB.typeOfExpression
//      variablesConstrained = combineConstrainedVars cavA.variablesConstrained cavB.variablesConstrained
//      namesNotResolved = Set.union cavA.namesNotResolved cavB.namesNotResolved }









///// Get the generic names of the parameters for a type declaration
//let private getTypeParams typeDecl =
//    match typeDecl with
//    | Cst.Alias { specifiedTypeParams = params' } -> List.map (Cst.getNode >> RigidGeneric) params'
//    | Cst.Sum { specifiedTypeParams = params' } -> List.map (Cst.getNode >> RigidGeneric) params'




////let rec private getInferredTypeFromMentionableType (mentionableType : Cst.MentionableType) : SingleTypeConstraint =
//let rec private getInferredTypeFromMentionableType (mentionableType : Cst.MentionableType) : DefinitiveType =
//    match mentionableType with
//    | Cst.GenericTypeVar name -> DtGeneric (Rigid (RigidGeneric name))
//    | Cst.UnitType -> DtUnitType
//    | Cst.Tuple { types = types } ->
//        TOM.map (Cst.getNode >> getInferredTypeFromMentionableType) types
//        |> DtTuple
//    | Cst.Record { fields = fields } ->
//        fields
//        |> Map.mapKeyVal (fun fieldName type' -> fieldName.node, getInferredTypeFromMentionableType type'.node)
//        |> DtRecordExact
//    | Cst.ExtendedRecord { fields = fields } ->
//        // @TODO: need to actually figure out the semantics of what it means to have `{ a | otherFields : otherType }`, is a the exact same record as the whole thing? Is it all the fields *except* for `otherFields`? Need to clarify
//        fields
//        |> Map.mapKeyVal (fun fieldName type' -> fieldName.node, getInferredTypeFromMentionableType type'.node)
//        |> DtRecordWith
//    | Cst.ReferencedType (typeName, typeParams) ->
//        DtReferencedType (typeName.node, List.map (Cst.getNode >> getInferredTypeFromMentionableType) typeParams)
//    | Cst.Arrow (fromType, toType) ->

//        let rec foldUpArrowDestType ((NEL (head, rest)) : DefinitiveType nel) : DefinitiveType =
//            match rest with
//            | [] -> head
//            | neck :: tail -> DtArrow (head, foldUpArrowDestType (NEL (neck, tail)))

//        DtArrow (
//            fromType.node
//            |> getInferredTypeFromMentionableType,
//            toType
//            |> NEL.map (Cst.getNode >> getInferredTypeFromMentionableType)
//            |> foldUpArrowDestType
//        )
//    | Cst.Parensed { node = node } -> getInferredTypeFromMentionableType node



////and getTypeConstraints (mentionableType : Cst.MentionableType) : InferredType =
////    Concrete (t, IsExplicitShape) |> SingleConstraint


//#nowarn "40"









//let typeOfPrimitiveLiteralValue : Cst.PrimitiveLiteralValue -> SingleTypeConstraint =
//    function
//    | Cst.NumberPrimitive num ->
//        match num with
//        | Cst.FloatLiteral _ -> Primitive Float
//        | Cst.IntLiteral _ -> Primitive Int
//    | Cst.CharPrimitive _ -> Primitive Char
//    | Cst.StringPrimitive _ -> Primitive String
//    | Cst.UnitPrimitive _ -> Unit
//    | Cst.BoolPrimitive _ -> Primitive Bool



//let rec typeOfExpression : NamesInScope -> Cst.Expression -> TypeCheckingInfo =
//    fun _ _ -> failwithf "Not implemented yet!"


///// @TODO: this should contain the logic to type check resolved named values
//and typeOfNamedValueIdentifier : NamesInScope -> Identifier -> TypeCheckingInfo =
//    fun resolvedNames ident ->
//        match ident with
//        | SingleValueIdentifier name ->
//            match ResolvedNames.tryFindValue name resolvedNames with
//            | Some (_, Value (_, expr)) -> typeOfExpression resolvedNames expr
//            | Some (_, Parameter _) -> Tci.succeed (Tci.Unified NotYetConstrained)
//            //makeGleanedInfo Unconstrained Map.empty
//            | None ->
//                SingleValueIdentifier name
//                |> Tci.UnresolvedName
//                |> Tci.succeed
//                |> Tci.addUnresolved (SingleValueIdentifier name)

//        //{ emptyGleanedInfo with
//        //    typeOfExpression = Unconstrained
//        //    namesNotResolved = Set.singleton (SingleValueIdentifier name) }

//        | TypeNameOrVariantOrTopLevelModule name ->
//            // I.e. it's a type constructor... I think

//            match ResolvedNames.tryFindTypeConstructor (UnqualType name) resolvedNames with
//            | Some (_, variantConstructor) ->
//                let paramsForVariant =
//                    variantConstructor.variantParams
//                    |> List.map getInferredTypeFromMentionableType

//                DtReferencedType (variantConstructor.typeName, paramsForVariant)
//                |> Tci.Constrained
//                |> Tci.Unified
//                |> Tci.succeed

//            //makeGleanedInfo (SingleConstraint inferredType) Map.empty

//            | None ->
//                TypeNameOrVariantOrTopLevelModule name
//                |> Tci.UnresolvedName
//                |> Tci.succeed
//                |> Tci.addUnresolved (TypeNameOrVariantOrTopLevelModule name)

//        //{ emptyGleanedInfo with
//        //    typeOfExpression = Unconstrained
//        //    namesNotResolved = Set.singleton (TypeNameOrVariantOrTopLevelModule name) }


//        | ModuleSegmentsOrQualifiedTypeOrVariant _ -> failwithf "Not implemented yet!"

//        | QualifiedPathValueIdentifier _ -> failwithf "Not implemented yet!"



////and typeOfSingleValueExpression : ResolvedNames -> Cst.SingleValueExpression -> GleanedInfo =
////    fun resolvedNames expr ->
////        match expr with
////        |





////and typeOfExplicitCompoundValue : ResolvedNames -> Cst.CompoundValues -> GleanedInfo =
//and typeOfExplicitCompoundValue : NamesInScope -> Cst.CompoundValues -> TypeCheckingInfo =
//    fun namesInScope compoundValue ->

//        //let rec listFolder items =
//        //    match items with
//        //    | [] -> emptyGleanedInfo
//        //    | head :: tail ->
//        //        let headConstraint = typeOfExpression namesInScope head

//        //        listFolder tail
//        //        |> combineGleanedInfos headConstraint

//        match compoundValue with
//        | Cst.List exprs -> exprs |> List.map Cst.getNode |> listFolder

//        | Cst.CompoundValues.Tuple list ->
//            list
//            |> TOM.map Cst.getNode
//            |> TOM.toList
//            |> listFolder

//        | Cst.CompoundValues.Record keyValList ->
//            let (keyAndValsConstraints, constrainedVars) =
//                keyValList
//                |> List.fold
//                    (fun (keyAndValsConstraints, vars) (key, value) ->
//                        let typeOfValue = typeOfExpression namesInScope value.node
//                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

//                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

//                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
//                    (List.empty, Map.empty)

//            let inferredType = keyAndValsConstraints |> Map.ofList |> RecordExact

//            makeGleanedInfo (SingleConstraint inferredType) constrainedVars

//        | Cst.CompoundValues.RecordExtension (recordToExtend, keyValList) ->
//            let (keyAndValsConstraints, constrainedVars) =
//                keyValList
//                |> NEL.toList
//                |> List.fold
//                    (fun (keyAndValsConstraints, vars) (key, value) ->
//                        let typeOfValue = typeOfExpression namesInScope value.node
//                        let newFieldAndValConstraint = (key.node, typeOfValue.typeOfExpression)

//                        let combinedVariables = combineConstrainedVars vars typeOfValue.variablesConstrained

//                        (newFieldAndValConstraint :: keyAndValsConstraints, combinedVariables))
//                    (List.empty, Map.empty)

//            let constraints = RecordWith (Map.ofList keyAndValsConstraints)

//            let thisType = SingleConstraint constraints

//            // Need to ensure that we're constraining the record being extended to be the same as the key/val constraints we've got here
//            Map.add (SingleValueIdentifier recordToExtend.node) thisType constrainedVars
//            |> makeGleanedInfo thisType


///// @TODO: hmmmm, this guy kinda needs to be able to bubble up constraints upwards, onto the parameter as a whole, based on the shape of the destructuring that we do to the parameters.
///// I think the way to do this is that each one of these guys needs to bubble up the sub-shapes inside of itself, and thereby informs the caller of this function what this specific assignment pattern is. Whether this function is called by a top level parameter or a destructured part of it doesn't matter, because the consequences of that will just be handled by whatever calls this function.
//let rec typeOfAssignmentPattern resolvedNames (assignmentPattern : Cst.AssignmentPattern) : GleanedInfo =
//    match assignmentPattern with
//    | Cst.Named _ -> makeGleanedInfo Unconstrained Map.empty
//    | Cst.Ignored -> makeGleanedInfo Unconstrained Map.empty
//    | Cst.Unit -> makeGleanedInfo (SingleConstraint Unit) Map.empty
//    | Cst.Aliased (pattern, alias) ->
//        let subType = typeOfAssignmentPattern resolvedNames pattern.node

//        { subType with
//            variablesConstrained =
//                Map.add (SingleValueIdentifier alias.node) subType.typeOfExpression subType.variablesConstrained }
//    | Cst.DestructuredPattern pattern -> typeOfDestructuredPattern resolvedNames pattern


//and typeOfDestructuredPattern (resolvedNames : NamesInScope) (pattern : Cst.DestructuredPattern) : GleanedInfo =
//    match pattern with
//    | Cst.DestructuredRecord fieldNames ->
//        let justTheFieldNames = fieldNames |> NEL.map Cst.getNode

//        let varConstraints : VariablesConstraints =
//            justTheFieldNames
//            |> NEL.map (fun fieldName -> SingleValueIdentifier fieldName, Unconstrained)
//            |> NEL.toList
//            |> Map.ofSeq

//        let extendedRecordType =
//            justTheFieldNames
//            |> NEL.map (fun fieldName -> fieldName, Unconstrained)
//            |> NEL.toList
//            |> Map.ofSeq
//            |> RecordWith

//        makeGleanedInfo (SingleConstraint extendedRecordType) varConstraints

//    | Cst.DestructuredTuple items ->
//        let gleaneds =
//            TOM.map
//                (Cst.getNode
//                 >> typeOfAssignmentPattern resolvedNames)
//                items

//        let combinedVars =
//            gleaneds
//            |> TOM.map getConstrainedVars
//            |> TOM.fold<_, _> combineConstrainedVars Map.empty

//        let inferredType =
//            Tuple (TOM.map getTypeInfo gleaneds)
//            |> SingleConstraint

//        makeGleanedInfo inferredType combinedVars


//    | Cst.DestructuredCons items ->
//        let gleaneds =
//            TOM.map
//                (Cst.getNode
//                 >> typeOfAssignmentPattern resolvedNames)
//                items

//        let combinedVars =
//            gleaneds
//            |> TOM.map getConstrainedVars
//            |> TOM.fold<_, _> combineConstrainedVars Map.empty

//        let constraints =
//            TOM.map getTypeInfo gleaneds
//            |> TOM.fold<_, _> combineTypeConstraints Unconstrained

//        let inferredType = List constraints

//        makeGleanedInfo (SingleConstraint inferredType) combinedVars

//    | Cst.DestructuredTypeVariant (constructor, params_) ->
//        let resolvedConstructor =
//            ResolvedNames.tryFindTypeConstructor constructor.node resolvedNames
//            |> Option.map snd

//        match resolvedConstructor with
//        | Some constructor ->
//            // @TODO: need to ensure here that the number of assignment params from the variant constructor pattern matches that actual number of params in the variant constructor definition!
//            let typesOfParams =
//                params_
//                |> List.map (
//                    Cst.getNode
//                    >> typeOfAssignmentPattern resolvedNames
//                )

//            //let (_, typeOfConstructor) =
//            //    ResolvedNames.findTypeDeclaration constructor.typeName resolvedNames

//            { emptyGleanedInfo with
//                typeOfExpression = typeOfConstructor
//                variablesConstrained = [ constructor.typeName ] }
//        | None ->
//            { emptyGleanedInfo with
//                namesNotResolved =
//                    Set.singleton
//                    <| convertTypeOrModuleIdentifierToIdentifier constructor.node }

////failwithf "Implement this!"



//type AppliedGenericsMap = Map<RigidGeneric, DefinitiveType>

////let applyGenerics (resolvedNames : ResolvedNames)

















//type TypeState =
//    { inferState : TypeConstraints
//      /// The type declaration for the value
//      typeDeclaration : SingleTypeConstraint option }





//type SimpleJudgment<'a> =
//    | SimpleUnconstrained
//    | SimpleUnified of 'a
//    | SimpleConflicting of 'a tom




///// This will probably be used in a nested way for each of the parameters of a type that has type parameters, to achieve gradual typing of its fields
//type TypeJudgment<'a> =
//    /// `unifiedType` will be `None` if the value is unconstrained
//    | Unified of unifiedType : SingleTypeConstraint option
//    /// Conflicts between inferred types
//    | ConflictingInferences of typeDeclaration : SingleTypeConstraint option * inferences : SingleTypeConstraint tom
//    /// Conflict between declared type and the one otherwise unified inferred type
//    | ConflictDeclarationInferences of declaredType : SingleTypeConstraint * unifiedInferredTypes : SingleTypeConstraint
//    /// Conflict both between declared type and also among the inferred types
//    | ConflictDeclarationAndBetweenInferences of
//        declaredType : SingleTypeConstraint *
//        inferredTypes : SingleTypeConstraint tom



///// Dear lord this is a big one - and doesn't even contain the actual unifier logic
///// But, ultimately this is the function that will let us do the type judgment on multiple type constraints!
//let tryUnifyTypes
//    (unifier : SimpleJudgment<SingleTypeConstraint> -> SingleTypeConstraint -> SimpleJudgment<SingleTypeConstraint>)
//    (typeState : TypeState)
//    : TypeJudgment<'a> =
//    match typeState.typeDeclaration with
//    | None ->
//        match typeState.inferState with
//        | Unconstrained -> Unified None
//        | SingleConstraint constr -> Unified (Some constr)
//        | MultipleConstraints constraints ->
//            match TOM.fold<SimpleJudgment<SingleTypeConstraint>, SingleTypeConstraint>
//                      unifier
//                      SimpleUnconstrained
//                      constraints
//                with
//            | SimpleUnconstrained -> Unified None
//            | SimpleUnified unifiedInferredConstraint -> Unified (Some unifiedInferredConstraint)
//            | SimpleConflicting clashes -> ConflictingInferences (None, clashes)

//    | Some declaration ->
//        match typeState.inferState with
//        | Unconstrained -> Unified (Some declaration)
//        | SingleConstraint constr ->
//            match unifier (SimpleUnified constr) declaration with
//            | SimpleUnconstrained -> Unified (Some declaration)
//            | SimpleUnified unified -> Unified (Some unified)
//            | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, constr)

//        | MultipleConstraints constraints ->
//            match TOM.fold<_, _> unifier SimpleUnconstrained constraints with
//            | SimpleUnconstrained -> Unified (Some declaration)
//            | SimpleUnified unifiedInferreds ->
//                match unifier (SimpleUnified unifiedInferreds) declaration with
//                | SimpleUnconstrained -> Unified (Some declaration)
//                | SimpleUnified fullyUnified -> Unified (Some fullyUnified)
//                | SimpleConflicting _ -> ConflictDeclarationInferences (declaration, unifiedInferreds)

//            | SimpleConflicting clashes -> ConflictingInferences (Some declaration, clashes)

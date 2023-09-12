module TypedSyntaxTree



open QualifiedSyntaxTree.Names

module S = SyntaxTree
module C = ConcreteSyntaxTree
module Q = QualifiedSyntaxTree



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
type TypeConstraintId = | TypeConstraintId of System.Guid


let makeTypeConstrId () =
    System.Guid.NewGuid () |> TypeConstraintId





type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Bool




/// Represents a correct type without clashes
and DefinitiveType =
    | DtUnitType
    | DtPrimitiveType of BuiltInPrimitiveTypes
    | DtTuple of TypeConstraints tom
    | DtList of TypeConstraints
    /// I think we need to pass in a type param to the extended record, so that not including one is a type error
    | DtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraints>
    | DtRecordExact of Map<RecordFieldName, TypeConstraints>
    /// This guy will only be able to be assigned at the root of a file once we have the types on hand to resolve them and assign
    | DtNewType of typeName : UpperNameValue * typeParams : TypeConstraints list
    | DtArrow of fromType : TypeConstraints * toType : TypeConstraints






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


    /// I.e. must be the type that this constructor is a variant of; when given constructor params this will look like a `DtArrow`.
    /// Technically if this is present in a TypeConstraints it implies that either the definitive type is a NewType (or still an incomplete Arrow), but that can be merged at the module level once we have names and constructors to resolve.
    | ByConstructorType of ctor : UpperNameValue


    // From here onwards are the constraints that are derived from a type expressions. The ones above are derived from value expressions.

    /// I.e. must be the same type as this type param
    | ByTypeParam of LowerIdent

//| IsOfTypeByName of typeName : UpperNameValue * typeParams : TypeConstraints list


///// A more limited reference constraint, only for value expressions
//and ValRefConstr =
//    | RefByVal of LowerNameValue
//    | BoundRef of TypeConstraintId


/// Contains the definitive constraints that have been inferred so far, plus any other value or type param constraints that have not been evaluated yet.
/// If a `RefConstr` turns out to be incompatible with the existing definitive type, this will be transformed into a `TypeJudgment` with the incompatible definitive types listed in the `Error` case.
and TypeConstraints =
    | Constrained of definitive : DefinitiveType option * otherConstraints : RefConstr set


    /// Makes a new TypeConstraints which is truly empty
    static member empty = Constrained (None, Set.empty)

    /// Makes a new TypeConstraints which is empty of specific, but still has a Guid so as not to lose links required between the thing that is assigned this constraint and anything else it is linked to
    static member makeUnspecific () =
        Constrained (None, Set.singleton (IsBoundVar (makeTypeConstrId ())))

    static member fromDefinitive (def : DefinitiveType) : TypeConstraints = Constrained (Some def, Set.empty)

    static member fromConstraint (constr : RefConstr) : TypeConstraints =
        Constrained (None, Set.singleton constr)



//static member bind f constraints =
//    match constraints with
//    | Recursive -> Recursive
//    | Constrained (defOpt,  set) ->




type Param =
    { //tokens : TokenWithSource list
      destructurePath : PathToDestructuredName }


and TypeError =
    | IncompatibleTypes of DefinitiveType list
    | UnprunedRecursion

    static member fromTypes types = IncompatibleTypes types



/// @TODO: this should really also contain the other `ConstrainType`s, in case some of them also get evaluated to incompatible definitive types
and TypeJudgment = Result<TypeConstraints, TypeError>








/// Basically the same as a T.DefinitiveType but with guids referencing other types in the Acc instead of their own TypeConstraints
type RefDefType =
    | RefDtUnitType
    | RefDtPrimitiveType of BuiltInPrimitiveTypes
    | RefDtTuple of TypeConstraintId tom
    | RefDtList of TypeConstraintId
    | RefDtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraintId>
    | RefDtRecordExact of Map<RecordFieldName, TypeConstraintId>
    | RefDtNewType of typeName : UpperNameValue * typeParams : TypeConstraintId list
    | RefDtArrow of fromType : TypeConstraintId * toType : TypeConstraintId



type AccTypeError = | DefTypeClash of RefDefType * RefDefType


/// Helper type for accumulating type constraints
type Accumulator = Map<RefConstr set, Result<RefDefType option, AccTypeError>>











/// Attempt at making accumulator working by using two internal maps, one where every single def type gets a guid assigned to it, and every ref constraint gets placed in a set with its others, which points to a guid, which in turn may have a def type assigned to it.
type Accumulator2
// electric boogaloo
 =
    { refConstraintsMap : Map<RefConstr set, TypeConstraintId>
      dataMap : Map<TypeConstraintId, Result<RefDefType, AccTypeError>> }

    static member empty =
        { refConstraintsMap = Map.empty
          dataMap = Map.empty }


    member this.getAlignedConstraints (constr : RefConstr) : RefConstr set option =
        this.refConstraintsMap
        |> Map.tryPick (fun key _ ->
            if Set.contains constr key then
                Some key
            else
                None)

    member this.getConstraintIdByRefConstr (constr : RefConstr) : TypeConstraintId option =
        let key = this.getAlignedConstraints constr
        Option.bind (fun k -> Map.tryFind k this.refConstraintsMap) key


    /// @TODO: still probably need to rework the dataMap so that it stores only defTypeResults - the no def type case is represented by there just not being a keyval in the dataMap for the given typeConstraintId
    member this.getDefByConstr (constr : RefConstr) =
        let key = this.getConstraintIdByRefConstr constr
        Option.bind (fun k -> Map.tryFind k this.dataMap) key

    member this.addTypeConstraints (tcRef : RefConstr) (tc : TypeConstraints) =
        let newKey = makeTypeConstrId ()

        let (Constrained (defOpt, refs)) = tc
        let refsFromTypeAndSelf = Set.add tcRef refs

        // Need to roll up the maps, first the refConstr map, and combine whichever ref constr sets are now to be combined - and where refs are to be combined, def types are indeed to be unified; which probably requires resolving the def types stored under constraint IDs and trying to unify those in turn, which also probably means regenerating constraint IDs, deleting the old ones under the old constraint IDs, and inserting new ones, containing the new unified definitive types!



        let hasOverlap a b = Set.union a b |> Set.isNotEmpty

        let shouldRefsKeyBeReplaced mapRefsKey =
            hasOverlap refsFromTypeAndSelf mapRefsKey



        let refConstraintsAndConstraintIdsToReplace =
            this.refConstraintsMap
            |> Map.fold
                (fun constrsAndIds key value ->
                    if shouldRefsKeyBeReplaced key then
                        (refsFromTypeAndSelf, value) :: constrsAndIds
                    else
                        constrsAndIds)
                List.empty

        let newRefsKey =
            refConstraintsAndConstraintIdsToReplace
            |> List.map fst
            |> Set.unionMany

        let constraintIdsToReplace =
            refConstraintsAndConstraintIdsToReplace
            |> List.map snd

        let newRefConstraintsMap =
            refConstraintsAndConstraintIdsToReplace
            |> List.fold
                (fun map (refConstraints, constrId) ->
                    Map.combineManyKeys (hasOverlap refConstraints) (fun _ -> refConstraints, constrId) map)
                this.refConstraintsMap



        let newDataMap =
            constraintIdsToReplace
            |> List.choose (fun constrId -> Map.tryFind constrId this.dataMap)
            |> Result.sequenceList
            |> Result.map (fun refDefs ->
                // @TODO: try to unify the refDefs - will likely need to do it recursively, with possibly needing to run multiple passes on unifying refDefs and then unifying the things referred to with constraint IDs - although that might mean that I also need to allow for constraint IDs to link to reference constraints, not only the other way around
                ())


        { refConstraintsMap = newRefConstraintsMap
          dataMap = newDataMap }



    member this.unifyRefDefTypes (replaceIdsWithIdAndType : TypeConstraintId list -> unit) a b = []




(* Name dictionaries *)










//type MentionableType =
//    | UnitType
//    | GenericTypeVar of LowerNameValue
//    | Tuple of TupleType
//    | Record of RecordType
//    | ExtendedRecord of ExtendedRecordType
//    | ReferencedType of typeName : UpperNameValue * typeParams : MentionableType list
//    | Arrow of fromType : MentionableType * toType : NEL<MentionableType>
//    | Parensed of MentionableType



///// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
//and TupleType = { types : MentionableType tom }


//and RecordType =
//    { fields : Map<RecordFieldName, MentionableType> }

///// @TODO: as said above at MentionableType, we may need separate versions of this for value type annotations vs for use in type declarations; because in the former free type variables are allowed, but in the latter they are not.
//and ExtendedRecordType =
//    { extendedAlias : LowerIdent // Because it has to be a type param
//      fields : Map<RecordFieldName, MentionableType> }





type VariantCase =
    { label : UpperIdent
      contents : TypeConstraints list }




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
    { associativity : S.InfixOpAssociativity
      precedence : int
      /// The value should be a function taking exactly two parameters
      value : TypedExpr }


and VariantConstructor =
    { typeParamsList : LowerIdent list // So as to not lose track of the order of the type params
      typeParamsMap : TypeParams
      variantCase : VariantCase
      allVariants : NEL<VariantCase>
      typeName : UpperIdent }



and LowerCaseName =
    | LocalName of LetBinding
    | Param of Param
    | TopLevelName of TypedExpr // ValueDeclaration -- This really only carried a TypedExpr anyway, so why stick it in a special wrapper record type







and TypeDeclaration =
    { typeParamsMap : TypeParams
      typeParamsList : LowerIdent list
      typeDeclaration : TypeDeclarationContent }







/// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
and LetBinding =
    { paramPattern : AssignmentPattern
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
      assignedExpression : TypedExpr

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
    | List of TypedExpr list
    | Tuple of TypedExpr tom
    | Record of (RecordFieldName * TypedExpr) list
    | RecordExtension of recordToExtend : LowerIdent * additions : NEL<RecordFieldName * TypedExpr>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParam nel
      body : TypedExpr }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of S.PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : RecordFieldName




and ControlFlowExpression =
    | IfExpression of condition : TypedExpr * ifTrue : TypedExpr * ifFalse : TypedExpr
    | CaseMatch of exprToMatch : TypedExpr * branches : CaseMatchBranch nel

and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | UpperIdentifier of name : UpperNameValue
    | LowerIdentifier of name : LowerNameValue
    | LetExpression of namedValues : LetBindings * expr : TypedExpr
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : TypedExpr * op : OperatorIdent * right : TypedExpr
    | FunctionApplication of funcExpr : TypedExpr * params' : NEL<TypedExpr>
    | DotAccess of expr : TypedExpr * dotSequence : NEL<RecordFieldName>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParam
      body : TypedExpr }


and SingleOrCompoundExpr =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and TypedExpr = { expr : SingleOrCompoundExpr }



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
      values : Map<LowerIdent, SOD<TypedExpr>>
      infixOperators : Map<LowerIdent, SOD<DeclaredInfixOp>> }

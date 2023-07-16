module TypedSyntaxTree



open QualifiedSyntaxTree.Names

module S = SyntaxTree
module Q = QualifiedSyntaxTree



type DestructuredPattern =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of LowerIdent nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of AssignmentPattern tom
    | DestructuredCons of AssignmentPattern tom
    | DestructuredTypeVariant of constructor : UpperIdent * params' : AssignmentPattern list

/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of ident : LowerIdent
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of pattern : AssignmentPattern * alias : LowerIdent








type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Bool


/// Represents a correct type without clashes
type DefinitiveType =
    | DtUnitType
    | DtPrimitiveType of BuiltInPrimitiveTypes
    | DtTuple of TypeConstraints tom
    | DtList of TypeConstraints
    | DtRecordWith of referencedFields : Map<RecordFieldName, TypeConstraints>
    | DtRecordExact of Map<RecordFieldName, TypeConstraints>
    | DtReferencedType of typeName : UpperIdent * typeParams : TypeConstraints list
    | DtArrow of fromType : TypeConstraints * toTypes : TypeConstraints nel




//and InferredType =
//    /// It being one or more captures the fact that multiple parameters or values may need to have the same type, regardless of what the specific type is
//    | Constrained of ConstrainType set
//    | Definitive of DefinitiveType



and ConstrainType =
    /// I.e. must be the same type as this value
    | ByValue of LowerIdent
    /// I.e. must be the same type as this type param
    | ByTypeParam of LowerIdent
    /// I.e. must be the type that this constructor is a variant of
    | ByConstructorType of UpperIdent



/// Contains the definitive constraints that have been inferred so far, plus any other value or type param constraints that have not been evaluated yet.
/// If a `ConstrainType` turns out to be incompatible with the existing definitive type, this will be transformed into a `TypeJudgment` with the incompatible definitive types listed in the `Error` case.
and TypeConstraints = | TypeConstraints of definitive : DefinitiveType option * otherConstraints : ConstrainType set




type Param =
    { //tokens : TokenWithSource list
      destructurePath : PathToDestructuredName
      /// Inferred through usage. If the param has a type annotation that will be a separate field.
      inferredType : TypeConstraints }



/// @TODO: this should really also contain the other `ConstrainType`s, in case some of them also get evaluated to incompatible definitive types
type TypeJudgment = Result<TypeConstraints, DefinitiveType list>





(* Name dictionaries *)










type MentionableType =
    | UnitType
    | GenericTypeVar of LowerIdent
    | Tuple of TupleType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : UpperIdent * typeParams : MentionableType list
    | Arrow of fromType : MentionableType * toType : NEL<MentionableType>
    | Parensed of MentionableType



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType = { types : MentionableType tom }


and RecordType =
    { fields : Map<RecordFieldName, MentionableType> }

/// @TODO: as said above at MentionableType, we may need separate versions of this for value type annotations vs for use in type declarations; because in the former free type variables are allowed, but in the latter they are not.
and ExtendedRecordType =
    { extendedAlias : LowerIdent // Because it has to be a type param
      fields : Map<RecordFieldName, MentionableType> }





type VariantCase =
    { label : UpperIdent
      contents : MentionableType list }




type TypeDeclarationContent =
    | Sum of variants : NEL<VariantCase>
    | Alias of referent : MentionableType








(* Dictionaries of declared names *)

type TypeDeclarations = Map<UpperIdent, TypeDeclaration>

and TypeConstructors = Map<UpperIdent, VariantConstructor>

and ValueDeclarations = Map<LowerIdent, LowerCaseName>

and ValueTypeDeclarations = Map<LowerIdent, ValueAnnotation>

and TypeParams = Map<LowerIdent, unit>






and VariantConstructor =
    { typeParamsList : LowerIdent list // So as to not lose track of the order of the type params
      typeParamsMap : TypeParams
      variantCase : VariantCase
      allVariants : NEL<VariantCase> }



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
    //{ tokens : TokenWithSource list
    { destructurePath : PathToDestructuredName

      (*
      @TODO: we need to take into account the assignment pattern here so that we can:
        a) add the type constraints implied by that pattern, and
        b) partially evaluate or slice up the expression so that we're assigning the right sub-expressions to the right names

      Although tbh evaluation of the assigned expression might not be straightforward, so maybe it is best to have something here to represent the fact that:
        a) we've only got one expression we're evaluating per binding (and so not doing the duplicate work of evaluating the expression once for every named value in the assignment pattern), and
        b) for each named value, what path to take in that expression to get the slice of the expression that should be assigned to it, e.g. a tuple, type destructuring, etc.
      *)
      assignedExpression : TypedExpr }




and LetDeclarationNames = Map<LowerIdent, LetBinding>

/// Represents all the named params in a single function parameter or case match expression
and FunctionOrCaseMatchParam =
    { paramPattern : AssignmentPattern
      namesMap : Map<LowerIdent, Param>
      inferredType : TypeConstraints }




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
    | LetExpression of namedValues : LetDeclarationNames * expr : TypedExpr
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : TypedExpr * op : Operator * right : TypedExpr
    | FunctionApplication of funcExpr : TypedExpr * params' : NEL<TypedExpr>
    | DotAccess of expr : TypedExpr * dotSequence : NEL<RecordFieldName>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParam
      body : TypedExpr }


and SingleOrCompoundExpr =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and TypedExpr =
    { inferredType : TypeJudgment
      expr : SingleOrCompoundExpr }



and Operator =
    | BuiltInOp of Lexer.BuiltInOperator
    | OtherOp of ident : LowerIdent



//and ValueDeclaration =
//    { //valueName : LowerIdent
//      value : TypedExpr }



and ValueAnnotation =
    { valueName : LowerIdent
      /// these aren't in the source code, but they're gathered from the type expression implicitly
      gatheredImplicitParams : TypeParams
      annotatedType : MentionableType }







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
      values : Map<LowerIdent, TypedExpr> }

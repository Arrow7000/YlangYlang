module TypedSyntaxTree


open Lexer
open QualifiedSyntaxTree.Names

module S = SyntaxTree
module Q = QualifiedSyntaxTree





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
    | DtReferencedType of typeName : ResolvedType * typeParams : TypeConstraints list
    | DtArrow of fromType : TypeConstraints * toTypes : TypeConstraints nel




//and InferredType =
//    /// It being one or more captures the fact that multiple parameters or values may need to have the same type, regardless of what the specific type is
//    | Constrained of ConstrainType set
//    | Definitive of DefinitiveType



and ConstrainType =
    /// I.e. must be the same type as this value
    | ByValue of ResolvedValue
    /// I.e. must be the same type as this type param
    | ByTypeParam of ResolvedTypeParam



/// Contains the definitive constraints that have been inferred so far, plus any other value or type param constraints that have not been evaluated yet.
/// If a `ConstrainType` turns out to be incompatible with the existing definitive type, this will be transformed into a `TypeJudgment` with the incompatible definitive types listed in the `Error` case.
and TypeConstraints = | TypeConstraints of definitive : DefinitiveType option * otherConstraints : ConstrainType set




type Param =
    { ident : LowerIdent
      tokens : TokenWithSource list
      destructurePath : PathToDestructuredName
      /// Inferred through usage. If the param has a type annotation that will be a separate field.
      inferredType : TypeConstraints }



/// @TODO: this should really also contain the other `ConstrainType`s, in case some of them also get evaluated to incompatible definitive types
type TypeJudgment = Result<TypeConstraints, DefinitiveType list>








type MentionableType =
    | UnitType
    | GenericTypeVar of ResolvedTypeParam
    | Tuple of TupleType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : ResolvedType * typeParams : S.CstNode<MentionableType> list
    | Arrow of fromType : S.CstNode<MentionableType> * toType : NEL<S.CstNode<MentionableType>>
    | Parensed of S.CstNode<MentionableType>



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType =
    { types : S.CstNode<MentionableType> tom }


and RecordType =
    { fields : Map<S.CstNode<RecordFieldName>, S.CstNode<MentionableType>> }

/// @TODO: as said above at MentionableType, we may need separate versions of this for value type annotations vs for use in type declarations; because in the former free type variables are allowed, but in the latter they are not.
and ExtendedRecordType =
    { extendedAlias : S.CstNode<ResolvedTypeParam> // Because it has to be a type param
      fields : Map<S.CstNode<RecordFieldName>, S.CstNode<MentionableType>> }





type VariantCase =
    { label : ResolvedTypeConstructor * S.CstNode<UpperIdent>
      contents : S.CstNode<MentionableType> list }




type TypeDeclarationContent =
    | Sum of variants : NEL<S.CstNode<VariantCase>>
    | Alias of referent : S.CstNode<MentionableType>


type TypeDeclaration =
    { typeParamsMap : Q.ResolvedTypeParams
      typeParamsList : ResolvedTypeParam list
      typeDeclaration : TypeDeclarationContent }







/// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
type ResolvedLetBinding =
    { ident : LowerIdent
      tokens : TokenWithSource list
      destructurePath : PathToDestructuredName

      (*
      @TODO: we need to take into account the assignment pattern here so that we can:
        a) add the type constraints implied by that pattern, and
        b) partially evaluate or slice up the expression so that we're assigning the right sub-expressions to the right names

      Although tbh evaluation of the assigned expression might not be straightforward, so maybe it is best to have something here to represent the fact that:
        a) we've only got one expression we're evaluating per binding (and so not doing the duplicate work of evaluating the expression once for every named value in the assignment pattern), and
        b) for each named value, what path to take in that expression to get the slice of the expression that should be assigned to it, e.g. a tuple, type destructuring, etc.
      *)
      assignedExpression : TypedExpr }




and LetDeclarationNames = Map<ResolvedValue, ResolvedLetBinding>

/// Represents all the named params in a single function parameter or case match expression
and FunctionOrCaseMatchParam =
    { paramPattern : Q.AssignmentPattern
      namesMap : Map<ResolvedValue, Param>
      inferredType : TypeConstraints }




and CompoundValues =
    | List of S.CstNode<TypedExpr> list
    | Tuple of S.CstNode<TypedExpr> tom
    | Record of (S.CstNode<RecordFieldName> * S.CstNode<TypedExpr>) list
    | RecordExtension of
        recordToExtend : (ResolvedValue * S.CstNode<LowerIdent>) *
        additions : NEL<S.CstNode<RecordFieldName> * S.CstNode<TypedExpr>>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParam nel
      body : S.CstNode<TypedExpr> }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of S.PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : RecordFieldName




and ControlFlowExpression =
    | IfExpression of condition : S.CstNode<TypedExpr> * ifTrue : S.CstNode<TypedExpr> * ifFalse : S.CstNode<TypedExpr>
    | CaseMatch of exprToMatch : S.CstNode<TypedExpr> * branches : CaseMatchBranch nel

and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | UpperIdentifier of fullyQualifiedName : FullyQualifiedUpperIdent * resolved : ResolvedTypeConstructor
    | LowerIdentifier of name : LowerNameValue * resolved : ResolvedValue
    | LetExpression of namedValues : LetDeclarationNames * expr : TypedExpr
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : S.CstNode<TypedExpr> * op : S.CstNode<Q.Operator> * right : S.CstNode<TypedExpr>
    | FunctionApplication of funcExpr : S.CstNode<TypedExpr> * params' : NEL<S.CstNode<TypedExpr>>
    | DotAccess of expr : S.CstNode<TypedExpr> * dotSequence : S.CstNode<NEL<RecordFieldName>>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParam
      body : S.CstNode<TypedExpr> }


and SingleOrCompoundExpr =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and TypedExpr =
    { inferredType : TypeJudgment
      expr : SingleOrCompoundExpr }





type ValueDeclaration =
    { valueName : S.CstNode<LowerIdent>
      value : S.CstNode<TypedExpr> }



type ValueAnnotation =
    { valueName : S.CstNode<LowerIdent>
      /// these aren't in the source code, but they're gathered from the type expression implicitly
      gatheredImplicitParams : Q.ResolvedTypeParams
      annotatedType : S.CstNode<MentionableType> }







type Declaration =
    | ImportDeclaration of S.ImportDeclaration
    | TypeDeclaration of resolved : ResolvedType * name : S.CstNode<UpperIdent> * declaration : TypeDeclaration
    | ValueTypeAnnotation of resolved : ResolvedValue * ValueAnnotation
    | ValueDeclaration of resolved : ResolvedValue * ValueDeclaration


// Representing a whole file/module
type YlModule =
    { moduleDecl : S.ModuleDeclaration
      imports : S.ImportDeclaration list
      types : Map<ResolvedType, UpperIdent * TypeDeclaration>
      valueTypes : Map<ResolvedValue, LowerIdent * ValueAnnotation>
      values : Map<ResolvedValue, LowerIdent * ValueDeclaration> }

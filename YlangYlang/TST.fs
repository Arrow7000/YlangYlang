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
    | DtTuple of InferredType tom
    | DtList of InferredType
    | DtRecordWith of referencedFields : Map<RecordFieldName, InferredType>
    | DtRecordExact of Map<RecordFieldName, InferredType>
    | DtReferencedType of typeName : ResolvedType * typeParams : InferredType list
    | DtArrow of fromType : InferredType * toTypes : InferredType nel




and InferredType =
    /// It being one or more captures the fact that multiple parameters or values may need to have the same type, regardless of what the specific type is
    | Constrained of ConstrainType set // not sure yet if it's only values that things can be linked to or other things also, like type params
    | Definitive of DefinitiveType


and ConstrainType =
    | ByValue of ResolvedValue
    | ByTypeParam of ResolvedTypeParam



type Param =
    { ident : LowerIdent
      tokens : TokenWithSource list
      destructurePath : PathToDestructuredName
      inferredType : InferredType }




/// This describes the strictest type constraint that an expression needs to be, but no stricter!
type TypeJudgment = Result<InferredType, DefinitiveType list>








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
      /// This expression is actually the whole expression after the assignment, not just the bit that was destructured to this named identifier; that will have to be implemented at the type checking phase
      assignedExpression : TypedExpr }




and LetDeclarationNames = Map<ResolvedValue, ResolvedLetBinding>

/// Represents all the named params in a single function parameter or case match expression
and FunctionOrCaseMatchParams =
    { paramPattern : Q.AssignmentPattern
      namesMap : Map<ResolvedValue, Param>
      inferredType : InferredType }




and CompoundValues =
    | List of S.CstNode<TypedExpr> list
    | Tuple of S.CstNode<TypedExpr> tom
    | Record of (S.CstNode<RecordFieldName> * S.CstNode<TypedExpr>) list
    | RecordExtension of
        recordToExtend : S.CstNode<ResolvedValue * LowerIdent> *
        additions : NEL<S.CstNode<RecordFieldName> * S.CstNode<TypedExpr>>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParams nel
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
    | Operator of left : S.CstNode<TypedExpr> * opSequence : NEL<S.CstNode<Lexer.Operator> * S.CstNode<TypedExpr>>
    | FunctionApplication of funcExpr : S.CstNode<TypedExpr> * params' : NEL<S.CstNode<TypedExpr>>
    | DotAccess of expr : S.CstNode<TypedExpr> * dotSequence : S.CstNode<NEL<RecordFieldName>>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParams
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

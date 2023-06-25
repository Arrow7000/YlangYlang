module TypedSyntaxTree


open Lexer
open QualifiedSyntaxTree.Names
open System

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
    | DtReferencedType of typeName : ResolvedTypeName * typeParams : InferredType list
    | DtArrow of fromType : InferredType * toType : InferredType




and InferredType =
    /// It being one or more captures the fact that multiple parameters or values may need to have the same type, regardless of what the specific type is
    | Unconstrained of Guid set
    | Constrained of DefinitiveType



/// This describes the strictest type constraint that an expression needs to be, but no stricter!
type TypeJudgment = Result<InferredType, DefinitiveType list>










type MentionableType =
    | UnitType
    | GenericTypeVar of ResolvedTypeParam
    | Tuple of TupleType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : ResolvedTypeName * typeParams : S.CstNode<MentionableType> list
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
    { label : S.CstNode<UpperIdent>
      contents : S.CstNode<MentionableType> list }

/// I.e. a sum type
type NewTypeDeclaration =
    { typeParams : Q.ResolvedTypeParams
      variants : NEL<S.CstNode<VariantCase>> }


type AliasDeclaration =
    { typeParams : Q.ResolvedTypeParams
      referent : S.CstNode<MentionableType> }


type TypeDeclaration =
    | Alias of AliasDeclaration
    | Sum of NewTypeDeclaration








/// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
type ResolvedLetBinding =
    { ident : LowerIdent
      tokens : TokenWithSource list
      destructurePath : PathToDestructuredName
      /// This expression is actually the whole expression after the assignment, not just the bit that was destructured to this named identifier; that will have to be implemented at the type checking phase
      assignedExpression : Expression }




and LetDeclarationNames = Map<ResolvedLower, ResolvedLetBinding>

and FunctionOrCaseMatchParams = Map<ResolvedLower, LowerIdent * PathToDestructuredName * TokenWithSource list>




and CompoundValues =
    | List of S.CstNode<Expression> list
    | Tuple of S.CstNode<Expression> tom
    | Record of (S.CstNode<LowerIdent> * S.CstNode<Expression>) list
    | RecordExtension of
        recordToExtend : S.CstNode<LowerIdent> *
        additions : NEL<S.CstNode<LowerIdent> * S.CstNode<Expression>>


and FunctionValue =
    { params_ : FunctionOrCaseMatchParams
      body : S.CstNode<Expression> }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of S.PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : LowerIdent




and ControlFlowExpression =
    | IfExpression of
        condition : S.CstNode<Expression> *
        ifTrue : S.CstNode<Expression> *
        ifFalse : S.CstNode<Expression>
    | CaseMatch of exprToMatch : S.CstNode<Expression> * branches : CaseMatchBranch nel

and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | UpperIdentifier of fullyQualifiedName : FullyQualifiedUpperIdent * resolved : ResolvedTypeConstructor
    | LowerIdentifier of name : LowerNameValue * resolved : ResolvedLower
    | LetExpression of namedValues : LetDeclarationNames * expr : Expression
    | ControlFlowExpression of ControlFlowExpression




and CompoundExpression =
    | Operator of left : S.CstNode<Expression> * opSequence : NEL<S.CstNode<Lexer.Operator> * S.CstNode<Expression>>
    | FunctionApplication of funcExpr : S.CstNode<Expression> * params' : NEL<S.CstNode<Expression>>
    | DotAccess of expr : S.CstNode<Expression> * dotSequence : S.CstNode<NEL<LowerIdent>>


and CaseMatchBranch =
    { matchPattern : FunctionOrCaseMatchParams
      body : S.CstNode<Expression> }


and SingleOrCompoundExpr =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression


/// A typed expression
and Expression =
    { inferredType : TypeJudgment
      expr : SingleOrCompoundExpr }





type ValueDeclaration =
    { valueName : S.CstNode<LowerIdent>
      value : S.CstNode<Expression> }



type ValueAnnotation =
    { valueName : S.CstNode<LowerIdent>
      /// these aren't in the source code, but they're gathered from the type expression implicitly
      gatheredImplicitParams : Q.ResolvedTypeParams
      annotatedType : S.CstNode<MentionableType> }







type Declaration =
    | ImportDeclaration of S.ImportDeclaration
    | TypeDeclaration of name : S.CstNode<UpperIdent> * declaration : TypeDeclaration
    | ValueTypeAnnotation of ValueAnnotation
    | ValueDeclaration of ValueDeclaration


// Representing a whole file/module
type YlModule =
    { moduleDecl : S.ModuleDeclaration
      imports : S.ImportDeclaration list
      types : Map<ResolvedTypeName, UpperIdent * TypeDeclaration>
      values : Map<ResolvedLower, LowerIdent * EitherOrBoth<ValueAnnotation, ValueDeclaration>> }

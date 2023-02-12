module ConcreteSyntaxTree

open Lexer


/// Structure to contain both a CST node and reference to the parsed tokens and source text
type CstNode<'a> =
    { node : 'a
      source : TokenWithSource list }


let makeCstNode node source = { node = node; source = source }


let getNode { node = node } = node

let mapNode f node =
    { source = node.source
      node = f node.node }

(* Names and identifiers *)




type DestructuredPattern =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of CstNode<UnqualValueIdentifier> nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of first : CstNode<AssignmentPattern> * tail : CstNode<AssignmentPattern> nel
    | DestructuredCons of first : CstNode<AssignmentPattern> * tail : CstNode<AssignmentPattern> nel
    | DestructuredTypeVariant of
        constructor : CstNode<TypeOrModuleIdentifier> *
        params' : CstNode<AssignmentPattern> list



/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of UnqualValueIdentifier
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of pattern : CstNode<AssignmentPattern> * alias : CstNode<UnqualValueIdentifier>










(* Types *)

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
type MentionableType =
    | UnitType
    | GenericTypeVar of UnqualValueIdentifier
    | Tuple of TupleType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : CstNode<TypeOrModuleIdentifier> * typeParams : CstNode<MentionableType> list
    | Arrow of fromType : CstNode<MentionableType> * toType : NEL<CstNode<MentionableType>>
    | Parensed of CstNode<MentionableType>



and TupleType =
    { /// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
      types : CstNode<MentionableType> * NEL<CstNode<MentionableType>> }


and RecordType =
    { fields : Map<CstNode<UnqualValueIdentifier>, CstNode<MentionableType>> }

and ExtendedRecordType =
    { extendedAlias : CstNode<UnqualValueIdentifier>
      fields : Map<CstNode<UnqualValueIdentifier>, CstNode<MentionableType>> }

type VariantCase =
    { label : CstNode<UnqualTypeOrModuleIdentifier>
      contents : CstNode<MentionableType> list }


type TypeDeclaration =
    | Alias of
        name : CstNode<UnqualTypeOrModuleIdentifier> *
        specifiedTypeParams : CstNode<UnqualValueIdentifier> list *  // in case the underlying type needs it
        referent : CstNode<MentionableType>
    | Sum of
        name : CstNode<UnqualTypeOrModuleIdentifier> *
        specifiedTypeParams : CstNode<UnqualValueIdentifier> list *
        variants : NEL<CstNode<VariantCase>>






type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Unit

// Not sure if this is useful yet
type BuiltInCompoundTypes =
    | List of CstNode<MentionableType> // or of it makes sense to have these subtypes on the compound type variants yet
    | Record of (CstNode<UnqualValueIdentifier> * CstNode<MentionableType>) nel
    | Tuple of CstNode<TupleType>








(* Values *)

type NumberLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int


type PrimitiveLiteralValue =
    | NumberPrimitive of NumberLiteralValue
    | CharPrimitive of char
    | StringPrimitive of string
    | BoolPrimitive of bool
    | UnitPrimitive


type InfixOpAssociativity =
    | Left
    | Right
    | Non

type InfixOpDeclaration =
    { name : Lexer.Operator
      associativity : InfixOpAssociativity
      precedence : int
      /// The value should be a function taking exactly two parameters
      value : Identifier }


type CompoundValues =
    | List of CstNode<Expression> list
    | Tuple of CstNode<Expression> * NEL<CstNode<Expression>> // Because a tuple has at least two members
    | Record of (CstNode<UnqualValueIdentifier> * CstNode<Expression>) list
    | RecordExtension of
        recordToExtend : CstNode<UnqualValueIdentifier> *
        additions : NEL<CstNode<UnqualValueIdentifier> * CstNode<Expression>>

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues =
    { label : CstNode<UnqualTypeOrModuleIdentifier>
      values : CstNode<ExplicitValue> list }

and FunctionValue =
    { params_ : NEL<CstNode<AssignmentPattern>> // cos if it didn't have any then it would just be a regular value expression
      body : CstNode<Expression> }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of PrimitiveLiteralValue
    | CustomTypeVariant of CustomTypeValues

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue // for the parameters
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : UnqualValueIdentifier

and LetBinding =
    { bindPattern : CstNode<AssignmentPattern>
      value : CstNode<Expression> }

and ControlFlowExpression =
    | IfExpression of condition : CstNode<Expression> * ifTrue : CstNode<Expression> * ifFalse : CstNode<Expression>
    | CaseMatch of exprToMatch : CstNode<Expression> * branches : NEL<CstNode<AssignmentPattern> * CstNode<Expression>>



and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | Identifier of Identifier // referencing some other expression...
    | LetExpression of bindings : NEL<CstNode<LetBinding>> * inExpr : CstNode<Expression> // can't have lets outside of an expression
    | ControlFlowExpression of ControlFlowExpression



and CompoundExpression =
    | Operator of left : CstNode<Expression> * opSequence : NEL<CstNode<Operator> * CstNode<Expression>>
    | FunctionApplication of funcExpr : CstNode<Expression> * params' : NEL<CstNode<Expression>>
    | DotAccess of expr : CstNode<Expression> * dotSequence : CstNode<NEL<UnqualValueIdentifier>>



and Expression =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression
    | ParensedExpression of Expression // doesn't make much difference for the syntax tree, but useful for debugging



type ValueDeclaration =
    { valueName : CstNode<UnqualValueIdentifier>
      value : CstNode<Expression> }



type ValueAnnotation =
    { valueName : CstNode<UnqualValueIdentifier>
      annotatedType : MentionableType }


(* The module as a whole *)



//module <Identifier>{.<Identifier>} exposing (..)
//module <Identifier>{.Identifier} exposing ((<Identifier>[(..)]|<identifier>){, (<Identifier>[(..)]|<identifier>)})


type ModuleExport =
    { name : CstNode<UnqualIdentifier>
      exposeVariants : CstNode<unit> option }


type ExportExposings =
    | ExposeAll // exposing (..)
    | ExplicitExposeds of NEL<CstNode<ModuleExport>> // exposing (Foo, Bar(..), baz)



type ModuleDeclaration =
    { moduleName : CstNode<QualifiedModuleOrTypeIdentifier>
      exposing : ExportExposings }





//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing (..)]]
//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing ( { <Identifier>|<identifier>, } <Identifier>|<identifier> )]]

type ImportExposings =
    | NoExposeds
    | ExplicitExposeds of NEL<CstNode<UnqualIdentifier>> // exposing (Foo,Bar,baz)
    | ExposeAll of CstNode<unit> // exposing (..)

type ImportDeclaration =
    { moduleName : CstNode<QualifiedModuleOrTypeIdentifier>
      alias : CstNode<UnqualTypeOrModuleIdentifier> option
      exposingMode : ImportExposings }


//type ValueDeclaration =
//    { typeSignature : TypeDeclaration list option // either it's explicit or it'll have to be inferred
//      body : Expression } // aaand heeere's where the magic happens!

// Representing a whole file/module
type YlModule =
    { moduleDecl : ModuleDeclaration
      imports : CstNode<ImportDeclaration> list
      typeDeclarations : CstNode<TypeDeclaration> list
      valueAnnotations : CstNode<ValueAnnotation> list
      valueDeclarations : CstNode<ValueDeclaration> list }

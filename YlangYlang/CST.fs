module ConcreteSyntaxTree

open Lexer
module S = SyntaxTree


///// Structure to contain both a CST node and reference to the parsed tokens and source text
////[<StructuredFormatDisplay("Node({str})")>]
//type CstNode<'a> =
//    { node : 'a
//      source : TokenWithSource list }

//    member this.str = sprintf "%A" this.node



//let makeCstNode node source = { node = node; source = source }


//let getNode { node = node } = node

//let mapNode f node =
//    { source = node.source
//      node = f node.node }

(* Names and identifiers *)




type DestructuredPattern = S.DestructuredPattern<TypeOrModuleIdentifier>
///// Destructured records need to have one destructured member
//| DestructuredRecord of CstNode<UnqualValueIdentifier> nel
///// Destructured tuples need to have at least two members
//| DestructuredTuple of CstNode<AssignmentPattern> tom
//| DestructuredCons of CstNode<AssignmentPattern> tom
//| DestructuredTypeVariant of
//    constructor : CstNode<TypeOrModuleIdentifier> *
//    params' : CstNode<AssignmentPattern> list



/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern = S.AssignmentPattern<TypeOrModuleIdentifier>
//| Named of UnqualValueIdentifier
//| Ignored // i.e. the underscore
//| Unit
//| DestructuredPattern of DestructuredPattern
//| Aliased of pattern : CstNode<AssignmentPattern> * alias : CstNode<UnqualValueIdentifier>










(* Types *)

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
type MentionableType = S.MentionableType<TypeOrModuleIdentifier>
//| UnitType
//| GenericTypeVar of UnqualValueIdentifier
//| Tuple of TupleType
//| Record of RecordType
//| ExtendedRecord of ExtendedRecordType
//| ReferencedType of typeName : CstNode<TypeOrModuleIdentifier> * typeParams : CstNode<MentionableType> list
//| Arrow of fromType : CstNode<MentionableType> * toType : NEL<CstNode<MentionableType>>
//| Parensed of CstNode<MentionableType>



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType = S.TupleType<TypeOrModuleIdentifier>
//{ types : CstNode<MentionableType> tom }


and RecordType = S.RecordType<TypeOrModuleIdentifier>
//{ fields : Map<CstNode<UnqualValueIdentifier>, CstNode<MentionableType>> }

and ExtendedRecordType = S.ExtendedRecordType<TypeOrModuleIdentifier>
//{ extendedAlias : CstNode<UnqualValueIdentifier>
//  fields : Map<CstNode<UnqualValueIdentifier>, CstNode<MentionableType>> }


type VariantCase = S.VariantCase<TypeOrModuleIdentifier>
//{ label : CstNode<UnqualTypeOrModuleIdentifier>
//  contents : CstNode<MentionableType> list }

type NewTypeDeclaration = S.NewTypeDeclaration<TypeOrModuleIdentifier>
//{ specifiedTypeParams : CstNode<UnqualValueIdentifier> list
//  variants : NEL<CstNode<VariantCase>> }


type AliasDeclaration = S.AliasDeclaration<TypeOrModuleIdentifier>
//{ specifiedTypeParams : CstNode<UnqualValueIdentifier> list // in case the underlying type needs it
//  referent : CstNode<MentionableType> }


type TypeDeclaration = S.TypeDeclaration<TypeOrModuleIdentifier>
//| Alias of AliasDeclaration
//| Sum of NewTypeDeclaration











(* Values *)

//type InfixOpAssociativity =
//    | Left
//    | Right
//    | Non

type InfixOpDeclaration = S.InfixOpDeclaration<ValueIdentifier>
//{ name : Lexer.Operator
//  associativity : InfixOpAssociativity
//  precedence : int
//  /// The value should be a function taking exactly two parameters
//  value : Identifier }




//type NumberLiteralValue =
//    | FloatLiteral of float
//    | IntLiteral of int


//type PrimitiveLiteralValue =
//    | NumberPrimitive of NumberLiteralValue
//    | CharPrimitive of char
//    | StringPrimitive of string
//    | BoolPrimitive of bool
//    | UnitPrimitive


type CompoundValues = S.CompoundValues<TypeOrModuleIdentifier, ValueIdentifier>
//| List of CstNode<Expression> list
//| Tuple of CstNode<Expression> tom
//| Record of (CstNode<UnqualValueIdentifier> * CstNode<Expression>) list
//| RecordExtension of
//    recordToExtend : CstNode<UnqualValueIdentifier> *
//    additions : NEL<CstNode<UnqualValueIdentifier> * CstNode<Expression>>

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues = S.CustomTypeValues<TypeOrModuleIdentifier, ValueIdentifier>
//{ label : CstNode<UnqualTypeOrModuleIdentifier>
//  values : CstNode<Expression> list }

and FunctionValue = S.FunctionValue<TypeOrModuleIdentifier, ValueIdentifier>
//{ params_ : NEL<CstNode<AssignmentPattern>> // cos if it didn't have any then it would just be a regular value expression
//  body : CstNode<Expression> }


and ExplicitValue = S.ExplicitValue<TypeOrModuleIdentifier, ValueIdentifier>
//| Compound of CompoundValues
//| Primitive of PrimitiveLiteralValue
//| CustomTypeVariant of CustomTypeValues

//// functions and other values might be unified by just giving all values a possibly-empty list of parameters
//| Function of FunctionValue // for the parameters
///// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
//| DotGetter of recordField : UnqualValueIdentifier

and LetBinding = S.LetBinding<TypeOrModuleIdentifier, ValueIdentifier>
//{ bindPattern : CstNode<AssignmentPattern>
//  value : CstNode<Expression> }

and ControlFlowExpression = S.ControlFlowExpression<TypeOrModuleIdentifier, ValueIdentifier>
//| IfExpression of condition : CstNode<Expression> * ifTrue : CstNode<Expression> * ifFalse : CstNode<Expression>
//| CaseMatch of exprToMatch : CstNode<Expression> * branches : NEL<CstNode<AssignmentPattern> * CstNode<Expression>>



and SingleValueExpression = S.SingleValueExpression<TypeOrModuleIdentifier, ValueIdentifier>
//| ExplicitValue of ExplicitValue
//| Identifier of Identifier // referencing some other expression...
//| LetExpression of bindings : NEL<CstNode<LetBinding>> * inExpr : CstNode<Expression> // can't have lets outside of an expression
//| ControlFlowExpression of ControlFlowExpression



and CompoundExpression = S.CompoundExpression<TypeOrModuleIdentifier, ValueIdentifier>
//| Operator of left : CstNode<Expression> * opSequence : NEL<CstNode<Operator> * CstNode<Expression>>
//| FunctionApplication of funcExpr : CstNode<Expression> * params' : NEL<CstNode<Expression>>
//| DotAccess of expr : CstNode<Expression> * dotSequence : CstNode<NEL<UnqualValueIdentifier>>



and Expression = S.Expression<TypeOrModuleIdentifier, ValueIdentifier>
//| SingleValueExpression of SingleValueExpression
//| CompoundExpression of CompoundExpression
//| ParensedExpression of Expression // doesn't make much difference for the syntax tree, but useful for debugging



type ValueDeclaration = S.ValueDeclaration<TypeOrModuleIdentifier, ValueIdentifier>
//{ valueName : CstNode<UnqualValueIdentifier>
//  value : CstNode<Expression> }



type ValueAnnotation = S.ValueAnnotation<TypeOrModuleIdentifier>
//{ valueName : CstNode<UnqualValueIdentifier>
//  annotatedType : CstNode<MentionableType> }


(* The module as a whole *)



//module <Identifier>{.<Identifier>} exposing (..)
//module <Identifier>{.Identifier} exposing ((<Identifier>[(..)]|<identifier>){, (<Identifier>[(..)]|<identifier>)})


//type ModuleExport = S.ModuleExport<TypeOrModuleIdentifier,ValueIdentifier>
//{ name : CstNode<UnqualIdentifier>
//  exposeVariants : CstNode<unit> option }


//type ExportExposings =
//    | ExposeAll // exposing (..)
//    | ExplicitExposeds of NEL<CstNode<ModuleExport>> // exposing (Foo, Bar(..), baz)



//type ModuleDeclaration =
//    { moduleName : CstNode<QualifiedModuleOrTypeIdentifier>
//      exposing : CstNode<ExportExposings> }





//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing (..)]]
//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing ( { <Identifier>|<identifier>, } <Identifier>|<identifier> )]]

//type ImportExposings =
//    | NoExposeds
//    | ExplicitExposeds of NEL<CstNode<UnqualIdentifier>> // exposing (Foo,Bar,baz)
//    | ExposeAll of CstNode<unit> // exposing (..)

//type ImportDeclaration =
//    { moduleName : CstNode<QualifiedModuleOrTypeIdentifier>
//      alias : CstNode<UnqualTypeOrModuleIdentifier> option
//      exposingMode : ImportExposings }



type Declaration = S.Declaration<TypeOrModuleIdentifier, ValueIdentifier>
//    | ImportDeclaration of ImportDeclaration
//    | TypeDeclaration of name : CstNode<UnqualTypeOrModuleIdentifier> * declaration : TypeDeclaration
//    | ValueTypeAnnotation of ValueAnnotation
//    | ValueDeclaration of ValueDeclaration


//// Representing a whole file/module
type YlModule = S.YlModule<TypeOrModuleIdentifier, ValueIdentifier>
//    { moduleDecl : ModuleDeclaration
//      declarations : CstNode<Declaration> list }


type YlProjectItem = S.YlProjectItem<TypeOrModuleIdentifier, ValueIdentifier>

type YlProject = S.YlProject<TypeOrModuleIdentifier, ValueIdentifier>

﻿module SyntaxTree

//open Lexer


/// Structure to contain both a CST node and reference to the parsed tokens and source text
//[<StructuredFormatDisplay("Node({str})")>]
type CstNode<'a> =
    { node : 'a
      source : Lexer.TokenWithSource list }

    member this.str = sprintf "%A" this.node



let makeCstNode node source = { node = node; source = source }


let getNode { node = node } = node

let mapNode f node =
    { source = node.source
      node = f node.node }

(* Names and identifiers *)




type DestructuredPattern<'Upper> =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of CstNode<Lexer.UnqualValueIdentifier> nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of CstNode<AssignmentPattern<'Upper>> tom
    | DestructuredCons of CstNode<AssignmentPattern<'Upper>> tom
    | DestructuredTypeVariant of constructor : CstNode<'Upper> * params' : CstNode<AssignmentPattern<'Upper>> list



/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern<'Upper> =
    | Named of Lexer.UnqualValueIdentifier
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern<'Upper>
    | Aliased of pattern : CstNode<AssignmentPattern<'Upper>> * alias : CstNode<Lexer.UnqualValueIdentifier>










(* Types *)

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
type MentionableType<'Upper, 'Lower when 'Lower : comparison> =
    | UnitType
    | GenericTypeVar of Lexer.UnqualValueIdentifier
    | Tuple of TupleType<'Upper, 'Lower>
    | Record of RecordType<'Upper, 'Lower>
    | ExtendedRecord of ExtendedRecordType<'Upper, 'Lower>
    | ReferencedType of typeName : CstNode<'Upper> * typeParams : CstNode<MentionableType<'Upper, 'Lower>> list
    | Arrow of
        fromType : CstNode<MentionableType<'Upper, 'Lower>> *
        toType : NEL<CstNode<MentionableType<'Upper, 'Lower>>>
    | Parensed of CstNode<MentionableType<'Upper, 'Lower>>



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType<'Upper, 'Lower when 'Lower : comparison> =
    { types : CstNode<MentionableType<'Upper, 'Lower>> tom }


and RecordType<'Upper, 'Lower when 'Lower : comparison> =
    { fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType<'Upper, 'Lower>>> }

and ExtendedRecordType<'Upper, 'Lower when 'Lower : comparison> =
    { extendedAlias : CstNode<Lexer.UnqualValueIdentifier> // Because it has to be a single named value, no dots.
      fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType<'Upper, 'Lower>>> }


type VariantCase<'Upper, 'Lower when 'Lower : comparison> =
    { label : CstNode<Lexer.UnqualTypeOrModuleIdentifier>
      contents : CstNode<MentionableType<'Upper, 'Lower>> list }

type NewTypeDeclaration<'Upper, 'Lower when 'Lower : comparison> =
    { typeParams : CstNode<'Lower> list
      variants : NEL<CstNode<VariantCase<'Upper, 'Lower>>> }


type AliasDeclaration<'Upper, 'Lower when 'Lower : comparison> =
    { typeParams : CstNode<Lexer.UnqualValueIdentifier> list // in case the underlying type needs it
      referent : CstNode<MentionableType<'Upper, 'Lower>> }


type TypeDeclaration<'Upper, 'Lower when 'Lower : comparison> =
    | Alias of AliasDeclaration<'Upper, 'Lower>
    | Sum of NewTypeDeclaration<'Upper, 'Lower>











(* Values *)

type InfixOpAssociativity =
    | Left
    | Right
    | Non

type InfixOpDeclaration<'Lower> =
    { name : Lexer.Operator
      associativity : InfixOpAssociativity
      precedence : int
      /// The value should be a function taking exactly two parameters
      value : 'Lower }




type NumberLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int


type PrimitiveLiteralValue =
    | NumberPrimitive of NumberLiteralValue
    | CharPrimitive of char
    | StringPrimitive of string
    | BoolPrimitive of bool
    | UnitPrimitive


type CompoundValues<'Upper, 'Lower when 'Lower : comparison> =
    | List of CstNode<Expression<'Upper, 'Lower>> list
    | Tuple of CstNode<Expression<'Upper, 'Lower>> tom
    | Record of (CstNode<Lexer.UnqualValueIdentifier> * CstNode<Expression<'Upper, 'Lower>>) list
    | RecordExtension of
        recordToExtend : CstNode<Lexer.UnqualValueIdentifier> *
        additions : NEL<CstNode<Lexer.UnqualValueIdentifier> * CstNode<Expression<'Upper, 'Lower>>>

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues<'Upper, 'Lower when 'Lower : comparison> =
    { label : CstNode<Lexer.UnqualTypeOrModuleIdentifier>
      values : CstNode<Expression<'Upper, 'Lower>> list }

and FunctionValue<'Upper, 'Lower when 'Lower : comparison> =
    { params_ : NEL<CstNode<AssignmentPattern<'Upper>>> // cos if it didn't have any then it would just be a regular value expression
      body : CstNode<Expression<'Upper, 'Lower>> }


and ExplicitValue<'Upper, 'Lower when 'Lower : comparison> =
    | Compound of CompoundValues<'Upper, 'Lower>
    | Primitive of PrimitiveLiteralValue
    | CustomTypeVariant of CustomTypeValues<'Upper, 'Lower>

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue<'Upper, 'Lower> // for the parameters
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : Lexer.UnqualValueIdentifier

and LetBinding<'Upper, 'Lower when 'Lower : comparison> =
    { bindPattern : CstNode<AssignmentPattern<'Upper>>
      value : CstNode<Expression<'Upper, 'Lower>> }

and ControlFlowExpression<'Upper, 'Lower when 'Lower : comparison> =
    | IfExpression of
        condition : CstNode<Expression<'Upper, 'Lower>> *
        ifTrue : CstNode<Expression<'Upper, 'Lower>> *
        ifFalse : CstNode<Expression<'Upper, 'Lower>>
    | CaseMatch of
        exprToMatch : CstNode<Expression<'Upper, 'Lower>> *
        branches : NEL<CstNode<AssignmentPattern<'Upper>> * CstNode<Expression<'Upper, 'Lower>>>



and SingleValueExpression<'Upper, 'Lower when 'Lower : comparison> =
    | ExplicitValue of ExplicitValue<'Upper, 'Lower>
    | Identifier of Lexer.Identifier
    | LetExpression of
        bindings : NEL<CstNode<LetBinding<'Upper, 'Lower>>> *
        inExpr : CstNode<Expression<'Upper, 'Lower>> // can't have lets outside of an expression
    | ControlFlowExpression of ControlFlowExpression<'Upper, 'Lower>



and CompoundExpression<'Upper, 'Lower when 'Lower : comparison> =
    | Operator of
        left : CstNode<Expression<'Upper, 'Lower>> *
        opSequence : NEL<CstNode<Lexer.Operator> * CstNode<Expression<'Upper, 'Lower>>>
    | FunctionApplication of
        funcExpr : CstNode<Expression<'Upper, 'Lower>> *
        params' : NEL<CstNode<Expression<'Upper, 'Lower>>>
    | DotAccess of expr : CstNode<Expression<'Upper, 'Lower>> * dotSequence : CstNode<NEL<Lexer.UnqualValueIdentifier>>



and Expression<'Upper, 'Lower when 'Lower : comparison> =
    | SingleValueExpression of SingleValueExpression<'Upper, 'Lower>
    | CompoundExpression of CompoundExpression<'Upper, 'Lower>
    | ParensedExpression of Expression<'Upper, 'Lower> // doesn't make much difference for the syntax tree, but useful for debugging



type ValueDeclaration<'Upper, 'Lower when 'Lower : comparison> =
    { valueName : CstNode<'Lower>
      value : CstNode<Expression<'Upper, 'Lower>> }



type ValueAnnotation<'Upper, 'Lower when 'Lower : comparison> =
    { valueName : CstNode<'Lower>
      annotatedType : CstNode<MentionableType<'Upper, 'Lower>> }


(* The module as a whole *)



//module <Identifier>{.<Identifier>} exposing (..)
//module <Identifier>{.Identifier} exposing ((<Identifier>[(..)]|<identifier>){, (<Identifier>[(..)]|<identifier>)})


type ModuleExport =
    { name : CstNode<Lexer.UnqualIdentifier>
      exposeVariants : CstNode<unit> option }


type ExportExposings =
    | ExposeAll // exposing (..)
    | ExplicitExposeds of NEL<CstNode<ModuleExport>> // exposing (Foo, Bar(..), baz)



type ModuleDeclaration =
    { moduleName : CstNode<Lexer.QualifiedModuleOrTypeIdentifier>
      exposing : CstNode<ExportExposings> }





//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing (..)]]
//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing ( { <Identifier>|<identifier>, } <Identifier>|<identifier> )]]

type ImportExposings =
    | NoExposeds
    | ExplicitExposeds of NEL<CstNode<Lexer.UnqualIdentifier>> // exposing (Foo,Bar,baz)
    | ExposeAll of CstNode<unit> // exposing (..)

type ImportDeclaration =
    { moduleName : CstNode<Lexer.QualifiedModuleOrTypeIdentifier>
      alias : CstNode<Lexer.UnqualTypeOrModuleIdentifier> option
      exposingMode : ImportExposings }



type Declaration<'Upper, 'Lower when 'Lower : comparison> =
    | ImportDeclaration of ImportDeclaration
    | TypeDeclaration of name : CstNode<'Upper> * declaration : TypeDeclaration<'Upper, 'Lower>
    | ValueTypeAnnotation of ValueAnnotation<'Upper, 'Lower>
    | ValueDeclaration of ValueDeclaration<'Upper, 'Lower>


// Representing a whole file/module
type YlModule<'Upper, 'Lower when 'Lower : comparison> =
    { moduleDecl : ModuleDeclaration
      declarations : CstNode<Declaration<'Upper, 'Lower>> list }
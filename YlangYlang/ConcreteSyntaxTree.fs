﻿module ConcreteSyntaxTree

open Lexer


(* Names and identifiers *)


type DestructuredPattern =
    | DestructuredRecord of Identifier list
    | DestructuredTuple of AssignmentPattern list // This should really be a type that we can ensure has at least 2 members
    | DestructuredCons of NEL<AssignmentPattern>
    | DestructuredTypeVariant of constructor : TypeOrModuleIdentifier * AssignmentPattern list



/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of UnqualValueIdentifier
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of AssignmentPattern * alias : UnqualValueIdentifier


(* Types *)

type TypeReference =
    | Concrete of QualifiedModuleOrTypeIdentifier // name of the type referenced
    | Generic of UnqualValueIdentifier // name of the type param. This includes unused parameters in functions and case matches



and Unit = Unit // it's a type tho so we gotta include it

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
and MentionableType =
    | UnitType
    | GenericTypeVar of UnqualValueIdentifier
    | Tuple of TupleType
    | Record of RecordType
    | ReferencedType of typeName : TypeOrModuleIdentifier * typeParams : MentionableType list
    | Arrow of fromType : MentionableType * toType : NEL<MentionableType>
    | Parensed of MentionableType



and TupleType =
    { types : MentionableType * NEL<MentionableType> }


and RecordType =
    { fields : Map<UnqualValueIdentifier, MentionableType> }


type VariantCase =
    { label : UnqualTypeOrModuleIdentifier
      contents : MentionableType list }


type TypeDeclaration =
    | Alias of
        name : UnqualTypeOrModuleIdentifier *
        specifiedTypeParams : UnqualValueIdentifier list *  // in case the underlying type needs it
        referent : MentionableType
    | Sum of
        name : UnqualTypeOrModuleIdentifier *
        specifiedTypeParams : UnqualValueIdentifier list *
        variants : NEL<VariantCase>






type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Unit

// Not sure if this is useful yet
type BuiltInCompoundTypes =
    | List of MentionableType // or of it makes sense to have these subtypes on the compound type variants yet
    | Record of (UnqualValueIdentifier * MentionableType) list
    | Tuple of TupleType








(* Values *)

type NumberLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int


type PrimitiveLiteralValue =
    | NumberPrimitive of NumberLiteralValue
    | CharPrimitive of char
    | StringPrimitive of string
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
    | List of Expression list
    | Tuple of Expression * NEL<Expression> // Because a tuple has at least two members
    | Record of (UnqualValueIdentifier * Expression) list
    | RecordExtension of recordToExtend : UnqualValueIdentifier * additions : NEL<UnqualValueIdentifier * Expression>

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues =
    { label : UnqualTypeOrModuleIdentifier
      values : ExplicitValue list }

and FunctionValue =
    { params_ : NEL<AssignmentPattern> // cos if it didn't have any then it would just be a regular value expression
      body : Expression }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of PrimitiveLiteralValue
    | CustomTypeVariant of CustomTypeValues

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue // for the parameters
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : UnqualValueIdentifier

/// @TODO: allow for destructured params here at some point
and LetBinding =
    { bindPattern : AssignmentPattern
      value : Expression }

and ControlFlowExpression =
    | IfExpression of condition : Expression * ifTrue : Expression * ifFalse : Expression
    | CaseMatch of exprToMatch : Expression * branches : NEL<AssignmentPattern * Expression>



and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | Identifier of Identifier // referencing some other expression...
    | LetExpression of bindings : NEL<LetBinding> * inExpr : Expression // can't have lets outside of an expression
    | ControlFlowExpression of ControlFlowExpression


/// @TODO: would be good to flatten these constructors in the abstract syntax tree so we can represent the operators and function applications as a list, not a tree with heavy right hand side children
and CompoundExpression =
    // Multiple operators in a row are in right nested expressions
    | Operator of left : Expression * opSequence : NEL<Operator * Expression>
    | FunctionApplication of funcExpr : Expression * params' : NEL<Expression>
    | DotAccess of expr : Expression * dotSequence : NEL<UnqualValueIdentifier>



and Expression =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression
    | ParensedExpression of Expression // doesn't make much difference for the syntax tree, but useful for debugging



type ValueDeclaration =
    { valueName : UnqualValueIdentifier
      value : Expression }

// Not sure if it makes sense to have these yet, when we haven't yet enforced that the types are consistent...
// Unless... maybe these type getters can return a Result of either consistent types or of conflicting types, which can then be used for type errors or type hinting or somesuch...?
let typeOfPrimitiveLiteralValue =
    function
    | NumberPrimitive num ->
        match num with
        | FloatLiteral _ -> Float
        | IntLiteral _ -> Int
    | CharPrimitive _ -> Char
    | StringPrimitive _ -> String
    | UnitPrimitive _ -> Unit

//let typeOfCompoundLiteralValue =
//    function
//    | List




(* The module as a whole *)



//module <Identifier>{.<Identifier>} exposing (..)
//module <Identifier>{.Identifier} exposing ((<Identifier>[(..)]|<identifier>){, (<Identifier>[(..)]|<identifier>)})


type ModuleExport =
    { name : UnqualIdentifier
      exposeVariants : bool }


type ExportExposings =
    | ExposeAll // exposing (..)
    | ExplicitExposeds of ModuleExport list // exposing (Foo, Bar(..), baz)



type ModuleDeclaration =
    { moduleName : QualifiedModuleOrTypeIdentifier
      exposing : ExportExposings }





// /// Use when parsing types works
//type ValueOrTypeExport =
//    | ValueExport of IdentifierName
//    | TypeExport of TypeExport

//type ExplicitExports =
//    { types : TypeExport list
//      values : IdentifierName list }

//type Exports =
//    | ExportAll
//    | ExportExplicits of ValueOrTypeExport list


//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing (..)]]
//import <Identifier>{.<Identifier>} [[as <Identifier>] [exposing ( { <Identifier>|<identifier>, } <Identifier>|<identifier> )]]

type ImportExposings =
    | NoExposeds
    | ExplicitExposeds of NEL<UnqualIdentifier> // exposing (Foo,Bar,baz)
    | ExposeAll // exposing (..)

type ImportDeclaration =
    { moduleName : QualifiedModuleOrTypeIdentifier
      alias : UnqualTypeOrModuleIdentifier option
      exposingMode : ImportExposings }


//type ValueDeclaration =
//    { typeSignature : TypeDeclaration list option // either it's explicit or it'll have to be inferred
//      body : Expression } // aaand heeere's where the magic happens!

// Representing a whole file/module
type YlModule =
    { moduleDecl : ModuleDeclaration
      imports : ImportDeclaration list
      typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

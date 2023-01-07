module ConcreteSyntaxTree

open Lexer


(* Names and identifiers *)


type DestructuredPattern =
    | DestructuredRecord of Identifier list
    | DestructuredTuple of AssignmentPattern list // This should really be a type that we can ensure has at least 2 members
    | DestructuredCons of NEL<AssignmentPattern>
    | DestructuredTypeVariant of TypeOrModuleIdentifier * AssignmentPattern list



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
    | Record of RecordType
    | Tuple of TupleType
    | Name of TypeReference
    | Arrow of (MentionableType * MentionableType)
    | UnitType of Unit



and RecordType =
    { fields : Map<UnqualTypeOrModuleIdentifier, MentionableType> }



and AliasType =
    { referent : MentionableType
      specifiedTypeParams : UnqualValueIdentifier list } // in case the underlying type needs it

and TupleType = { types : MentionableType list } // could process into pairs and triples once we've eliminated the quads (although they should be recognised by the compiler, they are still forbidden). Should we account for single entry tuples? Well no because those are just the same as the type in the single tuple. What about zero case tuples? Well no because those are just the same as Unit.

//type Pair<'a, 'b> = { fst : 'a; snd : 'b }

//type Triple<'a, 'b, 'c> = { fst : 'a; snd : 'b; third : 'c }

type VariantCase =
    { label : UnqualTypeOrModuleIdentifier
      contents : MentionableType list }

type SumType = { variants : NEL<VariantCase> }


type TypeOfTypeDeclaration =
    | Sum of SumType
    | Alias of AliasType

/// A top level type declaration
type TypeDeclaration =
    { typeParams : UnqualValueIdentifier list // generic params, could be empty
      typeOfTypeDeclaration : TypeOfTypeDeclaration }






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
    | Record of (UnqualValueIdentifier * Expression) list
    | Tuple of (Expression * Expression * Expression list) // Because a tuple has at least two members

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues =
    { label : UnqualTypeOrModuleIdentifier
      values : ExplicitValue list }

// lambas and named funcs have different syntaxes but i think they can both be treated as the same thing
and FunctionValue =
    { params_ : NEL<AssignmentPattern> // cos if it didn't have any then it would just be a regular value
      body : Expression }


and ExplicitValue =
    | Compound of CompoundValues
    | Primitive of PrimitiveLiteralValue
    | CustomTypeVariant of CustomTypeValues

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue // for the parameters

/// @TODO: allow for destructured params here at some point
and LetBinding =
    { bindPattern : AssignmentPattern
      value : Expression }



and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | Identifier of Identifier // referencing some other expression...
    | LetExpression of (NEL<LetBinding> * Expression) // can't have lets outside of an expression


/// @TODO: would be good to flatten these constructors in the abstract syntax tree so we can represent the operators and function applications as a list, not a tree with heavy right hand side children
and CompoundExpression =
    // Multiple operators in a row are in right nested expressions
    | Operator of (Expression * (Operator * Expression))
    | FunctionApplication of Expression * NEL<Expression>
    | DotAccess of Expression * NEL<UnqualValueIdentifier>

and ControlFlowExpression =
    | IfExpression of condition : Expression * ifTrue : Expression * ifFalse : Expression
    | CaseMatch of exprToMatch : Expression * branches : NEL<AssignmentPattern * Expression>


and Expression =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression
    | ParensedExpression of Expression
    | ControlFlowExpression of ControlFlowExpression



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
      //typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

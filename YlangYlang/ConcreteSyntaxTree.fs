module ConcreteSyntaxTree

open Lexer


// NAMES AND IDENTIFIERS

/// @TODO: Maybe wrap this in a newtype so that we can unambigiously differentiate between declared identifiers and referenced identifiers?
type IdentifierName = string


type TypeName = NEL<IdentifierName> // to account for fact that it could be direct or qualified reference
type ModuleName = NEL<IdentifierName> // to account for fact that it could be top level or submodule

type MaybeQualifiedValue = NEL<IdentifierName>

type DestructuredPattern =
    | DestructuredRecord of IdentifierName list
    | DestructuredTuple of AssignmentPattern list // This should really be a type that we can ensure has at least 2 members
    | DestructuredCons of NEL<AssignmentPattern>
    | DestructuredTypeVariant of TypeName * AssignmentPattern list



/// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of IdentifierName
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of AssignmentPattern * alias : IdentifierName


// TYPES

type TypeReference =
    | Concrete of TypeName // name of the type referenced
    | Generic of string // name of the type param. This includes unused parameters in functions and case matches



and Unit = Unit // it's a type tho so we gotta include it

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
and MentionableType =
    | Record of RecordType
    | Tuple of TupleType
    | Name of TypeReference
    | Arrow of (MentionableType * MentionableType)



and RecordType =
    { fields : Map<IdentifierName, MentionableType> }



and AliasType =
    { referent : MentionableType
      specifiedTypeParams : IdentifierName list } // in case the underlying type needs it

and TupleType = { types : MentionableType list } // could process into pairs and triples once we've eliminated the quads (although they should be recognised by the compiler, they are still forbidden). Should we account for single entry tuples? Well no because those are just the same as the type in the single tuple. What about zero case tuples? Well no because those are just the same as Unit.

//type Pair<'a, 'b> = { fst : 'a; snd : 'b }

//type Triple<'a, 'b, 'c> = { fst : 'a; snd : 'b; third : 'c }

type VariantCase =
    { label : IdentifierName
      contents : MentionableType list }

type SumType = { variants : NEL<VariantCase> }


type TypeOfTypeDeclaration =
    | Sum of SumType
    | Alias of AliasType

/// A top level type declaration
type TypeDeclaration =
    { typeParams : IdentifierName list // generic params, could be empty
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
    | Record of (IdentifierName * MentionableType) list
    | Tuple of TupleType








// VALUES

type NumberLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int


type PrimitiveLiteralValue =
    | NumberPrimitive of NumberLiteralValue
    | CharPrimitive of char
    | StringPrimitive of string
    | UnitPrimitive

type CompoundValues =
    | List of Expression list
    | Record of (IdentifierName * Expression) list
    | Tuple of Expression list

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues =
    { label : IdentifierName
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
    { name : AssignmentPattern
      value : Expression }



and SingleValueExpression =
    | ExplicitValue of ExplicitValue
    | Identifier of IdentifierName // referencing some other expression...
    | LetExpression of (NEL<LetBinding> * Expression) // can't have lets outside of an expression


/// @TODO: would be good to flatten these constructors in the abstract syntax tree so we can represent the operators and function applications as a list, not a tree with heavy right hand side children
and CompoundExpression =
    | Operator of (Expression * (Operator * Expression)) // Multiple operators in a row are in right nested expressions
    | FunctionApplication of (Expression * Expression)
    | DotAccess of Expression * IdentifierName

and Expression =
    | SingleValueExpression of SingleValueExpression
    | CompoundExpression of CompoundExpression
    | ParensedExpression of Expression


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




// THE MODULE AS AN ENTITY

/// `import Thing.OtherThing.Stuff (as TT) (exposing ((..)|(baa,baz,Bar))) `
type ImportExposingMode =
    | NoExposeds
    | ExplicitExposeds of IdentifierName list // exposing (Foo,Bar,baz)
    | ExposeAll // exposing (..)

type Import =
    { path : NEL<string> // dot-separated module path
      alias : IdentifierName option
      exposingMode : ImportExposingMode }


type TypeExport =
    { name : IdentifierName
      exposeVariants : bool }

//type ValueExport = { name : IdentifierName }
type ValueOrTypeExport =
    | ValueExport of IdentifierName
    | TypeExport of TypeExport

type ExportExposingMode =
    | ExposeAll // exposing (..)
    | ExplicitExposeds of ValueOrTypeExport list // exposing (Foo,Bar,baz)


type ExplicitExports =
    { types : TypeExport list
      values : IdentifierName list }



type Exports =
    | ExportAll
    | ExportExplicits of ValueOrTypeExport list

type ValueDeclaration =
    { typeSignature : TypeDeclaration list option // either it's explicit or it'll have to be inferred
      body : Expression } // aaand heeere's where the magic happens!

// Representing a whole file/module
type YlModule =
    { moduleName : ModuleName
      exports : Exports
      imports : Import list
      typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

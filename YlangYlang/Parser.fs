module Parser

open Lexer

type TypeName = NEL<string> // to account for fact that it could be direct or qualified reference
type ModuleName = NEL<string> // to account for fact that it could be top level or submodule

type MaybeQualifiedValue = NEL<string>

type TypeReference =
    | Concrete of TypeName // name of the type referenced
    | Generic of string // name of the type param



and Unit = Unit // it's a type tho so we gotta include it

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
and MentionableType =
    | Record of RecordType
    | Tuple of TupleType
    | Name of TypeReference
    | Arrow of (MentionableType * MentionableType)



and RecordType =
    { fields : Map<string, MentionableType> }



and AliasType =
    { referent : MentionableType
      specifiedTypeParams : string list } // in case the underlying type needs it

and TupleType = { types : MentionableType list } // could process into pairs and triples once we've eliminated the quads (although they should be recognised by the compiler, they are still forbidden). Should we account for single entry tuples? Well no because those are just the same as the type in the single tuple. What about zero case tuples? Well no because those are just the same as Unit.

//type Pair<'a, 'b> = { fst : 'a; snd : 'b }

//type Triple<'a, 'b, 'c> = { fst : 'a; snd : 'b; third : 'c }

and VariantCase =
    { label : string
      contents : MentionableType list }

and SumType = { variants : NEL<VariantCase> }


and TypeOfTypeDeclaration =
    | Sum of SumType
    | Alias of AliasType
    | Record of RecordType
    | Arrow of (TypeOfTypeDeclaration * TypeOfTypeDeclaration) // because functions can take functions as input and return functions as output (any multi-parameter function satisfies the latter criterion fyi)

/// A top level type declaration
type TypeDeclaration =
    { typeParams : string list // generic params, could be empty
      typeOfTypeDeclaration : TypeOfTypeDeclaration }

// not sure if this is fully right yet...
type TypeOfFunction =
    | Named of MaybeQualifiedValue
    | Lambda of (MentionableType * MentionableType)




/// import Thing.Thung
type ImportExposingMode =
    | NoExposeds
    | ExplicitExposeds of string list // exposing (Foo,Bar,baz)
    | ExposeAll // exposing (..)

type Import =
    { path : NEL<string> // dot-separated module path
      alias : string option
      exposingMode : ImportExposingMode }


type TypeExport =
    { name : string
      exposeVariants : bool }

type ValueExport = { name : string }

type Exports =
    { types : TypeExport list
      values : ValueExport list }


type BuiltInPrimitiveTypes =
    | Float
    | Int
    | String
    | Char
    | Unit

// Not sure if this is useful yet
type BuiltInCompoundTypes =
    | List of MentionableType // or of it makes sense to have these subtypes on the compound type variants yet
    | Record of (string * MentionableType) list
    | Tuple of TupleType



// Values from expressions

type NumberLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int


type PrimitiveLiteralValue =
    | NumberPrimitive of NumberLiteralValue
    | CharPrimitive of char
    | StringPrimitive of string
    | UnitPrimitive of unit

and CompoundTypeValues =
    | List of AnyValue list
    | Record of (string * AnyValue) list
    | Tuple of AnyValue list

// Not sure yet if it makes sense to have this as a separate type
and CustomTypeValues = Variant of (string * AnyValue list)

and AnyValue =
    | Compound of CompoundTypeValues
    | Primitive of PrimitiveLiteralValue
    | Custom of CustomTypeValues
    | Function of (MentionableType * MentionableType)



type IdentifierName = string

type Operator = string // maybe should be char list to symbolise that it's a list of symbols? idk

type Expression =
    | ExplicitValue of AnyValue
    | Identifier of IdentifierName // referencing some other expression...
    | Operator of (Operator * Expression * Expression)
    | FunctionApplication of (IdentifierName * AnyValue list)


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




type ValueDeclaration =
    { typeSignature : TypeDeclaration list option
    //body : Expression // aaand heeere's where the magic happens!
     }

type YlModule =
    { moduleName : ModuleName
      imports : Import list
      exports : Exports
      typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

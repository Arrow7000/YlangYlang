module Parser

open Lexer

type TypeName = NEL<string> // to account for fact that it could be direct or qualified reference


type TypeReference =
    | Concrete of TypeName // name of the type referenced
    | Generic of string // name of the type param



and Unit = Unit // it's a type tho so we gotta include it

/// For types that can be includes not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
and MentionedType =
    | Record of RecordType
    | Name of TypeReference



and RecordType = { fields : Map<string, MentionedType> }



and AliasType =
    { referent : MentionedType
      specifiedTypeParams : string list } // in case the underlying type needs it

and TupleType = { types : MentionedType list } // could process into pairs and triples once we've eliminated the quads (although they should be recognised by the compiler, they are still forbidden)

//type Pair<'a, 'b> = { fst : 'a; snd : 'b }

//type Triple<'a, 'b, 'c> = { fst : 'a; snd : 'b; third : 'c }

and VariantCase =
    { label : string
      contents : MentionedType list }

and SumType = { variants : NEL<VariantCase> }


and TypeOfTypeDeclaration =
    | Sum of SumType
    | Alias of AliasType
    | Record of RecordType

/// A top level type declaration
type TypeDeclaration =
    { typeParams : string list // generic params, could be empty
      typeOfTypeDeclaration : TypeOfTypeDeclaration }






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






type ValueDeclaration =
    { typeSignature : TypeDeclaration list option
    //body : Expression // aaand heeere's where the magic happens!
     }

type YlModule =
    { moduleName : NEL<string>
      imports : Import list
      exports : Exports
      typeDeclarations : TypeDeclaration list
      valueDeclarations : ValueDeclaration list }

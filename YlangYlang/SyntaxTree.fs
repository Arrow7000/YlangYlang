module SyntaxTree


/// Structure to contain both a CST node and reference to the parsed tokens and source text
//[<StructuredFormatDisplay("Node({str})")>]
type CstNode<'a> =
    {
        node : 'a
        /// @TODO: I wonder if this should be made an NEL, because it doesn't make sense to have a node with a tokens reference that doesn't contain any tokens
        source : Lexer.TokenWithSource list
    }

    member this.str = sprintf "%A" this.node



let makeCstNode (node : 'a) (source : Lexer.TokenWithSource list) : CstNode<'a> = { node = node; source = source }


let getNode { node = node } = node

let mapNode (f : 'a -> 'b) (node : CstNode<'a>) : CstNode<'b> =
    { source = node.source
      node = f node.node }

(* Names and identifiers *)




type DestructuredPattern =
    /// Destructured records need to have one destructured member
    | DestructuredRecord of CstNode<Lexer.UnqualValueIdentifier> nel
    /// Destructured tuples need to have at least two members
    | DestructuredTuple of CstNode<AssignmentPattern> tom
    | DestructuredCons of CstNode<AssignmentPattern> tom
    | DestructuredTypeVariant of
        constructor : CstNode<Lexer.TypeOrModuleIdentifier> *
        params' : CstNode<AssignmentPattern> list



/// Named – or ignored – variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern =
    | Named of Lexer.UnqualValueIdentifier
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern
    | Aliased of pattern : CstNode<AssignmentPattern> * alias : CstNode<Lexer.UnqualValueIdentifier>










(* Types *)

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
type MentionableType =
    | UnitType
    | GenericTypeVar of Lexer.UnqualValueIdentifier
    | Tuple of TupleType
    | Record of RecordType
    | ExtendedRecord of ExtendedRecordType
    | ReferencedType of typeName : CstNode<Lexer.TypeOrModuleIdentifier> * typeParams : CstNode<MentionableType> list
    | Arrow of fromType : CstNode<MentionableType> * toType : NEL<CstNode<MentionableType>>
    | Parensed of CstNode<MentionableType>



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType =
    { types : CstNode<MentionableType> tom }


and RecordType =
    { fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType>> }

and ExtendedRecordType =
    { extendedTypeParam : CstNode<Lexer.UnqualValueIdentifier> // Because it has to be a type param
      fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType>> }


type VariantCase =
    { label : CstNode<Lexer.UnqualTypeOrModuleIdentifier>
      contents : CstNode<MentionableType> list }

type NewTypeDeclaration =
    { typeParams : CstNode<Lexer.UnqualValueIdentifier> list
      variants : NEL<CstNode<VariantCase>> }


type AliasDeclaration =
    { typeParams : CstNode<Lexer.UnqualValueIdentifier> list // in case the underlying type needs it
      referent : CstNode<MentionableType> }


type TypeDeclaration =
    | Alias of AliasDeclaration
    | Sum of NewTypeDeclaration











(* Values *)

type InfixOpAssociativity =
    | Left
    | Right
    | Non




type InfixOpBuiltIn =
    { name : Lexer.BuiltInOperator
      associativity : InfixOpAssociativity
      precedence : int }





type PrimitiveLiteralValue =
    | FloatLiteral of float
    | IntLiteral of int
    | CharPrimitive of char
    | StringPrimitive of string
    | BoolPrimitive of bool
    | UnitPrimitive




type FunctionValue =
    { params_ : CstNode<AssignmentPattern> nel // cos if it didn't have any then it would just be a regular value expression
      body : CstNode<Expression> }




/// @TODO: need to account for let binding type annotations!
and LetBinding =
    { bindPattern : CstNode<AssignmentPattern>
      value : CstNode<Expression> }






and Expression =
    | Primitive of PrimitiveLiteralValue
    | Function of FunctionValue // for the parameters
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : Lexer.UnqualValueIdentifier

    | UpperIdentifier of Lexer.TypeOrModuleIdentifier
    | LowerIdentifier of Lexer.ValueIdentifier


    | List of CstNode<Expression> list
    | Tuple of CstNode<Expression> tom
    | Record of (CstNode<Lexer.UnqualValueIdentifier> * CstNode<Expression>) list
    | RecordExtension of
        recordToExtend : CstNode<Lexer.UnqualValueIdentifier> *
        additions : NEL<CstNode<Lexer.UnqualValueIdentifier> * CstNode<Expression>>

    | LetExpression of bindings : CstNode<LetBinding> nel * inExpr : CstNode<Expression> // can't have lets outside of an expression

    (* Control flow expressions *)
    | IfExpression of condition : CstNode<Expression> * ifTrue : CstNode<Expression> * ifFalse : CstNode<Expression>
    | CaseMatch of exprToMatch : CstNode<Expression> * branches : NEL<CstNode<AssignmentPattern> * CstNode<Expression>>

    (* Compound value expressions *)
    | Operator of left : CstNode<Expression> * opSequence : NEL<CstNode<Lexer.Operator> * CstNode<Expression>>
    | FunctionApplication of funcExpr : CstNode<Expression> * params' : NEL<CstNode<Expression>>
    /// I.e. an `expr.field` expression
    | DotAccess of expr : CstNode<Expression> * dotSequence : CstNode<NEL<Lexer.UnqualValueIdentifier>>

    | ParensedExpression of Expression // doesn't make much difference for the syntax tree, but useful for debugging



type InfixOpDeclaration =

    {
        /// Need to ensure we don't try to overwrite built-in operators in a new declaration here
        name : Lexer.UnqualValueIdentifier
        associativity : InfixOpAssociativity
        precedence : int
        /// The value should be a function taking exactly two parameters
        value : CstNode<Expression>
    }


type InfixOp =
    | BuiltIn of InfixOpBuiltIn
    | UserDefined of InfixOpDeclaration


type ValueDeclaration =
    { valueName : CstNode<Lexer.UnqualValueIdentifier>
      value : CstNode<Expression> }



type ValueAnnotation =
    { valueName : CstNode<Lexer.UnqualValueIdentifier>
      annotatedType : CstNode<MentionableType> }


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



type Declaration =
    | ImportDeclaration of ImportDeclaration
    | TypeDeclaration of name : CstNode<Lexer.UnqualTypeOrModuleIdentifier> * declaration : TypeDeclaration
    | ValueTypeAnnotation of ValueAnnotation
    | ValueDeclaration of ValueDeclaration
    | InfixOperatorDeclaration of InfixOpDeclaration


// Representing a whole file/module
type YlModule =
    { moduleDecl : ModuleDeclaration
      declarations : CstNode<Declaration> list }



/// A project item, so either a module file, or a dir containing more project items
type YlProjectItem =
    | NestedDir of dirName : string * dirContents : YlProjectItem list
    | Module of YlModule

type YlProject = YlProjectItem list

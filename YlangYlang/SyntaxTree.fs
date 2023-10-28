module SyntaxTree


/// Structure to contain both a CST node and reference to the parsed tokens and source text
//[<StructuredFormatDisplay("Node({str})")>]
type CstNode<'a> =
    { node : 'a
      /// @TODO: I wonder if this should be made an NEL, because it doesn't make sense to have a node with a tokens reference that doesn't contain any tokens
      source : Lexer.TokenWithSource list }

    member this.str = sprintf "%A" this.node



let makeCstNode (node : 'a) (source : Lexer.TokenWithSource list) : CstNode<'a> = { node = node; source = source }


let getNode { node = node } = node

let mapNode (f : 'a -> 'b) (node : CstNode<'a>) : CstNode<'b> =
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



/// Named – or ignored – variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
and AssignmentPattern<'Upper> =
    | Named of Lexer.UnqualValueIdentifier
    | Ignored // i.e. the underscore
    | Unit
    | DestructuredPattern of DestructuredPattern<'Upper>
    | Aliased of pattern : CstNode<AssignmentPattern<'Upper>> * alias : CstNode<Lexer.UnqualValueIdentifier>










(* Types *)

/// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
type MentionableType<'Upper> =
    | UnitType
    | GenericTypeVar of Lexer.UnqualValueIdentifier
    | Tuple of TupleType<'Upper>
    | Record of RecordType<'Upper>
    | ExtendedRecord of ExtendedRecordType<'Upper>
    | ReferencedType of typeName : CstNode<'Upper> * typeParams : CstNode<MentionableType<'Upper>> list
    | Arrow of fromType : CstNode<MentionableType<'Upper>> * toType : NEL<CstNode<MentionableType<'Upper>>>
    | Parensed of CstNode<MentionableType<'Upper>>



/// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
and TupleType<'Upper> =
    { types : CstNode<MentionableType<'Upper>> tom }


and RecordType<'Upper> =
    { fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType<'Upper>>> }

and ExtendedRecordType<'Upper> =
    { extendedTypeParam : CstNode<Lexer.UnqualValueIdentifier> // Because it has to be a type param
      fields : Map<CstNode<Lexer.UnqualValueIdentifier>, CstNode<MentionableType<'Upper>>> }


type VariantCase<'Upper> =
    { label : CstNode<Lexer.UnqualTypeOrModuleIdentifier>
      contents : CstNode<MentionableType<'Upper>> list }

type NewTypeDeclaration<'Upper> =
    { typeParams : CstNode<Lexer.UnqualValueIdentifier> list
      variants : NEL<CstNode<VariantCase<'Upper>>> }


type AliasDeclaration<'Upper> =
    { typeParams : CstNode<Lexer.UnqualValueIdentifier> list // in case the underlying type needs it
      referent : CstNode<MentionableType<'Upper>> }


type TypeDeclaration<'Upper> =
    | Alias of AliasDeclaration<'Upper>
    | Sum of NewTypeDeclaration<'Upper>











(* Values *)

type InfixOpAssociativity =
    | Left
    | Right
    | Non




type InfixOpBuiltIn =
    { name : Lexer.BuiltInOperator
      associativity : InfixOpAssociativity
      precedence : int }




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


and FunctionValue<'Upper, 'Lower when 'Lower : comparison> =
    { params_ : NEL<CstNode<AssignmentPattern<'Upper>>> // cos if it didn't have any then it would just be a regular value expression
      body : CstNode<Expression<'Upper, 'Lower>> }


and ExplicitValue<'Upper, 'Lower when 'Lower : comparison> =
    | Compound of CompoundValues<'Upper, 'Lower>
    | Primitive of PrimitiveLiteralValue

    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
    | Function of FunctionValue<'Upper, 'Lower> // for the parameters
    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
    | DotGetter of recordField : Lexer.UnqualValueIdentifier


/// @TODO: need to account for let binding type annotations!
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
    | UpperIdentifier of 'Upper
    | LowerIdentifier of 'Lower
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


type InfixOpDeclaration<'Upper, 'Lower when 'Lower : comparison> =

    { /// Need to ensure we don't try to overwrite built-in operators in a new declaration here
      name : Lexer.UnqualValueIdentifier
      associativity : InfixOpAssociativity
      precedence : int
      /// The value should be a function taking exactly two parameters
      value : CstNode<Expression<'Upper, 'Lower>> }


type InfixOp<'Upper, 'Lower when 'Lower : comparison> =
    | BuiltIn of InfixOpBuiltIn
    | UserDefined of InfixOpDeclaration<'Upper, 'Lower>


type ValueDeclaration<'Upper, 'Lower when 'Lower : comparison> =
    { valueName : CstNode<Lexer.UnqualValueIdentifier>
      value : CstNode<Expression<'Upper, 'Lower>> }



type ValueAnnotation<'Upper> =
    { valueName : CstNode<Lexer.UnqualValueIdentifier>
      annotatedType : CstNode<MentionableType<'Upper>> }


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
    | TypeDeclaration of name : CstNode<Lexer.UnqualTypeOrModuleIdentifier> * declaration : TypeDeclaration<'Upper>
    | ValueTypeAnnotation of ValueAnnotation<'Upper>
    | ValueDeclaration of ValueDeclaration<'Upper, 'Lower>
    | InfixOperatorDeclaration of InfixOpDeclaration<'Upper, 'Lower>


// Representing a whole file/module
type YlModule<'Upper, 'Lower when 'Lower : comparison> =
    { moduleDecl : ModuleDeclaration
      declarations : CstNode<Declaration<'Upper, 'Lower>> list }



/// A project item, so either a module file, or a dir containing more project items
type YlProjectItem<'Upper, 'Lower when 'Lower : comparison> =
    | NestedDir of dirName : string * dirContents : YlProjectItem<'Upper, 'Lower> list
    | Module of YlModule<'Upper, 'Lower>

type YlProject<'Upper, 'Lower when 'Lower : comparison> = YlProjectItem<'Upper, 'Lower> list

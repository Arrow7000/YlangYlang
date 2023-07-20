/// The CST with canonical, fully qualified names - where applicable
module QualifiedSyntaxTree

open Lexer
open System

module S = SyntaxTree
module C = ConcreteSyntaxTree




module Names =

    /// E.g. `module Page.Investigate.Aggregations`
    type ModulePath = | ModulePath of string nel

    /// A local alias for a module. E.g. `import Thing.Thang as Th`. Can't consist of multiple segments.
    type ModuleAlias = | ModuleAlias of string


    /// For names of types, type aliases, and constructors; but NOT for module paths. Use `ModulePath` for those.
    type UpperIdent = | UpperIdent of string

    /// For names of values, parameters or destructured fields
    type LowerIdent = | LowerIdent of string


    type RecordFieldName = | RecordFieldName of string


    /// Fully qualified type or type alias name
    type FullyQualifiedUpperIdent = | FullyQualifiedUpperIdent of module_ : ModulePath * name : UpperIdent

    /// Fully qualified named value
    type FullyQualifiedTopLevelLowerIdent =
        | FullyQualifiedTopLevelLowerIdent of module_ : ModulePath * name : LowerIdent



    /// For imports under an aliased module name
    type AliasedUpperIdent = | AliasedUpperIdent of moduleAlias : ModuleAlias * name : UpperIdent

    /// For imports under an aliased module name
    type AliasedTopLevelLowerIdent = | AliasedTopLevelLowerIdent of moduleAlias : ModuleAlias * name : LowerIdent


    type UpperNameValue =
        | FullyQualifiedUpper of FullyQualifiedUpperIdent
        | LocalUpper of UpperIdent

    type LowerNameValue =
        | FullyQualifiedLower of FullyQualifiedTopLevelLowerIdent
        | LocalLower of LowerIdent




    /// Top level because only top level types/values can be exposed/imported
    type TopLevelUpperIdent =
        /// Doesn't necessarily mean defined in this module, could also mean imported into this module; either explicitly or by exposing all
        | InThisModule of UpperIdent
        /// When it's a fully qualified reference to a type/value from a different module
        | OtherModuleFull of FullyQualifiedUpperIdent
        /// When it's a qualified reference, but qualified by an alias
        | OtherModuleAliased of AliasedUpperIdent

    /// Top level because only top level types/values can be exposed/imported
    type TopLevelLowerIdent =
        /// Doesn't necessarily mean defined in this module, could also mean imported into this module; either explicitly or by exposing all
        | InThisModule of LowerIdent
        /// When it's a fully qualified reference to a type/value from a different module
        | OtherModuleFull of FullyQualifiedTopLevelLowerIdent
        /// When it's a qualified reference, but qualified by an alias
        | OtherModuleAliased of AliasedTopLevelLowerIdent







    ///// Special token that lets us access the referenced item directly, without returning an option. Because if we have this token that means the named value in question has already been resolved.
    //type ResolvedType = | ResolvedType of Guid

    ///// Special token that lets us access the referenced item directly, without returning an option. Because if we have this token that means the named value in question has already been resolved.
    //type ResolvedTypeConstructor = | ResolvedTypeConstructor of Guid

    ///// Special token that lets us access the referenced item directly, without returning an option. Because if we have this token that means the named value in question has already been resolved.
    //type ResolvedValue = | ResolvedValue of Guid

    ////type ResolvedLowerTypeDeclaration = private | ResolvedLowerTypeDeclaration of Guid

    ///// Special token that lets us access the referenced item directly, without returning an option. Because if we have this token that means the named value in question has already been resolved.
    //type ResolvedTypeParam = | ResolvedTypeParam of Guid




    /// Type that describes the path to where a given name is declared.
    /// @TODO: hmmm how do we capture the fact that a name is the nth parameter of a function...? Maybe we don't need to actually? Because the name itself references it?
    type PathToDestructuredName =
        | SimpleName
        | InverseRecord
        | InverseTuple of index : uint * child : PathToDestructuredName
        | InverseCons of index : uint * child : PathToDestructuredName
        | InverseTypeVariant of constructor : UpperNameValue * index : uint * child : PathToDestructuredName









open Names


type Param =
    { ident : LowerIdent
      tokens : TokenWithSource list
      destructurePath : PathToDestructuredName }












//type DestructuredPattern =
//    /// Destructured records need to have one destructured member
//    | DestructuredRecord of (ResolvedValue * S.CstNode<LowerIdent>) nel
//    /// Destructured tuples need to have at least two members
//    | DestructuredTuple of S.CstNode<AssignmentPattern> tom
//    | DestructuredCons of S.CstNode<AssignmentPattern> tom
//    | DestructuredTypeVariant of constructor : ResolvedTypeConstructor * params' : S.CstNode<AssignmentPattern> list

///// Named - or ignored - variables to be declared, like an identifier name, function parameter, destructured field, pattern match case, etc.
//and AssignmentPattern =
//    | Named of resolved : ResolvedValue * ident : LowerIdent
//    | Ignored // i.e. the underscore
//    | Unit
//    | DestructuredPattern of DestructuredPattern
//    | Aliased of pattern : S.CstNode<AssignmentPattern> * alias : (ResolvedValue * S.CstNode<LowerIdent>)





///// We can't really store the tokens constituting the type param definition, because this is also used for storing the type params for value type annotations, which is only implicit and doesn't actually exist in source code
//type ResolvedTypeParams = Map<ResolvedTypeParam, LowerIdent>






//(* Types *)

///// For types that can be mentioned not at the top level of a file, e.g. records or types declared elsewhere. But e.g. you can't create an ad hoc sum type inside a record or another sum type. Sum types and aliases need to be declared at the top level of a module.
/////
///// @TODO: might need to make a separate version of this: one that can be used inside value type annotations where free type variables are allowed, and one to be used in type declarations, where free type variables are *not* allowed.
//type MentionableType =
//    | UnitType
//    | GenericTypeVar of ResolvedTypeParam
//    | Tuple of TupleType
//    | Record of RecordType
//    | ExtendedRecord of ExtendedRecordType
//    | ReferencedType of typeName : ResolvedType * typeParams : S.CstNode<MentionableType> list
//    | Arrow of fromType : S.CstNode<MentionableType> * toType : NEL<S.CstNode<MentionableType>>
//    | Parensed of S.CstNode<MentionableType>



///// Because there need to be at least two members for it to be a tuple type. Otherwise it's just a parensed expression.
//and TupleType =
//    { types : S.CstNode<MentionableType> tom }


//and RecordType =
//    { fields : Map<S.CstNode<RecordFieldName>, S.CstNode<MentionableType>> }

///// @TODO: as said above at MentionableType, we may need separate versions of this for value type annotations vs for use in type declarations; because in the former free type variables are allowed, but in the latter they are not.
//and ExtendedRecordType =
//    { extendedAlias : S.CstNode<ResolvedTypeParam> // Because it has to be a type param
//      fields : Map<S.CstNode<RecordFieldName>, S.CstNode<MentionableType>> }





//type VariantCase =
//    { label : S.CstNode<UpperIdent>
//      contents : S.CstNode<MentionableType> list }

///// I.e. a sum type
//type NewTypeDeclaration =
//    { typeParams : ResolvedTypeParams
//      variants : NEL<ResolvedTypeConstructor * S.CstNode<VariantCase>> }


//type AliasDeclaration =
//    { typeParams : ResolvedTypeParams // in case the underlying type needs it
//      referent : S.CstNode<MentionableType> }


//type TypeDeclaration =
//    | Alias of AliasDeclaration
//    | Sum of NewTypeDeclaration






//(* Values *)







//type Operator =
//    | BuiltInOp of Lexer.BuiltInOperator
//    | OtherOp of resolved : ResolvedValue * ident : LowerIdent

///// Note that each let binding could still create multiple named values through assignment patterns, so this is only the result of a single name, not a full binding
/////
///// @TODO: we don't currently parse for value type declarations in let bindings, so we need to support this!
//type ResolvedLetBinding =
//    { ident : LowerIdent
//      tokens : TokenWithSource list
//      destructurePath : PathToDestructuredName
//      /// This expression is actually the whole expression after the assignment, not just the bit that was destructured to this named identifier; that will have to be implemented at the type checking phase
//      assignedExpression : Expression }




//and LetDeclarationNames = Map<ResolvedValue, ResolvedLetBinding>

///// Represents all the named params in a single function parameter or case match expression
//and FunctionOrCaseMatchParam =
//    { paramPattern : AssignmentPattern
//      namesMap : Map<ResolvedValue, Param> }




//and CompoundValues =
//    | List of S.CstNode<Expression> list
//    | Tuple of S.CstNode<Expression> tom
//    | Record of (S.CstNode<RecordFieldName> * S.CstNode<Expression>) list
//    | RecordExtension of
//        recordToExtend : (ResolvedValue * S.CstNode<LowerIdent>) *
//        additions : NEL<S.CstNode<RecordFieldName> * S.CstNode<Expression>>


//and FunctionValue =
//    { params_ : FunctionOrCaseMatchParam nel
//      body : S.CstNode<Expression> }


//and ExplicitValue =
//    | Compound of CompoundValues
//    | Primitive of S.PrimitiveLiteralValue

//    // functions and other values might be unified by just giving all values a possibly-empty list of parameters
//    | Function of FunctionValue
//    /// A `.someField` expression which are first class getters for record fields. A `.someField` getter is a function that takes a record that has a `someField` field and returns the value at that field
//    | DotGetter of recordField : LowerIdent




//and ControlFlowExpression =
//    | IfExpression of
//        condition : S.CstNode<Expression> *
//        ifTrue : S.CstNode<Expression> *
//        ifFalse : S.CstNode<Expression>
//    | CaseMatch of exprToMatch : S.CstNode<Expression> * branches : CaseMatchBranch nel

//and SingleValueExpression =
//    | ExplicitValue of ExplicitValue
//    | UpperIdentifier of fullyQualifiedName : FullyQualifiedUpperIdent * resolved : ResolvedTypeConstructor
//    | LowerIdentifier of name : LowerNameValue * resolved : ResolvedValue
//    | LetExpression of namedValues : LetDeclarationNames * expr : Expression
//    | ControlFlowExpression of ControlFlowExpression




//and CompoundExpression =
//    | Operator of left : S.CstNode<Expression> * opSequence : NEL<S.CstNode<Operator> * S.CstNode<Expression>>
//    | FunctionApplication of funcExpr : S.CstNode<Expression> * params' : NEL<S.CstNode<Expression>>
//    | DotAccess of expr : S.CstNode<Expression> * dotSequence : S.CstNode<NEL<LowerIdent>>


//and CaseMatchBranch =
//    { matchPattern : FunctionOrCaseMatchParam
//      body : S.CstNode<Expression> }


//and Expression =
//    | SingleValueExpression of SingleValueExpression
//    | CompoundExpression of CompoundExpression





//type InfixOpDeclaration =
//    { name : LowerIdent
//      associativity : S.InfixOpAssociativity
//      precedence : int
//      /// The value should be a function taking exactly two parameters
//      value : S.CstNode<Expression> }


//type ValueDeclaration =
//    { valueName : S.CstNode<LowerIdent>
//      value : S.CstNode<Expression> }



//type ValueAnnotation =
//    { valueName : S.CstNode<LowerIdent>
//      /// these aren't in the source code, but they're gathered from the type expression implicitly
//      gatheredImplicitParams : ResolvedTypeParams
//      annotatedType : S.CstNode<MentionableType> }



//type InfixOp =
//    | BuiltIn of S.InfixOpBuiltIn
//    | UserDefined of declaration : InfixOpDeclaration * resolved : ResolvedValue





//type Declaration =
//    | ImportDeclaration of S.ImportDeclaration
//    | TypeDeclaration of resolved : ResolvedType * name : S.CstNode<UpperIdent> * declaration : TypeDeclaration
//    | ValueTypeAnnotation of resolved : ResolvedValue * ValueAnnotation
//    | ValueDeclaration of resolved : ResolvedValue * ValueDeclaration
//    | InfixOperatorDeclaration of resolved : ResolvedValue * InfixOpDeclaration


//// Representing a whole file/module
//type YlModule =
//    { moduleDecl : S.ModuleDeclaration
//      imports : S.ImportDeclaration list
//      types : Map<ResolvedType, UpperIdent * TypeDeclaration>
//      valueTypes : Map<ResolvedValue, LowerIdent * ValueAnnotation>
//      values : Map<ResolvedValue, LowerIdent * ValueDeclaration>
//      operators : Map<ResolvedValue, InfixOpDeclaration> }



///// A project item, so either a module file, or a dir containing more project items
//type YlProjectItem =
//    | NestedDir of dirName : string * dirContents : YlProjectItem list
//    | Module of YlModule

//type YlProject = { modules : YlProjectItem list }

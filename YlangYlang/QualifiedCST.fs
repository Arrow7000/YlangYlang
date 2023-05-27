/// The CST with canonical, fully qualified names - where applicable
module QualifiedSyntaxTree

open Lexer
module S = SyntaxTree
module C = ConcreteSyntaxTree
//open NameResolution


/// E.g. `module Page.Investigate.Aggregations`
type ModulePath = | ModulePath of string nel

/// A local alias for a module. E.g. `import Thing.Thang as Th`. Can't consist of multiple segments.
type ModuleAlias = | ModuleAlias of string


/// For names of types, type aliases, and constructors; but NOT for module paths. Use `ModulePath` for those.
type UpperIdent = | UpperIdent of string

/// For names of values, parameters or destructured fields
type LowerIdent = | LowerIdent of string


type LocalVariableOrParamIdent = | LocalVariableOrParamIdent of LowerIdent

/// Fully qualified type or type alias name
type FullyQualifiedUpperIdent = | FullyQualifiedUpperIdent of module_ : ModulePath * name : UpperIdent

/// Fully qualified named value
type FullyQualifiedTopLevelLowerIdent = | FullyQualifiedTopLevelLowerIdent of module_ : ModulePath * name : LowerIdent


type AliasedUpperIdent = | AliasedUpperIdent of moduleAlias : ModuleAlias * name : UpperIdent


type AliasedTopLevelLowerIdent = | AliasedTopLevelLowerIdent of moduleAlias : ModuleAlias * name : LowerIdent




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






type DestructuredPattern = S.DestructuredPattern<FullyQualifiedUpperIdent>
and AssignmentPattern = S.AssignmentPattern<FullyQualifiedUpperIdent>


type MentionableType = S.MentionableType<FullyQualifiedUpperIdent>
and TupleType = S.TupleType<FullyQualifiedUpperIdent>
and RecordType = S.RecordType<FullyQualifiedUpperIdent>
and ExtendedRecordType = S.ExtendedRecordType<FullyQualifiedUpperIdent>


type VariantCase = S.VariantCase<FullyQualifiedUpperIdent>

type NewTypeDeclaration = S.NewTypeDeclaration<FullyQualifiedUpperIdent>

type AliasDeclaration = S.AliasDeclaration<FullyQualifiedUpperIdent>

type TypeDeclaration = S.TypeDeclaration<FullyQualifiedUpperIdent>

type InfixOpDeclaration = S.InfixOpDeclaration<FullyQualifiedTopLevelLowerIdent>

type CompoundValues = S.CompoundValues<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and CustomTypeValues = S.CustomTypeValues<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and FunctionValue = S.FunctionValue<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and ExplicitValue = S.ExplicitValue<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and LetBinding = S.LetBinding<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and ControlFlowExpression = S.ControlFlowExpression<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and SingleValueExpression = S.SingleValueExpression<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and CompoundExpression = S.CompoundExpression<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>
and Expression = S.Expression<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>

type ValueDeclaration = S.ValueDeclaration<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>

type ValueAnnotation = S.ValueAnnotation<FullyQualifiedUpperIdent>

type Declaration = S.Declaration<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>


type YlModule = S.YlModule<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>

type YlProjectItem = S.YlProjectItem<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>

type YlProject = S.YlProject<FullyQualifiedUpperIdent, FullyQualifiedTopLevelLowerIdent>

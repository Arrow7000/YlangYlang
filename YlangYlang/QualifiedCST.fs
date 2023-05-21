module QualifiedSyntaxTree

open Lexer
module S = SyntaxTree
module C = ConcreteSyntaxTree


/// Fully qualified module path
type FullyQualifiedModule = FullyQualifiedModule of string nel

/// Fully qualified type or type alias name
type FullyQualifiedTypeIdent = FullyQualifiedTypeIdent of string nel

/// Fully qualified named value
type FullyQualifiedValueIdent = FullyQualifiedValueIdent of string nel







type DestructuredPattern = S.DestructuredPattern<QualifiedModuleOrTypeIdentifier>
and AssignmentPattern = S.AssignmentPattern<QualifiedModuleOrTypeIdentifier>


type MentionableType = S.MentionableType<QualifiedModuleOrTypeIdentifier>
and TupleType = S.TupleType<QualifiedModuleOrTypeIdentifier>
and RecordType = S.RecordType<QualifiedModuleOrTypeIdentifier>
and ExtendedRecordType = S.ExtendedRecordType<QualifiedModuleOrTypeIdentifier>


type VariantCase = S.VariantCase<QualifiedModuleOrTypeIdentifier>

type NewTypeDeclaration = S.NewTypeDeclaration<QualifiedModuleOrTypeIdentifier>

type AliasDeclaration = S.AliasDeclaration<QualifiedModuleOrTypeIdentifier>

type TypeDeclaration = S.TypeDeclaration<QualifiedModuleOrTypeIdentifier>

type InfixOpDeclaration = S.InfixOpDeclaration<QualifiedValueIdentifier>

type CompoundValues = S.CompoundValues<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and CustomTypeValues = S.CustomTypeValues<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and FunctionValue = S.FunctionValue<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and ExplicitValue = S.ExplicitValue<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and LetBinding = S.LetBinding<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and ControlFlowExpression = S.ControlFlowExpression<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and SingleValueExpression = S.SingleValueExpression<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and CompoundExpression = S.CompoundExpression<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>
and Expression = S.Expression<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>

type ValueDeclaration = S.ValueDeclaration<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>

type ValueAnnotation = S.ValueAnnotation<QualifiedModuleOrTypeIdentifier>

type Declaration = S.Declaration<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>


type YlModule = S.YlModule<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>

type YlProjectItem = S.YlProjectItem<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>

type YlProject = S.YlProject<QualifiedModuleOrTypeIdentifier, QualifiedValueIdentifier>





let qualifyValueNames




let qualifyDestructuredPattern (moduleCtx : ) (unqual : C.DestructuredPattern) : DestructuredPattern =
    match unqual with
    | S.DestructuredRecord content -> S.DestructuredRecord content
    | S.DestructuredTuple content -> S.DestructuredTuple content
    | S.DestructuredCons content -> S.DestructuredCons content
    | S.DestructuredTypeVariant (a,b) -> S.DestructuredTypeVariant (a,b)
    

let qualifyAssignmentPattern (moduleCtx : ) (unqual : C.AssignmentPattern) : AssignmentPattern =
    match unqual with


let qualifyMentionableType (moduleCtx : ) (unqual : C.MentionableType) : MentionableType =
    match unqual with


let qualifyTupleType (moduleCtx : ) (unqual : C.TupleType) : TupleType =
    match unqual with


let qualifyRecordType (moduleCtx : ) (unqual : C.RecordType) : RecordType =
    match unqual with


let qualifyExtendedRecordType (moduleCtx : ) (unqual : C.ExtendedRecordType) : ExtendedRecordType =
    match unqual with


let qualifyVariantCase (moduleCtx : ) (unqual : C.VariantCase) : VariantCase =
    match unqual with


let qualifyNewTypeDeclaration (moduleCtx : ) (unqual : C.NewTypeDeclaration) : NewTypeDeclaration =
    match unqual with


let qualifyAliasDeclaration (moduleCtx : ) (unqual : C.AliasDeclaration) : AliasDeclaration =
    match unqual with


let qualifyTypeDeclaration (moduleCtx : ) (unqual : C.TypeDeclaration) : TypeDeclaration =
    match unqual with


let qualifyCompoundValues (moduleCtx : ) (unqual : C.CompoundValues) : CompoundValues =
    match unqual with


let qualifyCustomTypeValues (moduleCtx : ) (unqual : C.CustomTypeValues) : CustomTypeValues =
    match unqual with


let qualifyFunctionValue (moduleCtx : ) (unqual : C.FunctionValue) : FunctionValue =
    match unqual with


let qualifyExplicitValue (moduleCtx : ) (unqual : C.ExplicitValue) : ExplicitValue =
    match unqual with


let qualifyLetBinding (moduleCtx : ) (unqual : C.LetBinding) : LetBinding =
    match unqual with


let qualifyControlFlowExpression (moduleCtx : ) (unqual : C.ControlFlowExpression) : ControlFlowExpression =
    match unqual with


let qualifySingleValueExpression (moduleCtx : ) (unqual : C.SingleValueExpression) : SingleValueExpression =
    match unqual with


let qualifyCompoundExpression (moduleCtx : ) (unqual : C.CompoundExpression) : CompoundExpression =
    match unqual with


let qualifyExpression (moduleCtx : ) (unqual : C.Expression) : Expression =
    match unqual with


let qualifyValueDeclaration (moduleCtx : ) (unqual : C.ValueDeclaration) : ValueDeclaration =
    match unqual with


let qualifyValueAnnotation (moduleCtx : ) (unqual : C.ValueAnnotation) : ValueAnnotation =
    match unqual with



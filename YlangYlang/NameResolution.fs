module NameResolution

open Lexer
open SyntaxTree
open ConcreteSyntaxTree


/// Denotes either a single instance of a named value, or 2 or more instances, which means the named value is a duplicate, which is a compile error
type SingleOrDuplicate<'a> =
    | Single of 'a
    | Duplicate of TwoOrMore<'a>

    static member map (f : 'a -> 'b) sod =
        match sod with
        | Single a -> Single (f a)
        | Duplicate tom -> Duplicate (TOM.map f tom)


    static member getFirst (sod : SingleOrDuplicate<'a>) =
        match sod with
        | Single a -> a
        | Duplicate tom -> TOM.head tom

/// Type that describes the path to where a given name is declared.
/// @TODO: hmmm how do we capture the fact that a name is the nth parameter of a function...? Maybe we don't need to actually? Because the name itself references it?
type PathToDestructuredName =
    | SimpleName
    | InverseRecord
    | InverseTuple of index : uint * child : PathToDestructuredName
    | InverseCons of index : uint * child : PathToDestructuredName
    | InverseTypeVariant of constructor : TypeOrModuleIdentifier * index : uint * child : PathToDestructuredName





module ResolvedNames =

    type TypeDeclarations = Map<TypeOrModuleIdentifier, SingleOrDuplicate<TokenWithSource list * TypeDeclaration>>

    type VariantConstructor =
        { typeName : TypeOrModuleIdentifier
          typeDeclaration : NewTypeDeclaration
          variantParams : MentionableType list }

    type TypeConstructors = Map<TypeOrModuleIdentifier, SingleOrDuplicate<TokenWithSource list * VariantConstructor>>

    type ValueOrParameter =
        | Value of assignmentPattern : PathToDestructuredName * assignedExpression : Expression
        /// If this assignment pattern is an alias for a greater deconstructed parameter expression, or just a function or match expression case parameter
        | Parameter of subPattern : PathToDestructuredName

    type ValueDeclarations = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * ValueOrParameter>>

    type ValueTypeDeclarations = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * MentionableType>>



    type ResolvedNames =
        { typeDeclarations : TypeDeclarations
          typeConstructors : TypeConstructors
          valueDeclarations : ValueDeclarations
          valueTypeDeclarations : ValueTypeDeclarations }


    let getTypeDeclarations names : TypeDeclarations = names.typeDeclarations
    let getTypeConstructors names : TypeConstructors = names.typeConstructors
    let getValueDeclarations names : ValueDeclarations = names.valueDeclarations
    let getValueTypeDeclarations names : ValueTypeDeclarations = names.valueTypeDeclarations


    let private getFromMap name =
        Map.tryFind name
        >> Option.map SingleOrDuplicate.getFirst


    let tryFindTypeDeclaration name { typeDeclarations = nameMap } : (TknSrc list * TypeDeclaration) option =
        getFromMap name nameMap

    let tryFindTypeConstructor name { typeConstructors = nameMap } : (TknSrc list * VariantConstructor) option =
        getFromMap name nameMap

    let tryFindValue name { valueDeclarations = nameMap } : (TknSrc list * ValueOrParameter) option =
        getFromMap name nameMap

    let tryFindValueTypeDeclarations name { valueTypeDeclarations = nameMap } : (TknSrc list * MentionableType) option =
        getFromMap name nameMap





    let empty =
        { typeDeclarations = Map.empty
          typeConstructors = Map.empty
          valueDeclarations = Map.empty
          valueTypeDeclarations = Map.empty }






    /// Useful lil' map to roll up all param declarations more easily
    type ResolvedParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * PathToDestructuredName>>

    /// Primarily useful to set sub-destructured params into their sub-path reference paths
    let mapResolvedParams f (resolvedParams : ResolvedParams) : ResolvedParams =
        Map.map (fun _ -> SingleOrDuplicate.map (fun (tokens, reference) -> tokens, f reference)) resolvedParams


    let addNewParamReference ident path (resolvedParams : ResolvedParams) : ResolvedParams =
        Map.change
            (ident.node)
            (fun oldValueOpt ->
                let newValueAndPath = ident.source, path

                match oldValueOpt with
                | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
                | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
                | None -> Some (Single newValueAndPath))
            resolvedParams




    /// This should be threaded back up to feed back on unresolved names errors
    /// Hmmm, I'm not entirely sure whether  this should be passed up, or whether we should resolve all the names at every scope level first, and then only feed things back up if a name can't be resolved.
    type UnresolvedNames = Set<UnqualIdentifier>




    let addNewReference
        (ident : CstNode<'name>)
        (value : 'v)
        (map : Map<'name, SingleOrDuplicate<TokenWithSource list * 'v>>)
        =
        map
        |> Map.change (ident.node) (fun oldValueOpt ->
            let newValueAndPath = ident.source, value

            match oldValueOpt with
            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
            | None -> Some (Single newValueAndPath))




    let addNewTypeDeclaration name value names =
        { names with typeDeclarations = addNewReference name value names.typeDeclarations }

    let addTypeConstructor variantName variantParams typeName typeDeclaration names =
        { names with
            typeConstructors =
                addNewReference
                    variantName
                    { typeName = typeName
                      typeDeclaration = typeDeclaration
                      variantParams = variantParams }
                    names.typeConstructors }

    let addValue name value names : ResolvedNames =
        { names with valueDeclarations = addNewReference name value names.valueDeclarations }

    let addValueTypeDeclaration name value names =
        { names with valueTypeDeclarations = addNewReference name value names.valueTypeDeclarations }




    let combineReferenceMaps (mapList : Map<'a, SingleOrDuplicate<'b>> seq) : Map<'a, SingleOrDuplicate<'b>> =
        let mapFolder
            (acc : Map<'a, SingleOrDuplicate<'b>>)
            (key : 'a)
            (value : SingleOrDuplicate<'b>)
            : Map<'a, SingleOrDuplicate<'b>> =
            Map.change
                key
                (fun oldValueOpt ->
                    match oldValueOpt with
                    | Some oldVal ->
                        match oldVal, value with
                        | Single oldRef, Single newRef -> Some (Duplicate <| TOM.make newRef oldRef)

                        | Single singleRef, Duplicate duplRefs
                        | Duplicate duplRefs, Single singleRef -> Some (Duplicate <| TOM.cons singleRef duplRefs)

                        | Duplicate a, Duplicate b -> Some (Duplicate <| TOM.append a b)

                    | None -> Some value)
                acc

        Seq.fold (fun acc thisMap -> Map.fold mapFolder thisMap acc) Map.empty mapList




    let combineResolvedNamesMaps (mapList : ResolvedNames seq) =
        let typeDeclarations = Seq.map getTypeDeclarations mapList
        let typeConstructors = Seq.map getTypeConstructors mapList
        let values = Seq.map getValueDeclarations mapList
        let valueTypeDeclarations = Seq.map getValueTypeDeclarations mapList


        { typeDeclarations = combineReferenceMaps typeDeclarations
          typeConstructors = combineReferenceMaps typeConstructors
          valueDeclarations = combineReferenceMaps values
          valueTypeDeclarations = combineReferenceMaps valueTypeDeclarations }







open ResolvedNames


let combineReferenceMaps (mapList : Map<'a, SingleOrDuplicate<'b>> seq) : Map<'a, SingleOrDuplicate<'b>> =
    let mapFolder
        (acc : Map<'a, SingleOrDuplicate<'b>>)
        (key : 'a)
        (value : SingleOrDuplicate<'b>)
        : Map<'a, SingleOrDuplicate<'b>> =
        Map.change
            key
            (fun oldValueOpt ->
                match oldValueOpt with
                | Some oldVal ->
                    match oldVal, value with
                    | Single oldRef, Single newRef -> Some (Duplicate <| TOM.make newRef oldRef)

                    | Single singleRef, Duplicate duplRefs
                    | Duplicate duplRefs, Single singleRef -> Some (Duplicate <| TOM.cons singleRef duplRefs)

                    | Duplicate a, Duplicate b -> Some (Duplicate <| TOM.append a b)

                | None -> Some value)
            acc

    Seq.fold (fun acc thisMap -> Map.fold mapFolder thisMap acc) Map.empty mapList







/// This is for straight converting a params map to a values map, but _not_ suitable for converting a
let convertParamsToValuesMap (resolvedParams : ResolvedParams) : ResolvedNames =
    { ResolvedNames.empty with
        valueDeclarations =
            Map.mapKeyVal
                (fun key tokensAndValues ->
                    key,
                    tokensAndValues
                    |> SingleOrDuplicate.map (fun (tokens, value) -> (tokens, Parameter value)))
                resolvedParams }



/// Get all the exposed names from a single assignment pattern
let rec resolveParamAssignment (assignmentPattern : CstNode<AssignmentPattern>) : ResolvedParams =
    match assignmentPattern.node with
    | Named ident ->
        Map.empty
        |> addNewParamReference (makeCstNode ident assignmentPattern.source) SimpleName

    | Ignored -> Map.empty
    | AssignmentPattern.Unit -> Map.empty
    | Aliased (alias = alias; pattern = pattern) ->
        resolveParamAssignment pattern
        |> addNewParamReference alias SimpleName

    | DestructuredPattern pattern -> resolveDestructuredParam (makeCstNode pattern assignmentPattern.source)



/// We need to recursively go down all the sub-destructurings, because all of those still get exposed to the same scope. Unlike let bindings in sub-expressions which don't get propagated upward.
and resolveDestructuredParam (pattern : CstNode<DestructuredPattern>) : ResolvedParams =

    let getParamsMapForEach
        (putInPath : PathToDestructuredName -> PathToDestructuredName)
        assignmentPattern
        : ResolvedParams =
        resolveParamAssignment assignmentPattern
        |> mapResolvedParams putInPath


    match pattern.node with
    | DestructuredRecord fieldNames ->
        fieldNames
        |> NEL.fold<_, _> (fun map fieldName -> addNewParamReference fieldName InverseRecord map) Map.empty

    | DestructuredTuple items ->
        let maps =
            items
            |> TOM.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseTuple (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 0u)
            |> fst

        combineReferenceMaps maps

    | DestructuredCons items ->
        let maps =
            items
            |> TOM.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseCons (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 0u)
            |> fst

        combineReferenceMaps maps

    | DestructuredTypeVariant (constructor, params_) ->
        params_
        |> List.mapi (fun i ->
            getParamsMapForEach (fun subPath -> InverseTypeVariant (constructor.node, uint i, subPath)))
        |> combineReferenceMaps










let resolveFuncParams ({ params_ = params_ } : FunctionValue) : ResolvedNames =
    let values =
        params_
        |> NEL.map (
            resolveParamAssignment
            >> Map.map (fun _ tokensAndValues ->
                tokensAndValues
                |> SingleOrDuplicate.map (fun (tokens, path) -> tokens, Parameter path))
        )
        |> NEL.toList
        |> combineReferenceMaps

    { ResolvedNames.empty with valueDeclarations = values }


let resolveLetBinding
    ({ bindPattern = bindPattern
       value = value } : LetBinding)
    : ResolvedNames =
    let values =
        resolveParamAssignment bindPattern
        |> Map.map (fun _ tokensAndValues ->
            tokensAndValues
            |> SingleOrDuplicate.map (fun (tokens, path) ->
                tokens, Value (assignmentPattern = path, assignedExpression = value.node)))

    { ResolvedNames.empty with valueDeclarations = values }


let resolveLetExpression (bindings : CstNode<LetBinding> nel) =
    bindings
    |> NEL.toList
    |> Seq.map (getNode >> resolveLetBinding)
    |> combineResolvedNamesMaps



let resolveTypeConstructors
    (typeName : CstNode<UnqualTypeOrModuleIdentifier>)
    (typeDeclaration : TypeDeclaration)
    : ResolvedNames =

    match typeDeclaration with
    | Alias aliasDecl ->
        // We're not accounting for record alias constructors just yet
        ResolvedNames.empty
        |> addNewTypeDeclaration (mapNode UnqualType typeName) (Alias aliasDecl)

    | Sum newTypeDecl ->
        newTypeDecl.variants
        |> NEL.fold<_, _>
            (fun map variant ->
                addTypeConstructor
                    (mapNode UnqualType variant.node.label)
                    (variant.node.contents |> List.map getNode)
                    (UnqualType typeName.node)
                    newTypeDecl
                    map)
            (addNewTypeDeclaration (mapNode UnqualType typeName) (Sum newTypeDecl) ResolvedNames.empty)





let rec resolveExpressionBindings (expression : Expression) : ResolvedNames =
    match expression with
    | SingleValueExpression expr ->
        match expr with
        | ExplicitValue value ->
            match value with
            | Compound _ -> ResolvedNames.empty

            | Primitive _ -> ResolvedNames.empty
            | CustomTypeVariant _ -> ResolvedNames.empty
            | Function funcVal -> resolveFuncParams funcVal
            | DotGetter _ -> ResolvedNames.empty
        | Identifier _ -> ResolvedNames.empty
        | LetExpression (bindings, _) -> resolveLetExpression bindings

        | ControlFlowExpression _ -> ResolvedNames.empty
    | CompoundExpression _ -> ResolvedNames.empty
    | ParensedExpression _ -> ResolvedNames.empty




let resolveModuleBindings (ylModule : YlModule) =
    let resolveSingleDeclaration (declaration : CstNode<Declaration>) =
        match declaration.node with
        | ImportDeclaration _ ->
            // @TODO: I'll need to implement the cross-module name resolution here!
            ResolvedNames.empty

        | TypeDeclaration (name, decl) -> resolveTypeConstructors name decl
        | ValueTypeAnnotation { valueName = valueName
                                annotatedType = annotatedType } ->
            ResolvedNames.empty
            |> addValueTypeDeclaration valueName annotatedType.node

        | ValueDeclaration { valueName = valueName; value = value } ->
            ResolvedNames.empty
            |> addValue valueName (Value (SimpleName, value.node))

    ylModule.declarations
    |> List.map resolveSingleDeclaration
    |> combineResolvedNamesMaps

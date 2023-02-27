module NameResolution

open Lexer
open ConcreteSyntaxTree


/// Denotes either a single instance of a named value, or 2 or more instances, which means the named value is a duplicate, which is a compile error
type SingleOrDuplicate<'a> =
    | Single of 'a
    | Duplicate of TwoOrMore<'a>

    static member map (f : 'a -> 'b) sod =
        match sod with
        | Single a -> Single (f a)
        | Duplicate tom -> Duplicate (TOM.map f tom)


/// Type that describes the path to where a given name is declared
type PathToDestructuredName =
    | SimpleName
    | InverseRecord
    | InverseTuple of index : uint * child : PathToDestructuredName
    | InverseCons of index : uint * child : PathToDestructuredName
    | InverseTypeVariant of index : uint * child : PathToDestructuredName


/// Map that stores just parameter references.
type ResolvedParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * PathToDestructuredName>>



//type ExpressionOrTypeRef =
//    | Expr of assignmentPattern : PathToDestructuredName * assignedExpression : CstNode<Expression>


/// A reference to either a real concrete expression or an assignment parameter
type NameReference =
    /// Reference a real expression
    | ExpressionRef of assignmentPattern : PathToDestructuredName * assignedExpression : CstNode<Expression>
    /// If this assignment pattern is an alias for a greater deconstructed parameter expression
    | AssignmentParam of subPattern : PathToDestructuredName
    | TypeRef of TypeDeclaration
    /// The type name should always be in the same resolved names map
    | VariantConstructor of typeName : UnqualTypeOrModuleIdentifier * variantParams : MentionableType list





/// Map that stores references to either parameters or real expressions.
/// The tokens list is about where the *name* is in the source.
type ResolvedNames = Map<UnqualIdentifier, SingleOrDuplicate<TokenWithSource list * NameReference>>

(*
The head is always the closest scope, so pop it off when we leave a given scope
*)

type NamesInScope = ResolvedNames list


/// Adds a new param to a `ResolvedParams` map.
let addNewParamsReference
    (ident : CstNode<UnqualValueIdentifier>)
    (path : PathToDestructuredName)
    (map : ResolvedParams)
    : ResolvedParams =
    Map.change
        ident.node
        (fun oldValueOpt ->
            let newValueAndPath = ident.source, path

            match oldValueOpt with
            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
            | None -> Some (Single newValueAndPath))
        map


/// Adds a new param to a `ResolvedValueNames` map.
let addNewValueReference
    (ident : CstNode<UnqualIdentifier>)
    (newValue : NameReference)
    (map : ResolvedNames)
    : ResolvedNames =
    Map.change
        ident.node
        (fun oldValueOpt ->
            let newValueAndSource = ident.source, newValue

            match oldValueOpt with
            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndSource oldRef)
            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndSource refList)
            | None -> Some (Single newValueAndSource))
        map




let combineReferenceMaps (mapList : Map<'a, SingleOrDuplicate<'b>> list) : Map<'a, SingleOrDuplicate<'b>> =
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

    let listFolder
        (acc : Map<'a, SingleOrDuplicate<'b>>)
        (thisMap : Map<'a, SingleOrDuplicate<'b>>)
        : Map<'a, SingleOrDuplicate<'b>> =
        Map.fold mapFolder thisMap acc

    List.fold listFolder Map.empty mapList



let convertParamsToValuesMap (resolvedParams : ResolvedParams) : ResolvedNames =
    Map.mapKeyVal
        (fun key tokensAndValues ->
            ValueIdentifier key,
            tokensAndValues
            |> SingleOrDuplicate.map (fun (tokens, value) -> (tokens, AssignmentParam value)))
        resolvedParams


/// I think this is the kind of thing we need for collecting the destructured parts of a single assignment pattern, and this could then be used by `resolveParamAssignment`
let rec resolveDestructuredParam (pattern : CstNode<DestructuredPattern>) : ResolvedParams =
    let getParamsMapForEach
        (putInPath : PathToDestructuredName -> PathToDestructuredName)
        assignmentPattern
        : ResolvedParams =
        resolveParamAssignment assignmentPattern
        |> Map.map (fun _ -> SingleOrDuplicate.map (fun (tokens, path) -> tokens, putInPath path))


    match pattern.node with
    | DestructuredRecord fieldNames ->
        fieldNames
        |> NEL.fold<_, _> (fun map fieldName -> addNewParamsReference fieldName InverseRecord map) Map.empty

    | DestructuredTuple (first, tail) ->
        let firstMap = getParamsMapForEach (fun subPath -> InverseTuple (0u, subPath)) first

        let tailMaps =
            tail
            |> NEL.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseTuple (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 1u)
            |> fst

        combineReferenceMaps (firstMap :: tailMaps)

    | DestructuredCons (first, tail) ->
        let firstMap = getParamsMapForEach (fun subPath -> InverseCons (0u, subPath)) first

        let tailMaps =
            tail
            |> NEL.fold<_, _>
                (fun (list, index) param ->
                    getParamsMapForEach (fun subPath -> InverseCons (index, subPath)) param
                    :: list,
                    index + 1u)
                (List.empty, 1u)
            |> fst

        combineReferenceMaps (firstMap :: tailMaps)

    | DestructuredTypeVariant (_, params_) ->
        params_
        |> List.mapi (fun i -> getParamsMapForEach (fun subPath -> InverseTypeVariant (uint i, subPath)))
        |> combineReferenceMaps





/// Get all the exposed names from a single assignment pattern
and resolveParamAssignment (assignmentPattern : CstNode<AssignmentPattern>) : ResolvedParams =
    match assignmentPattern.node with
    | Named ident ->
        Map.empty
        |> addNewParamsReference (makeCstNode ident assignmentPattern.source) (SimpleName)

    | Ignored -> Map.empty
    | AssignmentPattern.Unit -> Map.empty
    | Aliased (alias = alias; pattern = pattern) ->
        resolveParamAssignment pattern
        |> addNewParamsReference alias SimpleName

    | DestructuredPattern pattern -> resolveDestructuredParam (makeCstNode pattern assignmentPattern.source)




let resolveFuncParams ({ params_ = params_ } : FunctionValue) : ResolvedParams =
    NEL.map resolveParamAssignment params_
    |> NEL.toList
    |> combineReferenceMaps



let resolveLetBinding ({ bindPattern = bindPattern } : LetBinding) : ResolvedParams = resolveParamAssignment bindPattern


let resolveVariantConstructor
    (typeName : UnqualTypeOrModuleIdentifier)
    (variantCase : VariantCase)
    (map : ResolvedNames)
    : ResolvedNames =
    addNewValueReference
        (mapNode TypeIdentifier variantCase.label)
        (VariantConstructor (typeName, List.map getNode variantCase.contents))
        map


let resolveTypeConstructors
    (name : CstNode<UnqualTypeOrModuleIdentifier>)
    (typeDeclaration : TypeDeclaration)
    : ResolvedNames =
    match typeDeclaration with
    | Alias aliasDecl ->
        // We're not accounting for record alias constructors just yet
        Map.empty
        |> addNewValueReference (mapNode TypeIdentifier name) (TypeRef (Alias aliasDecl))
    | Sum newTypeDecl ->
        newTypeDecl.variants
        |> NEL.fold<_, _>
            (fun map variant -> resolveVariantConstructor name.node variant.node map)
            (addNewValueReference (mapNode TypeIdentifier name) (TypeRef (Sum newTypeDecl)) Map.empty)

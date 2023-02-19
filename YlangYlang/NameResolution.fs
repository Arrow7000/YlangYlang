module NameResolution

open Lexer
open ConcreteSyntaxTree



/// Type that describes the path to where a given name is declared
type PathToDestructuredName =
    | SimpleName
    | InverseRecord
    | InverseTuple of index : uint * child : PathToDestructuredName
    | InverseCons of index : uint * child : PathToDestructuredName
    | InverseTypeVariant of index : uint * child : PathToDestructuredName


/// Map that stores just parameter references.
type ResolvedParams = Map<UnqualValueIdentifier, (TokenWithSource list * PathToDestructuredName) nel>



type ExpressionOrTypeRef =
    | Expr of assignmentPattern : PathToDestructuredName * assignedExpression : CstNode<Expression>
    | VariantConstructor of VariantCase


/// A reference to either a real concrete expression or an assignment parameter
type ValueReference =
    /// Reference a real expression
    | ExpressionRef of ExpressionOrTypeRef
    /// If this assignment pattern is an alias for a greater deconstructed parameter expression
    | AssignmentParam of subPattern : PathToDestructuredName


/// Map that stores references to either parameters or real expressions.
/// The tokens list is about where the *name* is in the source.
type ResolvedValueNames = Map<UnqualIdentifier, (TokenWithSource list * ValueReference) nel>


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
            | Some referenceList -> Some (NEL.cons newValueAndPath referenceList)
            | None -> Some (NEL.make newValueAndPath))
        map


/// Adds a new param to a `ResolvedValueNames` map.
let addNewValueReference
    (ident : CstNode<UnqualIdentifier>)
    (newValue : ValueReference)
    (map : ResolvedValueNames)
    : ResolvedValueNames =
    Map.change
        ident.node
        (fun oldValueOpt ->
            let newValueAndSource = ident.source, newValue

            match oldValueOpt with
            | Some referenceList -> Some (NEL.cons newValueAndSource referenceList)
            | None -> Some (NEL.make newValueAndSource))
        map




let combineReferenceMaps (mapList : Map<'a, 'b nel> list) : Map<'a, 'b nel> =
    let mapFolder (acc : Map<'a, 'b nel>) (key : 'a) (value : 'b nel) : Map<'a, 'b nel> =
        Map.change
            key
            (function
            | Some oldVal -> Some <| NEL.append value oldVal
            | None -> Some value)
            acc

    let listFolder (acc : Map<'a, 'b nel>) (thisMap : Map<'a, 'b nel>) : Map<'a, 'b nel> =
        Map.fold mapFolder thisMap acc

    List.fold listFolder Map.empty mapList



/// I think this is the kind of thing we need for collecting the destructured parts of a single assignment pattern, and this could then be used by `resolveParamAssignment`
let rec resolveDestructuredParam (pattern : CstNode<DestructuredPattern>) : ResolvedParams =
    let getParamsMapForEach
        (putInPath : PathToDestructuredName -> PathToDestructuredName)
        assignmentPattern
        : ResolvedParams =
        resolveParamAssignment assignmentPattern
        |> Map.map (fun _ -> NEL.map (fun (tokens, path) -> tokens, putInPath path))


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

/// @TODO: this obviously doesn't create a guaranteed unique ID, so we should update how we reference identifiers so that this does work correctly
let createUniqueNameForAnonConstructorParams () = System.Guid.NewGuid ()


//let makeTypeConstructor (typeDeclaration : TypeDeclaration) =
//    match typeDeclaration with


(*
@TODO: should assign a new kind of reference from type constructors, the value of which is different to expressions or param aliases, but in fact stores the name of the constructors and also how many and which kinds of parameters each constructor has
*)

let resolveTypeConstructors (typeDeclaration : TypeDeclaration) : ResolvedValueNames =
    match typeDeclaration with
    | Alias _ -> Map.empty // We're not accounting for alias constructors just yet
    //| Alias (name = name) -> addNewValueReference (mapNode TypeIdentifier name)
    | Sum (name = name; variants = variants) ->
        variants
        |> NEL.fold<_, _>
            (fun map variant ->
                addNewValueReference
                    (mapNode TypeIdentifier name)
                    (ExpressionRef <| VariantConstructor variant.node)
                    map)
            Map.empty

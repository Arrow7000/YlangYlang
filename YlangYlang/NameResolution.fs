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


/// Type that describes the path to where a given name is declared.
/// @TODO: hmmm how do we capture the fact that a name is the nth parameter of a function...? Maybe we don't need to actually? Because the name itself references it?
type PathToDestructuredName =
    | SimpleName
    | InverseRecord
    | InverseTuple of index : uint * child : PathToDestructuredName
    | InverseCons of index : uint * child : PathToDestructuredName
    | InverseTypeVariant of constructor : TypeOrModuleIdentifier * index : uint * child : PathToDestructuredName


///// Map that stores just parameter references.
//type ResolvedParams = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * PathToDestructuredName>>



//type ExpressionOrTypeRef =
//    | Expr of assignmentPattern : PathToDestructuredName * assignedExpression : CstNode<Expression>




module ResolvedNames =
    ///// A reference to either a real concrete expression or an assignment parameter
    ///// This should really also let us store the referenced value's declared type
    //type NameReference =
    //    /// Reference a real expression
    //    | ExpressionRef of assignmentPattern : PathToDestructuredName * assignedExpression : CstNode<Expression>
    //    /// If this assignment pattern is an alias for a greater deconstructed parameter expression, or just a function or match expression case parameter
    //    | Parameter of subPattern : PathToDestructuredName
    //    | TypeRef of TypeDeclaration
    //    /// The type name should always be in the same resolved names map
    //    | VariantConstructor of typeName : UnqualTypeOrModuleIdentifier * variantParams : MentionableType list

    ///// Map that stores references to either parameters or real expressions.
    ///// The tokens list is about where the *name* is in the source.
    //type ResolvedNames = Map<UnqualIdentifier, SingleOrDuplicate<TokenWithSource list * NameReference>>



    type UppercaseReference =
        /// A type that has been declared. Could be an alias or a new type.
        | TypeRef of TypeDeclaration
        /// A type constructor.
        /// The type name should always be in the same resolved names map
        | VariantConstructor of typeName : TypeOrModuleIdentifier * variantParams : MentionableType list

    /// For types and type constructors
    type ResolvedUppercaseds = Map<TypeOrModuleIdentifier, SingleOrDuplicate<TokenWithSource list * UppercaseReference>>






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



    /// Contains either the body of a value, a type declaration for a value, or both
    type ValueAndOrTypeDeclaration = EitherOrBoth<CstNode<MentionableType>, CstNode<Expression>>


    type LowercaseReference =
        /// Reference a real expression.
        /// The referenced expression is the same for all the destructured names, but each of the destructured patterns has enough information to figure out a) what type the underlying value needs to have, and b) where in the structure its own assigned value needs to be.
        /// There are for sure more efficient ways of doing this than copying the same expression several times, but let's just do it like this for now.
        | Value of assignmentPattern : PathToDestructuredName * assignedExpression : ValueAndOrTypeDeclaration
        /// If this assignment pattern is an alias for a greater deconstructed parameter expression, or just a function or match expression case parameter
        | Parameter of subPattern : PathToDestructuredName

    /// For simple named values and functions
    type ResolvedLowercaseds = Map<UnqualValueIdentifier, SingleOrDuplicate<TokenWithSource list * LowercaseReference>>


    type ResolvedNames =
        { uppercaseds : ResolvedUppercaseds
          lowercaseds : ResolvedLowercaseds }


    let tryFindUppercased name { uppercaseds = uppercaseds } = Map.tryFind name uppercaseds


    let tryFindLowercased name { lowercaseds = lowercaseds } = Map.tryFind name lowercaseds


    let empty =
        { uppercaseds = Map.empty
          lowercaseds = Map.empty }

    let getLowercaseds { lowercaseds = lowercaseds } = lowercaseds
    let getUppercaseds { uppercaseds = uppercaseds } = uppercaseds


    //let mapLowercaseds f names =
    //    { names with
    //        lowercaseds =
    //            Map.map
    //                (fun key -> SingleOrDuplicate.map (fun (tokens, reference) -> tokens, f key reference))
    //                names.lowercaseds }


    /// This should be threaded back up to feed back on unresolved names errors
    /// Hmmm, I'm not entirely sure whether  this should be passed up, or whether we should resolve all the names at every scope level first, and then only feed things back up if a name can't be resolved.
    type UnresolvedNames = Set<UnqualIdentifier>



    ///// Adds a new param to a `ResolvedParams` map.
    //let addNewParamReference
    //    (ident : CstNode<UnqualValueIdentifier>)
    //    (path : PathToDestructuredName)
    //    (names : ResolvedNames)
    //    : ResolvedNames =
    //    let newLowerCaseds =
    //        Map.change
    //            (ident.node)
    //            (fun oldValueOpt ->
    //                let newValueAndPath = ident.source, Parameter path

    //                match oldValueOpt with
    //                | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
    //                | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
    //                | None -> Some (Single newValueAndPath))
    //            names.lowercaseds

    //    { names with lowercaseds = newLowerCaseds }


    let addNewLowercasedReference
        (ident : CstNode<UnqualValueIdentifier>)
        (lowercaseRef : LowercaseReference)
        (names : ResolvedNames)
        : ResolvedNames =
        let newLowerCaseds =
            names.lowercaseds
            |> Map.change ident.node (fun oldValueOpt ->
                let newValueAndPath = ident.source, lowercaseRef

                match oldValueOpt with
                | Some (Single ((tokens, ref) as oldRef)) ->
                    let duplicate = Some (Duplicate <| TOM.make newValueAndPath oldRef)

                    // Logic for allowing the adding of type declarations to a value declaration of the same name - and vice versa - without overwriting anything
                    match ref, lowercaseRef with
                    | Value (pattern, expr), Value (_, newRef) ->
                        match expr, newRef with
                        | (OnlyLeft oldType, OnlyRight newVal) ->
                            Some (Single (tokens, Value (pattern, Both (oldType, newVal))))

                        | (OnlyRight oldVal, OnlyLeft newType) ->
                            Some (Single (tokens, Value (pattern, Both (newType, oldVal))))

                        | _ -> duplicate

                    | _ -> duplicate


                | Some (Duplicate refList) ->
                    // We kind of just don't even try to merge the value and type declaration if there are already duplicates, but really we should do that here
                    Some (Duplicate <| TOM.cons newValueAndPath refList)
                | None -> Some (Single newValueAndPath))

        { names with lowercaseds = newLowerCaseds }


    //let addNewParamReference ident path names =
    //    addNewLowercasedReference ident (Parameter path) names



    let addNewUppercasedReference
        (ident : CstNode<TypeOrModuleIdentifier>)
        (uppercaseRef : UppercaseReference)
        (names : ResolvedNames)
        : ResolvedNames =
        let newUpperCaseds =
            Map.change
                (ident.node)
                (fun oldValueOpt ->
                    let newValueAndPath = ident.source, uppercaseRef

                    match oldValueOpt with
                    | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
                    | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
                    | None -> Some (Single newValueAndPath))
                names.uppercaseds

        { names with uppercaseds = newUpperCaseds }



///// Adds a new value to a `ResolvedValueNames` map.
//let addNewValueReference
//    (ident : CstNode<UnqualIdentifier>)
//    (newValue : NameReference)
//    (names : ResolvedNames)
//    : ResolvedNames =
//    Map.change
//        ident.node
//        (fun oldValueOpt ->
//            let newValueAndSource = ident.source, newValue

//            match oldValueOpt with
//            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndSource oldRef)
//            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndSource refList)
//            | None -> Some (Single newValueAndSource))
//        names


//let addNewNameReference
//    (ident : CstNode<UnqualIdentifier>)
//    (newValue : NameReference)
//    (names : ResolvedNames)
//    : ResolvedNames =
//    Map.change
//        ident.node
//        (fun oldValueOpt ->
//            let newValueAndSource = ident.source, newValue

//            match oldValueOpt with
//            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndSource oldRef)
//            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndSource refList)
//    | None -> Some (Single newValueAndSource))
//names




open ResolvedNames

(*
The head is always the closest scope, so pop it off when we leave a given scope
*)

type NamesInScope = ResolvedNames list


///// Adds a new param to a `ResolvedParams` map.
//let addNewParamsReference
//    (ident : CstNode<UnqualValueIdentifier>)
//    (path : PathToDestructuredName)
//    (map : ResolvedParams)
//    : ResolvedParams =
//    Map.change
//        ident.node
//        (fun oldValueOpt ->
//            let newValueAndPath = ident.source, path

//            match oldValueOpt with
//            | Some (Single oldRef) -> Some (Duplicate <| TOM.make newValueAndPath oldRef)
//            | Some (Duplicate refList) -> Some (Duplicate <| TOM.cons newValueAndPath refList)
//            | None -> Some (Single newValueAndPath))
//        map




///// @TODO: Hmm I'm not actually sure that we ever should be combining reference maps... actually maybe with the new approach where we're only getting the map one layer deep at a time then yeah maybe?
//let combineReferenceMaps (mapList : Map<'a, SingleOrDuplicate<'b>> seq) : Map<'a, SingleOrDuplicate<'b>> =
//    let mapFolder
//        (acc : Map<'a, SingleOrDuplicate<'b>>)
//        (key : 'a)
//        (value : SingleOrDuplicate<'b>)
//        : Map<'a, SingleOrDuplicate<'b>> =
//        Map.change
//            key
//            (fun oldValueOpt ->
//                match oldValueOpt with
//                | Some oldVal ->
//                    match oldVal, value with
//                    | Single oldRef, Single newRef -> Some (Duplicate <| TOM.make newRef oldRef)

//                    | Single singleRef, Duplicate duplRefs
//                    | Duplicate duplRefs, Single singleRef -> Some (Duplicate <| TOM.cons singleRef duplRefs)

//                    | Duplicate a, Duplicate b -> Some (Duplicate <| TOM.append a b)

//                | None -> Some value)
//            acc

//    //let listFolder
//    //    (acc : Map<'a, SingleOrDuplicate<'b>>)
//    //    (thisMap : Map<'a, SingleOrDuplicate<'b>>)
//    //    : Map<'a, SingleOrDuplicate<'b>> =
//    //    Map.fold mapFolder thisMap acc

//    //Seq.fold listFolder Map.empty mapList
//    Seq.fold (fun acc thisMap -> Map.fold mapFolder thisMap acc) Map.empty mapList


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
    let mergeLowercasedMaps
        (acc : ResolvedLowercaseds)
        key
        (value : SingleOrDuplicate<TokenWithSource list * LowercaseReference>)
        : ResolvedLowercaseds =
        Map.change
            key
            (fun oldValueOpt ->
                match oldValueOpt with
                | Some oldVal ->
                    match oldVal, value with
                    | Single ((tokens, oldLowercaseRef) as oldRef), Single ((_, newLowercaseRef) as newRef) ->
                        let duplicate = Some (Duplicate <| TOM.make newRef oldRef)

                        // Logic for allowing the adding of type declarations to a value declaration of the same name - and vice versa - without overwriting anything
                        match oldLowercaseRef, newLowercaseRef with
                        | Value (pattern, expr), Value (_, newRef') ->
                            match expr, newRef' with
                            | (OnlyLeft oldType, OnlyRight newVal) ->
                                Some (Single (tokens, Value (pattern, Both (oldType, newVal))))

                            | (OnlyRight oldVal, OnlyLeft newType) ->
                                Some (Single (tokens, Value (pattern, Both (newType, oldVal))))

                            | _ -> duplicate

                        | _ -> duplicate

                    // We kind of just don't even try to merge the value and type declaration if there are already duplicates, but really we should do that here

                    | Single singleRef, Duplicate duplRefs
                    | Duplicate duplRefs, Single singleRef -> Some (Duplicate <| TOM.cons singleRef duplRefs)

                    | Duplicate a, Duplicate b -> Some (Duplicate <| TOM.append a b)

                | None -> Some value)
            acc

    //Seq.fold (fun acc thisMap -> Map.fold mapFolder thisMap acc) Map.empty mapList
    let uppercaseds = Seq.map getUppercaseds mapList
    let lowercaseds = Seq.map getLowercaseds mapList

    { uppercaseds = combineReferenceMaps uppercaseds
      lowercaseds = Seq.fold (fun acc thisMap -> Map.fold mergeLowercasedMaps thisMap acc) Map.empty lowercaseds }

//Seq.fold (fun acc thisMap -> Map.fold mapFolder thisMap acc) Map.empty mapList




/// This is for straight converting a params map to a values map, but _not_ suitable for converting a
let convertParamsToValuesMap (resolvedParams : ResolvedParams) : ResolvedNames =
    { ResolvedNames.empty with
        lowercaseds =
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
    //NEL.map resolveParamAssignment params_
    //|> NEL.toList
    //|> combineReferenceMaps

    let lowercaseds : ResolvedLowercaseds =
        params_
        |> NEL.map (
            resolveParamAssignment
            >> Map.map (fun _ tokensAndValues ->
                tokensAndValues
                |> SingleOrDuplicate.map (fun (tokens, path) -> tokens, Parameter path))
        )
        |> NEL.toList
        |> combineReferenceMaps

    { ResolvedNames.empty with lowercaseds = lowercaseds }


let resolveLetBinding
    ({ bindPattern = bindPattern
       value = value } : LetBinding)
    : ResolvedNames =
    let lowercaseds : ResolvedLowercaseds =
        resolveParamAssignment bindPattern
        |> Map.map (fun _ tokensAndValues ->
            tokensAndValues
            |> SingleOrDuplicate.map (fun (tokens, path) ->
                tokens, Value (assignmentPattern = path, assignedExpression = OnlyRight value)))

    { ResolvedNames.empty with lowercaseds = lowercaseds }


let private resolveVariantConstructor
    (typeName : TypeOrModuleIdentifier)
    (variantCase : VariantCase)
    (names : ResolvedNames)
    : ResolvedNames =
    addNewUppercasedReference
        (mapNode UnqualType variantCase.label)
        (VariantConstructor (typeName, List.map getNode variantCase.contents))
        names


let resolveTypeConstructors
    (name : CstNode<UnqualTypeOrModuleIdentifier>)
    (typeDeclaration : TypeDeclaration)
    : ResolvedNames =

    match typeDeclaration with
    | Alias aliasDecl ->
        // We're not accounting for record alias constructors just yet
        ResolvedNames.empty
        |> addNewUppercasedReference (mapNode UnqualType name) (TypeRef (Alias aliasDecl))

    | Sum newTypeDecl ->
        newTypeDecl.variants
        |> NEL.fold<_, _>
            (fun map variant -> resolveVariantConstructor (UnqualType name.node) variant.node map)
            (addNewUppercasedReference (mapNode UnqualType name) (TypeRef (Sum newTypeDecl)) ResolvedNames.empty)





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
        | LetExpression (bindings, _) ->
            bindings
            |> NEL.toList
            |> Seq.map (getNode >> resolveLetBinding)
            |> combineResolvedNamesMaps

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
            |> addNewLowercasedReference valueName (Value (SimpleName, OnlyLeft annotatedType))

        | ValueDeclaration { valueName = valueName; value = value } ->
            ResolvedNames.empty
            |> addNewLowercasedReference valueName (Value (SimpleName, OnlyRight value))

    ylModule.declarations
    |> List.map resolveSingleDeclaration
    |> combineResolvedNamesMaps

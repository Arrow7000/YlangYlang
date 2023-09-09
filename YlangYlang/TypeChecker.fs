module TypeChecker


open Lexer


module Cst = ConcreteSyntaxTree
module S = SyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open Q.Names
open TypedSyntaxTree

module NameRes = TypedNameResolution


(*

@TODO list:

- [ ] resolve named values
    - [ ] in local scopes
    - [ ] from other modules
- [ ] infer types of primitives
- [ ] infer types of values referencing primitives
- [ ] infer types of

- [ ] parse type annotations
- [ ] infer types of values or function params by looking at the functions they are getting passed into
    - [ ] and similarly the types of values passed to operators

- [ ] support flagging up type clashes
    - [ ] and have some way of linking that back to a specific token, or even buffer range?

- [ ] support types with type params, e.g. `List a`
- [ ] support narrowing of types with type params while leaving the type params as generic

- [ ] support a parallel, field-name-and-value-based, type inference system to support typed records as extensible, partially typed things, instead of the all or nothing type system of generics vs explicit types specified above

*)













let reifyModuleName (QualifiedModuleOrTypeIdentifier moduleName) : ModulePath =
    moduleName
    |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
    |> ModulePath

let reifyUpper
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (UnqualTypeOrModuleIdentifier topLevelIdent)
    : FullyQualifiedUpperIdent =
    FullyQualifiedUpperIdent (reifyModuleName moduleName, UpperIdent topLevelIdent)

let reifyLower
    (moduleName : QualifiedModuleOrTypeIdentifier)
    (UnqualValueIdentifier topLevelIdent)
    : FullyQualifiedTopLevelLowerIdent =
    FullyQualifiedTopLevelLowerIdent (reifyModuleName moduleName, LowerIdent topLevelIdent)



let unqualValToRecField (UnqualValueIdentifier str) = RecordFieldName str
let unqualValToLowerIdent (UnqualValueIdentifier str) = LowerIdent str

let unqualValToLowerName (UnqualValueIdentifier str) = LowerIdent str |> LocalLower

let recFieldToLowerIdent (RecordFieldName str) = LowerIdent str
let lowerIdentToRecFieldName (LowerIdent ident) = RecordFieldName ident

let lowerIdentToUnqualVal (LowerIdent str) = UnqualValueIdentifier str

let unqualTypeToUpperIdent (UnqualTypeOrModuleIdentifier label) = UpperIdent label


let convertRecordMapFields map =
    Map.mapKeyVal (fun key v -> S.mapNode unqualValToRecField key, v) map



let private convertTypeOrModuleIdentifierToIdentifier : TypeOrModuleIdentifier -> Identifier =
    function
    | QualifiedType ident -> ModuleSegmentsOrQualifiedTypeOrVariant ident
    | UnqualType ident -> TypeNameOrVariantOrTopLevelModule ident


let private convertValueIdentifierToIdentifier : ValueIdentifier -> Identifier =
    function
    | QualifiedValue ident -> QualifiedPathValueIdentifier ident
    | UnqualValue ident -> SingleValueIdentifier ident



let private convertValueIdentifierToLowerName : ValueIdentifier -> LowerNameValue =
    function
    | QualifiedValue (QualifiedValueIdentifier (path, valIdent)) ->
        reifyLower (QualifiedModuleOrTypeIdentifier path) valIdent
        |> FullyQualifiedLower
    | UnqualValue ident -> unqualValToLowerIdent ident |> LocalLower


let private moduleNameToModulePath (QualifiedModuleOrTypeIdentifier moduleIdent) : ModulePath =
    moduleIdent
    |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)
    |> ModulePath


let private getModulePath (moduleCtx : Cst.YlModule) : ModulePath =
    moduleNameToModulePath moduleCtx.moduleDecl.moduleName.node




let typeOrModuleIdentToUpperNameVal : Lexer.TypeOrModuleIdentifier -> UpperNameValue =
    function
    | Lexer.QualifiedType (QualifiedModuleOrTypeIdentifier path) ->
        let (moduleSegments, UnqualTypeOrModuleIdentifier ident) = NEL.peelOffLast path

        let modulePath =
            moduleSegments
            |> NEL.map (fun (UnqualTypeOrModuleIdentifier segment) -> segment)

        FullyQualifiedUpperIdent (ModulePath modulePath, UpperIdent ident)
        |> FullyQualifiedUpper

    | Lexer.UnqualType (UnqualTypeOrModuleIdentifier ident) -> UpperIdent ident |> LocalUpper





let getParamFromPattern (pattern : FunctionOrCaseMatchParam) = pattern.paramPattern

/// Lil helper function for converting to arrow type
let rec makeDestType (NEL (first, rest)) =
    match rest with
    | [] -> first
    | head :: tail ->
        DtArrow (first, makeDestType (NEL.new_ head tail))
        |> TypeConstraints.fromDefinitive


let unifyTypeErrors (errA : TypeError) (errB : TypeError) : TypeError =
    match errA, errB with
    | UnprunedRecursion, other
    | other, UnprunedRecursion -> other
    | IncompatibleTypes a, IncompatibleTypes b -> IncompatibleTypes (a @ b)

let addDefToTypeError def err =
    match err with
    | UnprunedRecursion -> UnprunedRecursion
    | IncompatibleTypes types -> IncompatibleTypes (def :: types)


let concatResultErrListNelOrig (result : Result<'a, 'Err list nel>) : Result<'a, 'Err list> =
    Result.mapError (NEL.toList >> List.concat) result


let combineTypeErrorsFromNel ((NEL (head, tail)) : TypeError nel) : TypeError = List.fold unifyTypeErrors head tail

let combineTypeErrorsFromList (list : TypeError list) : TypeError =
    match list with
    | [] -> IncompatibleTypes []
    | head :: tail -> List.fold unifyTypeErrors head tail

let concatResultErrListNel (result : Result<'a, TypeError nel>) : Result<'a, TypeError> =
    Result.mapError combineTypeErrorsFromNel result
























/// @TODO: this needs to be fixed now that `Constrained` types no longer just refer to generically typed params, but also to references to concrete values defined elsewhere!
/// Not entirely sure yet how to do this without having to pass in names maps to this function, which I don't want to do, because of the circular definition problem (i.e. in a let bindings list all values can reference all others, even ones defined after itself, so we can't type check each value in isolation but have to "convert" them to type checked values all at once, and the only way we can do that is by allowing a type of an expression to be a reference to "whatever the type of value X is")
let rec unifyTypeConstraints (typeA : TypeConstraints) (typeB : TypeConstraints) : TypeJudgment =
    match typeA, typeB with
    | Constrained (Some defA, cnstrntsA), Constrained (Some defB, cnstrntsB) ->
        unifyDefinitiveTypes defA defB
        |> Result.map (fun unified -> Constrained (Some unified, Set.union cnstrntsA cnstrntsB))

    | Constrained (Some def, cnstrntsA), Constrained (None, cnstrntsB)
    | Constrained (None, cnstrntsA), Constrained (Some def, cnstrntsB) ->
        Constrained (Some def, Set.union cnstrntsA cnstrntsB)
        |> Ok

    | Constrained (None, cnstrntsA), Constrained (None, cnstrntsB) ->
        Constrained (
            None,
            // @TODO: this may not be a simple union of reference constraints, they need to be unified with their own unifier function!
            Set.union cnstrntsA cnstrntsB
        )
        |> Ok





/// @TODO: remember to resolve named types to check for unification, e.g. with named alias type and record
and unifyDefinitiveTypes (typeA : DefinitiveType) (typeB : DefinitiveType) : Result<DefinitiveType, TypeError> =
    match typeA, typeB with
    | DtTuple a, DtTuple b ->
        unifyTypesTom a b
        |> Result.mapError (fun (first, second) ->
            TypeError.fromTypes [ DtTuple first
                                  DtTuple second ])
        |> Result.bind (TOM.sequenceResult >> concatResultErrListNel)
        |> Result.map DtTuple

    | DtList a, DtList b -> unifyTypeConstraints a b |> Result.map DtList

    | DtArrow (fromA, toA), DtArrow (fromB, toB) ->
        (unifyTypeConstraints fromA fromB, unifyTypeConstraints toA toB)
        ||> Result.map2
                (fun fromType toType -> DtArrow (fromType, toType))
                (fun _ _ ->
                    TypeError.fromTypes [ DtArrow (fromA, toA)
                                          DtArrow (fromB, toB) ])
    //let unifiedToTypes =
    //    unifyTypesNel toA toB
    //    |> Result.mapError (fun _ ->
    //        TypeError.fromTypes [ DtArrow (fromA, toA)
    //                              DtArrow (fromB, toB) ])
    //    |> Result.bind (NEL.sequenceResult >> concatResultErrListNel)

    //(unifyTypeConstraints fromA fromB, unifiedToTypes)
    //||> Result.map2
    //        (fun fromType toTypes_ -> DtArrow (fromType, toTypes_))
    //        (fun _ _ ->
    //            TypeError.fromTypes [ DtArrow (fromA, toA)
    //                                  DtArrow (fromB, toB) ])

    | DtNewType (typeRefA, typeParamsA), DtNewType (typeRefB, typeParamsB) ->
        if typeRefA = typeRefB then
            unifyTypesList (List.map snd typeParamsA) (List.map snd typeParamsB)
            |> Result.mapError (fun _ -> TypeError.fromTypes [ typeA; typeB ])
            |> Result.bind (Result.sequenceList >> concatResultErrListNel)
            |> Result.map (fun unifiedParams -> DtNewType (typeRefA, List.zip (List.map fst typeParamsA) unifiedParams))

        else
            Error <| TypeError.fromTypes [ typeA; typeB ]

    | DtRecordExact a, DtRecordExact b ->
        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
        |> Result.mapError (fun _ ->
            TypeError.fromTypes [ DtRecordExact a
                                  DtRecordExact b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (
                Map.values
                >> Seq.toList
                >> combineTypeErrorsFromList
            )
        )
        |> Result.map DtRecordExact

    | DtRecordWith a, DtRecordWith b ->
        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
        |> Result.mapError (fun _ ->
            TypeError.fromTypes [ DtRecordWith a
                                  DtRecordWith b ])
        |> Result.bind (
            Map.sequenceResult
            >> Result.mapError (
                Map.values
                >> Seq.toList
                >> combineTypeErrorsFromList
            )
        )
        |> Result.map DtRecordExact

    | DtRecordExact a, DtRecordWith b
    | DtRecordWith b, DtRecordExact a -> failwith "@TODO: unify record and extended record types when compatible"

    | DtUnitType, DtUnitType -> DtUnitType |> Ok
    | DtPrimitiveType a, DtPrimitiveType b ->
        if a = b then
            DtPrimitiveType a |> Ok
        else
            TypeError.fromTypes [ DtPrimitiveType a
                                  DtPrimitiveType b ]
            |> Error

    | _, _ -> Error <| TypeError.fromTypes [ typeA; typeB ]





//and getConstrainedValues (constraintsList : TypeConstraints list) : Map<LowerNameValue, TypeJudgment> =
//    constraintsList
//    |> List.fold
//        (fun map constrainedValue ->

//            match constrainedValue with
//            | TypeConstraints (def, others) ->

//                let setFolder (state: (LowerNameValue set * TypeJudgment)) (constrainType: ConstrainType) =
//                    match constrainType with
//                    | ByValue name ->
//                        match Map.tryFind name state with
//                        | None -> Map.add name (Ok (TypeConstraints (def, others))) state

//                        | Some constraintsForName -> Map.add name (unifyJudgments (Ok constrainedValue) constraintsForName) state


//                    | _ -> state


//                let combinedFromOthers = Set.fold setFolder map others

//            //| Recursive ->
//            )
//        Map.empty


///// @TODO: this should basically allow for shrinking the referenced constraints and maybe unifying the concrete constraints, in the case when a name becomes available for resolution
//and concretiseConstraintValue (name : LowerNameValue) (constraints : TypeConstraints) : TypeJudgment =
//    let tryConcretiseSingleConstraintAndAdd
//        (constrainType : ConstrainType)
//        (typeConstraints : TypeConstraints)
//        : TypeJudgment =
//        match constrainType with
//        | ByValue valName ->
//            if name = valName then
//                Ok Recursive
//            else
//                unifyTypeConstraints typeOfName typeConstraints

//        | _ -> unifyTypeConstraints typeOfName typeConstraints

//    match constraints with
//    | Recursive -> Ok Recursive
//    | TypeConstraints (def, constraintSet) ->
//        let state : TypeConstraints =
//            Option.map TypeConstraints.makeFromDefinitive def
//            |> Option.defaultValue TypeConstraints.empty


//        constraintSet
//        |> Set.fold
//            (fun result constrainType -> Result.bind (tryConcretiseSingleConstraintAndAdd constrainType) result)
//            (Ok state)


/// If lengths are the same, returns a list of that length of the type judgments of trying to merge the type at every index in both lists. If lengths are not the same though, returns an error result of both inferred types lists.
and private listTraverser (onLengthErr : 'Err) (listA : TypeConstraints list) (listB : TypeConstraints list) =
    match listA, listB with
    | [], [] -> Ok []
    | headA :: tailA, headB :: tailB ->
        let unifiedHead = unifyTypeConstraints headA headB

        listTraverser onLengthErr tailA tailB
        |> Result.map (fun unifiedTail -> unifiedHead :: unifiedTail)

    | [], _ :: _
    | _ :: _, [] -> Error onLengthErr



and unifyTypesList
    (listA : TypeConstraints list)
    (listB : TypeConstraints list)
    : Result<TypeJudgment list, TypeConstraints list * TypeConstraints list> =
    listTraverser (listA, listB) listA listB

and unifyTypesNel
    (NEL (headA, tailA) as nelA : TypeConstraints nel)
    (NEL (headB, tailB) as nelB : TypeConstraints nel)
    : Result<TypeJudgment nel, TypeConstraints nel * TypeConstraints nel> =
    listTraverser (nelA, nelB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyTypeConstraints headA headB
        NEL (unifiedHead, unifiedTail))



and unifyTypesTom
    (TOM (headA, neckA, tailA) as listA : TypeConstraints tom)
    (TOM (headB, neckB, tailB) as listB : TypeConstraints tom)
    : Result<TypeJudgment tom, TypeConstraints tom * TypeConstraints tom> =
    listTraverser (listA, listB) tailA tailB
    |> Result.map (fun unifiedTail ->
        let unifiedHead = unifyTypeConstraints headA headB
        let unifiedNeck = unifyTypeConstraints neckA neckB
        TOM (unifiedHead, unifiedNeck, unifiedTail))




/// If both judgments are ok it unifies their constraints. Otherwise it adds any concrete types to the errors list, or combines errors.
///
/// @TODO: this should really also include the other `ConstrainType`s that can be resolved and evaluate to definitive types in case some of them are also incompatible with the other constraints
and unifyJudgments (judgmentA : TypeJudgment) (judgmentB : TypeJudgment) =
    match judgmentA, judgmentB with
    | Ok a, Ok b -> unifyTypeConstraints a b

    | Error err, Ok (Constrained (Some t, _))
    | Ok (Constrained (Some t, _)), Error err ->
        unifyTypeErrors (TypeError.fromTypes [ t ]) err
        |> Error

    | Error e, Ok (Constrained (None, _))
    | Ok (Constrained (None, _)), Error e -> Error e

    | Error a, Error b -> unifyTypeErrors a b |> Error

//| Error e, Ok Recursive
//| Ok Recursive, Error e -> Error e





and unifyDefinitiveJudgments
    (judgmentA : Result<DefinitiveType, TypeError>)
    (judgmentB : Result<DefinitiveType, TypeError>)
    : Result<DefinitiveType, TypeError> =
    match judgmentA, judgmentB with
    | Ok a, Ok b -> unifyDefinitiveTypes a b

    | Ok a, Error e
    | Error e, Ok a -> addDefToTypeError a e |> Error

    | Error a, Error b -> unifyTypeErrors a b |> Error







module TypeConstraints =

    let addConstraint (newConstraint : RefConstr) (constraints : TypeConstraints) : TypeConstraints =
        match constraints with
        | Constrained (def, cnstrnts) -> Constrained (def, Set.add newConstraint cnstrnts)
    //| Recursive ->
    //    // This tries to represent the logic for a recursive function that contains a base case: i.e. if one branch calls the function recursively but the other branch returns a non-recursive value with a type that can be inferred concretely, then the inferred type is that of the base case and the recursive branch is irrelevant to the type of the expression.
    //    //
    //    // @TODO: However this probably does not work for non-function *values*, which unlike functions cannot be referenced recursively in their own definitions (unless it is referenced inside a function) because otherwise evaluating itself will instantly cause an infinite expansion and a stack overflow. So we probably need a different way to express recursiveness in a non-function value so that we do return an error, and don't just throw away the recursiveness information.
    //    // We actually need to be able to represent 2 things:
    //    // - The fact that an expression calls itself with no base case
    //    // - The fact that an expression calls itself with no parameters in the middle to halt the immediate expansion
    //    //
    //    // But actually these two things are one and the same: the fact that an expression references itself without changing any of the parameters it feeds to itself! This is true not just for functions that do not have a base case at all, but even for functions that call themselves without changing any of their parameters – which would also result in an infinite loop – and also values that reference themselves without being functions with parameters in the middle – because those also technically have "no changed parameters" because a non-function value can still be thought of as a function, just with a list of parameters 0 items in length. And referencing itself therefore qualifies as "not changing the parameters it feeds itself" because every empty list is the same as any other!

    //    TypeConstraints.fromConstraint newConstraint


    let addDefinitiveType (newDef : DefinitiveType) (constraints : TypeConstraints) : TypeJudgment =
        match constraints with
        | Constrained (def, cnstrnts) ->
            match def with
            | None -> Constrained (Some newDef, cnstrnts) |> Ok
            | Some def_ ->
                let unifiedResult = unifyDefinitiveTypes def_ newDef

                unifiedResult
                |> Result.map (fun unified -> Constrained (Some unified, cnstrnts))














/// Converts a "mentionable type" representing a type expression to a TypeConstraints representing our internal type representation.
/// It has to be a type constraint and not a definitive type because we need to take into consideration type params (which may not be declared) and references to type names (which may not exist)
let rec mentionableTypeToDefinite (mentionable : Cst.MentionableType) : TypeConstraints =
    match mentionable with
    | S.UnitType -> TypeConstraints.fromDefinitive DtUnitType
    | S.GenericTypeVar unqual ->
        unqualValToLowerIdent unqual
        |> ByTypeParam
        |> TypeConstraints.fromConstraint

    | S.Tuple { types = types } ->
        types
        |> TOM.map (S.getNode >> mentionableTypeToDefinite)
        |> DtTuple
        |> TypeConstraints.fromDefinitive

    | S.Record { fields = fields } ->
        fields
        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
        |> DtRecordExact
        |> TypeConstraints.fromDefinitive

    | S.ExtendedRecord { extendedTypeParam = extendedParam
                         fields = fields } ->
        // TODO: ensure that we actually try to resolve the extended param at some point so that we type this type expression correctly

        fields
        |> Map.mapKeyVal (fun key value -> unqualValToRecField key.node, mentionableTypeToDefinite value.node)
        |> DtRecordWith
        |> TypeConstraints.fromDefinitive

    | S.ReferencedType (typeName, typeParams) ->
        let definiteTypeParams =
            List.map (S.getNode >> mentionableTypeToDefinite) typeParams

        IsOfTypeByName (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
        |> TypeConstraints.fromConstraint

    | S.Arrow (fromType, toTypes) ->
        DtArrow (
            mentionableTypeToDefinite fromType.node,
            NEL.map S.getNode toTypes
            |> mentionableArrowToDefinite
        )
        |> TypeConstraints.fromDefinitive

    | S.Parensed parensed -> mentionableTypeToDefinite parensed.node


/// Converts an NEL representing one or more destination types in an arrow type to a single type
and private mentionableArrowToDefinite (toTypes : Cst.MentionableType nel) : TypeConstraints =
    let (NEL (first, rest)) = toTypes
    let convertedFirst = mentionableTypeToDefinite first

    match rest with
    | [] -> convertedFirst
    | head :: tail ->
        DtArrow (convertedFirst, mentionableArrowToDefinite (NEL (head, tail)))
        |> TypeConstraints.fromDefinitive









//type FlatOpList<'a> =
//    | LastVal of 'a
//    | Op of left : 'a * op : Lexer.BuiltInOperator * right : FlatOpList<'a>


//let rec opSeqToFlatOpList
//    (leftOperand : Cst.Expression)
//    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
//    : FlatOpList<Cst.Expression> =
//    let (NEL ((firstOp, sndExpr), rest)) = opSequence

//    Op (
//        leftOperand,
//        firstOp,
//        (match rest with
//         | [] -> LastVal sndExpr
//         | headOfRest :: restOfRest -> opSeqToFlatOpList sndExpr (NEL.new_ headOfRest restOfRest))
//    )


///// @TODO: this currently only supports built-in operators, not custom ones
//type OpBinaryTree =
//    { left : BinaryTreeBranch
//      op : Lexer.BuiltInOperator
//      right : BinaryTreeBranch }


//and BinaryTreeBranch =
//    | Branch of OpBinaryTree
//    | Leaf of Cst.Expression




//let updateLastInList updater list =
//    List.rev list
//    |> (function
//    | [] -> []
//    | head :: rest -> updater head :: rest)
//    |> List.rev


//let updateOrAddIfEmpty updater toAdd list =
//    List.rev list
//    |> (function
//    | [] -> [ toAdd ]
//    | head :: rest -> updater head :: rest)
//    |> List.rev


//type ExprWithOpsList<'a> = | ExprWithOpsList of 'a * (BuiltInOperator * 'a) list



//type SplitLists<'a> = ExprWithOpsList<ExprWithOpsList<'a>>


//let newExprWithOpsList a = ExprWithOpsList (a, List.empty)

//let addToExprWithOpsList toAdd (ExprWithOpsList (a, list)) =
//    ExprWithOpsList (a, list @ [  toAdd ])


//let editLastInExprWithOpsList  toAdd (ExprWithOpsList (a, list): SplitLists<Cst.Expression>) =
//    ExprWithOpsList (a, updateOrAddIfEmpty (addToExprWithOpsList  toAdd) list)



//type FoldSuccess<'a> =
//    { lastOperand : 'a
//      listsSoFar : SplitLists<'a>
//      /// This should contain the lowest precedence other than the one we are currently looking at
//      lowestPrecedence : int option
//      associativity : S.InfixOpAssociativity option }



//let rec splitOpList
//    (precedence : int)
//    (firstOperand : Cst.Expression)
//    (opSeq : (Lexer.BuiltInOperator * Cst.Expression) list)
//    =
//    let initState : FoldSuccess<Cst.Expression> =
//        { lastOperand = firstOperand
//          listsSoFar =
//            newExprWithOpsList firstOperand
//            |> newExprWithOpsList
//          lowestPrecedence = None
//          associativity = None }

//    opSeq
//    |> List.fold<_, FoldSuccess<Cst.Expression>>
//        (fun state (op, expr) ->
//            let op_ = NameResolution.getBuiltInInfixOp op

//            if op_.precedence <= precedence then
//                match state.associativity with
//                | Some assoc ->
//                    match assoc with
//                    | S.Non ->
//                        failwith "@TODO: error! can't have more than one operator with non associativity without parens"
//                    | S.Left
//                    | S.Right ->
//                        if op_.associativity = assoc then
//                            let newLists = addToExprWithOpsList op (newExprWithOpsList expr) state.listsSoFar

//                            { lastOperand = expr
//                              listsSoFar = newLists
//                              lowestPrecedence = state.lowestPrecedence
//                              associativity = Some assoc }

//                        else
//                            failwith
//                                "@TODO: can't have more than one operator at the same level with different associativity. Need to group the expressions in parentheses!"

//                | None ->
//                    let newLists = addToExprWithOpsList op (newExprWithOpsList expr) state.listsSoFar

//                    { lastOperand = expr
//                      listsSoFar = newLists
//                      lowestPrecedence = state.lowestPrecedence
//                      associativity = Some op_.associativity }


//            else
//                // add to current list + keep track if operator is lower than the current lowest one?

//                let newLists = editLastInExprWithOpsList

//            )
//        initState



////let rec processListRecursively firstOperand (opSeq : (Lexer.BuiltInOperator * Cst.Expression) nel)
////    let splitList = splitOpList 0 opSeq



/////// Splits the operator list according to precedence and associativity
////let rec splitOpList currPrecedence (opSeq : (Lexer.BuiltInOperator * Cst.Expression) nel) =
////    match opSeq with
////    | NEL ((op, expr), []) -> Last (op, expr)
////    | NEL ((op, expr), head :: rest) ->
////        let op_ = NameResolution.getBuiltInInfixOp op

////        let newNel = NEL.new_ head rest

////        if op_.precedence <= currPrecedence then
////            New ((op, expr), splitOpList currPrecedence newNel)
////        else
////            Continue ((op, expr), splitOpList currPrecedence newNel)



////let rec splitOpSeqs (currPrecedence : int) (opSeq : FlatOpList<Cst.Expression>) : PartialOrFull<Cst.Expression> =
////    match opSeq with
////    | LastVal e -> Leaf e
////    | Op (left, op, right) ->
////        let op_ = NameResolution.getBuiltInInfixOp op

////        if op_.precedence <= currPrecedence then
////            LastVal left





////let rec normaliseOpSequence (currPrecedence:int)
////    (leftOperand : Cst.Expression)
////    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
////    : OpBinaryTree =
////    let (NEL ((firstOp, sndExpr), rest)) = opSequence

////    let op = NameResolution.getBuiltInInfixOp firstOp

////    match rest with
////    | [] ->
////        { left = Leaf leftOperand
////          op = firstOp
////          right = Leaf sndExpr }

////    | headOfRest :: restOfRest ->
////        if op.precedence <= currPrecedence then
////            match op.associativity with
////            | S.Non ->
////                { left = normaliseOpSequence
////                  op = firstOp
////                  right = normaliseOpSequence


////let rec normaliseOpSequence
////    (leftOperand : BinaryTreeBranch)
////    (opSequence : (Lexer.BuiltInOperator * Cst.Expression) nel)
////    : OpBinaryTree =
////    let (NEL ((firstOp, sndExpr), rest)) = opSequence
////    let op = NameResolution.getBuiltInInfixOp firstOp

////    match leftOperand, rest with
////    | Leaf leftExpr, [] ->
////        { left = Leaf leftExpr
////          op = firstOp
////          highestPrecedence = op.precedence
////          right = Leaf sndExpr }

////    | Leaf leftExpr, headOfRest :: restOfRest ->
////        { left = Leaf leftExpr
////          op = firstOp
////          highestPrecedence = op.precedence
////          right =
////            normaliseOpSequence (Leaf sndExpr) (NEL.new_ headOfRest restOfRest)
////             }

////    | Branch leftTree, [] ->
////        { left = Branch leftTree
////          op = firstOp
////          highestPrecedence = op.precedence
////          right = Leaf sndExpr }


////    | Branch leftTree, headOfRest :: restOfRest ->
////        let rightTree = normaliseOpSequence (Leaf sndExpr) (NEL.new_ headOfRest restOfRest)

////        if op.precedence > rightTree.precedence
////           && op.precedence > leftTree.precedence then
////            { left = Branch leftTree
////              op = firstOp
////              highestPrecedence = op.precedence
////              right = Branch rightTree }

////        else if op.precedence < subTree.highestPrecedence then








///// Creates a binary tree of operations, correctly constructed according to associativity and precedence
////let createOpBinaryTree (firstExpr : S.CstNode<Q.Expression >) (opExprSeq : (S.CstNode<Q.Operator > * S.CstNode<Q.Expression> ) nel ) : OpBinaryTree =
//// associativity: right is like the (::) operator. I.e. we consider everything to the right to be a single expression before appending the left things to it. Otherwise `a :: b :: []` would be parsed as `(a :: b) :: []`, which is wrong.
//// associativity: left is the opposite. i.e. `a (op) b (op) c` is equivalent to `(a (op) b) (op) c`

















let rec convertAssignmentPattern (pattern : Cst.AssignmentPattern) : AssignmentPattern =
    match pattern with
    | S.Named name -> Named (unqualValToLowerIdent name)
    | S.Ignored -> Ignored
    | S.Unit -> Unit
    | S.DestructuredPattern p ->
        convertDestructuredPattern p
        |> DestructuredPattern
    | S.Aliased (p, alias) -> Aliased (convertAssignmentPattern p.node, unqualValToLowerIdent alias.node)

and convertDestructuredPattern (pattern : Cst.DestructuredPattern) : DestructuredPattern =
    match pattern with
    | S.DestructuredRecord fields ->
        NEL.map (S.getNode >> unqualValToRecField) fields
        |> DestructuredRecord
    | S.DestructuredTuple items ->
        TOM.map (S.getNode >> convertAssignmentPattern) items
        |> DestructuredTuple
    | S.DestructuredCons items ->
        TOM.map (S.getNode >> convertAssignmentPattern) items
        |> DestructuredCons
    | S.DestructuredTypeVariant (ctor, params_) ->
        DestructuredTypeVariant (
            typeOrModuleIdentToUpperNameVal ctor.node,
            List.map (S.getNode >> convertAssignmentPattern) params_
        )




let rec gatherParams (pattern : AssignmentPattern) : FunctionOrCaseMatchParam =
    match pattern with
    | Named ident ->
        let param_ : Param = { destructurePath = SimpleName }

        { paramPattern = pattern
          namesMap = Map.add ident (SOD.new_ param_) Map.empty }

    | Ignored ->
        { paramPattern = pattern
          namesMap = Map.empty }

    | Unit ->
        { paramPattern = pattern
          namesMap = Map.empty }

    | DestructuredPattern destructured ->
        { paramPattern = pattern
          namesMap = gatherDestructuredPattern destructured }

    | Aliased (aliased, alias) ->

        let param_ : Param = { destructurePath = SimpleName }

        let gatheredFromAlias = gatherParams aliased

        { paramPattern = pattern
          namesMap =
            gatheredFromAlias.namesMap
            |> NameResolution.addNewReference alias param_ }




and gatherDestructuredPattern (pattern : DestructuredPattern) : Map<LowerIdent, SOD<Param>> =
    /// Adjusts the destructure path of a param to account for the fact that it is contained inside a nested destructuring
    let adjustDestructurePath (newPath : PathToDestructuredName) (param_ : Param) : Param =
        { param_ with destructurePath = newPath }


    match pattern with
    | DestructuredRecord fields ->
        fields
        |> NEL.map (fun recField ->
            let ident = recFieldToLowerIdent recField

            ident, { Param.destructurePath = InverseRecord })
        |> NEL.toList
        |> SOD.makeMapFromList

    | DestructuredTuple patterns ->
        TOM.map gatherParams patterns
        |> TOM.mapi (fun index tupleItem ->
            tupleItem.namesMap
            |> Map.map (fun _ paramsEntries ->
                paramsEntries
                |> SOD.map (fun param -> adjustDestructurePath (InverseTuple (uint index, param.destructurePath)) param)))
        |> TOM.fold NameResolution.combineTwoReferenceMaps Map.empty


    | DestructuredCons patterns ->
        patterns
        |> TOM.map gatherParams
        |> TOM.mapi (fun index params_ ->
            params_.namesMap
            |> Map.map (fun _ paramEntries ->
                paramEntries
                |> SOD.map (fun param_ ->
                    adjustDestructurePath (InverseCons (uint index, param_.destructurePath)) param_)))
        |> TOM.fold Map.merge Map.empty

    | DestructuredTypeVariant (ctor, params_) ->
        params_
        |> List.map gatherParams
        |> List.mapi (fun index params__ ->
            params__.namesMap
            |> Map.map (fun _ paramEntries ->
                paramEntries
                |> SOD.map (fun param_ ->
                    adjustDestructurePath (InverseTypeVariant (ctor, uint index, param_.destructurePath)) param_)))
        |> List.fold Map.merge Map.empty




let typeFuncOrCaseMatchParam : Cst.AssignmentPattern -> FunctionOrCaseMatchParam =
    convertAssignmentPattern >> gatherParams




let typeOfPrimitiveLiteralValue (primitive : S.PrimitiveLiteralValue) : DefinitiveType =
    match primitive with
    | S.NumberPrimitive num ->
        match num with
        | S.FloatLiteral _ -> DtPrimitiveType Float
        | S.IntLiteral _ -> DtPrimitiveType Int
    | S.CharPrimitive _ -> DtPrimitiveType Char
    | S.StringPrimitive _ -> DtPrimitiveType String
    | S.UnitPrimitive _ -> DtUnitType
    | S.BoolPrimitive _ -> DtPrimitiveType Bool



///// The purpose of this function is to rerun the type inference for a (potentially modified) expression
//let rec typeCheckExpression (expr : SingleOrCompoundExpr) : TypedExpr =

//    match expr with
//    | T.SingleValueExpression singleVal ->
//        match singleVal with
//        | T.ExplicitValue explicit ->
//            match explicit with
//            | T.Primitive primitive ->
//                let type_ =
//                    typeOfPrimitiveLiteralValue primitive
//                    |> TypeConstraints.fromDefinitive
//                    |> Ok

//                { inferredType = type_
//                  expr =
//                    Primitive primitive
//                    |> ExplicitValue
//                    |> SingleValueExpression }


//            | T.DotGetter dotGetter ->
//                let type_ =
//                    Map.empty
//                    |> Map.add dotGetter TypeConstraints.empty
//                    |> DtRecordWith
//                    |> TypeConstraints.fromDefinitive
//                    |> Ok

//                { inferredType = type_
//                  expr =
//                    DotGetter dotGetter
//                    |> ExplicitValue
//                    |> SingleValueExpression }

//            | T.Compound compound ->
//                match compound with
//                | T.List list ->
//                    let typedList = List.map (S.getNode >> typeCheckExpression) list

//                    let combinedType =
//                        typedList
//                        |> List.fold
//                            (fun state expr ->
//                                (state, expr.inferredType)
//                                ||> Result.bind2 unifyTypeConstraints unifyTypeErrors)
//                            (Ok TypeConstraints.empty)
//                        |> Result.map (DtList >> TypeConstraints.fromDefinitive)

//                    { inferredType = combinedType
//                      expr =
//                        typedList
//                        |> T.List
//                        |> Compound
//                        |> ExplicitValue
//                        |> SingleValueExpression }

//                | T.CompoundValues.Tuple tuple ->
//                    let typedList =
//                        TOM.map
//                            (S.getNode
//                             >> typeCheckCstExpression resolutionChain)
//                            tuple

//                    let combinedType =
//                        typedList
//                        |> TOM.map (fun expr -> expr.inferredType)
//                        |> TOM.sequenceResult
//                        |> concatResultErrListNel
//                        |> Result.map (DtTuple >> TypeConstraints.fromDefinitive)

//                    { inferredType = combinedType
//                      expr =
//                        typedList
//                        |> CompoundValues.Tuple
//                        |> Compound
//                        |> ExplicitValue
//                        |> SingleValueExpression }

//                | T.CompoundValues.Record record ->
//                    let typedList =
//                        record
//                        |> List.map (fun (key, value) ->
//                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

//                    let combinedType =
//                        typedList
//                        |> List.map (fun (key, expr) ->
//                            expr.inferredType
//                            |> Result.map (fun inferred -> key, inferred))
//                        |> Result.sequenceList
//                        |> Result.map Map.ofList
//                        |> concatResultErrListNel
//                        |> Result.map (DtRecordExact >> TypeConstraints.fromDefinitive)

//                    { inferredType = combinedType
//                      expr =
//                        typedList
//                        |> CompoundValues.Record
//                        |> Compound
//                        |> ExplicitValue
//                        |> SingleValueExpression }

//                | S.CompoundValues.RecordExtension (extended, additions) ->

//                    let typedList =
//                        additions
//                        |> NEL.map (fun (key, value) ->
//                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

//                    let typeOfEditedRecord =
//                        unqualValToLowerName extended.node
//                        |> ByValue
//                        |> TypeConstraints.fromConstraint

//                    let derivedFromFieldsType : TypeJudgment =
//                        typedList
//                        |> NEL.map (fun (key, expr) ->
//                            expr.inferredType
//                            |> Result.map (fun inferred -> key, inferred))
//                        |> NEL.sequenceResult
//                        |> Result.map (NEL.toList >> Map.ofList)
//                        |> concatResultErrListNel
//                        |> Result.map (DtRecordWith >> TypeConstraints.fromDefinitive)

//                    let combinedType : TypeJudgment =
//                        Result.bind (unifyTypeConstraints typeOfEditedRecord) derivedFromFieldsType

//                    { inferredType = combinedType
//                      expr =
//                        CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
//                        |> Compound
//                        |> ExplicitValue
//                        |> SingleValueExpression }

//            | T.Function funcVal ->
//                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
//                let typeOfBody = typeCheckCstExpression resolutionChain funcVal.body.node

//                let funcParams : FunctionOrCaseMatchParam nel =
//                    funcVal.params_
//                    |> NEL.map (S.getNode >> typeFuncOrCaseMatchParam)

//                let funcParamTypes =
//                    funcParams
//                    |> NEL.traverseResult (fun param_ -> param_.inferredType)
//                    |> concatResultErrListNel

//                let arrowType : TypeJudgment =
//                    (typeOfBody.inferredType, funcParamTypes)
//                    ||> Result.map2
//                            (fun typeOfBody_ (NEL (firstParamType, restParamTypes)) ->
//                                let toTypes =
//                                    NEL.new_ typeOfBody_ (List.rev restParamTypes)
//                                    |> NEL.reverse

//                                DtArrow (firstParamType, makeDestType toTypes)
//                                |> TypeConstraints.fromDefinitive)
//                            unifyTypeErrors


//                let funcVal : FunctionValue =
//                    { params_ = funcParams
//                      body = typeOfBody }

//                { expr =
//                    Function funcVal
//                    |> ExplicitValue
//                    |> SingleValueExpression
//                  inferredType = arrowType }


//        | T.UpperIdentifier name ->
//            let ctorName = typeOrModuleIdentToUpperNameVal name
//            let defType = ByConstructorType ctorName

//            { expr = UpperIdentifier ctorName |> SingleValueExpression
//              inferredType = TypeConstraints.fromConstraint defType |> Ok }

//        | T.LowerIdentifier name ->
//            let lowerNameVal = convertValueIdentifierToLowerName name

//            let inferredType =
//                match lowerNameVal with
//                | FullyQualifiedLower _ ->
//                    ByValue lowerNameVal
//                    |> TypeConstraints.fromConstraint
//                    |> Ok

//                | LocalLower local ->
//                    if List.contains local resolutionChain then
//                        Ok Recursive
//                    else
//                        ByValue lowerNameVal
//                        |> TypeConstraints.fromConstraint
//                        |> Ok

//            { expr =
//                LowerIdentifier lowerNameVal
//                |> SingleValueExpression
//              inferredType = inferredType }

//        | T.LetExpression (declarations, expr) ->

//            let bodyExpr = typeCheckExpression resolutionChain expr.node


//            let typedDeclarations : LetBindings =
//                declarations
//                |> NEL.map (fun binding -> binding.node.bindPattern.node, binding.node.value.node)
//                |> NEL.map (fun (bindPattern, bindValue) ->
//                    let param = typeFuncOrCaseMatchParam bindPattern
//                    let boundNames = param.namesMap |> Map.keys |> Seq.toList
//                    let assignedExpr = typeCheckExpression (boundNames @ resolutionChain) bindValue

//                    { paramPattern = param.paramPattern
//                      namesMap = param.namesMap
//                      bindingPatternInferredType = param.inferredType
//                      assignedExpression = assignedExpr
//                      combinedInferredType = unifyJudgments assignedExpr.inferredType param.inferredType })

//            let combinedNamesMap =
//                typedDeclarations
//                |> NEL.toList
//                |> List.map (fun decl -> decl.namesMap)
//                |> SOD.combineReferenceMaps

//            { inferredType = bodyExpr.inferredType
//              expr =
//                LetExpression (typedDeclarations, bodyExpr)
//                |> SingleValueExpression }


//        | T.ControlFlowExpression controlFlow ->
//            match controlFlow with
//            | T.IfExpression (cond, ifTrue, ifFalse) ->
//                let conditionalWithBoolConstraint =
//                    typeCheckCstExpression resolutionChain cond.node
//                    |> addDefinitiveConstraint (DtPrimitiveType Bool) // because conditions need to be booleans

//                // This is aiming to express the type constraint that both branches of the if expression should have the same type

//                let typedIfTrueBranch = typeCheckCstExpression resolutionChain ifTrue.node
//                let typedIfFalseBranch = typeCheckCstExpression resolutionChain ifFalse.node

//                let expressionType : TypeJudgment =
//                    match typedIfTrueBranch.inferredType with
//                    | Ok typedIfTrue -> Ok typedIfTrue
//                    | Error _ -> typedIfFalseBranch.inferredType

//                // This should leave whichever one had the original definitive type unchanged, and only add a definitive constraint to the other one
//                let unifiedTrue = addTypeJudgment expressionType typedIfTrueBranch
//                let unifiedFalse = addTypeJudgment expressionType typedIfFalseBranch


//                { inferredType = expressionType
//                  expr =
//                    IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
//                    |> ControlFlowExpression
//                    |> SingleValueExpression }


//            | T.CaseMatch (exprToMatch, branches) ->
//                let typedExprToMatch = typeCheckCstExpression resolutionChain exprToMatch.node

//                let typedBranches =
//                    branches
//                    |> NEL.map (fun (pattern, branchExpr) ->
//                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
//                          body = typeCheckCstExpression resolutionChain branchExpr.node })


//                let (matchExprType, branchReturnTypeConstraints) =
//                    typedBranches
//                    |> NEL.fold
//                        (fun (patternConstraints, branchConstraints) branch ->
//                            unifyJudgments patternConstraints branch.matchPattern.inferredType,
//                            unifyJudgments branchConstraints branch.body.inferredType)
//                        (typedExprToMatch.inferredType, Ok TypeConstraints.empty)

//                { inferredType = branchReturnTypeConstraints
//                  expr =
//                    CaseMatch (addTypeJudgment matchExprType typedExprToMatch, typedBranches)
//                    |> ControlFlowExpression
//                    |> SingleValueExpression }

//    | T.CompoundExpression compExpr ->
//        match compExpr with
//        | T.FunctionApplication (funcExpr, params_) ->
//            let typedFunc = typeCheckCstExpression resolutionChain funcExpr.node

//            let typedParams =
//                params_
//                |> NEL.map (
//                    S.getNode
//                    >> typeCheckCstExpression resolutionChain
//                )

//            /// @TODO: I _think_ this might be wrong, because this means letting type inference flow upstream, thus resulting in destroying let polymorphism
//            let paramRequirementsFromDeFactoParams =
//                typedParams
//                |> NEL.map (fun e -> e.inferredType)
//                |> NEL.sequenceResult
//                |> concatResultErrListNel

//            let unified =
//                paramRequirementsFromDeFactoParams
//                |> Result.bind (fun paramRequirements ->
//                    let (NEL (firstParam, restParams)) = paramRequirements

//                    let restParamsAndReturnType =
//                        NEL.fromListAndLast restParams TypeConstraints.unspecific

//                    let funcTypeRequirement = DtArrow (firstParam, makeDestType restParamsAndReturnType)

//                    unifyJudgments
//                        typedFunc.inferredType
//                        (TypeConstraints.fromDefinitive funcTypeRequirement
//                         |> Ok))

//            { inferredType = unified
//              expr =
//                FunctionApplication (typedFunc, typedParams)
//                |> CompoundExpression }

//        | T.DotAccess (dottedExpr, dotSequence) ->
//            let rec makeNestedMap (fieldSeq : RecordFieldName list) =
//                match fieldSeq with
//                | [] -> TypeConstraints.empty
//                | head :: rest ->
//                    Map.empty
//                    |> Map.add head (makeNestedMap rest)
//                    |> DtRecordWith
//                    |> TypeConstraints.fromDefinitive

//            let typedExpr = typeCheckCstExpression resolutionChain dottedExpr.node

//            let exprTypeConstraint =
//                dotSequence.node
//                |> NEL.map unqualValToRecField
//                |> NEL.toList
//                |> makeNestedMap

//            let fullyTypedExpr = addTypeConstraints exprTypeConstraint typedExpr

//            { inferredType = fullyTypedExpr.inferredType
//              expr =
//                DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
//                |> CompoundExpression }

//        | T.Operator (left, opSequence) ->
//            failwith
//                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"




















let rec typeCheckCstExpression (resolutionChain : LowerIdent list) (expr : Cst.Expression) : TypedExpr =

    match expr with
    | S.SingleValueExpression singleVal ->
        match singleVal with
        | S.ExplicitValue explicit ->
            match explicit with
            | S.Primitive primitive ->

                { expr =
                    Primitive primitive
                    |> ExplicitValue
                    |> SingleValueExpression }


            | S.DotGetter dotGetter ->
                let recFieldName = unqualValToRecField dotGetter


                { expr =
                    DotGetter recFieldName
                    |> ExplicitValue
                    |> SingleValueExpression }

            | S.Compound compound ->
                match compound with
                | S.List list ->
                    let typedList =
                        List.map
                            (S.getNode
                             >> typeCheckCstExpression resolutionChain)
                            list

                    { expr =
                        typedList
                        |> T.List
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.Tuple tuple ->
                    let typedList =
                        TOM.map
                            (S.getNode
                             >> typeCheckCstExpression resolutionChain)
                            tuple


                    { expr =
                        typedList
                        |> CompoundValues.Tuple
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) ->
                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

                    { expr =
                        typedList
                        |> CompoundValues.Record
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

                | S.CompoundValues.RecordExtension (extended, additions) ->

                    let typedList =
                        additions
                        |> NEL.map (fun (key, value) ->
                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

                    { expr =
                        CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
                        |> Compound
                        |> ExplicitValue
                        |> SingleValueExpression }

            | S.Function funcVal ->
                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
                let typeOfBody = typeCheckCstExpression resolutionChain funcVal.body.node

                let funcParams : FunctionOrCaseMatchParam nel =
                    funcVal.params_
                    |> NEL.map (S.getNode >> typeFuncOrCaseMatchParam)


                let funcVal : FunctionValue =
                    { params_ = funcParams
                      body = typeOfBody }

                { expr =
                    Function funcVal
                    |> ExplicitValue
                    |> SingleValueExpression }


        | S.UpperIdentifier name ->
            let ctorName = typeOrModuleIdentToUpperNameVal name

            { expr = UpperIdentifier ctorName |> SingleValueExpression }

        | S.LowerIdentifier name ->
            let lowerNameVal = convertValueIdentifierToLowerName name

            { expr =
                LowerIdentifier lowerNameVal
                |> SingleValueExpression }

        | S.LetExpression (declarations, expr) ->

            let bodyExpr = typeCheckCstExpression resolutionChain expr.node


            let typedDeclarations : LetBindings =
                declarations
                |> NEL.map (fun binding -> binding.node.bindPattern.node, binding.node.value.node)
                |> NEL.map (fun (bindPattern, bindValue) ->
                    let param = typeFuncOrCaseMatchParam bindPattern
                    let boundNames = param.namesMap |> Map.keys |> Seq.toList
                    let assignedExpr = typeCheckCstExpression (boundNames @ resolutionChain) bindValue

                    { paramPattern = param.paramPattern
                      namesMap = param.namesMap
                      assignedExpression = assignedExpr })


            { expr =
                LetExpression (typedDeclarations, bodyExpr)
                |> SingleValueExpression }


        | S.ControlFlowExpression controlFlow ->
            match controlFlow with
            | S.IfExpression (cond, ifTrue, ifFalse) ->
                let conditionalWithBoolConstraint = typeCheckCstExpression resolutionChain cond.node

                // This is aiming to express the type constraint that both branches of the if expression should have the same type

                let typedIfTrueBranch = typeCheckCstExpression resolutionChain ifTrue.node
                let typedIfFalseBranch = typeCheckCstExpression resolutionChain ifFalse.node

                // This should leave whichever one had the original definitive type unchanged, and only add a definitive constraint to the other one
                let unifiedTrue = typedIfTrueBranch
                let unifiedFalse = typedIfFalseBranch


                { expr =
                    IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
                    |> ControlFlowExpression
                    |> SingleValueExpression }


            | S.CaseMatch (exprToMatch, branches) ->
                let typedExprToMatch = typeCheckCstExpression resolutionChain exprToMatch.node

                let typedBranches =
                    branches
                    |> NEL.map (fun (pattern, branchExpr) ->
                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
                          body = typeCheckCstExpression resolutionChain branchExpr.node })


                { expr =
                    CaseMatch (typedExprToMatch, typedBranches)
                    |> ControlFlowExpression
                    |> SingleValueExpression }

    | S.CompoundExpression compExpr ->
        match compExpr with
        | S.FunctionApplication (funcExpr, params_) ->
            let typedFunc = typeCheckCstExpression resolutionChain funcExpr.node

            let typedParams =
                params_
                |> NEL.map (
                    S.getNode
                    >> typeCheckCstExpression resolutionChain
                )

            { expr =
                FunctionApplication (typedFunc, typedParams)
                |> CompoundExpression }

        | S.DotAccess (dottedExpr, dotSequence) ->
            let rec makeNestedMap (fieldSeq : RecordFieldName list) =
                match fieldSeq with
                | [] -> TypeConstraints.empty
                | head :: rest ->
                    Map.empty
                    |> Map.add head (makeNestedMap rest)
                    |> DtRecordWith
                    |> TypeConstraints.fromDefinitive

            let typedExpr = typeCheckCstExpression resolutionChain dottedExpr.node

            { expr =
                DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
                |> CompoundExpression }

        | S.Operator (left, opSequence) ->
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"

    | S.ParensedExpression expr -> typeCheckCstExpression resolutionChain expr




///// This looks into a typed expression and resolves any named values at this level with the provided dictionary, and propagates any changed type signatures accordingly
//and resolveValues
//    //(resolutionChain : LowerNameValue list)
//    (constraintAccumulator : Accumulator)
//    (typedExpr : TypedExpr)
//    : TypedExpr =
//    //let resolveRecursive (name : LowerNameValue) =
//    //    resolveValues (name :: resolutionChain) namesMaps

//    match typedExpr.expr with
//    | T.SingleValueExpression singleVal ->
//        match singleVal with
//        | T.ExplicitValue explicit ->
//            match explicit with
//            | T.Primitive prim ->
//                makeTypedExpr
//                    typedExpr.inferredType
//                    (T.Primitive prim
//                     |> T.ExplicitValue
//                     |> T.SingleValueExpression)

//        | T.UpperIdentifier upperIdent ->
//            match NameRes.findTypeConstructor upperIdent namesMaps with
//            | Some sod ->
//                let ctor = SOD.getFirst sod

//                makeTypedExpr
//                    ((LocalUpper ctor.typeName,
//                      List.map (Tuple.makePairWithSnd TypeConstraints.unspecific) ctor.typeParamsList)
//                     |> DtNewType
//                     |> TypeConstraints.fromDefinitive
//                     |> Ok)
//                    (T.UpperIdentifier upperIdent
//                     |> T.SingleValueExpression)

//            | None -> typedExpr

//        | T.LowerIdentifier lowerIdent ->
//            let value = NameRes.findValue lowerIdent namesMaps
//            let valType = NameRes.findValueType lowerIdent namesMaps

//            let inferredOrDeclaredType =
//                match value, valType with
//                | _, Some t ->
//                    let valueType = SOD.getFirst t
//                    Some (Ok valueType)

//                | Some v, None ->
//                    let value : T.LowerCaseName = SOD.getFirst v

//                    NameRes.getInferredTypeOfLowercaseName value
//                    |> Some

//                | None, None -> None

//            match inferredOrDeclaredType with
//            | Some type_ ->
//                makeTypedExpr
//                    type_
//                    (T.LowerIdentifier lowerIdent
//                     |> T.SingleValueExpression)


//            | None -> typedExpr

///// This looks into a typed expression and resolves any named values at this level with the provided dictionary, and propagates any changed type signatures accordingly
//and resolveValues
//    //(resolutionChain : LowerNameValue list)
//    (namesMaps : NameRes.NamesMaps)
//    (typedExpr : TypedExpr)
//    : TypedExpr =
//    //let resolveRecursive (name : LowerNameValue) =
//    //    resolveValues (name :: resolutionChain) namesMaps

//    match typedExpr.expr with
//    | T.SingleValueExpression singleVal ->
//        match singleVal with
//        | T.ExplicitValue explicit ->
//            match explicit with
//            | T.Primitive prim ->
//                makeTypedExpr
//                    typedExpr.inferredType
//                    (T.Primitive prim
//                     |> T.ExplicitValue
//                     |> T.SingleValueExpression)

//        | T.UpperIdentifier upperIdent ->
//            match NameRes.findTypeConstructor upperIdent namesMaps with
//            | Some sod ->
//                let ctor = SOD.getFirst sod

//                makeTypedExpr
//                    ((LocalUpper ctor.typeName, List.map (Tuple.makePairWithSnd TypeConstraints.empty) ctor.typeParamsList)
//                     |> DtNewType
//                     |> TypeConstraints.fromDefinitive
//                     |> Ok)
//                    (T.UpperIdentifier upperIdent
//                     |> T.SingleValueExpression)

//            | None -> typedExpr

//        | T.LowerIdentifier lowerIdent ->
//            let value = NameRes.findValue lowerIdent namesMaps
//            let valType = NameRes.findValueType lowerIdent namesMaps

//            let inferredOrDeclaredType =
//                match value, valType with
//                | _, Some t ->
//                    let valueType = SOD.getFirst t
//                    Some (Ok valueType)

//                | Some v, None ->
//                    let value : T.LowerCaseName = SOD.getFirst v

//                    NameRes.getInferredTypeOfLowercaseName value
//                    |> Some

//                | None, None -> None

//            match inferredOrDeclaredType with
//            | Some type_ ->
//                makeTypedExpr
//                    type_
//                    (T.LowerIdentifier lowerIdent
//                     |> T.SingleValueExpression)


//            | None -> typedExpr
//| T.LetExpression (bindings,body)->







module Accumulator =


    (*
    This should:
    - based on the intersections of which referenced values are colocated with which other referenced values and definitive types, build up a set of groups of all the inferred types for the referenced values
    - unify the definitive types in each group
    - from each group, construct a map for all the referenced value names as keys, the values of which is the same combined type for each of them
    - we can do this for a list of values and keep accumulating the same referenced value names with their usages in the other type constraints; that will allow us to construct a map where for each referenced value name we have a much specified TypeConstraints – which is effectively equal to having an inferred type for the value by that name!

    And it's only after doing all of that that it maybe makes sense to go back in and resolve all the referenced value types in an expression? Although tbh maybe even then not. Maybe internally where those values are referenced we just keep them as is, and it's only from the outside that we glean which types those things _must_ be, which we can then view from the outside

    So then there's the separate question of how we can then use that to figure out if there is some recursion anywhere? Because we need to know whether a value references itself inside its own definition so that we know not to try to resolve the type of that thing completely... but then tbh are we even attempting to do that anymore with this new approach?

    *)


    (*
        Create and add/combine
    *)

    let empty = Map.empty


    /// This contains the core logic for adding a new constraint to the Acc
    let rec addSingleConstrainedValueResult
        (defTypeOptResult : Result<DefinitiveType option, TypeError>)
        (namesSet : RefConstr set)
        (acc : Accumulator)
        : Accumulator =
        let predicate = Set.intersect namesSet >> Set.isNotEmpty

        let combiner
            (keyvalList : (RefConstr set * Result<DefinitiveType option, TypeError>) list)
            : RefConstr set * Result<DefinitiveType option, TypeError> =

            let combineTwoDefOptResults
                (a : Result<DefinitiveType option, TypeError>)
                (b : Result<DefinitiveType option, TypeError>)
                : Result<DefinitiveType option, TypeError> =
                match a, b with
                | Ok (Some a_), Ok (Some b_) -> unifyDefinitiveTypes a_ b_ |> Result.map Some

                | Ok (Some def), Ok None
                | Ok None, Ok (Some def) -> Ok (Some def)

                | Ok None, Ok None -> Ok None

                | Error err1, Error err2 -> unifyTypeErrors err1 err2 |> Error

                | Ok None, Error e
                | Error e, Ok None -> Error e

                | Ok (Some def), Error e
                | Error e, Ok (Some def) -> addDefToTypeError def e |> Error

            let keySets, defTypes = List.unzip keyvalList

            let newKey = Set.unionMany keySets

            let newVal =
                defTypes
                |> List.fold combineTwoDefOptResults defTypeOptResult

            newKey, newVal

        Map.combineManyKeys predicate combiner acc




    /// Adds a single new (non-error) constrained value to an Accumulator
    let private addSingleConstrainedValue
        (defTypeOpt : DefinitiveType option)
        (namesSet : RefConstr set)
        (acc : Accumulator)
        =
        addSingleConstrainedValueResult (Ok defTypeOpt) namesSet acc


    let addSingleTypeConstraint (constr : TypeConstraints) (acc : Accumulator) : Accumulator =
        let (Constrained (defOpt, others)) = constr

        addSingleConstrainedValue defOpt others acc


    let addSingleTypeJudgment (judgment : TypeJudgment) (acc : Accumulator) : Accumulator =
        match judgment with
        | Ok tc -> addSingleTypeConstraint tc acc
        | Error _ -> acc


    let private makeAccumFromConstraints (constraintsList : TypeConstraints list) : Accumulator =
        constraintsList
        |> List.fold (fun state cnstrnt -> addSingleTypeConstraint cnstrnt state) Map.empty






    let addJudgmentToAccum (ident : LowerIdent) (judgment : TypeJudgment) (acc : Accumulator) : Accumulator =
        let (defOptResult, refConstraints) =
            match judgment with
            | Ok (Constrained (defOpt, others)) -> Ok defOpt, others
            | Error e -> Error e, Set.empty

        let namesToAdd = Set.add (ByValue (LocalLower ident)) refConstraints

        addSingleConstrainedValueResult defOptResult namesToAdd acc


    let makeAccFromTypeConstraints (tc : TypeConstraints) : Accumulator = addSingleTypeConstraint tc Map.empty





    /// Add information about a named TypeConstraints into the Acc
    let makeAccFromNamedTypeConstraints (ident : LowerNameValue) (tc : TypeConstraints) : Accumulator =
        TypeConstraints.addConstraint (ByValue ident) tc
        |> makeAccFromTypeConstraints


    /// Add information about a named TypeConstraints for a value into the Acc
    let makeAccFromLocalIdentAndTypeConstraints (ident : LowerIdent) (tc : TypeConstraints) : Accumulator =
        makeAccFromNamedTypeConstraints (LocalLower ident) tc





    (*
        Combine Accs together
    *)

    /// In other words allow for merging constrained value constraints from two different maps
    let combineAccumulators (acc1 : Accumulator) (acc2 : Accumulator) : Accumulator =
        acc1
        |> Map.fold (fun acc key value -> addSingleConstrainedValueResult value key acc) acc2

    let addManyAccs (newAccs : Accumulator seq) (acc : Accumulator) : Accumulator =
        Seq.fold combineAccumulators acc newAccs

    let combineManyAccs (accs : Accumulator seq) : Accumulator = addManyAccs accs Map.empty






    (*
        Get information out of the Acc
    *)


    let private makeMapFromAccum (accum : Accumulator) : Map<RefConstr, TypeJudgment> =
        let convertSingleAccEntryBack (nameSet : RefConstr set) (defOpt : DefinitiveType option) : TypeConstraints =
            Constrained (defOpt, nameSet)

        accum
        // Convert it back to a map of names with their inferred types
        |> Map.toList
        |> List.collect (fun (nameSet, defOptResult) ->
            let constraintsForNameGroup =
                Result.map (convertSingleAccEntryBack nameSet) defOptResult

            Set.toList nameSet
            |> List.map (Tuple.makePairWithSnd constraintsForNameGroup))
        |> Map.ofList


    /// This is the function that infers all the types for all referenced values based on a list of TypeConstraints!
    let getConstrainedRefs (constraintsList : TypeConstraints list) : Map<RefConstr, TypeJudgment> =
        makeAccumFromConstraints constraintsList
        |> makeMapFromAccum


    let getConstrainedValues =
        getConstrainedRefs
        >> Map.chooseKeyVals (fun constr judgment ->
            match constr with
            | ByValue name -> Some (name, judgment)
            | _ -> None)



    let getConstrainedLocalValues =
        getConstrainedRefs
        >> Map.chooseKeyVals (fun constr judgment ->
            match constr with
            | ByValue (LocalLower name) -> Some (name, judgment)
            | _ -> None)







module Acc = Accumulator





type AccumulatorAndOwnType =
    { acc : Accumulator
      ownType : TypeJudgment }




module AccumulatorAndOwnType =

    /// This processes the type judgment with the information available in the accumulator at every opportune point, the idea being that in any AccumulatorAndOwnType, whenever we look at the Acc or its ownType, all the available information has been properly propagated through the type judgment and doesn't need to be done by the external code
    /// @TODO: check if I haven't already basically implemented this code somewhere in the Acc module!
    let private processAccAndOwnType acc typeJudgment = typeJudgment


    /// Makes an AccumulatorAndOwnType from a type judgment and an Accumulator
    let make (ownType : TypeJudgment) (acc : Accumulator) : AccumulatorAndOwnType = { acc = acc; ownType = ownType }

    let getAcc { acc = acc } : Accumulator = acc
    let getSelf { ownType = ownType } : TypeJudgment = ownType

    /// Combine two `AccumulatorAndSelfValue`s into a single accumulator and unified type judgment
    let combine (aas1 : AccumulatorAndOwnType) (aas2 : AccumulatorAndOwnType) : AccumulatorAndOwnType =
        { acc = Acc.combineAccumulators aas1.acc aas2.acc
          ownType = unifyJudgments aas1.ownType aas2.ownType }


    /// Combine multiple `AccumulatorAndSelfValue`s into a single accumulator and unified type judgment
    let combineMany (list : AccumulatorAndOwnType seq) : AccumulatorAndOwnType =
        Seq.fold
            combine
            { acc = Map.empty
              ownType = Ok TypeConstraints.empty }
            list





module Aaot = AccumulatorAndOwnType


let rec getAccumulatorFromSingleOrCompExpr (expr : SingleOrCompoundExpr) : AccumulatorAndOwnType =
    match expr with
    | T.SingleValueExpression singleVal ->
        match singleVal with
        | T.ExplicitValue explicit ->
            match explicit with
            | T.Primitive primitive ->
                Aaot.make
                    (typeOfPrimitiveLiteralValue primitive
                     |> TypeConstraints.fromDefinitive
                     |> Ok)
                    Map.empty

            | T.DotGetter dotGetter ->
                Aaot.make
                    (Map.empty
                     |> Map.add dotGetter TypeConstraints.empty
                     |> DtRecordWith
                     |> TypeConstraints.fromDefinitive
                     |> Ok)
                    Map.empty

            | T.Compound compound ->
                match compound with
                | T.List list ->
                    let typedList = List.map getAccumulatorFromExpr list

                    let combinedAcc =
                        typedList
                        |> List.map Aaot.getAcc
                        |> Acc.combineManyAccs

                    let combinedSelf =
                        (typedList
                         |> List.fold
                             (fun state expr ->
                                 (state, Aaot.getSelf expr)
                                 ||> Result.bind2 unifyTypeConstraints unifyTypeErrors)
                             (Ok TypeConstraints.empty)
                         |> Result.map (DtList >> TypeConstraints.fromDefinitive))


                    Aaot.make combinedSelf combinedAcc


                | T.CompoundValues.Tuple tuple ->
                    let typedList = TOM.map getAccumulatorFromExpr tuple

                    let combinedAcc =
                        typedList
                        |> TOM.map Aaot.getAcc
                        |> TOM.toList
                        |> Acc.combineManyAccs

                    let combinedSelf =
                        typedList
                        |> TOM.map Aaot.getSelf
                        |> TOM.sequenceResult
                        |> concatResultErrListNel
                        |> Result.map (DtTuple >> TypeConstraints.fromDefinitive)

                    Aaot.make combinedSelf combinedAcc



                | T.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) -> key, getAccumulatorFromExpr value)

                    let combinedAcc =
                        typedList
                        |> List.map (snd >> Aaot.getAcc)
                        |> Acc.combineManyAccs

                    let combinedType =
                        typedList
                        |> List.map (fun (key, expr) ->
                            Aaot.getSelf expr
                            |> Result.map (fun inferred -> key, inferred))
                        |> Result.sequenceList
                        |> Result.map Map.ofList
                        |> concatResultErrListNel
                        |> Result.map (DtRecordExact >> TypeConstraints.fromDefinitive)

                    Aaot.make combinedType combinedAcc


                | T.CompoundValues.RecordExtension (extended, additions) ->

                    let typedList =
                        additions
                        |> NEL.map (fun (key, value) -> key, getAccumulatorFromExpr value)

                    let combinedAcc =
                        typedList
                        |> NEL.map (snd >> Aaot.getAcc)
                        |> NEL.toList
                        |> Acc.combineManyAccs

                    let typeOfEditedRecord =
                        LocalLower extended
                        |> ByValue
                        |> TypeConstraints.fromConstraint

                    let derivedFromFieldsType : TypeJudgment =
                        typedList
                        |> NEL.map (fun (key, expr) ->
                            Aaot.getSelf expr
                            |> Result.map (fun inferred -> key, inferred))
                        |> NEL.sequenceResult
                        |> Result.map (NEL.toList >> Map.ofList)
                        |> concatResultErrListNel
                        |> Result.map (DtRecordWith >> TypeConstraints.fromDefinitive)

                    let combinedType : TypeJudgment =
                        Result.bind (unifyTypeConstraints typeOfEditedRecord) derivedFromFieldsType

                    Aaot.make combinedType combinedAcc

            | T.Function funcVal ->
                let typeOfBody = getAccumulatorFromExpr funcVal.body

                let funcParamsAccumulatorsAndSelfTypes =
                    NEL.map (getParamFromPattern >> getAccumulatorFromParam) funcVal.params_

                let funcParamsAccumulators =
                    funcParamsAccumulatorsAndSelfTypes
                    |> NEL.map Aaot.getAcc


                let funcParamTypes =
                    funcParamsAccumulatorsAndSelfTypes
                    |> NEL.map Aaot.getSelf
                    |> NEL.sequenceResult
                    |> concatResultErrListNel


                let arrowType : TypeJudgment =
                    (funcParamTypes, typeOfBody.ownType)
                    ||> Result.map2
                            (fun (NEL (firstParamType, restParamTypes)) typeOfBody_ ->
                                let toTypes =
                                    NEL.new_ typeOfBody_ (List.rev restParamTypes)
                                    |> NEL.reverse

                                DtArrow (firstParamType, makeDestType toTypes)
                                |> TypeConstraints.fromDefinitive)
                            unifyTypeErrors


                let combinedAcc =
                    funcParamsAccumulators
                    |> NEL.fold Acc.combineAccumulators Map.empty
                    |> Acc.combineAccumulators typeOfBody.acc


                /// This contains all the names defined from each param
                let combinedNamesDefinedHere =
                    funcParamsAccumulators
                    |> NEL.map getLocalValueNames
                    |> NEL.fold Set.union Set.empty

                let guidMap = makeGuidMapForNames combinedNamesDefinedHere


                Aaot.make
                    (replaceValueNamesWithGuidsInTypeJudgment guidMap arrowType)
                    (replaceValueNamesWithGuidsInAcc guidMap combinedAcc)


        | T.UpperIdentifier name ->
            Aaot.make
                (TypeConstraints.fromConstraint (ByConstructorType name)
                 |> Ok)
                Map.empty

        | T.LowerIdentifier name ->
            let inferredType =
                ByValue name
                |> TypeConstraints.fromConstraint
                |> Ok

            Aaot.make inferredType Map.empty


        | T.LetExpression (declarations, expr) ->
            let bodyExpr = getAccumulatorFromExpr expr

            let typedDeclarations =
                declarations
                |> NEL.map (fun binding ->
                    let bindingAccAndSelf = getAccumulatorFromBinding binding
                    let assignedExprAccAndSelf = getAccumulatorFromExpr binding.assignedExpression

                    let unifiedOwnType =
                        unifyJudgments assignedExprAccAndSelf.ownType bindingAccAndSelf.ownType

                    let unifiedAcc =
                        Acc.combineAccumulators assignedExprAccAndSelf.acc bindingAccAndSelf.acc

                    Aaot.make unifiedOwnType unifiedAcc)

            let bindingAccs = typedDeclarations |> NEL.map Aaot.getAcc

            let combinedAcc =
                bindingAccs
                |> NEL.fold Acc.combineAccumulators bodyExpr.acc

            /// This contains all the names defined from each param
            let combinedNamesDefinedHere =
                bindingAccs
                |> NEL.map getLocalValueNames
                |> NEL.fold Set.union Set.empty

            let guidMap = makeGuidMapForNames combinedNamesDefinedHere

            Aaot.make
                (replaceValueNamesWithGuidsInTypeJudgment guidMap bodyExpr.ownType)
                (deleteGuidsFromAcc guidMap combinedAcc)



        | T.ControlFlowExpression controlFlow ->
            match controlFlow with
            | T.IfExpression (cond, ifTrue, ifFalse) ->
                let condAccAndOwn = getAccumulatorFromExpr cond

                let condAccAndOwnWithBoolConstr =
                    // @TODO: I feel like there's gotta be a better abstraction for doing this, instead of tacking it on so manually. But I do also think that this kind of thing is fairly rare: a constraint imposed from the outside which *isn't* it being passed to a function as a parameter.
                    { condAccAndOwn with
                        ownType =
                            unifyJudgments
                                condAccAndOwn.ownType
                                (Ok (TypeConstraints.fromDefinitive (DtPrimitiveType Bool))) }

                let ifTrueAccAndOwn = getAccumulatorFromExpr ifTrue
                let ifFalseAccAndOwn = getAccumulatorFromExpr ifFalse

                let combinedAcc =
                    Acc.combineManyAccs [ condAccAndOwnWithBoolConstr.acc
                                          ifTrueAccAndOwn.acc
                                          ifFalseAccAndOwn.acc ]

                let combinedType = unifyJudgments ifTrueAccAndOwn.ownType ifFalseAccAndOwn.ownType

                Aaot.make combinedType combinedAcc




            | T.CaseMatch (exprToMatch, branches) ->
                let accsAndSelvesOfPatterns =
                    branches
                    |> NEL.map (fun branch ->
                        let branchAccAndSelf =
                            getAccumulatorFromParam (getParamFromPattern branch.matchPattern)

                        /// This contains all the names defined for this pattern
                        let combinedNamesDefinedHere = getLocalValueNames branchAccAndSelf.acc

                        let guidMap = makeGuidMapForNames combinedNamesDefinedHere

                        Aaot.make
                            (replaceValueNamesWithGuidsInTypeJudgment guidMap branchAccAndSelf.ownType)
                            (replaceValueNamesWithGuidsInAcc guidMap branchAccAndSelf.acc))
                    |> NEL.toList
                    |> Aaot.combineMany

                let matchExprAccAndSelf = getAccumulatorFromExpr exprToMatch

                // The combined accumulator and type from the matched expression and the patterns
                let combinedMatchExprAndPatterns =
                    Aaot.combine accsAndSelvesOfPatterns matchExprAccAndSelf

                // The combined accumulator and type from the branches
                let combinedBranches =
                    branches
                    |> NEL.map (fun branch -> getAccumulatorFromExpr branch.body)
                    |> NEL.toList
                    |> Aaot.combineMany

                let combinedAcc =
                    Acc.combineAccumulators combinedMatchExprAndPatterns.acc combinedBranches.acc


                Aaot.make combinedBranches.ownType combinedAcc




    | T.CompoundExpression compExpr ->
        match compExpr with
        | T.FunctionApplication (funcExpr, params_) ->

            let funcAccAndSelf = getAccumulatorFromExpr funcExpr
            let paramsAccAndSelves = params_ |> NEL.map getAccumulatorFromExpr

            let paramAndBodyAaot =
                match funcAccAndSelf.ownType with
                | Ok constr -> addMultipleParamConstraints constr paramsAccAndSelves Acc.empty

                | Error e ->
                    NEL.map Aaot.getAcc paramsAccAndSelves
                    |> NEL.fold Acc.combineAccumulators Acc.empty
                    |> Aaot.make (Error e)


            let combinedAcc = Acc.combineAccumulators paramAndBodyAaot.acc funcAccAndSelf.acc

            Aaot.make paramAndBodyAaot.ownType combinedAcc






        | T.DotAccess (dottedExpr, dotSequence) ->

            let rec makeImpliedRecStructure exprType dotSeqsLeft =
                match dotSeqsLeft with
                | [] -> Aaot.make (Ok exprType) Map.empty
                | firstDotter :: rest ->
                    let defRequirement =
                        DtRecordWith (
                            [ firstDotter, TypeConstraints.makeUnspecific () ]
                            |> Map.ofList
                        )

                    let requiredConstraint = TypeConstraints.fromDefinitive defRequirement

                    let unifiedTypeConstraints = unifyTypeConstraints exprType requiredConstraint
                    let acc = addConstraintToJudgment requiredConstraint unifiedTypeConstraints

                    let returnType : TypeJudgment =
                        unifiedTypeConstraints
                        |> Result.bind (function
                            | Constrained (Some (DtRecordWith fieldsMap), _)
                            | Constrained (Some (DtRecordExact fieldsMap), _) ->
                                match Map.tryFind firstDotter fieldsMap with
                                | Some valType -> Ok valType
                                | None -> Error (IncompatibleTypes [ defRequirement ])

                            | _ ->
                                // @TODO: this is technically not correct because this should be a list of multiple mutually irreconcilable definitive types, one on its own makes no sense. Need to actually implement what the correct type error logic would be.
                                Error (IncompatibleTypes [ defRequirement ]))

                    match returnType with
                    | Ok returnType_ ->
                        let recursiveAccAndSelf = makeImpliedRecStructure returnType_ rest

                        Aaot.make recursiveAccAndSelf.ownType (Acc.combineAccumulators acc recursiveAccAndSelf.acc)

                    | Error e -> Aaot.make (Error e) acc

            let exprAccAndSelf = getAccumulatorFromExpr dottedExpr

            let dottedExprAccAndSelf =
                exprAccAndSelf.ownType
                |> Result.map (fun constr -> makeImpliedRecStructure constr (NEL.toList dotSequence))
                |> function
                    | Ok accAndSelf -> accAndSelf
                    | Error e -> Aaot.make (Error e) Map.empty

            let combinedAcc =
                Acc.combineAccumulators exprAccAndSelf.acc dottedExprAccAndSelf.acc

            Aaot.make dottedExprAccAndSelf.ownType combinedAcc



        | T.Operator (left, op, right) ->
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"



and getAccumulatorFromExpr (expr : TypedExpr) : AccumulatorAndOwnType =
    getAccumulatorFromSingleOrCompExpr expr.expr


//and getAccumulatorFromParam (param : FunctionOrCaseMatchParam) : AccumulatorAndOwnType =
and getAccumulatorFromParam (param : AssignmentPattern) : AccumulatorAndOwnType =
    //failwith "@TODO: implement getAccumulatorFromParam"


    /// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
    ///
    /// We infer the types of the parameters based only on
    /// a) any structure implicit in a destructuring pattern
    /// b) their usage – not the usage from the param name
    ///
    /// @TODO: make this return an `AccumulatorAndOwnType`!
    let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : AccumulatorAndOwnType =
        match pattern with
        | Named ident ->
            let inferredType = TypeConstraints.makeUnspecific ()

            Acc.makeAccFromLocalIdentAndTypeConstraints ident inferredType
            |> Aaot.make (Ok inferredType)


        | Ignored -> Aaot.make (Ok TypeConstraints.empty) Map.empty

        | Unit -> Aaot.make (Ok <| TypeConstraints.fromDefinitive DtUnitType) Map.empty

        | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured

        | Aliased (pattern_, alias) ->
            let nestedAccAndType = getInferredTypeFromAssignmentPattern pattern_

            let aliasAcc = Acc.addJudgmentToAccum alias nestedAccAndType.ownType Map.empty

            let combinedAcc = Acc.combineAccumulators nestedAccAndType.acc aliasAcc
            Aaot.make nestedAccAndType.ownType combinedAcc






    and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : AccumulatorAndOwnType =
        match pattern with
        | DestructuredRecord fieldNames ->
            let fields =
                fieldNames
                |> NEL.map (fun recFieldName -> recFieldName, TypeConstraints.makeUnspecific ())
                |> NEL.toList
                |> Map.ofList

            let inferredType : TypeJudgment =
                fields
                |> DtRecordWith
                |> TypeConstraints.fromDefinitive
                |> Ok

            let acc : Accumulator =
                fields
                |> Map.fold
                    (fun acc fieldName constraints ->
                        Acc.makeAccFromLocalIdentAndTypeConstraints (recFieldToLowerIdent fieldName) constraints
                        |> Acc.combineAccumulators acc)
                    Map.empty


            Aaot.make inferredType acc


        | DestructuredCons consItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern consItems

            let inferredType : TypeJudgment =
                gatheredItems
                |> TOM.map Aaot.getSelf
                |> TOM.fold unifyJudgments (Ok TypeConstraints.empty)

            let acc : Accumulator =
                gatheredItems
                |> TOM.map Aaot.getAcc
                |> TOM.toList
                |> Acc.combineManyAccs

            Aaot.make inferredType acc


        | DestructuredTuple tupleItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern tupleItems

            let inferredType : TypeJudgment =
                gatheredItems
                |> TOM.map Aaot.getSelf
                |> TOM.sequenceResult
                |> Result.map (DtTuple >> TypeConstraints.fromDefinitive)
                |> concatResultErrListNel

            let acc : Accumulator =
                gatheredItems
                |> TOM.map Aaot.getAcc
                |> TOM.toList
                |> Acc.combineManyAccs


            Aaot.make inferredType acc


        | DestructuredTypeVariant (ctor, params_) ->
            let ctorType = ByConstructorType ctor

            let accAndSelf = makeArrowAndGetAccsAndSelves params_

            let selfType : TypeJudgment =
                accAndSelf.ownType
                |> Result.map (TypeConstraints.addConstraint ctorType)

            Aaot.make selfType accAndSelf.acc


    /// This is for a deconstructed newtype pattern match, which returns all the constraints and inferred accumulated information about the pattern matched params, to be used inside a function, let, or case match expression body
    and makeArrowAndGetAccsAndSelves (params_ : AssignmentPattern list) : AccumulatorAndOwnType =
        match params_ with
        | [] -> Aaot.make (Ok <| TypeConstraints.makeUnspecific ()) Map.empty
        | head :: rest ->
            let ofFirst = getInferredTypeFromAssignmentPattern head
            let ofRest = makeArrowAndGetAccsAndSelves rest

            let inferredType : TypeJudgment =
                (ofFirst.ownType, ofRest.ownType)
                ||> Result.map2
                        (fun ofFirst_ ofRest_ ->
                            DtArrow (ofFirst_, ofRest_)
                            |> TypeConstraints.fromDefinitive)
                        unifyTypeErrors

            let combinedAcc = Acc.combineAccumulators ofFirst.acc ofRest.acc

            Aaot.make inferredType combinedAcc


    getInferredTypeFromAssignmentPattern param



/// This gets the return type of the function, if we know that the function definitely has type Arrow. Otherwise it fails.
/// @TODO: which, on second thought, is not quite right because then it will fail unless we already know that it is an Arrow type, whereas actually this should impose its own constraint.
/// But I think the answer to the above is that this helper is only meant to be used after we've already tried to unify this with a definitive Arrow type, so any (compatible) function value should already have the definitive Arrow type by the time we get to this point.
and private getFuncReturnType (tc : TypeConstraints) : TypeJudgment =
    match tc with
    | Constrained (Some (DtArrow (_, toType)), _) -> Ok toType

    | Constrained _ ->
        let paramGeneric = TypeConstraints.makeUnspecific ()
        let returnGeneric = TypeConstraints.makeUnspecific ()

        let defFuncRequirement = DtArrow (paramGeneric, returnGeneric)
        Error (IncompatibleTypes [ defFuncRequirement ])


/// Ensure TypeConstraints is compatible with the params it's being called with, *but* don't narrow the function to only work with those params; because we want to maintain let polymorphism!
/// Hmm actually I think if we are to maintain let polymorphism, then instead of constraining the function's params and output type to only work with those from this one instance of its use, we actually *reverse* the constraints, and from this function we infer constraints on the param or params (and maybe its output also?)
/// So I think what this function needs to do is:
///     a) on the value called as a function: simply add a constraint that it needs to be a function
///         i. and maybe actually add additional constraints from the shape of its param(s); but nothing else! no narrowing of the param types based on the value it's called with!
///     b) impose any param-inferred constraints from the function onto the *value* it is called with - so not vice versa
//and addArrowConstraint
//    (funcExprConstraint : TypeConstraints)
//    (paramPattern : AssignmentPattern)
//    (actualParamType : TypeConstraints)
//    (acc : Accumulator)
//    : AccumulatorAndOwnType =
//    let paramAccAndOwn = getAccumulatorFromParam paramPattern

//    match paramAccAndOwn.ownType with
//    | Ok paramType ->
//        let funcRequirementConstraint =
//            DtArrow (paramType, TypeConstraints.makeUnspecific ())
//            |> TypeConstraints.fromDefinitive

//        let funcJudgment = unifyTypeConstraints funcRequirementConstraint funcExprConstraint
//        let actualParamJudgment = unifyTypeConstraints paramType actualParamType

//        let returnType = funcJudgment |> Result.bind getFuncReturnType

//        let newAcc =
//            acc
//            |> Acc.addSingleTypeConstraint funcRequirementConstraint
//            |> Acc.addSingleTypeJudgment actualParamJudgment
//            |> Acc.combineAccumulators paramAccAndOwn.acc

//        Aaot.make returnType newAcc

//    | Error e -> Aaot.make (Error e) acc




and addArrowConstraint


    (*



    @TODO: add the function expression itself in here - or at least its referenced name - because to ensure we're tracking that a function `f` is a function with whatever signature it has, we need to pass that name f into the Accumulator. Otherwise we're only storing the other type constraints about the function in the Acc that we bubble up from here, but not actually tracking `f`'s own type!



    *)


    (funcExprConstraint : TypeConstraints)
    (actualParamAccAndOwn : AccumulatorAndOwnType)
    (acc : Accumulator)
    : AccumulatorAndOwnType =

    let paramRefConstr = newGuid () |> IsBoundVar

    let paramConstraint = TypeConstraints.fromConstraint paramRefConstr
    let putativeReturnType = TypeConstraints.makeUnspecific ()

    let funcRequirementConstraint =
        DtArrow (paramConstraint, putativeReturnType)
        |> TypeConstraints.fromDefinitive

    let funcJudgment = unifyTypeConstraints funcRequirementConstraint funcExprConstraint

    let actualParamJudgment =
        unifyJudgments (Ok paramConstraint) actualParamAccAndOwn.ownType

    let returnType = funcJudgment |> Result.bind getFuncReturnType

    let newAcc =
        acc
        |> Acc.addSingleTypeConstraint funcRequirementConstraint
        |> Acc.addSingleTypeJudgment actualParamJudgment
        |> Acc.combineAccumulators actualParamAccAndOwn.acc

    Aaot.make returnType newAcc



and addMultipleParamConstraints
    (funcExprConstraint : TypeConstraints)
    (actualParams : AccumulatorAndOwnType nel)
    (acc : Accumulator)
    : AccumulatorAndOwnType =
    actualParams
    |> NEL.fold
        (fun state actualParam ->
            match state.ownType with
            | Ok constr -> addArrowConstraint constr actualParam state.acc
            | Error e -> Aaot.make (Error e) acc)
        (Aaot.make (Ok funcExprConstraint) acc)





and getAccumulatorFromBinding (binding : LetBinding) : AccumulatorAndOwnType =
    failwith "@TODO: implement getAccumulatorFromBinding"


/// This takes a map of names defined in this scope and the full combined Accumulator, and replaces the named values defined at this scope with GUIDs, so that they no longer reference named values (which are not in scope and therefore meaningless outside of this scope!) and replace them with simple GUIDs which therefore act as simple type variables
/// --This takes a map of names defined in this scope and the full combined Accumulator, and returns the map of names in this scope along with their definitive types and generics (exposed as guids) along with a new Accumulator with those names removed - since those names are no longer exposed to parent scopes and so constraints are no longer relevant to higher scopes
and replaceParamsFromAcc (names : Map<LowerIdent, TypeJudgment>) (acc : Accumulator) : Accumulator =
    failwith "@TODO: implement replaceParamsFromAcc"

/// This will only return names in the keys and only if they are locally defined, not namespaced ones
and getLocalValueNames (acc : Accumulator) : LowerIdent set =
    //failwith
    //    "@TODO: this should get all the value names in the Accumulator. So that we get all the names defined in a param or let binding, and replace it with type variable GUIDs. So this tells us which names we should be replacing."
    Map.keys acc
    |> Set.unionMany
    |> Set.choose (function
        | ByValue (LocalLower name) -> Some name
        | _ -> None)


and makeGuidMapForNames (names : LowerIdent set) : Map<LowerIdent, System.Guid> =
    failwith "@TODO: generates a GUID for each name given"


and replaceValueNamesWithGuidsInAcc (names : Map<LowerIdent, System.Guid>) (acc : Accumulator) : Accumulator =
    failwith "@TODO: replaces all the names in the given accumulator with GUIDs"

and replaceValueNamesWithGuidsInTypeJudgment
    (names : Map<LowerIdent, System.Guid>)
    (typeJudgment : TypeJudgment)
    : TypeJudgment =
    failwith
        "@TODO: implement replaceValueNamesWithGuidsInTypeJudgment. Replaces all the names in the given type judgment with GUIDs"

/// @TODO: removes all the listed GUIDs from the Accumulator, for a let expression so that we don't expose the names or type variables and shit to higher scopes when they're no longer needed.
and deleteGuidsFromAcc (names : Map<LowerIdent, System.Guid>) (acc : Accumulator) : Accumulator =
    failwith "@TODO: implement deleteGuidsFromAcc. Removes all the listed GUIDs from the Accumulator"


/// Denotes that a type judgment has another constraint upon it
and addConstraintToJudgment (constr : TypeConstraints) (judgment : TypeJudgment) : Accumulator =
    failwith "@TODO: implement addConstraintToJudgment"


and addJudgmentConstraintToAccumulator
    (constr : TypeConstraints)
    (judgment : TypeJudgment)
    (acc : Accumulator)
    : Accumulator =
    addConstraintToJudgment constr judgment
    |> Acc.combineAccumulators acc









//let rec getBoundVarsFromType (type_ : DefinitiveType) : TypeConstraints set =
//    match type_ with
//    | DtUnitType -> Set.empty
//    | DtPrimitiveType _ -> Set.empty
//    | DtArrow (fromType, toType) ->
//        Set.union (getBoundVarsFromTypeConstraint fromType) (getBoundVarsFromTypeConstraint toType)
//    | DtTuple tom ->
//        TOM.map getBoundVarsFromTypeConstraint tom
//        |> TOM.toList
//        |> Set.unionMany
//    | DtList list -> getBoundVarsFromTypeConstraint list
//    | DtRecordWith map ->
//        Map.values map
//        |> Seq.map getBoundVarsFromTypeConstraint
//        |> Set.unionMany
//    | DtRecordExact map ->
//        Map.values map
//        |> Seq.map getBoundVarsFromTypeConstraint
//        |> Set.unionMany
//    | DtNewType (_, typeParams) ->
//        List.map (snd >> getBoundVarsFromTypeConstraint) typeParams
//        |> Set.unionMany

//and getBoundVarsFromTypeConstraint (typeConstraint : TypeConstraints) =
//    match typeConstraint with
//    | Recursive -> Set.empty
//    | Constrained (defOpt, others) ->
//        let boundVarsFromOthers =
//            Set.choose getBoundVarsFromRefConstr others
//            |> Set.map IsBoundVar
//            |> Set.toList

//        match defOpt with
//        | Some def ->
//            Set.ofList boundVarsFromOthers
//            |> Set.union (getBoundVarsFromType def)

//        | None -> Set.ofList boundVarsFromOthers


//and private getBoundVarsFromRefConstr (refConstr : RefConstr) : TypeConstraintId option =
//    match refConstr with
//    | IsBoundVar var -> Some var
//    | _ -> None










/// Just a container to ferry the type and declarations to the TST module type
type private TypeAndDeclarations =
    { name : UpperIdent
      declaration : T.TypeDeclaration
      ctors : T.VariantConstructor list }


let private getTypeAndDeclaration
    (typeName : S.CstNode<UnqualTypeOrModuleIdentifier>)
    (decl : Cst.TypeDeclaration)
    : TypeAndDeclarations =
    match decl with
    | S.Alias aliasDecl ->
        let typeParamsList =
            aliasDecl.typeParams
            |> List.map (S.getNode >> unqualValToLowerIdent)

        let typeDeclaration : T.TypeDeclarationContent =
            mentionableTypeToDefinite aliasDecl.referent.node
            |> T.Alias

        let typeDecl : T.TypeDeclaration =
            { typeParamsMap =
                typeParamsList
                |> List.map (fun typeParam -> typeParam, ())
                |> SOD.makeMapFromList
              typeParamsList = typeParamsList
              typeDeclaration = typeDeclaration }

        let typeIdent = unqualTypeToUpperIdent typeName.node

        { name = typeIdent
          declaration = typeDecl
          ctors = List.empty }

    | S.Sum sumDecl ->
        let typeParamsList =
            sumDecl.typeParams
            |> List.map (S.getNode >> unqualValToLowerIdent)

        let typeParamsMap =
            typeParamsList
            |> List.map (fun typeParam -> typeParam, ())
            |> SOD.makeMapFromList

        let variantCases =
            sumDecl.variants
            |> NEL.map (fun variantCase ->
                let contents =
                    variantCase.node.contents
                    |> List.map (S.getNode >> mentionableTypeToDefinite)

                { label = unqualTypeToUpperIdent variantCase.node.label.node
                  contents = contents })

        let typeDeclaration = T.Sum variantCases

        let typeIdent = unqualTypeToUpperIdent typeName.node

        let variantConstructors : T.VariantConstructor nel =
            variantCases
            |> NEL.map (fun variantCase ->
                { typeParamsList = typeParamsList
                  typeParamsMap = typeParamsMap
                  variantCase = variantCase
                  allVariants = variantCases
                  typeName = typeIdent })


        let typeDecl : T.TypeDeclaration =
            { typeParamsMap = typeParamsMap
              typeParamsList = typeParamsList
              typeDeclaration = typeDeclaration }

        { name = typeIdent
          declaration = typeDecl
          ctors = NEL.toList variantConstructors }




let typeCheckModule (ylModule : Cst.YlModule) : T.YlModule =
    /// @TODO: Hmm looks we don't really do anything with the type constructors yet. Need to make sure we're using them to resolve any referenced constructors in the values.
    let typesAndConstructors =
        ylModule.declarations
        |> List.choose (
            S.getNode
            >> function
                | S.TypeDeclaration (typeName, decl) -> getTypeAndDeclaration typeName decl |> Some
                | _ -> None
        )

    let typesNames =
        typesAndConstructors
        |> List.map (fun typeAndCtor -> typeAndCtor.name, typeAndCtor.declaration)
        |> SOD.makeMapFromList

    let infixOps =
        ylModule.declarations
        |> List.choose (
            S.getNode
            >> function
                | S.InfixOperatorDeclaration infixOp ->
                    Some (
                        unqualValToLowerIdent infixOp.name,
                        { associativity = infixOp.associativity
                          precedence = infixOp.precedence
                          value = typeCheckCstExpression List.empty infixOp.value.node }
                    )
                | _ -> None
        )
        |> SOD.makeMapFromList


    let imports =
        ylModule.declarations
        |> List.choose (
            S.getNode
            >> function
                | S.ImportDeclaration import -> Some import
                | _ -> None
        )

    let values =
        ylModule.declarations
        |> List.choose (
            S.getNode
            >> function
                | S.ValueDeclaration valDecl ->
                    let ident = unqualValToLowerIdent valDecl.valueName.node

                    Some (
                        ident,
                        // @TODO: make sure we're actually passing in the names required for resolution here
                        typeCheckCstExpression [ ident ] valDecl.value.node
                    )
                | _ -> None
        )
        |> SOD.makeMapFromList

    let valueTypes : T.ValueTypeDeclarations =
        ylModule.declarations
        |> List.choose (
            S.getNode
            >> function
                | S.ValueTypeAnnotation annotation ->
                    let ident = unqualValToLowerIdent annotation.valueName.node

                    Some (LocalLower ident, mentionableTypeToDefinite annotation.annotatedType.node)
                | _ -> None
        )
        |> SOD.makeMapFromList


    { moduleDecl = ylModule.moduleDecl
      imports = imports
      types = typesNames
      values = values
      valueTypes = valueTypes
      infixOperators = infixOps }

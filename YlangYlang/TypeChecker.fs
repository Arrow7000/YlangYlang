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
let rec makeDestType ((NEL (first, rest)) : TypeConstraints nel) : TypeConstraints =
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



















module TypeConstraints =

    let fromDef = TypeConstraints.fromDefinitive
    let fromRef = TypeConstraints.fromConstraint

    /// Alias for TC.makeUnspecific
    let any () = TypeConstraints.makeUnspecific ()

///// @TODO: this needs to be fixed now that `Constrained` types no longer just refer to generically typed params, but also to references to concrete values defined elsewhere!
///// Not entirely sure yet how to do this without having to pass in names maps to this function, which I don't want to do, because of the circular definition problem (i.e. in a let bindings list all values can reference all others, even ones defined after itself, so we can't type check each value in isolation but have to "convert" them to type checked values all at once, and the only way we can do that is by allowing a type of an expression to be a reference to "whatever the type of value X is")
//let rec unifyTypeConstraints (typeA : TypeConstraints) (typeB : TypeConstraints) : TypeJudgment =
//    match typeA, typeB with
//    | Constrained (Some defA, cnstrntsA), Constrained (Some defB, cnstrntsB) ->
//        unifyDefinitiveTypes defA defB
//        |> Result.map (fun unified -> Constrained (Some unified, Set.union cnstrntsA cnstrntsB))

//    | Constrained (Some def, cnstrntsA), Constrained (None, cnstrntsB)
//    | Constrained (None, cnstrntsA), Constrained (Some def, cnstrntsB) ->
//        Constrained (Some def, Set.union cnstrntsA cnstrntsB)
//        |> Ok

//    | Constrained (None, cnstrntsA), Constrained (None, cnstrntsB) ->
//        Constrained (
//            None,
//            // @TODO: this may not be a simple union of reference constraints, they need to be unified with their own unifier function!
//            Set.union cnstrntsA cnstrntsB
//        )
//        |> Ok





///// @TODO: remember to resolve named types to check for unification, e.g. with named alias type and record
//and unifyDefinitiveTypes (typeA : DefinitiveType) (typeB : DefinitiveType) : Result<DefinitiveType, TypeError> =
//    match typeA, typeB with
//    | DtTuple a, DtTuple b ->
//        unifyTypesTom a b
//        |> Result.mapError (fun (first, second) ->
//            TypeError.fromTypes [ DtTuple first
//                                  DtTuple second ])
//        |> Result.bind (TOM.sequenceResult >> concatResultErrListNel)
//        |> Result.map DtTuple

//    | DtList a, DtList b -> unifyTypeConstraints a b |> Result.map DtList

//    | DtArrow (fromA, toA), DtArrow (fromB, toB) ->
//        (unifyTypeConstraints fromA fromB, unifyTypeConstraints toA toB)
//        ||> Result.map2
//                (fun fromType toType -> DtArrow (fromType, toType))
//                (fun _ _ ->
//                    TypeError.fromTypes [ DtArrow (fromA, toA)
//                                          DtArrow (fromB, toB) ])
//    //let unifiedToTypes =
//    //    unifyTypesNel toA toB
//    //    |> Result.mapError (fun _ ->
//    //        TypeError.fromTypes [ DtArrow (fromA, toA)
//    //                              DtArrow (fromB, toB) ])
//    //    |> Result.bind (NEL.sequenceResult >> concatResultErrListNel)

//    //(unifyTypeConstraints fromA fromB, unifiedToTypes)
//    //||> Result.map2
//    //        (fun fromType toTypes_ -> DtArrow (fromType, toTypes_))
//    //        (fun _ _ ->
//    //            TypeError.fromTypes [ DtArrow (fromA, toA)
//    //                                  DtArrow (fromB, toB) ])

//    | DtNewType (typeRefA, typeParamsA), DtNewType (typeRefB, typeParamsB) ->
//        if typeRefA = typeRefB then
//            unifyTypesList typeParamsA typeParamsB
//            |> Result.mapError (fun _ -> TypeError.fromTypes [ typeA; typeB ])
//            |> Result.bind (Result.sequenceList >> concatResultErrListNel)
//            |> Result.map (fun unifiedParams -> DtNewType (typeRefA, unifiedParams))

//        else
//            Error <| TypeError.fromTypes [ typeA; typeB ]

//    | DtRecordExact a, DtRecordExact b ->
//        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
//        |> Result.mapError (fun _ ->
//            TypeError.fromTypes [ DtRecordExact a
//                                  DtRecordExact b ])
//        |> Result.bind (
//            Map.sequenceResult
//            >> Result.mapError (
//                fst
//                >> Map.values
//                >> Seq.toList
//                >> combineTypeErrorsFromList
//            )
//        )
//        |> Result.map DtRecordExact

//    | DtRecordWith a, DtRecordWith b ->
//        Map.mergeExact (fun _ valueA valueB -> unifyTypeConstraints valueA valueB) a b
//        |> Result.mapError (fun _ ->
//            TypeError.fromTypes [ DtRecordWith a
//                                  DtRecordWith b ])
//        |> Result.bind (
//            Map.sequenceResult
//            >> Result.mapError (
//                fst
//                >> Map.values
//                >> Seq.toList
//                >> combineTypeErrorsFromList
//            )
//        )
//        |> Result.map DtRecordExact

//    | DtRecordExact a, DtRecordWith b
//    | DtRecordWith b, DtRecordExact a -> failwith "@TODO: unify record and extended record types when compatible"

//    | DtUnitType, DtUnitType -> DtUnitType |> Ok
//    | DtPrimitiveType a, DtPrimitiveType b ->
//        if a = b then
//            DtPrimitiveType a |> Ok
//        else
//            TypeError.fromTypes [ DtPrimitiveType a
//                                  DtPrimitiveType b ]
//            |> Error

//    | _, _ -> Error <| TypeError.fromTypes [ typeA; typeB ]





////and getConstrainedValues (constraintsList : TypeConstraints list) : Map<LowerNameValue, TypeJudgment> =
////    constraintsList
////    |> List.fold
////        (fun map constrainedValue ->

////            match constrainedValue with
////            | TypeConstraints (def, others) ->

////                let setFolder (state: (LowerNameValue set * TypeJudgment)) (constrainType: ConstrainType) =
////                    match constrainType with
////                    | ByValue name ->
////                        match Map.tryFind name state with
////                        | None -> Map.add name (Ok (TypeConstraints (def, others))) state

////                        | Some constraintsForName -> Map.add name (unifyJudgments (Ok constrainedValue) constraintsForName) state


////                    | _ -> state


////                let combinedFromOthers = Set.fold setFolder map others

////            //| Recursive ->
////            )
////        Map.empty


/////// @TODO: this should basically allow for shrinking the referenced constraints and maybe unifying the concrete constraints, in the case when a name becomes available for resolution
////and concretiseConstraintValue (name : LowerNameValue) (constraints : TypeConstraints) : TypeJudgment =
////    let tryConcretiseSingleConstraintAndAdd
////        (constrainType : ConstrainType)
////        (typeConstraints : TypeConstraints)
////        : TypeJudgment =
////        match constrainType with
////        | ByValue valName ->
////            if name = valName then
////                Ok Recursive
////            else
////                unifyTypeConstraints typeOfName typeConstraints

////        | _ -> unifyTypeConstraints typeOfName typeConstraints

////    match constraints with
////    | Recursive -> Ok Recursive
////    | TypeConstraints (def, constraintSet) ->
////        let state : TypeConstraints =
////            Option.map TypeConstraints.makeFromDefinitive def
////            |> Option.defaultValue TypeConstraints.empty


////        constraintSet
////        |> Set.fold
////            (fun result constrainType -> Result.bind (tryConcretiseSingleConstraintAndAdd constrainType) result)
////            (Ok state)


///// If lengths are the same, returns a list of that length of the type judgments of trying to merge the type at every index in both lists. If lengths are not the same though, returns an error result of both inferred types lists.
//and private listTraverser (onLengthErr : 'Err) (listA : TypeConstraints list) (listB : TypeConstraints list) =
//    match listA, listB with
//    | [], [] -> Ok []
//    | headA :: tailA, headB :: tailB ->
//        let unifiedHead = unifyTypeConstraints headA headB

//        listTraverser onLengthErr tailA tailB
//        |> Result.map (fun unifiedTail -> unifiedHead :: unifiedTail)

//    | [], _ :: _
//    | _ :: _, [] -> Error onLengthErr



//and unifyTypesList
//    (listA : TypeConstraints list)
//    (listB : TypeConstraints list)
//    : Result<TypeJudgment list, TypeConstraints list * TypeConstraints list> =
//    listTraverser (listA, listB) listA listB

//and unifyTypesNel
//    (NEL (headA, tailA) as nelA : TypeConstraints nel)
//    (NEL (headB, tailB) as nelB : TypeConstraints nel)
//    : Result<TypeJudgment nel, TypeConstraints nel * TypeConstraints nel> =
//    listTraverser (nelA, nelB) tailA tailB
//    |> Result.map (fun unifiedTail ->
//        let unifiedHead = unifyTypeConstraints headA headB
//        NEL (unifiedHead, unifiedTail))



//and unifyTypesTom
//    (TOM (headA, neckA, tailA) as listA : TypeConstraints tom)
//    (TOM (headB, neckB, tailB) as listB : TypeConstraints tom)
//    : Result<TypeJudgment tom, TypeConstraints tom * TypeConstraints tom> =
//    listTraverser (listA, listB) tailA tailB
//    |> Result.map (fun unifiedTail ->
//        let unifiedHead = unifyTypeConstraints headA headB
//        let unifiedNeck = unifyTypeConstraints neckA neckB
//        TOM (unifiedHead, unifiedNeck, unifiedTail))




///// If both judgments are ok it unifies their constraints. Otherwise it adds any concrete types to the errors list, or combines errors.
/////
///// @TODO: this should really also include the other `ConstrainType`s that can be resolved and evaluate to definitive types in case some of them are also incompatible with the other constraints
//and unifyJudgments (judgmentA : TypeJudgment) (judgmentB : TypeJudgment) =
//    match judgmentA, judgmentB with
//    | Ok a, Ok b -> unifyTypeConstraints a b

//    | Error err, Ok (Constrained (Some t, _))
//    | Ok (Constrained (Some t, _)), Error err ->
//        unifyTypeErrors (TypeError.fromTypes [ t ]) err
//        |> Error

//    | Error e, Ok (Constrained (None, _))
//    | Ok (Constrained (None, _)), Error e -> Error e

//    | Error a, Error b -> unifyTypeErrors a b |> Error

////| Error e, Ok Recursive
////| Ok Recursive, Error e -> Error e





//and unifyDefinitiveJudgments
//    (judgmentA : Result<DefinitiveType, TypeError>)
//    (judgmentB : Result<DefinitiveType, TypeError>)
//    : Result<DefinitiveType, TypeError> =
//    match judgmentA, judgmentB with
//    | Ok a, Ok b -> unifyDefinitiveTypes a b

//    | Ok a, Error e
//    | Error e, Ok a -> addDefToTypeError a e |> Error

//    | Error a, Error b -> unifyTypeErrors a b |> Error


//let addConstraint (newConstraint : RefConstr) (constraints : TypeConstraints) : TypeConstraints =
//    match constraints with
//    | Constrained (def, cnstrnts) -> Constrained (def, Set.add newConstraint cnstrnts)
////| Recursive ->
////    // This tries to represent the logic for a recursive function that contains a base case: i.e. if one branch calls the function recursively but the other branch returns a non-recursive value with a type that can be inferred concretely, then the inferred type is that of the base case and the recursive branch is irrelevant to the type of the expression.
////    //
////    // @TODO: However this probably does not work for non-function *values*, which unlike functions cannot be referenced recursively in their own definitions (unless it is referenced inside a function) because otherwise evaluating itself will instantly cause an infinite expansion and a stack overflow. So we probably need a different way to express recursiveness in a non-function value so that we do return an error, and don't just throw away the recursiveness information.
////    // We actually need to be able to represent 2 things:
////    // - The fact that an expression calls itself with no base case
////    // - The fact that an expression calls itself with no parameters in the middle to halt the immediate expansion
////    //
////    // But actually these two things are one and the same: the fact that an expression references itself without changing any of the parameters it feeds to itself! This is true not just for functions that do not have a base case at all, but even for functions that call themselves without changing any of their parameters – which would also result in an infinite loop – and also values that reference themselves without being functions with parameters in the middle – because those also technically have "no changed parameters" because a non-function value can still be thought of as a function, just with a list of parameters 0 items in length. And referencing itself therefore qualifies as "not changing the parameters it feeds itself" because every empty list is the same as any other!

////    TypeConstraints.fromConstraint newConstraint


//let addDefinitiveType (newDef : DefinitiveType) (constraints : TypeConstraints) : TypeJudgment =
//    match constraints with
//    | Constrained (def, cnstrnts) ->
//        match def with
//        | None -> Constrained (Some newDef, cnstrnts) |> Ok
//        | Some def_ ->
//            let unifiedResult = unifyDefinitiveTypes def_ newDef

//            unifiedResult
//            |> Result.map (fun unified -> Constrained (Some unified, cnstrnts))














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

        //IsOfTypeByName (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
        //|> TypeConstraints.fromConstraint
        DtNewType (typeOrModuleIdentToUpperNameVal typeName.node, definiteTypeParams)
        |> TypeConstraints.fromDefinitive

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




let typeOfPrimitiveLiteral (primitive : S.PrimitiveLiteralValue) : DefinitiveType =
    match primitive with
    | S.NumberPrimitive num ->
        match num with
        | S.FloatLiteral _ -> DtPrimitiveType Float
        | S.IntLiteral _ -> DtPrimitiveType Int
    | S.CharPrimitive _ -> DtPrimitiveType Char
    | S.StringPrimitive _ -> DtPrimitiveType String
    | S.UnitPrimitive _ -> DtUnitType
    | S.BoolPrimitive _ -> DtPrimitiveType Bool





let refDeftypeOfPrimitiveLiteral (primitive : S.PrimitiveLiteralValue) : RefDefType =
    match primitive with
    | S.NumberPrimitive num ->
        match num with
        | S.FloatLiteral _ -> RefDtPrimitiveType Float
        | S.IntLiteral _ -> RefDtPrimitiveType Int
    | S.CharPrimitive _ -> RefDtPrimitiveType Char
    | S.StringPrimitive _ -> RefDtPrimitiveType String
    | S.UnitPrimitive _ -> RefDtUnitType
    | S.BoolPrimitive _ -> RefDtPrimitiveType Bool




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







//module Accumulator =

//    module TC = TypeConstraints

//    (*
//    This should:
//    - based on the intersections of which referenced values are colocated with which other referenced values and definitive types, build up a set of groups of all the inferred types for the referenced values
//    - unify the definitive types in each group
//    - from each group, construct a map for all the referenced value names as keys, the values of which is the same combined type for each of them
//    - we can do this for a list of values and keep accumulating the same referenced value names with their usages in the other type constraints; that will allow us to construct a map where for each referenced value name we have a much specified TypeConstraints – which is effectively equal to having an inferred type for the value by that name!

//    And it's only after doing all of that that it maybe makes sense to go back in and resolve all the referenced value types in an expression? Although tbh maybe even then not. Maybe internally where those values are referenced we just keep them as is, and it's only from the outside that we glean which types those things _must_ be, which we can then view from the outside

//    So then there's the separate question of how we can then use that to figure out if there is some recursion anywhere? Because we need to know whether a value references itself inside its own definition so that we know not to try to resolve the type of that thing completely... but then tbh are we even attempting to do that anymore with this new approach?

//    *)








//    (*
//        Create and add/combine
//    *)

//    let empty = Map.empty












//    /// This contains the core logic for adding a new constraint to the Acc
//    let rec addSingleConstrainedValueResult
//        (defTypeOptResult : Result<DefinitiveType option, TypeError>)
//        (namesSet : RefConstr set)
//        (acc : Accumulator)
//        : Accumulator =
//        let predicate k _ =
//            Set.intersect namesSet k |> Set.isNotEmpty

//        let combineTwoDefOptResults
//            (a : Result<DefinitiveType option, TypeError>)
//            (b : Result<DefinitiveType option, TypeError>)
//            : Result<DefinitiveType option, TypeError> =
//            match a, b with
//            | Ok (Some a_), Ok (Some b_) -> TC.unifyDefinitiveTypes a_ b_ |> Result.map Some

//            | Ok (Some def), Ok None
//            | Ok None, Ok (Some def) -> Ok (Some def)

//            | Ok None, Ok None -> Ok None

//            | Error err1, Error err2 -> unifyTypeErrors err1 err2 |> Error

//            | Ok _, Error e
//            | Error e, Ok _ -> Error e



//        let combiner
//            (keyvalList : (RefConstr set * Result<DefinitiveType option, TypeError>) list)
//            : RefConstr set * Result<DefinitiveType option, TypeError> =
//            let keySets, defTypes = List.unzip keyvalList

//            let newKey = Set.unionMany keySets

//            let newVal =
//                defTypes
//                |> List.fold combineTwoDefOptResults defTypeOptResult

//            newKey, newVal

//        Map.combineManyKeys predicate combiner acc




//    /// Adds a single new (non-error) constrained value to an Accumulator
//    let private addSingleConstrainedValue
//        (defTypeOpt : DefinitiveType option)
//        (namesSet : RefConstr set)
//        (acc : Accumulator)
//        =
//        addSingleConstrainedValueResult (Ok defTypeOpt) namesSet acc


//    let addSingleTypeConstraint (constr : TypeConstraints) (acc : Accumulator) : Accumulator =
//        let (Constrained (defOpt, others)) = constr

//        addSingleConstrainedValue defOpt others acc


//    let addSingleTypeJudgment (judgment : TypeJudgment) (acc : Accumulator) : Accumulator =
//        match judgment with
//        | Ok tc -> addSingleTypeConstraint tc acc
//        | Error _ -> acc


//    let private makeAccumFromConstraints (constraintsList : TypeConstraints list) : Accumulator =
//        constraintsList
//        |> List.fold (fun state cnstrnt -> addSingleTypeConstraint cnstrnt state) Map.empty






//    let addJudgmentToAccum (ident : LowerIdent) (judgment : TypeJudgment) (acc : Accumulator) : Accumulator =
//        let (defOptResult, refConstraints) =
//            match judgment with
//            | Ok (Constrained (defOpt, others)) -> Ok defOpt, others
//            | Error e -> Error e, Set.empty

//        let namesToAdd = Set.add (ByValue (LocalLower ident)) refConstraints

//        addSingleConstrainedValueResult defOptResult namesToAdd acc


//    let makeAccFromTypeConstraints (tc : TypeConstraints) : Accumulator = addSingleTypeConstraint tc Map.empty





//    /// Add information about a named TypeConstraints into the Acc
//    let makeAccFromNamedTypeConstraints (ident : LowerNameValue) (tc : TypeConstraints) : Accumulator =
//        TypeConstraints.addConstraint (ByValue ident) tc
//        |> makeAccFromTypeConstraints


//    /// Add information about a named TypeConstraints for a value into the Acc
//    let makeAccFromLocalIdentAndTypeConstraints (ident : LowerIdent) (tc : TypeConstraints) : Accumulator =
//        makeAccFromNamedTypeConstraints (LocalLower ident) tc





//    (*
//        Combine Accs together
//    *)

//    /// In other words allow for merging constrained value constraints from two different maps
//    let combineAccumulators (acc1 : Accumulator) (acc2 : Accumulator) : Accumulator =
//        acc1
//        |> Map.fold (fun acc key value -> addSingleConstrainedValueResult value key acc) acc2

//    let addManyAccs (newAccs : Accumulator seq) (acc : Accumulator) : Accumulator =
//        Seq.fold combineAccumulators acc newAccs

//    let combineManyAccs (accs : Accumulator seq) : Accumulator = addManyAccs accs Map.empty






//    (*
//        Get information out of the Acc
//    *)

//    /// This takes an Acc and for each defType value it takes the TypeConstraints it contains, replaces it with a guid token, and sticks those replaced type constraints into the Acc, whilst flattening those too. All the while unifying the things it adds to the top level
//    let flattenAccVals (acc : Accumulator) = ()


//    /// Given a TypeConstraints, this uses the information from the Accumulator to populate the TC with as much (relevant and actionable) information as possible
//    let informTypeWithAcc (tc : TypeConstraints) (acc : Accumulator) = Ok ()




//    /// Returns a map of the referenced values inside an Acc and the type constraints they've been inferred to have
//    let private makeMapFromAccum (accum : Accumulator) : Map<RefConstr, TypeJudgment> =
//        let convertSingleAccEntryBack (nameSet : RefConstr set) (defOpt : DefinitiveType option) : TypeConstraints =
//            Constrained (defOpt, nameSet)

//        accum
//        // Convert it back to a map of names with their inferred types
//        |> Map.toList
//        |> List.collect (fun (nameSet, defOptResult) ->
//            let constraintsForNameGroup =
//                Result.map (convertSingleAccEntryBack nameSet) defOptResult

//            Set.toList nameSet
//            |> List.map (Tuple.makePairWithSnd constraintsForNameGroup))
//        |> Map.ofList


//    /// This is the function that infers all the types for all referenced values based on a list of TypeConstraints!
//    let getConstrainedRefs (constraintsList : TypeConstraints list) : Map<RefConstr, TypeJudgment> =
//        makeAccumFromConstraints constraintsList
//        |> makeMapFromAccum


//    let getConstrainedValues =
//        getConstrainedRefs
//        >> Map.chooseKeyVals (fun constr judgment ->
//            match constr with
//            | ByValue name -> Some (name, judgment)
//            | _ -> None)



//    let getConstrainedLocalValues =
//        getConstrainedRefs
//        >> Map.chooseKeyVals (fun constr judgment ->
//            match constr with
//            | ByValue (LocalLower name) -> Some (name, judgment)
//            | _ -> None)




/// Basically the same as the AccumulatorAndOwnType
type AccAndTypeId =
    { typeId : AccumulatorTypeId
      acc : Accumulator }


module AccAndTypeId =
    let make accTypeId acc : AccAndTypeId = { acc = acc; typeId = accTypeId }

    let getId (aati : AccAndTypeId) = aati.typeId
    let getAcc (aati : AccAndTypeId) = aati.acc



type AccChangeToMake =
    { idsToReplace : AccumulatorTypeId seq
      /// So I guess this is also the ID that the thing has returned?
      idToReplaceWith : AccumulatorTypeId
      typeToInsertForId : Result<RefDefType, AccTypeError> option
      refConstrsForId : RefConstr set }



module AccChangeToMake =

    type MultipleChanges = AccChangeToMake seq

    type MultipleAndAccId =
        { typeId : AccumulatorTypeId
          changes : MultipleChanges }


    let getId (actm : AccChangeToMake) : AccumulatorTypeId = actm.idToReplaceWith
    let getIdFromMultiple (actms : MultipleAndAccId) = actms.typeId

    let getChanges (actm : MultipleAndAccId) : MultipleChanges = actm.changes

    /// Convert a single change to an Accumulator
    let singleChangeToAcc (change : AccChangeToMake) : Accumulator =
        { redirectMap =
            change.idsToReplace
            |> Seq.map (fun id -> id, change.idToReplaceWith)
            |> Map.ofSeq
          refConstraintsMap =
            Map.empty
            |> Map.add change.idToReplaceWith (change.typeToInsertForId, change.refConstrsForId) }

    /// Convert multiple changes to an Accumulator
    let multipleChangesToAcc (changes : MultipleChanges) : Accumulator =
        { redirectMap =
            changes
            |> Seq.collect (fun change ->
                change.idsToReplace
                |> Seq.map (fun id -> id, change.idToReplaceWith))
            |> Map.ofSeq
          refConstraintsMap =
            changes
            |> Seq.map (fun change -> change.idToReplaceWith, (change.typeToInsertForId, change.refConstrsForId))
            |> Map.ofSeq }

    /// This intends to take a "newer" version of the Accumulator and returns a diff from the old Accumulator, i.e. the changes that would need to be applied to transform the old Acc to the new one
    let getAccDifference (newAcc : Accumulator) (oldAcc : Accumulator) : MultipleChanges =
        let redirectDiff =
            let oldKeys = Map.keys oldAcc.redirectMap |> Set.ofSeq

            newAcc.redirectMap
            |> Map.filter (fun key _ -> not (Set.contains key oldKeys))

        /// Newer Accs could have both more or less keys than the old one, depending on whether more things were added or if old entries were unified together. I think the only way to know which are meant to be there are to look at which ones are in the newer redirects and only include those. Or... actually just delete the ones from the new ones that are still present in the old one. I think that'll do it.
        let refConstraintsDiff =
            let oldKeys = Map.keys oldAcc.refConstraintsMap |> Set.ofSeq

            newAcc.refConstraintsMap
            |> Map.filter (fun key _ -> not (Set.contains key oldKeys))

        refConstraintsDiff
        |> Map.toSeq
        |> Seq.map (fun (accId, (resultOpt, refConstrs)) ->
            let idsToReplace =
                redirectDiff
                |> Map.toSeq
                |> Seq.choose (fun (oldId, newId) ->
                    if newId = accId then
                        Some oldId
                    else
                        None)

            { idsToReplace = idsToReplace
              idToReplaceWith = accId
              typeToInsertForId = resultOpt
              refConstrsForId = refConstrs })


    /// Take multiple sets of changes to make and return a single one.
    ///
    /// @TODO: I think this is dodgy tbh... because changes can't just be composed together on their own without being applied to an Accumulator to check if it results in unification cascades!
    let combineFromActms (aatms : MultipleAndAccId seq) : MultipleChanges = aatms |> Seq.collect getChanges

    /// Handy helper function to construct an AccChangeToMake
    let makeChange
        (idsToReplace : AccumulatorTypeId seq)
        (idToReplaceWith : AccumulatorTypeId)
        (typeToInsertForId : Result<RefDefType, AccTypeError> option)
        (refConstrsForId : RefConstr set)
        : AccChangeToMake =
        { idsToReplace = idsToReplace
          idToReplaceWith = idToReplaceWith
          typeToInsertForId = typeToInsertForId
          refConstrsForId = refConstrsForId }



    let makeChangesSingleton
        (idsToReplace : AccumulatorTypeId seq)
        (idToReplaceWith : AccumulatorTypeId)
        (typeToInsertForId : Result<RefDefType, AccTypeError> option)
        (refConstrsForId : RefConstr set)
        : MultipleAndAccId =
        { typeId = idToReplaceWith
          changes =
            makeChange idsToReplace idToReplaceWith typeToInsertForId refConstrsForId
            |> Seq.singleton }

    /// @TODO: Hm I think this is dodgy too, because you can't just add a type without checking if it results in unification cascades! (said in the tone of that scene from Mean Girls)
    let addTypeToChanges
        (accIds : AccumulatorTypeId seq)
        (newKey : AccumulatorTypeId)
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (changes : AccChangeToMake seq)
        : MultipleAndAccId =
        { typeId = newKey
          changes =
            [ makeChange accIds newKey refDefResOpt refConstrs ]
            |> Seq.append changes }


    let applyChanges (changes : MultipleChanges) (acc : Accumulator) : Accumulator =
        let getRootKey key =
            Accumulator.getRealIdAndType key acc |> fst

        let applySingleChange (change : AccChangeToMake) (acc : Accumulator) : Accumulator =
            let accIdsToReplace = change.idsToReplace |> Seq.map getRootKey
            let accIdToReplaceWith = change.idToReplaceWith

            { refConstraintsMap =
                Map.removeKeys accIdsToReplace acc.refConstraintsMap
                |> Map.add accIdToReplaceWith (change.typeToInsertForId, change.refConstrsForId)

              redirectMap =
                  acc.redirectMap
                  |> Map.addBulk (
                      accIdsToReplace
                      |> Seq.map (fun accId -> accId, accIdToReplaceWith)
                  ) }

        changes |> Seq.fold (flip applySingleChange) acc






module Accumulator =

    (*
        Helpers for the accumulator
    *)



    module Aati = AccAndTypeId
    module Actm = AccChangeToMake








    let private makeAccTypeId () : AccumulatorTypeId =
        System.Guid.NewGuid () |> AccumulatorTypeId


    let private hasOverlap setA setB =
        Set.intersect setA setB |> Set.isNotEmpty


    let empty = Accumulator.empty




    /// This returns the Accumulator resulting from unifying the two RefDefs at the given AccIds
    let rec unifyRefDefs (refDefsWithIds : (AccumulatorTypeId * RefDefType) tom) (acc : Accumulator) =
        /// Ok so what do we expect this thing to return? Well...
        /// - if there are refConstrsToUnify, that it will only have unified the RefDefs into a new entry (and set the old IDs to redirect to the new ones), but any RefConstrs that are implied to be unified from the RefDefs that have been unified, are merely returned to be unified by its specialised function. It will not unify RefConstrs itself.
        /// - if there are no refConstrsToUnify, that must mean that the only thing to do was unifying the RefDefs, and so that's all that needs to be done. Because it can unify its own RefDefs, even nested ones. And it knows how to integrate its own nested merged RefDefs itself. It's only RefConstrs that it defers to the calling function, to be done elsewhere. For a nice clean separation of concerns.
        ///     Although... maybe that last part is wrong actually. Maybe it should return both RefConstrs to merge *and* nested RefDefs to merge... So that this really only executes one level of operations. Which might make the logic cleaner to reason about... Because then the "single pass" functions truly only make one single pass of things, and then defer to their callers, which might be better than the single pass function trying to do nested things all on its own and accumulate a bunch of RefConstrs to merge from different levels.. AHA! Okay I think that may be why I ended up stuck and wrong the first few times maybe... because there are multiple levels of RefConstrs to merge.... but *not with each other*! Just with themselves! So... maybe it *is* right to only let these funcs only do one level of things...
        ///     But on the other hand, maybe the single pass functions should be executing a single pass merge only for their own type of things, but for the other thing call the other (non-single-pass) unifier function...? Hm. So maybe actually this does point towards each single pass function really only doing a single level pass merge. In which case it will need to return not only which of the *other* type of thing still need to be merged, but also which of its *own* type need to be merged in the next pass! But then... Ok that may all be fine... I think... as long as we don't get stuck in a problem of which one do we do first... Although tbh I think maybe the logic should be something like:
        ///     - unifyRefDefs -> gives us both refConstrs and the next refDefs to merge
        ///     - unifyRefConstrs -> gives us refDefs to merge and the next refConstrs also
        ///     - we call unifyRefDefs again, for each of the separate sets of refDefs to unify; taken from both the initial unifyRefDefs *and* the unifyRefConstrs
        ///     - Each of these unify operations could result in yet more things to unify, so we try to unify all of those too...
        ///     - But each time we do a unification we need to feed in the latest Accumulator, which incoroprates all the information we have gleaned so far
        ///     - Which means we need to be able to merge Accumulators simply, without exposing the "here's more stuff to unify" here... Otherwise it's just a complete infinite recursion of unifiers returning more unifiers, and nobody actually doing the work.
        ///     - Unless... idk, if each single-pass unifier/merging function does one bit of the work, reducing the unification work to do for the next function it passes it to? idk tbh. That's going to be very hard to figure out by just thinking about it without actually running some tests on it.
        ///     - Because what may end up happening is an infinite cascade of things to unify, with each unifier pass returning more and more things to unify, and so the amount of work to do grows far faster than it reduces... plus maybe this results in a On^n time complexity, since each tuple and record type could potentially have infinitely many members? But then tbh that would be appropriate for the amount of type information they have. But if they are not in fact infinitely deeply nested, then this all _should_ return in reasonable time I think?
        ///     - But what you do risk happening, is if the code we've parsed does have some infinite recursion in its type signature? E.g. something like... `f = f f` or something? Ok idk if that is a case that would actually give rise to the problem, but you could potentially have the case where a refConstr has to be equal to itself? Then maybe we end up with an infinite amount of merging work to do? Either way, I can imagine there being some pathological case where the amount of unification work to do grows and grows and grows, and never gets a chance to reduce down to something smaller. Not sure yet exactly what kind of case could give rise to that, but that's the thing I'm worried about and unsure if my proposed unification logic can handle.
        ///     - So... okay, maybe I just need to implement it and see?
        ///
        ///
        ///
        let firstPassResult = unifyRefDefsSinglePass refDefsWithIds acc

        match firstPassResult.refConstrsToUnify with
        | None -> firstPassResult.accAndTypeId
        | Some refConstrsToUnify -> unifyRefConstrs refConstrsToUnify firstPassResult.accAndTypeId.acc


    /// This returns the Accumulator resulting from unifying the two RefDefs at the given AccIds
    and unifyRefConstrs (refConstrsWithIds : (AccumulatorTypeId * RefConstr set) tom) (acc : Accumulator) =
        /// Ok so what do we expect this thing to return? Well...
        /// - if there are no refDefsToUnify, that merging
        let firstPassResult = unifyRefConstrsSinglePass refConstrsWithIds acc

        match firstPassResult.refDefsToUnify with
        | None -> firstPassResult.accAndTypeId
        | Some refDefsToUnify -> unifyRefDefs refDefsToUnify firstPassResult.accAndTypeId.acc







    and unifyRefDefsSinglePass
        (refDefsWithIds : (AccumulatorTypeId * RefDefType) tom)
        (acc : Accumulator)
        : {| refConstrsToUnify : (AccumulatorTypeId * RefConstr set) tom option
             accAndTypeId : AccAndTypeId |} =
        failwith "@TODO: implement"

    and unifyRefConstrsSinglePass
        (refConstrsWithIds : (AccumulatorTypeId * RefConstr set) tom)
        (acc : Accumulator)
        : {| refDefsToUnify : (AccumulatorTypeId * RefDefType) tom option
             accAndTypeId : AccAndTypeId |} =
        failwith "@TODO: implement"










    /// Merges two accumulators. No IDs should be lost, refDefs should be unified according to reference constraint overlaps. And resulting combined IDs should be unified also.
    ///
    /// There should be no entities from one Acc referencing IDs in the other.
    let rec combine (acc1 : Accumulator) (acc2 : Accumulator) : Accumulator =
        // I think do a naive merge of the maps first, and then hunt down for duplicates I think... don't think there's really any other way of doing that without running into the issue of new RefDefs containing references from the old map and not the new one.
        // Unless... we only add the entries in from the old map on an as-needed basis? (in addition to adding them one by one to make sure we've covered them all, even the ones that weren't referenced by other types added previously)

        // We need to do a naive merge first because otherwise the things we're unifying are going to be referencing AccIds that haven't been added to this map yet, which will therefore not be able to be unified because they will not be found. So we just mash everything together naively first, and *then* we unify those entries that we've worked out need to be unified because of their RefConstr overlap.
        let naivelyMergedAcc : Accumulator =
            { refConstraintsMap = Map.merge acc1.refConstraintsMap acc2.refConstraintsMap
              redirectMap = Map.merge acc1.redirectMap acc2.redirectMap }

        let entriesToAdd : RefConstr set list =
            acc1.refConstraintsMap
            |> Map.toList
            |> List.map (fun (_, (_, refConstrs)) -> refConstrs)

        entriesToAdd
        |> List.fold
            (fun state refConstrs ->
                addRefConstraintsChanges refConstrs state
                |> Aati.getAcc)
            naivelyMergedAcc



    and combineMany (accs : Accumulator seq) : Accumulator = Seq.fold combine Accumulator.empty accs

    /// Combine Accumulators from a seq of `AccAndTypeId`s
    and combineAccsFromAatis (aatis : AccAndTypeId seq) =
        Seq.map Aati.getAcc aatis |> combineMany




    /// Unifies all the entries in Acc based on the new information about the given RefConstrs all having to have the exact same type
    and addRefConstraintsChanges (refConstrs : RefConstr set) (acc : Accumulator) : Actm.MultipleAndAccId =
        let runSingleRefConstrSetThroughAcc
            (accIdsAndRefConstrs : Map<AccumulatorTypeId, RefConstr set>)
            (newRefConstrs : RefConstr set)
            : AccumulatorTypeId set * RefConstr set =
            let startingState = Set.empty, newRefConstrs

            accIdsAndRefConstrs
            |> Map.fold
                (fun (snowballedAccIds, snowballedRefConstrs) accId refConstrs ->
                    if hasOverlap refConstrs snowballedRefConstrs then
                        Set.add accId snowballedAccIds, Set.union refConstrs snowballedRefConstrs

                    else
                        snowballedAccIds, snowballedRefConstrs)
                startingState


        let newKey = makeAccTypeId ()

        let accWithNewRefConstrsAdded =
            { acc with
                refConstraintsMap =
                    acc.refConstraintsMap
                    |> Map.add newKey (None, refConstrs) }

        let accIdsAndRefConstrs : Map<AccumulatorTypeId, RefConstr set> =
            accWithNewRefConstrsAdded.refConstraintsMap
            |> Map.map (fun _ (_, refConstrs) -> refConstrs)

        let accIdsToUnify, _ =
            runSingleRefConstrSetThroughAcc accIdsAndRefConstrs refConstrs


        // Note: This should be the thing that creates the new AccIds for the merged entries and sticks the old ones in the redirectMap so that we don't have to do it separately in this function
        unifyManyTypeConstraintIds accIdsToUnify accWithNewRefConstrsAdded



    /// This adds a single extra RefDef constraint onto an existing entry in the Acc
    and addRefDefConstraintForAccId
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (accId : AccumulatorTypeId)
        (acc : Accumulator)
        : Actm.MultipleAndAccId =
        let newKey = makeAccTypeId ()

        /// It's not the most efficient way to do it to add a whole new AccId just so we have something to point `unifyTypeConstraintIds` to, but it works and if we really care we can make it more efficient later
        let accWithRefDefAdded =
            { acc with
                refConstraintsMap =
                    acc.refConstraintsMap
                    |> Map.add newKey (refDefResOpt, Set.empty) }

        accWithRefDefAdded
        |> unifyTypeConstraintIdsChanges newKey accId




    /// Adds a new RefDef and its reference constraints into the map (including RefConstr overlap unification)
    and addRefDefResOptWithRefConstrsChanges
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : Actm.MultipleAndAccId =
        let withRefConstrsAdded = addRefConstraintsChanges refConstrs acc
        let withRefConstrAppliedChanges = Actm.applyChanges withRefConstrsAdded.changes acc

        let withRefDefAdded =
            addRefDefConstraintForAccId refDefResOpt withRefConstrsAdded.typeId withRefConstrAppliedChanges

        let withRefDefAppliedChanges =
            Actm.applyChanges withRefDefAdded.changes withRefConstrAppliedChanges

        let onlyChanges = Actm.getAccDifference withRefDefAppliedChanges acc

        { typeId = withRefDefAdded.typeId
          changes = onlyChanges }






    /// This is the function that actually traverses AccumulatorTypeIds to check if types are actually compatible with one another!
    and unifyRefDefs
        (accIdA : AccumulatorTypeId)
        (refDefA : RefDefType)
        (accIdB : AccumulatorTypeId)
        (refDefB : RefDefType)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : Actm.MultipleAndAccId =
        let newKey = makeAccTypeId ()
        let accIds = Set.ofList [ accIdA; accIdB ]

        /// From a RefDefType
        let makeOkType : RefDefType -> Result<RefDefType, AccTypeError> option = Ok >> Some
        let makeErrType a b : Result<RefDefType, AccTypeError> option = DefTypeClash (a, b) |> Error |> Some

        /// With the combined two AccIds, an empty set of RefConstrs, and the new key created above
        let makeChangesSingleton_ refDefResOpt =
            Actm.makeChangesSingleton accIds newKey refDefResOpt refConstrs


        let addTypeToChanges refDefResOpt changes : Actm.MultipleAndAccId =
            { typeId = newKey
              changes =
                [ Actm.makeChange accIds newKey refDefResOpt refConstrs ]
                |> Seq.append changes }


        /// Returns an error with the lists so far if lists don't have the same length; which will be a list of n pairs, where n is the length of the shorter of the two input lists
        let zipList a b : Result<('a * 'b) list, ('a * 'b) list> =
            let rec zipList_ combinedSoFar a b =
                match a, b with
                | [], [] -> Ok (List.rev combinedSoFar)
                | headA :: tailA, headB :: tailB -> zipList_ ((headA, headB) :: combinedSoFar) tailA tailB
                | [], _ :: _
                | _ :: _, [] -> Error (List.rev combinedSoFar)

            zipList_ List.empty a b



        match refDefA, refDefB with
        | RefDtUnitType, RefDtUnitType ->
            //replaceEntriesInAcc (makeOkType RefDtUnitType) acc
            //|> Aati.make newKey
            makeChangesSingleton_ (makeOkType RefDtUnitType)


        | RefDtPrimitiveType primA, RefDtPrimitiveType primB ->
            let typeResult =
                if primA = primB then
                    makeOkType (RefDtPrimitiveType primA)
                else
                    makeErrType refDefA refDefB

            makeChangesSingleton_ typeResult


        | RefDtTuple (TOM (headA, neckA, tailA)), RefDtTuple (TOM (headB, neckB, tailB)) ->
            /// This ensures the two lists of AccIds have the same length, it doesn't try to unify them yet
            let combinedListResult = zipList tailA tailB

            match combinedListResult with
            | Ok combinedList ->
                let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedList

                let tomResults =
                    combinedTom
                    // I think this could be improved by using a TOM.mapFold (or TOM.mapFoldBack); that way we could feed in the already updated Acc for each iteration instead of having to make each thing use the original acc and then combine them all later
                    |> TOM.map (fun (idA, idB) -> unifyTypeConstraintIdsChanges idA idB acc)

                let tupleType =
                    tomResults
                    |> TOM.map Actm.getIdFromMultiple
                    |> RefDtTuple

                let combinedAccs = Actm.combineFromActms tomResults

                addTypeToChanges (makeOkType tupleType) combinedAccs


            | Error combinedListSoFar ->
                let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedListSoFar

                let tomResults =
                    combinedTom
                    |> TOM.map (fun (idA, idB) -> unifyTypeConstraintIdsChanges idA idB acc)

                let combinedAccs = Actm.combineFromActms tomResults

                addTypeToChanges (makeErrType refDefA refDefB) combinedAccs


        | RefDtList paramA, RefDtList paramB ->
            let unifiedResult = unifyTypeConstraintIdsChanges paramA paramB acc

            let listType = RefDtList unifiedResult.typeId

            addTypeToChanges (makeOkType listType) unifiedResult.changes


        | RefDtRecordExact mapA, RefDtRecordExact mapB ->
            let mergeResults =
                // @TODO: Actually ideally we should get the results of unifying the constraints and then separately get whether it's a non-exact merge or not, so that we don't lose the type information from the values of the two different maps
                Map.mergeExact (fun _ valA valB -> unifyTypeConstraintIdsChanges valA valB acc) mapA mapB

            match mergeResults with
            | Ok mergedMap ->
                let combinedAcc = Map.values mergedMap |> Actm.combineFromActms

                let mapType =
                    mergedMap
                    |> Map.map (fun _ -> Actm.getIdFromMultiple)
                    |> RefDtRecordExact

                addTypeToChanges (makeOkType mapType) combinedAcc

            | Error _ -> addTypeToChanges (makeErrType refDefA refDefB) Seq.empty


        | RefDtRecordWith mapA, RefDtRecordWith mapB ->
            // @TODO: actually the logic here should be very different to that of exact maps!
            // @TODO: and actually there should also be compatible cases where one is exact and one is "with"!


            let mergeResults =
                // @TODO: Actually ideally we should get the results of unifying the constraints and then separately get whether it's a non-exact merge or not, so that we don't lose the type information from the values of the two different maps
                Map.mergeExact (fun _ valA valB -> unifyTypeConstraintIdsChanges valA valB acc) mapA mapB

            match mergeResults with
            | Ok mergedMap ->
                let combinedAcc = Map.values mergedMap |> Actm.combineFromActms

                let mapType =
                    mergedMap
                    |> Map.map (fun _ -> Actm.getIdFromMultiple)
                    |> RefDtRecordWith

                addTypeToChanges (makeOkType mapType) combinedAcc

            | Error _ -> addTypeToChanges (makeErrType refDefA refDefB) Seq.empty




        | RefDtNewType (nameA, typeParamsA), RefDtNewType (nameB, typeParamsB) ->
            if nameA = nameB then
                let zippedLists = zipList typeParamsA typeParamsB

                match zippedLists with
                | Ok combinedList ->
                    let resultsList =
                        combinedList
                        |> List.map (fun (idA, idB) -> unifyTypeConstraintIdsChanges idA idB acc)

                    let typeConstraintIdList = resultsList |> List.map Actm.getIdFromMultiple
                    let newType = RefDtNewType (nameA, typeConstraintIdList)

                    let combinedAccs = Actm.combineFromActms resultsList

                    addTypeToChanges (makeOkType newType) combinedAccs

            else
                addTypeToChanges (makeErrType refDefA refDefB) Seq.empty


        | RefDtArrow (fromTypeA, toTypeA), RefDtArrow (fromTypeB, toTypeB) ->
            let unifiedFroms = unifyTypeConstraintIdsChanges fromTypeA fromTypeB acc
            let unifiedTos = unifyTypeConstraintIdsChanges toTypeA toTypeB acc

            let arrowType = RefDtArrow (unifiedFroms.typeId, unifiedTos.typeId)

            let combinedAccs =
                Actm.combineFromActms [ unifiedFroms
                                        unifiedTos ]

            addTypeToChanges (makeOkType arrowType) combinedAccs


        | _, _ ->
            // @TODO: Fill in the case where the types are not compatible
            addTypeToChanges (makeErrType refDefA refDefB) Seq.empty



    /// Lil helper function that essentially just does the same as above, but handles the non-success cases also
    and unifyRefDefResOpts
        (accIdA : AccumulatorTypeId)
        (refDefResOptA : Result<RefDefType, AccTypeError> option)
        (accIdB : AccumulatorTypeId)
        (refDefResOptB : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : Actm.MultipleAndAccId =
        let newKey = makeAccTypeId ()
        let accIdsToReplace = Set.ofList [ accIdA; accIdB ]

        match refDefResOptA, refDefResOptB with
        | None, None -> Actm.addTypeToChanges accIdsToReplace newKey None refConstrs Seq.empty

        | Some x, None
        | None, Some x -> Actm.addTypeToChanges accIdsToReplace newKey (Some x) refConstrs Seq.empty

        | Some refDefResA, Some refDefResB ->
            match refDefResA, refDefResB with
            | Ok _, Error e
            | Error e, Ok _
            | Error e, Error _ -> Actm.addTypeToChanges accIdsToReplace newKey (Some (Error e)) refConstrs Seq.empty

            | Ok refDefA, Ok refDefB -> unifyRefDefs accIdA refDefA accIdB refDefB refConstrs acc



    and unifyTypeConstraintIdsChanges
        (idA : AccumulatorTypeId)
        (idB : AccumulatorTypeId)
        (acc : Accumulator)
        : Actm.MultipleAndAccId =
        let itemA, refConstrsA = Accumulator.getTypeById idA acc
        let itemB, refConstrsB = Accumulator.getTypeById idB acc

        unifyRefDefResOpts idA itemA idB itemB (Set.union refConstrsA refConstrsB) acc



    /// @TODO: maybe do this using the more fundamental unifyTypeConstraintIds? idk tho
    and unifyManyTypeConstraintIds (ids : AccumulatorTypeId seq) (acc : Accumulator) : Actm.MultipleAndAccId =
        match Seq.toList ids with
        | [] ->
            let newKey = makeAccTypeId ()
            Actm.makeChangesSingleton Seq.empty newKey None Set.empty

        | single :: [] -> Actm.makeChangesSingleton Seq.empty single None Set.empty
        | head :: neck :: tail ->
            let firstMerged = unifyTypeConstraintIdsChanges head neck acc

            tail
            |> List.fold
                (fun state accId ->
                    let result = unifyTypeConstraintIdsChanges accId state.typeId acc
                    { result with changes = Seq.append state.changes result.changes })
                firstMerged


    //tail
    //|> List.fold
    //    (fun state accId ->
    //        let result = unifyTypeConstraintIds accId state.typeId state.acc
    //        let merged = Actm.applyChanges result.changes state.acc
    //        Aati.make result.typeId merged)
    //    (Aati.make firstMerged.typeId appliedToAcc)


    let addRefDefResOptWithRefConstrs
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        =
        let changes = addRefDefResOptWithRefConstrsChanges refDefResOpt refConstrs acc

        Actm.applyChanges changes.changes acc
        |> Aati.make changes.typeId


    let unifyTypeConstraintIds (idA : AccumulatorTypeId) (idB : AccumulatorTypeId) (acc : Accumulator) =
        let changes = unifyTypeConstraintIdsChanges idA idB acc

        Actm.applyChanges changes.changes acc
        |> Aati.make changes.typeId


    let addRefConstraints (refConstrs : RefConstr set) (acc : Accumulator) =
        let changes = addRefConstraintsChanges refConstrs acc

        Actm.applyChanges changes.changes acc
        |> Aati.make changes.typeId


    /// Adds a new RefDef (without any accompanying reference constraints) into the map
    let addRefDefResOpt (refDefResOpt : Result<RefDefType, AccTypeError> option) (acc : Accumulator) : AccAndTypeId =
        let changes = addRefDefResOptWithRefConstrsChanges refDefResOpt Set.empty acc

        Actm.applyChanges changes.changes acc
        |> Aati.make changes.typeId








    /// Convert a DefinitiveType to an Acc2 and get its root AccTypeId. This Acc2 can then be merged with others.
    let rec convertDefinitiveType (def : DefinitiveType) : AccAndTypeId =
        let newKey = makeAccTypeId ()

        /// From a RefDefType
        let makeOkType : RefDefType -> Result<RefDefType, AccTypeError> option = Ok >> Some
        let makeErrType a b : Result<RefDefType, AccTypeError> option = DefTypeClash (a, b) |> Error |> Some

        let makeSingletonAcc (refDefResOpt : Result<RefDefType, AccTypeError> option) : Accumulator =
            { Accumulator.empty with refConstraintsMap = Map.ofList [ newKey, (refDefResOpt, Set.empty) ] }

        //let addToAcc (refDefResOpt : Result<RefDefType, AccTypeError> option) (acc:Accumulator2) : Accumulator2 =


        match def with
        | DtUnitType ->
            makeSingletonAcc (makeOkType RefDtUnitType)
            |> Aati.make newKey

        | DtPrimitiveType prim ->
            makeSingletonAcc (makeOkType (RefDtPrimitiveType prim))
            |> Aati.make newKey

        | DtList tc ->
            let resultOfGeneric = convertTypeConstraints tc
            let listType = RefDtList resultOfGeneric.typeId

            addRefDefResOptWithRefConstrs (makeOkType listType) Set.empty resultOfGeneric.acc


        | DtTuple tom ->
            let resultsTom = TOM.map convertTypeConstraints tom

            let combinedAccs =
                resultsTom
                |> TOM.map Aati.getAcc
                |> TOM.fold combine Accumulator.empty

            let tupleType = RefDtTuple (TOM.map Aati.getId resultsTom)

            addRefDefResOptWithRefConstrs (makeOkType tupleType) Set.empty combinedAccs

        | DtArrow (fromType, toType) ->
            let fromResult = convertTypeConstraints fromType
            let toResult = convertTypeConstraints toType

            let fromAndToAcc = combine fromResult.acc toResult.acc

            let arrowType = RefDtArrow (fromResult.typeId, toResult.typeId)

            addRefDefResOptWithRefConstrs (makeOkType arrowType) Set.empty fromAndToAcc

        | DtRecordExact map ->
            let resultsMap = Map.map (fun _ tc -> convertTypeConstraints tc) map

            let mapType = RefDtRecordExact (resultsMap |> Map.map (fun _ -> Aati.getId))

            let combinedAcc =
                resultsMap
                |> Map.fold (fun state _ thisAati -> combine thisAati.acc state) Accumulator.empty

            addRefDefResOptWithRefConstrs (makeOkType mapType) Set.empty combinedAcc

        | DtRecordWith map ->
            let resultsMap = Map.map (fun _ tc -> convertTypeConstraints tc) map

            let mapType = RefDtRecordWith (resultsMap |> Map.map (fun _ -> Aati.getId))

            let combinedAcc =
                resultsMap
                |> Map.fold (fun state _ thisAati -> combine thisAati.acc state) Accumulator.empty

            addRefDefResOptWithRefConstrs (makeOkType mapType) Set.empty combinedAcc

        | DtNewType (typeName, constraints) ->
            let resultsList = List.map convertTypeConstraints constraints

            let combinedAccs = resultsList |> List.map Aati.getAcc |> combineMany

            let newType = RefDtNewType (typeName, List.map Aati.getId resultsList)

            addRefDefResOptWithRefConstrs (makeOkType newType) Set.empty combinedAccs




    and convertTypeConstraints (tc : TypeConstraints) : AccAndTypeId =
        let (Constrained (defOpt, refConstrs)) = tc

        let withRefConstrsAdded = addRefConstraints refConstrs Accumulator.empty

        match defOpt with
        | None -> withRefConstrsAdded
        | Some def ->
            let defTypeAcc = convertDefinitiveType def
            let combinedAcc = combine withRefConstrsAdded.acc defTypeAcc.acc

            unifyTypeConstraintIds defTypeAcc.typeId withRefConstrsAdded.typeId combinedAcc


    and convertTypeJudgment (judgment : TypeJudgment) : AccAndTypeId =
        let newKey = makeAccTypeId ()

        match judgment with
        | Ok tc -> convertTypeConstraints tc
        | Error e ->
            { Accumulator.empty with
                refConstraintsMap =
                    Map.empty
                    |> Map.add newKey (Some (Error e), Set.empty) }
            |> Aati.make newKey











    (*
        Conversions to and from TypeConstraints
    *)


    let rec convertRefDefToTypeConstraints
        (refDef : RefDefType)
        (refConstrsToAdd : RefConstr set)
        (acc : Accumulator)
        : Result<TypeConstraints, AccTypeError> =
        let fromDef def =
            TypeConstraints.Constrained (Some def, refConstrsToAdd)
            |> Ok

        /// Just a little helper where foundType is the last param, for easier use in `Result.bind`s
        let convertType refConstrs foundType =
            convertRefDefToTypeConstraints foundType refConstrs acc

        match refDef with
        | RefDtUnitType -> fromDef DtUnitType
        | RefDtPrimitiveType prim -> DtPrimitiveType prim |> fromDef
        | RefDtList constrId ->
            let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

            match foundTypeResultOpt with
            | Some foundTypeResult ->
                foundTypeResult
                |> Result.bind (convertType refConstrs)
                |> Result.map (DtList >> TypeConstraints.fromDefinitive)

            | None -> Constrained (None, refConstrs) |> Ok

        | RefDtTuple constrTom ->
            let resultsTom =
                constrTom
                |> TOM.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (convertType refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> TOM.sequenceResult

            match resultsTom with
            | Ok typeConstraints -> DtTuple typeConstraints |> fromDef

            | Error e -> Error (NEL.head e)


        | RefDtNewType (typeName, typeParams) ->
            let resultsTom =
                typeParams
                |> List.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (convertType refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Result.sequenceList

            match resultsTom with
            | Ok typeConstraints -> DtNewType (typeName, typeConstraints) |> fromDef

            | Error e -> Error (NEL.head e)


        | RefDtArrow (fromId, toId) ->
            let resultsPair =
                (fromId, toId)
                |> Tuple.map (fun constrId ->
                    let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (convertType refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Tuple.sequenceResult

            resultsPair
            |> Result.map (DtArrow >> TypeConstraints.fromDefinitive)



        | RefDtRecordExact fields ->
            let resultsMap =
                fields
                |> Map.map (fun _ constrId ->
                    let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (convertType refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Map.sequenceResult

            match resultsMap with
            | Ok typeConstraintsMap -> DtRecordExact typeConstraintsMap |> fromDef
            | Error (_, errsNel) -> Error (NEL.head errsNel)


        | RefDtRecordWith fields ->
            let resultsMap =
                fields
                |> Map.map (fun _ constrId ->
                    let foundTypeResultOpt, refConstrs = Accumulator.getTypeById constrId acc

                    match foundTypeResultOpt with
                    | Some foundTypeResult ->
                        foundTypeResult
                        |> Result.bind (convertType refConstrs)
                    | None -> Constrained (None, refConstrs) |> Ok)
                |> Map.sequenceResult

            match resultsMap with
            | Ok typeConstraintsMap -> DtRecordWith typeConstraintsMap |> fromDef
            | Error (_, errsNel) -> Error (NEL.head errsNel)




    let convertAccIdToTypeConstraints (accId : AccumulatorTypeId) (acc : Accumulator) : TypeJudgment =
        let foundType, refConstrs = Accumulator.getTypeById accId acc

        match foundType with
        | Some typeResult ->
            match typeResult with
            | Ok refDef -> convertRefDefToTypeConstraints refDef refConstrs acc
            | Error e -> Error e
        | None -> Constrained (None, refConstrs) |> Ok





    let addTypeConstraintsToAcc (typeConstraints : TypeConstraints) (acc : Accumulator) : AccAndTypeId =
        let result = convertTypeConstraints typeConstraints
        Aati.make result.typeId (combine result.acc acc)


    let addTypeConstraintForName (name : RefConstr) (tc : TypeConstraints) (acc : Accumulator) : AccAndTypeId =
        let (Constrained (defOpt, refs)) = tc
        let tcWithName = Constrained (defOpt, Set.add name refs)

        addTypeConstraintsToAcc tcWithName acc







type RefConstrToTypeConstraintsMap =
    | RefConstrToTypeConstraintsMap of Map<RefConstr, Result<TypeConstraints, AccTypeError> option>



module RefConstrToTypeConstraintsMap =

    /// Makes a new map from an Accumulator2
    let fromAcc2 (acc : Accumulator) : RefConstrToTypeConstraintsMap =
        Map.values acc.refConstraintsMap
        |> Seq.map (fun (refDefResOpt, refConstrs) ->
            refConstrs,
            refDefResOpt
            |> Option.map (Result.bind (fun refDef -> Accumulator.convertRefDefToTypeConstraints refDef refConstrs acc)))
        |> Seq.collect (fun (refConstrs, refDefResOpt) ->
            Set.toList refConstrs
            |> List.map (fun refConstr -> refConstr, refDefResOpt))
        |> Map.ofSeq
        |> RefConstrToTypeConstraintsMap


    /// Given a reference, get the TypeConstraints that that reference has been inferred to be
    let getTypeConstraintsFromMap
        (refConstr : RefConstr)
        (RefConstrToTypeConstraintsMap map : RefConstrToTypeConstraintsMap)
        : Result<TypeConstraints, AccTypeError> option =
        Map.tryFind refConstr map |> Option.flatten













module Acc = Accumulator
module Aati = AccAndTypeId
module Actm = AccChangeToMake
module TC = TypeConstraints










/// Pass in the IDs for the params and return type and this will return an Acc and AccId for the overall arrow type
let rec makeAccIdDestType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =
    match rest with
    | [] -> Aati.make first acc
    | head :: tail ->
        let tailResult = makeAccIdDestType (NEL.new_ head tail) acc
        let refDefType = RefDtArrow (first, tailResult.typeId)

        Accumulator.addRefDefResOpt (Ok refDefType |> Some) tailResult.acc




/// Pass in the IDs for the params passed to a function and return the arrow type the function expression must be inferred to be
let rec makeAccIdFuncApplicationType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =

    let makeArrowType (aati : AccAndTypeId) =
        let refDefType = RefDtArrow (first, aati.typeId)
        Accumulator.addRefDefResOpt (Some (Ok refDefType)) aati.acc

    match rest with
    | [] ->
        let unspecific = Accumulator.addRefDefResOpt None acc
        makeArrowType unspecific

    | head :: tail ->
        let tailResult = makeAccIdFuncApplicationType (NEL.new_ head tail) acc
        makeArrowType tailResult




let rec makeDottedSeqImpliedType (fields : RecordFieldName nel) acc =
    let (NEL (first, rest)) = fields

    let makeDotRecord fieldName aati =
        let refDefType = RefDtRecordWith ([ fieldName, aati.typeId ] |> Map.ofSeq)
        Accumulator.addRefDefResOpt (Some (Ok refDefType)) aati.acc

    match rest with
    | [] ->
        let unspecific = Accumulator.addRefDefResOpt None acc
        makeDotRecord first unspecific

    | head :: tail ->
        let tailResult = makeDottedSeqImpliedType (NEL.new_ head tail) acc
        makeDotRecord first tailResult









/// @TODO: I think it's finally time to tackle this now!!
let rec getAccumulatorFromSingleOrCompExpr (expr : SingleOrCompoundExpr) : AccAndTypeId =

    let makeOkType = Ok >> Some


    match expr with
    | T.SingleValueExpression singleVal ->
        match singleVal with
        | T.ExplicitValue explicit ->
            match explicit with
            | T.Primitive primitive ->
                let refDefType = refDeftypeOfPrimitiveLiteral primitive
                Accumulator.addRefDefResOpt (makeOkType refDefType) Accumulator.empty


            | T.DotGetter dotGetter ->
                let fields = Map.ofList [ dotGetter, TC.any () ]
                let defType = DtArrow (DtRecordWith fields |> TC.fromDef, TC.any ())

                Accumulator.convertDefinitiveType defType


            | T.Compound compound ->
                match compound with
                | T.CompoundValues.List list ->
                    let typedList = List.map getAccumulatorFromExpr list

                    let combinedAcc = typedList |> Accumulator.combineAccsFromAatis

                    let combinedAati =
                        Accumulator.unifyManyTypeConstraintIds (List.map Aati.getId typedList) combinedAcc

                    let refDefType = RefDtList combinedAati.typeId
                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAati.acc



                | T.CompoundValues.Tuple tuple ->
                    let typedTom = TOM.map getAccumulatorFromExpr tuple

                    let combinedAcc = typedTom |> Accumulator.combineAccsFromAatis

                    let refDefType = RefDtTuple (TOM.map Aati.getId typedTom)
                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAcc


                | T.CompoundValues.Record record ->
                    let typedKeyVals =
                        record
                        |> List.map (fun (key, value) -> key, getAccumulatorFromExpr value)

                    let combinedAcc =
                        typedKeyVals
                        |> List.map (snd >> Aati.getAcc)
                        |> Accumulator.combineMany

                    let refDefType =
                        typedKeyVals
                        |> List.map (fun (key, aati) -> key, aati.typeId)
                        |> Map.ofList
                        |> RefDtRecordExact

                    Accumulator.addRefDefResOpt (makeOkType refDefType) combinedAcc


                | T.CompoundValues.RecordExtension (extended, additions) ->
                    let typedKeyVals =
                        additions
                        |> NEL.map (fun (key, value) -> key, getAccumulatorFromExpr value)

                    let combinedAcc =
                        typedKeyVals
                        |> NEL.map (snd >> Aati.getAcc)
                        |> Accumulator.combineMany

                    let refDefType =
                        typedKeyVals
                        |> NEL.map (fun (key, aati) -> key, aati.typeId)
                        |> Map.ofSeq
                        // I think this needs to be exact because extending a record results in a record with exactly the same type as the record it's extending
                        |> RefDtRecordExact


                    Accumulator.addRefDefResOptWithRefConstrs
                        (makeOkType refDefType)
                        (LocalLower extended |> ByValue |> Set.singleton)
                        combinedAcc




            | T.Function funcVal ->
                let typeOfBody : AccAndTypeId = getAccumulatorFromExpr funcVal.body

                let funcParamsAccumulatorsAndSelfTypes =
                    NEL.map (getParamFromPattern >> getAccumulatorFromParam) funcVal.params_

                let funcParamsAccumulators =
                    funcParamsAccumulatorsAndSelfTypes
                    |> NEL.map AccAndTypeId.getAcc


                let funcParamTypes =
                    funcParamsAccumulatorsAndSelfTypes
                    |> NEL.map AccAndTypeId.getId

                /// Acc that combines the gleaned information about params from their shape and also from the body of the function
                let combinedAcc =
                    funcParamsAccumulators
                    |> Seq.fold Accumulator.combine typeOfBody.acc


                let paramsAndReturnTypeNel = NEL.appendList funcParamTypes [ typeOfBody.typeId ]
                let funcAati = makeAccIdDestType paramsAndReturnTypeNel combinedAcc

                /// This contains all the names defined from each param
                let combinedNamesDefinedHere =
                    funcParamsAccumulators
                    |> NEL.map getLocalValueNames
                    |> NEL.fold Set.union Set.empty

                let guidMap = makeGuidMapForNames combinedNamesDefinedHere

                replaceNameRefsWithBoundVars guidMap funcAati.acc
                |> Aati.make funcAati.typeId



        | T.UpperIdentifier name ->
            Accumulator.addRefConstraints (Set.singleton (ByConstructorType name)) Accumulator.empty


        | T.LowerIdentifier name -> Accumulator.addRefConstraints (Set.singleton (ByValue name)) Accumulator.empty





        | T.LetExpression (declarations, expr) ->
            let bodyExpr = getAccumulatorFromExpr expr

            let typedDeclarations =
                declarations
                |> NEL.map (fun binding ->
                    let bindingAccAndSelf = getAccumulatorFromBinding binding
                    let assignedExprAccAndSelf = getAccumulatorFromExpr binding.assignedExpression

                    let combinedAcc =
                        Actm.applyChanges
                            (Actm.getAccDifference bindingAccAndSelf.acc Acc.empty)
                            assignedExprAccAndSelf.acc

                    let combinedChanges =
                        Accumulator.unifyTypeConstraintIdsChanges
                            bindingAccAndSelf.typeId
                            assignedExprAccAndSelf.typeId
                            combinedAcc

                    Actm.applyChanges combinedChanges.changes Acc.empty)


            let combinedAcc = Accumulator.combineMany typedDeclarations

            /// This  contains all the names defined from each param
            let combinedNamesDefinedHere = getLocalValueNames combinedAcc
            let guidMap = makeGuidMapForNames combinedNamesDefinedHere

            replaceNameRefsWithBoundVars guidMap combinedAcc
            |> Aati.make bodyExpr.typeId



        | T.ControlFlowExpression controlFlow ->
            match controlFlow with
            | T.IfExpression (cond, ifTrue, ifFalse) ->
                let condAccAndOwn = getAccumulatorFromExpr cond

                let boolRefDef = RefDtPrimitiveType BuiltInPrimitiveTypes.Bool

                let withBoolConstrAdded =
                    Accumulator.addRefDefConstraintForAccId
                        (makeOkType boolRefDef)
                        condAccAndOwn.typeId
                        condAccAndOwn.acc
                    |> fun changes -> Aati.make changes.typeId (Actm.applyChanges changes.changes Acc.empty)

                let ifTrueAccAndOwn = getAccumulatorFromExpr ifTrue
                let ifFalseAccAndOwn = getAccumulatorFromExpr ifFalse

                let combinedAcc =
                    Accumulator.combineMany [ withBoolConstrAdded.acc
                                              ifTrueAccAndOwn.acc
                                              ifFalseAccAndOwn.acc ]

                let changes =
                    Accumulator.unifyTypeConstraintIdsChanges ifTrueAccAndOwn.typeId ifFalseAccAndOwn.typeId combinedAcc

                Actm.applyChanges changes.changes combinedAcc
                |> Aati.make changes.typeId




            | T.CaseMatch (exprToMatch, branches) ->
                let matchExprAccAndSelf = getAccumulatorFromExpr exprToMatch

                let accsAndSelvesOfPatterns =
                    branches
                    |> NEL.map (fun branch ->
                        let matchPatternAccAndSelf =
                            getAccumulatorFromParam (getParamFromPattern branch.matchPattern)

                        let combinedNamesDefinedHere = getLocalValueNames matchPatternAccAndSelf.acc
                        let guidMap = makeGuidMapForNames combinedNamesDefinedHere

                        let branchBodyExpr = getAccumulatorFromExpr branch.body

                        {| patternAccAndId =
                            replaceNameRefsWithBoundVars guidMap matchPatternAccAndSelf.acc
                            |> Aati.make matchPatternAccAndSelf.typeId
                           bodyAccAndId =
                            replaceNameRefsWithBoundVars guidMap branchBodyExpr.acc
                            |> Aati.make branchBodyExpr.typeId |})


                let combinedAcc =
                    accsAndSelvesOfPatterns
                    |> NEL.map (fun pattern -> Accumulator.combine pattern.patternAccAndId.acc pattern.bodyAccAndId.acc)
                    |> Accumulator.combineMany
                    |> Accumulator.combine matchExprAccAndSelf.acc

                let withMatchExprAndPatternsCombined =
                    combinedAcc
                    |> Accumulator.unifyManyTypeConstraintIds (
                        accsAndSelvesOfPatterns
                        |> NEL.map (fun pattern -> pattern.patternAccAndId.typeId)
                        |> Set.ofSeq
                        |> Set.add matchExprAccAndSelf.typeId
                    )

                let withReturnTypesCombined =
                    withMatchExprAndPatternsCombined.acc
                    |> Accumulator.unifyManyTypeConstraintIds (
                        accsAndSelvesOfPatterns
                        |> NEL.map (fun pattern -> pattern.bodyAccAndId.typeId)
                        |> Set.ofSeq
                    )

                withReturnTypesCombined




    | T.CompoundExpression compExpr ->
        match compExpr with
        | T.FunctionApplication (funcExpr, params_) ->
            let paramsAccAndSelves = params_ |> NEL.map getAccumulatorFromExpr

            let paramsAcc =
                paramsAccAndSelves
                |> Accumulator.combineAccsFromAatis

            /// The Acc based on the parameters and the type that the function must be compatible with based on the parameters that have been applied to the function
            let requiredFuncAccAndId =
                makeAccIdFuncApplicationType (NEL.map Aati.getId paramsAccAndSelves) paramsAcc

            let funcExprAccAndSelf = getAccumulatorFromExpr funcExpr

            let combinedAcc =
                Accumulator.combine requiredFuncAccAndId.acc funcExprAccAndSelf.acc

            combinedAcc
            |> Accumulator.unifyTypeConstraintIdsChanges funcExprAccAndSelf.typeId requiredFuncAccAndId.typeId


        | T.DotAccess (dottedExpr, dotSequence) ->
            let exprAccAndSelf = getAccumulatorFromExpr dottedExpr

            let withImpliedRecordType = makeDottedSeqImpliedType dotSequence exprAccAndSelf.acc

            Accumulator.unifyTypeConstraintIdsChanges
                exprAccAndSelf.typeId
                withImpliedRecordType.typeId
                withImpliedRecordType.acc


        | T.Operator (left, op, right) ->
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"



and getAccumulatorFromExpr (expr : TypedExpr) : AccAndTypeId =
    getAccumulatorFromSingleOrCompExpr expr.expr


//and getAccumulatorFromParam (param : FunctionOrCaseMatchParam) : AccumulatorAndOwnType =
and getAccumulatorFromParam (param : AssignmentPattern) : AccAndTypeId =
    /// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
    let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : AccAndTypeId =
        match pattern with
        | Named ident ->
            Accumulator.addRefDefResOptWithRefConstrsChanges
                None
                (Set.singleton (ByValue (LocalLower ident)))
                Accumulator.empty

        | Ignored -> Accumulator.addRefDefResOpt None Accumulator.empty

        | Unit -> Accumulator.addRefDefResOpt (Some (Ok RefDtUnitType)) Accumulator.empty

        | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured

        | Aliased (pattern_, alias) ->
            let nestedAccAndType = getInferredTypeFromAssignmentPattern pattern_

            let withNameAdded =
                Accumulator.addRefDefResOptWithRefConstrsChanges
                    None
                    (Set.singleton (ByValue (LocalLower alias)))
                    nestedAccAndType.acc

            Accumulator.unifyTypeConstraintIdsChanges nestedAccAndType.typeId withNameAdded.typeId withNameAdded.acc


    and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : AccAndTypeId =
        match pattern with
        | DestructuredRecord fieldNames ->
            let fields =
                fieldNames
                |> NEL.map (fun recFieldName ->
                    recFieldName,
                    Accumulator.addRefDefResOptWithRefConstrsChanges
                        None
                        (Set.singleton (ByValue (LocalLower (recFieldToLowerIdent recFieldName))))
                        Accumulator.empty)
                |> Map.ofSeq

            let combinedAcc =
                fields
                |> Map.fold (fun state _ v -> Accumulator.combine v.acc state) Accumulator.empty

            let refDefType =
                fields
                |> Map.map (fun _ v -> v.typeId)
                |> RefDtRecordWith

            Accumulator.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


        | DestructuredCons consItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern consItems
            let combinedAcc = Accumulator.combineAccsFromAatis gatheredItems

            let unified =
                combinedAcc
                |> Accumulator.unifyManyTypeConstraintIds (TOM.map Aati.getId gatheredItems)

            let refDefType = RefDtList unified.typeId
            Accumulator.addRefDefResOpt (Some (Ok refDefType)) unified.acc


        | DestructuredTuple tupleItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern tupleItems

            let combinedAcc = Accumulator.combineAccsFromAatis gatheredItems

            let refDefType = RefDtTuple (TOM.map Aati.getId gatheredItems)
            Accumulator.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


        | DestructuredTypeVariant (ctor, params_) ->
            let gatheredParams = List.map getInferredTypeFromAssignmentPattern params_
            let combinedAcc = Accumulator.combineAccsFromAatis gatheredParams

            let ctorType = ByConstructorType ctor

            match List.map Aati.getId gatheredParams with
            | [] ->
                // I.e. there are no params
                Accumulator.addRefDefResOptWithRefConstrsChanges None (Set.singleton ctorType) combinedAcc

            | head :: tail ->
                // I.e. there are params

                /// @TODO: I'm not 100% sure that this is the best way to do this, or if there is actually a more consistent way to specify what the relationship of the constructor to the params should be.
                /// E.g. one thing which `makeAccIdFuncApplicationType` does *not* capture is the fact that these are not just *some* parameters, but they need to be *all* of the parameters for that type variant. Otherwise should be a type error.
                let withFuncRequirement =
                    makeAccIdFuncApplicationType (NEL.new_ head tail) combinedAcc

                Accumulator.combine combinedAcc withFuncRequirement.acc
                |> Accumulator.addRefDefResOptWithRefConstrsChanges None (Set.singleton ctorType)



    getInferredTypeFromAssignmentPattern param






/// This should: from a binding, derive the type + all the names declared/destructured along with their types in the Accumulator - for use in the let expression body (and of course not outside of it)
and getAccumulatorFromBinding (binding : LetBinding) : AccAndTypeId =
    getAccumulatorFromParam binding.paramPattern




/// This will only return names in the keys and only if they are locally defined, not namespaced ones
and getLocalValueNames (acc : Accumulator) : LowerIdent set =
    Map.values acc.refConstraintsMap
    |> Seq.map snd
    |> Set.unionMany
    |> Set.choose (function
        | ByValue (LocalLower name) -> Some name
        | _ -> None)


and makeGuidMapForNames (names : LowerIdent set) : Map<LowerIdent, TypeConstraintId> =
    Set.toList names
    |> List.map (fun name -> name, makeTypeConstrId ())
    |> Map.ofList





and replaceRefConstrInDefType switcher (defType : DefinitiveType) =
    match defType with
    | DtUnitType -> DtUnitType
    | DtPrimitiveType p -> DtPrimitiveType p
    | DtTuple tom -> DtTuple (TOM.map (replaceRefConstrInTypeConstraints switcher) tom)
    | DtList tc -> DtList (replaceRefConstrInTypeConstraints switcher tc)
    | DtRecordWith fields -> DtRecordWith (Map.map (fun _ -> replaceRefConstrInTypeConstraints switcher) fields)
    | DtRecordExact fields -> DtRecordExact (Map.map (fun _ -> replaceRefConstrInTypeConstraints switcher) fields)
    | DtNewType (typeName, typeParams) ->
        DtNewType (typeName, List.map (replaceRefConstrInTypeConstraints switcher) typeParams)
    | DtArrow (fromType, toType) ->
        DtArrow (replaceRefConstrInTypeConstraints switcher fromType, replaceRefConstrInTypeConstraints switcher toType)

and replaceRefConstrInTypeConstraints switcher tc =
    let (Constrained (defOpt, refs)) = tc

    Constrained (Option.map (replaceRefConstrInDefType switcher) defOpt, switcher refs)





/// Replaces the references to names in the ref constraints with guids
and singleSwitcher (names : Map<LowerIdent, TypeConstraintId>) (refConstr : RefConstr) =
    match refConstr with
    | ByValue (LocalLower ident) ->
        match Map.tryFind ident names with
        | Some replacementId -> IsBoundVar replacementId
        | None -> refConstr

    //| HasTypeOfFirstParamOf constr' -> HasTypeOfFirstParamOf (singleSwitcher names constr')
    //| IsOfTypeByName (name, typeParams) ->
    //    IsOfTypeByName (name, List.map (replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names))) typeParams)
    | _ -> refConstr




and replaceValueNamesWithGuidsInTypeConstraints
    (names : Map<LowerIdent, TypeConstraintId>)
    (tc : TypeConstraints)
    : TypeConstraints =
    replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names)) tc


/// Replaces name references with bound var constraint IDs
and replaceNameRefsWithBoundVars (names : Map<LowerIdent, TypeConstraintId>) (acc : Accumulator) : Accumulator =
    let switcher = Set.map (singleSwitcher names)

    { acc with
        refConstraintsMap =
            acc.refConstraintsMap
            |> Map.map (fun _ (refDefOpt, refConstrs) -> refDefOpt, switcher refConstrs) }



and replaceValueNamesWithGuidsInTypeJudgment
    (names : Map<LowerIdent, TypeConstraintId>)
    (typeJudgment : TypeJudgment)
    : TypeJudgment =
    Result.map (replaceValueNamesWithGuidsInTypeConstraints names) typeJudgment









and private deleteAllBoundVarsFromRefConstraints (refConstr : RefConstr) =
    match refConstr with
    | IsBoundVar _ -> None
    | _ -> Some refConstr


and deleteGuidsFromDefType (defType : DefinitiveType) =
    match defType with
    | DtUnitType -> DtUnitType
    | DtPrimitiveType p -> DtPrimitiveType p
    | DtTuple tom -> DtTuple (TOM.map (deleteGuidsFromTypeConstraints) tom)
    | DtList tc -> DtList (deleteGuidsFromTypeConstraints tc)
    | DtRecordWith fields -> DtRecordWith (Map.map (fun _ -> deleteGuidsFromTypeConstraints) fields)
    | DtRecordExact fields -> DtRecordExact (Map.map (fun _ -> deleteGuidsFromTypeConstraints) fields)
    | DtNewType (typeName, typeParams) -> DtNewType (typeName, List.map (deleteGuidsFromTypeConstraints) typeParams)
    | DtArrow (fromType, toType) ->
        DtArrow (deleteGuidsFromTypeConstraints fromType, deleteGuidsFromTypeConstraints toType)



/// Delete bound vars with guids from TypeConstraints, for better test comparisons
and deleteGuidsFromTypeConstraints (tc : TypeConstraints) =
    let (Constrained (defOpt, refs)) = tc

    Constrained (Option.map (deleteGuidsFromDefType) defOpt, Set.choose (deleteAllBoundVarsFromRefConstraints) refs)









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

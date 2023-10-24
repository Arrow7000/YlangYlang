module TypeChecker
// Should maybe call this type inference


open Lexer


module Cst = ConcreteSyntaxTree
module S = SyntaxTree
module Q = QualifiedSyntaxTree
module T = TypedSyntaxTree

open Q.Names
open TypedSyntaxTree

module NameRes = TypedNameResolution

open NameResolution


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







(*

    Operator grouping stuff

*)


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
        | S.FloatLiteral _ -> RefDtPrimType Float
        | S.IntLiteral _ -> RefDtPrimType Int
    | S.CharPrimitive _ -> RefDtPrimType Char
    | S.StringPrimitive _ -> RefDtPrimType String
    | S.UnitPrimitive _ -> RefDtUnitType
    | S.BoolPrimitive _ -> RefDtPrimType Bool





(*
    Helpers for replacing bound variables with Guids that represent invariant constraints
*)


/// This will only return names in the keys and only if they are locally defined, not namespaced ones
let getLocalValueNames (acc : Accumulator) : LowerIdent set =
    Map.values acc.refConstraintsMap
    |> Seq.map snd
    |> Set.unionMany
    |> Set.choose (function
        | ByValue (LocalLower name) -> Some name
        | _ -> None)


let makeGuidMapForNames (names : LowerIdent set) : Map<LowerIdent, TypeConstraintId> =
    Set.toList names
    |> List.map (fun name -> name, makeTypeConstrId ())
    |> Map.ofList




let rec replaceRefConstrInTypeConstraints (switcher : RefConstr set -> RefConstr set) (tc : TypeConstraints) =
    let (Constrained (defOpt, refs)) = tc

    Constrained (Option.map (replaceRefConstrInDefType switcher) defOpt, switcher refs)

and replaceRefConstrInDefType (switcher : RefConstr set -> RefConstr set) (defType : DefinitiveType) =
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



///
/// Replaces the references to names in the ref constraints with guids
let singleSwitcher (names : Map<LowerIdent, TypeConstraintId>) (refConstr : RefConstr) =
    match refConstr with
    | ByValue (LocalLower ident) ->
        match Map.tryFind ident names with
        | Some replacementId -> IsBoundVar replacementId
        | None -> refConstr

    //| HasTypeOfFirstParamOf constr' -> HasTypeOfFirstParamOf (singleSwitcher names constr')
    //| IsOfTypeByName (name, typeParams) ->
    //    IsOfTypeByName (name, List.map (replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names))) typeParams)
    | _ -> refConstr




let replaceValueNamesWithGuidsInTypeConstraints
    (names : Map<LowerIdent, TypeConstraintId>)
    (tc : TypeConstraints)
    : TypeConstraints =
    replaceRefConstrInTypeConstraints (Set.map (singleSwitcher names)) tc


/// Replaces name references with bound var constraint IDs
let replaceNameRefsWithBoundVars (names : Map<LowerIdent, TypeConstraintId>) (acc : Accumulator) : Accumulator =
    let switcher = Set.map (singleSwitcher names)

    { acc with
        refConstraintsMap =
            acc.refConstraintsMap
            |> Map.map (fun _ (refDefOpt, refConstrs) -> refDefOpt, switcher refConstrs) }



let replaceValueNamesWithGuidsInTypeJudgment
    (names : Map<LowerIdent, TypeConstraintId>)
    (typeJudgment : TypeJudgment)
    : TypeJudgment =
    Result.map (replaceValueNamesWithGuidsInTypeConstraints names) typeJudgment









let rec private deleteAllBoundVarsFromRefConstraints (refConstr : RefConstr) =
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








/// Converts a CST node to an AST node ready for type inference
let rec convertCstToAst (resolutionChain : LowerIdent list) (expr : Cst.Expression) : T.Expression =

    match expr with
    | S.SingleValueExpression singleVal ->
        match singleVal with
        | S.ExplicitValue explicit ->
            match explicit with
            | S.Primitive primitive ->
                Primitive primitive
                |> ExplicitValue
                |> SingleValueExpression


            | S.DotGetter dotGetter ->
                let recFieldName = unqualValToRecField dotGetter

                DotGetter recFieldName
                |> ExplicitValue
                |> SingleValueExpression

            | S.Compound compound ->
                match compound with
                | S.List list ->
                    let typedList = List.map (S.getNode >> convertCstToAst resolutionChain) list

                    typedList
                    |> T.List
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.Tuple tuple ->
                    let typedList = TOM.map (S.getNode >> convertCstToAst resolutionChain) tuple

                    typedList
                    |> CompoundValues.Tuple
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) ->
                            unqualValToRecField key.node, convertCstToAst resolutionChain value.node)

                    typedList
                    |> CompoundValues.Record
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.RecordExtension (extended, additions) ->

                    let typedList =
                        additions
                        |> NEL.map (fun (key, value) ->
                            unqualValToRecField key.node, convertCstToAst resolutionChain value.node)

                    CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

            | S.Function funcVal ->
                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
                let typeOfBody = convertCstToAst resolutionChain funcVal.body.node

                let funcParams : FunctionOrCaseMatchParam nel =
                    funcVal.params_
                    |> NEL.map (S.getNode >> typeFuncOrCaseMatchParam)


                let funcVal : FunctionValue =
                    { params_ = funcParams
                      body = typeOfBody }

                Function funcVal
                |> ExplicitValue
                |> SingleValueExpression


        | S.UpperIdentifier name ->
            let ctorName = typeOrModuleIdentToUpperNameVal name

            UpperIdentifier ctorName |> SingleValueExpression

        | S.LowerIdentifier name ->
            let lowerNameVal = convertValueIdentifierToLowerName name

            LowerIdentifier lowerNameVal
            |> SingleValueExpression

        | S.LetExpression (declarations, expr) ->

            let bodyExpr = convertCstToAst resolutionChain expr.node


            let typedDeclarations : LetBindings =
                declarations
                |> NEL.map (fun binding -> binding.node.bindPattern.node, binding.node.value.node)
                |> NEL.map (fun (bindPattern, bindValue) ->
                    let param = typeFuncOrCaseMatchParam bindPattern
                    let boundNames = param.namesMap |> Map.keys |> Seq.toList
                    let assignedExpr = convertCstToAst (boundNames @ resolutionChain) bindValue

                    { paramPattern = param.paramPattern
                      namesMap = param.namesMap
                      assignedExpression = assignedExpr })

            LetExpression (typedDeclarations, bodyExpr)
            |> SingleValueExpression


        | S.ControlFlowExpression controlFlow ->
            match controlFlow with
            | S.IfExpression (cond, ifTrue, ifFalse) ->
                let conditionalWithBoolConstraint = convertCstToAst resolutionChain cond.node

                // This is aiming to express the type constraint that both branches of the if expression should have the same type

                let typedIfTrueBranch = convertCstToAst resolutionChain ifTrue.node
                let typedIfFalseBranch = convertCstToAst resolutionChain ifFalse.node

                // This should leave whichever one had the original definitive type unchanged, and only add a definitive constraint to the other one
                let unifiedTrue = typedIfTrueBranch
                let unifiedFalse = typedIfFalseBranch

                IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
                |> ControlFlowExpression
                |> SingleValueExpression


            | S.CaseMatch (exprToMatch, branches) ->
                let typedExprToMatch = convertCstToAst resolutionChain exprToMatch.node

                let typedBranches =
                    branches
                    |> NEL.map (fun (pattern, branchExpr) ->
                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
                          body = convertCstToAst resolutionChain branchExpr.node })

                CaseMatch (typedExprToMatch, typedBranches)
                |> ControlFlowExpression
                |> SingleValueExpression

    | S.CompoundExpression compExpr ->
        match compExpr with
        | S.FunctionApplication (funcExpr, params_) ->
            let typedFunc = convertCstToAst resolutionChain funcExpr.node

            let typedParams =
                params_
                |> NEL.map (S.getNode >> convertCstToAst resolutionChain)

            FunctionApplication (typedFunc, typedParams)
            |> CompoundExpression

        | S.DotAccess (dottedExpr, dotSequence) ->
            let rec makeNestedMap (fieldSeq : RecordFieldName list) =
                match fieldSeq with
                | [] -> TypeConstraints.empty
                | head :: rest ->
                    Map.empty
                    |> Map.add head (makeNestedMap rest)
                    |> DtRecordWith
                    |> TypeConstraints.fromDefinitive

            let typedExpr = convertCstToAst resolutionChain dottedExpr.node

            DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
            |> CompoundExpression

        | S.Operator (left, opSequence) ->
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"

    | S.ParensedExpression expr -> convertCstToAst resolutionChain expr






















module Acc = Accumulator
module Aati = Acc.AccAndTypeId

type private AccAndTypeId = Acc.AccAndTypeId

/// Just effectively a module alias import
type private TC = TypeConstraints











(*

    Helpers for function types and record dotting

*)


/// Pass in the IDs for the params and return type and this will return an Acc and AccId for the overall arrow type
let rec makeAccIdDestType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =
    match rest with
    | [] ->
        // In other words, it's not actually a function, we just have a value
        Aati.make first acc

    | head :: tail ->
        /// Get the type information from the return type, whether it's an arrow or not
        let tailResult = makeAccIdDestType (NEL.new_ head tail) acc
        let refDefType = RefDtArrow (first, tailResult.typeId)

        // And insert the new arrow type into the Acc
        Accumulator.addRefDefResOpt (Ok refDefType |> Some) tailResult.acc



/// Pass in the IDs for the params passed to a function and return the arrow type the function expression must be inferred to be
let rec makeAccIdFuncApplicationType ((NEL (first, rest)) : AccumulatorTypeId nel) (acc : Accumulator) : AccAndTypeId =

    let makeArrowType (aati : AccAndTypeId) : AccAndTypeId =
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

    let makeDotRecord fieldName (aati : AccAndTypeId) =
        let refDefType = RefDtRecordWith ([ fieldName, aati.typeId ] |> Map.ofSeq)
        Accumulator.addRefDefResOpt (Some (Ok refDefType)) aati.acc

    match rest with
    | [] ->
        let unspecific = Accumulator.addRefDefResOpt None acc
        makeDotRecord first unspecific

    | head :: tail ->
        let tailResult = makeDottedSeqImpliedType (NEL.new_ head tail) acc
        makeDotRecord first tailResult








/// Get type information based on a single assignment pattern – named values, destructurings, and so on.
/// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
let getAccumulatorFromParam (param : AssignmentPattern) : AccAndTypeId =
    let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : AccAndTypeId =
        match pattern with
        | Named ident -> Acc.addRefDefResOptWithRefConstrs None (Set.singleton (ByValue (LocalLower ident))) Acc.empty

        | Ignored -> Acc.addRefDefResOpt None Acc.empty

        | Unit -> Acc.addRefDefResOpt (Some (Ok RefDtUnitType)) Acc.empty

        | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured

        | Aliased (pattern_, alias) ->
            let nestedAccAndType = getInferredTypeFromAssignmentPattern pattern_

            let withNameAdded =
                Acc.addRefDefResOptWithRefConstrs None (Set.singleton (ByValue (LocalLower alias))) nestedAccAndType.acc

            Acc.unifyTwoAccTypeIds nestedAccAndType.typeId withNameAdded.typeId withNameAdded.acc


    and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : AccAndTypeId =
        match pattern with
        | DestructuredRecord fieldNames ->
            let fields =
                fieldNames
                |> NEL.map (fun recFieldName ->
                    recFieldName,
                    Acc.addRefDefResOptWithRefConstrs
                        None
                        (Set.singleton (ByValue (LocalLower (recFieldToLowerIdent recFieldName))))
                        Acc.empty)
                |> Map.ofSeq

            let combinedAcc =
                fields
                |> Map.fold (fun state _ v -> Acc.combine v.acc state) Acc.empty

            let refDefType =
                fields
                |> Map.map (fun _ v -> v.typeId)
                |> RefDtRecordWith

            Acc.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


        | DestructuredCons consItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern consItems
            let combinedAcc = Acc.combineAccsFromAatis gatheredItems

            let unified =
                combinedAcc
                |> Acc.unifyManyTypeConstraintIds (TOM.map Aati.getId gatheredItems)

            let refDefType = RefDtList unified.typeId
            Acc.addRefDefResOpt (Some (Ok refDefType)) unified.acc


        | DestructuredTuple tupleItems ->
            let gatheredItems = TOM.map getInferredTypeFromAssignmentPattern tupleItems

            let combinedAcc = Acc.combineAccsFromAatis gatheredItems

            let refDefType = RefDtTuple (TOM.map Aati.getId gatheredItems)
            Acc.addRefDefResOpt (Some (Ok refDefType)) combinedAcc


        | DestructuredTypeVariant (ctor, params_) ->
            let gatheredParams = List.map getInferredTypeFromAssignmentPattern params_
            let combinedAcc = Acc.combineAccsFromAatis gatheredParams

            let ctorType = ByConstructorType ctor

            match List.map Aati.getId gatheredParams with
            | [] ->
                // I.e. there are no params
                Acc.addRefDefResOptWithRefConstrs None (Set.singleton ctorType) combinedAcc

            | head :: tail ->
                // I.e. there are params

                /// @TODO: I'm not 100% sure that this is the best way to do this, or if there is actually a more consistent way to specify what the relationship of the constructor to the params should be.
                /// E.g. one thing which `makeAccIdFuncApplicationType` does *not* capture is the fact that these are not just *some* parameters, but they need to be *all* of the parameters for that type variant. Otherwise should be a type error.
                let withFuncRequirement =
                    makeAccIdFuncApplicationType (NEL.new_ head tail) combinedAcc

                Acc.combine combinedAcc withFuncRequirement.acc
                |> Acc.addRefDefResOptWithRefConstrs None (Set.singleton ctorType)



    getInferredTypeFromAssignmentPattern param








/// This should: from a binding, derive the type + all the names declared/destructured along with their types in the Accumulator - for use in the let expression body (and of course not outside of it)
let private getAccumulatorFromBinding (binding : LetBinding) : AccAndTypeId =
    getAccumulatorFromParam binding.paramPattern





(*
    Get Accumulator and type from expressions
*)

/// Return the Accumulator of constrained values along with the type ID of the expression in its entirety
let rec getAccumulatorFromExpr (expr : T.Expression) : AccAndTypeId =

    let makeOkType = Ok >> Some
    let getParamFromPattern (pattern : FunctionOrCaseMatchParam) = pattern.paramPattern

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
                    |> NEL.map Aati.getAcc


                let funcParamTypes =
                    funcParamsAccumulatorsAndSelfTypes
                    |> NEL.map Aati.getId

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





        | T.LetExpression (declarations, expr') ->
            let bodyExpr = getAccumulatorFromExpr expr'

            let typedDeclarations =
                declarations
                |> NEL.map (fun binding ->
                    let bindingAccAndSelf = getAccumulatorFromParam binding.paramPattern
                    let assignedExprAccAndSelf = getAccumulatorFromExpr binding.assignedExpression

                    let combinedAcc =
                        Accumulator.combineAccsFromAatis [ bindingAccAndSelf
                                                           assignedExprAccAndSelf ]

                    Accumulator.unifyTwoAccTypeIds bindingAccAndSelf.typeId assignedExprAccAndSelf.typeId combinedAcc)


            let combinedAcc =
                Accumulator.combineAccsFromAatis typedDeclarations
                |> Acc.combine bodyExpr.acc

            /// This contains all the names defined from each param
            let combinedNamesDefinedHere = getLocalValueNames combinedAcc
            let guidMap = makeGuidMapForNames combinedNamesDefinedHere


            replaceNameRefsWithBoundVars guidMap combinedAcc
            |> Aati.make bodyExpr.typeId



        | T.ControlFlowExpression controlFlow ->
            match controlFlow with
            | T.IfExpression (cond, ifTrue, ifFalse) ->
                let condAccAndOwn = getAccumulatorFromExpr cond

                let boolRefDef = RefDtPrimType BuiltInPrimitiveTypes.Bool

                let withBoolConstrAdded =
                    Accumulator.addRefDefConstraintForAccId
                        (makeOkType boolRefDef)
                        condAccAndOwn.typeId
                        condAccAndOwn.acc

                let ifTrueAccAndOwn = getAccumulatorFromExpr ifTrue
                let ifFalseAccAndOwn = getAccumulatorFromExpr ifFalse

                let combinedAcc =
                    Accumulator.combineMany [ withBoolConstrAdded.acc
                                              ifTrueAccAndOwn.acc
                                              ifFalseAccAndOwn.acc ]

                Accumulator.unifyTwoAccTypeIds ifTrueAccAndOwn.typeId ifFalseAccAndOwn.typeId combinedAcc



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
            // @TODO: no no no no no, this is wrong. The applied parameters don't need to impose constraints on the function expression; they just need to not clash with them! In other words, we want to maintain let polymorphism!
            // So how to do this... hmmm. Well I think instead of just unifying the thing back to the function expression, we want to... just ensure there is no clash? Hm not sure exactly how to approach this.
            |> Accumulator.unifyTwoAccTypeIds funcExprAccAndSelf.typeId requiredFuncAccAndId.typeId


        | T.DotAccess (dottedExpr, dotSequence) ->
            let exprAccAndSelf = getAccumulatorFromExpr dottedExpr

            let withImpliedRecordType = makeDottedSeqImpliedType dotSequence exprAccAndSelf.acc

            Accumulator.unifyTwoAccTypeIds exprAccAndSelf.typeId withImpliedRecordType.typeId withImpliedRecordType.acc


        | T.Operator (left, op, right) ->
            // @TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"
















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



/// @TODO: hm not sure this makes sense anymore if we don't store the type of the expressions inside the record itself but it's computed by a function
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
                          value = convertCstToAst List.empty infixOp.value.node }
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
                        convertCstToAst [ ident ] valDecl.value.node
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

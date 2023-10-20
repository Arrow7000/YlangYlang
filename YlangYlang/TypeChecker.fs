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















let rec typeCheckCstExpression (resolutionChain : LowerIdent list) (expr : Cst.Expression) : T.Expression =

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
                    let typedList =
                        List.map
                            (S.getNode
                             >> typeCheckCstExpression resolutionChain)
                            list

                    typedList
                    |> T.List
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.Tuple tuple ->
                    let typedList =
                        TOM.map
                            (S.getNode
                             >> typeCheckCstExpression resolutionChain)
                            tuple

                    typedList
                    |> CompoundValues.Tuple
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.Record record ->
                    let typedList =
                        record
                        |> List.map (fun (key, value) ->
                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

                    typedList
                    |> CompoundValues.Record
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

                | S.CompoundValues.RecordExtension (extended, additions) ->

                    let typedList =
                        additions
                        |> NEL.map (fun (key, value) ->
                            unqualValToRecField key.node, typeCheckCstExpression resolutionChain value.node)

                    CompoundValues.RecordExtension (unqualValToLowerIdent extended.node, typedList)
                    |> Compound
                    |> ExplicitValue
                    |> SingleValueExpression

            | S.Function funcVal ->
                // @TODO: we need to actually add the params to namesMaps before we can type check the expression
                let typeOfBody = typeCheckCstExpression resolutionChain funcVal.body.node

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

            LetExpression (typedDeclarations, bodyExpr)
            |> SingleValueExpression


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

                IfExpression (conditionalWithBoolConstraint, unifiedTrue, unifiedFalse)
                |> ControlFlowExpression
                |> SingleValueExpression


            | S.CaseMatch (exprToMatch, branches) ->
                let typedExprToMatch = typeCheckCstExpression resolutionChain exprToMatch.node

                let typedBranches =
                    branches
                    |> NEL.map (fun (pattern, branchExpr) ->
                        { matchPattern = typeFuncOrCaseMatchParam pattern.node
                          body = typeCheckCstExpression resolutionChain branchExpr.node })

                CaseMatch (typedExprToMatch, typedBranches)
                |> ControlFlowExpression
                |> SingleValueExpression

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

            let typedExpr = typeCheckCstExpression resolutionChain dottedExpr.node

            DotAccess (typedExpr, dotSequence.node |> NEL.map unqualValToRecField)
            |> CompoundExpression

        | S.Operator (left, opSequence) ->
            failwith
                "@TODO: need to break up operator sequence into a binary tree of operators branch nodes and operands leaf nodes"

    | S.ParensedExpression expr -> typeCheckCstExpression resolutionChain expr









/// Basically the same as the AccumulatorAndOwnType
type AccAndTypeId =
    { typeId : AccumulatorTypeId
      acc : Accumulator }


module AccAndTypeId =
    let make accTypeId acc : AccAndTypeId =
        /// @TODO: delete this when testing is complete
        let _ =
            try
                Accumulator.getTypeById accTypeId acc
            with
            | _ -> failwithf "Tried to make an Aati with an ID that's not present in the Acc!"

        { acc = acc; typeId = accTypeId }

    let getId (aati : AccAndTypeId) = aati.typeId
    let getAcc (aati : AccAndTypeId) = aati.acc






module Accumulator =

    (*
        Helpers for the accumulator
    *)



    module Aati = AccAndTypeId








    let private makeAccTypeId () : AccumulatorTypeId =
        System.Guid.NewGuid () |> AccumulatorTypeId




    let empty = Accumulator.empty



    type private UnifyRefDefPassResult =
        { refConstrsToUnify : RefConstr set seq
          accAndTypeId : AccAndTypeId }


    type private UnifyRefConstrsPassResult =
        /// The added refConstrs are not present in the Acc at all, so just create a new entry with only these RefConstrs and call it a day
        | NotCurrentlyInAcc
        /// The added refConstrs overlap with exactly one Acc entry, so all you need to do is replace that ID's existing RefConstrs with this one and call it a day
        | InOneEntry of realAccId : AccumulatorTypeId * combinedRefConstrs : RefConstr set
        /// The added refConstrs overlap with two or more Acc entries, so the RefDefs need to be unified, and they all need to have their refConstrs set to this unified set
        | InMultipleEntries of realAccIds : AccumulatorTypeId tom * allUnifiedRefConstrs : RefConstr set








    /// Given a set of RefConstrs to add into the Acc, this tells us whether they are either:
    ///     a) not in the Acc at all – so only one new entry with only these RefConstrs needs to be added
    ///     b) only present in one entry in the Acc – so we only need to add the combined RefConstrs (the existing ones for that entry + the ones provided here) to the existing entry in the Acc
    ///     c) present in multiple entries in the Acc – so those RefDefs in those entries need to be unified, and have its RefConstrs set as the union of both all the refConstrs in the unified entries + the ones provided here
    let rec private getRefConstrAddOrUnifyInfo
        (refConstrsToAddOrUnify : RefConstr set)
        (acc : Accumulator)
        : UnifyRefConstrsPassResult =
        let toBeMerged =
            acc.refConstraintsMap
            |> Map.choose (fun _ (_, refConstrs) ->
                if Set.hasOverlap refConstrs refConstrsToAddOrUnify then
                    let refConstrsUnion = Set.union refConstrs refConstrsToAddOrUnify

                    Some refConstrsUnion
                else
                    None)
            |> Map.toList

        match toBeMerged with
        | [] -> NotCurrentlyInAcc

        | onlyOne :: [] ->

            let accId, refConstrsUnion = onlyOne
            InOneEntry (accId, refConstrsUnion)

        | head :: neck :: tail ->
            let toBeMergedTom = TOM.new_ head neck tail

            /// This contains all the RefConstrs to put in the new entry
            let fullRefConstrUnion = TOM.map snd toBeMergedTom |> Set.unionMany

            let idsToMerge = TOM.map fst toBeMergedTom

            InMultipleEntries (idsToMerge, fullRefConstrUnion)


    /// This returns the Accumulator resulting from unifying the two or more AccIds and RefDefs
    ///
    /// @TODO: I think... unifying RefDefs should never ever need to return the "refConstrs to unify", because since the sets of RefConstrs should be completely disjoint... if we're unifying refdefs all we need to do is store a simple union of the refconstrs and that should never ever have any further ramifications... the only thing is if we're introducing a new refconstr set that combines a bunch of them, that could entail merging more than one thing... but even then, all we need to do then is a snowballing of those RefDefs into a single type result/judgment, but the refconstraints..? they're still only ever going to be a single fucking union. With never any further ramifications after unifying the refdefs... so... i think perhaps this whole symmetric single pass thing has been a bit of a red herring and maybe it's only the refConstr unification that can result in refDefs to unify, but once that's done... the refDef unification can do a simple unification of its own RefConstrs and call it a day... wahoooowww.
    let rec private unifyRefDefResOptsTom
        (refDefsWithIds : (AccumulatorTypeId * Result<RefDefType, AccTypeError> option) tom)
        (acc : Accumulator)
        : AccAndTypeId =

        let rec unifyTwoRefDefs
            (a : AccumulatorTypeId * RefDefType)
            (b : AccumulatorTypeId * RefDefType)
            (acc : Accumulator)
            : AccAndTypeId =
            // @TODO: So I think this will be the longer one with the lengthy logic for how to merge two RefDefTypes with all their intricate little details
            let makeOkType : RefDefType -> Result<RefDefType, AccTypeError> option = Ok >> Some

            let makeErrType a' b' : Result<RefDefType, AccTypeError> option = DefTypeClash (a', b') |> Error |> Some


            let accIdA, refDefA = a
            let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

            let accIdB, refDefB = b
            let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd

            let newKey = makeAccTypeId ()
            let accIdsToReplace = Set.ofList [ accIdA; accIdB ]

            /// For this level/pass of unification
            let combinedRefConstrs = Set.union refConstrsA refConstrsB

            /// Returns an error with the lists so far if lists don't have the same length; which will be a list of n pairs, where n is the length of the shorter of the two input lists.
            /// If the lists are not the same length, the Error will contain the combined lists so far. This is useful so that we can do some type checking on those bits that do overlap.
            let zipList listA listB : Result<('a * 'b) list, ('a * 'b) list> =
                let rec zipList_ combinedSoFar a b =
                    match a, b with
                    | [], [] -> Ok (List.rev combinedSoFar)
                    | headA :: tailA, headB :: tailB -> zipList_ ((headA, headB) :: combinedSoFar) tailA tailB
                    | [], _ :: _
                    | _ :: _, [] -> Error (List.rev combinedSoFar)

                zipList_ List.empty listA listB



            match refDefA, refDefB with
            | RefDtUnitType, RefDtUnitType ->
                let updatedAcc =
                    Accumulator.replaceEntries accIdsToReplace newKey (makeOkType RefDtUnitType) combinedRefConstrs acc

                Aati.make newKey updatedAcc


            | RefDtPrimitiveType primA, RefDtPrimitiveType primB ->
                let typeResult =
                    if primA = primB then
                        makeOkType (RefDtPrimitiveType primA)
                    else
                        makeErrType refDefA refDefB

                let updatedAcc =
                    Accumulator.replaceEntries accIdsToReplace newKey typeResult combinedRefConstrs acc

                Aati.make newKey updatedAcc


            | RefDtList paramA, RefDtList paramB ->
                let unifiedInnerResult = unifyTwoAccTypeIds paramA paramB acc

                let listType : RefDefType = RefDtList unifiedInnerResult.typeId

                let updatedAcc =
                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeOkType listType)
                        combinedRefConstrs
                        unifiedInnerResult.acc

                Aati.make newKey updatedAcc


            | RefDtTuple (TOM (headA, neckA, tailA)), RefDtTuple (TOM (headB, neckB, tailB)) ->
                /// This ensures the two lists of AccIds have the same length, it doesn't try to unify them yet
                let combinedListResult = zipList tailA tailB

                match combinedListResult with
                | Ok combinedList ->
                    let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedList

                    let unifiedAccIdsTom, combinedAcc =
                        combinedTom
                        |> TOM.foldMap
                            (fun state (idA, idB) ->
                                let unifyResult = unifyTwoAccTypeIds idA idB state
                                unifyResult.typeId, unifyResult.acc)
                            acc

                    let tupleType = RefDtTuple unifiedAccIdsTom

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeOkType tupleType)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey

                | Error combinedListSoFar ->
                    let combinedTom = TOM.new_ (headA, headB) (neckA, neckB) combinedListSoFar

                    let combinedAcc =
                        combinedTom
                        |> TOM.fold (fun state (idA, idB) -> unifyTwoAccTypeIds idA idB state |> Aati.getAcc) acc

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeErrType refDefA refDefB)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey


            | RefDtRecordExact mapA, RefDtRecordExact mapB ->
                let mergeResults =
                    // @TODO: Actually ideally we should get the results of unifying the constraints and then separately get whether it's a non-exact merge or not, so that we don't lose the type information from the values of the two different maps
                    Map.mergeExact (fun _ valA valB -> unifyTwoAccTypeIds valA valB acc) mapA mapB

                match mergeResults with
                | Ok mergedMap ->
                    let combinedAcc =
                        mergedMap
                        |> Map.fold (fun state _ aati -> combine aati.acc state) Accumulator.empty

                    let mapType =
                        mergedMap
                        |> Map.map (fun _ -> Aati.getId)
                        |> RefDtRecordExact

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeOkType mapType)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey

                | Error _ ->
                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeErrType refDefA refDefB)
                        combinedRefConstrs
                        acc
                    |> Aati.make newKey

            | RefDtRecordWith mapA, RefDtRecordWith mapB ->
                // @TODO: actually the logic here should be very different to that of exact maps!
                // @TODO: and actually there should also be compatible cases where one is exact and one is "with"!


                let mergeResults =
                    // @TODO: Actually ideally we should get the results of unifying the constraints and then separately get whether it's a non-exact merge or not, so that we don't lose the type information from the values of the two different maps
                    Map.mergeExact (fun _ valA valB -> unifyTwoAccTypeIds valA valB acc) mapA mapB

                match mergeResults with
                | Ok mergedMap ->
                    let combinedAcc =
                        mergedMap
                        |> Map.fold (fun state _ aati -> combine aati.acc state) Accumulator.empty

                    let mapType =
                        mergedMap
                        |> Map.map (fun _ -> Aati.getId)
                        |> RefDtRecordWith

                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeOkType mapType)
                        combinedRefConstrs
                        combinedAcc
                    |> Aati.make newKey

                | Error _ ->
                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeErrType refDefA refDefB)
                        combinedRefConstrs
                        acc
                    |> Aati.make newKey

            | RefDtNewType (nameA, typeParamsA), RefDtNewType (nameB, typeParamsB) ->
                if nameA = nameB then
                    let zippedLists = zipList typeParamsA typeParamsB

                    match zippedLists with
                    | Ok combinedList ->
                        let typeConstraintIdList, combinedAcc =
                            combinedList
                            |> List.mapFold
                                (fun state (idA, idB) ->
                                    let unifyResult = unifyTwoAccTypeIds idA idB state
                                    unifyResult.typeId, unifyResult.acc)
                                acc

                        let newType = RefDtNewType (nameA, typeConstraintIdList)

                        Accumulator.replaceEntries
                            accIdsToReplace
                            newKey
                            (makeOkType newType)
                            combinedRefConstrs
                            combinedAcc
                        |> Aati.make newKey

                    | Error combinedListSoFar ->
                        let combinedAcc =
                            combinedListSoFar
                            |> List.fold (fun state (idA, idB) -> unifyTwoAccTypeIds idA idB state |> Aati.getAcc) acc

                        Accumulator.replaceEntries
                            accIdsToReplace
                            newKey
                            (makeErrType refDefA refDefB)
                            combinedRefConstrs
                            combinedAcc
                        |> Aati.make newKey

                else
                    Accumulator.replaceEntries
                        accIdsToReplace
                        newKey
                        (makeErrType refDefA refDefB)
                        combinedRefConstrs
                        acc
                    |> Aati.make newKey


            | RefDtArrow (fromTypeA, toTypeA), RefDtArrow (fromTypeB, toTypeB) ->
                let unifiedFroms = unifyTwoAccTypeIds fromTypeA fromTypeB acc
                let unifiedTos = unifyTwoAccTypeIds toTypeA toTypeB unifiedFroms.acc

                let arrowType = RefDtArrow (unifiedFroms.typeId, unifiedTos.typeId)

                Accumulator.replaceEntries
                    accIdsToReplace
                    newKey
                    (makeOkType arrowType)
                    combinedRefConstrs
                    unifiedTos.acc
                |> Aati.make newKey


            | _, _ ->
                // @TODO: Fill in the case where the types are not compatible
                Accumulator.replaceEntries accIdsToReplace newKey (makeErrType refDefA refDefB) combinedRefConstrs acc
                |> Aati.make newKey




        and unifyTwoRefDefResults
            (a : AccumulatorTypeId * Result<RefDefType, AccTypeError>)
            (b : AccumulatorTypeId * Result<RefDefType, AccTypeError>)
            (acc : Accumulator)
            : AccAndTypeId =
            let accIdA, refDefResA = a
            let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

            let accIdB, refDefResB = b
            let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd

            match refDefResA, refDefResB with
            | Ok _, Error e
            | Error e, Ok _
            | Error e, Error _ ->
                let newKey = makeAccTypeId ()
                let accIdsToReplace = Set.ofList [ accIdA; accIdB ]
                let mergedRefConstrs = Set.union refConstrsA refConstrsB

                let updatedAcc =
                    Accumulator.replaceEntries accIdsToReplace newKey (Some (Error e)) mergedRefConstrs acc

                Aati.make newKey updatedAcc

            | Ok refDefA, Ok refDefB -> unifyTwoRefDefs (accIdA, refDefA) (accIdB, refDefB) acc



        /// This is the function that should be folded over all the `refDefsWithIds` in the input
        and unifyTwoRefDefResOpts
            (a : AccumulatorTypeId * Result<RefDefType, AccTypeError> option)
            (b : AccumulatorTypeId * Result<RefDefType, AccTypeError> option)
            (acc : Accumulator)
            : AccAndTypeId =

            let accIdA, refDefResOptA = a
            let refConstrsA : RefConstr set = Accumulator.getTypeById accIdA acc |> snd

            let accIdB, refDefResOptB = b
            let refConstrsB : RefConstr set = Accumulator.getTypeById accIdB acc |> snd


            let newKey = makeAccTypeId ()
            let accIdsToReplace = Set.ofList [ accIdA; accIdB ]
            let mergedRefConstrs = Set.union refConstrsA refConstrsB

            match refDefResOptA, refDefResOptB with
            | None, None ->
                let updatedAcc =
                    Accumulator.replaceEntries accIdsToReplace newKey None mergedRefConstrs acc

                Aati.make newKey updatedAcc

            | Some x, None
            | None, Some x ->
                let updatedAcc =
                    Accumulator.replaceEntries accIdsToReplace newKey (Some x) mergedRefConstrs acc

                Aati.make newKey updatedAcc

            | Some refDefResA, Some refDefResB -> unifyTwoRefDefResults (accIdA, refDefResA) (accIdB, refDefResB) acc



        let (TOM (head, neck, tail)) = refDefsWithIds
        let firstResult = unifyTwoRefDefResOpts head neck acc

        tail
        |> List.fold
            (fun state (accId, refDefResOpt) ->
                /// We retrieve the item whose ID is in the state because that's the one that the current item needs to be merged with
                let toMergeWith = Accumulator.getTypeById state.typeId state.acc

                let refDefToMergeWith : Result<RefDefType, AccTypeError> option = fst toMergeWith
                // // I don't think there was anything to do with this set, because this unifyRefDefsSinglePass function should only be responsible for unifying the RefDefs it was given, not the RefConstrs I think.
                //let refConstrsToMergeWith : RefConstr set = snd toMergeWith

                let unifyResult =
                    unifyTwoRefDefResOpts (accId, refDefResOpt) (state.typeId, refDefToMergeWith) state.acc


                unifyResult)
            firstResult
















    /// Version of unifyRefDefResOptsTom that only needs to be given AccIds, not the RefDefs also
    and unifyAccIdsTom (accIds : AccumulatorTypeId tom) (acc : Accumulator) : AccAndTypeId =
        let tom =
            accIds
            |> TOM.map (fun accId -> Accumulator.getRealIdAndType accId acc)
            |> TOM.map (fun (realAccId, (refDefResOpt, _)) -> realAccId, refDefResOpt)

        unifyRefDefResOptsTom tom acc




    /// Just a wrapper for unifyRefDefResOptsTom that handles all lists
    and unifyManyRefDefResOpts
        (refDefsWithIds : (AccumulatorTypeId * Result<RefDefType, AccTypeError> option) seq)
        (acc : Accumulator)
        : AccAndTypeId =
        match Seq.toList refDefsWithIds with
        | [] ->
            let newKey = makeAccTypeId ()

            { acc with
                refConstraintsMap =
                    acc.refConstraintsMap
                    |> Map.add newKey (None, Set.empty) }
            |> Aati.make newKey

        | (key, _) :: [] -> Aati.make key acc

        | head :: neck :: tail -> unifyRefDefResOptsTom (TOM.new_ head neck tail) acc





    /// This adds RefConstrs for an existing AccId and runs the unification if/when needed
    and addRefConstrsForAccId
        (accId : AccumulatorTypeId)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : AccAndTypeId =
        let refConstrInformation = getRefConstrAddOrUnifyInfo refConstrs acc

        /// Add the RefConstrs for the new entry
        let addRefConstrsToEntry combinedRefConstrs =
            Accumulator.replaceEntry accId (fun _ refDef _ -> refDef, combinedRefConstrs) acc
            |> snd

        match refConstrInformation with
        | UnifyRefConstrsPassResult.NotCurrentlyInAcc ->
            // The refConstrs need to be added for the newly added item

            addRefConstrsToEntry refConstrs |> Aati.make accId

        | UnifyRefConstrsPassResult.InOneEntry (existingAccId, combinedRefConstrs) ->
            // Unify the existing and new entries

            addRefConstrsToEntry combinedRefConstrs
            |> unifyTwoAccTypeIds existingAccId accId

        | UnifyRefConstrsPassResult.InMultipleEntries (accIds, combinedRefConstrs) ->
            // Unify the new and existing entries

            addRefConstrsToEntry combinedRefConstrs
            |> unifyAccIdsTom (TOM.cons accId accIds)



    /// Adds a new RefDef and its reference constraints into the map (including RefConstr overlap unification)
    and addRefDefResOptWithRefConstrs
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : AccAndTypeId =
        let accId, withRefDefAdded = Accumulator.addRefDefResOpt refDefResOpt acc

        addRefConstrsForAccId accId refConstrs withRefDefAdded



    /// Merges two accumulators. No IDs should be lost, refDefs should be unified according to reference constraint overlaps. And resulting combined IDs should be unified also.
    ///
    /// There should be no entities from one Acc referencing IDs in the other.
    and combine (acc1 : Accumulator) (acc2 : Accumulator) : Accumulator =
        // I think the way to do this is by inserting the items without any dependencies on other AccIds first, e.g. those entries which are None or Unit or PrimitiveType. Once those are done, then get their IDs and we can insert the next batch of types, namely those which reference (only) those IDs we've just inserted (or that reference any IDs we've inserted already, even if those were partly in a previous batch).
        // That way we can add one RefDefType (with accompanying RefConstrs) at a time, whilst still ensuring we never end up in a place where the Acc contains references to AccIds it does not contain!
        // Note: we add the items in acc1 to acc2, as per the convention where the last parameter is the data type being modified

        // @TODO: not sure this works if there are circular dependencies! Probably doesn't. We'll need to look into detecting cyclical deps and importing those as a single unit then.

        /// Is the given refDef one of the allowed ones
        let isRefDefWithAllowedAccIdDep (addedDepAccIds : AccumulatorTypeId set) (refDef : RefDefType) : bool =
            let hasId accId = Set.contains accId addedDepAccIds

            match refDef with
            | RefDtUnitType -> true
            | RefDtPrimitiveType _ -> true
            | RefDtList accId -> hasId accId
            | RefDtTuple accIdTom -> accIdTom |> TOM.map hasId |> TOM.fold (&&) true
            | RefDtRecordWith fields ->
                Map.values fields
                |> Seq.map hasId
                |> Seq.fold (&&) true
            | RefDtRecordExact fields ->
                Map.values fields
                |> Seq.map hasId
                |> Seq.fold (&&) true
            | RefDtNewType (_, typeParams) -> typeParams |> Seq.map hasId |> Seq.fold (&&) true
            | RefDtArrow (fromType, toType) -> hasId fromType && hasId toType


        /// Gets all the AccIds that redirect to a set of other AccIds, recursively
        let rec getAllRedirectsPointingTo (accIds : AccumulatorTypeId set) redirectsMap =
            let thisBatchResults =
                redirectsMap
                |> Map.filter (fun _ dest -> Set.contains dest accIds)
                |> Map.keys
                |> Seq.toList

            match thisBatchResults with
            | [] -> accIds
            | _ ->
                redirectsMap
                |> Map.removeKeys (Set.ofSeq thisBatchResults)
                |> getAllRedirectsPointingTo (Set.union accIds (Set.ofSeq thisBatchResults))



        /// Recursive function that plucks the types from the source Acc and moves them over to the destination Acc one at a time, ensuring it's only moving the ones that either have no dependencies on other AccIds, or whose dependencies have already been moved over!
        /// The base case is when there are no more new entries able to be moved over, which should occur only when the sourceAcc has been plucked empty – and therefore it's probably worth making it throw an error if only one but not both of those conditions are true!
        /// And at the base case, we return the destinationAcc, which should at that point be the fully merged Acc containing all the items from acc1 (and of course acc2 which is what it started out as)
        let rec getItemsWithAllowedDependencies (sourceAcc : Accumulator) (destinationAcc : Accumulator) : Accumulator =
            let addedDepAccIds =
                Set.union
                    (Map.keys destinationAcc.refConstraintsMap
                     |> Set.ofSeq)
                    (Map.keys destinationAcc.redirectMap |> Set.ofSeq)

            let allDepAccIds =
                getAllRedirectsPointingTo addedDepAccIds destinationAcc.redirectMap

            /// These are the entries whose AccIds they reference are all already in the destAcc so they can be moved over from the sourceAcc
            let entriesAllowedNow =
                sourceAcc.refConstraintsMap
                |> Map.filter (fun _ (refDefResOpt, _) ->
                    match refDefResOpt with
                    | None -> true
                    | Some refDefRes ->
                        match refDefRes with
                        | Ok refDef -> isRefDefWithAllowedAccIdDep allDepAccIds refDef
                        | Error (DefTypeClash (refDefA, refDefB)) ->
                            isRefDefWithAllowedAccIdDep allDepAccIds refDefA
                            && isRefDefWithAllowedAccIdDep allDepAccIds refDefB)


            let noMoreEntriesToAdd = Map.isEmpty entriesAllowedNow
            let sourceAccConstrsAreEmpty = Map.isEmpty sourceAcc.refConstraintsMap

            if noMoreEntriesToAdd && sourceAccConstrsAreEmpty then
                destinationAcc

            else if noMoreEntriesToAdd && not sourceAccConstrsAreEmpty then
                failwith
                    "Shouldn't be possible for there to be no more entries to add but the source Acc to not be empty"

            else if not noMoreEntriesToAdd && sourceAccConstrsAreEmpty then
                failwith "Shouldn't be possible for there to still be entries to add but the source Acc to be empty"

            else
                /// This expects that the thing we're adding does not depend on any AccIds that aren't already in the map
                let addSingleThingToDestMap
                    (singleThing : AccumulatorTypeId * (Result<RefDefType, AccTypeError> option * RefConstr set))
                    (acc : Accumulator)
                    : Accumulator =
                    let key, (refDefResOpt, refConstrs) = singleThing

                    let _, withRefDefInserted =
                        Accumulator.addRefDefResOptUnderKey key refDefResOpt acc
                        |> Accumulator.replaceEntry key (fun _ rd _ -> rd, refConstrs)

                    addRefConstrsForAccId key refConstrs withRefDefInserted
                    |> Aati.getAcc


                let updatedDestAcc =
                    entriesAllowedNow
                    |> Map.toList
                    |> List.fold (fun state thisEntry -> addSingleThingToDestMap thisEntry state) destinationAcc


                let updatedSourceAcc =
                    { sourceAcc with
                        refConstraintsMap =
                            sourceAcc.refConstraintsMap
                            |> Map.removeKeys (Map.keys entriesAllowedNow) }

                getItemsWithAllowedDependencies updatedSourceAcc updatedDestAcc


        getItemsWithAllowedDependencies acc1 { acc2 with redirectMap = Map.merge acc1.redirectMap acc2.redirectMap }







    and combineMany (accs : Accumulator seq) : Accumulator = Seq.fold combine Accumulator.empty accs

    /// Combine Accumulators from a seq of `AccAndTypeId`s
    and combineAccsFromAatis (aatis : AccAndTypeId seq) =
        Seq.map Aati.getAcc aatis |> combineMany







    /// Adds a new entry and unifies RefConstrs as needed
    and addRefConstraints (refConstrs : RefConstr set) (acc : Accumulator) : AccAndTypeId =
        addRefDefResOptWithRefConstrs None refConstrs acc



    and unifyTwoRefDefResOpts
        (accIdA : AccumulatorTypeId)
        (refDefResOptA : Result<RefDefType, AccTypeError> option)
        (accIdB : AccumulatorTypeId)
        (refDefResOptB : Result<RefDefType, AccTypeError> option)
        (acc : Accumulator)
        : AccAndTypeId =
        unifyRefDefResOptsTom (TOM.make (accIdA, refDefResOptA) (accIdB, refDefResOptB)) acc



    and unifyTwoAccTypeIds (idA : AccumulatorTypeId) (idB : AccumulatorTypeId) (acc : Accumulator) : AccAndTypeId =
        let itemA, _ = Accumulator.getTypeById idA acc
        let itemB, _ = Accumulator.getTypeById idB acc

        unifyTwoRefDefResOpts idA itemA idB itemB acc



    /// @TODO: maybe do this using the more fundamental unifyTypeConstraintIds? idk tho
    let unifyManyTypeConstraintIds (ids : AccumulatorTypeId seq) (acc : Accumulator) : AccAndTypeId =
        let refDefsWithIds =
            Seq.map (fun id -> id, Accumulator.getTypeById id acc |> fst) ids

        unifyManyRefDefResOpts refDefsWithIds acc





    /// This returns the Accumulator resulting from unifying the RefDefs that have the given RefConstrs
    let unifyRefConstrs
        // @TODO: hmm this keyOpt isn't actually used in all cases; and that's because this function is actually the wrong place to both add and edit things in the Acc. I think we probably want to get rid of this function eventually and replace it with a simple function that can handle being given RefConstrs to add/unify into the Acc, and then just sub-unifies the entries based on the return information from `getRefConstrAddOrUnifyInfo`.
        (keyOpt : AccumulatorTypeId option)
        (newRefDefResOpt : Result<RefDefType, AccTypeError> option)
        (refConstrs : RefConstr set)
        (acc : Accumulator)
        : AccAndTypeId =
        let newKey =
            match keyOpt with
            | Some key -> key
            | None -> makeAccTypeId ()

        let firstPassResult = getRefConstrAddOrUnifyInfo refConstrs acc

        match firstPassResult with
        | NotCurrentlyInAcc ->
            // Add the refConstrs to the Acc

            { acc with
                refConstraintsMap =
                    acc.refConstraintsMap
                    |> Map.add newKey (newRefDefResOpt, refConstrs) }
            |> Aati.make newKey

        | InOneEntry (accId, combinedRefConstrs) ->
            // Add the refConstrs to this accId's item in the Acc

            let replacedAcc =
                Accumulator.replaceEntry accId (fun _ refDefResOpt _ -> refDefResOpt, combinedRefConstrs) acc
                |> snd

            match newRefDefResOpt with
            | None -> Aati.make accId replacedAcc

            | Some newRefDefRes ->
                let newKey', accWithRefDefAdded =
                    Accumulator.addRefDefResOpt (Some newRefDefRes) replacedAcc

                let unificationResult = unifyTwoAccTypeIds accId newKey' accWithRefDefAdded

                unificationResult

        | InMultipleEntries (accIds, allUnifiedRefConstrs) ->
            // Merge all the RefDefs at the given IDs and insert the full unified RefConstrs into its slot in the Acc

            let accWithNewItemAdded =
                { acc with
                    refConstraintsMap =
                        acc.refConstraintsMap
                        |> Map.add newKey (newRefDefResOpt, allUnifiedRefConstrs) }

            let unifiedResult = unifyAccIdsTom accIds accWithNewItemAdded

            let unifiedRealId, (unifiedRefDef, _) =
                Accumulator.getRealIdAndType unifiedResult.typeId unifiedResult.acc

            let accWithRefConstrsReplaced =
                { unifiedResult.acc with
                    refConstraintsMap =
                        unifiedResult.acc.refConstraintsMap
                        |> Map.add unifiedRealId (unifiedRefDef, allUnifiedRefConstrs) }

            accWithRefConstrsReplaced
            |> Aati.make unifiedRealId





    /// This adds a single extra RefDef constraint onto an existing entry in the Acc
    let addRefDefConstraintForAccId
        (refDefResOpt : Result<RefDefType, AccTypeError> option)
        (accId : AccumulatorTypeId)
        (acc : Accumulator)
        : AccAndTypeId =
        let newKey = makeAccTypeId ()

        /// It's not the most efficient way to do it to add a whole new AccId just so we have something to point `unifyTypeConstraintIds` to, but it works and if we really care we can make it more efficient later
        let accWithRefDefAdded =
            { acc with
                refConstraintsMap =
                    acc.refConstraintsMap
                    |> Map.add newKey (refDefResOpt, Set.empty) }

        accWithRefDefAdded
        |> unifyTwoAccTypeIds newKey accId





    /// Adds a new RefDef (without any accompanying reference constraints) into the map
    let addRefDefResOpt (refDefResOpt : Result<RefDefType, AccTypeError> option) (acc : Accumulator) =
        addRefDefResOptWithRefConstrs refDefResOpt Set.empty acc











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

            let result =
                addRefDefResOptWithRefConstrs (makeOkType arrowType) Set.empty fromAndToAcc

            result

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

            unifyTwoAccTypeIds defTypeAcc.typeId withRefConstrsAdded.typeId combinedAcc


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
        combine result.acc acc |> Aati.make result.typeId


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
module TC = TypeConstraints








(*

    Helpers for function types and record dotting

*)


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







(*
    Get Accumulator and type from expressions
*)

let rec getAccumulatorFromExpr (expr : T.Expression) : AccAndTypeId =

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





        | T.LetExpression (declarations, expr') ->
            let bodyExpr = getAccumulatorFromExpr expr'

            let typedDeclarations =
                declarations
                |> NEL.map (fun binding ->
                    let bindingAccAndSelf = getAccumulatorFromBinding binding
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

                let boolRefDef = RefDtPrimitiveType BuiltInPrimitiveTypes.Bool

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



//and getAccumulatorFromParam (param : FunctionOrCaseMatchParam) : AccumulatorAndOwnType =
and getAccumulatorFromParam (param : AssignmentPattern) : AccAndTypeId =
    /// This *only* gets the inferred type based on the destructuring pattern, not based on usage or anything else.
    let rec getInferredTypeFromAssignmentPattern (pattern : AssignmentPattern) : AccAndTypeId =
        match pattern with
        | Named ident ->
            Accumulator.addRefDefResOptWithRefConstrs
                None
                (Set.singleton (ByValue (LocalLower ident)))
                Accumulator.empty

        | Ignored -> Accumulator.addRefDefResOpt None Accumulator.empty

        | Unit -> Accumulator.addRefDefResOpt (Some (Ok RefDtUnitType)) Accumulator.empty

        | DestructuredPattern destructured -> getInferredTypeFromDestructuredPattern destructured

        | Aliased (pattern_, alias) ->
            let nestedAccAndType = getInferredTypeFromAssignmentPattern pattern_

            let withNameAdded =
                Accumulator.addRefDefResOptWithRefConstrs
                    None
                    (Set.singleton (ByValue (LocalLower alias)))
                    nestedAccAndType.acc

            Accumulator.unifyTwoAccTypeIds nestedAccAndType.typeId withNameAdded.typeId withNameAdded.acc


    and getInferredTypeFromDestructuredPattern (pattern : DestructuredPattern) : AccAndTypeId =
        match pattern with
        | DestructuredRecord fieldNames ->
            let fields =
                fieldNames
                |> NEL.map (fun recFieldName ->
                    recFieldName,
                    Accumulator.addRefDefResOptWithRefConstrs
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
                Accumulator.addRefDefResOptWithRefConstrs None (Set.singleton ctorType) combinedAcc

            | head :: tail ->
                // I.e. there are params

                /// @TODO: I'm not 100% sure that this is the best way to do this, or if there is actually a more consistent way to specify what the relationship of the constructor to the params should be.
                /// E.g. one thing which `makeAccIdFuncApplicationType` does *not* capture is the fact that these are not just *some* parameters, but they need to be *all* of the parameters for that type variant. Otherwise should be a type error.
                let withFuncRequirement =
                    makeAccIdFuncApplicationType (NEL.new_ head tail) combinedAcc

                Accumulator.combine combinedAcc withFuncRequirement.acc
                |> Accumulator.addRefDefResOptWithRefConstrs None (Set.singleton ctorType)



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

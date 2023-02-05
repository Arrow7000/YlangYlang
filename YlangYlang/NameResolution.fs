module NameResolution

open Lexer
open ConcreteSyntaxTree


/// A reference to either a real concrete expression or an assignment parameter
type Reference =
    | RealExpression of Expression
    | AssignmentParam of AssignmentPattern


/// Supports shadowing
type ResolvedValueNames = Map<UnqualValueIdentifier, CstNode<Reference> nel>

let addNewReference ident newValue (map : ResolvedValueNames) =
    Map.change
        ident
        (function
        | Some oldValue -> Some (NEL.cons newValue oldValue)
        | None -> Some (NEL.make newValue))
        map

//let addMultipleReferences params_ map =
//    params_
//        |> NEL.fold<ResolvedValueNames, AssignmentPattern>
//            (fun map' pattern -> resolveAssignmentPattern pattern map')
//                map

let makeAssignmentParam pattern =
    makeCstNode (AssignmentParam pattern.node) pattern.source


let throwNotImplementedYet _ = failwithf "Not implemented yet!"



let rec addMultipleAssignmentPatterns (params_ : NEL<CstNode<AssignmentPattern>>) map =
    NEL.fold<ResolvedValueNames, CstNode<AssignmentPattern>>
        (fun mapState patternCst -> resolveAssignmentPattern patternCst mapState)
        map
        params_


and resolveExpression expr map =
    match expr with
    | ParensedExpression expr' -> resolveExpression expr' map
    | SingleValueExpression singleValExpr -> resolveSingleValExpression singleValExpr
    //| CompoundExpression compoundExpr -> resolveCompoundExpression compoundExpr
    | CompoundExpression compoundExpr -> throwNotImplementedYet compoundExpr


and resolveSingleValExpression singleValExpr =
    match singleValExpr with
    | ExplicitValue explicitVal -> throwNotImplementedYet ()

    //| Identifier
    //| LetExpression
    //| ControlFlowExpression
    | _ -> throwNotImplementedYet ()

and resolveExplicitValue explicitVal map =
    match explicitVal with
    | Primitive _ -> map
    | CustomTypeVariant _ -> map
    | DotGetter _ -> map
    | Function { params_ = params_; body = body } ->
        let paramsMap = addMultipleAssignmentPatterns params_ map

        resolveExpression body.node paramsMap


and resolveAssignmentPattern
    ({ node = assignmentPattern
       source = source } as cstNode)
    map
    =
    match assignmentPattern with
    | Named ident as namedIdent -> addNewReference ident (makeCstNode (AssignmentParam namedIdent) source) map
    | Ignored -> map
    | AssignmentPattern.Unit -> map
    | Aliased (alias = alias; pattern = pattern) ->
        let newMap = addNewReference alias.node (makeAssignmentParam pattern) map

        resolveAssignmentPattern pattern newMap

    | DestructuredPattern pattern ->
        match pattern with
        | DestructuredRecord fieldNames -> List.fold (fun fieldName -> addNewReference) map fieldNames

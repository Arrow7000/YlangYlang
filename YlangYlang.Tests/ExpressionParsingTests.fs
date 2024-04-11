module ExpressionParsingTests

open Expecto
open Lexer
open SyntaxTree
//open ConcreteSyntaxTree
open Parser
open ExpressionParsing
open System.Diagnostics


/// So that we don't have to reproduce the contextStack implementation details before we actuals with expecteds
//let private stripContexts (ctx : ParseContext<'token, 'ctx, 'err>) = { ctx with contextStack = List.empty }
let private stripContexts result =
    { result with
        parsingContext =
            { result.parsingContext with
                contextStack = List.empty } }

let private makeSuccess tokensParsed v =
    blankParseCtx
    |> makeParseResultWithCtx (ParsingSuccess v)
    |> fun result ->
        { result with
            parsingContext =
                { result.parsingContext with
                    prevTokens = tokensParsed } }



let makeBlankCstNode node = makeCstNode node List.empty
let stripTokens (cstNode : CstNode<'a>) = { cstNode with source = List.empty }




let rec stripTokensFromExpr (expr : Expression) =
    let mapAndStrip f = mapNode f >> stripTokens
    let mapAndStripExpr = mapAndStrip stripTokensFromExpr >> stripTokens

    let rec stripAssignmentPattern pattern =
        match pattern with
        | Named i -> Named i
        | Ignored -> Ignored
        | Unit -> Unit
        | DestructuredPattern des ->
            (match des with
             | DestructuredRecord fields -> NEL.map stripTokens fields |> DestructuredRecord
             | DestructuredTuple fields -> TOM.map (mapAndStrip stripAssignmentPattern) fields |> DestructuredTuple
             | DestructuredCons fields -> TOM.map (mapAndStrip stripAssignmentPattern) fields |> DestructuredCons
             | DestructuredTypeVariant (ctor, params_) ->
                 DestructuredTypeVariant (stripTokens ctor, List.map (mapAndStrip stripAssignmentPattern) params_))
            |> DestructuredPattern
        | Aliased (p, alias) -> Aliased (mapAndStrip stripAssignmentPattern p, stripTokens alias)

    match expr with
    | Primitive prim -> Primitive prim
    | List l -> List.map mapAndStripExpr l |> List
    | Tuple l -> TOM.map mapAndStripExpr l |> Tuple
    | Record l -> List.map (Tuple.mapBoth stripTokens mapAndStripExpr) l |> Record
    | RecordExtension (e, l) -> RecordExtension (stripTokens e, NEL.map (Tuple.mapBoth stripTokens mapAndStripExpr) l)

    | Function f ->
        Function
            { params_ = NEL.map stripTokens f.params_
              body = mapAndStripExpr f.body }
    | DotGetter field -> DotGetter field
    | UpperIdentifier i -> UpperIdentifier i
    | LowerIdentifier i -> LowerIdentifier i
    | LetExpression (b, inExpr) ->
        let bindings =
            b
            |> NEL.map (
                mapAndStrip (fun binding ->
                    { bindPattern = mapAndStrip stripAssignmentPattern binding.bindPattern
                      value = mapAndStripExpr binding.value })
            )

        LetExpression (bindings, mapAndStripExpr inExpr)
    | IfExpression (cond, ifTrue, ifFalse) ->
        IfExpression (mapAndStripExpr cond, mapAndStripExpr ifTrue, mapAndStripExpr ifFalse)
    | CaseMatch (matchExpr, branches) ->
        CaseMatch (
            mapAndStripExpr matchExpr,
            branches
            |> NEL.map (fun (ptrn, expr_) -> mapAndStrip stripAssignmentPattern ptrn, mapAndStripExpr expr_)
        )
    | Operator (left, opSeq) ->
        Operator (mapAndStripExpr left, opSeq |> NEL.map (fun (op, exp) -> stripTokens op, mapAndStripExpr exp))
    | FunctionApplication (funcExpr, params_) ->
        FunctionApplication (mapAndStripExpr funcExpr, NEL.map mapAndStripExpr params_)
    | DotAccess (exp, dotSeq) -> DotAccess (mapAndStripExpr exp, stripTokens dotSeq)
    | ParensedExpression exp -> stripTokensFromExpr exp |> ParensedExpression









[<Tests>]
let testSimpleExpression =
    (fun _ ->
        tokeniseString "-4.6"
        |> Result.map (run (parseDelimExpressions |> Parser.map stripTokensFromExpr))
        |> flip Expect.wantOk "Should succeed"
        |> fun res ->
            Expect.equal
                res.parseResult
                (ParsingSuccess (Primitive (FloatLiteral -4.6)))
                "Parse single value expression")
    |> testCase "Parse single value expression"



[<Tests>]
let testOperatorExpression =
    (fun _ ->
        let tokens = tokeniseString "-4.6  ++ \"test\""

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run (parseCompoundExpressions |> Parser.map stripTokensFromExpr))
            |> fun (tokens', res') ->
                Expect.equal
                    (stripContexts res')
                    (Operator (
                        Primitive (FloatLiteral -4.6) |> makeBlankCstNode,
                        NEL.make (
                            makeBlankCstNode (BuiltInOp AppendOp),
                            makeBlankCstNode ((Primitive (StringPrimitive "test")))
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse operator expression")
    |> testCase "Parse operator expression"


[<Tests>]
let testParensExpressionWithSimpleExpressions =
    (fun _ ->
        let tokens = tokeniseString "(  34) "

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (Parser.run (parseExpression |> Parser.map stripTokensFromExpr))
            |> fun (tokens', res') ->
                Expect.equal
                    res'.parseResult
                    (ParsingSuccess (ParensedExpression (Primitive (IntLiteral 34))))
                    "Parse parenthesised simple expression")
    |> testCase "Parse parenthesised simple expression"

[<Tests>]
let testNestedParensExpressionWithSimpleExpression =
    (fun _ ->
        let tokens = tokeniseString "( (  34) ) "

        tokens
        |> Result.map (Parser.run (parseExpression |> Parser.map stripTokensFromExpr))
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> fun res ->
                Expect.equal
                    res.parseResult
                    (ParsingSuccess (ParensedExpression (ParensedExpression (Primitive (IntLiteral 34)))))
                    "Parse nested parenthesised simple expression")
    |> testCase "Parse nested parenthesised simple expression"

[<Tests>]
let testCompoundExpression =
    (fun _ ->
        let tokens = tokeniseString "(  34 + -4.6   )"

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run (parseCompoundExpressions |> Parser.map stripTokensFromExpr))
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (
                        Operator (
                            makeBlankCstNode (Primitive (IntLiteral 34)),
                            NEL.make (
                                makeBlankCstNode (BuiltInOp PlusOp),
                                makeBlankCstNode (Primitive (FloatLiteral -4.6))
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse parenthesised single operator expression")
    |> testCase "Parse parenthesised single operator expression"

[<Tests>]
let testParensExpressionWithMultiOperators =
    (fun _ ->
        let tokens = tokeniseString "(  34 + -4.6 / 7 )"

        tokens
        |> fun res ->
            Expect.wantOk res "Should succeed"
            |> split (run (parseCompoundExpressions |> Parser.map stripTokensFromExpr))
            |> fun (tokens', res') ->

                Expect.equal
                    (stripContexts res')
                    (ParensedExpression (

                        Operator (
                            makeBlankCstNode (Primitive (IntLiteral 34)),
                            NEL.make (
                                makeBlankCstNode (BuiltInOp PlusOp),
                                makeBlankCstNode (
                                    Operator (
                                        makeBlankCstNode (Primitive (FloatLiteral -4.6)),
                                        NEL.make (
                                            makeBlankCstNode (BuiltInOp DivOp),
                                            makeBlankCstNode (Primitive (IntLiteral 7))

                                        )
                                    )
                                )
                            )
                        )
                     )
                     |> makeSuccess tokens')
                    "Parse parenthesised expression")
    |> testCase "Parse parenthesised expression"

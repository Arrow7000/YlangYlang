module DummyLangTests


open Expecto


open DummyLang
open DummyLang.AbstractSyntaxTree

module AST = DummyLang.AbstractSyntaxTree

open QualifiedSyntaxTree.Names
open FsToolkit.ErrorHandling

module Sacuv = DummyLang.SelfAndConstrainedUnificationVars


let private makePolyType typeContents =
    { forall = List.empty
      typeExpr = typeContents }



let private makePolyTypeWith typeVars typeContents =
    { forall = List.ofSeq typeVars
      typeExpr = typeContents }



[<Tests>]
let testTypeInference () =
    testList
        "Test type inference for the dummy language"
        [ testTheory "Infer the type of some primitive literals" [ str "hello", Types.strType; int 42, Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              let expectedType = result.self |> Result.map _.typeExpr

              Expect.equal expectedType (Ok type_) (sprintf "Expected %A but got %A" type_ expectedType)

          testTheory
              "Infer the type of more complex expressions with substitutions"
              [ apply (lambda "bla" (int 43)) (str "bloo"), makePolyType Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              let expectedType = result.self

              Expect.equal expectedType (Ok type_) (sprintf "Expected %A but got %A" type_ expectedType)







          test "Unify two polytypes" {
              let makeTypeVar () = TypeVariableId (System.Guid.NewGuid ())

              let typeVar1 = makeTypeVar ()
              let typeVar2 = makeTypeVar ()

              let tuple1 =
                  Types.tupleTypeOf (makePolyTypeWith [ typeVar1 ] (TypeVariable typeVar1)) (makePolyType Types.strType)

              let tuple2 =
                  Types.tupleTypeOf (makePolyType Types.intType) (makePolyTypeWith [ typeVar2 ] (TypeVariable typeVar2))

              let result = TypeInference.unifyTwoTypes tuple1 tuple2

              let expected =
                  Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType)
                  |> Ok

              Expect.equal
                  result.self
                  expected
                  "Two tuple types with concrete types in one slot and type vars in the other unify into a tuple with both slots concretised"
          }



          testTheory
              "Let polymorphism & other adventures"
              [ """
                let
                  makeTuple a = (a, 7)
                in
                makeTuple "bla" : (String, Int)
                """,
                letBindings
                    (NEL.make (letBinding "makeTuple" None (lambda "a" (tuple (name "a") (int 7)))))
                    (apply (name "makeTuple") (str "bla")),
                Types.tupleTypeOf (makePolyType Types.strType) (makePolyType Types.intType)
                """
                let
                  makeList a = [a]
                in
                makeList "bla" : List String
                """,
                letBindings
                    (NEL.make (letBinding "makeList" None (lambda "a" (list [ name "a" ]))))
                    (apply (name "makeList") (str "bla")),
                Types.listTypeOf (makePolyType Types.strType)

                """
                let
                  makeIntList b = [0, b]
                in
                makeIntList : Int -> List Int
                """,
                letBindings
                    (NEL.make (letBinding "makeIntList" None (lambda "b" (list [ int 0; name "b" ]))))
                    (name "makeIntList"),
                Types.funcTypeOf (makePolyType Types.intType) (Types.listTypeOf (makePolyType Types.intType))

                """
                let
                  identity x = x
                in
                identity 7 : Int
                """,
                letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (apply (name "identity") (int 7)),
                makePolyType Types.intType

                """
                let
                  identity x = x
                in
                identity "blabla" : String
                """,
                letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (apply (name "identity") (str "blabla")),
                makePolyType Types.strType

                """
                let
                  identity x = x
                in
                (identity 7, identity "blabla") : (Int, String)
                """,
                letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (tuple (apply (name "identity") (int 7)) (apply (name "identity") (str "blabla"))),
                Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType) ]
          <| fun (msg, expr, expectedType) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              Expect.equal result.self (Ok expectedType) msg

          test "Test recursive definition" {
              (*

              let
                factorial n =
                  if n <= 0 then 1 else n * factorial (n - 1)
              in factorial 5 : Int

              *)

              let factorial : Expr =
                  letBindings
                      (NEL.make (
                          letBinding
                              "factorial"
                              None
                              (lambda
                                  "n"
                                  (ifThenElse
                                      (infixOp (LowerIdent "<=") (name "n") (int 0))
                                      (int 1)
                                      (infixOp
                                          (LowerIdent "*")
                                          (name "n")
                                          (apply (name "factorial") (infixOp (LowerIdent "-") (name "n") (int 1))))))
                      ))
                      (apply (name "factorial") (int 5))

              let mult =
                  LowerIdent "*",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)

              let minus =
                  LowerIdent "-",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)

              let lte =
                  LowerIdent "<=",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.boolType)

              let namesMap : TypedNamesMap =
                  [ mult; minus; lte ] |> List.map (Tuple.mapFst LocalLower) |> Map.ofList

              let result = TypeInference.inferTypeFromExpr namesMap factorial

              Expect.equal
                  result.self
                  (Ok <| Types.makeEmptyPolyType Types.intType)
                  "Factorial expression should have type Int"
          }

          test "Test mutually recursive functions" {
              (*

              let
                isEven n =
                  if n == 0 then true else isOdd (n - 1)

                isOdd n =
                  if n == 0 then false else isEven (n - 1)

              in isEven 5 : Int

              *)

              let factorial : Expr =
                  letBindings
                      (NEL.new_
                          (letBinding
                              "isEven"
                              None
                              (lambda
                                  "n"
                                  (ifThenElse
                                      (infixOp (LowerIdent "==") (name "n") (int 0))
                                      (name "true")
                                      (apply (name "isOdd") (infixOp (LowerIdent "-") (name "n") (int 1))))))
                          [ letBinding
                                "isOdd"
                                None
                                (lambda
                                    "n"
                                    (ifThenElse
                                        (infixOp (LowerIdent "==") (name "n") (int 0))
                                        (name "false")
                                        (apply (name "isEven") (infixOp (LowerIdent "-") (name "n") (int 1))))) ])
                      (apply (name "isEven") (int 5))

              let minus =
                  LowerIdent "-",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)

              let eq =
                  LowerIdent "==",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.boolType)

              let true_ = LowerIdent "true", makePolyType Types.boolType
              let false_ = LowerIdent "false", makePolyType Types.boolType

              let namesMap : TypedNamesMap =
                  [ minus; eq; true_; false_ ] |> List.map (Tuple.mapFst LocalLower) |> Map.ofList

              let result = TypeInference.inferTypeFromExpr namesMap factorial

              Expect.equal
                  result.self
                  (Ok <| Types.makeEmptyPolyType Types.boolType)
                  "Mutually recursive functions should have type Bool"
          }

          test "Infer the type of a function application in steps" {

              let result =
                  result {
                      let identityFunc = lambda "x" (name "x")

                      let! identityFuncType =
                          TypeInference.inferTypeFromExpr Map.empty identityFunc |> Sacuv.sequenceResult

                      let appliedToInt = apply identityFunc (int 7)


                      let appliedToIntType =
                          TypeInference.inferTypeFromExpr
                              (Map.singleton (LocalLower (LowerIdent "identity")) identityFuncType.self)
                              appliedToInt

                      let appliedToStr = apply identityFunc (str "blabla")

                      let appliedToStrType =
                          TypeInference.inferTypeFromExpr
                              (Map.singleton (LocalLower (LowerIdent "identity")) identityFuncType.self)
                              appliedToStr

                      let appliedToTuple = apply identityFunc (tuple (int 7) (str "blabla"))

                      let! appliedToTupleType =
                          TypeInference.inferTypeFromExpr
                              (Map.singleton (LocalLower (LowerIdent "identity")) identityFuncType.self)
                              appliedToTuple
                          |> Sacuv.sequenceResult


                      return appliedToTupleType.self
                  }

              Expect.equal
                  result
                  (Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType)
                   |> Ok)
                  "Expected a tuple type"

          }

          ]

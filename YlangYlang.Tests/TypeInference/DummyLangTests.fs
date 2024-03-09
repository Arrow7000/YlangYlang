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

let private mono = makePolyType

let private makePolyTypeWith typeVars typeContents =
    { forall = List.ofSeq typeVars
      typeExpr = typeContents }

let private makeParametricTypeFromStr str = Types.makeParametricType (LocalUpper (UpperIdent str))




[<Tests>]
let testTypeInference () =
    testList
        "Test type inference for the dummy language"
        [ testTheory "Infer the type of some primitive literals" [ str "hello", Types.strType; int 42, Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Ctx.empty expr
              let expectedType = result.self |> Result.map _.typeExpr

              Expect.equal expectedType (Ok type_) (sprintf "Expected %A but got %A" type_ expectedType)

          testTheory
              "Infer the type of more complex expressions with substitutions"
              [ apply (lambda "bla" (int 43)) (str "bloo"), makePolyType Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Ctx.empty expr
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
                  result.unified
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
              let result = TypeInference.inferTypeFromExpr Ctx.empty expr
              Expect.equal result.self (Ok expectedType) msg


          test "Test let polymorphism with types that still have some polymorphic slots open" {
              (*
            
              let
                maybe = none
              
                strList = ["hi", maybe]
              
                intList = [9, maybe]

              in (strList, intList) : (List (Maybe String), List (Maybe Int))
              
              *)
              let maybeTypeParam1 = TypeVariableId (System.Guid.NewGuid ())
              let maybeTypeParam2 = TypeVariableId (System.Guid.NewGuid ())

              let concreteMaybeType typeParam = makeParametricTypeFromStr "Maybe" [ typeParam ]

              let none =
                  LocalLower (LowerIdent "none"),
                  makePolyTypeWith [ maybeTypeParam1 ] (concreteMaybeType (TypeVariable maybeTypeParam1))
                  |> Ok

              let just =
                  LocalLower (LowerIdent "just"),
                  makePolyTypeWith
                      [ maybeTypeParam2 ]
                      (makeParametricTypeFromStr
                          "Arrow"
                          [ TypeVariable maybeTypeParam2
                            concreteMaybeType (TypeVariable maybeTypeParam2) ])
                  |> Ok

              let namesMap = Map.ofList [ none; just ]

              let expr =
                  letBindings
                      (NEL.new_
                          (letBinding "maybe" None (name "none"))
                          [ letBinding "strList" None (AST.list [ apply (name "just") (AST.str "hi"); name "maybe" ])
                            letBinding "intList" None (AST.list [ apply (name "just") (AST.int 9); name "maybe" ]) ])
                      (tuple (name "strList") (name "intList"))

              let expected =
                  Types.tupleTypeOf
                      (concreteMaybeType Types.strType |> makePolyType |> Types.listTypeOf)
                      (concreteMaybeType Types.intType |> makePolyType |> Types.listTypeOf)


              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      expr

              Expect.equal result.self (Ok expected) "Expected a tuple of List String and List Int"
          }
          test "Test recursive definition" {
              (*

              let
                factorial n =
                  if n <= 0 then 1
                  else n * factorial (n - 1)

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
                  |> Ok

              let minus =
                  LowerIdent "-",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                  |> Ok

              let lte =
                  LowerIdent "<=",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.boolType)
                  |> Ok

              let namesMap : TypedNamesMap =
                  [ mult; minus; lte ] |> List.map (Tuple.mapFst LocalLower) |> Map.ofList

              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      factorial

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

              let minus =
                  LowerIdent "-",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                  |> Ok

              let eq =
                  LowerIdent "==",
                  Types.infixOpTypeOf
                      (makePolyType Types.intType)
                      (makePolyType Types.intType)
                      (makePolyType Types.boolType)
                  |> Ok


              // We need true and false values because DummyLang doesn't currently support type variant literals
              let true_ = LowerIdent "true", makePolyType Types.boolType |> Ok
              let false_ = LowerIdent "false", makePolyType Types.boolType |> Ok

              let namesMap : TypedNamesMap =
                  [ minus; eq; true_; false_ ] |> List.map (Tuple.mapFst LocalLower) |> Map.ofList


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

              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      factorial

              Expect.equal
                  result.self
                  (Ok <| Types.makeEmptyPolyType Types.boolType)
                  "Mutually recursive functions should have type Bool"
          }

          test "Infer the type of a function application in steps" {
              let identityFunc = lambda "x" (name "x")

              let identityFuncType = TypeInference.inferTypeFromExpr Ctx.empty identityFunc

              let appliedToTuple = apply identityFunc (tuple (int 7) (str "blabla"))

              let appliedToTupleType =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = Map.singleton (LocalLower (LowerIdent "identity")) identityFuncType.self }
                      appliedToTuple

              Expect.equal
                  appliedToTupleType.self
                  (Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType)
                   |> Ok)
                  "Expected a tuple type"

          }


          test "Skolemised type cannot work with two different types" {
              (*
              let
                f maybe =
                    let
                        strList = [ just "hi", maybe ]
                        intList = [ just 0, maybe ]
                    in (strList, intList)
              in f (just 9)
              *)
              let typeParam = TypeVariableId (System.Guid.NewGuid ())


              let concreteMaybeType typeParam = makeParametricTypeFromStr "Maybe" [ typeParam ]

              let just =
                  LocalLower (LowerIdent "just"),
                  makePolyTypeWith
                      [ typeParam ]
                      (makeParametricTypeFromStr
                          "Arrow"
                          [ TypeVariable typeParam; concreteMaybeType (TypeVariable typeParam) ])
                  |> Ok

              let namesMap = Map.ofList [ just ]

              let expr =
                  letBindings
                      (NEL.make (
                          letBinding
                              "f"
                              None
                              (lambda
                                  "maybe"
                                  (letBindings
                                      (NEL.new_
                                          (letBinding
                                              "strList"
                                              None
                                              (AST.list [ apply (name "just") (str "hi"); name "maybe" ]))
                                          [ letBinding
                                                "intList"
                                                None
                                                (AST.list [ apply (name "just") (int 0); name "maybe" ]) ])
                                      (tuple (name "strList") (name "intList"))))
                      ))
                      (apply (name "f") (apply (name "just") (int 9)))

              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      expr

              Expect.isError result.self "Skolems can't be polymorphic"
          }
          test "Prevent skolem from escaping" {
              (*
                let
                    f x =
                        let
                            g : (a -> ()) -> ()
                            g h = h x
                        in x
                in (f 10, f "boo")
              *)

              // This case throws an error in the Elm compiler, see https://github.com/elm/compiler/issues/2301
              let arrowTypeExpr from to_ = TypeExpr (Types.arrowTypeName, [ from; to_ ])
              let unitTypeExpr = TypeExpr (Types.unitTypeName, [])

              let typeAnnotation : TypeExpr =
                  arrowTypeExpr (arrowTypeExpr (TypeExpr.Skolem (LowerIdent "a")) unitTypeExpr) unitTypeExpr

              let expr =
                  letBindings
                      (NEL.make (
                          letBinding
                              "f"
                              None
                              (lambda
                                  "x"
                                  (letBindings
                                      (NEL.make (
                                          letBinding
                                              "g"
                                              (Some typeAnnotation)
                                              (lambda "h" (apply (name "h") (name "x")))
                                      ))
                                      (name "x")))
                      ))
                      (tuple (apply (name "f") (int 10)) (apply (name "f") (str "boo")))

              let result = TypeInference.inferTypeFromExpr Ctx.empty expr

              Expect.equal
                  result.self
                  (Ok (Types.tupleTypeOf (mono Types.intType) (mono Types.strType)))
                  "Expected (Int, String)"

              Expect.equal result.constrained Map.empty "Expected no constraints propagated up out of scope"
          } ]

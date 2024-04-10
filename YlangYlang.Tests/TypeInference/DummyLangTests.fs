module DummyLangTests


open Expecto


open DummyLang

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
        [ testTheory
              "Infer the type of some primitive literals"
              [ AST.str "hello", Types.strType; AST.int 42, Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Ctx.empty expr
              let expectedType = result |> Result.map _.typeExpr

              Expect.equal expectedType (Ok type_) (sprintf "Expected %A but got %A" type_ expectedType)

          testTheory
              "Infer the type of more complex expressions with substitutions"
              [ AST.apply (AST.lambda "bla" (AST.int 43)) (AST.str "bloo"), makePolyType Types.intType ]
          <| fun (expr, type_) ->
              let expectedType = TypeInference.inferTypeFromExpr Ctx.empty expr

              Expect.equal expectedType (Ok type_) (sprintf "Expected %A but got %A" type_ expectedType)







          test "Unify two polytypes" {
              let makeTypeVar () = TypeVariableId (System.Guid.NewGuid ())

              let typeVar1 = makeTypeVar ()
              let typeVar2 = makeTypeVar ()

              let tuple1 =
                  Types.tupleTypeOf (makePolyTypeWith [ typeVar1 ] (TypeVariable typeVar1)) (makePolyType Types.strType)

              let tuple2 =
                  Types.tupleTypeOf (makePolyType Types.intType) (makePolyTypeWith [ typeVar2 ] (TypeVariable typeVar2))

              let unified = TypeInference.unifyTwoTypes tuple1 tuple2

              let expected =
                  Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType)
                  |> Ok

              Expect.equal
                  unified
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
                AST.letBindings
                    (NEL.make (AST.letBinding "makeTuple" None (AST.lambda "a" (AST.tuple (AST.name "a") (AST.int 7)))))
                    (AST.apply (AST.name "makeTuple") (AST.str "bla")),
                Types.tupleTypeOf (makePolyType Types.strType) (makePolyType Types.intType)
                """
                let
                  makeList a = [a]
                in
                makeList "bla" : List String
                """,
                AST.letBindings
                    (NEL.make (AST.letBinding "makeList" None (AST.lambda "a" (AST.list [ AST.name "a" ]))))
                    (AST.apply (AST.name "makeList") (AST.str "bla")),
                Types.listTypeOf (makePolyType Types.strType)

                """
                let
                  makeIntList b = [0, b]
                in
                makeIntList : Int -> List Int
                """,
                AST.letBindings
                    (NEL.make (
                        AST.letBinding "makeIntList" None (AST.lambda "b" (AST.list [ AST.int 0; AST.name "b" ]))
                    ))
                    (AST.name "makeIntList"),
                Types.funcTypeOf (makePolyType Types.intType) (Types.listTypeOf (makePolyType Types.intType))

                """
                let
                  identity x = x
                in
                identity 7 : Int
                """,
                AST.letBindings
                    (NEL.make (AST.letBinding "identity" None (AST.lambda "x" (AST.name "x"))))
                    (AST.apply (AST.name "identity") (AST.int 7)),
                makePolyType Types.intType

                """
                let
                  identity x = x
                in
                identity "blabla" : String
                """,
                AST.letBindings
                    (NEL.make (AST.letBinding "identity" None (AST.lambda "x" (AST.name "x"))))
                    (AST.apply (AST.name "identity") (AST.str "blabla")),
                makePolyType Types.strType

                """
                let
                  identity x = x
                in
                (identity 7, identity "blabla") : (Int, String)
                """,
                AST.letBindings
                    (NEL.make (AST.letBinding "identity" None (AST.lambda "x" (AST.name "x"))))
                    (AST.tuple
                        (AST.apply (AST.name "identity") (AST.int 7))
                        (AST.apply (AST.name "identity") (AST.str "blabla"))),
                Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType) ]
          <| fun (msg, expr, expectedType) ->
              let result = TypeInference.inferTypeFromExpr Ctx.empty expr
              Expect.equal result (Ok expectedType) msg


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
                  AST.letBindings
                      (NEL.new_
                          (AST.letBinding "maybe" None (AST.name "none"))
                          [ AST.letBinding
                                "strList"
                                None
                                (AST.list [ AST.apply (AST.name "just") (AST.str "hi"); AST.name "maybe" ])
                            AST.letBinding
                                "intList"
                                None
                                (AST.list [ AST.apply (AST.name "just") (AST.int 9); AST.name "maybe" ]) ])
                      (AST.tuple (AST.name "strList") (AST.name "intList"))

              let expected =
                  Types.tupleTypeOf
                      (concreteMaybeType Types.strType |> makePolyType |> Types.listTypeOf)
                      (concreteMaybeType Types.intType |> makePolyType |> Types.listTypeOf)


              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      expr

              Expect.equal result (Ok expected) "Expected a tuple of List String and List Int"
          }
          test "Test recursive definition" {
              (*

              let
                factorial n =
                  if n <= 0 then 1
                  else n * factorial (n - 1)

              in factorial 5 : Int

              *)

              let factorial : AST.Expr =
                  AST.letBindings
                      (NEL.make (
                          AST.letBinding
                              "factorial"
                              None
                              (AST.lambda
                                  "n"
                                  (AST.ifThenElse
                                      (AST.infixOp (LowerIdent "<=") (AST.name "n") (AST.int 0))
                                      (AST.int 1)
                                      (AST.infixOp
                                          (LowerIdent "*")
                                          (AST.name "n")
                                          (AST.apply
                                              (AST.name "factorial")
                                              (AST.infixOp (LowerIdent "-") (AST.name "n") (AST.int 1))))))
                      ))
                      (AST.apply (AST.name "factorial") (AST.int 5))

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
                  result
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


              let factorial : AST.Expr =
                  AST.letBindings
                      (NEL.new_
                          (AST.letBinding
                              "isEven"
                              None
                              (AST.lambda
                                  "n"
                                  (AST.ifThenElse
                                      (AST.infixOp (LowerIdent "==") (AST.name "n") (AST.int 0))
                                      (AST.name "true")
                                      (AST.apply
                                          (AST.name "isOdd")
                                          (AST.infixOp (LowerIdent "-") (AST.name "n") (AST.int 1))))))
                          [ AST.letBinding
                                "isOdd"
                                None
                                (AST.lambda
                                    "n"
                                    (AST.ifThenElse
                                        (AST.infixOp (LowerIdent "==") (AST.name "n") (AST.int 0))
                                        (AST.name "false")
                                        (AST.apply
                                            (AST.name "isEven")
                                            (AST.infixOp (LowerIdent "-") (AST.name "n") (AST.int 1))))) ])
                      (AST.apply (AST.name "isEven") (AST.int 5))

              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      factorial

              Expect.equal
                  result
                  (Ok <| Types.makeEmptyPolyType Types.boolType)
                  "Mutually recursive functions should have type Bool"
          }

          test "Infer the type of a function application in steps" {
              let identityFunc = AST.lambda "x" (AST.name "x")

              let identityFuncType = TypeInference.inferTypeFromExpr Ctx.empty identityFunc

              let appliedToTuple =
                  AST.apply identityFunc (AST.tuple (AST.int 7) (AST.str "blabla"))

              let appliedToTupleType =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = Map.singleton (LocalLower (LowerIdent "identity")) identityFuncType }
                      appliedToTuple

              Expect.equal
                  appliedToTupleType
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
                  AST.letBindings
                      (NEL.make (
                          AST.letBinding
                              "f"
                              None
                              (AST.lambda
                                  "maybe"
                                  (AST.letBindings
                                      (NEL.new_
                                          (AST.letBinding
                                              "strList"
                                              None
                                              (AST.list [ AST.apply (AST.name "just") (AST.str "hi"); AST.name "maybe" ]))
                                          [ AST.letBinding
                                                "intList"
                                                None
                                                (AST.list [ AST.apply (AST.name "just") (AST.int 0); AST.name "maybe" ]) ])
                                      (AST.tuple (AST.name "strList") (AST.name "intList"))))
                      ))
                      (AST.apply (AST.name "f") (AST.apply (AST.name "just") (AST.int 9)))

              let result =
                  TypeInference.inferTypeFromExpr
                      { Ctx.empty with
                          typedNamesMap = namesMap }
                      expr

              Expect.isError result "Skolems can't be polymorphic"
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
                  AST.letBindings
                      (NEL.make (
                          AST.letBinding
                              "f"
                              None
                              (AST.lambda
                                  "x"
                                  (AST.letBindings
                                      (NEL.make (
                                          AST.letBinding
                                              "g"
                                              (Some typeAnnotation)
                                              (AST.lambda "h" (AST.apply (AST.name "h") (AST.name "x")))
                                      ))
                                      (AST.name "x")))
                      ))
                      (AST.tuple (AST.apply (AST.name "f") (AST.int 10)) (AST.apply (AST.name "f") (AST.str "boo")))

              let result = TypeInference.inferTypeFromExpr Ctx.empty expr

              Expect.equal
                  result
                  (Ok (Types.tupleTypeOf (mono Types.intType) (mono Types.strType)))
                  "Expected (Int, String)"

          //Expect.equal result.constrained Map.empty "Expected no constraints propagated up out of scope"
          }

          test "More specific type signature is allowed" {
              (*
              let
                  f : Int -> Int
                  f x = x
              in f
              *)

              // This case throws an error in the Elm compiler, see https://github.com/elm/compiler/issues/2301
              let arrowTypeExpr from to_ = TypeExpr (Types.arrowTypeName, [ from; to_ ])

              let typeAnnotation : TypeExpr =
                  arrowTypeExpr (TypeExpr (Types.intTypeName, [])) (TypeExpr (Types.intTypeName, []))

              let expr =
                  AST.letBindings
                      (NEL.make (AST.letBinding "f" (Some typeAnnotation) (AST.lambda "x" (AST.name "x"))))
                      (AST.name "f")

              let result = TypeInference.inferTypeFromExpr Ctx.empty expr


              //Expect.equal result.constrained Map.empty "Expected no constraints propagated up out of scope"

              match result with
              | Ok t -> Tests.printfn $"Success {t}"
              | Error e -> Tests.failtest $"Expected {string typeAnnotation} but got {e}"
          } ]

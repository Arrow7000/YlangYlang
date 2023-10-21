module TypeCheckerTests

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module T = TypedSyntaxTree

open TypedSyntaxTree
open TypeChecker
open Errors

module Acc = Accumulator
module Aati = Acc.AccAndTypeId


open Expecto


open TypeInferTestHelpers
open TypeInferTestHelpers.TypeDsl








[<Tests>]
let typeCheckThings =
    testList
        "Type check some things"
        [ testList
              "Test function and record dotting helpers"
              [ test "Correctly infers type of params based on type IDs" {

                    let id1 : RefConstr = v "1"
                    let id2 : RefConstr = v "2"
                    let id3 : RefConstr = v "3"
                    let id4 : RefConstr = v "4"

                    let tc : TypeConstraints =
                        arrowChain [ defCstrs unit [ id1 ]
                                     defCstrs (list (def s)) [ id2 ]
                                     cstr id3
                                     defCstrs (tuple [ def s; list (def s) |> def ]) [ id4 ] ]
                        |> def

                    let processedTc : Acc.AccAndTypeId = Acc.convertTypeConstraints tc

                    let accId1 =
                        Acc.getAccIdByRefConstr id1 processedTc.acc
                        |> Option.get

                    let accId2 =
                        Acc.getAccIdByRefConstr id2 processedTc.acc
                        |> Option.get

                    let accId3 =
                        Acc.getAccIdByRefConstr id3 processedTc.acc
                        |> Option.get

                    let accId4 =
                        Acc.getAccIdByRefConstr id4 processedTc.acc
                        |> Option.get


                    let result : Acc.AccAndTypeId =
                        makeAccIdDestType (NEL.new_ accId1 [ accId2; accId3; accId4 ]) processedTc.acc

                    let resultRefDef, _ = Accumulator.getTypeById result.typeId result.acc

                    let convertedToConcrete : Result<ConcreteOrGeneric, AccTypeError> =
                        Acc.convertRefDefResOptToConcrete resultRefDef result.acc

                    let conc = Concrete

                    let str = ConcretePrimitiveType String |> conc
                    let listOfStr = ConcreteList str |> conc

                    let expected =
                        ConcreteArrow (
                            conc ConcreteUnitType,
                            ConcreteArrow (
                                listOfStr,
                                ConcreteArrow (Generic, ConcreteTuple (TOM.make str listOfStr) |> conc)
                                |> conc
                            )
                            |> conc
                        )
                        |> conc
                        |> Ok

                    Expect.equal
                        convertedToConcrete
                        expected
                        "Arrow type signature is parsed correctly from NEL of type IDs"
                }

                test "Correctly infers type of params based on type IDs" {

                    let id1 : RefConstr = v "1"
                    let id2 : RefConstr = v "2"
                    let id3 : RefConstr = v "3"
                    let id4 : RefConstr = v "4"

                    let tc : TypeConstraints =
                        arrowChain [ defCstrs unit [ id1 ]
                                     defCstrs (list (def s)) [ id2 ]
                                     cstr id3
                                     defCstrs (tuple [ def s; list (def s) |> def ]) [ id4 ] ]
                        |> def

                    let processedTc : Acc.AccAndTypeId = Acc.convertTypeConstraints tc

                    let accId1 =
                        Acc.getAccIdByRefConstr id1 processedTc.acc
                        |> Option.get

                    let accId2 =
                        Acc.getAccIdByRefConstr id2 processedTc.acc
                        |> Option.get

                    let accId3 =
                        Acc.getAccIdByRefConstr id3 processedTc.acc
                        |> Option.get

                    let accId4 =
                        Acc.getAccIdByRefConstr id4 processedTc.acc
                        |> Option.get


                    let result : Acc.AccAndTypeId =
                        makeAccIdDestType (NEL.new_ accId1 [ accId2; accId3; accId4 ]) processedTc.acc

                    let resultRefDef, _ = Accumulator.getTypeById result.typeId result.acc

                    let convertedToConcrete : Result<ConcreteOrGeneric, AccTypeError> =
                        Acc.convertRefDefResOptToConcrete resultRefDef result.acc

                    let conc = Concrete

                    let str = ConcretePrimitiveType String |> conc
                    let listOfStr = ConcreteList str |> conc

                    let expected =
                        ConcreteArrow (
                            conc ConcreteUnitType,
                            ConcreteArrow (
                                listOfStr,
                                ConcreteArrow (Generic, ConcreteTuple (TOM.make str listOfStr) |> conc)
                                |> conc
                            )
                            |> conc
                        )
                        |> conc
                        |> Ok

                    Expect.equal
                        convertedToConcrete
                        expected
                        "Arrow type signature is parsed correctly from NEL of type IDs"



                } ]
          testList
              "Type check primitives"
              [ test "Type check int literal from string" {
                    Expect.equal (getTypeFromElmStr "7") (def i |> Ok) "7 : Int"
                }

                test "Type check bool literal from string" {
                    Expect.equal (getTypeFromElmStr "True ") (def b |> Ok) "True : Bool"
                }

                testTheory
                    "Type check a variety of correct cases"
                    [ " [1,2,3,6]", list (def i), "List Int"

                      "{ test = \"boo\", weee = 8.45}",
                      recExact [ kv "test" (def s)
                                 kv "weee" (def f) ],
                      "{ test: String, weee : Float }" ]
                <| fun (str, defType, description) ->
                    Expect.equal (getTypeFromElmStr str) (def defType |> Ok) description ]



          testList
              "Infer invariants of functions"
              [ testCase "Simple generic identity function"
                <| fun () ->
                    let str =
                        """
                        let
                            identity a = a
                        in
                        (identity 1, identity "hi")
                        """ in

                    let exprType = getTypeFromElmStr str

                    Expect.equal
                        exprType
                        (tuple [ def i; def s ] |> def |> Ok)
                        "Generic func applied to two things results in those two things"

                testCase "Function with destructured params applied to param"
                <| fun () ->
                    let str =
                        """
                        let
                            getTestFieldOfFirstParam {test} () (first,_) =
                                test
                        in getTestFieldOfFirstParam { test = { inner = "hullo" } } () (1,2)
                        """ in

                    let exprType = getTypeFromElmStr str

                    Expect.equal
                        exprType
                        (recExact [ kv "inner" (def s) ] |> def |> Ok)
                        "Lambda expression with some destructured params returns one of its destructured fields's types" ]

          testList
              "Ensure constrained and inferred types of names work correctly"
              [ testCase "Simple function application"
                <| fun () ->
                    Expect.equal
                        (getTypeFromElmStr "f x")
                        (defCstrs (arrow (cstr (v "x")) none) [ v "f" ]
                         |> Ok)
                        "f x => f : x -> _"

                testCase "Function applied to itself"
                <| fun () ->
                    Expect.equal
                        (getTypeFromElmStr "f f")
                        (defCstrs (arrow (cstrs [ v "f" ]) none) [ v "f" ]
                         |> Ok)
                        "f f => f : f -> _"

                testCase "Function applied to primitive literals"
                <| fun () ->
                    Expect.equal
                        (getTypeFromElmStr "f 'a' \"xyz\" 123 p ")
                        (defCstrs
                            (arrowChain [ def c
                                          def s
                                          def i
                                          cstr (v "p")
                                          none ])
                            [ v "f" ]
                         |> Ok)
                        "f 'a' \"xyz\" 123 p => f : Char -> String -> Int -> _"

                ptestCase "Function applied to primitive, named value, and itself"
                // @TODO: so this keeps crashing with a stack overflow – I think almost certainly because it gets stuck in infinite recursion trying to resolve f in terms of f. Maybe.
                // Which means to fix this I'm going to have to tackle recursive type dependencies!
                // Although I should add some more tests specifically for resolving recursive type deps so we have more than just this one case to test that sticky situation.
                <| fun () ->
                    Expect.equal
                        (getTypeFromElmStr "f 1 (f 2 p)")
                        (defCstrs
                            (arrowChain [ def i
                                          defCstrs (arrowChain [ def i; cstr (v "p"); none ]) [ v "f" ]
                                          none ])
                            [ v "f" ]
                         |> Ok)
                        "f 1 (f 2 p) => f : Int -> p -> p"

                testCase "Record update expression"
                <| fun () ->
                    Expect.equal
                        (getTypeFromElmStr "{ r | field1 = 7, field2 = True }")
                        (defCstrs
                            (recWith [ kv "field1" (def i)
                                       kv "field2" (def b) ])
                            [ v "r" ]
                         |> Ok)
                        "{ r | field1 = 7, field2 = True } => r : { _ | field1 : Int, field2 : Bool }" ]


          testCase "Infer param type from destructuring and return part of that record param"
          <| fun () ->
              Expect.equal
                  (getTypeFromElmStr "\({ hi, there }) -> there")
                  (defCstrs
                      (arrow
                          (def (
                              recWith [ kv "hi" none
                                        kv "there" none ]
                          ))
                          none)
                      []
                   |> Ok)
                  ""

          testList
              "Unify types and type judgments"
              [

                testList
                    "Unify definitive types"
                    [ testCase ""
                      <| fun () ->
                          let expr =
                              """
                                let
                                    g = f a
                                in
                                g b
                                """

                          let typedExpr = getTypedExprFromElmStr expr

                          let typeOfExpr =
                              typedExpr
                              |> Result.bind (getType >> Result.mapError TypeError)

                          let acc =
                              typedExpr
                              |> Result.map (getAccumulatorFromExpr >> Aati.getAcc)

                          let typeConstraint =
                              //arrow (cstr ) (arrow (v "b"|>cstr) (v "b"|>cstr)|> def)
                              //|>def
                              cstr (v "f")


                          //let acc =
                          //    [ set [ v "f" ]
                          //      => Ok (Some (arrow (cstr (v "a")) (any ()))) ]
                          //    |> Map.ofList

                          Expect.equal (getTypeFromElmStr expr) (Ok typeConstraint) "" ]

                testList "Unify type constraints" []

                testList "Unify type judgments" []

                ]

          ]

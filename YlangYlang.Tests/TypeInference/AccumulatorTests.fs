module AccumulatorTests


module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module T = TypedSyntaxTree

open TypedSyntaxTree

module Acc = Accumulator
module Aati = Acc.AccAndTypeId


open Expecto


open TypeInferTestHelpers
open TypeInferTestHelpers.TypeDsl



[<Tests>]
let testAccumulatorLogic =
    testList
        "Test Accumulator stuff"
        [ (let guid1 = makeAccTypeId ()
           let guid2 = makeAccTypeId ()
           let guid3 = makeAccTypeId ()
           let guid4 = makeAccTypeId ()
           let guid5 = makeAccTypeId ()
           let guid6 = makeAccTypeId ()

           let refA = v "a"
           let refB = v "b"
           let refC = v "c"
           let refD = v "d" in

           testList
               "Core unification logic"
               [ test "Unify acc with nothing in common" {
                     let acc =
                         { Acc.empty with
                             refConstraintsMap =
                                 [ guid1, (Ok RefDtUnitType |> Some, Set.empty)
                                   guid2, (None, set [ refB; refC ])
                                   guid3, (RefDtArrow (guid1, guid4) |> Ok |> Some, set [ refD ])
                                   guid4, (None, Set.empty) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTwoAccTypeIds guid2 guid3 acc

                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let guid2Result = Accumulator.getTypeById guid2 unified.acc
                     let guid3Result = Accumulator.getTypeById guid3 unified.acc

                     Expect.equal
                         returnedIdResult
                         guid2Result
                         "The unification result's ID returns the same as the first of the two unified items' IDs"

                     Expect.equal guid2Result guid3Result "Both original IDs link to the same items now"

                     let expectedResult =
                         RefDtArrow (guid1, guid4) |> Ok |> Some, set [ refB; refC; refD ]

                     Expect.equal
                         guid2Result
                         expectedResult
                         "Result has the type of the one with the definitive type but the ref constraints of both"
                 }

                 test "Unify acc with compatible types and narrowing of a type reference: using list" {
                     let acc =
                         { Acc.empty with
                             refConstraintsMap =
                                 [ guid1, (Ok RefDtUnitType |> Some, Set.empty)
                                   guid2, (None, Set.empty)
                                   guid3, (RefDtList guid4 |> Ok |> Some, set [ refD ])
                                   guid4, (None, set [ refA ])
                                   guid5, (RefDtList guid6 |> Ok |> Some, set [ refB; refC ])
                                   guid6, (RefDtPrimType String |> Ok |> Some, Set.empty) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTwoAccTypeIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult = RefDtList toTypeRealId |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedTypeParam = RefDtPrimType String |> Ok |> Some, set [ refA ]

                     Expect.equal
                         returnedIdResult
                         expectedResult
                         "Result has the type of the one with the definitive type but the ref constraints of both"

                     Expect.equal toTypeResult expectedTypeParam "The list's type param is the merger of guids 4 and 6"
                 }


                 test "Unify acc with compatible types and narrowing of a type reference: using arrow" {
                     let acc =
                         { Acc.empty with
                             refConstraintsMap =
                                 [ guid1, (Ok RefDtUnitType |> Some, Set.empty)
                                   guid2, (None, set [ refB; refC ])
                                   guid3, (RefDtArrow (guid1, guid4) |> Ok |> Some, set [ refD ])
                                   guid4, (None, set [ refA ])
                                   guid5, (RefDtArrow (guid1, guid6) |> Ok |> Some, Set.empty)
                                   guid6, (RefDtPrimType String |> Ok |> Some, Set.empty) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTwoAccTypeIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult =
                         RefDtArrow (guid1, toTypeRealId) |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedToType = RefDtPrimType String |> Ok |> Some, set [ refA ]

                     Expect.equal
                         returnedIdResult
                         expectedResult
                         "Result has the type of the one with the definitive type but the ref constraints of both"

                     Expect.equal toTypeResult expectedToType "The arrow's return type is the merger of guids 4 and 6"
                 }

                 test "Unify acc with only RefConstr unifications, triggering one RefDef unification" {
                     let acc =
                         { Acc.empty with
                             refConstraintsMap =
                                 [ guid1, (RefDtList guid3 |> Ok |> Some, set [ refA ])
                                   guid2, (RefDtList guid4 |> Ok |> Some, set [ refB ])
                                   guid3, (RefDtList guid5 |> Ok |> Some, set [ refC ])
                                   guid4, (RefDtList guid6 |> Ok |> Some, set [ refD ])
                                   guid5, (None, set [ refD ])
                                   guid6, (Ok RefDtUnitType |> Some, set [ refD ]) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTwoAccTypeIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult = RefDtList toTypeRealId |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedTypeParam = RefDtPrimType String |> Ok |> Some, set [ refA ]

                     Expect.equal
                         returnedIdResult
                         expectedResult
                         "Result has the type of the one with the definitive type but the ref constraints of both"

                     Expect.equal toTypeResult expectedTypeParam "The list's type param is the merger of guids 4 and 6"
                 }







                 ])


          //test "Simple Acc merge with no unifications needed" {
          //    let guid1 = makeAccTypeId ()
          //    let guid2 = makeAccTypeId ()
          //    let guid3 = makeAccTypeId ()
          //    let guid4 = makeAccTypeId ()


          //    let handMadeAcc1 : Accumulator =
          //        { Acc.empty with
          //            refConstraintsMap =
          //                [

          //                ]
          //                |> Map.ofSeq }

          //    let handMadeAcc2 : Accumulator =
          //        { Acc.empty with
          //            refConstraintsMap =
          //                [

          //                ]
          //                |> Map.ofSeq }

          //    let expected = Acc.empty

          //    let combined = Acc.combine handMadeAcc1 handMadeAcc2


          //    Expect.equal combined expected "Combined Accs is as expected"
          //}


          testTheory
              "Test conversions to and from TypeConstraints"
              // @TODO: add more test cases here to ensure good coverage!
              [ def (arrow (def s) (cstr (v "test")))
                def (
                    recExact [ kv "yo" (def s)
                               kv "cool" (v "thatOtherThing" |> cstr) ]
                ) ]
          <| fun tcToConvert ->
              let converted = Acc.convertTypeConstraints tcToConvert

              let convertedBack = Acc.convertAccIdToTypeConstraints converted.typeId converted.acc

              Expect.equal convertedBack (Ok tcToConvert) "Converting a TC to an Acc and back is consistent"


          ]

module DisjointSetForestTests

//open DisjointSetForest

//open Expecto




//type Items =
//    | A
//    | B
//    | C
//    | D
//    | E
//    | F
//    | G
//    | H
//    | I
//    | J







//[<Tests>]
//let testDisjointSetForest =
//    testList
//        "Disjoint set forests"
//        [ testList
//              "Simple DSF containing only sets"
//              [ testCase "Add disjoint set"
//                <| fun _ ->
//                    let dsf = DSF.init [ A; B; C ] |> DSF.addSet [ D; E; F ]
//                    let resultA = DSF.find A dsf
//                    let resultB = DSF.find B dsf

//                    let resultD = DSF.find D dsf

//                    Expect.isSome resultA "resultA can be found in the DSF"
//                    Expect.isSome resultB "resultB can be found in the DSF"
//                    Expect.isSome resultD "resultD can be found in the DSF"

//                    Expect.equal resultA resultB "A and B are in the same set"
//                    Expect.notEqual resultA resultD "A and D are not in the same set"
//                    Expect.notEqual resultB resultD "B and D are not in the same set"


//                testCase "Union set"
//                <| fun _ ->
//                    let dsf =
//                        DSF.init [ A; B; C ]
//                        |> DSF.addSet [ D; E; F ]
//                        |> DSF.addSet [ H; I; J ]
//                        |> DSF.union A E

//                    let resultA = DSF.find A dsf
//                    let resultD = DSF.find D dsf

//                    let resultH = DSF.find H dsf

//                    Expect.isSome resultA "resultA can be found in the DSF"
//                    Expect.isSome resultD "resultD can be found in the DSF"
//                    Expect.isSome resultH "resultH can be found in the DSF"

//                    Expect.equal resultA resultD "A and D are in the same set"
//                    Expect.notEqual resultA resultH "A and H are not in the same set"
//                    Expect.notEqual resultD resultH "D and H are not in the same set"

//                ]

//          ]


//type Name =
//    | Foo
//    | Bar
//    | Baz
//    | Qux
//    | Corge
//    | Grault
//    | Garply
//    | Waldo
//    | Fred
//    | Plugh
//    | Xyzzy
//    | Thud

///// Simplified version of the Elm type system, for ease of testing
//type SimpleType =
//    | Str
//    | Int
//    | List of TypeOrNamedOrAny
//    | Pair of TypeOrNamedOrAny * TypeOrNamedOrAny



///// Representing a type that's either constrained to be the same type as a particular named value or not constrained at all
//and TypeOrNamedOrAny =
//    | Type of SimpleResult
//    /// For types that are constrained to be the same type as some name
//    | Named of Name
//    /// For types that are not constrained to any name
//    | Any




//and SimpleResult = Result<SimpleType, unit>
//and SimpleResultAndItems = SimpleResult * TypeOrNamedOrAny set



///// Simplified type unification logic to be used in DSFC tests
//let unifySimpleTypes
//    (typeResultA : SimpleResult)
//    (typeResultB : SimpleResult)
//    (dsf : DSFC<Name, SimpleResult>)
//    : SimpleResult * Name seq * DSFC<Name, SimpleResult> =
//    let rec unifyTypes
//        (typeResultA : SimpleResult)
//        (typeResultB : SimpleResult)
//        : SimpleResult * Name seq * DSFC<Name, SimpleResult> =
//        match typeResultA, typeResultB with
//        | Ok typeA, Ok typeB ->
//            match typeA, typeB with
//            | Str, Str -> Ok Str, Seq.empty, dsf
//            | Int, Int -> Ok Int, Seq.empty, dsf
//            | List typeParamA, List typeParamB ->
//                let unifiedNamedsOrAnys, names, dsf = unifyNamedOrAnys typeParamA typeParamB
//                Ok (List unifiedNamedsOrAnys), names, dsf

//            | Pair (fstA, sndA), Pair (fstB, sndB) ->
//                let unifiedNamedsOrAnysFst, namesFst, dsf = unifyNamedOrAnys fstA fstB
//                let unifiedNamedsOrAnysSnd, namesSnd, dsf = unifyNamedOrAnys sndA sndB

//                Ok (Pair (unifiedNamedsOrAnysFst, unifiedNamedsOrAnysSnd)), Seq.append namesFst namesSnd, dsf

//            | _, _ -> Error (), Seq.empty, dsf

//        | Error e, _
//        | _, Error e -> Error e, Seq.empty, dsf

//    and unifyNamedOrAnys
//        (typeParamA : TypeOrNamedOrAny)
//        (typeParamB : TypeOrNamedOrAny)
//        : TypeOrNamedOrAny * Name seq * DSFC<Name, SimpleResult> =
//        match typeParamA, typeParamB with
//        | Any, other
//        | other, Any -> other, Seq.empty, dsf
//        | Named nameA, Named nameB ->
//            // We pick one of the two names, but we bubble up the fact that both these names need to be unified by returning the seq containing both names to the caller
//            Named nameA,
//            (if nameA = nameB then
//                 Seq.empty
//             else
//                 seq {
//                     nameA
//                     nameB
//                 }),
//            dsf

//        | Named name, Type t
//        | Type t, Named name ->
//            let result = DSFC.findData name dsf

//            match result with
//            | None ->
//                let newDsf = DSFC.addSet t [ name ] dsf
//                Type t, Seq.empty, newDsf

//            | Some existingData ->
//                let unifyResult, names, newDsf = unifyTypes t existingData
//                let newNewDsf = DSFC.addSet unifyResult [ name ] newDsf

//                Type unifyResult, names, newNewDsf

//        | Type t1, Type t2 ->
//            let result, names, newDsf = unifyTypes t1 t2
//            Type result, names, newDsf

//    unifyTypes typeResultA typeResultB


//let unifySimpleTypesMany (simpleTypesNel : Result<SimpleType, unit> nel) : SimpleResult * Name seq =
//    let (NEL (head, tail)) = simpleTypesNel

//    tail
//    |> List.fold
//        (fun (combinedTypeResult, names) item ->
//            let newResult, newNames = unifySimpleTypes combinedTypeResult item
//            newResult, Seq.append names newNames)
//        (head, Seq.empty)




//[<Tests>]
//let testSimpleTypeUnification =
//    testList
//        "Unification logic for SimpleTypes"
//        [ testCase "Unify the same primitives"
//          <| fun () ->
//              let unifiedStrs, namesToUnifyForStr = unifySimpleTypes (Ok Str) (Ok Str)
//              Expect.equal unifiedStrs (Ok Str) "Unifying two strings -> string"
//              Expect.equal namesToUnifyForStr Seq.empty "No names to unify for String unification"


//              let unifiedInts, namesToUnifyForInt = unifySimpleTypes (Ok Int) (Ok Int)
//              Expect.equal unifiedInts (Ok Int) "Unifying two Ints -> Int"
//              Expect.equal namesToUnifyForInt Seq.empty "No names to unify for Int unification"


//          testCase "Unify incompatible types"
//          <| fun () ->
//              let intWithStr, _ = unifySimpleTypes (Ok Int) (Ok Str)
//              Expect.equal intWithStr (Error ()) "Int =/= Str"

//              let intWithList, _ = unifySimpleTypes (Ok Int) (Ok (List Any))
//              Expect.equal intWithList (Error ()) "Int =/= List _"

//              let intWithPair, _ = unifySimpleTypes (Ok Int) (Ok (Pair (Named Foo, Any)))
//              Expect.equal intWithPair (Error ()) "Int =/= (foo, _)"


//          testCase "Unify List type with params"
//          <| fun () ->
//              let unifiedType, namesToUnify =
//                  unifySimpleTypes (Ok (List (Named Foo))) (Ok (List Any))

//              Expect.equal unifiedType (Ok (List (Named Foo))) "Narrows to more specific type param"
//              Expect.isEmpty namesToUnify "No names left to unify"

//          testCase "Unify Pair type with params"
//          <| fun () ->
//              let unifiedType, namesToUnify =
//                  unifySimpleTypes (Ok (Pair (Named Foo, Any))) (Ok (Pair (Any, Named Bar)))

//              Expect.equal unifiedType (Ok (Pair (Named Foo, Named Bar))) "Narrows to more specific type param"
//              Expect.isEmpty namesToUnify "No names left to unify"


//          testCase "Unify Pair type with named params"
//          <| fun () ->
//              let unifiedType, namesToUnify =
//                  unifySimpleTypes (Ok (Pair (Named Foo, Any))) (Ok (Pair (Any, Named Bar)))

//              Expect.equal unifiedType (Ok (Pair (Named Foo, Named Bar))) "Narrows to more specific type param"
//              Expect.isEmpty namesToUnify "No names left to unify"


//          testCase "Unify Pair type with multiple named params"
//          <| fun () ->
//              let unifiedType, namesToUnify =
//                  unifySimpleTypes (Ok (Pair (Named Foo, Any))) (Ok (Pair (Named Bar, Any)))

//              Expect.isOk unifiedType "Can be unified"
//              Expect.sequenceEqual (Seq.sort namesToUnify) (Seq.sort [ Foo; Bar ]) "Need to unify two names"

//          ]


//[<Tests>]
//let testDisjointForestSetWithData =
//    testList
//        "DSFs with data"
//        [ testCase "Set union results"
//          <| fun () ->
//              let dsf =
//                  DSFC.init unifySimpleTypesMany [ Foo; Bar ] (Ok (List Any))
//                  |> DSFC.addSet (Ok (List (Named Qux))) [ Bar; Baz ]

//              let firstSetRoot =
//                  Expect.wantSome (DSFC.findSetRoot Foo dsf) "Foo should be in the DSF"

//              let secondSetRoot =
//                  Expect.wantSome (DSFC.findSetRoot Baz dsf) "Baz should be in the DSF"

//              Expect.equal firstSetRoot secondSetRoot "The two sets should be the same now"


//          testCase "Set union results"
//          <| fun () ->
//              let dsf =
//                  DSFC.init unifySimpleTypesMany [ Foo; Bar ] (Ok (List Any))
//                  |> DSFC.addSet (Ok (List (Named Qux))) [ Bar; Baz ]
//                  |> DSFC.addSet (Ok (Pair (Named Corge, Named Bar))) [ Qux ] // I think... this results in an infinite type elaboration. Which, to be clear, may not be an issue for this dummy type system that can't actually expand the names, but ~would be an issue for a real type system, where we'd need to have some sanity checks in place to ensure that such infinitely deep recursive types are not allowed~ COULD be an issue for a real type system. But actually maybe also not. It may only be an issue for the developer because they could construct a type whose only valid *values* would need to be infinitely deep, but maybe that's not something we the language implementers need to care about? idk. It should probably be a warning though.
//              // Where this *wouldn't* be a problem at all though is where the type referenced is a sum type, meaning that even though following some branches leads to infinite depth recursion, actually it *is* possible to create non-infinitely deep values that satisfy the type, so that would be all cool and good.

//              let firstSetRoot =
//                  Expect.wantSome (DSFC.findSetRoot Foo dsf) "Foo should be in the DSF"

//              let secondSetRoot =
//                  Expect.wantSome (DSFC.findSetRoot Baz dsf) "Baz should be in the DSF"

//              Expect.equal firstSetRoot secondSetRoot "The two sets should be the same now" ]

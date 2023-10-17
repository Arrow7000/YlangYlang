module TypeCheckerTests

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module T = TypedSyntaxTree

open TypedSyntaxTree
open TypeChecker
open QualifiedSyntaxTree.Names
open Errors

module Acc = Accumulator
module Aati = AccAndTypeId


open Expecto


let private makeNumberExpression : S.NumberLiteralValue -> Cst.Expression =
    S.NumberPrimitive
    >> S.Primitive
    >> S.ExplicitValue
    >> S.SingleValueExpression

let private getType (expr : T.TypedExpr) : TypeJudgment =
    let result = getAccumulatorFromExpr expr

    Accumulator.convertAccIdToTypeConstraints result.typeId result.acc
    |> Result.map deleteGuidsFromTypeConstraints



/// Lex, parse, type check, and get the typed expression from a string containing an Elm expression!
let private getTypedExprFromElmStr text : Result<TypedExpr, Errors> =
    Lexer.tokeniseString text
    |> Result.mapError LexingError
    |> Result.bind (
        ExpressionParsing.run ExpressionParsing.parseExpression
        >> Parser.toResult
        >> Result.mapError ParsingError
    )
    |> Result.map (typeCheckCstExpression List.empty)



let private getTypeFromElmStr text : Result<TypeConstraints, Errors> =
    getTypedExprFromElmStr text
    |> Result.bind (getType >> Result.mapError TypeError)


let private getAccFromElmStr text : Result<Accumulator, Errors> =
    getTypedExprFromElmStr text
    |> Result.map (getAccumulatorFromExpr >> Aati.getAcc)






module TypeDsl =
    (* Helper functions *)

    /// Make a list of one or more.
    /// Will fail if this is given fewer items than that.
    let nel list =
        match list with
        | [] -> failwith "NEL needs to have at least one member"
        | h :: t -> NEL.new_ h t

    /// Make a list of two or more.
    /// Will fail if this is given fewer items than that.
    let tom list =
        match list with
        | []
        | [ _ ] -> failwith "TOM needs to have at least two members"
        | h :: n :: t -> TOM.new_ h n t

    /// Make a set
    let set list : RefConstr set = Set.ofSeq list




    /// Make a map from a seq of key/value pairs
    let map keyvals = Map.ofSeq keyvals


    /// Make type constraints from a definitive type
    let def = TypeConstraints.fromDefinitive

    /// Make type constraints from one reference constraint only
    let cstr cnstraint =
        TypeConstraints.Constrained (None, Set.singleton cnstraint)

    /// Make type constraints from reference constraints only
    let cstrs constraints =
        TypeConstraints.Constrained (None, set constraints)

    /// Make type constraints from definitive type and reference constraints
    let defCstrs def constraints =
        TypeConstraints.Constrained (Some def, set constraints)

    /// Make empty type constraints
    let none = TypeConstraints.empty

    let any () = TypeConstraints.makeUnspecific ()


    /// Make a key/value pair for a record
    let kv k v = RecordFieldName k, v





    (* Make constraints *)

    /// Make a constraint based on value name
    let v = LowerIdent >> LocalLower >> ByValue

    /// Make a constraint based on type param
    let tp = LowerIdent >> ByTypeParam

    /// Make a constraint based on constructor name
    let ct = LocalUpper >> ByConstructorType




    /// Make tuple
    let (=>) a b = a, b



    (* Make definitive types *)

    (* Make primitive types *)
    /// The Float type
    let f = DtPrimitiveType Float

    /// The Int type
    let i = DtPrimitiveType Int
    /// The String type
    let s = DtPrimitiveType String
    /// The Char type
    let c = DtPrimitiveType Char
    /// The Bool type
    let b = DtPrimitiveType Bool

    (* Make other types *)
    // The unit type
    let unit = def DtUnitType
    let tuple list = DtTuple (tom list)
    let list t = DtList t
    let recWith keyvals = DtRecordWith (map keyvals)
    let recExact keyvals = DtRecordExact (map keyvals)
    //let newType = DtNewType()
    let arrow a b = DtArrow (a, b)

    let rec arrowChain (list : TypeConstraints list) : DefinitiveType =
        match list with
        | []
        | _ :: [] -> failwith "Needs to have at least two items to represent the domain and range"
        | h :: n :: t ->
            arrow
                h
                (match t with
                 | [] -> n
                 | first :: rest -> defCstrs (arrowChain (n :: first :: rest)) [])





open TypeDsl


let private makeAccTypeId () =
    System.Guid.NewGuid () |> AccumulatorTypeId

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


                     let unified = Acc.unifyTypeConstraintIds guid2 guid3 acc

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
                                   guid6, (RefDtPrimitiveType String |> Ok |> Some, Set.empty) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTypeConstraintIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult = RefDtList toTypeRealId |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedTypeParam = RefDtPrimitiveType String |> Ok |> Some, set [ refA ]

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
                                   guid6, (RefDtPrimitiveType String |> Ok |> Some, Set.empty) ]
                                 |> Map.ofSeq }


                     let unified = Acc.unifyTypeConstraintIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult =
                         RefDtArrow (guid1, toTypeRealId) |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedToType = RefDtPrimitiveType String |> Ok |> Some, set [ refA ]

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


                     let unified = Acc.unifyTypeConstraintIds guid3 guid5 acc
                     let returnedIdResult = Accumulator.getTypeById unified.typeId unified.acc
                     let toTypeRealId, toTypeResult = Accumulator.getRealIdAndType guid4 unified.acc

                     let expectedResult = RefDtList toTypeRealId |> Ok |> Some, set [ refB; refC; refD ]

                     let expectedTypeParam = RefDtPrimitiveType String |> Ok |> Some, set [ refA ]

                     Expect.equal
                         returnedIdResult
                         expectedResult
                         "Result has the type of the one with the definitive type but the ref constraints of both"

                     Expect.equal toTypeResult expectedTypeParam "The list's type param is the merger of guids 4 and 6"
                 }







                 ])


          test "Simple Acc merge with no unifications needed" {
              let guid1 = makeAccTypeId ()
              let guid2 = makeAccTypeId ()
              let guid3 = makeAccTypeId ()
              let guid4 = makeAccTypeId ()


              let handMadeAcc1 : Accumulator =
                  { Acc.empty with
                      refConstraintsMap =
                          [

                          ]
                          |> Map.ofSeq }

              let handMadeAcc2 : Accumulator =
                  { Acc.empty with
                      refConstraintsMap =
                          [

                          ]
                          |> Map.ofSeq }

              let expected = Acc.empty

              let combined = Acc.combine handMadeAcc1 handMadeAcc2


              Expect.equal combined expected "Combined Accs is as expected"


          }

          test "Test conversion to and from TypeConstraints" {
              let tcToConvert = def (arrow (def s) (cstr (v "test")))

              let converted = Acc.convertTypeConstraints tcToConvert

              let convertedBack = Acc.convertAccIdToTypeConstraints converted.typeId converted.acc

              Expect.equal convertedBack (Ok tcToConvert) "Converting a TC to an Acc and back is consistent"
          } ]









[<Tests>]
let typeCheckThings =
    testList
        "Type check some things"
        [ testList
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
                        "Generic func applied to two things results in those two things" ]

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

                testCase "Function applied to primitive, named value, and itself"
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

                          let typeConstraint = cstr (v "f")


                          //let acc =
                          //    [ set [ v "f" ]
                          //      => Ok (Some (arrow (cstr (v "a")) (any ()))) ]
                          //    |> Map.ofList

                          Expect.equal (getTypeFromElmStr expr) (Ok typeConstraint) "" ]

                testList "Unify type constraints" []

                testList "Unify type judgments" []

                ]

          ]

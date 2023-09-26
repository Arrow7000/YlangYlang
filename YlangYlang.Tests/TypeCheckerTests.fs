module TypeCheckerTests

module S = SyntaxTree
module Cst = ConcreteSyntaxTree
module T = TypedSyntaxTree

open TypedSyntaxTree
open TypeChecker
open QualifiedSyntaxTree.Names
open Errors

module Acc = Accumulator2
module Aaot = AccAndTypeId


open Expecto


let private makeNumberExpression : S.NumberLiteralValue -> Cst.Expression =
    S.NumberPrimitive
    >> S.Primitive
    >> S.ExplicitValue
    >> S.SingleValueExpression

let private getType (expr : T.TypedExpr) : TypeJudgment =
    let result = getAccumulatorFromExpr expr

    Acc.convertAccIdToTypeConstraints result.typeId result.acc
    |> Result.map deleteGuidsFromTypeConstraints



/// Lex, parse, type check, and get the type of the expression from a string containing an Elm expression!
let private getTypeFromElmStr text : Result<TypeConstraints, Errors> =
    Lexer.tokeniseString text
    |> Result.mapError LexingError
    |> Result.bind (
        ExpressionParsing.run ExpressionParsing.parseExpression
        >> Parser.toResult
        >> Result.mapError ParsingError
    )
    |> Result.bind (
        typeCheckCstExpression List.empty
        >> getType
        >> Result.mapError TypeError
    )


let getAccFromElmStr text : Result<Accumulator, Errors> =
    Lexer.tokeniseString text
    |> Result.mapError LexingError
    |> Result.bind (
        ExpressionParsing.run ExpressionParsing.parseExpression
        >> Parser.toResult
        >> Result.mapError ParsingError
    )
    |> Result.map (
        typeCheckCstExpression List.empty
        >> getAccumulatorFromExpr
        >> Aaot.getAcc
    )





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

                          let acc =
                              [ set [ v "f" ]
                                => Ok (Some (arrow (cstr (v "a")) (any ()))) ]
                              |> Map.ofList

                          Expect.equal (getAccFromElmStr expr) (Ok acc) "" ]

                testList "Unify type constraints" []

                testList "Unify type judgments" []

                ]

          ]

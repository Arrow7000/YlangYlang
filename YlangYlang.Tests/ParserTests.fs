module ParserTests

open Parser
open Expecto


type SampleCtx =
    | FirstCtx
    | SndCtx
    | ThirdCtx

type TestToken =
    | A
    | B
    | C
    | D
    | W


type ExpectedErr =
    { expectedToken : TestToken
      actualToken : TestToken }

type TestError =
    | ExpectedTokenButFound of ExpectedErr
    | ExpectedTokenButNoneLeft of TestToken


type TestParser<'a> = Parser<'a, TestToken, SampleCtx, TestError>





let makeExpectedToken expected found =
    ExpectedTokenButFound
        { expectedToken = expected
          actualToken = found }


let makeResult parseResult prevTokens tokensLeft =
    let result =
        match parseResult with
        | Ok res -> ParsingSuccess res
        | Error errs ->
            NoParsingMatch (
                let errors =
                    errs
                    |> List.map (fun err ->
                        OneErr
                            { err = err
                              prevTokens = List.empty
                              contextStack = List.empty })

                match errors with
                | [ e ] -> e
                | _ -> MultipleErrs errors
            )

    { parseResult = result
      contextStack = List.empty
      prevTokens = prevTokens
      tokensLeft = tokensLeft
      committed = List.empty }


let parseSingleTestToken token : TestParser<TestToken> =
    let err t =
        ExpectedTokenButFound
            { expectedToken = token
              actualToken = t }

    parseSingleToken (ExpectedTokenButNoneLeft token) (function
        | t when t = token -> Ok token
        | t -> Error (err t))


let parseA = parseSingleTestToken A
let parseB = parseSingleTestToken B
let parseC = parseSingleTestToken C
let parseD = parseSingleTestToken D
let parseW = parseSingleTestToken W


[<Tests>]
let testEither =
    let eitherAorB = either parseA parseB

    let runAorB = run eitherAorB

    [ (fun _ ->
          let token = A

          let result = runAorB [ token ]
          let expected = makeResult (Ok token) [ token ] []

          Expect.equal result expected "Test first of either")
      |> testCase "Test first of either"
      (fun _ ->
          let token = B

          let result = runAorB [ token ]
          let expected = makeResult (Ok token) [ token ] []

          Expect.equal result expected "Test second of either")
      |> testCase "Test second of either"
      (fun _ ->
          let token = C

          let result = runAorB [ token ]

          let expected =
              makeResult
                  (Error [ makeExpectedToken A C
                           makeExpectedToken B C ])
                  []
                  [ token ]

          Expect.equal result expected "Test failure of either")
      |> testCase "Test failure of either"

      (fun _ ->
          let result = runAorB [ B; C; A; C ]

          let expected = makeResult (Ok B) [ B ] [ C; A; C ]

          Expect.equal result expected "Test more items in tokensLeft")
      |> testCase "Test more items in tokensLeft"
      makeTestCase "Test oneOf" (fun _ ->
          let parser =
              oneOf [ oneOrMore parseA
                      oneOrMore parseB
                      oneOrMore parseC
                      oneOrMore parseD ]

          let tokens = [ C; C ]


          let result = run parser tokens
          let expected = makeResult (Ok (NEL (C, [ C ]))) tokens List.empty

          expectEqual result expected None)


      ]
    |> testList "Test either"


[<Tests>]
let testRepeat =
    let eitherAorBlist = repeat (either parseA parseB)

    let runAorBlist = run eitherAorBlist

    [ (fun _ ->
          let result = runAorBlist [ C; D ]
          let expected = makeResult (Ok []) [] [ C; D ]

          Expect.equal result expected "Empty match list")
      |> testCase "Empty match list"
      (fun _ ->
          let result = runAorBlist [ A; A; B; A; B; C; A; D ]

          let expected = makeResult (Ok [ A; A; B; A; B ]) [ A; A; B; A; B ] [ C; A; D ]

          Expect.equal result expected "Match multiple of either")
      |> testCase "Match multiple of either" ]
    |> testList "Test repetitions"



[<Tests>]
let testKeepAndIgnoreOperators =

    let parseManyW = repeat parseW


    [ (fun _ ->
          let parser =
              succeed id

              |= parseA
              |. parseManyW


          let runParser = run parser
          let allTokens = [ A; W; W; W; W; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok A) allTokens List.empty

          Expect.equal result expected "Match an A and chomp remaining whitespace")
      |> testCase "Match an A and chomp remaining whitespace"
      (fun _ ->
          let parser =
              succeed (fun a b -> (a, b))

              |= parseA
              |. parseW
              |. parseW
              |. parseW
              |= parseB
              |. parseW
              |. parseW


          let runParser = run parser
          let allTokens = [ A; W; W; W; B; W; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok (A, B)) allTokens List.empty

          Expect.equal result expected "Match A and B separated by whitespace")
      |> testCase "Match A and B separated by whitespace"
      (fun _ ->

          // This is meant to emulate parsing a lambda with arbitrary many args and arbitrary whitespace between the args
          let parser =
              succeed (fun a b -> (a, b))

              |= parseA
              |. parseManyW
              |= parseB
              |. parseManyW
              |. parseC
              |. parseManyW


          let runParser = run parser
          let allTokens = [ A; W; W; B; W; W; W; C; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok (A, B)) allTokens List.empty

          Expect.equal result expected "Match an A and a B from a sequence")
      |> testCase "Match an A and a B from a sequence"

      (fun _ ->
          let parser =
              succeed (fun _ bList -> bList)

              |= parseA
              |. parseManyW
              |= repeat (parseB |. parseManyW)
              |. parseManyW
              |. parseC
              |. parseManyW


          let runParser = run parser
          let allTokens = [ A; W; W; B; B; W; W; B; W; B; C; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok [ B; B; B; B ]) allTokens List.empty

          Expect.equal result expected "Match with 4 Bs")
      |> testCase "Match with 4 Bs"
      (fun _ ->
          let parser =
              succeed (fun _ bList -> bList)

              |= parseA
              |. parseManyW
              |= oneOrMore (parseB |. parseManyW)
              |. parseManyW
              |. parseC
              |. parseManyW


          let runParser = run parser
          let allTokens = [ A; W; W; B; B; W; W; B; W; B; C; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok <| NEL.new_ B [ B; B; B ]) allTokens List.empty

          Expect.equal result expected "Match 4 Bs with oneOrMore")
      |> testCase "Match 4 Bs with oneOrMore" ]
    |> testList "Test complex parser with optional whitespace in the middle"



[<Tests>]
let testCommitment =

    let oneCommitParser =
        either
            (succeed (fun a _ _ -> a)

             |= parseA
             |. commit
             |= parseB
             |= parseC)
            (parseD |. parseC)


    let doubleCommitParser =
        either
            (succeed (fun a _ _ -> a)

             |= parseA
             |. commit
             |= parseB
             |= (either
                     (succeed (fun _ a -> a)

                      |= parseC
                      |. commit
                      |= parseA)
                     parseD))
            (parseD |. parseC)



    [ makeTestCase "Once we get past commit point we no longer backtrack" (fun _ ->
          let tokens = [ A; C ]

          let actual = run oneCommitParser tokens

          let coreExpected = makeResult (Error [ makeExpectedToken B C ]) [ A ] [ C ]

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          OneErr
                              { err = makeExpectedToken B C
                                prevTokens = [ A ]
                                contextStack = List.empty }
                      )
                  committed = [ true ] }

          expectEqual actual expected None)

      makeTestCase "Get another token past commit and still don't backtrack" (fun _ ->
          let tokens = [ A; B; D ]

          let actual = run oneCommitParser tokens

          let coreExpected = makeResult (Error [ makeExpectedToken C D ]) [ A; B ] [ D ]

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          OneErr
                              { err = makeExpectedToken C D
                                prevTokens = [ A; B ]
                                contextStack = List.empty }
                      )
                  committed = [ true ] }

          expectEqual actual expected None)

      makeTestCase "If not past commit point should still backtrack" (fun _ ->
          let tokens = [ D; B ]

          let actual = run oneCommitParser tokens

          let coreExpected =
              makeResult
                  (Error [ makeExpectedToken A D
                           makeExpectedToken C B ])
                  List.empty
                  tokens

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          MultipleErrs[

                          OneErr
                              { err = makeExpectedToken A D
                                prevTokens = List.empty
                                contextStack = List.empty }

                          OneErr
                              { err = makeExpectedToken C B
                                prevTokens = [ D ]
                                contextStack = List.empty }]
                      ) }

          expectEqual actual expected None)

      makeTestCase "Commit twice still doesn't backtrack" (fun _ ->
          let tokens = [ A; B; C; D ]

          let actual = run doubleCommitParser tokens

          let coreExpected = makeResult (Error [ makeExpectedToken A D ]) [ A; B; C ] [ D ]

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          OneErr
                              { err = makeExpectedToken A D
                                prevTokens = [ A; B; C ]
                                contextStack = List.empty }
                      )
                  committed = [ true; true ] }

          expectEqual actual expected None)

      makeTestCase "Only get past one commit in a two commit parser" (fun _ ->
          let tokens = [ A; B; W ]

          let actual = run doubleCommitParser tokens

          let coreExpected =
              makeResult
                  (Error [ makeExpectedToken C W
                           makeExpectedToken D W
                           makeExpectedToken D A ])
                  List.empty
                  tokens

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          MultipleErrs [ OneErr
                                             { err = makeExpectedToken C W
                                               prevTokens = [ A; B ]
                                               contextStack = List.empty }
                                         OneErr
                                             { err = makeExpectedToken D W
                                               prevTokens = [ A; B ]
                                               contextStack = List.empty }
                                         OneErr
                                             { err = makeExpectedToken D A
                                               prevTokens = List.empty
                                               contextStack = List.empty }

                                          ]
                      )
                  committed = List.empty }

          expectEqual actual expected None)

      makeTestCase "Fail parser before it commits to anything and pass on a different branch" (fun _ ->
          let tokens = [ D; C ]

          let actual = run doubleCommitParser tokens

          let expected = makeResult (Ok D) tokens List.empty


          expectEqual actual expected None)

      makeTestCase "Fail parser before it commits to anything and so return both branch errors" (fun _ ->
          let tokens = [ D; B; D ]

          let actual = run doubleCommitParser tokens

          let coreExpected =
              makeResult
                  (Error [ makeExpectedToken A D
                           makeExpectedToken C B ])
                  List.empty
                  tokens

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          MultipleErrs [ OneErr
                                             { err = makeExpectedToken A D
                                               prevTokens = List.empty
                                               contextStack = List.empty }
                                         OneErr
                                             { err = makeExpectedToken C B
                                               prevTokens = [ D ]
                                               contextStack = List.empty } ]
                      ) }

          expectEqual actual expected None)

      makeTestCase "Committing also works to stop alternative paths in oneOf" (fun _ ->

          let parser =
              oneOf [ (succeed (fun a _ _ -> a)

                       |= parseA
                       |. commit
                       |= parseB
                       |= (oneOf [ (succeed (fun _ a -> a)

                                    |= parseC
                                    |. commit
                                    |= parseA)
                                   parseD ]))
                      (parseD |. parseC)
                      (parseB |. parseA) ]

          let tokens = [ A; B; C; D ]

          let actual = run parser tokens

          let coreExpected = makeResult (Error [ makeExpectedToken A D ]) [ A; B; C ] [ D ]

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          OneErr
                              { err = makeExpectedToken A D
                                prevTokens = [ A; B; C ]
                                contextStack = List.empty }
                      )
                  committed = [ true; true ] }

          expectEqual actual expected None)

      makeTestCase "Only one commit inside two nested oneOfs should still commit across the entire tree" (fun _ ->

          let parser =
              oneOf [ (succeed (fun a _ _ -> a)

                       |= parseA
                       |= parseB
                       |= (oneOf [ (succeed (fun _ a -> a)

                                    |= parseC
                                    |. commit
                                    |= parseA)
                                   parseD ]))
                      (parseD |. parseC)
                      (parseB |. parseA) ]

          let tokens = [ A; B; C; D ]

          let actual = run parser tokens

          let coreExpected = makeResult (Error [ makeExpectedToken A D ]) [ A; B; C ] [ D ]

          let expected =
              { coreExpected with
                  parseResult =
                      NoParsingMatch (
                          OneErr
                              { err = makeExpectedToken A D
                                prevTokens = [ A; B; C ]
                                contextStack = List.empty }
                      )
                  committed = [ true ] }

          expectEqual actual expected None) ]
    |> testList "Test committing"

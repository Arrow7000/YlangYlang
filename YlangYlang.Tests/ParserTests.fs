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
                errs
                |> List.map (fun err ->
                    OneErr
                        { err = err
                          prevTokens = List.empty
                          contextStack = List.empty })
                |> MultipleErrs
            )

    { parseResult = result
      contextStack = List.empty
      prevTokens = prevTokens
      tokensLeft = tokensLeft }


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
      |> testCase "Test more items in tokensLeft" ]
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
              |= repeat (
                  succeed id

                  |= parseB
                  |. parseManyW
              )
              |. parseManyW
              |. parseC
              |. parseManyW


          let runParser = run parser
          let allTokens = [ A; W; W; B; B; W; W; B; W; B; C; W ]

          let result = runParser allTokens

          let expected = makeResult (Ok [ B; B; B; B ]) allTokens List.empty

          Expect.equal result expected "Match with 4 Bs")
      |> testCase "Match with 4 Bs" ]
    |> testList "Test complex parser with optional whitespace in the middle"






//let testSettingCtx =
//    let origParser =
//        spaces |. symbol ParensOpen |. spaces
//        |> addCtxToStack PrimitiveLiteral
//        |> addCtxToStack Int

//    (fun _ ->
//        let result =
//            Parser.run
//                origParser
//                ([ BracesClose
//                   BracketsClose
//                   Whitespace NewLineChar ]
//                 |> List.map makeDummyCtx)

//        Expect.equal
//            result
//            ({ parseResult = NoParsingMatch (ExpectedToken ParensOpen)
//               prevTokens = List.empty
//               tokensLeft = List.empty
//               contextStack = [ Int; PrimitiveLiteral ] })
//            "Parse single value expression")
//    |> testCase "Parse single value expression"



//let testBind =
//    let origParser =
//        spaces () |. symbol ParensOpen |. spaces ()
//        |> addCtxToStack PrimitiveLiteral
//        |> addCtxToStack Int

//    (fun _ ->
//        let result =
//            Parser.run
//                origParser
//                ([ BracesClose
//                   BracketsClose
//                   Whitespace NewLineChar ]
//                 |> List.map makeDummyCtx)

//        Expect.equal
//            result
//            ({ parseResult = NoParsingMatch (ExpectedToken ParensOpen)
//               prevTokens = List.empty
//               tokensLeft = List.empty
//               contextStack = [ Int; PrimitiveLiteral ] })
//            "Test parser bind")
//    |> testCase "Test parser bind"

//[<Tests>]
//let tests = testList "Parser tests" [ testSettingCtx; testBind ]

module ParserTests

open Lexer
open Parser
open Expecto


//type SampleCtx =
//    | FirstCtx
//    | SndCtx
//    | ThirdCtx

let makeDummyCtx t : TokenWithContext =
    { token = t
      startLine = 0u
      startCol = 0u
      endLine = 0u
      endCol = 0u
      chars = List.empty }




let testSettingCtx =
    let origParser =
        spaces |. symbol ParensOpen |. spaces
        |> addCtxToStack PrimitiveLiteral
        |> addCtxToStack Int

    (fun _ ->
        let result =
            Parser.run
                origParser
                ([ BracesClose
                   BracketsClose
                   Whitespace NewLineChar ]
                 |> List.map makeDummyCtx)

        Expect.equal
            result
            ({ parseResult = NoParsingMatch (ExpectedToken ParensOpen)
               prevTokens = List.empty
               tokensLeft = List.empty
               contextStack = [ Int; PrimitiveLiteral ] })
            "Parse single value expression")
    |> testCase "Parse single value expression"



let testBind =
    let origParser =
        spaces |. symbol ParensOpen |. spaces
        |> addCtxToStack PrimitiveLiteral
        |> addCtxToStack Int

    (fun _ ->
        let result =
            Parser.run
                origParser
                ([ BracesClose
                   BracketsClose
                   Whitespace NewLineChar ]
                 |> List.map makeDummyCtx)

        Expect.equal
            result
            ({ parseResult = NoParsingMatch (ExpectedToken ParensOpen)
               prevTokens = List.empty
               tokensLeft = List.empty
               contextStack = [ Int; PrimitiveLiteral ] })
            "Test parser bind")
    |> testCase "Test parser bind"

[<Tests>]
let tests = testList "Parser tests" [ testSettingCtx; testBind ]

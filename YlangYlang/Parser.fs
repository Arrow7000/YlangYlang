module Parser

open Lexer

/// @TODO: remove label cuz I don't think we need it anymore if we have a context stack and parser errors
type Label =
    | Label of string
    | UnknownLabel


/// Aka the problem
type ParserError =
    | ExpectedToken of Token
    | ExpectedString of string
    | NoParsersLeft
    | TokenNotValidHere of TokenWithContext
    | PredicateDidntMatch

    /// but there were yet more tokens
    | ExpectedEndOfExpression

    /// but there were no tokens left
    | UnexpectedEndOfExpression of expected : Token option
    | MultipleErrors of ParserError list


type Context =
    | PrimitiveLiteral
    | Int
    | Ufloat
    | Float
    | Unit
    | Operator
    | ParamList
    | Identifier
    | Lambda
    | SingleLetAssignment
    | LetBindingsAssignmentList
    | SingleValueExpression
    | CompoundExpression
    | WholeExpression
    | ParensExpression


//type ParsingSuccess<'a> = 'a

//type ParseFailure =  ParserError


type ParseResult<'a> =
    | ParsingSuccess of 'a
    | NoParsingMatch of ParserError


type ParseContext =
    { prevTokens : TokenWithContext list
      tokensLeft : TokenWithContext list
      contextStack : Context list }

type ParseResultWithContext<'a> =
    { parseResult : ParseResult<'a>
      prevTokens : TokenWithContext list
      tokensLeft : TokenWithContext list
      contextStack : Context list }


type ParseFn<'a> = ParseContext -> ParseResultWithContext<'a>




type Parser<'a> = private | Parser of ParseFn<'a>



let blankParseCtx : ParseContext =
    { prevTokens = List.empty
      tokensLeft = List.empty
      contextStack = List.empty }

let makeParseResultWithCtx result (record : ParseContext) =
    { parseResult = result
      prevTokens = record.prevTokens
      tokensLeft = record.tokensLeft
      contextStack = record.contextStack }


let makeCtxFromParseResult resultWithCtx =
    { prevTokens = resultWithCtx.prevTokens
      tokensLeft = resultWithCtx.tokensLeft
      contextStack = resultWithCtx.contextStack }

let replaceParseResultWithCtx result (record : ParseResultWithContext<'a>) : ParseResultWithContext<'b> =
    { parseResult = result
      prevTokens = record.prevTokens
      tokensLeft = record.tokensLeft
      contextStack = record.contextStack }

let addCtxToStack ctx (Parser parseFn) : Parser<'a> =
    Parser (fun record ->
        let newRecord = { record with contextStack = ctx :: record.contextStack }
        parseFn newRecord)




let makeWithCtx ctx (parseFn : ParseFn<'a>) = addCtxToStack ctx (Parser parseFn)


let runWithCtx (Parser parseFn) parseCtx : ParseResultWithContext<'a> = parseFn parseCtx

let run (parser) (tokens : TokenWithContext list) : ParseResultWithContext<'a> =
    runWithCtx
        parser
        // @TODO: not sure if I need to allow for existing previous tokens and context stack or not...
        { prevTokens = List.empty
          tokensLeft = tokens
          contextStack = List.empty }




let private bindHelper
    (bind' : ParseResultWithContext<'a> -> ParseResultWithContext<'b>)
    (parser : Parser<'a>)
    (record : ParseContext)
    =
    let parseResult = run parser record.tokensLeft

    match parseResult.parseResult with
    | NoParsingMatch e ->
        { parseResult = NoParsingMatch e
          prevTokens = parseResult.prevTokens
          tokensLeft = parseResult.tokensLeft
          contextStack = parseResult.contextStack }

    | ParsingSuccess _ ->
        let bindResult = bind' parseResult

        match bindResult.parseResult with
        | NoParsingMatch e ->
            { parseResult = NoParsingMatch e
              prevTokens = bindResult.prevTokens
              tokensLeft = bindResult.tokensLeft
              contextStack = bindResult.contextStack }
        | ParsingSuccess s ->
            { parseResult = ParsingSuccess s
              prevTokens = bindResult.prevTokens
              tokensLeft = bindResult.tokensLeft
              contextStack = bindResult.contextStack }



//let bind (f : 'a -> Parser<'b>) (Parser p as parser : Parser<'a>) : Parser<'b> =

//    let (Parser newParser) =
//        bindHelper
//            (fun tokens successRes _ ->
//                ParsingSuccess
//                    { result = successRes
//                      tokensLeft = tokens })
//            parser

//    Parser
//        { parseFn = newParser.parseFn
//          contextStack = newParser.contextStack }


let bind (f : 'a -> Parser<'b>) (Parser parseFn : Parser<'a>) : Parser<'b> =
    Parser (fun (context : ParseContext) ->
        let firstResult = parseFn context

        match firstResult.parseResult with
        | NoParsingMatch err ->
            { parseResult = NoParsingMatch err
              prevTokens = firstResult.prevTokens
              tokensLeft = firstResult.tokensLeft
              contextStack = firstResult.contextStack }

        | ParsingSuccess result ->
            // @TODO: not sure if this quite makes sense, but let's see.
            runWithCtx (f result) (makeCtxFromParseResult firstResult))


//let bind (f : 'a -> Parser<'b>) (parser : Parser<'a>) : Parser<'b> =
//    Parser (
//        bindHelper
//            (fun resultWithCtx ->

//                match resultWithCtx.parseResult with
//                | ParsingSuccess s ->
//                    let (Parser innerFun) = f s

//                    innerFun
//                        { prevTokens = resultWithCtx.prevTokens
//                          tokensLeft = resultWithCtx.tokensLeft
//                          contextStack = resultWithCtx.contextStack }
//                | NoParsingMatch e ->
//                    { parseResult = NoParsingMatch e
//                      prevTokens = resultWithCtx.prevTokens
//                      tokensLeft = resultWithCtx.tokensLeft
//                      contextStack = resultWithCtx.contextStack }

//                )
//            parser
//    )

//let fn tokens _ =

//    let firstResult = run parser tokens

//    match firstResult.parseResult with
//    | ParsingSuccess s ->
//        run (f s.result) tokens
//        |> fun innerResult ->
//            { parseResult = innerResult.parseResult
//              contextList = innerResult.contextList @ firstResult.contextList }


//    | NoParsingMatch x ->
//        { parseResult = NoParsingMatch x
//          contextList = firstResult.contextList }

//Parser
//    { parseFn = fn
//      contextStack = p.contextStack }



//let map (f : 'a -> 'b) (Parser p as parser : Parser<'a>) : Parser<'b> =
//    parser
//    |> bind (fun (s : 'a) ->
//        (fun tokens ctxs ->
//            { parseResult = ParsingSuccess { result = f s; tokensLeft = tokens }
//              contextList = ctxs })
//        |> makeWithCtx UnknownLabel)

let map (f : 'a -> 'b) (parser : Parser<'a>) : Parser<'b> =
    parser
    |> bind (fun (s : 'a) ->
        Parser (fun record ->
            { parseResult = ParsingSuccess (f s)
              prevTokens = record.prevTokens
              tokensLeft = record.tokensLeft
              contextStack = record.contextStack }))






let flatten : Parser<Parser<'a>> -> Parser<'a> = fun parser -> bind id parser






let map2 (f : 'a -> 'b -> 'c) (parserA : Parser<'a>) (parserB : Parser<'b>) : Parser<'c> =
    parserA
    |> map (fun a -> map (f a) parserB)
    |> flatten

let either (parserA : Parser<'a>) (parserB : Parser<'a>) : Parser<'a> =
    Parser (fun record ->
        let result = runWithCtx parserA record

        match result.parseResult with
        | ParsingSuccess _ -> result
        | NoParsingMatch _ -> runWithCtx parserB record)

//|> makeWithCtx UnknownLabel

let rec oneOf (parsers : Parser<'a> list) : Parser<'a> =
    let rec oneOfHelper errorsSoFar parsersLeft record : ParseResultWithContext<'a> =

        match parsersLeft with
        | [] ->
            makeParseResultWithCtx
                (NoParsingMatch (
                    match errorsSoFar with
                    | [] -> NoParsersLeft
                    | x :: [] -> x
                    | others -> MultipleErrors others
                ))
                record

        | head :: rest ->
            let result = runWithCtx head record

            match result.parseResult with
            | ParsingSuccess _ -> result
            | NoParsingMatch e -> oneOfHelper (e :: errorsSoFar) rest record

    Parser (fun record -> oneOfHelper List.empty parsers record)



/// Parser that always succeeds
let succeed a : Parser<'a> =
    Parser (makeParseResultWithCtx (ParsingSuccess a))

let fail : ParserError -> Parser<'a> =
    fun err -> Parser (makeParseResultWithCtx (NoParsingMatch err))

let lazyParser thunk : Parser<'a> =
    Parser (fun tokens ->
        let (Parser parse) = thunk ()
        parse tokens)



let keep (parserA : Parser<'a -> 'b>) (parserB : Parser<'a>) : Parser<'b> = map2 apply parserA parserB

let (|=) a b = keep a b


let skip (parserA : Parser<'keep>) (parserB : Parser<'ignore>) = map2 (fun a _ -> a) parserA parserB

let (|.) a b = skip a b


let ignore p = map ignore p


/// For when there are two paths to the same thing
let fork parserA parserB finalParser =
    either parserA parserB |> bind finalParser

/// `end` is a keyword in F# so have to use `isEnd`
let isEnd : Parser<unit> =
    Parser (fun { tokensLeft = tokensLeft } ->
        match tokensLeft with
        | [] -> makeParseResultWithCtx (ParsingSuccess ()) blankParseCtx
        | _ -> makeParseResultWithCtx (NoParsingMatch ExpectedEndOfExpression) blankParseCtx)


let rec chompWhileHelper contextList predicate tokensChomped tokensLeft : ParseResultWithContext<unit> =
    match tokensLeft with
    | [] ->
        { prevTokens = tokensChomped
          parseResult = ParsingSuccess ()
          tokensLeft = tokensLeft
          contextStack = contextList }
    | head :: rest ->
        if predicate head then
            chompWhileHelper contextList predicate (tokensChomped @ [ head ]) rest
        else
            { prevTokens = tokensChomped
              parseResult = ParsingSuccess ()
              tokensLeft = head :: rest
              contextStack = contextList }

//let rec chompWhileHelper predicate tokensChomped record : ParseResultWithContext<unit> =
//    match record.tokensLeft with
//    | [] ->
//        { prevTokens = tokensChomped
//          parseResult = ParsingSuccess ()
//          tokensLeft = record.
//          contextList = List.empty }
//    | head :: rest ->
//        if predicate head then
//            chompWhileHelper predicate (tokensChomped @ [ head ]) rest
//        else
//            { prevTokens = tokensChomped
//              parseResult = ParsingSuccess ()
//              tokensLeft = head :: rest
//              contextList = List.empty }



let rec chompWhile predicate : Parser<unit> =
    Parser (fun record -> chompWhileHelper record.contextStack predicate record.prevTokens record.tokensLeft)



let any : Parser<unit> = chompWhile (always true)


let printTokensAsText (tokens : TokenWithContext list) =
    tokens
    |> List.fold (fun charList t -> charList + String.ofSeq t.chars) ""

let tee f parser =
    Parser (fun record ->
        f record
        runWithCtx parser record)


let symbol expectedToken : Parser<unit> =
    Parser (fun record ->
        match record.tokensLeft with
        | [] ->
            record
            |> makeParseResultWithCtx (NoParsingMatch (UnexpectedEndOfExpression <| Some expectedToken))

        //NoParsingMatch
        //    { tokensChomped = List.empty
        //      label = UnknownLabel
        //      error = UnexpectedEndOfExpression <| Some expectedToken }
        | nextToken :: rest ->
            if expectedToken = nextToken.token then
                { parseResult = ParsingSuccess ()
                  prevTokens = record.prevTokens @ [ nextToken ]
                  tokensLeft = rest
                  contextStack = record.contextStack }

            else
                { parseResult = NoParsingMatch <| ExpectedToken expectedToken
                  prevTokens = record.prevTokens
                  tokensLeft = record.tokensLeft
                  contextStack = record.contextStack })


let ifMatches predicate : Parser<unit> = chompWhile predicate

/// Matches and maps over single token
let matchCtxToken chooser =
    Parser (fun record ->
        match record.tokensLeft with
        | [] ->
            { parseResult = NoParsingMatch <| UnexpectedEndOfExpression None
              prevTokens = record.prevTokens
              tokensLeft = record.tokensLeft
              contextStack = record.contextStack }
        //(UnknownLabel, UnexpectedEndOfExpression None)
        | nextToken :: rest ->
            match chooser nextToken with
            | Some x ->
                { parseResult = ParsingSuccess x
                  prevTokens = record.prevTokens @ [ nextToken ]
                  tokensLeft = rest
                  contextStack = record.contextStack }
            | None ->
                { parseResult = NoParsingMatch PredicateDidntMatch
                  prevTokens = record.prevTokens
                  tokensLeft = record.tokensLeft
                  contextStack = record.contextStack })
//(UnknownLabel, PredicateDidntMatch))

let matchSingleToken f = matchCtxToken (fun t -> f t.token)

/// If you need access to the matched token itself use `matchSingleToken`
let parseToken expectedToken f =
    matchSingleToken (fun token ->
        if token = expectedToken then
            Some f
        else
            None)




let rec repeat (parser : Parser<'a>) : Parser<'a list> =
    Parser (fun record ->
        let rec traverser state tokensChomped tokensRemaining =
            tokensRemaining
            |> run parser
            |> fun result ->
                match result.parseResult with
                | ParsingSuccess s -> traverser (s :: state) result.prevTokens result.tokensLeft

                | NoParsingMatch _ ->
                    { parseResult = ParsingSuccess state
                      prevTokens = tokensChomped
                      tokensLeft = tokensRemaining
                      contextStack = result.contextStack }

        traverser List.empty record.prevTokens record.tokensLeft)
    |> map List.rev

let oneOrMore (parser : Parser<'a>) : Parser<NEL<'a>> =
    map2 NEL.consFromList parser (repeat parser)


let opt parser =
    Parser (fun record ->
        let result = runWithCtx parser record

        match result.parseResult with
        | ParsingSuccess s -> replaceParseResultWithCtx (ParsingSuccess <| Some s) result
        | NoParsingMatch _ -> makeParseResultWithCtx (ParsingSuccess None) record)


let spaces : Parser<unit> =
    repeat (
        matchSingleToken (function
            | Whitespace _ -> Some ()
            | _ -> None)
    )
    |> ignore



type PartitionedTokens =
    { includedTokens : TokenWithContext list
      tokensLeft : TokenWithContext list }

let getTilLineBreak (tokens : TokenWithContext list) =
    let rec traverser tokensGatheredSoFar tokensLeft =
        match tokensLeft with
        | [] ->
            { includedTokens = tokensGatheredSoFar
              tokensLeft = tokensLeft }
        | head :: rest ->
            match head.token with
            | Whitespace char ->
                match char with
                | NewLineChar ->
                    { includedTokens = tokensGatheredSoFar
                      tokensLeft = tokensLeft }
                | Space -> traverser (head :: tokensGatheredSoFar) rest
            | _ -> traverser (head :: tokensGatheredSoFar) rest

    traverser List.empty tokens


let getBlock (tokens : TokenWithContext list) =
    match tokens with
    | [] ->
        { includedTokens = List.empty
          tokensLeft = List.empty }

    | blockHead :: _ ->
        let rec traverser tokensGathered (tokensLeft : TokenWithContext list) =
            match tokensLeft with
            | [] ->
                { includedTokens = tokensGathered
                  tokensLeft = List.empty }

            | head :: rest ->
                match head.token with
                | Whitespace _ -> traverser (tokensGathered @ [ head ]) rest
                | _ ->
                    if head.startLine <> blockHead.startLine // to ensure we're skipping the blockHead itself
                       && head.startCol <= blockHead.startCol then
                        { includedTokens = tokensGathered
                          tokensLeft = head :: rest }

                    else
                        traverser (tokensGathered @ [ head ]) rest

        traverser List.empty tokens


let parseBlock (parser : Parser<'a>) =
    Parser (fun record ->
        let partitioned = getBlock record.tokensLeft

        let result =
            runWithCtx
                parser
                { prevTokens = record.prevTokens
                  tokensLeft = partitioned.includedTokens
                  contextStack = record.contextStack }

        match result.parseResult with
        | ParsingSuccess s ->
            { parseResult = ParsingSuccess s
              prevTokens = result.prevTokens @ partitioned.includedTokens
              tokensLeft = result.tokensLeft @ partitioned.tokensLeft
              contextStack = record.contextStack }
        //ParsingSuccess
        //    { s with
        //        tokensLeft = s.tokensLeft @ partitioned.tokensLeft
        //        tokensChomped = s.tokensChomped @ partitioned.includedTokens }
        | NoParsingMatch x -> replaceParseResultWithCtx (NoParsingMatch x) result)





let parseUntilToken token (Parser p as parser) =
    Parser (fun record ->
        let rec traverser tokensChomped tokensLeft =
            match tokensLeft with
            | [] -> run parser tokensChomped
            | head :: rest ->
                if head.token = token then
                    let result = run parser tokensChomped

                    match result.parseResult with
                    //| ParsingSuccess (s, tokensLeft') -> ParsingSuccess (s, tokensLeft @ tokensLeft')
                    | ParsingSuccess s ->
                        { parseResult = ParsingSuccess s
                          prevTokens = result.prevTokens
                          tokensLeft = tokensLeft @ s.tokensLeft
                          contextStack = result.contextStack }
                    | NoParsingMatch x ->
                        { parseResult = NoParsingMatch x
                          prevTokens = result.prevTokens
                          tokensLeft = tokensLeft
                          contextStack = result.contextStack }

                else
                    traverser (tokensChomped @ [ head ]) rest

        traverser List.empty record.tokensLeft)


type SequenceConfig<'a> =
    { startToken : Token
      endToken : Token
      separator : Token
      spaces : Parser<unit>
      item : Parser<'a> }


let rec private postStartListParser config =
    (succeed (fun x xs -> x :: xs)

     |= config.item
     |. config.spaces
     |= either
         (succeed id
          |. symbol config.separator
          |. config.spaces
          |= postStartListParser config)

         (succeed List.empty
          |. symbol config.endToken
          |. config.spaces))


let rec sequence config =
    succeed id
    |. symbol config.startToken
    |. config.spaces
    |= postStartListParser config

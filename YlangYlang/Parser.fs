module Parser



type ParseErrWithCtx<'token, 'ctx, 'err> =
    { err : 'err
      prevTokens : 'token list
      contextStack : 'ctx list }

type OneOrMultipleErrs<'token, 'ctx, 'err> =
    | OneErr of ParseErrWithCtx<'token, 'ctx, 'err>
    | MultipleErrs of OneOrMultipleErrs<'token, 'ctx, 'err> list

type ParseResult<'a, 'token, 'ctx, 'err> =
    | ParsingSuccess of 'a
    | NoParsingMatch of OneOrMultipleErrs<'token, 'ctx, 'err>


type ParseContext<'token, 'ctx, 'err> =
    { contextStack : 'ctx list
      prevTokens : 'token list
      tokensLeft : 'token list
      committed : bool }

type ParseResultWithContext<'a, 'token, 'ctx, 'err> =
    { parseResult : ParseResult<'a, 'token, 'ctx, 'err>
      contextStack : 'ctx list
      prevTokens : 'token list
      tokensLeft : 'token list
      committed : bool }


type ParseFn<'a, 'token, 'ctx, 'err> =
    ParseContext<'token, 'ctx, 'err> -> ParseResultWithContext<'a, 'token, 'ctx, 'err>




type Parser<'a, 'token, 'ctx, 'err> = private | Parser of ParseFn<'a, 'token, 'ctx, 'err>



let blankParseCtx : ParseContext<'token, 'ctx, 'err> =
    { prevTokens = List.empty
      tokensLeft = List.empty
      contextStack = List.empty
      committed = false }

let makeParseResultWithCtx (result : ParseResult<'a, 'token, 'ctx, 'b>) (record : ParseContext<'token, 'ctx, 'err>) =
    { parseResult = result
      prevTokens = record.prevTokens
      tokensLeft = record.tokensLeft
      contextStack = record.contextStack
      committed = record.committed }

/// For continuing to parse from result
let private makeCtxFromParseResult
    (resultWithCtx : ParseResultWithContext<'a, 'token, 'ctx, 'b>)
    : ParseContext<'token, 'ctx, 'err> =
    { prevTokens = resultWithCtx.prevTokens
      tokensLeft = resultWithCtx.tokensLeft
      contextStack = resultWithCtx.contextStack
      committed = resultWithCtx.committed }

let private replaceParseResultWithCtx
    (result : ParseResult<'b, 'token, 'ctx, 'err>)
    (record : ParseResultWithContext<'a, 'token, 'ctx, 'err>)
    : ParseResultWithContext<'b, 'token, 'ctx, 'err> =
    { parseResult = result
      prevTokens = record.prevTokens
      tokensLeft = record.tokensLeft
      contextStack = record.contextStack
      committed = record.committed }

let addCtxToStack (ctx : 'ctx) (Parser parseFn) : Parser<'a, 'token, 'ctx, 'err> =
    Parser (fun record ->
        let newRecord = { record with contextStack = ctx :: record.contextStack }
        parseFn newRecord)





let private runWithCtx (Parser parseFn) parseCtx : ParseResultWithContext<'a, 'token, 'ctx, 'err> = parseFn parseCtx

let run parser (tokens : 'token list) : ParseResultWithContext<'a, 'token, 'ctx, 'err> =
    runWithCtx
        parser
        { prevTokens = List.empty
          tokensLeft = tokens
          contextStack = List.empty
          committed = false }


let getCtxFromStack (Parser parseFn : Parser<'a, 'token, 'ctx, 'err>) : 'ctx list =
    let result = parseFn blankParseCtx
    result.contextStack


/// Parser that always succeeds
let succeed a : Parser<'a, 'token, 'ctx, 'err> =
    Parser (makeParseResultWithCtx (ParsingSuccess a))

/// Parser that always fails
let fail : 'err -> Parser<'a, 'token, 'ctx, 'err> =
    fun err ->
        Parser (fun parseCtx ->
            parseCtx
            |> makeParseResultWithCtx (
                NoParsingMatch (
                    OneErr
                        { err = err
                          prevTokens = parseCtx.prevTokens
                          contextStack = parseCtx.contextStack }
                )
            ))







let mapResult
    (f : 'a -> 'b)
    (result : ParseResultWithContext<'a, 'token, 'ctx, 'err>)
    : ParseResultWithContext<'b, 'token, 'ctx, 'err> =
    { parseResult =
        match result with
        | { parseResult = ParsingSuccess s } -> ParsingSuccess (f s)
        | { parseResult = NoParsingMatch errs } -> NoParsingMatch errs
      prevTokens = result.prevTokens
      tokensLeft = result.tokensLeft
      contextStack = result.contextStack
      committed = result.committed }




let map f parser : Parser<'b, 'token, 'ctx, 'err> =
    Parser (fun ctx ->
        let result = runWithCtx parser ctx
        result |> mapResult f)


/// Essentially just flatten but implemented without relying on bind
let join : Parser<Parser<'a, 'token, 'ctx, 'err>, 'token, 'ctx, 'err> -> Parser<'a, 'token, 'ctx, 'err> =
    fun (Parser parseFn) ->
        Parser (fun context ->
            let result = parseFn context
            let newCtx = makeCtxFromParseResult result

            match result with
            | { parseResult = ParsingSuccess innerParser } -> runWithCtx innerParser newCtx
            | { parseResult = NoParsingMatch errs } -> makeParseResultWithCtx (NoParsingMatch errs) newCtx)


let bind f parser = map f parser |> join


let map2
    (f : 'a -> 'b -> 'c)
    (parserA : Parser<'a, 'token, 'ctx, 'err>)
    (parserB : Parser<'b, 'token, 'ctx, 'err>)
    : Parser<'c, 'token, 'ctx, 'err> =
    parserA
    |> map (fun a -> map (f a) parserB)
    |> join

let map3
    (f : 'a -> 'b -> 'c -> 'd)
    (parserA : Parser<'a, 'token, 'ctx, 'err>)
    (parserB : Parser<'b, 'token, 'ctx, 'err>)
    (parserC : Parser<'c, 'token, 'ctx, 'err>)
    : Parser<'d, 'token, 'ctx, 'err> =
    parserB
    |> map2 (fun a b -> map (f a b) parserC) parserA
    |> join


let either
    (parserA : Parser<'a, 'token, 'ctx, 'err>)
    (parserB : Parser<'a, 'token, 'ctx, 'err>)
    : Parser<'a, 'token, 'ctx, 'err> =
    Parser (fun record ->
        // @TODO: actually figure out the logic for committing to a path or not
        let isCurrentlyCommitted = record.committed

        match runWithCtx parserA record with
        | { parseResult = ParsingSuccess _ } as result -> { result with committed = isCurrentlyCommitted }
        | { parseResult = NoParsingMatch firstErrs } as result ->
            if result.committed then
                { result with committed = isCurrentlyCommitted }
            else
                match runWithCtx parserB record with
                | { parseResult = ParsingSuccess _ } as result -> result
                | { parseResult = NoParsingMatch sndErrs } ->
                    let errs =
                        match firstErrs, sndErrs with
                        | MultipleErrs [], _ -> sndErrs
                        | MultipleErrs list1, MultipleErrs list2 -> MultipleErrs (list1 @ list2)
                        | OneErr err, MultipleErrs list -> MultipleErrs (OneErr err :: list)
                        | MultipleErrs list, OneErr err -> MultipleErrs (list @ [ OneErr err ])
                        | OneErr err1, OneErr err2 ->
                            MultipleErrs [ OneErr err1
                                           OneErr err2 ]

                    makeParseResultWithCtx (NoParsingMatch errs) record)


let rec oneOf (parsers : Parser<'a, 'token, 'ctx, 'err> list) : Parser<'a, 'token, 'ctx, 'err> =
    match parsers with
    | [] -> Parser (makeParseResultWithCtx (NoParsingMatch (MultipleErrs List.empty)))
    | head :: tail -> either head (oneOf tail)






let lazyParser thunk : Parser<'a, 'token, 'ctx, 'err> =
    Parser (fun tokens ->
        let (Parser parse) = thunk ()
        parse tokens)



let keep
    (parserA : Parser<'a -> 'b, 'token, 'ctx, 'err>)
    (parserB : Parser<'a, 'token, 'ctx, 'err>)
    : Parser<'b, 'token, 'ctx, 'err> =
    map2 apply parserA parserB

let (|=) a b = keep a b


let skip (parserA : Parser<'keep, 'token, 'ctx, 'err>) (parserB : Parser<'ignore, 'token, 'ctx, 'err>) =
    map2 (fun a _ -> a) parserA parserB

let (|.) a b = skip a b


let ignore p = map ignore p


/// For when there are two paths to the same thing
let fork parserA parserB finalParser =
    either parserA parserB |> bind finalParser




let getOffset : Parser<int, 'token, 'ctx, 'err> =
    Parser (fun ctx -> makeParseResultWithCtx (ParsingSuccess <| List.length ctx.prevTokens) ctx)

let getSourceTokens : Parser<'token list, 'token, 'ctx, 'err> =
    Parser (fun ctx -> makeParseResultWithCtx (ParsingSuccess <| ctx.prevTokens @ ctx.tokensLeft) ctx)


let getSourceString tokenToString : Parser<string, 'token, 'ctx, 'err> =
    getSourceTokens
    |> map (List.map tokenToString >> String.ofSeq)



let rec chompWhileHelper
    contextList
    committed
    predicate
    tokensChomped
    tokensLeft
    : ParseResultWithContext<unit, 'token, 'ctx, 'err> =
    match tokensLeft with
    | [] ->
        { prevTokens = tokensChomped
          parseResult = ParsingSuccess ()
          tokensLeft = tokensLeft
          contextStack = contextList
          committed = committed }
    | head :: rest ->
        if predicate head then
            chompWhileHelper contextList committed predicate (tokensChomped @ [ head ]) rest
        else
            { prevTokens = tokensChomped
              parseResult = ParsingSuccess ()
              tokensLeft = head :: rest
              contextStack = contextList
              committed = committed }





let rec chompWhile predicate : Parser<unit, 'token, 'ctx, 'err> =
    Parser (fun record ->
        chompWhileHelper record.contextStack record.committed predicate record.prevTokens record.tokensLeft)




let any () = chompWhile (always true)




let tee f parser =
    Parser (fun record ->
        f record
        runWithCtx parser record)




let splitParser chomper parser : Parser<'a, 'token, 'ctx, 'err> =
    Parser (fun ctx ->
        let chomped = chomper ctx
        let newCtx = { ctx with tokensLeft = chomped }
        let parseResult = runWithCtx parser newCtx

        let diff =
            List.length parseResult.prevTokens
            - List.length ctx.prevTokens

        { parseResult with
            tokensLeft =
                parseResult.tokensLeft
                @ List.skip diff ctx.tokensLeft }

    )




let parseWhile
    (combine : 'a -> 'a -> 'a)
    (chomper : 'token list -> (ParseResult<'a, 'token, 'ctx, 'err> * 'token list))
    : Parser<'a, 'token, 'ctx, 'err> =
    let rec traverser (ctx : ParseContext<'token, 'ctx, 'err>) : ParseResultWithContext<'a, 'token, 'ctx, 'err> =
        let (result, chomped) = chomper ctx.tokensLeft

        match result with
        | ParsingSuccess success ->
            let newCtx =
                { contextStack = ctx.contextStack
                  prevTokens = ctx.prevTokens @ chomped
                  tokensLeft = List.skip (List.length chomped) ctx.tokensLeft
                  committed = ctx.committed }

            mapResult (combine success) (traverser newCtx)
        | NoParsingMatch errs -> makeParseResultWithCtx (NoParsingMatch errs) ctx

    Parser traverser



let parseSimple (chomper : 'token list -> (Result<'a, 'err> * 'token list)) : Parser<'a, 'token, 'ctx, 'err> =
    Parser (fun ctx ->
        let (result, chomped) = chomper ctx.tokensLeft

        let parseResult =
            match result with
            | Ok res -> ParsingSuccess res
            | Error err ->
                NoParsingMatch (
                    OneErr
                        { err = err
                          prevTokens = ctx.prevTokens
                          contextStack = ctx.contextStack }
                )

        { parseResult = parseResult
          contextStack = ctx.contextStack
          prevTokens = ctx.prevTokens @ chomped
          tokensLeft = List.skip (List.length chomped) ctx.tokensLeft
          committed = ctx.committed })





/// Parse a single token, with potential for different errors between matchers and no tokens left
let parseSingleToken (noTokensLeftErr : 'err) matcher : Parser<'a, 'token, 'ctx, 'err> =
    parseSimple (fun tokensLeft ->
        match tokensLeft with
        | head :: _ ->
            match matcher head with
            | Ok res -> Ok res, List.singleton head
            | Error err -> Error err, List.empty
        | [] -> Error noTokensLeftErr, List.empty)







let rec repeat (Parser parseFn : Parser<'a, 'token, 'ctx, 'err>) : Parser<'a list, 'token, 'ctx, 'err> =
    let rec traverser (ctx : ParseContext<'token, 'ctx, 'err>) : ParseResultWithContext<'a list, 'token, 'ctx, 'err> =
        match parseFn ctx with
        | { parseResult = ParsingSuccess success } as result ->
            makeCtxFromParseResult result
            |> traverser
            |> mapResult (fun list -> success :: list)

        | { parseResult = NoParsingMatch _ } -> makeParseResultWithCtx (ParsingSuccess List.empty) ctx

    Parser traverser





let oneOrMore (parser : Parser<'a, 'token, 'ctx, 'err>) : Parser<NEL<'a>, 'token, 'ctx, 'err> =
    succeed NEL.consFromList
    |= parser
    |= repeat parser




let opt (parser : Parser<'a, 'token, 'ctx, 'err>) : Parser<'a option, 'token, 'ctx, 'err> =
    Parser (fun record ->
        match runWithCtx parser record with
        | { parseResult = ParsingSuccess s } as result -> replaceParseResultWithCtx (ParsingSuccess <| Some s) result
        | { parseResult = NoParsingMatch _ } -> makeParseResultWithCtx (ParsingSuccess None) record)



let commit =
    Parser (fun ctx -> makeParseResultWithCtx (ParsingSuccess ()) { ctx with committed = true })


let uncommit =
    Parser (fun ctx -> makeParseResultWithCtx (ParsingSuccess ()) { ctx with committed = false })


//let parseUntilToken token (Parser p as parser) =
//    Parser (fun record ->
//        let rec traverser parseCtx =
//            match parseCtx.tokensLeft with
//            | [] -> runWithCtx parser parseCtx
//            | head :: rest ->
//                if head.token = token then
//                    let result = run parser tokensChomped

//                    match result.parseResult with
//                    //| ParsingSuccess (s, tokensLeft') -> ParsingSuccess (s, tokensLeft @ tokensLeft')
//                    | ParsingSuccess s ->
//                        { parseResult = ParsingSuccess s
//                          prevTokens = result.prevTokens
//                          tokensLeft = tokensLeft @ s.tokensLeft
//                          contextStack = result.contextStack }
//                    | NoParsingMatch x ->
//                        { parseResult = NoParsingMatch x
//                          prevTokens = result.prevTokens
//                          tokensLeft = tokensLeft
//                          contextStack = result.contextStack }

//                else
//                    traverser (tokensChomped @ [ head ]) rest

//        traverser List.empty record.tokensLeft)


//type SequenceConfig<'a, 'token, 'ctx, 'err> =
//    { startToken : 'token
//      endToken : 'token
//      separator : 'token
//      spaces : Parser<unit, 'token, 'ctx, 'err>
//      item : Parser<'a, 'token, 'ctx, 'err> }


//let rec private postStartListParser config =
//    (succeed (fun x xs -> x :: xs)

//     |= config.item
//     |. config.spaces
//     |= either
//         (succeed id
//          |. symbol config.separator
//          |. config.spaces
//          |= postStartListParser config)

//         (succeed List.empty
//          |. symbol config.endToken
//          |. config.spaces))


//let rec sequence config =
//    succeed id
//    |. symbol config.startToken
//    |. config.spaces
//    |= postStartListParser config

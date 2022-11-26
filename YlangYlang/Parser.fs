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





//type ParsingSuccess<'a> = 'a

//type ParseFailure =  ParserError


type ParseResult<'a> =
    | ParsingSuccess of 'a
    | NoParsingMatch of ParserError


type ParseContext<'ctx> =
    { prevTokens : TokenWithContext list
      tokensLeft : TokenWithContext list
      contextList : 'ctx list }

type ParseResultWithContext<'a, 'ctx> =
    { parseResult : ParseResult<'a>
      prevTokens : TokenWithContext list
      tokensLeft : TokenWithContext list
      contextList : 'ctx list }


type ParseFn<'a, 'ctx> = ParseContext<'ctx> -> ParseResultWithContext<'a, 'ctx>




type Parser<'a, 'ctx> = private | Parser of ParseFn<'a, 'ctx>


let addCtxToStack (ctx : 'ctx) (Parser parseFn) : Parser<'a, 'ctx> =
    Parser (fun record ->
        let newRecord = { record with contextList = ctx :: record.contextList }
        parseFn newRecord)




let makeWithCtx (ctx : 'ctx) (parseFn : ParseFn<'a, 'ctx>) =

    addCtxToStack ctx (Parser parseFn)


let run (Parser parseFn) (tokens : TokenWithContext list) : ParseResultWithContext<'a, 'ctx> =
    parseFn
        // @TODO: not sure if I need to allow for existing previous tokens and context stack or not...
        { prevTokens = List.empty
          tokensLeft = tokens
          contextList = List.empty }




//let private bindHelper (bind' : TokenWithContext list -> 'a -> 'ctx list -> ParseResult<'b>) (Parser p as parser) =
//    Parser
//        { parseFn =
//            fun tokens ctxList ->
//                let parseResult = run parser

//                match parseResult.parseResult with
//                | NoParsingMatch e ->
//                    { parseResult = NoParsingMatch e
//                      contextList = ctxList }

//                | ParsingSuccess s ->
//                    { parseResult =
//                        match bind' s.tokensLeft s.result ctxList with
//                        | NoParsingMatch e -> NoParsingMatch e
//                        | ParsingSuccess s -> ParsingSuccess s
//                      contextList = ctxList }

//          contextStack = p.contextStack }


//let bind (f : 'a -> Parser<'b, 'ctx>) (Parser p as parser : Parser<'a, 'ctx>) : Parser<'b, 'ctx> =

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


let bind (f : 'a -> Parser<'b, 'ctx>) (Parser parseFn : Parser<'a, 'ctx>) : Parser<'b, 'ctx> =
    Parser (fun (context : ParseContext<'ctx>) ->
        let firstResult = parseFn context

        match firstResult.parseResult with
        | NoParsingMatch err ->
            { parseResult = NoParsingMatch err
              prevTokens = firstResult.prevTokens
              tokensLeft = firstResult.tokensLeft
              contextList = firstResult.contextList }

        | ParsingSuccess result ->
            // @TODO: not sure if this quite makes sense, but let's see.
            run (f result) firstResult.tokensLeft)

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



//let map (f : 'a -> 'b) (Parser p as parser : Parser<'a, 'ctx>) : Parser<'b, 'ctx> =
//    parser
//    |> bind (fun (s : 'a) ->
//        (fun tokens ctxs ->
//            { parseResult = ParsingSuccess { result = f s; tokensLeft = tokens }
//              contextList = ctxs })
//        |> makeWithCtx UnknownLabel)

let map (f : 'a -> 'b) (parser : Parser<'a, 'ctx>) : Parser<'b, 'ctx> =
    parser
    |> bind (fun (s : 'a) ->
        Parser (fun record ->
            { parseResult = ParsingSuccess (f s)
              prevTokens = record.prevTokens
              tokensLeft = record.tokensLeft
              contextList = record.contextList }))






let flatten : Parser<Parser<'a, 'ctx>, 'ctx> -> Parser<'a, 'ctx> =
    fun parser -> bind id parser






let map2 (f : 'a -> 'b -> 'c) (parserA : Parser<'a, 'ctx>) (parserB : Parser<'b, 'ctx>) : Parser<'c, 'ctx> =
    parserA
    |> map (fun a -> map (f a) parserB)
    |> flatten

let either (parserA : Parser<'a, 'ctx>) (parserB : Parser<'a, 'ctx>) : Parser<'a, 'ctx> =
    fun token _ ->
        match run parserA token with
        | ParsingSuccess s -> ParsingSuccess s
        | NoParsingMatch _ -> run parserB token
    |> makeWithCtx UnknownLabel

let rec oneOf (parsers : Parser<'a> list) : Parser<'a> =
    match parsers with
    | [] ->
        makeWithCtx UnknownLabel (fun _ ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = NoParsersLeft })
    | head :: rest -> either head (oneOf rest)

/// Parser that always succeeds
let succeed a : Parser<'a> =
    makeWithCtx UnknownLabel (fun tokens ->
        ParsingSuccess
            { tokensChomped = List.empty
              result = a
              tokensLeft = tokens })

let fail : ParserError -> Parser<'a> =
    fun err ->
        makeWithCtx UnknownLabel (fun _ ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = err })

let lazyParser thunk =
    makeWithCtx UnknownLabel (fun tokens ->
        let (Parser parse) = thunk ()
        parse.parseFn tokens)



let keep (parserA : Parser<'a -> 'b>) (parserB : Parser<'a>) : Parser<'b> = map2 apply parserA parserB

let (|=) a b = keep a b


let skip (parserA : Parser<'keep>) (parserB : Parser<'ignore>) = map2 (fun a _ -> a) parserA parserB

let (|.) a b = skip a b


let ignore p = map ignore p


/// For when there are two paths to the same thing
let fork parserA parserB finalParser =
    either parserA parserB |> bind finalParser

/// `end` is a keyword in F# so have to use `isEnd`
let isEnd =
    makeWithCtx UnknownLabel (fun tokens ->
        match tokens with
        | [] ->
            ParsingSuccess
                { tokensChomped = List.empty
                  result = ()
                  tokensLeft = List.empty }
        | _ ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = ExpectedEndOfExpression })


let rec chompWhileHelper predicate tokensChomped tokensLeft =
    match tokensLeft with
    | [] ->
        ParsingSuccess
            { tokensChomped = tokensChomped
              result = ()
              tokensLeft = List.empty }
    | head :: rest ->
        if predicate head then
            chompWhileHelper predicate (tokensChomped @ [ head ]) rest
        else
            ParsingSuccess
                { tokensChomped = tokensChomped
                  result = ()
                  tokensLeft = head :: rest }

let rec chompWhile predicate : Parser<unit> =
    chompWhileHelper predicate List.empty
    |> makeWithCtx UnknownLabel



let any = chompWhile (always true)


let printTokensAsText (tokens : TokenWithContext list) =
    tokens
    |> List.fold (fun charList t -> charList + String.ofSeq t.chars) ""

let tee f parser =
    makeWithCtx UnknownLabel (fun tokens ->
        f tokens
        run parser tokens)


let symbol expectedToken : Parser<unit> =
    makeWithCtx UnknownLabel (function
        | [] ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = UnexpectedEndOfExpression <| Some expectedToken }
        | nextToken :: rest ->
            if expectedToken = nextToken.token then
                ParsingSuccess
                    { tokensChomped = List.singleton nextToken
                      result = ()
                      tokensLeft = rest }

            else
                NoParsingMatch
                    { tokensChomped = List.empty
                      label = UnknownLabel
                      error = ExpectedToken expectedToken })


let ifMatches predicate : Parser<unit> = chompWhile predicate

/// Matches and maps over single token
let matchCtxToken chooser =
    makeWithCtx UnknownLabel (function
        | [] ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = UnexpectedEndOfExpression None }
        //(UnknownLabel, UnexpectedEndOfExpression None)
        | nextToken :: rest ->
            match chooser nextToken with
            | Some x ->
                ParsingSuccess
                    { tokensChomped = List.singleton nextToken
                      result = x
                      tokensLeft = rest }
            //(x, rest)
            | None ->
                NoParsingMatch
                    { tokensChomped = List.empty
                      label = UnknownLabel
                      error = PredicateDidntMatch })
//(UnknownLabel, PredicateDidntMatch))

let matchSingleToken f = matchCtxToken (fun t -> f t.token)

/// If you need access to the matched token itself use `matchSingleToken`
let parseToken expectedToken f =
    matchSingleToken (fun token ->
        if token = expectedToken then
            Some f
        else
            None)




let rec repeat (Parser p as parser : Parser<'a>) : Parser<'a list> =
    makeWithCtx UnknownLabel (fun tokens ->
        let rec traverser state tokensChomped tokensRemaining =
            tokensRemaining
            |> run parser
            |> function
                | ParsingSuccess s -> traverser (s.result :: state) s.tokensChomped s.tokensLeft
                | NoParsingMatch _ ->
                    ParsingSuccess
                        { tokensChomped = tokensChomped
                          result = state
                          tokensLeft = tokensRemaining }
        //(state, tokensRemaining)


        traverser List.empty p.tokensChomped tokens)
    |> map List.rev

let oneOrMore (parser : Parser<_>) : Parser<_> =
    map2 NEL.consFromList parser (repeat parser)


let opt parser =
    makeWithCtx UnknownLabel (fun tokens ->
        match run parser tokens with
        | ParsingSuccess s ->
            ParsingSuccess
                { tokensLeft = s.tokensLeft
                  result = Some s.result
                  tokensChomped = s.tokensChomped }
        | NoParsingMatch e ->
            ParsingSuccess
                { result = None
                  tokensLeft = tokens
                  tokensChomped = List.empty }
    //(None, tokens)
    )


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
    makeWithCtx UnknownLabel (fun tokens ->
        let partitioned = getBlock tokens

        match run parser partitioned.includedTokens with
        //| ParsingSuccess (s, tokensLeft) -> ParsingSuccess (s, tokensLeft @ partitioned.tokensLeft)
        | ParsingSuccess s ->
            ParsingSuccess
                { s with
                    tokensLeft = s.tokensLeft @ partitioned.tokensLeft
                    tokensChomped = s.tokensChomped @ partitioned.includedTokens }
        | NoParsingMatch x -> NoParsingMatch x)





let parseUntilToken token (Parser p as parser) =
    makeWithCtx UnknownLabel (fun tokens ->
        let rec traverser tokensChomped tokensLeft =
            match tokensLeft with
            | [] -> run parser tokensChomped
            | head :: rest ->
                if head.token = token then
                    match run parser tokensChomped with
                    //| ParsingSuccess (s, tokensLeft') -> ParsingSuccess (s, tokensLeft @ tokensLeft')
                    | ParsingSuccess s -> ParsingSuccess { s with tokensLeft = tokensLeft @ s.tokensLeft }
                    | NoParsingMatch x -> NoParsingMatch x
                else
                    traverser (tokensChomped @ [ head ]) rest

        traverser List.empty tokens)


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

module Parser

open Lexer


type Label =
    | Label of string
    | UnknownLabel


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


type ParseResult<'a> =
    | ParsingSuccess of ('a * TokenWithContext list)
    | NoParsingMatch of (Label * ParserError)

/// Where the branch matched but threw a fatal parsing error (i.e. non-backtrackable)
/// Add this back in when we make the parsing more like Parser.Advanced than Parser.Simple
/// although even then the result isn't a separate variant, but we carry the errors with us in the parser! (I think)
/// well, running the parser does result in a Result type (heheh), but we accumulate the lists of dead ends along with us, I think
//| ParsingError of ParserError

type private ParserRecord<'a> =
    { parseFn : (TokenWithContext list -> ParseResult<'a>)
      label : Label }

type Parser<'a> = private Parser of ParserRecord<'a>


let setLabel newLabel (Parser parser) =
    let newInnerFn input =
        let result = parser.parseFn input

        match result with
        | ParsingSuccess s -> ParsingSuccess s
        | NoParsingMatch (_, err) -> NoParsingMatch (Label newLabel, err)

    Parser
        { parseFn = newInnerFn
          label = Label newLabel }

let getLabel (Parser parser) = parser.label

let setParseFn fn (Parser parser) =
    Parser { label = parser.label; parseFn = fn }

let setParseFnFlip p f = setParseFn f p

let makeWithLabel label fn = Parser { label = label; parseFn = fn }


let run (Parser parser) tokens = parser.parseFn tokens


let bind (f : 'a -> Parser<'b>) (parser : Parser<'a>) : Parser<'b> =
    (fun tokens ->
        run parser tokens
        |> function
            | ParsingSuccess (s, tokens) -> run (f s) tokens
            | NoParsingMatch x -> NoParsingMatch x)
    |> makeWithLabel UnknownLabel



let map (f : 'a -> 'b) (parser : Parser<'a>) : Parser<'b> =
    parser
    |> bind (fun s ->
        (fun tokens -> ParsingSuccess (f s, tokens))
        |> makeWithLabel UnknownLabel)

let flatten : Parser<Parser<'a>> -> Parser<'a> = fun parser -> parser |> bind id






let map2 (f : 'a -> 'b -> 'c) (parserA : Parser<'a>) (parserB : Parser<'b>) : Parser<'c> =
    parserA
    |> map (fun a -> map (fun b -> f a b) parserB)
    |> flatten

let either (parserA : Parser<'a>) (parserB : Parser<'a>) : Parser<'a> =
    fun token ->
        match run parserA token with
        | ParsingSuccess s -> ParsingSuccess s
        | NoParsingMatch _ -> run parserB token
    |> makeWithLabel UnknownLabel

let rec oneOf (parsers : Parser<'a> list) : Parser<'a> =
    match parsers with
    | [] -> makeWithLabel UnknownLabel (fun _ -> NoParsingMatch (UnknownLabel, NoParsersLeft))
    | head :: rest -> either head (oneOf rest)

/// Parser that always succeeds
let succeed a : Parser<'a> =
    makeWithLabel UnknownLabel (fun tokens -> ParsingSuccess (a, tokens))

let fail : ParserError -> Parser<'a> =
    fun err -> makeWithLabel UnknownLabel (fun _ -> NoParsingMatch (UnknownLabel, err))

let lazyParser thunk =
    makeWithLabel UnknownLabel (fun tokens ->
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
    makeWithLabel UnknownLabel (fun tokens ->
        match tokens with
        | [] -> ParsingSuccess ((), List.empty)
        | _ -> NoParsingMatch (UnknownLabel, ExpectedEndOfExpression))


let rec chompWhileHelper predicate tokens =
    match tokens with
    | [] -> ParsingSuccess ((), List.empty)
    | head :: rest ->
        if predicate head then
            chompWhileHelper predicate rest
        else
            ParsingSuccess ((), head :: rest)

let rec chompWhile predicate : Parser<unit> =
    chompWhileHelper predicate
    |> makeWithLabel UnknownLabel



let any = chompWhile (always true)


let printTokensAsText (tokens : TokenWithContext list) =
    tokens
    |> List.fold (fun charList t -> charList + String.ofSeq t.chars) ""

let tee f parser =
    makeWithLabel UnknownLabel (fun tokens ->
        f tokens
        run parser tokens)


let symbol expectedToken : Parser<unit> =
    makeWithLabel UnknownLabel (function
        | [] -> NoParsingMatch (UnknownLabel, UnexpectedEndOfExpression <| Some expectedToken)
        | nextToken :: rest ->
            if expectedToken = nextToken.token then
                ParsingSuccess ((), rest)
            else
                NoParsingMatch (UnknownLabel, ExpectedToken expectedToken))


let ifMatches predicate : Parser<unit> = chompWhile predicate

/// Matches and maps over single token
let matchCtxToken chooser =
    makeWithLabel UnknownLabel (function
        | [] -> NoParsingMatch (UnknownLabel, UnexpectedEndOfExpression None)
        | nextToken :: rest ->
            match chooser nextToken with
            | Some x -> ParsingSuccess (x, rest)
            | None -> NoParsingMatch (UnknownLabel, PredicateDidntMatch))

let matchSingleToken f = matchCtxToken (fun t -> f t.token)

/// If you need access to the matched token itself use `matchSingleToken`
let parseToken expectedToken f =
    matchSingleToken (fun token ->
        if token = expectedToken then
            Some f
        else
            None)




let rec repeat (parser : Parser<'a>) : Parser<'a list> =
    makeWithLabel UnknownLabel (fun tokens ->
        let rec traverser state tokensRemaining =
            tokensRemaining
            |> run parser
            |> function
                | ParsingSuccess (s, remainingTokens) -> traverser (s :: state) remainingTokens
                | NoParsingMatch _ -> ParsingSuccess (state, tokensRemaining)


        traverser List.empty tokens)
    |> map List.rev

let oneOrMore (parser : Parser<_>) : Parser<_> =
    map2 NEL.consFromList parser (repeat parser)


let opt parser =
    makeWithLabel UnknownLabel (fun tokens ->
        match run parser tokens with
        | ParsingSuccess (s, t) -> ParsingSuccess (Some s, t)
        | NoParsingMatch _ -> ParsingSuccess (None, tokens))


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


/// Parse block with parserA and then the rest with parserB
let parseBlock (combine : 'a -> 'b -> 'c) (parserA : Parser<'a>) (parserB : Parser<'b>) : Parser<'c> =
    makeWithLabel UnknownLabel (fun tokens ->
        let partitioned = getBlock tokens

        let parserA' =
            makeWithLabel UnknownLabel (fun _ -> run parserA partitioned.includedTokens)

        let parserB' =
            makeWithLabel UnknownLabel (fun _ -> run parserB partitioned.tokensLeft)

        run (map2 combine parserA' parserB') List.empty)



let parseUntilToken token (Parser p as parser) =
    makeWithLabel UnknownLabel (fun tokens ->
        let rec traverser tokensChomped tokensLeft =
            match tokensLeft with
            | [] -> run parser tokensChomped
            | head :: rest ->
                if head.token = token then
                    match run parser tokensChomped with
                    | ParsingSuccess (s, tokensLeft') -> ParsingSuccess (s, tokensLeft @ tokensLeft')
                    | NoParsingMatch x -> NoParsingMatch x
                else
                    traverser (tokensChomped @ [ head ]) rest


        traverser List.empty tokens

    )






//let rec skipIfAlreadyTried alreadyTriedTokens parser =
//    Parser
//    <| fun tokens ->
//        if tokens = alreadyTriedTokens then
//            NoParsingMatch
//        else
//            inspectTokens (skipIfAlreadyTried alreadyTriedTokens) parser

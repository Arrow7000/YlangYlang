module Parser

open Lexer


type ParserError =
    | TokenNotValidHere of TokenWithContext

    /// but there were yet more tokens
    | ExpectedEndOfExpression

    /// but there were no tokens left
    | UnexpectedEndOfExpression


type ParseResult<'a> =
    private
    | ParsingSuccess of ('a * TokenWithContext list)
    /// Where this branch didn't match but you could try other parsers (i.e. it's backtrackable)
    | NoParsingMatch

/// Where the branch matched but threw a fatal parsing error (i.e. non-backtrackable)
/// Add this back in when we make the parsing more like Parser.Advanced than Parser.Simple
/// although even then the result isn't a separate variant, but we carry the errors with us in the parser! (I think)
/// well, running the parser does result in a Result type (heheh), but we accumulate the lists of dead ends along with us, I think
//| ParsingError of ParserError

type Parser<'a> = private Parser of (TokenWithContext list -> ParseResult<'a>)


let run (Parser parser) tokens = parser tokens

let bind (f : 'a -> Parser<'b>) (parser : Parser<'a>) : Parser<'b> =
    Parser
    <| fun tokens ->
        run parser tokens
        |> function
            | ParsingSuccess (s, tokens) -> run (f s) tokens
            | NoParsingMatch -> NoParsingMatch


let map (f : 'a -> 'b) (parser : Parser<'a>) : Parser<'b> =
    parser
    |> bind (fun s -> Parser (fun tokens -> ParsingSuccess (f s, tokens)))

let flatten : Parser<Parser<'a>> -> Parser<'a> = fun parser -> parser |> bind id






let map2 (f : 'a -> 'b -> 'c) (parserA : Parser<'a>) (parserB : Parser<'b>) : Parser<'c> =
    parserA
    |> map (fun a -> map (fun b -> f a b) parserB)
    |> flatten

let either (parserA : Parser<'a>) (parserB : Parser<'a>) : Parser<'a> =
    Parser
    <| fun token ->
        match run parserA token with
        | ParsingSuccess s -> ParsingSuccess s
        | NoParsingMatch -> run parserB token

let rec oneOf (parsers : Parser<'a> list) : Parser<'a> =
    match parsers with
    | [] -> Parser (fun _ -> NoParsingMatch)
    | head :: rest -> either head (oneOf rest)

/// Parser that always succeeds
let succeed a : Parser<'a> =
    Parser (fun tokens -> ParsingSuccess (a, tokens))

let fail : Parser<'a> = Parser (fun _ -> NoParsingMatch)

let lazyParser thunk =
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
let isEnd =
    Parser (fun tokens ->
        match tokens with
        | [] -> ParsingSuccess ((), List.empty)
        | _ -> NoParsingMatch)


let rec chompWhileHelper predicate tokens =
    match tokens with
    | [] -> ParsingSuccess ((), List.empty)
    | head :: rest ->
        if predicate head then
            chompWhileHelper predicate tokens
        else
            ParsingSuccess ((), head :: rest)

let rec chompWhile predicate : Parser<unit> = chompWhileHelper predicate |> Parser




let symbol expectedToken : Parser<unit> =
    Parser
    <| function
        | [] -> NoParsingMatch
        | nextToken :: rest ->
            if expectedToken = nextToken.token then
                ParsingSuccess ((), rest)
            else
                NoParsingMatch



let ifMatches predicate : Parser<unit> = chompWhile predicate

/// Matches and maps over single token
let matchCtxToken chooser =
    Parser
    <| function
        | [] -> NoParsingMatch
        | nextToken :: rest ->
            match chooser nextToken with
            | Some x -> ParsingSuccess (x, rest)
            | None -> NoParsingMatch

let matchSingleToken f = matchCtxToken (fun t -> f t.token)

/// If you need access to the matched token itself use `matchSingleToken`
let parseToken expectedToken f =
    matchSingleToken (fun token ->
        if token = expectedToken then
            Some f
        else
            None)




let rec repeat (parser : Parser<'a>) : Parser<'a list> =
    Parser (fun tokens ->
        let rec traverser state tokensRemaining =
            tokensRemaining
            |> run parser
            |> function
                | ParsingSuccess (s, remainingTokens) -> traverser (s :: state) remainingTokens
                | NoParsingMatch -> ParsingSuccess (state, tokensRemaining)


        traverser List.empty tokens)
    |> map List.rev

let oneOrMore (parser : Parser<_>) : Parser<_> =
    map2 NEL.consFromList parser (repeat parser)



let spaces : Parser<unit> =
    repeat (
        matchSingleToken (function
            | Whitespace _ -> Some ()
            | _ -> None)
    )
    |> ignore

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


//type ParsingContext<'ctx> =




type ParsingSuccess<'a> =
    { tokensChomped : TokenWithContext list
      result : 'a
      tokensLeft : TokenWithContext list }

type ParseFailure =
    { tokensChomped : TokenWithContext list
      label : Label
      error : ParserError }

type ParseResult<'a> =
    | ParsingSuccess of ParsingSuccess<'a>
    | NoParsingMatch of ParseFailure



/// First param is tokens left to chomp, second params is the tokens already chomped
//type ParseFn<'a> = TokenWithContext list -> TokenWithContext list -> ParseResult<'a>
type ParseFn<'a> = TokenWithContext list -> ParseResult<'a>

type private ParserRecord<'a> =
    { parseFn : ParseFn<'a>
      tokensChomped : TokenWithContext list
    //label : Label
     }

type Parser<'a> = private | Parser of ParserRecord<'a>



let setLabelOnFailure label (failure : ParseFailure) = { failure with label = Label label }

let setLabel newLabel (Parser parser) =
    let newInnerFn input =
        let result = parser.parseFn input

        match result with
        | ParsingSuccess s -> ParsingSuccess s
        | NoParsingMatch e -> NoParsingMatch (setLabelOnFailure newLabel e)

    Parser
        { parseFn = newInnerFn
          tokensChomped = parser.tokensChomped
        //label = Label newLabel
        }


let setParseFn fn (Parser parser) =
    Parser
        {
          //label = parser.label
          tokensChomped = parser.tokensChomped
          parseFn = fn }


let makeWithLabel label fn =
    Parser
        {
          // label = label
          tokensChomped = List.empty
          parseFn = fn }


let run (Parser parser) tokens = parser.parseFn tokens


let bind (f : 'a -> Parser<'b>) (parser : Parser<'a>) : Parser<'b> =
    (fun tokens ->
        run parser tokens
        |> function
            | ParsingSuccess s -> run (f s.result) tokens
            | NoParsingMatch x -> NoParsingMatch x)
    |> makeWithLabel UnknownLabel



let map (f : 'a -> 'b) (Parser p as parser : Parser<'a>) : Parser<'b> =
    parser
    |> bind (fun (s : 'a) ->
        (fun tokens ->
            ParsingSuccess
                { tokensChomped = p.tokensChomped
                  result = f s
                  tokensLeft = tokens })
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
    | [] ->
        makeWithLabel UnknownLabel (fun _ ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = NoParsersLeft })
    | head :: rest -> either head (oneOf rest)

/// Parser that always succeeds
let succeed a : Parser<'a> =
    makeWithLabel UnknownLabel (fun tokens ->
        ParsingSuccess
            { tokensChomped = List.empty
              result = a
              tokensLeft = tokens })

let fail : ParserError -> Parser<'a> =
    fun err ->
        makeWithLabel UnknownLabel (fun _ ->
            NoParsingMatch
                { tokensChomped = List.empty
                  label = UnknownLabel
                  error = err })

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
    makeWithLabel UnknownLabel (function
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
    makeWithLabel UnknownLabel (fun tokens ->
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
    makeWithLabel UnknownLabel (fun tokens ->
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
    makeWithLabel UnknownLabel (fun tokens ->
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
    makeWithLabel UnknownLabel (fun tokens ->
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

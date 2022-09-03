module Lexer

open System
open System.Text.RegularExpressions


/// This should probably only represent errors and not actually be used as the source for the lexers, cos that would be annoying to have to map a function for every variant when I can just have the functions there directly
type CharacterClass =
    | Digit
    | Alphabetical
    | AlphaNumeric
    | Whitespace

type ParseError =
    | WrongCharacterClass of expectedChar : CharacterClass
    | TabsNotAllowed
    | UnknownCharacter of char
    | CouldntRecognise of string

// @TODO: at some point include the line and col numbers along with the errors, or even just with the tokens tbh
type ParseErrors = NonEmptyList<ParseError>

//type CharacterGotStuckOn =
//    { char : char
//      contextSoFar : char list
//      error : ParseError }

//type TokenParseState<'a> =
//    | StillGoing of 'a
//    | Stopped
//    | ParseError of CharacterGotStuckOn


type WhitespaceChar =
    | Space
    | NewLine

type Token =
    | Int of uint
    | Whitespace of WhitespaceChar list

/// Not yet used, but to add later
type TokenWithContext =
    { token : Token
      line : uint // is 1-indexed
      col : uint // the col of the starting character. Is 1-indexed.
      numOfChars : uint } // I don't think any token spans multiple lines so this should be fine

type LexingState =
    | NoMatch of ParseErrors option // there may or may not be a reason why it didn't match
    | Success of token : Token * charsChomped : uint



type LexingResult = Result<Token list, ParseErrors>


type Matcher = string -> LexingState




/// You probably want to use `getMatchAtStart`
let getMatch pattern input =
    let m = Regex.Match (input, pattern)
    if m.Success then Some m.Value else None

/// Prepends a ^ at the start of your search so you don't have to remember it each time. Don't say I don't do anything for you ;)
let getMatchAtStart pattern (input : string) =
    // This basically enforces that the match has to be at the start of the string
    getMatch ($"^(?:{pattern})") input


let (|SingleCharRegex|_|) pattern input =
    let result = getMatchAtStart pattern <| Char.ToString input

    match result with
    | Some res ->
        match Seq.toList res with
        | [ c ] -> Some c
        | _ -> None
    | None -> None

let (|MultiCharRegex|_|) pattern input = getMatchAtStart pattern input


let getUpToNextWhitespace string =
    match string with
    | MultiCharRegex "[^\s]+" chars -> Some chars
    | _ -> None






let intMatcher allFileChars =
    match allFileChars with
    | MultiCharRegex "\d+" digits ->
        match UInt32.TryParse (digits) with
        | true, num -> Success (Int num, String.length digits |> uint)
        | false, _ ->
            // Should never happen since we've matched on only digit chars, but just in case
            NoMatch (Some <| NEL.make (WrongCharacterClass Digit))
    | _ -> NoMatch None


let whitespaceMatcher allFileChars =
    match allFileChars with
    | MultiCharRegex "\s+" chars ->
        // Need to handle CRLF files so that we don't think there's double the newlines than there actually are
        let mapWhitespaceChar c =
            match c with
            | '\r' -> Ok NewLine
            | '\n' -> Ok NewLine
            | ' ' -> Ok Space
            | '\t' -> Error TabsNotAllowed
            | c' -> Error <| UnknownCharacter c'

        let tokensResult =
            chars
            |> Seq.map mapWhitespaceChar
            |> Seq.toList
            |> Result.anyErrors

        match tokensResult with
        | Ok tokens' -> Success (Whitespace tokens', List.length tokens' |> uint)
        | Error errs -> NoMatch (NEL.fromList errs)
    | _ -> NoMatch None




let justKeepLexing (allMatchers : Matcher list) string =
    let getFirstMatch string =
        allMatchers
        |> List.fold
            (fun state matcher ->
                match state with
                | Success (token, chars) -> Success (token, chars)
                | NoMatch errOpt1 ->
                    match matcher string with
                    | Success (token, chars) -> Success (token, chars)
                    | NoMatch errOpt2 -> NoMatch (Option.combine NEL.append errOpt1 errOpt2))
            (NoMatch None)
        |> function
            | Success (t, c) -> Success (t, c)
            | NoMatch errOpt ->
                let defaultErr =
                    getUpToNextWhitespace string
                    |> Option.map (CouldntRecognise >> NEL.make)

                errOpt |> Option.defaultBind defaultErr |> NoMatch

    let rec keepLexing tokensSoFar restOfString =
        match restOfString with
        | "" -> Ok tokensSoFar
        | rest ->
            match getFirstMatch rest with
            | Success (token, charsChomped) ->
                let stringLeft = rest[int charsChomped ..]

                keepLexing (tokensSoFar @ [ token ]) stringLeft

            | NoMatch errOpt -> Error errOpt

    keepLexing List.empty string

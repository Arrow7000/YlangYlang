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
    | NoMatchOnRestOfString of line : string

// @TODO: at some point include the line and col numbers along with the errors, or even just with the tokens tbh
type ParseErrors = NonEmptyList<ParseError>


type WhitespaceChar =
    | Space
    | NewLine

type Token =
    | Whitespace of WhitespaceChar list
    | SingleLineComment of string
    | IntLiteral of uint
    | String of string
    | LetKeyword
    | InKeyword
    | ModuleSegmentsOrQualifiedTypeOrVariant of NEL<string> // when it has dots in so it could be either a module name or refer to a (partially) qualified type or type variant
    | TypeNameOrVariantOrTopLevelModule of string // when there are no dots in the segments so it could be either a module name or just refer to a type or type variant. There's probably better ways of doing this less ambiguously. Atm I'm gonna leave that for the parsing stage, but it could be moved into the lexing stage at some point if we want to.
    | ModuleKeyword
    | ImportKeyWord
    | AsKeyword
    | ExposingKeyword
    | ParensOpen
    | ParensClose
    | BracketsOpen
    | BracketsClose
    | BracesOpen
    | BracesClose
    | ValueIdentifier of string
    | Comma
    | EqualityOp
    | InequalityOp
    | UnaryNegationOp // I think this one has to go, it's too context dependent, should only use the MinusOp and infer whether it's unary from the surrounding context
    | AssignmentOp
    | ConcatOp
    | PlusOp
    | MinusOp
    | MultOp
    | DivOp
    | ExpOp
    | PipeChar
    | TypeKeyword
    | AliasKeyword
    | Colon
    | Arrow
    | DoubleDot
    | Unit // ()
    | QualifiedIdentifier of segments : string list
    | RecordAccess of segments : string list
    | DotGetter of fieldName : string
    | ForwardComposeOp
    | BackwardComposeOp
    | ForwardPipeOp
    | BackwardPipeOp


/// Not yet used, but to add later for better debugging messages
type TokenWithContext =
    { token : Token
      line : uint // the line of the starting character. Is 1-indexed.
      col : uint // the col of the starting character. Is 1-indexed.
      chars : char list // keep the original constituent chars around, for better error messages :)
      numOfChars : uint } // bear in mind that the whitespace tokens will span multiple lines
    member this.charLength = List.length this.chars

// Should probably add an Error variant here for lexing errors that are more severe than just 'not a match', e.g. tabs, which are wholesale not allowed. Then that can contain all the parse errors and NoMatch can just denote a simple innocuous no match
type LexingState =
    | NoMatch
    | Success of token : Token * charsChomped : uint
    // In case we encounter a error even at the lexing stage, e.g. we've found a tab character.
    // @TODO: might be a good idea to thread errors through the lexing state, so that we can keep parsing the rest of the file even if we encounter an error locally!
    | Err of ParseErrors



type LexingResult = Result<Token list, ParseErrors>


type Matcher = string -> LexingState





/// Prepends a ^ at the start of your search so you don't have to remember it each time. Don't say I don't do anything for you ;)
let getMatchAtStart pattern (input : string) =
    // This basically enforces that the match has to be at the start of the string
    let wrappedPattern = $"^(?:{pattern})"
    let m = Regex.Match (input, wrappedPattern)
    if m.Success then Some m.Value else None


/// This will of course start to get fucky real fast if the before/after groups themselves contain groups
let getMatchAtStartWithGroup (beforeGroup : string) (pattern : string) (afterGroup : string) (input : string) =
    // This basically enforces that the match has to be at the start of the string, and wraps the pattern in a group
    let wrappedPattern = $"^(?:{beforeGroup}({pattern}){afterGroup})"
    let m = Regex.Match (input, wrappedPattern)

    if m.Success then
        (m.Groups
         |> Seq.item 1
         |> fun capture -> capture.Value, m.Length)
        |> Some
    else
        None


let (|SingleCharRegex|_|) pattern input =
    let result = getMatchAtStart pattern input

    match result with
    | Some res ->
        match Seq.toList res with
        | [ c ] -> Some c
        | _ -> None
    | None -> None

let (|MultiCharRegex|_|) pattern input = getMatchAtStart pattern input

let (|MultiCharRegexGrouped|_|) beforeGroup pattern afterGroup input =
    getMatchAtStartWithGroup beforeGroup pattern afterGroup input


let getUpToNextLineBreak string =
    match string with
    | MultiCharRegex "[^\\n\\r]+" chars -> chars
    | _ -> String.Empty


let justKeepLexing (allMatchers : Matcher list) string =
    let getFirstMatch string =
        allMatchers
        |> List.fold
            (fun state matcher ->
                match state with
                | Success (token, chars) -> Success (token, chars)
                | Err errs -> Err errs
                | NoMatch ->
                    match matcher string with
                    | Success (token, chars) -> Success (token, chars)
                    | NoMatch -> NoMatch
                    | Err errs -> Err errs

                )
            NoMatch

    let rec keepLexing tokensSoFar restOfString =
        match restOfString with
        | "" -> Ok tokensSoFar
        | rest ->
            match getFirstMatch rest with
            | Success (token, charsChomped) ->
                let stringLeft = rest[int charsChomped ..]

                keepLexing (tokensSoFar @ [ token ]) stringLeft

            | Err err -> Error err
            | NoMatch ->
                let line = getUpToNextLineBreak rest
                NoMatchOnRestOfString line |> NEL.make |> Error

    keepLexing List.empty string








module Matchers =

    let private charLen = uint 1

    /// For matches where the actual characters can be discarded
    let private simpleMatch token pattern =
        function
        | MultiCharRegex pattern str -> Success (token, String.len str)
        | _ -> NoMatch

    let intMatcher allFileChars =
        match allFileChars with
        | MultiCharRegex "\d+" digits ->
            match UInt32.TryParse (digits) with
            | true, num -> Success (IntLiteral num, String.length digits |> uint)
            | false, _ ->
                // Should never happen since we've matched on only digit chars, but just in case

                failwithf $"Tried to parse string of digits as int32 and encountered an error. Digits are: \"{digits}\""
        | _ -> NoMatch


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
                | c' -> failwithf "Couldn't match whitespace char in whitespace matcher: '%c'" c'

            let tokensResult =
                chars
                |> Seq.map mapWhitespaceChar
                |> Seq.toList
                |> Result.anyErrors

            match tokensResult with
            | Ok tokens' -> Success (Whitespace tokens', List.length tokens' |> uint)
            | Error errs -> Err errs
        | _ -> NoMatch



    type private EscapeState =
        | Normal
        | EscapeNextChar

    let stringMatcher string =
        match string with
        | MultiCharRegexGrouped "\"" """[^"\\]*(?:\\.[^"\\]*)*""" "\"" (groupString, len) -> // forgive me, Father, for I have sinned
            // The map of what escaped char to replace with what
            // @TODO: find out all the escaped char sequences and add them in
            let escapedCharsMap =
                [ '\\', '\\'
                  '"', '"'
                  'n', '\n'
                  'r', '\r' ]
                |> Map.ofSeq

            let escapedString =
                groupString
                |> Seq.fold
                    (fun (state, list) char ->
                        match state with
                        | EscapeNextChar ->
                            match Map.tryFind char escapedCharsMap with
                            | Some replaceChar -> Normal, (list @ [ replaceChar ])
                            | None -> Normal, list @ [ '\\' ] // cos we have to add in the slash we skipped when we were expecting an escape-able character
                        | Normal ->
                            match char with
                            | '\\' -> EscapeNextChar, list
                            | c -> Normal, (list @ [ c ]))
                    (Normal, List.empty)
                |> snd
                |> String.ofSeq


            Success (String escapedString, uint len)
        | _ -> NoMatch


    let letKeywordMatcher = simpleMatch LetKeyword "let(?=\s|$)"

    let inKeywordMatcher = simpleMatch InKeyword "in\\b"

    let moduleSegmentsMatcher =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)+(?=\s)" str ->
            let token =
                String.split '.' str
                |> NEL.fromList
                |> function
                    | Some nel -> ModuleSegmentsOrQualifiedTypeOrVariant nel
                    | None -> failwithf "Module segments list was somehow empty"

            Success (token, String.len str)
        | _ -> NoMatch

    let qualifiedIdentifierMatcher =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)*(?:\.[a-z]\w*)" str ->
            Success (QualifiedIdentifier <| String.split '.' str, String.len str)
        | _ -> NoMatch

    let recordAccess =
        function
        | MultiCharRegex "[a-z]\w*(?:\.[a-z]\w*)+" str ->
            Success (QualifiedIdentifier <| String.split '.' str, String.len str)
        | _ -> NoMatch

    let dotGetter =
        function
        | MultiCharRegex "\.[a-z]\w*" str -> Success (String.tail str |> String.ofSeq |> DotGetter, String.len str)
        | _ -> NoMatch

    let importKeyword = simpleMatch ImportKeyWord "import\\b"
    let asKeyword = simpleMatch AsKeyword "as\\b"

    let typeNameOrVariantOrTopLevelModule =
        function
        | MultiCharRegex "[A-Z]\w*" str -> Success (TypeNameOrVariantOrTopLevelModule str, String.len str)
        | _ -> NoMatch

    let moduleKeyWordMatcher = simpleMatch ModuleKeyword "module\\b"

    let exposingKeyWordMatcher = simpleMatch ExposingKeyword "exposing\\b"

    let private singleCharMatcher pattern keyword =
        function
        | SingleCharRegex pattern _ -> Success (keyword, charLen)
        | _ -> NoMatch

    let parensOpen = singleCharMatcher "\(" ParensOpen
    let parensClose = singleCharMatcher "\)" ParensClose
    let bracketsOpen = singleCharMatcher "\[" BracketsOpen
    let bracketsClose = singleCharMatcher "\]" BracketsClose
    let bracesOpen = singleCharMatcher "\{" BracesOpen
    let bracesClose = singleCharMatcher "\}" BracesClose
    let comma = singleCharMatcher "\," Comma

    let equality = simpleMatch EqualityOp "\=\="

    let inequality = simpleMatch InequalityOp "\/\="

    let assignment = singleCharMatcher "\=" AssignmentOp

    let concat =
        function
        | MultiCharRegex "\+\+" str -> Success (ConcatOp, String.len str)
        | _ -> NoMatch

    let typeKeyword = simpleMatch TypeKeyword "type\\b"
    let aliasKeyword = simpleMatch AliasKeyword "alias\\b"

    /// Only run this after all the keywords have been tried!
    let valueIdentifier =
        function
        | MultiCharRegex "[a-z]\w*" ident -> Success (ValueIdentifier ident, String.len ident)
        | _ -> NoMatch

    let singleLineComment =
        function
        | MultiCharRegex "--[^\\r\\n]*" str -> Success (SingleLineComment str, String.len str)
        | _ -> NoMatch

    let minus = singleCharMatcher "\-" MinusOp
    let plus = singleCharMatcher "\+" PlusOp
    let exp = singleCharMatcher "\^" ExpOp
    let pipe = singleCharMatcher "\|" PipeChar
    let colon = singleCharMatcher "\:" Colon

    let unit = simpleMatch Unit "\(\)"
    let arrow = simpleMatch Arrow "\-\>"
    let doubleDot = simpleMatch DoubleDot "\.\."

    let forwardComposeOp = simpleMatch ForwardComposeOp "\>\>"
    let backwardComposeOp = simpleMatch BackwardComposeOp "\<\<"
    let forwardPipeOp = simpleMatch ForwardPipeOp "\|\>"
    let backwardPipeOp = simpleMatch BackwardPipeOp "\<\|"


    let allMatchersInOrder =
        [ singleLineComment
          intMatcher
          whitespaceMatcher
          stringMatcher
          letKeywordMatcher
          inKeywordMatcher
          moduleSegmentsMatcher
          moduleKeyWordMatcher
          importKeyword
          asKeyword
          exposingKeyWordMatcher
          unit
          parensOpen
          parensClose
          bracketsOpen
          bracketsClose
          bracesOpen
          bracesClose
          comma
          qualifiedIdentifierMatcher
          recordAccess
          dotGetter
          valueIdentifier
          typeNameOrVariantOrTopLevelModule
          forwardComposeOp
          backwardComposeOp
          forwardPipeOp
          backwardPipeOp
          assignment
          concat
          arrow
          minus
          plus
          exp
          pipe
          colon
          doubleDot ]

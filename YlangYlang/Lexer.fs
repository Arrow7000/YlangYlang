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
    | NewLineChar

type Whitespace =
    | Spaces of int // i.e. combine all non-newline whitespace chars into a single item so they are easier to handle
    | NewLine



type Token =
    | Whitespace of Whitespace list
    | SingleLineComment of string
    | IntLiteral of uint
    | FloatLiteral of float
    | StringLiteral of string
    | CharLiteral of char
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
    | AppendOp
    | PlusOp
    | MinusOp
    | MultOp
    | DivOp
    | ExpOp
    | PipeChar
    | TypeKeyword
    | AliasKeyword
    | CaseKeyword
    | OfKeyword
    | IfKeyword
    | ThenKeyword
    | ElseKeyword
    | Colon
    | Arrow
    | DoubleDot
    | AndOp
    | OrOp
    | Backslash // to signify start of lambda
    | Underscore // to signify unused function param
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
      startLine : uint // the line of the starting character. Is 1-indexed.
      startCol : uint // the col of the starting character. Is 1-indexed.
      endLine : uint
      endCol : uint
      chars : char list } // keep the original constituent chars around, for better error messages :)
    member this.charLength = List.length this.chars // bear in mind that the whitespace tokens will span multiple lines


type FileCursor = { endLine : uint; endCol : uint }
//| Start
//| Prev of {| endLine : uint; endCol : uint |}

// Should probably add an Error variant here for lexing errors that are more severe than just 'not a match', e.g. tabs, which are wholesale not allowed. Then that can contain all the parse errors and NoMatch can just denote a simple innocuous no match
type LexingState =
    | NoMatch
    | Success of TokenWithContext
    // In case we encounter a error even at the lexing stage, e.g. we've found a tab character.
    // @TODO: might be a good idea to thread errors through the lexing state, so that we can keep parsing the rest of the file even if we encounter an error locally!
    | Err of ParseErrors



type LexingResult = Result<TokenWithContext list, ParseErrors>


type Matcher = FileCursor -> string -> LexingState

let makeCursorFromTokenCtx ({ endLine = line; endCol = col } : TokenWithContext) : FileCursor =
    { endLine = line; endCol = col }

/// This currently makes the token context have the col and line that the chars _end_ on, whereas it should be the ones that the token _begins_ on
let makeTokenWithCtx (cursor : FileCursor) token (chars : string) =
    let nextCursor =
        chars
        |> String.toList
        |> Seq.fold
            (fun cursor' char ->
                // Although ideally we wouldn't be parsing whitespace characters in two different places
                match char with
                | '\n'
                | '\r' ->
                    { endCol = uint 0
                      endLine = cursor'.endLine + uint 1 }
                | _ -> { cursor' with endCol = cursor'.endCol + uint 1 })
            cursor

    Success
        { token = token
          startLine = cursor.endLine
          startCol = cursor.endCol
          endLine = nextCursor.endLine
          endCol = nextCursor.endCol
          chars = String.toList chars }




/// Prepends a ^ at the start of your search so you don't have to remember it each time. Don't say I don't do anything for you ;)
let getMatchAtStart pattern (input : string) =
    // This basically enforces that the match has to be at the start of the string
    let wrappedPattern = $"^(?:{pattern})"
    let m = Regex.Match (input, wrappedPattern)
    if m.Success then Some m.Value else None


type GroupedCapture =
    { group : string
      chompedChars : string }

/// This will of course start to get fucky real fast if the before/after groups themselves contain groups
let getMatchAtStartWithGroup (beforeGroup : string) (pattern : string) (afterGroup : string) (input : string) =
    // This basically enforces that the match has to be at the start of the string, and wraps the pattern in a group
    let wrappedPattern = $"^(?:{beforeGroup}({pattern}){afterGroup})"
    let m = Regex.Match (input, wrappedPattern)

    if m.Success then
        (m.Groups
         |> Seq.item 1
         |> fun capture ->
             { group = capture.Value
               chompedChars = m.Value })
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
    let initialCursor = { endLine = uint 0; endCol = uint 0 }
    //let initialCursor = Start

    let getFirstMatch cursor string =
        allMatchers
        |> List.fold
            (fun state matcher ->
                match state with
                | Success ctx -> Success ctx
                | Err errs -> Err errs
                | NoMatch ->
                    match matcher cursor string with
                    | Success ctx -> Success ctx
                    | NoMatch -> NoMatch
                    | Err errs -> Err errs

                )
            NoMatch

    let rec keepLexing tokensSoFar cursor restOfString =
        match restOfString with
        | "" -> Ok tokensSoFar
        | rest ->
            match getFirstMatch cursor rest with
            | Success ctx ->
                let stringLeft = rest[int ctx.charLength ..]
                let newCursor = makeCursorFromTokenCtx ctx

                keepLexing (tokensSoFar @ [ ctx ]) newCursor stringLeft

            | Err err -> Error err
            | NoMatch ->
                let line = getUpToNextLineBreak rest
                NoMatchOnRestOfString line |> NEL.make |> Error

    keepLexing List.empty initialCursor string








module Matchers =

    let private charLen = uint 1

    /// For matches where the actual characters can be discarded
    let private simpleMatch token pattern cursor =
        function
        | MultiCharRegex pattern str -> makeTokenWithCtx cursor token str
        | _ -> NoMatch

    let intMatcher cursor allFileChars =
        match allFileChars with
        | MultiCharRegex "\d+" digits ->
            match UInt32.TryParse (digits) with
            | true, num -> makeTokenWithCtx cursor (IntLiteral num) digits
            | false, _ ->
                // Should never happen since we've matched on only digit chars, but just in case

                failwithf $"Tried to parse string of digits as int32 and encountered an error. Digits are: \"{digits}\""
        | _ -> NoMatch

    let floatMatcher cursor =
        function
        | MultiCharRegex "\d+\.\d+" str ->
            match Double.TryParse str with
            | true, num -> makeTokenWithCtx cursor (FloatLiteral num) str
            | false, _ -> NoMatch
        | _ -> NoMatch

    let whitespaceMatcher cursor allFileChars =
        match allFileChars with
        | MultiCharRegex "\s+" chars ->
            // Need to handle CRLF files so that we don't think there's double the newlines than there actually are
            let mapWhitespaceChar c =
                match c with
                | ' ' -> Ok Space
                | '\r' -> Ok NewLineChar
                | '\n' -> Ok NewLineChar
                | '\t' -> Error TabsNotAllowed
                | c' -> failwithf "Couldn't match whitespace char in whitespace matcher: '%c'" c'

            let tokensResult =
                chars
                |> Seq.map mapWhitespaceChar
                |> Seq.toList
                |> Result.anyErrors
                |> Result.map (function
                    | [] -> []
                    | head :: tail ->
                        let headState =
                            match head with
                            | Space -> Spaces 1
                            | NewLineChar -> NewLine

                        tail
                        |> List.fold
                            (fun (list, state) thisChar ->

                                match state with
                                | Spaces count ->
                                    match thisChar with
                                    | Space -> (list, Spaces (count + 1))
                                    | NewLineChar -> (list @ [ state ], NewLine)
                                | NewLine ->
                                    match thisChar with
                                    | Space -> (list @ [ state ], Spaces 1)
                                    | NewLineChar -> (list @ [ state ], NewLine))
                            ([], headState)
                        |> fun (list, state) -> list @ [ state ])

            match tokensResult with
            | Ok tokens' -> makeTokenWithCtx cursor (Whitespace tokens') chars
            | Error errs -> Err errs
        | _ -> NoMatch



    type private EscapeState =
        | Normal
        | EscapeNextChar

    let stringMatcher cursor string =
        match string with
        | MultiCharRegexGrouped "\"" """[^"\\]*(?:\\.[^"\\]*)*""" "\"" match' -> // forgive me, Father, for I have sinned
            // The map of what escaped char to replace with what
            // @TODO: find out all the escaped char sequences and add them in
            let escapedCharsMap =
                [ '\\', '\\'
                  '"', '"'
                  'n', '\n'
                  'r', '\r' ]
                |> Map.ofSeq

            let escapedString =
                match'.group
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

            makeTokenWithCtx cursor (StringLiteral escapedString) match'.chompedChars
        | _ -> NoMatch

    let charLiteral cursor =
        function
        | MultiCharRegexGrouped "'" "(.|\\\\\w)" "'" match' -> // I'm so sorry
            match Char.TryParse match'.group with
            | true, c -> makeTokenWithCtx cursor (CharLiteral c) match'.chompedChars
            | false, _ -> failwith $"Couldn't parse '{match'.group}' as char"
        | _ -> NoMatch


    let letKeywordMatcher = simpleMatch LetKeyword "let(?=\s|$)"

    let inKeywordMatcher = simpleMatch InKeyword "in\\b"

    let moduleSegmentsMatcher cursor =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)+(?=\s)" str ->
            let token =
                String.split '.' str
                |> NEL.fromList
                |> function
                    | Some nel -> ModuleSegmentsOrQualifiedTypeOrVariant nel
                    | None -> failwithf "Module segments list was somehow empty"

            makeTokenWithCtx cursor token str
        | _ -> NoMatch

    let qualifiedIdentifierMatcher cursor =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)*(?:\.[a-z]\w*)" str ->
            makeTokenWithCtx cursor (QualifiedIdentifier <| String.split '.' str) str

        | _ -> NoMatch

    let recordAccess cursor =
        function
        | MultiCharRegex "[a-z]\w*(?:\.[a-z]\w*)+" str ->
            makeTokenWithCtx cursor (RecordAccess <| String.split '.' str) str
        | _ -> NoMatch

    let dotGetter cursor =
        function
        | MultiCharRegex "\.[a-z]\w*" str -> makeTokenWithCtx cursor (String.tail str |> String.ofSeq |> DotGetter) str
        | _ -> NoMatch

    let importKeyword = simpleMatch ImportKeyWord "import\\b"
    let asKeyword = simpleMatch AsKeyword "as\\b"

    let typeNameOrVariantOrTopLevelModule cursor =
        function
        | MultiCharRegex "[A-Z]\w*" str -> makeTokenWithCtx cursor (TypeNameOrVariantOrTopLevelModule str) str
        | _ -> NoMatch

    let moduleKeyWordMatcher = simpleMatch ModuleKeyword "module\\b"

    let exposingKeyWordMatcher = simpleMatch ExposingKeyword "exposing\\b"

    let private singleCharMatcher pattern keyword cursor =
        function
        | SingleCharRegex pattern c -> makeTokenWithCtx cursor keyword <| Char.ToString c
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

    let append cursor =
        function
        | MultiCharRegex "\+\+" str -> makeTokenWithCtx cursor AppendOp str
        | _ -> NoMatch

    let typeKeyword = simpleMatch TypeKeyword "type\\b"
    let aliasKeyword = simpleMatch AliasKeyword "alias\\b"

    let singleLineComment cursor =
        function
        | MultiCharRegex "--[^\\r\\n]*" str -> makeTokenWithCtx cursor (SingleLineComment str) str
        | _ -> NoMatch

    let minus = singleCharMatcher "\-" MinusOp


    let unit = simpleMatch Unit "\(\)"
    let arrow = simpleMatch Arrow "\-\>"
    let doubleDot = simpleMatch DoubleDot "\.\."

    let caseKeyword = simpleMatch CaseKeyword "case\\b"
    let ofKeyword = simpleMatch OfKeyword "of\\b"
    let ifKeyword = simpleMatch IfKeyword "if\\b"
    let thenKeyword = simpleMatch ThenKeyword "then\\b"
    let elseKeyword = simpleMatch ElseKeyword "else\\b"

    let forwardComposeOp = simpleMatch ForwardComposeOp "\>\>"
    let backwardComposeOp = simpleMatch BackwardComposeOp "\<\<"
    let forwardPipeOp = simpleMatch ForwardPipeOp "\|\>"
    let backwardPipeOp = simpleMatch BackwardPipeOp "\<\|"
    let andOp = simpleMatch BackwardPipeOp "&&"
    let orOp = simpleMatch BackwardPipeOp "\|\|"

    let plus = singleCharMatcher "\+" PlusOp
    let exp = singleCharMatcher "\^" ExpOp
    let pipe = singleCharMatcher "\|" PipeChar
    let colon = singleCharMatcher "\:" Colon
    let backslash = simpleMatch BackwardPipeOp "\\\\"
    let underscore = simpleMatch BackwardPipeOp "_"


    /// Only run this after all the keywords have been tried!
    let valueIdentifier cursor =
        function
        | MultiCharRegex "[a-z]\w*" ident -> makeTokenWithCtx cursor (ValueIdentifier ident) ident
        | _ -> NoMatch

    let allMatchersInOrder =
        [ intMatcher
          floatMatcher
          whitespaceMatcher
          stringMatcher
          charLiteral
          letKeywordMatcher
          inKeywordMatcher
          moduleSegmentsMatcher
          qualifiedIdentifierMatcher
          recordAccess
          dotGetter
          importKeyword
          asKeyword
          typeNameOrVariantOrTopLevelModule
          moduleKeyWordMatcher
          exposingKeyWordMatcher
          equality
          inequality
          assignment
          append
          typeKeyword
          aliasKeyword
          singleLineComment
          unit
          arrow
          doubleDot
          caseKeyword
          ofKeyword
          ifKeyword
          thenKeyword
          elseKeyword
          forwardComposeOp
          backwardComposeOp
          forwardPipeOp
          backwardPipeOp
          parensOpen
          parensClose
          bracketsOpen
          bracketsClose
          bracesOpen
          bracesClose
          comma
          minus
          andOp
          orOp
          plus
          exp
          pipe
          colon
          backslash
          underscore
          valueIdentifier ]

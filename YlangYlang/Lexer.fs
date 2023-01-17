module Lexer

open System
open System.Text.RegularExpressions


/// This should probably only represent errors and not actually be used as the source for the lexers, cos that would be annoying to have to map a function for every variant when I can just have the functions there directly
type CharacterClass =
    | Digit
    | Alphabetical
    | AlphaNumeric
    | Whitespace

type LexingError =
    | WrongCharacterClass of expectedChar : CharacterClass
    | TabsNotAllowed
    | UnknownCharacter of char
    | CouldntRecognise of string
    | NoMatchOnRestOfString of line : string

type LexingErrors = NonEmptyList<LexingError>


type WhitespaceChar =
    | Space
    | NewLineChar


(* Identifiers *)

/// An unqualified lowercase identifier
type UnqualValueIdentifier = | UnqualValueIdentifier of string


/// An unqualified uppercase identifier, could be a type alias, type variant label/constructor, top-level module name, module segment, or module import alias
type UnqualTypeOrModuleIdentifier = | UnqualTypeOrModuleIdentifier of string


/// SomeModule.Segment.thing
type QualifiedValueIdentifier =
    | QualifiedValueIdentifier of
        qualifiedPath : NEL<UnqualTypeOrModuleIdentifier> *
        valueIdentifier : UnqualValueIdentifier


/// SomeModule.Segment.Thing
///
/// Could signify either a module, or a qualified type reference - either fully qualified or qualified by alias
type QualifiedModuleOrTypeIdentifier = | QualifiedModuleOrTypeIdentifier of NEL<UnqualTypeOrModuleIdentifier>


/// All the possible values that consist of a single, unqualified, variable name; i.e. either an unqualified type or unqualified value
type UnqualIdentifier =
    | ValueIdentifier of UnqualValueIdentifier
    | TypeIdentifier of UnqualTypeOrModuleIdentifier


type TypeOrModuleIdentifier =
    | QualifiedType of QualifiedModuleOrTypeIdentifier
    | UnqualType of UnqualTypeOrModuleIdentifier


type ValueIdentifier =
    | QualifiedValue of QualifiedValueIdentifier
    | UnqualValue of UnqualValueIdentifier



(* Tokens *)

type PrimitiveLiteral =
    | UintLiteral of uint
    | UfloatLiteral of float
    | StringLiteral of string
    | CharLiteral of char

type Identifier =
    | ModuleSegmentsOrQualifiedTypeOrVariant of QualifiedModuleOrTypeIdentifier // when it has dots in so it could be either a module name or refer to a (partially) qualified type or type variant
    | TypeNameOrVariantOrTopLevelModule of UnqualTypeOrModuleIdentifier // when there are no dots in the segments so it could be either a module name or just refer to a type or type variant. There's probably better ways of doing this less ambiguously. Atm I'm gonna leave that for the parsing stage, but it could be moved into the lexing stage at some point if we want to.
    | SingleValueIdentifier of UnqualValueIdentifier
    | QualifiedPathValueIdentifier of QualifiedValueIdentifier

type Operator =
    | EqualityOp
    | InequalityOp
    | AppendOp
    | PlusOp
    | MinusOp
    | MultOp
    | DivOp
    | ExpOp
    | AndOp
    | OrOp
    | ForwardComposeOp
    | BackwardComposeOp
    | ForwardPipeOp
    | BackwardPipeOp
    | ConsOp
    | OtherOp of UnqualValueIdentifier

type Token =
    | Whitespace of WhitespaceChar
    | SingleLineComment of string
    | PrimitiveLiteral of PrimitiveLiteral
    | LetKeyword
    | InKeyword
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
    | Comma
    | AssignmentEquals
    | PipeChar
    | TypeKeyword
    | AliasKeyword
    | CaseKeyword
    | OfKeyword
    | IfKeyword
    | ThenKeyword
    | ElseKeyword
    | InfixKeyword
    | Colon
    | Arrow
    | DoubleDot
    | Backslash // to signify start of lambda
    | Underscore // to signify unused function param
    | Unit // ()
    | DotFieldPath of fields : NEL<UnqualValueIdentifier> // for `<expression>.field.subfield` paths. For that dot field sequence this would only contain `field` and `subfield`, because the expression that is dotted into could be any arbitrary expression, it doesn't necessarily have to be an identifier
    | Identifier of Identifier
    | Operator of Operator


/// Not yet used, but to add later for better debugging messages
type TokenWithSource =
    { token : Token
      startLine : uint // the line of the starting character. Is 1-indexed.
      startCol : uint // the col of the starting character. Is 1-indexed.
      endLine : uint
      endCol : uint
      chars : char list } // keep the original constituent chars around, for better error messages :)
    member this.charLength = List.length this.chars // bear in mind that the whitespace tokens will span multiple lines
    override this.ToString () = String.ofSeq this.chars

/// Simple alias for `TokenWithContext`
type TknCtx = TokenWithSource

type FileCursor = { endLine : uint; endCol : uint }

// Should probably add an Error variant here for lexing errors that are more severe than just 'not a match', e.g. tabs, which are wholesale not allowed. Then that can contain all the parse errors and NoMatch can just denote a simple innocuous no match
type LexingState =
    | NoMatch
    | Success of TokenWithSource
    // In case we encounter a error even at the lexing stage, e.g. we've found a tab character.
    // @TODO: might be a good idea to thread errors through the lexing state, so that we can keep parsing the rest of the file even if we encounter an error locally!
    | Err of LexingErrors



type LexingResult = Result<TokenWithSource list, LexingErrors>


type Matcher = FileCursor -> string -> LexingState

let makeCursorFromTokenCtx ({ endLine = line; endCol = col } : TokenWithSource) : FileCursor =
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
let getMatchAtStart (pattern : string) (input : string) =
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
            | true, num -> makeTokenWithCtx cursor (UintLiteral num |> PrimitiveLiteral) digits
            | false, _ ->
                // Should never happen since we've matched on only digit chars, but just in case

                failwithf $"Tried to parse string of digits as int32 and encountered an error. Digits are: \"{digits}\""
        | _ -> NoMatch

    let floatMatcher cursor =
        function
        | MultiCharRegex "\\d+\\.\\d+" str ->
            match Double.TryParse str with
            | true, num -> makeTokenWithCtx cursor (UfloatLiteral num |> PrimitiveLiteral) str
            | false, _ -> NoMatch
        | _ -> NoMatch

    let whitespaceMatcher cursor allFileChars =
        match allFileChars with
        | SingleCharRegex "\s" char ->
            // Need to handle CRLF files so that we don't think there's double the newlines than there actually are
            let mapWhitespaceChar c =
                match c with
                | ' ' -> Ok Space
                | '\r' -> Ok NewLineChar
                | '\n' -> Ok NewLineChar
                | '\t' -> Error TabsNotAllowed
                | c' -> failwithf "Couldn't match whitespace char in whitespace matcher: '%c'" c'

            let tokensResult =
                //chars
                //|> Seq.map mapWhitespaceChar
                //|> Seq.toList
                //|> Result.anyErrors
                char |> mapWhitespaceChar
            //|> Result.map (function Space -> Spaces)
            //|> Result.map (fun c ->                            makeTokenWithCtx cursor (Whitespace c) chars)
            //        | [] -> []
            //        | head :: tail ->
            //            let headState =
            //                match head with
            //                | Space -> Spaces 1
            //                | NewLineChar -> NewLine

            //            tail
            //            |> List.fold
            //                (fun (list, state) thisChar ->

            //                    match state with
            //                    | Spaces count ->
            //                        match thisChar with
            //                        | Space -> (list, Spaces (count + 1))
            //                        | NewLineChar -> (list @ [ state ], NewLine)
            //                    | NewLine ->
            //                        match thisChar with
            //                        | Space -> (list @ [ state ], Spaces 1)
            //                        | NewLineChar -> (list @ [ state ], NewLine))
            //                ([], headState)
            //            |> fun (list, state) -> list @ [ state ])

            match tokensResult with
            | Ok token ->
                makeTokenWithCtx cursor (Whitespace token)
                <| Char.ToString char
            | Error errs -> Err <| NEL.make errs
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

            makeTokenWithCtx cursor (StringLiteral escapedString |> PrimitiveLiteral) match'.chompedChars
        | _ -> NoMatch

    let charLiteral cursor =
        function
        | MultiCharRegexGrouped "'" "(.|\\\\\w)" "'" match' -> // I'm so sorry
            match Char.TryParse match'.group with
            | true, c -> makeTokenWithCtx cursor (CharLiteral c |> PrimitiveLiteral) match'.chompedChars
            | false, _ -> failwith $"Couldn't parse '{match'.group}' as char"
        | _ -> NoMatch


    let letKeywordMatcher = simpleMatch LetKeyword "let(?=\s|$)"

    let inKeywordMatcher = simpleMatch InKeyword "in\\b"

    let importKeyword = simpleMatch ImportKeyWord "import\\b"
    let asKeyword = simpleMatch AsKeyword "as\\b"

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

    let equality = simpleMatch (Operator EqualityOp) "\=\="

    let inequality = simpleMatch (Operator InequalityOp) "\/\="

    let assignment = singleCharMatcher "\=" AssignmentEquals

    let append cursor =
        function
        | MultiCharRegex "\+\+" str -> makeTokenWithCtx cursor (Operator AppendOp) str
        | _ -> NoMatch

    let typeKeyword = simpleMatch TypeKeyword "type\\b"
    let aliasKeyword = simpleMatch AliasKeyword "alias\\b"

    let singleLineComment cursor =
        function
        | MultiCharRegex "--[^\\r\\n]*" str -> makeTokenWithCtx cursor (SingleLineComment str) str
        | _ -> NoMatch

    let unit = simpleMatch Unit "\(\)"
    let arrow = simpleMatch Arrow "\-\>"
    let doubleDot = simpleMatch DoubleDot "\.\."

    let caseKeyword = simpleMatch CaseKeyword "case\\b"
    let ofKeyword = simpleMatch OfKeyword "of\\b"
    let ifKeyword = simpleMatch IfKeyword "if\\b"
    let thenKeyword = simpleMatch ThenKeyword "then\\b"
    let elseKeyword = simpleMatch ElseKeyword "else\\b"
    let infixKeyword = simpleMatch InfixKeyword "infix\\b"

    let forwardComposeOp = simpleMatch (Operator ForwardComposeOp) "\>\>"
    let backwardComposeOp = simpleMatch (Operator BackwardComposeOp) "\<\<"
    let forwardPipeOp = simpleMatch (Operator ForwardPipeOp) "\|\>"
    let backwardPipeOp = simpleMatch (Operator BackwardPipeOp) "\<\|"
    let consOp = simpleMatch (Operator ConsOp) "::"
    let andOp = simpleMatch (Operator AndOp) "&&"
    let orOp = simpleMatch (Operator OrOp) "\|\|"

    let plus = singleCharMatcher "\+" (Operator PlusOp)
    let minus = singleCharMatcher "\\-" (Operator MinusOp)
    let mult = singleCharMatcher "\\*" (Operator MultOp)
    let div = singleCharMatcher "\/" (Operator DivOp)
    let exp = singleCharMatcher "\^" (Operator ExpOp)
    let pipe = singleCharMatcher "\|" PipeChar
    let colon = singleCharMatcher "\:" Colon
    let backslash = simpleMatch Backslash "\\\\"
    let underscore = simpleMatch Underscore "_"


    let moduleSegmentsOrQualifiedTypeMatcher cursor =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)+(?![\w\.])" str ->
            let token =
                String.split '.' str
                |> List.map UnqualTypeOrModuleIdentifier
                |> NEL.fromList
                |> function
                    | Some nel ->
                        QualifiedModuleOrTypeIdentifier nel
                        |> ModuleSegmentsOrQualifiedTypeOrVariant
                        |> Identifier

                    | None -> failwithf "Module segments list was somehow empty"

            makeTokenWithCtx cursor token str
        | _ -> NoMatch

    let qualifiedIdentifierMatcher cursor =
        function
        | MultiCharRegex "[A-Z]\w*(?:\.[A-Z]\w*)*(?:\.[a-z]\w*)(?![\w\.])" str ->
            String.split '.' str
            |> function
                | List.Empty -> failwithf "Qualified identifier sequence was somehow empty"

                | List.Last (allButLast, last) ->
                    match List.map UnqualTypeOrModuleIdentifier allButLast with
                    | [] -> failwithf "Qualified identifier sequence was somehow empty"
                    | head :: tail ->
                        let token =
                            QualifiedValueIdentifier (NEL.new_ head tail, UnqualValueIdentifier last)
                            |> QualifiedPathValueIdentifier
                            |> Identifier

                        makeTokenWithCtx cursor token str

        | _ -> NoMatch

    let typeNameOrVariantOrTopLevelModule cursor =
        function
        | MultiCharRegex "[A-Z]\w*(?![\w\.])" str ->
            makeTokenWithCtx
                cursor
                (UnqualTypeOrModuleIdentifier str
                 |> TypeNameOrVariantOrTopLevelModule
                 |> Identifier)
                str
        | _ -> NoMatch


    /// This parses both dot field name sequences of record expressions, but also first class record getters - depending on context and if there are more than one field path in the sequence
    let dotFieldPath cursor =
        function
        | MultiCharRegex "(?:\.[a-z]\w*)+" str ->
            String.split '.' str
            |> List.filter (String.IsNullOrWhiteSpace >> not)
            |> List.map UnqualValueIdentifier
            |> (function
            | [] -> failwithf "Dot field sequence was somehow empty"
            | head :: rest -> makeTokenWithCtx cursor (DotFieldPath (NEL (head, rest))) str)
        | _ -> NoMatch



    /// Only run this after all the keywords have been tried!
    let valueIdentifier cursor =
        function
        | MultiCharRegex "[a-z]\w*" ident ->
            makeTokenWithCtx
                cursor
                (UnqualValueIdentifier ident
                 |> SingleValueIdentifier
                 |> Identifier)
                ident
        | _ -> NoMatch

    let otherOp cursor =
        function
        | MultiCharRegex "[<>!@#\\\\\/*^%£$%&*\\-+|=]+" opChars ->
            makeTokenWithCtx
                cursor
                (UnqualValueIdentifier opChars
                 |> OtherOp
                 |> Operator)
                opChars
        | _ -> NoMatch

    let allMatchersInOrder =
        [ floatMatcher
          intMatcher
          whitespaceMatcher
          stringMatcher
          charLiteral
          letKeywordMatcher
          inKeywordMatcher
          importKeyword
          asKeyword
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
          infixKeyword
          forwardComposeOp
          backwardComposeOp
          forwardPipeOp
          backwardPipeOp
          consOp
          parensOpen
          parensClose
          bracketsOpen
          bracketsClose
          bracesOpen
          bracesClose
          comma
          minus
          mult
          div
          andOp
          orOp
          plus
          exp
          pipe
          colon
          backslash
          underscore
          moduleSegmentsOrQualifiedTypeMatcher
          qualifiedIdentifierMatcher
          typeNameOrVariantOrTopLevelModule
          dotFieldPath
          valueIdentifier
          otherOp ]



let tokeniseString = justKeepLexing Matchers.allMatchersInOrder

open System
open System.Text.RegularExpressions
open FileHelpers

type Number = Num of decimal

let (|Regex|_|) pattern input =
    let m = Regex.Match (Char.ToString input, pattern)


    if m.Success then
        match Seq.toList m.Value with
        | [ c ] -> Some c
        | _ -> None
    else
        None

type CharacterGotStuckOn<'e> =
    { char : char
      contextSoFar : char list
      error : 'e }

type CharacterClass =
    | Digit
    | Alphabetical
    | AlphaNumeric

type ParseError =
    | WrongCharacterClass of char * expectedChar : CharacterClass
    | Other // decide later

type TokenParseState<'a, 'e> =
    | StillGoing of 'a
    | Stopped
    | ParseError of CharacterGotStuckOn<'e>


let checkForEndOfToken validator contextSoFar c =
    match c with
    | ' '
    | '\n'
    | '\r' -> Stopped
    | c' ->
        match validator c' with
        | Ok _ -> StillGoing c'
        | Error err ->
            ParseError (
                { contextSoFar = contextSoFar
                  char = c'
                  error = err }

            )



let isDigit c =
    match c with
    | Regex "\d" digit -> Ok digit
    | _ -> Error (WrongCharacterClass (c, Digit))


let parseNum chars =
    let rec gatherer digitsSoFar currentChar restOfChars =
        match checkForEndOfToken isDigit digitsSoFar currentChar with
        | Stopped -> Ok digitsSoFar
        | ParseError ctx -> Error ctx
        | StillGoing parsedChar ->
            match restOfChars with
            | [] -> Ok digitsSoFar
            | first :: rest -> gatherer (digitsSoFar @ [ parsedChar ]) first rest

    let result =
        match chars with
        | [] -> Ok List.empty
        | first :: rest -> gatherer List.empty first rest

    match result with
    | Ok list ->
        // By this point it should be validated so this should be safe
        String.Join ("", list) |> decimal |> Ok
    | Error e -> Error e



[<EntryPoint>]
let main argv =
    let fileText = readFile "Test.yl"
    let chars = fileText.ToCharArray () |> Array.toList
    parseNum chars |> printfn "%A"

    0

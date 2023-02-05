﻿module DebugHelpers

open Lexer
open Parser


/// Get the actual constituent string from the `TokenWithContext`s
let formatTokensAsText (tokens : TokenWithSource list) =
    tokens
    |> List.fold (fun str token -> str + String.ofSeq token.chars) ""


/// Get a nicer formatted version of the `OneOrMultipleErrs`
let rec private makeErrsStringly ctx errs =
    match errs with
    | OneErr err ->
        One
            {| err = err.err
               prevTokens = formatTokensAsText err.prevTokens
               contextStack = List.rev err.contextStack
               committed = ctx.committed |}
    | MultipleErrs errs' -> Multiple (List.map (makeErrsStringly ctx) errs')


/// Return a result with either the success result, or a friendlier formatted error data
let formatErrors res =
    match res with
    | { parseResult = NoParsingMatch errs } as result ->
        Error
        <| makeErrsStringly result.parsingContext errs
    | { parseResult = ParsingSuccess s } as result -> Ok result

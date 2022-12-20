module DebugHelpers

open Lexer
open Parser
open ExpressionParsing


/// Get the actual constituent string from the `TokenWithContext`s
let private formatTokensAsText (tokens : TokenWithContext list) =
    tokens
    |> List.fold (fun str token -> str + String.ofSeq token.chars) ""


/// Get a nicer formatted version of the `OneOrMultipleErrs`
let rec private makeErrsStringly result errs =
    match errs with
    | OneErr err ->
        One
            {| err = err.err
               prevTokens = formatTokensAsText err.prevTokens
               contextStack = List.rev err.contextStack
               committed = result.committed |}
    | MultipleErrs errs' -> Multiple (List.map (makeErrsStringly result) errs')


/// Return a result with either the success result, or a friendlier formatted error data
let formatErrors (res : ExpressionParserResult<_>) =
    match res with
    | { parseResult = NoParsingMatch errs } as result -> Error <| makeErrsStringly result errs
    | { parseResult = ParsingSuccess s } as result -> Ok result

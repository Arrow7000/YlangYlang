﻿open System
open System.Text.RegularExpressions
open FileHelpers
open Lexer
open Lexer.Matchers
open Parsing


[<EntryPoint>]
let main argv =
    let fileText = readFile "Expression.yl"


    justKeepLexing allMatchersInOrder fileText
    //|> Result.map parser
    |> Result.map expressionParser
    |> printfn "%A"

    0

﻿module Debouncer


open System
open Elmish

type Id = string

type State = { PendingMessages : Map<Id, int> }

let initial = { PendingMessages = Map.empty }

type SelfMessage<'AppMsg> =
    | Timeout of id : Id * appMsg : 'AppMsg
    | OnError of exn

let bounce (delay : TimeSpan) (id : Id) (msgToSend : 'a) (currentState : State) =
    let counterInc = Option.map ((+) 1) >> Option.defaultValue 1

    let delayedCmd _ =
        async {
            do! Async.Sleep (int delay.TotalMilliseconds)
            return (id, msgToSend)
        }

    let updatedState =
        let newCounter =
            Map.tryFind id currentState.PendingMessages
            |> counterInc

        { currentState with PendingMessages = Map.add id newCounter currentState.PendingMessages }

    updatedState, Cmd.OfAsync.either delayedCmd () Timeout OnError

let update (selfMessage : SelfMessage<_>) (currentState : State) =
    match selfMessage with
    | OnError error ->
        eprintfn "%s" error.Message
        currentState, Cmd.none

    | Timeout (id, appMsg) ->
        let remainingMessages =
            (Map.tryFind id currentState.PendingMessages
             |> Option.defaultValue 0)
            - 1

        if remainingMessages = 0 then
            { currentState with PendingMessages = Map.remove id currentState.PendingMessages }, Cmd.OfFunc.result appMsg
        else if remainingMessages > 0 then
            { currentState with PendingMessages = Map.add id remainingMessages currentState.PendingMessages }, Cmd.none
        else
            printfn "Invalid debouncer state: there was no state information for the supplier id"
            currentState, Cmd.none

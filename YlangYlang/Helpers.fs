[<AutoOpen>]
module Helpers


type NonEmptyList<'a> =
    | NEL of first : 'a * rest : 'a list

    static member map f (NEL (first, rest)) = NEL (f first, List.map f rest)
    static member make(a : 'a) : NEL<'a> = NEL (a, List.empty)

    static member fromList(l : 'a list) : NEL<'a> option =
        match l with
        | [] -> None
        | head :: rest -> Some <| NEL (head, rest)

    static member append : (NEL<'a> -> NEL<'a> -> NEL<'a>) =
        fun (NEL (head1, rest1)) (NEL (head2, rest2)) ->

            NEL (head1, rest1 @ (head2 :: rest2))

/// A convenient alias
and NEL<'a> = NonEmptyList<'a>



type Option<'a> with
    static member combine f fst snd =
        match fst, snd with
        | Some a, Some b -> Some <| f a b
        | Some a, None
        | None, Some a -> Some a
        | None, None -> None

    static member defaultBind d option =
        match option with
        | Some x -> Some x
        | None -> d


type Result<'a, 'e> with
    static member isOk =
        function
        | Ok _ -> true
        | Error _ -> false

    static member toOption =
        function
        | Ok x -> Some x
        | Error _ -> None


    static member gatherErrors list =
        list
        |> List.choose (function
            | Error x -> Some x
            | Ok _ -> None)

    static member gatherOks list =
        list
        |> List.choose (function
            | Ok x -> Some x
            | Error _ -> None)

    static member anyErrors list =
        let errs = Result.gatherErrors list

        match errs with
        | [] -> Ok <| Result.gatherOks list
        | _ -> Error errs



module String =
    let fromSeq s = Seq.fold (fun s c -> s + string c) "" s

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

    static member toList(NEL (head, tail)) = head :: tail

    static member append : (NEL<'a> -> NEL<'a> -> NEL<'a>) =
        fun (NEL (head1, rest1)) (NEL (head2, rest2)) ->

            NEL (head1, rest1 @ (head2 :: rest2))

    static member cons (item : 'a) (NEL (head, tail)) = NEL (item, head :: tail)

    static member appendList (list : 'a list) (NEL (head, tail)) = NEL (head, tail @ list)

    static member fold f state (NEL (head, tail)) = tail |> List.fold f (f state head)

    static member last(NEL (head, tail)) =
        match List.tryLast tail with
        | None -> head
        | Some last -> last

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
        | head :: tail -> NEL.make head |> NEL.appendList tail |> Error



module String =
    let ofSeq s = Seq.fold (fun s c -> s + string c) "" s

    let len s = String.length s |> uint

    let split (separator : char) (str : string) = str.Split (separator) |> List.ofArray

    let toList (str : string) = str.ToCharArray () |> List.ofArray

    let tail = toList >> List.tail

[<AutoOpen>]
module Helpers

let tee f x =
    f x
    x

let always x _ = x

let apply (f : 'a -> 'b) a = f a

let flip f b a = f a b

/// Make a tuple containing the original value and the mapped value
let split f a = (a, f a)


type OneOrTree<'a> =
    | One of 'a
    | Multiple of OneOrTree<'a> list


type NonEmptyList<'a> =
    | NEL of first : 'a * rest : 'a list

    /// Make new NEL with head and tail
    static member new_ (a : 'a) a's : NEL<'a> = NEL (a, a's)

    /// Make new NEL by just giving it a head
    static member make (a : 'a) : NEL<'a> = NEL.new_ a List.empty



    (* Simple getters *)

    static member head (NEL (head', _)) = head'
    static member tail (NEL (_, tail')) = tail'

    static member map f (NEL (first, rest)) = NEL (f first, List.map f rest)

    static member fromList (l : 'a list) : NEL<'a> option =
        match l with
        | [] -> None
        | head :: rest -> Some <| NEL.new_ head rest

    static member toList (NEL (head, tail)) = head :: tail

    static member append : (NEL<'a> -> NEL<'a> -> NEL<'a>) =
        fun (NEL (head1, rest1)) (NEL (head2, rest2)) ->

            NEL (head1, rest1 @ (head2 :: rest2))

    static member cons (newHead : 'a) (NEL (head, tail)) = NEL (newHead, head :: tail)

    /// Appends the list to the end of the NEL
    static member appendList (list : 'a list) (NEL (head, tail)) = NEL (head, tail @ list)

    static member fold<'State, 'Item> (f : 'State -> 'Item -> 'State) (state : 'State) (NEL (head, tail)) =
        tail |> List.fold f (f state head)

    static member foldBack f state (NEL (head, tail)) = List.foldBack f tail state |> f head

    static member last (NEL (head, tail)) =
        match List.tryLast tail with
        | None -> head
        | Some last -> last

/// A convenient alias for NonEmptyList
and NEL<'a> = NonEmptyList<'a>

/// Non-empty list
type 'a nel = NonEmptyList<'a>


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

    static member bindError (f : 'errA -> Result<'T, 'errB>) (result : Result<'T, 'errA>) =
        match result with
        | Ok res -> Ok res
        | Error e -> f e


module String =
    let ofSeq s = Seq.fold (fun s c -> s + string c) "" s

    let len s = String.length s |> uint

    let split (separator : char) (str : string) = str.Split (separator) |> List.ofArray

    let toList (str : string) = str.ToCharArray () |> List.ofArray

    let tail = toList >> List.tail


module List =
    let takeWhilePartition predicate list =

        let firstPart = List.takeWhile predicate list
        let lastPart = List.skipWhile predicate list

        firstPart, lastPart


    let (|Empty|Last|) list =
        let rec getLast accumulated list =
            match list with
            | [] -> Empty
            | last :: [] -> Last (List.rev accumulated, last)
            | head :: rest -> getLast (head :: accumulated) rest

        getLast List.empty list


    let typedPartition f list =
        List.foldBack
            (fun item (lefts, rights) ->
                match f item with
                | Choice1Of2 a -> a :: lefts, rights
                | Choice2Of2 b -> lefts, b :: rights)
            list
            (List.empty, List.empty)


type Either<'a, 'b> =
    | Left of 'a
    | Right of 'b

    static member mapLeft f either =
        match either with
        | Left l -> Left (f l)
        | Right r -> Right r

    static member mapRight f either =
        match either with
        | Left l -> Left l
        | Right r -> Right (f r)



/// A list of type 'T but containing exactly one item of type 'U
type ListWithOneDifferentType<'T, 'U> =
    | NotUniqueYet of item : 'T * rest : ListWithOneDifferentType<'T, 'U>
    | UniqueNow of item : 'U * rest : 'T list

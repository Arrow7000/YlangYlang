[<AutoOpen>]
module Helpers

open System
open System.Collections
open System.Collections.Generic


let tee f x =
    f x
    x

let always x _ = x

let apply (f : 'a -> 'b) a = f a

let flip (f : 'b -> 'a -> 'c) : ('a -> 'b -> 'c) = fun a b -> f b a

/// Make a tuple containing the original value and the mapped value
let split f a = (a, f a)

/// Sort the two items
let sortItems a b = if compare a b <= 0 then a, b else b, a

type 'T set when 'T : comparison = Set<'T>

type OneOrTree<'a> =
    | One of 'a
    | Multiple of OneOrTree<'a> list


type NonEmptyList<'a> =
    | NEL of first : 'a * rest : 'a list


    interface IEnumerable<'a> with
        member this.GetEnumerator () =
            let (NEL (head, tail)) = this
            let items = head :: tail |> Seq.ofList
            items.GetEnumerator ()

    interface IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<'a>).GetEnumerator () :> IEnumerator




    /// Make new NEL with head and tail
    static member new_ (a : 'a) a's : NEL<'a> = NEL (a, a's)

    /// Make new NEL by just giving it a head
    static member make (a : 'a) : NEL<'a> = NEL.new_ a List.empty



    (* Simple getters *)

    static member head (NEL (head', _)) : 'a = head'
    static member tail (NEL (_, tail')) : 'a list = tail'

    static member split (NEL (head', tail')) = head', tail'


    static member map<'b> (f : 'a -> 'b) (NEL (first, rest) : 'a nel) = NEL (f first, List.map f rest)

    static member mapi<'b> (f : int -> 'a -> 'b) (NEL (first, rest) : 'a nel) =
        NEL (f 0 first, List.mapi ((+) 1 >> f) rest)

    static member fromList (l : 'a list) : NEL<'a> option =
        match l with
        | [] -> None
        | head :: rest -> Some <| NEL.new_ head rest

    static member fromListAndLast (list : 'a list) (last : 'a) =
        match list with
        | [] -> NEL.make last
        | head :: rest -> NEL.new_ head (rest @ [ last ])

    static member toList (NEL (head, tail) : 'a nel) = head :: tail

    static member append : (NEL<'a> -> NEL<'a> -> NEL<'a>) =
        fun (NEL (head1, rest1)) (NEL (head2, rest2)) ->

            NEL (head1, rest1 @ (head2 :: rest2))

    static member cons (newHead : 'a) (NEL (head, tail)) = NEL (newHead, head :: tail)

    /// Appends the list to the end of the NEL
    static member appendList (NEL (head, tail)) (list : 'a list) = NEL (head, tail @ list)

    static member fold (f : 'State -> 'a -> 'State) (state : 'State) (NEL (head, tail) : 'a nel) : 'State =
        tail |> List.fold f (f state head)

    static member reduce (f : 'T -> 'T -> 'T) (NEL (head, tail) : 'T nel) : 'T = List.fold f head tail

    static member foldBack f state (NEL (head, tail)) = List.foldBack f tail state |> f head

    static member last (NEL (head, tail)) : 'a =
        match List.tryLast tail with
        | None -> head
        | Some last -> last

    static member allButLast (NEL (head, tail) : 'a nel) : 'a nel =
        let rec getAllButLast list =
            match list with
            | [] -> []
            | _ :: [] -> []
            | head :: rest -> head :: getAllButLast rest

        NEL (head, getAllButLast tail)


    /// Separate out the last item from the NEL
    static member peelOffLast (nel : 'a nel) : 'a nel * 'a = NEL.allButLast nel, NEL.last nel


    static member sequenceResult (results : Result<'a, 'b> nel) : Result<'a nel, 'b nel> =
        let (NEL (head, tail)) = results

        match head with
        | Ok okHead ->
            (List.fold
                (fun state res ->
                    match state with
                    | Ok oks ->
                        match res with
                        | Ok ok -> Ok (NEL.appendList oks [ ok ])
                        | Error err -> Error (NEL.make err)
                    | Error errs ->
                        match res with
                        | Error err -> Error (NEL.appendList errs [ err ])
                        | Ok _ -> Error errs)
                (Ok (NEL.make okHead))
                tail)
        | Error err ->
            NEL.new_
                err
                (List.choose
                    (function
                    | Error e -> Some e
                    | Ok _ -> None)
                    tail)
            |> Error

    static member minBy<'b when 'b : comparison> (projection : 'a -> 'b) (nel : 'a nel) =
        let (NEL (head, tail)) = nel

        tail
        |> List.fold
            (fun (currMin, currMinProjected) item ->
                let itemProjected = projection item

                if itemProjected < currMinProjected then
                    (item, itemProjected)
                else
                    (currMin, currMinProjected))
            (head, projection head)
        |> fst

    static member min<'T when 'T : comparison> (nel : 'T nel) = NEL.minBy<'T> id nel


    static member distinctBy<'b when 'b : equality> (projection : 'a -> 'b) (nel : 'a nel) : 'a nel =
        let (NEL (head, tail)) = nel

        tail
        |> List.fold
            (fun hashMap item ->
                let itemHash = hash (projection item)

                match Map.tryFind itemHash hashMap with
                | None -> hashMap |> Map.add itemHash item
                | Some _ -> hashMap)
            (Map.add (hash (projection head)) head Map.empty)

        |> Map.values
        |> Seq.toList
        |> function
            | [] -> NEL.make head // although it shouldn't be possible for this to be empty
            | h :: t -> NEL.new_ h t


    static member distinct<'T when 'T : equality> (nel : 'T nel) = NEL.distinctBy<'T> id nel


    static member traverseResult (f : 'a -> Result<'b, 'err>) = NEL.map f >> NEL.sequenceResult


    static member reverse ((NEL (head, tail)) : NEL<'a>) =
        match tail with
        | [] -> NEL (head, [])
        | neck :: [] -> NEL (neck, [ head ])
        | neck :: rest -> NEL.appendList (NEL.reverse (NEL (neck, rest))) [ head ]


    static member contains<'T when 'T : equality> (item : 'T) ((NEL (head, tail)) : 'T nel) =
        item = head || List.contains item tail





/// A convenient alias for NonEmptyList
and NEL<'a> = NonEmptyList<'a>

/// Non-empty list
and 'a nel = NonEmptyList<'a>




/// List of Two Or More™
type TwoOrMore<'a> =
    | TOM of head : 'a * neck : 'a * tail : 'a list

    interface IEnumerable<'a> with
        member this.GetEnumerator () =
            let (TOM (head, neck, tail)) = this
            let items = [ head; neck ] @ tail |> Seq.ofList
            items.GetEnumerator ()

    interface IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<'a>).GetEnumerator () :> IEnumerator


    /// Make new TOM with head, neck, and tail
    static member new_ (head : 'a) (neck : 'a) tail : TwoOrMore<'a> = TOM (head, neck, tail)

    /// Make new TOM by just giving it a head and neck
    static member make (head : 'a) (neck : 'a) : TOM<'a> = TOM.new_ head neck List.empty

    (* Simple getters *)

    static member head (TOM (head', _, _) : 'a tom) = head'
    static member neck (TOM (_, neck', _) : 'a tom) = neck'
    static member tail (TOM (_, _, tail') : 'a tom) = tail'

    static member map<'b> (f : 'a -> 'b) (TOM (head, neck, rest) : 'a tom) = TOM (f head, f neck, List.map f rest)

    static member mapi<'b> (f : int -> 'a -> 'b) (TOM (head, neck, rest) : 'a tom) =
        TOM (f 0 head, f 1 neck, List.mapi ((+) 2 >> f) rest)

    static member fromList (l : 'a list) : TOM<'a> option =
        match l with
        | [] -> None
        | [ _ ] -> None
        | head :: neck :: tail -> Some <| TOM.new_ head neck tail

    static member toList (TOM (head, neck, tail) : 'a tom) = head :: neck :: tail

    static member cons (newHead : 'a) (TOM (oldHead, neck, tail)) = TOM (newHead, oldHead, neck :: tail)

    static member append : (TOM<'a> -> TOM<'a> -> TOM<'a>) =
        fun (TOM (head1, neck1, rest1)) (TOM (head2, neck2, rest2)) ->

            TOM (head1, neck1, rest1 @ (head2 :: neck2 :: rest2))

    /// Append a list to the end of the TOM
    static member appendList (TOM (head, neck, tail)) (list : 'a list) = TOM (head, neck, tail @ list)

    static member fold<'State>
        (f : 'State -> 'a -> 'State)
        (state : 'State)
        (TOM (head, neck, tail) : 'a tom)
        : 'State =
        f state head
        |> fun result -> f result neck
        |> fun result -> List.fold f result tail


    static member foldMap<'State, 'Result>
        (f : 'State -> 'a -> 'Result * 'State)
        state
        (TOM (head, neck, tail) : 'a tom)
        =
        let headResult, headState = f state head
        let neckResult, neckState = f headState neck
        let tailResults, finalState = List.mapFold f neckState tail

        TOM.new_ headResult neckResult tailResults, finalState


    static member foldBack<'State>
        (f : 'a -> 'State -> 'State)
        (state : 'State)
        (TOM (head, neck, tail) : 'a tom)
        : 'State =
        f head state
        |> fun result -> f neck result
        |> fun result -> List.foldBack f tail result


    static member fromItemAndNel item (NEL (first, tail)) = TOM (item, first, tail)


    static member sequenceResult (results : Result<'a, 'b> tom) : Result<'a tom, 'b nel> =
        let (TOM (head, neck, tail)) = results

        match head, neck with
        | Ok okHead, Ok okNeck ->
            (List.fold
                (fun state res ->
                    match state with
                    | Ok oks ->
                        match res with
                        | Ok ok -> Ok (TOM.appendList oks [ ok ])
                        | Error err -> Error (NEL.make err)
                    | Error errs ->
                        match res with
                        | Error err -> Error (NEL.appendList errs [ err ])
                        | Ok _ -> Error errs)
                (Ok (TOM.make okHead okNeck))
                tail)
        | Error err, Ok _
        | Ok _, Error err ->
            NEL.new_
                err
                (List.choose
                    (function
                    | Error e -> Some e
                    | Ok _ -> None)
                    tail)
            |> Error
        | Error err1, Error err2 ->
            NEL.new_
                err1
                (err2
                 :: (List.choose
                         (function
                         | Error e -> Some e
                         | Ok _ -> None)
                         tail))
            |> Error


    static member traverseResult (f : 'T -> Result<'a, 'b>) list = TOM.map f list |> TOM.sequenceResult


    static member contains<'T when 'T : equality> (item : 'T) (TOM (head, neck, rest) : 'T tom) =
        item = head || item = neck || List.contains item rest

    static member exists<'T when 'T : equality> (predicate : 'T -> bool) (TOM (head, neck, rest) : 'T tom) =
        predicate head || predicate neck || List.exists predicate rest


    /// Throws an exception if the seq contains fewer than two items!
    static member ofSeq (seq : 'a seq) =
        match seq |> Seq.toList with
        | head :: neck :: tail -> TOM.new_ head neck tail
        | _ -> failwith "A TwoOrMore needs to have at least two members"


    static member unzip (TOM (head, neck, tail) : ('a * 'b) tom) : 'a tom * 'b tom =
        TOM.new_ (fst head) (fst neck) (List.map fst tail), TOM.new_ (snd head) (snd neck) (List.map snd tail)


and TOM<'a> = TwoOrMore<'a>

/// List of two or more
and 'a tom = TwoOrMore<'a>






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

    static member ofOption errIfNone =
        function
        | Some x -> Ok x
        | None -> Error errIfNone

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

    static member sequence (list : Result<'a, 'b> seq) : Result<'a seq, 'b nel> =
        Seq.foldBack
            (fun res state ->
                match state with
                | Ok oks ->
                    match res with
                    | Ok ok -> Ok (ok :: oks)
                    | Error err -> Error (NEL.make err)
                | Error errs ->
                    match res with
                    | Error err -> Error (NEL.cons err errs)
                    | Ok _ -> Error errs)
            list
            (Ok List.empty)
        |> Result.map Seq.ofList

    static member sequenceList (list : Result<'a, 'b> list) : Result<'a list, 'b nel> =
        Result.sequence list |> Result.map Seq.toList

    static member traverse (f : 'a -> Result<'b, 'c>) : 'a list -> Result<'b list, 'c nel> =
        List.map f >> Result.sequenceList

    static member bindError (f : 'errA -> Result<'T, 'errB>) (result : Result<'T, 'errA>) =
        match result with
        | Ok res -> Ok res
        | Error e -> f e


    static member mapBoth mapOk mapErr = Result.map mapOk >> Result.mapError mapErr


    static member map2 mapOks (mapErrs : 'err -> 'err -> 'err) result1 result2 =
        match result1, result2 with
        | Ok ok1, Ok ok2 -> Ok <| mapOks ok1 ok2
        | Ok _, Error err
        | Error err, Ok _ -> Error err
        | Error err1, Error err2 -> Error <| mapErrs err1 err2


    static member bind2 bindOks (mapErrs : 'err -> 'err -> 'err) result1 result2 =
        match result1, result2 with
        | Ok ok1, Ok ok2 -> bindOks ok1 ok2
        | Ok _, Error err
        | Error err, Ok _ -> Error err
        | Error err1, Error err2 -> Error <| mapErrs err1 err2

    static member map3 mapOks (mapErrs : 'err -> 'err -> 'err) result1 result2 result3 =
        match result1, result2, result3 with
        | Ok ok1, Ok ok2, Ok ok3 -> Ok <| mapOks ok1 ok2 ok3
        | Error err, Ok _, Ok _
        | Ok _, Error err, Ok _
        | Ok _, Ok _, Error err -> Error err
        | Error err1, Error err2, Ok _
        | Error err1, Ok _, Error err2
        | Ok _, Error err1, Error err2 -> Error <| mapErrs err1 err2
        | Error err1, Error err2, Error err3 -> mapErrs (mapErrs err1 err2) err3 |> Error




module String =
    let ofSeq (chars : char seq) = String.Concat chars

    let len s = String.length s |> uint

    let split (separator : char) (str : string) = str.Split (separator) |> List.ofArray

    let toList (str : string) = str.ToCharArray () |> List.ofArray

    let tail = toList >> List.tail

    let join (sep : string) (seq : string seq) = String.Join (sep, seq)

    let trim len (str : string) = str.Substring (0, len)


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


    let typedPartition3 f list =
        List.foldBack
            (fun item (lefts, middles, rights) ->
                match f item with
                | Choice1Of3 a -> a :: lefts, middles, rights
                | Choice2Of3 b -> lefts, b :: middles, rights
                | Choice3Of3 c -> lefts, middles, c :: rights)
            list
            (List.empty, List.empty, List.empty)

    let typedPartition4 f list =
        List.foldBack
            (fun item (firsts, seconds, thirds, fourths) ->
                match f item with
                | Choice1Of4 a -> a :: firsts, seconds, thirds, fourths
                | Choice2Of4 b -> firsts, b :: seconds, thirds, fourths
                | Choice3Of4 c -> firsts, seconds, c :: thirds, fourths
                | Choice4Of4 d -> firsts, seconds, thirds, d :: fourths)
            list
            (List.empty, List.empty, List.empty, List.empty)

    let typedPartition5 f list =
        List.foldBack
            (fun item (firsts, seconds, thirds, fourths, fifths) ->
                match f item with
                | Choice1Of5 a -> a :: firsts, seconds, thirds, fourths, fifths
                | Choice2Of5 b -> firsts, b :: seconds, thirds, fourths, fifths
                | Choice3Of5 c -> firsts, seconds, c :: thirds, fourths, fifths
                | Choice4Of5 d -> firsts, seconds, thirds, d :: fourths, fifths
                | Choice5Of5 e -> firsts, seconds, thirds, fourths, e :: fifths)
            list
            (List.empty, List.empty, List.empty, List.empty, List.empty)


    let minBySafe projection list =
        match list with
        | [] -> None
        | _ :: _ -> List.minBy projection list |> Some

    let minSafe list = minBySafe id list


    /// Returns an Error result with the lists so far if lists don't have the same length; which will be a list of n pairs, where n is the length of the shorter of the two input lists.
    /// If the lists are not the same length, the Error will contain the combined lists so far. This is useful so that we can do some type checking on those bits that do overlap.
    let zipList listA listB : Result<('a * 'b) list, ('a * 'b) list> =
        let rec zipList_ combinedSoFar a b =
            match a, b with
            | [], [] -> Ok (List.rev combinedSoFar)
            | headA :: tailA, headB :: tailB -> zipList_ ((headA, headB) :: combinedSoFar) tailA tailB
            | [], _ :: _
            | _ :: _, [] -> Error (List.rev combinedSoFar)

        zipList_ List.empty listA listB



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






module Map =
    /// Make a new Map containing a single entry
    let singleton (key : 'Key) (value : 'T) : Map<'Key, 'T> = Map.add key value Map.empty

    let mapKeyVal (f : 'Key -> 'T -> ('NKey * 'U)) map =
        Map.fold
            (fun newMap key value ->
                let (newKey, newVal) = f key value
                Map.add newKey newVal newMap)
            Map.empty
            map

    /// Merge two maps. If there are duplicate keys they will be overridden
    let merge map1 map2 =
        map1 |> Map.fold (fun mapToAddTo key value -> Map.add key value mapToAddTo) map2

    /// Merge many maps. If there are duplicate keys they will be overridden
    let mergeMany maps = Seq.fold merge Map.empty maps

    /// Merges two maps, but defers to the merging function if there are key clashes
    let mergeSafe (merger : 'Key -> 'T -> 'T -> 'T) map1 map2 =
        map1
        |> Map.fold
            (fun merged key value ->
                match Map.tryFind key merged with
                | Some existingVal -> Map.add key (merger key existingVal value) merged
                | None -> Map.add key value merged)
            map2





    let foldSharedKeys
        (fold : 'State -> 'Key -> 'a -> 'b -> 'State)
        (map1 : Map<'Key, 'a>)
        (map2 : Map<'Key, 'b>)
        (initialState : 'State)
        : 'State =
        map1
        |> Map.fold
            (fun state keyFrom1 valueFrom1 ->
                match Map.tryFind keyFrom1 map2 with
                | Some valueFrom2 -> fold state keyFrom1 valueFrom1 valueFrom2
                | None -> state)
            initialState


    /// Map over two maps but only those keys that they both have in common. Discard the rest.
    let mapSharedKeys (map : 'Key -> 'a -> 'b -> 'c) (map1 : Map<'Key, 'a>) (map2 : Map<'Key, 'b>) : Map<'Key, 'c> =
        let fold state k a b = Map.add k (map k a b) state
        foldSharedKeys fold map1 map2 Map.empty






    /// @TODO: should ideally split this out into two different functions, one for getting only the map1 - map2 difference keys, and one for the map2 - map1 difference keys. Then we can compose those two to recreate this foldNonSharedKeys function
    let foldNonSharedKeys
        (foldFrom1 : 'State -> 'Key -> 'a -> 'State)
        (foldFrom2 : 'State -> 'Key -> 'b -> 'State)
        (map1 : Map<'Key, 'a>)
        (map2 : Map<'Key, 'b>)
        initialState
        : 'State =
        let map1FoldState, map2Remaining =
            map1
            |> Map.fold
                (fun (state, map2Remaining) keyFrom1 valueFrom1 ->
                    match Map.tryFind keyFrom1 map2Remaining with
                    | None ->
                        // If this key is not present in map2 then we add it to the map
                        //Map.add keyFrom1 (foldFrom1 keyFrom1 valueFrom1) merged, map2Remaining
                        foldFrom1 state keyFrom1 valueFrom1, map2Remaining
                    | Some _ ->
                        // If this key is present in map2 then we don't add it to the map and we also remove it from the map2 keys
                        state, Map.remove keyFrom1 map2Remaining)
                (initialState, map2)

        // So at this point map2Remaining contains only keys that are not present in map1, so we can just map and add its entries to the merged map
        map2Remaining
        |> Map.fold (fun state key value -> foldFrom2 state key value) map1FoldState


    /// Map only over those keys that the two maps do *not* have in common and combine the two difference maps
    let mapNonSharedKeys<'Key, 'a, 'b, 'c when 'Key : comparison>
        (mapFrom1 : 'Key -> 'a -> 'c)
        (mapFrom2 : 'Key -> 'b -> 'c)
        (map1 : Map<'Key, 'a>)
        (map2 : Map<'Key, 'b>)
        : Map<'Key, 'c> =
        let foldFrom1 state k v = Map.add k (mapFrom1 k v) state
        let foldFrom2 state k v = Map.add k (mapFrom2 k v) state
        foldNonSharedKeys foldFrom1 foldFrom2 map1 map2 Map.empty





    let foldAllEntries<'Key, 'a, 'b, 'State when 'Key : comparison>
        (foldFrom1 : 'State -> 'Key -> 'a -> 'State)
        (foldFrom2 : 'State -> 'Key -> 'b -> 'State)
        (foldShared : 'State -> 'Key -> 'a -> 'b -> 'State)
        (map1 : Map<'Key, 'a>)
        (map2 : Map<'Key, 'b>)
        (initialState : 'State)
        : 'State =
        foldSharedKeys foldShared map1 map2 initialState
        |> foldNonSharedKeys foldFrom1 foldFrom2 map1 map2


    /// Map over two maps, with separate mapping funcs for shared and exclusive keys – can handle heterogeneous maps!
    let mapAndCombineAllKeys mapFrom1 mapFrom2 (mapShared : 'Key -> 'a -> 'b -> 'c) map1 map2 : Map<'Key, 'c> =
        let foldFrom1 state k v = Map.add k (mapFrom1 k v) state
        let foldFrom2 state k v = Map.add k (mapFrom2 k v) state
        let foldShared state k a b = Map.add k (mapShared k a b) state

        foldAllEntries foldFrom1 foldFrom2 foldShared map1 map2 Map.empty




    /// Describes how two maps overlap – either they have exactly the same keys, the left one is a superset of the right, the right is a superset of the left, or they both have keys the other doesn't have (fully disjoint maps still fall under the `BothHaveMore` case, then it will just have an empty shared map)
    type MapsOverlap<'Key, 'T, 'U when 'Key : comparison> =
        | Exact of unified : Map<'Key, 'T * 'U>
        | BothHaveMore of diffLeft : Map<'Key, 'T> * shared : Map<'Key, 'T * 'U> * diffRight : Map<'Key, 'U>
        | LeftHasMore of diffLeft : Map<'Key, 'T> * shared : Map<'Key, 'T * 'U>
        | RightHasMore of shared : Map<'Key, 'T * 'U> * diffRight : Map<'Key, 'U>


    let getOverlap<'Key, 'T, 'U when 'Key : comparison>
        (map1 : Map<'Key, 'T>)
        (map2 : Map<'Key, 'U>)
        : MapsOverlap<'Key, 'T, 'U> =
        let combinedShared =
            foldSharedKeys (fun state key val1 val2 -> Map.add key (val1, val2) state) map1 map2 Map.empty

        let foldFrom1 state key (val1 : 'T) =
            let addToMap map = Map.add key val1 map

            match state with
            | Exact shared -> LeftHasMore (addToMap Map.empty, shared)
            | LeftHasMore (leftMore, shared) -> LeftHasMore (addToMap leftMore, shared)
            | BothHaveMore (left, shared, right) -> BothHaveMore (addToMap left, shared, right)
            | RightHasMore (shared, right) -> BothHaveMore (addToMap Map.empty, shared, right)

        let foldFrom2 state key (val2 : 'U) =
            let addToMap map = Map.add key val2 map

            match state with
            | Exact shared -> RightHasMore (shared, addToMap Map.empty)
            | RightHasMore (shared, rightMore) -> RightHasMore (shared, addToMap rightMore)
            | BothHaveMore (left, shared, right) -> BothHaveMore (left, shared, addToMap right)
            | LeftHasMore (left, shared) -> BothHaveMore (left, shared, addToMap Map.empty)

        Exact combinedShared |> foldNonSharedKeys foldFrom1 foldFrom2 map1 map2










    /// Merges many maps, but defers to the merging function if there are key clashes
    let mergeSafeMany (merger : 'Key -> 'T -> 'T -> 'T) (maps : seq<Map<'Key, 'T>> when 'Key : comparison) =
        Seq.fold (mergeSafe merger) Map.empty maps



    /// Merges two maps that have exactly the same keys. Returns an error result if they don't.
    let mergeExact<'Key, 'a, 'b, 'c when 'Key : comparison>
        (merger : 'Key -> 'a -> 'b -> 'c)
        (map1 : Map<'Key, 'a>)
        (map2 : Map<'Key, 'b>)
        =
        let keys1 = Map.keys map1 |> Set.ofSeq
        let keys2 = Map.keys map2 |> Set.ofSeq

        let allKeys = Set.union keys1 keys2
        let disjointKeys = Set.difference allKeys (Set.intersect keys1 keys2)

        allKeys
        |> Seq.fold
            (fun merged key ->
                match merged with
                | Ok merged_ ->
                    match Map.tryFind key map1, Map.tryFind key map2 with
                    | Some val1, Some val2 -> Map.add key (merger key val1 val2) merged_ |> Ok

                    | Some _, None
                    | None, Some _ -> Error disjointKeys
                    | None, None ->
                        // This shouldn't be possible
                        Error disjointKeys
                | Error err -> Error err)
            (Ok Map.empty)




    /// Also produces an NEL of the errors so that the first error can be accessed easily without needing to handle the (impossible) case of an empty map
    let sequenceResult map =
        map
        |> Map.fold
            (fun state key value ->
                match state with
                | Ok oks ->
                    match value with
                    | Ok ok -> Ok (Map.add key ok oks)
                    | Error err -> Error (Map.add key err Map.empty, NEL.make err)
                | Error (errsMap, errsNel) ->
                    match value with
                    | Ok _ -> Error (errsMap, errsNel)
                    | Error err -> Error (Map.add key err errsMap, NEL.cons err errsNel))
            (Ok Map.empty)


    let choose (f : 'Key -> 'T -> 'U option) map =
        map
        |> Map.fold
            (fun newMap key value ->
                match f key value with
                | Some x -> Map.add key x newMap
                | None -> newMap)
            Map.empty


    let chooseKeyVals (f : 'Key -> 'T -> ('K * 'U) option) map =
        map
        |> Map.fold
            (fun newMap key value ->
                match f key value with
                | Some (k', v') -> Map.add k' v' newMap
                | None -> newMap)
            Map.empty


    /// Gets the value at the given key and returns it along with a map with that key removed. If the key is not in the map returns None.
    let pop<'Key, 'T when 'Key : comparison> (key : 'Key) (map : Map<'Key, 'T>) =
        match Map.tryFind key map with
        | Some value -> Some (value, Map.remove key map)
        | None -> None


    let addBulk keyvals map =
        keyvals
        |> Seq.fold (fun combined (key, value) -> Map.add key value combined) map


    /// Combines two keys and values in a map by adding a combined keyval pair and removing the old two
    let combineTwoKeys<'Key, 'T when 'Key : comparison> (key1 : 'Key) key2 combiner (map : Map<'Key, 'T>) =
        match Map.tryFind key1 map, Map.tryFind key2 map with
        | Some val1, Some val2 ->
            let newKey, newVal = combiner (key1, val1) (key2, val2)

            Map.remove key1 map |> Map.remove key2 |> Map.add newKey newVal

        | Some _, None
        | None, Some _
        | None, None -> map


    /// Combine multiple keys and values in a map into a single keyval pair, according to which keys match a predicate. The resulting map will have the keys that were combined removed
    let combineManyKeys<'Key, 'T when 'Key : comparison>
        (predicate : 'Key -> 'T -> bool)
        (combiner : ('Key * 'T) list -> 'Key * 'T)
        (map : Map<'Key, 'T>)
        =
        let keyvalsToMerge, scouredMap =
            map
            |> Map.fold
                (fun (keyvalsToMerge, newMap) key value ->
                    if predicate key value then
                        (key, value) :: keyvalsToMerge, newMap
                    else
                        keyvalsToMerge, Map.add key value newMap

                )
                (List.empty, Map.empty)

        let combinedKey, combinedVal = combiner keyvalsToMerge
        Map.add combinedKey combinedVal scouredMap



    let removeKeys (keys : 'Key seq) map =
        let keySet = Set.ofSeq keys
        Map.filter (fun k _ -> Set.contains k keySet |> not) map


    let foldMap<'State, 'Key, 'Result, 'T when 'Key : comparison>
        (mapping : 'State -> 'Key -> 'T -> 'Result * 'State)
        (initialState : 'State)
        (map : Map<'Key, 'T>)
        : Map<'Key, 'Result> * 'State =
        let mappedSeq, newState =
            Map.toSeq map
            |> Seq.mapFold
                (fun state (key, value) ->
                    let newValue, newState = mapping state key value
                    (key, newValue), newState)
                initialState

        Map.ofSeq mappedSeq, newState






module Set =

    let isNotEmpty<'a when 'a : comparison> : 'a set -> bool = Set.isEmpty >> not

    let hasOverlap a b = Set.intersect a b |> isNotEmpty

    let choose<'a, 'b when 'a : comparison and 'b : comparison> (map : 'a -> 'b option) (set : Set<'a>) =
        Set.fold
            (fun combined item ->
                match map item with
                | Some v -> Set.add v combined
                | None -> combined)
            Set.empty
            set

    /// Map over a seq and union the resulting sequence of sets
    let collect (f : 'a -> 'b set) (seqs : 'a seq) : 'b set = Seq.map f seqs |> Set.unionMany





type EitherOrBoth<'a, 'b> =
    | OnlyLeft of 'a
    | OnlyRight of 'b
    | Both of left : 'a * right : 'b

    static member getLeft v =
        match v with
        | OnlyLeft l -> Some l
        | OnlyRight _ -> None
        | Both (l, _) -> Some l

    static member getRight v =
        match v with
        | OnlyLeft _ -> None
        | OnlyRight r -> Some r
        | Both (_, r) -> Some r

    static member mapLeft f v =
        match v with
        | OnlyLeft l -> OnlyLeft (f l)
        | OnlyRight r -> OnlyRight r
        | Both (l, r) -> Both (f l, r)

    static member mapRight f v =
        match v with
        | OnlyLeft l -> OnlyLeft l
        | OnlyRight r -> OnlyRight (f r)
        | Both (l, r) -> Both (l, f r)

    static member setLeft<'l0, 'l, 'r> (left : 'l) (v : EitherOrBoth<'l0, 'r>) =
        match v with
        | OnlyLeft _ -> OnlyLeft left
        | OnlyRight r -> Both (left, r)
        | Both (_, r) -> Both (left, r)

    static member setRight<'l, 'r0, 'r> (right : 'r) (v : EitherOrBoth<'l, 'r0>) =
        match v with
        | OnlyLeft l -> Both (l, right)
        | OnlyRight _ -> OnlyRight right
        | Both (l, _) -> Both (l, right)

    static member getFromBoth (fromLeft : 'a -> 'T) (fromRight : 'b -> 'T) (fromBoth : 'a -> 'b -> 'T) v =
        match v with
        | OnlyLeft l -> fromLeft l
        | OnlyRight r -> fromRight r
        | Both (l, r) -> fromBoth l r



/// A list of type 'T but containing exactly one item of type 'U
type ListWithOneDifferentType<'T, 'U> =
    | NotUniqueYet of item : 'T * rest : ListWithOneDifferentType<'T, 'U>
    | UniqueNow of item : 'U * rest : 'T list




/// Denotes either a single instance of a named value, or 2 or more instances, which means the named value is a duplicate, which is a compile error.
/// @TODO: Technically it's not a compile error if the name clash is between top level types/values in different modules, so we should account for that later
type SingleOrDuplicate<'a> =
    | Single of 'a
    | Duplicate of TwoOrMore<'a>

    static member new_ (a : 'a) = Single a

    static member map (f : 'a -> 'b) sod =
        match sod with
        | Single a -> Single (f a)
        | Duplicate tom -> Duplicate (TOM.map f tom)


    static member getFirst (sod : SingleOrDuplicate<'a>) =
        match sod with
        | Single a -> a
        | Duplicate tom -> TOM.head tom

    static member cons (newHead : 'a) sod =
        match sod with
        | Single a -> Duplicate (TOM.new_ newHead a List.empty)
        | Duplicate tom -> TOM.cons newHead tom |> Duplicate

    static member toList (sod : SingleOrDuplicate<'a>) =
        match sod with
        | Single a -> List.singleton a
        | Duplicate tom -> TOM.toList tom

    static member append (sod1 : SingleOrDuplicate<'a>) sod2 =
        match sod1, sod2 with
        | Single a, Single b -> Duplicate (TOM.make a b)
        | Duplicate (TOM (head, neck, tail)), Duplicate b -> Duplicate (TOM.new_ head neck (tail @ TOM.toList b))
        | Single a, Duplicate b -> Duplicate (TOM.cons a b)
        | Duplicate a, Single b -> TOM.appendList a [ b ] |> Duplicate

    static member makeMapFromList<'Key when 'Key : comparison> (list : ('Key * 'a) list) =
        let listFolder (acc : Map<'Key, SOD<'a>>) ((key, value) : 'Key * 'a) : Map<'Key, SOD<'a>> =
            Map.change key (Option.map (SOD.cons value) >> Option.defaultValue (SOD.new_ value) >> Some) acc

        list |> List.fold listFolder Map.empty


    static member combineTwoReferenceMaps<'Key when 'Key : comparison> map1 map2 =
        let mapFolder (acc : Map<'Key, SOD<'a>>) (key : 'Key) (value : SOD<'a>) : Map<'Key, SOD<'a>> =
            Map.change
                key
                (fun oldValueOpt ->
                    match oldValueOpt with
                    | Some oldVal -> SOD.append oldVal value |> Some
                    | None -> Some value)
                acc

        Map.fold mapFolder map1 map2


    static member combineReferenceMaps<'Key when 'Key : comparison> (mapList : Map<'Key, SOD<'a>> list) =
        Seq.fold SOD.combineTwoReferenceMaps Map.empty mapList




/// Alias for SingleOrDuplicate
and SOD<'a> = SingleOrDuplicate<'a>

/// Alias for SingleOrDuplicate
and sod<'a> = SingleOrDuplicate<'a>



module Tuple =
    let makePair a b = a, b
    let makePairWithSnd (b : 'b) (a : 'a) = a, b
    let mapFst f (a, b) = f a, b
    let mapSnd f (a, b) = a, f b
    let mapBoth f g (a, b) = f a, g b
    let map f (a, b) = f a, f b
    let clone x = x, x

    let sequenceResult (a, b) =
        match a, b with
        | Ok a', Ok b' -> Ok (a', b')
        | Ok _, Error e
        | Error e, Ok _ -> Error e
        | Error e, Error _ -> Error e



module Triple =
    let mapThird (f : 'c -> 'd) (a, b, c) = a, b, f c

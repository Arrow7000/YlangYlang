[<AutoOpen>]
module Helpers

open System


let tee f x =
    f x
    x

let always x _ = x

let apply (f : 'a -> 'b) a = f a

let flip (f : 'b -> 'a -> 'c) : ('a -> 'b -> 'c) = fun a b -> f b a

/// Make a tuple containing the original value and the mapped value
let split f a = (a, f a)


type 'T set when 'T : comparison = Set<'T>

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


    static member traverseResult (f : 'a -> Result<'b, 'err>) = NEL.map f >> NEL.sequenceResult


    static member reverse ((NEL (head, tail)) : NEL<'a>) =
        match tail with
        | [] -> NEL (head, [])
        | neck :: [] -> NEL (neck, [ head ])
        | neck :: rest -> NEL.appendList (NEL.reverse (NEL (neck, rest))) [ head ]





/// A convenient alias for NonEmptyList
and NEL<'a> = NonEmptyList<'a>

/// Non-empty list
and 'a nel = NonEmptyList<'a>



/// List of Two Or More™
type TwoOrMore<'a> =
    | TOM of head : 'a * neck : 'a * tail : 'a list

    /// Make new TOM with head, neck, and tail
    static member new_ (head : 'a) (neck : 'a) tail : TOM<'a> = TOM (head, neck, tail)

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

    static member traverse f =
        List.map f
        >> Result.sequence
        >> Result.map List.ofSeq

    static member bindError (f : 'errA -> Result<'T, 'errB>) (result : Result<'T, 'errA>) =
        match result with
        | Ok res -> Ok res
        | Error e -> f e


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
    let ofSeq s = Seq.fold (fun s c -> s + string c) "" s

    let len s = String.length s |> uint

    let split (separator : char) (str : string) = str.Split (separator) |> List.ofArray

    let toList (str : string) = str.ToCharArray () |> List.ofArray

    let tail = toList >> List.tail

    let join (sep : string) (seq : string seq) = String.Join (sep, seq)


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


module Map =
    let mapKeyVal (f : 'Key -> 'T -> ('NKey * 'U)) map =
        Map.fold
            (fun newMap key value ->
                let (newKey, newVal) = f key value
                Map.add newKey newVal newMap)
            Map.empty
            map

    /// Merge two maps. If there are duplicate keys they will be overridden
    let merge map1 map2 =
        map1
        |> Map.fold (fun mapToAddTo key value -> Map.add key value mapToAddTo) map2

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


    /// Merges many maps, but defers to the merging function if there are key clashes
    let mergeSafeMany (merger : 'Key -> 'T -> 'T -> 'T) (maps : seq<Map<'Key, 'T>> when 'Key : comparison) =
        Seq.fold (mergeSafe merger) Map.empty maps



    /// Merges two maps that have exactly the same keys. Returns an error if they don't.
    let mergeExact (merger : 'Key -> 'a -> 'b -> 'c) map1 map2 =
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



    let sequenceResult map =
        map
        |> Map.fold
            (fun state key value ->
                match state with
                | Ok oks ->
                    match value with
                    | Ok ok -> Ok (Map.add key ok oks)
                    | Error err -> Error (Map.add key err Map.empty)
                | Error errs ->
                    match value with
                    | Ok _ -> Error errs
                    | Error err -> Error (Map.add key err errs))
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

            Map.remove key1 map
            |> Map.remove key2
            |> Map.add newKey newVal

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
        Map.filter (fun k _ -> Set.contains k keySet) map




module Set =

    let isNotEmpty<'a when 'a : comparison> : 'a set -> bool = Set.isEmpty >> not


    let choose<'a, 'b when 'a : comparison and 'b : comparison> (map : 'a -> 'b option) (set : Set<'a>) =
        Set.fold
            (fun combined item ->
                match map item with
                | Some v -> Set.add v combined
                | None -> combined)
            Set.empty
            set






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
            Map.change
                key
                (Option.map (SOD.cons value)
                 >> Option.defaultValue (SOD.new_ value)
                 >> Some)
                acc

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
    let makePairWithSnd b a = a, b
    let mapFst f (a, b) = f a, b
    let mapSnd f (a, b) = a, f b
    let mapBoth f g (a, b) = f a, g b


module Triple =
    let mapThird (f : 'c -> 'd) (a, b, c) = a, b, f c

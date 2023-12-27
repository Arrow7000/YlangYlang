module DependencyGraphsTests


open Expecto

open DependencyGraphs



[<Tests>]
let testStronglyConnectedGraphs () =
    testList
        "Test strongly connected graphs collection"
        [ test "Test strongly connected graph" {
              let makeNonRec item = SingleNonRec (item, item)
              let makeSelfRec item = SingleSelfRec (item, item)
              let makeMutualRec items = items |> TOM.map Tuple.clone |> TOM.ofSeq |> MutualRecursive

              /// Lil helper function to get a consistent ordering of the `More` case, because the order of that isn't guaranteed or important in the algorithm, but a different ordering in the result vs the expected would fail the test
              let sortMoreContents oom =
                  match oom with
                  | SingleNonRec (name, x) -> SingleNonRec (name, x)
                  | SingleSelfRec (name, x) -> SingleSelfRec (name, x)
                  | MutualRecursive tom -> TOM.toList tom |> List.sort |> TOM.ofSeq |> MutualRecursive

              let graph : Map<char, char seq> =
                  [ 'a', []
                    'b', [ 'a'; 'c' ]
                    'c', [ 'b'; 'c' ]
                    'd', [ 'a'; 'c' ]
                    'e', [ 'd' ]
                    'f', [ 'c'; 'e'; 'h' ]
                    'g', [ 'a'; 'b'; 'd'; 'f' ]
                    'h', [ 'a'; 'b'; 'g'; 'e' ]
                    'i', [ 'd'; 'f'; 'i' ]
                    'j', [ 'c'; 'e'; 'g'; 'i' ] ]
                  |> Seq.map (Tuple.mapSnd Seq.ofList)
                  |> Map.ofSeq

              let getDeps key =
                  match Map.tryFind key graph with
                  | Some v -> v
                  | None -> failwith $"Can't find key {key} in the graph"

              let sortedSCCs =
                  DependencyGraphs.getStronglyConnectedComponents id getDeps (Map.keys graph)
                  |> DependencyGraphs.sortOneOrMoreTopologically id getDeps
                  |> List.map sortMoreContents

              let expected =
                  [ makeNonRec 'a'
                    makeMutualRec (TOM.make 'b' 'c')
                    makeNonRec 'd'
                    makeNonRec 'e'
                    makeMutualRec (TOM.new_ 'f' 'g' [ 'h' ])
                    makeSelfRec 'i'
                    makeNonRec 'j' ]
                  |> List.map sortMoreContents

              Expect.equal
                  sortedSCCs
                  expected
                  "Correctly group items into their strongly connected components and sort them topologically"
          } ]

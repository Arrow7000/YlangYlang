module DependencyGraphsTests


open Expecto

open DependencyGraphs



[<Tests>]
let testStronglyConnectedGraphs () =
    testList
        "Test strongly connected graphs collection"
        [ test "Test strongly connected graph" {

              let oom items =
                  match items with
                  | [] -> failwith "Needs to have at least one item"
                  | x :: [] -> One x
                  | x :: y :: rest -> More (TOM.new_ x y rest)

              /// Lil helper function to get a consistent ordering of the `More` case, because the order of that isn't guaranteed or important in the algorithm, but a different ordering in the result vs the expected would fail the test
              let sortMoreContents oom =
                  match oom with
                  | One x -> One x
                  | More tom -> TOM.toList tom |> List.sort |> TOM.ofSeq |> More

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
                  [ oom [ 'a' ]
                    oom [ 'b'; 'c' ]
                    oom [ 'd' ]
                    oom [ 'e' ]
                    oom [ 'f'; 'g'; 'h' ]
                    oom [ 'i' ]
                    oom [ 'j' ] ]
                  |> List.map sortMoreContents

              Expect.equal
                  sortedSCCs
                  expected
                  "Correctly group items into their strongly connected components and sort them topologically"
          } ]

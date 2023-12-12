module DummyLangTests


open Expecto


open DummyLang
open DummyLang.AbstractSyntaxTree


let private makePolyType typeContents =
    { forall = List.empty
      typeExpr = typeContents }


[<Tests>]
let testTypeInference () =
    testList
        "Test type inference for the dummy language"
        [ testTheory "Infer the type of some primitive literals" [ str "hello", Types.strType; int 42, Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              let expectedType = result.self.typeExpr

              Expect.equal expectedType type_ (sprintf "Expected %A but got %A" type_ expectedType)

          testTheory
              "Infer the type of more complex expressions with substitutions"
              [ apply (lambda "bla" (int 43)) (str "bloo"), makePolyType Types.intType ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              let expectedType = result.self

              Expect.equal expectedType type_ (sprintf "Expected %A but got %A" type_ expectedType)


          testTheory
              "Let polymorphism!"
              [ letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (apply (name "identity") (int 7)),
                makePolyType Types.intType

                letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (apply (name "identity") (str "blabla")),
                makePolyType Types.strType

                letBindings
                    (NEL.make (letBinding "identity" None (lambda "x" (name "x"))))
                    (tuple (apply (name "identity") (int 7)) (apply (name "identity") (str "blabla"))),
                Types.tupleTypeOf (makePolyType Types.intType) (makePolyType Types.strType) ]
          <| fun (expr, type_) ->
              let result = TypeInference.inferTypeFromExpr Map.empty expr
              let expectedType = result.self

              Expect.equal expectedType type_ (sprintf "Expected %A but got %A" type_ expectedType)





          ]

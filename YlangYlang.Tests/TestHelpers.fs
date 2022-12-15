[<AutoOpen>]
module TestHelpers

open Expecto

type ActualAndExpected<'a> = { actual : 'a; expected : 'a }

let expectEqual actual expected =
    { actual = actual; expected = expected }


let makeTestCase label makeTestFunc =
    (fun _ ->
        let { actual = actual; expected = expected } = makeTestFunc ()

        Expect.equal actual expected label)
    |> testCase label

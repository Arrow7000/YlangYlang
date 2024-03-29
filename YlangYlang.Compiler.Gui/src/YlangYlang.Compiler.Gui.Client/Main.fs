module YlangYlang.Compiler.Gui.Client.Main

open System
open System.Net.Http
open System.Net.Http.Json
open Microsoft.AspNetCore.Components
open Bolero
open Bolero.Html
open Elmish


/// Routing endpoints definition.
type Page =
    | [<EndPoint "/">] Home
    | [<EndPoint "/counter">] Counter
    | [<EndPoint "/data">] Data

///// The Elmish application's model.
//type Model =
//    { page : Page
//      counter : int
//      books : Book [] option
//      error : string option }

//and Book =
//    { title : string
//      author : string
//      publishDate : DateTime
//      isbn : string }

//let initModel =
//    { page = Home
//      counter = 0
//      books = None
//      error = None }


///// The Elmish application's update messages.
//type Message =
//    | SetPage of Page
//    | Increment
//    | Decrement
//    | SetCounter of int
//    | GetBooks
//    | GotBooks of Book []
//    | Error of exn
//    | ClearError

//let update (http : HttpClient) message model =
//    match message with
//    | SetPage page -> { model with page = page }, Elmish.Cmd.none

//    | Increment -> { model with counter = model.counter + 1 }, Elmish.Cmd.none
//    | Decrement -> { model with counter = model.counter - 1 }, Elmish.Cmd.none
//    | SetCounter value -> { model with counter = value }, Elmish.Cmd.none

//    | GetBooks ->
//        let getBooks () =
//            http.GetFromJsonAsync<Book []> ("/books.json")

//        let cmd = Cmd.OfTask.either getBooks () GotBooks Error
//        { model with books = None }, cmd
//    | GotBooks books -> { model with books = Some books }, Cmd.none

//    | Error exn -> { model with error = Some exn.Message }, Cmd.none
//    | ClearError -> { model with error = None }, Cmd.none

///// Connects the routing system to the Elmish application.
////let router = Router.infer SetPage (fun model -> model.page)

//type Main = Template<"wwwroot/main.html">

//let homePage model dispatch = Main.Home().Elt ()

//let counterPage model dispatch =
//    Main
//        .Counter()
//        .Decrement(fun _ -> dispatch Decrement)
//        .Increment(fun _ -> dispatch Increment)
//        .Value(model.counter, (fun v -> dispatch (SetCounter v)))
//        .Elt ()


type CodeResult =
    //| AwaitingDebounce // I think that this is just signified by there not being anything in the codeResult Map for this particular string
    | CompileStarted
    | Compiled of string


type Model =
    { code : string
      compileDebouncer : Debouncer.State
      codeResultMap : Map<string, CodeResult>
      shownResultCache : string option
      page : Page }


type Msg =
    | DebouncerSelfMsg of Debouncer.SelfMessage<Msg>
    | EditCode of string
    | EndOfInput
    | CompileSucceeded of forCode : string * result : string // should really be the actual compilation result entity but oh well
    | SetPage of Page

let newInitModel =
    { code = String.Empty
      compileDebouncer = Debouncer.initial
      codeResultMap = Map.empty
      shownResultCache = None
      page = Home }


let compileCode code =
    async {
        return
            Lexer.tokeniseString code
            |> Result.map (
                ExpressionParsing.run ExpressionParsing.parseEntireModule
                >> DebugHelpers.formatErrors
            )
    }

let router = Router.infer Msg.SetPage (fun model -> model.page)


let update_ msg model =
    match msg with
    | EditCode str ->
        let (debouncerModel, debouncerCmd) =
            model.compileDebouncer
            |> Debouncer.bounce (TimeSpan.FromSeconds 1) "user_input" EndOfInput

        let shownCompileResult =
            match Map.tryFind str model.codeResultMap with
            | Some (Compiled result) -> Some result
            | Some CompileStarted -> model.shownResultCache // might want to add a loading indicator here at some point
            | None -> model.shownResultCache

        { model with
            code = str
            shownResultCache = shownCompileResult
            compileDebouncer = debouncerModel },
        Cmd.map DebouncerSelfMsg debouncerCmd


    | SetPage page -> { model with page = page }, Cmd.none
    | CompileSucceeded (code, result) ->
        { model with
            codeResultMap = Map.add code (Compiled result) model.codeResultMap
            shownResultCache = Some result },
        Cmd.none

    | DebouncerSelfMsg debouncerMsg ->
        let (debouncerModel, debouncerCmd) =
            Debouncer.update debouncerMsg model.compileDebouncer

        { model with compileDebouncer = debouncerModel }, debouncerCmd

    | EndOfInput ->
        let cmdOpt =
            // Only compile if this code hasn't been compiled or sent to the compiler before
            match Map.tryFind model.code model.codeResultMap with
            | Some (Compiled _) -> None
            | Some CompileStarted -> None
            | None ->
                // @TODO: we should use OfAsync.either here so that we can capture errors and show them also
                Cmd.OfAsync.perform compileCode model.code (fun result ->
                    CompileSucceeded (model.code, sprintf "%A" result))
                |> Some

        let newResultsMap =
            match cmdOpt with
            | Some _ -> Map.add model.code CompileStarted model.codeResultMap
            | None -> model.codeResultMap

        { model with codeResultMap = newResultsMap },
        match cmdOpt with
        | Some cmd -> cmd
        | None -> Cmd.none


let view model dispatch =

    let isGreyedOut =
        match Map.tryFind model.code model.codeResultMap with
        | Some (Compiled _) -> false
        | Some CompileStarted -> true
        | None ->
            match model.code with
            | "" -> false // don't grey out the initial "start typing" message
            | _ -> true

    div {
        attr.``class`` "page"

        textarea {
            attr.``class`` "editor"
            bind.input.string model.code (EditCode >> dispatch)
        }

        code {
            attr.``class``
            <| String.join
                " "
                ("sidebar"
                 :: if isGreyedOut then
                        [ "loading" ]
                    else
                        List.empty)

            model.shownResultCache
            |> Option.defaultValue "Start typing..."
        }

    }





type MyApp () =
    inherit ProgramComponent<Model, Msg> ()

    //[<Inject>]
    //member val HttpClient = Unchecked.defaultof<HttpClient> with get, set

    override _.Program =
        //let update = update this.HttpClient

        Program.mkProgram (fun _ -> newInitModel, Cmd.none) update_ view
        |> Program.withConsoleTrace
        |> Program.withRouter router

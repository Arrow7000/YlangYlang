module YlangYlang.Compiler.Gui.Client.Main

open System
open System.Net.Http
open System.Net.Http.Json
open Microsoft.AspNetCore.Components
open Bolero
open Bolero.Html
open Elmish

//module Debouncer = Thoth.Elmish.Debouncer


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

////let dataPage model dispatch =
////    Main
////        .Data()
////        .Reload(fun _ -> dispatch GetBooks)
////        .Rows(
////            cond model.books
////            <| function
////                | None -> Main.EmptyData().Elt ()
////                | Some books ->
////                    forEach books
////                    <| fun book ->
////                        tr {
////                            td { book.title }
////                            td { book.author }
////                            td { book.publishDate.ToString ("yyyy-MM-dd") }
////                            td { book.isbn }
////                        }
////        )
////        .Elt ()


////let menuItem (model : Model) (page : Page) (text : string) =
////    Main
////        .MenuItem()
////        .Active(
////            if model.page = page then
////                "is-active"
////            else
////                ""
////        )
////        .Url(router.Link page)
////        .Text(text)
////        .Elt ()

////let view model dispatch =
////    Main()
////        .Menu(
////            concat {
////                menuItem model Home "Home"
////                menuItem model Counter "Counter"
////                menuItem model Data "Download data"
////            }
////        )
////        .Body(
////            cond model.page
////            <| function
////                | Home -> homePage model dispatch
////                | Counter -> counterPage model dispatch
////                | Data -> dataPage model dispatch
////        )
////        .Error(
////            cond model.error
////            <| function
////                | None -> empty ()
////                | Some err ->
////                    Main
////                        .ErrorNotification()
////                        .Text(err)
////                        .Hide(fun _ -> dispatch ClearError)
////                        .Elt ()
////        )
////        .Elt ()

type CodeResult =
    //| AwaitingDebounce // I think that this is just signified by there not being anything in the codeResult Map for this particular string
    | CompileStarted
    | Compiled of string


type NewModel =
    { code : string
      compileDebouncer : Debouncer.State
      codeResultMap : Map<string, CodeResult>
      compilationResultShown : string option
      page : Page }


type NewMsg =
    | DebouncerSelfMsg of Debouncer.SelfMessage<NewMsg>
    | EditCode of string
    | EndOfInput
    | CompileSucceeded of forCode : string * result : string // should really be the actual compilation result entity but oh well
    | SetPage of Page

let newInitModel =
    { code = String.Empty
      compileDebouncer = Debouncer.create ()
      codeResultMap = Map.empty
      compilationResultShown = None
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

let router = Router.infer NewMsg.SetPage (fun model -> model.page)


let update_ msg model =
    match msg with
    | EditCode str ->
        let (debouncerModel, debouncerCmd) =
            model.compileDebouncer
            |> Debouncer.bounce (TimeSpan.FromSeconds 1) "user_input" EndOfInput

        let shownCompileResult =
            match Map.tryFind str model.codeResultMap with
            | Some (Compiled result) -> Some result
            | Some CompileStarted -> model.compilationResultShown // might want to add a loading indicator here at some point
            | None -> model.compilationResultShown

        { model with
            code = str
            compilationResultShown = shownCompileResult
            compileDebouncer = debouncerModel },
        Cmd.map DebouncerSelfMsg debouncerCmd


    | SetPage page -> { model with page = page }, Cmd.none
    | CompileSucceeded (code, result) ->
        { model with
            codeResultMap = Map.add code (Compiled result) model.codeResultMap
            compilationResultShown = Some result },
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

            model.compilationResultShown
            |> Option.defaultValue "Start typing..."
        }

    }





type MyApp () =
    inherit ProgramComponent<NewModel, NewMsg> ()

    //[<Inject>]
    //member val HttpClient = Unchecked.defaultof<HttpClient> with get, set

    override _.Program =
        //let update = update this.HttpClient

        Program.mkProgram (fun _ -> newInitModel, Cmd.none) update_ view
        |> Program.withConsoleTrace
        |> Program.withRouter router

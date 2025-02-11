{- Author: Fabian Huch, TU München

Find Facts application.
-}
module Main exposing (init, main, subscriptions, update, view)


import About
import Delay exposing (Delay)
import Details
import Html.Attributes exposing (href, style)
import Html.Events as Events
import Html.Lazy as Lazy
import Http
import Browser
import Browser.Navigation as Navigation
import Html exposing (..)
import Json.Decode as Decode
import Material.Theme as Theme
import Material.TopAppBar as TopAppBar
import Material.Typography as Typography
import Query exposing (Query, Query_Blocks)
import Results
import Searcher
import Url exposing (Url)
import Url.Builder
import Utils


{- main -}

main: Program () Model Msg
main =
 Browser.application {init = init, view = view, update = update, subscriptions = subscriptions,
   onUrlChange = Url_Changed, onUrlRequest = Link_Clicked}


{- model -}

type Page = Not_Found | About | Detail Details.Model | Search Searcher.Model Query Results.Model

home: Page
home = Search Searcher.empty Query.empty Results.empty

type alias Model = {nav_key: Navigation.Key, url: Url, page: Page, delay: Delay.Model}

should_query : Maybe Query -> Query -> Bool
should_query query query1 = query /= Just query1 && not (Query.empty_query query1)

populate: Page -> Searcher.Model -> Page
populate page0 searcher =
  case page0 of
    Search searcher0 query0 results0 ->
      let
        query = Searcher.get_query searcher
        results =
          if should_query (Just query0) query then Results.loading
          else if Query.empty_query query then Results.empty
          else results0
      in Search (Searcher.populate searcher0 searcher) query results
    _ ->
     let
       query = Searcher.get_query searcher
       results0 = Results.empty
       results = if should_query Nothing query then Results.loading else results0
     in Search searcher query results

init: () -> Url -> Navigation.Key -> (Model, Cmd Msg)
init _ url key =
  case url.fragment of
    Nothing -> (Model key url home Delay.empty, home |> url_encode url |> push_url False key)
    Just fragment ->
      let
        page = fragment_decode (populate Not_Found) fragment
        cmd =
          case page of
            Search _ query _ ->
              if should_query Nothing query then get_result query else Cmd.none
            Detail details -> get_block (Details.get_id details)
            _ -> Cmd.none
      in (Model key url page Delay.empty, cmd)


{- url encoding/decoding -}
{- NB: routing only in URL fragment. -}

aboutN = "about"
searchN = "search"

url_encode: Url -> Page -> Url
url_encode url page =
  case page of
    Not_Found -> {url | fragment = Nothing}
    About -> {url | fragment = Just aboutN}
    Detail details ->
      {url | fragment = Just (Details.get_id details)}
    Search searcher _ _ ->
      let params = Searcher.params searcher
      in {url | fragment = Just (searchN ++ (Url.Builder.toQuery params))}

fragment_decode : (Searcher.Model -> Page) -> String -> Page
fragment_decode make_page fragment =
  case String.split "?" fragment of
    [] -> Not_Found
    page :: qs ->
      let
        parse parser f =
          Utils.parse_query (String.join "?" qs) parser
          |> Maybe.map f
          |> Maybe.withDefault Not_Found
      in
        if page == aboutN && List.isEmpty qs then About
        else if page == searchN then parse Searcher.parser make_page
        else if List.isEmpty qs then Detail (Details.init page)
        else Not_Found

url_decode: Url -> Page -> Page
url_decode url page0 =
  case url.fragment of
    Nothing -> home
    Just fragment -> fragment_decode (populate page0) fragment


{- commands -}

push_url: Bool -> Navigation.Key -> Url -> Cmd msg
push_url save key url =
  (if save then Navigation.pushUrl else Navigation.replaceUrl) key (Url.toString url)

get_result: Query -> Cmd Msg
get_result query =
  Http.post {url="api/query", expect = Http.expectJson (Query_Result query) Query.decode_result,
    body = query |> Query.encode_query |> Http.jsonBody}

query_delay: Query -> Delay Msg
query_delay query = {name = "query", delay = 500, event = get_result query}

get_blocks: Query -> String -> Cmd Msg
get_blocks query cursor =
  Http.post {url = "api/blocks", expect = Http.expectJson (Query_Blocks query) Query.decode_blocks,
    body = {query = query, cursor = cursor} |> Query.encode_query_blocks |> Http.jsonBody}

get_block: String -> Cmd Msg
get_block id =
  Http.post {url = "api/block", expect = Http.expectJson (Query_Block id) Query.decode_block,
    body = id |> Query.encode_query_block |> Http.jsonBody}


{- update -}

type alias Scroll_Info = {pos: Float, top: Float, height: Float}
type Msg =
  Link_Clicked Browser.UrlRequest |
  Url_Changed Url |
  Searcher_Msg Searcher.Msg |
  Delay_Msg (Delay Msg) |
  Results_Msg (Results.Msg) |
  Query_Result Query (Result Http.Error Query.Result) |
  Query_Blocks Query (Result Http.Error Query.Blocks) |
  Query_Block String (Result Http.Error Query.Block) |
  Scroll_Event Scroll_Info

update : Msg -> Model -> (Model, Cmd Msg)
update msg model =
  case msg of
    Link_Clicked urlRequest ->
      case urlRequest of
        Browser.Internal url ->
          if url.path == model.url.path then (model, push_url True model.nav_key url)
          else (model, Navigation.load (Url.toString url))
        Browser.External href -> (model, Navigation.load href)

    Url_Changed url ->
      let
        query0 =
          case model.page of
            Search _ query _ -> Just query
            _ -> Nothing
        page = url_decode url model.page
        (delay, cmd) =
          case page of
            Search _ query _ ->
              if should_query query0 query then Delay.now model.delay (query_delay query)
              else (model.delay, Cmd.none)
            Detail details -> (model.delay, get_block (Details.get_id details))
            _ -> (model.delay, Cmd.none)
      in ({model | url = url, delay = delay, page = page}, cmd)

    Delay_Msg msg1 ->
      let (delay, cmd) = Delay.update model.delay msg1
      in ({model | delay = delay}, cmd)

    Searcher_Msg msg1 ->
      case model.page of
        Search searcher _ results ->
          let
            (searcher1, update_search) = Searcher.update msg1 searcher
            ((delay, search_cmd), query1, results1) =
              case update_search of
                Searcher.None query -> ((model.delay, Cmd.none), query, results)
                Searcher.Empty query ->
                  ((Delay.cancel model.delay (query_delay query), Cmd.none), query, Results.empty)
                Searcher.Later query ->
                  (Delay.later Delay_Msg model.delay (query_delay query), query, Results.loading)
                Searcher.Now query ->
                  (Delay.now model.delay (query_delay query), query, Results.loading)
            page = Search searcher1 query1 results1
            nav_cmd = url_encode model.url page |> push_url False model.nav_key
          in
            ({model | page = page, delay = delay}, Cmd.batch [nav_cmd, search_cmd])
        _ -> (model, Cmd.none)

    Results_Msg (Results.Selected id) ->
      (model, url_encode model.url (id |> Details.init |> Detail) |> push_url True model.nav_key)

    Query_Result query res ->
      case model.page of
        Search searcher query1 _ ->
          case res of
            Result.Ok result ->
              if query /= query1 then (model, Cmd.none)
              else
                let
                  searcher1 = Searcher.set_result result searcher
                  results = Results.result result
                in ({model | page = Search searcher1 query1 results}, Cmd.none)
            Result.Err err ->
              ({model | page = Search searcher query (Results.error err)}, Cmd.none)
        _ -> (model, Cmd.none)

    Query_Blocks query res ->
      case model.page of
        Search searcher query1 results ->
          if query /= query1 then (model, Cmd.none)
          else ({model | page = Search searcher query (Results.set_loaded res results)}, Cmd.none)
        _ -> (model, Cmd.none)

    Query_Block id res ->
      case model.page of
        Detail details ->
          if id /= (Details.get_id details) then (model, Cmd.none)
          else ({model | page = Detail (Details.set_loaded res details)}, Cmd.none)
        _ -> (model, Cmd.none)

    Scroll_Event scroll ->
      if (scroll.pos - scroll.top) > scroll.height then (model, Cmd.none)
      else
        case model.page of
          Search searcher query results ->
            case Results.get_maybe_cursor results of
              Nothing -> (model, Cmd.none)
              Just cursor ->
                let results1 = Results.set_load_more results
                in ({model | page = Search searcher query results1}, get_blocks query cursor)
          _ -> (model, Cmd.none)



{- subscriptions -}

subscriptions: Model -> Sub Msg
subscriptions model =
  case model.page of
    Search searcher _ _ -> Searcher.subscriptions searcher |> Sub.map Searcher_Msg
    _ -> Sub.none


{- view -}

decode_scroll : Decode.Decoder Msg
decode_scroll =
  Decode.map Scroll_Event (
    Decode.map3 Scroll_Info
      (Decode.at ["target", "scrollHeight"] Decode.float)
      (Decode.at ["target", "scrollTop"] Decode.float)
      (Decode.at ["target", "offsetHeight"] Decode.float))

view: Model -> Browser.Document Msg
view model =
  let
    view_navlink attrs page name =
      a (attrs ++ [href ("#" ++ page), style "margin" "0 16px", Theme.onPrimary])
        [text name]
    (title, content) = case model.page of
      Not_Found -> ("404 Not Found", [h2 [Typography.headline4] [text "404 Not Found"]])
      About -> ("Find Facts | About", [About.view |> Html.map never])
      Detail details -> ("Find Facts | Details", [Details.view details |> Html.map never])
      Search searcher _ results -> ("Find Facts | Search", [
        searcher |> Lazy.lazy Searcher.view |> Html.map Searcher_Msg,
        results |> Lazy.lazy Results.view |> Html.map Results_Msg])
  in {
    title = title,
    body = [
      div [style "height" "100vh", Events.on "scroll" decode_scroll, style "overflow" "scroll"] [
        TopAppBar.regular
          (TopAppBar.config
           |> TopAppBar.setDense True
           |> TopAppBar.setAttributes [style "position" "relative"])
          [TopAppBar.row [style "max-width" "1200px", style "margin" "0 auto"]
            [TopAppBar.section [TopAppBar.alignStart]
              [view_navlink [TopAppBar.title] searchN "Find Facts"],
              TopAppBar.section [TopAppBar.alignEnd]
                [view_navlink [Typography.button] searchN "Search",
                 view_navlink [Typography.button] aboutN "About"]]],
        div
          [style "padding-left" "16px", style "padding-right" "16px", style "max-width" "1200px",
           style "margin" "0 auto"]
          content]]}

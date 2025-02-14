{- Author: Fabian Huch, TU München

Find Facts details view.
-}
module Details exposing (Model, init, get_id, set_loaded, view)


import Html exposing (..)
import Html.Attributes exposing (href, style)
import Html.Extra as Html exposing (viewIf)
import Http
import Library exposing (..)
import Material.Theme as Theme
import Material.Typography as Typography
import Query exposing (Block)
import Utils exposing (Query_Param)


{- model -}

type State = Loading | Error String | Loaded Block
type Model = Model {id: String, state: State}

init id = Model {id = id, state = Loading}

get_id: Model -> String
get_id (Model model) = model.id


{- updates -}

set_loaded: Result Http.Error Block -> Model -> Model
set_loaded res (Model model) =
  case res of
    Result.Ok block -> Model {model | state = Loaded block}
    Result.Err err -> Model {model | state = Error (get_msg err)}


{- view -}

view: Model -> Html Never
view (Model model) =
  case model.state of
    Loading -> text "Loading ..."
    Error msg -> text msg
    Loaded block ->
      let
        theory = block.chapter ++ "/" ++ block.theory
        start_before =
          block.start_line - count_lines (block.src_before ++ block.html) + count_lines block.html
        around s = "<span style=\"color: gray\">" ++ (Utils.escape_html s) ++ "</span>"
        code = around block.src_before ++ block.html ++ around block.src_after
        url = block.url ++ maybe_proper block.entity_kname ((++) "#")
      in div [] [
        h2 [Typography.headline4] [text "Details"],
        h3 [Typography.headline6]
          [text "In ", a [href url] [text theory], text (" (" ++ block.file ++ ")")],
        Utils.view_code code start_before Nothing]

{- Author: Fabian Huch, TU München

Various utilities.
-}
module Utils exposing (..)


import Html exposing (..)
import Html.Attributes exposing (class, style)
import Html.Parser
import Html.Parser.Util
import Json.Decode as Decode
import Maybe.Extra as Maybe
import Parser exposing (Parser)
import String.Extra as String
import Library exposing (..)
import Url


{- query params -}

type alias Query_Param = (String, String)

parse_query: String -> Parser Query_Param a -> Maybe a
parse_query query parser =
  let
    pair s =
      case String.split "=" s |> List.map Url.percentDecode of
        [Just k, Just v] -> Just (k, v)
        _ -> Nothing
    params = if query == "" then [] else String.split "&" query
    pairs = params |> List.map pair |> Maybe.combine
  in pairs |> Maybe.map (Parser.parse parser) |> Maybe.join

parse_key: (a -> Bool) -> Parser (a, b) (a, b)
parse_key cond = Parser.elem (Tuple.first >> cond)


{- code blocks -}

escape_html: String -> String
escape_html s = s
  |> String.replace "&" "&amp;"
  |> String.replace "<" "&lt;"
  |> String.replace ">" "&gt;"
  |> String.replace "\"" "&quot;"

view_html: String -> Html msg
view_html html =
  case Html.Parser.run html of
    Ok nodes -> span [] (Html.Parser.Util.toVirtualDom nodes)
    _ -> text (String.stripTags html)

view_code: String -> Int -> Maybe Int -> Html msg
view_code src start max_lines =
  let
    view_line i line =
      "<div style=\"width:5ch; color:gray; text-align:right; display:inline-block\">" ++ (String.fromInt (start + i)) ++ "</div>  " ++ line
    lines = split_lines src
    fade = """
linear-gradient(
  to bottom,
  rgba(0,0,0, 1) 0,
  rgba(0,0,0, 1) 80%,
  rgba(0,0,0, 0) 95%,
  rgba(0,0,0, 0) 0)
100% 50% / 100% 100% repeat-x
    """
    limit f =
      max_lines
      |> Maybe.filter ((>) (List.length lines)) |> Maybe.map f |> Maybe.withDefault identity
    src1 = lines |> limit List.take |> List.indexedMap view_line |> String.join "\n"
  in Html.pre (limit (always ((::) (style "mask" fade))) [class "source"]) [view_html src1]


outside_elem: String -> Decode.Decoder Bool
outside_elem name =
  let decode_name name1 = if name == name1 then Decode.succeed False else Decode.fail "continue"
  in
    Decode.oneOf [
      Decode.field "name" Decode.string |> Decode.andThen decode_name,
      Decode.lazy (\_ -> outside_elem name |> Decode.field "parentNode"),
      Decode.succeed True]

isabelle_font : Attribute msg
isabelle_font = style "font-family" "\"Isabelle DejaVu Sans Mono\", monospace"
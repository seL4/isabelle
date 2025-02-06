{- Author: Fabian Huch, TU München

Find Facts searcher component: Url-encoded 'dry' query state,
enriched by facet information from query.
-}
module Searcher exposing (Model, empty, params, parser, Msg, Update(..), update, populate,
  set_result, subscriptions, view, get_query)


import Array exposing (Array)
import Array.Extra as Array
import Browser.Events as Events
import Dict exposing (Dict)
import Html exposing (..)
import Html.Attributes exposing (class, name, style)
import Html.Events.Extra exposing (onEnter)
import Html.Extra as Html
import Json.Decode as Decode
import Library exposing (..)
import Material.Chip.Filter as FilterChip
import Material.ChipSet.Filter as FilterChipSet
import Material.Elevation as Elevation
import Material.IconButton as IconButton
import Material.LayoutGrid as LayoutGrid
import Material.List as ItemList
import Material.List.Item as ListItem
import Material.Select as Select
import Material.Select.Item as SelectItem
import Material.TextField as TextField
import Material.TextField.Icon as TextFieldIcon
import Material.Theme as Theme
import Material.Typography as Typography
import Parser exposing (Parser)
import Query exposing (Query)
import Set exposing (Set)
import Html.Lazy as Lazy
import Url.Builder exposing (QueryParameter)
import Maybe exposing (Maybe)
import Maybe.Extra as Maybe
import Utils exposing (Query_Param, parse_key)


{- config -}

max_facet_terms = 5


{- fields -}

chapterN = "chapter"
sessionN = "session"
file_typeN = "file_type"
theoryN = "theory"
commandN = "command"
sourceN = "source"
namesN = "names"
constsN = "consts"
typsN = "typs"
thmsN = "thms"
kindsN = "kinds"

search_fields = [sessionN, theoryN, commandN, sourceN, namesN, constsN, typsN, thmsN]
facet_fields = [chapterN, sessionN, file_typeN, theoryN, commandN, constsN, typsN, thmsN, kindsN]


{- search components -}

type alias Facet = {field: String, terms: Set String}
type alias Filter = {field: String, value: String, exclude: Bool}
type alias Search = {any_filter: String, filters: Array Filter, facets: Dict String Facet}
type Model =
  Model {search: Search, facets: Maybe Query.Facets, filter_search: String, focus: Maybe Int}

init search = Model {search = search, facets = Nothing, filter_search = "", focus = Nothing}

empty: Model
empty = init (Search "" Array.empty Dict.empty)


{- URL encoding -}

filter_params : Filter -> List QueryParameter
filter_params filter =
  [Url.Builder.string ((if filter.exclude then "-" else "!") ++ filter.field) filter.value ]

facet_params : Facet -> List QueryParameter
facet_params facet =
  facet.terms |> Set.toList |> List.sort |> List.map (Url.Builder.string facet.field)

search_params: Search -> List QueryParameter
search_params search =
  list_if (search.any_filter /= "") (Url.Builder.string "q" search.any_filter) ++
    (search.filters |> Array.toList |> List.concatMap filter_params) ++
    (search.facets |> Dict.values |> List.sortBy .field |> List.concatMap facet_params)

params: Model -> List QueryParameter
params (Model model) = search_params model.search

{- Url parsing -}

filter_parser: Parser Query_Param Filter
filter_parser =
  let
    make_filter exclude (key, value) = Filter (String.dropLeft 1 key) value exclude
    include_parser = parse_key (String.startsWith "!") |> Parser.map (make_filter False)
    exclude_parser = parse_key (String.startsWith "-") |> Parser.map (make_filter True)
  in Parser.or include_parser exclude_parser

facet_parser: Parser Query_Param Facet
facet_parser =
  let
    rest_parser (key, value) =
      Parser.rep (parse_key ((==) key))
      |> Parser.map (List.map Tuple.second >> ((::) value) >> Set.fromList >> Facet key)
  in Parser.elem (always True) |> Parser.flat_map rest_parser

search_parser: Parser Query_Param Search
search_parser =
  Parser.map3 Search
    (Parser.or (parse_key ((==) "q") |> Parser.map Tuple.second) (Parser.succeed ""))
    (Parser.rep filter_parser |> Parser.map Array.fromList)
    (Parser.rep facet_parser |> Parser.map
      (List.map (\facet -> (facet.field, facet)) >> Dict.fromList))

parser: Parser Query_Param Model
parser = Parser.map init search_parser


{- update -}

type Msg =
  Input_Any String |
  Add_Filter String |
  Input_Filter Bool String |
  Change_Filter Int |
  Remove_Filter Int |
  Change_Facet String String |
  Set_Focus (Maybe Int)

type Update = Empty Query | None Query | Later Query | Now Query

empty_filter field = Filter field "" False
update_filter value filter = {filter | value = value}
change_filter filter = {filter | exclude = (not filter.exclude)}
change_terms value terms = (if Set.member value terms then Set.remove else Set.insert) value terms

change_facet : String -> String -> Maybe Facet -> Maybe Facet
change_facet field value facet0 =
  let
    facet1 = Maybe.withDefault (Facet field Set.empty) facet0
    facet2 = {facet1 | terms = facet1.terms |> change_terms value}
  in if Set.isEmpty facet2.terms then Nothing else Just facet2

update_search: Model -> (Search -> (Search, Query -> Update)) -> (Model, Update)
update_search (Model model) update_search_f =
  let
    search0 = model.search
    search1 =
      case model.focus of
        Nothing -> search0
        Just i ->
          let filters = search0.filters |> Array.update i (update_filter model.filter_search)
          in {search0 | filters = filters}
    (search2, update_f) = update_search_f search1
    query1 = search_query search2
    model1 = {model | search = search2}
  in
    if Query.empty_query query1 then (Model {model1 | facets = Nothing}, Empty query1)
    else (Model model1, update_f query1)

update: Msg -> Model -> (Model, Update)
update msg (Model model) =
  let maybe_same h m = if Maybe.withDefault True m then None else h
  in case msg of
    Input_Any value ->
      update_search (Model model) (\search ->
        ({search | any_filter = value}, (if value == search.any_filter then None else Later)))

    Add_Filter field ->
     update_search (Model model) (\search ->
       ({search | filters = search.filters |> Array.push (empty_filter field)}, None))

    Input_Filter commit value ->
      let model1 = {model | filter_search = value}
      in
        if not commit then (Model model1, None (search_query model.search))
        else update_search (Model model1) (\search -> (search, Later))

    Change_Filter i ->
      update_search (Model model) (\search ->
        ({search | filters = search.filters |> Array.update i change_filter},
         maybe_same Now (Array.get i search.filters |> Maybe.map (.value >> String.isEmpty))))

    Remove_Filter i ->
      update_search (Model model) (\search ->
        ({search | filters = search.filters |> Array.removeAt i},
         maybe_same Now (Array.get i search.filters |> Maybe.map (.value >> String.isEmpty))))

    Change_Facet field value ->
      update_search (Model model) (\search ->
        ({search | facets = search.facets |> Dict.update field (change_facet field value)}, Now))

    Set_Focus focus ->
      let
        update_f = if Maybe.isNothing focus || Maybe.isJust model.focus then Now else None
        value =
          case focus of
            Nothing -> Nothing
            Just i -> Array.get i model.search.filters |> Maybe.map .value
        ((Model model1), upd) = update_search (Model model) (\search -> (search, update_f))
      in (Model {model1 | filter_search = value |> Maybe.withDefault "", focus = focus}, upd)

populate: Model -> Model -> Model
populate (Model model0) (Model model) = Model {model0 | search = model.search}

set_result: Query.Result -> Model -> Model
set_result res (Model model) = Model {model | facets = Just res.facets}


{- subscriptions -}

subscriptions: Model -> Sub Msg
subscriptions (Model model) =
  let
    decode_outside outside =
      if outside then Decode.succeed (Set_Focus Nothing) else Decode.fail "inside"
    decoder =
      Decode.field "target" (Utils.outside_elem "filter_menu") |> Decode.andThen decode_outside
  in if Maybe.isNothing model.focus then Sub.none else Events.onClick decoder


{- view -}

view_field: String -> String
view_field field =
  Dict.fromList [
    (chapterN, "Chapter"),
    (sessionN, "Session"),
    (file_typeN, "File Type"),
    (theoryN, "Theory"),
    (commandN, "Command"),
    (sourceN, "Source Code"),
    (namesN, "Name"),
    (constsN, "Constant Name"),
    (typsN, "Type Name"),
    (thmsN, "Theorem Name"),
    (kindsN, "Kind")]
  |> Dict.get field
  |> Maybe.withDefault field

view_menu: Dict String Int -> String -> Html Msg
view_menu counts value =
  let
    suggestions =
      counts
      |> Dict.toList
      |> List.filter (Tuple.first >> String.isEmpty >> not)
      |> List.filter (Tuple.first >> String.toLower >> String.contains (String.toLower value))
      |> List.sortBy Tuple.second
      |> List.reverse
    view_option (term, count) =
      ListItem.listItem (ListItem.config |> ListItem.setOnClick (Input_Filter True term))
        [text (term ++ " (" ++ String.fromInt count ++ ")")]
    menu_config =
      [name "filter_menu", style "position" "sticky", style "z-index" "999999", style "overflow-y" "scroll",
        style "max-height" "384px", Elevation.z3, Theme.surface]
  in case suggestions |> List.map view_option of
    x::xs -> ItemList.list (ItemList.config |> ItemList.setAttributes menu_config) x xs
    _ -> Html.nothing

isabelle_icon_button s =
  IconButton.customIcon
    Html.i
    [class "material-icons", style "vertical-align" "top",
      style "font-family" "\"Isabelle DejaVu Sans Mono\", monospace", style "font-size" "math"]
    [Html.text s]

isabelle_icon_textfield s =
  TextFieldIcon.customIcon
    Html.i
    [class "material-icons", style "font-family" "\"Isabelle DejaVu Sans Mono\", monospace",
      style "font-size" "larger"]
    [Html.text s]

view_filter: Maybe String -> Dict String Int -> (Int, Filter) -> Html Msg
view_filter search0 counts (i, filter) =
  let
    search = search0 |> Maybe.filter (always (Dict.size counts > 1))
    value = search |> Maybe.withDefault filter.value
  in
    LayoutGrid.inner [name "filter_menu", Typography.body1, style "margin" "16px 0"] [
      LayoutGrid.cell
        [LayoutGrid.span3Phone, LayoutGrid.span7Tablet, LayoutGrid.span11Desktop,
          LayoutGrid.alignMiddle]
        [TextField.outlined
          (TextField.config
           |> TextField.setLeadingIcon (Just (
             isabelle_icon_textfield (if filter.exclude then "∉" else "∈")
             |> TextFieldIcon.setOnInteraction (Change_Filter i)))
           |> TextField.setValue (Just value)
           |> TextField.setOnInput (Input_Filter (Maybe.isNothing search))
           |> TextField.setOnFocus (Set_Focus (Just i))
           |> TextField.setAttributes [style "width" "100%", onEnter (Input_Filter True value)]
           |> TextField.setLabel (Just (view_field filter.field))),
          search |> Maybe.map (view_menu counts) |> Maybe.withDefault Html.nothing],
      LayoutGrid.cell [LayoutGrid.span1, LayoutGrid.alignLeft] [
        IconButton.iconButton
          (IconButton.config |> IconButton.setOnClick (Remove_Filter i))
          (isabelle_icon_button "×")]]

view_facet: String -> String -> List String -> Dict String Int -> Set String -> Html Msg
view_facet field t ts counts selected =
  let
    chip term =
      FilterChip.chip
        (FilterChip.config
         |> FilterChip.setSelected (Set.member term selected)
         |> FilterChip.setOnChange (Change_Facet field term))
        (term ++ maybe_proper (Dict.get term counts) (\i -> " (" ++ String.fromInt i ++ ")"))
  in LayoutGrid.inner [Typography.body1] [
       LayoutGrid.cell [LayoutGrid.span2, LayoutGrid.alignMiddle] [text (view_field field)],
       LayoutGrid.cell [LayoutGrid.span10]
         [FilterChipSet.chipSet [] (chip t) (ts |> List.map chip)]]

view_add_filter : Html Msg
view_add_filter =
  let option field = SelectItem.selectItem (SelectItem.config {value=field}) (view_field field)
  in case search_fields of
    [] -> Html.nothing
    x :: xs ->
      Select.outlined
        (Select.config
         |> Select.setLabel (Just "Add Filter")
         |> Select.setAttributes [style "margin" "16px 0"]
         |> Select.setOnChange Add_Filter)
        (option x)
        (xs |> List.map option)

view: Model -> Html Msg
view (Model model) =
  let
    field_facet field =
      model.facets |> Maybe.map (Dict.get field) |> Maybe.join |> Maybe.withDefault Dict.empty

    search i = if model.focus == Just i then Just model.filter_search else Nothing
    view_filter1 (i, filter) = view_filter (search i) (field_facet filter.field) (i, filter)

    maybe_view_facet field =
      let
        counts = field_facet field
        selected =
          model.search.facets |> Dict.get field |> Maybe.map .terms |> Maybe.withDefault Set.empty
        counts1 =
          if Dict.size counts > max_facet_terms || Dict.size counts < 2 then Dict.empty else counts
        terms = Dict.keys counts1 |> Set.fromList |> Set.union selected |> Set.toList |> List.sort
      in case terms of
        [] -> Nothing
        t::ts -> Just (Lazy.lazy5 view_facet field t ts counts1 selected)
    facets = facet_fields |> List.filterMap maybe_view_facet
  in
    LayoutGrid.layoutGrid [Elevation.z2, style "margin" "16px 0"] ([
      TextField.outlined (TextField.config
      |> TextField.setPlaceholder (Just "Enter search terms...")
      |> TextField.setAttributes
        [style "width" "100%", style "background-color" "white", style "margin-bottom" "16px"]
      |> TextField.setValue (Just model.search.any_filter)
      |> TextField.setOnInput Input_Any),
      h3 [Typography.headline6] [text "Filters"]] ++ (
      Array.toIndexedList model.search.filters
      |> List.map view_filter1) ++
    [view_add_filter] ++ (
    list_if (not (List.isEmpty facets)) (h3 [Typography.headline6] [text "Drill-down"])) ++
    facets)


{- queries -}

explode_query: String -> Query.Atom
explode_query s =
 case try_unquote s of
   Just s1 -> Query.Exact s1
   Nothing -> Query.Value s

atoms_query: String -> List Query.Atom
atoms_query s = explode_query s |> List.singleton

filter_query: Filter -> Query.Filter
filter_query filter =
  Query.Field_Filter filter.field (filter.value |> atoms_query)

facet_query: Facet -> Query.Select
facet_query facet = Query.Select facet.field (Set.toList facet.terms)

search_query: Search -> Query.Query
search_query search =
  let (exclude, filters) = search.filters |> Array.toList |> List.partition .exclude
  in Query.Query (
    (list_if (search.any_filter /= "") (search.any_filter |> atoms_query |> Query.Any_Filter)) ++
    (filters |> List.filter (.value >> String.isEmpty >> not) |> List.map filter_query))
    (exclude |> List.filter (.value >> String.isEmpty >> not) |> List.map filter_query)
    (Dict.toList search.facets |> List.map Tuple.second |> List.map facet_query)

get_query: Model -> Query.Query
get_query (Model model) = search_query model.search

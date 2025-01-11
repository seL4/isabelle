{- Author: Fabian Huch, TU Muenchen

Queries against the find facts server.
-}
module Query exposing (Atom(..), Filter(..), Select, Query, Query_Blocks, empty, empty_query,
  encode_query, encode_query_blocks, encode_query_block, Block, Blocks, Facets, Result,
  decode_block, decode_blocks, decode_result)


import Dict exposing (Dict)
import Json.Decode as Decode
import Json.Decode.Extra as Decode
import Json.Encode as Encode


{- queries -}

type Atom = Value String | Exact String
type Filter = Any_Filter (List Atom) | Field_Filter String (List Atom)
type alias Select = {field: String, values: List String}
type alias Query = {filters: List Filter, exclude: List Filter, selects: List Select}
type alias Query_Blocks = {query: Query, cursor: String}

empty: Query
empty = Query [] [] []

empty_atom: Atom -> Bool
empty_atom atom =
  case atom of
    Value s -> String.words s |> List.isEmpty
    Exact s -> String.words s |> List.isEmpty

empty_filter: Filter -> Bool
empty_filter filter =
  case filter of
    Any_Filter atoms -> List.all empty_atom atoms
    Field_Filter _ atoms -> List.all empty_atom atoms

empty_select: Select -> Bool
empty_select select = List.isEmpty select.values

empty_query: Query -> Bool
empty_query query =
  List.all empty_filter (query.filters ++ query.exclude) && List.all empty_select query.selects


{- json encoding -}

encode_atom: Atom -> Encode.Value
encode_atom atom =
  case atom of
    Exact phrase -> Encode.object [("exact", Encode.string phrase)]
    Value wildcard -> Encode.object [("value", Encode.string wildcard)]

encode_filter: Filter -> Encode.Value
encode_filter filter =
  case filter of
    Any_Filter atoms -> Encode.object [("either", Encode.list encode_atom atoms)]
    Field_Filter field atoms ->
      Encode.object [("either", Encode.list encode_atom atoms), ("field", Encode.string field)]

encode_select: Select -> Encode.Value
encode_select select =
  Encode.object [
    ("field", Encode.string select.field),
    ("values", Encode.list Encode.string select.values)]

encode_query: Query -> Encode.Value
encode_query query =
  Encode.object [
    ("filters", Encode.list encode_filter query.filters),
    ("exclude", Encode.list encode_filter query.exclude),
    ("selects", Encode.list encode_select query.selects)]

encode_query_blocks: Query_Blocks -> Encode.Value
encode_query_blocks query_blocks =
  Encode.object
    [("query", encode_query query_blocks.query), ("cursor", Encode.string query_blocks.cursor)]

encode_query_block: String -> Encode.Value
encode_query_block id = Encode.object [("id", Encode.string id)]


{- results -}

type alias Block = {
  id: String,
  chapter: String,
  session: String,
  theory: String,
  file: String,
  file_name: String,
  url: String,
  command: String,
  start_line: Int,
  src_before: String,
  src_after: String,
  html: String,
  entity_kname: Maybe String}

type alias Blocks = {num_found: Int, blocks: List Block, cursor: String}
type alias Facets = Dict String (Dict String Int)
type alias Result = {blocks: Blocks, facets: Facets}


{- json decoding -}

decode_block: Decode.Decoder Block
decode_block =
  Decode.succeed Block
  |> Decode.andMap (Decode.field "id" Decode.string)
  |> Decode.andMap (Decode.field "chapter" Decode.string)
  |> Decode.andMap (Decode.field "session" Decode.string)
  |> Decode.andMap (Decode.field "theory" Decode.string)
  |> Decode.andMap (Decode.field "file" Decode.string)
  |> Decode.andMap (Decode.field "file_name" Decode.string)
  |> Decode.andMap (Decode.field "url" Decode.string)
  |> Decode.andMap (Decode.field "command" Decode.string)
  |> Decode.andMap (Decode.field "start_line" Decode.int)
  |> Decode.andMap (Decode.field "src_before" Decode.string)
  |> Decode.andMap (Decode.field "src_after" Decode.string)
  |> Decode.andMap (Decode.field "html" Decode.string)
  |> Decode.andMap (Decode.field "entity_kname" (Decode.maybe Decode.string))

decode_blocks: Decode.Decoder Blocks
decode_blocks =
  Decode.map3 Blocks
    (Decode.field "num_found" Decode.int)
    (Decode.field "blocks" (Decode.list decode_block))
    (Decode.field "cursor" Decode.string)

decode_facets: Decode.Decoder Facets
decode_facets = Decode.dict (Decode.dict Decode.int)

decode_result: Decode.Decoder Result
decode_result =
  Decode.map2 Result (Decode.field "blocks" decode_blocks) (Decode.field "facets" decode_facets)

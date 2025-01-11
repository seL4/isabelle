{- Author: Fabian Huch, TU Muenchen

Generic parser combinators.
-}
module Parser exposing (Parser, succeed, fail, elem, rep, map, map2, map3, flat_map, or, parse)


type Parser a b = Parser (List a -> Maybe (List a, b))

succeed: b -> Parser a b
succeed y = Parser (\xs -> Just (xs, y))

fail: Parser a b
fail = Parser (always Nothing)

elem: (a -> Bool) -> Parser a a
elem cond =
  Parser (\xs ->
    case xs of
      [] -> Nothing
      x :: xs1 -> (if cond x then Just (xs1, x) else Nothing))

rep: Parser a b -> Parser a (List b)
rep (Parser parser) =
  let
    rep_rec xs =
      case parser xs of
        Nothing -> (xs, [])
        Just (xs1, y) -> Tuple.mapSecond ((::) y) (rep_rec xs1)
  in Parser (rep_rec >> Just)

map: (b -> c) -> Parser a b -> Parser a c
map f (Parser parser) =
  Parser (parser >> Maybe.map (Tuple.mapSecond f))

map2: (b -> c -> d) -> Parser a b -> Parser a c -> Parser a d
map2 f (Parser parser1) (Parser parser2) =
  Parser (\xs ->
    case parser1 xs of
      Nothing -> Nothing
      Just (xs1, y1) ->
        case (parser2 xs1) of
          Nothing -> Nothing
          Just (xs2, y2) -> Just (xs2, f y1 y2))

map3: (b -> c -> d -> e) -> Parser a b -> Parser a c -> Parser a d -> Parser a e
map3 f parser1 parser2 parser3 =
  map2 (\(b, c) d -> f b c d) (map2 (\b c -> (b, c)) parser1 parser2) parser3

flat_map: (b -> Parser a c) -> Parser a b -> Parser a c
flat_map f (Parser parser) =
  Parser (\xs ->
    case parser xs of
      Nothing -> Nothing
      Just (xs1, y) ->
        case (f y) of
         Parser parser1 -> parser1 xs1)

or: Parser a b -> Parser a b -> Parser a b
or (Parser parser1) (Parser parser2) =
  Parser (\xs ->
    case parser1 xs of
      Nothing -> parser2 xs
      res -> res)

parse : Parser a b -> List a -> Maybe b
parse (Parser parser) elems =
  case parser elems of
    Just ([], y) -> Just y
    _ -> Nothing

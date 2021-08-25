(*  Title:      Tools/Haskell/Haskell.thy
    Author:     Makarius

Support for Isabelle tools in Haskell.
*)

theory Haskell
  imports Main
begin

generate_file "Isabelle/Bytes.hs" = \<open>
{-  Title:      Isabelle/Bytes.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Compact byte strings.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/bytes.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/General/bytes.scala\<close>.
-}

{-# LANGUAGE TypeApplications #-}

module Isabelle.Bytes (
  Bytes,
  make, unmake, pack, unpack,
  empty, null, length, index, all, any,
  head, last, take, drop, isPrefixOf, isSuffixOf,
  concat, space, spaces, char, all_char, any_char, byte, singleton
)
where

import Prelude hiding (null, length, all, any, head, last, take, drop, concat)

import qualified Data.ByteString.Short as ShortByteString
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString as ByteString
import Data.ByteString (ByteString)
import qualified Data.List as List
import Data.Word (Word8)
import Data.Array (Array, array, (!))


type Bytes = ShortByteString

make :: ByteString -> Bytes
make = ShortByteString.toShort

unmake :: Bytes -> ByteString
unmake = ShortByteString.fromShort

pack :: [Word8] -> Bytes
pack = ShortByteString.pack

unpack :: Bytes -> [Word8]
unpack = ShortByteString.unpack

empty :: Bytes
empty = ShortByteString.empty

null :: Bytes -> Bool
null = ShortByteString.null

length :: Bytes -> Int
length = ShortByteString.length

index :: Bytes -> Int -> Word8
index = ShortByteString.index

all :: (Word8 -> Bool) -> Bytes -> Bool
all p = List.all p . unpack

any :: (Word8 -> Bool) -> Bytes -> Bool
any p = List.any p . unpack

head :: Bytes -> Word8
head bytes = index bytes 0

last :: Bytes -> Word8
last bytes = index bytes (length bytes - 1)

take :: Int -> Bytes -> Bytes
take n = pack . List.take n . unpack

drop :: Int -> Bytes -> Bytes
drop n = pack . List.drop n . unpack

isPrefixOf :: Bytes -> Bytes -> Bool
isPrefixOf bs1 bs2 =
  n1 <= n2 && List.all (\i -> index bs1 i == index bs2 i) [0 .. n1 - 1]
  where n1 = length bs1; n2 = length bs2

isSuffixOf :: Bytes -> Bytes -> Bool
isSuffixOf bs1 bs2 =
  n1 <= n2 && List.all (\i -> index bs1 i == index bs2 (i + k)) [0 .. n1 - 1]
  where n1 = length bs1; n2 = length bs2; k = n2 - n1

concat :: [Bytes] -> Bytes
concat = mconcat

space :: Word8
space = 32

small_spaces :: Array Int Bytes
small_spaces = array (0, 64) [(i, pack (replicate i space)) | i <- [0 .. 64]]

spaces :: Int -> Bytes
spaces n =
  if n < 64 then small_spaces ! n
  else concat ((small_spaces ! (n `mod` 64)) : replicate (n `div` 64) (small_spaces ! 64))

char :: Word8 -> Char
char = toEnum . fromEnum

all_char :: (Char -> Bool) -> Bytes -> Bool
all_char pred = all (pred . char)

any_char :: (Char -> Bool) -> Bytes -> Bool
any_char pred = any (pred . char)

byte :: Char -> Word8
byte = toEnum . fromEnum

singletons :: Array Word8 Bytes
singletons =
  array (minBound, maxBound)
    [(i, make (ByteString.singleton i)) | i <- [minBound .. maxBound]]

singleton :: Word8 -> Bytes
singleton b = singletons ! b
\<close>

generate_file "Isabelle/UTF8.hs" = \<open>
{-  Title:      Isabelle/UTF8.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Variations on UTF-8.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/utf8.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/General/utf8.scala\<close>.
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Isabelle.UTF8 (
  setup, setup3,
  Recode (..)
)
where

import qualified System.IO as IO
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Encoding
import qualified Data.Text.Encoding.Error as Error

import Data.ByteString (ByteString)

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)

setup :: IO.Handle -> IO ()
setup h = do
  IO.hSetEncoding h IO.utf8
  IO.hSetNewlineMode h IO.noNewlineTranslation

setup3 :: IO.Handle -> IO.Handle -> IO.Handle -> IO ()
setup3 h1 h2 h3 = do
  setup h1
  setup h2
  setup h3

class Recode a b where
  encode :: a -> b
  decode :: b -> a

instance Recode Text ByteString where
  encode :: Text -> ByteString
  encode = Encoding.encodeUtf8
  decode :: ByteString -> Text
  decode = Encoding.decodeUtf8With Error.lenientDecode

instance Recode Text Bytes where
  encode :: Text -> Bytes
  encode = Bytes.make . encode
  decode :: Bytes -> Text
  decode = decode . Bytes.unmake

instance Recode String ByteString where
  encode :: String -> ByteString
  encode = encode . Text.pack
  decode :: ByteString -> String
  decode = Text.unpack . decode

instance Recode String Bytes where
  encode :: String -> Bytes
  encode = encode . Text.pack
  decode :: Bytes -> String
  decode = Text.unpack . decode
\<close>

generate_file "Isabelle/Library.hs" = \<open>
{-  Title:      Isabelle/Library.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Basic library of Isabelle idioms.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/basics.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/library.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Isabelle.Library (
  (|>), (|->), (#>), (#->),

  fold, fold_rev, single, map_index, get_index, separate,

  StringLike, STRING (..), TEXT (..), BYTES (..),
  show_bytes, show_text,

  proper_string, enclose, quote, space_implode, commas, commas_quote, cat_lines,
  space_explode, split_lines, trim_line)
where

import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.String (IsString)
import qualified Data.List.Split as Split
import qualified Isabelle.Symbol as Symbol
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.UTF8 as UTF8


{- functions -}

(|>) :: a -> (a -> b) -> b
x |> f = f x

(|->) :: (a, b) -> (a -> b -> c) -> c
(x, y) |-> f = f x y

(#>) :: (a -> b) -> (b -> c) -> a -> c
(f #> g) x = x |> f |> g

(#->) :: (a -> (c, b)) -> (c -> b -> d) -> a -> d
(f #-> g) x  = x |> f |-> g


{- lists -}

fold :: (a -> b -> b) -> [a] -> b -> b
fold _ [] y = y
fold f (x : xs) y = fold f xs (f x y)

fold_rev :: (a -> b -> b) -> [a] -> b -> b
fold_rev _ [] y = y
fold_rev f (x : xs) y = f x (fold_rev f xs y)

single :: a -> [a]
single x = [x]

map_index :: ((Int, a) -> b) -> [a] -> [b]
map_index f = map_aux 0
  where
    map_aux _ [] = []
    map_aux i (x : xs) = f (i, x) : map_aux (i + 1) xs

get_index :: (a -> Maybe b) -> [a] -> Maybe (Int, b)
get_index f = get_aux 0
  where
    get_aux _ [] = Nothing
    get_aux i (x : xs) =
      case f x of
        Nothing -> get_aux (i + 1) xs
        Just y -> Just (i, y)

separate :: a -> [a] -> [a]
separate s (x : (xs @ (_ : _))) = x : s : separate s xs
separate _ xs = xs;


{- string-like interfaces -}

class (IsString a, Monoid a, Eq a, Ord a) => StringLike a where
  space_explode :: Char -> a -> [a]
  trim_line :: a -> a

gen_trim_line :: Int -> (Int -> Char) -> (Int -> a -> a) -> a -> a
gen_trim_line n at trim s =
  if n >= 2 && at (n - 2) == '\r' && at (n - 1) == '\n' then trim (n - 2) s
  else if n >= 1 && Symbol.is_ascii_line_terminator (at (n - 1)) then trim (n - 1) s
  else s

instance StringLike String where
  space_explode :: Char -> String -> [String]
  space_explode c = Split.split (Split.dropDelims (Split.whenElt (== c)))
  trim_line :: String -> String
  trim_line s = gen_trim_line (length s) ((!!) s) take s

instance StringLike Text where
  space_explode :: Char -> Text -> [Text]
  space_explode c str =
    if Text.null str then []
    else if Text.all (/= c) str then [str]
    else map Text.pack $ space_explode c $ Text.unpack str
  trim_line :: Text -> Text
  trim_line s = gen_trim_line (Text.length s) (Text.index s) Text.take s

instance StringLike Lazy.Text where
  space_explode :: Char -> Lazy.Text -> [Lazy.Text]
  space_explode c str =
    if Lazy.null str then []
    else if Lazy.all (/= c) str then [str]
    else map Lazy.pack $ space_explode c $ Lazy.unpack str
  trim_line :: Lazy.Text -> Lazy.Text
  trim_line = Lazy.fromStrict . trim_line . Lazy.toStrict

instance StringLike Bytes where
  space_explode :: Char -> Bytes -> [Bytes]
  space_explode c str =
    if Bytes.null str then []
    else if Bytes.all_char (/= c) str then [str]
    else
      explode (Bytes.unpack str)
      where
        explode rest =
          case span (/= (Bytes.byte c)) rest of
            (_, []) -> [Bytes.pack rest]
            (prfx, _ : rest') -> Bytes.pack prfx : explode rest'
  trim_line :: Bytes -> Bytes
  trim_line s = gen_trim_line (Bytes.length s) (Bytes.char . Bytes.index s) Bytes.take s

class StringLike a => STRING a where make_string :: a -> String
instance STRING String where make_string = id
instance STRING Text where make_string = Text.unpack
instance STRING Lazy.Text where make_string = Lazy.unpack
instance STRING Bytes where make_string = UTF8.decode

class StringLike a => TEXT a where make_text :: a -> Text
instance TEXT String where make_text = Text.pack
instance TEXT Text where make_text = id
instance TEXT Lazy.Text where make_text = Lazy.toStrict
instance TEXT Bytes where make_text = UTF8.decode

class StringLike a => BYTES a where make_bytes :: a -> Bytes
instance BYTES String where make_bytes = UTF8.encode
instance BYTES Text where make_bytes = UTF8.encode
instance BYTES Lazy.Text where make_bytes = UTF8.encode . Lazy.toStrict
instance BYTES Bytes where make_bytes = id

show_bytes :: Show a => a -> Bytes
show_bytes = make_bytes . show

show_text :: Show a => a -> Text
show_text = make_text . show


{- strings -}

proper_string :: StringLike a => a -> Maybe a
proper_string s = if s == "" then Nothing else Just s

enclose :: StringLike a => a -> a -> a -> a
enclose lpar rpar str = lpar <> str <> rpar

quote :: StringLike a => a -> a
quote = enclose "\"" "\""

space_implode :: StringLike a => a -> [a] -> a
space_implode s = mconcat . separate s

commas, commas_quote :: StringLike a => [a] -> a
commas = space_implode ", "
commas_quote = commas . map quote

split_lines :: StringLike a => a -> [a]
split_lines = space_explode '\n'

cat_lines :: StringLike a => [a] -> a
cat_lines = space_implode "\n"
\<close>


generate_file "Isabelle/Symbol.hs" = \<open>
{-  Title:      Isabelle/Symbols.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Isabelle text symbols.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/symbol.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/General/symbol_explode.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Symbol (
  Symbol, eof, is_eof, not_eof,

  is_ascii_letter, is_ascii_digit, is_ascii_hex, is_ascii_quasi,
  is_ascii_blank, is_ascii_line_terminator, is_ascii_letdig,
  is_ascii_identifier,

  explode
)
where

import Data.Word (Word8)
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


{- type -}

type Symbol = Bytes

eof :: Symbol
eof = ""

is_eof, not_eof :: Symbol -> Bool
is_eof = Bytes.null
not_eof = not . is_eof


{- ASCII characters -}

is_ascii_letter :: Char -> Bool
is_ascii_letter c = 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z'

is_ascii_digit :: Char -> Bool
is_ascii_digit c = '0' <= c && c <= '9'

is_ascii_hex :: Char -> Bool
is_ascii_hex c = '0' <= c && c <= '9' || 'A' <= c && c <= 'F' || 'a' <= c && c <= 'f'

is_ascii_quasi :: Char -> Bool
is_ascii_quasi c = c == '_' || c == '\''

is_ascii_blank :: Char -> Bool
is_ascii_blank c = c `elem` (" \t\n\11\f\r" :: String)

is_ascii_line_terminator :: Char -> Bool
is_ascii_line_terminator c = c == '\r' || c == '\n'

is_ascii_letdig :: Char -> Bool
is_ascii_letdig c = is_ascii_letter c || is_ascii_digit c || is_ascii_quasi c

is_ascii_identifier :: String -> Bool
is_ascii_identifier s =
  not (null s) && is_ascii_letter (head s) && all is_ascii_letdig s


{- explode symbols: ASCII, UTF8, named -}

is_utf8 :: Word8 -> Bool
is_utf8 b = b >= 128

is_utf8_trailer :: Word8 -> Bool
is_utf8_trailer b = 128 <= b && b < 192

is_utf8_control :: Word8 -> Bool
is_utf8_control b = 128 <= b && b < 160

(|>) :: a -> (a -> b) -> b
x |> f = f x

explode :: Bytes -> [Symbol]
explode string = scan 0
  where
    byte = Bytes.index string
    substring i j =
      if i == j - 1 then Bytes.singleton (byte i)
      else Bytes.pack (map byte [i .. j - 1])

    n = Bytes.length string
    test pred i = i < n && pred (byte i)
    test_char pred i = i < n && pred (Bytes.char (byte i))
    many pred i = if test pred i then many pred (i + 1) else i
    maybe_char c i = if test_char (== c) i then i + 1 else i
    maybe_ascii_id i =
      if test_char is_ascii_letter i
      then many (is_ascii_letdig . Bytes.char) (i + 1)
      else i

    scan i =
      if i < n then
        let
          b = byte i
          c = Bytes.char b
        in
          {-encoded newline-}
          if c == '\r' then "\n" : scan (maybe_char '\n' (i + 1))
          {-pseudo utf8: encoded ascii control-}
          else if b == 192 && test is_utf8_control (i + 1) && not (test is_utf8 (i + 2))
          then Bytes.singleton (byte (i + 1) - 128) : scan (i + 2)
          {-utf8-}
          else if is_utf8 b then
            let j = many is_utf8_trailer (i + 1)
            in substring i j : scan j
          {-named symbol-}
          else if c == '\\' && test_char (== '<') (i + 1) then
            let j = (i + 2) |> maybe_char '^' |> maybe_ascii_id |> maybe_char '>'
            in substring i j : scan j
          {-single character-}
          else Bytes.singleton b : scan (i + 1)
      else []
\<close>

generate_file "Isabelle/Buffer.hs" = \<open>
{-  Title:      Isabelle/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient buffer of byte strings.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/buffer.ML\<close>.
-}

module Isabelle.Buffer (T, empty, add, content)
where

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


newtype T = Buffer [Bytes]

empty :: T
empty = Buffer []

add :: Bytes -> T -> T
add b (Buffer bs) = Buffer (if Bytes.null b then bs else b : bs)

content :: T -> Bytes
content (Buffer bs) = Bytes.concat (reverse bs)
\<close>

generate_file "Isabelle/Value.hs" = \<open>
{-  Title:      Isabelle/Value.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Plain values, represented as string.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/value.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Value
  (print_bool, parse_bool, parse_nat, print_int, parse_int, print_real, parse_real)
where

import qualified Data.List as List
import qualified Text.Read as Read
import Isabelle.Bytes (Bytes)
import Isabelle.Library


{- bool -}

print_bool :: Bool -> Bytes
print_bool True = "true"
print_bool False = "false"

parse_bool :: Bytes -> Maybe Bool
parse_bool "true" = Just True
parse_bool "false" = Just False
parse_bool _ = Nothing


{- nat -}

parse_nat :: Bytes -> Maybe Int
parse_nat s =
  case Read.readMaybe (make_string s) of
    Just n | n >= 0 -> Just n
    _ -> Nothing


{- int -}

print_int :: Int -> Bytes
print_int = show_bytes

parse_int :: Bytes -> Maybe Int
parse_int = Read.readMaybe . make_string


{- real -}

print_real :: Double -> Bytes
print_real x =
  let s = show x in
    case span (/= '.') s of
      (a, '.' : b) | List.all (== '0') b -> make_bytes a
      _ -> make_bytes s

parse_real :: Bytes -> Maybe Double
parse_real = Read.readMaybe . make_string
\<close>

generate_file "Isabelle/Properties.hs" = \<open>
{-  Title:      Isabelle/Properties.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Property lists.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/properties.ML\<close>.
-}

module Isabelle.Properties (Entry, T, defined, get, get_value, put, remove)
where

import qualified Data.List as List
import Isabelle.Bytes (Bytes)


type Entry = (Bytes, Bytes)
type T = [Entry]

defined :: T -> Bytes -> Bool
defined props name = any (\(a, _) -> a == name) props

get :: T -> Bytes -> Maybe Bytes
get props name = List.lookup name props

get_value :: (Bytes -> Maybe a) -> T -> Bytes -> Maybe a
get_value parse props name =
  case get props name of
    Nothing -> Nothing
    Just s -> parse s

put :: Entry -> T -> T
put entry props = entry : remove (fst entry) props

remove :: Bytes -> T -> T
remove name props =
  if defined props name then filter (\(a, _) -> a /= name) props
  else props
\<close>

generate_file "Isabelle/Markup.hs" = \<open>
{-  Title:      Isabelle/Markup.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Quasi-abstract markup elements.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/markup.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.Markup (
  T, empty, is_empty, properties,

  nameN, name, xnameN, xname, kindN,

  bindingN, binding, entityN, entity, defN, refN,

  completionN, completion, no_completionN, no_completion,

  lineN, end_lineN, offsetN, end_offsetN, fileN, idN, positionN, position,
  position_properties, def_name,

  expressionN, expression,

  citationN, citation,

  pathN, path, urlN, url, docN, doc,

  markupN, consistentN, unbreakableN, indentN, widthN,
  blockN, block, breakN, break, fbreakN, fbreak, itemN, item,

  wordsN, words,

  tfreeN, tfree, tvarN, tvar, freeN, free, skolemN, skolem, boundN, bound, varN, var,
  numeralN, numeral, literalN, literal, delimiterN, delimiter, inner_stringN, inner_string,
  inner_cartoucheN, inner_cartouche,
  token_rangeN, token_range,
  sortingN, sorting, typingN, typing, class_parameterN, class_parameter,

  antiquotedN, antiquoted, antiquoteN, antiquote,

  paragraphN, paragraph, text_foldN, text_fold,

  keyword1N, keyword1, keyword2N, keyword2, keyword3N, keyword3, quasi_keywordN, quasi_keyword,
  improperN, improper, operatorN, operator, stringN, string, alt_stringN, alt_string,
  verbatimN, verbatim, cartoucheN, cartouche, commentN, comment, comment1N, comment1,
  comment2N, comment2, comment3N, comment3,

  forkedN, forked, joinedN, joined, runningN, running, finishedN, finished,
  failedN, failed, canceledN, canceled, initializedN, initialized, finalizedN, finalized,
  consolidatedN, consolidated,

  writelnN, writeln, stateN, state, informationN, information, tracingN, tracing,
  warningN, warning, legacyN, legacy, errorN, error, reportN, report, no_reportN, no_report,

  intensifyN, intensify,
  Output, no_output)
where

import Prelude hiding (words, error, break)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Isabelle.Library
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Value as Value
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


{- basic markup -}

type T = (Bytes, Properties.T)

empty :: T
empty = ("", [])

is_empty :: T -> Bool
is_empty ("", _) = True
is_empty _ = False

properties :: Properties.T -> T -> T
properties more_props (elem, props) =
  (elem, fold_rev Properties.put more_props props)

markup_elem :: Bytes -> T
markup_elem name = (name, [])

markup_string :: Bytes -> Bytes -> Bytes -> T
markup_string name prop = \s -> (name, [(prop, s)])


{- misc properties -}

nameN :: Bytes
nameN = \<open>Markup.nameN\<close>

name :: Bytes -> T -> T
name a = properties [(nameN, a)]

xnameN :: Bytes
xnameN = \<open>Markup.xnameN\<close>

xname :: Bytes -> T -> T
xname a = properties [(xnameN, a)]

kindN :: Bytes
kindN = \<open>Markup.kindN\<close>


{- formal entities -}

bindingN :: Bytes
bindingN = \<open>Markup.bindingN\<close>
binding :: T
binding = markup_elem bindingN

entityN :: Bytes
entityN = \<open>Markup.entityN\<close>
entity :: Bytes -> Bytes -> T
entity kind name =
  (entityN,
    (if Bytes.null name then [] else [(nameN, name)]) <>
    (if Bytes.null kind then [] else [(kindN, kind)]))

defN :: Bytes
defN = \<open>Markup.defN\<close>

refN :: Bytes
refN = \<open>Markup.refN\<close>


{- completion -}

completionN :: Bytes
completionN = \<open>Markup.completionN\<close>
completion :: T
completion = markup_elem completionN

no_completionN :: Bytes
no_completionN = \<open>Markup.no_completionN\<close>
no_completion :: T
no_completion = markup_elem no_completionN


{- position -}

lineN, end_lineN :: Bytes
lineN = \<open>Markup.lineN\<close>
end_lineN = \<open>Markup.end_lineN\<close>

offsetN, end_offsetN :: Bytes
offsetN = \<open>Markup.offsetN\<close>
end_offsetN = \<open>Markup.end_offsetN\<close>

fileN, idN :: Bytes
fileN = \<open>Markup.fileN\<close>
idN = \<open>Markup.idN\<close>

positionN :: Bytes
positionN = \<open>Markup.positionN\<close>
position :: T
position = markup_elem positionN

position_properties :: [Bytes]
position_properties = [lineN, offsetN, end_offsetN, fileN, idN]


{- position "def" names -}

make_def :: Bytes -> Bytes
make_def a = "def_" <> a

def_names :: Map Bytes Bytes
def_names = Map.fromList $ map (\a -> (a, make_def a)) position_properties

def_name :: Bytes -> Bytes
def_name a =
  case Map.lookup a def_names of
    Just b -> b
    Nothing -> make_def a


{- expression -}

expressionN :: Bytes
expressionN = \<open>Markup.expressionN\<close>

expression :: Bytes -> T
expression kind = (expressionN, if kind == "" then [] else [(kindN, kind)])


{- citation -}

citationN :: Bytes
citationN = \<open>Markup.citationN\<close>
citation :: Bytes -> T
citation = markup_string nameN citationN


{- external resources -}

pathN :: Bytes
pathN = \<open>Markup.pathN\<close>
path :: Bytes -> T
path = markup_string pathN nameN

urlN :: Bytes
urlN = \<open>Markup.urlN\<close>
url :: Bytes -> T
url = markup_string urlN nameN

docN :: Bytes
docN = \<open>Markup.docN\<close>
doc :: Bytes -> T
doc = markup_string docN nameN


{- pretty printing -}

markupN, consistentN, unbreakableN, indentN :: Bytes
markupN = \<open>Markup.markupN\<close>
consistentN = \<open>Markup.consistentN\<close>
unbreakableN = \<open>Markup.unbreakableN\<close>
indentN = \<open>Markup.indentN\<close>

widthN :: Bytes
widthN = \<open>Markup.widthN\<close>

blockN :: Bytes
blockN = \<open>Markup.blockN\<close>
block :: Bool -> Int -> T
block c i =
  (blockN,
    (if c then [(consistentN, Value.print_bool c)] else []) <>
    (if i /= 0 then [(indentN, Value.print_int i)] else []))

breakN :: Bytes
breakN = \<open>Markup.breakN\<close>
break :: Int -> Int -> T
break w i =
  (breakN,
    (if w /= 0 then [(widthN, Value.print_int w)] else []) <>
    (if i /= 0 then [(indentN, Value.print_int i)] else []))

fbreakN :: Bytes
fbreakN = \<open>Markup.fbreakN\<close>
fbreak :: T
fbreak = markup_elem fbreakN

itemN :: Bytes
itemN = \<open>Markup.itemN\<close>
item :: T
item = markup_elem itemN


{- text properties -}

wordsN :: Bytes
wordsN = \<open>Markup.wordsN\<close>
words :: T
words = markup_elem wordsN


{- inner syntax -}

tfreeN :: Bytes
tfreeN = \<open>Markup.tfreeN\<close>
tfree :: T
tfree = markup_elem tfreeN

tvarN :: Bytes
tvarN = \<open>Markup.tvarN\<close>
tvar :: T
tvar = markup_elem tvarN

freeN :: Bytes
freeN = \<open>Markup.freeN\<close>
free :: T
free = markup_elem freeN

skolemN :: Bytes
skolemN = \<open>Markup.skolemN\<close>
skolem :: T
skolem = markup_elem skolemN

boundN :: Bytes
boundN = \<open>Markup.boundN\<close>
bound :: T
bound = markup_elem boundN

varN :: Bytes
varN = \<open>Markup.varN\<close>
var :: T
var = markup_elem varN

numeralN :: Bytes
numeralN = \<open>Markup.numeralN\<close>
numeral :: T
numeral = markup_elem numeralN

literalN :: Bytes
literalN = \<open>Markup.literalN\<close>
literal :: T
literal = markup_elem literalN

delimiterN :: Bytes
delimiterN = \<open>Markup.delimiterN\<close>
delimiter :: T
delimiter = markup_elem delimiterN

inner_stringN :: Bytes
inner_stringN = \<open>Markup.inner_stringN\<close>
inner_string :: T
inner_string = markup_elem inner_stringN

inner_cartoucheN :: Bytes
inner_cartoucheN = \<open>Markup.inner_cartoucheN\<close>
inner_cartouche :: T
inner_cartouche = markup_elem inner_cartoucheN


token_rangeN :: Bytes
token_rangeN = \<open>Markup.token_rangeN\<close>
token_range :: T
token_range = markup_elem token_rangeN


sortingN :: Bytes
sortingN = \<open>Markup.sortingN\<close>
sorting :: T
sorting = markup_elem sortingN

typingN :: Bytes
typingN = \<open>Markup.typingN\<close>
typing :: T
typing = markup_elem typingN

class_parameterN :: Bytes
class_parameterN = \<open>Markup.class_parameterN\<close>
class_parameter :: T
class_parameter = markup_elem class_parameterN


{- antiquotations -}

antiquotedN :: Bytes
antiquotedN = \<open>Markup.antiquotedN\<close>
antiquoted :: T
antiquoted = markup_elem antiquotedN

antiquoteN :: Bytes
antiquoteN = \<open>Markup.antiquoteN\<close>
antiquote :: T
antiquote = markup_elem antiquoteN


{- text structure -}

paragraphN :: Bytes
paragraphN = \<open>Markup.paragraphN\<close>
paragraph :: T
paragraph = markup_elem paragraphN

text_foldN :: Bytes
text_foldN = \<open>Markup.text_foldN\<close>
text_fold :: T
text_fold = markup_elem text_foldN


{- outer syntax -}

keyword1N :: Bytes
keyword1N = \<open>Markup.keyword1N\<close>
keyword1 :: T
keyword1 = markup_elem keyword1N

keyword2N :: Bytes
keyword2N = \<open>Markup.keyword2N\<close>
keyword2 :: T
keyword2 = markup_elem keyword2N

keyword3N :: Bytes
keyword3N = \<open>Markup.keyword3N\<close>
keyword3 :: T
keyword3 = markup_elem keyword3N

quasi_keywordN :: Bytes
quasi_keywordN = \<open>Markup.quasi_keywordN\<close>
quasi_keyword :: T
quasi_keyword = markup_elem quasi_keywordN

improperN :: Bytes
improperN = \<open>Markup.improperN\<close>
improper :: T
improper = markup_elem improperN

operatorN :: Bytes
operatorN = \<open>Markup.operatorN\<close>
operator :: T
operator = markup_elem operatorN

stringN :: Bytes
stringN = \<open>Markup.stringN\<close>
string :: T
string = markup_elem stringN

alt_stringN :: Bytes
alt_stringN = \<open>Markup.alt_stringN\<close>
alt_string :: T
alt_string = markup_elem alt_stringN

verbatimN :: Bytes
verbatimN = \<open>Markup.verbatimN\<close>
verbatim :: T
verbatim = markup_elem verbatimN

cartoucheN :: Bytes
cartoucheN = \<open>Markup.cartoucheN\<close>
cartouche :: T
cartouche = markup_elem cartoucheN

commentN :: Bytes
commentN = \<open>Markup.commentN\<close>
comment :: T
comment = markup_elem commentN


{- comments -}

comment1N :: Bytes
comment1N = \<open>Markup.comment1N\<close>
comment1 :: T
comment1 = markup_elem comment1N

comment2N :: Bytes
comment2N = \<open>Markup.comment2N\<close>
comment2 :: T
comment2 = markup_elem comment2N

comment3N :: Bytes
comment3N = \<open>Markup.comment3N\<close>
comment3 :: T
comment3 = markup_elem comment3N


{- command status -}

forkedN, joinedN, runningN, finishedN, failedN, canceledN,
  initializedN, finalizedN, consolidatedN :: Bytes
forkedN = \<open>Markup.forkedN\<close>
joinedN = \<open>Markup.joinedN\<close>
runningN = \<open>Markup.runningN\<close>
finishedN = \<open>Markup.finishedN\<close>
failedN = \<open>Markup.failedN\<close>
canceledN = \<open>Markup.canceledN\<close>
initializedN = \<open>Markup.initializedN\<close>
finalizedN = \<open>Markup.finalizedN\<close>
consolidatedN = \<open>Markup.consolidatedN\<close>

forked, joined, running, finished, failed, canceled,
  initialized, finalized, consolidated :: T
forked = markup_elem forkedN
joined = markup_elem joinedN
running = markup_elem runningN
finished = markup_elem finishedN
failed = markup_elem failedN
canceled = markup_elem canceledN
initialized = markup_elem initializedN
finalized = markup_elem finalizedN
consolidated = markup_elem consolidatedN


{- messages -}

writelnN :: Bytes
writelnN = \<open>Markup.writelnN\<close>
writeln :: T
writeln = markup_elem writelnN

stateN :: Bytes
stateN = \<open>Markup.stateN\<close>
state :: T
state = markup_elem stateN

informationN :: Bytes
informationN = \<open>Markup.informationN\<close>
information :: T
information = markup_elem informationN

tracingN :: Bytes
tracingN = \<open>Markup.tracingN\<close>
tracing :: T
tracing = markup_elem tracingN

warningN :: Bytes
warningN = \<open>Markup.warningN\<close>
warning :: T
warning = markup_elem warningN

legacyN :: Bytes
legacyN = \<open>Markup.legacyN\<close>
legacy :: T
legacy = markup_elem legacyN

errorN :: Bytes
errorN = \<open>Markup.errorN\<close>
error :: T
error = markup_elem errorN

reportN :: Bytes
reportN = \<open>Markup.reportN\<close>
report :: T
report = markup_elem reportN

no_reportN :: Bytes
no_reportN = \<open>Markup.no_reportN\<close>
no_report :: T
no_report = markup_elem no_reportN

intensifyN :: Bytes
intensifyN = \<open>Markup.intensifyN\<close>
intensify :: T
intensify = markup_elem intensifyN


{- output -}

type Output = (Bytes, Bytes)

no_output :: Output
no_output = ("", "")
\<close>

generate_file "Isabelle/Position.hs" = \<open>
{-  Title:      Isabelle/Position.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Source positions starting from 1; values <= 0 mean "absent". Count Isabelle
symbols, not UTF8 bytes nor UTF16 characters. Position range specifies a
right-open interval offset .. end_offset (exclusive).

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/position.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Position (
  T, line_of, column_of, offset_of, end_offset_of, file_of, id_of,
  start, none, put_file, file, file_only, put_id, id, id_only,
  symbol, symbol_explode, symbol_explode_string, shift_offsets,
  of_properties, properties_of, def_properties_of, entity_markup, make_entity_markup,
  Report, Report_Text, is_reported, is_reported_range, here,
  Range, no_range, no_range_position, range_position, range
)
where

import Prelude hiding (id)
import Data.Maybe (isJust, fromMaybe)
import Data.Bifunctor (first)
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Value as Value
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Markup as Markup
import qualified Isabelle.YXML as YXML
import Isabelle.Library
import qualified Isabelle.Symbol as Symbol
import Isabelle.Symbol (Symbol)


{- position -}

data T =
  Position {
    _line :: Int,
    _column :: Int,
    _offset :: Int,
    _end_offset :: Int,
    _file :: Bytes,
    _id :: Bytes }
  deriving (Eq, Ord)

valid, invalid :: Int -> Bool
valid i = i > 0
invalid = not . valid

maybe_valid :: Int -> Maybe Int
maybe_valid i = if valid i then Just i else Nothing

if_valid :: Int -> Int -> Int
if_valid i i' = if valid i then i' else i


{- fields -}

line_of, column_of, offset_of, end_offset_of :: T -> Maybe Int
line_of = maybe_valid . _line
column_of = maybe_valid . _column
offset_of = maybe_valid . _offset
end_offset_of = maybe_valid . _end_offset

file_of :: T -> Maybe Bytes
file_of = proper_string . _file

id_of :: T -> Maybe Bytes
id_of = proper_string . _id


{- make position -}

start :: T
start = Position 1 1 1 0 Bytes.empty Bytes.empty

none :: T
none = Position 0 0 0 0 Bytes.empty Bytes.empty

put_file :: Bytes -> T -> T
put_file file pos = pos { _file = file }

file :: Bytes -> T
file file = put_file file start

file_only :: Bytes -> T
file_only file = put_file file none

put_id :: Bytes -> T -> T
put_id id pos = pos { _id = id }

id :: Bytes -> T
id id = put_id id start

id_only :: Bytes -> T
id_only id = put_id id none


{- count position -}

count_line :: Symbol -> Int -> Int
count_line "\n" line = if_valid line (line + 1)
count_line _ line = line

count_column :: Symbol -> Int -> Int
count_column "\n" column = if_valid column 1
count_column s column = if Symbol.not_eof s then if_valid column (column + 1) else column

count_offset :: Symbol -> Int -> Int
count_offset s offset = if Symbol.not_eof s then if_valid offset (offset + 1) else offset

symbol :: Symbol -> T -> T
symbol s pos =
  pos {
    _line = count_line s (_line pos),
    _column = count_column s (_column pos),
    _offset = count_offset s (_offset pos) }

symbol_explode :: BYTES a => a -> T -> T
symbol_explode = fold symbol . Symbol.explode . make_bytes

symbol_explode_string :: String -> T -> T
symbol_explode_string = symbol_explode


{- shift offsets -}

shift_offsets :: Int -> T -> T
shift_offsets shift pos = pos { _offset = offset', _end_offset = end_offset' }
  where
    offset = _offset pos
    end_offset = _end_offset pos
    offset' = if invalid offset || invalid shift then offset else offset + shift
    end_offset' = if invalid end_offset || invalid shift then end_offset else end_offset + shift


{- markup properties -}

get_string :: Properties.T -> Bytes -> Bytes
get_string props name = fromMaybe "" (Properties.get_value Just props name)

get_int :: Properties.T -> Bytes -> Int
get_int props name = fromMaybe 0 (Properties.get_value Value.parse_int props name)

of_properties :: Properties.T -> T
of_properties props =
  none {
    _line = get_int props Markup.lineN,
    _offset = get_int props Markup.offsetN,
    _end_offset = get_int props Markup.end_offsetN,
    _file = get_string props Markup.fileN,
    _id = get_string props Markup.idN }

string_entry :: Bytes -> Bytes -> Properties.T
string_entry k s = if Bytes.null s then [] else [(k, s)]

int_entry :: Bytes -> Int -> Properties.T
int_entry k i = if invalid i then [] else [(k, Value.print_int i)]

properties_of :: T -> Properties.T
properties_of pos =
  int_entry Markup.lineN (_line pos) ++
  int_entry Markup.offsetN (_offset pos) ++
  int_entry Markup.end_offsetN (_end_offset pos) ++
  string_entry Markup.fileN (_file pos) ++
  string_entry Markup.idN (_id pos)

def_properties_of :: T -> Properties.T
def_properties_of = properties_of #> map (first Markup.def_name)

entity_markup :: Bytes -> (Bytes, T) -> Markup.T
entity_markup kind (name, pos) =
  Markup.entity kind name |> Markup.properties (def_properties_of pos)

make_entity_markup :: Bool -> Int -> Bytes -> (Bytes, T) -> Markup.T
make_entity_markup def serial kind (name, pos) =
  let
    props =
      if def then (Markup.defN, Value.print_int serial) : properties_of pos
      else (Markup.refN, Value.print_int serial) : def_properties_of pos
  in Markup.entity kind name |> Markup.properties props


{- reports -}

type Report = (T, Markup.T)
type Report_Text = (Report, Bytes)

is_reported :: T -> Bool
is_reported pos = isJust (offset_of pos) && isJust (id_of pos)

is_reported_range :: T -> Bool
is_reported_range pos = is_reported pos && isJust (end_offset_of pos)


{- here: user output -}

here :: T -> Bytes
here pos = if Bytes.null s2 then "" else s1 <> m1 <> s2 <> m2
  where
    props = properties_of pos
    (m1, m2) = YXML.output_markup (Markup.properties props Markup.position)
    (s1, s2) =
      case (line_of pos, file_of pos) of
        (Just i, Nothing) -> (" ", "(line " <> Value.print_int i <> ")")
        (Just i, Just name) -> (" ", "(line " <> Value.print_int i <> " of " <> quote name <> ")")
        (Nothing, Just name) -> (" ", "(file " <> quote name <> ")")
        _ -> if is_reported pos then ("", "\092<^here>") else ("", "")


{- range -}

type Range = (T, T)

no_range :: Range
no_range = (none, none)

no_range_position :: T -> T
no_range_position pos = pos { _end_offset = 0 }

range_position :: Range -> T
range_position (pos, pos') = pos { _end_offset = _offset pos' }

range :: Range -> Range
range (pos, pos') = (range_position (pos, pos'), no_range_position pos')
\<close>

generate_file "Isabelle/XML.hs" = \<open>
{-  Title:      Isabelle/XML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Untyped XML trees and representation of ML values.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.XML (Attributes, Body, Tree(..), wrap_elem, unwrap_elem, content_of)
where

import Isabelle.Library
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Buffer as Buffer
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


{- types -}

type Attributes = Properties.T
type Body = [Tree]
data Tree = Elem (Markup.T, Body) | Text Bytes


{- wrapped elements -}

wrap_elem :: ((Markup.T, Body), [Tree]) -> Tree
wrap_elem (((a, atts), body1), body2) =
  Elem ((\<open>XML.xml_elemN\<close>, (\<open>XML.xml_nameN\<close>, a) : atts), Elem ((\<open>XML.xml_bodyN\<close>, []), body1) : body2)

unwrap_elem :: Tree -> Maybe ((Markup.T, Body), [Tree])
unwrap_elem
  (Elem ((\<open>XML.xml_elemN\<close>, (\<open>XML.xml_nameN\<close>, a) : atts), Elem ((\<open>XML.xml_bodyN\<close>, []), body1) : body2)) =
  Just (((a, atts), body1), body2)
unwrap_elem _ = Nothing


{- text content -}

add_content :: Tree -> Buffer.T -> Buffer.T
add_content tree =
  case unwrap_elem tree of
    Just (_, ts) -> fold add_content ts
    Nothing ->
      case tree of
        Elem (_, ts) -> fold add_content ts
        Text s -> Buffer.add s

content_of :: Body -> Bytes
content_of body = Buffer.empty |> fold add_content body |> Buffer.content


{- string representation -}

encode_char :: Char -> String
encode_char '<' = "&lt;"
encode_char '>' = "&gt;"
encode_char '&' = "&amp;"
encode_char '\'' = "&apos;"
encode_char '\"' = "&quot;"
encode_char c = [c]

encode_text :: Bytes -> Bytes
encode_text = make_bytes . concatMap (encode_char . Bytes.char) . Bytes.unpack

instance Show Tree where
  show tree =
    Buffer.empty |> show_tree tree |> Buffer.content |> make_string
    where
      show_tree (Elem ((name, atts), [])) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add "/>"
      show_tree (Elem ((name, atts), ts)) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add ">" #>
        fold show_tree ts #>
        Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
      show_tree (Text s) = Buffer.add (encode_text s)

      show_elem name atts =
        space_implode " " (name : map (\(a, x) -> a <> "=\"" <> encode_text x <> "\"") atts)
\<close>

generate_file "Isabelle/XML/Encode.hs" = \<open>
{-  Title:      Isabelle/XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.XML.Encode (
  A, T, V, P,

  int_atom, bool_atom, unit_atom,

  tree, properties, string, int, bool, unit, pair, triple, list, option, variant
)
where

import Data.Maybe (fromJust)

import Isabelle.Library
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML


type A a = a -> Bytes
type T a = a -> XML.Body
type V a = a -> Maybe ([Bytes], XML.Body)
type P a = a -> [Bytes]


-- atomic values

int_atom :: A Int
int_atom = Value.print_int

bool_atom :: A Bool
bool_atom False = "0"
bool_atom True = "1"

unit_atom :: A ()
unit_atom () = ""


-- structural nodes

node ts = XML.Elem ((":", []), ts)

vector = map_index (\(i, x) -> (int_atom i, x))

tagged (tag, (xs, ts)) = XML.Elem ((int_atom tag, vector xs), ts)


-- representation of standard types

tree :: T XML.Tree
tree t = [t]

properties :: T Properties.T
properties props = [XML.Elem ((":", props), [])]

string :: T Bytes
string "" = []
string s = [XML.Text s]

int :: T Int
int = string . int_atom

bool :: T Bool
bool = string . bool_atom

unit :: T ()
unit = string . unit_atom

pair :: T a -> T b -> T (a, b)
pair f g (x, y) = [node (f x), node (g y)]

triple :: T a -> T b -> T c -> T (a, b, c)
triple f g h (x, y, z) = [node (f x), node (g y), node (h z)]

list :: T a -> T [a]
list f xs = map (node . f) xs

option :: T a -> T (Maybe a)
option _ Nothing = []
option f (Just x) = [node (f x)]

variant :: [V a] -> T a
variant fs x = [tagged (fromJust (get_index (\f -> f x) fs))]
\<close>

generate_file "Isabelle/XML/Decode.hs" = \<open>
{-  Title:      Isabelle/XML/Decode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.XML.Decode (
  A, T, V, P,

  int_atom, bool_atom, unit_atom,

  tree, properties, string, int, bool, unit, pair, triple, list, option, variant
)
where

import Isabelle.Library
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML


type A a = Bytes -> a
type T a = XML.Body -> a
type V a = ([Bytes], XML.Body) -> a
type P a = [Bytes] -> a

err_atom = error "Malformed XML atom"
err_body = error "Malformed XML body"


{- atomic values -}

int_atom :: A Int
int_atom s =
  case Value.parse_int s of
    Just i -> i
    Nothing -> err_atom

bool_atom :: A Bool
bool_atom "0" = False
bool_atom "1" = True
bool_atom _ = err_atom

unit_atom :: A ()
unit_atom "" = ()
unit_atom _ = err_atom


{- structural nodes -}

node (XML.Elem ((":", []), ts)) = ts
node _ = err_body

vector atts =
  map_index (\(i, (a, x)) -> if int_atom a == i then x else err_atom) atts

tagged (XML.Elem ((name, atts), ts)) = (int_atom name, (vector atts, ts))
tagged _ = err_body


{- representation of standard types -}

tree :: T XML.Tree
tree [t] = t
tree _ = err_body

properties :: T Properties.T
properties [XML.Elem ((":", props), [])] = props
properties _ = err_body

string :: T Bytes
string [] = ""
string [XML.Text s] = s
string _ = err_body

int :: T Int
int = int_atom . string

bool :: T Bool
bool = bool_atom . string

unit :: T ()
unit = unit_atom . string

pair :: T a -> T b -> T (a, b)
pair f g [t1, t2] = (f (node t1), g (node t2))
pair _ _ _ = err_body

triple :: T a -> T b -> T c -> T (a, b, c)
triple f g h [t1, t2, t3] = (f (node t1), g (node t2), h (node t3))
triple _ _ _ _ = err_body

list :: T a -> T [a]
list f ts = map (f . node) ts

option :: T a -> T (Maybe a)
option _ [] = Nothing
option f [t] = Just (f (node t))
option _ _ = err_body

variant :: [V a] -> T a
variant fs [t] = (fs !! tag) (xs, ts)
  where (tag, (xs, ts)) = tagged t
variant _ _ = err_body
\<close>

generate_file "Isabelle/YXML.hs" = \<open>
{-  Title:      Isabelle/YXML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text representation of XML trees.  Suitable for direct
inlining into plain text.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/yxml.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-incomplete-patterns #-}

module Isabelle.YXML (charX, charY, strX, strY, detect, output_markup,
  buffer_body, buffer, string_of_body, string_of, parse_body, parse)
where

import qualified Data.List as List
import Data.Word (Word8)

import Isabelle.Library
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.Buffer as Buffer


{- markers -}

charX, charY :: Word8
charX = 5
charY = 6

strX, strY, strXY, strXYX :: Bytes
strX = Bytes.singleton charX
strY = Bytes.singleton charY
strXY = strX <> strY
strXYX = strXY <> strX

detect :: Bytes -> Bool
detect = Bytes.any (\c -> c == charX || c == charY)


{- output -}

output_markup :: Markup.T -> Markup.Output
output_markup markup@(name, atts) =
  if Markup.is_empty markup then Markup.no_output
  else (strXY <> name <> Bytes.concat (map (\(a, x) -> strY <> a <> "=" <> x) atts) <> strX, strXYX)

buffer_attrib (a, x) =
  Buffer.add strY #> Buffer.add a #> Buffer.add "=" #> Buffer.add x

buffer_body :: XML.Body -> Buffer.T -> Buffer.T
buffer_body = fold buffer

buffer :: XML.Tree -> Buffer.T -> Buffer.T
buffer (XML.Elem ((name, atts), ts)) =
  Buffer.add strXY #> Buffer.add name #> fold buffer_attrib atts #> Buffer.add strX #>
  buffer_body ts #>
  Buffer.add strXYX
buffer (XML.Text s) = Buffer.add s

string_of_body :: XML.Body -> Bytes
string_of_body body = Buffer.empty |> buffer_body body |> Buffer.content

string_of :: XML.Tree -> Bytes
string_of = string_of_body . single


{- parse -}

-- split: fields or non-empty tokens

split :: Bool -> Word8 -> [Word8] -> [[Word8]]
split _ _ [] = []
split fields sep str = splitting str
  where
    splitting rest =
      case span (/= sep) rest of
        (_, []) -> cons rest []
        (prfx, _ : rest') -> cons prfx (splitting rest')
    cons item = if fields || not (null item) then (:) item else id


-- structural errors

err :: Bytes -> a
err msg = error (make_string ("Malformed YXML: " <> msg))

err_attribute = err "bad attribute"
err_element = err "bad element"

err_unbalanced :: Bytes -> a
err_unbalanced name =
  if Bytes.null name then err "unbalanced element"
  else err ("unbalanced element " <> quote name)


-- stack operations

add x ((elem, body) : pending) = (elem, x : body) : pending

push name atts pending =
  if Bytes.null name then err_element
  else ((name, atts), []) : pending

pop (((name, atts), body) : pending) =
  if Bytes.null name then err_unbalanced name
  else add (XML.Elem ((name, atts), reverse body)) pending


-- parsing

parse_attrib s =
  case List.elemIndex (Bytes.byte '=') s of
    Just i | i > 0 -> (Bytes.pack $ take i s, Bytes.pack $ drop (i + 1) s)
    _ -> err_attribute

parse_chunk [[], []] = pop
parse_chunk ([] : name : atts) = push (Bytes.pack name) (map parse_attrib atts)
parse_chunk txts = fold (add . XML.Text . Bytes.pack) txts

parse_body :: Bytes -> XML.Body
parse_body source =
  case fold parse_chunk chunks [((Bytes.empty, []), [])] of
    [((name, _), result)] | Bytes.null name -> reverse result
    ((name, _), _) : _ -> err_unbalanced name
  where chunks = source |> Bytes.unpack |> split False charX |> map (split True charY)

parse :: Bytes -> XML.Tree
parse source =
  case parse_body source of
    [result] -> result
    [] -> XML.Text ""
    _ -> err "multiple results"
\<close>

generate_file "Isabelle/Completion.hs" = \<open>
{-  Title:      Isabelle/Completion.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Completion of names.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/completion.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Completion (
    Name, T, names, none, make, markup_element, markup_report, make_report
  ) where

import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Name as Name
import Isabelle.Name (Name)
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Markup as Markup
import Isabelle.XML.Classes
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML


type Names = [(Name, (Name, Name))]  -- external name, kind, internal name
data T = Completion Properties.T Int Names  -- position, total length, names

names :: Int -> Properties.T -> Names -> T
names limit props names = Completion props (length names) (take limit names)

none :: T
none = names 0 [] []

make :: Int -> (Name, Properties.T) -> ((Name -> Bool) -> Names) -> T
make limit (name, props) make_names =
  if name /= "" && name /= "_" then
    names limit props (make_names (Bytes.isPrefixOf (Name.clean name)))
  else none

markup_element :: T -> (Markup.T, XML.Body)
markup_element (Completion props total names) =
  if not (null names) then
    (Markup.properties props Markup.completion, encode (total, names))
  else (Markup.empty, [])

markup_report :: [T] -> Name
markup_report [] = Bytes.empty
markup_report elems =
  YXML.string_of $ XML.Elem (Markup.report, map (XML.Elem . markup_element) elems)

make_report :: Int -> (Name, Properties.T) -> ((Name -> Bool) -> Names) -> Name
make_report limit name_props make_names =
  markup_report [make limit name_props make_names]
\<close>

generate_file "Isabelle/File.hs" = \<open>
{-  Title:      Isabelle/File.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

File-system operations.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/file.ML\<close>.
-}

module Isabelle.File (read, write, append) where

import Prelude hiding (read)
import qualified System.IO as IO
import qualified Data.ByteString as ByteString
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)

read :: IO.FilePath -> IO Bytes
read path = Bytes.make <$> IO.withFile path IO.ReadMode ByteString.hGetContents

write :: IO.FilePath -> Bytes -> IO ()
write path bs = IO.withFile path IO.WriteMode (\h -> ByteString.hPut h (Bytes.unmake bs))

append :: IO.FilePath -> Bytes -> IO ()
append path bs = IO.withFile path IO.AppendMode (\h -> ByteString.hPut h (Bytes.unmake bs))
\<close>

generate_file "Isabelle/Pretty.hs" = \<open>
{-  Title:      Isabelle/Pretty.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Generic pretty printing module.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/pretty.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.Pretty (
  T, symbolic, formatted, unformatted,

  str, brk_indent, brk, fbrk, breaks, fbreaks, blk, block, strs, markup, mark, mark_str, marks_str,
  item, text_fold, keyword1, keyword2, text, paragraph, para, quote, cartouche, separate,
  commas, enclose, enum, list, str_list, big_list)
where

import qualified Data.List as List

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import Isabelle.Library hiding (enclose, quote, separate, commas)
import qualified Isabelle.Buffer as Buffer
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML


data T =
    Block Markup.T Bool Int [T]
  | Break Int Int
  | Str Bytes


{- output -}

symbolic_text s = if Bytes.null s then [] else [XML.Text s]

symbolic_markup markup body =
  if Markup.is_empty markup then body
  else [XML.Elem (markup, body)]

symbolic :: T -> XML.Body
symbolic (Block markup consistent indent prts) =
  concatMap symbolic prts
  |> symbolic_markup block_markup
  |> symbolic_markup markup
  where block_markup = if null prts then Markup.empty else Markup.block consistent indent
symbolic (Break wd ind) = [XML.Elem (Markup.break wd ind, symbolic_text (Bytes.spaces wd))]
symbolic (Str s) = symbolic_text s

formatted :: T -> Bytes
formatted = YXML.string_of_body . symbolic

unformatted :: T -> Bytes
unformatted prt = Buffer.empty |> out prt |> Buffer.content
  where
    out (Block markup _ _ prts) =
      let (bg, en) = YXML.output_markup markup
      in Buffer.add bg #> fold out prts #> Buffer.add en
    out (Break _ wd) = Buffer.add (Bytes.spaces wd)
    out (Str s) = Buffer.add s


{- derived operations to create formatting expressions -}

force_nat n | n < 0 = 0
force_nat n = n

str :: BYTES a => a -> T
str = Str . make_bytes

brk_indent :: Int -> Int -> T
brk_indent wd ind = Break (force_nat wd) ind

brk :: Int -> T
brk wd = brk_indent wd 0

fbrk :: T
fbrk = Str "\n"

breaks, fbreaks :: [T] -> [T]
breaks = List.intersperse (brk 1)
fbreaks = List.intersperse fbrk

blk :: (Int, [T]) -> T
blk (indent, es) = Block Markup.empty False (force_nat indent) es

block :: [T] -> T
block prts = blk (2, prts)

strs :: BYTES a => [a] -> T
strs = block . breaks . map str

markup :: Markup.T -> [T] -> T
markup m = Block m False 0

mark :: Markup.T -> T -> T
mark m prt = if m == Markup.empty then prt else markup m [prt]

mark_str :: BYTES a => (Markup.T, a) -> T
mark_str (m, s) = mark m (str s)

marks_str :: BYTES a => ([Markup.T], a) -> T
marks_str (ms, s) = fold_rev mark ms (str s)

item :: [T] -> T
item = markup Markup.item

text_fold :: [T] -> T
text_fold = markup Markup.text_fold

keyword1, keyword2 :: BYTES a => a -> T
keyword1 name = mark_str (Markup.keyword1, name)
keyword2 name = mark_str (Markup.keyword2, name)

text :: BYTES a => a -> [T]
text = breaks . map str . filter (not . Bytes.null) . space_explode ' ' . make_bytes

paragraph :: [T] -> T
paragraph = markup Markup.paragraph

para :: BYTES a => a -> T
para = paragraph . text

quote :: T -> T
quote prt = blk (1, [Str "\"", prt, Str "\""])

cartouche :: T -> T
cartouche prt = blk (1, [Str "\92<open>", prt, Str "\92<close>"])

separate :: BYTES a => a -> [T] -> [T]
separate sep = List.intercalate [str sep, brk 1] . map single

commas :: [T] -> [T]
commas = separate ("," :: Bytes)

enclose :: BYTES a => a -> a -> [T] -> T
enclose lpar rpar prts = block (str lpar : prts <> [str rpar])

enum :: BYTES a => a -> a -> a -> [T] -> T
enum sep lpar rpar = enclose lpar rpar . separate sep

list :: BYTES a => a -> a -> [T] -> T
list = enum ","

str_list :: BYTES a => a -> a -> [a] -> T
str_list lpar rpar = list lpar rpar . map str

big_list :: BYTES a => a -> [T] -> T
big_list name prts = block (fbreaks (str name : prts))
\<close>

generate_file "Isabelle/Name.hs" = \<open>
{-  Title:      Isabelle/Name.hs
    Author:     Makarius

Names of basic logical entities (variables etc.).

See \<^file>\<open>$ISABELLE_HOME/src/Pure/name.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Name (
  Name,
  uu, uu_, aT,
  clean_index, clean, internal, skolem, is_internal, is_skolem,
  Context, declare, is_declared, context, make_context, variant
)
where

import Data.Word (Word8)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Symbol as Symbol
import Isabelle.Library


type Name = Bytes


{- common defaults -}

uu, uu_, aT :: Name
uu = "uu"
uu_ = "uu_"
aT = "'a"


{- internal names -- NB: internal subsumes skolem -}

underscore :: Word8
underscore = Bytes.byte '_'

internal, skolem :: Name -> Name
internal x = x <> "_"
skolem x = x <> "__"

is_internal, is_skolem :: Name -> Bool
is_internal = Bytes.isSuffixOf "_"
is_skolem = Bytes.isSuffixOf "__"

clean_index :: Name -> (Name, Int)
clean_index x =
  if Bytes.null x || Bytes.last x /= underscore then (x, 0)
  else
    let
      rev = reverse (Bytes.unpack x)
      n = length (takeWhile (== underscore) rev)
      y = Bytes.pack (reverse (drop n rev))
    in (y, n)

clean :: Name -> Name
clean = fst . clean_index


{- context for used names -}

newtype Context = Context (Set Name)

declare :: Name -> Context -> Context
declare x (Context names) = Context (Set.insert x names)

is_declared :: Context -> Name -> Bool
is_declared (Context names) x = Set.member x names

context :: Context
context = Context (Set.fromList ["", "'"])

make_context :: [Name] -> Context
make_context used = fold declare used context


{- generating fresh names -}

bump_init :: Name -> Name
bump_init str = str <> "a"

bump_string :: Name -> Name
bump_string str =
  let
    a = Bytes.byte 'a'
    z = Bytes.byte 'z'
    bump (b : bs) | b == z = a : bump bs
    bump (b : bs) | a <= b && b < z = b + 1 : bs
    bump bs = a : bs

    rev = reverse (Bytes.unpack str)
    part2 = reverse (takeWhile (Symbol.is_ascii_quasi . Bytes.char) rev)
    part1 = reverse (bump (drop (length part2) rev))
  in Bytes.pack (part1 <> part2)

variant :: Name -> Context -> (Name, Context)
variant name names =
  let
    vary bump x = if is_declared names x then bump x |> vary bump_string else x
    (x, n) = clean_index name
    x' = x |> vary bump_init
    names' = declare x' names;
  in (x' <> Bytes.pack (replicate n underscore), names')
\<close>

generate_file "Isabelle/Term.hs" = \<open>
{-  Title:      Isabelle/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Lambda terms, types, sorts.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/term.scala\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Term (
  Indexname, Sort, Typ(..), Term(..),
  Free, lambda, declare_frees, incr_boundvars, subst_bound, dest_abs, strip_abs,
  type_op0, type_op1, op0, op1, op2, typed_op1, typed_op2, binder,
  dummyS, dummyT, is_dummyT, propT, is_propT, (-->), dest_funT, (--->),
  aconv, list_comb, strip_comb, head_of
)
where

import Isabelle.Library
import qualified Isabelle.Name as Name
import Isabelle.Name (Name)

infixr 5 -->
infixr --->


{- types and terms -}

type Indexname = (Name, Int)

type Sort = [Name]

data Typ =
    Type (Name, [Typ])
  | TFree (Name, Sort)
  | TVar (Indexname, Sort)
  deriving (Show, Eq, Ord)

data Term =
    Const (Name, [Typ])
  | Free (Name, Typ)
  | Var (Indexname, Typ)
  | Bound Int
  | Abs (Name, Typ, Term)
  | App (Term, Term)
  deriving (Show, Eq, Ord)


{- free and bound variables -}

type Free = (Name, Typ)

lambda :: Free -> Term -> Term
lambda (name, typ) body = Abs (name, typ, abstract 0 body)
  where
    abstract lev (Free (x, ty)) | name == x && typ == ty = Bound lev
    abstract lev (Abs (a, ty, t)) = Abs (a, ty, abstract (lev + 1) t)
    abstract lev (App (t, u)) = App (abstract lev t, abstract lev u)
    abstract _ t = t

declare_frees :: Term -> Name.Context -> Name.Context
declare_frees (Free (x, _)) = Name.declare x
declare_frees (Abs (_, _, b)) = declare_frees b
declare_frees (App (t, u)) = declare_frees t #> declare_frees u
declare_frees _ = id

incr_boundvars :: Int -> Term -> Term
incr_boundvars inc = if inc == 0 then id else incr 0
  where
    incr lev (Bound i) = if i >= lev then Bound (i + inc) else Bound i
    incr lev (Abs (a, ty, b)) = Abs (a, ty, incr (lev + 1) b)
    incr lev (App (t, u)) = App (incr lev t, incr lev u)
    incr _ t = t

subst_bound :: Term -> Term -> Term
subst_bound arg = subst 0
  where
    subst lev (Bound i) =
      if i < lev then Bound i
      else if i == lev then incr_boundvars lev arg
      else Bound (i - 1)
    subst lev (Abs (a, ty, b)) = Abs (a, ty, subst (lev + 1) b)
    subst lev (App (t, u)) = App (subst lev t, subst lev u)
    subst _ t = t

dest_abs :: Name.Context -> Term -> Maybe (Free, Term)
dest_abs names (Abs (x, ty, b)) =
  let
    (x', _) = Name.variant x (declare_frees b names)
    v = (x', ty)
  in Just (v, subst_bound (Free v) b)
dest_abs _ _ = Nothing

strip_abs :: Name.Context -> Term -> ([Free], Term)
strip_abs names tm =
  case dest_abs names tm of
    Just (v, t) ->
      let (vs, t') = strip_abs names t'
      in (v : vs, t')
    Nothing -> ([], tm)


{- type and term operators -}

type_op0 :: Name -> (Typ, Typ -> Bool)
type_op0 name = (mk, is)
  where
    mk = Type (name, [])
    is (Type (name, _)) = True
    is _ = False

type_op1 :: Name -> (Typ -> Typ, Typ -> Maybe Typ)
type_op1 name = (mk, dest)
  where
    mk ty = Type (name, [ty])
    dest (Type (name, [ty])) = Just ty
    dest _ = Nothing

type_op2 :: Name -> (Typ -> Typ -> Typ, Typ -> Maybe (Typ, Typ))
type_op2 name = (mk, dest)
  where
    mk ty1 ty2 = Type (name, [ty1, ty2])
    dest (Type (name, [ty1, ty2])) = Just (ty1, ty2)
    dest _ = Nothing

op0 :: Name -> (Term, Term -> Bool)
op0 name = (mk, is)
  where
    mk = Const (name, [])
    is (Const (c, _)) = c == name
    is _ = False

op1 :: Name -> (Term -> Term, Term -> Maybe Term)
op1 name = (mk, dest)
  where
    mk t = App (Const (name, []), t)
    dest (App (Const (c, _), t)) | c == name = Just t
    dest _ = Nothing

op2 :: Name -> (Term -> Term -> Term, Term -> Maybe (Term, Term))
op2 name = (mk, dest)
  where
    mk t u = App (App (Const (name, []), t), u)
    dest (App (App (Const (c, _), t), u)) | c == name = Just (t, u)
    dest _ = Nothing

typed_op1 :: Name -> (Typ -> Term -> Term, Term -> Maybe (Typ, Term))
typed_op1 name = (mk, dest)
  where
    mk ty t = App (Const (name, [ty]), t)
    dest (App (Const (c, [ty]), t)) | c == name = Just (ty, t)
    dest _ = Nothing

typed_op2 :: Name -> (Typ -> Term -> Term -> Term, Term -> Maybe (Typ, Term, Term))
typed_op2 name = (mk, dest)
  where
    mk ty t u = App (App (Const (name, [ty]), t), u)
    dest (App (App (Const (c, [ty]), t), u)) | c == name = Just (ty, t, u)
    dest _ = Nothing

binder :: Name -> (Free -> Term -> Term, Name.Context -> Term -> Maybe (Free, Term))
binder name = (mk, dest)
  where
    mk (a, ty) b = App (Const (name, [ty]), lambda (a, ty) b)
    dest names (App (Const (c, _), t)) | c == name = dest_abs names t
    dest _ _ = Nothing


{- type operations -}

dummyS :: Sort
dummyS = [""]

dummyT :: Typ; is_dummyT :: Typ -> Bool
(dummyT, is_dummyT) = type_op0 \<open>\<^type_name>\<open>dummy\<close>\<close>

propT :: Typ; is_propT :: Typ -> Bool
(propT, is_propT) = type_op0 \<open>\<^type_name>\<open>prop\<close>\<close>

(-->) :: Typ -> Typ -> Typ; dest_funT :: Typ -> Maybe (Typ, Typ)
((-->), dest_funT) = type_op2 \<open>\<^type_name>\<open>fun\<close>\<close>

(--->) :: [Typ] -> Typ -> Typ
[] ---> b = b
(a : as) ---> b = a --> (as ---> b)


{- term operations -}

aconv :: Term -> Term -> Bool
aconv (App (t1, u1)) (App (t2, u2)) = aconv t1 t2 && aconv u1 u2
aconv (Abs (_, ty1, t1)) (Abs (_, ty2, t2)) = aconv t1 t2 && ty1 == ty2
aconv a1 a2 = a1 == a2

list_comb :: Term -> [Term] -> Term
list_comb f [] = f
list_comb f (t : ts) = list_comb (App (f, t)) ts

strip_comb :: Term -> (Term, [Term])
strip_comb tm = strip (tm, [])
  where
    strip (App (f, t), ts) = strip (f, t : ts)
    strip x = x

head_of :: Term -> Term
head_of (App (f, _)) = head_of f
head_of u = u
\<close>

generate_file "Isabelle/Pure.hs" = \<open>
{-  Title:      Isabelle/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Support for Isabelle/Pure logic.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/logic.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Pure (
  mk_forall_op, dest_forall_op, mk_forall, dest_forall,
  mk_equals, dest_equals, mk_implies, dest_implies
)
where

import qualified Isabelle.Name as Name
import Isabelle.Term

mk_forall_op :: Typ -> Term -> Term; dest_forall_op :: Term -> Maybe (Typ, Term)
(mk_forall_op, dest_forall_op) = typed_op1 \<open>\<^const_name>\<open>Pure.all\<close>\<close>

mk_forall :: Free -> Term -> Term; dest_forall :: Name.Context -> Term -> Maybe (Free, Term)
(mk_forall, dest_forall) = binder \<open>\<^const_name>\<open>Pure.all\<close>\<close>

mk_equals :: Typ -> Term -> Term -> Term; dest_equals :: Term -> Maybe (Typ, Term, Term)
(mk_equals, dest_equals) = typed_op2 \<open>\<^const_name>\<open>Pure.eq\<close>\<close>

mk_implies :: Term -> Term -> Term; dest_implies :: Term -> Maybe (Term, Term)
(mk_implies, dest_implies) = op2 \<open>\<^const_name>\<open>Pure.imp\<close>\<close>
\<close>

generate_file "Isabelle/HOL.hs" = \<open>
{-  Title:      Isabelle/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Support for Isabelle/HOL logic.

See \<^file>\<open>$ISABELLE_HOME/src/HOL/Tools/hologic.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.HOL (
  boolT, is_boolT, mk_trueprop, dest_trueprop,
  mk_setT, dest_setT, mk_mem, dest_mem,
  mk_eq, dest_eq, true, is_true, false, is_false,
  mk_not, dest_not, mk_conj, dest_conj, mk_disj, dest_disj,
  mk_imp, dest_imp, mk_iff, dest_iff,
  mk_all_op, dest_all_op, mk_ex_op, dest_ex_op,
  mk_all, dest_all, mk_ex, dest_ex
)
where

import qualified Isabelle.Name as Name
import Isabelle.Term


boolT :: Typ; is_boolT :: Typ -> Bool
(boolT, is_boolT) = type_op0 \<open>\<^type_name>\<open>bool\<close>\<close>

mk_trueprop :: Term -> Term; dest_trueprop :: Term -> Maybe Term
(mk_trueprop, dest_trueprop) = op1 \<open>\<^const_name>\<open>Trueprop\<close>\<close>

mk_setT :: Typ -> Typ; dest_setT :: Typ -> Maybe Typ
(mk_setT, dest_setT) = type_op1 \<open>\<^type_name>\<open>set\<close>\<close>

mk_mem :: Typ -> Term -> Term -> Term; dest_mem :: Term -> Maybe (Typ, Term, Term)
(mk_mem, dest_mem) = typed_op2 \<open>\<^const_name>\<open>Set.member\<close>\<close>

mk_eq :: Typ -> Term -> Term -> Term; dest_eq :: Term -> Maybe (Typ, Term, Term)
(mk_eq, dest_eq) = typed_op2 \<open>\<^const_name>\<open>HOL.eq\<close>\<close>

true :: Term; is_true :: Term -> Bool
(true, is_true) = op0 \<open>\<^const_name>\<open>True\<close>\<close>

false :: Term; is_false :: Term -> Bool
(false, is_false) = op0 \<open>\<^const_name>\<open>False\<close>\<close>

mk_not :: Term -> Term; dest_not :: Term -> Maybe Term
(mk_not, dest_not) = op1 \<open>\<^const_name>\<open>Not\<close>\<close>

mk_conj :: Term -> Term -> Term; dest_conj :: Term -> Maybe (Term, Term)
(mk_conj, dest_conj) = op2 \<open>\<^const_name>\<open>conj\<close>\<close>

mk_disj :: Term -> Term -> Term; dest_disj :: Term -> Maybe (Term, Term)
(mk_disj, dest_disj) = op2 \<open>\<^const_name>\<open>disj\<close>\<close>

mk_imp :: Term -> Term -> Term; dest_imp :: Term -> Maybe (Term, Term)
(mk_imp, dest_imp) = op2 \<open>\<^const_name>\<open>implies\<close>\<close>

mk_iff :: Term -> Term -> Term
mk_iff = mk_eq boolT

dest_iff :: Term -> Maybe (Term, Term)
dest_iff tm =
  case dest_eq tm of
    Just (ty, t, u) | ty == boolT -> Just (t, u)
    _ -> Nothing

mk_all_op :: Typ -> Term -> Term; dest_all_op :: Term -> Maybe (Typ, Term)
(mk_all_op, dest_all_op) = typed_op1 \<open>\<^const_name>\<open>All\<close>\<close>

mk_ex_op :: Typ -> Term -> Term; dest_ex_op :: Term -> Maybe (Typ, Term)
(mk_ex_op, dest_ex_op) = typed_op1 \<open>\<^const_name>\<open>Ex\<close>\<close>

mk_all :: Free -> Term -> Term; dest_all :: Name.Context -> Term -> Maybe (Free, Term)
(mk_all, dest_all) = binder \<open>\<^const_name>\<open>All\<close>\<close>

mk_ex :: Free -> Term -> Term; dest_ex :: Name.Context -> Term -> Maybe (Free, Term)
(mk_ex, dest_ex) = binder \<open>\<^const_name>\<open>Ex\<close>\<close>
\<close>

generate_file "Isabelle/Term_XML/Encode.hs" = \<open>
{-  Title:      Isabelle/Term_XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML data representation of lambda terms.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
-}

{-# LANGUAGE LambdaCase #-}

module Isabelle.Term_XML.Encode (indexname, sort, typ, typ_body, term)
where

import Isabelle.Library
import Isabelle.XML.Encode
import Isabelle.Term

indexname :: P Indexname
indexname (a, b) = if b == 0 then [a] else [a, int_atom b]

sort :: T Sort
sort = list string

typ :: T Typ
typ ty =
  ty |> variant
   [\case { Type (a, b) -> Just ([a], list typ b); _ -> Nothing },
    \case { TFree (a, b) -> Just ([a], sort b); _ -> Nothing },
    \case { TVar (a, b) -> Just (indexname a, sort b); _ -> Nothing }]

typ_body :: T Typ
typ_body ty = if is_dummyT ty then [] else typ ty

term :: T Term
term t =
  t |> variant
   [\case { Const (a, b) -> Just ([a], list typ b); _ -> Nothing },
    \case { Free (a, b) -> Just ([a], typ_body b); _ -> Nothing },
    \case { Var (a, b) -> Just (indexname a, typ_body b); _ -> Nothing },
    \case { Bound a -> Just ([], int a); _ -> Nothing },
    \case { Abs (a, b, c) -> Just ([a], pair typ term (b, c)); _ -> Nothing },
    \case { App a -> Just ([], pair term term a); _ -> Nothing }]
\<close>

generate_file "Isabelle/Term_XML/Decode.hs" = \<open>
{-  Title:      Isabelle/Term_XML/Decode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML data representation of lambda terms.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Isabelle.Term_XML.Decode (indexname, sort, typ, typ_body, term)
where

import Isabelle.Library
import Isabelle.XML.Decode
import Isabelle.Term


indexname :: P Indexname
indexname [a] = (a, 0)
indexname [a, b] = (a, int_atom b)

sort :: T Sort
sort = list string

typ :: T Typ
typ ty =
  ty |> variant
  [\([a], b) -> Type (a, list typ b),
   \([a], b) -> TFree (a, sort b),
   \(a, b) -> TVar (indexname a, sort b)]

typ_body :: T Typ
typ_body [] = dummyT
typ_body body = typ body

term :: T Term
term t =
  t |> variant
   [\([a], b) -> Const (a, list typ b),
    \([a], b) -> Free (a, typ_body b),
    \(a, b) -> Var (indexname a, typ_body b),
    \([], a) -> Bound (int a),
    \([a], b) -> let (c, d) = pair typ term b in Abs (a, c, d),
    \([], a) -> App (pair term term a)]
\<close>

generate_file "Isabelle/XML/Classes.hs" = \<open>
{- generated by Isabelle -}

{-  Title:      Isabelle/XML/Classes.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Type classes for XML data representation.
-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Isabelle.XML.Classes
  (Encode_Atom(..), Decode_Atom(..), Encode (..), Decode (..))
where

import qualified Isabelle.XML as XML
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.XML.Decode as Decode
import qualified Isabelle.Term_XML.Encode as Encode
import qualified Isabelle.Term_XML.Decode as Decode
import qualified Isabelle.Properties as Properties
import Isabelle.Bytes (Bytes)
import Isabelle.Term (Typ, Term)


class Encode_Atom a where encode_atom :: Encode.A a
class Decode_Atom a where decode_atom :: Decode.A a

instance Encode_Atom Int where encode_atom = Encode.int_atom
instance Decode_Atom Int where decode_atom = Decode.int_atom

instance Encode_Atom Bool where encode_atom = Encode.bool_atom
instance Decode_Atom Bool where decode_atom = Decode.bool_atom

instance Encode_Atom () where encode_atom = Encode.unit_atom
instance Decode_Atom () where decode_atom = Decode.unit_atom


class Encode a where encode :: Encode.T a
class Decode a where decode :: Decode.T a

instance Encode Bytes where encode = Encode.string
instance Decode Bytes where decode = Decode.string

instance Encode Int where encode = Encode.int
instance Decode Int where decode = Decode.int

instance Encode Bool where encode = Encode.bool
instance Decode Bool where decode = Decode.bool

instance Encode () where encode = Encode.unit
instance Decode () where decode = Decode.unit

instance (Encode a, Encode b) => Encode (a, b)
  where encode = Encode.pair encode encode
instance (Decode a, Decode b) => Decode (a, b)
  where decode = Decode.pair decode decode

instance (Encode a, Encode b, Encode c) => Encode (a, b, c)
  where encode = Encode.triple encode encode encode
instance (Decode a, Decode b, Decode c) => Decode (a, b, c)
  where decode = Decode.triple decode decode decode

instance Encode a => Encode [a] where encode = Encode.list encode
instance Decode a => Decode [a] where decode = Decode.list decode

instance Encode a => Encode (Maybe a) where encode = Encode.option encode
instance Decode a => Decode (Maybe a) where decode = Decode.option decode

instance Encode XML.Tree where encode = Encode.tree
instance Decode XML.Tree where decode = Decode.tree

instance Encode Properties.T where encode = Encode.properties
instance Decode Properties.T where decode = Decode.properties

instance Encode Typ where encode = Encode.typ
instance Decode Typ where decode = Decode.typ

instance Encode Term where encode = Encode.term
instance Decode Term where decode = Decode.term
\<close>

generate_file "Isabelle/UUID.hs" = \<open>
{-  Title:      Isabelle/UUID.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Universally unique identifiers.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/uuid.scala\<close>.
-}

module Isabelle.UUID (T, random, print, parse)
where

import Prelude hiding (print)

import Data.UUID (UUID)
import qualified Data.UUID as UUID
import Data.UUID.V4 (nextRandom)

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


type T = UUID

random :: IO T
random = nextRandom

print :: T -> Bytes
print = Bytes.make . UUID.toASCIIBytes

parse :: Bytes -> Maybe T
parse = UUID.fromASCIIBytes . Bytes.unmake
\<close>

generate_file "Isabelle/Byte_Message.hs" = \<open>
{-  Title:      Isabelle/Byte_Message.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Byte-oriented messages.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/byte_message.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/byte_message.scala\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Isabelle.Byte_Message (
    write, write_line,
    read, read_block, read_line,
    make_message, write_message, read_message,
    exchange_message, exchange_message0,
    make_line_message, write_line_message, read_line_message,
    read_yxml, write_yxml
  )
where

import Prelude hiding (read)
import Data.Maybe
import qualified Data.ByteString as ByteString
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Symbol as Symbol
import qualified Isabelle.UTF8 as UTF8
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML

import Network.Socket (Socket)
import qualified Network.Socket.ByteString as Socket

import Isabelle.Library
import qualified Isabelle.Value as Value


{- output operations -}

write :: Socket -> [Bytes] -> IO ()
write socket = Socket.sendMany socket . map Bytes.unmake

write_line :: Socket -> Bytes -> IO ()
write_line socket s = write socket [s, "\n"]


{- input operations -}

read :: Socket -> Int -> IO Bytes
read socket n = read_body 0 []
  where
    result = Bytes.concat . reverse
    read_body len ss =
      if len >= n then return (result ss)
      else
        (do
          s <- Socket.recv socket (min (n - len) 8192)
          case ByteString.length s of
            0 -> return (result ss)
            m -> read_body (len + m) (Bytes.make s : ss))

read_block :: Socket -> Int -> IO (Maybe Bytes, Int)
read_block socket n = do
  msg <- read socket n
  let len = Bytes.length msg
  return (if len == n then Just msg else Nothing, len)

read_line :: Socket -> IO (Maybe Bytes)
read_line socket = read_body []
  where
    result = trim_line . Bytes.pack . reverse
    read_body bs = do
      s <- Socket.recv socket 1
      case ByteString.length s of
        0 -> return (if null bs then Nothing else Just (result bs))
        1 ->
          case ByteString.head s of
            10 -> return (Just (result bs))
            b -> read_body (b : bs)


{- messages with multiple chunks (arbitrary content) -}

make_header :: [Int] -> [Bytes]
make_header ns = [space_implode "," (map Value.print_int ns), "\n"]

make_message :: [Bytes] -> [Bytes]
make_message chunks = make_header (map Bytes.length chunks) <> chunks

write_message :: Socket -> [Bytes] -> IO ()
write_message socket = write socket . make_message

parse_header :: Bytes -> [Int]
parse_header line =
  let
    res = map Value.parse_nat (space_explode ',' line)
  in
    if all isJust res then map fromJust res
    else error ("Malformed message header: " <> quote (UTF8.decode line))

read_chunk :: Socket -> Int -> IO Bytes
read_chunk socket n = do
  res <- read_block socket n
  return $
    case res of
      (Just chunk, _) -> chunk
      (Nothing, len) ->
        error ("Malformed message chunk: unexpected EOF after " <>
          show len <> " of " <> show n <> " bytes")

read_message :: Socket -> IO (Maybe [Bytes])
read_message socket = do
  res <- read_line socket
  case res of
    Just line -> Just <$> mapM (read_chunk socket) (parse_header line)
    Nothing -> return Nothing

exchange_message :: Socket -> [Bytes] -> IO (Maybe [Bytes])
exchange_message socket msg = do
  write_message socket msg
  read_message socket

exchange_message0 :: Socket -> [Bytes] -> IO ()
exchange_message0 socket msg = do
  _ <- exchange_message socket msg
  return ()


-- hybrid messages: line or length+block (with content restriction)

is_length :: Bytes -> Bool
is_length msg =
  not (Bytes.null msg) && Bytes.all_char (\c -> '0' <= c && c <= '9') msg

is_terminated :: Bytes -> Bool
is_terminated msg =
  not (Bytes.null msg) && Symbol.is_ascii_line_terminator (Bytes.char $ Bytes.last msg)

make_line_message :: Bytes -> [Bytes]
make_line_message msg =
  let n = Bytes.length msg in
    if is_length msg || is_terminated msg then
      error ("Bad content for line message:\n" <> take 100 (UTF8.decode msg))
    else
      (if n > 100 || Bytes.any_char (== '\n') msg then make_header [n + 1] else []) <> [msg, "\n"]

write_line_message :: Socket -> Bytes -> IO ()
write_line_message socket = write socket . make_line_message

read_line_message :: Socket -> IO (Maybe Bytes)
read_line_message socket = do
  opt_line <- read_line socket
  case opt_line of
    Nothing -> return Nothing
    Just line ->
      case Value.parse_nat line of
        Nothing -> return $ Just line
        Just n -> fmap trim_line . fst <$> read_block socket n


read_yxml :: Socket -> IO (Maybe XML.Body)
read_yxml socket = do
  res <- read_line_message socket
  return (YXML.parse_body <$> res)

write_yxml :: Socket -> XML.Body -> IO ()
write_yxml socket body =
  write_line_message socket (YXML.string_of_body body)
\<close>

generate_file "Isabelle/Isabelle_Thread.hs" = \<open>
{-  Title:      Isabelle/Isabelle_Thread.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Isabelle-specific thread management.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/Concurrent/isabelle_thread.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/Concurrent/isabelle_thread.scala\<close>.
-}

{-# LANGUAGE NamedFieldPuns #-}

module Isabelle.Isabelle_Thread (
  ThreadId, Result,
  find_id,
  properties, change_properties,
  add_resource, del_resource, bracket_resource,
  is_stopped, expose_stopped, stop,
  my_uuid, stop_uuid,
  Fork, fork_finally, fork)
where

import Data.Unique
import Data.IORef
import System.IO.Unsafe

import qualified Data.List as List
import Control.Monad (when, forM_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Exception as Exception
import Control.Concurrent (ThreadId)
import qualified Control.Concurrent as Concurrent
import Control.Concurrent.Thread (Result)
import qualified Control.Concurrent.Thread as Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Properties as Properties


{- thread info -}

type Resources = Map Unique (IO ())
data Info = Info {uuid :: UUID.T, props :: Properties.T, stopped :: Bool, resources :: Resources}
type Infos = Map ThreadId Info

lookup_info :: Infos -> ThreadId -> Maybe Info
lookup_info infos id = Map.lookup id infos

init_info :: ThreadId -> UUID.T -> Infos -> (Infos, ())
init_info id uuid infos = (Map.insert id (Info uuid [] False Map.empty) infos, ())


{- global state -}

{-# NOINLINE global_state #-}
global_state :: IORef Infos
global_state = unsafePerformIO (newIORef Map.empty)

find_id :: UUID.T -> IO (Maybe ThreadId)
find_id uuid = do
  state <- readIORef global_state
  return $ fst <$> List.find (\(_, Info{uuid = uuid'}) -> uuid == uuid') (Map.assocs state)

get_info :: ThreadId -> IO (Maybe Info)
get_info id = do
  state <- readIORef global_state
  return $ lookup_info state id

map_info :: ThreadId -> (Info -> Info) -> IO (Maybe Info)
map_info id f =
  atomicModifyIORef' global_state
    (\infos ->
      case lookup_info infos id of
        Nothing -> (infos, Nothing)
        Just info ->
          let info' = f info
          in (Map.insert id info' infos, Just info'))

delete_info :: ThreadId -> IO ()
delete_info id =
  atomicModifyIORef' global_state (\infos -> (Map.delete id infos, ()))


{- thread properties -}

my_info :: IO (Maybe Info)
my_info = do
  id <- Concurrent.myThreadId
  get_info id

properties :: IO Properties.T
properties = maybe [] props <$> my_info

change_properties :: (Properties.T -> Properties.T) -> IO ()
change_properties f = do
  id <- Concurrent.myThreadId
  map_info id (\info -> info {props = f (props info)})
  return ()


{- managed resources -}

add_resource :: IO () -> IO Unique
add_resource resource = do
  id <- Concurrent.myThreadId
  u <- newUnique
  map_info id (\info -> info {resources = Map.insert u resource (resources info)})
  return u

del_resource :: Unique -> IO ()
del_resource u = do
  id <- Concurrent.myThreadId
  map_info id (\info -> info {resources = Map.delete u (resources info)})
  return ()

bracket_resource :: IO () -> IO a -> IO a
bracket_resource resource body =
  Exception.bracket (add_resource resource) del_resource (const body)


{- stop -}

is_stopped :: IO Bool
is_stopped = maybe False stopped <$> my_info

expose_stopped :: IO ()
expose_stopped = do
  stopped <- is_stopped
  when stopped $ throw ThreadKilled

stop :: ThreadId -> IO ()
stop id = do
  info <- map_info id (\info -> info {stopped = True})
  let ops = case info of Nothing -> []; Just Info{resources} -> map snd (Map.toDescList resources)
  sequence_ ops


{- UUID -}

my_uuid :: IO (Maybe UUID.T)
my_uuid = fmap uuid <$> my_info

stop_uuid :: UUID.T -> IO ()
stop_uuid uuid = do
  id <- find_id uuid
  forM_ id stop


{- fork -}

type Fork a = (ThreadId, UUID.T, IO (Result a))

fork_finally :: IO a -> (Either SomeException a -> IO b) -> IO (Fork b)
fork_finally body finally = do
  uuid <- UUID.random
  (id, result) <-
    Exception.mask (\restore ->
      Thread.forkIO
        (Exception.try
          (do
            id <- Concurrent.myThreadId
            atomicModifyIORef' global_state (init_info id uuid)
            restore body)
         >>= (\res -> do id <- Concurrent.myThreadId; delete_info id; finally res)))
  return (id, uuid, result)

fork :: IO a -> IO (Fork a)
fork body = fork_finally body Thread.result
\<close>

generate_file "Isabelle/Server.hs" = \<open>
{-  Title:      Isabelle/Server.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

TCP server on localhost.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Server (
  localhost_name, localhost, publish_text, publish_stdout,
  server, connection
)
where

import Control.Monad (forever, when)
import qualified Control.Exception as Exception
import Network.Socket (Socket)
import qualified Network.Socket as Socket
import qualified System.IO as IO
import qualified Data.ByteString.Char8 as Char8

import Isabelle.Library
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread


{- server address -}

localhost_name :: Bytes
localhost_name = "127.0.0.1"

localhost :: Socket.HostAddress
localhost = Socket.tupleToHostAddress (127, 0, 0, 1)

publish_text :: Bytes -> Bytes -> UUID.T -> Bytes
publish_text name address password =
  "server " <> quote name <> " = " <> address <>
    " (password " <> quote (show_bytes password) <> ")"

publish_stdout :: Bytes -> Bytes -> UUID.T -> IO ()
publish_stdout name address password =
  Char8.putStrLn (Bytes.unmake $ publish_text name address password)


{- server -}

server :: (Bytes -> UUID.T -> IO ()) -> (Socket -> IO ()) -> IO ()
server publish handle =
  Socket.withSocketsDo $ Exception.bracket open (Socket.close . fst) (uncurry loop)
  where
    open :: IO (Socket, Bytes)
    open = do
      server_socket <- Socket.socket Socket.AF_INET Socket.Stream Socket.defaultProtocol
      Socket.bind server_socket (Socket.SockAddrInet 0 localhost)
      Socket.listen server_socket 50

      port <- Socket.socketPort server_socket
      let address = localhost_name <> ":" <> show_bytes port
      password <- UUID.random
      publish address password

      return (server_socket, UUID.print password)

    loop :: Socket -> Bytes -> IO ()
    loop server_socket password = forever $ do
      (connection, _) <- Socket.accept server_socket
      Isabelle_Thread.fork_finally
        (do
          line <- Byte_Message.read_line connection
          when (line == Just password) $ handle connection)
        (\finally -> do
          Socket.close connection
          case finally of
            Left exn -> IO.hPutStrLn IO.stderr $ Exception.displayException exn
            Right () -> return ())
      return ()


{- client connection -}

connection :: String -> Bytes -> (Socket -> IO a) -> IO a
connection port password client =
  Socket.withSocketsDo $ do
    addr <- resolve
    Exception.bracket (open addr) Socket.close body
  where
    resolve = do
      let hints =
            Socket.defaultHints {
              Socket.addrFlags = [Socket.AI_NUMERICHOST, Socket.AI_NUMERICSERV],
              Socket.addrSocketType = Socket.Stream }
      head <$> Socket.getAddrInfo (Just hints) (Just "127.0.0.1") (Just port)

    open addr = do
      socket <- Socket.socket (Socket.addrFamily addr) (Socket.addrSocketType addr)
                  (Socket.addrProtocol addr)
      Socket.connect socket $ Socket.addrAddress addr
      return socket

    body socket = do
      Byte_Message.write_line socket password
      client socket
\<close>

generate_file "Isabelle/Time.hs" = \<open>
{-  Title:      Isabelle/Time.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Time based on milliseconds.

See \<^file>\<open>~~/src/Pure/General/time.scala\<close>
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Time (
  Time, seconds, minutes, ms, zero, is_zero, is_relevant,
  get_seconds, get_minutes, get_ms, message
)
where

import Text.Printf (printf)
import Isabelle.Bytes (Bytes)
import Isabelle.Library


data Time = Time Int

instance Eq Time where Time ms1 == Time ms2 = ms1 == ms2
instance Ord Time where compare (Time ms1) (Time ms2) = compare ms1 ms2

seconds :: Double -> Time
seconds s = Time (round (s * 1000.0))

minutes :: Double -> Time
minutes m = Time (round (m * 60000.0))

ms :: Int -> Time
ms = Time

zero :: Time
zero = ms 0

is_zero :: Time -> Bool
is_zero (Time ms) = ms == 0

is_relevant :: Time -> Bool
is_relevant (Time ms) = ms >= 1

get_seconds :: Time -> Double
get_seconds (Time ms) = fromIntegral ms / 1000.0

get_minutes :: Time -> Double
get_minutes (Time ms) = fromIntegral ms / 60000.0

get_ms :: Time -> Int
get_ms (Time ms) = ms

instance Show Time where
  show t = printf "%.3f" (get_seconds t)

message :: Time -> Bytes
message t = make_bytes (show t) <> "s"
\<close>

generate_file "Isabelle/Timing.hs" = \<open>
{-  Title:      Isabelle/Timing.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Support for time measurement.

See \<^file>\<open>~~/src/Pure/General/timing.ML\<close>
and \<^file>\<open>~~/src/Pure/General/timing.scala\<close>
-}

module Isabelle.Timing (
  Timing (..), zero, is_zero, is_relevant
)
where

import qualified Isabelle.Time as Time
import Isabelle.Time (Time)

data Timing = Timing {elapsed :: Time, cpu :: Time, gc :: Time}
  deriving (Show, Eq)

zero :: Timing
zero = Timing Time.zero Time.zero Time.zero

is_zero :: Timing -> Bool
is_zero t = Time.is_zero (elapsed t) && Time.is_zero (cpu t) && Time.is_zero (gc t)

is_relevant :: Timing -> Bool
is_relevant t = Time.is_relevant (elapsed t) || Time.is_relevant (cpu t) || Time.is_relevant (gc t)
\<close>

generate_file "Isabelle/Bash.hs" = \<open>
{-  Title:      Isabelle/Bash.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Support for GNU bash.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/System/bash.ML\<close>
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Bash (
  string, strings,

  Params,
  get_script, get_input, get_cwd, get_putenv, get_redirect,
  get_timeout, get_description,
  script, input, cwd, putenv, redirect, timeout, description,
)
where

import Text.Printf (printf)
import qualified Isabelle.Symbol as Symbol
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Time as Time
import Isabelle.Time (Time)
import Isabelle.Library


{- concrete syntax -}

string :: Bytes -> Bytes
string str =
  if Bytes.null str then "\"\""
  else str |> Bytes.unpack |> map trans |> Bytes.concat
    where
      trans b =
        case Bytes.char b of
          '\t' -> "$'\\t'"
          '\n' -> "$'\\n'"
          '\f' -> "$'\\f'"
          '\r' -> "$'\\r'"
          c ->
            if Symbol.is_ascii_letter c || Symbol.is_ascii_digit c || c `elem` ("+,-./:_" :: String)
            then Bytes.singleton b
            else if b < 32 || b >= 127 then make_bytes (printf "$'\\x%02x'" b :: String)
            else "\\" <> Bytes.singleton b

strings :: [Bytes] -> Bytes
strings = space_implode " " . map string


{- server parameters -}

data Params = Params {
    _script :: Bytes,
    _input :: Bytes,
    _cwd :: Maybe Bytes,
    _putenv :: [(Bytes, Bytes)],
    _redirect :: Bool,
    _timeout :: Time,
    _description :: Bytes}
  deriving (Show, Eq)

get_script :: Params -> Bytes
get_script = _script

get_input :: Params -> Bytes
get_input = _input

get_cwd :: Params -> Maybe Bytes
get_cwd = _cwd

get_putenv :: Params -> [(Bytes, Bytes)]
get_putenv = _putenv

get_redirect :: Params -> Bool
get_redirect = _redirect

get_timeout :: Params -> Time
get_timeout = _timeout

get_description :: Params -> Bytes
get_description = _description

script :: Bytes -> Params
script script = Params script "" Nothing [] False Time.zero ""

input :: Bytes -> Params -> Params
input input params = params { _input = input }

cwd :: Bytes -> Params -> Params
cwd cwd params = params { _cwd = Just cwd }

putenv :: [(Bytes, Bytes)] -> Params -> Params
putenv putenv params = params { _putenv = putenv }

redirect :: Params -> Params
redirect params = params { _redirect = True }

timeout :: Time -> Params -> Params
timeout timeout params = params { _timeout = timeout }

description :: Bytes -> Params -> Params
description description params = params { _description = description }
\<close>

generate_file "Isabelle/Process_Result.hs" = \<open>
{-  Title:      Isabelle/Process_Result.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Result of system process.

See \<^file>\<open>~~/src/Pure/System/process_result.ML\<close>
and \<^file>\<open>~~/src/Pure/System/process_result.scala\<close>
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Process_Result (
  interrupt_rc, timeout_rc,

  T, make, rc, out_lines, err_lines, timing, timing_elapsed, out, err, ok, check
)
where

import Isabelle.Time (Time)
import qualified Isabelle.Timing as Timing
import Isabelle.Timing (Timing)
import Isabelle.Bytes (Bytes)
import Isabelle.Library


interrupt_rc :: Int
interrupt_rc = 130

timeout_rc :: Int
timeout_rc = 142

data T =
  Process_Result {
    _rc :: Int,
    _out_lines :: [Bytes],
    _err_lines :: [Bytes],
    _timing :: Timing}
  deriving (Show, Eq)

make :: Int -> [Bytes] -> [Bytes] -> Timing -> T
make = Process_Result

rc :: T -> Int
rc = _rc

out_lines :: T -> [Bytes]
out_lines = _out_lines

err_lines :: T -> [Bytes]
err_lines = _err_lines

timing :: T -> Timing
timing = _timing

timing_elapsed :: T -> Time
timing_elapsed = Timing.elapsed . timing

out :: T -> Bytes
out = trim_line . cat_lines . out_lines

err :: T -> Bytes
err = trim_line . cat_lines . err_lines

ok :: T -> Bool
ok result = rc result == 0

check :: T -> T
check result = if ok result then result else error (make_string $ err result)
\<close>

generate_file "Isabelle/Options.hs" = \<open>
{-  Title:      Isabelle/Options.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

System options with external string representation.

See \<^file>\<open>~~/src/Pure/System/options.ML\<close>
and \<^file>\<open>~~/src/Pure/System/options.scala\<close>
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}

module Isabelle.Options (
  boolT, intT, realT, stringT, unknownT,

  T, typ, bool, int, real, seconds, string,
  decode
)
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Isabelle.Properties as Properties
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Time as Time
import Isabelle.Time (Time)
import Isabelle.Library
import qualified Isabelle.XML.Decode as Decode
import Isabelle.XML.Classes (Decode (..))


{- representation -}

boolT :: Bytes
boolT = "bool"

intT :: Bytes
intT = "int"

realT :: Bytes
realT = "real"

stringT :: Bytes
stringT = "string"

unknownT :: Bytes
unknownT = "unknown"

data Opt = Opt {
  _pos :: Properties.T,
  _name :: Bytes,
  _typ :: Bytes,
  _value :: Bytes }

data T = Options (Map Bytes Opt)


{- check -}

check_name :: T -> Bytes -> Opt
check_name (Options map) name =
  case Map.lookup name map of
    Just opt | _typ opt /= unknownT -> opt
    _ -> error (make_string ("Unknown system option " <> quote name))

check_type :: T -> Bytes -> Bytes -> Opt
check_type options name typ =
  let
    opt = check_name options name
    t = _typ opt
  in
    if t == typ then opt
    else error (make_string ("Ill-typed system option " <> quote name <> " : " <> t <> " vs. " <> typ))


{- get typ -}

typ :: T -> Bytes -> Bytes
typ options name = _typ (check_name options name)


{- get value -}

get :: Bytes -> (Bytes -> Maybe a) -> T -> Bytes -> a
get typ parse options name =
  let opt = check_type options name typ in
    case parse (_value opt) of
      Just x -> x
      Nothing ->
        error (make_string ("Malformed value for system option " <> quote name <>
          " : " <> typ <> " =\n" <> quote (_value opt)))

bool :: T -> Bytes -> Bool
bool = get boolT Value.parse_bool

int :: T -> Bytes -> Int
int = get intT Value.parse_int

real :: T -> Bytes -> Double
real = get realT Value.parse_real

seconds :: T -> Bytes -> Time
seconds options = Time.seconds . real options

string :: T -> Bytes -> Bytes
string = get stringT Just


{- decode -}

instance Decode T where
  decode :: Decode.T T
  decode =
    let
      decode_entry :: Decode.T (Bytes, Opt)
      decode_entry body =
        let
          (pos, (name, (typ, value))) =
            Decode.pair Decode.properties (Decode.pair Decode.string (Decode.pair Decode.string Decode.string)) body
        in (name, Opt { _pos = pos, _name = name, _typ = typ, _value = value })
    in Options . Map.fromList . Decode.list decode_entry
\<close>

export_generated_files _

end

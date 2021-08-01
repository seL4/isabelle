(*  Title:      Tools/Haskell/Haskell.thy
    Author:     Makarius

Support for Isabelle tools in Haskell.
*)

theory Haskell
  imports Pure
begin

generate_file "Isabelle/Bytes.hs" = \<open>
{-  Title:      Isabelle/Bytes.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Compact byte strings.

See \<^file>\<open>$ISABELLE_HOME/src/Pure/General/bytes.ML\<close>
and \<^file>\<open>$ISABELLE_HOME/src/Pure/General/bytes.scala\<close>.
-}

module Isabelle.Bytes (
  Bytes,
  make, unmake, pack, unpack,
  empty, null, length, index, all, any,
  head, last, take, drop, isPrefixOf, isSuffixOf,
  concat, space, spaces, singleton, char, byte,
  trim_line, space_explode, split_lines
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

singletons :: Array Word8 Bytes
singletons =
  array (minBound, maxBound)
    [(i, make (ByteString.singleton i)) | i <- [minBound .. maxBound]]

singleton :: Word8 -> Bytes
singleton b = singletons ! b

char :: Word8 -> Char
char = toEnum . fromEnum

byte :: Char -> Word8
byte = toEnum . fromEnum

trim_line :: Bytes -> Bytes
trim_line s =
  if n >= 2 && at (n - 2) == '\r' && at (n - 1) == '\n' then take (n - 2) s
  else if n >= 1 && (at (n - 1) == '\r' || at (n - 1) == '\n') then take (n - 1) s
  else s
  where
    n = length s
    at = char . index s

space_explode :: Word8 -> Bytes -> [Bytes]
space_explode sep str =
  if null str then []
  else if all (/= sep) str then [str]
  else explode (unpack str)
  where
    explode rest =
      case span (/= sep) rest of
        (_, []) -> [pack rest]
        (prfx, _ : rest') -> pack prfx : explode rest'

split_lines :: Bytes -> [Bytes]
split_lines = space_explode (byte '\n')
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/basics.ML\<close>, \<^file>\<open>$ISABELLE_HOME/src/Pure/library.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Isabelle.Library (
  (|>), (|->), (#>), (#->),

  the, the_default,

  fold, fold_rev, single, map_index, get_index, separate,

  StringLike, STRING (..), TEXT (..), BYTES (..),

  proper_string, quote, space_implode, commas, commas_quote, cat_lines,
  space_explode, split_lines, trim_line)
where

import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.String (IsString)
import qualified Data.List.Split as Split
import qualified Isabelle.Symbol as Symbol
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


{- options -}

the :: Maybe a -> a
the (Just x) = x
the Nothing = error "the Nothing"

the_default :: a -> Maybe a -> a
the_default x Nothing = x
the_default _ (Just y) = y


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

class (IsString a, Monoid a, Eq a, Ord a) => StringLike a
instance StringLike String
instance StringLike Text
instance StringLike Lazy.Text
instance StringLike Bytes

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


{- strings -}

proper_string :: StringLike a => a -> Maybe a
proper_string s = if s == "" then Nothing else Just s

quote :: StringLike a => a -> a
quote s = "\"" <> s <> "\""

space_implode :: StringLike a => a -> [a] -> a
space_implode s = mconcat . separate s

commas, commas_quote :: StringLike a => [a] -> a
commas = space_implode ", "
commas_quote = commas . map quote

cat_lines :: StringLike a => [a] -> a
cat_lines = space_implode "\n"


space_explode :: Char -> String -> [String]
space_explode c = Split.split (Split.dropDelims (Split.whenElt (== c)))

split_lines :: String -> [String]
split_lines = space_explode '\n'

trim_line :: String -> String
trim_line line =
  if not (null line) && Symbol.is_ascii_line_terminator (last line) then
    case reverse line of
      '\n' : '\r' : rest -> reverse rest
      '\r' : rest -> reverse rest
      '\n' : rest -> reverse rest
      _ -> line
  else line
\<close>


generate_file "Isabelle/Symbol.hs" = \<open>
{-  Title:      Isabelle/Symbols.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Isabelle text symbols.
-}

module Isabelle.Symbol where

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
is_ascii_blank c = c `elem` " \t\n\11\f\r"

is_ascii_line_terminator :: Char -> Bool
is_ascii_line_terminator c = c == '\r' || c == '\n'

is_ascii_letdig :: Char -> Bool
is_ascii_letdig c = is_ascii_letter c || is_ascii_digit c || is_ascii_quasi c

is_ascii_identifier :: String -> Bool
is_ascii_identifier s =
  not (null s) && is_ascii_letter (head s) && all is_ascii_letdig s
\<close>

generate_file "Isabelle/Buffer.hs" = \<open>
{-  Title:      Isabelle/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient buffer of byte strings.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/buffer.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/value.ML\<close>.
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
print_int = make_bytes . show

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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/properties.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/markup.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.Markup (
  T, empty, is_empty, properties,

  nameN, name, xnameN, xname, kindN,

  bindingN, binding, entityN, entity, defN, refN,

  completionN, completion, no_completionN, no_completion,

  lineN, end_lineN, offsetN, end_offsetN, fileN, idN, positionN, position,

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

generate_file "Isabelle/XML.hs" = \<open>
{-  Title:      Isabelle/XML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Untyped XML trees and representation of ML values.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Isabelle.XML.Encode (
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
variant fs x = [tagged (the (get_index (\f -> f x) fs))]
\<close>

generate_file "Isabelle/XML/Decode.hs" = \<open>
{-  Title:      Isabelle/XML/Decode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/yxml.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/completion.ML\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Completion (
    Name, T, names, none, make, markup_element, markup_report, make_report
  ) where

import Isabelle.Library
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML


type Name = (Bytes, (Bytes, Bytes))  -- external name, kind, internal name
data T = Completion Properties.T Int [Name]  -- position, total length, names

names :: Int -> Properties.T -> [Name] -> T
names limit props names = Completion props (length names) (take limit names)

none :: T
none = names 0 [] []

clean_name :: Bytes -> Bytes
clean_name bs =
  if not (Bytes.null bs) && Bytes.last bs == u then
    Bytes.unpack bs |> reverse |> dropWhile (== u) |> reverse |> Bytes.pack
  else bs
  where u = Bytes.byte '_'

make :: Int -> (Bytes, Properties.T) -> ((Bytes -> Bool) -> [Name]) -> T
make limit (name, props) make_names =
  if name /= "" && name /= "_" then
    names limit props (make_names (Bytes.isPrefixOf (clean_name name)))
  else none

markup_element :: T -> (Markup.T, XML.Body)
markup_element (Completion props total names) =
  if not (null names) then
    let
      markup = Markup.properties props Markup.completion
      body =
        Encode.pair Encode.int
          (Encode.list (Encode.pair Encode.string (Encode.pair Encode.string Encode.string)))
          (total, names)
    in (markup, body)
  else (Markup.empty, [])

markup_report :: [T] -> Bytes
markup_report [] = Bytes.empty
markup_report elems =
  YXML.string_of $ XML.Elem (Markup.report, map (XML.Elem . markup_element) elems)

make_report :: Int -> (Bytes, Properties.T) -> ((Bytes -> Bool) -> [Name]) -> Bytes
make_report limit name_props make_names =
  markup_report [make limit name_props make_names]
\<close>

generate_file "Isabelle/File.hs" = \<open>
{-  Title:      Isabelle/File.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

File-system operations.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/file.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/pretty.ML\<close>.
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
import Isabelle.Library hiding (quote, separate, commas)
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
text = breaks . map str . filter (not . Bytes.null) . Bytes.space_explode Bytes.space . make_bytes

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

generate_file "Isabelle/Term.hs" = \<open>
{-  Title:      Isabelle/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Lambda terms, types, sorts.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term.scala\<close>.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Term (
  Indexname,

  Sort, dummyS,

  Typ(..), dummyT, is_dummyT, Term(..),
  aconv, list_comb, strip_comb, head_of, lambda)
where

import Isabelle.Bytes (Bytes)


type Indexname = (Bytes, Int)


type Sort = [Bytes]

dummyS :: Sort
dummyS = [""]


data Typ =
    Type (Bytes, [Typ])
  | TFree (Bytes, Sort)
  | TVar (Indexname, Sort)
  deriving (Show, Eq, Ord)

dummyT :: Typ
dummyT = Type (\<open>\<^type_name>\<open>dummy\<close>\<close>, [])

is_dummyT :: Typ -> Bool
is_dummyT (Type (\<open>\<^type_name>\<open>dummy\<close>\<close>, [])) = True
is_dummyT _ = False


data Term =
    Const (Bytes, [Typ])
  | Free (Bytes, Typ)
  | Var (Indexname, Typ)
  | Bound Int
  | Abs (Bytes, Typ, Term)
  | App (Term, Term)
  deriving (Show, Eq, Ord)

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

lambda :: (Bytes, Typ) -> Term -> Term
lambda (name, typ) body = Abs (name, typ, abstract 0 body)
  where
    abstract lev (Free (x, ty)) | name == x && typ == ty = Bound lev
    abstract lev (Abs (a, ty, t)) = Abs (a, ty, abstract (lev + 1) t)
    abstract lev (App (t, u)) = App (abstract lev t, abstract lev u)
    abstract _ t = t
\<close>

generate_file "Isabelle/Term_XML/Encode.hs" = \<open>
{-  Title:      Isabelle/Term_XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML data representation of lambda terms.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
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

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
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
    make_line_message, write_line_message, read_line_message,
    read_yxml, write_yxml
  )
where

import Prelude hiding (read)
import Data.Maybe
import qualified Data.ByteString as ByteString
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
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
    result = Bytes.trim_line . Bytes.pack . reverse
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
    res = map Value.parse_nat (Bytes.space_explode (Bytes.byte ',') line)
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


-- hybrid messages: line or length+block (with content restriction)

is_length :: Bytes -> Bool
is_length msg =
  not (Bytes.null msg) && Bytes.all (\b -> 48 <= b && b <= 57) msg

is_terminated :: Bytes -> Bool
is_terminated msg =
  not (Bytes.null msg) && (Bytes.last msg == 13 || Bytes.last msg == 10)

make_line_message :: Bytes -> [Bytes]
make_line_message msg =
  let n = Bytes.length msg in
    if is_length msg || is_terminated msg then
      error ("Bad content for line message:\n" <> take 100 (UTF8.decode msg))
    else
      (if n > 100 || Bytes.any (== 10) msg then make_header [n + 1] else []) <> [msg, "\n"]

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
        Just n -> fmap Bytes.trim_line . fst <$> read_block socket n


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

import Isabelle.Library
import Isabelle.Bytes (Bytes)
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread


{- server address -}

localhost_name :: String
localhost_name = "127.0.0.1"

localhost :: Socket.HostAddress
localhost = Socket.tupleToHostAddress (127, 0, 0, 1)

publish_text :: String -> String -> UUID.T -> String
publish_text name address password =
  "server " <> quote name <> " = " <> address <> " (password " <> quote (show password) <> ")"

publish_stdout :: String -> String -> UUID.T -> IO ()
publish_stdout name address password =
  putStrLn (publish_text name address password)


{- server -}

server :: (String -> UUID.T -> IO ()) -> (Socket -> IO ()) -> IO ()
server publish handle =
  Socket.withSocketsDo $ Exception.bracket open (Socket.close . fst) (uncurry loop)
  where
    open :: IO (Socket, Bytes)
    open = do
      server_socket <- Socket.socket Socket.AF_INET Socket.Stream Socket.defaultProtocol
      Socket.bind server_socket (Socket.SockAddrInet 0 localhost)
      Socket.listen server_socket 50

      port <- Socket.socketPort server_socket
      let address = localhost_name <> ":" <> show port
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

export_generated_files _

end

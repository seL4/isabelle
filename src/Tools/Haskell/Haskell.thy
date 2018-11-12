(*  Title:      Tools/Haskell/Haskell.thy
    Author:     Makarius

Support for Isabelle tools in Haskell.
*)

theory Haskell
  imports Pure
  keywords "generate_haskell_file" "export_haskell_file" :: thy_decl
begin

ML_file "haskell.ML"


section \<open>Commands\<close>

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>generate_haskell_file\<close> "generate Haskell file"
    (Parse.position Parse.path -- (\<^keyword>\<open>=\<close> |-- Parse.input Parse.embedded)
      >> Haskell.generate_file_cmd);

  Outer_Syntax.command \<^command_keyword>\<open>export_haskell_file\<close> "export Haskell file"
    (Parse.name -- (\<^keyword>\<open>=\<close> |-- Parse.input Parse.embedded)
      >> Haskell.export_file_cmd);
\<close>


section \<open>Source modules\<close>

generate_haskell_file "Library.hs" = \<open>
{-  Title:      Tools/Haskell/Library.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Basic library of Isabelle idioms.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/basics.ML\<close>, \<^file>\<open>$ISABELLE_HOME/src/Pure/library.ML\<close>.
-}

module Isabelle.Library (
  (|>), (|->), (#>), (#->),

  the, the_default,

  fold, fold_rev, single, map_index, get_index,

  quote, trim_line)
where

import Data.Maybe


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


{- strings -}

quote :: String -> String
quote s = "\"" ++ s ++ "\""

trim_line :: String -> String
trim_line line =
  case reverse line of
    '\n' : '\r' : rest -> reverse rest
    '\n' : rest -> reverse rest
    _ -> line
\<close>

generate_haskell_file "Value.hs" = \<open>
{-  Title:      Haskell/Tools/Value.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Plain values, represented as string.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/value.ML\<close>.
-}

module Isabelle.Value
  (print_bool, parse_bool, print_int, parse_int, print_real, parse_real)
where

import Data.Maybe
import qualified Data.List as List
import qualified Text.Read as Read


{- bool -}

print_bool :: Bool -> String
print_bool True = "true"
print_bool False = "false"

parse_bool :: String -> Maybe Bool
parse_bool "true" = Just True
parse_bool "false" = Just False
parse_bool _ = Nothing


{- int -}

print_int :: Int -> String
print_int = show

parse_int :: String -> Maybe Int
parse_int = Read.readMaybe


{- real -}

print_real :: Double -> String
print_real x =
  let s = show x in
    case span (/= '.') s of
      (a, '.' : b) | List.all (== '0') b -> a
      _ -> s

parse_real :: String -> Maybe Double
parse_real = Read.readMaybe
\<close>

generate_haskell_file "Buffer.hs" = \<open>
{-  Title:      Tools/Haskell/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text buffers.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/buffer.ML\<close>.
-}

module Isabelle.Buffer (T, empty, add, content)
where

newtype T = Buffer [String]

empty :: T
empty = Buffer []

add :: String -> T -> T
add "" buf = buf
add x (Buffer xs) = Buffer (x : xs)

content :: T -> String
content (Buffer xs) = concat (reverse xs)
\<close>

generate_haskell_file "Properties.hs" = \<open>
{-  Title:      Tools/Haskell/Properties.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Property lists.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/properties.ML\<close>.
-}

module Isabelle.Properties (Entry, T, defined, get, put, remove)
where

import qualified Data.List as List


type Entry = (String, String)
type T = [Entry]

defined :: T -> String -> Bool
defined props name = any (\(a, _) -> a == name) props

get :: T -> String -> Maybe String
get props name = List.lookup name props

put :: Entry -> T -> T
put entry props = entry : remove (fst entry) props

remove :: String -> T -> T
remove name props =
  if defined props name then filter (\(a, _) -> a /= name) props
  else props
\<close>

generate_haskell_file "Markup.hs" = \<open>
{-  Title:      Haskell/Tools/Markup.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Quasi-abstract markup elements.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/markup.ML\<close>.
-}

module Isabelle.Markup (
  T, empty, is_empty, properties,

  nameN, name, xnameN, xname, kindN,

  lineN, end_lineN, offsetN, end_offsetN, fileN, idN, positionN, position,

  markupN, consistentN, unbreakableN, indentN, widthN,
  blockN, block, breakN, break, fbreakN, fbreak, itemN, item,

  wordsN, words, no_wordsN, no_words,

  tfreeN, tfree, tvarN, tvar, freeN, free, skolemN, skolem, boundN, bound, varN, var,
  numeralN, numeral, literalN, literal, delimiterN, delimiter, inner_stringN, inner_string,
  inner_cartoucheN, inner_cartouche, inner_commentN, inner_comment,
  token_rangeN, token_range,
  sortingN, sorting, typingN, typing, class_parameterN, class_parameter,

  antiquotedN, antiquoted, antiquoteN, antiquote,

  paragraphN, paragraph, text_foldN, text_fold,

  keyword1N, keyword1, keyword2N, keyword2, keyword3N, keyword3, quasi_keywordN, quasi_keyword,
  improperN, improper, operatorN, operator, stringN, string, alt_stringN, alt_string,
  verbatimN, verbatim, cartoucheN, cartouche, commentN, comment,

  writelnN, writeln, stateN, state, informationN, information, tracingN, tracing,
  warningN, warning, legacyN, legacy, errorN, error, reportN, report, no_reportN, no_report,

  intensifyN, intensify,
  Output, no_output)
where

import Prelude hiding (words, error, break)

import Isabelle.Library
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Value as Value


{- basic markup -}

type T = (String, Properties.T)

empty :: T
empty = ("", [])

is_empty :: T -> Bool
is_empty ("", _) = True
is_empty _ = False

properties :: Properties.T -> T -> T
properties more_props (elem, props) =
  (elem, fold_rev Properties.put more_props props)

markup_elem name = (name, (name, []) :: T)


{- misc properties -}

nameN :: String
nameN = \<open>Markup.nameN\<close>

name :: String -> T -> T
name a = properties [(nameN, a)]

xnameN :: String
xnameN = \<open>Markup.xnameN\<close>

xname :: String -> T -> T
xname a = properties [(xnameN, a)]

kindN :: String
kindN = \<open>Markup.kindN\<close>


{- position -}

lineN, end_lineN :: String
lineN = \<open>Markup.lineN\<close>
end_lineN = \<open>Markup.end_lineN\<close>

offsetN, end_offsetN :: String
offsetN = \<open>Markup.offsetN\<close>
end_offsetN = \<open>Markup.end_offsetN\<close>

fileN, idN :: String
fileN = \<open>Markup.fileN\<close>
idN = \<open>Markup.idN\<close>

positionN :: String; position :: T
(positionN, position) = markup_elem \<open>Markup.positionN\<close>


{- pretty printing -}

markupN, consistentN, unbreakableN, indentN :: String
markupN = \<open>Markup.markupN\<close>;
consistentN = \<open>Markup.consistentN\<close>;
unbreakableN = \<open>Markup.unbreakableN\<close>;
indentN = \<open>Markup.indentN\<close>;

widthN :: String
widthN = \<open>Markup.widthN\<close>

blockN :: String
blockN = \<open>Markup.blockN\<close>
block :: Bool -> Int -> T
block c i =
  (blockN,
    (if c then [(consistentN, Value.print_bool c)] else []) ++
    (if i /= 0 then [(indentN, Value.print_int i)] else []))

breakN :: String
breakN = \<open>Markup.breakN\<close>
break :: Int -> Int -> T
break w i =
  (breakN,
    (if w /= 0 then [(widthN, Value.print_int w)] else []) ++
    (if i /= 0 then [(indentN, Value.print_int i)] else []))

fbreakN :: String; fbreak :: T
(fbreakN, fbreak) = markup_elem \<open>Markup.fbreakN\<close>

itemN :: String; item :: T
(itemN, item) = markup_elem \<open>Markup.itemN\<close>


{- text properties -}

wordsN :: String; words :: T
(wordsN, words) = markup_elem \<open>Markup.wordsN\<close>

no_wordsN :: String; no_words :: T
(no_wordsN, no_words) = markup_elem \<open>Markup.no_wordsN\<close>


{- inner syntax -}

tfreeN :: String; tfree :: T
(tfreeN, tfree) = markup_elem \<open>Markup.tfreeN\<close>

tvarN :: String; tvar :: T
(tvarN, tvar) = markup_elem \<open>Markup.tvarN\<close>

freeN :: String; free :: T
(freeN, free) = markup_elem \<open>Markup.freeN\<close>

skolemN :: String; skolem :: T
(skolemN, skolem) = markup_elem \<open>Markup.skolemN\<close>

boundN :: String; bound :: T
(boundN, bound) = markup_elem \<open>Markup.boundN\<close>

varN :: String; var :: T
(varN, var) = markup_elem \<open>Markup.varN\<close>

numeralN :: String; numeral :: T
(numeralN, numeral) = markup_elem \<open>Markup.numeralN\<close>

literalN :: String; literal :: T
(literalN, literal) = markup_elem \<open>Markup.literalN\<close>

delimiterN :: String; delimiter :: T
(delimiterN, delimiter) = markup_elem \<open>Markup.delimiterN\<close>

inner_stringN :: String; inner_string :: T
(inner_stringN, inner_string) = markup_elem \<open>Markup.inner_stringN\<close>

inner_cartoucheN :: String; inner_cartouche :: T
(inner_cartoucheN, inner_cartouche) = markup_elem \<open>Markup.inner_cartoucheN\<close>

inner_commentN :: String; inner_comment :: T
(inner_commentN, inner_comment) = markup_elem \<open>Markup.inner_commentN\<close>


token_rangeN :: String; token_range :: T
(token_rangeN, token_range) = markup_elem \<open>Markup.token_rangeN\<close>


sortingN :: String; sorting :: T
(sortingN, sorting) = markup_elem \<open>Markup.sortingN\<close>

typingN :: String; typing :: T
(typingN, typing) = markup_elem \<open>Markup.typingN\<close>

class_parameterN :: String; class_parameter :: T
(class_parameterN, class_parameter) = markup_elem \<open>Markup.class_parameterN\<close>


{- antiquotations -}

antiquotedN :: String; antiquoted :: T
(antiquotedN, antiquoted) = markup_elem \<open>Markup.antiquotedN\<close>

antiquoteN :: String; antiquote :: T
(antiquoteN, antiquote) = markup_elem \<open>Markup.antiquoteN\<close>


{- text structure -}

paragraphN :: String; paragraph :: T
(paragraphN, paragraph) = markup_elem \<open>Markup.paragraphN\<close>

text_foldN :: String; text_fold :: T
(text_foldN, text_fold) = markup_elem \<open>Markup.text_foldN\<close>


{- outer syntax -}

keyword1N :: String; keyword1 :: T
(keyword1N, keyword1) = markup_elem \<open>Markup.keyword1N\<close>

keyword2N :: String; keyword2 :: T
(keyword2N, keyword2) = markup_elem \<open>Markup.keyword2N\<close>

keyword3N :: String; keyword3 :: T
(keyword3N, keyword3) = markup_elem \<open>Markup.keyword3N\<close>

quasi_keywordN :: String; quasi_keyword :: T
(quasi_keywordN, quasi_keyword) = markup_elem \<open>Markup.quasi_keywordN\<close>

improperN :: String; improper :: T
(improperN, improper) = markup_elem \<open>Markup.improperN\<close>

operatorN :: String; operator :: T
(operatorN, operator) = markup_elem \<open>Markup.operatorN\<close>

stringN :: String; string :: T
(stringN, string) = markup_elem \<open>Markup.stringN\<close>

alt_stringN :: String; alt_string :: T
(alt_stringN, alt_string) = markup_elem \<open>Markup.alt_stringN\<close>

verbatimN :: String; verbatim :: T
(verbatimN, verbatim) = markup_elem \<open>Markup.verbatimN\<close>

cartoucheN :: String; cartouche :: T
(cartoucheN, cartouche) = markup_elem \<open>Markup.cartoucheN\<close>

commentN :: String; comment :: T
(commentN, comment) = markup_elem \<open>Markup.commentN\<close>


{- messages -}

writelnN :: String; writeln :: T
(writelnN, writeln) = markup_elem \<open>Markup.writelnN\<close>

stateN :: String; state :: T
(stateN, state) = markup_elem \<open>Markup.stateN\<close>

informationN :: String; information :: T
(informationN, information) = markup_elem \<open>Markup.informationN\<close>

tracingN :: String; tracing :: T
(tracingN, tracing) = markup_elem \<open>Markup.tracingN\<close>

warningN :: String; warning :: T
(warningN, warning) = markup_elem \<open>Markup.warningN\<close>

legacyN :: String; legacy :: T
(legacyN, legacy) = markup_elem \<open>Markup.legacyN\<close>

errorN :: String; error :: T
(errorN, error) = markup_elem \<open>Markup.errorN\<close>

reportN :: String; report :: T
(reportN, report) = markup_elem \<open>Markup.reportN\<close>

no_reportN :: String; no_report :: T
(no_reportN, no_report) = markup_elem \<open>Markup.no_reportN\<close>

intensifyN :: String; intensify :: T
(intensifyN, intensify) = markup_elem \<open>Markup.intensifyN\<close>


{- output -}

type Output = (String, String)

no_output :: Output
no_output = ("", "")
\<close>

generate_haskell_file "File.hs" = \<open>
{-  Title:      Tools/Haskell/File.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

File-system operations.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/file.ML\<close>.
-}

module Isabelle.File (setup, read, write, append) where

import Prelude hiding (read)
import System.IO (IO)
import qualified System.IO as IO

setup :: IO.Handle -> IO ()
setup h = do
  IO.hSetEncoding h IO.utf8
  IO.hSetNewlineMode h IO.noNewlineTranslation

read :: IO.FilePath -> IO String
read path =
  IO.withFile path IO.ReadMode (\h ->
    do setup h; IO.hGetContents h >>= \s -> length s `seq` return s)

write :: IO.FilePath -> String -> IO ()
write path s =
  IO.withFile path IO.WriteMode (\h -> do setup h; IO.hPutStr h s)

append :: IO.FilePath -> String -> IO ()
append path s =
  IO.withFile path IO.AppendMode (\h -> do setup h; IO.hPutStr h s)
\<close>

generate_haskell_file "XML.hs" = \<open>
{-  Title:      Tools/Haskell/XML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Untyped XML trees and representation of ML values.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

module Isabelle.XML (Attributes, Body, Tree(..), wrap_elem, unwrap_elem, content_of)
where

import qualified Data.List as List

import Isabelle.Library
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Buffer as Buffer


{- types -}

type Attributes = Properties.T
type Body = [Tree]
data Tree = Elem Markup.T Body | Text String


{- wrapped elements -}

wrap_elem (((a, atts), body1), body2) =
  Elem (\<open>XML.xml_elemN\<close>, (\<open>XML.xml_nameN\<close>, a) : atts) (Elem (\<open>XML.xml_bodyN\<close>, []) body1 : body2)

unwrap_elem
  (Elem (\<open>XML.xml_elemN\<close>, (\<open>XML.xml_nameN\<close>, a) : atts) (Elem (\<open>XML.xml_bodyN\<close>, []) body1 : body2)) =
  Just (((a, atts), body1), body2)
unwrap_elem _ = Nothing


{- text content -}

add_content tree =
  case unwrap_elem tree of
    Just (_, ts) -> fold add_content ts
    Nothing ->
      case tree of
        Elem _ ts -> fold add_content ts
        Text s -> Buffer.add s

content_of body = Buffer.empty |> fold add_content body |> Buffer.content


{- string representation -}

encode '<' = "&lt;"
encode '>' = "&gt;"
encode '&' = "&amp;"
encode '\'' = "&apos;"
encode '\"' = "&quot;"
encode c = [c]

instance Show Tree where
  show tree =
    Buffer.empty |> show_tree tree |> Buffer.content
    where
      show_tree (Elem (name, atts) []) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add "/>"
      show_tree (Elem (name, atts) ts) =
        Buffer.add "<" #> Buffer.add (show_elem name atts) #> Buffer.add ">" #>
        fold show_tree ts #>
        Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
      show_tree (Text s) = Buffer.add (show_text s)

      show_elem name atts =
        unwords (name : map (\(a, x) -> a ++ "=\"" ++ show_text x ++ "\"") atts)

      show_text = concatMap encode
\<close>

generate_haskell_file "XML/Encode.hs" = \<open>
{-  Title:      Tools/Haskell/XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

module Isabelle.XML.Encode (
  A, T, V,

  int_atom, bool_atom, unit_atom,

  tree, properties, string, int, bool, unit, pair, triple, list, variant
)
where

import Isabelle.Library
import qualified Isabelle.Value as Value
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML


type A a = a -> String
type T a = a -> XML.Body
type V a = a -> Maybe ([String], XML.Body)


-- atomic values

int_atom :: A Int
int_atom = Value.print_int

bool_atom :: A Bool
bool_atom False = "0"
bool_atom True = "1"

unit_atom :: A ()
unit_atom () = ""


-- structural nodes

node = XML.Elem (":", [])

vector = map_index (\(i, x) -> (int_atom i, x))

tagged (tag, (xs, ts)) = XML.Elem (int_atom tag, vector xs) ts


-- representation of standard types

tree :: T XML.Tree
tree t = [t]

properties :: T Properties.T
properties props = [XML.Elem (":", props) []]

string :: T String
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

variant :: [V a] -> T a
variant fs x = [tagged (the (get_index (\f -> f x) fs))]
\<close>

generate_haskell_file "XML/Decode.hs" = \<open>
{-  Title:      Tools/Haskell/XML/Decode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/xml.ML\<close>.
-}

module Isabelle.XML.Decode (
  A, T, V,

  int_atom, bool_atom, unit_atom,

  tree, properties, string, init, bool, unit, pair, triple, list, variant
)
where

import Data.List ((!!))

import Isabelle.Library
import qualified Isabelle.Value as Value
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML


type A a = String -> a
type T a = XML.Body -> a
type V a = ([String], XML.Body) -> a

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

node (XML.Elem (":", []) ts) = ts
node _ = err_body

vector atts =
  map_index (\(i, (a, x)) -> if int_atom a == i then x else err_atom) atts

tagged (XML.Elem (name, atts) ts) = (int_atom name, (vector atts, ts))
tagged _ = err_body


{- representation of standard types -}

tree :: T XML.Tree
tree [t] = t
tree _ = err_body

properties :: T Properties.T
properties [XML.Elem (":", props) []] = props
properties _ = err_body

string :: T String
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

generate_haskell_file "Pretty.hs" = \<open>
{-  Title:      Tools/Haskell/Pretty.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Generic pretty printing module.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/General/pretty.ML\<close>.
-}

module Isabelle.Pretty (
  T, symbolic, formatted, unformatted,

  str, brk_indent, brk, fbrk, breaks, fbreaks, blk, block, strs, markup, mark, mark_str, marks_str,
  item, text_fold, keyword1, keyword2, text, paragraph, para, quote, cartouche, separate,
  commas, enclose, enum, list, str_list, big_list)
where

import Isabelle.Library hiding (quote)
import qualified Data.List as List
import qualified Isabelle.Buffer as Buffer
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML


data T =
    Block Markup.T Bool Int [T]
  | Break Int Int
  | Str String


{- output -}

output_spaces n = replicate n ' '

symbolic_text "" = []
symbolic_text s = [XML.Text s]

symbolic_markup markup body =
  if Markup.is_empty markup then body
  else [XML.Elem markup body]

symbolic :: T -> XML.Body
symbolic (Block markup consistent indent prts) =
  concatMap symbolic prts
  |> symbolic_markup block_markup
  |> symbolic_markup markup
  where block_markup = if null prts then Markup.empty else Markup.block consistent indent
symbolic (Break wd ind) = [XML.Elem (Markup.break wd ind) (symbolic_text (output_spaces wd))]
symbolic (Str s) = symbolic_text s

formatted :: T -> String
formatted = YXML.string_of_body . symbolic

unformatted :: T -> String
unformatted prt = Buffer.empty |> out prt |> Buffer.content
  where
    out (Block markup _ _ prts) =
      let (bg, en) = YXML.output_markup markup
      in Buffer.add bg #> fold out prts #> Buffer.add en
    out (Break _ wd) = Buffer.add (output_spaces wd)
    out (Str s) = Buffer.add s


{- derived operations to create formatting expressions -}

force_nat n | n < 0 = 0
force_nat n = n

str :: String -> T
str = Str

brk_indent :: Int -> Int -> T
brk_indent wd ind = Break (force_nat wd) ind

brk :: Int -> T
brk wd = brk_indent wd 0

fbrk :: T
fbrk = str "\n"

breaks, fbreaks :: [T] -> [T]
breaks = List.intersperse (brk 1)
fbreaks = List.intersperse fbrk

blk :: (Int, [T]) -> T
blk (indent, es) = Block Markup.empty False (force_nat indent) es

block :: [T] -> T
block prts = blk (2, prts)

strs :: [String] -> T
strs = block . breaks . map str

markup :: Markup.T -> [T] -> T
markup m = Block m False 0

mark :: Markup.T -> T -> T
mark m prt = if m == Markup.empty then prt else markup m [prt]

mark_str :: (Markup.T, String) -> T
mark_str (m, s) = mark m (str s)

marks_str :: ([Markup.T], String) -> T
marks_str (ms, s) = fold_rev mark ms (str s)

item :: [T] -> T
item = markup Markup.item

text_fold :: [T] -> T
text_fold = markup Markup.text_fold

keyword1, keyword2 :: String -> T
keyword1 name = mark_str (Markup.keyword1, name)
keyword2 name = mark_str (Markup.keyword2, name)

text :: String -> [T]
text = breaks . map str . words

paragraph :: [T] -> T
paragraph = markup Markup.paragraph

para :: String -> T
para = paragraph . text

quote :: T -> T
quote prt = blk (1, [str "\"", prt, str "\""])

cartouche :: T -> T
cartouche prt = blk (1, [str "\92<open>", prt, str "\92<close>"])

separate :: String -> [T] -> [T]
separate sep = List.intercalate [str sep, brk 1] . map single

commas :: [T] -> [T]
commas = separate ","

enclose :: String -> String -> [T] -> T
enclose lpar rpar prts = block (str lpar : prts ++ [str rpar])

enum :: String -> String -> String -> [T] -> T
enum sep lpar rpar = enclose lpar rpar . separate sep

list :: String -> String -> [T] -> T
list = enum ","

str_list :: String -> String -> [String] -> T
str_list lpar rpar = list lpar rpar . map str

big_list :: String -> [T] -> T
big_list name prts = block (fbreaks (str name : prts))
\<close>

generate_haskell_file "YXML.hs" = \<open>
{-  Title:      Tools/Haskell/YXML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text representation of XML trees.  Suitable for direct
inlining into plain text.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/PIDE/yxml.ML\<close>.
-}

module Isabelle.YXML (charX, charY, strX, strY, detect, output_markup,
  buffer_body, buffer, string_of_body, string_of, parse_body, parse)
where

import qualified Data.Char as Char
import qualified Data.List as List

import Isabelle.Library
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.Buffer as Buffer


{- markers -}

charX, charY :: Char
charX = Char.chr 5
charY = Char.chr 6

strX, strY, strXY, strXYX :: String
strX = [charX]
strY = [charY]
strXY = strX ++ strY
strXYX = strXY ++ strX

detect :: String -> Bool
detect = any (\c -> c == charX || c == charY)


{- output -}

output_markup :: Markup.T -> Markup.Output
output_markup markup@(name, atts) =
  if Markup.is_empty markup then Markup.no_output
  else (strXY ++ name ++ concatMap (\(a, x) -> strY ++ a ++ "=" ++ x) atts ++ strX, strXYX)

buffer_attrib (a, x) =
  Buffer.add strY #> Buffer.add a #> Buffer.add "=" #> Buffer.add x

buffer_body :: XML.Body -> Buffer.T -> Buffer.T
buffer_body = fold buffer

buffer :: XML.Tree -> Buffer.T -> Buffer.T
buffer (XML.Elem (name, atts) ts) =
  Buffer.add strXY #> Buffer.add name #> fold buffer_attrib atts #> Buffer.add strX #>
  buffer_body ts #>
  Buffer.add strXYX
buffer (XML.Text s) = Buffer.add s

string_of_body :: XML.Body -> String
string_of_body body = Buffer.empty |> buffer_body body |> Buffer.content

string_of :: XML.Tree -> String
string_of = string_of_body . single


{- parse -}

-- split: fields or non-empty tokens

split :: Bool -> Char -> String -> [String]
split _ _ [] = []
split fields sep str = splitting str
  where
    splitting rest =
      case span (/= sep) rest of
        (_, []) -> cons rest []
        (prfx, _ : rest') -> cons prfx (splitting rest')
    cons item = if fields || not (null item) then (:) item else id


-- structural errors

err msg = error ("Malformed YXML: " ++ msg)
err_attribute = err "bad attribute"
err_element = err "bad element"
err_unbalanced "" = err "unbalanced element"
err_unbalanced name = err ("unbalanced element " ++ quote name)


-- stack operations

add x ((elem, body) : pending) = (elem, x : body) : pending

push "" _ _ = err_element
push name atts pending = ((name, atts), []) : pending

pop ((("", _), _) : _) = err_unbalanced ""
pop ((markup, body) : pending) = add (XML.Elem markup (reverse body)) pending


-- parsing

parse_attrib s =
  case List.elemIndex '=' s of
    Just i | i > 0 -> (take i s, drop (i + 1) s)
    _ -> err_attribute

parse_chunk ["", ""] = pop
parse_chunk ("" : name : atts) = push name (map parse_attrib atts)
parse_chunk txts = fold (add . XML.Text) txts

parse_body :: String -> XML.Body
parse_body source =
  case fold parse_chunk chunks [(("", []), [])] of
    [(("", _), result)] -> reverse result
    ((name, _), _) : _ -> err_unbalanced name
  where chunks = split False charX source |> map (split True charY)

parse :: String -> XML.Tree
parse source =
  case parse_body source of
    [result] -> result
    [] -> XML.Text ""
    _ -> err "multiple results"
\<close>

generate_haskell_file "Term.hs" = \<open>
{-  Title:      Tools/Haskell/Term.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Lambda terms, types, sorts.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term.scala\<close>.
-}

module Isabelle.Term (
  Indexname,

  Sort, dummyS,

  Typ(..), dummyT, Term(..))
where

type Indexname = (String, Int)


type Sort = [String]

dummyS :: Sort
dummyS = [""]


data Typ =
    Type (String, [Typ])
  | TFree (String, Sort)
  | TVar (Indexname, Sort)
  deriving Show

dummyT :: Typ
dummyT = Type (\<open>\<^type_name>\<open>dummy\<close>\<close>, [])


data Term =
    Const (String, Typ)
  | Free (String, Typ)
  | Var (Indexname, Typ)
  | Bound Int
  | Abs (String, Typ, Term)
  | App (Term, Term)
  deriving Show
\<close>

generate_haskell_file "Term_XML/Encode.hs" = \<open>
{-  Title:      Tools/Haskell/Term_XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML data representation of lambda terms.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
-}

{-# LANGUAGE LambdaCase #-}

module Isabelle.Term_XML.Encode (sort, typ, term)
where

import Isabelle.Library
import qualified Isabelle.XML as XML
import Isabelle.XML.Encode
import Isabelle.Term


sort :: T Sort
sort = list string

typ :: T Typ
typ ty =
  ty |> variant
   [\case { Type (a, b) -> Just ([a], list typ b); _ -> Nothing },
    \case { TFree (a, b) -> Just ([a], sort b); _ -> Nothing },
    \case { TVar ((a, b), c) -> Just ([a, int_atom b], sort c); _ -> Nothing }]

term :: T Term
term t =
  t |> variant
   [\case { Const (a, b) -> Just ([a], typ b); _ -> Nothing },
    \case { Free (a, b) -> Just ([a], typ b); _ -> Nothing },
    \case { Var ((a, b), c) -> Just ([a, int_atom b], typ c); _ -> Nothing },
    \case { Bound a -> Just ([int_atom a], []); _ -> Nothing },
    \case { Abs (a, b, c) -> Just ([a], pair typ term (b, c)); _ -> Nothing },
    \case { App a -> Just ([], pair term term a); _ -> Nothing }]
\<close>

generate_haskell_file "Term_XML/Decode.hs" = \<open>
{-  Title:      Tools/Haskell/Term_XML/Decode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML data representation of lambda terms.

See also \<^file>\<open>$ISABELLE_HOME/src/Pure/term_xml.ML\<close>.
-}

module Isabelle.Term_XML.Decode (sort, typ, term)
where

import Isabelle.Library
import qualified Isabelle.XML as XML
import Isabelle.XML.Decode
import Isabelle.Term


sort :: T Sort
sort = list string

typ :: T Typ
typ ty =
  ty |> variant
  [\([a], b) -> Type (a, list typ b),
   \([a], b) -> TFree (a, sort b),
   \([a, b], c) -> TVar ((a, int_atom b), sort c)]

term :: T Term
term t =
  t |> variant
   [\([a], b) -> Const (a, typ b),
    \([a], b) -> Free (a, typ b),
    \([a, b], c) -> Var ((a, int_atom b), typ c),
    \([a], []) -> Bound (int_atom a),
    \([a], b) -> let (c, d) = pair typ term b in Abs (a, c, d),
    \([], a) -> App (pair term term a)]
\<close>

end

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

generate_haskell_file Library.hs = \<open>
{-  Title:      Tools/Haskell/Library.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Basic library of Isabelle idioms.
-}

module Isabelle.Library
  ((|>), (|->), (#>), (#->), fold, fold_rev, single, quote, trim_line)
where

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

generate_haskell_file Value.hs = \<open>
{-  Title:      Haskell/Tools/Value.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Plain values, represented as string.
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

generate_haskell_file Buffer.hs = \<open>
{-  Title:      Tools/Haskell/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text buffers.
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

generate_haskell_file Properties.hs = \<open>
{-  Title:      Tools/Haskell/Properties.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Property lists.
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

generate_haskell_file Markup.hs = \<open>
{-  Title:      Haskell/Tools/Markup.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Quasi-abstract markup elements.
-}

module Isabelle.Markup (T, empty, is_empty, Output, no_output)
where

import qualified Isabelle.Properties as Properties


type T = (String, Properties.T)

empty :: T
empty = ("", [])

is_empty :: T -> Bool
is_empty ("", _) = True
is_empty _ = False


type Output = (String, String)

no_output :: Output
no_output = ("", "")
\<close>

generate_haskell_file XML.hs = \<open>
{-  Title:      Tools/Haskell/XML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Untyped XML trees and representation of ML values.
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

xml_elemN = "xml_elem";
xml_nameN = "xml_name";
xml_bodyN = "xml_body";

wrap_elem (((a, atts), body1), body2) =
  Elem (xml_elemN, (xml_nameN, a) : atts) (Elem (xml_bodyN, []) body1 : body2)

unwrap_elem (Elem (name, (n, a) : atts) (Elem (name', atts') body1 : body2)) =
  if name == xml_elemN && n == xml_nameN && name' == xml_bodyN && null atts'
  then Just (((a, atts), body1), body2) else Nothing
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

generate_haskell_file YXML.hs = \<open>
{-  Title:      Tools/Haskell/YXML.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text representation of XML trees.  Suitable for direct
inlining into plain text.
-}

module Isabelle.YXML (charX, charY, strX, strY, detect,
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

end

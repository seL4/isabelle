(*  Title:      Pure/PIDE/xml0.ML
    Author:     Makarius

Untyped XML trees and YXML notation: minimal bootstrap version.
*)

(** XML **)

signature XML =
sig
  type attributes = (string * string) list
  datatype tree =
      Elem of (string * attributes) * tree list
    | Text of string
  type body = tree list
  val xml_elemN: string
  val xml_nameN: string
  val xml_bodyN: string
  val wrap_elem: ((string * attributes) * body) * body -> tree
  val unwrap_elem: tree -> (((string * attributes) * body) * body) option
  val unwrap_elem_body: tree -> body option
  val traverse_text: (string -> 'a -> 'a) -> tree -> 'a -> 'a
  val traverse_texts: (string -> 'a -> 'a) -> body -> 'a -> 'a
  val content_of: body -> string
end

structure XML: XML =
struct

type attributes = (string * string) list;

datatype tree =
    Elem of (string * attributes) * tree list
  | Text of string;

type body = tree list;


(* wrapped elements *)

val xml_elemN = "xml_elem";
val xml_nameN = "xml_name";
val xml_bodyN = "xml_body";

fun wrap_elem (((a, atts), body1), body2) =
  Elem ((xml_elemN, (xml_nameN, a) :: atts), Elem ((xml_bodyN, []), body1) :: body2);

fun unwrap_elem (Elem ((name, (n, a) :: atts), Elem ((name', []), body1) :: body2)) =
      if name = xml_elemN andalso n = xml_nameN andalso name' = xml_bodyN
      then SOME (((a, atts), body1), body2) else NONE
  | unwrap_elem _ = NONE;

fun unwrap_elem_body (Elem ((name, (n, _) :: _), Elem ((name', []), _) :: body)) =
      if name = xml_elemN andalso n = xml_nameN andalso name' = xml_bodyN
      then SOME body else NONE
  | unwrap_elem_body _ = NONE;


(* traverse text content *)

fun traverse_text f tree =
  (case unwrap_elem_body tree of
    SOME ts => traverse_texts f ts
  | NONE =>
      (case tree of
        Elem (_, ts) => traverse_texts f ts
      | Text s => f s))
and traverse_texts _ [] res = res
  | traverse_texts f (t :: ts) res = traverse_texts f ts (traverse_text f t res);

fun content_of body =
  String.concat (rev (traverse_texts (fn x => fn xs => x :: xs) body []));

end;



(** YXML **)

signature YXML =
sig
  val X_char: char
  val Y_char: char
  val X: string
  val Y: string
  val XY: string
  val XYX: string
  val detect: string -> bool
  val output_markup: string * XML.attributes -> string * string
end;

structure YXML: YXML =
struct

(* markers *)

val X_char = Char.chr 5;
val Y_char = Char.chr 6;

val X = String.str X_char;
val Y = String.str Y_char;
val XY = X ^ Y;
val XYX = XY ^ X;

fun detect s = Char.contains s X_char orelse Char.contains s Y_char;


(* output markup *)

fun output_markup ("", _) = ("", "")
  | output_markup (name, atts) =
      let
        val bgs = XY :: name :: List.foldr (fn ((a, b), ps) => Y :: a :: "=" :: b :: ps) [X] atts;
        val en = XYX;
      in (String.concat bgs, en) end;

end;

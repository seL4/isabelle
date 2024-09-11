(*  Title:      Pure/PIDE/xml0.ML
    Author:     Makarius

Untyped XML trees (bootstrap).
*)

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

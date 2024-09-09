(*  Title:      Pure/PIDE/xml_type.ML
    Author:     Makarius

Untyped XML trees: minimal type definitions.
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


(* text content *)

fun add_contents [] res = res
  | add_contents (t :: ts) res = add_contents ts (add_content t res)
and add_content tree res =
  (case unwrap_elem tree of
    SOME (_, ts) => add_contents ts res
  | NONE =>
      (case tree of
        Elem (_, ts) => add_contents ts res
      | Text s => s :: res));

fun content_of body =
  String.concat (rev (add_contents body []));

end;

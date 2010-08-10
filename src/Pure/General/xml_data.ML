(*  Title:      Pure/General/xml_data.ML
    Author:     Makarius

XML as basic data representation language.
*)

signature XML_DATA =
sig
  exception XML_ATOM of string
  exception XML_BODY of XML.body
  val make_properties: Properties.T -> XML.body
  val dest_properties: XML.body -> Properties.T
  val make_string: string -> XML.body
  val dest_string : XML.body -> string
  val make_int: int -> XML.body
  val dest_int : XML.body -> int
  val make_bool: bool -> XML.body
  val dest_bool: XML.body -> bool
  val make_unit: unit -> XML.body
  val dest_unit: XML.body -> unit
  val make_pair: ('a -> XML.body) -> ('b -> XML.body) -> 'a * 'b -> XML.body
  val dest_pair: (XML.body -> 'a) -> (XML.body -> 'b) -> XML.body -> 'a * 'b
  val make_triple:
    ('a -> XML.body) -> ('b -> XML.body) -> ('c -> XML.body) -> 'a * 'b * 'c -> XML.body
  val dest_triple:
    (XML.body -> 'a) -> (XML.body -> 'b) -> (XML.body -> 'c) -> XML.body -> 'a * 'b * 'c
  val make_list: ('a -> XML.body) -> 'a list -> XML.body
  val dest_list: (XML.body -> 'a) -> XML.body -> 'a list
  val make_option: ('a -> XML.body) -> 'a option -> XML.body
  val dest_option: (XML.body -> 'a) -> XML.body -> 'a option
end;

structure XML_Data: XML_DATA =
struct

(* basic values *)

exception XML_ATOM of string;


fun make_int_atom i = signed_string_of_int i;

fun dest_int_atom s =
  (case Int.fromString s of
    SOME i => i
  | NONE => raise XML_ATOM s);


fun make_bool_atom false = "0"
  | make_bool_atom true = "1";

fun dest_bool_atom "0" = false
  | dest_bool_atom "1" = true
  | dest_bool_atom s = raise XML_ATOM s;


fun make_unit_atom () = "";

fun dest_unit_atom "" = ()
  | dest_unit_atom s = raise XML_ATOM s;


(* structural nodes *)

exception XML_BODY of XML.tree list;

fun make_node ts = XML.Elem ((":", []), ts);

fun dest_node (XML.Elem ((":", []), ts)) = ts
  | dest_node t = raise XML_BODY [t];


(* representation of standard types *)

fun make_properties props = [XML.Elem ((":", props), [])];

fun dest_properties [XML.Elem ((":", props), [])] = props
  | dest_properties ts = raise XML_BODY ts;


fun make_string "" = []
  | make_string s = [XML.Text s];

fun dest_string [] = ""
  | dest_string [XML.Text s] = s
  | dest_string ts = raise XML_BODY ts;


val make_int = make_string o make_int_atom;
val dest_int = dest_int_atom o dest_string;

val make_bool = make_string o make_bool_atom;
val dest_bool = dest_bool_atom o dest_string;

val make_unit = make_string o make_unit_atom;
val dest_unit = dest_unit_atom o dest_string;


fun make_pair make1 make2 (x, y) = [make_node (make1 x), make_node (make2 y)];

fun dest_pair dest1 dest2 [t1, t2] = (dest1 (dest_node t1), dest2 (dest_node t2))
  | dest_pair _ _ ts = raise XML_BODY ts;


fun make_triple make1 make2 make3 (x, y, z) =
  [make_node (make1 x), make_node (make2 y), make_node (make3 z)];

fun dest_triple dest1 dest2 dest3 [t1, t2, t3] =
      (dest1 (dest_node t1), dest2 (dest_node t2), dest3 (dest_node t3))
  | dest_triple _ _ _ ts = raise XML_BODY ts;


fun make_list make xs = map (make_node o make) xs;

fun dest_list dest ts = map (dest o dest_node) ts;


fun make_option make NONE = make_list make []
  | make_option make (SOME x) = make_list make [x];

fun dest_option dest ts =
  (case dest_list dest ts of
    [] => NONE
  | [x] => SOME x
  | _ => raise XML_BODY ts);

end;


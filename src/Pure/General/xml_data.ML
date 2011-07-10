(*  Title:      Pure/General/xml_data.ML
    Author:     Makarius

XML as basic data representation language.
*)

signature XML_DATA =
sig
  structure Make:
  sig
    val properties: Properties.T -> XML.body
    val string: string -> XML.body
    val int: int -> XML.body
    val bool: bool -> XML.body
    val unit: unit -> XML.body
    val pair: ('a -> XML.body) -> ('b -> XML.body) -> 'a * 'b -> XML.body
    val triple: ('a -> XML.body) -> ('b -> XML.body) -> ('c -> XML.body) -> 'a * 'b * 'c -> XML.body
    val list: ('a -> XML.body) -> 'a list -> XML.body
    val option: ('a -> XML.body) -> 'a option -> XML.body
    val variant: ('a -> XML.body) list -> 'a -> XML.body
  end
  exception XML_ATOM of string
  exception XML_BODY of XML.body
  structure Dest:
  sig
    val properties: XML.body -> Properties.T
    val string : XML.body -> string
    val int : XML.body -> int
    val bool: XML.body -> bool
    val unit: XML.body -> unit
    val pair: (XML.body -> 'a) -> (XML.body -> 'b) -> XML.body -> 'a * 'b
    val triple: (XML.body -> 'a) -> (XML.body -> 'b) -> (XML.body -> 'c) -> XML.body -> 'a * 'b * 'c
    val list: (XML.body -> 'a) -> XML.body -> 'a list
    val option: (XML.body -> 'a) -> XML.body -> 'a option
    val variant: (XML.body -> 'a) list -> XML.body -> 'a
  end
end;

structure XML_Data: XML_DATA =
struct

(** make **)

structure Make =
struct

(* basic values *)

fun int_atom i = signed_string_of_int i;

fun bool_atom false = "0"
  | bool_atom true = "1";

fun unit_atom () = "";


(* structural nodes *)

fun node ts = XML.Elem ((":", []), ts);

fun tagged (tag, ts) = XML.Elem ((int_atom tag, []), ts);


(* representation of standard types *)

fun properties props = [XML.Elem ((":", props), [])];

fun string "" = []
  | string s = [XML.Text s];

val int = string o int_atom;

val bool = string o bool_atom;

val unit = string o unit_atom;

fun pair f g (x, y) = [node (f x), node (g y)];

fun triple f g h (x, y, z) = [node (f x), node (g y), node (h z)];

fun list f xs = map (node o f) xs;

fun option _ NONE = []
  | option f (SOME x) = [node (f x)];

fun variant fs x = [tagged (the (get_index (fn f => try f x) fs))];

end;



(** dest **)

exception XML_ATOM of string;
exception XML_BODY of XML.tree list;

structure Dest =
struct

(* basic values *)

fun int_atom s =
  (case Int.fromString s of
    SOME i => i
  | NONE => raise XML_ATOM s);

fun bool_atom "0" = false
  | bool_atom "1" = true
  | bool_atom s = raise XML_ATOM s;

fun unit_atom "" = ()
  | unit_atom s = raise XML_ATOM s;


(* structural nodes *)

fun node (XML.Elem ((":", []), ts)) = ts
  | node t = raise XML_BODY [t];

fun tagged (XML.Elem ((s, []), ts)) = (int_atom s, ts)
  | tagged t = raise XML_BODY [t];


(* representation of standard types *)

fun properties [XML.Elem ((":", props), [])] = props
  | properties ts = raise XML_BODY ts;

fun string [] = ""
  | string [XML.Text s] = s
  | string ts = raise XML_BODY ts;

val int = int_atom o string;

val bool = bool_atom o string;

val unit = unit_atom o string;

fun pair f g [t1, t2] = (f (node t1), g (node t2))
  | pair _ _ ts = raise XML_BODY ts;

fun triple f g h [t1, t2, t3] = (f (node t1), g (node t2), h (node t3))
  | triple _ _ _ ts = raise XML_BODY ts;

fun list f ts = map (f o node) ts;

fun option _ [] = NONE
  | option f [t] = SOME (f (node t))
  | option _ ts = raise XML_BODY ts;

fun variant fs [t] = uncurry (nth fs) (tagged t)
  | variant _ ts = raise XML_BODY ts;

end;

end;


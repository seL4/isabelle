(*  Title:      Pure/General/xml_data.ML
    Author:     Makarius

XML as basic data representation language.
*)

signature XML_DATA_OPS =
sig
  type 'a T
  val properties: Properties.T T
  val string: string T
  val int: int T
  val bool: bool T
  val unit: unit T
  val pair: 'a T -> 'b T -> ('a * 'b) T
  val triple: 'a T -> 'b T -> 'c T -> ('a * 'b * 'c) T
  val list: 'a T -> 'a list T
  val option: 'a T -> 'a option T
  val variant: 'a T list -> 'a T
end;

signature XML_DATA =
sig
  structure Make: XML_DATA_OPS where type 'a T = 'a -> XML.body
  exception XML_ATOM of string
  exception XML_BODY of XML.body
  structure Dest: XML_DATA_OPS where type 'a T = XML.body -> 'a
end;

structure XML_Data: XML_DATA =
struct

(** make **)

structure Make =
struct

type 'a T = 'a -> XML.body;


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

type 'a T = XML.body -> 'a;


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


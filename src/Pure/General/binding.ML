(*  Title:      Pure/General/binding.ML
    Author:     Florian Haftmann, TU Muenchen

Structured name bindings.
*)

signature BASIC_BINDING =
sig
  val long_names: bool ref
  val short_names: bool ref
  val unique_names: bool ref
end;

signature BINDING =
sig
  include BASIC_BINDING
  type T
  val name_pos: string * Position.T -> T
  val name: string -> T
  val empty: T
  val map_base: (string -> string) -> T -> T
  val qualify: string -> T -> T
  val add_prefix: bool -> string -> T -> T
  val map_prefix: ((string * bool) list -> T -> T) -> T -> T
  val is_empty: T -> bool
  val base_name: T -> string
  val pos_of: T -> Position.T
  val dest: T -> (string * bool) list * string
  val separator: string
  val is_qualified: string -> bool
  val display: T -> string
end

structure Binding : BINDING =
struct

(** global flags **)

val long_names = ref false;
val short_names = ref false;
val unique_names = ref true;


(** qualification **)

val separator = ".";
val is_qualified = exists_string (fn s => s = separator);

fun reject_qualified kind s =
  if is_qualified s then
    error ("Attempt to declare qualified " ^ kind ^ " " ^ quote s)
  else s;


(** binding representation **)

datatype T = Binding of ((string * bool) list * string) * Position.T;
  (* (prefix components (with mandatory flag), base name, position) *)

fun name_pos (name, pos) = Binding (([], name), pos);
fun name name = name_pos (name, Position.none);
val empty = name "";

fun map_binding f (Binding (prefix_name, pos)) = Binding (f prefix_name, pos);

val map_base = map_binding o apsnd;

fun qualify_base path name =
  if path = "" orelse name = "" then name
  else path ^ separator ^ name;

val qualify = map_base o qualify_base;
  (*FIXME should all operations on bare names move here from name_space.ML ?*)

fun add_prefix sticky "" b = b
  | add_prefix sticky prfx b = (map_binding o apfst)
      (cons ((*reject_qualified "prefix"*) prfx, sticky)) b;

fun map_prefix f (Binding ((prefix, name), pos)) =
  f prefix (name_pos (name, pos));

fun is_empty (Binding ((_, name), _)) = name = "";
fun base_name (Binding ((_, name), _)) = name;
fun pos_of (Binding (_, pos)) = pos;
fun dest (Binding (prefix_name, _)) = prefix_name;

fun display (Binding ((prefix, name), _)) =
  let
    fun mk_prefix (prfx, true) = prfx
      | mk_prefix (prfx, false) = enclose "(" ")" prfx
  in if not (! long_names) orelse null prefix orelse name = "" then name
    else space_implode "." (map mk_prefix prefix) ^ ":" ^ name
  end;

end;

structure Basic_Binding : BASIC_BINDING = Binding;
open Basic_Binding;

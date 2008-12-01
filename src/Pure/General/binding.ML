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
  val binding_pos: string * Position.T -> T
  val binding: string -> T
  val no_binding: T
  val dest_binding: T -> (string * bool) list * string
  val is_nothing: T -> bool
  val pos_of: T -> Position.T
 
  val map_binding: ((string * bool) list * string -> (string * bool) list * string)
    -> T -> T
  val add_prefix: bool -> string -> T -> T
  val map_prefix: ((string * bool) list -> T -> T) -> T -> T
  val display: T -> string
end

structure Binding : BINDING =
struct

(** global flags **)

val long_names = ref false;
val short_names = ref false;
val unique_names = ref true;


(** binding representation **)

datatype T = Binding of ((string * bool) list * string) * Position.T;
  (* (prefix components (with mandatory flag), base name, position) *)

fun binding_pos (name, pos) = Binding (([], name), pos);
fun binding name = binding_pos (name, Position.none);
val no_binding = binding "";

fun pos_of (Binding (_, pos)) = pos;
fun dest_binding (Binding (prefix_name, _)) = prefix_name;

fun map_binding f (Binding (prefix_name, pos)) = Binding (f prefix_name, pos);

fun is_nothing (Binding ((_, name), _)) = name = "";

fun add_prefix sticky prfx b = if prfx = "" then error "empty name prefix"
  else (map_binding o apfst) (cons (prfx, sticky)) b;

fun map_prefix f (Binding ((prefix, name), pos)) =
  f prefix (binding_pos (name, pos));

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

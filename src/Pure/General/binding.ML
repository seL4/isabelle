(*  Title:      Pure/General/binding.ML
    Author:     Florian Haftmann, TU Muenchen
    Author:     Makarius

Structured name bindings.
*)

type bstring = string;    (*primitive names to be bound*)

signature BINDING =
sig
  type binding
  val dest: binding -> (string * bool) list * (string * bool) list * bstring
  val verbose: bool ref
  val str_of: binding -> string
  val make: bstring * Position.T -> binding
  val name: bstring -> binding
  val pos_of: binding -> Position.T
  val name_of: binding -> string
  val map_name: (bstring -> bstring) -> binding -> binding
  val empty: binding
  val is_empty: binding -> bool
  val qualify: bool -> string -> binding -> binding
  val map_prefix: ((string * bool) list -> (string * bool) list) -> binding -> binding
  val add_prefix: bool -> string -> binding -> binding
end;

structure Binding: BINDING =
struct

(** representation **)

(* datatype *)

type component = string * bool;   (*name with mandatory flag*)

datatype binding = Binding of
 {prefix: component list,         (*system prefix*)
  qualifier: component list,      (*user qualifier*)
  name: bstring,                  (*base name*)
  pos: Position.T};               (*source position*)

fun make_binding (prefix, qualifier, name, pos) =
  Binding {prefix = prefix, qualifier = qualifier, name = name, pos = pos};

fun map_binding f (Binding {prefix, qualifier, name, pos}) =
  make_binding (f (prefix, qualifier, name, pos));

fun dest (Binding {prefix, qualifier, name, ...}) = (prefix, qualifier, name);


(* diagnostic output *)

val verbose = ref false;

val str_of_components = implode o map (fn (s, true) => s ^ "!" | (s, false) => s ^ "?");

fun str_of (Binding {prefix, qualifier, name, pos}) =
  let
    val text =
      if ! verbose then
        (if null prefix then "" else enclose "(" ")" (str_of_components prefix)) ^
          str_of_components qualifier ^ name
      else name;
    val props = Position.properties_of pos;
  in Markup.markup (Markup.properties props (Markup.binding name)) text end;



(** basic operations **)

(* name and position *)

fun make (name, pos) = make_binding ([], [], name, pos);
fun name name = make (name, Position.none);

fun pos_of (Binding {pos, ...}) = pos;
fun name_of (Binding {name, ...}) = name;

fun map_name f = map_binding (fn (prefix, qualifier, name, pos) => (prefix, qualifier, f name, pos));

val empty = name "";
fun is_empty b = name_of b = "";


(* user qualifier *)

fun qualify _ "" = I
  | qualify mandatory qual = map_binding (fn (prefix, qualifier, name, pos) =>
      (prefix, (qual, mandatory) :: qualifier, name, pos));


(* system prefix *)

fun map_prefix f = map_binding (fn (prefix, qualifier, name, pos) =>
  (f prefix, qualifier, name, pos));

fun add_prefix _ "" = I
  | add_prefix mandatory prfx = map_prefix (cons (prfx, mandatory));

end;

type binding = Binding.binding;


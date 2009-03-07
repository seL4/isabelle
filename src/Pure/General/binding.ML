(*  Title:      Pure/General/binding.ML
    Author:     Florian Haftmann, TU Muenchen
    Author:     Makarius

Structured name bindings.
*)

type bstring = string;    (*primitive names to be bound*)

signature BINDING =
sig
  type binding
  val dest: binding -> (string * bool) list * bstring
  val str_of: binding -> string
  val make: bstring * Position.T -> binding
  val pos_of: binding -> Position.T
  val name: bstring -> binding
  val name_of: binding -> string
  val map_name: (bstring -> bstring) -> binding -> binding
  val prefix_name: string -> binding -> binding
  val suffix_name: string -> binding -> binding
  val eq_name: binding * binding -> bool
  val empty: binding
  val is_empty: binding -> bool
  val qualify: bool -> string -> binding -> binding
  val prefix_of: binding -> (string * bool) list
  val map_prefix: ((string * bool) list -> (string * bool) list) -> binding -> binding
  val prefix: bool -> string -> binding -> binding
end;

structure Binding:> BINDING =
struct

(** representation **)

(* datatype *)

datatype binding = Binding of
 {prefix: (string * bool) list,     (*system prefix*)
  qualifier: (string * bool) list,  (*user qualifier*)
  name: bstring,                    (*base name*)
  pos: Position.T};                 (*source position*)

fun make_binding (prefix, qualifier, name, pos) =
  Binding {prefix = prefix, qualifier = qualifier, name = name, pos = pos};

fun map_binding f (Binding {prefix, qualifier, name, pos}) =
  make_binding (f (prefix, qualifier, name, pos));

fun dest (Binding {prefix, qualifier, name, ...}) = (prefix @ qualifier, name);

fun str_of (Binding {prefix, qualifier, name, pos}) =
  let
    val text = space_implode "." (map #1 qualifier @ [name]);
    val props = Position.properties_of pos;
  in Markup.markup (Markup.properties props (Markup.binding name)) text end;



(** basic operations **)

(* name and position *)

fun make (name, pos) = make_binding ([], [], name, pos);
fun name name = make (name, Position.none);

fun pos_of (Binding {pos, ...}) = pos;
fun name_of (Binding {name, ...}) = name;

fun eq_name (b, b') = name_of b = name_of b';

fun map_name f = map_binding (fn (prefix, qualifier, name, pos) => (prefix, qualifier, f name, pos));
val prefix_name = map_name o prefix;
val suffix_name = map_name o suffix;

val empty = name "";
fun is_empty b = name_of b = "";


(* user qualifier *)

fun qualify _ "" = I
  | qualify strict qual = map_binding (fn (prefix, qualifier, name, pos) =>
      (prefix, (qual, strict) :: qualifier, name, pos));


(* system prefix *)

fun prefix_of (Binding {prefix, ...}) = prefix;

fun map_prefix f = map_binding (fn (prefix, qualifier, name, pos) =>
  (f prefix, qualifier, name, pos));

fun prefix _ "" = I
  | prefix strict prfx = map_prefix (cons (prfx, strict));

end;

type binding = Binding.binding;


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
  val make: bstring * Position.T -> binding
  val pos_of: binding -> Position.T
  val name: bstring -> binding
  val name_of: binding -> bstring
  val map_name: (bstring -> bstring) -> binding -> binding
  val prefix_name: string -> binding -> binding
  val suffix_name: string -> binding -> binding
  val eq_name: binding * binding -> bool
  val empty: binding
  val is_empty: binding -> bool
  val qualify: bool -> string -> binding -> binding
  val qualified_name: string -> binding
  val qualified_name_of: binding -> string
  val prefix_of: binding -> (string * bool) list
  val map_prefix: ((string * bool) list -> (string * bool) list) -> binding -> binding
  val prefix: bool -> string -> binding -> binding
  val str_of: binding -> string
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
  | qualify mandatory qual = map_binding (fn (prefix, qualifier, name, pos) =>
      (prefix, (qual, mandatory) :: qualifier, name, pos));

fun qualified_name "" = empty
  | qualified_name s =
      let val (qualifier, name) = split_last (Long_Name.explode s)
      in make_binding ([], map (rpair false) qualifier, name, Position.none) end;

fun qualified_name_of (Binding {qualifier, name, ...}) =
  Long_Name.implode (map #1 qualifier @ [name]);


(* system prefix *)

fun prefix_of (Binding {prefix, ...}) = prefix;

fun map_prefix f = map_binding (fn (prefix, qualifier, name, pos) =>
  (f prefix, qualifier, name, pos));

fun prefix _ "" = I
  | prefix mandatory prfx = map_prefix (cons (prfx, mandatory));


(* str_of *)

fun str_of binding =
  let
    val text = qualified_name_of binding;
    val props = Position.properties_of (pos_of binding);
  in Markup.markup (Markup.properties props (Markup.binding (name_of binding))) text end;

end;

type binding = Binding.binding;


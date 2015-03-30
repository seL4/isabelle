(*  Title:      Pure/General/binding.ML
    Author:     Florian Haftmann, TU Muenchen
    Author:     Makarius

Structured name bindings.
*)

type bstring = string;    (*primitive names to be bound*)

signature BINDING =
sig
  eqtype binding
  val dest: binding -> {private: bool, concealed: bool, path: (string * bool) list, name: bstring}
  val path_of: binding -> (string * bool) list
  val make: bstring * Position.T -> binding
  val pos_of: binding -> Position.T
  val set_pos: Position.T -> binding -> binding
  val name: bstring -> binding
  val name_of: binding -> bstring
  val map_name: (bstring -> bstring) -> binding -> binding
  val prefix_name: string -> binding -> binding
  val suffix_name: string -> binding -> binding
  val eq_name: binding * binding -> bool
  val empty: binding
  val is_empty: binding -> bool
  val qualify: bool -> string -> binding -> binding
  val qualified: bool -> string -> binding -> binding
  val qualified_name: string -> binding
  val prefix_of: binding -> (string * bool) list
  val map_prefix: ((string * bool) list -> (string * bool) list) -> binding -> binding
  val prefix: bool -> string -> binding -> binding
  val private: binding -> binding
  val concealed: binding -> binding
  val pretty: binding -> Pretty.T
  val print: binding -> string
  val pp: binding -> Pretty.T
  val bad: binding -> string
  val check: binding -> unit
end;

structure Binding: BINDING =
struct

(** representation **)

(* datatype *)

datatype binding = Binding of
 {private: bool,                    (*entry is strictly private -- no name space accesses*)
  concealed: bool,                  (*entry is for foundational purposes -- please ignore*)
  prefix: (string * bool) list,     (*system prefix*)
  qualifier: (string * bool) list,  (*user qualifier*)
  name: bstring,                    (*base name*)
  pos: Position.T};                 (*source position*)

fun make_binding (private, concealed, prefix, qualifier, name, pos) =
  Binding {private = private, concealed = concealed, prefix = prefix,
    qualifier = qualifier, name = name, pos = pos};

fun map_binding f (Binding {private, concealed, prefix, qualifier, name, pos}) =
  make_binding (f (private, concealed, prefix, qualifier, name, pos));

fun dest (Binding {private, concealed, prefix, qualifier, name, ...}) =
  {private = private, concealed = concealed, path = prefix @ qualifier, name = name};

val path_of = #path o dest;



(** basic operations **)

(* name and position *)

fun make (name, pos) = make_binding (false, false, [], [], name, pos);

fun pos_of (Binding {pos, ...}) = pos;
fun set_pos pos =
  map_binding (fn (private, concealed, prefix, qualifier, name, _) =>
    (private, concealed, prefix, qualifier, name, pos));

fun name name = make (name, Position.none);
fun name_of (Binding {name, ...}) = name;

fun eq_name (b, b') = name_of b = name_of b';

fun map_name f =
  map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
    (private, concealed, prefix, qualifier, f name, pos));

val prefix_name = map_name o prefix;
val suffix_name = map_name o suffix;

val empty = name "";
fun is_empty b = name_of b = "";


(* user qualifier *)

fun qualify _ "" = I
  | qualify mandatory qual =
      map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
        (private, concealed, prefix, (qual, mandatory) :: qualifier, name, pos));

fun qualified mandatory name' =
  map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
    let val qualifier' = if name = "" then qualifier else qualifier @ [(name, mandatory)]
    in (private, concealed, prefix, qualifier', name', pos) end);

fun qualified_name "" = empty
  | qualified_name s =
      let val (qualifier, name) = split_last (Long_Name.explode s)
      in make_binding (false, false, [], map (rpair false) qualifier, name, Position.none) end;


(* system prefix *)

fun prefix_of (Binding {prefix, ...}) = prefix;

fun map_prefix f =
  map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
    (private, concealed, f prefix, qualifier, name, pos));

fun prefix _ "" = I
  | prefix mandatory prfx = map_prefix (cons (prfx, mandatory));


(* visibility flags *)

val private =
  map_binding (fn (_, concealed, prefix, qualifier, name, pos) =>
    (true, concealed, prefix, qualifier, name, pos));

val concealed =
  map_binding (fn (private, _, prefix, qualifier, name, pos) =>
    (private, true, prefix, qualifier, name, pos));


(* print *)

fun pretty (Binding {prefix, qualifier, name, pos, ...}) =
  if name = "" then Pretty.str "\"\""
  else
    Pretty.markup (Position.markup pos Markup.binding)
      [Pretty.str (Long_Name.implode (map #1 (prefix @ qualifier) @ [name]))]
    |> Pretty.quote;

val print = Pretty.str_of o pretty;

val pp = pretty o set_pos Position.none;


(* check *)

fun bad binding = "Bad name binding: " ^ print binding ^ Position.here (pos_of binding);

fun check binding =
  if Symbol_Pos.is_identifier (name_of binding) then ()
  else legacy_feature (bad binding);

end;

type binding = Binding.binding;

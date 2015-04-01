(*  Title:      Pure/General/binding.ML
    Author:     Florian Haftmann, TU Muenchen
    Author:     Makarius

Structured name bindings.
*)

type bstring = string;    (*primitive names to be bound*)

signature BINDING =
sig
  eqtype scope
  val new_scope: unit -> scope
  eqtype binding
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
  val private: scope -> binding -> binding
  val private_default: scope option -> binding -> binding
  val concealed: binding -> binding
  val pretty: binding -> Pretty.T
  val print: binding -> string
  val pp: binding -> Pretty.T
  val bad: binding -> string
  val check: binding -> unit
  val name_spec: scope list -> (string * bool) list -> binding ->
    {accessible: bool, concealed: bool, spec: (string * bool) list}
end;

structure Binding: BINDING =
struct

(** representation **)

(* scope of private entries *)

datatype scope = Scope of serial;

fun new_scope () = Scope (serial ());


(* binding *)

datatype binding = Binding of
 {private: scope option,            (*entry is strictly private within its scope*)
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

fun path_of (Binding {prefix, qualifier, ...}) = prefix @ qualifier;



(** basic operations **)

(* name and position *)

fun make (name, pos) = make_binding (NONE, false, [], [], name, pos);

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
      in make_binding (NONE, false, [], map (rpair false) qualifier, name, Position.none) end;


(* system prefix *)

fun prefix_of (Binding {prefix, ...}) = prefix;

fun map_prefix f =
  map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
    (private, concealed, f prefix, qualifier, name, pos));

fun prefix _ "" = I
  | prefix mandatory prfx = map_prefix (cons (prfx, mandatory));


(* visibility flags *)

fun private scope =
  map_binding (fn (_, concealed, prefix, qualifier, name, pos) =>
    (SOME scope, concealed, prefix, qualifier, name, pos));

fun private_default private' =
  map_binding (fn (private, concealed, prefix, qualifier, name, pos) =>
    (if is_some private then private else private', concealed, prefix, qualifier, name, pos));

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



(** resulting name_spec **)

val bad_specs = ["", "??", "__"];

fun name_spec scopes path binding =
  let
    val Binding {private, concealed, prefix, qualifier, name, ...} = binding;
    val _ = Long_Name.is_qualified name andalso error (bad binding);

    val accessible =
      (case private of
        NONE => true
      | SOME scope => member (op =) scopes scope);

    val spec1 =
      maps (fn (a, b) => map (rpair b) (Long_Name.explode a)) (path @ prefix @ qualifier);
    val spec2 = if name = "" then [] else [(name, true)];
    val spec = spec1 @ spec2;
    val _ =
      exists (fn (a, _) => member (op =) bad_specs a orelse exists_string (fn s => s = "\"") a) spec
      andalso error (bad binding);
  in {accessible = accessible, concealed = concealed, spec = if null spec2 then [] else spec} end;

end;

type binding = Binding.binding;

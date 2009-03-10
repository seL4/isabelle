(*  Title:      Pure/General/name_space.ML
    Author:     Markus Wenzel, TU Muenchen

Generic name spaces with declared and hidden entries.  Unknown names
are considered global; no support for absolute addressing.
*)

type xstring = string;    (*external names*)

signature BASIC_NAME_SPACE =
sig
  val long_names: bool ref
  val short_names: bool ref
  val unique_names: bool ref
end;

signature NAME_SPACE =
sig
  include BASIC_NAME_SPACE
  val hidden: string -> string
  val is_hidden: string -> bool
  type T
  val empty: T
  val intern: T -> xstring -> string
  val extern: T -> string -> xstring
  val extern_flags: {long_names: bool, short_names: bool, unique_names: bool} ->
    T -> string -> xstring
  val hide: bool -> string -> T -> T
  val merge: T * T -> T
  type naming
  val default_naming: naming
  val declare: naming -> binding -> T -> string * T
  val full_name: naming -> binding -> string
  val external_names: naming -> string -> string list
  val add_path: string -> naming -> naming
  val no_base_names: naming -> naming
  val qualified_names: naming -> naming
  val sticky_prefix: string -> naming -> naming
  type 'a table = T * 'a Symtab.table
  val bind: naming -> binding * 'a -> 'a table -> string * 'a table       (*exception Symtab.DUP*)
  val empty_table: 'a table
  val merge_tables: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table  (*exception Symtab.DUP*)
  val join_tables: (string -> 'a * 'a -> 'a) (*exception Symtab.DUP/Symtab.SAME*) ->
    'a table * 'a table -> 'a table                                       (*exception Symtab.DUP*)
  val dest_table: 'a table -> (string * 'a) list
  val extern_table: 'a table -> (xstring * 'a) list
end;

structure NameSpace: NAME_SPACE =
struct


(** name spaces **)

(* hidden entries *)

fun hidden name = "??." ^ name;
val is_hidden = String.isPrefix "??.";


(* datatype T *)

datatype T =
  NameSpace of
    (string list * string list) Symtab.table *   (*internals, hidden internals*)
    xstring list Symtab.table;                   (*externals*)

val empty = NameSpace (Symtab.empty, Symtab.empty);

fun lookup (NameSpace (tab, _)) xname =
  (case Symtab.lookup tab xname of
    NONE => (xname, true)
  | SOME ([], []) => (xname, true)
  | SOME ([name], _) => (name, true)
  | SOME (name :: _, _) => (name, false)
  | SOME ([], name' :: _) => (hidden name', true));

fun get_accesses (NameSpace (_, xtab)) name =
  (case Symtab.lookup xtab name of
    NONE => [name]
  | SOME xnames => xnames);

fun put_accesses name xnames (NameSpace (tab, xtab)) =
  NameSpace (tab, Symtab.update (name, xnames) xtab);

fun valid_accesses (NameSpace (tab, _)) name = Symtab.fold (fn (xname, (names, _)) =>
  if not (null names) andalso hd names = name then cons xname else I) tab [];


(* intern and extern *)

fun intern space xname = #1 (lookup space xname);

fun extern_flags {long_names, short_names, unique_names} space name =
  let
    fun valid require_unique xname =
      let val (name', is_unique) = lookup space xname
      in name = name' andalso (not require_unique orelse is_unique) end;

    fun ext [] = if valid false name then name else hidden name
      | ext (nm :: nms) = if valid unique_names nm then nm else ext nms;
  in
    if long_names then name
    else if short_names then Long_Name.base_name name
    else ext (get_accesses space name)
  end;

val long_names = ref false;
val short_names = ref false;
val unique_names = ref true;

fun extern space name =
  extern_flags
   {long_names = ! long_names,
    short_names = ! short_names,
    unique_names = ! unique_names} space name;


(* basic operations *)

local

fun map_space f xname (NameSpace (tab, xtab)) =
  NameSpace (Symtab.map_default (xname, ([], [])) f tab, xtab);

in

val del_name = map_space o apfst o remove (op =);
fun del_name_extra name = map_space (apfst (fn [] => [] | x :: xs => x :: remove (op =) name xs));
val add_name = map_space o apfst o update (op =);
val add_name' = map_space o apsnd o update (op =);

end;


(* hide *)

fun hide fully name space =
  if not (Long_Name.is_qualified name) then
    error ("Attempt to hide global name " ^ quote name)
  else if is_hidden name then
    error ("Attempt to hide hidden name " ^ quote name)
  else
    let val names = valid_accesses space name in
      space
      |> add_name' name name
      |> fold (del_name name)
        (if fully then names else names inter_string [Long_Name.base_name name])
      |> fold (del_name_extra name) (get_accesses space name)
    end;


(* merge *)

fun merge (NameSpace (tab1, xtab1), NameSpace (tab2, xtab2)) =
  let
    val tab' = (tab1, tab2) |> Symtab.join
      (K (fn names as ((names1, names1'), (names2, names2')) =>
        if pointer_eq names then raise Symtab.SAME
        else (Library.merge (op =) (names1, names2), Library.merge (op =) (names1', names2'))));
    val xtab' = (xtab1, xtab2) |> Symtab.join
      (K (fn xnames =>
        if pointer_eq xnames then raise Symtab.SAME
        else (Library.merge (op =) xnames)));
  in NameSpace (tab', xtab') end;



(** naming contexts **)

(* datatype naming *)

datatype naming = Naming of
 {path: (string * bool) list,
  no_base_names: bool,
  qualified_names: bool};

fun make_naming (path, no_base_names, qualified_names) =
  Naming {path = path, no_base_names = no_base_names, qualified_names = qualified_names};

fun map_naming f (Naming {path, no_base_names, qualified_names}) =
  make_naming (f (path, no_base_names, qualified_names));

fun path_of (Naming {path, ...}) = path;


(* configure naming *)

val default_naming = make_naming ([], false, false);

fun add_path elems = map_naming (fn (path, no_base_names, qualified_names) =>
  if elems = "//" then ([], no_base_names, true)
  else if elems = "/" then ([], no_base_names, qualified_names)
  else if elems = ".." then (perhaps (try (#1 o split_last)) path, no_base_names, qualified_names)
  else (path @ map (rpair false) (Long_Name.explode elems), no_base_names, qualified_names));

fun sticky_prefix elems = map_naming (fn (path, no_base_names, qualified_names) =>
  (path @ map (rpair true) (Long_Name.explode elems), no_base_names, qualified_names));

val no_base_names = map_naming (fn (path, _, qualified_names) => (path, true, qualified_names));
val qualified_names = map_naming (fn (path, no_base_names, _) => (path, no_base_names, true));


(* full name *)

fun err_bad binding = error ("Bad name declaration " ^ quote (Binding.str_of binding));

fun name_spec (Naming {path, qualified_names, ...}) binding =
  let
    val (prefix, name) = Binding.dest binding;
    val _ = not qualified_names andalso Long_Name.is_qualified name andalso err_bad binding;

    val spec1 = maps (fn (a, b) => map (rpair b) (Long_Name.explode a)) (path @ prefix);
    val spec2 =
      (case try split_last (Long_Name.explode name) of
        NONE => []
      | SOME (qual, base) => map (rpair false) qual @ [(base, true)]);

    val spec = spec1 @ spec2;
    val _ =
      exists (fn (a, _) => a = "" orelse a = "??" orelse exists_string (fn s => s = "\"") a) spec
      andalso err_bad binding;
  in if null spec2 then [] else spec end;

fun full naming = name_spec naming #> map fst;
fun full_name naming = full naming #> Long_Name.implode;


(* accesses *)

fun mandatory xs = map_filter (fn (x, true) => SOME x | _ => NONE) xs;

fun mandatory_prefixes xs = mandatory xs :: mandatory_prefixes1 xs
and mandatory_prefixes1 [] = []
  | mandatory_prefixes1 ((x, true) :: xs) = map (cons x) (mandatory_prefixes1 xs)
  | mandatory_prefixes1 ((x, false) :: xs) = map (cons x) (mandatory_prefixes xs);

fun mandatory_suffixes1 xs = map rev (mandatory_prefixes1 (rev xs));
fun mandatory_suffixes xs = map rev (mandatory_prefixes (rev xs));

fun accesses (naming as Naming {no_base_names, ...}) binding =
  let
    val spec = name_spec naming binding;
    val sfxs = mandatory_suffixes spec;
    val pfxs = mandatory_prefixes spec;
  in
    (sfxs @ pfxs, sfxs)
    |> pairself (no_base_names ? filter (fn [_] => false | _ => true))
    |> pairself (map Long_Name.implode)
  end;

fun external_names naming = #2 o accesses naming o Binding.qualified_name;


(* declaration *)

fun declare naming binding space =
  let
    val names = full naming binding;
    val name = Long_Name.implode names;
    val _ = name = "" andalso err_bad binding;
    val (accs, accs') = accesses naming binding;
    val space' = space |> fold (add_name name) accs |> put_accesses name accs';
  in (name, space') end;



(** name spaces coupled with symbol tables **)

type 'a table = T * 'a Symtab.table;

fun bind naming (binding, x) (space, tab) =
  let val (name, space') = declare naming binding space
  in (name, (space', Symtab.update_new (name, x) tab)) end;

val empty_table = (empty, Symtab.empty);

fun merge_tables eq ((space1, tab1), (space2, tab2)) =
  (merge (space1, space2), Symtab.merge eq (tab1, tab2));

fun join_tables f ((space1, tab1), (space2, tab2)) =
  (merge (space1, space2), Symtab.join f (tab1, tab2));

fun ext_table (space, tab) =
  Symtab.fold (fn (name, x) => cons ((name, extern space name), x)) tab []
  |> Library.sort_wrt (#2 o #1);

fun dest_table tab = map (apfst #1) (ext_table tab);
fun extern_table tab = map (apfst #2) (ext_table tab);

end;

structure BasicNameSpace: BASIC_NAME_SPACE = NameSpace;
open BasicNameSpace;


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
  val separator: string                 (*single char*)
  val is_qualified: string -> bool
  val implode: string list -> string
  val explode: string -> string list
  val append: string -> string -> string
  val qualified: string -> string -> string
  val base: string -> string
  val qualifier: string -> string
  val map_base: (string -> string) -> string -> string
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
  val path_of: naming -> string
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

(** long identifiers **)

fun hidden name = "??." ^ name;
val is_hidden = String.isPrefix "??.";

val separator = ".";
val is_qualified = exists_string (fn s => s = separator);

val implode_name = space_implode separator;
val explode_name = space_explode separator;

fun append name1 "" = name1
  | append "" name2 = name2
  | append name1 name2 = name1 ^ separator ^ name2;

fun qualified path name =
  if path = "" orelse name = "" then name
  else path ^ separator ^ name;

fun base "" = ""
  | base name = List.last (explode_name name);

fun qualifier "" = ""
  | qualifier name = implode_name (#1 (split_last (explode_name name)));

fun map_base _ "" = ""
  | map_base f name =
      let val names = explode_name name
      in implode_name (nth_map (length names - 1) f names) end;


(* standard accesses *)

infixr 6 @@;
fun ([] @@ yss) = []
  | ((xs :: xss) @@ yss) = map (fn ys => xs @ ys) yss @ (xss @@ yss);

fun suffixes_prefixes list =
  let
    val (xs, ws) = chop (length list - 1) list;
    val sfxs = suffixes xs @@ [ws];
    val pfxs = prefixes1 xs @@ [ws];
  in (sfxs @ pfxs, sfxs) end;

fun suffixes_prefixes_split i k list =
  let
    val (((xs, ys), zs), ws) = list |> chop i ||>> chop k ||>> chop (length list - (i + k + 1));
    val sfxs =
      [ys] @@ suffixes zs @@ [ws] @
      suffixes1 xs @@ [ys @ zs @ ws];
    val pfxs =
      prefixes1 xs @@ [ys @ ws] @
      [xs @ ys] @@ prefixes1 zs @@ [ws];
  in (sfxs @ pfxs, sfxs) end;



(** name spaces **)

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
    else if short_names then base name
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
  if not (is_qualified name) then
    error ("Attempt to hide global name " ^ quote name)
  else if is_hidden name then
    error ("Attempt to hide hidden name " ^ quote name)
  else
    let val names = valid_accesses space name in
      space
      |> add_name' name name
      |> fold (del_name name) (if fully then names else names inter_string [base name])
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
  string *                                                 (*path*)
  ((string -> string -> string) *                          (*qualify*)
   (string list -> string list list * string list list));  (*accesses*)

fun path_of (Naming (path, _)) = path;
fun accesses (Naming (_, (_, accs))) = accs;

fun external_names naming = map implode_name o #2 o accesses naming o explode_name;


(* manipulate namings *)

fun reject_qualified name =
  if is_qualified name then
    error ("Attempt to declare qualified name " ^ quote name)
  else name;

val default_naming =
  Naming ("", (fn path => qualified path o reject_qualified, suffixes_prefixes));

fun add_path elems (Naming (path, policy)) =
  if elems = "//" then Naming ("", (qualified, #2 policy))
  else if elems = "/" then Naming ("", policy)
  else if elems = ".." then Naming (qualifier path, policy)
  else Naming (append path elems, policy);

fun no_base_names (Naming (path, (qualify, accs))) =
  Naming (path, (qualify, pairself (filter_out (fn [_] => true | _ => false)) o accs));

fun qualified_names (Naming (path, (_, accs))) = Naming (path, (qualified, accs));

fun sticky_prefix prfx (Naming (path, (qualify, _))) =
  Naming (append path prfx,
    (qualify, suffixes_prefixes_split (length (explode_name path)) (length (explode_name prfx))));

val apply_prefix =
  let
    fun mk_prefix (prfx, true) = sticky_prefix prfx
      | mk_prefix (prfx, false) = add_path prfx;
  in fold mk_prefix end;


(* full name *)

fun full (Naming (path, (qualify, _))) = qualify path;

fun full_name naming binding =
  let
    val (prfx, bname) = Binding.dest binding;
    val naming' = apply_prefix prfx naming;
  in full naming' bname end;


(* declaration *)

fun declare naming binding space =
  let
    val (prfx, bname) = Binding.dest binding;
    val naming' = apply_prefix prfx naming;
    val name = full naming' bname;
    val names = explode_name name;

    val _ = (null names orelse exists (fn s => s = "" orelse s = "??") names
        orelse exists_string (fn s => s = "\"") name) andalso
      error ("Bad name declaration " ^ quote (Binding.str_of binding));

    val (accs, accs') = pairself (map implode_name) (accesses naming' names);
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


(*final declarations of this structure!*)
val implode = implode_name;
val explode = explode_name;

end;

structure BasicNameSpace: BASIC_NAME_SPACE = NameSpace;
open BasicNameSpace;


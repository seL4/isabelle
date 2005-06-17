(*  Title:      Pure/General/name_space.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic name spaces with declared and hidden entries.  Unknown names
are considered global; no support for absolute addressing.
*)

type bstring = string;    (*names to be bound / internalized*)
type xstring = string;    (*externalized names / to be printed*)

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
  val separator: string                 (*single char*)
  val is_qualified: string -> bool
  val pack: string list -> string
  val unpack: string -> string list
  val append: string -> string -> string
  val qualified: string -> string -> string
  val base: string -> string
  val drop_base: string -> string
  val map_base: (string -> string) -> string -> string
  val suffixes_prefixes: 'a list -> 'a list list
  val accesses: string -> string list
  val accesses': string -> string list
  type T
  val empty: T
  val valid_accesses: T -> string -> xstring list
  val intern: T -> xstring -> string
  val extern: T -> string -> xstring
  val hide: bool -> string -> T -> T
  val merge: T * T -> T
  val dest: T -> (string * xstring list) list
  type naming
  val path_of: naming -> string
  val full: naming -> bstring -> string
  val declare: naming -> string -> T -> T
  val default_naming: naming
  val add_path: string -> naming -> naming
  val qualified_names: naming -> naming
  val no_base_names: naming -> naming
  val custom_accesses: (string list -> string list list) -> naming -> naming
  val set_policy: (string -> bstring -> string) * (string list -> string list list) ->
    naming -> naming
  type 'a table = T * 'a Symtab.table
  val empty_table: 'a table
  val extend_table: naming -> 'a table * (bstring * 'a) list -> 'a table
  val merge_tables: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table
  val extern_table: 'a table -> (xstring * 'a) list
end;

structure NameSpace: NAME_SPACE =
struct

(** long identifiers **)

fun hidden name = "??." ^ name;
val is_hidden = String.isPrefix "??."

val separator = ".";
val is_qualified = exists_string (equal separator);

val pack = space_implode separator;
val unpack = space_explode separator;

fun append name1 "" = name1
  | append "" name2 = name2
  | append name1 name2 = name1 ^ separator ^ name2;

fun qualified path name =
  if path = "" orelse name = "" then name
  else path ^ separator ^ name;

fun base "" = ""
  | base name = List.last (unpack name);

fun drop_base "" = ""
  | drop_base name = pack (#1 (split_last (unpack name)));

fun map_base _ "" = ""
  | map_base f name =
      let val names = unpack name
      in pack (map_nth_elem (length names - 1) f names) end;

fun suffixes_prefixes xs =
  let
    val (qs, b) = split_last xs;
    val sfxs = Library.suffixes1 xs;
    val pfxs = map (fn x => x @ [b]) (Library.prefixes1 qs);
  in sfxs @ pfxs end;

val accesses = map pack o suffixes_prefixes o unpack;
val accesses' = map pack o Library.suffixes1 o unpack;



(** name spaces **)

(* datatype T *)

datatype T =
  NameSpace of (string list * string list) Symtab.table;

val empty = NameSpace Symtab.empty;

fun lookup (NameSpace tab) xname =
  (case Symtab.lookup (tab, xname) of
    NONE => (xname, true)
  | SOME ([], []) => (xname, true)
  | SOME ([name], _) => (name, true)
  | SOME (name :: _, _) => (name, false)
  | SOME ([], name' :: _) => (hidden name', true));

fun valid_accesses (NameSpace tab) name = Symtab.fold (fn (xname, (names, _)) =>
  if not (null names) andalso hd names = name then cons xname else I) tab [];


(* intern and extern *)

fun intern space xname = #1 (lookup space xname);

val long_names = ref false;
val short_names = ref false;
val unique_names = ref true;

fun extern space name =
  let
    fun valid unique xname =
      let val (name', uniq) = lookup space xname
      in name = name' andalso (uniq orelse (not unique)) end;

    fun ex [] = if valid false name then name else hidden name
      | ex (nm :: nms) = if valid (! unique_names) nm then nm else ex nms;
  in
    if ! long_names then name
    else if ! short_names then base name
    else ex (accesses' name)
  end;


(* basic operations *)

fun map_space f xname (NameSpace tab) =
  NameSpace (Symtab.update ((xname, f (if_none (Symtab.lookup (tab, xname)) ([], []))), tab));

fun del (name: string) = remove (op =) name;
fun add name names = name :: del name names;

val del_name = map_space o apfst o del;
val add_name = map_space o apfst o add;
val add_name' = map_space o apsnd o add;


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
    end;


(* merge *)

fun merge (NameSpace tab1, space2) = Symtab.fold (fn (xname, (names1, names1')) =>
  xname |> map_space (fn (names2, names2') =>
    (merge_lists' names2 names1, merge_lists' names2' names1'))) tab1 space2;


(* dest *)

fun dest_entry (xname, ([], _)) = NONE
  | dest_entry (xname, (name :: _, _)) = SOME (name, xname);

fun dest (NameSpace tab) =
  map (apsnd (sort (int_ord o pairself size)))
    (Symtab.dest (Symtab.make_multi (List.mapPartial dest_entry (Symtab.dest tab))));



(** naming contexts **)

(* datatype naming *)

datatype naming = Naming of
  string * ((string -> string -> string) * (string list -> string list list));

fun path_of (Naming (path, _)) = path;


(* declarations *)

fun full (Naming (path, (qualify, _))) = qualify path;

fun declare (Naming (_, (_, accs))) name space =
  if is_hidden name then
    error ("Attempt to declare hidden name " ^ quote name)
  else
    let val names = unpack name in
      conditional (null names orelse exists (equal "") names) (fn () =>
        error ("Bad name declaration " ^ quote name));
      fold (add_name name) (map pack (accs names)) space
    end;


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
  else if elems = ".." then Naming (drop_base path, policy)
  else Naming (append path elems, policy);

fun qualified_names (Naming (path, (_, accs))) = Naming (path, (qualified, accs));

fun no_base_names (Naming (path, (qualify, accs))) =
  Naming (path, (qualify, filter_out (fn [_] => true | _ => false) o accs));

fun custom_accesses accs (Naming (path, (qualify, _))) = Naming (path, (qualify, accs));
fun set_policy policy (Naming (path, _)) = Naming (path, policy);



(** name spaces coupled with symbol tables **)

type 'a table = T * 'a Symtab.table;

val empty_table = (empty, Symtab.empty);

fun extend_table naming ((space, tab), bentries) =
  let val entries = map (apfst (full naming)) bentries
  in (fold (declare naming o #1) entries space, Symtab.extend (tab, entries)) end;

fun merge_tables eq ((space1, tab1), (space2, tab2)) =
  (merge (space1, space2), (Symtab.merge eq (tab1, tab2)));

fun extern_table (space, tab) =
  Library.sort_wrt #1 (map (apfst (extern space)) (Symtab.dest tab));

end;

structure BasicNameSpace: BASIC_NAME_SPACE = NameSpace;
open BasicNameSpace;

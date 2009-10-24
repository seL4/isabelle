(*  Title:      Pure/General/name_space.ML
    Author:     Markus Wenzel, TU Muenchen

Generic name spaces with declared and hidden entries.  Unknown names
are considered global; no support for absolute addressing.
*)

type xstring = string;    (*external names*)

signature BASIC_NAME_SPACE =
sig
  val long_names: bool Unsynchronized.ref
  val short_names: bool Unsynchronized.ref
  val unique_names: bool Unsynchronized.ref
end;

signature NAME_SPACE =
sig
  include BASIC_NAME_SPACE
  val hidden: string -> string
  val is_hidden: string -> bool
  type T
  val empty: string -> T
  val kind_of: T -> string
  val the_entry: T -> string -> {is_system: bool, pos: Position.T, id: serial}
  val intern: T -> xstring -> string
  val extern: T -> string -> xstring
  val extern_flags: {long_names: bool, short_names: bool, unique_names: bool} ->
    T -> string -> xstring
  val hide: bool -> string -> T -> T
  val merge: T * T -> T
  type naming
  val default_naming: naming
  val declare: bool -> naming -> binding -> T -> string * T
  val full_name: naming -> binding -> string
  val external_names: naming -> string -> string list
  val add_path: string -> naming -> naming
  val root_path: naming -> naming
  val parent_path: naming -> naming
  val mandatory_path: string -> naming -> naming
  type 'a table = T * 'a Symtab.table
  val define: bool -> naming -> binding * 'a -> 'a table -> string * 'a table
  val empty_table: string -> 'a table
  val merge_tables: 'a table * 'a table -> 'a table
  val join_tables:
    (string -> 'a * 'a -> 'a) (*Symtab.SAME*) -> 'a table * 'a table -> 'a table
  val dest_table: 'a table -> (string * 'a) list
  val extern_table: 'a table -> (xstring * 'a) list
end;

structure Name_Space: NAME_SPACE =
struct


(** name spaces **)

(* hidden entries *)

fun hidden name = "??." ^ name;
val is_hidden = String.isPrefix "??.";


(* datatype entry *)

type entry =
 {externals: xstring list,
  is_system: bool,
  pos: Position.T,
  id: serial};

fun str_of_entry def (name, {pos, id, ...}: entry) =
  let
    val occurrence = (if def then Markup.defN else Markup.refN, string_of_int id);
    val props = occurrence :: Position.properties_of pos;
  in Markup.markup (Markup.properties props (Markup.entity name)) name end;

fun err_dup kind entry1 entry2 =
  error ("Duplicate " ^ kind ^ " declaration " ^
    quote (str_of_entry true entry1) ^ " vs. " ^ quote (str_of_entry true entry2));


(* datatype T *)

datatype T =
  Name_Space of
   {kind: string,
    internals: (string list * string list) Symtab.table,  (*visible, hidden*)
    entries: entry Symtab.table};

fun make_name_space (kind, internals, entries) =
  Name_Space {kind = kind, internals = internals, entries = entries};

fun map_name_space f (Name_Space {kind = kind, internals = internals, entries = entries}) =
  make_name_space (f (kind, internals, entries));

fun map_internals f xname = map_name_space (fn (kind, internals, entries) =>
  (kind, Symtab.map_default (xname, ([], [])) f internals, entries));


fun empty kind = make_name_space (kind, Symtab.empty, Symtab.empty);

fun kind_of (Name_Space {kind, ...}) = kind;

fun the_entry (Name_Space {kind, entries, ...}) name =
  (case Symtab.lookup entries name of
    NONE => error ("Unknown " ^ kind ^ " " ^ quote name)
  | SOME {is_system, pos, id, ...} => {is_system = is_system, pos = pos, id = id});


(* name accesses *)

fun lookup (Name_Space {internals, ...}) xname =
  (case Symtab.lookup internals xname of
    NONE => (xname, true)
  | SOME ([], []) => (xname, true)
  | SOME ([name], _) => (name, true)
  | SOME (name :: _, _) => (name, false)
  | SOME ([], name' :: _) => (hidden name', true));

fun get_accesses (Name_Space {entries, ...}) name =
  (case Symtab.lookup entries name of
    NONE => [name]
  | SOME {externals, ...} => externals);

fun valid_accesses (Name_Space {internals, ...}) name =
  Symtab.fold (fn (xname, (names, _)) =>
    if not (null names) andalso hd names = name then cons xname else I) internals [];


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

val long_names = Unsynchronized.ref false;
val short_names = Unsynchronized.ref false;
val unique_names = Unsynchronized.ref true;

fun extern space name =
  extern_flags
   {long_names = ! long_names,
    short_names = ! short_names,
    unique_names = ! unique_names} space name;


(* modify internals *)

val del_name = map_internals o apfst o remove (op =);
fun del_name_extra name =
  map_internals (apfst (fn [] => [] | x :: xs => x :: remove (op =) name xs));
val add_name = map_internals o apfst o update (op =);
val add_name' = map_internals o apsnd o update (op =);


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
        (if fully then names else inter (op =) [Long_Name.base_name name] names)
      |> fold (del_name_extra name) (get_accesses space name)
    end;


(* merge *)

fun merge
  (Name_Space {kind = kind1, internals = internals1, entries = entries1},
    Name_Space {kind = kind2, internals = internals2, entries = entries2}) =
  let
    val kind' =
      if kind1 = kind2 then kind1
      else error ("Attempt to merge different kinds of name spaces " ^
        quote kind1 ^ " vs. " ^ quote kind2);
    val internals' = (internals1, internals2) |> Symtab.join
      (K (fn ((names1, names1'), (names2, names2')) =>
        if pointer_eq (names1, names2) andalso pointer_eq (names1', names2')
        then raise Symtab.SAME
        else (Library.merge (op =) (names1, names2), Library.merge (op =) (names1', names2'))));
    val entries' = (entries1, entries2) |> Symtab.join
      (fn name => fn (entry1, entry2) =>
        if #id entry1 = #id entry2 then raise Symtab.SAME
        else err_dup kind' (name, entry1) (name, entry2));
  in make_name_space (kind', internals', entries') end;



(** naming contexts **)

(* datatype naming *)

datatype naming = Naming of (string * bool) list;
fun map_naming f (Naming path) = Naming (f path);

val default_naming = Naming [];

fun add_path elems = map_naming (fn path => path @ [(elems, false)]);
val root_path = map_naming (fn _ => []);
val parent_path = map_naming (perhaps (try (#1 o split_last)));
fun mandatory_path elems = map_naming (fn path => path @ [(elems, true)]);


(* full name *)

fun err_bad binding = error ("Bad name binding " ^ quote (Binding.str_of binding));

fun name_spec (Naming path) binding =
  let
    val (prefix, name) = Binding.dest binding;
    val _ = Long_Name.is_qualified name andalso err_bad binding;

    val spec1 = maps (fn (a, b) => map (rpair b) (Long_Name.explode a)) (path @ prefix);
    val spec2 = if name = "" then [] else [(name, true)];
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

fun mandatory_suffixes xs = map rev (mandatory_prefixes (rev xs));

fun accesses naming binding =
  let
    val spec = name_spec naming binding;
    val sfxs = mandatory_suffixes spec;
    val pfxs = mandatory_prefixes spec;
  in pairself (map Long_Name.implode) (sfxs @ pfxs, sfxs) end;

fun external_names naming = #2 o accesses naming o Binding.qualified_name;


(* declaration *)

fun new_entry strict entry =
  map_name_space (fn (kind, internals, entries) =>
    let
      val entries' =
        (if strict then Symtab.update_new else Symtab.update) entry entries
          handle Symtab.DUP dup =>
            err_dup kind (dup, the (Symtab.lookup entries dup)) entry;
    in (kind, internals, entries') end);

fun declare strict naming binding space =
  let
    val names = full naming binding;
    val name = Long_Name.implode names;
    val _ = name = "" andalso err_bad binding;
    val (accs, accs') = accesses naming binding;
    val entry =
     {externals = accs',
      is_system = false,
      pos = Binding.pos_of binding,
      id = serial ()};
    val space' = space |> fold (add_name name) accs |> new_entry strict (name, entry);
  in (name, space') end;



(** name spaces coupled with symbol tables **)

type 'a table = T * 'a Symtab.table;

fun define strict naming (binding, x) (space, tab) =
  let val (name, space') = declare strict naming binding space
  in (name, (space', Symtab.update (name, x) tab)) end;

fun empty_table kind = (empty kind, Symtab.empty);

fun merge_tables ((space1, tab1), (space2, tab2)) =
  (merge (space1, space2), Symtab.merge (K true) (tab1, tab2));

fun join_tables f ((space1, tab1), (space2, tab2)) =
  (merge (space1, space2), Symtab.join f (tab1, tab2));

fun ext_table (space, tab) =
  Symtab.fold (fn (name, x) => cons ((name, extern space name), x)) tab []
  |> Library.sort_wrt (#2 o #1);

fun dest_table tab = map (apfst #1) (ext_table tab);
fun extern_table tab = map (apfst #2) (ext_table tab);

end;

structure Basic_Name_Space: BASIC_NAME_SPACE = Name_Space;
open Basic_Name_Space;


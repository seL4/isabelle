(*  Title:      Pure/General/name_space.ML
    Author:     Makarius

Generic name spaces with authentic declarations, hidden names and aliases.
*)

type xstring = string;    (*external names with partial qualification*)

signature NAME_SPACE =
sig
  type T
  val empty: string -> T
  val kind_of: T -> string
  val markup: T -> string -> Markup.T
  val markup_def: T -> string -> Markup.T
  val get_names: T -> string list
  val the_entry: T -> string ->
   {concealed: bool,
    suppress: bool list,
    group: serial,
    theory_long_name: string,
    pos: Position.T,
    serial: serial}
  val theory_name: {long: bool} -> T -> string -> string
  val entry_ord: T -> string ord
  val is_concealed: T -> string -> bool
  val intern: T -> xstring -> string
  val names_long: bool Config.T
  val names_short: bool Config.T
  val names_unique: bool Config.T
  val extern: Proof.context -> T -> string -> xstring
  val extern_ord: Proof.context -> T -> string ord
  val extern_shortest: Proof.context -> T -> string -> xstring
  val markup_extern: Proof.context -> T -> string -> Markup.T * xstring
  val pretty: Proof.context -> T -> string -> Pretty.T
  val completion: Context.generic -> T -> (string -> bool) -> xstring * Position.T -> Completion.T
  val merge: T * T -> T
  type naming
  val get_scopes: naming -> Binding.scope list
  val get_scope: naming -> Binding.scope option
  val new_scope: naming -> Binding.scope * naming
  val restricted: bool -> Position.T -> naming -> naming
  val private_scope: Binding.scope -> naming -> naming
  val private: Position.T -> naming -> naming
  val qualified_scope: Binding.scope -> naming -> naming
  val qualified: Position.T -> naming -> naming
  val concealed: naming -> naming
  val get_group: naming -> serial option
  val set_group: serial option -> naming -> naming
  val set_theory_long_name: string -> naming -> naming
  val new_group: naming -> naming
  val reset_group: naming -> naming
  val add_path: string -> naming -> naming
  val root_path: naming -> naming
  val parent_path: naming -> naming
  val mandatory_path: string -> naming -> naming
  val qualified_path: bool -> binding -> naming -> naming
  val global_naming: naming
  val local_naming: naming
  val transform_naming: naming -> naming -> naming
  val transform_binding: naming -> binding -> binding
  val full_name: naming -> binding -> string
  val base_name: binding -> string
  val hide: bool -> string -> T -> T
  val alias: naming -> binding -> string -> T -> T
  val naming_of: Context.generic -> naming
  val map_naming: (naming -> naming) -> Context.generic -> Context.generic
  val declared: T -> string -> bool
  val declare: Context.generic -> bool -> binding -> T -> string * T
  type 'a table
  val change_base: bool -> 'a table -> 'a table
  val change_ignore: 'a table -> 'a table
  val space_of_table: 'a table -> T
  val check_reports: Context.generic -> 'a table ->
    xstring * Position.T list -> (string * Position.report list) * 'a
  val check: Context.generic -> 'a table -> xstring * Position.T -> string * 'a
  val defined: 'a table -> string -> bool
  val lookup: 'a table -> string -> 'a option
  val lookup_key: 'a table -> string -> (string * 'a) option
  val get: 'a table -> string -> 'a
  val define: Context.generic -> bool -> binding * 'a -> 'a table -> string * 'a table
  val alias_table: naming -> binding -> string -> 'a table -> 'a table
  val hide_table: bool -> string -> 'a table -> 'a table
  val del_table: string -> 'a table -> 'a table
  val map_table_entry: string -> ('a -> 'a) -> 'a table -> 'a table
  val fold_table: (string * 'a -> 'b -> 'b) -> 'a table -> 'b -> 'b
  val dest_table: 'a table -> (string * 'a) list
  val empty_table: string -> 'a table
  val merge_tables: 'a table * 'a table -> 'a table
  val join_tables: (string -> 'a * 'a -> 'a) (*exception Change_Table.SAME*) ->
    'a table * 'a table -> 'a table
  val extern_entries: bool -> Proof.context -> T -> (string * 'a) list ->
    ((string * xstring) * 'a) list
  val markup_entries: bool -> Proof.context -> T -> (string * 'a) list ->
    ((Markup.T * xstring) * 'a) list
  val extern_table: bool -> Proof.context -> 'a table -> ((string * xstring) * 'a) list
  val markup_table: bool -> Proof.context -> 'a table -> ((Markup.T * xstring) * 'a) list
end;

structure Name_Space: NAME_SPACE =
struct


(** name spaces **)

(* datatype entry *)

type entry =
 {concealed: bool,
  suppress: bool list,
  group: serial,
  theory_long_name: string,
  pos: Position.T,
  serial: serial};

fun markup_entry def kind (name, entry: entry) =
  Position.make_entity_markup def (#serial entry) kind (name, #pos entry);

fun print_entry_ref kind (name, entry) =
  quote (Markup.markup (markup_entry {def = false} kind (name, entry)) name);

fun err_dup_entry kind entry1 entry2 pos =
  error ("Duplicate " ^ plain_words kind ^ " declaration " ^
    print_entry_ref kind entry1 ^ " vs. " ^ print_entry_ref kind entry2 ^ Position.here pos);

fun update_entry strict kind (name, entry: entry) entries =
  (if strict then Change_Table.update_new else Change_Table.update) (name, entry) entries
    handle Change_Table.DUP _ =>
      let val old_entry = the (Change_Table.lookup entries name)
      in err_dup_entry kind (name, old_entry) (name, entry) (#pos entry) end;


(* internal names *)

type internals = string list Long_Name.Chunks.T;  (*external name -> internal names*)

val merge_internals : internals * internals -> internals =
  Long_Name.Chunks.merge_list (op =);

fun add_internals name xname : internals -> internals =
  Long_Name.Chunks.update_list (op =) (xname, name);

fun del_internals name xname : internals -> internals =
  Long_Name.Chunks.remove_list (op =) (xname, name);

fun del_internals' name xname : internals -> internals =
  Long_Name.Chunks.map_default (xname, []) (fn [] => [] | x :: xs => x :: remove (op =) name xs);


(* accesses *)

local

fun suppress_prefixes1 [] = []
  | suppress_prefixes1 (s :: ss) =
      map (cons false) (if s then suppress_prefixes ss else suppress_prefixes1 ss)
and suppress_prefixes ss = ss :: suppress_prefixes1 ss;

fun suppress_suffixes ss = map rev (suppress_prefixes (rev ss));

fun make_chunks full_name m s =
  let val chunks = Long_Name.suppress_chunks 0 s full_name
  in if Long_Name.count_chunks chunks > m then SOME chunks else NONE end;

in

fun make_accesses {intern} restriction (suppress, full_name) =
  if restriction = SOME true then []
  else
    ((if intern then suppress_prefixes suppress else []) @ suppress_suffixes suppress)
    |> map_filter (make_chunks full_name (if is_some restriction then 1 else 0))
    |> distinct Long_Name.eq_chunks;

end;


(* datatype T *)

datatype T =
  Name_Space of
   {kind: string,
    internals: internals,
    internals_hidden: internals,
    entries: entry Change_Table.T,
    aliases: (bool list * string) list Symtab.table};

fun make_name_space (kind, internals, internals_hidden, entries, aliases) =
  Name_Space {kind = kind, internals = internals, internals_hidden = internals_hidden,
    entries = entries, aliases = aliases};

fun map_name_space f (Name_Space {kind, internals, internals_hidden, entries, aliases}) =
  make_name_space (f (kind, internals, internals_hidden, entries, aliases));

fun change_base_space begin =
  map_name_space (fn (kind, internals, internals_hidden, entries, aliases) =>
    (kind,
      Long_Name.Chunks.change_base begin internals,
      Long_Name.Chunks.change_base begin internals_hidden,
      Change_Table.change_base begin entries,
      aliases));

val change_ignore_space =
  map_name_space (fn (kind, internals, internals_hidden, entries, aliases) =>
    (kind,
      Long_Name.Chunks.change_ignore internals,
      Long_Name.Chunks.change_ignore internals_hidden,
      Change_Table.change_ignore entries,
      aliases));


fun empty kind =
  make_name_space
    (kind, Long_Name.Chunks.empty, Long_Name.Chunks.empty, Change_Table.empty, Symtab.empty);

fun kind_of (Name_Space {kind, ...}) = kind;
fun lookup_internals (Name_Space {internals, ...}) =
  Long_Name.Chunks.lookup_list internals;
fun lookup_internals_hidden (Name_Space {internals_hidden, ...}) =
  Long_Name.Chunks.lookup_list internals_hidden;
fun lookup_entries (Name_Space {entries, ...}) = Change_Table.lookup entries;
fun lookup_aliases (Name_Space {aliases, ...}) = Symtab.lookup_list aliases;


fun suppress_entry space name =
  (case lookup_entries space name of
    SOME {suppress, ...} => (suppress, name)
  | NONE => ([], name));

fun is_alias space c a =
  c = a orelse exists (fn (_, b) => b = a) (lookup_aliases space c);

fun get_aliases space name =
  lookup_aliases space name @ [suppress_entry space name];

fun gen_markup def space name =
  (case lookup_entries space name of
    NONE => Markup.intensify
  | SOME entry => markup_entry def (kind_of space) (name, entry));

val markup = gen_markup {def = false};
val markup_def = gen_markup {def = true};

fun undefined_entry (space as Name_Space {kind, entries, ...}) bad =
  let
    val (prfx, sfx) =
      (case Long_Name.dest_hidden bad of
        SOME name =>
          if Change_Table.defined entries name
          then ("Inaccessible", Markup.markup (markup space name) (quote name))
          else ("Undefined", quote name)
      | NONE => ("Undefined", quote bad));
  in prfx ^ " " ^ plain_words kind ^ ": " ^ sfx end;

fun the_entry space name =
  (case lookup_entries space name of
    SOME entry => entry
  | _ => error (undefined_entry space name));

fun get_names (Name_Space {entries, ...}) =
  Change_Table.fold (cons o #1) entries [];

fun theory_name {long} space name =
  #theory_long_name (the_entry space name)
  |> not long ? Long_Name.base_name;

fun entry_ord space = int_ord o apply2 (#serial o the_entry space);

fun is_concealed space name =
  #concealed (the_entry space name) handle ERROR _ => false;


(* intern *)

fun intern_chunks space xname =
  (case lookup_internals space xname of
    name :: rest => {name = name, full_name = name, unique = null rest}
  | [] =>
      (case lookup_internals_hidden space xname of
        name' :: _ => {name = Long_Name.hidden name', full_name = "", unique = true}
      | [] =>
         {name = Long_Name.hidden (Long_Name.implode_chunks xname),
          full_name = "",
          unique = true}));

fun intern space = #name o intern_chunks space o Long_Name.make_chunks;


(* extern *)

val names_long = Config.declare_option_bool ("names_long", \<^here>);
val names_short = Config.declare_option_bool ("names_short", \<^here>);
val names_unique = Config.declare_option_bool ("names_unique", \<^here>);

fun extern ctxt space name =
  let
    val names_long = Config.get ctxt names_long;
    val names_short = Config.get ctxt names_short;
    val names_unique = Config.get ctxt names_unique;

    fun extern_chunks require_unique a chunks =
      let val {full_name = c, unique, ...} = intern_chunks space chunks in
        if (not require_unique orelse unique) andalso is_alias space c a
        then SOME (Long_Name.implode_chunks chunks)
        else NONE
      end;

    fun extern_name (suppress, a) =
      get_first (extern_chunks names_unique a)
        (make_accesses {intern = false} NONE (suppress, a));

    fun extern_names aliases =
      (case get_first extern_name aliases of
        SOME xname => xname
      | NONE =>
          (case get_first (fn (_, a) => extern_chunks false a (Long_Name.make_chunks a)) aliases of
            SOME xname => xname
          | NONE => Long_Name.hidden name));
  in
    if names_long then name
    else if names_short then Long_Name.base_name name
    else extern_names (get_aliases space name)
  end;

fun extern_ord ctxt space = string_ord o apply2 (extern ctxt space);

fun extern_shortest ctxt =
  extern
    (ctxt
      |> Config.put names_long false
      |> Config.put names_short false
      |> Config.put names_unique false);

fun markup_extern ctxt space name = (markup space name, extern ctxt space name);
fun pretty ctxt space name = Pretty.mark_str (markup_extern ctxt space name);


(* completion *)

fun completion context space pred (xname, pos) =
  Completion.make (xname, pos) (fn completed =>
    let
      fun result_ord ((pri1, (xname1, (_, name1))), (pri2, (xname2, (_, name2)))) =
        (case int_ord (pri2, pri1) of
          EQUAL =>
            (case bool_ord (apply2 (is_some o Long_Name.dest_local) (name2, name1)) of
              EQUAL =>
                (case int_ord (apply2 Long_Name.count (xname1, xname2)) of
                  EQUAL => string_ord (xname1, xname2)
                | ord => ord)
            | ord => ord)
        | ord => ord);
      val Name_Space {kind, internals, ...} = space;
      val ext = extern_shortest (Context.proof_of context) space;
      val full = Name.clean xname = "";

      fun complete xname' name =
        if (completed xname' orelse exists completed (Long_Name.explode xname')) andalso
          not (is_concealed space name) andalso pred name
        then
          let
            val xname'' = ext name;
            val pri = (if xname' = xname'' then 1 else 0) + (if completed xname' then 1 else 0);
          in
            if xname' <> xname'' andalso full then I
            else cons (pri, (xname', (kind, name)))
          end
        else I;
    in
      Long_Name.Chunks.fold
        (fn (xname', name :: _) => complete (Long_Name.implode_chunks xname') name | _ => I)
        internals []
      |> sort_distinct result_ord
      |> map #2
    end);


(* merge *)

fun merge
   (Name_Space {kind = kind1, internals = internals1, internals_hidden = internals_hidden1,
     entries = entries1, aliases = aliases1},
    Name_Space {kind = kind2, internals = internals2, internals_hidden = internals_hidden2,
     entries = entries2, aliases = aliases2}) =
  let
    val kind' =
      if kind1 = kind2 then kind1
      else error ("Attempt to merge different kinds of name spaces " ^
        quote kind1 ^ " vs. " ^ quote kind2);
    val internals' = merge_internals (internals1, internals2);
    val internals_hidden' = merge_internals (internals_hidden1, internals_hidden2);
    val entries' = (entries1, entries2) |> Change_Table.join (fn name => fn (entry1, entry2) =>
      if op = (apply2 #serial (entry1, entry2)) then raise Change_Table.SAME
      else err_dup_entry kind' (name, entry1) (name, entry2) Position.none);
    val aliases' = Symtab.merge_list (op =) (aliases1, aliases2);
  in make_name_space (kind', internals', internals_hidden', entries', aliases') end;



(** naming context **)

(* datatype naming *)

datatype naming = Naming of
 {scopes: Binding.scope list,
  restricted: (bool * Binding.scope) option,
  concealed: bool,
  group: serial,
  theory_long_name: string,
  path: (string * bool) list};

fun make_naming (scopes, restricted, concealed, group, theory_long_name, path) =
  Naming {scopes = scopes, restricted = restricted, concealed = concealed,
    group = group, theory_long_name = theory_long_name, path = path};

fun map_naming f (Naming {scopes, restricted, concealed, group, theory_long_name, path}) =
  make_naming (f (scopes, restricted, concealed, group, theory_long_name, path));


(* scope and access restriction *)

fun get_scopes (Naming {scopes, ...}) = scopes;
val get_scope = try hd o get_scopes;

fun new_scope naming =
  let
    val scope = Binding.new_scope ();
    val naming' =
      naming |> map_naming (fn (scopes, restricted, concealed, group, theory_long_name, path) =>
        (scope :: scopes, restricted, concealed, group, theory_long_name, path));
  in (scope, naming') end;

fun restricted_scope strict scope =
  map_naming (fn (scopes, _, concealed, group, theory_long_name, path) =>
    (scopes, SOME (strict, scope), concealed, group, theory_long_name, path));

fun restricted strict pos naming =
  (case get_scope naming of
    SOME scope => restricted_scope strict scope naming
  | NONE => error ("Missing local scope -- cannot restrict name space accesses" ^ Position.here pos));

val private_scope = restricted_scope true;
val private = restricted true;

val qualified_scope = restricted_scope false;
val qualified = restricted false;

val concealed = map_naming (fn (scopes, restricted, _, group, theory_long_name, path) =>
  (scopes, restricted, true, group, theory_long_name, path));


(* additional structural info *)

fun set_theory_long_name theory_long_name =
  map_naming (fn (scopes, restricted, concealed, group, _, path) =>
    (scopes, restricted, concealed, group, theory_long_name, path));

fun get_group (Naming {group, ...}) = if group = 0 then NONE else SOME group;

fun set_group group =
  map_naming (fn (scopes, restricted, concealed, _, theory_long_name, path) =>
    (scopes, restricted, concealed, the_default 0 group, theory_long_name, path));

fun new_group naming = set_group (SOME (serial ())) naming;
val reset_group = set_group NONE;


(* name entry path *)

fun get_path (Naming {path, ...}) = path;

fun map_path f =
  map_naming (fn (scopes, restricted, concealed, group, theory_long_name, path) =>
    (scopes, restricted, concealed, group, theory_long_name, f path));

fun add_path elems = map_path (fn path => path @ [(elems, false)]);
val root_path = map_path (fn _ => []);
val parent_path = map_path (perhaps (try (#1 o split_last)));
fun mandatory_path elems = map_path (fn path => path @ [(elems, true)]);

fun qualified_path mandatory binding = map_path (fn path =>
  path @ Binding.path_of (Binding.qualify_name mandatory binding ""));

val global_naming = make_naming ([], NONE, false, 0, "", []);
val local_naming = global_naming |> add_path Long_Name.localN;


(* transform *)

fun transform_naming (Naming {restricted = restricted', concealed = concealed', ...}) =
  (case restricted' of
    SOME (strict, scope) => restricted_scope strict scope
  | NONE => I) #>
  concealed' ? concealed;

fun transform_binding (Naming {restricted, concealed, ...}) =
  Binding.restricted restricted #>
  concealed ? Binding.concealed;


(* full name *)

fun name_spec naming binding =
  Binding.name_spec (get_scopes naming) (get_path naming) (transform_binding naming binding);

val full_name = #full_name oo name_spec;
val base_name = Long_Name.base_name o full_name global_naming;


(* hide *)

fun hide fully name space =
  space |> map_name_space (fn (kind, internals, internals_hidden, entries, aliases) =>
    let
      val _ = the_entry space name;
      val hide_names = get_aliases space name;
      val accesses =
        maps (make_accesses {intern = true} NONE) hide_names
        |> not fully ? inter Long_Name.eq_chunks [Long_Name.base_chunks name];
      val accesses' = maps (make_accesses {intern = false} NONE) hide_names;
      val internals' = internals
        |> fold (del_internals name) accesses
        |> fold (del_internals' name) accesses';
      val internals_hidden' = internals_hidden
        |> add_internals name (Long_Name.make_chunks name);
    in (kind, internals', internals_hidden', entries, aliases) end);


(* alias *)

fun alias naming binding name space =
  space |> map_name_space (fn (kind, internals, internals_hidden, entries, aliases) =>
    let
      val _ = the_entry space name;
      val {restriction, suppress, full_name = alias_name, ...} = name_spec naming binding;
      val _ = alias_name = "" andalso error (Binding.bad binding);
      val alias_accesses = make_accesses {intern = true} restriction (suppress, alias_name);
      val internals' = internals |> fold (add_internals name) alias_accesses;
      val aliases' = aliases |> Symtab.update_list (op =) (name, (suppress, alias_name));
    in (kind, internals', internals_hidden, entries, aliases') end);



(** context naming **)

structure Data_Args =
struct
  type T = naming;
  val empty = global_naming;
  fun init _ = local_naming;
  val merge = #1;
end;

structure Global_Naming = Theory_Data(Data_Args);
structure Local_Naming = Proof_Data(Data_Args);

fun naming_of (Context.Theory thy) = Global_Naming.get thy
  | naming_of (Context.Proof ctxt) = Local_Naming.get ctxt;

fun map_naming f (Context.Theory thy) = Context.Theory (Global_Naming.map f thy)
  | map_naming f (Context.Proof ctxt) = Context.Proof (Local_Naming.map f ctxt);



(** entry definition **)

(* declaration *)

fun declared (Name_Space {entries, ...}) = Change_Table.defined entries;

fun declare context strict binding space =
  let
    val naming = naming_of context;
    val Naming {group, theory_long_name, ...} = naming;
    val name_spec as {restriction, suppress, full_name = name, ...} = name_spec naming binding;
    val _ = name = "" andalso error (Binding.bad binding);
    val accesses = make_accesses {intern = true} restriction (suppress, name);

    val (proper_pos, pos) = Position.default (Binding.pos_of binding);
    val entry: entry =
     {concealed = #concealed name_spec,
      suppress = suppress,
      group = group,
      theory_long_name = theory_long_name,
      pos = pos,
      serial = serial ()};
    val space' =
      space |> map_name_space (fn (kind, internals, internals_hidden, entries, aliases) =>
        let
          val internals' = internals |> fold (add_internals name) accesses;
          val entries' = entries |> update_entry strict kind (name, entry);
        in (kind, internals', internals_hidden, entries', aliases) end);
    val _ =
      if proper_pos andalso Context_Position.is_reported_generic context pos then
        Position.report pos (markup_entry {def = true} (kind_of space) (name, entry))
      else ();
  in (name, space') end;


(* definition in symbol table *)

datatype 'a table = Table of T * 'a Change_Table.T;

fun change_base begin (Table (space, tab)) =
  Table (change_base_space begin space, Change_Table.change_base begin tab);

fun change_ignore (Table (space, tab)) =
  Table (change_ignore_space space, Change_Table.change_ignore tab);

fun space_of_table (Table (space, _)) = space;

fun check_reports context (Table (space, tab)) (xname, ps) =
  let val name = intern space xname in
    (case Change_Table.lookup tab name of
      SOME x =>
        let
          val reports =
            filter (Context_Position.is_reported_generic context) ps
            |> map (fn pos => (pos, markup space name));
        in ((name, reports), x) end
    | NONE =>
        error (undefined_entry space name ^ Position.here_list ps ^
          Completion.markup_report
            (map (fn pos => completion context space (K true) (xname, pos)) ps)))
  end;

fun check context table (xname, pos) =
  let
    val ((name, reports), x) = check_reports context table (xname, [pos]);
    val _ = Context_Position.reports_generic context reports;
  in (name, x) end;

fun defined (Table (_, tab)) name = Change_Table.defined tab name;
fun lookup (Table (_, tab)) name = Change_Table.lookup tab name;
fun lookup_key (Table (_, tab)) name = Change_Table.lookup_key tab name;

fun get table name =
  (case lookup_key table name of
    SOME (_, x) => x
  | NONE => error (undefined_entry (space_of_table table) name));

fun define context strict (binding, x) (Table (space, tab)) =
  let
    val (name, space') = declare context strict binding space;
    val tab' = Change_Table.update (name, x) tab;
  in (name, Table (space', tab')) end;


(* derived table operations *)

fun alias_table naming binding name (Table (space, tab)) =
  Table (alias naming binding name space, tab);

fun hide_table fully name (Table (space, tab)) =
  Table (hide fully name space, tab);

fun del_table name (Table (space, tab)) =
  let
    val space' = hide true name space handle ERROR _ => space;
    val tab' = Change_Table.delete_safe name tab;
  in Table (space', tab') end;

fun map_table_entry name f (Table (space, tab)) =
  Table (space, Change_Table.map_entry name f tab);

fun fold_table f (Table (_, tab)) = Change_Table.fold f tab;
fun dest_table (Table (_, tab)) = Change_Table.dest tab;

fun empty_table kind = Table (empty kind, Change_Table.empty);

fun merge_tables (Table (space1, tab1), Table (space2, tab2)) =
  Table (merge (space1, space2), Change_Table.merge (K true) (tab1, tab2));

fun join_tables f (Table (space1, tab1), Table (space2, tab2)) =
  Table (merge (space1, space2), Change_Table.join f (tab1, tab2));


(* present table content *)

fun extern_entries verbose ctxt space entries =
  fold (fn (name, x) =>
    (verbose orelse not (is_concealed space name)) ?
      cons ((name, extern ctxt space name), x)) entries []
  |> sort_by (#2 o #1);

fun markup_entries verbose ctxt space entries =
  extern_entries verbose ctxt space entries
  |> map (fn ((name, xname), x) => ((markup space name, xname), x));

fun extern_table verbose ctxt (Table (space, tab)) =
  extern_entries verbose ctxt space (Change_Table.dest tab);

fun markup_table verbose ctxt (Table (space, tab)) =
  markup_entries verbose ctxt space (Change_Table.dest tab);

end;

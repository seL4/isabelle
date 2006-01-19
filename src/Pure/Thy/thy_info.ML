(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Main part of theory loader database, including handling of theory and
file dependencies.
*)

signature BASIC_THY_INFO =
sig
  val theory: string -> theory
(*val use: string -> unit*)             (*exported later*)
  val time_use: string -> unit
  val touch_thy: string -> unit
  val use_thy: string -> unit
  val update_thy: string -> unit
  val remove_thy: string -> unit
  val time_use_thy: string -> unit
  val use_thy_only: string -> unit
  val update_thy_only: string -> unit
end;

signature THY_INFO =
sig
  include BASIC_THY_INFO
  datatype action = Update | Outdate | Remove
  val str_of_action: action -> string
  val add_hook: (action -> string -> unit) -> unit
  val names: unit -> string list
  val known_thy: string -> bool
  val check_known_thy: string -> bool
  val if_known_thy: (string -> unit) -> string -> unit
  val lookup_theory: string -> theory option
  val get_theory: string -> theory
  val get_preds: string -> string list
  val loaded_files: string -> Path.T list
  val touch_child_thys: string -> unit
  val touch_all_thys: unit -> unit
  val load_file: bool -> Path.T -> unit
  val use: string -> unit
  val quiet_update_thy: bool -> string -> unit
  val pretend_use_thy_only: string -> unit
  val begin_theory: (Path.T option -> string -> string list ->
      (Path.T * bool) list -> theory -> theory) ->
    string -> string list -> (Path.T * bool) list -> bool -> theory
  val end_theory: theory -> theory
  val finish: unit -> unit
  val register_theory: theory -> unit
  val pretty_theory: theory -> Pretty.T
end;

structure ThyInfo: THY_INFO =
struct


(** theory loader actions and hooks **)

datatype action = Update | Outdate | Remove;
val str_of_action = fn Update => "Update" | Outdate => "Outdate" | Remove => "Remove";

local
  val hooks = ref ([]: (action -> string -> unit) list);
in
  fun add_hook f = hooks := f :: ! hooks;
  fun perform action name = List.app (fn f => (try (fn () => f action name) (); ())) (! hooks);
end;



(** thy database **)

(* messages *)

fun gen_msg txt [] = txt
  | gen_msg txt names = txt ^ " " ^ commas_quote names;

fun loader_msg txt names = gen_msg ("Theory loader: " ^ txt) names;

val show_path = space_implode " via " o map quote;
fun cycle_msg names = loader_msg ("cyclic dependency of " ^ show_path names) [];


(* derived graph operations *)

fun add_deps name parents G = Graph.add_deps_acyclic (name, parents) G
  handle Graph.CYCLES namess => error (cat_lines (map cycle_msg namess));

fun upd_deps name entry G =
  Library.foldl (fn (H, parent) => Graph.del_edge (parent, name) H) (G, Graph.imm_preds G name)
  |> Graph.map_node name (K entry);

fun update_node name parents entry G =
  (if can (Graph.get_node G) name then upd_deps name entry G else Graph.new_node (name, entry) G)
  |> add_deps name parents;


(* thy database *)

type deps =
  {present: bool, outdated: bool,
    master: ThyLoad.master option, files: (Path.T * (Path.T * File.info) option) list};

fun make_deps present outdated master files =
  {present = present, outdated = outdated, master = master, files = files}: deps;

fun init_deps master files = SOME (make_deps false true master (map (rpair NONE) files));


type thy = deps option * theory option;

local
  val database = ref (Graph.empty: thy Graph.T);
in
  fun get_thys () = ! database;
  val change_thys = Library.change database;
end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;

(*theory names in topological order*)
fun get_names () =
  let val G = get_thys ()
  in Graph.all_succs G (Graph.minimals G) end;


(* access thy *)

fun lookup_thy name =
  SOME (thy_graph Graph.get_node name) handle Graph.UNDEF _ => NONE;

val known_thy = is_some o lookup_thy;
fun check_known_thy name = known_thy name orelse (warning ("Unknown theory " ^ quote name); false);
fun if_known_thy f name = if check_known_thy name then f name else ();

fun get_thy name =
  (case lookup_thy name of
    SOME thy => thy
  | NONE => error (loader_msg "nothing known about theory" [name]));

fun change_thy name f = (get_thy name; change_thys (Graph.map_node name f));


(* access deps *)

val lookup_deps = Option.map #1 o lookup_thy;
val get_deps = #1 o get_thy;
fun change_deps name f = change_thy name (fn (deps, x) => (f deps, x));

fun is_finished name = is_none (get_deps name);
fun get_files name = (case get_deps name of SOME {files, ...} => files | _ => []);

fun loaded_files name =
  (case get_deps name of
    NONE => []
  | SOME {master, files, ...} =>
      (case master of SOME m => [#1 (ThyLoad.get_thy m)] | NONE => []) @
      (List.mapPartial (Option.map #1 o #2) files));

fun get_preds name =
  (thy_graph Graph.imm_preds name) handle Graph.UNDEF _ =>
    error (loader_msg "nothing known about theory" [name]);


(* pretty printing a theory *)

local

fun relevant_names names =
  let
    val (finished, unfinished) =
      List.filter (equal Context.draftN orf known_thy) names
      |> List.partition (not_equal Context.draftN andf is_finished);
  in (if not (null finished) then [List.last finished] else []) @ unfinished end;

in

fun pretty_theory thy =
  Pretty.str_list "{" "}" (relevant_names (Context.names_of thy));

end;


(* access theory *)

fun lookup_theory name =
  (case lookup_thy name of
    SOME (_, SOME thy) => SOME thy
  | _ => NONE);

fun get_theory name =
  (case lookup_theory name of
    (SOME theory) => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

fun put_theory name theory = change_thy name (fn (deps, _) => (deps, SOME theory));



(** thy operations **)

(* maintain 'outdated' flag *)

local

fun is_outdated name =
  (case lookup_deps name of
    SOME (SOME {outdated, ...}) => outdated
  | _ => false);

fun outdate_thy name =
  if is_finished name orelse is_outdated name then ()
  else (change_deps name (Option.map (fn {present, outdated = _, master, files} =>
    make_deps present true master files)); perform Outdate name);

fun check_unfinished name =
  if is_finished name then (warning (loader_msg "tried to touch finished theory" [name]); NONE)
  else SOME name;

in

fun touch_thys names =
  List.app outdate_thy (thy_graph Graph.all_succs (List.mapPartial check_unfinished names));

fun touch_thy name = touch_thys [name];
fun touch_child_thys name = touch_thys (thy_graph Graph.imm_succs name);

fun touch_all_thys () = List.app outdate_thy (get_names ());

end;


(* check 'finished' state *)

fun check_unfinished fail name =
  if known_thy name andalso is_finished name then
    fail (loader_msg "cannot update finished theory" [name])
  else ();


(* load_file *)

val opt_path = Option.map (Path.dir o fst o ThyLoad.get_thy);
fun opt_path' (d: deps option) = if_none (Option.map (opt_path o #master) d) NONE;
fun opt_path'' d = if_none (Option.map opt_path' d) NONE;

local

fun provide path name info (deps as SOME {present, outdated, master, files}) =
     (if exists (equal path o #1) files then ()
      else warning (loader_msg "undeclared dependency of theory" [name] ^
        " on file: " ^ quote (Path.pack path));
      SOME (make_deps present outdated master (AList.update (op =) (path, SOME info) files)))
  | provide _ _ _ NONE = NONE;

fun run_file path =
  (case Option.map Context.theory_name (Context.get_context ()) of
    NONE => (ThyLoad.load_file NONE path; ())
  | SOME name => (case lookup_deps name of
      SOME deps => change_deps name (provide path name
        (ThyLoad.load_file (opt_path' deps) path))
    | NONE => (ThyLoad.load_file NONE path; ())));

in

fun load_file time path = Output.toplevel_errors (fn () =>
  if time then
    let val name = Path.pack path in
      timeit (fn () =>
       (priority ("\n**** Starting file " ^ quote name ^ " ****");
        run_file path;
        priority ("**** Finished file " ^ quote name ^ " ****\n")))
    end
  else run_file path) ();

val use = load_file false o Path.unpack;
val time_use = load_file true o Path.unpack;

end;


(* load_thy *)

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy really ml time initiators dir name =
  let
    val _ =
      if really then priority ("Loading theory " ^ quote name ^ required_by " " initiators)
      else priority ("Registering theory " ^ quote name);

    val _ = touch_thy name;
    val master =
      if really then ThyLoad.load_thy dir name ml time
      else #1 (ThyLoad.deps_thy dir name ml);

    val files = get_files name;
    val missing_files = List.mapPartial (fn (path, NONE) => SOME (Path.pack path) | _ => NONE) files;
  in
    if null missing_files then ()
    else warning (loader_msg "unresolved dependencies of theory" [name] ^
      " on file(s): " ^ commas_quote missing_files);
    change_deps name (fn _ => SOME (make_deps true false (SOME master) files));
    perform Update name
  end;


(* require_thy *)

fun base_of_path s = Path.pack (Path.base (Path.unpack s));

local

fun load_deps ml dir name =
  let val (master, (parents, files)) = ThyLoad.deps_thy dir name ml
  in (SOME (init_deps (SOME master) files), parents) end;

fun file_current master (_, NONE) = false
  | file_current master (path, info) =
      (info = ThyLoad.check_file (opt_path master) path);

fun current_deps ml strict dir name =
  (case lookup_deps name of
    NONE => (false, load_deps ml dir name)
  | SOME deps =>
      let
        fun get_name s = (case opt_path'' (lookup_deps s) of NONE => s
          | SOME p => Path.pack (Path.append p (Path.basic s)));
        val same_deps = (NONE, map get_name (thy_graph Graph.imm_preds name))
      in
        (case deps of
          NONE => (true, same_deps)
        | SOME {present, outdated, master, files} =>
            if present andalso not strict then (true, same_deps)
            else
              let val master' = SOME (ThyLoad.check_thy dir name ml) in
                if master <> master' then (false, load_deps ml dir name)
                else (not outdated andalso forall (file_current master') files, same_deps)
              end)
      end);

fun require_thy really ml time strict keep_strict initiators prfx (visited, str) =
  let
    val path = Path.expand (Path.unpack str);
    val name = Path.pack (Path.base path);
  in
    if name mem_string initiators then error (cycle_msg initiators) else ();
    if known_thy name andalso is_finished name orelse name mem_string visited then
      (visited, (true, name))
    else
      let
        val dir = Path.append prfx (Path.dir path);
        val req_parent = require_thy true true time (strict andalso keep_strict) keep_strict
          (name :: initiators);

        val (current, (new_deps, parents)) = current_deps ml strict dir name
          handle ERROR msg => cat_error msg
            (loader_msg "the error(s) above occurred while examining theory" [name] ^
              (if null initiators then "" else required_by "\n" initiators));
        val dir' = if_none (opt_path'' new_deps) dir;
        val (visited', parent_results) = foldl_map (req_parent dir') (name :: visited, parents);

        val thy = if not really then SOME (get_theory name) else NONE;
        val result =
          if current andalso forall fst parent_results then true
          else
            ((case new_deps of
              SOME deps => change_thys (update_node name (map base_of_path parents) (deps, thy))
            | NONE => ());
             load_thy really ml (time orelse ! Output.timing) initiators dir name;
             false);
      in (visited', (result, name)) end
  end;

fun gen_use_thy' req prfx s = Output.toplevel_errors (fn () =>
  let val (_, (_, name)) = req [] prfx ([], s)
  in Context.context (get_theory name) end) ();

fun gen_use_thy req = gen_use_thy' req Path.current;

fun warn_finished f name = (check_unfinished warning name; f name);

in

val weak_use_thy         = gen_use_thy' (require_thy true true false false false);
fun quiet_update_thy' ml = gen_use_thy' (require_thy true ml false true true);
fun quiet_update_thy ml  = gen_use_thy (require_thy true ml false true true);

val use_thy          = warn_finished (gen_use_thy (require_thy true true false true false));
val time_use_thy     = warn_finished (gen_use_thy (require_thy true true true true false));
val use_thy_only     = warn_finished (gen_use_thy (require_thy true false false true false));
val update_thy       = warn_finished (gen_use_thy (require_thy true true false true true));
val update_thy_only  = warn_finished (gen_use_thy (require_thy true false false true true));
val pretend_use_thy_only = warn_finished (gen_use_thy (require_thy false false false true false));

end;


(* remove_thy *)

fun remove_thy name =
  if is_finished name then error (loader_msg "cannot remove finished theory" [name])
  else
    let val succs = thy_graph Graph.all_succs [name] in
      priority (loader_msg "removing" succs);
      List.app (perform Remove) succs;
      change_thys (Graph.del_nodes succs)
    end;


(* begin / end theory *)

fun check_uses name uses =
  let val illegal = map (fn ext => Path.ext ext (Path.basic name)) ThyLoad.ml_exts in
    (case find_first (member (op =) illegal o Path.base o Path.expand o #1) uses of
      NONE => ()
    | SOME (path, _) => error ("Illegal use of theory ML file: " ^ quote (Path.pack path)))
  end;

fun begin_theory present name parents uses int =
  let
    val bparents = map base_of_path parents;
    val dir' = opt_path'' (lookup_deps name);
    val dir = if_none dir' Path.current;
    val assert_thy = if int then quiet_update_thy' true dir else weak_use_thy dir;
    val _ = check_unfinished error name;
    val _ = List.app assert_thy parents;
    val _ = check_uses name uses;

    val theory = Theory.begin_theory name (map get_theory bparents);
    val deps =
      if known_thy name then get_deps name
      else (init_deps NONE (map #1 uses));   (*records additional ML files only!*)
    val uses_now = List.mapPartial (fn (x, true) => SOME x | _ => NONE) uses;

    val _ = change_thys (update_node name bparents (deps, SOME (Theory.copy theory)));
    val theory' = theory |> present dir' name bparents uses;
    val _ = put_theory name (Theory.copy theory');
    val ((), theory'') = Context.pass_theory theory' (List.app (load_file false)) uses_now;
    val _ = put_theory name (Theory.copy theory'');
  in theory'' end;

fun end_theory theory =
  let
    val name = Context.theory_name theory;
    val theory' = Theory.end_theory theory;
  in put_theory name theory'; theory' end;


(* finish all theories *)

fun finish () = change_thys (Graph.map_nodes (fn (_, entry) => (NONE, entry)));


(* register existing theories *)

fun register_theory theory =
  let
    val name = Context.theory_name theory;
    val parents = Theory.parents_of theory;
    val parent_names = map Context.theory_name parents;

    fun err txt bads =
      error (loader_msg txt bads ^ "\n" ^ gen_msg "cannot register theory" [name]);

    val nonfinished = filter_out is_finished parent_names;
    fun get_variant (x, y_name) =
      if Theory.eq_thy (x, get_theory y_name) then NONE
      else SOME y_name;
    val variants = List.mapPartial get_variant (parents ~~ parent_names);

    fun register G =
      (Graph.new_node (name, (NONE, SOME theory)) G
        handle Graph.DUP _ => err "duplicate theory entry" [])
      |> add_deps name parent_names;
  in
    if not (null nonfinished) then err "non-finished parent theories" nonfinished
    else if not (null variants) then err "different versions of parent theories" variants
    else (change_thys register; perform Update name)
  end;

val _ = register_theory ProtoPure.thy;


(*final declarations of this structure*)
val theory = get_theory;
val names = get_names;

end;

structure BasicThyInfo: BASIC_THY_INFO = ThyInfo;
open BasicThyInfo;

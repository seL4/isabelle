(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory loader database, including theory and file dependencies.
*)

signature BASIC_THY_INFO =
sig
  val theory: string -> theory
  val theory_of_sign: Sign.sg -> theory
  val theory_of_thm: thm -> theory
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
  val lookup_theory: string -> theory option
  val get_theory: string -> theory
  val get_preds: string -> string list
  val loaded_files: string -> ((Path.T * File.info) * bool) list
  val touch_all_thys: unit -> unit
  val may_load_file: bool -> bool -> Path.T -> unit
  val use_path: Path.T -> unit
  val use: string -> unit
  val pretend_use: string -> unit
  val quiet_update_thy: string -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> theory
  val begin_update_theory: string -> string list -> (Path.T * bool) list -> theory
  val end_theory: theory -> theory
  val finish: unit -> unit
  val register_theory: theory -> unit
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
  fun perform action name = seq (fn f => (try (fn () => f action name) (); ())) (! hooks);
end;



(** thy database **)

(* messages *)

fun gen_msg txt [] = txt
  | gen_msg txt names = txt ^ " " ^ commas_quote names;

fun loader_msg txt names = gen_msg ("Theory loader: " ^ txt) names;

val show_path = space_implode " via " o map quote;
fun cycle_msg name names = loader_msg ("cyclic dependency of " ^ show_path (name :: names)) [];


(* derived graph operations *)

fun add_deps name parents G =
  foldl (fn (H, parent) => Graph.add_edge_acyclic (parent, name) H) (G, parents)
    handle Graph.CYCLES namess => error (cat_lines (map (cycle_msg name) namess));

fun del_deps name G =
  foldl (fn (H, parent) => Graph.del_edge (parent, name) H) (G, Graph.imm_preds G name);

fun update_node name parents entry G =
  add_deps name parents
    (if can (Graph.get_node G) name then del_deps name G else Graph.new_node (name, entry) G);


(* thy database *)

type deps =
  {present: bool, outdated: bool,
    master: ThyLoad.master option, files: (Path.T * ((Path.T * File.info) * bool) option) list};

fun make_deps present outdated master files =
  {present = present, outdated = outdated, master = master, files = files}: deps;

fun init_deps master files = Some (make_deps false true master (map (rpair None) files));


type thy = deps option * theory option;

local
  val database = ref (Graph.empty: thy Graph.T);
in
  fun get_thys () = ! database;
  fun change_thys f = database := (f (! database));
end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;
fun get_names () = Graph.keys (get_thys ());


(* access thy *)

fun lookup_thy name = Some (thy_graph Graph.get_node name) handle Graph.UNDEFINED _ => None;

fun get_thy name =
  (case lookup_thy name of
    Some thy => thy
  | None => error (loader_msg "nothing known about theory" [name]));

fun change_thy name f = (get_thy name; change_thys (Graph.map_node name f));


(* access deps *)

val lookup_deps = apsome #1 o lookup_thy;
val get_deps = #1 o get_thy;
fun change_deps name f = change_thy name (fn (deps, x) => (f deps, x));

fun is_finished name = is_none (get_deps name);
fun get_files name = (case get_deps name of Some {files, ...} => files | _ => []);

fun loaded_files name =
  (case get_deps name of
    Some {master = Some master, files, ...} => (ThyLoad.get_thy master, true) :: mapfilter #2 files
  | Some {files, ...} => mapfilter #2 files
  | None => []);

fun get_preds name =
  (thy_graph Graph.imm_preds name) handle Graph.UNDEFINED _ =>
    error (loader_msg "nothing known about theory" [name]);


(* access theory *)

fun lookup_theory name = #2 (get_thy name);

fun get_theory name =
  (case lookup_theory name of
    (Some theory) => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

val theory_of_sign = get_theory o Sign.name_of;
val theory_of_thm = theory_of_sign o Thm.sign_of_thm;

fun put_theory name theory = change_thy name (fn (deps, _) => (deps, Some theory));



(** thy operations **)

(* maintain 'outdated' flag *)

local

fun is_outdated name =
  (case lookup_deps name of
    Some (Some {outdated, ...}) => outdated
  | _ => false);

fun outdate_thy name =
  if is_finished name orelse is_outdated name then ()
  else (change_deps name (apsome (fn {present, outdated = _, master, files} =>
    make_deps present true master files)); perform Outdate name);

in

fun touch_thy name =
  if is_finished name then warning (loader_msg "tried to touch finished theory" [name])
  else seq outdate_thy (thy_graph Graph.all_succs [name]);

fun touch_all_thys () = seq outdate_thy (get_names ());

end;


(* check 'finished' state *)

fun check_unfinished fail name =
  if is_some (lookup_thy name) andalso is_finished name then
    fail (loader_msg "cannot update finished theory" [name])
  else ();


(* may_load_file *)

local

fun may_run_file really path =
  let
    val load = ThyLoad.may_load_file really;
    fun provide name info (deps as Some {present, outdated, master, files}) =
          if exists (equal path o #1) files then
            Some (make_deps present outdated master
              (overwrite (files, (path, Some (info, really)))))
          else (warning (loader_msg "undeclared dependency of theory" [name] ^
            " on file: " ^ quote (Path.pack path)); deps)
      | provide _ _ None = None;
  in
    (case apsome PureThy.get_name (Context.get_context ()) of
      None => (load path; ())
    | Some name =>
        if is_some (lookup_thy name) then change_deps name (provide name (load path))
        else (load path; ()))
  end;

in

fun may_load_file really time path =
  if really andalso time then
    let val name = Path.pack path in
      timeit (fn () =>
       (writeln ("\n**** Starting file " ^ quote name ^ " ****");
        may_run_file really path;
        writeln ("**** Finished file " ^ quote name ^ " ****\n")))
    end
  else may_run_file really path;

end;

val use_path    = may_load_file true false;
val use         = use_path o Path.unpack;
val time_use    = may_load_file true true o Path.unpack;
val pretend_use = may_load_file false false o Path.unpack;


(* load_thy *)

fun required_by [] = ""
  | required_by initiators = " (required by " ^ show_path (rev initiators) ^ ")";

fun load_thy ml time initiators dir name parents =
  let
    val _ = writeln ("Loading theory " ^ quote name ^ required_by initiators);

    val _ = touch_thy name;
    val master = ThyLoad.load_thy dir name ml time;

    val files = get_files name;
    val missing_files = mapfilter (fn (path, None) => Some (Path.pack path) | _ => None) files;
  in
    if null missing_files then ()
    else warning (loader_msg "unresolved dependencies of theory" [name] ^
      " on file(s): " ^ commas_quote missing_files);
    change_deps name (fn _ => Some (make_deps true false (Some master) files));
    perform Update name
  end;


(* require_thy *)

local

fun load_deps dir name =
  let val (master, (parents, files)) = ThyLoad.deps_thy dir name
  in (Some (init_deps (Some master) files), parents) end;

fun file_current (_, None) = false
  | file_current (path, info) = (apsome fst info = ThyLoad.check_file path);

fun current_deps strict dir name =
  (case lookup_deps name of
    None => (false, load_deps dir name)
  | Some deps =>
      let val same_deps = (None, thy_graph Graph.imm_preds name) in
        (case deps of
          None => (true, same_deps)
        | Some {present, outdated, master, files} =>
            if present andalso not strict then (true, same_deps)
            else
              let val master' = Some (ThyLoad.check_thy dir name) in
                if master <> master' then (false, load_deps dir name)
                else (not outdated andalso forall file_current files, same_deps)
              end)
      end);

fun require_thy ml time strict keep_strict initiators prfx (visited, str) =
  let
    val path = Path.expand (Path.unpack str);
    val name = Path.pack (Path.base path);
  in
    if name mem_string initiators then error (cycle_msg name initiators) else ();
    if name mem_string visited then (visited, (true, name))
    else
      let
        val dir = Path.append prfx (Path.dir path);
        val req_parent =
          require_thy true time (strict andalso keep_strict) keep_strict (name :: initiators) dir;

        val (current, (new_deps, parents)) = current_deps strict dir name handle ERROR =>
          error (loader_msg "the error(s) above occurred while examining theory" [name] ^
            (if null initiators then "" else "\n" ^ required_by initiators));
        val (visited', parent_results) = foldl_map req_parent (name :: visited, parents);

        val result =
          if current andalso forall #1 parent_results then true
          else
            ((case new_deps of
              Some deps => change_thys (update_node name parents (deps, None))
            | None => ());
             load_thy ml time initiators dir name parents;
             false);
      in (visited', (result, name)) end
  end;

fun gen_use_thy req s =
  let val (_, (_, name)) = req [] Path.current ([], s)
  in Context.context (get_theory name) end;

fun warn_finished f name = (check_unfinished warning name; f name);

in

val weak_use_thy     = gen_use_thy (require_thy true false false false);
val quiet_update_thy = gen_use_thy (require_thy true false true true);

val use_thy          = warn_finished (gen_use_thy (require_thy true false true false));
val time_use_thy     = warn_finished (gen_use_thy (require_thy true true true false));
val use_thy_only     = warn_finished (gen_use_thy (require_thy false false true false));
val update_thy       = warn_finished (gen_use_thy (require_thy true false true true));
val update_thy_only  = warn_finished (gen_use_thy (require_thy false false true true));

end;


(* remove_thy *)

fun remove_thy name =
  if is_finished name then error (loader_msg "cannot remove finished theory" [name])
  else
    let val succs = thy_graph Graph.all_succs [name] in
      writeln (loader_msg "removing" succs);
      seq (perform Remove) succs;
      change_thys (Graph.del_nodes succs)
    end;


(* begin / end theory *)

fun gen_begin_theory check_thy name parents paths =
  let
    val _ = check_unfinished error name;
    val _ = (map Path.basic parents; seq check_thy parents);
    val theory = PureThy.begin_theory name (map get_theory parents);
    val _ = change_thys (update_node name parents (init_deps None [], Some theory));
    val use_paths = mapfilter (fn (x, true) => Some x | _ => None) paths;
  in Context.setmp (Some theory) (seq use_path) use_paths; theory end;

val begin_theory = gen_begin_theory weak_use_thy;
val begin_update_theory = gen_begin_theory quiet_update_thy;

fun end_theory theory =
  let
    val theory' = PureThy.end_theory theory;
    val name = PureThy.get_name theory;
  in put_theory name theory'; theory' end;


(* finish all theories *)

fun finish () = change_thys (Graph.map_nodes (fn (_, entry) => (None, entry)));


(* register existing theories *)

fun register_theory theory =
  let
    val name = PureThy.get_name theory;
    val parents = Theory.parents_of theory;
    val parent_names = map PureThy.get_name parents;

    fun err txt bads =
      error (loader_msg txt bads ^ "\n" ^ gen_msg "cannot register theory" [name]);

    val nonfinished = filter_out is_finished parent_names;
    fun get_variant (x, y_name) =
      if Theory.eq_thy (x, get_theory y_name) then None
      else Some y_name;
    val variants = mapfilter get_variant (parents ~~ parent_names);

    fun register G =
      (Graph.new_node (name, (None, Some theory)) G
        handle Graph.DUPLICATE _ => err "duplicate theory entry" [])
      |> add_deps name parent_names;
  in
    if not (null nonfinished) then err "non-finished parent theories" nonfinished
    else if not (null variants) then err "different versions of parent theories" variants
    else (change_thys register; perform Update name)
  end;


(*final declarations of this structure*)
val theory = get_theory;
val names = get_names;

end;

structure BasicThyInfo: BASIC_THY_INFO = ThyInfo;
open BasicThyInfo;

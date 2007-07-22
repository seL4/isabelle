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
  val the_theory: string -> theory -> theory
  val get_parents: string -> string list
  val loaded_files: string -> Path.T list
  val touch_child_thys: string -> unit
  val touch_all_thys: unit -> unit
  val load_file: bool -> Path.T -> unit
  val use: string -> unit
  val pretend_use_thy_only: string -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> bool -> theory
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

fun loader_msg txt [] = "Theory loader: " ^ txt
  | loader_msg txt names = "Theory loader: " ^ txt ^ " " ^ commas_quote names;

val show_path = space_implode " via " o map quote;
fun cycle_msg names = loader_msg ("cyclic dependency of " ^ show_path names) [];


(* derived graph operations *)

fun add_deps name parents G = Graph.add_deps_acyclic (name, parents) G
  handle Graph.CYCLES namess => error (cat_lines (map cycle_msg namess));

fun upd_deps name entry G =
  fold (fn parent => Graph.del_edge (parent, name)) (Graph.imm_preds G name) G
  |> Graph.map_node name (K entry);

fun update_node name parents entry G =
  (if can (Graph.get_node G) name then upd_deps name entry G else Graph.new_node (name, entry) G)
  |> add_deps name parents;


(* thy database *)

type master = (Path.T * File.ident) * (Path.T * File.ident) option;

type deps =
  {present: bool,               (*theory value present*)
    outdated: bool,             (*entry considered outdated*)
    master: master option,      (*master dependencies for thy + attached ML file*)
    parents: string list,       (*source specification of parents (partially qualified)*)
    files:                      (*auxiliary files: source path, physical path + identifier*)
      (Path.T * (Path.T * File.ident) option) list};

fun make_deps present outdated master parents files : deps =
  {present = present, outdated = outdated, master = master, parents = parents, files = files};

fun init_deps master parents files =
  SOME (make_deps false true master parents (map (rpair NONE) files));

fun master_idents (NONE: master option) = []
  | master_idents (SOME ((_, thy_id), NONE)) = [thy_id]
  | master_idents (SOME ((_, thy_id), SOME (_, ml_id))) = [thy_id, ml_id];

fun master_dir (NONE: master option) = Path.current
  | master_dir (SOME ((path, _), _)) = Path.dir path;

fun master_dir' (d: deps option) = the_default Path.current (Option.map (master_dir o #master) d);
fun master_dir'' d = the_default Path.current (Option.map master_dir' d);


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
      (case master of SOME ((thy_path, _), _) => [thy_path] | NONE => []) @
      (map_filter (Option.map #1 o #2) files));

fun get_parents name =
  (thy_graph Graph.imm_preds name) handle Graph.UNDEF _ =>
    error (loader_msg "nothing known about theory" [name]);


(* pretty printing a theory *)

local

fun relevant_names names =
  let
    val (finished, unfinished) =
      List.filter (fn name => name = Context.draftN orelse known_thy name) names
      |> List.partition (fn name => name <> Context.draftN andalso is_finished name);
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
    SOME theory => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

fun the_theory name thy =
  if Context.theory_name thy = name then thy
  else get_theory name;

val _ = ML_Context.value_antiq "theory"
  (Scan.lift Args.name
    >> (fn name => (name ^ "_thy", "ThyInfo.theory " ^ ML_Syntax.print_string name))
  || Scan.succeed ("thy", "ML_Context.the_context ()"));



(** thy operations **)

(* maintain 'outdated' flag *)

local

fun is_outdated name =
  (case lookup_deps name of
    SOME (SOME {outdated, ...}) => outdated
  | _ => false);

fun outdate_thy name =
  if is_finished name orelse is_outdated name then ()
  else (change_deps name (Option.map (fn {present, outdated = _, master, parents, files} =>
    make_deps present true master parents files)); perform Outdate name);

fun check_unfinished name =
  if is_finished name then (warning (loader_msg "tried to touch finished theory" [name]); NONE)
  else SOME name;

in

fun touch_thys names =
  List.app outdate_thy (thy_graph Graph.all_succs (map_filter check_unfinished names));

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

local

fun provide path name info (deps as SOME {present, outdated, master, parents, files}) =
     (if AList.defined (op =) files path then ()
      else warning (loader_msg "undeclared dependency of theory" [name] ^
        " on file: " ^ quote (Path.implode path));
      SOME (make_deps present outdated master parents
        (AList.update (op =) (path, SOME info) files)))
  | provide _ _ _ NONE = NONE;

fun run_file path =
  (case Option.map (Context.theory_name o Context.the_theory) (ML_Context.get_context ()) of
    NONE => (ThyLoad.load_ml Path.current path; ())
  | SOME name =>
      (case lookup_deps name of
        SOME deps =>
          change_deps name (provide path name (ThyLoad.load_ml (master_dir' deps) path))
      | NONE => (ThyLoad.load_ml Path.current path; ())));

in

fun load_file time path = Output.toplevel_errors (fn () =>
  if time then
    let val name = Path.implode path in
      timeit (fn () =>
       (priority ("\n**** Starting file " ^ quote name ^ " ****");
        run_file path;
        priority ("**** Finished file " ^ quote name ^ " ****\n")))
    end
  else run_file path) ();

val use = load_file false o Path.explode;
val time_use = load_file true o Path.explode;

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
    val missing_files = map_filter (fn (path, NONE) => SOME (Path.implode path) | _ => NONE) files;
  in
    if null missing_files then ()
    else warning (loader_msg "unresolved dependencies of theory" [name] ^
      " on file(s): " ^ commas_quote missing_files);
    change_deps name
      (Option.map (fn {parents, ...} => make_deps true false (SOME master) parents files));
    perform Update name
  end;


(* require_thy *)

fun base_name s = Path.implode (Path.base (Path.explode s));

local

fun check_ml master (src_path, info) =
  let val info' =
    (case info of NONE => NONE
    | SOME (_, id) =>
        (case ThyLoad.check_ml (master_dir master) src_path of NONE => NONE
        | SOME (path', id') => if id <> id' then NONE else SOME (path', id')))
  in (src_path, info') end;

fun check_deps ml strict dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, get_parents name)
  | NONE =>
      let val (master, (parents, files)) = ThyLoad.deps_thy dir name ml
      in (false, init_deps (SOME master) parents files, parents) end
  | SOME (deps as SOME {present, outdated, master, parents, files}) =>
      if present andalso not strict then (true, deps, parents)
      else
        let val master' = SOME (ThyLoad.check_thy dir name ml) in
          if master_idents master <> master_idents master'
          then
            let val (parents', files') = #2 (ThyLoad.deps_thy dir name ml)
            in (false, init_deps master' parents' files', parents') end
          else
            let
              val checked_files = map (check_ml master') files;
              val current = not outdated andalso forall (is_some o snd) checked_files;
              val deps' = SOME (make_deps present (not current) master' parents checked_files);
            in (current, deps', parents) end
        end);

fun require_thys really ml time strict keep_strict initiators dir strs visited =
  fold_map (require_thy really ml time strict keep_strict initiators dir) strs visited
and require_thy really ml time strict keep_strict initiators dir str visited =
  let
    val path = Path.expand (Path.explode str);
    val name = Path.implode (Path.base path);
    val dir' = Path.append dir (Path.dir path);
    val _ = member (op =) initiators name andalso error (cycle_msg initiators);
  in
    if known_thy name andalso is_finished name orelse member (op =) visited name
    then (true, visited)
    else
      let
        val (current, deps, parents) = check_deps ml strict dir' name
          handle ERROR msg => cat_error msg
            (loader_msg "the error(s) above occurred while examining theory" [name] ^
              required_by "\n" initiators);

        val (parents_current, visited') =
          require_thys true true time (strict andalso keep_strict) keep_strict
            (name :: initiators) (Path.append dir (master_dir' deps)) parents (name :: visited);

        val all_current = current andalso forall I parents_current;
        val thy = if all_current orelse not really then SOME (get_theory name) else NONE;
        val _ = change_thys (update_node name (map base_name parents) (deps, thy));
        val _ =
          if all_current then ()
          else load_thy really ml (time orelse ! Output.timing) initiators dir' name;
      in (all_current, visited') end
  end;

fun gen_use_thy' req dir arg =
  Output.toplevel_errors (fn () => (req [] dir arg []; ())) ();

fun gen_use_thy req str =
  let val name = base_name str in
    check_unfinished warning name;
    gen_use_thy' req Path.current str;
    ML_Context.set_context (SOME (Context.Theory (get_theory name)))
  end;

in

val quiet_update_thys    = gen_use_thy' (require_thys true true false true true);
val pretend_use_thy_only = gen_use_thy' (require_thy false false false true false) Path.current;

val use_thy              = gen_use_thy (require_thy true true false true false);
val time_use_thy         = gen_use_thy (require_thy true true true true false);
val update_thy           = gen_use_thy (require_thy true true false true true);

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
  let val illegal = map (fn ext => Path.ext ext (Path.basic name)) ("" :: ThyLoad.ml_exts) in
    (case find_first (member (op =) illegal o Path.base o Path.expand o #1) uses of
      NONE => ()
    | SOME (path, _) => error ("Illegal use of theory ML file: " ^ quote (Path.implode path)))
  end;

fun begin_theory name parents uses int =
  let
    val parent_names = map base_name parents;
    val dir = master_dir'' (lookup_deps name);
    val _ = check_unfinished error name;
    val _ = if int then quiet_update_thys dir parents else ();
    (* FIXME tmp *)
    val _ = ML_Context.set_context (SOME (Context.Theory (get_theory (List.last parent_names))));
    val _ = check_uses name uses;

    val theory =
      Theory.begin_theory name (map get_theory parent_names)
      |> Present.begin_theory dir uses;

    val deps =
      if known_thy name then get_deps name
      else init_deps NONE parents (map #1 uses);
    val _ = change_thys (update_node name parent_names (deps, NONE));

    val uses_now = map_filter (fn (x, true) => SOME x | _ => NONE) uses;
    val ((), theory') =
      ML_Context.pass_context (Context.Theory theory) (List.app (load_file false)) uses_now
      ||> Context.the_theory;
  in theory' end;

fun end_theory theory =
  let
    val name = Context.theory_name theory;
    val theory' = Theory.end_theory theory;
    val _ = change_thy name (fn (deps, _) => (deps, SOME theory'));
  in theory' end;


(* finish all theories *)

fun finish () = change_thys (Graph.map_nodes (fn (_, entry) => (NONE, entry)));


(* register existing theories *)

fun register_theory theory =
  let
    val name = Context.theory_name theory;
    val parents = Theory.parents_of theory;
    val parent_names = map Context.theory_name parents;

    fun err txt bads =
      error (loader_msg txt bads ^ "\ncannot register theory " ^ quote name);

    val nonfinished = filter_out is_finished parent_names;
    fun get_variant (x, y_name) =
      if Theory.eq_thy (x, get_theory y_name) then NONE
      else SOME y_name;
    val variants = map_filter get_variant (parents ~~ parent_names);

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

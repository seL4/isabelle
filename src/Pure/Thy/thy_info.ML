(*  Title:      Pure/Thy/thy_info.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Main part of theory loader database, including handling of theory and
file dependencies.
*)

signature BASIC_THY_INFO =
sig
  val theory: string -> theory
  val touch_thy: string -> unit
  val remove_thy: string -> unit
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
  val loaded_files: string -> Path.T list
  val get_parents: string -> string list
  val pretty_theory: theory -> Pretty.T
  val touch_child_thys: string -> unit
  val touch_all_thys: unit -> unit
  val load_file: bool -> Path.T -> unit
  val use: string -> unit
  val time_use: string -> unit
  val use_thys: string list -> unit
  val use_thy: string -> unit
  val time_use_thy: string -> unit
  val begin_theory: string -> string list -> (Path.T * bool) list -> bool -> theory
  val end_theory: theory -> theory
  val register_thy: string -> unit
  val register_theory: theory -> unit
  val finish: unit -> unit
end;

structure ThyInfo: THY_INFO =
struct

(** theory loader actions and hooks **)

datatype action = Update | Outdate | Remove;
val str_of_action = fn Update => "Update" | Outdate => "Outdate" | Remove => "Remove";

local
  val hooks = ref ([]: (action -> string -> unit) list);
in
  fun add_hook f = CRITICAL (fn () => change hooks (cons f));
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

fun new_deps name parents entry G =
  (if can (Graph.get_node G) name then upd_deps name entry G else Graph.new_node (name, entry) G)
  |> add_deps name parents;


(* thy database *)

type deps =
  {update_time: int,                      (*symbolic time of update; negative value means outdated*)
    master: (Path.T * File.ident) option, (*master dependencies for thy file*)
    text: string list,                    (*source text for thy*)
    parents: string list,                 (*source specification of parents (partially qualified)*)
      (*auxiliary files: source path, physical path + identifier*)
    files: (Path.T * (Path.T * File.ident) option) list};

fun make_deps update_time master text parents files : deps =
  {update_time = update_time, master = master, text = text, parents = parents, files = files};

fun init_deps master text parents files =
  SOME (make_deps ~1 master text parents (map (rpair NONE) files));

fun master_dir NONE = Path.current
  | master_dir (SOME (path, _)) = Path.dir path;

fun master_dir' (d: deps option) = the_default Path.current (Option.map (master_dir o #master) d);
fun master_dir'' d = the_default Path.current (Option.map master_dir' d);

fun base_name s = Path.implode (Path.base (Path.explode s));


type thy = deps option * theory option;

local
  val database = ref (Graph.empty: thy Graph.T);
in
  fun get_thys () = ! database;
  fun change_thys f = CRITICAL (fn () => Library.change database f);
end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;

fun get_names () = Graph.topological_order (get_thys ());


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

fun change_thy name f = CRITICAL (fn () =>
  (get_thy name; change_thys (Graph.map_node name f)));


(* access deps *)

val lookup_deps = Option.map #1 o lookup_thy;
val get_deps = #1 o get_thy;
fun change_deps name f = change_thy name (fn (deps, x) => (f deps, x));

fun is_finished name = is_none (get_deps name);

fun loaded_files name =
  (case get_deps name of
    NONE => []
  | SOME {master, files, ...} =>
      (case master of SOME (thy_path, _) => [thy_path] | NONE => []) @
      (map_filter (Option.map #1 o #2) files));

fun get_parents name =
  thy_graph Graph.imm_preds name handle Graph.UNDEF _ =>
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

(* check state *)

fun check_unfinished fail name =
  if known_thy name andalso is_finished name then
    fail (loader_msg "cannot update finished theory" [name])
  else ();

fun check_files name =
  let
    val files = (case get_deps name of SOME {files, ...} => files | NONE => []);
    val missing_files = map_filter (fn (path, NONE) => SOME (Path.implode path) | _ => NONE) files;
    val _ = null missing_files orelse
      error (loader_msg "unresolved dependencies of theory" [name] ^
        " on file(s): " ^ commas_quote missing_files);
  in () end;


(* maintain update_time *)

local

fun is_outdated name =
  (case lookup_deps name of
    SOME (SOME {update_time, ...}) => update_time < 0
  | _ => false);

fun check_unfinished name =
  if is_finished name then (warning (loader_msg "tried to touch finished theory" [name]); NONE)
  else SOME name;

in

fun outdate_thy name =
  if is_finished name orelse is_outdated name then ()
  else CRITICAL (fn () =>
   (change_deps name (Option.map (fn {master, text, parents, files, ...} =>
    make_deps ~1 master text parents files)); perform Outdate name));

fun touch_thys names =
  List.app outdate_thy (thy_graph Graph.all_succs (map_filter check_unfinished names));

fun touch_thy name = touch_thys [name];
fun touch_child_thys name = touch_thys (thy_graph Graph.imm_succs name);

fun touch_all_thys () = List.app outdate_thy (get_names ());

end;


(* load_file *)

local

fun provide path name info (deps as SOME {update_time, master, text, parents, files}) =
     (if AList.defined (op =) files path then ()
      else warning (loader_msg "undeclared dependency of theory" [name] ^
        " on file: " ^ quote (Path.implode path));
      SOME (make_deps update_time master text parents
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

fun load_file time path =
  if time then
    let val name = Path.implode path in
      timeit (fn () =>
       (priority ("\n**** Starting file " ^ quote name ^ " ****");
        run_file path;
        priority ("**** Finished file " ^ quote name ^ " ****\n")))
    end
  else run_file path;

val use = load_file false o Path.explode;
val time_use = load_file true o Path.explode;

end;


(* load_thy *)

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy time upd_time initiators dir name =
  let
    val _ = priority ("Loading theory " ^ quote name ^ required_by " " initiators);
    val (pos, text, files) =
      (case get_deps name of
        SOME {master = SOME (master_path, _), text as _ :: _, files, ...} =>
          (Position.path master_path, text, files)
      | _ => error (loader_msg "corrupted dependency information" [name]));
    val _ = touch_thy name;
    val _ = CRITICAL (fn () =>
      change_deps name (Option.map (fn {master, text, parents, files, ...} =>
        make_deps upd_time master text parents files)));
    val _ = ThyLoad.load_thy dir name pos text (time orelse ! Output.timing);
  in
    CRITICAL (fn () =>
     (change_deps name
        (Option.map (fn {update_time, master, parents, files, ...} =>
          make_deps update_time master [] parents files));
      perform Update name))
  end;


(* scheduling loader tasks *)

datatype task = Task of (unit -> unit) | Finished | Running;
fun task_finished Finished = true | task_finished _ = false;

local

fun max_task (name, (Task body, m)) NONE = SOME (name: string, (body, m))
  | max_task (name, (Task body, m)) (task' as SOME (name', (_, m'))) =
      if m > m' orelse m = m' andalso name < name' then SOME (name, (body, m)) else task'
  | max_task _ task' = task';

fun next_task G =
  let
    val tasks = Graph.minimals G |> map (fn name =>
      (name, (Graph.get_node G name, length (Graph.imm_succs G name))));
    val finished = filter (task_finished o fst o snd) tasks;
  in
    if not (null finished) then next_task (Graph.del_nodes (map fst finished) G)
    else if null tasks then (Multithreading.Terminate, G)
    else
      (case fold max_task tasks NONE of
        NONE => (Multithreading.Wait, G)
      | SOME (name, (body, _)) =>
         (Multithreading.Task {body = body, cont = Graph.del_nodes [name], fail = K Graph.empty},
          Graph.map_node name (K Running) G))
  end;

fun schedule_seq tasks =
  Graph.topological_order tasks
  |> List.app (fn name => (case Graph.get_node tasks name of Task body => body () | _ => ()));

in

fun schedule_tasks tasks n =
  let val m = ! Multithreading.max_threads in
    if m <= 1 orelse n <= 1 then schedule_seq tasks
    else if Multithreading.self_critical () then
     (warning (loader_msg "no multithreading within critical section" []);
      schedule_seq tasks)
    else
      (case Multithreading.schedule (Int.min (m, n)) next_task tasks of
        [] => ()
      | exns => raise Exn.EXCEPTIONS (exns, ""))
  end;

end;


(* require_thy -- checking database entries wrt. the file-system *)

local

fun check_ml master (src_path, info) =
  let val info' =
    (case info of NONE => NONE
    | SOME (_, id) =>
        (case ThyLoad.check_ml (master_dir master) src_path of NONE => NONE
        | SOME (path', id') => if id <> id' then NONE else SOME (path', id')))
  in (src_path, info') end;

fun check_deps dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, get_parents name)
  | NONE =>
      let val {master, text, imports = parents, uses = files} = ThyLoad.deps_thy dir name
      in (false, init_deps (SOME master) text parents files, parents) end
  | SOME (deps as SOME {update_time, master, text, parents, files}) =>
      let
        val (thy_path, thy_id) = ThyLoad.check_thy dir name;
        val master' = SOME (thy_path, thy_id);
      in
        if Option.map #2 master <> SOME thy_id then
          let val {text = text', imports = parents', uses = files', ...} =
            ThyLoad.deps_thy dir name;
          in (false, init_deps master' text' parents' files', parents') end
        else
          let
            val files' = map (check_ml master') files;
            val current = update_time >= 0 andalso can get_theory name
              andalso forall (is_some o snd) files';
            val update_time' = if current then update_time else ~1;
            val text' = if current then text else explode (File.read thy_path);
            val deps' = SOME (make_deps update_time' master' text' parents files');
          in (current, deps', parents) end
      end);

in

fun require_thys time initiators dir strs tasks =
      fold_map (require_thy time initiators dir) strs tasks |>> forall I
and require_thy time initiators dir str tasks =
  let
    val path = Path.expand (Path.explode str);
    val name = Path.implode (Path.base path);
    val dir' = Path.append dir (Path.dir path);
    val _ = member (op =) initiators name andalso error (cycle_msg initiators);
  in
    (case try (Graph.get_node (fst tasks)) name of
      SOME task => (task_finished task, tasks)
    | NONE =>
        let
          val (current, deps, parents) = check_deps dir' name
            handle ERROR msg => cat_error msg
              (loader_msg "the error(s) above occurred while examining theory" [name] ^
                required_by "\n" initiators);
          val parent_names = map base_name parents;

          val (parents_current, (tasks_graph', tasks_len')) =
            require_thys time (name :: initiators)
              (Path.append dir (master_dir' deps)) parents tasks;

          val all_current = current andalso parents_current;
          val theory = if all_current then SOME (get_theory name) else NONE;
          val _ = if not all_current andalso known_thy name then outdate_thy name else ();
          val _ = change_thys (new_deps name parent_names (deps, theory));

          val upd_time = serial ();
          val tasks_graph'' = tasks_graph' |> new_deps name parent_names
           (if all_current then Finished
            else Task (fn () => load_thy time upd_time initiators dir' name));
          val tasks_len'' = if all_current then tasks_len' else tasks_len' + 1;
        in (all_current, (tasks_graph'', tasks_len'')) end)
  end;

end;


(* use_thy etc. *)

local

fun gen_use_thy' req dir arg =
  let val (_, (tasks, n)) = req [] dir arg (Graph.empty, 0)
  in schedule_tasks tasks n end;

fun gen_use_thy req str =
  let val name = base_name str in
    check_unfinished warning name;
    gen_use_thy' req Path.current str;
    CRITICAL (fn () => ML_Context.set_context (SOME (Context.Theory (get_theory name))))
  end;

in

val use_thys_dir = gen_use_thy' (require_thys false);
val use_thys = use_thys_dir Path.current;
val use_thy = gen_use_thy (require_thy false);
val time_use_thy = gen_use_thy (require_thy true);

end;


(* remove_thy *)

fun remove_thy name =
  if is_finished name then error (loader_msg "cannot remove finished theory" [name])
  else
    let val succs = thy_graph Graph.all_succs [name] in
      priority (loader_msg "removing" succs);
      CRITICAL (fn () => (List.app (perform Remove) succs; change_thys (Graph.del_nodes succs)))
    end;


(* begin / end theory *)

fun begin_theory name parents uses int =
  let
    val parent_names = map base_name parents;
    val dir = master_dir'' (lookup_deps name);
    val _ = check_unfinished error name;
    val _ = if int then use_thys_dir dir parents else ();
    (* FIXME tmp *)
    val _ = CRITICAL (fn () =>
      ML_Context.set_context (SOME (Context.Theory (get_theory (List.last parent_names)))));

    val theory = Theory.begin_theory name (map get_theory parent_names);

    val deps =
      if known_thy name then get_deps name
      else init_deps NONE [] parents (map #1 uses);
    val _ = change_thys (new_deps name parent_names (deps, NONE));

    val update_time = (case deps of NONE => 0 | SOME {update_time, ...} => update_time);
    val theory' = Present.begin_theory update_time dir uses theory;

    val uses_now = map_filter (fn (x, true) => SOME x | _ => NONE) uses;
    val ((), theory'') =
      ML_Context.pass_context (Context.Theory theory') (List.app (load_file false)) uses_now
      ||> Context.the_theory;
  in theory'' end;

fun end_theory theory =
  let
    val name = Context.theory_name theory;
    val _ = check_files name;
    val theory' = Theory.end_theory theory;
    val _ = change_thy name (fn (deps, _) => (deps, SOME theory'));
  in theory' end;


(* register existing theories *)

fun register_thy name =
  let
    val _ = priority ("Registering theory " ^ quote name);
    val _ = get_theory name;
    val _ = map get_theory (get_parents name);
    val _ = check_unfinished error name;
    val _ = touch_thy name;
    val master = #master (ThyLoad.deps_thy Path.current name);
    val upd_time = serial ();
  in
    CRITICAL (fn () =>
     (change_deps name (Option.map
       (fn {parents, files, ...} => make_deps upd_time (SOME master) [] parents files));
      perform Update name))
  end;

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
    else CRITICAL (fn () => (change_thys register; perform Update name))
  end;

val _ = register_theory ProtoPure.thy;


(* finish all theories *)

fun finish () = change_thys (Graph.map_nodes (fn (_, entry) => (NONE, entry)));


(*final declarations of this structure*)
val theory = get_theory;
val names = get_names;

end;

structure BasicThyInfo: BASIC_THY_INFO = ThyInfo;
open BasicThyInfo;

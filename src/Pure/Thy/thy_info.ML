(*  Title:      Pure/Thy/thy_info.ML
    Author:     Markus Wenzel, TU Muenchen

Global theory info database, with auto-loading according to theory and
file dependencies.
*)

signature THY_INFO =
sig
  datatype action = Update | Remove
  val add_hook: (action -> string -> unit) -> unit
  val get_names: unit -> string list
  val lookup_theory: string -> theory option
  val get_theory: string -> theory
  val is_finished: string -> bool
  val master_directory: string -> Path.T
  val loaded_files: string -> Path.T list
  val remove_thy: string -> unit
  val kill_thy: string -> unit
  val use_thys: string list -> unit
  val use_thy: string -> unit
  val toplevel_begin_theory: string -> string list -> (Path.T * bool) list -> theory
  val register_thy: theory -> unit
  val finish: unit -> unit
end;

structure Thy_Info: THY_INFO =
struct

(** theory loader actions and hooks **)

datatype action = Update | Remove;

local
  val hooks = Unsynchronized.ref ([]: (action -> string -> unit) list);
in
  fun add_hook f = CRITICAL (fn () => Unsynchronized.change hooks (cons f));
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

fun new_entry name parents entry =
  Graph.new_node (name, entry) #> add_deps name parents;


(* thy database *)

type deps =
 {master: (Path.T * File.ident),  (*master dependencies for thy file*)
  parents: string list};          (*source specification of parents (partially qualified)*)

fun make_deps master parents : deps = {master = master, parents = parents};

fun master_dir (d: deps option) = the_default Path.current (Option.map (Path.dir o #1 o #master) d);
fun base_name s = Path.implode (Path.base (Path.explode s));

local
  val database = Unsynchronized.ref (Graph.empty: (deps option * theory option) Graph.T);
in
  fun get_thys () = ! database;
  fun change_thys f = CRITICAL (fn () => Unsynchronized.change database f);
end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;

fun get_names () = Graph.topological_order (get_thys ());


(* access thy *)

fun lookup_thy name =
  SOME (thy_graph Graph.get_node name) handle Graph.UNDEF _ => NONE;

val known_thy = is_some o lookup_thy;

fun get_thy name =
  (case lookup_thy name of
    SOME thy => thy
  | NONE => error (loader_msg "nothing known about theory" [name]));


(* access deps *)

val lookup_deps = Option.map #1 o lookup_thy;
val get_deps = #1 o get_thy;

val is_finished = is_none o get_deps;
val master_directory = master_dir o get_deps;

fun get_parents name =
  thy_graph Graph.imm_preds name handle Graph.UNDEF _ =>
    error (loader_msg "nothing known about theory" [name]);


(* access theory *)

fun lookup_theory name =
  (case lookup_thy name of
    SOME (_, SOME thy) => SOME thy
  | _ => NONE);

fun get_theory name =
  (case lookup_theory name of
    SOME theory => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

fun loaded_files name =
  (case get_deps name of
    NONE => []
  | SOME {master = (thy_path, _), ...} => thy_path :: Thy_Load.loaded_files (get_theory name));



(** thy operations **)

(* abstract update time *)

structure Update_Time = Theory_Data
(
  type T = int;
  val empty = 0;
  fun extend _ = empty;
  fun merge _ = empty;
);


(* remove theory *)

fun remove_thy name =
  if is_finished name then error (loader_msg "attempt to change finished theory" [name])
  else
    let
      val succs = thy_graph Graph.all_succs [name];
      val _ = priority (loader_msg "removing" succs);
      val _ = CRITICAL (fn () =>
        (List.app (perform Remove) succs; change_thys (Graph.del_nodes succs)));
    in () end;

fun kill_thy name =
  if known_thy name then remove_thy name
  else ();


(* scheduling loader tasks *)

datatype task =
  Task of string list * (theory list -> (theory * (unit -> unit))) |
  Finished of theory;

fun task_finished (Task _) = false
  | task_finished (Finished _) = true;

local

fun schedule_seq task_graph =
  ((Graph.topological_order task_graph, Symtab.empty) |-> fold (fn name => fn tab =>
    (case Graph.get_node task_graph name of
      Task (parents, body) =>
        let
          val (thy, after_load) = body (map (the o Symtab.lookup tab) parents);
          val _ = after_load ();
        in Symtab.update (name, thy) tab end
    | Finished thy => Symtab.update (name, thy) tab))) |> ignore;

fun schedule_futures task_graph = uninterruptible (fn _ => fn () =>
  let
    val tasks = Graph.topological_order task_graph;
    val par_proofs = ! parallel_proofs >= 1;

    val futures = (tasks, Symtab.empty) |-> fold (fn name => fn tab =>
      (case Graph.get_node task_graph name of
        Task (parents, body) =>
          let
            val get = the o Symtab.lookup tab;
            val deps = map (`get) (Graph.imm_preds task_graph name);
            fun failed (future, parent) = if can Future.join future then NONE else SOME parent;

            val future = Future.fork_deps (map #1 deps) (fn () =>
              (case map_filter failed deps of
                [] => body (map (#1 o Future.join o get) parents)
              | bad => error (loader_msg
                  ("failed to load " ^ quote name ^ " (unresolved " ^ commas_quote bad ^ ")") [])));
            val future' =
              if par_proofs then future
              else Future.map (fn (thy, after_load) => (after_load (); (thy, I))) future;
          in Symtab.update (name, future') tab end
      | Finished thy => Symtab.update (name, Future.value (thy, I)) tab));

    val _ =
      tasks |> maps (fn name =>
        let
          val (thy, after_load) = Future.join (the (Symtab.lookup futures name));
          val _ = PureThy.join_proofs thy;
          val _ = after_load ();
        in [] end handle exn => [Exn.Exn exn])
      |> rev |> Exn.release_all;
  in () end) ();

in

fun schedule_tasks tasks =
  if not (Multithreading.enabled ()) then schedule_seq tasks
  else if Multithreading.self_critical () then
     (warning (loader_msg "no multithreading within critical section" []);
      schedule_seq tasks)
  else schedule_futures tasks;

end;


(* require_thy -- checking database entries wrt. the file-system *)

local

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy initiators update_time (deps: deps) text name parent_thys =
  let
    val _ = kill_thy name;
    val _ = priority ("Loading theory " ^ quote name ^ required_by " " initiators);

    val {master = (thy_path, _), ...} = deps;
    val dir = Path.dir thy_path;
    val pos = Path.position thy_path;
    val uses = map (apfst Path.explode) (#3 (Thy_Header.read pos text));
    fun init () =
      Thy_Load.begin_theory dir name parent_thys uses
      |> Present.begin_theory update_time dir uses
      |> Update_Time.put update_time;

    val (after_load, theory) = Outer_Syntax.load_thy name init pos text;

    val parent_names = map Context.theory_name parent_thys;
    fun after_load' () =
     (after_load ();
      CRITICAL (fn () =>
        (change_thys (new_entry name parent_names (SOME deps, SOME theory));
          perform Update name)));

  in (theory, after_load') end;

fun check_deps dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, get_parents name, NONE)
  | NONE =>
      let val {master, text, imports = parents, ...} = Thy_Load.deps_thy dir name
      in (false, SOME (make_deps master parents), parents, SOME text) end
  | SOME (SOME {master, parents}) =>
      let val master' = Thy_Load.check_thy dir name in
        if #2 master <> #2 master' then
          let val {text = text', imports = parents', ...} = Thy_Load.deps_thy dir name;
          in (false, SOME (make_deps master' parents'), parents', SOME text') end
        else
          let
            val current =
              (case lookup_theory name of
                NONE => false
              | SOME theory => Thy_Load.all_current theory);
            val deps' = SOME (make_deps master' parents);
          in (current, deps', parents, NONE) end
      end);

in

fun require_thys initiators dir strs tasks =
      fold_map (require_thy initiators dir) strs tasks |>> forall I
and require_thy initiators dir str tasks =
  let
    val path = Path.expand (Path.explode str);
    val name = Path.implode (Path.base path);
    val dir' = Path.append dir (Path.dir path);
    val _ = member (op =) initiators name andalso error (cycle_msg initiators);
  in
    (case try (Graph.get_node tasks) name of
      SOME task => (task_finished task, tasks)
    | NONE =>
        let
          val (current, deps, parents, opt_text) = check_deps dir' name
            handle ERROR msg => cat_error msg
              (loader_msg "the error(s) above occurred while examining theory" [name] ^
                required_by "\n" initiators);

          val parent_names = map base_name parents;
          val (parents_current, tasks') =
            require_thys (name :: initiators) (Path.append dir (master_dir deps)) parents tasks;

          val all_current = current andalso parents_current;
          val task =
            if all_current then Finished (get_theory name)
            else
              (case deps of
                NONE => raise Fail "Malformed deps"
              | SOME (dep as {master = (thy_path, _), ...}) =>
                  let
                    val text = (case opt_text of SOME text => text | NONE => File.read thy_path);
                    val update_time = serial ();
                  in Task (parent_names, load_thy initiators update_time dep text name) end);
        in (all_current, new_entry name parent_names task tasks') end)
  end;

end;


(* use_thy *)

fun use_thys_dir dir arg =
  schedule_tasks (snd (require_thys [] dir arg Graph.empty));

val use_thys = use_thys_dir Path.current;
val use_thy = use_thys o single;


(* toplevel begin theory -- without maintaining database *)

fun toplevel_begin_theory name imports uses =
  let
    val dir = Thy_Load.get_master_path ();
    val _ = kill_thy name;
    val _ = use_thys_dir dir imports;
    val parents = map (get_theory o base_name) imports;
  in Thy_Load.begin_theory dir name parents uses end;


(* register theory *)

fun register_thy theory =
  let
    val name = Context.theory_name theory;
    val _ = kill_thy name;
    val _ = priority ("Registering theory " ^ quote name);

    val master = Thy_Load.check_thy (Thy_Load.master_directory theory) name;
    val parents = map Context.theory_name (Theory.parents_of theory);
    val deps = make_deps master parents;
  in
    CRITICAL (fn () =>
     (map get_theory parents;
      change_thys (new_entry name parents (SOME deps, SOME theory));
      perform Update name))
  end;


(* finish all theories *)

fun finish () = change_thys (Graph.map_nodes (fn (_, entry) => (NONE, entry)));

end;

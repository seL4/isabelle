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
  val use_thys_wrt: Path.T -> (string * Position.T) list -> unit
  val use_thys: (string * Position.T) list -> unit
  val use_thy: string * Position.T -> unit
  val toplevel_begin_theory: Path.T -> Thy_Header.header -> theory
  val register_thy: theory -> unit
  val finish: unit -> unit
end;

structure Thy_Info: THY_INFO =
struct

(** theory loader actions and hooks **)

datatype action = Update | Remove;

local
  val hooks = Synchronized.var "Thy_Info.hooks" ([]: (action -> string -> unit) list);
in
  fun add_hook f = Synchronized.change hooks (cons f);
  fun perform action name =
    List.app (fn f => (try (fn () => f action name) (); ())) (Synchronized.value hooks);
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
 {master: (Path.T * SHA1.digest),  (*master dependencies for thy file*)
  imports: (string * Position.T) list};  (*source specification of imports (partially qualified)*)

fun make_deps master imports : deps = {master = master, imports = imports};

fun master_dir (d: deps option) = the_default Path.current (Option.map (Path.dir o #1 o #master) d);
fun base_name s = Path.implode (Path.base (Path.explode s));

local
  val database = Unsynchronized.ref (Graph.empty: (deps option * theory option) Graph.T);
in
  fun get_thys () = ! database;
  fun change_thys f = NAMED_CRITICAL "Thy_Info" (fn () => Unsynchronized.change database f);
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


(* access theory *)

fun lookup_theory name =
  (case lookup_thy name of
    SOME (_, SOME theory) => SOME theory
  | _ => NONE);

fun get_theory name =
  (case lookup_theory name of
    SOME theory => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

val get_imports = Thy_Load.imports_of o get_theory;

fun loaded_files name = NAMED_CRITICAL "Thy_Info" (fn () =>
  (case get_deps name of
    NONE => []
  | SOME {master = (thy_path, _), ...} => thy_path :: Thy_Load.loaded_files (get_theory name)));



(** thy operations **)

(* main loader actions *)

fun remove_thy name = NAMED_CRITICAL "Thy_Info" (fn () =>
  if is_finished name then error (loader_msg "attempt to change finished theory" [name])
  else
    let
      val succs = thy_graph Graph.all_succs [name];
      val _ = Output.urgent_message (loader_msg "removing" succs);
      val _ = List.app (perform Remove) succs;
      val _ = change_thys (fold Graph.del_node succs);
    in () end);

fun kill_thy name = NAMED_CRITICAL "Thy_Info" (fn () =>
  if known_thy name then remove_thy name
  else ());

fun update_thy deps theory = NAMED_CRITICAL "Thy_Info" (fn () =>
  let
    val name = Context.theory_name theory;
    val parents = map Context.theory_name (Theory.parents_of theory);
    val _ = kill_thy name;
    val _ = map get_theory parents;
    val _ = change_thys (new_entry name parents (SOME deps, SOME theory));
    val _ = perform Update name;
  in () end);


(* scheduling loader tasks *)

type result = theory * unit future * (unit -> unit);

datatype task =
  Task of string list * (theory list -> result) |
  Finished of theory;

fun task_finished (Task _) = false
  | task_finished (Finished _) = true;

fun task_parents deps (parents: string list) = map (the o AList.lookup (op =) deps) parents;

local

fun finish_thy ((thy, present, commit): result) =
  (Global_Theory.join_proofs thy; Future.join present; commit (); thy);

val schedule_seq =
  Graph.schedule (fn deps => fn (_, task) =>
    (case task of
      Task (parents, body) => finish_thy (body (task_parents deps parents))
    | Finished thy => thy)) #> ignore;

val schedule_futures = uninterruptible (fn _ =>
  Graph.schedule (fn deps => fn (name, task) =>
    (case task of
      Task (parents, body) =>
        (singleton o Future.forks)
          {name = "theory:" ^ name, group = NONE,
            deps = map (Future.task_of o #2) deps, pri = 0, interrupts = true}
          (fn () =>
            (case filter (not o can Future.join o #2) deps of
              [] => body (map (#1 o Future.join) (task_parents deps parents))
            | bad =>
                error (loader_msg ("failed to load " ^ quote name ^
                  " (unresolved " ^ commas_quote (map #1 bad) ^ ")") [])))
    | Finished thy => Future.value (thy, Future.value (), I)))
  #> maps (fn result => (finish_thy (Future.join result); []) handle exn => [Exn.Exn exn])
  #> rev #> Par_Exn.release_all) #> ignore;

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

fun load_thy initiators update_time deps text (name, pos) uses keywords parents =
  let
    val _ = kill_thy name;
    val _ = Output.urgent_message ("Loading theory " ^ quote name ^ required_by " " initiators);

    val {master = (thy_path, _), imports} = deps;
    val dir = Path.dir thy_path;
    val header = Thy_Header.make (name, pos) imports keywords uses;

    val _ = Position.reports (map #2 imports ~~ map Theory.get_markup parents);

    val (theory, present) =
      Thy_Load.load_thy update_time dir header (Path.position thy_path) text
        (if name = Context.PureN then [ML_Context.the_global_context ()] else parents);
    fun commit () = update_thy deps theory;
  in (theory, present, commit) end;

fun check_deps dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, Position.none, get_imports name, [], [])
  | NONE =>
      let val {master, text, theory_pos, imports, keywords, uses} = Thy_Load.check_thy dir name
      in (false, SOME (make_deps master imports, text), theory_pos, imports, uses, keywords) end
  | SOME (SOME {master, ...}) =>
      let
        val {master = master', text = text', theory_pos = theory_pos', imports = imports',
          uses = uses', keywords = keywords'} = Thy_Load.check_thy dir name;
        val deps' = SOME (make_deps master' imports', text');
        val current =
          #2 master = #2 master' andalso
            (case lookup_theory name of
              NONE => false
            | SOME theory => Thy_Load.load_current theory);
      in (current, deps', theory_pos', imports', uses', keywords') end);

in

fun require_thys initiators dir strs tasks =
      fold_map (require_thy initiators dir) strs tasks |>> forall I
and require_thy initiators dir (str, require_pos) tasks =
  let
    val path = Path.expand (Path.explode str);
    val name = Path.implode (Path.base path);
  in
    (case try (Graph.get_node tasks) name of
      SOME task => (task_finished task, tasks)
    | NONE =>
        let
          val dir' = Path.append dir (Path.dir path);
          val _ = member (op =) initiators name andalso error (cycle_msg initiators);

          val (current, deps, theory_pos, imports, uses, keywords) = check_deps dir' name
            handle ERROR msg => cat_error msg
              (loader_msg "the error(s) above occurred while examining theory" [name] ^
                Position.here require_pos ^ required_by "\n" initiators);

          val parents = map (base_name o #1) imports;
          val (parents_current, tasks') =
            require_thys (name :: initiators)
              (Path.append dir (master_dir (Option.map #1 deps))) imports tasks;

          val all_current = current andalso parents_current;
          val task =
            if all_current then Finished (get_theory name)
            else
              (case deps of
                NONE => raise Fail "Malformed deps"
              | SOME (dep, text) =>
                  let
                    val update_time = serial ();
                    val load =
                      load_thy initiators update_time dep text (name, theory_pos) uses keywords;
                  in Task (parents, load) end);

          val tasks'' = new_entry name parents task tasks';
        in (all_current, tasks'') end)
  end;

end;


(* use_thy *)

fun use_thys_wrt dir arg =
  schedule_tasks (snd (require_thys [] dir arg Graph.empty));

val use_thys = use_thys_wrt Path.current;
val use_thy = use_thys o single;


(* toplevel begin theory -- without maintaining database *)

fun toplevel_begin_theory master_dir (header: Thy_Header.header) =
  let
    val {name = (name, _), imports, ...} = header;
    val _ = kill_thy name;
    val _ = use_thys_wrt master_dir imports;
    val _ = Thy_Header.define_keywords header;
    val parents = map (get_theory o base_name o fst) imports;
  in Thy_Load.begin_theory master_dir header parents end;


(* register theory *)

fun register_thy theory =
  let
    val name = Context.theory_name theory;
    val {master, ...} = Thy_Load.check_thy (Thy_Load.master_directory theory) name;
    val imports = Thy_Load.imports_of theory;
  in
    NAMED_CRITICAL "Thy_Info" (fn () =>
     (kill_thy name;
      Output.urgent_message ("Registering theory " ^ quote name);
      update_thy (make_deps master imports) theory))
  end;


(* finish all theories *)

fun finish () = change_thys (Graph.map (fn _ => fn (_, entry) => (NONE, entry)));

end;

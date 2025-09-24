(*  Title:      Pure/Thy/thy_info.ML
    Author:     Makarius

Global theory info database, with auto-loading according to theory and
file dependencies, and presentation of theory documents.
*)

signature THY_INFO =
sig
  type presentation_context =
    {options: Options.T, file_pos: Position.T, adjust_pos: Position.T -> Position.T,
      segments: Document_Output.segment list}
  val adjust_pos_properties: presentation_context -> Position.T -> Properties.T
  val apply_presentation: presentation_context -> theory -> unit
  val add_presentation: (presentation_context -> theory -> unit) -> theory -> theory
  val get_names: unit -> string list
  val lookup_theory: string -> theory option
  val defined_theory: string -> bool
  val get_theory: string -> theory
  val get_theory_segments: string -> Document_Output.segment list
  val get_theory_elements: string -> Document_Output.segment Thy_Element.element list
  val check_theory: Proof.context -> string * Position.T -> theory
  val master_directory: string -> Path.T
  val remove_thy: string -> unit
  val use_theories: Options.T -> string -> (string * Position.T) list ->
    (theory * Document_Output.segment list) list
  val use_thy: string -> unit
  val finish: unit -> unit
end;

structure Thy_Info: THY_INFO =
struct

(** theory presentation **)

(* hook for consolidated theory *)

type presentation_context =
  {options: Options.T, file_pos: Position.T, adjust_pos: Position.T -> Position.T,
    segments: Document_Output.segment list};

fun adjust_pos_properties (context: presentation_context) pos =
  let
    val props = Position.properties_of pos;
    val props' = Position.properties_of (#adjust_pos context pos);
  in
    filter (fn (a, _) => a = Markup.offsetN orelse a = Markup.end_offsetN) props' @
    filter (fn (a, _) => a = Markup.labelN orelse a = Markup.fileN orelse a = Markup.idN) props
  end;

structure Presentation = Theory_Data
(
  type T = ((presentation_context -> theory -> unit) * stamp) list;
  val empty = [];
  fun merge data : T = Library.merge (eq_snd op =) data;
);

fun apply_presentation (context: presentation_context) thy =
  ignore (Par_List.map (fn (f, _) => f context thy) (Presentation.get thy));

fun add_presentation f = Presentation.map (cons (f, stamp ()));

val _ =
  Theory.setup (add_presentation (fn {options, segments, ...} => fn thy =>
    if exists (Toplevel.is_skipped_proof o #state) segments then ()
    else
      let
        val keywords = Thy_Header.get_keywords thy;
        val thy_name = Context.theory_base_name thy;
        val latex = Document_Output.present_thy options keywords thy_name segments;
      in
        if Options.string options "document" = "false" then ()
        else Export.export thy \<^path_binding>\<open>document/latex\<close> latex
      end));



(** thy database **)

(* messages *)

val show_path = space_implode " via " o map quote;

fun cycle_msg names = "Cyclic dependency of " ^ show_path names;


(* derived graph operations *)

fun add_deps name parents G = String_Graph.add_deps_acyclic (name, parents) G
  handle String_Graph.CYCLES namess => error (cat_lines (map cycle_msg namess));

fun new_entry name parents entry =
  String_Graph.new_node (name, entry) #> add_deps name parents;


(* global thys *)

type deps =
 {master: (Path.T * SHA1.digest),  (*master dependencies for thy file*)
  imports: (string * Position.T) list};  (*source specification of imports (partially qualified)*)

fun make_deps master imports : deps = {master = master, imports = imports};

fun master_dir_deps (d: deps option) =
  the_default Path.current (Option.map (Path.dir o #1 o #master) d);

local
  type thy = deps option * (theory * Document_Output.segment list) option;
  val global_thys = Synchronized.var "Thy_Info.thys" (String_Graph.empty: thy String_Graph.T);
in
  fun get_thys () = Synchronized.value global_thys;
  fun change_thys f = Synchronized.change global_thys f;
end;

fun get_names () = String_Graph.topological_order (get_thys ());


(* access thy *)

fun lookup thys name = try (String_Graph.get_node thys) name;
fun lookup_thy name = lookup (get_thys ()) name;

fun get thys name =
  (case lookup thys name of
    SOME thy => thy
  | NONE => error ("Theory loader: nothing known about theory " ^ quote name));

fun get_thy name = get (get_thys ()) name;


(* access deps *)

val lookup_deps = Option.map #1 o lookup_thy;

val master_directory = master_dir_deps o #1 o get_thy;


(* access theory *)

fun lookup_theory name =
  (case lookup_thy name of
    SOME (_, SOME (theory, _)) => SOME theory
  | _ => NONE);

val defined_theory = is_some o lookup_theory;

fun get_theory name =
  (case lookup_theory name of
    SOME theory => theory
  | _ => error ("Theory loader: undefined entry for theory " ^ quote name));

fun get_theory_segments name =
  let
    val _ = get_theory name;
    val segments =
      (case lookup_thy name of
        SOME (_, SOME (_, segments)) => segments
      | _ => []);
  in
    if null segments then
      error ("Theory loader: no theory segments for theory " ^ quote name ^
        "\n Need to build with option " ^ quote \<^system_option>\<open>record_theories\<close>)
    else segments
  end;

fun get_theory_elements name =
  let
    val keywords = Thy_Header.get_keywords (get_theory name);
    val stopper = Document_Output.segment_stopper;
    val segments = get_theory_segments name;
  in Thy_Element.parse_elements_generic keywords #span stopper segments end;


val get_imports = Resources.imports_of o get_theory;

val check_theory = Theory.check_theory {get = get_theory, all = get_names};



(** thy operations **)

(* remove *)

fun remove name thys =
  (case lookup thys name of
    NONE => thys
  | SOME (NONE, _) => error ("Cannot update finished theory " ^ quote name)
  | SOME _ =>
      let
        val succs = String_Graph.all_succs thys [name];
        val _ = writeln ("Theory loader: removing " ^ commas_quote succs);
      in fold String_Graph.del_node succs thys end);

val remove_thy = change_thys o remove;


(* update *)

fun update deps (res as (theory, _)) thys =
  let
    val name = Context.theory_long_name theory;
    val parents = map Context.theory_long_name (Theory.parents_of theory);

    val thys' = remove name thys;
    val _ = List.app (ignore o get thys') parents;
  in new_entry name parents (SOME deps, SOME res) thys' end;

val update_thy = change_thys oo update;


(* scheduling loader tasks *)

datatype result =
  Result of
   {theory: theory,
    exec_id: Document_ID.exec,
    present: unit -> presentation_context option,
    commit: Document_Output.segment list -> unit};

fun theory_result theory =
  Result
   {theory = theory,
    exec_id = Document_ID.none,
    present = K NONE,
    commit = K ()};

fun result_theory (Result {theory, ...}) = theory;
fun result_commit (Result {commit, ...}) = commit;

datatype task =
  Task of string list * (theory list -> result) |
  Finished of theory;

local

fun consolidate_theory (Exn.Exn exn) = [Exn.Exn exn]
  | consolidate_theory (Exn.Res (Result {theory, exec_id, ...})) =
      let
        val _ = Execution.join [exec_id];
        val result = Exn.capture Thm.consolidate_theory theory;
        val exns = maps Task_Queue.group_status (Execution.peek exec_id);
      in result :: map Exn.Exn exns end;

fun present_theory (Exn.Exn exn) = SOME (Exn.Exn exn)
  | present_theory (Exn.Res (Result {theory, present, ...})) =
      present () |> Option.map (fn context as {segments, ...} =>
        Exn.capture_body (fn () => (apply_presentation context theory; (theory, segments))));

in

val schedule_theories = Thread_Attributes.uninterruptible (fn _ => fn tasks =>
  let
    fun join_parents deps name parents =
      (case map #1 (filter (not o can Future.join o #2) deps) of
        [] => map (result_theory o Future.join o the o AList.lookup (op =) deps) parents
      | bad =>
          error ("Failed to load theory " ^ quote name ^ " (unresolved " ^ commas_quote bad ^ ")"));

    val futures = tasks
      |> String_Graph.schedule (fn deps => fn (name, task) =>
        (case task of
          Task (parents, body) =>
            if Multithreading.max_threads () > 1 then
              (singleton o Future.forks)
                {name = "theory:" ^ name, group = NONE,
                  deps = map (Future.task_of o #2) deps, pri = 0, interrupts = true}
                (fn () => body (join_parents deps name parents))
            else
              Future.value_result (Exn.capture_body (fn () => body (join_parents deps name parents)))
        | Finished theory => Future.value (theory_result theory)));

    val results1 = futures |> maps (consolidate_theory o Future.join_result);

    val presented_results = futures |> map (present_theory o Future.join_result);
    val present_results = map_filter I presented_results;

    val results2 = (map o Exn.map_res) (K ()) present_results;

    val results3 = (futures, presented_results) |> ListPair.map (fn (future, presented) =>
      let val segments = (case presented of SOME (Exn.Res (_, segments)) => segments | _ => []);
      in Exn.capture_body (fn () => result_commit (Future.join future) segments) end);

    val results4 = map Exn.Exn (maps Task_Queue.group_status (Execution.reset ()));

    val _ = Par_Exn.release_all (results1 @ results2 @ results3 @ results4);
  in Par_Exn.release_all present_results end);

end;


(* eval theory *)

fun eval_thy options master_dir header text_pos text parents =
  let
    val (name, _) = #name header;
    val keywords =
      fold (curry Keyword.merge_keywords o Thy_Header.get_keywords) parents
        (Keyword.add_keywords (#keywords header) Keyword.empty_keywords);

    val spans = Outer_Syntax.parse_spans (Token.explode keywords text_pos text);
    val elements = Thy_Element.parse_elements keywords spans;
    val command_ranges =
      Command_Span.command_ranges spans |> map (fn (pos, _) => (pos, Markup.command_range));

    val text_id = Position.copy_id text_pos Position.none;

    fun init () = Resources.begin_theory master_dir header parents;

    fun excursion () =
      let
        val _ = Position.setmp_thread_data text_id (fn () => Position.reports command_ranges) ();

        fun element_result span_elem (st, _) =
          let
            fun prepare span =
              let
                val tr =
                  Position.setmp_thread_data text_id
                    (fn () => Command.read_span keywords st master_dir init span) ();
              in Toplevel.timing (Resources.last_timing tr) tr end;
            val elem = Thy_Element.map_element prepare span_elem;
            val (results, st') = Toplevel.element_result keywords elem st;
            val pos' = Toplevel.pos_of (Thy_Element.last_element elem);
          in (results, (st', pos')) end;

        val (results, (end_state, end_pos)) =
          fold_map element_result elements (Toplevel.make_state NONE, Position.none);

        val thy = Toplevel.end_theory end_pos end_state;
      in (results, thy) end;

    val (results, thy) = cond_timeit true ("theory " ^ quote name) excursion;

    fun present () : presentation_context =
      let
        val segments =
          (spans ~~ maps Toplevel.join_results results) |> map (fn (span, (st, tr, st')) =>
            {span = span, prev_state = st, command = tr, state = st'});
      in {options = options, file_pos = text_pos, adjust_pos = I, segments = segments} end;

  in (thy, present) end;


(* require_thy -- checking database entries wrt. the file-system *)

local

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy options initiators deps text (name, header_pos) keywords parents =
  let
    val {master = (thy_path, _), imports} = deps;
    val dir = Path.dir thy_path;

    val exec_id = Document_ID.make ();
    val id = Document_ID.print exec_id;
    val put_id = Position.put_id id;
    val _ =
      Execution.running Document_ID.none exec_id [] orelse
        raise Fail ("Failed to register execution: " ^ id);

    val text_pos = put_id (Position.file (File.symbolic_path thy_path));
    val text_props = Position.properties_of text_pos;

    val _ = remove_thy name;
    val _ = writeln ("Loading theory " ^ quote name ^ required_by " " initiators);
    val _ = Output.try_protocol_message (Markup.loading_theory name @ text_props) [XML.blob [text]];

    val _ =
      Position.setmp_thread_data (Position.id_only id) (fn () =>
        (parents, map #2 imports) |> ListPair.app (fn (thy, pos) =>
          Context_Position.reports_global thy [(put_id pos, Theory.get_markup thy)])) ();

    val header = Thy_Header.make (name, put_id header_pos) imports keywords;
    val (theory, present) =
      eval_thy options dir header text_pos text
        (if name = Context.PureN then [Context.the_global_context ()] else parents);

    fun commit segments =
      update_thy deps (theory,
        if Options.bool options \<^system_option>\<open>record_theories\<close> then segments else []);
  in Result {theory = theory, exec_id = exec_id, present = SOME o present, commit = commit} end;

fun check_thy_deps dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, Position.none, get_imports name, [])
  | NONE =>
      let val {master, text, theory_pos, imports, keywords} = Resources.check_thy dir name
      in (false, SOME (make_deps master imports, text), theory_pos, imports, keywords) end
  | SOME (SOME {master, ...}) =>
      let
        val {master = master', text = text', theory_pos = theory_pos', imports = imports',
          keywords = keywords'} = Resources.check_thy dir name;
        val deps' = SOME (make_deps master' imports', text');
        val current =
          #2 master = #2 master' andalso
            (case lookup_theory name of
              NONE => false
            | SOME theory => Resources.loaded_files_current theory);
      in (current, deps', theory_pos', imports', keywords') end);

fun task_finished (Task _) = false
  | task_finished (Finished _) = true;

in

fun require_thys options initiators qualifier dir strs tasks =
      fold_map (require_thy options initiators qualifier dir) strs tasks |>> forall I
and require_thy options initiators qualifier dir (s, require_pos) tasks =
  let
    val {master_dir, theory_name, ...} = Resources.import_name qualifier dir s;
  in
    (case try (String_Graph.get_node tasks) theory_name of
      SOME task => (task_finished task, tasks)
    | NONE =>
        let
          val _ = member (op =) initiators theory_name andalso error (cycle_msg initiators);

          val (current, deps, theory_pos, imports, keywords) = check_thy_deps master_dir theory_name
            handle ERROR msg =>
              cat_error msg
                ("The error(s) above occurred for theory " ^ quote theory_name ^
                  Position.here require_pos ^ required_by "\n" initiators);

          val qualifier' = Resources.theory_qualifier theory_name;
          val dir' = dir + master_dir_deps (Option.map #1 deps);

          val parents = map (#theory_name o Resources.import_name qualifier' dir' o #1) imports;
          val (parents_current, tasks') =
            require_thys options (theory_name :: initiators) qualifier' dir' imports tasks;

          val all_current = current andalso parents_current;
          val task =
            if all_current then Finished (get_theory theory_name)
            else
              (case deps of
                NONE => raise Fail "Malformed deps"
              | SOME (dep, text) =>
                  Task (parents,
                    load_thy options initiators dep text (theory_name, theory_pos) keywords));

          val tasks'' = new_entry theory_name parents task tasks';
        in (all_current, tasks'') end)
  end;

end;


(* use theories *)

fun use_theories options qualifier imports =
  schedule_theories (#2 (require_thys options [] qualifier Path.current imports String_Graph.empty));

fun use_thy name =
  ignore (use_theories (Options.default ()) Resources.default_qualifier [(name, Position.none)]);


(* finish all theories *)

fun finish () = change_thys (String_Graph.map (fn _ => fn (_, entry) => (NONE, entry)));

end;

fun use_thy name = Runtime.toplevel_program (fn () => Thy_Info.use_thy name);

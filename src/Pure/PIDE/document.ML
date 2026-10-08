(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, associated with asynchronous execution process.
*)

signature DOCUMENT =
sig
  val timing: bool Unsynchronized.ref
  type overlay = Document_ID.command * (string * string list)
  datatype node_edit =
    Edits of (Document_ID.command option * Document_ID.command option) list |
    Thy of Resources.thy |
    Perspective of bool * Document_ID.command list * overlay list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_blob: string -> string -> state -> state
  type blob_digest = {file_node: string, src_path: Path.T, digest: string option} Exn.result
  type command =
   {command_id: Document_ID.command,
    name: string,
    kind: string,
    parents: string list,
    blobs_digests: blob_digest list,
    blobs_index: int,
    tokens: ((int * int) * string) list}
  val define_command: command -> state -> state
  val command_exec: state -> string -> Document_ID.command -> Command.exec option
  val remove_versions: Document_ID.version list -> state -> state
  val start_execution: state -> state
  val update: Document_ID.version -> Document_ID.version -> edit list -> string list -> state ->
    string list * Document_ID.exec list * (Document_ID.command * Document_ID.exec list) list * state
  val state: unit -> state
  val change_state: (state -> state) -> unit
end;

structure Document: DOCUMENT =
struct

val timing = Unsynchronized.ref false;
fun timeit msg e = cond_timeit (! timing) msg e;



(** document structure **)

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ Document_ID.print id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ Document_ID.print id);

type perspective =
 {required: bool,  (*required node*)
  visible: Bitset.T,  (*visible commands*)
  visible_last: Document_ID.command option,  (*last visible command*)
  overlays: (string * string list) list Inttab.table};  (*command id -> print functions with args*)

structure Entries = Linear_Set(type key = Document_ID.command val ord = int_ord);

abstype node = Node of
 {thy: Resources.thy,  (*theory header information*)
  keywords: Keyword.keywords option,  (*outer syntax keywords*)
  perspective: perspective,  (*command perspective*)
  entries: Command.exec option Entries.T,  (*command entries with executions*)
  result: (Document_ID.command * Command.eval) option,  (*result of last execution*)
  consolidated: unit lazy}  (*consolidated status of eval forks*)
and version = Version of node String_Graph.T  (*development graph wrt. static imports*)
with

fun make_node (thy, keywords, perspective, entries, result, consolidated) =
  Node {thy = thy, keywords = keywords, perspective = perspective,
    entries = entries, result = result, consolidated = consolidated};

fun map_node f (Node {thy, keywords, perspective, entries, result, consolidated}) =
  make_node (f (thy, keywords, perspective, entries, result, consolidated));

fun make_perspective (required, command_ids, overlays) : perspective =
 {required = required,
  visible = Bitset.make command_ids,
  visible_last = try List.last command_ids,
  overlays = Inttab.make_list overlays};

val empty_perspective = make_perspective (false, [], []);

val empty_node =
  make_node (Resources.no_thy, NONE, empty_perspective, Entries.empty, NONE, Lazy.value ());

fun is_empty_perspective ({required, visible, visible_last, overlays}: perspective) =
  not required andalso
  Bitset.is_empty visible andalso
  is_none visible_last andalso
  Inttab.is_empty overlays;

fun is_empty_node (Node {thy, keywords, perspective, entries, result, consolidated}) =
  thy = Resources.no_thy andalso
  is_none keywords andalso
  is_empty_perspective perspective andalso
  Entries.is_empty entries andalso
  is_none result andalso
  Lazy.is_finished consolidated;


(* basic components *)

fun set_thy thy =
  map_node (fn (_, keywords, perspective, entries, result, consolidated) =>
    (thy, keywords, perspective, entries, result, consolidated));

fun get_thy (Node {thy, ...}) = thy;
val get_thy_options = Options.update_no_pos o #options o get_thy;

fun set_keywords keywords =
  map_node (fn (thy, _, perspective, entries, result, consolidated) =>
    (thy, keywords, perspective, entries, result, consolidated));

fun read_thy node span : Resources.thy =
  let
    val thy = Resources.check_thy_errors (get_thy node);
    val header = Thy_Header.read_tokens Position.none span;
    val more_options =
      drop (length (#options header)) (#options thy)
      |> Options.update_no_pos
      |> Options.update_pos_none;
  in
   {name = #name thy,
    pos = #2 (#name header),
    imports =
      (map #1 (#imports thy) ~~ map #2 (#imports header))
        handle ListPair.UnequalLengths => #imports thy,
    options = #options header @ more_options,
    keywords = #keywords header,
    condition_bad = #condition_bad thy,
    errors = #errors thy,
    initiators = #initiators thy}
  end;

fun get_perspective (Node {perspective, ...}) = perspective;

fun set_perspective args =
  map_node (fn (thy, keywords, _, entries, result, consolidated) =>
    (thy, keywords, make_perspective args, entries, result, consolidated));

val required_node = #required o get_perspective;
val command_overlays = Inttab.lookup_list o #overlays o get_perspective;
val command_visible = Bitset.member o #visible o get_perspective;
val visible_last = #visible_last o get_perspective;
val visible_node = is_some o visible_last

fun map_entries f =
  map_node (fn (thy, keywords, perspective, entries, result, consolidated) =>
    (thy, keywords, perspective, f entries, result, consolidated));

fun get_entries (Node {entries, ...}) = entries;

fun iterate_entries f = Entries.iterate NONE f o get_entries;
fun iterate_entries_after start f (Node {entries, ...}) =
  (case Entries.get_after entries start of
    NONE => I
  | SOME id => Entries.iterate (SOME id) f entries);

fun get_result (Node {result, ...}) = result;

fun set_result result =
  map_node (fn (thy, keywords, perspective, entries, _, consolidated) =>
    (thy, keywords, perspective, entries, result, consolidated));

fun pending_result node =
  (case get_result node of
    SOME (_, eval) => not (Command.eval_finished eval)
  | NONE => false);

fun finished_result node =
  (case get_result node of
    SOME (_, eval) => Command.eval_finished eval
  | NONE => false);

fun finished_result_theory node =
  if finished_result node then
    let
      val (result_id, eval) = the (get_result node);
      val st = Command.eval_result_state eval;
    in SOME (result_id, Toplevel.end_theory Position.none st) handle ERROR _ => NONE end
  else NONE;

fun get_consolidated (Node {consolidated, ...}) = consolidated;

val reset_consolidated =
  map_node (fn (thy, keywords, perspective, entries, result, _) =>
    (thy, keywords, perspective, entries, result, Lazy.lazy I));

fun could_consolidate node =
  not (Lazy.is_finished (get_consolidated node)) andalso
  is_some (finished_result_theory node);

fun get_node nodes name = String_Graph.get_node nodes name
  handle String_Graph.UNDEF _ => empty_node;
fun default_node name = String_Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> String_Graph.map_node name f;


(* outer syntax keywords *)

val pure_keywords = Thy_Header.get_keywords o Theory.get_pure;

fun node_keywords name node =
  let
    val keywords1 = Option.map Thy_Header.get_keywords (Build.lookup_theory name);
    val keywords2 = (case node of Node {keywords, ...} => keywords);
  in
    join_options Keyword.merge_keywords (keywords1, keywords2)
    |> the_default Keyword.empty_keywords
  end;


(* node edits and associated executions *)

type overlay = Document_ID.command * (string * string list);

datatype node_edit =
  Edits of (Document_ID.command option * Document_ID.command option) list |
  Thy of Resources.thy |
  Perspective of bool * Document_ID.command list * overlay list;

type edit = string * node_edit;

val after_entry = Entries.get_after o get_entries;

fun lookup_entry node id =
  (case Entries.lookup (get_entries node) id of
    NONE => NONE
  | SOME (exec, _) => exec);

fun the_entry node id =
  (case Entries.lookup (get_entries node) id of
    NONE => err_undef "command entry" id
  | SOME (exec, _) => exec);

fun assign_entry (command_id, exec) node =
  if is_none (Entries.lookup (get_entries node) command_id) then node
  else map_entries (Entries.update (command_id, exec)) node;

fun reset_after id entries =
  (case Entries.get_after entries id of
    NONE => entries
  | SOME next => Entries.update (next, NONE) entries);

val edit_node = map_entries o fold
  (fn (id, SOME id2) => Entries.insert_after id (id2, NONE)
    | (id, NONE) => Entries.delete_after id #> reset_after id);

fun cycle_msg names = "Cyclic dependency of " ^ space_implode " via " (map quote names);

fun edit_thy name thy nodes =
  let
    val imports = map (#node o #1) (#imports thy);
    val nodes1 = nodes |> default_node name |> fold default_node imports;
    val nodes2 =
      String_Graph.Keys.fold (fn dep => String_Graph.del_edge (dep, name))
        (String_Graph.imm_preds nodes1 name) nodes1;
    val (nodes3, more_errors) =
      (String_Graph.add_deps_acyclic (name, imports) nodes2, [])
        handle String_Graph.CYCLES cs => (nodes2, map cycle_msg cs);
    val thy' = thy |> Resources.map_thy_errors (fn errors => errors @ more_errors);
  in String_Graph.map_node name (set_thy thy') nodes3 end;



(* version operations *)

val empty_version = Version String_Graph.empty;

fun nodes_of (Version nodes) = nodes;
val node_of = get_node o nodes_of;

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (case node_edit of
      Edits edits => update_node name (edit_node edits) nodes
    | Thy thy => edit_thy name thy nodes
    | Perspective perspective => update_node name (set_perspective perspective) nodes);

fun update_keywords name nodes =
  nodes |> String_Graph.map_node name (fn node =>
    if is_empty_node node then node
    else
      let
        val thy = get_thy node;
        val imports_keywords = #imports thy
          |> map (fn ({node = import, ...}, _) => node_keywords import (get_node nodes import));
        val keywords = Library.foldl Keyword.merge_keywords (pure_keywords (), imports_keywords);
        val (keywords', more_errors) =
          (Keyword.add_keywords (#keywords thy) keywords, [])
            handle ERROR msg => (keywords, if member (op =) (#errors thy) msg then [] else [msg]);
        val thy' = thy |> Resources.map_thy_errors (fn errors => errors @ more_errors);
      in
        node
        |> set_thy thy'
        |> set_keywords (SOME keywords')
      end);

fun edit_keywords edits (Version nodes) =
  Version
    (fold update_keywords
      (String_Graph.all_succs nodes (map_filter (fn (a, Thy _) => SOME a | _ => NONE) edits))
      nodes);

fun suppressed_node (nodes: node String_Graph.T) (name, node) =
  String_Graph.is_maximal nodes name andalso is_empty_node node;

fun put_node (name, node) (Version nodes) =
  let
    val nodes1 = update_node name (K node) nodes;
    val nodes2 =
      if suppressed_node nodes1 (name, node)
      then String_Graph.del_node name nodes1
      else nodes1;
  in Version nodes2 end;

end;



(** main state -- document structure and execution process **)

type blob_digest = {file_node: string, src_path: Path.T, digest: string option} Exn.result;

type execution =
 {version_id: Document_ID.version,  (*static version id*)
  execution_id: Document_ID.execution,  (*dynamic execution id*)
  delay_request: unit future,  (*pending event timer request*)
  parallel_prints: Command.exec list};  (*parallel prints for early execution*)

val no_execution: execution =
  {version_id = Document_ID.none,
   execution_id = Document_ID.none,
   delay_request = Future.value (),
   parallel_prints = []};

fun new_execution version_id delay_request parallel_prints : execution =
  {version_id = version_id,
   execution_id = Execution.start (),
   delay_request = delay_request,
   parallel_prints = parallel_prints};

abstype state = State of
 {versions: version Inttab.table,  (*version id -> document content*)
  blobs: (Message_Digest.T * string list) Symtab.table,  (*raw digest -> digest, lines*)
  commands: (string * string * blob_digest list * int * Token.T list lazy) Inttab.table,
    (*command id -> name, kind, inlined files, token index of files, command span*)
  execution: execution}  (*current execution process*)
with

fun make_state (versions, blobs, commands, execution) =
  State {versions = versions, blobs = blobs, commands = commands, execution = execution};

fun map_state f (State {versions, blobs, commands, execution}) =
  make_state (f (versions, blobs, commands, execution));

val init_state =
  make_state (Inttab.make [(Document_ID.none, empty_version)],
    Symtab.empty, Inttab.empty, no_execution);


(* document versions *)

fun parallel_prints_node node =
  iterate_entries (fn (_, opt_exec) => fn rev_result =>
    (case opt_exec of
      SOME (eval, prints) =>
        (case filter Command.parallel_print prints of
          [] => SOME rev_result
        | prints' => SOME ((eval, prints') :: rev_result))
    | NONE => NONE)) node [] |> rev;

fun define_version version_id version assigned_nodes =
  map_state (fn (versions, blobs, commands, {delay_request, ...}) =>
    let
      val version' = fold put_node assigned_nodes version;
      val versions' = Inttab.update_new (version_id, version') versions
        handle Inttab.DUP dup => err_dup "document version" dup;
      val parallel_prints = maps (parallel_prints_node o #2) assigned_nodes;
      val execution' = new_execution version_id delay_request parallel_prints;
    in (versions', blobs, commands, execution') end);

fun the_version (State {versions, ...}) version_id =
  (case Inttab.lookup versions version_id of
    NONE => err_undef "document version" version_id
  | SOME version => version);

fun delete_version version_id versions =
  Inttab.delete version_id versions
    handle Inttab.UNDEF _ => err_undef "document version" version_id;


(* inlined files *)

fun define_blob digest text =
  map_state (fn (versions, blobs, commands, execution) =>
    let val blobs' = Symtab.update (digest, (Message_Digest.parse digest, split_lines text)) blobs
    in (versions, blobs', commands, execution) end);

fun the_blob (State {blobs, ...}) digest =
  (case Symtab.lookup blobs digest of
    NONE => error ("Undefined blob: " ^ digest)
  | SOME content => content);

fun resolve_blob state (blob_digest: blob_digest) =
  blob_digest |> Exn.map_res (fn {file_node, src_path, digest} =>
    {file_node = file_node, src_path = src_path, content = Option.map (the_blob state) digest});


(* commands *)

type command =
  {command_id: Document_ID.command,
   name: string,
   kind: string,
   parents: string list,
   blobs_digests: blob_digest list,
   blobs_index: int,
   tokens: ((int * int) * string) list};

fun define_command {command_id, name, kind, parents, blobs_digests, blobs_index, tokens} =
  map_state (fn (versions, blobs, commands, execution) =>
    let
      val id = Document_ID.print command_id;
      val span =
        Lazy.lazy_name "Document.define_command" (fn () =>
          Position.setmp_thread_data (Position.id_only id)
            (fn () =>
              let
                val (tokens, _) = fold_map Token.make tokens (Position.id id);
                val imports =
                  if name = Thy_Header.theoryN then
                    (#imports (Thy_Header.read_tokens Position.none tokens)
                      handle ERROR _ => [])
                  else [];
                val _ =
                  if length parents = length imports then
                    (parents, imports) |> ListPair.app (fn (parent, (_, pos)) =>
                      let val markup =
                        (case Build.lookup_theory parent of
                          SOME thy => Theory.get_markup thy
                        | NONE =>
                            (case try Url.explode parent of
                              SOME (Url.File path) => Markup.path (Path.implode path)
                            | _ => Markup.path parent))
                      in Position.report pos markup end)
                  else ();
                val _ =
                  if blobs_index < 0
                  then (*inlined errors*)
                    map_filter Exn.get_exn blobs_digests
                    |> List.app (Output.error_message o Runtime.exn_message)
                  else (*auxiliary files*)
                    let
                      val pos = Token.pos_of (nth tokens blobs_index);
                      fun reports (Exn.Res {file_node, ...}) = [(pos, Markup.path file_node)]
                        | reports _ = [];
                    in Position.reports (maps reports blobs_digests) end;
              in tokens end) ());
      val commands' =
        Inttab.update_new (command_id, (name, kind, blobs_digests, blobs_index, span)) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, blobs, commands', execution) end);

fun the_command (State {commands, ...}) command_id =
  (case Inttab.lookup commands command_id of
    NONE => err_undef "command" command_id
  | SOME command => command);

fun the_command_name_kind state =
  the_command state #> (fn (name, kind, _, _, _) => {name = name, kind = kind});


(* execution *)

fun get_execution (State {execution, ...}) = execution;
fun get_execution_version state = the_version state (#version_id (get_execution state));

fun command_exec state node_name command_id =
  let
    val version = get_execution_version state;
    val node = get_node (nodes_of version) node_name;
  in the_entry node command_id end;

end;


(* remove_versions *)

fun remove_versions version_ids state = state |> map_state (fn (versions, _, _, execution) =>
  let
    val _ =
      member (op =) version_ids (#version_id execution) andalso
        error ("Attempt to remove execution version " ^ Document_ID.print (#version_id execution));

    val versions' = fold delete_version version_ids versions;
    val commands' =
      Inttab.build (versions' |>
        Inttab.fold (fn (_, version) => nodes_of version |>
          String_Graph.fold (fn (_, (node, _)) => node |>
            iterate_entries (fn ((_, command_id), _) =>
              SOME o Inttab.insert (K true) (command_id, the_command state command_id)))));
    val blobs' =
      Symtab.build (commands' |>
        Inttab.fold (fn (_, (_, _, blobs, _, _)) => blobs |>
          fold (fn Exn.Res {digest = SOME b, ...} => Symtab.update (b, the_blob state b) | _ => I)));

  in (versions', blobs', commands', execution) end);


(* document execution *)

fun make_required nodes =
  let
    fun all_preds P =
      String_Graph.fold (fn (a, (node, _)) => P node ? cons a) nodes []
      |> String_Graph.all_preds nodes
      |> Symset.make;

    val all_visible = all_preds visible_node;
    val all_required = all_preds required_node;
  in
    Symset.fold (fn a =>
      exists (Symset.member all_visible) (String_Graph.immediate_succs nodes a) ?
        Symset.insert a) all_visible all_required
  end;

fun start_execution state = state |> map_state (fn (versions, blobs, commands, execution) =>
  timeit "Document.start_execution" (fn () =>
    let
      val {version_id, execution_id, delay_request, parallel_prints} = execution;

      val delay = seconds (Options.default_real \<^system_option>\<open>editor_execution_delay\<close>);

      val _ = Future.cancel delay_request;
      val delay_request' = Event_Timer.future {physical = true} (Time.now () + delay);
      val delay = Future.task_of delay_request';

      val parallel_prints' = parallel_prints
        |> map_filter (Command.exec_parallel_prints execution_id [delay]);

      fun finished_import (name, (node, _)) =
        finished_result node orelse Build.defined_theory name;

      val nodes = nodes_of (the_version state version_id);
      val required = make_required nodes;
      val _ =
        nodes |> String_Graph.schedule
          (fn deps => fn (name, node) =>
            if Symset.member required name orelse visible_node node orelse pending_result node then
              let
                fun main () =
                 (Execution.worker_task_active true name;
                  if forall finished_import deps then
                    iterate_entries (fn (_, opt_exec) => fn () =>
                      (case opt_exec of
                        SOME exec =>
                          if Execution.is_running execution_id
                          then SOME (Command.exec execution_id exec)
                          else NONE
                      | NONE => NONE)) node ()
                  else ();
                  Execution.worker_task_active false name);
                val future =
                  (singleton o Future.forks)
                   {name = "theory:" ^ name,
                    group = SOME (Future.new_group NONE),
                    deps = delay :: Execution.active_tasks name @ maps (the_list o #2 o #2) deps,
                    pri = 0, interrupts = false}
                  (fn () =>
                    (case Exn.capture_body main of
                      Exn.Res () => ()
                    | Exn.Exn exn =>
                       (Output.system_message (Runtime.exn_message exn);
                        Execution.worker_task_active false name;
                        Exn.reraise exn)));
              in (node, SOME (Future.task_of future)) end
            else (node, NONE));
      val execution' =
        {version_id = version_id, execution_id = execution_id,
          delay_request = delay_request', parallel_prints = parallel_prints'};
    in (versions, blobs, commands, execution') end));



(** document update **)

(* exec state assignment *)

type assign_update = Command.exec option Inttab.table;  (*command id -> exec*)

val assign_update_empty: assign_update = Inttab.empty;
fun assign_update_defined (tab: assign_update) command_id = Inttab.defined tab command_id;
fun assign_update_change entry (tab: assign_update) : assign_update = Inttab.update entry tab;
fun assign_update_apply (tab: assign_update) node = Inttab.fold assign_entry tab node;

fun assign_update_new upd (tab: assign_update) : assign_update =
  Inttab.update_new upd tab
    handle Inttab.DUP dup => err_dup "exec state assignment" dup;

fun assign_update_result (tab: assign_update) =
  Inttab.fold (fn (command_id, exec) => cons (command_id, Command.exec_ids exec)) tab [];


(* update *)

local

fun init_theory deps node span =
  let
    val thy = read_thy node span;

    fun maybe_eval_result eval = Command.eval_result_state eval
      handle Fail _ => Toplevel.make_state NONE;

    fun maybe_end_theory pos st = SOME (Toplevel.end_theory pos st)
      handle ERROR msg => (Output.error_message msg; NONE);

    val parents_reports =
      #imports thy |> map_filter (fn ({node = import, ...}, pos) =>
        (case Build.lookup_theory import of
          NONE =>
            maybe_end_theory pos
              (case get_result (snd (the (AList.lookup (op =) deps import))) of
                NONE => Toplevel.make_state NONE
              | SOME (_, eval) => maybe_eval_result eval)
            |> Option.map (fn thy => (thy, (pos, Theory.get_markup thy)))
        | SOME thy => SOME (thy, (Position.none, Markup.empty))));

    val parents =
      if null parents_reports then [Theory.get_pure ()] else map #1 parents_reports;
    val _ = List.app (fn (thy, r) => Context_Position.reports_global thy [r]) parents_reports;

    val theory = Resources.begin_theory thy parents;
    val ctxt = Proof_Context.init_global theory;

    val default = Options.the_process_default ();
    val _ =
      #options thy |> List.app (fn spec =>
        ignore (Completion.check_option_value ctxt spec default));

    val _ = Output.status [YXML.output_markup_only Markup.initialized];
    val _ = Resources.skipping_theory warning thy;
  in {skipped = Resources.skipped thy, theory = theory} end;

fun get_special_parent node =
  let
    val thy as {name, ...} = get_thy node;
    val parent =
      if #theory name = Sessions.root_name then
        SOME (Build.get_theory Sessions.theory_name)
      else if member (op =) Thy_Header.ml_roots (#theory name) then
        SOME (Build.get_theory Thy_Header.ml_bootstrapN)
      else NONE;
  in parent |> Option.map (Resources.begin_theory thy o single) end;

fun check_theory full name node =
  Build.defined_theory name orelse
  null (#errors (get_thy node)) andalso (not full orelse is_some (get_result node));

fun last_common the_command_name_kind node_required node0 node =
  let
    val is_theory_begin =
      Symset.member Keyword.theory_begin_kinds o #kind o the_command_name_kind;

    val thy0 = get_thy node0;
    val thy = get_thy node;

    fun thy_ok command_id =
      not (is_theory_begin command_id) orelse
        #options thy0 = #options thy andalso #condition_bad thy0 = #condition_bad thy;

    fun update_flags prev (visible, initial) =
      let
        val visible' = visible andalso prev <> visible_last node;
        val initial' = initial andalso
          (case prev of
            NONE => true
          | SOME command_id => not (is_theory_begin command_id));
      in (visible', initial') end;

    fun get_common ((prev, command_id), opt_exec) (_, ok, flags, assign_update) =
      if ok then
        let
          val flags' as (visible', _) = update_flags prev flags;
          val ok' =
            (case (lookup_entry node0 command_id, opt_exec) of
              (SOME (eval0, _), SOME (eval, _)) =>
                Command.eval_eq (eval0, eval) andalso thy_ok command_id andalso
                  (visible' orelse node_required orelse Command.eval_running eval)
            | _ => false);
          val assign_update' = assign_update |> ok' ?
            (case opt_exec of
              SOME (eval, prints) =>
                let
                  val visible = command_visible node command_id;
                  val overlays = command_overlays node command_id;
                  val {name = command_name, kind = command_kind} = the_command_name_kind command_id;
                  val opts = get_thy_options node;
                in
                  (case Command.print opts visible overlays command_name command_kind eval prints of
                    SOME prints' => assign_update_new (command_id, SOME (eval, prints'))
                  | NONE => I)
                end
            | NONE => I);
        in SOME (prev, ok', flags', assign_update') end
      else NONE;
    val (common, ok, flags, assign_update') =
      iterate_entries get_common node (NONE, true, (true, true), assign_update_empty);
    val (common', flags') =
      if ok then
        let val last = Entries.get_after (get_entries node) common
        in (last, update_flags last flags) end
      else (common, flags);
  in (assign_update', common', flags') end;

fun illegal_init _ = error "Illegal theory header";

fun new_exec keywords state node proper_init command_id' (assign_update, command_exec, init) =
  if not proper_init andalso is_none init then NONE
  else
    let
      val visible = command_visible node command_id';
      val overlays = command_overlays node command_id';
      val (command_name, command_kind, blob_digests, blobs_index, span0) =
        the_command state command_id';
      val blobs = map (resolve_blob state) blob_digests;
      val span = Lazy.force span0;

      val is_theory_begin = Symset.member Keyword.theory_begin_kinds command_kind;
      val opts = get_thy_options node;
      val eval' =
        Command.eval
          (if is_theory_begin then [] else opts)
          keywords
          (#master_dir (#name (get_thy node)))
          (fn () => the_default illegal_init init span)
          (blobs, blobs_index) command_id' span (#1 (#2 command_exec));
      val prints' = perhaps (Command.print opts visible overlays command_name command_kind eval') [];
      val exec' = (eval', prints');

      val assign_update' = assign_update_new (command_id', SOME exec') assign_update;
      val init' = if is_theory_begin then NONE else init;
    in SOME (assign_update', (command_id', exec'), init') end;

fun removed_execs node0 (command_id, exec_ids) =
  subtract (op =) exec_ids (Command.exec_ids (lookup_entry node0 command_id));

fun finished_eval node =
  let
    val active =
      (node, false) |-> iterate_entries (fn (_, opt_exec) => fn active =>
        if active then NONE
        else
          (case opt_exec of
            NONE => SOME true
          | SOME (eval, _) => SOME (not (null (Execution.snapshot [Command.eval_exec_id eval])))));
  in not active end;

fun presentation_context options the_command_span node : Thy_Presentation.context =
  let
    val (_, offsets, rev_segments) =
      (node, (0, Inttab.empty, [])) |-> iterate_entries
        (fn ((prev, id), opt_exec) => fn (offset, offsets, segments) =>
          (case opt_exec of
            SOME (eval, _) =>
              let
                val command_id = Command.eval_command_id eval;
                val span = the_command_span command_id;

                val st =
                  (case try (#1 o the o the_entry node o the) prev of
                    NONE => Toplevel.make_state NONE
                  | SOME prev_eval => Command.eval_result_state prev_eval);

                val exec_id = Command.eval_exec_id eval;
                val tr = Command.eval_result_command eval;
                val st' = Command.eval_result_state eval;

                val offset' = offset + the_default 0 (Command_Span.symbol_length span);
                val offsets' = offsets
                  |> Inttab.update (command_id, offset)
                  |> Inttab.update (exec_id, offset);
                val segments' = (span, (st, tr, st')) :: segments;
              in SOME (offset', offsets', segments') end
          | NONE => raise Fail ("Unassigned exec " ^ Value.print_int id)));

    val adjust = Inttab.lookup offsets;
    val segments =
      rev rev_segments |> map (fn (span, (st, tr, st')) =>
        {span = Command_Span.adjust_offsets adjust span,
         prev_state = st, command = tr, state = st'});
  in
   {options = options,
    file_pos = Position.file (#node (#name (get_thy node))),
    adjust_pos = Position.adjust_offsets adjust,
    segments = segments}
  end;

fun print_consolidation options the_command_span (assign_update, node) =
  timeit "Document.print_consolidation" (fn () =>
    (case finished_result_theory node of
      SOME (id, thy) =>
        if finished_eval node then
          let
            val context = presentation_context options the_command_span node;
            val consolidate =
              Command.print0 {pri = Task_Queue.urgent_pri + 1, print_fn = fn _ => fn _ =>
                let
                  val _ = Output.status [YXML.output_markup_only Markup.consolidating];
                  val result = Exn.capture (Thy_Presentation.apply_hooks context) thy;
                  val _ = Lazy.force (get_consolidated node);
                  val _ = Output.status [YXML.output_markup_only Markup.consolidated];
                in Exn.release result end};
            val result_entry =
              (case lookup_entry node id of
                NONE => err_undef "result command entry" id
              | SOME (eval, prints) => (id, SOME (eval, consolidate eval :: prints)));

            val assign_update' = assign_update |> assign_update_change result_entry;
            val node' = node |> assign_entry result_entry;
          in (assign_update', node') end
        else (assign_update, node)
    | NONE => (assign_update, node)));

in

fun update old_version_id new_version_id edits consolidate state =
  Runtime.exn_trace_system_message (fn () =>
  let
    val options = Options.default [];
    val the_command_name_kind = the_command_name_kind state;
    fun the_command_span id =
      let val cmd = the_command state id
      in Outer_Syntax.make_span (#2 cmd) (Lazy.force (#5 cmd)) end;

    val old_version = the_version state old_version_id;
    val new_version =
      timeit "Document.edit_nodes"
        (fn () => old_version |> fold edit_nodes edits |> edit_keywords edits);

    val consolidate = Symset.member (Symset.make consolidate);
    val nodes = nodes_of new_version;
    val required = make_required nodes;
    val required0 = make_required (nodes_of old_version);
    val edited = Symset.build (edits |> fold (Symset.insert o #1));

    val updated = timeit "Document.update" (fn () =>
      nodes |> String_Graph.schedule
        (fn deps_future => fn (name, node) =>
          (singleton o Future.forks)
            {name = "Document.update", group = NONE,
              deps = map (Future.task_of o #2) deps_future, pri = 1, interrupts = false}
            (fn () =>
              timeit ("Document.update " ^ name) (fn () =>
                Runtime.exn_trace_system_message (fn () =>
                  let
                    val special_parent = get_special_parent node;
                    val keywords = node_keywords name node;

                    val maybe_consolidate = consolidate name andalso could_consolidate node;
                    val deps = map (apsnd Future.join) deps_future;
                    val deps_result_changed = exists (#4 o #1 o #2) deps;
                    val node_required = Symset.member required name;
                  in
                    if Symset.member edited name orelse maybe_consolidate orelse
                      visible_node node orelse deps_result_changed orelse
                      Symset.member required0 name <> node_required
                    then
                      let
                        val node0 = node_of old_version name;
                        val init = init_theory deps node;
                        val proper_init =
                          is_some special_parent orelse
                            check_theory false name node andalso
                            forall (fn (a, (_, b)) => check_theory true a b) deps;

                        val (print_execs, common, (still_visible, initial)) =
                          if deps_result_changed
                          then (assign_update_empty, NONE, (true, true))
                          else last_common the_command_name_kind node_required node0 node;

                        val common_command_exec =
                          (case common of
                            SOME id => (id, the_default Command.no_exec (the_entry node id))
                          | NONE => (Document_ID.none, Command.init_exec special_parent));

                        val (updated_execs, (command_id', exec'), _) =
                          (print_execs, common_command_exec, if initial then SOME init else NONE)
                          |> (still_visible orelse node_required) ?
                            iterate_entries_after common
                              (fn ((prev, id), _) => fn res =>
                                if not node_required andalso prev = visible_last node then NONE
                                else new_exec keywords state node proper_init id res) node;

                        val assign_update =
                          (node0, updated_execs) |-> iterate_entries_after common
                            (fn ((_, command_id0), exec0) => fn res =>
                              if is_none exec0 then NONE
                              else if assign_update_defined updated_execs command_id0 then SOME res
                              else SOME (assign_update_new (command_id0, NONE) res));

                        val last_exec =
                          if command_id' = Document_ID.none then NONE else SOME command_id';
                        val result =
                          if is_none last_exec orelse is_some (after_entry node last_exec) then NONE
                          else SOME (command_id', #1 exec');

                        val result_changed =
                          not (eq_option (Command.eval_eq o apply2 #2) (get_result node0, result));
                        val (assign_update', node') = node
                          |> assign_update_apply assign_update
                          |> set_result result
                          |> result_changed ? reset_consolidated
                          |> pair assign_update
                          |> (not result_changed andalso maybe_consolidate) ?
                              print_consolidation options the_command_span;

                        val assign_result = assign_update_result assign_update';
                        val removed = maps (removed_execs node0) assign_result;
                        val _ = List.app Execution.cancel removed;

                        val assigned_node = SOME (name, node');
                      in ((removed, assign_result, assigned_node, result_changed), node') end
                    else (([], [], NONE, false), node)
                  end))))
      |> Future.joins |> map #1);

    val removed = maps #1 updated;
    val assign_result = maps #2 updated;
    val assigned_nodes = map_filter #3 updated;

    val state' = state
      |> define_version new_version_id new_version assigned_nodes;

  in (Symset.dest edited, removed, assign_result, state') end);

end;



(** global state **)

val global_state = Synchronized.var "Document.global_state" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;

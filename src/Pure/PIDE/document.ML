(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, with asynchronous read/eval/print processes.
*)

signature DOCUMENT =
sig
  type id = int
  type version_id = id
  type command_id = id
  type exec_id = id
  val no_id: id
  val new_id: unit -> id
  val parse_id: string -> id
  val print_id: id -> string
  type node_header = string * Thy_Header.header * string list
  datatype node_edit =
    Clear |    (* FIXME unused !? *)
    Edits of (command_id option * command_id option) list |
    Deps of node_header |
    Perspective of command_id list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_command: command_id -> string -> string -> state -> state
  val remove_versions: version_id list -> state -> state
  val discontinue_execution: state -> unit
  val cancel_execution: state -> unit
  val start_execution: state -> unit
  val timing: bool Unsynchronized.ref
  val update: version_id -> version_id -> edit list -> state ->
    (command_id * exec_id option) list * state
  val state: unit -> state
  val change_state: (state -> state) -> unit
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type id = int;
type version_id = id;
type command_id = id;
type exec_id = id;

val no_id = 0;
val new_id = Synchronized.counter ();

val parse_id = Markup.parse_int;
val print_id = Markup.print_int;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ print_id id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ print_id id);



(** document structure **)

type node_header = string * Thy_Header.header * string list;
type perspective = (command_id -> bool) * command_id option;
structure Entries = Linear_Set(type key = command_id val ord = int_ord);

type exec = ((Toplevel.state * bool) * unit lazy) Command.memo;  (*eval/print process*)
val no_exec = Command.memo_value ((Toplevel.toplevel, false), Lazy.value ());

abstype node = Node of
 {header: node_header,  (*master directory, theory header, errors*)
  perspective: perspective,  (*visible commands, last*)
  entries: (exec_id * exec) option Entries.T,  (*command entries with excecutions*)
  result: exec option}  (*result of last execution*)
and version = Version of node Graph.T  (*development graph wrt. static imports*)
with

fun make_node (header, perspective, entries, result) =
  Node {header = header, perspective = perspective, entries = entries, result = result};

fun map_node f (Node {header, perspective, entries, result}) =
  make_node (f (header, perspective, entries, result));

fun make_perspective command_ids : perspective =
  (Inttab.defined (Inttab.make (map (rpair ()) command_ids)), try List.last command_ids);

val no_header = ("", Thy_Header.make ("", Position.none) [] [] [], ["Bad theory header"]);
val no_perspective = make_perspective [];

val empty_node = make_node (no_header, no_perspective, Entries.empty, NONE);
val clear_node = map_node (fn (header, _, _, _) => (header, no_perspective, Entries.empty, NONE));


(* basic components *)

fun set_header header =
  map_node (fn (_, perspective, entries, result) => (header, perspective, entries, result));

fun get_header (Node {header = (master, header, errors), ...}) =
  if null errors then (master, header)
  else error (cat_lines errors);

fun read_header node span =
  let
    val (dir, {name = (name, _), imports, keywords, uses}) = get_header node;
    val {name = (_, pos), imports = imports', ...} = Thy_Header.read_tokens span;
  in (dir, Thy_Header.make (name, pos) (map #1 imports ~~ map #2 imports') keywords uses) end;

fun get_perspective (Node {perspective, ...}) = perspective;
fun set_perspective ids =
  map_node (fn (header, _, entries, result) => (header, make_perspective ids, entries, result));

val visible_command = #1 o get_perspective;
val visible_last = #2 o get_perspective;
val visible_node = is_some o visible_last

fun map_entries f =
  map_node (fn (header, perspective, entries, result) => (header, perspective, f entries, result));
fun get_entries (Node {entries, ...}) = entries;

fun iterate_entries f = Entries.iterate NONE f o get_entries;
fun iterate_entries_after start f (Node {entries, ...}) =
  (case Entries.get_after entries start of
    NONE => I
  | SOME id => Entries.iterate (SOME id) f entries);

fun get_result (Node {result, ...}) = result;
fun set_result result =
  map_node (fn (header, perspective, entries, _) => (header, perspective, entries, result));

fun get_node nodes name = Graph.get_node nodes name handle Graph.UNDEF _ => empty_node;
fun default_node name = Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> Graph.map_node name f;


(* node edits and associated executions *)

datatype node_edit =
  Clear |
  Edits of (command_id option * command_id option) list |
  Deps of node_header |
  Perspective of command_id list;

type edit = string * node_edit;

fun after_entry (Node {entries, ...}) = Entries.get_after entries;

fun lookup_entry (Node {entries, ...}) id =
  (case Entries.lookup entries id of
    NONE => NONE
  | SOME (exec, _) => exec);

fun the_entry (Node {entries, ...}) id =
  (case Entries.lookup entries id of
    NONE => err_undef "command entry" id
  | SOME (exec, _) => exec);

fun the_default_entry node (SOME id) = (id, the_default (no_id, no_exec) (the_entry node id))
  | the_default_entry _ NONE = (no_id, (no_id, no_exec));

fun update_entry id exec =
  map_entries (Entries.update (id, exec));

fun reset_entry id node =
  if is_some (lookup_entry node id) then update_entry id NONE node else node;

fun reset_after id entries =
  (case Entries.get_after entries id of
    NONE => entries
  | SOME next => Entries.update (next, NONE) entries);

val edit_node = map_entries o fold
  (fn (id, SOME id2) => Entries.insert_after id (id2, NONE)
    | (id, NONE) => Entries.delete_after id #> reset_after id);


(* version operations *)

val empty_version = Version Graph.empty;

fun nodes_of (Version nodes) = nodes;
val node_of = get_node o nodes_of;

fun cycle_msg names = "Cyclic dependency of " ^ space_implode " via " (map quote names);

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (case node_edit of
      Clear => update_node name clear_node nodes
    | Edits edits => update_node name (edit_node edits) nodes
    | Deps (master, header, errors) =>
        let
          val imports = map fst (#imports header);
          val errors1 =
            (Thy_Header.define_keywords header; errors)
              handle ERROR msg => errors @ [msg];
          val nodes1 = nodes
            |> default_node name
            |> fold default_node imports;
          val nodes2 = nodes1
            |> Graph.Keys.fold
                (fn dep => Graph.del_edge (dep, name)) (Graph.imm_preds nodes1 name);
          val (nodes3, errors2) =
            (Graph.add_deps_acyclic (name, imports) nodes2, errors1)
              handle Graph.CYCLES cs => (nodes2, errors1 @ map cycle_msg cs);
        in Graph.map_node name (set_header (master, header, errors2)) nodes3 end
    | Perspective perspective => update_node name (set_perspective perspective) nodes);

fun put_node (name, node) (Version nodes) =
  Version (update_node name (K node) nodes);

end;



(** main state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands: (string * Token.T list lazy) Inttab.table,  (*command_id -> named span*)
  execution: version_id * Future.group * bool Unsynchronized.ref}  (*current execution process*)
with

fun make_state (versions, commands, execution) =
  State {versions = versions, commands = commands, execution = execution};

fun map_state f (State {versions, commands, execution}) =
  make_state (f (versions, commands, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)], Inttab.empty,
    (no_id, Future.new_group NONE, Unsynchronized.ref false));

fun execution_of (State {execution, ...}) = execution;


(* document versions *)

fun define_version (id: version_id) version =
  map_state (fn (versions, commands, _) =>
    let
      val versions' = Inttab.update_new (id, version) versions
        handle Inttab.DUP dup => err_dup "document version" dup;
      val execution' = (id, Future.new_group NONE, Unsynchronized.ref true);
    in (versions', commands, execution') end);

fun the_version (State {versions, ...}) (id: version_id) =
  (case Inttab.lookup versions id of
    NONE => err_undef "document version" id
  | SOME version => version);

fun delete_version (id: version_id) versions = Inttab.delete id versions
  handle Inttab.UNDEF _ => err_undef "document version" id;


(* commands *)

fun define_command (id: command_id) name text =
  map_state (fn (versions, commands, execution) =>
    let
      val id_string = print_id id;
      val span = Lazy.lazy (fn () =>
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () =>
            Thy_Syntax.parse_tokens
              (#1 (Outer_Syntax.get_syntax ())) (Position.id id_string) text) ());
      val _ =
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Output.status (Markup.markup_only Isabelle_Markup.accepted)) ();
      val commands' =
        Inttab.update_new (id, (name, span)) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME command => command);

end;

fun remove_versions ids state = state |> map_state (fn (versions, _, execution) =>
  let
    val _ = member (op =) ids (#1 execution) andalso
      error ("Attempt to remove execution version " ^ print_id (#1 execution));

    val versions' = fold delete_version ids versions;
    val commands' =
      (versions', Inttab.empty) |->
        Inttab.fold (fn (_, version) => nodes_of version |>
          Graph.fold (fn (_, (node, _)) => node |>
            iterate_entries (fn ((_, id), _) =>
              SOME o Inttab.insert (K true) (id, the_command state id))));
  in (versions', commands', execution) end);



(** document execution **)

val discontinue_execution = execution_of #> (fn (_, _, running) => running := false);

val cancel_execution = execution_of #> (fn (_, group, _) => Future.cancel_group group);

fun terminate_execution state =
  let
    val (_, group, _) = execution_of state;
    val _ = Future.cancel_group group;
  in Future.join_tasks (Future.group_tasks group) end;

fun start_execution state =
  let
    fun finished_theory node =
      (case Exn.capture (Command.memo_result o the) (get_result node) of
        Exn.Res ((st, _), _) => can (Toplevel.end_theory Position.none) st
      | _ => false);

    fun run node command_id exec =
      let
        val (_, print) = Command.memo_eval exec;
        val _ =
          if visible_command node command_id
          then ignore (Lazy.future Future.default_params print)
          else ();
      in () end;

    val (version_id, group, running) = execution_of state;

    val _ =
      (singleton o Future.forks)
        {name = "execution", group = SOME group, deps = [], pri = ~2, interrupts = true}
        (fn () =>
         (OS.Process.sleep (seconds 0.02);
          nodes_of (the_version state version_id) |> Graph.schedule
            (fn deps => fn (name, node) =>
              if not (visible_node node) andalso finished_theory node then
                Future.value ()
              else
                (singleton o Future.forks)
                  {name = "theory:" ^ name, group = SOME (Future.new_group (SOME group)),
                    deps = map (Future.task_of o #2) deps, pri = ~2, interrupts = false}
                  (fn () =>
                    iterate_entries (fn ((_, id), opt_exec) => fn () =>
                      (case opt_exec of
                        SOME (_, exec) => if ! running then SOME (run node id exec) else NONE
                      | NONE => NONE)) node ()))));
  in () end;



(** document update **)

val timing = Unsynchronized.ref false;
fun timeit msg e = cond_timeit (! timing) msg e;

local

fun stable_finished_theory node =
  is_some (Exn.get_res (Exn.capture (fn () =>
    fst (fst (Command.memo_result (the (get_result node))))
    |> Toplevel.end_theory Position.none
    |> Global_Theory.join_proofs) ()));

fun stable_command exec =
  (case Exn.capture Command.memo_result exec of
    Exn.Exn exn => not (Exn.is_interrupt exn)
  | Exn.Res ((st, _), _) =>
      (case try Toplevel.theory_of st of
        NONE => true
      | SOME thy => is_some (Exn.get_res (Exn.capture Global_Theory.join_recent_proofs thy))));

fun make_required nodes =
  let
    val all_visible =
      Graph.fold (fn (a, (node, _)) => visible_node node ? cons a) nodes []
      |> Graph.all_preds nodes
      |> map (rpair ()) |> Symtab.make;

    val required =
      Symtab.fold (fn (a, ()) =>
        exists (Symtab.defined all_visible) (Graph.immediate_succs nodes a) ?
          Symtab.update (a, ())) all_visible Symtab.empty;
  in Symtab.defined required end;

fun init_theory deps node span =
  let
    (* FIXME provide files via Scala layer, not master_dir *)
    val (dir, header) = read_header node span;
    val master_dir =
      (case try Url.explode dir of
        SOME (Url.File path) => path
      | _ => Path.current);
    val imports = #imports header;
    val parents =
      imports |> map (fn (import, _) =>
        (case Thy_Info.lookup_theory import of
          SOME thy => thy
        | NONE =>
            Toplevel.end_theory (Position.file_only import)
              (fst (fst
                (Command.memo_result
                  (the_default no_exec
                    (get_result (snd (the (AList.lookup (op =) deps import))))))))));
    val _ = Position.reports (map #2 imports ~~ map Theory.get_markup parents);
  in Thy_Load.begin_theory master_dir header parents end;

fun check_theory full name node =
  is_some (Thy_Info.lookup_theory name) orelse
  can get_header node andalso (not full orelse is_some (get_result node));

fun last_common state last_visible node0 node =
  let
    fun update_flags prev (visible, initial) =
      let
        val visible' = visible andalso prev <> last_visible;
        val initial' = initial andalso
          (case prev of
            NONE => true
          | SOME id => not (Keyword.is_theory_begin (#1 (the_command state id))));
      in (visible', initial') end;
    fun get_common ((prev, id), opt_exec) (same, (_, flags)) =
      if same then
        let
          val flags' = update_flags prev flags;
          val same' =
            (case opt_exec of
              NONE => false
            | SOME (exec_id, exec) =>
                (case lookup_entry node0 id of
                  NONE => false
                | SOME (exec_id0, _) => exec_id = exec_id0 andalso stable_command exec));
        in SOME (same', (prev, flags')) end
      else NONE;
    val (same, (common, flags)) =
      iterate_entries get_common node (true, (NONE, (true, true)));
  in
    if same then
      let val last = Entries.get_after (get_entries node) common
      in (last, update_flags last flags) end
    else (common, flags)
  end;

fun illegal_init _ = error "Illegal theory header after end of theory";

fun new_exec state proper_init command_id' (execs, command_exec, init) =
  if not proper_init andalso is_none init then NONE
  else
    let
      val (name, span) = the_command state command_id' ||> Lazy.force;
      val (modify_init, init') =
        if Keyword.is_theory_begin name then
          (Toplevel.modify_init (fn () => the_default illegal_init init span), NONE)
        else (I, init);
      val exec_id' = new_id ();
      val exec_id'_string = print_id exec_id';
      val cmd =
        Position.setmp_thread_data (Position.id_only exec_id'_string)
          (fn () =>
            let
              val tr =
                #1 (Outer_Syntax.read_span (#2 (Outer_Syntax.get_syntax ())) span)
                |> modify_init
                |> Toplevel.put_id exec_id'_string;
              val cmts = Outer_Syntax.span_cmts span;
            in (tr, cmts) end);
      val exec' =
        Command.memo (fn () =>
          Command.run_command (cmd ()) (fst (Command.memo_result (snd (snd command_exec)))));
      val command_exec' = (command_id', (exec_id', exec'));
    in SOME (command_exec' :: execs, command_exec', init') end;

in

fun update (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 *)
    val new_version = timeit "Document.edit_nodes" (fn () => fold edit_nodes edits old_version);

    val nodes = nodes_of new_version;
    val is_required = make_required nodes;

    val _ = timeit "Document.terminate_execution" (fn () => terminate_execution state);
    val updated = timeit "Document.update" (fn () =>
      nodes |> Graph.schedule
        (fn deps => fn (name, node) =>
          (singleton o Future.forks)
            {name = "Document.update", group = NONE,
              deps = map (Future.task_of o #2) deps, pri = 0, interrupts = false}
            (fn () =>
              let
                val imports = map (apsnd Future.join) deps;
                val updated_imports = exists (is_some o #3 o #1 o #2) imports;
                val required = is_required name;
              in
                if updated_imports orelse AList.defined (op =) edits name orelse
                  not (stable_finished_theory node)
                then
                  let
                    val node0 = node_of old_version name;
                    val init = init_theory imports node;
                    val proper_init =
                      check_theory false name node andalso
                      forall (fn (name, (_, node)) => check_theory true name node) imports;

                    val last_visible = visible_last node;
                    val (common, (visible, initial)) =
                      if updated_imports then (NONE, (true, true))
                      else last_common state last_visible node0 node;
                    val common_command_exec = the_default_entry node common;

                    val (new_execs, (command_id', (_, exec')), _) =
                      ([], common_command_exec, if initial then SOME init else NONE) |>
                      (visible orelse required) ?
                        iterate_entries_after common
                          (fn ((prev, id), _) => fn res =>
                            if not required andalso prev = last_visible then NONE
                            else new_exec state proper_init id res) node;

                    val no_execs =
                      iterate_entries_after common
                        (fn ((_, id0), exec0) => fn res =>
                          if is_none exec0 then NONE
                          else if exists (fn (_, (id, _)) => id0 = id) new_execs then SOME res
                          else SOME (id0 :: res)) node0 [];

                    val last_exec = if command_id' = no_id then NONE else SOME command_id';
                    val result =
                      if is_some (after_entry node last_exec) then NONE
                      else SOME exec';

                    val node' = node
                      |> fold reset_entry no_execs
                      |> fold (fn (id, exec) => update_entry id (SOME exec)) new_execs
                      |> set_result result;
                    val updated_node =
                      if null no_execs andalso null new_execs then NONE
                      else SOME (name, node');
                  in ((no_execs, new_execs, updated_node), node') end
                else (([], [], NONE), node)
              end))
      |> Future.joins |> map #1);

    val command_execs =
      map (rpair NONE) (maps #1 updated) @
      map (fn (command_id, (exec_id, _)) => (command_id, SOME exec_id)) (maps #2 updated);
    val updated_nodes = map_filter #3 updated;

    val state' = state
      |> define_version new_id (fold put_node updated_nodes new_version);
  in (command_execs, state') end;

end;



(** global state **)

val global_state = Synchronized.var "Document" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;


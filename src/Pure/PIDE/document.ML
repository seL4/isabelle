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
  type node_header = (string * string list * (string * bool) list) Exn.result
  datatype node_edit =
    Clear |
    Edits of (command_id option * command_id option) list |
    Header of node_header |
    Perspective of command_id list
  type edit = string * node_edit
  type state
  val init_state: state
  val define_command: command_id -> string -> state -> state
  val join_commands: state -> state
  val cancel_execution: state -> Future.task list
  val update_perspective: version_id -> version_id -> string -> command_id list -> state -> state
  val update: version_id -> version_id -> edit list -> state ->
    ((command_id * exec_id option) list * (string * command_id option) list) * state
  val execute: version_id -> state -> state
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

type node_header = (string * string list * (string * bool) list) Exn.result;
type perspective = (command_id -> bool) * command_id option; (*visible commands, last*)
structure Entries = Linear_Set(type key = command_id val ord = int_ord);

abstype node = Node of
 {touched: bool,
  header: node_header,
  perspective: perspective,
  entries: exec_id option Entries.T,  (*command entries with excecutions*)
  last_exec: command_id option,  (*last command with exec state assignment*)
  result: Toplevel.state lazy}
and version = Version of node Graph.T  (*development graph wrt. static imports*)
with

fun make_node (touched, header, perspective, entries, last_exec, result) =
  Node {touched = touched, header = header, perspective = perspective,
    entries = entries, last_exec = last_exec, result = result};

fun map_node f (Node {touched, header, perspective, entries, last_exec, result}) =
  make_node (f (touched, header, perspective, entries, last_exec, result));

fun make_perspective command_ids : perspective =
  (Inttab.defined (Inttab.make (map (rpair ()) command_ids)), try List.last command_ids);

val no_header = Exn.Exn (ERROR "Bad theory header");
val no_perspective = make_perspective [];
val no_print = Lazy.value ();
val no_result = Lazy.value Toplevel.toplevel;

val empty_node = make_node (false, no_header, no_perspective, Entries.empty, NONE, no_result);
val clear_node = map_node (fn (_, header, _, _, _, _) =>
  (false, header, no_perspective, Entries.empty, NONE, no_result));


(* basic components *)

fun is_touched (Node {touched, ...}) = touched;
fun set_touched touched =
  map_node (fn (_, header, perspective, entries, last_exec, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_header (Node {header, ...}) = header;
fun set_header header =
  map_node (fn (touched, _, perspective, entries, last_exec, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_perspective (Node {perspective, ...}) = perspective;
fun set_perspective ids =
  map_node (fn (touched, header, _, entries, last_exec, result) =>
    (touched, header, make_perspective ids, entries, last_exec, result));

fun map_entries f =
  map_node (fn (touched, header, perspective, entries, last_exec, result) =>
    (touched, header, perspective, f entries, last_exec, result));
fun iterate_entries start f (Node {entries, ...}) = Entries.iterate start f entries;

fun get_last_exec (Node {last_exec, ...}) = last_exec;
fun set_last_exec last_exec =
  map_node (fn (touched, header, perspective, entries, _, result) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_theory pos (Node {result, ...}) = Toplevel.end_theory pos (Lazy.force result);
fun set_result result =
  map_node (fn (touched, header, perspective, entries, last_exec, _) =>
    (touched, header, perspective, entries, last_exec, result));

fun get_node nodes name = Graph.get_node nodes name handle Graph.UNDEF _ => empty_node;
fun default_node name = Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> Graph.map_node name f;


(* node edits and associated executions *)

datatype node_edit =
  Clear |
  Edits of (command_id option * command_id option) list |
  Header of node_header |
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

fun the_default_entry node (SOME id) = the_default no_id (the_entry node id)
  | the_default_entry _ NONE = no_id;

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

local

fun cycle_msg names = "Cyclic dependency of " ^ space_implode " via " (map quote names);

fun touch_node name nodes =
  fold (fn desc =>
      update_node desc (set_touched true) #>
      desc <> name ? update_node desc (map_entries (reset_after NONE)))
    (Graph.all_succs nodes [name]) nodes;

in

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (case node_edit of
      Clear =>
        nodes
        |> update_node name clear_node
        |> touch_node name
    | Edits edits =>
        nodes
        |> update_node name (edit_node edits)
        |> touch_node name
    | Header header =>
        let
          val parents = (case header of Exn.Res (_, parents, _) => parents | _ => []);
          val nodes1 = nodes
            |> default_node name
            |> fold default_node parents;
          val nodes2 = nodes1
            |> Graph.Keys.fold
                (fn dep => Graph.del_edge (dep, name)) (Graph.imm_preds nodes1 name);
          val (header', nodes3) =
            (header, Graph.add_deps_acyclic (name, parents) nodes2)
              handle Graph.CYCLES cs => (Exn.Exn (ERROR (cat_lines (map cycle_msg cs))), nodes2);
        in Graph.map_node name (set_header header') nodes3 end
        |> touch_node name
    | Perspective perspective =>
        update_node name (set_perspective perspective) nodes);

end;

fun put_node (name, node) (Version nodes) =
  Version (update_node name (K node) nodes);

end;



(** global state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands:
    Toplevel.transition future Inttab.table *  (*command_id -> transition (future parsing)*)
    Toplevel.transition future list,  (*recent commands to be joined*)
  execs: (command_id * (Toplevel.state * unit lazy) lazy) Inttab.table,
    (*exec_id -> command_id with eval/print process*)
  execution: Future.group}  (*global execution process*)
with

fun make_state (versions, commands, execs, execution) =
  State {versions = versions, commands = commands, execs = execs, execution = execution};

fun map_state f (State {versions, commands, execs, execution}) =
  make_state (f (versions, commands, execs, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)],
    (Inttab.make [(no_id, Future.value Toplevel.empty)], []),
    Inttab.make [(no_id, (no_id, Lazy.value (Toplevel.toplevel, no_print)))],
    Future.new_group NONE);


(* document versions *)

fun define_version (id: version_id) version =
  map_state (fn (versions, commands, execs, execution) =>
    let val versions' = Inttab.update_new (id, version) versions
      handle Inttab.DUP dup => err_dup "document version" dup
    in (versions', commands, execs, execution) end);

fun the_version (State {versions, ...}) (id: version_id) =
  (case Inttab.lookup versions id of
    NONE => err_undef "document version" id
  | SOME version => version);


(* commands *)

fun define_command (id: command_id) text =
  map_state (fn (versions, (commands, recent), execs, execution) =>
    let
      val id_string = print_id id;
      val tr =
        Future.fork_pri 2 (fn () =>
          Position.setmp_thread_data (Position.id_only id_string)
            (fn () => Outer_Syntax.read_command (Position.id id_string) text) ());
      val commands' =
        Inttab.update_new (id, tr) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, (commands', tr :: recent), execs, execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup (#1 commands) id of
    NONE => err_undef "command" id
  | SOME tr => tr);

val join_commands =
    map_state (fn (versions, (commands, recent), execs, execution) =>
      (Future.join_results recent; (versions, (commands, []), execs, execution)));


(* command executions *)

fun define_exec (exec_id, exec) =
  map_state (fn (versions, commands, execs, execution) =>
    let val execs' = Inttab.update_new (exec_id, exec) execs
      handle Inttab.DUP dup => err_dup "command execution" dup
    in (versions, commands, execs', execution) end);

fun the_exec (State {execs, ...}) exec_id =
  (case Inttab.lookup execs exec_id of
    NONE => err_undef "command execution" exec_id
  | SOME exec => exec);


(* document execution *)

fun cancel_execution (State {execution, ...}) = Future.cancel_group execution;

end;



(* toplevel transactions *)

local

fun timing tr t =
  if Timing.is_relevant t then Toplevel.status tr (Markup.timing t) else ();

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => Toplevel.status tr (Proof.status_markup prf)
  | NONE => ());

fun print_state tr st =
  (Lazy.lazy o Toplevel.setmp_thread_position tr)
    (fn () => Toplevel.print_state false st);

fun run int tr st =
  (case Toplevel.transition int tr st of
    SOME (st', NONE) => ([], SOME st')
  | SOME (_, SOME (exn, _)) =>
      (case ML_Compiler.exn_messages exn of
        [] => Exn.interrupt ()
      | errs => (errs, NONE))
  | NONE => ([(serial (), ML_Compiler.exn_message Runtime.TERMINATE)], NONE));

in

fun run_command tr st =
  let
    val is_init = Toplevel.is_init tr;
    val is_proof = Keyword.is_proof (Toplevel.name_of tr);
    val do_print = not is_init andalso (Toplevel.print_of tr orelse is_proof);

    val _ = Toplevel.status tr Markup.forked;
    val start = Timing.start ();
    val (errs, result) =
      if Toplevel.is_toplevel st andalso not is_init then ([], SOME st)
      else run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
    val _ = timing tr (Timing.result start);
    val _ = Toplevel.status tr Markup.joined;
    val _ = List.app (Toplevel.error_msg tr) errs;
  in
    (case result of
      NONE => (Toplevel.status tr Markup.failed; (st, no_print))
    | SOME st' =>
       (Toplevel.status tr Markup.finished;
        proof_status tr st';
        (st', if do_print then print_state tr st' else no_print)))
  end;

end;




(** update **)

(* perspective *)

fun update_perspective (old_id: version_id) (new_id: version_id) name perspective state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 -- needed? *)
    val new_version = edit_nodes (name, Perspective perspective) old_version;
  in define_version new_id new_version state end;


(* edits *)

local

fun last_common last_visible node0 node =
  let
    fun get_common ((prev, id), exec) (found, (_, visible)) =
      if found then NONE
      else
        let val found' = is_none exec orelse exec <> lookup_entry node0 id
        in SOME (found', (prev, visible andalso prev <> last_visible)) end;
  in #2 (iterate_entries NONE get_common node (false, (NONE, true))) end;

fun new_exec state init command_id' (execs, exec) =
  let
    val command' = the_command state command_id';
    val exec_id' = new_id ();
    val exec' =
      snd exec |> Lazy.map (fn (st, _) =>
        let val tr =
          Future.join command'
          |> Toplevel.modify_init init
          |> Toplevel.put_id (print_id exec_id');
        in run_command tr st end)
      |> pair command_id';
  in ((exec_id', exec') :: execs, exec') end;

fun make_required nodes =
  let
    val all_visible =
      Graph.fold (fn (a, (node, _)) => is_some (#2 (get_perspective node)) ? cons a) nodes []
      |> Graph.all_preds nodes;
    val required =
      fold (fn a => exists (fn b => Graph.is_edge nodes (a, b)) all_visible ? Symtab.update (a, ()))
        all_visible Symtab.empty;
  in Symtab.defined required end;

fun init_theory deps name node =
  let
    val (thy_name, imports, uses) = Exn.release (get_header node);
    (* FIXME provide files via Scala layer *)
    val (dir, files) =
      if ML_System.platform_is_cygwin then (Path.current, [])
      else (Path.dir (Path.explode name), map (apfst Path.explode) uses);

    val parents =
      imports |> map (fn import =>
        (case Thy_Info.lookup_theory import of  (* FIXME more robust!? *)
          SOME thy => thy
        | NONE =>
            get_theory (Position.file_only import)
              (snd (Future.join (the (AList.lookup (op =) deps import))))));
  in Thy_Load.begin_theory dir thy_name imports files parents end;

in

fun update (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 *)
    val new_version = fold edit_nodes edits old_version;

    val nodes = nodes_of new_version;
    val is_required = make_required nodes;

    val updated =
      nodes |> Graph.schedule
        (fn deps => fn (name, node) =>
          if not (is_touched node orelse is_required name)
          then Future.value (([], [], []), node)
          else
            let
              val node0 = node_of old_version name;
              fun init () = init_theory deps name node;
            in
              (singleton o Future.forks)
                {name = "Document.update", group = NONE,
                  deps = map (Future.task_of o #2) deps, pri = 0, interrupts = false}
                (fn () =>
                  let
                    val required = is_required name;
                    val last_visible = #2 (get_perspective node);
                    val (common, visible) = last_common last_visible node0 node;
                    val common_exec = the_exec state (the_default_entry node common);

                    val (execs, exec) = ([], common_exec) |>
                      (visible orelse required) ?
                        iterate_entries (after_entry node common)
                          (fn ((prev, id), _) => fn res =>
                            if not required andalso prev = last_visible then NONE
                            else SOME (new_exec state init id res)) node;

                    val no_execs =
                      iterate_entries (after_entry node0 common)
                        (fn ((_, id0), exec0) => fn res =>
                          if is_none exec0 then NONE
                          else if exists (fn (_, (id, _)) => id0 = id) execs then SOME res
                          else SOME (id0 :: res)) node0 [];

                    val last_exec = if #1 exec = no_id then NONE else SOME (#1 exec);
                    val result =
                      if is_some (after_entry node last_exec) then no_result
                      else Lazy.map #1 (#2 exec);

                    val node' = node
                      |> fold reset_entry no_execs
                      |> fold (fn (exec_id, (id, _)) => update_entry id (SOME exec_id)) execs
                      |> set_last_exec last_exec
                      |> set_result result
                      |> set_touched false;
                  in ((no_execs, execs, [(name, node')]), node') end)
            end)
      |> Future.joins |> map #1;

    val command_execs =
      map (rpair NONE) (maps #1 updated) @
      map (fn (exec_id, (command_id, _)) => (command_id, SOME exec_id)) (maps #2 updated);
    val updated_nodes = maps #3 updated;
    val last_execs = map (fn (name, node) => (name, get_last_exec node)) updated_nodes;

    val state' = state
      |> fold (fold define_exec o #2) updated
      |> define_version new_id (fold put_node updated_nodes new_version);
  in ((command_execs, last_execs), state') end;

end;


(* execute *)

fun execute version_id state =
  state |> map_state (fn (versions, commands, execs, _) =>
    let
      val version = the_version state version_id;

      fun force_exec _ NONE = ()
        | force_exec node (SOME exec_id) =
            let
              val (command_id, exec) = the_exec state exec_id;
              val (_, print) = Lazy.force exec;
              val _ =
                if #1 (get_perspective node) command_id
                then ignore (Lazy.future Future.default_params print)
                else ();
            in () end;

      val execution = Future.new_group NONE;
      val _ =
        nodes_of version |> Graph.schedule
          (fn deps => fn (name, node) =>
            (singleton o Future.forks)
              {name = "theory:" ^ name, group = SOME (Future.new_group (SOME execution)),
                deps = map (Future.task_of o #2) deps, pri = 1, interrupts = true}
              (iterate_entries NONE (fn (_, exec) => fn () => SOME (force_exec node exec)) node));

    in (versions, commands, execs, execution) end);



(** global state **)

val global_state = Synchronized.var "Document" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;


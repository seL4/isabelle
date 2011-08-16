(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, associated with asynchronous execution process.
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
    Header of node_header
  type edit = string * node_edit
  type state
  val init_state: state
  val join_commands: state -> unit
  val cancel_execution: state -> unit -> unit
  val define_command: command_id -> string -> state -> state
  val edit: version_id -> version_id -> edit list -> state -> (command_id * exec_id) list * state
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
structure Entries = Linear_Set(type key = command_id val ord = int_ord);

abstype node = Node of
 {header: node_header,
  entries: exec_id option Entries.T,  (*command entries with excecutions*)
  result: Toplevel.state lazy}
and version = Version of node Graph.T  (*development graph wrt. static imports*)
with

fun make_node (header, entries, result) =
  Node {header = header, entries = entries, result = result};

fun map_node f (Node {header, entries, result}) =
  make_node (f (header, entries, result));

fun get_header (Node {header, ...}) = header;
fun set_header header = map_node (fn (_, entries, result) => (header, entries, result));

fun map_entries f (Node {header, entries, result}) = make_node (header, f entries, result);
fun fold_entries start f (Node {entries, ...}) = Entries.fold start f entries;
fun first_entry start P (Node {entries, ...}) = Entries.get_first start P entries;

fun get_theory pos (Node {result, ...}) = Toplevel.end_theory pos (Lazy.get_finished result);
fun set_result result = map_node (fn (header, entries, _) => (header, entries, result));

val empty_exec = Lazy.value Toplevel.toplevel;
val empty_node = make_node (Exn.Exn (ERROR "Bad theory header"), Entries.empty, empty_exec);
val clear_node = map_node (fn (header, _, _) => (header, Entries.empty, empty_exec));

fun get_node nodes name = Graph.get_node nodes name handle Graph.UNDEF _ => empty_node;
fun remove_node name nodes = Graph.del_node name nodes handle Graph.UNDEF _ => nodes;
fun default_node name = Graph.default_node (name, empty_node);
fun update_node name f = default_node name #> Graph.map_node name f;


(* node edits and associated executions *)

datatype node_edit =
  Clear |
  Edits of (command_id option * command_id option) list |
  Header of node_header;

type edit = string * node_edit;

fun the_entry (Node {entries, ...}) id =
  (case Entries.lookup entries id of
    NONE => err_undef "command entry" id
  | SOME entry => entry);

fun update_entry (id, exec_id) =
  map_entries (Entries.update (id, SOME exec_id));

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

fun touch_descendants name nodes =
  fold (fn desc => desc <> name ? update_node desc (map_entries (reset_after NONE)))
    (Graph.all_succs nodes [name]) nodes;

fun edit_nodes (name, node_edit) (Version nodes) =
  Version
    (touch_descendants name
      (case node_edit of
        Clear => update_node name clear_node nodes
      | Edits edits =>
          nodes
          |> update_node name (edit_node edits)
      | Header header =>
          let
            val node = get_node nodes name;
            val nodes1 = Graph.new_node (name, node) (remove_node name nodes);
            val parents = (case header of Exn.Res (_, parents, _) => parents | _ => []);
            val nodes2 = fold default_node parents nodes1;
            val (header', nodes3) =
              (header, Graph.add_deps_acyclic (name, parents) nodes2)
                handle Graph.CYCLES cs => (Exn.Exn (ERROR (cat_lines (map cycle_msg cs))), nodes2);
          in Graph.map_node name (set_header header') nodes3 end));

fun put_node (name, node) (Version nodes) =
  Version (update_node name (K node) nodes);

end;



(** global state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands: Toplevel.transition future Inttab.table,  (*command_id -> transition (future parsing)*)
  execs: Toplevel.state lazy Inttab.table,  (*exec_id -> execution process*)
  execution: unit future list}  (*global execution process*)
with

fun make_state (versions, commands, execs, execution) =
  State {versions = versions, commands = commands, execs = execs, execution = execution};

fun map_state f (State {versions, commands, execs, execution}) =
  make_state (f (versions, commands, execs, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)],
    Inttab.make [(no_id, Future.value Toplevel.empty)],
    Inttab.make [(no_id, empty_exec)],
    []);


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
  map_state (fn (versions, commands, execs, execution) =>
    let
      val id_string = print_id id;
      val tr = Future.fork_pri 2 (fn () =>
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Outer_Syntax.prepare_command (Position.id id_string) text) ());
      val commands' =
        Inttab.update_new (id, tr) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execs, execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME tr => tr);

fun join_commands (State {commands, ...}) =
  Inttab.fold (fn (_, tr) => fn () => ignore (Future.join_result tr)) commands ();


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

fun cancel_execution (State {execution, ...}) =
  (List.app Future.cancel execution;
    fn () => ignore (Future.join_results execution));

end;



(* toplevel transactions *)

local

fun timing tr t = Toplevel.status tr (Markup.timing t);

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => Toplevel.status tr (Proof.status_markup prf)
  | NONE => ());

fun async_state tr st =
  ignore
    (singleton
      (Future.forks {name = "Document.async_state",
        group = SOME (Task_Queue.new_group NONE), deps = [], pri = 0, interrupts = true})
      (fn () =>
        Toplevel.setmp_thread_position tr
          (fn () => Toplevel.print_state false st) ()));

fun run int tr st =
  (case Toplevel.transition int tr st of
    SOME (st', NONE) => ([], SOME st')
  | SOME (_, SOME exn_info) =>
      (case ML_Compiler.exn_messages (Runtime.EXCURSION_FAIL exn_info) of
        [] => Exn.interrupt ()
      | errs => (errs, NONE))
  | NONE => ([ML_Compiler.exn_message Runtime.TERMINATE], NONE));

in

fun run_command tr st =
  let
    val is_init = Toplevel.is_init tr;
    val is_proof = Keyword.is_proof (Toplevel.name_of tr);
    val do_print = not is_init andalso (Toplevel.print_of tr orelse is_proof);

    val start = Timing.start ();
    val (errs, result) =
      if Toplevel.is_toplevel st andalso not is_init then ([], SOME st)
      else run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
    val _ = timing tr (Timing.result start);
    val _ = List.app (Toplevel.error_msg tr) errs;
  in
    (case result of
      NONE => (Toplevel.status tr Markup.failed; st)
    | SOME st' =>
       (Toplevel.status tr Markup.finished;
        proof_status tr st';
        if do_print then async_state tr st' else ();
        st'))
  end;

end;




(** editing **)

(* edit *)

local

fun is_changed node' ((_, id), exec) =
  (case try (the_entry node') id of
    NONE => true
  | SOME exec' => exec' <> exec);

fun new_exec (command_id, command) (assigns, execs, exec) =
  let
    val exec_id' = new_id ();
    val exec' =
      Lazy.lazy (fn () =>
        let
          val tr = Toplevel.put_id (print_id exec_id') (Future.get_finished command);
          val st = Lazy.get_finished exec;
        in run_command tr st end);
  in ((command_id, exec_id') :: assigns, (exec_id', exec') :: execs, exec') end;

in

fun edit (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround for polyml-5.4.0/x86_64 *)
    val new_version = fold edit_nodes edits old_version;

    val updates =
      nodes_of new_version |> Graph.schedule
        (fn deps => fn (name, node) =>
          (case first_entry NONE (is_changed (node_of old_version name)) node of
            NONE => Future.value (([], [], []), node)
          | SOME ((prev, id), _) =>
              let
                fun init () =
                  let
                    val (thy_name, imports, uses) = Exn.release (get_header node);
                    (* FIXME provide files via Scala layer *)
                    val dir = Path.dir (Path.explode name);
                    val files = map (apfst Path.explode) uses;

                    val parents =
                      imports |> map (fn import =>
                        (case Thy_Info.lookup_theory import of
                          SOME thy => thy
                        | NONE =>
                            get_theory (Position.file_only import)
                              (#2 (Future.join (the (AList.lookup (op =) deps import))))));
                  in Thy_Load.begin_theory dir thy_name imports files parents end
                fun get_command id =
                  (id, the_command state id |> Future.map (Toplevel.modify_init init));
              in
                singleton
                  (Future.forks {name = "Document.edit", group = NONE,
                    deps = map (Future.task_of o #2) deps, pri = 2, interrupts = false})
                  (fn () =>
                    let
                      val prev_exec =
                        (case prev of
                          NONE => no_id
                        | SOME prev_id => the_default no_id (the_entry node prev_id));
                      val (assigns, execs, result) =
                        fold_entries (SOME id) (new_exec o get_command o #2 o #1)
                          node ([], [], the_exec state prev_exec);
                      val node' = node
                        |> fold update_entry assigns
                        |> set_result result;
                    in ((assigns, execs, [(name, node')]), node') end)
              end))
      |> Future.join_results |> Exn.release_all |> map #1;

    val state' = state
      |> fold (fold define_exec o #2) updates
      |> define_version new_id (fold (fold put_node o #3) updates new_version);

  in (maps #1 (rev updates), state') end;

end;


(* execute *)

fun execute version_id state =
  state |> map_state (fn (versions, commands, execs, _) =>
    let
      val version = the_version state version_id;

      fun force_exec NONE = ()
        | force_exec (SOME exec_id) = ignore (Lazy.force (the_exec state exec_id));

      val execution' =
        nodes_of version |> Graph.schedule
          (fn deps => fn (name, node) =>
            singleton
              (Future.forks
                {name = "theory:" ^ name, group = NONE,
                  deps = map (Future.task_of o #2) deps,
                  pri = 1, interrupts = true})
              (fold_entries NONE (fn (_, exec) => fn () => force_exec exec) node));

    in (versions, commands, execs, execution') end);



(** global state **)

val global_state = Synchronized.var "Document" init_state;

fun state () = Synchronized.value global_state;
val change_state = Synchronized.change global_state;

end;


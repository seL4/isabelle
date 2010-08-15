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
  val create_id: unit -> id
  val parse_id: string -> id
  val print_id: id -> string
  type edit = string * ((command_id * command_id option) list) option
  type state
  val init_state: state
  val define_command: command_id -> string -> state -> state
  val edit: version_id -> version_id -> edit list -> state -> (command_id * exec_id) list * state
  val execute: version_id -> state -> state
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type id = int;
type version_id = id;
type command_id = id;
type exec_id = id;

val no_id = 0;

local
  val id_count = Synchronized.var "id" 0;
in
  fun create_id () =
    Synchronized.change_result id_count
      (fn i =>
        let val i' = i + 1
        in (i', i') end);
end;

val parse_id = Markup.parse_int;
val print_id = Markup.print_int;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ print_id id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ print_id id);



(** document structure **)

abstype entry = Entry of {next: command_id option, exec: exec_id option}
  and node = Node of entry Inttab.table  (*unique entries indexed by command_id, start with no_id*)
  and version = Version of node Graph.T  (*development graph wrt. static imports*)
with


(* command entries *)

fun make_entry next exec = Entry {next = next, exec = exec};

fun the_entry (Node entries) (id: command_id) =
  (case Inttab.lookup entries id of
    NONE => err_undef "command entry" id
  | SOME (Entry entry) => entry);

fun put_entry (id: command_id, entry: entry) (Node entries) =
  Node (Inttab.update (id, entry) entries);

fun put_entry_exec (id: command_id) exec node =
  let val {next, ...} = the_entry node id
  in put_entry (id, make_entry next exec) node end;

fun reset_entry_exec id = put_entry_exec id NONE;
fun set_entry_exec (id, exec_id) = put_entry_exec id (SOME exec_id);


(* iterate entries *)

fun fold_entries id0 f (node as Node entries) =
  let
    fun apply NONE x = x
      | apply (SOME id) x =
          let val entry = the_entry node id
          in apply (#next entry) (f (id, entry) x) end;
  in if Inttab.defined entries id0 then apply (SOME id0) else I end;

fun first_entry P node =
  let
    fun first _ NONE = NONE
      | first prev (SOME id) =
          let val entry = the_entry node id
          in if P (id, entry) then SOME (prev, id, entry) else first (SOME id) (#next entry) end;
  in first NONE (SOME no_id) end;


(* modify entries *)

fun insert_after (id: command_id) (id2: command_id) node =
  let val {next, exec} = the_entry node id in
    node
    |> put_entry (id, make_entry (SOME id2) exec)
    |> put_entry (id2, make_entry next NONE)
  end;

fun delete_after (id: command_id) node =
  let val {next, exec} = the_entry node id in
    (case next of
      NONE => error ("No next entry to delete: " ^ print_id id)
    | SOME id2 =>
        node |>
          (case #next (the_entry node id2) of
            NONE => put_entry (id, make_entry NONE exec)
          | SOME id3 => put_entry (id, make_entry (SOME id3) exec) #> reset_entry_exec id3))
  end;


(* node edits *)

type edit =
  string *  (*node name*)
  ((command_id * command_id option) list) option;  (*NONE: remove, SOME: insert/remove commands*)

val empty_node = Node (Inttab.make [(no_id, make_entry NONE (SOME no_id))]);

fun edit_node (id, SOME id2) = insert_after id id2
  | edit_node (id, NONE) = delete_after id;


(* version operations *)

fun nodes_of (Version nodes) = nodes;
val node_names_of = Graph.keys o nodes_of;

fun edit_nodes (name, SOME edits) (Version nodes) =
      Version (nodes
        |> Graph.default_node (name, empty_node)
        |> Graph.map_node name (fold edit_node edits))
  | edit_nodes (name, NONE) (Version nodes) = Version (Graph.del_node name nodes);

val empty_version = Version Graph.empty;

fun the_node version name =
  Graph.get_node (nodes_of version) name handle Graph.UNDEF _ => empty_node;

fun put_node name node (Version nodes) =
  Version (Graph.map_node name (K node) nodes);  (* FIXME Graph.UNDEF !? *)

end;



(** global state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,                   (*version_id -> document content*)
  commands: Toplevel.transition Inttab.table,       (*command_id -> transition function*)
  execs: Toplevel.state option lazy Inttab.table,   (*exec_id -> execution process*)
  execution: unit future list}                      (*global execution process*)
with

fun make_state (versions, commands, execs, execution) =
  State {versions = versions, commands = commands, execs = execs, execution = execution};

fun map_state f (State {versions, commands, execs, execution}) =
  make_state (f (versions, commands, execs, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)],
    Inttab.make [(no_id, Toplevel.empty)],
    Inttab.make [(no_id, Lazy.value (SOME Toplevel.toplevel))],
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
      val tr =
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Outer_Syntax.prepare_command (Position.id id_string) text) ();
      val commands' =
        Inttab.update_new (id, Toplevel.put_id id_string tr) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execs, execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME tr => tr);


(* command executions *)

fun define_exec (id: exec_id) exec =
  map_state (fn (versions, commands, execs, execution) =>
    let val execs' = Inttab.update_new (id, exec) execs
      handle Inttab.DUP dup => err_dup "command execution" dup
    in (versions, commands, execs', execution) end);

fun the_exec (State {execs, ...}) (id: exec_id) =
  (case Inttab.lookup execs id of
    NONE => err_undef "command execution" id
  | SOME exec => exec);

end;



(** editing **)

(* edit *)

local

fun is_changed node' (id, {next = _, exec}) =
  (case try (the_entry node') id of
    NONE => true
  | SOME {next = _, exec = exec'} => exec' <> exec);

fun new_exec name (id: command_id) (exec_id, updates, state) =
  let
    val exec = the_exec state exec_id;
    val exec_id' = create_id ();
    val tr = Toplevel.put_id (print_id exec_id') (the_command state id);
    val exec' =
      Lazy.lazy (fn () =>
        (case Lazy.force exec of
          NONE => NONE
        | SOME st => Toplevel.run_command name tr st));
    val state' = define_exec exec_id' exec' state;
  in (exec_id', (id, exec_id') :: updates, state') end;

in

fun edit (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val new_version = fold edit_nodes edits old_version;

    fun update_node name (rev_updates, version, st) =
      let val node = the_node version name in
        (case first_entry (is_changed (the_node old_version name)) node of
          NONE => (rev_updates, version, st)
        | SOME (prev, id, _) =>
            let
              val prev_exec = the (#exec (the_entry node (the prev)));
              val (_, rev_upds, st') =
                fold_entries id (new_exec name o #1) node (prev_exec, [], st);
              val node' = fold set_entry_exec rev_upds node;
            in (rev_upds @ rev_updates, put_node name node' version, st') end)
      end;

    (* FIXME proper node deps *)
    val (rev_updates, new_version', state') =
      fold update_node (node_names_of new_version) ([], new_version, state);
    val state'' = define_version new_id new_version' state';
  in (rev rev_updates, state'') end;

end;


(* execute *)

fun execute version_id state =
  state |> map_state (fn (versions, commands, execs, execution) =>
    let
      val version = the_version state version_id;

      fun force_exec NONE = ()
        | force_exec (SOME exec_id) = ignore (Lazy.force (the_exec state exec_id));

      val _ = List.app Future.cancel execution;
      fun await_cancellation () = uninterruptible (fn _ => Future.join_results) execution;

      val execution' = (* FIXME proper node deps *)
        node_names_of version |> map (fn name =>
          Future.fork_pri 1 (fn () =>
            (await_cancellation ();
              fold_entries no_id (fn (_, {exec, ...}) => fn () => force_exec exec)
                (the_node version name) ())));
    in (versions, commands, execs, execution') end);

end;


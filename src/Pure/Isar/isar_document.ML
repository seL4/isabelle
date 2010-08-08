(*  Title:      Pure/Isar/isar_document.ML
    Author:     Makarius

Interactive Isar documents, which are structured as follows:

  - history: tree of documents (i.e. changes without merge)
  - document: graph of nodes (cf. theory files)
  - node: linear set of commands, potentially with proof structure
*)

structure Isar_Document: sig end =
struct

(* unique identifiers *)

local
  val id_count = Synchronized.var "id" 0;
in
  fun create_id () =
    Synchronized.change_result id_count
      (fn i =>
        let val i' = i + 1
        in ("i" ^ string_of_int i', i') end);
end;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ quote id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ quote id);



(** documents **)

datatype entry = Entry of {next: Document.command_id option, state: Document.state_id option};
type node = entry Symtab.table; (*unique command entries indexed by command_id, start with no_id*)
type document = node Graph.T;   (*development graph via static imports*)


(* command entries *)

fun make_entry next state = Entry {next = next, state = state};

fun the_entry (node: node) (id: Document.command_id) =
  (case Symtab.lookup node id of
    NONE => err_undef "command entry" id
  | SOME (Entry entry) => entry);

fun put_entry (id: Document.command_id, entry: entry) = Symtab.update (id, entry);

fun put_entry_state (id: Document.command_id) state (node: node) =
  let val {next, ...} = the_entry node id
  in put_entry (id, make_entry next state) node end;

fun reset_entry_state id = put_entry_state id NONE;
fun set_entry_state (id, state_id) = put_entry_state id (SOME state_id);


(* iterate entries *)

fun fold_entries id0 f (node: node) =
  let
    fun apply NONE x = x
      | apply (SOME id) x =
          let val entry = the_entry node id
          in apply (#next entry) (f (id, entry) x) end;
  in if Symtab.defined node id0 then apply (SOME id0) else I end;

fun first_entry P (node: node) =
  let
    fun first _ NONE = NONE
      | first prev (SOME id) =
          let val entry = the_entry node id
          in if P (id, entry) then SOME (prev, id, entry) else first (SOME id) (#next entry) end;
  in first NONE (SOME Document.no_id) end;


(* modify entries *)

fun insert_after (id: Document.command_id) (id2: Document.command_id) (node: node) =
  let val {next, state} = the_entry node id in
    node
    |> put_entry (id, make_entry (SOME id2) state)
    |> put_entry (id2, make_entry next NONE)
  end;

fun delete_after (id: Document.command_id) (node: node) =
  let val {next, state} = the_entry node id in
    (case next of
      NONE => error ("No next entry to delete: " ^ quote id)
    | SOME id2 =>
        node |>
          (case #next (the_entry node id2) of
            NONE => put_entry (id, make_entry NONE state)
          | SOME id3 => put_entry (id, make_entry (SOME id3) state) #> reset_entry_state id3))
  end;


(* node operations *)

val empty_node: node = Symtab.make [(Document.no_id, make_entry NONE (SOME Document.no_id))];

fun the_node (document: document) name =
  Graph.get_node document name handle Graph.UNDEF _ => empty_node;

fun edit_node (id, SOME id2) = insert_after id id2
  | edit_node (id, NONE) = delete_after id;

fun edit_nodes (name, SOME edits) =
      Graph.default_node (name, empty_node) #>
      Graph.map_node name (fold edit_node edits)
  | edit_nodes (name, NONE) = Graph.del_node name;



(** global configuration **)

(* states *)

local

val global_states =
  Unsynchronized.ref (Symtab.make [(Document.no_id, Lazy.value (SOME Toplevel.toplevel))]);

in

fun define_state (id: Document.state_id) state =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_states (Symtab.update_new (id, state))
      handle Symtab.DUP dup => err_dup "state" dup);

fun the_state (id: Document.state_id) =
  (case Symtab.lookup (! global_states) id of
    NONE => err_undef "state" id
  | SOME state => state);

end;


(* commands *)

local

val global_commands = Unsynchronized.ref (Symtab.make [(Document.no_id, Toplevel.empty)]);

in

fun define_command (id: Document.command_id) tr =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_commands (Symtab.update_new (id, Toplevel.put_id id tr))
      handle Symtab.DUP dup => err_dup "command" dup);

fun the_command (id: Document.command_id) =
  (case Symtab.lookup (! global_commands) id of
    NONE => err_undef "command" id
  | SOME tr => tr);

end;


(* document versions *)

local

val global_documents = Unsynchronized.ref (Symtab.make [(Document.no_id, Graph.empty: document)]);

in

fun define_document (id: Document.version_id) document =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_documents (Symtab.update_new (id, document))
      handle Symtab.DUP dup => err_dup "document" dup);

fun the_document (id: Document.version_id) =
  (case Symtab.lookup (! global_documents) id of
    NONE => err_undef "document" id
  | SOME document => document);

end;



(** main operations **)

(* execution *)

local

val execution: unit future list Unsynchronized.ref = Unsynchronized.ref [];

fun force_state NONE = ()
  | force_state (SOME state_id) = ignore (Lazy.force (the_state state_id));

in

fun execute document =
  NAMED_CRITICAL "Isar" (fn () =>
    let
      val old_execution = ! execution;
      val _ = List.app Future.cancel old_execution;
      fun await_cancellation () = uninterruptible (K Future.join_results) old_execution;
      (* FIXME proper node deps *)
      val new_execution = Graph.keys document |> map (fn name =>
        Future.fork_pri 1 (fn () =>
          let
            val _ = await_cancellation ();
            val exec =
              fold_entries Document.no_id (fn (_, {state, ...}) => fn () => force_state state)
                (the_node document name);
          in exec () end));
    in execution := new_execution end);

end;


(* editing *)

local

fun is_changed node' (id, {next = _, state}) =
  (case try (the_entry node') id of
    NONE => true
  | SOME {next = _, state = state'} => state' <> state);

fun new_state name (id: Document.command_id) (state_id, updates) =
  let
    val state = the_state state_id;
    val state_id' = create_id ();
    val tr = Toplevel.put_id state_id' (the_command id);
    val state' =
      Lazy.lazy (fn () =>
        (case Lazy.force state of
          NONE => NONE
        | SOME st => Toplevel.run_command name tr st));
    val _ = define_state state_id' state';
  in (state_id', (id, state_id') :: updates) end;

fun updates_status updates =
  implode (map (fn (id, state_id) => Markup.markup (Markup.edit id state_id) "") updates)
  |> Markup.markup Markup.assign
  |> Output.status;

in

fun edit_document (old_id: Document.version_id) (new_id: Document.version_id) edits =
  NAMED_CRITICAL "Isar" (fn () =>
    let
      val old_document = the_document old_id;
      val new_document = fold edit_nodes edits old_document;

      fun update_node name node =
        (case first_entry (is_changed (the_node old_document name)) node of
          NONE => ([], node)
        | SOME (prev, id, _) =>
            let
              val prev_state_id = the (#state (the_entry node (the prev)));
              val (_, updates) = fold_entries id (new_state name o #1) node (prev_state_id, []);
              val node' = fold set_entry_state updates node;
            in (rev updates, node') end);

      (* FIXME proper node deps *)
      val (updatess, new_document') =
        (Graph.keys new_document, new_document)
          |-> fold_map (fn name => Graph.map_node_yield name (update_node name));

      val _ = define_document new_id new_document';
      val _ = updates_status (flat updatess);
      val _ = execute new_document';
    in () end);

end;



(** concrete syntax **)

val _ =
  Outer_Syntax.internal_command "Isar.define_command"
    (Parse.string -- Parse.string >> (fn (id, text) =>
      Toplevel.position (Position.id_only id) o
      Toplevel.imperative (fn () =>
        define_command id (Outer_Syntax.prepare_command (Position.id id) text))));

val _ =
  Outer_Syntax.internal_command "Isar.edit_document"
    (Parse.string -- Parse.string --
      Parse_Value.list
        (Parse.string -- Scan.option (Parse_Value.list (Parse.string -- Scan.option Parse.string)))
      >> (fn ((old_id, new_id), edits) =>
          Toplevel.position (Position.id_only new_id) o
          Toplevel.imperative (fn () => edit_document old_id new_id edits)));

end;


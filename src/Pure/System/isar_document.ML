(*  Title:      Pure/System/isar_document.ML
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
        in (i', i') end);
end;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ Document.print_id id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ Document.print_id id);


(** documents **)

datatype entry = Entry of {next: Document.command_id option, exec: Document.exec_id option};
type node = entry Inttab.table; (*unique command entries indexed by command_id, start with no_id*)
type document = node Graph.T;   (*development graph via static imports*)


(* command entries *)

fun make_entry next exec = Entry {next = next, exec = exec};

fun the_entry (node: node) (id: Document.command_id) =
  (case Inttab.lookup node id of
    NONE => err_undef "command entry" id
  | SOME (Entry entry) => entry);

fun put_entry (id: Document.command_id, entry: entry) = Inttab.update (id, entry);

fun put_entry_exec (id: Document.command_id) exec (node: node) =
  let val {next, ...} = the_entry node id
  in put_entry (id, make_entry next exec) node end;

fun reset_entry_exec id = put_entry_exec id NONE;
fun set_entry_exec (id, exec_id) = put_entry_exec id (SOME exec_id);


(* iterate entries *)

fun fold_entries id0 f (node: node) =
  let
    fun apply NONE x = x
      | apply (SOME id) x =
          let val entry = the_entry node id
          in apply (#next entry) (f (id, entry) x) end;
  in if Inttab.defined node id0 then apply (SOME id0) else I end;

fun first_entry P (node: node) =
  let
    fun first _ NONE = NONE
      | first prev (SOME id) =
          let val entry = the_entry node id
          in if P (id, entry) then SOME (prev, id, entry) else first (SOME id) (#next entry) end;
  in first NONE (SOME Document.no_id) end;


(* modify entries *)

fun insert_after (id: Document.command_id) (id2: Document.command_id) (node: node) =
  let val {next, exec} = the_entry node id in
    node
    |> put_entry (id, make_entry (SOME id2) exec)
    |> put_entry (id2, make_entry next NONE)
  end;

fun delete_after (id: Document.command_id) (node: node) =
  let val {next, exec} = the_entry node id in
    (case next of
      NONE => error ("No next entry to delete: " ^ Document.print_id id)
    | SOME id2 =>
        node |>
          (case #next (the_entry node id2) of
            NONE => put_entry (id, make_entry NONE exec)
          | SOME id3 => put_entry (id, make_entry (SOME id3) exec) #> reset_entry_exec id3))
  end;


(* node operations *)

val empty_node: node = Inttab.make [(Document.no_id, make_entry NONE (SOME Document.no_id))];

fun the_node (document: document) name =
  Graph.get_node document name handle Graph.UNDEF _ => empty_node;

fun edit_node (id, SOME id2) = insert_after id id2
  | edit_node (id, NONE) = delete_after id;

fun edit_nodes (name, SOME edits) =
      Graph.default_node (name, empty_node) #>
      Graph.map_node name (fold edit_node edits)
  | edit_nodes (name, NONE) = Graph.del_node name;



(** global configuration **)

(* command executions *)

local

val global_execs =
  Unsynchronized.ref (Inttab.make [(Document.no_id, Lazy.value (SOME Toplevel.toplevel))]);

in

fun define_exec (id: Document.exec_id) exec =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_execs (Inttab.update_new (id, exec))
      handle Inttab.DUP dup => err_dup "exec" dup);

fun the_exec (id: Document.exec_id) =
  (case Inttab.lookup (! global_execs) id of
    NONE => err_undef "exec" id
  | SOME exec => exec);

end;


(* commands *)

local

val global_commands = Unsynchronized.ref (Inttab.make [(Document.no_id, Toplevel.empty)]);

in

fun define_command (id: Document.command_id) text =
  let
    val id_string = Document.print_id id;
    val tr =
      Position.setmp_thread_data (Position.id_only id_string) (fn () =>
        Outer_Syntax.prepare_command (Position.id id_string) text) ();
  in
    NAMED_CRITICAL "Isar" (fn () =>
      Unsynchronized.change global_commands (Inttab.update_new (id, Toplevel.put_id id_string tr))
        handle Inttab.DUP dup => err_dup "command" dup)
  end;

fun the_command (id: Document.command_id) =
  (case Inttab.lookup (! global_commands) id of
    NONE => err_undef "command" id
  | SOME tr => tr);

end;


(* document versions *)

local

val global_documents = Unsynchronized.ref (Inttab.make [(Document.no_id, Graph.empty: document)]);

in

fun define_document (id: Document.version_id) document =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_documents (Inttab.update_new (id, document))
      handle Inttab.DUP dup => err_dup "document" dup);

fun the_document (id: Document.version_id) =
  (case Inttab.lookup (! global_documents) id of
    NONE => err_undef "document" id
  | SOME document => document);

end;



(** document editing **)

(* execution *)

local

val execution: unit future list Unsynchronized.ref = Unsynchronized.ref [];

fun force_exec NONE = ()
  | force_exec (SOME exec_id) = ignore (Lazy.force (the_exec exec_id));

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
              fold_entries Document.no_id (fn (_, {exec, ...}) => fn () => force_exec exec)
                (the_node document name);
          in exec () end));
    in execution := new_execution end);

end;


(* editing *)

local

fun is_changed node' (id, {next = _, exec}) =
  (case try (the_entry node') id of
    NONE => true
  | SOME {next = _, exec = exec'} => exec' <> exec);

fun new_exec name (id: Document.command_id) (exec_id, updates) =
  let
    val exec = the_exec exec_id;
    val exec_id' = create_id ();
    val tr = Toplevel.put_id (Document.print_id exec_id') (the_command id);
    val exec' =
      Lazy.lazy (fn () =>
        (case Lazy.force exec of
          NONE => NONE
        | SOME st => Toplevel.run_command name tr st));
    val _ = define_exec exec_id' exec';
  in (exec_id', (id, exec_id') :: updates) end;

fun updates_status new_id updates =
  implode (map (fn (id, exec_id) => Markup.markup (Markup.edit id exec_id) "") updates)
  |> Markup.markup (Markup.assign new_id)
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
              val prev_exec_id = the (#exec (the_entry node (the prev)));
              val (_, updates) = fold_entries id (new_exec name o #1) node (prev_exec_id, []);
              val node' = fold set_entry_exec updates node;
            in (rev updates, node') end);

      (* FIXME proper node deps *)
      val (updatess, new_document') =
        (Graph.keys new_document, new_document)
          |-> fold_map (fn name => Graph.map_node_yield name (update_node name));

      val _ = define_document new_id new_document';
      val _ = updates_status new_id (flat updatess);
      val _ = execute new_document';
    in () end);

end;



(** Isabelle process commands **)

val _ =
  Isabelle_Process.add_command "Isar_Document.define_command"
    (fn [id, text] => define_command (Document.parse_id id) text);

val _ =
  Isabelle_Process.add_command "Isar_Document.edit_document"
    (fn [old_id, new_id, edits] =>
      edit_document (Document.parse_id old_id) (Document.parse_id new_id)
        (XML_Data.dest_list (XML_Data.dest_pair XML_Data.dest_string
            (XML_Data.dest_option (XML_Data.dest_list
                (XML_Data.dest_pair XML_Data.dest_int
                  (XML_Data.dest_option XML_Data.dest_int))))) (YXML.parse_body edits)));

end;


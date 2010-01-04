(*  Title:      Pure/Isar/isar_document.ML
    Author:     Makarius

Interactive Isar documents.
*)

structure Isar_Document: sig end =
struct

(* unique identifiers *)

type state_id = string;
type command_id = string;
type document_id = string;

val no_id = "";

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

(* command entries *)

datatype entry = Entry of {next: command_id option, state: state_id option};
fun make_entry next state = Entry {next = next, state = state};

fun the_entry entries (id: command_id) =
  (case Symtab.lookup entries id of
    NONE => err_undef "document entry" id
  | SOME (Entry entry) => entry);

fun put_entry (id: command_id, entry: entry) = Symtab.update (id, entry);

fun put_entry_state (id: command_id) state entries =
  let val {next, ...} = the_entry entries id
  in put_entry (id, make_entry next state) entries end;

fun reset_entry_state id = put_entry_state id NONE;
fun set_entry_state (id, state_id) = put_entry_state id (SOME state_id);


(* document *)

datatype document = Document of
 {dir: Path.T,                   (*master directory*)
  name: string,                  (*theory name*)
  entries: entry Symtab.table};  (*unique command entries indexed by command_id, start with no_id*)

fun make_document dir name entries =
  Document {dir = dir, name = name, entries = entries};

fun map_entries f (Document {dir, name, entries}) =
  make_document dir name (f entries);


(* iterate entries *)

fun fold_entries id0 f (Document {entries, ...}) =
  let
    fun apply NONE x = x
      | apply (SOME id) x =
          let val entry = the_entry entries id
          in apply (#next entry) (f (id, entry) x) end;
  in if Symtab.defined entries id0 then apply (SOME id0) else I end;

fun first_entry P (Document {entries, ...}) =
  let
    fun first _ NONE = NONE
      | first prev (SOME id) =
          let val entry = the_entry entries id
          in if P (id, entry) then SOME (prev, id, entry) else first (SOME id) (#next entry) end;
  in first NONE (SOME no_id) end;


(* modify entries *)

fun insert_after (id: command_id) (id2: command_id) = map_entries (fn entries =>
  let val {next, state} = the_entry entries id in
    entries
    |> put_entry (id, make_entry (SOME id2) state)
    |> put_entry (id2, make_entry next NONE)
  end);

fun delete_after (id: command_id) = map_entries (fn entries =>
  let val {next, state} = the_entry entries id in
    (case next of
      NONE => error ("No next entry to delete: " ^ quote id)
    | SOME id2 =>
        entries |>
          (case #next (the_entry entries id2) of
            NONE => put_entry (id, make_entry NONE state)
          | SOME id3 => put_entry (id, make_entry (SOME id3) state) #> reset_entry_state id3))
  end);



(** global configuration **)

(* states *)

val empty_state = Future.value (SOME Toplevel.toplevel);

local

val global_states = Unsynchronized.ref (Symtab.make [(no_id, empty_state)]);

in

fun define_state (id: state_id) =
  Unsynchronized.change global_states (Symtab.update_new (id, empty_state))
    handle Symtab.DUP dup => err_dup "state" dup;

fun put_state (id: state_id) state =
  Unsynchronized.change global_states (Symtab.update (id, state));

fun the_state (id: state_id) =
  (case Symtab.lookup (! global_states) id of
    NONE => err_undef "state" id
  | SOME state => state);

end;


(* commands *)

local

val global_commands = Unsynchronized.ref (Symtab.make [(no_id, Toplevel.empty)]);

in

fun define_command id tr =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_commands (Symtab.update_new (id, Toplevel.put_id id tr))
      handle Symtab.DUP dup => err_dup "command" dup);

fun the_command (id: command_id) =
  (case Symtab.lookup (! global_commands) id of
    NONE => err_undef "command" id
  | SOME tr => tr);

end;


(* documents *)

local

val global_documents = Unsynchronized.ref (Symtab.empty: document Symtab.table);

in

fun define_document (id: document_id) document =
  NAMED_CRITICAL "Isar" (fn () =>
    Unsynchronized.change global_documents (Symtab.update_new (id, document))
      handle Symtab.DUP dup => err_dup "document" dup);

fun the_document (id: document_id) =
  (case Symtab.lookup (! global_documents) id of
    NONE => err_undef "document" id
  | SOME document => document);

end;



(** main operations **)

(* begin/end document *)

val no_entries = Symtab.make [(no_id, make_entry NONE (SOME no_id))];

fun begin_document (id: document_id) path =
  let
    val (dir, name) = ThyLoad.split_thy_path path;
    val _ = define_document id (make_document dir name no_entries);
  in () end;

fun end_document (id: document_id) =
  NAMED_CRITICAL "Isar" (fn () =>
    let
      val document as Document {name, ...} = the_document id;
      val end_state =
        the_state (the (#state (#3 (the
          (first_entry (fn (_, {next, ...}) => is_none next) document)))));
      val _ =
        Future.fork_deps [end_state] (fn () =>
          (case Future.join end_state of
            SOME st =>
             (Toplevel.run_command name (Toplevel.put_id id (Toplevel.commit_exit Position.none)) st;
              ThyInfo.touch_child_thys name;
              ThyInfo.register_thy name)
          | NONE => error ("Failed to finish theory " ^ quote name)));
    in () end);


(* document editing *)

local

fun is_changed entries' (id, {next = _, state}) =
  (case try (the_entry entries') id of
    NONE => true
  | SOME {next = _, state = state'} => state' <> state);

fun new_state name (id, _) (state_id, updates) =
  let
    val state_id' = create_id ();
    val _ = define_state state_id';
    val tr = Toplevel.put_id state_id' (the_command id);
    fun make_state' () =
      let
        val state = the_state state_id;
        val state' =
          Future.fork_deps [state] (fn () =>
            (case Future.join state of
              NONE => NONE
            | SOME st => Toplevel.run_command name tr st));
      in put_state state_id' state' end;
  in (state_id', ((id, state_id'), make_state') :: updates) end;

fun report_updates [] = ()
  | report_updates updates =
      implode (map (fn (id, state_id) => Markup.markup (Markup.edit id state_id) "") updates)
      |> Markup.markup Markup.assign
      |> Output.status;

in

fun edit_document (old_id: document_id) (new_id: document_id) edits =
  NAMED_CRITICAL "Isar" (fn () =>
    let
      val old_document as Document {name, entries = old_entries, ...} = the_document old_id;
      val new_document as Document {entries = new_entries, ...} = old_document
        |> fold (fn (id, SOME id2) => insert_after id id2 | (id, NONE) => delete_after id) edits;

      fun cancel_old id = fold_entries id
        (fn (_, {state = SOME state_id, ...}) => K (Future.cancel (the_state state_id)) | _ => K ())
        old_document ();

      val (updates, new_document') =
        (case first_entry (is_changed old_entries) new_document of
          NONE =>
            (case first_entry (is_changed new_entries) old_document of
              NONE => ([], new_document)
            | SOME (_, id, _) => (cancel_old id; ([], new_document)))
        | SOME (prev, id, _) =>
            let
              val _ = cancel_old id;
              val prev_state_id = the (#state (the_entry new_entries (the prev)));
              val (_, updates) = fold_entries id (new_state name) new_document (prev_state_id, []);
              val new_document' = new_document |> map_entries (fold (set_entry_state o #1) updates);
            in (rev updates, new_document') end);

      val _ = define_document new_id new_document';
      val _ = report_updates (map #1 updates);
      val _ = List.app (fn (_, run) => run ()) updates;
    in () end);

end;



(** concrete syntax **)

local structure P = OuterParse structure V = ValueParse in

val _ =
  OuterSyntax.internal_command "Isar.define_command"
    (P.string -- P.string >> (fn (id, text) =>
      Toplevel.position (Position.id_only id) o
      Toplevel.imperative (fn () =>
        define_command id (OuterSyntax.prepare_command (Position.id id) text))));

val _ =
  OuterSyntax.internal_command "Isar.begin_document"
    (P.string -- P.string >> (fn (id, path) =>
      Toplevel.imperative (fn () => begin_document id (Path.explode path))));

val _ =
  OuterSyntax.internal_command "Isar.end_document"
    (P.string >> (fn id => Toplevel.imperative (fn () => end_document id)));

val _ =
  OuterSyntax.internal_command "Isar.edit_document"
    (P.string -- P.string -- V.list (P.string -- (P.string >> SOME) || P.string >> rpair NONE)
      >> (fn ((id, new_id), edits) =>
        Toplevel.position (Position.id_only new_id) o
        Toplevel.imperative (fn () => edit_document id new_id edits)));

end;

end;


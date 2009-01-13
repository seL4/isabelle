(*  Title:      Pure/Isar/isar_document.ML
    Author:     Makarius

Interactive Isar documents.
*)

signature ISAR_DOCUMENT =
sig
  type state_id = string
  type command_id = string
  type document_id = string
  val define_command: command_id -> Toplevel.transition -> unit
  val begin_document: document_id -> Path.T -> unit
  val edit_document: document_id -> document_id -> (command_id * command_id option) list -> unit
  val end_document: document_id -> unit
end;

structure IsarDocument: ISAR_DOCUMENT =
struct

(* unique identifiers *)

type document_id = string;
type command_id = string;
type state_id = string;

val no_id = "";

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ quote id);
fun err_undef kind id = error ("Unknown " ^ kind ^ ": " ^ quote id);


(** execution states **)

(* command status *)

datatype status =
  Unprocessed |
  Running of Toplevel.state option future |
  Failed |
  Finished of Toplevel.state;

fun status_markup Unprocessed = Markup.unprocessed
  | status_markup (Running future) = Markup.running (Task_Queue.str_of_task (Future.task_of future))
  | status_markup Failed = Markup.failed
  | status_markup (Finished _) = Markup.finished;

fun status_update tr state status =
  (case status of
    Unprocessed => SOME (Running (Future.fork_pri 1 (fn () =>
      (case Toplevel.transition true tr state of
        NONE => (Toplevel.error_msg tr (ERROR "Cannot terminate here!", ""); NONE)
      | SOME (_, SOME err) => (Toplevel.error_msg tr err; NONE)
      | SOME (state', NONE) => SOME state'))))
  | Running future =>
      (case Future.peek future of
        NONE => NONE
      | SOME (Exn.Result NONE) => SOME Failed
      | SOME (Exn.Result (SOME state')) => SOME (Finished state')
      | SOME (Exn.Exn exn) => (Toplevel.error_msg tr (exn, ""); SOME Failed))
  | _ => NONE);


(* state *)

datatype state = State of
 {prev: state_id option,
  command: command_id,
  status: status};

fun make_state prev command status = State {prev = prev, command = command, status = status};



(** documents **)

(* command entries *)

datatype entry = Entry of
 {prev: command_id option,
  next: command_id option,
  state: state_id};

fun make_entry prev next state = Entry {prev = prev, next = next, state = state};

fun the_entry entries (id: command_id) =
  (case Symtab.lookup entries id of
    NONE => err_undef "document entry" id
  | SOME (Entry entry) => entry);

fun put_entry (id: command_id, entry: entry) = Symtab.update (id, entry);

fun map_entry (id: command_id) f entries =
  let
    val {prev, next, state} = the_entry entries id;
    val (prev', next', state') = f (prev, next, state);
  in put_entry (id, make_entry prev' next' state') entries end;


(* document *)

datatype document = Document of
 {dir: Path.T,                    (*master directory*)
  name: string,                   (*theory name*)
  start: command_id,              (*empty start command*)
  entries: entry Symtab.table};   (*unique command entries indexed by command_id*)

fun make_document dir name start entries =
  Document {dir = dir, name = name, start = start, entries = entries};

fun map_entries f (Document {dir, name, start, entries}) =
  make_document dir name start (f entries);


fun fold_entries f (Document {start, entries, ...}) =
  let
    fun descend NONE x = x
      | descend (SOME id) x = descend_next id (f id x)
    and descend_next id = descend (#next (the_entry entries id));
  in descend_next start end;


fun insert_entry (id: command_id, id2: command_id) = map_entries (fn entries =>
  let
    val {prev, next, state} = the_entry entries id;
    val state2 = no_id;
  in
    entries |>
      (case next of
        NONE => put_entry (id2, make_entry (SOME id) NONE state2)
      | SOME id3 =>
          let val {next = next3, state = state3, ...} = the_entry entries id3 in
            put_entry (id, make_entry prev (SOME id2) state) #>
            put_entry (id2, make_entry (SOME id) (SOME id3) state2) #>
            put_entry (id3, make_entry (SOME id2) next3 state3)
          end)
  end);

fun delete_after_entry (id: command_id) = map_entries (fn entries =>
  let val {prev, next, state} = the_entry entries id in
    entries |>
      (case next of
        NONE => error ("Missing next entry: " ^ quote id)
      | SOME id2 =>
          (case #next (the_entry entries id2) of
            NONE => put_entry (id, make_entry prev NONE state)
          | SOME id3 =>
              let val {next = next3, state = state3, ...} = the_entry entries id3 in
                put_entry (id, make_entry prev (SOME id3) state) #>
                put_entry (id3, make_entry (SOME id) next3 state3)
              end))
  end);



(** global configuration **)

local
  val global_states = ref (Symtab.empty: state Symtab.table);
  val global_commands = ref (Symtab.empty: Toplevel.transition Symtab.table);
  val global_documents = ref (Symtab.empty: document Symtab.table);
in

fun change_states f = NAMED_CRITICAL "Isar" (fn () => change global_states f);
fun get_states () = NAMED_CRITICAL "Isar" (fn () => ! global_states);

fun change_commands f = NAMED_CRITICAL "Isar" (fn () => change global_commands f);
fun get_commands () = NAMED_CRITICAL "Isar" (fn () => ! global_commands);

fun change_documents f = NAMED_CRITICAL "Isar" (fn () => change global_documents f);
fun get_documents () = NAMED_CRITICAL "Isar" (fn () => ! global_documents);

fun init () = NAMED_CRITICAL "Isar" (fn () =>
 (global_states := Symtab.empty;
  global_commands := Symtab.empty;
  global_documents := Symtab.empty));

end;


fun define_state (id: state_id) state =
  change_states (Symtab.update_new (id, state))
    handle Symtab.DUP dup => err_dup "state" dup;

fun the_state (id: state_id) =
  (case Symtab.lookup (get_states ()) id of
    NONE => err_undef "state" id
  | SOME (State {status as Finished state, ...}) => state
  | _ => error ("Unfinished state " ^ id));


fun define_command id tr =
  change_commands (Symtab.update_new (id, Toplevel.put_id id tr))
    handle Symtab.DUP dup => err_dup ("command " ^ Toplevel.name_of tr) dup;

fun the_command (id: command_id) =
  (case Symtab.lookup (get_commands ()) id of
    NONE => err_undef "command" id
  | SOME cmd => cmd);


fun define_document (id: document_id) document =
  change_documents (Symtab.update_new (id, document))
    handle Symtab.DUP dup => err_dup "document" dup;

fun the_document (id: document_id) =
  (case Symtab.lookup (get_documents ()) id of
    NONE => err_undef "document" id
  | SOME doc => doc);


(* document editing *)

fun begin_document (id: document_id) path =
  let
    val (dir, name) = ThyLoad.split_thy_path path;
    val _ = define_command id Toplevel.empty;
    val _ = define_state id (make_state NONE id (Finished Toplevel.toplevel));
    val entries = Symtab.make [(id, make_entry NONE NONE id)];
    val _ = define_document id (make_document dir name id entries);
  in () end;

fun edit_document (id: document_id) (new_id: document_id) edits =
  let
    val document' =
      fold (fn (id, SOME id2) => insert_entry (id, id2) | (id, NONE) => delete_after_entry id)
        edits (the_document id);
    (* FIXME update states *)
    val _ = define_document new_id document';
  in () end;

fun end_document (id: document_id) = error "FIXME";



(** concrete syntax **)

local structure P = OuterParse structure V = ValueParse in

val _ =
  OuterSyntax.internal_command "Isar.define_command"
    (P.string -- P.string >> (fn (id, text) =>
      Toplevel.imperative (fn () =>
        define_command id (OuterSyntax.prepare_command (Position.id id) text))));

val _ =
  OuterSyntax.internal_command "Isar.begin_document"
    (P.string -- P.string >> (fn (id, path) =>
      Toplevel.imperative (fn () => begin_document id (Path.explode path))));

val _ =
  OuterSyntax.internal_command "Isar.edit_document"
    (P.string -- P.string -- V.list (P.string -- (P.string >> SOME) || P.string >> rpair NONE)
      >> (fn ((id, new_id), edits) => Toplevel.imperative (fn () => end_document id new_id edits)));

val _ =
  OuterSyntax.internal_command "Isar.end_document"
    (P.string >> (fn id => Toplevel.imperative (fn () => end_document id)));

end;

end;


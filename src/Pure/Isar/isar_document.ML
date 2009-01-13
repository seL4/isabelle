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
        NONE => (Toplevel.error_msg tr (SYS_ERROR "Cannot terminate here!", ""); NONE)
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


(* document *)

datatype document = Document of
 {dir: Path.T,                    (*master directory*)
  name: string,                   (*theory name*)
  commands: entry Symtab.table};  (*unique command entries indexed by command_id*)

fun make_document dir name commands = Document {dir = dir, name = name, commands = commands};



(** global configuration **)

fun err_dup kind id = sys_error ("Duplicate " ^ kind ^ ": " ^ quote id);
fun err_undef kind id = sys_error ("Unknown " ^ kind ^ ": " ^ quote id);

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
  | _ => sys_error ("Unfinished state " ^ id));


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


fun begin_document (id: document_id) path =
  let
    val (dir, name) = ThyLoad.split_thy_path path;
    val _ = define_command id Toplevel.empty;
    val _ = define_state id (make_state NONE id (Finished Toplevel.toplevel));
    val commands = Symtab.make [(id, make_entry NONE NONE id)];
    val _ = define_document id (make_document dir name commands);
  in () end;

fun edit_document (id: document_id) (new_id: document_id) edits =
  let
    val Document {dir, name, commands} = the_document id;
    val commands' = sys_error "FIXME";
    val _ = define_document new_id (make_document dir name commands');
  in () end;

fun end_document (id: document_id) = sys_error "FIXME";



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

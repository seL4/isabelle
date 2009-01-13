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
  val end_document: document_id -> unit
  val edit_document: document_id -> document_id -> (command_id * command_id option) list -> unit
end;

structure IsarDocument: ISAR_DOCUMENT =
struct


(* unique identifiers *)

type document_id = string;
type command_id = string;
type state_id = string;

fun new_id () = "isabelle:" ^ serial_string ();

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ quote id);
fun err_undef kind id = error ("Unknown " ^ kind ^ ": " ^ quote id);


(** execution states **)

(* command status *)

datatype status =
  Unprocessed |
  Running of Toplevel.state option future |
  Failed |
  Finished of Toplevel.state;

fun markup_status Unprocessed = Markup.unprocessed
  | markup_status (Running future) = Markup.running (Task_Queue.str_of_task (Future.task_of future))
  | markup_status Failed = Markup.failed
  | markup_status (Finished _) = Markup.finished;

fun update_status retry tr state status =
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
  | Failed => if retry then SOME Unprocessed else NONE
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
  state: state_id option};

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


(* iterating entries *)

fun fold_entries opt_id f (Document {start, entries, ...}) =
  let
    fun apply NONE x = x
      | apply (SOME id) x = apply (#next (the_entry entries id)) (f id x);
  in if is_some opt_id then apply opt_id else apply (SOME start) end;

fun get_first_entries opt_id f (Document {start, entries, ...}) =
  let
    fun get NONE = NONE
      | get (SOME id) = (case f id of NONE => get (#next (the_entry entries id)) | some => some);
  in if is_some opt_id then get opt_id else get (SOME start) end;

fun find_first_entries opt_id P =
  get_first_entries opt_id (fn x => if P x then SOME x else NONE);


(* modify entries *)

fun insert_entry (id: command_id, id2: command_id) = map_entries (fn entries =>
  let val {prev, next, state} = the_entry entries id in
    entries |>
      (case next of
        NONE => put_entry (id2, make_entry (SOME id) NONE NONE)
      | SOME id3 =>
          put_entry (id, make_entry prev (SOME id2) state) #>
          put_entry (id2, make_entry (SOME id) (SOME id3) NONE) #>
          put_entry (id3, make_entry (SOME id2) (#next (the_entry entries id3)) NONE))
  end);

fun delete_after (id: command_id) = map_entries (fn entries =>
  let val {prev, next, state} = the_entry entries id in
    entries |>
      (case next of
        NONE => error ("Missing next entry: " ^ quote id)
      | SOME id2 =>
          (case #next (the_entry entries id2) of
            NONE => put_entry (id, make_entry prev NONE state)
          | SOME id3 =>
              put_entry (id, make_entry prev (SOME id3) state) #>
              put_entry (id3, make_entry (SOME id) (#next (the_entry entries id3)) NONE)))
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
  | SOME (State state) => state);


fun define_command id tr =
  change_commands (Symtab.update_new (id, Toplevel.put_id id tr))
    handle Symtab.DUP dup => err_dup ("command " ^ Toplevel.name_of tr) dup;

fun the_command (id: command_id) =
  (case Symtab.lookup (get_commands ()) id of
    NONE => err_undef "command" id
  | SOME tr => tr);


fun define_document (id: document_id) document =
  change_documents (Symtab.update_new (id, document))
    handle Symtab.DUP dup => err_dup "document" dup;

fun the_document (id: document_id) =
  (case Symtab.lookup (get_documents ()) id of
    NONE => err_undef "document" id
  | SOME (Document doc) => doc);


(* begin/end document *)

fun begin_document (id: document_id) path =
  let
    val (dir, name) = ThyLoad.split_thy_path path;
    val _ = define_command id Toplevel.empty;
    val _ = define_state id (make_state NONE id (Finished Toplevel.toplevel));
    val entries = Symtab.make [(id, make_entry NONE NONE (SOME id))];
    val _ = define_document id (make_document dir name id entries);
  in () end;

fun end_document (id: document_id) = error "FIXME";


(* document editing *)

fun refresh_states old_document new_document =
  let
    val Document {entries = old_entries, ...} = old_document;
    val Document {entries = new_entries, ...} = new_document;

    fun is_changed id =
      (case try (the_entry new_entries) id of
        SOME {state = SOME _, ...} => false
      | _ => true);

    fun cancel_state id () =
      (case the_entry old_entries id of
        {state = SOME state_id, ...} =>
          (case the_state state_id of
            {status = Running future, ...} => Future.cancel future
          | _ => ())
      | _ => ());

    fun new_state id (prev_state_id, new_states) =
      let
        val state_id = new_id ();
        val state = make_state prev_state_id id Unprocessed;
        val _ = define_state state_id state;
      in (SOME state_id, (state_id, state) :: new_states) end;
  in
    (case find_first_entries NONE is_changed old_document of
      NONE => new_document
    | SOME id =>
        let
          val _ = fold_entries (SOME id) cancel_state old_document ();
          val (_, new_states) = fold_entries (SOME id) new_state new_document (NONE, []);
          (* FIXME update states *)
        in new_document end)
  end;

fun edit_document (id: document_id) (id': document_id) edits =
  let
    val document = Document (the_document id);
    val document' =
      document
      |> fold (fn (id, SOME id2) => insert_entry (id, id2) | (id, NONE) => delete_after id) edits
      |> refresh_states document;
    val _ = define_document id' document';
  in () end;



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
  OuterSyntax.internal_command "Isar.end_document"
    (P.string >> (fn id => Toplevel.imperative (fn () => end_document id)));

val _ =
  OuterSyntax.internal_command "Isar.edit_document"
    (P.string -- P.string -- V.list (P.string -- (P.string >> SOME) || P.string >> rpair NONE)
      >> (fn ((id, new_id), edits) => Toplevel.imperative (fn () => end_document id new_id edits)));

end;

end;


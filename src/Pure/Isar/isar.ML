(*  Title:      Pure/Isar/isar.ML
    Author:     Makarius

The global Isabelle/Isar state and main read-eval-print loop.
*)

signature ISAR =
sig
  type id = string
  val no_id: id
  val create_command: Toplevel.transition -> id
  val init_point: unit -> unit
  val state: unit -> Toplevel.state
  val context: unit -> Proof.context
  val goal: unit -> thm
  val print: unit -> unit
  val exn: unit -> (exn * string) option
  val >> : Toplevel.transition -> bool
  val >>> : Toplevel.transition list -> unit
  val linear_undo: int -> unit
  val undo: int -> unit
  val kill: unit -> unit
  val kill_proof: unit -> unit
  val crashes: exn list ref
  val toplevel_loop: {init: bool, welcome: bool, sync: bool, secure: bool} -> unit
  val loop: unit -> unit
  val main: unit -> unit
  val insert_command: id -> id -> unit
  val remove_command: id -> unit
end;

structure Isar: ISAR =
struct


(** individual toplevel commands **)

(* unique identification *)

type id = string;
val no_id : id = "";


(* command category *)

datatype category = Empty | Theory | Proof | Diag | Control;

fun category_of tr =
  let val name = Toplevel.name_of tr in
    if name = "" then Empty
    else if OuterKeyword.is_theory name then Theory
    else if OuterKeyword.is_proof name then Proof
    else if OuterKeyword.is_diag name then Diag
    else Control
  end;

val is_theory = fn Theory => true | _ => false;
val is_proper = fn Theory => true | Proof => true | _ => false;
val is_regular = fn Control => false | _ => true;


(* command status *)

datatype status =
  Unprocessed |
  Running |
  Failed of exn * string |
  Finished of Toplevel.state;

fun status_markup Unprocessed = Markup.unprocessed
  | status_markup Running = Markup.running
  | status_markup (Failed _) = Markup.failed
  | status_markup (Finished _) = Markup.finished;

fun run int tr state =
  (case Toplevel.transition int tr state of
    NONE => NONE
  | SOME (_, SOME err) => (Toplevel.error_msg tr err; SOME (Failed err))
  | SOME (state', NONE) => SOME (Finished state'));


(* datatype command *)

datatype command = Command of
 {category: category,
  transition: Toplevel.transition,
  status: status};

fun make_command (category, transition, status) =
  Command {category = category, transition = transition, status = status};

val empty_command =
  make_command (Empty, Toplevel.empty, Finished Toplevel.toplevel);

fun map_command f (Command {category, transition, status}) =
  make_command (f (category, transition, status));

fun map_status f = map_command (fn (category, transition, status) =>
  (category, transition, f status));


(* global collection of identified commands *)

fun err_dup id = sys_error ("Duplicate command " ^ quote id);
fun err_undef id = sys_error ("Unknown command " ^ quote id);

local val global_commands = ref (Graph.empty: command Graph.T) in

fun change_commands f = NAMED_CRITICAL "Isar" (fn () => change global_commands f)
  handle Graph.DUP bad => err_dup bad | Graph.UNDEF bad => err_undef bad;

fun get_commands () = NAMED_CRITICAL "Isar" (fn () => ! global_commands);

end;

fun add_edge (id1, id2) =
  if id1 = no_id orelse id2 = no_id then I else Graph.add_edge (id1, id2);


fun init_commands () = change_commands (K Graph.empty);

fun the_command id =
  let val Command cmd =
    if id = no_id then empty_command
    else (Graph.get_node (get_commands ()) id handle Graph.UNDEF bad => err_undef bad)
  in cmd end;

fun prev_command id =
  if id = no_id then no_id
  else
    (case Graph.imm_preds (get_commands ()) id handle Graph.UNDEF bad => err_undef bad of
      [] => no_id
    | [prev] => prev
    | _ => sys_error ("Non-linear command dependency " ^ quote id));

fun next_commands id =
  if id = no_id then []
  else Graph.imm_succs (get_commands ()) id handle Graph.UNDEF bad => err_undef bad;

fun descendant_commands ids =
  Graph.all_succs (get_commands ()) (distinct (op =) (filter_out (fn id => id = no_id) ids))
    handle Graph.UNDEF bad => err_undef bad;


(* maintain status *)

fun report_status markup id = Toplevel.status (#transition (the_command id)) markup;

fun update_status status id = change_commands (Graph.map_node id (map_status (K status)));

fun report_update_status status id =
  change_commands (Graph.map_node id (map_status (fn old_status =>
    let val markup = status_markup status
    in if markup <> status_markup old_status then report_status markup id else (); status end)));


(* create and dispose commands *)

fun create_command raw_tr =
  let
    val (id, tr) =
      (case Toplevel.get_id raw_tr of
        SOME id => (id, raw_tr)
      | NONE =>
          let val id =
            if ! Toplevel.debug then "isabelle:" ^ Toplevel.name_of raw_tr ^ serial_string ()
            else "isabelle:" ^ serial_string ()
          in (id, Toplevel.put_id id raw_tr) end);

    val cmd = make_command (category_of tr, tr, Unprocessed);
    val _ = change_commands (Graph.new_node (id, cmd));
  in id end;

fun dispose_commands ids =
  let
    val desc = descendant_commands ids;
    val _ = List.app (report_status Markup.disposed) desc;
    val _ = change_commands (Graph.del_nodes desc);
  in () end;


(* final state *)

fun the_state id =
  (case the_command id of
    {status = Finished state, ...} => state
  | {transition, ...} => error ("Unfinished command " ^ Toplevel.str_of transition));



(** TTY model -- single-threaded **)

(* global point *)

local val global_point = ref no_id in

fun change_point f = NAMED_CRITICAL "Isar" (fn () => change global_point f);
fun point () = NAMED_CRITICAL "Isar" (fn () => ! global_point);

end;


fun set_point id = change_point (K id);
fun init_point () = set_point no_id;

fun point_state () = NAMED_CRITICAL "Isar" (fn () =>
  let val id = point () in (id, the_state id) end);

fun state () = #2 (point_state ());

fun context () =
  Toplevel.context_of (state ())
    handle Toplevel.UNDEF => error "Unknown context";

fun goal () =
  #2 (#2 (Proof.get_goal (Toplevel.proof_of (state ()))))
    handle Toplevel.UNDEF => error "No goal present";

fun print () = Toplevel.print_state false (state ());


(* global failure status *)

local val global_exn = ref (NONE: (exn * string) option) in

fun set_exn err = global_exn := err;
fun exn () = ! global_exn;

end;


(* interactive state transformations *)

fun op >> raw_tr =
  let
    val id = create_command raw_tr;
    val {category, transition = tr, ...} = the_command id;
    val (prev, prev_state) = point_state ();
    val _ =
      if is_regular category
      then (dispose_commands (next_commands prev); change_commands (add_edge (prev, id)))
      else ();
  in
    (case run true tr prev_state of
      NONE => false
    | SOME (status as Failed err) => (update_status status id; set_exn (SOME err); true)
    | SOME status =>
       (update_status status id; set_exn NONE;
        if is_regular category then set_point id else ();
        true))
  end;

fun op >>> [] = ()
  | op >>> (tr :: trs) = if op >> tr then op >>> trs else ();


(* implicit navigation wrt. proper commands *)

local

fun err_undo () = error "Undo history exhausted";

fun find_category which id =
  (case #category (the_command id) of
    Empty => err_undo ()
  | category => if which category then id else find_category which (prev_command id));

fun find_begin_theory id =
  if id = no_id then err_undo ()
  else if is_some (Toplevel.init_of (#transition (the_command id))) then id
  else find_begin_theory (prev_command id);

fun undo_command id =
  (case Toplevel.init_of (#transition (the_command id)) of
    SOME name => prev_command id before ThyInfo.kill_thy name
  | NONE => prev_command id);

in

fun linear_undo n = change_point (funpow n (fn id => undo_command (find_category is_proper id)));

fun undo n = change_point (funpow n (fn id => undo_command
  (find_category (if Toplevel.is_proof (the_state id) then is_proper else is_theory) id)));

fun kill () = change_point (fn id => undo_command
  (if Toplevel.is_proof (the_state id) then find_category is_theory id else find_begin_theory id));

fun kill_proof () = change_point (fn id =>
  if Toplevel.is_proof (the_state id) then undo_command (find_category is_theory id)
  else raise Toplevel.UNDEF);

end;


(* toplevel loop *)

val crashes = ref ([]: exn list);

local

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
    val prev = point ();
    val prev_name = Toplevel.name_of (#transition (the_command prev));
    val prompt_markup =
      prev <> no_id ? Markup.markup
        (Markup.properties [(Markup.idN, prev), (Markup.nameN, prev_name)] Markup.prompt);
  in
    (case Source.get_single (Source.set_prompt (prompt_markup Source.default_prompt) src) of
      NONE => if secure then quit () else ()
    | SOME (tr, src') => if op >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn => (Output.error_msg (Toplevel.exn_message exn) handle crash =>
      (CRITICAL (fn () => change crashes (cons crash));
        warning "Recovering after Isar toplevel crash -- see also Isar.crashes");
      raw_loop secure src)
  end;

in

fun toplevel_loop {init, welcome, sync, secure} =
 (Context.set_thread_data NONE;
  if init then (init_point (); init_commands ()) else ();
  if welcome then writeln (Session.welcome ()) else ();
  uninterruptible (fn _ => fn () => raw_loop secure (OuterSyntax.isar sync)) ());

end;

fun loop () =
  toplevel_loop {init = false, welcome = false, sync = false, secure = Secure.is_secure ()};

fun main () =
  toplevel_loop {init = true, welcome = true, sync = false, secure = Secure.is_secure ()};



(** editor model **)

(* run commands *)

fun try_run id =
  (case try the_state (prev_command id) of
    NONE => ()
  | SOME state =>
      (case run true (#transition (the_command id)) state of
        NONE => ()
      | SOME status => report_update_status status id));

fun rerun_commands ids =
  (List.app (report_update_status Unprocessed) ids; List.app try_run ids);


(* modify document *)

fun insert_command prev id = NAMED_CRITICAL "Isar" (fn () =>
  let
    val nexts = next_commands prev;
    val _ = change_commands
     (fold (fn next => Graph.del_edge (prev, next)) nexts #> add_edge (prev, id) #>
      fold (fn next => Graph.add_edge (id, next)) nexts);
  in descendant_commands [id] end) |> rerun_commands;

fun remove_command id = NAMED_CRITICAL "Isar" (fn () =>
  let
    val prev = prev_command id;
    val nexts = next_commands id;
    val _ = change_commands
     (fold (fn next => Graph.del_edge (id, next)) nexts #>
      fold (fn next => add_edge (prev, next)) nexts);
  in descendant_commands nexts end) |> rerun_commands;


(* concrete syntax *)

local

structure P = struct open OuterParse open ValueParse end;
val op >> = Scan.>>;

in

val _ =
  OuterSyntax.internal_command "Isar.command"
    (P.string -- P.string >> (fn (id, text) =>
      Toplevel.imperative (fn () =>
        ignore (create_command (OuterSyntax.prepare_command (Position.id id) text)))));

val _ =
  OuterSyntax.internal_command "Isar.insert"
    (P.string -- P.string >> (fn (prev, id) =>
      Toplevel.imperative (fn () => insert_command prev id)));

val _ =
  OuterSyntax.internal_command "Isar.remove"
    (P.string >> (fn id => Toplevel.imperative (fn () => remove_command id)));

end;

end;

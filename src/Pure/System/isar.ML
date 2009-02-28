(*  Title:      Pure/Isar/isar.ML
    Author:     Makarius

The global Isabelle/Isar state and main read-eval-print loop.
*)

signature ISAR =
sig
  val init: unit -> unit
  val exn: unit -> (exn * string) option
  val state: unit -> Toplevel.state
  val context: unit -> Proof.context
  val goal: unit -> thm
  val print: unit -> unit
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

  type id = string
  val no_id: id
  val create_command: Toplevel.transition -> id
  val insert_command: id -> id -> unit
  val remove_command: id -> unit
end;

structure Isar: ISAR =
struct


(** TTY model -- SINGLE-THREADED! **)

(* the global state *)

type history = (Toplevel.state * Toplevel.transition) list;
  (*previous state, state transition -- regular commands only*)

local
  val global_history = ref ([]: history);
  val global_state = ref Toplevel.toplevel;
  val global_exn = ref (NONE: (exn * string) option);
in

fun edit_history count f = NAMED_CRITICAL "Isar" (fn () =>
  let
    fun edit 0 (st, hist) = (global_history := hist; global_state := st; global_exn := NONE)
      | edit n (st, hist) = edit (n - 1) (f st hist);
  in edit count (! global_state, ! global_history) end);

fun state () = NAMED_CRITICAL "Isar" (fn () => ! global_state);
fun set_state state = NAMED_CRITICAL "Isar" (fn () => global_state := state);

fun exn () = NAMED_CRITICAL "Isar" (fn () => ! global_exn);
fun set_exn exn =  NAMED_CRITICAL "Isar" (fn () => global_exn := exn);

end;


fun init () = edit_history 1 (K (K (Toplevel.toplevel, [])));

fun context () = Toplevel.context_of (state ())
  handle Toplevel.UNDEF => error "Unknown context";

fun goal () = #2 (#2 (Proof.get_goal (Toplevel.proof_of (state ()))))
  handle Toplevel.UNDEF => error "No goal present";

fun print () = Toplevel.print_state false (state ());


(* history navigation *)

local

fun find_and_undo _ [] = error "Undo history exhausted"
  | find_and_undo which ((prev, tr) :: hist) =
      ((case Toplevel.init_of tr of SOME name => ThyInfo.kill_thy name | NONE => ());
        if which (Toplevel.name_of tr) then (prev, hist) else find_and_undo which hist);

in

fun linear_undo n = edit_history n (K (find_and_undo (K true)));

fun undo n = edit_history n (fn st => fn hist =>
  find_and_undo (if Toplevel.is_proof st then K true else OuterKeyword.is_theory) hist);

fun kill () = edit_history 1 (fn st => fn hist =>
  find_and_undo
    (if Toplevel.is_proof st then OuterKeyword.is_theory else OuterKeyword.is_theory_begin) hist);

fun kill_proof () = edit_history 1 (fn st => fn hist =>
  if Toplevel.is_proof st then find_and_undo OuterKeyword.is_theory hist
  else raise Toplevel.UNDEF);

end;


(* interactive state transformations *)

fun op >> tr =
  (case Toplevel.transition true tr (state ()) of
    NONE => false
  | SOME (_, SOME err) => (set_exn (SOME err); Toplevel.error_msg tr err; true)
  | SOME (st', NONE) =>
      let
        val name = Toplevel.name_of tr;
        val _ = if OuterKeyword.is_theory_begin name then init () else ();
        val _ =
          if OuterKeyword.is_regular name
          then edit_history 1 (fn st => fn hist => (st', (st, tr) :: hist)) else ();
      in true end);

fun op >>> [] = ()
  | op >>> (tr :: trs) = if op >> tr then op >>> trs else ();


(* toplevel loop *)

val crashes = ref ([]: exn list);

local

fun raw_loop secure src =
  let
    fun check_secure () =
      (if secure then warning "Secure loop -- cannot exit to ML" else (); secure);
  in
    (case Source.get_single (Source.set_prompt Source.default_prompt src) of
      NONE => if secure then quit () else ()
    | SOME (tr, src') => if op >> tr orelse check_secure () then raw_loop secure src' else ())
    handle exn =>
      (Output.error_msg (Toplevel.exn_message exn)
        handle crash =>
          (CRITICAL (fn () => change crashes (cons crash));
            warning "Recovering from Isar toplevel crash -- see also Isar.crashes");
          raw_loop secure src)
  end;

in

fun toplevel_loop {init = do_init, welcome, sync, secure} =
 (Context.set_thread_data NONE;
  if do_init then init () else ();  (* FIXME init editor model *)
  if welcome then writeln (Session.welcome ()) else ();
  uninterruptible (fn _ => fn () => raw_loop secure (OuterSyntax.isar sync)) ());

end;

fun loop () =
  toplevel_loop {init = false, welcome = false, sync = false, secure = Secure.is_secure ()};

fun main () =
  toplevel_loop {init = true, welcome = true, sync = false, secure = Secure.is_secure ()};



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
  | status_markup Running = (Markup.runningN, [])
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



(** command syntax **)

local

structure P = OuterParse and K = OuterKeyword;
val op >> = Scan.>>;

in

(* global history *)

val _ =
  OuterSyntax.improper_command "init_toplevel" "init toplevel point-of-interest" K.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative init));

val _ =
  OuterSyntax.improper_command "linear_undo" "undo commands" K.control
    (Scan.optional P.nat 1 >>
      (fn n => Toplevel.no_timing o Toplevel.imperative (fn () => linear_undo n)));

val _ =
  OuterSyntax.improper_command "undo" "undo commands (skipping closed proofs)" K.control
    (Scan.optional P.nat 1 >>
      (fn n => Toplevel.no_timing o Toplevel.imperative (fn () => undo n)));

val _ =
  OuterSyntax.improper_command "undos_proof" "undo commands (skipping closed proofs)" K.control
    (Scan.optional P.nat 1 >> (fn n => Toplevel.no_timing o
      Toplevel.keep (fn state =>
        if Toplevel.is_proof state then (undo n; print ()) else raise Toplevel.UNDEF)));

val _ =
  OuterSyntax.improper_command "cannot_undo" "partial undo -- Proof General legacy" K.control
    (P.name >>
      (fn "end" => Toplevel.no_timing o Toplevel.imperative (fn () => undo 1)
        | txt => Toplevel.imperative (fn () => error ("Cannot undo " ^ quote txt))));

val _ =
  OuterSyntax.improper_command "kill" "kill partial proof or theory development" K.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative kill));


(* editor model *)

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

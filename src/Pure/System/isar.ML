(*  Title:      Pure/System/isar.ML
    Author:     Makarius

Global state of the raw Isar read-eval-print loop.
*)

signature ISAR =
sig
  val init: unit -> unit
  val exn: unit -> (exn * string) option
  val state: unit -> Toplevel.state
  val goal: unit -> {context: Proof.context, facts: thm list, goal: thm}
  val print: unit -> unit
  val >> : Toplevel.transition -> bool
  val >>> : Toplevel.transition list -> unit
  val linear_undo: int -> unit
  val undo: int -> unit
  val kill: unit -> unit
  val kill_proof: unit -> unit
  val crashes: exn list Synchronized.var
  val toplevel_loop: TextIO.instream ->
    {init: bool, welcome: bool, sync: bool, secure: bool} -> unit
  val loop: unit -> unit
  val main: unit -> unit
end;

structure Isar: ISAR =
struct


(** TTY model -- SINGLE-THREADED! **)

(* the global state *)

type history = (Toplevel.state * Toplevel.transition) list;
  (*previous state, state transition -- regular commands only*)

local
  val global_history = Unsynchronized.ref ([]: history);
  val global_state = Unsynchronized.ref Toplevel.toplevel;
  val global_exn = Unsynchronized.ref (NONE: (exn * string) option);
in

fun edit_history count f = NAMED_CRITICAL "Isar" (fn () =>
  let
    fun edit 0 (st, hist) = (global_history := hist; global_state := st; global_exn := NONE)
      | edit n (st, hist) = edit (n - 1) (f st hist);
  in edit count (! global_state, ! global_history) end);

fun state () = ! global_state;

fun exn () = ! global_exn;
fun set_exn exn =  global_exn := exn;

end;


fun init () = edit_history 1 (K (K (Toplevel.toplevel, [])));

fun goal () = Proof.goal (Toplevel.proof_of (state ()))
  handle Toplevel.UNDEF => error "No goal present";

fun print () = Toplevel.print_state false (state ());


(* history navigation *)

local

fun find_and_undo _ [] = error "Undo history exhausted"
  | find_and_undo which ((prev, tr) :: hist) =
      if which (Toplevel.name_of tr) then (prev, hist) else find_and_undo which hist;

in

fun linear_undo n = edit_history n (K (find_and_undo (K true)));

fun undo n = edit_history n (fn st => fn hist =>
  find_and_undo (if Toplevel.is_proof st then K true else Keyword.is_theory) hist);

fun kill () = edit_history 1 (fn st => fn hist =>
  find_and_undo
    (if Toplevel.is_proof st then Keyword.is_theory else Keyword.is_theory_begin) hist);

fun kill_proof () = edit_history 1 (fn st => fn hist =>
  if Toplevel.is_proof st then find_and_undo Keyword.is_theory hist
  else raise Toplevel.UNDEF);

end;


(* interactive state transformations *)

fun op >> tr =
  (case Toplevel.transition true tr (state ()) of
    NONE => false
  | SOME (_, SOME exn_info) =>
     (set_exn (SOME exn_info);
      Toplevel.error_msg tr (serial (), ML_Compiler.exn_message (Runtime.EXCURSION_FAIL exn_info));
      true)
  | SOME (st', NONE) =>
      let
        val name = Toplevel.name_of tr;
        val _ = if Keyword.is_theory_begin name then init () else ();
        val _ =
          if Keyword.is_regular name
          then edit_history 1 (fn st => fn hist => (st', (st, tr) :: hist)) else ();
      in true end);

fun op >>> [] = ()
  | op >>> (tr :: trs) = if op >> tr then op >>> trs else ();


(* toplevel loop -- uninterruptible *)

val crashes = Synchronized.var "Isar.crashes" ([]: exn list);

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
      (Output.error_msg (ML_Compiler.exn_message exn)
        handle crash =>
          (Synchronized.change crashes (cons crash);
            warning "Recovering from Isar toplevel crash -- see also Isar.crashes");
        raw_loop secure src)
  end;

in

fun toplevel_loop in_stream {init = do_init, welcome, sync, secure} =
 (Context.set_thread_data NONE;
  if do_init then (Options.load_default (); init ()) else ();
  if welcome then writeln (Session.welcome ()) else ();
  uninterruptible (fn _ => fn () => raw_loop secure (Outer_Syntax.isar in_stream sync)) ());

end;

fun loop () =
  toplevel_loop TextIO.stdIn
    {init = false, welcome = false, sync = false, secure = Secure.is_secure ()};

fun main () =
  toplevel_loop TextIO.stdIn
    {init = true, welcome = true, sync = false, secure = Secure.is_secure ()};

end;

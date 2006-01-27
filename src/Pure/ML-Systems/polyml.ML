(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (version 4.0, 4.1, 4.1.x).
*)

(** ML system and platform related **)

(* String compatibility *)

structure String =
struct
  fun isSuffix s1 s2 =
    let val n1 = size s1 and n2 = size s2
    in if n1 = n2 then s1 = s2 else n1 <= n2 andalso String.substring (s2, n2 - n1, n1) = s1 end;
  open String;
end;

structure Substring =
struct
  open Substring;
  val full = all;
end;


(* cygwin *)

val cygwin_platform = String.isSuffix "cygwin" ml_platform;
fun if_cygwin f x = if cygwin_platform then f x else ();
fun unless_cygwin f x = if not cygwin_platform then f x else ();


(*low-level pointer equality*)
val pointer_eq = Address.wordEq;


(* old Poly/ML emulation *)

local
  val orig_exit = exit;
in
  open PolyML;
  val exit = orig_exit;
  fun quit () = exit 0;
end;


(* restore old-style character / string functions *)

val ord = SML90.ord;
val chr = SML90.chr;
val explode = SML90.explode;
val implode = SML90.implode;


(* compiler-independent timing functions *)

use "ML-Systems/cpu-timer-basis.ML";


(* bounded time execution *)

(* FIXME proper implementation available? *)
fun interrupt_timeout time f x =
  f x;

(*
unless_cygwin
  use "ML-Systems/polyml-interrupt-timeout.ML";
*)


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp _ pprint (str, blk, brk, en) _ _ obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);


(* ML command execution -- 'eval' *)

local

fun drop_last [] = []
  | drop_last [x] = []
  | drop_last (x :: xs) = x :: drop_last xs;

in

fun use_text (print, err) verbose txt =
  let
    val in_buffer = ref (explode txt);
    val out_buffer = ref ([]: string list);
    fun output () = implode (drop_last (rev (! out_buffer)));

    fun get () =
      (case ! in_buffer of
        [] => ""
      | c :: cs => (in_buffer := cs; c));
    fun put s = out_buffer := s :: ! out_buffer;

    fun exec () =
      (case ! in_buffer of
        [] => ()
      | _ => (PolyML.compiler (get, put) (); exec ()));
  in
    exec () handle exn => (err (output ()); raise exn);
    if verbose then print (output ()) else ()
  end;

end;


(*eval command line arguments*)
local
  fun println s =
    (TextIO.output (TextIO.stdOut, s ^ "\n"); TextIO.flushOut TextIO.stdOut);
  val eval = use_text (println, println) true;
in
  val _ = PolyML.onEntry (fn () => app eval (CommandLine.arguments ()));
end;



(** interrupts **)

exception Interrupt = SML90.Interrupt;

local

fun capture f x = ((f x): unit; NONE) handle exn => SOME exn;

fun release NONE = ()
  | release (SOME exn) = raise exn;

val sig_int = 2;

fun change_signal new_handler f x =
  let
    (*RACE wrt. other signals*)
    val old_handler = Signal.signal (sig_int, new_handler);
    val result = capture f x;
    val _ = Signal.signal (sig_int, old_handler);
  in release result end;

val default_handler = Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ());

in

val _ = Signal.signal (sig_int, default_handler);

fun ignore_interrupt f = change_signal Signal.SIG_IGN f;
fun raise_interrupt f = change_signal default_handler f;

end;



(** OS related **)

unless_cygwin
  use "ML-Systems/polyml-posix.ML";


(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout; could be done more easily by Unix.execute,
  but that function doesn't use the PATH*)
fun execute command =
  let
    val tmp_name = OS.FileSys.tmpName ();
    val is = (OS.Process.system (command ^ " > " ^ tmp_name); TextIO.openIn tmp_name);
    val result = TextIO.inputAll is;
  in
    TextIO.closeIn is;
    OS.FileSys.remove tmp_name;
    result
  end;

(*plain version; with return code*)
fun system cmd =
  if OS.Process.isSuccess (OS.Process.system cmd) then 0 else 1;


(*Convert a process ID to a decimal string (chiefly for tracing)*)
fun string_of_pid pid = 
    Word.fmt StringCvt.DEC (Word.fromLargeWord (Posix.Process.pidToWord pid));


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);


(* profile execution *)

local

fun no_profile () =
  RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;

in

fun profile 0 f x = f x
  | profile n f x =
     (RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
      let val y = f x handle exn => (no_profile (); raise exn)
      in no_profile (); y end);

end;

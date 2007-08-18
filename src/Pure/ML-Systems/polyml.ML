(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$

Compatibility file for Poly/ML (version 4.1.x and 4.2.0).
*)

use "ML-Systems/exn.ML";
use "ML-Systems/multithreading_dummy.ML";


(** ML system and platform related **)

(* String compatibility *)

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

fun start_timing () =
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

fun end_timing (CPUtimer, {sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  All "^ toString (sys2-sys + usr2-usr) ^
      " secs"
      handle Time => ""
  end;

fun check_timer timer =
  let
    val {sys, usr} = Timer.checkCPUTimer timer;
    val gc = Timer.checkGCTime timer;    (* FIXME already included in usr? *)
  in (sys, usr, gc) end;


(* bounded time execution *)

(*dummy implementation*)
fun interrupt_timeout time f x =
  f x;


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* toplevel pretty printing (see also Pure/pure_setup.ML) *)

fun make_pp _ pprint (str, blk, brk, en) _ _ obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);

(*print depth*)
local
  val depth = ref 10;
in
  fun get_print_depth () = ! depth;
  fun print_depth n = (depth := n; PolyML.print_depth n);
end;


(* ML command execution -- 'eval' *)

fun use_text name (print, err) verbose txt =
  let
    val in_buffer = ref (explode txt);
    val out_buffer = ref ([]: string list);
    fun output () = implode (rev (case ! out_buffer of "\n" :: cs => cs | cs => cs));

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
    exec () handle exn =>
      (err ((if name = "" then "" else "Error in " ^ name ^ "\n") ^ output ()); raise exn);
    if verbose then print (output ()) else ()
  end;

fun use_file _ _ name = use name;


(*eval command line arguments*)
local
  fun println s =
    (TextIO.output (TextIO.stdOut, s ^ "\n"); TextIO.flushOut TextIO.stdOut);
  fun eval "-q" = ()
    | eval txt = use_text "" (println, println) false txt;
in
  val _ = PolyML.onEntry (fn () =>
   (Signal.signal (2, Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ()));
    app eval (CommandLine.arguments ())));
end;



(** interrupts **)

exception Interrupt = SML90.Interrupt;

local

val sig_int = 2;

fun change_signal new_handler f x =
  let
    (*RACE wrt. other signals*)
    val old_handler = Signal.signal (sig_int, new_handler);
    val result = Exn.capture f x;
    val _ = Signal.signal (sig_int, old_handler);
  in Exn.release result end;

val default_handler = Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ());

in

val _ = Signal.signal (sig_int, default_handler);

fun ignore_interrupt f = change_signal Signal.SIG_IGN f;
fun raise_interrupt f = change_signal default_handler f;

end;



(** OS related **)

use "ML-Systems/polyml-posix.ML";


(* current directory *)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;


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

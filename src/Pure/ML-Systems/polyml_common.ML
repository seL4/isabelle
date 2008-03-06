(*  Title:      Pure/ML-Systems/polyml_common.ML
    ID:         $Id$

Compatibility file for Poly/ML -- common part for 4.x and 5.x.
*)

use "ML-Systems/exn.ML";
if List.exists (fn s => s = "Universal") (PolyML.Compiler.structureNames ()) then ()
else use "ML-Systems/universal.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/time_limit.ML";


(** ML system and platform related **)

(* Compiler options *)

val ml_system_fix_ints = false;

PolyML.Compiler.printInAlphabeticalOrder := false;
PolyML.Compiler.maxInlineSize := 80;


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

fun use_text (tune: string -> string) name (print, err) verbose txt =
  let
    val in_buffer = ref (explode (tune txt));
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

fun use_file tune output verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = TextIO.inputAll instream before TextIO.closeIn instream;
  in use_text tune name output verbose txt end;


(*eval command line arguments*)
local
  fun println s =
    (TextIO.output (TextIO.stdOut, s ^ "\n"); TextIO.flushOut TextIO.stdOut);
  fun eval "-q" = ()
    | eval txt = use_text (fn x => x) "" (println, println) false txt;
in
  val _ = PolyML.onEntry (fn () =>
   (Signal.signal (2, Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ()));
    app eval (CommandLine.arguments ())));
end;



(** interrupts **)

exception Interrupt = SML90.Interrupt;

local

val sig_int = 2;
val default_handler = Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ());

val _ = Signal.signal (sig_int, default_handler);

fun change_signal new_handler f x =
  let
    (*RACE wrt. other signals!*)
    val old_handler = Signal.signal (sig_int, new_handler);
    val result = Exn.capture (f old_handler) x;
    val _ = Signal.signal (sig_int, old_handler);
  in Exn.release result end;

in

fun interruptible f = change_signal default_handler (fn _ => f);

fun uninterruptible f =
  change_signal Signal.SIG_IGN
    (fn old_handler => f (fn g => change_signal old_handler (fn _ => g)));

end;



(** OS related **)

(* Posix patches *)

(*This extension of the Poly/ML Signal structure is only necessary
  because in SML/NJ, types Posix.Signal.signal and Signals.signal differ.*)
structure IsaSignal =
struct
  open Signal
  val usr1 = Posix.Signal.usr1
  val usr2 = Posix.Signal.usr2
  val alrm = Posix.Signal.alrm
  val chld = Posix.Signal.chld
  val cont = Posix.Signal.cont
  val int  = Posix.Signal.int
  val quit = Posix.Signal.quit
end;


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

fun profile 0 f x = f x
  | profile n f x =
      let
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
        val res = Exn.capture f x;
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;
      in Exn.release res end;


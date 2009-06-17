(*  Title:      Pure/ML-Systems/polyml_common.ML

Compatibility file for Poly/ML -- common part for 5.x.
*)

exception Interrupt = SML90.Interrupt;

use "ML-Systems/exn.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/time_limit.ML";
use "ML-Systems/timing.ML";
use "ML-Systems/system_shell.ML";
use "ML-Systems/ml_pretty.ML";
use "ML-Systems/use_context.ML";


(** ML system and platform related **)

val forget_structure = PolyML.Compiler.forgetStructure;

val _ = PolyML.Compiler.forgetValue "print";


(* Compiler options *)

val ml_system_fix_ints = false;

PolyML.Compiler.printInAlphabeticalOrder := false;
PolyML.Compiler.maxInlineSize := 80;


(* old Poly/ML emulation *)

fun quit () = exit 0;


(* restore old-style character / string functions *)

val ord = SML90.ord;
val chr = SML90.chr;
val explode = SML90.explode;
val implode = SML90.implode;


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* print depth *)

local
  val depth = ref 10;
in
  fun get_print_depth () = ! depth;
  fun print_depth n = (depth := n; PolyML.print_depth n);
end;

val error_depth = PolyML.error_depth;



(** interrupts **)

local

val sig_int = 2;
val default_handler = Signal.SIG_HANDLE (fn _ => Process.interruptConsoleProcesses ());

val _ = Signal.signal (sig_int, default_handler);
val _ = PolyML.onEntry (fn () => (Signal.signal (sig_int, default_handler); ()));

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

(* current directory *)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;

fun process_id () =
  Word.fmt StringCvt.DEC (Word.fromLargeWord (Posix.Process.pidToWord (Posix.ProcEnv.getpid ())));


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);



(** Runtime system **)

val exception_trace = PolyML.exception_trace;
val timing = PolyML.timing;
val profiling = PolyML.profiling;

fun profile 0 f x = f x
  | profile n f x =
      let
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
        val res = Exn.capture f x;
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;
      in Exn.release res end;


(*  Title:      Pure/ML-Systems/mlworks.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Compatibility file for MLWorks version 1.0r2 or later.
*)

(** ML system related **)

(* restore old-style character / string functions *)

val ord = SML90.ord;
val chr = SML90.chr;
val explode = SML90.explode;
val implode = SML90.implode;


(* MLWorks parameters *)

val _ =
 (MLWorks.Internal.Runtime.Event.stack_overflow_handler 
  (fn () =>
    let val max_stack = MLWorks.Internal.Runtime.Memory.max_stack_blocks
    in max_stack := (!max_stack * 3) div 2 + 5;
       print ("#### Increasing stack to " ^ Int.toString (64 * !max_stack) ^
              "KB\n")
    end);
  MLWorks.Internal.Runtime.Memory.gc_message_level := 10;
  (*Is this of any use at all?*)
  Shell.Options.set (Shell.Options.ValuePrinter.showExnDetails, true));


(* Poly/ML emulation *)

(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;
fun quit () = exit 0;

(*limit the printing depth*)
fun print_depth n = 
    let open Shell.Options
    in set (ValuePrinter.maximumDepth, n div 2);
       set (ValuePrinter.maximumSeqSize, n)
    end;

(*interface for toplevel pretty printers, see also Pure/install_pp.ML*)
(*n.a.*)
fun make_pp path pprint = ();
fun install_pp _ = ();

(*prompts*)
(*n.a.??*)
fun ml_prompts p1 p2 = ();


(** Compiler-independent timing functions **)

use "ML-Systems/cpu-timer-gc.ML"

(* bounded time execution *)

(* FIXME proper implementation available? *)

structure TimeLimit : sig
   exception TimeOut
   val timeLimit : Time.time -> ('a -> 'b) -> 'a -> 'b
end = struct
   exception TimeOut
   fun timeLimit t f x =
      f x;
end;

(* ML command execution *)

(*Can one redirect 'use' directly to an instream?*)
fun use_text _ _ txt =
  let
    val tmp_name = OS.FileSys.tmpName ();
    val tmp_file = TextIO.openOut tmp_name;
  in
    TextIO.output (tmp_file, txt);
    TextIO.closeOut tmp_file;
    use tmp_name;
    OS.FileSys.remove tmp_name
  end;



(** interrupts **)      (*Note: may get into race conditions*)

exception Interrupt;

MLWorks.Internal.Runtime.Event.interrupt_handler (fn () => raise Interrupt);

fun ignore_interrupt f x = f x;
fun raise_interrupt f x = f x;



(** OS related **)

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
  if OS.Process.system cmd = OS.Process.success then 0 else 1;


(* file handling *)

(*get time of last modification*)
fun file_info name = Time.toString (OS.FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

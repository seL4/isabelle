(*  Title:      Pure/ML-Systems/smlnj.ML

Compatibility file for Standard ML of New Jersey 110 or later.
*)

exception Interrupt;

use "ML-Systems/proper_int.ML";
use "ML-Systems/overloading_smlnj.ML";
use "ML-Systems/exn.ML";
use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/system_shell.ML";
use "ML-Systems/ml_name_space.ML";
use "ML-Systems/ml_pretty.ML";


(*low-level pointer equality*)

CM.autoload "$smlnj/init/init.cmi";
val pointer_eq = InlineT.ptreql;


(* restore old-style character / string functions *)

val ord     = mk_int o SML90.ord;
val chr     = SML90.chr o dest_int;
val explode = SML90.explode;
val implode = SML90.implode;


(* New Jersey ML parameters *)

val _ =
 (Control.Print.printLength := 1000;
  Control.Print.printDepth := 350;
  Control.Print.stringDepth := 250;
  Control.Print.signatures := 2;
  Control.MC.matchRedundantError := false);


(* Poly/ML emulation *)

val exit = exit o dest_int;
fun quit () = exit 0;

(*limit the printing depth -- divided by 2 for comparibility with Poly/ML*)
local
  val depth = ref (10: int);
in
  fun get_print_depth () = ! depth;
  fun print_depth n =
   (depth := n;
    Control.Print.printDepth := dest_int n div 2;
    Control.Print.printLength := dest_int n);
end;


(* compiler-independent timing functions *)

fun start_timing () =
  let
    val timer = Timer.startCPUTimer ();
    val time = Timer.checkCPUTimer timer;
  in (timer, time) end;

fun end_timing (timer, {sys, usr}) =
  let
    open Time;  (*...for Time.toString, Time.+ and Time.- *)
    val {sys = sys2, usr = usr2} = Timer.checkCPUTimer timer;
    val user = usr2 - usr;
    val all = user + sys2 - sys;
    val message = "User " ^ toString user ^ "  All "^ toString all ^ " secs" handle Time => "";
  in {message = message, user = user, all = all} end;

fun check_timer timer =
  let
    val {sys, usr} = Timer.checkCPUTimer timer;
    val gc = Timer.checkGCTime timer;    (* FIXME already included in usr? *)
  in (sys, usr, gc) end;


(*prompts*)
fun ml_prompts p1 p2 =
  (Control.primaryPrompt := p1; Control.secondaryPrompt := p2);

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();

(*dummy implementation*)
fun print x = x;

(*dummy implementation*)
fun makestring x = "dummy string for SML New Jersey";


(* toplevel pretty printing (see also Pure/pure_setup.ML) *)

fun make_pp path pprint =
  let
    open PrettyPrint;

    fun pp pps obj =
      pprint obj
        (string pps, openHOVBox pps o Rel o dest_int,
          fn wd => break pps {nsp=dest_int wd, offset=0}, fn () => newline pps,
          fn () => closeBox pps);
  in (path, pp) end;

fun install_pp (path, pp) = CompilerPPTable.install_pp path pp;


(* ML command execution *)

fun use_text (tune: string -> string) _ _ (line: int, name) (print, err) verbose txt =
  let
    val ref out_orig = Control.Print.out;

    val out_buffer = ref ([]: string list);
    val out = {say = (fn s => out_buffer := s :: ! out_buffer), flush = (fn () => ())};
    fun output () =
      let val str = implode (rev (! out_buffer))
      in String.substring (str, 0, Int.max (0, size str - 1)) end;
  in
    Control.Print.out := out;
    Backend.Interact.useStream (TextIO.openString (tune txt)) handle exn =>
      (Control.Print.out := out_orig;
        err ((if name = "" then "" else "Error in " ^ name ^ "\n") ^ output ()); raise exn);
    Control.Print.out := out_orig;
    if verbose then print (output ()) else ()
  end;

fun use_file tune str_of_pos name_space output verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text tune str_of_pos name_space (1, name) output verbose txt end;

fun forget_structure name =
  use_text (fn x => x) (fn _ => "") () (1, "ML") (TextIO.print, fn s => raise Fail s) false
    ("structure " ^ name ^ " = struct end");



(** interrupts **)

local

fun change_signal new_handler f x =
  let
    val old_handler = Signals.setHandler (Signals.sigINT, new_handler);
    val result = Exn.capture (f old_handler) x;
    val _ = Signals.setHandler (Signals.sigINT, old_handler);
  in Exn.release result end;

in

fun interruptible (f: 'a -> 'b) x =
  let
    val result = ref (Exn.Exn Interrupt: 'b Exn.result);
    val old_handler = Signals.inqHandler Signals.sigINT;
  in
    SMLofNJ.Cont.callcc (fn cont =>
      (Signals.setHandler (Signals.sigINT, Signals.HANDLER (fn _ => cont));
        result := Exn.capture f x));
    Signals.setHandler (Signals.sigINT, old_handler);
    Exn.release (! result)
  end;

fun uninterruptible f =
  change_signal Signals.IGNORE
    (fn old_handler => f (fn g => change_signal old_handler (fn _ => g)));

end;


(* basis library fixes *)

structure TextIO =
struct
  open TextIO;
  fun inputLine is = TextIO.inputLine is
    handle IO.Io _ => raise Interrupt;
end;



(** OS related **)

(* current directory *)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;


(* system command execution *)

val system_out = (fn (output, rc) => (output, mk_int rc)) o system_out;


(*Convert a process ID to a decimal string (chiefly for tracing)*)
fun process_id pid =
  Word.fmt StringCvt.DEC (Word.fromLargeWord (Posix.Process.pidToWord (Posix.ProcEnv.getpid ())));


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

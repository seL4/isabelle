(*  Title:      Pure/ML-Systems/smlnj.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel, TU Muenchen

Compatibility file for Standard ML of New Jersey 110 or later.
*)

(case #version_id (Compiler.version) of
  [110, x] => if x >= 35 then use "ML-Systems/smlnj-compiler.ML" else ()
| _ => ());


(** ML system related **)

(*low-level pointer equality*)

(*dummy version -- may get overridden in smlnj-ptreql.ML*)
fun pointer_eq (x:'a, y) = false;

(case #version_id (Compiler.version) of
  [110, x] => if x >= 49 then use "ML-Systems/smlnj-ptreql.ML" else ()
| _ => ());


(* restore old-style character / string functions *)

val ord     = SML90.ord;
val chr     = SML90.chr;
val explode = SML90.explode;
val implode = SML90.implode;


(* New Jersey ML parameters *)

val _ =
 (Compiler.Control.Print.printLength := 1000;
  Compiler.Control.Print.printDepth := 350;
  Compiler.Control.Print.stringDepth := 250;
  Compiler.Control.Print.signatures := 2;
  Compiler.Control.MC.matchRedundantError := false);


(* Poly/ML emulation *)

fun quit () = exit 0;

(*limit the printing depth -- divided by 2 for comparibility with Poly/ML*)
fun print_depth n =
 (Compiler.Control.Print.printDepth := n div 2;
  Compiler.Control.Print.printLength := n);


(* compiler-independent timing functions *)

(case #version_id (Compiler.version) of
  [110, x] => if x >= 44
              then use "ML-Systems/cpu-timer-basis.ML"
              else use "ML-Systems/cpu-timer-gc.ML"
| _ => use "ML-Systems/cpu-timer-gc.ML");


(*prompts*)
fun ml_prompts p1 p2 =
  (Compiler.Control.primaryPrompt := p1; Compiler.Control.secondaryPrompt := p2);

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

(case #version_id (Compiler.version) of
  [110, x] => if x >= 44
              then use "ML-Systems/smlnj-pp-new.ML"
              else use "ML-Systems/smlnj-pp-old.ML"
| _ => use "ML-Systems/smlnj-pp-old.ML");

fun install_pp (path, pp) = Compiler.PPTable.install_pp path pp;


(* ML command execution *)

fun use_text (print, err) verbose txt =
  let
    val ref out_orig = Compiler.Control.Print.out;

    val out_buffer = ref ([]: string list);
    val out = {say = (fn s => out_buffer := s :: ! out_buffer), flush = (fn () => ())};
    fun output () =
      let val str = implode (rev (! out_buffer))
      in String.substring (str, 0, Int.max (0, size str - 1)) end;
  in
    Compiler.Control.Print.out := out;
    Compiler.Interact.useStream (TextIO.openString txt) handle exn =>
      (Compiler.Control.Print.out := out_orig; err (output ()); raise exn);
    Compiler.Control.Print.out := out_orig;
    if verbose then print (output ()) else ()
  end;



(** interrupts **)

exception Interrupt;

local

fun capture f x = ((f x): unit; NONE) handle exn => SOME exn;

fun release NONE = ()
  | release (SOME exn) = raise exn;

in

fun ignore_interrupt f x =
  let
    val old_handler = Signals.setHandler (Signals.sigINT, Signals.IGNORE);
    val result = capture f x;
    val _ = Signals.setHandler (Signals.sigINT, old_handler);
  in release result end;

fun raise_interrupt f x =
  let
    val interrupted = ref false;
    val result = ref NONE;
    val old_handler = Signals.inqHandler Signals.sigINT;
  in
    SMLofNJ.Cont.callcc (fn cont =>
      (Signals.setHandler (Signals.sigINT, Signals.HANDLER (fn _ => (interrupted := true; cont)));
      result := capture f x));
    Signals.setHandler (Signals.sigINT, old_handler);
    if ! interrupted then raise Interrupt else release (! result)
  end;

end;

(case #version_id (Compiler.version) of
  [110, x] => if x >= 44
              then use "ML-Systems/smlnj-basis-compat.ML"
              else ()
| _ => ());


(** Signal handling: emulation of the Poly/ML Signal structure. Note that types
    Posix.Signal.signal and Signals.signal differ **)

structure IsaSignal =
struct

datatype sig_handle = SIG_DFL | SIG_IGN | SIG_HANDLE of Signals.signal -> unit;

(*From the SML/NJ documentation: "HANDLER(f) installs a handler for a
  signal. When signal is delivered to the process, the execution state
  of the current thread will be bundled up as a continuation k, then
  f(signal,n,k) will be called. The number n is the number of times
  signal has been signalled since the last time f was invoked for it."*)

fun toAction SIG_DFL = Signals.DEFAULT
  | toAction SIG_IGN = Signals.IGNORE
  | toAction (SIG_HANDLE iu) =
      Signals.HANDLER (fn (signo,_,cont) => (iu signo; cont));

(*The types are correct, but I'm not sure about the semantics!*)
fun fromAction Signals.DEFAULT = SIG_DFL
  | fromAction Signals.IGNORE = SIG_IGN
  | fromAction (Signals.HANDLER f) =
      SIG_HANDLE (fn signo => SMLofNJ.Cont.callcc (fn k => (f (signo,0,k); ())));

(*Poly/ML version has type  int * sig_handle -> sig_handle*)
fun signal (signo, sh) = fromAction (Signals.setHandler (signo, toAction sh));

val usr1 = UnixSignals.sigUSR1
val usr2 = UnixSignals.sigUSR2
val alrm = UnixSignals.sigALRM
val chld = UnixSignals.sigCHLD
val cont = UnixSignals.sigCONT
val int = UnixSignals.sigINT
val quit = UnixSignals.sigQUIT
val term = UnixSignals.sigTERM

end;


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
val system = OS.Process.system: string -> int;


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

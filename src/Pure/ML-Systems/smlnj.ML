(*  Title:      Pure/ML-Systems/smlnj.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Compatibility file for Standard ML of New Jersey 110 or later.
*)

(case #version_id (Compiler.version) of
  [110, x] => if x >= 35 then use "ML-Systems/smlnj-compiler.ML" else ()
| _ => ());

(** ML system related **)

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


(* prompts *)

fun ml_prompts p1 p2 =
  (Compiler.Control.primaryPrompt := p1; Compiler.Control.secondaryPrompt := p2);


(case #version_id (Compiler.version) of
  [110, x] => if x >= 44
	      then use "ML-Systems/smlnj-basis-compat.ML"
	      else ()
| _ => ());

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


(* file handling *)

(*get time of last modification*)
fun file_info name = Time.toString (OS.FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

(*  Title:      Pure/ML-Systems/smlnj-1.09.ML
    ID:         $Id$
    Author:     Carsten Clasohm, TU Muenchen
    Copyright   1996  TU Muenchen

Compatibility file for Standard ML of New Jersey version 1.09.27 or later.
*)

(** ML system related **)

(* restore old-style character / string functions *)

fun ord s = Char.ord (String.sub (s, 0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(* New Jersey ML parameters *)

val _ =
 (Compiler.Control.Print.printLength := 1000;
  Compiler.Control.Print.printDepth := 350;
  Compiler.Control.Print.stringDepth := 250;
  Compiler.Control.Print.signatures := 2);


(* Poly/ML emulation *)

fun quit () = exit 0;

(*limit the printing depth -- divided by 2 for comparibility with Poly/ML*)
fun print_depth n =
 (Compiler.Control.Print.printDepth := n div 2;
  Compiler.Control.Print.printLength := n);

(*Poly/ML-like prompts*)
Compiler.Control.primaryPrompt := "> ";
Compiler.Control.secondaryPrompt := "# ";


(* timing *)

(*a conditional timing function: applies f to () and, if the flag is true,
  prints its runtime*)
fun cond_timeit flag f =
  if flag then
    let open Time  (*...for Time.toString, Time.+ and Time.- *)
	val CPUtimer = Timer.startCPUTimer();
        val {gc=gct1,sys=syst1,usr=usrt1} = Timer.checkCPUTimer(CPUtimer);
        val result = f();
        val {gc=gct2,sys=syst2,usr=usrt2} = Timer.checkCPUTimer(CPUtimer)
    in  print("User " ^ toString (usrt2-usrt1) ^
              "  GC " ^ toString (gct2-gct1) ^
              "  All "^ toString (syst2-syst1 + usrt2-usrt1 + gct2-gct1) ^
              " secs\n")
	  handle Time => ();
        result
    end
  else f ();


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp path pprint =
  let
    open Compiler.PrettyPrint;

    fun pp pps obj =
      pprint obj
        (add_string pps, begin_block pps INCONSISTENT,
          fn wd => add_break pps (wd, 0), fn () => add_newline pps,
          fn () => end_block pps);
  in
    (path, pp)
  end;

fun install_pp (path, pp) = Compiler.PPTable.install_pp path pp;


(* ML command execution *)

val use_string = Compiler.Interact.useStream o TextIO.openString o implode;



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


(* file handling *)

(*get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""		(* FIXME !? *)
  | file_info name = Time.toString (OS.FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);


(* non-ASCII input (see also Thy/symbol_input.ML) *)

val needs_filtered_use = false;

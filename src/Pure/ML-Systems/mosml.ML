(*  Title:      Pure/ML-Systems/mosml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Compatibility file for Moscow ML 2.00

NOTE: saving images does not work (yet!?), may run it interactively as follows:

$ cd .../Pure
$ isabelle RAW_ML_SYSTEM
> val ml_system = "mosml";
> use "ML-Systems/mosml.ML";
> use "ROOT.ML";
*)

(** ML system related **)


(* Poly/ML emulation *)

load "Bool";
load "Int";
load "Real";
load "ListPair";

load "OS";
load "Process";
load "FileSys";

structure OS =
  struct
  open OS
  structure Process = Process
  structure FileSys = FileSys
  end;
 
(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = Process.exit Process.success
  | exit _ = Process.exit Process.failure;

(*limit the printing depth*)
fun print_depth n =
 (Meta.printDepth := n div 2;
  Meta.printLength := n);

(*interface for toplevel pretty printers, see also Pure/install_pp.ML*)
(*the documentation refers to an installPP but I couldn't fine it!*)
fun make_pp path pprint = ();
fun install_pp _ = ();

(*prompts*)
(*n.a.??*)
fun ml_prompts p1 p2 = ();


(** Compiler-independent timing functions **)

load "Timer";

use "ML-Systems/cpu-timer-gc.ML";


(* ML command execution *)

(*Can one redirect 'use' directly to an instream?*)
fun use_text _ _ txt =
  let
    val tmp_name = FileSys.tmpName ();
    val tmp_file = TextIO.openOut tmp_name;
  in
    TextIO.output (tmp_file, txt);
    TextIO.closeOut tmp_file;
    use tmp_name;
    FileSys.remove tmp_name
  end;



(** interrupts **)	(*Note: may get into race conditions*)

(* FIXME proper implementation available? *)

exception Interrupt;

fun ignore_interrupt f x = f x;           
fun raise_interrupt f x = f x;



(** OS related **)

(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout; could be done more easily by Unix.execute,
  but that function doesn't use the PATH*)
fun execute command =
  let
    val tmp_name = FileSys.tmpName ();
    val is = (Process.system (command ^ " > " ^ tmp_name); TextIO.openIn 
tmp_name);
    val result = TextIO.inputAll is;
  in
    TextIO.closeIn is;
    FileSys.remove tmp_name;
    result
  end;

(*plain version; with return code*)
fun system cmd =
  if Process.system cmd = Process.success then 0 else 1;


(* file handling *)

(*get time of last modification*)
fun file_info name = Time.toString (FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

(*  Title:      Pure/ML-Systems/mlworks.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Compatibility file for MLWorks version 1.0r2 or later.
*)

(** ML system related **)

(* restore old-style character / string functions *)

fun ord s = Char.ord (String.sub (s, 0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(* MLWorks parameters *)

MLWorks.Internal.Runtime.Event.stack_overflow_handler
  (fn () => MLWorks.Internal.Runtime.Memory.max_stack_blocks :=
    ! MLWorks.Internal.Runtime.Memory.max_stack_blocks + 20);


(* Poly/ML emulation *)

(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;
fun quit () = exit 0;

(*n.a.*)
fun print_depth n = ();

(*interface for toplevel pretty printers, see also Pure/install_pp.ML*)
(*n.a.*)
fun make_pp path pprint = ();
fun install_pp _ = ();

(*prompts*)
(*n.a.??*)
fun ml_prompts p1 p2 = ();


(** Compiler-independent timing functions **)

(*Note start point for timing*)
fun startTiming() = 
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

(*Finish timing and return string*)
fun endTiming (CPUtimer, {gc,sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {gc=gc2,sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  GC " ^ toString (gc2-gc) ^
      "  All "^ toString (sys2-sys + usr2-usr + gc2-gc) ^
      " secs"
      handle Time => ""
  end;


(* ML command execution *)

(*Can one redirect 'use' directly to an instream?*)
fun use_strings strs =
  let
    val tmp_name = OS.FileSys.tmpName ();
    val tmp_file = TextIO.openOut tmp_name;
  in app (fn s => TextIO.output (tmp_file, s)) strs;
     TextIO.closeOut tmp_file;
     use tmp_name;
     OS.FileSys.remove tmp_name
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


(* file handling *)

(*get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""		(* FIXME !? *)
  | file_info name = Time.toString (OS.FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);


(* non-ASCII input (see also Thy/use.ML) *)

val needs_filtered_use = false;

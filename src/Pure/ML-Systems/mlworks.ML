(*  Title:      Pure/ML-Systems/mlworks.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Compatibility file for MLWorks version 1.0r2 or later.
*)

(*** Poly/ML emulation ***)

(*Just for versions of MLWorks that don't provide the Option structure*)
structure Option = General;

(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;
fun quit () = exit 0;

(*To limit the printing depth [divided by 2 for comparibility with Poly/ML]*)
fun print_depth n = ();

(*Interface for toplevel pretty printers, see also Pure/install_pp.ML
  CURRENTLY UNAVAILABLE*)
fun make_pp path pprint = ();
fun install_pp _ = ();


(*** Character/string functions which are compatible with 0.93 and Poly/ML ***)

fun ord s = Char.ord (String.sub(s,0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


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


(*** File handling ***)

(*Get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""
  | file_info name = Time.toString (OS.FileSys.modTime name) handle _ =>"";


(*** ML command execution ***)

val tmpName = OS.FileSys.tmpName();

(*Can one redirect 'use' directly to an instream?*)
fun use_strings slist =
  let val tmpFile = TextIO.openOut tmpName
  in app (fn s => TextIO.output (tmpFile, s)) slist;
     TextIO.closeOut tmpFile;
     use tmpName
  end;


(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.
  This could be done more easily by Unix.execute, but that function
  doesn't use the PATH.*)
fun execute command =
  let val is = (OS.Process.system (command ^ " > " ^ tmpName);
                TextIO.openIn tmpName);
      val result = TextIO.inputAll is;
  in TextIO.closeIn is;
     OS.FileSys.remove tmpName;
     result
  end;


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);


(*Non-printing and 8-bit chars are forbidden in string constants*)
val needs_filtered_use = true;


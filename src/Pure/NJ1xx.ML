(*  Title:      Pure/NJ1xx.ML
    ID:         $Id$
    Author:     Carsten Clasohm, TU Muenchen
    Copyright   1996  TU Muenchen

Compatibility file for Standard ML of New Jersey version 1.xx.
*)

(*** Poly/ML emulation ***)


(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = OS.Process.exit OS.Process.success
  | exit _ = OS.Process.exit OS.Process.failure;
fun quit () = exit 0;

(*To limit the printing depth [divided by 2 for comparibility with Poly/ML]*)
fun print_depth n = (Compiler.Control.Print.printDepth := n div 2;
                     Compiler.Control.Print.printLength := n);

(*Interface for toplevel pretty printers, see also Pure/install_pp.ML*)

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


(*** New Jersey ML parameters ***)

(* Suppresses Garbage Collection messages; doesn't work yet *)
(*System.Runtime.gc 0;*)

val _ = (Compiler.Control.Print.printLength := 1000;
         Compiler.Control.Print.printDepth := 350;
         Compiler.Control.Print.stringDepth := 250;
         Compiler.Control.Print.signatures := 2);

(*** Character/string functions which are compatible with 0.93 and Poly/ML ***)

fun ord s = Char.ord (String.sub(s,0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(*** Timing functions ***)

(*A conditional timing function: applies f to () and, if the flag is true,
  prints its runtime. *)
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
  else f();


(*** File handling ***)

(*Get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""
  | file_info name = Time.toString (OS.FileSys.modTime name) handle _ =>"";



(*** ML command execution ***)


(*For version 109.21 and later:*)
val use_string = Compiler.Interact.useStream o TextIO.openString o implode;

(*For versions prior to 109.21:*****
fun use_string commands = 
   Compiler.Interact.use_stream (open_string (implode commands));
*)

(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.
  This could be done more easily by Unix.execute, but that function
  doesn't use the PATH.*)
fun execute command =
  let val tmp_name = "isa_converted.tmp"
      val is = (OS.Process.system (command ^ " > " ^ tmp_name);
                TextIO.openIn tmp_name);
      val result = TextIO.inputAll is;
  in TextIO.closeIn is;
     OS.FileSys.remove tmp_name;
     result
  end;

(*For exporting images.  The short name saves space in Makefiles*)
fun xML filename banner =
  let open SMLofNJ
      val runtime = hd (SMLofNJ.getAllArgs())
      and exec_file = TextIO.openOut filename
  in 
     TextIO.output  (*Write a shell script to invoke the actual image*)
       (exec_file,
	String.concat
	["#!/bin/sh\n", runtime, 
	 " @SMLdebug=/dev/null",  (*suppresses GC messages*)
	 " @SMLload=", filename, ".heap\n"]);
     TextIO.closeOut exec_file;
     OS.Process.system ("chmod a+x " ^ filename);
     exportML (filename^".heap");
     print(banner^"\n")
  end;


val needs_filtered_use = false;

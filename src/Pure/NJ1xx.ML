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

(*To change the current directory*)
val cd = OS.FileSys.chDir;

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

(*** Character/string functions which are compatibel with 0.93 and Poly/ML ***)

val ord = Char.ord o hd o explode;
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(*** Timing functions ***)

val CPUtimer = Timer.totalCPUTimer();

(*A conditional timing function: applies f to () and, if the flag is true,
  prints its runtime. *)
fun cond_timeit flag f =
  if flag then
    let open Time;
        open Timer;
        val {gc=gct1,sys=syst1,usr=usrt1} = checkCPUTimer(CPUtimer);
        val result = f();
        val {gc=gct2,sys=syst2,usr=usrt2} = checkCPUTimer(CPUtimer)
    in  print("Non GC " ^ toString (usrt2-usrt1) ^
              "   GC " ^ toString (gct2-gct1) ^
              "  both+sys "^ toString (syst2-syst1 + usrt2-usrt1 + gct2-gct1) ^
              " secs\n");
        result
    end
  else f();


(*** File handling ***)

(*Get time of last modification; if file doesn't exist return an empty string*)
local
    open Timer;
    open Posix.FileSys;
in
  fun file_info "" = ""
    | file_info name = Time.toString (ST.mtime (stat name))  handle _ => "";

  val delete_file = unlink;
end;

(*Get pathname of current working directory *)
fun pwd () = OS.FileSys.getDir ();


(*** ML command execution ***)

fun use_string commands = 
   Compiler.Interact.use_stream (open_string (implode commands));


(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.
  This could be done more easily by Unix.execute, but that function
  doesn't use the PATH.*)
fun execute command =
  let val tmp_name = "isa_converted.tmp"
      val is = (OS.Process.system (command ^ " > " ^ tmp_name);
                open_in tmp_name);
      val result = input (is, 999999);
  in close_in is;
     delete_file tmp_name;
     result
  end;


(*For use in Makefiles -- saves space*)
fun xML filename banner =
  let val runtime = List.hd (SMLofNJ.getAllArgs())
      val exec_file = IO.open_out filename

      val _ = IO.output (exec_file,
			 String.concat
			 ["#!/bin/sh\n",
			  runtime, " @SMLdebug=/dev/null @SMLload=", filename,
                          ".heap\n"])
                             (*"@SMLdebug=..." sends GC messages to /dev/null*)

	val _ = IO.close_out exec_file;
	val _ = OS.Process.system ("chmod a+x " ^ filename)
    in exportML (filename^".heap");
       print(banner^"\n")
    end;

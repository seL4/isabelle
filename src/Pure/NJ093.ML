(*  Title:      Pure/NJ093.ML
    ID:         $Id$
    Author:     Carsten Clasohm, TU Muenchen
    Copyright   1996  TU Muenchen

Compatibility file for Standard ML of New Jersey version 0.93.
*)


use"basis.ML";

(*** Poly/ML emulation ***)

(*To exit the system with an exit code -- an alternative to ^D *)
val exit = System.Unsafe.CInterface.exit;
fun quit () = exit 0;

(*To limit the printing depth [divided by 2 for comparibility with Poly/ML]*)
fun print_depth n = (System.Control.Print.printDepth := n div 2;
                     System.Control.Print.printLength := n);

(*Interface for toplevel pretty printers, see also Pure/install_pp.ML*)

fun make_pp path pprint =
  let
    open System.PrettyPrint;

    fun pp pps obj =
      pprint obj
        (add_string pps, begin_block pps INCONSISTENT,
          fn wd => add_break pps (wd, 0), fn () => add_newline pps,
          fn () => end_block pps);
  in
    (path, pp)
  end;

fun install_pp (path, pp) = System.PrettyPrint.install_pp path pp;


(*** New Jersey ML parameters ***)

(* Suppresses Garbage Collection messages;  default was 2 *)
System.Control.Runtime.gcmessages := 0;


(*** Timing functions ***)

(*Print microseconds, suppressing trailing zeroes*)
fun umakestring 0 = ""
  | umakestring n = chr(ord "0" + n div 100000) ^
                    umakestring(10 * (n mod 100000));

(*A conditional timing function: applies f to () and, if the flag is true,
  prints its runtime. *)
fun cond_timeit flag f =
  if flag then
    let fun string_of_time (System.Timer.TIME {sec, usec}) =
            makestring sec ^ "." ^ (if usec=0 then "0" else umakestring usec)
        open System.Timer;
        val start = start_timer()
        val result = f();
        val nongc = check_timer(start)
        and gc = check_timer_gc(start);
        val both = add_time(nongc, gc)
    in  print("Non GC " ^ string_of_time nongc ^
               "   GC " ^ string_of_time gc ^
               "  both "^ string_of_time both ^ " secs\n");
        result
    end
  else f();


(*** File handling ***)

(*Get time of last modification; if file doesn't exist return an empty string*)
local
    open System.Timer;
    open System.Unsafe.SysIO;
in
  fun file_info "" = ""
    | file_info name = makestring (mtime (PATH name))  handle _ => "";
end;

structure OS =
  struct
  structure FileSys =
    struct
    val OS.FileSys.chDir = System.Directory.cd
    val remove = System.Unsafe.SysIO.unlink       (*Delete a file *)
    val getDir = System.Directory.getWD           (*path of working directory*)
    end
  end;


(*** ML command execution ***)

fun use_string commands = 
  System.Compile.use_stream (open_string (implode commands));


(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.
  This could be done more easily by IO.execute, but that function
  seems to be buggy in SML/NJ 0.93.*)
fun execute command =
  let val tmp_name = "isa_converted.tmp"
      val is = (System.system (command ^ " > " ^ tmp_name);
                open_in tmp_name);
      val result = input (is, 999999);
  in close_in is;
     delete_file tmp_name;
     result
  end;

(*redefine to flush its output immediately -- temporary patch suggested
  by Kim Dam Petersen*)
val output = fn(s, t) => (output(s, t); flush_out s);

(*For use in Makefiles -- saves space*)
fun xML filename banner = (exportML filename;  print(banner^"\n"));


val needs_filtered_use = false;

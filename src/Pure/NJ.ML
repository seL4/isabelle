(*  Title:      Pure/NJ
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Compatibility file for Standard ML of New Jersey.
*)

(*** Poly/ML emulation ***)

(*To exit the system -- an alternative to ^D *)
fun quit () = System.Unsafe.CInterface.exit 0;

(*To change the current directory*)
val cd = System.Directory.cd;

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

(*redefine to flush its output immediately -- temporary patch suggested
  by Kim Dam Petersen*)
val output = fn(s, t) => (output(s, t); flush_out s);

(*Dummy version of the Poly/ML function*)
fun commit() = ();

(*For use in Makefiles -- saves space*)
fun xML filename banner = (exportML filename;  print(banner^"\n"));

(*** Timing functions ***)

(*Print microseconds, suppressing trailing zeroes*)
fun umakestring 0 = ""
  | umakestring n = chr(ord"0" + n div 100000) ^
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

(*Get time of last modification.*)
local
    open System.Timer;
    open System.Unsafe.SysIO;
in
  fun file_info "" = ""
    | file_info name = makestring (mtime (PATH name));
end;

fun delete_file name = 
  let val _ = System.system ("rm " ^ name)
  in () end;

(*Get pathname of current working directory *)
fun pwd () = System.Directory.getWD ();

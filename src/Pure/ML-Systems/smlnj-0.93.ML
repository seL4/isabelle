(*  Title:      Pure/ML-Systems/smlnj-0.93.ML
    ID:         $Id$
    Author:     Carsten Clasohm, TU Muenchen
    Copyright   1996  TU Muenchen

Compatibility file for Standard ML of New Jersey version 0.93.
*)

(*needs the Basis Library emulation*)
use "basis.ML";


(** ML system related **)

(* New Jersey ML parameters *)

System.Control.Runtime.gcmessages := 0;


(* Poly/ML emulation *)

fun quit () = exit 0;

(*limit the printing depth -- divided by 2 for comparibility with Poly/ML*)
fun print_depth n =
 (System.Control.Print.printDepth := n div 2;
  System.Control.Print.printLength := n);



(* timing *)

(*Note start point for timing*)
fun startTiming() = System.Timer.start_timer();

(*Finish timing and return string*)
local
  (*print microseconds, suppressing trailing zeroes*)
  fun umakestring 0 = ""
    | umakestring n =
        chr (ord "0" + n div 100000) ^ umakestring (10 * (n mod 100000));

  fun string_of_time (System.Timer.TIME {sec, usec}) =
      makestring sec ^ "." ^ (if usec=0 then "0" else umakestring usec)

in

fun endTiming start =
  let val nongc = System.Timer.check_timer(start)
      and gc    = System.Timer.check_timer_gc(start);
      val both  = System.Timer.add_time(nongc, gc)
  in  "Non GC " ^ string_of_time nongc ^
      "   GC " ^ string_of_time gc ^
      "  both "^ string_of_time both ^ " secs\n"
  end
end;


(* prompts *)

fun ml_prompts p1 p2 = ();


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

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


(* ML command execution *)

fun use_strings commands =
  System.Compile.use_stream (open_string (implode commands));



(** OS related **)

(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout; could be done more easily by IO.execute,
  but that function seems to be buggy in SML/NJ 0.93*)
fun execute command =
  let
    val tmp_name = "/tmp/isabelle-execute";
    val is = (System.system (command ^ " > " ^ tmp_name); open_in tmp_name);
    val result = input (is, 999999);
  in
    close_in is;
    System.Unsafe.SysIO.unlink tmp_name;
    result
  end;


(* file handling *)

(*Get time of last modification; if file doesn't exist return an empty string*)
local
  open System.Timer System.Unsafe.SysIO;
in
  fun file_info "" = ""
    | file_info name = makestring (mtime (PATH name)) handle _ => "";
end;

structure OS =
struct
  structure FileSys =
  struct
    val chDir = System.Directory.cd;
    val remove = System.Unsafe.SysIO.unlink;
    val getDir = System.Directory.getWD;
  end;
end;

(*redefine to flush its output immediately -- temporary patch suggested
  by Kim Dam Petersen*)		(* FIXME !? *)
val output = fn (s, t) => (output (s, t); flush_out s);


(* getenv *)

local
  fun drop_last [] = []
    | drop_last [x] = []
    | drop_last (x :: xs) = x :: drop_last xs;

  val drop_last_char = implode o drop_last o explode;
in
  fun getenv var = drop_last_char
    (execute ("env | grep '^" ^ var ^ "=' | sed -e 's/" ^ var ^ "=//'"));
end;


(* non-ASCII input (see also Thy/use.ML) *)

val needs_filtered_use = false;

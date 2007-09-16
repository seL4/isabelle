(*  Title:      Pure/ML-Systems/mosml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Compatibility file for Moscow ML 2.01

NOTE: saving images does not work; may run it interactively as follows:

$ cd Isabelle/src/Pure
$ isabelle RAW_ML_SYSTEM
> val ml_system = "mosml";
> use "ML-Systems/mosml.ML";
> use "ROOT.ML";
> Session.finish ();
> cd "../FOL";
> use "ROOT.ML";
*)

(** ML system related **)

val ml_system_fix_ints = false;

load "Obj";
load "Bool";
load "Int";
load "Real";
load "ListPair";
load "OS";
load "Process";
load "FileSys";
load "IO";

use "ML-Systems/exn.ML";
use "ML-Systems/multithreading_dummy.ML";


(*low-level pointer equality*)
local val cast : 'a -> int = Obj.magic
in fun pointer_eq (x:'a, y:'a) = (cast x = cast y) end;

(*proper implementation available?*)
structure IntInf =
struct
  open Int;
end;

structure Real =
struct
  open Real;
  val realFloor = real o floor;
end;

structure String =
struct
  fun isSuffix s1 s2 =
    let val n1 = size s1 and n2 = size s2
    in if n1 = n2 then s1 = s2 else n1 <= n2 andalso String.substring (s2, n2 - n1, n1) = s1 end;
  open String;
end;

structure Time =
struct
  open Time;
  fun toString t = Time.toString t
    handle Overflow => Real.toString (Time.toReal t);   (*workaround Y2004 bug*)
end;

structure OS =
struct
  open OS
  structure Process = Process
  structure FileSys = FileSys
end;

exception Option = Option.Option;


(*limit the printing depth*)
local
  val depth = ref 10;
in
  fun get_print_depth () = ! depth;
  fun print_depth n =
   (depth := n;
    Meta.printDepth := n div 2;
    Meta.printLength := n);
end;

(*interface for toplevel pretty printers, see also Pure/pure_setup.ML*)
(*the documentation refers to an installPP but I couldn't fine it!*)
fun make_pp path pprint = ();
fun install_pp _ = ();

(*dummy implementation*)
fun ml_prompts p1 p2 = ();

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();

(*dummy implementation*)
fun print x = x;


(** Compiler-independent timing functions **)

load "Timer";

fun start_timing () =
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

fun end_timing (CPUtimer, {gc,sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {gc=gc2,sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  GC " ^ toString (gc2-gc) ^
      "  All "^ toString (sys2-sys + usr2-usr + gc2-gc) ^
      " secs"
      handle Time => ""
  end;

fun check_timer timer =
  let val {sys, usr, gc} = Timer.checkCPUTimer timer
  in (sys, usr, gc) end;


(* SML basis library fixes *)

structure TextIO =
struct
  fun canInput _ = raise IO.Io {cause = Fail "undefined", function = "canInput", name = ""};
  open TextIO;
  fun inputLine is =
    let val s = TextIO.inputLine is
    in if s = "" then NONE else SOME s end;
end;


(* bounded time execution *)

(*dummy implementation*)
fun interrupt_timeout time f x =
  f x;


(* ML command execution *)

(*Can one redirect 'use' directly to an instream?*)
fun use_text _ _ _ txt =
  let
    val tmp_name = FileSys.tmpName ();
    val tmp_file = TextIO.openOut tmp_name;
  in
    TextIO.output (tmp_file, txt);
    TextIO.closeOut tmp_file;
    use tmp_name;
    FileSys.remove tmp_name
  end;

fun use_file _ _ name = use name;



(** interrupts **)      (*Note: may get into race conditions*)

(* FIXME proper implementation available? *)

exception Interrupt;

fun ignore_interrupt f x = f x;
fun raise_interrupt f x = f x;



(** OS related **)

(* current directory *)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;


(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout; could be done more easily by Unix.execute,
  but that function doesn't use the PATH*)
fun execute command =
  let
    val tmp_name = FileSys.tmpName ();
    val is = (Process.system (command ^ " > " ^ tmp_name); TextIO.openIn tmp_name);
    val result = TextIO.inputAll is;
  in
    TextIO.closeIn is;
    FileSys.remove tmp_name;
    result
  end;

(*plain version; with return code*)
fun system cmd =
  if Process.system cmd = Process.success then 0 else 1;


val string_of_pid = Int.toString;


(* getenv *)

fun getenv var =
  (case Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

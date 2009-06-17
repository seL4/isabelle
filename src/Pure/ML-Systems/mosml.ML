(*  Title:      Pure/ML-Systems/mosml.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Compatibility file for Moscow ML 2.01

NOTE: saving images does not work; may run it interactively as follows:

$ cd Isabelle/src/Pure
$ isabelle-process RAW_ML_SYSTEM
> val ml_system = "mosml";
> use "ML-Systems/mosml.ML";
> use "ROOT.ML";
> Session.finish ();
> cd "../FOL";
> use "ROOT.ML";
> Session.finish ();
> cd "../ZF";
> use "ROOT.ML";
*)

(** ML system related **)

val ml_system_fix_ints = false;

fun forget_structure _ = ();

load "Obj";
load "Word";
load "Bool";
load "Int";
load "Real";
load "ListPair";
load "OS";
load "Process";
load "FileSys";
load "IO";
load "CharVector";

exception Interrupt;
fun reraise exn = raise exn;

use "ML-Systems/exn.ML";
use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/time_limit.ML";
use "ML-Systems/ml_name_space.ML";
use "ML-Systems/ml_pretty.ML";
use "ML-Systems/use_context.ML";


(*low-level pointer equality*)
local val cast : 'a -> int = Obj.magic
in fun pointer_eq (x:'a, y:'a) = (cast x = cast y) end;

(*proper implementation available?*)
structure IntInf =
struct
  fun divMod (x, y) = (x div y, x mod y);

  local
    fun log 1 a = a
      | log n a = log (n div 2) (a + 1);
  in
    fun log2 n = if n > 0 then log n 0 else raise Domain;
  end;

  open Int;
end;

structure Substring =
struct
  open Substring;
  val full = all;
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
  structure Process =
  struct
    open Process
    fun sleep _ = raise Fail "OS.Process.sleep undefined"
  end;
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

(*dummy implementation*)
fun toplevel_pp _ _ _ = ();

(*dummy implementation*)
fun ml_prompts p1 p2 = ();

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();



(** Compiler-independent timing functions **)

load "Timer";

fun start_timing () =
  let
    val timer = Timer.startCPUTimer ();
    val time = Timer.checkCPUTimer timer;
  in (timer, time) end;

fun end_timing (timer, {gc, sys, usr}) =
  let
    open Time;  (*...for Time.toString, Time.+ and Time.- *)
    val {gc = gc2, sys = sys2, usr = usr2} = Timer.checkCPUTimer timer;
    val user = usr2 - usr + gc2 - gc;
    val all = user + sys2 - sys;
    val message = "User " ^ toString user ^ "  All "^ toString all ^ " secs" handle Time => "";
  in {message = message, user = user, all = all} end;


(* SML basis library fixes *)

structure TextIO =
struct
  fun canInput _ = raise IO.Io {cause = Fail "undefined", function = "canInput", name = ""};
  open TextIO;
  fun inputLine is =
    let val s = TextIO.inputLine is
    in if s = "" then NONE else SOME s end;
  fun getOutstream _ = ();
  structure StreamIO =
  struct
    fun setBufferMode _ = ();
  end
end;

structure IO =
struct
  open IO;
  val BLOCK_BUF = ();
end;


(* ML command execution *)

(*Can one redirect 'use' directly to an instream?*)
fun use_text ({tune_source, ...}: use_context) _ _ txt =
  let
    val tmp_name = FileSys.tmpName ();
    val tmp_file = TextIO.openOut tmp_name;
  in
    TextIO.output (tmp_file, tune_source txt);
    TextIO.closeOut tmp_file;
    use tmp_name;
    FileSys.remove tmp_name
  end;

fun use_file _ _ name = use name;



(** interrupts **)      (*Note: may get into race conditions*)

(* FIXME proper implementation available? *)

fun interruptible f x = f x;
fun uninterruptible f x = f (fn (g: 'c -> 'd) => g) x;



(** OS related **)

(*dummy implementation*)
structure Posix =
struct
  structure ProcEnv =
  struct
    fun getpid () = 0;
  end;  
end;

local

fun read_file name =
  let val is = TextIO.openIn name
  in Exn.release (Exn.capture TextIO.inputAll is before TextIO.closeIn is) end;

fun write_file name txt =
  let val os = TextIO.openOut name
  in Exn.release (Exn.capture TextIO.output (os, txt) before TextIO.closeOut os) end;

in

fun system_out script =
  let
    val script_name = OS.FileSys.tmpName ();
    val _ = write_file script_name script;

    val output_name = OS.FileSys.tmpName ();

    val status =
      OS.Process.system ("perl -w \"$ISABELLE_HOME/lib/scripts/system.pl\" nogroup " ^
        script_name ^ " /dev/null " ^ output_name);
    val rc = if status = OS.Process.success then 0 else 1;

    val output = read_file output_name handle IO.Io _ => "";
    val _ = OS.FileSys.remove script_name handle OS.SysErr _ => ();
    val _ = OS.FileSys.remove output_name handle OS.SysErr _ => ();
  in (output, rc) end;

end;

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;

val process_id = Int.toString o Posix.ProcEnv.getpid;

fun getenv var =
  (case Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

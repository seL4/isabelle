(*  Title:      Pure/ML-Systems/alice.ML
    ID:         $Id$

Compatibility file for Alice 1.4.

NOTE: there is no wrapper script; may run it interactively as follows:

$ cd Isabelle/src/Pure
$ env ALICE_JIT_MODE=0 alice
- val ml_system = "alice";
- use "ML-Systems/exn.ML";
- use "ML-Systems/multithreading.ML";
- use "ML-Systems/time_limit.ML";
- use "ML-Systems/system_shell.ML";
- use "ML-Systems/alice.ML";
- use "ROOT.ML";
- Session.finish ();
*)

val ml_system_fix_ints = false;

fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;


(** ML system related **)

(*low-level pointer equality*)
fun pointer_eq (_: 'a, _: 'a) = false;


(* integer compatibility -- downgraded IntInf *)

structure Time =
struct
  open Time;
  val fromMilliseconds = Time.fromMilliseconds o IntInf.fromInt;
  val fromSeconds = Time.fromSeconds o IntInf.fromInt;
end;

structure IntInf =
struct
  fun divMod (x, y) = (x div y, x mod y);
  open Int;
end;


(* restore old-style character / string functions *)

exception Ord;
fun ord "" = raise Ord
  | ord s = Char.ord (String.sub (s, 0));

val chr = String.str o chr;
val explode = map String.str o String.explode;
val implode = String.concat;


(* Poly/ML emulation *)

fun quit () = exit 0;

fun get_print_depth () = ! Print.depth;
fun print_depth n = Print.depth := n;


(* compiler-independent timing functions *)

structure Timer =
struct
  open Timer;
  type cpu_timer = unit;
  fun startCPUTimer () = ();
  fun checkCPUTimer () = {sys = Time.zeroTime, usr = Time.zeroTime};
  fun checkGCTime () = Time.zeroTime;
end;

fun start_timing () =
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

fun end_timing (CPUtimer, {sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  All "^ toString (sys2-sys + usr2-usr) ^
      " secs"
      handle Time => ""
  end;

fun check_timer timer =
  let
    val {sys, usr} = Timer.checkCPUTimer timer;
    val gc = Timer.checkGCTime timer;    (* FIXME already included in usr? *)
  in (sys, usr, gc) end;


(*prompts*)
fun ml_prompts p1 p2 = ();

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();

(*dummy implementation*)
fun print x = x;


(* toplevel pretty printing (see also Pure/pure_setup.ML) *)

fun make_pp path pprint = (path, pprint);
fun install_pp (path, pp) = ();


(* ML command execution *)

fun use_text tune name (print, err) verbose txt = (Compiler.eval txt; ());

fun use_file tune output verbose name = use name;



(** interrupts **)

exception Interrupt;

fun interruptible f x = f x;
fun uninterruptible f x = f (fn (g: 'c -> 'd) => g) x;


(* basis library fixes *)

structure TextIO =
struct
  open TextIO;
  fun inputLine is = TextIO.inputLine is
    handle IO.Io _ => raise Interrupt;
end;



(** OS related **)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;

val system = OS.Process.system: string -> int;

structure OS =
struct
  open OS;
  structure FileSys =
  struct
    fun fileId name =
      (case execute ("perl -e '@_ = stat(q:" ^ name ^ ":); print $_[1]'") of
        "" => raise Fail "OS.FileSys.fileId"   (* FIXME IO.Io!? *)
      | s => (case Int.fromString s of NONE => raise Fail "OS.FileSys.fileId" | SOME i => i));
    val compare = Int.compare;
    open FileSys;
  end;
end;

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

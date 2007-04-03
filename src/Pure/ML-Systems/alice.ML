(*  Title:      Pure/ML-Systems/alice.ML
    ID:         $Id$

Compatibility file for Alice 1.3.
val ml_system = "alice";
use "ML-Systems/alice.ML";

*)

fun exit 0 = (OS.Process.exit OS.Process.success): unit
  | exit _ = OS.Process.exit OS.Process.failure;


(** ML system related **)

(*low-level pointer equality*)
fun pointer_eq (_: 'a, _: 'a) = false;


(* restore old-style character / string functions *)

exception Ord;
fun ord "" = raise Ord
  | ord s = Char.ord (String.sub (s, 0));

val chr = Char.toString o chr;
val explode = map Char.toString o String.explode;
val implode = String.concat;


(* Poly/ML emulation *)

fun quit () = exit 0;

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


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp path pprint = (path, pprint);
fun install_pp (path, pp) = ();


(* ML command execution *)

fun use_text name (print, err) verbose txt = (Compiler.eval txt; ());

fun use_file _ _ name = use name;



(** interrupts **)

exception Interrupt;

fun ignore_interrupt f x = f x;
fun raise_interrupt f x = f x;


(* basis library fixes *)

structure TextIO =
struct
  open TextIO;

  fun inputLine is =
    (case TextIO.inputLine is of
      SOME str => str
    | NONE => "")
    handle IO.Io _ => raise Interrupt;
end;


(* bounded time execution *)

(*dummy implementation*)
fun interrupt_timeout time f x =
  f x;



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

(*plain version; with return code*)
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


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

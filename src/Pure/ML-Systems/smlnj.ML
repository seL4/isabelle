(*  Title:      Pure/ML-Systems/smlnj.ML

Compatibility file for Standard ML of New Jersey 110 or later.
*)

exception Interrupt;
fun reraise exn = raise exn;

use "ML-Systems/proper_int.ML";
use "ML-Systems/overloading_smlnj.ML";
use "ML-Systems/exn.ML";
use "ML-Systems/universal.ML";
use "ML-Systems/thread_dummy.ML";
use "ML-Systems/multithreading.ML";
use "ML-Systems/system_shell.ML";
use "ML-Systems/ml_name_space.ML";
use "ML-Systems/ml_pretty.ML";
use "ML-Systems/use_context.ML";


(*low-level pointer equality*)

CM.autoload "$smlnj/init/init.cmi";
val pointer_eq = InlineT.ptreql;


(* restore old-style character / string functions *)

val ord     = mk_int o SML90.ord;
val chr     = SML90.chr o dest_int;
val explode = SML90.explode;
val implode = SML90.implode;


(* New Jersey ML parameters *)

val _ =
 (Control.Print.printLength := 1000;
  Control.Print.printDepth := 350;
  Control.Print.stringDepth := 250;
  Control.Print.signatures := 2;
  Control.MC.matchRedundantError := false);


(* Poly/ML emulation *)

val exit = exit o dest_int;
fun quit () = exit 0;

(*limit the printing depth -- divided by 2 for comparibility with Poly/ML*)
local
  val depth = ref (10: int);
in
  fun get_print_depth () = ! depth;
  fun print_depth n =
   (depth := n;
    Control.Print.printDepth := dest_int n div 2;
    Control.Print.printLength := dest_int n);
end;


(* compiler-independent timing functions *)

fun start_timing () =
  let
    val timer = Timer.startCPUTimer ();
    val time = Timer.checkCPUTimer timer;
  in (timer, time) end;

fun end_timing (timer, {sys, usr}) =
  let
    open Time;  (*...for Time.toString, Time.+ and Time.- *)
    val {sys = sys2, usr = usr2} = Timer.checkCPUTimer timer;
    val user = usr2 - usr;
    val all = user + sys2 - sys;
    val message = "User " ^ toString user ^ "  All "^ toString all ^ " secs" handle Time => "";
  in {message = message, user = user, all = all} end;

fun check_timer timer =
  let
    val {sys, usr} = Timer.checkCPUTimer timer;
    val gc = Timer.checkGCTime timer;    (* FIXME already included in usr? *)
  in (sys, usr, gc) end;


(*prompts*)
fun ml_prompts p1 p2 =
  (Control.primaryPrompt := p1; Control.secondaryPrompt := p2);

(*dummy implementation*)
fun profile (n: int) f x = f x;

(*dummy implementation*)
fun exception_trace f = f ();


(* ML command execution *)

fun use_text ({tune_source, print, error, ...}: use_context) (line, name) verbose txt =
  let
    val ref out_orig = Control.Print.out;

    val out_buffer = ref ([]: string list);
    val out = {say = (fn s => out_buffer := s :: ! out_buffer), flush = (fn () => ())};
    fun output () =
      let val str = implode (rev (! out_buffer))
      in String.substring (str, 0, Int.max (0, size str - 1)) end;
  in
    Control.Print.out := out;
    Backend.Interact.useStream (TextIO.openString (tune_source txt)) handle exn =>
      (Control.Print.out := out_orig;
        error ((if name = "" then "" else "Error in " ^ name ^ "\n") ^ output ()); raise exn);
    Control.Print.out := out_orig;
    if verbose then print (output ()) else ()
  end;

fun use_file context verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text context (1, name) verbose txt end;

fun forget_structure _ = ();


(* toplevel pretty printing *)

fun ml_pprint pps =
  let
    fun str "" = ()
      | str s = PrettyPrint.string pps s;
    fun pprint (ML_Pretty.Block ((bg, en), prts, ind)) =
          (str bg; PrettyPrint.openHOVBox pps (PrettyPrint.Rel (dest_int ind));
            List.app pprint prts; PrettyPrint.closeBox pps; str en)
      | pprint (ML_Pretty.String (s, _)) = str s
      | pprint (ML_Pretty.Break (false, wd)) = PrettyPrint.break pps {nsp = dest_int wd, offset = 0}
      | pprint (ML_Pretty.Break (true, _)) = PrettyPrint.newline pps;
  in pprint end;

fun toplevel_pp context path pp =
  use_text context (1, "pp") false
    ("CompilerPPTable.install_pp [" ^ String.concatWith "," (map (fn s => "\"" ^ s ^ "\"")  path) ^
      "] (fn pps => ml_pprint pps o Pretty.to_ML o (" ^ pp ^ "))");



(** interrupts **)

local

fun change_signal new_handler f x =
  let
    val old_handler = Signals.setHandler (Signals.sigINT, new_handler);
    val result = Exn.capture (f old_handler) x;
    val _ = Signals.setHandler (Signals.sigINT, old_handler);
  in Exn.release result end;

in

fun interruptible (f: 'a -> 'b) x =
  let
    val result = ref (Exn.Exn Interrupt: 'b Exn.result);
    val old_handler = Signals.inqHandler Signals.sigINT;
  in
    SMLofNJ.Cont.callcc (fn cont =>
      (Signals.setHandler (Signals.sigINT, Signals.HANDLER (fn _ => cont));
        result := Exn.capture f x));
    Signals.setHandler (Signals.sigINT, old_handler);
    Exn.release (! result)
  end;

fun uninterruptible f =
  change_signal Signals.IGNORE
    (fn old_handler => f (fn g => change_signal old_handler (fn _ => g)));

end;


(* basis library fixes *)

structure TextIO =
struct
  open TextIO;
  fun inputLine is = TextIO.inputLine is
    handle IO.Io _ => raise Interrupt;
end;



(** OS related **)

(* current directory *)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;


(* system command execution *)

val system_out = (fn (output, rc) => (output, mk_int rc)) o system_out;


(*Convert a process ID to a decimal string (chiefly for tracing)*)
fun process_id pid =
  Word.fmt StringCvt.DEC (Word.fromLargeWord (Posix.Process.pidToWord (Posix.ProcEnv.getpid ())));


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);

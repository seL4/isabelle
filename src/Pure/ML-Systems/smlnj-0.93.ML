(*  Title:      Pure/ML-Systems/smlnj-0.93.ML
    ID:         $Id$
    Author:     Carsten Clasohm, TU Muenchen
    Copyright   1996  TU Muenchen

Compatibility file for Standard ML of New Jersey version 0.93.
*)

(*needs the Basis Library emulation*)
use "basis.ML";

structure String =
struct
  fun substring args = String.substring args
    handle String.Substring => raise Subscript;
  fun isPrefix s1 s2 = (s1 = substring(s2,0, size s1))
    handle Subscript => false;
end;



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

fun use_text _ _ = System.Compile.use_stream o open_string;



(** interrupts **)

exception Interrupt;

local

datatype 'a result =
  Result of 'a |
  Exn of exn;

fun capture f x = Result (f x) handle exn => Exn exn;

fun release (Result x) = x
  | release (Exn exn) = raise exn;


val sig_int = System.Signals.SIGINT;

val interruptible = not o System.Signals.masked;
fun mask_signals () = System.Signals.maskSignals true;
fun unmask_signals () = System.Signals.maskSignals false;

fun change_mask ok change unchange f x =
  if ok () then f x
  else
    let
      val _ = change ();
      val result = capture f x;
      val _ = unchange ();
    in release result end;

in

fun ignore_interrupt f = change_mask (not o interruptible) mask_signals unmask_signals f;

fun raise_interrupt f x =
  let
    val orig_handler = System.Signals.inqHandler sig_int;
    fun reset_handler () = (System.Signals.setHandler (sig_int, orig_handler); ());

    val interrupted = ref false;

    fun set_handler cont =
      System.Signals.setHandler (sig_int, SOME (fn _ => (interrupted := true; cont)));

    fun proceed cont =
      let
        val _ = set_handler cont;
        val result = unmask_interrupt (capture f) x;
        val _ = reset_handler ();
      in release result end;
  in
    callcc proceed;
    reset_handler ();
    if ! interrupted then raise Interrupt else ()
   end;

end;



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

(*plain version; with return code*)
fun system cmd = System.system cmd div 256;


(* file handling *)

(*get time of last modification*)
local
  open System.Timer System.Unsafe.SysIO;
in
  fun file_info name = makestring (mtime (PATH name)) handle _ => "";
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
  by Kim Dam Petersen*)         (* FIXME !? *)
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

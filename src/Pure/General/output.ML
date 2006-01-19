(*  Title:      Pure/General/output.ML
    ID:         $Id$
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Output channels and diagnostic messages.
*)

signature BASIC_OUTPUT =
sig
  val print_mode: string list ref
  val std_output: string -> unit
  val std_error: string -> unit
  val immediate_output: string -> unit
  val writeln_default: string -> unit
  val writeln_fn: (string -> unit) ref    (*default output (in messages window)*)
  val priority_fn: (string -> unit) ref   (*high-priority (maybe modal/pop-up; must be displayed)*)
  val tracing_fn: (string -> unit) ref    (*tracing message (possibly in tracing window)*)
  val warning_fn: (string -> unit) ref    (*display warning of non-fatal situation*)
  val error_fn: (string -> unit) ref      (*display fatal error (possibly modal msg)*)
  val panic_fn: (string -> unit) ref      (*unrecoverable fatal error; exits system!*)
  val info_fn: (string -> unit) ref       (*incidental information message (e.g. timing)*)
  val debug_fn: (string -> unit) ref      (*internal debug messages*)
  val writeln: string -> unit
  val priority: string -> unit
  val tracing: string -> unit
  val warning: string -> unit
  val update_warn: ('a * 'a -> bool) -> string -> ('a * 'b) -> ('a * 'b) list -> ('a * 'b) list
  val overwrite_warn: (''a * 'b) list * (''a * 'b) -> string -> (''a * 'b) list
  val show_debug_msgs: bool ref
  val no_warnings: ('a -> 'b) -> 'a -> 'b
  val timing: bool ref
  val cond_timeit: bool -> (unit -> 'a) -> 'a
  val timeit: (unit -> 'a) -> 'a
  val timeap: ('a -> 'b) -> 'a -> 'b
  val timeap_msg: string -> ('a -> 'b) -> 'a -> 'b
  val time_accumulator: string -> ('a -> 'b) -> 'a -> 'b
end;

signature OUTPUT =
sig
  include BASIC_OUTPUT
  val has_mode: string -> bool
  val output_width: string -> string * real
  val output: string -> string
  val indent: string * int -> string
  val raw: string -> string
  exception TOPLEVEL_ERROR
  val do_toplevel_errors: bool ref
  val toplevel_errors: ('a -> 'b) -> 'a -> 'b
  val ML_errors: ('a -> 'b) -> 'a -> 'b
  val panic: string -> unit
  val info: string -> unit
  val debug: string -> unit
  val error_msg: string -> unit
  val add_mode: string ->
    (string -> string * real) * (string * int -> string) * (string -> string) -> unit
  val accumulated_time: unit -> unit
end;

structure Output: OUTPUT =
struct

(** print modes **)

val print_mode = ref ([]: string list);

fun has_mode s = s mem_string ! print_mode;

type mode_fns =
 {output_width: string -> string * real,
  indent: string * int -> string,
  raw: string -> string};

val modes = ref (Symtab.empty: mode_fns Symtab.table);

fun lookup_mode name = Symtab.lookup (! modes) name;

exception MISSING_DEFAULT_OUTPUT;

fun get_mode () =
  (case Library.get_first lookup_mode (! print_mode) of SOME p => p
  | NONE =>
      (case lookup_mode "" of SOME p => p
      | NONE => raise MISSING_DEFAULT_OUTPUT));  (*sys_error would require output again!*)

fun output_width x = #output_width (get_mode ()) x;
val output = #1 o output_width;
fun indent x = #indent (get_mode ()) x;
fun raw x = #raw (get_mode ()) x;



(** output channels **)

(* output primitives -- normally NOT used directly!*)

fun std_output s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
fun std_error s = (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr);

val immediate_output = std_output o output;
val writeln_default = std_output o suffix "\n";


(* Isabelle output channels *)

val writeln_fn = ref writeln_default;
val priority_fn = ref (fn s => ! writeln_fn s);
val tracing_fn = ref (fn s => ! writeln_fn s);
val warning_fn = ref (std_output o suffix "\n" o prefix_lines "### ");
val error_fn = ref (std_output o suffix "\n" o prefix_lines "*** ");
val panic_fn = ref (std_output o suffix "\n" o prefix_lines "!!! ");
val info_fn = ref (std_output o suffix "\n" o prefix_lines  "+++ ");
val debug_fn = ref (std_output o suffix "\n" o prefix_lines "::: ");

fun writeln s = ! writeln_fn (output s);
fun priority s = ! priority_fn (output s);
fun tracing s = ! tracing_fn (output s);
fun warning s = ! warning_fn (output s);
fun info s = ! info_fn (output s);

fun no_warnings f = setmp warning_fn (K ()) f;

val show_debug_msgs = ref false;
fun debug s = if ! show_debug_msgs then ! debug_fn (output s) else ()

fun error_msg s = ! error_fn (output s);

fun panic_msg s = ! panic_fn (output s);
fun panic s = (panic_msg ("## SYSTEM EXIT ##\n" ^ s); exit 1);


(* toplevel errors *)

exception TOPLEVEL_ERROR;

val do_toplevel_errors = ref true;

fun toplevel_errors f x =
  if ! do_toplevel_errors then
    f x handle ERROR msg => (error_msg msg; raise TOPLEVEL_ERROR)
  else f x;

fun ML_errors f = setmp do_toplevel_errors true (toplevel_errors f);


(* AList operations *)

fun overwrite (al, p as (key, _)) =
  let fun over ((q as (keyi, _)) :: pairs) =
            if keyi = key then p :: pairs else q :: (over pairs)
        | over [] = [p]
  in over al end;

fun overwrite_warn (args as (alist, (a, _))) msg =
 (if is_none (AList.lookup (op =) alist a) then () else warning msg;
  overwrite args);

fun update_warn eq msg (kv as (key, value)) xs =
 (if (not o AList.defined eq xs) key then () else warning msg;
  AList.update eq kv xs);


(* add_mode *)

fun add_mode name (f, g, h) =
 (if is_none (lookup_mode name) then ()
  else warning ("Redeclaration of symbol print mode: " ^ quote name);
  modes := Symtab.update (name, {output_width = f, indent = g, raw = h}) (! modes));



(** timing **)

(*global timing mode*)
val timing = ref false;

(*a conditional timing function: applies f to () and, if the flag is true,
  prints its runtime on warning channel*)
fun cond_timeit flag f =
  if flag then
    let val start = startTiming()
        val result = f ()
    in info (endTiming start); result end
  else f ();

(*unconditional timing function*)
fun timeit x = cond_timeit true x;

(*timed application function*)
fun timeap f x = timeit (fn () => f x);
fun timeap_msg s f x = (info s; timeap f x);


(* accumulated timing *)

local

datatype time_info = TI of
  {name: string,
   timer: Timer.cpu_timer,
   sys: Time.time,
   usr: Time.time,
   gc: Time.time,
   count: int};

fun time_init name = ref (TI
 {name = name,
  timer = Timer.startCPUTimer (),
  sys = Time.zeroTime,
  usr = Time.zeroTime,
  gc = Time.zeroTime,
  count = 0});

fun time_reset (r as ref (TI {name, ...})) = r := ! (time_init name);

fun time_check (ref (TI r)) = r;

fun time_add ti f x =
  let
    fun add_diff time time1 time2 =
      Time.+ (time, Time.- (time2, time1) handle Time.Time => Time.zeroTime);
    val {name, timer, sys, usr, gc, count} = time_check ti;
    val (sys1, usr1, gc1) = checkTimer timer;
    val result = capture f x;
    val (sys2, usr2, gc2) = checkTimer timer;
  in
    ti := TI
     {name = name,
      timer = timer,
      sys = add_diff sys sys1 sys2,
      usr = add_diff usr usr1 usr2,
      gc = add_diff gc gc1 gc2,
      count = count + 1};
    release result
  end;

fun time_finish ti =
  let
    fun secs prfx time = prfx ^ Time.toString time;
    val {name, timer, sys, usr, gc, count} = time_check ti;
  in
    info ("Total of " ^ quote name ^ ": " ^
      secs "User " usr ^ secs "  GC " gc ^ secs "  All " (Time.+ (sys, Time.+ (usr, gc))) ^
      " secs in " ^ string_of_int count ^ " calls");
    time_reset ti
  end;

val time_finish_hooks = ref ([]: (unit -> unit) list);

in

fun time_accumulator name =
  let val ti = time_init name in
    change time_finish_hooks (cons (fn () => time_finish ti));
    time_add ti
  end;

fun accumulated_time () = List.app (fn f => f ()) (! time_finish_hooks);

end;

end;

structure BasicOutput: BASIC_OUTPUT = Output;
open BasicOutput;

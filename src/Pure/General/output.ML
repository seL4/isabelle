(*  Title:      Pure/General/output.ML
    ID:         $Id$
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Output channels and diagnostic messages.
*)

signature BASIC_OUTPUT =
sig
  val print_mode: string list ref
  val std_output: string -> unit
  val std_error: string -> unit
  val writeln_default: string -> unit
  val writeln_fn: (string -> unit) ref
  val priority_fn: (string -> unit) ref
  val tracing_fn: (string -> unit) ref
  val warning_fn: (string -> unit) ref
  val error_fn: (string -> unit) ref
  val panic_fn: (string -> unit) ref
  val writeln: string -> unit
  val priority: string -> unit
  val tracing: string -> unit
  val warning: string -> unit
  val error_msg: string -> unit
  val error: string -> 'a
  val sys_error: string -> 'a
  val panic: string -> unit
  val assert: bool -> string -> unit
  val deny: bool -> string -> unit
  val assert_all: ('a -> bool) -> 'a list -> ('a -> string) -> unit
  val overwrite_warn: (''a * 'b) list * (''a * 'b) -> string -> (''a * 'b) list
  datatype 'a error = Error of string | OK of 'a
  val get_error: 'a error -> string option
  val get_ok: 'a error -> 'a option
  val handle_error: ('a -> 'b) -> 'a -> 'b error
  exception ERROR_MESSAGE of string
  val transform_error: ('a -> 'b) -> 'a -> 'b
  val transform_failure: (exn -> exn) -> ('a -> 'b) -> 'a -> 'b
  val timing: bool ref
  val cond_timeit: bool -> (unit -> 'a) -> 'a
  val timeit: (unit -> 'a) -> 'a
  val timeap: ('a -> 'b) -> 'a -> 'b
  val timeap_msg: string -> ('a -> 'b) -> 'a -> 'b
  type time_info
  val time_init: unit -> time_info ref
  val time_reset: time_info ref -> unit
  val time_check: time_info ref -> {timer: Timer.cpu_timer,
    sys: Time.time, usr: Time.time, gc: Time.time, count: int}
  val time_finish: string -> time_info ref -> unit
  val time: time_info ref -> ('a -> 'b) -> 'a -> 'b
end;

signature OUTPUT =
sig
  include BASIC_OUTPUT
  val has_mode: string -> bool
  exception MISSING_DEFAULT_OUTPUT
  val output_width: string -> string * real
  val output: string -> string
  val indent: string * int -> string
  val raw: string -> string
  val add_mode: string ->
    (string -> string * real) * (string * int -> string) * (string -> string) -> unit
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

exception MISSING_DEFAULT_OUTPUT;

fun lookup_mode name = Symtab.lookup (! modes, name);

fun get_mode () =
  (case Library.get_first lookup_mode (! print_mode) of Some p => p
  | None =>
      (case lookup_mode "" of Some p => p
      | None => raise MISSING_DEFAULT_OUTPUT));  (*sys_error would require output again!*)

fun output_width x = #output_width (get_mode ()) x;
val output = #1 o output_width;
fun indent x = #indent (get_mode ()) x;
fun raw x = #raw (get_mode ()) x;



(** output channels **)

(*primitive process channels -- normally NOT used directly!*)
fun std_output s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
fun std_error s = (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr);

val writeln_default = std_output o suffix "\n";

(*hooks for Isabelle channels*)
val writeln_fn = ref writeln_default;
val priority_fn = ref (fn s => ! writeln_fn s);
val tracing_fn = ref (fn s => ! writeln_fn s);
val warning_fn = ref (std_output o suffix "\n" o prefix_lines "### ");
val error_fn = ref (std_output o suffix "\n" o prefix_lines "*** ");
val panic_fn = ref (std_output o suffix "\n" o prefix_lines "!!! ");

fun writeln s = ! writeln_fn (output s);
fun priority s = ! priority_fn (output s);
fun tracing s = ! tracing_fn (output s);
fun warning s = ! warning_fn (output s);
fun error_msg s = ! error_fn (output s);
fun panic_msg s = ! panic_fn (output s);


(* add_mode *)

fun add_mode name (f, g, h) =
 (if is_none (lookup_mode name) then ()
  else warning ("Redeclaration of symbol print mode: " ^ quote name);
  modes := Symtab.update ((name, {output_width = f, indent = g, raw = h}), ! modes));


(* produce errors *)

fun error s = (error_msg s; raise ERROR);
fun sys_error msg = error ("## SYSTEM ERROR ##\n" ^ msg);
fun panic s = (panic_msg ("## SYSTEM EXIT ##\n" ^ s); exit 1);

fun assert p msg = if p then () else error msg;
fun deny p msg = if p then error msg else ();

(*Assert pred for every member of l, generating a message if pred fails*)
fun assert_all pred l msg_fn =
  let fun asl [] = ()
        | asl (x::xs) = if pred x then asl xs else error (msg_fn x)
  in asl l end;

fun overwrite_warn (args as (alist, (a, _))) msg =
 (if is_none (assoc (alist, a)) then () else warning msg;
  overwrite args);



(** handle errors  **)

datatype 'a error =
  Error of string |
  OK of 'a;

fun get_error (Error msg) = Some msg
  | get_error _ = None;

fun get_ok (OK x) = Some x
  | get_ok _ = None;

fun handle_error f x =
  let
    val buffer = ref ([]: string list);
    fun store_msg s = buffer := ! buffer @ [raw s];
    fun err_msg () = if not (null (! buffer)) then error_msg (cat_lines (! buffer)) else ();
  in
    (case Result (setmp error_fn store_msg f x) handle exn => Exn exn of
      Result y => (err_msg (); OK y)
    | Exn ERROR => Error (cat_lines (! buffer))
    | Exn exn => (err_msg (); raise exn))
  end;


(* transform ERROR into ERROR_MESSAGE *)

exception ERROR_MESSAGE of string;

fun transform_error f x =
  (case handle_error f x of
    OK y => y
  | Error msg => raise ERROR_MESSAGE msg);


(* transform any exception, including ERROR *)

fun transform_failure exn f x =
  transform_error f x handle Interrupt => raise Interrupt | e => raise exn e;



(** timing **)

(*global timing mode*)
val timing = ref false;

(*a conditional timing function: applies f to () and, if the flag is true,
  prints its runtime on warning channel*)
fun cond_timeit flag f =
  if flag then
    let val start = startTiming()
        val result = f ()
    in warning (endTiming start); result end
  else f ();

(*unconditional timing function*)
fun timeit x = cond_timeit true x;

(*timed application function*)
fun timeap f x = timeit (fn () => f x);
fun timeap_msg s f x = (warning s; timeap f x);


(* accumulated timing *)

local

fun add_interval time time1 time2 =
  Time.+ (time, Time.- (time2, time1) handle Time.Time => Time.zeroTime);

fun secs prfx time = prfx ^ Time.toString time;

in

datatype time_info = TI of
  {timer: Timer.cpu_timer,
   sys: Time.time,
   usr: Time.time,
   gc: Time.time,
   count: int};

fun time_init () = ref (TI {timer = Timer.startCPUTimer (),
    sys = Time.zeroTime, usr = Time.zeroTime, gc = Time.zeroTime, count = 0});

fun time_reset r = r := ! (time_init ());

fun time_check (ref (TI r)) = r;

fun time_finish name ti =
  let val {timer, sys, usr, gc, count} = time_check ti in
    warning ("Total of " ^ quote name ^ ": " ^
      secs "User " usr ^ secs "  GC " gc ^ secs "  All " (Time.+ (sys, Time.+ (usr, gc))) ^
      " secs in " ^ string_of_int count ^ " calls");
    ti := TI {timer = timer, sys = Time.zeroTime, usr = Time.zeroTime,
      gc = Time.zeroTime, count = 0}
  end;

fun time ti f x =
  let
    val {timer, sys, usr, gc, count} = time_check ti;
    val (sys1, usr1, gc1) = checkTimer timer;
    val result = capture f x;
    val (sys2, usr2, gc2) = checkTimer timer;
  in
    ti := TI {timer = timer,
      sys = add_interval sys sys1 sys2,
      usr = add_interval usr usr1 usr2,
      gc = add_interval gc gc1 gc2,
      count = count + 1};
    release result
  end;

end;

end;

structure BasicOutput: BASIC_OUTPUT = Output;
open BasicOutput;

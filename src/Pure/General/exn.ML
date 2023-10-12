(*  Title:      Pure/General/exn.ML
    Author:     Makarius

Support for exceptions.
*)

signature BASIC_EXN =
sig
  exception ERROR of string
  val error: string -> 'a
  val cat_error: string -> string -> 'a
end;

signature EXN0 =
sig
  include BASIC_EXN
  val polyml_location: exn -> PolyML.location option
  val reraise: exn -> 'a
  datatype 'a result = Res of 'a | Exn of exn
  val is_res: 'a result -> bool
  val is_exn: 'a result -> bool
  val get_res: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture0: ('a -> 'b) -> 'a -> 'b result  (*unmanaged interrupts*)
  val release: 'a result -> 'a
  val map_res: ('a -> 'b) -> 'a result -> 'b result
  val maps_res: ('a -> 'b result) -> 'a result -> 'b result
  val map_exn: (exn -> exn) -> 'a result -> 'a result
  val cause: exn -> exn
  exception Interrupt_Break
  exception Interrupt_Breakdown
  val is_interrupt_raw: exn -> bool
  val is_interrupt_break: exn -> bool
  val is_interrupt_breakdown: exn -> bool
  val is_interrupt_proper: exn -> bool
  val is_interrupt: exn -> bool
  val is_interrupt_proper_exn: 'a result -> bool
  val is_interrupt_exn: 'a result -> bool
  val result: ('a -> 'b) -> 'a -> 'b result
  val failure_rc: exn -> int
  exception EXCEPTIONS of exn list
  val trace: (exn -> string) -> (string -> unit) -> (unit -> 'a) -> 'a
end;

signature EXN =
sig
  include EXN0
  val capture: ('a -> 'b) -> 'a -> 'b result  (*managed interrupts*)
  val capture_body: (unit -> 'a) -> 'a result
end;

structure Exn: EXN0 =
struct

(* location *)

val polyml_location = PolyML.Exception.exceptionLocation;

val reraise = PolyML.Exception.reraise;


(* user errors *)

exception ERROR of string;

fun error msg = raise ERROR msg;

fun cat_error "" msg = error msg
  | cat_error msg "" = error msg
  | cat_error msg1 msg2 = error (msg1 ^ "\n" ^ msg2);


(* exceptions as values *)

datatype 'a result =
  Res of 'a |
  Exn of exn;

fun is_res (Res _) = true
  | is_res _ = false;

fun is_exn (Exn _) = true
  | is_exn _ = false;

fun get_res (Res x) = SOME x
  | get_res _ = NONE;

fun get_exn (Exn exn) = SOME exn
  | get_exn _ = NONE;

fun capture0 f x = Res (f x) handle e => Exn e;

fun release (Res y) = y
  | release (Exn e) = reraise e;

fun map_res f (Res x) = Res (f x)
  | map_res f (Exn e) = Exn e;

fun maps_res f = (fn Res x => x | Exn e => Exn e) o map_res f;

fun map_exn f (Res x) = Res x
  | map_exn f (Exn e) = Exn (f e);


(* interrupts *)

fun cause (IO.Io {cause = exn, ...}) = cause exn
  | cause exn = exn;

exception Interrupt_Break;
exception Interrupt_Breakdown;

fun is_interrupt_raw exn = (case cause exn of Thread.Thread.Interrupt => true | _ => false);
fun is_interrupt_break exn = (case cause exn of Interrupt_Break => true | _ => false);
fun is_interrupt_breakdown exn = (case cause exn of Interrupt_Breakdown => true | _ => false);
fun is_interrupt_proper exn = is_interrupt_raw exn orelse is_interrupt_break exn;
fun is_interrupt exn = is_interrupt_proper exn orelse is_interrupt_breakdown exn;

fun is_interrupt_proper_exn (Exn exn) = is_interrupt_proper exn
  | is_interrupt_proper_exn _ = false;

fun is_interrupt_exn (Exn exn) = is_interrupt exn
  | is_interrupt_exn _ = false;

fun result f x =
  Res (f x) handle e => if is_interrupt e then reraise e else Exn e;

fun failure_rc exn = if is_interrupt exn then 130 else 2;


(* concatenated exceptions *)

exception EXCEPTIONS of exn list;


(* low-level trace *)

fun trace exn_message output e =
  PolyML.Exception.traceException
    (e, fn (trace, exn) =>
      let
        val title = "Exception trace - " ^ exn_message exn;
        val () = output (String.concatWith "\n" (title :: trace));
      in reraise exn end);

end;

(*  Title:      Pure/RAW/exn.ML
    Author:     Makarius

Support for exceptions.
*)

signature BASIC_EXN =
sig
  exception ERROR of string
  val error: string -> 'a
  val cat_error: string -> string -> 'a
end;

signature EXN =
sig
  include BASIC_EXN
  datatype 'a result = Res of 'a | Exn of exn
  val get_res: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a
  val map_res: ('a -> 'b) -> 'a result -> 'b result
  val maps_res: ('a -> 'b result) -> 'a result -> 'b result
  val map_exn: (exn -> exn) -> 'a result -> 'a result
  exception Interrupt
  val interrupt: unit -> 'a
  val is_interrupt: exn -> bool
  val interrupt_exn: 'a result
  val is_interrupt_exn: 'a result -> bool
  val interruptible_capture: ('a -> 'b) -> 'a -> 'b result
  val return_code: exn -> int -> int
  val capture_exit: int -> ('a -> 'b) -> 'a -> 'b
  exception EXCEPTIONS of exn list
end;

structure Exn: EXN =
struct

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

fun get_res (Res x) = SOME x
  | get_res _ = NONE;

fun get_exn (Exn exn) = SOME exn
  | get_exn _ = NONE;

fun capture f x = Res (f x) handle e => Exn e;

fun release (Res y) = y
  | release (Exn e) = reraise e;

fun map_res f (Res x) = Res (f x)
  | map_res f (Exn e) = Exn e;

fun maps_res f = (fn Res x => x | Exn e => Exn e) o map_res f;

fun map_exn f (Res x) = Res x
  | map_exn f (Exn e) = Exn (f e);


(* interrupts *)

exception Interrupt = Interrupt;

fun interrupt () = raise Interrupt;

fun is_interrupt Interrupt = true
  | is_interrupt (IO.Io {cause, ...}) = is_interrupt cause
  | is_interrupt _ = false;

val interrupt_exn = Exn Interrupt;

fun is_interrupt_exn (Exn exn) = is_interrupt exn
  | is_interrupt_exn _ = false;

fun interruptible_capture f x =
  Res (f x) handle e => if is_interrupt e then reraise e else Exn e;


(* POSIX return code *)

fun return_code exn rc =
  if is_interrupt exn then (130: int) else rc;

fun capture_exit rc f x =
  f x handle exn => exit (return_code exn rc);


(* concatenated exceptions *)

exception EXCEPTIONS of exn list;

end;

datatype illegal = Interrupt;

structure Basic_Exn: BASIC_EXN = Exn;
open Basic_Exn;

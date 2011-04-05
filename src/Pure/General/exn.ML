(*  Title:      Pure/General/exn.ML
    Author:     Makarius

Extra support for exceptions.
*)

signature EXN =
sig
  datatype 'a result = Result of 'a | Exn of exn
  val get_result: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a
  val flat_result: 'a result result -> 'a result
  val map_result: ('a -> 'b) -> 'a result -> 'b result
  val maps_result: ('a -> 'b result) -> 'a result -> 'b result
  exception Interrupt
  val interrupt: unit -> 'a
  val is_interrupt: exn -> bool
  val interrupt_exn: 'a result
  val is_interrupt_exn: 'a result -> bool
  val interruptible_capture: ('a -> 'b) -> 'a -> 'b result
  exception EXCEPTIONS of exn list
  val flatten: exn -> exn list
  val flatten_list: exn list -> exn list
  val release_all: 'a result list -> 'a list
  val release_first: 'a result list -> 'a list
end;

structure Exn: EXN =
struct

(* runtime exceptions as values *)

datatype 'a result =
  Result of 'a |
  Exn of exn;

fun get_result (Result x) = SOME x
  | get_result _ = NONE;

fun get_exn (Exn exn) = SOME exn
  | get_exn _ = NONE;

fun capture f x = Result (f x) handle e => Exn e;

fun release (Result y) = y
  | release (Exn e) = reraise e;

fun flat_result (Result x) = x
  | flat_result (Exn e) = Exn e;

fun map_result f (Result x) = Result (f x)
  | map_result f (Exn e) = Exn e;

fun maps_result f = flat_result o map_result f;


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
  Result (f x) handle e => if is_interrupt e then reraise e else Exn e;


(* nested exceptions *)

exception EXCEPTIONS of exn list;

fun flatten (EXCEPTIONS exns) = flatten_list exns
  | flatten exn = if is_interrupt exn then [] else [exn]
and flatten_list exns = List.concat (map flatten exns);

fun release_all results =
  if List.all (fn Result _ => true | _ => false) results
  then map (fn Result x => x) results
  else raise EXCEPTIONS (flatten_list (List.mapPartial get_exn results));

fun release_first results = release_all results
  handle EXCEPTIONS (exn :: _) => reraise exn;

end;

datatype illegal = Interrupt;


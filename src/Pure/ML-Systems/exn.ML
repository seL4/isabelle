(*  Title:      Pure/ML-Systems/exn.ML
    Author:     Makarius

Extra support for exceptions.
*)

signature EXN =
sig
  datatype 'a result = Exn of exn | Result of 'a
  val get_result: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a
  exception Interrupt
  exception EXCEPTIONS of exn list
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


(* interrupt and nested exceptions *)

exception Interrupt = Interrupt;
exception EXCEPTIONS of exn list;

fun plain_exns (Result _) = []
  | plain_exns (Exn Interrupt) = []
  | plain_exns (Exn (EXCEPTIONS exns)) = List.concat (map (plain_exns o Exn) exns)
  | plain_exns (Exn exn) = [exn];


fun release_all results =
  if List.all (fn Result _ => true | _ => false) results
  then map (fn Result x => x) results
  else
    (case List.concat (map plain_exns results) of
      [] => raise Interrupt
    | exns => raise EXCEPTIONS exns);

fun release_first results = release_all results
  handle EXCEPTIONS (exn :: _) => reraise exn;

end;

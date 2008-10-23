(*  Title:      Pure/General/lazy.ML
    ID:         $Id$
    Author:     Florian Haftmann and Makarius, TU Muenchen

Lazy evaluation with memoing.  Concurrency may lead to multiple
attempts of evaluation -- the first result persists.
*)

signature LAZY =
sig
  type 'a T
  val same: 'a T * 'a T -> bool
  val lazy: (unit -> 'a) -> 'a T
  val value: 'a -> 'a T
  val peek: 'a T -> 'a Exn.result option
  val force: 'a T -> 'a
  val map_force: ('a -> 'a) -> 'a T -> 'a T
end

structure Lazy :> LAZY =
struct

(* datatype *)

datatype 'a lazy =
  Lazy of unit -> 'a |
  Result of 'a Exn.result;

type 'a T = 'a lazy ref;

fun same (r1: 'a T, r2) = r1 = r2;

fun lazy e = ref (Lazy e);
fun value x = ref (Result (Exn.Result x));

fun peek r =
  (case ! r of
    Lazy _ => NONE
  | Result res => SOME res);


(* force result *)

fun force r =
  let
    (*potentially concurrent evaluation*)
    val res =
      (case ! r of
        Lazy e => Exn.capture e ()
      | Result res => res);
    (*assign result -- first one persists*)
    val res' = NAMED_CRITICAL "lazy" (fn () =>
      (case ! r of
        Lazy _ => (r := Result res; res)
      | Result res' => res'));
  in Exn.release res' end;

fun map_force f = value o f o force;

end;

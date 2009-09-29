(*  Title:      Pure/General/lazy.ML
    Author:     Florian Haftmann and Makarius, TU Muenchen

Lazy evaluation with memoing.  Concurrency may lead to multiple
attempts of evaluation -- the first result persists.
*)

signature LAZY =
sig
  type 'a lazy
  val same: 'a lazy * 'a lazy -> bool
  val lazy: (unit -> 'a) -> 'a lazy
  val value: 'a -> 'a lazy
  val peek: 'a lazy -> 'a Exn.result option
  val force_result: 'a lazy -> 'a Exn.result
  val force: 'a lazy -> 'a
  val map_force: ('a -> 'a) -> 'a lazy -> 'a lazy
end

structure Lazy :> LAZY =
struct

(* datatype *)

datatype 'a T =
  Lazy of unit -> 'a |
  Result of 'a Exn.result;

type 'a lazy = 'a T Unsynchronized.ref;

fun same (r1: 'a lazy, r2) = r1 = r2;

fun lazy e = Unsynchronized.ref (Lazy e);
fun value x = Unsynchronized.ref (Result (Exn.Result x));

fun peek r =
  (case ! r of
    Lazy _ => NONE
  | Result res => SOME res);


(* force result *)

fun force_result r =
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
  in res' end;

fun force r = Exn.release (force_result r);

fun map_force f = value o f o force;

end;

type 'a lazy = 'a Lazy.lazy;


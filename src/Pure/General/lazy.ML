(*  Title:      Pure/General/lazy.ML
    ID:         $Id$
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
  val force: 'a lazy -> 'a
  val map_force: ('a -> 'a) -> 'a lazy -> 'a lazy
end

structure Lazy :> LAZY =
struct

(* datatype *)

datatype 'a T =
  Lazy of unit -> 'a |
  Result of 'a Exn.result;

type 'a lazy = 'a T ref;

fun same (r1: 'a lazy, r2) = r1 = r2;

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

type 'a lazy = 'a Lazy.lazy;


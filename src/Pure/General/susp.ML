(*  Title:      Pure/General/susp.ML
    ID:         $Id$
    Author:     Sebastian Skalberg, Florian Haftmann and Makarius, TU Muenchen

Delayed evaluation with memoing.  Concurrency may lead to multiple
attempts of evaluation -- the first result persists.
*)

signature SUSP =
sig
  type 'a T
  val same: 'a T * 'a T -> bool
  val delay: (unit -> 'a) -> 'a T
  val value: 'a -> 'a T
  val peek: 'a T -> 'a Exn.result option
  val force: 'a T -> 'a
  val map_force: ('a -> 'a) -> 'a T -> 'a T
end

structure Susp :> SUSP =
struct

(* datatype *)

datatype 'a susp =
  Delay of unit -> 'a |
  Result of 'a Exn.result;

type 'a T = 'a susp ref;

fun same (r1: 'a T, r2) = r1 = r2;

fun delay e = ref (Delay e);
fun value x = ref (Result (Exn.Result x));

fun peek r =
  (case ! r of
    Delay _ => NONE
  | Result res => SOME res);


(* force result *)

fun force r =
  let
    (*potentially concurrent evaluation*)
    val res =
      (case ! r of
        Delay e => Exn.capture e ()
      | Result res => res);
    (*assign result -- first one persists*)
    val res' = NAMED_CRITICAL "susp" (fn () =>
      (case ! r of
        Delay _ => (r := Result res; res)
      | Result res' => res'));
  in Exn.release res' end;

fun map_force f = value o f o force;

end;

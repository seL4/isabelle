(*  Title:      Pure/Concurrent/lazy_sequential.ML
    Author:     Florian Haftmann and Makarius, TU Muenchen

Lazy evaluation with memoing (sequential version).
*)

structure Lazy: LAZY =
struct

(* datatype *)

datatype 'a expr =
  Expr of unit -> 'a |
  Result of 'a Exn.result;

abstype 'a lazy = Lazy of 'a expr Unsynchronized.ref
with

fun peek (Lazy r) =
  (case ! r of
    Expr _ => NONE
  | Result x => SOME x);

fun lazy e = Lazy (Unsynchronized.ref (Expr e));
fun value a = Lazy (Unsynchronized.ref (Result (Exn.Result a)));


(* force result *)

fun force_result (Lazy r) =
  (case ! r of
    Expr e => Exn.capture e ()
  | Result res => res);

fun force r = Exn.release (force_result r);

fun map_force f = value o f o force;

end;
end;

type 'a lazy = 'a Lazy.lazy;


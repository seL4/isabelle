(*  Title:      Pure/Concurrent/lazy.ML
    Author:     Makarius

Lazy evaluation based on futures.
*)

signature LAZY =
sig
  type 'a lazy
  val peek: 'a lazy -> 'a Exn.result option
  val lazy: (unit -> 'a) -> 'a lazy
  val value: 'a -> 'a lazy
  val force_result: 'a lazy -> 'a Exn.result
  val force: 'a lazy -> 'a
end;

structure Lazy: LAZY =
struct

(* datatype *)

datatype 'a expr =
  Expr of unit -> 'a |
  Future of 'a future;

abstype 'a lazy = Lazy of 'a expr Synchronized.var
with

fun peek (Lazy var) =
  (case Synchronized.value var of
    Expr _ => NONE
  | Future x => Future.peek x);

fun lazy e = Lazy (Synchronized.var "lazy" (Expr e));
fun value a = Lazy (Synchronized.var "lazy" (Future (Future.value a)));


(* force result *)

fun force_result (Lazy var) =
  (case peek (Lazy var) of
    SOME res => res
  | NONE =>
      Synchronized.guarded_access var
        (fn Expr e => let val x = Future.fork e in SOME (x, Future x) end
          | Future x => SOME (x, Future x))
      |> Future.join_result);

fun force r = Exn.release (force_result r);

end;
end;

type 'a lazy = 'a Lazy.lazy;


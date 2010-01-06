(*  Title:      Pure/Concurrent/lazy.ML
    Author:     Makarius

Lazy evaluation with memoing of results and regular exceptions.
Parallel version based on futures -- avoids critical or multiple
evaluation, unless interrupted.
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
  Result of 'a;

abstype 'a lazy = Lazy of 'a expr future Synchronized.var
with

fun peek (Lazy var) =
  (case Future.peek (Synchronized.value var) of
    NONE => NONE
  | SOME (Exn.Result (Expr _)) => NONE
  | SOME (Exn.Result (Result x)) => SOME (Exn.Result x)
  | SOME (Exn.Exn exn) => SOME (Exn.Exn exn));

fun lazy e = Lazy (Synchronized.var "lazy" (Future.value (Expr e)));
fun value a = Lazy (Synchronized.var "lazy" (Future.value (Result a)));


(* force result *)

fun fork e =
  let val x = Future.fork (fn () => Result (e ()) handle Exn.Interrupt => Expr e)
  in (x, x) end;

fun force_result (Lazy var) =
  (case peek (Lazy var) of
    SOME res => res
  | NONE =>
      let
        val result =
          Synchronized.change_result var
            (fn x =>
              (case Future.peek x of
                SOME (Exn.Result (Expr e)) => fork e
              | _ => (x, x)))
          |> Future.join_result;
      in
        case result of
          Exn.Result (Expr _) => Exn.Exn Exn.Interrupt
        | Exn.Result (Result x) => Exn.Result x
        | Exn.Exn exn => Exn.Exn exn
      end);

fun force r = Exn.release (force_result r);

end;
end;

type 'a lazy = 'a Lazy.lazy;


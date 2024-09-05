(*  Title:      Pure/Concurrent/lazy.ML
    Author:     Makarius

Lazy evaluation with memoing of results and regular exceptions.
Parallel version based on (passive) futures, to avoid critical or
multiple evaluation (unless interrupted).
*)

signature LAZY =
sig
  type 'a lazy
  val value: 'a -> 'a lazy
  val lazy_name: string -> (unit -> 'a) -> 'a lazy
  val lazy: (unit -> 'a) -> 'a lazy
  val peek: 'a lazy -> 'a Exn.result option
  val is_running: 'a lazy -> bool
  val is_finished: 'a lazy -> bool
  val finished_result: 'a lazy -> 'a Exn.result
  val force_result: {strict: bool} -> 'a lazy -> 'a Exn.result
  val force: 'a lazy -> 'a
  val force_value: 'a lazy -> 'a lazy
  val map: ('a -> 'b) -> 'a lazy -> 'b lazy
  val map_finished: ('a -> 'b) -> 'a lazy -> 'b lazy
  val consolidate: 'a lazy list -> 'a lazy list
  val future: Future.params -> 'a lazy -> 'a future
end;

structure Lazy: LAZY =
struct

(* datatype *)

datatype 'a expr =
  Expr of string * (unit -> 'a) |
  Result of 'a future;

abstype 'a lazy = Value of 'a | Lazy of 'a expr Synchronized.var
with

fun value a = Value a;

fun lazy_name name e = Lazy (Synchronized.var "lazy" (Expr (name, e)));
fun lazy e = lazy_name "lazy" e;

fun peek (Value a) = SOME (Exn.Res a)
  | peek (Lazy var) =
      (case Synchronized.value var of
        Expr _ => NONE
      | Result res => Future.peek res);


(* status *)

fun is_value (Value _) = true
  | is_value (Lazy _) = false;

fun is_running (Value _) = false
  | is_running (Lazy var) =
      (case Synchronized.value var of
        Expr _ => false
      | Result res => not (Future.is_finished res));

fun is_finished_future res =
  Future.is_finished res andalso not (Exn.is_interrupt_proper_exn (Future.join_result res));

fun is_finished (Value _) = true
  | is_finished (Lazy var) =
      (case Synchronized.value var of
        Expr _ => false
      | Result res => is_finished_future res);

fun finished_result (Value a) = Exn.Res a
  | finished_result (Lazy var) =
      let fun fail () = Exn.Exn (Fail "Unfinished lazy") in
        (case Synchronized.value var of
          Expr _ => fail ()
        | Result res => if is_finished_future res then Future.join_result res else fail ())
      end;


(* force result *)

fun force_result _ (Value a) = Exn.Res a
  | force_result {strict} (Lazy var) =
      (case peek (Lazy var) of
        SOME res => res
      | NONE =>
          Thread_Attributes.uninterruptible_body (fn run =>
            let
              val (expr, x) =
                Synchronized.change_result var
                  (fn Expr (name, e) =>
                        let val x = Future.promise_name name I
                        in ((SOME (name, e), x), Result x) end
                    | Result x => ((NONE, x), Result x))
                  handle exn as Fail _ =>
                    (case Synchronized.value var of
                      Expr _ => Exn.reraise exn
                    | Result x => (NONE, x));
            in
              (case expr of
                SOME (name, e) =>
                  let
                    val res0 = Exn.capture_body (run e);
                    val _ = Exn.capture_body (fn () => Future.fulfill_result x res0);
                    val res = Future.get_result x;
                    val _ =
                      if not (Exn.is_interrupt_proper_exn res) then
                        Synchronized.assign var (Result (Future.value_result res))
                      else if strict then
                        Synchronized.assign var
                          (Result (Future.value_result (Exn.Exn (Fail "Interrupt"))))
                      (*semantic race: some other threads might see the same
                        interrupt, until there is a fresh start*)
                      else Synchronized.change var (fn _ => Expr (name, e));
                  in res end
              | NONE => Exn.capture_body (run (fn () => Future.join x)))
            end));

end;

fun force x = Exn.release (force_result {strict = false} x);

fun force_value x = if is_value x then x else value (force x);


(* map *)

fun map f x = lazy_name "Lazy.map" (fn () => f (force x));

fun map_finished f x = if is_finished x then value (f (force x)) else map f x;


(* consolidate in parallel *)

fun consolidate xs =
  let
    val unfinished =
      xs |> map_filter (fn x =>
        if is_finished x then NONE else SOME (fn () => force_result {strict = false} x));
    val _ =
      if Future.relevant unfinished then
        ignore (Future.forked_results {name = "Lazy.consolidate", deps = []} unfinished)
      else List.app (fn e => ignore (e ())) unfinished;
  in xs end;


(* future evaluation *)

fun future params x =
  if is_finished x then Future.value_result (force_result {strict = false} x)
  else (singleton o Future.forks) params (fn () => force x);


(* toplevel pretty printing *)

val _ =
  ML_system_pp (fn depth => fn pretty => fn x =>
    (case peek x of
      NONE => ML_Pretty.str "<lazy>"
    | SOME (Exn.Exn _) => ML_Pretty.str "<failed>"
    | SOME (Exn.Res y) => pretty (y, depth)));

end;

type 'a lazy = 'a Lazy.lazy;

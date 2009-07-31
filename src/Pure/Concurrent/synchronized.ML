(*  Title:      Pure/Concurrent/synchronized.ML
    Author:     Fabian Immler and Makarius

State variables with synchronized access.
*)

signature SYNCHRONIZED =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val peek: 'a var -> 'a
  val value: 'a var -> 'a
  val timed_access: 'a var -> ('a -> Time.time option) -> ('a -> ('b * 'a) option) -> 'b option
  val guarded_access: 'a var -> ('a -> ('b * 'a) option) -> 'b
  val change_result: 'a var -> ('a -> 'b * 'a) -> 'b
  val change: 'a var -> ('a -> 'a) -> unit
end;

structure Synchronized: SYNCHRONIZED =
struct

(* state variables *)

datatype 'a var = Var of
 {name: string,
  lock: Mutex.mutex,
  cond: ConditionVar.conditionVar,
  var: 'a ref};

fun var name x = Var
 {name = name,
  lock = Mutex.mutex (),
  cond = ConditionVar.conditionVar (),
  var = ref x};

fun peek (Var {var, ...}) = ! var;  (*unsynchronized!*)

fun value (Var {name, lock, cond, var}) = SimpleThread.synchronized name lock (fn () => ! var);


(* synchronized access *)

fun timed_access (Var {name, lock, cond, var}) time_limit f =
  SimpleThread.synchronized name lock (fn () =>
    let
      fun try_change () =
        let val x = ! var in
          (case f x of
            SOME (y, x') => (var := x'; SOME y)
          | NONE =>
              if Multithreading.sync_wait (time_limit x) cond lock
              then try_change ()
              else NONE)
        end;
      val res = try_change ();
      val _ = ConditionVar.broadcast cond;
    in res end);

fun guarded_access var f = the (timed_access var (K NONE) f);


(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

end;

(*  Title:      Pure/Concurrent/synchronized.ML
    Author:     Fabian Immler and Makarius

Synchronized variables.
*)

signature SYNCHRONIZED =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val value: 'a var -> 'a
  val assign: 'a var -> 'a -> unit
  val timed_access: 'a var -> ('a -> Time.time option) -> ('a -> ('b * 'a) option) -> 'b option
  val guarded_access: 'a var -> ('a -> ('b * 'a) option) -> 'b
  val change_result: 'a var -> ('a -> 'b * 'a) -> 'b
  val change: 'a var -> ('a -> 'a) -> unit
  type 'a cache
  val cache: (unit -> 'a) -> 'a cache
  val cache_peek: 'a cache -> 'a option
  val cache_eval: 'a cache -> 'a
end;

structure Synchronized: SYNCHRONIZED =
struct

(* state variable *)

datatype 'a state =
    Immutable of 'a
  | Mutable of {lock: Thread.Mutex.mutex, cond: Thread.ConditionVar.conditionVar, content: 'a};

fun init_state x =
  Mutable {lock = Thread.Mutex.mutex (), cond = Thread.ConditionVar.conditionVar (), content = x};

fun immutable_fail name = raise Fail ("Illegal access to immutable value " ^ name);

abstype 'a var = Var of {name: string, state: 'a state Unsynchronized.ref}
with

fun var name x =
  Var {name = name, state = Unsynchronized.ref (init_state x)};

fun value (Var {name, state}) =
  (case ! state of
    Immutable x => x
  | Mutable {lock, ...} =>
      Multithreading.synchronized name lock (fn () =>
        (case ! state of
          Immutable x => x
        | Mutable {content, ...} => content)));

fun assign (Var {name, state}) x =
  (case ! state of
    Immutable _ => immutable_fail name
  | Mutable {lock, cond, ...} =>
      Multithreading.synchronized name lock (fn () =>
        (case ! state of
          Immutable _ => immutable_fail name
        | Mutable _ =>
            Thread_Attributes.uninterruptible_body (fn _ =>
             (state := Immutable x; RunCall.clearMutableBit state;
               Thread.ConditionVar.broadcast cond)))));


(* synchronized access *)

fun timed_access (Var {name, state}) time_limit f =
  (case ! state of
    Immutable _ => immutable_fail name
  | Mutable {lock, cond, ...} =>
      Multithreading.synchronized name lock (fn () =>
        let
          fun try_change () =
            (case ! state of
              Immutable _ => immutable_fail name
            | Mutable {content = x, ...} =>
                (case f x of
                  NONE =>
                    (case Multithreading.sync_wait (time_limit x) cond lock of
                      Exn.Res true => try_change ()
                    | Exn.Res false => NONE
                    | Exn.Exn exn => Exn.reraise exn)
                | SOME (y, x') =>
                    Thread_Attributes.uninterruptible_body (fn _ =>
                      (state := Mutable {lock = lock, cond = cond, content = x'};
                        Thread.ConditionVar.broadcast cond; SOME y))));
        in try_change () end));

fun guarded_access var f = the (timed_access var (fn _ => NONE) f);


(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

end;


(* cached evaluation via weak_ref *)

abstype 'a cache =
  Cache of {expr: unit -> 'a, var: 'a Unsynchronized.weak_ref option var}
with

fun cache expr =
  Cache {expr = expr, var = var "Synchronized.cache" NONE};

fun cache_peek (Cache {var, ...}) =
  Option.mapPartial Unsynchronized.weak_peek (value var);

fun cache_eval (Cache {expr, var}) =
  change_result var (fn state =>
    (case Option.mapPartial Unsynchronized.weak_peek state of
      SOME result => (result, state)
    | NONE =>
        let val result = expr ()
        in (result, SOME (Unsynchronized.weak_ref result)) end));

end;

end;

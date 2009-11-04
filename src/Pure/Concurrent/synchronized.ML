(*  Title:      Pure/Concurrent/synchronized.ML
    Author:     Fabian Immler and Makarius

State variables with synchronized access.
*)

signature SYNCHRONIZED =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val value: 'a var -> 'a
  val timed_access: 'a var -> ('a -> Time.time option) -> ('a -> ('b * 'a) option) -> 'b option
  val guarded_access: 'a var -> ('a -> ('b * 'a) option) -> 'b
  val readonly_access: 'a var -> ('a -> 'b option) -> 'b
  val change_result: 'a var -> ('a -> 'b * 'a) -> 'b
  val change: 'a var -> ('a -> 'a) -> unit
  val assign: 'a var -> ('a -> 'a) -> unit
end;

structure Synchronized: SYNCHRONIZED =
struct

(* state variables *)

datatype 'a var = Var of
 {name: string,
  lock: Mutex.mutex,
  cond: ConditionVar.conditionVar,
  var: 'a Unsynchronized.ref};

fun var name x = Var
 {name = name,
  lock = Mutex.mutex (),
  cond = ConditionVar.conditionVar (),
  var = Unsynchronized.ref x};

fun value (Var {var, ...}) = ! var;


(* synchronized access *)

fun access {time_limit, readonly, finish} (Var {name, lock, cond, var}) f =
  SimpleThread.synchronized name lock (fn () =>
    let
      fun try_change () =
        let val x = ! var in
          (case f x of
            NONE =>
              (case Multithreading.sync_wait NONE (time_limit x) cond lock of
                Exn.Result true => try_change ()
              | Exn.Result false => NONE
              | Exn.Exn exn => reraise exn)
          | SOME (y, x') =>
              if readonly then SOME y
              else
                let
                  val _ = magic_immutability_test var
                    andalso raise Fail ("Attempt to change finished variable " ^ quote name);
                  val _ = var := x';
                  val _ = if finish then magic_immutability_mark var else ();
                in SOME y end)
        end;
      val res = try_change ();
      val _ = ConditionVar.broadcast cond;
    in res end);

fun timed_access var time_limit f =
  access {time_limit = time_limit, readonly = false, finish = false} var f;

fun guarded_access var f = the (timed_access var (K NONE) f);

fun readonly_access var f =
  the (access {time_limit = K NONE, readonly = true, finish = false} var
    (fn x => (case f x of NONE => NONE | SOME y => SOME (y, x))));


(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

fun assign var f =
  the (access {time_limit = K NONE, readonly = false, finish = true} var
    (fn x => SOME ((), f x)));

end;

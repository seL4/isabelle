(*  Title:      Pure/Concurrent/synchronized.ML
    ID:         $Id$
    Author:     Fabian Immler and Makarius

State variables with synchronized access.
*)

signature SYNCHRONIZED =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val guarded_change: ('a -> bool) -> ('a -> Time.time option) ->
    'a var -> (bool -> 'a -> 'b * 'a) -> 'b
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


(* synchronized access *)

fun guarded_change guard time_limit (Var {name, lock, cond, var}) f =
  SimpleThread.synchronized name lock (fn () =>
    let
      fun check () = guard (! var) orelse
        (case time_limit (! var) of
          NONE => (ConditionVar.wait (cond, lock); check ())
        | SOME t => ConditionVar.waitUntil (cond, lock, t) andalso check ());
      val ok = check ();
      val res = change_result var (f ok);
      val _ = ConditionVar.broadcast cond;
    in res end);

fun change_result var f = guarded_change (K true) (K NONE) var (K f);
fun change var f = change_result var (fn x => ((), f x));

end;

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
  val cache_eval: {persistent: bool} -> 'a cache -> 'a
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

fun timed_access (Var {name, state}) until body =
  (case ! state of
    Immutable _ => immutable_fail name
  | Mutable {lock, cond, ...} =>
      Multithreading.synchronized name lock (fn () =>
        let
          fun check x =
            (case body x of
              NONE => NONE
            | SOME (y, x') =>
                Thread_Attributes.uninterruptible_body (fn _ =>
                 (state := Mutable {lock = lock, cond = cond, content = x'};
                  Thread.ConditionVar.broadcast cond;
                  SOME y)));
          fun min_limit x a =
            let val b = until x in
              if is_none b then a
              else if is_none a then b
              else if the a <= the b then a
              else b
            end;
          fun wait_until limit =
            ignore (Exn.release (Multithreading.sync_wait limit cond lock));
          fun loop limit0 =
            let
              val x =
                (case ! state of
                  Immutable _ => immutable_fail name
                | Mutable {content, ...} => content);
            in
              (case check x of
                NONE =>
                  let
                    val limit = min_limit x limit0;
                    val expired = (case limit of SOME t => Time.now () >= t | NONE => false);
                  in if expired then NONE else (wait_until limit; loop limit) end
              | some => some)
            end;
        in loop NONE end));

fun guarded_access var body = the (timed_access var (fn _ => NONE) body);


(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

end;


(* cached evaluation via weak_ref *)

local

datatype 'a cache_state =
    Undef
  | Value of 'a
  | Weak_Ref of 'a Unsynchronized.weak_ref;

fun peek Undef = NONE
  | peek (Value x) = SOME x
  | peek (Weak_Ref r) = Unsynchronized.weak_peek r;

fun weak_active (Weak_Ref r) = Unsynchronized.weak_active r
  | weak_active _ = false;

in

abstype 'a cache =
  Cache of {expr: unit -> 'a, var: 'a cache_state var}
with

fun cache expr =
  Cache {expr = expr, var = var "Synchronized.cache" Undef};

fun cache_peek (Cache {var, ...}) = peek (value var);

fun cache_eval {persistent} (Cache {expr, var}) =
  change_result var (fn state =>
    let
      val result =
        (case peek state of
          SOME result => result
        | NONE => expr ());
      val state' =
        if persistent then Value result
        else if weak_active state then state
        else Weak_Ref (Unsynchronized.weak_ref result);
    in (result, state') end);

end;

end;

end;

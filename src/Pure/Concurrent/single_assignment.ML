(*  Title:      Pure/Concurrent/single_assignment.ML
    Author:     Makarius

Single-assignment variables with locking/signalling.
*)

signature SINGLE_ASSIGNMENT =
sig
  type 'a var
  val var: string -> 'a var
  val peek: 'a var -> 'a option
  val await: 'a var -> 'a
  val assign: 'a var -> 'a -> unit
end;

structure Single_Assignment: SINGLE_ASSIGNMENT =
struct

datatype 'a state =
    Set of 'a
  | Unset of {lock: Mutex.mutex, cond: ConditionVar.conditionVar};

fun init_state () =
  Unset {lock = Mutex.mutex (), cond = ConditionVar.conditionVar ()};

abstype 'a var = Var of {name: string, state: 'a state Unsynchronized.ref}
with

fun var name = Var {name = name, state = Unsynchronized.ref (init_state ())};

fun peek (Var {name, state}) =
  (case ! state of
    Set x => SOME x
  | Unset {lock, ...} =>
      Multithreading.synchronized name lock (fn () =>
        (case ! state of
          Set x => SOME x
        | Unset _ => NONE)));

fun await (Var {name, state}) =
  (case ! state of
    Set x => x
  | Unset {lock, cond} =>
      Multithreading.synchronized name lock (fn () =>
        let
          fun wait () =
            (case ! state of
              Unset _ =>
                (case Multithreading.sync_wait NONE cond lock of
                  Exn.Res _ => wait ()
                | Exn.Exn exn => Exn.reraise exn)
            | Set x => x);
        in wait () end));

fun assign_fail name = raise Fail ("Duplicate assignment to " ^ name);
fun assign (Var {name, state}) x =
  (case ! state of
    Set _ => assign_fail name
  | Unset {lock, cond} =>
      Multithreading.synchronized name lock (fn () =>
        (case ! state of
          Set _ => assign_fail name
        | Unset _ =>
            Thread_Attributes.uninterruptible (fn _ => fn () =>
             (state := Set x; RunCall.clearMutableBit state; ConditionVar.broadcast cond)) ())));

end;

end;

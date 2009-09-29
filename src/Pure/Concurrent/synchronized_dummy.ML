(*  Title:      Pure/Concurrent/synchronized_dummy.ML
    Author:     Makarius

Dummy version of state variables -- plain refs for sequential access.
*)

structure Synchronized: SYNCHRONIZED =
struct

datatype 'a var = Var of 'a Unsynchronized.ref;

fun var _ x = Var (Unsynchronized.ref x);
fun value (Var var) = ! var;

fun timed_access (Var var) _ f =
  (case f (! var) of
    SOME (y, x') => (var := x'; SOME y)
  | NONE => Thread.unavailable ());

fun guarded_access var f = the (timed_access var (K NONE) f);

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

end;

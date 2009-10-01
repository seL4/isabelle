(*  Title:      Pure/ML-Systems/unsynchronized.ML
    Author:     Makarius

Raw ML references as unsynchronized state variables.
*)

structure Unsynchronized =
struct

datatype ref = datatype ref;

val op := = op :=;
val ! = !;

fun set flag = (flag := true; true);
fun reset flag = (flag := false; false);
fun toggle flag = (flag := not (! flag); ! flag);

fun change r f = r := f (! r);
fun change_result r f = let val (x, y) = f (! r) in r := y; x end;

fun inc i = (i := ! i + (1: int); ! i);
fun dec i = (i := ! i - (1: int); ! i);

end;

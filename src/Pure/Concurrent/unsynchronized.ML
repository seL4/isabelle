(*  Title:      Pure/Concurrent/unsynchronized.ML
    Author:     Makarius

Raw ML references as unsynchronized state variables.
*)

signature UNSYNCHRONIZED =
sig
  datatype ref = datatype ref
  val := : 'a ref * 'a -> unit
  val ! : 'a ref -> 'a
  val change: 'a ref -> ('a -> 'a) -> unit
  val change_result: 'a ref -> ('a -> 'b * 'a) -> 'b
  val inc: int ref -> int
  val dec: int ref -> int
  val add: int ref -> int -> int
  val setmp: 'a ref -> 'a -> ('b -> 'c) -> 'b -> 'c
  type 'a weak_ref = 'a ref option ref
  val weak_ref: 'a -> 'a weak_ref
  val weak_peek: 'a weak_ref -> 'a option
  val weak_active: 'a weak_ref -> bool
end;

structure Unsynchronized: UNSYNCHRONIZED =
struct

(* regular references *)

datatype ref = datatype ref;

val op := = op :=;
val ! = !;

fun change r f = r := f (! r);
fun change_result r f = let val (x, y) = f (! r) in r := y; x end;

fun inc i = (i := ! i + (1: int); ! i);
fun dec i = (i := ! i - (1: int); ! i);
fun add i n = (i := ! i + (n: int); ! i);

fun setmp flag value f x =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val orig_value = ! flag;
      val _ = flag := value;
      val result = Exn.capture0 (run f) x;
      val _ = flag := orig_value;
    in Exn.release result end);


(* weak references *)

(*see also $POLYML_HOME/src/basis/Weak.sml*)

type 'a weak_ref = 'a ref option ref;

fun weak_ref a = Weak.weak (SOME (ref a));

fun weak_peek (ref (SOME (ref a))) = SOME a
  | weak_peek _ = NONE;

fun weak_active (ref (SOME (ref _))) = true
  | weak_active _ = false;

end;

ML_Name_Space.forget_val "ref";
ML_Name_Space.forget_type "ref";

(*  Title:      Pure/General/array.ML
    Author:     Makarius

Additional operations for structure Array, following Isabelle/ML conventions.
*)

signature ARRAY =
sig
  include ARRAY
  val nth: 'a array -> int -> 'a
  val upd: 'a array -> int -> 'a -> unit
  val forall: ('a -> bool) -> 'a array -> bool
  val member: ('a * 'a -> bool) -> 'a array -> 'a -> bool
  val fold: ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
  val fold_rev: ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
end;

structure Array: ARRAY =
struct

open Array;

fun nth arr i = sub (arr, i);
fun upd arr i x = update (arr, i, x);

val forall = all;

fun member eq arr x = exists (fn y => eq (x, y)) arr;

fun fold f arr x = foldl (fn (a, b) => f a b) x arr;
fun fold_rev f arr x = foldr (fn (a, b) => f a b) x arr;

end;

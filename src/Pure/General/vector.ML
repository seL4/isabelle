(*  Title:      Pure/General/vector.ML
    Author:     Makarius

Additional operations for structure Vector, following Isabelle/ML conventions.
*)

signature VECTOR =
sig
  include VECTOR
  val nth: 'a vector -> int -> 'a
  val forall: ('a -> bool) -> 'a vector -> bool
  val member: ('a * 'a -> bool) -> 'a vector -> 'a -> bool
  val fold: ('a -> 'b -> 'b) -> 'a vector -> 'b -> 'b
  val fold_rev: ('a -> 'b -> 'b) -> 'a vector -> 'b -> 'b
end;

structure Vector: VECTOR =
struct

open Vector;

fun nth vec i = sub (vec, i);

val forall = all;

fun member eq vec x = exists (fn y => eq (x, y)) vec;

fun fold f vec x = foldl (fn (a, b) => f a b) x vec;
fun fold_rev f vec x = foldr (fn (a, b) => f a b) x vec;

end;

(*  Title:      Pure/General/same.ML
    Author:     Makarius

Support for copy-avoiding functions on pure values, at the cost of
readability.
*)

signature SAME =
sig
  exception SAME
  type ('a, 'b) function = 'a -> 'b  (*exception SAME*)
  type 'a operation = ('a, 'a) function  (*exception SAME*)
  val commit: 'a operation -> 'a -> 'a
  val function: ('a -> 'b option) -> ('a, 'b) function
  val capture: ('a, 'b) function -> 'a -> 'b option
  val map: 'a operation -> 'a list operation
end;

structure Same: SAME =
struct

exception SAME;

type ('a, 'b) function = 'a -> 'b;
type 'a operation = ('a, 'a) function;

fun commit f x = f x handle SAME => x;

fun capture f x = SOME (f x) handle SAME => NONE;

fun function f x =
  (case f x of
    NONE => raise SAME
  | SOME y => y);

fun map f [] = raise SAME
  | map f (x :: xs) = (f x :: commit (map f) xs handle SAME => x :: map f xs);

end;

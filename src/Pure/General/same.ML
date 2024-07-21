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
  val same: ('a, 'b) function
  val commit: 'a operation -> 'a -> 'a
  val commit_if: bool -> 'a operation -> 'a -> 'a
  val commit_id: 'a operation -> 'a -> 'a * bool
  val catch: ('a, 'b) function -> 'a -> 'b option
  val compose: 'a operation -> 'a operation -> 'a operation
  val function: ('a -> 'b option) -> ('a, 'b) function
  val function_eq: ('a * 'b -> bool) -> ('a -> 'b) -> ('a, 'b) function
  val map: 'a operation -> 'a list operation
  val map_option: ('a, 'b) function -> ('a option, 'b option) function
end;

structure Same: SAME =
struct

exception SAME;

type ('a, 'b) function = 'a -> 'b;
type 'a operation = ('a, 'a) function;

fun same _ = raise SAME;
fun commit f x = f x handle SAME => x;
fun commit_if b f x = if b then commit f x else f x;
fun commit_id f x = (f x, false) handle SAME => (x, true);

fun catch f x = SOME (f x) handle SAME => NONE;

fun compose g f x =
  (case catch f x of
    NONE => g x
  | SOME y => commit g y);

fun function f x =
  (case f x of
    NONE => raise SAME
  | SOME y => y);

fun function_eq eq f x =
  let val y = f x
  in if eq (x, y) then raise SAME else y end;

fun map f [] = raise SAME
  | map f (x :: xs) = (f x :: commit (map f) xs handle SAME => x :: map f xs);

fun map_option f NONE = raise SAME
  | map_option f (SOME x) = SOME (f x);

end;

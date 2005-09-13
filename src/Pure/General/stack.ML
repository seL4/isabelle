(*  Title:      Pure/General/stack.ML
    ID:         $Id$
    Author:     Makarius

Non-empty stacks.
*)

signature STACK =
sig
  type 'a T = 'a * 'a list
  val level: 'a T -> int
  val init: 'a -> 'a T
  val top: 'a T -> 'a
  val map: ('a -> 'a) -> 'a T -> 'a T
  val push: 'a T -> 'a T
  val pop: 'a T -> 'a T      (*exception Empty*)
end;

structure Stack: STACK =
struct

type 'a T = 'a * 'a list;

fun level (_, xs) = length xs;

fun init x = (x, []);

fun top (x, _) = x;

fun map f (x, xs) = (f x, xs);

fun push (x, xs) = (x, x :: xs);

fun pop (_, x :: xs) = (x, xs)
  | pop (_, []) = raise Empty;

end;

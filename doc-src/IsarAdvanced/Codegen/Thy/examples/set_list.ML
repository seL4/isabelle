structure HOL = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

end; (*struct HOL*)

structure List = 
struct

fun foldr f (x :: xs) a = f x (foldr f xs a)
  | foldr f [] a = a;

fun member A_ x (y :: ys) = HOL.eq A_ x y orelse member A_ x ys
  | member A_ x [] = false;

end; (*struct List*)

structure Set = 
struct

datatype 'a set = Set of 'a list;

val empty : 'a set = Set [];

fun insert x (Set xs) = Set (x :: xs);

fun uniona xs (Set ys) = List.foldr insert ys xs;

fun union (Set xs) = List.foldr uniona xs empty;

fun member A_ x (Set xs) = List.member A_ x xs;

end; (*struct Set*)

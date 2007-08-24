structure HOL = 
struct

type 'a eq = {eqop : 'a -> 'a -> bool};
fun eqop (A_:'a eq) = #eqop A_;

end; (*struct HOL*)

structure List = 
struct

fun foldr f (x :: xs) a = f x (foldr f xs a)
  | foldr f [] a = a;

fun member A_ x (y :: ys) = HOL.eqop A_ x y orelse member A_ x ys
  | member A_ x [] = false;

end; (*struct List*)

structure Set = 
struct

datatype 'a set = Set of 'a list;

val empty : 'a set = Set [];

fun insert x (Set xs) = Set (x :: xs);

fun union xs (Set ys) = List.foldr insert ys xs;

fun member A_ x (Set xs) = List.member A_ x xs;

fun uniona (Set xs) = List.foldr union xs empty;

end; (*struct Set*)

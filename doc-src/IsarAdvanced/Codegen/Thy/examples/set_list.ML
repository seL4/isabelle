structure ROOT = 
struct

structure Code_Generator = 
struct

type 'a eq = {op_eq : 'a -> 'a -> bool};
fun op_eq (A_:'a eq) = #op_eq A_;

end; (*struct Code_Generator*)

structure List = 
struct

fun foldr f (x :: xs) a = f x (foldr f xs a)
  | foldr f [] a = a;

fun memberl A_ x (y :: ys) =
  Code_Generator.op_eq A_ x y orelse memberl A_ x ys
  | memberl A_ x [] = false;

end; (*struct List*)

structure Set = 
struct

datatype 'a set = Set of 'a list;

fun opa A_ x (Set xs) = List.memberl A_ x xs;

val empty : 'a set = Set [];

fun insert x (Set xs) = Set (x :: xs);

fun op_Un xs (Set ys) = List.foldr insert ys xs;

fun union (Set xs) = List.foldr op_Un xs empty;

end; (*struct Set*)

end; (*struct ROOT*)

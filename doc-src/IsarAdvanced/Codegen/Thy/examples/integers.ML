structure ROOT = 
struct

structure Integer = 
struct

datatype bit = B0 | B1;

datatype int = Pls | Min | Bit of int * bit | Number_of_int of int;

fun pred (Bit (k, B0)) = Bit (pred k, B1)
  | pred (Bit (k, B1)) = Bit (k, B0)
  | pred Min = Bit (Min, B0)
  | pred Pls = Min;

fun succ (Bit (k, B0)) = Bit (k, B1)
  | succ (Bit (k, B1)) = Bit (succ k, B0)
  | succ Min = Pls
  | succ Pls = Bit (Pls, B1);

fun plus_int (Number_of_int v) (Number_of_int w) =
  Number_of_int (plus_int v w)
  | plus_int k Min = pred k
  | plus_int k Pls = k
  | plus_int (Bit (k, B1)) (Bit (l, B1)) = Bit (plus_int k (succ l), B0)
  | plus_int (Bit (k, B1)) (Bit (l, B0)) = Bit (plus_int k l, B1)
  | plus_int (Bit (k, B0)) (Bit (l, b)) = Bit (plus_int k l, b)
  | plus_int Min k = pred k
  | plus_int Pls k = k;

fun uminus_int (Number_of_int w) = Number_of_int (uminus_int w)
  | uminus_int (Bit (k, B0)) = Bit (uminus_int k, B0)
  | uminus_int (Bit (k, B1)) = Bit (pred (uminus_int k), B1)
  | uminus_int Min = Bit (Pls, B1)
  | uminus_int Pls = Pls;

fun times_int (Number_of_int v) (Number_of_int w) =
  Number_of_int (times_int v w)
  | times_int (Bit (k, B0)) l = Bit (times_int k l, B0)
  | times_int (Bit (k, B1)) l = plus_int (Bit (times_int k l, B0)) l
  | times_int Min k = uminus_int k
  | times_int Pls w = Pls;

end; (*struct Integer*)

structure Codegen = 
struct

fun double_inc k =
  Integer.plus_int
    (Integer.times_int
      (Integer.Number_of_int
        (Integer.Bit (Integer.Bit (Integer.Pls, Integer.B1), Integer.B0)))
      k)
    (Integer.Number_of_int (Integer.Bit (Integer.Pls, Integer.B1)));

end; (*struct Codegen*)

end; (*struct ROOT*)

structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

end; (*struct Nat*)

structure Integer = 
struct

datatype bit = B0 | B1;

datatype int = Pls | Min | Bit of int * bit | Number_of_int of int;

fun pred (Bit (k, B0)) = Bit (pred k, B1)
  | pred (Bit (k, B1)) = Bit (k, B0)
  | pred Min = Bit (Min, B0)
  | pred Pls = Min;

fun uminus_int (Number_of_int w) = Number_of_int (uminus_int w)
  | uminus_int (Bit (k, B0)) = Bit (uminus_int k, B0)
  | uminus_int (Bit (k, B1)) = Bit (pred (uminus_int k), B1)
  | uminus_int Min = Bit (Pls, B1)
  | uminus_int Pls = Pls;

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

fun minus_int (Number_of_int v) (Number_of_int w) =
  Number_of_int (plus_int v (uminus_int w))
  | minus_int z w = plus_int z (uminus_int w);

fun less_eq_int (Number_of_int k) (Number_of_int l) = less_eq_int k l
  | less_eq_int (Bit (k1, B1)) (Bit (k2, B0)) = less_int k1 k2
  | less_eq_int (Bit (k1, v)) (Bit (k2, B1)) = less_eq_int k1 k2
  | less_eq_int (Bit (k1, B0)) (Bit (k2, v)) = less_eq_int k1 k2
  | less_eq_int (Bit (k, v)) Min = less_eq_int k Min
  | less_eq_int (Bit (k, B1)) Pls = less_int k Pls
  | less_eq_int (Bit (k, B0)) Pls = less_eq_int k Pls
  | less_eq_int Min (Bit (k, B1)) = less_eq_int Min k
  | less_eq_int Min (Bit (k, B0)) = less_int Min k
  | less_eq_int Min Min = true
  | less_eq_int Min Pls = true
  | less_eq_int Pls (Bit (k, v)) = less_eq_int Pls k
  | less_eq_int Pls Min = false
  | less_eq_int Pls Pls = true
and less_int (Number_of_int k) (Number_of_int l) = less_int k l
  | less_int (Bit (k1, B0)) (Bit (k2, B1)) = less_eq_int k1 k2
  | less_int (Bit (k1, B1)) (Bit (k2, v)) = less_int k1 k2
  | less_int (Bit (k1, v)) (Bit (k2, B0)) = less_int k1 k2
  | less_int (Bit (k, B1)) Min = less_int k Min
  | less_int (Bit (k, B0)) Min = less_eq_int k Min
  | less_int (Bit (k, v)) Pls = less_int k Pls
  | less_int Min (Bit (k, v)) = less_int Min k
  | less_int Min Min = false
  | less_int Min Pls = true
  | less_int Pls (Bit (k, B1)) = less_eq_int Pls k
  | less_int Pls (Bit (k, B0)) = less_int Pls k
  | less_int Pls Min = false
  | less_int Pls Pls = false;

fun nat_aux n i =
  (if less_eq_int i (Number_of_int Pls) then n
    else nat_aux (Nat.Suc n)
           (minus_int i (Number_of_int (Bit (Pls, B1)))));

fun nat i = nat_aux Nat.Zero_nat i;

end; (*struct Integer*)

structure Codegen = 
struct

val dummy_set : (Nat.nat -> Nat.nat) list = Nat.Suc :: [];

val foobar_set : Nat.nat list =
  Nat.Zero_nat ::
    (Nat.Suc Nat.Zero_nat ::
      (Integer.nat
         (Integer.Number_of_int
           (Integer.Bit
             (Integer.Bit (Integer.Pls, Integer.B1), Integer.B0)))
        :: []));

end; (*struct Codegen*)

end; (*struct ROOT*)

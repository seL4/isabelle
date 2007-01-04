structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat (Suc m) n = Suc (plus_nat m n);

fun times_nat (Suc m) n = plus_nat n (times_nat m n);

end; (*struct Nat*)

structure Codegen = 
struct

fun fac n =
  (case n of Nat.Zero_nat => Nat.Suc Nat.Zero_nat
     | Nat.Suc m => Nat.times_nat n (fac m))
  | fac (Nat.Suc n) = Nat.times_nat (Nat.Suc n) (fac n);

end; (*struct Codegen*)

end; (*struct ROOT*)

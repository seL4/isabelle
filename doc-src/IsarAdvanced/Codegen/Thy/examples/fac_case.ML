structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun nat_case f1 f2 Zero_nat = f1
  | nat_case f1 f2 (Suc nat) = f2 nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

fun times_nat (Suc m) n = plus_nat n (times_nat m n)
  | times_nat Zero_nat n = Zero_nat;

end; (*struct Nat*)

structure Codegen = 
struct

fun fac n =
  (case n of Nat.Zero_nat => Nat.Suc Nat.Zero_nat
     | Nat.Suc m => Nat.times_nat n (fac m));

end; (*struct Codegen*)

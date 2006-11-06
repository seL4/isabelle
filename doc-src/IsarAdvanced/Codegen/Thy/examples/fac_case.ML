structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat y = y;

fun times_nat (Suc m) n = plus_nat n (times_nat m n)
  | times_nat Zero_nat n = Zero_nat;

end; (*struct Nat*)

structure Codegen = 
struct

fun fac n =
  (case n of Nat.Zero_nat => Nat.Suc Nat.Zero_nat
     | Nat.Suc ma => Nat.times_nat n (fac ma));

end; (*struct Codegen*)

end; (*struct ROOT*)

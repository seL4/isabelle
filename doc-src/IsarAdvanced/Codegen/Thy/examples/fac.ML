structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

val one_nat : nat = Suc Zero_nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

fun times_nat (Suc m) n = plus_nat n (times_nat m n)
  | times_nat Zero_nat n = Zero_nat;

end; (*struct Nat*)

structure Codegen = 
struct

fun fac (Nat.Suc n) = Nat.times_nat (Nat.Suc n) (fac n)
  | fac Nat.Zero_nat = Nat.one_nat;

end; (*struct Codegen*)

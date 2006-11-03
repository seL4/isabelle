structure ROOT = 
struct

structure IntDef = 
struct

datatype nat = Zero_nat | Succ_nat of nat;

fun plus_nat (Succ_nat m) n = plus_nat m (Succ_nat n)
  | plus_nat Zero_nat y = y;

fun times_nat (Succ_nat m) n = plus_nat n (times_nat m n)
  | times_nat Zero_nat na = Zero_nat;

end; (*struct IntDef*)

structure Codegen = 
struct

fun fac n =
  (case n of IntDef.Zero_nat => IntDef.Succ_nat IntDef.Zero_nat
     | IntDef.Succ_nat ma => IntDef.times_nat n (fac ma));

end; (*struct Codegen*)

end; (*struct ROOT*)

structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun less_nat Zero_nat (Suc n) = true;

fun minus_nat (Suc m) (Suc n) = minus_nat m n;

end; (*struct Nat*)

structure Codegen = 
struct

fun pick ((k, v) :: xs) n =
  (if Nat.less_nat n k then v else pick xs (Nat.minus_nat n k));

end; (*struct Codegen*)

end; (*struct ROOT*)

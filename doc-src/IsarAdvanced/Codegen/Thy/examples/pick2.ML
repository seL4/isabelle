structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false
and less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true;

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

end; (*struct Nat*)

structure Codegen = 
struct

fun pick ((k, v) :: xs) n =
  (if Nat.less_nat n k then v else pick xs (Nat.minus_nat n k));

end; (*struct Codegen*)

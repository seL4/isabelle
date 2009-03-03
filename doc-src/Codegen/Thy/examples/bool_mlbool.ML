structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false
and less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true;

end; (*struct Nat*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  (Nat.less_eq_nat k n) andalso (Nat.less_eq_nat n l);

end; (*struct Codegen*)

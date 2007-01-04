structure ROOT = 
struct

structure HOL = 
struct

fun nota false = true;

end; (*struct HOL*)

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun less_nat Zero_nat (Suc n) = true;

fun less_eq_nat m n = HOL.nota (less_nat n m);

end; (*struct Nat*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  (Nat.less_eq_nat k n) andalso (Nat.less_eq_nat n l)
  | in_interval (k, l) n =
    (Nat.less_eq_nat k n) andalso (Nat.less_eq_nat n l);

end; (*struct Codegen*)

end; (*struct ROOT*)

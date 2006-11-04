structure ROOT = 
struct

structure HOL = 
struct

fun nota false = true
  | nota true = false;

end; (*struct HOL*)

structure IntDef = 
struct

datatype nat = Zero_nat | Succ_nat of nat;

fun less_nat Zero_nat (Succ_nat n) = true
  | less_nat n Zero_nat = false
  | less_nat (Succ_nat m) (Succ_nat n) = less_nat m n;

fun less_eq_nat m n = HOL.nota (less_nat n m);

end; (*struct IntDef*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  IntDef.less_eq_nat k n andalso IntDef.less_eq_nat n l;

end; (*struct Codegen*)

end; (*struct ROOT*)

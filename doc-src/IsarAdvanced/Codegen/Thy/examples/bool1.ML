structure ROOT = 
struct

structure HOL = 
struct

datatype boola = True | False;

fun nota False = True
  | nota True = False;

fun op_conj y True = y
  | op_conj x False = False
  | op_conj True y = y
  | op_conj False x = False;

end; (*struct HOL*)

structure IntDef = 
struct

datatype nat = Zero_nat | Succ_nat of nat;

fun less_nat Zero_nat (Succ_nat n) = HOL.True
  | less_nat n Zero_nat = HOL.False
  | less_nat (Succ_nat m) (Succ_nat n) = less_nat m n;

fun less_eq_nat m n = HOL.nota (less_nat n m);

end; (*struct IntDef*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  HOL.op_conj (IntDef.less_eq_nat k n) (IntDef.less_eq_nat n l);

end; (*struct Codegen*)

end; (*struct ROOT*)

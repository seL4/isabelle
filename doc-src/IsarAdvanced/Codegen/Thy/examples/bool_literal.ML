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

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun less_nat Zero_nat (Suc n) = HOL.True
  | less_nat n Zero_nat = HOL.False
  | less_nat (Suc m) (Suc n) = less_nat m n;

fun less_eq_nat m n = HOL.nota (less_nat n m);

end; (*struct Nat*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  HOL.op_conj (Nat.less_eq_nat k n) (Nat.less_eq_nat n l);

end; (*struct Codegen*)

end; (*struct ROOT*)

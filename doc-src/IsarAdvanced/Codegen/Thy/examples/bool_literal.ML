structure HOL = 
struct

datatype boola = False | True;

fun anda x True = x
  | anda x False = False
  | anda True x = x
  | anda False x = False;

end; (*struct HOL*)

structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = HOL.False
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = HOL.True;

end; (*struct Nat*)

structure Codegen = 
struct

fun in_interval (k, l) n =
  HOL.anda (Nat.less_eq_nat k n) (Nat.less_eq_nat n l);

end; (*struct Codegen*)

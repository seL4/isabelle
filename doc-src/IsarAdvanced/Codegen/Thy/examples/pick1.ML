structure HOL = 
struct

fun leta s f = f s;

end; (*struct HOL*)

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = false
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = true;

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

fun prod_case f1 (a, b) = f1 a b;

end; (*struct Nat*)

structure Codegen = 
struct

fun pick ((k, v) :: xs) n =
  (if Nat.less_nat n k then v else pick xs (Nat.minus_nat n k))
  | pick (x :: xs) n =
    let
      val (k, v) = x;
    in
      (if Nat.less_nat n k then v else pick xs (Nat.minus_nat n k))
    end;

end; (*struct Codegen*)

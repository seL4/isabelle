structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun less_nat Zero_nat (Suc n) = true
  | less_nat n Zero_nat = false
  | less_nat (Suc m) (Suc n) = less_nat m n;

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat y Zero_nat = y;

end; (*struct Nat*)

structure Codegen = 
struct

fun pick ((k, v) :: xs) n =
  (if Nat.less_nat n k then v else pick xs (Nat.minus_nat n k))
  | pick (x :: xs) n =
    let
      val (ka, va) = x;
    in
      (if Nat.less_nat n ka then va else pick xs (Nat.minus_nat n ka))
    end;

end; (*struct Codegen*)

end; (*struct ROOT*)

structure ROOT = 
struct

structure IntDef = 
struct

datatype nat = Zero_nat | Succ_nat of nat;

fun less_nat Zero_nat (Succ_nat n) = true
  | less_nat n Zero_nat = false
  | less_nat (Succ_nat m) (Succ_nat n) = less_nat m n;

fun minus_nat (Succ_nat m) (Succ_nat n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat y Zero_nat = y;

end; (*struct IntDef*)

structure Codegen = 
struct

fun pick ((k, v) :: xs) n =
  (if IntDef.less_nat n k then v else pick xs (IntDef.minus_nat n k))
  | pick (x :: xs) n =
    let
      val (ka, va) = x;
    in
      (if IntDef.less_nat n ka then va else pick xs (IntDef.minus_nat n ka))
    end;

end; (*struct Codegen*)

end; (*struct ROOT*)

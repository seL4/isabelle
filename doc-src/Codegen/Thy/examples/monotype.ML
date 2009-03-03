structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun eq_nat (Suc a) Zero_nat = false
  | eq_nat Zero_nat (Suc a) = false
  | eq_nat (Suc nat) (Suc nat') = eq_nat nat nat'
  | eq_nat Zero_nat Zero_nat = true;

end; (*struct Nat*)

structure List = 
struct

fun null (x :: xs) = false
  | null [] = true;

fun list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys
  | list_all2 p xs [] = null xs
  | list_all2 p [] ys = null ys;

end; (*struct List*)

structure Codegen = 
struct

datatype monotype = Mono of Nat.nat * monotype list;

fun eq_monotype (Mono (tyco1, typargs1)) (Mono (tyco2, typargs2)) =
  Nat.eq_nat tyco1 tyco2 andalso
    List.list_all2 eq_monotype typargs1 typargs2;

end; (*struct Codegen*)

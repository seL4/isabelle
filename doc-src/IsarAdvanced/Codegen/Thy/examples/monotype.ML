structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun eqop_nat Zero_nat (Suc m) = false
  | eqop_nat (Suc n) Zero_nat = false
  | eqop_nat (Suc n) (Suc m) = eqop_nat n m
  | eqop_nat Zero_nat Zero_nat = true;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

fun prod_case f1 (a, b) = f1 a b;

end; (*struct Nat*)

structure List = 
struct

fun list_case f1 f2 [] = f1
  | list_case f1 f2 (a :: lista) = f2 a lista;

fun zip xs (y :: ys) =
  (case xs of [] => [] | z :: zs => (z, y) :: zip zs ys)
  | zip xs [] = [];

fun null (x :: xs) = false
  | null [] = true;

fun list_all p (x :: xs) = p x andalso list_all p xs
  | list_all p [] = true;

fun size_list (a :: lista) =
  Nat.plus_nat (size_list lista) (Nat.Suc Nat.Zero_nat)
  | size_list [] = Nat.Zero_nat;

fun list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys
  | list_all2 p xs [] = null xs
  | list_all2 p [] ys = null ys
  | list_all2 p xs ys =
    Nat.eqop_nat (size_list xs) (size_list ys) andalso
      list_all (fn a as (aa, b) => p aa b) (zip xs ys);

end; (*struct List*)

structure Codegen = 
struct

datatype monotype = Mono of Nat.nat * monotype list;

fun eqop_monotype (Mono (tyco1, typargs1)) (Mono (tyco2, typargs2)) =
  Nat.eqop_nat tyco1 tyco2 andalso
    List.list_all2 eqop_monotype typargs1 typargs2;

end; (*struct Codegen*)

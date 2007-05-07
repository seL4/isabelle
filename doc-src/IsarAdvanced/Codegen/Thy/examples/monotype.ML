structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

fun op_eq_nat Zero_nat (Suc m) = false
  | op_eq_nat (Suc n) Zero_nat = false
  | op_eq_nat (Suc n) (Suc m) = op_eq_nat n m
  | op_eq_nat Zero_nat Zero_nat = true;

end; (*struct Nat*)

structure Code_Generator = 
struct

type 'a eq = {op_eq : 'a -> 'a -> bool};
fun op_eq (A_:'a eq) = #op_eq A_;

end; (*struct Code_Generator*)

structure List = 
struct

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 |
  Nibble5 | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB |
  NibbleC | NibbleD | NibbleE | NibbleF;

datatype char = Char of nibble * nibble;

fun zip xs (y :: ys) =
  (case xs of [] => [] | z :: zs => (z, y) :: zip zs ys)
  | zip xs [] = [];

fun null (x :: xs) = false
  | null [] = true;

fun op_eq_nibble Nibble0 Nibble0 = true
  | op_eq_nibble Nibble1 Nibble1 = true
  | op_eq_nibble Nibble2 Nibble2 = true
  | op_eq_nibble Nibble3 Nibble3 = true
  | op_eq_nibble Nibble4 Nibble4 = true
  | op_eq_nibble Nibble5 Nibble5 = true
  | op_eq_nibble Nibble6 Nibble6 = true
  | op_eq_nibble Nibble7 Nibble7 = true
  | op_eq_nibble Nibble8 Nibble8 = true
  | op_eq_nibble Nibble9 Nibble9 = true
  | op_eq_nibble NibbleA NibbleA = true
  | op_eq_nibble NibbleB NibbleB = true
  | op_eq_nibble NibbleC NibbleC = true
  | op_eq_nibble NibbleD NibbleD = true
  | op_eq_nibble NibbleE NibbleE = true
  | op_eq_nibble NibbleF NibbleF = true
  | op_eq_nibble Nibble0 Nibble1 = false
  | op_eq_nibble Nibble0 Nibble2 = false
  | op_eq_nibble Nibble0 Nibble3 = false
  | op_eq_nibble Nibble0 Nibble4 = false
  | op_eq_nibble Nibble0 Nibble5 = false
  | op_eq_nibble Nibble0 Nibble6 = false
  | op_eq_nibble Nibble0 Nibble7 = false
  | op_eq_nibble Nibble0 Nibble8 = false
  | op_eq_nibble Nibble0 Nibble9 = false
  | op_eq_nibble Nibble0 NibbleA = false
  | op_eq_nibble Nibble0 NibbleB = false
  | op_eq_nibble Nibble0 NibbleC = false
  | op_eq_nibble Nibble0 NibbleD = false
  | op_eq_nibble Nibble0 NibbleE = false
  | op_eq_nibble Nibble0 NibbleF = false
  | op_eq_nibble Nibble1 Nibble2 = false
  | op_eq_nibble Nibble1 Nibble3 = false
  | op_eq_nibble Nibble1 Nibble4 = false
  | op_eq_nibble Nibble1 Nibble5 = false
  | op_eq_nibble Nibble1 Nibble6 = false
  | op_eq_nibble Nibble1 Nibble7 = false
  | op_eq_nibble Nibble1 Nibble8 = false
  | op_eq_nibble Nibble1 Nibble9 = false
  | op_eq_nibble Nibble1 NibbleA = false
  | op_eq_nibble Nibble1 NibbleB = false
  | op_eq_nibble Nibble1 NibbleC = false
  | op_eq_nibble Nibble1 NibbleD = false
  | op_eq_nibble Nibble1 NibbleE = false
  | op_eq_nibble Nibble1 NibbleF = false
  | op_eq_nibble Nibble2 Nibble3 = false
  | op_eq_nibble Nibble2 Nibble4 = false
  | op_eq_nibble Nibble2 Nibble5 = false
  | op_eq_nibble Nibble2 Nibble6 = false
  | op_eq_nibble Nibble2 Nibble7 = false
  | op_eq_nibble Nibble2 Nibble8 = false
  | op_eq_nibble Nibble2 Nibble9 = false
  | op_eq_nibble Nibble2 NibbleA = false
  | op_eq_nibble Nibble2 NibbleB = false
  | op_eq_nibble Nibble2 NibbleC = false
  | op_eq_nibble Nibble2 NibbleD = false
  | op_eq_nibble Nibble2 NibbleE = false
  | op_eq_nibble Nibble2 NibbleF = false
  | op_eq_nibble Nibble3 Nibble4 = false
  | op_eq_nibble Nibble3 Nibble5 = false
  | op_eq_nibble Nibble3 Nibble6 = false
  | op_eq_nibble Nibble3 Nibble7 = false
  | op_eq_nibble Nibble3 Nibble8 = false
  | op_eq_nibble Nibble3 Nibble9 = false
  | op_eq_nibble Nibble3 NibbleA = false
  | op_eq_nibble Nibble3 NibbleB = false
  | op_eq_nibble Nibble3 NibbleC = false
  | op_eq_nibble Nibble3 NibbleD = false
  | op_eq_nibble Nibble3 NibbleE = false
  | op_eq_nibble Nibble3 NibbleF = false
  | op_eq_nibble Nibble4 Nibble5 = false
  | op_eq_nibble Nibble4 Nibble6 = false
  | op_eq_nibble Nibble4 Nibble7 = false
  | op_eq_nibble Nibble4 Nibble8 = false
  | op_eq_nibble Nibble4 Nibble9 = false
  | op_eq_nibble Nibble4 NibbleA = false
  | op_eq_nibble Nibble4 NibbleB = false
  | op_eq_nibble Nibble4 NibbleC = false
  | op_eq_nibble Nibble4 NibbleD = false
  | op_eq_nibble Nibble4 NibbleE = false
  | op_eq_nibble Nibble4 NibbleF = false
  | op_eq_nibble Nibble5 Nibble6 = false
  | op_eq_nibble Nibble5 Nibble7 = false
  | op_eq_nibble Nibble5 Nibble8 = false
  | op_eq_nibble Nibble5 Nibble9 = false
  | op_eq_nibble Nibble5 NibbleA = false
  | op_eq_nibble Nibble5 NibbleB = false
  | op_eq_nibble Nibble5 NibbleC = false
  | op_eq_nibble Nibble5 NibbleD = false
  | op_eq_nibble Nibble5 NibbleE = false
  | op_eq_nibble Nibble5 NibbleF = false
  | op_eq_nibble Nibble6 Nibble7 = false
  | op_eq_nibble Nibble6 Nibble8 = false
  | op_eq_nibble Nibble6 Nibble9 = false
  | op_eq_nibble Nibble6 NibbleA = false
  | op_eq_nibble Nibble6 NibbleB = false
  | op_eq_nibble Nibble6 NibbleC = false
  | op_eq_nibble Nibble6 NibbleD = false
  | op_eq_nibble Nibble6 NibbleE = false
  | op_eq_nibble Nibble6 NibbleF = false
  | op_eq_nibble Nibble7 Nibble8 = false
  | op_eq_nibble Nibble7 Nibble9 = false
  | op_eq_nibble Nibble7 NibbleA = false
  | op_eq_nibble Nibble7 NibbleB = false
  | op_eq_nibble Nibble7 NibbleC = false
  | op_eq_nibble Nibble7 NibbleD = false
  | op_eq_nibble Nibble7 NibbleE = false
  | op_eq_nibble Nibble7 NibbleF = false
  | op_eq_nibble Nibble8 Nibble9 = false
  | op_eq_nibble Nibble8 NibbleA = false
  | op_eq_nibble Nibble8 NibbleB = false
  | op_eq_nibble Nibble8 NibbleC = false
  | op_eq_nibble Nibble8 NibbleD = false
  | op_eq_nibble Nibble8 NibbleE = false
  | op_eq_nibble Nibble8 NibbleF = false
  | op_eq_nibble Nibble9 NibbleA = false
  | op_eq_nibble Nibble9 NibbleB = false
  | op_eq_nibble Nibble9 NibbleC = false
  | op_eq_nibble Nibble9 NibbleD = false
  | op_eq_nibble Nibble9 NibbleE = false
  | op_eq_nibble Nibble9 NibbleF = false
  | op_eq_nibble NibbleA NibbleB = false
  | op_eq_nibble NibbleA NibbleC = false
  | op_eq_nibble NibbleA NibbleD = false
  | op_eq_nibble NibbleA NibbleE = false
  | op_eq_nibble NibbleA NibbleF = false
  | op_eq_nibble NibbleB NibbleC = false
  | op_eq_nibble NibbleB NibbleD = false
  | op_eq_nibble NibbleB NibbleE = false
  | op_eq_nibble NibbleB NibbleF = false
  | op_eq_nibble NibbleC NibbleD = false
  | op_eq_nibble NibbleC NibbleE = false
  | op_eq_nibble NibbleC NibbleF = false
  | op_eq_nibble NibbleD NibbleE = false
  | op_eq_nibble NibbleD NibbleF = false
  | op_eq_nibble NibbleE NibbleF = false
  | op_eq_nibble Nibble1 Nibble0 = false
  | op_eq_nibble Nibble2 Nibble0 = false
  | op_eq_nibble Nibble3 Nibble0 = false
  | op_eq_nibble Nibble4 Nibble0 = false
  | op_eq_nibble Nibble5 Nibble0 = false
  | op_eq_nibble Nibble6 Nibble0 = false
  | op_eq_nibble Nibble7 Nibble0 = false
  | op_eq_nibble Nibble8 Nibble0 = false
  | op_eq_nibble Nibble9 Nibble0 = false
  | op_eq_nibble NibbleA Nibble0 = false
  | op_eq_nibble NibbleB Nibble0 = false
  | op_eq_nibble NibbleC Nibble0 = false
  | op_eq_nibble NibbleD Nibble0 = false
  | op_eq_nibble NibbleE Nibble0 = false
  | op_eq_nibble NibbleF Nibble0 = false
  | op_eq_nibble Nibble2 Nibble1 = false
  | op_eq_nibble Nibble3 Nibble1 = false
  | op_eq_nibble Nibble4 Nibble1 = false
  | op_eq_nibble Nibble5 Nibble1 = false
  | op_eq_nibble Nibble6 Nibble1 = false
  | op_eq_nibble Nibble7 Nibble1 = false
  | op_eq_nibble Nibble8 Nibble1 = false
  | op_eq_nibble Nibble9 Nibble1 = false
  | op_eq_nibble NibbleA Nibble1 = false
  | op_eq_nibble NibbleB Nibble1 = false
  | op_eq_nibble NibbleC Nibble1 = false
  | op_eq_nibble NibbleD Nibble1 = false
  | op_eq_nibble NibbleE Nibble1 = false
  | op_eq_nibble NibbleF Nibble1 = false
  | op_eq_nibble Nibble3 Nibble2 = false
  | op_eq_nibble Nibble4 Nibble2 = false
  | op_eq_nibble Nibble5 Nibble2 = false
  | op_eq_nibble Nibble6 Nibble2 = false
  | op_eq_nibble Nibble7 Nibble2 = false
  | op_eq_nibble Nibble8 Nibble2 = false
  | op_eq_nibble Nibble9 Nibble2 = false
  | op_eq_nibble NibbleA Nibble2 = false
  | op_eq_nibble NibbleB Nibble2 = false
  | op_eq_nibble NibbleC Nibble2 = false
  | op_eq_nibble NibbleD Nibble2 = false
  | op_eq_nibble NibbleE Nibble2 = false
  | op_eq_nibble NibbleF Nibble2 = false
  | op_eq_nibble Nibble4 Nibble3 = false
  | op_eq_nibble Nibble5 Nibble3 = false
  | op_eq_nibble Nibble6 Nibble3 = false
  | op_eq_nibble Nibble7 Nibble3 = false
  | op_eq_nibble Nibble8 Nibble3 = false
  | op_eq_nibble Nibble9 Nibble3 = false
  | op_eq_nibble NibbleA Nibble3 = false
  | op_eq_nibble NibbleB Nibble3 = false
  | op_eq_nibble NibbleC Nibble3 = false
  | op_eq_nibble NibbleD Nibble3 = false
  | op_eq_nibble NibbleE Nibble3 = false
  | op_eq_nibble NibbleF Nibble3 = false
  | op_eq_nibble Nibble5 Nibble4 = false
  | op_eq_nibble Nibble6 Nibble4 = false
  | op_eq_nibble Nibble7 Nibble4 = false
  | op_eq_nibble Nibble8 Nibble4 = false
  | op_eq_nibble Nibble9 Nibble4 = false
  | op_eq_nibble NibbleA Nibble4 = false
  | op_eq_nibble NibbleB Nibble4 = false
  | op_eq_nibble NibbleC Nibble4 = false
  | op_eq_nibble NibbleD Nibble4 = false
  | op_eq_nibble NibbleE Nibble4 = false
  | op_eq_nibble NibbleF Nibble4 = false
  | op_eq_nibble Nibble6 Nibble5 = false
  | op_eq_nibble Nibble7 Nibble5 = false
  | op_eq_nibble Nibble8 Nibble5 = false
  | op_eq_nibble Nibble9 Nibble5 = false
  | op_eq_nibble NibbleA Nibble5 = false
  | op_eq_nibble NibbleB Nibble5 = false
  | op_eq_nibble NibbleC Nibble5 = false
  | op_eq_nibble NibbleD Nibble5 = false
  | op_eq_nibble NibbleE Nibble5 = false
  | op_eq_nibble NibbleF Nibble5 = false
  | op_eq_nibble Nibble7 Nibble6 = false
  | op_eq_nibble Nibble8 Nibble6 = false
  | op_eq_nibble Nibble9 Nibble6 = false
  | op_eq_nibble NibbleA Nibble6 = false
  | op_eq_nibble NibbleB Nibble6 = false
  | op_eq_nibble NibbleC Nibble6 = false
  | op_eq_nibble NibbleD Nibble6 = false
  | op_eq_nibble NibbleE Nibble6 = false
  | op_eq_nibble NibbleF Nibble6 = false
  | op_eq_nibble Nibble8 Nibble7 = false
  | op_eq_nibble Nibble9 Nibble7 = false
  | op_eq_nibble NibbleA Nibble7 = false
  | op_eq_nibble NibbleB Nibble7 = false
  | op_eq_nibble NibbleC Nibble7 = false
  | op_eq_nibble NibbleD Nibble7 = false
  | op_eq_nibble NibbleE Nibble7 = false
  | op_eq_nibble NibbleF Nibble7 = false
  | op_eq_nibble Nibble9 Nibble8 = false
  | op_eq_nibble NibbleA Nibble8 = false
  | op_eq_nibble NibbleB Nibble8 = false
  | op_eq_nibble NibbleC Nibble8 = false
  | op_eq_nibble NibbleD Nibble8 = false
  | op_eq_nibble NibbleE Nibble8 = false
  | op_eq_nibble NibbleF Nibble8 = false
  | op_eq_nibble NibbleA Nibble9 = false
  | op_eq_nibble NibbleB Nibble9 = false
  | op_eq_nibble NibbleC Nibble9 = false
  | op_eq_nibble NibbleD Nibble9 = false
  | op_eq_nibble NibbleE Nibble9 = false
  | op_eq_nibble NibbleF Nibble9 = false
  | op_eq_nibble NibbleB NibbleA = false
  | op_eq_nibble NibbleC NibbleA = false
  | op_eq_nibble NibbleD NibbleA = false
  | op_eq_nibble NibbleE NibbleA = false
  | op_eq_nibble NibbleF NibbleA = false
  | op_eq_nibble NibbleC NibbleB = false
  | op_eq_nibble NibbleD NibbleB = false
  | op_eq_nibble NibbleE NibbleB = false
  | op_eq_nibble NibbleF NibbleB = false
  | op_eq_nibble NibbleD NibbleC = false
  | op_eq_nibble NibbleE NibbleC = false
  | op_eq_nibble NibbleF NibbleC = false
  | op_eq_nibble NibbleE NibbleD = false
  | op_eq_nibble NibbleF NibbleD = false
  | op_eq_nibble NibbleF NibbleE = false;

fun op_eq_char (Char (nibble1, nibble2)) (Char (nibble1', nibble2')) =
  op_eq_nibble nibble1 nibble1' andalso op_eq_nibble nibble2 nibble2';

val eq_char = {op_eq = op_eq_char} : char Code_Generator.eq;

fun list_all p (x :: xs) = p x andalso list_all p xs
  | list_all p [] = true;

fun size_list (a :: lista) =
  Nat.plus_nat (size_list lista) (Nat.Suc Nat.Zero_nat)
  | size_list [] = Nat.Zero_nat;

fun list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys
  | list_all2 p xs [] = null xs
  | list_all2 p [] ys = null ys
  | list_all2 p xs ys =
    Nat.op_eq_nat (size_list xs) (size_list ys) andalso
      list_all (fn a as (aa, b) => p aa b) (zip xs ys);

fun op_eq_list A_ [] [] = true
  | op_eq_list A_ (a :: lista) (a' :: list') =
    Code_Generator.op_eq A_ a a' andalso op_eq_list A_ lista list'
  | op_eq_list A_ [] (a :: b) = false
  | op_eq_list A_ (a :: b) [] = false;

end; (*struct List*)

structure Codegen = 
struct

datatype monotype = Mono of List.char list * monotype list;

fun op_eq_monotype (Mono (tyco1, typargs1)) (Mono (tyco2, typargs2)) =
  List.op_eq_list List.eq_char tyco1 tyco2 andalso
    List.list_all2 op_eq_monotype typargs1 typargs2;

end; (*struct Codegen*)

end; (*struct ROOT*)

structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun eq_nat Zero_nat (Suc m) = false
  | eq_nat (Suc n) Zero_nat = false
  | eq_nat (Suc n) (Suc m) = eq_nat n m
  | eq_nat Zero_nat Zero_nat = true;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

end; (*struct Nat*)

structure Code_Generator = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

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

fun eq_nibble Nibble0 Nibble0 = true
  | eq_nibble Nibble1 Nibble1 = true
  | eq_nibble Nibble2 Nibble2 = true
  | eq_nibble Nibble3 Nibble3 = true
  | eq_nibble Nibble4 Nibble4 = true
  | eq_nibble Nibble5 Nibble5 = true
  | eq_nibble Nibble6 Nibble6 = true
  | eq_nibble Nibble7 Nibble7 = true
  | eq_nibble Nibble8 Nibble8 = true
  | eq_nibble Nibble9 Nibble9 = true
  | eq_nibble NibbleA NibbleA = true
  | eq_nibble NibbleB NibbleB = true
  | eq_nibble NibbleC NibbleC = true
  | eq_nibble NibbleD NibbleD = true
  | eq_nibble NibbleE NibbleE = true
  | eq_nibble NibbleF NibbleF = true
  | eq_nibble Nibble0 Nibble1 = false
  | eq_nibble Nibble0 Nibble2 = false
  | eq_nibble Nibble0 Nibble3 = false
  | eq_nibble Nibble0 Nibble4 = false
  | eq_nibble Nibble0 Nibble5 = false
  | eq_nibble Nibble0 Nibble6 = false
  | eq_nibble Nibble0 Nibble7 = false
  | eq_nibble Nibble0 Nibble8 = false
  | eq_nibble Nibble0 Nibble9 = false
  | eq_nibble Nibble0 NibbleA = false
  | eq_nibble Nibble0 NibbleB = false
  | eq_nibble Nibble0 NibbleC = false
  | eq_nibble Nibble0 NibbleD = false
  | eq_nibble Nibble0 NibbleE = false
  | eq_nibble Nibble0 NibbleF = false
  | eq_nibble Nibble1 Nibble2 = false
  | eq_nibble Nibble1 Nibble3 = false
  | eq_nibble Nibble1 Nibble4 = false
  | eq_nibble Nibble1 Nibble5 = false
  | eq_nibble Nibble1 Nibble6 = false
  | eq_nibble Nibble1 Nibble7 = false
  | eq_nibble Nibble1 Nibble8 = false
  | eq_nibble Nibble1 Nibble9 = false
  | eq_nibble Nibble1 NibbleA = false
  | eq_nibble Nibble1 NibbleB = false
  | eq_nibble Nibble1 NibbleC = false
  | eq_nibble Nibble1 NibbleD = false
  | eq_nibble Nibble1 NibbleE = false
  | eq_nibble Nibble1 NibbleF = false
  | eq_nibble Nibble2 Nibble3 = false
  | eq_nibble Nibble2 Nibble4 = false
  | eq_nibble Nibble2 Nibble5 = false
  | eq_nibble Nibble2 Nibble6 = false
  | eq_nibble Nibble2 Nibble7 = false
  | eq_nibble Nibble2 Nibble8 = false
  | eq_nibble Nibble2 Nibble9 = false
  | eq_nibble Nibble2 NibbleA = false
  | eq_nibble Nibble2 NibbleB = false
  | eq_nibble Nibble2 NibbleC = false
  | eq_nibble Nibble2 NibbleD = false
  | eq_nibble Nibble2 NibbleE = false
  | eq_nibble Nibble2 NibbleF = false
  | eq_nibble Nibble3 Nibble4 = false
  | eq_nibble Nibble3 Nibble5 = false
  | eq_nibble Nibble3 Nibble6 = false
  | eq_nibble Nibble3 Nibble7 = false
  | eq_nibble Nibble3 Nibble8 = false
  | eq_nibble Nibble3 Nibble9 = false
  | eq_nibble Nibble3 NibbleA = false
  | eq_nibble Nibble3 NibbleB = false
  | eq_nibble Nibble3 NibbleC = false
  | eq_nibble Nibble3 NibbleD = false
  | eq_nibble Nibble3 NibbleE = false
  | eq_nibble Nibble3 NibbleF = false
  | eq_nibble Nibble4 Nibble5 = false
  | eq_nibble Nibble4 Nibble6 = false
  | eq_nibble Nibble4 Nibble7 = false
  | eq_nibble Nibble4 Nibble8 = false
  | eq_nibble Nibble4 Nibble9 = false
  | eq_nibble Nibble4 NibbleA = false
  | eq_nibble Nibble4 NibbleB = false
  | eq_nibble Nibble4 NibbleC = false
  | eq_nibble Nibble4 NibbleD = false
  | eq_nibble Nibble4 NibbleE = false
  | eq_nibble Nibble4 NibbleF = false
  | eq_nibble Nibble5 Nibble6 = false
  | eq_nibble Nibble5 Nibble7 = false
  | eq_nibble Nibble5 Nibble8 = false
  | eq_nibble Nibble5 Nibble9 = false
  | eq_nibble Nibble5 NibbleA = false
  | eq_nibble Nibble5 NibbleB = false
  | eq_nibble Nibble5 NibbleC = false
  | eq_nibble Nibble5 NibbleD = false
  | eq_nibble Nibble5 NibbleE = false
  | eq_nibble Nibble5 NibbleF = false
  | eq_nibble Nibble6 Nibble7 = false
  | eq_nibble Nibble6 Nibble8 = false
  | eq_nibble Nibble6 Nibble9 = false
  | eq_nibble Nibble6 NibbleA = false
  | eq_nibble Nibble6 NibbleB = false
  | eq_nibble Nibble6 NibbleC = false
  | eq_nibble Nibble6 NibbleD = false
  | eq_nibble Nibble6 NibbleE = false
  | eq_nibble Nibble6 NibbleF = false
  | eq_nibble Nibble7 Nibble8 = false
  | eq_nibble Nibble7 Nibble9 = false
  | eq_nibble Nibble7 NibbleA = false
  | eq_nibble Nibble7 NibbleB = false
  | eq_nibble Nibble7 NibbleC = false
  | eq_nibble Nibble7 NibbleD = false
  | eq_nibble Nibble7 NibbleE = false
  | eq_nibble Nibble7 NibbleF = false
  | eq_nibble Nibble8 Nibble9 = false
  | eq_nibble Nibble8 NibbleA = false
  | eq_nibble Nibble8 NibbleB = false
  | eq_nibble Nibble8 NibbleC = false
  | eq_nibble Nibble8 NibbleD = false
  | eq_nibble Nibble8 NibbleE = false
  | eq_nibble Nibble8 NibbleF = false
  | eq_nibble Nibble9 NibbleA = false
  | eq_nibble Nibble9 NibbleB = false
  | eq_nibble Nibble9 NibbleC = false
  | eq_nibble Nibble9 NibbleD = false
  | eq_nibble Nibble9 NibbleE = false
  | eq_nibble Nibble9 NibbleF = false
  | eq_nibble NibbleA NibbleB = false
  | eq_nibble NibbleA NibbleC = false
  | eq_nibble NibbleA NibbleD = false
  | eq_nibble NibbleA NibbleE = false
  | eq_nibble NibbleA NibbleF = false
  | eq_nibble NibbleB NibbleC = false
  | eq_nibble NibbleB NibbleD = false
  | eq_nibble NibbleB NibbleE = false
  | eq_nibble NibbleB NibbleF = false
  | eq_nibble NibbleC NibbleD = false
  | eq_nibble NibbleC NibbleE = false
  | eq_nibble NibbleC NibbleF = false
  | eq_nibble NibbleD NibbleE = false
  | eq_nibble NibbleD NibbleF = false
  | eq_nibble NibbleE NibbleF = false
  | eq_nibble Nibble1 Nibble0 = false
  | eq_nibble Nibble2 Nibble0 = false
  | eq_nibble Nibble3 Nibble0 = false
  | eq_nibble Nibble4 Nibble0 = false
  | eq_nibble Nibble5 Nibble0 = false
  | eq_nibble Nibble6 Nibble0 = false
  | eq_nibble Nibble7 Nibble0 = false
  | eq_nibble Nibble8 Nibble0 = false
  | eq_nibble Nibble9 Nibble0 = false
  | eq_nibble NibbleA Nibble0 = false
  | eq_nibble NibbleB Nibble0 = false
  | eq_nibble NibbleC Nibble0 = false
  | eq_nibble NibbleD Nibble0 = false
  | eq_nibble NibbleE Nibble0 = false
  | eq_nibble NibbleF Nibble0 = false
  | eq_nibble Nibble2 Nibble1 = false
  | eq_nibble Nibble3 Nibble1 = false
  | eq_nibble Nibble4 Nibble1 = false
  | eq_nibble Nibble5 Nibble1 = false
  | eq_nibble Nibble6 Nibble1 = false
  | eq_nibble Nibble7 Nibble1 = false
  | eq_nibble Nibble8 Nibble1 = false
  | eq_nibble Nibble9 Nibble1 = false
  | eq_nibble NibbleA Nibble1 = false
  | eq_nibble NibbleB Nibble1 = false
  | eq_nibble NibbleC Nibble1 = false
  | eq_nibble NibbleD Nibble1 = false
  | eq_nibble NibbleE Nibble1 = false
  | eq_nibble NibbleF Nibble1 = false
  | eq_nibble Nibble3 Nibble2 = false
  | eq_nibble Nibble4 Nibble2 = false
  | eq_nibble Nibble5 Nibble2 = false
  | eq_nibble Nibble6 Nibble2 = false
  | eq_nibble Nibble7 Nibble2 = false
  | eq_nibble Nibble8 Nibble2 = false
  | eq_nibble Nibble9 Nibble2 = false
  | eq_nibble NibbleA Nibble2 = false
  | eq_nibble NibbleB Nibble2 = false
  | eq_nibble NibbleC Nibble2 = false
  | eq_nibble NibbleD Nibble2 = false
  | eq_nibble NibbleE Nibble2 = false
  | eq_nibble NibbleF Nibble2 = false
  | eq_nibble Nibble4 Nibble3 = false
  | eq_nibble Nibble5 Nibble3 = false
  | eq_nibble Nibble6 Nibble3 = false
  | eq_nibble Nibble7 Nibble3 = false
  | eq_nibble Nibble8 Nibble3 = false
  | eq_nibble Nibble9 Nibble3 = false
  | eq_nibble NibbleA Nibble3 = false
  | eq_nibble NibbleB Nibble3 = false
  | eq_nibble NibbleC Nibble3 = false
  | eq_nibble NibbleD Nibble3 = false
  | eq_nibble NibbleE Nibble3 = false
  | eq_nibble NibbleF Nibble3 = false
  | eq_nibble Nibble5 Nibble4 = false
  | eq_nibble Nibble6 Nibble4 = false
  | eq_nibble Nibble7 Nibble4 = false
  | eq_nibble Nibble8 Nibble4 = false
  | eq_nibble Nibble9 Nibble4 = false
  | eq_nibble NibbleA Nibble4 = false
  | eq_nibble NibbleB Nibble4 = false
  | eq_nibble NibbleC Nibble4 = false
  | eq_nibble NibbleD Nibble4 = false
  | eq_nibble NibbleE Nibble4 = false
  | eq_nibble NibbleF Nibble4 = false
  | eq_nibble Nibble6 Nibble5 = false
  | eq_nibble Nibble7 Nibble5 = false
  | eq_nibble Nibble8 Nibble5 = false
  | eq_nibble Nibble9 Nibble5 = false
  | eq_nibble NibbleA Nibble5 = false
  | eq_nibble NibbleB Nibble5 = false
  | eq_nibble NibbleC Nibble5 = false
  | eq_nibble NibbleD Nibble5 = false
  | eq_nibble NibbleE Nibble5 = false
  | eq_nibble NibbleF Nibble5 = false
  | eq_nibble Nibble7 Nibble6 = false
  | eq_nibble Nibble8 Nibble6 = false
  | eq_nibble Nibble9 Nibble6 = false
  | eq_nibble NibbleA Nibble6 = false
  | eq_nibble NibbleB Nibble6 = false
  | eq_nibble NibbleC Nibble6 = false
  | eq_nibble NibbleD Nibble6 = false
  | eq_nibble NibbleE Nibble6 = false
  | eq_nibble NibbleF Nibble6 = false
  | eq_nibble Nibble8 Nibble7 = false
  | eq_nibble Nibble9 Nibble7 = false
  | eq_nibble NibbleA Nibble7 = false
  | eq_nibble NibbleB Nibble7 = false
  | eq_nibble NibbleC Nibble7 = false
  | eq_nibble NibbleD Nibble7 = false
  | eq_nibble NibbleE Nibble7 = false
  | eq_nibble NibbleF Nibble7 = false
  | eq_nibble Nibble9 Nibble8 = false
  | eq_nibble NibbleA Nibble8 = false
  | eq_nibble NibbleB Nibble8 = false
  | eq_nibble NibbleC Nibble8 = false
  | eq_nibble NibbleD Nibble8 = false
  | eq_nibble NibbleE Nibble8 = false
  | eq_nibble NibbleF Nibble8 = false
  | eq_nibble NibbleA Nibble9 = false
  | eq_nibble NibbleB Nibble9 = false
  | eq_nibble NibbleC Nibble9 = false
  | eq_nibble NibbleD Nibble9 = false
  | eq_nibble NibbleE Nibble9 = false
  | eq_nibble NibbleF Nibble9 = false
  | eq_nibble NibbleB NibbleA = false
  | eq_nibble NibbleC NibbleA = false
  | eq_nibble NibbleD NibbleA = false
  | eq_nibble NibbleE NibbleA = false
  | eq_nibble NibbleF NibbleA = false
  | eq_nibble NibbleC NibbleB = false
  | eq_nibble NibbleD NibbleB = false
  | eq_nibble NibbleE NibbleB = false
  | eq_nibble NibbleF NibbleB = false
  | eq_nibble NibbleD NibbleC = false
  | eq_nibble NibbleE NibbleC = false
  | eq_nibble NibbleF NibbleC = false
  | eq_nibble NibbleE NibbleD = false
  | eq_nibble NibbleF NibbleD = false
  | eq_nibble NibbleF NibbleE = false;

fun eq_char (Char (nibble1, nibble2)) (Char (nibble1', nibble2')) =
  eq_nibble nibble1 nibble1' andalso eq_nibble nibble2 nibble2';

val eq_chara = {eq = eq_char} : char Code_Generator.eq;

fun eq_list A_ [] [] = true
  | eq_list A_ (a :: lista) (a' :: list') =
    Code_Generator.eq A_ a a' andalso eq_list A_ lista list'
  | eq_list A_ [] (a :: b) = false
  | eq_list A_ (a :: b) [] = false;

fun list_all p (x :: xs) = p x andalso list_all p xs
  | list_all p [] = true;

fun size_list (a :: lista) =
  Nat.plus_nat (size_list lista) (Nat.Suc Nat.Zero_nat)
  | size_list [] = Nat.Zero_nat;

fun list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys
  | list_all2 p xs [] = null xs
  | list_all2 p [] ys = null ys
  | list_all2 p xs ys =
    Nat.eq_nat (size_list xs) (size_list ys) andalso
      list_all (fn a as (aa, b) => p aa b) (zip xs ys);

end; (*struct List*)

structure Codegen = 
struct

datatype monotype = Mono of List.char list * monotype list;

fun eq_monotype (Mono (tyco1, typargs1)) (Mono (tyco2, typargs2)) =
  List.eq_list List.eq_chara tyco1 tyco2 andalso
    List.list_all2 eq_monotype typargs1 typargs2;

end; (*struct Codegen*)

end; (*struct ROOT*)

(*  Title:      HOL/Tools/Qelim/generated_cooper.ML

This file is generated from HOL/Decision_Procs/Cooper.thy.  DO NOT EDIT.
*)

structure GeneratedCooper = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

val eq_nat = {eq = (fn a => fn b => ((a : IntInf.int) = b))} : IntInf.int eq;

fun eqop A_ a b = eq A_ a b;

fun divmod n m = (if eqop eq_nat m 0 then (0, n) else IntInf.divMod (n, m));

fun snd (a, b) = b;

fun mod_nat m n = snd (divmod m n);

fun gcd m n = (if eqop eq_nat n 0 then m else gcd n (mod_nat m n));

fun fst (a, b) = a;

fun div_nat m n = fst (divmod m n);

fun lcm m n = div_nat (IntInf.* (m, n)) (gcd m n);

fun leta s f = f s;

fun suc n = IntInf.+ (n, 1);

datatype num = Mul of IntInf.int * num | Sub of num * num | Add of num * num |
  Neg of num | Cn of IntInf.int * IntInf.int * num | Bound of IntInf.int |
  C of IntInf.int;

datatype fm = NClosed of IntInf.int | Closed of IntInf.int | A of fm | E of fm |
  Iff of fm * fm | Imp of fm * fm | Or of fm * fm | And of fm * fm | Not of fm |
  NDvd of IntInf.int * num | Dvd of IntInf.int * num | NEq of num | Eq of num |
  Ge of num | Gt of num | Le of num | Lt of num | F | T;

fun abs_int i = (if IntInf.< (i, (0 : IntInf.int)) then IntInf.~ i else i);

fun zlcm i j =
  (lcm (IntInf.max (0, (abs_int i))) (IntInf.max (0, (abs_int j))));

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun append [] ys = ys
  | append (x :: xs) ys = x :: append xs ys;

fun disjuncts (Or (p, q)) = append (disjuncts p) (disjuncts q)
  | disjuncts F = []
  | disjuncts T = [T]
  | disjuncts (Lt u) = [Lt u]
  | disjuncts (Le v) = [Le v]
  | disjuncts (Gt w) = [Gt w]
  | disjuncts (Ge x) = [Ge x]
  | disjuncts (Eq y) = [Eq y]
  | disjuncts (NEq z) = [NEq z]
  | disjuncts (Dvd (aa, ab)) = [Dvd (aa, ab)]
  | disjuncts (NDvd (ac, ad)) = [NDvd (ac, ad)]
  | disjuncts (Not ae) = [Not ae]
  | disjuncts (And (af, ag)) = [And (af, ag)]
  | disjuncts (Imp (aj, ak)) = [Imp (aj, ak)]
  | disjuncts (Iff (al, am)) = [Iff (al, am)]
  | disjuncts (E an) = [E an]
  | disjuncts (A ao) = [A ao]
  | disjuncts (Closed ap) = [Closed ap]
  | disjuncts (NClosed aq) = [NClosed aq];

fun fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
  (NClosed nat) = f19 nat
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Closed nat) = f18 nat
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (A fm) = f17 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (E fm) = f16 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Iff (fm1, fm2)) = f15 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Imp (fm1, fm2)) = f14 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Or (fm1, fm2)) = f13 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (And (fm1, fm2)) = f12 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Not fm) = f11 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (NDvd (inta, num)) = f10 inta num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Dvd (inta, num)) = f9 inta num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (NEq num) = f8 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Eq num) = f7 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Ge num) = f6 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Gt num) = f5 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Le num) = f4 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Lt num) = f3 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 F
    = f2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 T
    = f1;

fun eq_num (Mul (c, d)) (Sub (a, b)) = false
  | eq_num (Mul (c, d)) (Add (a, b)) = false
  | eq_num (Sub (c, d)) (Add (a, b)) = false
  | eq_num (Mul (b, c)) (Neg a) = false
  | eq_num (Sub (b, c)) (Neg a) = false
  | eq_num (Add (b, c)) (Neg a) = false
  | eq_num (Mul (d, e)) (Cn (a, b, c)) = false
  | eq_num (Sub (d, e)) (Cn (a, b, c)) = false
  | eq_num (Add (d, e)) (Cn (a, b, c)) = false
  | eq_num (Neg d) (Cn (a, b, c)) = false
  | eq_num (Mul (b, c)) (Bound a) = false
  | eq_num (Sub (b, c)) (Bound a) = false
  | eq_num (Add (b, c)) (Bound a) = false
  | eq_num (Neg b) (Bound a) = false
  | eq_num (Cn (b, c, d)) (Bound a) = false
  | eq_num (Mul (b, c)) (C a) = false
  | eq_num (Sub (b, c)) (C a) = false
  | eq_num (Add (b, c)) (C a) = false
  | eq_num (Neg b) (C a) = false
  | eq_num (Cn (b, c, d)) (C a) = false
  | eq_num (Bound b) (C a) = false
  | eq_num (Sub (a, b)) (Mul (c, d)) = false
  | eq_num (Add (a, b)) (Mul (c, d)) = false
  | eq_num (Add (a, b)) (Sub (c, d)) = false
  | eq_num (Neg a) (Mul (b, c)) = false
  | eq_num (Neg a) (Sub (b, c)) = false
  | eq_num (Neg a) (Add (b, c)) = false
  | eq_num (Cn (a, b, c)) (Mul (d, e)) = false
  | eq_num (Cn (a, b, c)) (Sub (d, e)) = false
  | eq_num (Cn (a, b, c)) (Add (d, e)) = false
  | eq_num (Cn (a, b, c)) (Neg d) = false
  | eq_num (Bound a) (Mul (b, c)) = false
  | eq_num (Bound a) (Sub (b, c)) = false
  | eq_num (Bound a) (Add (b, c)) = false
  | eq_num (Bound a) (Neg b) = false
  | eq_num (Bound a) (Cn (b, c, d)) = false
  | eq_num (C a) (Mul (b, c)) = false
  | eq_num (C a) (Sub (b, c)) = false
  | eq_num (C a) (Add (b, c)) = false
  | eq_num (C a) (Neg b) = false
  | eq_num (C a) (Cn (b, c, d)) = false
  | eq_num (C a) (Bound b) = false
  | eq_num (Mul (inta, num)) (Mul (int', num')) =
    ((inta : IntInf.int) = int') andalso eq_num num num'
  | eq_num (Sub (num1, num2)) (Sub (num1', num2')) =
    eq_num num1 num1' andalso eq_num num2 num2'
  | eq_num (Add (num1, num2)) (Add (num1', num2')) =
    eq_num num1 num1' andalso eq_num num2 num2'
  | eq_num (Neg num) (Neg num') = eq_num num num'
  | eq_num (Cn (nat, inta, num)) (Cn (nat', int', num')) =
    ((nat : IntInf.int) = nat') andalso
      (((inta : IntInf.int) = int') andalso eq_num num num')
  | eq_num (Bound nat) (Bound nat') = ((nat : IntInf.int) = nat')
  | eq_num (C inta) (C int') = ((inta : IntInf.int) = int');

fun eq_fm (NClosed b) (Closed a) = false
  | eq_fm (NClosed b) (A a) = false
  | eq_fm (Closed b) (A a) = false
  | eq_fm (NClosed b) (E a) = false
  | eq_fm (Closed b) (E a) = false
  | eq_fm (A b) (E a) = false
  | eq_fm (NClosed c) (Iff (a, b)) = false
  | eq_fm (Closed c) (Iff (a, b)) = false
  | eq_fm (A c) (Iff (a, b)) = false
  | eq_fm (E c) (Iff (a, b)) = false
  | eq_fm (NClosed c) (Imp (a, b)) = false
  | eq_fm (Closed c) (Imp (a, b)) = false
  | eq_fm (A c) (Imp (a, b)) = false
  | eq_fm (E c) (Imp (a, b)) = false
  | eq_fm (Iff (c, d)) (Imp (a, b)) = false
  | eq_fm (NClosed c) (Or (a, b)) = false
  | eq_fm (Closed c) (Or (a, b)) = false
  | eq_fm (A c) (Or (a, b)) = false
  | eq_fm (E c) (Or (a, b)) = false
  | eq_fm (Iff (c, d)) (Or (a, b)) = false
  | eq_fm (Imp (c, d)) (Or (a, b)) = false
  | eq_fm (NClosed c) (And (a, b)) = false
  | eq_fm (Closed c) (And (a, b)) = false
  | eq_fm (A c) (And (a, b)) = false
  | eq_fm (E c) (And (a, b)) = false
  | eq_fm (Iff (c, d)) (And (a, b)) = false
  | eq_fm (Imp (c, d)) (And (a, b)) = false
  | eq_fm (Or (c, d)) (And (a, b)) = false
  | eq_fm (NClosed b) (Not a) = false
  | eq_fm (Closed b) (Not a) = false
  | eq_fm (A b) (Not a) = false
  | eq_fm (E b) (Not a) = false
  | eq_fm (Iff (b, c)) (Not a) = false
  | eq_fm (Imp (b, c)) (Not a) = false
  | eq_fm (Or (b, c)) (Not a) = false
  | eq_fm (And (b, c)) (Not a) = false
  | eq_fm (NClosed c) (NDvd (a, b)) = false
  | eq_fm (Closed c) (NDvd (a, b)) = false
  | eq_fm (A c) (NDvd (a, b)) = false
  | eq_fm (E c) (NDvd (a, b)) = false
  | eq_fm (Iff (c, d)) (NDvd (a, b)) = false
  | eq_fm (Imp (c, d)) (NDvd (a, b)) = false
  | eq_fm (Or (c, d)) (NDvd (a, b)) = false
  | eq_fm (And (c, d)) (NDvd (a, b)) = false
  | eq_fm (Not c) (NDvd (a, b)) = false
  | eq_fm (NClosed c) (Dvd (a, b)) = false
  | eq_fm (Closed c) (Dvd (a, b)) = false
  | eq_fm (A c) (Dvd (a, b)) = false
  | eq_fm (E c) (Dvd (a, b)) = false
  | eq_fm (Iff (c, d)) (Dvd (a, b)) = false
  | eq_fm (Imp (c, d)) (Dvd (a, b)) = false
  | eq_fm (Or (c, d)) (Dvd (a, b)) = false
  | eq_fm (And (c, d)) (Dvd (a, b)) = false
  | eq_fm (Not c) (Dvd (a, b)) = false
  | eq_fm (NDvd (c, d)) (Dvd (a, b)) = false
  | eq_fm (NClosed b) (NEq a) = false
  | eq_fm (Closed b) (NEq a) = false
  | eq_fm (A b) (NEq a) = false
  | eq_fm (E b) (NEq a) = false
  | eq_fm (Iff (b, c)) (NEq a) = false
  | eq_fm (Imp (b, c)) (NEq a) = false
  | eq_fm (Or (b, c)) (NEq a) = false
  | eq_fm (And (b, c)) (NEq a) = false
  | eq_fm (Not b) (NEq a) = false
  | eq_fm (NDvd (b, c)) (NEq a) = false
  | eq_fm (Dvd (b, c)) (NEq a) = false
  | eq_fm (NClosed b) (Eq a) = false
  | eq_fm (Closed b) (Eq a) = false
  | eq_fm (A b) (Eq a) = false
  | eq_fm (E b) (Eq a) = false
  | eq_fm (Iff (b, c)) (Eq a) = false
  | eq_fm (Imp (b, c)) (Eq a) = false
  | eq_fm (Or (b, c)) (Eq a) = false
  | eq_fm (And (b, c)) (Eq a) = false
  | eq_fm (Not b) (Eq a) = false
  | eq_fm (NDvd (b, c)) (Eq a) = false
  | eq_fm (Dvd (b, c)) (Eq a) = false
  | eq_fm (NEq b) (Eq a) = false
  | eq_fm (NClosed b) (Ge a) = false
  | eq_fm (Closed b) (Ge a) = false
  | eq_fm (A b) (Ge a) = false
  | eq_fm (E b) (Ge a) = false
  | eq_fm (Iff (b, c)) (Ge a) = false
  | eq_fm (Imp (b, c)) (Ge a) = false
  | eq_fm (Or (b, c)) (Ge a) = false
  | eq_fm (And (b, c)) (Ge a) = false
  | eq_fm (Not b) (Ge a) = false
  | eq_fm (NDvd (b, c)) (Ge a) = false
  | eq_fm (Dvd (b, c)) (Ge a) = false
  | eq_fm (NEq b) (Ge a) = false
  | eq_fm (Eq b) (Ge a) = false
  | eq_fm (NClosed b) (Gt a) = false
  | eq_fm (Closed b) (Gt a) = false
  | eq_fm (A b) (Gt a) = false
  | eq_fm (E b) (Gt a) = false
  | eq_fm (Iff (b, c)) (Gt a) = false
  | eq_fm (Imp (b, c)) (Gt a) = false
  | eq_fm (Or (b, c)) (Gt a) = false
  | eq_fm (And (b, c)) (Gt a) = false
  | eq_fm (Not b) (Gt a) = false
  | eq_fm (NDvd (b, c)) (Gt a) = false
  | eq_fm (Dvd (b, c)) (Gt a) = false
  | eq_fm (NEq b) (Gt a) = false
  | eq_fm (Eq b) (Gt a) = false
  | eq_fm (Ge b) (Gt a) = false
  | eq_fm (NClosed b) (Le a) = false
  | eq_fm (Closed b) (Le a) = false
  | eq_fm (A b) (Le a) = false
  | eq_fm (E b) (Le a) = false
  | eq_fm (Iff (b, c)) (Le a) = false
  | eq_fm (Imp (b, c)) (Le a) = false
  | eq_fm (Or (b, c)) (Le a) = false
  | eq_fm (And (b, c)) (Le a) = false
  | eq_fm (Not b) (Le a) = false
  | eq_fm (NDvd (b, c)) (Le a) = false
  | eq_fm (Dvd (b, c)) (Le a) = false
  | eq_fm (NEq b) (Le a) = false
  | eq_fm (Eq b) (Le a) = false
  | eq_fm (Ge b) (Le a) = false
  | eq_fm (Gt b) (Le a) = false
  | eq_fm (NClosed b) (Lt a) = false
  | eq_fm (Closed b) (Lt a) = false
  | eq_fm (A b) (Lt a) = false
  | eq_fm (E b) (Lt a) = false
  | eq_fm (Iff (b, c)) (Lt a) = false
  | eq_fm (Imp (b, c)) (Lt a) = false
  | eq_fm (Or (b, c)) (Lt a) = false
  | eq_fm (And (b, c)) (Lt a) = false
  | eq_fm (Not b) (Lt a) = false
  | eq_fm (NDvd (b, c)) (Lt a) = false
  | eq_fm (Dvd (b, c)) (Lt a) = false
  | eq_fm (NEq b) (Lt a) = false
  | eq_fm (Eq b) (Lt a) = false
  | eq_fm (Ge b) (Lt a) = false
  | eq_fm (Gt b) (Lt a) = false
  | eq_fm (Le b) (Lt a) = false
  | eq_fm (NClosed a) F = false
  | eq_fm (Closed a) F = false
  | eq_fm (A a) F = false
  | eq_fm (E a) F = false
  | eq_fm (Iff (a, b)) F = false
  | eq_fm (Imp (a, b)) F = false
  | eq_fm (Or (a, b)) F = false
  | eq_fm (And (a, b)) F = false
  | eq_fm (Not a) F = false
  | eq_fm (NDvd (a, b)) F = false
  | eq_fm (Dvd (a, b)) F = false
  | eq_fm (NEq a) F = false
  | eq_fm (Eq a) F = false
  | eq_fm (Ge a) F = false
  | eq_fm (Gt a) F = false
  | eq_fm (Le a) F = false
  | eq_fm (Lt a) F = false
  | eq_fm (NClosed a) T = false
  | eq_fm (Closed a) T = false
  | eq_fm (A a) T = false
  | eq_fm (E a) T = false
  | eq_fm (Iff (a, b)) T = false
  | eq_fm (Imp (a, b)) T = false
  | eq_fm (Or (a, b)) T = false
  | eq_fm (And (a, b)) T = false
  | eq_fm (Not a) T = false
  | eq_fm (NDvd (a, b)) T = false
  | eq_fm (Dvd (a, b)) T = false
  | eq_fm (NEq a) T = false
  | eq_fm (Eq a) T = false
  | eq_fm (Ge a) T = false
  | eq_fm (Gt a) T = false
  | eq_fm (Le a) T = false
  | eq_fm (Lt a) T = false
  | eq_fm F T = false
  | eq_fm (Closed a) (NClosed b) = false
  | eq_fm (A a) (NClosed b) = false
  | eq_fm (A a) (Closed b) = false
  | eq_fm (E a) (NClosed b) = false
  | eq_fm (E a) (Closed b) = false
  | eq_fm (E a) (A b) = false
  | eq_fm (Iff (a, b)) (NClosed c) = false
  | eq_fm (Iff (a, b)) (Closed c) = false
  | eq_fm (Iff (a, b)) (A c) = false
  | eq_fm (Iff (a, b)) (E c) = false
  | eq_fm (Imp (a, b)) (NClosed c) = false
  | eq_fm (Imp (a, b)) (Closed c) = false
  | eq_fm (Imp (a, b)) (A c) = false
  | eq_fm (Imp (a, b)) (E c) = false
  | eq_fm (Imp (a, b)) (Iff (c, d)) = false
  | eq_fm (Or (a, b)) (NClosed c) = false
  | eq_fm (Or (a, b)) (Closed c) = false
  | eq_fm (Or (a, b)) (A c) = false
  | eq_fm (Or (a, b)) (E c) = false
  | eq_fm (Or (a, b)) (Iff (c, d)) = false
  | eq_fm (Or (a, b)) (Imp (c, d)) = false
  | eq_fm (And (a, b)) (NClosed c) = false
  | eq_fm (And (a, b)) (Closed c) = false
  | eq_fm (And (a, b)) (A c) = false
  | eq_fm (And (a, b)) (E c) = false
  | eq_fm (And (a, b)) (Iff (c, d)) = false
  | eq_fm (And (a, b)) (Imp (c, d)) = false
  | eq_fm (And (a, b)) (Or (c, d)) = false
  | eq_fm (Not a) (NClosed b) = false
  | eq_fm (Not a) (Closed b) = false
  | eq_fm (Not a) (A b) = false
  | eq_fm (Not a) (E b) = false
  | eq_fm (Not a) (Iff (b, c)) = false
  | eq_fm (Not a) (Imp (b, c)) = false
  | eq_fm (Not a) (Or (b, c)) = false
  | eq_fm (Not a) (And (b, c)) = false
  | eq_fm (NDvd (a, b)) (NClosed c) = false
  | eq_fm (NDvd (a, b)) (Closed c) = false
  | eq_fm (NDvd (a, b)) (A c) = false
  | eq_fm (NDvd (a, b)) (E c) = false
  | eq_fm (NDvd (a, b)) (Iff (c, d)) = false
  | eq_fm (NDvd (a, b)) (Imp (c, d)) = false
  | eq_fm (NDvd (a, b)) (Or (c, d)) = false
  | eq_fm (NDvd (a, b)) (And (c, d)) = false
  | eq_fm (NDvd (a, b)) (Not c) = false
  | eq_fm (Dvd (a, b)) (NClosed c) = false
  | eq_fm (Dvd (a, b)) (Closed c) = false
  | eq_fm (Dvd (a, b)) (A c) = false
  | eq_fm (Dvd (a, b)) (E c) = false
  | eq_fm (Dvd (a, b)) (Iff (c, d)) = false
  | eq_fm (Dvd (a, b)) (Imp (c, d)) = false
  | eq_fm (Dvd (a, b)) (Or (c, d)) = false
  | eq_fm (Dvd (a, b)) (And (c, d)) = false
  | eq_fm (Dvd (a, b)) (Not c) = false
  | eq_fm (Dvd (a, b)) (NDvd (c, d)) = false
  | eq_fm (NEq a) (NClosed b) = false
  | eq_fm (NEq a) (Closed b) = false
  | eq_fm (NEq a) (A b) = false
  | eq_fm (NEq a) (E b) = false
  | eq_fm (NEq a) (Iff (b, c)) = false
  | eq_fm (NEq a) (Imp (b, c)) = false
  | eq_fm (NEq a) (Or (b, c)) = false
  | eq_fm (NEq a) (And (b, c)) = false
  | eq_fm (NEq a) (Not b) = false
  | eq_fm (NEq a) (NDvd (b, c)) = false
  | eq_fm (NEq a) (Dvd (b, c)) = false
  | eq_fm (Eq a) (NClosed b) = false
  | eq_fm (Eq a) (Closed b) = false
  | eq_fm (Eq a) (A b) = false
  | eq_fm (Eq a) (E b) = false
  | eq_fm (Eq a) (Iff (b, c)) = false
  | eq_fm (Eq a) (Imp (b, c)) = false
  | eq_fm (Eq a) (Or (b, c)) = false
  | eq_fm (Eq a) (And (b, c)) = false
  | eq_fm (Eq a) (Not b) = false
  | eq_fm (Eq a) (NDvd (b, c)) = false
  | eq_fm (Eq a) (Dvd (b, c)) = false
  | eq_fm (Eq a) (NEq b) = false
  | eq_fm (Ge a) (NClosed b) = false
  | eq_fm (Ge a) (Closed b) = false
  | eq_fm (Ge a) (A b) = false
  | eq_fm (Ge a) (E b) = false
  | eq_fm (Ge a) (Iff (b, c)) = false
  | eq_fm (Ge a) (Imp (b, c)) = false
  | eq_fm (Ge a) (Or (b, c)) = false
  | eq_fm (Ge a) (And (b, c)) = false
  | eq_fm (Ge a) (Not b) = false
  | eq_fm (Ge a) (NDvd (b, c)) = false
  | eq_fm (Ge a) (Dvd (b, c)) = false
  | eq_fm (Ge a) (NEq b) = false
  | eq_fm (Ge a) (Eq b) = false
  | eq_fm (Gt a) (NClosed b) = false
  | eq_fm (Gt a) (Closed b) = false
  | eq_fm (Gt a) (A b) = false
  | eq_fm (Gt a) (E b) = false
  | eq_fm (Gt a) (Iff (b, c)) = false
  | eq_fm (Gt a) (Imp (b, c)) = false
  | eq_fm (Gt a) (Or (b, c)) = false
  | eq_fm (Gt a) (And (b, c)) = false
  | eq_fm (Gt a) (Not b) = false
  | eq_fm (Gt a) (NDvd (b, c)) = false
  | eq_fm (Gt a) (Dvd (b, c)) = false
  | eq_fm (Gt a) (NEq b) = false
  | eq_fm (Gt a) (Eq b) = false
  | eq_fm (Gt a) (Ge b) = false
  | eq_fm (Le a) (NClosed b) = false
  | eq_fm (Le a) (Closed b) = false
  | eq_fm (Le a) (A b) = false
  | eq_fm (Le a) (E b) = false
  | eq_fm (Le a) (Iff (b, c)) = false
  | eq_fm (Le a) (Imp (b, c)) = false
  | eq_fm (Le a) (Or (b, c)) = false
  | eq_fm (Le a) (And (b, c)) = false
  | eq_fm (Le a) (Not b) = false
  | eq_fm (Le a) (NDvd (b, c)) = false
  | eq_fm (Le a) (Dvd (b, c)) = false
  | eq_fm (Le a) (NEq b) = false
  | eq_fm (Le a) (Eq b) = false
  | eq_fm (Le a) (Ge b) = false
  | eq_fm (Le a) (Gt b) = false
  | eq_fm (Lt a) (NClosed b) = false
  | eq_fm (Lt a) (Closed b) = false
  | eq_fm (Lt a) (A b) = false
  | eq_fm (Lt a) (E b) = false
  | eq_fm (Lt a) (Iff (b, c)) = false
  | eq_fm (Lt a) (Imp (b, c)) = false
  | eq_fm (Lt a) (Or (b, c)) = false
  | eq_fm (Lt a) (And (b, c)) = false
  | eq_fm (Lt a) (Not b) = false
  | eq_fm (Lt a) (NDvd (b, c)) = false
  | eq_fm (Lt a) (Dvd (b, c)) = false
  | eq_fm (Lt a) (NEq b) = false
  | eq_fm (Lt a) (Eq b) = false
  | eq_fm (Lt a) (Ge b) = false
  | eq_fm (Lt a) (Gt b) = false
  | eq_fm (Lt a) (Le b) = false
  | eq_fm F (NClosed a) = false
  | eq_fm F (Closed a) = false
  | eq_fm F (A a) = false
  | eq_fm F (E a) = false
  | eq_fm F (Iff (a, b)) = false
  | eq_fm F (Imp (a, b)) = false
  | eq_fm F (Or (a, b)) = false
  | eq_fm F (And (a, b)) = false
  | eq_fm F (Not a) = false
  | eq_fm F (NDvd (a, b)) = false
  | eq_fm F (Dvd (a, b)) = false
  | eq_fm F (NEq a) = false
  | eq_fm F (Eq a) = false
  | eq_fm F (Ge a) = false
  | eq_fm F (Gt a) = false
  | eq_fm F (Le a) = false
  | eq_fm F (Lt a) = false
  | eq_fm T (NClosed a) = false
  | eq_fm T (Closed a) = false
  | eq_fm T (A a) = false
  | eq_fm T (E a) = false
  | eq_fm T (Iff (a, b)) = false
  | eq_fm T (Imp (a, b)) = false
  | eq_fm T (Or (a, b)) = false
  | eq_fm T (And (a, b)) = false
  | eq_fm T (Not a) = false
  | eq_fm T (NDvd (a, b)) = false
  | eq_fm T (Dvd (a, b)) = false
  | eq_fm T (NEq a) = false
  | eq_fm T (Eq a) = false
  | eq_fm T (Ge a) = false
  | eq_fm T (Gt a) = false
  | eq_fm T (Le a) = false
  | eq_fm T (Lt a) = false
  | eq_fm T F = false
  | eq_fm (NClosed nat) (NClosed nat') = ((nat : IntInf.int) = nat')
  | eq_fm (Closed nat) (Closed nat') = ((nat : IntInf.int) = nat')
  | eq_fm (A fm) (A fm') = eq_fm fm fm'
  | eq_fm (E fm) (E fm') = eq_fm fm fm'
  | eq_fm (Iff (fm1, fm2)) (Iff (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Imp (fm1, fm2)) (Imp (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Or (fm1, fm2)) (Or (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (And (fm1, fm2)) (And (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Not fm) (Not fm') = eq_fm fm fm'
  | eq_fm (NDvd (inta, num)) (NDvd (int', num')) =
    ((inta : IntInf.int) = int') andalso eq_num num num'
  | eq_fm (Dvd (inta, num)) (Dvd (int', num')) =
    ((inta : IntInf.int) = int') andalso eq_num num num'
  | eq_fm (NEq num) (NEq num') = eq_num num num'
  | eq_fm (Eq num) (Eq num') = eq_num num num'
  | eq_fm (Ge num) (Ge num') = eq_num num num'
  | eq_fm (Gt num) (Gt num') = eq_num num num'
  | eq_fm (Le num) (Le num') = eq_num num num'
  | eq_fm (Lt num) (Lt num') = eq_num num num'
  | eq_fm F F = true
  | eq_fm T T = true;

val eq_fma = {eq = eq_fm} : fm eq;

fun djf f p q =
  (if eqop eq_fma q T then T
    else (if eqop eq_fma q F then f p
           else let
                  val a = f p;
                in
                  (case a of T => T | F => q | Lt num => Or (f p, q)
                     | Le num => Or (f p, q) | Gt num => Or (f p, q)
                     | Ge num => Or (f p, q) | Eq num => Or (f p, q)
                     | NEq num => Or (f p, q) | Dvd (inta, num) => Or (f p, q)
                     | NDvd (inta, num) => Or (f p, q) | Not fm => Or (f p, q)
                     | And (fm1, fm2) => Or (f p, q)
                     | Or (fm1, fm2) => Or (f p, q)
                     | Imp (fm1, fm2) => Or (f p, q)
                     | Iff (fm1, fm2) => Or (f p, q) | E fm => Or (f p, q)
                     | A fm => Or (f p, q) | Closed nat => Or (f p, q)
                     | NClosed nat => Or (f p, q))
                end));

fun foldr f [] a = a
  | foldr f (x :: xs) a = f x (foldr f xs a);

fun evaldjf f ps = foldr (djf f) ps F;

fun dj f p = evaldjf f (disjuncts p);

fun disj p q =
  (if eqop eq_fma p T orelse eqop eq_fma q T then T
    else (if eqop eq_fma p F then q
           else (if eqop eq_fma q F then p else Or (p, q))));

fun minus_nat n m = IntInf.max (0, (IntInf.- (n, m)));

fun decrnum (Bound n) = Bound (minus_nat n 1)
  | decrnum (Neg a) = Neg (decrnum a)
  | decrnum (Add (a, b)) = Add (decrnum a, decrnum b)
  | decrnum (Sub (a, b)) = Sub (decrnum a, decrnum b)
  | decrnum (Mul (c, a)) = Mul (c, decrnum a)
  | decrnum (Cn (n, i, a)) = Cn (minus_nat n 1, i, decrnum a)
  | decrnum (C u) = C u;

fun decr (Lt a) = Lt (decrnum a)
  | decr (Le a) = Le (decrnum a)
  | decr (Gt a) = Gt (decrnum a)
  | decr (Ge a) = Ge (decrnum a)
  | decr (Eq a) = Eq (decrnum a)
  | decr (NEq a) = NEq (decrnum a)
  | decr (Dvd (i, a)) = Dvd (i, decrnum a)
  | decr (NDvd (i, a)) = NDvd (i, decrnum a)
  | decr (Not p) = Not (decr p)
  | decr (And (p, q)) = And (decr p, decr q)
  | decr (Or (p, q)) = Or (decr p, decr q)
  | decr (Imp (p, q)) = Imp (decr p, decr q)
  | decr (Iff (p, q)) = Iff (decr p, decr q)
  | decr T = T
  | decr F = F
  | decr (E ao) = E ao
  | decr (A ap) = A ap
  | decr (Closed aq) = Closed aq
  | decr (NClosed ar) = NClosed ar;

fun concat [] = []
  | concat (x :: xs) = append x (concat xs);

fun split f (a, b) = f a b;

fun numsubst0 t (C c) = C c
  | numsubst0 t (Bound n) = (if eqop eq_nat n 0 then t else Bound n)
  | numsubst0 t (Neg a) = Neg (numsubst0 t a)
  | numsubst0 t (Add (a, b)) = Add (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Sub (a, b)) = Sub (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Mul (i, a)) = Mul (i, numsubst0 t a)
  | numsubst0 t (Cn (v, i, a)) =
    (if eqop eq_nat v 0 then Add (Mul (i, t), numsubst0 t a)
      else Cn (suc (minus_nat v 1), i, numsubst0 t a));

fun subst0 t T = T
  | subst0 t F = F
  | subst0 t (Lt a) = Lt (numsubst0 t a)
  | subst0 t (Le a) = Le (numsubst0 t a)
  | subst0 t (Gt a) = Gt (numsubst0 t a)
  | subst0 t (Ge a) = Ge (numsubst0 t a)
  | subst0 t (Eq a) = Eq (numsubst0 t a)
  | subst0 t (NEq a) = NEq (numsubst0 t a)
  | subst0 t (Dvd (i, a)) = Dvd (i, numsubst0 t a)
  | subst0 t (NDvd (i, a)) = NDvd (i, numsubst0 t a)
  | subst0 t (Not p) = Not (subst0 t p)
  | subst0 t (And (p, q)) = And (subst0 t p, subst0 t q)
  | subst0 t (Or (p, q)) = Or (subst0 t p, subst0 t q)
  | subst0 t (Imp (p, q)) = Imp (subst0 t p, subst0 t q)
  | subst0 t (Iff (p, q)) = Iff (subst0 t p, subst0 t q)
  | subst0 t (Closed p) = Closed p
  | subst0 t (NClosed p) = NClosed p;

fun minusinf (And (p, q)) = And (minusinf p, minusinf q)
  | minusinf (Or (p, q)) = Or (minusinf p, minusinf q)
  | minusinf T = T
  | minusinf F = F
  | minusinf (Lt (C bo)) = Lt (C bo)
  | minusinf (Lt (Bound bp)) = Lt (Bound bp)
  | minusinf (Lt (Neg bt)) = Lt (Neg bt)
  | minusinf (Lt (Add (bu, bv))) = Lt (Add (bu, bv))
  | minusinf (Lt (Sub (bw, bx))) = Lt (Sub (bw, bx))
  | minusinf (Lt (Mul (by, bz))) = Lt (Mul (by, bz))
  | minusinf (Le (C co)) = Le (C co)
  | minusinf (Le (Bound cp)) = Le (Bound cp)
  | minusinf (Le (Neg ct)) = Le (Neg ct)
  | minusinf (Le (Add (cu, cv))) = Le (Add (cu, cv))
  | minusinf (Le (Sub (cw, cx))) = Le (Sub (cw, cx))
  | minusinf (Le (Mul (cy, cz))) = Le (Mul (cy, cz))
  | minusinf (Gt (C doa)) = Gt (C doa)
  | minusinf (Gt (Bound dp)) = Gt (Bound dp)
  | minusinf (Gt (Neg dt)) = Gt (Neg dt)
  | minusinf (Gt (Add (du, dv))) = Gt (Add (du, dv))
  | minusinf (Gt (Sub (dw, dx))) = Gt (Sub (dw, dx))
  | minusinf (Gt (Mul (dy, dz))) = Gt (Mul (dy, dz))
  | minusinf (Ge (C eo)) = Ge (C eo)
  | minusinf (Ge (Bound ep)) = Ge (Bound ep)
  | minusinf (Ge (Neg et)) = Ge (Neg et)
  | minusinf (Ge (Add (eu, ev))) = Ge (Add (eu, ev))
  | minusinf (Ge (Sub (ew, ex))) = Ge (Sub (ew, ex))
  | minusinf (Ge (Mul (ey, ez))) = Ge (Mul (ey, ez))
  | minusinf (Eq (C fo)) = Eq (C fo)
  | minusinf (Eq (Bound fp)) = Eq (Bound fp)
  | minusinf (Eq (Neg ft)) = Eq (Neg ft)
  | minusinf (Eq (Add (fu, fv))) = Eq (Add (fu, fv))
  | minusinf (Eq (Sub (fw, fx))) = Eq (Sub (fw, fx))
  | minusinf (Eq (Mul (fy, fz))) = Eq (Mul (fy, fz))
  | minusinf (NEq (C go)) = NEq (C go)
  | minusinf (NEq (Bound gp)) = NEq (Bound gp)
  | minusinf (NEq (Neg gt)) = NEq (Neg gt)
  | minusinf (NEq (Add (gu, gv))) = NEq (Add (gu, gv))
  | minusinf (NEq (Sub (gw, gx))) = NEq (Sub (gw, gx))
  | minusinf (NEq (Mul (gy, gz))) = NEq (Mul (gy, gz))
  | minusinf (Dvd (aa, ab)) = Dvd (aa, ab)
  | minusinf (NDvd (ac, ad)) = NDvd (ac, ad)
  | minusinf (Not ae) = Not ae
  | minusinf (Imp (aj, ak)) = Imp (aj, ak)
  | minusinf (Iff (al, am)) = Iff (al, am)
  | minusinf (E an) = E an
  | minusinf (A ao) = A ao
  | minusinf (Closed ap) = Closed ap
  | minusinf (NClosed aq) = NClosed aq
  | minusinf (Lt (Cn (cm, c, e))) =
    (if eqop eq_nat cm 0 then T else Lt (Cn (suc (minus_nat cm 1), c, e)))
  | minusinf (Le (Cn (dm, c, e))) =
    (if eqop eq_nat dm 0 then T else Le (Cn (suc (minus_nat dm 1), c, e)))
  | minusinf (Gt (Cn (em, c, e))) =
    (if eqop eq_nat em 0 then F else Gt (Cn (suc (minus_nat em 1), c, e)))
  | minusinf (Ge (Cn (fm, c, e))) =
    (if eqop eq_nat fm 0 then F else Ge (Cn (suc (minus_nat fm 1), c, e)))
  | minusinf (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0 then F else Eq (Cn (suc (minus_nat gm 1), c, e)))
  | minusinf (NEq (Cn (hm, c, e))) =
    (if eqop eq_nat hm 0 then T else NEq (Cn (suc (minus_nat hm 1), c, e)));

val eq_int = {eq = (fn a => fn b => ((a : IntInf.int) = b))} : IntInf.int eq;

fun sgn_int i =
  (if eqop eq_int i (0 : IntInf.int) then (0 : IntInf.int)
    else (if IntInf.< ((0 : IntInf.int), i) then (1 : IntInf.int)
           else IntInf.~ (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmoda k l =
  (if eqop eq_int k (0 : IntInf.int) then ((0 : IntInf.int), (0 : IntInf.int))
    else (if eqop eq_int l (0 : IntInf.int) then ((0 : IntInf.int), k)
           else apsnd (fn a => IntInf.* (sgn_int l, a))
                  (if eqop eq_int (sgn_int k) (sgn_int l)
                    then (fn k => fn l => IntInf.divMod (IntInf.abs k,
                           IntInf.abs l))
                           k l
                    else let
                           val a =
                             (fn k => fn l => IntInf.divMod (IntInf.abs k,
                               IntInf.abs l))
                               k l;
                           val (r, s) = a;
                         in
                           (if eqop eq_int s (0 : IntInf.int)
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_int l, s)))
                         end)));

fun mod_int a b = snd (divmoda a b);

fun num_case f1 f2 f3 f4 f5 f6 f7 (Mul (inta, num)) = f7 inta num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Sub (num1, num2)) = f6 num1 num2
  | num_case f1 f2 f3 f4 f5 f6 f7 (Add (num1, num2)) = f5 num1 num2
  | num_case f1 f2 f3 f4 f5 f6 f7 (Neg num) = f4 num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Cn (nat, inta, num)) = f3 nat inta num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Bound nat) = f2 nat
  | num_case f1 f2 f3 f4 f5 f6 f7 (C inta) = f1 inta;

fun nummul i (C j) = C (IntInf.* (i, j))
  | nummul i (Cn (n, c, t)) = Cn (n, IntInf.* (c, i), nummul i t)
  | nummul i (Bound v) = Mul (i, Bound v)
  | nummul i (Neg v) = Mul (i, Neg v)
  | nummul i (Add (v, va)) = Mul (i, Add (v, va))
  | nummul i (Sub (v, va)) = Mul (i, Sub (v, va))
  | nummul i (Mul (v, va)) = Mul (i, Mul (v, va));

fun numneg t = nummul (IntInf.~ (1 : IntInf.int)) t;

fun numadd (Cn (n1, c1, r1), Cn (n2, c2, r2)) =
  (if eqop eq_nat n1 n2
    then let
           val c = IntInf.+ (c1, c2);
         in
           (if eqop eq_int c (0 : IntInf.int) then numadd (r1, r2)
             else Cn (n1, c, numadd (r1, r2)))
         end
    else (if IntInf.<= (n1, n2)
           then Cn (n1, c1, numadd (r1, Add (Mul (c2, Bound n2), r2)))
           else Cn (n2, c2, numadd (Add (Mul (c1, Bound n1), r1), r2))))
  | numadd (Cn (n1, c1, r1), C dd) = Cn (n1, c1, numadd (r1, C dd))
  | numadd (Cn (n1, c1, r1), Bound de) = Cn (n1, c1, numadd (r1, Bound de))
  | numadd (Cn (n1, c1, r1), Neg di) = Cn (n1, c1, numadd (r1, Neg di))
  | numadd (Cn (n1, c1, r1), Add (dj, dk)) =
    Cn (n1, c1, numadd (r1, Add (dj, dk)))
  | numadd (Cn (n1, c1, r1), Sub (dl, dm)) =
    Cn (n1, c1, numadd (r1, Sub (dl, dm)))
  | numadd (Cn (n1, c1, r1), Mul (dn, doa)) =
    Cn (n1, c1, numadd (r1, Mul (dn, doa)))
  | numadd (C w, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (C w, r2))
  | numadd (Bound x, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (Bound x, r2))
  | numadd (Neg ac, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (Neg ac, r2))
  | numadd (Add (ad, ae), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Add (ad, ae), r2))
  | numadd (Sub (af, ag), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Sub (af, ag), r2))
  | numadd (Mul (ah, ai), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Mul (ah, ai), r2))
  | numadd (C b1, C b2) = C (IntInf.+ (b1, b2))
  | numadd (C aj, Bound bi) = Add (C aj, Bound bi)
  | numadd (C aj, Neg bm) = Add (C aj, Neg bm)
  | numadd (C aj, Add (bn, bo)) = Add (C aj, Add (bn, bo))
  | numadd (C aj, Sub (bp, bq)) = Add (C aj, Sub (bp, bq))
  | numadd (C aj, Mul (br, bs)) = Add (C aj, Mul (br, bs))
  | numadd (Bound ak, C cf) = Add (Bound ak, C cf)
  | numadd (Bound ak, Bound cg) = Add (Bound ak, Bound cg)
  | numadd (Bound ak, Neg ck) = Add (Bound ak, Neg ck)
  | numadd (Bound ak, Add (cl, cm)) = Add (Bound ak, Add (cl, cm))
  | numadd (Bound ak, Sub (cn, co)) = Add (Bound ak, Sub (cn, co))
  | numadd (Bound ak, Mul (cp, cq)) = Add (Bound ak, Mul (cp, cq))
  | numadd (Neg ao, C en) = Add (Neg ao, C en)
  | numadd (Neg ao, Bound eo) = Add (Neg ao, Bound eo)
  | numadd (Neg ao, Neg es) = Add (Neg ao, Neg es)
  | numadd (Neg ao, Add (et, eu)) = Add (Neg ao, Add (et, eu))
  | numadd (Neg ao, Sub (ev, ew)) = Add (Neg ao, Sub (ev, ew))
  | numadd (Neg ao, Mul (ex, ey)) = Add (Neg ao, Mul (ex, ey))
  | numadd (Add (ap, aq), C fl) = Add (Add (ap, aq), C fl)
  | numadd (Add (ap, aq), Bound fm) = Add (Add (ap, aq), Bound fm)
  | numadd (Add (ap, aq), Neg fq) = Add (Add (ap, aq), Neg fq)
  | numadd (Add (ap, aq), Add (fr, fs)) = Add (Add (ap, aq), Add (fr, fs))
  | numadd (Add (ap, aq), Sub (ft, fu)) = Add (Add (ap, aq), Sub (ft, fu))
  | numadd (Add (ap, aq), Mul (fv, fw)) = Add (Add (ap, aq), Mul (fv, fw))
  | numadd (Sub (ar, asa), C gj) = Add (Sub (ar, asa), C gj)
  | numadd (Sub (ar, asa), Bound gk) = Add (Sub (ar, asa), Bound gk)
  | numadd (Sub (ar, asa), Neg go) = Add (Sub (ar, asa), Neg go)
  | numadd (Sub (ar, asa), Add (gp, gq)) = Add (Sub (ar, asa), Add (gp, gq))
  | numadd (Sub (ar, asa), Sub (gr, gs)) = Add (Sub (ar, asa), Sub (gr, gs))
  | numadd (Sub (ar, asa), Mul (gt, gu)) = Add (Sub (ar, asa), Mul (gt, gu))
  | numadd (Mul (at, au), C hh) = Add (Mul (at, au), C hh)
  | numadd (Mul (at, au), Bound hi) = Add (Mul (at, au), Bound hi)
  | numadd (Mul (at, au), Neg hm) = Add (Mul (at, au), Neg hm)
  | numadd (Mul (at, au), Add (hn, ho)) = Add (Mul (at, au), Add (hn, ho))
  | numadd (Mul (at, au), Sub (hp, hq)) = Add (Mul (at, au), Sub (hp, hq))
  | numadd (Mul (at, au), Mul (hr, hs)) = Add (Mul (at, au), Mul (hr, hs));

val eq_numa = {eq = eq_num} : num eq;

fun numsub s t =
  (if eqop eq_numa s t then C (0 : IntInf.int) else numadd (s, numneg t));

fun simpnum (C j) = C j
  | simpnum (Bound n) = Cn (n, (1 : IntInf.int), C (0 : IntInf.int))
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Add (t, s)) = numadd (simpnum t, simpnum s)
  | simpnum (Sub (t, s)) = numsub (simpnum t) (simpnum s)
  | simpnum (Mul (i, t)) =
    (if eqop eq_int i (0 : IntInf.int) then C (0 : IntInf.int)
      else nummul i (simpnum t))
  | simpnum (Cn (v, va, vb)) = Cn (v, va, vb);

fun nota (Not p) = p
  | nota T = F
  | nota F = T
  | nota (Lt v) = Not (Lt v)
  | nota (Le v) = Not (Le v)
  | nota (Gt v) = Not (Gt v)
  | nota (Ge v) = Not (Ge v)
  | nota (Eq v) = Not (Eq v)
  | nota (NEq v) = Not (NEq v)
  | nota (Dvd (v, va)) = Not (Dvd (v, va))
  | nota (NDvd (v, va)) = Not (NDvd (v, va))
  | nota (And (v, va)) = Not (And (v, va))
  | nota (Or (v, va)) = Not (Or (v, va))
  | nota (Imp (v, va)) = Not (Imp (v, va))
  | nota (Iff (v, va)) = Not (Iff (v, va))
  | nota (E v) = Not (E v)
  | nota (A v) = Not (A v)
  | nota (Closed v) = Not (Closed v)
  | nota (NClosed v) = Not (NClosed v);

fun iffa p q =
  (if eqop eq_fma p q then T
    else (if eqop eq_fma p (nota q) orelse eqop eq_fma (nota p) q then F
           else (if eqop eq_fma p F then nota q
                  else (if eqop eq_fma q F then nota p
                         else (if eqop eq_fma p T then q
                                else (if eqop eq_fma q T then p
                                       else Iff (p, q)))))));

fun impa p q =
  (if eqop eq_fma p F orelse eqop eq_fma q T then T
    else (if eqop eq_fma p T then q
           else (if eqop eq_fma q F then nota p else Imp (p, q))));

fun conj p q =
  (if eqop eq_fma p F orelse eqop eq_fma q F then F
    else (if eqop eq_fma p T then q
           else (if eqop eq_fma q T then p else And (p, q))));

fun simpfm (And (p, q)) = conj (simpfm p) (simpfm q)
  | simpfm (Or (p, q)) = disj (simpfm p) (simpfm q)
  | simpfm (Imp (p, q)) = impa (simpfm p) (simpfm q)
  | simpfm (Iff (p, q)) = iffa (simpfm p) (simpfm q)
  | simpfm (Not p) = nota (simpfm p)
  | simpfm (Lt a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.< (v, (0 : IntInf.int)) then T else F)
         | Bound nat => Lt a' | Cn (nat, inta, num) => Lt a' | Neg num => Lt a'
         | Add (num1, num2) => Lt a' | Sub (num1, num2) => Lt a'
         | Mul (inta, num) => Lt a')
    end
  | simpfm (Le a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.<= (v, (0 : IntInf.int)) then T else F)
         | Bound nat => Le a' | Cn (nat, inta, num) => Le a' | Neg num => Le a'
         | Add (num1, num2) => Le a' | Sub (num1, num2) => Le a'
         | Mul (inta, num) => Le a')
    end
  | simpfm (Gt a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.< ((0 : IntInf.int), v) then T else F)
         | Bound nat => Gt a' | Cn (nat, inta, num) => Gt a' | Neg num => Gt a'
         | Add (num1, num2) => Gt a' | Sub (num1, num2) => Gt a'
         | Mul (inta, num) => Gt a')
    end
  | simpfm (Ge a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.<= ((0 : IntInf.int), v) then T else F)
         | Bound nat => Ge a' | Cn (nat, inta, num) => Ge a' | Neg num => Ge a'
         | Add (num1, num2) => Ge a' | Sub (num1, num2) => Ge a'
         | Mul (inta, num) => Ge a')
    end
  | simpfm (Eq a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if eqop eq_int v (0 : IntInf.int) then T else F)
         | Bound nat => Eq a' | Cn (nat, inta, num) => Eq a' | Neg num => Eq a'
         | Add (num1, num2) => Eq a' | Sub (num1, num2) => Eq a'
         | Mul (inta, num) => Eq a')
    end
  | simpfm (NEq a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if not (eqop eq_int v (0 : IntInf.int)) then T else F)
         | Bound nat => NEq a' | Cn (nat, inta, num) => NEq a'
         | Neg num => NEq a' | Add (num1, num2) => NEq a'
         | Sub (num1, num2) => NEq a' | Mul (inta, num) => NEq a')
    end
  | simpfm (Dvd (i, a)) =
    (if eqop eq_int i (0 : IntInf.int) then simpfm (Eq a)
      else (if eqop eq_int (abs_int i) (1 : IntInf.int) then T
             else let
                    val a' = simpnum a;
                  in
                    (case a'
                       of C v =>
                         (if eqop eq_int (mod_int v i) (0 : IntInf.int) then T
                           else F)
                       | Bound nat => Dvd (i, a')
                       | Cn (nat, inta, num) => Dvd (i, a')
                       | Neg num => Dvd (i, a')
                       | Add (num1, num2) => Dvd (i, a')
                       | Sub (num1, num2) => Dvd (i, a')
                       | Mul (inta, num) => Dvd (i, a'))
                  end))
  | simpfm (NDvd (i, a)) =
    (if eqop eq_int i (0 : IntInf.int) then simpfm (NEq a)
      else (if eqop eq_int (abs_int i) (1 : IntInf.int) then F
             else let
                    val a' = simpnum a;
                  in
                    (case a'
                       of C v =>
                         (if not (eqop eq_int (mod_int v i) (0 : IntInf.int))
                           then T else F)
                       | Bound nat => NDvd (i, a')
                       | Cn (nat, inta, num) => NDvd (i, a')
                       | Neg num => NDvd (i, a')
                       | Add (num1, num2) => NDvd (i, a')
                       | Sub (num1, num2) => NDvd (i, a')
                       | Mul (inta, num) => NDvd (i, a'))
                  end))
  | simpfm T = T
  | simpfm F = F
  | simpfm (E v) = E v
  | simpfm (A v) = A v
  | simpfm (Closed v) = Closed v
  | simpfm (NClosed v) = NClosed v;

fun iupt i j =
  (if IntInf.< (j, i) then []
    else i :: iupt (IntInf.+ (i, (1 : IntInf.int))) j);

fun mirror (And (p, q)) = And (mirror p, mirror q)
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror T = T
  | mirror F = F
  | mirror (Lt (C bo)) = Lt (C bo)
  | mirror (Lt (Bound bp)) = Lt (Bound bp)
  | mirror (Lt (Neg bt)) = Lt (Neg bt)
  | mirror (Lt (Add (bu, bv))) = Lt (Add (bu, bv))
  | mirror (Lt (Sub (bw, bx))) = Lt (Sub (bw, bx))
  | mirror (Lt (Mul (by, bz))) = Lt (Mul (by, bz))
  | mirror (Le (C co)) = Le (C co)
  | mirror (Le (Bound cp)) = Le (Bound cp)
  | mirror (Le (Neg ct)) = Le (Neg ct)
  | mirror (Le (Add (cu, cv))) = Le (Add (cu, cv))
  | mirror (Le (Sub (cw, cx))) = Le (Sub (cw, cx))
  | mirror (Le (Mul (cy, cz))) = Le (Mul (cy, cz))
  | mirror (Gt (C doa)) = Gt (C doa)
  | mirror (Gt (Bound dp)) = Gt (Bound dp)
  | mirror (Gt (Neg dt)) = Gt (Neg dt)
  | mirror (Gt (Add (du, dv))) = Gt (Add (du, dv))
  | mirror (Gt (Sub (dw, dx))) = Gt (Sub (dw, dx))
  | mirror (Gt (Mul (dy, dz))) = Gt (Mul (dy, dz))
  | mirror (Ge (C eo)) = Ge (C eo)
  | mirror (Ge (Bound ep)) = Ge (Bound ep)
  | mirror (Ge (Neg et)) = Ge (Neg et)
  | mirror (Ge (Add (eu, ev))) = Ge (Add (eu, ev))
  | mirror (Ge (Sub (ew, ex))) = Ge (Sub (ew, ex))
  | mirror (Ge (Mul (ey, ez))) = Ge (Mul (ey, ez))
  | mirror (Eq (C fo)) = Eq (C fo)
  | mirror (Eq (Bound fp)) = Eq (Bound fp)
  | mirror (Eq (Neg ft)) = Eq (Neg ft)
  | mirror (Eq (Add (fu, fv))) = Eq (Add (fu, fv))
  | mirror (Eq (Sub (fw, fx))) = Eq (Sub (fw, fx))
  | mirror (Eq (Mul (fy, fz))) = Eq (Mul (fy, fz))
  | mirror (NEq (C go)) = NEq (C go)
  | mirror (NEq (Bound gp)) = NEq (Bound gp)
  | mirror (NEq (Neg gt)) = NEq (Neg gt)
  | mirror (NEq (Add (gu, gv))) = NEq (Add (gu, gv))
  | mirror (NEq (Sub (gw, gx))) = NEq (Sub (gw, gx))
  | mirror (NEq (Mul (gy, gz))) = NEq (Mul (gy, gz))
  | mirror (Dvd (aa, C ho)) = Dvd (aa, C ho)
  | mirror (Dvd (aa, Bound hp)) = Dvd (aa, Bound hp)
  | mirror (Dvd (aa, Neg ht)) = Dvd (aa, Neg ht)
  | mirror (Dvd (aa, Add (hu, hv))) = Dvd (aa, Add (hu, hv))
  | mirror (Dvd (aa, Sub (hw, hx))) = Dvd (aa, Sub (hw, hx))
  | mirror (Dvd (aa, Mul (hy, hz))) = Dvd (aa, Mul (hy, hz))
  | mirror (NDvd (ac, C io)) = NDvd (ac, C io)
  | mirror (NDvd (ac, Bound ip)) = NDvd (ac, Bound ip)
  | mirror (NDvd (ac, Neg it)) = NDvd (ac, Neg it)
  | mirror (NDvd (ac, Add (iu, iv))) = NDvd (ac, Add (iu, iv))
  | mirror (NDvd (ac, Sub (iw, ix))) = NDvd (ac, Sub (iw, ix))
  | mirror (NDvd (ac, Mul (iy, iz))) = NDvd (ac, Mul (iy, iz))
  | mirror (Not ae) = Not ae
  | mirror (Imp (aj, ak)) = Imp (aj, ak)
  | mirror (Iff (al, am)) = Iff (al, am)
  | mirror (E an) = E an
  | mirror (A ao) = A ao
  | mirror (Closed ap) = Closed ap
  | mirror (NClosed aq) = NClosed aq
  | mirror (Lt (Cn (cm, c, e))) =
    (if eqop eq_nat cm 0 then Gt (Cn (0, c, Neg e))
      else Lt (Cn (suc (minus_nat cm 1), c, e)))
  | mirror (Le (Cn (dm, c, e))) =
    (if eqop eq_nat dm 0 then Ge (Cn (0, c, Neg e))
      else Le (Cn (suc (minus_nat dm 1), c, e)))
  | mirror (Gt (Cn (em, c, e))) =
    (if eqop eq_nat em 0 then Lt (Cn (0, c, Neg e))
      else Gt (Cn (suc (minus_nat em 1), c, e)))
  | mirror (Ge (Cn (fm, c, e))) =
    (if eqop eq_nat fm 0 then Le (Cn (0, c, Neg e))
      else Ge (Cn (suc (minus_nat fm 1), c, e)))
  | mirror (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0 then Eq (Cn (0, c, Neg e))
      else Eq (Cn (suc (minus_nat gm 1), c, e)))
  | mirror (NEq (Cn (hm, c, e))) =
    (if eqop eq_nat hm 0 then NEq (Cn (0, c, Neg e))
      else NEq (Cn (suc (minus_nat hm 1), c, e)))
  | mirror (Dvd (i, Cn (im, c, e))) =
    (if eqop eq_nat im 0 then Dvd (i, Cn (0, c, Neg e))
      else Dvd (i, Cn (suc (minus_nat im 1), c, e)))
  | mirror (NDvd (i, Cn (jm, c, e))) =
    (if eqop eq_nat jm 0 then NDvd (i, Cn (0, c, Neg e))
      else NDvd (i, Cn (suc (minus_nat jm 1), c, e)));

fun size_list [] = 0
  | size_list (a :: lista) = IntInf.+ (size_list lista, suc 0);

fun alpha (And (p, q)) = append (alpha p) (alpha q)
  | alpha (Or (p, q)) = append (alpha p) (alpha q)
  | alpha T = []
  | alpha F = []
  | alpha (Lt (C bo)) = []
  | alpha (Lt (Bound bp)) = []
  | alpha (Lt (Neg bt)) = []
  | alpha (Lt (Add (bu, bv))) = []
  | alpha (Lt (Sub (bw, bx))) = []
  | alpha (Lt (Mul (by, bz))) = []
  | alpha (Le (C co)) = []
  | alpha (Le (Bound cp)) = []
  | alpha (Le (Neg ct)) = []
  | alpha (Le (Add (cu, cv))) = []
  | alpha (Le (Sub (cw, cx))) = []
  | alpha (Le (Mul (cy, cz))) = []
  | alpha (Gt (C doa)) = []
  | alpha (Gt (Bound dp)) = []
  | alpha (Gt (Neg dt)) = []
  | alpha (Gt (Add (du, dv))) = []
  | alpha (Gt (Sub (dw, dx))) = []
  | alpha (Gt (Mul (dy, dz))) = []
  | alpha (Ge (C eo)) = []
  | alpha (Ge (Bound ep)) = []
  | alpha (Ge (Neg et)) = []
  | alpha (Ge (Add (eu, ev))) = []
  | alpha (Ge (Sub (ew, ex))) = []
  | alpha (Ge (Mul (ey, ez))) = []
  | alpha (Eq (C fo)) = []
  | alpha (Eq (Bound fp)) = []
  | alpha (Eq (Neg ft)) = []
  | alpha (Eq (Add (fu, fv))) = []
  | alpha (Eq (Sub (fw, fx))) = []
  | alpha (Eq (Mul (fy, fz))) = []
  | alpha (NEq (C go)) = []
  | alpha (NEq (Bound gp)) = []
  | alpha (NEq (Neg gt)) = []
  | alpha (NEq (Add (gu, gv))) = []
  | alpha (NEq (Sub (gw, gx))) = []
  | alpha (NEq (Mul (gy, gz))) = []
  | alpha (Dvd (aa, ab)) = []
  | alpha (NDvd (ac, ad)) = []
  | alpha (Not ae) = []
  | alpha (Imp (aj, ak)) = []
  | alpha (Iff (al, am)) = []
  | alpha (E an) = []
  | alpha (A ao) = []
  | alpha (Closed ap) = []
  | alpha (NClosed aq) = []
  | alpha (Lt (Cn (cm, c, e))) = (if eqop eq_nat cm 0 then [e] else [])
  | alpha (Le (Cn (dm, c, e))) =
    (if eqop eq_nat dm 0 then [Add (C (~1 : IntInf.int), e)] else [])
  | alpha (Gt (Cn (em, c, e))) = (if eqop eq_nat em 0 then [] else [])
  | alpha (Ge (Cn (fm, c, e))) = (if eqop eq_nat fm 0 then [] else [])
  | alpha (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0 then [Add (C (~1 : IntInf.int), e)] else [])
  | alpha (NEq (Cn (hm, c, e))) = (if eqop eq_nat hm 0 then [e] else []);

fun beta (And (p, q)) = append (beta p) (beta q)
  | beta (Or (p, q)) = append (beta p) (beta q)
  | beta T = []
  | beta F = []
  | beta (Lt (C bo)) = []
  | beta (Lt (Bound bp)) = []
  | beta (Lt (Neg bt)) = []
  | beta (Lt (Add (bu, bv))) = []
  | beta (Lt (Sub (bw, bx))) = []
  | beta (Lt (Mul (by, bz))) = []
  | beta (Le (C co)) = []
  | beta (Le (Bound cp)) = []
  | beta (Le (Neg ct)) = []
  | beta (Le (Add (cu, cv))) = []
  | beta (Le (Sub (cw, cx))) = []
  | beta (Le (Mul (cy, cz))) = []
  | beta (Gt (C doa)) = []
  | beta (Gt (Bound dp)) = []
  | beta (Gt (Neg dt)) = []
  | beta (Gt (Add (du, dv))) = []
  | beta (Gt (Sub (dw, dx))) = []
  | beta (Gt (Mul (dy, dz))) = []
  | beta (Ge (C eo)) = []
  | beta (Ge (Bound ep)) = []
  | beta (Ge (Neg et)) = []
  | beta (Ge (Add (eu, ev))) = []
  | beta (Ge (Sub (ew, ex))) = []
  | beta (Ge (Mul (ey, ez))) = []
  | beta (Eq (C fo)) = []
  | beta (Eq (Bound fp)) = []
  | beta (Eq (Neg ft)) = []
  | beta (Eq (Add (fu, fv))) = []
  | beta (Eq (Sub (fw, fx))) = []
  | beta (Eq (Mul (fy, fz))) = []
  | beta (NEq (C go)) = []
  | beta (NEq (Bound gp)) = []
  | beta (NEq (Neg gt)) = []
  | beta (NEq (Add (gu, gv))) = []
  | beta (NEq (Sub (gw, gx))) = []
  | beta (NEq (Mul (gy, gz))) = []
  | beta (Dvd (aa, ab)) = []
  | beta (NDvd (ac, ad)) = []
  | beta (Not ae) = []
  | beta (Imp (aj, ak)) = []
  | beta (Iff (al, am)) = []
  | beta (E an) = []
  | beta (A ao) = []
  | beta (Closed ap) = []
  | beta (NClosed aq) = []
  | beta (Lt (Cn (cm, c, e))) = (if eqop eq_nat cm 0 then [] else [])
  | beta (Le (Cn (dm, c, e))) = (if eqop eq_nat dm 0 then [] else [])
  | beta (Gt (Cn (em, c, e))) = (if eqop eq_nat em 0 then [Neg e] else [])
  | beta (Ge (Cn (fm, c, e))) =
    (if eqop eq_nat fm 0 then [Sub (C (~1 : IntInf.int), e)] else [])
  | beta (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0 then [Sub (C (~1 : IntInf.int), e)] else [])
  | beta (NEq (Cn (hm, c, e))) = (if eqop eq_nat hm 0 then [Neg e] else []);

fun member A_ x [] = false
  | member A_ x (y :: ys) = eqop A_ x y orelse member A_ x ys;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ x xs then remdups A_ xs else x :: remdups A_ xs);

fun delta (And (p, q)) = zlcm (delta p) (delta q)
  | delta (Or (p, q)) = zlcm (delta p) (delta q)
  | delta T = (1 : IntInf.int)
  | delta F = (1 : IntInf.int)
  | delta (Lt u) = (1 : IntInf.int)
  | delta (Le v) = (1 : IntInf.int)
  | delta (Gt w) = (1 : IntInf.int)
  | delta (Ge x) = (1 : IntInf.int)
  | delta (Eq y) = (1 : IntInf.int)
  | delta (NEq z) = (1 : IntInf.int)
  | delta (Dvd (aa, C bo)) = (1 : IntInf.int)
  | delta (Dvd (aa, Bound bp)) = (1 : IntInf.int)
  | delta (Dvd (aa, Neg bt)) = (1 : IntInf.int)
  | delta (Dvd (aa, Add (bu, bv))) = (1 : IntInf.int)
  | delta (Dvd (aa, Sub (bw, bx))) = (1 : IntInf.int)
  | delta (Dvd (aa, Mul (by, bz))) = (1 : IntInf.int)
  | delta (NDvd (ac, C co)) = (1 : IntInf.int)
  | delta (NDvd (ac, Bound cp)) = (1 : IntInf.int)
  | delta (NDvd (ac, Neg ct)) = (1 : IntInf.int)
  | delta (NDvd (ac, Add (cu, cv))) = (1 : IntInf.int)
  | delta (NDvd (ac, Sub (cw, cx))) = (1 : IntInf.int)
  | delta (NDvd (ac, Mul (cy, cz))) = (1 : IntInf.int)
  | delta (Not ae) = (1 : IntInf.int)
  | delta (Imp (aj, ak)) = (1 : IntInf.int)
  | delta (Iff (al, am)) = (1 : IntInf.int)
  | delta (E an) = (1 : IntInf.int)
  | delta (A ao) = (1 : IntInf.int)
  | delta (Closed ap) = (1 : IntInf.int)
  | delta (NClosed aq) = (1 : IntInf.int)
  | delta (Dvd (i, Cn (cm, c, e))) =
    (if eqop eq_nat cm 0 then i else (1 : IntInf.int))
  | delta (NDvd (i, Cn (dm, c, e))) =
    (if eqop eq_nat dm 0 then i else (1 : IntInf.int));

fun div_int a b = fst (divmoda a b);

fun a_beta (And (p, q)) = (fn k => And (a_beta p k, a_beta q k))
  | a_beta (Or (p, q)) = (fn k => Or (a_beta p k, a_beta q k))
  | a_beta T = (fn k => T)
  | a_beta F = (fn k => F)
  | a_beta (Lt (C bo)) = (fn k => Lt (C bo))
  | a_beta (Lt (Bound bp)) = (fn k => Lt (Bound bp))
  | a_beta (Lt (Neg bt)) = (fn k => Lt (Neg bt))
  | a_beta (Lt (Add (bu, bv))) = (fn k => Lt (Add (bu, bv)))
  | a_beta (Lt (Sub (bw, bx))) = (fn k => Lt (Sub (bw, bx)))
  | a_beta (Lt (Mul (by, bz))) = (fn k => Lt (Mul (by, bz)))
  | a_beta (Le (C co)) = (fn k => Le (C co))
  | a_beta (Le (Bound cp)) = (fn k => Le (Bound cp))
  | a_beta (Le (Neg ct)) = (fn k => Le (Neg ct))
  | a_beta (Le (Add (cu, cv))) = (fn k => Le (Add (cu, cv)))
  | a_beta (Le (Sub (cw, cx))) = (fn k => Le (Sub (cw, cx)))
  | a_beta (Le (Mul (cy, cz))) = (fn k => Le (Mul (cy, cz)))
  | a_beta (Gt (C doa)) = (fn k => Gt (C doa))
  | a_beta (Gt (Bound dp)) = (fn k => Gt (Bound dp))
  | a_beta (Gt (Neg dt)) = (fn k => Gt (Neg dt))
  | a_beta (Gt (Add (du, dv))) = (fn k => Gt (Add (du, dv)))
  | a_beta (Gt (Sub (dw, dx))) = (fn k => Gt (Sub (dw, dx)))
  | a_beta (Gt (Mul (dy, dz))) = (fn k => Gt (Mul (dy, dz)))
  | a_beta (Ge (C eo)) = (fn k => Ge (C eo))
  | a_beta (Ge (Bound ep)) = (fn k => Ge (Bound ep))
  | a_beta (Ge (Neg et)) = (fn k => Ge (Neg et))
  | a_beta (Ge (Add (eu, ev))) = (fn k => Ge (Add (eu, ev)))
  | a_beta (Ge (Sub (ew, ex))) = (fn k => Ge (Sub (ew, ex)))
  | a_beta (Ge (Mul (ey, ez))) = (fn k => Ge (Mul (ey, ez)))
  | a_beta (Eq (C fo)) = (fn k => Eq (C fo))
  | a_beta (Eq (Bound fp)) = (fn k => Eq (Bound fp))
  | a_beta (Eq (Neg ft)) = (fn k => Eq (Neg ft))
  | a_beta (Eq (Add (fu, fv))) = (fn k => Eq (Add (fu, fv)))
  | a_beta (Eq (Sub (fw, fx))) = (fn k => Eq (Sub (fw, fx)))
  | a_beta (Eq (Mul (fy, fz))) = (fn k => Eq (Mul (fy, fz)))
  | a_beta (NEq (C go)) = (fn k => NEq (C go))
  | a_beta (NEq (Bound gp)) = (fn k => NEq (Bound gp))
  | a_beta (NEq (Neg gt)) = (fn k => NEq (Neg gt))
  | a_beta (NEq (Add (gu, gv))) = (fn k => NEq (Add (gu, gv)))
  | a_beta (NEq (Sub (gw, gx))) = (fn k => NEq (Sub (gw, gx)))
  | a_beta (NEq (Mul (gy, gz))) = (fn k => NEq (Mul (gy, gz)))
  | a_beta (Dvd (aa, C ho)) = (fn k => Dvd (aa, C ho))
  | a_beta (Dvd (aa, Bound hp)) = (fn k => Dvd (aa, Bound hp))
  | a_beta (Dvd (aa, Neg ht)) = (fn k => Dvd (aa, Neg ht))
  | a_beta (Dvd (aa, Add (hu, hv))) = (fn k => Dvd (aa, Add (hu, hv)))
  | a_beta (Dvd (aa, Sub (hw, hx))) = (fn k => Dvd (aa, Sub (hw, hx)))
  | a_beta (Dvd (aa, Mul (hy, hz))) = (fn k => Dvd (aa, Mul (hy, hz)))
  | a_beta (NDvd (ac, C io)) = (fn k => NDvd (ac, C io))
  | a_beta (NDvd (ac, Bound ip)) = (fn k => NDvd (ac, Bound ip))
  | a_beta (NDvd (ac, Neg it)) = (fn k => NDvd (ac, Neg it))
  | a_beta (NDvd (ac, Add (iu, iv))) = (fn k => NDvd (ac, Add (iu, iv)))
  | a_beta (NDvd (ac, Sub (iw, ix))) = (fn k => NDvd (ac, Sub (iw, ix)))
  | a_beta (NDvd (ac, Mul (iy, iz))) = (fn k => NDvd (ac, Mul (iy, iz)))
  | a_beta (Not ae) = (fn k => Not ae)
  | a_beta (Imp (aj, ak)) = (fn k => Imp (aj, ak))
  | a_beta (Iff (al, am)) = (fn k => Iff (al, am))
  | a_beta (E an) = (fn k => E an)
  | a_beta (A ao) = (fn k => A ao)
  | a_beta (Closed ap) = (fn k => Closed ap)
  | a_beta (NClosed aq) = (fn k => NClosed aq)
  | a_beta (Lt (Cn (cm, c, e))) =
    (if eqop eq_nat cm 0
      then (fn k => Lt (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Lt (Cn (suc (minus_nat cm 1), c, e))))
  | a_beta (Le (Cn (dm, c, e))) =
    (if eqop eq_nat dm 0
      then (fn k => Le (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Le (Cn (suc (minus_nat dm 1), c, e))))
  | a_beta (Gt (Cn (em, c, e))) =
    (if eqop eq_nat em 0
      then (fn k => Gt (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Gt (Cn (suc (minus_nat em 1), c, e))))
  | a_beta (Ge (Cn (fm, c, e))) =
    (if eqop eq_nat fm 0
      then (fn k => Ge (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Ge (Cn (suc (minus_nat fm 1), c, e))))
  | a_beta (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0
      then (fn k => Eq (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Eq (Cn (suc (minus_nat gm 1), c, e))))
  | a_beta (NEq (Cn (hm, c, e))) =
    (if eqop eq_nat hm 0
      then (fn k => NEq (Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => NEq (Cn (suc (minus_nat hm 1), c, e))))
  | a_beta (Dvd (i, Cn (im, c, e))) =
    (if eqop eq_nat im 0
      then (fn k =>
             Dvd (IntInf.* (div_int k c, i),
                   Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => Dvd (i, Cn (suc (minus_nat im 1), c, e))))
  | a_beta (NDvd (i, Cn (jm, c, e))) =
    (if eqop eq_nat jm 0
      then (fn k =>
             NDvd (IntInf.* (div_int k c, i),
                    Cn (0, (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn k => NDvd (i, Cn (suc (minus_nat jm 1), c, e))));

fun zeta (And (p, q)) = zlcm (zeta p) (zeta q)
  | zeta (Or (p, q)) = zlcm (zeta p) (zeta q)
  | zeta T = (1 : IntInf.int)
  | zeta F = (1 : IntInf.int)
  | zeta (Lt (C bo)) = (1 : IntInf.int)
  | zeta (Lt (Bound bp)) = (1 : IntInf.int)
  | zeta (Lt (Neg bt)) = (1 : IntInf.int)
  | zeta (Lt (Add (bu, bv))) = (1 : IntInf.int)
  | zeta (Lt (Sub (bw, bx))) = (1 : IntInf.int)
  | zeta (Lt (Mul (by, bz))) = (1 : IntInf.int)
  | zeta (Le (C co)) = (1 : IntInf.int)
  | zeta (Le (Bound cp)) = (1 : IntInf.int)
  | zeta (Le (Neg ct)) = (1 : IntInf.int)
  | zeta (Le (Add (cu, cv))) = (1 : IntInf.int)
  | zeta (Le (Sub (cw, cx))) = (1 : IntInf.int)
  | zeta (Le (Mul (cy, cz))) = (1 : IntInf.int)
  | zeta (Gt (C doa)) = (1 : IntInf.int)
  | zeta (Gt (Bound dp)) = (1 : IntInf.int)
  | zeta (Gt (Neg dt)) = (1 : IntInf.int)
  | zeta (Gt (Add (du, dv))) = (1 : IntInf.int)
  | zeta (Gt (Sub (dw, dx))) = (1 : IntInf.int)
  | zeta (Gt (Mul (dy, dz))) = (1 : IntInf.int)
  | zeta (Ge (C eo)) = (1 : IntInf.int)
  | zeta (Ge (Bound ep)) = (1 : IntInf.int)
  | zeta (Ge (Neg et)) = (1 : IntInf.int)
  | zeta (Ge (Add (eu, ev))) = (1 : IntInf.int)
  | zeta (Ge (Sub (ew, ex))) = (1 : IntInf.int)
  | zeta (Ge (Mul (ey, ez))) = (1 : IntInf.int)
  | zeta (Eq (C fo)) = (1 : IntInf.int)
  | zeta (Eq (Bound fp)) = (1 : IntInf.int)
  | zeta (Eq (Neg ft)) = (1 : IntInf.int)
  | zeta (Eq (Add (fu, fv))) = (1 : IntInf.int)
  | zeta (Eq (Sub (fw, fx))) = (1 : IntInf.int)
  | zeta (Eq (Mul (fy, fz))) = (1 : IntInf.int)
  | zeta (NEq (C go)) = (1 : IntInf.int)
  | zeta (NEq (Bound gp)) = (1 : IntInf.int)
  | zeta (NEq (Neg gt)) = (1 : IntInf.int)
  | zeta (NEq (Add (gu, gv))) = (1 : IntInf.int)
  | zeta (NEq (Sub (gw, gx))) = (1 : IntInf.int)
  | zeta (NEq (Mul (gy, gz))) = (1 : IntInf.int)
  | zeta (Dvd (aa, C ho)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Bound hp)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Neg ht)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Add (hu, hv))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Sub (hw, hx))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Mul (hy, hz))) = (1 : IntInf.int)
  | zeta (NDvd (ac, C io)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Bound ip)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Neg it)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Add (iu, iv))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Sub (iw, ix))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Mul (iy, iz))) = (1 : IntInf.int)
  | zeta (Not ae) = (1 : IntInf.int)
  | zeta (Imp (aj, ak)) = (1 : IntInf.int)
  | zeta (Iff (al, am)) = (1 : IntInf.int)
  | zeta (E an) = (1 : IntInf.int)
  | zeta (A ao) = (1 : IntInf.int)
  | zeta (Closed ap) = (1 : IntInf.int)
  | zeta (NClosed aq) = (1 : IntInf.int)
  | zeta (Lt (Cn (cm, c, e))) =
    (if eqop eq_nat cm 0 then c else (1 : IntInf.int))
  | zeta (Le (Cn (dm, c, e))) =
    (if eqop eq_nat dm 0 then c else (1 : IntInf.int))
  | zeta (Gt (Cn (em, c, e))) =
    (if eqop eq_nat em 0 then c else (1 : IntInf.int))
  | zeta (Ge (Cn (fm, c, e))) =
    (if eqop eq_nat fm 0 then c else (1 : IntInf.int))
  | zeta (Eq (Cn (gm, c, e))) =
    (if eqop eq_nat gm 0 then c else (1 : IntInf.int))
  | zeta (NEq (Cn (hm, c, e))) =
    (if eqop eq_nat hm 0 then c else (1 : IntInf.int))
  | zeta (Dvd (i, Cn (im, c, e))) =
    (if eqop eq_nat im 0 then c else (1 : IntInf.int))
  | zeta (NDvd (i, Cn (jm, c, e))) =
    (if eqop eq_nat jm 0 then c else (1 : IntInf.int));

fun zsplit0 (C c) = ((0 : IntInf.int), C c)
  | zsplit0 (Bound n) =
    (if eqop eq_nat n 0 then ((1 : IntInf.int), C (0 : IntInf.int))
      else ((0 : IntInf.int), Bound n))
  | zsplit0 (Cn (n, i, a)) =
    let
      val aa = zsplit0 a;
      val (i', a') = aa;
    in
      (if eqop eq_nat n 0 then (IntInf.+ (i, i'), a') else (i', Cn (n, i, a')))
    end
  | zsplit0 (Neg a) =
    let
      val aa = zsplit0 a;
      val (i', a') = aa;
    in
      (IntInf.~ i', Neg a')
    end
  | zsplit0 (Add (a, b)) =
    let
      val aa = zsplit0 a;
      val (ia, a') = aa;
      val ab = zsplit0 b;
      val (ib, b') = ab;
    in
      (IntInf.+ (ia, ib), Add (a', b'))
    end
  | zsplit0 (Sub (a, b)) =
    let
      val aa = zsplit0 a;
      val (ia, a') = aa;
      val ab = zsplit0 b;
      val (ib, b') = ab;
    in
      (IntInf.- (ia, ib), Sub (a', b'))
    end
  | zsplit0 (Mul (i, a)) =
    let
      val aa = zsplit0 a;
      val (i', a') = aa;
    in
      (IntInf.* (i, i'), Mul (i, a'))
    end;

fun zlfm (And (p, q)) = And (zlfm p, zlfm q)
  | zlfm (Or (p, q)) = Or (zlfm p, zlfm q)
  | zlfm (Imp (p, q)) = Or (zlfm (Not p), zlfm q)
  | zlfm (Iff (p, q)) =
    Or (And (zlfm p, zlfm q), And (zlfm (Not p), zlfm (Not q)))
  | zlfm (Lt a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then Lt r
        else (if IntInf.< ((0 : IntInf.int), c) then Lt (Cn (0, c, r))
               else Gt (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (Le a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then Le r
        else (if IntInf.< ((0 : IntInf.int), c) then Le (Cn (0, c, r))
               else Ge (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (Gt a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then Gt r
        else (if IntInf.< ((0 : IntInf.int), c) then Gt (Cn (0, c, r))
               else Lt (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (Ge a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then Ge r
        else (if IntInf.< ((0 : IntInf.int), c) then Ge (Cn (0, c, r))
               else Le (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (Eq a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then Eq r
        else (if IntInf.< ((0 : IntInf.int), c) then Eq (Cn (0, c, r))
               else Eq (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (NEq a) =
    let
      val aa = zsplit0 a;
      val (c, r) = aa;
    in
      (if eqop eq_int c (0 : IntInf.int) then NEq r
        else (if IntInf.< ((0 : IntInf.int), c) then NEq (Cn (0, c, r))
               else NEq (Cn (0, IntInf.~ c, Neg r))))
    end
  | zlfm (Dvd (i, a)) =
    (if eqop eq_int i (0 : IntInf.int) then zlfm (Eq a)
      else let
             val aa = zsplit0 a;
             val (c, r) = aa;
           in
             (if eqop eq_int c (0 : IntInf.int) then Dvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then Dvd (abs_int i, Cn (0, c, r))
                      else Dvd (abs_int i, Cn (0, IntInf.~ c, Neg r))))
           end)
  | zlfm (NDvd (i, a)) =
    (if eqop eq_int i (0 : IntInf.int) then zlfm (NEq a)
      else let
             val aa = zsplit0 a;
             val (c, r) = aa;
           in
             (if eqop eq_int c (0 : IntInf.int) then NDvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then NDvd (abs_int i, Cn (0, c, r))
                      else NDvd (abs_int i, Cn (0, IntInf.~ c, Neg r))))
           end)
  | zlfm (Not (And (p, q))) = Or (zlfm (Not p), zlfm (Not q))
  | zlfm (Not (Or (p, q))) = And (zlfm (Not p), zlfm (Not q))
  | zlfm (Not (Imp (p, q))) = And (zlfm p, zlfm (Not q))
  | zlfm (Not (Iff (p, q))) =
    Or (And (zlfm p, zlfm (Not q)), And (zlfm (Not p), zlfm q))
  | zlfm (Not (Not p)) = zlfm p
  | zlfm (Not T) = F
  | zlfm (Not F) = T
  | zlfm (Not (Lt a)) = zlfm (Ge a)
  | zlfm (Not (Le a)) = zlfm (Gt a)
  | zlfm (Not (Gt a)) = zlfm (Le a)
  | zlfm (Not (Ge a)) = zlfm (Lt a)
  | zlfm (Not (Eq a)) = zlfm (NEq a)
  | zlfm (Not (NEq a)) = zlfm (Eq a)
  | zlfm (Not (Dvd (i, a))) = zlfm (NDvd (i, a))
  | zlfm (Not (NDvd (i, a))) = zlfm (Dvd (i, a))
  | zlfm (Not (Closed p)) = NClosed p
  | zlfm (Not (NClosed p)) = Closed p
  | zlfm T = T
  | zlfm F = F
  | zlfm (Not (E ci)) = Not (E ci)
  | zlfm (Not (A cj)) = Not (A cj)
  | zlfm (E ao) = E ao
  | zlfm (A ap) = A ap
  | zlfm (Closed aq) = Closed aq
  | zlfm (NClosed ar) = NClosed ar;

fun unita p =
  let
    val p' = zlfm p;
    val l = zeta p';
    val q =
      And (Dvd (l, Cn (0, (1 : IntInf.int), C (0 : IntInf.int))), a_beta p' l);
    val d = delta q;
    val b = remdups eq_numa (map simpnum (beta q));
    val a = remdups eq_numa (map simpnum (alpha q));
  in
    (if IntInf.<= (size_list b, size_list a) then (q, (b, d))
      else (mirror q, (a, d)))
  end;

fun cooper p =
  let
    val a = unita p;
    val (q, aa) = a;
    val (b, d) = aa;
    val js = iupt (1 : IntInf.int) d;
    val mq = simpfm (minusinf q);
    val md = evaldjf (fn j => simpfm (subst0 (C j) mq)) js;
  in
    (if eqop eq_fma md T then T
      else let
             val qd =
               evaldjf (fn ab as (ba, j) => simpfm (subst0 (Add (ba, C j)) q))
                 (concat (map (fn ba => map (fn ab => (ba, ab)) js) b));
           in
             decr (disj md qd)
           end)
  end;

fun prep (E T) = T
  | prep (E F) = F
  | prep (E (Or (p, q))) = Or (prep (E p), prep (E q))
  | prep (E (Imp (p, q))) = Or (prep (E (Not p)), prep (E q))
  | prep (E (Iff (p, q))) =
    Or (prep (E (And (p, q))), prep (E (And (Not p, Not q))))
  | prep (E (Not (And (p, q)))) = Or (prep (E (Not p)), prep (E (Not q)))
  | prep (E (Not (Imp (p, q)))) = prep (E (And (p, Not q)))
  | prep (E (Not (Iff (p, q)))) =
    Or (prep (E (And (p, Not q))), prep (E (And (Not p, q))))
  | prep (E (Lt ef)) = E (prep (Lt ef))
  | prep (E (Le eg)) = E (prep (Le eg))
  | prep (E (Gt eh)) = E (prep (Gt eh))
  | prep (E (Ge ei)) = E (prep (Ge ei))
  | prep (E (Eq ej)) = E (prep (Eq ej))
  | prep (E (NEq ek)) = E (prep (NEq ek))
  | prep (E (Dvd (el, em))) = E (prep (Dvd (el, em)))
  | prep (E (NDvd (en, eo))) = E (prep (NDvd (en, eo)))
  | prep (E (Not T)) = E (prep (Not T))
  | prep (E (Not F)) = E (prep (Not F))
  | prep (E (Not (Lt gw))) = E (prep (Not (Lt gw)))
  | prep (E (Not (Le gx))) = E (prep (Not (Le gx)))
  | prep (E (Not (Gt gy))) = E (prep (Not (Gt gy)))
  | prep (E (Not (Ge gz))) = E (prep (Not (Ge gz)))
  | prep (E (Not (Eq ha))) = E (prep (Not (Eq ha)))
  | prep (E (Not (NEq hb))) = E (prep (Not (NEq hb)))
  | prep (E (Not (Dvd (hc, hd)))) = E (prep (Not (Dvd (hc, hd))))
  | prep (E (Not (NDvd (he, hf)))) = E (prep (Not (NDvd (he, hf))))
  | prep (E (Not (Not hg))) = E (prep (Not (Not hg)))
  | prep (E (Not (Or (hj, hk)))) = E (prep (Not (Or (hj, hk))))
  | prep (E (Not (E hp))) = E (prep (Not (E hp)))
  | prep (E (Not (A hq))) = E (prep (Not (A hq)))
  | prep (E (Not (Closed hr))) = E (prep (Not (Closed hr)))
  | prep (E (Not (NClosed hs))) = E (prep (Not (NClosed hs)))
  | prep (E (And (eq, er))) = E (prep (And (eq, er)))
  | prep (E (E ey)) = E (prep (E ey))
  | prep (E (A ez)) = E (prep (A ez))
  | prep (E (Closed fa)) = E (prep (Closed fa))
  | prep (E (NClosed fb)) = E (prep (NClosed fb))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (A T) = prep (Not (E (Not T)))
  | prep (A F) = prep (Not (E (Not F)))
  | prep (A (Lt jn)) = prep (Not (E (Not (Lt jn))))
  | prep (A (Le jo)) = prep (Not (E (Not (Le jo))))
  | prep (A (Gt jp)) = prep (Not (E (Not (Gt jp))))
  | prep (A (Ge jq)) = prep (Not (E (Not (Ge jq))))
  | prep (A (Eq jr)) = prep (Not (E (Not (Eq jr))))
  | prep (A (NEq js)) = prep (Not (E (Not (NEq js))))
  | prep (A (Dvd (jt, ju))) = prep (Not (E (Not (Dvd (jt, ju)))))
  | prep (A (NDvd (jv, jw))) = prep (Not (E (Not (NDvd (jv, jw)))))
  | prep (A (Not jx)) = prep (Not (E (Not (Not jx))))
  | prep (A (Or (ka, kb))) = prep (Not (E (Not (Or (ka, kb)))))
  | prep (A (Imp (kc, kd))) = prep (Not (E (Not (Imp (kc, kd)))))
  | prep (A (Iff (ke, kf))) = prep (Not (E (Not (Iff (ke, kf)))))
  | prep (A (E kg)) = prep (Not (E (Not (E kg))))
  | prep (A (A kh)) = prep (Not (E (Not (A kh))))
  | prep (A (Closed ki)) = prep (Not (E (Not (Closed ki))))
  | prep (A (NClosed kj)) = prep (Not (E (Not (NClosed kj))))
  | prep (Not (Not p)) = prep p
  | prep (Not (And (p, q))) = Or (prep (Not p), prep (Not q))
  | prep (Not (A p)) = prep (E (Not p))
  | prep (Not (Or (p, q))) = And (prep (Not p), prep (Not q))
  | prep (Not (Imp (p, q))) = And (prep p, prep (Not q))
  | prep (Not (Iff (p, q))) = Or (prep (And (p, Not q)), prep (And (Not p, q)))
  | prep (Not T) = Not (prep T)
  | prep (Not F) = Not (prep F)
  | prep (Not (Lt bo)) = Not (prep (Lt bo))
  | prep (Not (Le bp)) = Not (prep (Le bp))
  | prep (Not (Gt bq)) = Not (prep (Gt bq))
  | prep (Not (Ge br)) = Not (prep (Ge br))
  | prep (Not (Eq bs)) = Not (prep (Eq bs))
  | prep (Not (NEq bt)) = Not (prep (NEq bt))
  | prep (Not (Dvd (bu, bv))) = Not (prep (Dvd (bu, bv)))
  | prep (Not (NDvd (bw, bx))) = Not (prep (NDvd (bw, bx)))
  | prep (Not (E ch)) = Not (prep (E ch))
  | prep (Not (Closed cj)) = Not (prep (Closed cj))
  | prep (Not (NClosed ck)) = Not (prep (NClosed ck))
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Imp (p, q)) = prep (Or (Not p, q))
  | prep (Iff (p, q)) = Or (prep (And (p, q)), prep (And (Not p, Not q)))
  | prep T = T
  | prep F = F
  | prep (Lt u) = Lt u
  | prep (Le v) = Le v
  | prep (Gt w) = Gt w
  | prep (Ge x) = Ge x
  | prep (Eq y) = Eq y
  | prep (NEq z) = NEq z
  | prep (Dvd (aa, ab)) = Dvd (aa, ab)
  | prep (NDvd (ac, ad)) = NDvd (ac, ad)
  | prep (Closed ap) = Closed ap
  | prep (NClosed aq) = NClosed aq;

fun qelim (E p) = (fn qe => dj qe (qelim p qe))
  | qelim (A p) = (fn qe => nota (qe (qelim (Not p) qe)))
  | qelim (Not p) = (fn qe => nota (qelim p qe))
  | qelim (And (p, q)) = (fn qe => conj (qelim p qe) (qelim q qe))
  | qelim (Or (p, q)) = (fn qe => disj (qelim p qe) (qelim q qe))
  | qelim (Imp (p, q)) = (fn qe => impa (qelim p qe) (qelim q qe))
  | qelim (Iff (p, q)) = (fn qe => iffa (qelim p qe) (qelim q qe))
  | qelim T = (fn y => simpfm T)
  | qelim F = (fn y => simpfm F)
  | qelim (Lt u) = (fn y => simpfm (Lt u))
  | qelim (Le v) = (fn y => simpfm (Le v))
  | qelim (Gt w) = (fn y => simpfm (Gt w))
  | qelim (Ge x) = (fn y => simpfm (Ge x))
  | qelim (Eq y) = (fn ya => simpfm (Eq y))
  | qelim (NEq z) = (fn y => simpfm (NEq z))
  | qelim (Dvd (aa, ab)) = (fn y => simpfm (Dvd (aa, ab)))
  | qelim (NDvd (ac, ad)) = (fn y => simpfm (NDvd (ac, ad)))
  | qelim (Closed ap) = (fn y => simpfm (Closed ap))
  | qelim (NClosed aq) = (fn y => simpfm (NClosed aq));

fun pa p = qelim (prep p) cooper;

fun neg z = IntInf.< (z, (0 : IntInf.int));

fun nat_aux i n =
  (if IntInf.<= (i, (0 : IntInf.int)) then n
    else nat_aux (IntInf.- (i, (1 : IntInf.int))) (suc n));

fun adjust b =
  (fn a as (q, r) =>
    (if IntInf.<= ((0 : IntInf.int), IntInf.- (r, b))
      then (IntInf.+ (IntInf.* ((2 : IntInf.int), q), (1 : IntInf.int)),
             IntInf.- (r, b))
      else (IntInf.* ((2 : IntInf.int), q), r)));

fun posDivAlg a b =
  (if IntInf.< (a, b) orelse IntInf.<= (b, (0 : IntInf.int))
    then ((0 : IntInf.int), a)
    else adjust b (posDivAlg a (IntInf.* ((2 : IntInf.int), b))));

end; (*struct GeneratedCooper*)

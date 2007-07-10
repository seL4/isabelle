(*  Title:      HOL/Tools/Presburger/generated_cooper.ML
    ID:         $Id$

This file is generated from HOL/ex/Reflected_Presburger.thy.  DO NOT EDIT.
*)

structure GeneratedCooper = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

datatype bit = B0 | B1;

fun adjust b =
  (fn a as (q, r) =>
    (if IntInf.<= ((0 : IntInf.int), IntInf.- (r, b))
      then (IntInf.+ (IntInf.* ((2 : IntInf.int), q), (1 : IntInf.int)),
             IntInf.- (r, b))
      else (IntInf.* ((2 : IntInf.int), q), r)));

fun negDivAlg a b =
  (if IntInf.<= ((0 : IntInf.int), IntInf.+ (a, b)) orelse
        IntInf.<= (b, (0 : IntInf.int))
    then ((~1 : IntInf.int), IntInf.+ (a, b))
    else adjust b (negDivAlg a (IntInf.* ((2 : IntInf.int), b))));

val negateSnd : IntInf.int * IntInf.int -> IntInf.int * IntInf.int =
  (fn a as (q, r) => (q, IntInf.~ r));

fun posDivAlg a b =
  (if IntInf.< (a, b) orelse IntInf.<= (b, (0 : IntInf.int))
    then ((0 : IntInf.int), a)
    else adjust b (posDivAlg a (IntInf.* ((2 : IntInf.int), b))));

val divAlg : IntInf.int * IntInf.int -> IntInf.int * IntInf.int =
  (fn a as (aa, b) =>
    (if IntInf.<= ((0 : IntInf.int), aa)
      then (if IntInf.<= ((0 : IntInf.int), b) then posDivAlg aa b
             else (if ((aa : IntInf.int) = (0 : IntInf.int))
                    then ((0 : IntInf.int), (0 : IntInf.int))
                    else negateSnd (negDivAlg (IntInf.~ aa) (IntInf.~ b))))
      else (if IntInf.< ((0 : IntInf.int), b) then negDivAlg aa b
             else negateSnd (posDivAlg (IntInf.~ aa) (IntInf.~ b)))));

fun snd (a, y) = y;

fun mod_nat m k = (snd (divAlg (m, k)));

val zero_nat : IntInf.int = (0 : IntInf.int);

fun gcd (m, n) =
  (if ((n : IntInf.int) = zero_nat) then m else gcd (n, mod_nat m n));

fun fst (y, b) = y;

fun div_nat m k = (fst (divAlg (m, k)));

val lcm : IntInf.int * IntInf.int -> IntInf.int =
  (fn a as (m, n) => div_nat (IntInf.* (m, n)) (gcd (m, n)));

fun suc n = (IntInf.+ (n, (1 : IntInf.int)));

fun abs_int i = (if IntInf.< (i, (0 : IntInf.int)) then IntInf.~ i else i);

fun nat k = (if IntInf.< (k, (0 : IntInf.int)) then zero_nat else k);

fun int_aux i n =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then i
    else int_aux (IntInf.+ (i, (1 : IntInf.int)))
           (IntInf.- (n, (1 : IntInf.int))));

val ilcm : IntInf.int -> IntInf.int -> IntInf.int =
  (fn i => fn j =>
    int_aux (0 : IntInf.int) (lcm (nat (abs_int i), nat (abs_int j))));

type 'a zero = {zero : 'a};
fun zero (A_:'a zero) = #zero A_;

fun map f (x :: xs) = f x :: map f xs
  | map f [] = [];

type 'a times = {times : 'a -> 'a -> 'a};
fun times (A_:'a times) = #times A_;

fun foldr f (x :: xs) a = f x (foldr f xs a)
  | foldr f [] y = y;

type 'a diva = {div : 'a -> 'a -> 'a, mod : 'a -> 'a -> 'a};
fun diva (A_:'a diva) = #div A_;
fun moda (A_:'a diva) = #mod A_;

type 'a dvd_mod =
  {Divides__dvd_mod_div : 'a diva, Divides__dvd_mod_times : 'a times,
    Divides__dvd_mod_zero : 'a zero};
fun dvd_mod_div (A_:'a dvd_mod) = #Divides__dvd_mod_div A_;
fun dvd_mod_times (A_:'a dvd_mod) = #Divides__dvd_mod_times A_;
fun dvd_mod_zero (A_:'a dvd_mod) = #Divides__dvd_mod_zero A_;

fun dvd (A1_, A2_) x y =
  eq A2_ (moda (dvd_mod_div A1_) y x) (zero (dvd_mod_zero A1_));

fun append (x :: xs) ys = x :: append xs ys
  | append [] y = y;

fun memberl A_ x (y :: ys) = eq A_ x y orelse memberl A_ x ys
  | memberl A_ x [] = false;

fun remdups A_ (x :: xs) =
  (if memberl A_ x xs then remdups A_ xs else x :: remdups A_ xs)
  | remdups A_ [] = [];

fun mod_int a b = snd (divAlg (a, b));

fun div_int a b = fst (divAlg (a, b));

val div_inta = {div = div_int, mod = mod_int} : IntInf.int diva;

fun allpairs f (x :: xs) ys = append (map (f x) ys) (allpairs f xs ys)
  | allpairs f [] ys = [];

val eq_int = {eq = (fn a => fn b => ((a : IntInf.int) = b))} : IntInf.int eq;

val zero_int : IntInf.int = (0 : IntInf.int);

val zero_inta = {zero = zero_int} : IntInf.int zero;

fun size_list (a :: lista) = (IntInf.+ ((size_list lista), (suc zero_nat)))
  | size_list [] = zero_nat;

fun eq_bit B0 B0 = true
  | eq_bit B1 B1 = true
  | eq_bit B0 B1 = false
  | eq_bit B1 B0 = false;

val times_int = {times = (fn a => fn b => IntInf.* (a, b))} : IntInf.int times;

val dvd_mod_int =
  {Divides__dvd_mod_div = div_inta, Divides__dvd_mod_times = times_int,
    Divides__dvd_mod_zero = zero_inta}
  : IntInf.int dvd_mod;

datatype num = C of IntInf.int | Bound of IntInf.int | Cx of IntInf.int * num |
  Neg of num | Add of num * num | Sub of num * num | Mul of IntInf.int * num;

datatype fm = T | F | Lt of num | Le of num | Gt of num | Ge of num | Eq of num
  | NEq of num | Dvd of IntInf.int * num | NDvd of IntInf.int * num | Nota of fm
  | And of fm * fm | Or of fm * fm | Impa of fm * fm | Iffa of fm * fm | E of fm
  | A of fm | Closed of IntInf.int | NClosed of IntInf.int;

fun disjuncts (NClosed aq) = [NClosed aq]
  | disjuncts (Closed ap) = [Closed ap]
  | disjuncts (A ao) = [A ao]
  | disjuncts (E an) = [E an]
  | disjuncts (Iffa (al, am)) = [Iffa (al, am)]
  | disjuncts (Impa (aj, ak)) = [Impa (aj, ak)]
  | disjuncts (And (af, ag)) = [And (af, ag)]
  | disjuncts (Nota ae) = [Nota ae]
  | disjuncts (NDvd (ac, ad)) = [NDvd (ac, ad)]
  | disjuncts (Dvd (aa, ab)) = [Dvd (aa, ab)]
  | disjuncts (NEq z) = [NEq z]
  | disjuncts (Eq y) = [Eq y]
  | disjuncts (Ge x) = [Ge x]
  | disjuncts (Gt w) = [Gt w]
  | disjuncts (Le v) = [Le v]
  | disjuncts (Lt u) = [Lt u]
  | disjuncts T = [T]
  | disjuncts F = []
  | disjuncts (Or (p, q)) = append (disjuncts p) (disjuncts q);

fun eq_num (C int) (C int') = ((int : IntInf.int) = int')
  | eq_num (Bound nat) (Bound nat') = ((nat : IntInf.int) = nat')
  | eq_num (Cx (int, num)) (Cx (int', num')) =
    ((int : IntInf.int) = int') andalso eq_num num num'
  | eq_num (Neg num) (Neg num') = eq_num num num'
  | eq_num (Add (num1, num2)) (Add (num1', num2')) =
    eq_num num1 num1' andalso eq_num num2 num2'
  | eq_num (Sub (num1, num2)) (Sub (num1', num2')) =
    eq_num num1 num1' andalso eq_num num2 num2'
  | eq_num (Mul (int, num)) (Mul (int', num')) =
    ((int : IntInf.int) = int') andalso eq_num num num'
  | eq_num (C a) (Bound b) = false
  | eq_num (C a) (Cx (b, c)) = false
  | eq_num (C a) (Neg b) = false
  | eq_num (C a) (Add (b, c)) = false
  | eq_num (C a) (Sub (b, c)) = false
  | eq_num (C a) (Mul (b, c)) = false
  | eq_num (Bound a) (Cx (b, c)) = false
  | eq_num (Bound a) (Neg b) = false
  | eq_num (Bound a) (Add (b, c)) = false
  | eq_num (Bound a) (Sub (b, c)) = false
  | eq_num (Bound a) (Mul (b, c)) = false
  | eq_num (Cx (a, b)) (Neg c) = false
  | eq_num (Cx (a, b)) (Add (c, d)) = false
  | eq_num (Cx (a, b)) (Sub (c, d)) = false
  | eq_num (Cx (a, b)) (Mul (c, d)) = false
  | eq_num (Neg a) (Add (b, c)) = false
  | eq_num (Neg a) (Sub (b, c)) = false
  | eq_num (Neg a) (Mul (b, c)) = false
  | eq_num (Add (a, b)) (Sub (c, d)) = false
  | eq_num (Add (a, b)) (Mul (c, d)) = false
  | eq_num (Sub (a, b)) (Mul (c, d)) = false
  | eq_num (Bound b) (C a) = false
  | eq_num (Cx (b, c)) (C a) = false
  | eq_num (Neg b) (C a) = false
  | eq_num (Add (b, c)) (C a) = false
  | eq_num (Sub (b, c)) (C a) = false
  | eq_num (Mul (b, c)) (C a) = false
  | eq_num (Cx (b, c)) (Bound a) = false
  | eq_num (Neg b) (Bound a) = false
  | eq_num (Add (b, c)) (Bound a) = false
  | eq_num (Sub (b, c)) (Bound a) = false
  | eq_num (Mul (b, c)) (Bound a) = false
  | eq_num (Neg c) (Cx (a, b)) = false
  | eq_num (Add (c, d)) (Cx (a, b)) = false
  | eq_num (Sub (c, d)) (Cx (a, b)) = false
  | eq_num (Mul (c, d)) (Cx (a, b)) = false
  | eq_num (Add (b, c)) (Neg a) = false
  | eq_num (Sub (b, c)) (Neg a) = false
  | eq_num (Mul (b, c)) (Neg a) = false
  | eq_num (Sub (c, d)) (Add (a, b)) = false
  | eq_num (Mul (c, d)) (Add (a, b)) = false
  | eq_num (Mul (c, d)) (Sub (a, b)) = false;

fun eq_fm T T = true
  | eq_fm F F = true
  | eq_fm (Lt num) (Lt num') = eq_num num num'
  | eq_fm (Le num) (Le num') = eq_num num num'
  | eq_fm (Gt num) (Gt num') = eq_num num num'
  | eq_fm (Ge num) (Ge num') = eq_num num num'
  | eq_fm (Eq num) (Eq num') = eq_num num num'
  | eq_fm (NEq num) (NEq num') = eq_num num num'
  | eq_fm (Dvd (int, num)) (Dvd (int', num')) =
    ((int : IntInf.int) = int') andalso eq_num num num'
  | eq_fm (NDvd (int, num)) (NDvd (int', num')) =
    ((int : IntInf.int) = int') andalso eq_num num num'
  | eq_fm (Nota fm) (Nota fm') = eq_fm fm fm'
  | eq_fm (And (fm1, fm2)) (And (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Or (fm1, fm2)) (Or (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Impa (fm1, fm2)) (Impa (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (Iffa (fm1, fm2)) (Iffa (fm1', fm2')) =
    eq_fm fm1 fm1' andalso eq_fm fm2 fm2'
  | eq_fm (E fm) (E fm') = eq_fm fm fm'
  | eq_fm (A fm) (A fm') = eq_fm fm fm'
  | eq_fm (Closed nat) (Closed nat') = ((nat : IntInf.int) = nat')
  | eq_fm (NClosed nat) (NClosed nat') = ((nat : IntInf.int) = nat')
  | eq_fm T F = false
  | eq_fm T (Lt a) = false
  | eq_fm T (Le a) = false
  | eq_fm T (Gt a) = false
  | eq_fm T (Ge a) = false
  | eq_fm T (Eq a) = false
  | eq_fm T (NEq a) = false
  | eq_fm T (Dvd (a, b)) = false
  | eq_fm T (NDvd (a, b)) = false
  | eq_fm T (Nota a) = false
  | eq_fm T (And (a, b)) = false
  | eq_fm T (Or (a, b)) = false
  | eq_fm T (Impa (a, b)) = false
  | eq_fm T (Iffa (a, b)) = false
  | eq_fm T (E a) = false
  | eq_fm T (A a) = false
  | eq_fm T (Closed a) = false
  | eq_fm T (NClosed a) = false
  | eq_fm F (Lt a) = false
  | eq_fm F (Le a) = false
  | eq_fm F (Gt a) = false
  | eq_fm F (Ge a) = false
  | eq_fm F (Eq a) = false
  | eq_fm F (NEq a) = false
  | eq_fm F (Dvd (a, b)) = false
  | eq_fm F (NDvd (a, b)) = false
  | eq_fm F (Nota a) = false
  | eq_fm F (And (a, b)) = false
  | eq_fm F (Or (a, b)) = false
  | eq_fm F (Impa (a, b)) = false
  | eq_fm F (Iffa (a, b)) = false
  | eq_fm F (E a) = false
  | eq_fm F (A a) = false
  | eq_fm F (Closed a) = false
  | eq_fm F (NClosed a) = false
  | eq_fm (Lt a) (Le b) = false
  | eq_fm (Lt a) (Gt b) = false
  | eq_fm (Lt a) (Ge b) = false
  | eq_fm (Lt a) (Eq b) = false
  | eq_fm (Lt a) (NEq b) = false
  | eq_fm (Lt a) (Dvd (b, c)) = false
  | eq_fm (Lt a) (NDvd (b, c)) = false
  | eq_fm (Lt a) (Nota b) = false
  | eq_fm (Lt a) (And (b, c)) = false
  | eq_fm (Lt a) (Or (b, c)) = false
  | eq_fm (Lt a) (Impa (b, c)) = false
  | eq_fm (Lt a) (Iffa (b, c)) = false
  | eq_fm (Lt a) (E b) = false
  | eq_fm (Lt a) (A b) = false
  | eq_fm (Lt a) (Closed b) = false
  | eq_fm (Lt a) (NClosed b) = false
  | eq_fm (Le a) (Gt b) = false
  | eq_fm (Le a) (Ge b) = false
  | eq_fm (Le a) (Eq b) = false
  | eq_fm (Le a) (NEq b) = false
  | eq_fm (Le a) (Dvd (b, c)) = false
  | eq_fm (Le a) (NDvd (b, c)) = false
  | eq_fm (Le a) (Nota b) = false
  | eq_fm (Le a) (And (b, c)) = false
  | eq_fm (Le a) (Or (b, c)) = false
  | eq_fm (Le a) (Impa (b, c)) = false
  | eq_fm (Le a) (Iffa (b, c)) = false
  | eq_fm (Le a) (E b) = false
  | eq_fm (Le a) (A b) = false
  | eq_fm (Le a) (Closed b) = false
  | eq_fm (Le a) (NClosed b) = false
  | eq_fm (Gt a) (Ge b) = false
  | eq_fm (Gt a) (Eq b) = false
  | eq_fm (Gt a) (NEq b) = false
  | eq_fm (Gt a) (Dvd (b, c)) = false
  | eq_fm (Gt a) (NDvd (b, c)) = false
  | eq_fm (Gt a) (Nota b) = false
  | eq_fm (Gt a) (And (b, c)) = false
  | eq_fm (Gt a) (Or (b, c)) = false
  | eq_fm (Gt a) (Impa (b, c)) = false
  | eq_fm (Gt a) (Iffa (b, c)) = false
  | eq_fm (Gt a) (E b) = false
  | eq_fm (Gt a) (A b) = false
  | eq_fm (Gt a) (Closed b) = false
  | eq_fm (Gt a) (NClosed b) = false
  | eq_fm (Ge a) (Eq b) = false
  | eq_fm (Ge a) (NEq b) = false
  | eq_fm (Ge a) (Dvd (b, c)) = false
  | eq_fm (Ge a) (NDvd (b, c)) = false
  | eq_fm (Ge a) (Nota b) = false
  | eq_fm (Ge a) (And (b, c)) = false
  | eq_fm (Ge a) (Or (b, c)) = false
  | eq_fm (Ge a) (Impa (b, c)) = false
  | eq_fm (Ge a) (Iffa (b, c)) = false
  | eq_fm (Ge a) (E b) = false
  | eq_fm (Ge a) (A b) = false
  | eq_fm (Ge a) (Closed b) = false
  | eq_fm (Ge a) (NClosed b) = false
  | eq_fm (Eq a) (NEq b) = false
  | eq_fm (Eq a) (Dvd (b, c)) = false
  | eq_fm (Eq a) (NDvd (b, c)) = false
  | eq_fm (Eq a) (Nota b) = false
  | eq_fm (Eq a) (And (b, c)) = false
  | eq_fm (Eq a) (Or (b, c)) = false
  | eq_fm (Eq a) (Impa (b, c)) = false
  | eq_fm (Eq a) (Iffa (b, c)) = false
  | eq_fm (Eq a) (E b) = false
  | eq_fm (Eq a) (A b) = false
  | eq_fm (Eq a) (Closed b) = false
  | eq_fm (Eq a) (NClosed b) = false
  | eq_fm (NEq a) (Dvd (b, c)) = false
  | eq_fm (NEq a) (NDvd (b, c)) = false
  | eq_fm (NEq a) (Nota b) = false
  | eq_fm (NEq a) (And (b, c)) = false
  | eq_fm (NEq a) (Or (b, c)) = false
  | eq_fm (NEq a) (Impa (b, c)) = false
  | eq_fm (NEq a) (Iffa (b, c)) = false
  | eq_fm (NEq a) (E b) = false
  | eq_fm (NEq a) (A b) = false
  | eq_fm (NEq a) (Closed b) = false
  | eq_fm (NEq a) (NClosed b) = false
  | eq_fm (Dvd (a, b)) (NDvd (c, d)) = false
  | eq_fm (Dvd (a, b)) (Nota c) = false
  | eq_fm (Dvd (a, b)) (And (c, d)) = false
  | eq_fm (Dvd (a, b)) (Or (c, d)) = false
  | eq_fm (Dvd (a, b)) (Impa (c, d)) = false
  | eq_fm (Dvd (a, b)) (Iffa (c, d)) = false
  | eq_fm (Dvd (a, b)) (E c) = false
  | eq_fm (Dvd (a, b)) (A c) = false
  | eq_fm (Dvd (a, b)) (Closed c) = false
  | eq_fm (Dvd (a, b)) (NClosed c) = false
  | eq_fm (NDvd (a, b)) (Nota c) = false
  | eq_fm (NDvd (a, b)) (And (c, d)) = false
  | eq_fm (NDvd (a, b)) (Or (c, d)) = false
  | eq_fm (NDvd (a, b)) (Impa (c, d)) = false
  | eq_fm (NDvd (a, b)) (Iffa (c, d)) = false
  | eq_fm (NDvd (a, b)) (E c) = false
  | eq_fm (NDvd (a, b)) (A c) = false
  | eq_fm (NDvd (a, b)) (Closed c) = false
  | eq_fm (NDvd (a, b)) (NClosed c) = false
  | eq_fm (Nota a) (And (b, c)) = false
  | eq_fm (Nota a) (Or (b, c)) = false
  | eq_fm (Nota a) (Impa (b, c)) = false
  | eq_fm (Nota a) (Iffa (b, c)) = false
  | eq_fm (Nota a) (E b) = false
  | eq_fm (Nota a) (A b) = false
  | eq_fm (Nota a) (Closed b) = false
  | eq_fm (Nota a) (NClosed b) = false
  | eq_fm (And (a, b)) (Or (c, d)) = false
  | eq_fm (And (a, b)) (Impa (c, d)) = false
  | eq_fm (And (a, b)) (Iffa (c, d)) = false
  | eq_fm (And (a, b)) (E c) = false
  | eq_fm (And (a, b)) (A c) = false
  | eq_fm (And (a, b)) (Closed c) = false
  | eq_fm (And (a, b)) (NClosed c) = false
  | eq_fm (Or (a, b)) (Impa (c, d)) = false
  | eq_fm (Or (a, b)) (Iffa (c, d)) = false
  | eq_fm (Or (a, b)) (E c) = false
  | eq_fm (Or (a, b)) (A c) = false
  | eq_fm (Or (a, b)) (Closed c) = false
  | eq_fm (Or (a, b)) (NClosed c) = false
  | eq_fm (Impa (a, b)) (Iffa (c, d)) = false
  | eq_fm (Impa (a, b)) (E c) = false
  | eq_fm (Impa (a, b)) (A c) = false
  | eq_fm (Impa (a, b)) (Closed c) = false
  | eq_fm (Impa (a, b)) (NClosed c) = false
  | eq_fm (Iffa (a, b)) (E c) = false
  | eq_fm (Iffa (a, b)) (A c) = false
  | eq_fm (Iffa (a, b)) (Closed c) = false
  | eq_fm (Iffa (a, b)) (NClosed c) = false
  | eq_fm (E a) (A b) = false
  | eq_fm (E a) (Closed b) = false
  | eq_fm (E a) (NClosed b) = false
  | eq_fm (A a) (Closed b) = false
  | eq_fm (A a) (NClosed b) = false
  | eq_fm (Closed a) (NClosed b) = false
  | eq_fm F T = false
  | eq_fm (Lt a) T = false
  | eq_fm (Le a) T = false
  | eq_fm (Gt a) T = false
  | eq_fm (Ge a) T = false
  | eq_fm (Eq a) T = false
  | eq_fm (NEq a) T = false
  | eq_fm (Dvd (a, b)) T = false
  | eq_fm (NDvd (a, b)) T = false
  | eq_fm (Nota a) T = false
  | eq_fm (And (a, b)) T = false
  | eq_fm (Or (a, b)) T = false
  | eq_fm (Impa (a, b)) T = false
  | eq_fm (Iffa (a, b)) T = false
  | eq_fm (E a) T = false
  | eq_fm (A a) T = false
  | eq_fm (Closed a) T = false
  | eq_fm (NClosed a) T = false
  | eq_fm (Lt a) F = false
  | eq_fm (Le a) F = false
  | eq_fm (Gt a) F = false
  | eq_fm (Ge a) F = false
  | eq_fm (Eq a) F = false
  | eq_fm (NEq a) F = false
  | eq_fm (Dvd (a, b)) F = false
  | eq_fm (NDvd (a, b)) F = false
  | eq_fm (Nota a) F = false
  | eq_fm (And (a, b)) F = false
  | eq_fm (Or (a, b)) F = false
  | eq_fm (Impa (a, b)) F = false
  | eq_fm (Iffa (a, b)) F = false
  | eq_fm (E a) F = false
  | eq_fm (A a) F = false
  | eq_fm (Closed a) F = false
  | eq_fm (NClosed a) F = false
  | eq_fm (Le b) (Lt a) = false
  | eq_fm (Gt b) (Lt a) = false
  | eq_fm (Ge b) (Lt a) = false
  | eq_fm (Eq b) (Lt a) = false
  | eq_fm (NEq b) (Lt a) = false
  | eq_fm (Dvd (b, c)) (Lt a) = false
  | eq_fm (NDvd (b, c)) (Lt a) = false
  | eq_fm (Nota b) (Lt a) = false
  | eq_fm (And (b, c)) (Lt a) = false
  | eq_fm (Or (b, c)) (Lt a) = false
  | eq_fm (Impa (b, c)) (Lt a) = false
  | eq_fm (Iffa (b, c)) (Lt a) = false
  | eq_fm (E b) (Lt a) = false
  | eq_fm (A b) (Lt a) = false
  | eq_fm (Closed b) (Lt a) = false
  | eq_fm (NClosed b) (Lt a) = false
  | eq_fm (Gt b) (Le a) = false
  | eq_fm (Ge b) (Le a) = false
  | eq_fm (Eq b) (Le a) = false
  | eq_fm (NEq b) (Le a) = false
  | eq_fm (Dvd (b, c)) (Le a) = false
  | eq_fm (NDvd (b, c)) (Le a) = false
  | eq_fm (Nota b) (Le a) = false
  | eq_fm (And (b, c)) (Le a) = false
  | eq_fm (Or (b, c)) (Le a) = false
  | eq_fm (Impa (b, c)) (Le a) = false
  | eq_fm (Iffa (b, c)) (Le a) = false
  | eq_fm (E b) (Le a) = false
  | eq_fm (A b) (Le a) = false
  | eq_fm (Closed b) (Le a) = false
  | eq_fm (NClosed b) (Le a) = false
  | eq_fm (Ge b) (Gt a) = false
  | eq_fm (Eq b) (Gt a) = false
  | eq_fm (NEq b) (Gt a) = false
  | eq_fm (Dvd (b, c)) (Gt a) = false
  | eq_fm (NDvd (b, c)) (Gt a) = false
  | eq_fm (Nota b) (Gt a) = false
  | eq_fm (And (b, c)) (Gt a) = false
  | eq_fm (Or (b, c)) (Gt a) = false
  | eq_fm (Impa (b, c)) (Gt a) = false
  | eq_fm (Iffa (b, c)) (Gt a) = false
  | eq_fm (E b) (Gt a) = false
  | eq_fm (A b) (Gt a) = false
  | eq_fm (Closed b) (Gt a) = false
  | eq_fm (NClosed b) (Gt a) = false
  | eq_fm (Eq b) (Ge a) = false
  | eq_fm (NEq b) (Ge a) = false
  | eq_fm (Dvd (b, c)) (Ge a) = false
  | eq_fm (NDvd (b, c)) (Ge a) = false
  | eq_fm (Nota b) (Ge a) = false
  | eq_fm (And (b, c)) (Ge a) = false
  | eq_fm (Or (b, c)) (Ge a) = false
  | eq_fm (Impa (b, c)) (Ge a) = false
  | eq_fm (Iffa (b, c)) (Ge a) = false
  | eq_fm (E b) (Ge a) = false
  | eq_fm (A b) (Ge a) = false
  | eq_fm (Closed b) (Ge a) = false
  | eq_fm (NClosed b) (Ge a) = false
  | eq_fm (NEq b) (Eq a) = false
  | eq_fm (Dvd (b, c)) (Eq a) = false
  | eq_fm (NDvd (b, c)) (Eq a) = false
  | eq_fm (Nota b) (Eq a) = false
  | eq_fm (And (b, c)) (Eq a) = false
  | eq_fm (Or (b, c)) (Eq a) = false
  | eq_fm (Impa (b, c)) (Eq a) = false
  | eq_fm (Iffa (b, c)) (Eq a) = false
  | eq_fm (E b) (Eq a) = false
  | eq_fm (A b) (Eq a) = false
  | eq_fm (Closed b) (Eq a) = false
  | eq_fm (NClosed b) (Eq a) = false
  | eq_fm (Dvd (b, c)) (NEq a) = false
  | eq_fm (NDvd (b, c)) (NEq a) = false
  | eq_fm (Nota b) (NEq a) = false
  | eq_fm (And (b, c)) (NEq a) = false
  | eq_fm (Or (b, c)) (NEq a) = false
  | eq_fm (Impa (b, c)) (NEq a) = false
  | eq_fm (Iffa (b, c)) (NEq a) = false
  | eq_fm (E b) (NEq a) = false
  | eq_fm (A b) (NEq a) = false
  | eq_fm (Closed b) (NEq a) = false
  | eq_fm (NClosed b) (NEq a) = false
  | eq_fm (NDvd (c, d)) (Dvd (a, b)) = false
  | eq_fm (Nota c) (Dvd (a, b)) = false
  | eq_fm (And (c, d)) (Dvd (a, b)) = false
  | eq_fm (Or (c, d)) (Dvd (a, b)) = false
  | eq_fm (Impa (c, d)) (Dvd (a, b)) = false
  | eq_fm (Iffa (c, d)) (Dvd (a, b)) = false
  | eq_fm (E c) (Dvd (a, b)) = false
  | eq_fm (A c) (Dvd (a, b)) = false
  | eq_fm (Closed c) (Dvd (a, b)) = false
  | eq_fm (NClosed c) (Dvd (a, b)) = false
  | eq_fm (Nota c) (NDvd (a, b)) = false
  | eq_fm (And (c, d)) (NDvd (a, b)) = false
  | eq_fm (Or (c, d)) (NDvd (a, b)) = false
  | eq_fm (Impa (c, d)) (NDvd (a, b)) = false
  | eq_fm (Iffa (c, d)) (NDvd (a, b)) = false
  | eq_fm (E c) (NDvd (a, b)) = false
  | eq_fm (A c) (NDvd (a, b)) = false
  | eq_fm (Closed c) (NDvd (a, b)) = false
  | eq_fm (NClosed c) (NDvd (a, b)) = false
  | eq_fm (And (b, c)) (Nota a) = false
  | eq_fm (Or (b, c)) (Nota a) = false
  | eq_fm (Impa (b, c)) (Nota a) = false
  | eq_fm (Iffa (b, c)) (Nota a) = false
  | eq_fm (E b) (Nota a) = false
  | eq_fm (A b) (Nota a) = false
  | eq_fm (Closed b) (Nota a) = false
  | eq_fm (NClosed b) (Nota a) = false
  | eq_fm (Or (c, d)) (And (a, b)) = false
  | eq_fm (Impa (c, d)) (And (a, b)) = false
  | eq_fm (Iffa (c, d)) (And (a, b)) = false
  | eq_fm (E c) (And (a, b)) = false
  | eq_fm (A c) (And (a, b)) = false
  | eq_fm (Closed c) (And (a, b)) = false
  | eq_fm (NClosed c) (And (a, b)) = false
  | eq_fm (Impa (c, d)) (Or (a, b)) = false
  | eq_fm (Iffa (c, d)) (Or (a, b)) = false
  | eq_fm (E c) (Or (a, b)) = false
  | eq_fm (A c) (Or (a, b)) = false
  | eq_fm (Closed c) (Or (a, b)) = false
  | eq_fm (NClosed c) (Or (a, b)) = false
  | eq_fm (Iffa (c, d)) (Impa (a, b)) = false
  | eq_fm (E c) (Impa (a, b)) = false
  | eq_fm (A c) (Impa (a, b)) = false
  | eq_fm (Closed c) (Impa (a, b)) = false
  | eq_fm (NClosed c) (Impa (a, b)) = false
  | eq_fm (E c) (Iffa (a, b)) = false
  | eq_fm (A c) (Iffa (a, b)) = false
  | eq_fm (Closed c) (Iffa (a, b)) = false
  | eq_fm (NClosed c) (Iffa (a, b)) = false
  | eq_fm (A b) (E a) = false
  | eq_fm (Closed b) (E a) = false
  | eq_fm (NClosed b) (E a) = false
  | eq_fm (Closed b) (A a) = false
  | eq_fm (NClosed b) (A a) = false
  | eq_fm (NClosed b) (Closed a) = false;

fun djf f p q =
  (if eq_fm q T then T
    else (if eq_fm q F then f p
           else (case f p of T => T | F => q | Lt num => Or (f p, q)
                   | Le num => Or (f p, q) | Gt num => Or (f p, q)
                   | Ge num => Or (f p, q) | Eq num => Or (f p, q)
                   | NEq num => Or (f p, q) | Dvd (int, num) => Or (f p, q)
                   | NDvd (int, num) => Or (f p, q) | Nota fm => Or (f p, q)
                   | And (fm1, fm2) => Or (f p, q)
                   | Or (fm1, fm2) => Or (f p, q)
                   | Impa (fm1, fm2) => Or (f p, q)
                   | Iffa (fm1, fm2) => Or (f p, q) | E fm => Or (f p, q)
                   | A fm => Or (f p, q) | Closed nat => Or (f p, q)
                   | NClosed nat => Or (f p, q))));

fun evaldjf f ps = foldr (djf f) ps F;

fun dj f p = evaldjf f (disjuncts p);

fun zsplit0 (Mul (i, a)) =
  let
    val (i', a') = zsplit0 a;
  in
    (IntInf.* (i, i'), Mul (i, a'))
  end
  | zsplit0 (Sub (a, b)) =
    let
      val (ia, a') = zsplit0 a;
      val (ib, b') = zsplit0 b;
    in
      (IntInf.- (ia, ib), Sub (a', b'))
    end
  | zsplit0 (Add (a, b)) =
    let
      val (ia, a') = zsplit0 a;
      val (ib, b') = zsplit0 b;
    in
      (IntInf.+ (ia, ib), Add (a', b'))
    end
  | zsplit0 (Neg a) =
    let
      val (i', a') = zsplit0 a;
    in
      (IntInf.~ i', Neg a')
    end
  | zsplit0 (Cx (i, a)) =
    let
      val (i', aa) = zsplit0 a;
    in
      (IntInf.+ (i, i'), aa)
    end
  | zsplit0 (Bound n) =
    (if ((n : IntInf.int) = zero_nat)
      then ((1 : IntInf.int), C (0 : IntInf.int))
      else ((0 : IntInf.int), Bound n))
  | zsplit0 (C c) = ((0 : IntInf.int), C c);

fun zlfm (NClosed ar) = NClosed ar
  | zlfm (Closed aq) = Closed aq
  | zlfm (A ap) = A ap
  | zlfm (E ao) = E ao
  | zlfm (Nota (A cj)) = Nota (A cj)
  | zlfm (Nota (E ci)) = Nota (E ci)
  | zlfm F = F
  | zlfm T = T
  | zlfm (Nota (NClosed p)) = Closed p
  | zlfm (Nota (Closed p)) = NClosed p
  | zlfm (Nota (NDvd (i, a))) = zlfm (Dvd (i, a))
  | zlfm (Nota (Dvd (i, a))) = zlfm (NDvd (i, a))
  | zlfm (Nota (NEq a)) = zlfm (Eq a)
  | zlfm (Nota (Eq a)) = zlfm (NEq a)
  | zlfm (Nota (Ge a)) = zlfm (Lt a)
  | zlfm (Nota (Gt a)) = zlfm (Le a)
  | zlfm (Nota (Le a)) = zlfm (Gt a)
  | zlfm (Nota (Lt a)) = zlfm (Ge a)
  | zlfm (Nota F) = T
  | zlfm (Nota T) = F
  | zlfm (Nota (Nota p)) = zlfm p
  | zlfm (Nota (Iffa (p, q))) =
    Or (And (zlfm p, zlfm (Nota q)), And (zlfm (Nota p), zlfm q))
  | zlfm (Nota (Impa (p, q))) = And (zlfm p, zlfm (Nota q))
  | zlfm (Nota (Or (p, q))) = And (zlfm (Nota p), zlfm (Nota q))
  | zlfm (Nota (And (p, q))) = Or (zlfm (Nota p), zlfm (Nota q))
  | zlfm (NDvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then zlfm (NEq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if ((c : IntInf.int) = (0 : IntInf.int)) then NDvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then NDvd (abs_int i, Cx (c, r))
                      else NDvd (abs_int i, Cx (IntInf.~ c, Neg r))))
           end)
  | zlfm (Dvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then zlfm (Eq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if ((c : IntInf.int) = (0 : IntInf.int)) then Dvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then Dvd (abs_int i, Cx (c, r))
                      else Dvd (abs_int i, Cx (IntInf.~ c, Neg r))))
           end)
  | zlfm (NEq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then NEq r
        else (if IntInf.< ((0 : IntInf.int), c) then NEq (Cx (c, r))
               else NEq (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Eq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Eq r
        else (if IntInf.< ((0 : IntInf.int), c) then Eq (Cx (c, r))
               else Eq (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Ge a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Ge r
        else (if IntInf.< ((0 : IntInf.int), c) then Ge (Cx (c, r))
               else Le (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Gt a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Gt r
        else (if IntInf.< ((0 : IntInf.int), c) then Gt (Cx (c, r))
               else Lt (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Le a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Le r
        else (if IntInf.< ((0 : IntInf.int), c) then Le (Cx (c, r))
               else Ge (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Lt a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Lt r
        else (if IntInf.< ((0 : IntInf.int), c) then Lt (Cx (c, r))
               else Gt (Cx (IntInf.~ c, Neg r))))
    end
  | zlfm (Iffa (p, q)) =
    Or (And (zlfm p, zlfm q), And (zlfm (Nota p), zlfm (Nota q)))
  | zlfm (Impa (p, q)) = Or (zlfm (Nota p), zlfm q)
  | zlfm (Or (p, q)) = Or (zlfm p, zlfm q)
  | zlfm (And (p, q)) = And (zlfm p, zlfm q);

fun zeta (NClosed aq) = (1 : IntInf.int)
  | zeta (Closed ap) = (1 : IntInf.int)
  | zeta (A ao) = (1 : IntInf.int)
  | zeta (E an) = (1 : IntInf.int)
  | zeta (Iffa (al, am)) = (1 : IntInf.int)
  | zeta (Impa (aj, ak)) = (1 : IntInf.int)
  | zeta (Nota ae) = (1 : IntInf.int)
  | zeta (NDvd (ac, Mul (hv, hw))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Sub (ht, hu))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Add (hr, hs))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Neg hq)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Bound hn)) = (1 : IntInf.int)
  | zeta (NDvd (ac, C hm)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Mul (gz, ha))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Sub (gx, gy))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Add (gv, gw))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Neg gu)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Bound gr)) = (1 : IntInf.int)
  | zeta (Dvd (aa, C gq)) = (1 : IntInf.int)
  | zeta (NEq (Mul (gd, ge))) = (1 : IntInf.int)
  | zeta (NEq (Sub (gb, gc))) = (1 : IntInf.int)
  | zeta (NEq (Add (fz, ga))) = (1 : IntInf.int)
  | zeta (NEq (Neg fy)) = (1 : IntInf.int)
  | zeta (NEq (Bound fv)) = (1 : IntInf.int)
  | zeta (NEq (C fu)) = (1 : IntInf.int)
  | zeta (Eq (Mul (fh, fi))) = (1 : IntInf.int)
  | zeta (Eq (Sub (ff, fg))) = (1 : IntInf.int)
  | zeta (Eq (Add (fd, fe))) = (1 : IntInf.int)
  | zeta (Eq (Neg fc)) = (1 : IntInf.int)
  | zeta (Eq (Bound ez)) = (1 : IntInf.int)
  | zeta (Eq (C ey)) = (1 : IntInf.int)
  | zeta (Ge (Mul (el, em))) = (1 : IntInf.int)
  | zeta (Ge (Sub (ej, ek))) = (1 : IntInf.int)
  | zeta (Ge (Add (eh, ei))) = (1 : IntInf.int)
  | zeta (Ge (Neg eg)) = (1 : IntInf.int)
  | zeta (Ge (Bound ed)) = (1 : IntInf.int)
  | zeta (Ge (C ec)) = (1 : IntInf.int)
  | zeta (Gt (Mul (dp, dq))) = (1 : IntInf.int)
  | zeta (Gt (Sub (dn, doa))) = (1 : IntInf.int)
  | zeta (Gt (Add (dl, dm))) = (1 : IntInf.int)
  | zeta (Gt (Neg dk)) = (1 : IntInf.int)
  | zeta (Gt (Bound dh)) = (1 : IntInf.int)
  | zeta (Gt (C dg)) = (1 : IntInf.int)
  | zeta (Le (Mul (ct, cu))) = (1 : IntInf.int)
  | zeta (Le (Sub (cr, cs))) = (1 : IntInf.int)
  | zeta (Le (Add (cp, cq))) = (1 : IntInf.int)
  | zeta (Le (Neg co)) = (1 : IntInf.int)
  | zeta (Le (Bound cl)) = (1 : IntInf.int)
  | zeta (Le (C ck)) = (1 : IntInf.int)
  | zeta (Lt (Mul (bx, by))) = (1 : IntInf.int)
  | zeta (Lt (Sub (bv, bw))) = (1 : IntInf.int)
  | zeta (Lt (Add (bt, bu))) = (1 : IntInf.int)
  | zeta (Lt (Neg bs)) = (1 : IntInf.int)
  | zeta (Lt (Bound bp)) = (1 : IntInf.int)
  | zeta (Lt (C bo)) = (1 : IntInf.int)
  | zeta F = (1 : IntInf.int)
  | zeta T = (1 : IntInf.int)
  | zeta (NDvd (i, Cx (y, e))) = y
  | zeta (Dvd (i, Cx (y, e))) = y
  | zeta (Ge (Cx (y, e))) = y
  | zeta (Gt (Cx (y, e))) = y
  | zeta (Le (Cx (y, e))) = y
  | zeta (Lt (Cx (y, e))) = y
  | zeta (NEq (Cx (y, e))) = y
  | zeta (Eq (Cx (y, e))) = y
  | zeta (Or (p, q)) = ilcm (zeta p) (zeta q)
  | zeta (And (p, q)) = ilcm (zeta p) (zeta q);

fun a_beta (NClosed aq) = (fn k => NClosed aq)
  | a_beta (Closed ap) = (fn k => Closed ap)
  | a_beta (A ao) = (fn k => A ao)
  | a_beta (E an) = (fn k => E an)
  | a_beta (Iffa (al, am)) = (fn k => Iffa (al, am))
  | a_beta (Impa (aj, ak)) = (fn k => Impa (aj, ak))
  | a_beta (Nota ae) = (fn k => Nota ae)
  | a_beta (NDvd (ac, Mul (hv, hw))) = (fn k => NDvd (ac, Mul (hv, hw)))
  | a_beta (NDvd (ac, Sub (ht, hu))) = (fn k => NDvd (ac, Sub (ht, hu)))
  | a_beta (NDvd (ac, Add (hr, hs))) = (fn k => NDvd (ac, Add (hr, hs)))
  | a_beta (NDvd (ac, Neg hq)) = (fn k => NDvd (ac, Neg hq))
  | a_beta (NDvd (ac, Bound hn)) = (fn k => NDvd (ac, Bound hn))
  | a_beta (NDvd (ac, C hm)) = (fn k => NDvd (ac, C hm))
  | a_beta (Dvd (aa, Mul (gz, ha))) = (fn k => Dvd (aa, Mul (gz, ha)))
  | a_beta (Dvd (aa, Sub (gx, gy))) = (fn k => Dvd (aa, Sub (gx, gy)))
  | a_beta (Dvd (aa, Add (gv, gw))) = (fn k => Dvd (aa, Add (gv, gw)))
  | a_beta (Dvd (aa, Neg gu)) = (fn k => Dvd (aa, Neg gu))
  | a_beta (Dvd (aa, Bound gr)) = (fn k => Dvd (aa, Bound gr))
  | a_beta (Dvd (aa, C gq)) = (fn k => Dvd (aa, C gq))
  | a_beta (NEq (Mul (gd, ge))) = (fn k => NEq (Mul (gd, ge)))
  | a_beta (NEq (Sub (gb, gc))) = (fn k => NEq (Sub (gb, gc)))
  | a_beta (NEq (Add (fz, ga))) = (fn k => NEq (Add (fz, ga)))
  | a_beta (NEq (Neg fy)) = (fn k => NEq (Neg fy))
  | a_beta (NEq (Bound fv)) = (fn k => NEq (Bound fv))
  | a_beta (NEq (C fu)) = (fn k => NEq (C fu))
  | a_beta (Eq (Mul (fh, fi))) = (fn k => Eq (Mul (fh, fi)))
  | a_beta (Eq (Sub (ff, fg))) = (fn k => Eq (Sub (ff, fg)))
  | a_beta (Eq (Add (fd, fe))) = (fn k => Eq (Add (fd, fe)))
  | a_beta (Eq (Neg fc)) = (fn k => Eq (Neg fc))
  | a_beta (Eq (Bound ez)) = (fn k => Eq (Bound ez))
  | a_beta (Eq (C ey)) = (fn k => Eq (C ey))
  | a_beta (Ge (Mul (el, em))) = (fn k => Ge (Mul (el, em)))
  | a_beta (Ge (Sub (ej, ek))) = (fn k => Ge (Sub (ej, ek)))
  | a_beta (Ge (Add (eh, ei))) = (fn k => Ge (Add (eh, ei)))
  | a_beta (Ge (Neg eg)) = (fn k => Ge (Neg eg))
  | a_beta (Ge (Bound ed)) = (fn k => Ge (Bound ed))
  | a_beta (Ge (C ec)) = (fn k => Ge (C ec))
  | a_beta (Gt (Mul (dp, dq))) = (fn k => Gt (Mul (dp, dq)))
  | a_beta (Gt (Sub (dn, doa))) = (fn k => Gt (Sub (dn, doa)))
  | a_beta (Gt (Add (dl, dm))) = (fn k => Gt (Add (dl, dm)))
  | a_beta (Gt (Neg dk)) = (fn k => Gt (Neg dk))
  | a_beta (Gt (Bound dh)) = (fn k => Gt (Bound dh))
  | a_beta (Gt (C dg)) = (fn k => Gt (C dg))
  | a_beta (Le (Mul (ct, cu))) = (fn k => Le (Mul (ct, cu)))
  | a_beta (Le (Sub (cr, cs))) = (fn k => Le (Sub (cr, cs)))
  | a_beta (Le (Add (cp, cq))) = (fn k => Le (Add (cp, cq)))
  | a_beta (Le (Neg co)) = (fn k => Le (Neg co))
  | a_beta (Le (Bound cl)) = (fn k => Le (Bound cl))
  | a_beta (Le (C ck)) = (fn k => Le (C ck))
  | a_beta (Lt (Mul (bx, by))) = (fn k => Lt (Mul (bx, by)))
  | a_beta (Lt (Sub (bv, bw))) = (fn k => Lt (Sub (bv, bw)))
  | a_beta (Lt (Add (bt, bu))) = (fn k => Lt (Add (bt, bu)))
  | a_beta (Lt (Neg bs)) = (fn k => Lt (Neg bs))
  | a_beta (Lt (Bound bp)) = (fn k => Lt (Bound bp))
  | a_beta (Lt (C bo)) = (fn k => Lt (C bo))
  | a_beta F = (fn k => F)
  | a_beta T = (fn k => T)
  | a_beta (NDvd (i, Cx (c, e))) =
    (fn k =>
      NDvd (IntInf.* (div_int k c, i),
             Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Dvd (i, Cx (c, e))) =
    (fn k =>
      Dvd (IntInf.* (div_int k c, i),
            Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Ge (Cx (c, e))) =
    (fn k => Ge (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Gt (Cx (c, e))) =
    (fn k => Gt (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Le (Cx (c, e))) =
    (fn k => Le (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Lt (Cx (c, e))) =
    (fn k => Lt (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (NEq (Cx (c, e))) =
    (fn k => NEq (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Eq (Cx (c, e))) =
    (fn k => Eq (Cx ((1 : IntInf.int), Mul (div_int k c, e))))
  | a_beta (Or (p, q)) = (fn k => Or (a_beta p k, a_beta q k))
  | a_beta (And (p, q)) = (fn k => And (a_beta p k, a_beta q k));

fun delta (NClosed aq) = (1 : IntInf.int)
  | delta (Closed ap) = (1 : IntInf.int)
  | delta (A ao) = (1 : IntInf.int)
  | delta (E an) = (1 : IntInf.int)
  | delta (Iffa (al, am)) = (1 : IntInf.int)
  | delta (Impa (aj, ak)) = (1 : IntInf.int)
  | delta (Nota ae) = (1 : IntInf.int)
  | delta (NDvd (ac, Mul (ct, cu))) = (1 : IntInf.int)
  | delta (NDvd (ac, Sub (cr, cs))) = (1 : IntInf.int)
  | delta (NDvd (ac, Add (cp, cq))) = (1 : IntInf.int)
  | delta (NDvd (ac, Neg co)) = (1 : IntInf.int)
  | delta (NDvd (ac, Bound cl)) = (1 : IntInf.int)
  | delta (NDvd (ac, C ck)) = (1 : IntInf.int)
  | delta (Dvd (aa, Mul (bx, by))) = (1 : IntInf.int)
  | delta (Dvd (aa, Sub (bv, bw))) = (1 : IntInf.int)
  | delta (Dvd (aa, Add (bt, bu))) = (1 : IntInf.int)
  | delta (Dvd (aa, Neg bs)) = (1 : IntInf.int)
  | delta (Dvd (aa, Bound bp)) = (1 : IntInf.int)
  | delta (Dvd (aa, C bo)) = (1 : IntInf.int)
  | delta (NEq z) = (1 : IntInf.int)
  | delta (Eq y) = (1 : IntInf.int)
  | delta (Ge x) = (1 : IntInf.int)
  | delta (Gt w) = (1 : IntInf.int)
  | delta (Le v) = (1 : IntInf.int)
  | delta (Lt u) = (1 : IntInf.int)
  | delta F = (1 : IntInf.int)
  | delta T = (1 : IntInf.int)
  | delta (NDvd (y, Cx (c, e))) = y
  | delta (Dvd (y, Cx (c, e))) = y
  | delta (Or (p, q)) = ilcm (delta p) (delta q)
  | delta (And (p, q)) = ilcm (delta p) (delta q);

fun beta (NClosed aq) = []
  | beta (Closed ap) = []
  | beta (A ao) = []
  | beta (E an) = []
  | beta (Iffa (al, am)) = []
  | beta (Impa (aj, ak)) = []
  | beta (Nota ae) = []
  | beta (NDvd (ac, ad)) = []
  | beta (Dvd (aa, ab)) = []
  | beta (NEq (Mul (gd, ge))) = []
  | beta (NEq (Sub (gb, gc))) = []
  | beta (NEq (Add (fz, ga))) = []
  | beta (NEq (Neg fy)) = []
  | beta (NEq (Bound fv)) = []
  | beta (NEq (C fu)) = []
  | beta (Eq (Mul (fh, fi))) = []
  | beta (Eq (Sub (ff, fg))) = []
  | beta (Eq (Add (fd, fe))) = []
  | beta (Eq (Neg fc)) = []
  | beta (Eq (Bound ez)) = []
  | beta (Eq (C ey)) = []
  | beta (Ge (Mul (el, em))) = []
  | beta (Ge (Sub (ej, ek))) = []
  | beta (Ge (Add (eh, ei))) = []
  | beta (Ge (Neg eg)) = []
  | beta (Ge (Bound ed)) = []
  | beta (Ge (C ec)) = []
  | beta (Gt (Mul (dp, dq))) = []
  | beta (Gt (Sub (dn, doa))) = []
  | beta (Gt (Add (dl, dm))) = []
  | beta (Gt (Neg dk)) = []
  | beta (Gt (Bound dh)) = []
  | beta (Gt (C dg)) = []
  | beta (Le (Mul (ct, cu))) = []
  | beta (Le (Sub (cr, cs))) = []
  | beta (Le (Add (cp, cq))) = []
  | beta (Le (Neg co)) = []
  | beta (Le (Bound cl)) = []
  | beta (Le (C ck)) = []
  | beta (Lt (Mul (bx, by))) = []
  | beta (Lt (Sub (bv, bw))) = []
  | beta (Lt (Add (bt, bu))) = []
  | beta (Lt (Neg bs)) = []
  | beta (Lt (Bound bp)) = []
  | beta (Lt (C bo)) = []
  | beta F = []
  | beta T = []
  | beta (Ge (Cx (c, e))) = [Sub (C (~1 : IntInf.int), e)]
  | beta (Gt (Cx (c, e))) = [Neg e]
  | beta (Le (Cx (c, e))) = []
  | beta (Lt (Cx (c, e))) = []
  | beta (NEq (Cx (c, e))) = [Neg e]
  | beta (Eq (Cx (c, e))) = [Sub (C (~1 : IntInf.int), e)]
  | beta (Or (p, q)) = append (beta p) (beta q)
  | beta (And (p, q)) = append (beta p) (beta q);

fun alpha (NClosed aq) = []
  | alpha (Closed ap) = []
  | alpha (A ao) = []
  | alpha (E an) = []
  | alpha (Iffa (al, am)) = []
  | alpha (Impa (aj, ak)) = []
  | alpha (Nota ae) = []
  | alpha (NDvd (ac, ad)) = []
  | alpha (Dvd (aa, ab)) = []
  | alpha (NEq (Mul (gd, ge))) = []
  | alpha (NEq (Sub (gb, gc))) = []
  | alpha (NEq (Add (fz, ga))) = []
  | alpha (NEq (Neg fy)) = []
  | alpha (NEq (Bound fv)) = []
  | alpha (NEq (C fu)) = []
  | alpha (Eq (Mul (fh, fi))) = []
  | alpha (Eq (Sub (ff, fg))) = []
  | alpha (Eq (Add (fd, fe))) = []
  | alpha (Eq (Neg fc)) = []
  | alpha (Eq (Bound ez)) = []
  | alpha (Eq (C ey)) = []
  | alpha (Ge (Mul (el, em))) = []
  | alpha (Ge (Sub (ej, ek))) = []
  | alpha (Ge (Add (eh, ei))) = []
  | alpha (Ge (Neg eg)) = []
  | alpha (Ge (Bound ed)) = []
  | alpha (Ge (C ec)) = []
  | alpha (Gt (Mul (dp, dq))) = []
  | alpha (Gt (Sub (dn, doa))) = []
  | alpha (Gt (Add (dl, dm))) = []
  | alpha (Gt (Neg dk)) = []
  | alpha (Gt (Bound dh)) = []
  | alpha (Gt (C dg)) = []
  | alpha (Le (Mul (ct, cu))) = []
  | alpha (Le (Sub (cr, cs))) = []
  | alpha (Le (Add (cp, cq))) = []
  | alpha (Le (Neg co)) = []
  | alpha (Le (Bound cl)) = []
  | alpha (Le (C ck)) = []
  | alpha (Lt (Mul (bx, by))) = []
  | alpha (Lt (Sub (bv, bw))) = []
  | alpha (Lt (Add (bt, bu))) = []
  | alpha (Lt (Neg bs)) = []
  | alpha (Lt (Bound bp)) = []
  | alpha (Lt (C bo)) = []
  | alpha F = []
  | alpha T = []
  | alpha (Ge (Cx (c, e))) = []
  | alpha (Gt (Cx (c, e))) = []
  | alpha (Le (Cx (c, e))) = [Add (C (~1 : IntInf.int), e)]
  | alpha (Lt (Cx (c, e))) = [e]
  | alpha (NEq (Cx (c, e))) = [e]
  | alpha (Eq (Cx (c, e))) = [Add (C (~1 : IntInf.int), e)]
  | alpha (Or (p, q)) = append (alpha p) (alpha q)
  | alpha (And (p, q)) = append (alpha p) (alpha q);

fun numadd (Mul (ar, asa), Mul (aza, azb)) = Add (Mul (ar, asa), Mul (aza, azb))
  | numadd (Mul (ar, asa), Sub (ayy, ayz)) = Add (Mul (ar, asa), Sub (ayy, ayz))
  | numadd (Mul (ar, asa), Add (Mul (azw, Mul (bas, bat)), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, Mul (bas, bat)), ayx))
  | numadd (Mul (ar, asa), Add (Mul (azw, Sub (baq, bar)), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, Sub (baq, bar)), ayx))
  | numadd (Mul (ar, asa), Add (Mul (azw, Add (bao, bap)), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, Add (bao, bap)), ayx))
  | numadd (Mul (ar, asa), Add (Mul (azw, Neg ban), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, Neg ban), ayx))
  | numadd (Mul (ar, asa), Add (Mul (azw, Cx (bal, bam)), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, Cx (bal, bam)), ayx))
  | numadd (Mul (ar, asa), Add (Mul (azw, C baj), ayx)) =
    Add (Mul (ar, asa), Add (Mul (azw, C baj), ayx))
  | numadd (Mul (ar, asa), Add (Sub (azu, azv), ayx)) =
    Add (Mul (ar, asa), Add (Sub (azu, azv), ayx))
  | numadd (Mul (ar, asa), Add (Add (azs, azt), ayx)) =
    Add (Mul (ar, asa), Add (Add (azs, azt), ayx))
  | numadd (Mul (ar, asa), Add (Neg azr, ayx)) =
    Add (Mul (ar, asa), Add (Neg azr, ayx))
  | numadd (Mul (ar, asa), Add (Cx (azp, azq), ayx)) =
    Add (Mul (ar, asa), Add (Cx (azp, azq), ayx))
  | numadd (Mul (ar, asa), Add (Bound azo, ayx)) =
    Add (Mul (ar, asa), Add (Bound azo, ayx))
  | numadd (Mul (ar, asa), Add (C azn, ayx)) =
    Add (Mul (ar, asa), Add (C azn, ayx))
  | numadd (Mul (ar, asa), Neg ayv) = Add (Mul (ar, asa), Neg ayv)
  | numadd (Mul (ar, asa), Cx (ayt, ayu)) = Add (Mul (ar, asa), Cx (ayt, ayu))
  | numadd (Mul (ar, asa), Bound ays) = Add (Mul (ar, asa), Bound ays)
  | numadd (Mul (ar, asa), C ayr) = Add (Mul (ar, asa), C ayr)
  | numadd (Sub (ap, aq), Mul (awm, awn)) = Add (Sub (ap, aq), Mul (awm, awn))
  | numadd (Sub (ap, aq), Sub (awk, awl)) = Add (Sub (ap, aq), Sub (awk, awl))
  | numadd (Sub (ap, aq), Add (Mul (axi, Mul (aye, ayf)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Mul (aye, ayf)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Sub (ayc, ayd)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Sub (ayc, ayd)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Add (aya, ayb)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Add (aya, ayb)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Neg axz), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Neg axz), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, Cx (axx, axy)), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, Cx (axx, axy)), awj))
  | numadd (Sub (ap, aq), Add (Mul (axi, C axv), awj)) =
    Add (Sub (ap, aq), Add (Mul (axi, C axv), awj))
  | numadd (Sub (ap, aq), Add (Sub (axg, axh), awj)) =
    Add (Sub (ap, aq), Add (Sub (axg, axh), awj))
  | numadd (Sub (ap, aq), Add (Add (axe, axf), awj)) =
    Add (Sub (ap, aq), Add (Add (axe, axf), awj))
  | numadd (Sub (ap, aq), Add (Neg axd, awj)) =
    Add (Sub (ap, aq), Add (Neg axd, awj))
  | numadd (Sub (ap, aq), Add (Cx (axb, axc), awj)) =
    Add (Sub (ap, aq), Add (Cx (axb, axc), awj))
  | numadd (Sub (ap, aq), Add (Bound axa, awj)) =
    Add (Sub (ap, aq), Add (Bound axa, awj))
  | numadd (Sub (ap, aq), Add (C awz, awj)) =
    Add (Sub (ap, aq), Add (C awz, awj))
  | numadd (Sub (ap, aq), Neg awh) = Add (Sub (ap, aq), Neg awh)
  | numadd (Sub (ap, aq), Cx (awf, awg)) = Add (Sub (ap, aq), Cx (awf, awg))
  | numadd (Sub (ap, aq), Bound awe) = Add (Sub (ap, aq), Bound awe)
  | numadd (Sub (ap, aq), C awd) = Add (Sub (ap, aq), C awd)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Mul (aty, atz)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Mul (aty, atz))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Sub (atw, atx)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Sub (atw, atx))
  | numadd
    (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Mul (avq, avr)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Mul (avq, avr)), atv))
  | numadd
    (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Sub (avo, avp)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Sub (avo, avp)), atv))
  | numadd
    (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Add (avm, avn)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Add (avm, avn)), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Neg avl), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Neg avl), atv))
  | numadd
    (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, Cx (avj, avk)), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao),
          Add (Mul (auu, Cx (avj, avk)), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, C avh), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Mul (auu, C avh), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Sub (aus, aut), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Sub (aus, aut), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Add (auq, aur), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Add (auq, aur), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Neg aup, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Neg aup, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Cx (aun, auo), atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Cx (aun, auo), atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (Bound aum, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (Bound aum, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Add (C aul, atv)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Add (C aul, atv))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Neg att) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Neg att)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Cx (atr, ats)) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Cx (atr, ats))
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), Bound atq) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), Bound atq)
  | numadd (Add (Mul (mc, Mul (acp, acq)), ao), C atp) =
    Add (Add (Mul (mc, Mul (acp, acq)), ao), C atp)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Mul (ark, arl)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Mul (ark, arl))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Sub (ari, arj)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Sub (ari, arj))
  | numadd
    (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Mul (atc, atd)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Mul (atc, atd)), arh))
  | numadd
    (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Sub (ata, atb)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Sub (ata, atb)), arh))
  | numadd
    (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Add (asy, asz)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Add (asy, asz)), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Neg asx), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Neg asx), arh))
  | numadd
    (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, Cx (asv, asw)), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao),
          Add (Mul (asg, Cx (asv, asw)), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, C ast), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Mul (asg, C ast), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Sub (ase, asf), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Sub (ase, asf), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Add (asc, asd), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Add (asc, asd), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Neg asb, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Neg asb, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Cx (arz, asa), arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Cx (arz, asa), arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (Bound ary, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (Bound ary, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Add (C arx, arh)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Add (C arx, arh))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Neg arf) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Neg arf)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Cx (ard, are)) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Cx (ard, are))
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), Bound arc) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), Bound arc)
  | numadd (Add (Mul (mc, Sub (acn, aco)), ao), C arb) =
    Add (Add (Mul (mc, Sub (acn, aco)), ao), C arb)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Mul (aow, aox)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Mul (aow, aox))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Sub (aou, aov)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Sub (aou, aov))
  | numadd
    (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Mul (aqo, aqp)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Mul (aqo, aqp)), aot))
  | numadd
    (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Sub (aqm, aqn)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Sub (aqm, aqn)), aot))
  | numadd
    (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Add (aqk, aql)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Add (aqk, aql)), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Neg aqj), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Neg aqj), aot))
  | numadd
    (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, Cx (aqh, aqi)), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao),
          Add (Mul (aps, Cx (aqh, aqi)), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, C aqf), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Mul (aps, C aqf), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Sub (apq, apr), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Sub (apq, apr), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Add (apo, app), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Add (apo, app), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Neg apn, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Neg apn, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Cx (apl, apm), aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Cx (apl, apm), aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (Bound apk, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (Bound apk, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Add (C apj, aot)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Add (C apj, aot))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Neg aor) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Neg aor)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Cx (aop, aoq)) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Cx (aop, aoq))
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), Bound aoo) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), Bound aoo)
  | numadd (Add (Mul (mc, Add (acl, acm)), ao), C aon) =
    Add (Add (Mul (mc, Add (acl, acm)), ao), C aon)
  | numadd (Add (Mul (mc, Neg ack), ao), Mul (ami, amj)) =
    Add (Add (Mul (mc, Neg ack), ao), Mul (ami, amj))
  | numadd (Add (Mul (mc, Neg ack), ao), Sub (amg, amh)) =
    Add (Add (Mul (mc, Neg ack), ao), Sub (amg, amh))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Mul (aoa, aob)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Mul (aoa, aob)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Sub (any, anz)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Sub (any, anz)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Add (anw, anx)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Add (anw, anx)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Neg anv), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Neg anv), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Cx (ant, anu)), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, Cx (ant, anu)), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, C anr), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Mul (ane, C anr), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Sub (anc, anda), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Sub (anc, anda), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Add (ana, anb), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Add (ana, anb), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Neg amz, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Neg amz, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Cx (amx, amy), amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Cx (amx, amy), amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (Bound amw, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (Bound amw, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Add (C amv, amf)) =
    Add (Add (Mul (mc, Neg ack), ao), Add (C amv, amf))
  | numadd (Add (Mul (mc, Neg ack), ao), Neg amd) =
    Add (Add (Mul (mc, Neg ack), ao), Neg amd)
  | numadd (Add (Mul (mc, Neg ack), ao), Cx (amb, amc)) =
    Add (Add (Mul (mc, Neg ack), ao), Cx (amb, amc))
  | numadd (Add (Mul (mc, Neg ack), ao), Bound ama) =
    Add (Add (Mul (mc, Neg ack), ao), Bound ama)
  | numadd (Add (Mul (mc, Neg ack), ao), C alz) =
    Add (Add (Mul (mc, Neg ack), ao), C alz)
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Mul (aju, ajv)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Mul (aju, ajv))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Sub (ajs, ajt)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Sub (ajs, ajt))
  | numadd
    (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Mul (alm, aln)), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao),
          Add (Mul (akq, Mul (alm, aln)), ajr))
  | numadd
    (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Sub (alk, all)), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao),
          Add (Mul (akq, Sub (alk, all)), ajr))
  | numadd
    (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Add (ali, alj)), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao),
          Add (Mul (akq, Add (ali, alj)), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Neg alh), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Neg alh), ajr))
  | numadd
    (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Cx (alf, alg)), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, Cx (alf, alg)), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, C ald), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Mul (akq, C ald), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Sub (ako, akp), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Sub (ako, akp), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Add (akm, akn), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Add (akm, akn), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Neg akl, ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Neg akl, ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Cx (akj, akk), ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Cx (akj, akk), ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (Bound aki, ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (Bound aki, ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Add (C akh, ajr)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Add (C akh, ajr))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Neg ajp) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Neg ajp)
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Cx (ajn, ajo)) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Cx (ajn, ajo))
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), Bound ajm) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), Bound ajm)
  | numadd (Add (Mul (mc, Cx (aci, acj)), ao), C ajl) =
    Add (Add (Mul (mc, Cx (aci, acj)), ao), C ajl)
  | numadd (Add (Mul (mc, C acg), ao), Mul (adl, adm)) =
    Add (Add (Mul (mc, C acg), ao), Mul (adl, adm))
  | numadd (Add (Mul (mc, C acg), ao), Sub (adj, adk)) =
    Add (Add (Mul (mc, C acg), ao), Sub (adj, adk))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Mul (afd, afe)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Mul (afd, afe)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Sub (afb, afc)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Sub (afb, afc)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Add (aez, afa)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Add (aez, afa)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Neg aey), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Neg aey), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Cx (aew, aex)), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, Cx (aew, aex)), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Mul (aeh, C aeu), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Mul (aeh, C aeu), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Sub (aef, aeg), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Sub (aef, aeg), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Add (aed, aee), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Add (aed, aee), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Neg aec, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Neg aec, adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Cx (aea, aeb), adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Cx (aea, aeb), adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (Bound adz, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (Bound adz, adi))
  | numadd (Add (Mul (mc, C acg), ao), Add (C ady, adi)) =
    Add (Add (Mul (mc, C acg), ao), Add (C ady, adi))
  | numadd (Add (Mul (mc, C acg), ao), Neg adg) =
    Add (Add (Mul (mc, C acg), ao), Neg adg)
  | numadd (Add (Mul (mc, C acg), ao), Cx (ade, adf)) =
    Add (Add (Mul (mc, C acg), ao), Cx (ade, adf))
  | numadd (Add (Mul (mc, C acg), ao), Bound add) =
    Add (Add (Mul (mc, C acg), ao), Bound add)
  | numadd (Add (Mul (mc, C acg), ao), C adc) =
    Add (Add (Mul (mc, C acg), ao), C adc)
  | numadd (Add (Sub (ma, mb), ao), Mul (zq, zr)) =
    Add (Add (Sub (ma, mb), ao), Mul (zq, zr))
  | numadd (Add (Sub (ma, mb), ao), Sub (zo, zp)) =
    Add (Add (Sub (ma, mb), ao), Sub (zo, zp))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Mul (abi, abj)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Mul (abi, abj)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Sub (abg, abh)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Sub (abg, abh)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Add (abe, abf)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Add (abe, abf)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Neg abd), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Neg abd), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, Cx (abb, abc)), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, Cx (abb, abc)), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Mul (aam, C aaz), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Mul (aam, C aaz), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Sub (aak, aal), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Sub (aak, aal), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Add (aai, aaj), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Add (aai, aaj), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Neg aah, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Neg aah, zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Cx (aaf, aag), zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Cx (aaf, aag), zn))
  | numadd (Add (Sub (ma, mb), ao), Add (Bound aae, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (Bound aae, zn))
  | numadd (Add (Sub (ma, mb), ao), Add (C aad, zn)) =
    Add (Add (Sub (ma, mb), ao), Add (C aad, zn))
  | numadd (Add (Sub (ma, mb), ao), Neg zl) =
    Add (Add (Sub (ma, mb), ao), Neg zl)
  | numadd (Add (Sub (ma, mb), ao), Cx (zj, zk)) =
    Add (Add (Sub (ma, mb), ao), Cx (zj, zk))
  | numadd (Add (Sub (ma, mb), ao), Bound zi) =
    Add (Add (Sub (ma, mb), ao), Bound zi)
  | numadd (Add (Sub (ma, mb), ao), C zh) = Add (Add (Sub (ma, mb), ao), C zh)
  | numadd (Add (Add (ly, lz), ao), Mul (xc, xd)) =
    Add (Add (Add (ly, lz), ao), Mul (xc, xd))
  | numadd (Add (Add (ly, lz), ao), Sub (xa, xb)) =
    Add (Add (Add (ly, lz), ao), Sub (xa, xb))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Mul (yu, yv)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Mul (yu, yv)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Sub (ys, yt)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Sub (ys, yt)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Add (yq, yr)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Add (yq, yr)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Neg yp), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Neg yp), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, Cx (yn, yo)), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, Cx (yn, yo)), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Mul (xy, C yl), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Mul (xy, C yl), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Sub (xw, xx), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Sub (xw, xx), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Add (xu, xv), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Add (xu, xv), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Neg xt, wz)) =
    Add (Add (Add (ly, lz), ao), Add (Neg xt, wz))
  | numadd (Add (Add (ly, lz), ao), Add (Cx (xr, xs), wz)) =
    Add (Add (Add (ly, lz), ao), Add (Cx (xr, xs), wz))
  | numadd (Add (Add (ly, lz), ao), Add (Bound xq, wz)) =
    Add (Add (Add (ly, lz), ao), Add (Bound xq, wz))
  | numadd (Add (Add (ly, lz), ao), Add (C xp, wz)) =
    Add (Add (Add (ly, lz), ao), Add (C xp, wz))
  | numadd (Add (Add (ly, lz), ao), Neg wx) =
    Add (Add (Add (ly, lz), ao), Neg wx)
  | numadd (Add (Add (ly, lz), ao), Cx (wv, ww)) =
    Add (Add (Add (ly, lz), ao), Cx (wv, ww))
  | numadd (Add (Add (ly, lz), ao), Bound wu) =
    Add (Add (Add (ly, lz), ao), Bound wu)
  | numadd (Add (Add (ly, lz), ao), C wt) = Add (Add (Add (ly, lz), ao), C wt)
  | numadd (Add (Neg lx, ao), Mul (uo, up)) =
    Add (Add (Neg lx, ao), Mul (uo, up))
  | numadd (Add (Neg lx, ao), Sub (um, un)) =
    Add (Add (Neg lx, ao), Sub (um, un))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Mul (wg, wh)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Mul (wg, wh)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Sub (we, wf)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Sub (we, wf)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Add (wc, wd)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Add (wc, wd)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Neg wb), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Neg wb), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, Cx (vz, wa)), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, Cx (vz, wa)), ul))
  | numadd (Add (Neg lx, ao), Add (Mul (vk, C vx), ul)) =
    Add (Add (Neg lx, ao), Add (Mul (vk, C vx), ul))
  | numadd (Add (Neg lx, ao), Add (Sub (vi, vj), ul)) =
    Add (Add (Neg lx, ao), Add (Sub (vi, vj), ul))
  | numadd (Add (Neg lx, ao), Add (Add (vg, vh), ul)) =
    Add (Add (Neg lx, ao), Add (Add (vg, vh), ul))
  | numadd (Add (Neg lx, ao), Add (Neg vf, ul)) =
    Add (Add (Neg lx, ao), Add (Neg vf, ul))
  | numadd (Add (Neg lx, ao), Add (Cx (vd, ve), ul)) =
    Add (Add (Neg lx, ao), Add (Cx (vd, ve), ul))
  | numadd (Add (Neg lx, ao), Add (Bound vc, ul)) =
    Add (Add (Neg lx, ao), Add (Bound vc, ul))
  | numadd (Add (Neg lx, ao), Add (C vb, ul)) =
    Add (Add (Neg lx, ao), Add (C vb, ul))
  | numadd (Add (Neg lx, ao), Neg uj) = Add (Add (Neg lx, ao), Neg uj)
  | numadd (Add (Neg lx, ao), Cx (uh, ui)) = Add (Add (Neg lx, ao), Cx (uh, ui))
  | numadd (Add (Neg lx, ao), Bound ug) = Add (Add (Neg lx, ao), Bound ug)
  | numadd (Add (Neg lx, ao), C uf) = Add (Add (Neg lx, ao), C uf)
  | numadd (Add (Cx (lv, lw), ao), Mul (sa, sb)) =
    Add (Add (Cx (lv, lw), ao), Mul (sa, sb))
  | numadd (Add (Cx (lv, lw), ao), Sub (ry, rz)) =
    Add (Add (Cx (lv, lw), ao), Sub (ry, rz))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, Mul (ts, tt)), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, Mul (ts, tt)), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, Sub (tq, tr)), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, Sub (tq, tr)), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, Add (to, tp)), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, Add (to, tp)), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, Neg tn), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, Neg tn), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, Cx (tl, tm)), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, Cx (tl, tm)), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Mul (sw, C tj), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Mul (sw, C tj), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Sub (su, sv), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Sub (su, sv), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Add (ss, st), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Add (ss, st), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Neg sr, rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Neg sr, rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Cx (sp, sq), rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Cx (sp, sq), rx))
  | numadd (Add (Cx (lv, lw), ao), Add (Bound so, rx)) =
    Add (Add (Cx (lv, lw), ao), Add (Bound so, rx))
  | numadd (Add (Cx (lv, lw), ao), Add (C sn, rx)) =
    Add (Add (Cx (lv, lw), ao), Add (C sn, rx))
  | numadd (Add (Cx (lv, lw), ao), Neg rv) = Add (Add (Cx (lv, lw), ao), Neg rv)
  | numadd (Add (Cx (lv, lw), ao), Cx (rt, ru)) =
    Add (Add (Cx (lv, lw), ao), Cx (rt, ru))
  | numadd (Add (Cx (lv, lw), ao), Bound rs) =
    Add (Add (Cx (lv, lw), ao), Bound rs)
  | numadd (Add (Cx (lv, lw), ao), C rr) = Add (Add (Cx (lv, lw), ao), C rr)
  | numadd (Add (Bound lu, ao), Mul (pm, pn)) =
    Add (Add (Bound lu, ao), Mul (pm, pn))
  | numadd (Add (Bound lu, ao), Sub (pk, pl)) =
    Add (Add (Bound lu, ao), Sub (pk, pl))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Mul (re, rf)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Mul (re, rf)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Sub (rc, rd)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Sub (rc, rd)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Add (ra, rb)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Add (ra, rb)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Neg qz), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Neg qz), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, Cx (qx, qy)), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, Cx (qx, qy)), pj))
  | numadd (Add (Bound lu, ao), Add (Mul (qi, C qv), pj)) =
    Add (Add (Bound lu, ao), Add (Mul (qi, C qv), pj))
  | numadd (Add (Bound lu, ao), Add (Sub (qg, qh), pj)) =
    Add (Add (Bound lu, ao), Add (Sub (qg, qh), pj))
  | numadd (Add (Bound lu, ao), Add (Add (qe, qf), pj)) =
    Add (Add (Bound lu, ao), Add (Add (qe, qf), pj))
  | numadd (Add (Bound lu, ao), Add (Neg qd, pj)) =
    Add (Add (Bound lu, ao), Add (Neg qd, pj))
  | numadd (Add (Bound lu, ao), Add (Cx (qb, qc), pj)) =
    Add (Add (Bound lu, ao), Add (Cx (qb, qc), pj))
  | numadd (Add (Bound lu, ao), Add (Bound qa, pj)) =
    Add (Add (Bound lu, ao), Add (Bound qa, pj))
  | numadd (Add (Bound lu, ao), Add (C pz, pj)) =
    Add (Add (Bound lu, ao), Add (C pz, pj))
  | numadd (Add (Bound lu, ao), Neg ph) = Add (Add (Bound lu, ao), Neg ph)
  | numadd (Add (Bound lu, ao), Cx (pf, pg)) =
    Add (Add (Bound lu, ao), Cx (pf, pg))
  | numadd (Add (Bound lu, ao), Bound pe) = Add (Add (Bound lu, ao), Bound pe)
  | numadd (Add (Bound lu, ao), C pd) = Add (Add (Bound lu, ao), C pd)
  | numadd (Add (C lt, ao), Mul (my, mz)) = Add (Add (C lt, ao), Mul (my, mz))
  | numadd (Add (C lt, ao), Sub (mw, mx)) = Add (Add (C lt, ao), Sub (mw, mx))
  | numadd (Add (C lt, ao), Add (Mul (nu, Mul (oq, or)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Mul (oq, or)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Sub (ooa, opa)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Sub (ooa, opa)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Add (om, on)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Add (om, on)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Neg ol), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Neg ol), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, Cx (oj, ok)), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, Cx (oj, ok)), mv))
  | numadd (Add (C lt, ao), Add (Mul (nu, C oh), mv)) =
    Add (Add (C lt, ao), Add (Mul (nu, C oh), mv))
  | numadd (Add (C lt, ao), Add (Sub (ns, nt), mv)) =
    Add (Add (C lt, ao), Add (Sub (ns, nt), mv))
  | numadd (Add (C lt, ao), Add (Add (nq, nr), mv)) =
    Add (Add (C lt, ao), Add (Add (nq, nr), mv))
  | numadd (Add (C lt, ao), Add (Neg np, mv)) =
    Add (Add (C lt, ao), Add (Neg np, mv))
  | numadd (Add (C lt, ao), Add (Cx (nn, no), mv)) =
    Add (Add (C lt, ao), Add (Cx (nn, no), mv))
  | numadd (Add (C lt, ao), Add (Bound nm, mv)) =
    Add (Add (C lt, ao), Add (Bound nm, mv))
  | numadd (Add (C lt, ao), Add (C nl, mv)) =
    Add (Add (C lt, ao), Add (C nl, mv))
  | numadd (Add (C lt, ao), Neg mt) = Add (Add (C lt, ao), Neg mt)
  | numadd (Add (C lt, ao), Cx (mr, ms)) = Add (Add (C lt, ao), Cx (mr, ms))
  | numadd (Add (C lt, ao), Bound mq) = Add (Add (C lt, ao), Bound mq)
  | numadd (Add (C lt, ao), C mp) = Add (Add (C lt, ao), C mp)
  | numadd (Neg am, Mul (jd, je)) = Add (Neg am, Mul (jd, je))
  | numadd (Neg am, Sub (jb, jc)) = Add (Neg am, Sub (jb, jc))
  | numadd (Neg am, Add (Mul (jz, Mul (kv, kw)), ja)) =
    Add (Neg am, Add (Mul (jz, Mul (kv, kw)), ja))
  | numadd (Neg am, Add (Mul (jz, Sub (kt, ku)), ja)) =
    Add (Neg am, Add (Mul (jz, Sub (kt, ku)), ja))
  | numadd (Neg am, Add (Mul (jz, Add (kr, ks)), ja)) =
    Add (Neg am, Add (Mul (jz, Add (kr, ks)), ja))
  | numadd (Neg am, Add (Mul (jz, Neg kq), ja)) =
    Add (Neg am, Add (Mul (jz, Neg kq), ja))
  | numadd (Neg am, Add (Mul (jz, Cx (ko, kp)), ja)) =
    Add (Neg am, Add (Mul (jz, Cx (ko, kp)), ja))
  | numadd (Neg am, Add (Mul (jz, C km), ja)) =
    Add (Neg am, Add (Mul (jz, C km), ja))
  | numadd (Neg am, Add (Sub (jx, jy), ja)) =
    Add (Neg am, Add (Sub (jx, jy), ja))
  | numadd (Neg am, Add (Add (jv, jw), ja)) =
    Add (Neg am, Add (Add (jv, jw), ja))
  | numadd (Neg am, Add (Neg ju, ja)) = Add (Neg am, Add (Neg ju, ja))
  | numadd (Neg am, Add (Cx (js, jt), ja)) = Add (Neg am, Add (Cx (js, jt), ja))
  | numadd (Neg am, Add (Bound jr, ja)) = Add (Neg am, Add (Bound jr, ja))
  | numadd (Neg am, Add (C jq, ja)) = Add (Neg am, Add (C jq, ja))
  | numadd (Neg am, Neg iy) = Add (Neg am, Neg iy)
  | numadd (Neg am, Cx (iw, ix)) = Add (Neg am, Cx (iw, ix))
  | numadd (Neg am, Bound iv) = Add (Neg am, Bound iv)
  | numadd (Neg am, C iu) = Add (Neg am, C iu)
  | numadd (Cx (ak, al), Mul (gp, gq)) = Add (Cx (ak, al), Mul (gp, gq))
  | numadd (Cx (ak, al), Sub (gn, go)) = Add (Cx (ak, al), Sub (gn, go))
  | numadd (Cx (ak, al), Add (Mul (hl, Mul (ih, ii)), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, Mul (ih, ii)), gm))
  | numadd (Cx (ak, al), Add (Mul (hl, Sub (ifa, ig)), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, Sub (ifa, ig)), gm))
  | numadd (Cx (ak, al), Add (Mul (hl, Add (id, ie)), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, Add (id, ie)), gm))
  | numadd (Cx (ak, al), Add (Mul (hl, Neg ic), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, Neg ic), gm))
  | numadd (Cx (ak, al), Add (Mul (hl, Cx (ia, ib)), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, Cx (ia, ib)), gm))
  | numadd (Cx (ak, al), Add (Mul (hl, C hy), gm)) =
    Add (Cx (ak, al), Add (Mul (hl, C hy), gm))
  | numadd (Cx (ak, al), Add (Sub (hj, hk), gm)) =
    Add (Cx (ak, al), Add (Sub (hj, hk), gm))
  | numadd (Cx (ak, al), Add (Add (hh, hi), gm)) =
    Add (Cx (ak, al), Add (Add (hh, hi), gm))
  | numadd (Cx (ak, al), Add (Neg hg, gm)) = Add (Cx (ak, al), Add (Neg hg, gm))
  | numadd (Cx (ak, al), Add (Cx (he, hf), gm)) =
    Add (Cx (ak, al), Add (Cx (he, hf), gm))
  | numadd (Cx (ak, al), Add (Bound hd, gm)) =
    Add (Cx (ak, al), Add (Bound hd, gm))
  | numadd (Cx (ak, al), Add (C hc, gm)) = Add (Cx (ak, al), Add (C hc, gm))
  | numadd (Cx (ak, al), Neg gk) = Add (Cx (ak, al), Neg gk)
  | numadd (Cx (ak, al), Cx (gi, gj)) = Add (Cx (ak, al), Cx (gi, gj))
  | numadd (Cx (ak, al), Bound gh) = Add (Cx (ak, al), Bound gh)
  | numadd (Cx (ak, al), C gg) = Add (Cx (ak, al), C gg)
  | numadd (Bound aj, Mul (eb, ec)) = Add (Bound aj, Mul (eb, ec))
  | numadd (Bound aj, Sub (dz, ea)) = Add (Bound aj, Sub (dz, ea))
  | numadd (Bound aj, Add (Mul (ex, Mul (ft, fu)), dy)) =
    Add (Bound aj, Add (Mul (ex, Mul (ft, fu)), dy))
  | numadd (Bound aj, Add (Mul (ex, Sub (fr, fs)), dy)) =
    Add (Bound aj, Add (Mul (ex, Sub (fr, fs)), dy))
  | numadd (Bound aj, Add (Mul (ex, Add (fp, fq)), dy)) =
    Add (Bound aj, Add (Mul (ex, Add (fp, fq)), dy))
  | numadd (Bound aj, Add (Mul (ex, Neg fo), dy)) =
    Add (Bound aj, Add (Mul (ex, Neg fo), dy))
  | numadd (Bound aj, Add (Mul (ex, Cx (fm, fna)), dy)) =
    Add (Bound aj, Add (Mul (ex, Cx (fm, fna)), dy))
  | numadd (Bound aj, Add (Mul (ex, C fk), dy)) =
    Add (Bound aj, Add (Mul (ex, C fk), dy))
  | numadd (Bound aj, Add (Sub (ev, ew), dy)) =
    Add (Bound aj, Add (Sub (ev, ew), dy))
  | numadd (Bound aj, Add (Add (et, eu), dy)) =
    Add (Bound aj, Add (Add (et, eu), dy))
  | numadd (Bound aj, Add (Neg es, dy)) = Add (Bound aj, Add (Neg es, dy))
  | numadd (Bound aj, Add (Cx (eq, er), dy)) =
    Add (Bound aj, Add (Cx (eq, er), dy))
  | numadd (Bound aj, Add (Bound ep, dy)) = Add (Bound aj, Add (Bound ep, dy))
  | numadd (Bound aj, Add (C eo, dy)) = Add (Bound aj, Add (C eo, dy))
  | numadd (Bound aj, Neg dw) = Add (Bound aj, Neg dw)
  | numadd (Bound aj, Cx (du, dv)) = Add (Bound aj, Cx (du, dv))
  | numadd (Bound aj, Bound dt) = Add (Bound aj, Bound dt)
  | numadd (Bound aj, C ds) = Add (Bound aj, C ds)
  | numadd (C ai, Mul (bn, bo)) = Add (C ai, Mul (bn, bo))
  | numadd (C ai, Sub (bl, bm)) = Add (C ai, Sub (bl, bm))
  | numadd (C ai, Add (Mul (cj, Mul (df, dg)), bk)) =
    Add (C ai, Add (Mul (cj, Mul (df, dg)), bk))
  | numadd (C ai, Add (Mul (cj, Sub (dd, de)), bk)) =
    Add (C ai, Add (Mul (cj, Sub (dd, de)), bk))
  | numadd (C ai, Add (Mul (cj, Add (db, dc)), bk)) =
    Add (C ai, Add (Mul (cj, Add (db, dc)), bk))
  | numadd (C ai, Add (Mul (cj, Neg da), bk)) =
    Add (C ai, Add (Mul (cj, Neg da), bk))
  | numadd (C ai, Add (Mul (cj, Cx (cy, cz)), bk)) =
    Add (C ai, Add (Mul (cj, Cx (cy, cz)), bk))
  | numadd (C ai, Add (Mul (cj, C cw), bk)) =
    Add (C ai, Add (Mul (cj, C cw), bk))
  | numadd (C ai, Add (Sub (ch, ci), bk)) = Add (C ai, Add (Sub (ch, ci), bk))
  | numadd (C ai, Add (Add (cf, cg), bk)) = Add (C ai, Add (Add (cf, cg), bk))
  | numadd (C ai, Add (Neg ce, bk)) = Add (C ai, Add (Neg ce, bk))
  | numadd (C ai, Add (Cx (cc, cd), bk)) = Add (C ai, Add (Cx (cc, cd), bk))
  | numadd (C ai, Add (Bound cb, bk)) = Add (C ai, Add (Bound cb, bk))
  | numadd (C ai, Add (C ca, bk)) = Add (C ai, Add (C ca, bk))
  | numadd (C ai, Neg bi) = Add (C ai, Neg bi)
  | numadd (C ai, Cx (bg, bh)) = Add (C ai, Cx (bg, bh))
  | numadd (C ai, Bound bf) = Add (C ai, Bound bf)
  | numadd (C b1, C b2) = C (IntInf.+ (b1, b2))
  | numadd (Mul (ag, ah), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Mul (ag, ah), r2))
  | numadd (Sub (ae, af), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Sub (ae, af), r2))
  | numadd (Add (Mul (lr, Mul (ace, acf)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Mul (ace, acf)), ad), r2))
  | numadd (Add (Mul (lr, Sub (acc, acd)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Sub (acc, acd)), ad), r2))
  | numadd (Add (Mul (lr, Add (aca, acb)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Add (aca, acb)), ad), r2))
  | numadd (Add (Mul (lr, Neg abz), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Neg abz), ad), r2))
  | numadd (Add (Mul (lr, Cx (abx, aby)), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, Cx (abx, aby)), ad), r2))
  | numadd (Add (Mul (lr, C abv), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Mul (lr, C abv), ad), r2))
  | numadd (Add (Sub (lp, lq), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Sub (lp, lq), ad), r2))
  | numadd (Add (Add (ln, lo), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Add (ln, lo), ad), r2))
  | numadd (Add (Neg lm, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Neg lm, ad), r2))
  | numadd (Add (Cx (lk, ll), ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Cx (lk, ll), ad), r2))
  | numadd (Add (Bound lj, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (Bound lj, ad), r2))
  | numadd (Add (C li, ad), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Add (C li, ad), r2))
  | numadd (Neg ab, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Neg ab, r2))
  | numadd (Cx (y, z), Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Cx (y, z), r2))
  | numadd (Bound x, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (Bound x, r2))
  | numadd (C w, Add (Mul (c2, Bound n2), r2)) =
    Add (Mul (c2, Bound n2), numadd (C w, r2))
  | numadd (Add (Mul (c1, Bound n1), r1), Mul (afz, aga)) =
    Add (Mul (c1, Bound n1), numadd (r1, Mul (afz, aga)))
  | numadd (Add (Mul (c1, Bound n1), r1), Sub (afx, afy)) =
    Add (Mul (c1, Bound n1), numadd (r1, Sub (afx, afy)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Mul (ain, aio)), afw))
    = Add (Mul (c1, Bound n1),
            numadd (r1, Add (Mul (ahg, Mul (ain, aio)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Sub (ail, aim)), afw))
    = Add (Mul (c1, Bound n1),
            numadd (r1, Add (Mul (ahg, Sub (ail, aim)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Add (aij, aik)), afw))
    = Add (Mul (c1, Bound n1),
            numadd (r1, Add (Mul (ahg, Add (aij, aik)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Neg aii), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Neg aii), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, Cx (aig, aih)), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, Cx (aig, aih)), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (ahg, C aie), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Mul (ahg, C aie), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Sub (ahe, ahf), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Sub (ahe, ahf), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Add (ahc, ahd), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Add (ahc, ahd), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Neg ahb, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Neg ahb, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Cx (agz, aha), afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Cx (agz, aha), afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Bound agy, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (Bound agy, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (C agx, afw)) =
    Add (Mul (c1, Bound n1), numadd (r1, Add (C agx, afw)))
  | numadd (Add (Mul (c1, Bound n1), r1), Neg afu) =
    Add (Mul (c1, Bound n1), numadd (r1, Neg afu))
  | numadd (Add (Mul (c1, Bound n1), r1), Cx (afs, aft)) =
    Add (Mul (c1, Bound n1), numadd (r1, Cx (afs, aft)))
  | numadd (Add (Mul (c1, Bound n1), r1), Bound afr) =
    Add (Mul (c1, Bound n1), numadd (r1, Bound afr))
  | numadd (Add (Mul (c1, Bound n1), r1), C afq) =
    Add (Mul (c1, Bound n1), numadd (r1, C afq))
  | numadd (Add (Mul (c1, Bound n1), r1), Add (Mul (c2, Bound n2), r2)) =
    (if ((n1 : IntInf.int) = n2)
      then let
             val c = IntInf.+ (c1, c2);
           in
             (if ((c : IntInf.int) = (0 : IntInf.int)) then numadd (r1, r2)
               else Add (Mul (c, Bound n1), numadd (r1, r2)))
           end
      else (if IntInf.<= (n1, n2)
             then Add (Mul (c1, Bound n1),
                        numadd (r1, Add (Mul (c2, Bound n2), r2)))
             else Add (Mul (c2, Bound n2),
                        numadd (Add (Mul (c1, Bound n1), r1), r2))));

fun nummul i (Sub (v, va)) = Mul (i, Sub (v, va))
  | nummul i (Neg v) = Mul (i, Neg v)
  | nummul i (Cx (v, va)) = Mul (i, Cx (v, va))
  | nummul i (Bound v) = Mul (i, Bound v)
  | nummul i (Mul (c, t)) = nummul (IntInf.* (i, c)) t
  | nummul i (Add (a, b)) = numadd (nummul i a, nummul i b)
  | nummul i (C j) = C (IntInf.* (i, j));

fun numneg t = nummul (IntInf.~ (1 : IntInf.int)) t;

fun numsub s t =
  (if eq_num s t then C (0 : IntInf.int) else numadd (s, numneg t));

fun simpnum (Cx (v, va)) = Cx (v, va)
  | simpnum (Mul (i, t)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then C (0 : IntInf.int)
      else nummul i (simpnum t))
  | simpnum (Sub (t, s)) = numsub (simpnum t) (simpnum s)
  | simpnum (Add (t, s)) = numadd (simpnum t, simpnum s)
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Bound n) =
    Add (Mul ((1 : IntInf.int), Bound n), C (0 : IntInf.int))
  | simpnum (C j) = C j;

val eq_numa = {eq = eq_num} : num eq;

fun mirror (NClosed aq) = NClosed aq
  | mirror (Closed ap) = Closed ap
  | mirror (A ao) = A ao
  | mirror (E an) = E an
  | mirror (Iffa (al, am)) = Iffa (al, am)
  | mirror (Impa (aj, ak)) = Impa (aj, ak)
  | mirror (Nota ae) = Nota ae
  | mirror (NDvd (ac, Mul (hv, hw))) = NDvd (ac, Mul (hv, hw))
  | mirror (NDvd (ac, Sub (ht, hu))) = NDvd (ac, Sub (ht, hu))
  | mirror (NDvd (ac, Add (hr, hs))) = NDvd (ac, Add (hr, hs))
  | mirror (NDvd (ac, Neg hq)) = NDvd (ac, Neg hq)
  | mirror (NDvd (ac, Bound hn)) = NDvd (ac, Bound hn)
  | mirror (NDvd (ac, C hm)) = NDvd (ac, C hm)
  | mirror (Dvd (aa, Mul (gz, ha))) = Dvd (aa, Mul (gz, ha))
  | mirror (Dvd (aa, Sub (gx, gy))) = Dvd (aa, Sub (gx, gy))
  | mirror (Dvd (aa, Add (gv, gw))) = Dvd (aa, Add (gv, gw))
  | mirror (Dvd (aa, Neg gu)) = Dvd (aa, Neg gu)
  | mirror (Dvd (aa, Bound gr)) = Dvd (aa, Bound gr)
  | mirror (Dvd (aa, C gq)) = Dvd (aa, C gq)
  | mirror (NEq (Mul (gd, ge))) = NEq (Mul (gd, ge))
  | mirror (NEq (Sub (gb, gc))) = NEq (Sub (gb, gc))
  | mirror (NEq (Add (fz, ga))) = NEq (Add (fz, ga))
  | mirror (NEq (Neg fy)) = NEq (Neg fy)
  | mirror (NEq (Bound fv)) = NEq (Bound fv)
  | mirror (NEq (C fu)) = NEq (C fu)
  | mirror (Eq (Mul (fh, fi))) = Eq (Mul (fh, fi))
  | mirror (Eq (Sub (ff, fg))) = Eq (Sub (ff, fg))
  | mirror (Eq (Add (fd, fe))) = Eq (Add (fd, fe))
  | mirror (Eq (Neg fc)) = Eq (Neg fc)
  | mirror (Eq (Bound ez)) = Eq (Bound ez)
  | mirror (Eq (C ey)) = Eq (C ey)
  | mirror (Ge (Mul (el, em))) = Ge (Mul (el, em))
  | mirror (Ge (Sub (ej, ek))) = Ge (Sub (ej, ek))
  | mirror (Ge (Add (eh, ei))) = Ge (Add (eh, ei))
  | mirror (Ge (Neg eg)) = Ge (Neg eg)
  | mirror (Ge (Bound ed)) = Ge (Bound ed)
  | mirror (Ge (C ec)) = Ge (C ec)
  | mirror (Gt (Mul (dp, dq))) = Gt (Mul (dp, dq))
  | mirror (Gt (Sub (dn, doa))) = Gt (Sub (dn, doa))
  | mirror (Gt (Add (dl, dm))) = Gt (Add (dl, dm))
  | mirror (Gt (Neg dk)) = Gt (Neg dk)
  | mirror (Gt (Bound dh)) = Gt (Bound dh)
  | mirror (Gt (C dg)) = Gt (C dg)
  | mirror (Le (Mul (ct, cu))) = Le (Mul (ct, cu))
  | mirror (Le (Sub (cr, cs))) = Le (Sub (cr, cs))
  | mirror (Le (Add (cp, cq))) = Le (Add (cp, cq))
  | mirror (Le (Neg co)) = Le (Neg co)
  | mirror (Le (Bound cl)) = Le (Bound cl)
  | mirror (Le (C ck)) = Le (C ck)
  | mirror (Lt (Mul (bx, by))) = Lt (Mul (bx, by))
  | mirror (Lt (Sub (bv, bw))) = Lt (Sub (bv, bw))
  | mirror (Lt (Add (bt, bu))) = Lt (Add (bt, bu))
  | mirror (Lt (Neg bs)) = Lt (Neg bs)
  | mirror (Lt (Bound bp)) = Lt (Bound bp)
  | mirror (Lt (C bo)) = Lt (C bo)
  | mirror F = F
  | mirror T = T
  | mirror (NDvd (i, Cx (c, e))) = NDvd (i, Cx (c, Neg e))
  | mirror (Dvd (i, Cx (c, e))) = Dvd (i, Cx (c, Neg e))
  | mirror (Ge (Cx (c, e))) = Le (Cx (c, Neg e))
  | mirror (Gt (Cx (c, e))) = Lt (Cx (c, Neg e))
  | mirror (Le (Cx (c, e))) = Ge (Cx (c, Neg e))
  | mirror (Lt (Cx (c, e))) = Gt (Cx (c, Neg e))
  | mirror (NEq (Cx (c, e))) = NEq (Cx (c, Neg e))
  | mirror (Eq (Cx (c, e))) = Eq (Cx (c, Neg e))
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror (And (p, q)) = And (mirror p, mirror q);

fun unita p =
  let
    val p' = zlfm p;
    val l = zeta p';
    val q =
      And (Dvd (l, Cx ((1 : IntInf.int), C (0 : IntInf.int))), a_beta p' l);
    val d = delta q;
    val b = remdups eq_numa (map simpnum (beta q));
    val a = remdups eq_numa (map simpnum (alpha q));
  in
    (if IntInf.<= ((size_list b), (size_list a)) then (q, (b, d))
      else (mirror q, (a, d)))
  end;

fun iupt i j =
  (if IntInf.< (j, i) then []
    else i :: iupt (IntInf.+ (i, (1 : IntInf.int))) j);

fun minusinf (NClosed aq) = NClosed aq
  | minusinf (Closed ap) = Closed ap
  | minusinf (A ao) = A ao
  | minusinf (E an) = E an
  | minusinf (Iffa (al, am)) = Iffa (al, am)
  | minusinf (Impa (aj, ak)) = Impa (aj, ak)
  | minusinf (Nota ae) = Nota ae
  | minusinf (NDvd (ac, ad)) = NDvd (ac, ad)
  | minusinf (Dvd (aa, ab)) = Dvd (aa, ab)
  | minusinf (NEq (Mul (gd, ge))) = NEq (Mul (gd, ge))
  | minusinf (NEq (Sub (gb, gc))) = NEq (Sub (gb, gc))
  | minusinf (NEq (Add (fz, ga))) = NEq (Add (fz, ga))
  | minusinf (NEq (Neg fy)) = NEq (Neg fy)
  | minusinf (NEq (Bound fv)) = NEq (Bound fv)
  | minusinf (NEq (C fu)) = NEq (C fu)
  | minusinf (Eq (Mul (fh, fi))) = Eq (Mul (fh, fi))
  | minusinf (Eq (Sub (ff, fg))) = Eq (Sub (ff, fg))
  | minusinf (Eq (Add (fd, fe))) = Eq (Add (fd, fe))
  | minusinf (Eq (Neg fc)) = Eq (Neg fc)
  | minusinf (Eq (Bound ez)) = Eq (Bound ez)
  | minusinf (Eq (C ey)) = Eq (C ey)
  | minusinf (Ge (Mul (el, em))) = Ge (Mul (el, em))
  | minusinf (Ge (Sub (ej, ek))) = Ge (Sub (ej, ek))
  | minusinf (Ge (Add (eh, ei))) = Ge (Add (eh, ei))
  | minusinf (Ge (Neg eg)) = Ge (Neg eg)
  | minusinf (Ge (Bound ed)) = Ge (Bound ed)
  | minusinf (Ge (C ec)) = Ge (C ec)
  | minusinf (Gt (Mul (dp, dq))) = Gt (Mul (dp, dq))
  | minusinf (Gt (Sub (dn, doa))) = Gt (Sub (dn, doa))
  | minusinf (Gt (Add (dl, dm))) = Gt (Add (dl, dm))
  | minusinf (Gt (Neg dk)) = Gt (Neg dk)
  | minusinf (Gt (Bound dh)) = Gt (Bound dh)
  | minusinf (Gt (C dg)) = Gt (C dg)
  | minusinf (Le (Mul (ct, cu))) = Le (Mul (ct, cu))
  | minusinf (Le (Sub (cr, cs))) = Le (Sub (cr, cs))
  | minusinf (Le (Add (cp, cq))) = Le (Add (cp, cq))
  | minusinf (Le (Neg co)) = Le (Neg co)
  | minusinf (Le (Bound cl)) = Le (Bound cl)
  | minusinf (Le (C ck)) = Le (C ck)
  | minusinf (Lt (Mul (bx, by))) = Lt (Mul (bx, by))
  | minusinf (Lt (Sub (bv, bw))) = Lt (Sub (bv, bw))
  | minusinf (Lt (Add (bt, bu))) = Lt (Add (bt, bu))
  | minusinf (Lt (Neg bs)) = Lt (Neg bs)
  | minusinf (Lt (Bound bp)) = Lt (Bound bp)
  | minusinf (Lt (C bo)) = Lt (C bo)
  | minusinf F = F
  | minusinf T = T
  | minusinf (Ge (Cx (c, e))) = F
  | minusinf (Gt (Cx (c, e))) = F
  | minusinf (Le (Cx (c, e))) = T
  | minusinf (Lt (Cx (c, e))) = T
  | minusinf (NEq (Cx (c, e))) = T
  | minusinf (Eq (Cx (c, e))) = F
  | minusinf (Or (p, q)) = Or (minusinf p, minusinf q)
  | minusinf (And (p, q)) = And (minusinf p, minusinf q);

fun numsubst0 t (Mul (i, a)) = Mul (i, numsubst0 t a)
  | numsubst0 t (Sub (a, b)) = Sub (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Add (a, b)) = Add (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Neg a) = Neg (numsubst0 t a)
  | numsubst0 t (Cx (i, a)) = Add (Mul (i, t), numsubst0 t a)
  | numsubst0 t (Bound n) =
    (if ((n : IntInf.int) = zero_nat) then t else Bound n)
  | numsubst0 t (C c) = C c;

fun subst0 t (NClosed p) = NClosed p
  | subst0 t (Closed p) = Closed p
  | subst0 t (Iffa (p, q)) = Iffa (subst0 t p, subst0 t q)
  | subst0 t (Impa (p, q)) = Impa (subst0 t p, subst0 t q)
  | subst0 t (Or (p, q)) = Or (subst0 t p, subst0 t q)
  | subst0 t (And (p, q)) = And (subst0 t p, subst0 t q)
  | subst0 t (Nota p) = Nota (subst0 t p)
  | subst0 t (NDvd (i, a)) = NDvd (i, numsubst0 t a)
  | subst0 t (Dvd (i, a)) = Dvd (i, numsubst0 t a)
  | subst0 t (NEq a) = NEq (numsubst0 t a)
  | subst0 t (Eq a) = Eq (numsubst0 t a)
  | subst0 t (Ge a) = Ge (numsubst0 t a)
  | subst0 t (Gt a) = Gt (numsubst0 t a)
  | subst0 t (Le a) = Le (numsubst0 t a)
  | subst0 t (Lt a) = Lt (numsubst0 t a)
  | subst0 t F = F
  | subst0 t T = T;

fun conj p q =
  (if eq_fm p F orelse eq_fm q F then F
    else (if eq_fm p T then q else (if eq_fm q T then p else And (p, q))));

fun disj p q =
  (if eq_fm p T orelse eq_fm q T then T
    else (if eq_fm p F then q else (if eq_fm q F then p else Or (p, q))));

fun nota (NClosed v) = Nota (NClosed v)
  | nota (Closed v) = Nota (Closed v)
  | nota (A v) = Nota (A v)
  | nota (E v) = Nota (E v)
  | nota (Iffa (v, va)) = Nota (Iffa (v, va))
  | nota (Impa (v, va)) = Nota (Impa (v, va))
  | nota (Or (v, va)) = Nota (Or (v, va))
  | nota (And (v, va)) = Nota (And (v, va))
  | nota (NDvd (v, va)) = Nota (NDvd (v, va))
  | nota (Dvd (v, va)) = Nota (Dvd (v, va))
  | nota (NEq v) = Nota (NEq v)
  | nota (Eq v) = Nota (Eq v)
  | nota (Ge v) = Nota (Ge v)
  | nota (Gt v) = Nota (Gt v)
  | nota (Le v) = Nota (Le v)
  | nota (Lt v) = Nota (Lt v)
  | nota F = T
  | nota T = F
  | nota (Nota y) = y;

fun imp p q =
  (if eq_fm p F orelse eq_fm q T then T
    else (if eq_fm p T then q
           else (if eq_fm q F then nota p else Impa (p, q))));

fun iff p q =
  (if eq_fm p q then T
    else (if eq_fm p (nota q) orelse eq_fm (nota p) q then F
           else (if eq_fm p F then nota q
                  else (if eq_fm q F then nota p
                         else (if eq_fm p T then q
                                else (if eq_fm q T then p
                                       else Iffa (p, q)))))));

fun simpfm (NClosed v) = NClosed v
  | simpfm (Closed v) = Closed v
  | simpfm (A v) = A v
  | simpfm (E v) = E v
  | simpfm F = F
  | simpfm T = T
  | simpfm (NDvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then simpfm (NEq a)
      else (if (((abs_int i) : IntInf.int) = (1 : IntInf.int)) then F
             else let
                    val a' = simpnum a;
                  in
                    (case a'
                       of C v =>
                         (if not (dvd (dvd_mod_int, eq_int) i v) then T else F)
                       | Bound nat => NDvd (i, a')
                       | Cx (int, num) => NDvd (i, a') | Neg num => NDvd (i, a')
                       | Add (num1, num2) => NDvd (i, a')
                       | Sub (num1, num2) => NDvd (i, a')
                       | Mul (int, num) => NDvd (i, a'))
                  end))
  | simpfm (Dvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then simpfm (Eq a)
      else (if (((abs_int i) : IntInf.int) = (1 : IntInf.int)) then T
             else let
                    val a' = simpnum a;
                  in
                    (case a'
                       of C v =>
                         (if dvd (dvd_mod_int, eq_int) i v then T else F)
                       | Bound nat => Dvd (i, a') | Cx (int, num) => Dvd (i, a')
                       | Neg num => Dvd (i, a')
                       | Add (num1, num2) => Dvd (i, a')
                       | Sub (num1, num2) => Dvd (i, a')
                       | Mul (int, num) => Dvd (i, a'))
                  end))
  | simpfm (NEq a) =
    let
      val a' = simpnum a;
    in
      (case a'
         of C v => (if not ((v : IntInf.int) = (0 : IntInf.int)) then T else F)
         | Bound nat => NEq a' | Cx (int, num) => NEq a' | Neg num => NEq a'
         | Add (num1, num2) => NEq a' | Sub (num1, num2) => NEq a'
         | Mul (int, num) => NEq a')
    end
  | simpfm (Eq a) =
    let
      val a' = simpnum a;
    in
      (case a'
         of C v => (if ((v : IntInf.int) = (0 : IntInf.int)) then T else F)
         | Bound nat => Eq a' | Cx (int, num) => Eq a' | Neg num => Eq a'
         | Add (num1, num2) => Eq a' | Sub (num1, num2) => Eq a'
         | Mul (int, num) => Eq a')
    end
  | simpfm (Ge a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.<= ((0 : IntInf.int), v) then T else F)
         | Bound nat => Ge a' | Cx (int, num) => Ge a' | Neg num => Ge a'
         | Add (num1, num2) => Ge a' | Sub (num1, num2) => Ge a'
         | Mul (int, num) => Ge a')
    end
  | simpfm (Gt a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.< ((0 : IntInf.int), v) then T else F)
         | Bound nat => Gt a' | Cx (int, num) => Gt a' | Neg num => Gt a'
         | Add (num1, num2) => Gt a' | Sub (num1, num2) => Gt a'
         | Mul (int, num) => Gt a')
    end
  | simpfm (Le a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.<= (v, (0 : IntInf.int)) then T else F)
         | Bound nat => Le a' | Cx (int, num) => Le a' | Neg num => Le a'
         | Add (num1, num2) => Le a' | Sub (num1, num2) => Le a'
         | Mul (int, num) => Le a')
    end
  | simpfm (Lt a) =
    let
      val a' = simpnum a;
    in
      (case a' of C v => (if IntInf.< (v, (0 : IntInf.int)) then T else F)
         | Bound nat => Lt a' | Cx (int, num) => Lt a' | Neg num => Lt a'
         | Add (num1, num2) => Lt a' | Sub (num1, num2) => Lt a'
         | Mul (int, num) => Lt a')
    end
  | simpfm (Nota p) = nota (simpfm p)
  | simpfm (Iffa (p, q)) = iff (simpfm p) (simpfm q)
  | simpfm (Impa (p, q)) = imp (simpfm p) (simpfm q)
  | simpfm (Or (p, q)) = disj (simpfm p) (simpfm q)
  | simpfm (And (p, q)) = conj (simpfm p) (simpfm q);

fun decrnum (Cx (w, x)) = Cx (w, x)
  | decrnum (C u) = C u
  | decrnum (Mul (c, a)) = Mul (c, decrnum a)
  | decrnum (Sub (a, b)) = Sub (decrnum a, decrnum b)
  | decrnum (Add (a, b)) = Add (decrnum a, decrnum b)
  | decrnum (Neg a) = Neg (decrnum a)
  | decrnum (Bound n) = Bound (nat (IntInf.- (n, (1 : IntInf.int))));

fun decr (NClosed ar) = NClosed ar
  | decr (Closed aq) = Closed aq
  | decr (A ap) = A ap
  | decr (E ao) = E ao
  | decr F = F
  | decr T = T
  | decr (Iffa (p, q)) = Iffa (decr p, decr q)
  | decr (Impa (p, q)) = Impa (decr p, decr q)
  | decr (Or (p, q)) = Or (decr p, decr q)
  | decr (And (p, q)) = And (decr p, decr q)
  | decr (Nota p) = Nota (decr p)
  | decr (NDvd (i, a)) = NDvd (i, decrnum a)
  | decr (Dvd (i, a)) = Dvd (i, decrnum a)
  | decr (NEq a) = NEq (decrnum a)
  | decr (Eq a) = Eq (decrnum a)
  | decr (Ge a) = Ge (decrnum a)
  | decr (Gt a) = Gt (decrnum a)
  | decr (Le a) = Le (decrnum a)
  | decr (Lt a) = Lt (decrnum a);

fun cooper p =
  let
    val (q, a) = unita p;
    val (b, d) = a;
    val js = iupt (1 : IntInf.int) d;
    val mq = simpfm (minusinf q);
    val md = evaldjf (fn j => simpfm (subst0 (C j) mq)) js;
  in
    (if eq_fm md T then T
      else let
             val qd =
               evaldjf (fn aa as (ba, j) => simpfm (subst0 (Add (ba, C j)) q))
                 (allpairs (fn aa => fn ba => (aa, ba)) b js);
           in
             decr (disj md qd)
           end)
  end;

fun prep (NClosed aq) = NClosed aq
  | prep (Closed ap) = Closed ap
  | prep (NDvd (ac, ad)) = NDvd (ac, ad)
  | prep (Dvd (aa, ab)) = Dvd (aa, ab)
  | prep (NEq z) = NEq z
  | prep (Eq y) = Eq y
  | prep (Ge x) = Ge x
  | prep (Gt w) = Gt w
  | prep (Le v) = Le v
  | prep (Lt u) = Lt u
  | prep F = F
  | prep T = T
  | prep (Iffa (p, q)) = Or (prep (And (p, q)), prep (And (Nota p, Nota q)))
  | prep (Impa (p, q)) = prep (Or (Nota p, q))
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (Nota (NClosed ck)) = Nota (prep (NClosed ck))
  | prep (Nota (Closed cj)) = Nota (prep (Closed cj))
  | prep (Nota (E ch)) = Nota (prep (E ch))
  | prep (Nota (NDvd (bw, bx))) = Nota (prep (NDvd (bw, bx)))
  | prep (Nota (Dvd (bu, bv))) = Nota (prep (Dvd (bu, bv)))
  | prep (Nota (NEq bt)) = Nota (prep (NEq bt))
  | prep (Nota (Eq bs)) = Nota (prep (Eq bs))
  | prep (Nota (Ge br)) = Nota (prep (Ge br))
  | prep (Nota (Gt bq)) = Nota (prep (Gt bq))
  | prep (Nota (Le bp)) = Nota (prep (Le bp))
  | prep (Nota (Lt bo)) = Nota (prep (Lt bo))
  | prep (Nota F) = Nota (prep F)
  | prep (Nota T) = Nota (prep T)
  | prep (Nota (Iffa (p, q))) =
    Or (prep (And (p, Nota q)), prep (And (Nota p, q)))
  | prep (Nota (Impa (p, q))) = And (prep p, prep (Nota q))
  | prep (Nota (Or (p, q))) = And (prep (Nota p), prep (Nota q))
  | prep (Nota (A p)) = prep (E (Nota p))
  | prep (Nota (And (p, q))) = Or (prep (Nota p), prep (Nota q))
  | prep (Nota (Nota p)) = prep p
  | prep (A (NClosed kj)) = prep (Nota (E (Nota (NClosed kj))))
  | prep (A (Closed ki)) = prep (Nota (E (Nota (Closed ki))))
  | prep (A (A kh)) = prep (Nota (E (Nota (A kh))))
  | prep (A (E kg)) = prep (Nota (E (Nota (E kg))))
  | prep (A (Iffa (ke, kf))) = prep (Nota (E (Nota (Iffa (ke, kf)))))
  | prep (A (Impa (kc, kd))) = prep (Nota (E (Nota (Impa (kc, kd)))))
  | prep (A (Or (ka, kb))) = prep (Nota (E (Nota (Or (ka, kb)))))
  | prep (A (Nota jx)) = prep (Nota (E (Nota (Nota jx))))
  | prep (A (NDvd (jv, jw))) = prep (Nota (E (Nota (NDvd (jv, jw)))))
  | prep (A (Dvd (jt, ju))) = prep (Nota (E (Nota (Dvd (jt, ju)))))
  | prep (A (NEq js)) = prep (Nota (E (Nota (NEq js))))
  | prep (A (Eq jr)) = prep (Nota (E (Nota (Eq jr))))
  | prep (A (Ge jq)) = prep (Nota (E (Nota (Ge jq))))
  | prep (A (Gt jp)) = prep (Nota (E (Nota (Gt jp))))
  | prep (A (Le jo)) = prep (Nota (E (Nota (Le jo))))
  | prep (A (Lt jn)) = prep (Nota (E (Nota (Lt jn))))
  | prep (A F) = prep (Nota (E (Nota F)))
  | prep (A T) = prep (Nota (E (Nota T)))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (E (NClosed fb)) = E (prep (NClosed fb))
  | prep (E (Closed fa)) = E (prep (Closed fa))
  | prep (E (A ez)) = E (prep (A ez))
  | prep (E (E ey)) = E (prep (E ey))
  | prep (E (And (eq, er))) = E (prep (And (eq, er)))
  | prep (E (Nota (NClosed hs))) = E (prep (Nota (NClosed hs)))
  | prep (E (Nota (Closed hr))) = E (prep (Nota (Closed hr)))
  | prep (E (Nota (A hq))) = E (prep (Nota (A hq)))
  | prep (E (Nota (E hp))) = E (prep (Nota (E hp)))
  | prep (E (Nota (Or (hj, hk)))) = E (prep (Nota (Or (hj, hk))))
  | prep (E (Nota (Nota hg))) = E (prep (Nota (Nota hg)))
  | prep (E (Nota (NDvd (he, hf)))) = E (prep (Nota (NDvd (he, hf))))
  | prep (E (Nota (Dvd (hc, hd)))) = E (prep (Nota (Dvd (hc, hd))))
  | prep (E (Nota (NEq hb))) = E (prep (Nota (NEq hb)))
  | prep (E (Nota (Eq ha))) = E (prep (Nota (Eq ha)))
  | prep (E (Nota (Ge gz))) = E (prep (Nota (Ge gz)))
  | prep (E (Nota (Gt gy))) = E (prep (Nota (Gt gy)))
  | prep (E (Nota (Le gx))) = E (prep (Nota (Le gx)))
  | prep (E (Nota (Lt gw))) = E (prep (Nota (Lt gw)))
  | prep (E (Nota F)) = E (prep (Nota F))
  | prep (E (Nota T)) = E (prep (Nota T))
  | prep (E (NDvd (en, eo))) = E (prep (NDvd (en, eo)))
  | prep (E (Dvd (el, em))) = E (prep (Dvd (el, em)))
  | prep (E (NEq ek)) = E (prep (NEq ek))
  | prep (E (Eq ej)) = E (prep (Eq ej))
  | prep (E (Ge ei)) = E (prep (Ge ei))
  | prep (E (Gt eh)) = E (prep (Gt eh))
  | prep (E (Le eg)) = E (prep (Le eg))
  | prep (E (Lt ef)) = E (prep (Lt ef))
  | prep (E (Nota (Iffa (p, q)))) =
    Or (prep (E (And (p, Nota q))), prep (E (And (Nota p, q))))
  | prep (E (Nota (Impa (p, q)))) = prep (E (And (p, Nota q)))
  | prep (E (Nota (And (p, q)))) = Or (prep (E (Nota p)), prep (E (Nota q)))
  | prep (E (Iffa (p, q))) =
    Or (prep (E (And (p, q))), prep (E (And (Nota p, Nota q))))
  | prep (E (Impa (p, q))) = Or (prep (E (Nota p)), prep (E q))
  | prep (E (Or (p, q))) = Or (prep (E p), prep (E q))
  | prep (E F) = F
  | prep (E T) = T;

fun qelim (NClosed aq) = (fn y => simpfm (NClosed aq))
  | qelim (Closed ap) = (fn y => simpfm (Closed ap))
  | qelim (NDvd (ac, ad)) = (fn y => simpfm (NDvd (ac, ad)))
  | qelim (Dvd (aa, ab)) = (fn y => simpfm (Dvd (aa, ab)))
  | qelim (NEq z) = (fn y => simpfm (NEq z))
  | qelim (Eq y) = (fn ya => simpfm (Eq y))
  | qelim (Ge x) = (fn y => simpfm (Ge x))
  | qelim (Gt w) = (fn y => simpfm (Gt w))
  | qelim (Le v) = (fn y => simpfm (Le v))
  | qelim (Lt u) = (fn y => simpfm (Lt u))
  | qelim F = (fn y => simpfm F)
  | qelim T = (fn y => simpfm T)
  | qelim (Iffa (p, q)) = (fn qe => iff (qelim p qe) (qelim q qe))
  | qelim (Impa (p, q)) = (fn qe => imp (qelim p qe) (qelim q qe))
  | qelim (Or (p, q)) = (fn qe => disj (qelim p qe) (qelim q qe))
  | qelim (And (p, q)) = (fn qe => conj (qelim p qe) (qelim q qe))
  | qelim (Nota p) = (fn qe => nota (qelim p qe))
  | qelim (A p) = (fn qe => nota (qe (qelim (Nota p) qe)))
  | qelim (E p) = (fn qe => dj qe (qelim p qe));

val pa : fm -> fm = (fn p => qelim (prep p) cooper);

end; (*struct GeneratedCooper*)

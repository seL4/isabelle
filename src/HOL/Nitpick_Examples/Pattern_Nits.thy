(*  Title:      HOL/Nitpick_Examples/Pattern_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick's "destroy_constrs" optimization.
*)

header {* Examples Featuring Nitpick's \textit{destroy\_constrs} Optimization *}

theory Pattern_Nits
imports Main
begin

nitpick_params [verbose, card = 8, max_potential = 0, sat_solver = MiniSat_JNI,
                max_threads = 1, timeout = 240]

lemma "x = (case u of () \<Rightarrow> y)"
nitpick [expect = genuine]
oops

lemma "x = (case b of True \<Rightarrow> x | False \<Rightarrow> y)"
nitpick [expect = genuine]
oops

lemma "x = (case p of (x, y) \<Rightarrow> y)"
nitpick [expect = genuine]
oops

lemma "x = (case n of 0 \<Rightarrow> x | Suc n \<Rightarrow> n)"
nitpick [expect = genuine]
oops

lemma "x = (case opt of None \<Rightarrow> x | Some y \<Rightarrow> y)"
nitpick [expect = genuine]
oops

lemma "x = (case xs of [] \<Rightarrow> x | y # ys \<Rightarrow> y)"
nitpick [expect = genuine]
oops

lemma "x = (case xs of
              [] \<Rightarrow> x
            | y # ys \<Rightarrow>
              (case ys of
                 [] \<Rightarrow> x
               | z # zs \<Rightarrow>
                 (case z of
                    None \<Rightarrow> x
                  | Some p \<Rightarrow>
                    (case p of
                       (a, b) \<Rightarrow> b))))"
nitpick [expect = genuine]
oops

fun f1 where
"f1 x () = x"

lemma "x = f1 y u"
nitpick [expect = genuine]
oops

fun f2 where
"f2 x _ True = x" |
"f2 _ y False = y"

lemma "x = f2 x y b"
nitpick [expect = genuine]
oops

fun f3 where
"f3 (_, y) = y"

lemma "x = f3 p"
nitpick [expect = genuine]
oops

fun f4 where
"f4 x 0 = x" |
"f4 _ (Suc n) = n"

lemma "x = f4 x n"
nitpick [expect = genuine]
oops

fun f5 where
"f5 x None = x" |
"f5 _ (Some y) = y"

lemma "x = f5 x opt"
nitpick [expect = genuine]
oops

fun f6 where
"f6 x [] = x" |
"f6 _ (y # ys) = y"

lemma "x = f6 x xs"
nitpick [expect = genuine]
oops

fun f7 where
"f7 _ (y # Some (a, b) # zs) = b" |
"f7 x (y # None # zs) = x" |
"f7 x [y] = x" |
"f7 x [] = x"

lemma "x = f7 x xs"
nitpick [expect = genuine]
oops

lemma "u = ()"
nitpick [expect = none]
sorry

lemma "\<exists>y. (b::bool) = y"
nitpick [expect = none]
sorry

lemma "\<exists>x y. p = (x, y)"
nitpick [expect = none]
sorry

lemma "\<exists>x. n = Suc x"
nitpick [expect = genuine]
oops

lemma "\<exists>y. x = Some y"
nitpick [expect = genuine]
oops

lemma "\<exists>y ys. xs = y # ys"
nitpick [expect = genuine]
oops

lemma "\<exists>y a b zs. x = y # Some (a, b) # zs"
nitpick [expect = genuine]
oops

end

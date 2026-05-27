(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Mathias Fleury, JKU, UFR
    Author:     Hanna Lachnitt, Stanford University

Half of the examples come from the corresponding file for z3 or veriT,
the others come from the Isabelle distribution or the AFP.
*)

section \<open>Examples for the cvc5-SMT binding\<close>

theory SMT_Examples_CVC
  imports Complex_Main
begin


external_file \<open>SMT_Examples_CVC.certs\<close>

declare [[smt_certificates = "SMT_Examples_CVC.certs"]]
declare [[smt_read_only_certificates = true]]


declare [[smt_trace=false,smt_verbose=false,smt_debug_verit=false,smt_statistics]]
declare [[smt_nat_as_int]]

declare[[smt_expert_debug_alethe_level=0]]
declare[[smt_expert_debug_alethe_files="all"]]

(*declare [[unify_trace_failure]]*)

lemma
  assumes "x \<ge> (3::int)" and "y = x + 4"
  shows "y - x > 0"
  using assms supply [[smt_trace,smt_debug_verit]] by (smt (cvc5_proof)) (*success*)

section \<open>Propositional and first-order logic\<close>

lemma "True" supply [[smt_trace]] by (smt (cvc5_proof)) (*success*)
declare[[smt_expert_debug_alethe_level=0]]

lemma "p \<or> \<not>p" by (smt (cvc5_proof)) (*success*)
lemma "(p \<and> True) = p" by (smt (cvc5_proof)) (*success*)
lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by (smt (cvc5_proof)) (*success*)
lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)" by (smt (cvc5_proof)) (*success*)
lemma "(p1 \<and> p2) \<or> p3 \<longrightarrow> (p1 \<longrightarrow> (p3 \<and> p2) \<or> (p1 \<and> p3)) \<or> p1" by (smt (cvc5_proof)) (*success*)
lemma "P = P = P = P = P = P = P = P = P = P" by (smt (cvc5_proof)) (*success*)

lemma
  assumes "a \<or> b \<or> c \<or> d"
      and "e \<or> f \<or> (a \<and> d)"
      and "\<not> (a \<or> (c \<and> ~c)) \<or> b"
      and "\<not> (b \<and> (x \<or> \<not> x)) \<or> c"
      and "\<not> (d \<or> False) \<or> c"
      and "\<not> (c \<or> (\<not> p \<and> (p \<or> (q \<and> \<not> q))))"
  shows False
  using assms supply [[smt_trace]] by (smt (cvc5_proof)) (*success*)

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"

lemma "a = a \<and> symm_f a b = symm_f b a"
  supply [[smt_trace]]
  by (smt (cvc5) symm_f) (*success*)

(*
Taken from ~~/src/HOL/ex/SAT_Examples.thy.
Translated from TPTP problem library: PUZ015-2.006.dimacs
*)
lemma
  assumes "~x0"
  and "~x30"
  and "~x29"
  and "~x59"
  and "x1 \<or> x31 \<or> x0"
  and "x2 \<or> x32 \<or> x1"
  and "x3 \<or> x33 \<or> x2"
  and "x4 \<or> x34 \<or> x3"
  and "x35 \<or> x4"
  and "x5 \<or> x36 \<or> x30"
  and "x6 \<or> x37 \<or> x5 \<or> x31"
  and "x7 \<or> x38 \<or> x6 \<or> x32"
  and "x8 \<or> x39 \<or> x7 \<or> x33"
  and "x9 \<or> x40 \<or> x8 \<or> x34"
  and "x41 \<or> x9 \<or> x35"
  and "x10 \<or> x42 \<or> x36"
  and "x11 \<or> x43 \<or> x10 \<or> x37"
  and "x12 \<or> x44 \<or> x11 \<or> x38"
  and "x13 \<or> x45 \<or> x12 \<or> x39"
  and "x14 \<or> x46 \<or> x13 \<or> x40"
  and "x47 \<or> x14 \<or> x41"
  and "x15 \<or> x48 \<or> x42"
  and "x16 \<or> x49 \<or> x15 \<or> x43"
  and "x17 \<or> x50 \<or> x16 \<or> x44"
  and "x18 \<or> x51 \<or> x17 \<or> x45"
  and "x19 \<or> x52 \<or> x18 \<or> x46"
  and "x53 \<or> x19 \<or> x47"
  and "x20 \<or> x54 \<or> x48"
  and "x21 \<or> x55 \<or> x20 \<or> x49"
  and "x22 \<or> x56 \<or> x21 \<or> x50"
  and "x23 \<or> x57 \<or> x22 \<or> x51"
  and "x24 \<or> x58 \<or> x23 \<or> x52"
  and "x59 \<or> x24 \<or> x53"
  and "x25 \<or> x54"
  and "x26 \<or> x25 \<or> x55"
  and "x27 \<or> x26 \<or> x56"
  and "x28 \<or> x27 \<or> x57"
  and "x29 \<or> x28 \<or> x58"
  and "~x1 \<or> ~x31"
  and "~x1 \<or> ~x0"
  and "~x31 \<or> ~x0"
  and "~x2 \<or> ~x32"
  and "~x2 \<or> ~x1"
  and "~x32 \<or> ~x1"
  and "~x3 \<or> ~x33"
  and "~x3 \<or> ~x2"
  and "~x33 \<or> ~x2"
  and "~x4 \<or> ~x34"
  and "~x4 \<or> ~x3"
  and "~x34 \<or> ~x3"
  and "~x35 \<or> ~x4"
  and "~x5 \<or> ~x36"
  and "~x5 \<or> ~x30"
  and "~x36 \<or> ~x30"
  and "~x6 \<or> ~x37"
  and "~x6 \<or> ~x5"
  and "~x6 \<or> ~x31"
  and "~x37 \<or> ~x5"
  and "~x37 \<or> ~x31"
  and "~x5 \<or> ~x31"
  and "~x7 \<or> ~x38"
  and "~x7 \<or> ~x6"
  and "~x7 \<or> ~x32"
  and "~x38 \<or> ~x6"
  and "~x38 \<or> ~x32"
  and "~x6 \<or> ~x32"
  and "~x8 \<or> ~x39"
  and "~x8 \<or> ~x7"
  and "~x8 \<or> ~x33"
  and "~x39 \<or> ~x7"
  and "~x39 \<or> ~x33"
  and "~x7 \<or> ~x33"
  and "~x9 \<or> ~x40"
  and "~x9 \<or> ~x8"
  and "~x9 \<or> ~x34"
  and "~x40 \<or> ~x8"
  and "~x40 \<or> ~x34"
  and "~x8 \<or> ~x34"
  and "~x41 \<or> ~x9"
  and "~x41 \<or> ~x35"
  and "~x9 \<or> ~x35"
  and "~x10 \<or> ~x42"
  and "~x10 \<or> ~x36"
  and "~x42 \<or> ~x36"
  and "~x11 \<or> ~x43"
  and "~x11 \<or> ~x10"
  and "~x11 \<or> ~x37"
  and "~x43 \<or> ~x10"
  and "~x43 \<or> ~x37"
  and "~x10 \<or> ~x37"
  and "~x12 \<or> ~x44"
  and "~x12 \<or> ~x11"
  and "~x12 \<or> ~x38"
  and "~x44 \<or> ~x11"
  and "~x44 \<or> ~x38"
  and "~x11 \<or> ~x38"
  and "~x13 \<or> ~x45"
  and "~x13 \<or> ~x12"
  and "~x13 \<or> ~x39"
  and "~x45 \<or> ~x12"
  and "~x45 \<or> ~x39"
  and "~x12 \<or> ~x39"
  and "~x14 \<or> ~x46"
  and "~x14 \<or> ~x13"
  and "~x14 \<or> ~x40"
  and "~x46 \<or> ~x13"
  and "~x46 \<or> ~x40"
  and "~x13 \<or> ~x40"
  and "~x47 \<or> ~x14"
  and "~x47 \<or> ~x41"
  and "~x14 \<or> ~x41"
  and "~x15 \<or> ~x48"
  and "~x15 \<or> ~x42"
  and "~x48 \<or> ~x42"
  and "~x16 \<or> ~x49"
  and "~x16 \<or> ~x15"
  and "~x16 \<or> ~x43"
  and "~x49 \<or> ~x15"
  and "~x49 \<or> ~x43"
  and "~x15 \<or> ~x43"
  and "~x17 \<or> ~x50"
  and "~x17 \<or> ~x16"
  and "~x17 \<or> ~x44"
  and "~x50 \<or> ~x16"
  and "~x50 \<or> ~x44"
  and "~x16 \<or> ~x44"
  and "~x18 \<or> ~x51"
  and "~x18 \<or> ~x17"
  and "~x18 \<or> ~x45"
  and "~x51 \<or> ~x17"
  and "~x51 \<or> ~x45"
  and "~x17 \<or> ~x45"
  and "~x19 \<or> ~x52"
  and "~x19 \<or> ~x18"
  and "~x19 \<or> ~x46"
  and "~x52 \<or> ~x18"
  and "~x52 \<or> ~x46"
  and "~x18 \<or> ~x46"
  and "~x53 \<or> ~x19"
  and "~x53 \<or> ~x47"
  and "~x19 \<or> ~x47"
  and "~x20 \<or> ~x54"
  and "~x20 \<or> ~x48"
  and "~x54 \<or> ~x48"
  and "~x21 \<or> ~x55"
  and "~x21 \<or> ~x20"
  and "~x21 \<or> ~x49"
  and "~x55 \<or> ~x20"
  and "~x55 \<or> ~x49"
  and "~x20 \<or> ~x49"
  and "~x22 \<or> ~x56"
  and "~x22 \<or> ~x21"
  and "~x22 \<or> ~x50"
  and "~x56 \<or> ~x21"
  and "~x56 \<or> ~x50"
  and "~x21 \<or> ~x50"
  and "~x23 \<or> ~x57"
  and "~x23 \<or> ~x22"
  and "~x23 \<or> ~x51"
  and "~x57 \<or> ~x22"
  and "~x57 \<or> ~x51"
  and "~x22 \<or> ~x51"
  and "~x24 \<or> ~x58"
  and "~x24 \<or> ~x23"
  and "~x24 \<or> ~x52"
  and "~x58 \<or> ~x23"
  and "~x58 \<or> ~x52"
  and "~x23 \<or> ~x52"
  and "~x59 \<or> ~x24"
  and "~x59 \<or> ~x53"
  and "~x24 \<or> ~x53"
  and "~x25 \<or> ~x54"
  and "~x26 \<or> ~x25"
  and "~x26 \<or> ~x55"
  and "~x25 \<or> ~x55"
  and "~x27 \<or> ~x26"
  and "~x27 \<or> ~x56"
  and "~x26 \<or> ~x56"
  and "~x28 \<or> ~x27"
  and "~x28 \<or> ~x57"
  and "~x27 \<or> ~x57"
  and "~x29 \<or> ~x28"
  and "~x29 \<or> ~x58"
  and "~x28 \<or> ~x58"
shows False
  supply [[smt_trace=false]] using assms by (smt (cvc5_proof)) (*success*)


lemma "\<forall>x::int. P x \<longrightarrow> (\<forall>y::int. P x \<or> P y)"
  supply[[smt_trace]]
  by (smt (cvc5_proof)) (*success*)

lemma "\<exists>x::int. x + 1 = x * 2"
  by (smt (cvc5_proof)) (*success*)

lemma
  assumes "(\<forall>x y. P x y = x)"
  shows "(\<exists>y. P x y) = P x c"
  supply[[smt_trace=false]]
  using assms by (smt (cvc5_proof)) (*success*)

lemma
  assumes "(\<forall>x y. P x y = x)"
  and "(\<forall>x. \<exists>y. P x y) = (\<forall>x. P x c)"
  shows "(\<exists>y. P x y) = P x c"
  supply[[smt_trace=false]]
  using assms by (smt (cvc5_proof)) (*success*)

lemma
  assumes "if P x then \<not>(\<exists>y. P y) else (\<forall>y. \<not>P y)"
  shows "P x \<longrightarrow> P y"
  using assms by (smt (cvc5_proof)) (*success*)

(*Normalization testing*)

lemma "(case a of
 True \<Rightarrow> False |
 False \<Rightarrow> True)
= (\<not>a)"
 supply[[smt_trace]] by (smt (cvc5_proof)) (*success*)

lemma "min (3::int) 5 = 3"
 supply[[smt_trace]] by (smt (cvc5_proof)) (*success*)

lemma "min (3::nat) 5 = 3"
 supply[[smt_trace,smt_nat_as_int]] by (smt (cvc5_proof)) (*success*)

lemma "min (3::nat) 5 = 3"
 supply[[smt_nat_as_int,smt_trace]] by (smt (cvc5_proof)) (*success*)

lemma "(3::nat) + x = (x + 3)"
  supply[[smt_nat_as_int,show_types,smt_trace]]
  by (smt (cvc5)) (*success*)


section \<open>Arithmetic\<close>

subsection \<open>Linear arithmetic over integers and reals\<close>

declare[[smt_debug_arith_verit=false]]

lemma "(3::nat) = 3" by (smt (cvc5_proof)) (*success*)
lemma "(3::int) = 3" by (smt (cvc5_proof)) (*success*)
lemma "(3::real) = 3" by (smt (cvc5_proof)) (*success*)
lemma "(3 :: int) + 1 = 4" by (smt (cvc5_proof)) (*success*)
lemma "x + (y + z) = y + (z + (x::int))" by (smt (cvc5_proof)) (*success*)
lemma "max (3::int) 8 > 5" by (smt (cvc5_proof)) (*success*)
lemma "\<bar>x :: real\<bar> + \<bar>y\<bar> \<ge> \<bar>x + y\<bar>" supply[[smt_trace=false,smt_verbose=false]] by (smt (cvc5_proof)) (*success*)
lemma "P ((2::int) < 3) = P True" by (smt (cvc5_proof)) (*success*)
lemma "x + 3 \<ge> 4 \<or> x < (1::int)" by (smt (cvc5_proof)) (*success*)

lemma
  assumes "x \<ge> (3::int)" and "y = x + 4"
  shows "y - x > 0"
  using assms by (smt (cvc5_proof)) (*success*)

lemma "let x = (2 :: int) in x + x \<noteq> 5" by (smt (cvc5_proof)) (*success*)


lemma
  fixes x :: int
  assumes "3 * x + 7 * a < 4" and "3 < 2 * x"
  shows "a < 0"
  supply[[smt_trace]]
  using assms by (smt (cvc5_proof)) (*success*)

lemma "(0 \<le> y + -1 * x \<or> \<not> 0 \<le> x \<or> 0 \<le> (x::int)) = (\<not> False)" by (smt (cvc5_proof)) (*success*)

lemma "
  (n < m \<and> m < n') \<or> (n < m \<and> m = n') \<or> (n < n' \<and> n' < m) \<or>
  (n = n' \<and> n' < m) \<or> (n = m \<and> m < n') \<or>
  (n' < m \<and> m < n) \<or> (n' < m \<and> m = n) \<or>
  (n' < n \<and> n < m) \<or> (n' = n \<and> n < m) \<or> (n' = m \<and> m < n) \<or>
  (m < n \<and> n < n') \<or> (m < n \<and> n' = n) \<or> (m < n' \<and> n' < n) \<or>
  (m = n \<and> n < n') \<or> (m = n' \<and> n' < n) \<or>
  (n' = m \<and> m = (n::int))"
  supply[[smt_trace=false]]
  by (smt (cvc5_proof)) (*success*)

text\<open>
The following example was taken from HOL/ex/PresburgerEx.thy, where it says:

  This following theorem proves that all solutions to the
  recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
  period 9.  The example was brought to our attention by John
  Harrison. It does does not require Presburger arithmetic but merely
  quantifier-free linear arithmetic and holds for the rationals as well.

  Warning: it takes (in 2006) over 4.2 minutes!

There, it is proved by "arith". (smt (cvc5)) is not able to prove this within a fraction
of one second. With proof reconstruction, it takes about 13 seconds on a Core2
processor.
\<close>


(*SOLVED: cvc5 does not find a proof unlike z3 or veriT
now it times out.*)
(*lemma "\<lbrakk> x3 = \<bar>x2\<bar> - x1; x4 = \<bar>x3\<bar> - x2; x5 = \<bar>x4\<bar> - x3;
         x6 = \<bar>x5\<bar> - x4; x7 = \<bar>x6\<bar> - x5; x8 = \<bar>x7\<bar> - x6;
         x9 = \<bar>x8\<bar> - x7; x10 = \<bar>x9\<bar> - x8; x11 = \<bar>x10\<bar> - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 \<and> x2 = (x11::int)"
  by (smt (cvc5_proof))*)


lemma "let P = 2 * x + 1 > x + (x::real) in P \<or> False \<or> P" by (smt (cvc5_proof)) (*success*)


subsection \<open>Linear arithmetic with quantifiers\<close>

lemma "~ (\<exists>x::int. False)" by (smt (cvc5_proof)) (*success*)
lemma "~ (\<exists>x::real. False)" by (smt (cvc5_proof)) (*success*)

lemma "\<forall>x y::int. (x = 0 \<and> y = 1) \<longrightarrow> x \<noteq> y" supply [[smt_trace]] by (smt (cvc5_proof)) (*success*)
lemma "\<forall>x y::int. x < y \<longrightarrow> (2 * x + 1) < (2 * y)" by (smt (cvc5_proof)) (*success*)
lemma "\<forall>x y::int. x + y > 2 \<or> x + y = 2 \<or> x + y < 2" supply[[smt_trace]] by (smt (cvc5_proof)) (*success*)
lemma "\<forall>x::int. if x > 0 then x + 1 > 0 else 1 > x" by (smt (cvc5_proof)) (*success*)
lemma "(if (\<forall>x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)" by (smt (cvc5_proof)) (*success*)
lemma "\<exists>x::int. \<forall>x y. 0 < x \<and> 0 < y \<longrightarrow> (0::int) < x + y" supply [[verit_compress_proofs=false,smt_trace]]by (smt (cvc5_proof)) (*success*)

experiment
begin
lemma [cvc5_holes_simp]: \<open>\<not>(\<forall>v2::real. v2 \<le> 0)\<close>
  by (auto intro: exI[of _ \<open>1 :: real\<close>])


lemma "\<exists>u::int. \<forall>(x::int) y::real. 0 < x \<and> 0 < y \<longrightarrow> -1 < x"
  supply [[smt_trace]] by (smt (cvc5_proof)) (*success*)
end

lemma "\<forall>(a::int) b::int. 0 < b \<or> b < 1" by (smt (cvc5_proof)) (*success*)

subsection \<open>Linear arithmetic for natural numbers\<close>

lemma "2 * (5+ (1::int)) = 12" supply[[smt_trace]] by (smt (cvc5_proof)) (*success*)

lemma "2 * (x::nat) \<noteq> 1" supply[[smt_trace]] by (smt (cvc5_proof)) (*success*)

lemma "a < 3 \<Longrightarrow> (7::nat) > 2 * a" by (smt (cvc5_proof)) (*success*)

lemma "let x = (1::nat) + y in x - y > 0 * x" by (smt (cvc5_proof)) (*success*)

lemma
  "let x = (1::nat) + y in
   let P = (if x > 0 then True else False) in
   False \<or> P = (x - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  supply[[smt_trace=false,smt_verbose=false]] 
  by (smt (cvc5_proof)) (*success*)

lemma "int (nat \<bar>x::int\<bar>) = \<bar>x\<bar>" supply[[smt_trace=false,smt_verbose=false]] by (smt (cvc5) int_nat_eq) (*success*)

definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

lemma "prime_nat (4*m + 1) \<Longrightarrow> m \<ge> (1::nat)" using prime_nat_def by (smt (cvc5)) (*success*)

lemma "2 * (x::nat) \<noteq> 1"
  by (smt (cvc5_proof)) (*success*)

lemma \<open>2*(x :: int) \<noteq> 1\<close>
  supply [[smt_trace]]
  by (smt (cvc5_proof)) (*success*)


section \<open>Pairs\<close>

lemma "fst (x, y) = a \<Longrightarrow> x = a"
  using fst_conv by (smt (cvc5_proof)) (*success*)

lemma "p1 = (x, y) \<and> p2 = (y, x) \<Longrightarrow> fst p1 = snd p2"
  using fst_conv snd_conv by (smt (cvc5_proof)) (*success*)


section \<open>Higher-order problems and recursion\<close>

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> (f (i1 := v1, i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by (smt (cvc5_proof)) (*success*)

lemma "(f g (x::'a::type) = (g x \<and> True)) \<or> (f g x = True) \<or> (g x = True)"
  by (smt (cvc5_proof)) (*success*)

lemma "id x = x \<and> id True = True"
  by (smt (cvc5) id_def) (*success*)

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> ((f (i1 := v1)) (i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by (smt (cvc5_proof)) (*success*)

lemma
  "f (\<exists>x. g x) \<Longrightarrow> True"
  "f (\<forall>x. g x) \<Longrightarrow> True"
  by (smt (cvc5_proof))+ (*success*)

lemma True using let_rsp by (smt (cvc5_proof)) (*success*)
lemma "le = (\<le>) \<Longrightarrow> le (3::int) 42" by (smt (cvc5_proof))  (*success*)
lemma "map (\<lambda>i::int. i + 1) [0, 1] = [1, 2]" by (smt (cvc5) list.map) (*success*)
lemma "(\<forall>x. P x) \<or> \<not> All P" by (smt (cvc5_proof)) (*success*)

fun dec_10 :: "int \<Rightarrow> int" where
  "dec_10 n = (if n < 10 then n else dec_10 (n - 10))"

lemma "dec_10 (4 * dec_10 4) = 6"
  supply[[smt_trace=false,smt_verbose=false]] by (smt (cvc5) dec_10.simps) (*success*)

experiment
begin
lemma (in complete_lattice) [cvc5_holes_pre]:
  \<open>(\<forall>(v0) (v1) v2. v0 \<le> v1 \<and> v1 \<le> v2 \<longrightarrow> v0 \<le> v2) = (\<forall>v0 v1 v2. \<not> v0 \<le> v1 \<or> \<not> v1 \<le> v2 \<or> v0 \<le> v2) \<close>
  by auto

lemma (in complete_lattice)
  assumes "Sup {a | i::bool. True} \<le> Sup {b | i::bool. True}"
  and "Sup {b | i::bool. True} \<le> Sup {a | i::bool. True}"
  shows "Sup {a | i::bool. True} \<le> Sup {a | i::bool. True}"
  using assms by (smt (cvc5) order_trans) (*success*)
end

experiment
begin

lemma
 "eq_set (List.coset xs) (set ys) = rhs"
    if "\<And>ys. subset' (List.coset xs) (set ys) = (let n = card (UNIV::'a set) in 0 < n \<and> card (set (xs @ ys)) = n)"
      and "\<And>uu A. (uu::'a) \<in> - A \<Longrightarrow> uu \<notin> A"
      and "\<And>uu. card (set (uu::'a list)) = length (remdups uu)"
      and "\<And>uu. finite (set (uu::'a list))"
      and "\<And>uu. (uu::'a) \<in> UNIV"
      and "(UNIV::'a set) \<noteq> {}"
      and "\<And>c A B P. \<lbrakk>(c::'a) \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
      and "\<And>a b. (a::nat) + b = b + a"
      and "\<And>a b. ((a::nat) = a + b) = (b = 0)"
      and "card' (set xs) = length (remdups xs)"
      and "card' = (card :: 'a set \<Rightarrow> nat)"
      and "\<And>A B. \<lbrakk>finite (A::'a set); finite B\<rbrakk> \<Longrightarrow> card A + card B = card (A \<union> B) + card (A \<inter> B)"
      and "\<And>A. (card (A::'a set) = 0) = (A = {} \<or> infinite A)"
      and "\<And>A. \<lbrakk>finite (UNIV::'a set); card (A::'a set) = card (UNIV::'a set)\<rbrakk> \<Longrightarrow> A = UNIV"
      and "\<And>xs. - List.coset (xs::'a list) = set xs"
      and "\<And>xs. - set (xs::'a list) = List.coset xs"
      and "\<And>A B. (A \<inter> B = {}) = (\<forall>x. (x::'a) \<in> A \<longrightarrow> x \<notin> B)"
      and "eq_set = (=)"
      and "\<And>A. finite (A::'a set) \<Longrightarrow> finite (- A) = finite (UNIV::'a set)"
      and "rhs \<equiv> let n = card (UNIV::'a set) in if n = 0 then False else let xs' = remdups xs; ys' = remdups ys in length xs' + length ys' = n \<and> (\<forall>x\<in>set xs'. x \<notin> set ys') \<and> (\<forall>y\<in>set ys'. y \<notin> set xs')"
      and "\<And>xs ys. set ((xs::'a list) @ ys) = set xs \<union> set ys"
      and "\<And>A B. ((A::'a set) = B) = (A \<subseteq> B \<and> B \<subseteq> A)"
      and "\<And>xs. set (remdups (xs::'a list)) = set xs"
      and "subset' = (\<subseteq>)"
      and "\<And>A B. (\<And>x. (x::'a) \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
      and "\<And>A B. \<lbrakk>(A::'a set) \<subseteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> A = B"
      and "\<And>A ys. (A \<subseteq> List.coset ys) = (\<forall>y\<in>set ys. (y::'a) \<notin> A)"
  using that supply[[smt_trace=false,smt_verbose=false,smt_statistics]] by (smt (cvc5_proof)) (*success but no nat to int embedding*)
end

notepad
begin
  have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
    if \<open>(k, g) \<in> one_chain_typeI\<close>
      \<open>\<And>A b B. ({} = (A::(real \<times> real) set) \<inter> insert (b::real \<times> real) (B::(real \<times> real) set)) = (b \<notin> A \<and> {} = A \<inter> B)\<close>
      \<open>finite ({} :: (real \<times> real) set)\<close>
      \<open>\<And>a A. finite (A::(real \<times> real) set) \<Longrightarrow> finite (insert (a::real \<times> real) A)\<close>
      \<open>(i::real \<times> real) = (1::real, 0::real)\<close>
      \<open> \<And>a A. (a::real \<times> real) \<in> (A::(real \<times> real) set) \<Longrightarrow> insert a A = A\<close> \<open>j = (0, 1)\<close>
      \<open>\<And>x. (x::(real \<times> real) set) \<inter> {} = {}\<close>
      \<open>\<And>y x A. insert (x::real \<times> real) (insert (y::real \<times> real) (A::(real \<times> real) set)) =  insert y (insert x A)\<close>
      \<open>\<And>a A. insert (a::real \<times> real) (A::(real \<times> real) set) = {a} \<union> A\<close>
      \<open>\<And>F u basis2 basis1 \<gamma>. finite (u :: (real \<times> real) set) \<Longrightarrow>
    line_integral_exists F basis1 \<gamma> \<Longrightarrow>
    line_integral_exists F basis2 \<gamma> \<Longrightarrow>
    basis1 \<union> basis2 = u \<Longrightarrow>
    basis1 \<inter> basis2 = {} \<Longrightarrow>
    line_integral F u \<gamma> = line_integral F basis1 \<gamma> + line_integral F basis2 \<gamma>\<close>
      \<open>one_chain_line_integral F {i} one_chain_typeI =
    one_chain_line_integral F {i} one_chain_typeII \<and>
    (\<forall>(k, \<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>) \<and>
    (\<forall>(k, \<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>)\<close>
      \<open> one_chain_line_integral (F::real \<times> real \<Rightarrow> real \<times> real) {j::real \<times> real}
     (one_chain_typeII::(int \<times> (real \<Rightarrow> real \<times> real)) set) =
    one_chain_line_integral F {j} (one_chain_typeI::(int \<times> (real \<Rightarrow> real \<times> real)) set) \<and>
    (\<forall>(k::int, \<gamma>::real \<Rightarrow> real \<times> real)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>) \<and>
    (\<forall>(k::int, \<gamma>::real \<Rightarrow> real \<times> real)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>)\<close>
    for F i j g one_chain_typeI one_chain_typeII and
      line_integral :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (real \<Rightarrow> real \<times> real) \<Rightarrow> real\<close> and
      line_integral_exists :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (real \<Rightarrow> real \<times> real) \<Rightarrow> bool\<close> and
      one_chain_line_integral :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (int \<times> (real \<Rightarrow> real \<times> real)) set \<Rightarrow> real\<close> and
      k
    using prod.case_eq_if singleton_inject snd_conv
      that [[smt_trace=false,smt_verbose=false]] by (smt (cvc5_proof)) (*success*)
end


lemma
  fixes x y z :: real
  assumes \<open>x + 2 * y > 0\<close> and
    \<open>x - 2 * y > 0\<close> and
    \<open>x < 0\<close>
  shows False
  using assms by (smt (cvc5_proof)) (*success*)

context
begin

(*test for arith reconstruction*)
lemma
  fixes d :: real
  assumes \<open>0 < d\<close>
   \<open>diamond_y \<equiv> \<lambda>t. d / 2 - \<bar>t\<bar>\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b :: real. - a / b = - (a / b)\<close>
   \<open>\<And>a b :: real. - a * b = - (a * b)\<close>
   \<open>\<And>(x1 :: real) x2 y1 y2 :: real. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)\<close>
 shows \<open>(\<lambda>y. (d / 2, (2 * y - 1) * diamond_y (d / 2))) \<noteq>
    (\<lambda>x. ((x - 1 / 2) * d, - diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    (\<lambda>y. (- (d / 2), (2 * y - 1) * diamond_y (- (d / 2)))) =
    (\<lambda>x. ((x - 1 / 2) * d, diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    False\<close>
  using assms supply [[smt_trace=false,smt_verbose=false]] by (smt (cvc5_proof)) (*success*)

lemma
  fixes d :: real
  assumes \<open>0 < d\<close>
   \<open>diamond_y \<equiv> \<lambda>t. d / 2 - \<bar>t\<bar>\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b :: real. - a / b = - (a / b)\<close>
   \<open>\<And>a b :: real. - a * b = - (a * b)\<close>
   \<open>\<And>(x1 :: real) x2 y1 y2 :: real. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)\<close>
 shows \<open>(\<lambda>y. (d / 2, (2 * y - 1) * diamond_y (d / 2))) \<noteq>
    (\<lambda>x. ((x - 1 / 2) * d, - diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    (\<lambda>y. (- (d / 2), (2 * y - 1) * diamond_y (- (d / 2)))) =
    (\<lambda>x. ((x - 1 / 2) * d, diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    False\<close>
  using assms supply [[smt_trace=false,smt_verbose=false]]
  by (smt (cvc5_proof)) (*success*)

end
(*qnt_rm_unused example*)
lemma 
  assumes \<open>\<forall>z y x. P z y\<close>
    \<open>P z y \<Longrightarrow> False\<close>
  shows False
  using assms
  by (smt (cvc5_proof)) (*success*)


lemma
  "max (x::int) y \<ge> y"
  supply [[smt_trace=false,smt_verbose=false]]
  by (smt (cvc5_proof))+  (*success*)

context
begin
abbreviation finite' :: "'a set \<Rightarrow> bool"
  where "finite' A \<equiv> finite A \<and> A \<noteq> {}"

lemma
  fixes f :: "'b \<Rightarrow> 'c :: linorder"
  assumes
    \<open>\<forall>(S::'b::type set) f::'b::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'a::type set) f::'a::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'b::type set) (y::'b::type) f::'b::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(S::'a::type set) (y::'a::type) f::'a::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (g::'a::type \<Rightarrow> 'b::type) x::'a::type. (f \<circ> g) x = f (g x)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'a::type) A::'b::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'b::type) A::'b::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'b::type) A::'a::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'a::type) A::'a::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (A::'b::type set) (x::'b::type) y::'b::type.
       inj_on f A \<and> f x = f y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y\<close>
    \<open>\<forall>(x::'c::linorder) y::'c::linorder. (x < y) = (x \<le> y \<and> x \<noteq> y)\<close>
    \<open>inj_on (f::'b::type \<Rightarrow> 'c::linorder) ((g::'a::type \<Rightarrow> 'b::type) ` (B::'a::type set))\<close>
    \<open>finite (B::'a::type set)\<close>
    \<open>(B::'a::type set) \<noteq> {}\<close>
    \<open>arg_min_on ((f::'b::type \<Rightarrow> 'c::linorder) \<circ> (g::'a::type \<Rightarrow> 'b::type)) (B::'a::type set) \<in> B\<close>
    \<open>\<nexists>x::'a::type.
       x \<in> (B::'a::type set) \<and>
       ((f::'b::type \<Rightarrow> 'c::linorder) \<circ> (g::'a::type \<Rightarrow> 'b::type)) x < (f \<circ> g) (arg_min_on (f \<circ> g) B)\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (P::'b::type \<Rightarrow> bool) a::'b::type.
       inj_on f (Collect P) \<and> P a \<and> (\<forall>y::'b::type. P y \<longrightarrow> f a \<le> f y) \<longrightarrow> arg_min f P = a\<close>
    \<open>\<forall>(S::'b::type set) f::'b::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'a::type set) f::'a::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'b::type set) (y::'b::type) f::'b::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(S::'a::type set) (y::'a::type) f::'a::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (g::'a::type \<Rightarrow> 'b::type) x::'a::type. (f \<circ> g) x = f (g x)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'a::type) A::'b::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'b::type) A::'b::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'b::type) A::'a::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'a::type) A::'a::type set. (f ` A = {}) = (A = {})\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (A::'b::type set) (x::'b::type) y::'b::type.
       inj_on f A \<and> f x = f y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y\<close>
    \<open>\<forall>(x::'c::linorder) y::'c::linorder. (x < y) = (x \<le> y \<and> x \<noteq> y)\<close>
    \<open>arg_min_on (f::'b::type \<Rightarrow> 'c::linorder) ((g::'a::type \<Rightarrow> 'b::type) ` (B::'a::type set)) \<noteq>
       g (arg_min_on (f \<circ> g) B) \<close>
   shows False
  using assms supply [[smt_trace=false,smt_verbose=false]]
  by (smt (cvc5_proof)) (*success*)
end


context
  fixes piecewise_C1 :: "('real :: {one,zero,ord} \<Rightarrow> 'a :: {one,zero,ord}) \<Rightarrow> 'real set \<Rightarrow> bool"  and
     joinpaths :: "('real \<Rightarrow> 'a) \<Rightarrow> ('real \<Rightarrow> 'a) \<Rightarrow> 'real \<Rightarrow> 'a"
begin
notation piecewise_C1 (infixr "piecewise'_C1'_differentiable'_on" 50)
notation joinpaths (infixr "+++" 75)

lemma
   \<open>(\<And>v1. \<forall>v0. (rec_join v0 = v1 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = v1 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> v1 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> v1 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow> False) \<longrightarrow>
               False) =
              (rec_join v0 = rec_join v0 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = rec_join v0 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> rec_join v0 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> rec_join v0 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow>
                   False) \<longrightarrow>
               False)) \<Longrightarrow>
         (\<forall>v0 v1.
             rec_join v0 = v1 \<and>
             (v0 = [] \<and> (\<lambda>uu. 0) = v1 \<longrightarrow> False) \<and>
             (\<forall>v2. v0 = [v2] \<and> v1 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
             (\<forall>v2 v3 v4. v0 = v2 # v3 # v4 \<and> v1 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow> False) \<longrightarrow>
             False) =
         (\<forall>v0. rec_join v0 = rec_join v0 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = rec_join v0 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> rec_join v0 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> rec_join v0 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow>
                   False) \<longrightarrow>
               False)\<close>
  supply [[smt_trace=false,smt_verbose=false]]
  by (smt (cvc5_proof)) (*success*)
end


section \<open>Bugs\<close>

context
  fixes centered_divide :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cdiv\<close> 70) and
    centered_modulo :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cmod\<close> 70)
begin

declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]
lemma zero_cdiv_eq [simp]:
  assumes
       "\<forall>(b::int) (a::int) c::int. b * (a div b) + a mod b + c = a + c"
       "\<forall>k::int. k cdiv (0::int) = (0::int)"
       "\<forall>(k::int) l::int. k cdiv l * l + k cmod l = k"
       "\<forall>(k::int) l::int.
          k cmod l = (k + (if l < (0::int) then - l else l) div (2::int)) mod (if l < (0::int) then - l else l) - (if l < (0::int) then - l else l) div (2::int)"
       "\<forall>(A::int) n::int. A = A div n * n + A mod n"
       "\<forall>a::int. even a = (a mod (2::int) = (0::int))"
       "\<forall>k::int. ((0::int) \<le> k div (2::int)) = ((0::int) \<le> k)"
       "\<forall>(k::int) l::int. (0::int) \<le> k \<and> k < l \<longrightarrow> k mod l = k"
       "\<forall>(c::int) b::int. (c = b * c) = (c = (0::int) \<or> b = (1::int))"
       "\<forall>(a::int) b::int. a \<noteq> (0::int) \<longrightarrow> a * b div a = b"
       "\<forall>a::int. odd a = (a mod (2::int) = (1::int))"
       shows
  \<open>0 cdiv k = 0\<close>
  supply [[smt_trace=false,smt_verbose=false,smt_statistics]]
  by (smt (cvc5) assms) (*error*)

(*
final cong:
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 26 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 24 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 24 ms total time
              

new cong:
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 26 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 12 ms maximum time, 38 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 25 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 25 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 28 ms total time
                                 

old cong:
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 3 ms maximum time, 50 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 2 ms maximum time, 36 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 2 ms maximum time, 35 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 2 ms maximum time, 37 ms total time
cong: 415 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 2 ms maximum time, 36 ms total time
                    
*)
end

context
  fixes
   round_up :: "int \<Rightarrow> real \<Rightarrow> real"and
   round_down :: "int \<Rightarrow> real \<Rightarrow> real" and
   powr :: \<open>real \<Rightarrow> real \<Rightarrow> real\<close> (infix "powr2" 80)
  assumes powr_gt_zero: \<open>\<And>a b :: real. 0 < x powr2 a \<longleftrightarrow> x \<noteq> 0\<close>
   and powr_minus_divide: "\<And>a x :: real. x powr2 (- a) = 1/(x powr2 a)"
   and round_up_diff_round_down: \<open>\<And>prec (x::real). round_up prec x - round_down prec x
    \<le> 2 powr2 (- real_of_int prec)\<close> 
   and round_down_uminus_eq: \<open>\<And>prec x. round_down p (- x) = - round_up p x\<close>
   and round_up: \<open>\<And>prec x. x \<le> round_up prec x\<close>
   and round_up_diff_round_down: \<open>\<And>prec x. round_up prec x - round_down prec x \<le> 2 powr2 (- real_of_int prec)\<close>

begin

lemma
  assumes "x < 1 / 2" \<open>p > 0\<close>
     \<open>1 / 2 * 2 powr2 real_of_int p \<le> 2 powr2 real_of_int p - 1\<close> 
     \<open>x * 2 powr2 real_of_int p < 1 / 2 * 2 powr2 real_of_int p\<close>
  shows "round_up p x < 1"
  supply [[smt_trace=false,smt_statistics=true,smt_verbose=false,
ML_print_depth=1000,show_types]]
  using comm_semiring_class.distrib divide_divide_eq_right
 mult.assoc mult.commute mult_cancel_left1 mult_cancel_right mult_cancel_right2
 mult_less_cancel_left_pos mult_minus_left nonzero_eq_divide_eq nonzero_mult_div_cancel_left
 nonzero_mult_div_cancel_right powr_gt_zero powr_minus_divide round_down_uminus_eq
 round_up round_up_diff_round_down times_divide_eq_right assms
  by (smt (cvc5))

lemma
  assumes "x < 1 / 2" \<open>p > 0\<close>
     \<open>1 / 2 * 2 powr2 real_of_int p \<le> 2 powr2 real_of_int p - 1\<close> 
     \<open>x * 2 powr2 real_of_int p < 1 / 2 * 2 powr2 real_of_int p\<close>
  shows "round_up p x < 1"
  supply [[smt_trace=false,smt_statistics=true,smt_verbose=false,
        ML_print_depth=1000,show_types,alethe_use_propositional_skeleton=false]]
  using comm_semiring_class.distrib divide_divide_eq_right
 mult.assoc mult.commute mult_cancel_left1 mult_cancel_right mult_cancel_right2
 mult_less_cancel_left_pos mult_minus_left nonzero_eq_divide_eq nonzero_mult_div_cancel_left
 nonzero_mult_div_cancel_right powr_gt_zero powr_minus_divide round_down_uminus_eq
 round_up round_up_diff_round_down times_divide_eq_right assms
  by (smt (cvc5))

end

section \<open>Monomorphization examples\<close>

definition Pred :: "'a \<Rightarrow> bool" where
  "Pred x = True"

lemma poly_Pred: "Pred x \<and> (Pred [x] \<or> \<not> Pred [x])"
  by (simp add: Pred_def)

lemma "Pred (1::int)"
  by (smt (cvc5) poly_Pred)

axiomatization g :: "'a \<Rightarrow> nat"
axiomatization where
  g1: "g (Some x) = g [x]" and
  g2: "g None = g []" and
  g3: "g xs = length xs"

lemma "g (Some (3::int)) = g (Some True)" by (smt (cvc5) g1 g2 g3 list.size)


section \<open>cvc5 only examples\<close>

declare[[smt_expert_debug_alethe_files="smt_global_normalize"]]
declare[[smt_expert_debug_alethe_level=3]]

(*("current term",
 Const ("SMT.pow_2", "int \<Rightarrow> int") $
   (Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $
     (Const ("Num.num.Bit1", "num \<Rightarrow> num") $
       Const ("Num.num.One", "num")))) (line 359 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_global_normalize.ML") 
("builtin fun", false) (line 367 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_global_normalize.ML") 
("builtin fun ext", false) (line 368 of "/h*)
lemma "(3::nat) ^ 3 = 27"
  using power_0 power_Suc
  (*apply (smt (cvc5)) (*finds no proof*)*)
  oops

datatype 'a extended = Fin 'a | Pinf ("\<infinity>") | Minf ("-\<infinity>")
instantiation extended :: (plus)plus
begin

fun plus_extended where
"Fin x + Fin y = Fin(x+y)" |
"Fin x + Pinf  = Pinf" |
"Pinf  + Fin x = Pinf" |
"Pinf  + Pinf  = Pinf" |
"Minf  + Fin y = Minf" |
"Fin x + Minf  = Minf" |
"Minf  + Minf  = Minf" |
"Minf  + Pinf  = Pinf" |
"Pinf  + Minf  = Pinf"


instance ..

end
instantiation extended :: (zero)zero
begin
definition "0 = Fin(0::'a)"
instance ..
end

lemma
  assumes
       "\<forall>a::'a::comm_monoid_add. (0::'a::comm_monoid_add) + a = a"
       "\<forall>(x::'a::comm_monoid_add extended extended extended extended extended extended)
          (xa::'a::comm_monoid_add extended extended extended extended extended extended)
          y::'a::comm_monoid_add extended extended extended extended extended extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add extended extended extended extended extended) ya::'a::comm_monoid_add extended extended extended extended extended.
              x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended extended. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended extended. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add extended extended extended extended extended. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended extended. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended extended extended extended extended) (xa::'a::comm_monoid_add extended extended extended extended extended)
          y::'a::comm_monoid_add extended extended extended extended extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add extended extended extended extended) ya::'a::comm_monoid_add extended extended extended extended.
              x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add extended extended extended extended. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended extended. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended extended extended extended) (xa::'a::comm_monoid_add extended extended extended extended)
          y::'a::comm_monoid_add extended extended extended extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add extended extended extended) ya::'a::comm_monoid_add extended extended extended.
              x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add extended extended extended. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended extended. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended extended extended) (xa::'a::comm_monoid_add extended extended extended) y::'a::comm_monoid_add extended extended extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add extended extended) ya::'a::comm_monoid_add extended extended. x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add extended extended. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended extended. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended extended) (xa::'a::comm_monoid_add extended extended) y::'a::comm_monoid_add extended extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add extended) ya::'a::comm_monoid_add extended. x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add extended. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add extended. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended) (xa::'a::comm_monoid_add extended) y::'a::comm_monoid_add extended.
          x + xa = y \<and>
          (\<forall>(xb::'a::comm_monoid_add) ya::'a::comm_monoid_add. x = Fin xb \<and> xa = Fin ya \<and> y = Fin (xb + ya) \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add. x = Fin xb \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add. x = \<infinity> \<and> xa = Fin xb \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (x = \<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and>
          (\<forall>ya::'a::comm_monoid_add. x = -\<infinity> \<and> xa = Fin ya \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (\<forall>xb::'a::comm_monoid_add. x = Fin xb \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and>
          (x = -\<infinity> \<and> xa = -\<infinity> \<and> y = -\<infinity> \<longrightarrow> False) \<and> (x = -\<infinity> \<and> xa = \<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<and> (x = \<infinity> \<and> xa = -\<infinity> \<and> y = \<infinity> \<longrightarrow> False) \<longrightarrow>
          False"
       "\<forall>(x::'a::comm_monoid_add extended extended extended extended extended) y::'a::comm_monoid_add extended extended extended extended extended.
          Fin x + Fin y = Fin (x + y)"
       "\<forall>(x::'a::comm_monoid_add extended extended extended extended) y::'a::comm_monoid_add extended extended extended extended. Fin x + Fin y = Fin (x + y)"
       "\<forall>(x::'a::comm_monoid_add extended extended extended) y::'a::comm_monoid_add extended extended extended. Fin x + Fin y = Fin (x + y)"
       "\<forall>(x::'a::comm_monoid_add extended extended) y::'a::comm_monoid_add extended extended. Fin x + Fin y = Fin (x + y)"
       "\<forall>(x::'a::comm_monoid_add extended) y::'a::comm_monoid_add extended. Fin x + Fin y = Fin (x + y)"
       "\<forall>(x::'a::comm_monoid_add) y::'a::comm_monoid_add. Fin x + Fin y = Fin (x + y)"
       "\<forall>x::'a::comm_monoid_add extended extended extended extended. Fin x + \<infinity> = \<infinity>"
       "\<forall>x::'a::comm_monoid_add extended extended extended. Fin x + \<infinity> = \<infinity>"
       "\<forall>x::'a::comm_monoid_add extended extended. Fin x + \<infinity> = \<infinity>"
       "\<forall>x::'a::comm_monoid_add extended. Fin x + \<infinity> = \<infinity>"
       "\<forall>x::'a::comm_monoid_add. Fin x + \<infinity> = \<infinity>"
       "\<forall>x::'a::comm_monoid_add extended extended extended extended. Fin x + -\<infinity> = -\<infinity>"
       "\<forall>x::'a::comm_monoid_add extended extended extended. Fin x + -\<infinity> = -\<infinity>"
       "\<forall>x::'a::comm_monoid_add extended extended. Fin x + -\<infinity> = -\<infinity>"
       "\<forall>x::'a::comm_monoid_add extended. Fin x + -\<infinity> = -\<infinity>"
       "\<forall>x::'a::comm_monoid_add. Fin x + -\<infinity> = -\<infinity>"
       "(0::'a::comm_monoid_add extended extended extended extended extended) = Fin (0::'a::comm_monoid_add extended extended extended extended)"
       "(0::'a::comm_monoid_add extended extended extended extended) = Fin (0::'a::comm_monoid_add extended extended extended)"
       "(0::'a::comm_monoid_add extended extended extended) = Fin (0::'a::comm_monoid_add extended extended)"
       "(0::'a::comm_monoid_add extended extended) = Fin (0::'a::comm_monoid_add extended)"
       "(0::'a::comm_monoid_add extended) = Fin (0::'a::comm_monoid_add)"
   shows
       "Fin (0::'a::comm_monoid_add) + (x::'a::comm_monoid_add extended) = x "
  supply [[smt_trace=false,smt_statistics]]
  using assms
  by (smt (cvc5,no_ematching))

lemma
  assumes 
      "\<forall>(a::'a \<Rightarrow> 'b) (b::'a \<Rightarrow> 'b) A::('a \<Rightarrow> 'b) set. (a \<in> insert b A) = (a = b \<or> a \<in> A)"
      "\<forall>(a::'a) (b::'a) A::'a set. (a \<in> insert b A) = (a = b \<or> a \<in> A)"
      "\<forall>(a::'b) (b::'b) A::'b set. (a \<in> insert b A) = (a = b \<or> a \<in> A)"
      "\<forall>(a::'a) P::'a \<Rightarrow> bool. (a \<in> Collect P) = P a"
      "\<forall>(a::'b) P::'b \<Rightarrow> bool. (a \<in> Collect P) = P a"
      "\<forall>(a::'a \<Rightarrow> 'b) P::('a \<Rightarrow> 'b) \<Rightarrow> bool. (a \<in> Collect P) = P a"
      "(f0::'a \<Rightarrow> 'b) \<in> {f::'a \<Rightarrow> 'b. \<forall>a::'a. if a \<in> (A'::'a set) then f a \<in> (B::'a \<Rightarrow> 'b set) a else f a = (f0::'a \<Rightarrow> 'b) a}"
      "(f::'a \<Rightarrow> 'b) \<in> {f'::'a \<Rightarrow> 'b. \<forall>a'::'a. if (a::'a) = a' then f' a \<in> (B::'a \<Rightarrow> 'b set) a else f' a' = (f0::'a \<Rightarrow> 'b) a'}"
      "(a::'a) \<notin> (A'::'a set)"
      "(f::'a \<Rightarrow> 'b) \<notin> {f::'a \<Rightarrow> 'b. \<forall>aa::'a. if aa \<in> insert (a::'a) (A'::'a set) then f aa \<in> (B::'a \<Rightarrow> 'b set) aa else f aa = (f0::'a \<Rightarrow> 'b) aa} "
    shows False
  using assms supply [[smt_trace=false]] by (smt (cvc5))


experiment
begin

datatype tableau = Stuff
datatype ('i, 'a) mapping = Stuff 'i 'a
type_synonym var = nat
datatype 'a atom = Atom 'a
type_synonym 'i bound_index = "var \<Rightarrow> 'i"
type_synonym ('i,'a) bounds_index = "(var, ('i \<times> 'a))mapping"


datatype ('i,'a) state = State
  (\<T>: "tableau")
  (\<B>\<^sub>i\<^sub>l: "('i,'a) bounds_index")
  (\<B>\<^sub>i\<^sub>u: "('i,'a) bounds_index")
  (\<V>: "(var, 'a) mapping")
  (\<U>: bool)
  (\<U>\<^sub>c: "'i list option")

type_synonym ('i,'a) i_atom = "'i \<times> 'a atom"

type_synonym 'a bounds = "var \<rightharpoonup> 'a"
type_synonym 'a valuation = "var \<Rightarrow> 'a"

datatype ('i,'a) Direction = Direction
  (lt: "'a::linorder \<Rightarrow> 'a \<Rightarrow> bool")
  (LBI: "('i,'a) state \<Rightarrow> ('i,'a) bounds_index")
  (UBI: "('i,'a) state \<Rightarrow> ('i,'a) bounds_index")
  (LB: "('i,'a) state \<Rightarrow> 'a bounds")
  (UB: "('i,'a) state \<Rightarrow> 'a bounds")
  (LI: "('i,'a) state \<Rightarrow> 'i bound_index")
  (UI: "('i,'a) state \<Rightarrow> 'i bound_index")
  (UBI_upd: "(('i,'a) bounds_index \<Rightarrow> ('i,'a) bounds_index) \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state")
  (LE: "var \<Rightarrow> 'a \<Rightarrow> 'a atom")
  (GE: "var \<Rightarrow> 'a \<Rightarrow> 'a atom")
  (le_rat: "rat \<Rightarrow> rat \<Rightarrow> bool")

fun i_satisfies_atom_set :: "'i set \<times> 'a::linorder valuation \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> bool" (infixl \<open>\<Turnstile>\<^sub>i\<^sub>a\<^sub>s\<close> 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as \<longleftrightarrow> undefined"

fun atoms_imply_bounds_index :: "('i,'a) i_atom set \<Rightarrow> ('a bounds \<times> 'a bounds) \<times> ('i bound_index \<times> 'i bound_index)
  \<Rightarrow> bool" (infixl \<open>\<Turnstile>\<^sub>i\<close> 100) where
  "as \<Turnstile>\<^sub>i bi \<longleftrightarrow> undefined"
lemma
  assumes
    " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. lt (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x1"
       "\<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. GE (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x10"
      " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. LBI (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x2"
      " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. UBI (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x3"
      " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. LB (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x4"
      " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. UB (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x5"
       "\<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. LI (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x6"
       "\<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. UI (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x7"
       "\<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. UBI_upd (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x8"
      " \<forall>(x1::'a \<Rightarrow> 'a \<Rightarrow> bool) (x2::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x3::('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping) (x4::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
          (x5::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option) (x6::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) (x7::('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
          (x8::((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state) (x9::nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (x10::nat \<Rightarrow> 'a \<Rightarrow> 'a atom)
          x11::rat \<Rightarrow> rat \<Rightarrow> bool. LE (Direction x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = x9"
       "Negative = Direction (\<lambda>(x::'a) y::'a. y < x) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<I>\<^sub>u \<I>\<^sub>l \<B>\<^sub>i\<^sub>l_update Geq Leq (\<lambda>(x::rat) y::rat. y \<le> x)"
       "Positive = Direction (<) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<I>\<^sub>l \<I>\<^sub>u \<B>\<^sub>i\<^sub>u_update Leq Geq (\<le>)"
      " \<forall>(as::('i \<times> 'a atom) set) (as'::('i \<times> 'a atom) set) bi::((nat \<Rightarrow> 'a option) \<times> (nat \<Rightarrow> 'a option)) \<times> (nat \<Rightarrow> 'i) \<times> (nat \<Rightarrow> 'i).
          as \<subseteq> as' \<and> as \<Turnstile>\<^sub>i bi \<longrightarrow> as' \<Turnstile>\<^sub>i bi"
       "(ats::('i \<times> 'a atom) set) \<subseteq> (A::('i \<times> 'a atom) set)"
      " \<forall>(bs::('i \<times> 'a atom) set) s'::('i, 'a) state.
          bs \<Turnstile>\<^sub>i \<B>\<I> s' =
          (Q::('i \<times> 'a atom) set
              \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)
                 \<Rightarrow> (('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping)
                    \<Rightarrow> (('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping)
                       \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
                          \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
                             \<Rightarrow> (((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state)
                                \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
                                   \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a atom) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a atom) \<Rightarrow> ('i, 'a) state \<Rightarrow> bool)
           bs (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'"
       "\<forall>s'::('i, 'a) state.
          (A::('i \<times> 'a atom) set) \<Turnstile>\<^sub>i \<B>\<I> s' =
          (Q::('i \<times> 'a atom) set
              \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)
                 \<Rightarrow> (('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping)
                    \<Rightarrow> (('i, 'a) state \<Rightarrow> (nat, 'i \<times> 'a) mapping)
                       \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
                          \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'a option)
                             \<Rightarrow> (((nat, 'i \<times> 'a) mapping \<Rightarrow> (nat, 'i \<times> 'a) mapping) \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state)
                                \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i)
                                   \<Rightarrow> (('i, 'a) state \<Rightarrow> nat \<Rightarrow> 'i) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a atom) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a atom) \<Rightarrow> ('i, 'a) state \<Rightarrow> bool)
           A (\<lambda>(x::'a) y::'a. y < x) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
       "\<forall>(I::'i set) v::nat \<Rightarrow> 'a.
          (I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (ats::('i \<times> 'a atom) set) \<longrightarrow>
          (\<forall>(x::nat) c::'a. \<B>\<^sub>l (s::('i, 'a) state) x = Some c \<and> \<I>\<^sub>l s x \<in> I \<longrightarrow> c < v x \<or> c = v x) \<and>
          (\<forall>(x::nat) c::'a. \<B>\<^sub>u s x = Some c \<and> \<I>\<^sub>u s x \<in> I \<longrightarrow> v x < c \<or> v x = c)"
       "\<forall>(I::'i set) v::nat \<Rightarrow> 'a.
          (I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (ats::('i \<times> 'a atom) set) \<longrightarrow>
          (\<forall>(x::nat) c::'a. \<B>\<^sub>u (s::('i, 'a) state) x = Some c \<and> \<I>\<^sub>u s x \<in> I \<longrightarrow> v x < c \<or> c = v x) \<and>
          (\<forall>(x::nat) c::'a. \<B>\<^sub>l s x = Some c \<and> \<I>\<^sub>l s x \<in> I \<longrightarrow> c < v x \<or> v x = c)"
       "\<forall>v::'i set \<times> (nat \<Rightarrow> 'a). v \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (A::('i \<times> 'a atom) set) \<longrightarrow> v \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (ats::('i \<times> 'a atom) set)"
       "\<not> ((dir::('i, 'a) Direction) = Positive \<or> dir = Negative \<longrightarrow>
           (\<forall>(I::'i set) v::nat \<Rightarrow> 'a.
               (I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (A::('i \<times> 'a::linorder atom) set) \<longrightarrow>
               (\<forall>(x::nat) c::'a. LB dir (s::('i, 'a) state) x = Some c \<and> LI dir s x \<in> I \<longrightarrow> lt dir c (v x) \<or> c = v x) \<and>
               (\<forall>(x::nat) c::'a. UB dir s x = Some c \<and> UI dir s x \<in> I \<longrightarrow> lt dir (v x) c \<or> v x = c))) "
     shows False
  using assms supply [[smt_trace=false]] by (smt (cvc5)) 

abbreviation BoundsIndicesMap (\<open>\<B>\<^sub>i\<close>) where  "\<B>\<^sub>i s \<equiv> (\<B>\<^sub>i\<^sub>l s, \<B>\<^sub>i\<^sub>u s)"

lemma
  fixes  normalized_tableau :: "tableau \<Rightarrow> bool" (\<open>\<triangle>\<close>) and
         tableau_valuated :: \<open>_\<close> (\<open>\<nabla>\<close>) and
         bounds_consistent :: "('i,'a::linorder) state \<Rightarrow> bool" (\<open>\<diamond>\<close>) and
         gt_state :: "('i,'a) state \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl \<open>\<succ>\<^sub>x\<close> 100) and
         curr_val_satisfies_no_lhs :: \<open>_\<close> (\<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s\<close>)
  assumes "\<forall>c p. (case p of (x, xa) \<Rightarrow> c x xa) \<and> (\<forall>x y. p = (x, y) \<and> c x y \<longrightarrow> False) \<longrightarrow> False"
          "\<forall>c p. (case p of (x, xa) \<Rightarrow> c x xa) \<and> (\<forall>x y. p = (x, y) \<and> c x y \<longrightarrow> False) \<longrightarrow> False"
          "\<forall>a P. (a \<in> Collect P) = P a"
          "\<forall>a P. (a \<in> Collect P) = P a"
          "\<forall>x1 x2 y1 y2. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)"
          "\<forall>x1 x2 y1 y2. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)"
          "\<forall>x y R. (x, y) \<in> R\<^sup>+ \<longrightarrow> (\<exists>z. (x, z) \<in> R\<^sup>* \<and> (z, y) \<in> R)"
          "\<forall>x y R. (x, y) \<in> R\<^sup>+ \<longrightarrow> (\<exists>z. (x, z) \<in> R\<^sup>* \<and> (z, y) \<in> R)"
          "(s, s') \<in> {(s, s'). \<triangle> (\<T> s) \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<nabla> s \<and> s \<succ>\<^sub>x s' \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s}\<^sup>+"
          "\<forall>s. \<triangle> (\<T> s) \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<nabla> s \<and> s \<succ>\<^sub>x s' \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s \<longrightarrow> \<triangle> (\<T> s')"
          "\<not> \<triangle> (\<T> s')"
  shows False
  using assms by (smt (cvc5, no_ematching) case_prodE mem_Collect_eq prod.inject tranclD2)

end
end
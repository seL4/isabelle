(*  Title:      HOL/SMT_Examples/SMT_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
*)

section {* Examples for the SMT binding *}

theory SMT_Examples
imports Complex_Main
begin

declare [[smt_certificates = "SMT_Examples.certs"]]
declare [[smt_read_only_certificates = true]]


section {* Propositional and first-order logic *}

lemma "True" by smt
lemma "p \<or> \<not>p" by smt
lemma "(p \<and> True) = p" by smt
lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by smt
lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)" by smt
lemma "(p1 \<and> p2) \<or> p3 \<longrightarrow> (p1 \<longrightarrow> (p3 \<and> p2) \<or> (p1 \<and> p3)) \<or> p1" by smt
lemma "P = P = P = P = P = P = P = P = P = P" by smt

lemma
  assumes "a \<or> b \<or> c \<or> d"
      and "e \<or> f \<or> (a \<and> d)"
      and "\<not> (a \<or> (c \<and> ~c)) \<or> b"
      and "\<not> (b \<and> (x \<or> \<not> x)) \<or> c"
      and "\<not> (d \<or> False) \<or> c"
      and "\<not> (c \<or> (\<not> p \<and> (p \<or> (q \<and> \<not> q))))"
  shows False
  using assms by smt

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"

lemma "a = a \<and> symm_f a b = symm_f b a" by (smt symm_f)

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
  using assms by smt

lemma "\<forall>x::int. P x \<longrightarrow> (\<forall>y::int. P x \<or> P y)"
  by smt

lemma
  assumes "(\<forall>x y. P x y = x)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by smt

lemma
  assumes "(\<forall>x y. P x y = x)"
  and "(\<forall>x. \<exists>y. P x y) = (\<forall>x. P x c)"
  shows "(EX y. P x y) = P x c"
  using assms by smt

lemma
  assumes "if P x then \<not>(\<exists>y. P y) else (\<forall>y. \<not>P y)"
  shows "P x \<longrightarrow> P y"
  using assms by smt


section {* Arithmetic *}

subsection {* Linear arithmetic over integers and reals *}

lemma "(3::int) = 3" by smt
lemma "(3::real) = 3" by smt
lemma "(3 :: int) + 1 = 4" by smt
lemma "x + (y + z) = y + (z + (x::int))" by smt
lemma "max (3::int) 8 > 5" by smt
lemma "abs (x :: real) + abs y \<ge> abs (x + y)" by smt
lemma "P ((2::int) < 3) = P True" by smt
lemma "x + 3 \<ge> 4 \<or> x < (1::int)" by smt

lemma
  assumes "x \<ge> (3::int)" and "y = x + 4"
  shows "y - x > 0"
  using assms by smt

lemma "let x = (2 :: int) in x + x \<noteq> 5" by smt

lemma
  fixes x :: real
  assumes "3 * x + 7 * a < 4" and "3 < 2 * x"
  shows "a < 0"
  using assms by smt

lemma "(0 \<le> y + -1 * x \<or> \<not> 0 \<le> x \<or> 0 \<le> (x::int)) = (\<not> False)" by smt

lemma "
  (n < m \<and> m < n') \<or> (n < m \<and> m = n') \<or> (n < n' \<and> n' < m) \<or>
  (n = n' \<and> n' < m) \<or> (n = m \<and> m < n') \<or>
  (n' < m \<and> m < n) \<or> (n' < m \<and> m = n) \<or>
  (n' < n \<and> n < m) \<or> (n' = n \<and> n < m) \<or> (n' = m \<and> m < n) \<or>
  (m < n \<and> n < n') \<or> (m < n \<and> n' = n) \<or> (m < n' \<and> n' < n) \<or>
  (m = n \<and> n < n') \<or> (m = n' \<and> n' < n) \<or>
  (n' = m \<and> m = (n::int))"
  by smt

text{*
The following example was taken from HOL/ex/PresburgerEx.thy, where it says:

  This following theorem proves that all solutions to the
  recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
  period 9.  The example was brought to our attention by John
  Harrison. It does does not require Presburger arithmetic but merely
  quantifier-free linear arithmetic and holds for the rationals as well.

  Warning: it takes (in 2006) over 4.2 minutes!

There, it is proved by "arith". SMT is able to prove this within a fraction
of one second. With proof reconstruction, it takes about 13 seconds on a Core2
processor.
*}

lemma "\<lbrakk> x3 = abs x2 - x1; x4 = abs x3 - x2; x5 = abs x4 - x3;
         x6 = abs x5 - x4; x7 = abs x6 - x5; x8 = abs x7 - x6;
         x9 = abs x8 - x7; x10 = abs x9 - x8; x11 = abs x10 - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 \<and> x2 = (x11::int)"
  by smt


lemma "let P = 2 * x + 1 > x + (x::real) in P \<or> False \<or> P" by smt

lemma "x + (let y = x mod 2 in 2 * y + 1) \<ge> x + (1::int)"
  using [[z3_extensions]] by smt

lemma "x + (let y = x mod 2 in y + y) < x + (3::int)"
  using [[z3_extensions]] by smt

lemma
  assumes "x \<noteq> (0::real)"
  shows "x + x \<noteq> (let P = (abs x > 1) in if P \<or> \<not> P then 4 else 2) * x"
  using assms [[z3_extensions]] by smt

lemma
  assumes "(n + m) mod 2 = 0" and "n mod 4 = 3"
  shows "n mod 2 = 1 \<and> m mod 2 = (1::int)"
  using assms [[z3_extensions]] by smt


subsection {* Linear arithmetic with quantifiers *}

lemma "~ (\<exists>x::int. False)" by smt
lemma "~ (\<exists>x::real. False)" by smt

lemma "\<exists>x::int. 0 < x" by smt

lemma "\<exists>x::real. 0 < x"
  using [[smt_oracle=true]] (* no Z3 proof *)
  by smt

lemma "\<forall>x::int. \<exists>y. y > x" by smt

lemma "\<forall>x y::int. (x = 0 \<and> y = 1) \<longrightarrow> x \<noteq> y" by smt
lemma "\<exists>x::int. \<forall>y. x < y \<longrightarrow> y < 0 \<or> y >= 0" by smt
lemma "\<forall>x y::int. x < y \<longrightarrow> (2 * x + 1) < (2 * y)" by smt
lemma "\<forall>x y::int. (2 * x + 1) \<noteq> (2 * y)" by smt
lemma "\<forall>x y::int. x + y > 2 \<or> x + y = 2 \<or> x + y < 2" by smt
lemma "\<forall>x::int. if x > 0 then x + 1 > 0 else 1 > x" by smt
lemma "if (ALL x::int. x < 0 \<or> x > 0) then False else True" by smt
lemma "(if (ALL x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)" by smt
lemma "~ (\<exists>x y z::int. 4 * x + -6 * y = (1::int))" by smt
lemma "\<exists>x::int. \<forall>x y. 0 < x \<and> 0 < y \<longrightarrow> (0::int) < x + y" by smt
lemma "\<exists>u::int. \<forall>(x::int) y::real. 0 < x \<and> 0 < y \<longrightarrow> -1 < x" by smt
lemma "\<exists>x::int. (\<forall>y. y \<ge> x \<longrightarrow> y > 0) \<longrightarrow> x > 0" by smt
lemma "\<forall>(a::int) b::int. 0 < b \<or> b < 1" by smt


subsection {* Non-linear arithmetic over integers and reals *}

lemma "a > (0::int) \<Longrightarrow> a*b > 0 \<Longrightarrow> b > 0"
  using [[smt_oracle, z3_extensions]]
  by smt

lemma  "(a::int) * (x + 1 + y) = a * x + a * (y + 1)"
  using [[z3_extensions]]
  by smt

lemma "((x::real) * (1 + y) - x * (1 - y)) = (2 * x * y)"
  using [[z3_extensions]]
  by smt

lemma
  "(U::int) + (1 + p) * (b + e) + p * d =
   U + (2 * (1 + p) * (b + e) + (1 + p) * d + d * p) - (1 + p) * (b + d + e)"
  using [[z3_extensions]] by smt

lemma [z3_rule]:
  fixes x :: "int"
  assumes "x * y \<le> 0" and "\<not> y \<le> 0" and "\<not> x \<le> 0"
  shows False
  using assms by (metis mult_le_0_iff)


section {* Pairs *}

lemma "fst (x, y) = a \<Longrightarrow> x = a"
  using fst_conv by smt

lemma "p1 = (x, y) \<and> p2 = (y, x) \<Longrightarrow> fst p1 = snd p2"
  using fst_conv snd_conv by smt


section {* Higher-order problems and recursion *}

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> (f (i1 := v1, i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by smt

lemma "(f g (x::'a::type) = (g x \<and> True)) \<or> (f g x = True) \<or> (g x = True)"
  by smt

lemma "id x = x \<and> id True = True"
  by (smt id_def)

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> ((f (i1 := v1)) (i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by smt

lemma
  "f (\<exists>x. g x) \<Longrightarrow> True"
  "f (\<forall>x. g x) \<Longrightarrow> True"
  by smt+

lemma True using let_rsp by smt
lemma "le = op \<le> \<Longrightarrow> le (3::int) 42" by smt
lemma "map (\<lambda>i::int. i + 1) [0, 1] = [1, 2]" by (smt list.map)
lemma "(ALL x. P x) \<or> ~ All P" by smt

fun dec_10 :: "int \<Rightarrow> int" where
  "dec_10 n = (if n < 10 then n else dec_10 (n - 10))"

lemma "dec_10 (4 * dec_10 4) = 6" by (smt dec_10.simps)

axiomatization
  eval_dioph :: "int list \<Rightarrow> int list \<Rightarrow> int"
where
  eval_dioph_mod: "eval_dioph ks xs mod n = eval_dioph ks (map (\<lambda>x. x mod n) xs) mod n"
and
  eval_dioph_div_mult:
  "eval_dioph ks (map (\<lambda>x. x div n) xs) * n +
   eval_dioph ks (map (\<lambda>x. x mod n) xs) = eval_dioph ks xs"

lemma
  "(eval_dioph ks xs = l) =
   (eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 = l mod 2 \<and>
    eval_dioph ks (map (\<lambda>x. x div 2) xs) = (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2)"
  using [[smt_oracle = true]] (*FIXME*)
  using [[z3_extensions]]
  by (smt eval_dioph_mod[where n=2] eval_dioph_div_mult[where n=2])


context complete_lattice
begin

lemma
  assumes "Sup {a | i::bool. True} \<le> Sup {b | i::bool. True}"
  and "Sup {b | i::bool. True} \<le> Sup {a | i::bool. True}"
  shows "Sup {a | i::bool. True} \<le> Sup {a | i::bool. True}"
  using assms by (smt order_trans)

end


section {* Monomorphization examples *}

definition Pred :: "'a \<Rightarrow> bool" where "Pred x = True"

lemma poly_Pred: "Pred x \<and> (Pred [x] \<or> \<not> Pred [x])" by (simp add: Pred_def)

lemma "Pred (1::int)" by (smt poly_Pred)

axiomatization g :: "'a \<Rightarrow> nat"
axiomatization where
  g1: "g (Some x) = g [x]" and
  g2: "g None = g []" and
  g3: "g xs = length xs"

lemma "g (Some (3::int)) = g (Some True)" by (smt g1 g2 g3 list.size)

end

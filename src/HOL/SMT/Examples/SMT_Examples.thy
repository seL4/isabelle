(*  Title:       SMT_Examples.thy
    Author:      Sascha Boehme, TU Muenchen
*)

header {* Examples for the 'smt' tactic. *}

theory SMT_Examples
imports "../SMT"
begin

declare [[smt_solver=z3, z3_proofs=false]]
declare [[smt_trace=true]] (*FIXME*)


section {* Propositional and first-order logic *}

lemma "True" by smt
lemma "p \<or> \<not>p" by smt
lemma "(p \<and> True) = p" by smt
lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by smt
lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)" by smt
lemma "P=P=P=P=P=P=P=P=P=P" by smt

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"
lemma "a = a \<and> symm_f a b = symm_f b a" by (smt add: symm_f)


section {* Linear arithmetic *}

lemma "(3::int) = 3" by smt
lemma "(3::real) = 3" by smt
lemma "(3 :: int) + 1 = 4" by smt
lemma "max (3::int) 8 > 5" by smt
lemma "abs (x :: real) + abs y \<ge> abs (x + y)" by smt
lemma "let x = (2 :: int) in x + x \<noteq> 5" by smt

text{* 
The following example was taken from HOL/ex/PresburgerEx.thy, where it says:

  This following theorem proves that all solutions to the
  recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
  period 9.  The example was brought to our attention by John
  Harrison. It does does not require Presburger arithmetic but merely
  quantifier-free linear arithmetic and holds for the rationals as well.

  Warning: it takes (in 2006) over 4.2 minutes! 

There, it is proved by "arith". SMT is able to prove this within a fraction
of one second.
*}

lemma "\<lbrakk> x3 = abs x2 - x1; x4 = abs x3 - x2; x5 = abs x4 - x3;
         x6 = abs x5 - x4; x7 = abs x6 - x5; x8 = abs x7 - x6;
         x9 = abs x8 - x7; x10 = abs x9 - x8; x11 = abs x10 - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 & x2 = (x11::int)"
  by smt

lemma "\<exists>x::int. 0 < x" by smt
lemma "\<exists>x::real. 0 < x" by smt
lemma "\<forall>x y::int. x < y \<longrightarrow> (2 * x + 1) < (2 * y)" by smt
lemma "\<forall>x y::int. (2 * x + 1) \<noteq> (2 * y)" by smt
lemma "~ (\<exists>x y z::int. 4 * x + -6 * y = (1::int))" by smt
lemma "~ (\<exists>x::int. False)" by smt


section {* Non-linear arithmetic *}

lemma "((x::int) * (1 + y) - x * (1 - y)) = (2 * x * y)" by smt
lemma
  "(U::int) + (1 + p) * (b + e) + p * d =
   U + (2 * (1 + p) * (b + e) + (1 + p) * d + d * p) - (1 + p) * (b + d + e)"
  by smt


section {* Linear arithmetic for natural numbers *}

lemma "a < 3 \<Longrightarrow> (7::nat) > 2 * a" by smt
lemma "let x = (1::nat) + y in x - y > 0 * x" by smt
lemma
  "let x = (1::nat) + y in
   let P = (if x > 0 then True else False) in
   False \<or> P = (x - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  by smt


section {* Bitvectors *}

locale bv
begin

declare [[smt_solver=z3]]

lemma "(27 :: 4 word) = -5" by smt
lemma "(27 :: 4 word) = 11" by smt
lemma "23 < (27::8 word)" by smt
lemma "27 + 11 = (6::5 word)" by smt
lemma "7 * 3 = (21::8 word)" by smt
lemma "11 - 27 = (-16::8 word)" by smt
lemma "- -11 = (11::5 word)" by smt
lemma "-40 + 1 = (-39::7 word)" by smt
lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by smt

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by smt
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by smt
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by smt
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by smt

lemma "word_cat (27::4 word) (27::8 word) = (2843::12 word)" by smt
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)" 
  by smt

lemma "slice 1 (0b10110 :: 4 word) = (0b11 :: 2 word)" by smt

lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by smt
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by smt

lemma "bv_lshr 0b10011 2 = (0b100::8 word)" by smt
lemma "bv_ashr 0b10011 2 = (0b100::8 word)" by smt

lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by smt
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by smt

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by smt

lemma "w < 256 \<Longrightarrow> (w :: 16 word) AND 0x00FF = w" by smt

end


section {* Pairs *}

lemma "fst (x, y) = a \<Longrightarrow> x = a" by smt
lemma "p1 = (x, y) \<and> p2 = (y, x) \<Longrightarrow> fst p1 = snd p2" by smt


section {* Higher-order problems and recursion *}

lemma "(f g x = (g x \<and> True)) \<or> (f g x = True) \<or> (g x = True)" by smt
lemma "P ((2::int) < 3) = P True" by smt
lemma "P ((2::int) < 3) = (P True :: bool)" by smt
lemma "P (0 \<le> (a :: 4 word)) = P True" using [[smt_solver=z3]] by smt
lemma "id 3 = 3 \<and> id True = True" by (smt add: id_def)
lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> ((f (i1 := v1)) (i2 := v2)) i = f i" by smt
lemma "map (\<lambda>i::nat. i + 1) [0, 1] = [1, 2]" by (smt add: map.simps)
lemma "(ALL x. P x) | ~ All P" by smt

fun dec_10 :: "nat \<Rightarrow> nat" where
  "dec_10 n = (if n < 10 then n else dec_10 (n - 10))"
lemma "dec_10 (4 * dec_10 4) = 6" by (smt add: dec_10.simps)

axiomatization
  eval_dioph :: "int list \<Rightarrow> nat list \<Rightarrow> int"
  where
  eval_dioph_mod:
  "eval_dioph ks xs mod int n = eval_dioph ks (map (\<lambda>x. x mod n) xs) mod int n"
  and
  eval_dioph_div_mult:
  "eval_dioph ks (map (\<lambda>x. x div n) xs) * int n +
   eval_dioph ks (map (\<lambda>x. x mod n) xs) = eval_dioph ks xs"
lemma
  "(eval_dioph ks xs = l) =
   (eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 = l mod 2 \<and>
    eval_dioph ks (map (\<lambda>x. x div 2) xs) =
      (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2)"
  by (smt add: eval_dioph_mod[where n=2] eval_dioph_div_mult[where n=2])


section {* Monomorphization examples *}

definition P :: "'a \<Rightarrow> bool" where "P x = True"
lemma poly_P: "P x \<and> (P [x] \<or> \<not>P[x])" by (simp add: P_def)
lemma "P (1::int)" by (smt add: poly_P)

consts g :: "'a \<Rightarrow> nat"
axioms
  g1: "g (Some x) = g [x]"
  g2: "g None = g []"
  g3: "g xs = length xs"
lemma "g (Some (3::int)) = g (Some True)" by (smt add: g1 g2 g3 list.size)

end

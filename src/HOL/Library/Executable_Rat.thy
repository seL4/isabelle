(*  Title:      HOL/Library/Executable_Rat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Implementation of rational numbers as pairs of integers *}

theory Executable_Rat
imports Abstract_Rat "~~/src/HOL/Real/Rational"
begin

hide (open) const Rat

definition
  Rat :: "int \<times> int \<Rightarrow> rat"
where
  "Rat = INum"

code_datatype Rat

lemma Rat_simp:
  "Rat (k, l) = rat_of_int k / rat_of_int l"
  unfolding Rat_def INum_def by simp

lemma Rat_zero [simp]: "Rat 0\<^sub>N = 0"
  by (simp add: Rat_simp)

lemma Rat_lit [simp]: "Rat i\<^sub>N = rat_of_int i"
  by (simp add: Rat_simp)

lemma zero_rat_code [code]:
  "0 = Rat 0\<^sub>N" by simp

lemma zero_rat_code [code]:
  "1 = Rat 1\<^sub>N" by simp

lemma [code, code unfold]:
  "number_of k = rat_of_int (number_of k)"
  by (simp add: number_of_is_id rat_number_of_def)

definition
  [code func del]: "Fract' (b\<Colon>bool) k l = Fract k l"

lemma [code]:
  "Fract k l = Fract' (l \<noteq> 0) k l"
  unfolding Fract'_def ..

lemma [code]:
  "Fract' True k l = (if l \<noteq> 0 then Rat (k, l) else Fract 1 0)"
  by (simp add: Fract'_def Rat_simp Fract_of_int_quotient [of k l])

lemma [code]:
  "of_rat (Rat (k, l)) = (if l \<noteq> 0 then of_int k / of_int l else 0)"
  by (cases "l = 0")
    (auto simp add: Rat_simp of_rat_rat [simplified Fract_of_int_quotient [of k l], symmetric])

instance rat :: eq ..

lemma rat_eq_code [code]: "Rat x = Rat y \<longleftrightarrow> normNum x = normNum y"
  unfolding Rat_def INum_normNum_iff ..

lemma rat_less_eq_code [code]: "Rat x \<le> Rat y \<longleftrightarrow> normNum x \<le>\<^sub>N normNum y"
proof -
  have "normNum x \<le>\<^sub>N normNum y \<longleftrightarrow> Rat (normNum x) \<le> Rat (normNum y)" 
    by (simp add: Rat_def del: normNum)
  also have "\<dots> = (Rat x \<le> Rat y)" by (simp add: Rat_def)
  finally show ?thesis by simp
qed

lemma rat_less_code [code]: "Rat x < Rat y \<longleftrightarrow> normNum x <\<^sub>N normNum y"
proof -
  have "normNum x <\<^sub>N normNum y \<longleftrightarrow> Rat (normNum x) < Rat (normNum y)" 
    by (simp add: Rat_def del: normNum)
  also have "\<dots> = (Rat x < Rat y)" by (simp add: Rat_def)
  finally show ?thesis by simp
qed

lemma rat_add_code [code]: "Rat x + Rat y = Rat (x +\<^sub>N y)"
  unfolding Rat_def by simp

lemma rat_mul_code [code]: "Rat x * Rat y = Rat (x *\<^sub>N y)"
  unfolding Rat_def by simp

lemma rat_neg_code [code]: "- Rat x = Rat (~\<^sub>N x)"
  unfolding Rat_def by simp

lemma rat_sub_code [code]: "Rat x - Rat y = Rat (x -\<^sub>N y)"
  unfolding Rat_def by simp

lemma rat_inv_code [code]: "inverse (Rat x) = Rat (Ninv x)"
  unfolding Rat_def Ninv divide_rat_def by simp

lemma rat_div_code [code]: "Rat x / Rat y = Rat (x \<div>\<^sub>N y)"
  unfolding Rat_def by simp

code_modulename SML
  Rational Rational
  Executable_Rat Rational

code_modulename OCaml
  Rational Rational
  Executable_Rat Rational

code_modulename Haskell
  Rational Rational
  Executable_Rat Rational

end

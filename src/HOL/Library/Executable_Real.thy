(*  Title:      HOL/Library/Executable_Real.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Implementation of rational real numbers as pairs of integers *}

theory Executable_Real
imports Abstract_Rat "~~/src/HOL/Real/Real"
begin

hide (open) const Real

definition
  Real :: "int \<times> int \<Rightarrow> real"
where
  "Real = INum"

code_datatype Real

lemma Real_simp:
  "Real (k, l) = real_of_int k / real_of_int l"
  unfolding Real_def INum_def by simp

lemma Real_zero [simp]: "Real 0\<^sub>N = 0"
  by (simp add: Real_simp)

lemma Real_lit [simp]: "Real i\<^sub>N = real_of_int i"
  by (simp add: Real_simp)

lemma zero_real_code [code]:
  "0 = Real 0\<^sub>N" by simp

lemma zero_real_code [code]:
  "1 = Real 1\<^sub>N" by simp

lemma [code, code unfold]:
  "number_of k = real_of_int (number_of k)"
  by (simp add: number_of_is_id real_number_of_def)

instance real :: eq ..

lemma real_eq_code [code]: "Real x = Real y \<longleftrightarrow> normNum x = normNum y"
  unfolding Real_def INum_normNum_iff ..

lemma real_less_eq_code [code]: "Real x \<le> Real y \<longleftrightarrow> normNum x \<le>\<^sub>N normNum y"
proof -
  have "normNum x \<le>\<^sub>N normNum y \<longleftrightarrow> Real (normNum x) \<le> Real (normNum y)" 
    by (simp add: Real_def del: normNum)
  also have "\<dots> = (Real x \<le> Real y)" by (simp add: Real_def)
  finally show ?thesis by simp
qed

lemma real_less_code [code]: "Real x < Real y \<longleftrightarrow> normNum x <\<^sub>N normNum y"
proof -
  have "normNum x <\<^sub>N normNum y \<longleftrightarrow> Real (normNum x) < Real (normNum y)" 
    by (simp add: Real_def del: normNum)
  also have "\<dots> = (Real x < Real y)" by (simp add: Real_def)
  finally show ?thesis by simp
qed

lemma real_add_code [code]: "Real x + Real y = Real (x +\<^sub>N y)"
  unfolding Real_def by simp

lemma real_mul_code [code]: "Real x * Real y = Real (x *\<^sub>N y)"
  unfolding Real_def by simp

lemma real_neg_code [code]: "- Real x = Real (~\<^sub>N x)"
  unfolding Real_def by simp

lemma real_sub_code [code]: "Real x - Real y = Real (x -\<^sub>N y)"
  unfolding Real_def by simp

lemma real_inv_code [code]: "inverse (Real x) = Real (Ninv x)"
  unfolding Real_def Ninv real_divide_def by simp

lemma real_div_code [code]: "Real x / Real y = Real (x \<div>\<^sub>N y)"
  unfolding Real_def by simp

code_modulename SML
  RealDef Real
  Executable_Real Real

code_modulename OCaml
  RealDef Real
  Executable_Real Real

code_modulename Haskell
  RealDef Real
  Executable_Real Real

end

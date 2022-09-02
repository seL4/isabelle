(*  Title:      HOL/Library/Char_ord.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

section \<open>Order on characters\<close>

theory Char_ord
  imports Main
begin

instantiation char :: linorder
begin

definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close>
  where \<open>c1 \<le> c2 \<longleftrightarrow> of_char c1 \<le> (of_char c2 :: nat)\<close>

definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close>
  where \<open>c1 < c2 \<longleftrightarrow> of_char c1 < (of_char c2 :: nat)\<close>


instance
  by standard (auto simp add: less_eq_char_def less_char_def)

end

lemma less_eq_char_simp [simp, code]:
  \<open>Char b0 b1 b2 b3 b4 b5 b6 b7 \<le> Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> lexordp_eq [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0]\<close>
  by (simp only: less_eq_char_def of_char_def char.sel horner_sum_less_eq_iff_lexordp_eq list.size) simp

lemma less_char_simp [simp, code]:
  \<open>Char b0 b1 b2 b3 b4 b5 b6 b7 < Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> ord_class.lexordp [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0]\<close>
  by (simp only: less_char_def of_char_def char.sel horner_sum_less_iff_lexordp list.size) simp

instantiation char :: distrib_lattice
begin

definition \<open>(inf :: char \<Rightarrow> _) = min\<close>
definition \<open>(sup :: char \<Rightarrow> _) = max\<close>

instance
  by standard (auto simp add: inf_char_def sup_char_def max_min_distrib2)

end

code_identifier
  code_module Char_ord \<rightharpoonup>
    (SML) Str and (OCaml) Str and (Haskell) Str and (Scala) Str

end

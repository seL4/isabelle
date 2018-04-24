(*  Title:      HOL/Library/Char_ord.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

section \<open>Order on characters\<close>

theory Char_ord
  imports Main
begin

instantiation char :: linorder
begin

definition less_eq_char :: "char \<Rightarrow> char \<Rightarrow> bool"
  where "c1 \<le> c2 \<longleftrightarrow> of_char c1 \<le> (of_char c2 :: nat)"

definition less_char :: "char \<Rightarrow> char \<Rightarrow> bool"
  where "c1 < c2 \<longleftrightarrow> of_char c1 < (of_char c2 :: nat)"


instance
  by standard (auto simp add: less_eq_char_def less_char_def)

end

lemma less_eq_char_simp [simp]:
  "Char b0 b1 b2 b3 b4 b5 b6 b7 \<le> Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> foldr (\<lambda>b k. of_bool b + k * 2) [b0, b1, b2, b3, b4, b5, b6, b7] 0
      \<le> foldr (\<lambda>b k. of_bool b + k * 2) [c0, c1, c2, c3, c4, c5, c6, c7] (0::nat)"
  by (simp add: less_eq_char_def)

lemma less_char_simp [simp]:
  "Char b0 b1 b2 b3 b4 b5 b6 b7 < Char c0 c1 c2 c3 c4 c5 c6 c7
    \<longleftrightarrow> foldr (\<lambda>b k. of_bool b + k * 2) [b0, b1, b2, b3, b4, b5, b6, b7] 0
      < foldr (\<lambda>b k. of_bool b + k * 2) [c0, c1, c2, c3, c4, c5, c6, c7] (0::nat)"
  by (simp add: less_char_def)

instantiation char :: distrib_lattice
begin

definition "(inf :: char \<Rightarrow> _) = min"
definition "(sup :: char \<Rightarrow> _) = max"

instance
  by standard (auto simp add: inf_char_def sup_char_def max_min_distrib2)

end

end

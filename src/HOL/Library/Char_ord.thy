(*  Title:      HOL/Library/Char_ord.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

section \<open>Order on characters\<close>

theory Char_ord
  imports Main
begin

instantiation char :: linorder
begin

definition "c1 \<le> c2 \<longleftrightarrow> nat_of_char c1 \<le> nat_of_char c2"
definition "c1 < c2 \<longleftrightarrow> nat_of_char c1 < nat_of_char c2"

instance
  by standard (auto simp add: less_eq_char_def less_char_def)

end

lemma less_eq_char_simps:
  "0 \<le> c"
  "Char k \<le> 0 \<longleftrightarrow> numeral k mod 256 = (0 :: nat)"
  "Char k \<le> Char l \<longleftrightarrow> numeral k mod 256 \<le> (numeral l mod 256 :: nat)"
  for c :: char
  by (simp_all add: Char_def less_eq_char_def)

lemma less_char_simps:
  "\<not> c < 0"
  "0 < Char k \<longleftrightarrow> (0 :: nat) < numeral k mod 256"
  "Char k < Char l \<longleftrightarrow> numeral k mod 256 < (numeral l mod 256 :: nat)"
  for c :: char
  by (simp_all add: Char_def less_char_def)

instantiation char :: distrib_lattice
begin

definition "(inf :: char \<Rightarrow> _) = min"
definition "(sup :: char \<Rightarrow> _) = max"

instance
  by standard (auto simp add: inf_char_def sup_char_def max_min_distrib2)

end

instantiation String.literal :: linorder
begin

context includes literal.lifting
begin

lift_definition less_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
  is "ord.lexordp (<)" .

lift_definition less_eq_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
  is "ord.lexordp_eq (<)" .

instance
proof -
  interpret linorder "ord.lexordp_eq (<)" "ord.lexordp (<) :: string \<Rightarrow> string \<Rightarrow> bool"
    by (rule linorder.lexordp_linorder[where less_eq="(\<le>)"]) unfold_locales
  show "PROP ?thesis"
    by intro_classes (transfer, simp add: less_le_not_le linear)+
qed

end

end

lemma less_literal_code [code]:
  "(<) = (\<lambda>xs ys. ord.lexordp (<) (String.explode xs) (String.explode ys))"
  by (simp add: less_literal.rep_eq fun_eq_iff)

lemma less_eq_literal_code [code]:
  "(\<le>) = (\<lambda>xs ys. ord.lexordp_eq (<) (String.explode xs) (String.explode ys))"
  by (simp add: less_eq_literal.rep_eq fun_eq_iff)

lifting_update literal.lifting
lifting_forget literal.lifting

end

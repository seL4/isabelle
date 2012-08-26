(*  Title:      HOL/Library/Char_ord.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

header {* Order on characters *}

theory Char_ord
imports Char_nat
begin

instantiation nibble :: linorder
begin

definition
  nibble_less_eq_def: "n \<le> m \<longleftrightarrow> nat_of_nibble n \<le> nat_of_nibble m"

definition
  nibble_less_def: "n < m \<longleftrightarrow> nat_of_nibble n < nat_of_nibble m"

instance proof
  fix n :: nibble
  show "n \<le> n" unfolding nibble_less_eq_def nibble_less_def by auto
next
  fix n m q :: nibble
  assume "n \<le> m"
    and "m \<le> q"
  then show "n \<le> q" unfolding nibble_less_eq_def nibble_less_def by auto
next
  fix n m :: nibble
  assume "n \<le> m"
    and "m \<le> n"
  then show "n = m"
    unfolding nibble_less_eq_def nibble_less_def
    by (auto simp add: nat_of_nibble_eq)
next
  fix n m :: nibble
  show "n < m \<longleftrightarrow> n \<le> m \<and> \<not> m \<le> n"
    unfolding nibble_less_eq_def nibble_less_def less_le
    by (auto simp add: nat_of_nibble_eq)
next
  fix n m :: nibble
  show "n \<le> m \<or> m \<le> n"
    unfolding nibble_less_eq_def by auto
qed

end

instantiation nibble :: distrib_lattice
begin

definition
  "(inf \<Colon> nibble \<Rightarrow> _) = min"

definition
  "(sup \<Colon> nibble \<Rightarrow> _) = max"

instance by default (auto simp add:
    inf_nibble_def sup_nibble_def min_max.sup_inf_distrib1)

end

instantiation char :: linorder
begin

definition
  char_less_eq_def: "c1 \<le> c2 \<longleftrightarrow> (case c1 of Char n1 m1 \<Rightarrow> case c2 of Char n2 m2 \<Rightarrow>
    n1 < n2 \<or> n1 = n2 \<and> m1 \<le> m2)"

definition
  char_less_def: "c1 < c2 \<longleftrightarrow> (case c1 of Char n1 m1 \<Rightarrow> case c2 of Char n2 m2 \<Rightarrow>
    n1 < n2 \<or> n1 = n2 \<and> m1 < m2)"

instance
  by default (auto simp: char_less_eq_def char_less_def split: char.splits)

end

instantiation char :: distrib_lattice
begin

definition
  "(inf \<Colon> char \<Rightarrow> _) = min"

definition
  "(sup \<Colon> char \<Rightarrow> _) = max"

instance   by default (auto simp add:
    inf_char_def sup_char_def min_max.sup_inf_distrib1)

end

lemma [simp, code]:
  shows char_less_eq_simp: "Char n1 m1 \<le> Char n2 m2 \<longleftrightarrow> n1 < n2 \<or> n1 = n2 \<and> m1 \<le> m2"
  and char_less_simp:      "Char n1 m1 < Char n2 m2 \<longleftrightarrow> n1 < n2 \<or> n1 = n2 \<and> m1 < m2"
  unfolding char_less_eq_def char_less_def by simp_all

end

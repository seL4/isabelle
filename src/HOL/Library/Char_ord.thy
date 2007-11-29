(*  Title:      HOL/Library/Char_ord.thy
    ID:         $Id$
    Author:     Norbert Voelker, Florian Haftmann
*)

header {* Order on characters *}

theory Char_ord
imports Product_ord Char_nat
begin

instance nibble :: linorder
  nibble_less_eq_def: "n \<le> m \<equiv> nat_of_nibble n \<le> nat_of_nibble m"
  nibble_less_def: "n < m \<equiv> nat_of_nibble n < nat_of_nibble m"
proof
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
  show "n < m \<longleftrightarrow> n \<le> m \<and> n \<noteq> m"
    unfolding nibble_less_eq_def nibble_less_def less_le
    by (auto simp add: nat_of_nibble_eq)
next
  fix n m :: nibble
  show "n \<le> m \<or> m \<le> n"
    unfolding nibble_less_eq_def by auto
qed

instance nibble :: distrib_lattice
  "(inf \<Colon> nibble \<Rightarrow> _) = min"
  "(sup \<Colon> nibble \<Rightarrow> _) = max"
  by default (auto simp add:
    inf_nibble_def sup_nibble_def min_max.sup_inf_distrib1)

instance char :: linorder
  char_less_eq_def: "c1 \<le> c2 \<equiv> case c1 of Char n1 m1 \<Rightarrow> case c2 of Char n2 m2 \<Rightarrow>
    n1 < n2 \<or> n1 = n2 \<and> m1 \<le> m2"
  char_less_def:    "c1 < c2 \<equiv> case c1 of Char n1 m1 \<Rightarrow> case c2 of Char n2 m2 \<Rightarrow>
    n1 < n2 \<or> n1 = n2 \<and> m1 < m2"
  by default (auto simp: char_less_eq_def char_less_def split: char.splits)

lemmas [code func del] = char_less_eq_def char_less_def

instance char :: distrib_lattice
  "(inf \<Colon> char \<Rightarrow> _) = min"
  "(sup \<Colon> char \<Rightarrow> _) = max"
  by default (auto simp add:
    inf_char_def sup_char_def min_max.sup_inf_distrib1)

lemma [simp, code func]:
  shows char_less_eq_simp: "Char n1 m1 \<le> Char n2 m2 \<longleftrightarrow> n1 < n2 \<or> n1 = n2 \<and> m1 \<le> m2"
  and char_less_simp:      "Char n1 m1 < Char n2 m2 \<longleftrightarrow> n1 < n2 \<or> n1 = n2 \<and> m1 < m2"
  unfolding char_less_eq_def char_less_def by simp_all

end

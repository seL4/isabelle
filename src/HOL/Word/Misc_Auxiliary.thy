(*  Title:      HOL/Word/Misc_Auxiliary.thy
    Author:     Jeremy Dawson, NICTA
*)

section \<open>Generic auxiliary\<close>

theory Misc_Auxiliary
  imports Main
begin

subsection \<open>Lemmas on list operations\<close>

lemma butlast_power: "(butlast ^^ n) bl = take (length bl - n) bl"
  by (induct n) (auto simp: butlast_take)

lemma nth_rev: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
  using rev_nth by simp

lemma nth_rev_alt: "n < length ys \<Longrightarrow> ys ! n = rev ys ! (length ys - Suc n)"
  by (simp add: nth_rev)

lemma hd_butlast: "length xs > 1 \<Longrightarrow> hd (butlast xs) = hd xs"
  by (cases xs) auto

end

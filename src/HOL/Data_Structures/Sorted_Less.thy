(* Author: Tobias Nipkow *)

section {* Lists Sorted wrt $<$ *}

theory Sorted_Less
imports Less_False
begin

hide_const sorted

text \<open>Is a list sorted without duplicates, i.e., wrt @{text"<"}?
Could go into theory List under a name like @{term sorted_less}.\<close>

fun sorted :: "'a::linorder list \<Rightarrow> bool" where
"sorted [] = True" |
"sorted [x] = True" |
"sorted (x#y#zs) = (x < y \<and> sorted(y#zs))"

lemma sorted_Cons_iff:
  "sorted(x # xs) = (sorted xs \<and> (\<forall>y \<in> set xs. x < y))"
by(induction xs rule: sorted.induct) auto

lemma sorted_snoc_iff:
  "sorted(xs @ [x]) = (sorted xs \<and> (\<forall>y \<in> set xs. y < x))"
by(induction xs rule: sorted.induct) auto

lemma sorted_cons: "sorted (x#xs) \<Longrightarrow> sorted xs"
by(simp add: sorted_Cons_iff)

lemma sorted_cons': "ASSUMPTION (sorted (x#xs)) \<Longrightarrow> sorted xs"
by(rule ASSUMPTION_D [THEN sorted_cons])

lemma sorted_snoc: "sorted (xs @ [y]) \<Longrightarrow> sorted xs"
by(simp add: sorted_snoc_iff)

lemma sorted_snoc': "ASSUMPTION (sorted (xs @ [y])) \<Longrightarrow> sorted xs"
by(rule ASSUMPTION_D [THEN sorted_snoc])

lemma sorted_mid_iff:
  "sorted(xs @ y # ys) = (sorted(xs @ [y]) \<and> sorted(y # ys))"
by(induction xs rule: sorted.induct) auto

lemma sorted_mid_iff2:
  "sorted(x # xs @ y # ys) =
  (sorted(x # xs) \<and> x < y \<and> sorted(xs @ [y]) \<and> sorted(y # ys))"
by(induction xs rule: sorted.induct) auto

lemma sorted_mid_iff': "NO_MATCH [] ys \<Longrightarrow>
  sorted(xs @ y # ys) = (sorted(xs @ [y]) \<and> sorted(y # ys))"
by(rule sorted_mid_iff)

lemmas sorted_lems = sorted_mid_iff' sorted_mid_iff2 sorted_cons' sorted_snoc'

end

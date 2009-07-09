(*  Title:      FOL/ex/Natural_Numbers.thy
    Author:     Markus Wenzel, TU Munich
*)

header {* Natural numbers *}

theory Natural_Numbers
imports FOL
begin

text {*
  Theory of the natural numbers: Peano's axioms, primitive recursion.
  (Modernized version of Larry Paulson's theory "Nat".)  \medskip
*}

typedecl nat
arities nat :: "term"

axiomatization
  Zero :: nat    ("0") and
  Suc :: "nat => nat" and
  rec :: "[nat, 'a, [nat, 'a] => 'a] => 'a"
where
  induct [case_names 0 Suc, induct type: nat]:
    "P(0) ==> (!!x. P(x) ==> P(Suc(x))) ==> P(n)" and
  Suc_inject: "Suc(m) = Suc(n) ==> m = n" and
  Suc_neq_0: "Suc(m) = 0 ==> R" and
  rec_0: "rec(0, a, f) = a" and
  rec_Suc: "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

lemma Suc_n_not_n: "Suc(k) \<noteq> k"
proof (induct k)
  show "Suc(0) \<noteq> 0"
  proof
    assume "Suc(0) = 0"
    then show False by (rule Suc_neq_0)
  qed
next
  fix n assume hyp: "Suc(n) \<noteq> n"
  show "Suc(Suc(n)) \<noteq> Suc(n)"
  proof
    assume "Suc(Suc(n)) = Suc(n)"
    then have "Suc(n) = n" by (rule Suc_inject)
    with hyp show False by contradiction
  qed
qed


definition
  add :: "[nat, nat] => nat"    (infixl "+" 60) where
  "m + n = rec(m, n, \<lambda>x y. Suc(y))"

lemma add_0 [simp]: "0 + n = n"
  unfolding add_def by (rule rec_0)

lemma add_Suc [simp]: "Suc(m) + n = Suc(m + n)"
  unfolding add_def by (rule rec_Suc)

lemma add_assoc: "(k + m) + n = k + (m + n)"
  by (induct k) simp_all

lemma add_0_right: "m + 0 = m"
  by (induct m) simp_all

lemma add_Suc_right: "m + Suc(n) = Suc(m + n)"
  by (induct m) simp_all

lemma
  assumes "!!n. f(Suc(n)) = Suc(f(n))"
  shows "f(i + j) = i + f(j)"
  using assms by (induct i) simp_all

end

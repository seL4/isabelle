(*  Title:      FOL/ex/Natural_Numbers.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Munich
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Natural numbers *}

theory Natural_Numbers = FOL:

text {*
  Theory of the natural numbers: Peano's axioms, primitive recursion.
  (Modernized version of Larry Paulson's theory "Nat".)  \medskip
*}

typedecl nat
arities nat :: "term"

consts
  Zero :: nat    ("0")
  Suc :: "nat => nat"
  rec :: "[nat, 'a, [nat, 'a] => 'a] => 'a"

axioms
  induct [case_names 0 Suc, induct type: nat]:
    "P(0) ==> (!!x. P(x) ==> P(Suc(x))) ==> P(n)"
  Suc_inject: "Suc(m) = Suc(n) ==> m = n"
  Suc_neq_0: "Suc(m) = 0 ==> R"
  rec_0: "rec(0, a, f) = a"
  rec_Suc: "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

lemma Suc_n_not_n: "Suc(k) \<noteq> k"
proof (induct k)
  show "Suc(0) \<noteq> 0"
  proof
    assume "Suc(0) = 0"
    thus False by (rule Suc_neq_0)
  qed
  fix n assume hyp: "Suc(n) \<noteq> n"
  show "Suc(Suc(n)) \<noteq> Suc(n)"
  proof
    assume "Suc(Suc(n)) = Suc(n)"
    hence "Suc(n) = n" by (rule Suc_inject)
    with hyp show False by contradiction
  qed
qed


constdefs
  add :: "[nat, nat] => nat"    (infixl "+" 60)
  "m + n == rec(m, n, \<lambda>x y. Suc(y))"

lemma add_0 [simp]: "0 + n = n"
  by (unfold add_def) (rule rec_0)

lemma add_Suc [simp]: "Suc(m) + n = Suc(m + n)"
  by (unfold add_def) (rule rec_Suc)

lemma add_assoc: "(k + m) + n = k + (m + n)"
  by (induct k) simp_all

lemma add_0_right: "m + 0 = m"
  by (induct m) simp_all

lemma add_Suc_right: "m + Suc(n) = Suc(m + n)"
  by (induct m) simp_all

lemma "(!!n. f(Suc(n)) = Suc(f(n))) ==> f(i + j) = i + f(j)"
proof -
  assume "!!n. f(Suc(n)) = Suc(f(n))"
  thus ?thesis by (induct i) simp_all
qed

end

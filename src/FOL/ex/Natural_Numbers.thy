(*  Title:      FOL/ex/Natural_Numbers.thy
    Author:     Markus Wenzel, TU Munich
*)

section \<open>Natural numbers\<close>

theory Natural_Numbers
imports FOL
begin

text \<open>
  Theory of the natural numbers: Peano's axioms, primitive recursion.
  (Modernized version of Larry Paulson's theory "Nat".)  \medskip
\<close>

typedecl nat
instance nat :: \<open>term\<close> ..

axiomatization
  Zero :: \<open>nat\<close>    (\<open>0\<close>) and
  Suc :: \<open>nat => nat\<close> and
  rec :: \<open>[nat, 'a, [nat, 'a] => 'a] => 'a\<close>
where
  induct [case_names 0 Suc, induct type: nat]:
    \<open>P(0) ==> (!!x. P(x) ==> P(Suc(x))) ==> P(n)\<close> and
  Suc_inject: \<open>Suc(m) = Suc(n) ==> m = n\<close> and
  Suc_neq_0: \<open>Suc(m) = 0 ==> R\<close> and
  rec_0: \<open>rec(0, a, f) = a\<close> and
  rec_Suc: \<open>rec(Suc(m), a, f) = f(m, rec(m, a, f))\<close>

lemma Suc_n_not_n: \<open>Suc(k) \<noteq> k\<close>
proof (induct \<open>k\<close>)
  show \<open>Suc(0) \<noteq> 0\<close>
  proof
    assume \<open>Suc(0) = 0\<close>
    then show \<open>False\<close> by (rule Suc_neq_0)
  qed
next
  fix n assume hyp: \<open>Suc(n) \<noteq> n\<close>
  show \<open>Suc(Suc(n)) \<noteq> Suc(n)\<close>
  proof
    assume \<open>Suc(Suc(n)) = Suc(n)\<close>
    then have \<open>Suc(n) = n\<close> by (rule Suc_inject)
    with hyp show \<open>False\<close> by contradiction
  qed
qed


definition add :: \<open>nat => nat => nat\<close>    (infixl \<open>+\<close> 60)
  where \<open>m + n = rec(m, n, \<lambda>x y. Suc(y))\<close>

lemma add_0 [simp]: \<open>0 + n = n\<close>
  unfolding add_def by (rule rec_0)

lemma add_Suc [simp]: \<open>Suc(m) + n = Suc(m + n)\<close>
  unfolding add_def by (rule rec_Suc)

lemma add_assoc: \<open>(k + m) + n = k + (m + n)\<close>
  by (induct \<open>k\<close>) simp_all

lemma add_0_right: \<open>m + 0 = m\<close>
  by (induct \<open>m\<close>) simp_all

lemma add_Suc_right: \<open>m + Suc(n) = Suc(m + n)\<close>
  by (induct \<open>m\<close>) simp_all

lemma
  assumes \<open>!!n. f(Suc(n)) = Suc(f(n))\<close>
  shows \<open>f(i + j) = i + f(j)\<close>
  using assms by (induct \<open>i\<close>) simp_all

end

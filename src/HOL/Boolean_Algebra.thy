(*  Title:      HOL/Boolean_Algebra.thy
    Author:     Brian Huffman
*)

section \<open>Abstract boolean Algebras\<close>

theory Boolean_Algebra
  imports Lattices
begin

locale boolean_algebra = conj: abel_semigroup "(\<^bold>\<sqinter>)" + disj: abel_semigroup "(\<^bold>\<squnion>)"
  for conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>\<sqinter>" 70)
    and disj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>\<squnion>" 65) +
  fixes compl :: "'a \<Rightarrow> 'a"  ("\<^bold>- _" [81] 80)
    and zero :: "'a"  ("\<^bold>0")
    and one  :: "'a"  ("\<^bold>1")
  assumes conj_disj_distrib: "x \<^bold>\<sqinter> (y \<^bold>\<squnion> z) = (x \<^bold>\<sqinter> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z)"
    and disj_conj_distrib: "x \<^bold>\<squnion> (y \<^bold>\<sqinter> z) = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (x \<^bold>\<squnion> z)"
    and conj_one_right: "x \<^bold>\<sqinter> \<^bold>1 = x"
    and disj_zero_right: "x \<^bold>\<squnion> \<^bold>0 = x"
    and conj_cancel_right [simp]: "x \<^bold>\<sqinter> \<^bold>- x = \<^bold>0"
    and disj_cancel_right [simp]: "x \<^bold>\<squnion> \<^bold>- x = \<^bold>1"
begin

sublocale conj: semilattice_neutr "(\<^bold>\<sqinter>)" "\<^bold>1"
proof
  show "x \<^bold>\<sqinter> \<^bold>1 = x" for x
    by (fact conj_one_right)
  show "x \<^bold>\<sqinter> x = x" for x
  proof -
    have "x \<^bold>\<sqinter> x = (x \<^bold>\<sqinter> x) \<^bold>\<squnion> \<^bold>0"
      by (simp add: disj_zero_right)
    also have "\<dots> = (x \<^bold>\<sqinter> x) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- x)"
      by simp
    also have "\<dots> = x \<^bold>\<sqinter> (x \<^bold>\<squnion> \<^bold>- x)"
      by (simp only: conj_disj_distrib)
    also have "\<dots> = x \<^bold>\<sqinter> \<^bold>1"
      by simp
    also have "\<dots> = x"
      by (simp add: conj_one_right)
    finally show ?thesis .
  qed
qed

sublocale disj: semilattice_neutr "(\<^bold>\<squnion>)" "\<^bold>0"
proof
  show "x \<^bold>\<squnion> \<^bold>0 = x" for x
    by (fact disj_zero_right)
  show "x \<^bold>\<squnion> x = x" for x
  proof -
    have "x \<^bold>\<squnion> x = (x \<^bold>\<squnion> x) \<^bold>\<sqinter> \<^bold>1"
      by simp
    also have "\<dots> = (x \<^bold>\<squnion> x) \<^bold>\<sqinter> (x \<^bold>\<squnion> \<^bold>- x)"
      by simp
    also have "\<dots> = x \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- x)"
      by (simp only: disj_conj_distrib)
    also have "\<dots> = x \<^bold>\<squnion> \<^bold>0"
      by simp
    also have "\<dots> = x"
      by (simp add: disj_zero_right)
    finally show ?thesis .
  qed
qed


subsection \<open>Complement\<close>

lemma complement_unique:
  assumes 1: "a \<^bold>\<sqinter> x = \<^bold>0"
  assumes 2: "a \<^bold>\<squnion> x = \<^bold>1"
  assumes 3: "a \<^bold>\<sqinter> y = \<^bold>0"
  assumes 4: "a \<^bold>\<squnion> y = \<^bold>1"
  shows "x = y"
proof -
  from 1 3 have "(a \<^bold>\<sqinter> x) \<^bold>\<squnion> (x \<^bold>\<sqinter> y) = (a \<^bold>\<sqinter> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> y)"
    by simp
  then have "(x \<^bold>\<sqinter> a) \<^bold>\<squnion> (x \<^bold>\<sqinter> y) = (y \<^bold>\<sqinter> a) \<^bold>\<squnion> (y \<^bold>\<sqinter> x)"
    by (simp add: ac_simps)
  then have "x \<^bold>\<sqinter> (a \<^bold>\<squnion> y) = y \<^bold>\<sqinter> (a \<^bold>\<squnion> x)"
    by (simp add: conj_disj_distrib)
  with 2 4 have "x \<^bold>\<sqinter> \<^bold>1 = y \<^bold>\<sqinter> \<^bold>1"
    by simp
  then show "x = y"
    by simp
qed

lemma compl_unique: "x \<^bold>\<sqinter> y = \<^bold>0 \<Longrightarrow> x \<^bold>\<squnion> y = \<^bold>1 \<Longrightarrow> \<^bold>- x = y"
  by (rule complement_unique [OF conj_cancel_right disj_cancel_right])

lemma double_compl [simp]: "\<^bold>- (\<^bold>- x) = x"
proof (rule compl_unique)
  show "\<^bold>- x \<^bold>\<sqinter> x = \<^bold>0"
    by (simp only: conj_cancel_right conj.commute)
  show "\<^bold>- x \<^bold>\<squnion> x = \<^bold>1"
    by (simp only: disj_cancel_right disj.commute)
qed

lemma compl_eq_compl_iff [simp]: 
  \<open>\<^bold>- x = \<^bold>- y \<longleftrightarrow> x = y\<close>  (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume \<open>?Q\<close>
  then show ?P by simp
next
  assume \<open>?P\<close>
  then have \<open>\<^bold>- (\<^bold>- x) = \<^bold>- (\<^bold>- y)\<close>
    by simp
  then show ?Q
    by simp
qed


subsection \<open>Conjunction\<close>

lemma conj_zero_right [simp]: "x \<^bold>\<sqinter> \<^bold>0 = \<^bold>0"
  using conj.left_idem conj_cancel_right by fastforce

lemma compl_one [simp]: "\<^bold>- \<^bold>1 = \<^bold>0"
  by (rule compl_unique [OF conj_zero_right disj_zero_right])

lemma conj_zero_left [simp]: "\<^bold>0 \<^bold>\<sqinter> x = \<^bold>0"
  by (subst conj.commute) (rule conj_zero_right)

lemma conj_cancel_left [simp]: "\<^bold>- x \<^bold>\<sqinter> x = \<^bold>0"
  by (subst conj.commute) (rule conj_cancel_right)

lemma conj_disj_distrib2: "(y \<^bold>\<squnion> z) \<^bold>\<sqinter> x = (y \<^bold>\<sqinter> x) \<^bold>\<squnion> (z \<^bold>\<sqinter> x)"
  by (simp only: conj.commute conj_disj_distrib)

lemmas conj_disj_distribs = conj_disj_distrib conj_disj_distrib2

lemma conj_assoc: "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> z = x \<^bold>\<sqinter> (y \<^bold>\<sqinter> z)"
  by (fact ac_simps)

lemma conj_commute: "x \<^bold>\<sqinter> y = y \<^bold>\<sqinter> x"
  by (fact ac_simps)

lemmas conj_left_commute = conj.left_commute
lemmas conj_ac = conj.assoc conj.commute conj.left_commute

lemma conj_one_left: "\<^bold>1 \<^bold>\<sqinter> x = x"
  by (fact conj.left_neutral)

lemma conj_left_absorb: "x \<^bold>\<sqinter> (x \<^bold>\<sqinter> y) = x \<^bold>\<sqinter> y"
  by (fact conj.left_idem)

lemma conj_absorb: "x \<^bold>\<sqinter> x = x"
  by (fact conj.idem)


subsection \<open>Disjunction\<close>

interpretation dual: boolean_algebra "(\<^bold>\<squnion>)" "(\<^bold>\<sqinter>)" compl \<open>\<^bold>1\<close> \<open>\<^bold>0\<close>
  apply standard
       apply (rule disj_conj_distrib)
      apply (rule conj_disj_distrib)
     apply simp_all
  done

lemma compl_zero [simp]: "\<^bold>- \<^bold>0 = \<^bold>1"
  by (fact dual.compl_one)

lemma disj_one_right [simp]: "x \<^bold>\<squnion> \<^bold>1 = \<^bold>1"
  by (fact dual.conj_zero_right)

lemma disj_one_left [simp]: "\<^bold>1 \<^bold>\<squnion> x = \<^bold>1"
  by (fact dual.conj_zero_left)

lemma disj_cancel_left [simp]: "\<^bold>- x \<^bold>\<squnion> x = \<^bold>1"
  by (rule dual.conj_cancel_left)

lemma disj_conj_distrib2: "(y \<^bold>\<sqinter> z) \<^bold>\<squnion> x = (y \<^bold>\<squnion> x) \<^bold>\<sqinter> (z \<^bold>\<squnion> x)"
  by (rule dual.conj_disj_distrib2)

lemmas disj_conj_distribs = disj_conj_distrib disj_conj_distrib2

lemma disj_assoc: "(x \<^bold>\<squnion> y) \<^bold>\<squnion> z = x \<^bold>\<squnion> (y \<^bold>\<squnion> z)"
  by (fact ac_simps)

lemma disj_commute: "x \<^bold>\<squnion> y = y \<^bold>\<squnion> x"
  by (fact ac_simps)

lemmas disj_left_commute = disj.left_commute

lemmas disj_ac = disj.assoc disj.commute disj.left_commute

lemma disj_zero_left: "\<^bold>0 \<^bold>\<squnion> x = x"
  by (fact disj.left_neutral)

lemma disj_left_absorb: "x \<^bold>\<squnion> (x \<^bold>\<squnion> y) = x \<^bold>\<squnion> y"
  by (fact disj.left_idem)

lemma disj_absorb: "x \<^bold>\<squnion> x = x"
  by (fact disj.idem)


subsection \<open>De Morgan's Laws\<close>

lemma de_Morgan_conj [simp]: "\<^bold>- (x \<^bold>\<sqinter> y) = \<^bold>- x \<^bold>\<squnion> \<^bold>- y"
proof (rule compl_unique)
  have "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<^bold>- y)"
    by (rule conj_disj_distrib)
  also have "\<dots> = (y \<^bold>\<sqinter> (x \<^bold>\<sqinter> \<^bold>- x)) \<^bold>\<squnion> (x \<^bold>\<sqinter> (y \<^bold>\<sqinter> \<^bold>- y))"
    by (simp only: conj_ac)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = \<^bold>0"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_right)
next
  have "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = (x \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y)) \<^bold>\<sqinter> (y \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y))"
    by (rule disj_conj_distrib2)
  also have "\<dots> = (\<^bold>- y \<^bold>\<squnion> (x \<^bold>\<squnion> \<^bold>- x)) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> (y \<^bold>\<squnion> \<^bold>- y))"
    by (simp only: disj_ac)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = \<^bold>1"
    by (simp only: disj_cancel_right disj_one_right conj_one_right)
qed

lemma de_Morgan_disj [simp]: "\<^bold>- (x \<^bold>\<squnion> y) = \<^bold>- x \<^bold>\<sqinter> \<^bold>- y"
  using dual.boolean_algebra_axioms by (rule boolean_algebra.de_Morgan_conj)


subsection \<open>Symmetric Difference\<close>

definition xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>\<ominus>" 65)
  where "x \<^bold>\<ominus> y = (x \<^bold>\<sqinter> \<^bold>- y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> y)"

sublocale xor: comm_monoid xor \<open>\<^bold>0\<close>
proof
  fix x y z :: 'a
  let ?t = "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z)"
  have "?t \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (z \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- y) = ?t \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z \<^bold>\<sqinter> \<^bold>- z)"
    by (simp only: conj_cancel_right conj_zero_right)
  then show "(x \<^bold>\<ominus> y) \<^bold>\<ominus> z = x \<^bold>\<ominus> (y \<^bold>\<ominus> z)"
    by (simp only: xor_def de_Morgan_disj de_Morgan_conj double_compl)
      (simp only: conj_disj_distribs conj_ac disj_ac)
  show "x \<^bold>\<ominus> y = y \<^bold>\<ominus> x"
    by (simp only: xor_def conj_commute disj_commute)
  show "x \<^bold>\<ominus> \<^bold>0 = x"
    by (simp add: xor_def)
qed

lemmas xor_assoc = xor.assoc
lemmas xor_commute = xor.commute
lemmas xor_left_commute = xor.left_commute

lemmas xor_ac = xor.assoc xor.commute xor.left_commute

lemma xor_def2: "x \<^bold>\<ominus> y = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y)"
  using conj.commute conj_disj_distrib2 disj.commute xor_def by auto

lemma xor_zero_right: "x \<^bold>\<ominus> \<^bold>0 = x"
  by (fact xor.comm_neutral)

lemma xor_zero_left: "\<^bold>0 \<^bold>\<ominus> x = x"
  by (fact xor.left_neutral)

lemma xor_one_right [simp]: "x \<^bold>\<ominus> \<^bold>1 = \<^bold>- x"
  by (simp only: xor_def compl_one conj_zero_right conj_one_right disj_zero_left)

lemma xor_one_left [simp]: "\<^bold>1 \<^bold>\<ominus> x = \<^bold>- x"
  by (subst xor_commute) (rule xor_one_right)

lemma xor_self [simp]: "x \<^bold>\<ominus> x = \<^bold>0"
  by (simp only: xor_def conj_cancel_right conj_cancel_left disj_zero_right)

lemma xor_left_self [simp]: "x \<^bold>\<ominus> (x \<^bold>\<ominus> y) = y"
  by (simp only: xor_assoc [symmetric] xor_self xor_zero_left)

lemma xor_compl_left [simp]: "\<^bold>- x \<^bold>\<ominus> y = \<^bold>- (x \<^bold>\<ominus> y)"
  by (simp add: ac_simps flip: xor_one_left)

lemma xor_compl_right [simp]: "x \<^bold>\<ominus> \<^bold>- y = \<^bold>- (x \<^bold>\<ominus> y)"
  using xor_commute xor_compl_left by auto

lemma xor_cancel_right: "x \<^bold>\<ominus> \<^bold>- x = \<^bold>1"
  by (simp only: xor_compl_right xor_self compl_zero)

lemma xor_cancel_left: "\<^bold>- x \<^bold>\<ominus> x = \<^bold>1"
  by (simp only: xor_compl_left xor_self compl_zero)

lemma conj_xor_distrib: "x \<^bold>\<sqinter> (y \<^bold>\<ominus> z) = (x \<^bold>\<sqinter> y) \<^bold>\<ominus> (x \<^bold>\<sqinter> z)"
proof -
  have *: "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z) =
        (y \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z)"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_left)
  then show "x \<^bold>\<sqinter> (y \<^bold>\<ominus> z) = (x \<^bold>\<sqinter> y) \<^bold>\<ominus> (x \<^bold>\<sqinter> z)"
    by (simp (no_asm_use) only:
        xor_def de_Morgan_disj de_Morgan_conj double_compl
        conj_disj_distribs conj_ac disj_ac)
qed

lemma conj_xor_distrib2: "(y \<^bold>\<ominus> z) \<^bold>\<sqinter> x = (y \<^bold>\<sqinter> x) \<^bold>\<ominus> (z \<^bold>\<sqinter> x)"
  by (simp add: conj.commute conj_xor_distrib)

lemmas conj_xor_distribs = conj_xor_distrib conj_xor_distrib2

end

end

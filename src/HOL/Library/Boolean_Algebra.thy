(*  Title:      HOL/Library/Boolean_Algebra.thy
    Author:     Brian Huffman
*)

section \<open>Boolean Algebras\<close>

theory Boolean_Algebra
  imports Main
begin

locale boolean_algebra = conj: abel_semigroup "(\<^bold>\<sqinter>)" + disj: abel_semigroup "(\<^bold>\<squnion>)"
  for conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>\<sqinter>" 70)
    and disj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>\<squnion>" 65) +
  fixes compl :: "'a \<Rightarrow> 'a"  ("\<sim> _" [81] 80)
    and zero :: "'a"  ("\<zero>")
    and one  :: "'a"  ("\<one>")
  assumes conj_disj_distrib: "x \<^bold>\<sqinter> (y \<^bold>\<squnion> z) = (x \<^bold>\<sqinter> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z)"
    and disj_conj_distrib: "x \<^bold>\<squnion> (y \<^bold>\<sqinter> z) = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (x \<^bold>\<squnion> z)"
    and conj_one_right: "x \<^bold>\<sqinter> \<one> = x"
    and disj_zero_right: "x \<^bold>\<squnion> \<zero> = x"
    and conj_cancel_right [simp]: "x \<^bold>\<sqinter> \<sim> x = \<zero>"
    and disj_cancel_right [simp]: "x \<^bold>\<squnion> \<sim> x = \<one>"
begin

sublocale conj: semilattice_neutr "(\<^bold>\<sqinter>)" "\<one>"
proof
  show "x \<^bold>\<sqinter> \<one> = x" for x
    by (fact conj_one_right)
  show "x \<^bold>\<sqinter> x = x" for x
  proof -
    have "x \<^bold>\<sqinter> x = (x \<^bold>\<sqinter> x) \<^bold>\<squnion> \<zero>"
      by (simp add: disj_zero_right)
    also have "\<dots> = (x \<^bold>\<sqinter> x) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<sim> x)"
      by simp
    also have "\<dots> = x \<^bold>\<sqinter> (x \<^bold>\<squnion> \<sim> x)"
      by (simp only: conj_disj_distrib)
    also have "\<dots> = x \<^bold>\<sqinter> \<one>"
      by simp
    also have "\<dots> = x"
      by (simp add: conj_one_right)
    finally show ?thesis .
  qed
qed

sublocale disj: semilattice_neutr "(\<^bold>\<squnion>)" "\<zero>"
proof
  show "x \<^bold>\<squnion> \<zero> = x" for x
    by (fact disj_zero_right)
  show "x \<^bold>\<squnion> x = x" for x
  proof -
    have "x \<^bold>\<squnion> x = (x \<^bold>\<squnion> x) \<^bold>\<sqinter> \<one>"
      by simp
    also have "\<dots> = (x \<^bold>\<squnion> x) \<^bold>\<sqinter> (x \<^bold>\<squnion> \<sim> x)"
      by simp
    also have "\<dots> = x \<^bold>\<squnion> (x \<^bold>\<sqinter> \<sim> x)"
      by (simp only: disj_conj_distrib)
    also have "\<dots> = x \<^bold>\<squnion> \<zero>"
      by simp
    also have "\<dots> = x"
      by (simp add: disj_zero_right)
    finally show ?thesis .
  qed
qed


subsection \<open>Complement\<close>

lemma complement_unique:
  assumes 1: "a \<^bold>\<sqinter> x = \<zero>"
  assumes 2: "a \<^bold>\<squnion> x = \<one>"
  assumes 3: "a \<^bold>\<sqinter> y = \<zero>"
  assumes 4: "a \<^bold>\<squnion> y = \<one>"
  shows "x = y"
proof -
  from 1 3 have "(a \<^bold>\<sqinter> x) \<^bold>\<squnion> (x \<^bold>\<sqinter> y) = (a \<^bold>\<sqinter> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> y)"
    by simp
  then have "(x \<^bold>\<sqinter> a) \<^bold>\<squnion> (x \<^bold>\<sqinter> y) = (y \<^bold>\<sqinter> a) \<^bold>\<squnion> (y \<^bold>\<sqinter> x)"
    by (simp add: ac_simps)
  then have "x \<^bold>\<sqinter> (a \<^bold>\<squnion> y) = y \<^bold>\<sqinter> (a \<^bold>\<squnion> x)"
    by (simp add: conj_disj_distrib)
  with 2 4 have "x \<^bold>\<sqinter> \<one> = y \<^bold>\<sqinter> \<one>"
    by simp
  then show "x = y"
    by simp
qed

lemma compl_unique: "x \<^bold>\<sqinter> y = \<zero> \<Longrightarrow> x \<^bold>\<squnion> y = \<one> \<Longrightarrow> \<sim> x = y"
  by (rule complement_unique [OF conj_cancel_right disj_cancel_right])

lemma double_compl [simp]: "\<sim> (\<sim> x) = x"
proof (rule compl_unique)
  show "\<sim> x \<^bold>\<sqinter> x = \<zero>"
    by (simp only: conj_cancel_right conj.commute)
  show "\<sim> x \<^bold>\<squnion> x = \<one>"
    by (simp only: disj_cancel_right disj.commute)
qed

lemma compl_eq_compl_iff [simp]: "\<sim> x = \<sim> y \<longleftrightarrow> x = y"
  by (rule inj_eq [OF inj_on_inverseI]) (rule double_compl)


subsection \<open>Conjunction\<close>

lemma conj_zero_right [simp]: "x \<^bold>\<sqinter> \<zero> = \<zero>"
  using conj.left_idem conj_cancel_right by fastforce

lemma compl_one [simp]: "\<sim> \<one> = \<zero>"
  by (rule compl_unique [OF conj_zero_right disj_zero_right])

lemma conj_zero_left [simp]: "\<zero> \<^bold>\<sqinter> x = \<zero>"
  by (subst conj.commute) (rule conj_zero_right)

lemma conj_cancel_left [simp]: "\<sim> x \<^bold>\<sqinter> x = \<zero>"
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

lemma conj_one_left: "\<one> \<^bold>\<sqinter> x = x"
  by (fact conj.left_neutral)

lemma conj_left_absorb: "x \<^bold>\<sqinter> (x \<^bold>\<sqinter> y) = x \<^bold>\<sqinter> y"
  by (fact conj.left_idem)

lemma conj_absorb: "x \<^bold>\<sqinter> x = x"
  by (fact conj.idem)


subsection \<open>Disjunction\<close>

interpretation dual: boolean_algebra "(\<^bold>\<squnion>)" "(\<^bold>\<sqinter>)" compl \<one> \<zero>
  apply standard
       apply (rule disj_conj_distrib)
      apply (rule conj_disj_distrib)
     apply simp_all
  done

lemma compl_zero [simp]: "\<sim> \<zero> = \<one>"
  by (fact dual.compl_one)

lemma disj_one_right [simp]: "x \<^bold>\<squnion> \<one> = \<one>"
  by (fact dual.conj_zero_right)

lemma disj_one_left [simp]: "\<one> \<^bold>\<squnion> x = \<one>"
  by (fact dual.conj_zero_left)

lemma disj_cancel_left [simp]: "\<sim> x \<^bold>\<squnion> x = \<one>"
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

lemma disj_zero_left: "\<zero> \<^bold>\<squnion> x = x"
  by (fact disj.left_neutral)

lemma disj_left_absorb: "x \<^bold>\<squnion> (x \<^bold>\<squnion> y) = x \<^bold>\<squnion> y"
  by (fact disj.left_idem)

lemma disj_absorb: "x \<^bold>\<squnion> x = x"
  by (fact disj.idem)


subsection \<open>De Morgan's Laws\<close>

lemma de_Morgan_conj [simp]: "\<sim> (x \<^bold>\<sqinter> y) = \<sim> x \<^bold>\<squnion> \<sim> y"
proof (rule compl_unique)
  have "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<sim> x \<^bold>\<squnion> \<sim> y) = ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<sim> x) \<^bold>\<squnion> ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<sim> y)"
    by (rule conj_disj_distrib)
  also have "\<dots> = (y \<^bold>\<sqinter> (x \<^bold>\<sqinter> \<sim> x)) \<^bold>\<squnion> (x \<^bold>\<sqinter> (y \<^bold>\<sqinter> \<sim> y))"
    by (simp only: conj_ac)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<sim> x \<^bold>\<squnion> \<sim> y) = \<zero>"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_right)
next
  have "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<sim> x \<^bold>\<squnion> \<sim> y) = (x \<^bold>\<squnion> (\<sim> x \<^bold>\<squnion> \<sim> y)) \<^bold>\<sqinter> (y \<^bold>\<squnion> (\<sim> x \<^bold>\<squnion> \<sim> y))"
    by (rule disj_conj_distrib2)
  also have "\<dots> = (\<sim> y \<^bold>\<squnion> (x \<^bold>\<squnion> \<sim> x)) \<^bold>\<sqinter> (\<sim> x \<^bold>\<squnion> (y \<^bold>\<squnion> \<sim> y))"
    by (simp only: disj_ac)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<sim> x \<^bold>\<squnion> \<sim> y) = \<one>"
    by (simp only: disj_cancel_right disj_one_right conj_one_right)
qed

lemma de_Morgan_disj [simp]: "\<sim> (x \<^bold>\<squnion> y) = \<sim> x \<^bold>\<sqinter> \<sim> y"
  using dual.boolean_algebra_axioms by (rule boolean_algebra.de_Morgan_conj)


subsection \<open>Symmetric Difference\<close>

definition xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<oplus>" 65)
  where "x \<oplus> y = (x \<^bold>\<sqinter> \<sim> y) \<^bold>\<squnion> (\<sim> x \<^bold>\<sqinter> y)"

sublocale xor: abel_semigroup xor
proof
  fix x y z :: 'a
  let ?t = "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<sim> y \<^bold>\<sqinter> \<sim> z) \<^bold>\<squnion> (\<sim> x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<sim> z) \<^bold>\<squnion> (\<sim> x \<^bold>\<sqinter> \<sim> y \<^bold>\<sqinter> z)"
  have "?t \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<sim> x) \<^bold>\<squnion> (z \<^bold>\<sqinter> y \<^bold>\<sqinter> \<sim> y) = ?t \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<sim> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z \<^bold>\<sqinter> \<sim> z)"
    by (simp only: conj_cancel_right conj_zero_right)
  then show "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    by (simp only: xor_def de_Morgan_disj de_Morgan_conj double_compl)
      (simp only: conj_disj_distribs conj_ac disj_ac)
  show "x \<oplus> y = y \<oplus> x"
    by (simp only: xor_def conj_commute disj_commute)
qed

lemmas xor_assoc = xor.assoc
lemmas xor_commute = xor.commute
lemmas xor_left_commute = xor.left_commute

lemmas xor_ac = xor.assoc xor.commute xor.left_commute

lemma xor_def2: "x \<oplus> y = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (\<sim> x \<^bold>\<squnion> \<sim> y)"
  using conj.commute conj_disj_distrib2 disj.commute xor_def by auto

lemma xor_zero_right [simp]: "x \<oplus> \<zero> = x"
  by (simp only: xor_def compl_zero conj_one_right conj_zero_right disj_zero_right)

lemma xor_zero_left [simp]: "\<zero> \<oplus> x = x"
  by (subst xor_commute) (rule xor_zero_right)

lemma xor_one_right [simp]: "x \<oplus> \<one> = \<sim> x"
  by (simp only: xor_def compl_one conj_zero_right conj_one_right disj_zero_left)

lemma xor_one_left [simp]: "\<one> \<oplus> x = \<sim> x"
  by (subst xor_commute) (rule xor_one_right)

lemma xor_self [simp]: "x \<oplus> x = \<zero>"
  by (simp only: xor_def conj_cancel_right conj_cancel_left disj_zero_right)

lemma xor_left_self [simp]: "x \<oplus> (x \<oplus> y) = y"
  by (simp only: xor_assoc [symmetric] xor_self xor_zero_left)

lemma xor_compl_left [simp]: "\<sim> x \<oplus> y = \<sim> (x \<oplus> y)"
  by (metis xor_assoc xor_one_left)

lemma xor_compl_right [simp]: "x \<oplus> \<sim> y = \<sim> (x \<oplus> y)"
  using xor_commute xor_compl_left by auto

lemma xor_cancel_right: "x \<oplus> \<sim> x = \<one>"
  by (simp only: xor_compl_right xor_self compl_zero)

lemma xor_cancel_left: "\<sim> x \<oplus> x = \<one>"
  by (simp only: xor_compl_left xor_self compl_zero)

lemma conj_xor_distrib: "x \<^bold>\<sqinter> (y \<oplus> z) = (x \<^bold>\<sqinter> y) \<oplus> (x \<^bold>\<sqinter> z)"
proof -
  have *: "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<sim> z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<sim> y \<^bold>\<sqinter> z) =
        (y \<^bold>\<sqinter> x \<^bold>\<sqinter> \<sim> x) \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<sim> x) \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<sim> z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<sim> y \<^bold>\<sqinter> z)"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_left)
  then show "x \<^bold>\<sqinter> (y \<oplus> z) = (x \<^bold>\<sqinter> y) \<oplus> (x \<^bold>\<sqinter> z)"
    by (simp (no_asm_use) only:
        xor_def de_Morgan_disj de_Morgan_conj double_compl
        conj_disj_distribs conj_ac disj_ac)
qed

lemma conj_xor_distrib2: "(y \<oplus> z) \<^bold>\<sqinter> x = (y \<^bold>\<sqinter> x) \<oplus> (z \<^bold>\<sqinter> x)"
  by (simp add: conj.commute conj_xor_distrib)

lemmas conj_xor_distribs = conj_xor_distrib conj_xor_distrib2

end

end

(*  Title:      HOL/Library/Boolean_Algebra.thy
    Author:     Brian Huffman
*)

section \<open>Boolean Algebras\<close>

theory Boolean_Algebra
  imports Main
begin

locale boolean_algebra =
  fixes conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<sqinter>" 70)
    and disj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<squnion>" 65)
    and compl :: "'a \<Rightarrow> 'a"  ("\<sim> _" [81] 80)
    and zero :: "'a"  ("\<zero>")
    and one  :: "'a"  ("\<one>")
  assumes conj_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
    and disj_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
    and conj_commute: "x \<sqinter> y = y \<sqinter> x"
    and disj_commute: "x \<squnion> y = y \<squnion> x"
    and conj_disj_distrib: "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
    and disj_conj_distrib: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    and conj_one_right [simp]: "x \<sqinter> \<one> = x"
    and disj_zero_right [simp]: "x \<squnion> \<zero> = x"
    and conj_cancel_right [simp]: "x \<sqinter> \<sim> x = \<zero>"
    and disj_cancel_right [simp]: "x \<squnion> \<sim> x = \<one>"
begin

sublocale conj: abel_semigroup conj
  by standard (fact conj_assoc conj_commute)+

sublocale disj: abel_semigroup disj
  by standard (fact disj_assoc disj_commute)+

lemmas conj_left_commute = conj.left_commute
lemmas disj_left_commute = disj.left_commute

lemmas conj_ac = conj.assoc conj.commute conj.left_commute
lemmas disj_ac = disj.assoc disj.commute disj.left_commute

lemma dual: "boolean_algebra disj conj compl one zero"
  apply (rule boolean_algebra.intro)
           apply (rule disj_assoc)
          apply (rule conj_assoc)
         apply (rule disj_commute)
        apply (rule conj_commute)
       apply (rule disj_conj_distrib)
      apply (rule conj_disj_distrib)
     apply (rule disj_zero_right)
    apply (rule conj_one_right)
   apply (rule disj_cancel_right)
  apply (rule conj_cancel_right)
  done


subsection \<open>Complement\<close>

lemma complement_unique:
  assumes 1: "a \<sqinter> x = \<zero>"
  assumes 2: "a \<squnion> x = \<one>"
  assumes 3: "a \<sqinter> y = \<zero>"
  assumes 4: "a \<squnion> y = \<one>"
  shows "x = y"
proof -
  from 1 3 have "(a \<sqinter> x) \<squnion> (x \<sqinter> y) = (a \<sqinter> y) \<squnion> (x \<sqinter> y)"
    by simp
  then have "(x \<sqinter> a) \<squnion> (x \<sqinter> y) = (y \<sqinter> a) \<squnion> (y \<sqinter> x)"
    by (simp add: conj_commute)
  then have "x \<sqinter> (a \<squnion> y) = y \<sqinter> (a \<squnion> x)"
    by (simp add: conj_disj_distrib)
  with 2 4 have "x \<sqinter> \<one> = y \<sqinter> \<one>"
    by simp
  then show "x = y"
    by simp
qed

lemma compl_unique: "x \<sqinter> y = \<zero> \<Longrightarrow> x \<squnion> y = \<one> \<Longrightarrow> \<sim> x = y"
  by (rule complement_unique [OF conj_cancel_right disj_cancel_right])

lemma double_compl [simp]: "\<sim> (\<sim> x) = x"
proof (rule compl_unique)
  show "\<sim> x \<sqinter> x = \<zero>"
    by (simp only: conj_cancel_right conj_commute)
  show "\<sim> x \<squnion> x = \<one>"
    by (simp only: disj_cancel_right disj_commute)
qed

lemma compl_eq_compl_iff [simp]: "\<sim> x = \<sim> y \<longleftrightarrow> x = y"
  by (rule inj_eq [OF inj_on_inverseI]) (rule double_compl)


subsection \<open>Conjunction\<close>

lemma conj_absorb [simp]: "x \<sqinter> x = x"
proof -
  have "x \<sqinter> x = (x \<sqinter> x) \<squnion> \<zero>"
    by simp
  also have "\<dots> = (x \<sqinter> x) \<squnion> (x \<sqinter> \<sim> x)"
    by simp
  also have "\<dots> = x \<sqinter> (x \<squnion> \<sim> x)"
    by (simp only: conj_disj_distrib)
  also have "\<dots> = x \<sqinter> \<one>"
    by simp
  also have "\<dots> = x"
    by simp
  finally show ?thesis .
qed

lemma conj_zero_right [simp]: "x \<sqinter> \<zero> = \<zero>"
proof -
  from conj_cancel_right have "x \<sqinter> \<zero> = x \<sqinter> (x \<sqinter> \<sim> x)"
    by simp
  also from conj_assoc have "\<dots> = (x \<sqinter> x) \<sqinter> \<sim> x"
    by (simp only:)
  also from conj_absorb have "\<dots> = x \<sqinter> \<sim> x"
    by simp
  also have "\<dots> = \<zero>"
    by simp
  finally show ?thesis .
qed

lemma compl_one [simp]: "\<sim> \<one> = \<zero>"
  by (rule compl_unique [OF conj_zero_right disj_zero_right])

lemma conj_zero_left [simp]: "\<zero> \<sqinter> x = \<zero>"
  by (subst conj_commute) (rule conj_zero_right)

lemma conj_one_left [simp]: "\<one> \<sqinter> x = x"
  by (subst conj_commute) (rule conj_one_right)

lemma conj_cancel_left [simp]: "\<sim> x \<sqinter> x = \<zero>"
  by (subst conj_commute) (rule conj_cancel_right)

lemma conj_left_absorb [simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
  by (simp only: conj_assoc [symmetric] conj_absorb)

lemma conj_disj_distrib2: "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
  by (simp only: conj_commute conj_disj_distrib)

lemmas conj_disj_distribs = conj_disj_distrib conj_disj_distrib2


subsection \<open>Disjunction\<close>

lemma disj_absorb [simp]: "x \<squnion> x = x"
  by (rule boolean_algebra.conj_absorb [OF dual])

lemma disj_one_right [simp]: "x \<squnion> \<one> = \<one>"
  by (rule boolean_algebra.conj_zero_right [OF dual])

lemma compl_zero [simp]: "\<sim> \<zero> = \<one>"
  by (rule boolean_algebra.compl_one [OF dual])

lemma disj_zero_left [simp]: "\<zero> \<squnion> x = x"
  by (rule boolean_algebra.conj_one_left [OF dual])

lemma disj_one_left [simp]: "\<one> \<squnion> x = \<one>"
  by (rule boolean_algebra.conj_zero_left [OF dual])

lemma disj_cancel_left [simp]: "\<sim> x \<squnion> x = \<one>"
  by (rule boolean_algebra.conj_cancel_left [OF dual])

lemma disj_left_absorb [simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
  by (rule boolean_algebra.conj_left_absorb [OF dual])

lemma disj_conj_distrib2: "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  by (rule boolean_algebra.conj_disj_distrib2 [OF dual])

lemmas disj_conj_distribs = disj_conj_distrib disj_conj_distrib2


subsection \<open>De Morgan's Laws\<close>

lemma de_Morgan_conj [simp]: "\<sim> (x \<sqinter> y) = \<sim> x \<squnion> \<sim> y"
proof (rule compl_unique)
  have "(x \<sqinter> y) \<sqinter> (\<sim> x \<squnion> \<sim> y) = ((x \<sqinter> y) \<sqinter> \<sim> x) \<squnion> ((x \<sqinter> y) \<sqinter> \<sim> y)"
    by (rule conj_disj_distrib)
  also have "\<dots> = (y \<sqinter> (x \<sqinter> \<sim> x)) \<squnion> (x \<sqinter> (y \<sqinter> \<sim> y))"
    by (simp only: conj_ac)
  finally show "(x \<sqinter> y) \<sqinter> (\<sim> x \<squnion> \<sim> y) = \<zero>"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_right)
next
  have "(x \<sqinter> y) \<squnion> (\<sim> x \<squnion> \<sim> y) = (x \<squnion> (\<sim> x \<squnion> \<sim> y)) \<sqinter> (y \<squnion> (\<sim> x \<squnion> \<sim> y))"
    by (rule disj_conj_distrib2)
  also have "\<dots> = (\<sim> y \<squnion> (x \<squnion> \<sim> x)) \<sqinter> (\<sim> x \<squnion> (y \<squnion> \<sim> y))"
    by (simp only: disj_ac)
  finally show "(x \<sqinter> y) \<squnion> (\<sim> x \<squnion> \<sim> y) = \<one>"
    by (simp only: disj_cancel_right disj_one_right conj_one_right)
qed

lemma de_Morgan_disj [simp]: "\<sim> (x \<squnion> y) = \<sim> x \<sqinter> \<sim> y"
  by (rule boolean_algebra.de_Morgan_conj [OF dual])


subsection \<open>Symmetric Difference\<close>

definition xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<oplus>" 65)
  where "x \<oplus> y = (x \<sqinter> \<sim> y) \<squnion> (\<sim> x \<sqinter> y)"

sublocale xor: abel_semigroup xor
proof
  fix x y z :: 'a
  let ?t = "(x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> \<sim> y \<sqinter> \<sim> z) \<squnion> (\<sim> x \<sqinter> y \<sqinter> \<sim> z) \<squnion> (\<sim> x \<sqinter> \<sim> y \<sqinter> z)"
  have "?t \<squnion> (z \<sqinter> x \<sqinter> \<sim> x) \<squnion> (z \<sqinter> y \<sqinter> \<sim> y) = ?t \<squnion> (x \<sqinter> y \<sqinter> \<sim> y) \<squnion> (x \<sqinter> z \<sqinter> \<sim> z)"
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

lemma xor_def2: "x \<oplus> y = (x \<squnion> y) \<sqinter> (\<sim> x \<squnion> \<sim> y)"
  by (simp only: xor_def conj_disj_distribs disj_ac conj_ac conj_cancel_right disj_zero_left)

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
  apply (simp only: xor_def de_Morgan_disj de_Morgan_conj double_compl)
  apply (simp only: conj_disj_distribs)
  apply (simp only: conj_cancel_right conj_cancel_left)
  apply (simp only: disj_zero_left disj_zero_right)
  apply (simp only: disj_ac conj_ac)
  done

lemma xor_compl_right [simp]: "x \<oplus> \<sim> y = \<sim> (x \<oplus> y)"
  apply (simp only: xor_def de_Morgan_disj de_Morgan_conj double_compl)
  apply (simp only: conj_disj_distribs)
  apply (simp only: conj_cancel_right conj_cancel_left)
  apply (simp only: disj_zero_left disj_zero_right)
  apply (simp only: disj_ac conj_ac)
  done

lemma xor_cancel_right: "x \<oplus> \<sim> x = \<one>"
  by (simp only: xor_compl_right xor_self compl_zero)

lemma xor_cancel_left: "\<sim> x \<oplus> x = \<one>"
  by (simp only: xor_compl_left xor_self compl_zero)

lemma conj_xor_distrib: "x \<sqinter> (y \<oplus> z) = (x \<sqinter> y) \<oplus> (x \<sqinter> z)"
proof -
  have *: "(x \<sqinter> y \<sqinter> \<sim> z) \<squnion> (x \<sqinter> \<sim> y \<sqinter> z) =
        (y \<sqinter> x \<sqinter> \<sim> x) \<squnion> (z \<sqinter> x \<sqinter> \<sim> x) \<squnion> (x \<sqinter> y \<sqinter> \<sim> z) \<squnion> (x \<sqinter> \<sim> y \<sqinter> z)"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_left)
  then show "x \<sqinter> (y \<oplus> z) = (x \<sqinter> y) \<oplus> (x \<sqinter> z)"
    by (simp (no_asm_use) only:
        xor_def de_Morgan_disj de_Morgan_conj double_compl
        conj_disj_distribs conj_ac disj_ac)
qed

lemma conj_xor_distrib2: "(y \<oplus> z) \<sqinter> x = (y \<sqinter> x) \<oplus> (z \<sqinter> x)"
proof -
  have "x \<sqinter> (y \<oplus> z) = (x \<sqinter> y) \<oplus> (x \<sqinter> z)"
    by (rule conj_xor_distrib)
  then show "(y \<oplus> z) \<sqinter> x = (y \<sqinter> x) \<oplus> (z \<sqinter> x)"
    by (simp only: conj_commute)
qed

lemmas conj_xor_distribs = conj_xor_distrib conj_xor_distrib2

end

end

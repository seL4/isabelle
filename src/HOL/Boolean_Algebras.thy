(*  Title:      HOL/Boolean_Algebras.thy
    Author:     Brian Huffman
    Author:     Florian Haftmann
*)

section \<open>Boolean Algebras\<close>

theory Boolean_Algebras
  imports Lattices
begin

subsection \<open>Abstract boolean algebra\<close>

locale abstract_boolean_algebra = conj: abel_semigroup \<open>(\<^bold>\<sqinter>)\<close> + disj: abel_semigroup \<open>(\<^bold>\<squnion>)\<close>
  for conj :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>\<^bold>\<sqinter>\<close> 70)
    and disj :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>\<^bold>\<squnion>\<close> 65) +
  fixes compl :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>\<^bold>- _\<close> [81] 80)
    and zero :: \<open>'a\<close>  (\<open>\<^bold>0\<close>)
    and one  :: \<open>'a\<close>  (\<open>\<^bold>1\<close>)
  assumes conj_disj_distrib: \<open>x \<^bold>\<sqinter> (y \<^bold>\<squnion> z) = (x \<^bold>\<sqinter> y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z)\<close>
    and disj_conj_distrib: \<open>x \<^bold>\<squnion> (y \<^bold>\<sqinter> z) = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (x \<^bold>\<squnion> z)\<close>
    and conj_one_right: \<open>x \<^bold>\<sqinter> \<^bold>1 = x\<close>
    and disj_zero_right: \<open>x \<^bold>\<squnion> \<^bold>0 = x\<close>
    and conj_cancel_right [simp]: \<open>x \<^bold>\<sqinter> \<^bold>- x = \<^bold>0\<close>
    and disj_cancel_right [simp]: \<open>x \<^bold>\<squnion> \<^bold>- x = \<^bold>1\<close>
begin

sublocale conj: semilattice_neutr \<open>(\<^bold>\<sqinter>)\<close> \<open>\<^bold>1\<close>
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

sublocale disj: semilattice_neutr \<open>(\<^bold>\<squnion>)\<close> \<open>\<^bold>0\<close>
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


subsubsection \<open>Complement\<close>

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


subsubsection \<open>Conjunction\<close>

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


subsubsection \<open>Disjunction\<close>

context
begin

interpretation dual: abstract_boolean_algebra \<open>(\<^bold>\<squnion>)\<close> \<open>(\<^bold>\<sqinter>)\<close> compl \<open>\<^bold>1\<close> \<open>\<^bold>0\<close>
  apply standard
       apply (rule disj_conj_distrib)
      apply (rule conj_disj_distrib)
     apply simp_all
  done

lemma disj_one_right [simp]: "x \<^bold>\<squnion> \<^bold>1 = \<^bold>1"
  by (fact dual.conj_zero_right)

lemma compl_zero [simp]: "\<^bold>- \<^bold>0 = \<^bold>1"
  by (fact dual.compl_one)

lemma disj_one_left [simp]: "\<^bold>1 \<^bold>\<squnion> x = \<^bold>1"
  by (fact dual.conj_zero_left)

lemma disj_cancel_left [simp]: "\<^bold>- x \<^bold>\<squnion> x = \<^bold>1"
  by (fact dual.conj_cancel_left)

lemma disj_conj_distrib2: "(y \<^bold>\<sqinter> z) \<^bold>\<squnion> x = (y \<^bold>\<squnion> x) \<^bold>\<sqinter> (z \<^bold>\<squnion> x)"
  by (fact dual.conj_disj_distrib2)

lemmas disj_conj_distribs = disj_conj_distrib disj_conj_distrib2

end


subsubsection \<open>De Morgan's Laws\<close>

lemma de_Morgan_conj [simp]: "\<^bold>- (x \<^bold>\<sqinter> y) = \<^bold>- x \<^bold>\<squnion> \<^bold>- y"
proof (rule compl_unique)
  have "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> ((x \<^bold>\<sqinter> y) \<^bold>\<sqinter> \<^bold>- y)"
    by (rule conj_disj_distrib)
  also have "\<dots> = (y \<^bold>\<sqinter> (x \<^bold>\<sqinter> \<^bold>- x)) \<^bold>\<squnion> (x \<^bold>\<sqinter> (y \<^bold>\<sqinter> \<^bold>- y))"
    by (simp only: ac_simps)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = \<^bold>0"
    by (simp only: conj_cancel_right conj_zero_right disj_zero_right)
next
  have "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = (x \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y)) \<^bold>\<sqinter> (y \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y))"
    by (rule disj_conj_distrib2)
  also have "\<dots> = (\<^bold>- y \<^bold>\<squnion> (x \<^bold>\<squnion> \<^bold>- x)) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> (y \<^bold>\<squnion> \<^bold>- y))"
    by (simp only: ac_simps)
  finally show "(x \<^bold>\<sqinter> y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y) = \<^bold>1"
    by (simp only: disj_cancel_right disj_one_right conj_one_right)
qed

context
begin

interpretation dual: abstract_boolean_algebra \<open>(\<^bold>\<squnion>)\<close> \<open>(\<^bold>\<sqinter>)\<close> compl \<open>\<^bold>1\<close> \<open>\<^bold>0\<close>
  apply standard
       apply (rule disj_conj_distrib)
      apply (rule conj_disj_distrib)
     apply simp_all
  done

lemma de_Morgan_disj [simp]: "\<^bold>- (x \<^bold>\<squnion> y) = \<^bold>- x \<^bold>\<sqinter> \<^bold>- y"
  by (fact dual.de_Morgan_conj)

end

end


subsection \<open>Symmetric Difference\<close>

locale abstract_boolean_algebra_sym_diff = abstract_boolean_algebra +
  fixes xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>\<^bold>\<ominus>\<close> 65)
  assumes xor_def : \<open>x \<^bold>\<ominus> y = (x \<^bold>\<sqinter> \<^bold>- y) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> y)\<close>
begin

sublocale xor: comm_monoid xor \<open>\<^bold>0\<close>
proof
  fix x y z :: 'a
  let ?t = "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (\<^bold>- x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z)"
  have "?t \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (z \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- y) = ?t \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- y) \<^bold>\<squnion> (x \<^bold>\<sqinter> z \<^bold>\<sqinter> \<^bold>- z)"
    by (simp only: conj_cancel_right conj_zero_right)
  then show "(x \<^bold>\<ominus> y) \<^bold>\<ominus> z = x \<^bold>\<ominus> (y \<^bold>\<ominus> z)"
    by (simp only: xor_def de_Morgan_disj de_Morgan_conj double_compl)
      (simp only: conj_disj_distribs conj_ac ac_simps)
  show "x \<^bold>\<ominus> y = y \<^bold>\<ominus> x"
    by (simp only: xor_def ac_simps)
  show "x \<^bold>\<ominus> \<^bold>0 = x"
    by (simp add: xor_def)
qed

lemma xor_def2:
  \<open>x \<^bold>\<ominus> y = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y)\<close>
proof -
  note xor_def [of x y]
  also have \<open>x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<squnion> \<^bold>- x \<^bold>\<sqinter> y = ((x \<^bold>\<squnion> \<^bold>- x) \<^bold>\<sqinter> (\<^bold>- y \<^bold>\<squnion> \<^bold>- x)) \<^bold>\<sqinter> (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (\<^bold>- y \<^bold>\<squnion> y)\<close>
    by (simp add: ac_simps disj_conj_distribs)
  also have \<open>\<dots> = (x \<^bold>\<squnion> y) \<^bold>\<sqinter> (\<^bold>- x \<^bold>\<squnion> \<^bold>- y)\<close>
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma xor_one_right [simp]: "x \<^bold>\<ominus> \<^bold>1 = \<^bold>- x"
  by (simp only: xor_def compl_one conj_zero_right conj_one_right disj.left_neutral)

lemma xor_one_left [simp]: "\<^bold>1 \<^bold>\<ominus> x = \<^bold>- x"
  using xor_one_right [of x] by (simp add: ac_simps)

lemma xor_self [simp]: "x \<^bold>\<ominus> x = \<^bold>0"
  by (simp only: xor_def conj_cancel_right conj_cancel_left disj_zero_right)

lemma xor_left_self [simp]: "x \<^bold>\<ominus> (x \<^bold>\<ominus> y) = y"
  by (simp only: xor.assoc [symmetric] xor_self xor.left_neutral)

lemma xor_compl_left [simp]: "\<^bold>- x \<^bold>\<ominus> y = \<^bold>- (x \<^bold>\<ominus> y)"
  by (simp add: ac_simps flip: xor_one_left)

lemma xor_compl_right [simp]: "x \<^bold>\<ominus> \<^bold>- y = \<^bold>- (x \<^bold>\<ominus> y)"
  using xor.commute xor_compl_left by auto

lemma xor_cancel_right [simp]: "x \<^bold>\<ominus> \<^bold>- x = \<^bold>1"
  by (simp only: xor_compl_right xor_self compl_zero)

lemma xor_cancel_left [simp]: "\<^bold>- x \<^bold>\<ominus> x = \<^bold>1"
  by (simp only: xor_compl_left xor_self compl_zero)

lemma conj_xor_distrib: "x \<^bold>\<sqinter> (y \<^bold>\<ominus> z) = (x \<^bold>\<sqinter> y) \<^bold>\<ominus> (x \<^bold>\<sqinter> z)"
proof -
  have *: "(x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z) =
        (y \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (z \<^bold>\<sqinter> x \<^bold>\<sqinter> \<^bold>- x) \<^bold>\<squnion> (x \<^bold>\<sqinter> y \<^bold>\<sqinter> \<^bold>- z) \<^bold>\<squnion> (x \<^bold>\<sqinter> \<^bold>- y \<^bold>\<sqinter> z)"
    by (simp only: conj_cancel_right conj_zero_right disj.left_neutral)
  then show "x \<^bold>\<sqinter> (y \<^bold>\<ominus> z) = (x \<^bold>\<sqinter> y) \<^bold>\<ominus> (x \<^bold>\<sqinter> z)"
    by (simp (no_asm_use) only:
        xor_def de_Morgan_disj de_Morgan_conj double_compl
        conj_disj_distribs ac_simps)
qed

lemma conj_xor_distrib2: "(y \<^bold>\<ominus> z) \<^bold>\<sqinter> x = (y \<^bold>\<sqinter> x) \<^bold>\<ominus> (z \<^bold>\<sqinter> x)"
  by (simp add: conj.commute conj_xor_distrib)

lemmas conj_xor_distribs = conj_xor_distrib conj_xor_distrib2

end


subsection \<open>Type classes\<close>

class boolean_algebra = distrib_lattice + bounded_lattice + minus + uminus +
  assumes inf_compl_bot: \<open>x \<sqinter> - x = \<bottom>\<close>
    and sup_compl_top: \<open>x \<squnion> - x = \<top>\<close>
  assumes diff_eq: \<open>x - y = x \<sqinter> - y\<close>
begin

sublocale boolean_algebra: abstract_boolean_algebra \<open>(\<sqinter>)\<close> \<open>(\<squnion>)\<close> uminus \<bottom> \<top>
  apply standard
       apply (rule inf_sup_distrib1)
      apply (rule sup_inf_distrib1)
     apply (simp_all add: ac_simps inf_compl_bot sup_compl_top)
  done

lemma compl_inf_bot: "- x \<sqinter> x = \<bottom>"
  by (fact boolean_algebra.conj_cancel_left)

lemma compl_sup_top: "- x \<squnion> x = \<top>"
  by (fact boolean_algebra.disj_cancel_left)

lemma compl_unique:
  assumes "x \<sqinter> y = \<bottom>"
    and "x \<squnion> y = \<top>"
  shows "- x = y"
  using assms by (rule boolean_algebra.compl_unique)

lemma double_compl: "- (- x) = x"
  by (fact boolean_algebra.double_compl)

lemma compl_eq_compl_iff: "- x = - y \<longleftrightarrow> x = y"
  by (fact boolean_algebra.compl_eq_compl_iff)

lemma compl_bot_eq: "- \<bottom> = \<top>"
  by (fact boolean_algebra.compl_zero)

lemma compl_top_eq: "- \<top> = \<bottom>"
  by (fact boolean_algebra.compl_one)

lemma compl_inf: "- (x \<sqinter> y) = - x \<squnion> - y"
  by (fact boolean_algebra.de_Morgan_conj)

lemma compl_sup: "- (x \<squnion> y) = - x \<sqinter> - y"
  by (fact boolean_algebra.de_Morgan_disj)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
proof -
  from assms have "x \<squnion> y = y" by (simp only: le_iff_sup)
  then have "- (x \<squnion> y) = - y" by simp
  then have "- x \<sqinter> - y = - y" by simp
  then have "- y \<sqinter> - x = - y" by (simp only: inf_commute)
  then show ?thesis by (simp only: le_iff_inf)
qed

lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
proof -
  from assms have "- (- x) \<le> - y" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
proof -
  from assms have "- x \<le> - (- y)" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_compl_iff [simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
proof -
  from assms have "- (- x) < - y" by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
proof -
  from assms have "- x < - (- y)"
    by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

lemma sup_cancel_left1: \<open>x \<squnion> a \<squnion> (- x \<squnion> b) = \<top>\<close>
  by (simp add: ac_simps)

lemma sup_cancel_left2: \<open>- x \<squnion> a \<squnion> (x \<squnion> b) = \<top>\<close>
  by (simp add: ac_simps)

lemma inf_cancel_left1: \<open>x \<sqinter> a \<sqinter> (- x \<sqinter> b) = \<bottom>\<close>
  by (simp add: ac_simps)

lemma inf_cancel_left2: \<open>- x \<sqinter> a \<sqinter> (x \<sqinter> b) = \<bottom>\<close>
  by (simp add: ac_simps)

lemma sup_compl_top_left1 [simp]: \<open>- x \<squnion> (x \<squnion> y) = \<top>\<close>
  by (simp add: sup_assoc [symmetric])

lemma sup_compl_top_left2 [simp]: \<open>x \<squnion> (- x \<squnion> y) = \<top>\<close>
  using sup_compl_top_left1 [of "- x" y] by simp

lemma inf_compl_bot_left1 [simp]: \<open>- x \<sqinter> (x \<sqinter> y) = \<bottom>\<close>
  by (simp add: inf_assoc [symmetric])

lemma inf_compl_bot_left2 [simp]: \<open>x \<sqinter> (- x \<sqinter> y) = \<bottom>\<close>
  using inf_compl_bot_left1 [of "- x" y] by simp

lemma inf_compl_bot_right [simp]: \<open>x \<sqinter> (y \<sqinter> - x) = \<bottom>\<close>
  by (subst inf_left_commute) simp

end


subsection \<open>Lattice on \<^typ>\<open>bool\<close>\<close>

instantiation bool :: boolean_algebra
begin

definition bool_Compl_def [simp]: "uminus = Not"

definition bool_diff_def [simp]: "A - B \<longleftrightarrow> A \<and> \<not> B"

definition [simp]: "P \<sqinter> Q \<longleftrightarrow> P \<and> Q"

definition [simp]: "P \<squnion> Q \<longleftrightarrow> P \<or> Q"

instance by standard auto

end

lemma sup_boolI1: "P \<Longrightarrow> P \<squnion> Q"
  by simp

lemma sup_boolI2: "Q \<Longrightarrow> P \<squnion> Q"
  by simp

lemma sup_boolE: "P \<squnion> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

instance "fun" :: (type, boolean_algebra) boolean_algebra
  by standard (rule ext, simp_all add: inf_compl_bot sup_compl_top diff_eq)+


subsection \<open>Lattice on unary and binary predicates\<close>

lemma inf1I: "A x \<Longrightarrow> B x \<Longrightarrow> (A \<sqinter> B) x"
  by (simp add: inf_fun_def)

lemma inf2I: "A x y \<Longrightarrow> B x y \<Longrightarrow> (A \<sqinter> B) x y"
  by (simp add: inf_fun_def)

lemma inf1E: "(A \<sqinter> B) x \<Longrightarrow> (A x \<Longrightarrow> B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf2E: "(A \<sqinter> B) x y \<Longrightarrow> (A x y \<Longrightarrow> B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf1D1: "(A \<sqinter> B) x \<Longrightarrow> A x"
  by (rule inf1E)

lemma inf2D1: "(A \<sqinter> B) x y \<Longrightarrow> A x y"
  by (rule inf2E)

lemma inf1D2: "(A \<sqinter> B) x \<Longrightarrow> B x"
  by (rule inf1E)

lemma inf2D2: "(A \<sqinter> B) x y \<Longrightarrow> B x y"
  by (rule inf2E)

lemma sup1I1: "A x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I1: "A x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1I2: "B x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I2: "B x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1E: "(A \<squnion> B) x \<Longrightarrow> (A x \<Longrightarrow> P) \<Longrightarrow> (B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

lemma sup2E: "(A \<squnion> B) x y \<Longrightarrow> (A x y \<Longrightarrow> P) \<Longrightarrow> (B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

text \<open> \<^medskip> Classical introduction rule: no commitment to \<open>A\<close> vs \<open>B\<close>.\<close>

lemma sup1CI: "(\<not> B x \<Longrightarrow> A x) \<Longrightarrow> (A \<squnion> B) x"
  by (auto simp add: sup_fun_def)

lemma sup2CI: "(\<not> B x y \<Longrightarrow> A x y) \<Longrightarrow> (A \<squnion> B) x y"
  by (auto simp add: sup_fun_def)


subsection \<open>Simproc setup\<close>

locale boolean_algebra_cancel
begin

lemma sup1: "(A::'a::semilattice_sup) \<equiv> sup k a \<Longrightarrow> sup A b \<equiv> sup k (sup a b)"
  by (simp only: ac_simps)

lemma sup2: "(B::'a::semilattice_sup) \<equiv> sup k b \<Longrightarrow> sup a B \<equiv> sup k (sup a b)"
  by (simp only: ac_simps)

lemma sup0: "(a::'a::bounded_semilattice_sup_bot) \<equiv> sup a bot"
  by simp

lemma inf1: "(A::'a::semilattice_inf) \<equiv> inf k a \<Longrightarrow> inf A b \<equiv> inf k (inf a b)"
  by (simp only: ac_simps)

lemma inf2: "(B::'a::semilattice_inf) \<equiv> inf k b \<Longrightarrow> inf a B \<equiv> inf k (inf a b)"
  by (simp only: ac_simps)

lemma inf0: "(a::'a::bounded_semilattice_inf_top) \<equiv> inf a top"
  by simp

end

ML_file \<open>Tools/boolean_algebra_cancel.ML\<close>

simproc_setup boolean_algebra_cancel_sup ("sup a b::'a::boolean_algebra") =
  \<open>fn phi => fn ss => try Boolean_Algebra_Cancel.cancel_sup_conv\<close>

simproc_setup boolean_algebra_cancel_inf ("inf a b::'a::boolean_algebra") =
  \<open>fn phi => fn ss => try Boolean_Algebra_Cancel.cancel_inf_conv\<close>


context boolean_algebra
begin
    
lemma shunt1: "(x \<sqinter> y \<le> z) \<longleftrightarrow> (x \<le> -y \<squnion> z)"
proof
  assume "x \<sqinter> y \<le> z"
  hence  "-y \<squnion> (x \<sqinter> y) \<le> -y \<squnion> z"
    using sup.mono by blast
  hence "-y \<squnion> x \<le> -y \<squnion> z"
    by (simp add: sup_inf_distrib1)
  thus "x \<le> -y \<squnion> z"
    by simp
next
  assume "x \<le> -y \<squnion> z"
  hence "x \<sqinter> y \<le> (-y \<squnion> z) \<sqinter> y"
    using inf_mono by auto
  thus  "x \<sqinter> y \<le> z"
    using inf.boundedE inf_sup_distrib2 by auto
qed

lemma shunt2: "(x \<sqinter> -y \<le> z) \<longleftrightarrow> (x \<le> y \<squnion> z)"
  by (simp add: shunt1)

lemma inf_shunt: "(x \<sqinter> y = \<bottom>) \<longleftrightarrow> (x \<le> - y)"
  by (simp add: order.eq_iff shunt1)
  
lemma sup_shunt: "(x \<squnion> y = \<top>) \<longleftrightarrow> (- x \<le> y)"
  using inf_shunt [of \<open>- x\<close> \<open>- y\<close>, symmetric] 
  by (simp flip: compl_sup compl_top_eq)

lemma diff_shunt_var: "(x - y = \<bottom>) \<longleftrightarrow> (x \<le> y)"
  by (simp add: diff_eq inf_shunt)

lemma sup_neg_inf:
  \<open>p \<le> q \<squnion> r \<longleftrightarrow> p \<sqinter> -q \<le> r\<close>  (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?P
  then have \<open>p \<sqinter> - q \<le> (q \<squnion> r) \<sqinter> - q\<close>
    by (rule inf_mono) simp
  then show ?Q
    by (simp add: inf_sup_distrib2)
next
  assume ?Q
  then have \<open>p \<sqinter> - q \<squnion> q \<le> r \<squnion> q\<close>
    by (rule sup_mono) simp
  then show ?P
    by (simp add: sup_inf_distrib ac_simps)
qed

end

end

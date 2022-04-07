(*  Title:      HOL/Library/Complemented_Lattices.thy
    Authors:    Jose Manuel Rodriguez Caballero, Dominique Unruh
*)

section \<open>Complemented Lattices\<close>

theory Complemented_Lattices
  imports Main
begin

text \<open>The following class \<open>complemented_lattice\<close> describes complemented lattices (with
  \<^const>\<open>uminus\<close> for the complement). The definition follows
  \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties\<close>.
  Additionally, it adopts the convention from \<^class>\<open>boolean_algebra\<close> of defining
  \<^const>\<open>minus\<close> in terms of the complement.\<close>

class complemented_lattice = bounded_lattice + uminus + minus
  opening lattice_syntax +
  assumes inf_compl_bot [simp]: \<open>x \<sqinter> - x = \<bottom>\<close>
    and sup_compl_top [simp]: \<open>x \<squnion> - x = \<top>\<close>
    and diff_eq: \<open>x - y = x \<sqinter> - y\<close>
begin

lemma dual_complemented_lattice:
  "class.complemented_lattice (\<lambda>x y. x \<squnion> (- y)) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
proof (rule class.complemented_lattice.intro)
  show "class.bounded_lattice (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_bounded_lattice)
  show "class.complemented_lattice_axioms (\<lambda>x y. x \<squnion> - y) uminus (\<squnion>) (\<sqinter>) \<top> \<bottom>"
    by (unfold_locales, auto simp add: diff_eq)
qed

lemma compl_inf_bot [simp]: \<open>- x \<sqinter> x = \<bottom>\<close>
  by (simp add: inf_commute)

lemma compl_sup_top [simp]: \<open>- x \<squnion> x = \<top>\<close>
  by (simp add: sup_commute)

end

class complete_complemented_lattice = complemented_lattice + complete_lattice

text \<open>The following class \<open>complemented_lattice\<close> describes orthocomplemented lattices,
  following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation\<close>.\<close>
class orthocomplemented_lattice = complemented_lattice
  opening lattice_syntax +
  assumes ortho_involution [simp]: "- (- x) = x"
    and ortho_antimono: "x \<le> y \<Longrightarrow> - x \<ge> - y" begin

lemma dual_orthocomplemented_lattice:
  "class.orthocomplemented_lattice (\<lambda>x y. x \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
proof (rule class.orthocomplemented_lattice.intro)
  show "class.complemented_lattice (\<lambda>x y. x \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_complemented_lattice)
  show "class.orthocomplemented_lattice_axioms uminus (\<lambda>x y. y \<le> x)"
    by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)
qed

lemma compl_eq_compl_iff [simp]: \<open>- x = - y \<longleftrightarrow> x = y\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?P
  then have \<open>- (- x) = - (- y)\<close>
    by simp
  then show ?Q
    by simp
next
  assume ?Q
  then show ?P
    by simp
qed

lemma compl_bot_eq [simp]: \<open>- \<bottom> = \<top>\<close>
proof -
  have \<open>- \<bottom> = - (\<top> \<sqinter> - \<top>)\<close>
    by simp
  also have \<open>\<dots> = \<top>\<close>
    by (simp only: inf_top_left) simp
  finally show ?thesis .
qed

lemma compl_top_eq [simp]: "- \<top> = \<bottom>"
  using compl_bot_eq ortho_involution by blast

text \<open>De Morgan's law\<close> \<comment> \<open>Proof from \<^url>\<open>https://planetmath.org/orthocomplementedlattice\<close>\<close>
lemma compl_sup [simp]: "- (x \<squnion> y) = - x \<sqinter> - y"
proof -
  have "- (x \<squnion> y) \<le> - x"
    by (simp add: ortho_antimono)
  moreover have "- (x \<squnion> y) \<le> - y"
    by (simp add: ortho_antimono)
  ultimately have 1: "- (x \<squnion> y) \<le> - x \<sqinter> - y"
    by (simp add: sup.coboundedI1)
  have \<open>x \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded1 ortho_antimono ortho_involution)
  moreover have \<open>y \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded2 ortho_antimono ortho_involution)
  ultimately have \<open>x \<squnion> y \<le> - (-x \<sqinter> -y)\<close>
    by auto
  hence 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
    using ortho_antimono by fastforce
  from 1 2 show ?thesis
    using dual_order.antisym by blast
qed

text \<open>De Morgan's law\<close>
lemma compl_inf [simp]: "- (x \<sqinter> y) = - x \<squnion> - y"
  using compl_sup
  by (metis ortho_involution)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
  by (simp add: assms local.ortho_antimono)

lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
  using assms ortho_antimono by fastforce

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
  using assms local.ortho_antimono by fastforce

lemma compl_less_compl_iff[simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
  using assms compl_less_compl_iff by fastforce

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
  using assms compl_le_swap1 compl_le_swap2 less_le_not_le by auto

lemma sup_cancel_left1: \<open>x \<squnion> a \<squnion> (- x \<squnion> b) = \<top>\<close>
  by (simp add: sup_commute sup_left_commute)

lemma sup_cancel_left2: \<open>- x \<squnion> a \<squnion> (x \<squnion> b) = \<top>\<close>
  by (simp add: sup.commute sup_left_commute)

lemma inf_cancel_left1: \<open>x \<sqinter> a \<sqinter> (- x \<sqinter> b) = \<bottom>\<close>
  by (simp add: inf.left_commute inf_commute)

lemma inf_cancel_left2: \<open>- x \<sqinter> a \<sqinter> (x \<sqinter> b) = \<bottom>\<close>
  using inf.left_commute inf_commute by auto

lemma sup_compl_top_left1 [simp]: \<open>- x \<squnion> (x \<squnion> y) = \<top>\<close>
  by (simp add: sup_assoc[symmetric])

lemma sup_compl_top_left2 [simp]: \<open>x \<squnion> (- x \<squnion> y) = \<top>\<close>
  using sup_compl_top_left1[of "- x" y] by simp

lemma inf_compl_bot_left1 [simp]: \<open>- x \<sqinter> (x \<sqinter> y) = \<bottom>\<close>
  by (simp add: inf_assoc[symmetric])

lemma inf_compl_bot_left2 [simp]: \<open>x \<sqinter> (- x \<sqinter> y) = \<bottom>\<close>
  using inf_compl_bot_left1[of "- x" y] by simp

lemma inf_compl_bot_right [simp]: \<open>x \<sqinter> (y \<sqinter> - x) = \<bottom>\<close>
  by (subst inf_left_commute) simp

end

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice
begin

subclass complete_complemented_lattice ..

end

text \<open>The following class \<open>orthomodular_lattice\<close> describes orthomodular lattices,
following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices\<close>.\<close>
class orthomodular_lattice = orthocomplemented_lattice
  opening lattice_syntax +
  assumes orthomodular: "x \<le> y \<Longrightarrow> x \<squnion> (- x) \<sqinter> y = y" begin

lemma dual_orthomodular_lattice:
  "class.orthomodular_lattice (\<lambda>x y. x \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>)  \<top> \<bottom>"
proof (rule class.orthomodular_lattice.intro)
  show "class.orthocomplemented_lattice (\<lambda>x y. x \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_orthocomplemented_lattice)
  show "class.orthomodular_lattice_axioms uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<sqinter>)"
  proof (unfold_locales)
    show "(x::'a) \<sqinter> (- x \<squnion> y) = y"
      if "(y::'a) \<le> x"
      for x :: 'a
        and y :: 'a
      using that local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
  qed

qed

end

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice
begin

subclass complete_orthocomplemented_lattice ..

end

context boolean_algebra
  opening lattice_syntax
begin

subclass orthomodular_lattice
proof
  fix x y
  show \<open>x \<squnion> - x \<sqinter> y = y\<close>
    if \<open>x \<le> y\<close>
    using that
    by (simp add: sup.absorb_iff2 sup_inf_distrib1)
  show \<open>x - y = x \<sqinter> - y\<close>
    by (simp add: diff_eq)
qed auto

end

context complete_boolean_algebra
begin

subclass complete_orthomodular_lattice ..

end

lemma image_of_maximum:
  fixes f::"'a::order \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes "mono f"
    and "\<And>x. x:M \<Longrightarrow> x\<le>m"
    and "m:M"
  shows "(SUP x\<in>M. f x) = f m"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) cSup_eq_maximum imageE imageI monoD)

lemma cSup_eq_cSup:
  fixes A B :: \<open>'a::conditionally_complete_lattice set\<close>
  assumes bdd: \<open>bdd_above A\<close>
  assumes B: \<open>\<And>a. a\<in>A \<Longrightarrow> \<exists>b\<in>B. b \<ge> a\<close>
  assumes A: \<open>\<And>b. b\<in>B \<Longrightarrow> \<exists>a\<in>A. a \<ge> b\<close>
  shows \<open>Sup A = Sup B\<close>
proof (cases \<open>B = {}\<close>)
  case True
  with A B have \<open>A = {}\<close>
    by auto
  with True show ?thesis by simp
next
  case False
  have \<open>bdd_above B\<close>
    by (meson A bdd bdd_above_def order_trans)
  have \<open>A \<noteq> {}\<close>
    using A False by blast
  moreover have \<open>a \<le> Sup B\<close> if \<open>a \<in> A\<close> for a
  proof -
    obtain b where \<open>b \<in> B\<close> and \<open>b \<ge> a\<close>
      using B \<open>a \<in> A\<close> by auto
    then show ?thesis
      apply (rule cSup_upper2)
      using \<open>bdd_above B\<close> by simp
  qed
  moreover have \<open>Sup B \<le> c\<close> if \<open>\<And>a. a \<in> A \<Longrightarrow> a \<le> c\<close> for c
    using False apply (rule cSup_least)
    using A that by fastforce
  ultimately show ?thesis
    by (rule cSup_eq_non_empty)
qed

end

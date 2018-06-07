(*  Title:      HOL/Library/Infinite_Set.thy
    Author:     Stephan Merz
*)

section \<open>Infinite Sets and Related Concepts\<close>

theory Infinite_Set
  imports Main
begin

subsection \<open>The set of natural numbers is infinite\<close>

lemma infinite_nat_iff_unbounded_le: "infinite S \<longleftrightarrow> (\<forall>m. \<exists>n\<ge>m. n \<in> S)"
  for S :: "nat set"
  using frequently_cofinite[of "\<lambda>x. x \<in> S"]
  by (simp add: cofinite_eq_sequentially frequently_def eventually_sequentially)

lemma infinite_nat_iff_unbounded: "infinite S \<longleftrightarrow> (\<forall>m. \<exists>n>m. n \<in> S)"
  for S :: "nat set"
  using frequently_cofinite[of "\<lambda>x. x \<in> S"]
  by (simp add: cofinite_eq_sequentially frequently_def eventually_at_top_dense)

lemma finite_nat_iff_bounded: "finite S \<longleftrightarrow> (\<exists>k. S \<subseteq> {..<k})"
  for S :: "nat set"
  using infinite_nat_iff_unbounded_le[of S] by (simp add: subset_eq) (metis not_le)

lemma finite_nat_iff_bounded_le: "finite S \<longleftrightarrow> (\<exists>k. S \<subseteq> {.. k})"
  for S :: "nat set"
  using infinite_nat_iff_unbounded[of S] by (simp add: subset_eq) (metis not_le)

lemma finite_nat_bounded: "finite S \<Longrightarrow> \<exists>k. S \<subseteq> {..<k}"
  for S :: "nat set"
  by (simp add: finite_nat_iff_bounded)


text \<open>
  For a set of natural numbers to be infinite, it is enough to know
  that for any number larger than some \<open>k\<close>, there is some larger
  number that is an element of the set.
\<close>

lemma unbounded_k_infinite: "\<forall>m>k. \<exists>n>m. n \<in> S \<Longrightarrow> infinite (S::nat set)"
  apply (clarsimp simp add: finite_nat_set_iff_bounded)
  apply (drule_tac x="Suc (max m k)" in spec)
  using less_Suc_eq apply fastforce
  done

lemma nat_not_finite: "finite (UNIV::nat set) \<Longrightarrow> R"
  by simp

lemma range_inj_infinite:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "inj f"
  shows "infinite (range f)"
proof
  assume "finite (range f)"
  from this assms have "finite (UNIV::nat set)"
    by (rule finite_imageD)
  then show False by simp
qed


subsection \<open>The set of integers is also infinite\<close>

lemma infinite_int_iff_infinite_nat_abs: "infinite S \<longleftrightarrow> infinite ((nat \<circ> abs) ` S)"
  for S :: "int set"
proof -
  have "inj_on nat (abs ` A)" for A
    by (rule inj_onI) auto
  then show ?thesis
    by (auto simp flip: image_comp dest: finite_image_absD finite_imageD)
qed

proposition infinite_int_iff_unbounded_le: "infinite S \<longleftrightarrow> (\<forall>m. \<exists>n. \<bar>n\<bar> \<ge> m \<and> n \<in> S)"
  for S :: "int set"
  by (simp add: infinite_int_iff_infinite_nat_abs infinite_nat_iff_unbounded_le o_def image_def)
    (metis abs_ge_zero nat_le_eq_zle le_nat_iff)

proposition infinite_int_iff_unbounded: "infinite S \<longleftrightarrow> (\<forall>m. \<exists>n. \<bar>n\<bar> > m \<and> n \<in> S)"
  for S :: "int set"
  by (simp add: infinite_int_iff_infinite_nat_abs infinite_nat_iff_unbounded o_def image_def)
    (metis (full_types) nat_le_iff nat_mono not_le)

proposition finite_int_iff_bounded: "finite S \<longleftrightarrow> (\<exists>k. abs ` S \<subseteq> {..<k})"
  for S :: "int set"
  using infinite_int_iff_unbounded_le[of S] by (simp add: subset_eq) (metis not_le)

proposition finite_int_iff_bounded_le: "finite S \<longleftrightarrow> (\<exists>k. abs ` S \<subseteq> {.. k})"
  for S :: "int set"
  using infinite_int_iff_unbounded[of S] by (simp add: subset_eq) (metis not_le)


subsection \<open>Infinitely Many and Almost All\<close>

text \<open>
  We often need to reason about the existence of infinitely many
  (resp., all but finitely many) objects satisfying some predicate, so
  we introduce corresponding binders and their proof rules.
\<close>

lemma not_INFM [simp]: "\<not> (INFM x. P x) \<longleftrightarrow> (MOST x. \<not> P x)"
  by (rule not_frequently)

lemma not_MOST [simp]: "\<not> (MOST x. P x) \<longleftrightarrow> (INFM x. \<not> P x)"
  by (rule not_eventually)

lemma INFM_const [simp]: "(INFM x::'a. P) \<longleftrightarrow> P \<and> infinite (UNIV::'a set)"
  by (simp add: frequently_const_iff)

lemma MOST_const [simp]: "(MOST x::'a. P) \<longleftrightarrow> P \<or> finite (UNIV::'a set)"
  by (simp add: eventually_const_iff)

lemma INFM_imp_distrib: "(INFM x. P x \<longrightarrow> Q x) \<longleftrightarrow> ((MOST x. P x) \<longrightarrow> (INFM x. Q x))"
  by (rule frequently_imp_iff)

lemma MOST_imp_iff: "MOST x. P x \<Longrightarrow> (MOST x. P x \<longrightarrow> Q x) \<longleftrightarrow> (MOST x. Q x)"
  by (auto intro: eventually_rev_mp eventually_mono)

lemma INFM_conjI: "INFM x. P x \<Longrightarrow> MOST x. Q x \<Longrightarrow> INFM x. P x \<and> Q x"
  by (rule frequently_rev_mp[of P]) (auto elim: eventually_mono)


text \<open>Properties of quantifiers with injective functions.\<close>

lemma INFM_inj: "INFM x. P (f x) \<Longrightarrow> inj f \<Longrightarrow> INFM x. P x"
  using finite_vimageI[of "{x. P x}" f] by (auto simp: frequently_cofinite)

lemma MOST_inj: "MOST x. P x \<Longrightarrow> inj f \<Longrightarrow> MOST x. P (f x)"
  using finite_vimageI[of "{x. \<not> P x}" f] by (auto simp: eventually_cofinite)


text \<open>Properties of quantifiers with singletons.\<close>

lemma not_INFM_eq [simp]:
  "\<not> (INFM x. x = a)"
  "\<not> (INFM x. a = x)"
  unfolding frequently_cofinite by simp_all

lemma MOST_neq [simp]:
  "MOST x. x \<noteq> a"
  "MOST x. a \<noteq> x"
  unfolding eventually_cofinite by simp_all

lemma INFM_neq [simp]:
  "(INFM x::'a. x \<noteq> a) \<longleftrightarrow> infinite (UNIV::'a set)"
  "(INFM x::'a. a \<noteq> x) \<longleftrightarrow> infinite (UNIV::'a set)"
  unfolding frequently_cofinite by simp_all

lemma MOST_eq [simp]:
  "(MOST x::'a. x = a) \<longleftrightarrow> finite (UNIV::'a set)"
  "(MOST x::'a. a = x) \<longleftrightarrow> finite (UNIV::'a set)"
  unfolding eventually_cofinite by simp_all

lemma MOST_eq_imp:
  "MOST x. x = a \<longrightarrow> P x"
  "MOST x. a = x \<longrightarrow> P x"
  unfolding eventually_cofinite by simp_all


text \<open>Properties of quantifiers over the naturals.\<close>

lemma MOST_nat: "(\<forall>\<^sub>\<infinity>n. P n) \<longleftrightarrow> (\<exists>m. \<forall>n>m. P n)"
  for P :: "nat \<Rightarrow> bool"
  by (auto simp add: eventually_cofinite finite_nat_iff_bounded_le subset_eq simp flip: not_le)

lemma MOST_nat_le: "(\<forall>\<^sub>\<infinity>n. P n) \<longleftrightarrow> (\<exists>m. \<forall>n\<ge>m. P n)"
  for P :: "nat \<Rightarrow> bool"
  by (auto simp add: eventually_cofinite finite_nat_iff_bounded subset_eq simp flip: not_le)

lemma INFM_nat: "(\<exists>\<^sub>\<infinity>n. P n) \<longleftrightarrow> (\<forall>m. \<exists>n>m. P n)"
  for P :: "nat \<Rightarrow> bool"
  by (simp add: frequently_cofinite infinite_nat_iff_unbounded)

lemma INFM_nat_le: "(\<exists>\<^sub>\<infinity>n. P n) \<longleftrightarrow> (\<forall>m. \<exists>n\<ge>m. P n)"
  for P :: "nat \<Rightarrow> bool"
  by (simp add: frequently_cofinite infinite_nat_iff_unbounded_le)

lemma MOST_INFM: "infinite (UNIV::'a set) \<Longrightarrow> MOST x::'a. P x \<Longrightarrow> INFM x::'a. P x"
  by (simp add: eventually_frequently)

lemma MOST_Suc_iff: "(MOST n. P (Suc n)) \<longleftrightarrow> (MOST n. P n)"
  by (simp add: cofinite_eq_sequentially)

lemma MOST_SucI: "MOST n. P n \<Longrightarrow> MOST n. P (Suc n)"
  and MOST_SucD: "MOST n. P (Suc n) \<Longrightarrow> MOST n. P n"
  by (simp_all add: MOST_Suc_iff)

lemma MOST_ge_nat: "MOST n::nat. m \<le> n"
  by (simp add: cofinite_eq_sequentially)

\<comment> \<open>legacy names\<close>
lemma Inf_many_def: "Inf_many P \<longleftrightarrow> infinite {x. P x}" by (fact frequently_cofinite)
lemma Alm_all_def: "Alm_all P \<longleftrightarrow> \<not> (INFM x. \<not> P x)" by simp
lemma INFM_iff_infinite: "(INFM x. P x) \<longleftrightarrow> infinite {x. P x}" by (fact frequently_cofinite)
lemma MOST_iff_cofinite: "(MOST x. P x) \<longleftrightarrow> finite {x. \<not> P x}" by (fact eventually_cofinite)
lemma INFM_EX: "(\<exists>\<^sub>\<infinity>x. P x) \<Longrightarrow> (\<exists>x. P x)" by (fact frequently_ex)
lemma ALL_MOST: "\<forall>x. P x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. P x" by (fact always_eventually)
lemma INFM_mono: "\<exists>\<^sub>\<infinity>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> \<exists>\<^sub>\<infinity>x. Q x" by (fact frequently_elim1)
lemma MOST_mono: "\<forall>\<^sub>\<infinity>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> \<forall>\<^sub>\<infinity>x. Q x" by (fact eventually_mono)
lemma INFM_disj_distrib: "(\<exists>\<^sub>\<infinity>x. P x \<or> Q x) \<longleftrightarrow> (\<exists>\<^sub>\<infinity>x. P x) \<or> (\<exists>\<^sub>\<infinity>x. Q x)" by (fact frequently_disj_iff)
lemma MOST_rev_mp: "\<forall>\<^sub>\<infinity>x. P x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. P x \<longrightarrow> Q x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. Q x" by (fact eventually_rev_mp)
lemma MOST_conj_distrib: "(\<forall>\<^sub>\<infinity>x. P x \<and> Q x) \<longleftrightarrow> (\<forall>\<^sub>\<infinity>x. P x) \<and> (\<forall>\<^sub>\<infinity>x. Q x)" by (fact eventually_conj_iff)
lemma MOST_conjI: "MOST x. P x \<Longrightarrow> MOST x. Q x \<Longrightarrow> MOST x. P x \<and> Q x" by (fact eventually_conj)
lemma INFM_finite_Bex_distrib: "finite A \<Longrightarrow> (INFM y. \<exists>x\<in>A. P x y) \<longleftrightarrow> (\<exists>x\<in>A. INFM y. P x y)" by (fact frequently_bex_finite_distrib)
lemma MOST_finite_Ball_distrib: "finite A \<Longrightarrow> (MOST y. \<forall>x\<in>A. P x y) \<longleftrightarrow> (\<forall>x\<in>A. MOST y. P x y)" by (fact eventually_ball_finite_distrib)
lemma INFM_E: "INFM x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> thesis) \<Longrightarrow> thesis" by (fact frequentlyE)
lemma MOST_I: "(\<And>x. P x) \<Longrightarrow> MOST x. P x" by (rule eventuallyI)
lemmas MOST_iff_finiteNeg = MOST_iff_cofinite


subsection \<open>Enumeration of an Infinite Set\<close>

text \<open>The set's element type must be wellordered (e.g. the natural numbers).\<close>

text \<open>
  Could be generalized to
    @{prop "enumerate' S n = (SOME t. t \<in> s \<and> finite {s\<in>S. s < t} \<and> card {s\<in>S. s < t} = n)"}.
\<close>

primrec (in wellorder) enumerate :: "'a set \<Rightarrow> nat \<Rightarrow> 'a"
  where
    enumerate_0: "enumerate S 0 = (LEAST n. n \<in> S)"
  | enumerate_Suc: "enumerate S (Suc n) = enumerate (S - {LEAST n. n \<in> S}) n"

lemma enumerate_Suc': "enumerate S (Suc n) = enumerate (S - {enumerate S 0}) n"
  by simp

lemma enumerate_in_set: "infinite S \<Longrightarrow> enumerate S n \<in> S"
proof (induct n arbitrary: S)
  case 0
  then show ?case
    by (fastforce intro: LeastI dest!: infinite_imp_nonempty)
next
  case (Suc n)
  then show ?case
    by simp (metis DiffE infinite_remove)
qed

declare enumerate_0 [simp del] enumerate_Suc [simp del]

lemma enumerate_step: "infinite S \<Longrightarrow> enumerate S n < enumerate S (Suc n)"
  apply (induct n arbitrary: S)
   apply (rule order_le_neq_trans)
    apply (simp add: enumerate_0 Least_le enumerate_in_set)
   apply (simp only: enumerate_Suc')
   apply (subgoal_tac "enumerate (S - {enumerate S 0}) 0 \<in> S - {enumerate S 0}")
    apply (blast intro: sym)
   apply (simp add: enumerate_in_set del: Diff_iff)
  apply (simp add: enumerate_Suc')
  done

lemma enumerate_mono: "m < n \<Longrightarrow> infinite S \<Longrightarrow> enumerate S m < enumerate S n"
  by (induct m n rule: less_Suc_induct) (auto intro: enumerate_step)

lemma le_enumerate:
  assumes S: "infinite S"
  shows "n \<le> enumerate S n"
  using S
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "n \<le> enumerate S n" by simp
  also note enumerate_mono[of n "Suc n", OF _ \<open>infinite S\<close>]
  finally show ?case by simp
qed

lemma enumerate_Suc'':
  fixes S :: "'a::wellorder set"
  assumes "infinite S"
  shows "enumerate S (Suc n) = (LEAST s. s \<in> S \<and> enumerate S n < s)"
  using assms
proof (induct n arbitrary: S)
  case 0
  then have "\<forall>s \<in> S. enumerate S 0 \<le> s"
    by (auto simp: enumerate.simps intro: Least_le)
  then show ?case
    unfolding enumerate_Suc' enumerate_0[of "S - {enumerate S 0}"]
    by (intro arg_cong[where f = Least] ext) auto
next
  case (Suc n S)
  show ?case
    using enumerate_mono[OF zero_less_Suc \<open>infinite S\<close>, of n] \<open>infinite S\<close>
    apply (subst (1 2) enumerate_Suc')
    apply (subst Suc)
     apply (use \<open>infinite S\<close> in simp)
    apply (intro arg_cong[where f = Least] ext)
    apply (auto simp flip: enumerate_Suc')
    done
qed

lemma enumerate_Ex:
  fixes S :: "nat set"
  assumes S: "infinite S"
    and s: "s \<in> S"
  shows "\<exists>n. enumerate S n = s"
  using s
proof (induct s rule: less_induct)
  case (less s)
  show ?case
  proof (cases "\<exists>y\<in>S. y < s")
    case True
    let ?y = "Max {s'\<in>S. s' < s}"
    from True have y: "\<And>x. ?y < x \<longleftrightarrow> (\<forall>s'\<in>S. s' < s \<longrightarrow> s' < x)"
      by (subst Max_less_iff) auto
    then have y_in: "?y \<in> {s'\<in>S. s' < s}"
      by (intro Max_in) auto
    with less.hyps[of ?y] obtain n where "enumerate S n = ?y"
      by auto
    with S have "enumerate S (Suc n) = s"
      by (auto simp: y less enumerate_Suc'' intro!: Least_equality)
    then show ?thesis by auto
  next
    case False
    then have "\<forall>t\<in>S. s \<le> t" by auto
    with \<open>s \<in> S\<close> show ?thesis
      by (auto intro!: exI[of _ 0] Least_equality simp: enumerate_0)
  qed
qed

lemma bij_enumerate:
  fixes S :: "nat set"
  assumes S: "infinite S"
  shows "bij_betw (enumerate S) UNIV S"
proof -
  have "\<And>n m. n \<noteq> m \<Longrightarrow> enumerate S n \<noteq> enumerate S m"
    using enumerate_mono[OF _ \<open>infinite S\<close>] by (auto simp: neq_iff)
  then have "inj (enumerate S)"
    by (auto simp: inj_on_def)
  moreover have "\<forall>s \<in> S. \<exists>i. enumerate S i = s"
    using enumerate_Ex[OF S] by auto
  moreover note \<open>infinite S\<close>
  ultimately show ?thesis
    unfolding bij_betw_def by (auto intro: enumerate_in_set)
qed

text \<open>A pair of weird and wonderful lemmas from HOL Light.\<close>
lemma finite_transitivity_chain:
  assumes "finite A"
    and R: "\<And>x. \<not> R x x" "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
    and A: "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> A \<and> R x y"
  shows "A = {}"
  using \<open>finite A\<close> A
proof (induct A)
  case empty
  then show ?case by simp
next
  case (insert a A)
  with R show ?case
    by (metis empty_iff insert_iff)   (* somewhat slow *)
qed

corollary Union_maximal_sets:
  assumes "finite \<F>"
  shows "\<Union>{T \<in> \<F>. \<forall>U\<in>\<F>. \<not> T \<subset> U} = \<Union>\<F>"
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" by force
  show "?rhs \<subseteq> ?lhs"
  proof (rule Union_subsetI)
    fix S
    assume "S \<in> \<F>"
    have "{T \<in> \<F>. S \<subseteq> T} = {}"
      if "\<not> (\<exists>y. y \<in> {T \<in> \<F>. \<forall>U\<in>\<F>. \<not> T \<subset> U} \<and> S \<subseteq> y)"
      apply (rule finite_transitivity_chain [of _ "\<lambda>T U. S \<subseteq> T \<and> T \<subset> U"])
         apply (use assms that in auto)
      apply (blast intro: dual_order.trans psubset_imp_subset)
      done
    with \<open>S \<in> \<F>\<close> show "\<exists>y. y \<in> {T \<in> \<F>. \<forall>U\<in>\<F>. \<not> T \<subset> U} \<and> S \<subseteq> y"
      by blast
  qed
qed

end

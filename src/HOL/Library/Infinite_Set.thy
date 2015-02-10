(*  Title:      HOL/Library/Infinite_Set.thy
    Author:     Stephan Merz
*)

section {* Infinite Sets and Related Concepts *}

theory Infinite_Set
imports Main
begin

subsection "Infinite Sets"

text {*
  Some elementary facts about infinite sets, mostly by Stephan Merz.
  Beware! Because "infinite" merely abbreviates a negation, these
  lemmas may not work well with @{text "blast"}.
*}

abbreviation infinite :: "'a set \<Rightarrow> bool"
  where "infinite S \<equiv> \<not> finite S"

text {*
  Infinite sets are non-empty, and if we remove some elements from an
  infinite set, the result is still infinite.
*}

lemma infinite_imp_nonempty: "infinite S \<Longrightarrow> S \<noteq> {}"
  by auto

lemma infinite_remove: "infinite S \<Longrightarrow> infinite (S - {a})"
  by simp

lemma Diff_infinite_finite:
  assumes T: "finite T" and S: "infinite S"
  shows "infinite (S - T)"
  using T
proof induct
  from S
  show "infinite (S - {})" by auto
next
  fix T x
  assume ih: "infinite (S - T)"
  have "S - (insert x T) = (S - T) - {x}"
    by (rule Diff_insert)
  with ih
  show "infinite (S - (insert x T))"
    by (simp add: infinite_remove)
qed

lemma Un_infinite: "infinite S \<Longrightarrow> infinite (S \<union> T)"
  by simp

lemma infinite_Un: "infinite (S \<union> T) \<longleftrightarrow> infinite S \<or> infinite T"
  by simp

lemma infinite_super:
  assumes T: "S \<subseteq> T" and S: "infinite S"
  shows "infinite T"
proof
  assume "finite T"
  with T have "finite S" by (simp add: finite_subset)
  with S show False by simp
qed

text {*
  As a concrete example, we prove that the set of natural numbers is
  infinite.
*}

lemma finite_nat_bounded: assumes S: "finite (S::nat set)" shows "\<exists>k. S \<subseteq> {..<k}"
proof cases
  assume "S \<noteq> {}" with Max_less_iff[OF S this] show ?thesis
    by auto
qed simp

lemma finite_nat_iff_bounded: "finite (S::nat set) \<longleftrightarrow> (\<exists>k. S \<subseteq> {..<k})"
  by (auto intro: finite_nat_bounded dest: finite_subset)

lemma finite_nat_iff_bounded_le:
  "finite (S::nat set) \<longleftrightarrow> (\<exists>k. S \<subseteq> {..k})"  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain k where "S \<subseteq> {..<k}"
    by (blast dest: finite_nat_bounded)
  then have "S \<subseteq> {..k}" by auto
  then show ?rhs ..
next
  assume ?rhs
  then obtain k where "S \<subseteq> {..k}" ..
  then show "finite S"
    by (rule finite_subset) simp
qed

lemma infinite_nat_iff_unbounded: "infinite (S::nat set) \<longleftrightarrow> (\<forall>m. \<exists>n. m < n \<and> n \<in> S)"
  unfolding finite_nat_iff_bounded_le by (auto simp: subset_eq not_le)

lemma infinite_nat_iff_unbounded_le:
  "infinite (S::nat set) \<longleftrightarrow> (\<forall>m. \<exists>n. m \<le> n \<and> n \<in> S)"
  unfolding finite_nat_iff_bounded by (auto simp: subset_eq not_less)

text {*
  For a set of natural numbers to be infinite, it is enough to know
  that for any number larger than some @{text k}, there is some larger
  number that is an element of the set.
*}

lemma unbounded_k_infinite:
  assumes k: "\<forall>m. k < m \<longrightarrow> (\<exists>n. m < n \<and> n \<in> S)"
  shows "infinite (S::nat set)"
proof -
  {
    fix m have "\<exists>n. m < n \<and> n \<in> S"
    proof (cases "k < m")
      case True
      with k show ?thesis by blast
    next
      case False
      from k obtain n where "Suc k < n \<and> n \<in> S" by auto
      with False have "m < n \<and> n \<in> S" by auto
      then show ?thesis ..
    qed
  }
  then show ?thesis
    by (auto simp add: infinite_nat_iff_unbounded)
qed

lemma nat_not_finite: "finite (UNIV::nat set) \<Longrightarrow> R"
  by simp

lemma range_inj_infinite:
  "inj (f::nat \<Rightarrow> 'a) \<Longrightarrow> infinite (range f)"
proof
  assume "finite (range f)" and "inj f"
  then have "finite (UNIV::nat set)"
    by (rule finite_imageD)
  then show False by simp
qed

text {*
  For any function with infinite domain and finite range there is some
  element that is the image of infinitely many domain elements.  In
  particular, any infinite sequence of elements from a finite set
  contains some element that occurs infinitely often.
*}

lemma inf_img_fin_dom':
  assumes img: "finite (f ` A)" and dom: "infinite A"
  shows "\<exists>y \<in> f ` A. infinite (f -` {y} \<inter> A)"
proof (rule ccontr)
  have "A \<subseteq> (\<Union>y\<in>f ` A. f -` {y} \<inter> A)" by auto
  moreover
  assume "\<not> ?thesis"
  with img have "finite (\<Union>y\<in>f ` A. f -` {y} \<inter> A)" by blast
  ultimately have "finite A" by(rule finite_subset)
  with dom show False by contradiction
qed

lemma inf_img_fin_domE':
  assumes "finite (f ` A)" and "infinite A"
  obtains y where "y \<in> f`A" and "infinite (f -` {y} \<inter> A)"
  using assms by (blast dest: inf_img_fin_dom')

lemma inf_img_fin_dom:
  assumes img: "finite (f`A)" and dom: "infinite A"
  shows "\<exists>y \<in> f`A. infinite (f -` {y})"
using inf_img_fin_dom'[OF assms] by auto

lemma inf_img_fin_domE:
  assumes "finite (f`A)" and "infinite A"
  obtains y where "y \<in> f`A" and "infinite (f -` {y})"
  using assms by (blast dest: inf_img_fin_dom)

subsection "Infinitely Many and Almost All"

text {*
  We often need to reason about the existence of infinitely many
  (resp., all but finitely many) objects satisfying some predicate, so
  we introduce corresponding binders and their proof rules.
*}

definition Inf_many :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "INFM " 10)
  where "Inf_many P \<longleftrightarrow> infinite {x. P x}"

definition Alm_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "MOST " 10)
  where "Alm_all P \<longleftrightarrow> \<not> (INFM x. \<not> P x)"

notation (xsymbols)
  Inf_many  (binder "\<exists>\<^sub>\<infinity>" 10) and
  Alm_all  (binder "\<forall>\<^sub>\<infinity>" 10)

notation (HTML output)
  Inf_many  (binder "\<exists>\<^sub>\<infinity>" 10) and
  Alm_all  (binder "\<forall>\<^sub>\<infinity>" 10)

lemma INFM_iff_infinite: "(INFM x. P x) \<longleftrightarrow> infinite {x. P x}"
  unfolding Inf_many_def ..

lemma MOST_iff_cofinite: "(MOST x. P x) \<longleftrightarrow> finite {x. \<not> P x}"
  unfolding Alm_all_def Inf_many_def by simp

(* legacy name *)
lemmas MOST_iff_finiteNeg = MOST_iff_cofinite

lemma not_INFM [simp]: "\<not> (INFM x. P x) \<longleftrightarrow> (MOST x. \<not> P x)"
  unfolding Alm_all_def not_not ..

lemma not_MOST [simp]: "\<not> (MOST x. P x) \<longleftrightarrow> (INFM x. \<not> P x)"
  unfolding Alm_all_def not_not ..

lemma INFM_const [simp]: "(INFM x::'a. P) \<longleftrightarrow> P \<and> infinite (UNIV::'a set)"
  unfolding Inf_many_def by simp

lemma MOST_const [simp]: "(MOST x::'a. P) \<longleftrightarrow> P \<or> finite (UNIV::'a set)"
  unfolding Alm_all_def by simp

lemma INFM_EX: "(\<exists>\<^sub>\<infinity>x. P x) \<Longrightarrow> (\<exists>x. P x)"
  apply (erule contrapos_pp)
  apply simp
  done

lemma ALL_MOST: "\<forall>x. P x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. P x"
  by simp

lemma INFM_E:
  assumes "INFM x. P x"
  obtains x where "P x"
  using INFM_EX [OF assms] by (rule exE)

lemma MOST_I:
  assumes "\<And>x. P x"
  shows "MOST x. P x"
  using assms by simp

lemma INFM_mono:
  assumes inf: "\<exists>\<^sub>\<infinity>x. P x" and q: "\<And>x. P x \<Longrightarrow> Q x"
  shows "\<exists>\<^sub>\<infinity>x. Q x"
proof -
  from inf have "infinite {x. P x}" unfolding Inf_many_def .
  moreover from q have "{x. P x} \<subseteq> {x. Q x}" by auto
  ultimately show ?thesis
    using Inf_many_def infinite_super by blast
qed

lemma MOST_mono: "\<forall>\<^sub>\<infinity>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> \<forall>\<^sub>\<infinity>x. Q x"
  unfolding Alm_all_def by (blast intro: INFM_mono)

lemma INFM_disj_distrib:
  "(\<exists>\<^sub>\<infinity>x. P x \<or> Q x) \<longleftrightarrow> (\<exists>\<^sub>\<infinity>x. P x) \<or> (\<exists>\<^sub>\<infinity>x. Q x)"
  unfolding Inf_many_def by (simp add: Collect_disj_eq)

lemma INFM_imp_distrib:
  "(INFM x. P x \<longrightarrow> Q x) \<longleftrightarrow> ((MOST x. P x) \<longrightarrow> (INFM x. Q x))"
  by (simp only: imp_conv_disj INFM_disj_distrib not_MOST)

lemma MOST_conj_distrib:
  "(\<forall>\<^sub>\<infinity>x. P x \<and> Q x) \<longleftrightarrow> (\<forall>\<^sub>\<infinity>x. P x) \<and> (\<forall>\<^sub>\<infinity>x. Q x)"
  unfolding Alm_all_def by (simp add: INFM_disj_distrib del: disj_not1)

lemma MOST_conjI:
  "MOST x. P x \<Longrightarrow> MOST x. Q x \<Longrightarrow> MOST x. P x \<and> Q x"
  by (simp add: MOST_conj_distrib)

lemma INFM_conjI:
  "INFM x. P x \<Longrightarrow> MOST x. Q x \<Longrightarrow> INFM x. P x \<and> Q x"
  unfolding MOST_iff_cofinite INFM_iff_infinite
  apply (drule (1) Diff_infinite_finite)
  apply (simp add: Collect_conj_eq Collect_neg_eq)
  done

lemma MOST_rev_mp:
  assumes "\<forall>\<^sub>\<infinity>x. P x" and "\<forall>\<^sub>\<infinity>x. P x \<longrightarrow> Q x"
  shows "\<forall>\<^sub>\<infinity>x. Q x"
proof -
  have "\<forall>\<^sub>\<infinity>x. P x \<and> (P x \<longrightarrow> Q x)"
    using assms by (rule MOST_conjI)
  thus ?thesis by (rule MOST_mono) simp
qed

lemma MOST_imp_iff:
  assumes "MOST x. P x"
  shows "(MOST x. P x \<longrightarrow> Q x) \<longleftrightarrow> (MOST x. Q x)"
proof
  assume "MOST x. P x \<longrightarrow> Q x"
  with assms show "MOST x. Q x" by (rule MOST_rev_mp)
next
  assume "MOST x. Q x"
  then show "MOST x. P x \<longrightarrow> Q x" by (rule MOST_mono) simp
qed

lemma INFM_MOST_simps [simp]:
  "\<And>P Q. (INFM x. P x \<and> Q) \<longleftrightarrow> (INFM x. P x) \<and> Q"
  "\<And>P Q. (INFM x. P \<and> Q x) \<longleftrightarrow> P \<and> (INFM x. Q x)"
  "\<And>P Q. (MOST x. P x \<or> Q) \<longleftrightarrow> (MOST x. P x) \<or> Q"
  "\<And>P Q. (MOST x. P \<or> Q x) \<longleftrightarrow> P \<or> (MOST x. Q x)"
  "\<And>P Q. (MOST x. P x \<longrightarrow> Q) \<longleftrightarrow> ((INFM x. P x) \<longrightarrow> Q)"
  "\<And>P Q. (MOST x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (MOST x. Q x))"
  unfolding Alm_all_def Inf_many_def
  by (simp_all add: Collect_conj_eq)

text {* Properties of quantifiers with injective functions. *}

lemma INFM_inj: "INFM x. P (f x) \<Longrightarrow> inj f \<Longrightarrow> INFM x. P x"
  unfolding INFM_iff_infinite
  apply clarify
  apply (drule (1) finite_vimageI)
  apply simp
  done

lemma MOST_inj: "MOST x. P x \<Longrightarrow> inj f \<Longrightarrow> MOST x. P (f x)"
  unfolding MOST_iff_cofinite
  apply (drule (1) finite_vimageI)
  apply simp
  done

text {* Properties of quantifiers with singletons. *}

lemma not_INFM_eq [simp]:
  "\<not> (INFM x. x = a)"
  "\<not> (INFM x. a = x)"
  unfolding INFM_iff_infinite by simp_all

lemma MOST_neq [simp]:
  "MOST x. x \<noteq> a"
  "MOST x. a \<noteq> x"
  unfolding MOST_iff_cofinite by simp_all

lemma INFM_neq [simp]:
  "(INFM x::'a. x \<noteq> a) \<longleftrightarrow> infinite (UNIV::'a set)"
  "(INFM x::'a. a \<noteq> x) \<longleftrightarrow> infinite (UNIV::'a set)"
  unfolding INFM_iff_infinite by simp_all

lemma MOST_eq [simp]:
  "(MOST x::'a. x = a) \<longleftrightarrow> finite (UNIV::'a set)"
  "(MOST x::'a. a = x) \<longleftrightarrow> finite (UNIV::'a set)"
  unfolding MOST_iff_cofinite by simp_all

lemma MOST_eq_imp:
  "MOST x. x = a \<longrightarrow> P x"
  "MOST x. a = x \<longrightarrow> P x"
  unfolding MOST_iff_cofinite by simp_all

text {* Properties of quantifiers over the naturals. *}

lemma INFM_nat: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) \<longleftrightarrow> (\<forall>m. \<exists>n. m < n \<and> P n)"
  by (simp add: Inf_many_def infinite_nat_iff_unbounded)

lemma INFM_nat_le: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) \<longleftrightarrow> (\<forall>m. \<exists>n. m \<le> n \<and> P n)"
  by (simp add: Inf_many_def infinite_nat_iff_unbounded_le)

lemma MOST_nat: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) \<longleftrightarrow> (\<exists>m. \<forall>n. m < n \<longrightarrow> P n)"
  by (simp add: Alm_all_def INFM_nat)

lemma MOST_nat_le: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) \<longleftrightarrow> (\<exists>m. \<forall>n. m \<le> n \<longrightarrow> P n)"
  by (simp add: Alm_all_def INFM_nat_le)


subsection "Enumeration of an Infinite Set"

text {*
  The set's element type must be wellordered (e.g. the natural numbers).
*}

primrec (in wellorder) enumerate :: "'a set \<Rightarrow> nat \<Rightarrow> 'a"
where
  enumerate_0: "enumerate S 0 = (LEAST n. n \<in> S)"
| enumerate_Suc: "enumerate S (Suc n) = enumerate (S - {LEAST n. n \<in> S}) n"

lemma enumerate_Suc': "enumerate S (Suc n) = enumerate (S - {enumerate S 0}) n"
  by simp

lemma enumerate_in_set: "infinite S \<Longrightarrow> enumerate S n : S"
  apply (induct n arbitrary: S)
   apply (fastforce intro: LeastI dest!: infinite_imp_nonempty)
  apply simp
  apply (metis DiffE infinite_remove)
  done

declare enumerate_0 [simp del] enumerate_Suc [simp del]

lemma enumerate_step: "infinite S \<Longrightarrow> enumerate S n < enumerate S (Suc n)"
  apply (induct n arbitrary: S)
   apply (rule order_le_neq_trans)
    apply (simp add: enumerate_0 Least_le enumerate_in_set)
   apply (simp only: enumerate_Suc')
   apply (subgoal_tac "enumerate (S - {enumerate S 0}) 0 : S - {enumerate S 0}")
    apply (blast intro: sym)
   apply (simp add: enumerate_in_set del: Diff_iff)
  apply (simp add: enumerate_Suc')
  done

lemma enumerate_mono: "m<n \<Longrightarrow> infinite S \<Longrightarrow> enumerate S m < enumerate S n"
  apply (erule less_Suc_induct)
  apply (auto intro: enumerate_step)
  done


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
  also note enumerate_mono[of n "Suc n", OF _ `infinite S`]
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
    using enumerate_mono[OF zero_less_Suc `infinite S`, of n] `infinite S`
    apply (subst (1 2) enumerate_Suc')
    apply (subst Suc)
    using `infinite S`
    apply simp
    apply (intro arg_cong[where f = Least] ext)
    apply (auto simp: enumerate_Suc'[symmetric])
    done
qed

lemma enumerate_Ex:
  assumes S: "infinite (S::nat set)"
  shows "s \<in> S \<Longrightarrow> \<exists>n. enumerate S n = s"
proof (induct s rule: less_induct)
  case (less s)
  show ?case
  proof cases
    let ?y = "Max {s'\<in>S. s' < s}"
    assume "\<exists>y\<in>S. y < s"
    then have y: "\<And>x. ?y < x \<longleftrightarrow> (\<forall>s'\<in>S. s' < s \<longrightarrow> s' < x)"
      by (subst Max_less_iff) auto
    then have y_in: "?y \<in> {s'\<in>S. s' < s}"
      by (intro Max_in) auto
    with less.hyps[of ?y] obtain n where "enumerate S n = ?y"
      by auto
    with S have "enumerate S (Suc n) = s"
      by (auto simp: y less enumerate_Suc'' intro!: Least_equality)
    then show ?case by auto
  next
    assume *: "\<not> (\<exists>y\<in>S. y < s)"
    then have "\<forall>t\<in>S. s \<le> t" by auto
    with `s \<in> S` show ?thesis
      by (auto intro!: exI[of _ 0] Least_equality simp: enumerate_0)
  qed
qed

lemma bij_enumerate:
  fixes S :: "nat set"
  assumes S: "infinite S"
  shows "bij_betw (enumerate S) UNIV S"
proof -
  have "\<And>n m. n \<noteq> m \<Longrightarrow> enumerate S n \<noteq> enumerate S m"
    using enumerate_mono[OF _ `infinite S`] by (auto simp: neq_iff)
  then have "inj (enumerate S)"
    by (auto simp: inj_on_def)
  moreover have "\<forall>s \<in> S. \<exists>i. enumerate S i = s"
    using enumerate_Ex[OF S] by auto
  moreover note `infinite S`
  ultimately show ?thesis
    unfolding bij_betw_def by (auto intro: enumerate_in_set)
qed

subsection "Miscellaneous"

text {*
  A few trivial lemmas about sets that contain at most one element.
  These simplify the reasoning about deterministic automata.
*}

definition atmost_one :: "'a set \<Rightarrow> bool"
  where "atmost_one S \<longleftrightarrow> (\<forall>x y. x\<in>S \<and> y\<in>S \<longrightarrow> x = y)"

lemma atmost_one_empty: "S = {} \<Longrightarrow> atmost_one S"
  by (simp add: atmost_one_def)

lemma atmost_one_singleton: "S = {x} \<Longrightarrow> atmost_one S"
  by (simp add: atmost_one_def)

lemma atmost_one_unique [elim]: "atmost_one S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> y = x"
  by (simp add: atmost_one_def)

end


(*  Title:      HOL/Library/Infinite_Set.thy
    Author:     Stephan Merz
*)

header {* Infinite Sets and Related Concepts *}

theory Infinite_Set
imports Main
begin

subsection "Infinite Sets"

text {*
  Some elementary facts about infinite sets, mostly by Stefan Merz.
  Beware! Because "infinite" merely abbreviates a negation, these
  lemmas may not work well with @{text "blast"}.
*}

abbreviation
  infinite :: "'a set \<Rightarrow> bool" where
  "infinite S == \<not> finite S"

text {*
  Infinite sets are non-empty, and if we remove some elements from an
  infinite set, the result is still infinite.
*}

lemma infinite_imp_nonempty: "infinite S ==> S \<noteq> {}"
  by auto

lemma infinite_remove:
  "infinite S \<Longrightarrow> infinite (S - {a})"
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

lemma finite_nat_bounded:
  assumes S: "finite (S::nat set)"
  shows "\<exists>k. S \<subseteq> {..<k}"  (is "\<exists>k. ?bounded S k")
using S
proof induct
  have "?bounded {} 0" by simp
  then show "\<exists>k. ?bounded {} k" ..
next
  fix S x
  assume "\<exists>k. ?bounded S k"
  then obtain k where k: "?bounded S k" ..
  show "\<exists>k. ?bounded (insert x S) k"
  proof (cases "x < k")
    case True
    with k show ?thesis by auto
  next
    case False
    with k have "?bounded S (Suc x)" by auto
    then show ?thesis by auto
  qed
qed

lemma finite_nat_iff_bounded:
  "finite (S::nat set) = (\<exists>k. S \<subseteq> {..<k})"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs by (rule finite_nat_bounded)
next
  assume ?rhs
  then obtain k where "S \<subseteq> {..<k}" ..
  then show "finite S"
    by (rule finite_subset) simp
qed

lemma finite_nat_iff_bounded_le:
  "finite (S::nat set) = (\<exists>k. S \<subseteq> {..k})"  (is "?lhs = ?rhs")
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

lemma infinite_nat_iff_unbounded:
  "infinite (S::nat set) = (\<forall>m. \<exists>n. m<n \<and> n\<in>S)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof (rule ccontr)
    assume "\<not> ?rhs"
    then obtain m where m: "\<forall>n. m<n \<longrightarrow> n\<notin>S" by blast
    then have "S \<subseteq> {..m}"
      by (auto simp add: sym [OF linorder_not_less])
    with `?lhs` show False
      by (simp add: finite_nat_iff_bounded_le)
  qed
next
  assume ?rhs
  show ?lhs
  proof
    assume "finite S"
    then obtain m where "S \<subseteq> {..m}"
      by (auto simp add: finite_nat_iff_bounded_le)
    then have "\<forall>n. m<n \<longrightarrow> n\<notin>S" by auto
    with `?rhs` show False by blast
  qed
qed

lemma infinite_nat_iff_unbounded_le:
  "infinite (S::nat set) = (\<forall>m. \<exists>n. m\<le>n \<and> n\<in>S)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof
    fix m
    from `?lhs` obtain n where "m<n \<and> n\<in>S"
      by (auto simp add: infinite_nat_iff_unbounded)
    then have "m\<le>n \<and> n\<in>S" by simp
    then show "\<exists>n. m \<le> n \<and> n \<in> S" ..
  qed
next
  assume ?rhs
  show ?lhs
  proof (auto simp add: infinite_nat_iff_unbounded)
    fix m
    from `?rhs` obtain n where "Suc m \<le> n \<and> n\<in>S"
      by blast
    then have "m<n \<and> n\<in>S" by simp
    then show "\<exists>n. m < n \<and> n \<in> S" ..
  qed
qed

text {*
  For a set of natural numbers to be infinite, it is enough to know
  that for any number larger than some @{text k}, there is some larger
  number that is an element of the set.
*}

lemma unbounded_k_infinite:
  assumes k: "\<forall>m. k<m \<longrightarrow> (\<exists>n. m<n \<and> n\<in>S)"
  shows "infinite (S::nat set)"
proof -
  {
    fix m have "\<exists>n. m<n \<and> n\<in>S"
    proof (cases "k<m")
      case True
      with k show ?thesis by blast
    next
      case False
      from k obtain n where "Suc k < n \<and> n\<in>S" by auto
      with False have "m<n \<and> n\<in>S" by auto
      then show ?thesis ..
    qed
  }
  then show ?thesis
    by (auto simp add: infinite_nat_iff_unbounded)
qed

(* duplicates Finite_Set.infinite_UNIV_nat *)
lemma nat_infinite: "infinite (UNIV :: nat set)"
  by (auto simp add: infinite_nat_iff_unbounded)

lemma nat_not_finite: "finite (UNIV::nat set) \<Longrightarrow> R"
  by simp

text {*
  Every infinite set contains a countable subset. More precisely we
  show that a set @{text S} is infinite if and only if there exists an
  injective function from the naturals into @{text S}.
*}

lemma range_inj_infinite:
  "inj (f::nat \<Rightarrow> 'a) \<Longrightarrow> infinite (range f)"
proof
  assume "finite (range f)" and "inj f"
  then have "finite (UNIV::nat set)"
    by (rule finite_imageD)
  then show False by simp
qed

lemma int_infinite [simp]:
  shows "infinite (UNIV::int set)"
proof -
  from inj_int have "infinite (range int)" by (rule range_inj_infinite)
  moreover 
  have "range int \<subseteq> (UNIV::int set)" by simp
  ultimately show "infinite (UNIV::int set)" by (simp add: infinite_super)
qed

text {*
  The ``only if'' direction is harder because it requires the
  construction of a sequence of pairwise different elements of an
  infinite set @{text S}. The idea is to construct a sequence of
  non-empty and infinite subsets of @{text S} obtained by successively
  removing elements of @{text S}.
*}

lemma linorder_injI:
  assumes hyp: "!!x y. x < (y::'a::linorder) ==> f x \<noteq> f y"
  shows "inj f"
proof (rule inj_onI)
  fix x y
  assume f_eq: "f x = f y"
  show "x = y"
  proof (rule linorder_cases)
    assume "x < y"
    with hyp have "f x \<noteq> f y" by blast
    with f_eq show ?thesis by simp
  next
    assume "x = y"
    then show ?thesis .
  next
    assume "y < x"
    with hyp have "f y \<noteq> f x" by blast
    with f_eq show ?thesis by simp
  qed
qed

lemma infinite_countable_subset:
  assumes inf: "infinite (S::'a set)"
  shows "\<exists>f. inj (f::nat \<Rightarrow> 'a) \<and> range f \<subseteq> S"
proof -
  def Sseq \<equiv> "nat_rec S (\<lambda>n T. T - {SOME e. e \<in> T})"
  def pick \<equiv> "\<lambda>n. (SOME e. e \<in> Sseq n)"
  have Sseq_inf: "\<And>n. infinite (Sseq n)"
  proof -
    fix n
    show "infinite (Sseq n)"
    proof (induct n)
      from inf show "infinite (Sseq 0)"
        by (simp add: Sseq_def)
    next
      fix n
      assume "infinite (Sseq n)" then show "infinite (Sseq (Suc n))"
        by (simp add: Sseq_def infinite_remove)
    qed
  qed
  have Sseq_S: "\<And>n. Sseq n \<subseteq> S"
  proof -
    fix n
    show "Sseq n \<subseteq> S"
      by (induct n) (auto simp add: Sseq_def)
  qed
  have Sseq_pick: "\<And>n. pick n \<in> Sseq n"
  proof -
    fix n
    show "pick n \<in> Sseq n"
    proof (unfold pick_def, rule someI_ex)
      from Sseq_inf have "infinite (Sseq n)" .
      then have "Sseq n \<noteq> {}" by auto
      then show "\<exists>x. x \<in> Sseq n" by auto
    qed
  qed
  with Sseq_S have rng: "range pick \<subseteq> S"
    by auto
  have pick_Sseq_gt: "\<And>n m. pick n \<notin> Sseq (n + Suc m)"
  proof -
    fix n m
    show "pick n \<notin> Sseq (n + Suc m)"
      by (induct m) (auto simp add: Sseq_def pick_def)
  qed
  have pick_pick: "\<And>n m. pick n \<noteq> pick (n + Suc m)"
  proof -
    fix n m
    from Sseq_pick have "pick (n + Suc m) \<in> Sseq (n + Suc m)" .
    moreover from pick_Sseq_gt
    have "pick n \<notin> Sseq (n + Suc m)" .
    ultimately show "pick n \<noteq> pick (n + Suc m)"
      by auto
  qed
  have inj: "inj pick"
  proof (rule linorder_injI)
    fix i j :: nat
    assume "i < j"
    show "pick i \<noteq> pick j"
    proof
      assume eq: "pick i = pick j"
      from `i < j` obtain k where "j = i + Suc k"
        by (auto simp add: less_iff_Suc_add)
      with pick_pick have "pick i \<noteq> pick j" by simp
      with eq show False by simp
    qed
  qed
  from rng inj show ?thesis by auto
qed

lemma infinite_iff_countable_subset:
    "infinite S = (\<exists>f. inj (f::nat \<Rightarrow> 'a) \<and> range f \<subseteq> S)"
  by (auto simp add: infinite_countable_subset range_inj_infinite infinite_super)

text {*
  For any function with infinite domain and finite range there is some
  element that is the image of infinitely many domain elements.  In
  particular, any infinite sequence of elements from a finite set
  contains some element that occurs infinitely often.
*}

lemma inf_img_fin_dom:
  assumes img: "finite (f`A)" and dom: "infinite A"
  shows "\<exists>y \<in> f`A. infinite (f -` {y})"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with img have "finite (UN y:f`A. f -` {y})" by blast
  moreover have "A \<subseteq> (UN y:f`A. f -` {y})" by auto
  moreover note dom
  ultimately show False by (simp add: infinite_super)
qed

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

definition
  Inf_many :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "INFM " 10) where
  "Inf_many P = infinite {x. P x}"

definition
  Alm_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "MOST " 10) where
  "Alm_all P = (\<not> (INFM x. \<not> P x))"

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
  by (erule contrapos_pp, simp)

lemma ALL_MOST: "\<forall>x. P x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. P x"
  by simp

lemma INFM_E: assumes "INFM x. P x" obtains x where "P x"
  using INFM_EX [OF assms] by (rule exE)

lemma MOST_I: assumes "\<And>x. P x" shows "MOST x. P x"
  using assms by simp

lemma INFM_mono:
  assumes inf: "\<exists>\<^sub>\<infinity>x. P x" and q: "\<And>x. P x \<Longrightarrow> Q x"
  shows "\<exists>\<^sub>\<infinity>x. Q x"
proof -
  from inf have "infinite {x. P x}" unfolding Inf_many_def .
  moreover from q have "{x. P x} \<subseteq> {x. Q x}" by auto
  ultimately show ?thesis
    by (simp add: Inf_many_def infinite_super)
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

lemma INFM_inj:
  "INFM x. P (f x) \<Longrightarrow> inj f \<Longrightarrow> INFM x. P x"
  unfolding INFM_iff_infinite
  by (clarify, drule (1) finite_vimageI, simp)

lemma MOST_inj:
  "MOST x. P x \<Longrightarrow> inj f \<Longrightarrow> MOST x. P (f x)"
  unfolding MOST_iff_cofinite
  by (drule (1) finite_vimageI, simp)

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

lemma INFM_nat: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) = (\<forall>m. \<exists>n. m<n \<and> P n)"
  by (simp add: Inf_many_def infinite_nat_iff_unbounded)

lemma INFM_nat_le: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) = (\<forall>m. \<exists>n. m\<le>n \<and> P n)"
  by (simp add: Inf_many_def infinite_nat_iff_unbounded_le)

lemma MOST_nat: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) = (\<exists>m. \<forall>n. m<n \<longrightarrow> P n)"
  by (simp add: Alm_all_def INFM_nat)

lemma MOST_nat_le: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) = (\<exists>m. \<forall>n. m\<le>n \<longrightarrow> P n)"
  by (simp add: Alm_all_def INFM_nat_le)


subsection "Enumeration of an Infinite Set"

text {*
  The set's element type must be wellordered (e.g. the natural numbers).
*}

primrec (in wellorder) enumerate :: "'a set \<Rightarrow> nat \<Rightarrow> 'a" where
    enumerate_0:   "enumerate S 0       = (LEAST n. n \<in> S)"
  | enumerate_Suc: "enumerate S (Suc n) = enumerate (S - {LEAST n. n \<in> S}) n"

lemma enumerate_Suc':
    "enumerate S (Suc n) = enumerate (S - {enumerate S 0}) n"
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


subsection "Miscellaneous"

text {*
  A few trivial lemmas about sets that contain at most one element.
  These simplify the reasoning about deterministic automata.
*}

definition
  atmost_one :: "'a set \<Rightarrow> bool" where
  "atmost_one S = (\<forall>x y. x\<in>S \<and> y\<in>S \<longrightarrow> x=y)"

lemma atmost_one_empty: "S = {} \<Longrightarrow> atmost_one S"
  by (simp add: atmost_one_def)

lemma atmost_one_singleton: "S = {x} \<Longrightarrow> atmost_one S"
  by (simp add: atmost_one_def)

lemma atmost_one_unique [elim]: "atmost_one S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> y = x"
  by (simp add: atmost_one_def)

end


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
  by (metis finite_nat_set_iff_bounded gt_ex order_less_not_sym order_less_trans)

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
proof (unfold Not_eq_iff, rule iffI)
  assume "finite ((nat \<circ> abs) ` S)"
  then have "finite (nat ` (abs ` S))"
    by (simp add: image_image cong: image_cong)
  moreover have "inj_on nat (abs ` S)"
    by (rule inj_onI) auto
  ultimately have "finite (abs ` S)"
    by (rule finite_imageD)
  then show "finite S"
    by (rule finite_image_absD)
qed simp

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

lemma infinite_split: \<comment> \<open>courtesy of Michael Schmidt\<close>
  fixes S :: "'a set"
  assumes "infinite S"
  obtains A B
    where "A \<subseteq> S" "B \<subseteq> S" "infinite A" "infinite B" "A \<inter> B = {}"
proof-
  obtain f :: "nat \<Rightarrow> 'a"
    where f_inj: "inj f" and f_img: "range f \<subseteq> S"
    using assms infinite_countable_subset by blast
  let ?A = "range (\<lambda>n. f (2*n))"
  let ?B = "range (\<lambda>n. f (2*n+1))"
  have a_inf: "infinite ?A"
    using finite_imageD[of "\<lambda>n. f (2*n)" UNIV] f_inj infinite_UNIV_nat unfolding inj_def
    by fastforce
  have b_inf: "infinite ?B"
    using finite_imageD[of "\<lambda>n. f (2*n+1)" UNIV] f_inj infinite_UNIV_nat unfolding inj_def
    by fastforce
  from f_inj have "?A \<inter> ?B = {}" unfolding inj_def disjoint_iff using double_not_eq_Suc_double
    by auto
  from that[OF _ _ a_inf b_inf this] f_img show ?thesis
    by blast
qed


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
    \<^prop>\<open>enumerate' S n = (SOME t. t \<in> s \<and> finite {s\<in>S. s < t} \<and> card {s\<in>S. s < t} = n)\<close>.
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
proof (induction n arbitrary: S)
  case 0
  then have "enumerate S 0 \<le> enumerate S (Suc 0)"
    by (simp add: enumerate_0 Least_le enumerate_in_set)
  moreover have "enumerate (S - {enumerate S 0}) 0 \<in> S - {enumerate S 0}"
    by (meson "0.prems" enumerate_in_set infinite_remove)
  then have "enumerate S 0 \<noteq> enumerate (S - {enumerate S 0}) 0"
    by auto
  ultimately show ?case
    by (simp add: enumerate_Suc')
next
  case (Suc n)
  then show ?case 
    by (simp add: enumerate_Suc')
qed

lemma enumerate_mono: "m < n \<Longrightarrow> infinite S \<Longrightarrow> enumerate S m < enumerate S n"
  by (induct m n rule: less_Suc_induct) (auto intro: enumerate_step)

lemma enumerate_mono_iff [simp]:
  "infinite S \<Longrightarrow> enumerate S m < enumerate S n \<longleftrightarrow> m < n"
  by (metis enumerate_mono less_asym less_linear)

lemma enumerate_mono_le_iff [simp]:
  "infinite S \<Longrightarrow> enumerate S m \<le> enumerate S n \<longleftrightarrow> m \<le> n"
  by (meson enumerate_mono_iff not_le)

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

lemma infinite_enumerate:
  assumes fS: "infinite S"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (\<forall>n. r n \<in> S)"
  unfolding strict_mono_def
  using enumerate_in_set[OF fS] enumerate_mono[of _ _ S] fS by blast

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
  proof (rule order.antisym)
    have S: "infinite (S - {wellorder_class.enumerate S 0})"
      using Suc by auto
    show "wellorder_class.enumerate S (Suc (Suc n)) \<le> (LEAST s. s \<in> S \<and> wellorder_class.enumerate S (Suc n) < s)"
      using enumerate_mono[OF zero_less_Suc] \<open>infinite S\<close> S
      by (smt (verit, best) LeastI_ex Suc.hyps enumerate_0 enumerate_Suc enumerate_in_set
          enumerate_step insertE insert_Diff linorder_not_less not_less_Least)
  qed (simp add: Least_le Suc.prems enumerate_in_set)
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

lemma inj_enumerate:
  fixes S :: "'a::wellorder set"
  assumes S: "infinite S"
  shows "inj (enumerate S)"
  unfolding inj_on_def
proof clarsimp
  show "\<And>x y. enumerate S x = enumerate S y \<Longrightarrow> x = y"
    by (metis neq_iff enumerate_mono[OF _ \<open>infinite S\<close>]) 
qed

text \<open>To generalise this, we'd need a condition that all initial segments were finite\<close>
lemma bij_enumerate:
  fixes S :: "nat set"
  assumes S: "infinite S"
  shows "bij_betw (enumerate S) UNIV S"
proof -
  have "\<forall>s \<in> S. \<exists>i. enumerate S i = s"
    using enumerate_Ex[OF S] by auto
  moreover note \<open>infinite S\<close> inj_enumerate
  ultimately show ?thesis
    unfolding bij_betw_def by (auto intro: enumerate_in_set)
qed

lemma 
  fixes S :: "nat set"
  assumes S: "infinite S"
  shows range_enumerate: "range (enumerate S) = S" 
    and strict_mono_enumerate: "strict_mono (enumerate S)"
  by (auto simp add: bij_betw_imp_surj_on bij_enumerate assms strict_mono_def)

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
  have False
    using R(1)[of a] R(2)[of _ a] insert(3,4) by blast   
  thus ?case ..
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
    proof -
      have \<section>: "\<And>x. x \<in> \<F> \<and> S \<subseteq> x \<Longrightarrow> \<exists>y. y \<in> \<F> \<and> S \<subseteq> y \<and> x \<subset> y"
        using that by (blast intro: dual_order.trans psubset_imp_subset)
      show ?thesis
      proof (rule finite_transitivity_chain [of _ "\<lambda>T U. S \<subseteq> T \<and> T \<subset> U"])
      qed (use assms in \<open>auto intro: \<section>\<close>)
    qed
    with \<open>S \<in> \<F>\<close> show "\<exists>y. y \<in> {T \<in> \<F>. \<forall>U\<in>\<F>. \<not> T \<subset> U} \<and> S \<subseteq> y"
      by blast
  qed
qed

subsection \<open>Properties of @{term enumerate} on finite sets\<close>

lemma finite_enumerate_in_set: "\<lbrakk>finite S; n < card S\<rbrakk> \<Longrightarrow> enumerate S n \<in> S"
proof (induction n arbitrary: S)
  case 0
  then show ?case
    by (metis all_not_in_conv card.empty enumerate.simps(1) not_less0 wellorder_Least_lemma(1))
next
  case (Suc n)
  then have "wellorder_class.enumerate (S - {LEAST n. n \<in> S}) n \<in> S"
    by (metis Diff_empty Diff_insert0 Suc_lessD Suc_less_eq card.insert_remove
      finite_Diff insert_Diff insert_Diff_single insert_iff)
  then
  show ?case
    using Suc.prems Suc.IH [of "S - {LEAST n. n \<in> S}"]
    by (simp add: enumerate.simps)
qed

lemma finite_enumerate_step: "\<lbrakk>finite S; Suc n < card S\<rbrakk> \<Longrightarrow> enumerate S n < enumerate S (Suc n)"
proof (induction n arbitrary: S)
  case 0
  then have "enumerate S 0 \<le> enumerate S (Suc 0)"
    by (simp add: Least_le enumerate.simps(1) finite_enumerate_in_set)
  moreover have "enumerate (S - {enumerate S 0}) 0 \<in> S - {enumerate S 0}"
    by (metis 0 Suc_lessD Suc_less_eq card_Suc_Diff1 enumerate_in_set finite_enumerate_in_set)
  then have "enumerate S 0 \<noteq> enumerate (S - {enumerate S 0}) 0"
    by auto
  ultimately show ?case
    by (simp add: enumerate_Suc')
next
  case (Suc n)
  then show ?case
    by (simp add: enumerate_Suc' finite_enumerate_in_set)
qed

lemma finite_enumerate_mono: "\<lbrakk>m < n; finite S; n < card S\<rbrakk> \<Longrightarrow> enumerate S m < enumerate S n"
  by (induct m n rule: less_Suc_induct) (auto intro: finite_enumerate_step)

lemma finite_enumerate_mono_iff [simp]:
  "\<lbrakk>finite S; m < card S; n < card S\<rbrakk> \<Longrightarrow> enumerate S m < enumerate S n \<longleftrightarrow> m < n"
  by (metis finite_enumerate_mono less_asym less_linear)

lemma finite_le_enumerate:
  assumes "finite S" "n < card S"
  shows "n \<le> enumerate S n"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "n \<le> enumerate S n" by simp
  also note finite_enumerate_mono[of n "Suc n", OF _ \<open>finite S\<close>]
  finally show ?case
    using Suc.prems(2) Suc_leI by blast
qed

lemma finite_enumerate:
  assumes fS: "finite S"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono_on {..<card S} r \<and> (\<forall>n<card S. r n \<in> S)"
  unfolding strict_mono_def
  using finite_enumerate_in_set[OF fS] finite_enumerate_mono[of _ _ S] fS
  by (metis lessThan_iff strict_mono_on_def)

lemma finite_enumerate_Suc'':
  fixes S :: "'a::wellorder set"
  assumes "finite S" "Suc n < card S"
  shows "enumerate S (Suc n) = (LEAST s. s \<in> S \<and> enumerate S n < s)"
  using assms
proof (induction n arbitrary: S)
  case 0
  then have "\<forall>s \<in> S. enumerate S 0 \<le> s"
    by (auto simp: enumerate.simps intro: Least_le)
  then show ?case
    unfolding enumerate_Suc' enumerate_0[of "S - {enumerate S 0}"]
    by (metis Diff_iff dual_order.strict_iff_order singletonD singletonI)
next
  case (Suc n S)
  then have "Suc n < card (S - {enumerate S 0})"
    using Suc.prems(2) finite_enumerate_in_set by force
  then show ?case
    apply (subst (1 2) enumerate_Suc')
    apply (simp add: Suc)
    apply (intro arg_cong[where f = Least] HOL.ext)
    using finite_enumerate_mono[OF zero_less_Suc \<open>finite S\<close>, of n] Suc.prems
    by (auto simp flip: enumerate_Suc')
qed

lemma finite_enumerate_initial_segment:
  fixes S :: "'a::wellorder set"
  assumes "finite S" and n: "n < card (S \<inter> {..<s})"
  shows "enumerate (S \<inter> {..<s}) n = enumerate S n"
  using n
proof (induction n)
  case 0
  have "(LEAST n. n \<in> S \<and> n < s) = (LEAST n. n \<in> S)"
  proof (rule Least_equality)
    have "\<exists>t. t \<in> S \<and> t < s"
      by (metis "0" card_gt_0_iff disjoint_iff_not_equal lessThan_iff)
    then show "(LEAST n. n \<in> S) \<in> S \<and> (LEAST n. n \<in> S) < s"
      by (meson LeastI Least_le le_less_trans)
  qed (simp add: Least_le)
  then show ?case
    by (auto simp: enumerate_0)
next
  case (Suc n)
  then have less_card: "Suc n < card S"
    by (meson assms(1) card_mono inf_sup_ord(1) leD le_less_linear order.trans)
  obtain T where T: "T \<in> {s \<in> S. enumerate S n < s}"
    by (metis Infinite_Set.enumerate_step enumerate_in_set finite_enumerate_in_set finite_enumerate_step less_card mem_Collect_eq)
  have "(LEAST x. x \<in> S \<and> x < s \<and> enumerate S n < x) = (LEAST x. x \<in> S \<and> enumerate S n < x)"
       (is "_ = ?r")
  proof (intro Least_equality conjI)
    show "?r \<in> S"
      by (metis (mono_tags, lifting) LeastI mem_Collect_eq T)
    have "\<not> s \<le> ?r"
      using not_less_Least [of _ "\<lambda>x. x \<in> S \<and> enumerate S n < x"] Suc assms
      by (metis (mono_tags, lifting) Int_Collect Suc_lessD finite_Int finite_enumerate_in_set finite_enumerate_step lessThan_def less_le_trans)
    then show "?r < s"
      by auto
    show "enumerate S n < ?r"
      by (metis (no_types, lifting) LeastI mem_Collect_eq T)
  qed (auto simp: Least_le)
  then show ?case
    using Suc assms by (simp add: finite_enumerate_Suc'' less_card)
qed

lemma finite_enumerate_Ex:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
    and s: "s \<in> S"
  shows "\<exists>n<card S. enumerate S n = s"
  using s S
proof (induction s arbitrary: S rule: less_induct)
  case (less s)
  show ?case
  proof (cases "\<exists>y\<in>S. y < s")
    case True
    let ?T = "S \<inter> {..<s}"
    have "finite ?T"
      using less.prems(2) by blast
    have TS: "card ?T < card S"
      using less.prems by (blast intro: psubset_card_mono [OF \<open>finite S\<close>])
    from True have y: "\<And>x. Max ?T < x \<longleftrightarrow> (\<forall>s'\<in>S. s' < s \<longrightarrow> s' < x)"
      by (subst Max_less_iff) (auto simp: \<open>finite ?T\<close>)
    then have y_in: "Max ?T \<in> {s'\<in>S. s' < s}"
      using Max_in \<open>finite ?T\<close> by fastforce
    with less.IH[of "Max ?T" ?T] obtain n where n: "enumerate ?T n = Max ?T" "n < card ?T"
      using \<open>finite ?T\<close> by blast
    then have "Suc n < card S"
      using TS less_trans_Suc by blast
    with S n have "enumerate S (Suc n) = s"
      by (subst finite_enumerate_Suc'') (auto simp: y finite_enumerate_initial_segment less finite_enumerate_Suc'' intro!: Least_equality)
    then show ?thesis
      using \<open>Suc n < card S\<close> by blast
  next
    case False
    then have "\<forall>t\<in>S. s \<le> t" by auto
    moreover have "0 < card S"
      using card_0_eq less.prems by blast
    ultimately show ?thesis
      using \<open>s \<in> S\<close>
      by (auto intro!: exI[of _ 0] Least_equality simp: enumerate_0)
  qed
qed

lemma finite_enum_subset:
  assumes "\<And>i. i < card X \<Longrightarrow> enumerate X i = enumerate Y i" and "finite X" "finite Y" "card X \<le> card Y"
  shows "X \<subseteq> Y"
  by (metis assms finite_enumerate_Ex finite_enumerate_in_set less_le_trans subsetI)

lemma finite_enum_ext:
  assumes "\<And>i. i < card X \<Longrightarrow> enumerate X i = enumerate Y i" and "finite X" "finite Y" "card X = card Y"
  shows "X = Y"
  by (intro antisym finite_enum_subset) (auto simp: assms)

lemma finite_bij_enumerate:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
  shows "bij_betw (enumerate S) {..<card S} S"
proof -
  have "\<And>n m. \<lbrakk>n \<noteq> m; n < card S; m < card S\<rbrakk> \<Longrightarrow> enumerate S n \<noteq> enumerate S m"
    using finite_enumerate_mono[OF _ \<open>finite S\<close>] by (auto simp: neq_iff)
  then have "inj_on (enumerate S) {..<card S}"
    by (auto simp: inj_on_def)
  moreover have "\<forall>s \<in> S. \<exists>i<card S. enumerate S i = s"
    using finite_enumerate_Ex[OF S] by auto
  moreover note \<open>finite S\<close>
  ultimately show ?thesis
    unfolding bij_betw_def by (auto intro: finite_enumerate_in_set)
qed

lemma ex_bij_betw_strict_mono_card:
  fixes M :: "'a::wellorder set"
  assumes "finite M" 
  obtains h where "bij_betw h {..<card M} M" and "strict_mono_on {..<card M} h"
proof
  show "bij_betw (enumerate M) {..<card M} M"
    by (simp add: assms finite_bij_enumerate)
  show "strict_mono_on {..<card M} (enumerate M)"
    by (simp add: assms finite_enumerate_mono strict_mono_on_def)
qed

end

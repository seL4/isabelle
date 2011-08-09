(*  Title       : Limits.thy
    Author      : Brian Huffman
*)

header {* Filters and Limits *}

theory Limits
imports RealVector
begin

subsection {* Filters *}

text {*
  This definition also allows non-proper filters.
*}

locale is_filter =
  fixes F :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes True: "F (\<lambda>x. True)"
  assumes conj: "F (\<lambda>x. P x) \<Longrightarrow> F (\<lambda>x. Q x) \<Longrightarrow> F (\<lambda>x. P x \<and> Q x)"
  assumes mono: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> F (\<lambda>x. P x) \<Longrightarrow> F (\<lambda>x. Q x)"

typedef (open) 'a filter = "{F :: ('a \<Rightarrow> bool) \<Rightarrow> bool. is_filter F}"
proof
  show "(\<lambda>x. True) \<in> ?filter" by (auto intro: is_filter.intro)
qed

lemma is_filter_Rep_filter: "is_filter (Rep_filter A)"
  using Rep_filter [of A] by simp

lemma Abs_filter_inverse':
  assumes "is_filter F" shows "Rep_filter (Abs_filter F) = F"
  using assms by (simp add: Abs_filter_inverse)


subsection {* Eventually *}

definition eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "eventually P A \<longleftrightarrow> Rep_filter A P"

lemma eventually_Abs_filter:
  assumes "is_filter F" shows "eventually P (Abs_filter F) = F P"
  unfolding eventually_def using assms by (simp add: Abs_filter_inverse)

lemma filter_eq_iff:
  shows "A = B \<longleftrightarrow> (\<forall>P. eventually P A = eventually P B)"
  unfolding Rep_filter_inject [symmetric] fun_eq_iff eventually_def ..

lemma eventually_True [simp]: "eventually (\<lambda>x. True) A"
  unfolding eventually_def
  by (rule is_filter.True [OF is_filter_Rep_filter])

lemma always_eventually: "\<forall>x. P x \<Longrightarrow> eventually P A"
proof -
  assume "\<forall>x. P x" hence "P = (\<lambda>x. True)" by (simp add: ext)
  thus "eventually P A" by simp
qed

lemma eventually_mono:
  "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually P A \<Longrightarrow> eventually Q A"
  unfolding eventually_def
  by (rule is_filter.mono [OF is_filter_Rep_filter])

lemma eventually_conj:
  assumes P: "eventually (\<lambda>x. P x) A"
  assumes Q: "eventually (\<lambda>x. Q x) A"
  shows "eventually (\<lambda>x. P x \<and> Q x) A"
  using assms unfolding eventually_def
  by (rule is_filter.conj [OF is_filter_Rep_filter])

lemma eventually_mp:
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) A"
  assumes "eventually (\<lambda>x. P x) A"
  shows "eventually (\<lambda>x. Q x) A"
proof (rule eventually_mono)
  show "\<forall>x. (P x \<longrightarrow> Q x) \<and> P x \<longrightarrow> Q x" by simp
  show "eventually (\<lambda>x. (P x \<longrightarrow> Q x) \<and> P x) A"
    using assms by (rule eventually_conj)
qed

lemma eventually_rev_mp:
  assumes "eventually (\<lambda>x. P x) A"
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) A"
  shows "eventually (\<lambda>x. Q x) A"
using assms(2) assms(1) by (rule eventually_mp)

lemma eventually_conj_iff:
  "eventually (\<lambda>x. P x \<and> Q x) A \<longleftrightarrow> eventually P A \<and> eventually Q A"
  by (auto intro: eventually_conj elim: eventually_rev_mp)

lemma eventually_elim1:
  assumes "eventually (\<lambda>i. P i) A"
  assumes "\<And>i. P i \<Longrightarrow> Q i"
  shows "eventually (\<lambda>i. Q i) A"
  using assms by (auto elim!: eventually_rev_mp)

lemma eventually_elim2:
  assumes "eventually (\<lambda>i. P i) A"
  assumes "eventually (\<lambda>i. Q i) A"
  assumes "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "eventually (\<lambda>i. R i) A"
  using assms by (auto elim!: eventually_rev_mp)

subsection {* Finer-than relation *}

text {* @{term "A \<le> B"} means that filter @{term A} is finer than
filter @{term B}. *}

instantiation filter :: (type) complete_lattice
begin

definition le_filter_def:
  "A \<le> B \<longleftrightarrow> (\<forall>P. eventually P B \<longrightarrow> eventually P A)"

definition
  "(A :: 'a filter) < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> A"

definition
  "top = Abs_filter (\<lambda>P. \<forall>x. P x)"

definition
  "bot = Abs_filter (\<lambda>P. True)"

definition
  "sup A B = Abs_filter (\<lambda>P. eventually P A \<and> eventually P B)"

definition
  "inf A B = Abs_filter
      (\<lambda>P. \<exists>Q R. eventually Q A \<and> eventually R B \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"

definition
  "Sup S = Abs_filter (\<lambda>P. \<forall>A\<in>S. eventually P A)"

definition
  "Inf S = Sup {A::'a filter. \<forall>B\<in>S. A \<le> B}"

lemma eventually_top [simp]: "eventually P top \<longleftrightarrow> (\<forall>x. P x)"
  unfolding top_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_bot [simp]: "eventually P bot"
  unfolding bot_filter_def
  by (subst eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_sup:
  "eventually P (sup A B) \<longleftrightarrow> eventually P A \<and> eventually P B"
  unfolding sup_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma eventually_inf:
  "eventually P (inf A B) \<longleftrightarrow>
   (\<exists>Q R. eventually Q A \<and> eventually R B \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"
  unfolding inf_filter_def
  apply (rule eventually_Abs_filter, rule is_filter.intro)
  apply (fast intro: eventually_True)
  apply clarify
  apply (intro exI conjI)
  apply (erule (1) eventually_conj)
  apply (erule (1) eventually_conj)
  apply simp
  apply auto
  done

lemma eventually_Sup:
  "eventually P (Sup S) \<longleftrightarrow> (\<forall>A\<in>S. eventually P A)"
  unfolding Sup_filter_def
  apply (rule eventually_Abs_filter, rule is_filter.intro)
  apply (auto intro: eventually_conj elim!: eventually_rev_mp)
  done

instance proof
  fix A B :: "'a filter" show "A < B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> A"
    by (rule less_filter_def)
next
  fix A :: "'a filter" show "A \<le> A"
    unfolding le_filter_def by simp
next
  fix A B C :: "'a filter" assume "A \<le> B" and "B \<le> C" thus "A \<le> C"
    unfolding le_filter_def by simp
next
  fix A B :: "'a filter" assume "A \<le> B" and "B \<le> A" thus "A = B"
    unfolding le_filter_def filter_eq_iff by fast
next
  fix A :: "'a filter" show "A \<le> top"
    unfolding le_filter_def eventually_top by (simp add: always_eventually)
next
  fix A :: "'a filter" show "bot \<le> A"
    unfolding le_filter_def by simp
next
  fix A B :: "'a filter" show "A \<le> sup A B" and "B \<le> sup A B"
    unfolding le_filter_def eventually_sup by simp_all
next
  fix A B C :: "'a filter" assume "A \<le> C" and "B \<le> C" thus "sup A B \<le> C"
    unfolding le_filter_def eventually_sup by simp
next
  fix A B :: "'a filter" show "inf A B \<le> A" and "inf A B \<le> B"
    unfolding le_filter_def eventually_inf by (auto intro: eventually_True)
next
  fix A B C :: "'a filter" assume "A \<le> B" and "A \<le> C" thus "A \<le> inf B C"
    unfolding le_filter_def eventually_inf
    by (auto elim!: eventually_mono intro: eventually_conj)
next
  fix A :: "'a filter" and S assume "A \<in> S" thus "A \<le> Sup S"
    unfolding le_filter_def eventually_Sup by simp
next
  fix S and B :: "'a filter" assume "\<And>A. A \<in> S \<Longrightarrow> A \<le> B" thus "Sup S \<le> B"
    unfolding le_filter_def eventually_Sup by simp
next
  fix C :: "'a filter" and S assume "C \<in> S" thus "Inf S \<le> C"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp
next
  fix S and A :: "'a filter" assume "\<And>B. B \<in> S \<Longrightarrow> A \<le> B" thus "A \<le> Inf S"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp
qed

end

lemma filter_leD:
  "A \<le> B \<Longrightarrow> eventually P B \<Longrightarrow> eventually P A"
  unfolding le_filter_def by simp

lemma filter_leI:
  "(\<And>P. eventually P B \<Longrightarrow> eventually P A) \<Longrightarrow> A \<le> B"
  unfolding le_filter_def by simp

lemma eventually_False:
  "eventually (\<lambda>x. False) A \<longleftrightarrow> A = bot"
  unfolding filter_eq_iff by (auto elim: eventually_rev_mp)

subsection {* Map function for filters *}

definition filtermap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> 'b filter"
  where "filtermap f A = Abs_filter (\<lambda>P. eventually (\<lambda>x. P (f x)) A)"

lemma eventually_filtermap:
  "eventually P (filtermap f A) = eventually (\<lambda>x. P (f x)) A"
  unfolding filtermap_def
  apply (rule eventually_Abs_filter)
  apply (rule is_filter.intro)
  apply (auto elim!: eventually_rev_mp)
  done

lemma filtermap_ident: "filtermap (\<lambda>x. x) A = A"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_filtermap:
  "filtermap f (filtermap g A) = filtermap (\<lambda>x. f (g x)) A"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_mono: "A \<le> B \<Longrightarrow> filtermap f A \<le> filtermap f B"
  unfolding le_filter_def eventually_filtermap by simp

lemma filtermap_bot [simp]: "filtermap f bot = bot"
  by (simp add: filter_eq_iff eventually_filtermap)


subsection {* Sequentially *}

definition sequentially :: "nat filter"
  where "sequentially = Abs_filter (\<lambda>P. \<exists>k. \<forall>n\<ge>k. P n)"

lemma eventually_sequentially:
  "eventually P sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. P n)"
unfolding sequentially_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "nat \<Rightarrow> bool"
  assume "\<exists>i. \<forall>n\<ge>i. P n" and "\<exists>j. \<forall>n\<ge>j. Q n"
  then obtain i j where "\<forall>n\<ge>i. P n" and "\<forall>n\<ge>j. Q n" by auto
  then have "\<forall>n\<ge>max i j. P n \<and> Q n" by simp
  then show "\<exists>k. \<forall>n\<ge>k. P n \<and> Q n" ..
qed auto

lemma sequentially_bot [simp]: "sequentially \<noteq> bot"
  unfolding filter_eq_iff eventually_sequentially by auto

lemma eventually_False_sequentially [simp]:
  "\<not> eventually (\<lambda>n. False) sequentially"
  by (simp add: eventually_False)

lemma le_sequentially:
  "A \<le> sequentially \<longleftrightarrow> (\<forall>N. eventually (\<lambda>n. N \<le> n) A)"
  unfolding le_filter_def eventually_sequentially
  by (safe, fast, drule_tac x=N in spec, auto elim: eventually_rev_mp)


definition trivial_limit :: "'a filter \<Rightarrow> bool"
  where "trivial_limit A \<longleftrightarrow> eventually (\<lambda>x. False) A"

lemma trivial_limit_sequentially [intro]: "\<not> trivial_limit sequentially"
  by (auto simp add: trivial_limit_def eventually_sequentially)

subsection {* Standard filters *}

definition within :: "'a filter \<Rightarrow> 'a set \<Rightarrow> 'a filter" (infixr "within" 70)
  where "A within S = Abs_filter (\<lambda>P. eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) A)"

definition nhds :: "'a::topological_space \<Rightarrow> 'a filter"
  where "nhds a = Abs_filter (\<lambda>P. \<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"

definition at :: "'a::topological_space \<Rightarrow> 'a filter"
  where "at a = nhds a within - {a}"

lemma eventually_within:
  "eventually P (A within S) = eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) A"
  unfolding within_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma within_UNIV: "A within UNIV = A"
  unfolding filter_eq_iff eventually_within by simp

lemma eventually_nhds:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"
unfolding nhds_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  have "open UNIV \<and> a \<in> UNIV \<and> (\<forall>x\<in>UNIV. True)" by simp
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. True)" by - rule
next
  fix P Q
  assume "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x)"
     and "\<exists>T. open T \<and> a \<in> T \<and> (\<forall>x\<in>T. Q x)"
  then obtain S T where
    "open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x)"
    "open T \<and> a \<in> T \<and> (\<forall>x\<in>T. Q x)" by auto
  hence "open (S \<inter> T) \<and> a \<in> S \<inter> T \<and> (\<forall>x\<in>(S \<inter> T). P x \<and> Q x)"
    by (simp add: open_Int)
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x \<and> Q x)" by - rule
qed auto

lemma eventually_nhds_metric:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
unfolding eventually_nhds open_dist
apply safe
apply fast
apply (rule_tac x="{x. dist x a < d}" in exI, simp)
apply clarsimp
apply (rule_tac x="d - dist x a" in exI, clarsimp)
apply (simp only: less_diff_eq)
apply (erule le_less_trans [OF dist_triangle])
done

lemma eventually_at_topological:
  "eventually P (at a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x))"
unfolding at_def eventually_within eventually_nhds by simp

lemma eventually_at:
  fixes a :: "'a::metric_space"
  shows "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
unfolding at_def eventually_within eventually_nhds_metric by auto


subsection {* Boundedness *}

definition Bfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Bfun f A = (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) A)"

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) A" shows "Bfun f A"
unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) A"
    using K by (rule eventually_elim1, simp)
qed

lemma BfunE:
  assumes "Bfun f A"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) A"
using assms unfolding Bfun_def by fast


subsection {* Convergence to Zero *}

definition Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Zfun f A = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) A)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) A) \<Longrightarrow> Zfun f A"
  unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun f A; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) A"
  unfolding Zfun_def by simp

lemma Zfun_ssubst:
  "eventually (\<lambda>x. f x = g x) A \<Longrightarrow> Zfun g A \<Longrightarrow> Zfun f A"
  unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) A"
  unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) A = Zfun (\<lambda>x. f x) A"
  unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f A"
  assumes g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) A"
  shows "Zfun (\<lambda>x. g x) A"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>x. norm (f x) < r / K) A"
      using ZfunD [OF f] by fast
    with g show "eventually (\<lambda>x. norm (g x) < r) A"
    proof (rule eventually_elim2)
      fix x
      assume *: "norm (g x) \<le> norm (f x) * K"
      assume "norm (f x) < r / K"
      hence "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus "norm (g x) < r"
        by (simp add: order_le_less_trans [OF *])
    qed
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: not_less)
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    from g show "eventually (\<lambda>x. norm (g x) < r) A"
    proof (rule eventually_elim1)
      fix x
      assume "norm (g x) \<le> norm (f x) * K"
      also have "\<dots> \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show "norm (g x) < r"
        using `0 < r` by simp
    qed
  qed
qed

lemma Zfun_le: "\<lbrakk>Zfun g A; \<forall>x. norm (f x) \<le> norm (g x)\<rbrakk> \<Longrightarrow> Zfun f A"
  by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes f: "Zfun f A" and g: "Zfun g A"
  shows "Zfun (\<lambda>x. f x + g x) A"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) A"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) A"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) A"
  proof (rule eventually_elim2)
    fix x
    assume *: "norm (f x) < r/2" "norm (g x) < r/2"
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using * by (rule add_strict_mono)
    finally show "norm (f x + g x) < r"
      by simp
  qed
qed

lemma Zfun_minus: "Zfun f A \<Longrightarrow> Zfun (\<lambda>x. - f x) A"
  unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun f A; Zfun g A\<rbrakk> \<Longrightarrow> Zfun (\<lambda>x. f x - g x) A"
  by (simp only: diff_minus Zfun_add Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g A"
  shows "Zfun (\<lambda>x. f (g x)) A"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) A"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f A"
  assumes g: "Zfun g A"
  shows "Zfun (\<lambda>x. f x ** g x) A"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) A"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) A"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) A"
  proof (rule eventually_elim2)
    fix x
    assume *: "norm (f x) < r" "norm (g x) < inverse K"
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero * K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show "norm (f x ** g x) < r" .
  qed
qed

lemma (in bounded_bilinear) Zfun_left:
  "Zfun f A \<Longrightarrow> Zfun (\<lambda>x. f x ** a) A"
  by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun f A \<Longrightarrow> Zfun (\<lambda>x. a ** f x) A"
  by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = mult.Zfun
lemmas Zfun_mult_right = mult.Zfun_right
lemmas Zfun_mult_left = mult.Zfun_left


subsection {* Limits *}

definition tendsto :: "('a \<Rightarrow> 'b::topological_space) \<Rightarrow> 'b \<Rightarrow> 'a filter \<Rightarrow> bool"
    (infixr "--->" 55) where
  "(f ---> l) A \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) A)"

ML {*
structure Tendsto_Intros = Named_Thms
(
  val name = "tendsto_intros"
  val description = "introduction rules for tendsto"
)
*}

setup Tendsto_Intros.setup

lemma tendsto_mono: "A \<le> A' \<Longrightarrow> (f ---> l) A' \<Longrightarrow> (f ---> l) A"
  unfolding tendsto_def le_filter_def by fast

lemma topological_tendstoI:
  "(\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) A)
    \<Longrightarrow> (f ---> l) A"
  unfolding tendsto_def by auto

lemma topological_tendstoD:
  "(f ---> l) A \<Longrightarrow> open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) A"
  unfolding tendsto_def by auto

lemma tendstoI:
  assumes "\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) A"
  shows "(f ---> l) A"
  apply (rule topological_tendstoI)
  apply (simp add: open_dist)
  apply (drule (1) bspec, clarify)
  apply (drule assms)
  apply (erule eventually_elim1, simp)
  done

lemma tendstoD:
  "(f ---> l) A \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) A"
  apply (drule_tac S="{x. dist x l < e}" in topological_tendstoD)
  apply (clarsimp simp add: open_dist)
  apply (rule_tac x="e - dist x l" in exI, clarsimp)
  apply (simp only: less_diff_eq)
  apply (erule le_less_trans [OF dist_triangle])
  apply simp
  apply simp
  done

lemma tendsto_iff:
  "(f ---> l) A \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) A)"
  using tendstoI tendstoD by fast

lemma tendsto_Zfun_iff: "(f ---> a) A = Zfun (\<lambda>x. f x - a) A"
  by (simp only: tendsto_iff Zfun_def dist_norm)

lemma tendsto_ident_at [tendsto_intros]: "((\<lambda>x. x) ---> a) (at a)"
  unfolding tendsto_def eventually_at_topological by auto

lemma tendsto_ident_at_within [tendsto_intros]:
  "((\<lambda>x. x) ---> a) (at a within S)"
  unfolding tendsto_def eventually_within eventually_at_topological by auto

lemma tendsto_const [tendsto_intros]: "((\<lambda>x. k) ---> k) A"
  by (simp add: tendsto_def)

lemma tendsto_const_iff:
  fixes k l :: "'a::metric_space"
  assumes "A \<noteq> bot" shows "((\<lambda>n. k) ---> l) A \<longleftrightarrow> k = l"
  apply (safe intro!: tendsto_const)
  apply (rule ccontr)
  apply (drule_tac e="dist k l" in tendstoD)
  apply (simp add: zero_less_dist_iff)
  apply (simp add: eventually_False assms)
  done

lemma tendsto_dist [tendsto_intros]:
  assumes f: "(f ---> l) A" and g: "(g ---> m) A"
  shows "((\<lambda>x. dist (f x) (g x)) ---> dist l m) A"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  hence e2: "0 < e/2" by simp
  from tendstoD [OF f e2] tendstoD [OF g e2]
  show "eventually (\<lambda>x. dist (dist (f x) (g x)) (dist l m) < e) A"
  proof (rule eventually_elim2)
    fix x assume "dist (f x) l < e/2" "dist (g x) m < e/2"
    then show "dist (dist (f x) (g x)) (dist l m) < e"
      unfolding dist_real_def
      using dist_triangle2 [of "f x" "g x" "l"]
      using dist_triangle2 [of "g x" "l" "m"]
      using dist_triangle3 [of "l" "m" "f x"]
      using dist_triangle [of "f x" "m" "g x"]
      by arith
  qed
qed

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

lemma tendsto_norm [tendsto_intros]:
  "(f ---> a) A \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> norm a) A"
  unfolding norm_conv_dist by (intro tendsto_intros)

lemma tendsto_norm_zero:
  "(f ---> 0) A \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> 0) A"
  by (drule tendsto_norm, simp)

lemma tendsto_norm_zero_cancel:
  "((\<lambda>x. norm (f x)) ---> 0) A \<Longrightarrow> (f ---> 0) A"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_norm_zero_iff:
  "((\<lambda>x. norm (f x)) ---> 0) A \<longleftrightarrow> (f ---> 0) A"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) A; (g ---> b) A\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> a + b) A"
  by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma tendsto_minus [tendsto_intros]:
  fixes a :: "'a::real_normed_vector"
  shows "(f ---> a) A \<Longrightarrow> ((\<lambda>x. - f x) ---> - a) A"
  by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "((\<lambda>x. - f x) ---> - a) A \<Longrightarrow> (f ---> a) A"
  by (drule tendsto_minus, simp)

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) A; (g ---> b) A\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x - g x) ---> a - b) A"
  by (simp add: diff_minus tendsto_add tendsto_minus)

lemma tendsto_setsum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> a i) A"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) ---> (\<Sum>i\<in>S. a i)) A"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
  proof (induct set: finite)
    case empty show ?case
      by (simp add: tendsto_const)
  next
    case (insert i F) thus ?case
      by (simp add: tendsto_add)
  qed
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

lemma (in bounded_linear) tendsto [tendsto_intros]:
  "(g ---> a) A \<Longrightarrow> ((\<lambda>x. f (g x)) ---> f a) A"
  by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_bilinear) tendsto [tendsto_intros]:
  "\<lbrakk>(f ---> a) A; (g ---> b) A\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ** g x) ---> a ** b) A"
  by (simp only: tendsto_Zfun_iff prod_diff_prod
                 Zfun_add Zfun Zfun_left Zfun_right)


subsection {* Continuity of Inverse *}

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f A"
  assumes g: "Bfun g A"
  shows "Zfun (\<lambda>x. f x ** g x) A"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) A"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) A"
  using norm_g proof (rule eventually_elim1)
    fix x
    assume *: "norm (g x) \<le> B"
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero
                mult_nonneg_nonneg K *)
    also have "\<dots> = norm (f x) * (B * K)"
      by (rule mult_assoc)
    finally show "norm (f x ** g x) \<le> norm (f x) * (B * K)" .
  qed
  with f show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) flip:
  "bounded_bilinear (\<lambda>x y. y ** x)"
  apply default
  apply (rule add_right)
  apply (rule add_left)
  apply (rule scaleR_right)
  apply (rule scaleR_left)
  apply (subst mult_commute)
  using bounded by fast

lemma (in bounded_bilinear) Bfun_prod_Zfun:
  assumes f: "Bfun f A"
  assumes g: "Zfun g A"
  shows "Zfun (\<lambda>x. f x ** g x) A"
  using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma Bfun_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
  apply (subst nonzero_norm_inverse, clarsimp)
  apply (erule (1) le_imp_inverse_le)
  done

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) A"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) A"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  have "eventually (\<lambda>x. dist (f x) a < r) A"
    using tendstoD [OF f r1] by fast
  hence "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) A"
  proof (rule eventually_elim1)
    fix x
    assume "dist (f x) a < r"
    hence 1: "norm (f x - a) < r"
      by (simp add: dist_norm)
    hence 2: "f x \<noteq> 0" using r2 by auto
    hence "norm (inverse (f x)) = inverse (norm (f x))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r" using r2 by simp
    next
      have "norm a - norm (f x) \<le> norm (a - f x)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (f x - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (f x)" by simp
    qed
    finally show "norm (inverse (f x)) \<le> inverse (norm a - r)" .
  qed
  thus ?thesis by (rule BfunI)
qed

lemma tendsto_inverse_lemma:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>(f ---> a) A; a \<noteq> 0; eventually (\<lambda>x. f x \<noteq> 0) A\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. inverse (f x)) ---> inverse a) A"
  apply (subst tendsto_Zfun_iff)
  apply (rule Zfun_ssubst)
  apply (erule eventually_elim1)
  apply (erule (1) inverse_diff_inverse)
  apply (rule Zfun_minus)
  apply (rule Zfun_mult_left)
  apply (rule mult.Bfun_prod_Zfun)
  apply (erule (1) Bfun_inverse)
  apply (simp add: tendsto_Zfun_iff)
  done

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) A"
  assumes a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) ---> inverse a) A"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) A"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) A"
    unfolding dist_norm by (auto elim!: eventually_elim1)
  with f a show ?thesis
    by (rule tendsto_inverse_lemma)
qed

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>(f ---> a) A; (g ---> b) A; b \<noteq> 0\<rbrakk>
    \<Longrightarrow> ((\<lambda>x. f x / g x) ---> a / b) A"
  by (simp add: mult.tendsto tendsto_inverse divide_inverse)

lemma tendsto_unique:
  fixes f :: "'a \<Rightarrow> 'b::t2_space"
  assumes "\<not> trivial_limit A"  "(f ---> l) A"  "(f ---> l') A"
  shows "l = l'"
proof (rule ccontr)
  assume "l \<noteq> l'"
  obtain U V where "open U" "open V" "l \<in> U" "l' \<in> V" "U \<inter> V = {}"
    using hausdorff [OF `l \<noteq> l'`] by fast
  have "eventually (\<lambda>x. f x \<in> U) A"
    using `(f ---> l) A` `open U` `l \<in> U` by (rule topological_tendstoD)
  moreover
  have "eventually (\<lambda>x. f x \<in> V) A"
    using `(f ---> l') A` `open V` `l' \<in> V` by (rule topological_tendstoD)
  ultimately
  have "eventually (\<lambda>x. False) A"
  proof (rule eventually_elim2)
    fix x
    assume "f x \<in> U" "f x \<in> V"
    hence "f x \<in> U \<inter> V" by simp
    with `U \<inter> V = {}` show "False" by simp
  qed
  with `\<not> trivial_limit A` show "False"
    by (simp add: trivial_limit_def)
qed

end

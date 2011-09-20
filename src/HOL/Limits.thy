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

lemma is_filter_Rep_filter: "is_filter (Rep_filter F)"
  using Rep_filter [of F] by simp

lemma Abs_filter_inverse':
  assumes "is_filter F" shows "Rep_filter (Abs_filter F) = F"
  using assms by (simp add: Abs_filter_inverse)


subsection {* Eventually *}

definition eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "eventually P F \<longleftrightarrow> Rep_filter F P"

lemma eventually_Abs_filter:
  assumes "is_filter F" shows "eventually P (Abs_filter F) = F P"
  unfolding eventually_def using assms by (simp add: Abs_filter_inverse)

lemma filter_eq_iff:
  shows "F = F' \<longleftrightarrow> (\<forall>P. eventually P F = eventually P F')"
  unfolding Rep_filter_inject [symmetric] fun_eq_iff eventually_def ..

lemma eventually_True [simp]: "eventually (\<lambda>x. True) F"
  unfolding eventually_def
  by (rule is_filter.True [OF is_filter_Rep_filter])

lemma always_eventually: "\<forall>x. P x \<Longrightarrow> eventually P F"
proof -
  assume "\<forall>x. P x" hence "P = (\<lambda>x. True)" by (simp add: ext)
  thus "eventually P F" by simp
qed

lemma eventually_mono:
  "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually P F \<Longrightarrow> eventually Q F"
  unfolding eventually_def
  by (rule is_filter.mono [OF is_filter_Rep_filter])

lemma eventually_conj:
  assumes P: "eventually (\<lambda>x. P x) F"
  assumes Q: "eventually (\<lambda>x. Q x) F"
  shows "eventually (\<lambda>x. P x \<and> Q x) F"
  using assms unfolding eventually_def
  by (rule is_filter.conj [OF is_filter_Rep_filter])

lemma eventually_mp:
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  assumes "eventually (\<lambda>x. P x) F"
  shows "eventually (\<lambda>x. Q x) F"
proof (rule eventually_mono)
  show "\<forall>x. (P x \<longrightarrow> Q x) \<and> P x \<longrightarrow> Q x" by simp
  show "eventually (\<lambda>x. (P x \<longrightarrow> Q x) \<and> P x) F"
    using assms by (rule eventually_conj)
qed

lemma eventually_rev_mp:
  assumes "eventually (\<lambda>x. P x) F"
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  shows "eventually (\<lambda>x. Q x) F"
using assms(2) assms(1) by (rule eventually_mp)

lemma eventually_conj_iff:
  "eventually (\<lambda>x. P x \<and> Q x) F \<longleftrightarrow> eventually P F \<and> eventually Q F"
  by (auto intro: eventually_conj elim: eventually_rev_mp)

lemma eventually_elim1:
  assumes "eventually (\<lambda>i. P i) F"
  assumes "\<And>i. P i \<Longrightarrow> Q i"
  shows "eventually (\<lambda>i. Q i) F"
  using assms by (auto elim!: eventually_rev_mp)

lemma eventually_elim2:
  assumes "eventually (\<lambda>i. P i) F"
  assumes "eventually (\<lambda>i. Q i) F"
  assumes "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "eventually (\<lambda>i. R i) F"
  using assms by (auto elim!: eventually_rev_mp)

subsection {* Finer-than relation *}

text {* @{term "F \<le> F'"} means that filter @{term F} is finer than
filter @{term F'}. *}

instantiation filter :: (type) complete_lattice
begin

definition le_filter_def:
  "F \<le> F' \<longleftrightarrow> (\<forall>P. eventually P F' \<longrightarrow> eventually P F)"

definition
  "(F :: 'a filter) < F' \<longleftrightarrow> F \<le> F' \<and> \<not> F' \<le> F"

definition
  "top = Abs_filter (\<lambda>P. \<forall>x. P x)"

definition
  "bot = Abs_filter (\<lambda>P. True)"

definition
  "sup F F' = Abs_filter (\<lambda>P. eventually P F \<and> eventually P F')"

definition
  "inf F F' = Abs_filter
      (\<lambda>P. \<exists>Q R. eventually Q F \<and> eventually R F' \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"

definition
  "Sup S = Abs_filter (\<lambda>P. \<forall>F\<in>S. eventually P F)"

definition
  "Inf S = Sup {F::'a filter. \<forall>F'\<in>S. F \<le> F'}"

lemma eventually_top [simp]: "eventually P top \<longleftrightarrow> (\<forall>x. P x)"
  unfolding top_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_bot [simp]: "eventually P bot"
  unfolding bot_filter_def
  by (subst eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_sup:
  "eventually P (sup F F') \<longleftrightarrow> eventually P F \<and> eventually P F'"
  unfolding sup_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma eventually_inf:
  "eventually P (inf F F') \<longleftrightarrow>
   (\<exists>Q R. eventually Q F \<and> eventually R F' \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"
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
  "eventually P (Sup S) \<longleftrightarrow> (\<forall>F\<in>S. eventually P F)"
  unfolding Sup_filter_def
  apply (rule eventually_Abs_filter, rule is_filter.intro)
  apply (auto intro: eventually_conj elim!: eventually_rev_mp)
  done

instance proof
  fix F F' F'' :: "'a filter" and S :: "'a filter set"
  { show "F < F' \<longleftrightarrow> F \<le> F' \<and> \<not> F' \<le> F"
    by (rule less_filter_def) }
  { show "F \<le> F"
    unfolding le_filter_def by simp }
  { assume "F \<le> F'" and "F' \<le> F''" thus "F \<le> F''"
    unfolding le_filter_def by simp }
  { assume "F \<le> F'" and "F' \<le> F" thus "F = F'"
    unfolding le_filter_def filter_eq_iff by fast }
  { show "F \<le> top"
    unfolding le_filter_def eventually_top by (simp add: always_eventually) }
  { show "bot \<le> F"
    unfolding le_filter_def by simp }
  { show "F \<le> sup F F'" and "F' \<le> sup F F'"
    unfolding le_filter_def eventually_sup by simp_all }
  { assume "F \<le> F''" and "F' \<le> F''" thus "sup F F' \<le> F''"
    unfolding le_filter_def eventually_sup by simp }
  { show "inf F F' \<le> F" and "inf F F' \<le> F'"
    unfolding le_filter_def eventually_inf by (auto intro: eventually_True) }
  { assume "F \<le> F'" and "F \<le> F''" thus "F \<le> inf F' F''"
    unfolding le_filter_def eventually_inf
    by (auto elim!: eventually_mono intro: eventually_conj) }
  { assume "F \<in> S" thus "F \<le> Sup S"
    unfolding le_filter_def eventually_Sup by simp }
  { assume "\<And>F. F \<in> S \<Longrightarrow> F \<le> F'" thus "Sup S \<le> F'"
    unfolding le_filter_def eventually_Sup by simp }
  { assume "F'' \<in> S" thus "Inf S \<le> F''"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
  { assume "\<And>F'. F' \<in> S \<Longrightarrow> F \<le> F'" thus "F \<le> Inf S"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
qed

end

lemma filter_leD:
  "F \<le> F' \<Longrightarrow> eventually P F' \<Longrightarrow> eventually P F"
  unfolding le_filter_def by simp

lemma filter_leI:
  "(\<And>P. eventually P F' \<Longrightarrow> eventually P F) \<Longrightarrow> F \<le> F'"
  unfolding le_filter_def by simp

lemma eventually_False:
  "eventually (\<lambda>x. False) F \<longleftrightarrow> F = bot"
  unfolding filter_eq_iff by (auto elim: eventually_rev_mp)

abbreviation (input) trivial_limit :: "'a filter \<Rightarrow> bool"
  where "trivial_limit F \<equiv> F = bot"

lemma trivial_limit_def: "trivial_limit F \<longleftrightarrow> eventually (\<lambda>x. False) F"
  by (rule eventually_False [symmetric])


subsection {* Map function for filters *}

definition filtermap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> 'b filter"
  where "filtermap f F = Abs_filter (\<lambda>P. eventually (\<lambda>x. P (f x)) F)"

lemma eventually_filtermap:
  "eventually P (filtermap f F) = eventually (\<lambda>x. P (f x)) F"
  unfolding filtermap_def
  apply (rule eventually_Abs_filter)
  apply (rule is_filter.intro)
  apply (auto elim!: eventually_rev_mp)
  done

lemma filtermap_ident: "filtermap (\<lambda>x. x) F = F"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_filtermap:
  "filtermap f (filtermap g F) = filtermap (\<lambda>x. f (g x)) F"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_mono: "F \<le> F' \<Longrightarrow> filtermap f F \<le> filtermap f F'"
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

lemma sequentially_bot [simp, intro]: "sequentially \<noteq> bot"
  unfolding filter_eq_iff eventually_sequentially by auto

lemmas trivial_limit_sequentially = sequentially_bot

lemma eventually_False_sequentially [simp]:
  "\<not> eventually (\<lambda>n. False) sequentially"
  by (simp add: eventually_False)

lemma le_sequentially:
  "F \<le> sequentially \<longleftrightarrow> (\<forall>N. eventually (\<lambda>n. N \<le> n) F)"
  unfolding le_filter_def eventually_sequentially
  by (safe, fast, drule_tac x=N in spec, auto elim: eventually_rev_mp)


subsection {* Standard filters *}

definition within :: "'a filter \<Rightarrow> 'a set \<Rightarrow> 'a filter" (infixr "within" 70)
  where "F within S = Abs_filter (\<lambda>P. eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) F)"

definition (in topological_space) nhds :: "'a \<Rightarrow> 'a filter"
  where "nhds a = Abs_filter (\<lambda>P. \<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"

definition (in topological_space) at :: "'a \<Rightarrow> 'a filter"
  where "at a = nhds a within - {a}"

lemma eventually_within:
  "eventually P (F within S) = eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) F"
  unfolding within_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma within_UNIV [simp]: "F within UNIV = F"
  unfolding filter_eq_iff eventually_within by simp

lemma within_empty [simp]: "F within {} = bot"
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

lemma nhds_neq_bot [simp]: "nhds a \<noteq> bot"
  unfolding trivial_limit_def eventually_nhds by simp

lemma eventually_at_topological:
  "eventually P (at a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x))"
unfolding at_def eventually_within eventually_nhds by simp

lemma eventually_at:
  fixes a :: "'a::metric_space"
  shows "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
unfolding at_def eventually_within eventually_nhds_metric by auto

lemma at_eq_bot_iff: "at a = bot \<longleftrightarrow> open {a}"
  unfolding trivial_limit_def eventually_at_topological
  by (safe, case_tac "S = {a}", simp, fast, fast)

lemma at_neq_bot [simp]: "at (a::'a::perfect_space) \<noteq> bot"
  by (simp add: at_eq_bot_iff not_open_singleton)


subsection {* Boundedness *}

definition Bfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Bfun f F = (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) F)"

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) F" shows "Bfun f F"
unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) F"
    using K by (rule eventually_elim1, simp)
qed

lemma BfunE:
  assumes "Bfun f F"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) F"
using assms unfolding Bfun_def by fast


subsection {* Convergence to Zero *}

definition Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Zfun f F = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) F)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F) \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun f F; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F"
  unfolding Zfun_def by simp

lemma Zfun_ssubst:
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> Zfun g F \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) F"
  unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) F = Zfun (\<lambda>x. f x) F"
  unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f F"
  assumes g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F"
  shows "Zfun (\<lambda>x. g x) F"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>x. norm (f x) < r / K) F"
      using ZfunD [OF f] by fast
    with g show "eventually (\<lambda>x. norm (g x) < r) F"
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
    from g show "eventually (\<lambda>x. norm (g x) < r) F"
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

lemma Zfun_le: "\<lbrakk>Zfun g F; \<forall>x. norm (f x) \<le> norm (g x)\<rbrakk> \<Longrightarrow> Zfun f F"
  by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes f: "Zfun f F" and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x + g x) F"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) F"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) F"
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

lemma Zfun_minus: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. - f x) F"
  unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun f F; Zfun g F\<rbrakk> \<Longrightarrow> Zfun (\<lambda>x. f x - g x) F"
  by (simp only: diff_minus Zfun_add Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f (g x)) F"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) F"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) F"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) F"
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
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. f x ** a) F"
  by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. a ** f x) F"
  by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = bounded_bilinear.Zfun [OF bounded_bilinear_mult]
lemmas Zfun_mult_right = bounded_bilinear.Zfun_right [OF bounded_bilinear_mult]
lemmas Zfun_mult_left = bounded_bilinear.Zfun_left [OF bounded_bilinear_mult]


subsection {* Limits *}

definition (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" (infixr "--->" 55) where
  "(f ---> l) F \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F)"

ML {*
structure Tendsto_Intros = Named_Thms
(
  val name = "tendsto_intros"
  val description = "introduction rules for tendsto"
)
*}

setup Tendsto_Intros.setup

lemma tendsto_mono: "F \<le> F' \<Longrightarrow> (f ---> l) F' \<Longrightarrow> (f ---> l) F"
  unfolding tendsto_def le_filter_def by fast

lemma topological_tendstoI:
  "(\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F)
    \<Longrightarrow> (f ---> l) F"
  unfolding tendsto_def by auto

lemma topological_tendstoD:
  "(f ---> l) F \<Longrightarrow> open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F"
  unfolding tendsto_def by auto

lemma tendstoI:
  assumes "\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  shows "(f ---> l) F"
  apply (rule topological_tendstoI)
  apply (simp add: open_dist)
  apply (drule (1) bspec, clarify)
  apply (drule assms)
  apply (erule eventually_elim1, simp)
  done

lemma tendstoD:
  "(f ---> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  apply (drule_tac S="{x. dist x l < e}" in topological_tendstoD)
  apply (clarsimp simp add: open_dist)
  apply (rule_tac x="e - dist x l" in exI, clarsimp)
  apply (simp only: less_diff_eq)
  apply (erule le_less_trans [OF dist_triangle])
  apply simp
  apply simp
  done

lemma tendsto_iff:
  "(f ---> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  using tendstoI tendstoD by fast

lemma tendsto_Zfun_iff: "(f ---> a) F = Zfun (\<lambda>x. f x - a) F"
  by (simp only: tendsto_iff Zfun_def dist_norm)

lemma tendsto_bot [simp]: "(f ---> a) bot"
  unfolding tendsto_def by simp

lemma tendsto_ident_at [tendsto_intros]: "((\<lambda>x. x) ---> a) (at a)"
  unfolding tendsto_def eventually_at_topological by auto

lemma tendsto_ident_at_within [tendsto_intros]:
  "((\<lambda>x. x) ---> a) (at a within S)"
  unfolding tendsto_def eventually_within eventually_at_topological by auto

lemma tendsto_const [tendsto_intros]: "((\<lambda>x. k) ---> k) F"
  by (simp add: tendsto_def)

lemma tendsto_unique:
  fixes f :: "'a \<Rightarrow> 'b::t2_space"
  assumes "\<not> trivial_limit F" and "(f ---> a) F" and "(f ---> b) F"
  shows "a = b"
proof (rule ccontr)
  assume "a \<noteq> b"
  obtain U V where "open U" "open V" "a \<in> U" "b \<in> V" "U \<inter> V = {}"
    using hausdorff [OF `a \<noteq> b`] by fast
  have "eventually (\<lambda>x. f x \<in> U) F"
    using `(f ---> a) F` `open U` `a \<in> U` by (rule topological_tendstoD)
  moreover
  have "eventually (\<lambda>x. f x \<in> V) F"
    using `(f ---> b) F` `open V` `b \<in> V` by (rule topological_tendstoD)
  ultimately
  have "eventually (\<lambda>x. False) F"
  proof (rule eventually_elim2)
    fix x
    assume "f x \<in> U" "f x \<in> V"
    hence "f x \<in> U \<inter> V" by simp
    with `U \<inter> V = {}` show "False" by simp
  qed
  with `\<not> trivial_limit F` show "False"
    by (simp add: trivial_limit_def)
qed

lemma tendsto_const_iff:
  fixes a b :: "'a::t2_space"
  assumes "\<not> trivial_limit F" shows "((\<lambda>x. a) ---> b) F \<longleftrightarrow> a = b"
  by (safe intro!: tendsto_const tendsto_unique [OF assms tendsto_const])

lemma tendsto_compose:
  assumes g: "(g ---> g l) (at l)"
  assumes f: "(f ---> l) F"
  shows "((\<lambda>x. g (f x)) ---> g l) F"
proof (rule topological_tendstoI)
  fix B assume B: "open B" "g l \<in> B"
  obtain A where A: "open A" "l \<in> A"
    and gB: "\<forall>y. y \<in> A \<longrightarrow> g y \<in> B"
    using topological_tendstoD [OF g B] B(2)
    unfolding eventually_at_topological by fast
  hence "\<forall>x. f x \<in> A \<longrightarrow> g (f x) \<in> B" by simp
  from this topological_tendstoD [OF f A]
  show "eventually (\<lambda>x. g (f x) \<in> B) F"
    by (rule eventually_mono)
qed

lemma tendsto_compose_eventually:
  assumes g: "(g ---> m) (at l)"
  assumes f: "(f ---> l) F"
  assumes inj: "eventually (\<lambda>x. f x \<noteq> l) F"
  shows "((\<lambda>x. g (f x)) ---> m) F"
proof (rule topological_tendstoI)
  fix B assume B: "open B" "m \<in> B"
  obtain A where A: "open A" "l \<in> A"
    and gB: "\<And>y. y \<in> A \<Longrightarrow> y \<noteq> l \<Longrightarrow> g y \<in> B"
    using topological_tendstoD [OF g B]
    unfolding eventually_at_topological by fast
  show "eventually (\<lambda>x. g (f x) \<in> B) F"
    using topological_tendstoD [OF f A] inj
    by (rule eventually_elim2) (simp add: gB)
qed

lemma metric_tendsto_imp_tendsto:
  assumes f: "(f ---> a) F"
  assumes le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g ---> b) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

subsubsection {* Distance and norms *}

lemma tendsto_dist [tendsto_intros]:
  assumes f: "(f ---> l) F" and g: "(g ---> m) F"
  shows "((\<lambda>x. dist (f x) (g x)) ---> dist l m) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  hence e2: "0 < e/2" by simp
  from tendstoD [OF f e2] tendstoD [OF g e2]
  show "eventually (\<lambda>x. dist (dist (f x) (g x)) (dist l m) < e) F"
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
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> norm a) F"
  unfolding norm_conv_dist by (intro tendsto_intros)

lemma tendsto_norm_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> 0) F"
  by (drule tendsto_norm, simp)

lemma tendsto_norm_zero_cancel:
  "((\<lambda>x. norm (f x)) ---> 0) F \<Longrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_norm_zero_iff:
  "((\<lambda>x. norm (f x)) ---> 0) F \<longleftrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_rabs [tendsto_intros]:
  "(f ---> (l::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> \<bar>l\<bar>) F"
  by (fold real_norm_def, rule tendsto_norm)

lemma tendsto_rabs_zero:
  "(f ---> (0::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero)

lemma tendsto_rabs_zero_cancel:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<Longrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_cancel)

lemma tendsto_rabs_zero_iff:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<longleftrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_iff)

subsubsection {* Addition and subtraction *}

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> a + b) F"
  by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma tendsto_add_zero:
  fixes f g :: "'a::type \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>(f ---> 0) F; (g ---> 0) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> 0) F"
  by (drule (1) tendsto_add, simp)

lemma tendsto_minus [tendsto_intros]:
  fixes a :: "'a::real_normed_vector"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. - f x) ---> - a) F"
  by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "((\<lambda>x. - f x) ---> - a) F \<Longrightarrow> (f ---> a) F"
  by (drule tendsto_minus, simp)

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x - g x) ---> a - b) F"
  by (simp add: diff_minus tendsto_add tendsto_minus)

lemma tendsto_setsum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> a i) F"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) ---> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_add)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

subsubsection {* Linear operators and multiplication *}

lemma (in bounded_linear) tendsto:
  "(g ---> a) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> f a) F"
  by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_linear) tendsto_zero:
  "(g ---> 0) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> 0) F"
  by (drule tendsto, simp only: zero)

lemma (in bounded_bilinear) tendsto:
  "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ** g x) ---> a ** b) F"
  by (simp only: tendsto_Zfun_iff prod_diff_prod
                 Zfun_add Zfun Zfun_left Zfun_right)

lemma (in bounded_bilinear) tendsto_zero:
  assumes f: "(f ---> 0) F"
  assumes g: "(g ---> 0) F"
  shows "((\<lambda>x. f x ** g x) ---> 0) F"
  using tendsto [OF f g] by (simp add: zero_left)

lemma (in bounded_bilinear) tendsto_left_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. f x ** c) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) tendsto_right_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. c ** f x) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_right])

lemmas tendsto_of_real [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_of_real]

lemmas tendsto_scaleR [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_scaleR]

lemmas tendsto_mult [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_mult]

lemmas tendsto_mult_zero =
  bounded_bilinear.tendsto_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_left_zero =
  bounded_bilinear.tendsto_left_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_right_zero =
  bounded_bilinear.tendsto_right_zero [OF bounded_bilinear_mult]

lemma tendsto_power [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. f x ^ n) ---> a ^ n) F"
  by (induct n) (simp_all add: tendsto_const tendsto_mult)

lemma tendsto_setprod [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> L i) F"
  shows "((\<lambda>x. \<Prod>i\<in>S. f i x) ---> (\<Prod>i\<in>S. L i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_mult)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

subsubsection {* Inverse and division *}

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f F"
  assumes g: "Bfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) F"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) F"
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
  assumes f: "Bfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
  using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma Bfun_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
  apply (subst nonzero_norm_inverse, clarsimp)
  apply (erule (1) le_imp_inverse_le)
  done

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) F"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  have "eventually (\<lambda>x. dist (f x) a < r) F"
    using tendstoD [OF f r1] by fast
  hence "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) F"
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

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) ---> inverse a) F"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) F"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) F"
    unfolding dist_norm by (auto elim!: eventually_elim1)
  with a have "eventually (\<lambda>x. inverse (f x) - inverse a =
    - (inverse (f x) * (f x - a) * inverse a)) F"
    by (auto elim!: eventually_elim1 simp: inverse_diff_inverse)
  moreover have "Zfun (\<lambda>x. - (inverse (f x) * (f x - a) * inverse a)) F"
    by (intro Zfun_minus Zfun_mult_left
      bounded_bilinear.Bfun_prod_Zfun [OF bounded_bilinear_mult]
      Bfun_inverse [OF f a] f [unfolded tendsto_Zfun_iff])
  ultimately show ?thesis
    unfolding tendsto_Zfun_iff by (rule Zfun_ssubst)
qed

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F; b \<noteq> 0\<rbrakk>
    \<Longrightarrow> ((\<lambda>x. f x / g x) ---> a / b) F"
  by (simp add: tendsto_mult tendsto_inverse divide_inverse)

lemma tendsto_sgn [tendsto_intros]:
  fixes l :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> l) F; l \<noteq> 0\<rbrakk> \<Longrightarrow> ((\<lambda>x. sgn (f x)) ---> sgn l) F"
  unfolding sgn_div_norm by (simp add: tendsto_intros)

end

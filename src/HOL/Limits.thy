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

typedef 'a filter = "{F :: ('a \<Rightarrow> bool) \<Rightarrow> bool. is_filter F}"
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

lemma eventually_Ball_finite:
  assumes "finite A" and "\<forall>y\<in>A. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y\<in>A. P x y) net"
using assms by (induct set: finite, simp, simp add: eventually_conj)

lemma eventually_all_finite:
  fixes P :: "'a \<Rightarrow> 'b::finite \<Rightarrow> bool"
  assumes "\<And>y. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y. P x y) net"
using eventually_Ball_finite [of UNIV P] assms by simp

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

lemma eventually_subst:
  assumes "eventually (\<lambda>n. P n = Q n) F"
  shows "eventually P F = eventually Q F" (is "?L = ?R")
proof -
  from assms have "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
      and "eventually (\<lambda>x. Q x \<longrightarrow> P x) F"
    by (auto elim: eventually_elim1)
  then show ?thesis by (auto elim: eventually_elim2)
qed

ML {*
  fun eventually_elim_tac ctxt thms thm =
    let
      val thy = Proof_Context.theory_of ctxt
      val mp_thms = thms RL [@{thm eventually_rev_mp}]
      val raw_elim_thm =
        (@{thm allI} RS @{thm always_eventually})
        |> fold (fn thm1 => fn thm2 => thm2 RS thm1) mp_thms
        |> fold (fn _ => fn thm => @{thm impI} RS thm) thms
      val cases_prop = prop_of (raw_elim_thm RS thm)
      val cases = (Rule_Cases.make_common (thy, cases_prop) [(("elim", []), [])])
    in
      CASES cases (rtac raw_elim_thm 1) thm
    end
*}

method_setup eventually_elim = {*
  Scan.succeed (fn ctxt => METHOD_CASES (eventually_elim_tac ctxt))
*} "elimination of eventually quantifiers"


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

lemma filtermap_sup: "filtermap f (sup F1 F2) = sup (filtermap f F1) (filtermap f F2)"
  by (auto simp: filter_eq_iff eventually_filtermap eventually_sup)

subsection {* Order filters *}

definition at_top :: "('a::order) filter"
  where "at_top = Abs_filter (\<lambda>P. \<exists>k. \<forall>n\<ge>k. P n)"

lemma eventually_at_top_linorder: "eventually P at_top \<longleftrightarrow> (\<exists>N::'a::linorder. \<forall>n\<ge>N. P n)"
  unfolding at_top_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool"
  assume "\<exists>i. \<forall>n\<ge>i. P n" and "\<exists>j. \<forall>n\<ge>j. Q n"
  then obtain i j where "\<forall>n\<ge>i. P n" and "\<forall>n\<ge>j. Q n" by auto
  then have "\<forall>n\<ge>max i j. P n \<and> Q n" by simp
  then show "\<exists>k. \<forall>n\<ge>k. P n \<and> Q n" ..
qed auto

lemma eventually_ge_at_top:
  "eventually (\<lambda>x. (c::_::linorder) \<le> x) at_top"
  unfolding eventually_at_top_linorder by auto

lemma eventually_at_top_dense: "eventually P at_top \<longleftrightarrow> (\<exists>N::'a::dense_linorder. \<forall>n>N. P n)"
  unfolding eventually_at_top_linorder
proof safe
  fix N assume "\<forall>n\<ge>N. P n" then show "\<exists>N. \<forall>n>N. P n" by (auto intro!: exI[of _ N])
next
  fix N assume "\<forall>n>N. P n"
  moreover from gt_ex[of N] guess y ..
  ultimately show "\<exists>N. \<forall>n\<ge>N. P n" by (auto intro!: exI[of _ y])
qed

lemma eventually_gt_at_top:
  "eventually (\<lambda>x. (c::_::dense_linorder) < x) at_top"
  unfolding eventually_at_top_dense by auto

definition at_bot :: "('a::order) filter"
  where "at_bot = Abs_filter (\<lambda>P. \<exists>k. \<forall>n\<le>k. P n)"

lemma eventually_at_bot_linorder:
  fixes P :: "'a::linorder \<Rightarrow> bool" shows "eventually P at_bot \<longleftrightarrow> (\<exists>N. \<forall>n\<le>N. P n)"
  unfolding at_bot_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool"
  assume "\<exists>i. \<forall>n\<le>i. P n" and "\<exists>j. \<forall>n\<le>j. Q n"
  then obtain i j where "\<forall>n\<le>i. P n" and "\<forall>n\<le>j. Q n" by auto
  then have "\<forall>n\<le>min i j. P n \<and> Q n" by simp
  then show "\<exists>k. \<forall>n\<le>k. P n \<and> Q n" ..
qed auto

lemma eventually_le_at_bot:
  "eventually (\<lambda>x. x \<le> (c::_::linorder)) at_bot"
  unfolding eventually_at_bot_linorder by auto

lemma eventually_at_bot_dense:
  fixes P :: "'a::dense_linorder \<Rightarrow> bool" shows "eventually P at_bot \<longleftrightarrow> (\<exists>N. \<forall>n<N. P n)"
  unfolding eventually_at_bot_linorder
proof safe
  fix N assume "\<forall>n\<le>N. P n" then show "\<exists>N. \<forall>n<N. P n" by (auto intro!: exI[of _ N])
next
  fix N assume "\<forall>n<N. P n" 
  moreover from lt_ex[of N] guess y ..
  ultimately show "\<exists>N. \<forall>n\<le>N. P n" by (auto intro!: exI[of _ y])
qed

lemma eventually_gt_at_bot:
  "eventually (\<lambda>x. x < (c::_::dense_linorder)) at_bot"
  unfolding eventually_at_bot_dense by auto

subsection {* Sequentially *}

abbreviation sequentially :: "nat filter"
  where "sequentially == at_top"

lemma sequentially_def: "sequentially = Abs_filter (\<lambda>P. \<exists>k. \<forall>n\<ge>k. P n)"
  unfolding at_top_def by simp

lemma eventually_sequentially:
  "eventually P sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. P n)"
  by (rule eventually_at_top_linorder)

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

lemma eventually_sequentiallyI:
  assumes "\<And>x. c \<le> x \<Longrightarrow> P x"
  shows "eventually P sequentially"
using assms by (auto simp: eventually_sequentially)


subsection {* Standard filters *}

definition within :: "'a filter \<Rightarrow> 'a set \<Rightarrow> 'a filter" (infixr "within" 70)
  where "F within S = Abs_filter (\<lambda>P. eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) F)"

definition (in topological_space) nhds :: "'a \<Rightarrow> 'a filter"
  where "nhds a = Abs_filter (\<lambda>P. \<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"

definition (in topological_space) at :: "'a \<Rightarrow> 'a filter"
  where "at a = nhds a within - {a}"

abbreviation at_right :: "'a\<Colon>{topological_space, order} \<Rightarrow> 'a filter" where
  "at_right x \<equiv> at x within {x <..}"

abbreviation at_left :: "'a\<Colon>{topological_space, order} \<Rightarrow> 'a filter" where
  "at_left x \<equiv> at x within {..< x}"

definition at_infinity :: "'a::real_normed_vector filter" where
  "at_infinity = Abs_filter (\<lambda>P. \<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x)"

lemma eventually_within:
  "eventually P (F within S) = eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) F"
  unfolding within_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma within_UNIV [simp]: "F within UNIV = F"
  unfolding filter_eq_iff eventually_within by simp

lemma within_empty [simp]: "F within {} = bot"
  unfolding filter_eq_iff eventually_within by simp

lemma within_within_eq: "(F within S) within T = F within (S \<inter> T)"
  by (auto simp: filter_eq_iff eventually_within elim: eventually_elim1)

lemma at_within_eq: "at x within T = nhds x within (T - {x})"
  unfolding at_def within_within_eq by (simp add: ac_simps Diff_eq)

lemma within_le: "F within S \<le> F"
  unfolding le_filter_def eventually_within by (auto elim: eventually_elim1)

lemma le_withinI: "F \<le> F' \<Longrightarrow> eventually (\<lambda>x. x \<in> S) F \<Longrightarrow> F \<le> F' within S"
  unfolding le_filter_def eventually_within by (auto elim: eventually_elim2)

lemma le_within_iff: "eventually (\<lambda>x. x \<in> S) F \<Longrightarrow> F \<le> F' within S \<longleftrightarrow> F \<le> F'"
  by (blast intro: within_le le_withinI order_trans)

lemma eventually_nhds:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"
unfolding nhds_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  have "open UNIV \<and> a \<in> UNIV \<and> (\<forall>x\<in>UNIV. True)" by simp
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. True)" ..
next
  fix P Q
  assume "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x)"
     and "\<exists>T. open T \<and> a \<in> T \<and> (\<forall>x\<in>T. Q x)"
  then obtain S T where
    "open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x)"
    "open T \<and> a \<in> T \<and> (\<forall>x\<in>T. Q x)" by auto
  hence "open (S \<inter> T) \<and> a \<in> S \<inter> T \<and> (\<forall>x\<in>(S \<inter> T). P x \<and> Q x)"
    by (simp add: open_Int)
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x \<and> Q x)" ..
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

lemma eventually_within_less: (* COPY FROM Topo/eventually_within *)
  "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
  unfolding eventually_within eventually_at dist_nz by auto

lemma eventually_within_le: (* COPY FROM Topo/eventually_within_le *)
  "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a <= d \<longrightarrow> P x)"
  unfolding eventually_within_less by auto (metis dense order_le_less_trans)

lemma at_eq_bot_iff: "at a = bot \<longleftrightarrow> open {a}"
  unfolding trivial_limit_def eventually_at_topological
  by (safe, case_tac "S = {a}", simp, fast, fast)

lemma at_neq_bot [simp]: "at (a::'a::perfect_space) \<noteq> bot"
  by (simp add: at_eq_bot_iff not_open_singleton)

lemma trivial_limit_at_left_real [simp]: (* maybe generalize type *)
  "\<not> trivial_limit (at_left (x::real))"
  unfolding trivial_limit_def eventually_within_le
  apply clarsimp
  apply (rule_tac x="x - d/2" in bexI)
  apply (auto simp: dist_real_def)
  done

lemma trivial_limit_at_right_real [simp]: (* maybe generalize type *)
  "\<not> trivial_limit (at_right (x::real))"
  unfolding trivial_limit_def eventually_within_le
  apply clarsimp
  apply (rule_tac x="x + d/2" in bexI)
  apply (auto simp: dist_real_def)
  done

lemma eventually_at_infinity:
  "eventually P at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> P x)"
unfolding at_infinity_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool"
  assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<exists>s. \<forall>x. s \<le> norm x \<longrightarrow> Q x"
  then obtain r s where
    "\<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<forall>x. s \<le> norm x \<longrightarrow> Q x" by auto
  then have "\<forall>x. max r s \<le> norm x \<longrightarrow> P x \<and> Q x" by simp
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x \<and> Q x" ..
qed auto

lemma at_infinity_eq_at_top_bot:
  "(at_infinity \<Colon> real filter) = sup at_top at_bot"
  unfolding sup_filter_def at_infinity_def eventually_at_top_linorder eventually_at_bot_linorder
proof (intro arg_cong[where f=Abs_filter] ext iffI)
  fix P :: "real \<Rightarrow> bool" assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
  then guess r ..
  then have "(\<forall>x\<ge>r. P x) \<and> (\<forall>x\<le>-r. P x)" by auto
  then show "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)" by auto
next
  fix P :: "real \<Rightarrow> bool" assume "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)"
  then obtain p q where "\<forall>x\<ge>p. P x" "\<forall>x\<le>q. P x" by auto
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
    by (intro exI[of _ "max p (-q)"])
       (auto simp: abs_real_def)
qed

lemma at_top_le_at_infinity:
  "at_top \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

lemma at_bot_le_at_infinity:
  "at_bot \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

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
    proof eventually_elim
      case (elim x)
      hence "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus ?case
        by (simp add: order_le_less_trans [OF elim(1)])
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
    proof eventually_elim
      case (elim x)
      also have "norm (f x) * K \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show ?case
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
  proof eventually_elim
    case (elim x)
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using elim by (rule add_strict_mono)
    finally show ?case
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
  proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero elim K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show ?case .
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

definition filterlim :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b filter \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "filterlim f F2 F1 \<longleftrightarrow> filtermap f F1 \<le> F2"

syntax
  "_LIM" :: "pttrns \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(3LIM (_)/ (_)./ (_) :> (_))" [1000, 10, 0, 10] 10)

translations
  "LIM x F1. f :> F2"   == "CONST filterlim (%x. f) F2 F1"

lemma filterlim_iff:
  "(LIM x F1. f x :> F2) \<longleftrightarrow> (\<forall>P. eventually P F2 \<longrightarrow> eventually (\<lambda>x. P (f x)) F1)"
  unfolding filterlim_def le_filter_def eventually_filtermap ..

lemma filterlim_compose:
  "filterlim g F3 F2 \<Longrightarrow> filterlim f F2 F1 \<Longrightarrow> filterlim (\<lambda>x. g (f x)) F3 F1"
  unfolding filterlim_def filtermap_filtermap[symmetric] by (metis filtermap_mono order_trans)

lemma filterlim_mono:
  "filterlim f F2 F1 \<Longrightarrow> F2 \<le> F2' \<Longrightarrow> F1' \<le> F1 \<Longrightarrow> filterlim f F2' F1'"
  unfolding filterlim_def by (metis filtermap_mono order_trans)

lemma filterlim_ident: "LIM x F. x :> F"
  by (simp add: filterlim_def filtermap_ident)

lemma filterlim_cong:
  "F1 = F1' \<Longrightarrow> F2 = F2' \<Longrightarrow> eventually (\<lambda>x. f x = g x) F2 \<Longrightarrow> filterlim f F1 F2 = filterlim g F1' F2'"
  by (auto simp: filterlim_def le_filter_def eventually_filtermap elim: eventually_elim2)

lemma filterlim_within:
  "(LIM x F1. f x :> F2 within S) \<longleftrightarrow> (eventually (\<lambda>x. f x \<in> S) F1 \<and> (LIM x F1. f x :> F2))"
  unfolding filterlim_def
proof safe
  assume "filtermap f F1 \<le> F2 within S" then show "eventually (\<lambda>x. f x \<in> S) F1"
    by (auto simp: le_filter_def eventually_filtermap eventually_within elim!: allE[of _ "\<lambda>x. x \<in> S"])
qed (auto intro: within_le order_trans simp: le_within_iff eventually_filtermap)

lemma filterlim_filtermap: "filterlim f F1 (filtermap g F2) = filterlim (\<lambda>x. f (g x)) F1 F2"
  unfolding filterlim_def filtermap_filtermap ..

lemma filterlim_sup:
  "filterlim f F F1 \<Longrightarrow> filterlim f F F2 \<Longrightarrow> filterlim f F (sup F1 F2)"
  unfolding filterlim_def filtermap_sup by auto

lemma filterlim_Suc: "filterlim Suc sequentially sequentially"
  by (simp add: filterlim_iff eventually_sequentially) (metis le_Suc_eq)

abbreviation (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" (infixr "--->" 55) where
  "(f ---> l) F \<equiv> filterlim f (nhds l) F"

ML {*
structure Tendsto_Intros = Named_Thms
(
  val name = @{binding tendsto_intros}
  val description = "introduction rules for tendsto"
)
*}

setup Tendsto_Intros.setup

lemma tendsto_def: "(f ---> l) F \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F)"
  unfolding filterlim_def
proof safe
  fix S assume "open S" "l \<in> S" "filtermap f F \<le> nhds l"
  then show "eventually (\<lambda>x. f x \<in> S) F"
    unfolding eventually_nhds eventually_filtermap le_filter_def
    by (auto elim!: allE[of _ "\<lambda>x. x \<in> S"] eventually_rev_mp)
qed (auto elim!: eventually_rev_mp simp: eventually_nhds eventually_filtermap le_filter_def)

lemma filterlim_at:
  "(LIM x F. f x :> at b) \<longleftrightarrow> (eventually (\<lambda>x. f x \<noteq> b) F \<and> (f ---> b) F)"
  by (simp add: at_def filterlim_within)

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
  proof eventually_elim
    case (elim x)
    hence "f x \<in> U \<inter> V" by simp
    with `U \<inter> V = {}` show ?case by simp
  qed
  with `\<not> trivial_limit F` show "False"
    by (simp add: trivial_limit_def)
qed

lemma tendsto_const_iff:
  fixes a b :: "'a::t2_space"
  assumes "\<not> trivial_limit F" shows "((\<lambda>x. a) ---> b) F \<longleftrightarrow> a = b"
  by (safe intro!: tendsto_const tendsto_unique [OF assms tendsto_const])

lemma tendsto_at_iff_tendsto_nhds:
  "(g ---> g l) (at l) \<longleftrightarrow> (g ---> g l) (nhds l)"
  unfolding tendsto_def at_def eventually_within
  by (intro ext all_cong imp_cong) (auto elim!: eventually_elim1)

lemma tendsto_compose:
  "(g ---> g l) (at l) \<Longrightarrow> (f ---> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) ---> g l) F"
  unfolding tendsto_at_iff_tendsto_nhds by (rule filterlim_compose[of g])

lemma tendsto_compose_eventually:
  "(g ---> m) (at l) \<Longrightarrow> (f ---> l) F \<Longrightarrow> eventually (\<lambda>x. f x \<noteq> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) ---> m) F"
  by (rule filterlim_compose[of g _ "at l"]) (auto simp add: filterlim_at)

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
  proof (eventually_elim)
    case (elim x)
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

lemma tendsto_minus_cancel_left:
    "(f ---> - (y::_::real_normed_vector)) F \<longleftrightarrow> ((\<lambda>x. - f x) ---> y) F"
  using tendsto_minus_cancel[of f "- y" F]  tendsto_minus[of f "- y" F]
  by auto

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

lemma real_tendsto_sandwich:
  fixes f g h :: "'a \<Rightarrow> real"
  assumes ev: "eventually (\<lambda>n. f n \<le> g n) net" "eventually (\<lambda>n. g n \<le> h n) net"
  assumes lim: "(f ---> c) net" "(h ---> c) net"
  shows "(g ---> c) net"
proof -
  have "((\<lambda>n. g n - f n) ---> 0) net"
  proof (rule metric_tendsto_imp_tendsto)
    show "eventually (\<lambda>n. dist (g n - f n) 0 \<le> dist (h n - f n) 0) net"
      using ev by (rule eventually_elim2) (simp add: dist_real_def)
    show "((\<lambda>n. h n - f n) ---> 0) net"
      using tendsto_diff[OF lim(2,1)] by simp
  qed
  from tendsto_add[OF this lim(1)] show ?thesis by simp
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

lemma tendsto_le_const:
  fixes f :: "_ \<Rightarrow> real" 
  assumes F: "\<not> trivial_limit F"
  assumes x: "(f ---> x) F" and a: "eventually (\<lambda>x. a \<le> f x) F"
  shows "a \<le> x"
proof (rule ccontr)
  assume "\<not> a \<le> x"
  with x have "eventually (\<lambda>x. f x < a) F"
    by (auto simp add: tendsto_def elim!: allE[of _ "{..< a}"])
  with a have "eventually (\<lambda>x. False) F"
    by eventually_elim auto
  with F show False
    by (simp add: eventually_False)
qed

lemma tendsto_le:
  fixes f g :: "_ \<Rightarrow> real" 
  assumes F: "\<not> trivial_limit F"
  assumes x: "(f ---> x) F" and y: "(g ---> y) F"
  assumes ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
  using tendsto_le_const[OF F tendsto_diff[OF x y], of 0] ev
  by (simp add: sign_simps)

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
  using norm_g proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero
                mult_nonneg_nonneg K elim)
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
  proof eventually_elim
    case (elim x)
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

subsection {* Limits to @{const at_top} and @{const at_bot} *}

lemma filterlim_at_top:
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. Z \<le> f x) F)"
  by (auto simp: filterlim_iff eventually_at_top_linorder elim!: eventually_elim1)

lemma filterlim_at_top_dense:
  fixes f :: "'a \<Rightarrow> ('b::dense_linorder)"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. Z < f x) F)"
  by (metis eventually_elim1[of _ F] eventually_gt_at_top order_less_imp_le
            filterlim_at_top[of f F] filterlim_iff[of f at_top F])

lemma filterlim_at_top_ge:
  fixes f :: "'a \<Rightarrow> ('b::linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z\<ge>c. eventually (\<lambda>x. Z \<le> f x) F)"
  unfolding filterlim_at_top
proof safe
  fix Z assume *: "\<forall>Z\<ge>c. eventually (\<lambda>x. Z \<le> f x) F"
  with *[THEN spec, of "max Z c"] show "eventually (\<lambda>x. Z \<le> f x) F"
    by (auto elim!: eventually_elim1)
qed simp

lemma filterlim_at_top_at_top:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  assumes bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
  assumes Q: "eventually Q at_top"
  assumes P: "eventually P at_top"
  shows "filterlim f at_top at_top"
proof -
  from P obtain x where x: "\<And>y. x \<le> y \<Longrightarrow> P y"
    unfolding eventually_at_top_linorder by auto
  show ?thesis
  proof (intro filterlim_at_top_ge[THEN iffD2] allI impI)
    fix z assume "x \<le> z"
    with x have "P z" by auto
    have "eventually (\<lambda>x. g z \<le> x) at_top"
      by (rule eventually_ge_at_top)
    with Q show "eventually (\<lambda>x. z \<le> f x) at_top"
      by eventually_elim (metis mono bij `P z`)
  qed
qed

lemma filterlim_at_top_gt:
  fixes f :: "'a \<Rightarrow> ('b::dense_linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z>c. eventually (\<lambda>x. Z \<le> f x) F)"
  by (metis filterlim_at_top order_less_le_trans gt_ex filterlim_at_top_ge)

lemma filterlim_at_bot: 
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x \<le> Z) F)"
  by (auto simp: filterlim_iff eventually_at_bot_linorder elim!: eventually_elim1)

lemma filterlim_at_bot_le:
  fixes f :: "'a \<Rightarrow> ('b::linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z\<le>c. eventually (\<lambda>x. Z \<ge> f x) F)"
  unfolding filterlim_at_bot
proof safe
  fix Z assume *: "\<forall>Z\<le>c. eventually (\<lambda>x. Z \<ge> f x) F"
  with *[THEN spec, of "min Z c"] show "eventually (\<lambda>x. Z \<ge> f x) F"
    by (auto elim!: eventually_elim1)
qed simp

lemma filterlim_at_bot_lt:
  fixes f :: "'a \<Rightarrow> ('b::dense_linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z<c. eventually (\<lambda>x. Z \<ge> f x) F)"
  by (metis filterlim_at_bot filterlim_at_bot_le lt_ex order_le_less_trans)

lemma filterlim_at_bot_at_right:
  fixes f :: "real \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  assumes bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
  assumes Q: "eventually Q (at_right a)" and bound: "\<And>b. Q b \<Longrightarrow> a < b"
  assumes P: "eventually P at_bot"
  shows "filterlim f at_bot (at_right a)"
proof -
  from P obtain x where x: "\<And>y. y \<le> x \<Longrightarrow> P y"
    unfolding eventually_at_bot_linorder by auto
  show ?thesis
  proof (intro filterlim_at_bot_le[THEN iffD2] allI impI)
    fix z assume "z \<le> x"
    with x have "P z" by auto
    have "eventually (\<lambda>x. x \<le> g z) (at_right a)"
      using bound[OF bij(2)[OF `P z`]]
      by (auto simp add: eventually_within_less dist_real_def intro!:  exI[of _ "g z - a"])
    with Q show "eventually (\<lambda>x. f x \<le> z) (at_right a)"
      by eventually_elim (metis bij `P z` mono)
  qed
qed

lemma filterlim_at_top_at_left:
  fixes f :: "real \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  assumes bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
  assumes Q: "eventually Q (at_left a)" and bound: "\<And>b. Q b \<Longrightarrow> b < a"
  assumes P: "eventually P at_top"
  shows "filterlim f at_top (at_left a)"
proof -
  from P obtain x where x: "\<And>y. x \<le> y \<Longrightarrow> P y"
    unfolding eventually_at_top_linorder by auto
  show ?thesis
  proof (intro filterlim_at_top_ge[THEN iffD2] allI impI)
    fix z assume "x \<le> z"
    with x have "P z" by auto
    have "eventually (\<lambda>x. g z \<le> x) (at_left a)"
      using bound[OF bij(2)[OF `P z`]]
      by (auto simp add: eventually_within_less dist_real_def intro!:  exI[of _ "a - g z"])
    with Q show "eventually (\<lambda>x. z \<le> f x) (at_left a)"
      by eventually_elim (metis bij `P z` mono)
  qed
qed

lemma filterlim_at_infinity:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>real_normed_vector"
  assumes "0 \<le> c"
  shows "(LIM x F. f x :> at_infinity) \<longleftrightarrow> (\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F)"
  unfolding filterlim_iff eventually_at_infinity
proof safe
  fix P :: "'a \<Rightarrow> bool" and b
  assume *: "\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F"
    and P: "\<forall>x. b \<le> norm x \<longrightarrow> P x"
  have "max b (c + 1) > c" by auto
  with * have "eventually (\<lambda>x. max b (c + 1) \<le> norm (f x)) F"
    by auto
  then show "eventually (\<lambda>x. P (f x)) F"
  proof eventually_elim
    fix x assume "max b (c + 1) \<le> norm (f x)"
    with P show "P (f x)" by auto
  qed
qed force

lemma filterlim_real_sequentially: "LIM x sequentially. real x :> at_top"
  unfolding filterlim_at_top
  apply (intro allI)
  apply (rule_tac c="natceiling (Z + 1)" in eventually_sequentiallyI)
  apply (auto simp: natceiling_le_eq)
  done

subsection {* Relate @{const at}, @{const at_left} and @{const at_right} *}

text {*

This lemmas are useful for conversion between @{term "at x"} to @{term "at_left x"} and
@{term "at_right x"} and also @{term "at_right 0"}.

*}

lemma at_eq_sup_left_right: "at (x::real) = sup (at_left x) (at_right x)"
  by (auto simp: eventually_within at_def filter_eq_iff eventually_sup 
           elim: eventually_elim2 eventually_elim1)

lemma filterlim_split_at_real:
  "filterlim f F (at_left x) \<Longrightarrow> filterlim f F (at_right x) \<Longrightarrow> filterlim f F (at (x::real))"
  by (subst at_eq_sup_left_right) (rule filterlim_sup)

lemma filtermap_nhds_shift: "filtermap (\<lambda>x. x - d) (nhds a) = nhds (a - d::real)"
  unfolding filter_eq_iff eventually_filtermap eventually_nhds_metric
  by (intro allI ex_cong) (auto simp: dist_real_def field_simps)

lemma filtermap_nhds_minus: "filtermap (\<lambda>x. - x) (nhds a) = nhds (- a::real)"
  unfolding filter_eq_iff eventually_filtermap eventually_nhds_metric
  apply (intro allI ex_cong)
  apply (auto simp: dist_real_def field_simps)
  apply (erule_tac x="-x" in allE)
  apply simp
  done

lemma filtermap_at_shift: "filtermap (\<lambda>x. x - d) (at a) = at (a - d::real)"
  unfolding at_def filtermap_nhds_shift[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma filtermap_at_right_shift: "filtermap (\<lambda>x. x - d) (at_right a) = at_right (a - d::real)"
  unfolding filtermap_at_shift[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma at_right_to_0: "at_right (a::real) = filtermap (\<lambda>x. x + a) (at_right 0)"
  using filtermap_at_right_shift[of "-a" 0] by simp

lemma filterlim_at_right_to_0:
  "filterlim f F (at_right (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (x + a)) F (at_right 0)"
  unfolding filterlim_def filtermap_filtermap at_right_to_0[of a] ..

lemma eventually_at_right_to_0:
  "eventually P (at_right (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (x + a)) (at_right 0)"
  unfolding at_right_to_0[of a] by (simp add: eventually_filtermap)

lemma filtermap_at_minus: "filtermap (\<lambda>x. - x) (at a) = at (- a::real)"
  unfolding at_def filtermap_nhds_minus[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma at_left_minus: "at_left (a::real) = filtermap (\<lambda>x. - x) (at_right (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_within filtermap_at_minus[symmetric])

lemma at_right_minus: "at_right (a::real) = filtermap (\<lambda>x. - x) (at_left (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_within filtermap_at_minus[symmetric])

lemma filterlim_at_left_to_right:
  "filterlim f F (at_left (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (- x)) F (at_right (-a))"
  unfolding filterlim_def filtermap_filtermap at_left_minus[of a] ..

lemma eventually_at_left_to_right:
  "eventually P (at_left (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (- x)) (at_right (-a))"
  unfolding at_left_minus[of a] by (simp add: eventually_filtermap)

lemma filterlim_at_split:
  "filterlim f F (at (x::real)) \<longleftrightarrow> filterlim f F (at_left x) \<and> filterlim f F (at_right x)"
  by (subst at_eq_sup_left_right) (simp add: filterlim_def filtermap_sup)

lemma eventually_at_split:
  "eventually P (at (x::real)) \<longleftrightarrow> eventually P (at_left x) \<and> eventually P (at_right x)"
  by (subst at_eq_sup_left_right) (simp add: eventually_sup)

lemma at_top_mirror: "at_top = filtermap uminus (at_bot :: real filter)"
  unfolding filter_eq_iff eventually_filtermap eventually_at_top_linorder eventually_at_bot_linorder
  by (metis le_minus_iff minus_minus)

lemma at_bot_mirror: "at_bot = filtermap uminus (at_top :: real filter)"
  unfolding at_top_mirror filtermap_filtermap by (simp add: filtermap_ident)

lemma filterlim_at_top_mirror: "(LIM x at_top. f x :> F) \<longleftrightarrow> (LIM x at_bot. f (-x::real) :> F)"
  unfolding filterlim_def at_top_mirror filtermap_filtermap ..

lemma filterlim_at_bot_mirror: "(LIM x at_bot. f x :> F) \<longleftrightarrow> (LIM x at_top. f (-x::real) :> F)"
  unfolding filterlim_def at_bot_mirror filtermap_filtermap ..

lemma filterlim_uminus_at_top_at_bot: "LIM x at_bot. - x :: real :> at_top"
  unfolding filterlim_at_top eventually_at_bot_dense
  by (metis leI minus_less_iff order_less_asym)

lemma filterlim_uminus_at_bot_at_top: "LIM x at_top. - x :: real :> at_bot"
  unfolding filterlim_at_bot eventually_at_top_dense
  by (metis leI less_minus_iff order_less_asym)

lemma filterlim_uminus_at_top: "(LIM x F. f x :> at_top) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_bot)"
  using filterlim_compose[OF filterlim_uminus_at_bot_at_top, of f F]
  using filterlim_compose[OF filterlim_uminus_at_top_at_bot, of "\<lambda>x. - f x" F]
  by auto

lemma filterlim_uminus_at_bot: "(LIM x F. f x :> at_bot) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_top)"
  unfolding filterlim_uminus_at_top by simp

lemma filterlim_inverse_at_top_right: "LIM x at_right (0::real). inverse x :> at_top"
  unfolding filterlim_at_top_gt[where c=0] eventually_within at_def
proof safe
  fix Z :: real assume [arith]: "0 < Z"
  then have "eventually (\<lambda>x. x < inverse Z) (nhds 0)"
    by (auto simp add: eventually_nhds_metric dist_real_def intro!: exI[of _ "\<bar>inverse Z\<bar>"])
  then show "eventually (\<lambda>x. x \<in> - {0} \<longrightarrow> x \<in> {0<..} \<longrightarrow> Z \<le> inverse x) (nhds 0)"
    by (auto elim!: eventually_elim1 simp: inverse_eq_divide field_simps)
qed

lemma filterlim_inverse_at_top:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> LIM x F. inverse (f x) :> at_top"
  by (intro filterlim_compose[OF filterlim_inverse_at_top_right])
     (simp add: filterlim_def eventually_filtermap le_within_iff at_def eventually_elim1)

lemma filterlim_inverse_at_bot_neg:
  "LIM x (at_left (0::real)). inverse x :> at_bot"
  by (simp add: filterlim_inverse_at_top_right filterlim_uminus_at_bot filterlim_at_left_to_right)

lemma filterlim_inverse_at_bot:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. f x < 0) F \<Longrightarrow> LIM x F. inverse (f x) :> at_bot"
  unfolding filterlim_uminus_at_bot inverse_minus_eq[symmetric]
  by (rule filterlim_inverse_at_top) (simp_all add: tendsto_minus_cancel_left[symmetric])

lemma tendsto_inverse_0:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>real_normed_div_algebra"
  shows "(inverse ---> (0::'a)) at_infinity"
  unfolding tendsto_Zfun_iff diff_0_right Zfun_def eventually_at_infinity
proof safe
  fix r :: real assume "0 < r"
  show "\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> norm (inverse x :: 'a) < r"
  proof (intro exI[of _ "inverse (r / 2)"] allI impI)
    fix x :: 'a
    from `0 < r` have "0 < inverse (r / 2)" by simp
    also assume *: "inverse (r / 2) \<le> norm x"
    finally show "norm (inverse x) < r"
      using * `0 < r` by (subst nonzero_norm_inverse) (simp_all add: inverse_eq_divide field_simps)
  qed
qed

lemma at_right_to_top: "(at_right (0::real)) = filtermap inverse at_top"
proof (rule antisym)
  have "(inverse ---> (0::real)) at_top"
    by (metis tendsto_inverse_0 filterlim_mono at_top_le_at_infinity order_refl)
  then show "filtermap inverse at_top \<le> at_right (0::real)"
    unfolding at_within_eq
    by (intro le_withinI) (simp_all add: eventually_filtermap eventually_gt_at_top filterlim_def)
next
  have "filtermap inverse (filtermap inverse (at_right (0::real))) \<le> filtermap inverse at_top"
    using filterlim_inverse_at_top_right unfolding filterlim_def by (rule filtermap_mono)
  then show "at_right (0::real) \<le> filtermap inverse at_top"
    by (simp add: filtermap_ident filtermap_filtermap)
qed

lemma eventually_at_right_to_top:
  "eventually P (at_right (0::real)) \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) at_top"
  unfolding at_right_to_top eventually_filtermap ..

lemma filterlim_at_right_to_top:
  "filterlim f F (at_right (0::real)) \<longleftrightarrow> (LIM x at_top. f (inverse x) :> F)"
  unfolding filterlim_def at_right_to_top filtermap_filtermap ..

lemma at_top_to_right: "at_top = filtermap inverse (at_right (0::real))"
  unfolding at_right_to_top filtermap_filtermap inverse_inverse_eq filtermap_ident ..

lemma eventually_at_top_to_right:
  "eventually P at_top \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) (at_right (0::real))"
  unfolding at_top_to_right eventually_filtermap ..

lemma filterlim_at_top_to_right:
  "filterlim f F at_top \<longleftrightarrow> (LIM x (at_right (0::real)). f (inverse x) :> F)"
  unfolding filterlim_def at_top_to_right filtermap_filtermap ..

lemma filterlim_inverse_at_infinity:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "filterlim inverse at_infinity (at (0::'a))"
  unfolding filterlim_at_infinity[OF order_refl]
proof safe
  fix r :: real assume "0 < r"
  then show "eventually (\<lambda>x::'a. r \<le> norm (inverse x)) (at 0)"
    unfolding eventually_at norm_inverse
    by (intro exI[of _ "inverse r"])
       (auto simp: norm_conv_dist[symmetric] field_simps inverse_eq_divide)
qed

lemma filterlim_inverse_at_iff:
  fixes g :: "'a \<Rightarrow> 'b\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "(LIM x F. inverse (g x) :> at 0) \<longleftrightarrow> (LIM x F. g x :> at_infinity)"
  unfolding filterlim_def filtermap_filtermap[symmetric]
proof
  assume "filtermap g F \<le> at_infinity"
  then have "filtermap inverse (filtermap g F) \<le> filtermap inverse at_infinity"
    by (rule filtermap_mono)
  also have "\<dots> \<le> at 0"
    using tendsto_inverse_0
    by (auto intro!: le_withinI exI[of _ 1]
             simp: eventually_filtermap eventually_at_infinity filterlim_def at_def)
  finally show "filtermap inverse (filtermap g F) \<le> at 0" .
next
  assume "filtermap inverse (filtermap g F) \<le> at 0"
  then have "filtermap inverse (filtermap inverse (filtermap g F)) \<le> filtermap inverse (at 0)"
    by (rule filtermap_mono)
  with filterlim_inverse_at_infinity show "filtermap g F \<le> at_infinity"
    by (auto intro: order_trans simp: filterlim_def filtermap_filtermap)
qed

lemma tendsto_inverse_0_at_top:
  "LIM x F. f x :> at_top \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) ---> 0) F"
 by (metis at_top_le_at_infinity filterlim_at filterlim_inverse_at_iff filterlim_mono order_refl)

text {*

We only show rules for multiplication and addition when the functions are either against a real
value or against infinity. Further rules are easy to derive by using @{thm filterlim_uminus_at_top}.

*}

lemma filterlim_tendsto_pos_mult_at_top: 
  assumes f: "(f ---> c) F" and c: "0 < c"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f `0 < c` have "eventually (\<lambda>x. c / 2 < f x) F"
    by (auto dest!: tendstoD[where e="c / 2"] elim!: eventually_elim1
             simp: dist_real_def abs_real_def split: split_if_asm)
  moreover from g have "eventually (\<lambda>x. (Z / c * 2) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "c / 2 < f x" "Z / c * 2 \<le> g x"
    with `0 < Z` `0 < c` have "c / 2 * (Z / c * 2) \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    with `0 < c` show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_at_top_mult_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 1 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "1 \<le> f x" "Z \<le> g x"
    with `0 < Z` have "1 * Z \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    then show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_tendsto_pos_mult_at_bot:
  assumes "(f ---> c) F" "0 < (c::real)" "filterlim g at_bot F"
  shows "LIM x F. f x * g x :> at_bot"
  using filterlim_tendsto_pos_mult_at_top[OF assms(1,2), of "\<lambda>x. - g x"] assms(3)
  unfolding filterlim_uminus_at_bot by simp

lemma filterlim_tendsto_add_at_top: 
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. c - 1 < f x) F"
    by (auto dest!: tendstoD[where e=1] elim!: eventually_elim1 simp: dist_real_def)
  moreover from g have "eventually (\<lambda>x. Z - (c - 1) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma LIM_at_top_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "(f ---> a) F" "0 < a"
  assumes g: "(g ---> 0) F" "eventually (\<lambda>x. 0 < g x) F"
  shows "LIM x F. f x / g x :> at_top"
  unfolding divide_inverse
  by (rule filterlim_tendsto_pos_mult_at_top[OF f]) (rule filterlim_inverse_at_top[OF g])

lemma filterlim_at_top_add_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 0 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma tendsto_divide_0:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_infinity"
  shows "((\<lambda>x. f x / g x) ---> 0) F"
  using tendsto_mult[OF f filterlim_compose[OF tendsto_inverse_0 g]] by (simp add: divide_inverse)

lemma linear_plus_1_le_power:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
proof (induct n)
  case (Suc n)
  have "real (Suc n) * x + 1 \<le> (x + 1) * (real n * x + 1)"
    by (simp add: field_simps real_of_nat_Suc mult_nonneg_nonneg x)
  also have "\<dots> \<le> (x + 1)^Suc n"
    using Suc x by (simp add: mult_left_mono)
  finally show ?case .
qed simp

lemma filterlim_realpow_sequentially_gt1:
  fixes x :: "'a :: real_normed_div_algebra"
  assumes x[arith]: "1 < norm x"
  shows "LIM n sequentially. x ^ n :> at_infinity"
proof (intro filterlim_at_infinity[THEN iffD2] allI impI)
  fix y :: real assume "0 < y"
  have "0 < norm x - 1" by simp
  then obtain N::nat where "y < real N * (norm x - 1)" by (blast dest: reals_Archimedean3)
  also have "\<dots> \<le> real N * (norm x - 1) + 1" by simp
  also have "\<dots> \<le> (norm x - 1 + 1) ^ N" by (rule linear_plus_1_le_power) simp
  also have "\<dots> = norm x ^ N" by simp
  finally have "\<forall>n\<ge>N. y \<le> norm x ^ n"
    by (metis order_less_le_trans power_increasing order_less_imp_le x)
  then show "eventually (\<lambda>n. y \<le> norm (x ^ n)) sequentially"
    unfolding eventually_sequentially
    by (auto simp: norm_power)
qed simp

end


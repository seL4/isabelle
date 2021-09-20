(*  Title:      HOL/Library/Extended_Real.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
    Author:     Manuel Eberl, TU München
*)

section \<open>Extended real number line\<close>

theory Extended_Real
imports Complex_Main Extended_Nat Liminf_Limsup
begin

text \<open>
  This should be part of \<^theory>\<open>HOL-Library.Extended_Nat\<close> or \<^theory>\<open>HOL-Library.Order_Continuity\<close>, but then the AFP-entry \<open>Jinja_Thread\<close> fails, as it does overload
  certain named from \<^theory>\<open>Complex_Main\<close>.
\<close>

lemma incseq_sumI2:
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> 'a::ordered_comm_monoid_add"
  shows "(\<And>n. n \<in> A \<Longrightarrow> mono (f n)) \<Longrightarrow> mono (\<lambda>i. \<Sum>n\<in>A. f n i)"
  unfolding incseq_def by (auto intro: sum_mono)

lemma incseq_sumI:
  fixes f :: "nat \<Rightarrow> 'a::ordered_comm_monoid_add"
  assumes "\<And>i. 0 \<le> f i"
  shows "incseq (\<lambda>i. sum f {..< i})"
proof (intro incseq_SucI)
  fix n
  have "sum f {..< n} + 0 \<le> sum f {..<n} + f n"
    using assms by (rule add_left_mono)
  then show "sum f {..< n} \<le> sum f {..< Suc n}"
    by auto
qed

lemma continuous_at_left_imp_sup_continuous:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes "mono f" "\<And>x. continuous (at_left x) f"
  shows "sup_continuous f"
  unfolding sup_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'a" assume "incseq M" then show "f (SUP i. M i) = (SUP i. f (M i))"
    using continuous_at_Sup_mono [OF assms, of "range M"] by (simp add: image_comp)
qed

lemma sup_continuous_at_left:
  fixes f :: "'a::{complete_linorder, linorder_topology, first_countable_topology} \<Rightarrow>
    'b::{complete_linorder, linorder_topology}"
  assumes f: "sup_continuous f"
  shows "continuous (at_left x) f"
proof cases
  assume "x = bot" then show ?thesis
    by (simp add: trivial_limit_at_left_bot)
next
  assume x: "x \<noteq> bot"
  show ?thesis
    unfolding continuous_within
  proof (intro tendsto_at_left_sequentially[of bot])
    fix S :: "nat \<Rightarrow> 'a" assume S: "incseq S" and S_x: "S \<longlonglongrightarrow> x"
    from S_x have x_eq: "x = (SUP i. S i)"
      by (rule LIMSEQ_unique) (intro LIMSEQ_SUP S)
    show "(\<lambda>n. f (S n)) \<longlonglongrightarrow> f x"
      unfolding x_eq sup_continuousD[OF f S]
      using S sup_continuous_mono[OF f] by (intro LIMSEQ_SUP) (auto simp: mono_def)
  qed (insert x, auto simp: bot_less)
qed

lemma sup_continuous_iff_at_left:
  fixes f :: "'a::{complete_linorder, linorder_topology, first_countable_topology} \<Rightarrow>
    'b::{complete_linorder, linorder_topology}"
  shows "sup_continuous f \<longleftrightarrow> (\<forall>x. continuous (at_left x) f) \<and> mono f"
  using sup_continuous_at_left[of f] continuous_at_left_imp_sup_continuous[of f]
    sup_continuous_mono[of f] by auto

lemma continuous_at_right_imp_inf_continuous:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes "mono f" "\<And>x. continuous (at_right x) f"
  shows "inf_continuous f"
  unfolding inf_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'a" assume "decseq M" then show "f (INF i. M i) = (INF i. f (M i))"
    using continuous_at_Inf_mono [OF assms, of "range M"] by (simp add: image_comp)
qed

lemma inf_continuous_at_right:
  fixes f :: "'a::{complete_linorder, linorder_topology, first_countable_topology} \<Rightarrow>
    'b::{complete_linorder, linorder_topology}"
  assumes f: "inf_continuous f"
  shows "continuous (at_right x) f"
proof cases
  assume "x = top" then show ?thesis
    by (simp add: trivial_limit_at_right_top)
next
  assume x: "x \<noteq> top"
  show ?thesis
    unfolding continuous_within
  proof (intro tendsto_at_right_sequentially[of _ top])
    fix S :: "nat \<Rightarrow> 'a" assume S: "decseq S" and S_x: "S \<longlonglongrightarrow> x"
    from S_x have x_eq: "x = (INF i. S i)"
      by (rule LIMSEQ_unique) (intro LIMSEQ_INF S)
    show "(\<lambda>n. f (S n)) \<longlonglongrightarrow> f x"
      unfolding x_eq inf_continuousD[OF f S]
      using S inf_continuous_mono[OF f] by (intro LIMSEQ_INF) (auto simp: mono_def antimono_def)
  qed (insert x, auto simp: less_top)
qed

lemma inf_continuous_iff_at_right:
  fixes f :: "'a::{complete_linorder, linorder_topology, first_countable_topology} \<Rightarrow>
    'b::{complete_linorder, linorder_topology}"
  shows "inf_continuous f \<longleftrightarrow> (\<forall>x. continuous (at_right x) f) \<and> mono f"
  using inf_continuous_at_right[of f] continuous_at_right_imp_inf_continuous[of f]
    inf_continuous_mono[of f] by auto

instantiation enat :: linorder_topology
begin

definition open_enat :: "enat set \<Rightarrow> bool" where
  "open_enat = generate_topology (range lessThan \<union> range greaterThan)"

instance
  proof qed (rule open_enat_def)

end

lemma open_enat: "open {enat n}"
proof (cases n)
  case 0
  then have "{enat n} = {..< eSuc 0}"
    by (auto simp: enat_0)
  then show ?thesis
    by simp
next
  case (Suc n')
  then have "{enat n} = {enat n' <..< enat (Suc n)}"
    using enat_iless by (fastforce simp: set_eq_iff)
  then show ?thesis
    by simp
qed

lemma open_enat_iff:
  fixes A :: "enat set"
  shows "open A \<longleftrightarrow> (\<infinity> \<in> A \<longrightarrow> (\<exists>n::nat. {n <..} \<subseteq> A))"
proof safe
  assume "\<infinity> \<notin> A"
  then have "A = (\<Union>n\<in>{n. enat n \<in> A}. {enat n})"
    by (simp add: set_eq_iff) (metis not_enat_eq)
  moreover have "open \<dots>"
    by (auto intro: open_enat)
  ultimately show "open A"
    by simp
next
  fix n assume "{enat n <..} \<subseteq> A"
  then have "A = (\<Union>n\<in>{n. enat n \<in> A}. {enat n}) \<union> {enat n <..}"
    using enat_ile leI by (simp add: set_eq_iff) blast
  moreover have "open \<dots>"
    by (intro open_Un open_UN ballI open_enat open_greaterThan)
  ultimately show "open A"
    by simp
next
  assume "open A" "\<infinity> \<in> A"
  then have "generate_topology (range lessThan \<union> range greaterThan) A" "\<infinity> \<in> A"
    unfolding open_enat_def by auto
  then show "\<exists>n::nat. {n <..} \<subseteq> A"
  proof induction
    case (Int A B)
    then obtain n m where "{enat n<..} \<subseteq> A" "{enat m<..} \<subseteq> B"
      by auto
    then have "{enat (max n m) <..} \<subseteq> A \<inter> B"
      by (auto simp add: subset_eq Ball_def max_def simp flip: enat_ord_code(1))
    then show ?case
      by auto
  next
    case (UN K)
    then obtain k where "k \<in> K" "\<infinity> \<in> k"
      by auto
    with UN.IH[OF this] show ?case
      by auto
  qed auto
qed

lemma nhds_enat: "nhds x = (if x = \<infinity> then INF i. principal {enat i..} else principal {x})"
proof auto
  show "nhds \<infinity> = (INF i. principal {enat i..})"
  proof (rule antisym)
    show "nhds \<infinity> \<le> (INF i. principal {enat i..})"
      unfolding nhds_def
      using Ioi_le_Ico by (intro INF_greatest INF_lower) (auto simp add: open_enat_iff)
    show "(INF i. principal {enat i..}) \<le> nhds \<infinity>"
      unfolding nhds_def
      by (intro INF_greatest) (force intro: INF_lower2[of "Suc _"] simp add: open_enat_iff Suc_ile_eq)
  qed
  show "nhds (enat i) = principal {enat i}" for i
    by (simp add: nhds_discrete_open open_enat)
qed

instance enat :: topological_comm_monoid_add
proof
  have [simp]: "enat i \<le> aa \<Longrightarrow> enat i \<le> aa + ba" for aa ba i
    by (rule order_trans[OF _ add_mono[of aa aa 0 ba]]) auto
  then have [simp]: "enat i \<le> ba \<Longrightarrow> enat i \<le> aa + ba" for aa ba i
    by (metis add.commute)
  fix a b :: enat show "((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)"
    apply (auto simp: nhds_enat filterlim_INF prod_filter_INF1 prod_filter_INF2
                      filterlim_principal principal_prod_principal eventually_principal)
    subgoal for i
      by (auto intro!: eventually_INF1[of i] simp: eventually_principal)
    subgoal for j i
      by (auto intro!: eventually_INF1[of i] simp: eventually_principal)
    subgoal for j i
      by (auto intro!: eventually_INF1[of i] simp: eventually_principal)
    done
qed

text \<open>
  For more lemmas about the extended real numbers see
  \<^file>\<open>~~/src/HOL/Analysis/Extended_Real_Limits.thy\<close>.
\<close>

subsection \<open>Definition and basic properties\<close>

datatype ereal = ereal real | PInfty | MInfty

lemma ereal_cong: "x = y \<Longrightarrow> ereal x = ereal y" by simp

instantiation ereal :: uminus
begin

fun uminus_ereal where
  "- (ereal r) = ereal (- r)"
| "- PInfty = MInfty"
| "- MInfty = PInfty"

instance ..

end

instantiation ereal :: infinity
begin

definition "(\<infinity>::ereal) = PInfty"
instance ..

end

declare [[coercion "ereal :: real \<Rightarrow> ereal"]]

lemma ereal_uminus_uminus[simp]:
  fixes a :: ereal
  shows "- (- a) = a"
  by (cases a) simp_all

lemma
  shows PInfty_eq_infinity[simp]: "PInfty = \<infinity>"
    and MInfty_eq_minfinity[simp]: "MInfty = - \<infinity>"
    and MInfty_neq_PInfty[simp]: "\<infinity> \<noteq> - (\<infinity>::ereal)" "- \<infinity> \<noteq> (\<infinity>::ereal)"
    and MInfty_neq_ereal[simp]: "ereal r \<noteq> - \<infinity>" "- \<infinity> \<noteq> ereal r"
    and PInfty_neq_ereal[simp]: "ereal r \<noteq> \<infinity>" "\<infinity> \<noteq> ereal r"
    and PInfty_cases[simp]: "(case \<infinity> of ereal r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = y"
    and MInfty_cases[simp]: "(case - \<infinity> of ereal r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = z"
  by (simp_all add: infinity_ereal_def)

declare
  PInfty_eq_infinity[code_post]
  MInfty_eq_minfinity[code_post]

lemma [code_unfold]:
  "\<infinity> = PInfty"
  "- PInfty = MInfty"
  by simp_all

lemma inj_ereal[simp]: "inj_on ereal A"
  unfolding inj_on_def by auto

lemma ereal_cases[cases type: ereal]:
  obtains (real) r where "x = ereal r"
    | (PInf) "x = \<infinity>"
    | (MInf) "x = -\<infinity>"
  by (cases x) auto

lemmas ereal2_cases = ereal_cases[case_product ereal_cases]
lemmas ereal3_cases = ereal2_cases[case_product ereal_cases]

lemma ereal_all_split: "\<And>P. (\<forall>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<and> (\<forall>x. P (ereal x)) \<and> P (-\<infinity>)"
  by (metis ereal_cases)

lemma ereal_ex_split: "\<And>P. (\<exists>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<or> (\<exists>x. P (ereal x)) \<or> P (-\<infinity>)"
  by (metis ereal_cases)

lemma ereal_uminus_eq_iff[simp]:
  fixes a b :: ereal
  shows "-a = -b \<longleftrightarrow> a = b"
  by (cases rule: ereal2_cases[of a b]) simp_all

function real_of_ereal :: "ereal \<Rightarrow> real" where
  "real_of_ereal (ereal r) = r"
| "real_of_ereal \<infinity> = 0"
| "real_of_ereal (-\<infinity>) = 0"
  by (auto intro: ereal_cases)
termination by standard (rule wf_empty)

lemma real_of_ereal[simp]:
  "real_of_ereal (- x :: ereal) = - (real_of_ereal x)"
  by (cases x) simp_all

lemma range_ereal[simp]: "range ereal = UNIV - {\<infinity>, -\<infinity>}"
proof safe
  fix x
  assume "x \<notin> range ereal" "x \<noteq> \<infinity>"
  then show "x = -\<infinity>"
    by (cases x) auto
qed auto

lemma ereal_range_uminus[simp]: "range uminus = (UNIV::ereal set)"
proof safe
  fix x :: ereal
  show "x \<in> range uminus"
    by (intro image_eqI[of _ _ "-x"]) auto
qed auto

instantiation ereal :: abs
begin

function abs_ereal where
  "\<bar>ereal r\<bar> = ereal \<bar>r\<bar>"
| "\<bar>-\<infinity>\<bar> = (\<infinity>::ereal)"
| "\<bar>\<infinity>\<bar> = (\<infinity>::ereal)"
by (auto intro: ereal_cases)
termination proof qed (rule wf_empty)

instance ..

end

lemma abs_eq_infinity_cases[elim!]:
  fixes x :: ereal
  assumes "\<bar>x\<bar> = \<infinity>"
  obtains "x = \<infinity>" | "x = -\<infinity>"
  using assms by (cases x) auto

lemma abs_neq_infinity_cases[elim!]:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains r where "x = ereal r"
  using assms by (cases x) auto

lemma abs_ereal_uminus[simp]:
  fixes x :: ereal
  shows "\<bar>- x\<bar> = \<bar>x\<bar>"
  by (cases x) auto

lemma ereal_infinity_cases:
  fixes a :: ereal
  shows "a \<noteq> \<infinity> \<Longrightarrow> a \<noteq> -\<infinity> \<Longrightarrow> \<bar>a\<bar> \<noteq> \<infinity>"
  by auto

subsubsection "Addition"

instantiation ereal :: "{one,comm_monoid_add,zero_neq_one}"
begin

definition "0 = ereal 0"
definition "1 = ereal 1"

function plus_ereal where
  "ereal r + ereal p = ereal (r + p)"
| "\<infinity> + a = (\<infinity>::ereal)"
| "a + \<infinity> = (\<infinity>::ereal)"
| "ereal r + -\<infinity> = - \<infinity>"
| "-\<infinity> + ereal p = -(\<infinity>::ereal)"
| "-\<infinity> + -\<infinity> = -(\<infinity>::ereal)"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with prems show P
   by (cases rule: ereal2_cases[of a b]) auto
qed auto
termination by standard (rule wf_empty)

lemma Infty_neq_0[simp]:
  "(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<noteq> 0" "0 \<noteq> -(\<infinity>::ereal)"
  by (simp_all add: zero_ereal_def)

lemma ereal_eq_0[simp]:
  "ereal r = 0 \<longleftrightarrow> r = 0"
  "0 = ereal r \<longleftrightarrow> r = 0"
  unfolding zero_ereal_def by simp_all

lemma ereal_eq_1[simp]:
  "ereal r = 1 \<longleftrightarrow> r = 1"
  "1 = ereal r \<longleftrightarrow> r = 1"
  unfolding one_ereal_def by simp_all

instance
proof
  fix a b c :: ereal
  show "0 + a = a"
    by (cases a) (simp_all add: zero_ereal_def)
  show "a + b = b + a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  show "a + b + c = a + (b + c)"
    by (cases rule: ereal3_cases[of a b c]) simp_all
  show "0 \<noteq> (1::ereal)"
    by (simp add: one_ereal_def zero_ereal_def)
qed

end

lemma ereal_0_plus [simp]: "ereal 0 + x = x"
  and plus_ereal_0 [simp]: "x + ereal 0 = x"
by(simp_all flip: zero_ereal_def)

instance ereal :: numeral ..

lemma real_of_ereal_0[simp]: "real_of_ereal (0::ereal) = 0"
  unfolding zero_ereal_def by simp

lemma abs_ereal_zero[simp]: "\<bar>0\<bar> = (0::ereal)"
  unfolding zero_ereal_def abs_ereal.simps by simp

lemma ereal_uminus_zero[simp]: "- 0 = (0::ereal)"
  by (simp add: zero_ereal_def)

lemma ereal_uminus_zero_iff[simp]:
  fixes a :: ereal
  shows "-a = 0 \<longleftrightarrow> a = 0"
  by (cases a) simp_all

lemma ereal_plus_eq_PInfty[simp]:
  fixes a b :: ereal
  shows "a + b = \<infinity> \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_plus_eq_MInfty[simp]:
  fixes a b :: ereal
  shows "a + b = -\<infinity> \<longleftrightarrow> (a = -\<infinity> \<or> b = -\<infinity>) \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_add_cancel_left:
  fixes a b :: ereal
  assumes "a \<noteq> -\<infinity>"
  shows "a + b = a + c \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_add_cancel_right:
  fixes a b :: ereal
  assumes "a \<noteq> -\<infinity>"
  shows "b + a = c + a \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_real: "ereal (real_of_ereal x) = (if \<bar>x\<bar> = \<infinity> then 0 else x)"
  by (cases x) simp_all

lemma real_of_ereal_add:
  fixes a b :: ereal
  shows "real_of_ereal (a + b) =
    (if (\<bar>a\<bar> = \<infinity>) \<and> (\<bar>b\<bar> = \<infinity>) \<or> (\<bar>a\<bar> \<noteq> \<infinity>) \<and> (\<bar>b\<bar> \<noteq> \<infinity>) then real_of_ereal a + real_of_ereal b else 0)"
  by (cases rule: ereal2_cases[of a b]) auto


subsubsection "Linear order on \<^typ>\<open>ereal\<close>"

instantiation ereal :: linorder
begin

function less_ereal
where
  "   ereal x < ereal y     \<longleftrightarrow> x < y"
| "(\<infinity>::ereal) < a           \<longleftrightarrow> False"
| "         a < -(\<infinity>::ereal) \<longleftrightarrow> False"
| "ereal x    < \<infinity>           \<longleftrightarrow> True"
| "        -\<infinity> < ereal r     \<longleftrightarrow> True"
| "        -\<infinity> < (\<infinity>::ereal) \<longleftrightarrow> True"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a,b)" by (cases x) auto
  with prems show P by (cases rule: ereal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

definition "x \<le> (y::ereal) \<longleftrightarrow> x < y \<or> x = y"

lemma ereal_infty_less[simp]:
  fixes x :: ereal
  shows "x < \<infinity> \<longleftrightarrow> (x \<noteq> \<infinity>)"
    "-\<infinity> < x \<longleftrightarrow> (x \<noteq> -\<infinity>)"
  by (cases x, simp_all) (cases x, simp_all)

lemma ereal_infty_less_eq[simp]:
  fixes x :: ereal
  shows "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
    and "x \<le> -\<infinity> \<longleftrightarrow> x = -\<infinity>"
  by (auto simp add: less_eq_ereal_def)

lemma ereal_less[simp]:
  "ereal r < 0 \<longleftrightarrow> (r < 0)"
  "0 < ereal r \<longleftrightarrow> (0 < r)"
  "ereal r < 1 \<longleftrightarrow> (r < 1)"
  "1 < ereal r \<longleftrightarrow> (1 < r)"
  "0 < (\<infinity>::ereal)"
  "-(\<infinity>::ereal) < 0"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_less_eq[simp]:
  "x \<le> (\<infinity>::ereal)"
  "-(\<infinity>::ereal) \<le> x"
  "ereal r \<le> ereal p \<longleftrightarrow> r \<le> p"
  "ereal r \<le> 0 \<longleftrightarrow> r \<le> 0"
  "0 \<le> ereal r \<longleftrightarrow> 0 \<le> r"
  "ereal r \<le> 1 \<longleftrightarrow> r \<le> 1"
  "1 \<le> ereal r \<longleftrightarrow> 1 \<le> r"
  by (auto simp add: less_eq_ereal_def zero_ereal_def one_ereal_def)

lemma ereal_infty_less_eq2:
  "a \<le> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = (\<infinity>::ereal)"
  "a \<le> b \<Longrightarrow> b = -\<infinity> \<Longrightarrow> a = -(\<infinity>::ereal)"
  by simp_all

instance
proof
  fix x y z :: ereal
  show "x \<le> x"
    by (cases x) simp_all
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases rule: ereal2_cases[of x y]) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases rule: ereal2_cases[of x y]) auto
  {
    assume "x \<le> y" "y \<le> x"
    then show "x = y"
      by (cases rule: ereal2_cases[of x y]) auto
  }
  {
    assume "x \<le> y" "y \<le> z"
    then show "x \<le> z"
      by (cases rule: ereal3_cases[of x y z]) auto
  }
qed

end

lemma ereal_dense2: "x < y \<Longrightarrow> \<exists>z. x < ereal z \<and> ereal z < y"
  using lt_ex gt_ex dense by (cases x y rule: ereal2_cases) auto

instance ereal :: dense_linorder
  by standard (blast dest: ereal_dense2)

instance ereal :: ordered_comm_monoid_add
proof
  fix a b c :: ereal
  assume "a \<le> b"
  then show "c + a \<le> c + b"
    by (cases rule: ereal3_cases[of a b c]) auto
qed

lemma ereal_one_not_less_zero_ereal[simp]: "\<not> 1 < (0::ereal)"
  by (simp add: zero_ereal_def)

lemma real_of_ereal_positive_mono:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> real_of_ereal x \<le> real_of_ereal y"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_MInfty_lessI[intro, simp]:
  fixes a :: ereal
  shows "a \<noteq> -\<infinity> \<Longrightarrow> -\<infinity> < a"
  by (cases a) auto

lemma ereal_less_PInfty[intro, simp]:
  fixes a :: ereal
  shows "a \<noteq> \<infinity> \<Longrightarrow> a < \<infinity>"
  by (cases a) auto

lemma ereal_less_ereal_Ex:
  fixes a b :: ereal
  shows "x < ereal r \<longleftrightarrow> x = -\<infinity> \<or> (\<exists>p. p < r \<and> x = ereal p)"
  by (cases x) auto

lemma less_PInf_Ex_of_nat: "x \<noteq> \<infinity> \<longleftrightarrow> (\<exists>n::nat. x < ereal (real n))"
proof (cases x)
  case (real r)
  then show ?thesis
    using reals_Archimedean2[of r] by simp
qed simp_all

lemma ereal_add_strict_mono2:
  fixes a b c d :: ereal
  assumes "a < b" and "c < d"
  shows "a + c < b + d"
  using assms
  by (cases a; force simp add: elim: less_ereal.elims)

lemma ereal_minus_le_minus[simp]:
  fixes a b :: ereal
  shows "- a \<le> - b \<longleftrightarrow> b \<le> a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_minus_less_minus[simp]:
  fixes a b :: ereal
  shows "- a < - b \<longleftrightarrow> b < a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_le_real_iff:
  "x \<le> real_of_ereal y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x \<le> y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x \<le> 0)"
  by (cases y) auto

lemma real_le_ereal_iff:
  "real_of_ereal y \<le> x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y \<le> ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 \<le> x)"
  by (cases y) auto

lemma ereal_less_real_iff:
  "x < real_of_ereal y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> ereal x < y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x < 0)"
  by (cases y) auto

lemma real_less_ereal_iff:
  "real_of_ereal y < x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y < ereal x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 < x)"
  by (cases y) auto

text \<open>
  To help with inferences like \<^prop>\<open>a < ereal x \<Longrightarrow> x < y \<Longrightarrow> a < ereal y\<close>,
  where x and y are real.
\<close>

lemma le_ereal_le: "a \<le> ereal x \<Longrightarrow> x \<le> y \<Longrightarrow> a \<le> ereal y"
  using ereal_less_eq(3) order.trans by blast

lemma le_ereal_less: "a \<le> ereal x \<Longrightarrow> x < y \<Longrightarrow> a < ereal y"
  by (simp add: le_less_trans)

lemma less_ereal_le: "a < ereal x \<Longrightarrow> x \<le> y \<Longrightarrow> a < ereal y"
  using ereal_less_ereal_Ex by auto

lemma ereal_le_le: "ereal y \<le> a \<Longrightarrow> x \<le> y \<Longrightarrow> ereal x \<le> a"
  by (simp add: order_subst2)

lemma ereal_le_less: "ereal y \<le> a \<Longrightarrow> x < y \<Longrightarrow> ereal x < a"
  by (simp add: dual_order.strict_trans1)

lemma ereal_less_le: "ereal y < a \<Longrightarrow> x \<le> y \<Longrightarrow> ereal x < a"
  using ereal_less_eq(3) le_less_trans by blast

lemma real_of_ereal_pos:
  fixes x :: ereal
  shows "0 \<le> x \<Longrightarrow> 0 \<le> real_of_ereal x" by (cases x) auto

lemmas real_of_ereal_ord_simps =
  ereal_le_real_iff real_le_ereal_iff ereal_less_real_iff real_less_ereal_iff

lemma abs_ereal_ge0[simp]: "0 \<le> x \<Longrightarrow> \<bar>x :: ereal\<bar> = x"
  by (cases x) auto

lemma abs_ereal_less0[simp]: "x < 0 \<Longrightarrow> \<bar>x :: ereal\<bar> = -x"
  by (cases x) auto

lemma abs_ereal_pos[simp]: "0 \<le> \<bar>x :: ereal\<bar>"
  by (cases x) auto

lemma ereal_abs_leI:
  fixes x y :: ereal
  shows "\<lbrakk> x \<le> y; -x \<le> y \<rbrakk> \<Longrightarrow> \<bar>x\<bar> \<le> y"
by(cases x y rule: ereal2_cases)(simp_all)

lemma ereal_abs_add:
  fixes a b::ereal
  shows "abs(a+b) \<le> abs a + abs b"
by (cases rule: ereal2_cases[of a b]) (auto)

lemma real_of_ereal_le_0[simp]: "real_of_ereal (x :: ereal) \<le> 0 \<longleftrightarrow> x \<le> 0 \<or> x = \<infinity>"
  by (cases x) auto

lemma abs_real_of_ereal[simp]: "\<bar>real_of_ereal (x :: ereal)\<bar> = real_of_ereal \<bar>x\<bar>"
  by (cases x) auto

lemma zero_less_real_of_ereal:
  fixes x :: ereal
  shows "0 < real_of_ereal x \<longleftrightarrow> 0 < x \<and> x \<noteq> \<infinity>"
  by (cases x) auto

lemma ereal_0_le_uminus_iff[simp]:
  fixes a :: ereal
  shows "0 \<le> - a \<longleftrightarrow> a \<le> 0"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_uminus_le_0_iff[simp]:
  fixes a :: ereal
  shows "- a \<le> 0 \<longleftrightarrow> 0 \<le> a"
  by (cases rule: ereal2_cases[of a]) auto

lemma ereal_add_strict_mono:
  fixes a b c d :: ereal
  assumes "a \<le> b"
    and "0 \<le> a"
    and "a \<noteq> \<infinity>"
    and "c < d"
  shows "a + c < b + d"
  using assms
  by (cases rule: ereal3_cases[case_product ereal_cases, of a b c d]) auto

lemma ereal_less_add:
  fixes a b c :: ereal
  shows "\<bar>a\<bar> \<noteq> \<infinity> \<Longrightarrow> c < b \<Longrightarrow> a + c < a + b"
  by (cases rule: ereal2_cases[of b c]) auto

lemma ereal_add_nonneg_eq_0_iff:
  fixes a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (cases a b rule: ereal2_cases) auto

lemma ereal_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::ereal)"
  by auto

lemma ereal_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_less_minus)

lemma ereal_less_uminus_reorder: "a < - b \<longleftrightarrow> b < - (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_less_minus)

lemma ereal_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::ereal)"
  by (subst (3) ereal_uminus_uminus[symmetric]) (simp only: ereal_minus_le_minus)

lemmas ereal_uminus_reorder =
  ereal_uminus_eq_reorder ereal_uminus_less_reorder ereal_uminus_le_reorder

lemma ereal_bot:
  fixes x :: ereal
  assumes "\<And>B. x \<le> ereal B"
  shows "x = - \<infinity>"
proof (cases x)
  case (real r)
  with assms[of "r - 1"] show ?thesis
    by auto
next
  case PInf
  with assms[of 0] show ?thesis
    by auto
next
  case MInf
  then show ?thesis
    by simp
qed

lemma ereal_top:
  fixes x :: ereal
  assumes "\<And>B. x \<ge> ereal B"
  shows "x = \<infinity>"
proof (cases x)
  case (real r)
  with assms[of "r + 1"] show ?thesis
    by auto
next
  case MInf
  with assms[of 0] show ?thesis
    by auto
next
  case PInf
  then show ?thesis
    by simp
qed

lemma
  shows ereal_max[simp]: "ereal (max x y) = max (ereal x) (ereal y)"
    and ereal_min[simp]: "ereal (min x y) = min (ereal x) (ereal y)"
  by (simp_all add: min_def max_def)

lemma ereal_max_0: "max 0 (ereal r) = ereal (max 0 r)"
  by (auto simp: zero_ereal_def)

lemma
  fixes f :: "nat \<Rightarrow> ereal"
  shows ereal_incseq_uminus[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
    and ereal_decseq_uminus[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma incseq_ereal: "incseq f \<Longrightarrow> incseq (\<lambda>x. ereal (f x))"
  unfolding incseq_def by auto

lemma sum_ereal[simp]: "(\<Sum>x\<in>A. ereal (f x)) = ereal (\<Sum>x\<in>A. f x)"
proof (cases "finite A")
  case True
  then show ?thesis by induct auto
next
  case False
  then show ?thesis by simp
qed

lemma sum_list_ereal [simp]: "sum_list (map (\<lambda>x. ereal (f x)) xs) = ereal (sum_list (map f xs))"
  by (induction xs) simp_all

lemma sum_Pinfty:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<Sum>x\<in>P. f x) = \<infinity> \<longleftrightarrow> finite P \<and> (\<exists>i\<in>P. f i = \<infinity>)"
proof safe
  assume *: "sum f P = \<infinity>"
  show "finite P"
  proof (rule ccontr)
    assume "\<not> finite P"
    with * show False
      by auto
  qed
  show "\<exists>i\<in>P. f i = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<And>i. i \<in> P \<Longrightarrow> f i \<noteq> \<infinity>"
      by auto
    with \<open>finite P\<close> have "sum f P \<noteq> \<infinity>"
      by induct auto
    with * show False
      by auto
  qed
next
  fix i
  assume "finite P" and "i \<in> P" and "f i = \<infinity>"
  then show "sum f P = \<infinity>"
  proof induct
    case (insert x A)
    show ?case using insert by (cases "x = i") auto
  qed simp
qed

lemma sum_Inf:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "\<bar>sum f A\<bar> = \<infinity> \<longleftrightarrow> finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
proof
  assume *: "\<bar>sum f A\<bar> = \<infinity>"
  have "finite A"
    by (rule ccontr) (insert *, auto)
  moreover have "\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<forall>i\<in>A. \<exists>r. f i = ereal r"
      by auto
    from bchoice[OF this] obtain r where "\<forall>x\<in>A. f x = ereal (r x)" ..
    with * show False
      by auto
  qed
  ultimately show "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
    by auto
next
  assume "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
  then obtain i where "finite A" "i \<in> A" and "\<bar>f i\<bar> = \<infinity>"
    by auto
  then show "\<bar>sum f A\<bar> = \<infinity>"
  proof induct
    case (insert j A)
    then show ?case
      by (cases rule: ereal3_cases[of "f i" "f j" "sum f A"]) auto
  qed simp
qed

lemma sum_real_of_ereal:
  fixes f :: "'i \<Rightarrow> ereal"
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "(\<Sum>x\<in>S. real_of_ereal (f x)) = real_of_ereal (sum f S)"
proof -
  have "\<forall>x\<in>S. \<exists>r. f x = ereal r"
  proof
    fix x
    assume "x \<in> S"
    from assms[OF this] show "\<exists>r. f x = ereal r"
      by (cases "f x") auto
  qed
  from bchoice[OF this] obtain r where "\<forall>x\<in>S. f x = ereal (r x)" ..
  then show ?thesis
    by simp
qed

lemma sum_ereal_0:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "finite A"
    and "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
proof
  assume "sum f A = 0" with assms show "\<forall>i\<in>A. f i = 0"
  proof (induction A)
    case (insert a A)
    then have "f a = 0 \<and> (\<Sum>a\<in>A. f a) = 0"
      by (subst ereal_add_nonneg_eq_0_iff[symmetric]) (simp_all add: sum_nonneg)
    with insert show ?case
      by simp
  qed simp
qed auto

subsubsection "Multiplication"

instantiation ereal :: "{comm_monoid_mult,sgn}"
begin

function sgn_ereal :: "ereal \<Rightarrow> ereal" where
  "sgn (ereal r) = ereal (sgn r)"
| "sgn (\<infinity>::ereal) = 1"
| "sgn (-\<infinity>::ereal) = -1"
by (auto intro: ereal_cases)
termination by standard (rule wf_empty)

function times_ereal where
  "ereal r * ereal p = ereal (r * p)"
| "ereal r * \<infinity> = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "ereal r * -\<infinity> = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "-\<infinity> * ereal r = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "(\<infinity>::ereal) * \<infinity> = \<infinity>"
| "-(\<infinity>::ereal) * \<infinity> = -\<infinity>"
| "(\<infinity>::ereal) * -\<infinity> = -\<infinity>"
| "-(\<infinity>::ereal) * -\<infinity> = \<infinity>"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with prems show P
    by (cases rule: ereal2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

instance
proof
  fix a b c :: ereal
  show "1 * a = a"
    by (cases a) (simp_all add: one_ereal_def)
  show "a * b = b * a"
    by (cases rule: ereal2_cases[of a b]) simp_all
  show "a * b * c = a * (b * c)"
    by (cases rule: ereal3_cases[of a b c])
       (simp_all add: zero_ereal_def zero_less_mult_iff)
qed

end

lemma [simp]:
  shows ereal_1_times: "ereal 1 * x = x"
  and times_ereal_1: "x * ereal 1 = x"
by(simp_all flip: one_ereal_def)

lemma one_not_le_zero_ereal[simp]: "\<not> (1 \<le> (0::ereal))"
  by (simp add: one_ereal_def zero_ereal_def)

lemma real_ereal_1[simp]: "real_of_ereal (1::ereal) = 1"
  unfolding one_ereal_def by simp

lemma real_of_ereal_le_1:
  fixes a :: ereal
  shows "a \<le> 1 \<Longrightarrow> real_of_ereal a \<le> 1"
  by (cases a) (auto simp: one_ereal_def)

lemma abs_ereal_one[simp]: "\<bar>1\<bar> = (1::ereal)"
  unfolding one_ereal_def by simp

lemma ereal_mult_zero[simp]:
  fixes a :: ereal
  shows "a * 0 = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_zero_mult[simp]:
  fixes a :: ereal
  shows "0 * a = 0"
  by (cases a) (simp_all add: zero_ereal_def)

lemma ereal_m1_less_0[simp]: "-(1::ereal) < 0"
  by (simp add: zero_ereal_def one_ereal_def)

lemma ereal_times[simp]:
  "1 \<noteq> (\<infinity>::ereal)" "(\<infinity>::ereal) \<noteq> 1"
  "1 \<noteq> -(\<infinity>::ereal)" "-(\<infinity>::ereal) \<noteq> 1"
  by (auto simp: one_ereal_def)

lemma ereal_plus_1[simp]:
  "1 + ereal r = ereal (r + 1)"
  "ereal r + 1 = ereal (r + 1)"
  "1 + -(\<infinity>::ereal) = -\<infinity>"
  "-(\<infinity>::ereal) + 1 = -\<infinity>"
  unfolding one_ereal_def by auto

lemma ereal_zero_times[simp]:
  fixes a b :: ereal
  shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_PInfty[simp]:
  "a * b = (\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_eq_MInfty[simp]:
  "a * b = -(\<infinity>::ereal) \<longleftrightarrow>
    (a = \<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = -\<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_abs_mult: "\<bar>x * y :: ereal\<bar> = \<bar>x\<bar> * \<bar>y\<bar>"
  by (cases x y rule: ereal2_cases) (auto simp: abs_mult)

lemma ereal_0_less_1[simp]: "0 < (1::ereal)"
  by (simp_all add: zero_ereal_def one_ereal_def)

lemma ereal_mult_minus_left[simp]:
  fixes a b :: ereal
  shows "-a * b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_minus_right[simp]:
  fixes a b :: ereal
  shows "a * -b = - (a * b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_mult_infty[simp]:
  "a * (\<infinity>::ereal) = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_infty_mult[simp]:
  "(\<infinity>::ereal) * a = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma ereal_mult_strict_right_mono:
  assumes "a < b"
    and "0 < c"
    and "c < (\<infinity>::ereal)"
  shows "a * c < b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (auto simp: zero_le_mult_iff)

lemma ereal_mult_strict_left_mono:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c < (\<infinity>::ereal) \<Longrightarrow> c * a < c * b"
  using ereal_mult_strict_right_mono
  by (simp add: mult.commute[of c])

lemma ereal_mult_right_mono:
  fixes a b c :: ereal
  assumes "a \<le> b" "0 \<le> c"
  shows "a * c \<le> b * c"
proof (cases "c = 0")
  case False
  with assms show ?thesis
    by (cases rule: ereal3_cases[of a b c]) auto
qed auto

lemma ereal_mult_left_mono:
  fixes a b c :: ereal
  shows "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  using ereal_mult_right_mono
  by (simp add: mult.commute[of c])

lemma ereal_mult_mono:
  fixes a b c d::ereal
  assumes "b \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono':
  fixes a b c d::ereal
  assumes "a \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis ereal_mult_right_mono mult.commute order_trans assms)

lemma ereal_mult_mono_strict:
  fixes a b c d::ereal
  assumes "b > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
proof -
  have "c < \<infinity>" using \<open>c < d\<close> by auto
  then have "a * c < b * c" by (metis ereal_mult_strict_left_mono[OF assms(3) assms(2)] mult.commute)
  moreover have "b * c \<le> b * d" using assms(2) assms(4) by (simp add: assms(1) ereal_mult_left_mono less_imp_le)
  ultimately show ?thesis by simp
qed

lemma ereal_mult_mono_strict':
  fixes a b c d::ereal
  assumes "a > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
  using assms ereal_mult_mono_strict by auto

lemma zero_less_one_ereal[simp]: "0 \<le> (1::ereal)"
  by (simp add: one_ereal_def zero_ereal_def)

lemma ereal_0_le_mult[simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * (b :: ereal)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_right_distrib:
  fixes r a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> r * (a + b) = r * a + r * b"
  by (cases rule: ereal3_cases[of r a b]) (simp_all add: field_simps)

lemma ereal_left_distrib:
  fixes r a b :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a + b) * r = a * r + b * r"
  by (cases rule: ereal3_cases[of r a b]) (simp_all add: field_simps)

lemma ereal_mult_le_0_iff:
  fixes a b :: ereal
  shows "a * b \<le> 0 \<longleftrightarrow> (0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: mult_le_0_iff)

lemma ereal_zero_le_0_iff:
  fixes a b :: ereal
  shows "0 \<le> a * b \<longleftrightarrow> (0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: zero_le_mult_iff)

lemma ereal_mult_less_0_iff:
  fixes a b :: ereal
  shows "a * b < 0 \<longleftrightarrow> (0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: mult_less_0_iff)

lemma ereal_zero_less_0_iff:
  fixes a b :: ereal
  shows "0 < a * b \<longleftrightarrow> (0 < a \<and> 0 < b) \<or> (a < 0 \<and> b < 0)"
  by (cases rule: ereal2_cases[of a b]) (simp_all add: zero_less_mult_iff)

lemma ereal_left_mult_cong:
  fixes a b c :: ereal
  shows  "c = d \<Longrightarrow> (d \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> a * c = b * d"
  by (cases "c = 0") simp_all

lemma ereal_right_mult_cong:
  fixes a b c :: ereal
  shows "c = d \<Longrightarrow> (d \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> c * a = d * b"
  by (cases "c = 0") simp_all

lemma ereal_distrib:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma numeral_eq_ereal [simp]: "numeral w = ereal (numeral w)"
proof (induct w rule: num_induct)
  case One
  then show ?case
    by simp
next
  case (inc x)
  then show ?case
    by (simp add: inc numeral_inc)
qed

lemma distrib_left_ereal_nn:
  "c \<ge> 0 \<Longrightarrow> (x + y) * ereal c = x * ereal c + y * ereal c"
  by(cases x y rule: ereal2_cases)(simp_all add: ring_distribs)

lemma sum_ereal_right_distrib:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> r * sum f A = (\<Sum>n\<in>A. r * f n)"
  by (induct A rule: infinite_finite_induct)  (auto simp: ereal_right_distrib sum_nonneg)

lemma sum_ereal_left_distrib:
  "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> sum f A * r = (\<Sum>n\<in>A. f n * r :: ereal)"
  using sum_ereal_right_distrib[of A f r] by (simp add: mult_ac)

lemma sum_distrib_right_ereal:
  "c \<ge> 0 \<Longrightarrow> sum f A * ereal c = (\<Sum>x\<in>A. f x * c :: ereal)"
by(subst sum_comp_morphism[where h="\<lambda>x. x * ereal c", symmetric])(simp_all add: distrib_left_ereal_nn)

lemma ereal_le_epsilon:
  fixes x y :: ereal
  assumes "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (cases "x = -\<infinity> \<or> x = \<infinity> \<or> y = -\<infinity> \<or> y = \<infinity>")
  case True
  then show ?thesis
    using assms[of 1] by auto
next
  case False
  then obtain p q where "x = ereal p" "y = ereal q"
    by (metis MInfty_eq_minfinity ereal.distinct(3) uminus_ereal.elims)
  then show ?thesis 
    by (metis assms field_le_epsilon ereal_less(2) ereal_less_eq(3) plus_ereal.simps(1))
qed

lemma ereal_le_epsilon2:
  fixes x y :: ereal
  assumes "\<And>e::real. 0 < e \<Longrightarrow> x \<le> y + ereal e"
  shows "x \<le> y"
proof (rule ereal_le_epsilon)
  show "\<And>\<epsilon>::ereal. 0 < \<epsilon> \<Longrightarrow> x \<le> y + \<epsilon>"
  using assms less_ereal.elims(2) zero_less_real_of_ereal by fastforce
qed

lemma ereal_le_real:
  fixes x y :: ereal
  assumes "\<And>z. x \<le> ereal z \<Longrightarrow> y \<le> ereal z"
  shows "y \<le> x"
  by (metis assms ereal_bot ereal_cases ereal_infty_less_eq(2) ereal_less_eq(1) linorder_le_cases)

lemma prod_ereal_0:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<Prod>i\<in>A. f i) = 0 \<longleftrightarrow> finite A \<and> (\<exists>i\<in>A. f i = 0)"
proof (cases "finite A")
  case True
  then show ?thesis by (induct A) auto
qed auto

lemma prod_ereal_pos:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes pos: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "0 \<le> (\<Prod>i\<in>I. f i)"
proof (cases "finite I")
  case True
  from this pos show ?thesis
    by induct auto
qed auto

lemma prod_PInf:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Prod>i\<in>I. f i) = \<infinity> \<longleftrightarrow> finite I \<and> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<forall>i\<in>I. f i \<noteq> 0)"
proof (cases "finite I")
  case True
  from this assms show ?thesis
  proof (induct I)
    case (insert i I)
    then have pos: "0 \<le> f i" "0 \<le> prod f I"
      by (auto intro!: prod_ereal_pos)
    from insert have "(\<Prod>j\<in>insert i I. f j) = \<infinity> \<longleftrightarrow> prod f I * f i = \<infinity>"
      by auto
    also have "\<dots> \<longleftrightarrow> (prod f I = \<infinity> \<or> f i = \<infinity>) \<and> f i \<noteq> 0 \<and> prod f I \<noteq> 0"
      using prod_ereal_pos[of I f] pos
      by (cases rule: ereal2_cases[of "f i" "prod f I"]) auto
    also have "\<dots> \<longleftrightarrow> finite (insert i I) \<and> (\<exists>j\<in>insert i I. f j = \<infinity>) \<and> (\<forall>j\<in>insert i I. f j \<noteq> 0)"
      using insert by (auto simp: prod_ereal_0)
    finally show ?case .
  qed simp
qed auto

lemma prod_ereal: "(\<Prod>i\<in>A. ereal (f i)) = ereal (prod f A)"
proof (cases "finite A")
  case True
  then show ?thesis
    by induct (auto simp: one_ereal_def)
next
  case False
  then show ?thesis
    by (simp add: one_ereal_def)
qed


subsubsection \<open>Power\<close>

lemma ereal_power[simp]: "(ereal x) ^ n = ereal (x^n)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_PInf[simp]: "(\<infinity>::ereal) ^ n = (if n = 0 then 1 else \<infinity>)"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_uminus[simp]:
  fixes x :: ereal
  shows "(- x) ^ n = (if even n then x ^ n else - (x^n))"
  by (induct n) (auto simp: one_ereal_def)

lemma ereal_power_numeral[simp]:
  "(numeral num :: ereal) ^ n = ereal (numeral num ^ n)"
  by (induct n) (auto simp: one_ereal_def)

lemma zero_le_power_ereal[simp]:
  fixes a :: ereal
  assumes "0 \<le> a"
  shows "0 \<le> a ^ n"
  using assms by (induct n) (auto simp: ereal_zero_le_0_iff)


subsubsection \<open>Subtraction\<close>

lemma ereal_minus_minus_image[simp]:
  fixes S :: "ereal set"
  shows "uminus ` uminus ` S = S"
  by (auto simp: image_iff)

lemma ereal_uminus_lessThan[simp]:
  fixes a :: ereal
  shows "uminus ` {..<a} = {-a<..}"
proof -
  {
    fix x
    assume "-a < x"
    then have "- x < - (- a)"
      by (simp del: ereal_uminus_uminus)
    then have "- x < a"
      by simp
  }
  then show ?thesis
    by force
qed

lemma ereal_uminus_greaterThan[simp]: "uminus ` {(a::ereal)<..} = {..<-a}"
  by (metis ereal_uminus_lessThan ereal_uminus_uminus ereal_minus_minus_image)

instantiation ereal :: minus
begin

definition "x - y = x + -(y::ereal)"
instance ..

end

lemma ereal_minus[simp]:
  "ereal r - ereal p = ereal (r - p)"
  "-\<infinity> - ereal r = -\<infinity>"
  "ereal r - \<infinity> = -\<infinity>"
  "(\<infinity>::ereal) - x = \<infinity>"
  "-(\<infinity>::ereal) - \<infinity> = -\<infinity>"
  "x - -y = x + y"
  "x - 0 = x"
  "0 - x = -x"
  by (simp_all add: minus_ereal_def)

lemma ereal_x_minus_x[simp]: "x - x = (if \<bar>x\<bar> = \<infinity> then \<infinity> else 0::ereal)"
  by (cases x) simp_all

lemma ereal_eq_minus_iff:
  fixes x y z :: ereal
  shows "x = z - y \<longleftrightarrow>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y = z) \<and>
    (y = -\<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<longrightarrow> x = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_eq_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x = z - y \<longleftrightarrow> x + y = z"
  by (auto simp: ereal_eq_minus_iff)

lemma ereal_less_minus_iff:
  fixes x y z :: ereal
  shows "x < z - y \<longleftrightarrow>
    (y = \<infinity> \<longrightarrow> z = \<infinity> \<and> x \<noteq> \<infinity>) \<and>
    (y = -\<infinity> \<longrightarrow> x \<noteq> \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity>\<longrightarrow> x + y < z)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_less_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x < z - y \<longleftrightarrow> x + y < z"
  by (auto simp: ereal_less_minus_iff)

lemma ereal_le_minus_iff:
  fixes x y z :: ereal
  shows "x \<le> z - y \<longleftrightarrow> (y = \<infinity> \<longrightarrow> z \<noteq> \<infinity> \<longrightarrow> x = -\<infinity>) \<and> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x + y \<le> z)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_le_minus:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x \<le> z - y \<longleftrightarrow> x + y \<le> z"
  by (auto simp: ereal_le_minus_iff)

lemma ereal_minus_less_iff:
  fixes x y z :: ereal
  shows "x - y < z \<longleftrightarrow> y \<noteq> -\<infinity> \<and> (y = \<infinity> \<longrightarrow> x \<noteq> \<infinity> \<and> z \<noteq> -\<infinity>) \<and> (y \<noteq> \<infinity> \<longrightarrow> x < z + y)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_minus_less:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y < z \<longleftrightarrow> x < z + y"
  by (auto simp: ereal_minus_less_iff)

lemma ereal_minus_le_iff:
  fixes x y z :: ereal
  shows "x - y \<le> z \<longleftrightarrow>
    (y = -\<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (y = \<infinity> \<longrightarrow> x = \<infinity> \<longrightarrow> z = \<infinity>) \<and>
    (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> x \<le> z + y)"
  by (cases rule: ereal3_cases[of x y z]) auto

lemma ereal_minus_le:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - y \<le> z \<longleftrightarrow> x \<le> z + y"
  by (auto simp: ereal_minus_le_iff)

lemma ereal_minus_eq_minus_iff:
  fixes a b c :: ereal
  shows "a - b = a - c \<longleftrightarrow>
    b = c \<or> a = \<infinity> \<or> (a = -\<infinity> \<and> b \<noteq> -\<infinity> \<and> c \<noteq> -\<infinity>)"
  by (cases rule: ereal3_cases[of a b c]) auto

lemma ereal_add_le_add_iff:
  fixes a b c :: ereal
  shows "c + a \<le> c + b \<longleftrightarrow>
    a \<le> b \<or> c = \<infinity> \<or> (c = -\<infinity> \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>)"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma ereal_add_le_add_iff2:
  fixes a b c :: ereal
  shows "a + c \<le> b + c \<longleftrightarrow> a \<le> b \<or> c = \<infinity> \<or> (c = -\<infinity> \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>)"
by(cases rule: ereal3_cases[of a b c])(simp_all add: field_simps)

lemma ereal_mult_le_mult_iff:
  fixes a b c :: ereal
  shows "\<bar>c\<bar> \<noteq> \<infinity> \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: mult_le_cancel_left)

lemma ereal_minus_mono:
  fixes A B C D :: ereal assumes "A \<le> B" "D \<le> C"
  shows "A - C \<le> B - D"
  using assms
  by (cases rule: ereal3_cases[case_product ereal_cases, of A B C D]) simp_all

lemma ereal_mono_minus_cancel:
  fixes a b c :: ereal
  shows "c - a \<le> c - b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c < \<infinity> \<Longrightarrow> b \<le> a"
  by (cases a b c rule: ereal3_cases) auto

lemma real_of_ereal_minus:
  fixes a b :: ereal
  shows "real_of_ereal (a - b) = (if \<bar>a\<bar> = \<infinity> \<or> \<bar>b\<bar> = \<infinity> then 0 else real_of_ereal a - real_of_ereal b)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma real_of_ereal_minus': "\<bar>x\<bar> = \<infinity> \<longleftrightarrow> \<bar>y\<bar> = \<infinity> \<Longrightarrow> real_of_ereal x - real_of_ereal y = real_of_ereal (x - y :: ereal)"
by(subst real_of_ereal_minus) auto

lemma ereal_diff_positive:
  fixes a b :: ereal shows "a \<le> b \<Longrightarrow> 0 \<le> b - a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_between:
  fixes x e :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
    and "0 < e"
  shows "x - e < x"
    and "x < x + e"
  using assms  by (cases x, cases e, auto)+

lemma ereal_minus_eq_PInfty_iff:
  fixes x y :: ereal
  shows "x - y = \<infinity> \<longleftrightarrow> y = -\<infinity> \<or> x = \<infinity>"
  by (cases x y rule: ereal2_cases) simp_all

lemma ereal_diff_add_eq_diff_diff_swap:
  fixes x y z :: ereal
  shows "\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> x - (y + z) = x - y - z"
  by(cases x y z rule: ereal3_cases) simp_all

lemma ereal_diff_add_assoc2:
  fixes x y z :: ereal
  shows "x + y - z = x - z + y"
  by(cases x y z rule: ereal3_cases) simp_all

lemma ereal_add_uminus_conv_diff: fixes x y z :: ereal shows "- x + y = y - x"
  by(cases x y rule: ereal2_cases) simp_all

lemma ereal_minus_diff_eq:
  fixes x y :: ereal
  shows "\<lbrakk> x = \<infinity> \<longrightarrow> y \<noteq> \<infinity>; x = -\<infinity> \<longrightarrow> y \<noteq> - \<infinity> \<rbrakk> \<Longrightarrow> - (x - y) = y - x"
  by(cases x y rule: ereal2_cases) simp_all

lemma ediff_le_self [simp]: "x - y \<le> (x :: enat)"
  by(cases x y rule: enat.exhaust[case_product enat.exhaust]) simp_all

lemma ereal_abs_diff:
  fixes a b::ereal
  shows "abs(a-b) \<le> abs a + abs b"
  by (cases rule: ereal2_cases[of a b]) (auto)


subsubsection \<open>Division\<close>

instantiation ereal :: inverse
begin

function inverse_ereal where
  "inverse (ereal r) = (if r = 0 then \<infinity> else ereal (inverse r))"
| "inverse (\<infinity>::ereal) = 0"
| "inverse (-\<infinity>::ereal) = 0"
  by (auto intro: ereal_cases)
termination by (relation "{}") simp

definition "x div y = x * inverse (y :: ereal)"

instance ..

end

lemma real_of_ereal_inverse[simp]:
  fixes a :: ereal
  shows "real_of_ereal (inverse a) = 1 / real_of_ereal a"
  by (cases a) (auto simp: inverse_eq_divide)

lemma ereal_inverse[simp]:
  "inverse (0::ereal) = \<infinity>"
  "inverse (1::ereal) = 1"
  by (simp_all add: one_ereal_def zero_ereal_def)

lemma ereal_divide[simp]:
  "ereal r / ereal p = (if p = 0 then ereal r * \<infinity> else ereal (r / p))"
  unfolding divide_ereal_def by (auto simp: divide_real_def)

lemma ereal_divide_same[simp]:
  fixes x :: ereal
  shows "x / x = (if \<bar>x\<bar> = \<infinity> \<or> x = 0 then 0 else 1)"
  by (cases x) (simp_all add: divide_real_def divide_ereal_def one_ereal_def)

lemma ereal_inv_inv[simp]:
  fixes x :: ereal
  shows "inverse (inverse x) = (if x \<noteq> -\<infinity> then x else \<infinity>)"
  by (cases x) auto

lemma ereal_inverse_minus[simp]:
  fixes x :: ereal
  shows "inverse (- x) = (if x = 0 then \<infinity> else -inverse x)"
  by (cases x) simp_all

lemma ereal_uminus_divide[simp]:
  fixes x y :: ereal
  shows "- x / y = - (x / y)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_Infty[simp]:
  fixes x :: ereal
  shows "x / \<infinity> = 0" "x / -\<infinity> = 0"
  unfolding divide_ereal_def by simp_all

lemma ereal_divide_one[simp]: "x / 1 = (x::ereal)"
  unfolding divide_ereal_def by simp

lemma ereal_divide_ereal[simp]: "\<infinity> / ereal r = (if 0 \<le> r then \<infinity> else -\<infinity>)"
  unfolding divide_ereal_def by simp

lemma ereal_inverse_nonneg_iff: "0 \<le> inverse (x :: ereal) \<longleftrightarrow> 0 \<le> x \<or> x = -\<infinity>"
  by (cases x) auto

lemma inverse_ereal_ge0I: "0 \<le> (x :: ereal) \<Longrightarrow> 0 \<le> inverse x"
by(cases x) simp_all

lemma zero_le_divide_ereal[simp]:
  fixes a :: ereal
  assumes "0 \<le> a"
    and "0 \<le> b"
  shows "0 \<le> a / b"
  using assms by (cases rule: ereal2_cases[of a b]) (auto simp: zero_le_divide_iff)

lemma ereal_le_divide_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_le_divide_neg:
  fixes x y z :: ereal
  shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> y \<le> z / x \<longleftrightarrow> z \<le> x * y"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_le_neg:
  fixes x y z :: ereal
  shows "x < 0 \<Longrightarrow> x \<noteq> -\<infinity> \<Longrightarrow> z / x \<le> y \<longleftrightarrow> x * y \<le> z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_inverse_antimono_strict:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> inverse y < inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma ereal_inverse_antimono:
  fixes x y :: ereal
  shows "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> inverse y \<le> inverse x"
  by (cases rule: ereal2_cases[of x y]) auto

lemma inverse_inverse_Pinfty_iff[simp]:
  fixes x :: ereal
  shows "inverse x = \<infinity> \<longleftrightarrow> x = 0"
  by (cases x) auto

lemma ereal_inverse_eq_0:
  fixes x :: ereal
  shows "inverse x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity>"
  by (cases x) auto

lemma ereal_0_gt_inverse:
  fixes x :: ereal
  shows "0 < inverse x \<longleftrightarrow> x \<noteq> \<infinity> \<and> 0 \<le> x"
  by (cases x) auto

lemma ereal_inverse_le_0_iff:
  fixes x :: ereal
  shows "inverse x \<le> 0 \<longleftrightarrow> x < 0 \<or> x = \<infinity>"
  by(cases x) auto

lemma ereal_divide_eq_0_iff: "x / y = 0 \<longleftrightarrow> x = 0 \<or> \<bar>y :: ereal\<bar> = \<infinity>"
by(cases x y rule: ereal2_cases) simp_all

lemma ereal_mult_less_right:
  fixes a b c :: ereal
  assumes "b * a < c * a"
    and "0 < a"
    and "a < \<infinity>"
  shows "b < c"
  using assms
  by (cases rule: ereal3_cases[of a b c])
     (auto split: if_split_asm simp: zero_less_mult_iff zero_le_mult_iff)

lemma ereal_mult_divide: fixes a b :: ereal shows "0 < b \<Longrightarrow> b < \<infinity> \<Longrightarrow> b * (a / b) = a"
  by (cases a b rule: ereal2_cases) auto

lemma ereal_power_divide:
  fixes x y :: ereal
  shows "y \<noteq> 0 \<Longrightarrow> (x / y) ^ n = x^n / y^n"
  by (cases rule: ereal2_cases [of x y])
     (auto simp: one_ereal_def zero_ereal_def power_divide zero_le_power_eq)

lemma ereal_le_mult_one_interval:
  fixes x y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes z: "\<And>z. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases x)
  case PInf
  with z[of "1 / 2"] show "x \<le> y"
    by (simp add: one_ereal_def)
next
  case (real r)
  note r = this
  show "x \<le> y"
  proof (cases y)
    case (real p)
    note p = this
    have "r \<le> p"
    proof (rule field_le_mult_one_interval)
      fix z :: real
      assume "0 < z" and "z < 1"
      with z[of "ereal z"] show "z * r \<le> p"
        using p r by (auto simp: zero_le_mult_iff one_ereal_def)
    qed
    then show "x \<le> y"
      using p r by simp
  qed (insert y, simp_all)
qed simp

lemma ereal_divide_right_mono[simp]:
  fixes x y z :: ereal
  assumes "x \<le> y"
    and "0 < z"
  shows "x / z \<le> y / z"
  using assms by (cases x y z rule: ereal3_cases) (auto intro: divide_right_mono)

lemma ereal_divide_left_mono[simp]:
  fixes x y z :: ereal
  assumes "y \<le> x"
    and "0 < z"
    and "0 < x * y"
  shows "z / x \<le> z / y"
  using assms
  by (cases x y z rule: ereal3_cases)
     (auto intro: divide_left_mono simp: field_simps zero_less_mult_iff mult_less_0_iff split: if_split_asm)

lemma ereal_divide_zero_left[simp]:
  fixes a :: ereal
  shows "0 / a = 0"
  by (cases a) (auto simp: zero_ereal_def)

lemma ereal_times_divide_eq_left[simp]:
  fixes a b c :: ereal
  shows "b / c * a = b * a / c"
  by (cases a b c rule: ereal3_cases) (auto simp: field_simps zero_less_mult_iff mult_less_0_iff)

lemma ereal_times_divide_eq: "a * (b / c :: ereal) = a * b / c"
  by (cases a b c rule: ereal3_cases)
     (auto simp: field_simps zero_less_mult_iff)

lemma ereal_inverse_real [simp]: "\<bar>z\<bar> \<noteq> \<infinity> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> ereal (inverse (real_of_ereal z)) = inverse z"
  by auto

lemma ereal_inverse_mult:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse (a * (b::ereal)) = inverse a * inverse b"
  by (cases a; cases b) auto

lemma inverse_eq_infinity_iff_eq_zero [simp]:
  "1/(x::ereal) = \<infinity> \<longleftrightarrow> x = 0"
by (simp add: divide_ereal_def)

lemma ereal_distrib_left:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "c * (a + b) = c * a + c * b"
using assms
by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma ereal_distrib_minus_left:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> \<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> -\<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "c * (a - b) = c * a - c * b"
using assms
by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)

lemma ereal_distrib_minus_right:
  fixes a b c :: ereal
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> \<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> -\<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a - b) * c = a * c - b * c"
using assms
by (cases rule: ereal3_cases[of a b c]) (simp_all add: field_simps)


subsection "Complete lattice"

instantiation ereal :: lattice
begin

definition [simp]: "sup x y = (max x y :: ereal)"
definition [simp]: "inf x y = (min x y :: ereal)"
instance by standard simp_all

end

instantiation ereal :: complete_lattice
begin

definition "bot = (-\<infinity>::ereal)"
definition "top = (\<infinity>::ereal)"

definition "Sup S = (SOME x :: ereal. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z))"
definition "Inf S = (SOME x :: ereal. (\<forall>y\<in>S. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x))"

lemma ereal_complete_Sup:
  fixes S :: "ereal set"
  shows "\<exists>x. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z)"
proof (cases "\<exists>x. \<forall>a\<in>S. a \<le> ereal x")
  case True
  then obtain y where y: "a \<le> ereal y" if "a\<in>S" for a
    by auto
  then have "\<infinity> \<notin> S"
    by force
  show ?thesis
  proof (cases "S \<noteq> {-\<infinity>} \<and> S \<noteq> {}")
    case True
    with \<open>\<infinity> \<notin> S\<close> obtain x where x: "x \<in> S" "\<bar>x\<bar> \<noteq> \<infinity>"
      by auto
    obtain s where s: "\<forall>x\<in>ereal -` S. x \<le> s" "(\<forall>x\<in>ereal -` S. x \<le> z) \<Longrightarrow> s \<le> z" for z
    proof (atomize_elim, rule complete_real)
      show "\<exists>x. x \<in> ereal -` S"
        using x by auto
      show "\<exists>z. \<forall>x\<in>ereal -` S. x \<le> z"
        by (auto dest: y intro!: exI[of _ y])
    qed
    show ?thesis
    proof (safe intro!: exI[of _ "ereal s"])
      fix y
      assume "y \<in> S"
      with s \<open>\<infinity> \<notin> S\<close> show "y \<le> ereal s"
        by (cases y) auto
    next
      fix z
      assume "\<forall>y\<in>S. y \<le> z"
      with \<open>S \<noteq> {-\<infinity>} \<and> S \<noteq> {}\<close> show "ereal s \<le> z"
        by (cases z) (auto intro!: s)
    qed
  next
    case False
    then show ?thesis
      by (auto intro!: exI[of _ "-\<infinity>"])
  qed
next
  case False
  then show ?thesis
    by (fastforce intro!: exI[of _ \<infinity>] ereal_top intro: order_trans dest: less_imp_le simp: not_le)
qed

lemma ereal_complete_uminus_eq:
  fixes S :: "ereal set"
  shows "(\<forall>y\<in>uminus`S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>uminus`S. y \<le> z) \<longrightarrow> x \<le> z)
     \<longleftrightarrow> (\<forall>y\<in>S. -x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> -x)"
  by simp (metis ereal_minus_le_minus ereal_uminus_uminus)

lemma ereal_complete_Inf:
  "\<exists>x. (\<forall>y\<in>S::ereal set. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x)"
  using ereal_complete_Sup[of "uminus ` S"]
  unfolding ereal_complete_uminus_eq
  by auto

instance
proof
  show "Sup {} = (bot::ereal)"
    using ereal_bot by (auto simp: bot_ereal_def Sup_ereal_def)
  show "Inf {} = (top::ereal)"
    unfolding top_ereal_def Inf_ereal_def
    using ereal_infty_less_eq(1) ereal_less_eq(1) by blast
qed (auto intro: someI2_ex ereal_complete_Sup ereal_complete_Inf
  simp: Sup_ereal_def Inf_ereal_def bot_ereal_def top_ereal_def)

end

instance ereal :: complete_linorder ..

instance ereal :: linear_continuum
proof
  show "\<exists>a b::ereal. a \<noteq> b"
    using zero_neq_one by blast
qed

lemma min_PInf [simp]: "min (\<infinity>::ereal) x = x"
  by (metis min_top top_ereal_def)

lemma min_PInf2 [simp]: "min x (\<infinity>::ereal) = x"
  by (metis min_top2 top_ereal_def)

lemma max_PInf [simp]: "max (\<infinity>::ereal) x = \<infinity>"
  by (metis max_top top_ereal_def)

lemma max_PInf2 [simp]: "max x (\<infinity>::ereal) = \<infinity>"
  by (metis max_top2 top_ereal_def)

lemma min_MInf [simp]: "min (-\<infinity>::ereal) x = -\<infinity>"
  by (metis min_bot bot_ereal_def)

lemma min_MInf2 [simp]: "min x (-\<infinity>::ereal) = -\<infinity>"
  by (metis min_bot2 bot_ereal_def)

lemma max_MInf [simp]: "max (-\<infinity>::ereal) x = x"
  by (metis max_bot bot_ereal_def)

lemma max_MInf2 [simp]: "max x (-\<infinity>::ereal) = x"
  by (metis max_bot2 bot_ereal_def)

subsection \<open>Extended real intervals\<close>

lemma real_greaterThanLessThan_infinity_eq:
  "real_of_ereal ` {N::ereal<..<\<infinity>} =
    (if N = \<infinity> then {} else if N = -\<infinity> then UNIV else {real_of_ereal N<..})"
  by (force simp: real_less_ereal_iff intro!: image_eqI[where x="ereal _"] elim!: less_ereal.elims)

lemma real_greaterThanLessThan_minus_infinity_eq:
  "real_of_ereal ` {-\<infinity><..<N::ereal} =
    (if N = \<infinity> then UNIV else if N = -\<infinity> then {} else {..<real_of_ereal N})"
proof -
  have "real_of_ereal ` {-\<infinity><..<N::ereal} = uminus ` real_of_ereal ` {-N<..<\<infinity>}"
    by (auto simp: ereal_uminus_less_reorder intro!: image_eqI[where x="-x" for x])
  also note real_greaterThanLessThan_infinity_eq
  finally show ?thesis by (auto intro!: image_eqI[where x="-x" for x])
qed

lemma real_greaterThanLessThan_inter:
  "real_of_ereal ` {N<..<M::ereal} = real_of_ereal ` {-\<infinity><..<M} \<inter> real_of_ereal ` {N<..<\<infinity>}"
  by (force elim!: less_ereal.elims)

lemma real_atLeastGreaterThan_eq: "real_of_ereal ` {N<..<M::ereal} =
   (if N = \<infinity> then {} else
   if N = -\<infinity> then
    (if M = \<infinity> then UNIV
    else if M = -\<infinity> then {}
    else {..< real_of_ereal M})
  else if M = - \<infinity> then {}
  else if M = \<infinity> then {real_of_ereal N<..}
  else {real_of_ereal N <..< real_of_ereal M})"
proof (cases "M = -\<infinity> \<or> M = \<infinity> \<or> N = -\<infinity> \<or> N = \<infinity>")
  case True
  then show ?thesis
    by (auto simp: real_greaterThanLessThan_minus_infinity_eq real_greaterThanLessThan_infinity_eq )
next
  case False
  then obtain p q where "M = ereal p" "N = ereal q"
    by (metis MInfty_eq_minfinity ereal.distinct(3) uminus_ereal.elims)
  moreover have "\<And>x. \<lbrakk>q < x; x < p\<rbrakk> \<Longrightarrow> x \<in> real_of_ereal ` {ereal q<..<ereal p}"
    by (metis greaterThanLessThan_iff imageI less_ereal.simps(1) real_of_ereal.simps(1))
  ultimately show ?thesis 
    by (auto elim!: less_ereal.elims)
qed

lemma real_image_ereal_ivl:
  fixes a b::ereal
  shows
  "real_of_ereal ` {a<..<b} =
  (if a < b then (if a = - \<infinity> then if b = \<infinity> then UNIV else {..<real_of_ereal b}
  else if b = \<infinity> then {real_of_ereal a<..} else {real_of_ereal a <..< real_of_ereal b}) else {})"
  by (cases a; cases b; simp add: real_atLeastGreaterThan_eq not_less)

lemma fixes a b c::ereal
  shows not_inftyI: "a < b \<Longrightarrow> b < c \<Longrightarrow> abs b \<noteq> \<infinity>"
  by force

lemma
  interval_neqs:
  fixes r s t::real
  shows "{r<..<s} \<noteq> {t<..}"
    and "{r<..<s} \<noteq> {..<t}"
    and "{r<..<ra} \<noteq> UNIV"
    and "{r<..} \<noteq> {..<s}"
    and "{r<..} \<noteq> UNIV"
    and "{..<r} \<noteq> UNIV"
    and "{} \<noteq> {r<..}"
    and "{} \<noteq> {..<r}"
  subgoal
    by (metis dual_order.strict_trans greaterThanLessThan_iff greaterThan_iff gt_ex not_le order_refl)
  subgoal
    by (metis (no_types, opaque_lifting) greaterThanLessThan_empty_iff greaterThanLessThan_iff gt_ex
        lessThan_iff minus_minus neg_less_iff_less not_less order_less_irrefl)
  subgoal by force
  subgoal
    by (metis greaterThanLessThan_empty_iff greaterThanLessThan_eq greaterThan_iff inf.idem
        lessThan_iff lessThan_non_empty less_irrefl not_le)
  subgoal by force
  subgoal by force
  subgoal using greaterThan_non_empty by blast
  subgoal using lessThan_non_empty by blast
  done

lemma greaterThanLessThan_eq_iff:
  fixes r s t u::real
  shows "({r<..<s} = {t<..<u}) = (r \<ge> s \<and> u \<le> t \<or> r = t \<and> s = u)"
  by (metis cInf_greaterThanLessThan cSup_greaterThanLessThan greaterThanLessThan_empty_iff not_le)

lemma real_of_ereal_image_greaterThanLessThan_iff:
  "real_of_ereal ` {a <..< b} = real_of_ereal ` {c <..< d} \<longleftrightarrow> (a \<ge> b \<and> c \<ge> d \<or> a = c \<and> b = d)"
  unfolding real_atLeastGreaterThan_eq
  by (cases a; cases b; cases c; cases d;
    simp add: greaterThanLessThan_eq_iff interval_neqs interval_neqs[symmetric])

lemma uminus_image_real_of_ereal_image_greaterThanLessThan:
  "uminus ` real_of_ereal ` {l <..< u} = real_of_ereal ` {-u <..< -l}"
  by (force simp: algebra_simps ereal_less_uminus_reorder
    ereal_uminus_less_reorder intro: image_eqI[where x="-x" for x])

lemma add_image_real_of_ereal_image_greaterThanLessThan:
  "(+) c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c + l <..< c + u}"
  apply safe
  subgoal for x
    using ereal_less_add[of c]
    by (force simp: real_of_ereal_add add.commute)
  subgoal for _ x
    by (force simp: add.commute real_of_ereal_minus ereal_minus_less ereal_less_minus
      intro: image_eqI[where x="x - c"])
  done

lemma add2_image_real_of_ereal_image_greaterThanLessThan:
  "(\<lambda>x. x + c) ` real_of_ereal ` {l <..< u} = real_of_ereal ` {l + c <..< u + c}"
  using add_image_real_of_ereal_image_greaterThanLessThan[of c l u]
  by (metis add.commute image_cong)

lemma minus_image_real_of_ereal_image_greaterThanLessThan:
  "(-) c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c - u <..< c - l}"
  (is "?l = ?r")
proof -
  have "?l = (+) c ` uminus ` real_of_ereal ` {l <..< u}" by auto
  also note uminus_image_real_of_ereal_image_greaterThanLessThan
  also note add_image_real_of_ereal_image_greaterThanLessThan
  finally show ?thesis by (simp add: minus_ereal_def)
qed

lemma real_ereal_bound_lemma_up:
  assumes "s \<in> real_of_ereal ` {a<..<b}"
  assumes "t \<notin> real_of_ereal ` {a<..<b}"
  assumes "s \<le> t"
  shows "b \<noteq> \<infinity>"
proof (cases b)
  case PInf
  then show ?thesis
    using assms
    apply clarsimp
    by (metis UNIV_I assms(1) ereal_less_PInfty greaterThan_iff less_eq_ereal_def less_le_trans real_image_ereal_ivl)
qed auto

lemma real_ereal_bound_lemma_down:
  assumes s: "s \<in> real_of_ereal ` {a<..<b}"
  and t: "t \<notin> real_of_ereal ` {a<..<b}"
  and "t \<le> s"
  shows "a \<noteq> - \<infinity>"
proof (cases b)
  case (real r)
  then show ?thesis
    using assms real_greaterThanLessThan_minus_infinity_eq by force
next
  case PInf
  then show ?thesis
    using t real_greaterThanLessThan_infinity_eq by auto
next
  case MInf
  then show ?thesis
    using s by auto
qed


subsection "Topological space"

instantiation ereal :: linear_continuum_topology
begin

definition "open_ereal" :: "ereal set \<Rightarrow> bool" where
  open_ereal_generated: "open_ereal = generate_topology (range lessThan \<union> range greaterThan)"

instance
  by standard (simp add: open_ereal_generated)

end

lemma continuous_on_ereal[continuous_intros]:
  assumes f: "continuous_on s f" shows "continuous_on s (\<lambda>x. ereal (f x))"
  by (rule continuous_on_compose2 [OF continuous_onI_mono[of ereal UNIV] f]) auto

lemma tendsto_ereal[tendsto_intros, simp, intro]: "(f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>x. ereal (f x)) \<longlongrightarrow> ereal x) F"
  using isCont_tendsto_compose[of x ereal f F] continuous_on_ereal[of UNIV "\<lambda>x. x"]
  by (simp add: continuous_on_eq_continuous_at)

lemma tendsto_uminus_ereal[tendsto_intros, simp, intro]:
  assumes "(f \<longlongrightarrow> x) F"
  shows "((\<lambda>x. - f x::ereal) \<longlongrightarrow> - x) F"
proof (rule tendsto_compose[OF order_tendstoI assms])
  show "\<And>a. a < - x \<Longrightarrow> \<forall>\<^sub>F x in at x. a < - x"
    by (metis ereal_less_uminus_reorder eventually_at_topological lessThan_iff open_lessThan)
  show "\<And>a. - x < a \<Longrightarrow> \<forall>\<^sub>F x in at x. - x < a"
    by (metis ereal_uminus_reorder(2) eventually_at_topological greaterThan_iff open_greaterThan)
qed

lemma at_infty_ereal_eq_at_top: "at \<infinity> = filtermap ereal at_top"
  unfolding filter_eq_iff eventually_at_filter eventually_at_top_linorder eventually_filtermap
    top_ereal_def[symmetric]
  apply (subst eventually_nhds_top[of 0])
  apply (auto simp: top_ereal_def less_le ereal_all_split ereal_ex_split)
  apply (metis PInfty_neq_ereal(2) ereal_less_eq(3) ereal_top le_cases order_trans)
  done

lemma ereal_Lim_uminus: "(f \<longlongrightarrow> f0) net \<longleftrightarrow> ((\<lambda>x. - f x::ereal) \<longlongrightarrow> - f0) net"
  using tendsto_uminus_ereal[of f f0 net] tendsto_uminus_ereal[of "\<lambda>x. - f x" "- f0" net]
  by auto

lemma ereal_divide_less_iff: "0 < (c::ereal) \<Longrightarrow> c < \<infinity> \<Longrightarrow> a / c < b \<longleftrightarrow> a < b * c"
  by (cases a b c rule: ereal3_cases) (auto simp: field_simps)

lemma ereal_less_divide_iff: "0 < (c::ereal) \<Longrightarrow> c < \<infinity> \<Longrightarrow> a < b / c \<longleftrightarrow> a * c < b"
  by (cases a b c rule: ereal3_cases) (auto simp: field_simps)

lemma tendsto_cmult_ereal[tendsto_intros, simp, intro]:
  assumes c: "\<bar>c\<bar> \<noteq> \<infinity>" and f: "(f \<longlongrightarrow> x) F" shows "((\<lambda>x. c * f x::ereal) \<longlongrightarrow> c * x) F"
proof -
  { fix c :: ereal assume "0 < c" "c < \<infinity>"
    then have "((\<lambda>x. c * f x::ereal) \<longlongrightarrow> c * x) F"
      apply (intro tendsto_compose[OF _ f])
      apply (auto intro!: order_tendstoI simp: eventually_at_topological)
      apply (rule_tac x="{a/c <..}" in exI)
      apply (auto split: ereal.split simp: ereal_divide_less_iff mult.commute) []
      apply (rule_tac x="{..< a/c}" in exI)
      apply (auto split: ereal.split simp: ereal_less_divide_iff mult.commute) []
      done }
  note * = this

  have "((0 < c \<and> c < \<infinity>) \<or> (-\<infinity> < c \<and> c < 0) \<or> c = 0)"
    using c by (cases c) auto
  then show ?thesis
  proof (elim disjE conjE)
    assume "- \<infinity> < c" "c < 0"
    then have "0 < - c" "- c < \<infinity>"
      by (auto simp: ereal_uminus_reorder ereal_less_uminus_reorder[of 0])
    then have "((\<lambda>x. (- c) * f x) \<longlongrightarrow> (- c) * x) F"
      by (rule *)
    from tendsto_uminus_ereal[OF this] show ?thesis
      by simp
  qed (auto intro!: *)
qed

lemma tendsto_cmult_ereal_not_0[tendsto_intros, simp, intro]:
  assumes "x \<noteq> 0" and f: "(f \<longlongrightarrow> x) F" shows "((\<lambda>x. c * f x::ereal) \<longlongrightarrow> c * x) F"
proof cases
  assume "\<bar>c\<bar> = \<infinity>"
  show ?thesis
  proof (rule filterlim_cong[THEN iffD1, OF refl refl _ tendsto_const])
    have "0 < x \<or> x < 0"
      using \<open>x \<noteq> 0\<close> by (auto simp add: neq_iff)
    then show "eventually (\<lambda>x'. c * x = c * f x') F"
    proof
      assume "0 < x" from order_tendstoD(1)[OF f this] show ?thesis
        by eventually_elim (insert \<open>0<x\<close> \<open>\<bar>c\<bar> = \<infinity>\<close>, auto)
    next
      assume "x < 0" from order_tendstoD(2)[OF f this] show ?thesis
        by eventually_elim (insert \<open>x<0\<close> \<open>\<bar>c\<bar> = \<infinity>\<close>, auto)
    qed
  qed
qed (rule tendsto_cmult_ereal[OF _ f])

lemma tendsto_cadd_ereal[tendsto_intros, simp, intro]:
  assumes c: "y \<noteq> - \<infinity>" "x \<noteq> - \<infinity>" and f: "(f \<longlongrightarrow> x) F" shows "((\<lambda>x. f x + y::ereal) \<longlongrightarrow> x + y) F"
  apply (intro tendsto_compose[OF _ f])
  apply (auto intro!: order_tendstoI simp: eventually_at_topological)
  apply (rule_tac x="{a - y <..}" in exI)
  apply (auto split: ereal.split simp: ereal_minus_less_iff c) []
  apply (rule_tac x="{..< a - y}" in exI)
  apply (auto split: ereal.split simp: ereal_less_minus_iff c) []
  done

lemma tendsto_add_left_ereal[tendsto_intros, simp, intro]:
  assumes c: "\<bar>y\<bar> \<noteq> \<infinity>" and f: "(f \<longlongrightarrow> x) F" shows "((\<lambda>x. f x + y::ereal) \<longlongrightarrow> x + y) F"
  apply (intro tendsto_compose[OF _ f])
  apply (auto intro!: order_tendstoI simp: eventually_at_topological)
  apply (rule_tac x="{a - y <..}" in exI)
  apply (insert c, auto split: ereal.split simp: ereal_minus_less_iff) []
  apply (rule_tac x="{..< a - y}" in exI)
  apply (auto split: ereal.split simp: ereal_less_minus_iff c) []
  done

lemma continuous_at_ereal[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. ereal (f x))"
  unfolding continuous_def by auto

lemma ereal_Sup:
  assumes *: "\<bar>SUP a\<in>A. ereal a\<bar> \<noteq> \<infinity>"
  shows "ereal (Sup A) = (SUP a\<in>A. ereal a)"
proof (rule continuous_at_Sup_mono)
  obtain r where r: "ereal r = (SUP a\<in>A. ereal a)" "A \<noteq> {}"
    using * by (force simp: bot_ereal_def)
  then show "bdd_above A" "A \<noteq> {}"
    by (auto intro!: SUP_upper bdd_aboveI[of _ r] simp flip: ereal_less_eq)
qed (auto simp: mono_def continuous_at_imp_continuous_at_within continuous_at_ereal)

lemma ereal_SUP: "\<bar>SUP a\<in>A. ereal (f a)\<bar> \<noteq> \<infinity> \<Longrightarrow> ereal (SUP a\<in>A. f a) = (SUP a\<in>A. ereal (f a))"
  by (simp add: ereal_Sup image_comp)

lemma ereal_Inf:
  assumes *: "\<bar>INF a\<in>A. ereal a\<bar> \<noteq> \<infinity>"
  shows "ereal (Inf A) = (INF a\<in>A. ereal a)"
proof (rule continuous_at_Inf_mono)
  obtain r where r: "ereal r = (INF a\<in>A. ereal a)" "A \<noteq> {}"
    using * by (force simp: top_ereal_def)
  then show "bdd_below A" "A \<noteq> {}"
    by (auto intro!: INF_lower bdd_belowI[of _ r] simp flip: ereal_less_eq)
qed (auto simp: mono_def continuous_at_imp_continuous_at_within continuous_at_ereal)

lemma ereal_Inf':
  assumes *: "bdd_below A" "A \<noteq> {}"
  shows "ereal (Inf A) = (INF a\<in>A. ereal a)"
proof (rule ereal_Inf)
  from * obtain l u where "x \<in> A \<Longrightarrow> l \<le> x" "u \<in> A" for x
    by (auto simp: bdd_below_def)
  then have "l \<le> (INF x\<in>A. ereal x)" "(INF x\<in>A. ereal x) \<le> u"
    by (auto intro!: INF_greatest INF_lower)
  then show "\<bar>INF a\<in>A. ereal a\<bar> \<noteq> \<infinity>"
    by auto
qed

lemma ereal_INF: "\<bar>INF a\<in>A. ereal (f a)\<bar> \<noteq> \<infinity> \<Longrightarrow> ereal (INF a\<in>A. f a) = (INF a\<in>A. ereal (f a))"
  by (simp add: ereal_Inf image_comp)

lemma ereal_Sup_uminus_image_eq: "Sup (uminus ` S::ereal set) = - Inf S"
  by (auto intro!: SUP_eqI
           simp: Ball_def[symmetric] ereal_uminus_le_reorder le_Inf_iff
           intro!: complete_lattice_class.Inf_lower2)

lemma ereal_SUP_uminus_eq:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(SUP x\<in>S. uminus (f x)) = - (INF x\<in>S. f x)"
  using ereal_Sup_uminus_image_eq [of "f ` S"] by (simp add: image_comp)

lemma ereal_inj_on_uminus[intro, simp]: "inj_on uminus (A :: ereal set)"
  by (auto intro!: inj_onI)

lemma ereal_Inf_uminus_image_eq: "Inf (uminus ` S::ereal set) = - Sup S"
  using ereal_Sup_uminus_image_eq[of "uminus ` S"] by simp

lemma ereal_INF_uminus_eq:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(INF x\<in>S. - f x) = - (SUP x\<in>S. f x)"
  using ereal_Inf_uminus_image_eq [of "f ` S"] by (simp add: image_comp)

lemma ereal_SUP_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(SUP i \<in> R. - f i) = - (INF i \<in> R. f i)"
  using ereal_Sup_uminus_image_eq[of "f`R"]
  by (simp add: image_image)

lemma ereal_SUP_not_infty:
  fixes f :: "_ \<Rightarrow> ereal"
  shows "A \<noteq> {} \<Longrightarrow> l \<noteq> -\<infinity> \<Longrightarrow> u \<noteq> \<infinity> \<Longrightarrow> \<forall>a\<in>A. l \<le> f a \<and> f a \<le> u \<Longrightarrow> \<bar>Sup (f ` A)\<bar> \<noteq> \<infinity>"
  using SUP_upper2[of _ A l f] SUP_least[of A f u]
  by (cases "Sup (f ` A)") auto

lemma ereal_INF_not_infty:
  fixes f :: "_ \<Rightarrow> ereal"
  shows "A \<noteq> {} \<Longrightarrow> l \<noteq> -\<infinity> \<Longrightarrow> u \<noteq> \<infinity> \<Longrightarrow> \<forall>a\<in>A. l \<le> f a \<and> f a \<le> u \<Longrightarrow> \<bar>Inf (f ` A)\<bar> \<noteq> \<infinity>"
  using INF_lower2[of _ A f u] INF_greatest[of A l f]
  by (cases "Inf (f ` A)") auto

lemma ereal_image_uminus_shift:
  fixes X Y :: "ereal set"
  shows "uminus ` X = Y \<longleftrightarrow> X = uminus ` Y"
proof
  assume "uminus ` X = Y"
  then have "uminus ` uminus ` X = uminus ` Y"
    by (simp add: inj_image_eq_iff)
  then show "X = uminus ` Y"
    by (simp add: image_image)
qed (simp add: image_image)

lemma Sup_eq_MInfty:
  fixes S :: "ereal set"
  shows "Sup S = -\<infinity> \<longleftrightarrow> S = {} \<or> S = {-\<infinity>}"
  unfolding bot_ereal_def[symmetric] by auto

lemma Inf_eq_PInfty:
  fixes S :: "ereal set"
  shows "Inf S = \<infinity> \<longleftrightarrow> S = {} \<or> S = {\<infinity>}"
  using Sup_eq_MInfty[of "uminus`S"]
  unfolding ereal_Sup_uminus_image_eq ereal_image_uminus_shift by simp

lemma Inf_eq_MInfty:
  fixes S :: "ereal set"
  shows "-\<infinity> \<in> S \<Longrightarrow> Inf S = -\<infinity>"
  unfolding bot_ereal_def[symmetric] by auto

lemma Sup_eq_PInfty:
  fixes S :: "ereal set"
  shows "\<infinity> \<in> S \<Longrightarrow> Sup S = \<infinity>"
  unfolding top_ereal_def[symmetric] by auto

lemma not_MInfty_nonneg[simp]: "0 \<le> (x::ereal) \<Longrightarrow> x \<noteq> - \<infinity>"
  by auto

lemma Sup_ereal_close:
  fixes e :: ereal
  assumes "0 < e"
    and S: "\<bar>Sup S\<bar> \<noteq> \<infinity>" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
  using assms by (cases e) (auto intro!: less_Sup_iff[THEN iffD1])

lemma Inf_ereal_close:
  fixes e :: ereal
  assumes "\<bar>Inf X\<bar> \<noteq> \<infinity>"
    and "0 < e"
  shows "\<exists>x\<in>X. x < Inf X + e"
proof (rule Inf_less_iff[THEN iffD1])
  show "Inf X < Inf X + e"
    using assms by (cases e) auto
qed

lemma SUP_PInfty:
  "(\<And>n::nat. \<exists>i\<in>A. ereal (real n) \<le> f i) \<Longrightarrow> (SUP i\<in>A. f i :: ereal) = \<infinity>"
  unfolding top_ereal_def[symmetric] SUP_eq_top_iff
  by (metis MInfty_neq_PInfty(2) PInfty_neq_ereal(2) less_PInf_Ex_of_nat less_ereal.elims(2) less_le_trans)

lemma SUP_nat_Infty: "(SUP i. ereal (real i)) = \<infinity>"
  by (rule SUP_PInfty) auto

lemma SUP_ereal_add_left:
  assumes "I \<noteq> {}" "c \<noteq> -\<infinity>"
  shows "(SUP i\<in>I. f i + c :: ereal) = (SUP i\<in>I. f i) + c"
proof (cases "(SUP i\<in>I. f i) = - \<infinity>")
  case True
  then have "\<And>i. i \<in> I \<Longrightarrow> f i = -\<infinity>"
    unfolding Sup_eq_MInfty by auto
  with True show ?thesis
    by (cases c) (auto simp: \<open>I \<noteq> {}\<close>)
next
  case False
  then show ?thesis
    by (subst continuous_at_Sup_mono[where f="\<lambda>x. x + c"])
      (auto simp: continuous_at_imp_continuous_at_within continuous_at mono_def add_mono \<open>I \<noteq> {}\<close>
      \<open>c \<noteq> -\<infinity>\<close> image_comp)
qed

lemma SUP_ereal_add_right:
  fixes c :: ereal
  shows "I \<noteq> {} \<Longrightarrow> c \<noteq> -\<infinity> \<Longrightarrow> (SUP i\<in>I. c + f i) = c + (SUP i\<in>I. f i)"
  using SUP_ereal_add_left[of I c f] by (simp add: add.commute)

lemma SUP_ereal_minus_right:
  assumes "I \<noteq> {}" "c \<noteq> -\<infinity>"
  shows "(SUP i\<in>I. c - f i :: ereal) = c - (INF i\<in>I. f i)"
  using SUP_ereal_add_right[OF assms, of "\<lambda>i. - f i"]
  by (simp add: ereal_SUP_uminus minus_ereal_def)

lemma SUP_ereal_minus_left:
  assumes "I \<noteq> {}" "c \<noteq> \<infinity>"
  shows "(SUP i\<in>I. f i - c:: ereal) = (SUP i\<in>I. f i) - c"
  using SUP_ereal_add_left[OF \<open>I \<noteq> {}\<close>, of "-c" f] by (simp add: \<open>c \<noteq> \<infinity>\<close> minus_ereal_def)

lemma INF_ereal_minus_right:
  assumes "I \<noteq> {}" and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(INF i\<in>I. c - f i) = c - (SUP i\<in>I. f i::ereal)"
proof -
  { fix b have "(-c) + b = - (c - b)"
      using \<open>\<bar>c\<bar> \<noteq> \<infinity>\<close> by (cases c b rule: ereal2_cases) auto }
  note * = this
  show ?thesis
    using SUP_ereal_add_right[OF \<open>I \<noteq> {}\<close>, of "-c" f] \<open>\<bar>c\<bar> \<noteq> \<infinity>\<close>
    by (auto simp add: * ereal_SUP_uminus_eq)
qed

lemma SUP_ereal_le_addI:
  fixes f :: "'i \<Rightarrow> ereal"
  assumes "\<And>i. f i + y \<le> z" and "y \<noteq> -\<infinity>"
  shows "Sup (f ` UNIV) + y \<le> z"
  unfolding SUP_ereal_add_left[OF UNIV_not_empty \<open>y \<noteq> -\<infinity>\<close>, symmetric]
  by (rule SUP_least assms)+

lemma SUP_combine:
  fixes f :: "'a::semilattice_sup \<Rightarrow> 'a::semilattice_sup \<Rightarrow> 'b::complete_lattice"
  assumes mono: "\<And>a b c d. a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> f a c \<le> f b d"
  shows "(SUP i\<in>UNIV. SUP j\<in>UNIV. f i j) = (SUP i. f i i)"
proof (rule antisym)
  show "(SUP i j. f i j) \<le> (SUP i. f i i)"
    by (rule SUP_least SUP_upper2[where i="sup i j" for i j] UNIV_I mono sup_ge1 sup_ge2)+
  show "(SUP i. f i i) \<le> (SUP i j. f i j)"
    by (rule SUP_least SUP_upper2 UNIV_I mono order_refl)+
qed

lemma SUP_ereal_add:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes inc: "incseq f" "incseq g"
    and pos: "\<And>i. f i \<noteq> -\<infinity>" "\<And>i. g i \<noteq> -\<infinity>"
  shows "(SUP i. f i + g i) = Sup (f ` UNIV) + Sup (g ` UNIV)"
  apply (subst SUP_ereal_add_left[symmetric, OF UNIV_not_empty])
   apply (metis SUP_upper UNIV_I assms(4) ereal_infty_less_eq(2))
  apply (subst (2) add.commute)
  apply (subst SUP_ereal_add_left[symmetric, OF UNIV_not_empty assms(3)])
  apply (subst (2) add.commute)
  apply (rule SUP_combine[symmetric] add_mono inc[THEN monoD] | assumption)+
  done

lemma INF_eq_minf: "(INF i\<in>I. f i::ereal) \<noteq> -\<infinity> \<longleftrightarrow> (\<exists>b>-\<infinity>. \<forall>i\<in>I. b \<le> f i)"
  unfolding bot_ereal_def[symmetric] INF_eq_bot_iff by (auto simp: not_less)

lemma INF_ereal_add_left:
  assumes "I \<noteq> {}" "c \<noteq> -\<infinity>" "\<And>x. x \<in> I \<Longrightarrow> 0 \<le> f x"
  shows "(INF i\<in>I. f i + c :: ereal) = (INF i\<in>I. f i) + c"
proof -
  have "(INF i\<in>I. f i) \<noteq> -\<infinity>"
    unfolding INF_eq_minf using assms by (intro exI[of _ 0]) auto
  then show ?thesis
    by (subst continuous_at_Inf_mono[where f="\<lambda>x. x + c"])
       (auto simp: mono_def add_mono \<open>I \<noteq> {}\<close> \<open>c \<noteq> -\<infinity>\<close> continuous_at_imp_continuous_at_within
        continuous_at image_comp)
qed

lemma INF_ereal_add_right:
  assumes "I \<noteq> {}" "c \<noteq> -\<infinity>" "\<And>x. x \<in> I \<Longrightarrow> 0 \<le> f x"
  shows "(INF i\<in>I. c + f i :: ereal) = c + (INF i\<in>I. f i)"
  using INF_ereal_add_left[OF assms] by (simp add: ac_simps)

lemma INF_ereal_add_directed:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes nonneg: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> g i"
  assumes directed: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<exists>k\<in>I. f i + g j \<ge> f k + g k"
  shows "(INF i\<in>I. f i + g i) = (INF i\<in>I. f i) + (INF i\<in>I. g i)"
proof cases
  assume "I = {}" then show ?thesis
    by (simp add: top_ereal_def)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (rule antisym)
    show "(INF i\<in>I. f i) + (INF i\<in>I. g i) \<le> (INF i\<in>I. f i + g i)"
      by (rule INF_greatest; intro add_mono INF_lower)
  next
    have "(INF i\<in>I. f i + g i) \<le> (INF i\<in>I. (INF j\<in>I. f i + g j))"
      using directed by (intro INF_greatest) (blast intro: INF_lower2)
    also have "\<dots> = (INF i\<in>I. f i + (INF i\<in>I. g i))"
      using nonneg \<open>I \<noteq> {}\<close> by (auto simp: INF_ereal_add_right)
    also have "\<dots> = (INF i\<in>I. f i) + (INF i\<in>I. g i)"
      using nonneg by (intro INF_ereal_add_left \<open>I \<noteq> {}\<close>) (auto simp: INF_eq_minf intro!: exI[of _ 0])
    finally show "(INF i\<in>I. f i + g i) \<le> (INF i\<in>I. f i) + (INF i\<in>I. g i)" .
  qed
qed

lemma INF_ereal_add:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "decseq f" "decseq g"
    and fin: "\<And>i. f i \<noteq> \<infinity>" "\<And>i. g i \<noteq> \<infinity>"
  shows "(INF i. f i + g i) = Inf (f ` UNIV) + Inf (g ` UNIV)"
proof -
  have INF_less: "(INF i. f i) < \<infinity>" "(INF i. g i) < \<infinity>"
    using assms unfolding INF_less_iff by auto
  { fix a b :: ereal assume "a \<noteq> \<infinity>" "b \<noteq> \<infinity>"
    then have "- ((- a) + (- b)) = a + b"
      by (cases a b rule: ereal2_cases) auto }
  note * = this
  have "(INF i. f i + g i) = (INF i. - ((- f i) + (- g i)))"
    by (simp add: fin *)
  also have "\<dots> = Inf (f ` UNIV) + Inf (g ` UNIV)"
    unfolding ereal_INF_uminus_eq
    using assms INF_less
    by (subst SUP_ereal_add) (auto simp: ereal_SUP_uminus fin *)
  finally show ?thesis .
qed

lemma SUP_ereal_add_pos:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes inc: "incseq f" "incseq g"
    and pos: "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(SUP i. f i + g i) = Sup (f ` UNIV) + Sup (g ` UNIV)"
proof (intro SUP_ereal_add inc)
  fix i
  show "f i \<noteq> -\<infinity>" "g i \<noteq> -\<infinity>"
    using pos[of i] by auto
qed

lemma SUP_ereal_sum:
  fixes f g :: "'a \<Rightarrow> nat \<Rightarrow> ereal"
  assumes "\<And>n. n \<in> A \<Longrightarrow> incseq (f n)"
    and pos: "\<And>n i. n \<in> A \<Longrightarrow> 0 \<le> f n i"
  shows "(SUP i. \<Sum>n\<in>A. f n i) = (\<Sum>n\<in>A. Sup ((f n) ` UNIV))"
proof (cases "finite A")
  case True
  then show ?thesis using assms
    by induct (auto simp: incseq_sumI2 sum_nonneg SUP_ereal_add_pos)
next
  case False
  then show ?thesis by simp
qed

lemma SUP_ereal_mult_left:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" and c: "0 \<le> c"
  shows "(SUP i\<in>I. c * f i) = c * (SUP i\<in>I. f i)"
proof (cases "(SUP i \<in> I. f i) = 0")
  case True
  then have "\<And>i. i \<in> I \<Longrightarrow> f i = 0"
    by (metis SUP_upper f antisym)
  with True show ?thesis
    by simp
next
  case False
  then show ?thesis
    by (subst continuous_at_Sup_mono[where f="\<lambda>x. c * x"])
       (auto simp: mono_def continuous_at continuous_at_imp_continuous_at_within \<open>I \<noteq> {}\<close> image_comp
             intro!: ereal_mult_left_mono c)
qed

lemma countable_approach:
  fixes x :: ereal
  assumes "x \<noteq> -\<infinity>"
  shows "\<exists>f. incseq f \<and> (\<forall>i::nat. f i < x) \<and> (f \<longlonglongrightarrow> x)"
proof (cases x)
  case (real r)
  moreover have "(\<lambda>n. r - inverse (real (Suc n))) \<longlonglongrightarrow> r - 0"
    by (intro tendsto_intros LIMSEQ_inverse_real_of_nat)
  ultimately show ?thesis
    by (intro exI[of _ "\<lambda>n. x - inverse (Suc n)"]) (auto simp: incseq_def)
next
  case PInf with LIMSEQ_SUP[of "\<lambda>n::nat. ereal (real n)"] show ?thesis
    by (intro exI[of _ "\<lambda>n. ereal (real n)"]) (auto simp: incseq_def SUP_nat_Infty)
qed (simp add: assms)

lemma Sup_countable_SUP:
  assumes "A \<noteq> {}"
  shows "\<exists>f::nat \<Rightarrow> ereal. incseq f \<and> range f \<subseteq> A \<and> Sup A = (SUP i. f i)"
proof cases
  assume "Sup A = -\<infinity>"
  with \<open>A \<noteq> {}\<close> have "A = {-\<infinity>}"
    by (auto simp: Sup_eq_MInfty)
  then show ?thesis
    by (auto intro!: exI[of _ "\<lambda>_. -\<infinity>"] simp: bot_ereal_def)
next
  assume "Sup A \<noteq> -\<infinity>"
  then obtain l where "incseq l" and l: "l i < Sup A" and l_Sup: "l \<longlonglongrightarrow> Sup A" for i :: nat
    by (auto dest: countable_approach)

  have "\<exists>f. \<forall>n. (f n \<in> A \<and> l n \<le> f n) \<and> (f n \<le> f (Suc n))" (is "\<exists>f. ?P f")
  proof (rule dependent_nat_choice)
    show "\<exists>x. x \<in> A \<and> l 0 \<le> x"
      using l[of 0] by (auto simp: less_Sup_iff)
  next
    fix x n assume "x \<in> A \<and> l n \<le> x"
    moreover from l[of "Suc n"] obtain y where "y \<in> A" "l (Suc n) < y"
      by (auto simp: less_Sup_iff)
    ultimately show "\<exists>y. (y \<in> A \<and> l (Suc n) \<le> y) \<and> x \<le> y"
      by (auto intro!: exI[of _ "max x y"] split: split_max)
  qed
  then obtain f where f: "?P f" ..
  then have "range f \<subseteq> A" "incseq f"
    by (auto simp: incseq_Suc_iff)
  moreover
  have "(SUP i. f i) = Sup A"
  proof (rule tendsto_unique)
    show "f \<longlonglongrightarrow> (SUP i. f i)"
      by (rule LIMSEQ_SUP \<open>incseq f\<close>)+
    show "f \<longlonglongrightarrow> Sup A"
      using l f
      by (intro tendsto_sandwich[OF _ _ l_Sup tendsto_const])
         (auto simp: Sup_upper)
  qed simp
  ultimately show ?thesis
    by auto
qed

lemma Inf_countable_INF:
  assumes "A \<noteq> {}" shows "\<exists>f::nat \<Rightarrow> ereal. decseq f \<and> range f \<subseteq> A \<and> Inf A = (INF i. f i)"
proof -
  obtain f where "incseq f" "range f \<subseteq> uminus`A" "Sup (uminus`A) = (SUP i. f i)"
    using Sup_countable_SUP[of "uminus ` A"] \<open>A \<noteq> {}\<close> by auto
  then show ?thesis
    by (intro exI[of _ "\<lambda>x. - f x"])
       (auto simp: ereal_Sup_uminus_image_eq ereal_INF_uminus_eq eq_commute[of "- _"])
qed

lemma SUP_countable_SUP:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ereal. range f \<subseteq> g`A \<and> Sup (g ` A) = Sup (f ` UNIV)"
  using Sup_countable_SUP [of "g`A"] by auto

subsection "Relation to \<^typ>\<open>enat\<close>"

definition "ereal_of_enat n = (case n of enat n \<Rightarrow> ereal (real n) | \<infinity> \<Rightarrow> \<infinity>)"

declare [[coercion "ereal_of_enat :: enat \<Rightarrow> ereal"]]
declare [[coercion "(\<lambda>n. ereal (real n)) :: nat \<Rightarrow> ereal"]]

lemma ereal_of_enat_simps[simp]:
  "ereal_of_enat (enat n) = ereal n"
  "ereal_of_enat \<infinity> = \<infinity>"
  by (simp_all add: ereal_of_enat_def)

lemma ereal_of_enat_le_iff[simp]: "ereal_of_enat m \<le> ereal_of_enat n \<longleftrightarrow> m \<le> n"
  by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_less_iff[simp]: "ereal_of_enat m < ereal_of_enat n \<longleftrightarrow> m < n"
  by (cases m n rule: enat2_cases) auto

lemma numeral_le_ereal_of_enat_iff[simp]: "numeral m \<le> ereal_of_enat n \<longleftrightarrow> numeral m \<le> n"
by (cases n) (auto)

lemma numeral_less_ereal_of_enat_iff[simp]: "numeral m < ereal_of_enat n \<longleftrightarrow> numeral m < n"
  by (cases n) auto

lemma ereal_of_enat_ge_zero_cancel_iff[simp]: "0 \<le> ereal_of_enat n \<longleftrightarrow> 0 \<le> n"
  by (cases n) (auto simp flip: enat_0)

lemma ereal_of_enat_gt_zero_cancel_iff[simp]: "0 < ereal_of_enat n \<longleftrightarrow> 0 < n"
  by (cases n) (auto simp flip: enat_0)

lemma ereal_of_enat_zero[simp]: "ereal_of_enat 0 = 0"
  by (auto simp flip: enat_0)

lemma ereal_of_enat_inf[simp]: "ereal_of_enat n = \<infinity> \<longleftrightarrow> n = \<infinity>"
  by (cases n) auto

lemma ereal_of_enat_add: "ereal_of_enat (m + n) = ereal_of_enat m + ereal_of_enat n"
  by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_sub:
  assumes "n \<le> m"
  shows "ereal_of_enat (m - n) = ereal_of_enat m - ereal_of_enat n "
  using assms by (cases m n rule: enat2_cases) auto

lemma ereal_of_enat_mult:
  "ereal_of_enat (m * n) = ereal_of_enat m * ereal_of_enat n"
  by (cases m n rule: enat2_cases) auto

lemmas ereal_of_enat_pushin = ereal_of_enat_add ereal_of_enat_sub ereal_of_enat_mult
lemmas ereal_of_enat_pushout = ereal_of_enat_pushin[symmetric]

lemma ereal_of_enat_nonneg: "ereal_of_enat n \<ge> 0"
by(cases n) simp_all

lemma ereal_of_enat_Sup:
  assumes "A \<noteq> {}" shows "ereal_of_enat (Sup A) = (SUP a \<in> A. ereal_of_enat a)"
proof (intro antisym mono_Sup)
  show "ereal_of_enat (Sup A) \<le> (SUP a \<in> A. ereal_of_enat a)"
  proof cases
    assume "finite A"
    with \<open>A \<noteq> {}\<close> obtain a where "a \<in> A" "ereal_of_enat (Sup A) = ereal_of_enat a"
      using Max_in[of A] by (auto simp: Sup_enat_def simp del: Max_in)
    then show ?thesis
      by (auto intro: SUP_upper)
  next
    assume "\<not> finite A"
    have [simp]: "(SUP a \<in> A. ereal_of_enat a) = top"
      unfolding SUP_eq_top_iff
    proof safe
      fix x :: ereal assume "x < top"
      then obtain n :: nat where "x < n"
        using less_PInf_Ex_of_nat top_ereal_def by auto
      obtain a where "a \<in> A - enat ` {.. n}"
        by (metis \<open>\<not> finite A\<close> all_not_in_conv finite_Diff2 finite_atMost finite_imageI finite.emptyI)
      then have "a \<in> A" "ereal n \<le> ereal_of_enat a"
        by (auto simp: image_iff Ball_def)
           (metis enat_iless enat_ord_simps(1) ereal_of_enat_less_iff ereal_of_enat_simps(1) less_le not_less)
      with \<open>x < n\<close> show "\<exists>i\<in>A. x < ereal_of_enat i"
        by (auto intro!: bexI[of _ a])
    qed
    show ?thesis
      by simp
  qed
qed (simp add: mono_def)

lemma ereal_of_enat_SUP:
  "A \<noteq> {} \<Longrightarrow> ereal_of_enat (SUP a\<in>A. f a) = (SUP a \<in> A. ereal_of_enat (f a))"
  by (simp add: ereal_of_enat_Sup image_comp)


subsection "Limits on \<^typ>\<open>ereal\<close>"

lemma open_PInfty: "open A \<Longrightarrow> \<infinity> \<in> A \<Longrightarrow> (\<exists>x. {ereal x<..} \<subseteq> A)"
  unfolding open_ereal_generated
proof (induct rule: generate_topology.induct)
  case (Int A B)
  then obtain x z where "\<infinity> \<in> A \<Longrightarrow> {ereal x <..} \<subseteq> A" "\<infinity> \<in> B \<Longrightarrow> {ereal z <..} \<subseteq> B"
    by auto
  with Int show ?case
    by (intro exI[of _ "max x z"]) fastforce
next
  case (Basis S)
  {
    fix x
    have "x \<noteq> \<infinity> \<Longrightarrow> \<exists>t. x \<le> ereal t"
      by (cases x) auto
  }
  moreover note Basis
  ultimately show ?case
    by (auto split: ereal.split)
qed (fastforce simp add: vimage_Union)+

lemma open_MInfty: "open A \<Longrightarrow> -\<infinity> \<in> A \<Longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A)"
  unfolding open_ereal_generated
proof (induct rule: generate_topology.induct)
  case (Int A B)
  then obtain x z where "-\<infinity> \<in> A \<Longrightarrow> {..< ereal x} \<subseteq> A" "-\<infinity> \<in> B \<Longrightarrow> {..< ereal z} \<subseteq> B"
    by auto
  with Int show ?case
    by (intro exI[of _ "min x z"]) fastforce
next
  case (Basis S)
  {
    fix x
    have "x \<noteq> - \<infinity> \<Longrightarrow> \<exists>t. ereal t \<le> x"
      by (cases x) auto
  }
  moreover note Basis
  ultimately show ?case
    by (auto split: ereal.split)
qed (fastforce simp add: vimage_Union)+

lemma open_ereal_vimage: "open S \<Longrightarrow> open (ereal -` S)"
  by (intro open_vimage continuous_intros)

lemma open_ereal: "open S \<Longrightarrow> open (ereal ` S)"
  unfolding open_generated_order[where 'a=real]
proof (induct rule: generate_topology.induct)
  case (Basis S)
  moreover have "\<And>x. ereal ` {..< x} = { -\<infinity> <..< ereal x }"
    using ereal_less_ereal_Ex by auto
  moreover have "\<And>x. ereal ` {x <..} = { ereal x <..< \<infinity> }"
    using less_ereal.elims(2) by fastforce
  ultimately show ?case
    by auto
qed (auto simp add: image_Union image_Int)

lemma open_image_real_of_ereal:
  fixes X::"ereal set"
  assumes "open X"
  assumes infty: "\<infinity> \<notin> X" "-\<infinity> \<notin> X"
  shows "open (real_of_ereal ` X)"
proof -
  have "real_of_ereal ` X = ereal -` X"
    using infty ereal_real by (force simp: set_eq_iff)
  thus ?thesis
    by (auto intro!: open_ereal_vimage assms)
qed

lemma eventually_finite:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>" "(f \<longlongrightarrow> x) F"
  shows "eventually (\<lambda>x. \<bar>f x\<bar> \<noteq> \<infinity>) F"
proof -
  have "(f \<longlongrightarrow> ereal (real_of_ereal x)) F"
    using assms by (cases x) auto
  then have "eventually (\<lambda>x. f x \<in> ereal ` UNIV) F"
    by (rule topological_tendstoD) (auto intro: open_ereal)
  also have "(\<lambda>x. f x \<in> ereal ` UNIV) = (\<lambda>x. \<bar>f x\<bar> \<noteq> \<infinity>)"
    by auto
  finally show ?thesis .
qed


lemma open_ereal_def:
  "open A \<longleftrightarrow> open (ereal -` A) \<and> (\<infinity> \<in> A \<longrightarrow> (\<exists>x. {ereal x <..} \<subseteq> A)) \<and> (-\<infinity> \<in> A \<longrightarrow> (\<exists>x. {..<ereal x} \<subseteq> A))"
  (is "open A \<longleftrightarrow> ?rhs")
proof
  assume "open A"
  then show ?rhs
    using open_PInfty open_MInfty open_ereal_vimage by auto
next
  assume "?rhs"
  then obtain x y where A: "open (ereal -` A)" "\<infinity> \<in> A \<Longrightarrow> {ereal x<..} \<subseteq> A" "-\<infinity> \<in> A \<Longrightarrow> {..< ereal y} \<subseteq> A"
    by auto
  have *: "A = ereal ` (ereal -` A) \<union> (if \<infinity> \<in> A then {ereal x<..} else {}) \<union> (if -\<infinity> \<in> A then {..< ereal y} else {})"
    using A(2,3) by auto
  from open_ereal[OF A(1)] show "open A"
    by (subst *) (auto simp: open_Un)
qed

lemma open_PInfty2:
  assumes "open A"
    and "\<infinity> \<in> A"
  obtains x where "{ereal x<..} \<subseteq> A"
  using open_PInfty[OF assms] by auto

lemma open_MInfty2:
  assumes "open A"
    and "-\<infinity> \<in> A"
  obtains x where "{..<ereal x} \<subseteq> A"
  using open_MInfty[OF assms] by auto

lemma ereal_openE:
  assumes "open A"
  obtains x y where "open (ereal -` A)"
    and "\<infinity> \<in> A \<Longrightarrow> {ereal x<..} \<subseteq> A"
    and "-\<infinity> \<in> A \<Longrightarrow> {..<ereal y} \<subseteq> A"
  using assms open_ereal_def by auto

lemmas open_ereal_lessThan = open_lessThan[where 'a=ereal]
lemmas open_ereal_greaterThan = open_greaterThan[where 'a=ereal]
lemmas ereal_open_greaterThanLessThan = open_greaterThanLessThan[where 'a=ereal]
lemmas closed_ereal_atLeast = closed_atLeast[where 'a=ereal]
lemmas closed_ereal_atMost = closed_atMost[where 'a=ereal]
lemmas closed_ereal_atLeastAtMost = closed_atLeastAtMost[where 'a=ereal]
lemmas closed_ereal_singleton = closed_singleton[where 'a=ereal]

lemma ereal_open_cont_interval:
  fixes S :: "ereal set"
  assumes "open S"
    and "x \<in> S"
    and "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains e where "e > 0" and "{x-e <..< x+e} \<subseteq> S"
proof -
  from \<open>open S\<close>
  have "open (ereal -` S)"
    by (rule ereal_openE)
  then obtain e where "e > 0" and e: "dist y (real_of_ereal x) < e \<Longrightarrow> ereal y \<in> S" for y
    using assms unfolding open_dist by force
  show thesis
  proof (intro that subsetI)
    show "0 < ereal e"
      using \<open>0 < e\<close> by auto
    fix y
    assume "y \<in> {x - ereal e<..<x + ereal e}"
    with assms obtain t where "y = ereal t" "dist t (real_of_ereal x) < e"
      by (cases y) (auto simp: dist_real_def)
    then show "y \<in> S"
      using e[of t] by auto
  qed
qed

lemma ereal_open_cont_interval2:
  fixes S :: "ereal set"
  assumes "open S"
    and "x \<in> S"
    and x: "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains a b where "a < x" and "x < b" and "{a <..< b} \<subseteq> S"
proof -
  obtain e where "0 < e" "{x - e<..<x + e} \<subseteq> S"
    using assms by (rule ereal_open_cont_interval)
  with that[of "x - e" "x + e"] ereal_between[OF x, of e]
  show thesis
    by auto
qed

subsubsection \<open>Convergent sequences\<close>

lemma lim_real_of_ereal[simp]:
  assumes lim: "(f \<longlongrightarrow> ereal x) net"
  shows "((\<lambda>x. real_of_ereal (f x)) \<longlongrightarrow> x) net"
proof (intro topological_tendstoI)
  fix S
  assume "open S" and "x \<in> S"
  then have S: "open S" "ereal x \<in> ereal ` S"
    by (simp_all add: inj_image_mem_iff)
  show "eventually (\<lambda>x. real_of_ereal (f x) \<in> S) net"
    by (auto intro: eventually_mono [OF lim[THEN topological_tendstoD, OF open_ereal, OF S]])
qed

lemma lim_ereal[simp]: "((\<lambda>n. ereal (f n)) \<longlongrightarrow> ereal x) net \<longleftrightarrow> (f \<longlongrightarrow> x) net"
  by (auto dest!: lim_real_of_ereal)

lemma convergent_real_imp_convergent_ereal:
  assumes "convergent a"
  shows "convergent (\<lambda>n. ereal (a n))" and "lim (\<lambda>n. ereal (a n)) = ereal (lim a)"
proof -
  from assms obtain L where L: "a \<longlonglongrightarrow> L" unfolding convergent_def ..
  hence lim: "(\<lambda>n. ereal (a n)) \<longlonglongrightarrow> ereal L" using lim_ereal by auto
  thus "convergent (\<lambda>n. ereal (a n))" unfolding convergent_def ..
  thus "lim (\<lambda>n. ereal (a n)) = ereal (lim a)" using lim L limI by metis
qed

lemma tendsto_PInfty: "(f \<longlongrightarrow> \<infinity>) F \<longleftrightarrow> (\<forall>r. eventually (\<lambda>x. ereal r < f x) F)"
proof -
  {
    fix l :: ereal
    assume "\<forall>r. eventually (\<lambda>x. ereal r < f x) F"
    from this[THEN spec, of "real_of_ereal l"] have "l \<noteq> \<infinity> \<Longrightarrow> eventually (\<lambda>x. l < f x) F"
      by (cases l) (auto elim: eventually_mono)
  }
  then show ?thesis
    by (auto simp: order_tendsto_iff)
qed

lemma tendsto_PInfty': "(f \<longlongrightarrow> \<infinity>) F = (\<forall>r>c. eventually (\<lambda>x. ereal r < f x) F)"
proof (subst tendsto_PInfty, intro iffI allI impI)
  assume A: "\<forall>r>c. eventually (\<lambda>x. ereal r < f x) F"
  fix r :: real
  from A have A: "eventually (\<lambda>x. ereal r < f x) F" if "r > c" for r using that by blast
  show "eventually (\<lambda>x. ereal r < f x) F"
  proof (cases "r > c")
    case False
    hence B: "ereal r \<le> ereal (c + 1)" by simp
    have "c < c + 1" by simp
    from A[OF this] show "eventually (\<lambda>x. ereal r < f x) F"
      by eventually_elim (rule le_less_trans[OF B])
  qed (simp add: A)
qed simp

lemma tendsto_PInfty_eq_at_top:
  "((\<lambda>z. ereal (f z)) \<longlongrightarrow> \<infinity>) F \<longleftrightarrow> (LIM z F. f z :> at_top)"
  unfolding tendsto_PInfty filterlim_at_top_dense by simp

lemma tendsto_MInfty: "(f \<longlongrightarrow> -\<infinity>) F \<longleftrightarrow> (\<forall>r. eventually (\<lambda>x. f x < ereal r) F)"
  unfolding tendsto_def
proof safe
  fix S :: "ereal set"
  assume "open S" "-\<infinity> \<in> S"
  from open_MInfty[OF this] obtain B where "{..<ereal B} \<subseteq> S" ..
  moreover
  assume "\<forall>r::real. eventually (\<lambda>z. f z < r) F"
  then have "eventually (\<lambda>z. f z \<in> {..< B}) F"
    by auto
  ultimately show "eventually (\<lambda>z. f z \<in> S) F"
    by (auto elim!: eventually_mono)
next
  fix x
  assume "\<forall>S. open S \<longrightarrow> -\<infinity> \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F"
  from this[rule_format, of "{..< ereal x}"] show "eventually (\<lambda>y. f y < ereal x) F"
    by auto
qed

lemma tendsto_MInfty': "(f \<longlongrightarrow> -\<infinity>) F = (\<forall>r<c. eventually (\<lambda>x. ereal r > f x) F)"
proof (subst tendsto_MInfty, intro iffI allI impI)
  assume A: "\<forall>r<c. eventually (\<lambda>x. ereal r > f x) F"
  fix r :: real
  from A have A: "eventually (\<lambda>x. ereal r > f x) F" if "r < c" for r using that by blast
  show "eventually (\<lambda>x. ereal r > f x) F"
  proof (cases "r < c")
    case False
    hence B: "ereal r \<ge> ereal (c - 1)" by simp
    have "c > c - 1" by simp
    from A[OF this] show "eventually (\<lambda>x. ereal r > f x) F"
      by eventually_elim (erule less_le_trans[OF _ B])
  qed (simp add: A)
qed simp

lemma Lim_PInfty: "f \<longlonglongrightarrow> \<infinity> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. f n \<ge> ereal B)"
  unfolding tendsto_PInfty eventually_sequentially
proof safe
  fix r
  assume "\<forall>r. \<exists>N. \<forall>n\<ge>N. ereal r \<le> f n"
  then obtain N where "\<forall>n\<ge>N. ereal (r + 1) \<le> f n"
    by blast
  moreover have "ereal r < ereal (r + 1)"
    by auto
  ultimately show "\<exists>N. \<forall>n\<ge>N. ereal r < f n"
    by (blast intro: less_le_trans)
qed (blast intro: less_imp_le)

lemma Lim_MInfty: "f \<longlonglongrightarrow> -\<infinity> \<longleftrightarrow> (\<forall>B. \<exists>N. \<forall>n\<ge>N. ereal B \<ge> f n)"
  unfolding tendsto_MInfty eventually_sequentially
proof safe
  fix r
  assume "\<forall>r. \<exists>N. \<forall>n\<ge>N. f n \<le> ereal r"
  then obtain N where "\<forall>n\<ge>N. f n \<le> ereal (r - 1)"
    by blast
  moreover have "ereal (r - 1) < ereal r"
    by auto
  ultimately show "\<exists>N. \<forall>n\<ge>N. f n < ereal r"
    by (blast intro: le_less_trans)
qed (blast intro: less_imp_le)

lemma Lim_bounded_PInfty: "f \<longlonglongrightarrow> l \<Longrightarrow> (\<And>n. f n \<le> ereal B) \<Longrightarrow> l \<noteq> \<infinity>"
  using LIMSEQ_le_const2[of f l "ereal B"] by auto

lemma Lim_bounded_MInfty: "f \<longlonglongrightarrow> l \<Longrightarrow> (\<And>n. ereal B \<le> f n) \<Longrightarrow> l \<noteq> -\<infinity>"
  using LIMSEQ_le_const[of f l "ereal B"] by auto

lemma tendsto_zero_erealI:
  assumes "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>x. \<bar>f x\<bar> < ereal e) F"
  shows   "(f \<longlongrightarrow> 0) F"
proof (subst filterlim_cong[OF refl refl])
  from assms[OF zero_less_one] show "eventually (\<lambda>x. f x = ereal (real_of_ereal (f x))) F"
    by eventually_elim (auto simp: ereal_real)
  hence "eventually (\<lambda>x. abs (real_of_ereal (f x)) < e) F" if "e > 0" for e using assms[OF that]
    by eventually_elim (simp add: real_less_ereal_iff that)
  hence "((\<lambda>x. real_of_ereal (f x)) \<longlongrightarrow> 0) F" unfolding tendsto_iff
    by (auto simp: tendsto_iff dist_real_def)
  thus "((\<lambda>x. ereal (real_of_ereal (f x))) \<longlongrightarrow> 0) F" by (simp add: zero_ereal_def)
qed

lemma Lim_bounded_PInfty2: "f \<longlonglongrightarrow> l \<Longrightarrow> \<forall>n\<ge>N. f n \<le> ereal B \<Longrightarrow> l \<noteq> \<infinity>"
  using LIMSEQ_le_const2[of f l "ereal B"] by fastforce

lemma real_of_ereal_mult[simp]:
  fixes a b :: ereal
  shows "real_of_ereal (a * b) = real_of_ereal a * real_of_ereal b"
  by (cases rule: ereal2_cases[of a b]) auto

lemma real_of_ereal_eq_0:
  fixes x :: ereal
  shows "real_of_ereal x = 0 \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity> \<or> x = 0"
  by (cases x) auto

lemma tendsto_ereal_realD:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "x \<noteq> 0"
    and tendsto: "((\<lambda>x. ereal (real_of_ereal (f x))) \<longlongrightarrow> x) net"
  shows "(f \<longlongrightarrow> x) net"
proof (intro topological_tendstoI)
  fix S
  assume S: "open S" "x \<in> S"
  with \<open>x \<noteq> 0\<close> have "open (S - {0})" "x \<in> S - {0}"
    by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_rev_mp) (auto simp: ereal_real)
qed

lemma tendsto_ereal_realI:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and tendsto: "(f \<longlongrightarrow> x) net"
  shows "((\<lambda>x. ereal (real_of_ereal (f x))) \<longlongrightarrow> x) net"
proof (intro topological_tendstoI)
  fix S
  assume "open S" and "x \<in> S"
  with x have "open (S - {\<infinity>, -\<infinity>})" "x \<in> S - {\<infinity>, -\<infinity>}"
    by auto
  from tendsto[THEN topological_tendstoD, OF this]
  show "eventually (\<lambda>x. ereal (real_of_ereal (f x)) \<in> S) net"
    by (elim eventually_mono) (auto simp: ereal_real)
qed

lemma ereal_mult_cancel_left:
  fixes a b c :: ereal
  shows "a * b = a * c \<longleftrightarrow> (\<bar>a\<bar> = \<infinity> \<and> 0 < b * c) \<or> a = 0 \<or> b = c"
  by (cases rule: ereal3_cases[of a b c]) (simp_all add: zero_less_mult_iff)

lemma tendsto_add_ereal:
  fixes x y :: ereal
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and y: "\<bar>y\<bar> \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof -
  from x obtain r where x': "x = ereal r" by (cases x) auto
  with f have "((\<lambda>i. real_of_ereal (f i)) \<longlongrightarrow> r) F" by simp
  moreover
  from y obtain p where y': "y = ereal p" by (cases y) auto
  with g have "((\<lambda>i. real_of_ereal (g i)) \<longlongrightarrow> p) F" by simp
  ultimately have "((\<lambda>i. real_of_ereal (f i) + real_of_ereal (g i)) \<longlongrightarrow> r + p) F"
    by (rule tendsto_add)
  moreover
  from eventually_finite[OF x f] eventually_finite[OF y g]
  have "eventually (\<lambda>x. f x + g x = ereal (real_of_ereal (f x) + real_of_ereal (g x))) F"
    by eventually_elim auto
  ultimately show ?thesis
    by (simp add: x' y' cong: filterlim_cong)
qed

lemma tendsto_add_ereal_nonneg:
  fixes x y :: "ereal"
  assumes "x \<noteq> -\<infinity>" "y \<noteq> -\<infinity>" "(f \<longlongrightarrow> x) F" "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof cases
  assume "x = \<infinity> \<or> y = \<infinity>"
  moreover
  { fix y :: ereal and f g :: "'a \<Rightarrow> ereal" assume "y \<noteq> -\<infinity>" "(f \<longlongrightarrow> \<infinity>) F" "(g \<longlongrightarrow> y) F"
    then obtain y' where "-\<infinity> < y'" "y' < y"
      using dense[of "-\<infinity>" y] by auto
    have "((\<lambda>x. f x + g x) \<longlongrightarrow> \<infinity>) F"
    proof (rule tendsto_sandwich)
      have "\<forall>\<^sub>F x in F. y' < g x"
        using order_tendstoD(1)[OF \<open>(g \<longlongrightarrow> y) F\<close> \<open>y' < y\<close>] by auto
      then show "\<forall>\<^sub>F x in F. f x + y' \<le> f x + g x"
        by eventually_elim (auto intro!: add_mono)
      show "\<forall>\<^sub>F n in F. f n + g n \<le> \<infinity>" "((\<lambda>n. \<infinity>) \<longlongrightarrow> \<infinity>) F"
        by auto
      show "((\<lambda>x. f x + y') \<longlongrightarrow> \<infinity>) F"
        using tendsto_cadd_ereal[of y' \<infinity> f F] \<open>(f \<longlongrightarrow> \<infinity>) F\<close> \<open>-\<infinity> < y'\<close> by auto
    qed }
  note this[of y f g] this[of x g f]
  ultimately show ?thesis
    using assms by (auto simp: add_ac)
next
  assume "\<not> (x = \<infinity> \<or> y = \<infinity>)"
  with assms tendsto_add_ereal[of x y f F g]
  show ?thesis
    by auto
qed

lemma ereal_inj_affinity:
  fixes m t :: ereal
  assumes "\<bar>m\<bar> \<noteq> \<infinity>"
    and "m \<noteq> 0"
    and "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "inj_on (\<lambda>x. m * x + t) A"
  using assms
  by (cases rule: ereal2_cases[of m t])
     (auto intro!: inj_onI simp: ereal_add_cancel_right ereal_mult_cancel_left)

lemma ereal_PInfty_eq_plus[simp]:
  fixes a b :: ereal
  shows "\<infinity> = a + b \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_MInfty_eq_plus[simp]:
  fixes a b :: ereal
  shows "-\<infinity> = a + b \<longleftrightarrow> (a = -\<infinity> \<and> b \<noteq> \<infinity>) \<or> (b = -\<infinity> \<and> a \<noteq> \<infinity>)"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_less_divide_pos:
  fixes x y :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y < z / x \<longleftrightarrow> x * y < z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_less_pos:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> x \<noteq> \<infinity> \<Longrightarrow> y / x < z \<longleftrightarrow> y < x * z"
  by (cases rule: ereal3_cases[of x y z]) (auto simp: field_simps)

lemma ereal_divide_eq:
  fixes a b c :: ereal
  shows "b \<noteq> 0 \<Longrightarrow> \<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> a / b = c \<longleftrightarrow> a = b * c"
  by (cases rule: ereal3_cases[of a b c])
     (simp_all add: field_simps)

lemma ereal_inverse_not_MInfty[simp]: "inverse (a::ereal) \<noteq> -\<infinity>"
  by (cases a) auto

lemma ereal_mult_m1[simp]: "x * ereal (-1) = -x"
  by (cases x) auto

lemma ereal_real':
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "ereal (real_of_ereal x) = x"
  using assms by auto

lemma real_ereal_id: "real_of_ereal \<circ> ereal = id"
proof -
  {
    fix x
    have "(real_of_ereal \<circ> ereal) x = id x"
      by auto
  }
  then show ?thesis
    using ext by blast
qed

lemma open_image_ereal: "open(UNIV-{ \<infinity> , (-\<infinity> :: ereal)})"
  by (metis range_ereal open_ereal open_UNIV)

lemma ereal_le_distrib:
  fixes a b c :: ereal
  shows "c * (a + b) \<le> c * a + c * b"
  by (cases rule: ereal3_cases[of a b c])
     (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_pos_distrib:
  fixes a b c :: ereal
  assumes "0 \<le> c"
    and "c \<noteq> \<infinity>"
  shows "c * (a + b) = c * a + c * b"
  using assms
  by (cases rule: ereal3_cases[of a b c])
    (auto simp add: field_simps not_le mult_le_0_iff mult_less_0_iff)

lemma ereal_LimI_finite:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
    and "\<And>r. 0 < r \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r"
  shows "u \<longlonglongrightarrow> x"
proof (rule topological_tendstoI, unfold eventually_sequentially)
  obtain rx where rx: "x = ereal rx"
    using assms by (cases x) auto
  fix S
  assume "open S" and "x \<in> S"
  then have "open (ereal -` S)"
    unfolding open_ereal_def by auto
  with \<open>x \<in> S\<close> obtain r where "0 < r" and dist: "dist y rx < r \<Longrightarrow> ereal y \<in> S" for y
    unfolding open_dist rx by auto
  then obtain n
    where upper: "u N < x + ereal r"
      and lower: "x < u N + ereal r"
      if "n \<le> N" for N
    using assms(2)[of "ereal r"] by auto
  show "\<exists>N. \<forall>n\<ge>N. u n \<in> S"
  proof (safe intro!: exI[of _ n])
    fix N
    assume "n \<le> N"
    from upper[OF this] lower[OF this] assms \<open>0 < r\<close>
    have "u N \<notin> {\<infinity>,(-\<infinity>)}"
      by auto
    then obtain ra where ra_def: "(u N) = ereal ra"
      by (cases "u N") auto
    then have "rx < ra + r" and "ra < rx + r"
      using rx assms \<open>0 < r\<close> lower[OF \<open>n \<le> N\<close>] upper[OF \<open>n \<le> N\<close>]
      by auto
    then have "dist (real_of_ereal (u N)) rx < r"
      using rx ra_def
      by (auto simp: dist_real_def abs_diff_less_iff field_simps)
    from dist[OF this] show "u N \<in> S"
      using \<open>u N  \<notin> {\<infinity>, -\<infinity>}\<close>
      by (auto simp: ereal_real split: if_split_asm)
  qed
qed

lemma tendsto_obtains_N:
  assumes "f \<longlonglongrightarrow> f0"
  assumes "open S"
    and "f0 \<in> S"
  obtains N where "\<forall>n\<ge>N. f n \<in> S"
  using assms using tendsto_def
  using lim_explicit[of f f0] assms by auto

lemma ereal_LimI_finite_iff:
  fixes x :: ereal
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "u \<longlonglongrightarrow> x \<longleftrightarrow> (\<forall>r. 0 < r \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume lim: "u \<longlonglongrightarrow> x"
  {
    fix r :: ereal
    assume "r > 0"
    then obtain N where "\<forall>n\<ge>N. u n \<in> {x - r <..< x + r}"
       apply (subst tendsto_obtains_N[of u x "{x - r <..< x + r}"])
       using lim ereal_between[of x r] assms \<open>r > 0\<close>
       apply auto
       done
    then have "\<exists>N. \<forall>n\<ge>N. u n < x + r \<and> x < u n + r"
      using ereal_minus_less[of r x]
      by (cases r) auto
  }
  then show ?rhs
    by auto
next
  assume ?rhs
  then show "u \<longlonglongrightarrow> x"
    using ereal_LimI_finite[of x] assms by auto
qed

lemma ereal_Limsup_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "Limsup net (\<lambda>x. - (f x)) = - Liminf net f"
  unfolding Limsup_def Liminf_def ereal_SUP_uminus ereal_INF_uminus_eq ..

lemma liminf_bounded_iff:
  fixes x :: "nat \<Rightarrow> ereal"
  shows "C \<le> liminf x \<longleftrightarrow> (\<forall>B<C. \<exists>N. \<forall>n\<ge>N. B < x n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  unfolding le_Liminf_iff eventually_sequentially ..

lemma Liminf_add_le:
  fixes f g :: "_ \<Rightarrow> ereal"
  assumes F: "F \<noteq> bot"
  assumes ev: "eventually (\<lambda>x. 0 \<le> f x) F" "eventually (\<lambda>x. 0 \<le> g x) F"
  shows "Liminf F f + Liminf F g \<le> Liminf F (\<lambda>x. f x + g x)"
  unfolding Liminf_def
proof (subst SUP_ereal_add_left[symmetric])
  let ?F = "{P. eventually P F}"
  let ?INF = "\<lambda>P g. Inf (g ` (Collect P))"
  show "?F \<noteq> {}"
    by (auto intro: eventually_True)
  show "(SUP P\<in>?F. ?INF P g) \<noteq> - \<infinity>"
    unfolding bot_ereal_def[symmetric] SUP_bot_conv INF_eq_bot_iff
    by (auto intro!: exI[of _ 0] ev simp: bot_ereal_def)
  have "(SUP P\<in>?F. ?INF P f + (SUP P\<in>?F. ?INF P g)) \<le> (SUP P\<in>?F. (SUP P'\<in>?F. ?INF P f + ?INF P' g))"
  proof (safe intro!: SUP_mono bexI[of _ "\<lambda>x. P x \<and> 0 \<le> f x" for P])
    fix P let ?P' = "\<lambda>x. P x \<and> 0 \<le> f x"
    assume "eventually P F"
    with ev show "eventually ?P' F"
      by eventually_elim auto
    have "?INF P f + (SUP P\<in>?F. ?INF P g) \<le> ?INF ?P' f + (SUP P\<in>?F. ?INF P g)"
      by (intro add_mono INF_mono) auto
    also have "\<dots> = (SUP P'\<in>?F. ?INF ?P' f + ?INF P' g)"
    proof (rule SUP_ereal_add_right[symmetric])
      show "Inf (f ` {x. P x \<and> 0 \<le> f x}) \<noteq> - \<infinity>"
        unfolding bot_ereal_def[symmetric] INF_eq_bot_iff
        by (auto intro!: exI[of _ 0] ev simp: bot_ereal_def)
    qed fact
    finally show "?INF P f + (SUP P\<in>?F. ?INF P g) \<le> (SUP P'\<in>?F. ?INF ?P' f + ?INF P' g)" .
  qed
  also have "\<dots> \<le> (SUP P\<in>?F. INF x\<in>Collect P. f x + g x)"
  proof (safe intro!: SUP_least)
    fix P Q assume *: "eventually P F" "eventually Q F"
    show "?INF P f + ?INF Q g \<le> (SUP P\<in>?F. INF x\<in>Collect P. f x + g x)"
    proof (rule SUP_upper2)
      show "(\<lambda>x. P x \<and> Q x) \<in> ?F"
        using * by (auto simp: eventually_conj)
      show "?INF P f + ?INF Q g \<le> (INF x\<in>{x. P x \<and> Q x}. f x + g x)"
        by (intro INF_greatest add_mono) (auto intro: INF_lower)
    qed
  qed
  finally show "(SUP P\<in>?F. ?INF P f + (SUP P\<in>?F. ?INF P g)) \<le> (SUP P\<in>?F. INF x\<in>Collect P. f x + g x)" .
qed

lemma Sup_ereal_mult_right':
  assumes nonempty: "Y \<noteq> {}"
  and x: "x \<ge> 0"
  shows "(SUP i\<in>Y. f i) * ereal x = (SUP i\<in>Y. f i * ereal x)" (is "?lhs = ?rhs")
proof(cases "x = 0")
  case True thus ?thesis by(auto simp add: nonempty zero_ereal_def[symmetric])
next
  case False
  show ?thesis
  proof(rule antisym)
    show "?rhs \<le> ?lhs"
      by(rule SUP_least)(simp add: ereal_mult_right_mono SUP_upper x)
  next
    have "?lhs / ereal x = (SUP i\<in>Y. f i) * (ereal x / ereal x)" by(simp only: ereal_times_divide_eq)
    also have "\<dots> = (SUP i\<in>Y. f i)" using False by simp
    also have "\<dots> \<le> ?rhs / x"
    proof(rule SUP_least)
      fix i
      assume "i \<in> Y"
      have "f i = f i * (ereal x / ereal x)" using False by simp
      also have "\<dots> = f i * x / x" by(simp only: ereal_times_divide_eq)
      also from \<open>i \<in> Y\<close> have "f i * x \<le> ?rhs" by(rule SUP_upper)
      hence "f i * x / x \<le> ?rhs / x" using x False by simp
      finally show "f i \<le> ?rhs / x" .
    qed
    finally have "(?lhs / x) * x \<le> (?rhs / x) * x"
      by(rule ereal_mult_right_mono)(simp add: x)
    also have "\<dots> = ?rhs" using False ereal_divide_eq mult.commute by force
    also have "(?lhs / x) * x = ?lhs" using False ereal_divide_eq mult.commute by force
    finally show "?lhs \<le> ?rhs" .
  qed
qed

lemma Sup_ereal_mult_left':
  "\<lbrakk> Y \<noteq> {}; x \<ge> 0 \<rbrakk> \<Longrightarrow> ereal x * (SUP i\<in>Y. f i) = (SUP i\<in>Y. ereal x * f i)"
by(subst (1 2) mult.commute)(rule Sup_ereal_mult_right')

lemma sup_continuous_add[order_continuous_intros]:
  fixes f g :: "'a::complete_lattice \<Rightarrow> ereal"
  assumes nn: "\<And>x. 0 \<le> f x" "\<And>x. 0 \<le> g x" and cont: "sup_continuous f" "sup_continuous g"
  shows "sup_continuous (\<lambda>x. f x + g x)"
  unfolding sup_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'a" assume "incseq M"
  then show "f (SUP i. M i) + g (SUP i. M i) = (SUP i. f (M i) + g (M i))"
    using SUP_ereal_add_pos[of "\<lambda>i. f (M i)" "\<lambda>i. g (M i)"] nn
      cont[THEN sup_continuous_mono] cont[THEN sup_continuousD]
    by (auto simp: mono_def)
qed

lemma sup_continuous_mult_right[order_continuous_intros]:
  "0 \<le> c \<Longrightarrow> c < \<infinity> \<Longrightarrow> sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. f x * c :: ereal)"
  by (cases c) (auto simp: sup_continuous_def fun_eq_iff Sup_ereal_mult_right')

lemma sup_continuous_mult_left[order_continuous_intros]:
  "0 \<le> c \<Longrightarrow> c < \<infinity> \<Longrightarrow> sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. c * f x :: ereal)"
  using sup_continuous_mult_right[of c f] by (simp add: mult_ac)

lemma sup_continuous_ereal_of_enat[order_continuous_intros]:
  assumes f: "sup_continuous f" shows "sup_continuous (\<lambda>x. ereal_of_enat (f x))"
  by (rule sup_continuous_compose[OF _ f])
     (auto simp: sup_continuous_def ereal_of_enat_SUP)

subsubsection \<open>Sums\<close>

lemma sums_ereal_positive:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
  shows "f sums (SUP n. \<Sum>i<n. f i)"
proof -
  have "incseq (\<lambda>i. \<Sum>j=0..<i. f j)"
    using add_mono[OF _ assms]
    by (auto intro!: incseq_SucI)
  from LIMSEQ_SUP[OF this]
  show ?thesis unfolding sums_def
    by (simp add: atLeast0LessThan)
qed

lemma summable_ereal_pos:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
  shows "summable f"
  using sums_ereal_positive[of f, OF assms]
  unfolding summable_def
  by auto

lemma sums_ereal: "(\<lambda>x. ereal (f x)) sums ereal x \<longleftrightarrow> f sums x"
  unfolding sums_def by simp

lemma suminf_ereal_eq_SUP:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
  shows "(\<Sum>x. f x) = (SUP n. \<Sum>i<n. f i)"
  using sums_ereal_positive[of f, OF assms, THEN sums_unique]
  by simp

lemma suminf_bound:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<forall>N. (\<Sum>n<N. f n) \<le> x"
    and pos: "\<And>n. 0 \<le> f n"
  shows "suminf f \<le> x"
proof (rule Lim_bounded)
  have "summable f" using pos[THEN summable_ereal_pos] .
  then show "(\<lambda>N. \<Sum>n<N. f n) \<longlonglongrightarrow> suminf f"
    by (auto dest!: summable_sums simp: sums_def atLeast0LessThan)
  show "\<forall>n\<ge>0. sum f {..<n} \<le> x"
    using assms by auto
qed

lemma suminf_bound_add:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<forall>N. (\<Sum>n<N. f n) + y \<le> x"
    and pos: "\<And>n. 0 \<le> f n"
    and "y \<noteq> -\<infinity>"
  shows "suminf f + y \<le> x"
proof (cases y)
  case (real r)
  then have "\<forall>N. (\<Sum>n<N. f n) \<le> x - y"
    using assms by (simp add: ereal_le_minus)
  then have "(\<Sum> n. f n) \<le> x - y"
    using pos by (rule suminf_bound)
  then show "(\<Sum> n. f n) + y \<le> x"
    using assms real by (simp add: ereal_le_minus)
qed (insert assms, auto)

lemma suminf_upper:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>n. 0 \<le> f n"
  shows "(\<Sum>n<N. f n) \<le> (\<Sum>n. f n)"
  unfolding suminf_ereal_eq_SUP [OF assms]
  by (auto intro: complete_lattice_class.SUP_upper)

lemma suminf_0_le:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>n. 0 \<le> f n"
  shows "0 \<le> (\<Sum>n. f n)"
  using suminf_upper[of f 0, OF assms]
  by simp

lemma suminf_le_pos:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes "\<And>N. f N \<le> g N"
    and "\<And>N. 0 \<le> f N"
  shows "suminf f \<le> suminf g"
proof (safe intro!: suminf_bound)
  fix n
  {
    fix N
    have "0 \<le> g N"
      using assms(2,1)[of N] by auto
  }
  have "sum f {..<n} \<le> sum g {..<n}"
    using assms by (auto intro: sum_mono)
  also have "\<dots> \<le> suminf g"
    using \<open>\<And>N. 0 \<le> g N\<close>
    by (rule suminf_upper)
  finally show "sum f {..<n} \<le> suminf g" .
qed (rule assms(2))

lemma suminf_half_series_ereal: "(\<Sum>n. (1/2 :: ereal) ^ Suc n) = 1"
  using sums_ereal[THEN iffD2, OF power_half_series, THEN sums_unique, symmetric]
  by (simp add: one_ereal_def)

lemma suminf_add_ereal:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(\<Sum>i. f i + g i) = suminf f + suminf g"
proof -
  have "(SUP n. \<Sum>i<n. f i + g i) = (SUP n. sum f {..<n}) + (SUP n. sum g {..<n})"
    unfolding sum.distrib
    by (intro assms add_nonneg_nonneg SUP_ereal_add_pos incseq_sumI sum_nonneg ballI)
  with assms show ?thesis
    by (subst (1 2 3) suminf_ereal_eq_SUP) auto
qed

lemma suminf_cmult_ereal:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
    and "0 \<le> a"
  shows "(\<Sum>i. a * f i) = a * suminf f"
  by (auto simp: sum_ereal_right_distrib[symmetric] assms
       ereal_zero_le_0_iff sum_nonneg suminf_ereal_eq_SUP
       intro!: SUP_ereal_mult_left)

lemma suminf_PInfty:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "\<And>i. 0 \<le> f i"
    and "suminf f \<noteq> \<infinity>"
  shows "f i \<noteq> \<infinity>"
proof -
  from suminf_upper[of f "Suc i", OF assms(1)] assms(2)
  have "(\<Sum>i<Suc i. f i) \<noteq> \<infinity>"
    by auto
  then show ?thesis
    unfolding sum_Pinfty by simp
qed

lemma suminf_PInfty_fun:
  assumes "\<And>i. 0 \<le> f i"
    and "suminf f \<noteq> \<infinity>"
  shows "\<exists>f'. f = (\<lambda>x. ereal (f' x))"
proof -
  have "\<forall>i. \<exists>r. f i = ereal r"
  proof
    fix i
    show "\<exists>r. f i = ereal r"
      using suminf_PInfty[OF assms] assms(1)[of i]
      by (cases "f i") auto
  qed
  from choice[OF this] show ?thesis
    by auto
qed

lemma summable_ereal:
  assumes "\<And>i. 0 \<le> f i"
    and "(\<Sum>i. ereal (f i)) \<noteq> \<infinity>"
  shows "summable f"
proof -
  have "0 \<le> (\<Sum>i. ereal (f i))"
    using assms by (intro suminf_0_le) auto
  with assms obtain r where r: "(\<Sum>i. ereal (f i)) = ereal r"
    by (cases "\<Sum>i. ereal (f i)") auto
  from summable_ereal_pos[of "\<lambda>x. ereal (f x)"]
  have "summable (\<lambda>x. ereal (f x))"
    using assms by auto
  from summable_sums[OF this]
  have "(\<lambda>x. ereal (f x)) sums (\<Sum>x. ereal (f x))"
    by auto
  then show "summable f"
    unfolding r sums_ereal summable_def ..
qed

lemma suminf_ereal:
  assumes "\<And>i. 0 \<le> f i"
    and "(\<Sum>i. ereal (f i)) \<noteq> \<infinity>"
  shows "(\<Sum>i. ereal (f i)) = ereal (suminf f)"
proof (rule sums_unique[symmetric])
  from summable_ereal[OF assms]
  show "(\<lambda>x. ereal (f x)) sums (ereal (suminf f))"
    unfolding sums_ereal
    using assms
    by (intro summable_sums summable_ereal)
qed

lemma suminf_ereal_minus:
  fixes f g :: "nat \<Rightarrow> ereal"
  assumes ord: "\<And>i. g i \<le> f i" "\<And>i. 0 \<le> g i"
    and fin: "suminf f \<noteq> \<infinity>" "suminf g \<noteq> \<infinity>"
  shows "(\<Sum>i. f i - g i) = suminf f - suminf g"
proof -
  {
    fix i
    have "0 \<le> f i"
      using ord[of i] by auto
  }
  moreover
  from suminf_PInfty_fun[OF \<open>\<And>i. 0 \<le> f i\<close> fin(1)] obtain f' where [simp]: "f = (\<lambda>x. ereal (f' x))" ..
  from suminf_PInfty_fun[OF \<open>\<And>i. 0 \<le> g i\<close> fin(2)] obtain g' where [simp]: "g = (\<lambda>x. ereal (g' x))" ..
  {
    fix i
    have "0 \<le> f i - g i"
      using ord[of i] by (auto simp: ereal_le_minus_iff)
  }
  moreover
  have "suminf (\<lambda>i. f i - g i) \<le> suminf f"
    using assms by (auto intro!: suminf_le_pos simp: field_simps)
  then have "suminf (\<lambda>i. f i - g i) \<noteq> \<infinity>"
    using fin by auto
  ultimately show ?thesis
    using assms \<open>\<And>i. 0 \<le> f i\<close>
    apply simp
    apply (subst (1 2 3) suminf_ereal)
    apply (auto intro!: suminf_diff[symmetric] summable_ereal)
    done
qed

lemma suminf_ereal_PInf [simp]: "(\<Sum>x. \<infinity>::ereal) = \<infinity>"
proof -
  have "(\<Sum>i<Suc 0. \<infinity>) \<le> (\<Sum>x. \<infinity>::ereal)"
    by (rule suminf_upper) auto
  then show ?thesis
    by simp
qed

lemma summable_real_of_ereal:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes f: "\<And>i. 0 \<le> f i"
    and fin: "(\<Sum>i. f i) \<noteq> \<infinity>"
  shows "summable (\<lambda>i. real_of_ereal (f i))"
proof (rule summable_def[THEN iffD2])
  have "0 \<le> (\<Sum>i. f i)"
    using assms by (auto intro: suminf_0_le)
  with fin obtain r where r: "ereal r = (\<Sum>i. f i)"
    by (cases "(\<Sum>i. f i)") auto
  {
    fix i
    have "f i \<noteq> \<infinity>"
      using f by (intro suminf_PInfty[OF _ fin]) auto
    then have "\<bar>f i\<bar> \<noteq> \<infinity>"
      using f[of i] by auto
  }
  note fin = this
  have "(\<lambda>i. ereal (real_of_ereal (f i))) sums (\<Sum>i. ereal (real_of_ereal (f i)))"
    using f
    by (auto intro!: summable_ereal_pos simp: ereal_le_real_iff zero_ereal_def)
  also have "\<dots> = ereal r"
    using fin r by (auto simp: ereal_real)
  finally show "\<exists>r. (\<lambda>i. real_of_ereal (f i)) sums r"
    by (auto simp: sums_ereal)
qed

lemma suminf_SUP_eq:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> ereal"
  assumes "\<And>i. incseq (\<lambda>n. f n i)"
    and "\<And>n i. 0 \<le> f n i"
  shows "(\<Sum>i. SUP n. f n i) = (SUP n. \<Sum>i. f n i)"
proof -
  have *: "\<And>n. (\<Sum>i<n. SUP k. f k i) = (SUP k. \<Sum>i<n. f k i)"
    using assms
    by (auto intro!: SUP_ereal_sum [symmetric])
  show ?thesis
    using assms
    apply (subst (1 2) suminf_ereal_eq_SUP)
    apply (auto intro!: SUP_upper2 SUP_commute simp: *)
    done
qed

lemma suminf_sum_ereal:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> ereal"
  assumes nonneg: "\<And>i a. a \<in> A \<Longrightarrow> 0 \<le> f i a"
  shows "(\<Sum>i. \<Sum>a\<in>A. f i a) = (\<Sum>a\<in>A. \<Sum>i. f i a)"
proof (cases "finite A")
  case True
  then show ?thesis
    using nonneg
    by induct (simp_all add: suminf_add_ereal sum_nonneg)
next
  case False
  then show ?thesis by simp
qed

lemma suminf_ereal_eq_0:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes nneg: "\<And>i. 0 \<le> f i"
  shows "(\<Sum>i. f i) = 0 \<longleftrightarrow> (\<forall>i. f i = 0)"
proof
  assume "(\<Sum>i. f i) = 0"
  {
    fix i
    assume "f i \<noteq> 0"
    with nneg have "0 < f i"
      by (auto simp: less_le)
    also have "f i = (\<Sum>j. if j = i then f i else 0)"
      by (subst suminf_finite[where N="{i}"]) auto
    also have "\<dots> \<le> (\<Sum>i. f i)"
      using nneg
      by (auto intro!: suminf_le_pos)
    finally have False
      using \<open>(\<Sum>i. f i) = 0\<close> by auto
  }
  then show "\<forall>i. f i = 0"
    by auto
qed simp

lemma suminf_ereal_offset_le:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes f: "\<And>i. 0 \<le> f i"
  shows "(\<Sum>i. f (i + k)) \<le> suminf f"
proof -
  have "(\<lambda>n. \<Sum>i<n. f (i + k)) \<longlonglongrightarrow> (\<Sum>i. f (i + k))"
    using summable_sums[OF summable_ereal_pos]
    by (simp add: sums_def atLeast0LessThan f)
  moreover have "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> (\<Sum>i. f i)"
    using summable_sums[OF summable_ereal_pos]
    by (simp add: sums_def atLeast0LessThan f)
  then have "(\<lambda>n. \<Sum>i<n + k. f i) \<longlonglongrightarrow> (\<Sum>i. f i)"
    by (rule LIMSEQ_ignore_initial_segment)
  ultimately show ?thesis
  proof (rule LIMSEQ_le, safe intro!: exI[of _ k])
    fix n assume "k \<le> n"
    have "(\<Sum>i<n. f (i + k)) = (\<Sum>i<n. (f \<circ> plus k) i)"
      by (simp add: ac_simps)
    also have "\<dots> = (\<Sum>i\<in>(plus k) ` {..<n}. f i)"
      by (rule sum.reindex [symmetric]) simp
    also have "\<dots> \<le> sum f {..<n + k}"
      by (intro sum_mono2) (auto simp: f)
    finally show "(\<Sum>i<n. f (i + k)) \<le> sum f {..<n + k}" .
  qed
qed

lemma sums_suminf_ereal: "f sums x \<Longrightarrow> (\<Sum>i. ereal (f i)) = ereal x"
  by (metis sums_ereal sums_unique)

lemma suminf_ereal': "summable f \<Longrightarrow> (\<Sum>i. ereal (f i)) = ereal (\<Sum>i. f i)"
  by (metis sums_ereal sums_unique summable_def)

lemma suminf_ereal_finite: "summable f \<Longrightarrow> (\<Sum>i. ereal (f i)) \<noteq> \<infinity>"
  by (auto simp: summable_def simp flip: sums_ereal sums_unique)

lemma suminf_ereal_finite_neg:
  assumes "summable f"
  shows "(\<Sum>x. ereal (f x)) \<noteq> -\<infinity>"
proof-
  from assms obtain x where "f sums x" by blast
  hence "(\<lambda>x. ereal (f x)) sums ereal x" by (simp add: sums_ereal)
  from sums_unique[OF this] have "(\<Sum>x. ereal (f x)) = ereal x" ..
  thus "(\<Sum>x. ereal (f x)) \<noteq> -\<infinity>" by simp_all
qed

lemma SUP_ereal_add_directed:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes nonneg: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> g i"
  assumes directed: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<exists>k\<in>I. f i + g j \<le> f k + g k"
  shows "(SUP i\<in>I. f i + g i) = (SUP i\<in>I. f i) + (SUP i\<in>I. g i)"
proof cases
  assume "I = {}" then show ?thesis
    by (simp add: bot_ereal_def)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (rule antisym)
    show "(SUP i\<in>I. f i + g i) \<le> (SUP i\<in>I. f i) + (SUP i\<in>I. g i)"
      by (rule SUP_least; intro add_mono SUP_upper)
  next
    have "bot < (SUP i\<in>I. g i)"
      using \<open>I \<noteq> {}\<close> nonneg(2) by (auto simp: bot_ereal_def less_SUP_iff)
    then have "(SUP i\<in>I. f i) + (SUP i\<in>I. g i) = (SUP i\<in>I. f i + (SUP i\<in>I. g i))"
      by (intro SUP_ereal_add_left[symmetric] \<open>I \<noteq> {}\<close>) auto
    also have "\<dots> = (SUP i\<in>I. (SUP j\<in>I. f i + g j))"
      using nonneg(1) \<open>I \<noteq> {}\<close> by (simp add: SUP_ereal_add_right)
    also have "\<dots> \<le> (SUP i\<in>I. f i + g i)"
      using directed by (intro SUP_least) (blast intro: SUP_upper2)
    finally show "(SUP i\<in>I. f i) + (SUP i\<in>I. g i) \<le> (SUP i\<in>I. f i + g i)" .
  qed
qed

lemma SUP_ereal_sum_directed:
  fixes f g :: "'a \<Rightarrow> 'b \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes directed: "\<And>N i j. N \<subseteq> A \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<exists>k\<in>I. \<forall>n\<in>N. f n i \<le> f n k \<and> f n j \<le> f n k"
  assumes nonneg: "\<And>n i. i \<in> I \<Longrightarrow> n \<in> A \<Longrightarrow> 0 \<le> f n i"
  shows "(SUP i\<in>I. \<Sum>n\<in>A. f n i) = (\<Sum>n\<in>A. SUP i\<in>I. f n i)"
proof -
  have "N \<subseteq> A \<Longrightarrow> (SUP i\<in>I. \<Sum>n\<in>N. f n i) = (\<Sum>n\<in>N. SUP i\<in>I. f n i)" for N
  proof (induction N rule: infinite_finite_induct)
    case (insert n N)
    have "(SUP i\<in>I. f n i + (\<Sum>l\<in>N. f l i)) = (SUP i\<in>I. f n i) + (SUP i\<in>I. \<Sum>l\<in>N. f l i)"
    proof (rule SUP_ereal_add_directed)
      fix i assume "i \<in> I" then show "0 \<le> f n i" "0 \<le> (\<Sum>l\<in>N. f l i)"
        using insert by (auto intro!: sum_nonneg nonneg)
    next
      fix i j assume "i \<in> I" "j \<in> I"
      from directed[OF insert(4) this]
      show "\<exists>k\<in>I. f n i + (\<Sum>l\<in>N. f l j) \<le> f n k + (\<Sum>l\<in>N. f l k)"
        by (auto intro!: add_mono sum_mono)
    qed
    with insert show ?case
      by simp
  qed (simp_all add: SUP_constant \<open>I \<noteq> {}\<close>)
  from this[of A] show ?thesis by simp
qed

lemma suminf_SUP_eq_directed:
  fixes f :: "_ \<Rightarrow> nat \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes directed: "\<And>N i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> finite N \<Longrightarrow> \<exists>k\<in>I. \<forall>n\<in>N. f i n \<le> f k n \<and> f j n \<le> f k n"
  assumes nonneg: "\<And>n i. 0 \<le> f n i"
  shows "(\<Sum>i. SUP n\<in>I. f n i) = (SUP n\<in>I. \<Sum>i. f n i)"
proof (subst (1 2) suminf_ereal_eq_SUP)
  show "\<And>n i. 0 \<le> f n i" "\<And>i. 0 \<le> (SUP n\<in>I. f n i)"
    using \<open>I \<noteq> {}\<close> nonneg by (auto intro: SUP_upper2)
  show "(SUP n. \<Sum>i<n. SUP n\<in>I. f n i) = (SUP n\<in>I. SUP j. \<Sum>i<j. f n i)"
    by (auto simp: finite_subset SUP_commute SUP_ereal_sum_directed assms)
qed

lemma ereal_dense3:
  fixes x y :: ereal
  shows "x < y \<Longrightarrow> \<exists>r::rat. x < real_of_rat r \<and> real_of_rat r < y"
proof (cases x y rule: ereal2_cases, simp_all)
  fix r q :: real
  assume "r < q"
  from Rats_dense_in_real[OF this] show "\<exists>x. r < real_of_rat x \<and> real_of_rat x < q"
    by (fastforce simp: Rats_def)
next
  fix r :: real
  show "\<exists>x. r < real_of_rat x" "\<exists>x. real_of_rat x < r"
    using gt_ex[of r] lt_ex[of r] Rats_dense_in_real
    by (auto simp: Rats_def)
qed

lemma continuous_within_ereal[intro, simp]: "x \<in> A \<Longrightarrow> continuous (at x within A) ereal"
  using continuous_on_eq_continuous_within[of A ereal]
  by (auto intro: continuous_on_ereal continuous_on_id)

lemma ereal_open_uminus:
  fixes S :: "ereal set"
  assumes "open S"
  shows "open (uminus ` S)"
  using \<open>open S\<close>[unfolded open_generated_order]
proof induct
  have "range uminus = (UNIV :: ereal set)"
    by (auto simp: image_iff ereal_uminus_eq_reorder)
  then show "open (range uminus :: ereal set)"
    by simp
qed (auto simp add: image_Union image_Int)

lemma ereal_uminus_complement:
  fixes S :: "ereal set"
  shows "uminus ` (- S) = - uminus ` S"
  by (auto intro!: bij_image_Compl_eq surjI[of _ uminus] simp: bij_betw_def)

lemma ereal_closed_uminus:
  fixes S :: "ereal set"
  assumes "closed S"
  shows "closed (uminus ` S)"
  using assms
  unfolding closed_def ereal_uminus_complement[symmetric]
  by (rule ereal_open_uminus)

lemma ereal_open_affinity_pos:
  fixes S :: "ereal set"
  assumes "open S"
    and m: "m \<noteq> \<infinity>" "0 < m"
    and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof -
  have "continuous_on UNIV (\<lambda>x. inverse m * (x + - t))"
    using m t
    by (intro continuous_at_imp_continuous_on ballI continuous_at[THEN iffD2]; force)
  then have "open ((\<lambda>x. inverse m * (x + -t)) -` S)"
    using \<open>open S\<close> open_vimage by blast
  also have "(\<lambda>x. inverse m * (x + -t)) -` S = (\<lambda>x. (x - t) / m) -` S"
    using m t by (auto simp: divide_ereal_def mult.commute minus_ereal_def
                       simp flip: uminus_ereal.simps)
  also have "(\<lambda>x. (x - t) / m) -` S = (\<lambda>x. m * x + t) ` S"
    using m t
    by (simp add: set_eq_iff image_iff)
       (metis abs_ereal_less0 abs_ereal_uminus ereal_divide_eq ereal_eq_minus ereal_minus(7,8)
              ereal_minus_less_minus ereal_mult_eq_PInfty ereal_uminus_uminus ereal_zero_mult)
  finally show ?thesis .
qed

lemma ereal_open_affinity:
  fixes S :: "ereal set"
  assumes "open S"
    and m: "\<bar>m\<bar> \<noteq> \<infinity>" "m \<noteq> 0"
    and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof cases
  assume "0 < m"
  then show ?thesis
    using ereal_open_affinity_pos[OF \<open>open S\<close> _ _ t, of m] m
    by auto
next
  assume "\<not> 0 < m" then
  have "0 < -m"
    using \<open>m \<noteq> 0\<close>
    by (cases m) auto
  then have m: "-m \<noteq> \<infinity>" "0 < -m"
    using \<open>\<bar>m\<bar> \<noteq> \<infinity>\<close>
    by (auto simp: ereal_uminus_eq_reorder)
  from ereal_open_affinity_pos[OF ereal_open_uminus[OF \<open>open S\<close>] m t] show ?thesis
    unfolding image_image by simp
qed

lemma open_uminus_iff:
  fixes S :: "ereal set"
  shows "open (uminus ` S) \<longleftrightarrow> open S"
  using ereal_open_uminus[of S] ereal_open_uminus[of "uminus ` S"]
  by auto

lemma ereal_Liminf_uminus:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "Liminf net (\<lambda>x. - (f x)) = - Limsup net f"
  using ereal_Limsup_uminus[of _ "(\<lambda>x. - (f x))"] by auto

lemma Liminf_PInfty:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<not> trivial_limit net"
  shows "(f \<longlongrightarrow> \<infinity>) net \<longleftrightarrow> Liminf net f = \<infinity>"
  unfolding tendsto_iff_Liminf_eq_Limsup[OF assms]
  using Liminf_le_Limsup[OF assms, of f]
  by auto

lemma Limsup_MInfty:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<not> trivial_limit net"
  shows "(f \<longlongrightarrow> -\<infinity>) net \<longleftrightarrow> Limsup net f = -\<infinity>"
  unfolding tendsto_iff_Liminf_eq_Limsup[OF assms]
  using Liminf_le_Limsup[OF assms, of f]
  by auto

lemma convergent_ereal: \<comment> \<open>RENAME\<close>
  fixes X :: "nat \<Rightarrow> 'a :: {complete_linorder,linorder_topology}"
  shows "convergent X \<longleftrightarrow> limsup X = liminf X"
  using tendsto_iff_Liminf_eq_Limsup[of sequentially]
  by (auto simp: convergent_def)

lemma limsup_le_liminf_real:
  fixes X :: "nat \<Rightarrow> real" and L :: real
  assumes 1: "limsup X \<le> L" and 2: "L \<le> liminf X"
  shows "X \<longlonglongrightarrow> L"
proof -
  from 1 2 have "limsup X \<le> liminf X" by auto
  hence 3: "limsup X = liminf X"
    by (simp add: Liminf_le_Limsup order_class.order.antisym)
  hence 4: "convergent (\<lambda>n. ereal (X n))"
    by (subst convergent_ereal)
  hence "limsup X = lim (\<lambda>n. ereal(X n))"
    by (rule convergent_limsup_cl)
  also from 1 2 3 have "limsup X = L" by auto
  finally have "lim (\<lambda>n. ereal(X n)) = L" ..
  hence "(\<lambda>n. ereal (X n)) \<longlonglongrightarrow> L"
    using "4" convergent_LIMSEQ_iff by force
  thus ?thesis by simp
qed

lemma liminf_PInfty:
  fixes X :: "nat \<Rightarrow> ereal"
  shows "X \<longlonglongrightarrow> \<infinity> \<longleftrightarrow> liminf X = \<infinity>"
  by (metis Liminf_PInfty trivial_limit_sequentially)

lemma limsup_MInfty:
  fixes X :: "nat \<Rightarrow> ereal"
  shows "X \<longlonglongrightarrow> -\<infinity> \<longleftrightarrow> limsup X = -\<infinity>"
  by (metis Limsup_MInfty trivial_limit_sequentially)

lemma SUP_eq_LIMSEQ:
  assumes "mono f"
  shows "(SUP n. ereal (f n)) = ereal x \<longleftrightarrow> f \<longlonglongrightarrow> x"
proof
  have inc: "incseq (\<lambda>i. ereal (f i))"
    using \<open>mono f\<close> unfolding mono_def incseq_def by auto
  {
    assume "f \<longlonglongrightarrow> x"
    then have "(\<lambda>i. ereal (f i)) \<longlonglongrightarrow> ereal x"
      by auto
    from SUP_Lim[OF inc this] show "(SUP n. ereal (f n)) = ereal x" .
  next
    assume "(SUP n. ereal (f n)) = ereal x"
    with LIMSEQ_SUP[OF inc] show "f \<longlonglongrightarrow> x" by auto
  }
qed

lemma liminf_ereal_cminus:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes "c \<noteq> -\<infinity>"
  shows "liminf (\<lambda>x. c - f x) = c - limsup f"
proof (cases c)
  case PInf
  then show ?thesis
    by (simp add: Liminf_const)
next
  case (real r)
  then show ?thesis
    by (simp add: liminf_SUP_INF limsup_INF_SUP INF_ereal_minus_right SUP_ereal_minus_right)
qed (use \<open>c \<noteq> -\<infinity>\<close> in simp)


subsubsection \<open>Continuity\<close>

lemma continuous_at_of_ereal:
  "\<bar>x0 :: ereal\<bar> \<noteq> \<infinity> \<Longrightarrow> continuous (at x0) real_of_ereal"
  unfolding continuous_at
  by (rule lim_real_of_ereal) (simp add: ereal_real)

lemma nhds_ereal: "nhds (ereal r) = filtermap ereal (nhds r)"
  by (simp add: filtermap_nhds_open_map open_ereal continuous_at_of_ereal)

lemma at_ereal: "at (ereal r) = filtermap ereal (at r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_left_ereal: "at_left (ereal r) = filtermap ereal (at_left r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_right_ereal: "at_right (ereal r) = filtermap ereal (at_right r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma
  shows at_left_PInf: "at_left \<infinity> = filtermap ereal at_top"
    and at_right_MInf: "at_right (-\<infinity>) = filtermap ereal at_bot"
  unfolding filter_eq_iff eventually_filtermap eventually_at_top_dense eventually_at_bot_dense
    eventually_at_left[OF ereal_less(5)] eventually_at_right[OF ereal_less(6)]
  by (auto simp add: ereal_all_split ereal_ex_split)

lemma ereal_tendsto_simps1:
  "((f \<circ> real_of_ereal) \<longlongrightarrow> y) (at_left (ereal x)) \<longleftrightarrow> (f \<longlongrightarrow> y) (at_left x)"
  "((f \<circ> real_of_ereal) \<longlongrightarrow> y) (at_right (ereal x)) \<longleftrightarrow> (f \<longlongrightarrow> y) (at_right x)"
  "((f \<circ> real_of_ereal) \<longlongrightarrow> y) (at_left (\<infinity>::ereal)) \<longleftrightarrow> (f \<longlongrightarrow> y) at_top"
  "((f \<circ> real_of_ereal) \<longlongrightarrow> y) (at_right (-\<infinity>::ereal)) \<longleftrightarrow> (f \<longlongrightarrow> y) at_bot"
  unfolding tendsto_compose_filtermap at_left_ereal at_right_ereal at_left_PInf at_right_MInf
  by (auto simp: filtermap_filtermap filtermap_ident)

lemma ereal_tendsto_simps2:
  "((ereal \<circ> f) \<longlongrightarrow> ereal a) F \<longleftrightarrow> (f \<longlongrightarrow> a) F"
  "((ereal \<circ> f) \<longlongrightarrow> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  "((ereal \<circ> f) \<longlongrightarrow> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  unfolding tendsto_PInfty filterlim_at_top_dense tendsto_MInfty filterlim_at_bot_dense
  using lim_ereal by (simp_all add: comp_def)

lemma inverse_infty_ereal_tendsto_0: "inverse \<midarrow>\<infinity>\<rightarrow> (0::ereal)"
proof -
  have **: "((\<lambda>x. ereal (inverse x)) \<longlongrightarrow> ereal 0) at_infinity"
    by (intro tendsto_intros tendsto_inverse_0)
  then have "((\<lambda>x. if x = 0 then \<infinity> else ereal (inverse x)) \<longlongrightarrow> 0) at_top"
  proof (rule filterlim_mono_eventually)
    show "nhds (ereal 0) \<le> nhds 0"
      by (simp add: zero_ereal_def)
    show "(at_top::real filter) \<le> at_infinity"
      by (simp add: at_top_le_at_infinity)
  qed auto
  then show ?thesis
    unfolding at_infty_ereal_eq_at_top tendsto_compose_filtermap[symmetric] comp_def by auto
qed

lemma inverse_ereal_tendsto_pos:
  fixes x :: ereal assumes "0 < x"
  shows "inverse \<midarrow>x\<rightarrow> inverse x"
proof (cases x)
  case (real r)
  with \<open>0 < x\<close> have **: "(\<lambda>x. ereal (inverse x)) \<midarrow>r\<rightarrow> ereal (inverse r)"
    by (auto intro!: tendsto_inverse)
  from real \<open>0 < x\<close> show ?thesis
    by (auto simp: at_ereal tendsto_compose_filtermap[symmetric] eventually_at_filter
             intro!: Lim_transform_eventually[OF **] t1_space_nhds)
qed (insert \<open>0 < x\<close>, auto intro!: inverse_infty_ereal_tendsto_0)

lemma inverse_ereal_tendsto_at_right_0: "(inverse \<longlongrightarrow> \<infinity>) (at_right (0::ereal))"
  unfolding tendsto_compose_filtermap[symmetric] at_right_ereal zero_ereal_def
  by (subst filterlim_cong[OF refl refl, where g="\<lambda>x. ereal (inverse x)"])
     (auto simp: eventually_at_filter tendsto_PInfty_eq_at_top filterlim_inverse_at_top_right)

lemmas ereal_tendsto_simps = ereal_tendsto_simps1 ereal_tendsto_simps2

lemma continuous_at_iff_ereal:
  fixes f :: "'a::t2_space \<Rightarrow> real"
  shows "continuous (at x0 within s) f \<longleftrightarrow> continuous (at x0 within s) (ereal \<circ> f)"
  unfolding continuous_within comp_def lim_ereal ..

lemma continuous_on_iff_ereal:
  fixes f :: "'a::t2_space => real"
  assumes "open A"
  shows "continuous_on A f \<longleftrightarrow> continuous_on A (ereal \<circ> f)"
  unfolding continuous_on_def comp_def lim_ereal ..

lemma continuous_on_real: "continuous_on (UNIV - {\<infinity>, -\<infinity>::ereal}) real_of_ereal"
  using continuous_at_of_ereal continuous_on_eq_continuous_at open_image_ereal
  by auto

lemma continuous_on_iff_real:
  fixes f :: "'a::t2_space \<Rightarrow> ereal"
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "continuous_on A f \<longleftrightarrow> continuous_on A (real_of_ereal \<circ> f)"
proof 
  assume L: "continuous_on A f"
  have "f ` A \<subseteq> UNIV - {\<infinity>, -\<infinity>}"
    using assms by force
  then show "continuous_on A (real_of_ereal \<circ> f)"
    by (meson L continuous_on_compose continuous_on_real continuous_on_subset)
next
  assume R: "continuous_on A (real_of_ereal \<circ> f)"
  then have "continuous_on A (ereal \<circ> (real_of_ereal \<circ> f))"
    by (meson continuous_at_iff_ereal continuous_on_eq_continuous_within)
  then show "continuous_on A f"
    using assms ereal_real' by auto 
qed

lemma continuous_uminus_ereal [continuous_intros]: "continuous_on (A :: ereal set) uminus"
  unfolding continuous_on_def
  by (intro ballI tendsto_uminus_ereal[of "\<lambda>x. x::ereal"]) simp

lemma ereal_uminus_atMost [simp]: "uminus ` {..(a::ereal)} = {-a..}"
proof (intro equalityI subsetI)
  fix x :: ereal assume "x \<in> {-a..}"
  hence "-(-x) \<in> uminus ` {..a}" by (intro imageI) (simp add: ereal_uminus_le_reorder)
  thus "x \<in> uminus ` {..a}" by simp
qed auto

lemma continuous_on_inverse_ereal [continuous_intros]:
  "continuous_on {0::ereal ..} inverse"
  unfolding continuous_on_def
proof clarsimp
  fix x :: ereal assume "0 \<le> x"
  moreover have "at 0 within {0 ..} = at_right (0::ereal)"
    by (auto simp: filter_eq_iff eventually_at_filter le_less)
  moreover have "at x within {0 ..} = at x" if "0 < x"
    using that by (intro at_within_nhd[of _ "{0<..}"]) auto
  ultimately show "(inverse \<longlongrightarrow> inverse x) (at x within {0..})"
    by (auto simp: le_less inverse_ereal_tendsto_at_right_0 inverse_ereal_tendsto_pos)
qed

lemma continuous_inverse_ereal_nonpos: "continuous_on ({..<0} :: ereal set) inverse"
proof (subst continuous_on_cong[OF refl])
  have "continuous_on {(0::ereal)<..} inverse"
    by (rule continuous_on_subset[OF continuous_on_inverse_ereal]) auto
  thus "continuous_on {..<(0::ereal)} (uminus \<circ> inverse \<circ> uminus)"
    by (intro continuous_intros) simp_all
qed simp

lemma tendsto_inverse_ereal:
  assumes "(f \<longlongrightarrow> (c :: ereal)) F"
  assumes "eventually (\<lambda>x. f x \<ge> 0) F"
  shows   "((\<lambda>x. inverse (f x)) \<longlongrightarrow> inverse c) F"
  by (cases "F = bot")
     (auto intro!: tendsto_lowerbound assms
                   continuous_on_tendsto_compose[OF continuous_on_inverse_ereal])


subsubsection \<open>liminf and limsup\<close>

lemma Limsup_ereal_mult_right:
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Limsup F (\<lambda>n. f n * ereal c) = Limsup F f * ereal c"
proof (rule Limsup_compose_continuous_mono)
  from assms show "continuous_on UNIV (\<lambda>a. a * ereal c)"
    using tendsto_cmult_ereal[of "ereal c" "\<lambda>x. x" ]
    by (force simp: continuous_on_def mult_ac)
qed (insert assms, auto simp: mono_def ereal_mult_right_mono)

lemma Liminf_ereal_mult_right:
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Liminf F (\<lambda>n. f n * ereal c) = Liminf F f * ereal c"
proof (rule Liminf_compose_continuous_mono)
  from assms show "continuous_on UNIV (\<lambda>a. a * ereal c)"
    using tendsto_cmult_ereal[of "ereal c" "\<lambda>x. x" ]
    by (force simp: continuous_on_def mult_ac)
qed (use assms in \<open>auto simp: mono_def ereal_mult_right_mono\<close>)

lemma Liminf_ereal_mult_left:
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
    shows "Liminf F (\<lambda>n. ereal c * f n) = ereal c * Liminf F f"
using Liminf_ereal_mult_right[OF assms] by (subst (1 2) mult.commute)

lemma Limsup_ereal_mult_left:
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Limsup F (\<lambda>n. ereal c * f n) = ereal c * Limsup F f"
  using Limsup_ereal_mult_right[OF assms] by (subst (1 2) mult.commute)

lemma limsup_ereal_mult_right:
  "(c::real) \<ge> 0 \<Longrightarrow> limsup (\<lambda>n. f n * ereal c) = limsup f * ereal c"
  by (rule Limsup_ereal_mult_right) simp_all

lemma limsup_ereal_mult_left:
  "(c::real) \<ge> 0 \<Longrightarrow> limsup (\<lambda>n. ereal c * f n) = ereal c * limsup f"
  by (subst (1 2) mult.commute, rule limsup_ereal_mult_right) simp_all

lemma Limsup_add_ereal_right:
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Limsup F (\<lambda>n. g n + (c :: ereal)) = Limsup F g + c"
  by (rule Limsup_compose_continuous_mono) (auto simp: mono_def add_mono continuous_on_def)

lemma Limsup_add_ereal_left:
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Limsup F (\<lambda>n. (c :: ereal) + g n) = c + Limsup F g"
  by (subst (1 2) add.commute) (rule Limsup_add_ereal_right)

lemma Liminf_add_ereal_right:
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Liminf F (\<lambda>n. g n + (c :: ereal)) = Liminf F g + c"
  by (rule Liminf_compose_continuous_mono) (auto simp: mono_def add_mono continuous_on_def)

lemma Liminf_add_ereal_left:
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Liminf F (\<lambda>n. (c :: ereal) + g n) = c + Liminf F g"
  by (subst (1 2) add.commute) (rule Liminf_add_ereal_right)

lemma
  assumes "F \<noteq> bot"
  assumes nonneg: "eventually (\<lambda>x. f x \<ge> (0::ereal)) F"
  shows   Liminf_inverse_ereal: "Liminf F (\<lambda>x. inverse (f x)) = inverse (Limsup F f)"
  and     Limsup_inverse_ereal: "Limsup F (\<lambda>x. inverse (f x)) = inverse (Liminf F f)"
proof -
  define inv where [abs_def]: "inv x = (if x \<le> 0 then \<infinity> else inverse x)" for x :: ereal
  have "continuous_on ({..0} \<union> {0..}) inv" unfolding inv_def
    by (intro continuous_on_If) (auto intro!: continuous_intros)
  also have "{..0} \<union> {0..} = (UNIV :: ereal set)" by auto
  finally have cont: "continuous_on UNIV inv" .
  have antimono: "antimono inv" unfolding inv_def antimono_def
    by (auto intro!: ereal_inverse_antimono)

  have "Liminf F (\<lambda>x. inverse (f x)) = Liminf F (\<lambda>x. inv (f x))" using nonneg
    by (auto intro!: Liminf_eq elim!: eventually_mono simp: inv_def)
  also have "... = inv (Limsup F f)"
    by (simp add: assms(1) Liminf_compose_continuous_antimono[OF cont antimono])
  also from assms have "Limsup F f \<ge> 0" by (intro le_Limsup) simp_all
  hence "inv (Limsup F f) = inverse (Limsup F f)" by (simp add: inv_def)
  finally show "Liminf F (\<lambda>x. inverse (f x)) = inverse (Limsup F f)" .

  have "Limsup F (\<lambda>x. inverse (f x)) = Limsup F (\<lambda>x. inv (f x))" using nonneg
    by (auto intro!: Limsup_eq elim!: eventually_mono simp: inv_def)
  also have "... = inv (Liminf F f)"
    by (simp add: assms(1) Limsup_compose_continuous_antimono[OF cont antimono])
  also from assms have "Liminf F f \<ge> 0" by (intro Liminf_bounded) simp_all
  hence "inv (Liminf F f) = inverse (Liminf F f)" by (simp add: inv_def)
  finally show "Limsup F (\<lambda>x. inverse (f x)) = inverse (Liminf F f)" .
qed

lemma ereal_diff_le_mono_left: "\<lbrakk> x \<le> z; 0 \<le> y \<rbrakk> \<Longrightarrow> x - y \<le> (z :: ereal)"
by(cases x y z rule: ereal3_cases) simp_all

lemma neg_0_less_iff_less_erea [simp]: "0 < - a \<longleftrightarrow> (a :: ereal) < 0"
by(cases a) simp_all

lemma not_infty_ereal: "\<bar>x\<bar> \<noteq> \<infinity> \<longleftrightarrow> (\<exists>x'. x = ereal x')"
by(cases x) simp_all

lemma neq_PInf_trans: fixes x y :: ereal shows "\<lbrakk> y \<noteq> \<infinity>; x \<le> y \<rbrakk> \<Longrightarrow> x \<noteq> \<infinity>"
by auto

lemma mult_2_ereal: "ereal 2 * x = x + x"
by(cases x) simp_all

lemma ereal_diff_le_self: "0 \<le> y \<Longrightarrow> x - y \<le> (x :: ereal)"
by(cases x y rule: ereal2_cases) simp_all

lemma ereal_le_add_self: "0 \<le> y \<Longrightarrow> x \<le> x + (y :: ereal)"
by(cases x y rule: ereal2_cases) simp_all

lemma ereal_le_add_self2: "0 \<le> y \<Longrightarrow> x \<le> y + (x :: ereal)"
by(cases x y rule: ereal2_cases) simp_all

lemma ereal_le_add_mono1: "\<lbrakk> x \<le> y; 0 \<le> (z :: ereal) \<rbrakk> \<Longrightarrow> x \<le> y + z"
using add_mono by fastforce

lemma ereal_le_add_mono2: "\<lbrakk> x \<le> z; 0 \<le> (y :: ereal) \<rbrakk> \<Longrightarrow> x \<le> y + z"
using add_mono by fastforce

lemma ereal_diff_nonpos:
  fixes a b :: ereal shows "\<lbrakk> a \<le> b; a = \<infinity> \<Longrightarrow> b \<noteq> \<infinity>; a = -\<infinity> \<Longrightarrow> b \<noteq> -\<infinity> \<rbrakk> \<Longrightarrow> a - b \<le> 0"
  by (cases rule: ereal2_cases[of a b]) auto

lemma minus_ereal_0 [simp]: "x - ereal 0 = x"
by(simp flip: zero_ereal_def)

lemma ereal_diff_eq_0_iff: fixes a b :: ereal
  shows "(\<bar>a\<bar> = \<infinity> \<Longrightarrow> \<bar>b\<bar> \<noteq> \<infinity>) \<Longrightarrow> a - b = 0 \<longleftrightarrow> a = b"
by(cases a b rule: ereal2_cases) simp_all

lemma SUP_ereal_eq_0_iff_nonneg:
  fixes f :: "_ \<Rightarrow> ereal" and A
  assumes nonneg: "\<forall>x\<in>A. f x \<ge> 0"
  and A:"A \<noteq> {}"
  shows "(SUP x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI ballI)
  fix x
  assume "?lhs" "x \<in> A"
  from \<open>x \<in> A\<close> have "f x \<le> (SUP x\<in>A. f x)" by(rule SUP_upper)
  with \<open>?lhs\<close> show "f x = 0" using nonneg \<open>x \<in> A\<close> by auto
qed (simp add: A)

lemma ereal_divide_le_posI:
  fixes x y z :: ereal
  shows "x > 0 \<Longrightarrow> z \<noteq> - \<infinity> \<Longrightarrow> z \<le> x * y \<Longrightarrow> z / x \<le> y"
by (cases rule: ereal3_cases[of x y z])(auto simp: field_simps split: if_split_asm)

lemma add_diff_eq_ereal: fixes x y z :: ereal
  shows "x + (y - z) = x + y - z"
by(cases x y z rule: ereal3_cases) simp_all

lemma ereal_diff_gr0:
  fixes a b :: ereal shows "a < b \<Longrightarrow> 0 < b - a"
  by (cases rule: ereal2_cases[of a b]) auto

lemma ereal_minus_minus: fixes x y z :: ereal shows
  "(\<bar>y\<bar> = \<infinity> \<Longrightarrow> \<bar>z\<bar> \<noteq> \<infinity>) \<Longrightarrow> x - (y - z) = x + z - y"
by(cases x y z rule: ereal3_cases) simp_all

lemma diff_add_eq_ereal: fixes a b c :: ereal shows "a - b + c = a + c - b"
by(cases a b c rule: ereal3_cases) simp_all

lemma diff_diff_commute_ereal: fixes x y z :: ereal shows "x - y - z = x - z - y"
by(cases x y z rule: ereal3_cases) simp_all

lemma ereal_diff_eq_MInfty_iff: fixes x y :: ereal shows "x - y = -\<infinity> \<longleftrightarrow> x = -\<infinity> \<and> y \<noteq> -\<infinity> \<or> y = \<infinity> \<and> \<bar>x\<bar> \<noteq> \<infinity>"
by(cases x y rule: ereal2_cases) simp_all

lemma ereal_diff_add_inverse: fixes x y :: ereal shows "\<bar>x\<bar> \<noteq> \<infinity> \<Longrightarrow> x + y - x = y"
by(cases x y rule: ereal2_cases) simp_all

lemma tendsto_diff_ereal:
  fixes x y :: ereal
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>" and y: "\<bar>y\<bar> \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x - g x) \<longlongrightarrow> x - y) F"
proof -
  from x obtain r where x': "x = ereal r" by (cases x) auto
  with f have "((\<lambda>i. real_of_ereal (f i)) \<longlongrightarrow> r) F" by simp
  moreover
  from y obtain p where y': "y = ereal p" by (cases y) auto
  with g have "((\<lambda>i. real_of_ereal (g i)) \<longlongrightarrow> p) F" by simp
  ultimately have "((\<lambda>i. real_of_ereal (f i) - real_of_ereal (g i)) \<longlongrightarrow> r - p) F"
    by (rule tendsto_diff)
  moreover
  from eventually_finite[OF x f] eventually_finite[OF y g]
  have "eventually (\<lambda>x. f x - g x = ereal (real_of_ereal (f x) - real_of_ereal (g x))) F"
    by eventually_elim auto
  ultimately show ?thesis
    by (simp add: x' y' cong: filterlim_cong)
qed

lemma continuous_on_diff_ereal:
  "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> \<bar>g x\<bar> \<noteq> \<infinity>) \<Longrightarrow> continuous_on A (\<lambda>z. f z - g z::ereal)"
  by (auto simp: tendsto_diff_ereal continuous_on_def)


subsubsection \<open>Tests for code generator\<close>

text \<open>A small list of simple arithmetic expressions.\<close>

value "- \<infinity> :: ereal"
value "\<bar>-\<infinity>\<bar> :: ereal"
value "4 + 5 / 4 - ereal 2 :: ereal"
value "ereal 3 < \<infinity>"
value "real_of_ereal (\<infinity>::ereal) = 0"

end

(*  Title:      HOL/Topological_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

section \<open>Topological Spaces\<close>

theory Topological_Spaces
  imports Main
begin

named_theorems continuous_intros "structural introduction rules for continuity"

subsection \<open>Topological space\<close>

class "open" =
  fixes "open" :: "'a set \<Rightarrow> bool"

class topological_space = "open" +
  assumes open_UNIV [simp, intro]: "open UNIV"
  assumes open_Int [intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)"
  assumes open_Union [intro]: "\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union>K)"
begin

definition closed :: "'a set \<Rightarrow> bool"
  where "closed S \<longleftrightarrow> open (- S)"

lemma open_empty [continuous_intros, intro, simp]: "open {}"
  using open_Union [of "{}"] by simp

lemma open_Un [continuous_intros, intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<union> T)"
  using open_Union [of "{S, T}"] by simp

lemma open_UN [continuous_intros, intro]: "\<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Union>x\<in>A. B x)"
  using open_Union [of "B ` A"] by simp

lemma open_Inter [continuous_intros, intro]: "finite S \<Longrightarrow> \<forall>T\<in>S. open T \<Longrightarrow> open (\<Inter>S)"
  by (induction set: finite) auto

lemma open_INT [continuous_intros, intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Inter>x\<in>A. B x)"
  using open_Inter [of "B ` A"] by simp

lemma openI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S"
  shows "open S"
proof -
  have "open (\<Union>{T. open T \<and> T \<subseteq> S})" by auto
  moreover have "\<Union>{T. open T \<and> T \<subseteq> S} = S" by (auto dest!: assms)
  ultimately show "open S" by simp
qed

lemma open_subopen: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S)"
by (auto intro: openI)

lemma closed_empty [continuous_intros, intro, simp]: "closed {}"
  unfolding closed_def by simp

lemma closed_Un [continuous_intros, intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<union> T)"
  unfolding closed_def by auto

lemma closed_UNIV [continuous_intros, intro, simp]: "closed UNIV"
  unfolding closed_def by simp

lemma closed_Int [continuous_intros, intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<inter> T)"
  unfolding closed_def by auto

lemma closed_INT [continuous_intros, intro]: "\<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Inter>x\<in>A. B x)"
  unfolding closed_def by auto

lemma closed_Inter [continuous_intros, intro]: "\<forall>S\<in>K. closed S \<Longrightarrow> closed (\<Inter>K)"
  unfolding closed_def uminus_Inf by auto

lemma closed_Union [continuous_intros, intro]: "finite S \<Longrightarrow> \<forall>T\<in>S. closed T \<Longrightarrow> closed (\<Union>S)"
  by (induct set: finite) auto

lemma closed_UN [continuous_intros, intro]:
  "finite A \<Longrightarrow> \<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Union>x\<in>A. B x)"
  using closed_Union [of "B ` A"] by simp

lemma open_closed: "open S \<longleftrightarrow> closed (- S)"
  by (simp add: closed_def)

lemma closed_open: "closed S \<longleftrightarrow> open (- S)"
  by (rule closed_def)

lemma open_Diff [continuous_intros, intro]: "open S \<Longrightarrow> closed T \<Longrightarrow> open (S - T)"
  by (simp add: closed_open Diff_eq open_Int)

lemma closed_Diff [continuous_intros, intro]: "closed S \<Longrightarrow> open T \<Longrightarrow> closed (S - T)"
  by (simp add: open_closed Diff_eq closed_Int)

lemma open_Compl [continuous_intros, intro]: "closed S \<Longrightarrow> open (- S)"
  by (simp add: closed_open)

lemma closed_Compl [continuous_intros, intro]: "open S \<Longrightarrow> closed (- S)"
  by (simp add: open_closed)

lemma open_Collect_neg: "closed {x. P x} \<Longrightarrow> open {x. \<not> P x}"
  unfolding Collect_neg_eq by (rule open_Compl)

lemma open_Collect_conj:
  assumes "open {x. P x}" "open {x. Q x}"
  shows "open {x. P x \<and> Q x}"
  using open_Int[OF assms] by (simp add: Int_def)

lemma open_Collect_disj:
  assumes "open {x. P x}" "open {x. Q x}"
  shows "open {x. P x \<or> Q x}"
  using open_Un[OF assms] by (simp add: Un_def)

lemma open_Collect_ex: "(\<And>i. open {x. P i x}) \<Longrightarrow> open {x. \<exists>i. P i x}"
  using open_UN[of UNIV "\<lambda>i. {x. P i x}"] unfolding Collect_ex_eq by simp

lemma open_Collect_imp: "closed {x. P x} \<Longrightarrow> open {x. Q x} \<Longrightarrow> open {x. P x \<longrightarrow> Q x}"
  unfolding imp_conv_disj by (intro open_Collect_disj open_Collect_neg)

lemma open_Collect_const: "open {x. P}"
  by (cases P) auto

lemma closed_Collect_neg: "open {x. P x} \<Longrightarrow> closed {x. \<not> P x}"
  unfolding Collect_neg_eq by (rule closed_Compl)

lemma closed_Collect_conj:
  assumes "closed {x. P x}" "closed {x. Q x}"
  shows "closed {x. P x \<and> Q x}"
  using closed_Int[OF assms] by (simp add: Int_def)

lemma closed_Collect_disj:
  assumes "closed {x. P x}" "closed {x. Q x}"
  shows "closed {x. P x \<or> Q x}"
  using closed_Un[OF assms] by (simp add: Un_def)

lemma closed_Collect_all: "(\<And>i. closed {x. P i x}) \<Longrightarrow> closed {x. \<forall>i. P i x}"
  using closed_INT[of UNIV "\<lambda>i. {x. P i x}"] by (simp add: Collect_all_eq)

lemma closed_Collect_imp: "open {x. P x} \<Longrightarrow> closed {x. Q x} \<Longrightarrow> closed {x. P x \<longrightarrow> Q x}"
  unfolding imp_conv_disj by (intro closed_Collect_disj closed_Collect_neg)

lemma closed_Collect_const: "closed {x. P}"
  by (cases P) auto

end


subsection \<open>Hausdorff and other separation properties\<close>

class t0_space = topological_space +
  assumes t0_space: "x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> \<not> (x \<in> U \<longleftrightarrow> y \<in> U)"

class t1_space = topological_space +
  assumes t1_space: "x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> x \<in> U \<and> y \<notin> U"

instance t1_space \<subseteq> t0_space
  by standard (fast dest: t1_space)

context t1_space begin

lemma separation_t1: "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U)"
  using t1_space[of x y] by blast

lemma closed_singleton [iff]: "closed {a}"
proof -
  let ?T = "\<Union>{S. open S \<and> a \<notin> S}"
  have "open ?T"
    by (simp add: open_Union)
  also have "?T = - {a}"
    by (auto simp add: set_eq_iff separation_t1)
  finally show "closed {a}"
    by (simp only: closed_def)
qed

lemma closed_insert [continuous_intros, simp]:
  assumes "closed S"
  shows "closed (insert a S)"
proof -
  from closed_singleton assms have "closed ({a} \<union> S)"
    by (rule closed_Un)
  then show "closed (insert a S)"
    by simp
qed

lemma finite_imp_closed: "finite S \<Longrightarrow> closed S"
  by (induct pred: finite) simp_all

end

text \<open>T2 spaces are also known as Hausdorff spaces.\<close>

class t2_space = topological_space +
  assumes hausdorff: "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"

instance t2_space \<subseteq> t1_space
  by standard (fast dest: hausdorff)

lemma (in t2_space) separation_t2: "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})"
  using hausdorff [of x y] by blast

lemma (in t0_space) separation_t0: "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> \<not> (x \<in> U \<longleftrightarrow> y \<in> U))"
  using t0_space [of x y] by blast


text \<open>A classical separation axiom for topological space, the T3 axiom -- also called regularity:
if a point is not in a closed set, then there are open sets separating them.\<close>

class t3_space = t2_space +
  assumes t3_space: "closed S \<Longrightarrow> y \<notin> S \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> y \<in> U \<and> S \<subseteq> V \<and> U \<inter> V = {}"

text \<open>A classical separation axiom for topological space, the T4 axiom -- also called normality:
if two closed sets are disjoint, then there are open sets separating them.\<close>

class t4_space = t2_space +
  assumes t4_space: "closed S \<Longrightarrow> closed T \<Longrightarrow> S \<inter> T = {} \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> U \<inter> V = {}"

text \<open>T4 is stronger than T3, and weaker than metric.\<close>

instance t4_space \<subseteq> t3_space
proof
  fix S and y::'a assume "closed S" "y \<notin> S"
  then show "\<exists>U V. open U \<and> open V \<and> y \<in> U \<and> S \<subseteq> V \<and> U \<inter> V = {}"
    using t4_space[of "{y}" S] by auto
qed

text \<open>A perfect space is a topological space with no isolated points.\<close>

class perfect_space = topological_space +
  assumes not_open_singleton: "\<not> open {x}"

lemma (in perfect_space) UNIV_not_singleton: "UNIV \<noteq> {x}"
  for x::'a
  by (metis (no_types) open_UNIV not_open_singleton)


subsection \<open>Generators for toplogies\<close>

inductive generate_topology :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" for S :: "'a set set"
  where
    UNIV: "generate_topology S UNIV"
  | Int: "generate_topology S (a \<inter> b)" if "generate_topology S a" and "generate_topology S b"
  | UN: "generate_topology S (\<Union>K)" if "(\<And>k. k \<in> K \<Longrightarrow> generate_topology S k)"
  | Basis: "generate_topology S s" if "s \<in> S"

hide_fact (open) UNIV Int UN Basis

lemma generate_topology_Union:
  "(\<And>k. k \<in> I \<Longrightarrow> generate_topology S (K k)) \<Longrightarrow> generate_topology S (\<Union>k\<in>I. K k)"
  using generate_topology.UN [of "K ` I"] by auto

lemma topological_space_generate_topology: "class.topological_space (generate_topology S)"
  by standard (auto intro: generate_topology.intros)


subsection \<open>Order topologies\<close>

class order_topology = order + "open" +
  assumes open_generated_order: "open = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"
begin

subclass topological_space
  unfolding open_generated_order
  by (rule topological_space_generate_topology)

lemma open_greaterThan [continuous_intros, simp]: "open {a <..}"
  unfolding open_generated_order by (auto intro: generate_topology.Basis)

lemma open_lessThan [continuous_intros, simp]: "open {..< a}"
  unfolding open_generated_order by (auto intro: generate_topology.Basis)

lemma open_greaterThanLessThan [continuous_intros, simp]: "open {a <..< b}"
   unfolding greaterThanLessThan_eq by (simp add: open_Int)

end

class linorder_topology = linorder + order_topology

lemma closed_atMost [continuous_intros, simp]: "closed {..a}"
  for a :: "'a::linorder_topology"
  by (simp add: closed_open)

lemma closed_atLeast [continuous_intros, simp]: "closed {a..}"
  for a :: "'a::linorder_topology"
  by (simp add: closed_open)

lemma closed_atLeastAtMost [continuous_intros, simp]: "closed {a..b}"
  for a b :: "'a::linorder_topology"
proof -
  have "{a .. b} = {a ..} \<inter> {.. b}"
    by auto
  then show ?thesis
    by (simp add: closed_Int)
qed

lemma (in order) less_separate:
  assumes "x < y"
  shows "\<exists>a b. x \<in> {..< a} \<and> y \<in> {b <..} \<and> {..< a} \<inter> {b <..} = {}"
proof (cases "\<exists>z. x < z \<and> z < y")
  case True
  then obtain z where "x < z \<and> z < y" ..
  then have "x \<in> {..< z} \<and> y \<in> {z <..} \<and> {z <..} \<inter> {..< z} = {}"
    by auto
  then show ?thesis by blast
next
  case False
  with \<open>x < y\<close> have "x \<in> {..< y}" "y \<in> {x <..}" "{x <..} \<inter> {..< y} = {}"
    by auto
  then show ?thesis by blast
qed

instance linorder_topology \<subseteq> t2_space
proof
  fix x y :: 'a
  show "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    using less_separate [of x y] less_separate [of y x]
    by (elim neqE; metis open_lessThan open_greaterThan Int_commute)
qed

lemma (in linorder_topology) open_right:
  assumes "open S" "x \<in> S"
    and gt_ex: "x < y"
  shows "\<exists>b>x. {x ..< b} \<subseteq> S"
  using assms unfolding open_generated_order
proof induct
  case UNIV
  then show ?case by blast
next
  case (Int A B)
  then obtain a b where "a > x" "{x ..< a} \<subseteq> A"  "b > x" "{x ..< b} \<subseteq> B"
    by auto
  then show ?case
    by (auto intro!: exI[of _ "min a b"])
next
  case UN
  then show ?case by blast
next
  case Basis
  then show ?case
    by (fastforce intro: exI[of _ y] gt_ex)
qed

lemma (in linorder_topology) open_left:
  assumes "open S" "x \<in> S"
    and lt_ex: "y < x"
  shows "\<exists>b<x. {b <.. x} \<subseteq> S"
  using assms unfolding open_generated_order
proof induction
  case UNIV
  then show ?case by blast
next
  case (Int A B)
  then obtain a b where "a < x" "{a <.. x} \<subseteq> A"  "b < x" "{b <.. x} \<subseteq> B"
    by auto
  then show ?case
    by (auto intro!: exI[of _ "max a b"])
next
  case UN
  then show ?case by blast
next
  case Basis
  then show ?case
    by (fastforce intro: exI[of _ y] lt_ex)
qed


subsection \<open>Setup some topologies\<close>

subsubsection \<open>Boolean is an order topology\<close>

class discrete_topology = topological_space +
  assumes open_discrete: "\<And>A. open A"

instance discrete_topology < t2_space
proof
  fix x y :: 'a
  assume "x \<noteq> y"
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (intro exI[of _ "{_}"]) (auto intro!: open_discrete)
qed

instantiation bool :: linorder_topology
begin

definition open_bool :: "bool set \<Rightarrow> bool"
  where "open_bool = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"

instance
  by standard (rule open_bool_def)

end

instance bool :: discrete_topology
proof
  fix A :: "bool set"
  have *: "{False <..} = {True}" "{..< True} = {False}"
    by auto
  have "A = UNIV \<or> A = {} \<or> A = {False <..} \<or> A = {..< True}"
    using subset_UNIV[of A] unfolding UNIV_bool * by blast
  then show "open A"
    by auto
qed

instantiation nat :: linorder_topology
begin

definition open_nat :: "nat set \<Rightarrow> bool"
  where "open_nat = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"

instance
  by standard (rule open_nat_def)

end

instance nat :: discrete_topology
proof
  fix A :: "nat set"
  have "open {n}" for n :: nat
  proof (cases n)
    case 0
    moreover have "{0} = {..<1::nat}"
      by auto
    ultimately show ?thesis
       by auto
  next
    case (Suc n')
    then have "{n} = {..<Suc n} \<inter> {n' <..}"
      by auto
    with Suc show ?thesis
      by (auto intro: open_lessThan open_greaterThan)
  qed
  then have "open (\<Union>a\<in>A. {a})"
    by (intro open_UN) auto
  then show "open A"
    by simp
qed

instantiation int :: linorder_topology
begin

definition open_int :: "int set \<Rightarrow> bool"
  where "open_int = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"

instance
  by standard (rule open_int_def)

end

instance int :: discrete_topology
proof
  fix A :: "int set"
  have "{..<i + 1} \<inter> {i-1 <..} = {i}" for i :: int
    by auto
  then have "open {i}" for i :: int
    using open_Int[OF open_lessThan[of "i + 1"] open_greaterThan[of "i - 1"]] by auto
  then have "open (\<Union>a\<in>A. {a})"
    by (intro open_UN) auto
  then show "open A"
    by simp
qed


subsubsection \<open>Topological filters\<close>

definition (in topological_space) nhds :: "'a \<Rightarrow> 'a filter"
  where "nhds a = (INF S\<in>{S. open S \<and> a \<in> S}. principal S)"

definition (in topological_space) at_within :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a filter"
    ("at (_)/ within (_)" [1000, 60] 60)
  where "at a within s = inf (nhds a) (principal (s - {a}))"

abbreviation (in topological_space) at :: "'a \<Rightarrow> 'a filter"  ("at")
  where "at x \<equiv> at x within (CONST UNIV)"

abbreviation (in order_topology) at_right :: "'a \<Rightarrow> 'a filter"
  where "at_right x \<equiv> at x within {x <..}"

abbreviation (in order_topology) at_left :: "'a \<Rightarrow> 'a filter"
  where "at_left x \<equiv> at x within {..< x}"

lemma (in topological_space) nhds_generated_topology:
  "open = generate_topology T \<Longrightarrow> nhds x = (INF S\<in>{S\<in>T. x \<in> S}. principal S)"
  unfolding nhds_def
proof (safe intro!: antisym INF_greatest)
  fix S
  assume "generate_topology T S" "x \<in> S"
  then show "(INF S\<in>{S \<in> T. x \<in> S}. principal S) \<le> principal S"
    by induct
      (auto intro: INF_lower order_trans simp: inf_principal[symmetric] simp del: inf_principal)
qed (auto intro!: INF_lower intro: generate_topology.intros)

lemma (in topological_space) eventually_nhds:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"
  unfolding nhds_def by (subst eventually_INF_base) (auto simp: eventually_principal)

lemma eventually_eventually:
  "eventually (\<lambda>y. eventually P (nhds y)) (nhds x) = eventually P (nhds x)"
  by (auto simp: eventually_nhds)

lemma (in topological_space) eventually_nhds_in_open:
  "open s \<Longrightarrow> x \<in> s \<Longrightarrow> eventually (\<lambda>y. y \<in> s) (nhds x)"
  by (subst eventually_nhds) blast

lemma (in topological_space) eventually_nhds_x_imp_x: "eventually P (nhds x) \<Longrightarrow> P x"
  by (subst (asm) eventually_nhds) blast

lemma (in topological_space) nhds_neq_bot [simp]: "nhds a \<noteq> bot"
  by (simp add: trivial_limit_def eventually_nhds)

lemma (in t1_space) t1_space_nhds: "x \<noteq> y \<Longrightarrow> (\<forall>\<^sub>F x in nhds x. x \<noteq> y)"
  by (drule t1_space) (auto simp: eventually_nhds)

lemma (in topological_space) nhds_discrete_open: "open {x} \<Longrightarrow> nhds x = principal {x}"
  by (auto simp: nhds_def intro!: antisym INF_greatest INF_lower2[of "{x}"])

lemma (in discrete_topology) nhds_discrete: "nhds x = principal {x}"
  by (simp add: nhds_discrete_open open_discrete)

lemma (in discrete_topology) at_discrete: "at x within S = bot"
  unfolding at_within_def nhds_discrete by simp

lemma (in discrete_topology) tendsto_discrete:
  "filterlim (f :: 'b \<Rightarrow> 'a) (nhds y) F \<longleftrightarrow> eventually (\<lambda>x. f x = y) F"
  by (auto simp: nhds_discrete filterlim_principal)

lemma (in topological_space) at_within_eq:
  "at x within s = (INF S\<in>{S. open S \<and> x \<in> S}. principal (S \<inter> s - {x}))"
  unfolding nhds_def at_within_def
  by (subst INF_inf_const2[symmetric]) (auto simp: Diff_Int_distrib)

lemma (in topological_space) eventually_at_filter:
  "eventually P (at a within s) \<longleftrightarrow> eventually (\<lambda>x. x \<noteq> a \<longrightarrow> x \<in> s \<longrightarrow> P x) (nhds a)"
  by (simp add: at_within_def eventually_inf_principal imp_conjL[symmetric] conj_commute)

lemma (in topological_space) at_le: "s \<subseteq> t \<Longrightarrow> at x within s \<le> at x within t"
  unfolding at_within_def by (intro inf_mono) auto

lemma (in topological_space) eventually_at_topological:
  "eventually P (at a within s) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> x \<in> s \<longrightarrow> P x))"
  by (simp add: eventually_nhds eventually_at_filter)

lemma (in topological_space) at_within_open: "a \<in> S \<Longrightarrow> open S \<Longrightarrow> at a within S = at a"
  unfolding filter_eq_iff eventually_at_topological by (metis open_Int Int_iff UNIV_I)

lemma (in topological_space) at_within_open_NO_MATCH:
  "a \<in> s \<Longrightarrow> open s \<Longrightarrow> NO_MATCH UNIV s \<Longrightarrow> at a within s = at a"
  by (simp only: at_within_open)

lemma (in topological_space) at_within_open_subset:
  "a \<in> S \<Longrightarrow> open S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> at a within T = at a"
  by (metis at_le at_within_open dual_order.antisym subset_UNIV)

lemma (in topological_space) at_within_nhd:
  assumes "x \<in> S" "open S" "T \<inter> S - {x} = U \<inter> S - {x}"
  shows "at x within T = at x within U"
  unfolding filter_eq_iff eventually_at_filter
proof (intro allI eventually_subst)
  have "eventually (\<lambda>x. x \<in> S) (nhds x)"
    using \<open>x \<in> S\<close> \<open>open S\<close> by (auto simp: eventually_nhds)
  then show "\<forall>\<^sub>F n in nhds x. (n \<noteq> x \<longrightarrow> n \<in> T \<longrightarrow> P n) = (n \<noteq> x \<longrightarrow> n \<in> U \<longrightarrow> P n)" for P
    by eventually_elim (insert \<open>T \<inter> S - {x} = U \<inter> S - {x}\<close>, blast)
qed

lemma (in topological_space) at_within_empty [simp]: "at a within {} = bot"
  unfolding at_within_def by simp

lemma (in topological_space) at_within_union:
  "at x within (S \<union> T) = sup (at x within S) (at x within T)"
  unfolding filter_eq_iff eventually_sup eventually_at_filter
  by (auto elim!: eventually_rev_mp)

lemma (in topological_space) at_eq_bot_iff: "at a = bot \<longleftrightarrow> open {a}"
  unfolding trivial_limit_def eventually_at_topological
  apply safe
   apply (case_tac "S = {a}")
    apply simp
   apply fast
  apply fast
  done

lemma (in perfect_space) at_neq_bot [simp]: "at a \<noteq> bot"
  by (simp add: at_eq_bot_iff not_open_singleton)

lemma (in order_topology) nhds_order:
  "nhds x = inf (INF a\<in>{x <..}. principal {..< a}) (INF a\<in>{..< x}. principal {a <..})"
proof -
  have 1: "{S \<in> range lessThan \<union> range greaterThan. x \<in> S} =
      (\<lambda>a. {..< a}) ` {x <..} \<union> (\<lambda>a. {a <..}) ` {..< x}"
    by auto
  show ?thesis
    by (simp only: nhds_generated_topology[OF open_generated_order] INF_union 1 INF_image comp_def)
qed

lemma (in topological_space) filterlim_at_within_If:
  assumes "filterlim f G (at x within (A \<inter> {x. P x}))"
    and "filterlim g G (at x within (A \<inter> {x. \<not>P x}))"
  shows "filterlim (\<lambda>x. if P x then f x else g x) G (at x within A)"
proof (rule filterlim_If)
  note assms(1)
  also have "at x within (A \<inter> {x. P x}) = inf (nhds x) (principal (A \<inter> Collect P - {x}))"
    by (simp add: at_within_def)
  also have "A \<inter> Collect P - {x} = (A - {x}) \<inter> Collect P"
    by blast
  also have "inf (nhds x) (principal \<dots>) = inf (at x within A) (principal (Collect P))"
    by (simp add: at_within_def inf_assoc)
  finally show "filterlim f G (inf (at x within A) (principal (Collect P)))" .
next
  note assms(2)
  also have "at x within (A \<inter> {x. \<not> P x}) = inf (nhds x) (principal (A \<inter> {x. \<not> P x} - {x}))"
    by (simp add: at_within_def)
  also have "A \<inter> {x. \<not> P x} - {x} = (A - {x}) \<inter> {x. \<not> P x}"
    by blast
  also have "inf (nhds x) (principal \<dots>) = inf (at x within A) (principal {x. \<not> P x})"
    by (simp add: at_within_def inf_assoc)
  finally show "filterlim g G (inf (at x within A) (principal {x. \<not> P x}))" .
qed

lemma (in topological_space) filterlim_at_If:
  assumes "filterlim f G (at x within {x. P x})"
    and "filterlim g G (at x within {x. \<not>P x})"
  shows "filterlim (\<lambda>x. if P x then f x else g x) G (at x)"
  using assms by (intro filterlim_at_within_If) simp_all
lemma (in linorder_topology) at_within_order:
  assumes "UNIV \<noteq> {x}"
  shows "at x within s =
    inf (INF a\<in>{x <..}. principal ({..< a} \<inter> s - {x}))
        (INF a\<in>{..< x}. principal ({a <..} \<inter> s - {x}))"
proof (cases "{x <..} = {}" "{..< x} = {}" rule: case_split [case_product case_split])
  case True_True
  have "UNIV = {..< x} \<union> {x} \<union> {x <..}"
    by auto
  with assms True_True show ?thesis
    by auto
qed (auto simp del: inf_principal simp: at_within_def nhds_order Int_Diff
      inf_principal[symmetric] INF_inf_const2 inf_sup_aci[where 'a="'a filter"])

lemma (in linorder_topology) at_left_eq:
  "y < x \<Longrightarrow> at_left x = (INF a\<in>{..< x}. principal {a <..< x})"
  by (subst at_within_order)
     (auto simp: greaterThan_Int_greaterThan greaterThanLessThan_eq[symmetric] min.absorb2 INF_constant
           intro!: INF_lower2 inf_absorb2)

lemma (in linorder_topology) eventually_at_left:
  "y < x \<Longrightarrow> eventually P (at_left x) \<longleftrightarrow> (\<exists>b<x. \<forall>y>b. y < x \<longrightarrow> P y)"
  unfolding at_left_eq
  by (subst eventually_INF_base) (auto simp: eventually_principal Ball_def)

lemma (in linorder_topology) at_right_eq:
  "x < y \<Longrightarrow> at_right x = (INF a\<in>{x <..}. principal {x <..< a})"
  by (subst at_within_order)
     (auto simp: lessThan_Int_lessThan greaterThanLessThan_eq[symmetric] max.absorb2 INF_constant Int_commute
           intro!: INF_lower2 inf_absorb1)

lemma (in linorder_topology) eventually_at_right:
  "x < y \<Longrightarrow> eventually P (at_right x) \<longleftrightarrow> (\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> P y)"
  unfolding at_right_eq
  by (subst eventually_INF_base) (auto simp: eventually_principal Ball_def)

lemma eventually_at_right_less: "\<forall>\<^sub>F y in at_right (x::'a::{linorder_topology, no_top}). x < y"
  using gt_ex[of x] eventually_at_right[of x] by auto

lemma trivial_limit_at_right_top: "at_right (top::_::{order_top,linorder_topology}) = bot"
  by (auto simp: filter_eq_iff eventually_at_topological)

lemma trivial_limit_at_left_bot: "at_left (bot::_::{order_bot,linorder_topology}) = bot"
  by (auto simp: filter_eq_iff eventually_at_topological)

lemma trivial_limit_at_left_real [simp]: "\<not> trivial_limit (at_left x)"
  for x :: "'a::{no_bot,dense_order,linorder_topology}"
  using lt_ex [of x]
  by safe (auto simp add: trivial_limit_def eventually_at_left dest: dense)

lemma trivial_limit_at_right_real [simp]: "\<not> trivial_limit (at_right x)"
  for x :: "'a::{no_top,dense_order,linorder_topology}"
  using gt_ex[of x]
  by safe (auto simp add: trivial_limit_def eventually_at_right dest: dense)

lemma (in linorder_topology) at_eq_sup_left_right: "at x = sup (at_left x) (at_right x)"
  by (auto simp: eventually_at_filter filter_eq_iff eventually_sup
      elim: eventually_elim2 eventually_mono)

lemma (in linorder_topology) eventually_at_split:
  "eventually P (at x) \<longleftrightarrow> eventually P (at_left x) \<and> eventually P (at_right x)"
  by (subst at_eq_sup_left_right) (simp add: eventually_sup)

lemma (in order_topology) eventually_at_leftI:
  assumes "\<And>x. x \<in> {a<..<b} \<Longrightarrow> P x" "a < b"
  shows   "eventually P (at_left b)"
  using assms unfolding eventually_at_topological by (intro exI[of _ "{a<..}"]) auto

lemma (in order_topology) eventually_at_rightI:
  assumes "\<And>x. x \<in> {a<..<b} \<Longrightarrow> P x" "a < b"
  shows   "eventually P (at_right a)"
  using assms unfolding eventually_at_topological by (intro exI[of _ "{..<b}"]) auto

lemma eventually_filtercomap_nhds:
  "eventually P (filtercomap f (nhds x)) \<longleftrightarrow> (\<exists>S. open S \<and> x \<in> S \<and> (\<forall>x. f x \<in> S \<longrightarrow> P x))"
  unfolding eventually_filtercomap eventually_nhds by auto

lemma eventually_filtercomap_at_topological:
  "eventually P (filtercomap f (at A within B)) \<longleftrightarrow> 
     (\<exists>S. open S \<and> A \<in> S \<and> (\<forall>x. f x \<in> S \<inter> B - {A} \<longrightarrow> P x))" (is "?lhs = ?rhs")
  unfolding at_within_def filtercomap_inf eventually_inf_principal filtercomap_principal 
          eventually_filtercomap_nhds eventually_principal by blast

lemma eventually_at_right_field:
  "eventually P (at_right x) \<longleftrightarrow> (\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> P y)"
  for x :: "'a::{linordered_field, linorder_topology}"
  using linordered_field_no_ub[rule_format, of x]
  by (auto simp: eventually_at_right)

lemma eventually_at_left_field:
  "eventually P (at_left x) \<longleftrightarrow> (\<exists>b<x. \<forall>y>b. y < x \<longrightarrow> P y)"
  for x :: "'a::{linordered_field, linorder_topology}"
  using linordered_field_no_lb[rule_format, of x]
  by (auto simp: eventually_at_left)


subsubsection \<open>Tendsto\<close>

abbreviation (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool"  (infixr "\<longlongrightarrow>" 55)
  where "(f \<longlongrightarrow> l) F \<equiv> filterlim f (nhds l) F"

definition (in t2_space) Lim :: "'f filter \<Rightarrow> ('f \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Lim A f = (THE l. (f \<longlongrightarrow> l) A)"

lemma (in topological_space) tendsto_eq_rhs: "(f \<longlongrightarrow> x) F \<Longrightarrow> x = y \<Longrightarrow> (f \<longlongrightarrow> y) F"
  by simp

named_theorems tendsto_intros "introduction rules for tendsto"
setup \<open>
  Global_Theory.add_thms_dynamic (\<^binding>\<open>tendsto_eq_intros\<close>,
    fn context =>
      Named_Theorems.get (Context.proof_of context) \<^named_theorems>\<open>tendsto_intros\<close>
      |> map_filter (try (fn thm => @{thm tendsto_eq_rhs} OF [thm])))
\<close>

context topological_space begin

lemma tendsto_def:
   "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F)"
   unfolding nhds_def filterlim_INF filterlim_principal by auto

lemma tendsto_cong: "(f \<longlongrightarrow> c) F \<longleftrightarrow> (g \<longlongrightarrow> c) F" if "eventually (\<lambda>x. f x = g x) F"
  by (rule filterlim_cong [OF refl refl that])

lemma tendsto_mono: "F \<le> F' \<Longrightarrow> (f \<longlongrightarrow> l) F' \<Longrightarrow> (f \<longlongrightarrow> l) F"
  unfolding tendsto_def le_filter_def by fast

lemma tendsto_ident_at [tendsto_intros, simp, intro]: "((\<lambda>x. x) \<longlongrightarrow> a) (at a within s)"
  by (auto simp: tendsto_def eventually_at_topological)

lemma tendsto_const [tendsto_intros, simp, intro]: "((\<lambda>x. k) \<longlongrightarrow> k) F"
  by (simp add: tendsto_def)

lemma filterlim_at:
  "(LIM x F. f x :> at b within s) \<longleftrightarrow> eventually (\<lambda>x. f x \<in> s \<and> f x \<noteq> b) F \<and> (f \<longlongrightarrow> b) F"
  by (simp add: at_within_def filterlim_inf filterlim_principal conj_commute)

lemma (in -)
  assumes "filterlim f (nhds L) F"
  shows tendsto_imp_filterlim_at_right:
          "eventually (\<lambda>x. f x > L) F \<Longrightarrow> filterlim f (at_right L) F"
    and tendsto_imp_filterlim_at_left:
          "eventually (\<lambda>x. f x < L) F \<Longrightarrow> filterlim f (at_left L) F"
  using assms by (auto simp: filterlim_at elim: eventually_mono)

lemma  filterlim_at_withinI:
  assumes "filterlim f (nhds c) F"
  assumes "eventually (\<lambda>x. f x \<in> A - {c}) F"
  shows   "filterlim f (at c within A) F"
  using assms by (simp add: filterlim_at)

lemma filterlim_atI:
  assumes "filterlim f (nhds c) F"
  assumes "eventually (\<lambda>x. f x \<noteq> c) F"
  shows   "filterlim f (at c) F"
  using assms by (intro filterlim_at_withinI) simp_all

lemma topological_tendstoI:
  "(\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F) \<Longrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: tendsto_def)

lemma topological_tendstoD:
  "(f \<longlongrightarrow> l) F \<Longrightarrow> open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F"
  by (auto simp: tendsto_def)

lemma tendsto_bot [simp]: "(f \<longlongrightarrow> a) bot"
  by (simp add: tendsto_def)

lemma tendsto_eventually: "eventually (\<lambda>x. f x = l) net \<Longrightarrow> ((\<lambda>x. f x) \<longlongrightarrow> l) net"
  by (rule topological_tendstoI) (auto elim: eventually_mono)

(* Contributed by Dominique Unruh *)
lemma tendsto_principal_singleton[simp]:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

end

lemma (in topological_space) filterlim_within_subset:
  "filterlim f l (at x within S) \<Longrightarrow> T \<subseteq> S \<Longrightarrow> filterlim f l (at x within T)"
  by (blast intro: filterlim_mono at_le)

lemmas tendsto_within_subset = filterlim_within_subset

lemma (in order_topology) order_tendsto_iff:
  "(f \<longlongrightarrow> x) F \<longleftrightarrow> (\<forall>l<x. eventually (\<lambda>x. l < f x) F) \<and> (\<forall>u>x. eventually (\<lambda>x. f x < u) F)"
  by (auto simp: nhds_order filterlim_inf filterlim_INF filterlim_principal)

lemma (in order_topology) order_tendstoI:
  "(\<And>a. a < y \<Longrightarrow> eventually (\<lambda>x. a < f x) F) \<Longrightarrow> (\<And>a. y < a \<Longrightarrow> eventually (\<lambda>x. f x < a) F) \<Longrightarrow>
    (f \<longlongrightarrow> y) F"
  by (auto simp: order_tendsto_iff)

lemma (in order_topology) order_tendstoD:
  assumes "(f \<longlongrightarrow> y) F"
  shows "a < y \<Longrightarrow> eventually (\<lambda>x. a < f x) F"
    and "y < a \<Longrightarrow> eventually (\<lambda>x. f x < a) F"
  using assms by (auto simp: order_tendsto_iff)

lemma (in linorder_topology) tendsto_max[tendsto_intros]:
  assumes X: "(X \<longlongrightarrow> x) net"
    and Y: "(Y \<longlongrightarrow> y) net"
  shows "((\<lambda>x. max (X x) (Y x)) \<longlongrightarrow> max x y) net"
proof (rule order_tendstoI)
  fix a
  assume "a < max x y"
  then show "eventually (\<lambda>x. a < max (X x) (Y x)) net"
    using order_tendstoD(1)[OF X, of a] order_tendstoD(1)[OF Y, of a]
    by (auto simp: less_max_iff_disj elim: eventually_mono)
next
  fix a
  assume "max x y < a"
  then show "eventually (\<lambda>x. max (X x) (Y x) < a) net"
    using order_tendstoD(2)[OF X, of a] order_tendstoD(2)[OF Y, of a]
    by (auto simp: eventually_conj_iff)
qed

lemma (in linorder_topology) tendsto_min[tendsto_intros]:
  assumes X: "(X \<longlongrightarrow> x) net"
    and Y: "(Y \<longlongrightarrow> y) net"
  shows "((\<lambda>x. min (X x) (Y x)) \<longlongrightarrow> min x y) net"
proof (rule order_tendstoI)
  fix a
  assume "a < min x y"
  then show "eventually (\<lambda>x. a < min (X x) (Y x)) net"
    using order_tendstoD(1)[OF X, of a] order_tendstoD(1)[OF Y, of a]
    by (auto simp: eventually_conj_iff)
next
  fix a
  assume "min x y < a"
  then show "eventually (\<lambda>x. min (X x) (Y x) < a) net"
    using order_tendstoD(2)[OF X, of a] order_tendstoD(2)[OF Y, of a]
    by (auto simp: min_less_iff_disj elim: eventually_mono)
qed

lemma (in order_topology)
  assumes "a < b"
  shows at_within_Icc_at_right: "at a within {a..b} = at_right a"
    and at_within_Icc_at_left:  "at b within {a..b} = at_left b"
  using order_tendstoD(2)[OF tendsto_ident_at assms, of "{a<..}"]
  using order_tendstoD(1)[OF tendsto_ident_at assms, of "{..<b}"]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

lemma (in order_topology) at_within_Icc_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a..b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in t2_space) tendsto_unique:
  assumes "F \<noteq> bot"
    and "(f \<longlongrightarrow> a) F"
    and "(f \<longlongrightarrow> b) F"
  shows "a = b"
proof (rule ccontr)
  assume "a \<noteq> b"
  obtain U V where "open U" "open V" "a \<in> U" "b \<in> V" "U \<inter> V = {}"
    using hausdorff [OF \<open>a \<noteq> b\<close>] by fast
  have "eventually (\<lambda>x. f x \<in> U) F"
    using \<open>(f \<longlongrightarrow> a) F\<close> \<open>open U\<close> \<open>a \<in> U\<close> by (rule topological_tendstoD)
  moreover
  have "eventually (\<lambda>x. f x \<in> V) F"
    using \<open>(f \<longlongrightarrow> b) F\<close> \<open>open V\<close> \<open>b \<in> V\<close> by (rule topological_tendstoD)
  ultimately
  have "eventually (\<lambda>x. False) F"
  proof eventually_elim
    case (elim x)
    then have "f x \<in> U \<inter> V" by simp
    with \<open>U \<inter> V = {}\<close> show ?case by simp
  qed
  with \<open>\<not> trivial_limit F\<close> show "False"
    by (simp add: trivial_limit_def)
qed

lemma (in t2_space) tendsto_const_iff:
  fixes a b :: 'a
  assumes "\<not> trivial_limit F"
  shows "((\<lambda>x. a) \<longlongrightarrow> b) F \<longleftrightarrow> a = b"
  by (auto intro!: tendsto_unique [OF assms tendsto_const])

lemma (in t2_space) tendsto_unique':
 assumes "F \<noteq> bot"
 shows "\<exists>\<^sub>\<le>\<^sub>1l. (f \<longlongrightarrow> l) F"
 using Uniq_def assms local.tendsto_unique by fastforce

lemma Lim_in_closed_set:
  assumes "closed S" "eventually (\<lambda>x. f(x) \<in> S) F" "F \<noteq> bot" "(f \<longlongrightarrow> l) F"
  shows "l \<in> S"
proof (rule ccontr)
  assume "l \<notin> S"
  with \<open>closed S\<close> have "open (- S)" "l \<in> - S"
    by (simp_all add: open_Compl)
  with assms(4) have "eventually (\<lambda>x. f x \<in> - S) F"
    by (rule topological_tendstoD)
  with assms(2) have "eventually (\<lambda>x. False) F"
    by (rule eventually_elim2) simp
  with assms(3) show "False"
    by (simp add: eventually_False)
qed

lemma (in t3_space) nhds_closed:
  assumes "x \<in> A" and "open A"
  shows   "\<exists>A'. x \<in> A' \<and> closed A' \<and> A' \<subseteq> A \<and> eventually (\<lambda>y. y \<in> A') (nhds x)"
proof -
  from assms have "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> - A \<subseteq> V \<and> U \<inter> V = {}"
    by (intro t3_space) auto
  then obtain U V where UV: "open U" "open V" "x \<in> U" "-A \<subseteq> V" "U \<inter> V = {}"
    by auto
  have "eventually (\<lambda>y. y \<in> U) (nhds x)"
    using \<open>open U\<close> and \<open>x \<in> U\<close> by (intro eventually_nhds_in_open)
  hence "eventually (\<lambda>y. y \<in> -V) (nhds x)"
    by eventually_elim (use UV in auto)
  with UV show ?thesis by (intro exI[of _ "-V"]) auto
qed

lemma (in order_topology) increasing_tendsto:
  assumes bdd: "eventually (\<lambda>n. f n \<le> l) F"
    and en: "\<And>x. x < l \<Longrightarrow> eventually (\<lambda>n. x < f n) F"
  shows "(f \<longlongrightarrow> l) F"
  using assms by (intro order_tendstoI) (auto elim!: eventually_mono)

lemma (in order_topology) decreasing_tendsto:
  assumes bdd: "eventually (\<lambda>n. l \<le> f n) F"
    and en: "\<And>x. l < x \<Longrightarrow> eventually (\<lambda>n. f n < x) F"
  shows "(f \<longlongrightarrow> l) F"
  using assms by (intro order_tendstoI) (auto elim!: eventually_mono)

lemma (in order_topology) tendsto_sandwich:
  assumes ev: "eventually (\<lambda>n. f n \<le> g n) net" "eventually (\<lambda>n. g n \<le> h n) net"
  assumes lim: "(f \<longlongrightarrow> c) net" "(h \<longlongrightarrow> c) net"
  shows "(g \<longlongrightarrow> c) net"
proof (rule order_tendstoI)
  fix a
  show "a < c \<Longrightarrow> eventually (\<lambda>x. a < g x) net"
    using order_tendstoD[OF lim(1), of a] ev by (auto elim: eventually_elim2)
next
  fix a
  show "c < a \<Longrightarrow> eventually (\<lambda>x. g x < a) net"
    using order_tendstoD[OF lim(2), of a] ev by (auto elim: eventually_elim2)
qed

lemma (in t1_space) limit_frequently_eq:
  assumes "F \<noteq> bot"
    and "frequently (\<lambda>x. f x = c) F"
    and "(f \<longlongrightarrow> d) F"
  shows "d = c"
proof (rule ccontr)
  assume "d \<noteq> c"
  from t1_space[OF this] obtain U where "open U" "d \<in> U" "c \<notin> U"
    by blast
  with assms have "eventually (\<lambda>x. f x \<in> U) F"
    unfolding tendsto_def by blast
  then have "eventually (\<lambda>x. f x \<noteq> c) F"
    by eventually_elim (insert \<open>c \<notin> U\<close>, blast)
  with assms(2) show False
    unfolding frequently_def by contradiction
qed

lemma (in t1_space) tendsto_imp_eventually_ne:
  assumes  "(f \<longlongrightarrow> c) F" "c \<noteq> c'"
  shows "eventually (\<lambda>z. f z \<noteq> c') F"
proof (cases "F=bot")
  case True
  thus ?thesis by auto
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> eventually (\<lambda>z. f z \<noteq> c') F"
    then have "frequently (\<lambda>z. f z = c') F"
      by (simp add: frequently_def)
    from limit_frequently_eq[OF False this \<open>(f \<longlongrightarrow> c) F\<close>] and \<open>c \<noteq> c'\<close> show False
      by contradiction
  qed
qed

lemma (in linorder_topology) tendsto_le:
  assumes F: "\<not> trivial_limit F"
    and x: "(f \<longlongrightarrow> x) F"
    and y: "(g \<longlongrightarrow> y) F"
    and ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
proof (rule ccontr)
  assume "\<not> y \<le> x"
  with less_separate[of x y] obtain a b where xy: "x < a" "b < y" "{..<a} \<inter> {b<..} = {}"
    by (auto simp: not_le)
  then have "eventually (\<lambda>x. f x < a) F" "eventually (\<lambda>x. b < g x) F"
    using x y by (auto intro: order_tendstoD)
  with ev have "eventually (\<lambda>x. False) F"
    by eventually_elim (insert xy, fastforce)
  with F show False
    by (simp add: eventually_False)
qed

lemma (in linorder_topology) tendsto_lowerbound:
  assumes x: "(f \<longlongrightarrow> x) F"
      and ev: "eventually (\<lambda>i. a \<le> f i) F"
      and F: "\<not> trivial_limit F"
  shows "a \<le> x"
  using F x tendsto_const ev by (rule tendsto_le)

lemma (in linorder_topology) tendsto_upperbound:
  assumes x: "(f \<longlongrightarrow> x) F"
      and ev: "eventually (\<lambda>i. a \<ge> f i) F"
      and F: "\<not> trivial_limit F"
  shows "a \<ge> x"
  by (rule tendsto_le [OF F tendsto_const x ev])

lemma filterlim_at_within_not_equal:
  fixes f::"'a \<Rightarrow> 'b::t2_space"
  assumes "filterlim f (at a within s) F"
  shows "eventually (\<lambda>w. f w\<in>s \<and> f w \<noteq>b) F"
proof (cases "a=b")
  case True
  then show ?thesis using assms by (simp add: filterlim_at)
next
  case False
  from hausdorff[OF this] obtain U V where UV:"open U" "open V" "a \<in> U" "b \<in> V" "U \<inter> V = {}"
    by auto  
  have "(f \<longlongrightarrow> a) F" using assms filterlim_at by auto
  then have "\<forall>\<^sub>F x in F. f x \<in> U" using UV unfolding tendsto_def by auto
  moreover have  "\<forall>\<^sub>F x in F. f x \<in> s \<and> f x\<noteq>a" using assms filterlim_at by auto
  ultimately show ?thesis 
    apply eventually_elim
    using UV by auto
qed

subsubsection \<open>Rules about \<^const>\<open>Lim\<close>\<close>

lemma tendsto_Lim: "\<not> trivial_limit net \<Longrightarrow> (f \<longlongrightarrow> l) net \<Longrightarrow> Lim net f = l"
  unfolding Lim_def using tendsto_unique [of net f] by auto

lemma Lim_ident_at: "\<not> trivial_limit (at x within s) \<Longrightarrow> Lim (at x within s) (\<lambda>x. x) = x"
  by (rule tendsto_Lim[OF _ tendsto_ident_at]) auto

lemma eventually_Lim_ident_at:
  "(\<forall>\<^sub>F y in at x within X. P (Lim (at x within X) (\<lambda>x. x)) y) \<longleftrightarrow>
    (\<forall>\<^sub>F y in at x within X. P x y)" for x::"'a::t2_space"
  by (cases "at x within X = bot") (auto simp: Lim_ident_at)

lemma filterlim_at_bot_at_right:
  fixes f :: "'a::linorder_topology \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
    and bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
    and Q: "eventually Q (at_right a)"
    and bound: "\<And>b. Q b \<Longrightarrow> a < b"
    and P: "eventually P at_bot"
  shows "filterlim f at_bot (at_right a)"
proof -
  from P obtain x where x: "\<And>y. y \<le> x \<Longrightarrow> P y"
    unfolding eventually_at_bot_linorder by auto
  show ?thesis
  proof (intro filterlim_at_bot_le[THEN iffD2] allI impI)
    fix z
    assume "z \<le> x"
    with x have "P z" by auto
    have "eventually (\<lambda>x. x \<le> g z) (at_right a)"
      using bound[OF bij(2)[OF \<open>P z\<close>]]
      unfolding eventually_at_right[OF bound[OF bij(2)[OF \<open>P z\<close>]]]
      by (auto intro!: exI[of _ "g z"])
    with Q show "eventually (\<lambda>x. f x \<le> z) (at_right a)"
      by eventually_elim (metis bij \<open>P z\<close> mono)
  qed
qed

lemma filterlim_at_top_at_left:
  fixes f :: "'a::linorder_topology \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
    and bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
    and Q: "eventually Q (at_left a)"
    and bound: "\<And>b. Q b \<Longrightarrow> b < a"
    and P: "eventually P at_top"
  shows "filterlim f at_top (at_left a)"
proof -
  from P obtain x where x: "\<And>y. x \<le> y \<Longrightarrow> P y"
    unfolding eventually_at_top_linorder by auto
  show ?thesis
  proof (intro filterlim_at_top_ge[THEN iffD2] allI impI)
    fix z
    assume "x \<le> z"
    with x have "P z" by auto
    have "eventually (\<lambda>x. g z \<le> x) (at_left a)"
      using bound[OF bij(2)[OF \<open>P z\<close>]]
      unfolding eventually_at_left[OF bound[OF bij(2)[OF \<open>P z\<close>]]]
      by (auto intro!: exI[of _ "g z"])
    with Q show "eventually (\<lambda>x. z \<le> f x) (at_left a)"
      by eventually_elim (metis bij \<open>P z\<close> mono)
  qed
qed

lemma filterlim_split_at:
  "filterlim f F (at_left x) \<Longrightarrow> filterlim f F (at_right x) \<Longrightarrow>
    filterlim f F (at x)"
  for x :: "'a::linorder_topology"
  by (subst at_eq_sup_left_right) (rule filterlim_sup)

lemma filterlim_at_split:
  "filterlim f F (at x) \<longleftrightarrow> filterlim f F (at_left x) \<and> filterlim f F (at_right x)"
  for x :: "'a::linorder_topology"
  by (subst at_eq_sup_left_right) (simp add: filterlim_def filtermap_sup)

lemma eventually_nhds_top:
  fixes P :: "'a :: {order_top,linorder_topology} \<Rightarrow> bool"
    and b :: 'a
  assumes "b < top"
  shows "eventually P (nhds top) \<longleftrightarrow> (\<exists>b<top. (\<forall>z. b < z \<longrightarrow> P z))"
  unfolding eventually_nhds
proof safe
  fix S :: "'a set"
  assume "open S" "top \<in> S"
  note open_left[OF this \<open>b < top\<close>]
  moreover assume "\<forall>s\<in>S. P s"
  ultimately show "\<exists>b<top. \<forall>z>b. P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b
  assume "b < top" "\<forall>z>b. P z"
  then show "\<exists>S. open S \<and> top \<in> S \<and> (\<forall>xa\<in>S. P xa)"
    by (intro exI[of _ "{b <..}"]) auto
qed

lemma tendsto_at_within_iff_tendsto_nhds:
  "(g \<longlongrightarrow> g l) (at l within S) \<longleftrightarrow> (g \<longlongrightarrow> g l) (inf (nhds l) (principal S))"
  unfolding tendsto_def eventually_at_filter eventually_inf_principal
  by (intro ext all_cong imp_cong) (auto elim!: eventually_mono)


subsection \<open>Limits on sequences\<close>

abbreviation (in topological_space)
  LIMSEQ :: "[nat \<Rightarrow> 'a, 'a] \<Rightarrow> bool"  ("((_)/ \<longlonglongrightarrow> (_))" [60, 60] 60)
  where "X \<longlonglongrightarrow> L \<equiv> (X \<longlongrightarrow> L) sequentially"

abbreviation (in t2_space) lim :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "lim X \<equiv> Lim sequentially X"

definition (in topological_space) convergent :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "convergent X = (\<exists>L. X \<longlonglongrightarrow> L)"

lemma lim_def: "lim X = (THE L. X \<longlonglongrightarrow> L)"
  unfolding Lim_def ..

lemma lim_explicit:
  "f \<longlonglongrightarrow> f0 \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> f0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> S))"
  unfolding tendsto_def eventually_sequentially by auto


subsection \<open>Monotone sequences and subsequences\<close>

text \<open>
  Definition of monotonicity.
  The use of disjunction here complicates proofs considerably.
  One alternative is to add a Boolean argument to indicate the direction.
  Another is to develop the notions of increasing and decreasing first.
\<close>
definition monoseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool"
  where "monoseq X \<longleftrightarrow> (\<forall>m. \<forall>n\<ge>m. X m \<le> X n) \<or> (\<forall>m. \<forall>n\<ge>m. X n \<le> X m)"

abbreviation incseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool"
  where "incseq X \<equiv> mono X"

lemma incseq_def: "incseq X \<longleftrightarrow> (\<forall>m. \<forall>n\<ge>m. X n \<ge> X m)"
  unfolding mono_def ..

abbreviation decseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool"
  where "decseq X \<equiv> antimono X"

lemma decseq_def: "decseq X \<longleftrightarrow> (\<forall>m. \<forall>n\<ge>m. X n \<le> X m)"
  unfolding antimono_def ..

subsubsection \<open>Definition of subsequence.\<close>

(* For compatibility with the old "subseq" *)
lemma strict_mono_leD: "strict_mono r \<Longrightarrow> m \<le> n \<Longrightarrow> r m \<le> r n"
  by (erule (1) monoD [OF strict_mono_mono])

lemma strict_mono_id: "strict_mono id"
  by (simp add: strict_mono_def)

lemma incseq_SucI: "(\<And>n. X n \<le> X (Suc n)) \<Longrightarrow> incseq X"
  using lift_Suc_mono_le[of X] by (auto simp: incseq_def)

lemma incseqD: "incseq f \<Longrightarrow> i \<le> j \<Longrightarrow> f i \<le> f j"
  by (auto simp: incseq_def)

lemma incseq_SucD: "incseq A \<Longrightarrow> A i \<le> A (Suc i)"
  using incseqD[of A i "Suc i"] by auto

lemma incseq_Suc_iff: "incseq f \<longleftrightarrow> (\<forall>n. f n \<le> f (Suc n))"
  by (auto intro: incseq_SucI dest: incseq_SucD)

lemma incseq_const[simp, intro]: "incseq (\<lambda>x. k)"
  unfolding incseq_def by auto

lemma decseq_SucI: "(\<And>n. X (Suc n) \<le> X n) \<Longrightarrow> decseq X"
  using order.lift_Suc_mono_le[OF dual_order, of X] by (auto simp: decseq_def)

lemma decseqD: "decseq f \<Longrightarrow> i \<le> j \<Longrightarrow> f j \<le> f i"
  by (auto simp: decseq_def)

lemma decseq_SucD: "decseq A \<Longrightarrow> A (Suc i) \<le> A i"
  using decseqD[of A i "Suc i"] by auto

lemma decseq_Suc_iff: "decseq f \<longleftrightarrow> (\<forall>n. f (Suc n) \<le> f n)"
  by (auto intro: decseq_SucI dest: decseq_SucD)

lemma decseq_const[simp, intro]: "decseq (\<lambda>x. k)"
  unfolding decseq_def by auto

lemma monoseq_iff: "monoseq X \<longleftrightarrow> incseq X \<or> decseq X"
  unfolding monoseq_def incseq_def decseq_def ..

lemma monoseq_Suc: "monoseq X \<longleftrightarrow> (\<forall>n. X n \<le> X (Suc n)) \<or> (\<forall>n. X (Suc n) \<le> X n)"
  unfolding monoseq_iff incseq_Suc_iff decseq_Suc_iff ..

lemma monoI1: "\<forall>m. \<forall>n \<ge> m. X m \<le> X n \<Longrightarrow> monoseq X"
  by (simp add: monoseq_def)

lemma monoI2: "\<forall>m. \<forall>n \<ge> m. X n \<le> X m \<Longrightarrow> monoseq X"
  by (simp add: monoseq_def)

lemma mono_SucI1: "\<forall>n. X n \<le> X (Suc n) \<Longrightarrow> monoseq X"
  by (simp add: monoseq_Suc)

lemma mono_SucI2: "\<forall>n. X (Suc n) \<le> X n \<Longrightarrow> monoseq X"
  by (simp add: monoseq_Suc)

lemma monoseq_minus:
  fixes a :: "nat \<Rightarrow> 'a::ordered_ab_group_add"
  assumes "monoseq a"
  shows "monoseq (\<lambda> n. - a n)"
proof (cases "\<forall>m. \<forall>n \<ge> m. a m \<le> a n")
  case True
  then have "\<forall>m. \<forall>n \<ge> m. - a n \<le> - a m" by auto
  then show ?thesis by (rule monoI2)
next
  case False
  then have "\<forall>m. \<forall>n \<ge> m. - a m \<le> - a n"
    using \<open>monoseq a\<close>[unfolded monoseq_def] by auto
  then show ?thesis by (rule monoI1)
qed


subsubsection \<open>Subsequence (alternative definition, (e.g. Hoskins)\<close>

lemma strict_mono_Suc_iff: "strict_mono f \<longleftrightarrow> (\<forall>n. f n < f (Suc n))"
proof (intro iffI strict_monoI)
  assume *: "\<forall>n. f n < f (Suc n)"
  fix m n :: nat assume "m < n"
  thus "f m < f n"
    by (induction rule: less_Suc_induct) (use * in auto)
qed (auto simp: strict_mono_def)

lemma strict_mono_add: "strict_mono (\<lambda>n::'a::linordered_semidom. n + k)"
  by (auto simp: strict_mono_def)

text \<open>For any sequence, there is a monotonic subsequence.\<close>
lemma seq_monosub:
  fixes s :: "nat \<Rightarrow> 'a::linorder"
  shows "\<exists>f. strict_mono f \<and> monoseq (\<lambda>n. (s (f n)))"
proof (cases "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. s m \<le> s p")
  case True
  then have "\<exists>f. \<forall>n. (\<forall>m\<ge>f n. s m \<le> s (f n)) \<and> f n < f (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain f :: "nat \<Rightarrow> nat" 
    where f: "strict_mono f" and mono: "\<And>n m. f n \<le> m \<Longrightarrow> s m \<le> s (f n)"
    by (auto simp: strict_mono_Suc_iff)
  then have "incseq f"
    unfolding strict_mono_Suc_iff incseq_Suc_iff by (auto intro: less_imp_le)
  then have "monoseq (\<lambda>n. s (f n))"
    by (auto simp add: incseq_def intro!: mono monoI2)
  with f show ?thesis
    by auto
next
  case False
  then obtain N where N: "p > N \<Longrightarrow> \<exists>m>p. s p < s m" for p
    by (force simp: not_le le_less)
  have "\<exists>f. \<forall>n. N < f n \<and> f n < f (Suc n) \<and> s (f n) \<le> s (f (Suc n))"
  proof (intro dependent_nat_choice)
    fix x
    assume "N < x" with N[of x]
    show "\<exists>y>N. x < y \<and> s x \<le> s y"
      by (auto intro: less_trans)
  qed auto
  then show ?thesis
    by (auto simp: monoseq_iff incseq_Suc_iff strict_mono_Suc_iff)
qed

lemma seq_suble:
  assumes sf: "strict_mono (f :: nat \<Rightarrow> nat)"
  shows "n \<le> f n"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  with sf [unfolded strict_mono_Suc_iff, rule_format, of n] have "n < f (Suc n)"
     by arith
  then show ?case by arith
qed

lemma eventually_subseq:
  "strict_mono r \<Longrightarrow> eventually P sequentially \<Longrightarrow> eventually (\<lambda>n. P (r n)) sequentially"
  unfolding eventually_sequentially by (metis seq_suble le_trans)

lemma not_eventually_sequentiallyD:
  assumes "\<not> eventually P sequentially"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (\<forall>n. \<not> P (r n))"
proof -
  from assms have "\<forall>n. \<exists>m\<ge>n. \<not> P m"
    unfolding eventually_sequentially by (simp add: not_less)
  then obtain r where "\<And>n. r n \<ge> n" "\<And>n. \<not> P (r n)"
    by (auto simp: choice_iff)
  then show ?thesis
    by (auto intro!: exI[of _ "\<lambda>n. r (((Suc \<circ> r) ^^ Suc n) 0)"]
             simp: less_eq_Suc_le strict_mono_Suc_iff)
qed

lemma sequentially_offset: 
  assumes "eventually (\<lambda>i. P i) sequentially"
  shows "eventually (\<lambda>i. P (i + k)) sequentially"
  using assms by (rule eventually_sequentially_seg [THEN iffD2])

lemma seq_offset_neg: 
  "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> ((\<lambda>i. f(i - k)) \<longlongrightarrow> l) sequentially"
  apply (erule filterlim_compose)
  apply (simp add: filterlim_def le_sequentially eventually_filtermap eventually_sequentially, arith)
  done

lemma filterlim_subseq: "strict_mono f \<Longrightarrow> filterlim f sequentially sequentially"
  unfolding filterlim_iff by (metis eventually_subseq)

lemma strict_mono_o: "strict_mono r \<Longrightarrow> strict_mono s \<Longrightarrow> strict_mono (r \<circ> s)"
  unfolding strict_mono_def by simp

lemma strict_mono_compose: "strict_mono r \<Longrightarrow> strict_mono s \<Longrightarrow> strict_mono (\<lambda>x. r (s x))"
  using strict_mono_o[of r s] by (simp add: o_def)

lemma incseq_imp_monoseq:  "incseq X \<Longrightarrow> monoseq X"
  by (simp add: incseq_def monoseq_def)

lemma decseq_imp_monoseq:  "decseq X \<Longrightarrow> monoseq X"
  by (simp add: decseq_def monoseq_def)

lemma decseq_eq_incseq: "decseq X = incseq (\<lambda>n. - X n)"
  for X :: "nat \<Rightarrow> 'a::ordered_ab_group_add"
  by (simp add: decseq_def incseq_def)

lemma INT_decseq_offset:
  assumes "decseq F"
  shows "(\<Inter>i. F i) = (\<Inter>i\<in>{n..}. F i)"
proof safe
  fix x i
  assume x: "x \<in> (\<Inter>i\<in>{n..}. F i)"
  show "x \<in> F i"
  proof cases
    from x have "x \<in> F n" by auto
    also assume "i \<le> n" with \<open>decseq F\<close> have "F n \<subseteq> F i"
      unfolding decseq_def by simp
    finally show ?thesis .
  qed (insert x, simp)
qed auto

lemma LIMSEQ_const_iff: "(\<lambda>n. k) \<longlonglongrightarrow> l \<longleftrightarrow> k = l"
  for k l :: "'a::t2_space"
  using trivial_limit_sequentially by (rule tendsto_const_iff)

lemma LIMSEQ_SUP: "incseq X \<Longrightarrow> X \<longlonglongrightarrow> (SUP i. X i :: 'a::{complete_linorder,linorder_topology})"
  by (intro increasing_tendsto)
    (auto simp: SUP_upper less_SUP_iff incseq_def eventually_sequentially intro: less_le_trans)

lemma LIMSEQ_INF: "decseq X \<Longrightarrow> X \<longlonglongrightarrow> (INF i. X i :: 'a::{complete_linorder,linorder_topology})"
  by (intro decreasing_tendsto)
    (auto simp: INF_lower INF_less_iff decseq_def eventually_sequentially intro: le_less_trans)

lemma LIMSEQ_ignore_initial_segment: "f \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda>n. f (n + k)) \<longlonglongrightarrow> a"
  unfolding tendsto_def by (subst eventually_sequentially_seg[where k=k])

lemma LIMSEQ_offset: "(\<lambda>n. f (n + k)) \<longlonglongrightarrow> a \<Longrightarrow> f \<longlonglongrightarrow> a"
  unfolding tendsto_def
  by (subst (asm) eventually_sequentially_seg[where k=k])

lemma LIMSEQ_Suc: "f \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda>n. f (Suc n)) \<longlonglongrightarrow> l"
  by (drule LIMSEQ_ignore_initial_segment [where k="Suc 0"]) simp

lemma LIMSEQ_imp_Suc: "(\<lambda>n. f (Suc n)) \<longlonglongrightarrow> l \<Longrightarrow> f \<longlonglongrightarrow> l"
  by (rule LIMSEQ_offset [where k="Suc 0"]) simp

lemma LIMSEQ_lessThan_iff_atMost:
  shows "(\<lambda>n. f {..<n}) \<longlonglongrightarrow> x \<longleftrightarrow> (\<lambda>n. f {..n}) \<longlonglongrightarrow> x"
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp only: lessThan_Suc_atMost)
  done

lemma (in t2_space) LIMSEQ_Uniq: "\<exists>\<^sub>\<le>\<^sub>1l. X \<longlonglongrightarrow> l"
 by (simp add: tendsto_unique')

lemma (in t2_space) LIMSEQ_unique: "X \<longlonglongrightarrow> a \<Longrightarrow> X \<longlonglongrightarrow> b \<Longrightarrow> a = b"
  using trivial_limit_sequentially by (rule tendsto_unique)

lemma LIMSEQ_le_const: "X \<longlonglongrightarrow> x \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. a \<le> X n \<Longrightarrow> a \<le> x"
  for a x :: "'a::linorder_topology"
  by (simp add: eventually_at_top_linorder tendsto_lowerbound)

lemma LIMSEQ_le: "X \<longlonglongrightarrow> x \<Longrightarrow> Y \<longlonglongrightarrow> y \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. X n \<le> Y n \<Longrightarrow> x \<le> y"
  for x y :: "'a::linorder_topology"
  using tendsto_le[of sequentially Y y X x] by (simp add: eventually_sequentially)

lemma LIMSEQ_le_const2: "X \<longlonglongrightarrow> x \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. X n \<le> a \<Longrightarrow> x \<le> a"
  for a x :: "'a::linorder_topology"
  by (rule LIMSEQ_le[of X x "\<lambda>n. a"]) auto

lemma Lim_bounded: "f \<longlonglongrightarrow> l \<Longrightarrow> \<forall>n\<ge>M. f n \<le> C \<Longrightarrow> l \<le> C"
  for l :: "'a::linorder_topology"
  by (intro LIMSEQ_le_const2) auto

lemma Lim_bounded2:
  fixes f :: "nat \<Rightarrow> 'a::linorder_topology"
  assumes lim:"f \<longlonglongrightarrow> l" and ge: "\<forall>n\<ge>N. f n \<ge> C"
  shows "l \<ge> C"
  using ge
  by (intro tendsto_le[OF trivial_limit_sequentially lim tendsto_const])
     (auto simp: eventually_sequentially)

lemma lim_mono:
  fixes X Y :: "nat \<Rightarrow> 'a::linorder_topology"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n \<le> Y n"
    and "X \<longlonglongrightarrow> x"
    and "Y \<longlonglongrightarrow> y"
  shows "x \<le> y"
  using assms(1) by (intro LIMSEQ_le[OF assms(2,3)]) auto

lemma Sup_lim:
  fixes a :: "'a::{complete_linorder,linorder_topology}"
  assumes "\<And>n. b n \<in> s"
    and "b \<longlonglongrightarrow> a"
  shows "a \<le> Sup s"
  by (metis Lim_bounded assms complete_lattice_class.Sup_upper)

lemma Inf_lim:
  fixes a :: "'a::{complete_linorder,linorder_topology}"
  assumes "\<And>n. b n \<in> s"
    and "b \<longlonglongrightarrow> a"
  shows "Inf s \<le> a"
  by (metis Lim_bounded2 assms complete_lattice_class.Inf_lower)

lemma SUP_Lim:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  assumes inc: "incseq X"
    and l: "X \<longlonglongrightarrow> l"
  shows "(SUP n. X n) = l"
  using LIMSEQ_SUP[OF inc] tendsto_unique[OF trivial_limit_sequentially l]
  by simp

lemma INF_Lim:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  assumes dec: "decseq X"
    and l: "X \<longlonglongrightarrow> l"
  shows "(INF n. X n) = l"
  using LIMSEQ_INF[OF dec] tendsto_unique[OF trivial_limit_sequentially l]
  by simp

lemma convergentD: "convergent X \<Longrightarrow> \<exists>L. X \<longlonglongrightarrow> L"
  by (simp add: convergent_def)

lemma convergentI: "X \<longlonglongrightarrow> L \<Longrightarrow> convergent X"
  by (auto simp add: convergent_def)

lemma convergent_LIMSEQ_iff: "convergent X \<longleftrightarrow> X \<longlonglongrightarrow> lim X"
  by (auto intro: theI LIMSEQ_unique simp add: convergent_def lim_def)

lemma convergent_const: "convergent (\<lambda>n. c)"
  by (rule convergentI) (rule tendsto_const)

lemma monoseq_le:
  "monoseq a \<Longrightarrow> a \<longlonglongrightarrow> x \<Longrightarrow>
    (\<forall>n. a n \<le> x) \<and> (\<forall>m. \<forall>n\<ge>m. a m \<le> a n) \<or>
    (\<forall>n. x \<le> a n) \<and> (\<forall>m. \<forall>n\<ge>m. a n \<le> a m)"
  for x :: "'a::linorder_topology"
  by (metis LIMSEQ_le_const LIMSEQ_le_const2 decseq_def incseq_def monoseq_iff)

lemma LIMSEQ_subseq_LIMSEQ: "X \<longlonglongrightarrow> L \<Longrightarrow> strict_mono f \<Longrightarrow> (X \<circ> f) \<longlonglongrightarrow> L"
  unfolding comp_def by (rule filterlim_compose [of X, OF _ filterlim_subseq])

lemma convergent_subseq_convergent: "convergent X \<Longrightarrow> strict_mono f \<Longrightarrow> convergent (X \<circ> f)"
  by (auto simp: convergent_def intro: LIMSEQ_subseq_LIMSEQ)

lemma limI: "X \<longlonglongrightarrow> L \<Longrightarrow> lim X = L"
  by (rule tendsto_Lim) (rule trivial_limit_sequentially)

lemma lim_le: "convergent f \<Longrightarrow> (\<And>n. f n \<le> x) \<Longrightarrow> lim f \<le> x"
  for x :: "'a::linorder_topology"
  using LIMSEQ_le_const2[of f "lim f" x] by (simp add: convergent_LIMSEQ_iff)

lemma lim_const [simp]: "lim (\<lambda>m. a) = a"
  by (simp add: limI)


subsubsection \<open>Increasing and Decreasing Series\<close>

lemma incseq_le: "incseq X \<Longrightarrow> X \<longlonglongrightarrow> L \<Longrightarrow> X n \<le> L"
  for L :: "'a::linorder_topology"
  by (metis incseq_def LIMSEQ_le_const)

lemma decseq_ge: "decseq X \<Longrightarrow> X \<longlonglongrightarrow> L \<Longrightarrow> L \<le> X n"
  for L :: "'a::linorder_topology"
  by (metis decseq_def LIMSEQ_le_const2)


subsection \<open>First countable topologies\<close>

class first_countable_topology = topological_space +
  assumes first_countable_basis:
    "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"

lemma (in first_countable_topology) countable_basis_at_decseq:
  obtains A :: "nat \<Rightarrow> 'a set" where
    "\<And>i. open (A i)" "\<And>i. x \<in> (A i)"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
proof atomize_elim
  from first_countable_basis[of x] obtain A :: "nat \<Rightarrow> 'a set"
    where nhds: "\<And>i. open (A i)" "\<And>i. x \<in> A i"
      and incl: "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>i. A i \<subseteq> S"
    by auto
  define F where "F n = (\<Inter>i\<le>n. A i)" for n
  show "\<exists>A. (\<forall>i. open (A i)) \<and> (\<forall>i. x \<in> A i) \<and>
    (\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially)"
  proof (safe intro!: exI[of _ F])
    fix i
    show "open (F i)"
      using nhds(1) by (auto simp: F_def)
    show "x \<in> F i"
      using nhds(2) by (auto simp: F_def)
  next
    fix S
    assume "open S" "x \<in> S"
    from incl[OF this] obtain i where "F i \<subseteq> S"
      unfolding F_def by auto
    moreover have "\<And>j. i \<le> j \<Longrightarrow> F j \<subseteq> F i"
      by (simp add: Inf_superset_mono F_def image_mono)
    ultimately show "eventually (\<lambda>i. F i \<subseteq> S) sequentially"
      by (auto simp: eventually_sequentially)
  qed
qed

lemma (in first_countable_topology) nhds_countable:
  obtains X :: "nat \<Rightarrow> 'a set"
  where "decseq X" "\<And>n. open (X n)" "\<And>n. x \<in> X n" "nhds x = (INF n. principal (X n))"
proof -
  from first_countable_basis obtain A :: "nat \<Rightarrow> 'a set"
    where *: "\<And>n. x \<in> A n" "\<And>n. open (A n)" "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>i. A i \<subseteq> S"
    by metis
  show thesis
  proof
    show "decseq (\<lambda>n. \<Inter>i\<le>n. A i)"
      by (simp add: antimono_iff_le_Suc atMost_Suc)
    show "x \<in> (\<Inter>i\<le>n. A i)" "\<And>n. open (\<Inter>i\<le>n. A i)" for n
      using * by auto
    show "nhds x = (INF n. principal (\<Inter>i\<le>n. A i))"
      using *
      unfolding nhds_def
      apply -
      apply (rule INF_eq)
       apply simp_all
       apply fastforce
      apply (intro exI [of _ "\<Inter>i\<le>n. A i" for n] conjI open_INT)
         apply auto
      done
  qed
qed

lemma (in first_countable_topology) countable_basis:
  obtains A :: "nat \<Rightarrow> 'a set" where
    "\<And>i. open (A i)" "\<And>i. x \<in> A i"
    "\<And>F. (\<forall>n. F n \<in> A n) \<Longrightarrow> F \<longlonglongrightarrow> x"
proof atomize_elim
  obtain A :: "nat \<Rightarrow> 'a set" where *:
    "\<And>i. open (A i)"
    "\<And>i. x \<in> A i"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by (rule countable_basis_at_decseq) blast
  have "eventually (\<lambda>n. F n \<in> S) sequentially"
    if "\<forall>n. F n \<in> A n" "open S" "x \<in> S" for F S
    using *(3)[of S] that by (auto elim: eventually_mono simp: subset_eq)
  with * show "\<exists>A. (\<forall>i. open (A i)) \<and> (\<forall>i. x \<in> A i) \<and> (\<forall>F. (\<forall>n. F n \<in> A n) \<longrightarrow> F \<longlonglongrightarrow> x)"
    by (intro exI[of _ A]) (auto simp: tendsto_def)
qed

lemma (in first_countable_topology) sequentially_imp_eventually_nhds_within:
  assumes "\<forall>f. (\<forall>n. f n \<in> s) \<and> f \<longlonglongrightarrow> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (inf (nhds a) (principal s))"
proof (rule ccontr)
  obtain A :: "nat \<Rightarrow> 'a set" where *:
    "\<And>i. open (A i)"
    "\<And>i. a \<in> A i"
    "\<And>F. \<forall>n. F n \<in> A n \<Longrightarrow> F \<longlonglongrightarrow> a"
    by (rule countable_basis) blast
  assume "\<not> ?thesis"
  with * have "\<exists>F. \<forall>n. F n \<in> s \<and> F n \<in> A n \<and> \<not> P (F n)"
    unfolding eventually_inf_principal eventually_nhds
    by (intro choice) fastforce
  then obtain F where F: "\<forall>n. F n \<in> s" and "\<forall>n. F n \<in> A n" and F': "\<forall>n. \<not> P (F n)"
    by blast
  with * have "F \<longlonglongrightarrow> a"
    by auto
  then have "eventually (\<lambda>n. P (F n)) sequentially"
    using assms F by simp
  then show False
    by (simp add: F')
qed

lemma (in first_countable_topology) eventually_nhds_within_iff_sequentially:
  "eventually P (inf (nhds a) (principal s)) \<longleftrightarrow>
    (\<forall>f. (\<forall>n. f n \<in> s) \<and> f \<longlonglongrightarrow> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially)"
proof (safe intro!: sequentially_imp_eventually_nhds_within)
  assume "eventually P (inf (nhds a) (principal s))"
  then obtain S where "open S" "a \<in> S" "\<forall>x\<in>S. x \<in> s \<longrightarrow> P x"
    by (auto simp: eventually_inf_principal eventually_nhds)
  moreover
  fix f
  assume "\<forall>n. f n \<in> s" "f \<longlonglongrightarrow> a"
  ultimately show "eventually (\<lambda>n. P (f n)) sequentially"
    by (auto dest!: topological_tendstoD elim: eventually_mono)
qed

lemma (in first_countable_topology) eventually_nhds_iff_sequentially:
  "eventually P (nhds a) \<longleftrightarrow> (\<forall>f. f \<longlonglongrightarrow> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially)"
  using eventually_nhds_within_iff_sequentially[of P a UNIV] by simp

(*Thanks to Sébastien Gouëzel*)
lemma Inf_as_limit:
  fixes A::"'a::{linorder_topology, first_countable_topology, complete_linorder} set"
  assumes "A \<noteq> {}"
  shows "\<exists>u. (\<forall>n. u n \<in> A) \<and> u \<longlonglongrightarrow> Inf A"
proof (cases "Inf A \<in> A")
  case True
  show ?thesis
    by (rule exI[of _ "\<lambda>n. Inf A"], auto simp add: True)
next
  case False
  obtain y where "y \<in> A" using assms by auto
  then have "Inf A < y" using False Inf_lower less_le by auto
  obtain F :: "nat \<Rightarrow> 'a set" where F: "\<And>i. open (F i)" "\<And>i. Inf A \<in> F i"
                                       "\<And>u. (\<forall>n. u n \<in> F n) \<Longrightarrow> u \<longlonglongrightarrow> Inf A"
    by (metis first_countable_topology_class.countable_basis)
  define u where "u = (\<lambda>n. SOME z. z \<in> F n \<and> z \<in> A)"
  have "\<exists>z. z \<in> U \<and> z \<in> A" if "Inf A \<in> U" "open U" for U
  proof -
    obtain b where "b > Inf A" "{Inf A ..<b} \<subseteq> U"
      using open_right[OF \<open>open U\<close> \<open>Inf A \<in> U\<close> \<open>Inf A < y\<close>] by auto
    obtain z where "z < b" "z \<in> A"
      using \<open>Inf A < b\<close> Inf_less_iff by auto
    then have "z \<in> {Inf A ..<b}"
      by (simp add: Inf_lower)
    then show ?thesis using \<open>z \<in> A\<close> \<open>{Inf A ..<b} \<subseteq> U\<close> by auto
  qed
  then have *: "u n \<in> F n \<and> u n \<in> A" for n
    using \<open>Inf A \<in> F n\<close> \<open>open (F n)\<close> unfolding u_def by (metis (no_types, lifting) someI_ex)
  then have "u \<longlonglongrightarrow> Inf A" using F(3) by simp
  then show ?thesis using * by auto
qed

lemma tendsto_at_iff_sequentially:
  "(f \<longlongrightarrow> a) (at x within s) \<longleftrightarrow> (\<forall>X. (\<forall>i. X i \<in> s - {x}) \<longrightarrow> X \<longlonglongrightarrow> x \<longrightarrow> ((f \<circ> X) \<longlonglongrightarrow> a))"
  for f :: "'a::first_countable_topology \<Rightarrow> _"
  unfolding filterlim_def[of _ "nhds a"] le_filter_def eventually_filtermap
    at_within_def eventually_nhds_within_iff_sequentially comp_def
  by metis

lemma approx_from_above_dense_linorder:
  fixes x::"'a::{dense_linorder, linorder_topology, first_countable_topology}"
  assumes "x < y"
  shows "\<exists>u. (\<forall>n. u n > x) \<and> (u \<longlonglongrightarrow> x)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where A: "\<And>i. open (A i)" "\<And>i. x \<in> A i"
                                      "\<And>F. (\<forall>n. F n \<in> A n) \<Longrightarrow> F \<longlonglongrightarrow> x"
    by (metis first_countable_topology_class.countable_basis)
  define u where "u = (\<lambda>n. SOME z. z \<in> A n \<and> z > x)"
  have "\<exists>z. z \<in> U \<and> x < z" if "x \<in> U" "open U" for U
    using open_right[OF \<open>open U\<close> \<open>x \<in> U\<close> \<open>x < y\<close>]
    by (meson atLeastLessThan_iff dense less_imp_le subset_eq)
  then have *: "u n \<in> A n \<and> x < u n" for n
    using \<open>x \<in> A n\<close> \<open>open (A n)\<close> unfolding u_def by (metis (no_types, lifting) someI_ex)
  then have "u \<longlonglongrightarrow> x" using A(3) by simp
  then show ?thesis using * by auto
qed

lemma approx_from_below_dense_linorder:
  fixes x::"'a::{dense_linorder, linorder_topology, first_countable_topology}"
  assumes "x > y"
  shows "\<exists>u. (\<forall>n. u n < x) \<and> (u \<longlonglongrightarrow> x)"
proof -
  obtain A :: "nat \<Rightarrow> 'a set" where A: "\<And>i. open (A i)" "\<And>i. x \<in> A i"
                                      "\<And>F. (\<forall>n. F n \<in> A n) \<Longrightarrow> F \<longlonglongrightarrow> x"
    by (metis first_countable_topology_class.countable_basis)
  define u where "u = (\<lambda>n. SOME z. z \<in> A n \<and> z < x)"
  have "\<exists>z. z \<in> U \<and> z < x" if "x \<in> U" "open U" for U
    using open_left[OF \<open>open U\<close> \<open>x \<in> U\<close> \<open>x > y\<close>]
    by (meson dense greaterThanAtMost_iff less_imp_le subset_eq)
  then have *: "u n \<in> A n \<and> u n < x" for n
    using \<open>x \<in> A n\<close> \<open>open (A n)\<close> unfolding u_def by (metis (no_types, lifting) someI_ex)
  then have "u \<longlonglongrightarrow> x" using A(3) by simp
  then show ?thesis using * by auto
qed


subsection \<open>Function limit at a point\<close>

abbreviation LIM :: "('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
    ("((_)/ \<midarrow>(_)/\<rightarrow> (_))" [60, 0, 60] 60)
  where "f \<midarrow>a\<rightarrow> L \<equiv> (f \<longlongrightarrow> L) (at a)"

lemma tendsto_within_open: "a \<in> S \<Longrightarrow> open S \<Longrightarrow> (f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow> (f \<midarrow>a\<rightarrow> l)"
  by (simp add: tendsto_def at_within_open[where S = S])

lemma tendsto_within_open_NO_MATCH:
  "a \<in> S \<Longrightarrow> NO_MATCH UNIV S \<Longrightarrow> open S \<Longrightarrow> (f \<longlongrightarrow> l)(at a within S) \<longleftrightarrow> (f \<longlongrightarrow> l)(at a)"
  for f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  using tendsto_within_open by blast

lemma LIM_const_not_eq[tendsto_intros]: "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) \<midarrow>a\<rightarrow> L"
  for a :: "'a::perfect_space" and k L :: "'b::t2_space"
  by (simp add: tendsto_const_iff)

lemmas LIM_not_zero = LIM_const_not_eq [where L = 0]

lemma LIM_const_eq: "(\<lambda>x. k) \<midarrow>a\<rightarrow> L \<Longrightarrow> k = L"
  for a :: "'a::perfect_space" and k L :: "'b::t2_space"
  by (simp add: tendsto_const_iff)

lemma LIM_unique: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> f \<midarrow>a\<rightarrow> M \<Longrightarrow> L = M"
  for a :: "'a::perfect_space" and L M :: "'b::t2_space"
  using at_neq_bot by (rule tendsto_unique)

lemma LIM_Uniq: "\<exists>\<^sub>\<le>\<^sub>1L::'b::t2_space. f \<midarrow>a\<rightarrow> L"
  for a :: "'a::perfect_space"
 by (auto simp add: Uniq_def LIM_unique)


text \<open>Limits are equal for functions equal except at limit point.\<close>
lemma LIM_equal: "\<forall>x. x \<noteq> a \<longrightarrow> f x = g x \<Longrightarrow> (f \<midarrow>a\<rightarrow> l) \<longleftrightarrow> (g \<midarrow>a\<rightarrow> l)"
  by (simp add: tendsto_def eventually_at_topological)

lemma LIM_cong: "a = b \<Longrightarrow> (\<And>x. x \<noteq> b \<Longrightarrow> f x = g x) \<Longrightarrow> l = m \<Longrightarrow> (f \<midarrow>a\<rightarrow> l) \<longleftrightarrow> (g \<midarrow>b\<rightarrow> m)"
  by (simp add: LIM_equal)

lemma tendsto_cong_limit: "(f \<longlongrightarrow> l) F \<Longrightarrow> k = l \<Longrightarrow> (f \<longlongrightarrow> k) F"
  by simp

lemma tendsto_at_iff_tendsto_nhds: "g \<midarrow>l\<rightarrow> g l \<longleftrightarrow> (g \<longlongrightarrow> g l) (nhds l)"
  unfolding tendsto_def eventually_at_filter
  by (intro ext all_cong imp_cong) (auto elim!: eventually_mono)

lemma tendsto_compose: "g \<midarrow>l\<rightarrow> g l \<Longrightarrow> (f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) \<longlongrightarrow> g l) F"
  unfolding tendsto_at_iff_tendsto_nhds by (rule filterlim_compose[of g])

lemma tendsto_compose_eventually:
  "g \<midarrow>l\<rightarrow> m \<Longrightarrow> (f \<longlongrightarrow> l) F \<Longrightarrow> eventually (\<lambda>x. f x \<noteq> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) \<longlongrightarrow> m) F"
  by (rule filterlim_compose[of g _ "at l"]) (auto simp add: filterlim_at)

lemma LIM_compose_eventually:
  assumes "f \<midarrow>a\<rightarrow> b"
    and "g \<midarrow>b\<rightarrow> c"
    and "eventually (\<lambda>x. f x \<noteq> b) (at a)"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c"
  using assms(2,1,3) by (rule tendsto_compose_eventually)

lemma tendsto_compose_filtermap: "((g \<circ> f) \<longlongrightarrow> T) F \<longleftrightarrow> (g \<longlongrightarrow> T) (filtermap f F)"
  by (simp add: filterlim_def filtermap_filtermap comp_def)

lemma tendsto_compose_at:
  assumes f: "(f \<longlongrightarrow> y) F" and g: "(g \<longlongrightarrow> z) (at y)" and fg: "eventually (\<lambda>w. f w = y \<longrightarrow> g y = z) F"
  shows "((g \<circ> f) \<longlongrightarrow> z) F"
proof -
  have "(\<forall>\<^sub>F a in F. f a \<noteq> y) \<or> g y = z"
    using fg by force
  moreover have "(g \<longlongrightarrow> z) (filtermap f F) \<or> \<not> (\<forall>\<^sub>F a in F. f a \<noteq> y)"
    by (metis (no_types) filterlim_atI filterlim_def tendsto_mono f g)
  ultimately show ?thesis
    by (metis (no_types) f filterlim_compose filterlim_filtermap g tendsto_at_iff_tendsto_nhds tendsto_compose_filtermap)
qed


subsubsection \<open>Relation of \<open>LIM\<close> and \<open>LIMSEQ\<close>\<close>

lemma (in first_countable_topology) sequentially_imp_eventually_within:
  "(\<forall>f. (\<forall>n. f n \<in> s \<and> f n \<noteq> a) \<and> f \<longlonglongrightarrow> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially) \<Longrightarrow>
    eventually P (at a within s)"
  unfolding at_within_def
  by (intro sequentially_imp_eventually_nhds_within) auto

lemma (in first_countable_topology) sequentially_imp_eventually_at:
  "(\<forall>f. (\<forall>n. f n \<noteq> a) \<and> f \<longlonglongrightarrow> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially) \<Longrightarrow> eventually P (at a)"
  using sequentially_imp_eventually_within [where s=UNIV] by simp

lemma LIMSEQ_SEQ_conv1:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "f \<midarrow>a\<rightarrow> l"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S \<longlonglongrightarrow> a \<longrightarrow> (\<lambda>n. f (S n)) \<longlonglongrightarrow> l"
  using tendsto_compose_eventually [OF f, where F=sequentially] by simp

lemma LIMSEQ_SEQ_conv2:
  fixes f :: "'a::first_countable_topology \<Rightarrow> 'b::topological_space"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S \<longlonglongrightarrow> a \<longrightarrow> (\<lambda>n. f (S n)) \<longlonglongrightarrow> l"
  shows "f \<midarrow>a\<rightarrow> l"
  using assms unfolding tendsto_def [where l=l] by (simp add: sequentially_imp_eventually_at)

lemma LIMSEQ_SEQ_conv: "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S \<longlonglongrightarrow> a \<longrightarrow> (\<lambda>n. X (S n)) \<longlonglongrightarrow> L) \<longleftrightarrow> X \<midarrow>a\<rightarrow> L"
  for a :: "'a::first_countable_topology" and L :: "'b::topological_space"
  using LIMSEQ_SEQ_conv2 LIMSEQ_SEQ_conv1 ..

lemma sequentially_imp_eventually_at_left:
  fixes a :: "'a::{linorder_topology,first_countable_topology}"
  assumes b[simp]: "b < a"
    and *: "\<And>f. (\<And>n. b < f n) \<Longrightarrow> (\<And>n. f n < a) \<Longrightarrow> incseq f \<Longrightarrow> f \<longlonglongrightarrow> a \<Longrightarrow>
      eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at_left a)"
proof (safe intro!: sequentially_imp_eventually_within)
  fix X
  assume X: "\<forall>n. X n \<in> {..< a} \<and> X n \<noteq> a" "X \<longlonglongrightarrow> a"
  show "eventually (\<lambda>n. P (X n)) sequentially"
  proof (rule ccontr)
    assume neg: "\<not> ?thesis"
    have "\<exists>s. \<forall>n. (\<not> P (X (s n)) \<and> b < X (s n)) \<and> (X (s n) \<le> X (s (Suc n)) \<and> Suc (s n) \<le> s (Suc n))"
      (is "\<exists>s. ?P s")
    proof (rule dependent_nat_choice)
      have "\<not> eventually (\<lambda>n. b < X n \<longrightarrow> P (X n)) sequentially"
        by (intro not_eventually_impI neg order_tendstoD(1) [OF X(2) b])
      then show "\<exists>x. \<not> P (X x) \<and> b < X x"
        by (auto dest!: not_eventuallyD)
    next
      fix x n
      have "\<not> eventually (\<lambda>n. Suc x \<le> n \<longrightarrow> b < X n \<longrightarrow> X x < X n \<longrightarrow> P (X n)) sequentially"
        using X
        by (intro not_eventually_impI order_tendstoD(1)[OF X(2)] eventually_ge_at_top neg) auto
      then show "\<exists>n. (\<not> P (X n) \<and> b < X n) \<and> (X x \<le> X n \<and> Suc x \<le> n)"
        by (auto dest!: not_eventuallyD)
    qed
    then obtain s where "?P s" ..
    with X have "b < X (s n)"
      and "X (s n) < a"
      and "incseq (\<lambda>n. X (s n))"
      and "(\<lambda>n. X (s n)) \<longlonglongrightarrow> a"
      and "\<not> P (X (s n))"
      for n
      by (auto simp: strict_mono_Suc_iff Suc_le_eq incseq_Suc_iff
          intro!: LIMSEQ_subseq_LIMSEQ[OF \<open>X \<longlonglongrightarrow> a\<close>, unfolded comp_def])
    from *[OF this(1,2,3,4)] this(5) show False
      by auto
  qed
qed

lemma tendsto_at_left_sequentially:
  fixes a b :: "'b::{linorder_topology,first_countable_topology}"
  assumes "b < a"
  assumes *: "\<And>S. (\<And>n. S n < a) \<Longrightarrow> (\<And>n. b < S n) \<Longrightarrow> incseq S \<Longrightarrow> S \<longlonglongrightarrow> a \<Longrightarrow>
    (\<lambda>n. X (S n)) \<longlonglongrightarrow> L"
  shows "(X \<longlongrightarrow> L) (at_left a)"
  using assms by (simp add: tendsto_def [where l=L] sequentially_imp_eventually_at_left)

lemma sequentially_imp_eventually_at_right:
  fixes a b :: "'a::{linorder_topology,first_countable_topology}"
  assumes b[simp]: "a < b"
  assumes *: "\<And>f. (\<And>n. a < f n) \<Longrightarrow> (\<And>n. f n < b) \<Longrightarrow> decseq f \<Longrightarrow> f \<longlonglongrightarrow> a \<Longrightarrow>
    eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at_right a)"
proof (safe intro!: sequentially_imp_eventually_within)
  fix X
  assume X: "\<forall>n. X n \<in> {a <..} \<and> X n \<noteq> a" "X \<longlonglongrightarrow> a"
  show "eventually (\<lambda>n. P (X n)) sequentially"
  proof (rule ccontr)
    assume neg: "\<not> ?thesis"
    have "\<exists>s. \<forall>n. (\<not> P (X (s n)) \<and> X (s n) < b) \<and> (X (s (Suc n)) \<le> X (s n) \<and> Suc (s n) \<le> s (Suc n))"
      (is "\<exists>s. ?P s")
    proof (rule dependent_nat_choice)
      have "\<not> eventually (\<lambda>n. X n < b \<longrightarrow> P (X n)) sequentially"
        by (intro not_eventually_impI neg order_tendstoD(2) [OF X(2) b])
      then show "\<exists>x. \<not> P (X x) \<and> X x < b"
        by (auto dest!: not_eventuallyD)
    next
      fix x n
      have "\<not> eventually (\<lambda>n. Suc x \<le> n \<longrightarrow> X n < b \<longrightarrow> X n < X x \<longrightarrow> P (X n)) sequentially"
        using X
        by (intro not_eventually_impI order_tendstoD(2)[OF X(2)] eventually_ge_at_top neg) auto
      then show "\<exists>n. (\<not> P (X n) \<and> X n < b) \<and> (X n \<le> X x \<and> Suc x \<le> n)"
        by (auto dest!: not_eventuallyD)
    qed
    then obtain s where "?P s" ..
    with X have "a < X (s n)"
      and "X (s n) < b"
      and "decseq (\<lambda>n. X (s n))"
      and "(\<lambda>n. X (s n)) \<longlonglongrightarrow> a"
      and "\<not> P (X (s n))"
      for n
      by (auto simp: strict_mono_Suc_iff Suc_le_eq decseq_Suc_iff
          intro!: LIMSEQ_subseq_LIMSEQ[OF \<open>X \<longlonglongrightarrow> a\<close>, unfolded comp_def])
    from *[OF this(1,2,3,4)] this(5) show False
      by auto
  qed
qed

lemma tendsto_at_right_sequentially:
  fixes a :: "_ :: {linorder_topology, first_countable_topology}"
  assumes "a < b"
    and *: "\<And>S. (\<And>n. a < S n) \<Longrightarrow> (\<And>n. S n < b) \<Longrightarrow> decseq S \<Longrightarrow> S \<longlonglongrightarrow> a \<Longrightarrow>
      (\<lambda>n. X (S n)) \<longlonglongrightarrow> L"
  shows "(X \<longlongrightarrow> L) (at_right a)"
  using assms by (simp add: tendsto_def [where l=L] sequentially_imp_eventually_at_right)


subsection \<open>Continuity\<close>

subsubsection \<open>Continuity on a set\<close>

definition continuous_on :: "'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
  where "continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. (f \<longlongrightarrow> f x) (at x within s))"

lemma continuous_on_cong [cong]:
  "s = t \<Longrightarrow> (\<And>x. x \<in> t \<Longrightarrow> f x = g x) \<Longrightarrow> continuous_on s f \<longleftrightarrow> continuous_on t g"
  unfolding continuous_on_def
  by (intro ball_cong filterlim_cong) (auto simp: eventually_at_filter)

lemma continuous_on_cong_simp:
  "s = t \<Longrightarrow> (\<And>x. x \<in> t =simp=> f x = g x) \<Longrightarrow> continuous_on s f \<longleftrightarrow> continuous_on t g"
  unfolding simp_implies_def by (rule continuous_on_cong)

lemma continuous_on_topological:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>B. open B \<longrightarrow> f x \<in> B \<longrightarrow> (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)))"
  unfolding continuous_on_def tendsto_def eventually_at_topological by metis

lemma continuous_on_open_invariant:
  "continuous_on s f \<longleftrightarrow> (\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> s = f -` B \<inter> s))"
proof safe
  fix B :: "'b set"
  assume "continuous_on s f" "open B"
  then have "\<forall>x\<in>f -` B \<inter> s. (\<exists>A. open A \<and> x \<in> A \<and> s \<inter> A \<subseteq> f -` B)"
    by (auto simp: continuous_on_topological subset_eq Ball_def imp_conjL)
  then obtain A where "\<forall>x\<in>f -` B \<inter> s. open (A x) \<and> x \<in> A x \<and> s \<inter> A x \<subseteq> f -` B"
    unfolding bchoice_iff ..
  then show "\<exists>A. open A \<and> A \<inter> s = f -` B \<inter> s"
    by (intro exI[of _ "\<Union>x\<in>f -` B \<inter> s. A x"]) auto
next
  assume B: "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> s = f -` B \<inter> s)"
  show "continuous_on s f"
    unfolding continuous_on_topological
  proof safe
    fix x B
    assume "x \<in> s" "open B" "f x \<in> B"
    with B obtain A where A: "open A" "A \<inter> s = f -` B \<inter> s"
      by auto
    with \<open>x \<in> s\<close> \<open>f x \<in> B\<close> show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)"
      by (intro exI[of _ A]) auto
  qed
qed

lemma continuous_on_open_vimage:
  "open s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>B. open B \<longrightarrow> open (f -` B \<inter> s))"
  unfolding continuous_on_open_invariant
  by (metis open_Int Int_absorb Int_commute[of s] Int_assoc[of _ _ s])

corollary continuous_imp_open_vimage:
  assumes "continuous_on s f" "open s" "open B" "f -` B \<subseteq> s"
  shows "open (f -` B)"
  by (metis assms continuous_on_open_vimage le_iff_inf)

corollary open_vimage[continuous_intros]:
  assumes "open s"
    and "continuous_on UNIV f"
  shows "open (f -` s)"
  using assms by (simp add: continuous_on_open_vimage [OF open_UNIV])

lemma continuous_on_closed_invariant:
  "continuous_on s f \<longleftrightarrow> (\<forall>B. closed B \<longrightarrow> (\<exists>A. closed A \<and> A \<inter> s = f -` B \<inter> s))"
proof -
  have *: "(\<And>A. P A \<longleftrightarrow> Q (- A)) \<Longrightarrow> (\<forall>A. P A) \<longleftrightarrow> (\<forall>A. Q A)"
    for P Q :: "'b set \<Rightarrow> bool"
    by (metis double_compl)
  show ?thesis
    unfolding continuous_on_open_invariant
    by (intro *) (auto simp: open_closed[symmetric])
qed

lemma continuous_on_closed_vimage:
  "closed s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>B. closed B \<longrightarrow> closed (f -` B \<inter> s))"
  unfolding continuous_on_closed_invariant
  by (metis closed_Int Int_absorb Int_commute[of s] Int_assoc[of _ _ s])

corollary closed_vimage_Int[continuous_intros]:
  assumes "closed s"
    and "continuous_on t f"
    and t: "closed t"
  shows "closed (f -` s \<inter> t)"
  using assms by (simp add: continuous_on_closed_vimage [OF t])

corollary closed_vimage[continuous_intros]:
  assumes "closed s"
    and "continuous_on UNIV f"
  shows "closed (f -` s)"
  using closed_vimage_Int [OF assms] by simp

lemma continuous_on_empty [simp]: "continuous_on {} f"
  by (simp add: continuous_on_def)

lemma continuous_on_sing [simp]: "continuous_on {x} f"
  by (simp add: continuous_on_def at_within_def)

lemma continuous_on_open_Union:
  "(\<And>s. s \<in> S \<Longrightarrow> open s) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> continuous_on s f) \<Longrightarrow> continuous_on (\<Union>S) f"
  unfolding continuous_on_def
  by safe (metis open_Union at_within_open UnionI)

lemma continuous_on_open_UN:
  "(\<And>s. s \<in> S \<Longrightarrow> open (A s)) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> continuous_on (A s) f) \<Longrightarrow>
    continuous_on (\<Union>s\<in>S. A s) f"
  by (rule continuous_on_open_Union) auto

lemma continuous_on_open_Un:
  "open s \<Longrightarrow> open t \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on t f \<Longrightarrow> continuous_on (s \<union> t) f"
  using continuous_on_open_Union [of "{s,t}"] by auto

lemma continuous_on_closed_Un:
  "closed s \<Longrightarrow> closed t \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on t f \<Longrightarrow> continuous_on (s \<union> t) f"
  by (auto simp add: continuous_on_closed_vimage closed_Un Int_Un_distrib)

lemma continuous_on_closed_Union:
  assumes "finite I"
    "\<And>i. i \<in> I \<Longrightarrow> closed (U i)"
    "\<And>i. i \<in> I \<Longrightarrow> continuous_on (U i) f"
  shows "continuous_on (\<Union> i \<in> I. U i) f"
  using assms
  by (induction I) (auto intro!: continuous_on_closed_Un)

lemma continuous_on_If:
  assumes closed: "closed s" "closed t"
    and cont: "continuous_on s f" "continuous_on t g"
    and P: "\<And>x. x \<in> s \<Longrightarrow> \<not> P x \<Longrightarrow> f x = g x" "\<And>x. x \<in> t \<Longrightarrow> P x \<Longrightarrow> f x = g x"
  shows "continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
    (is "continuous_on _ ?h")
proof-
  from P have "\<forall>x\<in>s. f x = ?h x" "\<forall>x\<in>t. g x = ?h x"
    by auto
  with cont have "continuous_on s ?h" "continuous_on t ?h"
    by simp_all
  with closed show ?thesis
    by (rule continuous_on_closed_Un)
qed

lemma continuous_on_cases:
  "closed s \<Longrightarrow> closed t \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on t g \<Longrightarrow>
    \<forall>x. (x\<in>s \<and> \<not> P x) \<or> (x \<in> t \<and> P x) \<longrightarrow> f x = g x \<Longrightarrow>
    continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
  by (rule continuous_on_If) auto

lemma continuous_on_id[continuous_intros,simp]: "continuous_on s (\<lambda>x. x)"
  unfolding continuous_on_def by fast

lemma continuous_on_id'[continuous_intros,simp]: "continuous_on s id"
  unfolding continuous_on_def id_def by fast

lemma continuous_on_const[continuous_intros,simp]: "continuous_on s (\<lambda>x. c)"
  unfolding continuous_on_def by auto

lemma continuous_on_subset: "continuous_on s f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> continuous_on t f"
  unfolding continuous_on_def
  by (metis subset_eq tendsto_within_subset)

lemma continuous_on_compose[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on (f ` s) g \<Longrightarrow> continuous_on s (g \<circ> f)"
  unfolding continuous_on_topological by simp metis

lemma continuous_on_compose2:
  "continuous_on t g \<Longrightarrow> continuous_on s f \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> continuous_on s (\<lambda>x. g (f x))"
  using continuous_on_compose[of s f g] continuous_on_subset by (force simp add: comp_def)

lemma continuous_on_generate_topology:
  assumes *: "open = generate_topology X"
    and **: "\<And>B. B \<in> X \<Longrightarrow> \<exists>C. open C \<and> C \<inter> A = f -` B \<inter> A"
  shows "continuous_on A f"
  unfolding continuous_on_open_invariant
proof safe
  fix B :: "'a set"
  assume "open B"
  then show "\<exists>C. open C \<and> C \<inter> A = f -` B \<inter> A"
    unfolding *
  proof induct
    case (UN K)
    then obtain C where "\<And>k. k \<in> K \<Longrightarrow> open (C k)" "\<And>k. k \<in> K \<Longrightarrow> C k \<inter> A = f -` k \<inter> A"
      by metis
    then show ?case
      by (intro exI[of _ "\<Union>k\<in>K. C k"]) blast
  qed (auto intro: **)
qed

lemma continuous_onI_mono:
  fixes f :: "'a::linorder_topology \<Rightarrow> 'b::{dense_order,linorder_topology}"
  assumes "open (f`A)"
    and mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "continuous_on A f"
proof (rule continuous_on_generate_topology[OF open_generated_order], safe)
  have monoD: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x < f y \<Longrightarrow> x < y"
    by (auto simp: not_le[symmetric] mono)
  have "\<exists>x. x \<in> A \<and> f x < b \<and> a < x" if a: "a \<in> A" and fa: "f a < b" for a b
  proof -
    obtain y where "f a < y" "{f a ..< y} \<subseteq> f`A"
      using open_right[OF \<open>open (f`A)\<close>, of "f a" b] a fa
      by auto
    obtain z where z: "f a < z" "z < min b y"
      using dense[of "f a" "min b y"] \<open>f a < y\<close> \<open>f a < b\<close> by auto
    then obtain c where "z = f c" "c \<in> A"
      using \<open>{f a ..< y} \<subseteq> f`A\<close>[THEN subsetD, of z] by (auto simp: less_imp_le)
    with a z show ?thesis
      by (auto intro!: exI[of _ c] simp: monoD)
  qed
  then show "\<exists>C. open C \<and> C \<inter> A = f -` {..<b} \<inter> A" for b
    by (intro exI[of _ "(\<Union>x\<in>{x\<in>A. f x < b}. {..< x})"])
       (auto intro: le_less_trans[OF mono] less_imp_le)

  have "\<exists>x. x \<in> A \<and> b < f x \<and> x < a" if a: "a \<in> A" and fa: "b < f a" for a b
  proof -
    note a fa
    moreover
    obtain y where "y < f a" "{y <.. f a} \<subseteq> f`A"
      using open_left[OF \<open>open (f`A)\<close>, of "f a" b]  a fa
      by auto
    then obtain z where z: "max b y < z" "z < f a"
      using dense[of "max b y" "f a"] \<open>y < f a\<close> \<open>b < f a\<close> by auto
    then obtain c where "z = f c" "c \<in> A"
      using \<open>{y <.. f a} \<subseteq> f`A\<close>[THEN subsetD, of z] by (auto simp: less_imp_le)
    with a z show ?thesis
      by (auto intro!: exI[of _ c] simp: monoD)
  qed
  then show "\<exists>C. open C \<and> C \<inter> A = f -` {b <..} \<inter> A" for b
    by (intro exI[of _ "(\<Union>x\<in>{x\<in>A. b < f x}. {x <..})"])
       (auto intro: less_le_trans[OF _ mono] less_imp_le)
qed

lemma continuous_on_IccI:
  "\<lbrakk>(f \<longlongrightarrow> f a) (at_right a);
    (f \<longlongrightarrow> f b) (at_left b);
    (\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> f \<midarrow>x\<rightarrow> f x); a < b\<rbrakk> \<Longrightarrow>
    continuous_on {a .. b} f"
  for a::"'a::linorder_topology"
  using at_within_open[of _ "{a<..<b}"]
  by (auto simp: continuous_on_def at_within_Icc_at_right at_within_Icc_at_left le_less
      at_within_Icc_at)

lemma
  fixes a b::"'a::linorder_topology"
  assumes "continuous_on {a .. b} f" "a < b"
  shows continuous_on_Icc_at_rightD: "(f \<longlongrightarrow> f a) (at_right a)"
    and continuous_on_Icc_at_leftD: "(f \<longlongrightarrow> f b) (at_left b)"
  using assms
  by (auto simp: at_within_Icc_at_right at_within_Icc_at_left continuous_on_def
      dest: bspec[where x=a] bspec[where x=b])

lemma continuous_on_discrete [simp]:
  "continuous_on A (f :: 'a :: discrete_topology \<Rightarrow> _)"
  by (auto simp: continuous_on_def at_discrete)

subsubsection \<open>Continuity at a point\<close>

definition continuous :: "'a::t2_space filter \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
  where "continuous F f \<longleftrightarrow> (f \<longlongrightarrow> f (Lim F (\<lambda>x. x))) F"

lemma continuous_bot[continuous_intros, simp]: "continuous bot f"
  unfolding continuous_def by auto

lemma continuous_trivial_limit: "trivial_limit net \<Longrightarrow> continuous net f"
  by simp

lemma continuous_within: "continuous (at x within s) f \<longleftrightarrow> (f \<longlongrightarrow> f x) (at x within s)"
  by (cases "trivial_limit (at x within s)") (auto simp add: Lim_ident_at continuous_def)

lemma continuous_within_topological:
  "continuous (at x within s) f \<longleftrightarrow>
    (\<forall>B. open B \<longrightarrow> f x \<in> B \<longrightarrow> (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)))"
  unfolding continuous_within tendsto_def eventually_at_topological by metis

lemma continuous_within_compose[continuous_intros]:
  "continuous (at x within s) f \<Longrightarrow> continuous (at (f x) within f ` s) g \<Longrightarrow>
    continuous (at x within s) (g \<circ> f)"
  by (simp add: continuous_within_topological) metis

lemma continuous_within_compose2:
  "continuous (at x within s) f \<Longrightarrow> continuous (at (f x) within f ` s) g \<Longrightarrow>
    continuous (at x within s) (\<lambda>x. g (f x))"
  using continuous_within_compose[of x s f g] by (simp add: comp_def)

lemma continuous_at: "continuous (at x) f \<longleftrightarrow> f \<midarrow>x\<rightarrow> f x"
  using continuous_within[of x UNIV f] by simp

lemma continuous_ident[continuous_intros, simp]: "continuous (at x within S) (\<lambda>x. x)"
  unfolding continuous_within by (rule tendsto_ident_at)

lemma continuous_id[continuous_intros, simp]: "continuous (at x within S) id"
  by (simp add: id_def)

lemma continuous_const[continuous_intros, simp]: "continuous F (\<lambda>x. c)"
  unfolding continuous_def by (rule tendsto_const)

lemma continuous_on_eq_continuous_within:
  "continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. continuous (at x within s) f)"
  unfolding continuous_on_def continuous_within ..

lemma continuous_discrete [simp]:
  "continuous (at x within A) (f :: 'a :: discrete_topology \<Rightarrow> _)"
  by (auto simp: continuous_def at_discrete)

abbreviation isCont :: "('a::t2_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> bool"
  where "isCont f a \<equiv> continuous (at a) f"

lemma isCont_def: "isCont f a \<longleftrightarrow> f \<midarrow>a\<rightarrow> f a"
  by (rule continuous_at)

lemma isContD: "isCont f x \<Longrightarrow> f \<midarrow>x\<rightarrow> f x"
  by (simp add: isCont_def)

lemma isCont_cong:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)"
  shows "isCont f x \<longleftrightarrow> isCont g x"
proof -
  from assms have [simp]: "f x = g x"
    by (rule eventually_nhds_x_imp_x)
  from assms have "eventually (\<lambda>x. f x = g x) (at x)"
    by (auto simp: eventually_at_filter elim!: eventually_mono)
  with assms have "isCont f x \<longleftrightarrow> isCont g x" unfolding isCont_def
    by (intro filterlim_cong) (auto elim!: eventually_mono)
  with assms show ?thesis by simp
qed

lemma continuous_at_imp_continuous_at_within: "isCont f x \<Longrightarrow> continuous (at x within s) f"
  by (auto intro: tendsto_mono at_le simp: continuous_at continuous_within)

lemma continuous_on_eq_continuous_at: "open s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. isCont f x)"
  by (simp add: continuous_on_def continuous_at at_within_open[of _ s])

lemma continuous_within_open: "a \<in> A \<Longrightarrow> open A \<Longrightarrow> continuous (at a within A) f \<longleftrightarrow> isCont f a"
  by (simp add: at_within_open_NO_MATCH)

lemma continuous_at_imp_continuous_on: "\<forall>x\<in>s. isCont f x \<Longrightarrow> continuous_on s f"
  by (auto intro: continuous_at_imp_continuous_at_within simp: continuous_on_eq_continuous_within)

lemma isCont_o2: "isCont f a \<Longrightarrow> isCont g (f a) \<Longrightarrow> isCont (\<lambda>x. g (f x)) a"
  unfolding isCont_def by (rule tendsto_compose)

lemma continuous_at_compose[continuous_intros]: "isCont f a \<Longrightarrow> isCont g (f a) \<Longrightarrow> isCont (g \<circ> f) a"
  unfolding o_def by (rule isCont_o2)

lemma isCont_tendsto_compose: "isCont g l \<Longrightarrow> (f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) \<longlongrightarrow> g l) F"
  unfolding isCont_def by (rule tendsto_compose)

lemma continuous_on_tendsto_compose:
  assumes f_cont: "continuous_on s f"
    and g: "(g \<longlongrightarrow> l) F"
    and l: "l \<in> s"
    and ev: "\<forall>\<^sub>Fx in F. g x \<in> s"
  shows "((\<lambda>x. f (g x)) \<longlongrightarrow> f l) F"
proof -
  from f_cont l have f: "(f \<longlongrightarrow> f l) (at l within s)"
    by (simp add: continuous_on_def)
  have i: "((\<lambda>x. if g x = l then f l else f (g x)) \<longlongrightarrow> f l) F"
    by (rule filterlim_If)
       (auto intro!: filterlim_compose[OF f] eventually_conj tendsto_mono[OF _ g]
             simp: filterlim_at eventually_inf_principal eventually_mono[OF ev])
  show ?thesis
    by (rule filterlim_cong[THEN iffD1[OF _ i]]) auto
qed

lemma continuous_within_compose3:
  "isCont g (f x) \<Longrightarrow> continuous (at x within s) f \<Longrightarrow> continuous (at x within s) (\<lambda>x. g (f x))"
  using continuous_at_imp_continuous_at_within continuous_within_compose2 by blast

lemma filtermap_nhds_open_map:
  assumes cont: "isCont f a"
    and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (nhds a) = nhds (f a)"
  unfolding filter_eq_iff
proof safe
  fix P
  assume "eventually P (filtermap f (nhds a))"
  then obtain S where "open S" "a \<in> S" "\<forall>x\<in>S. P (f x)"
    by (auto simp: eventually_filtermap eventually_nhds)
  then show "eventually P (nhds (f a))"
    unfolding eventually_nhds by (intro exI[of _ "f`S"]) (auto intro!: open_map)
qed (metis filterlim_iff tendsto_at_iff_tendsto_nhds isCont_def eventually_filtermap cont)

lemma continuous_at_split:
  "continuous (at x) f \<longleftrightarrow> continuous (at_left x) f \<and> continuous (at_right x) f"
  for x :: "'a::linorder_topology"
  by (simp add: continuous_within filterlim_at_split)

lemma continuous_on_max [continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. max (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_max)

lemma continuous_on_min [continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. min (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_min)

lemma continuous_max [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::linorder_topology"
  shows "\<lbrakk>continuous F f; continuous F g\<rbrakk> \<Longrightarrow> continuous F (\<lambda>x. (max (f x) (g x)))"
  by (simp add: tendsto_max continuous_def)

lemma continuous_min [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::linorder_topology"
  shows "\<lbrakk>continuous F f; continuous F g\<rbrakk> \<Longrightarrow> continuous F (\<lambda>x. (min (f x) (g x)))"
  by (simp add: tendsto_min continuous_def)

text \<open>
  The following open/closed Collect lemmas are ported from
  Sébastien Gouëzel's \<open>Ergodic_Theory\<close>.
\<close>
lemma open_Collect_neq:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes f: "continuous_on UNIV f" and g: "continuous_on UNIV g"
  shows "open {x. f x \<noteq> g x}"
proof (rule openI)
  fix t
  assume "t \<in> {x. f x \<noteq> g x}"
  then obtain U V where *: "open U" "open V" "f t \<in> U" "g t \<in> V" "U \<inter> V = {}"
    by (auto simp add: separation_t2)
  with open_vimage[OF \<open>open U\<close> f] open_vimage[OF \<open>open V\<close> g]
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {x. f x \<noteq> g x}"
    by (intro exI[of _ "f -` U \<inter> g -` V"]) auto
qed

lemma closed_Collect_eq:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes f: "continuous_on UNIV f" and g: "continuous_on UNIV g"
  shows "closed {x. f x = g x}"
  using open_Collect_neq[OF f g] by (simp add: closed_def Collect_neg_eq)

lemma open_Collect_less:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  assumes f: "continuous_on UNIV f" and g: "continuous_on UNIV g"
  shows "open {x. f x < g x}"
proof (rule openI)
  fix t
  assume t: "t \<in> {x. f x < g x}"
  show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {x. f x < g x}"
  proof (cases "\<exists>z. f t < z \<and> z < g t")
    case True
    then obtain z where "f t < z \<and> z < g t" by blast
    then show ?thesis
      using open_vimage[OF _ f, of "{..< z}"] open_vimage[OF _ g, of "{z <..}"]
      by (intro exI[of _ "f -` {..<z} \<inter> g -` {z<..}"]) auto
  next
    case False
    then have *: "{g t ..} = {f t <..}" "{..< g t} = {.. f t}"
      using t by (auto intro: leI)
    show ?thesis
      using open_vimage[OF _ f, of "{..< g t}"] open_vimage[OF _ g, of "{f t <..}"] t
      apply (intro exI[of _ "f -` {..< g t} \<inter> g -` {f t<..}"])
      apply (simp add: open_Int)
      apply (auto simp add: *)
      done
  qed
qed

lemma closed_Collect_le:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b::linorder_topology"
  assumes f: "continuous_on UNIV f"
    and g: "continuous_on UNIV g"
  shows "closed {x. f x \<le> g x}"
  using open_Collect_less [OF g f]
  by (simp add: closed_def Collect_neg_eq[symmetric] not_le)


subsubsection \<open>Open-cover compactness\<close>

context topological_space
begin

definition compact :: "'a set \<Rightarrow> bool" where
compact_eq_Heine_Borel:  (* This name is used for backwards compatibility *)
    "compact S \<longleftrightarrow> (\<forall>C. (\<forall>c\<in>C. open c) \<and> S \<subseteq> \<Union>C \<longrightarrow> (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"

lemma compactI:
  assumes "\<And>C. \<forall>t\<in>C. open t \<Longrightarrow> s \<subseteq> \<Union>C \<Longrightarrow> \<exists>C'. C' \<subseteq> C \<and> finite C' \<and> s \<subseteq> \<Union>C'"
  shows "compact s"
  unfolding compact_eq_Heine_Borel using assms by metis

lemma compact_empty[simp]: "compact {}"
  by (auto intro!: compactI)

lemma compactE: (*related to COMPACT_IMP_HEINE_BOREL in HOL Light*)
  assumes "compact S" "S \<subseteq> \<Union>\<T>" "\<And>B. B \<in> \<T> \<Longrightarrow> open B"
  obtains \<T>' where "\<T>' \<subseteq> \<T>" "finite \<T>'" "S \<subseteq> \<Union>\<T>'"
  by (meson assms compact_eq_Heine_Borel)

lemma compactE_image:
  assumes "compact S"
    and opn: "\<And>T. T \<in> C \<Longrightarrow> open (f T)"
    and S: "S \<subseteq> (\<Union>c\<in>C. f c)"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "S \<subseteq> (\<Union>c\<in>C'. f c)"
    apply (rule compactE[OF \<open>compact S\<close> S])
    using opn apply force
    by (metis finite_subset_image)

lemma compact_Int_closed [intro]:
  assumes "compact S"
    and "closed T"
  shows "compact (S \<inter> T)"
proof (rule compactI)
  fix C
  assume C: "\<forall>c\<in>C. open c"
  assume cover: "S \<inter> T \<subseteq> \<Union>C"
  from C \<open>closed T\<close> have "\<forall>c\<in>C \<union> {- T}. open c"
    by auto
  moreover from cover have "S \<subseteq> \<Union>(C \<union> {- T})"
    by auto
  ultimately have "\<exists>D\<subseteq>C \<union> {- T}. finite D \<and> S \<subseteq> \<Union>D"
    using \<open>compact S\<close> unfolding compact_eq_Heine_Borel by auto
  then obtain D where "D \<subseteq> C \<union> {- T} \<and> finite D \<and> S \<subseteq> \<Union>D" ..
  then show "\<exists>D\<subseteq>C. finite D \<and> S \<inter> T \<subseteq> \<Union>D"
    by (intro exI[of _ "D - {-T}"]) auto
qed

lemma compact_diff: "\<lbrakk>compact S; open T\<rbrakk> \<Longrightarrow> compact(S - T)"
  by (simp add: Diff_eq compact_Int_closed open_closed)

lemma inj_setminus: "inj_on uminus (A::'a set set)"
  by (auto simp: inj_on_def)


subsection \<open>Finite intersection property\<close>

lemma compact_fip:
  "compact U \<longleftrightarrow>
    (\<forall>A. (\<forall>a\<in>A. closed a) \<longrightarrow> (\<forall>B \<subseteq> A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}) \<longrightarrow> U \<inter> \<Inter>A \<noteq> {})"
  (is "_ \<longleftrightarrow> ?R")
proof (safe intro!: compact_eq_Heine_Borel[THEN iffD2])
  fix A
  assume "compact U"
  assume A: "\<forall>a\<in>A. closed a" "U \<inter> \<Inter>A = {}"
  assume fin: "\<forall>B \<subseteq> A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}"
  from A have "(\<forall>a\<in>uminus`A. open a) \<and> U \<subseteq> \<Union>(uminus`A)"
    by auto
  with \<open>compact U\<close> obtain B where "B \<subseteq> A" "finite (uminus`B)" "U \<subseteq> \<Union>(uminus`B)"
    unfolding compact_eq_Heine_Borel by (metis subset_image_iff)
  with fin[THEN spec, of B] show False
    by (auto dest: finite_imageD intro: inj_setminus)
next
  fix A
  assume ?R
  assume "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A"
  then have "U \<inter> \<Inter>(uminus`A) = {}" "\<forall>a\<in>uminus`A. closed a"
    by auto
  with \<open>?R\<close> obtain B where "B \<subseteq> A" "finite (uminus`B)" "U \<inter> \<Inter>(uminus`B) = {}"
    by (metis subset_image_iff)
  then show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
    by (auto intro!: exI[of _ B] inj_setminus dest: finite_imageD)
qed

lemma compact_imp_fip:
  assumes "compact S"
    and "\<And>T. T \<in> F \<Longrightarrow> closed T"
    and "\<And>F'. finite F' \<Longrightarrow> F' \<subseteq> F \<Longrightarrow> S \<inter> (\<Inter>F') \<noteq> {}"
  shows "S \<inter> (\<Inter>F) \<noteq> {}"
  using assms unfolding compact_fip by auto

lemma compact_imp_fip_image:
  assumes "compact s"
    and P: "\<And>i. i \<in> I \<Longrightarrow> closed (f i)"
    and Q: "\<And>I'. finite I' \<Longrightarrow> I' \<subseteq> I \<Longrightarrow> (s \<inter> (\<Inter>i\<in>I'. f i) \<noteq> {})"
  shows "s \<inter> (\<Inter>i\<in>I. f i) \<noteq> {}"
proof -
  note \<open>compact s\<close>
  moreover from P have "\<forall>i \<in> f ` I. closed i"
    by blast
  moreover have "\<forall>A. finite A \<and> A \<subseteq> f ` I \<longrightarrow> (s \<inter> (\<Inter>A) \<noteq> {})"
    apply rule
    apply rule
    apply (erule conjE)
  proof -
    fix A :: "'a set set"
    assume "finite A" and "A \<subseteq> f ` I"
    then obtain B where "B \<subseteq> I" and "finite B" and "A = f ` B"
      using finite_subset_image [of A f I] by blast
    with Q [of B] show "s \<inter> \<Inter>A \<noteq> {}"
      by simp
  qed
  ultimately have "s \<inter> (\<Inter>(f ` I)) \<noteq> {}"
    by (metis compact_imp_fip)
  then show ?thesis by simp
qed

end

lemma (in t2_space) compact_imp_closed:
  assumes "compact s"
  shows "closed s"
  unfolding closed_def
proof (rule openI)
  fix y
  assume "y \<in> - s"
  let ?C = "\<Union>x\<in>s. {u. open u \<and> x \<in> u \<and> eventually (\<lambda>y. y \<notin> u) (nhds y)}"
  have "s \<subseteq> \<Union>?C"
  proof
    fix x
    assume "x \<in> s"
    with \<open>y \<in> - s\<close> have "x \<noteq> y" by clarsimp
    then have "\<exists>u v. open u \<and> open v \<and> x \<in> u \<and> y \<in> v \<and> u \<inter> v = {}"
      by (rule hausdorff)
    with \<open>x \<in> s\<close> show "x \<in> \<Union>?C"
      unfolding eventually_nhds by auto
  qed
  then obtain D where "D \<subseteq> ?C" and "finite D" and "s \<subseteq> \<Union>D"
    by (rule compactE [OF \<open>compact s\<close>]) auto
  from \<open>D \<subseteq> ?C\<close> have "\<forall>x\<in>D. eventually (\<lambda>y. y \<notin> x) (nhds y)"
    by auto
  with \<open>finite D\<close> have "eventually (\<lambda>y. y \<notin> \<Union>D) (nhds y)"
    by (simp add: eventually_ball_finite)
  with \<open>s \<subseteq> \<Union>D\<close> have "eventually (\<lambda>y. y \<notin> s) (nhds y)"
    by (auto elim!: eventually_mono)
  then show "\<exists>t. open t \<and> y \<in> t \<and> t \<subseteq> - s"
    by (simp add: eventually_nhds subset_eq)
qed

lemma compact_continuous_image:
  assumes f: "continuous_on s f"
    and s: "compact s"
  shows "compact (f ` s)"
proof (rule compactI)
  fix C
  assume "\<forall>c\<in>C. open c" and cover: "f`s \<subseteq> \<Union>C"
  with f have "\<forall>c\<in>C. \<exists>A. open A \<and> A \<inter> s = f -` c \<inter> s"
    unfolding continuous_on_open_invariant by blast
  then obtain A where A: "\<forall>c\<in>C. open (A c) \<and> A c \<inter> s = f -` c \<inter> s"
    unfolding bchoice_iff ..
  with cover have "\<And>c. c \<in> C \<Longrightarrow> open (A c)" "s \<subseteq> (\<Union>c\<in>C. A c)"
    by (fastforce simp add: subset_eq set_eq_iff)+
  from compactE_image[OF s this] obtain D where "D \<subseteq> C" "finite D" "s \<subseteq> (\<Union>c\<in>D. A c)" .
  with A show "\<exists>D \<subseteq> C. finite D \<and> f`s \<subseteq> \<Union>D"
    by (intro exI[of _ D]) (fastforce simp add: subset_eq set_eq_iff)+
qed

lemma continuous_on_inv:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "continuous_on s f"
    and "compact s"
    and "\<forall>x\<in>s. g (f x) = x"
  shows "continuous_on (f ` s) g"
  unfolding continuous_on_topological
proof (clarsimp simp add: assms(3))
  fix x :: 'a and B :: "'a set"
  assume "x \<in> s" and "open B" and "x \<in> B"
  have 1: "\<forall>x\<in>s. f x \<in> f ` (s - B) \<longleftrightarrow> x \<in> s - B"
    using assms(3) by (auto, metis)
  have "continuous_on (s - B) f"
    using \<open>continuous_on s f\<close> Diff_subset
    by (rule continuous_on_subset)
  moreover have "compact (s - B)"
    using \<open>open B\<close> and \<open>compact s\<close>
    unfolding Diff_eq by (intro compact_Int_closed closed_Compl)
  ultimately have "compact (f ` (s - B))"
    by (rule compact_continuous_image)
  then have "closed (f ` (s - B))"
    by (rule compact_imp_closed)
  then have "open (- f ` (s - B))"
    by (rule open_Compl)
  moreover have "f x \<in> - f ` (s - B)"
    using \<open>x \<in> s\<close> and \<open>x \<in> B\<close> by (simp add: 1)
  moreover have "\<forall>y\<in>s. f y \<in> - f ` (s - B) \<longrightarrow> y \<in> B"
    by (simp add: 1)
  ultimately show "\<exists>A. open A \<and> f x \<in> A \<and> (\<forall>y\<in>s. f y \<in> A \<longrightarrow> y \<in> B)"
    by fast
qed

lemma continuous_on_inv_into:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes s: "continuous_on s f" "compact s"
    and f: "inj_on f s"
  shows "continuous_on (f ` s) (the_inv_into s f)"
  by (rule continuous_on_inv[OF s]) (auto simp: the_inv_into_f_f[OF f])

lemma (in linorder_topology) compact_attains_sup:
  assumes "compact S" "S \<noteq> {}"
  shows "\<exists>s\<in>S. \<forall>t\<in>S. t \<le> s"
proof (rule classical)
  assume "\<not> (\<exists>s\<in>S. \<forall>t\<in>S. t \<le> s)"
  then obtain t where t: "\<forall>s\<in>S. t s \<in> S" and "\<forall>s\<in>S. s < t s"
    by (metis not_le)
  then have "\<And>s. s\<in>S \<Longrightarrow> open {..< t s}" "S \<subseteq> (\<Union>s\<in>S. {..< t s})"
    by auto
  with \<open>compact S\<close> obtain C where "C \<subseteq> S" "finite C" and C: "S \<subseteq> (\<Union>s\<in>C. {..< t s})"
    by (metis compactE_image)
  with \<open>S \<noteq> {}\<close> have Max: "Max (t`C) \<in> t`C" and "\<forall>s\<in>t`C. s \<le> Max (t`C)"
    by (auto intro!: Max_in)
  with C have "S \<subseteq> {..< Max (t`C)}"
    by (auto intro: less_le_trans simp: subset_eq)
  with t Max \<open>C \<subseteq> S\<close> show ?thesis
    by fastforce
qed

lemma (in linorder_topology) compact_attains_inf:
  assumes "compact S" "S \<noteq> {}"
  shows "\<exists>s\<in>S. \<forall>t\<in>S. s \<le> t"
proof (rule classical)
  assume "\<not> (\<exists>s\<in>S. \<forall>t\<in>S. s \<le> t)"
  then obtain t where t: "\<forall>s\<in>S. t s \<in> S" and "\<forall>s\<in>S. t s < s"
    by (metis not_le)
  then have "\<And>s. s\<in>S \<Longrightarrow> open {t s <..}" "S \<subseteq> (\<Union>s\<in>S. {t s <..})"
    by auto
  with \<open>compact S\<close> obtain C where "C \<subseteq> S" "finite C" and C: "S \<subseteq> (\<Union>s\<in>C. {t s <..})"
    by (metis compactE_image)
  with \<open>S \<noteq> {}\<close> have Min: "Min (t`C) \<in> t`C" and "\<forall>s\<in>t`C. Min (t`C) \<le> s"
    by (auto intro!: Min_in)
  with C have "S \<subseteq> {Min (t`C) <..}"
    by (auto intro: le_less_trans simp: subset_eq)
  with t Min \<open>C \<subseteq> S\<close> show ?thesis
    by fastforce
qed

lemma continuous_attains_sup:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s f \<Longrightarrow> (\<exists>x\<in>s. \<forall>y\<in>s.  f y \<le> f x)"
  using compact_attains_sup[of "f ` s"] compact_continuous_image[of s f] by auto

lemma continuous_attains_inf:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "compact s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> continuous_on s f \<Longrightarrow> (\<exists>x\<in>s. \<forall>y\<in>s. f x \<le> f y)"
  using compact_attains_inf[of "f ` s"] compact_continuous_image[of s f] by auto


subsection \<open>Connectedness\<close>

context topological_space
begin

definition "connected S \<longleftrightarrow>
  \<not> (\<exists>A B. open A \<and> open B \<and> S \<subseteq> A \<union> B \<and> A \<inter> B \<inter> S = {} \<and> A \<inter> S \<noteq> {} \<and> B \<inter> S \<noteq> {})"

lemma connectedI:
  "(\<And>A B. open A \<Longrightarrow> open B \<Longrightarrow> A \<inter> U \<noteq> {} \<Longrightarrow> B \<inter> U \<noteq> {} \<Longrightarrow> A \<inter> B \<inter> U = {} \<Longrightarrow> U \<subseteq> A \<union> B \<Longrightarrow> False)
  \<Longrightarrow> connected U"
  by (auto simp: connected_def)

lemma connected_empty [simp]: "connected {}"
  by (auto intro!: connectedI)

lemma connected_sing [simp]: "connected {x}"
  by (auto intro!: connectedI)

lemma connectedD:
  "connected A \<Longrightarrow> open U \<Longrightarrow> open V \<Longrightarrow> U \<inter> V \<inter> A = {} \<Longrightarrow> A \<subseteq> U \<union> V \<Longrightarrow> U \<inter> A = {} \<or> V \<inter> A = {}"
  by (auto simp: connected_def)

end

lemma connected_closed:
  "connected s \<longleftrightarrow>
    \<not> (\<exists>A B. closed A \<and> closed B \<and> s \<subseteq> A \<union> B \<and> A \<inter> B \<inter> s = {} \<and> A \<inter> s \<noteq> {} \<and> B \<inter> s \<noteq> {})"
  apply (simp add: connected_def del: ex_simps, safe)
   apply (drule_tac x="-A" in spec)
   apply (drule_tac x="-B" in spec)
   apply (fastforce simp add: closed_def [symmetric])
  apply (drule_tac x="-A" in spec)
  apply (drule_tac x="-B" in spec)
  apply (fastforce simp add: open_closed [symmetric])
  done

lemma connected_closedD:
  "\<lbrakk>connected s; A \<inter> B \<inter> s = {}; s \<subseteq> A \<union> B; closed A; closed B\<rbrakk> \<Longrightarrow> A \<inter> s = {} \<or> B \<inter> s = {}"
  by (simp add: connected_closed)

lemma connected_Union:
  assumes cs: "\<And>s. s \<in> S \<Longrightarrow> connected s"
    and ne: "\<Inter>S \<noteq> {}"
  shows "connected(\<Union>S)"
proof (rule connectedI)
  fix A B
  assume A: "open A" and B: "open B" and Alap: "A \<inter> \<Union>S \<noteq> {}" and Blap: "B \<inter> \<Union>S \<noteq> {}"
    and disj: "A \<inter> B \<inter> \<Union>S = {}" and cover: "\<Union>S \<subseteq> A \<union> B"
  have disjs:"\<And>s. s \<in> S \<Longrightarrow> A \<inter> B \<inter> s = {}"
    using disj by auto
  obtain sa where sa: "sa \<in> S" "A \<inter> sa \<noteq> {}"
    using Alap by auto
  obtain sb where sb: "sb \<in> S" "B \<inter> sb \<noteq> {}"
    using Blap by auto
  obtain x where x: "\<And>s. s \<in> S \<Longrightarrow> x \<in> s"
    using ne by auto
  then have "x \<in> \<Union>S"
    using \<open>sa \<in> S\<close> by blast
  then have "x \<in> A \<or> x \<in> B"
    using cover by auto
  then show False
    using cs [unfolded connected_def]
    by (metis A B IntI Sup_upper sa sb disjs x cover empty_iff subset_trans)
qed

lemma connected_Un: "connected s \<Longrightarrow> connected t \<Longrightarrow> s \<inter> t \<noteq> {} \<Longrightarrow> connected (s \<union> t)"
  using connected_Union [of "{s,t}"] by auto

lemma connected_diff_open_from_closed:
  assumes st: "s \<subseteq> t"
    and tu: "t \<subseteq> u"
    and s: "open s"
    and t: "closed t"
    and u: "connected u"
    and ts: "connected (t - s)"
  shows "connected(u - s)"
proof (rule connectedI)
  fix A B
  assume AB: "open A" "open B" "A \<inter> (u - s) \<noteq> {}" "B \<inter> (u - s) \<noteq> {}"
    and disj: "A \<inter> B \<inter> (u - s) = {}"
    and cover: "u - s \<subseteq> A \<union> B"
  then consider "A \<inter> (t - s) = {}" | "B \<inter> (t - s) = {}"
    using st ts tu connectedD [of "t-s" "A" "B"] by auto
  then show False
  proof cases
    case 1
    then have "(A - t) \<inter> (B \<union> s) \<inter> u = {}"
      using disj st by auto
    moreover have "u \<subseteq> (A - t) \<union> (B \<union> s)"
      using 1 cover by auto
    ultimately show False
      using connectedD [of u "A - t" "B \<union> s"] AB s t 1 u by auto
  next
    case 2
    then have "(A \<union> s) \<inter> (B - t) \<inter> u = {}"
      using disj st by auto
    moreover have "u \<subseteq> (A \<union> s) \<union> (B - t)"
      using 2 cover by auto
    ultimately show False
      using connectedD [of u "A \<union> s" "B - t"] AB s t 2 u by auto
  qed
qed

lemma connected_iff_const:
  fixes S :: "'a::topological_space set"
  shows "connected S \<longleftrightarrow> (\<forall>P::'a \<Rightarrow> bool. continuous_on S P \<longrightarrow> (\<exists>c. \<forall>s\<in>S. P s = c))"
proof safe
  fix P :: "'a \<Rightarrow> bool"
  assume "connected S" "continuous_on S P"
  then have "\<And>b. \<exists>A. open A \<and> A \<inter> S = P -` {b} \<inter> S"
    unfolding continuous_on_open_invariant by (simp add: open_discrete)
  from this[of True] this[of False]
  obtain t f where "open t" "open f" and *: "f \<inter> S = P -` {False} \<inter> S" "t \<inter> S = P -` {True} \<inter> S"
    by meson
  then have "t \<inter> S = {} \<or> f \<inter> S = {}"
    by (intro connectedD[OF \<open>connected S\<close>])  auto
  then show "\<exists>c. \<forall>s\<in>S. P s = c"
  proof (rule disjE)
    assume "t \<inter> S = {}"
    then show ?thesis
      unfolding * by (intro exI[of _ False]) auto
  next
    assume "f \<inter> S = {}"
    then show ?thesis
      unfolding * by (intro exI[of _ True]) auto
  qed
next
  assume P: "\<forall>P::'a \<Rightarrow> bool. continuous_on S P \<longrightarrow> (\<exists>c. \<forall>s\<in>S. P s = c)"
  show "connected S"
  proof (rule connectedI)
    fix A B
    assume *: "open A" "open B" "A \<inter> S \<noteq> {}" "B \<inter> S \<noteq> {}" "A \<inter> B \<inter> S = {}" "S \<subseteq> A \<union> B"
    have "continuous_on S (\<lambda>x. x \<in> A)"
      unfolding continuous_on_open_invariant
    proof safe
      fix C :: "bool set"
      have "C = UNIV \<or> C = {True} \<or> C = {False} \<or> C = {}"
        using subset_UNIV[of C] unfolding UNIV_bool by auto
      with * show "\<exists>T. open T \<and> T \<inter> S = (\<lambda>x. x \<in> A) -` C \<inter> S"
        by (intro exI[of _ "(if True \<in> C then A else {}) \<union> (if False \<in> C then B else {})"]) auto
    qed
    from P[rule_format, OF this] obtain c where "\<And>s. s \<in> S \<Longrightarrow> (s \<in> A) = c"
      by blast
    with * show False
      by (cases c) auto
  qed
qed

lemma connectedD_const: "connected S \<Longrightarrow> continuous_on S P \<Longrightarrow> \<exists>c. \<forall>s\<in>S. P s = c"
  for P :: "'a::topological_space \<Rightarrow> bool"
  by (auto simp: connected_iff_const)

lemma connectedI_const:
  "(\<And>P::'a::topological_space \<Rightarrow> bool. continuous_on S P \<Longrightarrow> \<exists>c. \<forall>s\<in>S. P s = c) \<Longrightarrow> connected S"
  by (auto simp: connected_iff_const)

lemma connected_local_const:
  assumes "connected A" "a \<in> A" "b \<in> A"
    and *: "\<forall>a\<in>A. eventually (\<lambda>b. f a = f b) (at a within A)"
  shows "f a = f b"
proof -
  obtain S where S: "\<And>a. a \<in> A \<Longrightarrow> a \<in> S a" "\<And>a. a \<in> A \<Longrightarrow> open (S a)"
    "\<And>a x. a \<in> A \<Longrightarrow> x \<in> S a \<Longrightarrow> x \<in> A \<Longrightarrow> f a = f x"
    using * unfolding eventually_at_topological by metis
  let ?P = "\<Union>b\<in>{b\<in>A. f a = f b}. S b" and ?N = "\<Union>b\<in>{b\<in>A. f a \<noteq> f b}. S b"
  have "?P \<inter> A = {} \<or> ?N \<inter> A = {}"
    using \<open>connected A\<close> S \<open>a\<in>A\<close>
    by (intro connectedD) (auto, metis)
  then show "f a = f b"
  proof
    assume "?N \<inter> A = {}"
    then have "\<forall>x\<in>A. f a = f x"
      using S(1) by auto
    with \<open>b\<in>A\<close> show ?thesis by auto
  next
    assume "?P \<inter> A = {}" then show ?thesis
      using \<open>a \<in> A\<close> S(1)[of a] by auto
  qed
qed

lemma (in linorder_topology) connectedD_interval:
  assumes "connected U"
    and xy: "x \<in> U" "y \<in> U"
    and "x \<le> z" "z \<le> y"
  shows "z \<in> U"
proof -
  have eq: "{..<z} \<union> {z<..} = - {z}"
    by auto
  have "\<not> connected U" if "z \<notin> U" "x < z" "z < y"
    using xy that
    apply (simp only: connected_def simp_thms)
    apply (rule_tac exI[of _ "{..< z}"])
    apply (rule_tac exI[of _ "{z <..}"])
    apply (auto simp add: eq)
    done
  with assms show "z \<in> U"
    by (metis less_le)
qed

lemma (in linorder_topology) not_in_connected_cases:
  assumes conn: "connected S"
  assumes nbdd: "x \<notin> S"
  assumes ne: "S \<noteq> {}"
  obtains "bdd_above S" "\<And>y. y \<in> S \<Longrightarrow> x \<ge> y" | "bdd_below S" "\<And>y. y \<in> S \<Longrightarrow> x \<le> y"
proof -
  obtain s where "s \<in> S" using ne by blast
  {
    assume "s \<le> x"
    have "False" if "x \<le> y" "y \<in> S" for y
      using connectedD_interval[OF conn \<open>s \<in> S\<close> \<open>y \<in> S\<close> \<open>s \<le> x\<close> \<open>x \<le> y\<close>] \<open>x \<notin> S\<close>
      by simp
    then have wit: "y \<in> S \<Longrightarrow> x \<ge> y" for y
      using le_cases by blast
    then have "bdd_above S"
      by (rule local.bdd_aboveI)
    note this wit
  } moreover {
    assume "x \<le> s"
    have "False" if "x \<ge> y" "y \<in> S" for y
      using connectedD_interval[OF conn \<open>y \<in> S\<close> \<open>s \<in> S\<close> \<open>x \<ge> y\<close> \<open>s \<ge> x\<close> ] \<open>x \<notin> S\<close>
      by simp
    then have wit: "y \<in> S \<Longrightarrow> x \<le> y" for y
      using le_cases by blast
    then have "bdd_below S"
      by (rule bdd_belowI)
    note this wit
  } ultimately show ?thesis
    by (meson le_cases that)
qed

lemma connected_continuous_image:
  assumes *: "continuous_on s f"
    and "connected s"
  shows "connected (f ` s)"
proof (rule connectedI_const)
  fix P :: "'b \<Rightarrow> bool"
  assume "continuous_on (f ` s) P"
  then have "continuous_on s (P \<circ> f)"
    by (rule continuous_on_compose[OF *])
  from connectedD_const[OF \<open>connected s\<close> this] show "\<exists>c. \<forall>s\<in>f ` s. P s = c"
    by auto
qed


section \<open>Linear Continuum Topologies\<close>

class linear_continuum_topology = linorder_topology + linear_continuum
begin

lemma Inf_notin_open:
  assumes A: "open A"
    and bnd: "\<forall>a\<in>A. x < a"
  shows "Inf A \<notin> A"
proof
  assume "Inf A \<in> A"
  then obtain b where "b < Inf A" "{b <.. Inf A} \<subseteq> A"
    using open_left[of A "Inf A" x] assms by auto
  with dense[of b "Inf A"] obtain c where "c < Inf A" "c \<in> A"
    by (auto simp: subset_eq)
  then show False
    using cInf_lower[OF \<open>c \<in> A\<close>] bnd
    by (metis not_le less_imp_le bdd_belowI)
qed

lemma Sup_notin_open:
  assumes A: "open A"
    and bnd: "\<forall>a\<in>A. a < x"
  shows "Sup A \<notin> A"
proof
  assume "Sup A \<in> A"
  with assms obtain b where "Sup A < b" "{Sup A ..< b} \<subseteq> A"
    using open_right[of A "Sup A" x] by auto
  with dense[of "Sup A" b] obtain c where "Sup A < c" "c \<in> A"
    by (auto simp: subset_eq)
  then show False
    using cSup_upper[OF \<open>c \<in> A\<close>] bnd
    by (metis less_imp_le not_le bdd_aboveI)
qed

end

instance linear_continuum_topology \<subseteq> perfect_space
proof
  fix x :: 'a
  obtain y where "x < y \<or> y < x"
    using ex_gt_or_lt [of x] ..
  with Inf_notin_open[of "{x}" y] Sup_notin_open[of "{x}" y] show "\<not> open {x}"
    by auto
qed

lemma connectedI_interval:
  fixes U :: "'a :: linear_continuum_topology set"
  assumes *: "\<And>x y z. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x \<le> z \<Longrightarrow> z \<le> y \<Longrightarrow> z \<in> U"
  shows "connected U"
proof (rule connectedI)
  {
    fix A B
    assume "open A" "open B" "A \<inter> B \<inter> U = {}" "U \<subseteq> A \<union> B"
    fix x y
    assume "x < y" "x \<in> A" "y \<in> B" "x \<in> U" "y \<in> U"

    let ?z = "Inf (B \<inter> {x <..})"

    have "x \<le> ?z" "?z \<le> y"
      using \<open>y \<in> B\<close> \<open>x < y\<close> by (auto intro: cInf_lower cInf_greatest)
    with \<open>x \<in> U\<close> \<open>y \<in> U\<close> have "?z \<in> U"
      by (rule *)
    moreover have "?z \<notin> B \<inter> {x <..}"
      using \<open>open B\<close> by (intro Inf_notin_open) auto
    ultimately have "?z \<in> A"
      using \<open>x \<le> ?z\<close> \<open>A \<inter> B \<inter> U = {}\<close> \<open>x \<in> A\<close> \<open>U \<subseteq> A \<union> B\<close> by auto
    have "\<exists>b\<in>B. b \<in> A \<and> b \<in> U" if "?z < y"
    proof -
      obtain a where "?z < a" "{?z ..< a} \<subseteq> A"
        using open_right[OF \<open>open A\<close> \<open>?z \<in> A\<close> \<open>?z < y\<close>] by auto
      moreover obtain b where "b \<in> B" "x < b" "b < min a y"
        using cInf_less_iff[of "B \<inter> {x <..}" "min a y"] \<open>?z < a\<close> \<open>?z < y\<close> \<open>x < y\<close> \<open>y \<in> B\<close>
        by auto
      moreover have "?z \<le> b"
        using \<open>b \<in> B\<close> \<open>x < b\<close>
        by (intro cInf_lower) auto
      moreover have "b \<in> U"
        using \<open>x \<le> ?z\<close> \<open>?z \<le> b\<close> \<open>b < min a y\<close>
        by (intro *[OF \<open>x \<in> U\<close> \<open>y \<in> U\<close>]) (auto simp: less_imp_le)
      ultimately show ?thesis
        by (intro bexI[of _ b]) auto
    qed
    then have False
      using \<open>?z \<le> y\<close> \<open>?z \<in> A\<close> \<open>y \<in> B\<close> \<open>y \<in> U\<close> \<open>A \<inter> B \<inter> U = {}\<close>
      unfolding le_less by blast
  }
  note not_disjoint = this

  fix A B assume AB: "open A" "open B" "U \<subseteq> A \<union> B" "A \<inter> B \<inter> U = {}"
  moreover assume "A \<inter> U \<noteq> {}" then obtain x where x: "x \<in> U" "x \<in> A" by auto
  moreover assume "B \<inter> U \<noteq> {}" then obtain y where y: "y \<in> U" "y \<in> B" by auto
  moreover note not_disjoint[of B A y x] not_disjoint[of A B x y]
  ultimately show False
    by (cases x y rule: linorder_cases) auto
qed

lemma connected_iff_interval: "connected U \<longleftrightarrow> (\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z. x \<le> z \<longrightarrow> z \<le> y \<longrightarrow> z \<in> U)"
  for U :: "'a::linear_continuum_topology set"
  by (auto intro: connectedI_interval dest: connectedD_interval)

lemma connected_UNIV[simp]: "connected (UNIV::'a::linear_continuum_topology set)"
  by (simp add: connected_iff_interval)

lemma connected_Ioi[simp]: "connected {a<..}"
  for a :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Ici[simp]: "connected {a..}"
  for a :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Iio[simp]: "connected {..<a}"
  for a :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Iic[simp]: "connected {..a}"
  for a :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Ioo[simp]: "connected {a<..<b}"
  for a b :: "'a::linear_continuum_topology"
  unfolding connected_iff_interval by auto

lemma connected_Ioc[simp]: "connected {a<..b}"
  for a b :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Ico[simp]: "connected {a..<b}"
  for a b :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_Icc[simp]: "connected {a..b}"
  for a b :: "'a::linear_continuum_topology"
  by (auto simp: connected_iff_interval)

lemma connected_contains_Ioo:
  fixes A :: "'a :: linorder_topology set"
  assumes "connected A" "a \<in> A" "b \<in> A" shows "{a <..< b} \<subseteq> A"
  using connectedD_interval[OF assms] by (simp add: subset_eq Ball_def less_imp_le)

lemma connected_contains_Icc:
  fixes A :: "'a::linorder_topology set"
  assumes "connected A" "a \<in> A" "b \<in> A"
  shows "{a..b} \<subseteq> A"
proof
  fix x assume "x \<in> {a..b}"
  then have "x = a \<or> x = b \<or> x \<in> {a<..<b}"
    by auto
  then show "x \<in> A"
    using assms connected_contains_Ioo[of A a b] by auto
qed


subsection \<open>Intermediate Value Theorem\<close>

lemma IVT':
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes y: "f a \<le> y" "y \<le> f b" "a \<le> b"
    and *: "continuous_on {a .. b} f"
  shows "\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
proof -
  have "connected {a..b}"
    unfolding connected_iff_interval by auto
  from connected_continuous_image[OF * this, THEN connectedD_interval, of "f a" "f b" y] y
  show ?thesis
    by (auto simp add: atLeastAtMost_def atLeast_def atMost_def)
qed

lemma IVT2':
  fixes f :: "'a :: linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes y: "f b \<le> y" "y \<le> f a" "a \<le> b"
    and *: "continuous_on {a .. b} f"
  shows "\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
proof -
  have "connected {a..b}"
    unfolding connected_iff_interval by auto
  from connected_continuous_image[OF * this, THEN connectedD_interval, of "f b" "f a" y] y
  show ?thesis
    by (auto simp add: atLeastAtMost_def atLeast_def atMost_def)
qed

lemma IVT:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  shows "f a \<le> y \<Longrightarrow> y \<le> f b \<Longrightarrow> a \<le> b \<Longrightarrow> (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x) \<Longrightarrow>
    \<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
  by (rule IVT') (auto intro: continuous_at_imp_continuous_on)

lemma IVT2:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  shows "f b \<le> y \<Longrightarrow> y \<le> f a \<Longrightarrow> a \<le> b \<Longrightarrow> (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x) \<Longrightarrow>
    \<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
  by (rule IVT2') (auto intro: continuous_at_imp_continuous_on)

lemma continuous_inj_imp_mono:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes x: "a < x" "x < b"
    and cont: "continuous_on {a..b} f"
    and inj: "inj_on f {a..b}"
  shows "(f a < f x \<and> f x < f b) \<or> (f b < f x \<and> f x < f a)"
proof -
  note I = inj_on_eq_iff[OF inj]
  {
    assume "f x < f a" "f x < f b"
    then obtain s t where "x \<le> s" "s \<le> b" "a \<le> t" "t \<le> x" "f s = f t" "f x < f s"
      using IVT'[of f x "min (f a) (f b)" b] IVT2'[of f x "min (f a) (f b)" a] x
      by (auto simp: continuous_on_subset[OF cont] less_imp_le)
    with x I have False by auto
  }
  moreover
  {
    assume "f a < f x" "f b < f x"
    then obtain s t where "x \<le> s" "s \<le> b" "a \<le> t" "t \<le> x" "f s = f t" "f s < f x"
      using IVT'[of f a "max (f a) (f b)" x] IVT2'[of f b "max (f a) (f b)" x] x
      by (auto simp: continuous_on_subset[OF cont] less_imp_le)
    with x I have False by auto
  }
  ultimately show ?thesis
    using I[of a x] I[of x b] x less_trans[OF x]
    by (auto simp add: le_less less_imp_neq neq_iff)
qed

lemma continuous_at_Sup_mono:
  fixes f :: "'a::{linorder_topology,conditionally_complete_linorder} \<Rightarrow>
    'b::{linorder_topology,conditionally_complete_linorder}"
  assumes "mono f"
    and cont: "continuous (at_left (Sup S)) f"
    and S: "S \<noteq> {}" "bdd_above S"
  shows "f (Sup S) = (SUP s\<in>S. f s)"
proof (rule antisym)
  have f: "(f \<longlongrightarrow> f (Sup S)) (at_left (Sup S))"
    using cont unfolding continuous_within .
  show "f (Sup S) \<le> (SUP s\<in>S. f s)"
  proof cases
    assume "Sup S \<in> S"
    then show ?thesis
      by (rule cSUP_upper) (auto intro: bdd_above_image_mono S \<open>mono f\<close>)
  next
    assume "Sup S \<notin> S"
    from \<open>S \<noteq> {}\<close> obtain s where "s \<in> S"
      by auto
    with \<open>Sup S \<notin> S\<close> S have "s < Sup S"
      unfolding less_le by (blast intro: cSup_upper)
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with order_tendstoD(1)[OF f, of "SUP s\<in>S. f s"] obtain b where "b < Sup S"
        and *: "\<And>y. b < y \<Longrightarrow> y < Sup S \<Longrightarrow> (SUP s\<in>S. f s) < f y"
        by (auto simp: not_le eventually_at_left[OF \<open>s < Sup S\<close>])
      with \<open>S \<noteq> {}\<close> obtain c where "c \<in> S" "b < c"
        using less_cSupD[of S b] by auto
      with \<open>Sup S \<notin> S\<close> S have "c < Sup S"
        unfolding less_le by (blast intro: cSup_upper)
      from *[OF \<open>b < c\<close> \<open>c < Sup S\<close>] cSUP_upper[OF \<open>c \<in> S\<close> bdd_above_image_mono[of f]]
      show False
        by (auto simp: assms)
    qed
  qed
qed (intro cSUP_least \<open>mono f\<close>[THEN monoD] cSup_upper S)

lemma continuous_at_Sup_antimono:
  fixes f :: "'a::{linorder_topology,conditionally_complete_linorder} \<Rightarrow>
    'b::{linorder_topology,conditionally_complete_linorder}"
  assumes "antimono f"
    and cont: "continuous (at_left (Sup S)) f"
    and S: "S \<noteq> {}" "bdd_above S"
  shows "f (Sup S) = (INF s\<in>S. f s)"
proof (rule antisym)
  have f: "(f \<longlongrightarrow> f (Sup S)) (at_left (Sup S))"
    using cont unfolding continuous_within .
  show "(INF s\<in>S. f s) \<le> f (Sup S)"
  proof cases
    assume "Sup S \<in> S"
    then show ?thesis
      by (intro cINF_lower) (auto intro: bdd_below_image_antimono S \<open>antimono f\<close>)
  next
    assume "Sup S \<notin> S"
    from \<open>S \<noteq> {}\<close> obtain s where "s \<in> S"
      by auto
    with \<open>Sup S \<notin> S\<close> S have "s < Sup S"
      unfolding less_le by (blast intro: cSup_upper)
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with order_tendstoD(2)[OF f, of "INF s\<in>S. f s"] obtain b where "b < Sup S"
        and *: "\<And>y. b < y \<Longrightarrow> y < Sup S \<Longrightarrow> f y < (INF s\<in>S. f s)"
        by (auto simp: not_le eventually_at_left[OF \<open>s < Sup S\<close>])
      with \<open>S \<noteq> {}\<close> obtain c where "c \<in> S" "b < c"
        using less_cSupD[of S b] by auto
      with \<open>Sup S \<notin> S\<close> S have "c < Sup S"
        unfolding less_le by (blast intro: cSup_upper)
      from *[OF \<open>b < c\<close> \<open>c < Sup S\<close>] cINF_lower[OF bdd_below_image_antimono, of f S c] \<open>c \<in> S\<close>
      show False
        by (auto simp: assms)
    qed
  qed
qed (intro cINF_greatest \<open>antimono f\<close>[THEN antimonoD] cSup_upper S)

lemma continuous_at_Inf_mono:
  fixes f :: "'a::{linorder_topology,conditionally_complete_linorder} \<Rightarrow>
    'b::{linorder_topology,conditionally_complete_linorder}"
  assumes "mono f"
    and cont: "continuous (at_right (Inf S)) f"
    and S: "S \<noteq> {}" "bdd_below S"
  shows "f (Inf S) = (INF s\<in>S. f s)"
proof (rule antisym)
  have f: "(f \<longlongrightarrow> f (Inf S)) (at_right (Inf S))"
    using cont unfolding continuous_within .
  show "(INF s\<in>S. f s) \<le> f (Inf S)"
  proof cases
    assume "Inf S \<in> S"
    then show ?thesis
      by (rule cINF_lower[rotated]) (auto intro: bdd_below_image_mono S \<open>mono f\<close>)
  next
    assume "Inf S \<notin> S"
    from \<open>S \<noteq> {}\<close> obtain s where "s \<in> S"
      by auto
    with \<open>Inf S \<notin> S\<close> S have "Inf S < s"
      unfolding less_le by (blast intro: cInf_lower)
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with order_tendstoD(2)[OF f, of "INF s\<in>S. f s"] obtain b where "Inf S < b"
        and *: "\<And>y. Inf S < y \<Longrightarrow> y < b \<Longrightarrow> f y < (INF s\<in>S. f s)"
        by (auto simp: not_le eventually_at_right[OF \<open>Inf S < s\<close>])
      with \<open>S \<noteq> {}\<close> obtain c where "c \<in> S" "c < b"
        using cInf_lessD[of S b] by auto
      with \<open>Inf S \<notin> S\<close> S have "Inf S < c"
        unfolding less_le by (blast intro: cInf_lower)
      from *[OF \<open>Inf S < c\<close> \<open>c < b\<close>] cINF_lower[OF bdd_below_image_mono[of f] \<open>c \<in> S\<close>]
      show False
        by (auto simp: assms)
    qed
  qed
qed (intro cINF_greatest \<open>mono f\<close>[THEN monoD] cInf_lower \<open>bdd_below S\<close> \<open>S \<noteq> {}\<close>)

lemma continuous_at_Inf_antimono:
  fixes f :: "'a::{linorder_topology,conditionally_complete_linorder} \<Rightarrow>
    'b::{linorder_topology,conditionally_complete_linorder}"
  assumes "antimono f"
    and cont: "continuous (at_right (Inf S)) f"
    and S: "S \<noteq> {}" "bdd_below S"
  shows "f (Inf S) = (SUP s\<in>S. f s)"
proof (rule antisym)
  have f: "(f \<longlongrightarrow> f (Inf S)) (at_right (Inf S))"
    using cont unfolding continuous_within .
  show "f (Inf S) \<le> (SUP s\<in>S. f s)"
  proof cases
    assume "Inf S \<in> S"
    then show ?thesis
      by (rule cSUP_upper) (auto intro: bdd_above_image_antimono S \<open>antimono f\<close>)
  next
    assume "Inf S \<notin> S"
    from \<open>S \<noteq> {}\<close> obtain s where "s \<in> S"
      by auto
    with \<open>Inf S \<notin> S\<close> S have "Inf S < s"
      unfolding less_le by (blast intro: cInf_lower)
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with order_tendstoD(1)[OF f, of "SUP s\<in>S. f s"] obtain b where "Inf S < b"
        and *: "\<And>y. Inf S < y \<Longrightarrow> y < b \<Longrightarrow> (SUP s\<in>S. f s) < f y"
        by (auto simp: not_le eventually_at_right[OF \<open>Inf S < s\<close>])
      with \<open>S \<noteq> {}\<close> obtain c where "c \<in> S" "c < b"
        using cInf_lessD[of S b] by auto
      with \<open>Inf S \<notin> S\<close> S have "Inf S < c"
        unfolding less_le by (blast intro: cInf_lower)
      from *[OF \<open>Inf S < c\<close> \<open>c < b\<close>] cSUP_upper[OF \<open>c \<in> S\<close> bdd_above_image_antimono[of f]]
      show False
        by (auto simp: assms)
    qed
  qed
qed (intro cSUP_least \<open>antimono f\<close>[THEN antimonoD] cInf_lower S)


subsection \<open>Uniform spaces\<close>

class uniformity =
  fixes uniformity :: "('a \<times> 'a) filter"
begin

abbreviation uniformity_on :: "'a set \<Rightarrow> ('a \<times> 'a) filter"
  where "uniformity_on s \<equiv> inf uniformity (principal (s\<times>s))"

end

lemma uniformity_Abort:
  "uniformity =
    Filter.abstract_filter (\<lambda>u. Code.abort (STR ''uniformity is not executable'') (\<lambda>u. uniformity))"
  by simp

class open_uniformity = "open" + uniformity +
  assumes open_uniformity:
    "\<And>U. open U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"
begin

subclass topological_space
  by standard (force elim: eventually_mono eventually_elim2 simp: split_beta' open_uniformity)+

end

class uniform_space = open_uniformity +
  assumes uniformity_refl: "eventually E uniformity \<Longrightarrow> E (x, x)"
    and uniformity_sym: "eventually E uniformity \<Longrightarrow> eventually (\<lambda>(x, y). E (y, x)) uniformity"
    and uniformity_trans:
      "eventually E uniformity \<Longrightarrow>
        \<exists>D. eventually D uniformity \<and> (\<forall>x y z. D (x, y) \<longrightarrow> D (y, z) \<longrightarrow> E (x, z))"
begin

lemma uniformity_bot: "uniformity \<noteq> bot"
  using uniformity_refl by auto

lemma uniformity_trans':
  "eventually E uniformity \<Longrightarrow>
    eventually (\<lambda>((x, y), (y', z)). y = y' \<longrightarrow> E (x, z)) (uniformity \<times>\<^sub>F uniformity)"
  by (drule uniformity_trans) (auto simp add: eventually_prod_same)

lemma uniformity_transE:
  assumes "eventually E uniformity"
  obtains D where "eventually D uniformity" "\<And>x y z. D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)"
  using uniformity_trans [OF assms] by auto

lemma eventually_nhds_uniformity:
  "eventually P (nhds x) \<longleftrightarrow> eventually (\<lambda>(x', y). x' = x \<longrightarrow> P y) uniformity"
  (is "_ \<longleftrightarrow> ?N P x")
  unfolding eventually_nhds
proof safe
  assume *: "?N P x"
  have "?N (?N P) x" if "?N P x" for x
  proof -
    from that obtain D where ev: "eventually D uniformity"
      and D: "D (a, b) \<Longrightarrow> D (b, c) \<Longrightarrow> case (a, c) of (x', y) \<Rightarrow> x' = x \<longrightarrow> P y" for a b c
      by (rule uniformity_transE) simp
    from ev show ?thesis
      by eventually_elim (insert ev D, force elim: eventually_mono split: prod.split)
  qed
  then have "open {x. ?N P x}"
    by (simp add: open_uniformity)
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>x\<in>S. P x)"
    by (intro exI[of _ "{x. ?N P x}"]) (auto dest: uniformity_refl simp: *)
qed (force simp add: open_uniformity elim: eventually_mono)


subsubsection \<open>Totally bounded sets\<close>

definition totally_bounded :: "'a set \<Rightarrow> bool"
  where "totally_bounded S \<longleftrightarrow>
    (\<forall>E. eventually E uniformity \<longrightarrow> (\<exists>X. finite X \<and> (\<forall>s\<in>S. \<exists>x\<in>X. E (x, s))))"

lemma totally_bounded_empty[iff]: "totally_bounded {}"
  by (auto simp add: totally_bounded_def)

lemma totally_bounded_subset: "totally_bounded S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> totally_bounded T"
  by (fastforce simp add: totally_bounded_def)

lemma totally_bounded_Union[intro]:
  assumes M: "finite M" "\<And>S. S \<in> M \<Longrightarrow> totally_bounded S"
  shows "totally_bounded (\<Union>M)"
  unfolding totally_bounded_def
proof safe
  fix E
  assume "eventually E uniformity"
  with M obtain X where "\<forall>S\<in>M. finite (X S) \<and> (\<forall>s\<in>S. \<exists>x\<in>X S. E (x, s))"
    by (metis totally_bounded_def)
  with \<open>finite M\<close> show "\<exists>X. finite X \<and> (\<forall>s\<in>\<Union>M. \<exists>x\<in>X. E (x, s))"
    by (intro exI[of _ "\<Union>S\<in>M. X S"]) force
qed


subsubsection \<open>Cauchy filter\<close>

definition cauchy_filter :: "'a filter \<Rightarrow> bool"
  where "cauchy_filter F \<longleftrightarrow> F \<times>\<^sub>F F \<le> uniformity"

definition Cauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where Cauchy_uniform: "Cauchy X = cauchy_filter (filtermap X sequentially)"

lemma Cauchy_uniform_iff:
  "Cauchy X \<longleftrightarrow> (\<forall>P. eventually P uniformity \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. P (X n, X m)))"
  unfolding Cauchy_uniform cauchy_filter_def le_filter_def eventually_prod_same
    eventually_filtermap eventually_sequentially
proof safe
  let ?U = "\<lambda>P. eventually P uniformity"
  {
    fix P
    assume "?U P" "\<forall>P. ?U P \<longrightarrow> (\<exists>Q. (\<exists>N. \<forall>n\<ge>N. Q (X n)) \<and> (\<forall>x y. Q x \<longrightarrow> Q y \<longrightarrow> P (x, y)))"
    then obtain Q N where "\<And>n. n \<ge> N \<Longrightarrow> Q (X n)" "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> P (x, y)"
      by metis
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. P (X n, X m)"
      by blast
  next
    fix P
    assume "?U P" and P: "\<forall>P. ?U P \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. P (X n, X m))"
    then obtain Q where "?U Q" and Q: "\<And>x y z. Q (x, y) \<Longrightarrow> Q (y, z) \<Longrightarrow> P (x, z)"
      by (auto elim: uniformity_transE)
    then have "?U (\<lambda>x. Q x \<and> (\<lambda>(x, y). Q (y, x)) x)"
      unfolding eventually_conj_iff by (simp add: uniformity_sym)
    from P[rule_format, OF this]
    obtain N where N: "\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> Q (X n, X m) \<and> Q (X m, X n)"
      by auto
    show "\<exists>Q. (\<exists>N. \<forall>n\<ge>N. Q (X n)) \<and> (\<forall>x y. Q x \<longrightarrow> Q y \<longrightarrow> P (x, y))"
    proof (safe intro!: exI[of _ "\<lambda>x. \<forall>n\<ge>N. Q (x, X n) \<and> Q (X n, x)"] exI[of _ N] N)
      fix x y
      assume "\<forall>n\<ge>N. Q (x, X n) \<and> Q (X n, x)" "\<forall>n\<ge>N. Q (y, X n) \<and> Q (X n, y)"
      then have "Q (x, X N)" "Q (X N, y)" by auto
      then show "P (x, y)"
        by (rule Q)
    qed
  }
qed

lemma nhds_imp_cauchy_filter:
  assumes *: "F \<le> nhds x"
  shows "cauchy_filter F"
proof -
  have "F \<times>\<^sub>F F \<le> nhds x \<times>\<^sub>F nhds x"
    by (intro prod_filter_mono *)
  also have "\<dots> \<le> uniformity"
    unfolding le_filter_def eventually_nhds_uniformity eventually_prod_same
  proof safe
    fix P
    assume "eventually P uniformity"
    then obtain Ql where ev: "eventually Ql uniformity"
      and "Ql (x, y) \<Longrightarrow> Ql (y, z) \<Longrightarrow> P (x, z)" for x y z
      by (rule uniformity_transE) simp
    with ev[THEN uniformity_sym]
    show "\<exists>Q. eventually (\<lambda>(x', y). x' = x \<longrightarrow> Q y) uniformity \<and>
        (\<forall>x y. Q x \<longrightarrow> Q y \<longrightarrow> P (x, y))"
      by (rule_tac exI[of _ "\<lambda>y. Ql (y, x) \<and> Ql (x, y)"]) (fastforce elim: eventually_elim2)
  qed
  finally show ?thesis
    by (simp add: cauchy_filter_def)
qed

lemma LIMSEQ_imp_Cauchy: "X \<longlonglongrightarrow> x \<Longrightarrow> Cauchy X"
  unfolding Cauchy_uniform filterlim_def by (intro nhds_imp_cauchy_filter)

lemma Cauchy_subseq_Cauchy:
  assumes "Cauchy X" "strict_mono f"
  shows "Cauchy (X \<circ> f)"
  unfolding Cauchy_uniform comp_def filtermap_filtermap[symmetric] cauchy_filter_def
  by (rule order_trans[OF _ \<open>Cauchy X\<close>[unfolded Cauchy_uniform cauchy_filter_def]])
     (intro prod_filter_mono filtermap_mono filterlim_subseq[OF \<open>strict_mono f\<close>, unfolded filterlim_def])

lemma convergent_Cauchy: "convergent X \<Longrightarrow> Cauchy X"
  unfolding convergent_def by (erule exE, erule LIMSEQ_imp_Cauchy)

definition complete :: "'a set \<Rightarrow> bool"
  where complete_uniform: "complete S \<longleftrightarrow>
    (\<forall>F \<le> principal S. F \<noteq> bot \<longrightarrow> cauchy_filter F \<longrightarrow> (\<exists>x\<in>S. F \<le> nhds x))"

end

subsubsection \<open>Uniformly continuous functions\<close>

definition uniformly_continuous_on :: "'a set \<Rightarrow> ('a::uniform_space \<Rightarrow> 'b::uniform_space) \<Rightarrow> bool"
  where uniformly_continuous_on_uniformity: "uniformly_continuous_on s f \<longleftrightarrow>
    (LIM (x, y) (uniformity_on s). (f x, f y) :> uniformity)"

lemma uniformly_continuous_onD:
  "uniformly_continuous_on s f \<Longrightarrow> eventually E uniformity \<Longrightarrow>
    eventually (\<lambda>(x, y). x \<in> s \<longrightarrow> y \<in> s \<longrightarrow> E (f x, f y)) uniformity"
  by (simp add: uniformly_continuous_on_uniformity filterlim_iff
      eventually_inf_principal split_beta' mem_Times_iff imp_conjL)

lemma uniformly_continuous_on_const[continuous_intros]: "uniformly_continuous_on s (\<lambda>x. c)"
  by (auto simp: uniformly_continuous_on_uniformity filterlim_iff uniformity_refl)

lemma uniformly_continuous_on_id[continuous_intros]: "uniformly_continuous_on s (\<lambda>x. x)"
  by (auto simp: uniformly_continuous_on_uniformity filterlim_def)

lemma uniformly_continuous_on_compose[continuous_intros]:
  "uniformly_continuous_on s g \<Longrightarrow> uniformly_continuous_on (g`s) f \<Longrightarrow>
    uniformly_continuous_on s (\<lambda>x. f (g x))"
  using filterlim_compose[of "\<lambda>(x, y). (f x, f y)" uniformity
      "uniformity_on (g`s)"  "\<lambda>(x, y). (g x, g y)" "uniformity_on s"]
  by (simp add: split_beta' uniformly_continuous_on_uniformity
      filterlim_inf filterlim_principal eventually_inf_principal mem_Times_iff)

lemma uniformly_continuous_imp_continuous:
  assumes f: "uniformly_continuous_on s f"
  shows "continuous_on s f"
  by (auto simp: filterlim_iff eventually_at_filter eventually_nhds_uniformity continuous_on_def
           elim: eventually_mono dest!: uniformly_continuous_onD[OF f])


section \<open>Product Topology\<close>

subsection \<open>Product is a topological space\<close>

instantiation prod :: (topological_space, topological_space) topological_space
begin

definition open_prod_def[code del]:
  "open (S :: ('a \<times> 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S)"

lemma open_prod_elim:
  assumes "open S" and "x \<in> S"
  obtains A B where "open A" and "open B" and "x \<in> A \<times> B" and "A \<times> B \<subseteq> S"
  using assms unfolding open_prod_def by fast

lemma open_prod_intro:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S"
  shows "open S"
  using assms unfolding open_prod_def by fast

instance
proof
  show "open (UNIV :: ('a \<times> 'b) set)"
    unfolding open_prod_def by auto
next
  fix S T :: "('a \<times> 'b) set"
  assume "open S" "open T"
  show "open (S \<inter> T)"
  proof (rule open_prod_intro)
    fix x
    assume x: "x \<in> S \<inter> T"
    from x have "x \<in> S" by simp
    obtain Sa Sb where A: "open Sa" "open Sb" "x \<in> Sa \<times> Sb" "Sa \<times> Sb \<subseteq> S"
      using \<open>open S\<close> and \<open>x \<in> S\<close> by (rule open_prod_elim)
    from x have "x \<in> T" by simp
    obtain Ta Tb where B: "open Ta" "open Tb" "x \<in> Ta \<times> Tb" "Ta \<times> Tb \<subseteq> T"
      using \<open>open T\<close> and \<open>x \<in> T\<close> by (rule open_prod_elim)
    let ?A = "Sa \<inter> Ta" and ?B = "Sb \<inter> Tb"
    have "open ?A \<and> open ?B \<and> x \<in> ?A \<times> ?B \<and> ?A \<times> ?B \<subseteq> S \<inter> T"
      using A B by (auto simp add: open_Int)
    then show "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S \<inter> T"
      by fast
  qed
next
  fix K :: "('a \<times> 'b) set set"
  assume "\<forall>S\<in>K. open S"
  then show "open (\<Union>K)"
    unfolding open_prod_def by fast
qed

end

declare [[code abort: "open :: ('a::topological_space \<times> 'b::topological_space) set \<Rightarrow> bool"]]

lemma open_Times: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<times> T)"
  unfolding open_prod_def by auto

lemma fst_vimage_eq_Times: "fst -` S = S \<times> UNIV"
  by auto

lemma snd_vimage_eq_Times: "snd -` S = UNIV \<times> S"
  by auto

lemma open_vimage_fst: "open S \<Longrightarrow> open (fst -` S)"
  by (simp add: fst_vimage_eq_Times open_Times)

lemma open_vimage_snd: "open S \<Longrightarrow> open (snd -` S)"
  by (simp add: snd_vimage_eq_Times open_Times)

lemma closed_vimage_fst: "closed S \<Longrightarrow> closed (fst -` S)"
  unfolding closed_open vimage_Compl [symmetric]
  by (rule open_vimage_fst)

lemma closed_vimage_snd: "closed S \<Longrightarrow> closed (snd -` S)"
  unfolding closed_open vimage_Compl [symmetric]
  by (rule open_vimage_snd)

lemma closed_Times: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<times> T)"
proof -
  have "S \<times> T = (fst -` S) \<inter> (snd -` T)"
    by auto
  then show "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<times> T)"
    by (simp add: closed_vimage_fst closed_vimage_snd closed_Int)
qed

lemma subset_fst_imageI: "A \<times> B \<subseteq> S \<Longrightarrow> y \<in> B \<Longrightarrow> A \<subseteq> fst ` S"
  unfolding image_def subset_eq by force

lemma subset_snd_imageI: "A \<times> B \<subseteq> S \<Longrightarrow> x \<in> A \<Longrightarrow> B \<subseteq> snd ` S"
  unfolding image_def subset_eq by force

lemma open_image_fst:
  assumes "open S"
  shows "open (fst ` S)"
proof (rule openI)
  fix x
  assume "x \<in> fst ` S"
  then obtain y where "(x, y) \<in> S"
    by auto
  then obtain A B where "open A" "open B" "x \<in> A" "y \<in> B" "A \<times> B \<subseteq> S"
    using \<open>open S\<close> unfolding open_prod_def by auto
  from \<open>A \<times> B \<subseteq> S\<close> \<open>y \<in> B\<close> have "A \<subseteq> fst ` S"
    by (rule subset_fst_imageI)
  with \<open>open A\<close> \<open>x \<in> A\<close> have "open A \<and> x \<in> A \<and> A \<subseteq> fst ` S"
    by simp
  then show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> fst ` S" ..
qed

lemma open_image_snd:
  assumes "open S"
  shows "open (snd ` S)"
proof (rule openI)
  fix y
  assume "y \<in> snd ` S"
  then obtain x where "(x, y) \<in> S"
    by auto
  then obtain A B where "open A" "open B" "x \<in> A" "y \<in> B" "A \<times> B \<subseteq> S"
    using \<open>open S\<close> unfolding open_prod_def by auto
  from \<open>A \<times> B \<subseteq> S\<close> \<open>x \<in> A\<close> have "B \<subseteq> snd ` S"
    by (rule subset_snd_imageI)
  with \<open>open B\<close> \<open>y \<in> B\<close> have "open B \<and> y \<in> B \<and> B \<subseteq> snd ` S"
    by simp
  then show "\<exists>T. open T \<and> y \<in> T \<and> T \<subseteq> snd ` S" ..
qed

lemma nhds_prod: "nhds (a, b) = nhds a \<times>\<^sub>F nhds b"
  unfolding nhds_def
proof (subst prod_filter_INF, auto intro!: antisym INF_greatest simp: principal_prod_principal)
  fix S T
  assume "open S" "a \<in> S" "open T" "b \<in> T"
  then show "(INF x \<in> {S. open S \<and> (a, b) \<in> S}. principal x) \<le> principal (S \<times> T)"
    by (intro INF_lower) (auto intro!: open_Times)
next
  fix S'
  assume "open S'" "(a, b) \<in> S'"
  then obtain S T where "open S" "a \<in> S" "open T" "b \<in> T" "S \<times> T \<subseteq> S'"
    by (auto elim: open_prod_elim)
  then show "(INF x \<in> {S. open S \<and> a \<in> S}. INF y \<in> {S. open S \<and> b \<in> S}.
      principal (x \<times> y)) \<le> principal S'"
    by (auto intro!: INF_lower2)
qed


subsubsection \<open>Continuity of operations\<close>

lemma tendsto_fst [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. fst (f x)) \<longlongrightarrow> fst a) F"
proof (rule topological_tendstoI)
  fix S
  assume "open S" and "fst a \<in> S"
  then have "open (fst -` S)" and "a \<in> fst -` S"
    by (simp_all add: open_vimage_fst)
  with assms have "eventually (\<lambda>x. f x \<in> fst -` S) F"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. fst (f x) \<in> S) F"
    by simp
qed

lemma tendsto_snd [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. snd (f x)) \<longlongrightarrow> snd a) F"
proof (rule topological_tendstoI)
  fix S
  assume "open S" and "snd a \<in> S"
  then have "open (snd -` S)" and "a \<in> snd -` S"
    by (simp_all add: open_vimage_snd)
  with assms have "eventually (\<lambda>x. f x \<in> snd -` S) F"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. snd (f x) \<in> S) F"
    by simp
qed

lemma tendsto_Pair [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. (f x, g x)) \<longlongrightarrow> (a, b)) F"
  unfolding nhds_prod using assms by (rule filterlim_Pair)

lemma continuous_fst[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. fst (f x))"
  unfolding continuous_def by (rule tendsto_fst)

lemma continuous_snd[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. snd (f x))"
  unfolding continuous_def by (rule tendsto_snd)

lemma continuous_Pair[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. (f x, g x))"
  unfolding continuous_def by (rule tendsto_Pair)

lemma continuous_on_fst[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. fst (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_fst)

lemma continuous_on_snd[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. snd (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_snd)

lemma continuous_on_Pair[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. (f x, g x))"
  unfolding continuous_on_def by (auto intro: tendsto_Pair)

lemma continuous_on_swap[continuous_intros]: "continuous_on A prod.swap"
  by (simp add: prod.swap_def continuous_on_fst continuous_on_snd
      continuous_on_Pair continuous_on_id)

lemma continuous_on_swap_args:
  assumes "continuous_on (A\<times>B) (\<lambda>(x,y). d x y)"
    shows "continuous_on (B\<times>A) (\<lambda>(x,y). d y x)"
proof -
  have "(\<lambda>(x,y). d y x) = (\<lambda>(x,y). d x y) \<circ> prod.swap"
    by force
  then show ?thesis
    by (metis assms continuous_on_compose continuous_on_swap product_swap)
qed

lemma isCont_fst [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. fst (f x)) a"
  by (fact continuous_fst)

lemma isCont_snd [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. snd (f x)) a"
  by (fact continuous_snd)

lemma isCont_Pair [simp]: "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. (f x, g x)) a"
  by (fact continuous_Pair)

lemma continuous_on_compose_Pair:
  assumes f: "continuous_on (Sigma A B) (\<lambda>(a, b). f a b)"
  assumes g: "continuous_on C g"
  assumes h: "continuous_on C h"
  assumes subset: "\<And>c. c \<in> C \<Longrightarrow> g c \<in> A" "\<And>c. c \<in> C \<Longrightarrow> h c \<in> B (g c)"
  shows "continuous_on C (\<lambda>c. f (g c) (h c))"
  using continuous_on_compose2[OF f continuous_on_Pair[OF g h]] subset
  by auto


subsubsection \<open>Connectedness of products\<close>

proposition connected_Times:
  assumes S: "connected S" and T: "connected T"
  shows "connected (S \<times> T)"
proof (rule connectedI_const)
  fix P::"'a \<times> 'b \<Rightarrow> bool"
  assume P[THEN continuous_on_compose2, continuous_intros]: "continuous_on (S \<times> T) P"
  have "continuous_on S (\<lambda>s. P (s, t))" if "t \<in> T" for t
    by (auto intro!: continuous_intros that)
  from connectedD_const[OF S this]
  obtain c1 where c1: "\<And>s t. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> P (s, t) = c1 t"
    by metis
  moreover
  have "continuous_on T (\<lambda>t. P (s, t))" if "s \<in> S" for s
    by (auto intro!: continuous_intros that)
  from connectedD_const[OF T this]
  obtain c2 where "\<And>s t. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> P (s, t) = c2 s"
    by metis
  ultimately show "\<exists>c. \<forall>s\<in>S \<times> T. P s = c"
    by auto
qed

corollary connected_Times_eq [simp]:
   "connected (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> connected S \<and> connected T"  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof cases
    assume "S \<noteq> {} \<and> T \<noteq> {}"
    moreover
    have "connected (fst ` (S \<times> T))" "connected (snd ` (S \<times> T))"
      using continuous_on_fst continuous_on_snd continuous_on_id
      by (blast intro: connected_continuous_image [OF _ L])+
    ultimately show ?thesis
      by auto
  qed auto
qed (auto simp: connected_Times)


subsubsection \<open>Separation axioms\<close>

instance prod :: (t0_space, t0_space) t0_space
proof
  fix x y :: "'a \<times> 'b"
  assume "x \<noteq> y"
  then have "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  then show "\<exists>U. open U \<and> (x \<in> U) \<noteq> (y \<in> U)"
    by (fast dest: t0_space elim: open_vimage_fst open_vimage_snd)
qed

instance prod :: (t1_space, t1_space) t1_space
proof
  fix x y :: "'a \<times> 'b"
  assume "x \<noteq> y"
  then have "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  then show "\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U"
    by (fast dest: t1_space elim: open_vimage_fst open_vimage_snd)
qed

instance prod :: (t2_space, t2_space) t2_space
proof
  fix x y :: "'a \<times> 'b"
  assume "x \<noteq> y"
  then have "fst x \<noteq> fst y \<or> snd x \<noteq> snd y"
    by (simp add: prod_eq_iff)
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (fast dest: hausdorff elim: open_vimage_fst open_vimage_snd)
qed

lemma isCont_swap[continuous_intros]: "isCont prod.swap a"
  using continuous_on_eq_continuous_within continuous_on_swap by blast

lemma open_diagonal_complement:
  "open {(x,y) |x y. x \<noteq> (y::('a::t2_space))}"
proof -
  have "open {(x, y). x \<noteq> (y::'a)}"
    unfolding split_def by (intro open_Collect_neq continuous_intros)
  also have "{(x, y). x \<noteq> (y::'a)} = {(x, y) |x y. x \<noteq> (y::'a)}"
    by auto
  finally show ?thesis .
qed

lemma closed_diagonal:
  "closed {y. \<exists> x::('a::t2_space). y = (x,x)}"
proof -
  have "{y. \<exists> x::'a. y = (x,x)} = UNIV - {(x,y) | x y. x \<noteq> y}" by auto
  then show ?thesis using open_diagonal_complement closed_Diff by auto
qed

lemma open_superdiagonal:
  "open {(x,y) | x y. x > (y::'a::{linorder_topology})}"
proof -
  have "open {(x, y). x > (y::'a)}"
    unfolding split_def by (intro open_Collect_less continuous_intros)
  also have "{(x, y). x > (y::'a)} = {(x, y) |x y. x > (y::'a)}"
    by auto
  finally show ?thesis .
qed

lemma closed_subdiagonal:
  "closed {(x,y) | x y. x \<le> (y::'a::{linorder_topology})}"
proof -
  have "{(x,y) | x y. x \<le> (y::'a)} = UNIV - {(x,y) | x y. x > (y::'a)}" by auto
  then show ?thesis using open_superdiagonal closed_Diff by auto
qed

lemma open_subdiagonal:
  "open {(x,y) | x y. x < (y::'a::{linorder_topology})}"
proof -
  have "open {(x, y). x < (y::'a)}"
    unfolding split_def by (intro open_Collect_less continuous_intros)
  also have "{(x, y). x < (y::'a)} = {(x, y) |x y. x < (y::'a)}"
    by auto
  finally show ?thesis .
qed

lemma closed_superdiagonal:
  "closed {(x,y) | x y. x \<ge> (y::('a::{linorder_topology}))}"
proof -
  have "{(x,y) | x y. x \<ge> (y::'a)} = UNIV - {(x,y) | x y. x < y}" by auto
  then show ?thesis using open_subdiagonal closed_Diff by auto
qed


end

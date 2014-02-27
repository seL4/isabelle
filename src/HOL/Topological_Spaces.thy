(*  Title:      HOL/Topological_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

header {* Topological Spaces *}

theory Topological_Spaces
imports Main Conditionally_Complete_Lattices
begin

subsection {* Topological space *}

class "open" =
  fixes "open" :: "'a set \<Rightarrow> bool"

class topological_space = "open" +
  assumes open_UNIV [simp, intro]: "open UNIV"
  assumes open_Int [intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)"
  assumes open_Union [intro]: "\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)"
begin

definition
  closed :: "'a set \<Rightarrow> bool" where
  "closed S \<longleftrightarrow> open (- S)"

lemma open_empty [intro, simp]: "open {}"
  using open_Union [of "{}"] by simp

lemma open_Un [intro]: "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<union> T)"
  using open_Union [of "{S, T}"] by simp

lemma open_UN [intro]: "\<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Union>x\<in>A. B x)"
  unfolding SUP_def by (rule open_Union) auto

lemma open_Inter [intro]: "finite S \<Longrightarrow> \<forall>T\<in>S. open T \<Longrightarrow> open (\<Inter>S)"
  by (induct set: finite) auto

lemma open_INT [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. open (B x) \<Longrightarrow> open (\<Inter>x\<in>A. B x)"
  unfolding INF_def by (rule open_Inter) auto

lemma openI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S"
  shows "open S"
proof -
  have "open (\<Union>{T. open T \<and> T \<subseteq> S})" by auto
  moreover have "\<Union>{T. open T \<and> T \<subseteq> S} = S" by (auto dest!: assms)
  ultimately show "open S" by simp
qed

lemma closed_empty [intro, simp]:  "closed {}"
  unfolding closed_def by simp

lemma closed_Un [intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<union> T)"
  unfolding closed_def by auto

lemma closed_UNIV [intro, simp]: "closed UNIV"
  unfolding closed_def by simp

lemma closed_Int [intro]: "closed S \<Longrightarrow> closed T \<Longrightarrow> closed (S \<inter> T)"
  unfolding closed_def by auto

lemma closed_INT [intro]: "\<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Inter>x\<in>A. B x)"
  unfolding closed_def by auto

lemma closed_Inter [intro]: "\<forall>S\<in>K. closed S \<Longrightarrow> closed (\<Inter> K)"
  unfolding closed_def uminus_Inf by auto

lemma closed_Union [intro]: "finite S \<Longrightarrow> \<forall>T\<in>S. closed T \<Longrightarrow> closed (\<Union>S)"
  by (induct set: finite) auto

lemma closed_UN [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. closed (B x) \<Longrightarrow> closed (\<Union>x\<in>A. B x)"
  unfolding SUP_def by (rule closed_Union) auto

lemma open_closed: "open S \<longleftrightarrow> closed (- S)"
  unfolding closed_def by simp

lemma closed_open: "closed S \<longleftrightarrow> open (- S)"
  unfolding closed_def by simp

lemma open_Diff [intro]: "open S \<Longrightarrow> closed T \<Longrightarrow> open (S - T)"
  unfolding closed_open Diff_eq by (rule open_Int)

lemma closed_Diff [intro]: "closed S \<Longrightarrow> open T \<Longrightarrow> closed (S - T)"
  unfolding open_closed Diff_eq by (rule closed_Int)

lemma open_Compl [intro]: "closed S \<Longrightarrow> open (- S)"
  unfolding closed_open .

lemma closed_Compl [intro]: "open S \<Longrightarrow> closed (- S)"
  unfolding open_closed .

end

subsection{* Hausdorff and other separation properties *}

class t0_space = topological_space +
  assumes t0_space: "x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> \<not> (x \<in> U \<longleftrightarrow> y \<in> U)"

class t1_space = topological_space +
  assumes t1_space: "x \<noteq> y \<Longrightarrow> \<exists>U. open U \<and> x \<in> U \<and> y \<notin> U"

instance t1_space \<subseteq> t0_space
proof qed (fast dest: t1_space)

lemma separation_t1:
  fixes x y :: "'a::t1_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U)"
  using t1_space[of x y] by blast

lemma closed_singleton:
  fixes a :: "'a::t1_space"
  shows "closed {a}"
proof -
  let ?T = "\<Union>{S. open S \<and> a \<notin> S}"
  have "open ?T" by (simp add: open_Union)
  also have "?T = - {a}"
    by (simp add: set_eq_iff separation_t1, auto)
  finally show "closed {a}" unfolding closed_def .
qed

lemma closed_insert [simp]:
  fixes a :: "'a::t1_space"
  assumes "closed S" shows "closed (insert a S)"
proof -
  from closed_singleton assms
  have "closed ({a} \<union> S)" by (rule closed_Un)
  thus "closed (insert a S)" by simp
qed

lemma finite_imp_closed:
  fixes S :: "'a::t1_space set"
  shows "finite S \<Longrightarrow> closed S"
by (induct set: finite, simp_all)

text {* T2 spaces are also known as Hausdorff spaces. *}

class t2_space = topological_space +
  assumes hausdorff: "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"

instance t2_space \<subseteq> t1_space
proof qed (fast dest: hausdorff)

lemma separation_t2:
  fixes x y :: "'a::t2_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {})"
  using hausdorff[of x y] by blast

lemma separation_t0:
  fixes x y :: "'a::t0_space"
  shows "x \<noteq> y \<longleftrightarrow> (\<exists>U. open U \<and> ~(x\<in>U \<longleftrightarrow> y\<in>U))"
  using t0_space[of x y] by blast

text {* A perfect space is a topological space with no isolated points. *}

class perfect_space = topological_space +
  assumes not_open_singleton: "\<not> open {x}"


subsection {* Generators for toplogies *}

inductive generate_topology for S where
  UNIV: "generate_topology S UNIV"
| Int: "generate_topology S a \<Longrightarrow> generate_topology S b \<Longrightarrow> generate_topology S (a \<inter> b)"
| UN: "(\<And>k. k \<in> K \<Longrightarrow> generate_topology S k) \<Longrightarrow> generate_topology S (\<Union>K)"
| Basis: "s \<in> S \<Longrightarrow> generate_topology S s"

hide_fact (open) UNIV Int UN Basis 

lemma generate_topology_Union: 
  "(\<And>k. k \<in> I \<Longrightarrow> generate_topology S (K k)) \<Longrightarrow> generate_topology S (\<Union>k\<in>I. K k)"
  unfolding SUP_def by (intro generate_topology.UN) auto

lemma topological_space_generate_topology:
  "class.topological_space (generate_topology S)"
  by default (auto intro: generate_topology.intros)

subsection {* Order topologies *}

class order_topology = order + "open" +
  assumes open_generated_order: "open = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"
begin

subclass topological_space
  unfolding open_generated_order
  by (rule topological_space_generate_topology)

lemma open_greaterThan [simp]: "open {a <..}"
  unfolding open_generated_order by (auto intro: generate_topology.Basis)

lemma open_lessThan [simp]: "open {..< a}"
  unfolding open_generated_order by (auto intro: generate_topology.Basis)

lemma open_greaterThanLessThan [simp]: "open {a <..< b}"
   unfolding greaterThanLessThan_eq by (simp add: open_Int)

end

class linorder_topology = linorder + order_topology

lemma closed_atMost [simp]: "closed {.. a::'a::linorder_topology}"
  by (simp add: closed_open)

lemma closed_atLeast [simp]: "closed {a::'a::linorder_topology ..}"
  by (simp add: closed_open)

lemma closed_atLeastAtMost [simp]: "closed {a::'a::linorder_topology .. b}"
proof -
  have "{a .. b} = {a ..} \<inter> {.. b}"
    by auto
  then show ?thesis
    by (simp add: closed_Int)
qed

lemma (in linorder) less_separate:
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
  with `x < y` have "x \<in> {..< y} \<and> y \<in> {x <..} \<and> {x <..} \<inter> {..< y} = {}"
    by auto
  then show ?thesis by blast
qed

instance linorder_topology \<subseteq> t2_space
proof
  fix x y :: 'a
  from less_separate[of x y] less_separate[of y x]
  show "x \<noteq> y \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (elim neqE) (metis open_lessThan open_greaterThan Int_commute)+
qed

lemma (in linorder_topology) open_right:
  assumes "open S" "x \<in> S" and gt_ex: "x < y" shows "\<exists>b>x. {x ..< b} \<subseteq> S"
  using assms unfolding open_generated_order
proof induction
  case (Int A B)
  then obtain a b where "a > x" "{x ..< a} \<subseteq> A"  "b > x" "{x ..< b} \<subseteq> B" by auto
  then show ?case by (auto intro!: exI[of _ "min a b"])
next
  case (Basis S) then show ?case by (fastforce intro: exI[of _ y] gt_ex)
qed blast+

lemma (in linorder_topology) open_left:
  assumes "open S" "x \<in> S" and lt_ex: "y < x" shows "\<exists>b<x. {b <.. x} \<subseteq> S"
  using assms unfolding open_generated_order
proof induction
  case (Int A B)
  then obtain a b where "a < x" "{a <.. x} \<subseteq> A"  "b < x" "{b <.. x} \<subseteq> B" by auto
  then show ?case by (auto intro!: exI[of _ "max a b"])
next
  case (Basis S) then show ?case by (fastforce intro: exI[of _ y] lt_ex)
qed blast+

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


subsubsection {* Eventually *}

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


subsubsection {* Finer-than relation *}

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
  { show "inf F F' \<le> F" and "inf F F' \<le> F'"
    unfolding le_filter_def eventually_inf by (auto intro: eventually_True) }
  { assume "F \<le> F'" and "F \<le> F''" thus "F \<le> inf F' F''"
    unfolding le_filter_def eventually_inf
    by (auto elim!: eventually_mono intro: eventually_conj) }
  { show "F \<le> sup F F'" and "F' \<le> sup F F'"
    unfolding le_filter_def eventually_sup by simp_all }
  { assume "F \<le> F''" and "F' \<le> F''" thus "sup F F' \<le> F''"
    unfolding le_filter_def eventually_sup by simp }
  { assume "F'' \<in> S" thus "Inf S \<le> F''"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
  { assume "\<And>F'. F' \<in> S \<Longrightarrow> F \<le> F'" thus "F \<le> Inf S"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
  { assume "F \<in> S" thus "F \<le> Sup S"
    unfolding le_filter_def eventually_Sup by simp }
  { assume "\<And>F. F \<in> S \<Longrightarrow> F \<le> F'" thus "Sup S \<le> F'"
    unfolding le_filter_def eventually_Sup by simp }
  { show "Inf {} = (top::'a filter)"
    by (auto simp: top_filter_def Inf_filter_def Sup_filter_def)
      (metis (full_types) top_filter_def always_eventually eventually_top) }
  { show "Sup {} = (bot::'a filter)"
    by (auto simp: bot_filter_def Sup_filter_def) }
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

lemma eventually_const: "\<not> trivial_limit net \<Longrightarrow> eventually (\<lambda>x. P) net \<longleftrightarrow> P"
  by (cases P) (simp_all add: eventually_False)


subsubsection {* Map function for filters *}

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

subsubsection {* Order filters *}

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

lemma eventually_at_top_dense: "eventually P at_top \<longleftrightarrow> (\<exists>N::'a::unbounded_dense_linorder. \<forall>n>N. P n)"
  unfolding eventually_at_top_linorder
proof safe
  fix N assume "\<forall>n\<ge>N. P n"
  then show "\<exists>N. \<forall>n>N. P n" by (auto intro!: exI[of _ N])
next
  fix N assume "\<forall>n>N. P n"
  moreover obtain y where "N < y" using gt_ex[of N] ..
  ultimately show "\<exists>N. \<forall>n\<ge>N. P n" by (auto intro!: exI[of _ y])
qed

lemma eventually_gt_at_top:
  "eventually (\<lambda>x. (c::_::unbounded_dense_linorder) < x) at_top"
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
  fixes P :: "'a::unbounded_dense_linorder \<Rightarrow> bool" shows "eventually P at_bot \<longleftrightarrow> (\<exists>N. \<forall>n<N. P n)"
  unfolding eventually_at_bot_linorder
proof safe
  fix N assume "\<forall>n\<le>N. P n" then show "\<exists>N. \<forall>n<N. P n" by (auto intro!: exI[of _ N])
next
  fix N assume "\<forall>n<N. P n" 
  moreover obtain y where "y < N" using lt_ex[of N] ..
  ultimately show "\<exists>N. \<forall>n\<le>N. P n" by (auto intro!: exI[of _ y])
qed

lemma eventually_gt_at_bot:
  "eventually (\<lambda>x. x < (c::_::unbounded_dense_linorder)) at_bot"
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

lemma eventually_sequentially_seg:
  "eventually (\<lambda>n. P (n + k)) sequentially \<longleftrightarrow> eventually P sequentially"
  unfolding eventually_sequentially
  apply safe
   apply (rule_tac x="N + k" in exI)
   apply rule
   apply (erule_tac x="n - k" in allE)
   apply auto []
  apply (rule_tac x=N in exI)
  apply auto []
  done

subsubsection {* Standard filters *}

definition principal :: "'a set \<Rightarrow> 'a filter" where
  "principal S = Abs_filter (\<lambda>P. \<forall>x\<in>S. P x)"

lemma eventually_principal: "eventually P (principal S) \<longleftrightarrow> (\<forall>x\<in>S. P x)"
  unfolding principal_def
  by (rule eventually_Abs_filter, rule is_filter.intro) auto

lemma eventually_inf_principal: "eventually P (inf F (principal s)) \<longleftrightarrow> eventually (\<lambda>x. x \<in> s \<longrightarrow> P x) F"
  unfolding eventually_inf eventually_principal by (auto elim: eventually_elim1)

lemma principal_UNIV[simp]: "principal UNIV = top"
  by (auto simp: filter_eq_iff eventually_principal)

lemma principal_empty[simp]: "principal {} = bot"
  by (auto simp: filter_eq_iff eventually_principal)

lemma principal_le_iff[iff]: "principal A \<le> principal B \<longleftrightarrow> A \<subseteq> B"
  by (auto simp: le_filter_def eventually_principal)

lemma le_principal: "F \<le> principal A \<longleftrightarrow> eventually (\<lambda>x. x \<in> A) F"
  unfolding le_filter_def eventually_principal
  apply safe
  apply (erule_tac x="\<lambda>x. x \<in> A" in allE)
  apply (auto elim: eventually_elim1)
  done

lemma principal_inject[iff]: "principal A = principal B \<longleftrightarrow> A = B"
  unfolding eq_iff by simp

lemma sup_principal[simp]: "sup (principal A) (principal B) = principal (A \<union> B)"
  unfolding filter_eq_iff eventually_sup eventually_principal by auto

lemma inf_principal[simp]: "inf (principal A) (principal B) = principal (A \<inter> B)"
  unfolding filter_eq_iff eventually_inf eventually_principal
  by (auto intro: exI[of _ "\<lambda>x. x \<in> A"] exI[of _ "\<lambda>x. x \<in> B"])

lemma SUP_principal[simp]: "(SUP i : I. principal (A i)) = principal (\<Union>i\<in>I. A i)"
  unfolding filter_eq_iff eventually_Sup SUP_def by (auto simp: eventually_principal)

lemma filtermap_principal[simp]: "filtermap f (principal A) = principal (f ` A)"
  unfolding filter_eq_iff eventually_filtermap eventually_principal by simp

subsubsection {* Topological filters *}

definition (in topological_space) nhds :: "'a \<Rightarrow> 'a filter"
  where "nhds a = Abs_filter (\<lambda>P. \<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P x))"

definition (in topological_space) at_within :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a filter" ("at (_) within (_)" [1000, 60] 60)
  where "at a within s = inf (nhds a) (principal (s - {a}))"

abbreviation (in topological_space) at :: "'a \<Rightarrow> 'a filter" ("at") where
  "at x \<equiv> at x within (CONST UNIV)"

abbreviation (in order_topology) at_right :: "'a \<Rightarrow> 'a filter" where
  "at_right x \<equiv> at x within {x <..}"

abbreviation (in order_topology) at_left :: "'a \<Rightarrow> 'a filter" where
  "at_left x \<equiv> at x within {..< x}"

lemma (in topological_space) eventually_nhds:
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

lemma nhds_neq_bot [simp]: "nhds a \<noteq> bot"
  unfolding trivial_limit_def eventually_nhds by simp

lemma eventually_at_filter:
  "eventually P (at a within s) \<longleftrightarrow> eventually (\<lambda>x. x \<noteq> a \<longrightarrow> x \<in> s \<longrightarrow> P x) (nhds a)"
  unfolding at_within_def eventually_inf_principal by (simp add: imp_conjL[symmetric] conj_commute)

lemma at_le: "s \<subseteq> t \<Longrightarrow> at x within s \<le> at x within t"
  unfolding at_within_def by (intro inf_mono) auto

lemma eventually_at_topological:
  "eventually P (at a within s) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> x \<in> s \<longrightarrow> P x))"
  unfolding eventually_nhds eventually_at_filter by simp

lemma at_within_open: "a \<in> S \<Longrightarrow> open S \<Longrightarrow> at a within S = at a"
  unfolding filter_eq_iff eventually_at_topological by (metis open_Int Int_iff UNIV_I)

lemma at_within_empty [simp]: "at a within {} = bot"
  unfolding at_within_def by simp

lemma at_within_union: "at x within (S \<union> T) = sup (at x within S) (at x within T)"
  unfolding filter_eq_iff eventually_sup eventually_at_filter
  by (auto elim!: eventually_rev_mp)

lemma at_eq_bot_iff: "at a = bot \<longleftrightarrow> open {a}"
  unfolding trivial_limit_def eventually_at_topological
  by (safe, case_tac "S = {a}", simp, fast, fast)

lemma at_neq_bot [simp]: "at (a::'a::perfect_space) \<noteq> bot"
  by (simp add: at_eq_bot_iff not_open_singleton)

lemma eventually_at_right:
  fixes x :: "'a :: {no_top, linorder_topology}"
  shows "eventually P (at_right x) \<longleftrightarrow> (\<exists>b. x < b \<and> (\<forall>z. x < z \<and> z < b \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  obtain y where "x < y" using gt_ex[of x] ..
  moreover fix S assume "open S" "x \<in> S" note open_right[OF this, of y]
  moreover note gt_ex[of x]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {x<..} \<longrightarrow> P s"
  ultimately show "\<exists>b>x. \<forall>z. x < z \<and> z < b \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "x < b" "\<forall>z. x < z \<and> z < b \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>xa\<in>S. xa \<noteq> x \<longrightarrow> xa \<in> {x<..} \<longrightarrow> P xa)"
    by (intro exI[of _ "{..< b}"]) auto
qed

lemma eventually_at_left:
  fixes x :: "'a :: {no_bot, linorder_topology}"
  shows "eventually P (at_left x) \<longleftrightarrow> (\<exists>b. x > b \<and> (\<forall>z. b < z \<and> z < x \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  obtain y where "y < x" using lt_ex[of x] ..
  moreover fix S assume "open S" "x \<in> S" note open_left[OF this, of y]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s"
  ultimately show "\<exists>b<x. \<forall>z. b < z \<and> z < x \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "b < x" "\<forall>z. b < z \<and> z < x \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s)"
    by (intro exI[of _ "{b <..}"]) auto
qed

lemma trivial_limit_at_left_real [simp]:
  "\<not> trivial_limit (at_left (x::'a::{no_bot, unbounded_dense_linorder, linorder_topology}))"
  unfolding trivial_limit_def eventually_at_left by (auto dest: dense)

lemma trivial_limit_at_right_real [simp]:
  "\<not> trivial_limit (at_right (x::'a::{no_top, unbounded_dense_linorder, linorder_topology}))"
  unfolding trivial_limit_def eventually_at_right by (auto dest: dense)

lemma at_eq_sup_left_right: "at (x::'a::linorder_topology) = sup (at_left x) (at_right x)"
  by (auto simp: eventually_at_filter filter_eq_iff eventually_sup 
           elim: eventually_elim2 eventually_elim1)

lemma eventually_at_split:
  "eventually P (at (x::'a::linorder_topology)) \<longleftrightarrow> eventually P (at_left x) \<and> eventually P (at_right x)"
  by (subst at_eq_sup_left_right) (simp add: eventually_sup)

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

lemma filterlim_principal:
  "(LIM x F. f x :> principal S) \<longleftrightarrow> (eventually (\<lambda>x. f x \<in> S) F)"
  unfolding filterlim_def eventually_filtermap le_principal ..

lemma filterlim_inf:
  "(LIM x F1. f x :> inf F2 F3) \<longleftrightarrow> ((LIM x F1. f x :> F2) \<and> (LIM x F1. f x :> F3))"
  unfolding filterlim_def by simp

lemma filterlim_filtermap: "filterlim f F1 (filtermap g F2) = filterlim (\<lambda>x. f (g x)) F1 F2"
  unfolding filterlim_def filtermap_filtermap ..

lemma filterlim_sup:
  "filterlim f F F1 \<Longrightarrow> filterlim f F F2 \<Longrightarrow> filterlim f F (sup F1 F2)"
  unfolding filterlim_def filtermap_sup by auto

lemma filterlim_Suc: "filterlim Suc sequentially sequentially"
  by (simp add: filterlim_iff eventually_sequentially) (metis le_Suc_eq)

subsubsection {* Tendsto *}

abbreviation (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" (infixr "--->" 55) where
  "(f ---> l) F \<equiv> filterlim f (nhds l) F"

definition (in t2_space) Lim :: "'f filter \<Rightarrow> ('f \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "Lim A f = (THE l. (f ---> l) A)"

lemma tendsto_eq_rhs: "(f ---> x) F \<Longrightarrow> x = y \<Longrightarrow> (f ---> y) F"
  by simp

ML {*

structure Tendsto_Intros = Named_Thms
(
  val name = @{binding tendsto_intros}
  val description = "introduction rules for tendsto"
)

*}

setup {*
  Tendsto_Intros.setup #>
  Global_Theory.add_thms_dynamic (@{binding tendsto_eq_intros},
    map_filter (try (fn thm => @{thm tendsto_eq_rhs} OF [thm])) o Tendsto_Intros.get o Context.proof_of);
*}

lemma (in topological_space) tendsto_def:
   "(f ---> l) F \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) F)"
  unfolding filterlim_def
proof safe
  fix S assume "open S" "l \<in> S" "filtermap f F \<le> nhds l"
  then show "eventually (\<lambda>x. f x \<in> S) F"
    unfolding eventually_nhds eventually_filtermap le_filter_def
    by (auto elim!: allE[of _ "\<lambda>x. x \<in> S"] eventually_rev_mp)
qed (auto elim!: eventually_rev_mp simp: eventually_nhds eventually_filtermap le_filter_def)

lemma tendsto_mono: "F \<le> F' \<Longrightarrow> (f ---> l) F' \<Longrightarrow> (f ---> l) F"
  unfolding tendsto_def le_filter_def by fast

lemma tendsto_within_subset: "(f ---> l) (at x within S) \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (f ---> l) (at x within T)"
  by (blast intro: tendsto_mono at_le)

lemma filterlim_at:
  "(LIM x F. f x :> at b within s) \<longleftrightarrow> (eventually (\<lambda>x. f x \<in> s \<and> f x \<noteq> b) F \<and> (f ---> b) F)"
  by (simp add: at_within_def filterlim_inf filterlim_principal conj_commute)

lemma (in topological_space) topological_tendstoI:
  "(\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F) \<Longrightarrow> (f ---> l) F"
  unfolding tendsto_def by auto

lemma (in topological_space) topological_tendstoD:
  "(f ---> l) F \<Longrightarrow> open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) F"
  unfolding tendsto_def by auto

lemma order_tendstoI:
  fixes y :: "_ :: order_topology"
  assumes "\<And>a. a < y \<Longrightarrow> eventually (\<lambda>x. a < f x) F"
  assumes "\<And>a. y < a \<Longrightarrow> eventually (\<lambda>x. f x < a) F"
  shows "(f ---> y) F"
proof (rule topological_tendstoI)
  fix S assume "open S" "y \<in> S"
  then show "eventually (\<lambda>x. f x \<in> S) F"
    unfolding open_generated_order
  proof induct
    case (UN K)
    then obtain k where "y \<in> k" "k \<in> K" by auto
    with UN(2)[of k] show ?case
      by (auto elim: eventually_elim1)
  qed (insert assms, auto elim: eventually_elim2)
qed

lemma order_tendstoD:
  fixes y :: "_ :: order_topology"
  assumes y: "(f ---> y) F"
  shows "a < y \<Longrightarrow> eventually (\<lambda>x. a < f x) F"
    and "y < a \<Longrightarrow> eventually (\<lambda>x. f x < a) F"
  using topological_tendstoD[OF y, of "{..< a}"] topological_tendstoD[OF y, of "{a <..}"] by auto

lemma order_tendsto_iff: 
  fixes f :: "_ \<Rightarrow> 'a :: order_topology"
  shows "(f ---> x) F \<longleftrightarrow>(\<forall>l<x. eventually (\<lambda>x. l < f x) F) \<and> (\<forall>u>x. eventually (\<lambda>x. f x < u) F)"
  by (metis order_tendstoI order_tendstoD)

lemma tendsto_bot [simp]: "(f ---> a) bot"
  unfolding tendsto_def by simp

lemma tendsto_ident_at [tendsto_intros]: "((\<lambda>x. x) ---> a) (at a within s)"
  unfolding tendsto_def eventually_at_topological by auto

lemma (in topological_space) tendsto_const [tendsto_intros]: "((\<lambda>x. k) ---> k) F"
  by (simp add: tendsto_def)

lemma (in t2_space) tendsto_unique:
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

lemma (in t2_space) tendsto_const_iff:
  assumes "\<not> trivial_limit F" shows "((\<lambda>x. a :: 'a) ---> b) F \<longleftrightarrow> a = b"
  by (safe intro!: tendsto_const tendsto_unique [OF assms tendsto_const])

lemma increasing_tendsto:
  fixes f :: "_ \<Rightarrow> 'a::order_topology"
  assumes bdd: "eventually (\<lambda>n. f n \<le> l) F"
      and en: "\<And>x. x < l \<Longrightarrow> eventually (\<lambda>n. x < f n) F"
  shows "(f ---> l) F"
  using assms by (intro order_tendstoI) (auto elim!: eventually_elim1)

lemma decreasing_tendsto:
  fixes f :: "_ \<Rightarrow> 'a::order_topology"
  assumes bdd: "eventually (\<lambda>n. l \<le> f n) F"
      and en: "\<And>x. l < x \<Longrightarrow> eventually (\<lambda>n. f n < x) F"
  shows "(f ---> l) F"
  using assms by (intro order_tendstoI) (auto elim!: eventually_elim1)

lemma tendsto_sandwich:
  fixes f g h :: "'a \<Rightarrow> 'b::order_topology"
  assumes ev: "eventually (\<lambda>n. f n \<le> g n) net" "eventually (\<lambda>n. g n \<le> h n) net"
  assumes lim: "(f ---> c) net" "(h ---> c) net"
  shows "(g ---> c) net"
proof (rule order_tendstoI)
  fix a show "a < c \<Longrightarrow> eventually (\<lambda>x. a < g x) net"
    using order_tendstoD[OF lim(1), of a] ev by (auto elim: eventually_elim2)
next
  fix a show "c < a \<Longrightarrow> eventually (\<lambda>x. g x < a) net"
    using order_tendstoD[OF lim(2), of a] ev by (auto elim: eventually_elim2)
qed

lemma tendsto_le:
  fixes f g :: "'a \<Rightarrow> 'b::linorder_topology"
  assumes F: "\<not> trivial_limit F"
  assumes x: "(f ---> x) F" and y: "(g ---> y) F"
  assumes ev: "eventually (\<lambda>x. g x \<le> f x) F"
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

lemma tendsto_le_const:
  fixes f :: "'a \<Rightarrow> 'b::linorder_topology"
  assumes F: "\<not> trivial_limit F"
  assumes x: "(f ---> x) F" and a: "eventually (\<lambda>x. a \<le> f x) F"
  shows "a \<le> x"
  using F x tendsto_const a by (rule tendsto_le)

subsubsection {* Rules about @{const Lim} *}

lemma (in t2_space) tendsto_Lim:
  "\<not>(trivial_limit net) \<Longrightarrow> (f ---> l) net \<Longrightarrow> Lim net f = l"
  unfolding Lim_def using tendsto_unique[of net f] by auto

lemma Lim_ident_at: "\<not> trivial_limit (at x within s) \<Longrightarrow> Lim (at x within s) (\<lambda>x. x) = x"
  by (rule tendsto_Lim[OF _ tendsto_ident_at]) auto

subsection {* Limits to @{const at_top} and @{const at_bot} *}

lemma filterlim_at_top:
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. Z \<le> f x) F)"
  by (auto simp: filterlim_iff eventually_at_top_linorder elim!: eventually_elim1)

lemma filterlim_at_top_dense:
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)"
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
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)" and c :: "'b"
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
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z<c. eventually (\<lambda>x. Z \<ge> f x) F)"
  by (metis filterlim_at_bot filterlim_at_bot_le lt_ex order_le_less_trans)

lemma filterlim_at_bot_at_right:
  fixes f :: "'a::{no_top, linorder_topology} \<Rightarrow> 'b::linorder"
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
      unfolding eventually_at_right by (auto intro!: exI[of _ "g z"])
    with Q show "eventually (\<lambda>x. f x \<le> z) (at_right a)"
      by eventually_elim (metis bij `P z` mono)
  qed
qed

lemma filterlim_at_top_at_left:
  fixes f :: "'a::{no_bot, linorder_topology} \<Rightarrow> 'b::linorder"
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
      unfolding eventually_at_left by (auto intro!: exI[of _ "g z"])
    with Q show "eventually (\<lambda>x. z \<le> f x) (at_left a)"
      by eventually_elim (metis bij `P z` mono)
  qed
qed

lemma filterlim_split_at:
  "filterlim f F (at_left x) \<Longrightarrow> filterlim f F (at_right x) \<Longrightarrow> filterlim f F (at (x::'a::linorder_topology))"
  by (subst at_eq_sup_left_right) (rule filterlim_sup)

lemma filterlim_at_split:
  "filterlim f F (at (x::'a::linorder_topology)) \<longleftrightarrow> filterlim f F (at_left x) \<and> filterlim f F (at_right x)"
  by (subst at_eq_sup_left_right) (simp add: filterlim_def filtermap_sup)


subsection {* Limits on sequences *}

abbreviation (in topological_space)
  LIMSEQ :: "[nat \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
    ("((_)/ ----> (_))" [60, 60] 60) where
  "X ----> L \<equiv> (X ---> L) sequentially"

abbreviation (in t2_space) lim :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "lim X \<equiv> Lim sequentially X"

definition (in topological_space) convergent :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "convergent X = (\<exists>L. X ----> L)"

lemma lim_def: "lim X = (THE L. X ----> L)"
  unfolding Lim_def ..

subsubsection {* Monotone sequences and subsequences *}

definition
  monoseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool" where
    --{*Definition of monotonicity.
        The use of disjunction here complicates proofs considerably.
        One alternative is to add a Boolean argument to indicate the direction.
        Another is to develop the notions of increasing and decreasing first.*}
  "monoseq X = ((\<forall>m. \<forall>n\<ge>m. X m \<le> X n) | (\<forall>m. \<forall>n\<ge>m. X n \<le> X m))"

definition
  incseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool" where
    --{*Increasing sequence*}
  "incseq X \<longleftrightarrow> (\<forall>m. \<forall>n\<ge>m. X m \<le> X n)"

definition
  decseq :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool" where
    --{*Decreasing sequence*}
  "decseq X \<longleftrightarrow> (\<forall>m. \<forall>n\<ge>m. X n \<le> X m)"

definition
  subseq :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
    --{*Definition of subsequence*}
  "subseq f \<longleftrightarrow> (\<forall>m. \<forall>n>m. f m < f n)"

lemma incseq_mono: "mono f \<longleftrightarrow> incseq f"
  unfolding mono_def incseq_def by auto

lemma incseq_SucI:
  "(\<And>n. X n \<le> X (Suc n)) \<Longrightarrow> incseq X"
  using lift_Suc_mono_le[of X]
  by (auto simp: incseq_def)

lemma incseqD: "\<And>i j. incseq f \<Longrightarrow> i \<le> j \<Longrightarrow> f i \<le> f j"
  by (auto simp: incseq_def)

lemma incseq_SucD: "incseq A \<Longrightarrow> A i \<le> A (Suc i)"
  using incseqD[of A i "Suc i"] by auto

lemma incseq_Suc_iff: "incseq f \<longleftrightarrow> (\<forall>n. f n \<le> f (Suc n))"
  by (auto intro: incseq_SucI dest: incseq_SucD)

lemma incseq_const[simp, intro]: "incseq (\<lambda>x. k)"
  unfolding incseq_def by auto

lemma decseq_SucI:
  "(\<And>n. X (Suc n) \<le> X n) \<Longrightarrow> decseq X"
  using order.lift_Suc_mono_le[OF dual_order, of X]
  by (auto simp: decseq_def)

lemma decseqD: "\<And>i j. decseq f \<Longrightarrow> i \<le> j \<Longrightarrow> f j \<le> f i"
  by (auto simp: decseq_def)

lemma decseq_SucD: "decseq A \<Longrightarrow> A (Suc i) \<le> A i"
  using decseqD[of A i "Suc i"] by auto

lemma decseq_Suc_iff: "decseq f \<longleftrightarrow> (\<forall>n. f (Suc n) \<le> f n)"
  by (auto intro: decseq_SucI dest: decseq_SucD)

lemma decseq_const[simp, intro]: "decseq (\<lambda>x. k)"
  unfolding decseq_def by auto

lemma monoseq_iff: "monoseq X \<longleftrightarrow> incseq X \<or> decseq X"
  unfolding monoseq_def incseq_def decseq_def ..

lemma monoseq_Suc:
  "monoseq X \<longleftrightarrow> (\<forall>n. X n \<le> X (Suc n)) \<or> (\<forall>n. X (Suc n) \<le> X n)"
  unfolding monoseq_iff incseq_Suc_iff decseq_Suc_iff ..

lemma monoI1: "\<forall>m. \<forall> n \<ge> m. X m \<le> X n ==> monoseq X"
by (simp add: monoseq_def)

lemma monoI2: "\<forall>m. \<forall> n \<ge> m. X n \<le> X m ==> monoseq X"
by (simp add: monoseq_def)

lemma mono_SucI1: "\<forall>n. X n \<le> X (Suc n) ==> monoseq X"
by (simp add: monoseq_Suc)

lemma mono_SucI2: "\<forall>n. X (Suc n) \<le> X n ==> monoseq X"
by (simp add: monoseq_Suc)

lemma monoseq_minus:
  fixes a :: "nat \<Rightarrow> 'a::ordered_ab_group_add"
  assumes "monoseq a"
  shows "monoseq (\<lambda> n. - a n)"
proof (cases "\<forall> m. \<forall> n \<ge> m. a m \<le> a n")
  case True
  hence "\<forall> m. \<forall> n \<ge> m. - a n \<le> - a m" by auto
  thus ?thesis by (rule monoI2)
next
  case False
  hence "\<forall> m. \<forall> n \<ge> m. - a m \<le> - a n" using `monoseq a`[unfolded monoseq_def] by auto
  thus ?thesis by (rule monoI1)
qed

text{*Subsequence (alternative definition, (e.g. Hoskins)*}

lemma subseq_Suc_iff: "subseq f = (\<forall>n. (f n) < (f (Suc n)))"
apply (simp add: subseq_def)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k)
apply (auto intro: less_trans)
done

text{* for any sequence, there is a monotonic subsequence *}
lemma seq_monosub:
  fixes s :: "nat => 'a::linorder"
  shows "\<exists>f. subseq f \<and> monoseq (\<lambda> n. (s (f n)))"
proof cases
  let "?P p n" = "p > n \<and> (\<forall>m\<ge>p. s m \<le> s p)"
  assume *: "\<forall>n. \<exists>p. ?P p n"
  def f \<equiv> "rec_nat (SOME p. ?P p 0) (\<lambda>_ n. SOME p. ?P p n)"
  have f_0: "f 0 = (SOME p. ?P p 0)" unfolding f_def by simp
  have f_Suc: "\<And>i. f (Suc i) = (SOME p. ?P p (f i))" unfolding f_def nat.rec(2) ..
  have P_0: "?P (f 0) 0" unfolding f_0 using *[rule_format] by (rule someI2_ex) auto
  have P_Suc: "\<And>i. ?P (f (Suc i)) (f i)" unfolding f_Suc using *[rule_format] by (rule someI2_ex) auto
  then have "subseq f" unfolding subseq_Suc_iff by auto
  moreover have "monoseq (\<lambda>n. s (f n))" unfolding monoseq_Suc
  proof (intro disjI2 allI)
    fix n show "s (f (Suc n)) \<le> s (f n)"
    proof (cases n)
      case 0 with P_Suc[of 0] P_0 show ?thesis by auto
    next
      case (Suc m)
      from P_Suc[of n] Suc have "f (Suc m) \<le> f (Suc (Suc m))" by simp
      with P_Suc Suc show ?thesis by simp
    qed
  qed
  ultimately show ?thesis by auto
next
  let "?P p m" = "m < p \<and> s m < s p"
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. s m \<le> s p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. s p < s m" by (force simp: not_le le_less)
  def f \<equiv> "rec_nat (SOME p. ?P p (Suc N)) (\<lambda>_ n. SOME p. ?P p n)"
  have f_0: "f 0 = (SOME p. ?P p (Suc N))" unfolding f_def by simp
  have f_Suc: "\<And>i. f (Suc i) = (SOME p. ?P p (f i))" unfolding f_def nat.rec(2) ..
  have P_0: "?P (f 0) (Suc N)"
    unfolding f_0 some_eq_ex[of "\<lambda>p. ?P p (Suc N)"] using N[of "Suc N"] by auto
  { fix i have "N < f i \<Longrightarrow> ?P (f (Suc i)) (f i)"
      unfolding f_Suc some_eq_ex[of "\<lambda>p. ?P p (f i)"] using N[of "f i"] . }
  note P' = this
  { fix i have "N < f i \<and> ?P (f (Suc i)) (f i)"
      by (induct i) (insert P_0 P', auto) }
  then have "subseq f" "monoseq (\<lambda>x. s (f x))"
    unfolding subseq_Suc_iff monoseq_Suc by (auto simp: not_le intro: less_imp_le)
  then show ?thesis by auto
qed

lemma seq_suble: assumes sf: "subseq f" shows "n \<le> f n"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  from sf[unfolded subseq_Suc_iff, rule_format, of n] Suc.hyps
  have "n < f (Suc n)" by arith
  thus ?case by arith
qed

lemma eventually_subseq:
  "subseq r \<Longrightarrow> eventually P sequentially \<Longrightarrow> eventually (\<lambda>n. P (r n)) sequentially"
  unfolding eventually_sequentially by (metis seq_suble le_trans)

lemma not_eventually_sequentiallyD:
  assumes P: "\<not> eventually P sequentially"
  shows "\<exists>r. subseq r \<and> (\<forall>n. \<not> P (r n))"
proof -
  from P have "\<forall>n. \<exists>m\<ge>n. \<not> P m"
    unfolding eventually_sequentially by (simp add: not_less)
  then obtain r where "\<And>n. r n \<ge> n" "\<And>n. \<not> P (r n)"
    by (auto simp: choice_iff)
  then show ?thesis
    by (auto intro!: exI[of _ "\<lambda>n. r (((Suc \<circ> r) ^^ Suc n) 0)"]
             simp: less_eq_Suc_le subseq_Suc_iff)
qed

lemma filterlim_subseq: "subseq f \<Longrightarrow> filterlim f sequentially sequentially"
  unfolding filterlim_iff by (metis eventually_subseq)

lemma subseq_o: "subseq r \<Longrightarrow> subseq s \<Longrightarrow> subseq (r \<circ> s)"
  unfolding subseq_def by simp

lemma subseq_mono: assumes "subseq r" "m < n" shows "r m < r n"
  using assms by (auto simp: subseq_def)

lemma incseq_imp_monoseq:  "incseq X \<Longrightarrow> monoseq X"
  by (simp add: incseq_def monoseq_def)

lemma decseq_imp_monoseq:  "decseq X \<Longrightarrow> monoseq X"
  by (simp add: decseq_def monoseq_def)

lemma decseq_eq_incseq:
  fixes X :: "nat \<Rightarrow> 'a::ordered_ab_group_add" shows "decseq X = incseq (\<lambda>n. - X n)" 
  by (simp add: decseq_def incseq_def)

lemma INT_decseq_offset:
  assumes "decseq F"
  shows "(\<Inter>i. F i) = (\<Inter>i\<in>{n..}. F i)"
proof safe
  fix x i assume x: "x \<in> (\<Inter>i\<in>{n..}. F i)"
  show "x \<in> F i"
  proof cases
    from x have "x \<in> F n" by auto
    also assume "i \<le> n" with `decseq F` have "F n \<subseteq> F i"
      unfolding decseq_def by simp
    finally show ?thesis .
  qed (insert x, simp)
qed auto

lemma LIMSEQ_const_iff:
  fixes k l :: "'a::t2_space"
  shows "(\<lambda>n. k) ----> l \<longleftrightarrow> k = l"
  using trivial_limit_sequentially by (rule tendsto_const_iff)

lemma LIMSEQ_SUP:
  "incseq X \<Longrightarrow> X ----> (SUP i. X i :: 'a :: {complete_linorder, linorder_topology})"
  by (intro increasing_tendsto)
     (auto simp: SUP_upper less_SUP_iff incseq_def eventually_sequentially intro: less_le_trans)

lemma LIMSEQ_INF:
  "decseq X \<Longrightarrow> X ----> (INF i. X i :: 'a :: {complete_linorder, linorder_topology})"
  by (intro decreasing_tendsto)
     (auto simp: INF_lower INF_less_iff decseq_def eventually_sequentially intro: le_less_trans)

lemma LIMSEQ_ignore_initial_segment:
  "f ----> a \<Longrightarrow> (\<lambda>n. f (n + k)) ----> a"
  unfolding tendsto_def
  by (subst eventually_sequentially_seg[where k=k])

lemma LIMSEQ_offset:
  "(\<lambda>n. f (n + k)) ----> a \<Longrightarrow> f ----> a"
  unfolding tendsto_def
  by (subst (asm) eventually_sequentially_seg[where k=k])

lemma LIMSEQ_Suc: "f ----> l \<Longrightarrow> (\<lambda>n. f (Suc n)) ----> l"
by (drule_tac k="Suc 0" in LIMSEQ_ignore_initial_segment, simp)

lemma LIMSEQ_imp_Suc: "(\<lambda>n. f (Suc n)) ----> l \<Longrightarrow> f ----> l"
by (rule_tac k="Suc 0" in LIMSEQ_offset, simp)

lemma LIMSEQ_Suc_iff: "(\<lambda>n. f (Suc n)) ----> l = f ----> l"
by (blast intro: LIMSEQ_imp_Suc LIMSEQ_Suc)

lemma LIMSEQ_unique:
  fixes a b :: "'a::t2_space"
  shows "\<lbrakk>X ----> a; X ----> b\<rbrakk> \<Longrightarrow> a = b"
  using trivial_limit_sequentially by (rule tendsto_unique)

lemma LIMSEQ_le_const:
  "\<lbrakk>X ----> (x::'a::linorder_topology); \<exists>N. \<forall>n\<ge>N. a \<le> X n\<rbrakk> \<Longrightarrow> a \<le> x"
  using tendsto_le_const[of sequentially X x a] by (simp add: eventually_sequentially)

lemma LIMSEQ_le:
  "\<lbrakk>X ----> x; Y ----> y; \<exists>N. \<forall>n\<ge>N. X n \<le> Y n\<rbrakk> \<Longrightarrow> x \<le> (y::'a::linorder_topology)"
  using tendsto_le[of sequentially Y y X x] by (simp add: eventually_sequentially)

lemma LIMSEQ_le_const2:
  "\<lbrakk>X ----> (x::'a::linorder_topology); \<exists>N. \<forall>n\<ge>N. X n \<le> a\<rbrakk> \<Longrightarrow> x \<le> a"
  by (rule LIMSEQ_le[of X x "\<lambda>n. a"]) (auto simp: tendsto_const)

lemma convergentD: "convergent X ==> \<exists>L. (X ----> L)"
by (simp add: convergent_def)

lemma convergentI: "(X ----> L) ==> convergent X"
by (auto simp add: convergent_def)

lemma convergent_LIMSEQ_iff: "convergent X = (X ----> lim X)"
by (auto intro: theI LIMSEQ_unique simp add: convergent_def lim_def)

lemma convergent_const: "convergent (\<lambda>n. c)"
  by (rule convergentI, rule tendsto_const)

lemma monoseq_le:
  "monoseq a \<Longrightarrow> a ----> (x::'a::linorder_topology) \<Longrightarrow>
    ((\<forall> n. a n \<le> x) \<and> (\<forall>m. \<forall>n\<ge>m. a m \<le> a n)) \<or> ((\<forall> n. x \<le> a n) \<and> (\<forall>m. \<forall>n\<ge>m. a n \<le> a m))"
  by (metis LIMSEQ_le_const LIMSEQ_le_const2 decseq_def incseq_def monoseq_iff)

lemma LIMSEQ_subseq_LIMSEQ:
  "\<lbrakk> X ----> L; subseq f \<rbrakk> \<Longrightarrow> (X o f) ----> L"
  unfolding comp_def by (rule filterlim_compose[of X, OF _ filterlim_subseq])

lemma convergent_subseq_convergent:
  "\<lbrakk>convergent X; subseq f\<rbrakk> \<Longrightarrow> convergent (X o f)"
  unfolding convergent_def by (auto intro: LIMSEQ_subseq_LIMSEQ)

lemma limI: "X ----> L ==> lim X = L"
apply (simp add: lim_def)
apply (blast intro: LIMSEQ_unique)
done

lemma lim_le: "convergent f \<Longrightarrow> (\<And>n. f n \<le> (x::'a::linorder_topology)) \<Longrightarrow> lim f \<le> x"
  using LIMSEQ_le_const2[of f "lim f" x] by (simp add: convergent_LIMSEQ_iff)

subsubsection{*Increasing and Decreasing Series*}

lemma incseq_le: "incseq X \<Longrightarrow> X ----> L \<Longrightarrow> X n \<le> (L::'a::linorder_topology)"
  by (metis incseq_def LIMSEQ_le_const)

lemma decseq_le: "decseq X \<Longrightarrow> X ----> L \<Longrightarrow> (L::'a::linorder_topology) \<le> X n"
  by (metis decseq_def LIMSEQ_le_const2)

subsection {* First countable topologies *}

class first_countable_topology = topological_space +
  assumes first_countable_basis:
    "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"

lemma (in first_countable_topology) countable_basis_at_decseq:
  obtains A :: "nat \<Rightarrow> 'a set" where
    "\<And>i. open (A i)" "\<And>i. x \<in> (A i)"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
proof atomize_elim
  from first_countable_basis[of x] obtain A :: "nat \<Rightarrow> 'a set" where
    nhds: "\<And>i. open (A i)" "\<And>i. x \<in> A i"
    and incl: "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>i. A i \<subseteq> S"  by auto
  def F \<equiv> "\<lambda>n. \<Inter>i\<le>n. A i"
  show "\<exists>A. (\<forall>i. open (A i)) \<and> (\<forall>i. x \<in> A i) \<and>
      (\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially)"
  proof (safe intro!: exI[of _ F])
    fix i
    show "open (F i)" using nhds(1) by (auto simp: F_def)
    show "x \<in> F i" using nhds(2) by (auto simp: F_def)
  next
    fix S assume "open S" "x \<in> S"
    from incl[OF this] obtain i where "F i \<subseteq> S" unfolding F_def by auto
    moreover have "\<And>j. i \<le> j \<Longrightarrow> F j \<subseteq> F i"
      by (auto simp: F_def)
    ultimately show "eventually (\<lambda>i. F i \<subseteq> S) sequentially"
      by (auto simp: eventually_sequentially)
  qed
qed

lemma (in first_countable_topology) countable_basis:
  obtains A :: "nat \<Rightarrow> 'a set" where
    "\<And>i. open (A i)" "\<And>i. x \<in> A i"
    "\<And>F. (\<forall>n. F n \<in> A n) \<Longrightarrow> F ----> x"
proof atomize_elim
  obtain A :: "nat \<Rightarrow> 'a set" where A:
    "\<And>i. open (A i)"
    "\<And>i. x \<in> A i"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by (rule countable_basis_at_decseq) blast
  {
    fix F S assume "\<forall>n. F n \<in> A n" "open S" "x \<in> S"
    with A(3)[of S] have "eventually (\<lambda>n. F n \<in> S) sequentially"
      by (auto elim: eventually_elim1 simp: subset_eq)
  }
  with A show "\<exists>A. (\<forall>i. open (A i)) \<and> (\<forall>i. x \<in> A i) \<and> (\<forall>F. (\<forall>n. F n \<in> A n) \<longrightarrow> F ----> x)"
    by (intro exI[of _ A]) (auto simp: tendsto_def)
qed

lemma (in first_countable_topology) sequentially_imp_eventually_nhds_within:
  assumes "\<forall>f. (\<forall>n. f n \<in> s) \<and> f ----> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (inf (nhds a) (principal s))"
proof (rule ccontr)
  obtain A :: "nat \<Rightarrow> 'a set" where A:
    "\<And>i. open (A i)"
    "\<And>i. a \<in> A i"
    "\<And>F. \<forall>n. F n \<in> A n \<Longrightarrow> F ----> a"
    by (rule countable_basis) blast
  assume "\<not> ?thesis"
  with A have P: "\<exists>F. \<forall>n. F n \<in> s \<and> F n \<in> A n \<and> \<not> P (F n)"
    unfolding eventually_inf_principal eventually_nhds by (intro choice) fastforce
  then obtain F where F0: "\<forall>n. F n \<in> s" and F2: "\<forall>n. F n \<in> A n" and F3: "\<forall>n. \<not> P (F n)"
    by blast
  with A have "F ----> a" by auto
  hence "eventually (\<lambda>n. P (F n)) sequentially"
    using assms F0 by simp
  thus "False" by (simp add: F3)
qed

lemma (in first_countable_topology) eventually_nhds_within_iff_sequentially:
  "eventually P (inf (nhds a) (principal s)) \<longleftrightarrow> 
    (\<forall>f. (\<forall>n. f n \<in> s) \<and> f ----> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially)"
proof (safe intro!: sequentially_imp_eventually_nhds_within)
  assume "eventually P (inf (nhds a) (principal s))" 
  then obtain S where "open S" "a \<in> S" "\<forall>x\<in>S. x \<in> s \<longrightarrow> P x"
    by (auto simp: eventually_inf_principal eventually_nhds)
  moreover fix f assume "\<forall>n. f n \<in> s" "f ----> a"
  ultimately show "eventually (\<lambda>n. P (f n)) sequentially"
    by (auto dest!: topological_tendstoD elim: eventually_elim1)
qed

lemma (in first_countable_topology) eventually_nhds_iff_sequentially:
  "eventually P (nhds a) \<longleftrightarrow> (\<forall>f. f ----> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially)"
  using eventually_nhds_within_iff_sequentially[of P a UNIV] by simp

subsection {* Function limit at a point *}

abbreviation
  LIM :: "('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
        ("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60) where
  "f -- a --> L \<equiv> (f ---> L) (at a)"

lemma tendsto_within_open: "a \<in> S \<Longrightarrow> open S \<Longrightarrow> (f ---> l) (at a within S) \<longleftrightarrow> (f -- a --> l)"
  unfolding tendsto_def by (simp add: at_within_open[where S=S])

lemma LIM_const_not_eq[tendsto_intros]:
  fixes a :: "'a::perfect_space"
  fixes k L :: "'b::t2_space"
  shows "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) -- a --> L"
  by (simp add: tendsto_const_iff)

lemmas LIM_not_zero = LIM_const_not_eq [where L = 0]

lemma LIM_const_eq:
  fixes a :: "'a::perfect_space"
  fixes k L :: "'b::t2_space"
  shows "(\<lambda>x. k) -- a --> L \<Longrightarrow> k = L"
  by (simp add: tendsto_const_iff)

lemma LIM_unique:
  fixes a :: "'a::perfect_space" and L M :: "'b::t2_space"
  shows "f -- a --> L \<Longrightarrow> f -- a --> M \<Longrightarrow> L = M"
  using at_neq_bot by (rule tendsto_unique)

text {* Limits are equal for functions equal except at limit point *}

lemma LIM_equal: "\<forall>x. x \<noteq> a --> (f x = g x) \<Longrightarrow> (f -- a --> l) \<longleftrightarrow> (g -- a --> l)"
  unfolding tendsto_def eventually_at_topological by simp

lemma LIM_cong: "a = b \<Longrightarrow> (\<And>x. x \<noteq> b \<Longrightarrow> f x = g x) \<Longrightarrow> l = m \<Longrightarrow> (f -- a --> l) \<longleftrightarrow> (g -- b --> m)"
  by (simp add: LIM_equal)

lemma LIM_cong_limit: "f -- x --> L \<Longrightarrow> K = L \<Longrightarrow> f -- x --> K"
  by simp

lemma tendsto_at_iff_tendsto_nhds:
  "g -- l --> g l \<longleftrightarrow> (g ---> g l) (nhds l)"
  unfolding tendsto_def eventually_at_filter
  by (intro ext all_cong imp_cong) (auto elim!: eventually_elim1)

lemma tendsto_compose:
  "g -- l --> g l \<Longrightarrow> (f ---> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) ---> g l) F"
  unfolding tendsto_at_iff_tendsto_nhds by (rule filterlim_compose[of g])

lemma LIM_o: "\<lbrakk>g -- l --> g l; f -- a --> l\<rbrakk> \<Longrightarrow> (g \<circ> f) -- a --> g l"
  unfolding o_def by (rule tendsto_compose)

lemma tendsto_compose_eventually:
  "g -- l --> m \<Longrightarrow> (f ---> l) F \<Longrightarrow> eventually (\<lambda>x. f x \<noteq> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) ---> m) F"
  by (rule filterlim_compose[of g _ "at l"]) (auto simp add: filterlim_at)

lemma LIM_compose_eventually:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "eventually (\<lambda>x. f x \<noteq> b) (at a)"
  shows "(\<lambda>x. g (f x)) -- a --> c"
  using g f inj by (rule tendsto_compose_eventually)

subsubsection {* Relation of LIM and LIMSEQ *}

lemma (in first_countable_topology) sequentially_imp_eventually_within:
  "(\<forall>f. (\<forall>n. f n \<in> s \<and> f n \<noteq> a) \<and> f ----> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially) \<Longrightarrow>
    eventually P (at a within s)"
  unfolding at_within_def
  by (intro sequentially_imp_eventually_nhds_within) auto

lemma (in first_countable_topology) sequentially_imp_eventually_at:
  "(\<forall>f. (\<forall>n. f n \<noteq> a) \<and> f ----> a \<longrightarrow> eventually (\<lambda>n. P (f n)) sequentially) \<Longrightarrow> eventually P (at a)"
  using assms sequentially_imp_eventually_within [where s=UNIV] by simp

lemma LIMSEQ_SEQ_conv1:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "f -- a --> l"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. f (S n)) ----> l"
  using tendsto_compose_eventually [OF f, where F=sequentially] by simp

lemma LIMSEQ_SEQ_conv2:
  fixes f :: "'a::first_countable_topology \<Rightarrow> 'b::topological_space"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. f (S n)) ----> l"
  shows "f -- a --> l"
  using assms unfolding tendsto_def [where l=l] by (simp add: sequentially_imp_eventually_at)

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::'a::first_countable_topology) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> (L::'b::topological_space))"
  using LIMSEQ_SEQ_conv2 LIMSEQ_SEQ_conv1 ..

subsection {* Continuity *}

subsubsection {* Continuity on a set *}

definition continuous_on :: "'a set \<Rightarrow> ('a :: topological_space \<Rightarrow> 'b :: topological_space) \<Rightarrow> bool" where
  "continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. (f ---> f x) (at x within s))"

lemma continuous_on_cong [cong]:
  "s = t \<Longrightarrow> (\<And>x. x \<in> t \<Longrightarrow> f x = g x) \<Longrightarrow> continuous_on s f \<longleftrightarrow> continuous_on t g"
  unfolding continuous_on_def by (intro ball_cong filterlim_cong) (auto simp: eventually_at_filter)

lemma continuous_on_topological:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>B. open B \<longrightarrow> f x \<in> B \<longrightarrow> (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)))"
  unfolding continuous_on_def tendsto_def eventually_at_topological by metis

lemma continuous_on_open_invariant:
  "continuous_on s f \<longleftrightarrow> (\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> s = f -` B \<inter> s))"
proof safe
  fix B :: "'b set" assume "continuous_on s f" "open B"
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
    fix x B assume "x \<in> s" "open B" "f x \<in> B"
    with B obtain A where A: "open A" "A \<inter> s = f -` B \<inter> s" by auto
    with `x \<in> s` `f x \<in> B` show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)"
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

corollary open_vimage:
  assumes "open s" and "continuous_on UNIV f"
  shows "open (f -` s)"
  using assms unfolding continuous_on_open_vimage [OF open_UNIV]
  by simp

lemma continuous_on_closed_invariant:
  "continuous_on s f \<longleftrightarrow> (\<forall>B. closed B \<longrightarrow> (\<exists>A. closed A \<and> A \<inter> s = f -` B \<inter> s))"
proof -
  have *: "\<And>P Q::'b set\<Rightarrow>bool. (\<And>A. P A \<longleftrightarrow> Q (- A)) \<Longrightarrow> (\<forall>A. P A) \<longleftrightarrow> (\<forall>A. Q A)"
    by (metis double_compl)
  show ?thesis
    unfolding continuous_on_open_invariant by (intro *) (auto simp: open_closed[symmetric])
qed

lemma continuous_on_closed_vimage:
  "closed s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>B. closed B \<longrightarrow> closed (f -` B \<inter> s))"
  unfolding continuous_on_closed_invariant
  by (metis closed_Int Int_absorb Int_commute[of s] Int_assoc[of _ _ s])

lemma continuous_on_open_Union:
  "(\<And>s. s \<in> S \<Longrightarrow> open s) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> continuous_on s f) \<Longrightarrow> continuous_on (\<Union>S) f"
  unfolding continuous_on_def by safe (metis open_Union at_within_open UnionI)

lemma continuous_on_open_UN:
  "(\<And>s. s \<in> S \<Longrightarrow> open (A s)) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> continuous_on (A s) f) \<Longrightarrow> continuous_on (\<Union>s\<in>S. A s) f"
  unfolding Union_image_eq[symmetric] by (rule continuous_on_open_Union) auto

lemma continuous_on_closed_Un:
  "closed s \<Longrightarrow> closed t \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on t f \<Longrightarrow> continuous_on (s \<union> t) f"
  by (auto simp add: continuous_on_closed_vimage closed_Un Int_Un_distrib)

lemma continuous_on_If:
  assumes closed: "closed s" "closed t" and cont: "continuous_on s f" "continuous_on t g"
    and P: "\<And>x. x \<in> s \<Longrightarrow> \<not> P x \<Longrightarrow> f x = g x" "\<And>x. x \<in> t \<Longrightarrow> P x \<Longrightarrow> f x = g x"
  shows "continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)" (is "continuous_on _ ?h")
proof-
  from P have "\<forall>x\<in>s. f x = ?h x" "\<forall>x\<in>t. g x = ?h x"
    by auto
  with cont have "continuous_on s ?h" "continuous_on t ?h"
    by simp_all
  with closed show ?thesis
    by (rule continuous_on_closed_Un)
qed

ML {*

structure Continuous_On_Intros = Named_Thms
(
  val name = @{binding continuous_on_intros}
  val description = "Structural introduction rules for setwise continuity"
)

*}

setup Continuous_On_Intros.setup

lemma continuous_on_id[continuous_on_intros]: "continuous_on s (\<lambda>x. x)"
  unfolding continuous_on_def by (fast intro: tendsto_ident_at)

lemma continuous_on_const[continuous_on_intros]: "continuous_on s (\<lambda>x. c)"
  unfolding continuous_on_def by (auto intro: tendsto_const)

lemma continuous_on_compose[continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on (f ` s) g \<Longrightarrow> continuous_on s (g o f)"
  unfolding continuous_on_topological by simp metis

lemma continuous_on_compose2:
  "continuous_on t g \<Longrightarrow> continuous_on s f \<Longrightarrow> t = f ` s \<Longrightarrow> continuous_on s (\<lambda>x. g (f x))"
  using continuous_on_compose[of s f g] by (simp add: comp_def)

subsubsection {* Continuity at a point *}

definition continuous :: "'a::t2_space filter \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> bool" where
  "continuous F f \<longleftrightarrow> (f ---> f (Lim F (\<lambda>x. x))) F"

ML {*

structure Continuous_Intros = Named_Thms
(
  val name = @{binding continuous_intros}
  val description = "Structural introduction rules for pointwise continuity"
)

*}

setup Continuous_Intros.setup

lemma continuous_bot[continuous_intros, simp]: "continuous bot f"
  unfolding continuous_def by auto

lemma continuous_trivial_limit: "trivial_limit net \<Longrightarrow> continuous net f"
  by simp

lemma continuous_within: "continuous (at x within s) f \<longleftrightarrow> (f ---> f x) (at x within s)"
  by (cases "trivial_limit (at x within s)") (auto simp add: Lim_ident_at continuous_def)

lemma continuous_within_topological:
  "continuous (at x within s) f \<longleftrightarrow>
    (\<forall>B. open B \<longrightarrow> f x \<in> B \<longrightarrow> (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>s. y \<in> A \<longrightarrow> f y \<in> B)))"
  unfolding continuous_within tendsto_def eventually_at_topological by metis

lemma continuous_within_compose[continuous_intros]:
  "continuous (at x within s) f \<Longrightarrow> continuous (at (f x) within f ` s) g \<Longrightarrow>
  continuous (at x within s) (g o f)"
  by (simp add: continuous_within_topological) metis

lemma continuous_within_compose2:
  "continuous (at x within s) f \<Longrightarrow> continuous (at (f x) within f ` s) g \<Longrightarrow>
  continuous (at x within s) (\<lambda>x. g (f x))"
  using continuous_within_compose[of x s f g] by (simp add: comp_def)

lemma continuous_at: "continuous (at x) f \<longleftrightarrow> f -- x --> f x"
  using continuous_within[of x UNIV f] by simp

lemma continuous_ident[continuous_intros, simp]: "continuous (at x within S) (\<lambda>x. x)"
  unfolding continuous_within by (rule tendsto_ident_at)

lemma continuous_const[continuous_intros, simp]: "continuous F (\<lambda>x. c)"
  unfolding continuous_def by (rule tendsto_const)

lemma continuous_on_eq_continuous_within:
  "continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. continuous (at x within s) f)"
  unfolding continuous_on_def continuous_within ..

abbreviation isCont :: "('a::t2_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a \<Rightarrow> bool" where
  "isCont f a \<equiv> continuous (at a) f"

lemma isCont_def: "isCont f a \<longleftrightarrow> f -- a --> f a"
  by (rule continuous_at)

lemma continuous_at_within: "isCont f x \<Longrightarrow> continuous (at x within s) f"
  by (auto intro: tendsto_mono at_le simp: continuous_at continuous_within)

lemma continuous_on_eq_continuous_at: "open s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. isCont f x)"
  by (simp add: continuous_on_def continuous_at at_within_open[of _ s])

lemma continuous_on_subset: "continuous_on s f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> continuous_on t f"
  unfolding continuous_on_def by (metis subset_eq tendsto_within_subset)

lemma continuous_at_imp_continuous_on: "\<forall>x\<in>s. isCont f x \<Longrightarrow> continuous_on s f"
  by (auto intro: continuous_at_within simp: continuous_on_eq_continuous_within)

lemma isContI_continuous: "continuous (at x within UNIV) f \<Longrightarrow> isCont f x"
  by simp

lemma isCont_ident[continuous_intros, simp]: "isCont (\<lambda>x. x) a"
  using continuous_ident by (rule isContI_continuous)

lemmas isCont_const = continuous_const

lemma isCont_o2: "isCont f a \<Longrightarrow> isCont g (f a) \<Longrightarrow> isCont (\<lambda>x. g (f x)) a"
  unfolding isCont_def by (rule tendsto_compose)

lemma isCont_o[continuous_intros]: "isCont f a \<Longrightarrow> isCont g (f a) \<Longrightarrow> isCont (g \<circ> f) a"
  unfolding o_def by (rule isCont_o2)

lemma isCont_tendsto_compose: "isCont g l \<Longrightarrow> (f ---> l) F \<Longrightarrow> ((\<lambda>x. g (f x)) ---> g l) F"
  unfolding isCont_def by (rule tendsto_compose)

lemma continuous_within_compose3:
  "isCont g (f x) \<Longrightarrow> continuous (at x within s) f \<Longrightarrow> continuous (at x within s) (\<lambda>x. g (f x))"
  using continuous_within_compose2[of x s f g] by (simp add: continuous_at_within)

subsubsection{* Open-cover compactness *}

context topological_space
begin

definition compact :: "'a set \<Rightarrow> bool" where
  compact_eq_heine_borel: -- "This name is used for backwards compatibility"
    "compact S \<longleftrightarrow> (\<forall>C. (\<forall>c\<in>C. open c) \<and> S \<subseteq> \<Union>C \<longrightarrow> (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"

lemma compactI:
  assumes "\<And>C. \<forall>t\<in>C. open t \<Longrightarrow> s \<subseteq> \<Union> C \<Longrightarrow> \<exists>C'. C' \<subseteq> C \<and> finite C' \<and> s \<subseteq> \<Union> C'"
  shows "compact s"
  unfolding compact_eq_heine_borel using assms by metis

lemma compact_empty[simp]: "compact {}"
  by (auto intro!: compactI)

lemma compactE:
  assumes "compact s" and "\<forall>t\<in>C. open t" and "s \<subseteq> \<Union>C"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "s \<subseteq> \<Union>C'"
  using assms unfolding compact_eq_heine_borel by metis

lemma compactE_image:
  assumes "compact s" and "\<forall>t\<in>C. open (f t)" and "s \<subseteq> (\<Union>c\<in>C. f c)"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "s \<subseteq> (\<Union>c\<in>C'. f c)"
  using assms unfolding ball_simps[symmetric] SUP_def
  by (metis (lifting) finite_subset_image compact_eq_heine_borel[of s])

lemma compact_inter_closed [intro]:
  assumes "compact s" and "closed t"
  shows "compact (s \<inter> t)"
proof (rule compactI)
  fix C assume C: "\<forall>c\<in>C. open c" and cover: "s \<inter> t \<subseteq> \<Union>C"
  from C `closed t` have "\<forall>c\<in>C \<union> {-t}. open c" by auto
  moreover from cover have "s \<subseteq> \<Union>(C \<union> {-t})" by auto
  ultimately have "\<exists>D\<subseteq>C \<union> {-t}. finite D \<and> s \<subseteq> \<Union>D"
    using `compact s` unfolding compact_eq_heine_borel by auto
  then obtain D where "D \<subseteq> C \<union> {- t} \<and> finite D \<and> s \<subseteq> \<Union>D" ..
  then show "\<exists>D\<subseteq>C. finite D \<and> s \<inter> t \<subseteq> \<Union>D"
    by (intro exI[of _ "D - {-t}"]) auto
qed

lemma inj_setminus: "inj_on uminus (A::'a set set)"
  by (auto simp: inj_on_def)

lemma compact_fip:
  "compact U \<longleftrightarrow>
    (\<forall>A. (\<forall>a\<in>A. closed a) \<longrightarrow> (\<forall>B \<subseteq> A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}) \<longrightarrow> U \<inter> \<Inter>A \<noteq> {})"
  (is "_ \<longleftrightarrow> ?R")
proof (safe intro!: compact_eq_heine_borel[THEN iffD2])
  fix A
  assume "compact U"
    and A: "\<forall>a\<in>A. closed a" "U \<inter> \<Inter>A = {}"
    and fi: "\<forall>B \<subseteq> A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}"
  from A have "(\<forall>a\<in>uminus`A. open a) \<and> U \<subseteq> \<Union>(uminus`A)"
    by auto
  with `compact U` obtain B where "B \<subseteq> A" "finite (uminus`B)" "U \<subseteq> \<Union>(uminus`B)"
    unfolding compact_eq_heine_borel by (metis subset_image_iff)
  with fi[THEN spec, of B] show False
    by (auto dest: finite_imageD intro: inj_setminus)
next
  fix A
  assume ?R
  assume "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A"
  then have "U \<inter> \<Inter>(uminus`A) = {}" "\<forall>a\<in>uminus`A. closed a"
    by auto
  with `?R` obtain B where "B \<subseteq> A" "finite (uminus`B)" "U \<inter> \<Inter>(uminus`B) = {}"
    by (metis subset_image_iff)
  then show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
    by  (auto intro!: exI[of _ B] inj_setminus dest: finite_imageD)
qed

lemma compact_imp_fip:
  "compact s \<Longrightarrow> \<forall>t \<in> f. closed t \<Longrightarrow> \<forall>f'. finite f' \<and> f' \<subseteq> f \<longrightarrow> (s \<inter> (\<Inter> f') \<noteq> {}) \<Longrightarrow>
    s \<inter> (\<Inter> f) \<noteq> {}"
  unfolding compact_fip by auto

lemma compact_imp_fip_image:
  "compact s \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> closed (f i)) \<Longrightarrow> (\<And>I'. finite I' \<Longrightarrow> I' \<subseteq> I \<Longrightarrow> (s \<inter> (\<Inter>i\<in>I'. f i) \<noteq> {})) \<Longrightarrow>
    s \<inter> (\<Inter>i\<in>I. f i) \<noteq> {}"
  using finite_subset_image[of _ f I] compact_imp_fip[of s "f`I"] unfolding ball_simps[symmetric] INF_def
  by (metis image_iff)

end

lemma (in t2_space) compact_imp_closed:
  assumes "compact s" shows "closed s"
unfolding closed_def
proof (rule openI)
  fix y assume "y \<in> - s"
  let ?C = "\<Union>x\<in>s. {u. open u \<and> x \<in> u \<and> eventually (\<lambda>y. y \<notin> u) (nhds y)}"
  note `compact s`
  moreover have "\<forall>u\<in>?C. open u" by simp
  moreover have "s \<subseteq> \<Union>?C"
  proof
    fix x assume "x \<in> s"
    with `y \<in> - s` have "x \<noteq> y" by clarsimp
    hence "\<exists>u v. open u \<and> open v \<and> x \<in> u \<and> y \<in> v \<and> u \<inter> v = {}"
      by (rule hausdorff)
    with `x \<in> s` show "x \<in> \<Union>?C"
      unfolding eventually_nhds by auto
  qed
  ultimately obtain D where "D \<subseteq> ?C" and "finite D" and "s \<subseteq> \<Union>D"
    by (rule compactE)
  from `D \<subseteq> ?C` have "\<forall>x\<in>D. eventually (\<lambda>y. y \<notin> x) (nhds y)" by auto
  with `finite D` have "eventually (\<lambda>y. y \<notin> \<Union>D) (nhds y)"
    by (simp add: eventually_Ball_finite)
  with `s \<subseteq> \<Union>D` have "eventually (\<lambda>y. y \<notin> s) (nhds y)"
    by (auto elim!: eventually_mono [rotated])
  thus "\<exists>t. open t \<and> y \<in> t \<and> t \<subseteq> - s"
    by (simp add: eventually_nhds subset_eq)
qed

lemma compact_continuous_image:
  assumes f: "continuous_on s f" and s: "compact s"
  shows "compact (f ` s)"
proof (rule compactI)
  fix C assume "\<forall>c\<in>C. open c" and cover: "f`s \<subseteq> \<Union>C"
  with f have "\<forall>c\<in>C. \<exists>A. open A \<and> A \<inter> s = f -` c \<inter> s"
    unfolding continuous_on_open_invariant by blast
  then obtain A where A: "\<forall>c\<in>C. open (A c) \<and> A c \<inter> s = f -` c \<inter> s"
    unfolding bchoice_iff ..
  with cover have "\<forall>c\<in>C. open (A c)" "s \<subseteq> (\<Union>c\<in>C. A c)"
    by (fastforce simp add: subset_eq set_eq_iff)+
  from compactE_image[OF s this] obtain D where "D \<subseteq> C" "finite D" "s \<subseteq> (\<Union>c\<in>D. A c)" .
  with A show "\<exists>D \<subseteq> C. finite D \<and> f`s \<subseteq> \<Union>D"
    by (intro exI[of _ D]) (fastforce simp add: subset_eq set_eq_iff)+
qed

lemma continuous_on_inv:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "continuous_on s f"  "compact s"  "\<forall>x\<in>s. g (f x) = x"
  shows "continuous_on (f ` s) g"
unfolding continuous_on_topological
proof (clarsimp simp add: assms(3))
  fix x :: 'a and B :: "'a set"
  assume "x \<in> s" and "open B" and "x \<in> B"
  have 1: "\<forall>x\<in>s. f x \<in> f ` (s - B) \<longleftrightarrow> x \<in> s - B"
    using assms(3) by (auto, metis)
  have "continuous_on (s - B) f"
    using `continuous_on s f` Diff_subset
    by (rule continuous_on_subset)
  moreover have "compact (s - B)"
    using `open B` and `compact s`
    unfolding Diff_eq by (intro compact_inter_closed closed_Compl)
  ultimately have "compact (f ` (s - B))"
    by (rule compact_continuous_image)
  hence "closed (f ` (s - B))"
    by (rule compact_imp_closed)
  hence "open (- f ` (s - B))"
    by (rule open_Compl)
  moreover have "f x \<in> - f ` (s - B)"
    using `x \<in> s` and `x \<in> B` by (simp add: 1)
  moreover have "\<forall>y\<in>s. f y \<in> - f ` (s - B) \<longrightarrow> y \<in> B"
    by (simp add: 1)
  ultimately show "\<exists>A. open A \<and> f x \<in> A \<and> (\<forall>y\<in>s. f y \<in> A \<longrightarrow> y \<in> B)"
    by fast
qed

lemma continuous_on_inv_into:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes s: "continuous_on s f" "compact s" and f: "inj_on f s"
  shows "continuous_on (f ` s) (the_inv_into s f)"
  by (rule continuous_on_inv[OF s]) (auto simp: the_inv_into_f_f[OF f])

lemma (in linorder_topology) compact_attains_sup:
  assumes "compact S" "S \<noteq> {}"
  shows "\<exists>s\<in>S. \<forall>t\<in>S. t \<le> s"
proof (rule classical)
  assume "\<not> (\<exists>s\<in>S. \<forall>t\<in>S. t \<le> s)"
  then obtain t where t: "\<forall>s\<in>S. t s \<in> S" and "\<forall>s\<in>S. s < t s"
    by (metis not_le)
  then have "\<forall>s\<in>S. open {..< t s}" "S \<subseteq> (\<Union>s\<in>S. {..< t s})"
    by auto
  with `compact S` obtain C where "C \<subseteq> S" "finite C" and C: "S \<subseteq> (\<Union>s\<in>C. {..< t s})"
    by (erule compactE_image)
  with `S \<noteq> {}` have Max: "Max (t`C) \<in> t`C" and "\<forall>s\<in>t`C. s \<le> Max (t`C)"
    by (auto intro!: Max_in)
  with C have "S \<subseteq> {..< Max (t`C)}"
    by (auto intro: less_le_trans simp: subset_eq)
  with t Max `C \<subseteq> S` show ?thesis
    by fastforce
qed

lemma (in linorder_topology) compact_attains_inf:
  assumes "compact S" "S \<noteq> {}"
  shows "\<exists>s\<in>S. \<forall>t\<in>S. s \<le> t"
proof (rule classical)
  assume "\<not> (\<exists>s\<in>S. \<forall>t\<in>S. s \<le> t)"
  then obtain t where t: "\<forall>s\<in>S. t s \<in> S" and "\<forall>s\<in>S. t s < s"
    by (metis not_le)
  then have "\<forall>s\<in>S. open {t s <..}" "S \<subseteq> (\<Union>s\<in>S. {t s <..})"
    by auto
  with `compact S` obtain C where "C \<subseteq> S" "finite C" and C: "S \<subseteq> (\<Union>s\<in>C. {t s <..})"
    by (erule compactE_image)
  with `S \<noteq> {}` have Min: "Min (t`C) \<in> t`C" and "\<forall>s\<in>t`C. Min (t`C) \<le> s"
    by (auto intro!: Min_in)
  with C have "S \<subseteq> {Min (t`C) <..}"
    by (auto intro: le_less_trans simp: subset_eq)
  with t Min `C \<subseteq> S` show ?thesis
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


subsection {* Connectedness *}

context topological_space
begin

definition "connected S \<longleftrightarrow>
  \<not> (\<exists>A B. open A \<and> open B \<and> S \<subseteq> A \<union> B \<and> A \<inter> B \<inter> S = {} \<and> A \<inter> S \<noteq> {} \<and> B \<inter> S \<noteq> {})"

lemma connectedI:
  "(\<And>A B. open A \<Longrightarrow> open B \<Longrightarrow> A \<inter> U \<noteq> {} \<Longrightarrow> B \<inter> U \<noteq> {} \<Longrightarrow> A \<inter> B \<inter> U = {} \<Longrightarrow> U \<subseteq> A \<union> B \<Longrightarrow> False)
  \<Longrightarrow> connected U"
  by (auto simp: connected_def)

lemma connected_empty[simp]: "connected {}"
  by (auto intro!: connectedI)

end

lemma (in linorder_topology) connectedD_interval:
  assumes "connected U" and xy: "x \<in> U" "y \<in> U" and "x \<le> z" "z \<le> y"
  shows "z \<in> U"
proof -
  have eq: "{..<z} \<union> {z<..} = - {z}"
    by auto
  { assume "z \<notin> U" "x < z" "z < y"
    with xy have "\<not> connected U"
      unfolding connected_def simp_thms
      apply (rule_tac exI[of _ "{..< z}"])
      apply (rule_tac exI[of _ "{z <..}"])
      apply (auto simp add: eq)
      done }
  with assms show "z \<in> U"
    by (metis less_le)
qed

lemma connected_continuous_image:
  assumes *: "continuous_on s f"
  assumes "connected s"
  shows "connected (f ` s)"
proof (rule connectedI)
  fix A B assume A: "open A" "A \<inter> f ` s \<noteq> {}" and B: "open B" "B \<inter> f ` s \<noteq> {}" and
    AB: "A \<inter> B \<inter> f ` s = {}" "f ` s \<subseteq> A \<union> B"
  obtain A' where A': "open A'" "f -` A \<inter> s = A' \<inter> s"
    using * `open A` unfolding continuous_on_open_invariant by metis
  obtain B' where B': "open B'" "f -` B \<inter> s = B' \<inter> s"
    using * `open B` unfolding continuous_on_open_invariant by metis

  have "\<exists>A B. open A \<and> open B \<and> s \<subseteq> A \<union> B \<and> A \<inter> B \<inter> s = {} \<and> A \<inter> s \<noteq> {} \<and> B \<inter> s \<noteq> {}"
  proof (rule exI[of _ A'], rule exI[of _ B'], intro conjI)
    have "s \<subseteq> (f -` A \<inter> s) \<union> (f -` B \<inter> s)" using AB by auto
    then show "s \<subseteq> A' \<union> B'" using A' B' by auto
  next
    have "(f -` A \<inter> s) \<inter> (f -` B \<inter> s) = {}" using AB by auto
    then show "A' \<inter> B' \<inter> s = {}" using A' B' by auto
  qed (insert A' B' A B, auto)
  with `connected s` show False
    unfolding connected_def by blast
qed


section {* Connectedness *}

class linear_continuum_topology = linorder_topology + linear_continuum
begin

lemma Inf_notin_open:
  assumes A: "open A" and bnd: "\<forall>a\<in>A. x < a"
  shows "Inf A \<notin> A"
proof
  assume "Inf A \<in> A"
  then obtain b where "b < Inf A" "{b <.. Inf A} \<subseteq> A"
    using open_left[of A "Inf A" x] assms by auto
  with dense[of b "Inf A"] obtain c where "c < Inf A" "c \<in> A"
    by (auto simp: subset_eq)
  then show False
    using cInf_lower[OF `c \<in> A`] bnd by (metis not_le less_imp_le bdd_belowI)
qed

lemma Sup_notin_open:
  assumes A: "open A" and bnd: "\<forall>a\<in>A. a < x"
  shows "Sup A \<notin> A"
proof
  assume "Sup A \<in> A"
  then obtain b where "Sup A < b" "{Sup A ..< b} \<subseteq> A"
    using open_right[of A "Sup A" x] assms by auto
  with dense[of "Sup A" b] obtain c where "Sup A < c" "c \<in> A"
    by (auto simp: subset_eq)
  then show False
    using cSup_upper[OF `c \<in> A`] bnd by (metis less_imp_le not_le bdd_aboveI)
qed

end

instance linear_continuum_topology \<subseteq> perfect_space
proof
  fix x :: 'a
  obtain y where "x < y \<or> y < x"
    using ex_gt_or_lt [of x] ..
  with Inf_notin_open[of "{x}" y] Sup_notin_open[of "{x}" y]
  show "\<not> open {x}"
    by auto
qed

lemma connectedI_interval:
  fixes U :: "'a :: linear_continuum_topology set"
  assumes *: "\<And>x y z. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x \<le> z \<Longrightarrow> z \<le> y \<Longrightarrow> z \<in> U"
  shows "connected U"
proof (rule connectedI)
  { fix A B assume "open A" "open B" "A \<inter> B \<inter> U = {}" "U \<subseteq> A \<union> B"
    fix x y assume "x < y" "x \<in> A" "y \<in> B" "x \<in> U" "y \<in> U"

    let ?z = "Inf (B \<inter> {x <..})"

    have "x \<le> ?z" "?z \<le> y"
      using `y \<in> B` `x < y` by (auto intro: cInf_lower cInf_greatest)
    with `x \<in> U` `y \<in> U` have "?z \<in> U"
      by (rule *)
    moreover have "?z \<notin> B \<inter> {x <..}"
      using `open B` by (intro Inf_notin_open) auto
    ultimately have "?z \<in> A"
      using `x \<le> ?z` `A \<inter> B \<inter> U = {}` `x \<in> A` `U \<subseteq> A \<union> B` by auto

    { assume "?z < y"
      obtain a where "?z < a" "{?z ..< a} \<subseteq> A"
        using open_right[OF `open A` `?z \<in> A` `?z < y`] by auto
      moreover obtain b where "b \<in> B" "x < b" "b < min a y"
        using cInf_less_iff[of "B \<inter> {x <..}" "min a y"] `?z < a` `?z < y` `x < y` `y \<in> B`
        by (auto intro: less_imp_le)
      moreover have "?z \<le> b"
        using `b \<in> B` `x < b`
        by (intro cInf_lower) auto
      moreover have "b \<in> U"
        using `x \<le> ?z` `?z \<le> b` `b < min a y`
        by (intro *[OF `x \<in> U` `y \<in> U`]) (auto simp: less_imp_le)
      ultimately have "\<exists>b\<in>B. b \<in> A \<and> b \<in> U"
        by (intro bexI[of _ b]) auto }
    then have False
      using `?z \<le> y` `?z \<in> A` `y \<in> B` `y \<in> U` `A \<inter> B \<inter> U = {}` unfolding le_less by blast }
  note not_disjoint = this

  fix A B assume AB: "open A" "open B" "U \<subseteq> A \<union> B" "A \<inter> B \<inter> U = {}"
  moreover assume "A \<inter> U \<noteq> {}" then obtain x where x: "x \<in> U" "x \<in> A" by auto
  moreover assume "B \<inter> U \<noteq> {}" then obtain y where y: "y \<in> U" "y \<in> B" by auto
  moreover note not_disjoint[of B A y x] not_disjoint[of A B x y]
  ultimately show False by (cases x y rule: linorder_cases) auto
qed

lemma connected_iff_interval:
  fixes U :: "'a :: linear_continuum_topology set"
  shows "connected U \<longleftrightarrow> (\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z. x \<le> z \<longrightarrow> z \<le> y \<longrightarrow> z \<in> U)"
  by (auto intro: connectedI_interval dest: connectedD_interval)

lemma connected_UNIV[simp]: "connected (UNIV::'a::linear_continuum_topology set)"
  unfolding connected_iff_interval by auto

lemma connected_Ioi[simp]: "connected {a::'a::linear_continuum_topology <..}"
  unfolding connected_iff_interval by auto

lemma connected_Ici[simp]: "connected {a::'a::linear_continuum_topology ..}"
  unfolding connected_iff_interval by auto

lemma connected_Iio[simp]: "connected {..< a::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_Iic[simp]: "connected {.. a::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_Ioo[simp]: "connected {a <..< b::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_Ioc[simp]: "connected {a <.. b::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_Ico[simp]: "connected {a ..< b::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_Icc[simp]: "connected {a .. b::'a::linear_continuum_topology}"
  unfolding connected_iff_interval by auto

lemma connected_contains_Ioo: 
  fixes A :: "'a :: linorder_topology set"
  assumes A: "connected A" "a \<in> A" "b \<in> A" shows "{a <..< b} \<subseteq> A"
  using connectedD_interval[OF A] by (simp add: subset_eq Ball_def less_imp_le)

subsection {* Intermediate Value Theorem *}

lemma IVT':
  fixes f :: "'a :: linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes y: "f a \<le> y" "y \<le> f b" "a \<le> b"
  assumes *: "continuous_on {a .. b} f"
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
  assumes *: "continuous_on {a .. b} f"
  shows "\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
proof -
  have "connected {a..b}"
    unfolding connected_iff_interval by auto
  from connected_continuous_image[OF * this, THEN connectedD_interval, of "f b" "f a" y] y
  show ?thesis
    by (auto simp add: atLeastAtMost_def atLeast_def atMost_def)
qed

lemma IVT:
  fixes f :: "'a :: linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  shows "f a \<le> y \<Longrightarrow> y \<le> f b \<Longrightarrow> a \<le> b \<Longrightarrow> (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x) \<Longrightarrow> \<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
  by (rule IVT') (auto intro: continuous_at_imp_continuous_on)

lemma IVT2:
  fixes f :: "'a :: linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  shows "f b \<le> y \<Longrightarrow> y \<le> f a \<Longrightarrow> a \<le> b \<Longrightarrow> (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x) \<Longrightarrow> \<exists>x. a \<le> x \<and> x \<le> b \<and> f x = y"
  by (rule IVT2') (auto intro: continuous_at_imp_continuous_on)

lemma continuous_inj_imp_mono:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b :: linorder_topology"
  assumes x: "a < x" "x < b"
  assumes cont: "continuous_on {a..b} f"
  assumes inj: "inj_on f {a..b}"
  shows "(f a < f x \<and> f x < f b) \<or> (f b < f x \<and> f x < f a)"
proof -
  note I = inj_on_iff[OF inj]
  { assume "f x < f a" "f x < f b"
    then obtain s t where "x \<le> s" "s \<le> b" "a \<le> t" "t \<le> x" "f s = f t" "f x < f s"
      using IVT'[of f x "min (f a) (f b)" b] IVT2'[of f x "min (f a) (f b)" a] x
      by (auto simp: continuous_on_subset[OF cont] less_imp_le)
    with x I have False by auto }
  moreover
  { assume "f a < f x" "f b < f x"
    then obtain s t where "x \<le> s" "s \<le> b" "a \<le> t" "t \<le> x" "f s = f t" "f s < f x"
      using IVT'[of f a "max (f a) (f b)" x] IVT2'[of f b "max (f a) (f b)" x] x
      by (auto simp: continuous_on_subset[OF cont] less_imp_le)
    with x I have False by auto }
  ultimately show ?thesis
    using I[of a x] I[of x b] x less_trans[OF x] by (auto simp add: le_less less_imp_neq neq_iff)
qed

subsection {* Setup @{typ "'a filter"} for lifting and transfer *}

context begin interpretation lifting_syntax .

definition filter_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> 'b filter \<Rightarrow> bool"
where "filter_rel R F G = ((R ===> op =) ===> op =) (Rep_filter F) (Rep_filter G)"

lemma filter_rel_eventually:
  "filter_rel R F G \<longleftrightarrow> 
  ((R ===> op =) ===> op =) (\<lambda>P. eventually P F) (\<lambda>P. eventually P G)"
by(simp add: filter_rel_def eventually_def)

lemma filtermap_id [simp, id_simps]: "filtermap id = id"
by(simp add: fun_eq_iff id_def filtermap_ident)

lemma filtermap_id' [simp]: "filtermap (\<lambda>x. x) = (\<lambda>F. F)"
using filtermap_id unfolding id_def .

lemma Quotient_filter [quot_map]:
  assumes Q: "Quotient R Abs Rep T"
  shows "Quotient (filter_rel R) (filtermap Abs) (filtermap Rep) (filter_rel T)"
unfolding Quotient_alt_def
proof(intro conjI strip)
  from Q have *: "\<And>x y. T x y \<Longrightarrow> Abs x = y"
    unfolding Quotient_alt_def by blast

  fix F G
  assume "filter_rel T F G"
  thus "filtermap Abs F = G" unfolding filter_eq_iff
    by(auto simp add: eventually_filtermap filter_rel_eventually * fun_relI del: iffI elim!: fun_relD)
next
  from Q have *: "\<And>x. T (Rep x) x" unfolding Quotient_alt_def by blast

  fix F
  show "filter_rel T (filtermap Rep F) F" 
    by(auto elim: fun_relD intro: * intro!: ext arg_cong[where f="\<lambda>P. eventually P F"] fun_relI
            del: iffI simp add: eventually_filtermap filter_rel_eventually)
qed(auto simp add: map_fun_def o_def eventually_filtermap filter_eq_iff fun_eq_iff filter_rel_eventually
         fun_quotient[OF fun_quotient[OF Q identity_quotient] identity_quotient, unfolded Quotient_alt_def])

lemma eventually_parametric [transfer_rule]:
  "((A ===> op =) ===> filter_rel A ===> op =) eventually eventually"
by(simp add: fun_rel_def filter_rel_eventually)

lemma filter_rel_eq [relator_eq]: "filter_rel op = = op ="
by(auto simp add: filter_rel_eventually fun_rel_eq fun_eq_iff filter_eq_iff)

lemma filter_rel_mono [relator_mono]:
  "A \<le> B \<Longrightarrow> filter_rel A \<le> filter_rel B"
unfolding filter_rel_eventually[abs_def]
by(rule le_funI)+(intro fun_mono fun_mono[THEN le_funD, THEN le_funD] order.refl)

lemma filter_rel_conversep [simp]: "filter_rel A\<inverse>\<inverse> = (filter_rel A)\<inverse>\<inverse>"
by(auto simp add: filter_rel_eventually fun_eq_iff fun_rel_def)

lemma is_filter_parametric_aux:
  assumes "is_filter F"
  assumes [transfer_rule]: "bi_total A" "bi_unique A"
  and [transfer_rule]: "((A ===> op =) ===> op =) F G"
  shows "is_filter G"
proof -
  interpret is_filter F by fact
  show ?thesis
  proof
    have "F (\<lambda>_. True) = G (\<lambda>x. True)" by transfer_prover
    thus "G (\<lambda>x. True)" by(simp add: True)
  next
    fix P' Q'
    assume "G P'" "G Q'"
    moreover
    from bi_total_fun[OF `bi_unique A` bi_total_eq, unfolded bi_total_def]
    obtain P Q where [transfer_rule]: "(A ===> op =) P P'" "(A ===> op =) Q Q'" by blast
    have "F P = G P'" "F Q = G Q'" by transfer_prover+
    ultimately have "F (\<lambda>x. P x \<and> Q x)" by(simp add: conj)
    moreover have "F (\<lambda>x. P x \<and> Q x) = G (\<lambda>x. P' x \<and> Q' x)" by transfer_prover
    ultimately show "G (\<lambda>x. P' x \<and> Q' x)" by simp
  next
    fix P' Q'
    assume "\<forall>x. P' x \<longrightarrow> Q' x" "G P'"
    moreover
    from bi_total_fun[OF `bi_unique A` bi_total_eq, unfolded bi_total_def]
    obtain P Q where [transfer_rule]: "(A ===> op =) P P'" "(A ===> op =) Q Q'" by blast
    have "F P = G P'" by transfer_prover
    moreover have "(\<forall>x. P x \<longrightarrow> Q x) \<longleftrightarrow> (\<forall>x. P' x \<longrightarrow> Q' x)" by transfer_prover
    ultimately have "F Q" by(simp add: mono)
    moreover have "F Q = G Q'" by transfer_prover
    ultimately show "G Q'" by simp
  qed
qed

lemma is_filter_parametric [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique A \<rbrakk>
  \<Longrightarrow> (((A ===> op =) ===> op =) ===> op =) is_filter is_filter"
apply(rule fun_relI)
apply(rule iffI)
 apply(erule (3) is_filter_parametric_aux)
apply(erule is_filter_parametric_aux[where A="conversep A"])
apply(auto simp add: fun_rel_def)
done

lemma left_total_filter_rel [reflexivity_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique A"
  shows "left_total (filter_rel A)"
proof(rule left_totalI)
  fix F :: "'a filter"
  from bi_total_fun[OF bi_unique_fun[OF `bi_total A` bi_unique_eq] bi_total_eq]
  obtain G where [transfer_rule]: "((A ===> op =) ===> op =) (\<lambda>P. eventually P F) G" 
    unfolding  bi_total_def by blast
  moreover have "is_filter (\<lambda>P. eventually P F) \<longleftrightarrow> is_filter G" by transfer_prover
  hence "is_filter G" by(simp add: eventually_def is_filter_Rep_filter)
  ultimately have "filter_rel A F (Abs_filter G)"
    by(simp add: filter_rel_eventually eventually_Abs_filter)
  thus "\<exists>G. filter_rel A F G" ..
qed

lemma right_total_filter_rel [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique A \<rbrakk> \<Longrightarrow> right_total (filter_rel A)"
using left_total_filter_rel[of "A\<inverse>\<inverse>"] by simp

lemma bi_total_filter_rel [transfer_rule]:
  assumes "bi_total A" "bi_unique A"
  shows "bi_total (filter_rel A)"
unfolding bi_total_conv_left_right using assms
by(simp add: left_total_filter_rel right_total_filter_rel)

lemma left_unique_filter_rel [reflexivity_rule]:
  assumes "left_unique A"
  shows "left_unique (filter_rel A)"
proof(rule left_uniqueI)
  fix F F' G
  assume [transfer_rule]: "filter_rel A F G" "filter_rel A F' G"
  show "F = F'"
    unfolding filter_eq_iff
  proof
    fix P :: "'a \<Rightarrow> bool"
    obtain P' where [transfer_rule]: "(A ===> op =) P P'"
      using left_total_fun[OF assms left_total_eq] unfolding left_total_def by blast
    have "eventually P F = eventually P' G" 
      and "eventually P F' = eventually P' G" by transfer_prover+
    thus "eventually P F = eventually P F'" by simp
  qed
qed

lemma right_unique_filter_rel [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (filter_rel A)"
using left_unique_filter_rel[of "A\<inverse>\<inverse>"] by simp

lemma bi_unique_filter_rel [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (filter_rel A)"
by(simp add: bi_unique_conv_left_right left_unique_filter_rel right_unique_filter_rel)

lemma top_filter_parametric [transfer_rule]:
  "bi_total A \<Longrightarrow> (filter_rel A) top top"
by(simp add: filter_rel_eventually All_transfer)

lemma bot_filter_parametric [transfer_rule]: "(filter_rel A) bot bot"
by(simp add: filter_rel_eventually fun_rel_def)

lemma sup_filter_parametric [transfer_rule]:
  "(filter_rel A ===> filter_rel A ===> filter_rel A) sup sup"
by(fastforce simp add: filter_rel_eventually[abs_def] eventually_sup dest: fun_relD)

lemma Sup_filter_parametric [transfer_rule]:
  "(set_rel (filter_rel A) ===> filter_rel A) Sup Sup"
proof(rule fun_relI)
  fix S T
  assume [transfer_rule]: "set_rel (filter_rel A) S T"
  show "filter_rel A (Sup S) (Sup T)"
    by(simp add: filter_rel_eventually eventually_Sup) transfer_prover
qed

lemma principal_parametric [transfer_rule]:
  "(set_rel A ===> filter_rel A) principal principal"
proof(rule fun_relI)
  fix S S'
  assume [transfer_rule]: "set_rel A S S'"
  show "filter_rel A (principal S) (principal S')"
    by(simp add: filter_rel_eventually eventually_principal) transfer_prover
qed

context
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [transfer_rule]: "bi_unique A" 
begin

lemma le_filter_parametric [transfer_rule]:
  "(filter_rel A ===> filter_rel A ===> op =) op \<le> op \<le>"
unfolding le_filter_def[abs_def] by transfer_prover

lemma less_filter_parametric [transfer_rule]:
  "(filter_rel A ===> filter_rel A ===> op =) op < op <"
unfolding less_filter_def[abs_def] by transfer_prover

context
  assumes [transfer_rule]: "bi_total A"
begin

lemma Inf_filter_parametric [transfer_rule]:
  "(set_rel (filter_rel A) ===> filter_rel A) Inf Inf"
unfolding Inf_filter_def[abs_def] by transfer_prover

lemma inf_filter_parametric [transfer_rule]:
  "(filter_rel A ===> filter_rel A ===> filter_rel A) inf inf"
proof(intro fun_relI)+
  fix F F' G G'
  assume [transfer_rule]: "filter_rel A F F'" "filter_rel A G G'"
  have "filter_rel A (Inf {F, G}) (Inf {F', G'})" by transfer_prover
  thus "filter_rel A (inf F G) (inf F' G')" by simp
qed

end

end

end

end

(*  Title:      HOL/Analysis/Extended_Real_Limits.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

section \<open>Limits on the Extended real number line\<close>

theory Extended_Real_Limits
imports
  Topology_Euclidean_Space
  "HOL-Library.Extended_Real"
  "HOL-Library.Extended_Nonnegative_Real"
  "HOL-Library.Indicator_Function"
begin

lemma compact_UNIV:
  "compact (UNIV :: 'a::{complete_linorder,linorder_topology,second_countable_topology} set)"
  using compact_complete_linorder
  by (auto simp: seq_compact_eq_compact[symmetric] seq_compact_def)

lemma compact_eq_closed:
  fixes S :: "'a::{complete_linorder,linorder_topology,second_countable_topology} set"
  shows "compact S \<longleftrightarrow> closed S"
  using closed_Int_compact[of S, OF _ compact_UNIV] compact_imp_closed
  by auto

lemma closed_contains_Sup_cl:
  fixes S :: "'a::{complete_linorder,linorder_topology,second_countable_topology} set"
  assumes "closed S"
    and "S \<noteq> {}"
  shows "Sup S \<in> S"
proof -
  from compact_eq_closed[of S] compact_attains_sup[of S] assms
  obtain s where S: "s \<in> S" "\<forall>t\<in>S. t \<le> s"
    by auto
  then have "Sup S = s"
    by (auto intro!: Sup_eqI)
  with S show ?thesis
    by simp
qed

lemma closed_contains_Inf_cl:
  fixes S :: "'a::{complete_linorder,linorder_topology,second_countable_topology} set"
  assumes "closed S"
    and "S \<noteq> {}"
  shows "Inf S \<in> S"
proof -
  from compact_eq_closed[of S] compact_attains_inf[of S] assms
  obtain s where S: "s \<in> S" "\<forall>t\<in>S. s \<le> t"
    by auto
  then have "Inf S = s"
    by (auto intro!: Inf_eqI)
  with S show ?thesis
    by simp
qed

instance enat :: second_countable_topology
proof
  show "\<exists>B::enat set set. countable B \<and> open = generate_topology B"
  proof (intro exI conjI)
    show "countable (range lessThan \<union> range greaterThan::enat set set)"
      by auto
  qed (simp add: open_enat_def)
qed

instance ereal :: second_countable_topology
proof (standard, intro exI conjI)
  let ?B = "(\<Union>r\<in>\<rat>. {{..< r}, {r <..}} :: ereal set set)"
  show "countable ?B"
    by (auto intro: countable_rat)
  show "open = generate_topology ?B"
  proof (intro ext iffI)
    fix S :: "ereal set"
    assume "open S"
    then show "generate_topology ?B S"
      unfolding open_generated_order
    proof induct
      case (Basis b)
      then obtain e where "b = {..<e} \<or> b = {e<..}"
        by auto
      moreover have "{..<e} = \<Union>{{..<x}|x. x \<in> \<rat> \<and> x < e}" "{e<..} = \<Union>{{x<..}|x. x \<in> \<rat> \<and> e < x}"
        by (auto dest: ereal_dense3
                 simp del: ex_simps
                 simp add: ex_simps[symmetric] conj_commute Rats_def image_iff)
      ultimately show ?case
        by (auto intro: generate_topology.intros)
    qed (auto intro: generate_topology.intros)
  next
    fix S
    assume "generate_topology ?B S"
    then show "open S"
      by induct auto
  qed
qed

text \<open>This is a copy from \<open>ereal :: second_countable_topology\<close>. Maybe find a common super class of
topological spaces where the rational numbers are densely embedded ?\<close>
instance ennreal :: second_countable_topology
proof (standard, intro exI conjI)
  let ?B = "(\<Union>r\<in>\<rat>. {{..< r}, {r <..}} :: ennreal set set)"
  show "countable ?B"
    by (auto intro: countable_rat)
  show "open = generate_topology ?B"
  proof (intro ext iffI)
    fix S :: "ennreal set"
    assume "open S"
    then show "generate_topology ?B S"
      unfolding open_generated_order
    proof induct
      case (Basis b)
      then obtain e where "b = {..<e} \<or> b = {e<..}"
        by auto
      moreover have "{..<e} = \<Union>{{..<x}|x. x \<in> \<rat> \<and> x < e}" "{e<..} = \<Union>{{x<..}|x. x \<in> \<rat> \<and> e < x}"
        by (auto dest: ennreal_rat_dense
                 simp del: ex_simps
                 simp add: ex_simps[symmetric] conj_commute Rats_def image_iff)
      ultimately show ?case
        by (auto intro: generate_topology.intros)
    qed (auto intro: generate_topology.intros)
  next
    fix S
    assume "generate_topology ?B S"
    then show "open S"
      by induct auto
  qed
qed

lemma ereal_open_closed_aux:
  fixes S :: "ereal set"
  assumes "open S"
    and "closed S"
    and S: "(-\<infinity>) \<notin> S"
  shows "S = {}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have *: "Inf S \<in> S"

    by (metis assms(2) closed_contains_Inf_cl)
  {
    assume "Inf S = -\<infinity>"
    then have False
      using * assms(3) by auto
  }
  moreover
  {
    assume "Inf S = \<infinity>"
    then have "S = {\<infinity>}"
      by (metis Inf_eq_PInfty \<open>S \<noteq> {}\<close>)
    then have False
      by (metis assms(1) not_open_singleton)
  }
  moreover
  {
    assume fin: "\<bar>Inf S\<bar> \<noteq> \<infinity>"
    from ereal_open_cont_interval[OF assms(1) * fin]
    obtain e where e: "e > 0" "{Inf S - e<..<Inf S + e} \<subseteq> S" .
    then obtain b where b: "Inf S - e < b" "b < Inf S"
      using fin ereal_between[of "Inf S" e] dense[of "Inf S - e"]
      by auto
    then have "b: {Inf S - e <..< Inf S + e}"
      using e fin ereal_between[of "Inf S" e]
      by auto
    then have "b \<in> S"
      using e by auto
    then have False
      using b by (metis complete_lattice_class.Inf_lower leD)
  }
  ultimately show False
    by auto
qed

lemma ereal_open_closed:
  fixes S :: "ereal set"
  shows "open S \<and> closed S \<longleftrightarrow> S = {} \<or> S = UNIV"
proof -
  {
    assume lhs: "open S \<and> closed S"
    {
      assume "-\<infinity> \<notin> S"
      then have "S = {}"
        using lhs ereal_open_closed_aux by auto
    }
    moreover
    {
      assume "-\<infinity> \<in> S"
      then have "- S = {}"
        using lhs ereal_open_closed_aux[of "-S"] by auto
    }
    ultimately have "S = {} \<or> S = UNIV"
      by auto
  }
  then show ?thesis
    by auto
qed

lemma ereal_open_atLeast:
  fixes x :: ereal
  shows "open {x..} \<longleftrightarrow> x = -\<infinity>"
proof
  assume "x = -\<infinity>"
  then have "{x..} = UNIV"
    by auto
  then show "open {x..}"
    by auto
next
  assume "open {x..}"
  then have "open {x..} \<and> closed {x..}"
    by auto
  then have "{x..} = UNIV"
    unfolding ereal_open_closed by auto
  then show "x = -\<infinity>"
    by (simp add: bot_ereal_def atLeast_eq_UNIV_iff)
qed

lemma mono_closed_real:
  fixes S :: "real set"
  assumes mono: "\<forall>y z. y \<in> S \<and> y \<le> z \<longrightarrow> z \<in> S"
    and "closed S"
  shows "S = {} \<or> S = UNIV \<or> (\<exists>a. S = {a..})"
proof -
  {
    assume "S \<noteq> {}"
    { assume ex: "\<exists>B. \<forall>x\<in>S. B \<le> x"
      then have *: "\<forall>x\<in>S. Inf S \<le> x"
        using cInf_lower[of _ S] ex by (metis bdd_below_def)
      then have "Inf S \<in> S"
        apply (subst closed_contains_Inf)
        using ex \<open>S \<noteq> {}\<close> \<open>closed S\<close>
        apply auto
        done
      then have "\<forall>x. Inf S \<le> x \<longleftrightarrow> x \<in> S"
        using mono[rule_format, of "Inf S"] *
        by auto
      then have "S = {Inf S ..}"
        by auto
      then have "\<exists>a. S = {a ..}"
        by auto
    }
    moreover
    {
      assume "\<not> (\<exists>B. \<forall>x\<in>S. B \<le> x)"
      then have nex: "\<forall>B. \<exists>x\<in>S. x < B"
        by (simp add: not_le)
      {
        fix y
        obtain x where "x\<in>S" and "x < y"
          using nex by auto
        then have "y \<in> S"
          using mono[rule_format, of x y] by auto
      }
      then have "S = UNIV"
        by auto
    }
    ultimately have "S = UNIV \<or> (\<exists>a. S = {a ..})"
      by blast
  }
  then show ?thesis
    by blast
qed

lemma mono_closed_ereal:
  fixes S :: "real set"
  assumes mono: "\<forall>y z. y \<in> S \<and> y \<le> z \<longrightarrow> z \<in> S"
    and "closed S"
  shows "\<exists>a. S = {x. a \<le> ereal x}"
proof -
  {
    assume "S = {}"
    then have ?thesis
      apply (rule_tac x=PInfty in exI)
      apply auto
      done
  }
  moreover
  {
    assume "S = UNIV"
    then have ?thesis
      apply (rule_tac x="-\<infinity>" in exI)
      apply auto
      done
  }
  moreover
  {
    assume "\<exists>a. S = {a ..}"
    then obtain a where "S = {a ..}"
      by auto
    then have ?thesis
      apply (rule_tac x="ereal a" in exI)
      apply auto
      done
  }
  ultimately show ?thesis
    using mono_closed_real[of S] assms by auto
qed

lemma Liminf_within:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Liminf (at x within S) f = (SUP e:{0<..}. INF y:(S \<inter> ball x e - {x}). f y)"
  unfolding Liminf_def eventually_at
proof (rule SUP_eq, simp_all add: Ball_def Bex_def, safe)
  fix P d
  assume "0 < d" and "\<forall>y. y \<in> S \<longrightarrow> y \<noteq> x \<and> dist y x < d \<longrightarrow> P y"
  then have "S \<inter> ball x d - {x} \<subseteq> {x. P x}"
    by (auto simp: zero_less_dist_iff dist_commute)
  then show "\<exists>r>0. INFIMUM (Collect P) f \<le> INFIMUM (S \<inter> ball x r - {x}) f"
    by (intro exI[of _ d] INF_mono conjI \<open>0 < d\<close>) auto
next
  fix d :: real
  assume "0 < d"
  then show "\<exists>P. (\<exists>d>0. \<forall>xa. xa \<in> S \<longrightarrow> xa \<noteq> x \<and> dist xa x < d \<longrightarrow> P xa) \<and>
    INFIMUM (S \<inter> ball x d - {x}) f \<le> INFIMUM (Collect P) f"
    by (intro exI[of _ "\<lambda>y. y \<in> S \<inter> ball x d - {x}"])
       (auto intro!: INF_mono exI[of _ d] simp: dist_commute)
qed

lemma Limsup_within:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Limsup (at x within S) f = (INF e:{0<..}. SUP y:(S \<inter> ball x e - {x}). f y)"
  unfolding Limsup_def eventually_at
proof (rule INF_eq, simp_all add: Ball_def Bex_def, safe)
  fix P d
  assume "0 < d" and "\<forall>y. y \<in> S \<longrightarrow> y \<noteq> x \<and> dist y x < d \<longrightarrow> P y"
  then have "S \<inter> ball x d - {x} \<subseteq> {x. P x}"
    by (auto simp: zero_less_dist_iff dist_commute)
  then show "\<exists>r>0. SUPREMUM (S \<inter> ball x r - {x}) f \<le> SUPREMUM (Collect P) f"
    by (intro exI[of _ d] SUP_mono conjI \<open>0 < d\<close>) auto
next
  fix d :: real
  assume "0 < d"
  then show "\<exists>P. (\<exists>d>0. \<forall>xa. xa \<in> S \<longrightarrow> xa \<noteq> x \<and> dist xa x < d \<longrightarrow> P xa) \<and>
    SUPREMUM (Collect P) f \<le> SUPREMUM (S \<inter> ball x d - {x}) f"
    by (intro exI[of _ "\<lambda>y. y \<in> S \<inter> ball x d - {x}"])
       (auto intro!: SUP_mono exI[of _ d] simp: dist_commute)
qed

lemma Liminf_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Liminf (at x) f = (SUP e:{0<..}. INF y:(ball x e - {x}). f y)"
  using Liminf_within[of x UNIV f] by simp

lemma Limsup_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Limsup (at x) f = (INF e:{0<..}. SUP y:(ball x e - {x}). f y)"
  using Limsup_within[of x UNIV f] by simp

lemma min_Liminf_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_linorder"
  shows "min (f x) (Liminf (at x) f) = (SUP e:{0<..}. INF y:ball x e. f y)"
  unfolding inf_min[symmetric] Liminf_at
  apply (subst inf_commute)
  apply (subst SUP_inf)
  apply (intro SUP_cong[OF refl])
  apply (cut_tac A="ball x xa - {x}" and B="{x}" and M=f in INF_union)
  apply (drule sym)
  apply auto
  apply (metis INF_absorb centre_in_ball)
  done

subsection \<open>monoset\<close>

definition (in order) mono_set:
  "mono_set S \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> x \<in> S \<longrightarrow> y \<in> S)"

lemma (in order) mono_greaterThan [intro, simp]: "mono_set {B<..}" unfolding mono_set by auto
lemma (in order) mono_atLeast [intro, simp]: "mono_set {B..}" unfolding mono_set by auto
lemma (in order) mono_UNIV [intro, simp]: "mono_set UNIV" unfolding mono_set by auto
lemma (in order) mono_empty [intro, simp]: "mono_set {}" unfolding mono_set by auto

lemma (in complete_linorder) mono_set_iff:
  fixes S :: "'a set"
  defines "a \<equiv> Inf S"
  shows "mono_set S \<longleftrightarrow> S = {a <..} \<or> S = {a..}" (is "_ = ?c")
proof
  assume "mono_set S"
  then have mono: "\<And>x y. x \<le> y \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S"
    by (auto simp: mono_set)
  show ?c
  proof cases
    assume "a \<in> S"
    show ?c
      using mono[OF _ \<open>a \<in> S\<close>]
      by (auto intro: Inf_lower simp: a_def)
  next
    assume "a \<notin> S"
    have "S = {a <..}"
    proof safe
      fix x assume "x \<in> S"
      then have "a \<le> x"
        unfolding a_def by (rule Inf_lower)
      then show "a < x"
        using \<open>x \<in> S\<close> \<open>a \<notin> S\<close> by (cases "a = x") auto
    next
      fix x assume "a < x"
      then obtain y where "y < x" "y \<in> S"
        unfolding a_def Inf_less_iff ..
      with mono[of y x] show "x \<in> S"
        by auto
    qed
    then show ?c ..
  qed
qed auto

lemma ereal_open_mono_set:
  fixes S :: "ereal set"
  shows "open S \<and> mono_set S \<longleftrightarrow> S = UNIV \<or> S = {Inf S <..}"
  by (metis Inf_UNIV atLeast_eq_UNIV_iff ereal_open_atLeast
    ereal_open_closed mono_set_iff open_ereal_greaterThan)

lemma ereal_closed_mono_set:
  fixes S :: "ereal set"
  shows "closed S \<and> mono_set S \<longleftrightarrow> S = {} \<or> S = {Inf S ..}"
  by (metis Inf_UNIV atLeast_eq_UNIV_iff closed_ereal_atLeast
    ereal_open_closed mono_empty mono_set_iff open_ereal_greaterThan)

lemma ereal_Liminf_Sup_monoset:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "Liminf net f =
    Sup {l. \<forall>S. open S \<longrightarrow> mono_set S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
    (is "_ = Sup ?A")
proof (safe intro!: Liminf_eqI complete_lattice_class.Sup_upper complete_lattice_class.Sup_least)
  fix P
  assume P: "eventually P net"
  fix S
  assume S: "mono_set S" "INFIMUM (Collect P) f \<in> S"
  {
    fix x
    assume "P x"
    then have "INFIMUM (Collect P) f \<le> f x"
      by (intro complete_lattice_class.INF_lower) simp
    with S have "f x \<in> S"
      by (simp add: mono_set)
  }
  with P show "eventually (\<lambda>x. f x \<in> S) net"
    by (auto elim: eventually_mono)
next
  fix y l
  assume S: "\<forall>S. open S \<longrightarrow> mono_set S \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net"
  assume P: "\<forall>P. eventually P net \<longrightarrow> INFIMUM (Collect P) f \<le> y"
  show "l \<le> y"
  proof (rule dense_le)
    fix B
    assume "B < l"
    then have "eventually (\<lambda>x. f x \<in> {B <..}) net"
      by (intro S[rule_format]) auto
    then have "INFIMUM {x. B < f x} f \<le> y"
      using P by auto
    moreover have "B \<le> INFIMUM {x. B < f x} f"
      by (intro INF_greatest) auto
    ultimately show "B \<le> y"
      by simp
  qed
qed

lemma ereal_Limsup_Inf_monoset:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "Limsup net f =
    Inf {l. \<forall>S. open S \<longrightarrow> mono_set (uminus ` S) \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
    (is "_ = Inf ?A")
proof (safe intro!: Limsup_eqI complete_lattice_class.Inf_lower complete_lattice_class.Inf_greatest)
  fix P
  assume P: "eventually P net"
  fix S
  assume S: "mono_set (uminus`S)" "SUPREMUM (Collect P) f \<in> S"
  {
    fix x
    assume "P x"
    then have "f x \<le> SUPREMUM (Collect P) f"
      by (intro complete_lattice_class.SUP_upper) simp
    with S(1)[unfolded mono_set, rule_format, of "- SUPREMUM (Collect P) f" "- f x"] S(2)
    have "f x \<in> S"
      by (simp add: inj_image_mem_iff) }
  with P show "eventually (\<lambda>x. f x \<in> S) net"
    by (auto elim: eventually_mono)
next
  fix y l
  assume S: "\<forall>S. open S \<longrightarrow> mono_set (uminus ` S) \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net"
  assume P: "\<forall>P. eventually P net \<longrightarrow> y \<le> SUPREMUM (Collect P) f"
  show "y \<le> l"
  proof (rule dense_ge)
    fix B
    assume "l < B"
    then have "eventually (\<lambda>x. f x \<in> {..< B}) net"
      by (intro S[rule_format]) auto
    then have "y \<le> SUPREMUM {x. f x < B} f"
      using P by auto
    moreover have "SUPREMUM {x. f x < B} f \<le> B"
      by (intro SUP_least) auto
    ultimately show "y \<le> B"
      by simp
  qed
qed

lemma liminf_bounded_open:
  fixes x :: "nat \<Rightarrow> ereal"
  shows "x0 \<le> liminf x \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> mono_set S \<longrightarrow> x0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. x n \<in> S))"
  (is "_ \<longleftrightarrow> ?P x0")
proof
  assume "?P x0"
  then show "x0 \<le> liminf x"
    unfolding ereal_Liminf_Sup_monoset eventually_sequentially
    by (intro complete_lattice_class.Sup_upper) auto
next
  assume "x0 \<le> liminf x"
  {
    fix S :: "ereal set"
    assume om: "open S" "mono_set S" "x0 \<in> S"
    {
      assume "S = UNIV"
      then have "\<exists>N. \<forall>n\<ge>N. x n \<in> S"
        by auto
    }
    moreover
    {
      assume "S \<noteq> UNIV"
      then obtain B where B: "S = {B<..}"
        using om ereal_open_mono_set by auto
      then have "B < x0"
        using om by auto
      then have "\<exists>N. \<forall>n\<ge>N. x n \<in> S"
        unfolding B
        using \<open>x0 \<le> liminf x\<close> liminf_bounded_iff
        by auto
    }
    ultimately have "\<exists>N. \<forall>n\<ge>N. x n \<in> S"
      by auto
  }
  then show "?P x0"
    by auto
qed

subsection "Relate extended reals and the indicator function"

lemma ereal_indicator_le_0: "(indicator S x::ereal) \<le> 0 \<longleftrightarrow> x \<notin> S"
  by (auto split: split_indicator simp: one_ereal_def)

lemma ereal_indicator: "ereal (indicator A x) = indicator A x"
  by (auto simp: indicator_def one_ereal_def)

lemma ereal_mult_indicator: "ereal (x * indicator A y) = ereal x * indicator A y"
  by (simp split: split_indicator)

lemma ereal_indicator_mult: "ereal (indicator A y * x) = indicator A y * ereal x"
  by (simp split: split_indicator)

lemma ereal_indicator_nonneg[simp, intro]: "0 \<le> (indicator A x ::ereal)"
  unfolding indicator_def by auto

lemma indicator_inter_arith_ereal: "indicator A x * indicator B x = (indicator (A \<inter> B) x :: ereal)"
  by (simp split: split_indicator)

end

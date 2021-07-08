(*  Title:      HOL/Analysis/Extended_Real_Limits.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

section \<open>Limits on the Extended Real Number Line\<close> (* TO FIX: perhaps put all Nonstandard Analysis related
topics together? *)

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

instance\<^marker>\<open>tag unimportant\<close> enat :: second_countable_topology
proof
  show "\<exists>B::enat set set. countable B \<and> open = generate_topology B"
  proof (intro exI conjI)
    show "countable (range lessThan \<union> range greaterThan::enat set set)"
      by auto
  qed (simp add: open_enat_def)
qed

instance\<^marker>\<open>tag unimportant\<close> ereal :: second_countable_topology
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
    then have "b \<in> {Inf S - e <..< Inf S + e}"
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
  shows "Liminf (at x within S) f = (SUP e\<in>{0<..}. INF y\<in>(S \<inter> ball x e - {x}). f y)"
  unfolding Liminf_def eventually_at
proof (rule SUP_eq, simp_all add: Ball_def Bex_def, safe)
  fix P d
  assume "0 < d" and "\<forall>y. y \<in> S \<longrightarrow> y \<noteq> x \<and> dist y x < d \<longrightarrow> P y"
  then have "S \<inter> ball x d - {x} \<subseteq> {x. P x}"
    by (auto simp: dist_commute)
  then show "\<exists>r>0. Inf (f ` (Collect P)) \<le> Inf (f ` (S \<inter> ball x r - {x}))"
    by (intro exI[of _ d] INF_mono conjI \<open>0 < d\<close>) auto
next
  fix d :: real
  assume "0 < d"
  then show "\<exists>P. (\<exists>d>0. \<forall>xa. xa \<in> S \<longrightarrow> xa \<noteq> x \<and> dist xa x < d \<longrightarrow> P xa) \<and>
    Inf (f ` (S \<inter> ball x d - {x})) \<le> Inf (f ` (Collect P))"
    by (intro exI[of _ "\<lambda>y. y \<in> S \<inter> ball x d - {x}"])
       (auto intro!: INF_mono exI[of _ d] simp: dist_commute)
qed

lemma Limsup_within:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Limsup (at x within S) f = (INF e\<in>{0<..}. SUP y\<in>(S \<inter> ball x e - {x}). f y)"
  unfolding Limsup_def eventually_at
proof (rule INF_eq, simp_all add: Ball_def Bex_def, safe)
  fix P d
  assume "0 < d" and "\<forall>y. y \<in> S \<longrightarrow> y \<noteq> x \<and> dist y x < d \<longrightarrow> P y"
  then have "S \<inter> ball x d - {x} \<subseteq> {x. P x}"
    by (auto simp: dist_commute)
  then show "\<exists>r>0. Sup (f ` (S \<inter> ball x r - {x})) \<le> Sup (f ` (Collect P))"
    by (intro exI[of _ d] SUP_mono conjI \<open>0 < d\<close>) auto
next
  fix d :: real
  assume "0 < d"
  then show "\<exists>P. (\<exists>d>0. \<forall>xa. xa \<in> S \<longrightarrow> xa \<noteq> x \<and> dist xa x < d \<longrightarrow> P xa) \<and>
    Sup (f ` (Collect P)) \<le> Sup (f ` (S \<inter> ball x d - {x}))"
    by (intro exI[of _ "\<lambda>y. y \<in> S \<inter> ball x d - {x}"])
       (auto intro!: SUP_mono exI[of _ d] simp: dist_commute)
qed

lemma Liminf_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Liminf (at x) f = (SUP e\<in>{0<..}. INF y\<in>(ball x e - {x}). f y)"
  using Liminf_within[of x UNIV f] by simp

lemma Limsup_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_lattice"
  shows "Limsup (at x) f = (INF e\<in>{0<..}. SUP y\<in>(ball x e - {x}). f y)"
  using Limsup_within[of x UNIV f] by simp

lemma min_Liminf_at:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::complete_linorder"
  shows "min (f x) (Liminf (at x) f) = (SUP e\<in>{0<..}. INF y\<in>ball x e. f y)"
  apply (simp add: inf_min [symmetric] Liminf_at)
  apply (subst inf_commute)
  apply (subst SUP_inf)
  apply auto
  apply (metis (no_types, lifting) INF_insert centre_in_ball greaterThan_iff image_cong inf_commute insert_Diff)
  done


subsection \<open>Extended-Real.thy\<close> (*FIX ME change title *)

lemma sum_constant_ereal:
  fixes a::ereal
  shows "(\<Sum>i\<in>I. a) = a * card I"
apply (cases "finite I", induct set: finite, simp_all)
apply (cases a, auto, metis (no_types, opaque_lifting) add.commute mult.commute semiring_normalization_rules(3))
done

lemma real_lim_then_eventually_real:
  assumes "(u \<longlongrightarrow> ereal l) F"
  shows "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F"
proof -
  have "ereal l \<in> {-\<infinity><..<(\<infinity>::ereal)}" by simp
  moreover have "open {-\<infinity><..<(\<infinity>::ereal)}" by simp
  ultimately have "eventually (\<lambda>n. u n \<in> {-\<infinity><..<(\<infinity>::ereal)}) F" using assms tendsto_def by blast
  moreover have "\<And>x. x \<in> {-\<infinity><..<(\<infinity>::ereal)} \<Longrightarrow> x = ereal(real_of_ereal x)" using ereal_real by auto
  ultimately show ?thesis by (metis (mono_tags, lifting) eventually_mono)
qed

lemma ereal_Inf_cmult:
  assumes "c>(0::real)"
  shows "Inf {ereal c * x |x. P x} = ereal c * Inf {x. P x}"
proof -
  have "(\<lambda>x::ereal. c * x) (Inf {x::ereal. P x}) = Inf ((\<lambda>x::ereal. c * x)`{x::ereal. P x})"
    apply (rule mono_bij_Inf)
    apply (simp add: assms ereal_mult_left_mono less_imp_le mono_def)
    apply (rule bij_betw_byWitness[of _ "\<lambda>x. (x::ereal) / c"], auto simp add: assms ereal_mult_divide)
    using assms ereal_divide_eq apply auto
    done
  then show ?thesis by (simp only: setcompr_eq_image[symmetric])
qed


subsubsection\<^marker>\<open>tag important\<close> \<open>Continuity of addition\<close>

text \<open>The next few lemmas remove an unnecessary assumption in \<open>tendsto_add_ereal\<close>, culminating
in \<open>tendsto_add_ereal_general\<close> which essentially says that the addition
is continuous on ereal times ereal, except at \<open>(-\<infinity>, \<infinity>)\<close> and \<open>(\<infinity>, -\<infinity>)\<close>.
It is much more convenient in many situations, see for instance the proof of
\<open>tendsto_sum_ereal\<close> below.\<close>

lemma tendsto_add_ereal_PInf:
  fixes y :: ereal
  assumes y: "y \<noteq> -\<infinity>"
  assumes f: "(f \<longlongrightarrow> \<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> \<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x > ereal C) F"
  proof (cases y)
    case (real r)
    have "y > y-1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x > y - 1) F" using g y order_tendsto_iff by auto
    moreover have "y-1 = ereal(real_of_ereal(y-1))"
      by (metis real ereal_eq_1(1) ereal_minus(1) real_of_ereal.simps(1))
    ultimately have "eventually (\<lambda>x. g x > ereal(real_of_ereal(y - 1))) F" by simp
    then show ?thesis by auto
  next
    case (PInf)
    have "eventually (\<lambda>x. g x > ereal 0) F" using g PInf by (simp add: tendsto_PInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x > ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x > ereal(M - C)) F" using f by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > ereal (M-C)) \<and> (g x > ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x > ereal (M-C)) \<and> (g x > ereal C)) \<Longrightarrow> (f x + g x > ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x > ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_PInfty)
qed

text\<open>One would like to deduce the next lemma from the previous one, but the fact
that \<open>- (x + y)\<close> is in general different from \<open>(- x) + (- y)\<close> in ereal creates difficulties,
so it is more efficient to copy the previous proof.\<close>

lemma tendsto_add_ereal_MInf:
  fixes y :: ereal
  assumes y: "y \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> -\<infinity>) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> -\<infinity>) F"
proof -
  have "\<exists>C. eventually (\<lambda>x. g x < ereal C) F"
  proof (cases y)
    case (real r)
    have "y < y+1" using y real by (simp add: ereal_between(1))
    then have "eventually (\<lambda>x. g x < y + 1) F" using g y order_tendsto_iff by force
    moreover have "y+1 = ereal(real_of_ereal (y+1))" by (simp add: real)
    ultimately have "eventually (\<lambda>x. g x < ereal(real_of_ereal(y + 1))) F" by simp
    then show ?thesis by auto
  next
    case (MInf)
    have "eventually (\<lambda>x. g x < ereal 0) F" using g MInf by (simp add: tendsto_MInfty)
    then show ?thesis by auto
  qed (simp add: y)
  then obtain C::real where ge: "eventually (\<lambda>x. g x < ereal C) F" by auto

  {
    fix M::real
    have "eventually (\<lambda>x. f x < ereal(M - C)) F" using f by (simp add: tendsto_MInfty)
    then have "eventually (\<lambda>x. (f x < ereal (M- C)) \<and> (g x < ereal C)) F"
      by (auto simp add: ge eventually_conj_iff)
    moreover have "\<And>x. ((f x < ereal (M-C)) \<and> (g x < ereal C)) \<Longrightarrow> (f x + g x < ereal M)"
      using ereal_add_strict_mono2 by fastforce
    ultimately have "eventually (\<lambda>x. f x + g x < ereal M) F" using eventually_mono by force
  }
  then show ?thesis by (simp add: tendsto_MInfty)
qed

lemma tendsto_add_ereal_general1:
  fixes x y :: ereal
  assumes y: "\<bar>y\<bar> \<noteq> \<infinity>"
  assumes f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  have a: "\<bar>x\<bar> \<noteq> \<infinity>" by (simp add: real)
  show ?thesis by (rule tendsto_add_ereal[OF a, OF y, OF f, OF g])
next
  case PInf
  then show ?thesis using tendsto_add_ereal_PInf assms by force
next
  case MInf
  then show ?thesis using tendsto_add_ereal_MInf assms
    by (metis abs_ereal.simps(3) ereal_MInfty_eq_plus)
qed

lemma tendsto_add_ereal_general2:
  fixes x y :: ereal
  assumes x: "\<bar>x\<bar> \<noteq> \<infinity>"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof -
  have "((\<lambda>x. g x + f x) \<longlongrightarrow> x + y) F"
    using tendsto_add_ereal_general1[OF x, OF g, OF f] add.commute[of "y", of "x"] by simp
  moreover have "\<And>x. g x + f x = f x + g x" using add.commute by auto
  ultimately show ?thesis by simp
qed

text \<open>The next lemma says that the addition is continuous on \<open>ereal\<close>, except at
the pairs \<open>(-\<infinity>, \<infinity>)\<close> and \<open>(\<infinity>, -\<infinity>)\<close>.\<close>

lemma tendsto_add_ereal_general [tendsto_intros]:
  fixes x y :: ereal
  assumes "\<not>((x=\<infinity> \<and> y=-\<infinity>) \<or> (x=-\<infinity> \<and> y=\<infinity>))"
      and f: "(f \<longlongrightarrow> x) F" and g: "(g \<longlongrightarrow> y) F"
  shows "((\<lambda>x. f x + g x) \<longlongrightarrow> x + y) F"
proof (cases x)
  case (real r)
  show ?thesis
    apply (rule tendsto_add_ereal_general2) using real assms by auto
next
  case (PInf)
  then have "y \<noteq> -\<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_PInf PInf assms by auto
next
  case (MInf)
  then have "y \<noteq> \<infinity>" using assms by simp
  then show ?thesis using tendsto_add_ereal_MInf MInf f g by (metis ereal_MInfty_eq_plus)
qed

subsubsection\<^marker>\<open>tag important\<close> \<open>Continuity of multiplication\<close>

text \<open>In the same way as for addition, we prove that the multiplication is continuous on
ereal times ereal, except at \<open>(\<infinity>, 0)\<close> and \<open>(-\<infinity>, 0)\<close> and \<open>(0, \<infinity>)\<close> and \<open>(0, -\<infinity>)\<close>,
starting with specific situations.\<close>

lemma tendsto_mult_real_ereal:
  assumes "(u \<longlongrightarrow> ereal l) F" "(v \<longlongrightarrow> ereal m) F"
  shows "((\<lambda>n. u n * v n) \<longlongrightarrow> ereal l * ereal m) F"
proof -
  have ureal: "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) F" by (rule real_lim_then_eventually_real[OF assms(1)])
  then have "((\<lambda>n. ereal(real_of_ereal(u n))) \<longlongrightarrow> ereal l) F" using assms by auto
  then have limu: "((\<lambda>n. real_of_ereal(u n)) \<longlongrightarrow> l) F" by auto
  have vreal: "eventually (\<lambda>n. v n = ereal(real_of_ereal(v n))) F" by (rule real_lim_then_eventually_real[OF assms(2)])
  then have "((\<lambda>n. ereal(real_of_ereal(v n))) \<longlongrightarrow> ereal m) F" using assms by auto
  then have limv: "((\<lambda>n. real_of_ereal(v n)) \<longlongrightarrow> m) F" by auto

  {
    fix n assume "u n = ereal(real_of_ereal(u n))" "v n = ereal(real_of_ereal(v n))"
    then have "ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n" by (metis times_ereal.simps(1))
  }
  then have *: "eventually (\<lambda>n. ereal(real_of_ereal(u n) * real_of_ereal(v n)) = u n * v n) F"
    using eventually_elim2[OF ureal vreal] by auto

  have "((\<lambda>n. real_of_ereal(u n) * real_of_ereal(v n)) \<longlongrightarrow> l * m) F" using tendsto_mult[OF limu limv] by auto
  then have "((\<lambda>n. ereal(real_of_ereal(u n)) * real_of_ereal(v n)) \<longlongrightarrow> ereal(l * m)) F" by auto
  then show ?thesis using * filterlim_cong by fastforce
qed

lemma tendsto_mult_ereal_PInf:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "l>0" "(g \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> \<infinity>) F"
proof -
  obtain a::real where "0 < ereal a" "a < l" using assms(2) using ereal_dense2 by blast
  have *: "eventually (\<lambda>x. f x > a) F" using \<open>a < l\<close> assms(1) by (simp add: order_tendsto_iff)
  {
    fix K::real
    define M where "M = max K 1"
    then have "M > 0" by simp
    then have "ereal(M/a) > 0" using \<open>ereal a > 0\<close> by simp
    then have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > ereal a * ereal(M/a))"
      using ereal_mult_mono_strict'[where ?c = "M/a", OF \<open>0 < ereal a\<close>] by auto
    moreover have "ereal a * ereal(M/a) = M" using \<open>ereal a > 0\<close> by simp
    ultimately have "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > M)" by simp
    moreover have "M \<ge> K" unfolding M_def by simp
    ultimately have Imp: "\<And>x. ((f x > a) \<and> (g x > M/a)) \<Longrightarrow> (f x * g x > K)"
      using ereal_less_eq(3) le_less_trans by blast

    have "eventually (\<lambda>x. g x > M/a) F" using assms(3) by (simp add: tendsto_PInfty)
    then have "eventually (\<lambda>x. (f x > a) \<and> (g x > M/a)) F"
      using * by (auto simp add: eventually_conj_iff)
    then have "eventually (\<lambda>x. f x * g x > K) F" using eventually_mono Imp by force
  }
  then show ?thesis by (auto simp add: tendsto_PInfty)
qed

lemma tendsto_mult_ereal_pos:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "l>0" "m>0"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume *: "l = \<infinity> \<or> m = \<infinity>"
  then show ?thesis
  proof (cases)
    assume "m = \<infinity>"
    then show ?thesis using tendsto_mult_ereal_PInf assms by auto
  next
    assume "\<not>(m = \<infinity>)"
    then have "l = \<infinity>" using * by simp
    then have "((\<lambda>x. g x * f x) \<longlongrightarrow> l * m) F" using tendsto_mult_ereal_PInf assms by auto
    moreover have "\<And>x. g x * f x = f x * g x" using mult.commute by auto
    ultimately show ?thesis by simp
  qed
next
  assume "\<not>(l = \<infinity> \<or> m = \<infinity>)"
  then have "l < \<infinity>" "m < \<infinity>" by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr"
    using \<open>l>0\<close> \<open>m>0\<close> by (metis ereal_cases ereal_less(6) not_less_iff_gr_or_eq)
  then show ?thesis using tendsto_mult_real_ereal assms by auto
qed

text \<open>We reduce the general situation to the positive case by multiplying by suitable signs.
Unfortunately, as ereal is not a ring, all the neat sign lemmas are not available there. We
give the bare minimum we need.\<close>

lemma ereal_sgn_abs:
  fixes l::ereal
  shows "sgn(l) * l = abs(l)"
apply (cases l) by (auto simp add: sgn_if ereal_less_uminus_reorder)

lemma sgn_squared_ereal:
  assumes "l \<noteq> (0::ereal)"
  shows "sgn(l) * sgn(l) = 1"
apply (cases l) using assms by (auto simp add: one_ereal_def sgn_if)

lemma tendsto_mult_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "\<not>((l=0 \<and> abs(m) = \<infinity>) \<or> (m=0 \<and> abs(l) = \<infinity>))"
  shows "((\<lambda>x. f x * g x) \<longlongrightarrow> l * m) F"
proof (cases)
  assume "l=0 \<or> m=0"
  then have "abs(l) \<noteq> \<infinity>" "abs(m) \<noteq> \<infinity>" using assms(3) by auto
  then obtain lr mr where "l = ereal lr" "m = ereal mr" by auto
  then show ?thesis using tendsto_mult_real_ereal assms by auto
next
  have sgn_finite: "\<And>a::ereal. abs(sgn a) \<noteq> \<infinity>"
    by (metis MInfty_neq_ereal(2) PInfty_neq_ereal(2) abs_eq_infinity_cases ereal_times(1) ereal_times(3) ereal_uminus_eq_reorder sgn_ereal.elims)
  then have sgn_finite2: "\<And>a b::ereal. abs(sgn a * sgn b) \<noteq> \<infinity>"
    by (metis abs_eq_infinity_cases abs_ereal.simps(2) abs_ereal.simps(3) ereal_mult_eq_MInfty ereal_mult_eq_PInfty)
  assume "\<not>(l=0 \<or> m=0)"
  then have "l \<noteq> 0" "m \<noteq> 0" by auto
  then have "abs(l) > 0" "abs(m) > 0"
    by (metis abs_ereal_ge0 abs_ereal_less0 abs_ereal_pos ereal_uminus_uminus ereal_uminus_zero less_le not_less)+
  then have "sgn(l) * l > 0" "sgn(m) * m > 0" using ereal_sgn_abs by auto
  moreover have "((\<lambda>x. sgn(l) * f x) \<longlongrightarrow> (sgn(l) * l)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(1))
  moreover have "((\<lambda>x. sgn(m) * g x) \<longlongrightarrow> (sgn(m) * m)) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite assms(2))
  ultimately have *: "((\<lambda>x. (sgn(l) * f x) * (sgn(m) * g x)) \<longlongrightarrow> (sgn(l) * l) * (sgn(m) * m)) F"
    using tendsto_mult_ereal_pos by force
  have "((\<lambda>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x))) \<longlongrightarrow> (sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m))) F"
    by (rule tendsto_cmult_ereal, auto simp add: sgn_finite2 *)
  moreover have "\<And>x. (sgn(l) * sgn(m)) * ((sgn(l) * f x) * (sgn(m) * g x)) = f x * g x"
    by (metis mult.left_neutral sgn_squared_ereal[OF \<open>l \<noteq> 0\<close>] sgn_squared_ereal[OF \<open>m \<noteq> 0\<close>] mult.assoc mult.commute)
  moreover have "(sgn(l) * sgn(m)) * ((sgn(l) * l) * (sgn(m) * m)) = l * m"
    by (metis mult.left_neutral sgn_squared_ereal[OF \<open>l \<noteq> 0\<close>] sgn_squared_ereal[OF \<open>m \<noteq> 0\<close>] mult.assoc mult.commute)
  ultimately show ?thesis by auto
qed

lemma tendsto_cmult_ereal_general [tendsto_intros]:
  fixes f::"_ \<Rightarrow> ereal" and c::ereal
  assumes "(f \<longlongrightarrow> l) F" "\<not> (l=0 \<and> abs(c) = \<infinity>)"
  shows "((\<lambda>x. c * f x) \<longlongrightarrow> c * l) F"
by (cases "c = 0", auto simp add: assms tendsto_mult_ereal)


subsubsection\<^marker>\<open>tag important\<close> \<open>Continuity of division\<close>

lemma tendsto_inverse_ereal_PInf:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> \<infinity>) F"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 0) F"
proof -
  {
    fix e::real assume "e>0"
    have "1/e < \<infinity>" by auto
    then have "eventually (\<lambda>n. u n > 1/e) F" using assms(1) by (simp add: tendsto_PInfty)
    moreover
    {
      fix z::ereal assume "z>1/e"
      then have "z>0" using \<open>e>0\<close> using less_le_trans not_le by fastforce
      then have "1/z \<ge> 0" by auto
      moreover have "1/z < e" using \<open>e>0\<close> \<open>z>1/e\<close>
        apply (cases z) apply auto
        by (metis (mono_tags, opaque_lifting) less_ereal.simps(2) less_ereal.simps(4) divide_less_eq ereal_divide_less_pos ereal_less(4)
            ereal_less_eq(4) less_le_trans mult_eq_0_iff not_le not_one_less_zero times_ereal.simps(1))
      ultimately have "1/z \<ge> 0" "1/z < e" by auto
    }
    ultimately have "eventually (\<lambda>n. 1/u n<e) F" "eventually (\<lambda>n. 1/u n\<ge>0) F" by (auto simp add: eventually_mono)
  } note * = this
  show ?thesis
  proof (subst order_tendsto_iff, auto)
    fix a::ereal assume "a<0"
    then show "eventually (\<lambda>n. 1/u n > a) F" using *(2) eventually_mono less_le_trans linordered_field_no_ub by fastforce
  next
    fix a::ereal assume "a>0"
    then obtain e::real where "e>0" "a>e" using ereal_dense2 ereal_less(2) by blast
    then have "eventually (\<lambda>n. 1/u n < e) F" using *(1) by auto
    then show "eventually (\<lambda>n. 1/u n < a) F" using \<open>a>e\<close> by (metis (mono_tags, lifting) eventually_mono less_trans)
  qed
qed

text \<open>The next lemma deserves to exist by itself, as it is so common and useful.\<close>

lemma tendsto_inverse_real [tendsto_intros]:
  fixes u::"_ \<Rightarrow> real"
  shows "(u \<longlongrightarrow> l) F \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> ((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
  using tendsto_inverse unfolding inverse_eq_divide .

lemma tendsto_inverse_ereal [tendsto_intros]:
  fixes u::"_ \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> l) F" "l \<noteq> 0"
  shows "((\<lambda>x. 1/ u x) \<longlongrightarrow> 1/l) F"
proof (cases l)
  case (real r)
  then have "r \<noteq> 0" using assms(2) by auto
  then have "1/l = ereal(1/r)" using real by (simp add: one_ereal_def)
  define v where "v = (\<lambda>n. real_of_ereal(u n))"
  have ureal: "eventually (\<lambda>n. u n = ereal(v n)) F" unfolding v_def using real_lim_then_eventually_real assms(1) real by auto
  then have "((\<lambda>n. ereal(v n)) \<longlongrightarrow> ereal r) F" using assms real v_def by auto
  then have *: "((\<lambda>n. v n) \<longlongrightarrow> r) F" by auto
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 1/r) F" using \<open>r \<noteq> 0\<close> tendsto_inverse_real by auto
  then have lim: "((\<lambda>n. ereal(1/v n)) \<longlongrightarrow> 1/l) F" using \<open>1/l = ereal(1/r)\<close> by auto

  have "r \<in> -{0}" "open (-{(0::real)})" using \<open>r \<noteq> 0\<close> by auto
  then have "eventually (\<lambda>n. v n \<in> -{0}) F" using * using topological_tendstoD by blast
  then have "eventually (\<lambda>n. v n \<noteq> 0) F" by auto
  moreover
  {
    fix n assume H: "v n \<noteq> 0" "u n = ereal(v n)"
    then have "ereal(1/v n) = 1/ereal(v n)" by (simp add: one_ereal_def)
    then have "ereal(1/v n) = 1/u n" using H(2) by simp
  }
  ultimately have "eventually (\<lambda>n. ereal(1/v n) = 1/u n) F" using ureal eventually_elim2 by force
  with Lim_transform_eventually[OF lim this] show ?thesis by simp
next
  case (PInf)
  then have "1/l = 0" by auto
  then show ?thesis using tendsto_inverse_ereal_PInf assms PInf by auto
next
  case (MInf)
  then have "1/l = 0" by auto
  have "1/z = -1/ -z" if "z < 0" for z::ereal
    apply (cases z) using divide_ereal_def \<open> z < 0 \<close> by auto
  moreover have "eventually (\<lambda>n. u n < 0) F" by (metis (no_types) MInf assms(1) tendsto_MInfty zero_ereal_def)
  ultimately have *: "eventually (\<lambda>n. -1/-u n = 1/u n) F" by (simp add: eventually_mono)

  define v where "v = (\<lambda>n. - u n)"
  have "(v \<longlongrightarrow> \<infinity>) F" unfolding v_def using MInf assms(1) tendsto_uminus_ereal by fastforce
  then have "((\<lambda>n. 1/v n) \<longlongrightarrow> 0) F" using tendsto_inverse_ereal_PInf by auto
  then have "((\<lambda>n. -1/v n) \<longlongrightarrow> 0) F" using tendsto_uminus_ereal by fastforce
  then show ?thesis unfolding v_def using Lim_transform_eventually[OF _ *] \<open> 1/l = 0 \<close> by auto
qed

lemma tendsto_divide_ereal [tendsto_intros]:
  fixes f g::"_ \<Rightarrow> ereal"
  assumes "(f \<longlongrightarrow> l) F" "(g \<longlongrightarrow> m) F" "m \<noteq> 0" "\<not>(abs(l) = \<infinity> \<and> abs(m) = \<infinity>)"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> l / m) F"
proof -
  define h where "h = (\<lambda>x. 1/ g x)"
  have *: "(h \<longlongrightarrow> 1/m) F" unfolding h_def using assms(2) assms(3) tendsto_inverse_ereal by auto
  have "((\<lambda>x. f x * h x) \<longlongrightarrow> l * (1/m)) F"
    apply (rule tendsto_mult_ereal[OF assms(1) *]) using assms(3) assms(4) by (auto simp add: divide_ereal_def)
  moreover have "f x * h x = f x / g x" for x unfolding h_def by (simp add: divide_ereal_def)
  moreover have "l * (1/m) = l/m" by (simp add: divide_ereal_def)
  ultimately show ?thesis unfolding h_def using Lim_transform_eventually by auto
qed


subsubsection \<open>Further limits\<close>

text \<open>The assumptions of @{thm tendsto_diff_ereal} are too strong, we weaken them here.\<close>

lemma tendsto_diff_ereal_general [tendsto_intros]:
  fixes u v::"'a \<Rightarrow> ereal"
  assumes "(u \<longlongrightarrow> l) F" "(v \<longlongrightarrow> m) F" "\<not>((l = \<infinity> \<and> m = \<infinity>) \<or> (l = -\<infinity> \<and> m = -\<infinity>))"
  shows "((\<lambda>n. u n - v n) \<longlongrightarrow> l - m) F"
proof -
  have "((\<lambda>n. u n + (-v n)) \<longlongrightarrow> l + (-m)) F"
    apply (intro tendsto_intros assms) using assms by (auto simp add: ereal_uminus_eq_reorder)
  then show ?thesis by (simp add: minus_ereal_def)
qed

lemma id_nat_ereal_tendsto_PInf [tendsto_intros]:
  "(\<lambda> n::nat. real n) \<longlonglongrightarrow> \<infinity>"
by (simp add: filterlim_real_sequentially tendsto_PInfty_eq_at_top)

lemma tendsto_at_top_pseudo_inverse [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Inf {N. u N \<ge> n} :> at_top"
proof -
  {
    fix C::nat
    define M where "M = Max {u n| n. n \<le> C}+1"
    {
      fix n assume "n \<ge> M"
      have "eventually (\<lambda>N. u N \<ge> n) sequentially" using assms
        by (simp add: filterlim_at_top)
      then have *: "{N. u N \<ge> n} \<noteq> {}" by force

      have "N > C" if "u N \<ge> n" for N
      proof (rule ccontr)
        assume "\<not>(N > C)"
        have "u N \<le> Max {u n| n. n \<le> C}"
          apply (rule Max_ge) using \<open>\<not>(N > C)\<close> by auto
        then show False using \<open>u N \<ge> n\<close> \<open>n \<ge> M\<close> unfolding M_def by auto
      qed
      then have **: "{N. u N \<ge> n} \<subseteq> {C..}" by fastforce
      have "Inf {N. u N \<ge> n} \<ge> C"
        by (metis "*" "**" Inf_nat_def1 atLeast_iff subset_eq)
    }
    then have "eventually (\<lambda>n. Inf {N. u N \<ge> n} \<ge> C) sequentially"
      using eventually_sequentially by auto
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma pseudo_inverse_finite_set:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "finite {N. u N \<le> n}"
proof -
  fix n
  have "eventually (\<lambda>N. u N \<ge> n+1) sequentially" using assms
    by (simp add: filterlim_at_top)
  then obtain N1 where N1: "\<And>N. N \<ge> N1 \<Longrightarrow> u N \<ge> n + 1"
    using eventually_sequentially by auto
  have "{N. u N \<le> n} \<subseteq> {..<N1}"
    apply auto using N1 by (metis Suc_eq_plus1 not_less not_less_eq_eq)
  then show "finite {N. u N \<le> n}" by (simp add: finite_subset)
qed

lemma tendsto_at_top_pseudo_inverse2 [tendsto_intros]:
  fixes u::"nat \<Rightarrow> nat"
  assumes "LIM n sequentially. u n :> at_top"
  shows "LIM n sequentially. Max {N. u N \<le> n} :> at_top"
proof -
  {
    fix N0::nat
    have "N0 \<le> Max {N. u N \<le> n}" if "n \<ge> u N0" for n
      apply (rule Max.coboundedI) using pseudo_inverse_finite_set[OF assms] that by auto
    then have "eventually (\<lambda>n. N0 \<le> Max {N. u N \<le> n}) sequentially"
      using eventually_sequentially by blast
  }
  then show ?thesis using filterlim_at_top by auto
qed

lemma ereal_truncation_top [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. min x n) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. min x n = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: tendsto_eventually)
next
  case (PInf)
  then have "min x n = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
next
  case (MInf)
  then have "min x n = x" for n::nat by (auto simp add: min_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_top [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> - \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(min x n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "min x n = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(min x n) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(min x n) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(min x n)) \<longlonglongrightarrow> r" by (simp add: tendsto_eventually)
  then show ?thesis using real by auto
next
  case (PInf)
  then have "real_of_ereal(min x n) = n" for n::nat by (auto simp add: min_def)
  then show ?thesis using id_nat_ereal_tendsto_PInf PInf by auto
qed (simp add: assms)

lemma ereal_truncation_bottom [tendsto_intros]:
  fixes x::ereal
  shows "(\<lambda>n::nat. max x (- real n)) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "eventually (\<lambda>n. max x (-real n) = x) sequentially" using eventually_at_top_linorder by blast
  then show ?thesis by (simp add: tendsto_eventually)
next
  case (MInf)
  then have "max x (-real n) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
next
  case (PInf)
  then have "max x (-real n) = x" for n::nat by (auto simp add: max_def)
  then show ?thesis by auto
qed

lemma ereal_truncation_real_bottom [tendsto_intros]:
  fixes x::ereal
  assumes "x \<noteq> \<infinity>"
  shows "(\<lambda>n::nat. real_of_ereal(max x (- real n))) \<longlonglongrightarrow> x"
proof (cases x)
  case (real r)
  then obtain K::nat where "K>0" "K > abs(r)" using reals_Archimedean2 gr0I by auto
  then have "max x (-real n) = x" if "n \<ge> K" for n apply (subst real, subst real, auto) using that eq_iff by fastforce
  then have "real_of_ereal(max x (-real n)) = r" if "n \<ge> K" for n using real that by auto
  then have "eventually (\<lambda>n. real_of_ereal(max x (-real n)) = r) sequentially" using eventually_at_top_linorder by blast
  then have "(\<lambda>n. real_of_ereal(max x (-real n))) \<longlonglongrightarrow> r" by (simp add: tendsto_eventually)
  then show ?thesis using real by auto
next
  case (MInf)
  then have "real_of_ereal(max x (-real n)) = (-1)* ereal(real n)" for n::nat by (auto simp add: max_def)
  moreover have "(\<lambda>n. (-1)* ereal(real n)) \<longlonglongrightarrow> -\<infinity>"
    using tendsto_cmult_ereal[of "-1", OF _ id_nat_ereal_tendsto_PInf] by (simp add: one_ereal_def)
  ultimately show ?thesis using MInf by auto
qed (simp add: assms)

text \<open>the next one is copied from \<open>tendsto_sum\<close>.\<close>
lemma tendsto_sum_ereal [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i \<longlongrightarrow> a i) F"
          "\<And>i. abs(a i) \<noteq> \<infinity>"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) \<longlongrightarrow> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" then show ?thesis using assms
    by (induct, simp, simp add: tendsto_add_ereal_general2 assms)
qed(simp)


lemma continuous_ereal_abs:
  "continuous_on (UNIV::ereal set) abs"
proof -
  have "continuous_on ({..0} \<union> {(0::ereal)..}) abs"
    apply (rule continuous_on_closed_Un, auto)
    apply (rule iffD1[OF continuous_on_cong, of "{..0}" _ "\<lambda>x. -x"])
    using less_eq_ereal_def apply (auto simp add: continuous_uminus_ereal)
    apply (rule iffD1[OF continuous_on_cong, of "{0..}" _ "\<lambda>x. x"])
      apply (auto)
    done
  moreover have "(UNIV::ereal set) = {..0} \<union> {(0::ereal)..}" by auto
  ultimately show ?thesis by auto
qed

lemmas continuous_on_compose_ereal_abs[continuous_intros] =
  continuous_on_compose2[OF continuous_ereal_abs _ subset_UNIV]

lemma tendsto_abs_ereal [tendsto_intros]:
  assumes "(u \<longlongrightarrow> (l::ereal)) F"
  shows "((\<lambda>n. abs(u n)) \<longlongrightarrow> abs l) F"
using continuous_ereal_abs assms by (metis UNIV_I continuous_on tendsto_compose)

lemma ereal_minus_real_tendsto_MInf [tendsto_intros]:
  "(\<lambda>x. ereal (- real x)) \<longlonglongrightarrow> - \<infinity>"
by (subst uminus_ereal.simps(1)[symmetric], intro tendsto_intros)


subsection \<open>Extended-Nonnegative-Real.thy\<close> (*FIX title *)

lemma tendsto_diff_ennreal_general [tendsto_intros]:
  fixes u v::"'a \<Rightarrow> ennreal"
  assumes "(u \<longlongrightarrow> l) F" "(v \<longlongrightarrow> m) F" "\<not>(l = \<infinity> \<and> m = \<infinity>)"
  shows "((\<lambda>n. u n - v n) \<longlongrightarrow> l - m) F"
proof -
  have "((\<lambda>n. e2ennreal(enn2ereal(u n) - enn2ereal(v n))) \<longlongrightarrow> e2ennreal(enn2ereal l - enn2ereal m)) F"
    apply (intro tendsto_intros) using assms by  auto
  then show ?thesis by auto
qed

lemma tendsto_mult_ennreal [tendsto_intros]:
  fixes l m::ennreal
  assumes "(u \<longlongrightarrow> l) F" "(v \<longlongrightarrow> m) F" "\<not>((l = 0 \<and> m = \<infinity>) \<or> (l = \<infinity> \<and> m = 0))"
  shows "((\<lambda>n. u n * v n) \<longlongrightarrow> l * m) F"
proof -
  have "((\<lambda>n. e2ennreal(enn2ereal (u n) * enn2ereal (v n))) \<longlongrightarrow> e2ennreal(enn2ereal l * enn2ereal m)) F"
    apply (intro tendsto_intros) using assms apply auto
    using enn2ereal_inject zero_ennreal.rep_eq by fastforce+
  moreover have "e2ennreal(enn2ereal (u n) * enn2ereal (v n)) = u n * v n" for n
    by (subst times_ennreal.abs_eq[symmetric], auto simp add: eq_onp_same_args)
  moreover have "e2ennreal(enn2ereal l * enn2ereal m)  = l * m"
    by (subst times_ennreal.abs_eq[symmetric], auto simp add: eq_onp_same_args)
  ultimately show ?thesis
    by auto
qed


subsection \<open>monoset\<close> (*FIX ME title *)

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
  assume S: "mono_set S" "Inf (f ` (Collect P)) \<in> S"
  {
    fix x
    assume "P x"
    then have "Inf (f ` (Collect P)) \<le> f x"
      by (intro complete_lattice_class.INF_lower) simp
    with S have "f x \<in> S"
      by (simp add: mono_set)
  }
  with P show "eventually (\<lambda>x. f x \<in> S) net"
    by (auto elim: eventually_mono)
next
  fix y l
  assume S: "\<forall>S. open S \<longrightarrow> mono_set S \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net"
  assume P: "\<forall>P. eventually P net \<longrightarrow> Inf (f ` (Collect P)) \<le> y"
  show "l \<le> y"
  proof (rule dense_le)
    fix B
    assume "B < l"
    then have "eventually (\<lambda>x. f x \<in> {B <..}) net"
      by (intro S[rule_format]) auto
    then have "Inf (f ` {x. B < f x}) \<le> y"
      using P by auto
    moreover have "B \<le> Inf (f ` {x. B < f x})"
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
  assume S: "mono_set (uminus`S)" "Sup (f ` (Collect P)) \<in> S"
  {
    fix x
    assume "P x"
    then have "f x \<le> Sup (f ` (Collect P))"
      by (intro complete_lattice_class.SUP_upper) simp
    with S(1)[unfolded mono_set, rule_format, of "- Sup (f ` (Collect P))" "- f x"] S(2)
    have "f x \<in> S"
      by (simp add: inj_image_mem_iff) }
  with P show "eventually (\<lambda>x. f x \<in> S) net"
    by (auto elim: eventually_mono)
next
  fix y l
  assume S: "\<forall>S. open S \<longrightarrow> mono_set (uminus ` S) \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net"
  assume P: "\<forall>P. eventually P net \<longrightarrow> y \<le> Sup (f ` (Collect P))"
  show "y \<le> l"
  proof (rule dense_ge)
    fix B
    assume "l < B"
    then have "eventually (\<lambda>x. f x \<in> {..< B}) net"
      by (intro S[rule_format]) auto
    then have "y \<le> Sup (f ` {x. f x < B})"
      using P by auto
    moreover have "Sup (f ` {x. f x < B}) \<le> B"
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

lemma limsup_finite_then_bounded:
  fixes u::"nat \<Rightarrow> real"
  assumes "limsup u < \<infinity>"
  shows "\<exists>C. \<forall>n. u n \<le> C"
proof -
  obtain C where C: "limsup u < C" "C < \<infinity>" using assms ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n < C) sequentially" using C(1) unfolding Limsup_def
    apply (auto simp add: INF_less_iff)
    using SUP_lessD eventually_mono by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n < C" using eventually_sequentially by auto
  define D where "D = max (real_of_ereal C) (Max {u n |n. n \<le> N})"
  have "\<And>n. u n \<le> D"
  proof -
    fix n show "u n \<le> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<le> Max {u n |n. n \<le> N}" by (rule Max_ge, auto simp add: *)
      then show "u n \<le> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n < C" using N by auto
      then have "u n < real_of_ereal C" using \<open>C = ereal(real_of_ereal C)\<close> less_ereal.simps(1) by fastforce
      then show "u n \<le> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_finite_then_bounded_below:
  fixes u::"nat \<Rightarrow> real"
  assumes "liminf u > -\<infinity>"
  shows "\<exists>C. \<forall>n. u n \<ge> C"
proof -
  obtain C where C: "liminf u > C" "C > -\<infinity>" using assms using ereal_dense2 by blast
  then have "C = ereal(real_of_ereal C)" using ereal_real by force
  have "eventually (\<lambda>n. u n > C) sequentially" using C(1) unfolding Liminf_def
    apply (auto simp add: less_SUP_iff)
    using eventually_elim2 less_INF_D by fastforce
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n > C" using eventually_sequentially by auto
  define D where "D = min (real_of_ereal C) (Min {u n |n. n \<le> N})"
  have "\<And>n. u n \<ge> D"
  proof -
    fix n show "u n \<ge> D"
    proof (cases)
      assume *: "n \<le> N"
      have "u n \<ge> Min {u n |n. n \<le> N}" by (rule Min_le, auto simp add: *)
      then show "u n \<ge> D" unfolding D_def by linarith
    next
      assume "\<not>(n \<le> N)"
      then have "n \<ge> N" by simp
      then have "u n > C" using N by auto
      then have "u n > real_of_ereal C" using \<open>C = ereal(real_of_ereal C)\<close> less_ereal.simps(1) by fastforce
      then show "u n \<ge> D" unfolding D_def by linarith
    qed
  qed
  then show ?thesis by blast
qed

lemma liminf_upper_bound:
  fixes u:: "nat \<Rightarrow> ereal"
  assumes "liminf u < l"
  shows "\<exists>N>k. u N < l"
by (metis assms gt_ex less_le_trans liminf_bounded_iff not_less)

lemma limsup_shift:
  "limsup (\<lambda>n. u (n+1)) = limsup u"
proof -
  have "(SUP m\<in>{n+1..}. u m) = (SUP m\<in>{n..}. u (m + 1))" for n
    apply (rule SUP_eq) using Suc_le_D by auto
  then have a: "(INF n. SUP m\<in>{n..}. u (m + 1)) = (INF n. (SUP m\<in>{n+1..}. u m))" by auto
  have b: "(INF n. (SUP m\<in>{n+1..}. u m)) = (INF n\<in>{1..}. (SUP m\<in>{n..}. u m))"
    apply (rule INF_eq) using Suc_le_D by auto
  have "(INF n\<in>{1..}. v n) = (INF n. v n)" if "decseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule INF_eq) using \<open>decseq v\<close> decseq_Suc_iff by auto
  moreover have "decseq (\<lambda>n. (SUP m\<in>{n..}. u m))" by (simp add: SUP_subset_mono decseq_def)
  ultimately have c: "(INF n\<in>{1..}. (SUP m\<in>{n..}. u m)) = (INF n. (SUP m\<in>{n..}. u m))" by simp
  have "(INF n. Sup (u ` {n..})) = (INF n. SUP m\<in>{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: limsup_INF_SUP)
qed

lemma limsup_shift_k:
  "limsup (\<lambda>n. u (n+k)) = limsup u"
proof (induction k)
  case (Suc k)
  have "limsup (\<lambda>n. u (n+k+1)) = limsup (\<lambda>n. u (n+k))" using limsup_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma liminf_shift:
  "liminf (\<lambda>n. u (n+1)) = liminf u"
proof -
  have "(INF m\<in>{n+1..}. u m) = (INF m\<in>{n..}. u (m + 1))" for n
    apply (rule INF_eq) using Suc_le_D by (auto)
  then have a: "(SUP n. INF m\<in>{n..}. u (m + 1)) = (SUP n. (INF m\<in>{n+1..}. u m))" by auto
  have b: "(SUP n. (INF m\<in>{n+1..}. u m)) = (SUP n\<in>{1..}. (INF m\<in>{n..}. u m))"
    apply (rule SUP_eq) using Suc_le_D by (auto)
  have "(SUP n\<in>{1..}. v n) = (SUP n. v n)" if "incseq v" for v::"nat \<Rightarrow> 'a"
    apply (rule SUP_eq) using \<open>incseq v\<close> incseq_Suc_iff by auto
  moreover have "incseq (\<lambda>n. (INF m\<in>{n..}. u m))" by (simp add: INF_superset_mono mono_def)
  ultimately have c: "(SUP n\<in>{1..}. (INF m\<in>{n..}. u m)) = (SUP n. (INF m\<in>{n..}. u m))" by simp
  have "(SUP n. Inf (u ` {n..})) = (SUP n. INF m\<in>{n..}. u (m + 1))" using a b c by simp
  then show ?thesis by (auto cong: liminf_SUP_INF)
qed

lemma liminf_shift_k:
  "liminf (\<lambda>n. u (n+k)) = liminf u"
proof (induction k)
  case (Suc k)
  have "liminf (\<lambda>n. u (n+k+1)) = liminf (\<lambda>n. u (n+k))" using liminf_shift[where ?u="\<lambda>n. u(n+k)"] by simp
  then show ?case using Suc.IH by simp
qed (auto)

lemma Limsup_obtain:
  fixes u::"_ \<Rightarrow> 'a :: complete_linorder"
  assumes "Limsup F u > c"
  shows "\<exists>i. u i > c"
proof -
  have "(INF P\<in>{P. eventually P F}. SUP x\<in>{x. P x}. u x) > c" using assms by (simp add: Limsup_def)
  then show ?thesis by (metis eventually_True mem_Collect_eq less_INF_D less_SUP_iff)
qed

text \<open>The next lemma is extremely useful, as it often makes it possible to reduce statements
about limsups to statements about limits.\<close>

lemma limsup_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (u o r) \<longlonglongrightarrow> limsup u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<le> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<le> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r :: "nat \<Rightarrow> nat" where "strict_mono r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<le> u (r n)"
    by (auto simp: strict_mono_Suc_iff)
  define umax where "umax = (\<lambda>n. (SUP m\<in>{n..}. u m))"
  have "decseq umax" unfolding umax_def by (simp add: SUP_subset_mono antimono_def)
  then have "umax \<longlonglongrightarrow> limsup u" unfolding umax_def by (metis LIMSEQ_INF limsup_INF_SUP)
  then have *: "(umax o r) \<longlonglongrightarrow> limsup u" by (simp add: LIMSEQ_subseq_LIMSEQ \<open>strict_mono r\<close>)
  have "\<And>n. umax(r n) = u(r n)" unfolding umax_def using mono
    by (metis SUP_le_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umax o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using * by simp
  then show ?thesis using \<open>strict_mono r\<close> by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<le> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p < u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Max {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Max_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmax: "u p = Max{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p < u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] \<open>p \<in> {N<..x}\<close> by auto
    define y where "y = Inf U"
    then have "y \<in> U" using \<open>U \<noteq> {}\<close> by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<le> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<le> u p" using upmax by simp
    qed
    moreover have "u p < u y" using \<open>y \<in> U\<close> U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using \<open>y \<in> U\<close> U_def \<open>p \<in> {N<..x}\<close> by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<le> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<le> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using \<open>i \<in> {N<..y}\<close> by simp
        have "u i \<le> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using \<open>p \<in> {N<..x}\<close> by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<le> u y" using \<open>u p < u y\<close> by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" using \<open>y > x\<close> \<open>y > N\<close> by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<le> u y)" by auto
  qed (auto)
  then obtain r where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<le> u (r (Suc n)))" by auto
  have "strict_mono r" using r by (auto simp: strict_mono_Suc_iff)
  have "incseq (u o r)" unfolding o_def using r by (simp add: incseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)" using LIMSEQ_SUP by blast
  then have "limsup (u o r) = (SUP n. (u o r) n)" by (simp add: lim_imp_Limsup)
  moreover have "limsup (u o r) \<le> limsup u" using \<open>strict_mono r\<close> by (simp add: limsup_subseq_mono)
  ultimately have "(SUP n. (u o r) n) \<le> limsup u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using \<open>strict_mono r\<close> using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<le> u (r(Suc n))" using r by simp
    then have "u i \<le> (SUP n. (u o r) n)" unfolding o_def by (meson SUP_upper2 UNIV_I)
  }
  then have "(SUP i\<in>{N<..}. u i) \<le> (SUP n. (u o r) n)" using SUP_least by blast
  then have "limsup u \<le> (SUP n. (u o r) n)" unfolding Limsup_def
    by (metis (mono_tags, lifting) INF_lower2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "limsup u = (SUP n. (u o r) n)" using \<open>(SUP n. (u o r) n) \<le> limsup u\<close> by simp
  then have "(u o r) \<longlonglongrightarrow> limsup u" using \<open>(u o r) \<longlonglongrightarrow> (SUP n. (u o r) n)\<close> by simp
  then show ?thesis using \<open>strict_mono r\<close> by auto
qed

lemma liminf_subseq_lim:
  fixes u::"nat \<Rightarrow> 'a :: {complete_linorder, linorder_topology}"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (u o r) \<longlonglongrightarrow> liminf u"
proof (cases)
  assume "\<forall>n. \<exists>p>n. \<forall>m\<ge>p. u m \<ge> u p"
  then have "\<exists>r. \<forall>n. (\<forall>m\<ge>r n. u m \<ge> u (r n)) \<and> r n < r (Suc n)"
    by (intro dependent_nat_choice) (auto simp: conj_commute)
  then obtain r :: "nat \<Rightarrow> nat" where "strict_mono r" and mono: "\<And>n m. r n \<le> m \<Longrightarrow> u m \<ge> u (r n)"
    by (auto simp: strict_mono_Suc_iff)
  define umin where "umin = (\<lambda>n. (INF m\<in>{n..}. u m))"
  have "incseq umin" unfolding umin_def by (simp add: INF_superset_mono incseq_def)
  then have "umin \<longlonglongrightarrow> liminf u" unfolding umin_def by (metis LIMSEQ_SUP liminf_SUP_INF)
  then have *: "(umin o r) \<longlonglongrightarrow> liminf u" by (simp add: LIMSEQ_subseq_LIMSEQ \<open>strict_mono r\<close>)
  have "\<And>n. umin(r n) = u(r n)" unfolding umin_def using mono
    by (metis le_INF_iff antisym atLeast_def mem_Collect_eq order_refl)
  then have "umin o r = u o r" unfolding o_def by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using * by simp
  then show ?thesis using \<open>strict_mono r\<close> by blast
next
  assume "\<not> (\<forall>n. \<exists>p>n. (\<forall>m\<ge>p. u m \<ge> u p))"
  then obtain N where N: "\<And>p. p > N \<Longrightarrow> \<exists>m>p. u p > u m" by (force simp: not_le le_less)
  have "\<exists>r. \<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))"
  proof (rule dependent_nat_choice)
    fix x assume "N < x"
    then have a: "finite {N<..x}" "{N<..x} \<noteq> {}" by simp_all
    have "Min {u i |i. i \<in> {N<..x}} \<in> {u i |i. i \<in> {N<..x}}" apply (rule Min_in) using a by (auto)
    then obtain p where "p \<in> {N<..x}" and upmin: "u p = Min{u i |i. i \<in> {N<..x}}" by auto
    define U where "U = {m. m > p \<and> u p > u m}"
    have "U \<noteq> {}" unfolding U_def using N[of p] \<open>p \<in> {N<..x}\<close> by auto
    define y where "y = Inf U"
    then have "y \<in> U" using \<open>U \<noteq> {}\<close> by (simp add: Inf_nat_def1)
    have a: "\<And>i. i \<in> {N<..x} \<Longrightarrow> u i \<ge> u p"
    proof -
      fix i assume "i \<in> {N<..x}"
      then have "u i \<in> {u i |i. i \<in> {N<..x}}" by blast
      then show "u i \<ge> u p" using upmin by simp
    qed
    moreover have "u p > u y" using \<open>y \<in> U\<close> U_def by auto
    ultimately have "y \<notin> {N<..x}" using not_le by blast
    moreover have "y > N" using \<open>y \<in> U\<close> U_def \<open>p \<in> {N<..x}\<close> by auto
    ultimately have "y > x" by auto

    have "\<And>i. i \<in> {N<..y} \<Longrightarrow> u i \<ge> u y"
    proof -
      fix i assume "i \<in> {N<..y}" show "u i \<ge> u y"
      proof (cases)
        assume "i = y"
        then show ?thesis by simp
      next
        assume "\<not>(i=y)"
        then have i:"i \<in> {N<..<y}" using \<open>i \<in> {N<..y}\<close> by simp
        have "u i \<ge> u p"
        proof (cases)
          assume "i \<le> x"
          then have "i \<in> {N<..x}" using i by simp
          then show ?thesis using a by simp
        next
          assume "\<not>(i \<le> x)"
          then have "i > x" by simp
          then have *: "i > p" using \<open>p \<in> {N<..x}\<close> by simp
          have "i < Inf U" using i y_def by simp
          then have "i \<notin> U" using Inf_nat_def not_less_Least by auto
          then show ?thesis using U_def * by auto
        qed
        then show "u i \<ge> u y" using \<open>u p > u y\<close> by auto
      qed
    qed
    then have "N < y \<and> x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" using \<open>y > x\<close> \<open>y > N\<close> by auto
    then show "\<exists>y>N. x < y \<and> (\<forall>i\<in>{N<..y}. u i \<ge> u y)" by auto
  qed (auto)
  then obtain r :: "nat \<Rightarrow> nat" 
    where r: "\<forall>n. N < r n \<and> r n < r (Suc n) \<and> (\<forall>i\<in> {N<..r (Suc n)}. u i \<ge> u (r (Suc n)))" by auto
  have "strict_mono r" using r by (auto simp: strict_mono_Suc_iff)
  have "decseq (u o r)" unfolding o_def using r by (simp add: decseq_SucI order.strict_implies_order)
  then have "(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)" using LIMSEQ_INF by blast
  then have "liminf (u o r) = (INF n. (u o r) n)" by (simp add: lim_imp_Liminf)
  moreover have "liminf (u o r) \<ge> liminf u" using \<open>strict_mono r\<close> by (simp add: liminf_subseq_mono)
  ultimately have "(INF n. (u o r) n) \<ge> liminf u" by simp

  {
    fix i assume i: "i \<in> {N<..}"
    obtain n where "i < r (Suc n)" using \<open>strict_mono r\<close> using Suc_le_eq seq_suble by blast
    then have "i \<in> {N<..r(Suc n)}" using i by simp
    then have "u i \<ge> u (r(Suc n))" using r by simp
    then have "u i \<ge> (INF n. (u o r) n)" unfolding o_def by (meson INF_lower2 UNIV_I)
  }
  then have "(INF i\<in>{N<..}. u i) \<ge> (INF n. (u o r) n)" using INF_greatest by blast
  then have "liminf u \<ge> (INF n. (u o r) n)" unfolding Liminf_def
    by (metis (mono_tags, lifting) SUP_upper2 atLeast_Suc_greaterThan atLeast_def eventually_ge_at_top mem_Collect_eq)
  then have "liminf u = (INF n. (u o r) n)" using \<open>(INF n. (u o r) n) \<ge> liminf u\<close> by simp
  then have "(u o r) \<longlonglongrightarrow> liminf u" using \<open>(u o r) \<longlonglongrightarrow> (INF n. (u o r) n)\<close> by simp
  then show ?thesis using \<open>strict_mono r\<close> by auto
qed

text \<open>The following statement about limsups is reduced to a statement about limits using
subsequences thanks to \<open>limsup_subseq_lim\<close>. The statement for limits follows for instance from
\<open>tendsto_add_ereal_general\<close>.\<close>

lemma ereal_limsup_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
proof (cases)
  assume "(limsup u = \<infinity>) \<or> (limsup v = \<infinity>)"
  then have "limsup u + limsup v = \<infinity>" by simp
  then show ?thesis by auto
next
  assume "\<not>((limsup u = \<infinity>) \<or> (limsup v = \<infinity>))"
  then have "limsup u < \<infinity>" "limsup v < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "strict_mono r" "(w o r) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  obtain s where s: "strict_mono s" "(u o r o s) \<longlonglongrightarrow> limsup (u o r)" using limsup_subseq_lim by auto
  obtain t where t: "strict_mono t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "strict_mono a" using r s t by (simp add: a_def strict_mono_o)
  have l:"(w o a) \<longlonglongrightarrow> limsup w"
         "(u o a) \<longlonglongrightarrow> limsup (u o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "limsup (u o r) \<le> limsup u" by (simp add: limsup_subseq_mono r(1))
  then have a: "limsup (u o r) \<noteq> \<infinity>" using \<open>limsup u < \<infinity>\<close> by auto
  have "limsup (v o r o s) \<le> limsup v" 
    by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) strict_mono_o)
  then have b: "limsup (v o r o s) \<noteq> \<infinity>" using \<open>limsup v < \<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> limsup (u o r) + limsup (v o r o s)" by simp
  then have "limsup w = limsup (u o r) + limsup (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "limsup w \<le> limsup u + limsup v"
    using \<open>limsup (u o r) \<le> limsup u\<close> \<open>limsup (v o r o s) \<le> limsup v\<close> add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

text \<open>There is an asymmetry between liminfs and limsups in \<open>ereal\<close>, as \<open>\<infinity> + (-\<infinity>) = \<infinity>\<close>.
This explains why there are more assumptions in the next lemma dealing with liminfs that in the
previous one about limsups.\<close>

lemma ereal_liminf_add_mono:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "\<not>((liminf u = \<infinity> \<and> liminf v = -\<infinity>) \<or> (liminf u = -\<infinity> \<and> liminf v = \<infinity>))"
  shows "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
proof (cases)
  assume "(liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>)"
  then have *: "liminf u + liminf v = -\<infinity>" using assms by auto
  show ?thesis by (simp add: *)
next
  assume "\<not>((liminf u = -\<infinity>) \<or> (liminf v = -\<infinity>))"
  then have "liminf u > -\<infinity>" "liminf v > -\<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "strict_mono r" "(w o r) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  obtain s where s: "strict_mono s" "(u o r o s) \<longlonglongrightarrow> liminf (u o r)" using liminf_subseq_lim by auto
  obtain t where t: "strict_mono t" "(v o r o s o t) \<longlonglongrightarrow> liminf (v o r o s)" using liminf_subseq_lim by auto

  define a where "a = r o s o t"
  have "strict_mono a" using r s t by (simp add: a_def strict_mono_o)
  have l:"(w o a) \<longlonglongrightarrow> liminf w"
         "(u o a) \<longlonglongrightarrow> liminf (u o r)"
         "(v o a) \<longlonglongrightarrow> liminf (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (u o r) \<ge> liminf u" by (simp add: liminf_subseq_mono r(1))
  then have a: "liminf (u o r) \<noteq> -\<infinity>" using \<open>liminf u > -\<infinity>\<close> by auto
  have "liminf (v o r o s) \<ge> liminf v" 
    by (simp add: comp_assoc liminf_subseq_mono r(1) s(1) strict_mono_o)
  then have b: "liminf (v o r o s) \<noteq> -\<infinity>" using \<open>liminf v > -\<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)"
    using l tendsto_add_ereal_general a b by fastforce
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf (u o r) + liminf (v o r o s)" by simp
  then have "liminf w = liminf (u o r) + liminf (v o r o s)" using l(1) LIMSEQ_unique by blast
  then have "liminf w \<ge> liminf u + liminf v"
    using \<open>liminf (u o r) \<ge> liminf u\<close> \<open>liminf (v o r o s) \<ge> liminf v\<close> add_mono by simp
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_limsup_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n + v n) = a + limsup v"
proof -
  have "limsup u = a" using assms(1) using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "limsup (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast

  have "limsup (\<lambda>n. u n + v n) \<le> limsup u + limsup v"
    by (rule ereal_limsup_add_mono)
  then have up: "limsup (\<lambda>n. u n + v n) \<le> a + limsup v" using \<open>limsup u = a\<close> by simp

  have a: "limsup (\<lambda>n. (u n + v n) + (-u n)) \<le> limsup (\<lambda>n. u n + v n) + limsup (\<lambda>n. -u n)"
    by (rule ereal_limsup_add_mono)
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "limsup v = limsup (\<lambda>n. u n + v n + (-u n))" using Limsup_eq by force
  then have "limsup v \<le> limsup (\<lambda>n. u n + v n) -a" using a \<open>limsup (\<lambda>n. -u n) = -a\<close> by (simp add: minus_ereal_def)
  then have "limsup (\<lambda>n. u n + v n) \<ge> a + limsup v" using assms(2) by (metis add.commute ereal_le_minus)
  then show ?thesis using up by simp
qed

lemma ereal_limsup_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "limsup (\<lambda>n. u n * v n) = a * limsup v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "strict_mono r" "(v o r) \<longlonglongrightarrow> limsup v" using limsup_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * limsup v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * limsup v" unfolding w_def by presburger
  then have "limsup (w o r) = a * limsup v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "limsup w \<ge> a * limsup v" by (metis limsup_subseq_mono r(1))

  obtain s where s: "strict_mono s" "(w o s) \<longlonglongrightarrow> limsup w" using limsup_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (limsup w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (limsup w) / a" using Lim_transform_eventually by fastforce
  then have "limsup (v o s) = (limsup w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "limsup v \<ge> (limsup w) / a" by (metis limsup_subseq_mono s(1))
  then have "a * limsup v \<ge> limsup w" using assms(2) assms(3) by (simp add: ereal_divide_le_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_mult:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "a>0" "a \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n * v n) = a * liminf v"
proof -
  define w where "w = (\<lambda>n. u n * v n)"
  obtain r where r: "strict_mono r" "(v o r) \<longlonglongrightarrow> liminf v" using liminf_subseq_lim by auto
  have "(u o r) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ r by auto
  with tendsto_mult_ereal[OF this r(2)] have "(\<lambda>n. (u o r) n * (v o r) n) \<longlonglongrightarrow> a * liminf v" using assms(2) assms(3) by auto
  moreover have "\<And>n. (w o r) n = (u o r) n * (v o r) n" unfolding w_def by auto
  ultimately have "(w o r) \<longlonglongrightarrow> a * liminf v" unfolding w_def by presburger
  then have "liminf (w o r) = a * liminf v" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have I: "liminf w \<le> a * liminf v" by (metis liminf_subseq_mono r(1))

  obtain s where s: "strict_mono s" "(w o s) \<longlonglongrightarrow> liminf w" using liminf_subseq_lim by auto
  have *: "(u o s) \<longlonglongrightarrow> a" using assms(1) LIMSEQ_subseq_LIMSEQ s by auto
  have "eventually (\<lambda>n. (u o s) n > 0) sequentially" using assms(2) * order_tendsto_iff by blast
  moreover have "eventually (\<lambda>n. (u o s) n < \<infinity>) sequentially" using assms(3) * order_tendsto_iff by blast
  moreover have "(w o s) n / (u o s) n = (v o s) n" if "(u o s) n > 0" "(u o s) n < \<infinity>" for n
    unfolding w_def using that by (auto simp add: ereal_divide_eq)
  ultimately have "eventually (\<lambda>n. (w o s) n / (u o s) n = (v o s) n) sequentially" using eventually_elim2 by force
  moreover have "(\<lambda>n. (w o s) n / (u o s) n) \<longlonglongrightarrow> (liminf w) / a"
    apply (rule tendsto_divide_ereal[OF s(2) *]) using assms(2) assms(3) by auto
  ultimately have "(v o s) \<longlonglongrightarrow> (liminf w) / a" using Lim_transform_eventually by fastforce
  then have "liminf (v o s) = (liminf w) / a" by (simp add: tendsto_iff_Liminf_eq_Limsup)
  then have "liminf v \<le> (liminf w) / a" by (metis liminf_subseq_mono s(1))
  then have "a * liminf v \<le> liminf w" using assms(2) assms(3) by (simp add: ereal_le_divide_pos)
  then show ?thesis using I unfolding w_def by auto
qed

lemma ereal_liminf_lim_add:
  fixes u v::"nat \<Rightarrow> ereal"
  assumes "u \<longlonglongrightarrow> a" "abs(a) \<noteq> \<infinity>"
  shows "liminf (\<lambda>n. u n + v n) = a + liminf v"
proof -
  have "liminf u = a" using assms(1) tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have *: "abs(liminf u) \<noteq> \<infinity>" using assms(2) by auto
  have "(\<lambda>n. -u n) \<longlonglongrightarrow> -a" using assms(1) by auto
  then have "liminf (\<lambda>n. -u n) = -a" using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast
  then have **: "abs(liminf (\<lambda>n. -u n)) \<noteq> \<infinity>" using assms(2) by auto

  have "liminf (\<lambda>n. u n + v n) \<ge> liminf u + liminf v"
    apply (rule ereal_liminf_add_mono) using * by auto
  then have up: "liminf (\<lambda>n. u n + v n) \<ge> a + liminf v" using \<open>liminf u = a\<close> by simp

  have a: "liminf (\<lambda>n. (u n + v n) + (-u n)) \<ge> liminf (\<lambda>n. u n + v n) + liminf (\<lambda>n. -u n)"
    apply (rule ereal_liminf_add_mono) using ** by auto
  have "eventually (\<lambda>n. u n = ereal(real_of_ereal(u n))) sequentially" using assms
    real_lim_then_eventually_real by auto
  moreover have "\<And>x. x = ereal(real_of_ereal(x)) \<Longrightarrow> x + (-x) = 0"
    by (metis plus_ereal.simps(1) right_minus uminus_ereal.simps(1) zero_ereal_def)
  ultimately have "eventually (\<lambda>n. u n + (-u n) = 0) sequentially"
    by (metis (mono_tags, lifting) eventually_mono)
  moreover have "\<And>n. u n + (-u n) = 0 \<Longrightarrow> u n + v n + (-u n) = v n"
    by (metis add.commute add.left_commute add.left_neutral)
  ultimately have "eventually (\<lambda>n. u n + v n + (-u n) = v n) sequentially"
    using eventually_mono by force
  then have "liminf v = liminf (\<lambda>n. u n + v n + (-u n))" using Liminf_eq by force
  then have "liminf v \<ge> liminf (\<lambda>n. u n + v n) -a" using a \<open>liminf (\<lambda>n. -u n) = -a\<close> by (simp add: minus_ereal_def)
  then have "liminf (\<lambda>n. u n + v n) \<le> a + liminf v" using assms(2) by (metis add.commute ereal_minus_le)
  then show ?thesis using up by simp
qed

lemma ereal_liminf_limsup_add:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n + v n) \<le> liminf u + limsup v"
proof (cases)
  assume "limsup v = \<infinity> \<or> liminf u = \<infinity>"
  then show ?thesis by auto
next
  assume "\<not>(limsup v = \<infinity> \<or> liminf u = \<infinity>)"
  then have "limsup v < \<infinity>" "liminf u < \<infinity>" by auto

  define w where "w = (\<lambda>n. u n + v n)"
  obtain r where r: "strict_mono r" "(u o r) \<longlonglongrightarrow> liminf u" using liminf_subseq_lim by auto
  obtain s where s: "strict_mono s" "(w o r o s) \<longlonglongrightarrow> liminf (w o r)" using liminf_subseq_lim by auto
  obtain t where t: "strict_mono t" "(v o r o s o t) \<longlonglongrightarrow> limsup (v o r o s)" using limsup_subseq_lim by auto

  define a where "a = r o s o t"
  have "strict_mono a" using r s t by (simp add: a_def strict_mono_o)
  have l:"(u o a) \<longlonglongrightarrow> liminf u"
         "(w o a) \<longlonglongrightarrow> liminf (w o r)"
         "(v o a) \<longlonglongrightarrow> limsup (v o r o s)"
  apply (metis (no_types, lifting) r(2) s(1) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) s(2) t(1) LIMSEQ_subseq_LIMSEQ a_def comp_assoc)
  apply (metis (no_types, lifting) t(2) a_def comp_assoc)
  done

  have "liminf (w o r) \<ge> liminf w" by (simp add: liminf_subseq_mono r(1))
  have "limsup (v o r o s) \<le> limsup v" 
    by (simp add: comp_assoc limsup_subseq_mono r(1) s(1) strict_mono_o)
  then have b: "limsup (v o r o s) < \<infinity>" using \<open>limsup v < \<infinity>\<close> by auto

  have "(\<lambda>n. (u o a) n + (v o a) n) \<longlonglongrightarrow> liminf u + limsup (v o r o s)"
    apply (rule tendsto_add_ereal_general) using b \<open>liminf u < \<infinity>\<close> l(1) l(3) by force+
  moreover have "(\<lambda>n. (u o a) n + (v o a) n) = (w o a)" unfolding w_def by auto
  ultimately have "(w o a) \<longlonglongrightarrow> liminf u + limsup (v o r o s)" by simp
  then have "liminf (w o r) = liminf u + limsup (v o r o s)" using l(2) using LIMSEQ_unique by blast
  then have "liminf w \<le> liminf u + limsup v"
    using \<open>liminf (w o r) \<ge> liminf w\<close> \<open>limsup (v o r o s) \<le> limsup v\<close>
    by (metis add_mono_thms_linordered_semiring(2) le_less_trans not_less)
  then show ?thesis unfolding w_def by simp
qed

lemma ereal_liminf_limsup_minus:
  fixes u v::"nat \<Rightarrow> ereal"
  shows "liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding minus_ereal_def
  apply (subst add.commute)
  apply (rule order_trans[OF ereal_liminf_limsup_add])
  using ereal_Limsup_uminus[of sequentially "\<lambda>n. - v n"]
  apply (simp add: add.commute)
  done


lemma liminf_minus_ennreal:
  fixes u v::"nat \<Rightarrow> ennreal"
  shows "(\<And>n. v n \<le> u n) \<Longrightarrow> liminf (\<lambda>n. u n - v n) \<le> limsup u - limsup v"
  unfolding liminf_SUP_INF limsup_INF_SUP
  including ennreal.lifting
proof (transfer, clarsimp)
  fix v u :: "nat \<Rightarrow> ereal" assume *: "\<forall>x. 0 \<le> v x" "\<forall>x. 0 \<le> u x" "\<And>n. v n \<le> u n"
  moreover have "0 \<le> limsup u - limsup v"
    using * by (intro ereal_diff_positive Limsup_mono always_eventually) simp
  moreover have "0 \<le> Sup (u ` {x..})" for x
    using * by (intro SUP_upper2[of x]) auto
  moreover have "0 \<le> Sup (v ` {x..})" for x
    using * by (intro SUP_upper2[of x]) auto
  ultimately show "(SUP n. INF n\<in>{n..}. max 0 (u n - v n))
            \<le> max 0 ((INF x. max 0 (Sup (u ` {x..}))) - (INF x. max 0 (Sup (v ` {x..}))))"
    by (auto simp: * ereal_diff_positive max.absorb2 liminf_SUP_INF[symmetric] limsup_INF_SUP[symmetric] ereal_liminf_limsup_minus)
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

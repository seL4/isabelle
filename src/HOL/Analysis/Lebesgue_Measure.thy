(*  Title:      HOL/Analysis/Lebesgue_Measure.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Jeremy Avigad
    Author:     Luke Serafin
*)

section \<open>Lebesgue measure\<close>

theory Lebesgue_Measure
  imports Finite_Product_Measure Bochner_Integration Caratheodory
begin

subsection \<open>Every right continuous and nondecreasing function gives rise to a measure\<close>

definition interval_measure :: "(real \<Rightarrow> real) \<Rightarrow> real measure" where
  "interval_measure F = extend_measure UNIV {(a, b). a \<le> b} (\<lambda>(a, b). {a <.. b}) (\<lambda>(a, b). ennreal (F b - F a))"

lemma emeasure_interval_measure_Ioc:
  assumes "a \<le> b"
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes right_cont_F : "\<And>a. continuous (at_right a) F"
  shows "emeasure (interval_measure F) {a <.. b} = F b - F a"
proof (rule extend_measure_caratheodory_pair[OF interval_measure_def \<open>a \<le> b\<close>])
  show "semiring_of_sets UNIV {{a<..b} |a b :: real. a \<le> b}"
  proof (unfold_locales, safe)
    fix a b c d :: real assume *: "a \<le> b" "c \<le> d"
    then show "\<exists>C\<subseteq>{{a<..b} |a b. a \<le> b}. finite C \<and> disjoint C \<and> {a<..b} - {c<..d} = \<Union>C"
    proof cases
      let ?C = "{{a<..b}}"
      assume "b < c \<or> d \<le> a \<or> d \<le> c"
      with * have "?C \<subseteq> {{a<..b} |a b. a \<le> b} \<and> finite ?C \<and> disjoint ?C \<and> {a<..b} - {c<..d} = \<Union>?C"
        by (auto simp add: disjoint_def)
      thus ?thesis ..
    next
      let ?C = "{{a<..c}, {d<..b}}"
      assume "\<not> (b < c \<or> d \<le> a \<or> d \<le> c)"
      with * have "?C \<subseteq> {{a<..b} |a b. a \<le> b} \<and> finite ?C \<and> disjoint ?C \<and> {a<..b} - {c<..d} = \<Union>?C"
        by (auto simp add: disjoint_def Ioc_inj) (metis linear)+
      thus ?thesis ..
    qed
  qed (auto simp: Ioc_inj, metis linear)
next
  fix l r :: "nat \<Rightarrow> real" and a b :: real
  assume l_r[simp]: "\<And>n. l n \<le> r n" and "a \<le> b" and disj: "disjoint_family (\<lambda>n. {l n<..r n})"
  assume lr_eq_ab: "(\<Union>i. {l i<..r i}) = {a<..b}"

  have [intro, simp]: "\<And>a b. a \<le> b \<Longrightarrow> F a \<le> F b"
    by (auto intro!: l_r mono_F)

  { fix S :: "nat set" assume "finite S"
    moreover note \<open>a \<le> b\<close>
    moreover have "\<And>i. i \<in> S \<Longrightarrow> {l i <.. r i} \<subseteq> {a <.. b}"
      unfolding lr_eq_ab[symmetric] by auto
    ultimately have "(\<Sum>i\<in>S. F (r i) - F (l i)) \<le> F b - F a"
    proof (induction S arbitrary: a rule: finite_psubset_induct)
      case (psubset S)
      show ?case
      proof cases
        assume "\<exists>i\<in>S. l i < r i"
        with \<open>finite S\<close> have "Min (l ` {i\<in>S. l i < r i}) \<in> l ` {i\<in>S. l i < r i}"
          by (intro Min_in) auto
        then obtain m where m: "m \<in> S" "l m < r m" "l m = Min (l ` {i\<in>S. l i < r i})"
          by fastforce

        have "(\<Sum>i\<in>S. F (r i) - F (l i)) = (F (r m) - F (l m)) + (\<Sum>i\<in>S - {m}. F (r i) - F (l i))"
          using m psubset by (intro setsum.remove) auto
        also have "(\<Sum>i\<in>S - {m}. F (r i) - F (l i)) \<le> F b - F (r m)"
        proof (intro psubset.IH)
          show "S - {m} \<subset> S"
            using \<open>m\<in>S\<close> by auto
          show "r m \<le> b"
            using psubset.prems(2)[OF \<open>m\<in>S\<close>] \<open>l m < r m\<close> by auto
        next
          fix i assume "i \<in> S - {m}"
          then have i: "i \<in> S" "i \<noteq> m" by auto
          { assume i': "l i < r i" "l i < r m"
            with \<open>finite S\<close> i m have "l m \<le> l i"
              by auto
            with i' have "{l i <.. r i} \<inter> {l m <.. r m} \<noteq> {}"
              by auto
            then have False
              using disjoint_family_onD[OF disj, of i m] i by auto }
          then have "l i \<noteq> r i \<Longrightarrow> r m \<le> l i"
            unfolding not_less[symmetric] using l_r[of i] by auto
          then show "{l i <.. r i} \<subseteq> {r m <.. b}"
            using psubset.prems(2)[OF \<open>i\<in>S\<close>] by auto
        qed
        also have "F (r m) - F (l m) \<le> F (r m) - F a"
          using psubset.prems(2)[OF \<open>m \<in> S\<close>] \<open>l m < r m\<close>
          by (auto simp add: Ioc_subset_iff intro!: mono_F)
        finally show ?case
          by (auto intro: add_mono)
      qed (auto simp add: \<open>a \<le> b\<close> less_le)
    qed }
  note claim1 = this

  (* second key induction: a lower bound on the measures of any finite collection of Ai's
     that cover an interval {u..v} *)

  { fix S u v and l r :: "nat \<Rightarrow> real"
    assume "finite S" "\<And>i. i\<in>S \<Longrightarrow> l i < r i" "{u..v} \<subseteq> (\<Union>i\<in>S. {l i<..< r i})"
    then have "F v - F u \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
    proof (induction arbitrary: v u rule: finite_psubset_induct)
      case (psubset S)
      show ?case
      proof cases
        assume "S = {}" then show ?case
          using psubset by (simp add: mono_F)
      next
        assume "S \<noteq> {}"
        then obtain j where "j \<in> S"
          by auto

        let ?R = "r j < u \<or> l j > v \<or> (\<exists>i\<in>S-{j}. l i \<le> l j \<and> r j \<le> r i)"
        show ?case
        proof cases
          assume "?R"
          with \<open>j \<in> S\<close> psubset.prems have "{u..v} \<subseteq> (\<Union>i\<in>S-{j}. {l i<..< r i})"
            apply (auto simp: subset_eq Ball_def)
            apply (metis Diff_iff less_le_trans leD linear singletonD)
            apply (metis Diff_iff less_le_trans leD linear singletonD)
            apply (metis order_trans less_le_not_le linear)
            done
          with \<open>j \<in> S\<close> have "F v - F u \<le> (\<Sum>i\<in>S - {j}. F (r i) - F (l i))"
            by (intro psubset) auto
          also have "\<dots> \<le> (\<Sum>i\<in>S. F (r i) - F (l i))"
            using psubset.prems
            by (intro setsum_mono2 psubset) (auto intro: less_imp_le)
          finally show ?thesis .
        next
          assume "\<not> ?R"
          then have j: "u \<le> r j" "l j \<le> v" "\<And>i. i \<in> S - {j} \<Longrightarrow> r i < r j \<or> l i > l j"
            by (auto simp: not_less)
          let ?S1 = "{i \<in> S. l i < l j}"
          let ?S2 = "{i \<in> S. r i > r j}"

          have "(\<Sum>i\<in>S. F (r i) - F (l i)) \<ge> (\<Sum>i\<in>?S1 \<union> ?S2 \<union> {j}. F (r i) - F (l i))"
            using \<open>j \<in> S\<close> \<open>finite S\<close> psubset.prems j
            by (intro setsum_mono2) (auto intro: less_imp_le)
          also have "(\<Sum>i\<in>?S1 \<union> ?S2 \<union> {j}. F (r i) - F (l i)) =
            (\<Sum>i\<in>?S1. F (r i) - F (l i)) + (\<Sum>i\<in>?S2 . F (r i) - F (l i)) + (F (r j) - F (l j))"
            using psubset(1) psubset.prems(1) j
            apply (subst setsum.union_disjoint)
            apply simp_all
            apply (subst setsum.union_disjoint)
            apply auto
            apply (metis less_le_not_le)
            done
          also (xtrans) have "(\<Sum>i\<in>?S1. F (r i) - F (l i)) \<ge> F (l j) - F u"
            using \<open>j \<in> S\<close> \<open>finite S\<close> psubset.prems j
            apply (intro psubset.IH psubset)
            apply (auto simp: subset_eq Ball_def)
            apply (metis less_le_trans not_le)
            done
          also (xtrans) have "(\<Sum>i\<in>?S2. F (r i) - F (l i)) \<ge> F v - F (r j)"
            using \<open>j \<in> S\<close> \<open>finite S\<close> psubset.prems j
            apply (intro psubset.IH psubset)
            apply (auto simp: subset_eq Ball_def)
            apply (metis le_less_trans not_le)
            done
          finally (xtrans) show ?case
            by (auto simp: add_mono)
        qed
      qed
    qed }
  note claim2 = this

  (* now prove the inequality going the other way *)
  have "ennreal (F b - F a) \<le> (\<Sum>i. ennreal (F (r i) - F (l i)))"
  proof (rule ennreal_le_epsilon)
    fix epsilon :: real assume egt0: "epsilon > 0"
    have "\<forall>i. \<exists>d>0. F (r i + d) < F (r i) + epsilon / 2^(i+2)"
    proof
      fix i
      note right_cont_F [of "r i"]
      thus "\<exists>d>0. F (r i + d) < F (r i) + epsilon / 2^(i+2)"
        apply -
        apply (subst (asm) continuous_at_right_real_increasing)
        apply (rule mono_F, assumption)
        apply (drule_tac x = "epsilon / 2 ^ (i + 2)" in spec)
        apply (erule impE)
        using egt0 by (auto simp add: field_simps)
    qed
    then obtain delta where
        deltai_gt0: "\<And>i. delta i > 0" and
        deltai_prop: "\<And>i. F (r i + delta i) < F (r i) + epsilon / 2^(i+2)"
      by metis
    have "\<exists>a' > a. F a' - F a < epsilon / 2"
      apply (insert right_cont_F [of a])
      apply (subst (asm) continuous_at_right_real_increasing)
      using mono_F apply force
      apply (drule_tac x = "epsilon / 2" in spec)
      using egt0 unfolding mult.commute [of 2] by force
    then obtain a' where a'lea [arith]: "a' > a" and
      a_prop: "F a' - F a < epsilon / 2"
      by auto
    define S' where "S' = {i. l i < r i}"
    obtain S :: "nat set" where
      "S \<subseteq> S'" and finS: "finite S" and
      Sprop: "{a'..b} \<subseteq> (\<Union>i \<in> S. {l i<..<r i + delta i})"
    proof (rule compactE_image)
      show "compact {a'..b}"
        by (rule compact_Icc)
      show "\<forall>i \<in> S'. open ({l i<..<r i + delta i})" by auto
      have "{a'..b} \<subseteq> {a <.. b}"
        by auto
      also have "{a <.. b} = (\<Union>i\<in>S'. {l i<..r i})"
        unfolding lr_eq_ab[symmetric] by (fastforce simp add: S'_def intro: less_le_trans)
      also have "\<dots> \<subseteq> (\<Union>i \<in> S'. {l i<..<r i + delta i})"
        apply (intro UN_mono)
        apply (auto simp: S'_def)
        apply (cut_tac i=i in deltai_gt0)
        apply simp
        done
      finally show "{a'..b} \<subseteq> (\<Union>i \<in> S'. {l i<..<r i + delta i})" .
    qed
    with S'_def have Sprop2: "\<And>i. i \<in> S \<Longrightarrow> l i < r i" by auto
    from finS have "\<exists>n. \<forall>i \<in> S. i \<le> n"
      by (subst finite_nat_set_iff_bounded_le [symmetric])
    then obtain n where Sbound [rule_format]: "\<forall>i \<in> S. i \<le> n" ..
    have "F b - F a' \<le> (\<Sum>i\<in>S. F (r i + delta i) - F (l i))"
      apply (rule claim2 [rule_format])
      using finS Sprop apply auto
      apply (frule Sprop2)
      apply (subgoal_tac "delta i > 0")
      apply arith
      by (rule deltai_gt0)
    also have "... \<le> (\<Sum>i \<in> S. F(r i) - F(l i) + epsilon / 2^(i+2))"
      apply (rule setsum_mono)
      apply simp
      apply (rule order_trans)
      apply (rule less_imp_le)
      apply (rule deltai_prop)
      by auto
    also have "... = (\<Sum>i \<in> S. F(r i) - F(l i)) +
        (epsilon / 4) * (\<Sum>i \<in> S. (1 / 2)^i)" (is "_ = ?t + _")
      by (subst setsum.distrib) (simp add: field_simps setsum_right_distrib)
    also have "... \<le> ?t + (epsilon / 4) * (\<Sum> i < Suc n. (1 / 2)^i)"
      apply (rule add_left_mono)
      apply (rule mult_left_mono)
      apply (rule setsum_mono2)
      using egt0 apply auto
      by (frule Sbound, auto)
    also have "... \<le> ?t + (epsilon / 2)"
      apply (rule add_left_mono)
      apply (subst geometric_sum)
      apply auto
      apply (rule mult_left_mono)
      using egt0 apply auto
      done
    finally have aux2: "F b - F a' \<le> (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon / 2"
      by simp

    have "F b - F a = (F b - F a') + (F a' - F a)"
      by auto
    also have "... \<le> (F b - F a') + epsilon / 2"
      using a_prop by (intro add_left_mono) simp
    also have "... \<le> (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon / 2 + epsilon / 2"
      apply (intro add_right_mono)
      apply (rule aux2)
      done
    also have "... = (\<Sum>i\<in>S. F (r i) - F (l i)) + epsilon"
      by auto
    also have "... \<le> (\<Sum>i\<le>n. F (r i) - F (l i)) + epsilon"
      using finS Sbound Sprop by (auto intro!: add_right_mono setsum_mono3)
    finally have "ennreal (F b - F a) \<le> (\<Sum>i\<le>n. ennreal (F (r i) - F (l i))) + epsilon"
      using egt0 by (simp add: ennreal_plus[symmetric] setsum_nonneg del: ennreal_plus)
    then show "ennreal (F b - F a) \<le> (\<Sum>i. ennreal (F (r i) - F (l i))) + (epsilon :: real)"
      by (rule order_trans) (auto intro!: add_mono setsum_le_suminf simp del: setsum_ennreal)
  qed
  moreover have "(\<Sum>i. ennreal (F (r i) - F (l i))) \<le> ennreal (F b - F a)"
    using \<open>a \<le> b\<close> by (auto intro!: suminf_le_const ennreal_le_iff[THEN iffD2] claim1)
  ultimately show "(\<Sum>n. ennreal (F (r n) - F (l n))) = ennreal (F b - F a)"
    by (rule antisym[rotated])
qed (auto simp: Ioc_inj mono_F)

lemma measure_interval_measure_Ioc:
  assumes "a \<le> b"
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes right_cont_F : "\<And>a. continuous (at_right a) F"
  shows "measure (interval_measure F) {a <.. b} = F b - F a"
  unfolding measure_def
  apply (subst emeasure_interval_measure_Ioc)
  apply fact+
  apply (simp add: assms)
  done

lemma emeasure_interval_measure_Ioc_eq:
  "(\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y) \<Longrightarrow> (\<And>a. continuous (at_right a) F) \<Longrightarrow>
    emeasure (interval_measure F) {a <.. b} = (if a \<le> b then F b - F a else 0)"
  using emeasure_interval_measure_Ioc[of a b F] by auto

lemma sets_interval_measure [simp, measurable_cong]: "sets (interval_measure F) = sets borel"
  apply (simp add: sets_extend_measure interval_measure_def borel_sigma_sets_Ioc)
  apply (rule sigma_sets_eqI)
  apply auto
  apply (case_tac "a \<le> ba")
  apply (auto intro: sigma_sets.Empty)
  done

lemma space_interval_measure [simp]: "space (interval_measure F) = UNIV"
  by (simp add: interval_measure_def space_extend_measure)

lemma emeasure_interval_measure_Icc:
  assumes "a \<le> b"
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes cont_F : "continuous_on UNIV F"
  shows "emeasure (interval_measure F) {a .. b} = F b - F a"
proof (rule tendsto_unique)
  { fix a b :: real assume "a \<le> b" then have "emeasure (interval_measure F) {a <.. b} = F b - F a"
      using cont_F
      by (subst emeasure_interval_measure_Ioc)
         (auto intro: mono_F continuous_within_subset simp: continuous_on_eq_continuous_within) }
  note * = this

  let ?F = "interval_measure F"
  show "((\<lambda>a. F b - F a) \<longlongrightarrow> emeasure ?F {a..b}) (at_left a)"
  proof (rule tendsto_at_left_sequentially)
    show "a - 1 < a" by simp
    fix X assume "\<And>n. X n < a" "incseq X" "X \<longlonglongrightarrow> a"
    with \<open>a \<le> b\<close> have "(\<lambda>n. emeasure ?F {X n<..b}) \<longlonglongrightarrow> emeasure ?F (\<Inter>n. {X n <..b})"
      apply (intro Lim_emeasure_decseq)
      apply (auto simp: decseq_def incseq_def emeasure_interval_measure_Ioc *)
      apply force
      apply (subst (asm ) *)
      apply (auto intro: less_le_trans less_imp_le)
      done
    also have "(\<Inter>n. {X n <..b}) = {a..b}"
      using \<open>\<And>n. X n < a\<close>
      apply auto
      apply (rule LIMSEQ_le_const2[OF \<open>X \<longlonglongrightarrow> a\<close>])
      apply (auto intro: less_imp_le)
      apply (auto intro: less_le_trans)
      done
    also have "(\<lambda>n. emeasure ?F {X n<..b}) = (\<lambda>n. F b - F (X n))"
      using \<open>\<And>n. X n < a\<close> \<open>a \<le> b\<close> by (subst *) (auto intro: less_imp_le less_le_trans)
    finally show "(\<lambda>n. F b - F (X n)) \<longlonglongrightarrow> emeasure ?F {a..b}" .
  qed
  show "((\<lambda>a. ennreal (F b - F a)) \<longlongrightarrow> F b - F a) (at_left a)"
    by (rule continuous_on_tendsto_compose[where g="\<lambda>x. x" and s=UNIV])
       (auto simp: continuous_on_ennreal continuous_on_diff cont_F continuous_on_const)
qed (rule trivial_limit_at_left_real)

lemma sigma_finite_interval_measure:
  assumes mono_F: "\<And>x y. x \<le> y \<Longrightarrow> F x \<le> F y"
  assumes right_cont_F : "\<And>a. continuous (at_right a) F"
  shows "sigma_finite_measure (interval_measure F)"
  apply unfold_locales
  apply (intro exI[of _ "(\<lambda>(a, b). {a <.. b}) ` (\<rat> \<times> \<rat>)"])
  apply (auto intro!: Rats_no_top_le Rats_no_bot_less countable_rat simp: emeasure_interval_measure_Ioc_eq[OF assms])
  done

subsection \<open>Lebesgue-Borel measure\<close>

definition lborel :: "('a :: euclidean_space) measure" where
  "lborel = distr (\<Pi>\<^sub>M b\<in>Basis. interval_measure (\<lambda>x. x)) borel (\<lambda>f. \<Sum>b\<in>Basis. f b *\<^sub>R b)"

lemma
  shows sets_lborel[simp, measurable_cong]: "sets lborel = sets borel"
    and space_lborel[simp]: "space lborel = space borel"
    and measurable_lborel1[simp]: "measurable M lborel = measurable M borel"
    and measurable_lborel2[simp]: "measurable lborel M = measurable borel M"
  by (simp_all add: lborel_def)

context
begin

interpretation sigma_finite_measure "interval_measure (\<lambda>x. x)"
  by (rule sigma_finite_interval_measure) auto
interpretation finite_product_sigma_finite "\<lambda>_. interval_measure (\<lambda>x. x)" Basis
  proof qed simp

lemma lborel_eq_real: "lborel = interval_measure (\<lambda>x. x)"
  unfolding lborel_def Basis_real_def
  using distr_id[of "interval_measure (\<lambda>x. x)"]
  by (subst distr_component[symmetric])
     (simp_all add: distr_distr comp_def del: distr_id cong: distr_cong)

lemma lborel_eq: "lborel = distr (\<Pi>\<^sub>M b\<in>Basis. lborel) borel (\<lambda>f. \<Sum>b\<in>Basis. f b *\<^sub>R b)"
  by (subst lborel_def) (simp add: lborel_eq_real)

lemma nn_integral_lborel_setprod:
  assumes [measurable]: "\<And>b. b \<in> Basis \<Longrightarrow> f b \<in> borel_measurable borel"
  assumes nn[simp]: "\<And>b x. b \<in> Basis \<Longrightarrow> 0 \<le> f b x"
  shows "(\<integral>\<^sup>+x. (\<Prod>b\<in>Basis. f b (x \<bullet> b)) \<partial>lborel) = (\<Prod>b\<in>Basis. (\<integral>\<^sup>+x. f b x \<partial>lborel))"
  by (simp add: lborel_def nn_integral_distr product_nn_integral_setprod
                product_nn_integral_singleton)

lemma emeasure_lborel_Icc[simp]:
  fixes l u :: real
  assumes [simp]: "l \<le> u"
  shows "emeasure lborel {l .. u} = u - l"
proof -
  have "((\<lambda>f. f 1) -` {l..u} \<inter> space (Pi\<^sub>M {1} (\<lambda>b. interval_measure (\<lambda>x. x)))) = {1::real} \<rightarrow>\<^sub>E {l..u}"
    by (auto simp: space_PiM)
  then show ?thesis
    by (simp add: lborel_def emeasure_distr emeasure_PiM emeasure_interval_measure_Icc continuous_on_id)
qed

lemma emeasure_lborel_Icc_eq: "emeasure lborel {l .. u} = ennreal (if l \<le> u then u - l else 0)"
  by simp

lemma emeasure_lborel_cbox[simp]:
  assumes [simp]: "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  shows "emeasure lborel (cbox l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
proof -
  have "(\<lambda>x. \<Prod>b\<in>Basis. indicator {l\<bullet>b .. u\<bullet>b} (x \<bullet> b) :: ennreal) = indicator (cbox l u)"
    by (auto simp: fun_eq_iff cbox_def split: split_indicator)
  then have "emeasure lborel (cbox l u) = (\<integral>\<^sup>+x. (\<Prod>b\<in>Basis. indicator {l\<bullet>b .. u\<bullet>b} (x \<bullet> b)) \<partial>lborel)"
    by simp
  also have "\<dots> = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    by (subst nn_integral_lborel_setprod) (simp_all add: setprod_ennreal inner_diff_left)
  finally show ?thesis .
qed

lemma AE_lborel_singleton: "AE x in lborel::'a::euclidean_space measure. x \<noteq> c"
  using SOME_Basis AE_discrete_difference [of "{c}" lborel] emeasure_lborel_cbox [of c c]
  by (auto simp add: cbox_sing setprod_constant power_0_left)

lemma emeasure_lborel_Ioo[simp]:
  assumes [simp]: "l \<le> u"
  shows "emeasure lborel {l <..< u} = ennreal (u - l)"
proof -
  have "emeasure lborel {l <..< u} = emeasure lborel {l .. u}"
    using AE_lborel_singleton[of u] AE_lborel_singleton[of l] by (intro emeasure_eq_AE) auto
  then show ?thesis
    by simp
qed

lemma emeasure_lborel_Ioc[simp]:
  assumes [simp]: "l \<le> u"
  shows "emeasure lborel {l <.. u} = ennreal (u - l)"
proof -
  have "emeasure lborel {l <.. u} = emeasure lborel {l .. u}"
    using AE_lborel_singleton[of u] AE_lborel_singleton[of l] by (intro emeasure_eq_AE) auto
  then show ?thesis
    by simp
qed

lemma emeasure_lborel_Ico[simp]:
  assumes [simp]: "l \<le> u"
  shows "emeasure lborel {l ..< u} = ennreal (u - l)"
proof -
  have "emeasure lborel {l ..< u} = emeasure lborel {l .. u}"
    using AE_lborel_singleton[of u] AE_lborel_singleton[of l] by (intro emeasure_eq_AE) auto
  then show ?thesis
    by simp
qed

lemma emeasure_lborel_box[simp]:
  assumes [simp]: "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  shows "emeasure lborel (box l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
proof -
  have "(\<lambda>x. \<Prod>b\<in>Basis. indicator {l\<bullet>b <..< u\<bullet>b} (x \<bullet> b) :: ennreal) = indicator (box l u)"
    by (auto simp: fun_eq_iff box_def split: split_indicator)
  then have "emeasure lborel (box l u) = (\<integral>\<^sup>+x. (\<Prod>b\<in>Basis. indicator {l\<bullet>b <..< u\<bullet>b} (x \<bullet> b)) \<partial>lborel)"
    by simp
  also have "\<dots> = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    by (subst nn_integral_lborel_setprod) (simp_all add: setprod_ennreal inner_diff_left)
  finally show ?thesis .
qed

lemma emeasure_lborel_cbox_eq:
  "emeasure lborel (cbox l u) = (if \<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b then \<Prod>b\<in>Basis. (u - l) \<bullet> b else 0)"
  using box_eq_empty(2)[THEN iffD2, of u l] by (auto simp: not_le)

lemma emeasure_lborel_box_eq:
  "emeasure lborel (box l u) = (if \<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b then \<Prod>b\<in>Basis. (u - l) \<bullet> b else 0)"
  using box_eq_empty(1)[THEN iffD2, of u l] by (auto simp: not_le dest!: less_imp_le) force

lemma emeasure_lborel_singleton[simp]: "emeasure lborel {x} = 0"
  using emeasure_lborel_cbox[of x x] nonempty_Basis
  by (auto simp del: emeasure_lborel_cbox nonempty_Basis simp add: cbox_sing setprod_constant)

lemma
  fixes l u :: real
  assumes [simp]: "l \<le> u"
  shows measure_lborel_Icc[simp]: "measure lborel {l .. u} = u - l"
    and measure_lborel_Ico[simp]: "measure lborel {l ..< u} = u - l"
    and measure_lborel_Ioc[simp]: "measure lborel {l <.. u} = u - l"
    and measure_lborel_Ioo[simp]: "measure lborel {l <..< u} = u - l"
  by (simp_all add: measure_def)

lemma
  assumes [simp]: "\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  shows measure_lborel_box[simp]: "measure lborel (box l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
    and measure_lborel_cbox[simp]: "measure lborel (cbox l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  by (simp_all add: measure_def inner_diff_left setprod_nonneg)

lemma measure_lborel_cbox_eq:
  "measure lborel (cbox l u) = (if \<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b then \<Prod>b\<in>Basis. (u - l) \<bullet> b else 0)"
  using box_eq_empty(2)[THEN iffD2, of u l] by (auto simp: not_le)

lemma measure_lborel_box_eq:
  "measure lborel (box l u) = (if \<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b then \<Prod>b\<in>Basis. (u - l) \<bullet> b else 0)"
  using box_eq_empty(1)[THEN iffD2, of u l] by (auto simp: not_le dest!: less_imp_le) force

lemma measure_lborel_singleton[simp]: "measure lborel {x} = 0"
  by (simp add: measure_def)

lemma sigma_finite_lborel: "sigma_finite_measure lborel"
proof
  show "\<exists>A::'a set set. countable A \<and> A \<subseteq> sets lborel \<and> \<Union>A = space lborel \<and> (\<forall>a\<in>A. emeasure lborel a \<noteq> \<infinity>)"
    by (intro exI[of _ "range (\<lambda>n::nat. box (- real n *\<^sub>R One) (real n *\<^sub>R One))"])
       (auto simp: emeasure_lborel_cbox_eq UN_box_eq_UNIV)
qed

end

lemma emeasure_lborel_UNIV: "emeasure lborel (UNIV::'a::euclidean_space set) = \<infinity>"
proof -
  { fix n::nat
    let ?Ba = "Basis :: 'a set"
    have "real n \<le> (2::real) ^ card ?Ba * real n"
      by (simp add: mult_le_cancel_right1)
    also
    have "... \<le> (2::real) ^ card ?Ba * real (Suc n) ^ card ?Ba"
      apply (rule mult_left_mono)
      apply (metis DIM_positive One_nat_def less_eq_Suc_le less_imp_le of_nat_le_iff of_nat_power self_le_power zero_less_Suc)
      apply (simp add: DIM_positive)
      done
    finally have "real n \<le> (2::real) ^ card ?Ba * real (Suc n) ^ card ?Ba" .
  } note [intro!] = this
  show ?thesis
    unfolding UN_box_eq_UNIV[symmetric]
    apply (subst SUP_emeasure_incseq[symmetric])
    apply (auto simp: incseq_def subset_box inner_add_left setprod_constant
      simp del: Sup_eq_top_iff SUP_eq_top_iff
      intro!: ennreal_SUP_eq_top)
    done
qed

lemma emeasure_lborel_countable:
  fixes A :: "'a::euclidean_space set"
  assumes "countable A"
  shows "emeasure lborel A = 0"
proof -
  have "A \<subseteq> (\<Union>i. {from_nat_into A i})" using from_nat_into_surj assms by force
  then have "emeasure lborel A \<le> emeasure lborel (\<Union>i. {from_nat_into A i})"
    by (intro emeasure_mono) auto
  also have "emeasure lborel (\<Union>i. {from_nat_into A i}) = 0"
    by (rule emeasure_UN_eq_0) auto
  finally show ?thesis
    by (auto simp add: )
qed

lemma countable_imp_null_set_lborel: "countable A \<Longrightarrow> A \<in> null_sets lborel"
  by (simp add: null_sets_def emeasure_lborel_countable sets.countable)

lemma finite_imp_null_set_lborel: "finite A \<Longrightarrow> A \<in> null_sets lborel"
  by (intro countable_imp_null_set_lborel countable_finite)

lemma lborel_neq_count_space[simp]: "lborel \<noteq> count_space (A::('a::ordered_euclidean_space) set)"
proof
  assume asm: "lborel = count_space A"
  have "space lborel = UNIV" by simp
  hence [simp]: "A = UNIV" by (subst (asm) asm) (simp only: space_count_space)
  have "emeasure lborel {undefined::'a} = 1"
      by (subst asm, subst emeasure_count_space_finite) auto
  moreover have "emeasure lborel {undefined} \<noteq> 1" by simp
  ultimately show False by contradiction
qed

subsection \<open>Affine transformation on the Lebesgue-Borel\<close>

lemma lborel_eqI:
  fixes M :: "'a::euclidean_space measure"
  assumes emeasure_eq: "\<And>l u. (\<And>b. b \<in> Basis \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b) \<Longrightarrow> emeasure M (box l u) = (\<Prod>b\<in>Basis. (u - l) \<bullet> b)"
  assumes sets_eq: "sets M = sets borel"
  shows "lborel = M"
proof (rule measure_eqI_generator_eq)
  let ?E = "range (\<lambda>(a, b). box a b::'a set)"
  show "Int_stable ?E"
    by (auto simp: Int_stable_def box_Int_box)

  show "?E \<subseteq> Pow UNIV" "sets lborel = sigma_sets UNIV ?E" "sets M = sigma_sets UNIV ?E"
    by (simp_all add: borel_eq_box sets_eq)

  let ?A = "\<lambda>n::nat. box (- (real n *\<^sub>R One)) (real n *\<^sub>R One) :: 'a set"
  show "range ?A \<subseteq> ?E" "(\<Union>i. ?A i) = UNIV"
    unfolding UN_box_eq_UNIV by auto

  { fix i show "emeasure lborel (?A i) \<noteq> \<infinity>" by auto }
  { fix X assume "X \<in> ?E" then show "emeasure lborel X = emeasure M X"
      apply (auto simp: emeasure_eq emeasure_lborel_box_eq)
      apply (subst box_eq_empty(1)[THEN iffD2])
      apply (auto intro: less_imp_le simp: not_le)
      done }
qed

lemma lborel_affine_euclidean:
  fixes c :: "'a::euclidean_space \<Rightarrow> real" and t
  defines "T x \<equiv> t + (\<Sum>j\<in>Basis. (c j * (x \<bullet> j)) *\<^sub>R j)"
  assumes c: "\<And>j. j \<in> Basis \<Longrightarrow> c j \<noteq> 0"
  shows "lborel = density (distr lborel borel T) (\<lambda>_. (\<Prod>j\<in>Basis. \<bar>c j\<bar>))" (is "_ = ?D")
proof (rule lborel_eqI)
  let ?B = "Basis :: 'a set"
  fix l u assume le: "\<And>b. b \<in> ?B \<Longrightarrow> l \<bullet> b \<le> u \<bullet> b"
  have [measurable]: "T \<in> borel \<rightarrow>\<^sub>M borel"
    by (simp add: T_def[abs_def])
  have eq: "T -` box l u = box
    (\<Sum>j\<in>Basis. (((if 0 < c j then l - t else u - t) \<bullet> j) / c j) *\<^sub>R j)
    (\<Sum>j\<in>Basis. (((if 0 < c j then u - t else l - t) \<bullet> j) / c j) *\<^sub>R j)"
    using c by (auto simp: box_def T_def field_simps inner_simps divide_less_eq)
  with le c show "emeasure ?D (box l u) = (\<Prod>b\<in>?B. (u - l) \<bullet> b)"
    by (auto simp: emeasure_density emeasure_distr nn_integral_multc emeasure_lborel_box_eq inner_simps
                   field_simps divide_simps ennreal_mult'[symmetric] setprod_nonneg setprod.distrib[symmetric]
             intro!: setprod.cong)
qed simp

lemma lborel_affine:
  fixes t :: "'a::euclidean_space"
  shows "c \<noteq> 0 \<Longrightarrow> lborel = density (distr lborel borel (\<lambda>x. t + c *\<^sub>R x)) (\<lambda>_. \<bar>c\<bar>^DIM('a))"
  using lborel_affine_euclidean[where c="\<lambda>_::'a. c" and t=t]
  unfolding scaleR_scaleR[symmetric] scaleR_setsum_right[symmetric] euclidean_representation setprod_constant by simp

lemma lborel_real_affine:
  "c \<noteq> 0 \<Longrightarrow> lborel = density (distr lborel borel (\<lambda>x. t + c * x)) (\<lambda>_. ennreal (abs c))"
  using lborel_affine[of c t] by simp

lemma AE_borel_affine:
  fixes P :: "real \<Rightarrow> bool"
  shows "c \<noteq> 0 \<Longrightarrow> Measurable.pred borel P \<Longrightarrow> AE x in lborel. P x \<Longrightarrow> AE x in lborel. P (t + c * x)"
  by (subst lborel_real_affine[where t="- t / c" and c="1 / c"])
     (simp_all add: AE_density AE_distr_iff field_simps)

lemma nn_integral_real_affine:
  fixes c :: real assumes [measurable]: "f \<in> borel_measurable borel" and c: "c \<noteq> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>lborel) = \<bar>c\<bar> * (\<integral>\<^sup>+x. f (t + c * x) \<partial>lborel)"
  by (subst lborel_real_affine[OF c, of t])
     (simp add: nn_integral_density nn_integral_distr nn_integral_cmult)

lemma lborel_integrable_real_affine:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "integrable lborel f"
  shows "c \<noteq> 0 \<Longrightarrow> integrable lborel (\<lambda>x. f (t + c * x))"
  using f f[THEN borel_measurable_integrable] unfolding integrable_iff_bounded
  by (subst (asm) nn_integral_real_affine[where c=c and t=t]) (auto simp: ennreal_mult_less_top)

lemma lborel_integrable_real_affine_iff:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "c \<noteq> 0 \<Longrightarrow> integrable lborel (\<lambda>x. f (t + c * x)) \<longleftrightarrow> integrable lborel f"
  using
    lborel_integrable_real_affine[of f c t]
    lborel_integrable_real_affine[of "\<lambda>x. f (t + c * x)" "1/c" "-t/c"]
  by (auto simp add: field_simps)

lemma lborel_integral_real_affine:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}" and c :: real
  assumes c: "c \<noteq> 0" shows "(\<integral>x. f x \<partial> lborel) = \<bar>c\<bar> *\<^sub>R (\<integral>x. f (t + c * x) \<partial>lborel)"
proof cases
  assume f[measurable]: "integrable lborel f" then show ?thesis
    using c f f[THEN borel_measurable_integrable] f[THEN lborel_integrable_real_affine, of c t]
    by (subst lborel_real_affine[OF c, of t])
       (simp add: integral_density integral_distr)
next
  assume "\<not> integrable lborel f" with c show ?thesis
    by (simp add: lborel_integrable_real_affine_iff not_integrable_integral_eq)
qed

lemma divideR_right:
  fixes x y :: "'a::real_normed_vector"
  shows "r \<noteq> 0 \<Longrightarrow> y = x /\<^sub>R r \<longleftrightarrow> r *\<^sub>R y = x"
  using scaleR_cancel_left[of r y "x /\<^sub>R r"] by simp

lemma lborel_has_bochner_integral_real_affine_iff:
  fixes x :: "'a :: {banach, second_countable_topology}"
  shows "c \<noteq> 0 \<Longrightarrow>
    has_bochner_integral lborel f x \<longleftrightarrow>
    has_bochner_integral lborel (\<lambda>x. f (t + c * x)) (x /\<^sub>R \<bar>c\<bar>)"
  unfolding has_bochner_integral_iff lborel_integrable_real_affine_iff
  by (simp_all add: lborel_integral_real_affine[symmetric] divideR_right cong: conj_cong)

lemma lborel_distr_uminus: "distr lborel borel uminus = (lborel :: real measure)"
  by (subst lborel_real_affine[of "-1" 0])
     (auto simp: density_1 one_ennreal_def[symmetric])

lemma lborel_distr_mult:
  assumes "(c::real) \<noteq> 0"
  shows "distr lborel borel (op * c) = density lborel (\<lambda>_. inverse \<bar>c\<bar>)"
proof-
  have "distr lborel borel (op * c) = distr lborel lborel (op * c)" by (simp cong: distr_cong)
  also from assms have "... = density lborel (\<lambda>_. inverse \<bar>c\<bar>)"
    by (subst lborel_real_affine[of "inverse c" 0]) (auto simp: o_def distr_density_distr)
  finally show ?thesis .
qed

lemma lborel_distr_mult':
  assumes "(c::real) \<noteq> 0"
  shows "lborel = density (distr lborel borel (op * c)) (\<lambda>_. \<bar>c\<bar>)"
proof-
  have "lborel = density lborel (\<lambda>_. 1)" by (rule density_1[symmetric])
  also from assms have "(\<lambda>_. 1 :: ennreal) = (\<lambda>_. inverse \<bar>c\<bar> * \<bar>c\<bar>)" by (intro ext) simp
  also have "density lborel ... = density (density lborel (\<lambda>_. inverse \<bar>c\<bar>)) (\<lambda>_. \<bar>c\<bar>)"
    by (subst density_density_eq) (auto simp: ennreal_mult)
  also from assms have "density lborel (\<lambda>_. inverse \<bar>c\<bar>) = distr lborel borel (op * c)"
    by (rule lborel_distr_mult[symmetric])
  finally show ?thesis .
qed

lemma lborel_distr_plus: "distr lborel borel (op + c) = (lborel :: real measure)"
  by (subst lborel_real_affine[of 1 c]) (auto simp: density_1 one_ennreal_def[symmetric])

interpretation lborel: sigma_finite_measure lborel
  by (rule sigma_finite_lborel)

interpretation lborel_pair: pair_sigma_finite lborel lborel ..

lemma lborel_prod:
  "lborel \<Otimes>\<^sub>M lborel = (lborel :: ('a::euclidean_space \<times> 'b::euclidean_space) measure)"
proof (rule lborel_eqI[symmetric], clarify)
  fix la ua :: 'a and lb ub :: 'b
  assume lu: "\<And>a b. (a, b) \<in> Basis \<Longrightarrow> (la, lb) \<bullet> (a, b) \<le> (ua, ub) \<bullet> (a, b)"
  have [simp]:
    "\<And>b. b \<in> Basis \<Longrightarrow> la \<bullet> b \<le> ua \<bullet> b"
    "\<And>b. b \<in> Basis \<Longrightarrow> lb \<bullet> b \<le> ub \<bullet> b"
    "inj_on (\<lambda>u. (u, 0)) Basis" "inj_on (\<lambda>u. (0, u)) Basis"
    "(\<lambda>u. (u, 0)) ` Basis \<inter> (\<lambda>u. (0, u)) ` Basis = {}"
    "box (la, lb) (ua, ub) = box la ua \<times> box lb ub"
    using lu[of _ 0] lu[of 0] by (auto intro!: inj_onI simp add: Basis_prod_def ball_Un box_def)
  show "emeasure (lborel \<Otimes>\<^sub>M lborel) (box (la, lb) (ua, ub)) =
      ennreal (setprod (op \<bullet> ((ua, ub) - (la, lb))) Basis)"
    by (simp add: lborel.emeasure_pair_measure_Times Basis_prod_def setprod.union_disjoint
                  setprod.reindex ennreal_mult inner_diff_left setprod_nonneg)
qed (simp add: borel_prod[symmetric])

(* FIXME: conversion in measurable prover *)
lemma lborelD_Collect[measurable (raw)]: "{x\<in>space borel. P x} \<in> sets borel \<Longrightarrow> {x\<in>space lborel. P x} \<in> sets lborel" by simp
lemma lborelD[measurable (raw)]: "A \<in> sets borel \<Longrightarrow> A \<in> sets lborel" by simp

lemma emeasure_bounded_finite:
  assumes "bounded A" shows "emeasure lborel A < \<infinity>"
proof -
  from bounded_subset_cbox[OF \<open>bounded A\<close>] obtain a b where "A \<subseteq> cbox a b"
    by auto
  then have "emeasure lborel A \<le> emeasure lborel (cbox a b)"
    by (intro emeasure_mono) auto
  then show ?thesis
    by (auto simp: emeasure_lborel_cbox_eq setprod_nonneg less_top[symmetric] top_unique split: if_split_asm)
qed

lemma emeasure_compact_finite: "compact A \<Longrightarrow> emeasure lborel A < \<infinity>"
  using emeasure_bounded_finite[of A] by (auto intro: compact_imp_bounded)

lemma borel_integrable_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "compact S" "continuous_on S f"
  shows "integrable lborel (\<lambda>x. indicator S x *\<^sub>R f x)"
proof cases
  assume "S \<noteq> {}"
  have "continuous_on S (\<lambda>x. norm (f x))"
    using assms by (intro continuous_intros)
  from continuous_attains_sup[OF \<open>compact S\<close> \<open>S \<noteq> {}\<close> this]
  obtain M where M: "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> M"
    by auto

  show ?thesis
  proof (rule integrable_bound)
    show "integrable lborel (\<lambda>x. indicator S x * M)"
      using assms by (auto intro!: emeasure_compact_finite borel_compact integrable_mult_left)
    show "(\<lambda>x. indicator S x *\<^sub>R f x) \<in> borel_measurable lborel"
      using assms by (auto intro!: borel_measurable_continuous_on_indicator borel_compact)
    show "AE x in lborel. norm (indicator S x *\<^sub>R f x) \<le> norm (indicator S x * M)"
      by (auto split: split_indicator simp: abs_real_def dest!: M)
  qed
qed simp

lemma borel_integrable_atLeastAtMost:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows "integrable lborel (\<lambda>x. f x * indicator {a .. b} x)" (is "integrable _ ?f")
proof -
  have "integrable lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x)"
  proof (rule borel_integrable_compact)
    from f show "continuous_on {a..b} f"
      by (auto intro: continuous_at_imp_continuous_on)
  qed simp
  then show ?thesis
    by (auto simp: mult.commute)
qed

end

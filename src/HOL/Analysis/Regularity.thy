(*  Title:      HOL/Analysis/Regularity.thy
    Author:     Fabian Immler, TU München
*)

section \<open>Regularity of Measures\<close>

theory Regularity (* FIX suggestion to rename  e.g. RegularityMeasures and/ or move as
this theory consists of 1 result only  *)
imports Measure_Space Borel_Space
begin

theorem
  fixes M::"'a::{second_countable_topology, complete_space} measure"
  assumes sb: "sets M = sets borel"
  assumes "emeasure M (space M) \<noteq> \<infinity>"
  assumes "B \<in> sets borel"
  shows inner_regular: "emeasure M B =
    (SUP K \<in> {K. K \<subseteq> B \<and> compact K}. emeasure M K)" (is "?inner B")
  and outer_regular: "emeasure M B =
    (INF U \<in> {U. B \<subseteq> U \<and> open U}. emeasure M U)" (is "?outer B")
proof -
  have Us: "UNIV = space M" by (metis assms(1) sets_eq_imp_space_eq space_borel)
  hence sU: "space M = UNIV" by simp
  interpret finite_measure M by rule fact
  have approx_inner: "\<And>A. A \<in> sets M \<Longrightarrow>
    (\<And>e. e > 0 \<Longrightarrow> \<exists>K. K \<subseteq> A \<and> compact K \<and> emeasure M A \<le> emeasure M K + ennreal e) \<Longrightarrow> ?inner A"
    by (rule ennreal_approx_SUP)
      (force intro!: emeasure_mono simp: compact_imp_closed emeasure_eq_measure)+
  have approx_outer: "\<And>A. A \<in> sets M \<Longrightarrow>
    (\<And>e. e > 0 \<Longrightarrow> \<exists>B. A \<subseteq> B \<and> open B \<and> emeasure M B \<le> emeasure M A + ennreal e) \<Longrightarrow> ?outer A"
    by (rule ennreal_approx_INF)
       (force intro!: emeasure_mono simp: emeasure_eq_measure sb)+
  from countable_dense_setE obtain X :: "'a set"
    where X: "countable X" "\<And>Y :: 'a set. open Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> \<exists>d\<in>X. d \<in> Y"
    by auto
  {
    fix r::real assume "r > 0" hence "\<And>y. open (ball y r)" "\<And>y. ball y r \<noteq> {}" by auto
    with X(2)[OF this]
    have x: "space M = (\<Union>x\<in>X. cball x r)"
      by (auto simp add: sU) (metis dist_commute order_less_imp_le)
    let ?U = "\<Union>k. (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)"
    have "(\<lambda>k. emeasure M (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)) \<longlonglongrightarrow> M ?U"
      by (rule Lim_emeasure_incseq) (auto intro!: borel_closed bexI simp: incseq_def Us sb)
    also have "?U = space M"
    proof safe
      fix x from X(2)[OF open_ball[of x r]] \<open>r > 0\<close> obtain d where d: "d\<in>X" "d \<in> ball x r" by auto
      show "x \<in> ?U"
        using X(1) d
        by simp (auto intro!: exI [where x = "to_nat_on X d"] simp: dist_commute Bex_def)
    qed (simp add: sU)
    finally have "(\<lambda>k. M (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)) \<longlonglongrightarrow> M (space M)" .
  } note M_space = this
  {
    fix e ::real and n :: nat assume "e > 0" "n > 0"
    hence "1/n > 0" "e * 2 powr - n > 0" by (auto)
    from M_space[OF \<open>1/n>0\<close>]
    have "(\<lambda>k. measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n))) \<longlonglongrightarrow> measure M (space M)"
      unfolding emeasure_eq_measure by (auto)
    from metric_LIMSEQ_D[OF this \<open>0 < e * 2 powr -n\<close>]
    obtain k where "dist (measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n))) (measure M (space M)) <
      e * 2 powr -n"
      by auto
    hence "measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n)) \<ge>
      measure M (space M) - e * 2 powr -real n"
      by (auto simp: dist_real_def)
    hence "\<exists>k. measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n)) \<ge>
      measure M (space M) - e * 2 powr - real n" ..
  } note k=this
  hence "\<forall>e\<in>{0<..}. \<forall>(n::nat)\<in>{0<..}. \<exists>k.
    measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n)) \<ge> measure M (space M) - e * 2 powr - real n"
    by blast
  then obtain k where k: "\<forall>e\<in>{0<..}. \<forall>n\<in>{0<..}. measure M (space M) - e * 2 powr - real (n::nat)
    \<le> measure M (\<Union>i\<in>{0..k e n}. cball (from_nat_into X i) (1 / n))"
    by metis
  hence k: "\<And>e n. e > 0 \<Longrightarrow> n > 0 \<Longrightarrow> measure M (space M) - e * 2 powr - n
    \<le> measure M (\<Union>i\<in>{0..k e n}. cball (from_nat_into X i) (1 / n))"
    unfolding Ball_def by blast
  have approx_space:
    "\<exists>K \<in> {K. K \<subseteq> space M \<and> compact K}. emeasure M (space M) \<le> emeasure M K + ennreal e"
    (is "?thesis e") if "0 < e" for e :: real
  proof -
    define B where [abs_def]:
      "B n = (\<Union>i\<in>{0..k e (Suc n)}. cball (from_nat_into X i) (1 / Suc n))" for n
    have "\<And>n. closed (B n)" by (auto simp: B_def)
    hence [simp]: "\<And>n. B n \<in> sets M" by (simp add: sb)
    from k[OF \<open>e > 0\<close> zero_less_Suc]
    have "\<And>n. measure M (space M) - measure M (B n) \<le> e * 2 powr - real (Suc n)"
      by (simp add: algebra_simps B_def finite_measure_compl)
    hence B_compl_le: "\<And>n::nat. measure M (space M - B n) \<le> e * 2 powr - real (Suc n)"
      by (simp add: finite_measure_compl)
    define K where "K = (\<Inter>n. B n)"
    from \<open>closed (B _)\<close> have "closed K" by (auto simp: K_def)
    hence [simp]: "K \<in> sets M" by (simp add: sb)
    have "measure M (space M) - measure M K = measure M (space M - K)"
      by (simp add: finite_measure_compl)
    also have "\<dots> = emeasure M (\<Union>n. space M - B n)" by (auto simp: K_def emeasure_eq_measure)
    also have "\<dots> \<le> (\<Sum>n. emeasure M (space M - B n))"
      by (rule emeasure_subadditive_countably) (auto simp: summable_def)
    also have "\<dots> \<le> (\<Sum>n. ennreal (e*2 powr - real (Suc n)))"
      using B_compl_le by (intro suminf_le) (simp_all add: emeasure_eq_measure ennreal_leI)
    also have "\<dots> \<le> (\<Sum>n. ennreal (e * (1 / 2) ^ Suc n))"
      by (simp add: powr_minus powr_realpow field_simps del: of_nat_Suc)
    also have "\<dots> = ennreal e * (\<Sum>n. ennreal ((1 / 2) ^ Suc n))"
      unfolding ennreal_power[symmetric]
      using \<open>0 < e\<close>
      by (simp add: ac_simps ennreal_mult' divide_ennreal[symmetric] divide_ennreal_def
                    ennreal_power[symmetric])
    also have "\<dots> = e"
      by (subst suminf_ennreal_eq[OF zero_le_power power_half_series]) auto
    finally have "measure M (space M) \<le> measure M K + e"
      using \<open>0 < e\<close> by simp
    hence "emeasure M (space M) \<le> emeasure M K + e"
      using \<open>0 < e\<close> by (simp add: emeasure_eq_measure flip: ennreal_plus)
    moreover have "compact K"
      unfolding compact_eq_totally_bounded
    proof safe
      show "complete K" using \<open>closed K\<close> by (simp add: complete_eq_closed)
      fix e'::real assume "0 < e'"
      then obtain n where n: "1 / real (Suc n) < e'" by (rule nat_approx_posE)
      let ?k = "from_nat_into X ` {0..k e (Suc n)}"
      have "finite ?k" by simp
      moreover have "K \<subseteq> (\<Union>x\<in>?k. ball x e')" unfolding K_def B_def using n by force
      ultimately show "\<exists>k. finite k \<and> K \<subseteq> (\<Union>x\<in>k. ball x e')" by blast
    qed
    ultimately
    show ?thesis by (auto simp: sU)
  qed
  { fix A::"'a set" assume "closed A" hence "A \<in> sets borel" by (simp add: compact_imp_closed)
    hence [simp]: "A \<in> sets M" by (simp add: sb)
    have "?inner A"
    proof (rule approx_inner)
      fix e::real assume "e > 0"
      from approx_space[OF this] obtain K where
        K: "K \<subseteq> space M" "compact K" "emeasure M (space M) \<le> emeasure M K + e"
        by (auto simp: emeasure_eq_measure)
      hence [simp]: "K \<in> sets M" by (simp add: sb compact_imp_closed)
      have "measure M A - measure M (A \<inter> K) = measure M (A - A \<inter> K)"
        by (subst finite_measure_Diff) auto
      also have "A - A \<inter> K = A \<union> K - K" by auto
      also have "measure M \<dots> = measure M (A \<union> K) - measure M K"
        by (subst finite_measure_Diff) auto
      also have "\<dots> \<le> measure M (space M) - measure M K"
        by (simp add: emeasure_eq_measure sU sb finite_measure_mono)
      also have "\<dots> \<le> e"
        using K \<open>0 < e\<close> by (simp add: emeasure_eq_measure flip: ennreal_plus)
      finally have "emeasure M A \<le> emeasure M (A \<inter> K) + ennreal e"
        using \<open>0<e\<close> by (simp add: emeasure_eq_measure algebra_simps flip: ennreal_plus)
      moreover have "A \<inter> K \<subseteq> A" "compact (A \<inter> K)" using \<open>closed A\<close> \<open>compact K\<close> by auto
      ultimately show "\<exists>K \<subseteq> A. compact K \<and> emeasure M A \<le> emeasure M K + ennreal e"
        by blast
    qed simp
    have "?outer A"
    proof cases
      assume "A \<noteq> {}"
      let ?G = "\<lambda>d. {x. infdist x A < d}"
      {
        fix d
        have "?G d = (\<lambda>x. infdist x A) -` {..<d}" by auto
        also have "open \<dots>"
          by (intro continuous_open_vimage) (auto intro!: continuous_infdist continuous_ident)
        finally have "open (?G d)" .
      } note open_G = this
      from in_closed_iff_infdist_zero[OF \<open>closed A\<close> \<open>A \<noteq> {}\<close>]
      have "A = {x. infdist x A = 0}" by auto
      also have "\<dots> = (\<Inter>i. ?G (1/real (Suc i)))"
      proof (auto simp del: of_nat_Suc, rule ccontr)
        fix x
        assume "infdist x A \<noteq> 0"
        then have pos: "infdist x A > 0" using infdist_nonneg[of x A] by simp
        then obtain n where n: "1 / real (Suc n) < infdist x A" by (rule nat_approx_posE)
        assume "\<forall>i. infdist x A < 1 / real (Suc i)"
        then have "infdist x A < 1 / real (Suc n)" by auto
        with n show False by simp
      qed
      also have "M \<dots> = (INF n. emeasure M (?G (1 / real (Suc n))))"
      proof (rule INF_emeasure_decseq[symmetric], safe)
        fix i::nat
        from open_G[of "1 / real (Suc i)"]
        show "?G (1 / real (Suc i)) \<in> sets M" by (simp add: sb borel_open)
      next
        show "decseq (\<lambda>i. {x. infdist x A < 1 / real (Suc i)})"
          by (auto intro: less_trans intro!: divide_strict_left_mono
            simp: decseq_def le_eq_less_or_eq)
      qed simp
      finally
      have "emeasure M A = (INF n. emeasure M {x. infdist x A < 1 / real (Suc n)})" .
      moreover
      have "\<dots> \<ge> (INF U\<in>{U. A \<subseteq> U \<and> open U}. emeasure M U)"
      proof (intro INF_mono)
        fix m
        have "?G (1 / real (Suc m)) \<in> {U. A \<subseteq> U \<and> open U}" using open_G by auto
        moreover have "M (?G (1 / real (Suc m))) \<le> M (?G (1 / real (Suc m)))" by simp
        ultimately show "\<exists>U\<in>{U. A \<subseteq> U \<and> open U}.
          emeasure M U \<le> emeasure M {x. infdist x A < 1 / real (Suc m)}"
          by blast
      qed
      moreover
      have "emeasure M A \<le> (INF U\<in>{U. A \<subseteq> U \<and> open U}. emeasure M U)"
        by (rule INF_greatest) (auto intro!: emeasure_mono simp: sb)
      ultimately show ?thesis by simp
    qed (auto intro!: INF_eqI)
    note \<open>?inner A\<close> \<open>?outer A\<close> }
  note closed_in_D = this
  from \<open>B \<in> sets borel\<close>
  have "Int_stable (Collect closed)" "Collect closed \<subseteq> Pow UNIV" "B \<in> sigma_sets UNIV (Collect closed)"
    by (auto simp: Int_stable_def borel_eq_closed)
  then show "?inner B" "?outer B"
  proof (induct B rule: sigma_sets_induct_disjoint)
    case empty
    { case 1 show ?case by (intro SUP_eqI[symmetric]) auto }
    { case 2 show ?case by (intro INF_eqI[symmetric]) (auto elim!: meta_allE[of _ "{}"]) }
  next
    case (basic B)
    { case 1 from basic closed_in_D show ?case by auto }
    { case 2 from basic closed_in_D show ?case by auto }
  next
    case (compl B)
    note inner = compl(2) and outer = compl(3)
    from compl have [simp]: "B \<in> sets M" by (auto simp: sb borel_eq_closed)
    case 2
    have "M (space M - B) = M (space M) - emeasure M B" by (auto simp: emeasure_compl)
    also have "\<dots> = (INF K\<in>{K. K \<subseteq> B \<and> compact K}. M (space M) -  M K)"
      by (subst ennreal_SUP_const_minus) (auto simp: less_top[symmetric] inner)
    also have "\<dots> = (INF U\<in>{U. U \<subseteq> B \<and> compact U}. M (space M - U))"
      by (auto simp add: emeasure_compl sb compact_imp_closed)
    also have "\<dots> \<ge> (INF U\<in>{U. U \<subseteq> B \<and> closed U}. M (space M - U))"
      by (rule INF_superset_mono) (auto simp add: compact_imp_closed)
    also have "(INF U\<in>{U. U \<subseteq> B \<and> closed U}. M (space M - U)) =
        (INF U\<in>{U. space M - B \<subseteq> U \<and> open U}. emeasure M U)"
      apply (rule arg_cong [of _ _ Inf])
      using sU
      apply (auto simp add: image_iff)
      apply (rule exI [of _ "UNIV - y" for y])
      apply safe
        apply (auto simp add: double_diff)
      done
    finally have
      "(INF U\<in>{U. space M - B \<subseteq> U \<and> open U}. emeasure M U) \<le> emeasure M (space M - B)" .
    moreover have
      "(INF U\<in>{U. space M - B \<subseteq> U \<and> open U}. emeasure M U) \<ge> emeasure M (space M - B)"
      by (auto simp: sb sU intro!: INF_greatest emeasure_mono)
    ultimately show ?case by (auto intro!: antisym simp: sets_eq_imp_space_eq[OF sb])

    case 1
    have "M (space M - B) = M (space M) - emeasure M B" by (auto simp: emeasure_compl)
    also have "\<dots> = (SUP U\<in> {U. B \<subseteq> U \<and> open U}. M (space M) -  M U)"
      unfolding outer by (subst ennreal_INF_const_minus) auto
    also have "\<dots> = (SUP U\<in>{U. B \<subseteq> U \<and> open U}. M (space M - U))"
      by (auto simp add: emeasure_compl sb compact_imp_closed)
    also have "\<dots> = (SUP K\<in>{K. K \<subseteq> space M - B \<and> closed K}. emeasure M K)"
      unfolding SUP_image [of _ "\<lambda>u. space M - u" _, symmetric, unfolded comp_def]
      apply (rule arg_cong [of _ _ Sup])
      using sU apply (auto intro!: imageI)
      done
    also have "\<dots> = (SUP K\<in>{K. K \<subseteq> space M - B \<and> compact K}. emeasure M K)"
    proof (safe intro!: antisym SUP_least)
      fix K assume "closed K" "K \<subseteq> space M - B"
      from closed_in_D[OF \<open>closed K\<close>]
      have K_inner: "emeasure M K = (SUP K\<in>{Ka. Ka \<subseteq> K \<and> compact Ka}. emeasure M K)" by simp
      show "emeasure M K \<le> (SUP K\<in>{K. K \<subseteq> space M - B \<and> compact K}. emeasure M K)"
        unfolding K_inner using \<open>K \<subseteq> space M - B\<close>
        by (auto intro!: SUP_upper SUP_least)
    qed (fastforce intro!: SUP_least SUP_upper simp: compact_imp_closed)
    finally show ?case by (auto intro!: antisym simp: sets_eq_imp_space_eq[OF sb])
  next
    case (union D)
    then have "range D \<subseteq> sets M" by (auto simp: sb borel_eq_closed)
    with union have M[symmetric]: "(\<Sum>i. M (D i)) = M (\<Union>i. D i)" by (intro suminf_emeasure)
    also have "(\<lambda>n. \<Sum>i<n. M (D i)) \<longlonglongrightarrow> (\<Sum>i. M (D i))"
      by (intro summable_LIMSEQ) auto
    finally have measure_LIMSEQ: "(\<lambda>n. \<Sum>i<n. measure M (D i)) \<longlonglongrightarrow> measure M (\<Union>i. D i)"
      by (simp add: emeasure_eq_measure sum_nonneg)
    have "(\<Union>i. D i) \<in> sets M" using \<open>range D \<subseteq> sets M\<close> by auto

    case 1
    show ?case
    proof (rule approx_inner)
      fix e::real assume "e > 0"
      with measure_LIMSEQ
      have "\<exists>no. \<forall>n\<ge>no. \<bar>(\<Sum>i<n. measure M (D i)) -measure M (\<Union>x. D x)\<bar> < e/2"
        by (auto simp: lim_sequentially dist_real_def simp del: less_divide_eq_numeral1)
      hence "\<exists>n0. \<bar>(\<Sum>i<n0. measure M (D i)) - measure M (\<Union>x. D x)\<bar> < e/2" by auto
      then obtain n0 where n0: "\<bar>(\<Sum>i<n0. measure M (D i)) - measure M (\<Union>i. D i)\<bar> < e/2"
        unfolding choice_iff by blast
      have "ennreal (\<Sum>i<n0. measure M (D i)) = (\<Sum>i<n0. M (D i))"
        by (auto simp add: emeasure_eq_measure)
      also have "\<dots> \<le> (\<Sum>i. M (D i))" by (rule sum_le_suminf) auto
      also have "\<dots> = M (\<Union>i. D i)" by (simp add: M)
      also have "\<dots> = measure M (\<Union>i. D i)" by (simp add: emeasure_eq_measure)
      finally have n0: "measure M (\<Union>i. D i) - (\<Sum>i<n0. measure M (D i)) < e/2"
        using n0 by (auto simp: sum_nonneg)
      have "\<forall>i. \<exists>K. K \<subseteq> D i \<and> compact K \<and> emeasure M (D i) \<le> emeasure M K + e/(2*Suc n0)"
      proof
        fix i
        from \<open>0 < e\<close> have "0 < e/(2*Suc n0)" by simp
        have "emeasure M (D i) = (SUP K\<in>{K. K \<subseteq> (D i) \<and> compact K}. emeasure M K)"
          using union by blast
        from SUP_approx_ennreal[OF \<open>0 < e/(2*Suc n0)\<close> _ this]
        show "\<exists>K. K \<subseteq> D i \<and> compact K \<and> emeasure M (D i) \<le> emeasure M K + e/(2*Suc n0)"
          by (auto simp: emeasure_eq_measure intro: less_imp_le compact_empty)
      qed
      then obtain K where K: "\<And>i. K i \<subseteq> D i" "\<And>i. compact (K i)"
        "\<And>i. emeasure M (D i) \<le> emeasure M (K i) + e/(2*Suc n0)"
        unfolding choice_iff by blast
      let ?K = "\<Union>i\<in>{..<n0}. K i"
      have "disjoint_family_on K {..<n0}" using K \<open>disjoint_family D\<close>
        unfolding disjoint_family_on_def by blast
      hence mK: "measure M ?K = (\<Sum>i<n0. measure M (K i))" using K
        by (intro finite_measure_finite_Union) (auto simp: sb compact_imp_closed)
      have "measure M (\<Union>i. D i) < (\<Sum>i<n0. measure M (D i)) + e/2" using n0 by simp
      also have "(\<Sum>i<n0. measure M (D i)) \<le> (\<Sum>i<n0. measure M (K i) + e/(2*Suc n0))"
        using K \<open>0 < e\<close>
        by (auto intro: sum_mono simp: emeasure_eq_measure simp flip: ennreal_plus)
      also have "\<dots> = (\<Sum>i<n0. measure M (K i)) + (\<Sum>i<n0. e/(2*Suc n0))"
        by (simp add: sum.distrib)
      also have "\<dots> \<le> (\<Sum>i<n0. measure M (K i)) +  e / 2" using \<open>0 < e\<close>
        by (auto simp: field_simps intro!: mult_left_mono)
      finally
      have "measure M (\<Union>i. D i) < (\<Sum>i<n0. measure M (K i)) + e / 2 + e / 2"
        by auto
      hence "M (\<Union>i. D i) < M ?K + e"
        using \<open>0<e\<close> by (auto simp: mK emeasure_eq_measure sum_nonneg ennreal_less_iff simp flip: ennreal_plus)
      moreover
      have "?K \<subseteq> (\<Union>i. D i)" using K by auto
      moreover
      have "compact ?K" using K by auto
      ultimately
      have "?K\<subseteq>(\<Union>i. D i) \<and> compact ?K \<and> emeasure M (\<Union>i. D i) \<le> emeasure M ?K + ennreal e" by simp
      thus "\<exists>K\<subseteq>\<Union>i. D i. compact K \<and> emeasure M (\<Union>i. D i) \<le> emeasure M K + ennreal e" ..
    qed fact
    case 2
    show ?case
    proof (rule approx_outer[OF \<open>(\<Union>i. D i) \<in> sets M\<close>])
      fix e::real assume "e > 0"
      have "\<forall>i::nat. \<exists>U. D i \<subseteq> U \<and> open U \<and> e/(2 powr Suc i) > emeasure M U - emeasure M (D i)"
      proof
        fix i::nat
        from \<open>0 < e\<close> have "0 < e/(2 powr Suc i)" by simp
        have "emeasure M (D i) = (INF U\<in>{U. (D i) \<subseteq> U \<and> open U}. emeasure M U)"
          using union by blast
        from INF_approx_ennreal[OF \<open>0 < e/(2 powr Suc i)\<close> this]
        show "\<exists>U. D i \<subseteq> U \<and> open U \<and> e/(2 powr Suc i) > emeasure M U - emeasure M (D i)"
          using \<open>0<e\<close>
          by (auto simp: emeasure_eq_measure sum_nonneg ennreal_less_iff ennreal_minus
                         finite_measure_mono sb
                   simp flip: ennreal_plus)
      qed
      then obtain U where U: "\<And>i. D i \<subseteq> U i" "\<And>i. open (U i)"
        "\<And>i. e/(2 powr Suc i) > emeasure M (U i) - emeasure M (D i)"
        unfolding choice_iff by blast
      let ?U = "\<Union>i. U i"
      have "ennreal (measure M ?U - measure M (\<Union>i. D i)) = M ?U - M (\<Union>i. D i)"
        using U(1,2)
        by (subst ennreal_minus[symmetric])
           (auto intro!: finite_measure_mono simp: sb emeasure_eq_measure)
      also have "\<dots> = M (?U - (\<Union>i. D i))" using U  \<open>(\<Union>i. D i) \<in> sets M\<close>
        by (subst emeasure_Diff) (auto simp: sb)
      also have "\<dots> \<le> M (\<Union>i. U i - D i)" using U  \<open>range D \<subseteq> sets M\<close>
        by (intro emeasure_mono) (auto simp: sb intro!: sets.countable_nat_UN sets.Diff)
      also have "\<dots> \<le> (\<Sum>i. M (U i - D i))" using U  \<open>range D \<subseteq> sets M\<close>
        by (intro emeasure_subadditive_countably) (auto intro!: sets.Diff simp: sb)
      also have "\<dots> \<le> (\<Sum>i. ennreal e/(2 powr Suc i))" using U \<open>range D \<subseteq> sets M\<close>
        using \<open>0<e\<close>
        by (intro suminf_le, subst emeasure_Diff)
           (auto simp: emeasure_Diff emeasure_eq_measure sb ennreal_minus
                       finite_measure_mono divide_ennreal ennreal_less_iff
                 intro: less_imp_le)
      also have "\<dots> \<le> (\<Sum>n. ennreal (e * (1 / 2) ^ Suc n))"
        using \<open>0<e\<close>
        by (simp add: powr_minus powr_realpow field_simps divide_ennreal del: of_nat_Suc)
      also have "\<dots> = ennreal e * (\<Sum>n. ennreal ((1 / 2) ^  Suc n))"
        unfolding ennreal_power[symmetric]
        using \<open>0 < e\<close>
        by (simp add: ac_simps ennreal_mult' divide_ennreal[symmetric] divide_ennreal_def
                      ennreal_power[symmetric])
      also have "\<dots> = ennreal e"
        by (subst suminf_ennreal_eq[OF zero_le_power power_half_series]) auto
      finally have "emeasure M ?U \<le> emeasure M (\<Union>i. D i) + ennreal e"
        using \<open>0<e\<close> by (simp add: emeasure_eq_measure flip: ennreal_plus)
      moreover
      have "(\<Union>i. D i) \<subseteq> ?U" using U by auto
      moreover
      have "open ?U" using U by auto
      ultimately
      have "(\<Union>i. D i) \<subseteq> ?U \<and> open ?U \<and> emeasure M ?U \<le> emeasure M (\<Union>i. D i) + ennreal e" by simp
      thus "\<exists>B. (\<Union>i. D i) \<subseteq> B \<and> open B \<and> emeasure M B \<le> emeasure M (\<Union>i. D i) + ennreal e" ..
    qed
  qed
qed

end


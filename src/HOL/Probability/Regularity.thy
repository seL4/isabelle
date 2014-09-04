(*  Title:      HOL/Probability/Regularity.thy
    Author:     Fabian Immler, TU München
*)

header {* Regularity of Measures *}

theory Regularity
imports Measure_Space Borel_Space
begin

lemma ereal_approx_SUP:
  fixes x::ereal
  assumes A_notempty: "A \<noteq> {}"
  assumes f_bound: "\<And>i. i \<in> A \<Longrightarrow> f i \<le> x"
  assumes f_fin: "\<And>i. i \<in> A \<Longrightarrow> f i \<noteq> \<infinity>"
  assumes f_nonneg: "\<And>i. 0 \<le> f i"
  assumes approx: "\<And>e. (e::real) > 0 \<Longrightarrow> \<exists>i \<in> A. x \<le> f i + e"
  shows "x = (SUP i : A. f i)"
proof (subst eq_commute, rule SUP_eqI)
  show "\<And>i. i \<in> A \<Longrightarrow> f i \<le> x" using f_bound by simp
next
  fix y :: ereal assume f_le_y: "(\<And>i::'a. i \<in> A \<Longrightarrow> f i \<le> y)"
  with A_notempty f_nonneg have "y \<ge> 0" by auto (metis order_trans)
  show "x \<le> y"
  proof (rule ccontr)
    assume "\<not> x \<le> y" hence "x > y" by simp
    hence y_fin: "\<bar>y\<bar> \<noteq> \<infinity>" using `y \<ge> 0` by auto
    have x_fin: "\<bar>x\<bar> \<noteq> \<infinity>" using `x > y` f_fin approx[where e = 1] by auto
    def e \<equiv> "real ((x - y) / 2)"
    have e: "x > y + e" "e > 0" using `x > y` y_fin x_fin by (auto simp: e_def field_simps)
    note e(1)
    also from approx[OF `e > 0`] obtain i where i: "i \<in> A" "x \<le> f i + e" by blast
    note i(2)
    finally have "y < f i" using y_fin f_fin by (metis add_right_mono linorder_not_le)
    moreover have "f i \<le> y" by (rule f_le_y) fact
    ultimately show False by simp
  qed
qed

lemma ereal_approx_INF:
  fixes x::ereal
  assumes A_notempty: "A \<noteq> {}"
  assumes f_bound: "\<And>i. i \<in> A \<Longrightarrow> x \<le> f i"
  assumes f_fin: "\<And>i. i \<in> A \<Longrightarrow> f i \<noteq> \<infinity>"
  assumes f_nonneg: "\<And>i. 0 \<le> f i"
  assumes approx: "\<And>e. (e::real) > 0 \<Longrightarrow> \<exists>i \<in> A. f i \<le> x + e"
  shows "x = (INF i : A. f i)"
proof (subst eq_commute, rule INF_eqI)
  show "\<And>i. i \<in> A \<Longrightarrow> x \<le> f i" using f_bound by simp
next
  fix y :: ereal assume f_le_y: "(\<And>i::'a. i \<in> A \<Longrightarrow> y \<le> f i)"
  with A_notempty f_fin have "y \<noteq> \<infinity>" by force
  show "y \<le> x"
  proof (rule ccontr)
    assume "\<not> y \<le> x" hence "y > x" by simp hence "y \<noteq> - \<infinity>" by auto
    hence y_fin: "\<bar>y\<bar> \<noteq> \<infinity>" using `y \<noteq> \<infinity>` by auto
    have x_fin: "\<bar>x\<bar> \<noteq> \<infinity>" using `y > x` f_fin f_nonneg approx[where e = 1] A_notempty
      apply auto by (metis ereal_infty_less_eq(2) f_le_y)
    def e \<equiv> "real ((y - x) / 2)"
    have e: "y > x + e" "e > 0" using `y > x` y_fin x_fin by (auto simp: e_def field_simps)
    from approx[OF `e > 0`] obtain i where i: "i \<in> A" "x + e \<ge> f i" by blast
    note i(2)
    also note e(1)
    finally have "y > f i" .
    moreover have "y \<le> f i" by (rule f_le_y) fact
    ultimately show False by simp
  qed
qed

lemma INF_approx_ereal:
  fixes x::ereal and e::real
  assumes "e > 0"
  assumes INF: "x = (INF i : A. f i)"
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "\<exists>i \<in> A. f i < x + e"
proof (rule ccontr, clarsimp)
  assume "\<forall>i\<in>A. \<not> f i < x + e"
  moreover
  from INF have "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> y \<le> f i) \<Longrightarrow> y \<le> x" by (auto intro: INF_greatest)
  ultimately
  have "(INF i : A. f i) = x + e" using `e > 0`
    by (intro INF_eqI)
      (force, metis add.comm_neutral add_left_mono ereal_less(1)
        linorder_not_le not_less_iff_gr_or_eq)
  thus False using assms by auto
qed

lemma SUP_approx_ereal:
  fixes x::ereal and e::real
  assumes "e > 0"
  assumes SUP: "x = (SUP i : A. f i)"
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  shows "\<exists>i \<in> A. x \<le> f i + e"
proof (rule ccontr, clarsimp)
  assume "\<forall>i\<in>A. \<not> x \<le> f i + e"
  moreover
  from SUP have "\<And>y. (\<And>i. i \<in> A \<Longrightarrow> f i \<le> y) \<Longrightarrow> y \<ge> x" by (auto intro: SUP_least)
  ultimately
  have "(SUP i : A. f i) = x - e" using `e > 0` `\<bar>x\<bar> \<noteq> \<infinity>`
    by (intro SUP_eqI)
       (metis PInfty_neq_ereal(2) abs_ereal.simps(1) ereal_minus_le linorder_linear,
        metis ereal_between(1) ereal_less(2) less_eq_ereal_def order_trans)
  thus False using assms by auto
qed

lemma
  fixes M::"'a::{second_countable_topology, complete_space} measure"
  assumes sb: "sets M = sets borel"
  assumes "emeasure M (space M) \<noteq> \<infinity>"
  assumes "B \<in> sets borel"
  shows inner_regular: "emeasure M B =
    (SUP K : {K. K \<subseteq> B \<and> compact K}. emeasure M K)" (is "?inner B")
  and outer_regular: "emeasure M B =
    (INF U : {U. B \<subseteq> U \<and> open U}. emeasure M U)" (is "?outer B")
proof -
  have Us: "UNIV = space M" by (metis assms(1) sets_eq_imp_space_eq space_borel)
  hence sU: "space M = UNIV" by simp
  interpret finite_measure M by rule fact
  have approx_inner: "\<And>A. A \<in> sets M \<Longrightarrow>
    (\<And>e. e > 0 \<Longrightarrow> \<exists>K. K \<subseteq> A \<and> compact K \<and> emeasure M A \<le> emeasure M K + ereal e) \<Longrightarrow> ?inner A"
    by (rule ereal_approx_SUP)
      (force intro!: emeasure_mono simp: compact_imp_closed emeasure_eq_measure)+
  have approx_outer: "\<And>A. A \<in> sets M \<Longrightarrow>
    (\<And>e. e > 0 \<Longrightarrow> \<exists>B. A \<subseteq> B \<and> open B \<and> emeasure M B \<le> emeasure M A + ereal e) \<Longrightarrow> ?outer A"
    by (rule ereal_approx_INF)
       (force intro!: emeasure_mono simp: emeasure_eq_measure sb)+
  from countable_dense_setE guess X::"'a set"  . note X = this
  {
    fix r::real assume "r > 0" hence "\<And>y. open (ball y r)" "\<And>y. ball y r \<noteq> {}" by auto
    with X(2)[OF this]
    have x: "space M = (\<Union>x\<in>X. cball x r)"
      by (auto simp add: sU) (metis dist_commute order_less_imp_le)
    let ?U = "\<Union>k. (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)"
    have "(\<lambda>k. emeasure M (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)) ----> M ?U"
      by (rule Lim_emeasure_incseq)
        (auto intro!: borel_closed bexI simp: closed_cball incseq_def Us sb)
    also have "?U = space M"
    proof safe
      fix x from X(2)[OF open_ball[of x r]] `r > 0` obtain d where d: "d\<in>X" "d \<in> ball x r" by auto
      show "x \<in> ?U"
        using X(1) d by (auto intro!: exI[where x="to_nat_on X d"] simp: dist_commute Bex_def)
    qed (simp add: sU)
    finally have "(\<lambda>k. M (\<Union>n\<in>{0..k}. cball (from_nat_into X n) r)) ----> M (space M)" .
  } note M_space = this
  {
    fix e ::real and n :: nat assume "e > 0" "n > 0"
    hence "1/n > 0" "e * 2 powr - n > 0" by (auto)
    from M_space[OF `1/n>0`]
    have "(\<lambda>k. measure M (\<Union>i\<in>{0..k}. cball (from_nat_into X i) (1/real n))) ----> measure M (space M)"
      unfolding emeasure_eq_measure by simp
    from metric_LIMSEQ_D[OF this `0 < e * 2 powr -n`]
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
    "\<And>e. e > 0 \<Longrightarrow>
      \<exists>K \<in> {K. K \<subseteq> space M \<and> compact K}. emeasure M (space M) \<le> emeasure M K + ereal e"
      (is "\<And>e. _ \<Longrightarrow> ?thesis e")
  proof -
    fix e :: real assume "e > 0"
    def B \<equiv> "\<lambda>n. \<Union>i\<in>{0..k e (Suc n)}. cball (from_nat_into X i) (1 / Suc n)"
    have "\<And>n. closed (B n)" by (auto simp: B_def closed_cball)
    hence [simp]: "\<And>n. B n \<in> sets M" by (simp add: sb)
    from k[OF `e > 0` zero_less_Suc]
    have "\<And>n. measure M (space M) - measure M (B n) \<le> e * 2 powr - real (Suc n)"
      by (simp add: algebra_simps B_def finite_measure_compl)
    hence B_compl_le: "\<And>n::nat. measure M (space M - B n) \<le> e * 2 powr - real (Suc n)"
      by (simp add: finite_measure_compl)
    def K \<equiv> "\<Inter>n. B n"
    from `closed (B _)` have "closed K" by (auto simp: K_def)
    hence [simp]: "K \<in> sets M" by (simp add: sb)
    have "measure M (space M) - measure M K = measure M (space M - K)"
      by (simp add: finite_measure_compl)
    also have "\<dots> = emeasure M (\<Union>n. space M - B n)" by (auto simp: K_def emeasure_eq_measure)
    also have "\<dots> \<le> (\<Sum>n. emeasure M (space M - B n))"
      by (rule emeasure_subadditive_countably) (auto simp: summable_def)
    also have "\<dots> \<le> (\<Sum>n. ereal (e*2 powr - real (Suc n)))"
      using B_compl_le by (intro suminf_le_pos) (simp_all add: measure_nonneg emeasure_eq_measure)
    also have "\<dots> \<le> (\<Sum>n. ereal (e * (1 / 2) ^ Suc n))"
      by (simp add: powr_minus inverse_eq_divide powr_realpow field_simps power_divide)
    also have "\<dots> = (\<Sum>n. ereal e * ((1 / 2) ^ Suc n))"
      unfolding times_ereal.simps[symmetric] ereal_power[symmetric] one_ereal_def numeral_eq_ereal
      by simp
    also have "\<dots> = ereal e * (\<Sum>n. ((1 / 2) ^ Suc n))"
      by (rule suminf_cmult_ereal) (auto simp: `0 < e` less_imp_le)
    also have "\<dots> = e" unfolding suminf_half_series_ereal by simp
    finally have "measure M (space M) \<le> measure M K + e" by simp
    hence "emeasure M (space M) \<le> emeasure M K + e" by (simp add: emeasure_eq_measure)
    moreover have "compact K"
      unfolding compact_eq_totally_bounded
    proof safe
      show "complete K" using `closed K` by (simp add: complete_eq_closed)
      fix e'::real assume "0 < e'"
      from nat_approx_posE[OF this] guess n . note n = this
      let ?k = "from_nat_into X ` {0..k e (Suc n)}"
      have "finite ?k" by simp
      moreover have "K \<subseteq> (\<Union>x\<in>?k. ball x e')" unfolding K_def B_def using n by force
      ultimately show "\<exists>k. finite k \<and> K \<subseteq> (\<Union>x\<in>k. ball x e')" by blast
    qed
    ultimately
    show "?thesis e " by (auto simp: sU)
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
      have "M A - M (A \<inter> K) = measure M A - measure M (A \<inter> K)"
        by (simp add: emeasure_eq_measure)
      also have "\<dots> = measure M (A - A \<inter> K)"
        by (subst finite_measure_Diff) auto
      also have "A - A \<inter> K = A \<union> K - K" by auto
      also have "measure M \<dots> = measure M (A \<union> K) - measure M K"
        by (subst finite_measure_Diff) auto
      also have "\<dots> \<le> measure M (space M) - measure M K"
        by (simp add: emeasure_eq_measure sU sb finite_measure_mono)
      also have "\<dots> \<le> e" using K by (simp add: emeasure_eq_measure)
      finally have "emeasure M A \<le> emeasure M (A \<inter> K) + ereal e"
        by (simp add: emeasure_eq_measure algebra_simps)
      moreover have "A \<inter> K \<subseteq> A" "compact (A \<inter> K)" using `closed A` `compact K` by auto
      ultimately show "\<exists>K \<subseteq> A. compact K \<and> emeasure M A \<le> emeasure M K + ereal e"
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
          by (intro continuous_open_vimage) (auto intro!: continuous_infdist continuous_at_id)
        finally have "open (?G d)" .
      } note open_G = this
      from in_closed_iff_infdist_zero[OF `closed A` `A \<noteq> {}`]
      have "A = {x. infdist x A = 0}" by auto
      also have "\<dots> = (\<Inter>i. ?G (1/real (Suc i)))"
      proof (auto, rule ccontr)
        fix x
        assume "infdist x A \<noteq> 0"
        hence pos: "infdist x A > 0" using infdist_nonneg[of x A] by simp
        from nat_approx_posE[OF this] guess n .
        moreover
        assume "\<forall>i. infdist x A < 1 / real (Suc i)"
        hence "infdist x A < 1 / real (Suc n)" by auto
        ultimately show False by simp
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
      have "\<dots> \<ge> (INF U:{U. A \<subseteq> U \<and> open U}. emeasure M U)"
      proof (intro INF_mono)
        fix m
        have "?G (1 / real (Suc m)) \<in> {U. A \<subseteq> U \<and> open U}" using open_G by auto
        moreover have "M (?G (1 / real (Suc m))) \<le> M (?G (1 / real (Suc m)))" by simp
        ultimately show "\<exists>U\<in>{U. A \<subseteq> U \<and> open U}.
          emeasure M U \<le> emeasure M {x. infdist x A < 1 / real (Suc m)}"
          by blast
      qed
      moreover
      have "emeasure M A \<le> (INF U:{U. A \<subseteq> U \<and> open U}. emeasure M U)"
        by (rule INF_greatest) (auto intro!: emeasure_mono simp: sb)
      ultimately show ?thesis by simp
    qed (auto intro!: INF_eqI)
    note `?inner A` `?outer A` }
  note closed_in_D = this
  from `B \<in> sets borel`
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
    also have "\<dots> = (INF K:{K. K \<subseteq> B \<and> compact K}. M (space M) -  M K)"
      unfolding inner by (subst INF_ereal_cminus) force+
    also have "\<dots> = (INF U:{U. U \<subseteq> B \<and> compact U}. M (space M - U))"
      by (rule INF_cong) (auto simp add: emeasure_compl sb compact_imp_closed)
    also have "\<dots> \<ge> (INF U:{U. U \<subseteq> B \<and> closed U}. M (space M - U))"
      by (rule INF_superset_mono) (auto simp add: compact_imp_closed)
    also have "(INF U:{U. U \<subseteq> B \<and> closed U}. M (space M - U)) =
        (INF U:{U. space M - B \<subseteq> U \<and> open U}. emeasure M U)"
      by (subst INF_image [of "\<lambda>u. space M - u", symmetric, unfolded comp_def])
        (rule INF_cong, auto simp add: sU intro!: INF_cong)
    finally have
      "(INF U:{U. space M - B \<subseteq> U \<and> open U}. emeasure M U) \<le> emeasure M (space M - B)" .
    moreover have
      "(INF U:{U. space M - B \<subseteq> U \<and> open U}. emeasure M U) \<ge> emeasure M (space M - B)"
      by (auto simp: sb sU intro!: INF_greatest emeasure_mono)
    ultimately show ?case by (auto intro!: antisym simp: sets_eq_imp_space_eq[OF sb])

    case 1
    have "M (space M - B) = M (space M) - emeasure M B" by (auto simp: emeasure_compl)
    also have "\<dots> = (SUP U: {U. B \<subseteq> U \<and> open U}. M (space M) -  M U)"
      unfolding outer by (subst SUP_ereal_cminus) auto
    also have "\<dots> = (SUP U:{U. B \<subseteq> U \<and> open U}. M (space M - U))"
      by (rule SUP_cong) (auto simp add: emeasure_compl sb compact_imp_closed)
    also have "\<dots> = (SUP K:{K. K \<subseteq> space M - B \<and> closed K}. emeasure M K)"
      by (subst SUP_image [of "\<lambda>u. space M - u", symmetric, simplified comp_def])
         (rule SUP_cong, auto simp: sU)
    also have "\<dots> = (SUP K:{K. K \<subseteq> space M - B \<and> compact K}. emeasure M K)"
    proof (safe intro!: antisym SUP_least)
      fix K assume "closed K" "K \<subseteq> space M - B"
      from closed_in_D[OF `closed K`]
      have K_inner: "emeasure M K = (SUP K:{Ka. Ka \<subseteq> K \<and> compact Ka}. emeasure M K)" by simp
      show "emeasure M K \<le> (SUP K:{K. K \<subseteq> space M - B \<and> compact K}. emeasure M K)"
        unfolding K_inner using `K \<subseteq> space M - B`
        by (auto intro!: SUP_upper SUP_least)
    qed (fastforce intro!: SUP_least SUP_upper simp: compact_imp_closed)
    finally show ?case by (auto intro!: antisym simp: sets_eq_imp_space_eq[OF sb])
  next
    case (union D)
    then have "range D \<subseteq> sets M" by (auto simp: sb borel_eq_closed)
    with union have M[symmetric]: "(\<Sum>i. M (D i)) = M (\<Union>i. D i)" by (intro suminf_emeasure)
    also have "(\<lambda>n. \<Sum>i<n. M (D i)) ----> (\<Sum>i. M (D i))"
      by (intro summable_LIMSEQ summable_ereal_pos emeasure_nonneg)
    finally have measure_LIMSEQ: "(\<lambda>n. \<Sum>i<n. measure M (D i)) ----> measure M (\<Union>i. D i)"
      by (simp add: emeasure_eq_measure)
    have "(\<Union>i. D i) \<in> sets M" using `range D \<subseteq> sets M` by auto
    
    case 1
    show ?case
    proof (rule approx_inner)
      fix e::real assume "e > 0"
      with measure_LIMSEQ
      have "\<exists>no. \<forall>n\<ge>no. \<bar>(\<Sum>i<n. measure M (D i)) -measure M (\<Union>x. D x)\<bar> < e/2"
        by (auto simp: LIMSEQ_def dist_real_def simp del: less_divide_eq_numeral1)
      hence "\<exists>n0. \<bar>(\<Sum>i<n0. measure M (D i)) - measure M (\<Union>x. D x)\<bar> < e/2" by auto
      then obtain n0 where n0: "\<bar>(\<Sum>i<n0. measure M (D i)) - measure M (\<Union>i. D i)\<bar> < e/2"
        unfolding choice_iff by blast
      have "ereal (\<Sum>i<n0. measure M (D i)) = (\<Sum>i<n0. M (D i))"
        by (auto simp add: emeasure_eq_measure)
      also have "\<dots> \<le> (\<Sum>i. M (D i))" by (rule suminf_upper) (auto simp: emeasure_nonneg)
      also have "\<dots> = M (\<Union>i. D i)" by (simp add: M)
      also have "\<dots> = measure M (\<Union>i. D i)" by (simp add: emeasure_eq_measure)
      finally have n0: "measure M (\<Union>i. D i) - (\<Sum>i<n0. measure M (D i)) < e/2"
        using n0 by auto
      have "\<forall>i. \<exists>K. K \<subseteq> D i \<and> compact K \<and> emeasure M (D i) \<le> emeasure M K + e/(2*Suc n0)"
      proof
        fix i
        from `0 < e` have "0 < e/(2*Suc n0)" by simp
        have "emeasure M (D i) = (SUP K:{K. K \<subseteq> (D i) \<and> compact K}. emeasure M K)"
          using union by blast
        from SUP_approx_ereal[OF `0 < e/(2*Suc n0)` this]
        show "\<exists>K. K \<subseteq> D i \<and> compact K \<and> emeasure M (D i) \<le> emeasure M K + e/(2*Suc n0)"
          by (auto simp: emeasure_eq_measure)
      qed
      then obtain K where K: "\<And>i. K i \<subseteq> D i" "\<And>i. compact (K i)"
        "\<And>i. emeasure M (D i) \<le> emeasure M (K i) + e/(2*Suc n0)"
        unfolding choice_iff by blast
      let ?K = "\<Union>i\<in>{..<n0}. K i"
      have "disjoint_family_on K {..<n0}" using K `disjoint_family D`
        unfolding disjoint_family_on_def by blast
      hence mK: "measure M ?K = (\<Sum>i<n0. measure M (K i))" using K
        by (intro finite_measure_finite_Union) (auto simp: sb compact_imp_closed)
      have "measure M (\<Union>i. D i) < (\<Sum>i<n0. measure M (D i)) + e/2" using n0 by simp
      also have "(\<Sum>i<n0. measure M (D i)) \<le> (\<Sum>i<n0. measure M (K i) + e/(2*Suc n0))"
        using K by (auto intro: setsum_mono simp: emeasure_eq_measure)
      also have "\<dots> = (\<Sum>i<n0. measure M (K i)) + (\<Sum>i<n0. e/(2*Suc n0))"
        by (simp add: setsum.distrib)
      also have "\<dots> \<le> (\<Sum>i<n0. measure M (K i)) +  e / 2" using `0 < e`
        by (auto simp: real_of_nat_def[symmetric] field_simps intro!: mult_left_mono)
      finally
      have "measure M (\<Union>i. D i) < (\<Sum>i<n0. measure M (K i)) + e / 2 + e / 2"
        by auto
      hence "M (\<Union>i. D i) < M ?K + e" by (auto simp: mK emeasure_eq_measure)
      moreover
      have "?K \<subseteq> (\<Union>i. D i)" using K by auto
      moreover
      have "compact ?K" using K by auto
      ultimately
      have "?K\<subseteq>(\<Union>i. D i) \<and> compact ?K \<and> emeasure M (\<Union>i. D i) \<le> emeasure M ?K + ereal e" by simp
      thus "\<exists>K\<subseteq>\<Union>i. D i. compact K \<and> emeasure M (\<Union>i. D i) \<le> emeasure M K + ereal e" ..
    qed fact
    case 2
    show ?case
    proof (rule approx_outer[OF `(\<Union>i. D i) \<in> sets M`])
      fix e::real assume "e > 0"
      have "\<forall>i::nat. \<exists>U. D i \<subseteq> U \<and> open U \<and> e/(2 powr Suc i) > emeasure M U - emeasure M (D i)"
      proof
        fix i::nat
        from `0 < e` have "0 < e/(2 powr Suc i)" by simp
        have "emeasure M (D i) = (INF U:{U. (D i) \<subseteq> U \<and> open U}. emeasure M U)"
          using union by blast
        from INF_approx_ereal[OF `0 < e/(2 powr Suc i)` this]
        show "\<exists>U. D i \<subseteq> U \<and> open U \<and> e/(2 powr Suc i) > emeasure M U - emeasure M (D i)"
          by (auto simp: emeasure_eq_measure)
      qed
      then obtain U where U: "\<And>i. D i \<subseteq> U i" "\<And>i. open (U i)"
        "\<And>i. e/(2 powr Suc i) > emeasure M (U i) - emeasure M (D i)"
        unfolding choice_iff by blast
      let ?U = "\<Union>i. U i"
      have "M ?U - M (\<Union>i. D i) = M (?U - (\<Union>i. D i))" using U  `(\<Union>i. D i) \<in> sets M`
        by (subst emeasure_Diff) (auto simp: sb)
      also have "\<dots> \<le> M (\<Union>i. U i - D i)" using U  `range D \<subseteq> sets M`
        by (intro emeasure_mono) (auto simp: sb intro!: sets.countable_nat_UN sets.Diff)
      also have "\<dots> \<le> (\<Sum>i. M (U i - D i))" using U  `range D \<subseteq> sets M`
        by (intro emeasure_subadditive_countably) (auto intro!: sets.Diff simp: sb)
      also have "\<dots> \<le> (\<Sum>i. ereal e/(2 powr Suc i))" using U `range D \<subseteq> sets M`
        by (intro suminf_le_pos, subst emeasure_Diff)
           (auto simp: emeasure_Diff emeasure_eq_measure sb measure_nonneg intro: less_imp_le)
      also have "\<dots> \<le> (\<Sum>n. ereal (e * (1 / 2) ^ Suc n))"
        by (simp add: powr_minus inverse_eq_divide powr_realpow field_simps power_divide)
      also have "\<dots> = (\<Sum>n. ereal e * ((1 / 2) ^  Suc n))"
        unfolding times_ereal.simps[symmetric] ereal_power[symmetric] one_ereal_def numeral_eq_ereal
        by simp
      also have "\<dots> = ereal e * (\<Sum>n. ((1 / 2) ^ Suc n))"
        by (rule suminf_cmult_ereal) (auto simp: `0 < e` less_imp_le)
      also have "\<dots> = e" unfolding suminf_half_series_ereal by simp
      finally
      have "emeasure M ?U \<le> emeasure M (\<Union>i. D i) + ereal e" by (simp add: emeasure_eq_measure)
      moreover
      have "(\<Union>i. D i) \<subseteq> ?U" using U by auto
      moreover
      have "open ?U" using U by auto
      ultimately
      have "(\<Union>i. D i) \<subseteq> ?U \<and> open ?U \<and> emeasure M ?U \<le> emeasure M (\<Union>i. D i) + ereal e" by simp
      thus "\<exists>B. (\<Union>i. D i) \<subseteq> B \<and> open B \<and> emeasure M B \<le> emeasure M (\<Union>i. D i) + ereal e" ..
    qed
  qed
qed

end


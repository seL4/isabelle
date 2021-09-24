(*  Title:      HOL/Probability/Projective_Limit.thy
    Author:     Fabian Immler, TU München
*)

section \<open>Projective Limit\<close>

theory Projective_Limit
imports
  Fin_Map
  Infinite_Product_Measure
  "HOL-Library.Diagonal_Subsequence"
begin

subsection \<open>Sequences of Finite Maps in Compact Sets\<close>

locale finmap_seqs_into_compact =
  fixes K::"nat \<Rightarrow> (nat \<Rightarrow>\<^sub>F 'a::metric_space) set" and f::"nat \<Rightarrow> (nat \<Rightarrow>\<^sub>F 'a)" and M
  assumes compact: "\<And>n. compact (K n)"
  assumes f_in_K: "\<And>n. K n \<noteq> {}"
  assumes domain_K: "\<And>n. k \<in> K n \<Longrightarrow> domain k = domain (f n)"
  assumes proj_in_K:
    "\<And>t n m. m \<ge> n \<Longrightarrow> t \<in> domain (f n) \<Longrightarrow> (f m)\<^sub>F t \<in> (\<lambda>k. (k)\<^sub>F t) ` K n"
begin

lemma proj_in_K': "(\<exists>n. \<forall>m \<ge> n. (f m)\<^sub>F t \<in> (\<lambda>k. (k)\<^sub>F t) ` K n)"
  using proj_in_K f_in_K
proof cases
  obtain k where "k \<in> K (Suc 0)" using f_in_K by auto
  assume "\<forall>n. t \<notin> domain (f n)"
  thus ?thesis
    by (auto intro!: exI[where x=1] image_eqI[OF _ \<open>k \<in> K (Suc 0)\<close>]
      simp: domain_K[OF \<open>k \<in> K (Suc 0)\<close>])
qed blast

lemma proj_in_KE:
  obtains n where "\<And>m. m \<ge> n \<Longrightarrow> (f m)\<^sub>F t \<in> (\<lambda>k. (k)\<^sub>F t) ` K n"
  using proj_in_K' by blast

lemma compact_projset:
  shows "compact ((\<lambda>k. (k)\<^sub>F i) ` K n)"
  using continuous_proj compact by (rule compact_continuous_image)

end

lemma compactE':
  fixes S :: "'a :: metric_space set"
  assumes "compact S" "\<forall>n\<ge>m. f n \<in> S"
  obtains l r where "l \<in> S" "strict_mono (r::nat\<Rightarrow>nat)" "((f \<circ> r) \<longlongrightarrow> l) sequentially"
proof atomize_elim
  have "strict_mono ((+) m)" by (simp add: strict_mono_def)
  have "\<forall>n. (f o (\<lambda>i. m + i)) n \<in> S" using assms by auto
  from seq_compactE[OF \<open>compact S\<close>[unfolded compact_eq_seq_compact_metric] this]
  obtain l r where "l \<in> S" "strict_mono r" "(f \<circ> (+) m \<circ> r) \<longlonglongrightarrow> l" by blast
  hence "l \<in> S" "strict_mono ((\<lambda>i. m + i) o r) \<and> (f \<circ> ((\<lambda>i. m + i) o r)) \<longlonglongrightarrow> l"
    using strict_mono_o[OF \<open>strict_mono ((+) m)\<close> \<open>strict_mono r\<close>] by (auto simp: o_def)
  thus "\<exists>l r. l \<in> S \<and> strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l" by blast
qed

sublocale finmap_seqs_into_compact \<subseteq> subseqs "\<lambda>n s. (\<exists>l. (\<lambda>i. ((f o s) i)\<^sub>F n) \<longlonglongrightarrow> l)"
proof
  fix n and s :: "nat \<Rightarrow> nat"
  assume "strict_mono s"
  from proj_in_KE[of n] obtain n0 where n0: "\<And>m. n0 \<le> m \<Longrightarrow> (f m)\<^sub>F n \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0"
    by blast
  have "\<forall>i \<ge> n0. ((f \<circ> s) i)\<^sub>F n \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0"
  proof safe
    fix i assume "n0 \<le> i"
    also have "\<dots> \<le> s i" by (rule seq_suble) fact
    finally have "n0 \<le> s i" .
    with n0 show "((f \<circ> s) i)\<^sub>F n \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0 "
      by auto
  qed
  then obtain ls rs
    where "ls \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0" "strict_mono rs" "((\<lambda>i. ((f \<circ> s) i)\<^sub>F n) \<circ> rs) \<longlonglongrightarrow> ls"
    by (rule compactE'[OF compact_projset])
  thus "\<exists>r'. strict_mono r' \<and> (\<exists>l. (\<lambda>i. ((f \<circ> (s \<circ> r')) i)\<^sub>F n) \<longlonglongrightarrow> l)" by (auto simp: o_def)
qed

lemma (in finmap_seqs_into_compact) diagonal_tendsto: "\<exists>l. (\<lambda>i. (f (diagseq i))\<^sub>F n) \<longlonglongrightarrow> l"
proof -
  obtain l where "(\<lambda>i. ((f o (diagseq o (+) (Suc n))) i)\<^sub>F n) \<longlonglongrightarrow> l"
  proof (atomize_elim, rule diagseq_holds)
    fix r s n
    assume "strict_mono (r :: nat \<Rightarrow> nat)"
    assume "\<exists>l. (\<lambda>i. ((f \<circ> s) i)\<^sub>F n) \<longlonglongrightarrow> l"
    then obtain l where "((\<lambda>i. (f i)\<^sub>F n) o s) \<longlonglongrightarrow> l"
      by (auto simp: o_def)
    hence "((\<lambda>i. (f i)\<^sub>F n) o s o r) \<longlonglongrightarrow> l" using \<open>strict_mono r\<close>
      by (rule LIMSEQ_subseq_LIMSEQ)
    thus "\<exists>l. (\<lambda>i. ((f \<circ> (s \<circ> r)) i)\<^sub>F n) \<longlonglongrightarrow> l" by (auto simp add: o_def)
  qed
  hence "(\<lambda>i. ((f (diagseq (i + Suc n))))\<^sub>F n) \<longlonglongrightarrow> l" by (simp add: ac_simps)
  hence "(\<lambda>i. (f (diagseq i))\<^sub>F n) \<longlonglongrightarrow> l" by (rule LIMSEQ_offset)
  thus ?thesis ..
qed

subsection \<open>Daniell-Kolmogorov Theorem\<close>

text \<open>Existence of Projective Limit\<close>

locale polish_projective = projective_family I P "\<lambda>_. borel::'a::polish_space measure"
  for I::"'i set" and P
begin

lemma emeasure_lim_emb:
  assumes X: "J \<subseteq> I" "finite J" "X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel)"
  shows "lim (emb I J X) = P J X"
proof (rule emeasure_lim)
  write mu_G ("\<mu>G")
  interpret generator: algebra "space (PiM I (\<lambda>i. borel))" generator
    by (rule algebra_generator)

  fix J and B :: "nat \<Rightarrow> ('i \<Rightarrow> 'a) set"
  assume J: "\<And>n. finite (J n)" "\<And>n. J n \<subseteq> I" "\<And>n. B n \<in> sets (\<Pi>\<^sub>M i\<in>J n. borel)" "incseq J"
    and B: "decseq (\<lambda>n. emb I (J n) (B n))"
    and "0 < (INF i. P (J i) (B i))" (is "0 < ?a")
  moreover have "?a \<le> 1"
    using J by (auto intro!: INF_lower2[of 0] prob_space_P[THEN prob_space.measure_le_1])
  ultimately obtain r where r: "?a = ennreal r" "0 < r" "r \<le> 1"
    by (cases "?a") (auto simp: top_unique)
  define Z where "Z n = emb I (J n) (B n)" for n
  have Z_mono: "n \<le> m \<Longrightarrow> Z m \<subseteq> Z n" for n m
    unfolding Z_def using B[THEN antimonoD, of n m] .
  have J_mono: "\<And>n m. n \<le> m \<Longrightarrow> J n \<subseteq> J m"
    using \<open>incseq J\<close> by (force simp: incseq_def)
  note [simp] = \<open>\<And>n. finite (J n)\<close>
  interpret prob_space "P (J i)" for i using J prob_space_P by simp

  have P_eq[simp]:
      "sets (P (J i)) = sets (\<Pi>\<^sub>M i\<in>J i. borel)" "space (P (J i)) = space (\<Pi>\<^sub>M i\<in>J i. borel)" for i
    using J by (auto simp: sets_P space_P)

  have "Z i \<in> generator" for i
    unfolding Z_def by (auto intro!: generator.intros J)

  have countable_UN_J: "countable (\<Union>n. J n)" by (simp add: countable_finite)
  define Utn where "Utn = to_nat_on (\<Union>n. J n)"
  interpret function_to_finmap "J n" Utn "from_nat_into (\<Union>n. J n)" for n
    by unfold_locales (auto simp: Utn_def intro: from_nat_into_to_nat_on[OF countable_UN_J])
  have inj_on_Utn: "inj_on Utn (\<Union>n. J n)"
    unfolding Utn_def using countable_UN_J by (rule inj_on_to_nat_on)
  hence inj_on_Utn_J: "\<And>n. inj_on Utn (J n)" by (rule subset_inj_on) auto
  define P' where "P' n = mapmeasure n (P (J n)) (\<lambda>_. borel)" for n
  interpret P': prob_space "P' n" for n
    unfolding P'_def mapmeasure_def using J
    by (auto intro!: prob_space_distr fm_measurable simp: measurable_cong_sets[OF sets_P])

  let ?SUP = "\<lambda>n. SUP K \<in> {K. K \<subseteq> fm n ` (B n) \<and> compact K}. emeasure (P' n) K"
  { fix n
    have "emeasure (P (J n)) (B n) = emeasure (P' n) (fm n ` (B n))"
      using J by (auto simp: P'_def mapmeasure_PiM space_P sets_P)
    also
    have "\<dots> = ?SUP n"
    proof (rule inner_regular)
      show "sets (P' n) = sets borel" by (simp add: borel_eq_PiF_borel P'_def)
    next
      show "fm n ` B n \<in> sets borel"
        unfolding borel_eq_PiF_borel by (auto simp: P'_def fm_image_measurable_finite sets_P J(3))
    qed simp
    finally have *: "emeasure (P (J n)) (B n) = ?SUP n" .
    have "?SUP n \<noteq> \<infinity>"
      unfolding *[symmetric] by simp
    note * this
  } note R = this
  have "\<forall>n. \<exists>K. emeasure (P (J n)) (B n) - emeasure (P' n) K \<le> 2 powr (-n) * ?a \<and> compact K \<and> K \<subseteq> fm n ` B n"
  proof
    fix n show "\<exists>K. emeasure (P (J n)) (B n) - emeasure (P' n) K \<le> ennreal (2 powr - real n) * ?a \<and>
        compact K \<and> K \<subseteq> fm n ` B n"
      unfolding R[of n]
    proof (rule ccontr)
      assume H: "\<nexists>K'. ?SUP n - emeasure (P' n) K' \<le> ennreal (2 powr - real n)  * ?a \<and>
        compact K' \<and> K' \<subseteq> fm n ` B n"
      have "?SUP n + 0 < ?SUP n + 2 powr (-n) * ?a"
        using R[of n] unfolding ennreal_add_left_cancel_less ennreal_zero_less_mult_iff
        by (auto intro: \<open>0 < ?a\<close>)
      also have "\<dots> = (SUP K\<in>{K. K \<subseteq> fm n ` B n \<and> compact K}. emeasure (P' n) K + 2 powr (-n) * ?a)"
        by (rule ennreal_SUP_add_left[symmetric]) auto
      also have "\<dots> \<le> ?SUP n"
      proof (intro SUP_least)
        fix K assume "K \<in> {K. K \<subseteq> fm n ` B n \<and> compact K}"
        with H have "2 powr (-n) * ?a < ?SUP n - emeasure (P' n) K"
          by auto
        then show "emeasure (P' n) K + (2 powr (-n)) * ?a \<le> ?SUP n"
          by (subst (asm) less_diff_eq_ennreal) (auto simp: less_top[symmetric] R(1)[symmetric] ac_simps)
      qed
      finally show False by simp
    qed
  qed
  then obtain K' where K':
    "\<And>n. emeasure (P (J n)) (B n) - emeasure (P' n) (K' n) \<le> ennreal (2 powr - real n) * ?a"
    "\<And>n. compact (K' n)" "\<And>n. K' n \<subseteq> fm n ` B n"
    unfolding choice_iff by blast
  define K where "K n = fm n -` K' n \<inter> space (Pi\<^sub>M (J n) (\<lambda>_. borel))" for n
  have K_sets: "\<And>n. K n \<in> sets (Pi\<^sub>M (J n) (\<lambda>_. borel))"
    unfolding K_def
    using compact_imp_closed[OF \<open>compact (K' _)\<close>]
    by (intro measurable_sets[OF fm_measurable, of _ "Collect finite"])
       (auto simp: borel_eq_PiF_borel[symmetric])
  have K_B: "\<And>n. K n \<subseteq> B n"
  proof
    fix x n assume "x \<in> K n"
    then have fm_in: "fm n x \<in> fm n ` B n"
      using K' by (force simp: K_def)
    show "x \<in> B n"
      using \<open>x \<in> K n\<close> K_sets sets.sets_into_space J(1,2,3)[of n] inj_on_image_mem_iff[OF inj_on_fm]
    by (metis (no_types) Int_iff K_def fm_in space_borel)
  qed
  define Z' where "Z' n = emb I (J n) (K n)" for n
  have Z': "\<And>n. Z' n \<subseteq> Z n"
    unfolding Z'_def Z_def
  proof (rule prod_emb_mono, safe)
    fix n x assume "x \<in> K n"
    hence "fm n x \<in> K' n" "x \<in> space (Pi\<^sub>M (J n) (\<lambda>_. borel))"
      by (simp_all add: K_def space_P)
    note this(1)
    also have "K' n \<subseteq> fm n ` B n" by (simp add: K')
    finally have "fm n x \<in> fm n ` B n" .
    thus "x \<in> B n"
    proof safe
      fix y assume y: "y \<in> B n"
      hence "y \<in> space (Pi\<^sub>M (J n) (\<lambda>_. borel))" using J sets.sets_into_space[of "B n" "P (J n)"]
        by (auto simp add: space_P sets_P)
      assume "fm n x = fm n y"
      note inj_onD[OF inj_on_fm[OF space_borel],
        OF \<open>fm n x = fm n y\<close> \<open>x \<in> space _\<close> \<open>y \<in> space _\<close>]
      with y show "x \<in> B n" by simp
    qed
  qed
  have "\<And>n. Z' n \<in> generator" using J K'(2) unfolding Z'_def
    by (auto intro!: generator.intros measurable_sets[OF fm_measurable[of _ "Collect finite"]]
             simp: K_def borel_eq_PiF_borel[symmetric] compact_imp_closed)
  define Y where "Y n = (\<Inter>i\<in>{1..n}. Z' i)" for n
  hence "\<And>n k. Y (n + k) \<subseteq> Y n" by (induct_tac k) (auto simp: Y_def)
  hence Y_mono: "\<And>n m. n \<le> m \<Longrightarrow> Y m \<subseteq> Y n" by (auto simp: le_iff_add)
  have Y_Z': "\<And>n. n \<ge> 1 \<Longrightarrow> Y n \<subseteq> Z' n" by (auto simp: Y_def)
  hence Y_Z: "\<And>n. n \<ge> 1 \<Longrightarrow> Y n \<subseteq> Z n" using Z' by auto

  have Y_notempty: "\<And>n. n \<ge> 1 \<Longrightarrow> (Y n) \<noteq> {}"
  proof -
    fix n::nat assume "n \<ge> 1" hence "Y n \<subseteq> Z n" by fact
    have "Y n = (\<Inter>i\<in>{1..n}. emb I (J n) (emb (J n) (J i) (K i)))" using J J_mono
      by (auto simp: Y_def Z'_def)
    also have "\<dots> = prod_emb I (\<lambda>_. borel) (J n) (\<Inter>i\<in>{1..n}. emb (J n) (J i) (K i))"
      using \<open>n \<ge> 1\<close>
      by (subst prod_emb_INT) auto
    finally
    have Y_emb:
      "Y n = prod_emb I (\<lambda>_. borel) (J n) (\<Inter>i\<in>{1..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i))" .
    hence "Y n \<in> generator" using J J_mono K_sets \<open>n \<ge> 1\<close>
      by (auto simp del: prod_emb_INT intro!: generator.intros)
    have *: "\<mu>G (Z n) = P (J n) (B n)"
      unfolding Z_def using J by (intro mu_G_spec) auto
    then have "\<mu>G (Z n) \<noteq> \<infinity>" by auto
    note *
    moreover have *: "\<mu>G (Y n) = P (J n) (\<Inter>i\<in>{Suc 0..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i))"
      unfolding Y_emb using J J_mono K_sets \<open>n \<ge> 1\<close> by (subst mu_G_spec) auto
    then have "\<mu>G (Y n) \<noteq> \<infinity>" by auto
    note *
    moreover have "\<mu>G (Z n - Y n) =
        P (J n) (B n - (\<Inter>i\<in>{Suc 0..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i)))"
      unfolding Z_def Y_emb prod_emb_Diff[symmetric] using J J_mono K_sets \<open>n \<ge> 1\<close>
      by (subst mu_G_spec) (auto intro!: sets.Diff)
    ultimately
    have "\<mu>G (Z n) - \<mu>G (Y n) = \<mu>G (Z n - Y n)"
      using J J_mono K_sets \<open>n \<ge> 1\<close>
      by (simp only: emeasure_eq_measure Z_def)
         (auto dest!: bspec[where x=n] intro!: measure_Diff[symmetric] subsetD[OF K_B]
               intro!: arg_cong[where f=ennreal]
               simp: extensional_restrict emeasure_eq_measure prod_emb_iff sets_P space_P
                     ennreal_minus measure_nonneg)
    also have subs: "Z n - Y n \<subseteq> (\<Union>i\<in>{1..n}. (Z i - Z' i))"
      using \<open>n \<ge> 1\<close> unfolding Y_def UN_extend_simps(7) by (intro UN_mono Diff_mono Z_mono order_refl) auto
    have "Z n - Y n \<in> generator" "(\<Union>i\<in>{1..n}. (Z i - Z' i)) \<in> generator"
      using \<open>Z' _ \<in> generator\<close> \<open>Z _ \<in> generator\<close> \<open>Y _ \<in> generator\<close> by auto
    hence "\<mu>G (Z n - Y n) \<le> \<mu>G (\<Union>i\<in>{1..n}. (Z i - Z' i))"
      using subs generator.additive_increasing[OF positive_mu_G additive_mu_G]
      unfolding increasing_def by auto
    also have "\<dots> \<le> (\<Sum> i\<in>{1..n}. \<mu>G (Z i - Z' i))" using \<open>Z _ \<in> generator\<close> \<open>Z' _ \<in> generator\<close>
      by (intro generator.subadditive[OF positive_mu_G additive_mu_G]) auto
    also have "\<dots> \<le> (\<Sum> i\<in>{1..n}. 2 powr -real i * ?a)"
    proof (rule sum_mono)
      fix i assume "i \<in> {1..n}" hence "i \<le> n" by simp
      have "\<mu>G (Z i - Z' i) = \<mu>G (prod_emb I (\<lambda>_. borel) (J i) (B i - K i))"
        unfolding Z'_def Z_def by simp
      also have "\<dots> = P (J i) (B i - K i)"
        using J K_sets by (subst mu_G_spec) auto
      also have "\<dots> = P (J i) (B i) - P (J i) (K i)"
        using K_sets J \<open>K _ \<subseteq> B _\<close> by (simp add: emeasure_Diff)
      also have "\<dots> = P (J i) (B i) - P' i (K' i)"
        unfolding K_def P'_def
        by (auto simp: mapmeasure_PiF borel_eq_PiF_borel[symmetric]
          compact_imp_closed[OF \<open>compact (K' _)\<close>] space_PiM PiE_def)
      also have "\<dots> \<le> ennreal (2 powr - real i) * ?a" using K'(1)[of i] .
      finally show "\<mu>G (Z i - Z' i) \<le> (2 powr - real i) * ?a" .
    qed
    also have "\<dots> = ennreal ((\<Sum> i\<in>{1..n}. (2 powr -enn2real i)) * enn2real ?a)"
      using r by (simp add: sum_distrib_right ennreal_mult[symmetric])
    also have "\<dots> < ennreal (1 * enn2real ?a)"
    proof (intro ennreal_lessI mult_strict_right_mono)
      have "(\<Sum>i = 1..n. 2 powr - real i) = (\<Sum>i = 1..<Suc n. (1/2) ^ i)"
        by (rule sum.cong) (auto simp: powr_realpow powr_divide power_divide powr_minus_divide)
      also have "{1..<Suc n} = {..<Suc n} - {0}" by auto
      also have "sum ((^) (1 / 2::real)) ({..<Suc n} - {0}) =
        sum ((^) (1 / 2)) ({..<Suc n}) - 1" by (auto simp: sum_diff1)
      also have "\<dots> < 1" by (subst geometric_sum) auto
      finally show "(\<Sum>i = 1..n. 2 powr - enn2real i) < 1" by simp
    qed (auto simp: r enn2real_positive_iff)
    also have "\<dots> = ?a" by (auto simp: r)
    also have "\<dots> \<le> \<mu>G (Z n)"
      using J by (auto intro: INF_lower simp: Z_def mu_G_spec)
    finally have "\<mu>G (Z n) - \<mu>G (Y n) < \<mu>G (Z n)" .
    hence R: "\<mu>G (Z n) < \<mu>G (Z n) + \<mu>G (Y n)"
      using \<open>\<mu>G (Y n) \<noteq> \<infinity>\<close> by (auto simp: zero_less_iff_neq_zero)
    then have "\<mu>G (Y n) > 0"
      by simp
    thus "Y n \<noteq> {}" using positive_mu_G by (auto simp add: positive_def)
  qed
  hence "\<forall>n\<in>{1..}. \<exists>y. y \<in> Y n" by auto
  then obtain y where y: "\<And>n. n \<ge> 1 \<Longrightarrow> y n \<in> Y n" unfolding bchoice_iff by force
  {
    fix t and n m::nat
    assume "1 \<le> n" "n \<le> m" hence "1 \<le> m" by simp
    from Y_mono[OF \<open>m \<ge> n\<close>] y[OF \<open>1 \<le> m\<close>] have "y m \<in> Y n" by auto
    also have "\<dots> \<subseteq> Z' n" using Y_Z'[OF \<open>1 \<le> n\<close>] .
    finally
    have "fm n (restrict (y m) (J n)) \<in> K' n"
      unfolding Z'_def K_def prod_emb_iff by (simp add: Z'_def K_def prod_emb_iff)
    moreover have "finmap_of (J n) (restrict (y m) (J n)) = finmap_of (J n) (y m)"
      using J by (simp add: fm_def)
    ultimately have "fm n (y m) \<in> K' n" by simp
  } note fm_in_K' = this
  interpret finmap_seqs_into_compact "\<lambda>n. K' (Suc n)" "\<lambda>k. fm (Suc k) (y (Suc k))" borel
  proof
    fix n show "compact (K' n)" by fact
  next
    fix n
    from Y_mono[of n "Suc n"] y[of "Suc n"] have "y (Suc n) \<in> Y (Suc n)" by auto
    also have "\<dots> \<subseteq> Z' (Suc n)" using Y_Z' by auto
    finally
    have "fm (Suc n) (restrict (y (Suc n)) (J (Suc n))) \<in> K' (Suc n)"
      unfolding Z'_def K_def prod_emb_iff by (simp add: Z'_def K_def prod_emb_iff)
    thus "K' (Suc n) \<noteq> {}" by auto
    fix k
    assume "k \<in> K' (Suc n)"
    with K'[of "Suc n"] sets.sets_into_space have "k \<in> fm (Suc n) ` B (Suc n)" by auto
    then obtain b where "k = fm (Suc n) b" by auto
    thus "domain k = domain (fm (Suc n) (y (Suc n)))"
      by (simp_all add: fm_def)
  next
    fix t and n m::nat
    assume "n \<le> m" hence "Suc n \<le> Suc m" by simp
    assume "t \<in> domain (fm (Suc n) (y (Suc n)))"
    then obtain j where j: "t = Utn j" "j \<in> J (Suc n)" by auto
    hence "j \<in> J (Suc m)" using J_mono[OF \<open>Suc n \<le> Suc m\<close>] by auto
    have img: "fm (Suc n) (y (Suc m)) \<in> K' (Suc n)" using \<open>n \<le> m\<close>
      by (intro fm_in_K') simp_all
    show "(fm (Suc m) (y (Suc m)))\<^sub>F t \<in> (\<lambda>k. (k)\<^sub>F t) ` K' (Suc n)"
      apply (rule image_eqI[OF _ img])
      using \<open>j \<in> J (Suc n)\<close> \<open>j \<in> J (Suc m)\<close>
      unfolding j by (subst proj_fm, auto)+
  qed
  have "\<forall>t. \<exists>z. (\<lambda>i. (fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) \<longlonglongrightarrow> z"
    using diagonal_tendsto ..
  then obtain z where z:
    "\<And>t. (\<lambda>i. (fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) \<longlonglongrightarrow> z t"
    unfolding choice_iff by blast
  {
    fix n :: nat assume "n \<ge> 1"
    have "\<And>i. domain (fm n (y (Suc (diagseq i)))) = domain (finmap_of (Utn ` J n) z)"
      by simp
    moreover
    {
      fix t
      assume t: "t \<in> domain (finmap_of (Utn ` J n) z)"
      hence "t \<in> Utn ` J n" by simp
      then obtain j where j: "t = Utn j" "j \<in> J n" by auto
      have "(\<lambda>i. (fm n (y (Suc (diagseq i))))\<^sub>F t) \<longlonglongrightarrow> z t"
        apply (subst (2) tendsto_iff, subst eventually_sequentially)
      proof safe
        fix e :: real assume "0 < e"
        { fix i and x :: "'i \<Rightarrow> 'a" assume i: "i \<ge> n"
          assume "t \<in> domain (fm n x)"
          hence "t \<in> domain (fm i x)" using J_mono[OF \<open>i \<ge> n\<close>] by auto
          with i have "(fm i x)\<^sub>F t = (fm n x)\<^sub>F t"
            using j by (auto simp: proj_fm dest!: inj_onD[OF inj_on_Utn])
        } note index_shift = this
        have I: "\<And>i. i \<ge> n \<Longrightarrow> Suc (diagseq i) \<ge> n"
          apply (rule le_SucI)
          apply (rule order_trans) apply simp
          apply (rule seq_suble[OF subseq_diagseq])
          done
        from z
        have "\<exists>N. \<forall>i\<ge>N. dist ((fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) (z t) < e"
          unfolding tendsto_iff eventually_sequentially using \<open>0 < e\<close> by auto
        then obtain N where N: "\<And>i. i \<ge> N \<Longrightarrow>
          dist ((fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) (z t) < e" by auto
        show "\<exists>N. \<forall>na\<ge>N. dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) < e "
        proof (rule exI[where x="max N n"], safe)
          fix na assume "max N n \<le> na"
          hence  "dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) =
                  dist ((fm (Suc (diagseq na)) (y (Suc (diagseq na))))\<^sub>F t) (z t)" using t
            by (subst index_shift[OF I]) auto
          also have "\<dots> < e" using \<open>max N n \<le> na\<close> by (intro N) simp
          finally show "dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) < e" .
        qed
      qed
      hence "(\<lambda>i. (fm n (y (Suc (diagseq i))))\<^sub>F t) \<longlonglongrightarrow> (finmap_of (Utn ` J n) z)\<^sub>F t"
        by (simp add: tendsto_intros)
    } ultimately
    have "(\<lambda>i. fm n (y (Suc (diagseq i)))) \<longlonglongrightarrow> finmap_of (Utn ` J n) z"
      by (rule tendsto_finmap)
    hence "((\<lambda>i. fm n (y (Suc (diagseq i)))) o (\<lambda>i. i + n)) \<longlonglongrightarrow> finmap_of (Utn ` J n) z"
      by (rule LIMSEQ_subseq_LIMSEQ) (simp add: strict_mono_def)
    moreover
    have "(\<forall>i. ((\<lambda>i. fm n (y (Suc (diagseq i)))) o (\<lambda>i. i + n)) i \<in> K' n)"
      apply (auto simp add: o_def intro!: fm_in_K' \<open>1 \<le> n\<close> le_SucI)
      apply (rule le_trans)
      apply (rule le_add2)
      using seq_suble[OF subseq_diagseq]
      apply auto
      done
    moreover
    from \<open>compact (K' n)\<close> have "closed (K' n)" by (rule compact_imp_closed)
    ultimately
    have "finmap_of (Utn ` J n) z \<in> K' n"
      unfolding closed_sequential_limits by blast
    also have "finmap_of (Utn ` J n) z  = fm n (\<lambda>i. z (Utn i))"
      unfolding finmap_eq_iff
    proof clarsimp
      fix i assume i: "i \<in> J n"
      hence "from_nat_into (\<Union>n. J n) (Utn i) = i"
        unfolding Utn_def
        by (subst from_nat_into_to_nat_on[OF countable_UN_J]) auto
      with i show "z (Utn i) = (fm n (\<lambda>i. z (Utn i)))\<^sub>F (Utn i)"
        by (simp add: finmap_eq_iff fm_def compose_def)
    qed
    finally have "fm n (\<lambda>i. z (Utn i)) \<in> K' n" .
    moreover
    let ?J = "\<Union>n. J n"
    have "(?J \<inter> J n) = J n" by auto
    ultimately have "restrict (\<lambda>i. z (Utn i)) (?J \<inter> J n) \<in> K n"
      unfolding K_def by (auto simp: space_P space_PiM)
    hence "restrict (\<lambda>i. z (Utn i)) ?J \<in> Z' n" unfolding Z'_def
      using J by (auto simp: prod_emb_def PiE_def extensional_def)
    also have "\<dots> \<subseteq> Z n" using Z' by simp
    finally have "restrict (\<lambda>i. z (Utn i)) ?J \<in> Z n" .
  } note in_Z = this
  hence "(\<Inter>i\<in>{1..}. Z i) \<noteq> {}" by auto
  thus "(\<Inter>i. Z i) \<noteq> {}"
    using INT_decseq_offset[OF antimonoI[OF Z_mono]] by simp
qed fact+

lemma measure_lim_emb:
  "J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel) \<Longrightarrow> measure lim (emb I J X) = measure (P J) X"
  unfolding measure_def by (subst emeasure_lim_emb) auto

end

hide_const (open) PiF
hide_const (open) Pi\<^sub>F
hide_const (open) Pi'
hide_const (open) finmap_of
hide_const (open) proj
hide_const (open) domain
hide_const (open) basis_finmap

sublocale polish_projective \<subseteq> P: prob_space lim
proof
  have *: "emb I {} {\<lambda>x. undefined} = space (\<Pi>\<^sub>M i\<in>I. borel)"
    by (auto simp: prod_emb_def space_PiM)
  interpret prob_space "P {}"
    using prob_space_P by simp
  show "emeasure lim (space lim) = 1"
    using emeasure_lim_emb[of "{}" "{\<lambda>x. undefined}"] emeasure_space_1
    by (simp add: * PiM_empty space_P)
qed

locale polish_product_prob_space =
  product_prob_space "\<lambda>_. borel::('a::polish_space) measure" I for I::"'i set"

sublocale polish_product_prob_space \<subseteq> P: polish_projective I "\<lambda>J. PiM J (\<lambda>_. borel::('a) measure)"
  ..

lemma (in polish_product_prob_space) limP_eq_PiM: "lim = PiM I (\<lambda>_. borel)"
  by (rule PiM_eq) (auto simp: emeasure_PiM emeasure_lim_emb)

end

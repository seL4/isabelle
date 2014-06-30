(*  Title:      HOL/Probability/Projective_Limit.thy
    Author:     Fabian Immler, TU München
*)

header {* Projective Limit *}

theory Projective_Limit
  imports
    Caratheodory
    Fin_Map
    Regularity
    Projective_Family
    Infinite_Product_Measure
    "~~/src/HOL/Library/Diagonal_Subsequence"
begin

subsection {* Sequences of Finite Maps in Compact Sets *}

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
    by (auto intro!: exI[where x=1] image_eqI[OF _ `k \<in> K (Suc 0)`]
      simp: domain_K[OF `k \<in> K (Suc 0)`])
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
  obtains l r where "l \<in> S" "subseq r" "((f \<circ> r) ---> l) sequentially"
proof atomize_elim
  have "subseq (op + m)" by (simp add: subseq_def)
  have "\<forall>n. (f o (\<lambda>i. m + i)) n \<in> S" using assms by auto
  from seq_compactE[OF `compact S`[unfolded compact_eq_seq_compact_metric] this] guess l r .
  hence "l \<in> S" "subseq ((\<lambda>i. m + i) o r) \<and> (f \<circ> ((\<lambda>i. m + i) o r)) ----> l"
    using subseq_o[OF `subseq (op + m)` `subseq r`] by (auto simp: o_def)
  thus "\<exists>l r. l \<in> S \<and> subseq r \<and> (f \<circ> r) ----> l" by blast
qed

sublocale finmap_seqs_into_compact \<subseteq> subseqs "\<lambda>n s. (\<exists>l. (\<lambda>i. ((f o s) i)\<^sub>F n) ----> l)"
proof
  fix n s
  assume "subseq s"
  from proj_in_KE[of n] guess n0 . note n0 = this
  have "\<forall>i \<ge> n0. ((f \<circ> s) i)\<^sub>F n \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0"
  proof safe
    fix i assume "n0 \<le> i"
    also have "\<dots> \<le> s i" by (rule seq_suble) fact
    finally have "n0 \<le> s i" .
    with n0 show "((f \<circ> s) i)\<^sub>F n \<in> (\<lambda>k. (k)\<^sub>F n) ` K n0 "
      by auto
  qed
  from compactE'[OF compact_projset this] guess ls rs .
  thus "\<exists>r'. subseq r' \<and> (\<exists>l. (\<lambda>i. ((f \<circ> (s \<circ> r')) i)\<^sub>F n) ----> l)" by (auto simp: o_def)
qed

lemma (in finmap_seqs_into_compact) diagonal_tendsto: "\<exists>l. (\<lambda>i. (f (diagseq i))\<^sub>F n) ----> l"
proof -
  obtain l where "(\<lambda>i. ((f o (diagseq o op + (Suc n))) i)\<^sub>F n) ----> l"
  proof (atomize_elim, rule diagseq_holds)
    fix r s n
    assume "subseq r"
    assume "\<exists>l. (\<lambda>i. ((f \<circ> s) i)\<^sub>F n) ----> l"
    then obtain l where "((\<lambda>i. (f i)\<^sub>F n) o s) ----> l"
      by (auto simp: o_def)
    hence "((\<lambda>i. (f i)\<^sub>F n) o s o r) ----> l" using `subseq r`
      by (rule LIMSEQ_subseq_LIMSEQ)
    thus "\<exists>l. (\<lambda>i. ((f \<circ> (s \<circ> r)) i)\<^sub>F n) ----> l" by (auto simp add: o_def)
  qed
  hence "(\<lambda>i. ((f (diagseq (i + Suc n))))\<^sub>F n) ----> l" by (simp add: ac_simps)
  hence "(\<lambda>i. (f (diagseq i))\<^sub>F n) ----> l" by (rule LIMSEQ_offset)
  thus ?thesis ..
qed

subsection {* Daniell-Kolmogorov Theorem *}

text {* Existence of Projective Limit *}

locale polish_projective = projective_family I P "\<lambda>_. borel::'a::polish_space measure"
  for I::"'i set" and P
begin

abbreviation "lim\<^sub>B \<equiv> (\<lambda>J P. limP J (\<lambda>_. borel) P)"

lemma emeasure_limB_emb_not_empty:
  assumes "I \<noteq> {}"
  assumes X: "J \<noteq> {}" "J \<subseteq> I" "finite J" "\<forall>i\<in>J. B i \<in> sets borel"
  shows "emeasure (lim\<^sub>B I P) (emb I J (Pi\<^sub>E J B)) = emeasure (lim\<^sub>B J P) (Pi\<^sub>E J B)"
proof -
  let ?\<Omega> = "\<Pi>\<^sub>E i\<in>I. space borel"
  let ?G = generator
  interpret G!: algebra ?\<Omega> generator by (intro  algebra_generator) fact
  note mu_G_mono =
    G.additive_increasing[OF positive_mu_G[OF `I \<noteq> {}`] additive_mu_G[OF `I \<noteq> {}`],
      THEN increasingD]
  write mu_G  ("\<mu>G")

  have "\<exists>\<mu>. (\<forall>s\<in>?G. \<mu> s = \<mu>G s) \<and> measure_space ?\<Omega> (sigma_sets ?\<Omega> ?G) \<mu>"
  proof (rule G.caratheodory_empty_continuous[OF positive_mu_G additive_mu_G,
      OF `I \<noteq> {}`, OF `I \<noteq> {}`])
    fix A assume "A \<in> ?G"
    with generatorE guess J X . note JX = this
    interpret prob_space "P J" using proj_prob_space[OF `finite J`] .
    show "\<mu>G A \<noteq> \<infinity>" using JX by (simp add: limP_finite)
  next
    fix Z assume Z: "range Z \<subseteq> ?G" "decseq Z" "(\<Inter>i. Z i) = {}"
    then have "decseq (\<lambda>i. \<mu>G (Z i))"
      by (auto intro!: mu_G_mono simp: decseq_def)
    moreover
    have "(INF i. \<mu>G (Z i)) = 0"
    proof (rule ccontr)
      assume "(INF i. \<mu>G (Z i)) \<noteq> 0" (is "?a \<noteq> 0")
      moreover have "0 \<le> ?a"
        using Z positive_mu_G[OF `I \<noteq> {}`] by (auto intro!: INF_greatest simp: positive_def)
      ultimately have "0 < ?a" by auto
      hence "?a \<noteq> -\<infinity>" by auto
      have "\<forall>n. \<exists>J B. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> B \<in> sets (Pi\<^sub>M J (\<lambda>_. borel)) \<and>
        Z n = emb I J B \<and> \<mu>G (Z n) = emeasure (lim\<^sub>B J P) B"
        using Z by (intro allI generator_Ex) auto
      then obtain J' B' where J': "\<And>n. J' n \<noteq> {}" "\<And>n. finite (J' n)" "\<And>n. J' n \<subseteq> I"
          "\<And>n. B' n \<in> sets (\<Pi>\<^sub>M i\<in>J' n. borel)"
        and Z_emb: "\<And>n. Z n = emb I (J' n) (B' n)"
        unfolding choice_iff by blast
      moreover def J \<equiv> "\<lambda>n. (\<Union>i\<le>n. J' i)"
      moreover def B \<equiv> "\<lambda>n. emb (J n) (J' n) (B' n)"
      ultimately have J: "\<And>n. J n \<noteq> {}" "\<And>n. finite (J n)" "\<And>n. J n \<subseteq> I"
        "\<And>n. B n \<in> sets (\<Pi>\<^sub>M i\<in>J n. borel)"
        by auto
      have J_mono: "\<And>n m. n \<le> m \<Longrightarrow> J n \<subseteq> J m"
        unfolding J_def by force
      have "\<forall>n. \<exists>j. j \<in> J n" using J by blast
      then obtain j where j: "\<And>n. j n \<in> J n"
        unfolding choice_iff by blast
      note [simp] = `\<And>n. finite (J n)`
      from J  Z_emb have Z_eq: "\<And>n. Z n = emb I (J n) (B n)" "\<And>n. Z n \<in> ?G"
        unfolding J_def B_def by (subst prod_emb_trans) (insert Z, auto)
      interpret prob_space "P (J i)" for i using proj_prob_space by simp
      have "?a \<le> \<mu>G (Z 0)" by (auto intro: INF_lower)
      also have "\<dots> < \<infinity>" using J by (auto simp: Z_eq mu_G_eq limP_finite proj_sets)
      finally have "?a \<noteq> \<infinity>" by simp
      have "\<And>n. \<bar>\<mu>G (Z n)\<bar> \<noteq> \<infinity>" unfolding Z_eq using J J_mono
        by (subst mu_G_eq) (auto simp: limP_finite proj_sets mu_G_eq)

      have countable_UN_J: "countable (\<Union>n. J n)" by (simp add: countable_finite)
      def Utn \<equiv> "to_nat_on (\<Union>n. J n)"
      interpret function_to_finmap "J n" Utn "from_nat_into (\<Union>n. J n)" for n
        by unfold_locales (auto simp: Utn_def intro: from_nat_into_to_nat_on[OF countable_UN_J])
      have inj_on_Utn: "inj_on Utn (\<Union>n. J n)"
        unfolding Utn_def using countable_UN_J by (rule inj_on_to_nat_on)
      hence inj_on_Utn_J: "\<And>n. inj_on Utn (J n)" by (rule subset_inj_on) auto
      def P' \<equiv> "\<lambda>n. mapmeasure n (P (J n)) (\<lambda>_. borel)"
      let ?SUP = "\<lambda>n. SUP K : {K. K \<subseteq> fm n ` (B n) \<and> compact K}. emeasure (P' n) K"
      {
        fix n
        interpret finite_measure "P (J n)" by unfold_locales
        have "emeasure (P (J n)) (B n) = emeasure (P' n) (fm n ` (B n))"
          using J by (auto simp: P'_def mapmeasure_PiM proj_space proj_sets)
        also
        have "\<dots> = ?SUP n"
        proof (rule inner_regular)
          show "emeasure (P' n) (space (P' n)) \<noteq> \<infinity>"
            unfolding P'_def
            by (auto simp: P'_def mapmeasure_PiF fm_measurable proj_space proj_sets)
          show "sets (P' n) = sets borel" by (simp add: borel_eq_PiF_borel P'_def)
        next
          show "fm n ` B n \<in> sets borel"
            unfolding borel_eq_PiF_borel
            by (auto simp del: J(2) simp: P'_def fm_image_measurable_finite proj_sets J)
        qed
        finally
        have "emeasure (P (J n)) (B n) = ?SUP n" "?SUP n \<noteq> \<infinity>" "?SUP n \<noteq> - \<infinity>" by auto
      } note R = this
      have "\<forall>n. \<exists>K. emeasure (P (J n)) (B n) - emeasure (P' n) K \<le> 2 powr (-n) * ?a
        \<and> compact K \<and> K \<subseteq> fm n ` B n"
      proof
        fix n
        have "emeasure (P' n) (space (P' n)) \<noteq> \<infinity>"
          by (simp add: mapmeasure_PiF P'_def proj_space proj_sets)
        then interpret finite_measure "P' n" ..
        show "\<exists>K. emeasure (P (J n)) (B n) - emeasure (P' n) K \<le> ereal (2 powr - real n) * ?a \<and>
            compact K \<and> K \<subseteq> fm n ` B n"
          unfolding R
        proof (rule ccontr)
          assume H: "\<not> (\<exists>K'. ?SUP n - emeasure (P' n) K' \<le> ereal (2 powr - real n)  * ?a \<and>
            compact K' \<and> K' \<subseteq> fm n ` B n)"
          have "?SUP n \<le> ?SUP n - 2 powr (-n) * ?a"
          proof (intro SUP_least)
            fix K
            assume "K \<in> {K. K \<subseteq> fm n ` B n \<and> compact K}"
            with H have "\<not> ?SUP n - emeasure (P' n) K \<le> 2 powr (-n) * ?a"
              by auto
            hence "?SUP n - emeasure (P' n) K > 2 powr (-n) * ?a"
              unfolding not_less[symmetric] by simp
            hence "?SUP n - 2 powr (-n) * ?a > emeasure (P' n) K"
              using `0 < ?a` by (auto simp add: ereal_less_minus_iff ac_simps)
            thus "?SUP n - 2 powr (-n) * ?a \<ge> emeasure (P' n) K" by simp
          qed
          hence "?SUP n + 0 \<le> ?SUP n - (2 powr (-n) * ?a)" using `0 < ?a` by simp
          hence "?SUP n + 0 \<le> ?SUP n + - (2 powr (-n) * ?a)" unfolding minus_ereal_def .
          hence "0 \<le> - (2 powr (-n) * ?a)"
            using `?SUP _ \<noteq> \<infinity>` `?SUP _ \<noteq> - \<infinity>`
            by (subst (asm) ereal_add_le_add_iff) (auto simp:)
          moreover have "ereal (2 powr - real n) * ?a > 0" using `0 < ?a`
            by (auto simp: ereal_zero_less_0_iff)
          ultimately show False by simp
        qed
      qed
      then obtain K' where K':
        "\<And>n. emeasure (P (J n)) (B n) - emeasure (P' n) (K' n) \<le> ereal (2 powr - real n) * ?a"
        "\<And>n. compact (K' n)" "\<And>n. K' n \<subseteq> fm n ` B n"
        unfolding choice_iff by blast
      def K \<equiv> "\<lambda>n. fm n -` K' n \<inter> space (Pi\<^sub>M (J n) (\<lambda>_. borel))"
      have K_sets: "\<And>n. K n \<in> sets (Pi\<^sub>M (J n) (\<lambda>_. borel))"
        unfolding K_def
        using compact_imp_closed[OF `compact (K' _)`]
        by (intro measurable_sets[OF fm_measurable, of _ "Collect finite"])
           (auto simp: borel_eq_PiF_borel[symmetric])
      have K_B: "\<And>n. K n \<subseteq> B n"
      proof
        fix x n
        assume "x \<in> K n" hence fm_in: "fm n x \<in> fm n ` B n"
          using K' by (force simp: K_def)
        show "x \<in> B n"
          using `x \<in> K n` K_sets sets.sets_into_space J[of n]
          by (intro inj_on_image_mem_iff[OF inj_on_fm _ fm_in, of "\<lambda>_. borel"]) auto
      qed
      def Z' \<equiv> "\<lambda>n. emb I (J n) (K n)"
      have Z': "\<And>n. Z' n \<subseteq> Z n"
        unfolding Z_eq unfolding Z'_def
      proof (rule prod_emb_mono, safe)
        fix n x assume "x \<in> K n"
        hence "fm n x \<in> K' n" "x \<in> space (Pi\<^sub>M (J n) (\<lambda>_. borel))"
          by (simp_all add: K_def proj_space)
        note this(1)
        also have "K' n \<subseteq> fm n ` B n" by (simp add: K')
        finally have "fm n x \<in> fm n ` B n" .
        thus "x \<in> B n"
        proof safe
          fix y assume y: "y \<in> B n"
          hence "y \<in> space (Pi\<^sub>M (J n) (\<lambda>_. borel))" using J sets.sets_into_space[of "B n" "P (J n)"]
            by (auto simp add: proj_space proj_sets)
          assume "fm n x = fm n y"
          note inj_onD[OF inj_on_fm[OF space_borel],
            OF `fm n x = fm n y` `x \<in> space _` `y \<in> space _`]
          with y show "x \<in> B n" by simp
        qed
      qed
      { fix n
        have "Z' n \<in> ?G" using K' unfolding Z'_def
          apply (intro generatorI'[OF J(1-3)])
          unfolding K_def proj_space
          apply (rule measurable_sets[OF fm_measurable[of _ "Collect finite"]])
          apply (auto simp add: P'_def borel_eq_PiF_borel[symmetric] compact_imp_closed)
          done
      }
      def Y \<equiv> "\<lambda>n. \<Inter>i\<in>{1..n}. Z' i"
      hence "\<And>n k. Y (n + k) \<subseteq> Y n" by (induct_tac k) (auto simp: Y_def)
      hence Y_mono: "\<And>n m. n \<le> m \<Longrightarrow> Y m \<subseteq> Y n" by (auto simp: le_iff_add)
      have Y_Z': "\<And>n. n \<ge> 1 \<Longrightarrow> Y n \<subseteq> Z' n" by (auto simp: Y_def)
      hence Y_Z: "\<And>n. n \<ge> 1 \<Longrightarrow> Y n \<subseteq> Z n" using Z' by auto
      have Y_notempty: "\<And>n. n \<ge> 1 \<Longrightarrow> (Y n) \<noteq> {}"
      proof -
        fix n::nat assume "n \<ge> 1" hence "Y n \<subseteq> Z n" by fact
        have "Y n = (\<Inter> i\<in>{1..n}. emb I (J n) (emb (J n) (J i) (K i)))" using J J_mono
          by (auto simp: Y_def Z'_def)
        also have "\<dots> = prod_emb I (\<lambda>_. borel) (J n) (\<Inter> i\<in>{1..n}. emb (J n) (J i) (K i))"
          using `n \<ge> 1`
          by (subst prod_emb_INT) auto
        finally
        have Y_emb:
          "Y n = prod_emb I (\<lambda>_. borel) (J n)
            (\<Inter> i\<in>{1..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i))" .
        hence "Y n \<in> ?G" using J J_mono K_sets `n \<ge> 1` by (intro generatorI[OF _ _ _ _ Y_emb]) auto
        hence "\<bar>\<mu>G (Y n)\<bar> \<noteq> \<infinity>" unfolding Y_emb using J J_mono K_sets `n \<ge> 1`
          by (subst mu_G_eq) (auto simp: limP_finite proj_sets mu_G_eq)
        interpret finite_measure "(limP (J n) (\<lambda>_. borel) P)"
        proof
          have "emeasure (limP (J n) (\<lambda>_. borel) P) (J n \<rightarrow>\<^sub>E space borel) \<noteq> \<infinity>"
            using J by (subst emeasure_limP) auto
          thus  "emeasure (limP (J n) (\<lambda>_. borel) P) (space (limP (J n) (\<lambda>_. borel) P)) \<noteq> \<infinity>"
             by (simp add: space_PiM)
        qed
        have "\<mu>G (Z n) = limP (J n) (\<lambda>_. borel) P (B n)"
          unfolding Z_eq using J by (auto simp: mu_G_eq)
        moreover have "\<mu>G (Y n) =
          limP (J n) (\<lambda>_. borel) P (\<Inter>i\<in>{Suc 0..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i))"
          unfolding Y_emb using J J_mono K_sets `n \<ge> 1` by (subst mu_G_eq) auto
        moreover have "\<mu>G (Z n - Y n) = limP (J n) (\<lambda>_. borel) P
          (B n - (\<Inter>i\<in>{Suc 0..n}. prod_emb (J n) (\<lambda>_. borel) (J i) (K i)))"
          unfolding Z_eq Y_emb prod_emb_Diff[symmetric] using J J_mono K_sets `n \<ge> 1`
          by (subst mu_G_eq) (auto intro!: sets.Diff)
        ultimately
        have "\<mu>G (Z n) - \<mu>G (Y n) = \<mu>G (Z n - Y n)"
          using J J_mono K_sets `n \<ge> 1`
          by (simp only: emeasure_eq_measure)
            (auto dest!: bspec[where x=n]
            simp: extensional_restrict emeasure_eq_measure prod_emb_iff simp del: limP_finite
            intro!: measure_Diff[symmetric] set_mp[OF K_B])
        also have subs: "Z n - Y n \<subseteq> (\<Union> i\<in>{1..n}. (Z i - Z' i))" using Z' Z `n \<ge> 1`
          unfolding Y_def by (force simp: decseq_def)
        have "Z n - Y n \<in> ?G" "(\<Union> i\<in>{1..n}. (Z i - Z' i)) \<in> ?G"
          using `Z' _ \<in> ?G` `Z _ \<in> ?G` `Y _ \<in> ?G` by auto
        hence "\<mu>G (Z n - Y n) \<le> \<mu>G (\<Union> i\<in>{1..n}. (Z i - Z' i))"
          using subs G.additive_increasing[OF positive_mu_G[OF `I \<noteq> {}`] additive_mu_G[OF `I \<noteq> {}`]]
          unfolding increasing_def by auto
        also have "\<dots> \<le> (\<Sum> i\<in>{1..n}. \<mu>G (Z i - Z' i))" using `Z _ \<in> ?G` `Z' _ \<in> ?G`
          by (intro G.subadditive[OF positive_mu_G additive_mu_G, OF `I \<noteq> {}` `I \<noteq> {}`]) auto
        also have "\<dots> \<le> (\<Sum> i\<in>{1..n}. 2 powr -real i * ?a)"
        proof (rule setsum_mono)
          fix i assume "i \<in> {1..n}" hence "i \<le> n" by simp
          have "\<mu>G (Z i - Z' i) = \<mu>G (prod_emb I (\<lambda>_. borel) (J i) (B i - K i))"
            unfolding Z'_def Z_eq by simp
          also have "\<dots> = P (J i) (B i - K i)"
            using J K_sets by (subst mu_G_eq) auto
          also have "\<dots> = P (J i) (B i) - P (J i) (K i)"
            apply (subst emeasure_Diff) using K_sets J `K _ \<subseteq> B _` apply (auto simp: proj_sets)
            done
          also have "\<dots> = P (J i) (B i) - P' i (K' i)"
            unfolding K_def P'_def
            by (auto simp: mapmeasure_PiF proj_space proj_sets borel_eq_PiF_borel[symmetric]
              compact_imp_closed[OF `compact (K' _)`] space_PiM PiE_def)
          also have "\<dots> \<le> ereal (2 powr - real i) * ?a" using K'(1)[of i] .
          finally show "\<mu>G (Z i - Z' i) \<le> (2 powr - real i) * ?a" .
        qed
        also have "\<dots> = (\<Sum> i\<in>{1..n}. ereal (2 powr -real i) * ereal(real ?a))"
          using `?a \<noteq> \<infinity>` `?a \<noteq> - \<infinity>` by (subst ereal_real') auto
        also have "\<dots> = ereal (\<Sum> i\<in>{1..n}. (2 powr -real i) * (real ?a))" by simp
        also have "\<dots> = ereal ((\<Sum> i\<in>{1..n}. (2 powr -real i)) * real ?a)"
          by (simp add: setsum_left_distrib)
        also have "\<dots> < ereal (1 * real ?a)" unfolding less_ereal.simps
        proof (rule mult_strict_right_mono)
          have "(\<Sum>i\<in>{1..n}. 2 powr - real i) = (\<Sum>i\<in>{1..<Suc n}. (1/2) ^ i)"
            by (rule setsum.cong)
               (auto simp: powr_realpow[symmetric] powr_minus powr_divide inverse_eq_divide)
          also have "{1..<Suc n} = {..<Suc n} - {0}" by auto
          also have "setsum (op ^ (1 / 2::real)) ({..<Suc n} - {0}) =
            setsum (op ^ (1 / 2)) ({..<Suc n}) - 1" by (auto simp: setsum_diff1)
          also have "\<dots> < 1" by (subst geometric_sum) auto
          finally show "(\<Sum>i = 1..n. 2 powr - real i) < 1" .
        qed (auto simp:
          `0 < ?a` `?a \<noteq> \<infinity>` `?a \<noteq> - \<infinity>` ereal_less_real_iff zero_ereal_def[symmetric])
        also have "\<dots> = ?a" using `0 < ?a` `?a \<noteq> \<infinity>` by (auto simp: ereal_real')
        also have "\<dots> \<le> \<mu>G (Z n)" by (auto intro: INF_lower)
        finally have "\<mu>G (Z n) - \<mu>G (Y n) < \<mu>G (Z n)" .
        hence R: "\<mu>G (Z n) < \<mu>G (Z n) + \<mu>G (Y n)"
          using `\<bar>\<mu>G (Y n)\<bar> \<noteq> \<infinity>` by (simp add: ereal_minus_less)
        have "0 \<le> (- \<mu>G (Z n)) + \<mu>G (Z n)" using `\<bar>\<mu>G (Z n)\<bar> \<noteq> \<infinity>` by auto
        also have "\<dots> < (- \<mu>G (Z n)) + (\<mu>G (Z n) + \<mu>G (Y n))"
          apply (rule ereal_less_add[OF _ R]) using `\<bar>\<mu>G (Z n)\<bar> \<noteq> \<infinity>` by auto
        finally have "\<mu>G (Y n) > 0"
          using `\<bar>\<mu>G (Z n)\<bar> \<noteq> \<infinity>` by (auto simp: ac_simps zero_ereal_def[symmetric])
        thus "Y n \<noteq> {}" using positive_mu_G `I \<noteq> {}` by (auto simp add: positive_def)
      qed
      hence "\<forall>n\<in>{1..}. \<exists>y. y \<in> Y n" by auto
      then obtain y where y: "\<And>n. n \<ge> 1 \<Longrightarrow> y n \<in> Y n" unfolding bchoice_iff by force
      {
        fix t and n m::nat
        assume "1 \<le> n" "n \<le> m" hence "1 \<le> m" by simp
        from Y_mono[OF `m \<ge> n`] y[OF `1 \<le> m`] have "y m \<in> Y n" by auto
        also have "\<dots> \<subseteq> Z' n" using Y_Z'[OF `1 \<le> n`] .
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
        hence "j \<in> J (Suc m)" using J_mono[OF `Suc n \<le> Suc m`] by auto
        have img: "fm (Suc n) (y (Suc m)) \<in> K' (Suc n)" using `n \<le> m`
          by (intro fm_in_K') simp_all
        show "(fm (Suc m) (y (Suc m)))\<^sub>F t \<in> (\<lambda>k. (k)\<^sub>F t) ` K' (Suc n)"
          apply (rule image_eqI[OF _ img])
          using `j \<in> J (Suc n)` `j \<in> J (Suc m)`
          unfolding j by (subst proj_fm, auto)+
      qed
      have "\<forall>t. \<exists>z. (\<lambda>i. (fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) ----> z"
        using diagonal_tendsto ..
      then obtain z where z:
        "\<And>t. (\<lambda>i. (fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) ----> z t"
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
          have "(\<lambda>i. (fm n (y (Suc (diagseq i))))\<^sub>F t) ----> z t"
            apply (subst (2) tendsto_iff, subst eventually_sequentially)
          proof safe
            fix e :: real assume "0 < e"
            { fix i x
              assume i: "i \<ge> n"
              assume "t \<in> domain (fm n x)"
              hence "t \<in> domain (fm i x)" using J_mono[OF `i \<ge> n`] by auto
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
              unfolding tendsto_iff eventually_sequentially using `0 < e` by auto
            then obtain N where N: "\<And>i. i \<ge> N \<Longrightarrow>
              dist ((fm (Suc (diagseq i)) (y (Suc (diagseq i))))\<^sub>F t) (z t) < e" by auto
            show "\<exists>N. \<forall>na\<ge>N. dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) < e "
            proof (rule exI[where x="max N n"], safe)
              fix na assume "max N n \<le> na"
              hence  "dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) =
                      dist ((fm (Suc (diagseq na)) (y (Suc (diagseq na))))\<^sub>F t) (z t)" using t
                by (subst index_shift[OF I]) auto
              also have "\<dots> < e" using `max N n \<le> na` by (intro N) simp
              finally show "dist ((fm n (y (Suc (diagseq na))))\<^sub>F t) (z t) < e" .
            qed
          qed
          hence "(\<lambda>i. (fm n (y (Suc (diagseq i))))\<^sub>F t) ----> (finmap_of (Utn ` J n) z)\<^sub>F t"
            by (simp add: tendsto_intros)
        } ultimately
        have "(\<lambda>i. fm n (y (Suc (diagseq i)))) ----> finmap_of (Utn ` J n) z"
          by (rule tendsto_finmap)
        hence "((\<lambda>i. fm n (y (Suc (diagseq i)))) o (\<lambda>i. i + n)) ----> finmap_of (Utn ` J n) z"
          by (intro lim_subseq) (simp add: subseq_def)
        moreover
        have "(\<forall>i. ((\<lambda>i. fm n (y (Suc (diagseq i)))) o (\<lambda>i. i + n)) i \<in> K' n)"
          apply (auto simp add: o_def intro!: fm_in_K' `1 \<le> n` le_SucI)
          apply (rule le_trans)
          apply (rule le_add2)
          using seq_suble[OF subseq_diagseq]
          apply auto
          done
        moreover
        from `compact (K' n)` have "closed (K' n)" by (rule compact_imp_closed)
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
          unfolding K_def by (auto simp: proj_space space_PiM)
        hence "restrict (\<lambda>i. z (Utn i)) ?J \<in> Z' n" unfolding Z'_def
          using J by (auto simp: prod_emb_def PiE_def extensional_def)
        also have "\<dots> \<subseteq> Z n" using Z' by simp
        finally have "restrict (\<lambda>i. z (Utn i)) ?J \<in> Z n" .
      } note in_Z = this
      hence "(\<Inter>i\<in>{1..}. Z i) \<noteq> {}" by auto
      hence "(\<Inter>i. Z i) \<noteq> {}" using Z INT_decseq_offset[OF `decseq Z`] by simp
      thus False using Z by simp
    qed
    ultimately show "(\<lambda>i. \<mu>G (Z i)) ----> 0"
      using LIMSEQ_INF[of "\<lambda>i. \<mu>G (Z i)"] by simp
  qed
  then guess \<mu> .. note \<mu> = this
  def f \<equiv> "finmap_of J B"
  show "emeasure (lim\<^sub>B I P) (emb I J (Pi\<^sub>E J B)) = emeasure (lim\<^sub>B J P) (Pi\<^sub>E J B)"
  proof (subst emeasure_extend_measure_Pair[OF limP_def, of I "\<lambda>_. borel" \<mu>])
    show "positive (sets (lim\<^sub>B I P)) \<mu>" "countably_additive (sets (lim\<^sub>B I P)) \<mu>"
      using \<mu> unfolding sets_limP sets_PiM_generator by (auto simp: measure_space_def)
  next
    show "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> B \<in> J \<rightarrow> sets borel"
      using assms by (auto simp: f_def)
  next
    fix J and X::"'i \<Rightarrow> 'a set"
    show "prod_emb I (\<lambda>_. borel) J (Pi\<^sub>E J X) \<in> Pow (I \<rightarrow>\<^sub>E space borel)"
      by (auto simp: prod_emb_def)
    assume JX: "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> J \<rightarrow> sets borel"
    hence "emb I J (Pi\<^sub>E J X) \<in> generator" using assms
      by (intro generatorI[where J=J and X="Pi\<^sub>E J X"]) (auto intro: sets_PiM_I_finite)
    hence "\<mu> (emb I J (Pi\<^sub>E J X)) = \<mu>G (emb I J (Pi\<^sub>E J X))" using \<mu> by simp
    also have "\<dots> = emeasure (P J) (Pi\<^sub>E J X)"
      using JX assms proj_sets
      by (subst mu_G_eq) (auto simp: mu_G_eq limP_finite intro: sets_PiM_I_finite)
    finally show "\<mu> (emb I J (Pi\<^sub>E J X)) = emeasure (P J) (Pi\<^sub>E J X)" .
  next
    show "emeasure (P J) (Pi\<^sub>E J B) = emeasure (limP J (\<lambda>_. borel) P) (Pi\<^sub>E J B)"
      using assms by (simp add: f_def limP_finite Pi_def)
  qed
qed

end

hide_const (open) PiF
hide_const (open) Pi\<^sub>F
hide_const (open) Pi'
hide_const (open) Abs_finmap
hide_const (open) Rep_finmap
hide_const (open) finmap_of
hide_const (open) proj
hide_const (open) domain
hide_const (open) basis_finmap

sublocale polish_projective \<subseteq> P!: prob_space "(lim\<^sub>B I P)"
proof
  show "emeasure (lim\<^sub>B I P) (space (lim\<^sub>B I P)) = 1"
  proof cases
    assume "I = {}"
    interpret prob_space "P {}" using proj_prob_space by simp
    show ?thesis
      by (simp add: space_PiM_empty limP_finite emeasure_space_1 `I = {}`)
  next
    assume "I \<noteq> {}"
    then obtain i where "i \<in> I" by auto
    interpret prob_space "P {i}" using proj_prob_space by simp
    have R: "(space (lim\<^sub>B I P)) = (emb I {i} (Pi\<^sub>E {i} (\<lambda>_. space borel)))"
      by (auto simp: prod_emb_def space_PiM)
    moreover have "extensional {i} = space (P {i})" by (simp add: proj_space space_PiM PiE_def)
    ultimately show ?thesis using `i \<in> I`
      apply (subst R)
      apply (subst emeasure_limB_emb_not_empty)
      apply (auto simp: limP_finite emeasure_space_1 PiE_def)
      done
  qed
qed

context polish_projective begin

lemma emeasure_limB_emb:
  assumes X: "J \<subseteq> I" "finite J" "\<forall>i\<in>J. B i \<in> sets borel"
  shows "emeasure (lim\<^sub>B I P) (emb I J (Pi\<^sub>E J B)) = emeasure (P J) (Pi\<^sub>E J B)"
proof cases
  interpret prob_space "P {}" using proj_prob_space by simp
  assume "J = {}"
  moreover have "emb I {} {\<lambda>x. undefined} = space (lim\<^sub>B I P)"
    by (auto simp: space_PiM prod_emb_def)
  moreover have "{\<lambda>x. undefined} = space (lim\<^sub>B {} P)"
    by (auto simp: space_PiM prod_emb_def simp del: limP_finite)
  ultimately show ?thesis
    by (simp add: P.emeasure_space_1 limP_finite emeasure_space_1 del: space_limP)
next
  assume "J \<noteq> {}" with X show ?thesis
    by (subst emeasure_limB_emb_not_empty) (auto simp: limP_finite)
qed

lemma measure_limB_emb:
  assumes "J \<subseteq> I" "finite J" "\<forall>i\<in>J. B i \<in> sets borel"
  shows "measure (lim\<^sub>B I P) (emb I J (Pi\<^sub>E J B)) = measure (P J) (Pi\<^sub>E J B)"
proof -
  interpret prob_space "P J" using proj_prob_space assms by simp
  show ?thesis
    using emeasure_limB_emb[OF assms]
    unfolding emeasure_eq_measure limP_finite[OF `finite J` `J \<subseteq> I`] P.emeasure_eq_measure
    by simp
qed

end

locale polish_product_prob_space =
  product_prob_space "\<lambda>_. borel::('a::polish_space) measure" I for I::"'i set"

sublocale polish_product_prob_space \<subseteq> P: polish_projective I "\<lambda>J. PiM J (\<lambda>_. borel::('a) measure)"
proof qed

lemma (in polish_product_prob_space) limP_eq_PiM:
  "I \<noteq> {} \<Longrightarrow> lim\<^sub>P I (\<lambda>_. borel) (\<lambda>J. PiM J (\<lambda>_. borel::('a) measure)) =
    PiM I (\<lambda>_. borel)"
  by (rule PiM_eq) (auto simp: emeasure_PiM emeasure_limB_emb)

end

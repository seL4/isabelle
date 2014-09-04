(*  Title:      HOL/Probability/Infinite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Infinite Product Measure*}

theory Infinite_Product_Measure
  imports Probability_Measure Caratheodory Projective_Family
begin

lemma (in product_prob_space) emeasure_PiM_emb_not_empty:
  assumes X: "J \<noteq> {}" "J \<subseteq> I" "finite J" "\<forall>i\<in>J. X i \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) (emb I J (Pi\<^sub>E J X)) = emeasure (Pi\<^sub>M J M) (Pi\<^sub>E J X)"
proof cases
  assume "finite I" with X show ?thesis by simp
next
  let ?\<Omega> = "\<Pi>\<^sub>E i\<in>I. space (M i)"
  let ?G = generator
  assume "\<not> finite I"
  then have I_not_empty: "I \<noteq> {}" by auto
  interpret G!: algebra ?\<Omega> generator by (rule algebra_generator) fact
  note mu_G_mono =
    G.additive_increasing[OF positive_mu_G[OF I_not_empty] additive_mu_G[OF I_not_empty],
      THEN increasingD]
  write mu_G  ("\<mu>G")

  { fix Z J assume J: "J \<noteq> {}" "finite J" "J \<subseteq> I" and Z: "Z \<in> ?G"

    from `infinite I` `finite J` obtain k where k: "k \<in> I" "k \<notin> J"
      by (metis rev_finite_subset subsetI)
    moreover from Z guess K' X' by (rule generatorE)
    moreover def K \<equiv> "insert k K'"
    moreover def X \<equiv> "emb K K' X'"
    ultimately have K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "X \<in> sets (Pi\<^sub>M K M)" "Z = emb I K X"
      "K - J \<noteq> {}" "K - J \<subseteq> I" "\<mu>G Z = emeasure (Pi\<^sub>M K M) X"
      by (auto simp: subset_insertI)
    let ?M = "\<lambda>y. (\<lambda>x. merge J (K - J) (y, x)) -` emb (J \<union> K) K X \<inter> space (Pi\<^sub>M (K - J) M)"
    { fix y assume y: "y \<in> space (Pi\<^sub>M J M)"
      note * = merge_emb[OF `K \<subseteq> I` `J \<subseteq> I` y, of X]
      moreover
      have **: "?M y \<in> sets (Pi\<^sub>M (K - J) M)"
        using J K y by (intro merge_sets) auto
      ultimately
      have ***: "((\<lambda>x. merge J (I - J) (y, x)) -` Z \<inter> space (Pi\<^sub>M I M)) \<in> ?G"
        using J K by (intro generatorI) auto
      have "\<mu>G ((\<lambda>x. merge J (I - J) (y, x)) -` emb I K X \<inter> space (Pi\<^sub>M I M)) = emeasure (Pi\<^sub>M (K - J) M) (?M y)"
        unfolding * using K J by (subst mu_G_eq[OF _ _ _ **]) auto
      note * ** *** this }
    note merge_in_G = this

    have "finite (K - J)" using K by auto

    interpret J: finite_product_prob_space M J by default fact+
    interpret KmJ: finite_product_prob_space M "K - J" by default fact+

    have "\<mu>G Z = emeasure (Pi\<^sub>M (J \<union> (K - J)) M) (emb (J \<union> (K - J)) K X)"
      using K J by simp
    also have "\<dots> = (\<integral>\<^sup>+ x. emeasure (Pi\<^sub>M (K - J) M) (?M x) \<partial>Pi\<^sub>M J M)"
      using K J by (subst emeasure_fold_integral) auto
    also have "\<dots> = (\<integral>\<^sup>+ y. \<mu>G ((\<lambda>x. merge J (I - J) (y, x)) -` Z \<inter> space (Pi\<^sub>M I M)) \<partial>Pi\<^sub>M J M)"
      (is "_ = (\<integral>\<^sup>+x. \<mu>G (?MZ x) \<partial>Pi\<^sub>M J M)")
    proof (intro nn_integral_cong)
      fix x assume x: "x \<in> space (Pi\<^sub>M J M)"
      with K merge_in_G(2)[OF this]
      show "emeasure (Pi\<^sub>M (K - J) M) (?M x) = \<mu>G (?MZ x)"
        unfolding `Z = emb I K X` merge_in_G(1)[OF x] by (subst mu_G_eq) auto
    qed
    finally have fold: "\<mu>G Z = (\<integral>\<^sup>+x. \<mu>G (?MZ x) \<partial>Pi\<^sub>M J M)" .

    { fix x assume x: "x \<in> space (Pi\<^sub>M J M)"
      then have "\<mu>G (?MZ x) \<le> 1"
        unfolding merge_in_G(4)[OF x] `Z = emb I K X`
        by (intro KmJ.measure_le_1 merge_in_G(2)[OF x]) }
    note le_1 = this

    let ?q = "\<lambda>y. \<mu>G ((\<lambda>x. merge J (I - J) (y,x)) -` Z \<inter> space (Pi\<^sub>M I M))"
    have "?q \<in> borel_measurable (Pi\<^sub>M J M)"
      unfolding `Z = emb I K X` using J K merge_in_G(3)
      by (simp add: merge_in_G  mu_G_eq emeasure_fold_measurable cong: measurable_cong)
    note this fold le_1 merge_in_G(3) }
  note fold = this

  have "\<exists>\<mu>. (\<forall>s\<in>?G. \<mu> s = \<mu>G s) \<and> measure_space ?\<Omega> (sigma_sets ?\<Omega> ?G) \<mu>"
  proof (rule G.caratheodory_empty_continuous[OF positive_mu_G additive_mu_G])
    fix A assume "A \<in> ?G"
    with generatorE guess J X . note JX = this
    interpret JK: finite_product_prob_space M J by default fact+ 
    from JX show "\<mu>G A \<noteq> \<infinity>" by simp
  next
    fix A assume A: "range A \<subseteq> ?G" "decseq A" "(\<Inter>i. A i) = {}"
    then have "decseq (\<lambda>i. \<mu>G (A i))"
      by (auto intro!: mu_G_mono simp: decseq_def)
    moreover
    have "(INF i. \<mu>G (A i)) = 0"
    proof (rule ccontr)
      assume "(INF i. \<mu>G (A i)) \<noteq> 0" (is "?a \<noteq> 0")
      moreover have "0 \<le> ?a"
        using A positive_mu_G[OF I_not_empty] by (auto intro!: INF_greatest simp: positive_def)
      ultimately have "0 < ?a" by auto

      have "\<forall>n. \<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^sub>M J M) \<and> A n = emb I J X \<and> \<mu>G (A n) = emeasure (limP J M (\<lambda>J. (Pi\<^sub>M J M))) X"
        using A by (intro allI generator_Ex) auto
      then obtain J' X' where J': "\<And>n. J' n \<noteq> {}" "\<And>n. finite (J' n)" "\<And>n. J' n \<subseteq> I" "\<And>n. X' n \<in> sets (Pi\<^sub>M (J' n) M)"
        and A': "\<And>n. A n = emb I (J' n) (X' n)"
        unfolding choice_iff by blast
      moreover def J \<equiv> "\<lambda>n. (\<Union>i\<le>n. J' i)"
      moreover def X \<equiv> "\<lambda>n. emb (J n) (J' n) (X' n)"
      ultimately have J: "\<And>n. J n \<noteq> {}" "\<And>n. finite (J n)" "\<And>n. J n \<subseteq> I" "\<And>n. X n \<in> sets (Pi\<^sub>M (J n) M)"
        by auto
      with A' have A_eq: "\<And>n. A n = emb I (J n) (X n)" "\<And>n. A n \<in> ?G"
        unfolding J_def X_def by (subst prod_emb_trans) (insert A, auto)

      have J_mono: "\<And>n m. n \<le> m \<Longrightarrow> J n \<subseteq> J m"
        unfolding J_def by force

      interpret J: finite_product_prob_space M "J i" for i by default fact+

      have a_le_1: "?a \<le> 1"
        using mu_G_spec[of "J 0" "A 0" "X 0"] J A_eq
        by (auto intro!: INF_lower2[of 0] J.measure_le_1)

      let ?M = "\<lambda>K Z y. (\<lambda>x. merge K (I - K) (y, x)) -` Z \<inter> space (Pi\<^sub>M I M)"

      { fix Z k assume Z: "range Z \<subseteq> ?G" "decseq Z" "\<forall>n. ?a / 2^k \<le> \<mu>G (Z n)"
        then have Z_sets: "\<And>n. Z n \<in> ?G" by auto
        fix J' assume J': "J' \<noteq> {}" "finite J'" "J' \<subseteq> I"
        interpret J': finite_product_prob_space M J' by default fact+

        let ?q = "\<lambda>n y. \<mu>G (?M J' (Z n) y)"
        let ?Q = "\<lambda>n. ?q n -` {?a / 2^(k+1) ..} \<inter> space (Pi\<^sub>M J' M)"
        { fix n
          have "?q n \<in> borel_measurable (Pi\<^sub>M J' M)"
            using Z J' by (intro fold(1)) auto
          then have "?Q n \<in> sets (Pi\<^sub>M J' M)"
            by (rule measurable_sets) auto }
        note Q_sets = this

        have "?a / 2^(k+1) \<le> (INF n. emeasure (Pi\<^sub>M J' M) (?Q n))"
        proof (intro INF_greatest)
          fix n
          have "?a / 2^k \<le> \<mu>G (Z n)" using Z by auto
          also have "\<dots> \<le> (\<integral>\<^sup>+ x. indicator (?Q n) x + ?a / 2^(k+1) \<partial>Pi\<^sub>M J' M)"
            unfolding fold(2)[OF J' `Z n \<in> ?G`]
          proof (intro nn_integral_mono)
            fix x assume x: "x \<in> space (Pi\<^sub>M J' M)"
            then have "?q n x \<le> 1 + 0"
              using J' Z fold(3) Z_sets by auto
            also have "\<dots> \<le> 1 + ?a / 2^(k+1)"
              using `0 < ?a` by (intro add_mono) auto
            finally have "?q n x \<le> 1 + ?a / 2^(k+1)" .
            with x show "?q n x \<le> indicator (?Q n) x + ?a / 2^(k+1)"
              by (auto split: split_indicator simp del: power_Suc)
          qed
          also have "\<dots> = emeasure (Pi\<^sub>M J' M) (?Q n) + ?a / 2^(k+1)"
            using `0 \<le> ?a` Q_sets J'.emeasure_space_1
            by (subst nn_integral_add) auto
          finally show "?a / 2^(k+1) \<le> emeasure (Pi\<^sub>M J' M) (?Q n)" using `?a \<le> 1`
            by (cases rule: ereal2_cases[of ?a "emeasure (Pi\<^sub>M J' M) (?Q n)"])
               (auto simp: field_simps)
        qed
        also have "\<dots> = emeasure (Pi\<^sub>M J' M) (\<Inter>n. ?Q n)"
        proof (intro INF_emeasure_decseq)
          show "range ?Q \<subseteq> sets (Pi\<^sub>M J' M)" using Q_sets by auto
          show "decseq ?Q"
            unfolding decseq_def
          proof (safe intro!: vimageI[OF refl])
            fix m n :: nat assume "m \<le> n"
            fix x assume x: "x \<in> space (Pi\<^sub>M J' M)"
            assume "?a / 2^(k+1) \<le> ?q n x"
            also have "?q n x \<le> ?q m x"
            proof (rule mu_G_mono)
              from fold(4)[OF J', OF Z_sets x]
              show "?M J' (Z n) x \<in> ?G" "?M J' (Z m) x \<in> ?G" by auto
              show "?M J' (Z n) x \<subseteq> ?M J' (Z m) x"
                using `decseq Z`[THEN decseqD, OF `m \<le> n`] by auto
            qed
            finally show "?a / 2^(k+1) \<le> ?q m x" .
          qed
        qed simp
        finally have "(\<Inter>n. ?Q n) \<noteq> {}"
          using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then have "\<exists>w\<in>space (Pi\<^sub>M J' M). \<forall>n. ?a / 2 ^ (k + 1) \<le> ?q n w" by auto }
      note Ex_w = this

      let ?q = "\<lambda>k n y. \<mu>G (?M (J k) (A n) y)"

      let ?P = "\<lambda>w k. w \<in> space (Pi\<^sub>M (J k) M) \<and> (\<forall>n. ?a / 2 ^ (Suc k) \<le> ?q k n w)"
      have "\<exists>w. \<forall>k. ?P (w k) k \<and> restrict (w (Suc k)) (J k) = w k"
      proof (rule dependent_nat_choice)
        have "\<forall>n. ?a / 2 ^ 0 \<le> \<mu>G (A n)" by (auto intro: INF_lower)
        from Ex_w[OF A(1,2) this J(1-3), of 0] show "\<exists>w. ?P w 0" by auto
      next
        fix w k assume Suc: "?P w k"
        show "\<exists>w'. ?P w' (Suc k) \<and> restrict w' (J k) = w"
        proof cases
          assume [simp]: "J k = J (Suc k)"
          have "?a / 2 ^ (Suc (Suc k)) \<le> ?a / 2 ^ (k + 1)"
            using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: field_simps)
          with Suc show ?thesis
            by (auto intro!: exI[of _ w] simp: extensional_restrict space_PiM intro: order_trans)
        next
          assume "J k \<noteq> J (Suc k)"
          with J_mono[of k "Suc k"] have "J (Suc k) - J k \<noteq> {}" (is "?D \<noteq> {}") by auto
          have "range (\<lambda>n. ?M (J k) (A n) w) \<subseteq> ?G" "decseq (\<lambda>n. ?M (J k) (A n) w)"
            "\<forall>n. ?a / 2 ^ (k + 1) \<le> \<mu>G (?M (J k) (A n) w)"
            using `decseq A` fold(4)[OF J(1-3) A_eq(2), of w k] Suc
            by (auto simp: decseq_def)
          from Ex_w[OF this `?D \<noteq> {}`] J[of "Suc k"]
          obtain w' where w': "w' \<in> space (Pi\<^sub>M ?D M)"
            "\<forall>n. ?a / 2 ^ (Suc k + 1) \<le> \<mu>G (?M ?D (?M (J k) (A n) w) w')" by auto
          let ?w = "merge (J k) ?D (w, w')"
          have [simp]: "\<And>x. merge (J k) (I - J k) (w, merge ?D (I - ?D) (w', x)) =
            merge (J (Suc k)) (I - (J (Suc k))) (?w, x)"
            using J(3)[of "Suc k"] J(3)[of k] J_mono[of k "Suc k"]
            by (auto intro!: ext split: split_merge)
          have *: "\<And>n. ?M ?D (?M (J k) (A n) w) w' = ?M (J (Suc k)) (A n) ?w"
            using w'(1) J(3)[of "Suc k"]
            by (auto simp: space_PiM split: split_merge intro!: extensional_merge_sub) force+
          show ?thesis
            using Suc w' J_mono[of k "Suc k"] unfolding *
            by (intro exI[of _ ?w])
               (auto split: split_merge intro!: extensional_merge_sub ext simp: space_PiM PiE_iff)
        qed
      qed
      then obtain w where w:
        "\<And>k. w k \<in> space (Pi\<^sub>M (J k) M)"
        "\<And>k n. ?a / 2 ^ (Suc k) \<le> ?q k n (w k)"
        "\<And>k. restrict (w (Suc k)) (J k) = w k"
        by metis

      { fix k
        from w have "?a / 2 ^ (k + 1) \<le> ?q k k (w k)" by auto
        then have "?M (J k) (A k) (w k) \<noteq> {}"
          using positive_mu_G[OF I_not_empty, unfolded positive_def] `0 < ?a` `?a \<le> 1`
          by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then obtain x where "x \<in> ?M (J k) (A k) (w k)" by auto
        then have "merge (J k) (I - J k) (w k, x) \<in> A k" by auto
        then have "\<exists>x\<in>A k. restrict x (J k) = w k"
          using `w k \<in> space (Pi\<^sub>M (J k) M)`
          by (intro rev_bexI) (auto intro!: ext simp: extensional_def space_PiM) }
      note w_ext = this

      { fix k l i assume "k \<le> l" "i \<in> J k"
        { fix l have "w k i = w (k + l) i"
          proof (induct l)
            case (Suc l)
            from `i \<in> J k` J_mono[of k "k + l"] have "i \<in> J (k + l)" by auto
            with w(3)[of "k + l"]
            have "w (k + l) i = w (k + Suc l) i"
              by (auto simp: restrict_def fun_eq_iff split: split_if_asm)
            with Suc show ?case by simp
          qed simp }
        from this[of "l - k"] `k \<le> l` have "w l i = w k i" by simp }
      note w_mono = this

      def w' \<equiv> "\<lambda>i. if i \<in> (\<Union>k. J k) then w (LEAST k. i \<in> J k) i else if i \<in> I then (SOME x. x \<in> space (M i)) else undefined"
      { fix i k assume k: "i \<in> J k"
        have "w k i = w (LEAST k. i \<in> J k) i"
          by (intro w_mono Least_le k LeastI[of _ k])
        then have "w' i = w k i"
          unfolding w'_def using k by auto }
      note w'_eq = this
      have w'_simps1: "\<And>i. i \<notin> I \<Longrightarrow> w' i = undefined"
        using J by (auto simp: w'_def)
      have w'_simps2: "\<And>i. i \<notin> (\<Union>k. J k) \<Longrightarrow> i \<in> I \<Longrightarrow> w' i \<in> space (M i)"
        using J by (auto simp: w'_def intro!: someI_ex[OF M.not_empty[unfolded ex_in_conv[symmetric]]])
      { fix i assume "i \<in> I" then have "w' i \<in> space (M i)"
          using w(1) by (cases "i \<in> (\<Union>k. J k)") (force simp: w'_simps2 w'_eq space_PiM)+ }
      note w'_simps[simp] = w'_eq w'_simps1 w'_simps2 this

      have w': "w' \<in> space (Pi\<^sub>M I M)"
        using w(1) by (auto simp add: Pi_iff extensional_def space_PiM)

      { fix n
        have "restrict w' (J n) = w n" using w(1)[of n]
          by (auto simp add: fun_eq_iff space_PiM)
        with w_ext[of n] obtain x where "x \<in> A n" "restrict x (J n) = restrict w' (J n)"
          by auto
        then have "w' \<in> A n" unfolding A_eq using w' by (auto simp: prod_emb_def space_PiM) }
      then have "w' \<in> (\<Inter>i. A i)" by auto
      with `(\<Inter>i. A i) = {}` show False by auto
    qed
    ultimately show "(\<lambda>i. \<mu>G (A i)) ----> 0"
      using LIMSEQ_INF[of "\<lambda>i. \<mu>G (A i)"] by simp
  qed fact+
  then guess \<mu> .. note \<mu> = this
  show ?thesis
  proof (subst emeasure_extend_measure_Pair[OF PiM_def, of I M \<mu> J X])
    from assms show "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))"
      by (simp add: Pi_iff)
  next
    fix J X assume J: "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))"
    then show "emb I J (Pi\<^sub>E J X) \<in> Pow (\<Pi>\<^sub>E i\<in>I. space (M i))"
      by (auto simp: Pi_iff prod_emb_def dest: sets.sets_into_space)
    have "emb I J (Pi\<^sub>E J X) \<in> generator"
      using J `I \<noteq> {}` by (intro generatorI') (auto simp: Pi_iff)
    then have "\<mu> (emb I J (Pi\<^sub>E J X)) = \<mu>G (emb I J (Pi\<^sub>E J X))"
      using \<mu> by simp
    also have "\<dots> = (\<Prod> j\<in>J. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"
      using J  `I \<noteq> {}` by (subst mu_G_spec[OF _ _ _ refl]) (auto simp: emeasure_PiM Pi_iff)
    also have "\<dots> = (\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}.
      if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"
      using J `I \<noteq> {}` by (intro setprod.mono_neutral_right) (auto simp: M.emeasure_space_1)
    finally show "\<mu> (emb I J (Pi\<^sub>E J X)) = \<dots>" .
  next
    let ?F = "\<lambda>j. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j))"
    have "(\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}. ?F j) = (\<Prod>j\<in>J. ?F j)"
      using X `I \<noteq> {}` by (intro setprod.mono_neutral_right) (auto simp: M.emeasure_space_1)
    then show "(\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}. ?F j) =
      emeasure (Pi\<^sub>M J M) (Pi\<^sub>E J X)"
      using X by (auto simp add: emeasure_PiM) 
  next
    show "positive (sets (Pi\<^sub>M I M)) \<mu>" "countably_additive (sets (Pi\<^sub>M I M)) \<mu>"
      using \<mu> unfolding sets_PiM_generator by (auto simp: measure_space_def)
  qed
qed

sublocale product_prob_space \<subseteq> P: prob_space "Pi\<^sub>M I M"
proof
  show "emeasure (Pi\<^sub>M I M) (space (Pi\<^sub>M I M)) = 1"
  proof cases
    assume "I = {}" then show ?thesis by (simp add: space_PiM_empty)
  next
    assume "I \<noteq> {}"
    then obtain i where i: "i \<in> I" by auto
    then have "emb I {i} (\<Pi>\<^sub>E i\<in>{i}. space (M i)) = (space (Pi\<^sub>M I M))"
      by (auto simp: prod_emb_def space_PiM)
    with i show ?thesis
      using emeasure_PiM_emb_not_empty[of "{i}" "\<lambda>i. space (M i)"]
      by (simp add: emeasure_PiM emeasure_space_1)
  qed
qed

lemma (in product_prob_space) emeasure_PiM_emb:
  assumes X: "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod> i\<in>J. emeasure (M i) (X i))"
proof cases
  assume "J = {}"
  moreover have "emb I {} {\<lambda>x. undefined} = space (Pi\<^sub>M I M)"
    by (auto simp: space_PiM prod_emb_def)
  ultimately show ?thesis
    by (simp add: space_PiM_empty P.emeasure_space_1)
next
  assume "J \<noteq> {}" with X show ?thesis
    by (subst emeasure_PiM_emb_not_empty) (auto simp: emeasure_PiM)
qed

lemma (in product_prob_space) emeasure_PiM_Collect:
  assumes X: "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) {x\<in>space (Pi\<^sub>M I M). \<forall>i\<in>J. x i \<in> X i} = (\<Prod> i\<in>J. emeasure (M i) (X i))"
proof -
  have "{x\<in>space (Pi\<^sub>M I M). \<forall>i\<in>J. x i \<in> X i} = emb I J (Pi\<^sub>E J X)"
    unfolding prod_emb_def using assms by (auto simp: space_PiM Pi_iff)
  with emeasure_PiM_emb[OF assms] show ?thesis by simp
qed

lemma (in product_prob_space) emeasure_PiM_Collect_single:
  assumes X: "i \<in> I" "A \<in> sets (M i)"
  shows "emeasure (Pi\<^sub>M I M) {x\<in>space (Pi\<^sub>M I M). x i \<in> A} = emeasure (M i) A"
  using emeasure_PiM_Collect[of "{i}" "\<lambda>i. A"] assms
  by simp

lemma (in product_prob_space) measure_PiM_emb:
  assumes "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "measure (PiM I M) (emb I J (Pi\<^sub>E J X)) = (\<Prod> i\<in>J. measure (M i) (X i))"
  using emeasure_PiM_emb[OF assms]
  unfolding emeasure_eq_measure M.emeasure_eq_measure by (simp add: setprod_ereal)

lemma sets_Collect_single':
  "i \<in> I \<Longrightarrow> {x\<in>space (M i). P x} \<in> sets (M i) \<Longrightarrow> {x\<in>space (PiM I M). P (x i)} \<in> sets (PiM I M)"
  using sets_Collect_single[of i I "{x\<in>space (M i). P x}" M]
  by (simp add: space_PiM PiE_iff cong: conj_cong)

lemma (in finite_product_prob_space) finite_measure_PiM_emb:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> measure (PiM I M) (Pi\<^sub>E I A) = (\<Prod>i\<in>I. measure (M i) (A i))"
  using measure_PiM_emb[of I A] finite_index prod_emb_PiE_same_index[OF sets.sets_into_space, of I A M]
  by auto

lemma (in product_prob_space) PiM_component:
  assumes "i \<in> I"
  shows "distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i) = M i"
proof (rule measure_eqI[symmetric])
  fix A assume "A \<in> sets (M i)"
  moreover have "((\<lambda>\<omega>. \<omega> i) -` A \<inter> space (PiM I M)) = {x\<in>space (PiM I M). x i \<in> A}"
    by auto
  ultimately show "emeasure (M i) A = emeasure (distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i)) A"
    by (auto simp: `i\<in>I` emeasure_distr measurable_component_singleton emeasure_PiM_Collect_single)
qed simp

lemma (in product_prob_space) PiM_eq:
  assumes "I \<noteq> {}"
  assumes "sets M' = sets (PiM I M)"
  assumes eq: "\<And>J F. finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>j. j \<in> J \<Longrightarrow> F j \<in> sets (M j)) \<Longrightarrow>
    emeasure M' (prod_emb I M J (\<Pi>\<^sub>E j\<in>J. F j)) = (\<Prod>j\<in>J. emeasure (M j) (F j))"
  shows "M' = (PiM I M)"
proof (rule measure_eqI_generator_eq[symmetric, OF Int_stable_prod_algebra prod_algebra_sets_into_space])
  show "sets (PiM I M) = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) (prod_algebra I M)"
    by (rule sets_PiM)
  then show "sets M' = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) (prod_algebra I M)"
    unfolding `sets M' = sets (PiM I M)` by simp

  def i \<equiv> "SOME i. i \<in> I"
  with `I \<noteq> {}` have i: "i \<in> I"
    by (auto intro: someI_ex)

  def A \<equiv> "\<lambda>n::nat. prod_emb I M {i} (\<Pi>\<^sub>E j\<in>{i}. space (M i))"
  then show "range A \<subseteq> prod_algebra I M"
    by (auto intro!: prod_algebraI i)

  have A_eq: "\<And>i. A i = space (PiM I M)"
    by (auto simp: prod_emb_def space_PiM Pi_iff A_def i)
  show "(\<Union>i. A i) = (\<Pi>\<^sub>E i\<in>I. space (M i))"
    unfolding A_eq by (auto simp: space_PiM)
  show "\<And>i. emeasure (PiM I M) (A i) \<noteq> \<infinity>"
    unfolding A_eq P.emeasure_space_1 by simp
next
  fix X assume X: "X \<in> prod_algebra I M"
  then obtain J E where X: "X = prod_emb I M J (PIE j:J. E j)"
    and J: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets (M j)"
    by (force elim!: prod_algebraE)
  from eq[OF J] have "emeasure M' X = (\<Prod>j\<in>J. emeasure (M j) (E j))"
    by (simp add: X)
  also have "\<dots> = emeasure (PiM I M) X"
    unfolding X using J by (intro emeasure_PiM_emb[symmetric]) auto
  finally show "emeasure (PiM I M) X = emeasure M' X" ..
qed

subsection {* Sequence space *}

definition comb_seq :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "comb_seq i \<omega> \<omega>' j = (if j < i then \<omega> j else \<omega>' (j - i))"

lemma split_comb_seq: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> (j < i \<longrightarrow> P (\<omega> j)) \<and> (\<forall>k. j = i + k \<longrightarrow> P (\<omega>' k))"
  by (auto simp: comb_seq_def not_less)

lemma split_comb_seq_asm: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> \<not> ((j < i \<and> \<not> P (\<omega> j)) \<or> (\<exists>k. j = i + k \<and> \<not> P (\<omega>' k)))"
  by (auto simp: comb_seq_def)

lemma measurable_comb_seq:
  "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> measurable ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)) (\<Pi>\<^sub>M i\<in>UNIV. M)"
proof (rule measurable_PiM_single)
  show "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)) \<rightarrow> (UNIV \<rightarrow>\<^sub>E space M)"
    by (auto simp: space_pair_measure space_PiM PiE_iff split: split_comb_seq)
  fix j :: nat and A assume A: "A \<in> sets M"
  then have *: "{\<omega> \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)). case_prod (comb_seq i) \<omega> j \<in> A} =
    (if j < i then {\<omega> \<in> space (\<Pi>\<^sub>M i\<in>UNIV. M). \<omega> j \<in> A} \<times> space (\<Pi>\<^sub>M i\<in>UNIV. M)
              else space (\<Pi>\<^sub>M i\<in>UNIV. M) \<times> {\<omega> \<in> space (\<Pi>\<^sub>M i\<in>UNIV. M). \<omega> (j - i) \<in> A})"
    by (auto simp: space_PiM space_pair_measure comb_seq_def dest: sets.sets_into_space)
  show "{\<omega> \<in> space ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M)). case_prod (comb_seq i) \<omega> j \<in> A} \<in> sets ((\<Pi>\<^sub>M i\<in>UNIV. M) \<Otimes>\<^sub>M (\<Pi>\<^sub>M i\<in>UNIV. M))"
    unfolding * by (auto simp: A intro!: sets_Collect_single)
qed

lemma measurable_comb_seq'[measurable (raw)]:
  assumes f: "f \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)" and g: "g \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  shows "(\<lambda>x. comb_seq i (f x) (g x)) \<in> measurable N (\<Pi>\<^sub>M i\<in>UNIV. M)"
  using measurable_compose[OF measurable_Pair[OF f g] measurable_comb_seq] by simp

lemma comb_seq_0: "comb_seq 0 \<omega> \<omega>' = \<omega>'"
  by (auto simp add: comb_seq_def)

lemma comb_seq_Suc: "comb_seq (Suc n) \<omega> \<omega>' = comb_seq n \<omega> (case_nat (\<omega> n) \<omega>')"
  by (auto simp add: comb_seq_def not_less less_Suc_eq le_imp_diff_is_add intro!: ext split: nat.split)

lemma comb_seq_Suc_0[simp]: "comb_seq (Suc 0) \<omega> = case_nat (\<omega> 0)"
  by (intro ext) (simp add: comb_seq_Suc comb_seq_0)

lemma comb_seq_less: "i < n \<Longrightarrow> comb_seq n \<omega> \<omega>' i = \<omega> i"
  by (auto split: split_comb_seq)

lemma comb_seq_add: "comb_seq n \<omega> \<omega>' (i + n) = \<omega>' i"
  by (auto split: nat.split split_comb_seq)

lemma case_nat_comb_seq: "case_nat s' (comb_seq n \<omega> \<omega>') (i + n) = case_nat (case_nat s' \<omega> n) \<omega>' i"
  by (auto split: nat.split split_comb_seq)

lemma case_nat_comb_seq':
  "case_nat s (comb_seq i \<omega> \<omega>') = comb_seq (Suc i) (case_nat s \<omega>) \<omega>'"
  by (auto split: split_comb_seq nat.split)

locale sequence_space = product_prob_space "\<lambda>i. M" "UNIV :: nat set" for M
begin

abbreviation "S \<equiv> \<Pi>\<^sub>M i\<in>UNIV::nat set. M"

lemma infprod_in_sets[intro]:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "Pi UNIV E \<in> sets S"
proof -
  have "Pi UNIV E = (\<Inter>i. emb UNIV {..i} (\<Pi>\<^sub>E j\<in>{..i}. E j))"
    using E E[THEN sets.sets_into_space]
    by (auto simp: prod_emb_def Pi_iff extensional_def) blast
  with E show ?thesis by auto
qed

lemma measure_PiM_countable:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "(\<lambda>n. \<Prod>i\<le>n. measure M (E i)) ----> measure S (Pi UNIV E)"
proof -
  let ?E = "\<lambda>n. emb UNIV {..n} (Pi\<^sub>E {.. n} E)"
  have "\<And>n. (\<Prod>i\<le>n. measure M (E i)) = measure S (?E n)"
    using E by (simp add: measure_PiM_emb)
  moreover have "Pi UNIV E = (\<Inter>n. ?E n)"
    using E E[THEN sets.sets_into_space]
    by (auto simp: prod_emb_def extensional_def Pi_iff) blast
  moreover have "range ?E \<subseteq> sets S"
    using E by auto
  moreover have "decseq ?E"
    by (auto simp: prod_emb_def Pi_iff decseq_def)
  ultimately show ?thesis
    by (simp add: finite_Lim_measure_decseq)
qed

lemma nat_eq_diff_eq: 
  fixes a b c :: nat
  shows "c \<le> b \<Longrightarrow> a = b - c \<longleftrightarrow> a + c = b"
  by auto

lemma PiM_comb_seq:
  "distr (S \<Otimes>\<^sub>M S) S (\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (\<Pi>\<^sub>E j\<in>J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets.sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (S \<Otimes>\<^sub>M S) =
    (prod_emb ?I ?M (J \<inter> {..<i}) (PIE j:J \<inter> {..<i}. E j)) \<times>
    (prod_emb ?I ?M ((op + i) -` J) (PIE j:(op + i) -` J. E (i + j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM prod_emb_def all_conj_distrib PiE_iff
               split: split_comb_seq split_comb_seq_asm)
  then have "emeasure ?D ?X = emeasure (S \<Otimes>\<^sub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr[OF measurable_comb_seq])
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure S ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times)  (auto intro!: sets_PiM_I finite_vimageI simp: inj_on_def)
  also have "emeasure S ?F = (\<Prod>j\<in>(op + i) -` J. emeasure M (E (i + j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI inj_on_def)
  also have "\<dots> = (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j))"
    by (rule setprod.reindex_cong [of "\<lambda>x. x - i"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure S ?E = (\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j))"
    using J by (intro emeasure_PiM_emb) simp_all
  also have "(\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j)) * (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (subst mult.commute) (auto simp: J setprod.subset_diff[symmetric])
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

lemma PiM_iter:
  "distr (M \<Otimes>\<^sub>M S) S (\<lambda>(s, \<omega>). case_nat s \<omega>) = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (PIE j:J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets.sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (M \<Otimes>\<^sub>M S) = (if 0 \<in> J then E 0 else space M) \<times>
    (prod_emb ?I ?M (Suc -` J) (PIE j:Suc -` J. E (Suc j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM PiE_iff prod_emb_def all_conj_distrib
      split: nat.split nat.split_asm)
  then have "emeasure ?D ?X = emeasure (M \<Otimes>\<^sub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr)
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure M ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times) (auto intro!: sets_PiM_I finite_vimageI)
  also have "emeasure S ?F = (\<Prod>j\<in>Suc -` J. emeasure M (E (Suc j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI)
  also have "\<dots> = (\<Prod>j\<in>J - {0}. emeasure M (E j))"
    by (rule setprod.reindex_cong [of "\<lambda>x. x - 1"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure M ?E * (\<Prod>j\<in>J - {0}. emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (auto simp: M.emeasure_space_1 setprod.remove J)
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

end

end
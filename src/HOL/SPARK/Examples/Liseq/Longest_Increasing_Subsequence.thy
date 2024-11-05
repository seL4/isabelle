(*  Title:      HOL/SPARK/Examples/Liseq/Longest_Increasing_Subsequence.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Longest_Increasing_Subsequence
imports "HOL-SPARK.SPARK"
begin

text \<open>
Set of all increasing subsequences in a prefix of an array
\<close>

definition iseq :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat \<Rightarrow> nat set set" where
  "iseq xs l = {is. (\<forall>i\<in>is. i < l) \<and>
     (\<forall>i\<in>is. \<forall>j\<in>is. i \<le> j \<longrightarrow> xs i \<le> xs j)}"

text \<open>
Length of longest increasing subsequence in a prefix of an array
\<close>

definition liseq :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat \<Rightarrow> nat" where
  "liseq xs i = Max (card ` iseq xs i)"

text \<open>
Length of longest increasing subsequence ending at a particular position
\<close>

definition liseq' :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat \<Rightarrow> nat" where
  "liseq' xs i = Max (card ` (iseq xs (Suc i) \<inter> {is. Max is = i}))"

lemma iseq_finite: "finite (iseq xs i)"
  apply (simp add: iseq_def)
  apply (rule finite_subset [OF _
    finite_Collect_subsets [of "{j. j < i}"]])
  apply auto
  done

lemma iseq_finite': "is \<in> iseq xs i \<Longrightarrow> finite is"
  by (auto simp add: iseq_def bounded_nat_set_is_finite)

lemma iseq_singleton: "i < l \<Longrightarrow> {i} \<in> iseq xs l"
  by (simp add: iseq_def)

lemma iseq_trivial: "{} \<in> iseq xs i"
  by (simp add: iseq_def)

lemma iseq_nonempty: "iseq xs i \<noteq> {}"
  by (auto intro: iseq_trivial)

lemma liseq'_ge1: "1 \<le> liseq' xs x"
  apply (simp add: liseq'_def)
  apply (subgoal_tac "iseq xs (Suc x) \<inter> {is. Max is = x} \<noteq> {}")
  apply (simp add: Max_ge_iff iseq_finite)
  apply (rule_tac x="{x}" in bexI)
  apply (auto intro: iseq_singleton)
  done

lemma liseq_expand:
  assumes R: "\<And>is. liseq xs i = card is \<Longrightarrow> is \<in> iseq xs i \<Longrightarrow>
    (\<And>js. js \<in> iseq xs i \<Longrightarrow> card js \<le> card is) \<Longrightarrow> P"
  shows "P"
proof -
  have "Max (card ` iseq xs i) \<in> card ` iseq xs i"
    by (rule Max_in) (simp_all add: iseq_finite iseq_nonempty)
  then obtain js where js: "liseq xs i = card js" and "js \<in> iseq xs i"
    by (rule imageE) (simp add: liseq_def)
  moreover {
    fix js'
    assume "js' \<in> iseq xs i"
    then have "card js' \<le> card js"
      by (simp add: js [symmetric] liseq_def iseq_finite iseq_trivial)
  }
  ultimately show ?thesis by (rule R)
qed

lemma liseq'_expand:
  assumes R: "\<And>is. liseq' xs i = card is \<Longrightarrow> is \<in> iseq xs (Suc i) \<Longrightarrow>
    finite is \<Longrightarrow> Max is = i \<Longrightarrow>
    (\<And>js. js \<in> iseq xs (Suc i) \<Longrightarrow> Max js = i \<Longrightarrow> card js \<le> card is) \<Longrightarrow>
    is \<noteq> {} \<Longrightarrow> P"
  shows "P"
proof -
  have "Max (card ` (iseq xs (Suc i) \<inter> {is. Max is = i})) \<in>
    card ` (iseq xs (Suc i) \<inter> {is. Max is = i})"
    by (auto simp add: iseq_finite intro!: iseq_singleton Max_in)
  then obtain js where js: "liseq' xs i = card js" and "js \<in> iseq xs (Suc i)"
    and "finite js" and "Max js = i"
    by (auto simp add: liseq'_def intro: iseq_finite')
  moreover have max: "card js' \<le> card js" if "js' \<in> iseq xs (Suc i)" "Max js' = i" for js'
    using that by (auto simp add: js [symmetric] liseq'_def iseq_finite intro!: iseq_singleton)
  moreover have "card {i} \<le> card js"
    by (rule max) (simp_all add: iseq_singleton)
  then have "js \<noteq> {}" by auto
  ultimately show ?thesis by (rule R)
qed

lemma liseq'_ge:
  "j = card js \<Longrightarrow> js \<in> iseq xs (Suc i) \<Longrightarrow> Max js = i \<Longrightarrow>
  js \<noteq> {} \<Longrightarrow> j \<le> liseq' xs i"
  by (simp add: liseq'_def iseq_finite)

lemma liseq'_eq:
  "j = card js \<Longrightarrow> js \<in> iseq xs (Suc i) \<Longrightarrow> Max js = i \<Longrightarrow>
  js \<noteq> {} \<Longrightarrow> (\<And>js'. js' \<in> iseq xs (Suc i) \<Longrightarrow> Max js' = i \<Longrightarrow> finite js' \<Longrightarrow>
    js' \<noteq> {} \<Longrightarrow> card js' \<le> card js) \<Longrightarrow>
  j = liseq' xs i"
  by (fastforce simp add: liseq'_def iseq_finite
    intro: Max_eqI [symmetric])

lemma liseq_ge:
  "j = card js \<Longrightarrow> js \<in> iseq xs i \<Longrightarrow> j \<le> liseq xs i"
  by (auto simp add: liseq_def iseq_finite)

lemma liseq_eq:
  "j = card js \<Longrightarrow> js \<in> iseq xs i \<Longrightarrow>
  (\<And>js'. js' \<in> iseq xs i \<Longrightarrow> finite js' \<Longrightarrow>
    js' \<noteq> {} \<Longrightarrow> card js' \<le> card js) \<Longrightarrow>
  j = liseq xs i"
  by (fastforce simp add: liseq_def iseq_finite
    intro: Max_eqI [symmetric])

lemma max_notin: "finite xs \<Longrightarrow> Max xs < x \<Longrightarrow> x \<notin> xs"
  by (cases "xs = {}") auto

lemma iseq_insert:
  "xs (Max is) \<le> xs i \<Longrightarrow> is \<in> iseq xs i \<Longrightarrow>
  is \<union> {i} \<in> iseq xs (Suc i)"
  apply (frule iseq_finite')
  apply (cases "is = {}")
  apply (auto simp add: iseq_def)
  apply (rule order_trans [of _ "xs (Max is)"])
  apply auto
  apply (thin_tac "\<forall>a\<in>is. a < i")
  apply (drule_tac x=ia in bspec)
  apply assumption
  apply (drule_tac x="Max is" in bspec)
  apply (auto intro: Max_in)
  done

lemma iseq_diff: "is \<in> iseq xs (Suc (Max is)) \<Longrightarrow>
  is - {Max is} \<in> iseq xs (Suc (Max (is - {Max is})))"
  apply (frule iseq_finite')
  apply (simp add: iseq_def less_Suc_eq_le)
  done

lemma iseq_butlast:
  assumes "js \<in> iseq xs (Suc i)" and "js \<noteq> {}"
  and "Max js \<noteq> i"
  shows "js \<in> iseq xs i"
proof -
  from assms have fin: "finite js"
    by (simp add: iseq_finite')
  with assms have "Max js \<in> js"
    by auto
  with assms have "Max js < i"
    by (auto simp add: iseq_def)
  with fin assms have "\<forall>j\<in>js. j < i"
    by simp
  with assms show ?thesis
    by (simp add: iseq_def)
qed

lemma iseq_mono: "is \<in> iseq xs i \<Longrightarrow> i \<le> j \<Longrightarrow> is \<in> iseq xs j"
  by (auto simp add: iseq_def)

lemma diff_nonempty:
  assumes "1 < card is"
  shows "is - {i} \<noteq> {}"
proof -
  from assms have fin: "finite is" by (auto intro: card_ge_0_finite)
  with assms fin have "card is - 1 \<le> card (is - {i})"
    by (simp add: card_Diff_singleton_if)
  with assms have "0 < card (is - {i})" by simp
  then show ?thesis by (simp add: card_gt_0_iff)
qed

lemma Max_diff:
  assumes "1 < card is"
  shows "Max (is - {Max is}) < Max is"
proof -
  from assms have "finite is" by (auto intro: card_ge_0_finite)
  moreover from assms have "is - {Max is} \<noteq> {}"
    by (rule diff_nonempty)
  ultimately show ?thesis using assms
    apply (auto simp add: not_less)
    apply (subgoal_tac "a \<le> Max is")
    apply auto
    done
qed

lemma iseq_nth: "js \<in> iseq xs l \<Longrightarrow> 1 < card js \<Longrightarrow>
  xs (Max (js - {Max js})) \<le> xs (Max js)"
  apply (auto simp add: iseq_def)
  apply (subgoal_tac "Max (js - {Max js}) \<in> js")
  apply (thin_tac "\<forall>i\<in>js. i < l")
  apply (drule_tac x="Max (js - {Max js})" in bspec)
  apply assumption
  apply (drule_tac x="Max js" in bspec)
  using card_gt_0_iff [of js]
  apply simp
  using Max_diff [of js]
  apply simp
  using Max_in [of "js - {Max js}", OF _ diff_nonempty] card_gt_0_iff [of js]
  apply auto
  done

lemma card_leq1_singleton:
  assumes "finite xs" "xs \<noteq> {}" "card xs \<le> 1"
  obtains x where "xs = {x}"
  using assms
  by induct simp_all

lemma longest_iseq1:
  "liseq' xs i =
   Max ({0} \<union> {liseq' xs j |j. j < i \<and> xs j \<le> xs i}) + 1"
proof -
  have "Max ({0} \<union> {liseq' xs j |j. j < i \<and> xs j \<le> xs i}) = liseq' xs i - 1"
  proof (rule Max_eqI)
    fix y
    assume "y \<in> {0} \<union> {liseq' xs j |j. j < i \<and> xs j \<le> xs i}"
    then show "y \<le> liseq' xs i - 1"
    proof
      assume "y \<in> {liseq' xs j |j. j < i \<and> xs j \<le> xs i}"
      then obtain j where j: "j < i" "xs j \<le> xs i" "y = liseq' xs j"
        by auto
      have "liseq' xs j + 1 \<le> liseq' xs i"
      proof (rule liseq'_expand)
        fix "is"
        assume H: "liseq' xs j = card is" "is \<in> iseq xs (Suc j)"
          "finite is" "Max is = j" "is \<noteq> {}"
        from H j have "card is + 1 = card (is \<union> {i})"
          by (simp add: card.insert_remove max_notin)
        moreover {
          from H j have "xs (Max is) \<le> xs i" by simp
          moreover from \<open>j < i\<close> have "Suc j \<le> i" by simp
          with \<open>is \<in> iseq xs (Suc j)\<close> have "is \<in> iseq xs i"
            by (rule iseq_mono)
          ultimately have "is \<union> {i} \<in> iseq xs (Suc i)"
          by (rule iseq_insert)
        } moreover from H j have "Max (is \<union> {i}) = i" by simp
        moreover have "is \<union> {i} \<noteq> {}" by simp
        ultimately have "card is + 1 \<le> liseq' xs i"
          by (rule liseq'_ge)
        with H show ?thesis by simp
      qed
      with j show "y \<le> liseq' xs i - 1"
        by simp
    qed simp
  next
    have "liseq' xs i \<le> 1 \<or>
      (\<exists>j. liseq' xs i - 1 = liseq' xs j \<and> j < i \<and> xs j \<le> xs i)"
    proof (rule liseq'_expand)
      fix "is"
      assume H: "liseq' xs i = card is" "is \<in> iseq xs (Suc i)"
        "finite is" "Max is = i" "is \<noteq> {}"
      assume R: "\<And>js. js \<in> iseq xs (Suc i) \<Longrightarrow> Max js = i \<Longrightarrow>
        card js \<le> card is"
      show ?thesis
      proof (cases "card is \<le> 1")
        case True with H show ?thesis by simp
      next
        case False
        then have "1 < card is" by simp
        then have "Max (is - {Max is}) < Max is"
          by (rule Max_diff)
        from \<open>is \<in> iseq xs (Suc i)\<close> \<open>1 < card is\<close>
        have "xs (Max (is - {Max is})) \<le> xs (Max is)"
          by (rule iseq_nth)
        have "card is - 1 = liseq' xs (Max (is - {i}))"
        proof (rule liseq'_eq)
          from \<open>Max is = i\<close> [symmetric] \<open>finite is\<close> \<open>is \<noteq> {}\<close>
          show "card is - 1 = card (is - {i})" by simp
        next
          from \<open>is \<in> iseq xs (Suc i)\<close> \<open>Max is = i\<close> [symmetric]
          show "is - {i} \<in> iseq xs (Suc (Max (is - {i})))"
            by simp (rule iseq_diff)
        next
          from \<open>1 < card is\<close>
          show "is - {i} \<noteq> {}" by (rule diff_nonempty)
        next
          fix js
          assume "js \<in> iseq xs (Suc (Max (is - {i})))"
            "Max js = Max (is - {i})" "finite js" "js \<noteq> {}"
          from \<open>xs (Max (is - {Max is})) \<le> xs (Max is)\<close>
            \<open>Max js = Max (is - {i})\<close> \<open>Max is = i\<close>
          have "xs (Max js) \<le> xs i" by simp
          moreover from \<open>Max is = i\<close> \<open>Max (is - {Max is}) < Max is\<close>
          have "Suc (Max (is - {i})) \<le> i"
            by simp
          with \<open>js \<in> iseq xs (Suc (Max (is - {i})))\<close>
          have "js \<in> iseq xs i"
            by (rule iseq_mono)
          ultimately have "js \<union> {i} \<in> iseq xs (Suc i)"
            by (rule iseq_insert)
          moreover from \<open>js \<noteq> {}\<close> \<open>finite js\<close> \<open>Max js = Max (is - {i})\<close>
            \<open>Max is = i\<close> [symmetric] \<open>Max (is - {Max is}) < Max is\<close>
          have "Max (js \<union> {i}) = i"
            by simp
          ultimately have "card (js \<union> {i}) \<le> card is" by (rule R)
          moreover from \<open>Max is = i\<close> [symmetric] \<open>finite js\<close>
            \<open>Max (is - {Max is}) < Max is\<close> \<open>Max js = Max (is - {i})\<close>
          have "i \<notin> js" by (simp add: max_notin)
          with \<open>finite js\<close>
          have "card (js \<union> {i}) = card ((js \<union> {i}) - {i}) + 1"
            by simp
          ultimately show "card js \<le> card (is - {i})"
            using \<open>i \<notin> js\<close> \<open>Max is = i\<close> [symmetric] \<open>is \<noteq> {}\<close> \<open>finite is\<close>
            by simp
        qed simp
        with H \<open>Max (is - {Max is}) < Max is\<close>
          \<open>xs (Max (is - {Max is})) \<le> xs (Max is)\<close>
        show ?thesis by auto
      qed
    qed
    then show "liseq' xs i - 1 \<in> {0} \<union>
      {liseq' xs j |j. j < i \<and> xs j \<le> xs i}" by simp
  qed simp
  moreover have "1 \<le> liseq' xs i" by (rule liseq'_ge1)
  ultimately show ?thesis by simp
qed

lemma longest_iseq2': "liseq xs i < liseq' xs i \<Longrightarrow>
  liseq xs (Suc i) = liseq' xs i"
  apply (rule_tac xs=xs and i=i in liseq'_expand)
  apply simp
  apply (rule liseq_eq [symmetric])
  apply (rule refl)
  apply assumption
  apply (case_tac "Max js' = i")
  apply simp
  apply (drule_tac js=js' in iseq_butlast)
  apply assumption+
  apply (drule_tac js=js' in liseq_ge [OF refl])
  apply simp
  done

lemma longest_iseq2: "liseq xs i < liseq' xs i \<Longrightarrow>
  liseq xs i + 1 = liseq' xs i"
  apply (rule_tac xs=xs and i=i in liseq'_expand)
  apply simp
  apply (rule_tac xs=xs and i=i in liseq_expand)
  apply (drule_tac s="Max is" in sym)
  apply simp
  apply (case_tac "card is \<le> 1")
  apply simp
  apply (drule iseq_diff)
  apply (drule_tac i="Suc (Max (is - {Max is}))" and j="Max is" in iseq_mono)
  apply (simp add: less_eq_Suc_le [symmetric])
  apply (rule Max_diff)
  apply simp
  apply (drule_tac x="is - {Max is}" in meta_spec,
    drule meta_mp, assumption)
  apply simp
  done

lemma longest_iseq3:
  "liseq xs j = liseq' xs i \<Longrightarrow> xs i \<le> xs j \<Longrightarrow> i < j \<Longrightarrow>
  liseq xs (Suc j) = liseq xs j + 1"
  apply (rule_tac xs=xs and i=j in liseq_expand)
  apply simp
  apply (rule_tac xs=xs and i=i in liseq'_expand)
  apply simp
  apply (rule_tac js="isa \<union> {j}" in liseq_eq [symmetric])
  apply (simp add: card.insert_remove card_Diff_singleton_if max_notin)
  apply (rule iseq_insert)
  apply simp
  apply (erule iseq_mono)
  apply simp
  apply (case_tac "j = Max js'")
  apply simp
  apply (drule iseq_diff)
  apply (drule_tac x="js' - {j}" in meta_spec)
  apply (drule meta_mp)
  apply simp
  apply (case_tac "card js' \<le> 1")
  apply (erule_tac xs=js' in card_leq1_singleton)
  apply assumption+
  apply (simp add: iseq_trivial)
  apply (erule iseq_mono)
  apply (simp add: less_eq_Suc_le [symmetric])
  apply (rule Max_diff)
  apply simp
  apply (rule le_diff_iff [THEN iffD1, of 1])
  apply (simp add: card_0_eq [symmetric] del: card_0_eq)
  apply (simp add: card.insert_remove)
  apply (subgoal_tac "card (js' - {j}) = card js' - 1")
  apply (simp add: card.insert_remove card_Diff_singleton_if max_notin)
  apply (frule_tac A=js' in Max_in)
  apply assumption
  apply (simp add: card_Diff_singleton_if)
  apply (drule_tac js=js' in iseq_butlast)
  apply assumption
  apply (erule not_sym)
  apply (drule_tac x=js' in meta_spec)
  apply (drule meta_mp)
  apply assumption
  apply (simp add: card_insert_disjoint max_notin)
  done

lemma longest_iseq4:
  "liseq xs j = liseq' xs i \<Longrightarrow> xs i \<le> xs j \<Longrightarrow> i < j \<Longrightarrow>
  liseq' xs j = liseq' xs i + 1"
  apply (rule_tac xs=xs and i=j in liseq_expand)
  apply simp
  apply (rule_tac xs=xs and i=i in liseq'_expand)
  apply simp
  apply (rule_tac js="isa \<union> {j}" in liseq'_eq [symmetric])
  apply (simp add: card.insert_remove card_Diff_singleton_if max_notin)
  apply (rule iseq_insert)
  apply simp
  apply (erule iseq_mono)
  apply simp
  apply simp
  apply simp
  apply (drule_tac s="Max js'" in sym)
  apply simp
  apply (drule iseq_diff)
  apply (drule_tac x="js' - {j}" in meta_spec)
  apply (drule meta_mp)
  apply simp
  apply (case_tac "card js' \<le> 1")
  apply (erule_tac xs=js' in card_leq1_singleton)
  apply assumption+
  apply (simp add: iseq_trivial)
  apply (erule iseq_mono)
  apply (simp add: less_eq_Suc_le [symmetric])
  apply (rule Max_diff)
  apply simp
  apply (rule le_diff_iff [THEN iffD1, of 1])
  apply (simp add: card_0_eq [symmetric] del: card_0_eq)
  apply (simp add: card.insert_remove)
  apply (subgoal_tac "card (js' - {j}) = card js' - 1")
  apply (simp add: card.insert_remove card_Diff_singleton_if max_notin)
  apply (frule_tac A=js' in Max_in)
  apply assumption
  apply (simp add: card_Diff_singleton_if)
  done

lemma longest_iseq5: "liseq' xs i \<le> liseq xs i \<Longrightarrow>
  liseq xs (Suc i) = liseq xs i"
  apply (rule_tac i=i and xs=xs in liseq'_expand)
  apply simp
  apply (rule_tac xs=xs and i=i in liseq_expand)
  apply simp
  apply (rule liseq_eq [symmetric])
  apply (rule refl)
  apply (erule iseq_mono)
  apply simp
  apply (case_tac "Max js' = i")
  apply (drule_tac x=js' in meta_spec)
  apply simp
  apply (drule iseq_butlast, assumption, assumption)
  apply simp
  done

lemma liseq_empty: "liseq xs 0 = 0"
  apply (rule_tac js="{}" in liseq_eq [symmetric])
  apply simp
  apply (rule iseq_trivial)
  apply (simp add: iseq_def)
  done

lemma liseq'_singleton: "liseq' xs 0 = 1"
  by (simp add: longest_iseq1 [of _ 0])

lemma liseq_singleton: "liseq xs (Suc 0) = Suc 0"
  by (simp add: longest_iseq2' liseq_empty liseq'_singleton)

lemma liseq'_Suc_unfold:
  "A j \<le> x \<Longrightarrow>
   (insert 0 {liseq' A j' |j'. j' < Suc j \<and> A j' \<le> x}) =
   (insert 0 {liseq' A j' |j'. j' < j \<and> A j' \<le> x}) \<union>
   {liseq' A j}"
  by (auto simp add: less_Suc_eq)

lemma liseq'_Suc_unfold':
  "\<not> (A j \<le> x) \<Longrightarrow>
   {liseq' A j' |j'. j' < Suc j \<and> A j' \<le> x} =
   {liseq' A j' |j'. j' < j \<and> A j' \<le> x}"
  by (auto simp add: less_Suc_eq)

lemma iseq_card_limit:
  assumes "is \<in> iseq A i"
  shows "card is \<le> i"
proof -
  from assms have "is \<subseteq> {0..<i}"
    by (auto simp add: iseq_def)
  with finite_atLeastLessThan have "card is \<le> card {0..<i}"
    by (rule card_mono)
  with card_atLeastLessThan show ?thesis by simp
qed

lemma liseq_limit: "liseq A i \<le> i"
  by (rule_tac xs=A and i=i in liseq_expand)
    (simp add: iseq_card_limit)

lemma liseq'_limit: "liseq' A i \<le> i + 1"
  by (rule_tac xs=A and i=i in liseq'_expand)
    (simp add: iseq_card_limit)

definition max_ext :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "max_ext A i j = Max ({0} \<union> {liseq' A j' |j'. j' < j \<and> A j' \<le> A i})"

lemma max_ext_limit: "max_ext A i j \<le> j"
  apply (auto simp add: max_ext_def)
  apply (drule Suc_leI)
  apply (cut_tac i=j' and A=A in liseq'_limit)
  apply simp
  done


text \<open>Proof functions\<close>

abbreviation (input)
  "arr_conv a \<equiv> (\<lambda>n. a (int n))"

lemma idx_conv_suc:
  "0 \<le> i \<Longrightarrow> nat (i + 1) = nat i + 1"
  by simp

abbreviation liseq_ends_at' :: "(int \<Rightarrow> 'a::linorder) \<Rightarrow> int \<Rightarrow> int" where
  "liseq_ends_at' A i \<equiv> int (liseq' (\<lambda>l. A (int l)) (nat i))"

abbreviation liseq_prfx' :: "(int \<Rightarrow> 'a::linorder) \<Rightarrow> int \<Rightarrow> int" where
  "liseq_prfx' A i \<equiv> int (liseq (\<lambda>l. A (int l)) (nat i))"

abbreviation max_ext' :: "(int \<Rightarrow> 'a::linorder) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "max_ext' A i j \<equiv> int (max_ext (\<lambda>l. A (int l)) (nat i) (nat j))"

spark_proof_functions
  liseq_ends_at = "liseq_ends_at' :: (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"
  liseq_prfx = "liseq_prfx' :: (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"
  max_ext = "max_ext' :: (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"


text \<open>The verification conditions\<close>

spark_open \<open>liseq/liseq_length\<close>

spark_vc procedure_liseq_length_5
  by (simp_all add: liseq_singleton liseq'_singleton)

spark_vc procedure_liseq_length_6
proof -
  from H1 H2 H3 H4
  have eq: "liseq (arr_conv a) (nat i) =
    liseq' (arr_conv a) (nat pmax)"
    by simp
  from H14 H3 H4
  have pmax1: "arr_conv a (nat pmax) \<le> arr_conv a (nat i)"
    by simp
  from H3 H4 have pmax2: "nat pmax < nat i"
    by simp
  {
    fix i2
    assume i2: "0 \<le> i2" "i2 \<le> i"
    have "(l(i := l pmax + 1)) i2 =
      int (liseq' (arr_conv a) (nat i2))"
    proof (cases "i2 = i")
      case True
      from eq pmax1 pmax2 have "liseq' (arr_conv a) (nat i) =
        liseq' (arr_conv a) (nat pmax) + 1"
        by (rule longest_iseq4)
      with True H1 H3 H4 show ?thesis
        by simp
    next
      case False
      with H1 i2 show ?thesis
        by simp
    qed
  }
  then show ?C1 by simp
  from eq pmax1 pmax2
  have "liseq (arr_conv a) (Suc (nat i)) =
    liseq (arr_conv a) (nat i) + 1"
    by (rule longest_iseq3)
 with H2 H3 H4 show ?C2
    by (simp add: idx_conv_suc)
qed

spark_vc procedure_liseq_length_7
proof -
  from H1 show ?C1
    by (simp add: max_ext_def longest_iseq1 [of _ "nat i"])
  from H6
  have m: "max_ext (arr_conv a) (nat i) (nat i) + 1 =
    liseq' (arr_conv a) (nat i)"
    by (simp add: max_ext_def longest_iseq1 [of _ "nat i"])
  with H2 H18
  have gt: "liseq (arr_conv a) (nat i) < liseq' (arr_conv a) (nat i)"
    by simp
  then have "liseq' (arr_conv a) (nat i) = liseq (arr_conv a) (nat i) + 1"
    by (rule longest_iseq2 [symmetric])
  with H2 m show ?C2 by simp
  from gt have "liseq (arr_conv a) (Suc (nat i)) = liseq' (arr_conv a) (nat i)"
    by (rule longest_iseq2')
  with m H6 show ?C3 by (simp add: idx_conv_suc)
qed

spark_vc procedure_liseq_length_8
proof -
  {
    fix i2
    assume i2: "0 \<le> i2" "i2 \<le> i"
    have "(l(i := max_ext' a i i + 1)) i2 =
      int (liseq' (arr_conv a) (nat i2))"
    proof (cases "i2 = i")
      case True
      with H1 show ?thesis
        by (simp add: max_ext_def longest_iseq1 [of _ "nat i"])
    next
      case False
      with H1 i2 show ?thesis by simp
    qed
  }
  then show ?C1 by simp
  from H2 H6 H18
  have "liseq' (arr_conv a) (nat i) \<le> liseq (arr_conv a) (nat i)"
    by (simp add: max_ext_def longest_iseq1 [of _ "nat i"])
  then have "liseq (arr_conv a) (Suc (nat i)) = liseq (arr_conv a) (nat i)"
    by (rule longest_iseq5)
  with H2 H6 show ?C2 by (simp add: idx_conv_suc)
qed

spark_vc procedure_liseq_length_12
  by (simp add: max_ext_def)

spark_vc procedure_liseq_length_13
  using H1 H6 H13 H21 H22
  by (simp add: max_ext_def
    idx_conv_suc liseq'_Suc_unfold max_def del: Max_less_iff)

spark_vc procedure_liseq_length_14
  using H1 H6 H13 H21
  by (cases "a j \<le> a i")
    (simp_all add: max_ext_def
      idx_conv_suc liseq'_Suc_unfold liseq'_Suc_unfold')

spark_vc procedure_liseq_length_19
  using H3 H4 H5 H8 H9
  apply (rule_tac y="int (nat i)" in order_trans)
  apply (cut_tac A="arr_conv a" and i="nat i" and j="nat i" in max_ext_limit)
  apply simp_all
  done

spark_vc procedure_liseq_length_23
  using H2 H3 H4 H7 H8 H11
  apply (rule_tac y="int (nat i)" in order_trans)
  apply (cut_tac A="arr_conv a" and i="nat i" in liseq_limit)
  apply simp_all
  done

spark_vc procedure_liseq_length_29
  using H2 H3 H8 H13
  by (simp add: add1_zle_eq [symmetric])

spark_end

end

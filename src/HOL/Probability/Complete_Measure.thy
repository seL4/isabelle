(*  Title:      HOL/Probability/Complete_Measure.thy
    Author:     Robert Himmelmann, Johannes Hoelzl, TU Muenchen
*)

theory Complete_Measure
imports Lebesgue_Integration
begin

definition
  "split_completion M A p = (if A \<in> sets M then p = (A, {}) else
   \<exists>N'. A = fst p \<union> snd p \<and> fst p \<inter> snd p = {} \<and> fst p \<in> sets M \<and> snd p \<subseteq> N' \<and> N' \<in> null_sets M)"

definition
  "main_part M A = fst (Eps (split_completion M A))"

definition
  "null_part M A = snd (Eps (split_completion M A))"

definition completion :: "'a measure \<Rightarrow> 'a measure" where
  "completion M = measure_of (space M) { S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' }
    (emeasure M \<circ> main_part M)"

lemma completion_into_space:
  "{ S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' } \<subseteq> Pow (space M)"
  using sets_into_space by auto

lemma space_completion[simp]: "space (completion M) = space M"
  unfolding completion_def using space_measure_of[OF completion_into_space] by simp

lemma completionI:
  assumes "A = S \<union> N" "N \<subseteq> N'" "N' \<in> null_sets M" "S \<in> sets M"
  shows "A \<in> { S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' }"
  using assms by auto

lemma completionE:
  assumes "A \<in> { S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' }"
  obtains S N N' where "A = S \<union> N" "N \<subseteq> N'" "N' \<in> null_sets M" "S \<in> sets M"
  using assms by auto

lemma sigma_algebra_completion:
  "sigma_algebra (space M) { S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' }"
    (is "sigma_algebra _ ?A")
  unfolding sigma_algebra_iff2
proof (intro conjI ballI allI impI)
  show "?A \<subseteq> Pow (space M)"
    using sets_into_space by auto
next
  show "{} \<in> ?A" by auto
next
  let ?C = "space M"
  fix A assume "A \<in> ?A" from completionE[OF this] guess S N N' .
  then show "space M - A \<in> ?A"
    by (intro completionI[of _ "(?C - S) \<inter> (?C - N')" "(?C - S) \<inter> N' \<inter> (?C - N)"]) auto
next
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> ?A"
  then have "\<forall>n. \<exists>S N N'. A n = S \<union> N \<and> S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N'"
    by (auto simp: image_subset_iff)
  from choice[OF this] guess S ..
  from choice[OF this] guess N ..
  from choice[OF this] guess N' ..
  then show "UNION UNIV A \<in> ?A"
    using null_sets_UN[of N']
    by (intro completionI[of _ "UNION UNIV S" "UNION UNIV N" "UNION UNIV N'"]) auto
qed

lemma sets_completion:
  "sets (completion M) = { S \<union> N |S N N'. S \<in> sets M \<and> N' \<in> null_sets M \<and> N \<subseteq> N' }"
  using sigma_algebra.sets_measure_of_eq[OF sigma_algebra_completion] by (simp add: completion_def)

lemma sets_completionE:
  assumes "A \<in> sets (completion M)"
  obtains S N N' where "A = S \<union> N" "N \<subseteq> N'" "N' \<in> null_sets M" "S \<in> sets M"
  using assms unfolding sets_completion by auto

lemma sets_completionI:
  assumes "A = S \<union> N" "N \<subseteq> N'" "N' \<in> null_sets M" "S \<in> sets M"
  shows "A \<in> sets (completion M)"
  using assms unfolding sets_completion by auto

lemma sets_completionI_sets[intro, simp]:
  "A \<in> sets M \<Longrightarrow> A \<in> sets (completion M)"
  unfolding sets_completion by force

lemma null_sets_completion:
  assumes "N' \<in> null_sets M" "N \<subseteq> N'" shows "N \<in> sets (completion M)"
  using assms by (intro sets_completionI[of N "{}" N N']) auto

lemma split_completion:
  assumes "A \<in> sets (completion M)"
  shows "split_completion M A (main_part M A, null_part M A)"
proof cases
  assume "A \<in> sets M" then show ?thesis
    by (simp add: split_completion_def[abs_def] main_part_def null_part_def)
next
  assume nA: "A \<notin> sets M"
  show ?thesis
    unfolding main_part_def null_part_def if_not_P[OF nA]
  proof (rule someI2_ex)
    from assms[THEN sets_completionE] guess S N N' . note A = this
    let ?P = "(S, N - S)"
    show "\<exists>p. split_completion M A p"
      unfolding split_completion_def if_not_P[OF nA] using A
    proof (intro exI conjI)
      show "A = fst ?P \<union> snd ?P" using A by auto
      show "snd ?P \<subseteq> N'" using A by auto
   qed auto
  qed auto
qed

lemma
  assumes "S \<in> sets (completion M)"
  shows main_part_sets[intro, simp]: "main_part M S \<in> sets M"
    and main_part_null_part_Un[simp]: "main_part M S \<union> null_part M S = S"
    and main_part_null_part_Int[simp]: "main_part M S \<inter> null_part M S = {}"
  using split_completion[OF assms]
  by (auto simp: split_completion_def split: split_if_asm)

lemma main_part[simp]: "S \<in> sets M \<Longrightarrow> main_part M S = S"
  using split_completion[of S M]
  by (auto simp: split_completion_def split: split_if_asm)

lemma null_part:
  assumes "S \<in> sets (completion M)" shows "\<exists>N. N\<in>null_sets M \<and> null_part M S \<subseteq> N"
  using split_completion[OF assms] by (auto simp: split_completion_def split: split_if_asm)

lemma null_part_sets[intro, simp]:
  assumes "S \<in> sets M" shows "null_part M S \<in> sets M" "emeasure M (null_part M S) = 0"
proof -
  have S: "S \<in> sets (completion M)" using assms by auto
  have "S - main_part M S \<in> sets M" using assms by auto
  moreover
  from main_part_null_part_Un[OF S] main_part_null_part_Int[OF S]
  have "S - main_part M S = null_part M S" by auto
  ultimately show sets: "null_part M S \<in> sets M" by auto
  from null_part[OF S] guess N ..
  with emeasure_eq_0[of N _ "null_part M S"] sets
  show "emeasure M (null_part M S) = 0" by auto
qed

lemma emeasure_main_part_UN:
  fixes S :: "nat \<Rightarrow> 'a set"
  assumes "range S \<subseteq> sets (completion M)"
  shows "emeasure M (main_part M (\<Union>i. (S i))) = emeasure M (\<Union>i. main_part M (S i))"
proof -
  have S: "\<And>i. S i \<in> sets (completion M)" using assms by auto
  then have UN: "(\<Union>i. S i) \<in> sets (completion M)" by auto
  have "\<forall>i. \<exists>N. N \<in> null_sets M \<and> null_part M (S i) \<subseteq> N"
    using null_part[OF S] by auto
  from choice[OF this] guess N .. note N = this
  then have UN_N: "(\<Union>i. N i) \<in> null_sets M" by (intro null_sets_UN) auto
  have "(\<Union>i. S i) \<in> sets (completion M)" using S by auto
  from null_part[OF this] guess N' .. note N' = this
  let ?N = "(\<Union>i. N i) \<union> N'"
  have null_set: "?N \<in> null_sets M" using N' UN_N by (intro null_sets.Un) auto
  have "main_part M (\<Union>i. S i) \<union> ?N = (main_part M (\<Union>i. S i) \<union> null_part M (\<Union>i. S i)) \<union> ?N"
    using N' by auto
  also have "\<dots> = (\<Union>i. main_part M (S i) \<union> null_part M (S i)) \<union> ?N"
    unfolding main_part_null_part_Un[OF S] main_part_null_part_Un[OF UN] by auto
  also have "\<dots> = (\<Union>i. main_part M (S i)) \<union> ?N"
    using N by auto
  finally have *: "main_part M (\<Union>i. S i) \<union> ?N = (\<Union>i. main_part M (S i)) \<union> ?N" .
  have "emeasure M (main_part M (\<Union>i. S i)) = emeasure M (main_part M (\<Union>i. S i) \<union> ?N)"
    using null_set UN by (intro emeasure_Un_null_set[symmetric]) auto
  also have "\<dots> = emeasure M ((\<Union>i. main_part M (S i)) \<union> ?N)"
    unfolding * ..
  also have "\<dots> = emeasure M (\<Union>i. main_part M (S i))"
    using null_set S by (intro emeasure_Un_null_set) auto
  finally show ?thesis .
qed

lemma emeasure_completion[simp]:
  assumes S: "S \<in> sets (completion M)" shows "emeasure (completion M) S = emeasure M (main_part M S)"
proof (subst emeasure_measure_of[OF completion_def completion_into_space])
  let ?\<mu> = "emeasure M \<circ> main_part M"
  show "S \<in> sets (completion M)" "?\<mu> S = emeasure M (main_part M S) " using S by simp_all
  show "positive (sets (completion M)) ?\<mu>"
    by (simp add: positive_def emeasure_nonneg)
  show "countably_additive (sets (completion M)) ?\<mu>"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets (completion M)" "disjoint_family A"
    have "disjoint_family (\<lambda>i. main_part M (A i))"
    proof (intro disjoint_family_on_bisimulation[OF A(2)])
      fix n m assume "A n \<inter> A m = {}"
      then have "(main_part M (A n) \<union> null_part M (A n)) \<inter> (main_part M (A m) \<union> null_part M (A m)) = {}"
        using A by (subst (1 2) main_part_null_part_Un) auto
      then show "main_part M (A n) \<inter> main_part M (A m) = {}" by auto
    qed
    then have "(\<Sum>n. emeasure M (main_part M (A n))) = emeasure M (\<Union>i. main_part M (A i))"
      using A by (auto intro!: suminf_emeasure)
    then show "(\<Sum>n. ?\<mu> (A n)) = ?\<mu> (UNION UNIV A)"
      by (simp add: completion_def emeasure_main_part_UN[OF A(1)])
  qed
qed

lemma emeasure_completion_UN:
  "range S \<subseteq> sets (completion M) \<Longrightarrow>
    emeasure (completion M) (\<Union>i::nat. (S i)) = emeasure M (\<Union>i. main_part M (S i))"
  by (subst emeasure_completion) (auto simp add: emeasure_main_part_UN)

lemma emeasure_completion_Un:
  assumes S: "S \<in> sets (completion M)" and T: "T \<in> sets (completion M)"
  shows "emeasure (completion M) (S \<union> T) = emeasure M (main_part M S \<union> main_part M T)"
proof (subst emeasure_completion)
  have UN: "(\<Union>i. binary (main_part M S) (main_part M T) i) = (\<Union>i. main_part M (binary S T i))"
    unfolding binary_def by (auto split: split_if_asm)
  show "emeasure M (main_part M (S \<union> T)) = emeasure M (main_part M S \<union> main_part M T)"
    using emeasure_main_part_UN[of "binary S T" M] assms
    unfolding range_binary_eq Un_range_binary UN by auto
qed (auto intro: S T)

lemma sets_completionI_sub:
  assumes N: "N' \<in> null_sets M" "N \<subseteq> N'"
  shows "N \<in> sets (completion M)"
  using assms by (intro sets_completionI[of _ "{}" N N']) auto

lemma completion_ex_simple_function:
  assumes f: "simple_function (completion M) f"
  shows "\<exists>f'. simple_function M f' \<and> (AE x in M. f x = f' x)"
proof -
  let ?F = "\<lambda>x. f -` {x} \<inter> space M"
  have F: "\<And>x. ?F x \<in> sets (completion M)" and fin: "finite (f`space M)"
    using simple_functionD[OF f] simple_functionD[OF f] by simp_all
  have "\<forall>x. \<exists>N. N \<in> null_sets M \<and> null_part M (?F x) \<subseteq> N"
    using F null_part by auto
  from choice[OF this] obtain N where
    N: "\<And>x. null_part M (?F x) \<subseteq> N x" "\<And>x. N x \<in> null_sets M" by auto
  let ?N = "\<Union>x\<in>f`space M. N x"
  let ?f' = "\<lambda>x. if x \<in> ?N then undefined else f x"
  have sets: "?N \<in> null_sets M" using N fin by (intro null_sets.finite_UN) auto
  show ?thesis unfolding simple_function_def
  proof (safe intro!: exI[of _ ?f'])
    have "?f' ` space M \<subseteq> f`space M \<union> {undefined}" by auto
    from finite_subset[OF this] simple_functionD(1)[OF f]
    show "finite (?f' ` space M)" by auto
  next
    fix x assume "x \<in> space M"
    have "?f' -` {?f' x} \<inter> space M =
      (if x \<in> ?N then ?F undefined \<union> ?N
       else if f x = undefined then ?F (f x) \<union> ?N
       else ?F (f x) - ?N)"
      using N(2) sets_into_space by (auto split: split_if_asm simp: null_sets_def)
    moreover { fix y have "?F y \<union> ?N \<in> sets M"
      proof cases
        assume y: "y \<in> f`space M"
        have "?F y \<union> ?N = (main_part M (?F y) \<union> null_part M (?F y)) \<union> ?N"
          using main_part_null_part_Un[OF F] by auto
        also have "\<dots> = main_part M (?F y) \<union> ?N"
          using y N by auto
        finally show ?thesis
          using F sets by auto
      next
        assume "y \<notin> f`space M" then have "?F y = {}" by auto
        then show ?thesis using sets by auto
      qed }
    moreover {
      have "?F (f x) - ?N = main_part M (?F (f x)) \<union> null_part M (?F (f x)) - ?N"
        using main_part_null_part_Un[OF F] by auto
      also have "\<dots> = main_part M (?F (f x)) - ?N"
        using N `x \<in> space M` by auto
      finally have "?F (f x) - ?N \<in> sets M"
        using F sets by auto }
    ultimately show "?f' -` {?f' x} \<inter> space M \<in> sets M" by auto
  next
    show "AE x in M. f x = ?f' x"
      by (rule AE_I', rule sets) auto
  qed
qed

lemma completion_ex_borel_measurable_pos:
  fixes g :: "'a \<Rightarrow> ereal"
  assumes g: "g \<in> borel_measurable (completion M)" and "\<And>x. 0 \<le> g x"
  shows "\<exists>g'\<in>borel_measurable M. (AE x in M. g x = g' x)"
proof -
  from g[THEN borel_measurable_implies_simple_function_sequence'] guess f . note f = this
  from this(1)[THEN completion_ex_simple_function]
  have "\<forall>i. \<exists>f'. simple_function M f' \<and> (AE x in M. f i x = f' x)" ..
  from this[THEN choice] obtain f' where
    sf: "\<And>i. simple_function M (f' i)" and
    AE: "\<forall>i. AE x in M. f i x = f' i x" by auto
  show ?thesis
  proof (intro bexI)
    from AE[unfolded AE_all_countable[symmetric]]
    show "AE x in M. g x = (SUP i. f' i x)" (is "AE x in M. g x = ?f x")
    proof (elim AE_mp, safe intro!: AE_I2)
      fix x assume eq: "\<forall>i. f i x = f' i x"
      moreover have "g x = (SUP i. f i x)"
        unfolding f using `0 \<le> g x` by (auto split: split_max)
      ultimately show "g x = ?f x" by auto
    qed
    show "?f \<in> borel_measurable M"
      using sf by (auto intro: borel_measurable_simple_function)
  qed
qed

lemma completion_ex_borel_measurable:
  fixes g :: "'a \<Rightarrow> ereal"
  assumes g: "g \<in> borel_measurable (completion M)"
  shows "\<exists>g'\<in>borel_measurable M. (AE x in M. g x = g' x)"
proof -
  have "(\<lambda>x. max 0 (g x)) \<in> borel_measurable (completion M)" "\<And>x. 0 \<le> max 0 (g x)" using g by auto
  from completion_ex_borel_measurable_pos[OF this] guess g_pos ..
  moreover
  have "(\<lambda>x. max 0 (- g x)) \<in> borel_measurable (completion M)" "\<And>x. 0 \<le> max 0 (- g x)" using g by auto
  from completion_ex_borel_measurable_pos[OF this] guess g_neg ..
  ultimately
  show ?thesis
  proof (safe intro!: bexI[of _ "\<lambda>x. g_pos x - g_neg x"])
    show "AE x in M. max 0 (- g x) = g_neg x \<longrightarrow> max 0 (g x) = g_pos x \<longrightarrow> g x = g_pos x - g_neg x"
    proof (intro AE_I2 impI)
      fix x assume g: "max 0 (- g x) = g_neg x" "max 0 (g x) = g_pos x"
      show "g x = g_pos x - g_neg x" unfolding g[symmetric]
        by (cases "g x") (auto split: split_max)
    qed
  qed auto
qed

end

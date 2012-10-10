(*  Title:      HOL/Probability/Independent_Family.thy
    Author:     Johannes Hölzl, TU München
*)

header {* Independent families of events, event sets, and random variables *}

theory Independent_Family
  imports Probability_Measure Infinite_Product_Measure
begin

lemma INT_decseq_offset:
  assumes "decseq F"
  shows "(\<Inter>i. F i) = (\<Inter>i\<in>{n..}. F i)"
proof safe
  fix x i assume x: "x \<in> (\<Inter>i\<in>{n..}. F i)"
  show "x \<in> F i"
  proof cases
    from x have "x \<in> F n" by auto
    also assume "i \<le> n" with `decseq F` have "F n \<subseteq> F i"
      unfolding decseq_def by simp
    finally show ?thesis .
  qed (insert x, simp)
qed auto

definition (in prob_space)
  "indep_sets F I \<longleftrightarrow> (\<forall>i\<in>I. F i \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> (\<forall>A\<in>Pi J F. prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))))"

definition (in prob_space)
  "indep_set A B \<longleftrightarrow> indep_sets (bool_case A B) UNIV"

definition (in prob_space)
  indep_events_def_alt: "indep_events A I \<longleftrightarrow> indep_sets (\<lambda>i. {A i}) I"

lemma image_subset_iff_funcset: "F ` A \<subseteq> B \<longleftrightarrow> F \<in> A \<rightarrow> B"
  by auto

lemma (in prob_space) indep_events_def:
  "indep_events A I \<longleftrightarrow> (A`I \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j)))"
  unfolding indep_events_def_alt indep_sets_def
  apply (simp add: Ball_def Pi_iff image_subset_iff_funcset)
  apply (intro conj_cong refl arg_cong[where f=All] ext imp_cong)
  apply auto
  done

definition (in prob_space)
  "indep_event A B \<longleftrightarrow> indep_events (bool_case A B) UNIV"

lemma (in prob_space) indep_sets_cong:
  "I = J \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> F i = G i) \<Longrightarrow> indep_sets F I \<longleftrightarrow> indep_sets G J"
  by (simp add: indep_sets_def, intro conj_cong all_cong imp_cong ball_cong) blast+

lemma (in prob_space) indep_events_finite_index_events:
  "indep_events F I \<longleftrightarrow> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_events F J)"
  by (auto simp: indep_events_def)

lemma (in prob_space) indep_sets_finite_index_sets:
  "indep_sets F I \<longleftrightarrow> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_sets F J)"
proof (intro iffI allI impI)
  assume *: "\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_sets F J"
  show "indep_sets F I" unfolding indep_sets_def
  proof (intro conjI ballI allI impI)
    fix i assume "i \<in> I"
    with *[THEN spec, of "{i}"] show "F i \<subseteq> events"
      by (auto simp: indep_sets_def)
  qed (insert *, auto simp: indep_sets_def)
qed (auto simp: indep_sets_def)

lemma (in prob_space) indep_sets_mono_index:
  "J \<subseteq> I \<Longrightarrow> indep_sets F I \<Longrightarrow> indep_sets F J"
  unfolding indep_sets_def by auto

lemma (in prob_space) indep_sets_mono_sets:
  assumes indep: "indep_sets F I"
  assumes mono: "\<And>i. i\<in>I \<Longrightarrow> G i \<subseteq> F i"
  shows "indep_sets G I"
proof -
  have "(\<forall>i\<in>I. F i \<subseteq> events) \<Longrightarrow> (\<forall>i\<in>I. G i \<subseteq> events)"
    using mono by auto
  moreover have "\<And>A J. J \<subseteq> I \<Longrightarrow> A \<in> (\<Pi> j\<in>J. G j) \<Longrightarrow> A \<in> (\<Pi> j\<in>J. F j)"
    using mono by (auto simp: Pi_iff)
  ultimately show ?thesis
    using indep by (auto simp: indep_sets_def)
qed

lemma (in prob_space) indep_sets_mono:
  assumes indep: "indep_sets F I"
  assumes mono: "J \<subseteq> I" "\<And>i. i\<in>J \<Longrightarrow> G i \<subseteq> F i"
  shows "indep_sets G J"
  apply (rule indep_sets_mono_sets)
  apply (rule indep_sets_mono_index)
  apply (fact +)
  done

lemma (in prob_space) indep_setsI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> events"
    and "\<And>A J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> (\<forall>j\<in>J. A j \<in> F j) \<Longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  shows "indep_sets F I"
  using assms unfolding indep_sets_def by (auto simp: Pi_iff)

lemma (in prob_space) indep_setsD:
  assumes "indep_sets F I" and "J \<subseteq> I" "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> F j"
  shows "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  using assms unfolding indep_sets_def by auto

lemma (in prob_space) indep_setI:
  assumes ev: "A \<subseteq> events" "B \<subseteq> events"
    and indep: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> prob (a \<inter> b) = prob a * prob b"
  shows "indep_set A B"
  unfolding indep_set_def
proof (rule indep_setsI)
  fix F J assume "J \<noteq> {}" "J \<subseteq> UNIV"
    and F: "\<forall>j\<in>J. F j \<in> (case j of True \<Rightarrow> A | False \<Rightarrow> B)"
  have "J \<in> Pow UNIV" by auto
  with F `J \<noteq> {}` indep[of "F True" "F False"]
  show "prob (\<Inter>j\<in>J. F j) = (\<Prod>j\<in>J. prob (F j))"
    unfolding UNIV_bool Pow_insert by (auto simp: ac_simps)
qed (auto split: bool.split simp: ev)

lemma (in prob_space) indep_setD:
  assumes indep: "indep_set A B" and ev: "a \<in> A" "b \<in> B"
  shows "prob (a \<inter> b) = prob a * prob b"
  using indep[unfolded indep_set_def, THEN indep_setsD, of UNIV "bool_case a b"] ev
  by (simp add: ac_simps UNIV_bool)

lemma (in prob_space)
  assumes indep: "indep_set A B"
  shows indep_setD_ev1: "A \<subseteq> events"
    and indep_setD_ev2: "B \<subseteq> events"
  using indep unfolding indep_set_def indep_sets_def UNIV_bool by auto

lemma (in prob_space) indep_sets_dynkin:
  assumes indep: "indep_sets F I"
  shows "indep_sets (\<lambda>i. dynkin (space M) (F i)) I"
    (is "indep_sets ?F I")
proof (subst indep_sets_finite_index_sets, intro allI impI ballI)
  fix J assume "finite J" "J \<subseteq> I" "J \<noteq> {}"
  with indep have "indep_sets F J"
    by (subst (asm) indep_sets_finite_index_sets) auto
  { fix J K assume "indep_sets F K"
    let ?G = "\<lambda>S i. if i \<in> S then ?F i else F i"
    assume "finite J" "J \<subseteq> K"
    then have "indep_sets (?G J) K"
    proof induct
      case (insert j J)
      moreover def G \<equiv> "?G J"
      ultimately have G: "indep_sets G K" "\<And>i. i \<in> K \<Longrightarrow> G i \<subseteq> events" and "j \<in> K"
        by (auto simp: indep_sets_def)
      let ?D = "{E\<in>events. indep_sets (G(j := {E})) K }"
      { fix X assume X: "X \<in> events"
        assume indep: "\<And>J A. J \<noteq> {} \<Longrightarrow> J \<subseteq> K \<Longrightarrow> finite J \<Longrightarrow> j \<notin> J \<Longrightarrow> (\<forall>i\<in>J. A i \<in> G i)
          \<Longrightarrow> prob ((\<Inter>i\<in>J. A i) \<inter> X) = prob X * (\<Prod>i\<in>J. prob (A i))"
        have "indep_sets (G(j := {X})) K"
        proof (rule indep_setsI)
          fix i assume "i \<in> K" then show "(G(j:={X})) i \<subseteq> events"
            using G X by auto
        next
          fix A J assume J: "J \<noteq> {}" "J \<subseteq> K" "finite J" "\<forall>i\<in>J. A i \<in> (G(j := {X})) i"
          show "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
          proof cases
            assume "j \<in> J"
            with J have "A j = X" by auto
            show ?thesis
            proof cases
              assume "J = {j}" then show ?thesis by simp
            next
              assume "J \<noteq> {j}"
              have "prob (\<Inter>i\<in>J. A i) = prob ((\<Inter>i\<in>J-{j}. A i) \<inter> X)"
                using `j \<in> J` `A j = X` by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
              also have "\<dots> = prob X * (\<Prod>i\<in>J-{j}. prob (A i))"
              proof (rule indep)
                show "J - {j} \<noteq> {}" "J - {j} \<subseteq> K" "finite (J - {j})" "j \<notin> J - {j}"
                  using J `J \<noteq> {j}` `j \<in> J` by auto
                show "\<forall>i\<in>J - {j}. A i \<in> G i"
                  using J by auto
              qed
              also have "\<dots> = prob (A j) * (\<Prod>i\<in>J-{j}. prob (A i))"
                using `A j = X` by simp
              also have "\<dots> = (\<Prod>i\<in>J. prob (A i))"
                unfolding setprod.insert_remove[OF `finite J`, symmetric, of "\<lambda>i. prob  (A i)"]
                using `j \<in> J` by (simp add: insert_absorb)
              finally show ?thesis .
            qed
          next
            assume "j \<notin> J"
            with J have "\<forall>i\<in>J. A i \<in> G i" by (auto split: split_if_asm)
            with J show ?thesis
              by (intro indep_setsD[OF G(1)]) auto
          qed
        qed }
      note indep_sets_insert = this
      have "dynkin_system (space M) ?D"
      proof (rule dynkin_systemI', simp_all cong del: indep_sets_cong, safe)
        show "indep_sets (G(j := {{}})) K"
          by (rule indep_sets_insert) auto
      next
        fix X assume X: "X \<in> events" and G': "indep_sets (G(j := {X})) K"
        show "indep_sets (G(j := {space M - X})) K"
        proof (rule indep_sets_insert)
          fix J A assume J: "J \<noteq> {}" "J \<subseteq> K" "finite J" "j \<notin> J" and A: "\<forall>i\<in>J. A i \<in> G i"
          then have A_sets: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> events"
            using G by auto
          have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) =
              prob ((\<Inter>j\<in>J. A j) - (\<Inter>i\<in>insert j J. (A(j := X)) i))"
            using A_sets sets_into_space[of _ M] X `J \<noteq> {}`
            by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
          also have "\<dots> = prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)"
            using J `J \<noteq> {}` `j \<notin> J` A_sets X sets_into_space
            by (auto intro!: finite_measure_Diff finite_INT split: split_if_asm)
          finally have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) =
              prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)" .
          moreover {
            have "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
              using J A `finite J` by (intro indep_setsD[OF G(1)]) auto
            then have "prob (\<Inter>j\<in>J. A j) = prob (space M) * (\<Prod>i\<in>J. prob (A i))"
              using prob_space by simp }
          moreover {
            have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = (\<Prod>i\<in>insert j J. prob ((A(j := X)) i))"
              using J A `j \<in> K` by (intro indep_setsD[OF G']) auto
            then have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = prob X * (\<Prod>i\<in>J. prob (A i))"
              using `finite J` `j \<notin> J` by (auto intro!: setprod_cong) }
          ultimately have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) = (prob (space M) - prob X) * (\<Prod>i\<in>J. prob (A i))"
            by (simp add: field_simps)
          also have "\<dots> = prob (space M - X) * (\<Prod>i\<in>J. prob (A i))"
            using X A by (simp add: finite_measure_compl)
          finally show "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) = prob (space M - X) * (\<Prod>i\<in>J. prob (A i))" .
        qed (insert X, auto)
      next
        fix F :: "nat \<Rightarrow> 'a set" assume disj: "disjoint_family F" and "range F \<subseteq> ?D"
        then have F: "\<And>i. F i \<in> events" "\<And>i. indep_sets (G(j:={F i})) K" by auto
        show "indep_sets (G(j := {\<Union>k. F k})) K"
        proof (rule indep_sets_insert)
          fix J A assume J: "j \<notin> J" "J \<noteq> {}" "J \<subseteq> K" "finite J" and A: "\<forall>i\<in>J. A i \<in> G i"
          then have A_sets: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> events"
            using G by auto
          have "prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)) = prob (\<Union>k. (\<Inter>i\<in>insert j J. (A(j := F k)) i))"
            using `J \<noteq> {}` `j \<notin> J` `j \<in> K` by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
          moreover have "(\<lambda>k. prob (\<Inter>i\<in>insert j J. (A(j := F k)) i)) sums prob (\<Union>k. (\<Inter>i\<in>insert j J. (A(j := F k)) i))"
          proof (rule finite_measure_UNION)
            show "disjoint_family (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i)"
              using disj by (rule disjoint_family_on_bisimulation) auto
            show "range (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i) \<subseteq> events"
              using A_sets F `finite J` `J \<noteq> {}` `j \<notin> J` by (auto intro!: Int)
          qed
          moreover { fix k
            from J A `j \<in> K` have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * (\<Prod>i\<in>J. prob (A i))"
              by (subst indep_setsD[OF F(2)]) (auto intro!: setprod_cong split: split_if_asm)
            also have "\<dots> = prob (F k) * prob (\<Inter>i\<in>J. A i)"
              using J A `j \<in> K` by (subst indep_setsD[OF G(1)]) auto
            finally have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * prob (\<Inter>i\<in>J. A i)" . }
          ultimately have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)))"
            by simp
          moreover
          have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * prob (\<Inter>i\<in>J. A i))"
            using disj F(1) by (intro finite_measure_UNION sums_mult2) auto
          then have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * (\<Prod>i\<in>J. prob (A i)))"
            using J A `j \<in> K` by (subst indep_setsD[OF G(1), symmetric]) auto
          ultimately
          show "prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)) = prob (\<Union>k. F k) * (\<Prod>j\<in>J. prob (A j))"
            by (auto dest!: sums_unique)
        qed (insert F, auto)
      qed (insert sets_into_space, auto)
      then have mono: "dynkin (space M) (G j) \<subseteq> {E \<in> events. indep_sets (G(j := {E})) K}"
      proof (rule dynkin_system.dynkin_subset, safe)
        fix X assume "X \<in> G j"
        then show "X \<in> events" using G `j \<in> K` by auto
        from `indep_sets G K`
        show "indep_sets (G(j := {X})) K"
          by (rule indep_sets_mono_sets) (insert `X \<in> G j`, auto)
      qed
      have "indep_sets (G(j:=?D)) K"
      proof (rule indep_setsI)
        fix i assume "i \<in> K" then show "(G(j := ?D)) i \<subseteq> events"
          using G(2) by auto
      next
        fix A J assume J: "J\<noteq>{}" "J \<subseteq> K" "finite J" and A: "\<forall>i\<in>J. A i \<in> (G(j := ?D)) i"
        show "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
        proof cases
          assume "j \<in> J"
          with A have indep: "indep_sets (G(j := {A j})) K" by auto
          from J A show ?thesis
            by (intro indep_setsD[OF indep]) auto
        next
          assume "j \<notin> J"
          with J A have "\<forall>i\<in>J. A i \<in> G i" by (auto split: split_if_asm)
          with J show ?thesis
            by (intro indep_setsD[OF G(1)]) auto
        qed
      qed
      then have "indep_sets (G(j := dynkin (space M) (G j))) K"
        by (rule indep_sets_mono_sets) (insert mono, auto)
      then show ?case
        by (rule indep_sets_mono_sets) (insert `j \<in> K` `j \<notin> J`, auto simp: G_def)
    qed (insert `indep_sets F K`, simp) }
  from this[OF `indep_sets F J` `finite J` subset_refl]
  show "indep_sets ?F J"
    by (rule indep_sets_mono_sets) auto
qed

lemma (in prob_space) indep_sets_sigma:
  assumes indep: "indep_sets F I"
  assumes stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  shows "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I"
proof -
  from indep_sets_dynkin[OF indep]
  show ?thesis
  proof (rule indep_sets_mono_sets, subst sigma_eq_dynkin, simp_all add: stable)
    fix i assume "i \<in> I"
    with indep have "F i \<subseteq> events" by (auto simp: indep_sets_def)
    with sets_into_space show "F i \<subseteq> Pow (space M)" by auto
  qed
qed

lemma (in prob_space) indep_sets_sigma_sets_iff:
  assumes "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  shows "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I \<longleftrightarrow> indep_sets F I"
proof
  assume "indep_sets F I" then show "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I"
    by (rule indep_sets_sigma) fact
next
  assume "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I" then show "indep_sets F I"
    by (rule indep_sets_mono_sets) (intro subsetI sigma_sets.Basic)
qed

definition (in prob_space)
  indep_vars_def2: "indep_vars M' X I \<longleftrightarrow>
    (\<forall>i\<in>I. random_variable (M' i) (X i)) \<and>
    indep_sets (\<lambda>i. { X i -` A \<inter> space M | A. A \<in> sets (M' i)}) I"

definition (in prob_space)
  "indep_var Ma A Mb B \<longleftrightarrow> indep_vars (bool_case Ma Mb) (bool_case A B) UNIV"

lemma (in prob_space) indep_vars_def:
  "indep_vars M' X I \<longleftrightarrow>
    (\<forall>i\<in>I. random_variable (M' i) (X i)) \<and>
    indep_sets (\<lambda>i. sigma_sets (space M) { X i -` A \<inter> space M | A. A \<in> sets (M' i)}) I"
  unfolding indep_vars_def2
  apply (rule conj_cong[OF refl])
  apply (rule indep_sets_sigma_sets_iff[symmetric])
  apply (auto simp: Int_stable_def)
  apply (rule_tac x="A \<inter> Aa" in exI)
  apply auto
  done

lemma (in prob_space) indep_var_eq:
  "indep_var S X T Y \<longleftrightarrow>
    (random_variable S X \<and> random_variable T Y) \<and>
    indep_set
      (sigma_sets (space M) { X -` A \<inter> space M | A. A \<in> sets S})
      (sigma_sets (space M) { Y -` A \<inter> space M | A. A \<in> sets T})"
  unfolding indep_var_def indep_vars_def indep_set_def UNIV_bool
  by (intro arg_cong2[where f="op \<and>"] arg_cong2[where f=indep_sets] ext)
     (auto split: bool.split)

lemma (in prob_space) indep_sets2_eq:
  "indep_set A B \<longleftrightarrow> A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  unfolding indep_set_def
proof (intro iffI ballI conjI)
  assume indep: "indep_sets (bool_case A B) UNIV"
  { fix a b assume "a \<in> A" "b \<in> B"
    with indep_setsD[OF indep, of UNIV "bool_case a b"]
    show "prob (a \<inter> b) = prob a * prob b"
      unfolding UNIV_bool by (simp add: ac_simps) }
  from indep show "A \<subseteq> events" "B \<subseteq> events"
    unfolding indep_sets_def UNIV_bool by auto
next
  assume *: "A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  show "indep_sets (bool_case A B) UNIV"
  proof (rule indep_setsI)
    fix i show "(case i of True \<Rightarrow> A | False \<Rightarrow> B) \<subseteq> events"
      using * by (auto split: bool.split)
  next
    fix J X assume "J \<noteq> {}" "J \<subseteq> UNIV" and X: "\<forall>j\<in>J. X j \<in> (case j of True \<Rightarrow> A | False \<Rightarrow> B)"
    then have "J = {True} \<or> J = {False} \<or> J = {True,False}"
      by (auto simp: UNIV_bool)
    then show "prob (\<Inter>j\<in>J. X j) = (\<Prod>j\<in>J. prob (X j))"
      using X * by auto
  qed
qed

lemma (in prob_space) indep_set_sigma_sets:
  assumes "indep_set A B"
  assumes A: "Int_stable A" and B: "Int_stable B"
  shows "indep_set (sigma_sets (space M) A) (sigma_sets (space M) B)"
proof -
  have "indep_sets (\<lambda>i. sigma_sets (space M) (case i of True \<Rightarrow> A | False \<Rightarrow> B)) UNIV"
  proof (rule indep_sets_sigma)
    show "indep_sets (bool_case A B) UNIV"
      by (rule `indep_set A B`[unfolded indep_set_def])
    fix i show "Int_stable (case i of True \<Rightarrow> A | False \<Rightarrow> B)"
      using A B by (cases i) auto
  qed
  then show ?thesis
    unfolding indep_set_def
    by (rule indep_sets_mono_sets) (auto split: bool.split)
qed

lemma (in prob_space) indep_sets_collect_sigma:
  fixes I :: "'j \<Rightarrow> 'i set" and J :: "'j set" and E :: "'i \<Rightarrow> 'a set set"
  assumes indep: "indep_sets E (\<Union>j\<in>J. I j)"
  assumes Int_stable: "\<And>i j. j \<in> J \<Longrightarrow> i \<in> I j \<Longrightarrow> Int_stable (E i)"
  assumes disjoint: "disjoint_family_on I J"
  shows "indep_sets (\<lambda>j. sigma_sets (space M) (\<Union>i\<in>I j. E i)) J"
proof -
  let ?E = "\<lambda>j. {\<Inter>k\<in>K. E' k| E' K. finite K \<and> K \<noteq> {} \<and> K \<subseteq> I j \<and> (\<forall>k\<in>K. E' k \<in> E k) }"

  from indep have E: "\<And>j i. j \<in> J \<Longrightarrow> i \<in> I j \<Longrightarrow> E i \<subseteq> events"
    unfolding indep_sets_def by auto
  { fix j
    let ?S = "sigma_sets (space M) (\<Union>i\<in>I j. E i)"
    assume "j \<in> J"
    from E[OF this] interpret S: sigma_algebra "space M" ?S
      using sets_into_space[of _ M] by (intro sigma_algebra_sigma_sets) auto

    have "sigma_sets (space M) (\<Union>i\<in>I j. E i) = sigma_sets (space M) (?E j)"
    proof (rule sigma_sets_eqI)
      fix A assume "A \<in> (\<Union>i\<in>I j. E i)"
      then guess i ..
      then show "A \<in> sigma_sets (space M) (?E j)"
        by (auto intro!: sigma_sets.intros(2-) exI[of _ "{i}"] exI[of _ "\<lambda>i. A"])
    next
      fix A assume "A \<in> ?E j"
      then obtain E' K where "finite K" "K \<noteq> {}" "K \<subseteq> I j" "\<And>k. k \<in> K \<Longrightarrow> E' k \<in> E k"
        and A: "A = (\<Inter>k\<in>K. E' k)"
        by auto
      then have "A \<in> ?S" unfolding A
        by (safe intro!: S.finite_INT) auto
      then show "A \<in> sigma_sets (space M) (\<Union>i\<in>I j. E i)"
        by simp
    qed }
  moreover have "indep_sets (\<lambda>j. sigma_sets (space M) (?E j)) J"
  proof (rule indep_sets_sigma)
    show "indep_sets ?E J"
    proof (intro indep_setsI)
      fix j assume "j \<in> J" with E show "?E j \<subseteq> events" by (force  intro!: finite_INT)
    next
      fix K A assume K: "K \<noteq> {}" "K \<subseteq> J" "finite K"
        and "\<forall>j\<in>K. A j \<in> ?E j"
      then have "\<forall>j\<in>K. \<exists>E' L. A j = (\<Inter>l\<in>L. E' l) \<and> finite L \<and> L \<noteq> {} \<and> L \<subseteq> I j \<and> (\<forall>l\<in>L. E' l \<in> E l)"
        by simp
      from bchoice[OF this] guess E' ..
      from bchoice[OF this] obtain L
        where A: "\<And>j. j\<in>K \<Longrightarrow> A j = (\<Inter>l\<in>L j. E' j l)"
        and L: "\<And>j. j\<in>K \<Longrightarrow> finite (L j)" "\<And>j. j\<in>K \<Longrightarrow> L j \<noteq> {}" "\<And>j. j\<in>K \<Longrightarrow> L j \<subseteq> I j"
        and E': "\<And>j l. j\<in>K \<Longrightarrow> l \<in> L j \<Longrightarrow> E' j l \<in> E l"
        by auto

      { fix k l j assume "k \<in> K" "j \<in> K" "l \<in> L j" "l \<in> L k"
        have "k = j"
        proof (rule ccontr)
          assume "k \<noteq> j"
          with disjoint `K \<subseteq> J` `k \<in> K` `j \<in> K` have "I k \<inter> I j = {}"
            unfolding disjoint_family_on_def by auto
          with L(2,3)[OF `j \<in> K`] L(2,3)[OF `k \<in> K`]
          show False using `l \<in> L k` `l \<in> L j` by auto
        qed }
      note L_inj = this

      def k \<equiv> "\<lambda>l. (SOME k. k \<in> K \<and> l \<in> L k)"
      { fix x j l assume *: "j \<in> K" "l \<in> L j"
        have "k l = j" unfolding k_def
        proof (rule some_equality)
          fix k assume "k \<in> K \<and> l \<in> L k"
          with * L_inj show "k = j" by auto
        qed (insert *, simp) }
      note k_simp[simp] = this
      let ?E' = "\<lambda>l. E' (k l) l"
      have "prob (\<Inter>j\<in>K. A j) = prob (\<Inter>l\<in>(\<Union>k\<in>K. L k). ?E' l)"
        by (auto simp: A intro!: arg_cong[where f=prob])
      also have "\<dots> = (\<Prod>l\<in>(\<Union>k\<in>K. L k). prob (?E' l))"
        using L K E' by (intro indep_setsD[OF indep]) (simp_all add: UN_mono)
      also have "\<dots> = (\<Prod>j\<in>K. \<Prod>l\<in>L j. prob (E' j l))"
        using K L L_inj by (subst setprod_UN_disjoint) auto
      also have "\<dots> = (\<Prod>j\<in>K. prob (A j))"
        using K L E' by (auto simp add: A intro!: setprod_cong indep_setsD[OF indep, symmetric]) blast
      finally show "prob (\<Inter>j\<in>K. A j) = (\<Prod>j\<in>K. prob (A j))" .
    qed
  next
    fix j assume "j \<in> J"
    show "Int_stable (?E j)"
    proof (rule Int_stableI)
      fix a assume "a \<in> ?E j" then obtain Ka Ea
        where a: "a = (\<Inter>k\<in>Ka. Ea k)" "finite Ka" "Ka \<noteq> {}" "Ka \<subseteq> I j" "\<And>k. k\<in>Ka \<Longrightarrow> Ea k \<in> E k" by auto
      fix b assume "b \<in> ?E j" then obtain Kb Eb
        where b: "b = (\<Inter>k\<in>Kb. Eb k)" "finite Kb" "Kb \<noteq> {}" "Kb \<subseteq> I j" "\<And>k. k\<in>Kb \<Longrightarrow> Eb k \<in> E k" by auto
      let ?A = "\<lambda>k. (if k \<in> Ka \<inter> Kb then Ea k \<inter> Eb k else if k \<in> Kb then Eb k else if k \<in> Ka then Ea k else {})"
      have "a \<inter> b = INTER (Ka \<union> Kb) ?A"
        by (simp add: a b set_eq_iff) auto
      with a b `j \<in> J` Int_stableD[OF Int_stable] show "a \<inter> b \<in> ?E j"
        by (intro CollectI exI[of _ "Ka \<union> Kb"] exI[of _ ?A]) auto
    qed
  qed
  ultimately show ?thesis
    by (simp cong: indep_sets_cong)
qed

definition (in prob_space) tail_events where
  "tail_events A = (\<Inter>n. sigma_sets (space M) (UNION {n..} A))"

lemma (in prob_space) tail_events_sets:
  assumes A: "\<And>i::nat. A i \<subseteq> events"
  shows "tail_events A \<subseteq> events"
proof
  fix X assume X: "X \<in> tail_events A"
  let ?A = "(\<Inter>n. sigma_sets (space M) (UNION {n..} A))"
  from X have "\<And>n::nat. X \<in> sigma_sets (space M) (UNION {n..} A)" by (auto simp: tail_events_def)
  from this[of 0] have "X \<in> sigma_sets (space M) (UNION UNIV A)" by simp
  then show "X \<in> events"
    by induct (insert A, auto)
qed

lemma (in prob_space) sigma_algebra_tail_events:
  assumes "\<And>i::nat. sigma_algebra (space M) (A i)"
  shows "sigma_algebra (space M) (tail_events A)"
  unfolding tail_events_def
proof (simp add: sigma_algebra_iff2, safe)
  let ?A = "(\<Inter>n. sigma_sets (space M) (UNION {n..} A))"
  interpret A: sigma_algebra "space M" "A i" for i by fact
  { fix X x assume "X \<in> ?A" "x \<in> X"
    then have "\<And>n. X \<in> sigma_sets (space M) (UNION {n..} A)" by auto
    from this[of 0] have "X \<in> sigma_sets (space M) (UNION UNIV A)" by simp
    then have "X \<subseteq> space M"
      by induct (insert A.sets_into_space, auto)
    with `x \<in> X` show "x \<in> space M" by auto }
  { fix F :: "nat \<Rightarrow> 'a set" and n assume "range F \<subseteq> ?A"
    then show "(UNION UNIV F) \<in> sigma_sets (space M) (UNION {n..} A)"
      by (intro sigma_sets.Union) auto }
qed (auto intro!: sigma_sets.Compl sigma_sets.Empty)

lemma (in prob_space) kolmogorov_0_1_law:
  fixes A :: "nat \<Rightarrow> 'a set set"
  assumes "\<And>i::nat. sigma_algebra (space M) (A i)"
  assumes indep: "indep_sets A UNIV"
  and X: "X \<in> tail_events A"
  shows "prob X = 0 \<or> prob X = 1"
proof -
  have A: "\<And>i. A i \<subseteq> events"
    using indep unfolding indep_sets_def by simp

  let ?D = "{D \<in> events. prob (X \<inter> D) = prob X * prob D}"
  interpret A: sigma_algebra "space M" "A i" for i by fact
  interpret T: sigma_algebra "space M" "tail_events A"
    by (rule sigma_algebra_tail_events) fact
  have "X \<subseteq> space M" using T.space_closed X by auto

  have X_in: "X \<in> events"
    using tail_events_sets A X by auto

  interpret D: dynkin_system "space M" ?D
  proof (rule dynkin_systemI)
    fix D assume "D \<in> ?D" then show "D \<subseteq> space M"
      using sets_into_space by auto
  next
    show "space M \<in> ?D"
      using prob_space `X \<subseteq> space M` by (simp add: Int_absorb2)
  next
    fix A assume A: "A \<in> ?D"
    have "prob (X \<inter> (space M - A)) = prob (X - (X \<inter> A))"
      using `X \<subseteq> space M` by (auto intro!: arg_cong[where f=prob])
    also have "\<dots> = prob X - prob (X \<inter> A)"
      using X_in A by (intro finite_measure_Diff) auto
    also have "\<dots> = prob X * prob (space M) - prob X * prob A"
      using A prob_space by auto
    also have "\<dots> = prob X * prob (space M - A)"
      using X_in A sets_into_space
      by (subst finite_measure_Diff) (auto simp: field_simps)
    finally show "space M - A \<in> ?D"
      using A `X \<subseteq> space M` by auto
  next
    fix F :: "nat \<Rightarrow> 'a set" assume dis: "disjoint_family F" and "range F \<subseteq> ?D"
    then have F: "range F \<subseteq> events" "\<And>i. prob (X \<inter> F i) = prob X * prob (F i)"
      by auto
    have "(\<lambda>i. prob (X \<inter> F i)) sums prob (\<Union>i. X \<inter> F i)"
    proof (rule finite_measure_UNION)
      show "range (\<lambda>i. X \<inter> F i) \<subseteq> events"
        using F X_in by auto
      show "disjoint_family (\<lambda>i. X \<inter> F i)"
        using dis by (rule disjoint_family_on_bisimulation) auto
    qed
    with F have "(\<lambda>i. prob X * prob (F i)) sums prob (X \<inter> (\<Union>i. F i))"
      by simp
    moreover have "(\<lambda>i. prob X * prob (F i)) sums (prob X * prob (\<Union>i. F i))"
      by (intro sums_mult finite_measure_UNION F dis)
    ultimately have "prob (X \<inter> (\<Union>i. F i)) = prob X * prob (\<Union>i. F i)"
      by (auto dest!: sums_unique)
    with F show "(\<Union>i. F i) \<in> ?D"
      by auto
  qed

  { fix n
    have "indep_sets (\<lambda>b. sigma_sets (space M) (\<Union>m\<in>bool_case {..n} {Suc n..} b. A m)) UNIV"
    proof (rule indep_sets_collect_sigma)
      have *: "(\<Union>b. case b of True \<Rightarrow> {..n} | False \<Rightarrow> {Suc n..}) = UNIV" (is "?U = _")
        by (simp split: bool.split add: set_eq_iff) (metis not_less_eq_eq)
      with indep show "indep_sets A ?U" by simp
      show "disjoint_family (bool_case {..n} {Suc n..})"
        unfolding disjoint_family_on_def by (auto split: bool.split)
      fix m
      show "Int_stable (A m)"
        unfolding Int_stable_def using A.Int by auto
    qed
    also have "(\<lambda>b. sigma_sets (space M) (\<Union>m\<in>bool_case {..n} {Suc n..} b. A m)) =
      bool_case (sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) (sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m))"
      by (auto intro!: ext split: bool.split)
    finally have indep: "indep_set (sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) (sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m))"
      unfolding indep_set_def by simp

    have "sigma_sets (space M) (\<Union>m\<in>{..n}. A m) \<subseteq> ?D"
    proof (simp add: subset_eq, rule)
      fix D assume D: "D \<in> sigma_sets (space M) (\<Union>m\<in>{..n}. A m)"
      have "X \<in> sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m)"
        using X unfolding tail_events_def by simp
      from indep_setD[OF indep D this] indep_setD_ev1[OF indep] D
      show "D \<in> events \<and> prob (X \<inter> D) = prob X * prob D"
        by (auto simp add: ac_simps)
    qed }
  then have "(\<Union>n. sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) \<subseteq> ?D" (is "?A \<subseteq> _")
    by auto

  note `X \<in> tail_events A`
  also {
    have "\<And>n. sigma_sets (space M) (\<Union>i\<in>{n..}. A i) \<subseteq> sigma_sets (space M) ?A"
      by (intro sigma_sets_subseteq UN_mono) auto
   then have "tail_events A \<subseteq> sigma_sets (space M) ?A"
      unfolding tail_events_def by auto }
  also have "sigma_sets (space M) ?A = dynkin (space M) ?A"
  proof (rule sigma_eq_dynkin)
    { fix B n assume "B \<in> sigma_sets (space M) (\<Union>m\<in>{..n}. A m)"
      then have "B \<subseteq> space M"
        by induct (insert A sets_into_space[of _ M], auto) }
    then show "?A \<subseteq> Pow (space M)" by auto
    show "Int_stable ?A"
    proof (rule Int_stableI)
      fix a assume "a \<in> ?A" then guess n .. note a = this
      fix b assume "b \<in> ?A" then guess m .. note b = this
      interpret Amn: sigma_algebra "space M" "sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        using A sets_into_space[of _ M] by (intro sigma_algebra_sigma_sets) auto
      have "sigma_sets (space M) (\<Union>i\<in>{..n}. A i) \<subseteq> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        by (intro sigma_sets_subseteq UN_mono) auto
      with a have "a \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)" by auto
      moreover
      have "sigma_sets (space M) (\<Union>i\<in>{..m}. A i) \<subseteq> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        by (intro sigma_sets_subseteq UN_mono) auto
      with b have "b \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)" by auto
      ultimately have "a \<inter> b \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        using Amn.Int[of a b] by simp
      then show "a \<inter> b \<in> (\<Union>n. sigma_sets (space M) (\<Union>i\<in>{..n}. A i))" by auto
    qed
  qed
  also have "dynkin (space M) ?A \<subseteq> ?D"
    using `?A \<subseteq> ?D` by (auto intro!: D.dynkin_subset)
  finally show ?thesis by auto
qed

lemma (in prob_space) borel_0_1_law:
  fixes F :: "nat \<Rightarrow> 'a set"
  assumes F2: "indep_events F UNIV"
  shows "prob (\<Inter>n. \<Union>m\<in>{n..}. F m) = 0 \<or> prob (\<Inter>n. \<Union>m\<in>{n..}. F m) = 1"
proof (rule kolmogorov_0_1_law[of "\<lambda>i. sigma_sets (space M) { F i }"])
  have F1: "range F \<subseteq> events"
    using F2 by (simp add: indep_events_def subset_eq)
  { fix i show "sigma_algebra (space M) (sigma_sets (space M) {F i})"
      using sigma_algebra_sigma_sets[of "{F i}" "space M"] F1 sets_into_space
      by auto }
  show "indep_sets (\<lambda>i. sigma_sets (space M) {F i}) UNIV"
  proof (rule indep_sets_sigma)
    show "indep_sets (\<lambda>i. {F i}) UNIV"
      unfolding indep_events_def_alt[symmetric] by fact
    fix i show "Int_stable {F i}"
      unfolding Int_stable_def by simp
  qed
  let ?Q = "\<lambda>n. \<Union>i\<in>{n..}. F i"
  show "(\<Inter>n. \<Union>m\<in>{n..}. F m) \<in> tail_events (\<lambda>i. sigma_sets (space M) {F i})"
    unfolding tail_events_def
  proof
    fix j
    interpret S: sigma_algebra "space M" "sigma_sets (space M) (\<Union>i\<in>{j..}. sigma_sets (space M) {F i})"
      using order_trans[OF F1 space_closed]
      by (intro sigma_algebra_sigma_sets) (simp add: sigma_sets_singleton subset_eq)
    have "(\<Inter>n. ?Q n) = (\<Inter>n\<in>{j..}. ?Q n)"
      by (intro decseq_SucI INT_decseq_offset UN_mono) auto
    also have "\<dots> \<in> sigma_sets (space M) (\<Union>i\<in>{j..}. sigma_sets (space M) {F i})"
      using order_trans[OF F1 space_closed]
      by (safe intro!: S.countable_INT S.countable_UN)
         (auto simp: sigma_sets_singleton intro!: sigma_sets.Basic bexI)
    finally show "(\<Inter>n. ?Q n) \<in> sigma_sets (space M) (\<Union>i\<in>{j..}. sigma_sets (space M) {F i})"
      by simp
  qed
qed

lemma (in prob_space) indep_sets_finite:
  assumes I: "I \<noteq> {}" "finite I"
    and F: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> events" "\<And>i. i \<in> I \<Longrightarrow> space M \<in> F i"
  shows "indep_sets F I \<longleftrightarrow> (\<forall>A\<in>Pi I F. prob (\<Inter>j\<in>I. A j) = (\<Prod>j\<in>I. prob (A j)))"
proof
  assume *: "indep_sets F I"
  from I show "\<forall>A\<in>Pi I F. prob (\<Inter>j\<in>I. A j) = (\<Prod>j\<in>I. prob (A j))"
    by (intro indep_setsD[OF *] ballI) auto
next
  assume indep: "\<forall>A\<in>Pi I F. prob (\<Inter>j\<in>I. A j) = (\<Prod>j\<in>I. prob (A j))"
  show "indep_sets F I"
  proof (rule indep_setsI[OF F(1)])
    fix A J assume J: "J \<noteq> {}" "J \<subseteq> I" "finite J"
    assume A: "\<forall>j\<in>J. A j \<in> F j"
    let ?A = "\<lambda>j. if j \<in> J then A j else space M"
    have "prob (\<Inter>j\<in>I. ?A j) = prob (\<Inter>j\<in>J. A j)"
      using subset_trans[OF F(1) space_closed] J A
      by (auto intro!: arg_cong[where f=prob] split: split_if_asm) blast
    also
    from A F have "(\<lambda>j. if j \<in> J then A j else space M) \<in> Pi I F" (is "?A \<in> _")
      by (auto split: split_if_asm)
    with indep have "prob (\<Inter>j\<in>I. ?A j) = (\<Prod>j\<in>I. prob (?A j))"
      by auto
    also have "\<dots> = (\<Prod>j\<in>J. prob (A j))"
      unfolding if_distrib setprod.If_cases[OF `finite I`]
      using prob_space `J \<subseteq> I` by (simp add: Int_absorb1 setprod_1)
    finally show "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))" ..
  qed
qed

lemma (in prob_space) indep_vars_finite:
  fixes I :: "'i set"
  assumes I: "I \<noteq> {}" "finite I"
    and M': "\<And>i. i \<in> I \<Longrightarrow> sets (M' i) = sigma_sets (space (M' i)) (E i)"
    and rv: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X i)"
    and Int_stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (E i)"
    and space: "\<And>i. i \<in> I \<Longrightarrow> space (M' i) \<in> E i" and closed: "\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> Pow (space (M' i))"
  shows "indep_vars M' X I \<longleftrightarrow>
    (\<forall>A\<in>(\<Pi> i\<in>I. E i). prob (\<Inter>j\<in>I. X j -` A j \<inter> space M) = (\<Prod>j\<in>I. prob (X j -` A j \<inter> space M)))"
proof -
  from rv have X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> space M \<rightarrow> space (M' i)"
    unfolding measurable_def by simp

  { fix i assume "i\<in>I"
    from closed[OF `i \<in> I`]
    have "sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}
      = sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> E i}"
      unfolding sigma_sets_vimage_commute[OF X, OF `i \<in> I`, symmetric] M'[OF `i \<in> I`]
      by (subst sigma_sets_sigma_sets_eq) auto }
  note sigma_sets_X = this

  { fix i assume "i\<in>I"
    have "Int_stable {X i -` A \<inter> space M |A. A \<in> E i}"
    proof (rule Int_stableI)
      fix a assume "a \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
      then obtain A where "a = X i -` A \<inter> space M" "A \<in> E i" by auto
      moreover
      fix b assume "b \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
      then obtain B where "b = X i -` B \<inter> space M" "B \<in> E i" by auto
      moreover
      have "(X i -` A \<inter> space M) \<inter> (X i -` B \<inter> space M) = X i -` (A \<inter> B) \<inter> space M" by auto
      moreover note Int_stable[OF `i \<in> I`]
      ultimately
      show "a \<inter> b \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
        by (auto simp del: vimage_Int intro!: exI[of _ "A \<inter> B"] dest: Int_stableD)
    qed }
  note indep_sets_X = indep_sets_sigma_sets_iff[OF this]

  { fix i assume "i \<in> I"
    { fix A assume "A \<in> E i"
      with M'[OF `i \<in> I`] have "A \<in> sets (M' i)" by auto
      moreover
      from rv[OF `i\<in>I`] have "X i \<in> measurable M (M' i)" by auto
      ultimately
      have "X i -` A \<inter> space M \<in> sets M" by (auto intro: measurable_sets) }
    with X[OF `i\<in>I`] space[OF `i\<in>I`]
    have "{X i -` A \<inter> space M |A. A \<in> E i} \<subseteq> events"
      "space M \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
      by (auto intro!: exI[of _ "space (M' i)"]) }
  note indep_sets_finite_X = indep_sets_finite[OF I this]

  have "(\<forall>A\<in>\<Pi> i\<in>I. {X i -` A \<inter> space M |A. A \<in> E i}. prob (INTER I A) = (\<Prod>j\<in>I. prob (A j))) =
    (\<forall>A\<in>\<Pi> i\<in>I. E i. prob ((\<Inter>j\<in>I. X j -` A j) \<inter> space M) = (\<Prod>x\<in>I. prob (X x -` A x \<inter> space M)))"
    (is "?L = ?R")
  proof safe
    fix A assume ?L and A: "A \<in> (\<Pi> i\<in>I. E i)"
    from `?L`[THEN bspec, of "\<lambda>i. X i -` A i \<inter> space M"] A `I \<noteq> {}`
    show "prob ((\<Inter>j\<in>I. X j -` A j) \<inter> space M) = (\<Prod>x\<in>I. prob (X x -` A x \<inter> space M))"
      by (auto simp add: Pi_iff)
  next
    fix A assume ?R and A: "A \<in> (\<Pi> i\<in>I. {X i -` A \<inter> space M |A. A \<in> E i})"
    from A have "\<forall>i\<in>I. \<exists>B. A i = X i -` B \<inter> space M \<and> B \<in> E i" by auto
    from bchoice[OF this] obtain B where B: "\<forall>i\<in>I. A i = X i -` B i \<inter> space M"
      "B \<in> (\<Pi> i\<in>I. E i)" by auto
    from `?R`[THEN bspec, OF B(2)] B(1) `I \<noteq> {}`
    show "prob (INTER I A) = (\<Prod>j\<in>I. prob (A j))"
      by simp
  qed
  then show ?thesis using `I \<noteq> {}`
    by (simp add: rv indep_vars_def indep_sets_X sigma_sets_X indep_sets_finite_X cong: indep_sets_cong)
qed

lemma (in prob_space) indep_vars_compose:
  assumes "indep_vars M' X I"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "indep_vars N (\<lambda>i. Y i \<circ> X i) I"
  unfolding indep_vars_def
proof
  from rv `indep_vars M' X I`
  show "\<forall>i\<in>I. random_variable (N i) (Y i \<circ> X i)"
    by (auto simp: indep_vars_def)

  have "indep_sets (\<lambda>i. sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
    using `indep_vars M' X I` by (simp add: indep_vars_def)
  then show "indep_sets (\<lambda>i. sigma_sets (space M) {(Y i \<circ> X i) -` A \<inter> space M |A. A \<in> sets (N i)}) I"
  proof (rule indep_sets_mono_sets)
    fix i assume "i \<in> I"
    with `indep_vars M' X I` have X: "X i \<in> space M \<rightarrow> space (M' i)"
      unfolding indep_vars_def measurable_def by auto
    { fix A assume "A \<in> sets (N i)"
      then have "\<exists>B. (Y i \<circ> X i) -` A \<inter> space M = X i -` B \<inter> space M \<and> B \<in> sets (M' i)"
        by (intro exI[of _ "Y i -` A \<inter> space (M' i)"])
           (auto simp: vimage_compose intro!: measurable_sets rv `i \<in> I` funcset_mem[OF X]) }
    then show "sigma_sets (space M) {(Y i \<circ> X i) -` A \<inter> space M |A. A \<in> sets (N i)} \<subseteq>
      sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
      by (intro sigma_sets_subseteq) (auto simp: vimage_compose)
  qed
qed

lemma (in prob_space) indep_varsD_finite:
  assumes X: "indep_vars M' X I"
  assumes I: "I \<noteq> {}" "finite I" "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M' i)"
  shows "prob (\<Inter>i\<in>I. X i -` A i \<inter> space M) = (\<Prod>i\<in>I. prob (X i -` A i \<inter> space M))"
proof (rule indep_setsD)
  show "indep_sets (\<lambda>i. sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
    using X by (auto simp: indep_vars_def)
  show "I \<subseteq> I" "I \<noteq> {}" "finite I" using I by auto
  show "\<forall>i\<in>I. X i -` A i \<inter> space M \<in> sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
    using I by auto
qed

lemma (in prob_space) indep_varsD:
  assumes X: "indep_vars M' X I"
  assumes I: "J \<noteq> {}" "finite J" "J \<subseteq> I" "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets (M' i)"
  shows "prob (\<Inter>i\<in>J. X i -` A i \<inter> space M) = (\<Prod>i\<in>J. prob (X i -` A i \<inter> space M))"
proof (rule indep_setsD)
  show "indep_sets (\<lambda>i. sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
    using X by (auto simp: indep_vars_def)
  show "\<forall>i\<in>J. X i -` A i \<inter> space M \<in> sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
    using I by auto
qed fact+

lemma prod_algebra_cong:
  assumes "I = J" and sets: "(\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (N i))"
  shows "prod_algebra I M = prod_algebra J N"
proof -
  have space: "\<And>i. i \<in> I \<Longrightarrow> space (M i) = space (N i)"
    using sets_eq_imp_space_eq[OF sets] by auto
  with sets show ?thesis unfolding `I = J`
    by (intro antisym prod_algebra_mono) auto
qed

lemma space_in_prod_algebra:
  "(\<Pi>\<^isub>E i\<in>I. space (M i)) \<in> prod_algebra I M"
proof cases
  assume "I = {}" then show ?thesis
    by (auto simp add: prod_algebra_def image_iff prod_emb_def)
next
  assume "I \<noteq> {}"
  then obtain i where "i \<in> I" by auto
  then have "(\<Pi>\<^isub>E i\<in>I. space (M i)) = prod_emb I M {i} (\<Pi>\<^isub>E i\<in>{i}. space (M i))"
    by (auto simp: prod_emb_def Pi_iff)
  also have "\<dots> \<in> prod_algebra I M"
    using `i \<in> I` by (intro prod_algebraI) auto
  finally show ?thesis .
qed

lemma (in prob_space) indep_vars_iff_distr_eq_PiM:
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "I \<noteq> {}"
  assumes rv: "\<And>i. random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
    distr M (\<Pi>\<^isub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^isub>M i\<in>I. distr M (M' i) (X i))"
proof -
  let ?P = "\<Pi>\<^isub>M i\<in>I. M' i"
  let ?X = "\<lambda>x. \<lambda>i\<in>I. X i x"
  let ?D = "distr M ?P ?X"
  have X: "random_variable ?P ?X" by (intro measurable_restrict rv)
  interpret D: prob_space ?D by (intro prob_space_distr X)

  let ?D' = "\<lambda>i. distr M (M' i) (X i)"
  let ?P' = "\<Pi>\<^isub>M i\<in>I. distr M (M' i) (X i)"
  interpret D': prob_space "?D' i" for i by (intro prob_space_distr rv)
  interpret P: product_prob_space ?D' I ..
    
  show ?thesis
  proof
    assume "indep_vars M' X I"
    show "?D = ?P'"
    proof (rule measure_eqI_generator_eq)
      show "Int_stable (prod_algebra I M')"
        by (rule Int_stable_prod_algebra)
      show "prod_algebra I M' \<subseteq> Pow (space ?P)"
        using prod_algebra_sets_into_space by (simp add: space_PiM)
      show "sets ?D = sigma_sets (space ?P) (prod_algebra I M')"
        by (simp add: sets_PiM space_PiM)
      show "sets ?P' = sigma_sets (space ?P) (prod_algebra I M')"
        by (simp add: sets_PiM space_PiM cong: prod_algebra_cong)
      let ?A = "\<lambda>i. \<Pi>\<^isub>E i\<in>I. space (M' i)"
      show "range ?A \<subseteq> prod_algebra I M'" "(\<Union>i. ?A i) = space (Pi\<^isub>M I M')"
        by (auto simp: space_PiM intro!: space_in_prod_algebra cong: prod_algebra_cong)
      { fix i show "emeasure ?D (\<Pi>\<^isub>E i\<in>I. space (M' i)) \<noteq> \<infinity>" by auto }
    next
      fix E assume E: "E \<in> prod_algebra I M'"
      from prod_algebraE[OF E] guess J Y . note J = this

      from E have "E \<in> sets ?P" by (auto simp: sets_PiM)
      then have "emeasure ?D E = emeasure M (?X -` E \<inter> space M)"
        by (simp add: emeasure_distr X)
      also have "?X -` E \<inter> space M = (\<Inter>i\<in>J. X i -` Y i \<inter> space M)"
        using J `I \<noteq> {}` measurable_space[OF rv] by (auto simp: prod_emb_def Pi_iff split: split_if_asm)
      also have "emeasure M (\<Inter>i\<in>J. X i -` Y i \<inter> space M) = (\<Prod> i\<in>J. emeasure M (X i -` Y i \<inter> space M))"
        using `indep_vars M' X I` J `I \<noteq> {}` using indep_varsD[of M' X I J]
        by (auto simp: emeasure_eq_measure setprod_ereal)
      also have "\<dots> = (\<Prod> i\<in>J. emeasure (?D' i) (Y i))"
        using rv J by (simp add: emeasure_distr)
      also have "\<dots> = emeasure ?P' E"
        using P.emeasure_PiM_emb[of J Y] J by (simp add: prod_emb_def)
      finally show "emeasure ?D E = emeasure ?P' E" .
    qed
  next
    assume "?D = ?P'"
    show "indep_vars M' X I" unfolding indep_vars_def
    proof (intro conjI indep_setsI ballI rv)
      fix i show "sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)} \<subseteq> events"
        by (auto intro!: sigma_sets_subset measurable_sets rv)
    next
      fix J Y' assume J: "J \<noteq> {}" "J \<subseteq> I" "finite J"
      assume Y': "\<forall>j\<in>J. Y' j \<in> sigma_sets (space M) {X j -` A \<inter> space M |A. A \<in> sets (M' j)}"
      have "\<forall>j\<in>J. \<exists>Y. Y' j = X j -` Y \<inter> space M \<and> Y \<in> sets (M' j)"
      proof
        fix j assume "j \<in> J"
        from Y'[rule_format, OF this] rv[of j]
        show "\<exists>Y. Y' j = X j -` Y \<inter> space M \<and> Y \<in> sets (M' j)"
          by (subst (asm) sigma_sets_vimage_commute[symmetric, of _ _ "space (M' j)"])
             (auto dest: measurable_space simp: sigma_sets_eq)
      qed
      from bchoice[OF this] obtain Y where
        Y: "\<And>j. j \<in> J \<Longrightarrow> Y' j = X j -` Y j \<inter> space M" "\<And>j. j \<in> J \<Longrightarrow> Y j \<in> sets (M' j)" by auto
      let ?E = "prod_emb I M' J (Pi\<^isub>E J Y)"
      from Y have "(\<Inter>j\<in>J. Y' j) = ?X -` ?E \<inter> space M"
        using J `I \<noteq> {}` measurable_space[OF rv] by (auto simp: prod_emb_def Pi_iff split: split_if_asm)
      then have "emeasure M (\<Inter>j\<in>J. Y' j) = emeasure M (?X -` ?E \<inter> space M)"
        by simp
      also have "\<dots> = emeasure ?D ?E"
        using Y  J by (intro emeasure_distr[symmetric] X sets_PiM_I) auto
      also have "\<dots> = emeasure ?P' ?E"
        using `?D = ?P'` by simp
      also have "\<dots> = (\<Prod> i\<in>J. emeasure (?D' i) (Y i))"
        using P.emeasure_PiM_emb[of J Y] J Y by (simp add: prod_emb_def)
      also have "\<dots> = (\<Prod> i\<in>J. emeasure M (Y' i))"
        using rv J Y by (simp add: emeasure_distr)
      finally have "emeasure M (\<Inter>j\<in>J. Y' j) = (\<Prod> i\<in>J. emeasure M (Y' i))" .
      then show "prob (\<Inter>j\<in>J. Y' j) = (\<Prod> i\<in>J. prob (Y' i))"
        by (auto simp: emeasure_eq_measure setprod_ereal)
    qed
  qed
qed

lemma (in prob_space) indep_varD:
  assumes indep: "indep_var Ma A Mb B"
  assumes sets: "Xa \<in> sets Ma" "Xb \<in> sets Mb"
  shows "prob ((\<lambda>x. (A x, B x)) -` (Xa \<times> Xb) \<inter> space M) =
    prob (A -` Xa \<inter> space M) * prob (B -` Xb \<inter> space M)"
proof -
  have "prob ((\<lambda>x. (A x, B x)) -` (Xa \<times> Xb) \<inter> space M) =
    prob (\<Inter>i\<in>UNIV. (bool_case A B i -` bool_case Xa Xb i \<inter> space M))"
    by (auto intro!: arg_cong[where f=prob] simp: UNIV_bool)
  also have "\<dots> = (\<Prod>i\<in>UNIV. prob (bool_case A B i -` bool_case Xa Xb i \<inter> space M))"
    using indep unfolding indep_var_def
    by (rule indep_varsD) (auto split: bool.split intro: sets)
  also have "\<dots> = prob (A -` Xa \<inter> space M) * prob (B -` Xb \<inter> space M)"
    unfolding UNIV_bool by simp
  finally show ?thesis .
qed

lemma (in prob_space)
  assumes "indep_var S X T Y"
  shows indep_var_rv1: "random_variable S X"
    and indep_var_rv2: "random_variable T Y"
proof -
  have "\<forall>i\<in>UNIV. random_variable (bool_case S T i) (bool_case X Y i)"
    using assms unfolding indep_var_def indep_vars_def by auto
  then show "random_variable S X" "random_variable T Y"
    unfolding UNIV_bool by auto
qed

lemma measurable_bool_case[simp, intro]:
  "(\<lambda>(x, y). bool_case x y) \<in> measurable (M \<Otimes>\<^isub>M N) (Pi\<^isub>M UNIV (bool_case M N))"
    (is "?f \<in> measurable ?B ?P")
proof (rule measurable_PiM_single)
  show "?f \<in> space ?B \<rightarrow> (\<Pi>\<^isub>E i\<in>UNIV. space (bool_case M N i))"
    by (auto simp: space_pair_measure extensional_def split: bool.split)
  fix i A assume "A \<in> sets (case i of True \<Rightarrow> M | False \<Rightarrow> N)"
  moreover then have "{\<omega> \<in> space (M \<Otimes>\<^isub>M N). prod_case bool_case \<omega> i \<in> A}
    = (case i of True \<Rightarrow> A \<times> space N | False \<Rightarrow> space M \<times> A)" 
    by (auto simp: space_pair_measure split: bool.split dest!: sets_into_space)
  ultimately show "{\<omega> \<in> space (M \<Otimes>\<^isub>M N). prod_case bool_case \<omega> i \<in> A} \<in> sets ?B"
    by (auto split: bool.split)
qed

lemma borel_measurable_indicator':
  "A \<in> sets N \<Longrightarrow> f \<in> measurable M N \<Longrightarrow> (\<lambda>x. indicator A (f x)) \<in> borel_measurable M"
  using measurable_comp[OF _ borel_measurable_indicator, of f M N A] by (auto simp add: comp_def)

lemma (in product_sigma_finite) distr_component:
  "distr (M i) (Pi\<^isub>M {i} M) (\<lambda>x. \<lambda>i\<in>{i}. x) = Pi\<^isub>M {i} M" (is "?D = ?P")
proof (intro measure_eqI[symmetric])
  interpret I: finite_product_sigma_finite M "{i}" by default simp

  have eq: "\<And>x. x \<in> extensional {i} \<Longrightarrow> (\<lambda>j\<in>{i}. x i) = x"
    by (auto simp: extensional_def restrict_def)

  fix A assume A: "A \<in> sets ?P"
  then have "emeasure ?P A = (\<integral>\<^isup>+x. indicator A x \<partial>?P)" 
    by simp
  also have "\<dots> = (\<integral>\<^isup>+x. indicator ((\<lambda>x. \<lambda>i\<in>{i}. x) -` A \<inter> space (M i)) x \<partial>M i)" 
    apply (subst product_positive_integral_singleton[symmetric])
    apply (force intro!: measurable_restrict measurable_sets A)
    apply (auto intro!: positive_integral_cong simp: space_PiM indicator_def simp: eq)
    done
  also have "\<dots> = emeasure (M i) ((\<lambda>x. \<lambda>i\<in>{i}. x) -` A \<inter> space (M i))"
    by (force intro!: measurable_restrict measurable_sets A positive_integral_indicator)
  also have "\<dots> = emeasure ?D A"
    using A by (auto intro!: emeasure_distr[symmetric] measurable_restrict) 
  finally show "emeasure (Pi\<^isub>M {i} M) A = emeasure ?D A" .
qed simp

lemma pair_measure_eqI:
  assumes "sigma_finite_measure M1" "sigma_finite_measure M2"
  assumes sets: "sets (M1 \<Otimes>\<^isub>M M2) = sets M"
  assumes emeasure: "\<And>A B. A \<in> sets M1 \<Longrightarrow> B \<in> sets M2 \<Longrightarrow> emeasure M1 A * emeasure M2 B = emeasure M (A \<times> B)"
  shows "M1 \<Otimes>\<^isub>M M2 = M"
proof -
  interpret M1: sigma_finite_measure M1 by fact
  interpret M2: sigma_finite_measure M2 by fact
  interpret pair_sigma_finite M1 M2 by default
  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  let ?E = "{a \<times> b |a b. a \<in> sets M1 \<and> b \<in> sets M2}"
  let ?P = "M1 \<Otimes>\<^isub>M M2"
  show ?thesis
  proof (rule measure_eqI_generator_eq[OF Int_stable_pair_measure_generator[of M1 M2]])
    show "?E \<subseteq> Pow (space ?P)"
      using space_closed[of M1] space_closed[of M2] by (auto simp: space_pair_measure)
    show "sets ?P = sigma_sets (space ?P) ?E"
      by (simp add: sets_pair_measure space_pair_measure)
    then show "sets M = sigma_sets (space ?P) ?E"
      using sets[symmetric] by simp
  next
    show "range F \<subseteq> ?E" "(\<Union>i. F i) = space ?P" "\<And>i. emeasure ?P (F i) \<noteq> \<infinity>"
      using F by (auto simp: space_pair_measure)
  next
    fix X assume "X \<in> ?E"
    then obtain A B where X[simp]: "X = A \<times> B" and A: "A \<in> sets M1" and B: "B \<in> sets M2" by auto
    then have "emeasure ?P X = emeasure M1 A * emeasure M2 B"
       by (simp add: M2.emeasure_pair_measure_Times)
    also have "\<dots> = emeasure M (A \<times> B)"
      using A B emeasure by auto
    finally show "emeasure ?P X = emeasure M X"
      by simp
  qed
qed

lemma pair_measure_eq_distr_PiM:
  fixes M1 :: "'a measure" and M2 :: "'a measure"
  assumes "sigma_finite_measure M1" "sigma_finite_measure M2"
  shows "(M1 \<Otimes>\<^isub>M M2) = distr (Pi\<^isub>M UNIV (bool_case M1 M2)) (M1 \<Otimes>\<^isub>M M2) (\<lambda>x. (x True, x False))"
    (is "?P = ?D")
proof (rule pair_measure_eqI[OF assms])
  interpret B: product_sigma_finite "bool_case M1 M2"
    unfolding product_sigma_finite_def using assms by (auto split: bool.split)
  let ?B = "Pi\<^isub>M UNIV (bool_case M1 M2)"

  have [simp]: "fst \<circ> (\<lambda>x. (x True, x False)) = (\<lambda>x. x True)" "snd \<circ> (\<lambda>x. (x True, x False)) = (\<lambda>x. x False)"
    by auto
  fix A B assume A: "A \<in> sets M1" and B: "B \<in> sets M2"
  have "emeasure M1 A * emeasure M2 B = (\<Prod> i\<in>UNIV. emeasure (bool_case M1 M2 i) (bool_case A B i))"
    by (simp add: UNIV_bool ac_simps)
  also have "\<dots> = emeasure ?B (Pi\<^isub>E UNIV (bool_case A B))"
    using A B by (subst B.emeasure_PiM) (auto split: bool.split)
  also have "Pi\<^isub>E UNIV (bool_case A B) = (\<lambda>x. (x True, x False)) -` (A \<times> B) \<inter> space ?B"
    using A[THEN sets_into_space] B[THEN sets_into_space]
    by (auto simp: Pi_iff all_bool_eq space_PiM split: bool.split)
  finally show "emeasure M1 A * emeasure M2 B = emeasure ?D (A \<times> B)"
    using A B
      measurable_component_singleton[of True UNIV "bool_case M1 M2"]
      measurable_component_singleton[of False UNIV "bool_case M1 M2"]
    by (subst emeasure_distr) (auto simp: measurable_pair_iff)
qed simp

lemma measurable_Pair:
  assumes rvs: "X \<in> measurable M S" "Y \<in> measurable M T"
  shows "(\<lambda>x. (X x, Y x)) \<in> measurable M (S \<Otimes>\<^isub>M T)"
proof -
  have [simp]: "fst \<circ> (\<lambda>x. (X x, Y x)) = (\<lambda>x. X x)" "snd \<circ> (\<lambda>x. (X x, Y x)) = (\<lambda>x. Y x)"
    by auto
  show " (\<lambda>x. (X x, Y x)) \<in> measurable M (S \<Otimes>\<^isub>M T)"
    by (auto simp: measurable_pair_iff rvs)
qed

lemma (in prob_space) indep_var_distribution_eq:
  "indep_var S X T Y \<longleftrightarrow> random_variable S X \<and> random_variable T Y \<and>
    distr M S X \<Otimes>\<^isub>M distr M T Y = distr M (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))" (is "_ \<longleftrightarrow> _ \<and> _ \<and> ?S \<Otimes>\<^isub>M ?T = ?J")
proof safe
  assume "indep_var S X T Y"
  then show rvs: "random_variable S X" "random_variable T Y"
    by (blast dest: indep_var_rv1 indep_var_rv2)+
  then have XY: "random_variable (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
    by (rule measurable_Pair)

  interpret X: prob_space ?S by (rule prob_space_distr) fact
  interpret Y: prob_space ?T by (rule prob_space_distr) fact
  interpret XY: pair_prob_space ?S ?T ..
  show "?S \<Otimes>\<^isub>M ?T = ?J"
  proof (rule pair_measure_eqI)
    show "sigma_finite_measure ?S" ..
    show "sigma_finite_measure ?T" ..

    fix A B assume A: "A \<in> sets ?S" and B: "B \<in> sets ?T"
    have "emeasure ?J (A \<times> B) = emeasure M ((\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M)"
      using A B by (intro emeasure_distr[OF XY]) auto
    also have "\<dots> = emeasure M (X -` A \<inter> space M) * emeasure M (Y -` B \<inter> space M)"
      using indep_varD[OF `indep_var S X T Y`, of A B] A B by (simp add: emeasure_eq_measure)
    also have "\<dots> = emeasure ?S A * emeasure ?T B"
      using rvs A B by (simp add: emeasure_distr)
    finally show "emeasure ?S A * emeasure ?T B = emeasure ?J (A \<times> B)" by simp
  qed simp
next
  assume rvs: "random_variable S X" "random_variable T Y"
  then have XY: "random_variable (S \<Otimes>\<^isub>M T) (\<lambda>x. (X x, Y x))"
    by (rule measurable_Pair)

  let ?S = "distr M S X" and ?T = "distr M T Y"
  interpret X: prob_space ?S by (rule prob_space_distr) fact
  interpret Y: prob_space ?T by (rule prob_space_distr) fact
  interpret XY: pair_prob_space ?S ?T ..

  assume "?S \<Otimes>\<^isub>M ?T = ?J"

  { fix S and X
    have "Int_stable {X -` A \<inter> space M |A. A \<in> sets S}"
    proof (safe intro!: Int_stableI)
      fix A B assume "A \<in> sets S" "B \<in> sets S"
      then show "\<exists>C. (X -` A \<inter> space M) \<inter> (X -` B \<inter> space M) = (X -` C \<inter> space M) \<and> C \<in> sets S"
        by (intro exI[of _ "A \<inter> B"]) auto
    qed }
  note Int_stable = this

  show "indep_var S X T Y" unfolding indep_var_eq
  proof (intro conjI indep_set_sigma_sets Int_stable rvs)
    show "indep_set {X -` A \<inter> space M |A. A \<in> sets S} {Y -` A \<inter> space M |A. A \<in> sets T}"
    proof (safe intro!: indep_setI)
      { fix A assume "A \<in> sets S" then show "X -` A \<inter> space M \<in> sets M"
        using `X \<in> measurable M S` by (auto intro: measurable_sets) }
      { fix A assume "A \<in> sets T" then show "Y -` A \<inter> space M \<in> sets M"
        using `Y \<in> measurable M T` by (auto intro: measurable_sets) }
    next
      fix A B assume ab: "A \<in> sets S" "B \<in> sets T"
      then have "ereal (prob ((X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M))) = emeasure ?J (A \<times> B)"
        using XY by (auto simp add: emeasure_distr emeasure_eq_measure intro!: arg_cong[where f="prob"])
      also have "\<dots> = emeasure (?S \<Otimes>\<^isub>M ?T) (A \<times> B)"
        unfolding `?S \<Otimes>\<^isub>M ?T = ?J` ..
      also have "\<dots> = emeasure ?S A * emeasure ?T B"
        using ab by (simp add: Y.emeasure_pair_measure_Times)
      finally show "prob ((X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M)) =
        prob (X -` A \<inter> space M) * prob (Y -` B \<inter> space M)"
        using rvs ab by (simp add: emeasure_eq_measure emeasure_distr)
    qed
  qed
qed

end

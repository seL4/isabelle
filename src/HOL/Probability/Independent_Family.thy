(*  Title:      HOL/Probability/Independent_Family.thy
    Author:     Johannes Hölzl, TU München
    Author:     Sudeep Kanav, TU München
*)

section \<open>Independent families of events, event sets, and random variables\<close>

theory Independent_Family
  imports Infinite_Product_Measure
begin

definition (in prob_space)
  "indep_sets F I \<longleftrightarrow> (\<forall>i\<in>I. F i \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> (\<forall>A\<in>Pi J F. prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))))"

definition (in prob_space)
  "indep_set A B \<longleftrightarrow> indep_sets (case_bool A B) UNIV"

definition (in prob_space)
  indep_events_def_alt: "indep_events A I \<longleftrightarrow> indep_sets (\<lambda>i. {A i}) I"

lemma (in prob_space) indep_events_def:
  "indep_events A I \<longleftrightarrow> (A`I \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j)))"
  unfolding indep_events_def_alt indep_sets_def
  apply (simp add: Ball_def Pi_iff image_subset_iff_funcset)
  apply (intro conj_cong refl arg_cong[where f=All] ext imp_cong)
  apply auto
  done

lemma (in prob_space) indep_eventsI:
  "(\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M) \<Longrightarrow> (\<And>J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter>i\<in>J. F i) = (\<Prod>i\<in>J. prob (F i))) \<Longrightarrow> indep_events F I"
  by (auto simp: indep_events_def)

definition (in prob_space)
  "indep_event A B \<longleftrightarrow> indep_events (case_bool A B) UNIV"

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
  with F \<open>J \<noteq> {}\<close> indep[of "F True" "F False"]
  show "prob (\<Inter>j\<in>J. F j) = (\<Prod>j\<in>J. prob (F j))"
    unfolding UNIV_bool Pow_insert by (auto simp: ac_simps)
qed (auto split: bool.split simp: ev)

lemma (in prob_space) indep_setD:
  assumes indep: "indep_set A B" and ev: "a \<in> A" "b \<in> B"
  shows "prob (a \<inter> b) = prob a * prob b"
  using indep[unfolded indep_set_def, THEN indep_setsD, of UNIV "case_bool a b"] ev
  by (simp add: ac_simps UNIV_bool)

lemma (in prob_space)
  assumes indep: "indep_set A B"
  shows indep_setD_ev1: "A \<subseteq> events"
    and indep_setD_ev2: "B \<subseteq> events"
  using indep unfolding indep_set_def indep_sets_def UNIV_bool by auto

lemma (in prob_space) indep_sets_Dynkin:
  assumes indep: "indep_sets F I"
  shows "indep_sets (\<lambda>i. Dynkin (space M) (F i)) I"
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
      moreover define G where "G = ?G J"
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
                using \<open>j \<in> J\<close> \<open>A j = X\<close> by (auto intro!: arg_cong[where f=prob] split: if_split_asm)
              also have "\<dots> = prob X * (\<Prod>i\<in>J-{j}. prob (A i))"
              proof (rule indep)
                show "J - {j} \<noteq> {}" "J - {j} \<subseteq> K" "finite (J - {j})" "j \<notin> J - {j}"
                  using J \<open>J \<noteq> {j}\<close> \<open>j \<in> J\<close> by auto
                show "\<forall>i\<in>J - {j}. A i \<in> G i"
                  using J by auto
              qed
              also have "\<dots> = prob (A j) * (\<Prod>i\<in>J-{j}. prob (A i))"
                using \<open>A j = X\<close> by simp
              also have "\<dots> = (\<Prod>i\<in>J. prob (A i))"
                unfolding prod.insert_remove[OF \<open>finite J\<close>, symmetric, of "\<lambda>i. prob  (A i)"]
                using \<open>j \<in> J\<close> by (simp add: insert_absorb)
              finally show ?thesis .
            qed
          next
            assume "j \<notin> J"
            with J have "\<forall>i\<in>J. A i \<in> G i" by (auto split: if_split_asm)
            with J show ?thesis
              by (intro indep_setsD[OF G(1)]) auto
          qed
        qed }
      note indep_sets_insert = this
      have "Dynkin_system (space M) ?D"
      proof (rule Dynkin_systemI', simp_all cong del: indep_sets_cong, safe)
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
            using A_sets sets.sets_into_space[of _ M] X \<open>J \<noteq> {}\<close>
            by (auto intro!: arg_cong[where f=prob] split: if_split_asm)
          also have "\<dots> = prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)"
            using J \<open>J \<noteq> {}\<close> \<open>j \<notin> J\<close> A_sets X sets.sets_into_space
            by (auto intro!: finite_measure_Diff sets.finite_INT split: if_split_asm)
          finally have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) =
              prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)" .
          moreover {
            have "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
              using J A \<open>finite J\<close> by (intro indep_setsD[OF G(1)]) auto
            then have "prob (\<Inter>j\<in>J. A j) = prob (space M) * (\<Prod>i\<in>J. prob (A i))"
              using prob_space by simp }
          moreover {
            have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = (\<Prod>i\<in>insert j J. prob ((A(j := X)) i))"
              using J A \<open>j \<in> K\<close> by (intro indep_setsD[OF G']) auto
            then have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = prob X * (\<Prod>i\<in>J. prob (A i))"
              using \<open>finite J\<close> \<open>j \<notin> J\<close> by (auto intro!: prod.cong) }
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
            using \<open>J \<noteq> {}\<close> \<open>j \<notin> J\<close> \<open>j \<in> K\<close> by (auto intro!: arg_cong[where f=prob] split: if_split_asm)
          moreover have "(\<lambda>k. prob (\<Inter>i\<in>insert j J. (A(j := F k)) i)) sums prob (\<Union>k. (\<Inter>i\<in>insert j J. (A(j := F k)) i))"
          proof (rule finite_measure_UNION)
            show "disjoint_family (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i)"
              using disj by (rule disjoint_family_on_bisimulation) auto
            show "range (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i) \<subseteq> events"
              using A_sets F \<open>finite J\<close> \<open>J \<noteq> {}\<close> \<open>j \<notin> J\<close> by (auto intro!: sets.Int)
          qed
          moreover { fix k
            from J A \<open>j \<in> K\<close> have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * (\<Prod>i\<in>J. prob (A i))"
              by (subst indep_setsD[OF F(2)]) (auto intro!: prod.cong split: if_split_asm)
            also have "\<dots> = prob (F k) * prob (\<Inter>i\<in>J. A i)"
              using J A \<open>j \<in> K\<close> by (subst indep_setsD[OF G(1)]) auto
            finally have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * prob (\<Inter>i\<in>J. A i)" . }
          ultimately have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)))"
            by simp
          moreover
          have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * prob (\<Inter>i\<in>J. A i))"
            using disj F(1) by (intro finite_measure_UNION sums_mult2) auto
          then have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * (\<Prod>i\<in>J. prob (A i)))"
            using J A \<open>j \<in> K\<close> by (subst indep_setsD[OF G(1), symmetric]) auto
          ultimately
          show "prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)) = prob (\<Union>k. F k) * (\<Prod>j\<in>J. prob (A j))"
            by (auto dest!: sums_unique)
        qed (insert F, auto)
      qed (insert sets.sets_into_space, auto)
      then have mono: "Dynkin (space M) (G j) \<subseteq> {E \<in> events. indep_sets (G(j := {E})) K}"
      proof (rule Dynkin_system.Dynkin_subset, safe)
        fix X assume "X \<in> G j"
        then show "X \<in> events" using G \<open>j \<in> K\<close> by auto
        from \<open>indep_sets G K\<close>
        show "indep_sets (G(j := {X})) K"
          by (rule indep_sets_mono_sets) (insert \<open>X \<in> G j\<close>, auto)
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
          with J A have "\<forall>i\<in>J. A i \<in> G i" by (auto split: if_split_asm)
          with J show ?thesis
            by (intro indep_setsD[OF G(1)]) auto
        qed
      qed
      then have "indep_sets (G(j := Dynkin (space M) (G j))) K"
        by (rule indep_sets_mono_sets) (insert mono, auto)
      then show ?case
        by (rule indep_sets_mono_sets) (insert \<open>j \<in> K\<close> \<open>j \<notin> J\<close>, auto simp: G_def)
    qed (insert \<open>indep_sets F K\<close>, simp) }
  from this[OF \<open>indep_sets F J\<close> \<open>finite J\<close> subset_refl]
  show "indep_sets ?F J"
    by (rule indep_sets_mono_sets) auto
qed

lemma (in prob_space) indep_sets_sigma:
  assumes indep: "indep_sets F I"
  assumes stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  shows "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I"
proof -
  from indep_sets_Dynkin[OF indep]
  show ?thesis
  proof (rule indep_sets_mono_sets, subst sigma_eq_Dynkin, simp_all add: stable)
    fix i assume "i \<in> I"
    with indep have "F i \<subseteq> events" by (auto simp: indep_sets_def)
    with sets.sets_into_space show "F i \<subseteq> Pow (space M)" by auto
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
  "indep_var Ma A Mb B \<longleftrightarrow> indep_vars (case_bool Ma Mb) (case_bool A B) UNIV"

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
  by (intro arg_cong2[where f="(\<and>)"] arg_cong2[where f=indep_sets] ext)
     (auto split: bool.split)

lemma (in prob_space) indep_sets2_eq:
  "indep_set A B \<longleftrightarrow> A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  unfolding indep_set_def
proof (intro iffI ballI conjI)
  assume indep: "indep_sets (case_bool A B) UNIV"
  { fix a b assume "a \<in> A" "b \<in> B"
    with indep_setsD[OF indep, of UNIV "case_bool a b"]
    show "prob (a \<inter> b) = prob a * prob b"
      unfolding UNIV_bool by (simp add: ac_simps) }
  from indep show "A \<subseteq> events" "B \<subseteq> events"
    unfolding indep_sets_def UNIV_bool by auto
next
  assume *: "A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  show "indep_sets (case_bool A B) UNIV"
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
    show "indep_sets (case_bool A B) UNIV"
      by (rule \<open>indep_set A B\<close>[unfolded indep_set_def])
    fix i show "Int_stable (case i of True \<Rightarrow> A | False \<Rightarrow> B)"
      using A B by (cases i) auto
  qed
  then show ?thesis
    unfolding indep_set_def
    by (rule indep_sets_mono_sets) (auto split: bool.split)
qed

lemma (in prob_space) indep_eventsI_indep_vars:
  assumes indep: "indep_vars N X I"
  assumes P: "\<And>i. i \<in> I \<Longrightarrow> {x\<in>space (N i). P i x} \<in> sets (N i)"
  shows "indep_events (\<lambda>i. {x\<in>space M. P i (X i x)}) I"
proof -
  have "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (N i)}) I"
    using indep unfolding indep_vars_def2 by auto
  then show ?thesis
    unfolding indep_events_def_alt
  proof (rule indep_sets_mono_sets)
    fix i assume "i \<in> I"
    then have "{{x \<in> space M. P i (X i x)}} = {X i -` {x\<in>space (N i). P i x} \<inter> space M}"
      using indep by (auto simp: indep_vars_def dest: measurable_space)
    also have "\<dots> \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}"
      using P[OF \<open>i \<in> I\<close>] by blast
    finally show "{{x \<in> space M. P i (X i x)}} \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}" .
  qed
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
      using sets.sets_into_space[of _ M] by (intro sigma_algebra_sigma_sets) auto

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
      fix j assume "j \<in> J" with E show "?E j \<subseteq> events" by (force  intro!: sets.finite_INT)
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
          with disjoint \<open>K \<subseteq> J\<close> \<open>k \<in> K\<close> \<open>j \<in> K\<close> have "I k \<inter> I j = {}"
            unfolding disjoint_family_on_def by auto
          with L(2,3)[OF \<open>j \<in> K\<close>] L(2,3)[OF \<open>k \<in> K\<close>]
          show False using \<open>l \<in> L k\<close> \<open>l \<in> L j\<close> by auto
        qed }
      note L_inj = this

      define k where "k l = (SOME k. k \<in> K \<and> l \<in> L k)" for l
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
        using K L L_inj by (subst prod.UNION_disjoint) auto
      also have "\<dots> = (\<Prod>j\<in>K. prob (A j))"
        using K L E' by (auto simp add: A intro!: prod.cong indep_setsD[OF indep, symmetric]) blast
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
      let ?f = "\<lambda>k. (if k \<in> Ka \<inter> Kb then Ea k \<inter> Eb k else if k \<in> Kb then Eb k else if k \<in> Ka then Ea k else {})"
      have "Ka \<union> Kb = (Ka \<inter> Kb) \<union> (Kb - Ka) \<union> (Ka - Kb)"
        by blast
      moreover have "(\<Inter>x\<in>Ka \<inter> Kb. Ea x \<inter> Eb x) \<inter>
        (\<Inter>x\<in>Kb - Ka. Eb x) \<inter> (\<Inter>x\<in>Ka - Kb. Ea x) = (\<Inter>k\<in>Ka. Ea k) \<inter> (\<Inter>k\<in>Kb. Eb k)"
        by auto
      ultimately have "(\<Inter>k\<in>Ka \<union> Kb. ?f k) = (\<Inter>k\<in>Ka. Ea k) \<inter> (\<Inter>k\<in>Kb. Eb k)" (is "?lhs = ?rhs")
        by (simp only: image_Un Inter_Un_distrib) simp
      then have "a \<inter> b = (\<Inter>k\<in>Ka \<union> Kb. ?f k)"
        by (simp only: a(1) b(1))
      with a b \<open>j \<in> J\<close> Int_stableD[OF Int_stable] show "a \<inter> b \<in> ?E j"
        by (intro CollectI exI[of _ "Ka \<union> Kb"] exI[of _ ?f]) auto
    qed
  qed
  ultimately show ?thesis
    by (simp cong: indep_sets_cong)
qed

lemma (in prob_space) indep_vars_restrict:
  assumes ind: "indep_vars M' X I" and K: "\<And>j. j \<in> L \<Longrightarrow> K j \<subseteq> I" and J: "disjoint_family_on K L"
  shows "indep_vars (\<lambda>j. PiM (K j) M') (\<lambda>j \<omega>. restrict (\<lambda>i. X i \<omega>) (K j)) L"
  unfolding indep_vars_def
proof safe
  fix j assume "j \<in> L" then show "random_variable (Pi\<^sub>M (K j) M') (\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>)"
    using K ind by (auto simp: indep_vars_def intro!: measurable_restrict)
next
  have X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> measurable M (M' i)"
    using ind by (auto simp: indep_vars_def)
  let ?proj = "\<lambda>j S. {(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` A \<inter> space M |A. A \<in> S}"
  let ?UN = "\<lambda>j. sigma_sets (space M) (\<Union>i\<in>K j. { X i -` A \<inter> space M| A. A \<in> sets (M' i) })"
  show "indep_sets (\<lambda>i. sigma_sets (space M) (?proj i (sets (Pi\<^sub>M (K i) M')))) L"
  proof (rule indep_sets_mono_sets)
    fix j assume j: "j \<in> L"
    have "sigma_sets (space M) (?proj j (sets (Pi\<^sub>M (K j) M'))) =
      sigma_sets (space M) (sigma_sets (space M) (?proj j (prod_algebra (K j) M')))"
      using j K X[THEN measurable_space] unfolding sets_PiM
      by (subst sigma_sets_vimage_commute) (auto simp add: Pi_iff)
    also have "\<dots> = sigma_sets (space M) (?proj j (prod_algebra (K j) M'))"
      by (rule sigma_sets_sigma_sets_eq) auto
    also have "\<dots> \<subseteq> ?UN j"
    proof (rule sigma_sets_mono, safe del: disjE elim!: prod_algebraE)
      fix J E assume J: "finite J" "J \<noteq> {} \<or> K j = {}"  "J \<subseteq> K j" and E: "\<forall>i. i \<in> J \<longrightarrow> E i \<in> sets (M' i)"
      show "(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` prod_emb (K j) M' J (Pi\<^sub>E J E) \<inter> space M \<in> ?UN j"
      proof cases
        assume "K j = {}" with J show ?thesis
          by (auto simp add: sigma_sets_empty_eq prod_emb_def)
      next
        assume "K j \<noteq> {}" with J have "J \<noteq> {}"
          by auto
        { interpret sigma_algebra "space M" "?UN j"
            by (rule sigma_algebra_sigma_sets) auto
          have "\<And>A. (\<And>i. i \<in> J \<Longrightarrow> A i \<in> ?UN j) \<Longrightarrow> \<Inter>(A ` J) \<in> ?UN j"
            using \<open>finite J\<close> \<open>J \<noteq> {}\<close> by (rule finite_INT) blast }
        note INT = this

        from \<open>J \<noteq> {}\<close> J K E[rule_format, THEN sets.sets_into_space] j
        have "(\<lambda>\<omega>. \<lambda>i\<in>K j. X i \<omega>) -` prod_emb (K j) M' J (Pi\<^sub>E J E) \<inter> space M
          = (\<Inter>i\<in>J. X i -` E i \<inter> space M)"
          apply (subst prod_emb_PiE[OF _ ])
          apply auto []
          apply auto []
          apply (auto simp add: Pi_iff intro!: X[THEN measurable_space])
          apply (erule_tac x=i in ballE)
          apply auto
          done
        also have "\<dots> \<in> ?UN j"
          apply (rule INT)
          apply (rule sigma_sets.Basic)
          using \<open>J \<subseteq> K j\<close> E
          apply auto
          done
        finally show ?thesis .
      qed
    qed
    finally show "sigma_sets (space M) (?proj j (sets (Pi\<^sub>M (K j) M'))) \<subseteq> ?UN j" .
  next
    show "indep_sets ?UN L"
    proof (rule indep_sets_collect_sigma)
      show "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) (\<Union>j\<in>L. K j)"
      proof (rule indep_sets_mono_index)
        show "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
          using ind unfolding indep_vars_def2 by auto
        show "(\<Union>l\<in>L. K l) \<subseteq> I"
          using K by auto
      qed
    next
      fix l i assume "l \<in> L" "i \<in> K l"
      show "Int_stable {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
        apply (auto simp: Int_stable_def)
        apply (rule_tac x="A \<inter> Aa" in exI)
        apply auto
        done
    qed fact
  qed
qed

lemma (in prob_space) indep_var_restrict:
  assumes ind: "indep_vars M' X I" and AB: "A \<inter> B = {}" "A \<subseteq> I" "B \<subseteq> I"
  shows "indep_var (PiM A M') (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) A) (PiM B M') (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) B)"
proof -
  have *:
    "case_bool (Pi\<^sub>M A M') (Pi\<^sub>M B M') = (\<lambda>b. PiM (case_bool A B b) M')"
    "case_bool (\<lambda>\<omega>. \<lambda>i\<in>A. X i \<omega>) (\<lambda>\<omega>. \<lambda>i\<in>B. X i \<omega>) = (\<lambda>b \<omega>. \<lambda>i\<in>case_bool A B b. X i \<omega>)"
    by (simp_all add: fun_eq_iff split: bool.split)
  show ?thesis
    unfolding indep_var_def * using AB
    by (intro indep_vars_restrict[OF ind]) (auto simp: disjoint_family_on_def split: bool.split)
qed

lemma (in prob_space) indep_vars_subset:
  assumes "indep_vars M' X I" "J \<subseteq> I"
  shows "indep_vars M' X J"
  using assms unfolding indep_vars_def indep_sets_def
  by auto

lemma (in prob_space) indep_vars_cong:
  "I = J \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> X i = Y i) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> M' i = N' i) \<Longrightarrow> indep_vars M' X I \<longleftrightarrow> indep_vars N' Y J"
  unfolding indep_vars_def2 by (intro conj_cong indep_sets_cong) auto

definition (in prob_space) tail_events where
  "tail_events A = (\<Inter>n. sigma_sets (space M) (\<Union> (A ` {n..})))"

lemma (in prob_space) tail_events_sets:
  assumes A: "\<And>i::nat. A i \<subseteq> events"
  shows "tail_events A \<subseteq> events"
proof
  fix X assume X: "X \<in> tail_events A"
  let ?A = "(\<Inter>n. sigma_sets (space M) (\<Union> (A ` {n..})))"
  from X have "\<And>n::nat. X \<in> sigma_sets (space M) (\<Union> (A ` {n..}))" by (auto simp: tail_events_def)
  from this[of 0] have "X \<in> sigma_sets (space M) (\<Union>(A ` UNIV))" by simp
  then show "X \<in> events"
    by induct (insert A, auto)
qed

lemma (in prob_space) sigma_algebra_tail_events:
  assumes "\<And>i::nat. sigma_algebra (space M) (A i)"
  shows "sigma_algebra (space M) (tail_events A)"
  unfolding tail_events_def
proof (simp add: sigma_algebra_iff2, safe)
  let ?A = "(\<Inter>n. sigma_sets (space M) (\<Union> (A ` {n..})))"
  interpret A: sigma_algebra "space M" "A i" for i by fact
  { fix X x assume "X \<in> ?A" "x \<in> X"
    then have "\<And>n. X \<in> sigma_sets (space M) (\<Union> (A ` {n..}))" by auto
    from this[of 0] have "X \<in> sigma_sets (space M) (\<Union>(A ` UNIV))" by simp
    then have "X \<subseteq> space M"
      by induct (insert A.sets_into_space, auto)
    with \<open>x \<in> X\<close> show "x \<in> space M" by auto }
  { fix F :: "nat \<Rightarrow> 'a set" and n assume "range F \<subseteq> ?A"
    then show "(\<Union>(F ` UNIV)) \<in> sigma_sets (space M) (\<Union> (A ` {n..}))"
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

  interpret D: Dynkin_system "space M" ?D
  proof (rule Dynkin_systemI)
    fix D assume "D \<in> ?D" then show "D \<subseteq> space M"
      using sets.sets_into_space by auto
  next
    show "space M \<in> ?D"
      using prob_space \<open>X \<subseteq> space M\<close> by (simp add: Int_absorb2)
  next
    fix A assume A: "A \<in> ?D"
    have "prob (X \<inter> (space M - A)) = prob (X - (X \<inter> A))"
      using \<open>X \<subseteq> space M\<close> by (auto intro!: arg_cong[where f=prob])
    also have "\<dots> = prob X - prob (X \<inter> A)"
      using X_in A by (intro finite_measure_Diff) auto
    also have "\<dots> = prob X * prob (space M) - prob X * prob A"
      using A prob_space by auto
    also have "\<dots> = prob X * prob (space M - A)"
      using X_in A sets.sets_into_space
      by (subst finite_measure_Diff) (auto simp: field_simps)
    finally show "space M - A \<in> ?D"
      using A \<open>X \<subseteq> space M\<close> by auto
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
    have "indep_sets (\<lambda>b. sigma_sets (space M) (\<Union>m\<in>case_bool {..n} {Suc n..} b. A m)) UNIV"
    proof (rule indep_sets_collect_sigma)
      have *: "(\<Union>b. case b of True \<Rightarrow> {..n} | False \<Rightarrow> {Suc n..}) = UNIV" (is "?U = _")
        by (simp split: bool.split add: set_eq_iff) (metis not_less_eq_eq)
      with indep show "indep_sets A ?U" by simp
      show "disjoint_family (case_bool {..n} {Suc n..})"
        unfolding disjoint_family_on_def by (auto split: bool.split)
      fix m
      show "Int_stable (A m)"
        unfolding Int_stable_def using A.Int by auto
    qed
    also have "(\<lambda>b. sigma_sets (space M) (\<Union>m\<in>case_bool {..n} {Suc n..} b. A m)) =
      case_bool (sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) (sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m))"
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

  note \<open>X \<in> tail_events A\<close>
  also {
    have "\<And>n. sigma_sets (space M) (\<Union>i\<in>{n..}. A i) \<subseteq> sigma_sets (space M) ?A"
      by (intro sigma_sets_subseteq UN_mono) auto
   then have "tail_events A \<subseteq> sigma_sets (space M) ?A"
      unfolding tail_events_def by auto }
  also have "sigma_sets (space M) ?A = Dynkin (space M) ?A"
  proof (rule sigma_eq_Dynkin)
    { fix B n assume "B \<in> sigma_sets (space M) (\<Union>m\<in>{..n}. A m)"
      then have "B \<subseteq> space M"
        by induct (insert A sets.sets_into_space[of _ M], auto) }
    then show "?A \<subseteq> Pow (space M)" by auto
    show "Int_stable ?A"
    proof (rule Int_stableI)
      fix a assume "a \<in> ?A" then guess n .. note a = this
      fix b assume "b \<in> ?A" then guess m .. note b = this
      interpret Amn: sigma_algebra "space M" "sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        using A sets.sets_into_space[of _ M] by (intro sigma_algebra_sigma_sets) auto
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
  also have "Dynkin (space M) ?A \<subseteq> ?D"
    using \<open>?A \<subseteq> ?D\<close> by (auto intro!: D.Dynkin_subset)
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
      using sigma_algebra_sigma_sets[of "{F i}" "space M"] F1 sets.sets_into_space
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
      using order_trans[OF F1 sets.space_closed]
      by (intro sigma_algebra_sigma_sets) (simp add: sigma_sets_singleton subset_eq)
    have "(\<Inter>n. ?Q n) = (\<Inter>n\<in>{j..}. ?Q n)"
      by (intro decseq_SucI INT_decseq_offset UN_mono) auto
    also have "\<dots> \<in> sigma_sets (space M) (\<Union>i\<in>{j..}. sigma_sets (space M) {F i})"
      using order_trans[OF F1 sets.space_closed]
      by (safe intro!: S.countable_INT S.countable_UN)
         (auto simp: sigma_sets_singleton intro!: sigma_sets.Basic bexI)
    finally show "(\<Inter>n. ?Q n) \<in> sigma_sets (space M) (\<Union>i\<in>{j..}. sigma_sets (space M) {F i})"
      by simp
  qed
qed

lemma (in prob_space) borel_0_1_law_AE:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "indep_events (\<lambda>m. {x\<in>space M. P m x}) UNIV" (is "indep_events ?P _")
  shows "(AE x in M. infinite {m. P m x}) \<or> (AE x in M. finite {m. P m x})"
proof -
  have [measurable]: "\<And>m. {x\<in>space M. P m x} \<in> sets M"
    using assms by (auto simp: indep_events_def)
  have *: "(\<Inter>n. \<Union>m\<in>{n..}. {x \<in> space M. P m x}) \<in> events"
    by simp
  from assms have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<or> prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1"
    by (rule borel_0_1_law)
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1 \<longleftrightarrow> (AE x in M. infinite {m. P m x})"
    using * by (simp add: prob_eq_1)
      (simp add: Bex_def infinite_nat_iff_unbounded_le)
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<longleftrightarrow> (AE x in M. finite {m. P m x})"
    using * by (simp add: prob_eq_0)
      (auto simp add: Ball_def finite_nat_iff_bounded not_less [symmetric])
  finally show ?thesis
    by blast
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
      using subset_trans[OF F(1) sets.space_closed] J A
      by (auto intro!: arg_cong[where f=prob] split: if_split_asm) blast
    also
    from A F have "(\<lambda>j. if j \<in> J then A j else space M) \<in> Pi I F" (is "?A \<in> _")
      by (auto split: if_split_asm)
    with indep have "prob (\<Inter>j\<in>I. ?A j) = (\<Prod>j\<in>I. prob (?A j))"
      by auto
    also have "\<dots> = (\<Prod>j\<in>J. prob (A j))"
      unfolding if_distrib prod.If_cases[OF \<open>finite I\<close>]
      using prob_space \<open>J \<subseteq> I\<close> by (simp add: Int_absorb1 prod.neutral_const)
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
    from closed[OF \<open>i \<in> I\<close>]
    have "sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}
      = sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> E i}"
      unfolding sigma_sets_vimage_commute[OF X, OF \<open>i \<in> I\<close>, symmetric] M'[OF \<open>i \<in> I\<close>]
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
      moreover note Int_stable[OF \<open>i \<in> I\<close>]
      ultimately
      show "a \<inter> b \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
        by (auto simp del: vimage_Int intro!: exI[of _ "A \<inter> B"] dest: Int_stableD)
    qed }
  note indep_sets_X = indep_sets_sigma_sets_iff[OF this]

  { fix i assume "i \<in> I"
    { fix A assume "A \<in> E i"
      with M'[OF \<open>i \<in> I\<close>] have "A \<in> sets (M' i)" by auto
      moreover
      from rv[OF \<open>i\<in>I\<close>] have "X i \<in> measurable M (M' i)" by auto
      ultimately
      have "X i -` A \<inter> space M \<in> sets M" by (auto intro: measurable_sets) }
    with X[OF \<open>i\<in>I\<close>] space[OF \<open>i\<in>I\<close>]
    have "{X i -` A \<inter> space M |A. A \<in> E i} \<subseteq> events"
      "space M \<in> {X i -` A \<inter> space M |A. A \<in> E i}"
      by (auto intro!: exI[of _ "space (M' i)"]) }
  note indep_sets_finite_X = indep_sets_finite[OF I this]

  have "(\<forall>A\<in>\<Pi> i\<in>I. {X i -` A \<inter> space M |A. A \<in> E i}. prob (\<Inter>(A ` I)) = (\<Prod>j\<in>I. prob (A j))) =
    (\<forall>A\<in>\<Pi> i\<in>I. E i. prob ((\<Inter>j\<in>I. X j -` A j) \<inter> space M) = (\<Prod>x\<in>I. prob (X x -` A x \<inter> space M)))"
    (is "?L = ?R")
  proof safe
    fix A assume ?L and A: "A \<in> (\<Pi> i\<in>I. E i)"
    from \<open>?L\<close>[THEN bspec, of "\<lambda>i. X i -` A i \<inter> space M"] A \<open>I \<noteq> {}\<close>
    show "prob ((\<Inter>j\<in>I. X j -` A j) \<inter> space M) = (\<Prod>x\<in>I. prob (X x -` A x \<inter> space M))"
      by (auto simp add: Pi_iff)
  next
    fix A assume ?R and A: "A \<in> (\<Pi> i\<in>I. {X i -` A \<inter> space M |A. A \<in> E i})"
    from A have "\<forall>i\<in>I. \<exists>B. A i = X i -` B \<inter> space M \<and> B \<in> E i" by auto
    from bchoice[OF this] obtain B where B: "\<forall>i\<in>I. A i = X i -` B i \<inter> space M"
      "B \<in> (\<Pi> i\<in>I. E i)" by auto
    from \<open>?R\<close>[THEN bspec, OF B(2)] B(1) \<open>I \<noteq> {}\<close>
    show "prob (\<Inter>(A ` I)) = (\<Prod>j\<in>I. prob (A j))"
      by simp
  qed
  then show ?thesis using \<open>I \<noteq> {}\<close>
    by (simp add: rv indep_vars_def indep_sets_X sigma_sets_X indep_sets_finite_X cong: indep_sets_cong)
qed

lemma (in prob_space) indep_vars_compose:
  assumes "indep_vars M' X I"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "indep_vars N (\<lambda>i. Y i \<circ> X i) I"
  unfolding indep_vars_def
proof
  from rv \<open>indep_vars M' X I\<close>
  show "\<forall>i\<in>I. random_variable (N i) (Y i \<circ> X i)"
    by (auto simp: indep_vars_def)

  have "indep_sets (\<lambda>i. sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}) I"
    using \<open>indep_vars M' X I\<close> by (simp add: indep_vars_def)
  then show "indep_sets (\<lambda>i. sigma_sets (space M) {(Y i \<circ> X i) -` A \<inter> space M |A. A \<in> sets (N i)}) I"
  proof (rule indep_sets_mono_sets)
    fix i assume "i \<in> I"
    with \<open>indep_vars M' X I\<close> have X: "X i \<in> space M \<rightarrow> space (M' i)"
      unfolding indep_vars_def measurable_def by auto
    { fix A assume "A \<in> sets (N i)"
      then have "\<exists>B. (Y i \<circ> X i) -` A \<inter> space M = X i -` B \<inter> space M \<and> B \<in> sets (M' i)"
        by (intro exI[of _ "Y i -` A \<inter> space (M' i)"])
           (auto simp: vimage_comp intro!: measurable_sets rv \<open>i \<in> I\<close> funcset_mem[OF X]) }
    then show "sigma_sets (space M) {(Y i \<circ> X i) -` A \<inter> space M |A. A \<in> sets (N i)} \<subseteq>
      sigma_sets (space M) {X i -` A \<inter> space M |A. A \<in> sets (M' i)}"
      by (intro sigma_sets_subseteq) (auto simp: vimage_comp)
  qed
qed

lemma (in prob_space) indep_vars_compose2:
  assumes "indep_vars M' X I"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> Y i \<in> measurable (M' i) (N i)"
  shows "indep_vars N (\<lambda>i x. Y i (X i x)) I"
  using indep_vars_compose [OF assms] by (simp add: comp_def)

lemma (in prob_space) indep_var_compose:
  assumes "indep_var M1 X1 M2 X2" "Y1 \<in> measurable M1 N1" "Y2 \<in> measurable M2 N2"
  shows "indep_var N1 (Y1 \<circ> X1) N2 (Y2 \<circ> X2)"
proof -
  have "indep_vars (case_bool N1 N2) (\<lambda>b. case_bool Y1 Y2 b \<circ> case_bool X1 X2 b) UNIV"
    using assms
    by (intro indep_vars_compose[where M'="case_bool M1 M2"])
       (auto simp: indep_var_def split: bool.split)
  also have "(\<lambda>b. case_bool Y1 Y2 b \<circ> case_bool X1 X2 b) = case_bool (Y1 \<circ> X1) (Y2 \<circ> X2)"
    by (simp add: fun_eq_iff split: bool.split)
  finally show ?thesis
    unfolding indep_var_def .
qed

lemma (in prob_space) indep_vars_Min:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. Min ((\<lambda>i. X i \<omega>)`I))"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. Min (f`I)) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] borel_measurable_Min) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. Min (f`I)) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. Min ((\<lambda>i. X i \<omega>)`I))"
    by (auto cong: rev_conj_cong)
  finally show ?thesis
    unfolding indep_var_def .
qed

lemma (in prob_space) indep_vars_sum:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] ) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
    by (auto cong: rev_conj_cong)
  finally show ?thesis .
qed

lemma (in prob_space) indep_vars_prod:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. \<Prod>i\<in>I. X i \<omega>)"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. \<Prod>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] ) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. \<Prod>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. \<Prod>i\<in>I. X i \<omega>)"
    by (auto cong: rev_conj_cong)
  finally show ?thesis .
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

lemma (in prob_space) indep_vars_iff_distr_eq_PiM:
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "I \<noteq> {}"
  assumes rv: "\<And>i. random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
    distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
proof -
  let ?P = "\<Pi>\<^sub>M i\<in>I. M' i"
  let ?X = "\<lambda>x. \<lambda>i\<in>I. X i x"
  let ?D = "distr M ?P ?X"
  have X: "random_variable ?P ?X" by (intro measurable_restrict rv)
  interpret D: prob_space ?D by (intro prob_space_distr X)

  let ?D' = "\<lambda>i. distr M (M' i) (X i)"
  let ?P' = "\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i)"
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
      let ?A = "\<lambda>i. \<Pi>\<^sub>E i\<in>I. space (M' i)"
      show "range ?A \<subseteq> prod_algebra I M'" "(\<Union>i. ?A i) = space (Pi\<^sub>M I M')"
        by (auto simp: space_PiM intro!: space_in_prod_algebra cong: prod_algebra_cong)
      { fix i show "emeasure ?D (\<Pi>\<^sub>E i\<in>I. space (M' i)) \<noteq> \<infinity>" by auto }
    next
      fix E assume E: "E \<in> prod_algebra I M'"
      from prod_algebraE[OF E] guess J Y . note J = this

      from E have "E \<in> sets ?P" by (auto simp: sets_PiM)
      then have "emeasure ?D E = emeasure M (?X -` E \<inter> space M)"
        by (simp add: emeasure_distr X)
      also have "?X -` E \<inter> space M = (\<Inter>i\<in>J. X i -` Y i \<inter> space M)"
        using J \<open>I \<noteq> {}\<close> measurable_space[OF rv] by (auto simp: prod_emb_def PiE_iff split: if_split_asm)
      also have "emeasure M (\<Inter>i\<in>J. X i -` Y i \<inter> space M) = (\<Prod> i\<in>J. emeasure M (X i -` Y i \<inter> space M))"
        using \<open>indep_vars M' X I\<close> J \<open>I \<noteq> {}\<close> using indep_varsD[of M' X I J]
        by (auto simp: emeasure_eq_measure prod_ennreal measure_nonneg prod_nonneg)
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
        by (auto intro!: sets.sigma_sets_subset measurable_sets rv)
    next
      fix J Y' assume J: "J \<noteq> {}" "J \<subseteq> I" "finite J"
      assume Y': "\<forall>j\<in>J. Y' j \<in> sigma_sets (space M) {X j -` A \<inter> space M |A. A \<in> sets (M' j)}"
      have "\<forall>j\<in>J. \<exists>Y. Y' j = X j -` Y \<inter> space M \<and> Y \<in> sets (M' j)"
      proof
        fix j assume "j \<in> J"
        from Y'[rule_format, OF this] rv[of j]
        show "\<exists>Y. Y' j = X j -` Y \<inter> space M \<and> Y \<in> sets (M' j)"
          by (subst (asm) sigma_sets_vimage_commute[symmetric, of _ _ "space (M' j)"])
             (auto dest: measurable_space simp: sets.sigma_sets_eq)
      qed
      from bchoice[OF this] obtain Y where
        Y: "\<And>j. j \<in> J \<Longrightarrow> Y' j = X j -` Y j \<inter> space M" "\<And>j. j \<in> J \<Longrightarrow> Y j \<in> sets (M' j)" by auto
      let ?E = "prod_emb I M' J (Pi\<^sub>E J Y)"
      from Y have "(\<Inter>j\<in>J. Y' j) = ?X -` ?E \<inter> space M"
        using J \<open>I \<noteq> {}\<close> measurable_space[OF rv] by (auto simp: prod_emb_def PiE_iff split: if_split_asm)
      then have "emeasure M (\<Inter>j\<in>J. Y' j) = emeasure M (?X -` ?E \<inter> space M)"
        by simp
      also have "\<dots> = emeasure ?D ?E"
        using Y  J by (intro emeasure_distr[symmetric] X sets_PiM_I) auto
      also have "\<dots> = emeasure ?P' ?E"
        using \<open>?D = ?P'\<close> by simp
      also have "\<dots> = (\<Prod> i\<in>J. emeasure (?D' i) (Y i))"
        using P.emeasure_PiM_emb[of J Y] J Y by (simp add: prod_emb_def)
      also have "\<dots> = (\<Prod> i\<in>J. emeasure M (Y' i))"
        using rv J Y by (simp add: emeasure_distr)
      finally have "emeasure M (\<Inter>j\<in>J. Y' j) = (\<Prod> i\<in>J. emeasure M (Y' i))" .
      then show "prob (\<Inter>j\<in>J. Y' j) = (\<Prod> i\<in>J. prob (Y' i))"
        by (auto simp: emeasure_eq_measure prod_ennreal measure_nonneg prod_nonneg)
    qed
  qed
qed

lemma (in prob_space) indep_vars_iff_distr_eq_PiM':
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "I \<noteq> {}"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
           distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
proof -
  from assms obtain j where j: "j \<in> I"
    by auto
  define N' where "N' = (\<lambda>i. if i \<in> I then M' i else M' j)"
  define Y where "Y = (\<lambda>i. if i \<in> I then X i else X j)"
  have rv: "random_variable (N' i) (Y i)" for i
    using j by (auto simp: N'_def Y_def intro: assms)

  have "indep_vars M' X I = indep_vars N' Y I"
    by (intro indep_vars_cong) (auto simp: N'_def Y_def)
  also have "\<dots> \<longleftrightarrow> distr M (\<Pi>\<^sub>M i\<in>I. N' i) (\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i))"
    by (intro indep_vars_iff_distr_eq_PiM rv assms)
  also have "(\<Pi>\<^sub>M i\<in>I. N' i) = (\<Pi>\<^sub>M i\<in>I. M' i)"
    by (intro PiM_cong) (simp_all add: N'_def)
  also have "(\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<lambda>x. \<lambda>i\<in>I. X i x)"
    by (simp_all add: Y_def fun_eq_iff)
  also have "(\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i)) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
    by (intro PiM_cong distr_cong) (simp_all add: N'_def Y_def)
  finally show ?thesis .
qed

lemma (in prob_space) indep_varD:
  assumes indep: "indep_var Ma A Mb B"
  assumes sets: "Xa \<in> sets Ma" "Xb \<in> sets Mb"
  shows "prob ((\<lambda>x. (A x, B x)) -` (Xa \<times> Xb) \<inter> space M) =
    prob (A -` Xa \<inter> space M) * prob (B -` Xb \<inter> space M)"
proof -
  have "prob ((\<lambda>x. (A x, B x)) -` (Xa \<times> Xb) \<inter> space M) =
    prob (\<Inter>i\<in>UNIV. (case_bool A B i -` case_bool Xa Xb i \<inter> space M))"
    by (auto intro!: arg_cong[where f=prob] simp: UNIV_bool)
  also have "\<dots> = (\<Prod>i\<in>UNIV. prob (case_bool A B i -` case_bool Xa Xb i \<inter> space M))"
    using indep unfolding indep_var_def
    by (rule indep_varsD) (auto split: bool.split intro: sets)
  also have "\<dots> = prob (A -` Xa \<inter> space M) * prob (B -` Xb \<inter> space M)"
    unfolding UNIV_bool by simp
  finally show ?thesis .
qed

lemma (in prob_space) prob_indep_random_variable:
  assumes ind[simp]: "indep_var N X N Y"
  assumes [simp]: "A \<in> sets N" "B \<in> sets N"
  shows "\<P>(x in M. X x \<in> A \<and> Y x \<in> B) = \<P>(x in M. X x \<in> A) * \<P>(x in M. Y x \<in> B)"
proof-
  have  " \<P>(x in M. (X x)\<in>A \<and>  (Y x)\<in> B ) = prob ((\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M)"
    by (auto intro!: arg_cong[where f= prob])
  also have "...=  prob (X -` A \<inter> space M) * prob (Y -` B \<inter> space M)"
    by (auto intro!: indep_varD[where Ma=N and Mb=N])
  also have "... = \<P>(x in M. X x \<in> A) * \<P>(x in M. Y x \<in> B)"
    by (auto intro!: arg_cong2[where f= "(*)"] arg_cong[where f= prob])
  finally show ?thesis .
qed

lemma (in prob_space)
  assumes "indep_var S X T Y"
  shows indep_var_rv1: "random_variable S X"
    and indep_var_rv2: "random_variable T Y"
proof -
  have "\<forall>i\<in>UNIV. random_variable (case_bool S T i) (case_bool X Y i)"
    using assms unfolding indep_var_def indep_vars_def by auto
  then show "random_variable S X" "random_variable T Y"
    unfolding UNIV_bool by auto
qed

lemma (in prob_space) indep_var_distribution_eq:
  "indep_var S X T Y \<longleftrightarrow> random_variable S X \<and> random_variable T Y \<and>
    distr M S X \<Otimes>\<^sub>M distr M T Y = distr M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))" (is "_ \<longleftrightarrow> _ \<and> _ \<and> ?S \<Otimes>\<^sub>M ?T = ?J")
proof safe
  assume "indep_var S X T Y"
  then show rvs: "random_variable S X" "random_variable T Y"
    by (blast dest: indep_var_rv1 indep_var_rv2)+
  then have XY: "random_variable (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
    by (rule measurable_Pair)

  interpret X: prob_space ?S by (rule prob_space_distr) fact
  interpret Y: prob_space ?T by (rule prob_space_distr) fact
  interpret XY: pair_prob_space ?S ?T ..
  show "?S \<Otimes>\<^sub>M ?T = ?J"
  proof (rule pair_measure_eqI)
    show "sigma_finite_measure ?S" ..
    show "sigma_finite_measure ?T" ..

    fix A B assume A: "A \<in> sets ?S" and B: "B \<in> sets ?T"
    have "emeasure ?J (A \<times> B) = emeasure M ((\<lambda>x. (X x, Y x)) -` (A \<times> B) \<inter> space M)"
      using A B by (intro emeasure_distr[OF XY]) auto
    also have "\<dots> = emeasure M (X -` A \<inter> space M) * emeasure M (Y -` B \<inter> space M)"
      using indep_varD[OF \<open>indep_var S X T Y\<close>, of A B] A B
      by (simp add: emeasure_eq_measure measure_nonneg ennreal_mult)
    also have "\<dots> = emeasure ?S A * emeasure ?T B"
      using rvs A B by (simp add: emeasure_distr)
    finally show "emeasure ?S A * emeasure ?T B = emeasure ?J (A \<times> B)" by simp
  qed simp
next
  assume rvs: "random_variable S X" "random_variable T Y"
  then have XY: "random_variable (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x))"
    by (rule measurable_Pair)

  let ?S = "distr M S X" and ?T = "distr M T Y"
  interpret X: prob_space ?S by (rule prob_space_distr) fact
  interpret Y: prob_space ?T by (rule prob_space_distr) fact
  interpret XY: pair_prob_space ?S ?T ..

  assume "?S \<Otimes>\<^sub>M ?T = ?J"

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
        using \<open>X \<in> measurable M S\<close> by (auto intro: measurable_sets) }
      { fix A assume "A \<in> sets T" then show "Y -` A \<inter> space M \<in> sets M"
        using \<open>Y \<in> measurable M T\<close> by (auto intro: measurable_sets) }
    next
      fix A B assume ab: "A \<in> sets S" "B \<in> sets T"
      then have "prob ((X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M)) = emeasure ?J (A \<times> B)"
        using XY by (auto simp add: emeasure_distr emeasure_eq_measure measure_nonneg intro!: arg_cong[where f="prob"])
      also have "\<dots> = emeasure (?S \<Otimes>\<^sub>M ?T) (A \<times> B)"
        unfolding \<open>?S \<Otimes>\<^sub>M ?T = ?J\<close> ..
      also have "\<dots> = emeasure ?S A * emeasure ?T B"
        using ab by (simp add: Y.emeasure_pair_measure_Times)
      finally show "prob ((X -` A \<inter> space M) \<inter> (Y -` B \<inter> space M)) =
        prob (X -` A \<inter> space M) * prob (Y -` B \<inter> space M)"
        using rvs ab by (simp add: emeasure_eq_measure emeasure_distr measure_nonneg ennreal_mult[symmetric])
    qed
  qed
qed

lemma (in prob_space) distributed_joint_indep:
  assumes S: "sigma_finite_measure S" and T: "sigma_finite_measure T"
  assumes X: "distributed M S X Px" and Y: "distributed M T Y Py"
  assumes indep: "indep_var S X T Y"
  shows "distributed M (S \<Otimes>\<^sub>M T) (\<lambda>x. (X x, Y x)) (\<lambda>(x, y). Px x * Py y)"
  using indep_var_distribution_eq[of S X T Y] indep
  by (intro distributed_joint_indep'[OF S T X Y]) auto

lemma (in prob_space) indep_vars_nn_integral:
  assumes I: "finite I" "indep_vars (\<lambda>_. borel) X I" "\<And>i \<omega>. i \<in> I \<Longrightarrow> 0 \<le> X i \<omega>"
  shows "(\<integral>\<^sup>+\<omega>. (\<Prod>i\<in>I. X i \<omega>) \<partial>M) = (\<Prod>i\<in>I. \<integral>\<^sup>+\<omega>. X i \<omega> \<partial>M)"
proof cases
  assume "I \<noteq> {}"
  define Y where [abs_def]: "Y i \<omega> = (if i \<in> I then X i \<omega> else 0)" for i \<omega>
  { fix i have "i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using I(2) by (cases "i\<in>I") (auto simp: indep_vars_def) }
  note rv_X = this

  { fix i have "random_variable borel (Y i)"
    using I(2) by (cases "i\<in>I") (auto simp: Y_def rv_X) }
  note rv_Y = this[measurable]

  interpret Y: prob_space "distr M borel (Y i)" for i
    using I(2) by (cases "i \<in> I") (auto intro!: prob_space_distr simp: indep_vars_def prob_space_return)
  interpret product_sigma_finite "\<lambda>i. distr M borel (Y i)"
    ..

  have indep_Y: "indep_vars (\<lambda>i. borel) Y I"
    by (rule indep_vars_cong[THEN iffD1, OF _ _ _ I(2)]) (auto simp: Y_def)

  have "(\<integral>\<^sup>+\<omega>. (\<Prod>i\<in>I. X i \<omega>) \<partial>M) = (\<integral>\<^sup>+\<omega>. (\<Prod>i\<in>I. Y i \<omega>) \<partial>M)"
    using I(3) by (auto intro!: nn_integral_cong prod.cong simp add: Y_def max_def)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<Prod>i\<in>I. \<omega> i) \<partial>distr M (Pi\<^sub>M I (\<lambda>i. borel)) (\<lambda>x. \<lambda>i\<in>I. Y i x))"
    by (subst nn_integral_distr) auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<Prod>i\<in>I. \<omega> i) \<partial>Pi\<^sub>M I (\<lambda>i. distr M borel (Y i)))"
    unfolding indep_vars_iff_distr_eq_PiM[THEN iffD1, OF \<open>I \<noteq> {}\<close> rv_Y indep_Y] ..
  also have "\<dots> = (\<Prod>i\<in>I. (\<integral>\<^sup>+\<omega>. \<omega> \<partial>distr M borel (Y i)))"
    by (rule product_nn_integral_prod) (auto intro: \<open>finite I\<close>)
  also have "\<dots> = (\<Prod>i\<in>I. \<integral>\<^sup>+\<omega>. X i \<omega> \<partial>M)"
    by (intro prod.cong nn_integral_cong) (auto simp: nn_integral_distr Y_def rv_X)
  finally show ?thesis .
qed (simp add: emeasure_space_1)

lemma (in prob_space)
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b::{real_normed_field, banach, second_countable_topology}"
  assumes I: "finite I" "indep_vars (\<lambda>_. borel) X I" "\<And>i. i \<in> I \<Longrightarrow> integrable M (X i)"
  shows indep_vars_lebesgue_integral: "(\<integral>\<omega>. (\<Prod>i\<in>I. X i \<omega>) \<partial>M) = (\<Prod>i\<in>I. \<integral>\<omega>. X i \<omega> \<partial>M)" (is ?eq)
    and indep_vars_integrable: "integrable M (\<lambda>\<omega>. (\<Prod>i\<in>I. X i \<omega>))" (is ?int)
proof (induct rule: case_split)
  assume "I \<noteq> {}"
  define Y where [abs_def]: "Y i \<omega> = (if i \<in> I then X i \<omega> else 0)" for i \<omega>
  { fix i have "i \<in> I \<Longrightarrow> random_variable borel (X i)"
    using I(2) by (cases "i\<in>I") (auto simp: indep_vars_def) }
  note rv_X = this[measurable]

  { fix i have "random_variable borel (Y i)"
    using I(2) by (cases "i\<in>I") (auto simp: Y_def rv_X) }
  note rv_Y = this[measurable]

  { fix i have "integrable M (Y i)"
    using I(3) by (cases "i\<in>I") (auto simp: Y_def) }
  note int_Y = this

  interpret Y: prob_space "distr M borel (Y i)" for i
    using I(2) by (cases "i \<in> I") (auto intro!: prob_space_distr simp: indep_vars_def prob_space_return)
  interpret product_sigma_finite "\<lambda>i. distr M borel (Y i)"
    ..

  have indep_Y: "indep_vars (\<lambda>i. borel) Y I"
    by (rule indep_vars_cong[THEN iffD1, OF _ _ _ I(2)]) (auto simp: Y_def)

  have "(\<integral>\<omega>. (\<Prod>i\<in>I. X i \<omega>) \<partial>M) = (\<integral>\<omega>. (\<Prod>i\<in>I. Y i \<omega>) \<partial>M)"
    using I(3) by (simp add: Y_def)
  also have "\<dots> = (\<integral>\<omega>. (\<Prod>i\<in>I. \<omega> i) \<partial>distr M (Pi\<^sub>M I (\<lambda>i. borel)) (\<lambda>x. \<lambda>i\<in>I. Y i x))"
    by (subst integral_distr) auto
  also have "\<dots> = (\<integral>\<omega>. (\<Prod>i\<in>I. \<omega> i) \<partial>Pi\<^sub>M I (\<lambda>i. distr M borel (Y i)))"
    unfolding indep_vars_iff_distr_eq_PiM[THEN iffD1, OF \<open>I \<noteq> {}\<close> rv_Y indep_Y] ..
  also have "\<dots> = (\<Prod>i\<in>I. (\<integral>\<omega>. \<omega> \<partial>distr M borel (Y i)))"
    by (rule product_integral_prod) (auto intro: \<open>finite I\<close> simp: integrable_distr_eq int_Y)
  also have "\<dots> = (\<Prod>i\<in>I. \<integral>\<omega>. X i \<omega> \<partial>M)"
    by (intro prod.cong integral_cong)
       (auto simp: integral_distr Y_def rv_X)
  finally show ?eq .

  have "integrable (distr M (Pi\<^sub>M I (\<lambda>i. borel)) (\<lambda>x. \<lambda>i\<in>I. Y i x)) (\<lambda>\<omega>. (\<Prod>i\<in>I. \<omega> i))"
    unfolding indep_vars_iff_distr_eq_PiM[THEN iffD1, OF \<open>I \<noteq> {}\<close> rv_Y indep_Y]
    by (intro product_integrable_prod[OF \<open>finite I\<close>])
       (simp add: integrable_distr_eq int_Y)
  then show ?int
    by (simp add: integrable_distr_eq Y_def)
qed (simp_all add: prob_space)

lemma (in prob_space)
  fixes X1 X2 :: "'a \<Rightarrow> 'b::{real_normed_field, banach, second_countable_topology}"
  assumes "indep_var borel X1 borel X2" "integrable M X1" "integrable M X2"
  shows indep_var_lebesgue_integral: "(\<integral>\<omega>. X1 \<omega> * X2 \<omega> \<partial>M) = (\<integral>\<omega>. X1 \<omega> \<partial>M) * (\<integral>\<omega>. X2 \<omega> \<partial>M)" (is ?eq)
    and indep_var_integrable: "integrable M (\<lambda>\<omega>. X1 \<omega> * X2 \<omega>)" (is ?int)
unfolding indep_var_def
proof -
  have *: "(\<lambda>\<omega>. X1 \<omega> * X2 \<omega>) = (\<lambda>\<omega>. \<Prod>i\<in>UNIV. (case_bool X1 X2 i \<omega>))"
    by (simp add: UNIV_bool mult.commute)
  have **: "(\<lambda> _. borel) = case_bool borel borel"
    by (rule ext, metis (full_types) bool.simps(3) bool.simps(4))
  show ?eq
    apply (subst *)
    apply (subst indep_vars_lebesgue_integral)
    apply (auto)
    apply (subst **, subst indep_var_def [symmetric], rule assms)
    apply (simp split: bool.split add: assms)
    by (simp add: UNIV_bool mult.commute)
  show ?int
    apply (subst *)
    apply (rule indep_vars_integrable)
    apply auto
    apply (subst **, subst indep_var_def [symmetric], rule assms)
    by (simp split: bool.split add: assms)
qed

end

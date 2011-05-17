(*  Title:      HOL/Probability/Independent_Family.thy
    Author:     Johannes Hölzl, TU München
*)

header {* Independent families of events, event sets, and random variables *}

theory Independent_Family
  imports Probability_Measure
begin

definition (in prob_space)
  "indep_events A I \<longleftrightarrow> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j)))"

definition (in prob_space)
  "indep_sets F I \<longleftrightarrow> (\<forall>i\<in>I. F i \<subseteq> events) \<and> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow>
    (\<forall>A\<in>(\<Pi> j\<in>J. F j). prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))))"

definition (in prob_space)
  "indep_sets2 A B \<longleftrightarrow> indep_sets (bool_case A B) UNIV"

definition (in prob_space)
  "indep_rv M' X I \<longleftrightarrow>
    (\<forall>i\<in>I. random_variable (M' i) (X i)) \<and>
    indep_sets (\<lambda>i. sigma_sets (space M) { X i -` A \<inter> space M | A. A \<in> sets (M' i)}) I"

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

lemma (in prob_space) indep_setsI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> events"
    and "\<And>A J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> (\<forall>j\<in>J. A j \<in> F j) \<Longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  shows "indep_sets F I"
  using assms unfolding indep_sets_def by (auto simp: Pi_iff)

lemma (in prob_space) indep_setsD:
  assumes "indep_sets F I" and "J \<subseteq> I" "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> F j"
  shows "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  using assms unfolding indep_sets_def by auto

lemma dynkin_systemI':
  assumes 1: "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M"
  assumes empty: "{} \<in> sets M"
  assumes Diff: "\<And> A. A \<in> sets M \<Longrightarrow> space M - A \<in> sets M"
  assumes 2: "\<And> A. disjoint_family A \<Longrightarrow> range A \<subseteq> sets M
          \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  shows "dynkin_system M"
proof -
  from Diff[OF empty] have "space M \<in> sets M" by auto
  from 1 this Diff 2 show ?thesis
    by (intro dynkin_systemI) auto
qed

lemma (in prob_space) indep_sets_dynkin:
  assumes indep: "indep_sets F I"
  shows "indep_sets (\<lambda>i. sets (dynkin \<lparr> space = space M, sets = F i \<rparr>)) I"
    (is "indep_sets ?F I")
proof (subst indep_sets_finite_index_sets, intro allI impI ballI)
  fix J assume "finite J" "J \<subseteq> I" "J \<noteq> {}"
  with indep have "indep_sets F J"
    by (subst (asm) indep_sets_finite_index_sets) auto
  { fix J K assume "indep_sets F K"
    let "?G S i" = "if i \<in> S then ?F i else F i"
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
      have "dynkin_system \<lparr> space = space M, sets = ?D \<rparr>"
      proof (rule dynkin_systemI', simp_all, safe)
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
            using A_sets sets_into_space X `J \<noteq> {}`
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
      then have mono: "sets (dynkin \<lparr>space = space M, sets = G j\<rparr>) \<subseteq>
        sets \<lparr>space = space M, sets = {E \<in> events. indep_sets (G(j := {E})) K}\<rparr>"
      proof (rule dynkin_system.dynkin_subset, simp_all, safe)
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
      then have "indep_sets (G(j:=sets (dynkin \<lparr>space = space M, sets = G j\<rparr>))) K"
        by (rule indep_sets_mono_sets) (insert mono, auto)
      then show ?case
        by (rule indep_sets_mono_sets) (insert `j \<in> K` `j \<notin> J`, auto simp: G_def)
    qed (insert `indep_sets F K`, simp) }
  from this[OF `indep_sets F J` `finite J` subset_refl]
  show "indep_sets (\<lambda>i. sets (dynkin \<lparr> space = space M, sets = F i \<rparr>)) J"
    by (rule indep_sets_mono_sets) auto
qed

lemma (in prob_space) indep_sets_sigma:
  assumes indep: "indep_sets F I"
  assumes stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable \<lparr> space = space M, sets = F i \<rparr>"
  shows "indep_sets (\<lambda>i. sets (sigma \<lparr> space = space M, sets = F i \<rparr>)) I"
proof -
  from indep_sets_dynkin[OF indep]
  show ?thesis
  proof (rule indep_sets_mono_sets, subst sigma_eq_dynkin, simp_all add: stable)
    fix i assume "i \<in> I"
    with indep have "F i \<subseteq> events" by (auto simp: indep_sets_def)
    with sets_into_space show "F i \<subseteq> Pow (space M)" by auto
  qed
qed

lemma (in prob_space) indep_sets_sigma_sets:
  assumes "indep_sets F I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> Int_stable \<lparr> space = space M, sets = F i \<rparr>"
  shows "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I"
  using indep_sets_sigma[OF assms] by (simp add: sets_sigma)

lemma (in prob_space) indep_sets2_eq:
  "indep_sets2 A B \<longleftrightarrow> A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  unfolding indep_sets2_def
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

lemma (in prob_space) indep_sets2_sigma_sets:
  assumes "indep_sets2 A B"
  assumes A: "Int_stable \<lparr> space = space M, sets = A \<rparr>"
  assumes B: "Int_stable \<lparr> space = space M, sets = B \<rparr>"
  shows "indep_sets2 (sigma_sets (space M) A) (sigma_sets (space M) B)"
proof -
  have "indep_sets (\<lambda>i. sigma_sets (space M) (case i of True \<Rightarrow> A | False \<Rightarrow> B)) UNIV"
  proof (rule indep_sets_sigma_sets)
    show "indep_sets (bool_case A B) UNIV"
      by (rule `indep_sets2 A B`[unfolded indep_sets2_def])
    fix i show "Int_stable \<lparr>space = space M, sets = case i of True \<Rightarrow> A | False \<Rightarrow> B\<rparr>"
      using A B by (cases i) auto
  qed
  then show ?thesis
    unfolding indep_sets2_def
    by (rule indep_sets_mono_sets) (auto split: bool.split)
qed

end

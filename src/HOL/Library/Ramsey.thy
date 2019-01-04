(*  Title:      HOL/Library/Ramsey.thy
    Author:     Tom Ridge.  Converted to structured Isar by L C Paulson
*)

section \<open>Ramsey's Theorem\<close>

theory Ramsey
  imports Infinite_Set
begin

subsection \<open>Finite Ramsey theorem(s)\<close>

text \<open>
  To distinguish the finite and infinite ones, lower and upper case
  names are used.

  This is the most basic version in terms of cliques and independent
  sets, i.e. the version for graphs and 2 colours.
\<close>

definition "clique V E \<longleftrightarrow> (\<forall>v\<in>V. \<forall>w\<in>V. v \<noteq> w \<longrightarrow> {v, w} \<in> E)"
definition "indep V E \<longleftrightarrow> (\<forall>v\<in>V. \<forall>w\<in>V. v \<noteq> w \<longrightarrow> {v, w} \<notin> E)"

lemma ramsey2:
  "\<exists>r\<ge>1. \<forall>(V::'a set) (E::'a set set). finite V \<and> card V \<ge> r \<longrightarrow>
    (\<exists>R \<subseteq> V. card R = m \<and> clique R E \<or> card R = n \<and> indep R E)"
  (is "\<exists>r\<ge>1. ?R m n r")
proof (induct k \<equiv> "m + n" arbitrary: m n)
  case 0
  show ?case (is "\<exists>r. ?Q r")
  proof
    from 0 show "?Q 1"
      by (clarsimp simp: indep_def) (metis card.empty emptyE empty_subsetI)
  qed
next
  case (Suc k)
  consider "m = 0 \<or> n = 0" | "m \<noteq> 0" "n \<noteq> 0" by auto
  then show ?case (is "\<exists>r. ?Q r")
  proof cases
    case 1
    then have "?Q 1"
      by (simp add: clique_def) (meson card_empty empty_iff empty_subsetI indep_def)
    then show ?thesis ..
  next
    case 2
    with Suc(2) have "k = (m - 1) + n" "k = m + (n - 1)" by auto
    from this [THEN Suc(1)]
    obtain r1 r2 where "r1 \<ge> 1" "r2 \<ge> 1" "?R (m - 1) n r1" "?R m (n - 1) r2" by auto
    then have "r1 + r2 \<ge> 1" by arith
    moreover have "?R m n (r1 + r2)" (is "\<forall>V E. _ \<longrightarrow> ?EX V E m n")
    proof clarify
      fix V :: "'a set"
      fix E :: "'a set set"
      assume "finite V" "r1 + r2 \<le> card V"
      with \<open>r1 \<ge> 1\<close> have "V \<noteq> {}" by auto
      then obtain v where "v \<in> V" by blast
      let ?M = "{w \<in> V. w \<noteq> v \<and> {v, w} \<in> E}"
      let ?N = "{w \<in> V. w \<noteq> v \<and> {v, w} \<notin> E}"
      from \<open>v \<in> V\<close> have "V = insert v (?M \<union> ?N)" by auto
      then have "card V = card (insert v (?M \<union> ?N))" by metis
      also from \<open>finite V\<close> have "\<dots> = card ?M + card ?N + 1"
        by (fastforce intro: card_Un_disjoint)
      finally have "card V = card ?M + card ?N + 1" .
      with \<open>r1 + r2 \<le> card V\<close> have "r1 + r2 \<le> card ?M + card ?N + 1" by simp
      then consider "r1 \<le> card ?M" | "r2 \<le> card ?N" by arith
      then show "?EX V E m n"
      proof cases
        case 1
        from \<open>finite V\<close> have "finite ?M" by auto
        with \<open>?R (m - 1) n r1\<close> and 1 have "?EX ?M E (m - 1) n" by blast
        then obtain R where "R \<subseteq> ?M" "v \<notin> R"
          and CI: "card R = m - 1 \<and> clique R E \<or> card R = n \<and> indep R E" (is "?C \<or> ?I")
          by blast
        from \<open>R \<subseteq> ?M\<close> have "R \<subseteq> V" by auto
        with \<open>finite V\<close> have "finite R" by (metis finite_subset)
        from CI show ?thesis
        proof
          assume "?I"
          with \<open>R \<subseteq> V\<close> show ?thesis by blast
        next
          assume "?C"
          with \<open>R \<subseteq> ?M\<close> have *: "clique (insert v R) E"
            by (auto simp: clique_def insert_commute)
          from \<open>?C\<close> \<open>finite R\<close> \<open>v \<notin> R\<close> \<open>m \<noteq> 0\<close> have "card (insert v R) = m" by simp
          with \<open>R \<subseteq> V\<close> \<open>v \<in> V\<close> * show ?thesis by (metis insert_subset)
        qed
      next
        case 2
        from \<open>finite V\<close> have "finite ?N" by auto
        with \<open>?R m (n - 1) r2\<close> 2 have "?EX ?N E m (n - 1)" by blast
        then obtain R where "R \<subseteq> ?N" "v \<notin> R"
          and CI: "card R = m \<and> clique R E \<or> card R = n - 1 \<and> indep R E" (is "?C \<or> ?I")
          by blast
        from \<open>R \<subseteq> ?N\<close> have "R \<subseteq> V" by auto
        with \<open>finite V\<close> have "finite R" by (metis finite_subset)
        from CI show ?thesis
        proof
          assume "?C"
          with \<open>R \<subseteq> V\<close> show ?thesis by blast
        next
          assume "?I"
          with \<open>R \<subseteq> ?N\<close> have *: "indep (insert v R) E"
            by (auto simp: indep_def insert_commute)
          from \<open>?I\<close> \<open>finite R\<close> \<open>v \<notin> R\<close> \<open>n \<noteq> 0\<close> have "card (insert v R) = n" by simp
          with \<open>R \<subseteq> V\<close> \<open>v \<in> V\<close> * show ?thesis by (metis insert_subset)
        qed
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed


subsection \<open>Preliminaries\<close>

subsubsection \<open>``Axiom'' of Dependent Choice\<close>

primrec choice :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> 'a"
  where \<comment> \<open>An integer-indexed chain of choices\<close>
    choice_0: "choice P r 0 = (SOME x. P x)"
  | choice_Suc: "choice P r (Suc n) = (SOME y. P y \<and> (choice P r n, y) \<in> r)"

lemma choice_n:
  assumes P0: "P x0"
    and Pstep: "\<And>x. P x \<Longrightarrow> \<exists>y. P y \<and> (x, y) \<in> r"
  shows "P (choice P r n)"
proof (induct n)
  case 0
  show ?case by (force intro: someI P0)
next
  case Suc
  then show ?case by (auto intro: someI2_ex [OF Pstep])
qed

lemma dependent_choice:
  assumes trans: "trans r"
    and P0: "P x0"
    and Pstep: "\<And>x. P x \<Longrightarrow> \<exists>y. P y \<and> (x, y) \<in> r"
  obtains f :: "nat \<Rightarrow> 'a" where "\<And>n. P (f n)" and "\<And>n m. n < m \<Longrightarrow> (f n, f m) \<in> r"
proof
  fix n
  show "P (choice P r n)"
    by (blast intro: choice_n [OF P0 Pstep])
next
  fix n m :: nat
  assume "n < m"
  from Pstep [OF choice_n [OF P0 Pstep]] have "(choice P r k, choice P r (Suc k)) \<in> r" for k
    by (auto intro: someI2_ex)
  then show "(choice P r n, choice P r m) \<in> r"
    by (auto intro: less_Suc_induct [OF \<open>n < m\<close>] transD [OF trans])
qed


subsubsection \<open>Partitions of a Set\<close>

definition part :: "nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> nat) \<Rightarrow> bool"
  \<comment> \<open>the function \<^term>\<open>f\<close> partitions the \<^term>\<open>r\<close>-subsets of the typically
      infinite set \<^term>\<open>Y\<close> into \<^term>\<open>s\<close> distinct categories.\<close>
  where "part r s Y f \<longleftrightarrow> (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = r \<longrightarrow> f X < s)"

text \<open>For induction, we decrease the value of \<^term>\<open>r\<close> in partitions.\<close>
lemma part_Suc_imp_part:
  "\<lbrakk>infinite Y; part (Suc r) s Y f; y \<in> Y\<rbrakk> \<Longrightarrow> part r s (Y - {y}) (\<lambda>u. f (insert y u))"
  apply (simp add: part_def)
  apply clarify
  apply (drule_tac x="insert y X" in spec)
  apply force
  done

lemma part_subset: "part r s YY f \<Longrightarrow> Y \<subseteq> YY \<Longrightarrow> part r s Y f"
  unfolding part_def by blast


subsection \<open>Ramsey's Theorem: Infinitary Version\<close>

lemma Ramsey_induction:
  fixes s r :: nat
    and YY :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  assumes "infinite YY" "part r s YY f"
  shows "\<exists>Y' t'. Y' \<subseteq> YY \<and> infinite Y' \<and> t' < s \<and> (\<forall>X. X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> f X = t')"
  using assms
proof (induct r arbitrary: YY f)
  case 0
  then show ?case
    by (auto simp add: part_def card_eq_0_iff cong: conj_cong)
next
  case (Suc r)
  show ?case
  proof -
    from Suc.prems infinite_imp_nonempty obtain yy where yy: "yy \<in> YY"
      by blast
    let ?ramr = "{((y, Y, t), (y', Y', t')). y' \<in> Y \<and> Y' \<subseteq> Y}"
    let ?propr = "\<lambda>(y, Y, t).
                 y \<in> YY \<and> y \<notin> Y \<and> Y \<subseteq> YY \<and> infinite Y \<and> t < s
                 \<and> (\<forall>X. X\<subseteq>Y \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert y) X = t)"
    from Suc.prems have infYY': "infinite (YY - {yy})" by auto
    from Suc.prems have partf': "part r s (YY - {yy}) (f \<circ> insert yy)"
      by (simp add: o_def part_Suc_imp_part yy)
    have transr: "trans ?ramr" by (force simp add: trans_def)
    from Suc.hyps [OF infYY' partf']
    obtain Y0 and t0 where "Y0 \<subseteq> YY - {yy}" "infinite Y0" "t0 < s"
      "X \<subseteq> Y0 \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yy) X = t0" for X
      by blast
    with yy have propr0: "?propr(yy, Y0, t0)" by blast
    have proprstep: "\<exists>y. ?propr y \<and> (x, y) \<in> ?ramr" if x: "?propr x" for x
    proof (cases x)
      case (fields yx Yx tx)
      with x obtain yx' where yx': "yx' \<in> Yx"
        by (blast dest: infinite_imp_nonempty)
      from fields x have infYx': "infinite (Yx - {yx'})" by auto
      with fields x yx' Suc.prems have partfx': "part r s (Yx - {yx'}) (f \<circ> insert yx')"
        by (simp add: o_def part_Suc_imp_part part_subset [where YY=YY and Y=Yx])
      from Suc.hyps [OF infYx' partfx'] obtain Y' and t'
        where Y': "Y' \<subseteq> Yx - {yx'}" "infinite Y'" "t' < s"
          "X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yx') X = t'" for X
        by blast
      from fields x Y' yx' have "?propr (yx', Y', t') \<and> (x, (yx', Y', t')) \<in> ?ramr"
        by blast
      then show ?thesis ..
    qed
    from dependent_choice [OF transr propr0 proprstep]
    obtain g where pg: "?propr (g n)" and rg: "n < m \<Longrightarrow> (g n, g m) \<in> ?ramr" for n m :: nat
      by blast
    let ?gy = "fst \<circ> g"
    let ?gt = "snd \<circ> snd \<circ> g"
    have rangeg: "\<exists>k. range ?gt \<subseteq> {..<k}"
    proof (intro exI subsetI)
      fix x
      assume "x \<in> range ?gt"
      then obtain n where "x = ?gt n" ..
      with pg [of n] show "x \<in> {..<s}" by (cases "g n") auto
    qed
    have "finite (range ?gt)"
      by (simp add: finite_nat_iff_bounded rangeg)
    then obtain s' and n' where s': "s' = ?gt n'" and infeqs': "infinite {n. ?gt n = s'}"
      by (rule inf_img_fin_domE) (auto simp add: vimage_def intro: infinite_UNIV_nat)
    with pg [of n'] have less': "s'<s" by (cases "g n'") auto
    have inj_gy: "inj ?gy"
    proof (rule linorder_injI)
      fix m m' :: nat
      assume "m < m'"
      from rg [OF this] pg [of m] show "?gy m \<noteq> ?gy m'"
        by (cases "g m", cases "g m'") auto
    qed
    show ?thesis
    proof (intro exI conjI)
      from pg show "?gy ` {n. ?gt n = s'} \<subseteq> YY"
        by (auto simp add: Let_def split_beta)
      from infeqs' show "infinite (?gy ` {n. ?gt n = s'})"
        by (blast intro: inj_gy [THEN subset_inj_on] dest: finite_imageD)
      show "s' < s" by (rule less')
      show "\<forall>X. X \<subseteq> ?gy ` {n. ?gt n = s'} \<and> finite X \<and> card X = Suc r \<longrightarrow> f X = s'"
      proof -
        have "f X = s'"
          if X: "X \<subseteq> ?gy ` {n. ?gt n = s'}"
          and cardX: "finite X" "card X = Suc r"
          for X
        proof -
          from X obtain AA where AA: "AA \<subseteq> {n. ?gt n = s'}" and Xeq: "X = ?gy`AA"
            by (auto simp add: subset_image_iff)
          with cardX have "AA \<noteq> {}" by auto
          then have AAleast: "(LEAST x. x \<in> AA) \<in> AA" by (auto intro: LeastI_ex)
          show ?thesis
          proof (cases "g (LEAST x. x \<in> AA)")
            case (fields ya Ya ta)
            with AAleast Xeq have ya: "ya \<in> X" by (force intro!: rev_image_eqI)
            then have "f X = f (insert ya (X - {ya}))" by (simp add: insert_absorb)
            also have "\<dots> = ta"
            proof -
              have *: "X - {ya} \<subseteq> Ya"
              proof
                fix x assume x: "x \<in> X - {ya}"
                then obtain a' where xeq: "x = ?gy a'" and a': "a' \<in> AA"
                  by (auto simp add: Xeq)
                with fields x have "a' \<noteq> (LEAST x. x \<in> AA)" by auto
                with Least_le [of "\<lambda>x. x \<in> AA", OF a'] have "(LEAST x. x \<in> AA) < a'"
                  by arith
                from xeq fields rg [OF this] show "x \<in> Ya" by auto
              qed
              have "card (X - {ya}) = r"
                by (simp add: cardX ya)
              with pg [of "LEAST x. x \<in> AA"] fields cardX * show ?thesis
                by (auto simp del: insert_Diff_single)
            qed
            also from AA AAleast fields have "\<dots> = s'" by auto
            finally show ?thesis .
          qed
        qed
        then show ?thesis by blast
      qed
    qed
  qed
qed


theorem Ramsey:
  fixes s r :: nat
    and Z :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  shows
   "\<lbrakk>infinite Z;
      \<forall>X. X \<subseteq> Z \<and> finite X \<and> card X = r \<longrightarrow> f X < s\<rbrakk>
    \<Longrightarrow> \<exists>Y t. Y \<subseteq> Z \<and> infinite Y \<and> t < s
            \<and> (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = r \<longrightarrow> f X = t)"
  by (blast intro: Ramsey_induction [unfolded part_def])


corollary Ramsey2:
  fixes s :: nat
    and Z :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  assumes infZ: "infinite Z"
    and part: "\<forall>x\<in>Z. \<forall>y\<in>Z. x \<noteq> y \<longrightarrow> f {x, y} < s"
  shows "\<exists>Y t. Y \<subseteq> Z \<and> infinite Y \<and> t < s \<and> (\<forall>x\<in>Y. \<forall>y\<in>Y. x\<noteq>y \<longrightarrow> f {x, y} = t)"
proof -
  from part have part2: "\<forall>X. X \<subseteq> Z \<and> finite X \<and> card X = 2 \<longrightarrow> f X < s"
    by (fastforce simp add: eval_nat_numeral card_Suc_eq)
  obtain Y t where *:
    "Y \<subseteq> Z" "infinite Y" "t < s" "(\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = 2 \<longrightarrow> f X = t)"
    by (insert Ramsey [OF infZ part2]) auto
  then have "\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow> f {x, y} = t" by auto
  with * show ?thesis by iprover
qed


subsection \<open>Disjunctive Well-Foundedness\<close>

text \<open>
  An application of Ramsey's theorem to program termination. See
  @{cite "Podelski-Rybalchenko"}.
\<close>

definition disj_wf :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "disj_wf r \<longleftrightarrow> (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf (T i)) \<and> r = (\<Union>i<n. T i))"

definition transition_idx :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> nat set \<Rightarrow> nat"
  where "transition_idx s T A = (LEAST k. \<exists>i j. A = {i, j} \<and> i < j \<and> (s j, s i) \<in> T k)"


lemma transition_idx_less:
  assumes "i < j" "(s j, s i) \<in> T k" "k < n"
  shows "transition_idx s T {i, j} < n"
proof -
  from assms(1,2) have "transition_idx s T {i, j} \<le> k"
    by (simp add: transition_idx_def, blast intro: Least_le)
  with assms(3) show ?thesis by simp
qed

lemma transition_idx_in:
  assumes "i < j" "(s j, s i) \<in> T k"
  shows "(s j, s i) \<in> T (transition_idx s T {i, j})"
  using assms
  by (simp add: transition_idx_def doubleton_eq_iff conj_disj_distribR cong: conj_cong) (erule LeastI)

text \<open>To be equal to the union of some well-founded relations is equivalent
  to being the subset of such a union.\<close>
lemma disj_wf: "disj_wf r \<longleftrightarrow> (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf(T i)) \<and> r \<subseteq> (\<Union>i<n. T i))"
  apply (auto simp add: disj_wf_def)
  apply (rule_tac x="\<lambda>i. T i Int r" in exI)
  apply (rule_tac x=n in exI)
  apply (force simp add: wf_Int1)
  done

theorem trans_disj_wf_implies_wf:
  assumes "trans r"
    and "disj_wf r"
  shows "wf r"
proof (simp only: wf_iff_no_infinite_down_chain, rule notI)
  assume "\<exists>s. \<forall>i. (s (Suc i), s i) \<in> r"
  then obtain s where sSuc: "\<forall>i. (s (Suc i), s i) \<in> r" ..
  from \<open>disj_wf r\<close> obtain T and n :: nat where wfT: "\<forall>k<n. wf(T k)" and r: "r = (\<Union>k<n. T k)"
    by (auto simp add: disj_wf_def)
  have s_in_T: "\<exists>k. (s j, s i) \<in> T k \<and> k<n" if "i < j" for i j
  proof -
    from \<open>i < j\<close> have "(s j, s i) \<in> r"
    proof (induct rule: less_Suc_induct)
      case 1
      then show ?case by (simp add: sSuc)
    next
      case 2
      with \<open>trans r\<close> show ?case
        unfolding trans_def by blast
    qed
    then show ?thesis by (auto simp add: r)
  qed
  have trless: "i \<noteq> j \<Longrightarrow> transition_idx s T {i, j} < n" for i j
    apply (auto simp add: linorder_neq_iff)
     apply (blast dest: s_in_T transition_idx_less)
    apply (subst insert_commute)
    apply (blast dest: s_in_T transition_idx_less)
    done
  have "\<exists>K k. K \<subseteq> UNIV \<and> infinite K \<and> k < n \<and>
      (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k)"
    by (rule Ramsey2) (auto intro: trless infinite_UNIV_nat)
  then obtain K and k where infK: "infinite K" and "k < n"
    and allk: "\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k"
    by auto
  have "(s (enumerate K (Suc m)), s (enumerate K m)) \<in> T k" for m :: nat
  proof -
    let ?j = "enumerate K (Suc m)"
    let ?i = "enumerate K m"
    have ij: "?i < ?j" by (simp add: enumerate_step infK)
    have "?j \<in> K" "?i \<in> K" by (simp_all add: enumerate_in_set infK)
    with ij have k: "k = transition_idx s T {?i, ?j}" by (simp add: allk)
    from s_in_T [OF ij] obtain k' where "(s ?j, s ?i) \<in> T k'" "k'<n" by blast
    then show "(s ?j, s ?i) \<in> T k" by (simp add: k transition_idx_in ij)
  qed
  then have "\<not> wf (T k)"
    unfolding wf_iff_no_infinite_down_chain by fast
  with wfT \<open>k < n\<close> show False by blast
qed

end

(*  Title:      HOL/Library/Ramsey.thy
    Author:     Tom Ridge.  Converted to structured Isar by L C Paulson
*)

header "Ramsey's Theorem"

theory Ramsey
imports Main Infinite_Set
begin

subsection{* Finite Ramsey theorem(s) *}

text{* To distinguish the finite and infinite ones, lower and upper case
names are used.

This is the most basic version in terms of cliques and independent
sets, i.e. the version for graphs and 2 colours. *}

definition "clique V E = (\<forall>v\<in>V. \<forall>w\<in>V. v\<noteq>w \<longrightarrow> {v,w} : E)"
definition "indep V E = (\<forall>v\<in>V. \<forall>w\<in>V. v\<noteq>w \<longrightarrow> \<not> {v,w} : E)"

lemma ramsey2:
  "\<exists>r\<ge>1. \<forall> (V::'a set) (E::'a set set). finite V \<and> card V \<ge> r \<longrightarrow>
  (\<exists> R \<subseteq> V. card R = m \<and> clique R E \<or> card R = n \<and> indep R E)"
  (is "\<exists>r\<ge>1. ?R m n r")
proof(induct k == "m+n" arbitrary: m n)
  case 0
  show ?case (is "EX r. ?R r")
  proof
    show "?R 1" using 0
      by (clarsimp simp: indep_def)(metis card.empty emptyE empty_subsetI)
  qed
next
  case (Suc k)
  { assume "m=0"
    have ?case (is "EX r. ?R r")
    proof
      show "?R 1" using `m=0`
        by (simp add:clique_def)(metis card.empty emptyE empty_subsetI)
    qed
  } moreover
  { assume "n=0"
    have ?case (is "EX r. ?R r")
    proof
      show "?R 1" using `n=0`
        by (simp add:indep_def)(metis card.empty emptyE empty_subsetI)
    qed
  } moreover
  { assume "m\<noteq>0" "n\<noteq>0"
    then have "k = (m - 1) + n" "k = m + (n - 1)" using `Suc k = m+n` by auto
    from Suc(1)[OF this(1)] Suc(1)[OF this(2)]
    obtain r1 r2 where "r1\<ge>1" "r2\<ge>1" "?R (m - 1) n r1" "?R m (n - 1) r2"
      by auto
    then have "r1+r2 \<ge> 1" by arith
    moreover
    have "?R m n (r1+r2)" (is "ALL V E. _ \<longrightarrow> ?EX V E m n")
    proof clarify
      fix V :: "'a set" and E :: "'a set set"
      assume "finite V" "r1+r2 \<le> card V"
      with `r1\<ge>1` have "V \<noteq> {}" by auto
      then obtain v where "v : V" by blast
      let ?M = "{w : V. w\<noteq>v & {v,w} : E}"
      let ?N = "{w : V. w\<noteq>v & {v,w} ~: E}"
      have "V = insert v (?M \<union> ?N)" using `v : V` by auto
      then have "card V = card(insert v (?M \<union> ?N))" by metis
      also have "\<dots> = card ?M + card ?N + 1" using `finite V`
        by(fastforce intro: card_Un_disjoint)
      finally have "card V = card ?M + card ?N + 1" .
      then have "r1+r2 \<le> card ?M + card ?N + 1" using `r1+r2 \<le> card V` by simp
      then have "r1 \<le> card ?M \<or> r2 \<le> card ?N" by arith
      moreover
      { assume "r1 \<le> card ?M"
        moreover have "finite ?M" using `finite V` by auto
        ultimately have "?EX ?M E (m - 1) n" using `?R (m - 1) n r1` by blast
        then obtain R where "R \<subseteq> ?M" "v ~: R" and
          CI: "card R = m - 1 \<and> clique R E \<or>
               card R = n \<and> indep R E" (is "?C \<or> ?I")
          by blast
        have "R <= V" using `R <= ?M` by auto
        have "finite R" using `finite V` `R \<subseteq> V` by (metis finite_subset)
        { assume "?I"
          with `R <= V` have "?EX V E m n" by blast
        } moreover
        { assume "?C"
          then have "clique (insert v R) E" using `R <= ?M`
           by(auto simp:clique_def insert_commute)
          moreover have "card(insert v R) = m"
            using `?C` `finite R` `v ~: R` `m\<noteq>0` by simp
          ultimately have "?EX V E m n" using `R <= V` `v : V` by blast
        } ultimately have "?EX V E m n" using CI by blast
      } moreover
      { assume "r2 \<le> card ?N"
        moreover have "finite ?N" using `finite V` by auto
        ultimately have "?EX ?N E m (n - 1)" using `?R m (n - 1) r2` by blast
        then obtain R where "R \<subseteq> ?N" "v ~: R" and
          CI: "card R = m \<and> clique R E \<or>
               card R = n - 1 \<and> indep R E" (is "?C \<or> ?I")
          by blast
        have "R <= V" using `R <= ?N` by auto
        have "finite R" using `finite V` `R \<subseteq> V` by (metis finite_subset)
        { assume "?C"
          with `R <= V` have "?EX V E m n" by blast
        } moreover
        { assume "?I"
          then have "indep (insert v R) E" using `R <= ?N`
            by(auto simp:indep_def insert_commute)
          moreover have "card(insert v R) = n"
            using `?I` `finite R` `v ~: R` `n\<noteq>0` by simp
          ultimately have "?EX V E m n" using `R <= V` `v : V` by blast
        } ultimately have "?EX V E m n" using CI by blast
      } ultimately show "?EX V E m n" by blast
    qed
    ultimately have ?case by blast
  } ultimately show ?case by blast
qed


subsection {* Preliminaries *}

subsubsection {* ``Axiom'' of Dependent Choice *}

primrec choice :: "('a => bool) => ('a * 'a) set => nat => 'a" where
  --{*An integer-indexed chain of choices*}
    choice_0:   "choice P r 0 = (SOME x. P x)"
  | choice_Suc: "choice P r (Suc n) = (SOME y. P y & (choice P r n, y) \<in> r)"

lemma choice_n:
  assumes P0: "P x0"
      and Pstep: "!!x. P x ==> \<exists>y. P y & (x,y) \<in> r"
  shows "P (choice P r n)"
proof (induct n)
  case 0 show ?case by (force intro: someI P0)
next
  case Suc then show ?case by (auto intro: someI2_ex [OF Pstep])
qed

lemma dependent_choice:
  assumes trans: "trans r"
      and P0: "P x0"
      and Pstep: "!!x. P x ==> \<exists>y. P y & (x,y) \<in> r"
  obtains f :: "nat => 'a" where
    "!!n. P (f n)" and "!!n m. n < m ==> (f n, f m) \<in> r"
proof
  fix n
  show "P (choice P r n)" by (blast intro: choice_n [OF P0 Pstep])
next
  have PSuc: "\<forall>n. (choice P r n, choice P r (Suc n)) \<in> r"
    using Pstep [OF choice_n [OF P0 Pstep]]
    by (auto intro: someI2_ex)
  fix n m :: nat
  assume less: "n < m"
  show "(choice P r n, choice P r m) \<in> r" using PSuc
    by (auto intro: less_Suc_induct [OF less] transD [OF trans])
qed


subsubsection {* Partitions of a Set *}

definition part :: "nat => nat => 'a set => ('a set => nat) => bool"
  --{*the function @{term f} partitions the @{term r}-subsets of the typically
       infinite set @{term Y} into @{term s} distinct categories.*}
where
  "part r s Y f = (\<forall>X. X \<subseteq> Y & finite X & card X = r --> f X < s)"

text{*For induction, we decrease the value of @{term r} in partitions.*}
lemma part_Suc_imp_part:
     "[| infinite Y; part (Suc r) s Y f; y \<in> Y |]
      ==> part r s (Y - {y}) (%u. f (insert y u))"
  apply(simp add: part_def, clarify)
  apply(drule_tac x="insert y X" in spec)
  apply(force)
  done

lemma part_subset: "part r s YY f ==> Y \<subseteq> YY ==> part r s Y f"
  unfolding part_def by blast


subsection {* Ramsey's Theorem: Infinitary Version *}

lemma Ramsey_induction:
  fixes s and r::nat
  shows
  "!!(YY::'a set) (f::'a set => nat).
      [|infinite YY; part r s YY f|]
      ==> \<exists>Y' t'. Y' \<subseteq> YY & infinite Y' & t' < s &
                  (\<forall>X. X \<subseteq> Y' & finite X & card X = r --> f X = t')"
proof (induct r)
  case 0
  then show ?case by (auto simp add: part_def card_eq_0_iff cong: conj_cong)
next
  case (Suc r)
  show ?case
  proof -
    from Suc.prems infinite_imp_nonempty obtain yy where yy: "yy \<in> YY" by blast
    let ?ramr = "{((y,Y,t),(y',Y',t')). y' \<in> Y & Y' \<subseteq> Y}"
    let ?propr = "%(y,Y,t).
                 y \<in> YY & y \<notin> Y & Y \<subseteq> YY & infinite Y & t < s
                 & (\<forall>X. X\<subseteq>Y & finite X & card X = r --> (f o insert y) X = t)"
    have infYY': "infinite (YY-{yy})" using Suc.prems by auto
    have partf': "part r s (YY - {yy}) (f \<circ> insert yy)"
      by (simp add: o_def part_Suc_imp_part yy Suc.prems)
    have transr: "trans ?ramr" by (force simp add: trans_def)
    from Suc.hyps [OF infYY' partf']
    obtain Y0 and t0
    where "Y0 \<subseteq> YY - {yy}"  "infinite Y0"  "t0 < s"
          "\<forall>X. X\<subseteq>Y0 \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yy) X = t0"
        by blast
    with yy have propr0: "?propr(yy,Y0,t0)" by blast
    have proprstep: "\<And>x. ?propr x \<Longrightarrow> \<exists>y. ?propr y \<and> (x, y) \<in> ?ramr"
    proof -
      fix x
      assume px: "?propr x" then show "?thesis x"
      proof (cases x)
        case (fields yx Yx tx)
        then obtain yx' where yx': "yx' \<in> Yx" using px
               by (blast dest: infinite_imp_nonempty)
        have infYx': "infinite (Yx-{yx'})" using fields px by auto
        with fields px yx' Suc.prems
        have partfx': "part r s (Yx - {yx'}) (f \<circ> insert yx')"
          by (simp add: o_def part_Suc_imp_part part_subset [where YY=YY and Y=Yx])
        from Suc.hyps [OF infYx' partfx']
        obtain Y' and t'
        where Y': "Y' \<subseteq> Yx - {yx'}"  "infinite Y'"  "t' < s"
               "\<forall>X. X\<subseteq>Y' \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yx') X = t'"
            by blast
        show ?thesis
        proof
          show "?propr (yx',Y',t') & (x, (yx',Y',t')) \<in> ?ramr"
            using fields Y' yx' px by blast
        qed
      qed
    qed
    from dependent_choice [OF transr propr0 proprstep]
    obtain g where pg: "!!n::nat.  ?propr (g n)"
      and rg: "!!n m. n<m ==> (g n, g m) \<in> ?ramr" by blast
    let ?gy = "fst o g"
    let ?gt = "snd o snd o g"
    have rangeg: "\<exists>k. range ?gt \<subseteq> {..<k}"
    proof (intro exI subsetI)
      fix x
      assume "x \<in> range ?gt"
      then obtain n where "x = ?gt n" ..
      with pg [of n] show "x \<in> {..<s}" by (cases "g n") auto
    qed
    have "finite (range ?gt)"
      by (simp add: finite_nat_iff_bounded rangeg)
    then obtain s' and n'
      where s': "s' = ?gt n'"
        and infeqs': "infinite {n. ?gt n = s'}"
      by (rule inf_img_fin_domE) (auto simp add: vimage_def intro: nat_infinite)
    with pg [of n'] have less': "s'<s" by (cases "g n'") auto
    have inj_gy: "inj ?gy"
    proof (rule linorder_injI)
      fix m m' :: nat assume less: "m < m'" show "?gy m \<noteq> ?gy m'"
        using rg [OF less] pg [of m] by (cases "g m", cases "g m'") auto
    qed
    show ?thesis
    proof (intro exI conjI)
      show "?gy ` {n. ?gt n = s'} \<subseteq> YY" using pg
        by (auto simp add: Let_def split_beta)
      show "infinite (?gy ` {n. ?gt n = s'})" using infeqs'
        by (blast intro: inj_gy [THEN subset_inj_on] dest: finite_imageD)
      show "s' < s" by (rule less')
      show "\<forall>X. X \<subseteq> ?gy ` {n. ?gt n = s'} & finite X & card X = Suc r
          --> f X = s'"
      proof -
        {fix X
         assume "X \<subseteq> ?gy ` {n. ?gt n = s'}"
            and cardX: "finite X" "card X = Suc r"
         then obtain AA where AA: "AA \<subseteq> {n. ?gt n = s'}" and Xeq: "X = ?gy`AA"
             by (auto simp add: subset_image_iff)
         with cardX have "AA\<noteq>{}" by auto
         then have AAleast: "(LEAST x. x \<in> AA) \<in> AA" by (auto intro: LeastI_ex)
         have "f X = s'"
         proof (cases "g (LEAST x. x \<in> AA)")
           case (fields ya Ya ta)
           with AAleast Xeq
           have ya: "ya \<in> X" by (force intro!: rev_image_eqI)
           then have "f X = f (insert ya (X - {ya}))" by (simp add: insert_absorb)
           also have "... = ta"
           proof -
             have "X - {ya} \<subseteq> Ya"
             proof
               fix x assume x: "x \<in> X - {ya}"
               then obtain a' where xeq: "x = ?gy a'" and a': "a' \<in> AA"
                 by (auto simp add: Xeq)
               then have "a' \<noteq> (LEAST x. x \<in> AA)" using x fields by auto
               then have lessa': "(LEAST x. x \<in> AA) < a'"
                 using Least_le [of "%x. x \<in> AA", OF a'] by arith
               show "x \<in> Ya" using xeq fields rg [OF lessa'] by auto
             qed
             moreover
             have "card (X - {ya}) = r"
               by (simp add: cardX ya)
             ultimately show ?thesis
               using pg [of "LEAST x. x \<in> AA"] fields cardX
               by (clarsimp simp del:insert_Diff_single)
           qed
           also have "... = s'" using AA AAleast fields by auto
           finally show ?thesis .
         qed}
        then show ?thesis by blast
      qed
    qed
  qed
qed


theorem Ramsey:
  fixes s r :: nat and Z::"'a set" and f::"'a set => nat"
  shows
   "[|infinite Z;
      \<forall>X. X \<subseteq> Z & finite X & card X = r --> f X < s|]
  ==> \<exists>Y t. Y \<subseteq> Z & infinite Y & t < s
            & (\<forall>X. X \<subseteq> Y & finite X & card X = r --> f X = t)"
by (blast intro: Ramsey_induction [unfolded part_def])


corollary Ramsey2:
  fixes s::nat and Z::"'a set" and f::"'a set => nat"
  assumes infZ: "infinite Z"
      and part: "\<forall>x\<in>Z. \<forall>y\<in>Z. x\<noteq>y --> f{x,y} < s"
  shows
   "\<exists>Y t. Y \<subseteq> Z & infinite Y & t < s & (\<forall>x\<in>Y. \<forall>y\<in>Y. x\<noteq>y --> f{x,y} = t)"
proof -
  have part2: "\<forall>X. X \<subseteq> Z & finite X & card X = 2 --> f X < s"
    using part by (fastforce simp add: eval_nat_numeral card_Suc_eq)
  obtain Y t
    where "Y \<subseteq> Z" "infinite Y" "t < s"
          "(\<forall>X. X \<subseteq> Y & finite X & card X = 2 --> f X = t)"
    by (insert Ramsey [OF infZ part2]) auto
  moreover from this have  "\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow> f {x, y} = t" by auto
  ultimately show ?thesis by iprover
qed


subsection {* Disjunctive Well-Foundedness *}

text {*
  An application of Ramsey's theorem to program termination. See
  \cite{Podelski-Rybalchenko}.
*}

definition disj_wf :: "('a * 'a)set => bool"
  where "disj_wf r = (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf(T i)) & r = (\<Union>i<n. T i))"

definition transition_idx :: "[nat => 'a, nat => ('a*'a)set, nat set] => nat"
  where
    "transition_idx s T A =
      (LEAST k. \<exists>i j. A = {i,j} & i<j & (s j, s i) \<in> T k)"


lemma transition_idx_less:
    "[|i<j; (s j, s i) \<in> T k; k<n|] ==> transition_idx s T {i,j} < n"
apply (subgoal_tac "transition_idx s T {i, j} \<le> k", simp)
apply (simp add: transition_idx_def, blast intro: Least_le)
done

lemma transition_idx_in:
    "[|i<j; (s j, s i) \<in> T k|] ==> (s j, s i) \<in> T (transition_idx s T {i,j})"
apply (simp add: transition_idx_def doubleton_eq_iff conj_disj_distribR
            cong: conj_cong)
apply (erule LeastI)
done

text{*To be equal to the union of some well-founded relations is equivalent
to being the subset of such a union.*}
lemma disj_wf:
     "disj_wf(r) = (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf(T i)) & r \<subseteq> (\<Union>i<n. T i))"
apply (auto simp add: disj_wf_def)
apply (rule_tac x="%i. T i Int r" in exI)
apply (rule_tac x=n in exI)
apply (force simp add: wf_Int1)
done

theorem trans_disj_wf_implies_wf:
  assumes transr: "trans r"
      and dwf:    "disj_wf(r)"
  shows "wf r"
proof (simp only: wf_iff_no_infinite_down_chain, rule notI)
  assume "\<exists>s. \<forall>i. (s (Suc i), s i) \<in> r"
  then obtain s where sSuc: "\<forall>i. (s (Suc i), s i) \<in> r" ..
  have s: "!!i j. i < j ==> (s j, s i) \<in> r"
  proof -
    fix i and j::nat
    assume less: "i<j"
    then show "(s j, s i) \<in> r"
    proof (rule less_Suc_induct)
      show "\<And>i. (s (Suc i), s i) \<in> r" by (simp add: sSuc)
      show "\<And>i j k. \<lbrakk>(s j, s i) \<in> r; (s k, s j) \<in> r\<rbrakk> \<Longrightarrow> (s k, s i) \<in> r"
        using transr by (unfold trans_def, blast)
    qed
  qed
  from dwf
  obtain T and n::nat where wfT: "\<forall>k<n. wf(T k)" and r: "r = (\<Union>k<n. T k)"
    by (auto simp add: disj_wf_def)
  have s_in_T: "\<And>i j. i<j ==> \<exists>k. (s j, s i) \<in> T k & k<n"
  proof -
    fix i and j::nat
    assume less: "i<j"
    then have "(s j, s i) \<in> r" by (rule s [of i j])
    then show "\<exists>k. (s j, s i) \<in> T k & k<n" by (auto simp add: r)
  qed
  have trless: "!!i j. i\<noteq>j ==> transition_idx s T {i,j} < n"
    apply (auto simp add: linorder_neq_iff)
    apply (blast dest: s_in_T transition_idx_less)
    apply (subst insert_commute)
    apply (blast dest: s_in_T transition_idx_less)
    done
  have
   "\<exists>K k. K \<subseteq> UNIV & infinite K & k < n &
          (\<forall>i\<in>K. \<forall>j\<in>K. i\<noteq>j --> transition_idx s T {i,j} = k)"
    by (rule Ramsey2) (auto intro: trless nat_infinite)
  then obtain K and k
    where infK: "infinite K" and less: "k < n" and
          allk: "\<forall>i\<in>K. \<forall>j\<in>K. i\<noteq>j --> transition_idx s T {i,j} = k"
    by auto
  have "\<forall>m. (s (enumerate K (Suc m)), s(enumerate K m)) \<in> T k"
  proof
    fix m::nat
    let ?j = "enumerate K (Suc m)"
    let ?i = "enumerate K m"
    have jK: "?j \<in> K" by (simp add: enumerate_in_set infK)
    have iK: "?i \<in> K" by (simp add: enumerate_in_set infK)
    have ij: "?i < ?j" by (simp add: enumerate_step infK)
    have ijk: "transition_idx s T {?i,?j} = k" using iK jK ij
      by (simp add: allk)
    obtain k' where "(s ?j, s ?i) \<in> T k'" "k'<n"
      using s_in_T [OF ij] by blast
    then show "(s ?j, s ?i) \<in> T k"
      by (simp add: ijk [symmetric] transition_idx_in ij)
  qed
  then have "~ wf(T k)" by (force simp add: wf_iff_no_infinite_down_chain)
  then show False using wfT less by blast
qed

end

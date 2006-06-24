(*  Title:      HOL/Library/Ramsey.thy
    ID:         $Id$
    Author:     Tom Ridge. Converted to structured Isar by L C Paulson
*)

header "Ramsey's Theorem"

theory Ramsey imports Main begin


subsection{*``Axiom'' of Dependent Choice*}

consts choice :: "('a => bool) => ('a * 'a) set => nat => 'a"
  --{*An integer-indexed chain of choices*}
primrec
  choice_0:   "choice P r 0 = (SOME x. P x)"

  choice_Suc: "choice P r (Suc n) = (SOME y. P y & (choice P r n, y) \<in> r)"


lemma choice_n: 
  assumes P0: "P x0"
      and Pstep: "!!x. P x ==> \<exists>y. P y & (x,y) \<in> r"
  shows "P (choice P r n)"
proof (induct n)
  case 0 show ?case by (force intro: someI P0) 
next
  case Suc thus ?case by (auto intro: someI2_ex [OF Pstep]) 
qed

lemma dependent_choice: 
  assumes trans: "trans r"
      and P0: "P x0"
      and Pstep: "!!x. P x ==> \<exists>y. P y & (x,y) \<in> r"
  shows "\<exists>f::nat=>'a. (\<forall>n. P (f n)) & (\<forall>n m. n<m --> (f n, f m) \<in> r)"
proof (intro exI conjI)
  show "\<forall>n. P (choice P r n)" by (blast intro: choice_n [OF P0 Pstep]) 
next
  have PSuc: "\<forall>n. (choice P r n, choice P r (Suc n)) \<in> r" 
    using Pstep [OF choice_n [OF P0 Pstep]]
    by (auto intro: someI2_ex)
  show "\<forall>n m. n<m --> (choice P r n, choice P r m) \<in> r"
  proof (intro strip)
    fix n m :: nat
    assume less: "n<m"
    show "(choice P r n, choice P r m) \<in> r" using PSuc
      by (auto intro: less_Suc_induct [OF less] transD [OF trans])
  qed
qed 


subsection {*Partitions of a Set*}

definition
  part :: "nat => nat => 'a set => ('a set => nat) => bool"
  --{*the function @{term f} partitions the @{term r}-subsets of the typically
       infinite set @{term Y} into @{term s} distinct categories.*}
  "part r s Y f = (\<forall>X. X \<subseteq> Y & finite X & card X = r --> f X < s)"

text{*For induction, we decrease the value of @{term r} in partitions.*}
lemma part_Suc_imp_part:
     "[| infinite Y; part (Suc r) s Y f; y \<in> Y |] 
      ==> part r s (Y - {y}) (%u. f (insert y u))"
  apply(simp add: part_def, clarify)
  apply(drule_tac x="insert y X" in spec)
  apply(force simp:card_Diff_singleton_if)
  done

lemma part_subset: "part r s YY f ==> Y \<subseteq> YY ==> part r s Y f" 
  unfolding part_def by blast
  

subsection {*Ramsey's Theorem: Infinitary Version*}

lemma ramsey_induction: 
  fixes s r :: nat
  shows
  "!!(YY::'a set) (f::'a set => nat). 
      [|infinite YY; part r s YY f|]
      ==> \<exists>Y' t'. Y' \<subseteq> YY & infinite Y' & t' < s & 
                  (\<forall>X. X \<subseteq> Y' & finite X & card X = r --> f X = t')"
proof (induct r)
  case 0
  thus ?case by (auto simp add: part_def card_eq_0_iff cong: conj_cong) 
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
      assume px: "?propr x" thus "?thesis x"
      proof (cases x)
        case (fields yx Yx tx)
        then obtain yx' where yx': "yx' \<in> Yx" using px
               by (blast dest: infinite_imp_nonempty)
        have infYx': "infinite (Yx-{yx'})" using fields px by auto
        with fields px yx' Suc.prems
        have partfx': "part r s (Yx - {yx'}) (f \<circ> insert yx')"
          by (simp add: o_def part_Suc_imp_part part_subset [where ?YY=YY]) 
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
      and rg: "!!n m. n<m ==> (g n, g m) \<in> ?ramr" by force
    let ?gy = "(\<lambda>n. let (y,Y,t) = g n in y)"
    let ?gt = "(\<lambda>n. let (y,Y,t) = g n in t)"
    have rangeg: "\<exists>k. range ?gt \<subseteq> {..<k}"
    proof (intro exI subsetI)
      fix x
      assume "x \<in> range ?gt"
      then obtain n where "x = ?gt n" ..
      with pg [of n] show "x \<in> {..<s}" by (cases "g n") auto
    qed
    have "\<exists>s' \<in> range ?gt. infinite (?gt -` {s'})" 
     by (rule inf_img_fin_dom [OF _ nat_infinite]) 
        (simp add: finite_nat_iff_bounded rangeg)
    then obtain s' and n'
            where s':      "s' = ?gt n'"
              and infeqs': "infinite {n. ?gt n = s'}"
       by (auto simp add: vimage_def)
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
         hence AAleast: "(LEAST x. x \<in> AA) \<in> AA" by (auto intro: LeastI_ex) 
         have "f X = s'"
         proof (cases "g (LEAST x. x \<in> AA)") 
           case (fields ya Ya ta)
           with AAleast Xeq 
           have ya: "ya \<in> X" by (force intro!: rev_image_eqI) 
           hence "f X = f (insert ya (X - {ya}))" by (simp add: insert_absorb)
           also have "... = ta" 
           proof -
             have "X - {ya} \<subseteq> Ya"
             proof 
               fix x
               assume x: "x \<in> X - {ya}"
               then obtain a' where xeq: "x = ?gy a'" and a': "a' \<in> AA" 
                 by (auto simp add: Xeq) 
               hence "a' \<noteq> (LEAST x. x \<in> AA)" using x fields by auto
               hence lessa': "(LEAST x. x \<in> AA) < a'"
                 using Least_le [of "%x. x \<in> AA", OF a'] by arith
               show "x \<in> Ya" using xeq fields rg [OF lessa'] by auto
             qed
             moreover
             have "card (X - {ya}) = r"
               by (simp add: card_Diff_singleton_if cardX ya)
             ultimately show ?thesis 
               using pg [of "LEAST x. x \<in> AA"] fields cardX
	       by (clarsimp simp del:insert_Diff_single)
           qed
           also have "... = s'" using AA AAleast fields by auto
           finally show ?thesis .
         qed}
        thus ?thesis by blast
      qed 
    qed 
  qed
qed


text{*Repackaging of Tom Ridge's final result*}
theorem Ramsey:
  fixes s r :: nat and Z::"'a set" and f::"'a set => nat"
  shows
   "[|infinite Z;
      \<forall>X. X \<subseteq> Z & finite X & card X = r --> f X < s|]
  ==> \<exists>Y t. Y \<subseteq> Z & infinite Y & t < s 
            & (\<forall>X. X \<subseteq> Y & finite X & card X = r --> f X = t)"
by (blast intro: ramsey_induction [unfolded part_def]) 

end

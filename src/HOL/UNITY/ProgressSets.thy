(*  Title:      HOL/UNITY/ProgressSets
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Progress Sets.  From 

    David Meier and Beverly Sanders,
    Composing Leads-to Properties
    Theoretical Computer Science 243:1-2 (2000), 339-361.

    David Meier,
    Progress Properties in Program Refinement and Parallel Composition
    Swiss Federal Institute of Technology Zurich (1997)
*)

header{*Progress Sets*}

theory ProgressSets = Transformers:

subsection {*Complete Lattices and the Operator @{term cl}*}

constdefs
  lattice :: "'a set set => bool"
   --{*Meier calls them closure sets, but they are just complete lattices*}
   "lattice L ==
	 (\<forall>M. M \<subseteq> L --> \<Inter>M \<in> L) & (\<forall>M. M \<subseteq> L --> \<Union>M \<in> L)"

  cl :: "['a set set, 'a set] => 'a set"
   --{*short for ``closure''*}
   "cl L r == \<Inter>{x. x\<in>L & r \<subseteq> x}"

lemma UNIV_in_lattice: "lattice L ==> UNIV \<in> L"
by (force simp add: lattice_def)

lemma empty_in_lattice: "lattice L ==> {} \<in> L"
by (force simp add: lattice_def)

lemma Union_in_lattice: "[|M \<subseteq> L; lattice L|] ==> \<Union>M \<in> L"
by (simp add: lattice_def)

lemma Inter_in_lattice: "[|M \<subseteq> L; lattice L|] ==> \<Inter>M \<in> L"
by (simp add: lattice_def)

lemma UN_in_lattice:
     "[|lattice L; !!i. i\<in>I ==> r i \<in> L|] ==> (\<Union>i\<in>I. r i) \<in> L"
apply (simp add: Set.UN_eq) 
apply (blast intro: Union_in_lattice) 
done

lemma INT_in_lattice:
     "[|lattice L; !!i. i\<in>I ==> r i \<in> L|] ==> (\<Inter>i\<in>I. r i)  \<in> L"
apply (simp add: INT_eq) 
apply (blast intro: Inter_in_lattice) 
done

lemma Un_in_lattice: "[|x\<in>L; y\<in>L; lattice L|] ==> x\<union>y \<in> L"
apply (simp only: Un_eq_Union) 
apply (blast intro: Union_in_lattice) 
done

lemma Int_in_lattice: "[|x\<in>L; y\<in>L; lattice L|] ==> x\<inter>y \<in> L"
apply (simp only: Int_eq_Inter) 
apply (blast intro: Inter_in_lattice) 
done

lemma lattice_stable: "lattice {X. F \<in> stable X}"
by (simp add: lattice_def stable_def constrains_def, blast)

text{*The next three results state that @{term "cl L r"} is the minimal
 element of @{term L} that includes @{term r}.*}
lemma cl_in_lattice: "lattice L ==> cl L r \<in> L"
apply (simp add: lattice_def cl_def)
apply (erule conjE)  
apply (drule spec, erule mp, blast) 
done

lemma cl_least: "[|c\<in>L; r\<subseteq>c|] ==> cl L r \<subseteq> c" 
by (force simp add: cl_def)

text{*The next three lemmas constitute assertion (4.61)*}
lemma cl_mono: "r \<subseteq> r' ==> cl L r \<subseteq> cl L r'"
by (simp add: cl_def, blast)

lemma subset_cl: "r \<subseteq> cl L r"
by (simp add: cl_def, blast)

lemma cl_UN_subset: "(\<Union>i\<in>I. cl L (r i)) \<subseteq> cl L (\<Union>i\<in>I. r i)"
by (simp add: cl_def, blast)

lemma cl_Un: "lattice L ==> cl L (r\<union>s) = cl L r \<union> cl L s"
apply (rule equalityI) 
 prefer 2 
  apply (simp add: cl_def, blast)
apply (rule cl_least)
 apply (blast intro: Un_in_lattice cl_in_lattice)
apply (blast intro: subset_cl [THEN subsetD])  
done

lemma cl_UN: "lattice L ==> cl L (\<Union>i\<in>I. r i) = (\<Union>i\<in>I. cl L (r i))"
apply (rule equalityI) 
 prefer 2 apply (simp add: cl_def, blast)
apply (rule cl_least)
 apply (blast intro: UN_in_lattice cl_in_lattice)
apply (blast intro: subset_cl [THEN subsetD])  
done

lemma cl_idem [simp]: "cl L (cl L r) = cl L r"
by (simp add: cl_def, blast)

lemma cl_ident: "r\<in>L ==> cl L r = r" 
by (force simp add: cl_def)

text{*Assertion (4.62)*}
lemma cl_ident_iff: "lattice L ==> (cl L r = r) = (r\<in>L)" 
apply (rule iffI) 
 apply (erule subst)
 apply (erule cl_in_lattice)  
apply (erule cl_ident) 
done

lemma cl_subset_in_lattice: "[|cl L r \<subseteq> r; lattice L|] ==> r\<in>L" 
by (simp add: cl_ident_iff [symmetric] equalityI subset_cl)


subsection {*Progress Sets and the Main Lemma*}

constdefs 
  closed :: "['a program, 'a set, 'a set,  'a set set] => bool"
   "closed F T B L == \<forall>M. \<forall>act \<in> Acts F. B\<subseteq>M & T\<inter>M \<in> L -->
                              T \<inter> (B \<union> wp act M) \<in> L"

  progress_set :: "['a program, 'a set, 'a set] => 'a set set set"
   "progress_set F T B ==
      {L. F \<in> stable T & lattice L & B \<in> L & T \<in> L & closed F T B L}"

lemma closedD:
   "[|closed F T B L; act \<in> Acts F; B\<subseteq>M; T\<inter>M \<in> L|] 
    ==> T \<inter> (B \<union> wp act M) \<in> L"
by (simp add: closed_def) 

text{*Note: the formalization below replaces Meier's @{term q} by @{term B}
and @{term m} by @{term X}. *}

text{*Part of the proof of the claim at the bottom of page 97.  It's
proved separately because the argument requires a generalization over
all @{term "act \<in> Acts F"}.*}
lemma lattice_awp_lemma:
  assumes TXC:  "T\<inter>X \<in> C" --{*induction hypothesis in theorem below*}
      and BsubX:  "B \<subseteq> X"   --{*holds in inductive step*}
      and latt: "lattice C"
      and TC:   "T \<in> C"
      and BC:   "B \<in> C"
      and clos: "closed F T B C"
    shows "T \<inter> (B \<union> awp F (X \<union> cl C (T\<inter>r))) \<in> C"
apply (simp del: INT_simps add: awp_def INT_extend_simps) 
apply (rule INT_in_lattice [OF latt]) 
apply (erule closedD [OF clos]) 
apply (simp add: subset_trans [OF BsubX Un_upper1]) 
apply (subgoal_tac "T \<inter> (X \<union> cl C (T\<inter>r)) = (T\<inter>X) \<union> cl C (T\<inter>r)")
 prefer 2 apply (blast intro: TC rev_subsetD [OF _ cl_least]) 
apply (erule ssubst) 
apply (blast intro: Un_in_lattice latt cl_in_lattice TXC) 
done

text{*Remainder of the proof of the claim at the bottom of page 97.*}
lemma lattice_lemma:
  assumes TXC:  "T\<inter>X \<in> C" --{*induction hypothesis in theorem below*}
      and BsubX:  "B \<subseteq> X"   --{*holds in inductive step*}
      and act:  "act \<in> Acts F"
      and latt: "lattice C"
      and TC:   "T \<in> C"
      and BC:   "B \<in> C"
      and clos: "closed F T B C"
    shows "T \<inter> (wp act X \<inter> awp F (X \<union> cl C (T\<inter>r)) \<union> X) \<in> C"
apply (subgoal_tac "T \<inter> (B \<union> wp act X) \<in> C")
 prefer 2 apply (simp add: closedD [OF clos] act BsubX TXC)
apply (drule Int_in_lattice
              [OF _ lattice_awp_lemma [OF TXC BsubX latt TC BC clos, of r]
                    latt])
apply (subgoal_tac
	 "T \<inter> (B \<union> wp act X) \<inter> (T \<inter> (B \<union> awp F (X \<union> cl C (T\<inter>r)))) = 
	  T \<inter> (B \<union> wp act X \<inter> awp F (X \<union> cl C (T\<inter>r)))") 
 prefer 2 apply blast 
apply simp  
apply (drule Un_in_lattice [OF _ TXC latt])  
apply (subgoal_tac
	 "T \<inter> (B \<union> wp act X \<inter> awp F (X \<union> cl C (T\<inter>r))) \<union> T\<inter>X = 
	  T \<inter> (wp act X \<inter> awp F (X \<union> cl C (T\<inter>r)) \<union> X)")
 apply simp 
apply (blast intro: BsubX [THEN subsetD]) 
done


text{*Induction step for the main lemma*}
lemma progress_induction_step:
  assumes TXC:  "T\<inter>X \<in> C" --{*induction hypothesis in theorem below*}
      and act:  "act \<in> Acts F"
      and Xwens: "X \<in> wens_set F B"
      and latt: "lattice C"
      and  TC:  "T \<in> C"
      and  BC:  "B \<in> C"
      and clos: "closed F T B C"
      and Fstable: "F \<in> stable T"
  shows "T \<inter> wens F act X \<in> C"
proof -
  from Xwens have BsubX: "B \<subseteq> X"
    by (rule wens_set_imp_subset) 
  let ?r = "wens F act X"
  have "?r \<subseteq> (wp act X \<inter> awp F (X\<union>?r)) \<union> X"
    by (simp add: wens_unfold [symmetric])
  then have "T\<inter>?r \<subseteq> T \<inter> ((wp act X \<inter> awp F (X\<union>?r)) \<union> X)"
    by blast
  then have "T\<inter>?r \<subseteq> T \<inter> ((wp act X \<inter> awp F (T \<inter> (X\<union>?r))) \<union> X)"
    by (simp add: awp_Int_eq Fstable stable_imp_awp_ident, blast) 
  then have "T\<inter>?r \<subseteq> T \<inter> ((wp act X \<inter> awp F (X \<union> cl C (T\<inter>?r))) \<union> X)"
    by (blast intro: awp_mono [THEN [2] rev_subsetD] subset_cl [THEN subsetD])
  then have "cl C (T\<inter>?r) \<subseteq> 
             cl C (T \<inter> ((wp act X \<inter> awp F (X \<union> cl C (T\<inter>?r))) \<union> X))"
    by (rule cl_mono) 
  then have "cl C (T\<inter>?r) \<subseteq> 
             T \<inter> ((wp act X \<inter> awp F (X \<union> cl C (T\<inter>?r))) \<union> X)"
    by (simp add: cl_ident lattice_lemma [OF TXC BsubX act latt TC BC clos])
  then have "cl C (T\<inter>?r) \<subseteq> (wp act X \<inter> awp F (X \<union> cl C (T\<inter>?r))) \<union> X"
    by blast
  then have "cl C (T\<inter>?r) \<subseteq> ?r"
    by (blast intro!: subset_wens) 
  then have cl_subset: "cl C (T\<inter>?r) \<subseteq> T\<inter>?r"
    by (simp add: Int_subset_iff cl_ident TC
                  subset_trans [OF cl_mono [OF Int_lower1]]) 
  show ?thesis
    by (rule cl_subset_in_lattice [OF cl_subset latt]) 
qed

text{*The Lemma proved on page 96*}
lemma progress_set_lemma:
     "[|C \<in> progress_set F T B; r \<in> wens_set F B|] ==> T\<inter>r \<in> C"
apply (simp add: progress_set_def, clarify) 
apply (erule wens_set.induct) 
  txt{*Base*}
  apply (simp add: Int_in_lattice) 
 txt{*The difficult @{term wens} case*}
 apply (simp add: progress_induction_step) 
txt{*Disjunctive case*}
apply (subgoal_tac "(\<Union>U\<in>W. T \<inter> U) \<in> C") 
 apply (simp add: Int_Union) 
apply (blast intro: UN_in_lattice) 
done


subsection {*The Progress Set Union Theorem*}

lemma closed_mono:
  assumes BB':  "B \<subseteq> B'"
      and TBwp: "T \<inter> (B \<union> wp act M) \<in> C"
      and B'C:  "B' \<in> C"
      and TC:   "T \<in> C"
      and latt: "lattice C"
  shows "T \<inter> (B' \<union> wp act M) \<in> C"
proof -
  from TBwp have "(T\<inter>B) \<union> (T \<inter> wp act M) \<in> C"
    by (simp add: Int_Un_distrib)
  then have TBBC: "(T\<inter>B') \<union> ((T\<inter>B) \<union> (T \<inter> wp act M)) \<in> C"
    by (blast intro: Int_in_lattice Un_in_lattice TC B'C latt) 
  show ?thesis
    by (rule eqelem_imp_iff [THEN iffD1, OF _ TBBC], 
        blast intro: BB' [THEN subsetD]) 
qed


lemma progress_set_mono:
    assumes BB':  "B \<subseteq> B'"
    shows
     "[| B' \<in> C;  C \<in> progress_set F T B|] 
      ==> C \<in> progress_set F T B'"
by (simp add: progress_set_def closed_def closed_mono [OF BB'] 
                 subset_trans [OF BB']) 

theorem progress_set_Union:
  assumes prog: "C \<in> progress_set F T B"
      and BB':  "B \<subseteq> B'"
      and B'C:  "B' \<in> C"
      and Gco: "!!X. X\<in>C ==> G \<in> X-B co X"
      and leadsTo: "F \<in> A leadsTo B'"
  shows "F\<squnion>G \<in> T\<inter>A leadsTo B'"
apply (insert prog) 
apply (rule leadsTo_Join [OF leadsTo]) 
  apply (force simp add: progress_set_def awp_iff_stable [symmetric]) 
apply (simp add: awp_iff_constrains)
apply (drule progress_set_mono [OF BB' B'C]) 
apply (blast intro: progress_set_lemma Gco constrains_weaken_L 
                    BB' [THEN subsetD]) 
done

end

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

text{*A reformulation of @{thm subset_cl}*}
lemma clI: "x \<in> r ==> x \<in> cl L r"
by (simp add: cl_def, blast)

text{*A reformulation of @{thm cl_least}*}
lemma clD: "[|c \<in> cl L r; B \<in> L; r \<subseteq> B|] ==> c \<in> B"
by (force simp add: cl_def)

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

lemma cl_Int_subset: "cl L (r\<inter>s) \<subseteq> cl L r \<inter> cl L s"
by (simp add: cl_def, blast)

lemma cl_idem [simp]: "cl L (cl L r) = cl L r"
by (simp add: cl_def, blast)

lemma cl_ident: "r\<in>L ==> cl L r = r" 
by (force simp add: cl_def)

lemma cl_empty [simp]: "lattice L ==> cl L {} = {}"
by (simp add: cl_ident empty_in_lattice)

lemma cl_UNIV [simp]: "lattice L ==> cl L UNIV = UNIV"
by (simp add: cl_ident UNIV_in_lattice)

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
text{*A progress set satisfies certain closure conditions and is a 
simple way of including the set @{term "wens_set F B"}.*}

constdefs 
  closed :: "['a program, 'a set, 'a set,  'a set set] => bool"
   "closed F T B L == \<forall>M. \<forall>act \<in> Acts F. B\<subseteq>M & T\<inter>M \<in> L -->
                              T \<inter> (B \<union> wp act M) \<in> L"

  progress_set :: "['a program, 'a set, 'a set] => 'a set set set"
   "progress_set F T B ==
      {L. lattice L & B \<in> L & T \<in> L & closed F T B L}"

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
 prefer 2 apply (blast intro: TC clD) 
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

text{*Proved on page 96 of Meier's thesis.  The special case when
   @{term "T=UNIV"} states that every progress set for the program @{term F}
   and set @{term B} includes the set @{term "wens_set F B"}.*}
lemma progress_set_lemma:
     "[|C \<in> progress_set F T B; r \<in> wens_set F B; F \<in> stable T|] ==> T\<inter>r \<in> C"
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
  assumes leadsTo: "F \<in> A leadsTo B'"
      and prog: "C \<in> progress_set F T B"
      and Fstable: "F \<in> stable T"
      and BB':  "B \<subseteq> B'"
      and B'C:  "B' \<in> C"
      and Gco: "!!X. X\<in>C ==> G \<in> X-B co X"
  shows "F\<squnion>G \<in> T\<inter>A leadsTo B'"
apply (insert prog Fstable) 
apply (rule leadsTo_Join [OF leadsTo]) 
  apply (force simp add: progress_set_def awp_iff_stable [symmetric]) 
apply (simp add: awp_iff_constrains)
apply (drule progress_set_mono [OF BB' B'C]) 
apply (blast intro: progress_set_lemma Gco constrains_weaken_L 
                    BB' [THEN subsetD]) 
done


subsection {*Some Progress Sets*}

lemma UNIV_in_progress_set: "UNIV \<in> progress_set F T B"
by (simp add: progress_set_def lattice_def closed_def)



subsubsection {*Lattices and Relations*}
text{*From Meier's thesis, section 4.5.3*}

constdefs
  relcl :: "'a set set => ('a * 'a) set"
    -- {*Derived relation from a lattice*}
    "relcl L == {(x,y). y \<in> cl L {x}}"
  
  latticeof :: "('a * 'a) set => 'a set set"
    -- {*Derived lattice from a relation: the set of upwards-closed sets*}
    "latticeof r == {X. \<forall>s t. s \<in> X & (s,t) \<in> r --> t \<in> X}"


lemma relcl_refl: "(a,a) \<in> relcl L"
by (simp add: relcl_def subset_cl [THEN subsetD])

lemma relcl_trans:
     "[| (a,b) \<in> relcl L; (b,c) \<in> relcl L; lattice L |] ==> (a,c) \<in> relcl L"
apply (simp add: relcl_def)
apply (blast intro: clD cl_in_lattice)
done

lemma refl_relcl: "lattice L ==> refl UNIV (relcl L)"
by (simp add: reflI relcl_def subset_cl [THEN subsetD])

lemma trans_relcl: "lattice L ==> trans (relcl L)"
by (blast intro: relcl_trans transI)

lemma lattice_latticeof: "lattice (latticeof r)"
by (auto simp add: lattice_def latticeof_def)

lemma lattice_singletonI:
     "[|lattice L; !!s. s \<in> X ==> {s} \<in> L|] ==> X \<in> L"
apply (cut_tac UN_singleton [of X]) 
apply (erule subst) 
apply (simp only: UN_in_lattice) 
done

text{*Equation (4.71) of Meier's thesis.  He gives no proof.*}
lemma cl_latticeof:
     "[|refl UNIV r; trans r|] 
      ==> cl (latticeof r) X = {t. \<exists>s. s\<in>X & (s,t) \<in> r}" 
apply (rule equalityI) 
 apply (rule cl_least) 
  apply (simp (no_asm_use) add: latticeof_def trans_def, blast)
 apply (simp add: latticeof_def refl_def, blast)
apply (simp add: latticeof_def, clarify)
apply (unfold cl_def, blast) 
done

text{*Related to (4.71).*}
lemma cl_eq_Collect_relcl:
     "lattice L ==> cl L X = {t. \<exists>s. s\<in>X & (s,t) \<in> relcl L}" 
apply (cut_tac UN_singleton [of X]) 
apply (erule subst) 
apply (force simp only: relcl_def cl_UN)
done

text{*Meier's theorem of section 4.5.3*}
theorem latticeof_relcl_eq: "lattice L ==> latticeof (relcl L) = L"
apply (rule equalityI) 
 prefer 2 apply (force simp add: latticeof_def relcl_def cl_def, clarify) 
apply (rename_tac X)
apply (rule cl_subset_in_lattice)   
 prefer 2 apply assumption
apply (drule cl_ident_iff [OF lattice_latticeof, THEN iffD2])
apply (drule equalityD1)   
apply (rule subset_trans) 
 prefer 2 apply assumption
apply (thin_tac "?U \<subseteq> X") 
apply (cut_tac A=X in UN_singleton) 
apply (erule subst) 
apply (simp only: cl_UN lattice_latticeof 
                  cl_latticeof [OF refl_relcl trans_relcl]) 
apply (simp add: relcl_def) 
done

theorem relcl_latticeof_eq:
     "[|refl UNIV r; trans r|] ==> relcl (latticeof r) = r"
by (simp add: relcl_def cl_latticeof, blast)


subsubsection {*Decoupling Theorems*}

constdefs
  decoupled :: "['a program, 'a program] => bool"
   "decoupled F G ==
	\<forall>act \<in> Acts F. \<forall>B. G \<in> stable B --> G \<in> stable (wp act B)"


text{*Rao's Decoupling Theorem*}
lemma stableco: "F \<in> stable A ==> F \<in> A-B co A"
by (simp add: stable_def constrains_def, blast) 

theorem decoupling:
  assumes leadsTo: "F \<in> A leadsTo B"
      and Gstable: "G \<in> stable B"
      and dec:     "decoupled F G"
  shows "F\<squnion>G \<in> A leadsTo B"
proof -
  have prog: "{X. G \<in> stable X} \<in> progress_set F UNIV B"
    by (simp add: progress_set_def lattice_stable Gstable closed_def
                  stable_Un [OF Gstable] dec [unfolded decoupled_def]) 
  have "F\<squnion>G \<in> (UNIV\<inter>A) leadsTo B" 
    by (rule progress_set_Union [OF leadsTo prog],
        simp_all add: Gstable stableco)
  thus ?thesis by simp
qed


text{*Rao's Weak Decoupling Theorem*}
theorem weak_decoupling:
  assumes leadsTo: "F \<in> A leadsTo B"
      and stable: "F\<squnion>G \<in> stable B"
      and dec:     "decoupled F (F\<squnion>G)"
  shows "F\<squnion>G \<in> A leadsTo B"
proof -
  have prog: "{X. F\<squnion>G \<in> stable X} \<in> progress_set F UNIV B" 
    by (simp del: Join_stable
             add: progress_set_def lattice_stable stable closed_def
                  stable_Un [OF stable] dec [unfolded decoupled_def])
  have "F\<squnion>G \<in> (UNIV\<inter>A) leadsTo B" 
    by (rule progress_set_Union [OF leadsTo prog],
        simp_all del: Join_stable add: stable,
        simp add: stableco) 
  thus ?thesis by simp
qed

text{*The ``Decoupling via @{term G'} Union Theorem''*}
theorem decoupling_via_aux:
  assumes leadsTo: "F \<in> A leadsTo B"
      and prog: "{X. G' \<in> stable X} \<in> progress_set F UNIV B"
      and GG':  "G \<le> G'"  
               --{*Beware!  This is the converse of the refinement relation!*}
  shows "F\<squnion>G \<in> A leadsTo B"
proof -
  from prog have stable: "G' \<in> stable B"
    by (simp add: progress_set_def)
  have "F\<squnion>G \<in> (UNIV\<inter>A) leadsTo B" 
    by (rule progress_set_Union [OF leadsTo prog],
        simp_all add: stable stableco component_stable [OF GG'])
  thus ?thesis by simp
qed


subsection{*Composition Theorems Based on Monotonicity and Commutativity*}

subsubsection{*Commutativity of @{term "cl L"} and assignment.*}
constdefs 
  commutes :: "['a program, 'a set, 'a set,  'a set set] => bool"
   "commutes F T B L ==
       \<forall>M. \<forall>act \<in> Acts F. B \<subseteq> M --> 
           cl L (T \<inter> wp act M) \<subseteq> T \<inter> (B \<union> wp act (cl L (T\<inter>M)))"


text{*From Meier's thesis, section 4.5.6*}
lemma commutativity1_lemma:
  assumes commutes: "commutes F T B L" 
      and lattice:  "lattice L"
      and BL: "B \<in> L"
      and TL: "T \<in> L"
  shows "closed F T B L"
apply (simp add: closed_def, clarify)
apply (rule ProgressSets.cl_subset_in_lattice [OF _ lattice])  
apply (simp add: Int_Un_distrib cl_Un [OF lattice] Un_subset_iff
                 cl_ident Int_in_lattice [OF TL BL lattice] Un_upper1)
apply (subgoal_tac "cl L (T \<inter> wp act M) \<subseteq> T \<inter> (B \<union> wp act (cl L (T \<inter> M)))") 
 prefer 2 
 apply (simp add: commutes [unfolded commutes_def]) 
apply (erule subset_trans) 
apply (simp add: cl_ident)
apply (blast intro: rev_subsetD [OF _ wp_mono]) 
done

text{*Version packaged with @{thm progress_set_Union}*}
lemma commutativity1:
  assumes leadsTo: "F \<in> A leadsTo B"
      and lattice:  "lattice L"
      and BL: "B \<in> L"
      and TL: "T \<in> L"
      and Fstable: "F \<in> stable T"
      and Gco: "!!X. X\<in>L ==> G \<in> X-B co X"
      and commutes: "commutes F T B L" 
  shows "F\<squnion>G \<in> T\<inter>A leadsTo B"
by (rule progress_set_Union [OF leadsTo _ Fstable subset_refl BL Gco],
    simp add: progress_set_def commutativity1_lemma commutes lattice BL TL) 



text{*Possibly move to Relation.thy, after @{term single_valued}*}
constdefs
  funof :: "[('a*'b)set, 'a] => 'b"
   "funof r == (\<lambda>x. THE y. (x,y) \<in> r)"

lemma funof_eq: "[|single_valued r; (x,y) \<in> r|] ==> funof r x = y"
by (simp add: funof_def single_valued_def, blast)

lemma funof_Pair_in:
     "[|single_valued r; x \<in> Domain r|] ==> (x, funof r x) \<in> r"
by (force simp add: funof_eq) 

lemma funof_in:
     "[|r``{x} \<subseteq> A; single_valued r; x \<in> Domain r|] ==> funof r x \<in> A" 
by (force simp add: funof_eq)
 
lemma funof_imp_wp: "[|funof act t \<in> A; single_valued act|] ==> t \<in> wp act A"
by (force simp add: in_wp_iff funof_eq)


subsubsection{*Commutativity of Functions and Relation*}
text{*Thesis, page 109*}

(*FIXME: this proof is an ungodly mess*)
text{*From Meier's thesis, section 4.5.6*}
lemma commutativity2_lemma:
  assumes dcommutes: 
        "\<forall>act \<in> Acts F. 
         \<forall>s \<in> T. \<forall>t. (s,t) \<in> relcl L --> 
                      s \<in> B | t \<in> B | (funof act s, funof act t) \<in> relcl L"
      and determ: "!!act. act \<in> Acts F ==> single_valued act"
      and total: "!!act. act \<in> Acts F ==> Domain act = UNIV"
      and lattice:  "lattice L"
      and BL: "B \<in> L"
      and TL: "T \<in> L"
      and Fstable: "F \<in> stable T"
  shows  "commutes F T B L"
apply (simp add: commutes_def, clarify)  
apply (rename_tac t)
apply (subgoal_tac "\<exists>s. (s,t) \<in> relcl L & s \<in> T \<inter> wp act M") 
 prefer 2 
 apply (force simp add: cl_eq_Collect_relcl [OF lattice], simp, clarify) 
apply (subgoal_tac "\<forall>u\<in>L. s \<in> u --> t \<in> u") 
 prefer 2 
 apply (intro ballI impI) 
 apply (subst cl_ident [symmetric], assumption)
 apply (simp add: relcl_def)  
 apply (blast intro: cl_mono [THEN [2] rev_subsetD])  
apply (subgoal_tac "funof act s \<in> T\<inter>M") 
 prefer 2 
 apply (cut_tac Fstable) 
 apply (force intro!: funof_in 
              simp add: wp_def stable_def constrains_def determ total) 
apply (subgoal_tac "s \<in> B | t \<in> B | (funof act s, funof act t) \<in> relcl L")
 prefer 2
 apply (rule dcommutes [rule_format], assumption+) 
apply (subgoal_tac "t \<in> B | funof act t \<in> cl L (T\<inter>M)")
 prefer 2 
 apply (simp add: relcl_def)
 apply (blast intro: BL cl_mono [THEN [2] rev_subsetD])  
apply (subgoal_tac "t \<in> B | t \<in> wp act (cl L (T\<inter>M))")
 prefer 2
 apply (blast intro: funof_imp_wp determ) 
apply (blast intro: TL cl_mono [THEN [2] rev_subsetD])  
done


text{*Version packaged with @{thm progress_set_Union}*}
lemma commutativity2:
  assumes leadsTo: "F \<in> A leadsTo B"
      and dcommutes: 
        "\<forall>act \<in> Acts F. 
         \<forall>s \<in> T. \<forall>t. (s,t) \<in> relcl L --> 
                      s \<in> B | t \<in> B | (funof act s, funof act t) \<in> relcl L"
      and determ: "!!act. act \<in> Acts F ==> single_valued act"
      and total: "!!act. act \<in> Acts F ==> Domain act = UNIV"
      and lattice:  "lattice L"
      and BL: "B \<in> L"
      and TL: "T \<in> L"
      and Fstable: "F \<in> stable T"
      and Gco: "!!X. X\<in>L ==> G \<in> X-B co X"
  shows "F\<squnion>G \<in> T\<inter>A leadsTo B"
apply (rule commutativity1 [OF leadsTo lattice]) 
apply (simp_all add: Gco commutativity2_lemma dcommutes determ total
                     lattice BL TL Fstable)
done


subsection {*Monotonicity*}
(*to be continued?*)

end

(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

header{*Progress under Weak Fairness*}

theory WFair = UNITY:

constdefs

  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "'a set => 'a program set"
    "transient A == {F. \<exists>act\<in>Acts F. A \<subseteq> Domain act & act``A \<subseteq> -A}"

  ensures :: "['a set, 'a set] => 'a program set"       (infixl "ensures" 60)
    "A ensures B == (A-B co A \<union> B) \<inter> transient (A-B)"


consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "'a program => ('a set * 'a set) set"


inductive "leads F"
  intros 

    Basis:  "F \<in> A ensures B ==> (A,B) \<in> leads F"

    Trans:  "[| (A,B) \<in> leads F;  (B,C) \<in> leads F |] ==> (A,C) \<in> leads F"

    Union:  "\<forall>A \<in> S. (A,B) \<in> leads F ==> (Union S, B) \<in> leads F"


constdefs

  (*visible version of the LEADS-TO relation*)
  leadsTo :: "['a set, 'a set] => 'a program set"    (infixl "leadsTo" 60)
    "A leadsTo B == {F. (A,B) \<in> leads F}"
  
  (*wlt F B is the largest set that leads to B*)
  wlt :: "['a program, 'a set] => 'a set"
    "wlt F B == Union {A. F \<in> A leadsTo B}"

syntax (xsymbols)
  "op leadsTo" :: "['a set, 'a set] => 'a program set" (infixl "\<longmapsto>" 60)


subsection{*transient*}

lemma stable_transient_empty: 
    "[| F \<in> stable A; F \<in> transient A |] ==> A = {}"
by (unfold stable_def constrains_def transient_def, blast)

lemma transient_strengthen: 
    "[| F \<in> transient A; B \<subseteq> A |] ==> F \<in> transient B"
apply (unfold transient_def, clarify)
apply (blast intro!: rev_bexI)
done

lemma transientI: 
    "[| act: Acts F;  A \<subseteq> Domain act;  act``A \<subseteq> -A |] ==> F \<in> transient A"
by (unfold transient_def, blast)

lemma transientE: 
    "[| F \<in> transient A;   
        !!act. [| act: Acts F;  A \<subseteq> Domain act;  act``A \<subseteq> -A |] ==> P |]  
     ==> P"
by (unfold transient_def, blast)

lemma transient_UNIV [simp]: "transient UNIV = {}"
by (unfold transient_def, blast)

lemma transient_empty [simp]: "transient {} = UNIV"
by (unfold transient_def, auto)


subsection{*ensures*}

lemma ensuresI: 
    "[| F \<in> (A-B) co (A \<union> B); F \<in> transient (A-B) |] ==> F \<in> A ensures B"
by (unfold ensures_def, blast)

lemma ensuresD: 
    "F \<in> A ensures B ==> F \<in> (A-B) co (A \<union> B) & F \<in> transient (A-B)"
by (unfold ensures_def, blast)

lemma ensures_weaken_R: 
    "[| F \<in> A ensures A'; A'<=B' |] ==> F \<in> A ensures B'"
apply (unfold ensures_def)
apply (blast intro: constrains_weaken transient_strengthen)
done

(*The L-version (precondition strengthening) fails, but we have this*)
lemma stable_ensures_Int: 
    "[| F \<in> stable C;  F \<in> A ensures B |]    
    ==> F \<in> (C \<inter> A) ensures (C \<inter> B)"
apply (unfold ensures_def)
apply (auto simp add: ensures_def Int_Un_distrib [symmetric] Diff_Int_distrib [symmetric])
prefer 2 apply (blast intro: transient_strengthen)
apply (blast intro: stable_constrains_Int constrains_weaken)
done

lemma stable_transient_ensures:
     "[| F \<in> stable A;  F \<in> transient C;  A \<subseteq> B \<union> C |] ==> F \<in> A ensures B"
apply (simp add: ensures_def stable_def)
apply (blast intro: constrains_weaken transient_strengthen)
done

lemma ensures_eq: "(A ensures B) = (A unless B) \<inter> transient (A-B)"
by (simp (no_asm) add: ensures_def unless_def)


subsection{*leadsTo*}

lemma leadsTo_Basis [intro]: "F \<in> A ensures B ==> F \<in> A leadsTo B"
apply (unfold leadsTo_def)
apply (blast intro: leads.Basis)
done

lemma leadsTo_Trans: 
     "[| F \<in> A leadsTo B;  F \<in> B leadsTo C |] ==> F \<in> A leadsTo C"
apply (unfold leadsTo_def)
apply (blast intro: leads.Trans)
done

lemma transient_imp_leadsTo: "F \<in> transient A ==> F \<in> A leadsTo (-A)"
by (simp (no_asm_simp) add: leadsTo_Basis ensuresI Compl_partition)

(*Useful with cancellation, disjunction*)
lemma leadsTo_Un_duplicate: "F \<in> A leadsTo (A' \<union> A') ==> F \<in> A leadsTo A'"
by (simp add: Un_ac)

lemma leadsTo_Un_duplicate2:
     "F \<in> A leadsTo (A' \<union> C \<union> C) ==> F \<in> A leadsTo (A' \<union> C)"
by (simp add: Un_ac)

(*The Union introduction rule as we should have liked to state it*)
lemma leadsTo_Union: 
    "(!!A. A \<in> S ==> F \<in> A leadsTo B) ==> F \<in> (Union S) leadsTo B"
apply (unfold leadsTo_def)
apply (blast intro: leads.Union)
done

lemma leadsTo_Union_Int: 
 "(!!A. A \<in> S ==> F \<in> (A \<inter> C) leadsTo B) ==> F \<in> (Union S \<inter> C) leadsTo B"
apply (unfold leadsTo_def)
apply (simp only: Int_Union_Union)
apply (blast intro: leads.Union)
done

lemma leadsTo_UN: 
    "(!!i. i \<in> I ==> F \<in> (A i) leadsTo B) ==> F \<in> (\<Union>i \<in> I. A i) leadsTo B"
apply (subst Union_image_eq [symmetric])
apply (blast intro: leadsTo_Union)
done

(*Binary union introduction rule*)
lemma leadsTo_Un:
     "[| F \<in> A leadsTo C; F \<in> B leadsTo C |] ==> F \<in> (A \<union> B) leadsTo C"
apply (subst Un_eq_Union)
apply (blast intro: leadsTo_Union)
done

lemma single_leadsTo_I: 
     "(!!x. x \<in> A ==> F \<in> {x} leadsTo B) ==> F \<in> A leadsTo B"
by (subst UN_singleton [symmetric], rule leadsTo_UN, blast)


(*The INDUCTION rule as we should have liked to state it*)
lemma leadsTo_induct: 
  "[| F \<in> za leadsTo zb;   
      !!A B. F \<in> A ensures B ==> P A B;  
      !!A B C. [| F \<in> A leadsTo B; P A B; F \<in> B leadsTo C; P B C |]  
               ==> P A C;  
      !!B S. \<forall>A \<in> S. F \<in> A leadsTo B & P A B ==> P (Union S) B  
   |] ==> P za zb"
apply (unfold leadsTo_def)
apply (drule CollectD, erule leads.induct)
apply (blast+)
done


lemma subset_imp_ensures: "A \<subseteq> B ==> F \<in> A ensures B"
by (unfold ensures_def constrains_def transient_def, blast)

lemmas subset_imp_leadsTo = subset_imp_ensures [THEN leadsTo_Basis, standard]

lemmas leadsTo_refl = subset_refl [THEN subset_imp_leadsTo, standard]

lemmas empty_leadsTo = empty_subsetI [THEN subset_imp_leadsTo, standard, simp]

lemmas leadsTo_UNIV = subset_UNIV [THEN subset_imp_leadsTo, standard, simp]



(** Variant induction rule: on the preconditions for B **)

(*Lemma is the weak version: can't see how to do it in one step*)
lemma leadsTo_induct_pre_lemma: 
  "[| F \<in> za leadsTo zb;   
      P zb;  
      !!A B. [| F \<in> A ensures B;  P B |] ==> P A;  
      !!S. \<forall>A \<in> S. P A ==> P (Union S)  
   |] ==> P za"
(*by induction on this formula*)
apply (subgoal_tac "P zb --> P za")
(*now solve first subgoal: this formula is sufficient*)
apply (blast intro: leadsTo_refl)
apply (erule leadsTo_induct)
apply (blast+)
done

lemma leadsTo_induct_pre: 
  "[| F \<in> za leadsTo zb;   
      P zb;  
      !!A B. [| F \<in> A ensures B;  F \<in> B leadsTo zb;  P B |] ==> P A;  
      !!S. \<forall>A \<in> S. F \<in> A leadsTo zb & P A ==> P (Union S)  
   |] ==> P za"
apply (subgoal_tac "F \<in> za leadsTo zb & P za")
apply (erule conjunct2)
apply (erule leadsTo_induct_pre_lemma)
prefer 3 apply (blast intro: leadsTo_Union)
prefer 2 apply (blast intro: leadsTo_Trans)
apply (blast intro: leadsTo_refl)
done


lemma leadsTo_weaken_R: "[| F \<in> A leadsTo A'; A'<=B' |] ==> F \<in> A leadsTo B'"
by (blast intro: subset_imp_leadsTo leadsTo_Trans)

lemma leadsTo_weaken_L [rule_format]:
     "[| F \<in> A leadsTo A'; B \<subseteq> A |] ==> F \<in> B leadsTo A'"
by (blast intro: leadsTo_Trans subset_imp_leadsTo)

(*Distributes over binary unions*)
lemma leadsTo_Un_distrib:
     "F \<in> (A \<union> B) leadsTo C  =  (F \<in> A leadsTo C & F \<in> B leadsTo C)"
by (blast intro: leadsTo_Un leadsTo_weaken_L)

lemma leadsTo_UN_distrib:
     "F \<in> (\<Union>i \<in> I. A i) leadsTo B  =  (\<forall>i \<in> I. F \<in> (A i) leadsTo B)"
by (blast intro: leadsTo_UN leadsTo_weaken_L)

lemma leadsTo_Union_distrib:
     "F \<in> (Union S) leadsTo B  =  (\<forall>A \<in> S. F \<in> A leadsTo B)"
by (blast intro: leadsTo_Union leadsTo_weaken_L)


lemma leadsTo_weaken:
     "[| F \<in> A leadsTo A'; B \<subseteq> A; A'<=B' |] ==> F \<in> B leadsTo B'"
by (blast intro: leadsTo_weaken_R leadsTo_weaken_L leadsTo_Trans)


(*Set difference: maybe combine with leadsTo_weaken_L?*)
lemma leadsTo_Diff:
     "[| F \<in> (A-B) leadsTo C; F \<in> B leadsTo C |]   ==> F \<in> A leadsTo C"
by (blast intro: leadsTo_Un leadsTo_weaken)

lemma leadsTo_UN_UN:
   "(!! i. i \<in> I ==> F \<in> (A i) leadsTo (A' i))  
    ==> F \<in> (\<Union>i \<in> I. A i) leadsTo (\<Union>i \<in> I. A' i)"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: leadsTo_Union leadsTo_weaken_R)
done

(*Binary union version*)
lemma leadsTo_Un_Un:
     "[| F \<in> A leadsTo A'; F \<in> B leadsTo B' |]  
      ==> F \<in> (A \<union> B) leadsTo (A' \<union> B')"
by (blast intro: leadsTo_Un leadsTo_weaken_R)


(** The cancellation law **)

lemma leadsTo_cancel2:
     "[| F \<in> A leadsTo (A' \<union> B); F \<in> B leadsTo B' |]  
      ==> F \<in> A leadsTo (A' \<union> B')"
by (blast intro: leadsTo_Un_Un subset_imp_leadsTo leadsTo_Trans)

lemma leadsTo_cancel_Diff2:
     "[| F \<in> A leadsTo (A' \<union> B); F \<in> (B-A') leadsTo B' |]  
      ==> F \<in> A leadsTo (A' \<union> B')"
apply (rule leadsTo_cancel2)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done

lemma leadsTo_cancel1:
     "[| F \<in> A leadsTo (B \<union> A'); F \<in> B leadsTo B' |]  
    ==> F \<in> A leadsTo (B' \<union> A')"
apply (simp add: Un_commute)
apply (blast intro!: leadsTo_cancel2)
done

lemma leadsTo_cancel_Diff1:
     "[| F \<in> A leadsTo (B \<union> A'); F \<in> (B-A') leadsTo B' |]  
    ==> F \<in> A leadsTo (B' \<union> A')"
apply (rule leadsTo_cancel1)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done



(** The impossibility law **)

lemma leadsTo_empty: "F \<in> A leadsTo {} ==> A={}"
apply (erule leadsTo_induct_pre)
apply (simp_all add: ensures_def constrains_def transient_def, blast)
done


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
lemma psp_stable: 
   "[| F \<in> A leadsTo A'; F \<in> stable B |]  
    ==> F \<in> (A \<inter> B) leadsTo (A' \<inter> B)"
apply (unfold stable_def)
apply (erule leadsTo_induct)
prefer 3 apply (blast intro: leadsTo_Union_Int)
prefer 2 apply (blast intro: leadsTo_Trans)
apply (rule leadsTo_Basis)
apply (simp add: ensures_def Diff_Int_distrib2 [symmetric] Int_Un_distrib2 [symmetric])
apply (blast intro: transient_strengthen constrains_Int)
done

lemma psp_stable2: 
   "[| F \<in> A leadsTo A'; F \<in> stable B |] ==> F \<in> (B \<inter> A) leadsTo (B \<inter> A')"
by (simp add: psp_stable Int_ac)

lemma psp_ensures: 
   "[| F \<in> A ensures A'; F \<in> B co B' |]  
    ==> F \<in> (A \<inter> B') ensures ((A' \<inter> B) \<union> (B' - B))"
apply (unfold ensures_def constrains_def, clarify) (*speeds up the proof*)
apply (blast intro: transient_strengthen)
done

lemma psp:
     "[| F \<in> A leadsTo A'; F \<in> B co B' |]  
      ==> F \<in> (A \<inter> B') leadsTo ((A' \<inter> B) \<union> (B' - B))"
apply (erule leadsTo_induct)
  prefer 3 apply (blast intro: leadsTo_Union_Int)
 txt{*Basis case*}
 apply (blast intro: psp_ensures)
txt{*Transitivity case has a delicate argument involving "cancellation"*}
apply (rule leadsTo_Un_duplicate2)
apply (erule leadsTo_cancel_Diff1)
apply (simp add: Int_Diff Diff_triv)
apply (blast intro: leadsTo_weaken_L dest: constrains_imp_subset)
done

lemma psp2:
     "[| F \<in> A leadsTo A'; F \<in> B co B' |]  
    ==> F \<in> (B' \<inter> A) leadsTo ((B \<inter> A') \<union> (B' - B))"
by (simp (no_asm_simp) add: psp Int_ac)

lemma psp_unless: 
   "[| F \<in> A leadsTo A';  F \<in> B unless B' |]  
    ==> F \<in> (A \<inter> B) leadsTo ((A' \<inter> B) \<union> B')"

apply (unfold unless_def)
apply (drule psp, assumption)
apply (blast intro: leadsTo_weaken)
done


subsection{*Proving the induction rules*}

(** The most general rule: r is any wf relation; f is any variant function **)

lemma leadsTo_wf_induct_lemma:
     "[| wf r;      
         \<forall>m. F \<in> (A \<inter> f-`{m}) leadsTo                      
                    ((A \<inter> f-`(r^-1 `` {m})) \<union> B) |]  
      ==> F \<in> (A \<inter> f-`{m}) leadsTo B"
apply (erule_tac a = m in wf_induct)
apply (subgoal_tac "F \<in> (A \<inter> (f -` (r^-1 `` {x}))) leadsTo B")
 apply (blast intro: leadsTo_cancel1 leadsTo_Un_duplicate)
apply (subst vimage_eq_UN)
apply (simp only: UN_simps [symmetric])
apply (blast intro: leadsTo_UN)
done


(** Meta or object quantifier ? **)
lemma leadsTo_wf_induct:
     "[| wf r;      
         \<forall>m. F \<in> (A \<inter> f-`{m}) leadsTo                      
                    ((A \<inter> f-`(r^-1 `` {m})) \<union> B) |]  
      ==> F \<in> A leadsTo B"
apply (rule_tac t = A in subst)
 defer 1
 apply (rule leadsTo_UN)
 apply (erule leadsTo_wf_induct_lemma)
 apply assumption
apply fast (*Blast_tac: Function unknown's argument not a parameter*)
done


lemma bounded_induct:
     "[| wf r;      
         \<forall>m \<in> I. F \<in> (A \<inter> f-`{m}) leadsTo                    
                      ((A \<inter> f-`(r^-1 `` {m})) \<union> B) |]  
      ==> F \<in> A leadsTo ((A - (f-`I)) \<union> B)"
apply (erule leadsTo_wf_induct, safe)
apply (case_tac "m \<in> I")
apply (blast intro: leadsTo_weaken)
apply (blast intro: subset_imp_leadsTo)
done


(*Alternative proof is via the lemma F \<in> (A \<inter> f-`(lessThan m)) leadsTo B*)
lemma lessThan_induct: 
     "[| !!m::nat. F \<in> (A \<inter> f-`{m}) leadsTo ((A \<inter> f-`{..m(}) \<union> B) |]  
      ==> F \<in> A leadsTo B"
apply (rule wf_less_than [THEN leadsTo_wf_induct])
apply (simp (no_asm_simp))
apply blast
done

lemma lessThan_bounded_induct:
     "!!l::nat. [| \<forall>m \<in> greaterThan l.     
            F \<in> (A \<inter> f-`{m}) leadsTo ((A \<inter> f-`(lessThan m)) \<union> B) |]  
      ==> F \<in> A leadsTo ((A \<inter> (f-`(atMost l))) \<union> B)"
apply (simp only: Diff_eq [symmetric] vimage_Compl Compl_greaterThan [symmetric])
apply (rule wf_less_than [THEN bounded_induct])
apply (simp (no_asm_simp))
done

lemma greaterThan_bounded_induct:
     "(!!l::nat. \<forall>m \<in> lessThan l.     
                 F \<in> (A \<inter> f-`{m}) leadsTo ((A \<inter> f-`(greaterThan m)) \<union> B))
      ==> F \<in> A leadsTo ((A \<inter> (f-`(atLeast l))) \<union> B)"
apply (rule_tac f = f and f1 = "%k. l - k" 
       in wf_less_than [THEN wf_inv_image, THEN leadsTo_wf_induct])
apply (simp (no_asm) add: inv_image_def Image_singleton)
apply clarify
apply (case_tac "m<l")
 apply (blast intro: leadsTo_weaken_R diff_less_mono2)
apply (blast intro: not_leE subset_imp_leadsTo)
done


subsection{*wlt*}

(*Misra's property W3*)
lemma wlt_leadsTo: "F \<in> (wlt F B) leadsTo B"
apply (unfold wlt_def)
apply (blast intro!: leadsTo_Union)
done

lemma leadsTo_subset: "F \<in> A leadsTo B ==> A \<subseteq> wlt F B"
apply (unfold wlt_def)
apply (blast intro!: leadsTo_Union)
done

(*Misra's property W2*)
lemma leadsTo_eq_subset_wlt: "F \<in> A leadsTo B = (A \<subseteq> wlt F B)"
by (blast intro!: leadsTo_subset wlt_leadsTo [THEN leadsTo_weaken_L])

(*Misra's property W4*)
lemma wlt_increasing: "B \<subseteq> wlt F B"
apply (simp (no_asm_simp) add: leadsTo_eq_subset_wlt [symmetric] subset_imp_leadsTo)
done


(*Used in the Trans case below*)
lemma lemma1: 
   "[| B \<subseteq> A2;   
       F \<in> (A1 - B) co (A1 \<union> B);  
       F \<in> (A2 - C) co (A2 \<union> C) |]  
    ==> F \<in> (A1 \<union> A2 - C) co (A1 \<union> A2 \<union> C)"
by (unfold constrains_def, clarify,  blast)

(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
lemma leadsTo_123:
     "F \<in> A leadsTo A'  
      ==> \<exists>B. A \<subseteq> B & F \<in> B leadsTo A' & F \<in> (B-A') co (B \<union> A')"
apply (erule leadsTo_induct)
(*Basis*)
apply (blast dest: ensuresD)
(*Trans*)
apply clarify
apply (rule_tac x = "Ba \<union> Bb" in exI)
apply (blast intro: lemma1 leadsTo_Un_Un leadsTo_cancel1 leadsTo_Un_duplicate)
(*Union*)
apply (clarify dest!: ball_conj_distrib [THEN iffD1] bchoice)
apply (rule_tac x = "\<Union>A \<in> S. f A" in exI)
apply (auto intro: leadsTo_UN)
(*Blast_tac says PROOF FAILED*)
apply (rule_tac I1=S and A1="%i. f i - B" and A'1="%i. f i \<union> B" 
       in constrains_UN [THEN constrains_weaken], auto) 
done


(*Misra's property W5*)
lemma wlt_constrains_wlt: "F \<in> (wlt F B - B) co (wlt F B)"
proof -
  from wlt_leadsTo [of F B, THEN leadsTo_123]
  show ?thesis
  proof (elim exE conjE)
(* assumes have to be in exactly the form as in the goal displayed at
   this point.  Isar doesn't give you any automation. *)
    fix C
    assume wlt: "wlt F B \<subseteq> C"
       and lt:  "F \<in> C leadsTo B"
       and co:  "F \<in> C - B co C \<union> B"
    have eq: "C = wlt F B"
    proof -
      from lt and wlt show ?thesis 
           by (blast dest: leadsTo_eq_subset_wlt [THEN iffD1])
    qed
    from co show ?thesis by (simp add: eq wlt_increasing Un_absorb2)
  qed
qed


subsection{*Completion: Binary and General Finite versions*}

lemma completion_lemma :
     "[| W = wlt F (B' \<union> C);      
       F \<in> A leadsTo (A' \<union> C);  F \<in> A' co (A' \<union> C);    
       F \<in> B leadsTo (B' \<union> C);  F \<in> B' co (B' \<union> C) |]  
    ==> F \<in> (A \<inter> B) leadsTo ((A' \<inter> B') \<union> C)"
apply (subgoal_tac "F \<in> (W-C) co (W \<union> B' \<union> C) ")
 prefer 2
 apply (blast intro: wlt_constrains_wlt [THEN [2] constrains_Un, 
                                         THEN constrains_weaken])
apply (subgoal_tac "F \<in> (W-C) co W")
 prefer 2
 apply (simp add: wlt_increasing Un_assoc Un_absorb2)
apply (subgoal_tac "F \<in> (A \<inter> W - C) leadsTo (A' \<inter> W \<union> C) ")
 prefer 2 apply (blast intro: wlt_leadsTo psp [THEN leadsTo_weaken])
(** LEVEL 6 **)
apply (subgoal_tac "F \<in> (A' \<inter> W \<union> C) leadsTo (A' \<inter> B' \<union> C) ")
 prefer 2
 apply (rule leadsTo_Un_duplicate2)
 apply (blast intro: leadsTo_Un_Un wlt_leadsTo
                         [THEN psp2, THEN leadsTo_weaken] leadsTo_refl)
apply (drule leadsTo_Diff)
apply (blast intro: subset_imp_leadsTo)
apply (subgoal_tac "A \<inter> B \<subseteq> A \<inter> W")
 prefer 2
 apply (blast dest!: leadsTo_subset intro!: subset_refl [THEN Int_mono])
apply (blast intro: leadsTo_Trans subset_imp_leadsTo)
done

lemmas completion = completion_lemma [OF refl]

lemma finite_completion_lemma:
     "finite I ==> (\<forall>i \<in> I. F \<in> (A i) leadsTo (A' i \<union> C)) -->   
                   (\<forall>i \<in> I. F \<in> (A' i) co (A' i \<union> C)) -->  
                   F \<in> (\<Inter>i \<in> I. A i) leadsTo ((\<Inter>i \<in> I. A' i) \<union> C)"
apply (erule finite_induct, auto)
apply (rule completion)
   prefer 4
   apply (simp only: INT_simps [symmetric])
   apply (rule constrains_INT, auto)
done

lemma finite_completion: 
     "[| finite I;   
         !!i. i \<in> I ==> F \<in> (A i) leadsTo (A' i \<union> C);  
         !!i. i \<in> I ==> F \<in> (A' i) co (A' i \<union> C) |]    
      ==> F \<in> (\<Inter>i \<in> I. A i) leadsTo ((\<Inter>i \<in> I. A' i) \<union> C)"
by (blast intro: finite_completion_lemma [THEN mp, THEN mp])

lemma stable_completion: 
     "[| F \<in> A leadsTo A';  F \<in> stable A';    
         F \<in> B leadsTo B';  F \<in> stable B' |]  
    ==> F \<in> (A \<inter> B) leadsTo (A' \<inter> B')"
apply (unfold stable_def)
apply (rule_tac C1 = "{}" in completion [THEN leadsTo_weaken_R])
apply (force+)
done

lemma finite_stable_completion: 
     "[| finite I;   
         !!i. i \<in> I ==> F \<in> (A i) leadsTo (A' i);  
         !!i. i \<in> I ==> F \<in> stable (A' i) |]    
      ==> F \<in> (\<Inter>i \<in> I. A i) leadsTo (\<Inter>i \<in> I. A' i)"
apply (unfold stable_def)
apply (rule_tac C1 = "{}" in finite_completion [THEN leadsTo_weaken_R])
apply (simp_all (no_asm_simp))
apply blast+
done

end

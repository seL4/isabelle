(*  Title:      HOL/UNITY/WFair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak Fairness versions of transient, ensures, leadsTo.

From Misra, "A Logic for Concurrent Programming", 1994
*)

theory WFair = UNITY:

constdefs

  (*This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "'a set => 'a program set"
    "transient A == {F. EX act: Acts F. A <= Domain act & act``A <= -A}"

  ensures :: "['a set, 'a set] => 'a program set"       (infixl "ensures" 60)
    "A ensures B == (A-B co A Un B) Int transient (A-B)"


consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "'a program => ('a set * 'a set) set"


inductive "leads F"
  intros 

    Basis:  "F : A ensures B ==> (A,B) : leads F"

    Trans:  "[| (A,B) : leads F;  (B,C) : leads F |] ==> (A,C) : leads F"

    Union:  "ALL A: S. (A,B) : leads F ==> (Union S, B) : leads F"


constdefs

  (*visible version of the LEADS-TO relation*)
  leadsTo :: "['a set, 'a set] => 'a program set"    (infixl "leadsTo" 60)
    "A leadsTo B == {F. (A,B) : leads F}"
  
  (*wlt F B is the largest set that leads to B*)
  wlt :: "['a program, 'a set] => 'a set"
    "wlt F B == Union {A. F: A leadsTo B}"

syntax (xsymbols)
  "op leadsTo" :: "['a set, 'a set] => 'a program set" (infixl "\<longmapsto>" 60)


(*** transient ***)

lemma stable_transient_empty: 
    "[| F : stable A; F : transient A |] ==> A = {}"

by (unfold stable_def constrains_def transient_def, blast)

lemma transient_strengthen: 
    "[| F : transient A; B<=A |] ==> F : transient B"
apply (unfold transient_def, clarify)
apply (blast intro!: rev_bexI)
done

lemma transientI: 
    "[| act: Acts F;  A <= Domain act;  act``A <= -A |] ==> F : transient A"
by (unfold transient_def, blast)

lemma transientE: 
    "[| F : transient A;   
        !!act. [| act: Acts F;  A <= Domain act;  act``A <= -A |] ==> P |]  
     ==> P"
by (unfold transient_def, blast)

lemma transient_UNIV [simp]: "transient UNIV = {}"
by (unfold transient_def, blast)

lemma transient_empty [simp]: "transient {} = UNIV"
by (unfold transient_def, auto)


(*** ensures ***)

lemma ensuresI: 
    "[| F : (A-B) co (A Un B); F : transient (A-B) |] ==> F : A ensures B"
by (unfold ensures_def, blast)

lemma ensuresD: 
    "F : A ensures B ==> F : (A-B) co (A Un B) & F : transient (A-B)"
by (unfold ensures_def, blast)

lemma ensures_weaken_R: 
    "[| F : A ensures A'; A'<=B' |] ==> F : A ensures B'"
apply (unfold ensures_def)
apply (blast intro: constrains_weaken transient_strengthen)
done

(*The L-version (precondition strengthening) fails, but we have this*)
lemma stable_ensures_Int: 
    "[| F : stable C;  F : A ensures B |]    
    ==> F : (C Int A) ensures (C Int B)"
apply (unfold ensures_def)
apply (auto simp add: ensures_def Int_Un_distrib [symmetric] Diff_Int_distrib [symmetric])
prefer 2 apply (blast intro: transient_strengthen)
apply (blast intro: stable_constrains_Int constrains_weaken)
done

lemma stable_transient_ensures:
     "[| F : stable A;  F : transient C;  A <= B Un C |] ==> F : A ensures B"
apply (simp add: ensures_def stable_def)
apply (blast intro: constrains_weaken transient_strengthen)
done

lemma ensures_eq: "(A ensures B) = (A unless B) Int transient (A-B)"
by (simp (no_asm) add: ensures_def unless_def)


(*** leadsTo ***)

lemma leadsTo_Basis [intro]: "F : A ensures B ==> F : A leadsTo B"
apply (unfold leadsTo_def)
apply (blast intro: leads.Basis)
done

lemma leadsTo_Trans: 
     "[| F : A leadsTo B;  F : B leadsTo C |] ==> F : A leadsTo C"
apply (unfold leadsTo_def)
apply (blast intro: leads.Trans)
done

lemma transient_imp_leadsTo: "F : transient A ==> F : A leadsTo (-A)"
by (simp (no_asm_simp) add: leadsTo_Basis ensuresI Compl_partition)

(*Useful with cancellation, disjunction*)
lemma leadsTo_Un_duplicate: "F : A leadsTo (A' Un A') ==> F : A leadsTo A'"
by (simp add: Un_ac)

lemma leadsTo_Un_duplicate2:
     "F : A leadsTo (A' Un C Un C) ==> F : A leadsTo (A' Un C)"
by (simp add: Un_ac)

(*The Union introduction rule as we should have liked to state it*)
lemma leadsTo_Union: 
    "(!!A. A : S ==> F : A leadsTo B) ==> F : (Union S) leadsTo B"
apply (unfold leadsTo_def)
apply (blast intro: leads.Union)
done

lemma leadsTo_Union_Int: 
 "(!!A. A : S ==> F : (A Int C) leadsTo B) ==> F : (Union S Int C) leadsTo B"
apply (unfold leadsTo_def)
apply (simp only: Int_Union_Union)
apply (blast intro: leads.Union)
done

lemma leadsTo_UN: 
    "(!!i. i : I ==> F : (A i) leadsTo B) ==> F : (UN i:I. A i) leadsTo B"
apply (subst Union_image_eq [symmetric])
apply (blast intro: leadsTo_Union)
done

(*Binary union introduction rule*)
lemma leadsTo_Un:
     "[| F : A leadsTo C; F : B leadsTo C |] ==> F : (A Un B) leadsTo C"
apply (subst Un_eq_Union)
apply (blast intro: leadsTo_Union)
done

lemma single_leadsTo_I: 
     "(!!x. x : A ==> F : {x} leadsTo B) ==> F : A leadsTo B"
by (subst UN_singleton [symmetric], rule leadsTo_UN, blast)


(*The INDUCTION rule as we should have liked to state it*)
lemma leadsTo_induct: 
  "[| F : za leadsTo zb;   
      !!A B. F : A ensures B ==> P A B;  
      !!A B C. [| F : A leadsTo B; P A B; F : B leadsTo C; P B C |]  
               ==> P A C;  
      !!B S. ALL A:S. F : A leadsTo B & P A B ==> P (Union S) B  
   |] ==> P za zb"
apply (unfold leadsTo_def)
apply (drule CollectD, erule leads.induct)
apply (blast+)
done


lemma subset_imp_ensures: "A<=B ==> F : A ensures B"
by (unfold ensures_def constrains_def transient_def, blast)

lemmas subset_imp_leadsTo = subset_imp_ensures [THEN leadsTo_Basis, standard]

lemmas leadsTo_refl = subset_refl [THEN subset_imp_leadsTo, standard]

lemmas empty_leadsTo = empty_subsetI [THEN subset_imp_leadsTo, standard, simp]

lemmas leadsTo_UNIV = subset_UNIV [THEN subset_imp_leadsTo, standard, simp]



(** Variant induction rule: on the preconditions for B **)

(*Lemma is the weak version: can't see how to do it in one step*)
lemma leadsTo_induct_pre_lemma: 
  "[| F : za leadsTo zb;   
      P zb;  
      !!A B. [| F : A ensures B;  P B |] ==> P A;  
      !!S. ALL A:S. P A ==> P (Union S)  
   |] ==> P za"
(*by induction on this formula*)
apply (subgoal_tac "P zb --> P za")
(*now solve first subgoal: this formula is sufficient*)
apply (blast intro: leadsTo_refl)
apply (erule leadsTo_induct)
apply (blast+)
done

lemma leadsTo_induct_pre: 
  "[| F : za leadsTo zb;   
      P zb;  
      !!A B. [| F : A ensures B;  F : B leadsTo zb;  P B |] ==> P A;  
      !!S. ALL A:S. F : A leadsTo zb & P A ==> P (Union S)  
   |] ==> P za"
apply (subgoal_tac "F : za leadsTo zb & P za")
apply (erule conjunct2)
apply (erule leadsTo_induct_pre_lemma)
prefer 3 apply (blast intro: leadsTo_Union)
prefer 2 apply (blast intro: leadsTo_Trans)
apply (blast intro: leadsTo_refl)
done


lemma leadsTo_weaken_R: "[| F : A leadsTo A'; A'<=B' |] ==> F : A leadsTo B'"
by (blast intro: subset_imp_leadsTo leadsTo_Trans)

lemma leadsTo_weaken_L [rule_format (no_asm)]:
     "[| F : A leadsTo A'; B<=A |] ==> F : B leadsTo A'"
by (blast intro: leadsTo_Trans subset_imp_leadsTo)

(*Distributes over binary unions*)
lemma leadsTo_Un_distrib:
     "F : (A Un B) leadsTo C  =  (F : A leadsTo C & F : B leadsTo C)"
by (blast intro: leadsTo_Un leadsTo_weaken_L)

lemma leadsTo_UN_distrib:
     "F : (UN i:I. A i) leadsTo B  =  (ALL i : I. F : (A i) leadsTo B)"
by (blast intro: leadsTo_UN leadsTo_weaken_L)

lemma leadsTo_Union_distrib:
     "F : (Union S) leadsTo B  =  (ALL A : S. F : A leadsTo B)"
by (blast intro: leadsTo_Union leadsTo_weaken_L)


lemma leadsTo_weaken:
     "[| F : A leadsTo A'; B<=A; A'<=B' |] ==> F : B leadsTo B'"
by (blast intro: leadsTo_weaken_R leadsTo_weaken_L leadsTo_Trans)


(*Set difference: maybe combine with leadsTo_weaken_L?*)
lemma leadsTo_Diff:
     "[| F : (A-B) leadsTo C; F : B leadsTo C |]   ==> F : A leadsTo C"
by (blast intro: leadsTo_Un leadsTo_weaken)

lemma leadsTo_UN_UN:
   "(!! i. i:I ==> F : (A i) leadsTo (A' i))  
    ==> F : (UN i:I. A i) leadsTo (UN i:I. A' i)"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: leadsTo_Union leadsTo_weaken_R)
done

(*Binary union version*)
lemma leadsTo_Un_Un:
     "[| F : A leadsTo A'; F : B leadsTo B' |]  
      ==> F : (A Un B) leadsTo (A' Un B')"
by (blast intro: leadsTo_Un leadsTo_weaken_R)


(** The cancellation law **)

lemma leadsTo_cancel2:
     "[| F : A leadsTo (A' Un B); F : B leadsTo B' |]  
      ==> F : A leadsTo (A' Un B')"
by (blast intro: leadsTo_Un_Un subset_imp_leadsTo leadsTo_Trans)

lemma leadsTo_cancel_Diff2:
     "[| F : A leadsTo (A' Un B); F : (B-A') leadsTo B' |]  
      ==> F : A leadsTo (A' Un B')"
apply (rule leadsTo_cancel2)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done

lemma leadsTo_cancel1:
     "[| F : A leadsTo (B Un A'); F : B leadsTo B' |]  
    ==> F : A leadsTo (B' Un A')"
apply (simp add: Un_commute)
apply (blast intro!: leadsTo_cancel2)
done

lemma leadsTo_cancel_Diff1:
     "[| F : A leadsTo (B Un A'); F : (B-A') leadsTo B' |]  
    ==> F : A leadsTo (B' Un A')"
apply (rule leadsTo_cancel1)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done



(** The impossibility law **)

lemma leadsTo_empty: "F : A leadsTo {} ==> A={}"
apply (erule leadsTo_induct_pre)
apply (simp_all add: ensures_def constrains_def transient_def, blast)
done


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
lemma psp_stable: 
   "[| F : A leadsTo A'; F : stable B |]  
    ==> F : (A Int B) leadsTo (A' Int B)"
apply (unfold stable_def)
apply (erule leadsTo_induct)
prefer 3 apply (blast intro: leadsTo_Union_Int)
prefer 2 apply (blast intro: leadsTo_Trans)
apply (rule leadsTo_Basis)
apply (simp add: ensures_def Diff_Int_distrib2 [symmetric] Int_Un_distrib2 [symmetric])
apply (blast intro: transient_strengthen constrains_Int)
done

lemma psp_stable2: 
   "[| F : A leadsTo A'; F : stable B |] ==> F : (B Int A) leadsTo (B Int A')"
by (simp add: psp_stable Int_ac)

lemma psp_ensures: 
   "[| F : A ensures A'; F : B co B' |]  
    ==> F : (A Int B') ensures ((A' Int B) Un (B' - B))"
apply (unfold ensures_def constrains_def, clarify) (*speeds up the proof*)
apply (blast intro: transient_strengthen)
done

lemma psp:
     "[| F : A leadsTo A'; F : B co B' |]  
      ==> F : (A Int B') leadsTo ((A' Int B) Un (B' - B))"
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
     "[| F : A leadsTo A'; F : B co B' |]  
    ==> F : (B' Int A) leadsTo ((B Int A') Un (B' - B))"
by (simp (no_asm_simp) add: psp Int_ac)

lemma psp_unless: 
   "[| F : A leadsTo A';  F : B unless B' |]  
    ==> F : (A Int B) leadsTo ((A' Int B) Un B')"

apply (unfold unless_def)
apply (drule psp, assumption)
apply (blast intro: leadsTo_weaken)
done


(*** Proving the induction rules ***)

(** The most general rule: r is any wf relation; f is any variant function **)

lemma leadsTo_wf_induct_lemma:
     "[| wf r;      
         ALL m. F : (A Int f-`{m}) leadsTo                      
                    ((A Int f-`(r^-1 `` {m})) Un B) |]  
      ==> F : (A Int f-`{m}) leadsTo B"
apply (erule_tac a = m in wf_induct)
apply (subgoal_tac "F : (A Int (f -` (r^-1 `` {x}))) leadsTo B")
 apply (blast intro: leadsTo_cancel1 leadsTo_Un_duplicate)
apply (subst vimage_eq_UN)
apply (simp only: UN_simps [symmetric])
apply (blast intro: leadsTo_UN)
done


(** Meta or object quantifier ? **)
lemma leadsTo_wf_induct:
     "[| wf r;      
         ALL m. F : (A Int f-`{m}) leadsTo                      
                    ((A Int f-`(r^-1 `` {m})) Un B) |]  
      ==> F : A leadsTo B"
apply (rule_tac t = A in subst)
 defer 1
 apply (rule leadsTo_UN)
 apply (erule leadsTo_wf_induct_lemma)
 apply assumption
apply fast (*Blast_tac: Function unknown's argument not a parameter*)
done


lemma bounded_induct:
     "[| wf r;      
         ALL m:I. F : (A Int f-`{m}) leadsTo                    
                      ((A Int f-`(r^-1 `` {m})) Un B) |]  
      ==> F : A leadsTo ((A - (f-`I)) Un B)"
apply (erule leadsTo_wf_induct, safe)
apply (case_tac "m:I")
apply (blast intro: leadsTo_weaken)
apply (blast intro: subset_imp_leadsTo)
done


(*Alternative proof is via the lemma F : (A Int f-`(lessThan m)) leadsTo B*)
lemma lessThan_induct: 
     "[| !!m::nat. F : (A Int f-`{m}) leadsTo ((A Int f-`{..m(}) Un B) |]  
      ==> F : A leadsTo B"
apply (rule wf_less_than [THEN leadsTo_wf_induct])
apply (simp (no_asm_simp))
apply blast
done

lemma lessThan_bounded_induct:
     "!!l::nat. [| ALL m:(greaterThan l).     
            F : (A Int f-`{m}) leadsTo ((A Int f-`(lessThan m)) Un B) |]  
      ==> F : A leadsTo ((A Int (f-`(atMost l))) Un B)"
apply (simp only: Diff_eq [symmetric] vimage_Compl Compl_greaterThan [symmetric])
apply (rule wf_less_than [THEN bounded_induct])
apply (simp (no_asm_simp))
done

lemma greaterThan_bounded_induct:
     "!!l::nat. [| ALL m:(lessThan l).     
            F : (A Int f-`{m}) leadsTo ((A Int f-`(greaterThan m)) Un B) |]  
      ==> F : A leadsTo ((A Int (f-`(atLeast l))) Un B)"
apply (rule_tac f = f and f1 = "%k. l - k" 
       in wf_less_than [THEN wf_inv_image, THEN leadsTo_wf_induct])
apply (simp (no_asm) add: inv_image_def Image_singleton)
apply clarify
apply (case_tac "m<l")
prefer 2 apply (blast intro: not_leE subset_imp_leadsTo)
apply (blast intro: leadsTo_weaken_R diff_less_mono2)
done


(*** wlt ****)

(*Misra's property W3*)
lemma wlt_leadsTo: "F : (wlt F B) leadsTo B"
apply (unfold wlt_def)
apply (blast intro!: leadsTo_Union)
done

lemma leadsTo_subset: "F : A leadsTo B ==> A <= wlt F B"
apply (unfold wlt_def)
apply (blast intro!: leadsTo_Union)
done

(*Misra's property W2*)
lemma leadsTo_eq_subset_wlt: "F : A leadsTo B = (A <= wlt F B)"
by (blast intro!: leadsTo_subset wlt_leadsTo [THEN leadsTo_weaken_L])

(*Misra's property W4*)
lemma wlt_increasing: "B <= wlt F B"
apply (simp (no_asm_simp) add: leadsTo_eq_subset_wlt [symmetric] subset_imp_leadsTo)
done


(*Used in the Trans case below*)
lemma lemma1: 
   "[| B <= A2;   
       F : (A1 - B) co (A1 Un B);  
       F : (A2 - C) co (A2 Un C) |]  
    ==> F : (A1 Un A2 - C) co (A1 Un A2 Un C)"
by (unfold constrains_def, clarify,  blast)

(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
lemma leadsTo_123:
     "F : A leadsTo A'  
      ==> EX B. A<=B & F : B leadsTo A' & F : (B-A') co (B Un A')"
apply (erule leadsTo_induct)
(*Basis*)
apply (blast dest: ensuresD)
(*Trans*)
apply clarify
apply (rule_tac x = "Ba Un Bb" in exI)
apply (blast intro: lemma1 leadsTo_Un_Un leadsTo_cancel1 leadsTo_Un_duplicate)
(*Union*)
apply (clarify dest!: ball_conj_distrib [THEN iffD1] bchoice)
apply (rule_tac x = "UN A:S. f A" in exI)
apply (auto intro: leadsTo_UN)
(*Blast_tac says PROOF FAILED*)
apply (rule_tac I1=S and A1="%i. f i - B" and A'1="%i. f i Un B" 
       in constrains_UN [THEN constrains_weaken])
apply (auto ); 
done


(*Misra's property W5*)
lemma wlt_constrains_wlt: "F : (wlt F B - B) co (wlt F B)"
apply (cut_tac F = F in wlt_leadsTo [THEN leadsTo_123], clarify)
apply (subgoal_tac "Ba = wlt F B")
prefer 2 apply (blast dest: leadsTo_eq_subset_wlt [THEN iffD1], clarify)
apply (simp add: wlt_increasing Un_absorb2)
done


(*** Completion: Binary and General Finite versions ***)

lemma completion_lemma :
     "[| W = wlt F (B' Un C);      
       F : A leadsTo (A' Un C);  F : A' co (A' Un C);    
       F : B leadsTo (B' Un C);  F : B' co (B' Un C) |]  
    ==> F : (A Int B) leadsTo ((A' Int B') Un C)"
apply (subgoal_tac "F : (W-C) co (W Un B' Un C) ")
 prefer 2
 apply (blast intro: wlt_constrains_wlt [THEN [2] constrains_Un, 
                                         THEN constrains_weaken])
apply (subgoal_tac "F : (W-C) co W")
 prefer 2
 apply (simp add: wlt_increasing Un_assoc Un_absorb2)
apply (subgoal_tac "F : (A Int W - C) leadsTo (A' Int W Un C) ")
 prefer 2 apply (blast intro: wlt_leadsTo psp [THEN leadsTo_weaken])
(** LEVEL 6 **)
apply (subgoal_tac "F : (A' Int W Un C) leadsTo (A' Int B' Un C) ")
 prefer 2
 apply (rule leadsTo_Un_duplicate2)
 apply (blast intro: leadsTo_Un_Un wlt_leadsTo
                         [THEN psp2, THEN leadsTo_weaken] leadsTo_refl)
apply (drule leadsTo_Diff)
apply (blast intro: subset_imp_leadsTo)
apply (subgoal_tac "A Int B <= A Int W")
 prefer 2
 apply (blast dest!: leadsTo_subset intro!: subset_refl [THEN Int_mono])
apply (blast intro: leadsTo_Trans subset_imp_leadsTo)
done

lemmas completion = completion_lemma [OF refl]

lemma finite_completion_lemma:
     "finite I ==> (ALL i:I. F : (A i) leadsTo (A' i Un C)) -->   
                   (ALL i:I. F : (A' i) co (A' i Un C)) -->  
                   F : (INT i:I. A i) leadsTo ((INT i:I. A' i) Un C)"
apply (erule finite_induct, auto)
apply (rule completion)
   prefer 4
   apply (simp only: INT_simps [symmetric])
   apply (rule constrains_INT, auto)
done

lemma finite_completion: 
     "[| finite I;   
         !!i. i:I ==> F : (A i) leadsTo (A' i Un C);  
         !!i. i:I ==> F : (A' i) co (A' i Un C) |]    
      ==> F : (INT i:I. A i) leadsTo ((INT i:I. A' i) Un C)"
by (blast intro: finite_completion_lemma [THEN mp, THEN mp])

lemma stable_completion: 
     "[| F : A leadsTo A';  F : stable A';    
         F : B leadsTo B';  F : stable B' |]  
    ==> F : (A Int B) leadsTo (A' Int B')"
apply (unfold stable_def)
apply (rule_tac C1 = "{}" in completion [THEN leadsTo_weaken_R])
apply (force+)
done

lemma finite_stable_completion: 
     "[| finite I;   
         !!i. i:I ==> F : (A i) leadsTo (A' i);  
         !!i. i:I ==> F : stable (A' i) |]    
      ==> F : (INT i:I. A i) leadsTo (INT i:I. A' i)"
apply (unfold stable_def)
apply (rule_tac C1 = "{}" in finite_completion [THEN leadsTo_weaken_R])
apply (simp_all (no_asm_simp))
apply blast+
done

end

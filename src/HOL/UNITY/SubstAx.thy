(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak LeadsTo relation (restricted to the set of reachable states)
*)

theory SubstAx = WFair + Constrains:

constdefs
   Ensures :: "['a set, 'a set] => 'a program set"    (infixl "Ensures" 60)
    "A Ensures B == {F. F : (reachable F Int A) ensures B}"

   LeadsTo :: "['a set, 'a set] => 'a program set"    (infixl "LeadsTo" 60)
    "A LeadsTo B == {F. F : (reachable F Int A) leadsTo B}"

syntax (xsymbols)
  "op LeadsTo" :: "['a set, 'a set] => 'a program set" (infixl " \<longmapsto>w " 60)


(*Resembles the previous definition of LeadsTo*)
lemma LeadsTo_eq_leadsTo: 
     "A LeadsTo B = {F. F : (reachable F Int A) leadsTo (reachable F Int B)}"
apply (unfold LeadsTo_def)
apply (blast dest: psp_stable2 intro: leadsTo_weaken)
done


(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)

lemma Always_LeadsTo_pre:
     "F : Always INV ==> (F : (INV Int A) LeadsTo A') = (F : A LeadsTo A')"
by (simp add: LeadsTo_def Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric])

lemma Always_LeadsTo_post:
     "F : Always INV ==> (F : A LeadsTo (INV Int A')) = (F : A LeadsTo A')"
by (simp add: LeadsTo_eq_leadsTo Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric])

(* [| F : Always C;  F : (C Int A) LeadsTo A' |] ==> F : A LeadsTo A' *)
lemmas Always_LeadsToI = Always_LeadsTo_pre [THEN iffD1, standard]

(* [| F : Always INV;  F : A LeadsTo A' |] ==> F : A LeadsTo (INV Int A') *)
lemmas Always_LeadsToD = Always_LeadsTo_post [THEN iffD2, standard]


(*** Introduction rules: Basis, Trans, Union ***)

lemma leadsTo_imp_LeadsTo: "F : A leadsTo B ==> F : A LeadsTo B"
apply (simp add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_L)
done

lemma LeadsTo_Trans:
     "[| F : A LeadsTo B;  F : B LeadsTo C |] ==> F : A LeadsTo C"
apply (simp add: LeadsTo_eq_leadsTo)
apply (blast intro: leadsTo_Trans)
done

lemma LeadsTo_Union: 
     "(!!A. A : S ==> F : A LeadsTo B) ==> F : (Union S) LeadsTo B"
apply (simp add: LeadsTo_def)
apply (subst Int_Union)
apply (blast intro: leadsTo_UN)
done


(*** Derived rules ***)

lemma LeadsTo_UNIV [simp]: "F : A LeadsTo UNIV"
by (simp add: LeadsTo_def)

(*Useful with cancellation, disjunction*)
lemma LeadsTo_Un_duplicate:
     "F : A LeadsTo (A' Un A') ==> F : A LeadsTo A'"
by (simp add: Un_ac)

lemma LeadsTo_Un_duplicate2:
     "F : A LeadsTo (A' Un C Un C) ==> F : A LeadsTo (A' Un C)"
by (simp add: Un_ac)

lemma LeadsTo_UN: 
     "(!!i. i : I ==> F : (A i) LeadsTo B) ==> F : (UN i:I. A i) LeadsTo B"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: LeadsTo_Union)
done

(*Binary union introduction rule*)
lemma LeadsTo_Un:
     "[| F : A LeadsTo C; F : B LeadsTo C |] ==> F : (A Un B) LeadsTo C"
apply (subst Un_eq_Union)
apply (blast intro: LeadsTo_Union)
done

(*Lets us look at the starting state*)
lemma single_LeadsTo_I:
     "(!!s. s : A ==> F : {s} LeadsTo B) ==> F : A LeadsTo B"
by (subst UN_singleton [symmetric], rule LeadsTo_UN, blast)

lemma subset_imp_LeadsTo: "A <= B ==> F : A LeadsTo B"
apply (simp add: LeadsTo_def)
apply (blast intro: subset_imp_leadsTo)
done

lemmas empty_LeadsTo = empty_subsetI [THEN subset_imp_LeadsTo, standard, simp]

lemma LeadsTo_weaken_R [rule_format]:
     "[| F : A LeadsTo A';  A' <= B' |] ==> F : A LeadsTo B'"
apply (simp (no_asm_use) add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_R)
done

lemma LeadsTo_weaken_L [rule_format]:
     "[| F : A LeadsTo A';  B <= A |]   
      ==> F : B LeadsTo A'"
apply (simp (no_asm_use) add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_L)
done

lemma LeadsTo_weaken:
     "[| F : A LeadsTo A';    
         B  <= A;   A' <= B' |]  
      ==> F : B LeadsTo B'"
by (blast intro: LeadsTo_weaken_R LeadsTo_weaken_L LeadsTo_Trans)

lemma Always_LeadsTo_weaken:
     "[| F : Always C;  F : A LeadsTo A';    
         C Int B <= A;   C Int A' <= B' |]  
      ==> F : B LeadsTo B'"
by (blast dest: Always_LeadsToI intro: LeadsTo_weaken intro: Always_LeadsToD)

(** Two theorems for "proof lattices" **)

lemma LeadsTo_Un_post: "F : A LeadsTo B ==> F : (A Un B) LeadsTo B"
by (blast intro: LeadsTo_Un subset_imp_LeadsTo)

lemma LeadsTo_Trans_Un:
     "[| F : A LeadsTo B;  F : B LeadsTo C |]  
      ==> F : (A Un B) LeadsTo C"
by (blast intro: LeadsTo_Un subset_imp_LeadsTo LeadsTo_weaken_L LeadsTo_Trans)


(** Distributive laws **)

lemma LeadsTo_Un_distrib:
     "(F : (A Un B) LeadsTo C)  = (F : A LeadsTo C & F : B LeadsTo C)"
by (blast intro: LeadsTo_Un LeadsTo_weaken_L)

lemma LeadsTo_UN_distrib:
     "(F : (UN i:I. A i) LeadsTo B)  =  (ALL i : I. F : (A i) LeadsTo B)"
by (blast intro: LeadsTo_UN LeadsTo_weaken_L)

lemma LeadsTo_Union_distrib:
     "(F : (Union S) LeadsTo B)  =  (ALL A : S. F : A LeadsTo B)"
by (blast intro: LeadsTo_Union LeadsTo_weaken_L)


(** More rules using the premise "Always INV" **)

lemma LeadsTo_Basis: "F : A Ensures B ==> F : A LeadsTo B"
by (simp add: Ensures_def LeadsTo_def leadsTo_Basis)

lemma EnsuresI:
     "[| F : (A-B) Co (A Un B);  F : transient (A-B) |]    
      ==> F : A Ensures B"
apply (simp add: Ensures_def Constrains_eq_constrains)
apply (blast intro: ensuresI constrains_weaken transient_strengthen)
done

lemma Always_LeadsTo_Basis:
     "[| F : Always INV;       
         F : (INV Int (A-A')) Co (A Un A');  
         F : transient (INV Int (A-A')) |]    
  ==> F : A LeadsTo A'"
apply (rule Always_LeadsToI, assumption)
apply (blast intro: EnsuresI LeadsTo_Basis Always_ConstrainsD [THEN Constrains_weaken] transient_strengthen)
done

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
lemma LeadsTo_Diff:
     "[| F : (A-B) LeadsTo C;  F : (A Int B) LeadsTo C |]  
      ==> F : A LeadsTo C"
by (blast intro: LeadsTo_Un LeadsTo_weaken)


lemma LeadsTo_UN_UN: 
     "(!! i. i:I ==> F : (A i) LeadsTo (A' i))  
      ==> F : (UN i:I. A i) LeadsTo (UN i:I. A' i)"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: LeadsTo_Union LeadsTo_weaken_R)
done


(*Version with no index set*)
lemma LeadsTo_UN_UN_noindex: 
     "(!! i. F : (A i) LeadsTo (A' i))  
      ==> F : (UN i. A i) LeadsTo (UN i. A' i)"
by (blast intro: LeadsTo_UN_UN)

(*Version with no index set*)
lemma all_LeadsTo_UN_UN:
     "ALL i. F : (A i) LeadsTo (A' i)  
      ==> F : (UN i. A i) LeadsTo (UN i. A' i)"
by (blast intro: LeadsTo_UN_UN)

(*Binary union version*)
lemma LeadsTo_Un_Un:
     "[| F : A LeadsTo A'; F : B LeadsTo B' |]  
            ==> F : (A Un B) LeadsTo (A' Un B')"
by (blast intro: LeadsTo_Un LeadsTo_weaken_R)


(** The cancellation law **)

lemma LeadsTo_cancel2:
     "[| F : A LeadsTo (A' Un B); F : B LeadsTo B' |]     
      ==> F : A LeadsTo (A' Un B')"
by (blast intro: LeadsTo_Un_Un subset_imp_LeadsTo LeadsTo_Trans)

lemma LeadsTo_cancel_Diff2:
     "[| F : A LeadsTo (A' Un B); F : (B-A') LeadsTo B' |]  
      ==> F : A LeadsTo (A' Un B')"
apply (rule LeadsTo_cancel2)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done

lemma LeadsTo_cancel1:
     "[| F : A LeadsTo (B Un A'); F : B LeadsTo B' |]  
      ==> F : A LeadsTo (B' Un A')"
apply (simp add: Un_commute)
apply (blast intro!: LeadsTo_cancel2)
done

lemma LeadsTo_cancel_Diff1:
     "[| F : A LeadsTo (B Un A'); F : (B-A') LeadsTo B' |]  
      ==> F : A LeadsTo (B' Un A')"
apply (rule LeadsTo_cancel1)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done


(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
lemma LeadsTo_empty: "F : A LeadsTo {} ==> F : Always (-A)"
apply (simp (no_asm_use) add: LeadsTo_def Always_eq_includes_reachable)
apply (drule leadsTo_empty, auto)
done


(** PSP: Progress-Safety-Progress **)

(*Special case of PSP: Misra's "stable conjunction"*)
lemma PSP_Stable:
     "[| F : A LeadsTo A';  F : Stable B |]  
      ==> F : (A Int B) LeadsTo (A' Int B)"
apply (simp (no_asm_use) add: LeadsTo_eq_leadsTo Stable_eq_stable)
apply (drule psp_stable, assumption)
apply (simp add: Int_ac)
done

lemma PSP_Stable2:
     "[| F : A LeadsTo A'; F : Stable B |]  
      ==> F : (B Int A) LeadsTo (B Int A')"
by (simp add: PSP_Stable Int_ac)

lemma PSP:
     "[| F : A LeadsTo A'; F : B Co B' |]  
      ==> F : (A Int B') LeadsTo ((A' Int B) Un (B' - B))"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains)
apply (blast dest: psp intro: leadsTo_weaken)
done

lemma PSP2:
     "[| F : A LeadsTo A'; F : B Co B' |]  
      ==> F : (B' Int A) LeadsTo ((B Int A') Un (B' - B))"
by (simp add: PSP Int_ac)

lemma PSP_Unless: 
     "[| F : A LeadsTo A'; F : B Unless B' |]  
      ==> F : (A Int B) LeadsTo ((A' Int B) Un B')"
apply (unfold Unless_def)
apply (drule PSP, assumption)
apply (blast intro: LeadsTo_Diff LeadsTo_weaken subset_imp_LeadsTo)
done


lemma Stable_transient_Always_LeadsTo:
     "[| F : Stable A;  F : transient C;   
         F : Always (-A Un B Un C) |] ==> F : A LeadsTo B"
apply (erule Always_LeadsTo_weaken)
apply (rule LeadsTo_Diff)
   prefer 2
   apply (erule
          transient_imp_leadsTo [THEN leadsTo_imp_LeadsTo, THEN PSP_Stable2])
   apply (blast intro: subset_imp_LeadsTo)+
done


(*** Induction rules ***)

(** Meta or object quantifier ????? **)
lemma LeadsTo_wf_induct:
     "[| wf r;      
         ALL m. F : (A Int f-`{m}) LeadsTo                      
                            ((A Int f-`(r^-1 `` {m})) Un B) |]  
      ==> F : A LeadsTo B"
apply (simp (no_asm_use) add: LeadsTo_eq_leadsTo)
apply (erule leadsTo_wf_induct)
apply (blast intro: leadsTo_weaken)
done


lemma Bounded_induct:
     "[| wf r;      
         ALL m:I. F : (A Int f-`{m}) LeadsTo                    
                              ((A Int f-`(r^-1 `` {m})) Un B) |]  
      ==> F : A LeadsTo ((A - (f-`I)) Un B)"
apply (erule LeadsTo_wf_induct, safe)
apply (case_tac "m:I")
apply (blast intro: LeadsTo_weaken)
apply (blast intro: subset_imp_LeadsTo)
done


lemma LessThan_induct:
     "(!!m::nat. F : (A Int f-`{m}) LeadsTo ((A Int f-`(lessThan m)) Un B))  
      ==> F : A LeadsTo B"
apply (rule wf_less_than [THEN LeadsTo_wf_induct], auto)
done

(*Integer version.  Could generalize from 0 to any lower bound*)
lemma integ_0_le_induct:
     "[| F : Always {s. (0::int) <= f s};   
         !! z. F : (A Int {s. f s = z}) LeadsTo                      
                            ((A Int {s. f s < z}) Un B) |]  
      ==> F : A LeadsTo B"
apply (rule_tac f = "nat o f" in LessThan_induct)
apply (simp add: vimage_def)
apply (rule Always_LeadsTo_weaken, assumption+)
apply (auto simp add: nat_eq_iff nat_less_iff)
done

lemma LessThan_bounded_induct:
     "!!l::nat. [| ALL m:(greaterThan l). F : (A Int f-`{m}) LeadsTo    
                                         ((A Int f-`(lessThan m)) Un B) |]  
            ==> F : A LeadsTo ((A Int (f-`(atMost l))) Un B)"
apply (simp only: Diff_eq [symmetric] vimage_Compl Compl_greaterThan [symmetric])
apply (rule wf_less_than [THEN Bounded_induct])
apply (simp (no_asm_simp))
done

lemma GreaterThan_bounded_induct:
     "!!l::nat. [| ALL m:(lessThan l). F : (A Int f-`{m}) LeadsTo    
                               ((A Int f-`(greaterThan m)) Un B) |]  
      ==> F : A LeadsTo ((A Int (f-`(atLeast l))) Un B)"
apply (rule_tac f = f and f1 = "%k. l - k" 
       in wf_less_than [THEN wf_inv_image, THEN LeadsTo_wf_induct])
apply (simp add: inv_image_def Image_singleton, clarify)
apply (case_tac "m<l")
 prefer 2 apply (blast intro: not_leE subset_imp_LeadsTo)
apply (blast intro: LeadsTo_weaken_R diff_less_mono2)
done


(*** Completion: Binary and General Finite versions ***)

lemma Completion:
     "[| F : A LeadsTo (A' Un C);  F : A' Co (A' Un C);  
         F : B LeadsTo (B' Un C);  F : B' Co (B' Un C) |]  
      ==> F : (A Int B) LeadsTo ((A' Int B') Un C)"
apply (simp (no_asm_use) add: LeadsTo_eq_leadsTo Constrains_eq_constrains Int_Un_distrib)
apply (blast intro: completion leadsTo_weaken)
done

lemma Finite_completion_lemma:
     "finite I  
      ==> (ALL i:I. F : (A i) LeadsTo (A' i Un C)) -->   
          (ALL i:I. F : (A' i) Co (A' i Un C)) -->  
          F : (INT i:I. A i) LeadsTo ((INT i:I. A' i) Un C)"
apply (erule finite_induct, auto)
apply (rule Completion)
   prefer 4
   apply (simp only: INT_simps [symmetric])
   apply (rule Constrains_INT, auto)
done

lemma Finite_completion: 
     "[| finite I;   
         !!i. i:I ==> F : (A i) LeadsTo (A' i Un C);  
         !!i. i:I ==> F : (A' i) Co (A' i Un C) |]    
      ==> F : (INT i:I. A i) LeadsTo ((INT i:I. A' i) Un C)"
by (blast intro: Finite_completion_lemma [THEN mp, THEN mp])

lemma Stable_completion: 
     "[| F : A LeadsTo A';  F : Stable A';    
         F : B LeadsTo B';  F : Stable B' |]  
      ==> F : (A Int B) LeadsTo (A' Int B')"
apply (unfold Stable_def)
apply (rule_tac C1 = "{}" in Completion [THEN LeadsTo_weaken_R])
apply (force+)
done

lemma Finite_stable_completion: 
     "[| finite I;   
         !!i. i:I ==> F : (A i) LeadsTo (A' i);  
         !!i. i:I ==> F : Stable (A' i) |]    
      ==> F : (INT i:I. A i) LeadsTo (INT i:I. A' i)"
apply (unfold Stable_def)
apply (rule_tac C1 = "{}" in Finite_completion [THEN LeadsTo_weaken_R])
apply (simp_all (no_asm_simp))
apply blast+
done


end

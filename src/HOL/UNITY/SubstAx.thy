(*  Title:      HOL/UNITY/SubstAx
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak LeadsTo relation (restricted to the set of reachable states)
*)

header{*Weak Progress*}

theory SubstAx = WFair + Constrains:

constdefs
   Ensures :: "['a set, 'a set] => 'a program set"    (infixl "Ensures" 60)
    "A Ensures B == {F. F \<in> (reachable F \<inter> A) ensures B}"

   LeadsTo :: "['a set, 'a set] => 'a program set"    (infixl "LeadsTo" 60)
    "A LeadsTo B == {F. F \<in> (reachable F \<inter> A) leadsTo B}"

syntax (xsymbols)
  "op LeadsTo" :: "['a set, 'a set] => 'a program set" (infixl " \<longmapsto>w " 60)


text{*Resembles the previous definition of LeadsTo*}
lemma LeadsTo_eq_leadsTo: 
     "A LeadsTo B = {F. F \<in> (reachable F \<inter> A) leadsTo (reachable F \<inter> B)}"
apply (unfold LeadsTo_def)
apply (blast dest: psp_stable2 intro: leadsTo_weaken)
done


subsection{*Specialized laws for handling invariants*}

(** Conjoining an Always property **)

lemma Always_LeadsTo_pre:
     "F \<in> Always INV ==> (F \<in> (INV \<inter> A) LeadsTo A') = (F \<in> A LeadsTo A')"
by (simp add: LeadsTo_def Always_eq_includes_reachable Int_absorb2 
              Int_assoc [symmetric])

lemma Always_LeadsTo_post:
     "F \<in> Always INV ==> (F \<in> A LeadsTo (INV \<inter> A')) = (F \<in> A LeadsTo A')"
by (simp add: LeadsTo_eq_leadsTo Always_eq_includes_reachable Int_absorb2 
              Int_assoc [symmetric])

(* [| F \<in> Always C;  F \<in> (C \<inter> A) LeadsTo A' |] ==> F \<in> A LeadsTo A' *)
lemmas Always_LeadsToI = Always_LeadsTo_pre [THEN iffD1, standard]

(* [| F \<in> Always INV;  F \<in> A LeadsTo A' |] ==> F \<in> A LeadsTo (INV \<inter> A') *)
lemmas Always_LeadsToD = Always_LeadsTo_post [THEN iffD2, standard]


subsection{*Introduction rules: Basis, Trans, Union*}

lemma leadsTo_imp_LeadsTo: "F \<in> A leadsTo B ==> F \<in> A LeadsTo B"
apply (simp add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_L)
done

lemma LeadsTo_Trans:
     "[| F \<in> A LeadsTo B;  F \<in> B LeadsTo C |] ==> F \<in> A LeadsTo C"
apply (simp add: LeadsTo_eq_leadsTo)
apply (blast intro: leadsTo_Trans)
done

lemma LeadsTo_Union: 
     "(!!A. A \<in> S ==> F \<in> A LeadsTo B) ==> F \<in> (Union S) LeadsTo B"
apply (simp add: LeadsTo_def)
apply (subst Int_Union)
apply (blast intro: leadsTo_UN)
done


subsection{*Derived rules*}

lemma LeadsTo_UNIV [simp]: "F \<in> A LeadsTo UNIV"
by (simp add: LeadsTo_def)

text{*Useful with cancellation, disjunction*}
lemma LeadsTo_Un_duplicate:
     "F \<in> A LeadsTo (A' \<union> A') ==> F \<in> A LeadsTo A'"
by (simp add: Un_ac)

lemma LeadsTo_Un_duplicate2:
     "F \<in> A LeadsTo (A' \<union> C \<union> C) ==> F \<in> A LeadsTo (A' \<union> C)"
by (simp add: Un_ac)

lemma LeadsTo_UN: 
     "(!!i. i \<in> I ==> F \<in> (A i) LeadsTo B) ==> F \<in> (\<Union>i \<in> I. A i) LeadsTo B"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: LeadsTo_Union)
done

text{*Binary union introduction rule*}
lemma LeadsTo_Un:
     "[| F \<in> A LeadsTo C; F \<in> B LeadsTo C |] ==> F \<in> (A \<union> B) LeadsTo C"
apply (subst Un_eq_Union)
apply (blast intro: LeadsTo_Union)
done

text{*Lets us look at the starting state*}
lemma single_LeadsTo_I:
     "(!!s. s \<in> A ==> F \<in> {s} LeadsTo B) ==> F \<in> A LeadsTo B"
by (subst UN_singleton [symmetric], rule LeadsTo_UN, blast)

lemma subset_imp_LeadsTo: "A \<subseteq> B ==> F \<in> A LeadsTo B"
apply (simp add: LeadsTo_def)
apply (blast intro: subset_imp_leadsTo)
done

lemmas empty_LeadsTo = empty_subsetI [THEN subset_imp_LeadsTo, standard, simp]

lemma LeadsTo_weaken_R [rule_format]:
     "[| F \<in> A LeadsTo A';  A' \<subseteq> B' |] ==> F \<in> A LeadsTo B'"
apply (simp add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_R)
done

lemma LeadsTo_weaken_L [rule_format]:
     "[| F \<in> A LeadsTo A';  B \<subseteq> A |]   
      ==> F \<in> B LeadsTo A'"
apply (simp add: LeadsTo_def)
apply (blast intro: leadsTo_weaken_L)
done

lemma LeadsTo_weaken:
     "[| F \<in> A LeadsTo A';    
         B  \<subseteq> A;   A' \<subseteq> B' |]  
      ==> F \<in> B LeadsTo B'"
by (blast intro: LeadsTo_weaken_R LeadsTo_weaken_L LeadsTo_Trans)

lemma Always_LeadsTo_weaken:
     "[| F \<in> Always C;  F \<in> A LeadsTo A';    
         C \<inter> B \<subseteq> A;   C \<inter> A' \<subseteq> B' |]  
      ==> F \<in> B LeadsTo B'"
by (blast dest: Always_LeadsToI intro: LeadsTo_weaken intro: Always_LeadsToD)

(** Two theorems for "proof lattices" **)

lemma LeadsTo_Un_post: "F \<in> A LeadsTo B ==> F \<in> (A \<union> B) LeadsTo B"
by (blast intro: LeadsTo_Un subset_imp_LeadsTo)

lemma LeadsTo_Trans_Un:
     "[| F \<in> A LeadsTo B;  F \<in> B LeadsTo C |]  
      ==> F \<in> (A \<union> B) LeadsTo C"
by (blast intro: LeadsTo_Un subset_imp_LeadsTo LeadsTo_weaken_L LeadsTo_Trans)


(** Distributive laws **)

lemma LeadsTo_Un_distrib:
     "(F \<in> (A \<union> B) LeadsTo C)  = (F \<in> A LeadsTo C & F \<in> B LeadsTo C)"
by (blast intro: LeadsTo_Un LeadsTo_weaken_L)

lemma LeadsTo_UN_distrib:
     "(F \<in> (\<Union>i \<in> I. A i) LeadsTo B)  =  (\<forall>i \<in> I. F \<in> (A i) LeadsTo B)"
by (blast intro: LeadsTo_UN LeadsTo_weaken_L)

lemma LeadsTo_Union_distrib:
     "(F \<in> (Union S) LeadsTo B)  =  (\<forall>A \<in> S. F \<in> A LeadsTo B)"
by (blast intro: LeadsTo_Union LeadsTo_weaken_L)


(** More rules using the premise "Always INV" **)

lemma LeadsTo_Basis: "F \<in> A Ensures B ==> F \<in> A LeadsTo B"
by (simp add: Ensures_def LeadsTo_def leadsTo_Basis)

lemma EnsuresI:
     "[| F \<in> (A-B) Co (A \<union> B);  F \<in> transient (A-B) |]    
      ==> F \<in> A Ensures B"
apply (simp add: Ensures_def Constrains_eq_constrains)
apply (blast intro: ensuresI constrains_weaken transient_strengthen)
done

lemma Always_LeadsTo_Basis:
     "[| F \<in> Always INV;       
         F \<in> (INV \<inter> (A-A')) Co (A \<union> A');  
         F \<in> transient (INV \<inter> (A-A')) |]    
  ==> F \<in> A LeadsTo A'"
apply (rule Always_LeadsToI, assumption)
apply (blast intro: EnsuresI LeadsTo_Basis Always_ConstrainsD [THEN Constrains_weaken] transient_strengthen)
done

text{*Set difference: maybe combine with @{text leadsTo_weaken_L}??
  This is the most useful form of the "disjunction" rule*}
lemma LeadsTo_Diff:
     "[| F \<in> (A-B) LeadsTo C;  F \<in> (A \<inter> B) LeadsTo C |]  
      ==> F \<in> A LeadsTo C"
by (blast intro: LeadsTo_Un LeadsTo_weaken)


lemma LeadsTo_UN_UN: 
     "(!! i. i \<in> I ==> F \<in> (A i) LeadsTo (A' i))  
      ==> F \<in> (\<Union>i \<in> I. A i) LeadsTo (\<Union>i \<in> I. A' i)"
apply (simp only: Union_image_eq [symmetric])
apply (blast intro: LeadsTo_Union LeadsTo_weaken_R)
done


text{*Version with no index set*}
lemma LeadsTo_UN_UN_noindex: 
     "(!!i. F \<in> (A i) LeadsTo (A' i)) ==> F \<in> (\<Union>i. A i) LeadsTo (\<Union>i. A' i)"
by (blast intro: LeadsTo_UN_UN)

text{*Version with no index set*}
lemma all_LeadsTo_UN_UN:
     "\<forall>i. F \<in> (A i) LeadsTo (A' i)  
      ==> F \<in> (\<Union>i. A i) LeadsTo (\<Union>i. A' i)"
by (blast intro: LeadsTo_UN_UN)

text{*Binary union version*}
lemma LeadsTo_Un_Un:
     "[| F \<in> A LeadsTo A'; F \<in> B LeadsTo B' |]  
            ==> F \<in> (A \<union> B) LeadsTo (A' \<union> B')"
by (blast intro: LeadsTo_Un LeadsTo_weaken_R)


(** The cancellation law **)

lemma LeadsTo_cancel2:
     "[| F \<in> A LeadsTo (A' \<union> B); F \<in> B LeadsTo B' |]     
      ==> F \<in> A LeadsTo (A' \<union> B')"
by (blast intro: LeadsTo_Un_Un subset_imp_LeadsTo LeadsTo_Trans)

lemma LeadsTo_cancel_Diff2:
     "[| F \<in> A LeadsTo (A' \<union> B); F \<in> (B-A') LeadsTo B' |]  
      ==> F \<in> A LeadsTo (A' \<union> B')"
apply (rule LeadsTo_cancel2)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done

lemma LeadsTo_cancel1:
     "[| F \<in> A LeadsTo (B \<union> A'); F \<in> B LeadsTo B' |]  
      ==> F \<in> A LeadsTo (B' \<union> A')"
apply (simp add: Un_commute)
apply (blast intro!: LeadsTo_cancel2)
done

lemma LeadsTo_cancel_Diff1:
     "[| F \<in> A LeadsTo (B \<union> A'); F \<in> (B-A') LeadsTo B' |]  
      ==> F \<in> A LeadsTo (B' \<union> A')"
apply (rule LeadsTo_cancel1)
prefer 2 apply assumption
apply (simp_all (no_asm_simp))
done


text{*The impossibility law*}

text{*The set "A" may be non-empty, but it contains no reachable states*}
lemma LeadsTo_empty: "[|F \<in> A LeadsTo {}; all_total F|] ==> F \<in> Always (-A)"
apply (simp add: LeadsTo_def Always_eq_includes_reachable)
apply (drule leadsTo_empty, auto)
done


subsection{*PSP: Progress-Safety-Progress*}

text{*Special case of PSP: Misra's "stable conjunction"*}
lemma PSP_Stable:
     "[| F \<in> A LeadsTo A';  F \<in> Stable B |]  
      ==> F \<in> (A \<inter> B) LeadsTo (A' \<inter> B)"
apply (simp add: LeadsTo_eq_leadsTo Stable_eq_stable)
apply (drule psp_stable, assumption)
apply (simp add: Int_ac)
done

lemma PSP_Stable2:
     "[| F \<in> A LeadsTo A'; F \<in> Stable B |]  
      ==> F \<in> (B \<inter> A) LeadsTo (B \<inter> A')"
by (simp add: PSP_Stable Int_ac)

lemma PSP:
     "[| F \<in> A LeadsTo A'; F \<in> B Co B' |]  
      ==> F \<in> (A \<inter> B') LeadsTo ((A' \<inter> B) \<union> (B' - B))"
apply (simp add: LeadsTo_def Constrains_eq_constrains)
apply (blast dest: psp intro: leadsTo_weaken)
done

lemma PSP2:
     "[| F \<in> A LeadsTo A'; F \<in> B Co B' |]  
      ==> F \<in> (B' \<inter> A) LeadsTo ((B \<inter> A') \<union> (B' - B))"
by (simp add: PSP Int_ac)

lemma PSP_Unless: 
     "[| F \<in> A LeadsTo A'; F \<in> B Unless B' |]  
      ==> F \<in> (A \<inter> B) LeadsTo ((A' \<inter> B) \<union> B')"
apply (unfold Unless_def)
apply (drule PSP, assumption)
apply (blast intro: LeadsTo_Diff LeadsTo_weaken subset_imp_LeadsTo)
done


lemma Stable_transient_Always_LeadsTo:
     "[| F \<in> Stable A;  F \<in> transient C;   
         F \<in> Always (-A \<union> B \<union> C) |] ==> F \<in> A LeadsTo B"
apply (erule Always_LeadsTo_weaken)
apply (rule LeadsTo_Diff)
   prefer 2
   apply (erule
          transient_imp_leadsTo [THEN leadsTo_imp_LeadsTo, THEN PSP_Stable2])
   apply (blast intro: subset_imp_LeadsTo)+
done


subsection{*Induction rules*}

(** Meta or object quantifier ????? **)
lemma LeadsTo_wf_induct:
     "[| wf r;      
         \<forall>m. F \<in> (A \<inter> f-`{m}) LeadsTo                      
                    ((A \<inter> f-`(r^-1 `` {m})) \<union> B) |]  
      ==> F \<in> A LeadsTo B"
apply (simp add: LeadsTo_eq_leadsTo)
apply (erule leadsTo_wf_induct)
apply (blast intro: leadsTo_weaken)
done


lemma Bounded_induct:
     "[| wf r;      
         \<forall>m \<in> I. F \<in> (A \<inter> f-`{m}) LeadsTo                    
                      ((A \<inter> f-`(r^-1 `` {m})) \<union> B) |]  
      ==> F \<in> A LeadsTo ((A - (f-`I)) \<union> B)"
apply (erule LeadsTo_wf_induct, safe)
apply (case_tac "m \<in> I")
apply (blast intro: LeadsTo_weaken)
apply (blast intro: subset_imp_LeadsTo)
done


lemma LessThan_induct:
     "(!!m::nat. F \<in> (A \<inter> f-`{m}) LeadsTo ((A \<inter> f-`(lessThan m)) \<union> B))
      ==> F \<in> A LeadsTo B"
by (rule wf_less_than [THEN LeadsTo_wf_induct], auto)

text{*Integer version.  Could generalize from 0 to any lower bound*}
lemma integ_0_le_induct:
     "[| F \<in> Always {s. (0::int) \<le> f s};   
         !! z. F \<in> (A \<inter> {s. f s = z}) LeadsTo                      
                   ((A \<inter> {s. f s < z}) \<union> B) |]  
      ==> F \<in> A LeadsTo B"
apply (rule_tac f = "nat o f" in LessThan_induct)
apply (simp add: vimage_def)
apply (rule Always_LeadsTo_weaken, assumption+)
apply (auto simp add: nat_eq_iff nat_less_iff)
done

lemma LessThan_bounded_induct:
     "!!l::nat. \<forall>m \<in> greaterThan l. 
                   F \<in> (A \<inter> f-`{m}) LeadsTo ((A \<inter> f-`(lessThan m)) \<union> B)
            ==> F \<in> A LeadsTo ((A \<inter> (f-`(atMost l))) \<union> B)"
apply (simp only: Diff_eq [symmetric] vimage_Compl 
                  Compl_greaterThan [symmetric])
apply (rule wf_less_than [THEN Bounded_induct], simp)
done

lemma GreaterThan_bounded_induct:
     "!!l::nat. \<forall>m \<in> lessThan l. 
                 F \<in> (A \<inter> f-`{m}) LeadsTo ((A \<inter> f-`(greaterThan m)) \<union> B)
      ==> F \<in> A LeadsTo ((A \<inter> (f-`(atLeast l))) \<union> B)"
apply (rule_tac f = f and f1 = "%k. l - k" 
       in wf_less_than [THEN wf_inv_image, THEN LeadsTo_wf_induct])
apply (simp add: inv_image_def Image_singleton, clarify)
apply (case_tac "m<l")
 apply (blast intro: LeadsTo_weaken_R diff_less_mono2)
apply (blast intro: not_leE subset_imp_LeadsTo)
done


subsection{*Completion: Binary and General Finite versions*}

lemma Completion:
     "[| F \<in> A LeadsTo (A' \<union> C);  F \<in> A' Co (A' \<union> C);  
         F \<in> B LeadsTo (B' \<union> C);  F \<in> B' Co (B' \<union> C) |]  
      ==> F \<in> (A \<inter> B) LeadsTo ((A' \<inter> B') \<union> C)"
apply (simp add: LeadsTo_eq_leadsTo Constrains_eq_constrains Int_Un_distrib)
apply (blast intro: completion leadsTo_weaken)
done

lemma Finite_completion_lemma:
     "finite I  
      ==> (\<forall>i \<in> I. F \<in> (A i) LeadsTo (A' i \<union> C)) -->   
          (\<forall>i \<in> I. F \<in> (A' i) Co (A' i \<union> C)) -->  
          F \<in> (\<Inter>i \<in> I. A i) LeadsTo ((\<Inter>i \<in> I. A' i) \<union> C)"
apply (erule finite_induct, auto)
apply (rule Completion)
   prefer 4
   apply (simp only: INT_simps [symmetric])
   apply (rule Constrains_INT, auto)
done

lemma Finite_completion: 
     "[| finite I;   
         !!i. i \<in> I ==> F \<in> (A i) LeadsTo (A' i \<union> C);  
         !!i. i \<in> I ==> F \<in> (A' i) Co (A' i \<union> C) |]    
      ==> F \<in> (\<Inter>i \<in> I. A i) LeadsTo ((\<Inter>i \<in> I. A' i) \<union> C)"
by (blast intro: Finite_completion_lemma [THEN mp, THEN mp])

lemma Stable_completion: 
     "[| F \<in> A LeadsTo A';  F \<in> Stable A';    
         F \<in> B LeadsTo B';  F \<in> Stable B' |]  
      ==> F \<in> (A \<inter> B) LeadsTo (A' \<inter> B')"
apply (unfold Stable_def)
apply (rule_tac C1 = "{}" in Completion [THEN LeadsTo_weaken_R])
apply (force+)
done

lemma Finite_stable_completion: 
     "[| finite I;   
         !!i. i \<in> I ==> F \<in> (A i) LeadsTo (A' i);  
         !!i. i \<in> I ==> F \<in> Stable (A' i) |]    
      ==> F \<in> (\<Inter>i \<in> I. A i) LeadsTo (\<Inter>i \<in> I. A' i)"
apply (unfold Stable_def)
apply (rule_tac C1 = "{}" in Finite_completion [THEN LeadsTo_weaken_R])
apply (simp_all, blast+)
done

end

(*  Title:      HOL/UNITY/Detects
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Detects definition (Section 3.8 of Chandy & Misra) using LeadsTo
*)

header{*The Detects Relation*}

theory Detects = FP + SubstAx:

consts
   op_Detects  :: "['a set, 'a set] => 'a program set"  (infixl "Detects" 60)
   op_Equality :: "['a set, 'a set] => 'a set"          (infixl "<==>" 60)
   
defs
  Detects_def:  "A Detects B == (Always (-A \<union> B)) \<inter> (B LeadsTo A)"
  Equality_def: "A <==> B == (-A \<union> B) \<inter> (A \<union> -B)"


(* Corollary from Sectiom 3.6.4 *)

lemma Always_at_FP: "F \<in> A LeadsTo B ==> F \<in> Always (-((FP F) \<inter> A \<inter> -B))"
apply (rule LeadsTo_empty)
apply (subgoal_tac "F \<in> (FP F \<inter> A \<inter> - B) LeadsTo (B \<inter> (FP F \<inter> -B))")
apply (subgoal_tac [2] " (FP F \<inter> A \<inter> - B) = (A \<inter> (FP F \<inter> -B))")
apply (subgoal_tac "(B \<inter> (FP F \<inter> -B)) = {}")
apply auto
apply (blast intro: PSP_Stable stable_imp_Stable stable_FP_Int)
done


lemma Detects_Trans: 
     "[| F \<in> A Detects B; F \<in> B Detects C |] ==> F \<in> A Detects C"
apply (unfold Detects_def Int_def)
apply (simp (no_asm))
apply safe
apply (rule_tac [2] LeadsTo_Trans)
apply auto
apply (subgoal_tac "F \<in> Always ((-A \<union> B) \<inter> (-B \<union> C))")
 apply (blast intro: Always_weaken)
apply (simp add: Always_Int_distrib)
done

lemma Detects_refl: "F \<in> A Detects A"
apply (unfold Detects_def)
apply (simp (no_asm) add: Un_commute Compl_partition subset_imp_LeadsTo)
done

lemma Detects_eq_Un: "(A<==>B) = (A \<inter> B) \<union> (-A \<inter> -B)"
apply (unfold Equality_def)
apply blast
done

(*Not quite antisymmetry: sets A and B agree in all reachable states *)
lemma Detects_antisym: 
     "[| F \<in> A Detects B;  F \<in> B Detects A|] ==> F \<in> Always (A <==> B)"
apply (unfold Detects_def Equality_def)
apply (simp add: Always_Int_I Un_commute)
done


(* Theorem from Section 3.8 *)

lemma Detects_Always: 
     "F \<in> A Detects B ==> F \<in> Always ((-(FP F)) \<union> (A <==> B))"
apply (unfold Detects_def Equality_def)
apply (simp (no_asm) add: Un_Int_distrib Always_Int_distrib)
apply (blast dest: Always_at_FP intro: Always_weaken)
done

(* Theorem from exercise 11.1 Section 11.3.1 *)

lemma Detects_Imp_LeadstoEQ: 
     "F \<in> A Detects B ==> F \<in> UNIV LeadsTo (A <==> B)"
apply (unfold Detects_def Equality_def)
apply (rule_tac B = "B" in LeadsTo_Diff)
 apply (blast intro: Always_LeadsToI subset_imp_LeadsTo)
apply (blast intro: Always_LeadsTo_weaken)
done


end


(*  Title:      HOL/UNITY/Detects
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Detects definition (Section 3.8 of Chandy & Misra) using LeadsTo
*)

theory Detects = FP + SubstAx:

consts
   op_Detects  :: "['a set, 'a set] => 'a program set"  (infixl "Detects" 60)
   op_Equality :: "['a set, 'a set] => 'a set"          (infixl "<==>" 60)
   
defs
  Detects_def:  "A Detects B == (Always (-A Un B)) Int (B LeadsTo A)"
  Equality_def: "A <==> B == (-A Un B) Int (A Un -B)"


(* Corollary from Sectiom 3.6.4 *)

lemma Always_at_FP: "F: A LeadsTo B ==> F : Always (-((FP F) Int A Int -B))"
apply (rule LeadsTo_empty)
apply (subgoal_tac "F : (FP F Int A Int - B) LeadsTo (B Int (FP F Int -B))")
apply (subgoal_tac [2] " (FP F Int A Int - B) = (A Int (FP F Int -B))")
apply (subgoal_tac "(B Int (FP F Int -B)) = {}")
apply auto
apply (blast intro: PSP_Stable stable_imp_Stable stable_FP_Int)
done


lemma Detects_Trans: 
     "[| F : A Detects B; F : B Detects C |] ==> F : A Detects C"
apply (unfold Detects_def Int_def)
apply (simp (no_asm))
apply safe
apply (rule_tac [2] LeadsTo_Trans)
apply auto
apply (subgoal_tac "F : Always ((-A Un B) Int (-B Un C))")
 apply (blast intro: Always_weaken)
apply (simp add: Always_Int_distrib)
done

lemma Detects_refl: "F : A Detects A"
apply (unfold Detects_def)
apply (simp (no_asm) add: Un_commute Compl_partition subset_imp_LeadsTo)
done

lemma Detects_eq_Un: "(A<==>B) = (A Int B) Un (-A Int -B)"
apply (unfold Equality_def)
apply blast
done

(*Not quite antisymmetry: sets A and B agree in all reachable states *)
lemma Detects_antisym: 
     "[| F : A Detects B;  F : B Detects A|] ==> F : Always (A <==> B)"
apply (unfold Detects_def Equality_def)
apply (simp add: Always_Int_I Un_commute)
done


(* Theorem from Section 3.8 *)

lemma Detects_Always: 
     "F : A Detects B ==> F : Always ((-(FP F)) Un (A <==> B))"
apply (unfold Detects_def Equality_def)
apply (simp (no_asm) add: Un_Int_distrib Always_Int_distrib)
apply (blast dest: Always_at_FP intro: Always_weaken)
done

(* Theorem from exercise 11.1 Section 11.3.1 *)

lemma Detects_Imp_LeadstoEQ: 
     "F : A Detects B ==> F : UNIV LeadsTo (A <==> B)"
apply (unfold Detects_def Equality_def)
apply (rule_tac B = "B" in LeadsTo_Diff)
prefer 2 apply (blast intro: Always_LeadsTo_weaken)
apply (blast intro: Always_LeadsToI subset_imp_LeadsTo)
done


end


(*  Title:      HOL/UNITY/Deadlock
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Deadlock examples from section 5.6 of 
    Misra, "A Logic for Concurrent Programming", 1994
*)

theory Deadlock = UNITY:

(*Trivial, two-process case*)
lemma "[| F : (A Int B) co A;  F : (B Int A) co B |] ==> F : stable (A Int B)"
by (unfold constrains_def stable_def, blast)


(*a simplification step*)
lemma Collect_le_Int_equals:
     "(INT i: atMost n. A(Suc i) Int A i) = (INT i: atMost (Suc n). A i)"
apply (induct_tac "n")
apply (simp_all (no_asm_simp) add: atMost_Suc)
apply auto
done

(*Dual of the required property.  Converse inclusion fails.*)
lemma UN_Int_Compl_subset:
     "(UN i: lessThan n. A i) Int (- A n) <=   
      (UN i: lessThan n. (A i) Int (- A (Suc i)))"
apply (induct_tac "n")
apply (simp (no_asm_simp))
apply (simp (no_asm) add: lessThan_Suc)
apply blast
done


(*Converse inclusion fails.*)
lemma INT_Un_Compl_subset:
     "(INT i: lessThan n. -A i Un A (Suc i))  <=  
      (INT i: lessThan n. -A i) Un A n"
apply (induct_tac "n")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) add: lessThan_Suc)
apply blast
done


(*Specialized rewriting*)
lemma INT_le_equals_Int_lemma:
     "A 0 Int (-(A n) Int (INT i: lessThan n. -A i Un A (Suc i))) = {}"
by (blast intro: gr0I dest: INT_Un_Compl_subset [THEN subsetD])

(*Reverse direction makes it harder to invoke the ind hyp*)
lemma INT_le_equals_Int:
     "(INT i: atMost n. A i) =  
      A 0 Int (INT i: lessThan n. -A i Un A(Suc i))"
apply (induct_tac "n", simp)
apply (simp add: Int_ac Int_Un_distrib Int_Un_distrib2
                 INT_le_equals_Int_lemma lessThan_Suc atMost_Suc)
done

lemma INT_le_Suc_equals_Int:
     "(INT i: atMost (Suc n). A i) =  
      A 0 Int (INT i: atMost n. -A i Un A(Suc i))"
by (simp add: lessThan_Suc_atMost INT_le_equals_Int)


(*The final deadlock example*)
lemma
  assumes zeroprem: "F : (A 0 Int A (Suc n)) co (A 0)"
      and allprem:
	    "!!i. i: atMost n ==> F : (A(Suc i) Int A i) co (-A i Un A(Suc i))"
  shows "F : stable (INT i: atMost (Suc n). A i)"
apply (unfold stable_def) 
apply (rule constrains_Int [THEN constrains_weaken])
   apply (rule zeroprem) 
  apply (rule constrains_INT) 
  apply (erule allprem)
 apply (simp add: Collect_le_Int_equals Int_assoc INT_absorb)
apply (simp add: INT_le_Suc_equals_Int)
done

end

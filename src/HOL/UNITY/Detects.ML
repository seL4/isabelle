(*  Title:      HOL/UNITY/Detects
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Detects definition (Section 3.8 of Chandy & Misra) using LeadsTo
*)

(* Corollary from Sectiom 3.6.4 *)

Goal "F: A LeadsTo B ==> F : Always (-((FP F) Int A Int -B))";
by (rtac LeadsTo_empty 1);
by (subgoal_tac "F : (FP F Int A Int - B) LeadsTo (B Int (FP F Int -B))" 1);
by (subgoal_tac "(FP F Int A Int - B) = (A Int (FP F Int -B))" 2);
by (subgoal_tac "(B Int (FP F Int -B)) = {}" 1);
by Auto_tac;
by (blast_tac (claset() addIs [PSP_Stable, stable_imp_Stable, 
			       stable_FP_Int]) 1);
qed "Always_at_FP";


Goalw [Detects_def, Int_def]
     "[| F : A Detects B; F : B Detects C |] ==> F : A Detects C";
by (Simp_tac 1);
by Safe_tac;
by (rtac LeadsTo_Trans 2);
by Auto_tac;
by (subgoal_tac "F : Always ((-A Un B) Int (-B Un C))" 1);
by (simp_tac (simpset() addsimps [Always_Int_distrib]) 2);
by Auto_tac;
by (blast_tac (claset() addIs [Always_weaken]) 1);
qed "Detects_Trans";


Goalw [Detects_def] "F : A Detects A";
by (simp_tac (simpset() addsimps [Un_commute, Compl_partition, 
				  subset_imp_LeadsTo]) 1);
qed "Detects_refl";

Goalw [Equality_def] "(A<==>B) = (A Int B) Un (-A Int -B)";
by (Blast_tac 1);
qed "Detects_eq_Un";

(*Not quite antisymmetry: sets A and B agree in all reachable states *)
Goalw [Detects_def, Equality_def]
     "[| F : A Detects B;  F : B Detects A|] ==> F : Always (A <==> B)";
by (asm_full_simp_tac (simpset() addsimps [Always_Int_I, Un_commute]) 1);
qed "Detects_antisym";


(* Theorem from Section 3.8 *)

Goalw [Detects_def, Equality_def]
     "F : A Detects B ==> F : Always ((-(FP F)) Un (A <==> B))";
by (simp_tac (simpset() addsimps [Un_Int_distrib, Always_Int_distrib]) 1);
by (blast_tac (claset() addDs [Always_at_FP]
			addIs [Always_weaken]) 1);
qed "Detects_Always";

(* Theorem from exercise 11.1 Section 11.3.1 *)

Goalw [Detects_def, Equality_def]
     "F : A Detects B ==> F : UNIV LeadsTo (A <==> B)";
by (res_inst_tac [("B", "B")]  LeadsTo_Diff 1);
by (blast_tac (claset() addIs [Always_LeadsTo_weaken]) 2);
by (blast_tac (claset() addIs [Always_LeadsToI, subset_imp_LeadsTo]) 1);
qed "Detects_Imp_LeadstoEQ";



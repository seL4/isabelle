(*  Title:      HOL/UNITY/Deadlock
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Deadlock examples from section 5.6 of 
    Misra, "A Logic for Concurrent Programming", 1994
*)

(*Trivial, two-process case*)
Goalw [constrains_def, stable_def]
    "[| F : (A Int B) co A;  F : (B Int A) co B |] ==> F : stable (A Int B)";
by (Blast_tac 1);
result();


(*a simplification step*)
Goal "(INT i: atMost n. A(Suc i) Int A i) = (INT i: atMost (Suc n). A i)";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [atMost_Suc])));
by (blast_tac (claset() addEs [le_SucE] addSEs [equalityE]) 1);
qed "Collect_le_Int_equals";


(*Dual of the required property.  Converse inclusion fails.*)
Goal "(UN i: lessThan n. A i) Int (- A n) <=  \
\     (UN i: lessThan n. (A i) Int (- A (Suc i)))";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (simp_tac (simpset() addsimps [lessThan_Suc]) 1);
by (Blast_tac 1);
qed "UN_Int_Compl_subset";


(*Converse inclusion fails.*)
Goal "(INT i: lessThan n. -A i Un A (Suc i))  <= \
\     (INT i: lessThan n. -A i) Un A n";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [lessThan_Suc]) 1);
by (Blast_tac 1);
qed "INT_Un_Compl_subset";


(*Specialized rewriting*)
Goal "A 0 Int (-(A n) Int (INT i: lessThan n. -A i Un A (Suc i))) = {}";
by (blast_tac (claset() addIs [gr0I]
		        addDs [impOfSubs INT_Un_Compl_subset]) 1);
val lemma = result();

(*Reverse direction makes it harder to invoke the ind hyp*)
Goal "(INT i: atMost n. A i) = \
\         A 0 Int (INT i: lessThan n. -A i Un A(Suc i))";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac
    (simpset() addsimps Int_ac @ [Int_Un_distrib, Int_Un_distrib2, lemma,
				  lessThan_Suc, atMost_Suc]) 1);
qed "INT_le_equals_Int";

Goal "(INT i: atMost (Suc n). A i) = \
\     A 0 Int (INT i: atMost n. -A i Un A(Suc i))";
by (simp_tac (simpset() addsimps [lessThan_Suc_atMost, INT_le_equals_Int]) 1);
qed "INT_le_Suc_equals_Int";


(*The final deadlock example*)
val [zeroprem, allprem] = goalw thy [stable_def]
    "[| F : (A 0 Int A (Suc n)) co (A 0);  \
\       ALL i: atMost n. F : (A(Suc i) Int A i) co \
\                            (-A i Un A(Suc i)) |] \
\    ==> F : stable (INT i: atMost (Suc n). A i)";
by (rtac ([zeroprem, allprem RS ball_constrains_INT] MRS 
	  constrains_Int RS constrains_weaken) 1);
by (simp_tac (simpset() addsimps [Collect_le_Int_equals, 
				  Int_assoc, INT_absorb]) 1);
by (simp_tac (simpset() addsimps [INT_le_Suc_equals_Int]) 1);
result();


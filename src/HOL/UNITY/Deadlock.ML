

(*** Deadlock examples from section 5.6 ***)

(*Trivial, two-process case*)
goalw thy [constrains_def, stable_def]
    "!!Acts. [| constrains Acts (A Int B) A;  constrains Acts (B Int A) B |] \
\           ==> stable Acts (A Int B)";
by (Blast_tac 1);
result();


goal thy "{i. i < Suc n} = insert n {i. i < n}";
by (blast_tac (claset() addSEs [less_SucE] addIs [less_SucI]) 1);
qed "Collect_less_Suc_insert";


goal thy "{i. i <= Suc n} = insert (Suc n) {i. i <= n}";
by (blast_tac (claset() addSEs [le_SucE] addIs [le_SucI]) 1);
qed "Collect_le_Suc_insert";


(*a simplification step*)
goal thy "(INT i:{i. i <= n}. A(Suc i) Int A i) = \
\         (INT i:{i. i <= Suc n}. A i)";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Collect_le_Suc_insert])));
by (blast_tac (claset() addEs [le_SucE] addSEs [equalityE]) 1);
qed "Collect_le_Int_equals";


(*Dual of the required property.  Converse inclusion fails.*)
goal thy "(UN i:{i. i < n}. A i) Int Compl (A n) <=  \
\         (UN i:{i. i < n}. (A i) Int Compl (A(Suc i)))";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (simp_tac (simpset() addsimps [Collect_less_Suc_insert]) 1);
by (Blast_tac 1);
qed "UN_Int_Compl_subset";


(*Converse inclusion fails.*)
goal thy "(INT i:{i. i < n}. Compl(A i) Un A (Suc i))  <= \
\         (INT i:{i. i < n}. Compl(A i)) Un A n";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [Collect_less_Suc_insert]) 1);
by (Blast_tac 1);
qed "INT_Un_Compl_subset";


(*Specialized rewriting*)
goal thy "A 0 Int (Compl (A n) Int \
\                  (INT i:{i. i < n}. Compl(A i) Un A (Suc i))) = {}";
by (blast_tac (claset() addIs [gr0I]
		        addDs [impOfSubs INT_Un_Compl_subset]) 1);
val lemma = result();

(*Reverse direction makes it harder to invoke the ind hyp*)
goal thy "(INT i:{i. i <= n}. A i) = \
\         A 0 Int (INT i:{i. i < n}. Compl(A i) Un A(Suc i))";
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac
    (simpset() addsimps (Int_ac @
			 [Int_Un_distrib, Int_Un_distrib2, lemma,
			  Collect_less_Suc_insert, Collect_le_Suc_insert])) 1);
qed "INT_le_equals_Int";

goal thy "(INT i:{i. i <= Suc n}. A i) = \
\         A 0 Int (INT i:{i. i <= n}. Compl(A i) Un A(Suc i))";
by (simp_tac (simpset() addsimps [le_eq_less_Suc RS sym, 
				  INT_le_equals_Int]) 1);
qed "INT_le_Suc_equals_Int";


(*The final deadlock example*)
val [zeroprem, allprem] = goalw thy [stable_def]
    "[| constrains Acts (A 0 Int A (Suc n)) (A 0);  \
\       ALL i:{i. i <= n}. constrains Acts (A(Suc i) Int A i) \
\                                         (Compl(A i) Un A(Suc i)) |] \
\    ==> stable Acts (INT i:{i. i <= Suc n}. A i)";

by (rtac ([zeroprem, allprem RS ball_constrains_INT] MRS 
    constrains_Int RS constrains_weaken) 1);
by (simp_tac (simpset() addsimps [Collect_le_Int_equals, 
				  Int_assoc, INT_absorb]) 1);
by (simp_tac (simpset() addsimps ([INT_le_Suc_equals_Int])) 1);
result();


(*  Title:      HOL/ex/PiSets.ML
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Pi sets and their application.
*)

(*** Bijection between Pi in terms of => and Pi in terms of Sigma ***)
Goal "f \\<in> Pi A B ==> PiBij A B f <= Sigma A B";
by (auto_tac (claset(), simpset() addsimps [PiBij_def,Pi_def]));
qed "PiBij_subset_Sigma";

Goal "f \\<in> Pi A B ==> \\<forall>x \\<in> A. \\<exists>!y. (x, y) \\<in> (PiBij A B f)";
by (auto_tac (claset(), simpset() addsimps [PiBij_def]));
qed "PiBij_unique";

Goal "f \\<in> Pi A B ==> PiBij A B f \\<in> Graph A B";
by (asm_simp_tac (simpset() addsimps [Graph_def,PiBij_unique,
				      PiBij_subset_Sigma]) 1);
qed "PiBij_in_Graph";

Goalw [PiBij_def, Graph_def] "PiBij A B \\<in> Pi A B \\<rightarrow> Graph A B";
by (rtac restrictI 1);
by (auto_tac (claset(), simpset() addsimps [Pi_def]));
qed "PiBij_func";

Goal "inj_on (PiBij A B) (Pi A B)";
by (rtac inj_onI 1);
by (rtac Pi_extensionality 1);			
by (assume_tac 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [PiBij_def]) 1);
by (Blast_tac 1);
qed "inj_PiBij";


Goal "x \\<in> Graph A B \\<Longrightarrow> (%a:A. SOME y. (a, y) \\<in> x) \\<in> Pi A B";
by (rtac restrictI 1);
by (res_inst_tac [("P", "%xa. (a, xa)\\<in>x")] ex1E 1);
 by (force_tac (claset(), simpset() addsimps [Graph_def]) 1);
by (full_simp_tac (simpset() addsimps [Graph_def]) 1);
by (stac some_equality 1);
  by (assume_tac 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "in_Graph_imp_in_Pi";

Goal "PiBij A B ` (Pi A B) = Graph A B";
by (rtac equalityI 1);
by (force_tac (claset(), simpset() addsimps [PiBij_in_Graph]) 1);
by (rtac subsetI 1);
by (rtac image_eqI 1); 
by (etac in_Graph_imp_in_Pi 2); 
(* x = PiBij A B (%a:A. @ y. (a, y)\\<in>x) *)
by (asm_simp_tac (simpset() addsimps [in_Graph_imp_in_Pi, PiBij_def]) 1);
by (auto_tac (claset(), simpset() addsimps [some1_equality, Graph_def])); 
by (fast_tac (claset() addIs [someI2]) 1);
qed "surj_PiBij";

Goal "f \\<in> Pi A B ==> Inv (Pi A B) (PiBij A B) (PiBij A B f) = f";
by (asm_simp_tac (simpset() addsimps [Inv_f_f, inj_PiBij]) 1);
qed "PiBij_bij1";

Goal "f \\<in> Graph A B ==> PiBij A B (Inv (Pi A B) (PiBij A B) f) = f";
by (asm_simp_tac (simpset() addsimps [f_Inv_f, surj_PiBij]) 1);
qed "PiBij_bij2";

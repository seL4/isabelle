(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

(*** component ***)

Goalw [component_def]
     "H <= F | H <= G ==> H <= (F Join G)";
by Auto_tac;
by (res_inst_tac [("x", "G Join Ga")] exI 1);
by (res_inst_tac [("x", "G Join F")] exI 2);
by (auto_tac (claset(), simpset() addsimps Join_ac));
qed "componentI";

Goalw [component_def]
     "(F <= G) = (Init G <= Init F & Acts F <= Acts G)";
by (force_tac (claset() addSIs [exI, program_equalityI], 
	       simpset() addsimps [Acts_Join]) 1);
qed "component_eq_subset";

Goalw [component_def] "SKIP <= F";
by (force_tac (claset() addIs [Join_SKIP_left], simpset()) 1);
qed "component_SKIP";

Goalw [component_def] "F <= (F :: 'a program)";
by (blast_tac (claset() addIs [Join_SKIP_right]) 1);
qed "component_refl";

AddIffs [component_SKIP, component_refl];

Goal "F <= SKIP ==> F = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [component_eq_subset]));
qed "SKIP_minimal";

Goalw [component_def] "F <= (F Join G)";
by (Blast_tac 1);
qed "component_Join1";

Goalw [component_def] "G <= (F Join G)";
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (Blast_tac 1);
qed "component_Join2";

Goalw [component_def] "i : I ==> (F i) <= (JN i:I. (F i))";
by (blast_tac (claset() addIs [JN_absorb]) 1);
qed "component_JN";

Goalw [component_def] "[| F <= G; G <= H |] ==> F <= (H :: 'a program)";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_trans";

Goal "[| F <= G; G <= F |] ==> F = (G :: 'a program)";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (blast_tac (claset() addSIs [program_equalityI]) 1);
qed "component_antisym";

Goalw [component_def]
      "F <= H = (EX G. F Join G = H & Disjoint F G)";
by (blast_tac (claset() addSIs [Diff_Disjoint, Join_Diff2]) 1);
qed "component_eq";

Goal "((F Join G) <= H) = (F <= H & G <= H)";
by (simp_tac (simpset() addsimps [component_eq_subset, Acts_Join]) 1);
by (Blast_tac 1);
qed "Join_component_iff";

Goal "[| F <= G; G : A co B |] ==> F : A co B";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, component_eq_subset]));
qed "component_constrains";

bind_thm ("program_less_le", strict_component_def RS meta_eq_to_obj_eq);

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
	       simpset()) 1);
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

Goal "F<=G ==> F Join G = G";
by (auto_tac (claset(), simpset() addsimps [component_def, Join_left_absorb]));
qed "Join_absorb1";

Goal "G<=F ==> F Join G = F";
by (auto_tac (claset(), simpset() addsimps Join_ac@[component_def]));
qed "Join_absorb2";

Goal "((JOIN I F) <= H) = (ALL i: I. F i <= H)";
by (simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (Blast_tac 1);
qed "JN_component_iff";

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

Goal "((F Join G) <= H) = (F <= H & G <= H)";
by (simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (Blast_tac 1);
qed "Join_component_iff";

Goal "[| F <= G; G : A co B |] ==> F : A co B";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, component_eq_subset]));
qed "component_constrains";

(*Used in Guar.thy to show that programs are partially ordered*)
bind_thm ("program_less_le", strict_component_def RS meta_eq_to_obj_eq);


(*** preserves ***)

Goal "(F Join G : preserves v) = (F : preserves v & G : preserves v)";
by (simp_tac (simpset() addsimps [Join_stable, preserves_def]) 1);
by (Blast_tac 1);
qed "Join_preserves";

Goal "(JOIN I F : preserves v) = (ALL i:I. F i : preserves v)";
by (simp_tac (simpset() addsimps [JN_stable, preserves_def]) 1);
by (Blast_tac 1);
qed "JN_preserves";

AddIffs [Join_preserves, JN_preserves];

Goal "preserves (funPair v w) = preserves v Int preserves w";
by (auto_tac (claset(),
	      simpset() addsimps [funPair_def, preserves_def, 
				  stable_def, constrains_def]));
by (Blast_tac 1);
qed "preserves_funPair";

(* (F : preserves (funPair v w)) = (F : preserves v Int preserves w) *)
AddIffs [preserves_funPair RS eqset_imp_iff];


Goal "(funPair f g) o h = funPair (f o h) (g o h)";
by (simp_tac (simpset() addsimps [funPair_def, o_def]) 1);
qed "funPair_o_distrib";

Goal "preserves v <= preserves (w o v)";
by (force_tac (claset(),
	       simpset() addsimps [preserves_def, 
				   stable_def, constrains_def]) 1);
qed "subset_preserves_o";

Goal "preserves v <= stable {s. P (v s)}";
by (auto_tac (claset(),
	      simpset() addsimps [preserves_def, 
				  stable_def, constrains_def]));
by (rename_tac "s' s" 1);
by (subgoal_tac "v s = v s'" 1);
by (ALLGOALS Force_tac);
qed "preserves_subset_stable";

Goal "preserves id <= stable A";
by (force_tac (claset(), 
	   simpset() addsimps [preserves_def, stable_def, constrains_def]) 1);
qed "preserves_id_subset_stable";


(** Some lemmas used only in Client.ML **)

Goal "[| F : stable {s. P (v s) (w s)};   \
\        G : preserves v;  G : preserves w |]               \
\     ==> F Join G : stable {s. P (v s) (w s)}";
by (asm_simp_tac (simpset() addsimps [Join_stable]) 1);
by (subgoal_tac "G: preserves (funPair v w)" 1);
by (Asm_simp_tac 2);
by (dres_inst_tac [("P1", "split ?Q")]  
    (impOfSubs preserves_subset_stable) 1);
by (auto_tac (claset(), simpset() addsimps [funPair_def]));
qed "stable_localTo_stable2";

Goal "[| F : stable {s. v s <= w s};  G : preserves v;       \
\        F Join G : Increasing w |]               \
\     ==> F Join G : Stable {s. v s <= w s}";
by (auto_tac (claset(), 
	      simpset() addsimps [stable_def, Stable_def, Increasing_def, 
		    Constrains_def, Join_constrains, all_conj_distrib]));
by (blast_tac (claset() addIs [constrains_weaken]) 1);
(*The G case remains*)
by (auto_tac (claset(), 
              simpset() addsimps [preserves_def, stable_def, constrains_def]));
by (case_tac "act: Acts F" 1);
by (Blast_tac 1);
(*We have a G-action, so delete assumptions about F-actions*)
by (thin_tac "ALL act:Acts F. ?P act" 1);
by (thin_tac "ALL z. ALL act:Acts F. ?P z act" 1);
by (subgoal_tac "v x = v xa" 1);
by (Blast_tac 2);
by Auto_tac;
by (etac order_trans 1);
by (Blast_tac 1);
qed "Increasing_preserves_Stable";

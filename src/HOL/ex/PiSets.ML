(*  Title:      HOL/ex/PiSets.ML
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Pi sets and their application.
*)

(*** Bijection between Pi in terms of => and Pi in terms of Sigma ***)
Goal "f: Pi A B ==> PiBij A B f <= Sigma A B";
by (auto_tac (claset(),
	      simpset() addsimps [PiBij_def,Pi_def,restrict_apply1]));
qed "PiBij_subset_Sigma";

Goal "f: Pi A B ==> (! x: A. (?! y. (x, y): (PiBij A B f)))";
by (auto_tac (claset(),
	      simpset() addsimps [PiBij_def,restrict_apply1]));
qed "PiBij_unique";

Goal "f: Pi A B ==> PiBij A B f : Graph A B";
by (asm_simp_tac (simpset() addsimps [Graph_def,PiBij_unique,
				      PiBij_subset_Sigma]) 1);
qed "PiBij_in_Graph";

Goalw [PiBij_def, Graph_def] "PiBij A B:  Pi A B -> Graph A B";
by (rtac restrictI 1);
by (auto_tac (claset(), simpset() addsimps [Pi_def]));
qed "PiBij_func";

Goal "inj_on (PiBij A B) (Pi A B)";
by (rtac inj_onI 1);
by (rtac Pi_extensionality 1);			
by (assume_tac 1);
by (assume_tac 1);
by (rotate_tac 1 1);
by (asm_full_simp_tac (simpset() addsimps [PiBij_def,restrict_apply1]) 1);
by (Blast_tac 1);
qed "inj_PiBij";



Goal "PiBij A B ` (Pi A B) = Graph A B";
by (rtac equalityI 1);
by (force_tac (claset(), simpset() addsimps [image_def,PiBij_in_Graph]) 1);
by (rtac subsetI 1);
by (asm_full_simp_tac (simpset() addsimps [image_def]) 1);
by (res_inst_tac [("x","lam a: A. @ y. (a, y): x")] bexI 1);
 by (rtac restrictI 2);
 by (res_inst_tac [("P", "%xa. (a, xa) : x")] ex1E 2);
  by (force_tac (claset(), simpset() addsimps [Graph_def]) 2);
 by (full_simp_tac (simpset() addsimps [Graph_def]) 2);
  by (stac some_equality 2);
   by (assume_tac 2);
  by (Blast_tac 2);
 by (Blast_tac 2);
(* x = PiBij A B (lam a:A. @ y. (a, y) : x) *)
by (full_simp_tac (simpset() addsimps [PiBij_def,Graph_def]) 1);
by (stac restrict_apply1 1);
 by (rtac restrictI 1);
 by (blast_tac (claset() addSDs [[some_eq_ex, ex1_implies_ex] MRS iffD2]) 1);
(** LEVEL 17 **)
by (rtac equalityI 1);
by (rtac subsetI 1);
by (split_all_tac 1);
by (subgoal_tac "a: A" 1);
by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [restrict_apply1]) 1);
(*Blast_tac: PROOF FAILED for depth 5*)
by (fast_tac (claset() addSIs [some1_equality RS sym]) 1);
(* {(xa,y). xa : A & y = (lam a:A. @ y. (a, y) : x) xa} <= x   *)
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [restrict_apply1]) 1);
by (fast_tac (claset() addIs [someI2]) 1);
qed "surj_PiBij";

Goal "f: Pi A B ==> \
\     (lam y: Graph A B. (Inv (Pi A B)(PiBij A B)) y)(PiBij A B f) = f";
by (asm_simp_tac
    (simpset() addsimps [Inv_f_f, PiBij_func, inj_PiBij, surj_PiBij]) 1);
qed "PiBij_bij1";

Goal "[| f: Graph A B  |] ==> \
\    (PiBij A B) ((lam y: (Graph A B). (Inv (Pi A B)(PiBij A B)) y) f) = f";
by (rtac (PiBij_func RS f_Inv_f) 1);
by (asm_full_simp_tac (simpset() addsimps [surj_PiBij]) 1);
by (assume_tac 1);
qed "PiBij_bij2";


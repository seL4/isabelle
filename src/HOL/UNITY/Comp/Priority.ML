(*  Title:      HOL/UNITY/Priority
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

The priority system

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Addsimps [Component_def RS def_prg_Init];
program_defs_ref := [Component_def, system_def];
Addsimps [highest_def, lowest_def];
Addsimps [simp_of_act  act_def];
Addsimps (map simp_of_set [Highest_def, Lowest_def]);




(**** Component correctness proofs  ****)

(* neighbors is stable  *)
Goal "Component i: stable {s. neighbors k s = n}";
by (constrains_tac 1);
by Auto_tac;
qed "Component_neighbors_stable";

(* property 4 *)
Goal 
"Component i: {s. ((i,j):s) = b} Int (- Highest i) co {s. ((i,j):s)=b}";
by (constrains_tac 1);
qed "Component_waits_priority";  

(* property 5: charpentier and Chandy mistakenly express it as
 'transient Highest i'. Consider the case where i has neighbors *)
Goal
 "Component i: {s. neighbors i s ~= {}} Int Highest i \
\              ensures - Highest i";
by (ensures_tac "act i" 1);
by (REPEAT(Fast_tac 1));
qed "Component_yields_priority"; 

(* or better *)
Goal "Component i: Highest i ensures Lowest i";
by (ensures_tac "act i" 1);
by (REPEAT(Fast_tac 1));
qed "Component_yields_priority'";

(* property 6: Component doesn't introduce cycle *)
Goal "Component i: Highest i co Highest i Un Lowest i";
by (constrains_tac 1);
by (Fast_tac 1);
qed "Component_well_behaves"; 

(* property 7: local axiom *)
Goal "Component i: stable {s. ALL j k. j~=i & k~=i--> ((j,k):s) = b j k}";
by (constrains_tac 1);
qed "locality";  


(**** System  properties  ****)
(* property 8: strictly universal *)

Goalw [Safety_def] 
    "system: stable Safety";
by (rtac stable_INT 1);
by (constrains_tac 1);
by (Fast_tac 1);
qed "Safety"; 

(* property 13: universal *)
Goal
"system: {s. s = q} co {s. s=q} Un {s. EX i. derive i q s}";
by (constrains_tac 1);
by (Blast_tac 1);
qed "p13";

(* property 14: the 'above set' of a Component that hasn't got 
      priority doesn't increase *)
Goal
"ALL j. system: -Highest i Int {s. j~:above i s} co {s. j~:above i s}";
by (Clarify_tac 1);
by (cut_inst_tac [("i", "j")] reach_lemma 1);
by (constrains_tac 1);
by (auto_tac (claset(), simpset() addsimps [trancl_converse]));
qed "above_not_increase";  

Goal 
"system: -Highest i Int {s. above i s = x} co {s. above i s <= x}";
by (cut_inst_tac [("i", "i")] above_not_increase 1);
by (asm_full_simp_tac (simpset() addsimps 
                 [trancl_converse, constrains_def]) 1); 
by (Blast_tac 1);
qed "above_not_increase'";  



(* p15: universal property: all Components well behave  *)
Goal "ALL i. system: Highest i co Highest i Un Lowest i";
by (Clarify_tac 1);
by (constrains_tac 1);
by Auto_tac;
qed "system_well_behaves";  


Goal "Acyclic = (INT i. {s. i~:above i s})";
by (auto_tac (claset(), simpset() 
   addsimps [Acyclic_def, acyclic_def, trancl_converse]));
qed "Acyclic_eq";


val lemma = [above_not_increase RS spec, 
           system_well_behaves RS spec] MRS constrains_Un;
Goal 
"system: stable Acyclic";
by (auto_tac (claset() addSIs [stable_INT, stableI, 
                               lemma RS constrains_weaken],
              simpset() addsimps [Acyclic_eq, 
                    image0_r_iff_image0_trancl,trancl_converse]));
qed "Acyclic_stable";


Goalw [Acyclic_def, Maximal_def]
"Acyclic <= Maximal";
by (Clarify_tac 1);
by (dtac above_lemma_b 1);
by Auto_tac;
qed "Acyclic_subset_Maximal";

(* property 17: original one is an invariant *)
Goal 
"system: stable (Acyclic Int Maximal)";
by (simp_tac (simpset() addsimps 
     [Acyclic_subset_Maximal RS Int_absorb2, Acyclic_stable]) 1);
qed "Acyclic_Maximal_stable";  


(* propert 5: existential property *)

Goal "system: Highest i leadsTo Lowest i";
by (ensures_tac "act i" 1);
by (auto_tac (claset(), simpset() addsimps [Component_def]));
qed "Highest_leadsTo_Lowest";

(* a lowest i can never be in any abover set *) 
Goal "Lowest i <= (INT k. {s. i~:above k s})";
by (auto_tac (claset(), 
          simpset() addsimps [image0_r_iff_image0_trancl, trancl_converse]));
qed  "Lowest_above_subset";

(* property 18: a simpler proof than the original, one which uses psp *)
Goal "system: Highest i leadsTo (INT k. {s. i~:above k s})";
by (rtac leadsTo_weaken_R 1);
by (rtac Lowest_above_subset 2);
by (rtac Highest_leadsTo_Lowest 1);
qed "Highest_escapes_above";

Goal 
"system: Highest j Int {s. j:above i s} leadsTo {s. j~:above i s}";
by (blast_tac (claset() addIs 
   [[Highest_escapes_above, Int_lower1, INT_lower] MRS leadsTo_weaken]) 1);
qed "Highest_escapes_above'"; 

(*** The main result: above set decreases ***)
(* The original proof of the following formula was wrong *)
val above_decreases_lemma = 
[Highest_escapes_above', above_not_increase'] MRS psp RS leadsTo_weaken;

Goal "Highest i = {s. above i s ={}}";
by (auto_tac (claset(), 
        simpset() addsimps [image0_trancl_iff_image0_r]));
qed "Highest_iff_above0";


Goal 
"system: (UN j. {s. above i s = x} Int {s. j:above i s} Int Highest j) \
\          leadsTo {s. above i s < x}";
by (rtac leadsTo_UN 1);
by (rtac single_leadsTo_I 1);
by (Clarify_tac 1);
by (res_inst_tac [("x2", "above i x")] above_decreases_lemma 1);
by (ALLGOALS(full_simp_tac (simpset() delsimps [Highest_def]
                  addsimps [Highest_iff_above0])));
by (REPEAT(Blast_tac 1));
qed "above_decreases";  

(** Just a massage of conditions to have the desired form ***)
Goalw [Maximal_def, Maximal'_def, Highest_def]
"Maximal = Maximal'";
by (Blast_tac 1);
qed "Maximal_eq_Maximal'";

Goal "x~={} ==> \
\   Acyclic Int {s. above i s = x} <= \
\   (UN j. {s. above i s = x} Int {s. j:above i s} Int Highest j)";
by (res_inst_tac [("B", "Maximal' Int {s. above i s = x}")] subset_trans 1);
by (simp_tac (simpset() addsimps [Maximal_eq_Maximal' RS sym]) 1);
by (blast_tac (claset() addIs [Acyclic_subset_Maximal RS subsetD]) 1);
by (simp_tac (simpset() delsimps [above_def] addsimps [Maximal'_def, Highest_iff_above0]) 1);
by (Blast_tac 1);
qed "Acyclic_subset";

val above_decreases' = [above_decreases, Acyclic_subset] MRS leadsTo_weaken_L;
val above_decreases_psp = [above_decreases', Acyclic_stable] MRS psp_stable;

Goal 
"x~={}==> \
\ system: Acyclic Int {s. above i s = x} leadsTo Acyclic Int {s. above i s < x}";
by (etac (above_decreases_psp RS leadsTo_weaken) 1);
by (Blast_tac 1);
by Auto_tac;
qed "above_decreases_psp'";


val finite_psubset_induct = wf_finite_psubset RS leadsTo_wf_induct;
val leadsTo_weaken_L' = rotate_prems 1 leadsTo_weaken_L;


Goal "system: Acyclic leadsTo Highest i";
by (res_inst_tac [("f", "%s. above i s")] finite_psubset_induct 1);
by (asm_simp_tac (simpset() delsimps [Highest_def, above_def] 
                            addsimps [Highest_iff_above0,
                                      vimage_def, finite_psubset_def]) 1); 
by (Clarify_tac 1);
by (case_tac "m={}" 1);
by (rtac (Int_lower2 RS leadsTo_weaken_L') 1);
by (force_tac (claset(), simpset() addsimps [leadsTo_refl]) 1);
by (res_inst_tac [("A'", "Acyclic Int {x. above i x < m}")] 
    leadsTo_weaken_R 1);
by (REPEAT(blast_tac (claset() addIs [above_decreases_psp']) 1));
qed "Progress";

(* We have proved all (relevant) theorems given in the paper *)
(* We didn't assume any thing about the relation r *)
(* It is not necessary that r be a priority relation as assumed in the original proof *)
(* It suffices that we start from a state which is finite and acyclic *)

(*  Title:      HOL/UNITY/Counterc
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version with a full use of "compatibility "

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Addsimps [Component_def RS def_prg_Init, 
Component_def RS def_prg_AllowedActs];
program_defs_ref := [Component_def];
Addsimps (map simp_of_act  [a_def]);

(* Theorems about sum and sumj *)
Goal "ALL i. I<i--> (sum I s = sumj I i s)";
by (induct_tac "I" 1);
by Auto_tac;
qed_spec_mp  "sum_sumj_eq1";

Goal "i<I --> sum I s  = c s i + sumj I i s";
by (induct_tac "I" 1);
by (auto_tac (claset() addSEs [nat_neqE],
              simpset() addsimps [sum_sumj_eq1]));
qed_spec_mp "sum_sumj_eq2";

Goal 
"(ALL i. i<I --> c s' i = c s i) --> (sum I s' = sum I s)";
by (induct_tac "I" 1 THEN Auto_tac);
qed_spec_mp "sum_ext";

Goal 
"(ALL j. j<I & j~=i --> c s' j =  c s j) --> (sumj I i s' = sumj I i s)";
by (induct_tac "I" 1);
by Safe_tac;
by (auto_tac (claset() addSIs [sum_ext], simpset()));
qed_spec_mp "sumj_ext";


Goal "(ALL i. i<I --> c s i = #0) -->  sum I s = #0";
by (induct_tac "I" 1);
by Auto_tac;
qed "sum0";


(* Safety properties for Components *)

Goal "(Component i ok G) = \
\     (G: preserves (%s. c s i) & Component i:Allowed G)";
by (auto_tac (claset(), 
  simpset() addsimps [ok_iff_Allowed, Component_def RS def_prg_Allowed]));  
qed "Component_ok_iff";
AddIffs [Component_ok_iff];
AddIffs [OK_iff_ok];
Addsimps [preserves_def];


Goal "Component i: stable {s. C s = (c s) i + k}";
by (constrains_tac 1);
qed "p2";

Goal 
"[| OK I Component; i:I |] ==> \
\ Component i: stable {s. ALL j:I. j~=i --> c s j = c k j}";
by (full_simp_tac (simpset() addsimps [stable_def, constrains_def]) 1);
by (Blast_tac 1);
qed "p3";


Goal 
"[| OK {i. i<I} Component; i<I |] ==> \
\ ALL k. Component i: stable ({s. C s = c s i + sumj I i k} Int \
\                             {s. ALL j:{i. i<I}. j~=i --> c s j = c k j})";
by (blast_tac (claset() addIs [[p2, p3] MRS stable_Int]) 1);
qed "p2_p3_lemma1";


Goal 
"(ALL k. F:stable ({s. C s = (c s) i + sumj I i k} Int \
\                 {s. ALL j:{i. i<I}. j~=i --> c s j = c k j})) ==> \
\ (F:stable {s. C s = c s i + sumj I i s})";
by (full_simp_tac (simpset() addsimps [constrains_def, stable_def]) 1);
by (force_tac (claset() addSIs [sumj_ext], simpset()) 1);
qed "p2_p3_lemma2";


Goal 
"[| OK {i. i<I} Component; i<I |] ==> \
\ Component i: stable {s. C s = c s i + sumj I i s}";
by (blast_tac (claset() addIs [p2_p3_lemma1 RS p2_p3_lemma2]) 1);
qed "p2_p3";


(* Compositional correctness *)
Goalw [invariant_def]
 "[| 0<I; OK {i. i<I} Component |] ==> \
\     (JN i:{i. i<I}. (Component i)) : invariant {s. C s = sum I s}";
by (simp_tac (simpset() addsimps [JN_stable, sum_sumj_eq2]) 1);
by (auto_tac (claset() addSIs [sum0 RS mp, p2_p3], 
              simpset()));
qed "safety";




















 





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
          Component_def RS def_prg_AllowedActs,
          simp_of_act a_def];

(* Theorems about sum and sumj *)
Goal "\\<forall>i. I<i--> (sum I s = sumj I i s)";
by (induct_tac "I" 1);
by Auto_tac;
qed_spec_mp  "sum_sumj_eq1";

Goal "i<I --> sum I s  = c s i + sumj I i s";
by (induct_tac "I" 1);
by (auto_tac (claset(), simpset() addsimps [linorder_neq_iff, sum_sumj_eq1]));
qed_spec_mp "sum_sumj_eq2";

Goal "(\\<forall>i. i<I --> c s' i = c s i) --> (sum I s' = sum I s)";
by (induct_tac "I" 1 THEN Auto_tac);
qed_spec_mp "sum_ext";

Goal "(\\<forall>j. j<I & j~=i --> c s' j =  c s j) --> (sumj I i s' = sumj I i s)";
by (induct_tac "I" 1);
by Safe_tac;
by (auto_tac (claset() addSIs [sum_ext], simpset()));
qed_spec_mp "sumj_ext";


Goal "(\\<forall>i. i<I --> c s i = 0) -->  sum I s = 0";
by (induct_tac "I" 1);
by Auto_tac;
qed "sum0";


(* Safety properties for Components *)

Goal "(Component i ok G) = \
\     (G \\<in> preserves (%s. c s i) & Component i \\<in> Allowed G)";
by (auto_tac (claset(), 
      simpset() addsimps [ok_iff_Allowed, Component_def RS def_total_prg_Allowed]));
qed "Component_ok_iff";
AddIffs [Component_ok_iff];
AddIffs [OK_iff_ok];
Addsimps [preserves_def];


Goal "Component i \\<in> stable {s. C s = (c s) i + k}";
by (asm_full_simp_tac (simpset() addsimps [Component_def]) 1);
by (constrains_tac 1);
qed "p2";

Goal "[| OK I Component; i\\<in>I |]  \
\     ==> Component i \\<in> stable {s. \\<forall>j\\<in>I. j~=i --> c s j = c k j}";
by (asm_full_simp_tac (simpset() addsimps []) 1); 
by (rewrite_goals_tac [Component_def, mk_total_program_def]);
by (full_simp_tac (simpset() addsimps [stable_def, constrains_def]) 1);
by (Blast_tac 1);
qed "p3";


Goal 
"[| OK {i. i<I} Component; i<I |] ==> \
\ \\<forall>k. Component i \\<in> stable ({s. C s = c s i + sumj I i k} Int \
\                             {s. \\<forall>j\\<in>{i. i<I}. j~=i --> c s j = c k j})";
by (blast_tac (claset() addIs [[p2, p3] MRS stable_Int]) 1);
qed "p2_p3_lemma1";


Goal "(\\<forall>k. F\\<in>stable ({s. C s = (c s) i + sumj I i k} Int \
\                       {s. \\<forall>j\\<in>{i. i<I}. j~=i --> c s j = c k j}))  \
\     ==> (F\\<in>stable {s. C s = c s i + sumj I i s})";
by (full_simp_tac (simpset() addsimps [constrains_def, stable_def]) 1);
by (force_tac (claset() addSIs [sumj_ext], simpset()) 1);
qed "p2_p3_lemma2";


Goal "[| OK {i. i<I} Component; i<I |] \
\     ==> Component i \\<in> stable {s. C s = c s i + sumj I i s}";
by (blast_tac (claset() addIs [p2_p3_lemma1 RS p2_p3_lemma2]) 1);
qed "p2_p3";


(* Compositional correctness *)
Goalw [invariant_def]
     "[| 0<I; OK {i. i<I} Component |]  \
\     ==> (\\<Squnion>i\\<in>{i. i<I}. (Component i)) \\<in> invariant {s. C s = sum I s}";
by (simp_tac (simpset() addsimps [JN_stable, sum_sumj_eq2]) 1);
by (auto_tac (claset() addSIs [sum0 RS mp, p2_p3], 
              simpset()));
qed "safety";




















 





(*  Title:      HOL/UNITY/Counter
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version close to the original. 

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Addsimps [Component_def RS def_prg_Init];
Addsimps (map simp_of_act  [a_def]);

(* Theorems about sum and sumj *)
Goal "ALL n. I<n --> sum I (s(c n := x)) = sum I s";
by (induct_tac "I" 1);
by Auto_tac;
qed_spec_mp "sum_upd_gt";


Goal "sum I (s(c I := x)) = sum I s";
by (induct_tac "I" 1);
by Auto_tac;
by (simp_tac (simpset() 
    addsimps [rewrite_rule [fun_upd_def] sum_upd_gt]) 1);
qed "sum_upd_eq";

Goal "sum I (s(C := x)) = sum I s";
by (induct_tac "I" 1);
by Auto_tac;
qed "sum_upd_C";

Goal "sumj I i (s(c i := x)) = sumj I i s";
by (induct_tac "I" 1);
by Auto_tac;
by (simp_tac (simpset() addsimps 
    [rewrite_rule [fun_upd_def] sum_upd_eq]) 1);
qed "sumj_upd_ci";

Goal "sumj I i (s(C := x)) = sumj I i s";
by (induct_tac "I" 1);
by Auto_tac;
by (simp_tac (simpset() 
    addsimps [rewrite_rule [fun_upd_def] sum_upd_C]) 1);
qed "sumj_upd_C";

Goal "ALL i. I<i--> (sumj I i s = sum I s)";
by (induct_tac "I" 1);
by Auto_tac;
qed_spec_mp  "sumj_sum_gt";

Goal "(sumj I I s = sum I s)";
by (induct_tac "I" 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [sumj_sum_gt]) 1);
qed "sumj_sum_eq";

Goal "ALL i. i<I-->(sum I s = s (c i) +  sumj I i s)";
by (induct_tac "I" 1);
by (auto_tac (claset(), simpset() addsimps [linorder_neq_iff, sumj_sum_eq]));  
qed_spec_mp "sum_sumj";

(* Correctness proofs for Components *)
(* p2 and p3 proofs *)
Goal "Component i : stable {s. s C = s (c i) + k}";
by (asm_full_simp_tac (simpset() addsimps [Component_def]) 1);
by (constrains_tac 1);
qed "p2";

Goal "Component i: stable {s. ALL v. v~=c i & v~=C --> s v = k v}";
by (asm_full_simp_tac (simpset() addsimps [Component_def]) 1);
by (constrains_tac 1);
qed "p3";


Goal 
"(ALL k. Component i: stable ({s. s C = s (c i) + sumj I i k} \
\                  Int {s. ALL v. v~=c i & v~=C --> s v = k v})) \
\  = (Component i: stable {s. s C = s (c i) + sumj I i s})";
by (auto_tac (claset(), simpset() 
     addsimps [constrains_def, stable_def,Component_def,
               sumj_upd_C, sumj_upd_ci]));
qed "p2_p3_lemma1";

Goal 
"ALL k. Component i: stable ({s. s C = s (c i) + sumj I i k} Int \
\                             {s. ALL v. v~=c i & v~=C --> s v = k v})";
by (blast_tac (claset() addIs [[p2, p3] MRS stable_Int]) 1);
qed "p2_p3_lemma2";


Goal 
"Component i: stable {s.  s C = s (c i) + sumj I i s}";
by (auto_tac (claset() addSIs [p2_p3_lemma2],
              simpset() addsimps [p2_p3_lemma1 RS sym]));
qed "p2_p3";

(* Compositional Proof *)

Goal "(ALL i. i < I --> s (c i) = 0) --> sum I s = 0";
by (induct_tac "I" 1);
by Auto_tac;
qed "sum_0'";
val sum0_lemma =  (sum_0' RS mp) RS sym;

(* I could'nt be empty *)
Goalw [invariant_def] 
"!!I. 0<I ==> (JN i:{i. i<I}. Component i):invariant {s. s C = sum I s}";
by (simp_tac (simpset() addsimps [JN_stable,Init_JN,sum_sumj]) 1);
by (force_tac (claset() addIs [p2_p3, sum0_lemma RS sym], simpset()) 1);
qed "safety";





















 





(*  Title:      HOLCF/IOA/meta_theory/RefMappings.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Refinement Mappings in HOLCF/IOA.
*)


(* ---------------------------------------------------------------------------- *)

section "transitions and moves";


Goal "s -a--A-> t ==> ? ex. move A ex s a t";

by (res_inst_tac [("x","(a,t)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"transition_is_ex";
 

Goal "(~a:ext A) & s=t ==> ? ex. move A ex s a t";

by (res_inst_tac [("x","nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"nothing_is_ex";


Goal "(s -a--A-> s') & (s' -a'--A-> s'') & (~a':ext A) \
\        ==> ? ex. move A ex s a s''";

by (res_inst_tac [("x","(a,s')>>(a',s'')>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"ei_transitions_are_ex";


Goal "(s1 -a1--A-> s2) & (s2 -a2--A-> s3) & (s3 -a3--A-> s4) &\
\     (~a2:ext A) & (~a3:ext A) ==> \
\     ? ex. move A ex s1 a1 s4";
  
by (res_inst_tac [("x","(a1,s2)>>(a2,s3)>>(a3,s4)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"eii_transitions_are_ex";


(* ---------------------------------------------------------------------------- *)

section "weak_ref_map and ref_map";


Goalw [is_weak_ref_map_def,is_ref_map_def]
  "[| ext C = ext A; \
\    is_weak_ref_map f C A |] ==> is_ref_map f C A";
by (safe_tac set_cs);
by (case_tac "a:ext A" 1);
by (rtac transition_is_ex 1);
by (Asm_simp_tac 1);
by (rtac nothing_is_ex 1);
by (Asm_simp_tac 1);
qed"weak_ref_map2ref_map";


val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by (fast_tac (claset() addDs prems) 1);
val lemma = result();

Delsplits [split_if]; Delcongs [if_weak_cong];

Goal "[| is_weak_ref_map f C A |] \
\     ==> (is_weak_ref_map f (rename C g) (rename A g))";
by (asm_full_simp_tac (simpset() addsimps [is_weak_ref_map_def]) 1);
by (rtac conjI 1);
(* 1: start states *)
by (asm_full_simp_tac (simpset() addsimps [rename_def,rename_set_def,starts_of_def]) 1);
(* 2: reachable transitions *)
by (REPEAT (rtac allI 1));
by (rtac lemma 1);
by (simp_tac (simpset() addsimps [rename_def,rename_set_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [externals_def,asig_inputs_def,
asig_outputs_def,asig_of_def,trans_of_def]) 1);
by Safe_tac;
by (stac split_if 1);
 by (rtac conjI 1);
 by (rtac impI 1);
 by (etac disjE 1);
 by (etac exE 1);
by (etac conjE 1);
(* x is input *)
 by (dtac sym 1);
 by (dtac sym 1);
by (Asm_full_simp_tac 1);
by (REPEAT (hyp_subst_tac 1));
by (ftac reachable_rename 1);
by (Asm_full_simp_tac 1);
(* x is output *)
 by (etac exE 1);
by (etac conjE 1);
 by (dtac sym 1);
 by (dtac sym 1);
by (Asm_full_simp_tac 1);
by (REPEAT (hyp_subst_tac 1));
by (ftac reachable_rename 1);
by (Asm_full_simp_tac 1);
(* x is internal *)
by (ftac reachable_rename 1);
by Auto_tac;
qed"rename_through_pmap";
Addsplits [split_if]; Addcongs [if_weak_cong];



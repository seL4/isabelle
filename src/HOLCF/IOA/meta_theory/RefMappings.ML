(*  Title:      HOLCF/IOA/meta_theory/RefMappings.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Refinement Mappings in HOLCF/IOA
*)



(* ---------------------------------------------------------------------------- *)
                           section "laststate";
(* ---------------------------------------------------------------------------- *)

goal thy "laststate (s,UU) = s";
by (simp_tac (simpset() addsimps [laststate_def]) 1); 
qed"laststate_UU";

goal thy "laststate (s,nil) = s";
by (simp_tac (simpset() addsimps [laststate_def]) 1);
qed"laststate_nil";

goal thy "!! ex. Finite ex ==> laststate (s,at>>ex) = laststate (snd at,ex)";
by (simp_tac (simpset() addsimps [laststate_def]) 1);
by (case_tac "ex=nil" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (dtac (Finite_Last1 RS mp) 1);
by (assume_tac 1);
by (def_tac 1);
qed"laststate_cons";

Addsimps [laststate_UU,laststate_nil,laststate_cons];

goal thy "!!ex. Finite ex ==> (! s. ? u. laststate (s,ex)=u)";
by (Seq_Finite_induct_tac 1);
qed"exists_laststate";


(* ---------------------------------------------------------------------------- *)

section "transitions and moves";


goal thy"!!f. s -a--A-> t ==> ? ex. move A ex s a t";

by (res_inst_tac [("x","(a,t)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"transition_is_ex";
 

goal thy"!!f. (~a:ext A) & s=t ==> ? ex. move A ex s a t";

by (res_inst_tac [("x","nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"nothing_is_ex";


goal thy"!!f. (s -a--A-> s') & (s' -a'--A-> s'') & (~a':ext A) \
\        ==> ? ex. move A ex s a s''";

by (res_inst_tac [("x","(a,s')>>(a',s'')>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"ei_transitions_are_ex";


goal thy
"!!f. (s1 -a1--A-> s2) & (s2 -a2--A-> s3) & (s3 -a3--A-> s4) &\
\     (~a2:ext A) & (~a3:ext A) ==> \
\     ? ex. move A ex s1 a1 s4";
  
by (res_inst_tac [("x","(a1,s2)>>(a2,s3)>>(a3,s4)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"eii_transitions_are_ex";


(* ---------------------------------------------------------------------------- *)

section "weak_ref_map and ref_map";


goalw thy [is_weak_ref_map_def,is_ref_map_def]
  "!!f. [| ext C = ext A; \
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


goal thy "!!f.[| is_weak_ref_map f C A |]\
\                      ==> (is_weak_ref_map f (rename C g) (rename A g))";
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
by (stac expand_if 1);
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
by (forward_tac  [reachable_rename] 1);
by (Asm_full_simp_tac 1);
(* x is output *)
 by (etac exE 1);
by (etac conjE 1);
 by (dtac sym 1);
 by (dtac sym 1);
by (Asm_full_simp_tac 1);
by (REPEAT (hyp_subst_tac 1));
by (forward_tac  [reachable_rename] 1);
by (Asm_full_simp_tac 1);
(* x is internal *)
by (simp_tac (simpset() addcongs [conj_cong]) 1);
by (rtac impI 1);
by (etac conjE 1);
by (forward_tac  [reachable_rename] 1);
by (Auto_tac());
qed"rename_through_pmap";



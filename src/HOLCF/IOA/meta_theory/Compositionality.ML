(*  Title:      HOLCF/IOA/meta_theory/Compositionality.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Compositionality of I/O automata
*) 



goal thy "!! A. [|eA --> A ; eB & ~eA --> ~A|] ==> (eA | eB) --> A=eA";
by (Auto_tac());
qed"compatibility_consequence3";


goal thy 
"!! A B. [| compatible A B; Forall (%a. a: ext A | a: ext B) tr |] ==> \
\           Filter (%a. a: act A)`tr= Filter (%a. a: ext A)`tr";
by (rtac ForallPFilterQR 1);
(* i.e.: [| (! x. P x --> (Q x = R x)) ; Forall P tr |] ==> Filter Q`tr = Filter R`tr *)
by (assume_tac 2);
by (rtac compatibility_consequence3 1);
by (REPEAT (asm_full_simp_tac (simpset() 
                  addsimps [ext_is_act,ext1_ext2_is_not_act1]) 1));
qed"Filter_actAisFilter_extA";


(* the next two theorems are only necessary, as there is no theorem ext (A||B) = ext (B||A)
    or even better A||B= B||A, FIX *)

goal thy "!! A. [|eA --> A ; eB & ~eA --> ~A|] ==> (eB | eA) --> A=eA";
by (Auto_tac());
qed"compatibility_consequence4";

goal thy 
"!! A B. [| compatible A B; Forall (%a. a: ext B | a: ext A) tr |] ==> \
\           Filter (%a. a: act A)`tr= Filter (%a. a: ext A)`tr";
by (rtac ForallPFilterQR 1);
by (assume_tac 2);
by (rtac compatibility_consequence4 1);
by (REPEAT (asm_full_simp_tac (simpset() 
                  addsimps [ext_is_act,ext1_ext2_is_not_act1]) 1));
qed"Filter_actAisFilter_extA2";


(* -------------------------------------------------------------------------- *)
                     section " Main Compositionality Theorem ";
(* -------------------------------------------------------------------------- *)



goal thy "!! A1 A2 B1 B2. \
\         [| is_trans_of A1; is_trans_of A2; is_trans_of B1; is_trans_of B2;\
\            is_asig_of A1; is_asig_of A2; \
\            is_asig_of B1; is_asig_of B2; \
\            compatible A1 B1; compatible A2 B2; \
\            A1 =<| A2; \
\            B1 =<| B2 |] \
\        ==> (A1 || B1) =<| (A2 || B2)";

by (asm_full_simp_tac (simpset() addsimps [is_asig_of_def]) 1);
by (forw_inst_tac [("A2","A1")] (compat_commute RS iffD1) 1);
by (forw_inst_tac [("A2","A2")] (compat_commute RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps [ioa_implements_def,
          inputs_of_par,outputs_of_par,externals_of_par]) 1);
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [compositionality_tr]) 1);
by (subgoal_tac "ext A1 = ext A2 & ext B1 = ext B2" 1);
by (asm_full_simp_tac (simpset() addsimps [externals_def]) 2);
by (REPEAT (etac conjE 1));
(* rewrite with proven subgoal *)
by (asm_full_simp_tac (simpset() addsimps [externals_of_par]) 1);
by (safe_tac set_cs);

(* 2 goals, the 3rd has been solved automatically *)
(* 1: Filter A2 x : traces A2 *)
by (dres_inst_tac [("A","traces A1")] subsetD 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Filter_actAisFilter_extA]) 1);
(* 2: Filter B2 x : traces B2 *)
by (dres_inst_tac [("A","traces B1")] subsetD 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Filter_actAisFilter_extA2]) 1);
qed"compositionality";





(*  Title:      HOL/IOA/Asig.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Action signatures
*)

open Asig;

val asig_projections = [asig_inputs_def, asig_outputs_def, asig_internals_def];

goal Asig.thy "!!a.[| a~:internals(S) ;a~:externals(S)|] ==> a~:actions(S)";
by (asm_full_simp_tac (simpset() addsimps [externals_def,actions_def]) 1);
qed"int_and_ext_is_act";

goal Asig.thy "!!a.[|a:externals(S)|] ==> a:actions(S)";
by (asm_full_simp_tac (simpset() addsimps [externals_def,actions_def]) 1);
qed"ext_is_act";

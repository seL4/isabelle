(*  Title:      HOL/IOA/meta_theory/Asig.ML
    ID:         $Id$
    Author:     Olaf Mueller, Tobias Nipkow & Konrad Slind
    Copyright   1994,1996  TU Muenchen

Action signatures
*)

open Asig;

val asig_projections = [asig_inputs_def, asig_outputs_def, asig_internals_def];

goal thy
 "(outputs    (a,b,c) = b)   & \
\ (inputs     (a,b,c) = a) & \
\ (internals  (a,b,c) = c)";
  by (simp_tac (simpset() addsimps asig_projections) 1);
qed "asig_triple_proj";

goal thy "!!a.[| a~:internals(S) ;a~:externals(S)|] ==> a~:actions(S)";
by (asm_full_simp_tac (simpset() addsimps [externals_def,actions_def]) 1);
qed"int_and_ext_is_act";

goal thy "!!a.[|a:externals(S)|] ==> a:actions(S)";
by (asm_full_simp_tac (simpset() addsimps [externals_def,actions_def]) 1);
qed"ext_is_act";

goal thy "!!a.[|a:internals S|] ==> a:actions S";
by (asm_full_simp_tac (simpset() addsimps [asig_internals_def,actions_def]) 1);
qed"int_is_act";

goal thy "!!a.[|a:inputs S|] ==> a:actions S";
by (asm_full_simp_tac (simpset() addsimps [asig_inputs_def,actions_def]) 1);
qed"inp_is_act";

goal thy "!!a.[|a:outputs S|] ==> a:actions S";
by (asm_full_simp_tac (simpset() addsimps [asig_outputs_def,actions_def]) 1);
qed"out_is_act";

goal thy "(x: actions S & x : externals S) = (x: externals S)";
by (fast_tac (claset() addSIs [ext_is_act]) 1 );
qed"ext_and_act";
 
goal thy "!!S. [|is_asig S;x: actions S|] ==> (x~:externals S) = (x: internals S)";
by (asm_full_simp_tac (simpset() addsimps [actions_def,is_asig_def,externals_def]) 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"not_ext_is_int";

goal thy "!!S. is_asig S ==> (x~:externals S) = (x: internals S | x~:actions S)";
by (asm_full_simp_tac (simpset() addsimps [actions_def,is_asig_def,externals_def]) 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"not_ext_is_int_or_not_act";

goalw thy  [externals_def,actions_def,is_asig_def]
 "!! x. [| is_asig (S); x:internals S |] ==> x~:externals S";
by (Asm_full_simp_tac 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"int_is_not_ext";


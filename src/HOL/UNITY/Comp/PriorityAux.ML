(*  Title:      HOL/UNITY/PriorityAux
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Auxiliary definitions needed in Priority.thy
*)

Addsimps [derive_def, derive1_def, symcl_def, A_def, R_def,  
          above_def, reach_def, reverse_def, neighbors_def];

(*All vertex sets are finite \\<dots>*)
AddIffs [[subset_UNIV, finite_vertex_univ] MRS finite_subset];

(* and relatons over vertex are finite too *)
AddIffs [[subset_UNIV, [finite_vertex_univ, finite_vertex_univ] 
           MRS finite_Prod_UNIV] MRS finite_subset];


(* The equalities (above i r = {}) = (A i r = {}) 
   and (reach i r = {}) = (R i r) rely on the following theorem  *)

Goal "((r^+)``{i} = {}) = (r``{i} = {})";
by Auto_tac;
by (etac trancl_induct 1);
by Auto_tac;
qed "image0_trancl_iff_image0_r";

(* Another form usefull in some situation *)
Goal "(r``{i}={}) = (ALL x. ((i,x):r^+) = False)";
by Auto_tac;
by (dtac (image0_trancl_iff_image0_r RS ssubst) 1);
by Auto_tac;
qed "image0_r_iff_image0_trancl";


(* In finite universe acyclic coincides with wf *)
Goal 
"!!r::(vertex*vertex)set. acyclic r = wf r";
by (auto_tac (claset(), simpset() addsimps [wf_iff_acyclic_if_finite]));
qed "acyclic_eq_wf";

(* derive and derive1 are equivalent *)
Goal "derive i r q = derive1 i r q";
by Auto_tac;
qed "derive_derive1_eq";

(* Lemma 1 *)
Goalw [reach_def]
"[| x:reach i q; derive1 k r q |] ==> x~=k --> x:reach i r";
by (etac ImageE 1);
by (etac trancl_induct 1);
by (case_tac "i=k" 1);
by (auto_tac (claset() addIs [r_into_trancl], simpset()));
by (dres_inst_tac [("x", "y")] spec 1);
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "z")] spec 1);
by (auto_tac (claset() addDs [r_into_trancl] addIs [trancl_trans], simpset()));
qed "lemma1_a";

Goal "ALL k r q. derive k r q -->(reach i q <= (reach i r Un {k}))";
by (REPEAT(rtac allI 1));
by (rtac impI 1);
by (rtac subsetI 1 THEN dtac lemma1_a 1);
by (auto_tac (claset(), simpset() addsimps [derive_derive1_eq]
                    delsimps [reach_def, derive_def, derive1_def]));
qed "reach_lemma";

(* An other possible formulation of the above theorem based on
   the equivalence x:reach y r = y:above x r                  *)
Goal 
"(ALL i. reach i q <= (reach i r Un {k})) =\
\ (ALL x. x~=k --> (ALL i. i~:above x r --> i~:above x q))";
by (auto_tac (claset(), simpset() addsimps [trancl_converse]));
qed "reach_above_lemma";

(* Lemma 2 *)
Goal 
"(z, i):r^+ ==> (ALL y. (y, z):r --> (y, i)~:r^+) = ((r^-1)``{z}={})";
by Auto_tac;
by (forw_inst_tac [("r", "r")] trancl_into_trancl2 1);
by Auto_tac;
qed "maximal_converse_image0";

Goal
 "acyclic r ==> A i r~={}-->(EX j:above i r. A j r = {})";
by (full_simp_tac (simpset() 
            addsimps [acyclic_eq_wf, wf_eq_minimal]) 1);
by (dres_inst_tac [("x", "((r^-1)^+)``{i}")] spec 1);
by Auto_tac;
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() 
        addsimps [maximal_converse_image0, trancl_converse]) 1);
qed "above_lemma_a";


Goal
 "acyclic r ==> above i r~={}-->(EX j:above i r. above j r = {})";
by (dtac above_lemma_a 1);
by (auto_tac (claset(), simpset() 
        addsimps [image0_trancl_iff_image0_r]));
qed "above_lemma_b";















(*  Title:      Cube.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Addsimps [commutation, residuals_preserve_comp, sub_preserve_reg,
	  residuals_preserve_reg, sub_comp, sub_comp RS comp_sym];

(* ------------------------------------------------------------------------- *)
(*         Prism theorem                                                     *)
(*         =============                                                     *)
(* ------------------------------------------------------------------------- *)

(* Having more assumptions than needed -- removed below  *)
Goal "v<==u ==> \
\   regular(u) --> (\\<forall>w. w~v --> w~u -->  \
\                          w |> u = (w|>v) |> (u|>v))";
by (etac Ssub.induct 1);
by Auto_tac;
qed_spec_mp "prism_l";

Goal "[|v <== u; regular(u); w~v|]==> \
\       w |> u = (w|>v) |> (u|>v)";
by (rtac prism_l 1);
by (rtac comp_trans 4);
by Auto_tac;
qed "prism";


(* ------------------------------------------------------------------------- *)
(*    Levy's Cube Lemma                                                      *)
(* ------------------------------------------------------------------------- *)

Goal "[|u~v; regular(v); regular(u); w~u|]==>  \
\          (w|>u) |> (v|>u) = (w|>v) |> (u|>v)";
by (stac preservation 1 
    THEN assume_tac 1 THEN assume_tac 1);
by (stac preservation 1 
    THEN etac comp_sym 1 THEN assume_tac 1);
by (stac (prism RS sym) 1);
by (asm_full_simp_tac (simpset() addsimps 
		       [prism RS sym,union_l,union_preserve_regular,
			comp_sym_iff, union_sym]) 4);
by (asm_simp_tac (simpset() addsimps [union_r, comp_sym_iff]) 1);
by (asm_simp_tac (simpset() addsimps 
		  [union_preserve_regular, comp_sym_iff]) 1);
by (etac comp_trans 1);
by (atac 1);
qed "cube";


(* ------------------------------------------------------------------------- *)
(*           paving theorem                                                  *)
(* ------------------------------------------------------------------------- *)

Goal "[|w~u; w~v; regular(u); regular(v)|]==> \
\          \\<exists>uv vu. (w|>u) |> vu = (w|>v) |> uv & (w|>u)~vu &\
\            regular(vu) & (w|>v)~uv & regular(uv) ";
by (subgoal_tac "u~v" 1);
by (safe_tac (claset() addSIs [exI]));
by (rtac cube 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [comp_sym_iff])));
by (ALLGOALS (blast_tac (claset() addIs [residuals_preserve_comp, 
					comp_trans, comp_sym])));
qed "paving";


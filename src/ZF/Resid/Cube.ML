(*  Title:      Cube.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Cube;

val prism_ss = (res1L_ss addsimps 
                [commutation,residuals_preserve_comp,sub_preserve_reg,
                 residuals_preserve_reg,sub_comp,sub_comp RS comp_sym]);

(* ------------------------------------------------------------------------- *)
(*         Prism theorem                                                     *)
(*         =============                                                     *)
(* ------------------------------------------------------------------------- *)

(* Having more ssumptions than needed -- removed below  *)
goal Cube.thy 
    "!!u.v<==u ==> \
\   regular(u)-->(ALL w.w~v-->w~u-->  \
\             w |> u = (w|>v) |> (u|>v))";
by (etac Ssub.induct 1);
by (asm_simp_tac (prism_ss) 1);
by (asm_simp_tac (prism_ss ) 1);
by (asm_simp_tac (prism_ss ) 1);
by (dresolve_tac [spec RS mp RS mp] 1 THEN resolve_tac [Scomp.Comp_Fun] 1 
    THEN resolve_tac [Scomp.Comp_Fun] 2 THEN (REPEAT(assume_tac 1)));
by (asm_full_simp_tac (prism_ss ) 1);
by (asm_simp_tac (prism_ss ) 1);
by (dresolve_tac [spec RS mp RS mp] 1 THEN resolve_tac [Scomp.Comp_Fun] 1 
    THEN resolve_tac [Scomp.Comp_Fun] 2 THEN (REPEAT(assume_tac 1)));
by (asm_full_simp_tac (prism_ss ) 1);
val prism_l = result();

goal Cube.thy 
    "!!u.[|v <== u; regular(u); w~v|]==> \
\       w |> u = (w|>v) |> (u|>v)";
by (resolve_tac [prism_l RS mp RS spec RS mp RS mp ] 1);
by (rtac comp_trans 4);
by (assume_tac 4);
by (ALLGOALS(asm_simp_tac (prism_ss)));
val prism = result();


(* ------------------------------------------------------------------------- *)
(*    Levy's Cube Lemma                                                      *)
(* ------------------------------------------------------------------------- *)

goal Cube.thy 
    "!!u.[|u~v; regular(v); regular(u); w~u|]==>  \
\          (w|>u) |> (v|>u) = (w|>v) |> (u|>v)";
by (res_inst_tac [("u2","u"),("v2","v")](preservation RS ssubst) 1 
    THEN assume_tac 1 THEN assume_tac 1);
by (res_inst_tac [("u2","v"),("v2","u")](preservation RS ssubst) 1);
by (etac comp_sym 1);
by (atac 1);
by(rtac (prism RS sym RS ssubst) 1);
by (asm_full_simp_tac (res1_ss addsimps 
    [prism RS sym,union_l,union_preserve_regular,
     comp_sym_iff, union_sym]) 4);
by (asm_full_simp_tac (res1_ss addsimps [union_r, comp_sym_iff]) 1);
by (asm_full_simp_tac (res1_ss addsimps 
    [union_preserve_regular, comp_sym_iff]) 1);
by (etac comp_trans 1);
by (atac 1);
val cube = result();


(* ------------------------------------------------------------------------- *)
(*           paving theorem                                                  *)
(* ------------------------------------------------------------------------- *)

goal Cube.thy 
    "!!u.[|w~u; w~v; regular(u); regular(v)|]==> \
\          EX uv.EX vu. (w|>u) |> vu = (w|>v) |> uv & (w|>u)~vu &\
\            regular(vu) & (w|>v)~uv & regular(uv) ";
by (forw_inst_tac [("x1","v")] (comp_sym RS comp_trans) 1);
by (REPEAT(step_tac ZF_cs 1));
by (rtac cube 1);
by (asm_simp_tac (prism_ss addsimps [comp_sym_iff]) 1);
by (asm_simp_tac (prism_ss addsimps [comp_sym_iff]) 1);
by (asm_simp_tac (prism_ss addsimps [comp_sym_iff]) 1);
by (atac 1);
by (etac (residuals_preserve_comp RS spec RS mp RS mp RS mp) 1);
 by(atac 1);
 by(etac comp_sym 1);
 by(atac 1);
by (asm_simp_tac (prism_ss addsimps [comp_sym_iff]) 1);
by (asm_simp_tac prism_ss 1);
by (asm_simp_tac (prism_ss addsimps [comp_sym_iff]) 1);
val paving = result();


(*  Title:      HOLCF/Dnat.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993, 1995 Technische Universitaet Muenchen

*)

open Dnat;

(* ------------------------------------------------------------------------- *)
(* expand fixed point properties                                             *)
(* ------------------------------------------------------------------------- *)

bind_thm ("iterator_def2", fix_prover2 Dnat.thy iterator_def 
	"iterator = (LAM n f x. case n of dzero => x | \
\                                     dsucc`m => f`(iterator`m`f`x))");

(* ------------------------------------------------------------------------- *)
(* recursive  properties                                                     *)
(* ------------------------------------------------------------------------- *)

Goal "iterator`UU`f`x = UU";
by (stac iterator_def2 1);
by (simp_tac (HOLCF_ss addsimps dnat.rews) 1);
qed "iterator1";

Goal "iterator`dzero`f`x = x";
by (stac iterator_def2 1);
by (simp_tac (HOLCF_ss addsimps dnat.rews) 1);
qed "iterator2";

Goal "n~=UU ==> iterator`(dsucc`n)`f`x = f`(iterator`n`f`x)";
by (rtac trans 1);
by (stac iterator_def2 1);
by (asm_simp_tac (HOLCF_ss addsimps dnat.rews) 1);
by (rtac refl 1);
qed "iterator3";

val iterator_rews = 
	[iterator1, iterator2, iterator3];

Goal "ALL x y::dnat. x<<y --> x=UU | x=y";
by (rtac allI 1);
by (res_inst_tac [("x","x")] dnat.ind 1);
by (fast_tac HOL_cs 1);
by (rtac allI 1);
by (res_inst_tac [("x","y")] dnat.casedist 1);
by (fast_tac (HOL_cs addSIs [UU_I]) 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps dnat.dist_les) 1);
by (rtac allI 1);
by (res_inst_tac [("x","y")] dnat.casedist 1);
by (fast_tac (HOL_cs addSIs [UU_I]) 1);
by (asm_simp_tac (simpset() addsimps dnat.dist_les) 1);
by (asm_simp_tac (simpset() addsimps dnat.rews) 1);
by (strip_tac 1);
by (subgoal_tac "d<<da" 1);
by (etac allE 1);
by (dtac mp 1);
by (atac 1);
by (etac disjE 1);
by (contr_tac 1);
by (Asm_simp_tac 1);
by (resolve_tac  dnat.inverts 1);
by (REPEAT (atac 1));
qed "dnat_flat";


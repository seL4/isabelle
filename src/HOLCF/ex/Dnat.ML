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

qed_goal "iterator1" Dnat.thy "iterator`UU`f`x = UU"
 (fn prems =>
	[
	(rtac (iterator_def2 RS ssubst) 1),
	(simp_tac (HOLCF_ss addsimps dnat.rews) 1)
	]);

qed_goal "iterator2" Dnat.thy "iterator`dzero`f`x = x"
 (fn prems =>
	[
	(rtac (iterator_def2 RS ssubst) 1),
	(simp_tac (HOLCF_ss addsimps dnat.rews) 1)
	]);

qed_goal "iterator3" Dnat.thy 
"n~=UU ==> iterator`(dsucc`n)`f`x = f`(iterator`n`f`x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(rtac (iterator_def2 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps dnat.rews) 1),
	(rtac refl 1)
	]);

val iterator_rews = 
	[iterator1, iterator2, iterator3];

val dnat_flat = prove_goal Dnat.thy "!x y::dnat.x<<y --> x=UU | x=y" 
(fn _ => [
	(rtac allI 1),
	(res_inst_tac [("x","x")] dnat.ind 1),
	(fast_tac HOL_cs 1),
	(rtac allI 1),
	(res_inst_tac [("x","y")] dnat.cases 1),
	(fast_tac (HOL_cs addSIs [UU_I]) 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat.dists_le) 1),
	(rtac allI 1),
	(res_inst_tac [("x","y")] dnat.cases 1),
	(fast_tac (HOL_cs addSIs [UU_I]) 1),
	(asm_simp_tac (!simpset addsimps dnat.dists_le) 1),
	(asm_simp_tac (!simpset addsimps dnat.rews) 1),
	(strip_tac 1),
	(subgoal_tac "d<<da" 1),
	(etac allE 1),
	(dtac mp 1),
	(atac 1),
	(etac disjE 1),
	(contr_tac 1),
	(Asm_simp_tac 1),
	(resolve_tac  dnat.inverts 1),
	(REPEAT (atac 1))]);


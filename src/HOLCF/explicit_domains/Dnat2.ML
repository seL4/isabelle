(*  Title: 	HOLCF/Dnat2.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for theory Dnat2.thy
*)

open Dnat2;


(* ------------------------------------------------------------------------- *)
(* expand fixed point properties                                             *)
(* ------------------------------------------------------------------------- *)

val iterator_def2 = fix_prover2 Dnat2.thy iterator_def 
	"iterator = (LAM n f x. dnat_when`x`(LAM m.f`(iterator`m`f`x)) `n)";

(* ------------------------------------------------------------------------- *)
(* recursive  properties                                                     *)
(* ------------------------------------------------------------------------- *)

qed_goal "iterator1" Dnat2.thy "iterator`UU`f`x = UU"
 (fn prems =>
	[
	(rtac (iterator_def2 RS ssubst) 1),
	(simp_tac (!simpset addsimps dnat_when) 1)
	]);

qed_goal "iterator2" Dnat2.thy "iterator`dzero`f`x = x"
 (fn prems =>
	[
	(rtac (iterator_def2 RS ssubst) 1),
	(simp_tac (!simpset addsimps dnat_when) 1)
	]);

qed_goal "iterator3" Dnat2.thy 
"n~=UU ==> iterator`(dsucc`n)`f`x = f`(iterator`n`f`x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(rtac (iterator_def2 RS ssubst) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(rtac refl 1)
	]);

val dnat2_rews = 
	[iterator1, iterator2, iterator3];




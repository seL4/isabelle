(*  Title:      HOLCF/One.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

Lemmas for One.thy
*)

open One;

(* ------------------------------------------------------------------------ *)
(* Exhaustion and Elimination for type one                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_one" thy [ONE_def] "t=UU | t = ONE"
 (fn prems =>
        [
	(lift.induct_tac "t" 1),
	(fast_tac HOL_cs 1),
	(Simp_tac 1),
	(rtac unit_eq 1)
	]);

qed_goal "oneE" thy
        "[| p=UU ==> Q; p = ONE ==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac (Exh_one RS disjE) 1),
        (eresolve_tac prems 1),
        (eresolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *) 
(* tactic for one-thms                                                      *)
(* ------------------------------------------------------------------------ *)

fun prover t = prove_goalw thy [ONE_def] t
 (fn prems =>
        [
	(asm_simp_tac (simpset() addsimps [inst_lift_po]) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* distinctness for type one : stored in a list                             *)
(* ------------------------------------------------------------------------ *)

val dist_less_one = map prover ["~ONE << UU"];

val dist_eq_one = map prover ["ONE~=UU","UU~=ONE"];

Addsimps (dist_less_one@dist_eq_one);

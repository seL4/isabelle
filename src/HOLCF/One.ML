(*  Title:      HOLCF/One.ML
    ID:         $Id$
    Author:     Oscar Slotosch

The unit domain.
*)

(* ------------------------------------------------------------------------ *)
(* Exhaustion and Elimination for type one                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [ONE_def] "t=UU | t = ONE";
by (induct_tac "t" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "Exh_one";

val prems = Goal "[| p=UU ==> Q; p = ONE ==>Q|] ==>Q";
by (rtac (Exh_one RS disjE) 1);
by (eresolve_tac prems 1);
by (eresolve_tac prems 1);
qed "oneE";

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

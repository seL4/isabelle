(*  Title:      HOLCF/One.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for one.thy 
*)

open One;

(* ------------------------------------------------------------------------ *)
(* Exhaustion and Elimination for type one                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_one" One.thy [one_def] "z=UU | z = one"
 (fn prems =>
        [
        (res_inst_tac [("p","rep_one`z")] upE1 1),
        (rtac disjI1 1),
        (rtac ((abs_one_iso RS allI) RS ((rep_one_iso RS allI) RS iso_strict )
                RS conjunct2 RS subst) 1),
        (rtac (abs_one_iso RS subst) 1),
        (etac cfun_arg_cong 1),
        (rtac disjI2 1),
        (rtac (abs_one_iso RS subst) 1),
        (rtac cfun_arg_cong 1),
        (rtac (unique_void2 RS subst) 1),
        (atac 1)
        ]);

qed_goal "oneE" One.thy
        "[| p=UU ==> Q; p = one ==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac (Exh_one RS disjE) 1),
        (eresolve_tac prems 1),
        (eresolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* distinctness for type one : stored in a list                             *)
(* ------------------------------------------------------------------------ *)

val dist_less_one = [
prove_goalw One.thy [one_def] "~one << UU"
 (fn prems =>
        [
        (rtac classical2 1),
        (rtac less_up4b 1),
        (rtac (rep_one_iso RS subst) 1),
        (rtac (rep_one_iso RS subst) 1),
        (rtac monofun_cfun_arg 1),
        (etac ((abs_one_iso RS allI) RS ((rep_one_iso RS allI) RS iso_strict ) 
                RS conjunct2 RS ssubst) 1)
        ])
];

val  dist_eq_one = [prove_goal One.thy "one~=UU"
 (fn prems =>
        [
        (rtac not_less2not_eq 1),
        (resolve_tac dist_less_one 1)
        ])];

val dist_eq_one = dist_eq_one @ (map (fn thm => (thm RS not_sym)) dist_eq_one);

(* ------------------------------------------------------------------------ *)
(* one is flat                                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "flat_one" One.thy [flat_def] "flat one"
 (fn prems =>
        [
        (rtac allI 1),
        (rtac allI 1),
        (res_inst_tac [("p","x")] oneE 1),
        (Asm_simp_tac 1),
        (res_inst_tac [("p","y")] oneE 1),
        (asm_simp_tac (!simpset addsimps dist_less_one) 1),
        (Asm_simp_tac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* properties of one_when                                                   *)
(* here I tried a generic prove procedure                                   *)
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw One.thy [one_when_def,one_def] s
 (fn prems =>
        [
        (simp_tac (!simpset addsimps [(rep_one_iso ),
        (abs_one_iso RS allI) RS ((rep_one_iso RS allI) 
        RS iso_strict) RS conjunct1] )1)
        ]);

val one_when = map prover ["one_when`x`UU = UU","one_when`x`one = x"];


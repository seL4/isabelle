(*  Title: 	HOLCF/tr1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for tr1.thy
*)

open Tr1;

(* -------------------------------------------------------------------------- *) 
(* distinctness for type tr                                                   *) 
(* -------------------------------------------------------------------------- *)

val dist_less_tr = [
prove_goalw Tr1.thy [TT_def] "~TT << UU"
 (fn prems =>
	[
	(rtac classical3 1),
	(rtac defined_sinl 1),
	(rtac not_less2not_eq 1),
	(resolve_tac dist_less_one 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac cfun_arg_cong 1),
	(rtac ((abs_tr_iso RS allI) RS ((rep_tr_iso RS allI) RS iso_strict ) 		RS conjunct2 RS ssubst) 1),
	(etac (eq_UU_iff RS ssubst) 1)
	]),
prove_goalw Tr1.thy [FF_def] "~FF << UU"
 (fn prems =>
	[
	(rtac classical3 1),
	(rtac defined_sinr 1),
	(rtac not_less2not_eq 1),
	(resolve_tac dist_less_one 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac cfun_arg_cong 1),
	(rtac ((abs_tr_iso RS allI) RS ((rep_tr_iso RS allI) RS iso_strict ) 		RS conjunct2 RS ssubst) 1),
	(etac (eq_UU_iff RS ssubst) 1)
	]),
prove_goalw Tr1.thy [FF_def,TT_def] "~TT << FF"
 (fn prems =>
	[
	(rtac classical3 1),
	(rtac (less_ssum4c RS iffD1) 2),
	(rtac not_less2not_eq 1),
	(resolve_tac dist_less_one 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac (rep_tr_iso RS subst) 1),
	(etac monofun_cfun_arg 1)
	]),
prove_goalw Tr1.thy [FF_def,TT_def] "~FF << TT"
 (fn prems =>
	[
	(rtac classical3 1),
	(rtac (less_ssum4d RS iffD1) 2),
	(rtac not_less2not_eq 1),
	(resolve_tac dist_less_one 1),
	(rtac (rep_tr_iso RS subst) 1),
	(rtac (rep_tr_iso RS subst) 1),
	(etac monofun_cfun_arg 1)
	])
];

fun prover s =  prove_goal Tr1.thy s
 (fn prems =>
	[
	(rtac not_less2not_eq 1),
	(resolve_tac dist_less_tr 1)
	]);

val dist_eq_tr = map prover ["~TT=UU","~FF=UU","~TT=FF"];
val dist_eq_tr = dist_eq_tr @ (map (fn thm => (thm RS not_sym)) dist_eq_tr);

(* ------------------------------------------------------------------------ *) 
(* Exhaustion and elimination for type tr                                   *) 
(* ------------------------------------------------------------------------ *)

val Exh_tr = prove_goalw Tr1.thy [FF_def,TT_def] "t=UU | t = TT | t = FF"
 (fn prems =>
	[
	(res_inst_tac [("p","rep_tr[t]")] ssumE 1),
	(rtac disjI1 1),
	(rtac ((abs_tr_iso RS allI) RS ((rep_tr_iso RS allI) RS iso_strict )
		  RS conjunct2 RS subst) 1),
	(rtac (abs_tr_iso RS subst) 1),
	(etac cfun_arg_cong 1),
	(rtac disjI2 1),
	(rtac disjI1 1),
	(rtac (abs_tr_iso RS subst) 1),
	(rtac cfun_arg_cong 1),
	(etac trans 1),
	(rtac cfun_arg_cong 1),
	(rtac (Exh_one RS disjE) 1),
	(contr_tac 1),
	(atac 1),
	(rtac disjI2 1),
	(rtac disjI2 1),
	(rtac (abs_tr_iso RS subst) 1),
	(rtac cfun_arg_cong 1),
	(etac trans 1),
	(rtac cfun_arg_cong 1),
	(rtac (Exh_one RS disjE) 1),
	(contr_tac 1),
	(atac 1)
	]);


val trE = prove_goal Tr1.thy
	"[| p=UU ==> Q; p = TT ==>Q; p = FF ==>Q|] ==>Q"
 (fn prems =>
	[
	(rtac (Exh_tr RS disjE) 1),
	(eresolve_tac prems 1),
	(etac disjE 1),
	(eresolve_tac prems 1),
	(eresolve_tac prems 1)
	]);


(* ------------------------------------------------------------------------ *) 
(* type tr is flat                                                          *) 
(* ------------------------------------------------------------------------ *)

val prems = goalw Tr1.thy [flat_def] "flat(TT)";
by (rtac allI 1);
by (rtac allI 1);
by (res_inst_tac [("p","x")] trE 1);
by (asm_simp_tac ccc1_ss 1);
by (res_inst_tac [("p","y")] trE 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
by (res_inst_tac [("p","y")] trE 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
by (asm_simp_tac (ccc1_ss addsimps dist_less_tr) 1);
val flat_tr = result();


(* ------------------------------------------------------------------------ *) 
(* properties of tr_when                                                    *) 
(* ------------------------------------------------------------------------ *)

fun prover s =  prove_goalw Tr1.thy [tr_when_def,TT_def,FF_def] s
 (fn prems =>
	[
	(simp_tac Cfun_ss 1),
	(simp_tac (Ssum_ss addsimps [(rep_tr_iso ),
		(abs_tr_iso RS allI) RS ((rep_tr_iso RS allI) 
		RS iso_strict) RS conjunct1]@dist_eq_one)1)
	]);

val tr_when = map prover [
			"tr_when[x][y][UU] = UU",
			"tr_when[x][y][TT] = x",
			"tr_when[x][y][FF] = y"
			];






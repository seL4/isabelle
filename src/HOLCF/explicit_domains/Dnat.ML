(*  Title: 	HOLCF/Dnat.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for dnat.thy 
*)

open Dnat;

(* ------------------------------------------------------------------------*)
(* The isomorphisms dnat_rep_iso and dnat_abs_iso are strict               *)
(* ------------------------------------------------------------------------*)

val dnat_iso_strict = dnat_rep_iso RS (dnat_abs_iso RS 
	(allI  RSN (2,allI RS iso_strict)));

val dnat_rews = [dnat_iso_strict RS conjunct1,
		dnat_iso_strict RS conjunct2];

(* ------------------------------------------------------------------------*)
(* Properties of dnat_copy                                                 *)
(* ------------------------------------------------------------------------*)

fun prover defs thm =  prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (!simpset addsimps 
		(dnat_rews @ [dnat_abs_iso,dnat_rep_iso])) 1)
	]);

val dnat_copy = 
	[
	prover [dnat_copy_def] "dnat_copy`f`UU=UU",
	prover [dnat_copy_def,dzero_def] "dnat_copy`f`dzero= dzero",
	prover [dnat_copy_def,dsucc_def] 
		"n~=UU ==> dnat_copy`f`(dsucc`n) = dsucc`(f`n)"
	];

val dnat_rews =  dnat_copy @ dnat_rews; 

(* ------------------------------------------------------------------------*)
(* Exhaustion and elimination for dnat                                     *)
(* ------------------------------------------------------------------------*)

qed_goalw "Exh_dnat" Dnat.thy [dsucc_def,dzero_def]
	"n = UU | n = dzero | (? x . x~=UU & n = dsucc`x)"
 (fn prems =>
	[
	(Simp_tac  1),
	(rtac (dnat_rep_iso RS subst) 1),
	(res_inst_tac [("p","dnat_rep`n")] ssumE 1),
	(rtac disjI1 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(rtac (disjI1 RS disjI2) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(res_inst_tac [("p","x")] oneE 1),
	(contr_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(rtac (disjI2 RS disjI2) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "dnatE" Dnat.thy 
 "[| n=UU ==> Q; n=dzero ==> Q; !!x.[|n=dsucc`x;x~=UU|]==>Q|]==>Q"
 (fn prems =>
	[
	(rtac (Exh_dnat RS disjE) 1),
	(eresolve_tac prems 1),
	(etac disjE 1),
	(eresolve_tac prems 1),
	(REPEAT (etac exE 1)),
	(resolve_tac prems 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

(* ------------------------------------------------------------------------*)
(* Properties of dnat_when                                                 *)
(* ------------------------------------------------------------------------*)

fun prover defs thm =  prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (!simpset addsimps 
		(dnat_rews @ [dnat_abs_iso,dnat_rep_iso])) 1)
	]);


val dnat_when = [
	prover [dnat_when_def] "dnat_when`c`f`UU=UU",
	prover [dnat_when_def,dzero_def] "dnat_when`c`f`dzero=c",
	prover [dnat_when_def,dsucc_def] 
		"n~=UU ==> dnat_when`c`f`(dsucc`n)=f`n"
	];

val dnat_rews = dnat_when @ dnat_rews;

(* ------------------------------------------------------------------------*)
(* Rewrites for  discriminators and  selectors                             *)
(* ------------------------------------------------------------------------*)

fun prover defs thm = prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_discsel = [
	prover [is_dzero_def] "is_dzero`UU=UU",
	prover [is_dsucc_def] "is_dsucc`UU=UU",
	prover [dpred_def] "dpred`UU=UU"
	];


fun prover defs thm = prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_discsel = [
	prover [is_dzero_def] "is_dzero`dzero=TT",
	prover [is_dzero_def] "n~=UU ==>is_dzero`(dsucc`n)=FF",
	prover [is_dsucc_def] "is_dsucc`dzero=FF",
	prover [is_dsucc_def] "n~=UU ==> is_dsucc`(dsucc`n)=TT",
	prover [dpred_def] "dpred`dzero=UU",
	prover [dpred_def] "n~=UU ==> dpred`(dsucc`n)=n"
	] @ dnat_discsel;

val dnat_rews = dnat_discsel @ dnat_rews;

(* ------------------------------------------------------------------------*)
(* Definedness and strictness                                              *)
(* ------------------------------------------------------------------------*)

fun prover contr thm = prove_goal Dnat.thy thm
 (fn prems =>
	[
	(res_inst_tac [("P1",contr)] classical3 1),
	(simp_tac (!simpset addsimps dnat_rews) 1),
	(dtac sym 1),
	(Asm_simp_tac  1),
	(simp_tac (!simpset addsimps (prems @ dnat_rews)) 1)
	]);

val dnat_constrdef = [
	prover "is_dzero`UU ~= UU" "dzero~=UU",
	prover "is_dsucc`UU ~= UU" "n~=UU ==> dsucc`n~=UU"
	]; 


fun prover defs thm = prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_constrdef = [
	prover [dsucc_def] "dsucc`UU=UU"
	] @ dnat_constrdef;

val dnat_rews = dnat_constrdef @ dnat_rews;


(* ------------------------------------------------------------------------*)
(* Distinctness wrt. << and =                                              *)
(* ------------------------------------------------------------------------*)

val temp = prove_goal Dnat.thy  "~dzero << dsucc`n"
 (fn prems =>
	[
	(res_inst_tac [("P1","TT << FF")] classical3 1),
	(resolve_tac dist_less_tr 1),
	(dres_inst_tac [("fo5","is_dzero")] monofun_cfun_arg 1),
	(etac box_less 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(res_inst_tac [("Q","n=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_dist_less = [temp];

val temp = prove_goal Dnat.thy  "n~=UU ==> ~dsucc`n << dzero"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("P1","TT << FF")] classical3 1),
	(resolve_tac dist_less_tr 1),
	(dres_inst_tac [("fo5","is_dsucc")] monofun_cfun_arg 1),
	(etac box_less 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_dist_less = temp::dnat_dist_less;

val temp = prove_goal Dnat.thy   "dzero ~= dsucc`n"
 (fn prems =>
	[
	(res_inst_tac [("Q","n=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(res_inst_tac [("P1","TT = FF")] classical3 1),
	(resolve_tac dist_eq_tr 1),
	(dres_inst_tac [("f","is_dzero")] cfun_arg_cong 1),
	(etac box_equals 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_dist_eq = [temp, temp RS not_sym];

val dnat_rews = dnat_dist_less @ dnat_dist_eq @ dnat_rews;

(* ------------------------------------------------------------------------*)
(* Invertibility                                                           *)
(* ------------------------------------------------------------------------*)

val dnat_invert = 
	[
prove_goal Dnat.thy 
"[|x1~=UU; y1~=UU; dsucc`x1 << dsucc`y1 |] ==> x1<< y1"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(dres_inst_tac [("fo5","dnat_when`c`(LAM x.x)")] monofun_cfun_arg 1),
	(etac box_less 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	])
	];

(* ------------------------------------------------------------------------*)
(* Injectivity                                                             *)
(* ------------------------------------------------------------------------*)

val dnat_inject = 
	[
prove_goal Dnat.thy 
"[|x1~=UU; y1~=UU; dsucc`x1 = dsucc`y1 |] ==> x1= y1"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(dres_inst_tac [("f","dnat_when`c`(LAM x.x)")] cfun_arg_cong 1),
	(etac box_equals 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	])
	];

(* ------------------------------------------------------------------------*)
(* definedness for  discriminators and  selectors                          *)
(* ------------------------------------------------------------------------*)


fun prover thm = prove_goal Dnat.thy thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac dnatE 1),
	(contr_tac 1),
	(REPEAT (asm_simp_tac (!simpset addsimps dnat_rews) 1))
	]);

val dnat_discsel_def = 
	[
	prover  "n~=UU ==> is_dzero`n ~= UU",
	prover  "n~=UU ==> is_dsucc`n ~= UU"
	];

val dnat_rews = dnat_discsel_def @ dnat_rews;

 
(* ------------------------------------------------------------------------*)
(* Properties dnat_take                                                    *)
(* ------------------------------------------------------------------------*)
val temp = prove_goalw Dnat.thy [dnat_take_def] "dnat_take n`UU = UU"
 (fn prems =>
	[
	(res_inst_tac [("n","n")] natE 1),
	(Asm_simp_tac 1),
	(Asm_simp_tac 1),
	(simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_take = [temp];

val temp = prove_goalw Dnat.thy [dnat_take_def] "dnat_take 0`xs = UU"
 (fn prems =>
	[
	(Asm_simp_tac 1)
	]);

val dnat_take = temp::dnat_take;

val temp = prove_goalw Dnat.thy [dnat_take_def]
	"dnat_take (Suc n)`dzero=dzero"
 (fn prems =>
	[
	(Asm_simp_tac 1),
	(simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_take = temp::dnat_take;

val temp = prove_goalw Dnat.thy [dnat_take_def]
  "dnat_take (Suc n)`(dsucc`xs)=dsucc`(dnat_take n ` xs)"
 (fn prems =>
	[
	(res_inst_tac [("Q","xs=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(res_inst_tac [("n","n")] natE 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

val dnat_take = temp::dnat_take;

val dnat_rews = dnat_take @ dnat_rews;


(* ------------------------------------------------------------------------*)
(* take lemma for dnats                                                  *)
(* ------------------------------------------------------------------------*)

fun prover reach defs thm  = prove_goalw Dnat.thy defs thm
 (fn prems =>
	[
	(res_inst_tac [("t","s1")] (reach RS subst) 1),
	(res_inst_tac [("t","s2")] (reach RS subst) 1),
	(rtac (fix_def2 RS ssubst) 1),
	(rtac (contlub_cfun_fun RS ssubst) 1),
	(rtac is_chain_iterate 1),
	(rtac (contlub_cfun_fun RS ssubst) 1),
	(rtac is_chain_iterate 1),
	(rtac lub_equal 1),
	(rtac (is_chain_iterate RS ch2ch_fappL) 1),
	(rtac (is_chain_iterate RS ch2ch_fappL) 1),
	(rtac allI 1),
	(resolve_tac prems 1)
	]);

val dnat_take_lemma = prover dnat_reach  [dnat_take_def]
	"(!!n.dnat_take n`s1 = dnat_take n`s2) ==> s1=s2";


(* ------------------------------------------------------------------------*)
(* Co -induction for dnats                                                 *)
(* ------------------------------------------------------------------------*)

qed_goalw "dnat_coind_lemma" Dnat.thy [dnat_bisim_def] 
"dnat_bisim R ==> ! p q. R p q --> dnat_take n`p = dnat_take n`q"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(nat_ind_tac "n" 1),
	(simp_tac (!simpset addsimps dnat_take) 1),
	(strip_tac 1),
	((etac allE 1) THEN (etac allE 1) THEN (etac (mp RS disjE) 1)),
	(atac 1),
	(asm_simp_tac (!simpset addsimps dnat_take) 1),
	(etac disjE 1),
	(asm_simp_tac (!simpset addsimps dnat_take) 1),
	(etac exE 1),
	(etac exE 1),
	(asm_simp_tac (!simpset addsimps dnat_take) 1),
	(REPEAT (etac conjE 1)),
	(rtac cfun_arg_cong 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "dnat_coind" Dnat.thy "[|dnat_bisim R;R p q|] ==> p = q"
 (fn prems =>
	[
	(rtac dnat_take_lemma 1),
	(rtac (dnat_coind_lemma RS spec RS spec RS mp) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1)
	]);


(* ------------------------------------------------------------------------*)
(* structural induction for admissible predicates                          *)
(* ------------------------------------------------------------------------*)

(* not needed any longer
qed_goal "dnat_ind" Dnat.thy
"[| adm(P);\
\   P(UU);\
\   P(dzero);\
\   !! s1.[|s1~=UU ; P(s1)|] ==> P(dsucc`s1)|] ==> P(s)"
 (fn prems =>
	[
	(rtac (dnat_reach RS subst) 1),
	(res_inst_tac [("x","s")] spec 1),
	(rtac fix_ind 1),
	(rtac adm_all2 1),
	(rtac adm_subst 1),
	(cont_tacR 1),
	(resolve_tac prems 1),
	(Simp_tac 1),
	(resolve_tac prems 1),
	(strip_tac 1),
	(res_inst_tac [("n","xa")] dnatE 1),
	(asm_simp_tac (!simpset addsimps dnat_copy) 1),
	(resolve_tac prems 1),
	(asm_simp_tac (!simpset addsimps dnat_copy) 1),
	(resolve_tac prems 1),
	(asm_simp_tac (!simpset addsimps dnat_copy) 1),
	(res_inst_tac [("Q","x`xb=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(resolve_tac prems 1),
	(eresolve_tac prems 1),
	(etac spec 1)
	]);
*)

qed_goal "dnat_finite_ind" Dnat.thy
"[|P(UU);P(dzero);\
\  !! s1.[|s1~=UU;P(s1)|] ==> P(dsucc`s1)\
\  |] ==> !s.P(dnat_take n`s)"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (!simpset addsimps dnat_rews) 1),
	(resolve_tac prems 1),
	(rtac allI 1),
	(res_inst_tac [("n","s")] dnatE 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(resolve_tac prems 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(resolve_tac prems 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(res_inst_tac [("Q","dnat_take n1`x=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1),
	(atac 1),
	(etac spec 1)
	]);

qed_goal "dnat_all_finite_lemma1" Dnat.thy
"!s.dnat_take n`s=UU |dnat_take n`s=s"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (!simpset addsimps dnat_rews) 1),
	(rtac allI 1),
	(res_inst_tac [("n","s")] dnatE 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(eres_inst_tac [("x","x")] allE 1),
	(etac disjE 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1)
	]);

qed_goal "dnat_all_finite_lemma2" Dnat.thy "? n.dnat_take n`s=s"
 (fn prems =>
	[
	(res_inst_tac [("Q","s=UU")] classical2 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(subgoal_tac "(!n.dnat_take(n)`s=UU) |(? n.dnat_take(n)`s=s)" 1),
	(etac disjE 1),
	(eres_inst_tac [("P","s=UU")] notE 1),
	(rtac dnat_take_lemma 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(atac 1),
	(subgoal_tac "!n.!s.dnat_take(n)`s=UU |dnat_take(n)`s=s" 1),
	(fast_tac HOL_cs 1),
	(rtac allI 1),
	(rtac dnat_all_finite_lemma1 1)
	]);


qed_goal "dnat_ind" Dnat.thy
"[|P(UU);P(dzero);\
\  !! s1.[|s1~=UU;P(s1)|] ==> P(dsucc`s1)\
\  |] ==> P(s)"
 (fn prems =>
	[
	(rtac (dnat_all_finite_lemma2 RS exE) 1),
	(etac subst 1),
	(rtac (dnat_finite_ind RS spec) 1),
	(REPEAT (resolve_tac prems 1)),
	(REPEAT (atac 1))
	]);


qed_goalw "dnat_flat" Dnat.thy [flat_def] "flat(dzero)"
 (fn prems =>
	[
	(rtac allI 1),
	(res_inst_tac [("s","x")] dnat_ind 1),
	(fast_tac HOL_cs 1),
	(rtac allI 1),
	(res_inst_tac [("n","y")] dnatE 1),
	(fast_tac (HOL_cs addSIs [UU_I]) 1),
	(Asm_simp_tac 1),
	(asm_simp_tac (!simpset addsimps dnat_dist_less) 1),
	(rtac allI 1),
	(res_inst_tac [("n","y")] dnatE 1),
	(fast_tac (HOL_cs addSIs [UU_I]) 1),
	(asm_simp_tac (!simpset addsimps dnat_dist_less) 1),
	(asm_simp_tac (!simpset addsimps dnat_rews) 1),
	(strip_tac 1),
	(subgoal_tac "s1<<xa" 1),
	(etac allE 1),
	(dtac mp 1),
	(atac 1),
	(etac disjE 1),
	(contr_tac 1),
	(Asm_simp_tac 1),
	(resolve_tac  dnat_invert 1),
	(REPEAT (atac 1))
	]);







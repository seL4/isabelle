(*  Title: 	HOLCF/coind.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open Coind;

(* ------------------------------------------------------------------------- *)
(* expand fixed point properties                                             *)
(* ------------------------------------------------------------------------- *)


val nats_def2 = fix_prover Coind.thy nats_def 
	"nats = scons[dzero][smap[dsucc][nats]]";

val from_def2 = fix_prover Coind.thy from_def 
	"from = (LAM n.scons[n][from[dsucc[n]]])";



(* ------------------------------------------------------------------------- *)
(* recursive  properties                                                     *)
(* ------------------------------------------------------------------------- *)


qed_goal "from" Coind.thy "from[n] = scons[n][from[dsucc[n]]]"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac (from_def2 RS ssubst) 1),
	(simp_tac HOLCF_ss  1),
	(rtac refl 1)
	]);


qed_goal "from1" Coind.thy "from[UU] = UU"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac (from RS ssubst) 1),
	(resolve_tac  stream_constrdef 1),
	(rtac refl 1)
	]);

val coind_rews = 
	[iterator1, iterator2, iterator3, smap1, smap2,from1];


(* ------------------------------------------------------------------------- *)
(* the example                                                               *)
(* prove:        nats = from[dzero]                                          *)
(* ------------------------------------------------------------------------- *)


qed_goal "coind_lemma1" Coind.thy "iterator[n][smap[dsucc]][nats] =\
\		 scons[n][iterator[dsucc[n]][smap[dsucc]][nats]]"
 (fn prems =>
	[
	(res_inst_tac [("s","n")] dnat_ind 1),
	(simp_tac (HOLCF_ss addsimps (coind_rews @ stream_rews)) 1),
	(simp_tac (HOLCF_ss addsimps (coind_rews @ stream_rews)) 1),
	(rtac trans 1),
	(rtac nats_def2 1),
	(simp_tac (HOLCF_ss addsimps (coind_rews @ dnat_rews)) 1),
	(rtac trans 1),
	(etac iterator3 1),
	(rtac trans 1),
	(asm_simp_tac HOLCF_ss 1),
	(rtac trans 1),
	(etac smap2 1),
	(rtac cfun_arg_cong 1),
	(asm_simp_tac (HOLCF_ss addsimps ([iterator3 RS sym] @ dnat_rews)) 1)
	]);


qed_goal "nats_eq_from" Coind.thy "nats = from[dzero]"
 (fn prems =>
	[
	(res_inst_tac [("R",
"% p q.? n. p = iterator[n][smap[dsucc]][nats] & q = from[n]")] stream_coind 1),
	(res_inst_tac [("x","dzero")] exI 2),
	(asm_simp_tac (HOLCF_ss addsimps coind_rews) 2),
	(rewrite_goals_tac [stream_bisim_def]),
	(strip_tac 1),
	(etac exE 1),
	(res_inst_tac [("Q","n=UU")] classical2 1),
	(rtac disjI1 1),
	(asm_simp_tac (HOLCF_ss addsimps coind_rews) 1),
	(rtac disjI2 1),
	(etac conjE 1),
	(hyp_subst_tac 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("x","n")] exI 1),
	(res_inst_tac [("x","iterator[dsucc[n]][smap[dsucc]][nats]")] exI 1),
	(res_inst_tac [("x","from[dsucc[n]]")] exI 1),
	(etac conjI 1),
	(rtac conjI 1),
	(rtac coind_lemma1 1),
	(rtac conjI 1),
	(rtac from 1),
	(res_inst_tac [("x","dsucc[n]")] exI 1),
	(fast_tac HOL_cs 1)
	]);

(* another proof using stream_coind_lemma2 *)

qed_goal "nats_eq_from" Coind.thy "nats = from[dzero]"
 (fn prems =>
	[
	(res_inst_tac [("R","% p q.? n. p = \
\	iterator[n][smap[dsucc]][nats] & q = from[n]")] stream_coind 1),
	(rtac stream_coind_lemma2 1),
	(strip_tac 1),
	(etac exE 1),
	(res_inst_tac [("Q","n=UU")] classical2 1),
	(asm_simp_tac (HOLCF_ss addsimps coind_rews) 1),
	(res_inst_tac [("x","UU::dnat")] exI 1),
	(simp_tac (HOLCF_ss addsimps coind_rews addsimps stream_rews) 1),
	(etac conjE 1),
	(hyp_subst_tac 1),
	(hyp_subst_tac 1),
	(rtac conjI 1),
	(rtac (coind_lemma1 RS ssubst) 1),
	(rtac (from RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(res_inst_tac [("x","dsucc[n]")] exI 1),
	(rtac conjI 1),
	(rtac trans 1),
	(rtac (coind_lemma1 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(rtac refl 1),
	(rtac trans 1),
	(rtac (from RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(rtac refl 1),
	(res_inst_tac [("x","dzero")] exI 1),
	(asm_simp_tac (HOLCF_ss addsimps coind_rews) 1)
	]);


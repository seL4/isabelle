(*  Title: 	FOCUS/ex/coind.ML
    ID:         $ $
    Author: 	Franz Regensburger
    Copyright   1993, 1995 Technische Universitaet Muenchen
*)

open Coind;

(* ------------------------------------------------------------------------- *)
(* expand fixed point properties                                             *)
(* ------------------------------------------------------------------------- *)


val nats_def2 = fix_prover2 Coind.thy nats_def 
	"nats = dzero&&(smap`dsucc`nats)";

val from_def2 = fix_prover2 Coind.thy from_def 
	"from = (¤n.n&&(from`(dsucc`n)))";



(* ------------------------------------------------------------------------- *)
(* recursive  properties                                                     *)
(* ------------------------------------------------------------------------- *)


val from = prove_goal Coind.thy "from`n = n&&(from`(dsucc`n))"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac (from_def2 RS ssubst) 1),
	(simp_tac HOLCF_ss  1),
	(rtac refl 1)
	]);


val from1 = prove_goal Coind.thy "from`Ø = Ø"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac (from RS ssubst) 1),
	(resolve_tac  stream.con_rews 1),
	(rtac refl 1)
	]);

val coind_rews = 
	[iterator1, iterator2, iterator3, smap1, smap2,from1];

(* ------------------------------------------------------------------------- *)
(* the example                                                               *)
(* prove:        nats = from`dzero                                           *)
(* ------------------------------------------------------------------------- *)

val prems = goal Coind.thy "iterator`n`(smap`dsucc)`nats =\
\		 n&&(iterator`(dsucc`n)`(smap`dsucc)`nats)";
by (res_inst_tac [("x","n")] dnat.ind 1);
by (simp_tac (HOLCF_ss addsimps (coind_rews @ stream.rews)) 1);
by (simp_tac (HOLCF_ss addsimps (coind_rews @ stream.rews)) 1);
by (rtac trans 1);
by (rtac nats_def2 1);
by (simp_tac (HOLCF_ss addsimps (coind_rews @ dnat.rews)) 1);
by (rtac trans 1);
by (etac iterator3 1);
by (rtac trans 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac trans 1);
by (etac smap2 1);
by (rtac cfun_arg_cong 1);
by (asm_simp_tac (HOLCF_ss addsimps ([iterator3 RS sym] @ dnat.rews)) 1);
val coind_lemma1 = result();

val prems = goal Coind.thy "nats = from`dzero";
by (res_inst_tac [("R","% p q.? n. p = iterator`n`(smap`dsucc)`nats & q = from`n")] stream.coind 1);
by (res_inst_tac [("x","dzero")] exI 2);
by (asm_simp_tac (HOLCF_ss addsimps coind_rews) 2);
by (rewrite_goals_tac [stream.bisim_def]);
by (strip_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (case_tac "n=Ø" 1);
by (rtac disjI1 1);
by (asm_simp_tac (HOLCF_ss addsimps coind_rews) 1);
by (rtac disjI2 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x","n")] exI 1);
by (res_inst_tac [("x","iterator`(dsucc`n)`(smap`dsucc)`nats")] exI 1);
by (res_inst_tac [("x","from`(dsucc`n)")] exI 1);
by (etac conjI 1);
by (rtac conjI 1);
by (res_inst_tac [("x","dsucc`n")] exI 1);
by (fast_tac HOL_cs 1);
by (rtac conjI 1);
by (rtac coind_lemma1 1);
by (rtac from 1);
val nats_eq_from = result();

(* another proof using stream_coind_lemma2 *)

val prems = goal Coind.thy "nats = from`dzero";
by (res_inst_tac [("R","% p q.? n. p = iterator`n`(smap`dsucc)`nats & q = from`n")] stream.coind 1);
by (rtac stream_coind_lemma2 1);
by (strip_tac 1);
by (etac exE 1);
by (case_tac "n=Ø" 1);
by (asm_simp_tac (HOLCF_ss addsimps coind_rews) 1);
by (res_inst_tac [("x","Ø::dnat")] exI 1);
by (simp_tac (HOLCF_ss addsimps coind_rews addsimps stream.rews) 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
by (rtac conjI 1);
by (rtac (coind_lemma1 RS ssubst) 1);
by (rtac (from RS ssubst) 1);
by (asm_simp_tac (HOLCF_ss addsimps stream.rews) 1);
by (res_inst_tac [("x","dsucc`n")] exI 1);
by (rtac conjI 1);
by (rtac trans 1);
by (rtac (coind_lemma1 RS ssubst) 1);
by (asm_simp_tac (HOLCF_ss addsimps stream.rews) 1);
by (rtac refl 1);
by (rtac trans 1);
by (rtac (from RS ssubst) 1);
by (asm_simp_tac (HOLCF_ss addsimps stream.rews) 1);
by (rtac refl 1);
by (res_inst_tac [("x","dzero")] exI 1);
by (asm_simp_tac (HOLCF_ss addsimps coind_rews) 1);
val nats_eq_from = result();

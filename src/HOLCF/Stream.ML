(*  Title: 	HOLCF/stream.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for stream.thy
*)

open Stream;

(* ------------------------------------------------------------------------*)
(* The isomorphisms stream_rep_iso and stream_abs_iso are strict           *)
(* ------------------------------------------------------------------------*)

val stream_iso_strict= stream_rep_iso RS (stream_abs_iso RS 
	(allI  RSN (2,allI RS iso_strict)));

val stream_rews = [stream_iso_strict RS conjunct1,
		stream_iso_strict RS conjunct2];

(* ------------------------------------------------------------------------*)
(* Properties of stream_copy                                               *)
(* ------------------------------------------------------------------------*)

fun prover defs thm =  prove_goalw Stream.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps 
		(stream_rews @ [stream_abs_iso,stream_rep_iso])) 1)
	]);

val stream_copy = 
	[
	prover [stream_copy_def] "stream_copy`f`UU=UU",
	prover [stream_copy_def,scons_def] 
	"x~=UU ==> stream_copy`f`(scons`x`xs)= scons`x`(f`xs)"
	];

val stream_rews =  stream_copy @ stream_rews; 

(* ------------------------------------------------------------------------*)
(* Exhaustion and elimination for streams                                  *)
(* ------------------------------------------------------------------------*)

qed_goalw "Exh_stream" Stream.thy [scons_def]
	"s = UU | (? x xs. x~=UU & s = scons`x`xs)"
 (fn prems =>
	[
	(simp_tac HOLCF_ss  1),
	(rtac (stream_rep_iso RS subst) 1),
	(res_inst_tac [("p","stream_rep`s")] sprodE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac HOLCF_ss  1),
	(res_inst_tac [("p","y")] liftE1 1),
	(contr_tac 1),
	(rtac disjI2 1),
	(rtac exI 1),
	(rtac exI 1),
	(etac conjI 1),
	(asm_simp_tac HOLCF_ss  1)
	]);

qed_goal "streamE" Stream.thy 
	"[| s=UU ==> Q; !!x xs.[|s=scons`x`xs;x~=UU|]==>Q|]==>Q"
 (fn prems =>
	[
	(rtac (Exh_stream RS disjE) 1),
	(eresolve_tac prems 1),
	(etac exE 1),
	(etac exE 1),
	(resolve_tac prems 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

(* ------------------------------------------------------------------------*)
(* Properties of stream_when                                               *)
(* ------------------------------------------------------------------------*)

fun prover defs thm =  prove_goalw Stream.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps 
		(stream_rews @ [stream_abs_iso,stream_rep_iso])) 1)
	]);


val stream_when = [
	prover [stream_when_def] "stream_when`f`UU=UU",
	prover [stream_when_def,scons_def] 
		"x~=UU ==> stream_when`f`(scons`x`xs)= f`x`xs"
	];

val stream_rews = stream_when @ stream_rews;

(* ------------------------------------------------------------------------*)
(* Rewrites for  discriminators and  selectors                             *)
(* ------------------------------------------------------------------------*)

fun prover defs thm = prove_goalw Stream.thy defs thm
 (fn prems =>
	[
	(simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

val stream_discsel = [
	prover [is_scons_def] "is_scons`UU=UU",
	prover [shd_def] "shd`UU=UU",
	prover [stl_def] "stl`UU=UU"
	];

fun prover defs thm = prove_goalw Stream.thy defs thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

val stream_discsel = [
prover [is_scons_def,shd_def,stl_def] "x~=UU ==> is_scons`(scons`x`xs)=TT",
prover [is_scons_def,shd_def,stl_def] "x~=UU ==> shd`(scons`x`xs)=x",
prover [is_scons_def,shd_def,stl_def] "x~=UU ==> stl`(scons`x`xs)=xs"
	] @ stream_discsel;

val stream_rews = stream_discsel @ stream_rews;

(* ------------------------------------------------------------------------*)
(* Definedness and strictness                                              *)
(* ------------------------------------------------------------------------*)

fun prover contr thm = prove_goal Stream.thy thm
 (fn prems =>
	[
	(res_inst_tac [("P1",contr)] classical3 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(dtac sym 1),
	(asm_simp_tac HOLCF_ss  1),
	(simp_tac (HOLCF_ss addsimps (prems @ stream_rews)) 1)
	]);

val stream_constrdef = [
	prover "is_scons`(UU::'a stream)~=UU" "x~=UU ==> scons`(x::'a)`xs~=UU"
	]; 

fun prover defs thm = prove_goalw Stream.thy defs thm
 (fn prems =>
	[
	(simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

val stream_constrdef = [
	prover [scons_def] "scons`UU`xs=UU"
	] @ stream_constrdef;

val stream_rews = stream_constrdef @ stream_rews;


(* ------------------------------------------------------------------------*)
(* Distinctness wrt. << and =                                              *)
(* ------------------------------------------------------------------------*)


(* ------------------------------------------------------------------------*)
(* Invertibility                                                           *)
(* ------------------------------------------------------------------------*)

val stream_invert =
	[
prove_goal Stream.thy "[|x1~=UU; y1~=UU;\
\ scons`x1`x2 << scons`y1`y2|] ==> x1<< y1 & x2 << y2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac conjI 1),
	(dres_inst_tac [("fo5","stream_when`(LAM x l.x)")] monofun_cfun_arg 1),
	(etac box_less 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(dres_inst_tac [("fo5","stream_when`(LAM x l.l)")] monofun_cfun_arg 1),
	(etac box_less 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1)
	])
	];

(* ------------------------------------------------------------------------*)
(* Injectivity                                                             *)
(* ------------------------------------------------------------------------*)

val stream_inject = 
	[
prove_goal Stream.thy "[|x1~=UU; y1~=UU;\
\ scons`x1`x2 = scons`y1`y2 |] ==> x1= y1 & x2 = y2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac conjI 1),
	(dres_inst_tac [("f","stream_when`(LAM x l.x)")] cfun_arg_cong 1),
	(etac box_equals 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(dres_inst_tac [("f","stream_when`(LAM x l.l)")] cfun_arg_cong 1),
	(etac box_equals 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_when) 1)
	])
	];

(* ------------------------------------------------------------------------*)
(* definedness for  discriminators and  selectors                          *)
(* ------------------------------------------------------------------------*)

fun prover thm = prove_goal Stream.thy thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac streamE 1),
	(contr_tac 1),
	(REPEAT (asm_simp_tac (HOLCF_ss addsimps stream_discsel) 1))
	]);

val stream_discsel_def = 
	[
	prover "s~=UU ==> is_scons`s ~= UU", 
	prover "s~=UU ==> shd`s ~=UU" 
	];

val stream_rews = stream_discsel_def @ stream_rews;


(* ------------------------------------------------------------------------*)
(* Properties stream_take                                                  *)
(* ------------------------------------------------------------------------*)

val stream_take =
	[
prove_goalw Stream.thy [stream_take_def] "stream_take n`UU = UU"
 (fn prems =>
	[
	(res_inst_tac [("n","n")] natE 1),
	(asm_simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]),
prove_goalw Stream.thy [stream_take_def] "stream_take 0`xs=UU"
 (fn prems =>
	[
	(asm_simp_tac iterate_ss 1)
	])];

fun prover thm = prove_goalw Stream.thy [stream_take_def] thm
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(simp_tac iterate_ss 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

val stream_take = [
prover 
  "x~=UU ==> stream_take (Suc n)`(scons`x`xs) = scons`x`(stream_take n`xs)"
	] @ stream_take;

val stream_rews = stream_take @ stream_rews;

(* ------------------------------------------------------------------------*)
(* enhance the simplifier                                                  *)
(* ------------------------------------------------------------------------*)

qed_goal "stream_copy2" Stream.thy 
     "stream_copy`f`(scons`x`xs) = scons`x`(f`xs)"
 (fn prems =>
	[
	(res_inst_tac [("Q","x=UU")] classical2 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

qed_goal "shd2" Stream.thy "shd`(scons`x`xs) = x"
 (fn prems =>
	[
	(res_inst_tac [("Q","x=UU")] classical2 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

qed_goal "stream_take2" Stream.thy 
 "stream_take (Suc n)`(scons`x`xs) = scons`x`(stream_take n`xs)"
 (fn prems =>
	[
	(res_inst_tac [("Q","x=UU")] classical2 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

val stream_rews = [stream_iso_strict RS conjunct1,
		   stream_iso_strict RS conjunct2,
                   hd stream_copy, stream_copy2]
                  @ stream_when
                  @ [hd stream_discsel,shd2] @ (tl (tl stream_discsel))  
                  @ stream_constrdef
                  @ stream_discsel_def
                  @ [ stream_take2] @ (tl stream_take);


(* ------------------------------------------------------------------------*)
(* take lemma for streams                                                  *)
(* ------------------------------------------------------------------------*)

fun prover reach defs thm  = prove_goalw Stream.thy defs thm
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

val stream_take_lemma = prover stream_reach  [stream_take_def]
	"(!!n.stream_take n`s1 = stream_take n`s2) ==> s1=s2";


qed_goal "stream_reach2" Stream.thy  "lub(range(%i.stream_take i`s))=s"
 (fn prems =>
	[
	(res_inst_tac [("t","s")] (stream_reach RS subst) 1),
	(rtac (fix_def2 RS ssubst) 1),
	(rewrite_goals_tac [stream_take_def]),
	(rtac (contlub_cfun_fun RS ssubst) 1),
	(rtac is_chain_iterate 1),
	(rtac refl 1)
	]);

(* ------------------------------------------------------------------------*)
(* Co -induction for streams                                               *)
(* ------------------------------------------------------------------------*)

qed_goalw "stream_coind_lemma" Stream.thy [stream_bisim_def] 
"stream_bisim R ==> ! p q. R p q --> stream_take n`p = stream_take n`q"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(nat_ind_tac "n" 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1),
	((etac allE 1) THEN (etac allE 1) THEN (etac (mp RS disjE) 1)),
	(atac 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(etac exE 1),
	(etac exE 1),
	(etac exE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(REPEAT (etac conjE 1)),
	(rtac cfun_arg_cong 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "stream_coind" Stream.thy "[|stream_bisim R ;R p q|] ==> p = q"
 (fn prems =>
	[
	(rtac stream_take_lemma 1),
	(rtac (stream_coind_lemma RS spec RS spec RS mp) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1)
	]);

(* ------------------------------------------------------------------------*)
(* structural induction for admissible predicates                          *)
(* ------------------------------------------------------------------------*)

qed_goal "stream_finite_ind" Stream.thy
"[|P(UU);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(scons`x`s1)\
\  |] ==> !s.P(stream_take n`s)"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(resolve_tac prems 1),
	(rtac allI 1),
	(res_inst_tac [("s","s")] streamE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(resolve_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(resolve_tac prems 1),
	(atac 1),
	(etac spec 1)
	]);

qed_goalw "stream_finite_ind2" Stream.thy  [stream_finite_def]
"(!!n.P(stream_take n`s)) ==>  stream_finite(s) -->P(s)"
 (fn prems =>
	[
	(strip_tac 1),
	(etac exE 1),
	(etac subst 1),
	(resolve_tac prems 1)
	]);

qed_goal "stream_finite_ind3" Stream.thy 
"[|P(UU);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(scons`x`s1)\
\  |] ==> stream_finite(s) --> P(s)"
 (fn prems =>
	[
	(rtac stream_finite_ind2 1),
	(rtac (stream_finite_ind RS spec) 1),
	(REPEAT (resolve_tac prems 1)),
	(REPEAT (atac 1))
	]);

(* prove induction using definition of admissibility 
   stream_reach rsp. stream_reach2 
   and finite induction stream_finite_ind *)

qed_goal "stream_ind" Stream.thy
"[|adm(P);\
\  P(UU);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(scons`x`s1)\
\  |] ==> P(s)"
 (fn prems =>
	[
	(rtac (stream_reach2 RS subst) 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(resolve_tac prems 1),
	(SELECT_GOAL (rewrite_goals_tac [stream_take_def]) 1),
	(rtac ch2ch_fappL 1),
	(rtac is_chain_iterate 1),
	(rtac allI 1),
	(rtac (stream_finite_ind RS spec) 1),
	(REPEAT (resolve_tac prems 1)),
	(REPEAT (atac 1))
	]);

(* prove induction with usual LCF-Method using fixed point induction *)
qed_goal "stream_ind" Stream.thy
"[|adm(P);\
\  P(UU);\
\  !! x s1.[|x~=UU;P(s1)|] ==> P(scons`x`s1)\
\  |] ==> P(s)"
 (fn prems =>
	[
	(rtac (stream_reach RS subst) 1),
	(res_inst_tac [("x","s")] spec 1),
	(rtac wfix_ind 1),
	(rtac adm_impl_admw 1),
	(REPEAT (resolve_tac adm_thms 1)),
	(rtac adm_subst 1),
	(cont_tacR 1),
	(resolve_tac prems 1),
	(rtac allI 1),
	(rtac (rewrite_rule [stream_take_def] stream_finite_ind) 1),
	(REPEAT (resolve_tac prems 1)),
	(REPEAT (atac 1))
	]);


(* ------------------------------------------------------------------------*)
(* simplify use of Co-induction                                            *)
(* ------------------------------------------------------------------------*)

qed_goal "surjectiv_scons" Stream.thy "scons`(shd`s)`(stl`s)=s"
 (fn prems =>
	[
	(res_inst_tac [("s","s")] streamE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);


qed_goalw "stream_coind_lemma2" Stream.thy [stream_bisim_def]
"!s1 s2. R s1 s2 --> shd`s1 = shd`s2 & R (stl`s1) (stl`s2) ==> stream_bisim R"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(etac allE 1),
	(etac allE 1),
	(dtac mp 1),
	(atac 1),
	(etac conjE 1),
	(res_inst_tac [("Q","s1 = UU & s2 = UU")] classical2 1),
	(rtac disjI1 1),
	(fast_tac HOL_cs 1),
	(rtac disjI2 1),
	(rtac disjE 1),
	(etac (de_morgan2 RS ssubst) 1),
	(res_inst_tac [("x","shd`s1")] exI 1),
	(res_inst_tac [("x","stl`s1")] exI 1),
	(res_inst_tac [("x","stl`s2")] exI 1),
	(rtac conjI 1),
	(eresolve_tac stream_discsel_def 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews addsimps [surjectiv_scons]) 1),
	(eres_inst_tac [("s","shd`s1"),("t","shd`s2")] subst 1),
	(simp_tac (HOLCF_ss addsimps stream_rews addsimps [surjectiv_scons]) 1),
	(res_inst_tac [("x","shd`s2")] exI 1),
	(res_inst_tac [("x","stl`s1")] exI 1),
	(res_inst_tac [("x","stl`s2")] exI 1),
	(rtac conjI 1),
	(eresolve_tac stream_discsel_def 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews addsimps [surjectiv_scons]) 1),
	(res_inst_tac [("s","shd`s1"),("t","shd`s2")] ssubst 1),
	(etac sym 1),
	(simp_tac (HOLCF_ss addsimps stream_rews addsimps [surjectiv_scons]) 1)
	]);


(* ------------------------------------------------------------------------*)
(* theorems about finite and infinite streams                              *)
(* ------------------------------------------------------------------------*)

(* ----------------------------------------------------------------------- *)
(* 2 lemmas about stream_finite                                            *)
(* ----------------------------------------------------------------------- *)

qed_goalw "stream_finite_UU" Stream.thy [stream_finite_def]
	 "stream_finite(UU)"
 (fn prems =>
	[
	(rtac exI 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

qed_goal "inf_stream_not_UU" Stream.thy  "~stream_finite(s)  ==> s ~= UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac swap 1),
	(dtac notnotD 1),
	(hyp_subst_tac  1),
	(rtac stream_finite_UU 1)
	]);

(* ----------------------------------------------------------------------- *)
(* a lemma about shd                                                       *)
(* ----------------------------------------------------------------------- *)

qed_goal "stream_shd_lemma1" Stream.thy "shd`s=UU --> s=UU"
 (fn prems =>
	[
	(res_inst_tac [("s","s")] streamE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(hyp_subst_tac 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);


(* ----------------------------------------------------------------------- *)
(* lemmas about stream_take                                                *)
(* ----------------------------------------------------------------------- *)

qed_goal "stream_take_lemma1" Stream.thy 
 "!x xs.x~=UU --> \
\  stream_take (Suc n)`(scons`x`xs) = scons`x`xs --> stream_take n`xs=xs"
 (fn prems =>
	[
	(rtac allI 1),
	(rtac allI 1),
	(rtac impI 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1),
	(rtac ((hd stream_inject) RS conjunct2) 1),
	(atac 1),
	(atac 1),
	(atac 1)
	]);


qed_goal "stream_take_lemma2" Stream.thy 
 "! s2. stream_take n`s2 = s2 --> stream_take (Suc n)`s2=s2"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1 ),
	(hyp_subst_tac  1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(rtac allI 1),
	(res_inst_tac [("s","s2")] streamE 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1 ),
	(subgoal_tac "stream_take n1`xs = xs" 1),
	(rtac ((hd stream_inject) RS conjunct2) 2),
	(atac 4),
	(atac 2),
	(atac 2),
	(rtac cfun_arg_cong 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "stream_take_lemma3" Stream.thy 
 "!x xs.x~=UU --> \
\  stream_take n`(scons`x`xs) = scons`x`xs --> stream_take n`xs=xs"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1 ),
	(res_inst_tac [("P","scons`x`xs=UU")] notE 1),
	(eresolve_tac stream_constrdef 1),
	(etac sym 1),
	(strip_tac 1 ),
	(rtac (stream_take_lemma2 RS spec RS mp) 1),
	(res_inst_tac [("x1.1","x")] ((hd stream_inject) RS conjunct2) 1),
	(atac 1),
	(atac 1),
	(etac (stream_take2 RS subst) 1)
	]);

qed_goal "stream_take_lemma4" Stream.thy 
 "!x xs.\
\stream_take n`xs=xs --> stream_take (Suc n)`(scons`x`xs) = scons`x`xs"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

(* ---- *)

qed_goal "stream_take_lemma5" Stream.thy 
"!s. stream_take n`s=s --> iterate n stl s=UU"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac iterate_ss 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1),
	(res_inst_tac [("s","s")] streamE 1),
	(hyp_subst_tac 1),
	(rtac (iterate_Suc2 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(rtac (iterate_Suc2 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(etac allE 1),
	(etac mp 1),
	(hyp_subst_tac 1),
	(etac (stream_take_lemma1 RS spec RS spec RS mp RS mp) 1),
	(atac 1)
	]);

qed_goal "stream_take_lemma6" Stream.thy 
"!s.iterate n stl s =UU --> stream_take n`s=s"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac iterate_ss 1),
	(strip_tac 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(rtac allI 1),
	(res_inst_tac [("s","s")] streamE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(hyp_subst_tac 1),
	(rtac (iterate_Suc2 RS ssubst) 1),
	(asm_simp_tac (HOLCF_ss addsimps stream_rews) 1)
	]);

qed_goal "stream_take_lemma7" Stream.thy 
"(iterate n stl s=UU) = (stream_take n`s=s)"
 (fn prems =>
	[
	(rtac iffI 1),
	(etac (stream_take_lemma6 RS spec RS mp) 1),
	(etac (stream_take_lemma5 RS spec RS mp) 1)
	]);


qed_goal "stream_take_lemma8" Stream.thy
"[|adm(P); !n. ? m. n < m & P (stream_take m`s)|] ==> P(s)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (stream_reach2 RS subst) 1),
	(rtac adm_disj_lemma11 1),
	(atac 1),
	(atac 2),
	(rewrite_goals_tac [stream_take_def]),
	(rtac ch2ch_fappL 1),
	(rtac is_chain_iterate 1)
	]);

(* ----------------------------------------------------------------------- *)
(* lemmas stream_finite                                                    *)
(* ----------------------------------------------------------------------- *)

qed_goalw "stream_finite_lemma1" Stream.thy [stream_finite_def]
 "stream_finite(xs) ==> stream_finite(scons`x`xs)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(rtac exI 1),
	(etac (stream_take_lemma4 RS spec RS spec RS mp) 1)
	]);

qed_goalw "stream_finite_lemma2" Stream.thy [stream_finite_def]
 "[|x~=UU; stream_finite(scons`x`xs)|] ==> stream_finite(xs)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(rtac exI 1),
	(etac (stream_take_lemma3 RS spec RS spec RS mp RS mp) 1),
	(atac 1)
	]);

qed_goal "stream_finite_lemma3" Stream.thy 
 "x~=UU ==> stream_finite(scons`x`xs) = stream_finite(xs)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac iffI 1),
	(etac stream_finite_lemma2 1),
	(atac 1),
	(etac stream_finite_lemma1 1)
	]);


qed_goalw "stream_finite_lemma5" Stream.thy [stream_finite_def]
 "(!n. s1 << s2  --> stream_take n`s2 = s2 --> stream_finite(s1))\
\=(s1 << s2  --> stream_finite(s2) --> stream_finite(s1))"
 (fn prems =>
	[
	(rtac iffI 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "stream_finite_lemma6" Stream.thy
 "!s1 s2. s1 << s2  --> stream_take n`s2 = s2 --> stream_finite(s1)"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1 ),
	(hyp_subst_tac  1),
	(dtac UU_I 1),
	(hyp_subst_tac  1),
	(rtac stream_finite_UU 1),
	(rtac allI 1),
	(rtac allI 1),
	(res_inst_tac [("s","s1")] streamE 1),
	(hyp_subst_tac  1),
	(strip_tac 1 ),
	(rtac stream_finite_UU 1),
	(hyp_subst_tac  1),
	(res_inst_tac [("s","s2")] streamE 1),
	(hyp_subst_tac  1),
	(strip_tac 1 ),
	(dtac UU_I 1),
	(asm_simp_tac(HOLCF_ss addsimps (stream_rews @ [stream_finite_UU])) 1),
	(hyp_subst_tac  1),
	(simp_tac (HOLCF_ss addsimps stream_rews) 1),
	(strip_tac 1 ),
	(rtac stream_finite_lemma1 1),
	(subgoal_tac "xs << xsa" 1),
	(subgoal_tac "stream_take n1`xsa = xsa" 1),
	(fast_tac HOL_cs 1),
	(res_inst_tac  [("x1.1","xa"),("y1.1","xa")] 
                   ((hd stream_inject) RS conjunct2) 1),
	(atac 1),
	(atac 1),
	(atac 1),
	(res_inst_tac [("x1.1","x"),("y1.1","xa")]
	 ((hd stream_invert) RS conjunct2) 1),
	(atac 1),
	(atac 1),
	(atac 1)
	]);

qed_goal "stream_finite_lemma7" Stream.thy 
"s1 << s2  --> stream_finite(s2) --> stream_finite(s1)"
 (fn prems =>
	[
	(rtac (stream_finite_lemma5 RS iffD1) 1),
	(rtac allI 1),
	(rtac (stream_finite_lemma6 RS spec RS spec) 1)
	]);

qed_goalw "stream_finite_lemma8" Stream.thy [stream_finite_def]
"stream_finite(s) = (? n. iterate n stl s = UU)"
 (fn prems =>
	[
	(simp_tac (HOL_ss addsimps [stream_take_lemma7]) 1)
	]);


(* ----------------------------------------------------------------------- *)
(* admissibility of ~stream_finite                                         *)
(* ----------------------------------------------------------------------- *)

qed_goalw "adm_not_stream_finite" Stream.thy [adm_def]
 "adm(%s. ~ stream_finite(s))"
 (fn prems =>
	[
	(strip_tac 1 ),
	(res_inst_tac [("P1","!i. ~ stream_finite(Y(i))")] classical3 1),
	(atac 2),
	(subgoal_tac "!i.stream_finite(Y(i))" 1),
	(fast_tac HOL_cs 1),
	(rtac allI 1),
	(rtac (stream_finite_lemma7 RS mp RS mp) 1),
	(etac is_ub_thelub 1),
	(atac 1)
	]);

(* ----------------------------------------------------------------------- *)
(* alternative prove for admissibility of ~stream_finite                   *)
(* show that stream_finite(s) = (? n. iterate n stl s = UU)                *)
(* and prove adm. of ~(? n. iterate n stl s = UU)                          *)
(* proof uses theorems stream_take_lemma5-7; stream_finite_lemma8          *)
(* ----------------------------------------------------------------------- *)


qed_goal "adm_not_stream_finite" Stream.thy "adm(%s. ~ stream_finite(s))"
 (fn prems =>
	[
	(subgoal_tac "(!s.(~stream_finite(s))=(!n.iterate n stl s ~=UU))" 1),
	(etac (adm_cong RS iffD2)1),
	(REPEAT(resolve_tac adm_thms 1)),
	(rtac  cont_iterate2 1),
	(rtac allI 1),
	(rtac (stream_finite_lemma8 RS ssubst) 1),
	(fast_tac HOL_cs 1)
	]);



(*  Title: 	FOCUS/Stream.ML
    ID:         $ $
    Author: 	Franz Regensburger, David von Oheimb
    Copyright   1993, 1995 Technische Universitaet Muenchen

Theorems for Stream.thy
*)

open Stream;

fun stream_case_tac s i = res_inst_tac [("x",s)] stream.cases i
			  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1);


(* ----------------------------------------------------------------------- *)
(* theorems about scons                                                    *)
(* ----------------------------------------------------------------------- *)

section "scons";

qed_goal "scons_eq_UU" thy "a && s = UU = (a = UU)" (fn _ => [
	safe_tac HOL_cs,
	etac contrapos2 1,
	safe_tac (HOL_cs addSIs stream.con_rews)]);

qed_goal "scons_not_empty" thy "[| a && x = UU; a ~= UU |] ==> R" (fn prems => [
	cut_facts_tac prems 1,
	dresolve_tac stream.con_rews 1,
	contr_tac 1]);

qed_goal "stream_exhaust_eq" thy "x ~= UU = (? a y. a ~= UU &  x = a && y)" (fn _ =>[
	cut_facts_tac [stream.exhaust] 1,
	safe_tac HOL_cs,
	   contr_tac 1,
	  fast_tac (HOL_cs addDs (tl stream.con_rews)) 1,
	 fast_tac HOL_cs 1,
	fast_tac (HOL_cs addDs (tl stream.con_rews)) 1]);

qed_goal "stream_prefix" thy 
"[| a && s << t; a ~= UU  |] ==> ? b tt. t = b && tt &  b ~= UU &  s << tt" (fn prems => [
	cut_facts_tac prems 1,
	stream_case_tac "t" 1,
	 fast_tac (HOL_cs addDs [eq_UU_iff RS iffD2,hd (tl stream.con_rews)]) 1,
	fast_tac (HOL_cs addDs stream.inverts) 1]);

qed_goal "stream_flat_prefix" thy 
"[| x && xs << y && ys; (x::'a) ~= UU; flat (z::'a) |] ==> x = y &  xs << ys"(fn prems=>[
	cut_facts_tac prems 1,
	(forward_tac stream.inverts 1),
	(safe_tac HOL_cs),
	(dtac (hd stream.con_rews RS subst) 1),
	(fast_tac (HOL_cs addDs ((eq_UU_iff RS iffD2)::stream.con_rews)) 1),
	(rewtac flat_def),
	(fast_tac HOL_cs 1)]);

qed_goal "stream_prefix'" thy "b ~= UU ==> x << b && z = \
\(x = UU |  (? a y. x = a && y &  a ~= UU &  a << b &  y << z))" (fn prems => [
	cut_facts_tac prems 1,
	safe_tac HOL_cs,
	  stream_case_tac "x" 1,
	   safe_tac (HOL_cs addSDs stream.inverts 
			    addSIs [minimal, monofun_cfun, monofun_cfun_arg]),
	fast_tac HOL_cs 1]);

qed_goal "stream_inject_eq" thy
 "[| a ~= UU; b ~= UU |] ==> (a && s = b && t) = (a = b &  s = t)" (fn prems => [
	cut_facts_tac prems 1,
	safe_tac (HOL_cs addSEs stream.injects)]);	


(* ----------------------------------------------------------------------- *)
(* theorems about stream_when                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_when";

qed_goal "stream_when_strictf" thy "stream_when`UU`s=UU" (fn _ => [
	stream_case_tac "s" 1,
	ALLGOALS(asm_simp_tac (HOL_ss addsimps strict_fapp1::stream.when_rews))
	]);
	

(* ----------------------------------------------------------------------- *)
(* theorems about ft and rt                                                *)
(* ----------------------------------------------------------------------- *)

section "ft & rt";

(*
qed_goal "stream_ft_lemma1" thy "ft`s=UU --> s=UU" (fn prems => [
	stream_case_tac "s" 1,
	REPEAT (asm_simp_tac (HOLCF_ss addsimps stream.rews) 1)]);
*)

qed_goal "ft_defin" thy "s~=UU ==> ft`s~=UU" (fn prems => [
	cut_facts_tac prems 1,
	stream_case_tac "s" 1,
	fast_tac HOL_cs 1,
	asm_simp_tac (HOLCF_ss addsimps stream.rews) 1]);

qed_goal "rt_strict_rev" thy "rt`s~=UU ==> s~=UU" (fn prems => [
	cut_facts_tac prems 1,
	etac contrapos 1,
	asm_simp_tac (HOLCF_ss addsimps stream.sel_rews) 1]);

qed_goal "surjectiv_scons" thy "(ft`s)&&(rt`s)=s"
 (fn prems =>
	[
	stream_case_tac "s" 1,
	REPEAT (asm_simp_tac (HOLCF_ss addsimps stream.rews) 1)
	]);

qed_goal_spec_mp "monofun_rt_mult" thy 
"!x s. x << s --> iterate i rt x << iterate i rt s" (fn _ => [
	nat_ind_tac "i" 1,
	simp_tac (HOLCF_ss addsimps stream.take_rews) 1,
	strip_tac 1,
	stream_case_tac "x" 1,
	rtac (minimal RS (monofun_iterate2 RS monofunE RS spec RS spec RS mp))1,
	dtac stream_prefix 1,
	 safe_tac HOL_cs,
	asm_simp_tac (HOL_ss addsimps iterate_Suc2::stream.rews) 1]);
			

(* ----------------------------------------------------------------------- *)
(* theorems about stream_take                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_take";

qed_goal "stream_reach2" thy  "(LUB i. stream_take i`s) = s"
 (fn prems =>
	[
	(res_inst_tac [("t","s")] (stream.reach RS subst) 1),
	(stac fix_def2 1),
	(rewrite_goals_tac [stream.take_def]),
	(stac contlub_cfun_fun 1),
	(rtac is_chain_iterate 1),
	(rtac refl 1)
	]);

qed_goal "chain_stream_take" thy "is_chain (%i.stream_take i`s)" (fn _ => [
	rtac is_chainI 1,
	subgoal_tac "!i s. stream_take i`s << stream_take (Suc i)`s" 1,
	fast_tac HOL_cs 1,
	rtac allI 1,
	nat_ind_tac "i" 1,
	 simp_tac (HOLCF_ss addsimps stream.take_rews) 1,
	rtac allI 1,
	stream_case_tac "s" 1,
	 simp_tac (HOLCF_ss addsimps stream.take_rews) 1,
	asm_simp_tac (HOLCF_ss addsimps monofun_cfun_arg::stream.take_rews) 1]);

qed_goalw "stream_take_more" thy [stream.take_def] 
	"stream_take n`x = x ==> stream_take (Suc n)`x = x" (fn prems => [
		cut_facts_tac prems 1,
		rtac antisym_less 1,
		rtac (stream.reach RS subst) 1, (* 1*back(); *)
		rtac monofun_cfun_fun 1,
		stac fix_def2 1,
		rtac is_ub_thelub 1,
		rtac is_chain_iterate 1,
		etac subst 1, (* 2*back(); *)
		rtac monofun_cfun_fun 1,
		rtac (rewrite_rule [is_chain] is_chain_iterate RS spec) 1]);

(*
val stream_take_lemma2 = prove_goal thy 
 "! s2. stream_take n`s2 = s2 --> stream_take (Suc n)`s2=s2" (fn prems => [
	(nat_ind_tac "n" 1),
	(simp_tac (!simpset addsimps stream_rews) 1),
	(strip_tac 1),
	(hyp_subst_tac  1),
	(simp_tac (!simpset addsimps stream_rews) 1),
	(rtac allI 1),
	(res_inst_tac [("s","s2")] streamE 1),
	(asm_simp_tac (!simpset addsimps stream_rews) 1),
	(asm_simp_tac (!simpset addsimps stream_rews) 1),
	(strip_tac 1 ),
	(subgoal_tac "stream_take n1`xs = xs" 1),
	(rtac ((hd stream_inject) RS conjunct2) 2),
	(atac 4),
	(atac 2),
	(atac 2),
	(rtac cfun_arg_cong 1),
	(fast_tac HOL_cs 1)
	]);
*)

val stream_take_lemma3 = prove_goal thy 
 "!x xs.x~=UU --> stream_take n`(x && xs) = x && xs --> stream_take n`xs=xs"
 (fn prems => [
	(nat_ind_tac "n" 1),
	(asm_simp_tac (HOL_ss addsimps stream.take_rews) 1),
	(strip_tac 1),
	(res_inst_tac [("P","x && xs=UU")] notE 1),
	(eresolve_tac stream.con_rews 1),
	(etac sym 1),
	(strip_tac 1),
	(rtac stream_take_more 1),
	(res_inst_tac [("a1","x")] ((hd stream.injects) RS conjunct2) 1),
	(etac (hd(tl(tl(stream.take_rews))) RS subst) 1),
	(atac 1),
	(atac 1)]) RS spec RS spec RS mp RS mp;

val stream_take_lemma4 = prove_goal thy 
 "!x xs. stream_take n`xs=xs --> stream_take (Suc n)`(x && xs) = x && xs"
 (fn _ => [
	(nat_ind_tac "n" 1),
	(simp_tac (HOL_ss addsimps stream.take_rews) 1),
	(simp_tac (HOL_ss addsimps stream.take_rews) 1)
	]) RS spec RS spec RS mp;


(* ------------------------------------------------------------------------- *)
(* special induction rules                                                   *)
(* ------------------------------------------------------------------------- *)

section "induction";

qed_goalw "stream_finite_ind" thy [stream.finite_def] 
 "[| stream_finite x; P UU; !!a s. [| a ~= UU; P s |] ==> P (a && s) |] ==> P x" 
 (fn prems => [
	(cut_facts_tac prems 1),
	(etac exE 1),
	(etac subst 1),
	(rtac stream.finite_ind 1),
	(atac 1),
	(eresolve_tac prems 1),
	(atac 1)]);

qed_goal "stream_finite_ind2" thy
"[| P UU;\
\   !! x    .    x ~= UU                  ==> P (x      && UU); \
\   !! y z s. [| y ~= UU; z ~= UU; P s |] ==> P (y && z && s )  \
\   |] ==> !s. P (stream_take n`s)" (fn prems => [
	res_inst_tac [("n","n")] nat_induct2 1,
	  asm_simp_tac (HOL_ss addsimps (hd prems)::stream.take_rews) 1,
	 rtac allI 1,
	 stream_case_tac "s" 1,
	  asm_simp_tac (HOL_ss addsimps (hd prems)::stream.take_rews) 1,
	 asm_simp_tac (HOL_ss addsimps stream.take_rews addsimps prems) 1,
	rtac allI 1,
	stream_case_tac "s" 1,
	 asm_simp_tac (HOL_ss addsimps (hd prems)::stream.take_rews) 1,
	res_inst_tac [("x","sa")] stream.cases 1,
	 asm_simp_tac (HOL_ss addsimps stream.take_rews addsimps prems) 1,
	asm_simp_tac (HOL_ss addsimps stream.take_rews addsimps prems) 1]);


qed_goal "stream_ind2" thy
"[| adm P; P UU; !!a. a ~= UU ==> P (a && UU); \
\   !!a b s. [| a ~= UU; b ~= UU; P s |] ==> P (a && b && s)\
\ |] ==> P x" (fn prems => [
	rtac (stream.reach RS subst) 1,
	rtac (adm_impl_admw RS wfix_ind) 1,
	rtac adm_subst 1,
	cont_tacR 1,
	resolve_tac prems 1,
	rtac allI 1,
	rtac (rewrite_rule [stream.take_def] stream_finite_ind2 RS spec) 1,
	resolve_tac prems 1,
	eresolve_tac prems 1,
	eresolve_tac prems 1, atac 1, atac 1]);


(* ----------------------------------------------------------------------- *)
(* simplify use of coinduction                                             *)
(* ----------------------------------------------------------------------- *)

section "coinduction";

qed_goalw "stream_coind_lemma2" thy [stream.bisim_def]
"!s1 s2. R s1 s2 --> ft`s1 = ft`s2 &  R (rt`s1) (rt`s2) ==> stream_bisim R"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(etac allE 1),
	(etac allE 1),
	(dtac mp 1),
	(atac 1),
	(etac conjE 1),
	(case_tac "x = UU & x' = UU" 1),
	(rtac disjI1 1),
	(fast_tac HOL_cs 1),
	(rtac disjI2 1),
	(rtac disjE 1),
	(etac (de_Morgan_conj RS subst) 1),
	(res_inst_tac [("x","ft`x")] exI 1),
	(res_inst_tac [("x","rt`x")] exI 1),
	(res_inst_tac [("x","rt`x'")] exI 1),
	(rtac conjI 1),
	(etac ft_defin 1),
	(asm_simp_tac (HOLCF_ss addsimps stream.rews addsimps [surjectiv_scons]) 1),
	(eres_inst_tac [("s","ft`x"),("t","ft`x'")] subst 1),
	(simp_tac (HOLCF_ss addsimps stream.rews addsimps [surjectiv_scons]) 1),
	(res_inst_tac [("x","ft`x'")] exI 1),
	(res_inst_tac [("x","rt`x")] exI 1),
	(res_inst_tac [("x","rt`x'")] exI 1),
	(rtac conjI 1),
	(etac ft_defin 1),
	(asm_simp_tac (HOLCF_ss addsimps stream.rews addsimps [surjectiv_scons]) 1),
	(res_inst_tac [("s","ft`x"),("t","ft`x'")] ssubst 1),
	(etac sym 1),
	(simp_tac (HOLCF_ss addsimps stream.rews addsimps [surjectiv_scons]) 1)
	]);

(* ----------------------------------------------------------------------- *)
(* theorems about stream_finite                                            *)
(* ----------------------------------------------------------------------- *)

section "stream_finite";

qed_goalw "stream_finite_UU" thy [stream.finite_def] "stream_finite UU" 
	(fn prems => [
	(rtac exI 1),
	(simp_tac (HOLCF_ss addsimps stream.rews) 1)]);

qed_goal "stream_finite_UU_rev" thy  "~  stream_finite s ==> s ~= UU"  (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac contrapos 1),
	(hyp_subst_tac  1),
	(rtac stream_finite_UU 1)
	]);

qed_goalw "stream_finite_lemma1" thy [stream.finite_def]
 "stream_finite xs ==> stream_finite (x && xs)" (fn prems => [
	(cut_facts_tac prems 1),
	(etac exE 1),
	(rtac exI 1),
	(etac stream_take_lemma4 1)
	]);

qed_goalw "stream_finite_lemma2" thy [stream.finite_def]
 "[| x ~= UU; stream_finite (x && xs) |] ==> stream_finite xs" (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(rtac exI 1),
	(etac stream_take_lemma3 1),
	(atac 1)
	]);

qed_goal "stream_finite_rt_eq" thy "stream_finite (rt`s) = stream_finite s"
	(fn _ => [
	stream_case_tac "s" 1,
	 simp_tac (HOL_ss addsimps stream_finite_UU::stream.sel_rews) 1,
	asm_simp_tac (HOL_ss addsimps stream.sel_rews) 1,
	fast_tac (HOL_cs addIs [stream_finite_lemma1] 
			 addDs [stream_finite_lemma2]) 1]);

qed_goal_spec_mp "stream_finite_less" thy 
 "stream_finite s ==> !t. t<<s --> stream_finite t" (fn prems => [
	cut_facts_tac prems 1,
	eres_inst_tac [("x","s")] stream_finite_ind 1,
	 strip_tac 1, dtac UU_I 1,
	 asm_simp_tac (HOLCF_ss addsimps [stream_finite_UU]) 1,
	strip_tac 1,
	asm_full_simp_tac (HOL_ss addsimps [stream_prefix']) 1,
	fast_tac (HOL_cs addSIs [stream_finite_UU, stream_finite_lemma1]) 1]);

qed_goal "adm_not_stream_finite" thy "adm (%x. ~  stream_finite x)" (fn _ => [
	rtac admI 1,
	dtac spec 1,
	etac contrapos 1,
	dtac stream_finite_less 1,
	 etac is_ub_thelub 1,
	atac 1]);

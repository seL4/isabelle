(*  Title: 	HOLCF/sprod3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Sprod3.thy 
*)

open Sprod3;

(* ------------------------------------------------------------------------ *)
(* continuity of Ispair, Isfst, Issnd                                       *)
(* ------------------------------------------------------------------------ *)

val sprod3_lemma1 = prove_goal Sprod3.thy 
"[| is_chain(Y);  x~= UU;  lub(range(Y))~= UU |] ==>\
\ Ispair(lub(range(Y)),x) =\
\ Ispair(lub(range(%i. Isfst(Ispair(Y(i),x)))),\
\        lub(range(%i. Issnd(Ispair(Y(i),x)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("f1","Ispair")] (arg_cong RS cong) 1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_Isfst RS ch2ch_monofun) 1),
	(rtac ch2ch_fun 1),
	(rtac (monofun_Ispair1 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac allI 1),
	(asm_simp_tac Sprod_ss 1),
	(rtac sym 1),
	(rtac lub_chain_maxelem 1),
	(rtac (monofun_Issnd RS ch2ch_monofun) 1),
	(rtac ch2ch_fun 1),
	(rtac (monofun_Ispair1 RS ch2ch_monofun) 1),
	(atac 1),
	(res_inst_tac [("P","%j.~Y(j)=UU")] exE 1),
	(rtac (notall2ex RS iffD1) 1),
	(res_inst_tac [("Q","lub(range(Y)) = UU")] contrapos 1),
	(atac 1),
	(rtac chain_UU_I_inverse 1),
	(atac 1),
	(rtac exI 1),
	(etac Issnd2 1),
	(rtac allI 1),
	(res_inst_tac [("Q","Y(i)=UU")] (excluded_middle RS disjE) 1),
	(asm_simp_tac Sprod_ss  1),
	(rtac refl_less 1),
	(res_inst_tac [("s","UU"),("t","Y(i)")] subst 1),
	(etac sym 1),
	(asm_simp_tac Sprod_ss  1),
	(rtac minimal 1)
	]);


val sprod3_lemma2 = prove_goal Sprod3.thy 
"[| is_chain(Y); ~ x = UU; lub(range(Y)) = UU |] ==>\
\   Ispair(lub(range(Y)),x) =\
\   Ispair(lub(range(%i. Isfst(Ispair(Y(i),x)))),\
\          lub(range(%i. Issnd(Ispair(Y(i),x)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac strict_Ispair1 1),
	(rtac (strict_Ispair RS sym) 1),
	(rtac disjI1 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(asm_simp_tac Sprod_ss  1),
	(etac (chain_UU_I RS spec) 1),
	(atac 1)
	]);


val sprod3_lemma3 = prove_goal Sprod3.thy 
"[| is_chain(Y); x = UU |] ==>\
\          Ispair(lub(range(Y)),x) =\
\          Ispair(lub(range(%i. Isfst(Ispair(Y(i),x)))),\
\                  lub(range(%i. Issnd(Ispair(Y(i),x)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("s","UU"),("t","x")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac strict_Ispair2 1),
	(rtac (strict_Ispair RS sym) 1),
	(rtac disjI1 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(simp_tac Sprod_ss  1)
	]);


val contlub_Ispair1 = prove_goal Sprod3.thy "contlub(Ispair)"
(fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(rtac (lub_fun RS thelubI RS ssubst) 1),
	(etac (monofun_Ispair1 RS ch2ch_monofun) 1),
	(rtac trans 1),
	(rtac (thelub_sprod RS sym) 2),
	(rtac ch2ch_fun 2),
	(etac (monofun_Ispair1 RS ch2ch_monofun) 2),
	(res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
	(res_inst_tac 
		[("Q","lub(range(Y))=UU")] (excluded_middle RS disjE) 1),
	(etac sprod3_lemma1 1),
	(atac 1),
	(atac 1),
	(etac sprod3_lemma2 1),
	(atac 1),
	(atac 1),
	(etac sprod3_lemma3 1),
	(atac 1)
	]);

val sprod3_lemma4 = prove_goal Sprod3.thy 
"[| is_chain(Y); ~ x = UU; ~ lub(range(Y)) = UU |] ==>\
\         Ispair(x,lub(range(Y))) =\
\         Ispair(lub(range(%i. Isfst(Ispair(x,Y(i))))),\
\                lub(range(%i. Issnd(Ispair(x,Y(i))))))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("f1","Ispair")] (arg_cong RS cong) 1),
	(rtac sym 1),
	(rtac lub_chain_maxelem 1),
	(rtac (monofun_Isfst RS ch2ch_monofun) 1),
	(rtac (monofun_Ispair2 RS ch2ch_monofun) 1),
	(atac 1),
	(res_inst_tac [("P","%j.~Y(j)=UU")] exE 1),
	(rtac (notall2ex RS iffD1) 1),
	(res_inst_tac [("Q","lub(range(Y)) = UU")] contrapos 1),
	(atac 1),
	(rtac chain_UU_I_inverse 1),
	(atac 1),
	(rtac exI 1),
	(etac Isfst2 1),
	(rtac allI 1),
	(res_inst_tac [("Q","Y(i)=UU")] (excluded_middle RS disjE) 1),
	(asm_simp_tac Sprod_ss 1),
	(rtac refl_less 1),
	(res_inst_tac [("s","UU"),("t","Y(i)")] subst 1),
	(etac sym 1),
	(asm_simp_tac Sprod_ss  1),
	(rtac minimal 1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_Issnd RS ch2ch_monofun) 1),
	(rtac (monofun_Ispair2 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac allI 1),
	(asm_simp_tac Sprod_ss 1)
	]);

val sprod3_lemma5 = prove_goal Sprod3.thy 
"[| is_chain(Y); ~ x = UU; lub(range(Y)) = UU |] ==>\
\         Ispair(x,lub(range(Y))) =\
\         Ispair(lub(range(%i. Isfst(Ispair(x,Y(i))))),\
\                lub(range(%i. Issnd(Ispair(x,Y(i))))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac strict_Ispair2 1),
	(rtac (strict_Ispair RS sym) 1),
	(rtac disjI2 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(asm_simp_tac Sprod_ss  1),
	(etac (chain_UU_I RS spec) 1),
	(atac 1)
	]);

val sprod3_lemma6 = prove_goal Sprod3.thy 
"[| is_chain(Y); x = UU |] ==>\
\         Ispair(x,lub(range(Y))) =\
\         Ispair(lub(range(%i. Isfst(Ispair(x,Y(i))))),\
\                lub(range(%i. Issnd(Ispair(x,Y(i))))))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("s","UU"),("t","x")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac strict_Ispair1 1),
	(rtac (strict_Ispair RS sym) 1),
	(rtac disjI1 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(simp_tac Sprod_ss  1)
	]);

val contlub_Ispair2 = prove_goal Sprod3.thy "contlub(Ispair(x))"
(fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_sprod RS sym) 2),
	(etac (monofun_Ispair2 RS ch2ch_monofun) 2),
	(res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
	(res_inst_tac [("Q","lub(range(Y))=UU")] 
		(excluded_middle RS disjE) 1),
	(etac sprod3_lemma4 1),
	(atac 1),
	(atac 1),
	(etac sprod3_lemma5 1),
	(atac 1),
	(atac 1),
	(etac sprod3_lemma6 1),
	(atac 1)
	]);


val contX_Ispair1 = prove_goal Sprod3.thy "contX(Ispair)"
(fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Ispair1 1),
	(rtac contlub_Ispair1 1)
	]);


val contX_Ispair2 = prove_goal Sprod3.thy "contX(Ispair(x))"
(fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Ispair2 1),
	(rtac contlub_Ispair2 1)
	]);

val contlub_Isfst = prove_goal Sprod3.thy "contlub(Isfst)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (lub_sprod RS thelubI RS ssubst) 1),
	(atac 1),
	(res_inst_tac [("Q","lub(range(%i. Issnd(Y(i))))=UU")]	
		(excluded_middle RS disjE) 1),
	(asm_simp_tac Sprod_ss  1),
	(res_inst_tac [("s","UU"),("t","lub(range(%i. Issnd(Y(i))))")]
		ssubst 1),
	(atac 1),
	(rtac trans 1),
	(asm_simp_tac Sprod_ss  1),
	(rtac sym 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(rtac strict_Isfst 1),
	(rtac swap 1),
	(etac (defined_IsfstIssnd RS conjunct2) 2),
	(rtac notnotI 1),
	(rtac (chain_UU_I RS spec) 1),
	(rtac (monofun_Issnd RS ch2ch_monofun) 1),
	(atac 1),
	(atac 1)
	]);


val contlub_Issnd = prove_goal Sprod3.thy "contlub(Issnd)"
(fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (lub_sprod RS thelubI RS ssubst) 1),
	(atac 1),
	(res_inst_tac [("Q","lub(range(%i. Isfst(Y(i))))=UU")]
	 (excluded_middle RS disjE) 1),
	(asm_simp_tac Sprod_ss  1),
	(res_inst_tac [("s","UU"),("t","lub(range(%i. Isfst(Y(i))))")] 
		ssubst 1),
	(atac 1),
	(asm_simp_tac Sprod_ss  1),
	(rtac sym 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(rtac strict_Issnd 1),
	(rtac swap 1),
	(etac (defined_IsfstIssnd RS conjunct1) 2),
	(rtac notnotI 1),
	(rtac (chain_UU_I RS spec) 1),
	(rtac (monofun_Isfst RS ch2ch_monofun) 1),
	(atac 1),
	(atac 1)
	]);


val contX_Isfst = prove_goal Sprod3.thy "contX(Isfst)"
(fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Isfst 1),
	(rtac contlub_Isfst 1)
	]);

val contX_Issnd = prove_goal Sprod3.thy "contX(Issnd)"
(fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Issnd 1),
	(rtac contlub_Issnd 1)
	]);

(* 
 -------------------------------------------------------------------------- 
 more lemmas for Sprod3.thy 
 
 -------------------------------------------------------------------------- 
*)

val spair_eq = prove_goal Sprod3.thy "[|x1=x2;y1=y2|] ==> x1##y1 = x2##y2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

val beta_cfun_sprod = prove_goalw Sprod3.thy [spair_def]
	"(LAM x y.Ispair(x,y))[a][b] = Ispair(a,b)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tac 1),
	(rtac contX_Ispair2 1),
	(rtac contX2contX_CF1L 1),
	(rtac contX_Ispair1 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Ispair2 1),
	(rtac refl 1)
	]);

val inject_spair = prove_goalw Sprod3.thy [spair_def]
	"[|~aa=UU ; ~ba=UU ; (a##b)=(aa##ba) |] ==> a=aa & b=ba"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac inject_Ispair 1),
	(atac 1),
	(etac box_equals 1),
	(rtac beta_cfun_sprod 1),
	(rtac beta_cfun_sprod 1)
	]);

val inst_sprod_pcpo2 = prove_goalw Sprod3.thy [spair_def] "UU = (UU##UU)"
 (fn prems =>
	[
	(rtac sym 1),
	(rtac trans 1),
	(rtac beta_cfun_sprod 1),
	(rtac sym 1),
	(rtac inst_sprod_pcpo 1)
	]);

val strict_spair = prove_goalw Sprod3.thy [spair_def] 
	"(a=UU | b=UU) ==> (a##b)=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(rtac beta_cfun_sprod 1),
	(rtac trans 1),
	(rtac (inst_sprod_pcpo RS sym) 2),
	(etac strict_Ispair 1)
	]);

val strict_spair1 = prove_goalw Sprod3.thy [spair_def] "(UU##b) = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac trans 1),
	(rtac (inst_sprod_pcpo RS sym) 2),
	(rtac strict_Ispair1 1)
	]);

val strict_spair2 = prove_goalw Sprod3.thy [spair_def] "(a##UU) = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac trans 1),
	(rtac (inst_sprod_pcpo RS sym) 2),
	(rtac strict_Ispair2 1)
	]);

val strict_spair_rev = prove_goalw Sprod3.thy [spair_def]
	"~(x##y)=UU ==> ~x=UU & ~y=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac strict_Ispair_rev 1),
	(rtac (beta_cfun_sprod RS subst) 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);

val defined_spair_rev = prove_goalw Sprod3.thy [spair_def]
 "(a##b) = UU ==> (a = UU | b = UU)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac defined_Ispair_rev 1),
	(rtac (beta_cfun_sprod RS subst) 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);

val defined_spair = prove_goalw Sprod3.thy [spair_def]
	"[|~a=UU; ~b=UU|] ==> ~(a##b) = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (inst_sprod_pcpo RS ssubst) 1),
	(etac defined_Ispair 1),
	(atac 1)
	]);

val Exh_Sprod2 = prove_goalw Sprod3.thy [spair_def]
	"z=UU | (? a b. z=(a##b) & ~a=UU & ~b=UU)"
 (fn prems =>
	[
	(rtac (Exh_Sprod RS disjE) 1),
	(rtac disjI1 1),
	(rtac (inst_sprod_pcpo RS ssubst) 1),
	(atac 1),
	(rtac disjI2 1),
	(etac exE 1),
	(etac exE 1),
	(rtac exI 1),
	(rtac exI 1),
	(rtac conjI 1),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);


val sprodE =  prove_goalw Sprod3.thy [spair_def]
"[|p=UU ==> Q;!!x y. [|p=(x##y);~x=UU ; ~y=UU|] ==> Q|] ==> Q"
(fn prems =>
	[
	(rtac IsprodE 1),
	(resolve_tac prems 1),
	(rtac (inst_sprod_pcpo RS ssubst) 1),
	(atac 1),
	(resolve_tac prems 1),
	(atac 2),
	(atac 2),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(atac 1)
	]);


val strict_sfst = prove_goalw Sprod3.thy [sfst_def] 
	"p=UU==>sfst[p]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac strict_Isfst 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);

val strict_sfst1 = prove_goalw Sprod3.thy [sfst_def,spair_def] 
	"sfst[UU##y] = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac strict_Isfst1 1)
	]);
 
val strict_sfst2 = prove_goalw Sprod3.thy [sfst_def,spair_def] 
	"sfst[x##UU] = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac strict_Isfst2 1)
	]);

val strict_ssnd = prove_goalw Sprod3.thy [ssnd_def] 
	"p=UU==>ssnd[p]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac strict_Issnd 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);

val strict_ssnd1 = prove_goalw Sprod3.thy [ssnd_def,spair_def] 
	"ssnd[UU##y] = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac strict_Issnd1 1)
	]);

val strict_ssnd2 = prove_goalw Sprod3.thy [ssnd_def,spair_def] 
	"ssnd[x##UU] = UU"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac strict_Issnd2 1)
	]);

val sfst2 = prove_goalw Sprod3.thy [sfst_def,spair_def] 
	"~y=UU ==>sfst[x##y]=x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(etac Isfst2 1)
	]);

val ssnd2 = prove_goalw Sprod3.thy [ssnd_def,spair_def] 
	"~x=UU ==>ssnd[x##y]=y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(etac Issnd2 1)
	]);


val defined_sfstssnd = prove_goalw Sprod3.thy [sfst_def,ssnd_def,spair_def]
	"~p=UU ==> ~sfst[p]=UU & ~ssnd[p]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac defined_IsfstIssnd 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);
 

val surjective_pairing_Sprod2 = prove_goalw Sprod3.thy 
	[sfst_def,ssnd_def,spair_def] "(sfst[p] ## ssnd[p]) = p"
 (fn prems =>
	[
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac (surjective_pairing_Sprod RS sym) 1)
	]);


val less_sprod5b = prove_goalw Sprod3.thy [sfst_def,ssnd_def,spair_def]
 "~p1=UU ==> (p1<<p2) = (sfst[p1]<<sfst[p2] & ssnd[p1]<<ssnd[p2])"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac less_sprod3b 1),
	(rtac (inst_sprod_pcpo RS subst) 1),
	(atac 1)
	]);

 
val less_sprod5c = prove_goalw Sprod3.thy [sfst_def,ssnd_def,spair_def]
 "[|xa##ya<<x##y;~xa=UU;~ya=UU;~x=UU;~y=UU|] ==>xa<<x & ya << y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac less_sprod4c 1),
	(REPEAT (atac 2)),
	(rtac (beta_cfun_sprod RS subst) 1),
	(rtac (beta_cfun_sprod RS subst) 1),
	(atac 1)
	]);

val lub_sprod2 = prove_goalw Sprod3.thy [sfst_def,ssnd_def,spair_def]
"[|is_chain(S)|] ==> range(S) <<| \
\ (lub(range(%i.sfst[S(i)])) ## lub(range(%i.ssnd[S(i)])))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_sprod RS ssubst) 1),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(rtac contX_Issnd 1),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(rtac contX_Isfst 1),
	(rtac lub_sprod 1),
	(resolve_tac prems 1)
	]);


val thelub_sprod2 = (lub_sprod2 RS thelubI);
(* is_chain(?S1) ==> lub(range(?S1)) =                                    *) 
(*     (lub(range(%i. sfst[?S1(i)]))## lub(range(%i. ssnd[?S1(i)])))        *)



val ssplit1 = prove_goalw Sprod3.thy [ssplit_def]
	"ssplit[f][UU]=UU"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tacR 1),
	(rtac (strictify1 RS ssubst) 1),
	(rtac refl 1)
	]);

val ssplit2 = prove_goalw Sprod3.thy [ssplit_def]
	"[|~x=UU;~y=UU|] ==> ssplit[f][x##y]=f[x][y]"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tacR 1),
	(rtac (strictify2 RS ssubst) 1),
	(rtac defined_spair 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tacR 1),
	(rtac (sfst2 RS ssubst) 1),
	(resolve_tac prems 1),
	(rtac (ssnd2 RS ssubst) 1),
	(resolve_tac prems 1),
	(rtac refl 1)
	]);


val ssplit3 = prove_goalw Sprod3.thy [ssplit_def]
  "ssplit[spair][z]=z"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tacR 1),
	(res_inst_tac [("Q","z=UU")] classical2 1),
	(hyp_subst_tac 1),
	(rtac strictify1 1),
	(rtac trans 1),
	(rtac strictify2 1),
	(atac 1),
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tacR 1),
	(rtac surjective_pairing_Sprod2 1)
	]);


(* ------------------------------------------------------------------------ *)
(* install simplifier for Sprod                                             *)
(* ------------------------------------------------------------------------ *)

val Sprod_rews = [strict_spair1,strict_spair2,strict_sfst1,strict_sfst2,
		strict_ssnd1,strict_ssnd2,sfst2,ssnd2,
		ssplit1,ssplit2];

val Sprod_ss = Cfun_ss addsimps Sprod_rews;



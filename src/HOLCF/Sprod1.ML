(*  Title: 	HOLCF/sprod1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory sprod1.thy
*)

open Sprod1;

(* ------------------------------------------------------------------------ *)
(* reduction properties for less_sprod                                      *)
(* ------------------------------------------------------------------------ *)


qed_goalw "less_sprod1a" Sprod1.thy [less_sprod_def]
	"p1=Ispair UU UU ==> less_sprod p1 p2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(Asm_simp_tac 1)
	]);

qed_goalw "less_sprod1b" Sprod1.thy [less_sprod_def]
 "p1~=Ispair UU UU ==> \
\ less_sprod p1 p2 = ( Isfst p1 << Isfst p2 & Issnd p1 << Issnd p2)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(Asm_simp_tac 1)
	]);

qed_goal "less_sprod2a" Sprod1.thy
	"less_sprod(Ispair x y)(Ispair UU UU) ==> x = UU | y = UU"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (excluded_middle RS disjE) 1),
	(atac 2),
	(rtac disjI1 1),
	(rtac antisym_less 1),
	(rtac minimal 2),
	(res_inst_tac [("s","Isfst(Ispair x y)"),("t","x")] subst 1),
	(rtac Isfst 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1),
	(res_inst_tac [("s","Isfst(Ispair UU UU)"),("t","UU")] subst 1),
	(Simp_tac 1),
	(rtac (defined_Ispair RS less_sprod1b RS iffD1 RS conjunct1) 1),
	(REPEAT (fast_tac HOL_cs 1))
	]);

qed_goal "less_sprod2b" Sprod1.thy
 "less_sprod p (Ispair UU UU) ==> p = Ispair UU UU"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p")] IsprodE 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac strict_Ispair 1),
	(etac less_sprod2a 1)
	]);

qed_goal "less_sprod2c" Sprod1.thy 
 "[|less_sprod(Ispair xa ya)(Ispair x y);\
\  xa ~= UU ; ya ~= UU; x ~= UU ;  y ~= UU |] ==> xa << x & ya << y"
(fn prems =>
	[
	(rtac conjI 1),
	(res_inst_tac [("s","Isfst(Ispair xa ya)"),("t","xa")] subst 1),
	(simp_tac (!simpset addsimps prems)1),
	(res_inst_tac [("s","Isfst(Ispair x y)"),("t","x")] subst 1),
	(simp_tac (!simpset addsimps prems)1),
	(rtac (defined_Ispair RS less_sprod1b RS iffD1 RS conjunct1) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1),
	(simp_tac (!simpset addsimps prems)1),
	(res_inst_tac [("s","Issnd(Ispair xa ya)"),("t","ya")] subst 1),
	(simp_tac (!simpset addsimps prems)1),
	(res_inst_tac [("s","Issnd(Ispair x y)"),("t","y")] subst 1),
	(simp_tac (!simpset addsimps prems)1),
	(rtac (defined_Ispair RS less_sprod1b RS iffD1 RS conjunct2) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1),
	(simp_tac (!simpset addsimps prems)1)
	]);

(* ------------------------------------------------------------------------ *)
(* less_sprod is a partial order on Sprod                                   *)
(* ------------------------------------------------------------------------ *)

qed_goal "refl_less_sprod" Sprod1.thy "less_sprod p p"
(fn prems =>
	[
	(res_inst_tac [("p","p")] IsprodE 1),
	(etac less_sprod1a 1),
	(hyp_subst_tac 1),
	(rtac (less_sprod1b RS ssubst) 1),
	(rtac defined_Ispair 1),
	(REPEAT (fast_tac (HOL_cs addIs [refl_less]) 1))
	]);


qed_goal "antisym_less_sprod" Sprod1.thy 
 "[|less_sprod p1 p2;less_sprod p2 p1|] ==> p1=p2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] IsprodE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] IsprodE 1),
	(hyp_subst_tac 1),
	(rtac refl 1),
	(hyp_subst_tac 1),
	(rtac (strict_Ispair RS sym) 1),
	(etac less_sprod2a 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] IsprodE 1),
	(hyp_subst_tac 1),
	(rtac (strict_Ispair) 1),
	(etac less_sprod2a 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("x1","x"),("y1","xa"),("x","y"),("y","ya")] (arg_cong RS cong) 1),
	(rtac antisym_less 1),
	(asm_simp_tac (!simpset addsimps [less_sprod2c RS conjunct1]) 1),
	(asm_simp_tac (!simpset addsimps [less_sprod2c RS conjunct1]) 1),
	(rtac antisym_less 1),
	(asm_simp_tac (!simpset addsimps [less_sprod2c RS conjunct2]) 1),
	(asm_simp_tac (!simpset addsimps [less_sprod2c RS conjunct2]) 1)
	]);

qed_goal "trans_less_sprod" Sprod1.thy 
 "[|less_sprod (p1::'a**'b) p2;less_sprod p2 p3|] ==> less_sprod p1 p3"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] IsprodE 1),
	(etac less_sprod1a 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p3")] IsprodE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("s","p2"),("t","Ispair (UU::'a)(UU::'b)")] subst 1),
	(etac less_sprod2b 1),
	(atac 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("Q","p2=Ispair(UU::'a)(UU::'b)")]
		 (excluded_middle RS disjE) 1),
	(rtac (defined_Ispair RS less_sprod1b RS ssubst) 1),
	(REPEAT (atac 1)),
	(rtac conjI 1),
	(res_inst_tac [("y","Isfst(p2)")] trans_less 1),
	(rtac conjunct1 1),
	(rtac (less_sprod1b RS subst) 1),
	(rtac defined_Ispair 1),
	(REPEAT (atac 1)),
	(rtac conjunct1 1),
	(rtac (less_sprod1b RS subst) 1),
	(REPEAT (atac 1)),
	(res_inst_tac [("y","Issnd(p2)")] trans_less 1),
	(rtac conjunct2 1),
	(rtac (less_sprod1b RS subst) 1),
	(rtac defined_Ispair 1),
	(REPEAT (atac 1)),
	(rtac conjunct2 1),
	(rtac (less_sprod1b RS subst) 1),
	(REPEAT (atac 1)),
	(hyp_subst_tac 1),
	(res_inst_tac [("s","Ispair(UU::'a)(UU::'b)"),("t","Ispair x y")] 
		subst 1),
	(etac (less_sprod2b RS sym) 1),
	(atac 1)
	]);











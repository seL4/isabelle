(*  Title: 	LCF/fix
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1992  University of Cambridge

Fixedpoint theory
*)

signature FIX =
sig
  val adm_eq: thm
  val adm_not_eq_tr: thm
  val adm_not_not: thm
  val not_eq_TT: thm
  val not_eq_FF: thm
  val not_eq_UU: thm
  val induct2: thm
  val induct_tac: string -> int -> tactic
  val induct2_tac: string*string -> int -> tactic
end;

structure Fix:FIX =
struct

val adm_eq = prove_goal LCF.thy "adm(%x.t(x)=(u(x)::'a::cpo))"
	(fn _ => [rewrite_goals_tac [eq_def],
		  REPEAT(rstac[adm_conj,adm_less]1)]);

val adm_not_not = prove_goal LCF.thy "adm(P) ==> adm(%x.~~P(x))"
	(fn prems => [simp_tac (LCF_ss addsimps prems) 1]);


val tac = rtac tr_induct 1 THEN REPEAT(simp_tac LCF_ss 1);

val not_eq_TT = prove_goal LCF.thy "ALL p. ~p=TT <-> (p=FF | p=UU)"
    (fn _ => [tac]) RS spec;

val not_eq_FF = prove_goal LCF.thy "ALL p. ~p=FF <-> (p=TT | p=UU)"
    (fn _ => [tac]) RS spec;

val not_eq_UU = prove_goal LCF.thy "ALL p. ~p=UU <-> (p=TT | p=FF)"
    (fn _ => [tac]) RS spec;

val adm_not_eq_tr = prove_goal LCF.thy "ALL p::tr.adm(%x. ~t(x)=p)"
    (fn _ => [rtac tr_induct 1,
    REPEAT(simp_tac (LCF_ss addsimps [not_eq_TT,not_eq_FF,not_eq_UU]) 1 THEN
	   REPEAT(rstac [adm_disj,adm_eq] 1))]) RS spec;

val adm_lemmas = [adm_not_free,adm_eq,adm_less,adm_not_less,adm_not_eq_tr,
		  adm_conj,adm_disj,adm_imp,adm_all];

fun induct_tac v i = res_inst_tac[("f",v)] induct i THEN
		     REPEAT(rstac adm_lemmas i);


val least_FIX = prove_goal LCF.thy "f(p) = p ==> FIX(f) << p"
	(fn [prem] => [induct_tac "f" 1, rtac minimal 1, strip_tac 1,
			stac (prem RS sym) 1, etac less_ap_term 1]);

val lfp_is_FIX = prove_goal LCF.thy
	"[| f(p) = p; ALL q. f(q)=q --> p << q |] ==> p = FIX(f)"
	(fn [prem1,prem2] => [rtac less_anti_sym 1,
			      rtac (prem2 RS spec RS mp) 1, rtac FIX_eq 1,
			      rtac least_FIX 1, rtac prem1 1]);

val ffix = read_instantiate [("f","f::?'a=>?'a")] FIX_eq;
val gfix = read_instantiate [("f","g::?'a=>?'a")] FIX_eq;
val ss = LCF_ss addsimps [ffix,gfix];

val FIX_pair = prove_goal LCF.thy
  "<FIX(f),FIX(g)> = FIX(%p.<f(FST(p)),g(SND(p))>)"
  (fn _ => [rtac lfp_is_FIX 1, simp_tac ss 1,
	  strip_tac 1, simp_tac (LCF_ss addsimps [PROD_less]) 1,
	  rtac conjI 1, rtac least_FIX 1, etac subst 1, rtac (FST RS sym) 1,
	  rtac least_FIX 1, etac subst 1, rtac (SND RS sym) 1]);

val FIX_pair_conj = rewrite_rule (map mk_meta_eq [PROD_eq,FST,SND]) FIX_pair;

val FIX1 = FIX_pair_conj RS conjunct1;
val FIX2 = FIX_pair_conj RS conjunct2;

val induct2 = prove_goal LCF.thy
	 "[| adm(%p.P(FST(p),SND(p))); P(UU::'a,UU::'b);\
\	     ALL x y. P(x,y) --> P(f(x),g(y)) |] ==> P(FIX(f),FIX(g))"
	(fn prems => [EVERY1
	[res_inst_tac [("f","f"),("g","g")] (standard(FIX1 RS ssubst)),
	 res_inst_tac [("f","f"),("g","g")] (standard(FIX2 RS ssubst)),
	 res_inst_tac [("f","%x. <f(FST(x)),g(SND(x))>")] induct,
	 rstac prems, simp_tac ss, rstac prems,
	 simp_tac (LCF_ss addsimps [expand_all_PROD]), rstac prems]]);

fun induct2_tac (f,g) i = res_inst_tac[("f",f),("g",g)] induct2 i THEN
		     REPEAT(rstac adm_lemmas i);

end;

open Fix;

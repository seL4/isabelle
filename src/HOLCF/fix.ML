(*  Title: 	HOLCF/fix.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for fix.thy 
*)

open Fix;

(* ------------------------------------------------------------------------ *)
(* derive inductive properties of iterate from primitive recursion          *)
(* ------------------------------------------------------------------------ *)

val iterate_0 = prove_goal Fix.thy "iterate(0,F,x) = x"
 (fn prems =>
	[
	(resolve_tac (nat_recs iterate_def) 1)
	]);

val iterate_Suc = prove_goal Fix.thy "iterate(Suc(n),F,x) = F[iterate(n,F,x)]"
 (fn prems =>
	[
	(resolve_tac (nat_recs iterate_def) 1)
	]);

val iterate_ss = Cfun_ss addsimps [iterate_0,iterate_Suc];

val iterate_Suc2 = prove_goal Fix.thy "iterate(Suc(n),F,x) = iterate(n,F,F[x])"
 (fn prems =>
	[
	(nat_ind_tac "n" 1),
	(simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1)
	]);

(* ------------------------------------------------------------------------ *)
(* the sequence of function itertaions is a chain                           *)
(* This property is essential since monotonicity of iterate makes no sense  *)
(* ------------------------------------------------------------------------ *)

val is_chain_iterate2 = prove_goalw Fix.thy [is_chain] 
	" x << F[x] ==> is_chain(%i.iterate(i,F,x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(simp_tac iterate_ss 1),
	(nat_ind_tac "i" 1),
	(asm_simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1),
	(etac monofun_cfun_arg 1)
	]);


val is_chain_iterate = prove_goal Fix.thy  
	"is_chain(%i.iterate(i,F,UU))"
 (fn prems =>
	[
	(rtac is_chain_iterate2 1),
	(rtac minimal 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Kleene's fixed point theorems for continuous functions in pointed        *)
(* omega cpo's                                                              *)
(* ------------------------------------------------------------------------ *)


val Ifix_eq = prove_goalw Fix.thy  [Ifix_def] "Ifix(F)=F[Ifix(F)]"
 (fn prems =>
	[
	(rtac (contlub_cfun_arg RS ssubst) 1),
	(rtac is_chain_iterate 1),
	(rtac antisym_less 1),
	(rtac lub_mono 1),
	(rtac is_chain_iterate 1),
	(rtac ch2ch_fappR 1),
	(rtac is_chain_iterate 1),
	(rtac allI 1),
	(rtac (iterate_Suc RS subst) 1),
	(rtac (is_chain_iterate RS is_chainE RS spec) 1),
	(rtac is_lub_thelub 1),
	(rtac ch2ch_fappR 1),
	(rtac is_chain_iterate 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(rtac (iterate_Suc RS subst) 1),
	(rtac is_ub_thelub 1),
	(rtac is_chain_iterate 1)
	]);


val Ifix_least = prove_goalw Fix.thy [Ifix_def] "F[x]=x ==> Ifix(F) << x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lub_thelub 1),
	(rtac is_chain_iterate 1),
	(rtac ub_rangeI 1),
	(strip_tac 1),
	(nat_ind_tac "i" 1),
	(asm_simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1),
	(res_inst_tac [("t","x")] subst 1),
	(atac 1),
	(etac monofun_cfun_arg 1)
	]);


(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of iterate                                   *)
(* ------------------------------------------------------------------------ *)

val monofun_iterate = prove_goalw Fix.thy  [monofun] "monofun(iterate(i))"
 (fn prems =>
	[
	(strip_tac 1),
	(nat_ind_tac "i" 1),
	(asm_simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1),
	(rtac (less_fun RS iffD2) 1),
	(rtac allI 1),
	(rtac monofun_cfun 1),
	(atac 1),
	(rtac (less_fun RS iffD1 RS spec) 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* the following lemma uses contlub_cfun which itself is based on a         *)
(* diagonalisation lemma for continuous functions with two arguments.       *)
(* In this special case it is the application function fapp                 *)
(* ------------------------------------------------------------------------ *)

val contlub_iterate = prove_goalw Fix.thy  [contlub] "contlub(iterate(i))"
 (fn prems =>
	[
	(strip_tac 1),
	(nat_ind_tac "i" 1),
	(asm_simp_tac iterate_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1),
	(asm_simp_tac iterate_ss 1),
	(rtac ext 1),
	(rtac (thelub_fun RS ssubst) 1),
	(rtac is_chainI 1),
	(rtac allI 1),
	(rtac (less_fun RS iffD2) 1),
	(rtac allI 1),
	(rtac (is_chainE RS spec) 1),
	(rtac (monofun_fapp1 RS ch2ch_MF2LR) 1),
	(rtac allI 1),
	(rtac monofun_fapp2 1),
	(atac 1),
	(rtac ch2ch_fun 1),
	(rtac (monofun_iterate RS ch2ch_monofun) 1),
	(atac 1),
	(rtac (thelub_fun RS ssubst) 1),
	(rtac (monofun_iterate RS ch2ch_monofun) 1),
	(atac 1),
	(rtac contlub_cfun  1),
	(atac 1),
	(etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1)
	]);


val contX_iterate = prove_goal Fix.thy "contX(iterate(i))"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_iterate 1),
	(rtac contlub_iterate 1)
	]);

(* ------------------------------------------------------------------------ *)
(* a lemma about continuity of iterate in its third argument                *)
(* ------------------------------------------------------------------------ *)

val monofun_iterate2 = prove_goal Fix.thy "monofun(iterate(n,F))"
 (fn prems =>
	[
	(rtac monofunI 1),
	(strip_tac 1),
	(nat_ind_tac "n" 1),
	(asm_simp_tac iterate_ss 1),
	(asm_simp_tac iterate_ss 1),
	(etac monofun_cfun_arg 1)
	]);

val contlub_iterate2 = prove_goal Fix.thy "contlub(iterate(n,F))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(nat_ind_tac "n" 1),
	(simp_tac iterate_ss 1),
	(simp_tac iterate_ss 1),
	(res_inst_tac [("t","iterate(n1, F, lub(range(%u. Y(u))))"),
	("s","lub(range(%i. iterate(n1, F, Y(i))))")] ssubst 1),
	(atac 1),
	(rtac contlub_cfun_arg 1),
	(etac (monofun_iterate2 RS ch2ch_monofun) 1)
	]);

val contX_iterate2 = prove_goal Fix.thy "contX(iterate(n,F))"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_iterate2 1),
	(rtac contlub_iterate2 1)
	]);

(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of Ifix                                      *)
(* ------------------------------------------------------------------------ *)

val monofun_Ifix = prove_goalw Fix.thy  [monofun,Ifix_def] "monofun(Ifix)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac lub_mono 1),
	(rtac is_chain_iterate 1),
	(rtac is_chain_iterate 1),
	(rtac allI 1),
	(rtac (less_fun RS iffD1 RS spec) 1),
	(etac (monofun_iterate RS monofunE RS spec RS spec RS mp) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* since iterate is not monotone in its first argument, special lemmas must *)
(* be derived for lubs in this argument                                     *)
(* ------------------------------------------------------------------------ *)

val is_chain_iterate_lub = prove_goal Fix.thy   
"is_chain(Y) ==> is_chain(%i. lub(range(%ia. iterate(ia,Y(i),UU))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_chainI 1),
	(strip_tac 1),
	(rtac lub_mono 1),
	(rtac is_chain_iterate 1),
	(rtac is_chain_iterate 1),
	(strip_tac 1),
	(etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun RS is_chainE 
         RS spec) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* this exchange lemma is analog to the one for monotone functions          *)
(* observe that monotonicity is not really needed. The propagation of       *)
(* chains is the essential argument which is usually derived from monot.    *)
(* ------------------------------------------------------------------------ *)

val contlub_Ifix_lemma1 = prove_goal Fix.thy 
"is_chain(Y) ==> iterate(n,lub(range(Y)),y) = lub(range(%i. iterate(n,Y(i),y)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (thelub_fun RS subst) 1),
	(rtac (monofun_iterate RS ch2ch_monofun) 1),
	(atac 1),
	(rtac fun_cong 1),
	(rtac (contlub_iterate RS contlubE RS spec RS mp RS ssubst) 1),
	(atac 1),
	(rtac refl 1)
	]);


val ex_lub_iterate = prove_goal Fix.thy  "is_chain(Y) ==>\
\         lub(range(%i. lub(range(%ia. iterate(i,Y(ia),UU))))) =\
\         lub(range(%i. lub(range(%ia. iterate(ia,Y(i),UU)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac antisym_less 1),
	(rtac is_lub_thelub 1),
	(rtac (contlub_Ifix_lemma1 RS ext RS subst) 1),
	(atac 1),
	(rtac is_chain_iterate 1),
	(rtac ub_rangeI 1),
	(strip_tac 1),
	(rtac lub_mono 1),
	(etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1),
	(etac is_chain_iterate_lub 1),
	(strip_tac 1),
	(rtac is_ub_thelub 1),
	(rtac is_chain_iterate 1),
	(rtac is_lub_thelub 1),
	(etac is_chain_iterate_lub 1),
	(rtac ub_rangeI 1),
	(strip_tac 1),
	(rtac lub_mono 1),
	(rtac is_chain_iterate 1),
	(rtac (contlub_Ifix_lemma1 RS ext RS subst) 1),
	(atac 1),
	(rtac is_chain_iterate 1),
	(strip_tac 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1)
	]);


val contlub_Ifix = prove_goalw Fix.thy  [contlub,Ifix_def] "contlub(Ifix)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (contlub_Ifix_lemma1 RS ext RS ssubst) 1),
	(atac 1),
	(etac ex_lub_iterate 1)
	]);


val contX_Ifix = prove_goal Fix.thy "contX(Ifix)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Ifix 1),
	(rtac contlub_Ifix 1)
	]);

(* ------------------------------------------------------------------------ *)
(* propagate properties of Ifix to its continuous counterpart               *)
(* ------------------------------------------------------------------------ *)

val fix_eq = prove_goalw Fix.thy  [fix_def] "fix[F]=F[fix[F]]"
 (fn prems =>
	[
	(asm_simp_tac (Cfun_ss addsimps [contX_Ifix]) 1),
	(rtac Ifix_eq 1)
	]);

val fix_least = prove_goalw Fix.thy [fix_def] "F[x]=x ==> fix[F] << x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (Cfun_ss addsimps [contX_Ifix]) 1),
	(etac Ifix_least 1)
	]);


val fix_eq2 = prove_goal Fix.thy "f == fix[F] ==> f = F[f]"
 (fn prems =>
	[
	(rewrite_goals_tac prems),
	(rtac fix_eq 1)
	]);

val fix_eq3 = prove_goal Fix.thy "f == fix[F] ==> f[x] = F[f][x]"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac ((hd prems) RS fix_eq2 RS cfun_fun_cong) 1),
	(rtac refl 1)
	]);

fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i)); 

val fix_eq4 = prove_goal Fix.thy "f = fix[F] ==> f = F[f]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(rtac fix_eq 1)
	]);

val fix_eq5 = prove_goal Fix.thy "f = fix[F] ==> f[x] = F[f][x]"
 (fn prems =>
	[
	(rtac trans 1),
	(rtac ((hd prems) RS fix_eq4 RS cfun_fun_cong) 1),
	(rtac refl 1)
	]);

fun fix_tac5 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq5) i)); 

fun fix_prover thy fixdef thm = prove_goal thy thm
 (fn prems =>
        [
        (rtac trans 1),
        (rtac (fixdef RS fix_eq4) 1),
        (rtac trans 1),
        (rtac beta_cfun 1),
        (contX_tacR 1),
        (rtac refl 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* better access to definitions                                             *)
(* ------------------------------------------------------------------------ *)


val Ifix_def2 = prove_goal Fix.thy "Ifix=(%x. lub(range(%i. iterate(i,x,UU))))"
 (fn prems =>
	[
	(rtac ext 1),
	(rewrite_goals_tac [Ifix_def]),
	(rtac refl 1)
	]);

(* ------------------------------------------------------------------------ *)
(* direct connection between fix and iteration without Ifix                 *)
(* ------------------------------------------------------------------------ *)

val fix_def2 = prove_goalw Fix.thy [fix_def]
 "fix[F] = lub(range(%i. iterate(i,F,UU)))"
 (fn prems =>
	[
	(fold_goals_tac [Ifix_def]),
	(asm_simp_tac (Cfun_ss addsimps [contX_Ifix]) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Lemmas about admissibility and fixed point induction                     *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)

val adm_def2 = prove_goalw Fix.thy [adm_def]
	"adm(P) = (!Y. is_chain(Y) --> (!i.P(Y(i))) --> P(lub(range(Y))))"
 (fn prems =>
	[
	(rtac refl 1)
	]);

val admw_def2 = prove_goalw Fix.thy [admw_def]
	"admw(P) = (!F.((!n.P(iterate(n,F,UU)))-->\
\			 P(lub(range(%i.iterate(i,F,UU))))))"
 (fn prems =>
	[
	(rtac refl 1)
	]);

(* ------------------------------------------------------------------------ *)
(* an admissible formula is also weak admissible                            *)
(* ------------------------------------------------------------------------ *)

val adm_impl_admw = prove_goalw  Fix.thy [admw_def] "adm(P)==>admw(P)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(rtac is_chain_iterate 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* fixed point induction                                                    *)
(* ------------------------------------------------------------------------ *)

val fix_ind = prove_goal  Fix.thy  
"[| adm(P);P(UU);!!x. P(x) ==> P(F[x])|] ==> P(fix[F])"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (fix_def2 RS ssubst) 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(rtac is_chain_iterate 1),
	(rtac allI 1),
	(nat_ind_tac "i" 1),
	(rtac (iterate_0 RS ssubst) 1),
	(atac 1),
	(rtac (iterate_Suc RS ssubst) 1),
	(resolve_tac prems 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* computational induction for weak admissible formulae                     *)
(* ------------------------------------------------------------------------ *)

val wfix_ind = prove_goal  Fix.thy  
"[| admw(P); !n. P(iterate(n,F,UU))|] ==> P(fix[F])"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (fix_def2 RS ssubst) 1),
	(rtac (admw_def2 RS iffD1 RS spec RS mp) 1),
	(atac 1),
	(rtac allI 1),
	(etac spec 1)
	]);

(* ------------------------------------------------------------------------ *)
(* for chain-finite (easy) types every formula is admissible                *)
(* ------------------------------------------------------------------------ *)

val adm_max_in_chain = prove_goalw  Fix.thy  [adm_def]
"!Y. is_chain(Y::nat=>'a) --> (? n.max_in_chain(n,Y)) ==> adm(P::'a=>bool)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac exE 1),
	(rtac mp 1),
	(etac spec 1),
	(atac 1),
	(rtac (lub_finch1 RS thelubI RS ssubst) 1),
	(atac 1),
	(atac 1),
	(etac spec 1)
	]);


val adm_chain_finite = prove_goalw  Fix.thy  [chain_finite_def]
	"chain_finite(x::'a) ==> adm(P::'a=>bool)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac adm_max_in_chain 1)
	]);

(* ------------------------------------------------------------------------ *)
(* flat types are chain_finite                                              *)
(* ------------------------------------------------------------------------ *)

val flat_imp_chain_finite = prove_goalw  Fix.thy  [flat_def,chain_finite_def]
	"flat(x::'a)==>chain_finite(x::'a)"
 (fn prems =>
	[
	(rewrite_goals_tac [max_in_chain_def]),
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(res_inst_tac [("Q","!i.Y(i)=UU")] classical2 1),
	(res_inst_tac [("x","0")] exI 1),
	(strip_tac 1),
	(rtac trans 1),
	(etac spec 1),
	(rtac sym 1),
	(etac spec 1),
	(rtac (chain_mono2 RS exE) 1),
	(fast_tac HOL_cs 1),
	(atac 1),
	(res_inst_tac [("x","Suc(x)")] exI 1),
	(strip_tac 1),
	(rtac disjE 1),
	(atac 3),
	(rtac mp 1),
	(dtac spec 1),
	(etac spec 1),
	(etac (le_imp_less_or_eq RS disjE) 1),
	(etac (chain_mono RS mp) 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac refl_less 1),
	(res_inst_tac [("P","Y(Suc(x)) = UU")] notE 1),
	(atac 2),
	(rtac mp 1),
	(etac spec 1),
	(asm_simp_tac nat_ss 1)
	]);


val adm_flat = flat_imp_chain_finite RS adm_chain_finite;
(* flat(?x::?'a) ==> adm(?P::?'a => bool) *)

val flat_void = prove_goalw Fix.thy [flat_def] "flat(UU::void)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac disjI1 1),
	(rtac unique_void2 1)
	]);

(* ------------------------------------------------------------------------ *)
(* continuous isomorphisms are strict                                       *)
(* a prove for embedding projection pairs is similar                        *)
(* ------------------------------------------------------------------------ *)

val iso_strict = prove_goal  Fix.thy  
"!!f g.[|!y.f[g[y]]=(y::'b) ; !x.g[f[x]]=(x::'a) |] \
\ ==> f[UU]=UU & g[UU]=UU"
 (fn prems =>
	[
	(rtac conjI 1),
	(rtac UU_I 1),
	(res_inst_tac [("s","f[g[UU::'b]]"),("t","UU::'b")] subst 1),
	(etac spec 1),
	(rtac (minimal RS monofun_cfun_arg) 1),
	(rtac UU_I 1),
	(res_inst_tac [("s","g[f[UU::'a]]"),("t","UU::'a")] subst 1),
	(etac spec 1),
	(rtac (minimal RS monofun_cfun_arg) 1)
	]);


val isorep_defined = prove_goal Fix.thy 
	"[|!x.rep[abs[x]]=x;!y.abs[rep[y]]=y;z~=UU|] ==> rep[z]~=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac swap 1),
	(dtac notnotD 1),
	(dres_inst_tac [("f","abs")] cfun_arg_cong 1),
	(etac box_equals 1),
	(fast_tac HOL_cs 1),
	(etac (iso_strict RS conjunct1) 1),
	(atac 1)
	]);

val isoabs_defined = prove_goal Fix.thy 
	"[|!x.rep[abs[x]]=x;!y.abs[rep[y]]=y;z~=UU|] ==> abs[z]~=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac swap 1),
	(dtac notnotD 1),
	(dres_inst_tac [("f","rep")] cfun_arg_cong 1),
	(etac box_equals 1),
	(fast_tac HOL_cs 1),
	(etac (iso_strict RS conjunct2) 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* propagation of flatness and chainfiniteness by continuous isomorphisms   *)
(* ------------------------------------------------------------------------ *)

val chfin2chfin = prove_goalw  Fix.thy  [chain_finite_def]
"!!f g.[|chain_finite(x::'a); !y.f[g[y]]=(y::'b) ; !x.g[f[x]]=(x::'a) |] \
\ ==> chain_finite(y::'b)"
 (fn prems =>
	[
	(rewrite_goals_tac [max_in_chain_def]),
	(strip_tac 1),
	(rtac exE 1),
	(res_inst_tac [("P","is_chain(%i.g[Y(i)])")] mp 1),
	(etac spec 1),
	(etac ch2ch_fappR 1),
	(rtac exI 1),
	(strip_tac 1),
	(res_inst_tac [("s","f[g[Y(x)]]"),("t","Y(x)")] subst 1),
	(etac spec 1),
	(res_inst_tac [("s","f[g[Y(j)]]"),("t","Y(j)")] subst 1),
	(etac spec 1),
	(rtac cfun_arg_cong 1),
	(rtac mp 1),
	(etac spec 1),
	(atac 1)
	]);

val flat2flat = prove_goalw  Fix.thy  [flat_def]
"!!f g.[|flat(x::'a); !y.f[g[y]]=(y::'b) ; !x.g[f[x]]=(x::'a) |] \
\ ==> flat(y::'b)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac disjE 1),
	(res_inst_tac [("P","g[x]<<g[y]")] mp 1),
	(etac monofun_cfun_arg 2),
	(dtac spec 1),
	(etac spec 1),
	(rtac disjI1 1),
	(rtac trans 1),
	(res_inst_tac [("s","f[g[x]]"),("t","x")] subst 1),
	(etac spec 1),
	(etac cfun_arg_cong 1),
	(rtac (iso_strict RS conjunct1) 1),
	(atac 1),
	(atac 1),
	(rtac disjI2 1),
	(res_inst_tac [("s","f[g[x]]"),("t","x")] subst 1),
	(etac spec 1),
	(res_inst_tac [("s","f[g[y]]"),("t","y")] subst 1),
	(etac spec 1),
	(etac cfun_arg_cong 1)
	]);

(* ------------------------------------------------------------------------ *)
(* admissibility of special formulae and propagation                        *)
(* ------------------------------------------------------------------------ *)

val adm_less = prove_goalw  Fix.thy [adm_def]
	"[|contX(u);contX(v)|]==> adm(%x.u(x)<<v(x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(etac (contX2contlub RS contlubE RS spec RS mp RS ssubst) 1),
	(atac 1),
	(etac (contX2contlub RS contlubE RS spec RS mp RS ssubst) 1),
	(atac 1),
	(rtac lub_mono 1),
	(cut_facts_tac prems 1),
	(etac (contX2mono RS ch2ch_monofun) 1),
	(atac 1),
	(cut_facts_tac prems 1),
	(etac (contX2mono RS ch2ch_monofun) 1),
	(atac 1),
	(atac 1)
	]);

val adm_conj = prove_goal  Fix.thy  
	"[| adm(P); adm(Q) |] ==> adm(%x.P(x)&Q(x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (adm_def2 RS iffD2) 1),
	(strip_tac 1),
	(rtac conjI 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(atac 1),
	(fast_tac HOL_cs 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(atac 1),
	(fast_tac HOL_cs 1)
	]);

val adm_cong = prove_goal  Fix.thy  
	"(!x. P(x) = Q(x)) ==> adm(P)=adm(Q)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("s","P"),("t","Q")] subst 1),
	(rtac refl 2),
	(rtac ext 1),
	(etac spec 1)
	]);

val adm_not_free = prove_goalw  Fix.thy [adm_def] "adm(%x.t)"
 (fn prems =>
	[
	(fast_tac HOL_cs 1)
	]);

val adm_not_less = prove_goalw  Fix.thy [adm_def]
	"contX(t) ==> adm(%x.~ t(x) << u)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac contrapos 1),
	(etac spec 1),
	(rtac trans_less 1),
	(atac 2),
	(etac (contX2mono RS monofun_fun_arg) 1),
	(rtac is_ub_thelub 1),
	(atac 1)
	]);

val adm_all = prove_goal  Fix.thy  
	" !y.adm(P(y)) ==> adm(%x.!y.P(y,x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (adm_def2 RS iffD2) 1),
	(strip_tac 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(etac spec 1),
	(atac 1),
	(rtac allI 1),
	(dtac spec 1),
	(etac spec 1)
	]);

val adm_subst = prove_goal  Fix.thy  
	"[|contX(t); adm(P)|] ==> adm(%x.P(t(x)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (adm_def2 RS iffD2) 1),
	(strip_tac 1),
	(rtac (contX2contlub RS contlubE RS spec RS mp RS ssubst) 1),
	(atac 1),
	(atac 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(rtac (contX2mono RS ch2ch_monofun) 1),
	(atac 1),
	(atac 1),
	(atac 1)
	]);

val adm_UU_not_less = prove_goal  Fix.thy "adm(%x.~ UU << t(x))"
 (fn prems =>
	[
	(res_inst_tac [("P2","%x.False")] (adm_cong RS iffD1) 1),
	(asm_simp_tac Cfun_ss 1),
	(rtac adm_not_free 1)
	]);

val adm_not_UU = prove_goalw  Fix.thy [adm_def] 
	"contX(t)==> adm(%x.~ t(x) = UU)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac contrapos 1),
	(etac spec 1),
	(rtac (chain_UU_I RS spec) 1),
	(rtac (contX2mono RS ch2ch_monofun) 1),
	(atac 1),
	(atac 1),
	(rtac (contX2contlub RS contlubE RS spec RS mp RS subst) 1),
	(atac 1),
	(atac 1),
	(atac 1)
	]);

val adm_eq = prove_goal  Fix.thy 
	"[|contX(u);contX(v)|]==> adm(%x.u(x)= v(x))"
 (fn prems =>
	[
	(rtac (adm_cong RS iffD1) 1),
	(rtac allI 1),
	(rtac iffI 1),
	(rtac antisym_less 1),
	(rtac antisym_less_inverse 3),
	(atac 3),
	(etac conjunct1 1),
	(etac conjunct2 1),
	(rtac adm_conj 1),
	(rtac adm_less 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1),
	(rtac adm_less 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1)
	]);


(* ------------------------------------------------------------------------ *)
(* admissibility for disjunction is hard to prove. It takes 10 Lemmas       *)
(* ------------------------------------------------------------------------ *)

val adm_disj_lemma1 = prove_goal  Pcpo.thy 
"[| is_chain(Y); !n.P(Y(n))|Q(Y(n))|]\
\ ==> (? i.!j. i<j --> Q(Y(j))) | (!i.? j.i<j & P(Y(j)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);

val adm_disj_lemma2 = prove_goal  Fix.thy  
"[| adm(Q); ? X.is_chain(X) & (!n.Q(X(n))) &\
\   lub(range(Y))=lub(range(X))|] ==> Q(lub(range(Y)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(etac conjE 1),
	(etac conjE 1),
	(res_inst_tac [("s","lub(range(X))"),("t","lub(range(Y))")] ssubst 1),
	(atac 1),
	(rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
	(atac 1),
	(atac 1),
	(atac 1)
	]);

val adm_disj_lemma3 = prove_goal  Fix.thy
"[| is_chain(Y); ! j. i < j --> Q(Y(j)) |] ==>\
\         is_chain(%m. if(m < Suc(i),Y(Suc(i)),Y(m)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_chainI 1),
	(rtac allI 1),
	(res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1),
	(res_inst_tac [("s","False"),("t","ia < Suc(i)")] ssubst 1),
	(rtac iffI 1),
	(etac FalseE 2),
	(rtac notE 1),
	(rtac (not_less_eq RS iffD2) 1),
	(atac 1),
	(atac 1),
	(res_inst_tac [("s","False"),("t","Suc(ia) < Suc(i)")] ssubst 1),
	(asm_simp_tac nat_ss  1),
	(rtac iffI 1),
	(etac FalseE 2),
	(rtac notE 1),
	(etac (less_not_sym RS mp) 1),	
	(atac 1),
	(asm_simp_tac Cfun_ss  1),
	(etac (is_chainE RS spec) 1),
	(hyp_subst_tac 1),
	(asm_simp_tac nat_ss 1),
	(rtac refl_less 1),
	(asm_simp_tac nat_ss 1),
	(rtac refl_less 1)
	]);

val adm_disj_lemma4 = prove_goal  Fix.thy
"[| ! j. i < j --> Q(Y(j)) |] ==>\
\	 ! n. Q(if(n < Suc(i),Y(Suc(i)),Y(n)))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac allI 1),
	(res_inst_tac [("m","n"),("n","Suc(i)")] nat_less_cases 1),
	(res_inst_tac[("s","Y(Suc(i))"),("t","if(n<Suc(i),Y(Suc(i)),Y(n))")]
		ssubst 1),
	(asm_simp_tac nat_ss 1),
	(etac allE 1),
	(rtac mp 1),
	(atac 1),
	(asm_simp_tac nat_ss 1),
	(res_inst_tac[("s","Y(n)"),("t","if(n<Suc(i),Y(Suc(i)),Y(n))")] 
		ssubst 1),
	(asm_simp_tac nat_ss 1),
	(hyp_subst_tac 1),
	(dtac spec 1),
	(rtac mp 1),
	(atac 1),
	(asm_simp_tac nat_ss 1),
	(res_inst_tac [("s","Y(n)"),("t","if(n < Suc(i),Y(Suc(i)),Y(n))")] 
		ssubst 1),
	(res_inst_tac [("s","False"),("t","n < Suc(i)")] ssubst 1),
	(rtac iffI 1),
	(etac FalseE 2),
	(rtac notE 1),
	(etac (less_not_sym RS mp) 1),	
	(atac 1),
	(asm_simp_tac nat_ss 1),
	(dtac spec 1),
	(rtac mp 1),
	(atac 1),
	(etac Suc_lessD 1)
	]);

val adm_disj_lemma5 = prove_goal  Fix.thy
"[| is_chain(Y::nat=>'a); ! j. i < j --> Q(Y(j)) |] ==>\
\         lub(range(Y)) = lub(range(%m. if(m < Suc(i),Y(Suc(i)),Y(m))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac lub_equal2 1),
	(atac 2),
	(rtac adm_disj_lemma3 2),
	(atac 2),
	(atac 2),
	(res_inst_tac [("x","i")] exI 1),
	(strip_tac 1),
	(res_inst_tac [("s","False"),("t","ia < Suc(i)")] ssubst 1),
	(rtac iffI 1),
	(etac FalseE 2),
	(rtac notE 1),
	(rtac (not_less_eq RS iffD2) 1),
	(atac 1),
	(atac 1),
	(rtac (if_False RS ssubst) 1),
	(rtac refl 1)
	]);

val adm_disj_lemma6 = prove_goal  Fix.thy
"[| is_chain(Y::nat=>'a); ? i. ! j. i < j --> Q(Y(j)) |] ==>\
\         ? X. is_chain(X) & (! n. Q(X(n))) & lub(range(Y)) = lub(range(X))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(res_inst_tac [("x","%m.if(m< Suc(i),Y(Suc(i)),Y(m))")] exI 1),
	(rtac conjI 1),
	(rtac adm_disj_lemma3 1),
	(atac 1),
	(atac 1),
	(rtac conjI 1),
	(rtac adm_disj_lemma4 1),
	(atac 1),
	(rtac adm_disj_lemma5 1),
	(atac 1),
	(atac 1)
	]);


val adm_disj_lemma7 = prove_goal  Fix.thy 
"[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j))  |] ==>\
\         is_chain(%m. Y(theleast(%j. m<j & P(Y(j)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_chainI 1),
	(rtac allI 1),
	(rtac chain_mono3 1),
	(atac 1),
	(rtac theleast2 1),
	(rtac conjI 1),
	(rtac Suc_lessD 1),
	(etac allE 1),
	(etac exE 1),
	(rtac (theleast1 RS conjunct1) 1),
	(atac 1),
	(etac allE 1),
	(etac exE 1),
	(rtac (theleast1 RS conjunct2) 1),
	(atac 1)
	]);

val adm_disj_lemma8 = prove_goal  Fix.thy 
"[| ! i. ? j. i < j & P(Y(j)) |] ==> ! m. P(Y(theleast(%j. m<j & P(Y(j)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(etac allE 1),
	(etac exE 1),
	(etac (theleast1 RS conjunct2) 1)
	]);

val adm_disj_lemma9 = prove_goal  Fix.thy
"[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j)) |] ==>\
\         lub(range(Y)) = lub(range(%m. Y(theleast(%j. m<j & P(Y(j))))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac antisym_less 1),
	(rtac lub_mono 1),
	(atac 1),
	(rtac adm_disj_lemma7 1),
	(atac 1),
	(atac 1),
	(strip_tac 1),
	(rtac (chain_mono RS mp) 1),
	(atac 1),
	(etac allE 1),
	(etac exE 1),
	(rtac (theleast1 RS conjunct1) 1),
	(atac 1),
	(rtac lub_mono3 1),
	(rtac adm_disj_lemma7 1),
	(atac 1),
	(atac 1),
	(atac 1),
	(strip_tac 1),
	(rtac exI 1),
	(rtac (chain_mono RS mp) 1),
	(atac 1),
	(rtac lessI 1)
	]);

val adm_disj_lemma10 = prove_goal  Fix.thy
"[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j)) |] ==>\
\         ? X. is_chain(X) & (! n. P(X(n))) & lub(range(Y)) = lub(range(X))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("x","%m. Y(theleast(%j. m<j & P(Y(j))))")] exI 1),
	(rtac conjI 1),
	(rtac adm_disj_lemma7 1),
	(atac 1),
	(atac 1),
	(rtac conjI 1),
	(rtac adm_disj_lemma8 1),
	(atac 1),
	(rtac adm_disj_lemma9 1),
	(atac 1),
	(atac 1)
	]);

val adm_disj = prove_goal  Fix.thy  
	"[| adm(P); adm(Q) |] ==> adm(%x.P(x)|Q(x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (adm_def2 RS iffD2) 1),
	(strip_tac 1),
	(rtac (adm_disj_lemma1 RS disjE) 1),
	(atac 1),
	(atac 1),
	(rtac disjI2 1),
	(rtac adm_disj_lemma2 1),
	(atac 1),
	(rtac adm_disj_lemma6 1),
	(atac 1),
	(atac 1),
	(rtac disjI1 1),
	(rtac adm_disj_lemma2 1),
	(atac 1),
	(rtac adm_disj_lemma10 1),
	(atac 1),
	(atac 1)
	]);

val adm_impl = prove_goal  Fix.thy  
	"[| adm(%x.~P(x)); adm(Q) |] ==> adm(%x.P(x)-->Q(x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("P2","%x.~P(x)|Q(x)")] (adm_cong RS iffD1) 1),
	(fast_tac HOL_cs 1),
	(rtac adm_disj 1),
	(atac 1),
	(atac 1)
	]);


val adm_all2 = (allI RS adm_all);

val adm_thms = [adm_impl,adm_disj,adm_eq,adm_not_UU,adm_UU_not_less,
	adm_all2,adm_not_less,adm_not_free,adm_conj,adm_less
	];

(* ------------------------------------------------------------------------- *)
(* a result about functions with flat codomain                               *)
(* ------------------------------------------------------------------------- *)

val flat_codom = prove_goalw Fix.thy [flat_def]
"[|flat(y::'b);f[x::'a]=(c::'b)|] ==> f[UU::'a]=UU::'b | (!z.f[z::'a]=c)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("Q","f[x::'a]=UU::'b")] classical2 1),
	(rtac disjI1 1),
	(rtac UU_I 1),
	(res_inst_tac [("s","f[x]"),("t","UU::'b")] subst 1),
	(atac 1),
	(rtac (minimal RS monofun_cfun_arg) 1),
	(res_inst_tac [("Q","f[UU::'a]=UU::'b")] classical2 1),
	(etac disjI1 1),
	(rtac disjI2 1),
	(rtac allI 1),
	(res_inst_tac [("s","f[x]"),("t","c")] subst 1),
	(atac 1),
	(res_inst_tac [("a","f[UU::'a]")] (refl RS box_equals) 1),
	(etac allE 1),(etac allE 1),
	(dtac mp 1),
	(res_inst_tac [("fo5","f")] (minimal RS monofun_cfun_arg) 1),
	(etac disjE 1),
	(contr_tac 1),
	(atac 1),
	(etac allE 1),
	(etac allE 1),
	(dtac mp 1),
	(res_inst_tac [("fo5","f")] (minimal RS monofun_cfun_arg) 1),
	(etac disjE 1),
	(contr_tac 1),
	(atac 1)
	]);

(*  Title:      HOLCF/fix.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for fix.thy 
*)

open Fix;

(* ------------------------------------------------------------------------ *)
(* derive inductive properties of iterate from primitive recursion          *)
(* ------------------------------------------------------------------------ *)

qed_goal "iterate_0" Fix.thy "iterate 0 F x = x"
 (fn prems =>
        [
        (resolve_tac (nat_recs iterate_def) 1)
        ]);

qed_goal "iterate_Suc" Fix.thy "iterate (Suc n) F x  = F`(iterate n F x)"
 (fn prems =>
        [
        (resolve_tac (nat_recs iterate_def) 1)
        ]);

Addsimps [iterate_0, iterate_Suc];

qed_goal "iterate_Suc2" Fix.thy "iterate (Suc n) F x = iterate n F (F`x)"
 (fn prems =>
        [
        (nat_ind_tac "n" 1),
        (Simp_tac 1),
        (stac iterate_Suc 1),
        (stac iterate_Suc 1),
        (etac ssubst 1),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the sequence of function itertaions is a chain                           *)
(* This property is essential since monotonicity of iterate makes no sense  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "is_chain_iterate2" Fix.thy [is_chain] 
        " x << F`x ==> is_chain (%i.iterate i F x)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (Simp_tac 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (etac monofun_cfun_arg 1)
        ]);


qed_goal "is_chain_iterate" Fix.thy  
        "is_chain (%i.iterate i F UU)"
 (fn prems =>
        [
        (rtac is_chain_iterate2 1),
        (rtac minimal 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Kleene's fixed point theorems for continuous functions in pointed        *)
(* omega cpo's                                                              *)
(* ------------------------------------------------------------------------ *)


qed_goalw "Ifix_eq" Fix.thy  [Ifix_def] "Ifix F =F`(Ifix F)"
 (fn prems =>
        [
        (stac contlub_cfun_arg 1),
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


qed_goalw "Ifix_least" Fix.thy [Ifix_def] "F`x=x ==> Ifix(F) << x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lub_thelub 1),
        (rtac is_chain_iterate 1),
        (rtac ub_rangeI 1),
        (strip_tac 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (res_inst_tac [("t","x")] subst 1),
        (atac 1),
        (etac monofun_cfun_arg 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of iterate                                   *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_iterate" Fix.thy  [monofun] "monofun(iterate(i))"
 (fn prems =>
        [
        (strip_tac 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
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

qed_goalw "contlub_iterate" Fix.thy  [contlub] "contlub(iterate(i))"
 (fn prems =>
        [
        (strip_tac 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (rtac (lub_const RS thelubI RS sym) 1),
        (Asm_simp_tac 1),
        (rtac ext 1),
        (stac thelub_fun 1),
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
        (stac thelub_fun 1),
        (rtac (monofun_iterate RS ch2ch_monofun) 1),
        (atac 1),
        (rtac contlub_cfun  1),
        (atac 1),
        (etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1)
        ]);


qed_goal "cont_iterate" Fix.thy "cont(iterate(i))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_iterate 1),
        (rtac contlub_iterate 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* a lemma about continuity of iterate in its third argument                *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_iterate2" Fix.thy "monofun(iterate n F)"
 (fn prems =>
        [
        (rtac monofunI 1),
        (strip_tac 1),
        (nat_ind_tac "n" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (etac monofun_cfun_arg 1)
        ]);

qed_goal "contlub_iterate2" Fix.thy "contlub(iterate n F)"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (nat_ind_tac "n" 1),
        (Simp_tac 1),
        (Simp_tac 1),
        (res_inst_tac [("t","iterate n1 F (lub(range(%u. Y u)))"),
        ("s","lub(range(%i. iterate n1 F (Y i)))")] ssubst 1),
        (atac 1),
        (rtac contlub_cfun_arg 1),
        (etac (monofun_iterate2 RS ch2ch_monofun) 1)
        ]);

qed_goal "cont_iterate2" Fix.thy "cont (iterate n F)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_iterate2 1),
        (rtac contlub_iterate2 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of Ifix                                      *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Ifix" Fix.thy  [monofun,Ifix_def] "monofun(Ifix)"
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

qed_goal "is_chain_iterate_lub" Fix.thy   
"is_chain(Y) ==> is_chain(%i. lub(range(%ia. iterate ia (Y i) UU)))"
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

qed_goal "contlub_Ifix_lemma1" Fix.thy 
"is_chain(Y) ==>iterate n (lub(range Y)) y = lub(range(%i. iterate n (Y i) y))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (thelub_fun RS subst) 1),
        (rtac (monofun_iterate RS ch2ch_monofun) 1),
        (atac 1),
        (rtac fun_cong 1),
        (stac (contlub_iterate RS contlubE RS spec RS mp) 1),
        (atac 1),
        (rtac refl 1)
        ]);


qed_goal "ex_lub_iterate" Fix.thy  "is_chain(Y) ==>\
\         lub(range(%i. lub(range(%ia. iterate i (Y ia) UU)))) =\
\         lub(range(%i. lub(range(%ia. iterate ia (Y i) UU))))"
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


qed_goalw "contlub_Ifix" Fix.thy  [contlub,Ifix_def] "contlub(Ifix)"
 (fn prems =>
        [
        (strip_tac 1),
        (stac (contlub_Ifix_lemma1 RS ext) 1),
        (atac 1),
        (etac ex_lub_iterate 1)
        ]);


qed_goal "cont_Ifix" Fix.thy "cont(Ifix)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Ifix 1),
        (rtac contlub_Ifix 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* propagate properties of Ifix to its continuous counterpart               *)
(* ------------------------------------------------------------------------ *)

qed_goalw "fix_eq" Fix.thy  [fix_def] "fix`F = F`(fix`F)"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps [cont_Ifix]) 1),
        (rtac Ifix_eq 1)
        ]);

qed_goalw "fix_least" Fix.thy [fix_def] "F`x = x ==> fix`F << x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (!simpset addsimps [cont_Ifix]) 1),
        (etac Ifix_least 1)
        ]);


qed_goal "fix_eqI" Fix.thy
"[| F`x = x; !z. F`z = z --> x << z |] ==> x = fix`F"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac antisym_less 1),
        (etac allE 1),
        (etac mp 1),
        (rtac (fix_eq RS sym) 1),
        (etac fix_least 1)
        ]);


qed_goal "fix_eq2" Fix.thy "f == fix`F ==> f = F`f"
 (fn prems =>
        [
        (rewrite_goals_tac prems),
        (rtac fix_eq 1)
        ]);

qed_goal "fix_eq3" Fix.thy "f == fix`F ==> f`x = F`f`x"
 (fn prems =>
        [
        (rtac trans 1),
        (rtac ((hd prems) RS fix_eq2 RS cfun_fun_cong) 1),
        (rtac refl 1)
        ]);

fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i)); 

qed_goal "fix_eq4" Fix.thy "f = fix`F ==> f = F`f"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (hyp_subst_tac 1),
        (rtac fix_eq 1)
        ]);

qed_goal "fix_eq5" Fix.thy "f = fix`F ==> f`x = F`f`x"
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
        (cont_tacR 1),
        (rtac refl 1)
        ]);

(* use this one for definitions! *)

fun fix_prover2 thy fixdef thm = prove_goal thy thm
 (fn prems =>
        [
        (rtac trans 1),
        (rtac (fix_eq2) 1),
        (rtac fixdef 1),
        (rtac beta_cfun 1),
        (cont_tacR 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* better access to definitions                                             *)
(* ------------------------------------------------------------------------ *)


qed_goal "Ifix_def2" Fix.thy "Ifix=(%x. lub(range(%i. iterate i x UU)))"
 (fn prems =>
        [
        (rtac ext 1),
        (rewtac Ifix_def),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* direct connection between fix and iteration without Ifix                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "fix_def2" Fix.thy [fix_def]
 "fix`F = lub(range(%i. iterate i F UU))"
 (fn prems =>
        [
        (fold_goals_tac [Ifix_def]),
        (asm_simp_tac (!simpset addsimps [cont_Ifix]) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Lemmas about admissibility and fixed point induction                     *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_def2" Fix.thy [adm_def]
        "adm(P) = (!Y. is_chain(Y) --> (!i.P(Y(i))) --> P(lub(range(Y))))"
 (fn prems =>
        [
        (rtac refl 1)
        ]);

qed_goalw "admw_def2" Fix.thy [admw_def]
        "admw(P) = (!F.(!n.P(iterate n F UU)) -->\
\                        P (lub(range(%i.iterate i F UU))))"
 (fn prems =>
        [
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* an admissible formula is also weak admissible                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_impl_admw"  Fix.thy [admw_def] "adm(P)==>admw(P)"
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

qed_goal "fix_ind"  Fix.thy  
"[| adm(P);P(UU);!!x. P(x) ==> P(F`x)|] ==> P(fix`F)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac fix_def2 1),
        (rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
        (atac 1),
        (rtac is_chain_iterate 1),
        (rtac allI 1),
        (nat_ind_tac "i" 1),
        (stac iterate_0 1),
        (atac 1),
        (stac iterate_Suc 1),
        (resolve_tac prems 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* computational induction for weak admissible formulae                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "wfix_ind"  Fix.thy  
"[| admw(P); !n. P(iterate n F UU)|] ==> P(fix`F)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac fix_def2 1),
        (rtac (admw_def2 RS iffD1 RS spec RS mp) 1),
        (atac 1),
        (rtac allI 1),
        (etac spec 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* for chain-finite (easy) types every formula is admissible                *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_max_in_chain"  Fix.thy  [adm_def]
"!Y. is_chain(Y::nat=>'a) --> (? n.max_in_chain n Y) ==> adm(P::'a=>bool)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac exE 1),
        (rtac mp 1),
        (etac spec 1),
        (atac 1),
        (stac (lub_finch1 RS thelubI) 1),
        (atac 1),
        (atac 1),
        (etac spec 1)
        ]);

qed_goalw "adm_chain_finite"  Fix.thy  [chain_finite_def]
        "chain_finite(x::'a) ==> adm(P::'a=>bool)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac adm_max_in_chain 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* flat types are chain_finite                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "flat_imp_chain_finite"  Fix.thy  [is_flat_def,chain_finite_def]
        "is_flat(x::'a)==>chain_finite(x::'a)"
 (fn prems =>
        [
        (rewtac max_in_chain_def),
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (case_tac "!i.Y(i)=UU" 1),
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
        (Asm_simp_tac 1)
        ]);


bind_thm ("adm_flat", flat_imp_chain_finite RS adm_chain_finite);
(* is_flat(?x::?'a) ==> adm(?P::?'a => bool) *)

qed_goalw "flat_void" Fix.thy [is_flat_def] "is_flat(UU::void)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac disjI1 1),
        (rtac unique_void2 1)
        ]);

qed_goalw "flat_eq" Fix.thy [is_flat_def] 
        "[| is_flat (x::'a); (a::'a) ~= UU |] ==> a << b = (a = b)" (fn prems=>[
        (cut_facts_tac prems 1),
        (fast_tac (HOL_cs addIs [refl_less]) 1)]);

(* ------------------------------------------------------------------------ *)
(* lemmata for improved admissibility introdution rule                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "infinite_chain_adm_lemma" Porder.thy 
"[|is_chain Y; !i. P (Y i); \
\  (!!Y. [| is_chain Y; !i. P (Y i); ~ finite_chain Y |] ==> P (lub (range Y)))\
\ |] ==> P (lub (range Y))"
 (fn prems => [
        cut_facts_tac prems 1,
        case_tac "finite_chain Y" 1,
         eresolve_tac prems 2, atac 2, atac 2,
        rewtac finite_chain_def,
        safe_tac HOL_cs,
        etac (lub_finch1 RS thelubI RS ssubst) 1, atac 1, etac spec 1]);

qed_goal "increasing_chain_adm_lemma" Porder.thy 
"[|is_chain Y; !i. P (Y i); \
\  (!!Y. [| is_chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j|]\
\ ==> P (lub (range Y))) |] ==> P (lub (range Y))"
 (fn prems => [
        cut_facts_tac prems 1,
        etac infinite_chain_adm_lemma 1, atac 1, etac thin_rl 1,
        rewtac finite_chain_def,
        safe_tac HOL_cs,
        etac swap 1,
        rewtac max_in_chain_def,
        resolve_tac prems 1, atac 1, atac 1,
        fast_tac (HOL_cs addDs [le_imp_less_or_eq] 
                         addEs [chain_mono RS mp]) 1]);

qed_goalw "admI" Fix.thy [adm_def]
 "(!!Y. [| is_chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j |]\
\ ==> P(lub (range Y))) ==> adm P" 
 (fn prems => [
        strip_tac 1,
        etac increasing_chain_adm_lemma 1, atac 1,
        eresolve_tac prems 1, atac 1, atac 1]);


(* ------------------------------------------------------------------------ *)
(* continuous isomorphisms are strict                                       *)
(* a prove for embedding projection pairs is similar                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "iso_strict"  Fix.thy  
"!!f g.[|!y.f`(g`y)=(y::'b) ; !x.g`(f`x)=(x::'a) |] \
\ ==> f`UU=UU & g`UU=UU"
 (fn prems =>
        [
        (rtac conjI 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","f`(g`(UU::'b))"),("t","UU::'b")] subst 1),
        (etac spec 1),
        (rtac (minimal RS monofun_cfun_arg) 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","g`(f`(UU::'a))"),("t","UU::'a")] subst 1),
        (etac spec 1),
        (rtac (minimal RS monofun_cfun_arg) 1)
        ]);


qed_goal "isorep_defined" Fix.thy 
        "[|!x.rep`(abs`x)=x;!y.abs`(rep`y)=y; z~=UU|] ==> rep`z ~= UU"
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

qed_goal "isoabs_defined" Fix.thy 
        "[|!x.rep`(abs`x) = x;!y.abs`(rep`y)=y ; z~=UU|] ==> abs`z ~= UU"
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

qed_goalw "chfin2chfin"  Fix.thy  [chain_finite_def]
"!!f g.[|chain_finite(x::'a); !y.f`(g`y)=(y::'b) ; !x.g`(f`x)=(x::'a) |] \
\ ==> chain_finite(y::'b)"
 (fn prems =>
        [
        (rewtac max_in_chain_def),
        (strip_tac 1),
        (rtac exE 1),
        (res_inst_tac [("P","is_chain(%i.g`(Y i))")] mp 1),
        (etac spec 1),
        (etac ch2ch_fappR 1),
        (rtac exI 1),
        (strip_tac 1),
        (res_inst_tac [("s","f`(g`(Y x))"),("t","Y(x)")] subst 1),
        (etac spec 1),
        (res_inst_tac [("s","f`(g`(Y j))"),("t","Y(j)")] subst 1),
        (etac spec 1),
        (rtac cfun_arg_cong 1),
        (rtac mp 1),
        (etac spec 1),
        (atac 1)
        ]);

qed_goalw "flat2flat"  Fix.thy  [is_flat_def]
"!!f g.[|is_flat(x::'a); !y.f`(g`y)=(y::'b) ; !x.g`(f`x)=(x::'a) |] \
\ ==> is_flat(y::'b)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac disjE 1),
        (res_inst_tac [("P","g`x<<g`y")] mp 1),
        (etac monofun_cfun_arg 2),
        (dtac spec 1),
        (etac spec 1),
        (rtac disjI1 1),
        (rtac trans 1),
        (res_inst_tac [("s","f`(g`x)"),("t","x")] subst 1),
        (etac spec 1),
        (etac cfun_arg_cong 1),
        (rtac (iso_strict RS conjunct1) 1),
        (atac 1),
        (atac 1),
        (rtac disjI2 1),
        (res_inst_tac [("s","f`(g`x)"),("t","x")] subst 1),
        (etac spec 1),
        (res_inst_tac [("s","f`(g`y)"),("t","y")] subst 1),
        (etac spec 1),
        (etac cfun_arg_cong 1)
        ]);

(* ------------------------------------------------------------------------- *)
(* a result about functions with flat codomain                               *)
(* ------------------------------------------------------------------------- *)

qed_goalw "flat_codom" Fix.thy [is_flat_def]
"[|is_flat(y::'b);f`(x::'a)=(c::'b)|] ==> f`(UU::'a)=(UU::'b) | (!z.f`(z::'a)=c)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (case_tac "f`(x::'a)=(UU::'b)" 1),
        (rtac disjI1 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","f`(x)"),("t","UU::'b")] subst 1),
        (atac 1),
        (rtac (minimal RS monofun_cfun_arg) 1),
        (case_tac "f`(UU::'a)=(UU::'b)" 1),
        (etac disjI1 1),
        (rtac disjI2 1),
        (rtac allI 1),
        (res_inst_tac [("s","f`x"),("t","c")] subst 1),
        (atac 1),
        (res_inst_tac [("a","f`(UU::'a)")] (refl RS box_equals) 1),
        (etac allE 1),(etac allE 1),
        (dtac mp 1),
        (res_inst_tac [("fo","f")] (minimal RS monofun_cfun_arg) 1),
        (etac disjE 1),
        (contr_tac 1),
        (atac 1),
        (etac allE 1),
        (etac allE 1),
        (dtac mp 1),
        (res_inst_tac [("fo","f")] (minimal RS monofun_cfun_arg) 1),
        (etac disjE 1),
        (contr_tac 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* admissibility of special formulae and propagation                        *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_less"  Fix.thy [adm_def]
        "[|cont u;cont v|]==> adm(%x.u x << v x)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (etac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1),
        (atac 1),
        (etac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1),
        (atac 1),
        (rtac lub_mono 1),
        (cut_facts_tac prems 1),
        (etac (cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (cut_facts_tac prems 1),
        (etac (cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "adm_conj"  Fix.thy  
        "[| adm P; adm Q |] ==> adm(%x. P x & Q x)"
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

qed_goal "adm_cong"  Fix.thy  
        "(!x. P x = Q x) ==> adm P = adm Q "
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("s","P"),("t","Q")] subst 1),
        (rtac refl 2),
        (rtac ext 1),
        (etac spec 1)
        ]);

qed_goalw "adm_not_free"  Fix.thy [adm_def] "adm(%x.t)"
 (fn prems =>
        [
        (fast_tac HOL_cs 1)
        ]);

qed_goalw "adm_not_less"  Fix.thy [adm_def]
        "cont t ==> adm(%x.~ (t x) << u)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac contrapos 1),
        (etac spec 1),
        (rtac trans_less 1),
        (atac 2),
        (etac (cont2mono RS monofun_fun_arg) 1),
        (rtac is_ub_thelub 1),
        (atac 1)
        ]);

qed_goal "adm_all"  Fix.thy  
        " !y.adm(P y) ==> adm(%x.!y.P y x)"
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

bind_thm ("adm_all2", allI RS adm_all);

qed_goal "adm_subst"  Fix.thy  
        "[|cont t; adm P|] ==> adm(%x. P (t x))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (adm_def2 RS iffD2) 1),
        (strip_tac 1),
        (stac (cont2contlub RS contlubE RS spec RS mp) 1),
        (atac 1),
        (atac 1),
        (rtac (adm_def2 RS iffD1 RS spec RS mp RS mp) 1),
        (atac 1),
        (rtac (cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "adm_UU_not_less"  Fix.thy "adm(%x.~ UU << t(x))"
 (fn prems =>
        [
        (res_inst_tac [("P2","%x.False")] (adm_cong RS iffD1) 1),
        (Asm_simp_tac 1),
        (rtac adm_not_free 1)
        ]);

qed_goalw "adm_not_UU"  Fix.thy [adm_def] 
        "cont(t)==> adm(%x.~ (t x) = UU)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac contrapos 1),
        (etac spec 1),
        (rtac (chain_UU_I RS spec) 1),
        (rtac (cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (atac 1),
        (rtac (cont2contlub RS contlubE RS spec RS mp RS subst) 1),
        (atac 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "adm_eq"  Fix.thy 
        "[|cont u ; cont v|]==> adm(%x. u x = v x)"
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

local

  val adm_disj_lemma1 = prove_goal Pcpo.thy 
  "[| is_chain Y; !n.P (Y n) | Q(Y n)|]\
  \ ==> (? i.!j. i<j --> Q(Y(j))) | (!i.? j.i<j & P(Y(j)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);

  val adm_disj_lemma2 = prove_goal Fix.thy  
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

  val adm_disj_lemma3 = prove_goal Fix.thy
  "[| is_chain(Y); ! j. i < j --> Q(Y(j)) |] ==>\
  \         is_chain(%m. if m < Suc i then Y(Suc i) else Y m)"
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
        (Asm_simp_tac  1),
        (rtac iffI 1),
        (etac FalseE 2),
        (rtac notE 1),
        (etac less_not_sym 1),  
        (atac 1),
        (Asm_simp_tac 1),
        (etac (is_chainE RS spec) 1),
        (hyp_subst_tac 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (asm_simp_tac (!simpset addsimps [less_Suc_eq]) 1)
        ]);

  val adm_disj_lemma4 = prove_goal Fix.thy
  "[| ! j. i < j --> Q(Y(j)) |] ==>\
  \        ! n. Q( if n < Suc i then Y(Suc i) else Y n)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac allI 1),
        (res_inst_tac [("m","n"),("n","Suc(i)")] nat_less_cases 1),
        (res_inst_tac[("s","Y(Suc(i))"),
                      ("t","if n<Suc(i) then Y(Suc(i)) else Y n")] ssubst 1),
        (Asm_simp_tac 1),
        (etac allE 1),
        (rtac mp 1),
        (atac 1),
        (Asm_simp_tac 1),
        (res_inst_tac[("s","Y(n)"),
                      ("t","if n<Suc(i) then Y(Suc(i)) else Y(n)")] ssubst 1),
        (Asm_simp_tac 1),
        (hyp_subst_tac 1),
        (dtac spec 1),
        (rtac mp 1),
        (atac 1),
        (Asm_simp_tac 1),
        (res_inst_tac [("s","Y(n)"),
                       ("t","if n < Suc(i) then Y(Suc(i)) else Y(n)")]ssubst 1),
        (res_inst_tac [("s","False"),("t","n < Suc(i)")] ssubst 1),
        (rtac iffI 1),
        (etac FalseE 2),
        (rtac notE 1),
        (etac less_not_sym 1),  
        (atac 1),
        (Asm_simp_tac 1),
        (dtac spec 1),
        (rtac mp 1),
        (atac 1),
        (etac Suc_lessD 1)
        ]);

  val adm_disj_lemma5 = prove_goal Fix.thy
  "[| is_chain(Y::nat=>'a); ! j. i < j --> Q(Y(j)) |] ==>\
  \       lub(range(Y)) = lub(range(%m. if m< Suc(i) then Y(Suc(i)) else Y m))"
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
        (stac if_False 1),
        (rtac refl 1)
        ]);

  val adm_disj_lemma6 = prove_goal Fix.thy
  "[| is_chain(Y::nat=>'a); ? i. ! j. i < j --> Q(Y(j)) |] ==>\
  \         ? X. is_chain(X) & (! n. Q(X(n))) & lub(range(Y)) = lub(range(X))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exE 1),
        (res_inst_tac [("x","%m.if m<Suc(i) then Y(Suc(i)) else Y m")] exI 1),
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

  val adm_disj_lemma7 = prove_goal Fix.thy 
  "[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j))  |] ==>\
  \         is_chain(%m. Y(Least(%j. m<j & P(Y(j)))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_chainI 1),
        (rtac allI 1),
        (rtac chain_mono3 1),
        (atac 1),
        (rtac Least_le 1),
        (rtac conjI 1),
        (rtac Suc_lessD 1),
        (etac allE 1),
        (etac exE 1),
        (rtac (LeastI RS conjunct1) 1),
        (atac 1),
        (etac allE 1),
        (etac exE 1),
        (rtac (LeastI RS conjunct2) 1),
        (atac 1)
        ]);

  val adm_disj_lemma8 = prove_goal Fix.thy 
  "[| ! i. ? j. i < j & P(Y(j)) |] ==> ! m. P(Y(Least(%j. m<j & P(Y(j)))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (etac allE 1),
        (etac exE 1),
        (etac (LeastI RS conjunct2) 1)
        ]);

  val adm_disj_lemma9 = prove_goal Fix.thy
  "[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j)) |] ==>\
  \         lub(range(Y)) = lub(range(%m. Y(Least(%j. m<j & P(Y(j))))))"
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
        (rtac (LeastI RS conjunct1) 1),
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

  val adm_disj_lemma10 = prove_goal Fix.thy
  "[| is_chain(Y::nat=>'a); ! i. ? j. i < j & P(Y(j)) |] ==>\
  \         ? X. is_chain(X) & (! n. P(X(n))) & lub(range(Y)) = lub(range(X))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("x","%m. Y(Least(%j. m<j & P(Y(j))))")] exI 1),
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

  val adm_disj_lemma12 = prove_goal Fix.thy
  "[| adm(P); is_chain(Y);? i. ! j. i < j --> P(Y(j))|]==>P(lub(range(Y)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac adm_disj_lemma2 1),
        (etac adm_disj_lemma6 1),
        (atac 1)
        ]);

in

val adm_lemma11 = prove_goal Fix.thy
"[| adm(P); is_chain(Y); ! i. ? j. i < j & P(Y(j)) |]==>P(lub(range(Y)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac adm_disj_lemma2 1),
        (etac adm_disj_lemma10 1),
        (atac 1)
        ]);

val adm_disj = prove_goal Fix.thy  
        "[| adm P; adm Q |] ==> adm(%x.P x | Q x)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (adm_def2 RS iffD2) 1),
        (strip_tac 1),
        (rtac (adm_disj_lemma1 RS disjE) 1),
        (atac 1),
        (atac 1),
        (rtac disjI2 1),
        (etac adm_disj_lemma12 1),
        (atac 1),
        (atac 1),
        (rtac disjI1 1),
        (etac adm_lemma11 1),
        (atac 1),
        (atac 1)
        ]);

end;

bind_thm("adm_lemma11",adm_lemma11);
bind_thm("adm_disj",adm_disj);

qed_goal "adm_imp"  Fix.thy  
        "[| adm(%x.~(P x)); adm Q |] ==> adm(%x.P x --> Q x)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("P2","%x.~(P x)|Q x")] (adm_cong RS iffD1) 1),
        (fast_tac HOL_cs 1),
        (rtac adm_disj 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "adm_not_conj"  Fix.thy  
"[| adm (%x. ~ P x); adm (%x. ~ Q x) |] ==> adm (%x. ~ (P x & Q x))"(fn prems=>[
        cut_facts_tac prems 1,
        subgoal_tac 
        "(%x. ~ (P x & Q x)) = (%x. ~ P x | ~ Q x)" 1,
        rtac ext 2,
        fast_tac HOL_cs 2,
        etac ssubst 1,
        etac adm_disj 1,
        atac 1]);

val adm_thms = [adm_imp,adm_disj,adm_eq,adm_not_UU,adm_UU_not_less,
        adm_all2,adm_not_less,adm_not_free,adm_not_conj,adm_conj,adm_less];


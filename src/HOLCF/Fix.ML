(*  Title:      HOLCF/Fix.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for Fix.thy 
*)

open Fix;

(* ------------------------------------------------------------------------ *)
(* derive inductive properties of iterate from primitive recursion          *)
(* ------------------------------------------------------------------------ *)

qed_goal "iterate_0" thy "iterate 0 F x = x"
 (fn prems =>
        [
        (resolve_tac (nat_recs iterate_def) 1)
        ]);

qed_goal "iterate_Suc" thy "iterate (Suc n) F x  = F`(iterate n F x)"
 (fn prems =>
        [
        (resolve_tac (nat_recs iterate_def) 1)
        ]);

Addsimps [iterate_0, iterate_Suc];

qed_goal "iterate_Suc2" thy "iterate (Suc n) F x = iterate n F (F`x)"
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

qed_goalw "is_chain_iterate2" thy [is_chain] 
        " x << F`x ==> is_chain (%i. iterate i F x)"
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


qed_goal "is_chain_iterate" thy  
        "is_chain (%i. iterate i F UU)"
 (fn prems =>
        [
        (rtac is_chain_iterate2 1),
        (rtac minimal 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Kleene's fixed point theorems for continuous functions in pointed        *)
(* omega cpo's                                                              *)
(* ------------------------------------------------------------------------ *)


qed_goalw "Ifix_eq" thy  [Ifix_def] "Ifix F =F`(Ifix F)"
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


qed_goalw "Ifix_least" thy [Ifix_def] "F`x=x ==> Ifix(F) << x"
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

qed_goalw "monofun_iterate" thy  [monofun] "monofun(iterate(i))"
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

qed_goalw "contlub_iterate" thy  [contlub] "contlub(iterate(i))"
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


qed_goal "cont_iterate" thy "cont(iterate(i))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_iterate 1),
        (rtac contlub_iterate 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* a lemma about continuity of iterate in its third argument                *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_iterate2" thy "monofun(iterate n F)"
 (fn prems =>
        [
        (rtac monofunI 1),
        (strip_tac 1),
        (nat_ind_tac "n" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (etac monofun_cfun_arg 1)
        ]);

qed_goal "contlub_iterate2" thy "contlub(iterate n F)"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (nat_ind_tac "n" 1),
        (Simp_tac 1),
        (Simp_tac 1),
        (res_inst_tac [("t","iterate n F (lub(range(%u. Y u)))"),
        ("s","lub(range(%i. iterate n F (Y i)))")] ssubst 1),
        (atac 1),
        (rtac contlub_cfun_arg 1),
        (etac (monofun_iterate2 RS ch2ch_monofun) 1)
        ]);

qed_goal "cont_iterate2" thy "cont (iterate n F)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_iterate2 1),
        (rtac contlub_iterate2 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of Ifix                                      *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Ifix" thy  [monofun,Ifix_def] "monofun(Ifix)"
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

qed_goal "is_chain_iterate_lub" thy   
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

qed_goal "contlub_Ifix_lemma1" thy 
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


qed_goal "ex_lub_iterate" thy  "is_chain(Y) ==>\
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


qed_goalw "contlub_Ifix" thy  [contlub,Ifix_def] "contlub(Ifix)"
 (fn prems =>
        [
        (strip_tac 1),
        (stac (contlub_Ifix_lemma1 RS ext) 1),
        (atac 1),
        (etac ex_lub_iterate 1)
        ]);


qed_goal "cont_Ifix" thy "cont(Ifix)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Ifix 1),
        (rtac contlub_Ifix 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* propagate properties of Ifix to its continuous counterpart               *)
(* ------------------------------------------------------------------------ *)

qed_goalw "fix_eq" thy  [fix_def] "fix`F = F`(fix`F)"
 (fn prems =>
        [
        (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1),
        (rtac Ifix_eq 1)
        ]);

qed_goalw "fix_least" thy [fix_def] "F`x = x ==> fix`F << x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1),
        (etac Ifix_least 1)
        ]);


qed_goal "fix_eqI" thy
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


qed_goal "fix_eq2" thy "f == fix`F ==> f = F`f"
 (fn prems =>
        [
        (rewrite_goals_tac prems),
        (rtac fix_eq 1)
        ]);

qed_goal "fix_eq3" thy "f == fix`F ==> f`x = F`f`x"
 (fn prems =>
        [
        (rtac trans 1),
        (rtac ((hd prems) RS fix_eq2 RS cfun_fun_cong) 1),
        (rtac refl 1)
        ]);

fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i)); 

qed_goal "fix_eq4" thy "f = fix`F ==> f = F`f"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (hyp_subst_tac 1),
        (rtac fix_eq 1)
        ]);

qed_goal "fix_eq5" thy "f = fix`F ==> f`x = F`f`x"
 (fn prems =>
        [
        (rtac trans 1),
        (rtac ((hd prems) RS fix_eq4 RS cfun_fun_cong) 1),
        (rtac refl 1)
        ]);

fun fix_tac5 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq5) i)); 

(* proves the unfolding theorem for function equations f = fix`... *)
fun fix_prover thy fixeq s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fixeq RS fix_eq4) 1),
        (rtac trans 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ]);

(* proves the unfolding theorem for function definitions f == fix`... *)
fun fix_prover2 thy fixdef s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fix_eq2) 1),
        (rtac fixdef 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ]);

(* proves an application case for a function from its unfolding thm *)
fun case_prover thy unfold s = prove_goal thy s (fn prems => [
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(stac unfold 1),
	(Auto_tac ())
	]);

(* ------------------------------------------------------------------------ *)
(* better access to definitions                                             *)
(* ------------------------------------------------------------------------ *)


qed_goal "Ifix_def2" thy "Ifix=(%x. lub(range(%i. iterate i x UU)))"
 (fn prems =>
        [
        (rtac ext 1),
        (rewtac Ifix_def),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* direct connection between fix and iteration without Ifix                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "fix_def2" thy [fix_def]
 "fix`F = lub(range(%i. iterate i F UU))"
 (fn prems =>
        [
        (fold_goals_tac [Ifix_def]),
        (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Lemmas about admissibility and fixed point induction                     *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "admI" thy [adm_def]
        "(!!Y. [| is_chain(Y); !i. P(Y(i)) |] ==> P(lub(range(Y)))) ==> adm(P)"
 (fn prems => [fast_tac (HOL_cs addIs prems) 1]);

qed_goalw "admD" thy [adm_def]
        "!!P. [| adm(P); is_chain(Y); !i. P(Y(i)) |] ==> P(lub(range(Y)))"
 (fn prems => [fast_tac HOL_cs 1]);

qed_goalw "admw_def2" thy [admw_def]
        "admw(P) = (!F.(!n. P(iterate n F UU)) -->\
\                        P (lub(range(%i. iterate i F UU))))"
 (fn prems =>
        [
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* an admissible formula is also weak admissible                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_impl_admw"  thy [admw_def] "!!P. adm(P)==>admw(P)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac admD 1),
        (rtac is_chain_iterate 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* fixed point induction                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "fix_ind"  thy  
"[| adm(P);P(UU);!!x. P(x) ==> P(F`x)|] ==> P(fix`F)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac fix_def2 1),
        (etac admD 1),
        (rtac is_chain_iterate 1),
        (rtac allI 1),
        (nat_ind_tac "i" 1),
        (stac iterate_0 1),
        (atac 1),
        (stac iterate_Suc 1),
        (resolve_tac prems 1),
        (atac 1)
        ]);

qed_goal "def_fix_ind" thy "[| f == fix`F; adm(P); \
\       P(UU);!!x. P(x) ==> P(F`x)|] ==> P f" (fn prems => [
        (cut_facts_tac prems 1),
	(asm_simp_tac HOL_ss 1),
	(etac fix_ind 1),
	(atac 1),
	(eresolve_tac prems 1)]);
	
(* ------------------------------------------------------------------------ *)
(* computational induction for weak admissible formulae                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "wfix_ind"  thy  
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

qed_goal "def_wfix_ind" thy "[| f == fix`F; admw(P); \
\       !n. P(iterate n F UU) |] ==> P f" (fn prems => [
        (cut_facts_tac prems 1),
	(asm_simp_tac HOL_ss 1),
	(etac wfix_ind 1),
	(atac 1)]);

(* ------------------------------------------------------------------------ *)
(* for chain-finite (easy) types every formula is admissible                *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_max_in_chain"  thy  [adm_def]
"!Y. is_chain(Y::nat=>'a) --> (? n. max_in_chain n Y) ==> adm(P::'a=>bool)"
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

bind_thm ("adm_chain_finite" ,chfin RS adm_max_in_chain);

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chain_finite domain/range types	    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_chfindom" thy [adm_def] "adm (%(u::'a::cpo->'b::chfin). P(u`s))"
    (fn _ => [
	strip_tac 1,
	dtac chfin_fappR 1,
	eres_inst_tac [("x","s")] allE 1,
	fast_tac (HOL_cs addss (simpset() addsimps [chfin])) 1]);

(* adm_flat not needed any more, since it is a special case of adm_chfindom *)

(* ------------------------------------------------------------------------ *)
(* improved admisibility introduction                                       *)
(* ------------------------------------------------------------------------ *)

qed_goalw "admI2" thy [adm_def]
 "(!!Y. [| is_chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j |]\
\ ==> P(lub (range Y))) ==> adm P" 
 (fn prems => [
        strip_tac 1,
        etac increasing_chain_adm_lemma 1, atac 1,
        eresolve_tac prems 1, atac 1, atac 1]);


(* ------------------------------------------------------------------------ *)
(* admissibility of special formulae and propagation                        *)
(* ------------------------------------------------------------------------ *)

qed_goalw "adm_less"  thy [adm_def]
        "[|cont u;cont v|]==> adm(%x. u x << v x)"
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
Addsimps [adm_less];

qed_goal "adm_conj"  thy  
        "!!P. [| adm P; adm Q |] ==> adm(%x. P x & Q x)"
 (fn prems => [fast_tac (HOL_cs addEs [admD] addIs [admI]) 1]);
Addsimps [adm_conj];

qed_goalw "adm_not_free"  thy [adm_def] "adm(%x. t)"
 (fn prems => [fast_tac HOL_cs 1]);
Addsimps [adm_not_free];

qed_goalw "adm_not_less"  thy [adm_def]
        "!!t. cont t ==> adm(%x.~ (t x) << u)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac contrapos 1),
        (etac spec 1),
        (rtac trans_less 1),
        (atac 2),
        (etac (cont2mono RS monofun_fun_arg) 1),
        (rtac is_ub_thelub 1),
        (atac 1)
        ]);

qed_goal "adm_all" thy  
        "!!P. !y. adm(P y) ==> adm(%x.!y. P y x)"
 (fn prems => [fast_tac (HOL_cs addIs [admI] addEs [admD]) 1]);

bind_thm ("adm_all2", allI RS adm_all);

qed_goal "adm_subst"  thy  
        "!!P. [|cont t; adm P|] ==> adm(%x. P (t x))"
 (fn prems =>
        [
        (rtac admI 1),
        (stac (cont2contlub RS contlubE RS spec RS mp) 1),
        (atac 1),
        (atac 1),
        (etac admD 1),
        (etac (cont2mono RS ch2ch_monofun) 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "adm_UU_not_less"  thy "adm(%x.~ UU << t(x))"
 (fn prems => [Simp_tac 1]);

qed_goalw "adm_not_UU"  thy [adm_def] 
        "!!t. cont(t)==> adm(%x.~ (t x) = UU)"
 (fn prems =>
        [
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

qed_goal "adm_eq"  thy 
        "!!u. [|cont u ; cont v|]==> adm(%x. u x = v x)"
 (fn prems => [asm_simp_tac (simpset() addsimps [po_eq_conv]) 1]);



(* ------------------------------------------------------------------------ *)
(* admissibility for disjunction is hard to prove. It takes 10 Lemmas       *)
(* ------------------------------------------------------------------------ *)

local

  val adm_disj_lemma1 = prove_goal HOL.thy 
  "!n. P(Y n)|Q(Y n) ==> (? i.!j. R i j --> Q(Y(j))) | (!i.? j. R i j & P(Y(j)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);

  val adm_disj_lemma2 = prove_goal thy  
  "!!Q. [| adm(Q); ? X. is_chain(X) & (!n. Q(X(n))) &\
  \   lub(range(Y))=lub(range(X))|] ==> Q(lub(range(Y)))"
 (fn _ => [fast_tac (claset() addEs [admD] addss simpset()) 1]);

  val adm_disj_lemma3 = prove_goalw thy [is_chain]
  "!!Q. is_chain(Y) ==> is_chain(%m. if m < Suc i then Y(Suc i) else Y m)"
 (fn _ =>
        [
        asm_simp_tac (simpset() setloop (split_tac[expand_if])) 1,
        safe_tac HOL_cs,
        subgoal_tac "ia = i" 1,
        Asm_simp_tac 1,
        trans_tac 1
        ]);

  val adm_disj_lemma4 = prove_goal Nat.thy
  "!!Q. !j. i < j --> Q(Y(j))  ==> !n. Q( if n < Suc i then Y(Suc i) else Y n)"
 (fn _ =>
        [
        asm_simp_tac (simpset() setloop (split_tac[expand_if])) 1,
        strip_tac 1,
        etac allE 1,
        etac mp 1,
        trans_tac 1
        ]);

  val adm_disj_lemma5 = prove_goal thy
  "!!Y::nat=>'a::cpo. [| is_chain(Y); ! j. i < j --> Q(Y(j)) |] ==>\
  \       lub(range(Y)) = lub(range(%m. if m< Suc(i) then Y(Suc(i)) else Y m))"
 (fn prems =>
        [
        safe_tac (HOL_cs addSIs [lub_equal2,adm_disj_lemma3]),
        atac 2,
        asm_simp_tac (simpset() setloop (split_tac[expand_if])) 1,
        res_inst_tac [("x","i")] exI 1,
        strip_tac 1,
        trans_tac 1
        ]);

  val adm_disj_lemma6 = prove_goal thy
  "[| is_chain(Y::nat=>'a::cpo); ? i. ! j. i < j --> Q(Y(j)) |] ==>\
  \         ? X. is_chain(X) & (! n. Q(X(n))) & lub(range(Y)) = lub(range(X))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exE 1),
        (res_inst_tac [("x","%m. if m<Suc(i) then Y(Suc(i)) else Y m")] exI 1),
        (rtac conjI 1),
        (rtac adm_disj_lemma3 1),
        (atac 1),
        (rtac conjI 1),
        (rtac adm_disj_lemma4 1),
        (atac 1),
        (rtac adm_disj_lemma5 1),
        (atac 1),
        (atac 1)
        ]);

  val adm_disj_lemma7 = prove_goal thy 
  "[| is_chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j))  |] ==>\
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

  val adm_disj_lemma8 = prove_goal thy 
  "[| ! i. ? j. i < j & P(Y(j)) |] ==> ! m. P(Y(LEAST j::nat. m<j & P(Y(j))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (etac allE 1),
        (etac exE 1),
        (etac (LeastI RS conjunct2) 1)
        ]);

  val adm_disj_lemma9 = prove_goal thy
  "[| is_chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==>\
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

  val adm_disj_lemma10 = prove_goal thy
  "[| is_chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==>\
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

  val adm_disj_lemma12 = prove_goal thy
  "[| adm(P); is_chain(Y);? i. ! j. i < j --> P(Y(j))|]==>P(lub(range(Y)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac adm_disj_lemma2 1),
        (etac adm_disj_lemma6 1),
        (atac 1)
        ]);

in

val adm_lemma11 = prove_goal thy
"[| adm(P); is_chain(Y); ! i. ? j. i < j & P(Y(j)) |]==>P(lub(range(Y)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac adm_disj_lemma2 1),
        (etac adm_disj_lemma10 1),
        (atac 1)
        ]);

val adm_disj = prove_goal thy  
        "!!P. [| adm P; adm Q |] ==> adm(%x. P x | Q x)"
 (fn prems =>
        [
        (rtac admI 1),
        (rtac (adm_disj_lemma1 RS disjE) 1),
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

qed_goal "adm_imp"  thy  
        "!!P. [| adm(%x.~(P x)); adm Q |] ==> adm(%x. P x --> Q x)"
 (fn prems =>
        [
        (subgoal_tac "(%x. P x --> Q x) = (%x. ~P x | Q x)" 1),
         (Asm_simp_tac 1),
         (etac adm_disj 1),
         (atac 1),
        (rtac ext 1),
        (fast_tac HOL_cs 1)
        ]);

goal Fix.thy "!! P. [| adm (%x. P x --> Q x); adm (%x. Q x --> P x) |] \
\           ==> adm (%x. P x = Q x)";
by (subgoal_tac "(%x. P x = Q x) = (%x. (P x --> Q x) & (Q x --> P x))" 1);
by (Asm_simp_tac 1);
by (rtac ext 1);
by (fast_tac HOL_cs 1);
qed"adm_iff";


qed_goal "adm_not_conj"  thy  
"[| adm (%x. ~ P x); adm (%x. ~ Q x) |] ==> adm (%x. ~ (P x & Q x))"(fn prems=>[
        cut_facts_tac prems 1,
        subgoal_tac 
        "(%x. ~ (P x & Q x)) = (%x. ~ P x | ~ Q x)" 1,
        rtac ext 2,
        fast_tac HOL_cs 2,
        etac ssubst 1,
        etac adm_disj 1,
        atac 1]);

val adm_lemmas = [adm_imp,adm_disj,adm_eq,adm_not_UU,adm_UU_not_less,
        adm_all2,adm_not_less,adm_not_free,adm_not_conj,adm_conj,adm_less,
        adm_iff];

Addsimps adm_lemmas;

(*  Title:      HOLCF/Fix.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

fixed point operator and admissibility
*)

(* ------------------------------------------------------------------------ *)
(* derive inductive properties of iterate from primitive recursion          *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "iterate (Suc n) F x = iterate n F (F`x)";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (stac iterate_Suc 1);
by (stac iterate_Suc 1);
by (etac ssubst 1);
by (rtac refl 1);
qed "iterate_Suc2";

(* ------------------------------------------------------------------------ *)
(* the sequence of function itertaions is a chain                           *)
(* This property is essential since monotonicity of iterate makes no sense  *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [chain] 
        " x << F`x ==> chain (%i. iterate i F x)";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (Simp_tac 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac monofun_cfun_arg 1);
qed "chain_iterate2";


val prems = goal thy  
        "chain (%i. iterate i F UU)";
by (rtac chain_iterate2 1);
by (rtac minimal 1);
qed "chain_iterate";


(* ------------------------------------------------------------------------ *)
(* Kleene's fixed point theorems for continuous functions in pointed        *)
(* omega cpo's                                                              *)
(* ------------------------------------------------------------------------ *)


val prems = goalw thy [Ifix_def] "Ifix F =F`(Ifix F)";
by (stac contlub_cfun_arg 1);
by (rtac chain_iterate 1);
by (rtac antisym_less 1);
by (rtac lub_mono 1);
by (rtac chain_iterate 1);
by (rtac ch2ch_Rep_CFunR 1);
by (rtac chain_iterate 1);
by (rtac allI 1);
by (rtac (iterate_Suc RS subst) 1);
by (rtac (chain_iterate RS chainE RS spec) 1);
by (rtac is_lub_thelub 1);
by (rtac ch2ch_Rep_CFunR 1);
by (rtac chain_iterate 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
by (rtac (iterate_Suc RS subst) 1);
by (rtac is_ub_thelub 1);
by (rtac chain_iterate 1);
qed "Ifix_eq";


val prems = goalw thy [Ifix_def] "F`x=x ==> Ifix(F) << x";
by (cut_facts_tac prems 1);
by (rtac is_lub_thelub 1);
by (rtac chain_iterate 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("t","x")] subst 1);
by (atac 1);
by (etac monofun_cfun_arg 1);
qed "Ifix_least";


(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of iterate                                   *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun] "monofun(iterate(i))";
by (strip_tac 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [less_fun, monofun_cfun]) 1);
qed "monofun_iterate";

(* ------------------------------------------------------------------------ *)
(* the following lemma uses contlub_cfun which itself is based on a         *)
(* diagonalisation lemma for continuous functions with two arguments.       *)
(* In this special case it is the application function Rep_CFun                 *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [contlub] "contlub(iterate(i))";
by (strip_tac 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (rtac (lub_const RS thelubI RS sym) 1);
by (asm_simp_tac (simpset() delsimps [range_composition]) 1);
by (rtac ext 1);
by (stac thelub_fun 1);
by (rtac chainI 1);
by (rtac allI 1);
by (rtac (less_fun RS iffD2) 1);
by (rtac allI 1);
by (rtac (chainE RS spec) 1);
by (rtac (monofun_Rep_CFun1 RS ch2ch_MF2LR) 1);
by (rtac allI 1);
by (rtac monofun_Rep_CFun2 1);
by (atac 1);
by (rtac ch2ch_fun 1);
by (rtac (monofun_iterate RS ch2ch_monofun) 1);
by (atac 1);
by (stac thelub_fun 1);
by (rtac (monofun_iterate RS ch2ch_monofun) 1);
by (atac 1);
by (rtac contlub_cfun  1);
by (atac 1);
by (etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1);
qed "contlub_iterate";


val prems = goal thy "cont(iterate(i))";
by (rtac monocontlub2cont 1);
by (rtac monofun_iterate 1);
by (rtac contlub_iterate 1);
qed "cont_iterate";

(* ------------------------------------------------------------------------ *)
(* a lemma about continuity of iterate in its third argument                *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "monofun(iterate n F)";
by (rtac monofunI 1);
by (strip_tac 1);
by (induct_tac "n" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (etac monofun_cfun_arg 1);
qed "monofun_iterate2";

Goal "contlub(iterate n F)";
by (rtac contlubI 1);
by (strip_tac 1);
by (induct_tac "n" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (res_inst_tac [("t","iterate n F (lub(range(%u. Y u)))"),
                  ("s","lub(range(%i. iterate n F (Y i)))")] ssubst 1);
by (atac 1);
by (rtac contlub_cfun_arg 1);
by (etac (monofun_iterate2 RS ch2ch_monofun) 1);
qed "contlub_iterate2";

val prems = goal thy "cont (iterate n F)";
by (rtac monocontlub2cont 1);
by (rtac monofun_iterate2 1);
by (rtac contlub_iterate2 1);
qed "cont_iterate2";

(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of Ifix                                      *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun,Ifix_def] "monofun(Ifix)";
by (strip_tac 1);
by (rtac lub_mono 1);
by (rtac chain_iterate 1);
by (rtac chain_iterate 1);
by (rtac allI 1);
by (rtac (less_fun RS iffD1 RS spec) 1 THEN
    etac (monofun_iterate RS monofunE RS spec RS spec RS mp) 1);
qed "monofun_Ifix";

(* ------------------------------------------------------------------------ *)
(* since iterate is not monotone in its first argument, special lemmas must *)
(* be derived for lubs in this argument                                     *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy   
"chain(Y) ==> chain(%i. lub(range(%ia. iterate ia (Y i) UU)))";
by (cut_facts_tac prems 1);
by (rtac chainI 1);
by (strip_tac 1);
by (rtac lub_mono 1);
by (rtac chain_iterate 1);
by (rtac chain_iterate 1);
by (strip_tac 1);
by (etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun RS chainE RS spec) 1);
qed "chain_iterate_lub";

(* ------------------------------------------------------------------------ *)
(* this exchange lemma is analog to the one for monotone functions          *)
(* observe that monotonicity is not really needed. The propagation of       *)
(* chains is the essential argument which is usually derived from monot.    *)
(* ------------------------------------------------------------------------ *)

Goal
 "chain(Y) ==>iterate n (lub(range Y)) y = lub(range(%i. iterate n (Y i) y))";
by (rtac (thelub_fun RS subst) 1);
by (etac (monofun_iterate RS ch2ch_monofun) 1);
by (asm_simp_tac (simpset() addsimps [contlub_iterate RS contlubE]) 1);
qed "contlub_Ifix_lemma1";


val prems = goal thy  "chain(Y) ==>\
\         lub(range(%i. lub(range(%ia. iterate i (Y ia) UU)))) =\
\         lub(range(%i. lub(range(%ia. iterate ia (Y i) UU))))";
by (cut_facts_tac prems 1);
by (rtac antisym_less 1);
by (rtac is_lub_thelub 1);
by (rtac (contlub_Ifix_lemma1 RS ext RS subst) 1);
by (atac 1);
by (rtac chain_iterate 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (rtac lub_mono 1);
by (etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1);
by (etac chain_iterate_lub 1);
by (strip_tac 1);
by (rtac is_ub_thelub 1);
by (rtac chain_iterate 1);
by (rtac is_lub_thelub 1);
by (etac chain_iterate_lub 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (rtac lub_mono 1);
by (rtac chain_iterate 1);
by (rtac (contlub_Ifix_lemma1 RS ext RS subst) 1);
by (atac 1);
by (rtac chain_iterate 1);
by (strip_tac 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_iterate RS ch2ch_monofun RS ch2ch_fun) 1);
qed "ex_lub_iterate";


val prems = goalw thy [contlub,Ifix_def] "contlub(Ifix)";
by (strip_tac 1);
by (stac (contlub_Ifix_lemma1 RS ext) 1);
by (atac 1);
by (etac ex_lub_iterate 1);
qed "contlub_Ifix";


val prems = goal thy "cont(Ifix)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Ifix 1);
by (rtac contlub_Ifix 1);
qed "cont_Ifix";

(* ------------------------------------------------------------------------ *)
(* propagate properties of Ifix to its continuous counterpart               *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [fix_def] "fix`F = F`(fix`F)";
by (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1);
by (rtac Ifix_eq 1);
qed "fix_eq";

val prems = goalw thy [fix_def] "F`x = x ==> fix`F << x";
by (cut_facts_tac prems 1);
by (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1);
by (etac Ifix_least 1);
qed "fix_least";


val prems = goal thy
"[| F`x = x; !z. F`z = z --> x << z |] ==> x = fix`F";
by (cut_facts_tac prems 1);
by (rtac antisym_less 1);
by (etac allE 1);
by (etac mp 1);
by (rtac (fix_eq RS sym) 1);
by (etac fix_least 1);
qed "fix_eqI";


val prems = goal thy "f == fix`F ==> f = F`f";
by (rewrite_goals_tac prems);
by (rtac fix_eq 1);
qed "fix_eq2";

val prems = goal thy "f == fix`F ==> f`x = F`f`x";
by (rtac trans 1);
by (rtac ((hd prems) RS fix_eq2 RS cfun_fun_cong) 1);
by (rtac refl 1);
qed "fix_eq3";

fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i)); 

val prems = goal thy "f = fix`F ==> f = F`f";
by (cut_facts_tac prems 1);
by (hyp_subst_tac 1);
by (rtac fix_eq 1);
qed "fix_eq4";

val prems = goal thy "f = fix`F ==> f`x = F`f`x";
by (rtac trans 1);
by (rtac ((hd prems) RS fix_eq4 RS cfun_fun_cong) 1);
by (rtac refl 1);
qed "fix_eq5";

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
	Auto_tac
	]);

(* ------------------------------------------------------------------------ *)
(* better access to definitions                                             *)
(* ------------------------------------------------------------------------ *)


val prems = goal thy "Ifix=(%x. lub(range(%i. iterate i x UU)))";
by (rtac ext 1);
by (rewtac Ifix_def);
by (rtac refl 1);
qed "Ifix_def2";

(* ------------------------------------------------------------------------ *)
(* direct connection between fix and iteration without Ifix                 *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [fix_def]
 "fix`F = lub(range(%i. iterate i F UU))";
by (fold_goals_tac [Ifix_def]);
by (asm_simp_tac (simpset() addsimps [cont_Ifix]) 1);
qed "fix_def2";


(* ------------------------------------------------------------------------ *)
(* Lemmas about admissibility and fixed point induction                     *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [adm_def]
        "(!!Y. [| chain(Y); !i. P(Y(i)) |] ==> P(lub(range(Y)))) ==> adm(P)";
by (fast_tac (HOL_cs addIs prems) 1);
qed "admI";

Goalw [adm_def] "[| adm(P); chain(Y); !i. P(Y(i)) |] ==> P(lub(range(Y)))";
by (Blast_tac 1);
qed "admD";

val prems = goalw thy [admw_def]
        "admw(P) = (!F.(!n. P(iterate n F UU)) -->\
\                        P (lub(range(%i. iterate i F UU))))";
by (rtac refl 1);
qed "admw_def2";

(* ------------------------------------------------------------------------ *)
(* an admissible formula is also weak admissible                            *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [admw_def] "!!P. adm(P)==>admw(P)";
by (strip_tac 1);
by (etac admD 1);
by (rtac chain_iterate 1);
by (atac 1);
qed "adm_impl_admw";

(* ------------------------------------------------------------------------ *)
(* fixed point induction                                                    *)
(* ------------------------------------------------------------------------ *)

val prems = goal  thy  
"[| adm(P);P(UU);!!x. P(x) ==> P(F`x)|] ==> P(fix`F)";
by (cut_facts_tac prems 1);
by (stac fix_def2 1);
by (etac admD 1);
by (rtac chain_iterate 1);
by (rtac allI 1);
by (induct_tac "i" 1);
by (stac iterate_0 1);
by (atac 1);
by (stac iterate_Suc 1);
by (resolve_tac prems 1);
by (atac 1);
qed "fix_ind";

val prems = goal thy "[| f == fix`F; adm(P); \
\       P(UU);!!x. P(x) ==> P(F`x)|] ==> P f";
by (cut_facts_tac prems 1);
by (asm_simp_tac HOL_ss 1);
by (etac fix_ind 1);
by (atac 1);
by (eresolve_tac prems 1);
qed "def_fix_ind";
	
(* ------------------------------------------------------------------------ *)
(* computational induction for weak admissible formulae                     *)
(* ------------------------------------------------------------------------ *)

val prems = goal  thy  
"[| admw(P); !n. P(iterate n F UU)|] ==> P(fix`F)";
by (cut_facts_tac prems 1);
by (stac fix_def2 1);
by (rtac (admw_def2 RS iffD1 RS spec RS mp) 1);
by (atac 1);
by (rtac allI 1);
by (etac spec 1);
qed "wfix_ind";

val prems = goal thy "[| f == fix`F; admw(P); \
\       !n. P(iterate n F UU) |] ==> P f";
by (cut_facts_tac prems 1);
by (asm_simp_tac HOL_ss 1);
by (etac wfix_ind 1);
by (atac 1);
qed "def_wfix_ind";

(* ------------------------------------------------------------------------ *)
(* for chain-finite (easy) types every formula is admissible                *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [adm_def]
"!Y. chain(Y::nat=>'a) --> (? n. max_in_chain n Y) ==> adm(P::'a=>bool)";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (rtac exE 1);
by (rtac mp 1);
by (etac spec 1);
by (atac 1);
by (stac (lub_finch1 RS thelubI) 1);
by (atac 1);
by (atac 1);
by (etac spec 1);
qed "adm_max_in_chain";

bind_thm ("adm_chfin" ,chfin RS adm_max_in_chain);

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chfin domain/range types	    *)
(* ------------------------------------------------------------------------ *)

val _ = goalw thy [adm_def] "adm (%(u::'a::cpo->'b::chfin). P(u`s))";
by (strip_tac 1);
by (dtac chfin_Rep_CFunR 1);
by (eres_inst_tac [("x","s")] allE 1);
by (fast_tac (HOL_cs addss (simpset() addsimps [chfin])) 1);
qed "adm_chfindom";

(* adm_flat not needed any more, since it is a special case of adm_chfindom *)

(* ------------------------------------------------------------------------ *)
(* improved admisibility introduction                                       *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [adm_def]
 "(!!Y. [| chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j |]\
\ ==> P(lub (range Y))) ==> adm P";
by (strip_tac 1);
by (etac increasing_chain_adm_lemma 1);
by (atac 1);
by (eresolve_tac prems 1);
by (atac 1);
by (atac 1);
qed "admI2";


(* ------------------------------------------------------------------------ *)
(* admissibility of special formulae and propagation                        *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [adm_def]
        "[|cont u;cont v|]==> adm(%x. u x << v x)";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (etac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1);
by (atac 1);
by (etac (cont2contlub RS contlubE RS spec RS mp RS ssubst) 1);
by (atac 1);
by (rtac lub_mono 1);
by (cut_facts_tac prems 1);
by (etac (cont2mono RS ch2ch_monofun) 1);
by (atac 1);
by (cut_facts_tac prems 1);
by (etac (cont2mono RS ch2ch_monofun) 1);
by (atac 1);
by (atac 1);
qed "adm_less";
Addsimps [adm_less];

val prems = goal  thy  
        "!!P. [| adm P; adm Q |] ==> adm(%x. P x & Q x)";
by (fast_tac (HOL_cs addEs [admD] addIs [admI]) 1);
qed "adm_conj";
Addsimps [adm_conj];

val prems = goalw thy [adm_def] "adm(%x. t)";
by (fast_tac HOL_cs 1);
qed "adm_not_free";
Addsimps [adm_not_free];

val prems = goalw thy [adm_def]
        "!!t. cont t ==> adm(%x.~ (t x) << u)";
by (strip_tac 1);
by (rtac contrapos 1);
by (etac spec 1);
by (rtac trans_less 1);
by (atac 2);
by (etac (cont2mono RS monofun_fun_arg) 1);
by (rtac is_ub_thelub 1);
by (atac 1);
qed "adm_not_less";

val prems = goal thy  
        "!!P. !y. adm(P y) ==> adm(%x.!y. P y x)";
by (fast_tac (HOL_cs addIs [admI] addEs [admD]) 1);
qed "adm_all";

bind_thm ("adm_all2", allI RS adm_all);

val prems = goal  thy  
        "!!P. [|cont t; adm P|] ==> adm(%x. P (t x))";
by (rtac admI 1);
by (stac (cont2contlub RS contlubE RS spec RS mp) 1);
by (atac 1);
by (atac 1);
by (etac admD 1);
by (etac (cont2mono RS ch2ch_monofun) 1);
by (atac 1);
by (atac 1);
qed "adm_subst";

val prems = goal  thy "adm(%x.~ UU << t(x))";
by (Simp_tac 1);
qed "adm_UU_not_less";


Goalw [adm_def] "cont(t)==> adm(%x.~ (t x) = UU)";
by (strip_tac 1);
by (rtac contrapos 1);
by (etac spec 1);
by (rtac (chain_UU_I RS spec) 1);
by (etac (cont2mono RS ch2ch_monofun) 1);
by (atac 1);
by (etac (cont2contlub RS contlubE RS spec RS mp RS subst) 1);
by (atac 1);
by (atac 1);
qed "adm_not_UU";

Goal "[|cont u ; cont v|]==> adm(%x. u x = v x)";
by (asm_simp_tac (simpset() addsimps [po_eq_conv]) 1);
qed "adm_eq";



(* ------------------------------------------------------------------------ *)
(* admissibility for disjunction is hard to prove. It takes 10 Lemmas       *)
(* ------------------------------------------------------------------------ *)


val prems = goal HOL.thy 
  "!n. P(Y n)|Q(Y n) ==> (? i.!j. R i j --> Q(Y(j))) | (!i.? j. R i j & P(Y(j)))";
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
qed "adm_disj_lemma1";

val _ = goal thy  
  "!!Q. [| adm(Q); ? X. chain(X) & (!n. Q(X(n))) &\
  \   lub(range(Y))=lub(range(X))|] ==> Q(lub(range(Y)))";
by (fast_tac (claset() addEs [admD] addss simpset()) 1);
qed "adm_disj_lemma2";

val _ = goalw thy [chain]
  "!!Q. chain(Y) ==> chain(%m. if m < Suc i then Y(Suc i) else Y m)";
by (Asm_simp_tac 1);
by (safe_tac HOL_cs);
by (subgoal_tac "ia = i" 1);
by (ALLGOALS Asm_simp_tac);
qed "adm_disj_lemma3";

val _ = goal Arith.thy
  "!!Q. !j. i < j --> Q(Y(j))  ==> !n. Q( if n < Suc i then Y(Suc i) else Y n)";
by (asm_simp_tac (simpset_of Arith.thy) 1);
qed "adm_disj_lemma4";

val prems = goal thy
  "!!Y::nat=>'a::cpo. [| chain(Y); ! j. i < j --> Q(Y(j)) |] ==>\
  \       lub(range(Y)) = lub(range(%m. if m< Suc(i) then Y(Suc(i)) else Y m))";
by (safe_tac (HOL_cs addSIs [lub_equal2,adm_disj_lemma3]));
by (atac 2);
by (res_inst_tac [("x","i")] exI 1);
by (Asm_simp_tac 1);
qed "adm_disj_lemma5";

val prems = goal thy
  "[| chain(Y::nat=>'a::cpo); ? i. ! j. i < j --> Q(Y(j)) |] ==>\
  \         ? X. chain(X) & (! n. Q(X(n))) & lub(range(Y)) = lub(range(X))";
by (cut_facts_tac prems 1);
by (etac exE 1);
by (res_inst_tac [("x","%m. if m<Suc(i) then Y(Suc(i)) else Y m")] exI 1);
by (rtac conjI 1);
by (rtac adm_disj_lemma3 1);
by (atac 1);
by (rtac conjI 1);
by (rtac adm_disj_lemma4 1);
by (atac 1);
by (rtac adm_disj_lemma5 1);
by (atac 1);
by (atac 1);
qed "adm_disj_lemma6";

val prems = goal thy 
  "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j))  |] ==>\
  \         chain(%m. Y(Least(%j. m<j & P(Y(j)))))";
by (cut_facts_tac prems 1);
by (rtac chainI 1);
by (rtac allI 1);
by (rtac chain_mono3 1);
by (atac 1);
by (rtac Least_le 1);
by (rtac conjI 1);
by (rtac Suc_lessD 1);
by (etac allE 1);
by (etac exE 1);
by (rtac (LeastI RS conjunct1) 1);
by (atac 1);
by (etac allE 1);
by (etac exE 1);
by (rtac (LeastI RS conjunct2) 1);
by (atac 1);
qed "adm_disj_lemma7";

val prems = goal thy 
  "[| ! i. ? j. i < j & P(Y(j)) |] ==> ! m. P(Y(LEAST j::nat. m<j & P(Y(j))))";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (etac allE 1);
by (etac exE 1);
by (etac (LeastI RS conjunct2) 1);
qed "adm_disj_lemma8";

val prems = goal thy
  "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==>\
  \         lub(range(Y)) = lub(range(%m. Y(Least(%j. m<j & P(Y(j))))))";
by (cut_facts_tac prems 1);
by (rtac antisym_less 1);
by (rtac lub_mono 1);
by (atac 1);
by (rtac adm_disj_lemma7 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac (chain_mono RS mp) 1);
by (atac 1);
by (etac allE 1);
by (etac exE 1);
by (rtac (LeastI RS conjunct1) 1);
by (atac 1);
by (rtac lub_mono3 1);
by (rtac adm_disj_lemma7 1);
by (atac 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac exI 1);
by (rtac (chain_mono RS mp) 1);
by (atac 1);
by (rtac lessI 1);
qed "adm_disj_lemma9";

val prems = goal thy
  "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==>\
  \         ? X. chain(X) & (! n. P(X(n))) & lub(range(Y)) = lub(range(X))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("x","%m. Y(Least(%j. m<j & P(Y(j))))")] exI 1);
by (rtac conjI 1);
by (rtac adm_disj_lemma7 1);
by (atac 1);
by (atac 1);
by (rtac conjI 1);
by (rtac adm_disj_lemma8 1);
by (atac 1);
by (rtac adm_disj_lemma9 1);
by (atac 1);
by (atac 1);
qed "adm_disj_lemma10";

val prems = goal thy
  "[| adm(P); chain(Y);? i. ! j. i < j --> P(Y(j))|]==>P(lub(range(Y)))";
by (cut_facts_tac prems 1);
by (etac adm_disj_lemma2 1);
by (etac adm_disj_lemma6 1);
by (atac 1);
qed "adm_disj_lemma12";


val prems = goal thy
"[| adm(P); chain(Y); ! i. ? j. i < j & P(Y(j)) |]==>P(lub(range(Y)))";
by (cut_facts_tac prems 1);
by (etac adm_disj_lemma2 1);
by (etac adm_disj_lemma10 1);
by (atac 1);
qed "adm_lemma11";

val prems = goal thy  
        "!!P. [| adm P; adm Q |] ==> adm(%x. P x | Q x)";
by (rtac admI 1);
by (rtac (adm_disj_lemma1 RS disjE) 1);
by (atac 1);
by (rtac disjI2 1);
by (etac adm_disj_lemma12 1);
by (atac 1);
by (atac 1);
by (rtac disjI1 1);
by (etac adm_lemma11 1);
by (atac 1);
by (atac 1);
qed "adm_disj";


bind_thm("adm_lemma11",adm_lemma11);
bind_thm("adm_disj",adm_disj);

val prems = goal  thy  
        "!!P. [| adm(%x.~(P x)); adm Q |] ==> adm(%x. P x --> Q x)";
by (subgoal_tac "(%x. P x --> Q x) = (%x. ~P x | Q x)" 1);
by (etac ssubst 1);
by (etac adm_disj 1);
by (atac 1);
by (Simp_tac 1);
qed "adm_imp";

Goal "[| adm (%x. P x --> Q x); adm (%x. Q x --> P x) |] \
\           ==> adm (%x. P x = Q x)";
by (subgoal_tac "(%x. P x = Q x) = (%x. (P x --> Q x) & (Q x --> P x))" 1);
by (Asm_simp_tac 1);
by (rtac ext 1);
by (fast_tac HOL_cs 1);
qed"adm_iff";


val prems= goal  thy  
"[| adm (%x. ~ P x); adm (%x. ~ Q x) |] ==> adm (%x. ~ (P x & Q x))";
by (cut_facts_tac prems 1);
by (subgoal_tac "(%x. ~ (P x & Q x)) = (%x. ~ P x | ~ Q x)" 1);
by (rtac ext 2);
by (fast_tac HOL_cs 2);
by (etac ssubst 1);
by (etac adm_disj 1);
by (atac 1);
qed "adm_not_conj";

bind_thms ("adm_lemmas", [adm_imp,adm_disj,adm_eq,adm_not_UU,adm_UU_not_less,
        adm_all2,adm_not_less,adm_not_conj,adm_iff]);

Addsimps adm_lemmas;

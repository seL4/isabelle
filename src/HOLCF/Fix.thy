(*  Title:      HOLCF/Fix.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

definitions for fixed point operator and admissibility
*)

header {* Fixed point operator and admissibility *}

theory Fix
imports Cfun
begin

consts

iterate	:: "nat=>('a->'a)=>'a=>'a"
Ifix	:: "('a->'a)=>'a"
"fix"	:: "('a->'a)->'a"
adm		:: "('a::cpo=>bool)=>bool"
admw		:: "('a=>bool)=>bool"

primrec
  iterate_0:   "iterate 0 F x = x"
  iterate_Suc: "iterate (Suc n) F x  = F$(iterate n F x)"

defs

Ifix_def:      "Ifix F == lub(range(%i. iterate i F UU))"
fix_def:       "fix == (LAM f. Ifix f)"

adm_def:       "adm P == !Y. chain(Y) --> 
                        (!i. P(Y i)) --> P(lub(range Y))"

admw_def:      "admw P == !F. (!n. P (iterate n F UU)) -->
                            P (lub(range (%i. iterate i F UU)))" 

(*  Title:      HOLCF/Fix.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

fixed point operator and admissibility
*)

(* ------------------------------------------------------------------------ *)
(* derive inductive properties of iterate from primitive recursion          *)
(* ------------------------------------------------------------------------ *)

lemma iterate_Suc2: "iterate (Suc n) F x = iterate n F (F$x)"
apply (induct_tac "n")
apply auto
done

(* ------------------------------------------------------------------------ *)
(* the sequence of function itertaions is a chain                           *)
(* This property is essential since monotonicity of iterate makes no sense  *)
(* ------------------------------------------------------------------------ *)

lemma chain_iterate2: "x << F$x ==> chain (%i. iterate i F x)"

apply (unfold chain_def)
apply (intro strip)
apply (induct_tac "i")
apply auto
apply (erule monofun_cfun_arg)
done


lemma chain_iterate: "chain (%i. iterate i F UU)"
apply (rule chain_iterate2)
apply (rule minimal)
done


(* ------------------------------------------------------------------------ *)
(* Kleene's fixed point theorems for continuous functions in pointed        *)
(* omega cpo's                                                              *)
(* ------------------------------------------------------------------------ *)


lemma Ifix_eq: "Ifix F =F$(Ifix F)"


apply (unfold Ifix_def)
apply (subst contlub_cfun_arg)
apply (rule chain_iterate)
apply (rule antisym_less)
apply (rule lub_mono)
apply (rule chain_iterate)
apply (rule ch2ch_Rep_CFunR)
apply (rule chain_iterate)
apply (rule allI)
apply (rule iterate_Suc [THEN subst])
apply (rule chain_iterate [THEN chainE])
apply (rule is_lub_thelub)
apply (rule ch2ch_Rep_CFunR)
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (rule iterate_Suc [THEN subst])
apply (rule is_ub_thelub)
apply (rule chain_iterate)
done


lemma Ifix_least: "F$x=x ==> Ifix(F) << x"

apply (unfold Ifix_def)
apply (rule is_lub_thelub)
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (induct_tac "i")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (rule_tac t = "x" in subst)
apply assumption
apply (erule monofun_cfun_arg)
done


(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of iterate                                   *)
(* ------------------------------------------------------------------------ *)

lemma monofun_iterate: "monofun(iterate(i))"
apply (unfold monofun)
apply (intro strip)
apply (induct_tac "i")
apply (simp (no_asm_simp))
apply (simp add: less_fun monofun_cfun)
done

(* ------------------------------------------------------------------------ *)
(* the following lemma uses contlub_cfun which itself is based on a         *)
(* diagonalisation lemma for continuous functions with two arguments.       *)
(* In this special case it is the application function Rep_CFun                 *)
(* ------------------------------------------------------------------------ *)

lemma contlub_iterate: "contlub(iterate(i))"

apply (unfold contlub)
apply (intro strip)
apply (induct_tac "i")
apply (simp (no_asm_simp))
apply (rule lub_const [THEN thelubI, symmetric])
apply (simp (no_asm_simp) del: range_composition)
apply (rule ext)
apply (simplesubst thelub_fun)
apply (rule chainI)
apply (rule less_fun [THEN iffD2])
apply (rule allI)
apply (rule chainE)
apply (rule monofun_Rep_CFun1 [THEN ch2ch_MF2LR])
apply (rule allI)
apply (rule monofun_Rep_CFun2)
apply assumption
apply (rule ch2ch_fun)
apply (rule monofun_iterate [THEN ch2ch_monofun])
apply assumption
apply (subst thelub_fun)
apply (rule monofun_iterate [THEN ch2ch_monofun])
apply assumption
apply (rule contlub_cfun)
apply assumption
apply (erule monofun_iterate [THEN ch2ch_monofun, THEN ch2ch_fun])
done


lemma cont_iterate: "cont(iterate(i))"
apply (rule monocontlub2cont)
apply (rule monofun_iterate)
apply (rule contlub_iterate)
done

(* ------------------------------------------------------------------------ *)
(* a lemma about continuity of iterate in its third argument                *)
(* ------------------------------------------------------------------------ *)

lemma monofun_iterate2: "monofun(iterate n F)"
apply (rule monofunI)
apply (intro strip)
apply (induct_tac "n")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (erule monofun_cfun_arg)
done

lemma contlub_iterate2: "contlub(iterate n F)"
apply (rule contlubI)
apply (intro strip)
apply (induct_tac "n")
apply (simp (no_asm))
apply (simp (no_asm))
apply (rule_tac t = "iterate n F (lub (range (%u. Y u))) " and s = "lub (range (%i. iterate n F (Y i))) " in ssubst)
apply assumption
apply (rule contlub_cfun_arg)
apply (erule monofun_iterate2 [THEN ch2ch_monofun])
done

lemma cont_iterate2: "cont (iterate n F)"
apply (rule monocontlub2cont)
apply (rule monofun_iterate2)
apply (rule contlub_iterate2)
done

(* ------------------------------------------------------------------------ *)
(* monotonicity and continuity of Ifix                                      *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Ifix: "monofun(Ifix)"

apply (unfold monofun Ifix_def)
apply (intro strip)
apply (rule lub_mono)
apply (rule chain_iterate)
apply (rule chain_iterate)
apply (rule allI)
apply (rule less_fun [THEN iffD1, THEN spec], erule monofun_iterate [THEN monofunE, THEN spec, THEN spec, THEN mp])
done

(* ------------------------------------------------------------------------ *)
(* since iterate is not monotone in its first argument, special lemmas must *)
(* be derived for lubs in this argument                                     *)
(* ------------------------------------------------------------------------ *)

lemma chain_iterate_lub: 
"chain(Y) ==> chain(%i. lub(range(%ia. iterate ia (Y i) UU)))"
apply (rule chainI)
apply (rule lub_mono)
apply (rule chain_iterate)
apply (rule chain_iterate)
apply (intro strip)
apply (erule monofun_iterate [THEN ch2ch_monofun, THEN ch2ch_fun, THEN chainE])
done

(* ------------------------------------------------------------------------ *)
(* this exchange lemma is analog to the one for monotone functions          *)
(* observe that monotonicity is not really needed. The propagation of       *)
(* chains is the essential argument which is usually derived from monot.    *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Ifix_lemma1: "chain(Y) ==>iterate n (lub(range Y)) y = lub(range(%i. iterate n (Y i) y))"
apply (rule thelub_fun [THEN subst])
apply (erule monofun_iterate [THEN ch2ch_monofun])
apply (simp (no_asm_simp) add: contlub_iterate [THEN contlubE])
done


lemma ex_lub_iterate: "chain(Y) ==> 
          lub(range(%i. lub(range(%ia. iterate i (Y ia) UU)))) = 
          lub(range(%i. lub(range(%ia. iterate ia (Y i) UU))))"
apply (rule antisym_less)
apply (rule is_lub_thelub)
apply (rule contlub_Ifix_lemma1 [THEN ext, THEN subst])
apply assumption
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (rule lub_mono)
apply (erule monofun_iterate [THEN ch2ch_monofun, THEN ch2ch_fun])
apply (erule chain_iterate_lub)
apply (intro strip)
apply (rule is_ub_thelub)
apply (rule chain_iterate)
apply (rule is_lub_thelub)
apply (erule chain_iterate_lub)
apply (rule ub_rangeI)
apply (rule lub_mono)
apply (rule chain_iterate)
apply (rule contlub_Ifix_lemma1 [THEN ext, THEN subst])
apply assumption
apply (rule chain_iterate)
apply (intro strip)
apply (rule is_ub_thelub)
apply (erule monofun_iterate [THEN ch2ch_monofun, THEN ch2ch_fun])
done


lemma contlub_Ifix: "contlub(Ifix)"

apply (unfold contlub Ifix_def)
apply (intro strip)
apply (subst contlub_Ifix_lemma1 [THEN ext])
apply assumption
apply (erule ex_lub_iterate)
done


lemma cont_Ifix: "cont(Ifix)"
apply (rule monocontlub2cont)
apply (rule monofun_Ifix)
apply (rule contlub_Ifix)
done

(* ------------------------------------------------------------------------ *)
(* propagate properties of Ifix to its continuous counterpart               *)
(* ------------------------------------------------------------------------ *)

lemma fix_eq: "fix$F = F$(fix$F)"

apply (unfold fix_def)
apply (simp (no_asm_simp) add: cont_Ifix)
apply (rule Ifix_eq)
done

lemma fix_least: "F$x = x ==> fix$F << x"
apply (unfold fix_def)
apply (simp (no_asm_simp) add: cont_Ifix)
apply (erule Ifix_least)
done


lemma fix_eqI: 
"[| F$x = x; !z. F$z = z --> x << z |] ==> x = fix$F"
apply (rule antisym_less)
apply (erule allE)
apply (erule mp)
apply (rule fix_eq [symmetric])
apply (erule fix_least)
done


lemma fix_eq2: "f == fix$F ==> f = F$f"
apply (simp (no_asm_simp) add: fix_eq [symmetric])
done

lemma fix_eq3: "f == fix$F ==> f$x = F$f$x"
apply (erule fix_eq2 [THEN cfun_fun_cong])
done

(* fun fix_tac3 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq3) i)) *)

lemma fix_eq4: "f = fix$F ==> f = F$f"
apply (erule ssubst)
apply (rule fix_eq)
done

lemma fix_eq5: "f = fix$F ==> f$x = F$f$x"
apply (rule trans)
apply (erule fix_eq4 [THEN cfun_fun_cong])
apply (rule refl)
done

(* fun fix_tac5 thm i  = ((rtac trans i) THEN (rtac (thm RS fix_eq5) i)) *)

(* proves the unfolding theorem for function equations f = fix$... *)
(*
fun fix_prover thy fixeq s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fixeq RS fix_eq4) 1),
        (rtac trans 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ])
*)
(* proves the unfolding theorem for function definitions f == fix$... *)
(*
fun fix_prover2 thy fixdef s = prove_goal thy s (fn prems => [
        (rtac trans 1),
        (rtac (fix_eq2) 1),
        (rtac fixdef 1),
        (rtac beta_cfun 1),
        (Simp_tac 1)
        ])
*)
(* proves an application case for a function from its unfolding thm *)
(*
fun case_prover thy unfold s = prove_goal thy s (fn prems => [
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(stac unfold 1),
	Auto_tac
	])
*)
(* ------------------------------------------------------------------------ *)
(* better access to definitions                                             *)
(* ------------------------------------------------------------------------ *)


lemma Ifix_def2: "Ifix=(%x. lub(range(%i. iterate i x UU)))"
apply (rule ext)
apply (unfold Ifix_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* direct connection between fix and iteration without Ifix                 *)
(* ------------------------------------------------------------------------ *)

lemma fix_def2: "fix$F = lub(range(%i. iterate i F UU))"
apply (unfold fix_def)
apply (fold Ifix_def)
apply (simp (no_asm_simp) add: cont_Ifix)
done


(* ------------------------------------------------------------------------ *)
(* Lemmas about admissibility and fixed point induction                     *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)

lemma admI:
   "(!!Y. [| chain Y; !i. P (Y i) |] ==> P (lub (range Y))) ==> adm P"
apply (unfold adm_def)
apply blast
done

lemma triv_admI: "!x. P x ==> adm P"
apply (rule admI)
apply (erule spec)
done

lemma admD: "[| adm(P); chain(Y); !i. P(Y(i)) |] ==> P(lub(range(Y)))"
apply (unfold adm_def)
apply blast
done

lemma admw_def2: "admw(P) = (!F.(!n. P(iterate n F UU)) --> 
                         P (lub(range(%i. iterate i F UU))))"
apply (unfold admw_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* an admissible formula is also weak admissible                            *)
(* ------------------------------------------------------------------------ *)

lemma adm_impl_admw: "adm(P)==>admw(P)"
apply (unfold admw_def)
apply (intro strip)
apply (erule admD)
apply (rule chain_iterate)
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* fixed point induction                                                    *)
(* ------------------------------------------------------------------------ *)

lemma fix_ind:
     "[| adm(P); P(UU); !!x. P(x) ==> P(F$x)|] ==> P(fix$F)"
apply (subst fix_def2)
apply (erule admD)
apply (rule chain_iterate)
apply (rule allI)
apply (induct_tac "i")
apply simp
apply simp
done

lemma def_fix_ind: "[| f == fix$F; adm(P);  
        P(UU); !!x. P(x) ==> P(F$x)|] ==> P f"
apply simp
apply (erule fix_ind)
apply assumption
apply fast
done
	
(* ------------------------------------------------------------------------ *)
(* computational induction for weak admissible formulae                     *)
(* ------------------------------------------------------------------------ *)

lemma wfix_ind: "[| admw(P); !n. P(iterate n F UU)|] ==> P(fix$F)"
apply (subst fix_def2)
apply (rule admw_def2 [THEN iffD1, THEN spec, THEN mp])
apply assumption
apply (rule allI)
apply (erule spec)
done

lemma def_wfix_ind: "[| f == fix$F; admw(P);  
        !n. P(iterate n F UU) |] ==> P f"
apply simp
apply (erule wfix_ind)
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* for chain-finite (easy) types every formula is admissible                *)
(* ------------------------------------------------------------------------ *)

lemma adm_max_in_chain: 
"!Y. chain(Y::nat=>'a) --> (? n. max_in_chain n Y) ==> adm(P::'a=>bool)"
apply (unfold adm_def)
apply (intro strip)
apply (rule exE)
apply (rule mp)
apply (erule spec)
apply assumption
apply (subst lub_finch1 [THEN thelubI])
apply assumption
apply assumption
apply (erule spec)
done

lemmas adm_chfin = chfin [THEN adm_max_in_chain, standard]

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chfin domain/range types	    *)
(* ------------------------------------------------------------------------ *)

lemma adm_chfindom: "adm (%(u::'a::cpo->'b::chfin). P(u$s))"
apply (unfold adm_def)
apply (intro strip)
apply (drule chfin_Rep_CFunR)
apply (erule_tac x = "s" in allE)
apply clarsimp
done

(* adm_flat not needed any more, since it is a special case of adm_chfindom *)

(* ------------------------------------------------------------------------ *)
(* improved admisibility introduction                                       *)
(* ------------------------------------------------------------------------ *)

lemma admI2:
 "(!!Y. [| chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j |] 
  ==> P(lub (range Y))) ==> adm P"
apply (unfold adm_def)
apply (intro strip)
apply (erule increasing_chain_adm_lemma)
apply assumption
apply fast
done


(* ------------------------------------------------------------------------ *)
(* admissibility of special formulae and propagation                        *)
(* ------------------------------------------------------------------------ *)

lemma adm_less: "[|cont u;cont v|]==> adm(%x. u x << v x)"
apply (unfold adm_def)
apply (intro strip)
apply (frule_tac f = "u" in cont2mono [THEN ch2ch_monofun])
apply assumption
apply (frule_tac f = "v" in cont2mono [THEN ch2ch_monofun])
apply assumption
apply (erule cont2contlub [THEN contlubE, THEN spec, THEN mp, THEN ssubst])
apply assumption
apply (erule cont2contlub [THEN contlubE, THEN spec, THEN mp, THEN ssubst])
apply assumption
apply (blast intro: lub_mono)
done
declare adm_less [simp]

lemma adm_conj: "[| adm P; adm Q |] ==> adm(%x. P x & Q x)"
apply (fast elim: admD intro: admI)
done
declare adm_conj [simp]

lemma adm_not_free: "adm(%x. t)"
apply (unfold adm_def)
apply fast
done
declare adm_not_free [simp]

lemma adm_not_less: "cont t ==> adm(%x.~ (t x) << u)"
apply (unfold adm_def)
apply (intro strip)
apply (rule contrapos_nn)
apply (erule spec)
apply (rule trans_less)
prefer 2 apply (assumption)
apply (erule cont2mono [THEN monofun_fun_arg])
apply (rule is_ub_thelub)
apply assumption
done

lemma adm_all: "!y. adm(P y) ==> adm(%x.!y. P y x)"
apply (fast intro: admI elim: admD)
done

lemmas adm_all2 = allI [THEN adm_all, standard]

lemma adm_subst: "[|cont t; adm P|] ==> adm(%x. P (t x))"
apply (rule admI)
apply (simplesubst cont2contlub [THEN contlubE, THEN spec, THEN mp])
apply assumption
apply assumption
apply (erule admD)
apply (erule cont2mono [THEN ch2ch_monofun])
apply assumption
apply assumption
done

lemma adm_UU_not_less: "adm(%x.~ UU << t(x))"
apply (simp (no_asm))
done


lemma adm_not_UU: "cont(t)==> adm(%x.~ (t x) = UU)"

apply (unfold adm_def)
apply (intro strip)
apply (rule contrapos_nn)
apply (erule spec)
apply (rule chain_UU_I [THEN spec])
apply (erule cont2mono [THEN ch2ch_monofun])
apply assumption
apply (erule cont2contlub [THEN contlubE, THEN spec, THEN mp, THEN subst])
apply assumption
apply assumption
done

lemma adm_eq: "[|cont u ; cont v|]==> adm(%x. u x = v x)"
apply (simp (no_asm_simp) add: po_eq_conv)
done



(* ------------------------------------------------------------------------ *)
(* admissibility for disjunction is hard to prove. It takes 10 Lemmas       *)
(* ------------------------------------------------------------------------ *)


lemma adm_disj_lemma1: "!n. P(Y n)|Q(Y n) ==> (? i.!j. R i j --> Q(Y(j))) | (!i.? j. R i j & P(Y(j)))"
apply fast
done

lemma adm_disj_lemma2: "[| adm(Q); ? X. chain(X) & (!n. Q(X(n))) & 
      lub(range(Y))=lub(range(X))|] ==> Q(lub(range(Y)))"
apply (force elim: admD)
done

lemma adm_disj_lemma3: "chain Y ==> chain (%m. if m < Suc i then Y (Suc i) else Y m)"
apply (unfold chain_def)
apply (simp (no_asm_simp))
apply safe
apply (subgoal_tac "ia = i")
apply (simp_all (no_asm_simp))
done

lemma adm_disj_lemma4: "!j. i < j --> Q(Y(j))  ==> !n. Q( if n < Suc i then Y(Suc i) else Y n)"
apply (simp (no_asm_simp))
done

lemma adm_disj_lemma5: 
  "!!Y::nat=>'a::cpo. [| chain(Y); ! j. i < j --> Q(Y(j)) |] ==> 
          lub(range(Y)) = lub(range(%m. if m< Suc(i) then Y(Suc(i)) else Y m))"
apply (safe intro!: lub_equal2 adm_disj_lemma3)
prefer 2 apply (assumption)
apply (rule_tac x = "i" in exI)
apply (simp (no_asm_simp))
done

lemma adm_disj_lemma6: 
  "[| chain(Y::nat=>'a::cpo); ? i. ! j. i < j --> Q(Y(j)) |] ==> 
            ? X. chain(X) & (! n. Q(X(n))) & lub(range(Y)) = lub(range(X))"
apply (erule exE)
apply (rule_tac x = "%m. if m<Suc (i) then Y (Suc (i)) else Y m" in exI)
apply (rule conjI)
apply (rule adm_disj_lemma3)
apply assumption
apply (rule conjI)
apply (rule adm_disj_lemma4)
apply assumption
apply (rule adm_disj_lemma5)
apply assumption
apply assumption
done

lemma adm_disj_lemma7: 
  "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j))  |] ==> 
            chain(%m. Y(Least(%j. m<j & P(Y(j)))))"
apply (rule chainI)
apply (rule chain_mono3)
apply assumption
apply (rule Least_le)
apply (rule conjI)
apply (rule Suc_lessD)
apply (erule allE)
apply (erule exE)
apply (rule LeastI [THEN conjunct1])
apply assumption
apply (erule allE)
apply (erule exE)
apply (rule LeastI [THEN conjunct2])
apply assumption
done

lemma adm_disj_lemma8: 
  "[| ! i. ? j. i < j & P(Y(j)) |] ==> ! m. P(Y(LEAST j::nat. m<j & P(Y(j))))"
apply (intro strip)
apply (erule allE)
apply (erule exE)
apply (erule LeastI [THEN conjunct2])
done

lemma adm_disj_lemma9: 
  "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==> 
            lub(range(Y)) = lub(range(%m. Y(Least(%j. m<j & P(Y(j))))))"
apply (rule antisym_less)
apply (rule lub_mono)
apply assumption
apply (rule adm_disj_lemma7)
apply assumption
apply assumption
apply (intro strip)
apply (rule chain_mono)
apply assumption
apply (erule allE)
apply (erule exE)
apply (rule LeastI [THEN conjunct1])
apply assumption
apply (rule lub_mono3)
apply (rule adm_disj_lemma7)
apply assumption
apply assumption
apply assumption
apply (intro strip)
apply (rule exI)
apply (rule chain_mono)
apply assumption
apply (rule lessI)
done

lemma adm_disj_lemma10: "[| chain(Y::nat=>'a::cpo); ! i. ? j. i < j & P(Y(j)) |] ==> 
            ? X. chain(X) & (! n. P(X(n))) & lub(range(Y)) = lub(range(X))"
apply (rule_tac x = "%m. Y (Least (%j. m<j & P (Y (j))))" in exI)
apply (rule conjI)
apply (rule adm_disj_lemma7)
apply assumption
apply assumption
apply (rule conjI)
apply (rule adm_disj_lemma8)
apply assumption
apply (rule adm_disj_lemma9)
apply assumption
apply assumption
done

lemma adm_disj_lemma12: "[| adm(P); chain(Y);? i. ! j. i < j --> P(Y(j))|]==>P(lub(range(Y)))"
apply (erule adm_disj_lemma2)
apply (erule adm_disj_lemma6)
apply assumption
done


lemma adm_lemma11: 
"[| adm(P); chain(Y); ! i. ? j. i < j & P(Y(j)) |]==>P(lub(range(Y)))"
apply (erule adm_disj_lemma2)
apply (erule adm_disj_lemma10)
apply assumption
done

lemma adm_disj: "[| adm P; adm Q |] ==> adm(%x. P x | Q x)"
apply (rule admI)
apply (rule adm_disj_lemma1 [THEN disjE])
apply assumption
apply (rule disjI2)
apply (erule adm_disj_lemma12)
apply assumption
apply assumption
apply (rule disjI1)
apply (erule adm_lemma11)
apply assumption
apply assumption
done

lemma adm_imp: "[| adm(%x.~(P x)); adm Q |] ==> adm(%x. P x --> Q x)"
apply (subgoal_tac " (%x. P x --> Q x) = (%x. ~P x | Q x) ")
apply (erule ssubst)
apply (erule adm_disj)
apply assumption
apply (simp (no_asm))
done

lemma adm_iff: "[| adm (%x. P x --> Q x); adm (%x. Q x --> P x) |]  
            ==> adm (%x. P x = Q x)"
apply (subgoal_tac " (%x. P x = Q x) = (%x. (P x --> Q x) & (Q x --> P x))")
apply (simp (no_asm_simp))
apply (rule ext)
apply fast
done


lemma adm_not_conj: "[| adm (%x. ~ P x); adm (%x. ~ Q x) |] ==> adm (%x. ~ (P x & Q x))"
apply (subgoal_tac " (%x. ~ (P x & Q x)) = (%x. ~ P x | ~ Q x) ")
apply (rule_tac [2] ext)
prefer 2 apply fast
apply (erule ssubst)
apply (erule adm_disj)
apply assumption
done

lemmas adm_lemmas = adm_not_free adm_imp adm_disj adm_eq adm_not_UU
        adm_UU_not_less adm_all2 adm_not_less adm_not_conj adm_iff

declare adm_lemmas [simp]

end


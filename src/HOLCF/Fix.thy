(*  Title:      HOLCF/Fix.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

definitions for fixed point operator and admissibility
*)

header {* Fixed point operator and admissibility *}

theory Fix
imports Cfun Cprod
begin

subsection {* Definitions *}

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

subsection {* Binder syntax for @{term fix} *}

syntax
  "@FIX" :: "('a => 'a) => 'a"  (binder "FIX " 10)
  "@FIXP" :: "[patterns, 'a] => 'a"  ("(3FIX <_>./ _)" [0, 10] 10)

syntax (xsymbols)
  "FIX " :: "[idt, 'a] => 'a"  ("(3\<mu>_./ _)" [0, 10] 10)
  "@FIXP" :: "[patterns, 'a] => 'a"  ("(3\<mu>()<_>./ _)" [0, 10] 10)

translations
  "FIX x. LAM y. t" == "fix\<cdot>(LAM x y. t)"
  "FIX x. t" == "fix\<cdot>(LAM x. t)"
  "FIX <xs>. t" == "fix\<cdot>(LAM <xs>. t)"

subsection {* Properties of @{term iterate} and @{term fix} *}

text {* derive inductive properties of iterate from primitive recursion *}

lemma iterate_Suc2: "iterate (Suc n) F x = iterate n F (F$x)"
by (induct_tac "n", auto)

text {*
  The sequence of function iterations is a chain.
  This property is essential since monotonicity of iterate makes no sense.
*}

lemma chain_iterate2: "x << F$x ==> chain (%i. iterate i F x)"
by (rule chainI, induct_tac "i", auto elim: monofun_cfun_arg)

lemma chain_iterate: "chain (%i. iterate i F UU)"
by (rule chain_iterate2 [OF minimal])

text {*
  Kleene's fixed point theorems for continuous functions in pointed
  omega cpo's
*}

lemma Ifix_eq: "Ifix F = F$(Ifix F)"
apply (unfold Ifix_def)
apply (subst lub_range_shift [of _ 1, symmetric])
apply (rule chain_iterate)
apply (subst contlub_cfun_arg)
apply (rule chain_iterate)
apply simp
done

lemma Ifix_least: "F$x=x ==> Ifix(F) << x"
apply (unfold Ifix_def)
apply (rule is_lub_thelub)
apply (rule chain_iterate)
apply (rule ub_rangeI)
apply (induct_tac "i")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (erule_tac t = "x" in subst)
apply (erule monofun_cfun_arg)
done

text {* monotonicity and continuity of @{term iterate} *}

lemma cont_iterate: "cont(iterate(i))"
apply (induct_tac i)
apply simp
apply simp
apply (rule cont2cont_CF1L_rev)
apply (rule allI)
apply (rule cont2cont_Rep_CFun)
apply (rule cont_id)
apply (erule cont2cont_CF1L)
done

lemma monofun_iterate: "monofun(iterate(i))"
by (rule cont_iterate [THEN cont2mono])

lemma contlub_iterate: "contlub(iterate(i))"
by (rule cont_iterate [THEN cont2contlub])

text {* a lemma about continuity of @{term iterate} in its third argument *}

lemma cont_iterate2: "cont (iterate n F)"
by (induct_tac "n", simp_all)

lemma monofun_iterate2: "monofun(iterate n F)"
by (rule cont_iterate2 [THEN cont2mono])

lemma contlub_iterate2: "contlub(iterate n F)"
by (rule cont_iterate2 [THEN cont2contlub])

text {* monotonicity and continuity of @{term Ifix} *}

text {* better access to definitions *}

lemma Ifix_def2: "Ifix=(%x. lub(range(%i. iterate i x UU)))"
apply (rule ext)
apply (unfold Ifix_def)
apply (rule refl)
done

lemma cont_Ifix: "cont(Ifix)"
apply (subst Ifix_def2)
apply (subst cont_iterate [THEN cont2cont_CF1L, THEN beta_cfun, symmetric])
apply (rule cont_lubcfun)
apply (rule chainI)
apply (rule less_cfun2)
apply (simp add: cont_iterate [THEN cont2cont_CF1L] del: iterate_Suc)
apply (rule chainE)
apply (rule chain_iterate)
done

lemma monofun_Ifix: "monofun(Ifix)"
by (rule cont_Ifix [THEN cont2mono])

lemma contlub_Ifix: "contlub(Ifix)"
by (rule cont_Ifix [THEN cont2contlub])

text {* propagate properties of @{term Ifix} to its continuous counterpart *}

lemma fix_eq: "fix$F = F$(fix$F)"
apply (unfold fix_def)
apply (simp add: cont_Ifix)
apply (rule Ifix_eq)
done

lemma fix_least: "F$x = x ==> fix$F << x"
apply (unfold fix_def)
apply (simp add: cont_Ifix)
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
by (simp add: fix_eq [symmetric])

lemma fix_eq3: "f == fix$F ==> f$x = F$f$x"
by (erule fix_eq2 [THEN cfun_fun_cong])

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
text {* direct connection between @{term fix} and iteration without @{term Ifix} *}

lemma fix_def2: "fix$F = lub(range(%i. iterate i F UU))"
apply (unfold fix_def)
apply (fold Ifix_def)
apply (simp (no_asm_simp) add: cont_Ifix)
done

subsection {* Admissibility and fixed point induction *}

text {* access to definitions *}

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

text {* an admissible formula is also weak admissible *}

lemma adm_impl_admw: "adm(P)==>admw(P)"
apply (unfold admw_def)
apply (intro strip)
apply (erule admD)
apply (rule chain_iterate)
apply assumption
done

text {* fixed point induction *}

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

text {* computational induction for weak admissible formulae *}

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

text {* for chain-finite (easy) types every formula is admissible *}

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

text {* some lemmata for functions with flat/chfin domain/range types *}

lemma adm_chfindom: "adm (%(u::'a::cpo->'b::chfin). P(u$s))"
apply (unfold adm_def)
apply (intro strip)
apply (drule chfin_Rep_CFunR)
apply (erule_tac x = "s" in allE)
apply clarsimp
done

(* adm_flat not needed any more, since it is a special case of adm_chfindom *)

text {* improved admissibility introduction *}

lemma admI2:
 "(!!Y. [| chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j |] 
  ==> P(lub (range Y))) ==> adm P"
apply (unfold adm_def)
apply (intro strip)
apply (erule increasing_chain_adm_lemma)
apply assumption
apply fast
done

text {* admissibility of special formulae and propagation *}

lemma adm_less [simp]: "[|cont u;cont v|]==> adm(%x. u x << v x)"
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

lemma adm_conj [simp]: "[| adm P; adm Q |] ==> adm(%x. P x & Q x)"
by (fast elim: admD intro: admI)

lemma adm_not_free [simp]: "adm(%x. t)"
apply (unfold adm_def)
apply fast
done

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
by (fast intro: admI elim: admD)

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
by simp

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
by (simp add: po_eq_conv)

text {* admissibility for disjunction is hard to prove. It takes 7 Lemmas *}

lemma adm_disj_lemma1:
  "\<forall>n::nat. P n \<or> Q n \<Longrightarrow> (\<forall>i. \<exists>j\<ge>i. P j) \<or> (\<forall>i. \<exists>j\<ge>i. Q j)"
apply (erule contrapos_pp)
apply clarsimp
apply (rule exI)
apply (rule conjI)
apply (drule spec, erule mp)
apply (rule le_maxI1)
apply (drule spec, erule mp)
apply (rule le_maxI2)
done

lemma adm_disj_lemma2: "[| adm P; \<exists>X. chain X & (!n. P(X n)) & 
      lub(range Y)=lub(range X)|] ==> P(lub(range Y))"
by (force elim: admD)

lemma adm_disj_lemma3: 
  "[| chain(Y::nat=>'a::cpo); \<forall>i. \<exists>j\<ge>i. P (Y j) |] ==> 
            chain(%m. Y (LEAST j. m\<le>j \<and> P(Y j)))"
apply (rule chainI)
apply (erule chain_mono3)
apply (rule Least_le)
apply (rule conjI)
apply (rule Suc_leD)
apply (erule allE)
apply (erule exE)
apply (erule LeastI [THEN conjunct1])
apply (erule allE)
apply (erule exE)
apply (erule LeastI [THEN conjunct2])
done

lemma adm_disj_lemma4: 
  "[| \<forall>i. \<exists>j\<ge>i. P (Y j) |] ==> ! m. P(Y(LEAST j::nat. m\<le>j & P(Y j)))"
apply (rule allI)
apply (erule allE)
apply (erule exE)
apply (erule LeastI [THEN conjunct2])
done

lemma adm_disj_lemma5: 
  "[| chain(Y::nat=>'a::cpo); \<forall>i. \<exists>j\<ge>i. P(Y j) |] ==> 
            lub(range(Y)) = (LUB m. Y(LEAST j. m\<le>j & P(Y j)))"
 apply (rule antisym_less)
  apply (rule lub_mono)
    apply assumption
   apply (erule adm_disj_lemma3)
   apply assumption
  apply (rule allI)
  apply (erule chain_mono3)
  apply (erule allE)
  apply (erule exE)
  apply (erule LeastI [THEN conjunct1])
 apply (rule lub_mono3)
   apply (erule adm_disj_lemma3)
   apply assumption
  apply assumption
 apply (rule allI)
 apply (rule exI)
 apply (rule refl_less)
done

lemma adm_disj_lemma6:
  "[| chain(Y::nat=>'a::cpo); \<forall>i. \<exists>j\<ge>i. P(Y j) |] ==> 
            \<exists>X. chain X & (\<forall>n. P(X n)) & lub(range Y) = lub(range X)"
apply (rule_tac x = "%m. Y (LEAST j. m\<le>j & P (Y j))" in exI)
apply (fast intro!: adm_disj_lemma3 adm_disj_lemma4 adm_disj_lemma5)
done

lemma adm_disj_lemma7:
"[| adm(P); chain(Y); \<forall>i. \<exists>j\<ge>i. P(Y j) |]==>P(lub(range(Y)))"
apply (erule adm_disj_lemma2)
apply (erule adm_disj_lemma6)
apply assumption
done

lemma adm_disj: "[| adm P; adm Q |] ==> adm(%x. P x | Q x)"
apply (rule admI)
apply (erule adm_disj_lemma1 [THEN disjE])
apply (rule disjI1)
apply (erule adm_disj_lemma7)
apply assumption
apply assumption
apply (rule disjI2)
apply (erule adm_disj_lemma7)
apply assumption
apply assumption
done

lemma adm_imp: "[| adm(%x.~(P x)); adm Q |] ==> adm(%x. P x --> Q x)"
by (subst imp_conv_disj, rule adm_disj)

lemma adm_iff: "[| adm (%x. P x --> Q x); adm (%x. Q x --> P x) |]  
            ==> adm (%x. P x = Q x)"
by (subst iff_conv_conj_imp, rule adm_conj)

lemma adm_not_conj: "[| adm (%x. ~ P x); adm (%x. ~ Q x) |] ==> adm (%x. ~ (P x & Q x))"
by (subst de_Morgan_conj, rule adm_disj)

lemmas adm_lemmas = adm_not_free adm_imp adm_disj adm_eq adm_not_UU
        adm_UU_not_less adm_all2 adm_not_less adm_not_conj adm_iff

declare adm_lemmas [simp]

end


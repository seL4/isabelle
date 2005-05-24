(*  Title:      HOLCF/Adm.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Admissibility *}

theory Adm
imports Cfun
begin

defaultsort cpo

subsection {* Definitions *}

consts
adm		:: "('a::cpo=>bool)=>bool"

defs
adm_def:       "adm P == !Y. chain(Y) --> 
                        (!i. P(Y i)) --> P(lub(range Y))"

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


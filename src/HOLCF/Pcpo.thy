(*  Title:      HOLCF/Pcpo.thy
    ID:         $Id$
    Author:     Franz Regensburger

Introduction of the classes cpo and pcpo.
*)

header {* Classes cpo and pcpo *}

theory Pcpo
imports Porder
begin

subsection {* Complete partial orders *}

text {* The class cpo of chain complete partial orders *}

axclass cpo < po
        -- {* class axiom: *}
  cpo:   "chain S ==> ? x. range S <<| x" 

text {* in cpo's everthing equal to THE lub has lub properties for every chain *}

lemma thelubE: "[| chain(S); lub(range(S)) = (l::'a::cpo) |] ==> range(S) <<| l"
by (blast dest: cpo intro: lubI)

text {* Properties of the lub *}

lemma is_ub_thelub: "chain (S::nat => 'a::cpo) ==> S(x) << lub(range(S))"
by (blast dest: cpo intro: lubI [THEN is_ub_lub])

lemma is_lub_thelub: "[| chain (S::nat => 'a::cpo); range(S) <| x |] ==> lub(range S) << x"
by (blast dest: cpo intro: lubI [THEN is_lub_lub])

lemma lub_range_mono: "[| range X <= range Y;  chain Y; chain (X::nat=>'a::cpo) |] ==> lub(range X) << lub(range Y)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (subgoal_tac "? j. X i = Y j")
apply  clarsimp
apply  (erule is_ub_thelub)
apply auto
done

lemma lub_range_shift: "chain (Y::nat=>'a::cpo) ==> lub(range (%i. Y(i + j))) = lub(range Y)"
apply (rule antisym_less)
apply (rule lub_range_mono)
apply    fast
apply   assumption
apply (erule chain_shift)
apply (rule is_lub_thelub)
apply assumption
apply (rule ub_rangeI)
apply (rule trans_less)
apply (rule_tac [2] is_ub_thelub)
apply (erule_tac [2] chain_shift)
apply (erule chain_mono3)
apply (rule le_add1)
done

lemma maxinch_is_thelub: "chain Y ==> max_in_chain i Y = (lub(range(Y)) = ((Y i)::'a::cpo))"
apply (rule iffI)
apply (fast intro!: thelubI lub_finch1)
apply (unfold max_in_chain_def)
apply (safe intro!: antisym_less)
apply (fast elim!: chain_mono3)
apply (drule sym)
apply (force elim!: is_ub_thelub)
done

text {* the @{text "<<"} relation between two chains is preserved by their lubs *}

lemma lub_mono: "[|chain(C1::(nat=>'a::cpo));chain(C2); ALL k. C1(k) << C2(k)|] 
      ==> lub(range(C1)) << lub(range(C2))"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (rule trans_less)
apply (erule spec)
apply (erule is_ub_thelub)
done

text {* the = relation between two chains is preserved by their lubs *}

lemma lub_equal: "[| chain(C1::(nat=>'a::cpo));chain(C2);ALL k. C1(k)=C2(k)|] 
      ==> lub(range(C1))=lub(range(C2))"
by (simp only: expand_fun_eq [symmetric])

text {* more results about mono and = of lubs of chains *}

lemma lub_mono2: "[|EX j. ALL i. j<i --> X(i::nat)=Y(i);chain(X::nat=>'a::cpo);chain(Y)|] 
      ==> lub(range(X))<<lub(range(Y))"
apply (erule exE)
apply (rule is_lub_thelub)
apply assumption
apply (rule ub_rangeI)
apply (case_tac "j<i")
apply (rule_tac s = "Y (i) " and t = "X (i) " in subst)
apply (rule sym)
apply fast
apply (rule is_ub_thelub)
apply assumption
apply (rule_tac y = "X (Suc (j))" in trans_less)
apply (rule chain_mono)
apply assumption
apply (rule not_less_eq [THEN subst])
apply assumption
apply (rule_tac s = "Y (Suc (j))" and t = "X (Suc (j))" in subst)
apply (simp)
apply (erule is_ub_thelub)
done

lemma lub_equal2: "[|EX j. ALL i. j<i --> X(i)=Y(i); chain(X::nat=>'a::cpo); chain(Y)|] 
      ==> lub(range(X))=lub(range(Y))"
by (blast intro: antisym_less lub_mono2 sym)

lemma lub_mono3: "[|chain(Y::nat=>'a::cpo);chain(X); 
 ALL i. EX j. Y(i)<< X(j)|]==> lub(range(Y))<<lub(range(X))"
apply (rule is_lub_thelub)
apply assumption
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (rule trans_less)
apply (rule_tac [2] is_ub_thelub)
prefer 2 apply (assumption)
apply assumption
done

lemma diag_lub:
  fixes Y :: "nat \<Rightarrow> nat \<Rightarrow> 'a::cpo"
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>i. Y i i)"
proof (rule antisym_less)
  have 3: "chain (\<lambda>i. Y i i)"
    apply (rule chainI)
    apply (rule trans_less)
    apply (rule chainE [OF 1])
    apply (rule chainE [OF 2])
    done
  have 4: "chain (\<lambda>i. \<Squnion>j. Y i j)"
    apply (rule chainI)
    apply (rule lub_mono [OF 2 2, rule_format])
    apply (rule chainE [OF 1])
    done
  show "(\<Squnion>i. \<Squnion>j. Y i j) \<sqsubseteq> (\<Squnion>i. Y i i)"
    apply (rule is_lub_thelub [OF 4])
    apply (rule ub_rangeI)
    apply (rule lub_mono3 [OF 2 3, rule_format])
    apply (rule exI)
    apply (rule trans_less)
    apply (rule chain_mono3 [OF 1 le_maxI1])
    apply (rule chain_mono3 [OF 2 le_maxI2])
    done
  show "(\<Squnion>i. Y i i) \<sqsubseteq> (\<Squnion>i. \<Squnion>j. Y i j)"
    apply (rule lub_mono [OF 3 4, rule_format])
    apply (rule is_ub_thelub [OF 2])
    done
qed

lemma ex_lub:
  fixes Y :: "nat \<Rightarrow> nat \<Rightarrow> 'a::cpo"
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>j. \<Squnion>i. Y i j)"
by (simp add: diag_lub 1 2)


subsection {* Pointed cpos *}

text {* The class pcpo of pointed cpos *}

axclass pcpo < cpo
  least:         "? x.!y. x<<y"

consts
  UU            :: "'a::pcpo"

syntax (xsymbols)
  UU            :: "'a::pcpo"                           ("\<bottom>")

defs
  UU_def:        "UU == THE x. ALL y. x<<y"

text {* derive the old rule minimal *}
 
lemma UU_least: "ALL z. UU << z"
apply (unfold UU_def)
apply (rule theI')
apply (rule ex_ex1I)
apply (rule least)
apply (blast intro: antisym_less)
done

lemmas minimal = UU_least [THEN spec, standard]

declare minimal [iff]

text {* useful lemmas about @{term UU} *}

lemma eq_UU_iff: "(x=UU)=(x<<UU)"
apply (rule iffI)
apply (erule ssubst)
apply (rule refl_less)
apply (rule antisym_less)
apply assumption
apply (rule minimal)
done

lemma UU_I: "x << UU ==> x = UU"
by (subst eq_UU_iff)

lemma not_less2not_eq: "~(x::'a::po)<<y ==> ~x=y"
by auto

lemma chain_UU_I: "[|chain(Y);lub(range(Y))=UU|] ==> ALL i. Y(i)=UU"
apply (rule allI)
apply (rule antisym_less)
apply (rule_tac [2] minimal)
apply (erule subst)
apply (erule is_ub_thelub)
done

lemma chain_UU_I_inverse: "ALL i. Y(i::nat)=UU ==> lub(range(Y::(nat=>'a::pcpo)))=UU"
apply (rule lub_chain_maxelem)
apply (erule spec)
apply simp
done

lemma chain_UU_I_inverse2: "~lub(range(Y::(nat=>'a::pcpo)))=UU ==> EX i.~ Y(i)=UU"
by (blast intro: chain_UU_I_inverse)

lemma notUU_I: "[| x<<y; ~x=UU |] ==> ~y=UU"
by (blast intro: UU_I)

lemma chain_mono2: 
 "[|EX j. ~Y(j)=UU;chain(Y::nat=>'a::pcpo)|] ==> EX j. ALL i. j<i-->~Y(i)=UU"
by (blast dest: notUU_I chain_mono)

subsection {* Chain-finite and flat cpos *}

text {* further useful classes for HOLCF domains *}

axclass chfin < po
  chfin: 	"!Y. chain Y-->(? n. max_in_chain n Y)"

axclass flat < pcpo
  ax_flat:	 	"! x y. x << y --> (x = UU) | (x=y)"

text {* some properties for chfin and flat *}

text {* chfin types are cpo *}

lemma chfin_imp_cpo:
  "chain (S::nat=>'a::chfin) ==> EX x. range S <<| x"
apply (frule chfin [rule_format])
apply (blast intro: lub_finch1)
done

instance chfin < cpo
by intro_classes (rule chfin_imp_cpo)

text {* flat types are chfin *}

lemma flat_imp_chfin: 
     "ALL Y::nat=>'a::flat. chain Y --> (EX n. max_in_chain n Y)"
apply (unfold max_in_chain_def)
apply clarify
apply (case_tac "ALL i. Y (i) =UU")
apply simp
apply simp
apply (erule exE)
apply (rule_tac x = "i" in exI)
apply clarify
apply (erule le_imp_less_or_eq [THEN disjE])
apply safe
apply (blast dest: chain_mono ax_flat [rule_format])
done

instance flat < chfin
by intro_classes (rule flat_imp_chfin)

text {* flat subclass of chfin @{text "-->"} @{text adm_flat} not needed *}

lemma flat_eq: "(a::'a::flat) ~= UU ==> a << b = (a = b)"
by (safe dest!: ax_flat [rule_format])

lemma chfin2finch: "chain (Y::nat=>'a::chfin) ==> finite_chain Y"
by (simp add: chfin finite_chain_def)

text {* lemmata for improved admissibility introdution rule *}

lemma infinite_chain_adm_lemma:
"[|chain Y; ALL i. P (Y i);  
   (!!Y. [| chain Y; ALL i. P (Y i); ~ finite_chain Y |] ==> P (lub(range Y))) 
  |] ==> P (lub (range Y))"
apply (case_tac "finite_chain Y")
prefer 2 apply fast
apply (unfold finite_chain_def)
apply safe
apply (erule lub_finch1 [THEN thelubI, THEN ssubst])
apply assumption
apply (erule spec)
done

lemma increasing_chain_adm_lemma:
"[|chain Y;  ALL i. P (Y i);  
   (!!Y. [| chain Y; ALL i. P (Y i);   
            ALL i. EX j. i < j & Y i ~= Y j & Y i << Y j|] 
  ==> P (lub (range Y))) |] ==> P (lub (range Y))"
apply (erule infinite_chain_adm_lemma)
apply assumption
apply (erule thin_rl)
apply (unfold finite_chain_def)
apply (unfold max_in_chain_def)
apply (fast dest: le_imp_less_or_eq elim: chain_mono)
done

end 

(*  Title:      HOLCF/Up.thy
    ID:         $Id$
    Author:     Franz Regensburger and Brian Huffman

Lifting.
*)

header {* The type of lifted values *}

theory Up
imports Cfun Sum_Type Datatype
begin

defaultsort cpo

subsection {* Definition of new type for lifting *}

typedef (Up) 'a u = "UNIV :: 'a option set" ..

consts
  Iup         :: "'a \<Rightarrow> 'a u"
  Ifup        :: "('a \<rightarrow> 'b::pcpo) \<Rightarrow> 'a u \<Rightarrow> 'b"

defs
  Iup_def:     "Iup x \<equiv> Abs_Up (Some x)"
  Ifup_def:    "Ifup f x \<equiv> case Rep_Up x of None \<Rightarrow> \<bottom> | Some z \<Rightarrow> f\<cdot>z"

lemma Abs_Up_inverse2: "Rep_Up (Abs_Up y) = y"
by (simp add: Up_def Abs_Up_inverse)

lemma Exh_Up: "z = Abs_Up None \<or> (\<exists>x. z = Iup x)"
apply (unfold Iup_def)
apply (rule Rep_Up_inverse [THEN subst])
apply (case_tac "Rep_Up z")
apply auto
done

lemma inj_Abs_Up: "inj Abs_Up" (* worthless *)
apply (rule inj_on_inverseI)
apply (rule Abs_Up_inverse2)
done

lemma inj_Rep_Up: "inj Rep_Up" (* worthless *)
apply (rule inj_on_inverseI)
apply (rule Rep_Up_inverse)
done

lemma Iup_eq [simp]: "(Iup x = Iup y) = (x = y)"
by (simp add: Iup_def Abs_Up_inject Up_def)

lemma Iup_defined [simp]: "Iup x \<noteq> Abs_Up None"
by (simp add: Iup_def Abs_Up_inject Up_def)

lemma upE: "\<lbrakk>p = Abs_Up None \<Longrightarrow> Q; \<And>x. p = Iup x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (rule Exh_Up [THEN disjE], auto)

lemma Ifup1 [simp]: "Ifup f (Abs_Up None) = \<bottom>"
by (simp add: Ifup_def Abs_Up_inverse2)

lemma Ifup2 [simp]: "Ifup f (Iup x) = f\<cdot>x"
by (simp add: Ifup_def Iup_def Abs_Up_inverse2)

subsection {* Ordering on type @{typ "'a u"} *}

instance u :: (sq_ord) sq_ord ..

defs (overloaded)
  less_up_def: "(op \<sqsubseteq>) \<equiv> (\<lambda>x1 x2. case Rep_Up x1 of
               None \<Rightarrow> True
             | Some y1 \<Rightarrow> (case Rep_Up x2 of None \<Rightarrow> False
                                           | Some y2 \<Rightarrow> y1 \<sqsubseteq> y2))"

lemma minimal_up [iff]: "Abs_Up None \<sqsubseteq> z"
by (simp add: less_up_def Abs_Up_inverse2)

lemma not_Iup_less [iff]: "\<not> Iup x \<sqsubseteq> Abs_Up None"
by (simp add: Iup_def less_up_def Abs_Up_inverse2)

lemma Iup_less [iff]: "(Iup x \<sqsubseteq> Iup y) = (x \<sqsubseteq> y)"
by (simp add: Iup_def less_up_def Abs_Up_inverse2)

subsection {* Type @{typ "'a u"} is a partial order *}

lemma refl_less_up: "(p::'a u) \<sqsubseteq> p"
by (rule_tac p = "p" in upE, auto)

lemma antisym_less_up: "\<lbrakk>(p1::'a u) \<sqsubseteq> p2; p2 \<sqsubseteq> p1\<rbrakk> \<Longrightarrow> p1 = p2"
apply (rule_tac p = "p1" in upE)
apply (rule_tac p = "p2" in upE)
apply simp
apply simp
apply (rule_tac p = "p2" in upE)
apply simp
apply simp
apply (drule antisym_less, assumption)
apply simp
done

lemma trans_less_up: "\<lbrakk>(p1::'a u) \<sqsubseteq> p2; p2 \<sqsubseteq> p3\<rbrakk> \<Longrightarrow> p1 \<sqsubseteq> p3"
apply (rule_tac p = "p1" in upE)
apply simp
apply (rule_tac p = "p2" in upE)
apply simp
apply (rule_tac p = "p3" in upE)
apply simp
apply (auto elim: trans_less)
done

instance u :: (cpo) po
by intro_classes
  (assumption | rule refl_less_up antisym_less_up trans_less_up)+

subsection {* Type @{typ "'a u"} is a cpo *}

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (\<lambda>i. Iup (S i)) <<| Iup x"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst Iup_less)
apply (erule is_ub_lub)
apply (rule_tac p="u" in upE)
apply (drule ub_rangeD)
apply simp
apply simp
apply (erule is_lub_lub)
apply (rule ub_rangeI)
apply (drule_tac i=i in ub_rangeD)
apply simp
done

text {* Now some lemmas about chains of @{typ "'a u"} elements *}

lemma up_lemma1: "z \<noteq> Abs_Up None \<Longrightarrow> Iup (THE a. Iup a = z) = z"
by (rule_tac p="z" in upE, simp_all)

lemma up_lemma2:
  "\<lbrakk>chain Y; Y j \<noteq> Abs_Up None\<rbrakk> \<Longrightarrow> Y (i + j) \<noteq> Abs_Up None"
apply (erule contrapos_nn)
apply (drule_tac x="j" and y="i + j" in chain_mono3)
apply (rule le_add2)
apply (rule_tac p="Y j" in upE)
apply assumption
apply simp
done

lemma up_lemma3:
  "\<lbrakk>chain Y; Y j \<noteq> Abs_Up None\<rbrakk> \<Longrightarrow> Iup (THE a. Iup a = Y (i + j)) = Y (i + j)"
by (rule up_lemma1 [OF up_lemma2])

lemma up_lemma4:
  "\<lbrakk>chain Y; Y j \<noteq> Abs_Up None\<rbrakk> \<Longrightarrow> chain (\<lambda>i. THE a. Iup a = Y (i + j))"
apply (rule chainI)
apply (rule Iup_less [THEN iffD1])
apply (subst up_lemma3, assumption+)+
apply (simp add: chainE)
done

lemma up_lemma5:
  "\<lbrakk>chain Y; Y j \<noteq> Abs_Up None\<rbrakk> \<Longrightarrow>
    (\<lambda>i. Y (i + j)) = (\<lambda>i. Iup (THE a. Iup a = Y (i + j)))"
by (rule ext, rule up_lemma3 [symmetric])

lemma up_lemma6:
  "\<lbrakk>chain Y; Y j \<noteq> Abs_Up None\<rbrakk>  
      \<Longrightarrow> range Y <<| Iup (\<Squnion>i. THE a. Iup a = Y(i + j))"
apply (rule_tac j1="j" in is_lub_range_shift [THEN iffD1])
apply assumption
apply (subst up_lemma5, assumption+)
apply (rule is_lub_Iup)
apply (rule thelubE [OF _ refl])
apply (rule up_lemma4, assumption+)
done

lemma up_chain_cases:
  "chain Y \<Longrightarrow>
   (\<exists>A. chain A \<and> lub (range Y) = Iup (lub (range A)) \<and>
   (\<exists>j. \<forall>i. Y (i + j) = Iup (A i))) \<or> (Y = (\<lambda>i. Abs_Up None))"
apply (rule disjCI)
apply (simp add: expand_fun_eq)
apply (erule exE, rename_tac j)
apply (rule_tac x="\<lambda>i. THE a. Iup a = Y (i + j)" in exI)
apply (rule conjI)
apply (simp add: up_lemma4)
apply (rule conjI)
apply (simp add: up_lemma6 [THEN thelubI])
apply (rule_tac x=j in exI)
apply (simp add: up_lemma3)
done

lemma cpo_up: "chain (Y::nat \<Rightarrow> 'a u) \<Longrightarrow> \<exists>x. range Y <<| x"
apply (frule up_chain_cases, safe)
apply (rule_tac x="Iup (lub (range A))" in exI)
apply (erule_tac j1="j" in is_lub_range_shift [THEN iffD1])
apply (simp add: is_lub_Iup thelubE)
apply (rule_tac x="Abs_Up None" in exI)
apply (rule lub_const)
done

instance u :: (cpo) cpo
by intro_classes (rule cpo_up)

subsection {* Type @{typ "'a u"} is pointed *}

lemma least_up: "EX x::'a u. ALL y. x\<sqsubseteq>y"
apply (rule_tac x = "Abs_Up None" in exI)
apply (rule minimal_up [THEN allI])
done

instance u :: (cpo) pcpo
by intro_classes (rule least_up)

text {* for compatibility with old HOLCF-Version *}
lemma inst_up_pcpo: "\<bottom> = Abs_Up None"
by (rule minimal_up [THEN UU_I, symmetric])

text {* some lemmas restated for class pcpo *}

lemma less_up3b: "~ Iup(x) \<sqsubseteq> \<bottom>"
apply (subst inst_up_pcpo)
apply simp
done

lemma defined_Iup2 [iff]: "Iup(x) ~= \<bottom>"
apply (subst inst_up_pcpo)
apply (rule Iup_defined)
done

subsection {* Continuity of @{term Iup} and @{term Ifup} *}

text {* continuity for @{term Iup} *}

lemma cont_Iup: "cont Iup"
apply (rule contI)
apply (rule is_lub_Iup)
apply (erule thelubE [OF _ refl])
done

text {* continuity for @{term Ifup} *}

lemma cont_Ifup1: "cont (\<lambda>f. Ifup f x)"
apply (rule contI)
apply (rule_tac p="x" in upE)
apply (simp add: lub_const)
apply (simp add: cont_cfun_fun)
done

lemma monofun_Ifup2: "monofun (\<lambda>x. Ifup f x)"
apply (rule monofunI)
apply (rule_tac p="x" in upE)
apply simp
apply (rule_tac p="y" in upE)
apply simp
apply (simp add: monofun_cfun_arg)
done

lemma cont_Ifup2: "cont (\<lambda>x. Ifup f x)"
apply (rule contI)
apply (frule up_chain_cases, safe)
apply (rule_tac j1="j" in is_lub_range_shift [THEN iffD1])
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (simp add: cont_cfun_arg)
apply (simp add: thelub_const lub_const)
done

subsection {* Continuous versions of constants *}

constdefs  
  up  :: "'a \<rightarrow> 'a u"
  "up \<equiv> \<Lambda> x. Iup x"

  fup :: "('a \<rightarrow> 'b::pcpo) \<rightarrow> 'a u \<rightarrow> 'b"
  "fup \<equiv> \<Lambda> f p. Ifup f p"

translations
"case l of up\<cdot>x => t1" == "fup\<cdot>(LAM x. t1)\<cdot>l"

text {* continuous versions of lemmas for @{typ "('a)u"} *}

lemma Exh_Up1: "z = \<bottom> \<or> (\<exists>x. z = up\<cdot>x)"
apply (rule_tac p="z" in upE)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma up_inject: "up\<cdot>x = up\<cdot>y \<Longrightarrow> x = y"
by (simp add: up_def cont_Iup)

lemma up_eq [simp]: "(up\<cdot>x = up\<cdot>y) = (x = y)"
by (rule iffI, erule up_inject, simp)

lemma up_defined [simp]: " up\<cdot>x \<noteq> \<bottom>"
by (simp add: up_def cont_Iup inst_up_pcpo)

lemma not_up_less_UU [simp]: "\<not> up\<cdot>x \<sqsubseteq> \<bottom>"
by (simp add: eq_UU_iff [symmetric])

lemma up_less [simp]: "(up\<cdot>x \<sqsubseteq> up\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: up_def cont_Iup)

lemma upE1: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x. p = up\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (rule_tac p="p" in upE)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma fup1 [simp]: "fup\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: fup_def cont_Ifup1 cont_Ifup2 inst_up_pcpo)

lemma fup2 [simp]: "fup\<cdot>f\<cdot>(up\<cdot>x) = f\<cdot>x"
by (simp add: up_def fup_def cont_Iup cont_Ifup1 cont_Ifup2 )

lemma fup3 [simp]: "fup\<cdot>up\<cdot>x = x"
by (rule_tac p=x in upE1, simp_all)

end

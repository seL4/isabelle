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

datatype 'a u = Ibottom | Iup 'a

consts
  Ifup :: "('a \<rightarrow> 'b::pcpo) \<Rightarrow> 'a u \<Rightarrow> 'b"

primrec
  "Ifup f Ibottom = \<bottom>"
  "Ifup f (Iup x) = f\<cdot>x"

subsection {* Ordering on type @{typ "'a u"} *}

instance u :: (sq_ord) sq_ord ..

defs (overloaded)
  less_up_def:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. case x of Ibottom \<Rightarrow> True | Iup a \<Rightarrow>
      (case y of Ibottom \<Rightarrow> False | Iup b \<Rightarrow> a \<sqsubseteq> b))"

lemma minimal_up [iff]: "Ibottom \<sqsubseteq> z"
by (simp add: less_up_def)

lemma not_Iup_less [iff]: "\<not> Iup x \<sqsubseteq> Ibottom"
by (simp add: less_up_def)

lemma Iup_less [iff]: "(Iup x \<sqsubseteq> Iup y) = (x \<sqsubseteq> y)"
by (simp add: less_up_def)

subsection {* Type @{typ "'a u"} is a partial order *}

lemma refl_less_up: "(x::'a u) \<sqsubseteq> x"
by (simp add: less_up_def split: u.split)

lemma antisym_less_up: "\<lbrakk>(x::'a u) \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
apply (simp add: less_up_def split: u.split_asm)
apply (erule (1) antisym_less)
done

lemma trans_less_up: "\<lbrakk>(x::'a u) \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
apply (simp add: less_up_def split: u.split_asm)
apply (erule (1) trans_less)
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
apply (case_tac u)
apply (drule ub_rangeD)
apply simp
apply simp
apply (erule is_lub_lub)
apply (rule ub_rangeI)
apply (drule_tac i=i in ub_rangeD)
apply simp
done

text {* Now some lemmas about chains of @{typ "'a u"} elements *}

lemma up_lemma1: "z \<noteq> Ibottom \<Longrightarrow> Iup (THE a. Iup a = z) = z"
by (case_tac z, simp_all)

lemma up_lemma2:
  "\<lbrakk>chain Y; Y j \<noteq> Ibottom\<rbrakk> \<Longrightarrow> Y (i + j) \<noteq> Ibottom"
apply (erule contrapos_nn)
apply (drule_tac x="j" and y="i + j" in chain_mono3)
apply (rule le_add2)
apply (case_tac "Y j")
apply assumption
apply simp
done

lemma up_lemma3:
  "\<lbrakk>chain Y; Y j \<noteq> Ibottom\<rbrakk> \<Longrightarrow> Iup (THE a. Iup a = Y (i + j)) = Y (i + j)"
by (rule up_lemma1 [OF up_lemma2])

lemma up_lemma4:
  "\<lbrakk>chain Y; Y j \<noteq> Ibottom\<rbrakk> \<Longrightarrow> chain (\<lambda>i. THE a. Iup a = Y (i + j))"
apply (rule chainI)
apply (rule Iup_less [THEN iffD1])
apply (subst up_lemma3, assumption+)+
apply (simp add: chainE)
done

lemma up_lemma5:
  "\<lbrakk>chain Y; Y j \<noteq> Ibottom\<rbrakk> \<Longrightarrow>
    (\<lambda>i. Y (i + j)) = (\<lambda>i. Iup (THE a. Iup a = Y (i + j)))"
by (rule ext, rule up_lemma3 [symmetric])

lemma up_lemma6:
  "\<lbrakk>chain Y; Y j \<noteq> Ibottom\<rbrakk>  
      \<Longrightarrow> range Y <<| Iup (\<Squnion>i. THE a. Iup a = Y(i + j))"
apply (rule_tac j1 = j in is_lub_range_shift [THEN iffD1])
apply assumption
apply (subst up_lemma5, assumption+)
apply (rule is_lub_Iup)
apply (rule thelubE [OF _ refl])
apply (erule (1) up_lemma4)
done

lemma up_chain_lemma:
  "chain Y \<Longrightarrow>
   (\<exists>A. chain A \<and> lub (range Y) = Iup (lub (range A)) \<and>
   (\<exists>j. \<forall>i. Y (i + j) = Iup (A i))) \<or> (Y = (\<lambda>i. Ibottom))"
apply (rule disjCI)
apply (simp add: expand_fun_eq)
apply (erule exE, rename_tac j)
apply (rule_tac x="\<lambda>i. THE a. Iup a = Y (i + j)" in exI)
apply (simp add: up_lemma4)
apply (simp add: up_lemma6 [THEN thelubI])
apply (rule_tac x=j in exI)
apply (simp add: up_lemma3)
done

lemma cpo_up: "chain (Y::nat \<Rightarrow> 'a u) \<Longrightarrow> \<exists>x. range Y <<| x"
apply (frule up_chain_lemma, safe)
apply (rule_tac x="Iup (lub (range A))" in exI)
apply (erule_tac j="j" in is_lub_range_shift [THEN iffD1, standard])
apply (simp add: is_lub_Iup thelubE)
apply (rule exI, rule lub_const)
done

instance u :: (cpo) cpo
by intro_classes (rule cpo_up)

subsection {* Type @{typ "'a u"} is pointed *}

lemma least_up: "\<exists>x::'a u. \<forall>y. x \<sqsubseteq> y"
apply (rule_tac x = "Ibottom" in exI)
apply (rule minimal_up [THEN allI])
done

instance u :: (cpo) pcpo
by intro_classes (rule least_up)

text {* for compatibility with old HOLCF-Version *}
lemma inst_up_pcpo: "\<bottom> = Ibottom"
by (rule minimal_up [THEN UU_I, symmetric])

subsection {* Continuity of @{term Iup} and @{term Ifup} *}

text {* continuity for @{term Iup} *}

lemma cont_Iup: "cont Iup"
apply (rule contI)
apply (rule is_lub_Iup)
apply (erule thelubE [OF _ refl])
done

text {* continuity for @{term Ifup} *}

lemma cont_Ifup1: "cont (\<lambda>f. Ifup f x)"
by (induct x, simp_all)

lemma monofun_Ifup2: "monofun (\<lambda>x. Ifup f x)"
apply (rule monofunI)
apply (case_tac x, simp)
apply (case_tac y, simp)
apply (simp add: monofun_cfun_arg)
done

lemma cont_Ifup2: "cont (\<lambda>x. Ifup f x)"
apply (rule contI)
apply (frule up_chain_lemma, safe)
apply (rule_tac j="j" in is_lub_range_shift [THEN iffD1, standard])
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (simp add: cont_cfun_arg)
apply (simp add: lub_const)
done

subsection {* Continuous versions of constants *}

constdefs  
  up  :: "'a \<rightarrow> 'a u"
  "up \<equiv> \<Lambda> x. Iup x"

  fup :: "('a \<rightarrow> 'b::pcpo) \<rightarrow> 'a u \<rightarrow> 'b"
  "fup \<equiv> \<Lambda> f p. Ifup f p"

translations
  "case l of up\<cdot>x \<Rightarrow> t" == "fup\<cdot>(\<Lambda> x. t)\<cdot>l"
  "\<Lambda>(up\<cdot>x). t" == "fup\<cdot>(\<Lambda> x. t)"

text {* continuous versions of lemmas for @{typ "('a)u"} *}

lemma Exh_Up: "z = \<bottom> \<or> (\<exists>x. z = up\<cdot>x)"
apply (induct z)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma up_eq [simp]: "(up\<cdot>x = up\<cdot>y) = (x = y)"
by (simp add: up_def cont_Iup)

lemma up_inject: "up\<cdot>x = up\<cdot>y \<Longrightarrow> x = y"
by simp

lemma up_defined [simp]: "up\<cdot>x \<noteq> \<bottom>"
by (simp add: up_def cont_Iup inst_up_pcpo)

lemma not_up_less_UU [simp]: "\<not> up\<cdot>x \<sqsubseteq> \<bottom>"
by (simp add: eq_UU_iff [symmetric])

lemma up_less [simp]: "(up\<cdot>x \<sqsubseteq> up\<cdot>y) = (x \<sqsubseteq> y)"
by (simp add: up_def cont_Iup)

lemma upE: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x. p = up\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (case_tac p)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma up_chain_cases:
  "chain Y \<Longrightarrow>
  (\<exists>A. chain A \<and> (\<Squnion>i. Y i) = up\<cdot>(\<Squnion>i. A i) \<and>
  (\<exists>j. \<forall>i. Y (i + j) = up\<cdot>(A i))) \<or> Y = (\<lambda>i. \<bottom>)"
by (simp add: inst_up_pcpo up_def cont_Iup up_chain_lemma)

lemma compact_up [simp]: "compact x \<Longrightarrow> compact (up\<cdot>x)"
apply (unfold compact_def)
apply (rule admI)
apply (drule up_chain_cases)
apply (elim disjE exE conjE)
apply simp
apply (erule (1) admD)
apply (rule allI, drule_tac x="i + j" in spec)
apply simp
apply simp
done

text {* properties of fup *}

lemma fup1 [simp]: "fup\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: fup_def cont_Ifup1 cont_Ifup2 inst_up_pcpo)

lemma fup2 [simp]: "fup\<cdot>f\<cdot>(up\<cdot>x) = f\<cdot>x"
by (simp add: up_def fup_def cont_Iup cont_Ifup1 cont_Ifup2)

lemma fup3 [simp]: "fup\<cdot>up\<cdot>x = x"
by (rule_tac p=x in upE, simp_all)

end

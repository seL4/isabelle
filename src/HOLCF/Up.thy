(*  Title:      HOLCF/Up.thy
    Author:     Franz Regensburger and Brian Huffman
*)

header {* The type of lifted values *}

theory Up
imports Bifinite
begin

defaultsort cpo

subsection {* Definition of new type for lifting *}

datatype 'a u = Ibottom | Iup 'a

syntax (xsymbols)
  "u" :: "type \<Rightarrow> type" ("(_\<^sub>\<bottom>)" [1000] 999)

consts
  Ifup :: "('a \<rightarrow> 'b::pcpo) \<Rightarrow> 'a u \<Rightarrow> 'b"

primrec
  "Ifup f Ibottom = \<bottom>"
  "Ifup f (Iup x) = f\<cdot>x"

subsection {* Ordering on lifted cpo *}

instantiation u :: (cpo) below
begin

definition
  below_up_def:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. case x of Ibottom \<Rightarrow> True | Iup a \<Rightarrow>
      (case y of Ibottom \<Rightarrow> False | Iup b \<Rightarrow> a \<sqsubseteq> b))"

instance ..
end

lemma minimal_up [iff]: "Ibottom \<sqsubseteq> z"
by (simp add: below_up_def)

lemma not_Iup_below [iff]: "\<not> Iup x \<sqsubseteq> Ibottom"
by (simp add: below_up_def)

lemma Iup_below [iff]: "(Iup x \<sqsubseteq> Iup y) = (x \<sqsubseteq> y)"
by (simp add: below_up_def)

subsection {* Lifted cpo is a partial order *}

instance u :: (cpo) po
proof
  fix x :: "'a u"
  show "x \<sqsubseteq> x"
    unfolding below_up_def by (simp split: u.split)
next
  fix x y :: "'a u"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding below_up_def
    by (auto split: u.split_asm intro: below_antisym)
next
  fix x y z :: "'a u"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding below_up_def
    by (auto split: u.split_asm intro: below_trans)
qed

lemma u_UNIV: "UNIV = insert Ibottom (range Iup)"
by (auto, case_tac x, auto)

instance u :: (finite_po) finite_po
by (intro_classes, simp add: u_UNIV)


subsection {* Lifted cpo is a cpo *}

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (\<lambda>i. Iup (S i)) <<| Iup x"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst Iup_below)
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
apply (drule_tac i="j" and j="i + j" in chain_mono)
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
apply (rule Iup_below [THEN iffD1])
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
apply (rule cpo_lubI)
apply (erule (1) up_lemma4)
done

lemma up_chain_lemma:
  "chain Y \<Longrightarrow>
   (\<exists>A. chain A \<and> (\<Squnion>i. Y i) = Iup (\<Squnion>i. A i) \<and>
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
apply (rule_tac x="Iup (\<Squnion>i. A i)" in exI)
apply (erule_tac j="j" in is_lub_range_shift [THEN iffD1, standard])
apply (simp add: is_lub_Iup cpo_lubI)
apply (rule exI, rule lub_const)
done

instance u :: (cpo) cpo
by intro_classes (rule cpo_up)

subsection {* Lifted cpo is pointed *}

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
apply (erule cpo_lubI)
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

definition
  up  :: "'a \<rightarrow> 'a u" where
  "up = (\<Lambda> x. Iup x)"

definition
  fup :: "('a \<rightarrow> 'b::pcpo) \<rightarrow> 'a u \<rightarrow> 'b" where
  "fup = (\<Lambda> f p. Ifup f p)"

translations
  "case l of XCONST up\<cdot>x \<Rightarrow> t" == "CONST fup\<cdot>(\<Lambda> x. t)\<cdot>l"
  "\<Lambda>(XCONST up\<cdot>x). t" == "CONST fup\<cdot>(\<Lambda> x. t)"

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

lemma not_up_less_UU: "\<not> up\<cdot>x \<sqsubseteq> \<bottom>"
by simp (* FIXME: remove? *)

lemma up_below [simp]: "up\<cdot>x \<sqsubseteq> up\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
by (simp add: up_def cont_Iup)

lemma upE [cases type: u]: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x. p = up\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma up_induct [induct type: u]: "\<lbrakk>P \<bottom>; \<And>x. P (up\<cdot>x)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

text {* lifting preserves chain-finiteness *}

lemma up_chain_cases:
  "chain Y \<Longrightarrow>
  (\<exists>A. chain A \<and> (\<Squnion>i. Y i) = up\<cdot>(\<Squnion>i. A i) \<and>
  (\<exists>j. \<forall>i. Y (i + j) = up\<cdot>(A i))) \<or> Y = (\<lambda>i. \<bottom>)"
by (simp add: inst_up_pcpo up_def cont_Iup up_chain_lemma)

lemma compact_up: "compact x \<Longrightarrow> compact (up\<cdot>x)"
apply (rule compactI2)
apply (drule up_chain_cases, safe)
apply (drule (1) compactD2, simp)
apply (erule exE, rule_tac x="i + j" in exI)
apply simp
apply simp
done

lemma compact_upD: "compact (up\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_CFun2 [where f=up]], simp)

lemma compact_up_iff [simp]: "compact (up\<cdot>x) = compact x"
by (safe elim!: compact_up compact_upD)

instance u :: (chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (rule_tac p="\<Squnion>i. Y i" in upE, simp_all)
done

text {* properties of fup *}

lemma fup1 [simp]: "fup\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: fup_def cont_Ifup1 cont_Ifup2 inst_up_pcpo cont2cont_LAM)

lemma fup2 [simp]: "fup\<cdot>f\<cdot>(up\<cdot>x) = f\<cdot>x"
by (simp add: up_def fup_def cont_Iup cont_Ifup1 cont_Ifup2 cont2cont_LAM)

lemma fup3 [simp]: "fup\<cdot>up\<cdot>x = x"
by (cases x, simp_all)

subsection {* Map function for lifted cpo *}

definition
  u_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a u \<rightarrow> 'b u"
where
  "u_map = (\<Lambda> f. fup\<cdot>(up oo f))"

lemma u_map_strict [simp]: "u_map\<cdot>f\<cdot>\<bottom> = \<bottom>"
unfolding u_map_def by simp

lemma u_map_up [simp]: "u_map\<cdot>f\<cdot>(up\<cdot>x) = up\<cdot>(f\<cdot>x)"
unfolding u_map_def by simp

lemma ep_pair_u_map: "ep_pair e p \<Longrightarrow> ep_pair (u_map\<cdot>e) (u_map\<cdot>p)"
apply default
apply (case_tac x, simp, simp add: ep_pair.e_inverse)
apply (case_tac y, simp, simp add: ep_pair.e_p_below)
done

lemma deflation_u_map: "deflation d \<Longrightarrow> deflation (u_map\<cdot>d)"
apply default
apply (case_tac x, simp, simp add: deflation.idem)
apply (case_tac x, simp, simp add: deflation.below)
done

lemma finite_deflation_u_map:
  assumes "finite_deflation d" shows "finite_deflation (u_map\<cdot>d)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (u_map\<cdot>d)" by (rule deflation_u_map)
  have "{x. u_map\<cdot>d\<cdot>x = x} \<subseteq> insert \<bottom> ((\<lambda>x. up\<cdot>x) ` {x. d\<cdot>x = x})"
    by (rule subsetI, case_tac x, simp_all)
  thus "finite {x. u_map\<cdot>d\<cdot>x = x}"
    by (rule finite_subset, simp add: d.finite_fixes)
qed

subsection {* Lifted cpo is a bifinite domain *}

instantiation u :: (profinite) bifinite
begin

definition
  approx_up_def:
    "approx = (\<lambda>n. u_map\<cdot>(approx n))"

instance proof
  fix i :: nat and x :: "'a u"
  show "chain (approx :: nat \<Rightarrow> 'a u \<rightarrow> 'a u)"
    unfolding approx_up_def by simp
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_up_def
    by (induct x, simp, simp add: lub_distribs)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx_up_def
    by (induct x) simp_all
  show "finite {x::'a u. approx i\<cdot>x = x}"
    unfolding approx_up_def
    by (intro finite_deflation.finite_fixes
              finite_deflation_u_map
              finite_deflation_approx)
qed

end

lemma approx_up [simp]: "approx i\<cdot>(up\<cdot>x) = up\<cdot>(approx i\<cdot>x)"
unfolding approx_up_def by simp

end

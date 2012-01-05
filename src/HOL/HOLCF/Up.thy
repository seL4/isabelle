(*  Title:      HOL/HOLCF/Up.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

header {* The type of lifted values *}

theory Up
imports Cfun
begin

default_sort cpo

subsection {* Definition of new type for lifting *}

datatype 'a u = Ibottom | Iup 'a

type_notation (xsymbols)
  u  ("(_\<^sub>\<bottom>)" [1000] 999)

primrec Ifup :: "('a \<rightarrow> 'b::pcpo) \<Rightarrow> 'a u \<Rightarrow> 'b" where
    "Ifup f Ibottom = \<bottom>"
 |  "Ifup f (Iup x) = f\<cdot>x"

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

lemma not_Iup_below [iff]: "Iup x \<notsqsubseteq> Ibottom"
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

subsection {* Lifted cpo is a cpo *}

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (\<lambda>i. Iup (S i)) <<| Iup x"
unfolding is_lub_def is_ub_def ball_simps
by (auto simp add: below_up_def split: u.split)

lemma up_chain_lemma:
  assumes Y: "chain Y" obtains "\<forall>i. Y i = Ibottom"
  | A k where "\<forall>i. Iup (A i) = Y (i + k)" and "chain A" and "range Y <<| Iup (\<Squnion>i. A i)"
proof (cases "\<exists>k. Y k \<noteq> Ibottom")
  case True
  then obtain k where k: "Y k \<noteq> Ibottom" ..
  def A \<equiv> "\<lambda>i. THE a. Iup a = Y (i + k)"
  have Iup_A: "\<forall>i. Iup (A i) = Y (i + k)"
  proof
    fix i :: nat
    from Y le_add2 have "Y k \<sqsubseteq> Y (i + k)" by (rule chain_mono)
    with k have "Y (i + k) \<noteq> Ibottom" by (cases "Y k", auto)
    thus "Iup (A i) = Y (i + k)"
      by (cases "Y (i + k)", simp_all add: A_def)
  qed
  from Y have chain_A: "chain A"
    unfolding chain_def Iup_below [symmetric]
    by (simp add: Iup_A)
  hence "range A <<| (\<Squnion>i. A i)"
    by (rule cpo_lubI)
  hence "range (\<lambda>i. Iup (A i)) <<| Iup (\<Squnion>i. A i)"
    by (rule is_lub_Iup)
  hence "range (\<lambda>i. Y (i + k)) <<| Iup (\<Squnion>i. A i)"
    by (simp only: Iup_A)
  hence "range (\<lambda>i. Y i) <<| Iup (\<Squnion>i. A i)"
    by (simp only: is_lub_range_shift [OF Y])
  with Iup_A chain_A show ?thesis ..
next
  case False
  then have "\<forall>i. Y i = Ibottom" by simp
  then show ?thesis ..
qed

instance u :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a u"
  assume S: "chain S"
  thus "\<exists>x. range (\<lambda>i. S i) <<| x"
  proof (rule up_chain_lemma)
    assume "\<forall>i. S i = Ibottom"
    hence "range (\<lambda>i. S i) <<| Ibottom"
      by (simp add: is_lub_const)
    thus ?thesis ..
  next
    fix A :: "nat \<Rightarrow> 'a"
    assume "range S <<| Iup (\<Squnion>i. A i)"
    thus ?thesis ..
  qed
qed

subsection {* Lifted cpo is pointed *}

instance u :: (cpo) pcpo
by intro_classes fast

text {* for compatibility with old HOLCF-Version *}
lemma inst_up_pcpo: "\<bottom> = Ibottom"
by (rule minimal_up [THEN bottomI, symmetric])

subsection {* Continuity of \emph{Iup} and \emph{Ifup} *}

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
proof (rule contI2)
  fix Y assume Y: "chain Y" and Y': "chain (\<lambda>i. Ifup f (Y i))"
  from Y show "Ifup f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Ifup f (Y i))"
  proof (rule up_chain_lemma)
    fix A and k
    assume A: "\<forall>i. Iup (A i) = Y (i + k)"
    assume "chain A" and "range Y <<| Iup (\<Squnion>i. A i)"
    hence "Ifup f (\<Squnion>i. Y i) = (\<Squnion>i. Ifup f (Iup (A i)))"
      by (simp add: lub_eqI contlub_cfun_arg)
    also have "\<dots> = (\<Squnion>i. Ifup f (Y (i + k)))"
      by (simp add: A)
    also have "\<dots> = (\<Squnion>i. Ifup f (Y i))"
      using Y' by (rule lub_range_shift)
    finally show ?thesis by simp
  qed simp
qed (rule monofun_Ifup2)

subsection {* Continuous versions of constants *}

definition
  up  :: "'a \<rightarrow> 'a u" where
  "up = (\<Lambda> x. Iup x)"

definition
  fup :: "('a \<rightarrow> 'b::pcpo) \<rightarrow> 'a u \<rightarrow> 'b" where
  "fup = (\<Lambda> f p. Ifup f p)"

translations
  "case l of XCONST up\<cdot>x \<Rightarrow> t" == "CONST fup\<cdot>(\<Lambda> x. t)\<cdot>l"
  "case l of (XCONST up :: 'a)\<cdot>x \<Rightarrow> t" => "CONST fup\<cdot>(\<Lambda> x. t)\<cdot>l"
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

lemma not_up_less_UU: "up\<cdot>x \<notsqsubseteq> \<bottom>"
by simp (* FIXME: remove? *)

lemma up_below [simp]: "up\<cdot>x \<sqsubseteq> up\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
by (simp add: up_def cont_Iup)

lemma upE [case_names bottom up, cases type: u]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; \<And>x. p = up\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp add: inst_up_pcpo)
apply (simp add: up_def cont_Iup)
done

lemma up_induct [case_names bottom up, induct type: u]:
  "\<lbrakk>P \<bottom>; \<And>x. P (up\<cdot>x)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

text {* lifting preserves chain-finiteness *}

lemma up_chain_cases:
  assumes Y: "chain Y" obtains "\<forall>i. Y i = \<bottom>"
  | A k where "\<forall>i. up\<cdot>(A i) = Y (i + k)" and "chain A" and "(\<Squnion>i. Y i) = up\<cdot>(\<Squnion>i. A i)"
apply (rule up_chain_lemma [OF Y])
apply (simp_all add: inst_up_pcpo up_def cont_Iup lub_eqI)
done

lemma compact_up: "compact x \<Longrightarrow> compact (up\<cdot>x)"
apply (rule compactI2)
apply (erule up_chain_cases)
apply simp
apply (drule (1) compactD2, simp)
apply (erule exE)
apply (drule_tac f="up" and x="x" in monofun_cfun_arg)
apply (simp, erule exI)
done

lemma compact_upD: "compact (up\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_cfun2 [where f=up]], simp)

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

end

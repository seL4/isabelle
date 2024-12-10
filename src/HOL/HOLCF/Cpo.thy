(*  Title:      HOL/HOLCF/Cpo.thy
    Author:     Franz Regensburger
    Author:     Tobias Nipkow
    Author:     Brian Huffman

Foundations of HOLCF: complete partial orders etc.
*)

theory Cpo
  imports Main
begin

section \<open>Partial orders\<close>

declare [[typedef_overloaded]]


subsection \<open>Type class for partial orders\<close>

class below =
  fixes below :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation (ASCII)
  below (infix \<open><<\<close> 50)

notation
  below (infix \<open>\<sqsubseteq>\<close> 50)

abbreviation not_below :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix \<open>\<notsqsubseteq>\<close> 50)
  where "not_below x y \<equiv> \<not> below x y"

notation (ASCII)
  not_below  (infix \<open>~<<\<close> 50)

lemma below_eq_trans: "a \<sqsubseteq> b \<Longrightarrow> b = c \<Longrightarrow> a \<sqsubseteq> c"
  by (rule subst)

lemma eq_below_trans: "a = b \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> a \<sqsubseteq> c"
  by (rule ssubst)

end

class po = below +
  assumes below_refl [iff]: "x \<sqsubseteq> x"
  assumes below_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  assumes below_antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
begin

lemma eq_imp_below: "x = y \<Longrightarrow> x \<sqsubseteq> y"
  by simp

lemma box_below: "a \<sqsubseteq> b \<Longrightarrow> c \<sqsubseteq> a \<Longrightarrow> b \<sqsubseteq> d \<Longrightarrow> c \<sqsubseteq> d"
  by (rule below_trans [OF below_trans])

lemma po_eq_conv: "x = y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
  by (fast intro!: below_antisym)

lemma rev_below_trans: "y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z"
  by (rule below_trans)

lemma not_below2not_eq: "x \<notsqsubseteq> y \<Longrightarrow> x \<noteq> y"
  by auto

end

lemmas HOLCF_trans_rules [trans] =
  below_trans
  below_antisym
  below_eq_trans
  eq_below_trans

context po
begin

subsection \<open>Upper bounds\<close>

definition is_ub :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open><|\<close> 55)
  where "S <| x \<longleftrightarrow> (\<forall>y\<in>S. y \<sqsubseteq> x)"

lemma is_ubI: "(\<And>x. x \<in> S \<Longrightarrow> x \<sqsubseteq> u) \<Longrightarrow> S <| u"
  by (simp add: is_ub_def)

lemma is_ubD: "\<lbrakk>S <| u; x \<in> S\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u"
  by (simp add: is_ub_def)

lemma ub_imageI: "(\<And>x. x \<in> S \<Longrightarrow> f x \<sqsubseteq> u) \<Longrightarrow> (\<lambda>x. f x) ` S <| u"
  unfolding is_ub_def by fast

lemma ub_imageD: "\<lbrakk>f ` S <| u; x \<in> S\<rbrakk> \<Longrightarrow> f x \<sqsubseteq> u"
  unfolding is_ub_def by fast

lemma ub_rangeI: "(\<And>i. S i \<sqsubseteq> x) \<Longrightarrow> range S <| x"
  unfolding is_ub_def by fast

lemma ub_rangeD: "range S <| x \<Longrightarrow> S i \<sqsubseteq> x"
  unfolding is_ub_def by fast

lemma is_ub_empty [simp]: "{} <| u"
  unfolding is_ub_def by fast

lemma is_ub_insert [simp]: "(insert x A) <| y = (x \<sqsubseteq> y \<and> A <| y)"
  unfolding is_ub_def by fast

lemma is_ub_upward: "\<lbrakk>S <| x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> S <| y"
  unfolding is_ub_def by (fast intro: below_trans)


subsection \<open>Least upper bounds\<close>

definition is_lub :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open><<|\<close> 55)
  where "S <<| x \<longleftrightarrow> S <| x \<and> (\<forall>u. S <| u \<longrightarrow> x \<sqsubseteq> u)"

definition lub :: "'a set \<Rightarrow> 'a"
  where "lub S = (THE x. S <<| x)"

end

syntax (ASCII)
  "_BLub" :: "[pttrn, 'a set, 'b] \<Rightarrow> 'b" (\<open>(\<open>indent=3 notation=\<open>binder LUB\<close>\<close>LUB _:_./ _)\<close> [0,0, 10] 10)

syntax
  "_BLub" :: "[pttrn, 'a set, 'b] \<Rightarrow> 'b" (\<open>(\<open>indent=3 notation=\<open>binder \<Squnion>\<close>\<close>\<Squnion>_\<in>_./ _)\<close> [0,0, 10] 10)

syntax_consts
  "_BLub" \<rightleftharpoons> lub

translations
  "LUB x:A. t" \<rightleftharpoons> "CONST lub ((\<lambda>x. t) ` A)"

context po
begin

abbreviation Lub  (binder \<open>\<Squnion>\<close> 10)
  where "\<Squnion>n. t n \<equiv> lub (range t)"

notation (ASCII)
  Lub  (binder \<open>LUB \<close> 10)

text \<open>access to some definition as inference rule\<close>

lemma is_lubD1: "S <<| x \<Longrightarrow> S <| x"
  unfolding is_lub_def by fast

lemma is_lubD2: "\<lbrakk>S <<| x; S <| u\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u"
  unfolding is_lub_def by fast

lemma is_lubI: "\<lbrakk>S <| x; \<And>u. S <| u \<Longrightarrow> x \<sqsubseteq> u\<rbrakk> \<Longrightarrow> S <<| x"
  unfolding is_lub_def by fast

lemma is_lub_below_iff: "S <<| x \<Longrightarrow> x \<sqsubseteq> u \<longleftrightarrow> S <| u"
  unfolding is_lub_def is_ub_def by (metis below_trans)

text \<open>lubs are unique\<close>

lemma is_lub_unique: "S <<| x \<Longrightarrow> S <<| y \<Longrightarrow> x = y"
  unfolding is_lub_def is_ub_def by (blast intro: below_antisym)

text \<open>technical lemmas about \<^term>\<open>lub\<close> and \<^term>\<open>is_lub\<close>\<close>

lemma is_lub_lub: "M <<| x \<Longrightarrow> M <<| lub M"
  unfolding lub_def by (rule theI [OF _ is_lub_unique])

lemma lub_eqI: "M <<| l \<Longrightarrow> lub M = l"
  by (rule is_lub_unique [OF is_lub_lub])

lemma is_lub_singleton [simp]: "{x} <<| x"
  by (simp add: is_lub_def)

lemma lub_singleton [simp]: "lub {x} = x"
  by (rule is_lub_singleton [THEN lub_eqI])

lemma is_lub_bin: "x \<sqsubseteq> y \<Longrightarrow> {x, y} <<| y"
  by (simp add: is_lub_def)

lemma lub_bin: "x \<sqsubseteq> y \<Longrightarrow> lub {x, y} = y"
  by (rule is_lub_bin [THEN lub_eqI])

lemma is_lub_maximal: "S <| x \<Longrightarrow> x \<in> S \<Longrightarrow> S <<| x"
  by (erule is_lubI, erule (1) is_ubD)

lemma lub_maximal: "S <| x \<Longrightarrow> x \<in> S \<Longrightarrow> lub S = x"
  by (rule is_lub_maximal [THEN lub_eqI])


subsection \<open>Countable chains\<close>

definition chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where \<comment> \<open>Here we use countable chains and I prefer to code them as functions!\<close>
  "chain Y = (\<forall>i. Y i \<sqsubseteq> Y (Suc i))"

lemma chainI: "(\<And>i. Y i \<sqsubseteq> Y (Suc i)) \<Longrightarrow> chain Y"
  unfolding chain_def by fast

lemma chainE: "chain Y \<Longrightarrow> Y i \<sqsubseteq> Y (Suc i)"
  unfolding chain_def by fast

text \<open>chains are monotone functions\<close>

lemma chain_mono_less: "chain Y \<Longrightarrow> i < j \<Longrightarrow> Y i \<sqsubseteq> Y j"
  by (erule less_Suc_induct, erule chainE, erule below_trans)

lemma chain_mono: "chain Y \<Longrightarrow> i \<le> j \<Longrightarrow> Y i \<sqsubseteq> Y j"
  by (cases "i = j") (simp_all add: chain_mono_less)

lemma chain_shift: "chain Y \<Longrightarrow> chain (\<lambda>i. Y (i + j))"
  by (rule chainI, simp, erule chainE)

text \<open>technical lemmas about (least) upper bounds of chains\<close>

lemma is_lub_rangeD1: "range S <<| x \<Longrightarrow> S i \<sqsubseteq> x"
  by (rule is_lubD1 [THEN ub_rangeD])

lemma is_ub_range_shift: "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <| x = range S <| x"
  apply (rule iffI)
   apply (rule ub_rangeI)
   apply (rule_tac y="S (i + j)" in below_trans)
    apply (erule chain_mono)
    apply (rule le_add1)
   apply (erule ub_rangeD)
  apply (rule ub_rangeI)
  apply (erule ub_rangeD)
  done

lemma is_lub_range_shift: "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <<| x = range S <<| x"
  by (simp add: is_lub_def is_ub_range_shift)

text \<open>the lub of a constant chain is the constant\<close>

lemma chain_const [simp]: "chain (\<lambda>i. c)"
  by (simp add: chainI)

lemma is_lub_const: "range (\<lambda>x. c) <<| c"
by (blast dest: ub_rangeD intro: is_lubI ub_rangeI)

lemma lub_const [simp]: "(\<Squnion>i. c) = c"
  by (rule is_lub_const [THEN lub_eqI])


subsection \<open>Finite chains\<close>

definition max_in_chain :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where \<comment> \<open>finite chains, needed for monotony of continuous functions\<close>
  "max_in_chain i C \<longleftrightarrow> (\<forall>j. i \<le> j \<longrightarrow> C i = C j)"

definition finite_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "finite_chain C = (chain C \<and> (\<exists>i. max_in_chain i C))"

text \<open>results about finite chains\<close>

lemma max_in_chainI: "(\<And>j. i \<le> j \<Longrightarrow> Y i = Y j) \<Longrightarrow> max_in_chain i Y"
  unfolding max_in_chain_def by fast

lemma max_in_chainD: "max_in_chain i Y \<Longrightarrow> i \<le> j \<Longrightarrow> Y i = Y j"
  unfolding max_in_chain_def by fast

lemma finite_chainI: "chain C \<Longrightarrow> max_in_chain i C \<Longrightarrow> finite_chain C"
  unfolding finite_chain_def by fast

lemma finite_chainE: "\<lbrakk>finite_chain C; \<And>i. \<lbrakk>chain C; max_in_chain i C\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding finite_chain_def by fast

lemma lub_finch1: "chain C \<Longrightarrow> max_in_chain i C \<Longrightarrow> range C <<| C i"
  apply (rule is_lubI)
   apply (rule ub_rangeI, rename_tac j)
   apply (rule_tac x=i and y=j in linorder_le_cases)
    apply (drule (1) max_in_chainD, simp)
   apply (erule (1) chain_mono)
  apply (erule ub_rangeD)
  done

lemma lub_finch2: "finite_chain C \<Longrightarrow> range C <<| C (LEAST i. max_in_chain i C)"
  apply (erule finite_chainE)
  apply (erule LeastI2 [where Q="\<lambda>i. range C <<| C i"])
  apply (erule (1) lub_finch1)
  done

lemma finch_imp_finite_range: "finite_chain Y \<Longrightarrow> finite (range Y)"
  apply (erule finite_chainE)
  apply (rule_tac B="Y ` {..i}" in finite_subset)
   apply (rule subsetI)
   apply (erule rangeE, rename_tac j)
   apply (rule_tac x=i and y=j in linorder_le_cases)
    apply (subgoal_tac "Y j = Y i", simp)
    apply (simp add: max_in_chain_def)
   apply simp
  apply simp
  done

lemma finite_range_has_max:
  fixes f :: "nat \<Rightarrow> 'a"
    and r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>i j. i \<le> j \<Longrightarrow> r (f i) (f j)"
  assumes finite_range: "finite (range f)"
  shows "\<exists>k. \<forall>i. r (f i) (f k)"
proof (intro exI allI)
  fix i :: nat
  let ?j = "LEAST k. f k = f i"
  let ?k = "Max ((\<lambda>x. LEAST k. f k = x) ` range f)"
  have "?j \<le> ?k"
  proof (rule Max_ge)
    show "finite ((\<lambda>x. LEAST k. f k = x) ` range f)"
      using finite_range by (rule finite_imageI)
    show "?j \<in> (\<lambda>x. LEAST k. f k = x) ` range f"
      by (intro imageI rangeI)
  qed
  hence "r (f ?j) (f ?k)"
    by (rule mono)
  also have "f ?j = f i"
    by (rule LeastI, rule refl)
  finally show "r (f i) (f ?k)" .
qed

lemma finite_range_imp_finch: "chain Y \<Longrightarrow> finite (range Y) \<Longrightarrow> finite_chain Y"
  apply (subgoal_tac "\<exists>k. \<forall>i. Y i \<sqsubseteq> Y k")
   apply (erule exE)
   apply (rule finite_chainI, assumption)
   apply (rule max_in_chainI)
   apply (rule below_antisym)
    apply (erule (1) chain_mono)
   apply (erule spec)
  apply (rule finite_range_has_max)
   apply (erule (1) chain_mono)
  apply assumption
  done

lemma bin_chain: "x \<sqsubseteq> y \<Longrightarrow> chain (\<lambda>i. if i=0 then x else y)"
  by (rule chainI) simp

lemma bin_chainmax: "x \<sqsubseteq> y \<Longrightarrow> max_in_chain (Suc 0) (\<lambda>i. if i=0 then x else y)"
  by (simp add: max_in_chain_def)

lemma is_lub_bin_chain: "x \<sqsubseteq> y \<Longrightarrow> range (\<lambda>i::nat. if i=0 then x else y) <<| y"
  apply (frule bin_chain)
  apply (drule bin_chainmax)
  apply (drule (1) lub_finch1)
  apply simp
  done

text \<open>the maximal element in a chain is its lub\<close>

lemma lub_chain_maxelem: "Y i = c \<Longrightarrow> \<forall>i. Y i \<sqsubseteq> c \<Longrightarrow> lub (range Y) = c"
  by (blast dest: ub_rangeD intro: lub_eqI is_lubI ub_rangeI)

end


section \<open>Classes cpo and pcpo\<close>

subsection \<open>Complete partial orders\<close>

text \<open>The class cpo of chain complete partial orders\<close>

class cpo = po +
  assumes cpo: "chain S \<Longrightarrow> \<exists>x. range S <<| x"
begin

text \<open>in cpo's everthing equal to THE lub has lub properties for every chain\<close>

lemma cpo_lubI: "chain S \<Longrightarrow> range S <<| (\<Squnion>i. S i)"
  by (fast dest: cpo elim: is_lub_lub)

lemma thelubE: "\<lbrakk>chain S; (\<Squnion>i. S i) = l\<rbrakk> \<Longrightarrow> range S <<| l"
  by (blast dest: cpo intro: is_lub_lub)

text \<open>Properties of the lub\<close>

lemma is_ub_thelub: "chain S \<Longrightarrow> S x \<sqsubseteq> (\<Squnion>i. S i)"
  by (blast dest: cpo intro: is_lub_lub [THEN is_lub_rangeD1])

lemma is_lub_thelub: "\<lbrakk>chain S; range S <| x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
  by (blast dest: cpo intro: is_lub_lub [THEN is_lubD2])

lemma lub_below_iff: "chain S \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x \<longleftrightarrow> (\<forall>i. S i \<sqsubseteq> x)"
  by (simp add: is_lub_below_iff [OF cpo_lubI] is_ub_def)

lemma lub_below: "\<lbrakk>chain S; \<And>i. S i \<sqsubseteq> x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
  by (simp add: lub_below_iff)

lemma below_lub: "\<lbrakk>chain S; x \<sqsubseteq> S i\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. S i)"
  by (erule below_trans, erule is_ub_thelub)

lemma lub_range_mono: "\<lbrakk>range X \<subseteq> range Y; chain Y; chain X\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
  apply (erule lub_below)
  apply (subgoal_tac "\<exists>j. X i = Y j")
   apply clarsimp
   apply (erule is_ub_thelub)
  apply auto
  done

lemma lub_range_shift: "chain Y \<Longrightarrow> (\<Squnion>i. Y (i + j)) = (\<Squnion>i. Y i)"
  apply (rule below_antisym)
   apply (rule lub_range_mono)
     apply fast
    apply assumption
   apply (erule chain_shift)
  apply (rule lub_below)
   apply assumption
  apply (rule_tac i="i" in below_lub)
   apply (erule chain_shift)
  apply (erule chain_mono)
  apply (rule le_add1)
  done

lemma maxinch_is_thelub: "chain Y \<Longrightarrow> max_in_chain i Y = ((\<Squnion>i. Y i) = Y i)"
  apply (rule iffI)
   apply (fast intro!: lub_eqI lub_finch1)
  apply (unfold max_in_chain_def)
  apply (safe intro!: below_antisym)
   apply (fast elim!: chain_mono)
  apply (drule sym)
  apply (force elim!: is_ub_thelub)
  done

text \<open>the \<open>\<sqsubseteq>\<close> relation between two chains is preserved by their lubs\<close>

lemma lub_mono: "\<lbrakk>chain X; chain Y; \<And>i. X i \<sqsubseteq> Y i\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
  by (fast elim: lub_below below_lub)

text \<open>the = relation between two chains is preserved by their lubs\<close>

lemma lub_eq: "(\<And>i. X i = Y i) \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
  by simp

lemma ch2ch_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "chain (\<lambda>i. \<Squnion>j. Y i j)"
  apply (rule chainI)
  apply (rule lub_mono [OF 2 2])
  apply (rule chainE [OF 1])
  done

lemma diag_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>i. Y i i)"
proof (rule below_antisym)
  have 3: "chain (\<lambda>i. Y i i)"
    apply (rule chainI)
    apply (rule below_trans)
     apply (rule chainE [OF 1])
    apply (rule chainE [OF 2])
    done
  have 4: "chain (\<lambda>i. \<Squnion>j. Y i j)"
    by (rule ch2ch_lub [OF 1 2])
  show "(\<Squnion>i. \<Squnion>j. Y i j) \<sqsubseteq> (\<Squnion>i. Y i i)"
    apply (rule lub_below [OF 4])
    apply (rule lub_below [OF 2])
    apply (rule below_lub [OF 3])
    apply (rule below_trans)
     apply (rule chain_mono [OF 1 max.cobounded1])
    apply (rule chain_mono [OF 2 max.cobounded2])
    done
  show "(\<Squnion>i. Y i i) \<sqsubseteq> (\<Squnion>i. \<Squnion>j. Y i j)"
    apply (rule lub_mono [OF 3 4])
    apply (rule is_ub_thelub [OF 2])
    done
qed

lemma ex_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>j. \<Squnion>i. Y i j)"
  by (simp add: diag_lub 1 2)

end


subsection \<open>Pointed cpos\<close>

text \<open>The class pcpo of pointed cpos\<close>

class pcpo = cpo +
  assumes least: "\<exists>x. \<forall>y. x \<sqsubseteq> y"
begin

definition bottom :: "'a"  (\<open>\<bottom>\<close>)
  where "bottom = (THE x. \<forall>y. x \<sqsubseteq> y)"

lemma minimal [iff]: "\<bottom> \<sqsubseteq> x"
  unfolding bottom_def
  apply (rule the1I2)
   apply (rule ex_ex1I)
    apply (rule least)
   apply (blast intro: below_antisym)
  apply simp
  done

end

text \<open>Old "UU" syntax:\<close>
abbreviation (input) "UU \<equiv> bottom"

text \<open>Simproc to rewrite \<^term>\<open>\<bottom> = x\<close> to \<^term>\<open>x = \<bottom>\<close>.\<close>
setup \<open>Reorient_Proc.add (fn \<^Const_>\<open>bottom _\<close> => true | _ => false)\<close>
simproc_setup reorient_bottom ("\<bottom> = x") = \<open>K Reorient_Proc.proc\<close>

text \<open>useful lemmas about \<^term>\<open>\<bottom>\<close>\<close>

lemma below_bottom_iff [simp]: "x \<sqsubseteq> \<bottom> \<longleftrightarrow> x = \<bottom>"
  by (simp add: po_eq_conv)

lemma eq_bottom_iff: "x = \<bottom> \<longleftrightarrow> x \<sqsubseteq> \<bottom>"
  by simp

lemma bottomI: "x \<sqsubseteq> \<bottom> \<Longrightarrow> x = \<bottom>"
  by (subst eq_bottom_iff)

lemma lub_eq_bottom_iff: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = \<bottom> \<longleftrightarrow> (\<forall>i. Y i = \<bottom>)"
  by (simp only: eq_bottom_iff lub_below_iff)


subsection \<open>Chain-finite and flat cpos\<close>

text \<open>further useful classes for HOLCF domains\<close>

class chfin = po +
  assumes chfin: "chain Y \<Longrightarrow> \<exists>n. max_in_chain n Y"
begin

subclass cpo
  apply standard
  apply (frule chfin)
  apply (blast intro: lub_finch1)
  done

lemma chfin2finch: "chain Y \<Longrightarrow> finite_chain Y"
  by (simp add: chfin finite_chain_def)

end

class flat = pcpo +
  assumes ax_flat: "x \<sqsubseteq> y \<Longrightarrow> x = \<bottom> \<or> x = y"
begin

subclass chfin
proof
  fix Y
  assume *: "chain Y"
  show "\<exists>n. max_in_chain n Y"
    apply (unfold max_in_chain_def)
    apply (cases "\<forall>i. Y i = \<bottom>")
     apply simp
    apply simp
    apply (erule exE)
    apply (rule_tac x="i" in exI)
    apply clarify
    using * apply (blast dest: chain_mono ax_flat)
    done
qed

lemma flat_below_iff: "x \<sqsubseteq> y \<longleftrightarrow> x = \<bottom> \<or> x = y"
  by (safe dest!: ax_flat)

lemma flat_eq: "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b = (a = b)"
  by (safe dest!: ax_flat)

end

subsection \<open>Discrete cpos\<close>

class discrete_cpo = below +
  assumes discrete_cpo [simp]: "x \<sqsubseteq> y \<longleftrightarrow> x = y"
begin

subclass po
  by standard simp_all

text \<open>In a discrete cpo, every chain is constant\<close>

lemma discrete_chain_const:
  assumes S: "chain S"
  shows "\<exists>x. S = (\<lambda>i. x)"
proof (intro exI ext)
  fix i :: nat
  from S le0 have "S 0 \<sqsubseteq> S i" by (rule chain_mono)
  then have "S 0 = S i" by simp
  then show "S i = S 0" by (rule sym)
qed

subclass chfin
proof
  fix S :: "nat \<Rightarrow> 'a"
  assume S: "chain S"
  then have "\<exists>x. S = (\<lambda>i. x)"
    by (rule discrete_chain_const)
  then have "max_in_chain 0 S"
    by (auto simp: max_in_chain_def)
  then show "\<exists>i. max_in_chain i S" ..
qed

end


section \<open>Continuity and monotonicity\<close>

text \<open>
   Now we change the default class! Form now on all untyped type variables are
   of default class po
\<close>

default_sort po

subsection \<open>Definitions\<close>

definition monofun :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"  \<comment> \<open>monotonicity\<close>
  where "monofun f \<longleftrightarrow> (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

definition cont :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"
  where "cont f = (\<forall>Y. chain Y \<longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i))"

lemma contI: "(\<And>Y. chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)) \<Longrightarrow> cont f"
  by (simp add: cont_def)

lemma contE: "cont f \<Longrightarrow> chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
  by (simp add: cont_def)

lemma monofunI: "(\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y) \<Longrightarrow> monofun f"
  by (simp add: monofun_def)

lemma monofunE: "monofun f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  by (simp add: monofun_def)


subsection \<open>Equivalence of alternate definition\<close>

text \<open>monotone functions map chains to chains\<close>

lemma ch2ch_monofun: "monofun f \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i))"
  apply (rule chainI)
  apply (erule monofunE)
  apply (erule chainE)
  done

text \<open>monotone functions map upper bound to upper bounds\<close>

lemma ub2ub_monofun: "monofun f \<Longrightarrow> range Y <| u \<Longrightarrow> range (\<lambda>i. f (Y i)) <| f u"
  apply (rule ub_rangeI)
  apply (erule monofunE)
  apply (erule ub_rangeD)
  done

text \<open>a lemma about binary chains\<close>

lemma binchain_cont: "cont f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
  apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
   apply (erule subst)
   apply (erule contE)
   apply (erule bin_chain)
  apply (rule_tac f=f in arg_cong)
  apply (erule is_lub_bin_chain [THEN lub_eqI])
  done

text \<open>continuity implies monotonicity\<close>

lemma cont2mono: "cont f \<Longrightarrow> monofun f"
  apply (rule monofunI)
  apply (drule (1) binchain_cont)
  apply (drule_tac i=0 in is_lub_rangeD1)
  apply simp
  done

lemmas cont2monofunE = cont2mono [THEN monofunE]

lemmas ch2ch_cont = cont2mono [THEN ch2ch_monofun]

text \<open>continuity implies preservation of lubs\<close>

lemma cont2contlubE: "cont f \<Longrightarrow> chain Y \<Longrightarrow> f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
  apply (rule lub_eqI [symmetric])
  apply (erule (1) contE)
  done

lemma contI2:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes mono: "monofun f"
  assumes below: "\<And>Y. \<lbrakk>chain Y; chain (\<lambda>i. f (Y i))\<rbrakk> \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  shows "cont f"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y"
  with mono have fY: "chain (\<lambda>i. f (Y i))"
    by (rule ch2ch_monofun)
  have "(\<Squnion>i. f (Y i)) = f (\<Squnion>i. Y i)"
    apply (rule below_antisym)
     apply (rule lub_below [OF fY])
     apply (rule monofunE [OF mono])
     apply (rule is_ub_thelub [OF Y])
    apply (rule below [OF Y fY])
    done
  with fY show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
    by (rule thelubE)
qed


subsection \<open>Collection of continuity rules\<close>

named_theorems cont2cont "continuity intro rule"


subsection \<open>Continuity of basic functions\<close>

text \<open>The identity function is continuous\<close>

lemma cont_id [simp, cont2cont]: "cont (\<lambda>x. x)"
  apply (rule contI)
  apply (erule cpo_lubI)
  done

text \<open>constant functions are continuous\<close>

lemma cont_const [simp, cont2cont]: "cont (\<lambda>x. c)"
  using is_lub_const by (rule contI)

text \<open>application of functions is continuous\<close>

lemma cont_apply:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'c::cpo" and t :: "'a \<Rightarrow> 'b"
  assumes 1: "cont (\<lambda>x. t x)"
  assumes 2: "\<And>x. cont (\<lambda>y. f x y)"
  assumes 3: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. (f x) (t x))"
proof (rule contI2 [OF monofunI])
  fix x y :: "'a"
  assume "x \<sqsubseteq> y"
  then show "f x (t x) \<sqsubseteq> f y (t y)"
    by (auto intro: cont2monofunE [OF 1]
        cont2monofunE [OF 2]
        cont2monofunE [OF 3]
        below_trans)
next
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  then show "f (\<Squnion>i. Y i) (t (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. f (Y i) (t (Y i)))"
    by (simp only: cont2contlubE [OF 1] ch2ch_cont [OF 1]
        cont2contlubE [OF 2] ch2ch_cont [OF 2]
        cont2contlubE [OF 3] ch2ch_cont [OF 3]
        diag_lub below_refl)
qed

lemma cont_compose: "cont c \<Longrightarrow> cont (\<lambda>x. f x) \<Longrightarrow> cont (\<lambda>x. c (f x))"
  by (rule cont_apply [OF _ _ cont_const])

text \<open>Least upper bounds preserve continuity\<close>

lemma cont2cont_lub [simp]:
  assumes chain: "\<And>x. chain (\<lambda>i. F i x)"
    and cont: "\<And>i. cont (\<lambda>x. F i x)"
  shows "cont (\<lambda>x. \<Squnion>i. F i x)"
  apply (rule contI2)
   apply (simp add: monofunI cont2monofunE [OF cont] lub_mono chain)
  apply (simp add: cont2contlubE [OF cont])
  apply (simp add: diag_lub ch2ch_cont [OF cont] chain)
  done

text \<open>if-then-else is continuous\<close>

lemma cont_if [simp, cont2cont]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. if b then f x else g x)"
  by (induct b) simp_all


subsection \<open>Finite chains and flat pcpos\<close>

text \<open>Monotone functions map finite chains to finite chains.\<close>

lemma monofun_finch2finch: "monofun f \<Longrightarrow> finite_chain Y \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
  by (force simp add: finite_chain_def ch2ch_monofun max_in_chain_def)

text \<open>The same holds for continuous functions.\<close>

lemma cont_finch2finch: "cont f \<Longrightarrow> finite_chain Y \<Longrightarrow> finite_chain (\<lambda>n. f (Y n))"
  by (rule cont2mono [THEN monofun_finch2finch])

text \<open>All monotone functions with chain-finite domain are continuous.\<close>

lemma chfindom_monofun2cont: "monofun f \<Longrightarrow> cont f"
  for f :: "'a::chfin \<Rightarrow> 'b::cpo"
  apply (erule contI2)
  apply (frule chfin2finch)
  apply (clarsimp simp add: finite_chain_def)
  apply (subgoal_tac "max_in_chain i (\<lambda>i. f (Y i))")
   apply (simp add: maxinch_is_thelub ch2ch_monofun)
  apply (force simp add: max_in_chain_def)
  done

text \<open>All strict functions with flat domain are continuous.\<close>

lemma flatdom_strict2mono: "f \<bottom> = \<bottom> \<Longrightarrow> monofun f"
  for f :: "'a::flat \<Rightarrow> 'b::pcpo"
  apply (rule monofunI)
  apply (drule ax_flat)
  apply auto
  done

lemma flatdom_strict2cont: "f \<bottom> = \<bottom> \<Longrightarrow> cont f"
  for f :: "'a::flat \<Rightarrow> 'b::pcpo"
  by (rule flatdom_strict2mono [THEN chfindom_monofun2cont])

text \<open>All functions with discrete domain are continuous.\<close>

lemma cont_discrete_cpo [simp, cont2cont]: "cont f"
  for f :: "'a::discrete_cpo \<Rightarrow> 'b::cpo"
  apply (rule contI)
  apply (drule discrete_chain_const, clarify)
  apply simp
  done

section \<open>Admissibility and compactness\<close>

default_sort cpo

subsection \<open>Definitions\<close>

definition adm :: "('a::cpo \<Rightarrow> bool) \<Rightarrow> bool"
  where "adm P \<longleftrightarrow> (\<forall>Y. chain Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i))"

lemma admI: "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i)\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
  unfolding adm_def by fast

lemma admD: "adm P \<Longrightarrow> chain Y \<Longrightarrow> (\<And>i. P (Y i)) \<Longrightarrow> P (\<Squnion>i. Y i)"
  unfolding adm_def by fast

lemma admD2: "adm (\<lambda>x. \<not> P x) \<Longrightarrow> chain Y \<Longrightarrow> P (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. P (Y i)"
  unfolding adm_def by fast

lemma triv_admI: "\<forall>x. P x \<Longrightarrow> adm P"
  by (rule admI) (erule spec)


subsection \<open>Admissibility on chain-finite types\<close>

text \<open>For chain-finite (easy) types every formula is admissible.\<close>

lemma adm_chfin [simp]: "adm P"
  for P :: "'a::chfin \<Rightarrow> bool"
  by (rule admI, frule chfin, auto simp add: maxinch_is_thelub)


subsection \<open>Admissibility of special formulae and propagation\<close>

lemma adm_const [simp]: "adm (\<lambda>x. t)"
  by (rule admI, simp)

lemma adm_conj [simp]: "adm (\<lambda>x. P x) \<Longrightarrow> adm (\<lambda>x. Q x) \<Longrightarrow> adm (\<lambda>x. P x \<and> Q x)"
  by (fast intro: admI elim: admD)

lemma adm_all [simp]: "(\<And>y. adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y. P x y)"
  by (fast intro: admI elim: admD)

lemma adm_ball [simp]: "(\<And>y. y \<in> A \<Longrightarrow> adm (\<lambda>x. P x y)) \<Longrightarrow> adm (\<lambda>x. \<forall>y\<in>A. P x y)"
  by (fast intro: admI elim: admD)

text \<open>Admissibility for disjunction is hard to prove. It requires 2 lemmas.\<close>

lemma adm_disj_lemma1:
  assumes adm: "adm P"
  assumes chain: "chain Y"
  assumes P: "\<forall>i. \<exists>j\<ge>i. P (Y j)"
  shows "P (\<Squnion>i. Y i)"
proof -
  define f where "f i = (LEAST j. i \<le> j \<and> P (Y j))" for i
  have chain': "chain (\<lambda>i. Y (f i))"
    unfolding f_def
    apply (rule chainI)
    apply (rule chain_mono [OF chain])
    apply (rule Least_le)
    apply (rule LeastI2_ex)
     apply (simp_all add: P)
    done
  have f1: "\<And>i. i \<le> f i" and f2: "\<And>i. P (Y (f i))"
    using LeastI_ex [OF P [rule_format]] by (simp_all add: f_def)
  have lub_eq: "(\<Squnion>i. Y i) = (\<Squnion>i. Y (f i))"
    apply (rule below_antisym)
     apply (rule lub_mono [OF chain chain'])
     apply (rule chain_mono [OF chain f1])
    apply (rule lub_range_mono [OF _ chain chain'])
    apply clarsimp
    done
  show "P (\<Squnion>i. Y i)"
    unfolding lub_eq using adm chain' f2 by (rule admD)
qed

lemma adm_disj_lemma2: "\<forall>n::nat. P n \<or> Q n \<Longrightarrow> (\<forall>i. \<exists>j\<ge>i. P j) \<or> (\<forall>i. \<exists>j\<ge>i. Q j)"
  apply (erule contrapos_pp)
  apply (clarsimp, rename_tac a b)
  apply (rule_tac x="max a b" in exI)
  apply simp
  done

lemma adm_disj [simp]: "adm (\<lambda>x. P x) \<Longrightarrow> adm (\<lambda>x. Q x) \<Longrightarrow> adm (\<lambda>x. P x \<or> Q x)"
  apply (rule admI)
  apply (erule adm_disj_lemma2 [THEN disjE])
   apply (erule (2) adm_disj_lemma1 [THEN disjI1])
  apply (erule (2) adm_disj_lemma1 [THEN disjI2])
  done

lemma adm_imp [simp]: "adm (\<lambda>x. \<not> P x) \<Longrightarrow> adm (\<lambda>x. Q x) \<Longrightarrow> adm (\<lambda>x. P x \<longrightarrow> Q x)"
  by (subst imp_conv_disj) (rule adm_disj)

lemma adm_iff [simp]: "adm (\<lambda>x. P x \<longrightarrow> Q x) \<Longrightarrow> adm (\<lambda>x. Q x \<longrightarrow> P x) \<Longrightarrow> adm (\<lambda>x. P x \<longleftrightarrow> Q x)"
  by (subst iff_conv_conj_imp) (rule adm_conj)

text \<open>admissibility and continuity\<close>

lemma adm_below [simp]: "cont (\<lambda>x. u x) \<Longrightarrow> cont (\<lambda>x. v x) \<Longrightarrow> adm (\<lambda>x. u x \<sqsubseteq> v x)"
  by (simp add: adm_def cont2contlubE lub_mono ch2ch_cont)

lemma adm_eq [simp]: "cont (\<lambda>x. u x) \<Longrightarrow> cont (\<lambda>x. v x) \<Longrightarrow> adm (\<lambda>x. u x = v x)"
  by (simp add: po_eq_conv)

lemma adm_subst: "cont (\<lambda>x. t x) \<Longrightarrow> adm P \<Longrightarrow> adm (\<lambda>x. P (t x))"
  by (simp add: adm_def cont2contlubE ch2ch_cont)

lemma adm_not_below [simp]: "cont (\<lambda>x. t x) \<Longrightarrow> adm (\<lambda>x. t x \<notsqsubseteq> u)"
  by (rule admI) (simp add: cont2contlubE ch2ch_cont lub_below_iff)


subsection \<open>Compactness\<close>

definition compact :: "'a::cpo \<Rightarrow> bool"
  where "compact k = adm (\<lambda>x. k \<notsqsubseteq> x)"

lemma compactI: "adm (\<lambda>x. k \<notsqsubseteq> x) \<Longrightarrow> compact k"
  unfolding compact_def .

lemma compactD: "compact k \<Longrightarrow> adm (\<lambda>x. k \<notsqsubseteq> x)"
  unfolding compact_def .

lemma compactI2: "(\<And>Y. \<lbrakk>chain Y; x \<sqsubseteq> (\<Squnion>i. Y i)\<rbrakk> \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i) \<Longrightarrow> compact x"
  unfolding compact_def adm_def by fast

lemma compactD2: "compact x \<Longrightarrow> chain Y \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. x \<sqsubseteq> Y i"
  unfolding compact_def adm_def by fast

lemma compact_below_lub_iff: "compact x \<Longrightarrow> chain Y \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. Y i) \<longleftrightarrow> (\<exists>i. x \<sqsubseteq> Y i)"
  by (fast intro: compactD2 elim: below_lub)

lemma compact_chfin [simp]: "compact x"
  for x :: "'a::chfin"
  by (rule compactI [OF adm_chfin])

lemma compact_imp_max_in_chain: "chain Y \<Longrightarrow> compact (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. max_in_chain i Y"
  apply (drule (1) compactD2, simp)
  apply (erule exE, rule_tac x=i in exI)
  apply (rule max_in_chainI)
  apply (rule below_antisym)
   apply (erule (1) chain_mono)
  apply (erule (1) below_trans [OF is_ub_thelub])
  done

text \<open>admissibility and compactness\<close>

lemma adm_compact_not_below [simp]:
  "compact k \<Longrightarrow> cont (\<lambda>x. t x) \<Longrightarrow> adm (\<lambda>x. k \<notsqsubseteq> t x)"
  unfolding compact_def by (rule adm_subst)

lemma adm_neq_compact [simp]: "compact k \<Longrightarrow> cont (\<lambda>x. t x) \<Longrightarrow> adm (\<lambda>x. t x \<noteq> k)"
  by (simp add: po_eq_conv)

lemma adm_compact_neq [simp]: "compact k \<Longrightarrow> cont (\<lambda>x. t x) \<Longrightarrow> adm (\<lambda>x. k \<noteq> t x)"
  by (simp add: po_eq_conv)

lemma compact_bottom [simp, intro]: "compact \<bottom>"
  by (rule compactI) simp

text \<open>Any upward-closed predicate is admissible.\<close>

lemma adm_upward:
  assumes P: "\<And>x y. \<lbrakk>P x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> P y"
  shows "adm P"
  by (rule admI, drule spec, erule P, erule is_ub_thelub)

lemmas adm_lemmas =
  adm_const adm_conj adm_all adm_ball adm_disj adm_imp adm_iff
  adm_below adm_eq adm_not_below
  adm_compact_not_below adm_compact_neq adm_neq_compact

section \<open>Class instances for the full function space\<close>

subsection \<open>Full function space is a partial order\<close>

instantiation "fun"  :: (type, below) below
begin

definition below_fun_def: "(\<sqsubseteq>) \<equiv> (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x)"

instance ..
end

instance "fun" :: (type, po) po
proof
  fix f :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> f"
    by (simp add: below_fun_def)
next
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> f" then show "f = g"
    by (simp add: below_fun_def fun_eq_iff below_antisym)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<sqsubseteq> g" and "g \<sqsubseteq> h" then show "f \<sqsubseteq> h"
    unfolding below_fun_def by (fast elim: below_trans)
qed

lemma fun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> (\<forall>x. f x \<sqsubseteq> g x)"
  by (simp add: below_fun_def)

lemma fun_belowI: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
  by (simp add: below_fun_def)

lemma fun_belowD: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
  by (simp add: below_fun_def)


subsection \<open>Full function space is chain complete\<close>

text \<open>Properties of chains of functions.\<close>

lemma fun_chain_iff: "chain S \<longleftrightarrow> (\<forall>x. chain (\<lambda>i. S i x))"
  by (auto simp: chain_def fun_below_iff)

lemma ch2ch_fun: "chain S \<Longrightarrow> chain (\<lambda>i. S i x)"
  by (simp add: chain_def below_fun_def)

lemma ch2ch_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> chain S"
  by (simp add: chain_def below_fun_def)

text \<open>Type \<^typ>\<open>'a::type \<Rightarrow> 'b::cpo\<close> is chain complete\<close>

lemma is_lub_lambda: "(\<And>x. range (\<lambda>i. Y i x) <<| f x) \<Longrightarrow> range Y <<| f"
  by (simp add: is_lub_def is_ub_def below_fun_def)

lemma is_lub_fun: "chain S \<Longrightarrow> range S <<| (\<lambda>x. \<Squnion>i. S i x)"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  apply (rule is_lub_lambda)
  apply (rule cpo_lubI)
  apply (erule ch2ch_fun)
  done

lemma lub_fun: "chain S \<Longrightarrow> (\<Squnion>i. S i) = (\<lambda>x. \<Squnion>i. S i x)"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  by (rule is_lub_fun [THEN lub_eqI])

instance "fun"  :: (type, cpo) cpo
  by intro_classes (rule exI, erule is_lub_fun)

instance "fun" :: (type, discrete_cpo) discrete_cpo
proof
  fix f g :: "'a \<Rightarrow> 'b"
  show "f \<sqsubseteq> g \<longleftrightarrow> f = g"
    by (simp add: fun_below_iff fun_eq_iff)
qed


subsection \<open>Full function space is pointed\<close>

lemma minimal_fun: "(\<lambda>x. \<bottom>) \<sqsubseteq> f"
  by (simp add: below_fun_def)

instance "fun"  :: (type, pcpo) pcpo
  by standard (fast intro: minimal_fun)

lemma inst_fun_pcpo: "\<bottom> = (\<lambda>x. \<bottom>)"
  by (rule minimal_fun [THEN bottomI, symmetric])

lemma app_strict [simp]: "\<bottom> x = \<bottom>"
  by (simp add: inst_fun_pcpo)

lemma lambda_strict: "(\<lambda>x. \<bottom>) = \<bottom>"
  by (rule bottomI, rule minimal_fun)


subsection \<open>Propagation of monotonicity and continuity\<close>

text \<open>The lub of a chain of monotone functions is monotone.\<close>

lemma adm_monofun: "adm monofun"
  by (rule admI) (simp add: lub_fun fun_chain_iff monofun_def lub_mono)

text \<open>The lub of a chain of continuous functions is continuous.\<close>

lemma adm_cont: "adm cont"
  by (rule admI) (simp add: lub_fun fun_chain_iff)

text \<open>Function application preserves monotonicity and continuity.\<close>

lemma mono2mono_fun: "monofun f \<Longrightarrow> monofun (\<lambda>x. f x y)"
  by (simp add: monofun_def fun_below_iff)

lemma cont2cont_fun: "cont f \<Longrightarrow> cont (\<lambda>x. f x y)"
  apply (rule contI2)
   apply (erule cont2mono [THEN mono2mono_fun])
  apply (simp add: cont2contlubE lub_fun ch2ch_cont)
  done

lemma cont_fun: "cont (\<lambda>f. f x)"
  using cont_id by (rule cont2cont_fun)

text \<open>
  Lambda abstraction preserves monotonicity and continuity.
  (Note \<open>(\<lambda>x. \<lambda>y. f x y) = f\<close>.)
\<close>

lemma mono2mono_lambda: "(\<And>y. monofun (\<lambda>x. f x y)) \<Longrightarrow> monofun f"
  by (simp add: monofun_def fun_below_iff)

lemma cont2cont_lambda [simp]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont f"
  by (rule contI, rule is_lub_lambda, rule contE [OF f])

text \<open>What D.A.Schmidt calls continuity of abstraction; never used here\<close>

lemma contlub_lambda: "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> (\<lambda>x. \<Squnion>i. S i x) = (\<Squnion>i. (\<lambda>x. S i x))"
  for S :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  by (simp add: lub_fun ch2ch_lambda)

section \<open>The cpo of cartesian products\<close>

default_sort cpo


subsection \<open>Unit type is a pcpo\<close>

instantiation unit :: discrete_cpo
begin

definition below_unit_def [simp]: "x \<sqsubseteq> (y::unit) \<longleftrightarrow> True"

instance
  by standard simp

end

instance unit :: pcpo
  by standard simp


subsection \<open>Product type is a partial order\<close>

instantiation prod :: (below, below) below
begin

definition below_prod_def: "(\<sqsubseteq>) \<equiv> \<lambda>p1 p2. (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance ..

end

instance prod :: (po, po) po
proof
  fix x :: "'a \<times> 'b"
  show "x \<sqsubseteq> x"
    by (simp add: below_prod_def)
next
  fix x y :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x"
  then show "x = y"
    unfolding below_prod_def prod_eq_iff
    by (fast intro: below_antisym)
next
  fix x y z :: "'a \<times> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z"
  then show "x \<sqsubseteq> z"
    unfolding below_prod_def
    by (fast intro: below_trans)
qed


subsection \<open>Monotonicity of \emph{Pair}, \emph{fst}, \emph{snd}\<close>

lemma prod_belowI: "fst p \<sqsubseteq> fst q \<Longrightarrow> snd p \<sqsubseteq> snd q \<Longrightarrow> p \<sqsubseteq> q"
  by (simp add: below_prod_def)

lemma Pair_below_iff [simp]: "(a, b) \<sqsubseteq> (c, d) \<longleftrightarrow> a \<sqsubseteq> c \<and> b \<sqsubseteq> d"
  by (simp add: below_prod_def)

text \<open>Pair \<open>(_,_)\<close>  is monotone in both arguments\<close>

lemma monofun_pair1: "monofun (\<lambda>x. (x, y))"
  by (simp add: monofun_def)

lemma monofun_pair2: "monofun (\<lambda>y. (x, y))"
  by (simp add: monofun_def)

lemma monofun_pair: "x1 \<sqsubseteq> x2 \<Longrightarrow> y1 \<sqsubseteq> y2 \<Longrightarrow> (x1, y1) \<sqsubseteq> (x2, y2)"
  by simp

lemma ch2ch_Pair [simp]: "chain X \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. (X i, Y i))"
  by (rule chainI, simp add: chainE)

text \<open>\<^term>\<open>fst\<close> and \<^term>\<open>snd\<close> are monotone\<close>

lemma fst_monofun: "x \<sqsubseteq> y \<Longrightarrow> fst x \<sqsubseteq> fst y"
  by (simp add: below_prod_def)

lemma snd_monofun: "x \<sqsubseteq> y \<Longrightarrow> snd x \<sqsubseteq> snd y"
  by (simp add: below_prod_def)

lemma monofun_fst: "monofun fst"
  by (simp add: monofun_def below_prod_def)

lemma monofun_snd: "monofun snd"
  by (simp add: monofun_def below_prod_def)

lemmas ch2ch_fst [simp] = ch2ch_monofun [OF monofun_fst]

lemmas ch2ch_snd [simp] = ch2ch_monofun [OF monofun_snd]

lemma prod_chain_cases:
  assumes chain: "chain Y"
  obtains A B
  where "chain A" and "chain B" and "Y = (\<lambda>i. (A i, B i))"
proof
  from chain show "chain (\<lambda>i. fst (Y i))"
    by (rule ch2ch_fst)
  from chain show "chain (\<lambda>i. snd (Y i))"
    by (rule ch2ch_snd)
  show "Y = (\<lambda>i. (fst (Y i), snd (Y i)))"
    by simp
qed


subsection \<open>Product type is a cpo\<close>

lemma is_lub_Pair: "range A <<| x \<Longrightarrow> range B <<| y \<Longrightarrow> range (\<lambda>i. (A i, B i)) <<| (x, y)"
  by (simp add: is_lub_def is_ub_def below_prod_def)

lemma lub_Pair: "chain A \<Longrightarrow> chain B \<Longrightarrow> (\<Squnion>i. (A i, B i)) = (\<Squnion>i. A i, \<Squnion>i. B i)"
  for A :: "nat \<Rightarrow> 'a::cpo" and B :: "nat \<Rightarrow> 'b::cpo"
  by (fast intro: lub_eqI is_lub_Pair elim: thelubE)

lemma is_lub_prod:
  fixes S :: "nat \<Rightarrow> ('a::cpo \<times> 'b::cpo)"
  assumes "chain S"
  shows "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
  using assms by (auto elim: prod_chain_cases simp: is_lub_Pair cpo_lubI)

lemma lub_prod: "chain S \<Longrightarrow> (\<Squnion>i. S i) = (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
  for S :: "nat \<Rightarrow> 'a::cpo \<times> 'b::cpo"
  by (rule is_lub_prod [THEN lub_eqI])

instance prod :: (cpo, cpo) cpo
proof
  fix S :: "nat \<Rightarrow> ('a \<times> 'b)"
  assume "chain S"
  then have "range S <<| (\<Squnion>i. fst (S i), \<Squnion>i. snd (S i))"
    by (rule is_lub_prod)
  then show "\<exists>x. range S <<| x" ..
qed

instance prod :: (discrete_cpo, discrete_cpo) discrete_cpo
proof
  fix x y :: "'a \<times> 'b"
  show "x \<sqsubseteq> y \<longleftrightarrow> x = y"
    by (simp add: below_prod_def prod_eq_iff)
qed


subsection \<open>Product type is pointed\<close>

lemma minimal_prod: "(\<bottom>, \<bottom>) \<sqsubseteq> p"
  by (simp add: below_prod_def)

instance prod :: (pcpo, pcpo) pcpo
  by intro_classes (fast intro: minimal_prod)

lemma inst_prod_pcpo: "\<bottom> = (\<bottom>, \<bottom>)"
  by (rule minimal_prod [THEN bottomI, symmetric])

lemma Pair_bottom_iff [simp]: "(x, y) = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (simp add: inst_prod_pcpo)

lemma fst_strict [simp]: "fst \<bottom> = \<bottom>"
  unfolding inst_prod_pcpo by (rule fst_conv)

lemma snd_strict [simp]: "snd \<bottom> = \<bottom>"
  unfolding inst_prod_pcpo by (rule snd_conv)

lemma Pair_strict [simp]: "(\<bottom>, \<bottom>) = \<bottom>"
  by simp

lemma split_strict [simp]: "case_prod f \<bottom> = f \<bottom> \<bottom>"
  by (simp add: split_def)


subsection \<open>Continuity of \emph{Pair}, \emph{fst}, \emph{snd}\<close>

lemma cont_pair1: "cont (\<lambda>x. (x, y))"
  apply (rule contI)
  apply (rule is_lub_Pair)
   apply (erule cpo_lubI)
  apply (rule is_lub_const)
  done

lemma cont_pair2: "cont (\<lambda>y. (x, y))"
  apply (rule contI)
  apply (rule is_lub_Pair)
   apply (rule is_lub_const)
  apply (erule cpo_lubI)
  done

lemma cont_fst: "cont fst"
  apply (rule contI)
  apply (simp add: lub_prod)
  apply (erule cpo_lubI [OF ch2ch_fst])
  done

lemma cont_snd: "cont snd"
  apply (rule contI)
  apply (simp add: lub_prod)
  apply (erule cpo_lubI [OF ch2ch_snd])
  done

lemma cont2cont_Pair [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. (f x, g x))"
  apply (rule cont_apply [OF f cont_pair1])
  apply (rule cont_apply [OF g cont_pair2])
  apply (rule cont_const)
  done

lemmas cont2cont_fst [simp, cont2cont] = cont_compose [OF cont_fst]

lemmas cont2cont_snd [simp, cont2cont] = cont_compose [OF cont_snd]

lemma cont2cont_case_prod:
  assumes f1: "\<And>a b. cont (\<lambda>x. f x a b)"
  assumes f2: "\<And>x b. cont (\<lambda>a. f x a b)"
  assumes f3: "\<And>x a. cont (\<lambda>b. f x a b)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. case g x of (a, b) \<Rightarrow> f x a b)"
  unfolding split_def
  apply (rule cont_apply [OF g])
   apply (rule cont_apply [OF cont_fst f2])
   apply (rule cont_apply [OF cont_snd f3])
   apply (rule cont_const)
  apply (rule f1)
  done

lemma prod_contI:
  assumes f1: "\<And>y. cont (\<lambda>x. f (x, y))"
  assumes f2: "\<And>x. cont (\<lambda>y. f (x, y))"
  shows "cont f"
proof -
  have "cont (\<lambda>(x, y). f (x, y))"
    by (intro cont2cont_case_prod f1 f2 cont2cont)
  then show "cont f"
    by (simp only: case_prod_eta)
qed

lemma prod_cont_iff: "cont f \<longleftrightarrow> (\<forall>y. cont (\<lambda>x. f (x, y))) \<and> (\<forall>x. cont (\<lambda>y. f (x, y)))"
  apply safe
    apply (erule cont_compose [OF _ cont_pair1])
   apply (erule cont_compose [OF _ cont_pair2])
  apply (simp only: prod_contI)
  done

lemma cont2cont_case_prod' [simp, cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (fst (snd p)) (snd (snd p)))"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. case_prod (f x) (g x))"
  using assms by (simp add: cont2cont_case_prod prod_cont_iff)

text \<open>The simple version (due to Joachim Breitner) is needed if
  either element type of the pair is not a cpo.\<close>

lemma cont2cont_split_simple [simp, cont2cont]:
  assumes "\<And>a b. cont (\<lambda>x. f x a b)"
  shows "cont (\<lambda>x. case p of (a, b) \<Rightarrow> f x a b)"
  using assms by (cases p) auto

text \<open>Admissibility of predicates on product types.\<close>

lemma adm_case_prod [simp]:
  assumes "adm (\<lambda>x. P x (fst (f x)) (snd (f x)))"
  shows "adm (\<lambda>x. case f x of (a, b) \<Rightarrow> P x a b)"
  unfolding case_prod_beta using assms .


subsection \<open>Compactness and chain-finiteness\<close>

lemma fst_below_iff: "fst x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (y, snd x)"
  for x :: "'a \<times> 'b"
  by (simp add: below_prod_def)

lemma snd_below_iff: "snd x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (fst x, y)"
  for x :: "'a \<times> 'b"
  by (simp add: below_prod_def)

lemma compact_fst: "compact x \<Longrightarrow> compact (fst x)"
  by (rule compactI) (simp add: fst_below_iff)

lemma compact_snd: "compact x \<Longrightarrow> compact (snd x)"
  by (rule compactI) (simp add: snd_below_iff)

lemma compact_Pair: "compact x \<Longrightarrow> compact y \<Longrightarrow> compact (x, y)"
  by (rule compactI) (simp add: below_prod_def)

lemma compact_Pair_iff [simp]: "compact (x, y) \<longleftrightarrow> compact x \<and> compact y"
  apply (safe intro!: compact_Pair)
   apply (drule compact_fst, simp)
  apply (drule compact_snd, simp)
  done

instance prod :: (chfin, chfin) chfin
  apply intro_classes
  apply (erule compact_imp_max_in_chain)
  apply (case_tac "\<Squnion>i. Y i", simp)
  done

section \<open>Discrete cpo types\<close>

datatype 'a discr = Discr "'a :: type"

subsection \<open>Discrete cpo class instance\<close>

instantiation discr :: (type) discrete_cpo
begin

definition "((\<sqsubseteq>) :: 'a discr \<Rightarrow> 'a discr \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_discr_def)

end


subsection \<open>\emph{undiscr}\<close>

definition undiscr :: "('a::type)discr \<Rightarrow> 'a"
  where "undiscr x = (case x of Discr y \<Rightarrow> y)"

lemma undiscr_Discr [simp]: "undiscr (Discr x) = x"
  by (simp add: undiscr_def)

lemma Discr_undiscr [simp]: "Discr (undiscr y) = y"
  by (induct y) simp

end

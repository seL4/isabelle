(*  Title:      HOL/HOLCF/Porder.thy
    Author:     Franz Regensburger and Brian Huffman
*)

section \<open>Partial orders\<close>

theory Porder
  imports Main
begin

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

end

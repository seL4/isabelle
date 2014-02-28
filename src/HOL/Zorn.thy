(*  Title:      HOL/Zorn.thy
    Author:     Jacques D. Fleuriot
    Author:     Tobias Nipkow, TUM
    Author:     Christian Sternagel, JAIST

Zorn's Lemma (ported from Larry Paulson's Zorn.thy in ZF).
The well-ordering theorem.
*)

header {* Zorn's Lemma *}

theory Zorn
imports Order_Relation Hilbert_Choice
begin

subsection {* Zorn's Lemma for the Subset Relation *}

subsubsection {* Results that do not require an order *}

text {*Let @{text P} be a binary predicate on the set @{text A}.*}
locale pred_on =
  fixes A :: "'a set"
    and P :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
begin

abbreviation Peq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<equiv> P\<^sup>=\<^sup>= x y"

text {*A chain is a totally ordered subset of @{term A}.*}
definition chain :: "'a set \<Rightarrow> bool" where
  "chain C \<longleftrightarrow> C \<subseteq> A \<and> (\<forall>x\<in>C. \<forall>y\<in>C. x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

text {*We call a chain that is a proper superset of some set @{term X},
but not necessarily a chain itself, a superchain of @{term X}.*}
abbreviation superchain :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "<c" 50) where
  "X <c C \<equiv> chain C \<and> X \<subset> C"

text {*A maximal chain is a chain that does not have a superchain.*}
definition maxchain :: "'a set \<Rightarrow> bool" where
  "maxchain C \<longleftrightarrow> chain C \<and> \<not> (\<exists>S. C <c S)"

text {*We define the successor of a set to be an arbitrary
superchain, if such exists, or the set itself, otherwise.*}
definition suc :: "'a set \<Rightarrow> 'a set" where
  "suc C = (if \<not> chain C \<or> maxchain C then C else (SOME D. C <c D))"

lemma chainI [Pure.intro?]:
  "\<lbrakk>C \<subseteq> A; \<And>x y. \<lbrakk>x \<in> C; y \<in> C\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> chain C"
  unfolding chain_def by blast

lemma chain_total:
  "chain C \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  by (simp add: chain_def)

lemma not_chain_suc [simp]: "\<not> chain X \<Longrightarrow> suc X = X"
  by (simp add: suc_def)

lemma maxchain_suc [simp]: "maxchain X \<Longrightarrow> suc X = X"
  by (simp add: suc_def)

lemma suc_subset: "X \<subseteq> suc X"
  by (auto simp: suc_def maxchain_def intro: someI2)

lemma chain_empty [simp]: "chain {}"
  by (auto simp: chain_def)

lemma not_maxchain_Some:
  "chain C \<Longrightarrow> \<not> maxchain C \<Longrightarrow> C <c (SOME D. C <c D)"
  by (rule someI_ex) (auto simp: maxchain_def)

lemma suc_not_equals:
  "chain C \<Longrightarrow> \<not> maxchain C \<Longrightarrow> suc C \<noteq> C"
  using not_maxchain_Some by (auto simp: suc_def)

lemma subset_suc:
  assumes "X \<subseteq> Y" shows "X \<subseteq> suc Y"
  using assms by (rule subset_trans) (rule suc_subset)

text {*We build a set @{term \<C>} that is closed under applications
of @{term suc} and contains the union of all its subsets.*}
inductive_set suc_Union_closed ("\<C>") where
  suc: "X \<in> \<C> \<Longrightarrow> suc X \<in> \<C>" |
  Union [unfolded Pow_iff]: "X \<in> Pow \<C> \<Longrightarrow> \<Union>X \<in> \<C>"

text {*Since the empty set as well as the set itself is a subset of
every set, @{term \<C>} contains at least @{term "{} \<in> \<C>"} and
@{term "\<Union>\<C> \<in> \<C>"}.*}
lemma
  suc_Union_closed_empty: "{} \<in> \<C>" and
  suc_Union_closed_Union: "\<Union>\<C> \<in> \<C>"
  using Union [of "{}"] and Union [of "\<C>"] by simp+
text {*Thus closure under @{term suc} will hit a maximal chain
eventually, as is shown below.*}

lemma suc_Union_closed_induct [consumes 1, case_names suc Union,
  induct pred: suc_Union_closed]:
  assumes "X \<in> \<C>"
    and "\<And>X. \<lbrakk>X \<in> \<C>; Q X\<rbrakk> \<Longrightarrow> Q (suc X)"
    and "\<And>X. \<lbrakk>X \<subseteq> \<C>; \<forall>x\<in>X. Q x\<rbrakk> \<Longrightarrow> Q (\<Union>X)"
  shows "Q X"
  using assms by (induct) blast+

lemma suc_Union_closed_cases [consumes 1, case_names suc Union,
  cases pred: suc_Union_closed]:
  assumes "X \<in> \<C>"
    and "\<And>Y. \<lbrakk>X = suc Y; Y \<in> \<C>\<rbrakk> \<Longrightarrow> Q"
    and "\<And>Y. \<lbrakk>X = \<Union>Y; Y \<subseteq> \<C>\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (cases) simp+

text {*On chains, @{term suc} yields a chain.*}
lemma chain_suc:
  assumes "chain X" shows "chain (suc X)"
  using assms
  by (cases "\<not> chain X \<or> maxchain X")
     (force simp: suc_def dest: not_maxchain_Some)+

lemma chain_sucD:
  assumes "chain X" shows "suc X \<subseteq> A \<and> chain (suc X)"
proof -
  from `chain X` have *: "chain (suc X)" by (rule chain_suc)
  then have "suc X \<subseteq> A" unfolding chain_def by blast
  with * show ?thesis by blast
qed

lemma suc_Union_closed_total':
  assumes "X \<in> \<C>" and "Y \<in> \<C>"
    and *: "\<And>Z. Z \<in> \<C> \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow> Z = Y \<or> suc Z \<subseteq> Y"
  shows "X \<subseteq> Y \<or> suc Y \<subseteq> X"
  using `X \<in> \<C>`
proof (induct)
  case (suc X)
  with * show ?case by (blast del: subsetI intro: subset_suc)
qed blast

lemma suc_Union_closed_subsetD:
  assumes "Y \<subseteq> X" and "X \<in> \<C>" and "Y \<in> \<C>"
  shows "X = Y \<or> suc Y \<subseteq> X"
  using assms(2-, 1)
proof (induct arbitrary: Y)
  case (suc X)
  note * = `\<And>Y. \<lbrakk>Y \<in> \<C>; Y \<subseteq> X\<rbrakk> \<Longrightarrow> X = Y \<or> suc Y \<subseteq> X`
  with suc_Union_closed_total' [OF `Y \<in> \<C>` `X \<in> \<C>`]
    have "Y \<subseteq> X \<or> suc X \<subseteq> Y" by blast
  then show ?case
  proof
    assume "Y \<subseteq> X"
    with * and `Y \<in> \<C>` have "X = Y \<or> suc Y \<subseteq> X" by blast
    then show ?thesis
    proof
      assume "X = Y" then show ?thesis by simp
    next
      assume "suc Y \<subseteq> X"
      then have "suc Y \<subseteq> suc X" by (rule subset_suc)
      then show ?thesis by simp
    qed
  next
    assume "suc X \<subseteq> Y"
    with `Y \<subseteq> suc X` show ?thesis by blast
  qed
next
  case (Union X)
  show ?case
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with `Y \<subseteq> \<Union>X` obtain x y z
    where "\<not> suc Y \<subseteq> \<Union>X"
      and "x \<in> X" and "y \<in> x" and "y \<notin> Y"
      and "z \<in> suc Y" and "\<forall>x\<in>X. z \<notin> x" by blast
    with `X \<subseteq> \<C>` have "x \<in> \<C>" by blast
    from Union and `x \<in> X`
      have *: "\<And>y. \<lbrakk>y \<in> \<C>; y \<subseteq> x\<rbrakk> \<Longrightarrow> x = y \<or> suc y \<subseteq> x" by blast
    with suc_Union_closed_total' [OF `Y \<in> \<C>` `x \<in> \<C>`]
      have "Y \<subseteq> x \<or> suc x \<subseteq> Y" by blast
    then show False
    proof
      assume "Y \<subseteq> x"
      with * [OF `Y \<in> \<C>`] have "x = Y \<or> suc Y \<subseteq> x" by blast
      then show False
      proof
        assume "x = Y" with `y \<in> x` and `y \<notin> Y` show False by blast
      next
        assume "suc Y \<subseteq> x"
        with `x \<in> X` have "suc Y \<subseteq> \<Union>X" by blast
        with `\<not> suc Y \<subseteq> \<Union>X` show False by contradiction
      qed
    next
      assume "suc x \<subseteq> Y"
      moreover from suc_subset and `y \<in> x` have "y \<in> suc x" by blast
      ultimately show False using `y \<notin> Y` by blast
    qed
  qed
qed

text {*The elements of @{term \<C>} are totally ordered by the subset relation.*}
lemma suc_Union_closed_total:
  assumes "X \<in> \<C>" and "Y \<in> \<C>"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X"
proof (cases "\<forall>Z\<in>\<C>. Z \<subseteq> Y \<longrightarrow> Z = Y \<or> suc Z \<subseteq> Y")
  case True
  with suc_Union_closed_total' [OF assms]
    have "X \<subseteq> Y \<or> suc Y \<subseteq> X" by blast
  then show ?thesis using suc_subset [of Y] by blast
next
  case False
  then obtain Z
    where "Z \<in> \<C>" and "Z \<subseteq> Y" and "Z \<noteq> Y" and "\<not> suc Z \<subseteq> Y" by blast
  with suc_Union_closed_subsetD and `Y \<in> \<C>` show ?thesis by blast
qed

text {*Once we hit a fixed point w.r.t. @{term suc}, all other elements
of @{term \<C>} are subsets of this fixed point.*}
lemma suc_Union_closed_suc:
  assumes "X \<in> \<C>" and "Y \<in> \<C>" and "suc Y = Y"
  shows "X \<subseteq> Y"
using `X \<in> \<C>`
proof (induct)
  case (suc X)
  with `Y \<in> \<C>` and suc_Union_closed_subsetD
    have "X = Y \<or> suc X \<subseteq> Y" by blast
  then show ?case by (auto simp: `suc Y = Y`)
qed blast

lemma eq_suc_Union:
  assumes "X \<in> \<C>"
  shows "suc X = X \<longleftrightarrow> X = \<Union>\<C>"
proof
  assume "suc X = X"
  with suc_Union_closed_suc [OF suc_Union_closed_Union `X \<in> \<C>`]
    have "\<Union>\<C> \<subseteq> X" .
  with `X \<in> \<C>` show "X = \<Union>\<C>" by blast
next
  from `X \<in> \<C>` have "suc X \<in> \<C>" by (rule suc)
  then have "suc X \<subseteq> \<Union>\<C>" by blast
  moreover assume "X = \<Union>\<C>"
  ultimately have "suc X \<subseteq> X" by simp
  moreover have "X \<subseteq> suc X" by (rule suc_subset)
  ultimately show "suc X = X" ..
qed

lemma suc_in_carrier:
  assumes "X \<subseteq> A"
  shows "suc X \<subseteq> A"
  using assms
  by (cases "\<not> chain X \<or> maxchain X")
     (auto dest: chain_sucD)

lemma suc_Union_closed_in_carrier:
  assumes "X \<in> \<C>"
  shows "X \<subseteq> A"
  using assms
  by (induct) (auto dest: suc_in_carrier)

text {*All elements of @{term \<C>} are chains.*}
lemma suc_Union_closed_chain:
  assumes "X \<in> \<C>"
  shows "chain X"
using assms
proof (induct)
  case (suc X) then show ?case using not_maxchain_Some by (simp add: suc_def)
next
  case (Union X)
  then have "\<Union>X \<subseteq> A" by (auto dest: suc_Union_closed_in_carrier)
  moreover have "\<forall>x\<in>\<Union>X. \<forall>y\<in>\<Union>X. x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  proof (intro ballI)
    fix x y
    assume "x \<in> \<Union>X" and "y \<in> \<Union>X"
    then obtain u v where "x \<in> u" and "u \<in> X" and "y \<in> v" and "v \<in> X" by blast
    with Union have "u \<in> \<C>" and "v \<in> \<C>" and "chain u" and "chain v" by blast+
    with suc_Union_closed_total have "u \<subseteq> v \<or> v \<subseteq> u" by blast
    then show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
    proof
      assume "u \<subseteq> v"
      from `chain v` show ?thesis
      proof (rule chain_total)
        show "y \<in> v" by fact
        show "x \<in> v" using `u \<subseteq> v` and `x \<in> u` by blast
      qed
    next
      assume "v \<subseteq> u"
      from `chain u` show ?thesis
      proof (rule chain_total)
        show "x \<in> u" by fact
        show "y \<in> u" using `v \<subseteq> u` and `y \<in> v` by blast
      qed
    qed
  qed
  ultimately show ?case unfolding chain_def ..
qed

subsubsection {* Hausdorff's Maximum Principle *}

text {*There exists a maximal totally ordered subset of @{term A}. (Note that we do not
require @{term A} to be partially ordered.)*}

theorem Hausdorff: "\<exists>C. maxchain C"
proof -
  let ?M = "\<Union>\<C>"
  have "maxchain ?M"
  proof (rule ccontr)
    assume "\<not> maxchain ?M"
    then have "suc ?M \<noteq> ?M"
      using suc_not_equals and
      suc_Union_closed_chain [OF suc_Union_closed_Union] by simp
    moreover have "suc ?M = ?M"
      using eq_suc_Union [OF suc_Union_closed_Union] by simp
    ultimately show False by contradiction
  qed
  then show ?thesis by blast
qed

text {*Make notation @{term \<C>} available again.*}
no_notation suc_Union_closed ("\<C>")

lemma chain_extend:
  "chain C \<Longrightarrow> z \<in> A \<Longrightarrow> \<forall>x\<in>C. x \<sqsubseteq> z \<Longrightarrow> chain ({z} \<union> C)"
  unfolding chain_def by blast

lemma maxchain_imp_chain:
  "maxchain C \<Longrightarrow> chain C"
  by (simp add: maxchain_def)

end

text {*Hide constant @{const pred_on.suc_Union_closed}, which was just needed
for the proof of Hausforff's maximum principle.*}
hide_const pred_on.suc_Union_closed

lemma chain_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q x y"
    and "pred_on.chain A P C"
  shows "pred_on.chain A Q C"
  using assms unfolding pred_on.chain_def by blast

subsubsection {* Results for the proper subset relation *}

interpretation subset: pred_on "A" "op \<subset>" for A .

lemma subset_maxchain_max:
  assumes "subset.maxchain A C" and "X \<in> A" and "\<Union>C \<subseteq> X"
  shows "\<Union>C = X"
proof (rule ccontr)
  let ?C = "{X} \<union> C"
  from `subset.maxchain A C` have "subset.chain A C"
    and *: "\<And>S. subset.chain A S \<Longrightarrow> \<not> C \<subset> S"
    by (auto simp: subset.maxchain_def)
  moreover have "\<forall>x\<in>C. x \<subseteq> X" using `\<Union>C \<subseteq> X` by auto
  ultimately have "subset.chain A ?C"
    using subset.chain_extend [of A C X] and `X \<in> A` by auto
  moreover assume **: "\<Union>C \<noteq> X"
  moreover from ** have "C \<subset> ?C" using `\<Union>C \<subseteq> X` by auto
  ultimately show False using * by blast
qed

subsubsection {* Zorn's lemma *}

text {*If every chain has an upper bound, then there is a maximal set.*}
lemma subset_Zorn:
  assumes "\<And>C. subset.chain A C \<Longrightarrow> \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U"
  shows "\<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
proof -
  from subset.Hausdorff [of A] obtain M where "subset.maxchain A M" ..
  then have "subset.chain A M" by (rule subset.maxchain_imp_chain)
  with assms obtain Y where "Y \<in> A" and "\<forall>X\<in>M. X \<subseteq> Y" by blast
  moreover have "\<forall>X\<in>A. Y \<subseteq> X \<longrightarrow> Y = X"
  proof (intro ballI impI)
    fix X
    assume "X \<in> A" and "Y \<subseteq> X"
    show "Y = X"
    proof (rule ccontr)
      assume "Y \<noteq> X"
      with `Y \<subseteq> X` have "\<not> X \<subseteq> Y" by blast
      from subset.chain_extend [OF `subset.chain A M` `X \<in> A`] and `\<forall>X\<in>M. X \<subseteq> Y`
        have "subset.chain A ({X} \<union> M)" using `Y \<subseteq> X` by auto
      moreover have "M \<subset> {X} \<union> M" using `\<forall>X\<in>M. X \<subseteq> Y` and `\<not> X \<subseteq> Y` by auto
      ultimately show False
        using `subset.maxchain A M` by (auto simp: subset.maxchain_def)
    qed
  qed
  ultimately show ?thesis by blast
qed

text{*Alternative version of Zorn's lemma for the subset relation.*}
lemma subset_Zorn':
  assumes "\<And>C. subset.chain A C \<Longrightarrow> \<Union>C \<in> A"
  shows "\<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
proof -
  from subset.Hausdorff [of A] obtain M where "subset.maxchain A M" ..
  then have "subset.chain A M" by (rule subset.maxchain_imp_chain)
  with assms have "\<Union>M \<in> A" .
  moreover have "\<forall>Z\<in>A. \<Union>M \<subseteq> Z \<longrightarrow> \<Union>M = Z"
  proof (intro ballI impI)
    fix Z
    assume "Z \<in> A" and "\<Union>M \<subseteq> Z"
    with subset_maxchain_max [OF `subset.maxchain A M`]
      show "\<Union>M = Z" .
  qed
  ultimately show ?thesis by blast
qed


subsection {* Zorn's Lemma for Partial Orders *}

text {*Relate old to new definitions.*}

(* Define globally? In Set.thy? *)
definition chain_subset :: "'a set set \<Rightarrow> bool" ("chain\<^sub>\<subseteq>") where
  "chain\<^sub>\<subseteq> C \<longleftrightarrow> (\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B \<or> B \<subseteq> A)"

definition chains :: "'a set set \<Rightarrow> 'a set set set" where
  "chains A = {C. C \<subseteq> A \<and> chain\<^sub>\<subseteq> C}"

(* Define globally? In Relation.thy? *)
definition Chains :: "('a \<times> 'a) set \<Rightarrow> 'a set set" where
  "Chains r = {C. \<forall>a\<in>C. \<forall>b\<in>C. (a, b) \<in> r \<or> (b, a) \<in> r}"

lemma chains_extend:
  "[| c \<in> chains S; z \<in> S; \<forall>x \<in> c. x \<subseteq> (z:: 'a set) |] ==> {z} Un c \<in> chains S"
  by (unfold chains_def chain_subset_def) blast

lemma mono_Chains: "r \<subseteq> s \<Longrightarrow> Chains r \<subseteq> Chains s"
  unfolding Chains_def by blast

lemma chain_subset_alt_def: "chain\<^sub>\<subseteq> C = subset.chain UNIV C"
  unfolding chain_subset_def subset.chain_def by fast

lemma chains_alt_def: "chains A = {C. subset.chain A C}"
  by (simp add: chains_def chain_subset_alt_def subset.chain_def)

lemma Chains_subset:
  "Chains r \<subseteq> {C. pred_on.chain UNIV (\<lambda>x y. (x, y) \<in> r) C}"
  by (force simp add: Chains_def pred_on.chain_def)

lemma Chains_subset':
  assumes "refl r"
  shows "{C. pred_on.chain UNIV (\<lambda>x y. (x, y) \<in> r) C} \<subseteq> Chains r"
  using assms
  by (auto simp add: Chains_def pred_on.chain_def refl_on_def)

lemma Chains_alt_def:
  assumes "refl r"
  shows "Chains r = {C. pred_on.chain UNIV (\<lambda>x y. (x, y) \<in> r) C}"
  using assms Chains_subset Chains_subset' by blast

lemma Zorn_Lemma:
  "\<forall>C\<in>chains A. \<Union>C \<in> A \<Longrightarrow> \<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
  using subset_Zorn' [of A] by (force simp: chains_alt_def)

lemma Zorn_Lemma2:
  "\<forall>C\<in>chains A. \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U \<Longrightarrow> \<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
  using subset_Zorn [of A] by (auto simp: chains_alt_def)

text{*Various other lemmas*}

lemma chainsD: "[| c \<in> chains S; x \<in> c; y \<in> c |] ==> x \<subseteq> y | y \<subseteq> x"
by (unfold chains_def chain_subset_def) blast

lemma chainsD2: "!!(c :: 'a set set). c \<in> chains S ==> c \<subseteq> S"
by (unfold chains_def) blast

lemma Zorns_po_lemma:
  assumes po: "Partial_order r"
    and u: "\<forall>C\<in>Chains r. \<exists>u\<in>Field r. \<forall>a\<in>C. (a, u) \<in> r"
  shows "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
proof -
  have "Preorder r" using po by (simp add: partial_order_on_def)
--{* Mirror r in the set of subsets below (wrt r) elements of A*}
  let ?B = "%x. r\<inverse> `` {x}" let ?S = "?B ` Field r"
  {
    fix C assume 1: "C \<subseteq> ?S" and 2: "\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B \<or> B \<subseteq> A"
    let ?A = "{x\<in>Field r. \<exists>M\<in>C. M = ?B x}"
    have "C = ?B ` ?A" using 1 by (auto simp: image_def)
    have "?A \<in> Chains r"
    proof (simp add: Chains_def, intro allI impI, elim conjE)
      fix a b
      assume "a \<in> Field r" and "?B a \<in> C" and "b \<in> Field r" and "?B b \<in> C"
      hence "?B a \<subseteq> ?B b \<or> ?B b \<subseteq> ?B a" using 2 by auto
      thus "(a, b) \<in> r \<or> (b, a) \<in> r"
        using `Preorder r` and `a \<in> Field r` and `b \<in> Field r`
        by (simp add:subset_Image1_Image1_iff)
    qed
    then obtain u where uA: "u \<in> Field r" "\<forall>a\<in>?A. (a, u) \<in> r" using u by auto
    have "\<forall>A\<in>C. A \<subseteq> r\<inverse> `` {u}" (is "?P u")
    proof auto
      fix a B assume aB: "B \<in> C" "a \<in> B"
      with 1 obtain x where "x \<in> Field r" and "B = r\<inverse> `` {x}" by auto
      thus "(a, u) \<in> r" using uA and aB and `Preorder r`
        unfolding preorder_on_def refl_on_def by simp (fast dest: transD)
    qed
    then have "\<exists>u\<in>Field r. ?P u" using `u \<in> Field r` by blast
  }
  then have "\<forall>C\<in>chains ?S. \<exists>U\<in>?S. \<forall>A\<in>C. A \<subseteq> U"
    by (auto simp: chains_def chain_subset_def)
  from Zorn_Lemma2 [OF this]
  obtain m B where "m \<in> Field r" and "B = r\<inverse> `` {m}"
    and "\<forall>x\<in>Field r. B \<subseteq> r\<inverse> `` {x} \<longrightarrow> r\<inverse> `` {x} = B"
    by auto
  hence "\<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
    using po and `Preorder r` and `m \<in> Field r`
    by (auto simp: subset_Image1_Image1_iff Partial_order_eq_Image1_Image1_iff)
  thus ?thesis using `m \<in> Field r` by blast
qed


subsection {* The Well Ordering Theorem *}

(* The initial segment of a relation appears generally useful.
   Move to Relation.thy?
   Definition correct/most general?
   Naming?
*)
definition init_seg_of :: "(('a \<times> 'a) set \<times> ('a \<times> 'a) set) set" where
  "init_seg_of = {(r, s). r \<subseteq> s \<and> (\<forall>a b c. (a, b) \<in> s \<and> (b, c) \<in> r \<longrightarrow> (a, b) \<in> r)}"

abbreviation
  initialSegmentOf :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" (infix "initial'_segment'_of" 55)
where
  "r initial_segment_of s \<equiv> (r, s) \<in> init_seg_of"

lemma refl_on_init_seg_of [simp]: "r initial_segment_of r"
  by (simp add: init_seg_of_def)

lemma trans_init_seg_of:
  "r initial_segment_of s \<Longrightarrow> s initial_segment_of t \<Longrightarrow> r initial_segment_of t"
  by (simp (no_asm_use) add: init_seg_of_def) blast

lemma antisym_init_seg_of:
  "r initial_segment_of s \<Longrightarrow> s initial_segment_of r \<Longrightarrow> r = s"
  unfolding init_seg_of_def by safe

lemma Chains_init_seg_of_Union:
  "R \<in> Chains init_seg_of \<Longrightarrow> r\<in>R \<Longrightarrow> r initial_segment_of \<Union>R"
  by (auto simp: init_seg_of_def Ball_def Chains_def) blast

lemma chain_subset_trans_Union:
  assumes "chain\<^sub>\<subseteq> R" "\<forall>r\<in>R. trans r"
  shows "trans (\<Union>R)"
proof (intro transI, elim UnionE)
  fix  S1 S2 :: "'a rel" and x y z :: 'a
  assume "S1 \<in> R" "S2 \<in> R"
  with assms(1) have "S1 \<subseteq> S2 \<or> S2 \<subseteq> S1" unfolding chain_subset_def by blast
  moreover assume "(x, y) \<in> S1" "(y, z) \<in> S2"
  ultimately have "((x, y) \<in> S1 \<and> (y, z) \<in> S1) \<or> ((x, y) \<in> S2 \<and> (y, z) \<in> S2)" by blast
  with `S1 \<in> R` `S2 \<in> R` assms(2) show "(x, z) \<in> \<Union>R" by (auto elim: transE)
qed

lemma chain_subset_antisym_Union:
  assumes "chain\<^sub>\<subseteq> R" "\<forall>r\<in>R. antisym r"
  shows "antisym (\<Union>R)"
proof (intro antisymI, elim UnionE)
  fix  S1 S2 :: "'a rel" and x y :: 'a
  assume "S1 \<in> R" "S2 \<in> R"
  with assms(1) have "S1 \<subseteq> S2 \<or> S2 \<subseteq> S1" unfolding chain_subset_def by blast
  moreover assume "(x, y) \<in> S1" "(y, x) \<in> S2"
  ultimately have "((x, y) \<in> S1 \<and> (y, x) \<in> S1) \<or> ((x, y) \<in> S2 \<and> (y, x) \<in> S2)" by blast
  with `S1 \<in> R` `S2 \<in> R` assms(2) show "x = y" unfolding antisym_def by auto
qed

lemma chain_subset_Total_Union:
  assumes "chain\<^sub>\<subseteq> R" and "\<forall>r\<in>R. Total r"
  shows "Total (\<Union>R)"
proof (simp add: total_on_def Ball_def, auto del: disjCI)
  fix r s a b assume A: "r \<in> R" "s \<in> R" "a \<in> Field r" "b \<in> Field s" "a \<noteq> b"
  from `chain\<^sub>\<subseteq> R` and `r \<in> R` and `s \<in> R` have "r \<subseteq> s \<or> s \<subseteq> r"
    by (auto simp add: chain_subset_def)
  thus "(\<exists>r\<in>R. (a, b) \<in> r) \<or> (\<exists>r\<in>R. (b, a) \<in> r)"
  proof
    assume "r \<subseteq> s" hence "(a, b) \<in> s \<or> (b, a) \<in> s" using assms(2) A mono_Field[of r s]
      by (auto simp add: total_on_def)
    thus ?thesis using `s \<in> R` by blast
  next
    assume "s \<subseteq> r" hence "(a, b) \<in> r \<or> (b, a) \<in> r" using assms(2) A mono_Field[of s r]
      by (fastforce simp add: total_on_def)
    thus ?thesis using `r \<in> R` by blast
  qed
qed

lemma wf_Union_wf_init_segs:
  assumes "R \<in> Chains init_seg_of" and "\<forall>r\<in>R. wf r"
  shows "wf (\<Union>R)"
proof(simp add: wf_iff_no_infinite_down_chain, rule ccontr, auto)
  fix f assume 1: "\<forall>i. \<exists>r\<in>R. (f (Suc i), f i) \<in> r"
  then obtain r where "r \<in> R" and "(f (Suc 0), f 0) \<in> r" by auto
  { fix i have "(f (Suc i), f i) \<in> r"
    proof (induct i)
      case 0 show ?case by fact
    next
      case (Suc i)
      then obtain s where s: "s \<in> R" "(f (Suc (Suc i)), f(Suc i)) \<in> s"
        using 1 by auto
      then have "s initial_segment_of r \<or> r initial_segment_of s"
        using assms(1) `r \<in> R` by (simp add: Chains_def)
      with Suc s show ?case by (simp add: init_seg_of_def) blast
    qed
  }
  thus False using assms(2) and `r \<in> R`
    by (simp add: wf_iff_no_infinite_down_chain) blast
qed

lemma initial_segment_of_Diff:
  "p initial_segment_of q \<Longrightarrow> p - s initial_segment_of q - s"
  unfolding init_seg_of_def by blast

lemma Chains_inits_DiffI:
  "R \<in> Chains init_seg_of \<Longrightarrow> {r - s |r. r \<in> R} \<in> Chains init_seg_of"
  unfolding Chains_def by (blast intro: initial_segment_of_Diff)

theorem well_ordering: "\<exists>r::'a rel. Well_order r \<and> Field r = UNIV"
proof -
-- {*The initial segment relation on well-orders: *}
  let ?WO = "{r::'a rel. Well_order r}"
  def I \<equiv> "init_seg_of \<inter> ?WO \<times> ?WO"
  have I_init: "I \<subseteq> init_seg_of" by (auto simp: I_def)
  hence subch: "\<And>R. R \<in> Chains I \<Longrightarrow> chain\<^sub>\<subseteq> R"
    unfolding init_seg_of_def chain_subset_def Chains_def by blast
  have Chains_wo: "\<And>R r. R \<in> Chains I \<Longrightarrow> r \<in> R \<Longrightarrow> Well_order r"
    by (simp add: Chains_def I_def) blast
  have FI: "Field I = ?WO" by (auto simp add: I_def init_seg_of_def Field_def)
  hence 0: "Partial_order I"
    by (auto simp: partial_order_on_def preorder_on_def antisym_def antisym_init_seg_of refl_on_def
      trans_def I_def elim!: trans_init_seg_of)
-- {*I-chains have upper bounds in ?WO wrt I: their Union*}
  { fix R assume "R \<in> Chains I"
    hence Ris: "R \<in> Chains init_seg_of" using mono_Chains [OF I_init] by blast
    have subch: "chain\<^sub>\<subseteq> R" using `R : Chains I` I_init
      by (auto simp: init_seg_of_def chain_subset_def Chains_def)
    have "\<forall>r\<in>R. Refl r" and "\<forall>r\<in>R. trans r" and "\<forall>r\<in>R. antisym r"
      and "\<forall>r\<in>R. Total r" and "\<forall>r\<in>R. wf (r - Id)"
      using Chains_wo [OF `R \<in> Chains I`] by (simp_all add: order_on_defs)
    have "Refl (\<Union>R)" using `\<forall>r\<in>R. Refl r` unfolding refl_on_def by fastforce
    moreover have "trans (\<Union>R)"
      by (rule chain_subset_trans_Union [OF subch `\<forall>r\<in>R. trans r`])
    moreover have "antisym (\<Union>R)"
      by (rule chain_subset_antisym_Union [OF subch `\<forall>r\<in>R. antisym r`])
    moreover have "Total (\<Union>R)"
      by (rule chain_subset_Total_Union [OF subch `\<forall>r\<in>R. Total r`])
    moreover have "wf ((\<Union>R) - Id)"
    proof -
      have "(\<Union>R) - Id = \<Union>{r - Id | r. r \<in> R}" by blast
      with `\<forall>r\<in>R. wf (r - Id)` and wf_Union_wf_init_segs [OF Chains_inits_DiffI [OF Ris]]
      show ?thesis by fastforce
    qed
    ultimately have "Well_order (\<Union>R)" by(simp add:order_on_defs)
    moreover have "\<forall>r \<in> R. r initial_segment_of \<Union>R" using Ris
      by(simp add: Chains_init_seg_of_Union)
    ultimately have "\<Union>R \<in> ?WO \<and> (\<forall>r\<in>R. (r, \<Union>R) \<in> I)"
      using mono_Chains [OF I_init] Chains_wo[of R] and `R \<in> Chains I`
      unfolding I_def by blast
  }
  hence 1: "\<forall>R \<in> Chains I. \<exists>u\<in>Field I. \<forall>r\<in>R. (r, u) \<in> I" by (subst FI) blast
--{*Zorn's Lemma yields a maximal well-order m:*}
  then obtain m::"'a rel" where "Well_order m" and
    max: "\<forall>r. Well_order r \<and> (m, r) \<in> I \<longrightarrow> r = m"
    using Zorns_po_lemma[OF 0 1] unfolding FI by fastforce
--{*Now show by contradiction that m covers the whole type:*}
  { fix x::'a assume "x \<notin> Field m"
--{*We assume that x is not covered and extend m at the top with x*}
    have "m \<noteq> {}"
    proof
      assume "m = {}"
      moreover have "Well_order {(x, x)}"
        by (simp add: order_on_defs refl_on_def trans_def antisym_def total_on_def Field_def)
      ultimately show False using max
        by (auto simp: I_def init_seg_of_def simp del: Field_insert)
    qed
    hence "Field m \<noteq> {}" by(auto simp:Field_def)
    moreover have "wf (m - Id)" using `Well_order m`
      by (simp add: well_order_on_def)
--{*The extension of m by x:*}
    let ?s = "{(a, x) | a. a \<in> Field m}"
    let ?m = "insert (x, x) m \<union> ?s"
    have Fm: "Field ?m = insert x (Field m)"
      by (auto simp: Field_def)
    have "Refl m" and "trans m" and "antisym m" and "Total m" and "wf (m - Id)"
      using `Well_order m` by (simp_all add: order_on_defs)
--{*We show that the extension is a well-order*}
    have "Refl ?m" using `Refl m` Fm unfolding refl_on_def by blast
    moreover have "trans ?m" using `trans m` and `x \<notin> Field m`
      unfolding trans_def Field_def by blast
    moreover have "antisym ?m" using `antisym m` and `x \<notin> Field m`
      unfolding antisym_def Field_def by blast
    moreover have "Total ?m" using `Total m` and Fm by (auto simp: total_on_def)
    moreover have "wf (?m - Id)"
    proof -
      have "wf ?s" using `x \<notin> Field m` unfolding wf_eq_minimal Field_def
        by (auto simp: Bex_def)
      thus ?thesis using `wf (m - Id)` and `x \<notin> Field m`
        wf_subset [OF `wf ?s` Diff_subset]
        unfolding Un_Diff Field_def by (auto intro: wf_Un)
    qed
    ultimately have "Well_order ?m" by (simp add: order_on_defs)
--{*We show that the extension is above m*}
    moreover have "(m, ?m) \<in> I" using `Well_order ?m` and `Well_order m` and `x \<notin> Field m`
      by (fastforce simp: I_def init_seg_of_def Field_def)
    ultimately
--{*This contradicts maximality of m:*}
    have False using max and `x \<notin> Field m` unfolding Field_def by blast
  }
  hence "Field m = UNIV" by auto
  with `Well_order m` show ?thesis by blast
qed

corollary well_order_on: "\<exists>r::'a rel. well_order_on A r"
proof -
  obtain r::"'a rel" where wo: "Well_order r" and univ: "Field r = UNIV"
    using well_ordering [where 'a = "'a"] by blast
  let ?r = "{(x, y). x \<in> A \<and> y \<in> A \<and> (x, y) \<in> r}"
  have 1: "Field ?r = A" using wo univ
    by (fastforce simp: Field_def order_on_defs refl_on_def)
  have "Refl r" and "trans r" and "antisym r" and "Total r" and "wf (r - Id)"
    using `Well_order r` by (simp_all add: order_on_defs)
  have "Refl ?r" using `Refl r` by (auto simp: refl_on_def 1 univ)
  moreover have "trans ?r" using `trans r`
    unfolding trans_def by blast
  moreover have "antisym ?r" using `antisym r`
    unfolding antisym_def by blast
  moreover have "Total ?r" using `Total r` by (simp add:total_on_def 1 univ)
  moreover have "wf (?r - Id)" by (rule wf_subset [OF `wf (r - Id)`]) blast
  ultimately have "Well_order ?r" by (simp add: order_on_defs)
  with 1 show ?thesis by auto
qed

end

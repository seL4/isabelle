(*  Title:       HOL/Zorn.thy
    Author:      Jacques D. Fleuriot
    Author:      Tobias Nipkow, TUM
    Author:      Christian Sternagel, JAIST

Zorn's Lemma (ported from Larry Paulson's Zorn.thy in ZF).
*)

section \<open>Zorn's Lemma and the Well-ordering Theorem\<close>

theory Zorn
  imports Order_Relation Hilbert_Choice
begin

subsection \<open>Zorn's Lemma for the Subset Relation\<close>

subsubsection \<open>Results that do not require an order\<close>

text \<open>Let \<open>P\<close> be a binary predicate on the set \<open>A\<close>.\<close>
locale pred_on =
  fixes A :: "'a set"
    and P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix \<open>\<sqsubset>\<close> 50)
begin

abbreviation Peq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix \<open>\<sqsubseteq>\<close> 50)
  where "x \<sqsubseteq> y \<equiv> P\<^sup>=\<^sup>= x y"

text \<open>A chain is a totally ordered subset of \<open>A\<close>.\<close>
definition chain :: "'a set \<Rightarrow> bool"
  where "chain C \<longleftrightarrow> C \<subseteq> A \<and> (\<forall>x\<in>C. \<forall>y\<in>C. x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

text \<open>
  We call a chain that is a proper superset of some set \<open>X\<close>,
  but not necessarily a chain itself, a superchain of \<open>X\<close>.
\<close>
abbreviation superchain :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"  (infix \<open><c\<close> 50)
  where "X <c C \<equiv> chain C \<and> X \<subset> C"

text \<open>A maximal chain is a chain that does not have a superchain.\<close>
definition maxchain :: "'a set \<Rightarrow> bool"
  where "maxchain C \<longleftrightarrow> chain C \<and> (\<nexists>S. C <c S)"

text \<open>
  We define the successor of a set to be an arbitrary
  superchain, if such exists, or the set itself, otherwise.
\<close>
definition suc :: "'a set \<Rightarrow> 'a set"
  where "suc C = (if \<not> chain C \<or> maxchain C then C else (SOME D. C <c D))"

lemma chainI [Pure.intro?]: "C \<subseteq> A \<Longrightarrow> (\<And>x y. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x) \<Longrightarrow> chain C"
  unfolding chain_def by blast

lemma chain_total: "chain C \<Longrightarrow> x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  by (simp add: chain_def)

lemma not_chain_suc [simp]: "\<not> chain X \<Longrightarrow> suc X = X"
  by (simp add: suc_def)

lemma maxchain_suc [simp]: "maxchain X \<Longrightarrow> suc X = X"
  by (simp add: suc_def)

lemma suc_subset: "X \<subseteq> suc X"
  by (auto simp: suc_def maxchain_def intro: someI2)

lemma chain_empty [simp]: "chain {}"
  by (auto simp: chain_def)

lemma not_maxchain_Some: "chain C \<Longrightarrow> \<not> maxchain C \<Longrightarrow> C <c (SOME D. C <c D)"
  by (rule someI_ex) (auto simp: maxchain_def)

lemma suc_not_equals: "chain C \<Longrightarrow> \<not> maxchain C \<Longrightarrow> suc C \<noteq> C"
  using not_maxchain_Some by (auto simp: suc_def)

lemma subset_suc:
  assumes "X \<subseteq> Y"
  shows "X \<subseteq> suc Y"
  using assms by (rule subset_trans) (rule suc_subset)

text \<open>
  We build a set \<^term>\<open>\<C>\<close> that is closed under applications
  of \<^term>\<open>suc\<close> and contains the union of all its subsets.
\<close>
inductive_set suc_Union_closed (\<open>\<C>\<close>)
  where
    suc: "X \<in> \<C> \<Longrightarrow> suc X \<in> \<C>"
  | Union [unfolded Pow_iff]: "X \<in> Pow \<C> \<Longrightarrow> \<Union>X \<in> \<C>"

text \<open>
  Since the empty set as well as the set itself is a subset of
  every set, \<^term>\<open>\<C>\<close> contains at least \<^term>\<open>{} \<in> \<C>\<close> and
  \<^term>\<open>\<Union>\<C> \<in> \<C>\<close>.
\<close>
lemma suc_Union_closed_empty: "{} \<in> \<C>"
  and suc_Union_closed_Union: "\<Union>\<C> \<in> \<C>"
  using Union [of "{}"] and Union [of "\<C>"] by simp_all

text \<open>Thus closure under \<^term>\<open>suc\<close> will hit a maximal chain
  eventually, as is shown below.\<close>

lemma suc_Union_closed_induct [consumes 1, case_names suc Union, induct pred: suc_Union_closed]:
  assumes "X \<in> \<C>"
    and "\<And>X. X \<in> \<C> \<Longrightarrow> Q X \<Longrightarrow> Q (suc X)"
    and "\<And>X. X \<subseteq> \<C> \<Longrightarrow> \<forall>x\<in>X. Q x \<Longrightarrow> Q (\<Union>X)"
  shows "Q X"
  using assms by induct blast+

lemma suc_Union_closed_cases [consumes 1, case_names suc Union, cases pred: suc_Union_closed]:
  assumes "X \<in> \<C>"
    and "\<And>Y. X = suc Y \<Longrightarrow> Y \<in> \<C> \<Longrightarrow> Q"
    and "\<And>Y. X = \<Union>Y \<Longrightarrow> Y \<subseteq> \<C> \<Longrightarrow> Q"
  shows "Q"
  using assms by cases simp_all

text \<open>On chains, \<^term>\<open>suc\<close> yields a chain.\<close>
lemma chain_suc:
  assumes "chain X"
  shows "chain (suc X)"
  using assms
  by (cases "\<not> chain X \<or> maxchain X") (force simp: suc_def dest: not_maxchain_Some)+

lemma chain_sucD:
  assumes "chain X"
  shows "suc X \<subseteq> A \<and> chain (suc X)"
proof -
  from \<open>chain X\<close> have *: "chain (suc X)"
    by (rule chain_suc)
  then have "suc X \<subseteq> A"
    unfolding chain_def by blast
  with * show ?thesis by blast
qed

lemma suc_Union_closed_total':
  assumes "X \<in> \<C>" and "Y \<in> \<C>"
    and *: "\<And>Z. Z \<in> \<C> \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow> Z = Y \<or> suc Z \<subseteq> Y"
  shows "X \<subseteq> Y \<or> suc Y \<subseteq> X"
  using \<open>X \<in> \<C>\<close>
proof induct
  case (suc X)
  with * show ?case by (blast del: subsetI intro: subset_suc)
next
  case Union
  then show ?case by blast
qed

lemma suc_Union_closed_subsetD:
  assumes "Y \<subseteq> X" and "X \<in> \<C>" and "Y \<in> \<C>"
  shows "X = Y \<or> suc Y \<subseteq> X"
  using assms(2,3,1)
proof (induct arbitrary: Y)
  case (suc X)
  note * = \<open>\<And>Y. Y \<in> \<C> \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> X = Y \<or> suc Y \<subseteq> X\<close>
  with suc_Union_closed_total' [OF \<open>Y \<in> \<C>\<close> \<open>X \<in> \<C>\<close>]
  have "Y \<subseteq> X \<or> suc X \<subseteq> Y" by blast
  then show ?case
  proof
    assume "Y \<subseteq> X"
    with * and \<open>Y \<in> \<C>\<close> subset_suc show ?thesis
      by fastforce
  next
    assume "suc X \<subseteq> Y"
    with \<open>Y \<subseteq> suc X\<close> show ?thesis by blast
  qed
next
  case (Union X)
  show ?case
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with \<open>Y \<subseteq> \<Union>X\<close> obtain x y z
      where "\<not> suc Y \<subseteq> \<Union>X"
        and "x \<in> X" and "y \<in> x" and "y \<notin> Y"
        and "z \<in> suc Y" and "\<forall>x\<in>X. z \<notin> x" by blast
    with \<open>X \<subseteq> \<C>\<close> have "x \<in> \<C>" by blast
    from Union and \<open>x \<in> X\<close> have *: "\<And>y. y \<in> \<C> \<Longrightarrow> y \<subseteq> x \<Longrightarrow> x = y \<or> suc y \<subseteq> x"
      by blast
    with suc_Union_closed_total' [OF \<open>Y \<in> \<C>\<close> \<open>x \<in> \<C>\<close>] have "Y \<subseteq> x \<or> suc x \<subseteq> Y"
      by blast
    then show False
    proof
      assume "Y \<subseteq> x"
      with * [OF \<open>Y \<in> \<C>\<close>] \<open>y \<in> x\<close> \<open>y \<notin> Y\<close> \<open>x \<in> X\<close> \<open>\<not> suc Y \<subseteq> \<Union>X\<close> show False
        by blast
    next
      assume "suc x \<subseteq> Y"
      with \<open>y \<notin> Y\<close> suc_subset \<open>y \<in> x\<close> show False by blast
    qed
  qed
qed

text \<open>The elements of \<^term>\<open>\<C>\<close> are totally ordered by the subset relation.\<close>
lemma suc_Union_closed_total:
  assumes "X \<in> \<C>" and "Y \<in> \<C>"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X"
proof (cases "\<forall>Z\<in>\<C>. Z \<subseteq> Y \<longrightarrow> Z = Y \<or> suc Z \<subseteq> Y")
  case True
  with suc_Union_closed_total' [OF assms]
  have "X \<subseteq> Y \<or> suc Y \<subseteq> X" by blast
  with suc_subset [of Y] show ?thesis by blast
next
  case False
  then obtain Z where "Z \<in> \<C>" and "Z \<subseteq> Y" and "Z \<noteq> Y" and "\<not> suc Z \<subseteq> Y"
    by blast
  with suc_Union_closed_subsetD and \<open>Y \<in> \<C>\<close> show ?thesis
    by blast
qed

text \<open>Once we hit a fixed point w.r.t. \<^term>\<open>suc\<close>, all other elements
  of \<^term>\<open>\<C>\<close> are subsets of this fixed point.\<close>
lemma suc_Union_closed_suc:
  assumes "X \<in> \<C>" and "Y \<in> \<C>" and "suc Y = Y"
  shows "X \<subseteq> Y"
  using \<open>X \<in> \<C>\<close>
proof induct
  case (suc X)
  with \<open>Y \<in> \<C>\<close> and suc_Union_closed_subsetD have "X = Y \<or> suc X \<subseteq> Y"
    by blast
  then show ?case
    by (auto simp: \<open>suc Y = Y\<close>)
next
  case Union
  then show ?case by blast
qed

lemma eq_suc_Union:
  assumes "X \<in> \<C>"
  shows "suc X = X \<longleftrightarrow> X = \<Union>\<C>"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "\<Union>\<C> \<subseteq> X"
    by (rule suc_Union_closed_suc [OF suc_Union_closed_Union \<open>X \<in> \<C>\<close>])
  with \<open>X \<in> \<C>\<close> show ?rhs
    by blast
next
  from \<open>X \<in> \<C>\<close> have "suc X \<in> \<C>" by (rule suc)
  then have "suc X \<subseteq> \<Union>\<C>" by blast
  moreover assume ?rhs
  ultimately have "suc X \<subseteq> X" by simp
  moreover have "X \<subseteq> suc X" by (rule suc_subset)
  ultimately show ?lhs ..
qed

lemma suc_in_carrier:
  assumes "X \<subseteq> A"
  shows "suc X \<subseteq> A"
  using assms
  by (cases "\<not> chain X \<or> maxchain X") (auto dest: chain_sucD)

lemma suc_Union_closed_in_carrier:
  assumes "X \<in> \<C>"
  shows "X \<subseteq> A"
  using assms
  by induct (auto dest: suc_in_carrier)

text \<open>All elements of \<^term>\<open>\<C>\<close> are chains.\<close>
lemma suc_Union_closed_chain:
  assumes "X \<in> \<C>"
  shows "chain X"
  using assms
proof induct
  case (suc X)
  then show ?case
    using not_maxchain_Some by (simp add: suc_def)
next
  case (Union X)
  then have "\<Union>X \<subseteq> A"
    by (auto dest: suc_Union_closed_in_carrier)
  moreover have "\<forall>x\<in>\<Union>X. \<forall>y\<in>\<Union>X. x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  proof (intro ballI)
    fix x y
    assume "x \<in> \<Union>X" and "y \<in> \<Union>X"
    then obtain u v where "x \<in> u" and "u \<in> X" and "y \<in> v" and "v \<in> X"
      by blast
    with Union have "u \<in> \<C>" and "v \<in> \<C>" and "chain u" and "chain v"
      by blast+
    with suc_Union_closed_total have "u \<subseteq> v \<or> v \<subseteq> u"
      by blast
    then show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
    proof
      assume "u \<subseteq> v"
      from \<open>chain v\<close> show ?thesis
      proof (rule chain_total)
        show "y \<in> v" by fact
        show "x \<in> v" using \<open>u \<subseteq> v\<close> and \<open>x \<in> u\<close> by blast
      qed
    next
      assume "v \<subseteq> u"
      from \<open>chain u\<close> show ?thesis
      proof (rule chain_total)
        show "x \<in> u" by fact
        show "y \<in> u" using \<open>v \<subseteq> u\<close> and \<open>y \<in> v\<close> by blast
      qed
    qed
  qed
  ultimately show ?case unfolding chain_def ..
qed

subsubsection \<open>Hausdorff's Maximum Principle\<close>

text \<open>There exists a maximal totally ordered subset of \<open>A\<close>. (Note that we do not
  require \<open>A\<close> to be partially ordered.)\<close>

theorem Hausdorff: "\<exists>C. maxchain C"
proof -
  let ?M = "\<Union>\<C>"
  have "maxchain ?M"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "suc ?M \<noteq> ?M"
      using suc_not_equals and suc_Union_closed_chain [OF suc_Union_closed_Union] by simp
    moreover have "suc ?M = ?M"
      using eq_suc_Union [OF suc_Union_closed_Union] by simp
    ultimately show False by contradiction
  qed
  then show ?thesis by blast
qed

text \<open>Make notation \<^term>\<open>\<C>\<close> available again.\<close>
no_notation suc_Union_closed  (\<open>\<C>\<close>)

lemma chain_extend: "chain C \<Longrightarrow> z \<in> A \<Longrightarrow> \<forall>x\<in>C. x \<sqsubseteq> z \<Longrightarrow> chain ({z} \<union> C)"
  unfolding chain_def by blast

lemma maxchain_imp_chain: "maxchain C \<Longrightarrow> chain C"
  by (simp add: maxchain_def)

end

text \<open>Hide constant \<^const>\<open>pred_on.suc_Union_closed\<close>, which was just needed
  for the proof of Hausforff's maximum principle.\<close>
hide_const pred_on.suc_Union_closed

lemma chain_mono:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P x y \<Longrightarrow> Q x y"
    and "pred_on.chain A P C"
  shows "pred_on.chain A Q C"
  using assms unfolding pred_on.chain_def by blast


subsubsection \<open>Results for the proper subset relation\<close>

interpretation subset: pred_on "A" "(\<subset>)" for A .

lemma subset_maxchain_max:
  assumes "subset.maxchain A C"
    and "X \<in> A"
    and "\<Union>C \<subseteq> X"
  shows "\<Union>C = X"
proof (rule ccontr)
  let ?C = "{X} \<union> C"
  from \<open>subset.maxchain A C\<close> have "subset.chain A C"
    and *: "\<And>S. subset.chain A S \<Longrightarrow> \<not> C \<subset> S"
    by (auto simp: subset.maxchain_def)
  moreover have "\<forall>x\<in>C. x \<subseteq> X" using \<open>\<Union>C \<subseteq> X\<close> by auto
  ultimately have "subset.chain A ?C"
    using subset.chain_extend [of A C X] and \<open>X \<in> A\<close> by auto
  moreover assume **: "\<Union>C \<noteq> X"
  moreover from ** have "C \<subset> ?C" using \<open>\<Union>C \<subseteq> X\<close> by auto
  ultimately show False using * by blast
qed

lemma subset_chain_def: "\<And>\<A>. subset.chain \<A> \<C> = (\<C> \<subseteq> \<A> \<and> (\<forall>X\<in>\<C>. \<forall>Y\<in>\<C>. X \<subseteq> Y \<or> Y \<subseteq> X))"
  by (auto simp: subset.chain_def)

lemma subset_chain_insert:
  "subset.chain \<A> (insert B \<B>) \<longleftrightarrow> B \<in> \<A> \<and> (\<forall>X\<in>\<B>. X \<subseteq> B \<or> B \<subseteq> X) \<and> subset.chain \<A> \<B>"
  by (fastforce simp add: subset_chain_def)

subsubsection \<open>Zorn's lemma\<close>

text \<open>If every chain has an upper bound, then there is a maximal set.\<close>
theorem subset_Zorn:
  assumes "\<And>C. subset.chain A C \<Longrightarrow> \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U"
  shows "\<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
proof -
  from subset.Hausdorff [of A] obtain M where "subset.maxchain A M" ..
  then have "subset.chain A M"
    by (rule subset.maxchain_imp_chain)
  with assms obtain Y where "Y \<in> A" and "\<forall>X\<in>M. X \<subseteq> Y"
    by blast
  moreover have "\<forall>X\<in>A. Y \<subseteq> X \<longrightarrow> Y = X"
  proof (intro ballI impI)
    fix X
    assume "X \<in> A" and "Y \<subseteq> X"
    show "Y = X"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with \<open>Y \<subseteq> X\<close> have "\<not> X \<subseteq> Y" by blast
      from subset.chain_extend [OF \<open>subset.chain A M\<close> \<open>X \<in> A\<close>] and \<open>\<forall>X\<in>M. X \<subseteq> Y\<close>
      have "subset.chain A ({X} \<union> M)"
        using \<open>Y \<subseteq> X\<close> by auto
      moreover have "M \<subset> {X} \<union> M"
        using \<open>\<forall>X\<in>M. X \<subseteq> Y\<close> and \<open>\<not> X \<subseteq> Y\<close> by auto
      ultimately show False
        using \<open>subset.maxchain A M\<close> by (auto simp: subset.maxchain_def)
    qed
  qed
  ultimately show ?thesis by blast
qed

text \<open>Alternative version of Zorn's lemma for the subset relation.\<close>
lemma subset_Zorn':
  assumes "\<And>C. subset.chain A C \<Longrightarrow> \<Union>C \<in> A"
  shows "\<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
proof -
  from subset.Hausdorff [of A] obtain M where "subset.maxchain A M" ..
  then have "subset.chain A M"
    by (rule subset.maxchain_imp_chain)
  with assms have "\<Union>M \<in> A" .
  moreover have "\<forall>Z\<in>A. \<Union>M \<subseteq> Z \<longrightarrow> \<Union>M = Z"
  proof (intro ballI impI)
    fix Z
    assume "Z \<in> A" and "\<Union>M \<subseteq> Z"
    with subset_maxchain_max [OF \<open>subset.maxchain A M\<close>]
      show "\<Union>M = Z" .
  qed
  ultimately show ?thesis by blast
qed


subsection \<open>Zorn's Lemma for Partial Orders\<close>

text \<open>Relate old to new definitions.\<close>

definition chain_subset :: "'a set set \<Rightarrow> bool"  (\<open>chain\<^sub>\<subseteq>\<close>)  (* Define globally? In Set.thy? *)
  where "chain\<^sub>\<subseteq> C \<longleftrightarrow> (\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B \<or> B \<subseteq> A)"

definition chains :: "'a set set \<Rightarrow> 'a set set set"
  where "chains A = {C. C \<subseteq> A \<and> chain\<^sub>\<subseteq> C}"

definition Chains :: "('a \<times> 'a) set \<Rightarrow> 'a set set"  (* Define globally? In Relation.thy? *)
  where "Chains r = {C. \<forall>a\<in>C. \<forall>b\<in>C. (a, b) \<in> r \<or> (b, a) \<in> r}"

lemma chains_extend: "c \<in> chains S \<Longrightarrow> z \<in> S \<Longrightarrow> \<forall>x \<in> c. x \<subseteq> z \<Longrightarrow> {z} \<union> c \<in> chains S"
  for z :: "'a set"
  unfolding chains_def chain_subset_def by blast

lemma mono_Chains: "r \<subseteq> s \<Longrightarrow> Chains r \<subseteq> Chains s"
  unfolding Chains_def by blast

lemma chain_subset_alt_def: "chain\<^sub>\<subseteq> C = subset.chain UNIV C"
  unfolding chain_subset_def subset.chain_def by fast

lemma chains_alt_def: "chains A = {C. subset.chain A C}"
  by (simp add: chains_def chain_subset_alt_def subset.chain_def)

lemma Chains_subset: "Chains r \<subseteq> {C. pred_on.chain UNIV (\<lambda>x y. (x, y) \<in> r) C}"
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

lemma Chains_relation_of:
  assumes "C \<in> Chains (relation_of P A)" shows "C \<subseteq> A"
  using assms unfolding Chains_def relation_of_def by auto

lemma pairwise_chain_Union:
  assumes P: "\<And>S. S \<in> \<C> \<Longrightarrow> pairwise R S" and "chain\<^sub>\<subseteq> \<C>"
  shows "pairwise R (\<Union>\<C>)"
  using \<open>chain\<^sub>\<subseteq> \<C>\<close> unfolding pairwise_def chain_subset_def
  by (blast intro: P [unfolded pairwise_def, rule_format])

lemma Zorn_Lemma: "\<forall>C\<in>chains A. \<Union>C \<in> A \<Longrightarrow> \<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
  using subset_Zorn' [of A] by (force simp: chains_alt_def)

lemma Zorn_Lemma2: "\<forall>C\<in>chains A. \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U \<Longrightarrow> \<exists>M\<in>A. \<forall>X\<in>A. M \<subseteq> X \<longrightarrow> X = M"
  using subset_Zorn [of A] by (auto simp: chains_alt_def)

subsection \<open>Other variants of Zorn's Lemma\<close>

lemma chainsD: "c \<in> chains S \<Longrightarrow> x \<in> c \<Longrightarrow> y \<in> c \<Longrightarrow> x \<subseteq> y \<or> y \<subseteq> x"
  unfolding chains_def chain_subset_def by blast

lemma chainsD2: "c \<in> chains S \<Longrightarrow> c \<subseteq> S"
  unfolding chains_def by blast

lemma Zorns_po_lemma:
  assumes po: "Partial_order r"
    and u: "\<And>C. C \<in> Chains r \<Longrightarrow> \<exists>u\<in>Field r. \<forall>a\<in>C. (a, u) \<in> r"
  shows "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
proof -
  have "Preorder r"
    using po by (simp add: partial_order_on_def)
  txt \<open>Mirror \<open>r\<close> in the set of subsets below (wrt \<open>r\<close>) elements of \<open>A\<close>.\<close>
  let ?B = "\<lambda>x. r\<inverse> `` {x}"
  let ?S = "?B ` Field r"
  have "\<exists>u\<in>Field r. \<forall>A\<in>C. A \<subseteq> r\<inverse> `` {u}"  (is "\<exists>u\<in>Field r. ?P u")
    if 1: "C \<subseteq> ?S" and 2: "\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B \<or> B \<subseteq> A" for C
  proof -
    let ?A = "{x\<in>Field r. \<exists>M\<in>C. M = ?B x}"
    from 1 have "C = ?B ` ?A" by (auto simp: image_def)
    have "?A \<in> Chains r"
    proof (simp add: Chains_def, intro allI impI, elim conjE)
      fix a b
      assume "a \<in> Field r" and "?B a \<in> C" and "b \<in> Field r" and "?B b \<in> C"
      with 2 have "?B a \<subseteq> ?B b \<or> ?B b \<subseteq> ?B a" by auto
      then show "(a, b) \<in> r \<or> (b, a) \<in> r"
        using \<open>Preorder r\<close> and \<open>a \<in> Field r\<close> and \<open>b \<in> Field r\<close>
        by (simp add:subset_Image1_Image1_iff)
    qed
    then obtain u where uA: "u \<in> Field r" "\<forall>a\<in>?A. (a, u) \<in> r"
      by (auto simp: dest: u)
    have "?P u"
    proof auto
      fix a B assume aB: "B \<in> C" "a \<in> B"
      with 1 obtain x where "x \<in> Field r" and "B = r\<inverse> `` {x}" by auto
      then show "(a, u) \<in> r"
        using uA and aB and \<open>Preorder r\<close>
        unfolding preorder_on_def refl_on_def by simp (fast dest: transD)
    qed
    then show ?thesis
      using \<open>u \<in> Field r\<close> by blast
  qed
  then have "\<forall>C\<in>chains ?S. \<exists>U\<in>?S. \<forall>A\<in>C. A \<subseteq> U"
    by (auto simp: chains_def chain_subset_def)
  from Zorn_Lemma2 [OF this] obtain m B
    where "m \<in> Field r"
      and "B = r\<inverse> `` {m}"
      and "\<forall>x\<in>Field r. B \<subseteq> r\<inverse> `` {x} \<longrightarrow> r\<inverse> `` {x} = B"
    by auto
  then have "\<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
    using po and \<open>Preorder r\<close> and \<open>m \<in> Field r\<close>
    by (auto simp: subset_Image1_Image1_iff Partial_order_eq_Image1_Image1_iff)
  then show ?thesis
    using \<open>m \<in> Field r\<close> by blast
qed

lemma predicate_Zorn:
  assumes po: "partial_order_on A (relation_of P A)"
    and ch: "\<And>C. C \<in> Chains (relation_of P A) \<Longrightarrow> \<exists>u \<in> A. \<forall>a \<in> C. P a u"
  shows "\<exists>m \<in> A. \<forall>a \<in> A. P m a \<longrightarrow> a = m"
proof -
  have "a \<in> A" if "C \<in> Chains (relation_of P A)" and "a \<in> C" for C a
    using that unfolding Chains_def relation_of_def by auto
  moreover have "(a, u) \<in> relation_of P A" if "a \<in> A" and "u \<in> A" and "P a u" for a u
    unfolding relation_of_def using that by auto
  ultimately have "\<exists>m\<in>A. \<forall>a\<in>A. (m, a) \<in> relation_of P A \<longrightarrow> a = m"
    using Zorns_po_lemma[OF Partial_order_relation_ofI[OF po], rule_format] ch
    unfolding Field_relation_of[OF partial_order_onD(1)[OF po]] by blast
  then show ?thesis
    by (auto simp: relation_of_def)
qed

lemma Union_in_chain: "\<lbrakk>finite \<B>; \<B> \<noteq> {}; subset.chain \<A> \<B>\<rbrakk> \<Longrightarrow> \<Union>\<B> \<in> \<B>"
proof (induction \<B> rule: finite_induct)
  case (insert B \<B>)
  show ?case
  proof (cases "\<B> = {}")
    case False
    then show ?thesis
      using insert sup.absorb2 by (auto simp: subset_chain_insert dest!: bspec [where x="\<Union>\<B>"])
  qed auto
qed simp

lemma Inter_in_chain: "\<lbrakk>finite \<B>; \<B> \<noteq> {}; subset.chain \<A> \<B>\<rbrakk> \<Longrightarrow> \<Inter>\<B> \<in> \<B>"
proof (induction \<B> rule: finite_induct)
  case (insert B \<B>)
  show ?case
  proof (cases "\<B> = {}")
    case False
    then show ?thesis
      using insert inf.absorb2 by (auto simp: subset_chain_insert dest!: bspec [where x="\<Inter>\<B>"])
  qed auto
qed simp

lemma finite_subset_Union_chain:
  assumes "finite A" "A \<subseteq> \<Union>\<B>" "\<B> \<noteq> {}" and sub: "subset.chain \<A> \<B>"
  obtains B where "B \<in> \<B>" "A \<subseteq> B"
proof -
  obtain \<F> where \<F>: "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union>\<F>"
    using assms by (auto intro: finite_subset_Union)
  show thesis
  proof (cases "\<F> = {}")
    case True
    then show ?thesis
      using \<open>A \<subseteq> \<Union>\<F>\<close> \<open>\<B> \<noteq> {}\<close> that by fastforce
  next
    case False
    show ?thesis
    proof
      show "\<Union>\<F> \<in> \<B>"
        using sub \<open>\<F> \<subseteq> \<B>\<close> \<open>finite \<F>\<close>
        by (simp add: Union_in_chain False subset.chain_def subset_iff)
      show "A \<subseteq> \<Union>\<F>"
        using \<open>A \<subseteq> \<Union>\<F>\<close> by blast
    qed
  qed
qed

lemma subset_Zorn_nonempty:
  assumes "\<A> \<noteq> {}" and ch: "\<And>\<C>. \<lbrakk>\<C>\<noteq>{}; subset.chain \<A> \<C>\<rbrakk> \<Longrightarrow> \<Union>\<C> \<in> \<A>"
  shows "\<exists>M\<in>\<A>. \<forall>X\<in>\<A>. M \<subseteq> X \<longrightarrow> X = M"
proof (rule subset_Zorn)
  show "\<exists>U\<in>\<A>. \<forall>X\<in>\<C>. X \<subseteq> U" if "subset.chain \<A> \<C>" for \<C>
  proof (cases "\<C> = {}")
    case True
    then show ?thesis
      using \<open>\<A> \<noteq> {}\<close> by blast
  next
    case False
    show ?thesis
      by (blast intro!: ch False that Union_upper)
  qed
qed

subsection \<open>The Well Ordering Theorem\<close>

(* The initial segment of a relation appears generally useful.
   Move to Relation.thy?
   Definition correct/most general?
   Naming?
*)
definition init_seg_of :: "(('a \<times> 'a) set \<times> ('a \<times> 'a) set) set"
  where "init_seg_of = {(r, s). r \<subseteq> s \<and> (\<forall>a b c. (a, b) \<in> s \<and> (b, c) \<in> r \<longrightarrow> (a, b) \<in> r)}"

abbreviation initial_segment_of_syntax :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
    (infix \<open>initial'_segment'_of\<close> 55)
  where "r initial_segment_of s \<equiv> (r, s) \<in> init_seg_of"

lemma refl_on_init_seg_of [simp]: "r initial_segment_of r"
  by (simp add: init_seg_of_def)

lemma trans_init_seg_of:
  "r initial_segment_of s \<Longrightarrow> s initial_segment_of t \<Longrightarrow> r initial_segment_of t"
  by (simp (no_asm_use) add: init_seg_of_def) blast

lemma antisym_init_seg_of: "r initial_segment_of s \<Longrightarrow> s initial_segment_of r \<Longrightarrow> r = s"
  unfolding init_seg_of_def by safe

lemma Chains_init_seg_of_Union: "R \<in> Chains init_seg_of \<Longrightarrow> r\<in>R \<Longrightarrow> r initial_segment_of \<Union>R"
  by (auto simp: init_seg_of_def Ball_def Chains_def) blast

lemma chain_subset_trans_Union:
  assumes "chain\<^sub>\<subseteq> R" "\<forall>r\<in>R. trans r"
  shows "trans (\<Union>R)"
proof (intro transI, elim UnionE)
  fix S1 S2 :: "'a rel" and x y z :: 'a
  assume "S1 \<in> R" "S2 \<in> R"
  with assms(1) have "S1 \<subseteq> S2 \<or> S2 \<subseteq> S1"
    unfolding chain_subset_def by blast
  moreover assume "(x, y) \<in> S1" "(y, z) \<in> S2"
  ultimately have "((x, y) \<in> S1 \<and> (y, z) \<in> S1) \<or> ((x, y) \<in> S2 \<and> (y, z) \<in> S2)"
    by blast
  with \<open>S1 \<in> R\<close> \<open>S2 \<in> R\<close> assms(2) show "(x, z) \<in> \<Union>R"
    by (auto elim: transE)
qed

lemma chain_subset_antisym_Union:
  assumes "chain\<^sub>\<subseteq> R" "\<forall>r\<in>R. antisym r"
  shows "antisym (\<Union>R)"
proof (intro antisymI, elim UnionE)
  fix S1 S2 :: "'a rel" and x y :: 'a
  assume "S1 \<in> R" "S2 \<in> R"
  with assms(1) have "S1 \<subseteq> S2 \<or> S2 \<subseteq> S1"
    unfolding chain_subset_def by blast
  moreover assume "(x, y) \<in> S1" "(y, x) \<in> S2"
  ultimately have "((x, y) \<in> S1 \<and> (y, x) \<in> S1) \<or> ((x, y) \<in> S2 \<and> (y, x) \<in> S2)"
    by blast
  with \<open>S1 \<in> R\<close> \<open>S2 \<in> R\<close> assms(2) show "x = y"
    unfolding antisym_def by auto
qed

lemma chain_subset_Total_Union:
  assumes "chain\<^sub>\<subseteq> R" and "\<forall>r\<in>R. Total r"
  shows "Total (\<Union>R)"
proof (simp add: total_on_def Ball_def, auto del: disjCI)
  fix r s a b
  assume A: "r \<in> R" "s \<in> R" "a \<in> Field r" "b \<in> Field s" "a \<noteq> b"
  from \<open>chain\<^sub>\<subseteq> R\<close> and \<open>r \<in> R\<close> and \<open>s \<in> R\<close> have "r \<subseteq> s \<or> s \<subseteq> r"
    by (auto simp add: chain_subset_def)
  then show "(\<exists>r\<in>R. (a, b) \<in> r) \<or> (\<exists>r\<in>R. (b, a) \<in> r)"
  proof
    assume "r \<subseteq> s"
    then have "(a, b) \<in> s \<or> (b, a) \<in> s"
      using assms(2) A mono_Field[of r s]
      by (auto simp add: total_on_def)
    then show ?thesis
      using \<open>s \<in> R\<close> by blast
  next
    assume "s \<subseteq> r"
    then have "(a, b) \<in> r \<or> (b, a) \<in> r"
      using assms(2) A mono_Field[of s r]
      by (fastforce simp add: total_on_def)
    then show ?thesis
      using \<open>r \<in> R\<close> by blast
  qed
qed

lemma wf_Union_wf_init_segs:
  assumes "R \<in> Chains init_seg_of"
    and "\<forall>r\<in>R. wf r"
  shows "wf (\<Union>R)"
proof (simp add: wf_iff_no_infinite_down_chain, rule ccontr, auto)
  fix f
  assume 1: "\<forall>i. \<exists>r\<in>R. (f (Suc i), f i) \<in> r"
  then obtain r where "r \<in> R" and "(f (Suc 0), f 0) \<in> r" by auto
  have "(f (Suc i), f i) \<in> r" for i
  proof (induct i)
    case 0
    show ?case by fact
  next
    case (Suc i)
    then obtain s where s: "s \<in> R" "(f (Suc (Suc i)), f(Suc i)) \<in> s"
      using 1 by auto
    then have "s initial_segment_of r \<or> r initial_segment_of s"
      using assms(1) \<open>r \<in> R\<close> by (simp add: Chains_def)
    with Suc s show ?case by (simp add: init_seg_of_def) blast
  qed
  then show False
    using assms(2) and \<open>r \<in> R\<close>
    by (simp add: wf_iff_no_infinite_down_chain) blast
qed

lemma initial_segment_of_Diff: "p initial_segment_of q \<Longrightarrow> p - s initial_segment_of q - s"
  unfolding init_seg_of_def by blast

lemma Chains_inits_DiffI: "R \<in> Chains init_seg_of \<Longrightarrow> {r - s |r. r \<in> R} \<in> Chains init_seg_of"
  unfolding Chains_def by (blast intro: initial_segment_of_Diff)

theorem well_ordering: "\<exists>r::'a rel. Well_order r \<and> Field r = UNIV"
proof -
\<comment> \<open>The initial segment relation on well-orders:\<close>
  let ?WO = "{r::'a rel. Well_order r}"
  define I where "I = init_seg_of \<inter> ?WO \<times> ?WO"
  then have I_init: "I \<subseteq> init_seg_of" by simp
  then have subch: "\<And>R. R \<in> Chains I \<Longrightarrow> chain\<^sub>\<subseteq> R"
    unfolding init_seg_of_def chain_subset_def Chains_def by blast
  have Chains_wo: "\<And>R r. R \<in> Chains I \<Longrightarrow> r \<in> R \<Longrightarrow> Well_order r"
    by (simp add: Chains_def I_def) blast
  have FI: "Field I = ?WO"
    by (auto simp add: I_def init_seg_of_def Field_def)
  then have 0: "Partial_order I"
    by (auto simp: partial_order_on_def preorder_on_def antisym_def antisym_init_seg_of refl_on_def
        trans_def I_def elim!: trans_init_seg_of)
\<comment> \<open>\<open>I\<close>-chains have upper bounds in \<open>?WO\<close> wrt \<open>I\<close>: their Union\<close>
  have "\<Union>R \<in> ?WO \<and> (\<forall>r\<in>R. (r, \<Union>R) \<in> I)" if "R \<in> Chains I" for R
  proof -
    from that have Ris: "R \<in> Chains init_seg_of"
      using mono_Chains [OF I_init] by blast
    have subch: "chain\<^sub>\<subseteq> R"
      using \<open>R \<in> Chains I\<close> I_init by (auto simp: init_seg_of_def chain_subset_def Chains_def)
    have "\<forall>r\<in>R. Refl r" and "\<forall>r\<in>R. trans r" and "\<forall>r\<in>R. antisym r"
      and "\<forall>r\<in>R. Total r" and "\<forall>r\<in>R. wf (r - Id)"
      using Chains_wo [OF \<open>R \<in> Chains I\<close>] by (simp_all add: order_on_defs)
    have "Refl (\<Union>R)"
      using \<open>\<forall>r\<in>R. Refl r\<close> unfolding refl_on_def by fastforce
    moreover have "trans (\<Union>R)"
      by (rule chain_subset_trans_Union [OF subch \<open>\<forall>r\<in>R. trans r\<close>])
    moreover have "antisym (\<Union>R)"
      by (rule chain_subset_antisym_Union [OF subch \<open>\<forall>r\<in>R. antisym r\<close>])
    moreover have "Total (\<Union>R)"
      by (rule chain_subset_Total_Union [OF subch \<open>\<forall>r\<in>R. Total r\<close>])
    moreover have "wf ((\<Union>R) - Id)"
    proof -
      have "(\<Union>R) - Id = \<Union>{r - Id | r. r \<in> R}" by blast
      with \<open>\<forall>r\<in>R. wf (r - Id)\<close> and wf_Union_wf_init_segs [OF Chains_inits_DiffI [OF Ris]]
      show ?thesis by fastforce
    qed
    ultimately have "Well_order (\<Union>R)"
      by (simp add:order_on_defs)
    moreover have "\<forall>r \<in> R. r initial_segment_of \<Union>R"
      using Ris by (simp add: Chains_init_seg_of_Union)
    ultimately show ?thesis
      using mono_Chains [OF I_init] Chains_wo[of R] and \<open>R \<in> Chains I\<close>
      unfolding I_def by blast
  qed
  then have 1: "\<exists>u\<in>Field I. \<forall>r\<in>R. (r, u) \<in> I" if "R \<in> Chains I" for R
    using that by (subst FI) blast
\<comment> \<open>Zorn's Lemma yields a maximal well-order \<open>m\<close>:\<close>
  then obtain m :: "'a rel"
    where "Well_order m"
      and max: "\<forall>r. Well_order r \<and> (m, r) \<in> I \<longrightarrow> r = m"
    using Zorns_po_lemma[OF 0 1] unfolding FI by fastforce
\<comment> \<open>Now show by contradiction that \<open>m\<close> covers the whole type:\<close>
  have False if "x \<notin> Field m" for x :: 'a
  proof -
\<comment> \<open>Assuming that \<open>x\<close> is not covered and extend \<open>m\<close> at the top with \<open>x\<close>\<close>
    have "m \<noteq> {}"
    proof
      assume "m = {}"
      moreover have "Well_order {(x, x)}"
        by (simp add: order_on_defs refl_on_def trans_def antisym_def total_on_def Field_def)
      ultimately show False using max
        by (auto simp: I_def init_seg_of_def simp del: Field_insert)
    qed
    then have "Field m \<noteq> {}" by (auto simp: Field_def)
    moreover have "wf (m - Id)"
      using \<open>Well_order m\<close> by (simp add: well_order_on_def)
\<comment> \<open>The extension of \<open>m\<close> by \<open>x\<close>:\<close>
    let ?s = "{(a, x) | a. a \<in> Field m}"
    let ?m = "insert (x, x) m \<union> ?s"
    have Fm: "Field ?m = insert x (Field m)"
      by (auto simp: Field_def)
    have "Refl m" and "trans m" and "antisym m" and "Total m" and "wf (m - Id)"
      using \<open>Well_order m\<close> by (simp_all add: order_on_defs)
\<comment> \<open>We show that the extension is a well-order\<close>
    have "Refl ?m"
      using \<open>Refl m\<close> Fm unfolding refl_on_def by blast
    moreover have "trans ?m" using \<open>trans m\<close> and \<open>x \<notin> Field m\<close>
      unfolding trans_def Field_def by blast
    moreover have "antisym ?m"
      using \<open>antisym m\<close> and \<open>x \<notin> Field m\<close> unfolding antisym_def Field_def by blast
    moreover have "Total ?m"
      using \<open>Total m\<close> and Fm by (auto simp: total_on_def)
    moreover have "wf (?m - Id)"
    proof -
      have "wf ?s"
        using \<open>x \<notin> Field m\<close> by (auto simp: wf_eq_minimal Field_def Bex_def)
      then show ?thesis
        using \<open>wf (m - Id)\<close> and \<open>x \<notin> Field m\<close> wf_subset [OF \<open>wf ?s\<close> Diff_subset]
        by (auto simp: Un_Diff Field_def intro: wf_Un)
    qed
    ultimately have "Well_order ?m"
      by (simp add: order_on_defs)
\<comment> \<open>We show that the extension is above \<open>m\<close>\<close>
    moreover have "(m, ?m) \<in> I"
      using \<open>Well_order ?m\<close> and \<open>Well_order m\<close> and \<open>x \<notin> Field m\<close>
      by (fastforce simp: I_def init_seg_of_def Field_def)
    ultimately
\<comment> \<open>This contradicts maximality of \<open>m\<close>:\<close>
    show False
      using max and \<open>x \<notin> Field m\<close> unfolding Field_def by blast
  qed
  then have "Field m = UNIV" by auto
  with \<open>Well_order m\<close> show ?thesis by blast
qed

corollary well_order_on: "\<exists>r::'a rel. well_order_on A r"
proof -
  obtain r :: "'a rel" where wo: "Well_order r" and univ: "Field r = UNIV"
    using well_ordering [where 'a = "'a"] by blast
  let ?r = "{(x, y). x \<in> A \<and> y \<in> A \<and> (x, y) \<in> r}"
  have 1: "Field ?r = A"
    using wo univ by (fastforce simp: Field_def order_on_defs refl_on_def)
  from \<open>Well_order r\<close> have "Refl r" "trans r" "antisym r" "Total r" "wf (r - Id)"
    by (simp_all add: order_on_defs)
  from \<open>Refl r\<close> have "Refl ?r"
    by (auto simp: refl_on_def 1 univ)
  moreover from \<open>trans r\<close> have "trans ?r"
    unfolding trans_def by blast
  moreover from \<open>antisym r\<close> have "antisym ?r"
    unfolding antisym_def by blast
  moreover from \<open>Total r\<close> have "Total ?r"
    by (simp add:total_on_def 1 univ)
  moreover have "wf (?r - Id)"
    by (rule wf_subset [OF \<open>wf (r - Id)\<close>]) blast
  ultimately have "Well_order ?r"
    by (simp add: order_on_defs)
  with 1 show ?thesis by auto
qed

lemma dependent_wf_choice:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "wf R"
    and adm: "\<And>f g x r. (\<And>z. (z, x) \<in> R \<Longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r"
    and P: "\<And>x f. (\<And>y. (y, x) \<in> R \<Longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r"
  shows "\<exists>f. \<forall>x. P f x (f x)"
proof (intro exI allI)
  fix x
  define f where "f \<equiv> wfrec R (\<lambda>f x. SOME r. P f x r)"
  from \<open>wf R\<close> show "P f x (f x)"
  proof (induct x)
    case (less x)
    show "P f x (f x)"
    proof (subst (2) wfrec_def_adm[OF f_def \<open>wf R\<close>])
      show "adm_wf R (\<lambda>f x. SOME r. P f x r)"
        by (auto simp: adm_wf_def intro!: arg_cong[where f=Eps] adm)
      show "P f x (Eps (P f x))"
        using P by (rule someI_ex) fact
    qed
  qed
qed

lemma (in wellorder) dependent_wellorder_choice:
  assumes "\<And>r f g x. (\<And>y. y < x \<Longrightarrow> f y = g y) \<Longrightarrow> P f x r = P g x r"
    and P: "\<And>x f. (\<And>y. y < x \<Longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r"
  shows "\<exists>f. \<forall>x. P f x (f x)"
  using wf by (rule dependent_wf_choice) (auto intro!: assms)

end

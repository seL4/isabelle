(*  Title:      HOL/Library/Bourbaki_Witt_Fixpoint.thy
    Author:     Andreas Lochbihler, ETH Zurich

  Follows G. Smolka, S. Schäfer and C. Doczkal: Transfinite Constructions in
  Classical Type Theory. ITP 2015
*)

section \<open>The Bourbaki-Witt tower construction for transfinite iteration\<close>

theory Bourbaki_Witt_Fixpoint imports Main begin

lemma ChainsI [intro?]:
  "(\<And>a b. \<lbrakk> a \<in> Y; b \<in> Y \<rbrakk> \<Longrightarrow> (a, b) \<in> r \<or> (b, a) \<in> r) \<Longrightarrow> Y \<in> Chains r"
unfolding Chains_def by blast

lemma in_Chains_subset: "\<lbrakk> M \<in> Chains r; M' \<subseteq> M \<rbrakk> \<Longrightarrow> M' \<in> Chains r"
by(auto simp add: Chains_def)

lemma FieldI1: "(i, j) \<in> R \<Longrightarrow> i \<in> Field R"
  unfolding Field_def by auto

lemma Chains_FieldD: "\<lbrakk> M \<in> Chains r; x \<in> M \<rbrakk> \<Longrightarrow> x \<in> Field r"
by(auto simp add: Chains_def intro: FieldI1 FieldI2)

lemma in_Chains_conv_chain: "M \<in> Chains r \<longleftrightarrow> Complete_Partial_Order.chain (\<lambda>x y. (x, y) \<in> r) M"
by(simp add: Chains_def chain_def)

lemma partial_order_on_trans:
  "\<lbrakk> partial_order_on A r; (x, y) \<in> r; (y, z) \<in> r \<rbrakk> \<Longrightarrow> (x, z) \<in> r"
by(auto simp add: order_on_defs dest: transD)

locale bourbaki_witt_fixpoint =
  fixes lub :: "'a set \<Rightarrow> 'a"
  and leq :: "('a \<times> 'a) set"
  and f :: "'a \<Rightarrow> 'a"
  assumes po: "Partial_order leq"
  and lub_least: "\<lbrakk> M \<in> Chains leq; M \<noteq> {}; \<And>x. x \<in> M \<Longrightarrow> (x, z) \<in> leq \<rbrakk> \<Longrightarrow> (lub M, z) \<in> leq"
  and lub_upper: "\<lbrakk> M \<in> Chains leq; x \<in> M \<rbrakk> \<Longrightarrow> (x, lub M) \<in> leq"
  and lub_in_Field: "\<lbrakk> M \<in> Chains leq; M \<noteq> {} \<rbrakk> \<Longrightarrow> lub M \<in> Field leq"
  and increasing: "\<And>x. x \<in> Field leq \<Longrightarrow> (x, f x) \<in> leq"
begin

lemma leq_trans: "\<lbrakk> (x, y) \<in> leq; (y, z) \<in> leq \<rbrakk> \<Longrightarrow> (x, z) \<in> leq"
by(rule partial_order_on_trans[OF po])

lemma leq_refl: "x \<in> Field leq \<Longrightarrow> (x, x) \<in> leq"
using po by(simp add: order_on_defs refl_on_def)

lemma leq_antisym: "\<lbrakk> (x, y) \<in> leq; (y, x) \<in> leq \<rbrakk> \<Longrightarrow> x = y"
using po by(simp add: order_on_defs antisym_def)

inductive_set iterates_above :: "'a \<Rightarrow> 'a set"
  for a
where
  base: "a \<in> iterates_above a"
| step: "x \<in> iterates_above a \<Longrightarrow> f x \<in> iterates_above a"
| Sup: "\<lbrakk> M \<in> Chains leq; M \<noteq> {}; \<And>x. x \<in> M \<Longrightarrow> x \<in> iterates_above a \<rbrakk> \<Longrightarrow> lub M \<in> iterates_above a"

definition fixp_above :: "'a \<Rightarrow> 'a"
where "fixp_above a = lub (iterates_above a)"

context 
  notes leq_refl [intro!, simp]
  and base [intro]
  and step [intro]
  and Sup [intro]
  and leq_trans [trans]
begin

lemma iterates_above_le_f: "\<lbrakk> x \<in> iterates_above a; a \<in> Field leq \<rbrakk> \<Longrightarrow> (x, f x) \<in> leq"
by(induction x rule: iterates_above.induct)(blast intro: increasing FieldI2 lub_in_Field)+

lemma iterates_above_Field: "\<lbrakk> x \<in> iterates_above a; a \<in> Field leq \<rbrakk> \<Longrightarrow> x \<in> Field leq"
by(drule (1) iterates_above_le_f)(rule FieldI1)

lemma iterates_above_ge:
  assumes y: "y \<in> iterates_above a"
  and a: "a \<in> Field leq"
  shows "(a, y) \<in> leq"
using y by(induction)(auto intro: a increasing iterates_above_le_f leq_trans leq_trans[OF _ lub_upper])

lemma iterates_above_lub:
  assumes M: "M \<in> Chains leq"
  and nempty: "M \<noteq> {}"
  and upper: "\<And>y. y \<in> M \<Longrightarrow> \<exists>z \<in> M. (y, z) \<in> leq \<and> z \<in> iterates_above a"
  shows "lub M \<in> iterates_above a"
proof -
  let ?M = "M \<inter> iterates_above a"
  from M have M': "?M \<in> Chains leq" by(rule in_Chains_subset)simp
  have "?M \<noteq> {}" using nempty by(auto dest: upper)
  with M' have "lub ?M \<in> iterates_above a" by(rule Sup) blast
  also have "lub ?M = lub M" using nempty
    by(intro leq_antisym)(blast intro!: lub_least[OF M] lub_least[OF M'] intro: lub_upper[OF M'] lub_upper[OF M] leq_trans dest: upper)+
  finally show ?thesis .
qed

lemma iterates_above_successor:
  assumes y: "y \<in> iterates_above a"
  and a: "a \<in> Field leq"
  shows "y = a \<or> y \<in> iterates_above (f a)"
using y
proof induction
  case base thus ?case by simp
next
  case (step x) thus ?case by auto
next
  case (Sup M)
  show ?case
  proof(cases "\<exists>x. M \<subseteq> {x}")
    case True
    with \<open>M \<noteq> {}\<close> obtain y where M: "M = {y}" by auto
    have "lub M = y"
      by(rule leq_antisym)(auto intro!: lub_upper Sup lub_least ChainsI simp add: a M Sup.hyps(3)[of y, THEN iterates_above_Field] dest: iterates_above_Field)
    with Sup.IH[of y] M show ?thesis by simp
  next
    case False
    from Sup(1-2) have "lub M \<in> iterates_above (f a)"
    proof(rule iterates_above_lub)
      fix y
      assume y: "y \<in> M"
      from Sup.IH[OF this] show "\<exists>z\<in>M. (y, z) \<in> leq \<and> z \<in> iterates_above (f a)"
      proof
        assume "y = a"
        from y False obtain z where z: "z \<in> M" and neq: "y \<noteq> z" by (metis insertI1 subsetI)
        with Sup.IH[OF z] \<open>y = a\<close> Sup.hyps(3)[OF z]
        show ?thesis by(auto dest: iterates_above_ge intro: a)
      next
        assume "y \<in> iterates_above (f a)"
        moreover with increasing[OF a] have "y \<in> Field leq"
          by(auto dest!: iterates_above_Field intro: FieldI2)
        ultimately show ?thesis using y by(auto)
      qed
    qed
    thus ?thesis by simp
  qed
qed

lemma iterates_above_Sup_aux:
  assumes M: "M \<in> Chains leq" "M \<noteq> {}"
  and M': "M' \<in> Chains leq" "M' \<noteq> {}"
  and comp: "\<And>x. x \<in> M \<Longrightarrow> x \<in> iterates_above (lub M') \<or> lub M' \<in> iterates_above x"
  shows "(lub M, lub M') \<in> leq \<or> lub M \<in> iterates_above (lub M')"
proof(cases "\<exists>x \<in> M. x \<in> iterates_above (lub M')")
  case True
  then obtain x where x: "x \<in> M" "x \<in> iterates_above (lub M')" by blast
  have lub_M': "lub M' \<in> Field leq" using M' by(rule lub_in_Field)
  have "lub M \<in> iterates_above (lub M')" using M
  proof(rule iterates_above_lub)
    fix y
    assume y: "y \<in> M"
    from comp[OF y] show "\<exists>z\<in>M. (y, z) \<in> leq \<and> z \<in> iterates_above (lub M')"
    proof
      assume "y \<in> iterates_above (lub M')"
      from this iterates_above_Field[OF this] y lub_M' show ?thesis by blast
    next
      assume "lub M' \<in> iterates_above y"
      hence "(y, lub M') \<in> leq" using Chains_FieldD[OF M(1) y] by(rule iterates_above_ge)
      also have "(lub M', x) \<in> leq" using x(2) lub_M' by(rule iterates_above_ge)
      finally show ?thesis using x by blast
    qed
  qed
  thus ?thesis ..
next
  case False
  have "(lub M, lub M') \<in> leq" using M
  proof(rule lub_least)
    fix x
    assume x: "x \<in> M"
    from comp[OF x] x False have "lub M' \<in> iterates_above x" by auto
    moreover from M(1) x have "x \<in> Field leq" by(rule Chains_FieldD)
    ultimately show "(x, lub M') \<in> leq" by(rule iterates_above_ge)
  qed
  thus ?thesis ..
qed

lemma iterates_above_triangle:
  assumes x: "x \<in> iterates_above a"
  and y: "y \<in> iterates_above a"
  and a: "a \<in> Field leq"
  shows "x \<in> iterates_above y \<or> y \<in> iterates_above x"
using x y
proof(induction arbitrary: y)
  case base then show ?case by simp
next
  case (step x) thus ?case using a
    by(auto dest: iterates_above_successor intro: iterates_above_Field)
next
  case x: (Sup M)
  hence lub: "lub M \<in> iterates_above a" by blast
  from \<open>y \<in> iterates_above a\<close> show ?case
  proof(induction)
    case base show ?case using lub by simp
  next
    case (step y) thus ?case using a
      by(auto dest: iterates_above_successor intro: iterates_above_Field)
  next
    case y: (Sup M')
    hence lub': "lub M' \<in> iterates_above a" by blast
    have *: "x \<in> iterates_above (lub M') \<or> lub M' \<in> iterates_above x" if "x \<in> M" for x
      using that lub' by(rule x.IH)
    with x(1-2) y(1-2) have "(lub M, lub M') \<in> leq \<or> lub M \<in> iterates_above (lub M')"
      by(rule iterates_above_Sup_aux)
    moreover from y(1-2) x(1-2) have "(lub M', lub M) \<in> leq \<or> lub M' \<in> iterates_above (lub M)"
      by(rule iterates_above_Sup_aux)(blast dest: y.IH)
    ultimately show ?case by(auto 4 3 dest: leq_antisym)
  qed
qed

lemma chain_iterates_above: 
  assumes a: "a \<in> Field leq"
  shows "iterates_above a \<in> Chains leq" (is "?C \<in> _")
proof (rule ChainsI)
  fix x y
  assume "x \<in> ?C" "y \<in> ?C"
  hence "x \<in> iterates_above y \<or> y \<in> iterates_above x" using a by(rule iterates_above_triangle)
  moreover from \<open>x \<in> ?C\<close> a have "x \<in> Field leq" by(rule iterates_above_Field)
  moreover from \<open>y \<in> ?C\<close> a have "y \<in> Field leq" by(rule iterates_above_Field)
  ultimately show "(x, y) \<in> leq \<or> (y, x) \<in> leq" by(auto dest: iterates_above_ge)
qed

lemma fixp_iterates_above: "a \<in> Field leq \<Longrightarrow> fixp_above a \<in> iterates_above a"
unfolding fixp_above_def by(rule iterates_above.Sup)(blast intro: chain_iterates_above)+

lemma fixp_above_Field: "a \<in> Field leq \<Longrightarrow> fixp_above a \<in> Field leq"
using fixp_iterates_above by(rule iterates_above_Field)

lemma fixp_above_unfold:
  assumes a: "a \<in> Field leq"
  shows "fixp_above a = f (fixp_above a)" (is "?a = f ?a")
proof(rule leq_antisym)
  show "(?a, f ?a) \<in> leq" using fixp_above_Field[OF a] by(rule increasing)
  
  have "f ?a \<in> iterates_above a" using fixp_iterates_above[OF a] by(rule iterates_above.step)
  with chain_iterates_above[OF a] show "(f ?a, ?a) \<in> leq" unfolding fixp_above_def by(rule lub_upper)
qed

end

lemma fixp_induct [case_names adm closed base step]:
  assumes adm: "ccpo.admissible lub (\<lambda>x y. (x, y) \<in> leq) P"
  and a: "a \<in> Field leq"
  and base: "P a"
  and step: "\<And>x. P x \<Longrightarrow> P (f x)"
  shows "P (fixp_above a)"
using adm chain_iterates_above[OF a] unfolding fixp_above_def in_Chains_conv_chain
proof(rule ccpo.admissibleD)
  have "a \<in> iterates_above a" ..
  then show "iterates_above a \<noteq> {}" by(auto)
  show "P x" if "x \<in> iterates_above a" for x using that
    by induction(auto intro: base step simp add: in_Chains_conv_chain dest: ccpo.admissibleD[OF adm])
qed

end

end

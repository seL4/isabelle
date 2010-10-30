(* Title:    HOL/Complete_Partial_Order.thy
   Author:   Brian Huffman, Portland State University
   Author:   Alexander Krauss, TU Muenchen
*)

header {* Chain-complete partial orders and their fixpoints *}

theory Complete_Partial_Order
imports Product_Type
begin

subsection {* Monotone functions *}

text {* Dictionary-passing version of @{const Orderings.mono}. *}

definition monotone :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where "monotone orda ordb f \<longleftrightarrow> (\<forall>x y. orda x y \<longrightarrow> ordb (f x) (f y))"

lemma monotoneI[intro?]: "(\<And>x y. orda x y \<Longrightarrow> ordb (f x) (f y))
 \<Longrightarrow> monotone orda ordb f"
unfolding monotone_def by iprover

lemma monotoneD[dest?]: "monotone orda ordb f \<Longrightarrow> orda x y \<Longrightarrow> ordb (f x) (f y)"
unfolding monotone_def by iprover


subsection {* Chains *}

text {* A chain is a totally-ordered set. Chains are parameterized over
  the order for maximal flexibility, since type classes are not enough.
*}

definition
  chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "chain ord S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. ord x y \<or> ord y x)"

lemma chainI:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> ord x y \<or> ord y x"
  shows "chain ord S"
using assms unfolding chain_def by fast

lemma chainD:
  assumes "chain ord S" and "x \<in> S" and "y \<in> S"
  shows "ord x y \<or> ord y x"
using assms unfolding chain_def by fast

lemma chainE:
  assumes "chain ord S" and "x \<in> S" and "y \<in> S"
  obtains "ord x y" | "ord y x"
using assms unfolding chain_def by fast

subsection {* Chain-complete partial orders *}

text {*
  A ccpo has a least upper bound for any chain.  In particular, the
  empty set is a chain, so every ccpo must have a bottom element.
*}

class ccpo = order +
  fixes lub :: "'a set \<Rightarrow> 'a"
  assumes lub_upper: "chain (op \<le>) A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> lub A"
  assumes lub_least: "chain (op \<le>) A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> lub A \<le> z"
begin

subsection {* Transfinite iteration of a function *}

inductive_set iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set"
for f :: "'a \<Rightarrow> 'a"
where
  step: "x \<in> iterates f \<Longrightarrow> f x \<in> iterates f"
| lub: "chain (op \<le>) M \<Longrightarrow> \<forall>x\<in>M. x \<in> iterates f \<Longrightarrow> lub M \<in> iterates f"

lemma iterates_le_f:
  "x \<in> iterates f \<Longrightarrow> monotone (op \<le>) (op \<le>) f \<Longrightarrow> x \<le> f x"
by (induct x rule: iterates.induct)
  (force dest: monotoneD intro!: lub_upper lub_least)+

lemma chain_iterates:
  assumes f: "monotone (op \<le>) (op \<le>) f"
  shows "chain (op \<le>) (iterates f)" (is "chain _ ?C")
proof (rule chainI)
  fix x y assume "x \<in> ?C" "y \<in> ?C"
  then show "x \<le> y \<or> y \<le> x"
  proof (induct x arbitrary: y rule: iterates.induct)
    fix x y assume y: "y \<in> ?C"
    and IH: "\<And>z. z \<in> ?C \<Longrightarrow> x \<le> z \<or> z \<le> x"
    from y show "f x \<le> y \<or> y \<le> f x"
    proof (induct y rule: iterates.induct)
      case (step y) with IH f show ?case by (auto dest: monotoneD)
    next
      case (lub M)
      then have chM: "chain (op \<le>) M"
        and IH': "\<And>z. z \<in> M \<Longrightarrow> f x \<le> z \<or> z \<le> f x" by auto
      show "f x \<le> lub M \<or> lub M \<le> f x"
      proof (cases "\<exists>z\<in>M. f x \<le> z")
        case True then have "f x \<le> lub M"
          apply rule
          apply (erule order_trans)
          by (rule lub_upper[OF chM])
        thus ?thesis ..
      next
        case False with IH'
        show ?thesis by (auto intro: lub_least[OF chM])
      qed
    qed
  next
    case (lub M y)
    show ?case
    proof (cases "\<exists>x\<in>M. y \<le> x")
      case True then have "y \<le> lub M"
        apply rule
        apply (erule order_trans)
        by (rule lub_upper[OF lub(1)])
      thus ?thesis ..
    next
      case False with lub
      show ?thesis by (auto intro: lub_least)
    qed
  qed
qed

subsection {* Fixpoint combinator *}

definition
  fixp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "fixp f = lub (iterates f)"

lemma iterates_fixp:
  assumes f: "monotone (op \<le>) (op \<le>) f" shows "fixp f \<in> iterates f"
unfolding fixp_def
by (simp add: iterates.lub chain_iterates f)

lemma fixp_unfold:
  assumes f: "monotone (op \<le>) (op \<le>) f"
  shows "fixp f = f (fixp f)"
proof (rule antisym)
  show "fixp f \<le> f (fixp f)"
    by (intro iterates_le_f iterates_fixp f)
  have "f (fixp f) \<le> lub (iterates f)"
    by (intro lub_upper chain_iterates f iterates.step iterates_fixp)
  thus "f (fixp f) \<le> fixp f"
    unfolding fixp_def .
qed

lemma fixp_lowerbound:
  assumes f: "monotone (op \<le>) (op \<le>) f" and z: "f z \<le> z" shows "fixp f \<le> z"
unfolding fixp_def
proof (rule lub_least[OF chain_iterates[OF f]])
  fix x assume "x \<in> iterates f"
  thus "x \<le> z"
  proof (induct x rule: iterates.induct)
    fix x assume "x \<le> z" with f have "f x \<le> f z" by (rule monotoneD)
    also note z finally show "f x \<le> z" .
  qed (auto intro: lub_least)
qed


subsection {* Fixpoint induction *}

definition
  admissible :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "admissible P = (\<forall>A. chain (op \<le>) A \<longrightarrow> (\<forall>x\<in>A. P x) \<longrightarrow> P (lub A))"

lemma admissibleI:
  assumes "\<And>A. chain (op \<le>) A \<Longrightarrow> \<forall>x\<in>A. P x \<Longrightarrow> P (lub A)"
  shows "admissible P"
using assms unfolding admissible_def by fast

lemma admissibleD:
  assumes "admissible P"
  assumes "chain (op \<le>) A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> P x"
  shows "P (lub A)"
using assms by (auto simp: admissible_def)

lemma fixp_induct:
  assumes adm: "admissible P"
  assumes mono: "monotone (op \<le>) (op \<le>) f"
  assumes step: "\<And>x. P x \<Longrightarrow> P (f x)"
  shows "P (fixp f)"
unfolding fixp_def using adm chain_iterates[OF mono]
proof (rule admissibleD)
  fix x assume "x \<in> iterates f"
  thus "P x"
    by (induct rule: iterates.induct)
      (auto intro: step admissibleD adm)
qed

lemma admissible_True: "admissible (\<lambda>x. True)"
unfolding admissible_def by simp

lemma admissible_False: "\<not> admissible (\<lambda>x. False)"
unfolding admissible_def chain_def by simp

lemma admissible_const: "admissible (\<lambda>x. t) = t"
by (cases t, simp_all add: admissible_True admissible_False)

lemma admissible_conj:
  assumes "admissible (\<lambda>x. P x)"
  assumes "admissible (\<lambda>x. Q x)"
  shows "admissible (\<lambda>x. P x \<and> Q x)"
using assms unfolding admissible_def by simp

lemma admissible_all:
  assumes "\<And>y. admissible (\<lambda>x. P x y)"
  shows "admissible (\<lambda>x. \<forall>y. P x y)"
using assms unfolding admissible_def by fast

lemma admissible_ball:
  assumes "\<And>y. y \<in> A \<Longrightarrow> admissible (\<lambda>x. P x y)"
  shows "admissible (\<lambda>x. \<forall>y\<in>A. P x y)"
using assms unfolding admissible_def by fast

lemma chain_compr: "chain (op \<le>) A \<Longrightarrow> chain (op \<le>) {x \<in> A. P x}"
unfolding chain_def by fast

lemma admissible_disj_lemma:
  assumes A: "chain (op \<le>)A"
  assumes P: "\<forall>x\<in>A. \<exists>y\<in>A. x \<le> y \<and> P y"
  shows "lub A = lub {x \<in> A. P x}"
proof (rule antisym)
  have *: "chain (op \<le>) {x \<in> A. P x}"
    by (rule chain_compr [OF A])
  show "lub A \<le> lub {x \<in> A. P x}"
    apply (rule lub_least [OF A])
    apply (drule P [rule_format], clarify)
    apply (erule order_trans)
    apply (simp add: lub_upper [OF *])
    done
  show "lub {x \<in> A. P x} \<le> lub A"
    apply (rule lub_least [OF *])
    apply clarify
    apply (simp add: lub_upper [OF A])
    done
qed

lemma admissible_disj:
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes P: "admissible (\<lambda>x. P x)"
  assumes Q: "admissible (\<lambda>x. Q x)"
  shows "admissible (\<lambda>x. P x \<or> Q x)"
proof (rule admissibleI)
  fix A :: "'a set" assume A: "chain (op \<le>) A"
  assume "\<forall>x\<in>A. P x \<or> Q x"
  hence "(\<forall>x\<in>A. \<exists>y\<in>A. x \<le> y \<and> P y) \<or> (\<forall>x\<in>A. \<exists>y\<in>A. x \<le> y \<and> Q y)"
    using chainD[OF A] by blast
  hence "lub A = lub {x \<in> A. P x} \<or> lub A = lub {x \<in> A. Q x}"
    using admissible_disj_lemma [OF A] by fast
  thus "P (lub A) \<or> Q (lub A)"
    apply (rule disjE, simp_all)
    apply (rule disjI1, rule admissibleD [OF P chain_compr [OF A]], simp)
    apply (rule disjI2, rule admissibleD [OF Q chain_compr [OF A]], simp)
    done
qed

end

hide_const (open) lub iterates fixp admissible

end

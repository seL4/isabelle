(*  Title:      HOL/Complete_Partial_Order.thy
    Author:     Brian Huffman, Portland State University
    Author:     Alexander Krauss, TU Muenchen
*)

section \<open>Chain-complete partial orders and their fixpoints\<close>

theory Complete_Partial_Order
  imports Product_Type
begin

subsection \<open>Monotone functions\<close>

text \<open>Dictionary-passing version of \<^const>\<open>Orderings.mono\<close>.\<close>

definition monotone :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "monotone orda ordb f \<longleftrightarrow> (\<forall>x y. orda x y \<longrightarrow> ordb (f x) (f y))"

lemma monotoneI[intro?]: "(\<And>x y. orda x y \<Longrightarrow> ordb (f x) (f y)) \<Longrightarrow> monotone orda ordb f"
  unfolding monotone_def by iprover

lemma monotoneD[dest?]: "monotone orda ordb f \<Longrightarrow> orda x y \<Longrightarrow> ordb (f x) (f y)"
  unfolding monotone_def by iprover


subsection \<open>Chains\<close>

text \<open>
  A chain is a totally-ordered set. Chains are parameterized over
  the order for maximal flexibility, since type classes are not enough.
\<close>

definition chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "chain ord S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. ord x y \<or> ord y x)"

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

lemma chain_empty: "chain ord {}"
  by (simp add: chain_def)

lemma chain_equality: "chain (=) A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x = y)"
  by (auto simp add: chain_def)

lemma chain_subset: "chain ord A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> chain ord B"
  by (rule chainI) (blast dest: chainD)

lemma chain_imageI:
  assumes chain: "chain le_a Y"
    and mono: "\<And>x y. x \<in> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> le_a x y \<Longrightarrow> le_b (f x) (f y)"
  shows "chain le_b (f ` Y)"
  by (blast intro: chainI dest: chainD[OF chain] mono)


subsection \<open>Chain-complete partial orders\<close>

text \<open>
  A \<open>ccpo\<close> has a least upper bound for any chain.  In particular, the
  empty set is a chain, so every \<open>ccpo\<close> must have a bottom element.
\<close>

class ccpo = order + Sup +
  assumes ccpo_Sup_upper: "chain (\<le>) A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> Sup A"
  assumes ccpo_Sup_least: "chain (\<le>) A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
begin

lemma chain_singleton: "Complete_Partial_Order.chain (\<le>) {x}"
  by (rule chainI) simp

lemma ccpo_Sup_singleton [simp]: "\<Squnion>{x} = x"
  by (rule order.antisym) (auto intro: ccpo_Sup_least ccpo_Sup_upper simp add: chain_singleton)


subsection \<open>Transfinite iteration of a function\<close>

context notes [[inductive_internals]]
begin

inductive_set iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set"
  for f :: "'a \<Rightarrow> 'a"
  where
    step: "x \<in> iterates f \<Longrightarrow> f x \<in> iterates f"
  | Sup: "chain (\<le>) M \<Longrightarrow> \<forall>x\<in>M. x \<in> iterates f \<Longrightarrow> Sup M \<in> iterates f"

end

lemma iterates_le_f: "x \<in> iterates f \<Longrightarrow> monotone (\<le>) (\<le>) f \<Longrightarrow> x \<le> f x"
  by (induct x rule: iterates.induct)
    (force dest: monotoneD intro!: ccpo_Sup_upper ccpo_Sup_least)+

lemma chain_iterates:
  assumes f: "monotone (\<le>) (\<le>) f"
  shows "chain (\<le>) (iterates f)" (is "chain _ ?C")
proof (rule chainI)
  fix x y
  assume "x \<in> ?C" "y \<in> ?C"
  then show "x \<le> y \<or> y \<le> x"
  proof (induct x arbitrary: y rule: iterates.induct)
    fix x y
    assume y: "y \<in> ?C"
      and IH: "\<And>z. z \<in> ?C \<Longrightarrow> x \<le> z \<or> z \<le> x"
    from y show "f x \<le> y \<or> y \<le> f x"
    proof (induct y rule: iterates.induct)
      case (step y)
      with IH f show ?case by (auto dest: monotoneD)
    next
      case (Sup M)
      then have chM: "chain (\<le>) M"
        and IH': "\<And>z. z \<in> M \<Longrightarrow> f x \<le> z \<or> z \<le> f x" by auto
      show "f x \<le> Sup M \<or> Sup M \<le> f x"
      proof (cases "\<exists>z\<in>M. f x \<le> z")
        case True
        then have "f x \<le> Sup M"
          by (blast intro: ccpo_Sup_upper[OF chM] order_trans)
        then show ?thesis ..
      next
        case False
        with IH' show ?thesis
          by (auto intro: ccpo_Sup_least[OF chM])
      qed
    qed
  next
    case (Sup M y)
    show ?case
    proof (cases "\<exists>x\<in>M. y \<le> x")
      case True
      then have "y \<le> Sup M"
        by (blast intro: ccpo_Sup_upper[OF Sup(1)] order_trans)
      then show ?thesis ..
    next
      case False with Sup
      show ?thesis by (auto intro: ccpo_Sup_least)
    qed
  qed
qed

lemma bot_in_iterates: "Sup {} \<in> iterates f"
  by (auto intro: iterates.Sup simp add: chain_empty)


subsection \<open>Fixpoint combinator\<close>

definition fixp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "fixp f = Sup (iterates f)"

lemma iterates_fixp:
  assumes f: "monotone (\<le>) (\<le>) f"
  shows "fixp f \<in> iterates f"
  unfolding fixp_def
  by (simp add: iterates.Sup chain_iterates f)

lemma fixp_unfold:
  assumes f: "monotone (\<le>) (\<le>) f"
  shows "fixp f = f (fixp f)"
proof (rule order.antisym)
  show "fixp f \<le> f (fixp f)"
    by (intro iterates_le_f iterates_fixp f)
  have "f (fixp f) \<le> Sup (iterates f)"
    by (intro ccpo_Sup_upper chain_iterates f iterates.step iterates_fixp)
  then show "f (fixp f) \<le> fixp f"
    by (simp only: fixp_def)
qed

lemma fixp_lowerbound:
  assumes f: "monotone (\<le>) (\<le>) f"
    and z: "f z \<le> z"
  shows "fixp f \<le> z"
  unfolding fixp_def
proof (rule ccpo_Sup_least[OF chain_iterates[OF f]])
  fix x
  assume "x \<in> iterates f"
  then show "x \<le> z"
  proof (induct x rule: iterates.induct)
    case (step x)
    from f \<open>x \<le> z\<close> have "f x \<le> f z" by (rule monotoneD)
    also note z
    finally show "f x \<le> z" .
  next
    case (Sup M)
    then show ?case
      by (auto intro: ccpo_Sup_least)
  qed
qed

end


subsection \<open>Fixpoint induction\<close>

setup \<open>Sign.map_naming (Name_Space.mandatory_path "ccpo")\<close>

definition admissible :: "('a set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "admissible lub ord P \<longleftrightarrow> (\<forall>A. chain ord A \<longrightarrow> A \<noteq> {} \<longrightarrow> (\<forall>x\<in>A. P x) \<longrightarrow> P (lub A))"

lemma admissibleI:
  assumes "\<And>A. chain ord A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<forall>x\<in>A. P x \<Longrightarrow> P (lub A)"
  shows "ccpo.admissible lub ord P"
  using assms unfolding ccpo.admissible_def by fast

lemma admissibleD:
  assumes "ccpo.admissible lub ord P"
  assumes "chain ord A"
  assumes "A \<noteq> {}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> P x"
  shows "P (lub A)"
  using assms by (auto simp: ccpo.admissible_def)

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

lemma (in ccpo) fixp_induct:
  assumes adm: "ccpo.admissible Sup (\<le>) P"
  assumes mono: "monotone (\<le>) (\<le>) f"
  assumes bot: "P (Sup {})"
  assumes step: "\<And>x. P x \<Longrightarrow> P (f x)"
  shows "P (fixp f)"
  unfolding fixp_def
  using adm chain_iterates[OF mono]
proof (rule ccpo.admissibleD)
  show "iterates f \<noteq> {}"
    using bot_in_iterates by auto
next
  fix x
  assume "x \<in> iterates f"
  then show "P x"
  proof (induct rule: iterates.induct)
    case prems: (step x)
    from this(2) show ?case by (rule step)
  next
    case (Sup M)
    then show ?case by (cases "M = {}") (auto intro: step bot ccpo.admissibleD adm)
  qed
qed

lemma admissible_True: "ccpo.admissible lub ord (\<lambda>x. True)"
  unfolding ccpo.admissible_def by simp

(*lemma admissible_False: "\<not> ccpo.admissible lub ord (\<lambda>x. False)"
unfolding ccpo.admissible_def chain_def by simp
*)
lemma admissible_const: "ccpo.admissible lub ord (\<lambda>x. t)"
  by (auto intro: ccpo.admissibleI)

lemma admissible_conj:
  assumes "ccpo.admissible lub ord (\<lambda>x. P x)"
  assumes "ccpo.admissible lub ord (\<lambda>x. Q x)"
  shows "ccpo.admissible lub ord (\<lambda>x. P x \<and> Q x)"
  using assms unfolding ccpo.admissible_def by simp

lemma admissible_all:
  assumes "\<And>y. ccpo.admissible lub ord (\<lambda>x. P x y)"
  shows "ccpo.admissible lub ord (\<lambda>x. \<forall>y. P x y)"
  using assms unfolding ccpo.admissible_def by fast

lemma admissible_ball:
  assumes "\<And>y. y \<in> A \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. P x y)"
  shows "ccpo.admissible lub ord (\<lambda>x. \<forall>y\<in>A. P x y)"
  using assms unfolding ccpo.admissible_def by fast

lemma chain_compr: "chain ord A \<Longrightarrow> chain ord {x \<in> A. P x}"
  unfolding chain_def by fast

context ccpo
begin

lemma admissible_disj:
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes P: "ccpo.admissible Sup (\<le>) (\<lambda>x. P x)"
  assumes Q: "ccpo.admissible Sup (\<le>) (\<lambda>x. Q x)"
  shows "ccpo.admissible Sup (\<le>) (\<lambda>x. P x \<or> Q x)"
proof (rule ccpo.admissibleI)
  fix A :: "'a set"
  assume chain: "chain (\<le>) A"
  assume A: "A \<noteq> {}" and P_Q: "\<forall>x\<in>A. P x \<or> Q x"
  have "(\<exists>x\<in>A. P x) \<and> (\<forall>x\<in>A. \<exists>y\<in>A. x \<le> y \<and> P y) \<or> (\<exists>x\<in>A. Q x) \<and> (\<forall>x\<in>A. \<exists>y\<in>A. x \<le> y \<and> Q y)"
    (is "?P \<or> ?Q" is "?P1 \<and> ?P2 \<or> _")
  proof (rule disjCI)
    assume "\<not> ?Q"
    then consider "\<forall>x\<in>A. \<not> Q x" | a where "a \<in> A" "\<forall>y\<in>A. a \<le> y \<longrightarrow> \<not> Q y"
      by blast
    then show ?P
    proof cases
      case 1
      with P_Q have "\<forall>x\<in>A. P x" by blast
      with A show ?P by blast
    next
      case 2
      note a = \<open>a \<in> A\<close>
      show ?P
      proof
        from P_Q 2 have *: "\<forall>y\<in>A. a \<le> y \<longrightarrow> P y" by blast
        with a have "P a" by blast
        with a show ?P1 by blast
        show ?P2
        proof
          fix x
          assume x: "x \<in> A"
          with chain a show "\<exists>y\<in>A. x \<le> y \<and> P y"
          proof (rule chainE)
            assume le: "a \<le> x"
            with * a x have "P x" by blast
            with x le show ?thesis by blast
          next
            assume "a \<ge> x"
            with a \<open>P a\<close> show ?thesis by blast
          qed
        qed
      qed
    qed
  qed
  moreover
  have "Sup A = Sup {x \<in> A. P x}" if "\<And>x. x\<in>A \<Longrightarrow> \<exists>y\<in>A. x \<le> y \<and> P y" for P
  proof (rule order.antisym)
    have chain_P: "chain (\<le>) {x \<in> A. P x}"
      by (rule chain_compr [OF chain])
    show "Sup A \<le> Sup {x \<in> A. P x}"
    proof (rule ccpo_Sup_least [OF chain])
      show "\<And>x. x \<in> A \<Longrightarrow> x \<le> \<Squnion> {x \<in> A. P x}"
          by (blast intro: ccpo_Sup_upper[OF chain_P] order_trans dest: that)
      qed
    show "Sup {x \<in> A. P x} \<le> Sup A"
      apply (rule ccpo_Sup_least [OF chain_P])
      apply (simp add: ccpo_Sup_upper [OF chain])
      done
  qed
  ultimately
  consider "\<exists>x. x \<in> A \<and> P x" "Sup A = Sup {x \<in> A. P x}"
    | "\<exists>x. x \<in> A \<and> Q x" "Sup A = Sup {x \<in> A. Q x}"
    by blast
  then show "P (Sup A) \<or> Q (Sup A)"
  proof cases
    case 1
    then show ?thesis
      using ccpo.admissibleD [OF P chain_compr [OF chain]] by force
  next
    case 2
    then show ?thesis 
      using ccpo.admissibleD [OF Q chain_compr [OF chain]] by force
  qed
qed

end

instance complete_lattice \<subseteq> ccpo
  by standard (fast intro: Sup_upper Sup_least)+

lemma lfp_eq_fixp:
  assumes mono: "mono f"
  shows "lfp f = fixp f"
proof (rule order.antisym)
  from mono have f': "monotone (\<le>) (\<le>) f"
    unfolding mono_def monotone_def .
  show "lfp f \<le> fixp f"
    by (rule lfp_lowerbound, subst fixp_unfold [OF f'], rule order_refl)
  show "fixp f \<le> lfp f"
    by (rule fixp_lowerbound [OF f']) (simp add: lfp_fixpoint [OF mono])
qed

hide_const (open) iterates fixp

end

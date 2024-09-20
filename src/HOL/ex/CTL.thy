(*  Title:      HOL/ex/CTL.thy
    Author:     Gertrud Bauer
*)

section \<open>CTL formulae\<close>

theory CTL
imports Main
begin

text \<open>
  We formalize basic concepts of Computational Tree Logic (CTL) \<^cite>\<open>"McMillan-PhDThesis"\<close> within the simply-typed
  set theory of HOL.

  By using the common technique of ``shallow embedding'', a CTL formula is
  identified with the corresponding set of states where it holds.
  Consequently, CTL operations such as negation, conjunction, disjunction
  simply become complement, intersection, union of sets. We only require a
  separate operation for implication, as point-wise inclusion is usually not
  encountered in plain set-theory.
\<close>

lemmas [intro!] = Int_greatest Un_upper2 Un_upper1 Int_lower1 Int_lower2

type_synonym 'a ctl = "'a set"

definition imp :: "'a ctl \<Rightarrow> 'a ctl \<Rightarrow> 'a ctl"  (infixr \<open>\<rightarrow>\<close> 75)
  where "p \<rightarrow> q = - p \<union> q"

lemma [intro!]: "p \<inter> p \<rightarrow> q \<subseteq> q" unfolding imp_def by auto
lemma [intro!]: "p \<subseteq> (q \<rightarrow> p)" unfolding imp_def by rule


text \<open>
  \<^smallskip>
  The CTL path operators are more interesting; they are based on an arbitrary,
  but fixed model \<open>\<M>\<close>, which is simply a transition relation over states
  \<^typ>\<open>'a\<close>.
\<close>

axiomatization \<M> :: "('a \<times> 'a) set"

text \<open>
  The operators \<open>\<^bold>E\<^bold>X\<close>, \<open>\<^bold>E\<^bold>F\<close>, \<open>\<^bold>E\<^bold>G\<close> are taken as primitives, while \<open>\<^bold>A\<^bold>X\<close>,
  \<open>\<^bold>A\<^bold>F\<close>, \<open>\<^bold>A\<^bold>G\<close> are defined as derived ones. The formula \<open>\<^bold>E\<^bold>X p\<close> holds in a
  state \<open>s\<close>, iff there is a successor state \<open>s'\<close> (with respect to the model
  \<open>\<M>\<close>), such that \<open>p\<close> holds in \<open>s'\<close>. The formula \<open>\<^bold>E\<^bold>F p\<close> holds in a state
  \<open>s\<close>, iff there is a path in \<open>\<M>\<close>, starting from \<open>s\<close>, such that there exists a
  state \<open>s'\<close> on the path, such that \<open>p\<close> holds in \<open>s'\<close>. The formula \<open>\<^bold>E\<^bold>G p\<close>
  holds in a state \<open>s\<close>, iff there is a path, starting from \<open>s\<close>, such that for
  all states \<open>s'\<close> on the path, \<open>p\<close> holds in \<open>s'\<close>. It is easy to see that \<open>\<^bold>E\<^bold>F
  p\<close> and \<open>\<^bold>E\<^bold>G p\<close> may be expressed using least and greatest fixed points
  \<^cite>\<open>"McMillan-PhDThesis"\<close>.
\<close>

definition EX  (\<open>\<^bold>E\<^bold>X _\<close> [80] 90)
  where [simp]: "\<^bold>E\<^bold>X p = {s. \<exists>s'. (s, s') \<in> \<M> \<and> s' \<in> p}"

definition EF (\<open>\<^bold>E\<^bold>F _\<close> [80] 90)
  where [simp]: "\<^bold>E\<^bold>F p = lfp (\<lambda>s. p \<union> \<^bold>E\<^bold>X s)"

definition EG (\<open>\<^bold>E\<^bold>G _\<close> [80] 90)
  where [simp]: "\<^bold>E\<^bold>G p = gfp (\<lambda>s. p \<inter> \<^bold>E\<^bold>X s)"

text \<open>
  \<open>\<^bold>A\<^bold>X\<close>, \<open>\<^bold>A\<^bold>F\<close> and \<open>\<^bold>A\<^bold>G\<close> are now defined dually in terms of \<open>\<^bold>E\<^bold>X\<close>,
  \<open>\<^bold>E\<^bold>F\<close> and \<open>\<^bold>E\<^bold>G\<close>.
\<close>

definition AX  (\<open>\<^bold>A\<^bold>X _\<close> [80] 90)
  where [simp]: "\<^bold>A\<^bold>X p = - \<^bold>E\<^bold>X - p"
definition AF  (\<open>\<^bold>A\<^bold>F _\<close> [80] 90)
  where [simp]: "\<^bold>A\<^bold>F p = - \<^bold>E\<^bold>G - p"
definition AG  (\<open>\<^bold>A\<^bold>G _\<close> [80] 90)
  where [simp]: "\<^bold>A\<^bold>G p = - \<^bold>E\<^bold>F - p"


subsection \<open>Basic fixed point properties\<close>

text \<open>
  First of all, we use the de-Morgan property of fixed points.
\<close>

lemma lfp_gfp: "lfp f = - gfp (\<lambda>s::'a set. - (f (- s)))"
proof
  show "lfp f \<subseteq> - gfp (\<lambda>s. - f (- s))"
  proof
    show "x \<in> - gfp (\<lambda>s. - f (- s))" if l: "x \<in> lfp f" for x
    proof
      assume "x \<in> gfp (\<lambda>s. - f (- s))"
      then obtain u where "x \<in> u" and "u \<subseteq> - f (- u)"
        by (auto simp add: gfp_def)
      then have "f (- u) \<subseteq> - u" by auto
      then have "lfp f \<subseteq> - u" by (rule lfp_lowerbound)
      from l and this have "x \<notin> u" by auto
      with \<open>x \<in> u\<close> show False by contradiction
    qed
  qed
  show "- gfp (\<lambda>s. - f (- s)) \<subseteq> lfp f"
  proof (rule lfp_greatest)
    fix u
    assume "f u \<subseteq> u"
    then have "- u \<subseteq> - f u" by auto
    then have "- u \<subseteq> - f (- (- u))" by simp
    then have "- u \<subseteq> gfp (\<lambda>s. - f (- s))" by (rule gfp_upperbound)
    then show "- gfp (\<lambda>s. - f (- s)) \<subseteq> u" by auto
  qed
qed

lemma lfp_gfp': "- lfp f = gfp (\<lambda>s::'a set. - (f (- s)))"
  by (simp add: lfp_gfp)

lemma gfp_lfp': "- gfp f = lfp (\<lambda>s::'a set. - (f (- s)))"
  by (simp add: lfp_gfp)

text \<open>
  In order to give dual fixed point representations of \<^term>\<open>\<^bold>A\<^bold>F p\<close> and
  \<^term>\<open>\<^bold>A\<^bold>G p\<close>:
\<close>

lemma AF_lfp: "\<^bold>A\<^bold>F p = lfp (\<lambda>s. p \<union> \<^bold>A\<^bold>X s)"
  by (simp add: lfp_gfp)

lemma AG_gfp: "\<^bold>A\<^bold>G p = gfp (\<lambda>s. p \<inter> \<^bold>A\<^bold>X s)"
  by (simp add: lfp_gfp)

lemma EF_fp: "\<^bold>E\<^bold>F p = p \<union> \<^bold>E\<^bold>X \<^bold>E\<^bold>F p"
proof -
  have "mono (\<lambda>s. p \<union> \<^bold>E\<^bold>X s)" by rule auto
  then show ?thesis by (simp only: EF_def) (rule lfp_unfold)
qed

lemma AF_fp: "\<^bold>A\<^bold>F p = p \<union> \<^bold>A\<^bold>X \<^bold>A\<^bold>F p"
proof -
  have "mono (\<lambda>s. p \<union> \<^bold>A\<^bold>X s)" by rule auto
  then show ?thesis by (simp only: AF_lfp) (rule lfp_unfold)
qed

lemma EG_fp: "\<^bold>E\<^bold>G p = p \<inter> \<^bold>E\<^bold>X \<^bold>E\<^bold>G p"
proof -
  have "mono (\<lambda>s. p \<inter> \<^bold>E\<^bold>X s)" by rule auto
  then show ?thesis by (simp only: EG_def) (rule gfp_unfold)
qed

text \<open>
  From the greatest fixed point definition of \<^term>\<open>\<^bold>A\<^bold>G p\<close>, we derive as
  a consequence of the Knaster-Tarski theorem on the one hand that \<^term>\<open>\<^bold>A\<^bold>G p\<close> is a fixed point of the monotonic function
  \<^term>\<open>\<lambda>s. p \<inter> \<^bold>A\<^bold>X s\<close>.
\<close>

lemma AG_fp: "\<^bold>A\<^bold>G p = p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p"
proof -
  have "mono (\<lambda>s. p \<inter> \<^bold>A\<^bold>X s)" by rule auto
  then show ?thesis by (simp only: AG_gfp) (rule gfp_unfold)
qed

text \<open>
  This fact may be split up into two inequalities (merely using transitivity
  of \<open>\<subseteq>\<close>, which is an instance of the overloaded \<open>\<le>\<close> in Isabelle/HOL).
\<close>

lemma AG_fp_1: "\<^bold>A\<^bold>G p \<subseteq> p"
proof -
  note AG_fp also have "p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p \<subseteq> p" by auto
  finally show ?thesis .
qed

lemma AG_fp_2: "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p"
proof -
  note AG_fp also have "p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p" by auto
  finally show ?thesis .
qed

text \<open>
  On the other hand, we have from the Knaster-Tarski fixed point theorem that
  any other post-fixed point of \<^term>\<open>\<lambda>s. p \<inter> \<^bold>A\<^bold>X s\<close> is smaller than
  \<^term>\<open>\<^bold>A\<^bold>G p\<close>. A post-fixed point is a set of states \<open>q\<close> such that \<^term>\<open>q \<subseteq> p \<inter> \<^bold>A\<^bold>X q\<close>. This leads to the following co-induction principle for
  \<^term>\<open>\<^bold>A\<^bold>G p\<close>.
\<close>

lemma AG_I: "q \<subseteq> p \<inter> \<^bold>A\<^bold>X q \<Longrightarrow> q \<subseteq> \<^bold>A\<^bold>G p"
  by (simp only: AG_gfp) (rule gfp_upperbound)


subsection \<open>The tree induction principle \label{sec:calc-ctl-tree-induct}\<close>

text \<open>
  With the most basic facts available, we are now able to establish a few more
  interesting results, leading to the \<^emph>\<open>tree induction\<close> principle for \<open>\<^bold>A\<^bold>G\<close>
  (see below). We will use some elementary monotonicity and distributivity
  rules.
\<close>

lemma AX_int: "\<^bold>A\<^bold>X (p \<inter> q) = \<^bold>A\<^bold>X p \<inter> \<^bold>A\<^bold>X q" by auto
lemma AX_mono: "p \<subseteq> q \<Longrightarrow> \<^bold>A\<^bold>X p \<subseteq> \<^bold>A\<^bold>X q" by auto
lemma AG_mono: "p \<subseteq> q \<Longrightarrow> \<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G q"
  by (simp only: AG_gfp, rule gfp_mono) auto

text \<open>
  The formula \<^term>\<open>AG p\<close> implies \<^term>\<open>AX p\<close> (we use substitution of
  \<open>\<subseteq>\<close> with monotonicity).
\<close>

lemma AG_AX: "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X p"
proof -
  have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p" by (rule AG_fp_2)
  also have "\<^bold>A\<^bold>G p \<subseteq> p" by (rule AG_fp_1)
  moreover note AX_mono
  finally show ?thesis .
qed

text \<open>
  Furthermore we show idempotency of the \<open>\<^bold>A\<^bold>G\<close> operator. The proof is a good
  example of how accumulated facts may get used to feed a single rule step.
\<close>

lemma AG_AG: "\<^bold>A\<^bold>G \<^bold>A\<^bold>G p = \<^bold>A\<^bold>G p"
proof
  show "\<^bold>A\<^bold>G \<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G p" by (rule AG_fp_1)
next
  show "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G \<^bold>A\<^bold>G p"
  proof (rule AG_I)
    have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G p" ..
    moreover have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p" by (rule AG_fp_2)
    ultimately show "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G p" ..
  qed
qed

text \<open>
  \<^smallskip>
  We now give an alternative characterization of the \<open>\<^bold>A\<^bold>G\<close> operator, which
  describes the \<open>\<^bold>A\<^bold>G\<close> operator in an ``operational'' way by tree induction:
  In a state holds \<^term>\<open>AG p\<close> iff in that state holds \<open>p\<close>, and in all
  reachable states \<open>s\<close> follows from the fact that \<open>p\<close> holds in \<open>s\<close>, that \<open>p\<close>
  also holds in all successor states of \<open>s\<close>. We use the co-induction principle
  @{thm [source] AG_I} to establish this in a purely algebraic manner.
\<close>

theorem AG_induct: "p \<inter> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p) = \<^bold>A\<^bold>G p"
proof
  show "p \<inter> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p) \<subseteq> \<^bold>A\<^bold>G p"  (is "?lhs \<subseteq> _")
  proof (rule AG_I)
    show "?lhs \<subseteq> p \<inter> \<^bold>A\<^bold>X ?lhs"
    proof
      show "?lhs \<subseteq> p" ..
      show "?lhs \<subseteq> \<^bold>A\<^bold>X ?lhs"
      proof -
        {
          have "\<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p) \<subseteq> p \<rightarrow> \<^bold>A\<^bold>X p" by (rule AG_fp_1)
          also have "p \<inter> p \<rightarrow> \<^bold>A\<^bold>X p \<subseteq> \<^bold>A\<^bold>X p" ..
          finally have "?lhs \<subseteq> \<^bold>A\<^bold>X p" by auto
        }
        moreover
        {
          have "p \<inter> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p) \<subseteq> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p)" ..
          also have "\<dots> \<subseteq> \<^bold>A\<^bold>X \<dots>" by (rule AG_fp_2)
          finally have "?lhs \<subseteq> \<^bold>A\<^bold>X \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p)" .
        }
        ultimately have "?lhs \<subseteq> \<^bold>A\<^bold>X p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p)" ..
        also have "\<dots> = \<^bold>A\<^bold>X ?lhs" by (simp only: AX_int)
        finally show ?thesis .
      qed
    qed
  qed
next
  show "\<^bold>A\<^bold>G p \<subseteq> p \<inter> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p)"
  proof
    show "\<^bold>A\<^bold>G p \<subseteq> p" by (rule AG_fp_1)
    show "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p)"
    proof -
      have "\<^bold>A\<^bold>G p = \<^bold>A\<^bold>G \<^bold>A\<^bold>G p" by (simp only: AG_AG)
      also have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X p" by (rule AG_AX) moreover note AG_mono
      also have "\<^bold>A\<^bold>X p \<subseteq> (p \<rightarrow> \<^bold>A\<^bold>X p)" .. moreover note AG_mono
      finally show ?thesis .
    qed
  qed
qed


subsection \<open>An application of tree induction \label{sec:calc-ctl-commute}\<close>

text \<open>
  Further interesting properties of CTL expressions may be demonstrated with
  the help of tree induction; here we show that \<open>\<^bold>A\<^bold>X\<close> and \<open>\<^bold>A\<^bold>G\<close> commute.
\<close>

theorem AG_AX_commute: "\<^bold>A\<^bold>G \<^bold>A\<^bold>X p = \<^bold>A\<^bold>X \<^bold>A\<^bold>G p"
proof -
  have "\<^bold>A\<^bold>G \<^bold>A\<^bold>X p = \<^bold>A\<^bold>X p \<inter> \<^bold>A\<^bold>X \<^bold>A\<^bold>G \<^bold>A\<^bold>X p" by (rule AG_fp)
  also have "\<dots> = \<^bold>A\<^bold>X (p \<inter> \<^bold>A\<^bold>G \<^bold>A\<^bold>X p)" by (simp only: AX_int)
  also have "p \<inter> \<^bold>A\<^bold>G \<^bold>A\<^bold>X p = \<^bold>A\<^bold>G p"  (is "?lhs = _")
  proof
    have "\<^bold>A\<^bold>X p \<subseteq> p \<rightarrow> \<^bold>A\<^bold>X p" ..
    also have "p \<inter> \<^bold>A\<^bold>G (p \<rightarrow> \<^bold>A\<^bold>X p) = \<^bold>A\<^bold>G p" by (rule AG_induct)
    also note Int_mono AG_mono
    ultimately show "?lhs \<subseteq> \<^bold>A\<^bold>G p" by fast
  next
    have "\<^bold>A\<^bold>G p \<subseteq> p" by (rule AG_fp_1)
    moreover
    {
      have "\<^bold>A\<^bold>G p = \<^bold>A\<^bold>G \<^bold>A\<^bold>G p" by (simp only: AG_AG)
      also have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>X p" by (rule AG_AX)
      also note AG_mono
      ultimately have "\<^bold>A\<^bold>G p \<subseteq> \<^bold>A\<^bold>G \<^bold>A\<^bold>X p" .
    }
    ultimately show "\<^bold>A\<^bold>G p \<subseteq> ?lhs" ..
  qed
  finally show ?thesis .
qed

end

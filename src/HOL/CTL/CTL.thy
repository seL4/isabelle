
theory CTL = Main:

section {* CTL formulae *}

text {*
  \tweakskip We formalize basic concepts of Computational Tree Logic
  (CTL) \cite{McMillan-PhDThesis,McMillan-LectureNotes} within the
  simply-typed set theory of HOL.

  By using the common technique of ``shallow embedding'', a CTL
  formula is identified with the corresponding set of states where it
  holds.  Consequently, CTL operations such as negation, conjunction,
  disjunction simply become complement, intersection, union of sets.
  We only require a separate operation for implication, as point-wise
  inclusion is usually not encountered in plain set-theory.
*}

lemmas [intro!] = Int_greatest Un_upper2 Un_upper1 Int_lower1 Int_lower2

types 'a ctl = "'a set"
constdefs
  imp :: "'a ctl \<Rightarrow> 'a ctl \<Rightarrow> 'a ctl"    (infixr "\<rightarrow>" 75)
  "p \<rightarrow> q \<equiv> - p \<union> q"

lemma [intro!]: "p \<inter> p \<rightarrow> q \<subseteq> q" by (unfold imp_def) auto
lemma [intro!]: "p \<subseteq> (q \<rightarrow> p)" by (unfold imp_def) rule


text {*
  \smallskip The CTL path operators are more interesting; they are
  based on an arbitrary, but fixed model @{text \<M>}, which is simply
  a transition relation over states @{typ "'a"}.
*}

consts model :: "('a \<times> 'a) set"    ("\<M>")

text {*
  The operators @{text \<EX>}, @{text \<EF>}, @{text \<EG>} are taken
  as primitives, while @{text \<AX>}, @{text \<AF>}, @{text \<AG>} are
  defined as derived ones.  The formula @{text "\<EX> p"} holds in a
  state @{term s}, iff there is a successor state @{term s'} (with
  respect to the model @{term \<M>}), such that @{term p} holds in
  @{term s'}.  The formula @{text "\<EF> p"} holds in a state @{term
  s}, iff there is a path in @{text \<M>}, starting from @{term s},
  such that there exists a state @{term s'} on the path, such that
  @{term p} holds in @{term s'}.  The formula @{text "\<EG> p"} holds
  in a state @{term s}, iff there is a path, starting from @{term s},
  such that for all states @{term s'} on the path, @{term p} holds in
  @{term s'}.  It is easy to see that @{text "\<EF> p"} and @{text
  "\<EG> p"} may be expressed using least and greatest fixed points
  \cite{McMillan-PhDThesis}.
*}

constdefs
  EX :: "'a ctl \<Rightarrow> 'a ctl"    ("\<EX> _" [80] 90)    "\<EX> p \<equiv> {s. \<exists>s'. (s, s') \<in> \<M> \<and> s' \<in> p}"
  EF :: "'a ctl \<Rightarrow> 'a ctl"    ("\<EF> _" [80] 90)    "\<EF> p \<equiv> lfp (\<lambda>s. p \<union> \<EX> s)"
  EG :: "'a ctl \<Rightarrow> 'a ctl"    ("\<EG> _" [80] 90)    "\<EG> p \<equiv> gfp (\<lambda>s. p \<inter> \<EX> s)"

text {*
  @{text "\<AX>"}, @{text "\<AF>"} and @{text "\<AG>"} are now defined
  dually in terms of @{text "\<EX>"}, @{text "\<EF>"} and @{text
  "\<EG>"}.
*}

constdefs
  AX :: "'a ctl \<Rightarrow> 'a ctl"    ("\<AX> _" [80] 90)    "\<AX> p \<equiv> - \<EX> - p"
  AF :: "'a ctl \<Rightarrow> 'a ctl"    ("\<AF> _" [80] 90)    "\<AF> p \<equiv> - \<EG> - p"
  AG :: "'a ctl \<Rightarrow> 'a ctl"    ("\<AG> _" [80] 90)    "\<AG> p \<equiv> - \<EF> - p"

lemmas [simp] = EX_def EG_def AX_def EF_def AF_def AG_def


section {* Basic fixed point properties *}

text {*
  \tweakskip First of all, we use the de-Morgan property of fixed
  points
*}

lemma lfp_gfp: "lfp f = - gfp (\<lambda>s . - (f (- s)))"
proof
  show "lfp f \<subseteq> - gfp (\<lambda>s. - f (- s))"
  proof
    fix x assume l: "x \<in> lfp f"
    show "x \<in> - gfp (\<lambda>s. - f (- s))"
    proof
      assume "x \<in> gfp (\<lambda>s. - f (- s))"
      then obtain u where "x \<in> u" and "u \<subseteq> - f (- u)" by (unfold gfp_def) auto
      then have "f (- u) \<subseteq> - u" by auto
      then have "lfp f \<subseteq> - u" by (rule lfp_lowerbound)
      from l and this have "x \<notin> u" by auto
      then show False by contradiction
    qed
  qed
  show "- gfp (\<lambda>s. - f (- s)) \<subseteq> lfp f"
  proof (rule lfp_greatest)
    fix u assume "f u \<subseteq> u"
    then have "- u \<subseteq> - f u" by auto
    then have "- u \<subseteq> - f (- (- u))" by simp
    then have "- u \<subseteq> gfp (\<lambda>s. - f (- s))" by (rule gfp_upperbound)
    then show "- gfp (\<lambda>s. - f (- s)) \<subseteq> u" by auto
  qed
qed

lemma lfp_gfp': "- lfp f = gfp (\<lambda>s. - (f (- s)))"
  by (simp add: lfp_gfp)

lemma gfp_lfp': "- gfp f = lfp (\<lambda>s. - (f (- s)))"
  by (simp add: lfp_gfp)

text {*
  in order to give dual fixed point representations of @{term "AF p"}
  and @{term "AG p"}:
*}

lemma AF_lfp: "\<AF> p = lfp (\<lambda>s. p \<union> \<AX> s)" by (simp add: lfp_gfp)
lemma AG_gfp: "\<AG> p = gfp (\<lambda>s. p \<inter> \<AX> s)" by (simp add: lfp_gfp)

lemma EF_fp: "\<EF> p = p \<union> \<EX> \<EF> p"
proof -
  have "mono (\<lambda>s. p \<union> \<EX> s)" by rule (auto simp add: EX_def)
  then show ?thesis by (simp only: EF_def) (rule lfp_unfold)
qed

lemma AF_fp: "\<AF> p = p \<union> \<AX> \<AF> p"
proof -
  have "mono (\<lambda>s. p \<union> \<AX> s)" by rule (auto simp add: AX_def EX_def)
  then show ?thesis by (simp only: AF_lfp) (rule lfp_unfold)
qed

lemma EG_fp: "\<EG> p = p \<inter> \<EX> \<EG> p"
proof -
  have "mono (\<lambda>s. p \<inter> \<EX> s)" by rule (auto simp add: EX_def)
  then show ?thesis by (simp only: EG_def) (rule gfp_unfold)
qed

text {*
  From the greatest fixed point definition of @{term "\<AG> p"}, we
  derive as a consequence of the Knaster-Tarski theorem on the one
  hand that @{term "\<AG> p"} is a fixed point of the monotonic
  function @{term "\<lambda>s. p \<inter> \<AX> s"}.
*}

lemma AG_fp: "\<AG> p = p \<inter> \<AX> \<AG> p"
proof -
  have "mono (\<lambda>s. p \<inter> \<AX> s)" by rule (auto simp add: AX_def EX_def)
  then show ?thesis by (simp only: AG_gfp) (rule gfp_unfold)
qed

text {*
  This fact may be split up into two inequalities (merely using
  transitivity of @{text "\<subseteq>" }, which is an instance of the overloaded
  @{text "\<le>"} in Isabelle/HOL).
*}

lemma AG_fp_1: "\<AG> p \<subseteq> p"
proof -
  note AG_fp also have "p \<inter> \<AX> \<AG> p \<subseteq> p" by auto
  finally show ?thesis .
qed

text {**}

lemma AG_fp_2: "\<AG> p \<subseteq> \<AX> \<AG> p"
proof -
  note AG_fp also have "p \<inter> \<AX> \<AG> p \<subseteq> \<AX> \<AG> p" by auto
  finally show ?thesis .
qed

text {*
  On the other hand, we have from the Knaster-Tarski fixed point
  theorem that any other post-fixed point of @{term "\<lambda>s. p \<inter> AX s"} is
  smaller than @{term "AG p"}.  A post-fixed point is a set of states
  @{term q} such that @{term "q \<subseteq> p \<inter> AX q"}.  This leads to the
  following co-induction principle for @{term "AG p"}.
*}

lemma AG_I: "q \<subseteq> p \<inter> \<AX> q \<Longrightarrow> q \<subseteq> \<AG> p"
  by (simp only: AG_gfp) (rule gfp_upperbound)


section {* The tree induction principle \label{sec:calc-ctl-tree-induct} *}

text {*
  \tweakskip With the most basic facts available, we are now able to
  establish a few more interesting results, leading to the \emph{tree
  induction} principle for @{text AG} (see below).  We will use some
  elementary monotonicity and distributivity rules.
*}

lemma AX_int: "\<AX> (p \<inter> q) = \<AX> p \<inter> \<AX> q" by auto 
lemma AX_mono: "p \<subseteq> q \<Longrightarrow> \<AX> p \<subseteq> \<AX> q" by auto
lemma AG_mono: "p \<subseteq> q \<Longrightarrow> \<AG> p \<subseteq> \<AG> q"
  by (simp only: AG_gfp, rule gfp_mono) auto 

text {*
  The formula @{term "AG p"} implies @{term "AX p"} (we use
  substitution of @{text "\<subseteq>"} with monotonicity).
*}

lemma AG_AX: "\<AG> p \<subseteq> \<AX> p"
proof -
  have "\<AG> p \<subseteq> \<AX> \<AG> p" by (rule AG_fp_2)
  also have "\<AG> p \<subseteq> p" by (rule AG_fp_1) moreover note AX_mono
  finally show ?thesis .
qed

text {*
  Furthermore we show idempotency of the @{text "\<AG>"} operator.
  The proof is a good example of how accumulated facts may get
  used to feed a single rule step.
*}

lemma AG_AG: "\<AG> \<AG> p = \<AG> p"
proof
  show "\<AG> \<AG> p \<subseteq> \<AG> p" by (rule AG_fp_1)
next
  show "\<AG> p \<subseteq> \<AG> \<AG> p"
  proof (rule AG_I)
    have "\<AG> p \<subseteq> \<AG> p" ..
    moreover have "\<AG> p \<subseteq> \<AX> \<AG> p" by (rule AG_fp_2)
    ultimately show "\<AG> p \<subseteq> \<AG> p \<inter> \<AX> \<AG> p" ..
  qed
qed

text {*
  \smallskip We now give an alternative characterization of the @{text
  "\<AG>"} operator, which describes the @{text "\<AG>"} operator in
  an ``operational'' way by tree induction: In a state holds @{term
  "AG p"} iff in that state holds @{term p}, and in all reachable
  states @{term s} follows from the fact that @{term p} holds in
  @{term s}, that @{term p} also holds in all successor states of
  @{term s}.  We use the co-induction principle @{thm [source] AG_I}
  to establish this in a purely algebraic manner.
*}

theorem AG_induct: "p \<inter> \<AG> (p \<rightarrow> \<AX> p) = \<AG> p"
proof
  show "p \<inter> \<AG> (p \<rightarrow> \<AX> p) \<subseteq> \<AG> p"  (is "?lhs \<subseteq> _")
  proof (rule AG_I)
    show "?lhs \<subseteq> p \<inter> \<AX> ?lhs"
    proof
      show "?lhs \<subseteq> p" ..
      show "?lhs \<subseteq> \<AX> ?lhs"
      proof -
	{
	  have "\<AG> (p \<rightarrow> \<AX> p) \<subseteq> p \<rightarrow> \<AX> p" by (rule AG_fp_1)
          also have "p \<inter> p \<rightarrow> \<AX> p \<subseteq> \<AX> p" ..
          finally have "?lhs \<subseteq> \<AX> p" by auto
	}  
	moreover
	{
	  have "p \<inter> \<AG> (p \<rightarrow> \<AX> p) \<subseteq> \<AG> (p \<rightarrow> \<AX> p)" ..
          also have "\<dots> \<subseteq> \<AX> \<dots>" by (rule AG_fp_2)
          finally have "?lhs \<subseteq> \<AX> \<AG> (p \<rightarrow> \<AX> p)" .
	}  
	ultimately have "?lhs \<subseteq> \<AX> p \<inter> \<AX> \<AG> (p \<rightarrow> \<AX> p)" ..
	also have "\<dots> = \<AX> ?lhs" by (simp only: AX_int)
	finally show ?thesis .
      qed
    qed
  qed
next
  show "\<AG> p \<subseteq> p \<inter> \<AG> (p \<rightarrow> \<AX> p)"
  proof
    show "\<AG> p \<subseteq> p" by (rule AG_fp_1)
    show "\<AG> p \<subseteq> \<AG> (p \<rightarrow> \<AX> p)"
    proof -
      have "\<AG> p = \<AG> \<AG> p" by (simp only: AG_AG)
      also have "\<AG> p \<subseteq> \<AX> p" by (rule AG_AX) moreover note AG_mono
      also have "\<AX> p \<subseteq> (p \<rightarrow> \<AX> p)" .. moreover note AG_mono
      finally show ?thesis .
    qed
  qed
qed


section {* An application of tree induction \label{sec:calc-ctl-commute} *}

text {*
  \tweakskip Further interesting properties of CTL expressions may be
  demonstrated with the help of tree induction; here we show that
  @{text \<AX>} and @{text \<AG>} commute.
*}

theorem AG_AX_commute: "\<AG> \<AX> p = \<AX> \<AG> p"
proof -
  have "\<AG> \<AX> p = \<AX> p \<inter> \<AX> \<AG> \<AX> p" by (rule AG_fp)
  also have "\<dots> = \<AX> (p \<inter> \<AG> \<AX> p)" by (simp only: AX_int)
  also have "p \<inter> \<AG> \<AX> p = \<AG> p"  (is "?lhs = _")
  proof  
    have "\<AX> p \<subseteq> p \<rightarrow> \<AX> p" ..
    also have "p \<inter> \<AG> (p \<rightarrow> \<AX> p) = \<AG> p" by (rule AG_induct)
    also note Int_mono AG_mono  
    ultimately show "?lhs \<subseteq> \<AG> p" by auto
  next  
    have "\<AG> p \<subseteq> p" by (rule AG_fp_1)
    moreover 
    {
      have "\<AG> p = \<AG> \<AG> p" by (simp only: AG_AG)
      also have "\<AG> p \<subseteq> \<AX> p" by (rule AG_AX)
      also note AG_mono
      ultimately have "\<AG> p \<subseteq> \<AG> \<AX> p" .
    } 
    ultimately show "\<AG> p \<subseteq> ?lhs" ..
  qed  
  finally show ?thesis .
qed

end

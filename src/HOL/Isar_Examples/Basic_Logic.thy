(*  Title:      HOL/Isar_Examples/Basic_Logic.thy
    Author:     Makarius

Basic propositional and quantifier reasoning.
*)

section \<open>Basic logical reasoning\<close>

theory Basic_Logic
  imports Main
begin


subsection \<open>Pure backward reasoning\<close>

text \<open>
  In order to get a first idea of how Isabelle/Isar proof documents may look
  like, we consider the propositions \<open>I\<close>, \<open>K\<close>, and \<open>S\<close>. The following (rather
  explicit) proofs should require little extra explanations.
\<close>

lemma I: "A \<longrightarrow> A"
proof
  assume A
  show A by fact
qed

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
proof
  assume A
  show "B \<longrightarrow> A"
  proof
    show A by fact
  qed
qed

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof
  assume "A \<longrightarrow> B \<longrightarrow> C"
  show "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  proof
    assume "A \<longrightarrow> B"
    show "A \<longrightarrow> C"
    proof
      assume A
      show C
      proof (rule mp)
        show "B \<longrightarrow> C" by (rule mp) fact+
        show B by (rule mp) fact+
      qed
    qed
  qed
qed

text \<open>
  Isar provides several ways to fine-tune the reasoning, avoiding excessive
  detail. Several abbreviated language elements are available, enabling the
  writer to express proofs in a more concise way, even without referring to
  any automated proof tools yet.

  Concluding any (sub-)proof already involves solving any remaining goals by
  assumption\<^footnote>\<open>This is not a completely trivial operation, as proof by
  assumption may involve full higher-order unification.\<close>. Thus we may skip the
  rather vacuous body of the above proof.
\<close>

lemma "A \<longrightarrow> A"
proof
qed

text \<open>
  Note that the \<^theory_text>\<open>proof\<close> command refers to the \<open>rule\<close> method (without
  arguments) by default. Thus it implicitly applies a single rule, as
  determined from the syntactic form of the statements involved. The \<^theory_text>\<open>by\<close>
  command abbreviates any proof with empty body, so the proof may be further
  pruned.
\<close>

lemma "A \<longrightarrow> A"
  by rule

text \<open>
  Proof by a single rule may be abbreviated as double-dot.
\<close>

lemma "A \<longrightarrow> A" ..

text \<open>
  Thus we have arrived at an adequate representation of the proof of a
  tautology that holds by a single standard rule.\<^footnote>\<open>Apparently, the
  rule here is implication introduction.\<close>

  \<^medskip>
  Let us also reconsider \<open>K\<close>. Its statement is composed of iterated
  connectives. Basic decomposition is by a single rule at a time, which is why
  our first version above was by nesting two proofs.

  The \<open>intro\<close> proof method repeatedly decomposes a goal's conclusion.\<^footnote>\<open>The
  dual method is \<open>elim\<close>, acting on a goal's premises.\<close>
\<close>

lemma "A \<longrightarrow> B \<longrightarrow> A"
proof (intro impI)
  assume A
  show A by fact
qed

text \<open>Again, the body may be collapsed.\<close>

lemma "A \<longrightarrow> B \<longrightarrow> A"
  by (intro impI)

text \<open>
  Just like \<open>rule\<close>, the \<open>intro\<close> and \<open>elim\<close> proof methods pick standard
  structural rules, in case no explicit arguments are given. While implicit
  rules are usually just fine for single rule application, this may go too far
  with iteration. Thus in practice, \<open>intro\<close> and \<open>elim\<close> would be typically
  restricted to certain structures by giving a few rules only, e.g.\ \<^theory_text>\<open>proof
  (intro impI allI)\<close> to strip implications and universal quantifiers.

  Such well-tuned iterated decomposition of certain structures is the prime
  application of \<open>intro\<close> and \<open>elim\<close>. In contrast, terminal steps that solve a
  goal completely are usually performed by actual automated proof methods
  (such as \<^theory_text>\<open>by blast\<close>.
\<close>


subsection \<open>Variations of backward vs.\ forward reasoning\<close>

text \<open>
  Certainly, any proof may be performed in backward-style only. On the other
  hand, small steps of reasoning are often more naturally expressed in
  forward-style. Isar supports both backward and forward reasoning as a
  first-class concept. In order to demonstrate the difference, we consider
  several proofs of \<open>A \<and> B \<longrightarrow> B \<and> A\<close>.

  The first version is purely backward.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  show "B \<and> A"
  proof
    show B by (rule conjunct2) fact
    show A by (rule conjunct1) fact
  qed
qed

text \<open>
  Above, the projection rules \<open>conjunct1\<close> / \<open>conjunct2\<close> had to be named
  explicitly, since the goals \<open>B\<close> and \<open>A\<close> did not provide any structural clue.
  This may be avoided using \<^theory_text>\<open>from\<close> to focus on the \<open>A \<and> B\<close> assumption as the
  current facts, enabling the use of double-dot proofs. Note that \<^theory_text>\<open>from\<close>
  already does forward-chaining, involving the \<open>conjE\<close> rule here.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  show "B \<and> A"
  proof
    from \<open>A \<and> B\<close> show B ..
    from \<open>A \<and> B\<close> show A ..
  qed
qed

text \<open>
  In the next version, we move the forward step one level upwards.
  Forward-chaining from the most recent facts is indicated by the \<^theory_text>\<open>then\<close>
  command. Thus the proof of \<open>B \<and> A\<close> from \<open>A \<and> B\<close> actually becomes an
  elimination, rather than an introduction. The resulting proof structure
  directly corresponds to that of the \<open>conjE\<close> rule, including the repeated
  goal proposition that is abbreviated as \<open>?thesis\<close> below.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then show "B \<and> A"
  proof                    \<comment> \<open>rule \<open>conjE\<close> of \<open>A \<and> B\<close>\<close>
    assume B A
    then show ?thesis ..   \<comment> \<open>rule \<open>conjI\<close> of \<open>B \<and> A\<close>\<close>
  qed
qed

text \<open>
  In the subsequent version we flatten the structure of the main body by doing
  forward reasoning all the time. Only the outermost decomposition step is
  left as backward.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from \<open>A \<and> B\<close> have A ..
  from \<open>A \<and> B\<close> have B ..
  from \<open>B\<close> \<open>A\<close> show "B \<and> A" ..
qed

text \<open>
  We can still push forward-reasoning a bit further, even at the risk of
  getting ridiculous. Note that we force the initial proof step to do nothing
  here, by referring to the \<open>-\<close> proof method.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof -
  {
    assume "A \<and> B"
    from \<open>A \<and> B\<close> have A ..
    from \<open>A \<and> B\<close> have B ..
    from \<open>B\<close> \<open>A\<close> have "B \<and> A" ..
  }
  then show ?thesis ..         \<comment> \<open>rule \<open>impI\<close>\<close>
qed

text \<open>
  \<^medskip>
  With these examples we have shifted through a whole range from purely
  backward to purely forward reasoning. Apparently, in the extreme ends we get
  slightly ill-structured proofs, which also require much explicit naming of
  either rules (backward) or local facts (forward).

  The general lesson learned here is that good proof style would achieve just
  the \<^emph>\<open>right\<close> balance of top-down backward decomposition, and bottom-up
  forward composition. In general, there is no single best way to arrange some
  pieces of formal reasoning, of course. Depending on the actual applications,
  the intended audience etc., rules (and methods) on the one hand vs.\ facts
  on the other hand have to be emphasized in an appropriate way. This requires
  the proof writer to develop good taste, and some practice, of course.

  \<^medskip>
  For our example the most appropriate way of reasoning is probably the middle
  one, with conjunction introduction done after elimination.
\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then show "B \<and> A"
  proof
    assume B A
    then show ?thesis ..
  qed
qed



subsection \<open>A few examples from ``Introduction to Isabelle''\<close>

text \<open>
  We rephrase some of the basic reasoning examples of \<^cite>\<open>"isabelle-intro"\<close>, using HOL rather than FOL.
\<close>


subsubsection \<open>A propositional proof\<close>

text \<open>
  We consider the proposition \<open>P \<or> P \<longrightarrow> P\<close>. The proof below involves
  forward-chaining from \<open>P \<or> P\<close>, followed by an explicit case-analysis on the
  two \<^emph>\<open>identical\<close> cases.
\<close>

lemma "P \<or> P \<longrightarrow> P"
proof
  assume "P \<or> P"
  then show P
  proof                    \<comment> \<open>rule \<open>disjE\<close>: \smash{$\infer{\<open>C\<close>}{\<open>A \<or> B\<close> & \infer*{\<open>C\<close>}{[\<open>A\<close>]} & \infer*{\<open>C\<close>}{[\<open>B\<close>]}}$}\<close>
    assume P show P by fact
  next
    assume P show P by fact
  qed
qed

text \<open>
  Case splits are \<^emph>\<open>not\<close> hardwired into the Isar language as a special
  feature. The \<^theory_text>\<open>next\<close> command used to separate the cases above is just a
  short form of managing block structure.

  \<^medskip>
  In general, applying proof methods may split up a goal into separate
  ``cases'', i.e.\ new subgoals with individual local assumptions. The
  corresponding proof text typically mimics this by establishing results in
  appropriate contexts, separated by blocks.

  In order to avoid too much explicit parentheses, the Isar system implicitly
  opens an additional block for any new goal, the \<^theory_text>\<open>next\<close> statement then
  closes one block level, opening a new one. The resulting behaviour is what
  one would expect from separating cases, only that it is more flexible. E.g.\
  an induction base case (which does not introduce local assumptions) would
  \<^emph>\<open>not\<close> require \<^theory_text>\<open>next\<close> to separate the subsequent step case.

  \<^medskip>
  In our example the situation is even simpler, since the two cases actually
  coincide. Consequently the proof may be rephrased as follows.
\<close>

lemma "P \<or> P \<longrightarrow> P"
proof
  assume "P \<or> P"
  then show P
  proof
    assume P
    show P by fact
    show P by fact
  qed
qed

text \<open>Again, the rather vacuous body of the proof may be collapsed.
  Thus the case analysis degenerates into two assumption steps, which
  are implicitly performed when concluding the single rule step of the
  double-dot proof as follows.\<close>

lemma "P \<or> P \<longrightarrow> P"
proof
  assume "P \<or> P"
  then show P ..
qed


subsubsection \<open>A quantifier proof\<close>

text \<open>
  To illustrate quantifier reasoning, let us prove
  \<open>(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)\<close>. Informally, this holds because any \<open>a\<close> with
  \<open>P (f a)\<close> may be taken as a witness for the second existential statement.

  The first proof is rather verbose, exhibiting quite a lot of (redundant)
  detail. It gives explicit rules, even with some instantiation. Furthermore,
  we encounter two new language elements: the \<^theory_text>\<open>fix\<close> command augments the
  context by some new ``arbitrary, but fixed'' element; the \<^theory_text>\<open>is\<close> annotation
  binds term abbreviations by higher-order pattern matching.
\<close>

lemma "(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then show "\<exists>y. P y"
  proof (rule exE)             \<comment> \<open>rule \<open>exE\<close>: \smash{$\infer{\<open>B\<close>}{\<open>\<exists>x. A(x)\<close> & \infer*{\<open>B\<close>}{[\<open>A(x)\<close>]_x}}$}\<close>
    fix a
    assume "P (f a)" (is "P ?witness")
    then show ?thesis by (rule exI [of P ?witness])
  qed
qed

text \<open>
  While explicit rule instantiation may occasionally improve readability of
  certain aspects of reasoning, it is usually quite redundant. Above, the
  basic proof outline gives already enough structural clues for the system to
  infer both the rules and their instances (by higher-order unification). Thus
  we may as well prune the text as follows.
\<close>

lemma "(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then show "\<exists>y. P y"
  proof
    fix a
    assume "P (f a)"
    then show ?thesis ..
  qed
qed

text \<open>
  Explicit \<open>\<exists>\<close>-elimination as seen above can become quite cumbersome in
  practice. The derived Isar language element ``\<^theory_text>\<open>obtain\<close>'' provides a more
  handsome way to do generalized existence reasoning.
\<close>

lemma "(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then obtain a where "P (f a)" ..
  then show "\<exists>y. P y" ..
qed

text \<open>
  Technically, \<^theory_text>\<open>obtain\<close> is similar to \<^theory_text>\<open>fix\<close> and \<^theory_text>\<open>assume\<close> together with a
  soundness proof of the elimination involved. Thus it behaves similar to any
  other forward proof element. Also note that due to the nature of general
  existence reasoning involved here, any result exported from the context of
  an \<^theory_text>\<open>obtain\<close> statement may \<^emph>\<open>not\<close> refer to the parameters introduced there.
\<close>


subsubsection \<open>Deriving rules in Isabelle\<close>

text \<open>
  We derive the conjunction elimination rule from the corresponding
  projections. The proof is quite straight-forward, since Isabelle/Isar
  supports non-atomic goals and assumptions fully transparently.
\<close>

theorem conjE: "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
proof -
  assume "A \<and> B"
  assume r: "A \<Longrightarrow> B \<Longrightarrow> C"
  show C
  proof (rule r)
    show A by (rule conjunct1) fact
    show B by (rule conjunct2) fact
  qed
qed

end

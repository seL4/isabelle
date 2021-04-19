(*:maxLineLen=78:*)

theory Eq
imports Base
begin

chapter \<open>Equational reasoning\<close>

text \<open>
  Equality is one of the most fundamental concepts of mathematics. The
  Isabelle/Pure logic (\chref{ch:logic}) provides a builtin relation \<open>\<equiv> :: \<alpha> \<Rightarrow>
  \<alpha> \<Rightarrow> prop\<close> that expresses equality of arbitrary terms (or propositions) at
  the framework level, as expressed by certain basic inference rules
  (\secref{sec:eq-rules}).

  Equational reasoning means to replace equals by equals, using reflexivity
  and transitivity to form chains of replacement steps, and congruence rules
  to access sub-structures. Conversions (\secref{sec:conv}) provide a
  convenient framework to compose basic equational steps to build specific
  equational reasoning tools.

  Higher-order matching is able to provide suitable instantiations for giving
  equality rules, which leads to the versatile concept of \<open>\<lambda>\<close>-term rewriting
  (\secref{sec:rewriting}). Internally this is based on the general-purpose
  Simplifier engine of Isabelle, which is more specific and more efficient
  than plain conversions.

  Object-logics usually introduce specific notions of equality or equivalence,
  and relate it with the Pure equality. This enables to re-use the Pure tools
  for equational reasoning for particular object-logic connectives as well.
\<close>


section \<open>Basic equality rules \label{sec:eq-rules}\<close>

text \<open>
  Isabelle/Pure uses \<open>\<equiv>\<close> for equality of arbitrary terms, which includes
  equivalence of propositions of the logical framework. The conceptual
  axiomatization of the constant \<open>\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop\<close> is given in
  \figref{fig:pure-equality}. The inference kernel presents slightly different
  equality rules, which may be understood as derived rules from this minimal
  axiomatization. The Pure theory also provides some theorems that express the
  same reasoning schemes as theorems that can be composed like object-level
  rules as explained in \secref{sec:obj-rules}.

  For example, \<^ML>\<open>Thm.symmetric\<close> as Pure inference is an ML function that
  maps a theorem \<open>th\<close> stating \<open>t \<equiv> u\<close> to one stating \<open>u \<equiv> t\<close>. In contrast,
  @{thm [source] Pure.symmetric} as Pure theorem expresses the same reasoning
  in declarative form. If used like \<open>th [THEN Pure.symmetric]\<close> in Isar source
  notation, it achieves a similar effect as the ML inference function,
  although the rule attribute @{attribute THEN} or ML operator \<^ML>\<open>op RS\<close>
  involve the full machinery of higher-order unification (modulo
  \<open>\<beta>\<eta>\<close>-conversion) and lifting of \<open>\<And>/\<Longrightarrow>\<close> contexts.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Thm.reflexive: "cterm -> thm"} \\
  @{index_ML Thm.symmetric: "thm -> thm"} \\
  @{index_ML Thm.transitive: "thm -> thm -> thm"} \\
  @{index_ML Thm.abstract_rule: "string -> cterm -> thm -> thm"} \\
  @{index_ML Thm.combination: "thm -> thm -> thm"} \\[0.5ex]
  @{index_ML Thm.equal_intr: "thm -> thm -> thm"} \\
  @{index_ML Thm.equal_elim: "thm -> thm -> thm"} \\
  \end{mldecls}

  See also \<^file>\<open>~~/src/Pure/thm.ML\<close> for further description of these inference
  rules, and a few more for primitive \<open>\<beta>\<close> and \<open>\<eta>\<close> conversions. Note that \<open>\<alpha>\<close>
  conversion is implicit due to the representation of terms with de-Bruijn
  indices (\secref{sec:terms}).
\<close>


section \<open>Conversions \label{sec:conv}\<close>

text \<open>
  The classic article @{cite "paulson:1983"} introduces the concept of
  conversion for Cambridge LCF. This was historically important to implement
  all kinds of ``simplifiers'', but the Isabelle Simplifier is done quite
  differently, see @{cite \<open>\S9.3\<close> "isabelle-isar-ref"}.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_structure Conv} \\
  @{index_ML_type conv} \\
  @{index_ML Simplifier.asm_full_rewrite : "Proof.context -> conv"} \\
  \end{mldecls}

  \<^descr> \<^ML_structure>\<open>Conv\<close> is a library of combinators to build conversions,
  over type \<^ML_type>\<open>conv\<close> (see also \<^file>\<open>~~/src/Pure/conv.ML\<close>). This is one
  of the few Isabelle/ML modules that are usually used with \<^verbatim>\<open>open\<close>: finding
  examples works by searching for ``\<^verbatim>\<open>open Conv\<close>'' instead of ``\<^verbatim>\<open>Conv.\<close>''.

  \<^descr> \<^ML>\<open>Simplifier.asm_full_rewrite\<close> invokes the Simplifier as a
  conversion. There are a few related operations, corresponding to the various
  modes of simplification.
\<close>


section \<open>Rewriting \label{sec:rewriting}\<close>

text \<open>
  Rewriting normalizes a given term (theorem or goal) by replacing instances
  of given equalities \<open>t \<equiv> u\<close> in subterms. Rewriting continues until no
  rewrites are applicable to any subterm. This may be used to unfold simple
  definitions of the form \<open>f x\<^sub>1 \<dots> x\<^sub>n \<equiv> u\<close>, but is slightly more general than
  that. \<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML rewrite_rule: "Proof.context -> thm list -> thm -> thm"} \\
  @{index_ML rewrite_goals_rule: "Proof.context -> thm list -> thm -> thm"} \\
  @{index_ML rewrite_goal_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{index_ML rewrite_goals_tac: "Proof.context -> thm list -> tactic"} \\
  @{index_ML fold_goals_tac: "Proof.context -> thm list -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>rewrite_rule\<close>~\<open>ctxt rules thm\<close> rewrites the whole theorem by the
  given rules.

  \<^descr> \<^ML>\<open>rewrite_goals_rule\<close>~\<open>ctxt rules thm\<close> rewrites the outer premises of
  the given theorem. Interpreting the same as a goal state
  (\secref{sec:tactical-goals}) it means to rewrite all subgoals (in the same
  manner as \<^ML>\<open>rewrite_goals_tac\<close>).

  \<^descr> \<^ML>\<open>rewrite_goal_tac\<close>~\<open>ctxt rules i\<close> rewrites subgoal \<open>i\<close> by the given
  rewrite rules.

  \<^descr> \<^ML>\<open>rewrite_goals_tac\<close>~\<open>ctxt rules\<close> rewrites all subgoals by the given
  rewrite rules.

  \<^descr> \<^ML>\<open>fold_goals_tac\<close>~\<open>ctxt rules\<close> essentially uses \<^ML>\<open>rewrite_goals_tac\<close>
  with the symmetric form of each member of \<open>rules\<close>, re-ordered to fold longer
  expression first. This supports to idea to fold primitive definitions that
  appear in expended form in the proof state.
\<close>

end

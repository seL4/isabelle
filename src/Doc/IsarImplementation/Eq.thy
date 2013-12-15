theory Eq
imports Base
begin

chapter {* Equational reasoning *}

text {* Equality is one of the most fundamental concepts of
  mathematics.  The Isabelle/Pure logic (\chref{ch:logic}) provides a
  builtin relation @{text "\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop"} that expresses equality
  of arbitrary terms (or propositions) at the framework level, as
  expressed by certain basic inference rules (\secref{sec:eq-rules}).

  Equational reasoning means to replace equals by equals, using
  reflexivity and transitivity to form chains of replacement steps,
  and congruence rules to access sub-structures.  Conversions
  (\secref{sec:conv}) provide a convenient framework to compose basic
  equational steps to build specific equational reasoning tools.

  Higher-order matching is able to provide suitable instantiations for
  giving equality rules, which leads to the versatile concept of
  @{text "\<lambda>"}-term rewriting (\secref{sec:rewriting}).  Internally
  this is based on the general-purpose Simplifier engine of Isabelle,
  which is more specific and more efficient than plain conversions.

  Object-logics usually introduce specific notions of equality or
  equivalence, and relate it with the Pure equality.  This enables to
  re-use the Pure tools for equational reasoning for particular
  object-logic connectives as well.
*}


section {* Basic equality rules \label{sec:eq-rules} *}

text {* Isabelle/Pure uses @{text "\<equiv>"} for equality of arbitrary
  terms, which includes equivalence of propositions of the logical
  framework.  The conceptual axiomatization of the constant @{text "\<equiv>
  :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop"} is given in \figref{fig:pure-equality}.  The
  inference kernel presents slightly different equality rules, which
  may be understood as derived rules from this minimal axiomatization.
  The Pure theory also provides some theorems that express the same
  reasoning schemes as theorems that can be composed like object-level
  rules as explained in \secref{sec:obj-rules}.

  For example, @{ML Thm.symmetric} as Pure inference is an ML function
  that maps a theorem @{text "th"} stating @{text "t \<equiv> u"} to one
  stating @{text "u \<equiv> t"}.  In contrast, @{thm [source]
  Pure.symmetric} as Pure theorem expresses the same reasoning in
  declarative form.  If used like @{text "th [THEN Pure.symmetric]"}
  in Isar source notation, it achieves a similar effect as the ML
  inference function, although the rule attribute @{attribute THEN} or
  ML operator @{ML "op RS"} involve the full machinery of higher-order
  unification (modulo @{text "\<beta>\<eta>"}-conversion) and lifting of @{text
  "\<And>/\<Longrightarrow>"} contexts. *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Thm.reflexive: "cterm -> thm"} \\
  @{index_ML Thm.symmetric: "thm -> thm"} \\
  @{index_ML Thm.transitive: "thm -> thm -> thm"} \\
  @{index_ML Thm.abstract_rule: "string -> cterm -> thm -> thm"} \\
  @{index_ML Thm.combination: "thm -> thm -> thm"} \\[0.5ex]
  @{index_ML Thm.equal_intr: "thm -> thm -> thm"} \\
  @{index_ML Thm.equal_elim: "thm -> thm -> thm"} \\
  \end{mldecls}

  See also @{file "~~/src/Pure/thm.ML" } for further description of
  these inference rules, and a few more for primitive @{text "\<beta>"} and
  @{text "\<eta>"} conversions.  Note that @{text "\<alpha>"} conversion is
  implicit due to the representation of terms with de-Bruijn indices
  (\secref{sec:terms}). *}


section {* Conversions \label{sec:conv} *}

text {*
  %FIXME

  The classic article that introduces the concept of conversion (for
  Cambridge LCF) is \cite{paulson:1983}.
*}


section {* Rewriting \label{sec:rewriting} *}

text {* Rewriting normalizes a given term (theorem or goal) by
  replacing instances of given equalities @{text "t \<equiv> u"} in subterms.
  Rewriting continues until no rewrites are applicable to any subterm.
  This may be used to unfold simple definitions of the form @{text "f
  x\<^sub>1 \<dots> x\<^sub>n \<equiv> u"}, but is slightly more general than that.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML rewrite_rule: "Proof.context -> thm list -> thm -> thm"} \\
  @{index_ML rewrite_goals_rule: "Proof.context -> thm list -> thm -> thm"} \\
  @{index_ML rewrite_goal_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{index_ML rewrite_goals_tac: "Proof.context -> thm list -> tactic"} \\
  @{index_ML fold_goals_tac: "Proof.context -> thm list -> tactic"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML rewrite_rule}~@{text "ctxt rules thm"} rewrites the whole
  theorem by the given rules.

  \item @{ML rewrite_goals_rule}~@{text "ctxt rules thm"} rewrites the
  outer premises of the given theorem.  Interpreting the same as a
  goal state (\secref{sec:tactical-goals}) it means to rewrite all
  subgoals (in the same manner as @{ML rewrite_goals_tac}).

  \item @{ML rewrite_goal_tac}~@{text "ctxt rules i"} rewrites subgoal
  @{text "i"} by the given rewrite rules.

  \item @{ML rewrite_goals_tac}~@{text "ctxt rules"} rewrites all subgoals
  by the given rewrite rules.

  \item @{ML fold_goals_tac}~@{text "ctxt rules"} essentially uses @{ML
  rewrite_goals_tac} with the symmetric form of each member of @{text
  "rules"}, re-ordered to fold longer expression first.  This supports
  to idea to fold primitive definitions that appear in expended form
  in the proof state.

  \end{description}
*}

end

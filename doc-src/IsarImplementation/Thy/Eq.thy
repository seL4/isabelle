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

text {* FIXME *}


section {* Conversions \label{sec:conv} *}

text {* FIXME *}


section {* Rewriting \label{sec:rewriting} *}

text {* Rewriting normalizes a given term (theorem or goal) by
  replacing instances of given equalities @{text "t \<equiv> u"} in subterms.
  Rewriting continues until no rewrites are applicable to any subterm.
  This may be used to unfold simple definitions of the form @{text "f
  x\<^sub>1 \<dots> x\<^sub>n \<equiv> u"}, but is slightly more general than that.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML rewrite_goal_tac: "thm list -> int -> tactic"} \\
  @{index_ML rewrite_goals_tac: "thm list -> tactic"} \\
  @{index_ML fold_goals_tac: "thm list -> tactic"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML rewrite_goal_tac}~@{text "rules i"} rewrites subgoal
  @{text "i"} by the given rewrite rules.

  \item @{ML rewrite_goals_tac}~@{text "rules"} rewrites all subgoals
  by the given rewrite rules.

  \item @{ML fold_goals_tac}~@{text "rules"} essentially uses @{ML
  rewrite_goals_tac} with the symmetric form of each member of @{text
  "rules"}, re-ordered to fold longer expression first.  This supports
  to idea to fold primitive definitions that appear in expended form
  in the proof state.

  \end{description}
*}

end

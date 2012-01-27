theory ML_Tactic
imports Base Main
begin

chapter {* ML tactic expressions *}

text {*
  Isar Proof methods closely resemble traditional tactics, when used
  in unstructured sequences of @{command "apply"} commands.
  Isabelle/Isar provides emulations for all major ML tactics of
  classic Isabelle --- mostly for the sake of easy porting of existing
  developments, as actual Isar proof texts would demand much less
  diversity of proof methods.

  Unlike tactic expressions in ML, Isar proof methods provide proper
  concrete syntax for additional arguments, options, modifiers etc.
  Thus a typical method text is usually more concise than the
  corresponding ML tactic.  Furthermore, the Isar versions of classic
  Isabelle tactics often cover several variant forms by a single
  method with separate options to tune the behavior.  For example,
  method @{method simp} replaces all of @{ML simp_tac}~/ @{ML
  asm_simp_tac}~/ @{ML full_simp_tac}~/ @{ML asm_full_simp_tac}, there
  is also concrete syntax for augmenting the Simplifier context (the
  current ``simpset'') in a convenient way.
*}


section {* Resolution tactics *}

text {*
  Classic Isabelle provides several variant forms of tactics for
  single-step rule applications (based on higher-order resolution).
  The space of resolution tactics has the following main dimensions.

  \begin{enumerate}

  \item The ``mode'' of resolution: intro, elim, destruct, or forward
  (e.g.\ @{ML resolve_tac}, @{ML eresolve_tac}, @{ML dresolve_tac},
  @{ML forward_tac}).

  \item Optional explicit instantiation (e.g.\ @{ML resolve_tac} vs.\
  @{ML res_inst_tac}).

  \item Abbreviations for singleton arguments (e.g.\ @{ML resolve_tac}
  vs.\ @{ML rtac}).

  \end{enumerate}

  Basically, the set of Isar tactic emulations @{method rule_tac},
  @{method erule_tac}, @{method drule_tac}, @{method frule_tac} (see
  \secref{sec:tactics}) would be sufficient to cover the four modes,
  either with or without instantiation, and either with single or
  multiple arguments.  Although it is more convenient in most cases to
  use the plain @{method_ref (Pure) rule} method, or any of its
  ``improper'' variants @{method erule}, @{method drule}, @{method
  frule}.  Note that explicit goal addressing is only supported by the
  actual @{method rule_tac} version.

  With this in mind, plain resolution tactics correspond to Isar
  methods as follows.

  \medskip
  \begin{tabular}{lll}
    @{ML rtac}~@{text "a 1"} & & @{text "rule a"} \\
    @{ML resolve_tac}~@{text "[a\<^sub>1, \<dots>] 1"} & & @{text "rule a\<^sub>1 \<dots>"} \\
    @{ML res_inst_tac}~@{text "ctxt [(x\<^sub>1, t\<^sub>1), \<dots>] a 1"} & &
    @{text "rule_tac x\<^sub>1 = t\<^sub>1 \<AND> \<dots> \<IN> a"} \\[0.5ex]
    @{ML rtac}~@{text "a i"} & & @{text "rule_tac [i] a"} \\
    @{ML resolve_tac}~@{text "[a\<^sub>1, \<dots>] i"} & & @{text "rule_tac [i] a\<^sub>1 \<dots>"} \\
    @{ML res_inst_tac}~@{text "ctxt [(x\<^sub>1, t\<^sub>1), \<dots>] a i"} & &
    @{text "rule_tac [i] x\<^sub>1 = t\<^sub>1 \<AND> \<dots> \<IN> a"} \\
  \end{tabular}
  \medskip

  Note that explicit goal addressing may be usually avoided by
  changing the order of subgoals with @{command "defer"} or @{command
  "prefer"} (see \secref{sec:tactic-commands}).
*}


section {* Simplifier tactics *}

text {*
  The main Simplifier tactics @{ML simp_tac} and variants (cf.\
  \cite{isabelle-ref}) are all covered by the @{method simp} and
  @{method simp_all} methods (see \secref{sec:simplifier}).  Note that
  there is no individual goal addressing available, simplification
  acts either on the first goal (@{method simp}) or all goals
  (@{method simp_all}).

  \medskip
  \begin{tabular}{lll}
    @{ML asm_full_simp_tac}~@{text "@{simpset} 1"} & & @{method simp} \\
    @{ML ALLGOALS}~(@{ML asm_full_simp_tac}~@{text "@{simpset}"}) & & @{method simp_all} \\[0.5ex]
    @{ML simp_tac}~@{text "@{simpset} 1"} & & @{method simp}~@{text "(no_asm)"} \\
    @{ML asm_simp_tac}~@{text "@{simpset} 1"} & & @{method simp}~@{text "(no_asm_simp)"} \\
    @{ML full_simp_tac}~@{text "@{simpset} 1"} & & @{method simp}~@{text "(no_asm_use)"} \\
    @{ML asm_lr_simp_tac}~@{text "@{simpset} 1"} & & @{method simp}~@{text "(asm_lr)"} \\
  \end{tabular}
  \medskip
*}


section {* Classical Reasoner tactics *}

text {* The Classical Reasoner provides a rather large number of
  variations of automated tactics, such as @{ML blast_tac}, @{ML
  fast_tac}, @{ML clarify_tac} etc.  The corresponding Isar methods
  usually share the same base name, such as @{method blast}, @{method
  fast}, @{method clarify} etc.\ (see \secref{sec:classical}).  *}


section {* Miscellaneous tactics *}

text {*
  There are a few additional tactics defined in various theories of
  Isabelle/HOL, some of these also in Isabelle/FOL or Isabelle/ZF.
  The most common ones of these may be ported to Isar as follows.

  \medskip
  \begin{tabular}{lll}
    @{ML stac}~@{text "a 1"} & & @{text "subst a"} \\
    @{ML hyp_subst_tac}~@{text 1} & & @{text hypsubst} \\
    @{ML strip_tac}~@{text 1} & @{text "\<approx>"} & @{text "intro strip"} \\
    @{ML split_all_tac}~@{text 1} & & @{text "simp (no_asm_simp) only: split_tupled_all"} \\
      & @{text "\<approx>"} & @{text "simp only: split_tupled_all"} \\
      & @{text "\<lless>"} & @{text "clarify"} \\
  \end{tabular}
*}


section {* Tacticals *}

text {*
  Classic Isabelle provides a huge amount of tacticals for combination
  and modification of existing tactics.  This has been greatly reduced
  in Isar, providing the bare minimum of combinators only: ``@{text
  ","}'' (sequential composition), ``@{text "|"}'' (alternative
  choices), ``@{text "?"}'' (try), ``@{text "+"}'' (repeat at least
  once).  These are usually sufficient in practice; if all fails,
  arbitrary ML tactic code may be invoked via the @{method tactic}
  method (see \secref{sec:tactics}).

  \medskip Common ML tacticals may be expressed directly in Isar as
  follows:

  \medskip
  \begin{tabular}{lll}
    @{text "tac\<^sub>1"}~@{ML_text THEN}~@{text "tac\<^sub>2"} & & @{text "meth\<^sub>1, meth\<^sub>2"} \\
    @{text "tac\<^sub>1"}~@{ML_text ORELSE}~@{text "tac\<^sub>2"} & & @{text "meth\<^sub>1 | meth\<^sub>2"} \\
    @{ML TRY}~@{text tac} & & @{text "meth?"} \\
    @{ML REPEAT1}~@{text tac} & & @{text "meth+"} \\
    @{ML REPEAT}~@{text tac} & & @{text "(meth+)?"} \\
    @{ML EVERY}~@{text "[tac\<^sub>1, \<dots>]"} & & @{text "meth\<^sub>1, \<dots>"} \\
    @{ML FIRST}~@{text "[tac\<^sub>1, \<dots>]"} & & @{text "meth\<^sub>1 | \<dots>"} \\
  \end{tabular}
  \medskip

  \medskip @{ML CHANGED} (see \cite{isabelle-implementation}) is
  usually not required in Isar, since most basic proof methods already
  fail unless there is an actual change in the goal state.
  Nevertheless, ``@{text "?"}''  (try) may be used to accept
  \emph{unchanged} results as well.

  \medskip @{ML ALLGOALS}, @{ML SOMEGOAL} etc.\ (see
  \cite{isabelle-implementation}) are not available in Isar, since
  there is no direct goal addressing.  Nevertheless, some basic
  methods address all goals internally, notably @{method simp_all}
  (see \secref{sec:simplifier}).  Also note that @{ML ALLGOALS} can be
  often replaced by ``@{text "+"}'' (repeat at least once), although
  this usually has a different operational behavior: subgoals are
  solved in a different order.

  \medskip Iterated resolution, such as
  @{ML_text "REPEAT (FIRSTGOAL (resolve_tac ...))"}, is usually better
  expressed using the @{method intro} and @{method elim} methods of
  Isar (see \secref{sec:classical}).
*}

end

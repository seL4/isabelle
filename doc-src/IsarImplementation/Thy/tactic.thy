
(* $Id$ *)

theory tactic imports base begin

chapter {* Tactical theorem proving *}

text {* The basic idea of tactical theorem proving is to refine the
initial claim in a backwards fashion, until a solved form is reached.
An intermediate goal consists of several subgoals that need to be
solved in order to achieve the main statement; zero subgoals means
that the proof may be finished.  Goal refinement operations are called
tactics; combinators for composing tactics are called tacticals.  *}


section {* Goals \label{sec:tactical-goals} *}

text {* Isabelle/Pure represents a goal\glossary{Tactical goal}{A
theorem of \seeglossary{Horn Clause} form stating that a number of
subgoals imply the main conclusion, which is marked as a protected
proposition.} as a theorem stating that the subgoals imply the main
goal: @{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C"}.  The outermost goal
structure is that of a Horn Clause\glossary{Horn Clause}{An iterated
implication @{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C"}, without any
outermost quantifiers.  Strictly speaking, propositions @{text
"A\<^sub>i"} need to be atomic in Horn Clauses, but Isabelle admits
arbitrary substructure here (nested @{text "\<Longrightarrow>"} and @{text "\<And>"}
connectives).}: an iterated implication without any
quantifiers\footnote{Recall that outermost @{text "\<And>x. \<phi>[x]"} is
always represented via schematic variables in the body: @{text
"\<phi>[?x]"}.  These may get instantiated during the course of
reasoning.}.  For @{text "n = 0"} a goal is solved.

The structure of each subgoal @{text "A\<^sub>i"} is that of a general
Heriditary Harrop Formula @{text "\<And>x\<^sub>1 \<dots> \<And>x\<^sub>k. H\<^sub>1 \<Longrightarrow>
\<dots> \<Longrightarrow> H\<^sub>m \<Longrightarrow> B"} according to the normal form where any local
@{text \<And>} is pulled before @{text \<Longrightarrow>}.  Here @{text "x\<^sub>1, \<dots>,
x\<^sub>k"} are goal parameters, i.e.\ arbitrary-but-fixed entities of
certain types, and @{text "H\<^sub>1, \<dots>, H\<^sub>m"} are goal
hypotheses, i.e.\ facts that may be assumed locally.  Together, this
forms the goal context of the conclusion @{text B} to be established.
The goal hypotheses may be again arbitrary Harrop Formulas, although
the level of nesting rarely exceeds 1--2 in practice.

The main conclusion @{text C} is internally marked as a protected
proposition\glossary{Protected proposition}{An arbitrarily structured
proposition @{text "C"} which is forced to appear as atomic by
wrapping it into a propositional identity operator; notation @{text
"#C"}.  Protecting a proposition prevents basic inferences from
entering into that structure for the time being.}, which is
occasionally represented explicitly by the notation @{text "#C"}.
This ensures that the decomposition into subgoals and main conclusion
is well-defined for arbitrarily structured claims.

\medskip Basic goal management is performed via the following
Isabelle/Pure rules:

  \[
  \infer[@{text "(init)"}]{@{text "C \<Longrightarrow> #C"}}{} \qquad
  \infer[@{text "(finish)"}]{@{text "#C"}}{@{text "C"}}
  \]

  \medskip The following low-level variants admit general reasoning
  with protected propositions:

  \[
  \infer[@{text "(protect)"}]{@{text "#C"}}{@{text "C"}} \qquad
  \infer[@{text "(conclude)"}]{@{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C"}}{@{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> #C"}}
  \]
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Goal.init: "cterm -> thm"} \\
  @{index_ML Goal.finish: "thm -> thm"} \\
  @{index_ML Goal.protect: "thm -> thm"} \\
  @{index_ML Goal.conclude: "thm -> thm"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML "Goal.init"}~@{text "\<phi>"} initializes a tactical goal with
  the type-checked proposition @{text \<phi>}.

  \item @{ML "Goal.finish"}~@{text "th"} checks whether theorem @{text
  "th"} is a solved goal configuration (zero subgoals), and concludes
  the result by removing the goal protection.

  \item @{ML "Goal.protect"}~@{text "th"} protects the whole statement
  of theorem @{text "th"}.

  \item @{ML "Goal.conclude"}~@{text "th"} removes the goal protection
  for any number of pending subgoals.

  \end{description}
*}


section {* Tactics *}

text {*

FIXME

\glossary{Tactic}{Any function that maps a \seeglossary{tactical goal}
to a lazy sequence of possible sucessors.  This scheme subsumes
failure (empty result sequence), as well as lazy enumeration of proof
search results.  Error conditions are usually mapped to an empty
result, which gives further tactics a chance to try in turn.
Commonly, tactics either take an argument to address a particular
subgoal, or operate on a certain range of subgoals in a uniform
fashion.  In any case, the main conclusion is normally left untouched,
apart from instantiating \seeglossary{schematic variables}.}


*}

section {* Tacticals *}

text {*

FIXME

\glossary{Tactical}{A functional combinator for building up complex
tactics from simpler ones.  Typical tactical perform sequential
composition, disjunction (choice), iteration, or goal addressing.
Various search strategies may be expressed via tacticals.}

*}

section {* Programmed proofs *}

text {*
  In order to perform a complete tactical proof under program control,
  one needs to set up an initial goal configuration, apply a tactic,
  and finish the result, cf.\ the rules given in
  \secref{sec:tactical-goals}.  Further checks are required to ensure
  that the result is actually an instance of the original claim --
  ill-behaved tactics could have destroyed that information.

  Several simultaneous claims may be handled within a single goal
  statement by using meta-level conjunction internally.\footnote{This
  is merely syntax for certain derived statements within
  Isabelle/Pure, there is no need to introduce a separate conjunction
  operator.}  The whole configuration may be considered within a
  context of arbitrary-but-fixed parameters and hypotheses, which will
  be available as local facts during the proof and discharged into
  implications in the result.

  All of these administrative tasks are packaged into a separate
  operation, such that the user merely needs to provide the statement
  and tactic to be applied.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Goal.prove: "theory -> string list -> term list -> term ->
  (thm list -> tactic) -> thm"} \\
  @{index_ML Goal.prove_multi: "theory -> string list -> term list -> term list ->
  (thm list -> tactic) -> thm list"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Goal.prove}~@{text "thy xs As C tac"} states goal @{text
  "C"} in the context of arbitrary-but-fixed parameters @{text "xs"}
  and hypotheses @{text "As"} and applies tactic @{text "tac"} to
  solve it.  The latter may depend on the local assumptions being
  presented as facts.  The result is essentially @{text "\<And>xs. As \<Longrightarrow>
  C"}, but is normalized by pulling @{text "\<And>"} before @{text "\<Longrightarrow>"}
  (the conclusion @{text "C"} itself may be a rule statement), turning
  the quantifier prefix into schematic variables, and generalizing
  implicit type-variables.

  Any additional fixed variables or hypotheses not being mentioned in
  the initial statement are left unchanged --- programmed proofs may
  well occur in a larger context.

  \item @{ML Goal.prove_multi} is simular to @{ML Goal.prove}, but
  states several conclusions simultaneously.  @{ML
  Tactic.conjunction_tac} may be used to split these into individual
  subgoals before commencing the actual proof.

  \end{description}
*}

end



(* $Id$ *)

theory tactic imports base begin

chapter {* Tactical reasoning *}

text {*
  Tactical reasoning works by refining the initial claim in a
  backwards fashion, until a solved form is reached.  A @{text "goal"}
  consists of several subgoals that need to be solved in order to
  achieve the main statement; zero subgoals means that the proof may
  be finished.  A @{text "tactic"} is a refinement operation that maps
  a goal to a lazy sequence of potential successors.  A @{text
  "tactical"} is a combinator for composing tactics.
*}


section {* Goals \label{sec:tactical-goals} *}

text {*
  Isabelle/Pure represents a goal\glossary{Tactical goal}{A theorem of
  \seeglossary{Horn Clause} form stating that a number of subgoals
  imply the main conclusion, which is marked as a protected
  proposition.} as a theorem stating that the subgoals imply the main
  goal: @{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C"}.  The outermost goal
  structure is that of a Horn Clause\glossary{Horn Clause}{An iterated
  implication @{text "A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C"}, without any
  outermost quantifiers.  Strictly speaking, propositions @{text
  "A\<^sub>i"} need to be atomic in Horn Clauses, but Isabelle admits
  arbitrary substructure here (nested @{text "\<Longrightarrow>"} and @{text "\<And>"}
  connectives).}: i.e.\ an iterated implication without any
  quantifiers\footnote{Recall that outermost @{text "\<And>x. \<phi>[x]"} is
  always represented via schematic variables in the body: @{text
  "\<phi>[?x]"}.  These variables may get instantiated during the course of
  reasoning.}.  For @{text "n = 0"} a goal is called ``solved''.

  The structure of each subgoal @{text "A\<^sub>i"} is that of a
  general Hereditary Harrop Formula @{text "\<And>x\<^sub>1 \<dots>
  \<And>x\<^sub>k. H\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> H\<^sub>m \<Longrightarrow> B"} in normal form where.
  Here @{text "x\<^sub>1, \<dots>, x\<^sub>k"} are goal parameters, i.e.\
  arbitrary-but-fixed entities of certain types, and @{text
  "H\<^sub>1, \<dots>, H\<^sub>m"} are goal hypotheses, i.e.\ facts that may
  be assumed locally.  Together, this forms the goal context of the
  conclusion @{text B} to be established.  The goal hypotheses may be
  again arbitrary Hereditary Harrop Formulas, although the level of
  nesting rarely exceeds 1--2 in practice.

  The main conclusion @{text C} is internally marked as a protected
  proposition\glossary{Protected proposition}{An arbitrarily
  structured proposition @{text "C"} which is forced to appear as
  atomic by wrapping it into a propositional identity operator;
  notation @{text "#C"}.  Protecting a proposition prevents basic
  inferences from entering into that structure for the time being.},
  which is represented explicitly by the notation @{text "#C"}.  This
  ensures that the decomposition into subgoals and main conclusion is
  well-defined for arbitrarily structured claims.

  \medskip Basic goal management is performed via the following
  Isabelle/Pure rules:

  \[
  \infer[@{text "(init)"}]{@{text "C \<Longrightarrow> #C"}}{} \qquad
  \infer[@{text "(finish)"}]{@{text "C"}}{@{text "#C"}}
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

  \item @{ML "Goal.init"}~@{text C} initializes a tactical goal from
  the well-formed proposition @{text C}.

  \item @{ML "Goal.finish"}~@{text "thm"} checks whether theorem
  @{text "thm"} is a solved goal (no subgoals), and concludes the
  result by removing the goal protection.

  \item @{ML "Goal.protect"}~@{text "thm"} protects the full statement
  of theorem @{text "thm"}.

  \item @{ML "Goal.conclude"}~@{text "thm"} removes the goal
  protection, even if there are pending subgoals.

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

end


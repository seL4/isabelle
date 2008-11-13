
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

  The structure of each subgoal @{text "A\<^sub>i"} is that of a general
  Hereditary Harrop Formula @{text "\<And>x\<^sub>1 \<dots> \<And>x\<^sub>k. H\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> H\<^sub>m \<Longrightarrow> B"} in
  normal form.  Here @{text "x\<^sub>1, \<dots>, x\<^sub>k"} are goal parameters, i.e.\
  arbitrary-but-fixed entities of certain types, and @{text "H\<^sub>1, \<dots>,
  H\<^sub>m"} are goal hypotheses, i.e.\ facts that may be assumed locally.
  Together, this forms the goal context of the conclusion @{text B} to
  be established.  The goal hypotheses may be again arbitrary
  Hereditary Harrop Formulas, although the level of nesting rarely
  exceeds 1--2 in practice.

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

text {* A @{text "tactic"} is a function @{text "goal \<rightarrow> goal\<^sup>*\<^sup>*"} that
  maps a given goal state (represented as a theorem, cf.\
  \secref{sec:tactical-goals}) to a lazy sequence of potential
  successor states.  The underlying sequence implementation is lazy
  both in head and tail, and is purely functional in \emph{not}
  supporting memoing.\footnote{The lack of memoing and the strict
  nature of SML requires some care when working with low-level
  sequence operations, to avoid duplicate or premature evaluation of
  results.}

  An \emph{empty result sequence} means that the tactic has failed: in
  a compound tactic expressions other tactics might be tried instead,
  or the whole refinement step might fail outright, producing a
  toplevel error message.  When implementing tactics from scratch, one
  should take care to observe the basic protocol of mapping regular
  error conditions to an empty result; only serious faults should
  emerge as exceptions.

  By enumerating \emph{multiple results}, a tactic can easily express
  the potential outcome of an internal search process.  There are also
  combinators for building proof tools that involve search
  systematically, see also \secref{sec:tacticals}.

  \medskip As explained in \secref{sec:tactical-goals}, a goal state
  essentially consists of a list of subgoals that imply the main goal
  (conclusion).  Tactics may operate on all subgoals or on a
  particularly specified subgoal, but must not change the main
  conclusion (apart from instantiating schematic goal variables).

  Tactics with explicit \emph{subgoal addressing} are of the form
  @{text "int \<rightarrow> tactic"} and may be applied to a particular subgoal
  (counting from 1).  If the subgoal number is out of range, the
  tactic should fail with an empty result sequence, but must not raise
  an exception!

  Operating on a particular subgoal means to replace it by an interval
  of zero or more subgoals in the same place; other subgoals must not
  be affected, apart from instantiating schematic variables ranging
  over the whole goal state.

  A common pattern of composing tactics with subgoal addressing is to
  try the first one, and then the second one only if the subgoal has
  not been solved yet.  Special care is required here to avoid bumping
  into unrelated subgoals that happen come after the original subgoal.
  Assuming that there is only a single initial subgoal is a very
  common error when implementing tactics!
  
  \medskip The main well-formedness conditions for proper tactics are
  summarized as follows.

  \begin{itemize}

  \item General tactic failure is indicated by an empty result, only
  serious faults may produce an exception.

  \item The main conclusion must not be changed, apart from
  instantiating schematic variables.

  \item A tactic operates either uniformly on all subgoals, or
  specifically on a selected subgoal (without bumping into unrelated
  subgoals).

  \item Range errors in subgoal addressing produce an empty result.

  \end{itemize}
*}


section {* Tacticals \label{sec:tacticals} *}

text {*

FIXME

\glossary{Tactical}{A functional combinator for building up complex
tactics from simpler ones.  Typical tactical perform sequential
composition, disjunction (choice), iteration, or goal addressing.
Various search strategies may be expressed via tacticals.}

*}

end


theory Tactic
imports Base
begin

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
  into unrelated subgoals that happen to come after the original
  subgoal.  Assuming that there is only a single initial subgoal is a
  very common error when implementing tactics!

  Tactics with internal subgoal addressing should expose the subgoal
  index as @{text "int"} argument in full generality; a hardwired
  subgoal 1 inappropriate.
  
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

  Some of these conditions are checked by higher-level goal
  infrastructure (\secref{sec:results}); others are not checked
  explicitly, and violating them merely results in ill-behaved tactics
  experienced by the user (e.g.\ tactics that insist in being
  applicable only to singleton goals, or disallow composition with
  basic tacticals).
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type tactic: "thm -> thm Seq.seq"} \\
  @{index_ML no_tac: tactic} \\
  @{index_ML all_tac: tactic} \\
  @{index_ML print_tac: "string -> tactic"} \\[1ex]
  @{index_ML PRIMITIVE: "(thm -> thm) -> tactic"} \\[1ex]
  @{index_ML SUBGOAL: "(term * int -> tactic) -> int -> tactic"} \\
  @{index_ML CSUBGOAL: "(cterm * int -> tactic) -> int -> tactic"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type tactic} represents tactics.  The well-formedness
  conditions described above need to be observed.  See also @{"file"
  "~~/src/Pure/General/seq.ML"} for the underlying implementation of
  lazy sequences.

  \item @{ML_type "int -> tactic"} represents tactics with explicit
  subgoal addressing, with well-formedness conditions as described
  above.

  \item @{ML no_tac} is a tactic that always fails, returning the
  empty sequence.

  \item @{ML all_tac} is a tactic that always succeeds, returning a
  singleton sequence with unchanged goal state.

  \item @{ML print_tac}~@{text "message"} is like @{ML all_tac}, but
  prints a message together with the goal state on the tracing
  channel.

  \item @{ML PRIMITIVE}~@{text rule} turns a primitive inference rule
  into a tactic with unique result.  Exception @{ML THM} is considered
  a regular tactic failure and produces an empty result; other
  exceptions are passed through.

  \item @{ML SUBGOAL}~@{text "(fn (subgoal, i) => tactic)"} is the
  most basic form to produce a tactic with subgoal addressing.  The
  given abstraction over the subgoal term and subgoal number allows to
  peek at the relevant information of the full goal state.  The
  subgoal range is checked as required above.

  \item @{ML CSUBGOAL} is similar to @{ML SUBGOAL}, but passes the
  subgoal as @{ML_type cterm} instead of raw @{ML_type term}.  This
  avoids expensive re-certification in situations where the subgoal is
  used directly for primitive inferences.

  \end{description}
*}


subsection {* Resolution and assumption tactics \label{sec:resolve-assume-tac} *}

text {* \emph{Resolution} is the most basic mechanism for refining a
  subgoal using a theorem as object-level rule.
  \emph{Elim-resolution} is particularly suited for elimination rules:
  it resolves with a rule, proves its first premise by assumption, and
  finally deletes that assumption from any new subgoals.
  \emph{Destruct-resolution} is like elim-resolution, but the given
  destruction rules are first turned into canonical elimination
  format.  \emph{Forward-resolution} is like destruct-resolution, but
  without deleting the selected assumption.  The @{text "r/e/d/f"}
  naming convention is maintained for several different kinds of
  resolution rules and tactics.

  Assumption tactics close a subgoal by unifying some of its premises
  against its conclusion.

  \medskip All the tactics in this section operate on a subgoal
  designated by a positive integer.  Other subgoals might be affected
  indirectly, due to instantiation of schematic variables.

  There are various sources of non-determinism, the tactic result
  sequence enumerates all possibilities of the following choices (if
  applicable):

  \begin{enumerate}

  \item selecting one of the rules given as argument to the tactic;

  \item selecting a subgoal premise to eliminate, unifying it against
  the first premise of the rule;

  \item unifying the conclusion of the subgoal to the conclusion of
  the rule.

  \end{enumerate}

  Recall that higher-order unification may produce multiple results
  that are enumerated here.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML resolve_tac: "thm list -> int -> tactic"} \\
  @{index_ML eresolve_tac: "thm list -> int -> tactic"} \\
  @{index_ML dresolve_tac: "thm list -> int -> tactic"} \\
  @{index_ML forward_tac: "thm list -> int -> tactic"} \\[1ex]
  @{index_ML assume_tac: "int -> tactic"} \\
  @{index_ML eq_assume_tac: "int -> tactic"} \\[1ex]
  @{index_ML match_tac: "thm list -> int -> tactic"} \\
  @{index_ML ematch_tac: "thm list -> int -> tactic"} \\
  @{index_ML dmatch_tac: "thm list -> int -> tactic"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML resolve_tac}~@{text "thms i"} refines the goal state
  using the given theorems, which should normally be introduction
  rules.  The tactic resolves a rule's conclusion with subgoal @{text
  i}, replacing it by the corresponding versions of the rule's
  premises.

  \item @{ML eresolve_tac}~@{text "thms i"} performs elim-resolution
  with the given theorems, which should normally be elimination rules.

  \item @{ML dresolve_tac}~@{text "thms i"} performs
  destruct-resolution with the given theorems, which should normally
  be destruction rules.  This replaces an assumption by the result of
  applying one of the rules.

  \item @{ML forward_tac} is like @{ML dresolve_tac} except that the
  selected assumption is not deleted.  It applies a rule to an
  assumption, adding the result as a new assumption.

  \item @{ML assume_tac}~@{text i} attempts to solve subgoal @{text i}
  by assumption (modulo higher-order unification).

  \item @{ML eq_assume_tac} is similar to @{ML assume_tac}, but checks
  only for immediate @{text "\<alpha>"}-convertibility instead of using
  unification.  It succeeds (with a unique next state) if one of the
  assumptions is equal to the subgoal's conclusion.  Since it does not
  instantiate variables, it cannot make other subgoals unprovable.

  \item @{ML match_tac}, @{ML ematch_tac}, and @{ML dmatch_tac} are
  similar to @{ML resolve_tac}, @{ML eresolve_tac}, and @{ML
  dresolve_tac}, respectively, but do not instantiate schematic
  variables in the goal state.

  Flexible subgoals are not updated at will, but are left alone.
  Strictly speaking, matching means to treat the unknowns in the goal
  state as constants; these tactics merely discard unifiers that would
  update the goal state.

  \end{description}
*}


subsection {* Explicit instantiation within a subgoal context *}

text {* The main resolution tactics (\secref{sec:resolve-assume-tac})
  use higher-order unification, which works well in many practical
  situations despite its daunting theoretical properties.
  Nonetheless, there are important problem classes where unguided
  higher-order unification is not so useful.  This typically involves
  rules like universal elimination, existential introduction, or
  equational substitution.  Here the unification problem involves
  fully flexible @{text "?P ?x"} schemes, which are hard to manage
  without further hints.

  By providing a (small) rigid term for @{text "?x"} explicitly, the
  remaining unification problem is to assign a (large) term to @{text
  "?P"}, according to the shape of the given subgoal.  This is
  sufficiently well-behaved in most practical situations.

  \medskip Isabelle provides separate versions of the standard @{text
  "r/e/d/f"} resolution tactics that allow to provide explicit
  instantiations of unknowns of the given rule, wrt.\ terms that refer
  to the implicit context of the selected subgoal.

  An instantiation consists of a list of pairs of the form @{text
  "(?x, t)"}, where @{text ?x} is a schematic variable occurring in
  the given rule, and @{text t} is a term from the current proof
  context, augmented by the local goal parameters of the selected
  subgoal; cf.\ the @{text "focus"} operation described in
  \secref{sec:variables}.

  Entering the syntactic context of a subgoal is a brittle operation,
  because its exact form is somewhat accidental, and the choice of
  bound variable names depends on the presence of other local and
  global names.  Explicit renaming of subgoal parameters prior to
  explicit instantiation might help to achieve a bit more robustness.

  Type instantiations may be given as well, via pairs like @{text
  "(?'a, \<tau>)"}.  Type instantiations are distinguished from term
  instantiations by the syntactic form of the schematic variable.
  Types are instantiated before terms are.  Since term instantiation
  already performs type-inference as expected, explicit type
  instantiations are seldom necessary.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML res_inst_tac: "Proof.context -> (indexname * string) list -> thm -> int -> tactic"} \\
  @{index_ML eres_inst_tac: "Proof.context -> (indexname * string) list -> thm -> int -> tactic"} \\
  @{index_ML dres_inst_tac: "Proof.context -> (indexname * string) list -> thm -> int -> tactic"} \\
  @{index_ML forw_inst_tac: "Proof.context -> (indexname * string) list -> thm -> int -> tactic"} \\[1ex]
  @{index_ML rename_tac: "string list -> int -> tactic"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML res_inst_tac}~@{text "ctxt insts thm i"} instantiates the
  rule @{text thm} with the instantiations @{text insts}, as described
  above, and then performs resolution on subgoal @{text i}.
  
  \item @{ML eres_inst_tac} is like @{ML res_inst_tac}, but performs
  elim-resolution.

  \item @{ML dres_inst_tac} is like @{ML res_inst_tac}, but performs
  destruct-resolution.

  \item @{ML forw_inst_tac} is like @{ML dres_inst_tac} except that
  the selected assumption is not deleted.

  \item @{ML rename_tac}~@{text "names i"} renames the innermost
  parameters of subgoal @{text i} according to the provided @{text
  names} (which need to be distinct indentifiers).

  \end{description}
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

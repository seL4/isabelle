(*:maxLineLen=78:*)

theory Tactic
imports Base
begin

chapter \<open>Tactical reasoning\<close>

text \<open>
  Tactical reasoning works by refining an initial claim in a backwards
  fashion, until a solved form is reached. A \<open>goal\<close> consists of several
  subgoals that need to be solved in order to achieve the main statement; zero
  subgoals means that the proof may be finished. A \<open>tactic\<close> is a refinement
  operation that maps a goal to a lazy sequence of potential successors. A
  \<open>tactical\<close> is a combinator for composing tactics.
\<close>


section \<open>Goals \label{sec:tactical-goals}\<close>

text \<open>
  Isabelle/Pure represents a goal as a theorem stating that the subgoals imply
  the main goal: \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>. The outermost goal structure is that of
  a Horn Clause: i.e.\ an iterated implication without any quantifiers\<^footnote>\<open>Recall
  that outermost \<open>\<And>x. \<phi>[x]\<close> is always represented via schematic variables in
  the body: \<open>\<phi>[?x]\<close>. These variables may get instantiated during the course of
  reasoning.\<close>. For \<open>n = 0\<close> a goal is called ``solved''.

  The structure of each subgoal \<open>A\<^sub>i\<close> is that of a general Hereditary Harrop
  Formula \<open>\<And>x\<^sub>1 \<dots> \<And>x\<^sub>k. H\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> H\<^sub>m \<Longrightarrow> B\<close>. Here \<open>x\<^sub>1, \<dots>, x\<^sub>k\<close> are goal
  parameters, i.e.\ arbitrary-but-fixed entities of certain types, and \<open>H\<^sub>1,
  \<dots>, H\<^sub>m\<close> are goal hypotheses, i.e.\ facts that may be assumed locally.
  Together, this forms the goal context of the conclusion \<open>B\<close> to be
  established. The goal hypotheses may be again arbitrary Hereditary Harrop
  Formulas, although the level of nesting rarely exceeds 1--2 in practice.

  The main conclusion \<open>C\<close> is internally marked as a protected proposition,
  which is represented explicitly by the notation \<open>#C\<close> here. This ensures that
  the decomposition into subgoals and main conclusion is well-defined for
  arbitrarily structured claims.

  \<^medskip>
  Basic goal management is performed via the following Isabelle/Pure rules:

  \[
  \infer[\<open>(init)\<close>]{\<open>C \<Longrightarrow> #C\<close>}{} \qquad
  \infer[\<open>(finish)\<close>]{\<open>C\<close>}{\<open>#C\<close>}
  \]

  \<^medskip>
  The following low-level variants admit general reasoning with protected
  propositions:

  \[
  \infer[\<open>(protect n)\<close>]{\<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> #C\<close>}{\<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>}
  \]
  \[
  \infer[\<open>(conclude)\<close>]{\<open>A \<Longrightarrow> \<dots> \<Longrightarrow> C\<close>}{\<open>A \<Longrightarrow> \<dots> \<Longrightarrow> #C\<close>}
  \]
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Goal.init: "cterm -> thm"} \\
  @{define_ML Goal.finish: "Proof.context -> thm -> thm"} \\
  @{define_ML Goal.protect: "int -> thm -> thm"} \\
  @{define_ML Goal.conclude: "thm -> thm"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Goal.init\<close>~\<open>C\<close> initializes a tactical goal from the well-formed
  proposition \<open>C\<close>.

  \<^descr> \<^ML>\<open>Goal.finish\<close>~\<open>ctxt thm\<close> checks whether theorem \<open>thm\<close> is a solved
  goal (no subgoals), and concludes the result by removing the goal
  protection. The context is only required for printing error messages.

  \<^descr> \<^ML>\<open>Goal.protect\<close>~\<open>n thm\<close> protects the statement of theorem \<open>thm\<close>. The
  parameter \<open>n\<close> indicates the number of premises to be retained.

  \<^descr> \<^ML>\<open>Goal.conclude\<close>~\<open>thm\<close> removes the goal protection, even if there are
  pending subgoals.
\<close>


section \<open>Tactics\label{sec:tactics}\<close>

text \<open>
  A \<open>tactic\<close> is a function \<open>goal \<rightarrow> goal\<^sup>*\<^sup>*\<close> that maps a given goal state
  (represented as a theorem, cf.\ \secref{sec:tactical-goals}) to a lazy
  sequence of potential successor states. The underlying sequence
  implementation is lazy both in head and tail, and is purely functional in
  \<^emph>\<open>not\<close> supporting memoing.\<^footnote>\<open>The lack of memoing and the strict nature of ML
  requires some care when working with low-level sequence operations, to avoid
  duplicate or premature evaluation of results. It also means that modified
  runtime behavior, such as timeout, is very hard to achieve for general
  tactics.\<close>

  An \<^emph>\<open>empty result sequence\<close> means that the tactic has failed: in a compound
  tactic expression other tactics might be tried instead, or the whole
  refinement step might fail outright, producing a toplevel error message in
  the end. When implementing tactics from scratch, one should take care to
  observe the basic protocol of mapping regular error conditions to an empty
  result; only serious faults should emerge as exceptions.

  By enumerating \<^emph>\<open>multiple results\<close>, a tactic can easily express the
  potential outcome of an internal search process. There are also combinators
  for building proof tools that involve search systematically, see also
  \secref{sec:tacticals}.

  \<^medskip>
  As explained before, a goal state essentially consists of a list of subgoals
  that imply the main goal (conclusion). Tactics may operate on all subgoals
  or on a particularly specified subgoal, but must not change the main
  conclusion (apart from instantiating schematic goal variables).

  Tactics with explicit \<^emph>\<open>subgoal addressing\<close> are of the form \<open>int \<rightarrow> tactic\<close>
  and may be applied to a particular subgoal (counting from 1). If the subgoal
  number is out of range, the tactic should fail with an empty result
  sequence, but must not raise an exception!

  Operating on a particular subgoal means to replace it by an interval of zero
  or more subgoals in the same place; other subgoals must not be affected,
  apart from instantiating schematic variables ranging over the whole goal
  state.

  A common pattern of composing tactics with subgoal addressing is to try the
  first one, and then the second one only if the subgoal has not been solved
  yet. Special care is required here to avoid bumping into unrelated subgoals
  that happen to come after the original subgoal. Assuming that there is only
  a single initial subgoal is a very common error when implementing tactics!

  Tactics with internal subgoal addressing should expose the subgoal index as
  \<open>int\<close> argument in full generality; a hardwired subgoal 1 is not acceptable.
  
  \<^medskip>
  The main well-formedness conditions for proper tactics are summarized as
  follows.

    \<^item> General tactic failure is indicated by an empty result, only serious
    faults may produce an exception.

    \<^item> The main conclusion must not be changed, apart from instantiating
    schematic variables.

    \<^item> A tactic operates either uniformly on all subgoals, or specifically on a
    selected subgoal (without bumping into unrelated subgoals).

    \<^item> Range errors in subgoal addressing produce an empty result.

  Some of these conditions are checked by higher-level goal infrastructure
  (\secref{sec:struct-goals}); others are not checked explicitly, and
  violating them merely results in ill-behaved tactics experienced by the user
  (e.g.\ tactics that insist in being applicable only to singleton goals, or
  prevent composition via standard tacticals such as \<^ML>\<open>REPEAT\<close>).
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type tactic = "thm -> thm Seq.seq"} \\
  @{define_ML no_tac: tactic} \\
  @{define_ML all_tac: tactic} \\
  @{define_ML print_tac: "Proof.context -> string -> tactic"} \\[1ex]
  @{define_ML PRIMITIVE: "(thm -> thm) -> tactic"} \\[1ex]
  @{define_ML SUBGOAL: "(term * int -> tactic) -> int -> tactic"} \\
  @{define_ML CSUBGOAL: "(cterm * int -> tactic) -> int -> tactic"} \\
  @{define_ML SELECT_GOAL: "tactic -> int -> tactic"} \\
  @{define_ML PREFER_GOAL: "tactic -> int -> tactic"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>tactic\<close> represents tactics. The well-formedness conditions
  described above need to be observed. See also \<^file>\<open>~~/src/Pure/General/seq.ML\<close>
  for the underlying implementation of lazy sequences.

  \<^descr> Type \<^ML_type>\<open>int -> tactic\<close> represents tactics with explicit subgoal
  addressing, with well-formedness conditions as described above.

  \<^descr> \<^ML>\<open>no_tac\<close> is a tactic that always fails, returning the empty sequence.

  \<^descr> \<^ML>\<open>all_tac\<close> is a tactic that always succeeds, returning a singleton
  sequence with unchanged goal state.

  \<^descr> \<^ML>\<open>print_tac\<close>~\<open>ctxt message\<close> is like \<^ML>\<open>all_tac\<close>, but prints a message
  together with the goal state on the tracing channel.

  \<^descr> \<^ML>\<open>PRIMITIVE\<close>~\<open>rule\<close> turns a primitive inference rule into a tactic with
  unique result. Exception \<^ML>\<open>THM\<close> is considered a regular tactic failure
  and produces an empty result; other exceptions are passed through.

  \<^descr> \<^ML>\<open>SUBGOAL\<close>~\<open>(fn (subgoal, i) => tactic)\<close> is the most basic form to
  produce a tactic with subgoal addressing. The given abstraction over the
  subgoal term and subgoal number allows to peek at the relevant information
  of the full goal state. The subgoal range is checked as required above.

  \<^descr> \<^ML>\<open>CSUBGOAL\<close> is similar to \<^ML>\<open>SUBGOAL\<close>, but passes the subgoal as
  \<^ML_type>\<open>cterm\<close> instead of raw \<^ML_type>\<open>term\<close>. This avoids expensive
  re-certification in situations where the subgoal is used directly for
  primitive inferences.

  \<^descr> \<^ML>\<open>SELECT_GOAL\<close>~\<open>tac i\<close> confines a tactic to the specified subgoal \<open>i\<close>.
  This rearranges subgoals and the main goal protection
  (\secref{sec:tactical-goals}), while retaining the syntactic context of the
  overall goal state (concerning schematic variables etc.).

  \<^descr> \<^ML>\<open>PREFER_GOAL\<close>~\<open>tac i\<close> rearranges subgoals to put \<open>i\<close> in front. This is
  similar to \<^ML>\<open>SELECT_GOAL\<close>, but without changing the main goal protection.
\<close>


subsection \<open>Resolution and assumption tactics \label{sec:resolve-assume-tac}\<close>

text \<open>
  \<^emph>\<open>Resolution\<close> is the most basic mechanism for refining a subgoal using a
  theorem as object-level rule. \<^emph>\<open>Elim-resolution\<close> is particularly suited for
  elimination rules: it resolves with a rule, proves its first premise by
  assumption, and finally deletes that assumption from any new subgoals.
  \<^emph>\<open>Destruct-resolution\<close> is like elim-resolution, but the given destruction
  rules are first turned into canonical elimination format.
  \<^emph>\<open>Forward-resolution\<close> is like destruct-resolution, but without deleting the
  selected assumption. The \<open>r/e/d/f\<close> naming convention is maintained for
  several different kinds of resolution rules and tactics.

  Assumption tactics close a subgoal by unifying some of its premises against
  its conclusion.

  \<^medskip>
  All the tactics in this section operate on a subgoal designated by a
  positive integer. Other subgoals might be affected indirectly, due to
  instantiation of schematic variables.

  There are various sources of non-determinism, the tactic result sequence
  enumerates all possibilities of the following choices (if applicable):

    \<^enum> selecting one of the rules given as argument to the tactic;

    \<^enum> selecting a subgoal premise to eliminate, unifying it against the first
    premise of the rule;

    \<^enum> unifying the conclusion of the subgoal to the conclusion of the rule.

  Recall that higher-order unification may produce multiple results that are
  enumerated here.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML resolve_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML eresolve_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML dresolve_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML forward_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML biresolve_tac: "Proof.context -> (bool * thm) list -> int -> tactic"} \\[1ex]
  @{define_ML assume_tac: "Proof.context -> int -> tactic"} \\
  @{define_ML eq_assume_tac: "int -> tactic"} \\[1ex]
  @{define_ML match_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML ematch_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML dmatch_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML bimatch_tac: "Proof.context -> (bool * thm) list -> int -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>resolve_tac\<close>~\<open>ctxt thms i\<close> refines the goal state using the given
  theorems, which should normally be introduction rules. The tactic resolves a
  rule's conclusion with subgoal \<open>i\<close>, replacing it by the corresponding
  versions of the rule's premises.

  \<^descr> \<^ML>\<open>eresolve_tac\<close>~\<open>ctxt thms i\<close> performs elim-resolution with the given
  theorems, which are normally be elimination rules.

  Note that \<^ML_text>\<open>eresolve_tac ctxt [asm_rl]\<close> is equivalent to \<^ML_text>\<open>assume_tac ctxt\<close>, which facilitates mixing of assumption steps with
  genuine eliminations.

  \<^descr> \<^ML>\<open>dresolve_tac\<close>~\<open>ctxt thms i\<close> performs destruct-resolution with the
  given theorems, which should normally be destruction rules. This replaces an
  assumption by the result of applying one of the rules.

  \<^descr> \<^ML>\<open>forward_tac\<close> is like \<^ML>\<open>dresolve_tac\<close> except that the selected
  assumption is not deleted. It applies a rule to an assumption, adding the
  result as a new assumption.

  \<^descr> \<^ML>\<open>biresolve_tac\<close>~\<open>ctxt brls i\<close> refines the proof state by resolution or
  elim-resolution on each rule, as indicated by its flag. It affects subgoal
  \<open>i\<close> of the proof state.

  For each pair \<open>(flag, rule)\<close>, it applies resolution if the flag is \<open>false\<close>
  and elim-resolution if the flag is \<open>true\<close>. A single tactic call handles a
  mixture of introduction and elimination rules, which is useful to organize
  the search process systematically in proof tools.

  \<^descr> \<^ML>\<open>assume_tac\<close>~\<open>ctxt i\<close> attempts to solve subgoal \<open>i\<close> by assumption
  (modulo higher-order unification).

  \<^descr> \<^ML>\<open>eq_assume_tac\<close> is similar to \<^ML>\<open>assume_tac\<close>, but checks only for
  immediate \<open>\<alpha>\<close>-convertibility instead of using unification. It succeeds (with
  a unique next state) if one of the assumptions is equal to the subgoal's
  conclusion. Since it does not instantiate variables, it cannot make other
  subgoals unprovable.

  \<^descr> \<^ML>\<open>match_tac\<close>, \<^ML>\<open>ematch_tac\<close>, \<^ML>\<open>dmatch_tac\<close>, and \<^ML>\<open>bimatch_tac\<close>
  are similar to \<^ML>\<open>resolve_tac\<close>, \<^ML>\<open>eresolve_tac\<close>, \<^ML>\<open>dresolve_tac\<close>,
  and \<^ML>\<open>biresolve_tac\<close>, respectively, but do not instantiate schematic
  variables in the goal state.\<^footnote>\<open>Strictly speaking, matching means to treat the
  unknowns in the goal state as constants, but these tactics merely discard
  unifiers that would update the goal state. In rare situations (where the
  conclusion and goal state have flexible terms at the same position), the
  tactic will fail even though an acceptable unifier exists.\<close> These tactics
  were written for a specific application within the classical reasoner.

  Flexible subgoals are not updated at will, but are left alone.
\<close>


subsection \<open>Explicit instantiation within a subgoal context\<close>

text \<open>
  The main resolution tactics (\secref{sec:resolve-assume-tac}) use
  higher-order unification, which works well in many practical situations
  despite its daunting theoretical properties. Nonetheless, there are
  important problem classes where unguided higher-order unification is not so
  useful. This typically involves rules like universal elimination,
  existential introduction, or equational substitution. Here the unification
  problem involves fully flexible \<open>?P ?x\<close> schemes, which are hard to manage
  without further hints.

  By providing a (small) rigid term for \<open>?x\<close> explicitly, the remaining
  unification problem is to assign a (large) term to \<open>?P\<close>, according to the
  shape of the given subgoal. This is sufficiently well-behaved in most
  practical situations.

  \<^medskip>
  Isabelle provides separate versions of the standard \<open>r/e/d/f\<close> resolution
  tactics that allow to provide explicit instantiations of unknowns of the
  given rule, wrt.\ terms that refer to the implicit context of the selected
  subgoal.

  An instantiation consists of a list of pairs of the form \<open>(?x, t)\<close>, where
  \<open>?x\<close> is a schematic variable occurring in the given rule, and \<open>t\<close> is a term
  from the current proof context, augmented by the local goal parameters of
  the selected subgoal; cf.\ the \<open>focus\<close> operation described in
  \secref{sec:variables}.

  Entering the syntactic context of a subgoal is a brittle operation, because
  its exact form is somewhat accidental, and the choice of bound variable
  names depends on the presence of other local and global names. Explicit
  renaming of subgoal parameters prior to explicit instantiation might help to
  achieve a bit more robustness.

  Type instantiations may be given as well, via pairs like \<open>(?'a, \<tau>)\<close>. Type
  instantiations are distinguished from term instantiations by the syntactic
  form of the schematic variable. Types are instantiated before terms are.
  Since term instantiation already performs simple type-inference, so explicit
  type instantiations are seldom necessary.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Rule_Insts.res_inst_tac: "Proof.context ->
    ((indexname * Position.T) * string) list -> (binding * string option * mixfix) list ->
    thm -> int -> tactic"} \\
  @{define_ML Rule_Insts.eres_inst_tac: "Proof.context ->
    ((indexname * Position.T) * string) list -> (binding * string option * mixfix) list ->
    thm -> int -> tactic"} \\
  @{define_ML Rule_Insts.dres_inst_tac: "Proof.context ->
    ((indexname * Position.T) * string) list -> (binding * string option * mixfix) list ->
    thm -> int -> tactic"} \\
  @{define_ML Rule_Insts.forw_inst_tac: "Proof.context ->
    ((indexname * Position.T) * string) list -> (binding * string option * mixfix) list ->
    thm -> int -> tactic"} \\
  @{define_ML Rule_Insts.subgoal_tac: "Proof.context -> string ->
    (binding * string option * mixfix) list -> int -> tactic"} \\
  @{define_ML Rule_Insts.thin_tac: "Proof.context -> string ->
    (binding * string option * mixfix) list -> int -> tactic"} \\
  @{define_ML rename_tac: "string list -> int -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Rule_Insts.res_inst_tac\<close>~\<open>ctxt insts thm i\<close> instantiates the rule
  \<open>thm\<close> with the instantiations \<open>insts\<close>, as described above, and then performs
  resolution on subgoal \<open>i\<close>.
  
  \<^descr> \<^ML>\<open>Rule_Insts.eres_inst_tac\<close> is like \<^ML>\<open>Rule_Insts.res_inst_tac\<close>, but
  performs elim-resolution.

  \<^descr> \<^ML>\<open>Rule_Insts.dres_inst_tac\<close> is like \<^ML>\<open>Rule_Insts.res_inst_tac\<close>, but
  performs destruct-resolution.

  \<^descr> \<^ML>\<open>Rule_Insts.forw_inst_tac\<close> is like \<^ML>\<open>Rule_Insts.dres_inst_tac\<close>
  except that the selected assumption is not deleted.

  \<^descr> \<^ML>\<open>Rule_Insts.subgoal_tac\<close>~\<open>ctxt \<phi> i\<close> adds the proposition \<open>\<phi>\<close> as local
  premise to subgoal \<open>i\<close>, and poses the same as a new subgoal \<open>i + 1\<close> (in the
  original context).

  \<^descr> \<^ML>\<open>Rule_Insts.thin_tac\<close>~\<open>ctxt \<phi> i\<close> deletes the specified premise from
  subgoal \<open>i\<close>. Note that \<open>\<phi>\<close> may contain schematic variables, to abbreviate
  the intended proposition; the first matching subgoal premise will be
  deleted. Removing useless premises from a subgoal increases its readability
  and can make search tactics run faster.

  \<^descr> \<^ML>\<open>rename_tac\<close>~\<open>names i\<close> renames the innermost parameters of subgoal \<open>i\<close>
  according to the provided \<open>names\<close> (which need to be distinct identifiers).


  For historical reasons, the above instantiation tactics take unparsed string
  arguments, which makes them hard to use in general ML code. The slightly
  more advanced \<^ML>\<open>Subgoal.FOCUS\<close> combinator of \secref{sec:struct-goals}
  allows to refer to internal goal structure with explicit context management.
\<close>


subsection \<open>Rearranging goal states\<close>

text \<open>
  In rare situations there is a need to rearrange goal states: either the
  overall collection of subgoals, or the local structure of a subgoal. Various
  administrative tactics allow to operate on the concrete presentation these
  conceptual sets of formulae.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML rotate_tac: "int -> int -> tactic"} \\
  @{define_ML distinct_subgoals_tac: tactic} \\
  @{define_ML flexflex_tac: "Proof.context -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>rotate_tac\<close>~\<open>n i\<close> rotates the premises of subgoal \<open>i\<close> by \<open>n\<close>
  positions: from right to left if \<open>n\<close> is positive, and from left to right if
  \<open>n\<close> is negative.

  \<^descr> \<^ML>\<open>distinct_subgoals_tac\<close> removes duplicate subgoals from a proof state.
  This is potentially inefficient.

  \<^descr> \<^ML>\<open>flexflex_tac\<close> removes all flex-flex pairs from the proof state by
  applying the trivial unifier. This drastic step loses information. It is
  already part of the Isar infrastructure for facts resulting from goals, and
  rarely needs to be invoked manually.

  Flex-flex constraints arise from difficult cases of higher-order
  unification. To prevent this, use \<^ML>\<open>Rule_Insts.res_inst_tac\<close> to
  instantiate some variables in a rule. Normally flex-flex constraints can be
  ignored; they often disappear as unknowns get instantiated.
\<close>


subsection \<open>Raw composition: resolution without lifting\<close>

text \<open>
  Raw composition of two rules means resolving them without prior lifting or
  renaming of unknowns. This low-level operation, which underlies the
  resolution tactics, may occasionally be useful for special effects.
  Schematic variables are not renamed by default, so beware of clashes!
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML compose_tac: "Proof.context -> (bool * thm * int) -> int -> tactic"} \\
  @{define_ML Drule.compose: "thm * int * thm -> thm"} \\
  @{define_ML_infix COMP: "thm * thm -> thm"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>compose_tac\<close>~\<open>ctxt (flag, rule, m) i\<close> refines subgoal \<open>i\<close> using
  \<open>rule\<close>, without lifting. The \<open>rule\<close> is taken to have the form \<open>\<psi>\<^sub>1 \<Longrightarrow> \<dots> \<psi>\<^sub>m \<Longrightarrow>
  \<psi>\<close>, where \<open>\<psi>\<close> need not be atomic; thus \<open>m\<close> determines the number of new
  subgoals. If \<open>flag\<close> is \<open>true\<close> then it performs elim-resolution --- it solves
  the first premise of \<open>rule\<close> by assumption and deletes that assumption.

  \<^descr> \<^ML>\<open>Drule.compose\<close>~\<open>(thm\<^sub>1, i, thm\<^sub>2)\<close> uses \<open>thm\<^sub>1\<close>, regarded as an
  atomic formula, to solve premise \<open>i\<close> of \<open>thm\<^sub>2\<close>. Let \<open>thm\<^sub>1\<close> and \<open>thm\<^sub>2\<close> be
  \<open>\<psi>\<close> and \<open>\<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> \<phi>\<close>. The unique \<open>s\<close> that unifies \<open>\<psi>\<close> and \<open>\<phi>\<^sub>i\<close> yields
  the theorem \<open>(\<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>i\<^sub>-\<^sub>1 \<Longrightarrow> \<phi>\<^sub>i\<^sub>+\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> \<phi>)s\<close>. Multiple results are
  considered as error (exception \<^ML>\<open>THM\<close>).

  \<^descr> \<open>thm\<^sub>1 COMP thm\<^sub>2\<close> is the same as \<open>Drule.compose (thm\<^sub>1, 1, thm\<^sub>2)\<close>.


  \begin{warn}
  These low-level operations are stepping outside the structure imposed by
  regular rule resolution. Used without understanding of the consequences,
  they may produce results that cause problems with standard rules and tactics
  later on.
  \end{warn}
\<close>


section \<open>Tacticals \label{sec:tacticals}\<close>

text \<open>
  A \<^emph>\<open>tactical\<close> is a functional combinator for building up complex tactics
  from simpler ones. Common tacticals perform sequential composition,
  disjunctive choice, iteration, or goal addressing. Various search strategies
  may be expressed via tacticals.
\<close>


subsection \<open>Combining tactics\<close>

text \<open>
  Sequential composition and alternative choices are the most basic ways to
  combine tactics, similarly to ``\<^verbatim>\<open>,\<close>'' and ``\<^verbatim>\<open>|\<close>'' in Isar method notation.
  This corresponds to \<^ML_op>\<open>THEN\<close> and \<^ML_op>\<open>ORELSE\<close> in ML, but there
  are further possibilities for fine-tuning alternation of tactics such as
  \<^ML_op>\<open>APPEND\<close>. Further details become visible in ML due to explicit
  subgoal addressing.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_infix "THEN": "tactic * tactic -> tactic"} \\
  @{define_ML_infix "ORELSE": "tactic * tactic -> tactic"} \\
  @{define_ML_infix "APPEND": "tactic * tactic -> tactic"} \\
  @{define_ML "EVERY": "tactic list -> tactic"} \\
  @{define_ML "FIRST": "tactic list -> tactic"} \\[0.5ex]

  @{define_ML_infix "THEN'": "('a -> tactic) * ('a -> tactic) -> 'a -> tactic"} \\
  @{define_ML_infix "ORELSE'": "('a -> tactic) * ('a -> tactic) -> 'a -> tactic"} \\
  @{define_ML_infix "APPEND'": "('a -> tactic) * ('a -> tactic) -> 'a -> tactic"} \\
  @{define_ML "EVERY'": "('a -> tactic) list -> 'a -> tactic"} \\
  @{define_ML "FIRST'": "('a -> tactic) list -> 'a -> tactic"} \\
  \end{mldecls}

  \<^descr> \<open>tac\<^sub>1\<close>~\<^ML_op>\<open>THEN\<close>~\<open>tac\<^sub>2\<close> is the sequential composition of \<open>tac\<^sub>1\<close> and
  \<open>tac\<^sub>2\<close>. Applied to a goal state, it returns all states reachable in two
  steps by applying \<open>tac\<^sub>1\<close> followed by \<open>tac\<^sub>2\<close>. First, it applies \<open>tac\<^sub>1\<close> to
  the goal state, getting a sequence of possible next states; then, it applies
  \<open>tac\<^sub>2\<close> to each of these and concatenates the results to produce again one
  flat sequence of states.

  \<^descr> \<open>tac\<^sub>1\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>tac\<^sub>2\<close> makes a choice between \<open>tac\<^sub>1\<close> and
  \<open>tac\<^sub>2\<close>. Applied to a state, it tries \<open>tac\<^sub>1\<close> and returns the result if
  non-empty; if \<open>tac\<^sub>1\<close> fails then it uses \<open>tac\<^sub>2\<close>. This is a deterministic
  choice: if \<open>tac\<^sub>1\<close> succeeds then \<open>tac\<^sub>2\<close> is excluded from the result.

  \<^descr> \<open>tac\<^sub>1\<close>~\<^ML_op>\<open>APPEND\<close>~\<open>tac\<^sub>2\<close> concatenates the possible results of
  \<open>tac\<^sub>1\<close> and \<open>tac\<^sub>2\<close>. Unlike \<^ML_op>\<open>ORELSE\<close> there is \<^emph>\<open>no commitment\<close> to
  either tactic, so \<^ML_op>\<open>APPEND\<close> helps to avoid incompleteness during
  search, at the cost of potential inefficiencies.

  \<^descr> \<^ML>\<open>EVERY\<close>~\<open>[tac\<^sub>1, \<dots>, tac\<^sub>n]\<close> abbreviates \<open>tac\<^sub>1\<close>~\<^ML_op>\<open>THEN\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>THEN\<close>~\<open>tac\<^sub>n\<close>. Note that \<^ML>\<open>EVERY []\<close> is the same as
  \<^ML>\<open>all_tac\<close>: it always succeeds.

  \<^descr> \<^ML>\<open>FIRST\<close>~\<open>[tac\<^sub>1, \<dots>, tac\<^sub>n]\<close> abbreviates \<open>tac\<^sub>1\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>tac\<^sub>n\<close>. Note that \<^ML>\<open>FIRST []\<close> is the
  same as \<^ML>\<open>no_tac\<close>: it always fails.

  \<^descr> \<^ML_op>\<open>THEN'\<close> is the lifted version of \<^ML_op>\<open>THEN\<close>, for tactics
  with explicit subgoal addressing. So \<open>(tac\<^sub>1\<close>~\<^ML_op>\<open>THEN'\<close>~\<open>tac\<^sub>2) i\<close> is
  the same as \<open>(tac\<^sub>1 i\<close>~\<^ML_op>\<open>THEN\<close>~\<open>tac\<^sub>2 i)\<close>.

  The other primed tacticals work analogously.
\<close>


subsection \<open>Repetition tacticals\<close>

text \<open>
  These tacticals provide further control over repetition of tactics, beyond
  the stylized forms of ``\<^verbatim>\<open>?\<close>'' and ``\<^verbatim>\<open>+\<close>'' in Isar method expressions.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML "TRY": "tactic -> tactic"} \\
  @{define_ML "REPEAT": "tactic -> tactic"} \\
  @{define_ML "REPEAT1": "tactic -> tactic"} \\
  @{define_ML "REPEAT_DETERM": "tactic -> tactic"} \\
  @{define_ML "REPEAT_DETERM_N": "int -> tactic -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>TRY\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and returns the resulting
  sequence, if non-empty; otherwise it returns the original state. Thus, it
  applies \<open>tac\<close> at most once.

  Note that for tactics with subgoal addressing, the combinator can be applied
  via functional composition: \<^ML>\<open>TRY\<close>~\<^ML_op>\<open>o\<close>~\<open>tac\<close>. There is no need
  for \<^verbatim>\<open>TRY'\<close>.

  \<^descr> \<^ML>\<open>REPEAT\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and, recursively, to
  each element of the resulting sequence. The resulting sequence consists of
  those states that make \<open>tac\<close> fail. Thus, it applies \<open>tac\<close> as many times as
  possible (including zero times), and allows backtracking over each
  invocation of \<open>tac\<close>. \<^ML>\<open>REPEAT\<close> is more general than \<^ML>\<open>REPEAT_DETERM\<close>,
  but requires more space.

  \<^descr> \<^ML>\<open>REPEAT1\<close>~\<open>tac\<close> is like \<^ML>\<open>REPEAT\<close>~\<open>tac\<close> but it always applies \<open>tac\<close>
  at least once, failing if this is impossible.

  \<^descr> \<^ML>\<open>REPEAT_DETERM\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and,
  recursively, to the head of the resulting sequence. It returns the first
  state to make \<open>tac\<close> fail. It is deterministic, discarding alternative
  outcomes.

  \<^descr> \<^ML>\<open>REPEAT_DETERM_N\<close>~\<open>n tac\<close> is like \<^ML>\<open>REPEAT_DETERM\<close>~\<open>tac\<close> but the
  number of repetitions is bound by \<open>n\<close> (where \<^ML>\<open>~1\<close> means \<open>\<infinity>\<close>).
\<close>

text %mlex \<open>
  The basic tactics and tacticals considered above follow some algebraic laws:

  \<^item> \<^ML>\<open>all_tac\<close> is the identity element of the tactical \<^ML_op>\<open>THEN\<close>.

  \<^item> \<^ML>\<open>no_tac\<close> is the identity element of \<^ML_op>\<open>ORELSE\<close> and \<^ML_op>\<open>APPEND\<close>. Also, it is a zero element for \<^ML_op>\<open>THEN\<close>, which means that
  \<open>tac\<close>~\<^ML_op>\<open>THEN\<close>~\<^ML>\<open>no_tac\<close> is equivalent to \<^ML>\<open>no_tac\<close>.

  \<^item> \<^ML>\<open>TRY\<close> and \<^ML>\<open>REPEAT\<close> can be expressed as (recursive) functions over
  more basic combinators (ignoring some internal implementation tricks):
\<close>

ML \<open>
  fun TRY tac = tac ORELSE all_tac;
  fun REPEAT tac st = ((tac THEN REPEAT tac) ORELSE all_tac) st;
\<close>

text \<open>
  If \<open>tac\<close> can return multiple outcomes then so can \<^ML>\<open>REPEAT\<close>~\<open>tac\<close>. \<^ML>\<open>REPEAT\<close> uses \<^ML_op>\<open>ORELSE\<close> and not \<^ML_op>\<open>APPEND\<close>, it applies \<open>tac\<close>
  as many times as possible in each outcome.

  \begin{warn}
  Note the explicit abstraction over the goal state in the ML definition of
  \<^ML>\<open>REPEAT\<close>. Recursive tacticals must be coded in this awkward fashion to
  avoid infinite recursion of eager functional evaluation in Standard ML. The
  following attempt would make \<^ML>\<open>REPEAT\<close>~\<open>tac\<close> loop:
  \end{warn}
\<close>

ML_val \<open>
  (*BAD -- does not terminate!*)
  fun REPEAT tac = (tac THEN REPEAT tac) ORELSE all_tac;
\<close>


subsection \<open>Applying tactics to subgoal ranges\<close>

text \<open>
  Tactics with explicit subgoal addressing \<^ML_type>\<open>int -> tactic\<close> can be
  used together with tacticals that act like ``subgoal quantifiers'': guided
  by success of the body tactic a certain range of subgoals is covered. Thus
  the body tactic is applied to \<^emph>\<open>all\<close> subgoals, \<^emph>\<open>some\<close> subgoal etc.

  Suppose that the goal state has \<open>n \<ge> 0\<close> subgoals. Many of these tacticals
  address subgoal ranges counting downwards from \<open>n\<close> towards \<open>1\<close>. This has the
  fortunate effect that newly emerging subgoals are concatenated in the
  result, without interfering each other. Nonetheless, there might be
  situations where a different order is desired.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML ALLGOALS: "(int -> tactic) -> tactic"} \\
  @{define_ML SOMEGOAL: "(int -> tactic) -> tactic"} \\
  @{define_ML FIRSTGOAL: "(int -> tactic) -> tactic"} \\
  @{define_ML HEADGOAL: "(int -> tactic) -> tactic"} \\
  @{define_ML REPEAT_SOME: "(int -> tactic) -> tactic"} \\
  @{define_ML REPEAT_FIRST: "(int -> tactic) -> tactic"} \\
  @{define_ML RANGE: "(int -> tactic) list -> int -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>ALLGOALS\<close>~\<open>tac\<close> is equivalent to \<open>tac n\<close>~\<^ML_op>\<open>THEN\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>THEN\<close>~\<open>tac 1\<close>. It applies the \<open>tac\<close> to all the subgoals, counting downwards.

  \<^descr> \<^ML>\<open>SOMEGOAL\<close>~\<open>tac\<close> is equivalent to \<open>tac n\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>tac 1\<close>. It applies \<open>tac\<close> to one subgoal, counting downwards.

  \<^descr> \<^ML>\<open>FIRSTGOAL\<close>~\<open>tac\<close> is equivalent to \<open>tac 1\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>ORELSE\<close>~\<open>tac n\<close>. It applies \<open>tac\<close> to one subgoal, counting upwards.

  \<^descr> \<^ML>\<open>HEADGOAL\<close>~\<open>tac\<close> is equivalent to \<open>tac 1\<close>. It applies \<open>tac\<close>
  unconditionally to the first subgoal.

  \<^descr> \<^ML>\<open>REPEAT_SOME\<close>~\<open>tac\<close> applies \<open>tac\<close> once or more to a subgoal, counting
  downwards.

  \<^descr> \<^ML>\<open>REPEAT_FIRST\<close>~\<open>tac\<close> applies \<open>tac\<close> once or more to a subgoal, counting
  upwards.

  \<^descr> \<^ML>\<open>RANGE\<close>~\<open>[tac\<^sub>1, \<dots>, tac\<^sub>k] i\<close> is equivalent to \<open>tac\<^sub>k (i + k -
  1)\<close>~\<^ML_op>\<open>THEN\<close>~\<open>\<dots>\<close>~\<^ML_op>\<open>THEN\<close>~\<open>tac\<^sub>1 i\<close>. It applies the given list of
  tactics to the corresponding range of subgoals, counting downwards.
\<close>


subsection \<open>Control and search tacticals\<close>

text \<open>
  A predicate on theorems \<^ML_type>\<open>thm -> bool\<close> can test whether a goal
  state enjoys some desirable property --- such as having no subgoals. Tactics
  that search for satisfactory goal states are easy to express. The main
  search procedures, depth-first, breadth-first and best-first, are provided
  as tacticals. They generate the search tree by repeatedly applying a given
  tactic.
\<close>


text %mlref ""

subsubsection \<open>Filtering a tactic's results\<close>

text \<open>
  \begin{mldecls}
  @{define_ML FILTER: "(thm -> bool) -> tactic -> tactic"} \\
  @{define_ML CHANGED: "tactic -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>FILTER\<close>~\<open>sat tac\<close> applies \<open>tac\<close> to the goal state and returns a
  sequence consisting of those result goal states that are satisfactory in the
  sense of \<open>sat\<close>.

  \<^descr> \<^ML>\<open>CHANGED\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and returns precisely
  those states that differ from the original state (according to \<^ML>\<open>Thm.eq_thm\<close>). Thus \<^ML>\<open>CHANGED\<close>~\<open>tac\<close> always has some effect on the state.
\<close>


subsubsection \<open>Depth-first search\<close>

text \<open>
  \begin{mldecls}
  @{define_ML DEPTH_FIRST: "(thm -> bool) -> tactic -> tactic"} \\
  @{define_ML DEPTH_SOLVE: "tactic -> tactic"} \\
  @{define_ML DEPTH_SOLVE_1: "tactic -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>DEPTH_FIRST\<close>~\<open>sat tac\<close> returns the goal state if \<open>sat\<close> returns true.
  Otherwise it applies \<open>tac\<close>, then recursively searches from each element of
  the resulting sequence. The code uses a stack for efficiency, in effect
  applying \<open>tac\<close>~\<^ML_op>\<open>THEN\<close>~\<^ML>\<open>DEPTH_FIRST\<close>~\<open>sat tac\<close> to the state.

  \<^descr> \<^ML>\<open>DEPTH_SOLVE\<close>\<open>tac\<close> uses \<^ML>\<open>DEPTH_FIRST\<close> to search for states having
  no subgoals.

  \<^descr> \<^ML>\<open>DEPTH_SOLVE_1\<close>~\<open>tac\<close> uses \<^ML>\<open>DEPTH_FIRST\<close> to search for states
  having fewer subgoals than the given state. Thus, it insists upon solving at
  least one subgoal.
\<close>


subsubsection \<open>Other search strategies\<close>

text \<open>
  \begin{mldecls}
  @{define_ML BREADTH_FIRST: "(thm -> bool) -> tactic -> tactic"} \\
  @{define_ML BEST_FIRST: "(thm -> bool) * (thm -> int) -> tactic -> tactic"} \\
  @{define_ML THEN_BEST_FIRST: "tactic -> (thm -> bool) * (thm -> int) -> tactic -> tactic"} \\
  \end{mldecls}

  These search strategies will find a solution if one exists. However, they do
  not enumerate all solutions; they terminate after the first satisfactory
  result from \<open>tac\<close>.

  \<^descr> \<^ML>\<open>BREADTH_FIRST\<close>~\<open>sat tac\<close> uses breadth-first search to find states for
  which \<open>sat\<close> is true. For most applications, it is too slow.

  \<^descr> \<^ML>\<open>BEST_FIRST\<close>~\<open>(sat, dist) tac\<close> does a heuristic search, using \<open>dist\<close>
  to estimate the distance from a satisfactory state (in the sense of \<open>sat\<close>).
  It maintains a list of states ordered by distance. It applies \<open>tac\<close> to the
  head of this list; if the result contains any satisfactory states, then it
  returns them. Otherwise, \<^ML>\<open>BEST_FIRST\<close> adds the new states to the list,
  and continues.

  The distance function is typically \<^ML>\<open>size_of_thm\<close>, which computes the
  size of the state. The smaller the state, the fewer and simpler subgoals it
  has.

  \<^descr> \<^ML>\<open>THEN_BEST_FIRST\<close>~\<open>tac\<^sub>0 (sat, dist) tac\<close> is like \<^ML>\<open>BEST_FIRST\<close>,
  except that the priority queue initially contains the result of applying
  \<open>tac\<^sub>0\<close> to the goal state. This tactical permits separate tactics for
  starting the search and continuing the search.
\<close>


subsubsection \<open>Auxiliary tacticals for searching\<close>

text \<open>
  \begin{mldecls}
  @{define_ML COND: "(thm -> bool) -> tactic -> tactic -> tactic"} \\
  @{define_ML IF_UNSOLVED: "tactic -> tactic"} \\
  @{define_ML SOLVE: "tactic -> tactic"} \\
  @{define_ML DETERM: "tactic -> tactic"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>COND\<close>~\<open>sat tac\<^sub>1 tac\<^sub>2\<close> applies \<open>tac\<^sub>1\<close> to the goal state if it
  satisfies predicate \<open>sat\<close>, and applies \<open>tac\<^sub>2\<close>. It is a conditional tactical
  in that only one of \<open>tac\<^sub>1\<close> and \<open>tac\<^sub>2\<close> is applied to a goal state. However,
  both \<open>tac\<^sub>1\<close> and \<open>tac\<^sub>2\<close> are evaluated because ML uses eager evaluation.

  \<^descr> \<^ML>\<open>IF_UNSOLVED\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state if it has any
  subgoals, and simply returns the goal state otherwise. Many common tactics,
  such as \<^ML>\<open>resolve_tac\<close>, fail if applied to a goal state that has no
  subgoals.

  \<^descr> \<^ML>\<open>SOLVE\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and then fails iff there
  are subgoals left.

  \<^descr> \<^ML>\<open>DETERM\<close>~\<open>tac\<close> applies \<open>tac\<close> to the goal state and returns the head of
  the resulting sequence. \<^ML>\<open>DETERM\<close> limits the search space by making its
  argument deterministic.
\<close>


subsubsection \<open>Predicates and functions useful for searching\<close>

text \<open>
  \begin{mldecls}
  @{define_ML has_fewer_prems: "int -> thm -> bool"} \\
  @{define_ML Thm.eq_thm: "thm * thm -> bool"} \\
  @{define_ML Thm.eq_thm_prop: "thm * thm -> bool"} \\
  @{define_ML size_of_thm: "thm -> int"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>has_fewer_prems\<close>~\<open>n thm\<close> reports whether \<open>thm\<close> has fewer than \<open>n\<close>
  premises.

  \<^descr> \<^ML>\<open>Thm.eq_thm\<close>~\<open>(thm\<^sub>1, thm\<^sub>2)\<close> reports whether \<open>thm\<^sub>1\<close> and \<open>thm\<^sub>2\<close> are
  equal. Both theorems must have the same conclusions, the same set of
  hypotheses, and the same set of sort hypotheses. Names of bound variables
  are ignored as usual.

  \<^descr> \<^ML>\<open>Thm.eq_thm_prop\<close>~\<open>(thm\<^sub>1, thm\<^sub>2)\<close> reports whether the propositions of
  \<open>thm\<^sub>1\<close> and \<open>thm\<^sub>2\<close> are equal. Names of bound variables are ignored.

  \<^descr> \<^ML>\<open>size_of_thm\<close>~\<open>thm\<close> computes the size of \<open>thm\<close>, namely the number of
  variables, constants and abstractions in its conclusion. It may serve as a
  distance function for \<^ML>\<open>BEST_FIRST\<close>.
\<close>

end

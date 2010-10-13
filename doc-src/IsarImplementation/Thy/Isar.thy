theory Isar
imports Base
begin

chapter {* Isar language elements *}

text {*
  The Isar proof language (see also \cite[\S2]{isabelle-isar-ref})
  consists of three main categories of language elements:

  \begin{enumerate}

  \item Proof \emph{commands} define the primary language of
  transactions of the underlying Isar/VM interpreter.  Typical
  examples are @{command "fix"}, @{command "assume"}, @{command
  "show"}, @{command "proof"}, and @{command "qed"}.

  Composing proof commands according to the rules of the Isar/VM leads
  to expressions of structured proof text, such that both the machine
  and the human reader can give it a meaning as formal reasoning.

  \item Proof \emph{methods} define a secondary language of mixed
  forward-backward refinement steps involving facts and goals.
  Typical examples are @{method rule}, @{method unfold}, and @{method
  simp}.

  Methods can occur in certain well-defined parts of the Isar proof
  language, say as arguments to @{command "proof"}, @{command "qed"},
  or @{command "by"}.

  \item \emph{Attributes} define a tertiary language of small
  annotations to facts being defined or referenced.  Attributes can
  modify both the fact and the context.

  Typical examples are @{attribute symmetric} (which affects the
  fact), and @{attribute intro} (which affects the context).

  \end{enumerate}
*}


section {* Proof commands *}

text {* In principle, Isar proof commands could be defined in
  user-space as well.  The system is built like that in the first
  place: part of the commands are primitive, the other part is defined
  as derived elements.  Adding to the genuine structured proof
  language requires profound understanding of the Isar/VM machinery,
  though, so this is beyond the scope of this manual.

  What can be done realistically is to define some diagnostic commands
  that inspect the general state of the Isar/VM, and report some
  feedback to the user.  Typically this involves checking of the
  linguistic \emph{mode} of a proof state, or peeking at the pending
  goals (if available).

  Another common application is to define a toplevel command that
  poses a problem to the user as Isar proof state and stores the final
  result in a suitable context data slot.  Thus a proof can be
  incorporated into the context of some user-space tool, without
  modifying the Isar proof language itself.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Proof.state} \\
  @{index_ML Proof.assert_forward: "Proof.state -> Proof.state"} \\
  @{index_ML Proof.assert_chain: "Proof.state -> Proof.state"} \\
  @{index_ML Proof.assert_backward: "Proof.state -> Proof.state"} \\
  @{index_ML Proof.simple_goal: "Proof.state -> {context: Proof.context, goal: thm}"} \\
  @{index_ML Proof.goal: "Proof.state ->
  {context: Proof.context, facts: thm list, goal: thm}"} \\
  @{index_ML Proof.raw_goal: "Proof.state ->
  {context: Proof.context, facts: thm list, goal: thm}"} \\
  @{index_ML Proof.theorem: "Method.text option ->
  (thm list list -> Proof.context -> Proof.context) ->
  (term * term list) list list -> Proof.context -> Proof.state"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Proof.state} represents Isar proof states.  This is
  a block-structured configuration with proof context, linguistic
  mode, and optional goal.  The latter consists of goal context, goal
  facts (``@{text "using"}''), and tactical goal state (see
  \secref{sec:tactical-goals}).

  The general idea is that the facts shall contribute to the
  refinement of some parts of the tactical goal --- how exactly is
  defined by the proof method that is applied in that situation.

  \item @{ML Proof.assert_forward}, @{ML Proof.assert_chain}, @{ML
  Proof.assert_backward} are partial identity functions that fail
  unless a certain linguistic mode is active, namely ``@{text
  "proof(state)"}'', ``@{text "proof(chain)"}'', ``@{text
  "proof(prove)"}'', respectively (using the terminology of
  \cite{isabelle-isar-ref}).

  It is advisable study the implementations of existing proof commands
  for suitable modes to be asserted.

  \item @{ML Proof.simple_goal}~@{text "state"} returns the structured
  Isar goal (if available) in the form seen by ``simple'' methods
  (like @{method simp} or @{method blast}).  The Isar goal facts are
  already inserted as premises into the subgoals, which are presented
  individually as in @{ML Proof.goal}.

  \item @{ML Proof.goal}~@{text "state"} returns the structured Isar
  goal (if available) in the form seen by regular methods (like
  @{method rule}).  The auxiliary internal encoding of Pure
  conjunctions is split into individual subgoals as usual.

  \item @{ML Proof.raw_goal}~@{text "state"} returns the structured
  Isar goal (if available) in the raw internal form seen by ``raw''
  methods (like @{method induct}).  This form is rarely appropriate
  for dignostic tools; @{ML Proof.simple_goal} or @{ML Proof.goal}
  should be used in most situations.

  \item @{ML Proof.theorem}~@{text "before_qed after_qed statement ctxt"}
  initializes a toplevel Isar proof state within a given context.

  The optional @{text "before_qed"} method is applied at the end of
  the proof, just before extracting the result (this feature is rarely
  used).

  The @{text "after_qed"} continuation receives the extracted result
  in order to apply it to the final context in a suitable way (e.g.\
  storing named facts).  Note that at this generic level the target
  context is specified as @{ML_type Proof.context}, but the usual
  wrapping of toplevel proofs into command transactions will provide a
  @{ML_type local_theory} here (see also \chref{ch:local-theory}).
  This usually affects the way how results are stored.

  The @{text "statement"} is given as a nested list of terms, each
  associated with optional @{keyword "is"} patterns as usual in the
  Isar source language.  The original list structure over terms is
  turned into one over theorems when @{text "after_qed"} is invoked.

  \end{description}
*}


text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "Isar.goal"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  \begin{description}

  \item @{text "@{Isar.goal}"} refers to the regular goal state (if
  available) of the current proof state managed by the Isar toplevel
  --- as abstract value.

  This only works for diagnostic ML commands, such as @{command
  ML_val} or @{command ML_command}.

  \end{description}
*}

text %mlex {* The following example peeks at a certain goal configuration. *}

example_proof
  have A and B and C
    ML_val {* Thm.nprems_of (#goal @{Isar.goal}) *}
    oops

text {* \noindent Here we see 3 individual subgoals in the same way as
  regular proof methods would do.
*}


section {* Proof methods *}

text {* A @{text "method"} is a function @{text "context \<rightarrow> thm\<^sup>* \<rightarrow> goal
  \<rightarrow> (cases \<times> goal)\<^sup>*\<^sup>*"} that operates on the full Isar goal
  configuration with context, goal facts, and tactical goal state and
  enumerates possible follow-up goal states, with the potential
  addition of named extensions of the proof context (\emph{cases}).
  The latter feature is rarely used.

  This means a proof method is like a structurally enhanced tactic
  (cf.\ \secref{sec:tactics}).  The well-formedness conditions for
  tactics need to hold for methods accordingly, with the following
  additions.

  \begin{itemize}

  \item Goal addressing is further limited either to operate either
  uniformly on \emph{all} subgoals, or specifically on the
  \emph{first} subgoal.

  Exception: old-style tactic emulations that are embedded into the
  method space, e.g.\ @{method rule_tac}.

  \item A non-trivial method always needs to make progress: an
  identical follow-up goal state has to be avoided.\footnote{This
  enables the user to write method expressions like @{text "meth\<^sup>+"}
  without looping, while the trivial do-nothing case can be recovered
  via @{text "meth\<^sup>?"}.}

  Exception: trivial stuttering steps, such as ``@{method -}'' or
  @{method succeed}.

  \item Goal facts passed to the method must not be ignored.  If there
  is no sensible use of facts outside the goal state, facts should be
  inserted into the subgoals that are addressed by the method.

  \end{itemize}

  \medskip Syntactically, the language of proof methods is embedded
  into Isar as arguments to certain commands, e.g.\ @{command "by"} or
  @{command apply}.  User-space additions are reasonably easy by
  plugging suitable method-valued parser functions into the framework,
  using the @{command method_setup} command, for example.

  To get a better idea about the range of possibilities, consider the
  following Isar proof schemes.  First some general form of structured
  proof text:

  \medskip
  \begin{tabular}{l}
  @{command from}~@{text "facts\<^sub>1"}~@{command have}~@{text "props"}~@{command using}~@{text "facts\<^sub>2"} \\
  @{command proof}~@{text "(initial_method)"} \\
  \quad@{text "body"} \\
  @{command qed}~@{text "(terminal_method)"} \\
  \end{tabular}
  \medskip

  \noindent The goal configuration consists of @{text "facts\<^sub>1"} and
  @{text "facts\<^sub>2"} appended in that order, and various @{text "props"}
  being claimed here.  The @{text "initial_method"} is invoked with
  facts and goals together and refines the problem to something that
  is handled recursively in the proof @{text "body"}.  The @{text
  "terminal_method"} has another chance to finish-off any remaining
  subgoals, but it does not see the facts of the initial step.

  \medskip The second pattern illustrates unstructured proof scripts:

  \medskip
  \begin{tabular}{l}
  @{command have}~@{text "props"} \\
  \quad@{command using}~@{text "facts\<^sub>1"}~@{command apply}~@{text "method\<^sub>1"} \\
  \quad@{command apply}~@{text "method\<^sub>2"} \\
  \quad@{command using}~@{text "facts\<^sub>3"}~@{command apply}~@{text "method\<^sub>3"} \\
  \quad@{command done} \\
  \end{tabular}
  \medskip

  \noindent The @{text "method\<^sub>1"} operates on the original claim
  together while using @{text "facts\<^sub>1"}.  Since the @{command apply}
  command structurally resets the facts, the @{text "method\<^sub>2"} will
  operate on the remaining goal state without facts.  The @{text
  "method\<^sub>3"} will see again a collection of @{text "facts\<^sub>3"} that has
  been inserted into the script explicitly.

  \medskip Empirically, Isar proof methods can be categorized as
  follows.

  \begin{enumerate}

  \item \emph{Special method with cases} with named context additions
  associated with the follow-up goal state.

  Example: @{method "induct"}, which is also a ``raw'' method since it
  operates on the internal representation of simultaneous claims as
  Pure conjunction, instead of separate subgoals.

  \item \emph{Structured method} with strong emphasis on facts outside
  the goal state.

  Example: @{method "rule"}, which captures the key ideas behind
  structured reasoning in Isar in purest form.

  \item \emph{Simple method} with weaker emphasis on facts, which are
  inserted into subgoals to emulate old-style tactical as
  ``premises''.

  Examples: @{method "simp"}, @{method "blast"}, @{method "auto"}.

  \item \emph{Old-style tactic emulation} with detailed numeric goal
  addressing and explicit references to entities of the internal goal
  state (which are otherwise invisible from proper Isar proof text).
  To make the special non-standard status clear, the naming convention
  @{text "foo_tac"} needs to be observed.

  Example: @{method "rule_tac"}.

  \end{enumerate}

  When implementing proof methods, it is advisable to study existing
  implementations carefully and imitate the typical ``boiler plate''
  for context-sensitive parsing and further combinators to wrap-up
  tactic expressions as methods.\footnote{Home-grown aliases or
  abbreviations of the standard method combinators should be avoided.
  Old user code often retains similar remains of complicated two-phase
  method setup of Isabelle99 that was discontinued in Isabelle2009.}
*}


text %mlref {*
  \begin{mldecls}
  @{index_ML_type Proof.method} \\
  @{index_ML METHOD_CASES: "(thm list -> cases_tactic) -> Proof.method"} \\
  @{index_ML METHOD: "(thm list -> tactic) -> Proof.method"} \\
  @{index_ML SIMPLE_METHOD: "tactic -> Proof.method"} \\
  @{index_ML SIMPLE_METHOD': "(int -> tactic) -> Proof.method"} \\
  @{index_ML HEADGOAL: "(int -> tactic) -> tactic"} \\
  @{index_ML Method.insert_tac: "thm list -> int -> tactic"} \\
  @{index_ML Method.setup: "binding -> (Proof.context -> Proof.method) context_parser ->
  string -> theory -> theory"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Proof.method} represents proof methods as abstract type.

  \item @{ML METHOD_CASES}~@{text "(fn facts => cases_tactic)"} wraps
  @{text cases_tactic} depending on goal facts as proof method with
  cases; the goal context is passed via method syntax.

  \item @{ML METHOD}~@{text "(fn facts => tactic)"} wraps @{text
  tactic} depending on goal facts as regular proof method; the goal
  context is passed via method syntax.

  \item @{ML SIMPLE_METHOD}~@{text "tactic"} wraps a tactic that
  addresses all subgoals uniformly as simple proof method.  Goal facts
  are already inserted into all subgoals before @{text "tactic"} is
  applied.

  \item @{ML SIMPLE_METHOD'}~@{text "tactic"} wraps a tactic that
  addresses a specific subgoal as simple proof method.  Goal facts are
  already inserted into the first subgoal before @{text "tactic"} is
  applied to the same.

  \item @{ML HEADGOAL}~@{text "tactic"} applies @{text "tactic"} to
  the first subgoal.  This is convenient to reproduce part the @{ML
  SIMPLE_METHOD'} wrapping within regular @{ML METHOD}, for example.

  \item @{ML Method.insert_tac}~@{text "facts i"} inserts @{text
  "facts"} into subgoal @{text "i"}.  This is convenient to reproduce
  part of the @{ML SIMPLE_METHOD} or @{ML SIMPLE_METHOD'} wrapping
  within regular @{ML METHOD}, for example.

  \item @{ML Method.setup}~@{text "name parser description"} provides
  the functionality of the Isar command @{command method_setup}~@{text
  "name text description"} as ML function.

  \end{description}
*}

text %mlex {* The following toy examples illustrate how goal facts and
  goal state are passed to proof methods.  The pre-defined proof
  method called ``@{method tactic}'' wraps ML source of type @{ML_type
  tactic} (abstracted over @{verbatim facts}).  This allows immediate
  experimentation without concrete syntax parsing.
*}

example_proof
  assume a: A and b: B

  have "A \<and> B"
    apply (tactic {* rtac @{thm conjI} 1 *})
    using a apply (tactic {* resolve_tac facts 1 *})
    using b apply (tactic {* resolve_tac facts 1 *})
    done

  have "A \<and> B"
    using a and b
    ML_val "@{Isar.goal}"
    apply (tactic {* Method.insert_tac facts 1 *})
    apply (tactic {* (rtac @{thm conjI} THEN_ALL_NEW atac) 1 *})
    done
qed

text {* \medskip The subsequent example implements a method @{text
  "my_simp"} that rewrites the first subgoal by rules declared in the
  context.  As a shortcut to rule management we use a cheap solution
  via functor @{ML_functor Named_Thms} (see also @{"file"
  "~~/src/Pure/Tools/named_thms.ML"}).
*}

ML {*
  structure My_Simps =
    Named_Thms
      (val name = "my_simp" val description = "my_simp rule")
*}
setup My_Simps.setup

text {* \medskip\noindent This provides ML access to a list of
  theorems in canonical declaration order via @{ML My_Simps.get}.  The
  user can add or delete rules via the attribute @{attribute my_simp}.
  The actual proof method is now defined as follows:
*}

method_setup my_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (asm_full_simp_tac
        (HOL_basic_ss addsimps (My_Simps.get ctxt)) i)))
*} "rewrite subgoal by my_rewrite rules"

text {* \medskip\noindent Now method @{method my_simp} can be used in
  Isar proofs like this: *}

example_proof
  fix a b c
  assume [my_simp]: "a \<equiv> b"
  assume [my_simp]: "b \<equiv> c"
  have "a \<equiv> c" by my_simp
qed

text {* \medskip\noindent Note how the @{ML CHANGED} tactical is used
  to ensure progress of simplification: identical goal states need to
  be filtered out explicitly, because the internal Simplifier tactics
  never fail.

  \medskip Further refinement of method syntax is illustrated below:
  rules presented as explicit method arguments are included in the
  collection of rewrite rules.
*}

method_setup my_simp' = {*
  Attrib.thms >> (fn my_simps => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (asm_full_simp_tac
        (HOL_basic_ss addsimps (my_simps @ My_Simps.get ctxt)) i)))
*} "rewrite subgoal by my_rewrite rules"

example_proof
  fix a b c
  assume a: "a \<equiv> b"
  assume b: "b \<equiv> c"
  have "a \<equiv> c" by (my_simp' a b)
qed

text {* \medskip Both @{method my_simp} and @{method my_simp'} are
  simple methods, i.e.\ the goal facts are merely inserted as goal
  premises by the method wrapper.  For proof methods that are similar
  to the standard collection of @{method simp}, @{method blast},
  @{method auto} little more can be done here.

  Note that using the primary goal facts in the same manner as the
  method parameters obtained by the context or concrete syntax does
  not quite meet the requirement of ``strong emphasis on facts'' of
  regular proof methods, because rewrite rules as used above can be
  easily ignored.  A proof text ``@{command using}~@{text
  "foo"}~@{command "by"}~@{text "my_simp"}'' where @{text "foo"} is
  not used would deceive the reader.

  \medskip The technical treatment of rules from the context requires
  further attention.  Above we rebuild a fresh @{ML_type simpset} from
  the list of rules retrieved from the context on every invocation of
  the method.  This does not scale to really large collections of
  rules.

  This is an inherent limitation of the above rule management via
  functor @{ML_functor Named_Thms}, because that lacks tool-specific
  storage and retrieval.  More realistic applications require
  efficient index-structures that organize theorems in a customized
  manner, such as a discrimination net that is indexed by the
  left-hand sides of rewrite rules.  For variations on the Simplifier
  it is possible to re-use the existing type @{ML_type simpset}, but
  scalability requires it be maintained statically within the context
  data, not dynamically on each tool invocation.  *}


section {* Attributes *}

text FIXME

end

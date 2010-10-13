theory Isar
imports Base
begin

chapter {* Isar language elements *}

text {*
  %FIXME proper formal markup of methods!?

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
  Typical examples are @{method rule}, @{method unfold}, and @{text
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
  (like @{text simp} or @{text blast}).  The Isar goal facts are
  already inserted as premises into the subgoals, which are presented
  individually as in @{ML Proof.goal}.

  \item @{ML Proof.goal}~@{text "state"} returns the structured Isar
  goal (if available) in the form seen by regular methods (like
  @{method rule}).  The auxiliary internal encoding of Pure
  conjunctions is split into individual subgoals as usual.

  \item @{ML Proof.raw_goal}~@{text "state"} returns the structured
  Isar goal (if available) in the raw internal form seen by ``raw''
  methods (like @{text induct}).  This form is rarely appropriate for
  dignostic tools; @{ML Proof.simple_goal} or @{ML Proof.goal} should
  be used in most situations.

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
  have "PROP A" and "PROP B" and "PROP C"
    ML_val {* Thm.nprems_of (#goal @{Isar.goal}) *}
    oops

text {* \noindent Here we see 3 individual subgoals in the same way as
  regular proof methods would do.
*}


section {* Proof methods *}

text {* Proof methods are syntactically embedded into the Isar proof
  language as arguments to certain commands, e.g.\ @{command "by"} or
  @{command apply}.  User-space additions are reasonably easy by
  plugging suitable method-valued parser functions into the framework.

  Operationally, a proof method is like a structurally enhanced
  tactic: it operates on the full Isar goal configuration with
  context, goal facts, and tactical goal state.  Like a tactic, it
  enumerates possible follow-up goal states, with the potential
  addition of named extensions of the proof context (\emph{cases}).

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
  together while using @{text "facts\<^bsub>1\<^esub>"}.  Since the @{command apply}
  command structurally resets the facts, the @{text "method\<^sub>2"} will
  operate on the remaining goal state without facts.  The @{text
  "method\<^sub>3"} will see again a collection of @{text "facts\<^sub>3"} that has
  been inserted into the script explicitly.

  \medskip Empirically, Isar proof methods can be categorized as follows:

  \begin{enumerate}

  \item structured method with cases, e.g.\ @{text "induct"}

  \item regular method: strong emphasis on facts, e.g.\ @{text "rule"}

  \item simple method: weak emphasis on facts, merely inserted into subgoals, e.g.\ @{text "simp"}

  \item old-style tactic emulation, e.g. @{text "rule_tac"}

  \begin{itemize}

  \item naming convention @{text "foo_tac"}

  \item numeric goal addressing

  \item explicit references to internal goal state (invisible from text!)

  \end{itemize}

  \end{enumerate}

  FIXME
*}


section {* Attributes *}

text FIXME

end

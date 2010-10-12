theory Isar
imports Base
begin

chapter {* Isar language elements *}

text {* The Isar proof language (see also
  \cite[\S2]{isabelle-isar-ref}) consists of three main categories of
  language elements:

  \begin{enumerate}

  \item Proof \emph{commands} define the primary language of
  transactions of the underlying Isar/VM interpreter.  Typical
  examples are @{command "fix"}, @{command "assume"}, @{command
  "show"}, and @{command "by"}.

  Composing proof commands according to the rules of the Isar/VM
  essentially leads to expressions of structured proof text, such that
  both the machine and the human reader can give it a meaning as
  formal reasoning.

  \item Proof \emph{methods} define a secondary language of mixed
  forward-backward refinement steps involving facts and goals.
  Typical example methods are @{method rule}, @{method unfold}, or
  @{text simp}.  %FIXME proper formal markup!?

  Methods can occur in certain well-defined parts of the Isar proof
  language, say as arguments to @{command "proof"}, @{command "qed"},
  or @{command "by"}.

  \item \emph{Attributes} define a tertiary language of small
  annotations to facts: facts being defined or referenced may always
  be decorated with attribute expressions.  Attributes can modify both
  the fact and the context.

  Typical example attributes are @{attribute intro} (which affects the
  context), or @{attribute symmetric} (which affects the fact).

  \end{enumerate}
*}


section {* Proof commands *}

text {* In principle, Isar proof commands could be defined in
  user-space as well.  The system is built like that in the first
  place: part of the commands are primitive, the other part is defined
  as derived elements.  Adding to the genuine structured proof
  language requires profound understanding of the Isar/VM machinery,
  though, so this is far beyond the scope of this manual.

  What can be done realistically is to define some diagnostic commands
  that merely inspect the general state of the Isar/VM, and report
  some feedback to the user.  Typically this involves checking of the
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
  mode, and optional goal state.  An Isar goal consists of goal
  context, goal facts (``@{text "using"}''), and tactical goal state
  (see \secref{sec:tactical-goals}).

  The general idea is that the facts shall contribute to the
  refinement of the goal state --- how exactly is defined by the proof
  method that is applied in that situation.

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
  separately as in @{ML Proof.goal}.

  \item @{ML Proof.goal}~@{text "state"} returns the structured Isar
  goal (if available) in the form seen by regular methods (like
  @{method rule}).  The auxiliary internal encoding of Pure
  conjunctions is split into individual subgoals as usual.

  \item @{ML Proof.raw_goal}~@{text "state"} returns the structured
  Isar goal (if available) in the raw internal form seen by ``raw''
  methods (like @{text induct}).  This form is very rarely appropriate
  for dignostic tools; @{ML Proof.simple_goal} or @{ML Proof.goal}
  should be used in most situations.

  \end{description}
*}



section {* Proof methods *}

text FIXME


section {* Attributes *}

text FIXME

end

theory Proof
imports Base Main
begin

chapter {* Proofs \label{ch:proofs} *}

text {*
  Proof commands perform transitions of Isar/VM machine
  configurations, which are block-structured, consisting of a stack of
  nodes with three main components: logical proof context, current
  facts, and open goals.  Isar/VM transitions are typed according to
  the following three different modes of operation:

  \begin{description}

  \item @{text "proof(prove)"} means that a new goal has just been
  stated that is now to be \emph{proven}; the next command may refine
  it by some proof method, and enter a sub-proof to establish the
  actual result.

  \item @{text "proof(state)"} is like a nested theory mode: the
  context may be augmented by \emph{stating} additional assumptions,
  intermediate results etc.

  \item @{text "proof(chain)"} is intermediate between @{text
  "proof(state)"} and @{text "proof(prove)"}: existing facts (i.e.\
  the contents of the special ``@{fact_ref this}'' register) have been
  just picked up in order to be used when refining the goal claimed
  next.

  \end{description}

  The proof mode indicator may be understood as an instruction to the
  writer, telling what kind of operation may be performed next.  The
  corresponding typings of proof commands restricts the shape of
  well-formed proof texts to particular command sequences.  So dynamic
  arrangements of commands eventually turn out as static texts of a
  certain structure.

  \Appref{ap:refcard} gives a simplified grammar of the (extensible)
  language emerging that way from the different types of proof
  commands.  The main ideas of the overall Isar framework are
  explained in \chref{ch:isar-framework}.
*}


section {* Proof structure *}

subsection {* Formal notepad *}

text {*
  \begin{matharray}{rcl}
    @{command_def "notepad"} & : & @{text "local_theory \<rightarrow> proof(state)"} \\
  \end{matharray}

  @{rail "
    @@{command notepad} @'begin'
    ;
    @@{command end}
  "}

  \begin{description}

  \item @{command "notepad"}~@{keyword "begin"} opens a proof state
  without any goal statement.  This allows to experiment with Isar,
  without producing any persistent result.

  The notepad can be closed by @{command "end"} or discontinued by
  @{command "oops"}.

  \end{description}
*}


subsection {* Blocks *}

text {*
  \begin{matharray}{rcl}
    @{command_def "next"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "{"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "}"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
  \end{matharray}

  While Isar is inherently block-structured, opening and closing
  blocks is mostly handled rather casually, with little explicit
  user-intervention.  Any local goal statement automatically opens
  \emph{two} internal blocks, which are closed again when concluding
  the sub-proof (by @{command "qed"} etc.).  Sections of different
  context within a sub-proof may be switched via @{command "next"},
  which is just a single block-close followed by block-open again.
  The effect of @{command "next"} is to reset the local proof context;
  there is no goal focus involved here!

  For slightly more advanced applications, there are explicit block
  parentheses as well.  These typically achieve a stronger forward
  style of reasoning.

  \begin{description}

  \item @{command "next"} switches to a fresh block within a
  sub-proof, resetting the local context to the initial one.

  \item @{command "{"} and @{command "}"} explicitly open and close
  blocks.  Any current facts pass through ``@{command "{"}''
  unchanged, while ``@{command "}"}'' causes any result to be
  \emph{exported} into the enclosing context.  Thus fixed variables
  are generalized, assumptions discharged, and local definitions
  unfolded (cf.\ \secref{sec:proof-context}).  There is no difference
  of @{command "assume"} and @{command "presume"} in this mode of
  forward reasoning --- in contrast to plain backward reasoning with
  the result exported at @{command "show"} time.

  \end{description}
*}


subsection {* Omitting proofs *}

text {*
  \begin{matharray}{rcl}
    @{command_def "oops"} & : & @{text "proof \<rightarrow> local_theory | theory"} \\
  \end{matharray}

  The @{command "oops"} command discontinues the current proof
  attempt, while considering the partial proof text as properly
  processed.  This is conceptually quite different from ``faking''
  actual proofs via @{command_ref "sorry"} (see
  \secref{sec:proof-steps}): @{command "oops"} does not observe the
  proof structure at all, but goes back right to the theory level.
  Furthermore, @{command "oops"} does not produce any result theorem
  --- there is no intended claim to be able to complete the proof
  in any way.

  A typical application of @{command "oops"} is to explain Isar proofs
  \emph{within} the system itself, in conjunction with the document
  preparation tools of Isabelle described in \chref{ch:document-prep}.
  Thus partial or even wrong proof attempts can be discussed in a
  logically sound manner.  Note that the Isabelle {\LaTeX} macros can
  be easily adapted to print something like ``@{text "\<dots>"}'' instead of
  the keyword ``@{command "oops"}''.
*}


section {* Statements *}

subsection {* Context elements \label{sec:proof-context} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "fix"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "assume"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "presume"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "def"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
  \end{matharray}

  The logical proof context consists of fixed variables and
  assumptions.  The former closely correspond to Skolem constants, or
  meta-level universal quantification as provided by the Isabelle/Pure
  logical framework.  Introducing some \emph{arbitrary, but fixed}
  variable via ``@{command "fix"}~@{text x}'' results in a local value
  that may be used in the subsequent proof as any other variable or
  constant.  Furthermore, any result @{text "\<turnstile> \<phi>[x]"} exported from
  the context will be universally closed wrt.\ @{text x} at the
  outermost level: @{text "\<turnstile> \<And>x. \<phi>[x]"} (this is expressed in normal
  form using Isabelle's meta-variables).

  Similarly, introducing some assumption @{text \<chi>} has two effects.
  On the one hand, a local theorem is created that may be used as a
  fact in subsequent proof steps.  On the other hand, any result
  @{text "\<chi> \<turnstile> \<phi>"} exported from the context becomes conditional wrt.\
  the assumption: @{text "\<turnstile> \<chi> \<Longrightarrow> \<phi>"}.  Thus, solving an enclosing goal
  using such a result would basically introduce a new subgoal stemming
  from the assumption.  How this situation is handled depends on the
  version of assumption command used: while @{command "assume"}
  insists on solving the subgoal by unification with some premise of
  the goal, @{command "presume"} leaves the subgoal unchanged in order
  to be proved later by the user.

  Local definitions, introduced by ``@{command "def"}~@{text "x \<equiv>
  t"}'', are achieved by combining ``@{command "fix"}~@{text x}'' with
  another version of assumption that causes any hypothetical equation
  @{text "x \<equiv> t"} to be eliminated by the reflexivity rule.  Thus,
  exporting some result @{text "x \<equiv> t \<turnstile> \<phi>[x]"} yields @{text "\<turnstile>
  \<phi>[t]"}.

  @{rail "
    @@{command fix} (@{syntax vars} + @'and')
    ;
    (@@{command assume} | @@{command presume}) (@{syntax props} + @'and')
    ;
    @@{command def} (def + @'and')
    ;
    def: @{syntax thmdecl}? \\ @{syntax name} ('==' | '\<equiv>') @{syntax term} @{syntax term_pat}?
  "}

  \begin{description}
  
  \item @{command "fix"}~@{text x} introduces a local variable @{text
  x} that is \emph{arbitrary, but fixed.}
  
  \item @{command "assume"}~@{text "a: \<phi>"} and @{command
  "presume"}~@{text "a: \<phi>"} introduce a local fact @{text "\<phi> \<turnstile> \<phi>"} by
  assumption.  Subsequent results applied to an enclosing goal (e.g.\
  by @{command_ref "show"}) are handled as follows: @{command
  "assume"} expects to be able to unify with existing premises in the
  goal, while @{command "presume"} leaves @{text \<phi>} as new subgoals.
  
  Several lists of assumptions may be given (separated by
  @{keyword_ref "and"}; the resulting list of current facts consists
  of all of these concatenated.
  
  \item @{command "def"}~@{text "x \<equiv> t"} introduces a local
  (non-polymorphic) definition.  In results exported from the context,
  @{text x} is replaced by @{text t}.  Basically, ``@{command
  "def"}~@{text "x \<equiv> t"}'' abbreviates ``@{command "fix"}~@{text
  x}~@{command "assume"}~@{text "x \<equiv> t"}'', with the resulting
  hypothetical equation solved by reflexivity.
  
  The default name for the definitional equation is @{text x_def}.
  Several simultaneous definitions may be given at the same time.

  \end{description}

  The special name @{fact_ref prems} refers to all assumptions of the
  current context as a list of theorems.  This feature should be used
  with great care!  It is better avoided in final proof texts.
*}


subsection {* Term abbreviations \label{sec:term-abbrev} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "let"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{keyword_def "is"} & : & syntax \\
  \end{matharray}

  Abbreviations may be either bound by explicit @{command
  "let"}~@{text "p \<equiv> t"} statements, or by annotating assumptions or
  goal statements with a list of patterns ``@{text "(\<IS> p\<^sub>1 \<dots>
  p\<^sub>n)"}''.  In both cases, higher-order matching is invoked to
  bind extra-logical term variables, which may be either named
  schematic variables of the form @{text ?x}, or nameless dummies
  ``@{variable _}'' (underscore). Note that in the @{command "let"}
  form the patterns occur on the left-hand side, while the @{keyword
  "is"} patterns are in postfix position.

  Polymorphism of term bindings is handled in Hindley-Milner style,
  similar to ML.  Type variables referring to local assumptions or
  open goal statements are \emph{fixed}, while those of finished
  results or bound by @{command "let"} may occur in \emph{arbitrary}
  instances later.  Even though actual polymorphism should be rarely
  used in practice, this mechanism is essential to achieve proper
  incremental type-inference, as the user proceeds to build up the
  Isar proof text from left to right.

  \medskip Term abbreviations are quite different from local
  definitions as introduced via @{command "def"} (see
  \secref{sec:proof-context}).  The latter are visible within the
  logic as actual equations, while abbreviations disappear during the
  input process just after type checking.  Also note that @{command
  "def"} does not support polymorphism.

  @{rail "
    @@{command let} ((@{syntax term} + @'and') '=' @{syntax term} + @'and')
  "}

  The syntax of @{keyword "is"} patterns follows @{syntax term_pat} or
  @{syntax prop_pat} (see \secref{sec:term-decls}).

  \begin{description}

  \item @{command "let"}~@{text "p\<^sub>1 = t\<^sub>1 \<AND> \<dots> p\<^sub>n = t\<^sub>n"} binds any
  text variables in patterns @{text "p\<^sub>1, \<dots>, p\<^sub>n"} by simultaneous
  higher-order matching against terms @{text "t\<^sub>1, \<dots>, t\<^sub>n"}.

  \item @{text "(\<IS> p\<^sub>1 \<dots> p\<^sub>n)"} resembles @{command "let"}, but
  matches @{text "p\<^sub>1, \<dots>, p\<^sub>n"} against the preceding statement.  Also
  note that @{keyword "is"} is not a separate command, but part of
  others (such as @{command "assume"}, @{command "have"} etc.).

  \end{description}

  Some \emph{implicit} term abbreviations\index{term abbreviations}
  for goals and facts are available as well.  For any open goal,
  @{variable_ref thesis} refers to its object-level statement,
  abstracted over any meta-level parameters (if present).  Likewise,
  @{variable_ref this} is bound for fact statements resulting from
  assumptions or finished goals.  In case @{variable this} refers to
  an object-logic statement that is an application @{text "f t"}, then
  @{text t} is bound to the special text variable ``@{variable "\<dots>"}''
  (three dots).  The canonical application of this convenience are
  calculational proofs (see \secref{sec:calculation}).
*}


subsection {* Facts and forward chaining \label{sec:proof-facts} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "note"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "then"} & : & @{text "proof(state) \<rightarrow> proof(chain)"} \\
    @{command_def "from"} & : & @{text "proof(state) \<rightarrow> proof(chain)"} \\
    @{command_def "with"} & : & @{text "proof(state) \<rightarrow> proof(chain)"} \\
    @{command_def "using"} & : & @{text "proof(prove) \<rightarrow> proof(prove)"} \\
    @{command_def "unfolding"} & : & @{text "proof(prove) \<rightarrow> proof(prove)"} \\
  \end{matharray}

  New facts are established either by assumption or proof of local
  statements.  Any fact will usually be involved in further proofs,
  either as explicit arguments of proof methods, or when forward
  chaining towards the next goal via @{command "then"} (and variants);
  @{command "from"} and @{command "with"} are composite forms
  involving @{command "note"}.  The @{command "using"} elements
  augments the collection of used facts \emph{after} a goal has been
  stated.  Note that the special theorem name @{fact_ref this} refers
  to the most recently established facts, but only \emph{before}
  issuing a follow-up claim.

  @{rail "
    @@{command note} (@{syntax thmdef}? @{syntax thmrefs} + @'and')
    ;
    (@@{command from} | @@{command with} | @@{command using} | @@{command unfolding})
      (@{syntax thmrefs} + @'and')
  "}

  \begin{description}

  \item @{command "note"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"} recalls existing facts
  @{text "b\<^sub>1, \<dots>, b\<^sub>n"}, binding the result as @{text a}.  Note that
  attributes may be involved as well, both on the left and right hand
  sides.

  \item @{command "then"} indicates forward chaining by the current
  facts in order to establish the goal to be claimed next.  The
  initial proof method invoked to refine that will be offered the
  facts to do ``anything appropriate'' (see also
  \secref{sec:proof-steps}).  For example, method @{method (Pure) rule}
  (see \secref{sec:pure-meth-att}) would typically do an elimination
  rather than an introduction.  Automatic methods usually insert the
  facts into the goal state before operation.  This provides a simple
  scheme to control relevance of facts in automated proof search.
  
  \item @{command "from"}~@{text b} abbreviates ``@{command
  "note"}~@{text b}~@{command "then"}''; thus @{command "then"} is
  equivalent to ``@{command "from"}~@{text this}''.
  
  \item @{command "with"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"} abbreviates ``@{command
  "from"}~@{text "b\<^sub>1 \<dots> b\<^sub>n \<AND> this"}''; thus the forward chaining
  is from earlier facts together with the current ones.
  
  \item @{command "using"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"} augments the facts being
  currently indicated for use by a subsequent refinement step (such as
  @{command_ref "apply"} or @{command_ref "proof"}).
  
  \item @{command "unfolding"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"} is structurally
  similar to @{command "using"}, but unfolds definitional equations
  @{text "b\<^sub>1, \<dots> b\<^sub>n"} throughout the goal state and facts.

  \end{description}

  Forward chaining with an empty list of theorems is the same as not
  chaining at all.  Thus ``@{command "from"}~@{text nothing}'' has no
  effect apart from entering @{text "prove(chain)"} mode, since
  @{fact_ref nothing} is bound to the empty list of theorems.

  Basic proof methods (such as @{method_ref (Pure) rule}) expect multiple
  facts to be given in their proper order, corresponding to a prefix
  of the premises of the rule involved.  Note that positions may be
  easily skipped using something like @{command "from"}~@{text "_
  \<AND> a \<AND> b"}, for example.  This involves the trivial rule
  @{text "PROP \<psi> \<Longrightarrow> PROP \<psi>"}, which is bound in Isabelle/Pure as
  ``@{fact_ref "_"}'' (underscore).

  Automated methods (such as @{method simp} or @{method auto}) just
  insert any given facts before their usual operation.  Depending on
  the kind of procedure involved, the order of facts is less
  significant here.
*}


subsection {* Goals \label{sec:goals} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "lemma"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "theorem"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "corollary"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "schematic_lemma"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "schematic_theorem"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "schematic_corollary"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "have"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
    @{command_def "show"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
    @{command_def "hence"} & : & @{text "proof(state) \<rightarrow> proof(prove)"} \\
    @{command_def "thus"} & : & @{text "proof(state) \<rightarrow> proof(prove)"} \\
    @{command_def "print_statement"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  From a theory context, proof mode is entered by an initial goal
  command such as @{command "lemma"}, @{command "theorem"}, or
  @{command "corollary"}.  Within a proof, new claims may be
  introduced locally as well; four variants are available here to
  indicate whether forward chaining of facts should be performed
  initially (via @{command_ref "then"}), and whether the final result
  is meant to solve some pending goal.

  Goals may consist of multiple statements, resulting in a list of
  facts eventually.  A pending multi-goal is internally represented as
  a meta-level conjunction (@{text "&&&"}), which is usually
  split into the corresponding number of sub-goals prior to an initial
  method application, via @{command_ref "proof"}
  (\secref{sec:proof-steps}) or @{command_ref "apply"}
  (\secref{sec:tactic-commands}).  The @{method_ref induct} method
  covered in \secref{sec:cases-induct} acts on multiple claims
  simultaneously.

  Claims at the theory level may be either in short or long form.  A
  short goal merely consists of several simultaneous propositions
  (often just one).  A long goal includes an explicit context
  specification for the subsequent conclusion, involving local
  parameters and assumptions.  Here the role of each part of the
  statement is explicitly marked by separate keywords (see also
  \secref{sec:locale}); the local assumptions being introduced here
  are available as @{fact_ref assms} in the proof.  Moreover, there
  are two kinds of conclusions: @{element_def "shows"} states several
  simultaneous propositions (essentially a big conjunction), while
  @{element_def "obtains"} claims several simultaneous simultaneous
  contexts of (essentially a big disjunction of eliminated parameters
  and assumptions, cf.\ \secref{sec:obtain}).

  @{rail "
    (@@{command lemma} | @@{command theorem} | @@{command corollary} |
     @@{command schematic_lemma} | @@{command schematic_theorem} |
     @@{command schematic_corollary}) @{syntax target}? (goal | longgoal)
    ;
    (@@{command have} | @@{command show} | @@{command hence} | @@{command thus}) goal
    ;
    @@{command print_statement} @{syntax modes}? @{syntax thmrefs}
    ;
  
    goal: (@{syntax props} + @'and')
    ;
    longgoal: @{syntax thmdecl}? (@{syntax_ref \"includes\"}?) (@{syntax context_elem} * ) conclusion
    ;
    conclusion: @'shows' goal | @'obtains' (@{syntax parname}? case + '|')
    ;
    case: (@{syntax vars} + @'and') @'where' (@{syntax props} + @'and')
  "}

  \begin{description}
  
  \item @{command "lemma"}~@{text "a: \<phi>"} enters proof mode with
  @{text \<phi>} as main goal, eventually resulting in some fact @{text "\<turnstile>
  \<phi>"} to be put back into the target context.  An additional @{syntax
  context} specification may build up an initial proof context for the
  subsequent claim; this includes local definitions and syntax as
  well, see also @{syntax "includes"} in \secref{sec:bundle} and
  @{syntax context_elem} in \secref{sec:locale}.
  
  \item @{command "theorem"}~@{text "a: \<phi>"} and @{command
  "corollary"}~@{text "a: \<phi>"} are essentially the same as @{command
  "lemma"}~@{text "a: \<phi>"}, but the facts are internally marked as
  being of a different kind.  This discrimination acts like a formal
  comment.

  \item @{command "schematic_lemma"}, @{command "schematic_theorem"},
  @{command "schematic_corollary"} are similar to @{command "lemma"},
  @{command "theorem"}, @{command "corollary"}, respectively but allow
  the statement to contain unbound schematic variables.

  Under normal circumstances, an Isar proof text needs to specify
  claims explicitly.  Schematic goals are more like goals in Prolog,
  where certain results are synthesized in the course of reasoning.
  With schematic statements, the inherent compositionality of Isar
  proofs is lost, which also impacts performance, because proof
  checking is forced into sequential mode.
  
  \item @{command "have"}~@{text "a: \<phi>"} claims a local goal,
  eventually resulting in a fact within the current logical context.
  This operation is completely independent of any pending sub-goals of
  an enclosing goal statements, so @{command "have"} may be freely
  used for experimental exploration of potential results within a
  proof body.
  
  \item @{command "show"}~@{text "a: \<phi>"} is like @{command
  "have"}~@{text "a: \<phi>"} plus a second stage to refine some pending
  sub-goal for each one of the finished result, after having been
  exported into the corresponding context (at the head of the
  sub-proof of this @{command "show"} command).
  
  To accommodate interactive debugging, resulting rules are printed
  before being applied internally.  Even more, interactive execution
  of @{command "show"} predicts potential failure and displays the
  resulting error as a warning beforehand.  Watch out for the
  following message:

  %FIXME proper antiquitation
  \begin{ttbox}
  Problem! Local statement will fail to solve any pending goal
  \end{ttbox}
  
  \item @{command "hence"} abbreviates ``@{command "then"}~@{command
  "have"}'', i.e.\ claims a local goal to be proven by forward
  chaining the current facts.  Note that @{command "hence"} is also
  equivalent to ``@{command "from"}~@{text this}~@{command "have"}''.
  
  \item @{command "thus"} abbreviates ``@{command "then"}~@{command
  "show"}''.  Note that @{command "thus"} is also equivalent to
  ``@{command "from"}~@{text this}~@{command "show"}''.
  
  \item @{command "print_statement"}~@{text a} prints facts from the
  current theory or proof context in long statement form, according to
  the syntax for @{command "lemma"} given above.

  \end{description}

  Any goal statement causes some term abbreviations (such as
  @{variable_ref "?thesis"}) to be bound automatically, see also
  \secref{sec:term-abbrev}.

  The optional case names of @{element_ref "obtains"} have a twofold
  meaning: (1) during the of this claim they refer to the the local
  context introductions, (2) the resulting rule is annotated
  accordingly to support symbolic case splits when used with the
  @{method_ref cases} method (cf.\ \secref{sec:cases-induct}).
*}


section {* Refinement steps *}

subsection {* Proof method expressions \label{sec:proof-meth} *}

text {* Proof methods are either basic ones, or expressions composed
  of methods via ``@{verbatim ","}'' (sequential composition),
  ``@{verbatim "|"}'' (alternative choices), ``@{verbatim "?"}''
  (try), ``@{verbatim "+"}'' (repeat at least once), ``@{verbatim
  "["}@{text n}@{verbatim "]"}'' (restriction to first @{text n}
  sub-goals, with default @{text "n = 1"}).  In practice, proof
  methods are usually just a comma separated list of @{syntax
  nameref}~@{syntax args} specifications.  Note that parentheses may
  be dropped for single method specifications (with no arguments).

  @{rail "
    @{syntax_def method}:
      (@{syntax nameref} | '(' methods ')') (() | '?' | '+' | '[' @{syntax nat}? ']')
    ;
    methods: (@{syntax nameref} @{syntax args} | @{syntax method}) + (',' | '|')
  "}

  Proper Isar proof methods do \emph{not} admit arbitrary goal
  addressing, but refer either to the first sub-goal or all sub-goals
  uniformly.  The goal restriction operator ``@{text "[n]"}''
  evaluates a method expression within a sandbox consisting of the
  first @{text n} sub-goals (which need to exist).  For example, the
  method ``@{text "simp_all[3]"}'' simplifies the first three
  sub-goals, while ``@{text "(rule foo, simp_all)[]"}'' simplifies all
  new goals that emerge from applying rule @{text "foo"} to the
  originally first one.

  Improper methods, notably tactic emulations, offer a separate
  low-level goal addressing scheme as explicit argument to the
  individual tactic being involved.  Here ``@{text "[!]"}'' refers to
  all goals, and ``@{text "[n-]"}'' to all goals starting from @{text
  "n"}.

  @{rail "
    @{syntax_def goal_spec}:
      '[' (@{syntax nat} '-' @{syntax nat} | @{syntax nat} '-' | @{syntax nat} | '!' ) ']'
  "}
*}


subsection {* Initial and terminal proof steps \label{sec:proof-steps} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "proof"} & : & @{text "proof(prove) \<rightarrow> proof(state)"} \\
    @{command_def "qed"} & : & @{text "proof(state) \<rightarrow> proof(state) | local_theory | theory"} \\
    @{command_def "by"} & : & @{text "proof(prove) \<rightarrow> proof(state) | local_theory | theory"} \\
    @{command_def ".."} & : & @{text "proof(prove) \<rightarrow> proof(state) | local_theory | theory"} \\
    @{command_def "."} & : & @{text "proof(prove) \<rightarrow> proof(state) | local_theory | theory"} \\
    @{command_def "sorry"} & : & @{text "proof(prove) \<rightarrow> proof(state) | local_theory | theory"} \\
  \end{matharray}

  Arbitrary goal refinement via tactics is considered harmful.
  Structured proof composition in Isar admits proof methods to be
  invoked in two places only.

  \begin{enumerate}

  \item An \emph{initial} refinement step @{command_ref
  "proof"}~@{text "m\<^sub>1"} reduces a newly stated goal to a number
  of sub-goals that are to be solved later.  Facts are passed to
  @{text "m\<^sub>1"} for forward chaining, if so indicated by @{text
  "proof(chain)"} mode.
  
  \item A \emph{terminal} conclusion step @{command_ref "qed"}~@{text
  "m\<^sub>2"} is intended to solve remaining goals.  No facts are
  passed to @{text "m\<^sub>2"}.

  \end{enumerate}

  The only other (proper) way to affect pending goals in a proof body
  is by @{command_ref "show"}, which involves an explicit statement of
  what is to be solved eventually.  Thus we avoid the fundamental
  problem of unstructured tactic scripts that consist of numerous
  consecutive goal transformations, with invisible effects.

  \medskip As a general rule of thumb for good proof style, initial
  proof methods should either solve the goal completely, or constitute
  some well-understood reduction to new sub-goals.  Arbitrary
  automatic proof tools that are prone leave a large number of badly
  structured sub-goals are no help in continuing the proof document in
  an intelligible manner.

  Unless given explicitly by the user, the default initial method is
  @{method_ref (Pure) rule} (or its classical variant @{method_ref
  rule}), which applies a single standard elimination or introduction
  rule according to the topmost symbol involved.  There is no separate
  default terminal method.  Any remaining goals are always solved by
  assumption in the very last step.

  @{rail "
    @@{command proof} method?
    ;
    @@{command qed} method?
    ;
    @@{command \"by\"} method method?
    ;
    (@@{command \".\"} | @@{command \"..\"} | @@{command sorry})
  "}

  \begin{description}
  
  \item @{command "proof"}~@{text "m\<^sub>1"} refines the goal by proof
  method @{text "m\<^sub>1"}; facts for forward chaining are passed if so
  indicated by @{text "proof(chain)"} mode.
  
  \item @{command "qed"}~@{text "m\<^sub>2"} refines any remaining goals by
  proof method @{text "m\<^sub>2"} and concludes the sub-proof by assumption.
  If the goal had been @{text "show"} (or @{text "thus"}), some
  pending sub-goal is solved as well by the rule resulting from the
  result \emph{exported} into the enclosing goal context.  Thus @{text
  "qed"} may fail for two reasons: either @{text "m\<^sub>2"} fails, or the
  resulting rule does not fit to any pending goal\footnote{This
  includes any additional ``strong'' assumptions as introduced by
  @{command "assume"}.} of the enclosing context.  Debugging such a
  situation might involve temporarily changing @{command "show"} into
  @{command "have"}, or weakening the local context by replacing
  occurrences of @{command "assume"} by @{command "presume"}.
  
  \item @{command "by"}~@{text "m\<^sub>1 m\<^sub>2"} is a \emph{terminal
  proof}\index{proof!terminal}; it abbreviates @{command
  "proof"}~@{text "m\<^sub>1"}~@{command "qed"}~@{text "m\<^sub>2"}, but with
  backtracking across both methods.  Debugging an unsuccessful
  @{command "by"}~@{text "m\<^sub>1 m\<^sub>2"} command can be done by expanding its
  definition; in many cases @{command "proof"}~@{text "m\<^sub>1"} (or even
  @{text "apply"}~@{text "m\<^sub>1"}) is already sufficient to see the
  problem.

  \item ``@{command ".."}'' is a \emph{default
  proof}\index{proof!default}; it abbreviates @{command "by"}~@{text
  "rule"}.

  \item ``@{command "."}'' is a \emph{trivial
  proof}\index{proof!trivial}; it abbreviates @{command "by"}~@{text
  "this"}.
  
  \item @{command "sorry"} is a \emph{fake proof}\index{proof!fake}
  pretending to solve the pending claim without further ado.  This
  only works in interactive development, or if the @{ML
  quick_and_dirty} flag is enabled (in ML).  Facts emerging from fake
  proofs are not the real thing.  Internally, each theorem container
  is tainted by an oracle invocation, which is indicated as ``@{text
  "[!]"}'' in the printed result.
  
  The most important application of @{command "sorry"} is to support
  experimentation and top-down proof development.

  \end{description}
*}


subsection {* Fundamental methods and attributes \label{sec:pure-meth-att} *}

text {*
  The following proof methods and attributes refer to basic logical
  operations of Isar.  Further methods and attributes are provided by
  several generic and object-logic specific tools and packages (see
  \chref{ch:gen-tools} and \chref{ch:hol}).

  \begin{matharray}{rcl}
    @{method_def "-"} & : & @{text method} \\
    @{method_def "fact"} & : & @{text method} \\
    @{method_def "assumption"} & : & @{text method} \\
    @{method_def "this"} & : & @{text method} \\
    @{method_def (Pure) "rule"} & : & @{text method} \\
    @{attribute_def (Pure) "intro"} & : & @{text attribute} \\
    @{attribute_def (Pure) "elim"} & : & @{text attribute} \\
    @{attribute_def (Pure) "dest"} & : & @{text attribute} \\
    @{attribute_def (Pure) "rule"} & : & @{text attribute} \\[0.5ex]
    @{attribute_def "OF"} & : & @{text attribute} \\
    @{attribute_def "of"} & : & @{text attribute} \\
    @{attribute_def "where"} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{method fact} @{syntax thmrefs}?
    ;
    @@{method (Pure) rule} @{syntax thmrefs}?
    ;
    rulemod: ('intro' | 'elim' | 'dest')
      ((('!' | () | '?') @{syntax nat}?) | 'del') ':' @{syntax thmrefs}
    ;
    (@@{attribute intro} | @@{attribute elim} | @@{attribute dest})
      ('!' | () | '?') @{syntax nat}?
    ;
    @@{attribute (Pure) rule} 'del'
    ;
    @@{attribute OF} @{syntax thmrefs}
    ;
    @@{attribute of} @{syntax insts} ('concl' ':' @{syntax insts})?
    ;
    @@{attribute \"where\"}
      ((@{syntax name} | @{syntax var} | @{syntax typefree} | @{syntax typevar}) '='
      (@{syntax type} | @{syntax term}) * @'and')
  "}

  \begin{description}
  
  \item ``@{method "-"}'' (minus) does nothing but insert the forward
  chaining facts as premises into the goal.  Note that command
  @{command_ref "proof"} without any method actually performs a single
  reduction step using the @{method_ref (Pure) rule} method; thus a plain
  \emph{do-nothing} proof step would be ``@{command "proof"}~@{text
  "-"}'' rather than @{command "proof"} alone.
  
  \item @{method "fact"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} composes some fact from
  @{text "a\<^sub>1, \<dots>, a\<^sub>n"} (or implicitly from the current proof context)
  modulo unification of schematic type and term variables.  The rule
  structure is not taken into account, i.e.\ meta-level implication is
  considered atomic.  This is the same principle underlying literal
  facts (cf.\ \secref{sec:syn-att}): ``@{command "have"}~@{text
  "\<phi>"}~@{command "by"}~@{text fact}'' is equivalent to ``@{command
  "note"}~@{verbatim "`"}@{text \<phi>}@{verbatim "`"}'' provided that
  @{text "\<turnstile> \<phi>"} is an instance of some known @{text "\<turnstile> \<phi>"} in the
  proof context.
  
  \item @{method assumption} solves some goal by a single assumption
  step.  All given facts are guaranteed to participate in the
  refinement; this means there may be only 0 or 1 in the first place.
  Recall that @{command "qed"} (\secref{sec:proof-steps}) already
  concludes any remaining sub-goals by assumption, so structured
  proofs usually need not quote the @{method assumption} method at
  all.
  
  \item @{method this} applies all of the current facts directly as
  rules.  Recall that ``@{command "."}'' (dot) abbreviates ``@{command
  "by"}~@{text this}''.
  
  \item @{method (Pure) rule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} applies some rule given as
  argument in backward manner; facts are used to reduce the rule
  before applying it to the goal.  Thus @{method (Pure) rule} without facts
  is plain introduction, while with facts it becomes elimination.
  
  When no arguments are given, the @{method (Pure) rule} method tries to pick
  appropriate rules automatically, as declared in the current context
  using the @{attribute (Pure) intro}, @{attribute (Pure) elim},
  @{attribute (Pure) dest} attributes (see below).  This is the
  default behavior of @{command "proof"} and ``@{command ".."}'' 
  (double-dot) steps (see \secref{sec:proof-steps}).
  
  \item @{attribute (Pure) intro}, @{attribute (Pure) elim}, and
  @{attribute (Pure) dest} declare introduction, elimination, and
  destruct rules, to be used with method @{method (Pure) rule}, and similar
  tools.  Note that the latter will ignore rules declared with
  ``@{text "?"}'', while ``@{text "!"}''  are used most aggressively.
  
  The classical reasoner (see \secref{sec:classical}) introduces its
  own variants of these attributes; use qualified names to access the
  present versions of Isabelle/Pure, i.e.\ @{attribute (Pure)
  "Pure.intro"}.
  
  \item @{attribute (Pure) rule}~@{text del} undeclares introduction,
  elimination, or destruct rules.
  
  \item @{attribute OF}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} applies some theorem to all
  of the given rules @{text "a\<^sub>1, \<dots>, a\<^sub>n"} in canonical right-to-left
  order, which means that premises stemming from the @{text "a\<^sub>i"}
  emerge in parallel in the result, without interfering with each
  other.  In many practical situations, the @{text "a\<^sub>i"} do not have
  premises themselves, so @{text "rule [OF a\<^sub>1 \<dots> a\<^sub>n]"} can be actually
  read as functional application (modulo unification).

  Argument positions may be effectively skipped by using ``@{text _}''
  (underscore), which refers to the propositional identity rule in the
  Pure theory.
  
  \item @{attribute of}~@{text "t\<^sub>1 \<dots> t\<^sub>n"} performs positional
  instantiation of term variables.  The terms @{text "t\<^sub>1, \<dots>, t\<^sub>n"} are
  substituted for any schematic variables occurring in a theorem from
  left to right; ``@{text _}'' (underscore) indicates to skip a
  position.  Arguments following a ``@{text "concl:"}'' specification
  refer to positions of the conclusion of a rule.
  
  \item @{attribute "where"}~@{text "x\<^sub>1 = t\<^sub>1 \<AND> \<dots> x\<^sub>n = t\<^sub>n"}
  performs named instantiation of schematic type and term variables
  occurring in a theorem.  Schematic variables have to be specified on
  the left-hand side (e.g.\ @{text "?x1.3"}).  The question mark may
  be omitted if the variable name is a plain identifier without index.
  As type instantiations are inferred from term instantiations,
  explicit type instantiations are seldom necessary.

  \end{description}
*}


subsection {* Emulating tactic scripts \label{sec:tactic-commands} *}

text {*
  The Isar provides separate commands to accommodate tactic-style
  proof scripts within the same system.  While being outside the
  orthodox Isar proof language, these might come in handy for
  interactive exploration and debugging, or even actual tactical proof
  within new-style theories (to benefit from document preparation, for
  example).  See also \secref{sec:tactics} for actual tactics, that
  have been encapsulated as proof methods.  Proper proof methods may
  be used in scripts, too.

  \begin{matharray}{rcl}
    @{command_def "apply"}@{text "\<^sup>*"} & : & @{text "proof(prove) \<rightarrow> proof(prove)"} \\
    @{command_def "apply_end"}@{text "\<^sup>*"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "done"}@{text "\<^sup>*"} & : & @{text "proof(prove) \<rightarrow> proof(state) | local_theory | theory"} \\
    @{command_def "defer"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "prefer"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "back"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow> proof"} \\
  \end{matharray}

  @{rail "
    ( @@{command apply} | @@{command apply_end} ) @{syntax method}
    ;
    @@{command defer} @{syntax nat}?
    ;
    @@{command prefer} @{syntax nat}
  "}

  \begin{description}

  \item @{command "apply"}~@{text m} applies proof method @{text m} in
  initial position, but unlike @{command "proof"} it retains ``@{text
  "proof(prove)"}'' mode.  Thus consecutive method applications may be
  given just as in tactic scripts.
  
  Facts are passed to @{text m} as indicated by the goal's
  forward-chain mode, and are \emph{consumed} afterwards.  Thus any
  further @{command "apply"} command would always work in a purely
  backward manner.
  
  \item @{command "apply_end"}~@{text "m"} applies proof method @{text
  m} as if in terminal position.  Basically, this simulates a
  multi-step tactic script for @{command "qed"}, but may be given
  anywhere within the proof body.
  
  No facts are passed to @{text m} here.  Furthermore, the static
  context is that of the enclosing goal (as for actual @{command
  "qed"}).  Thus the proof method may not refer to any assumptions
  introduced in the current body, for example.
  
  \item @{command "done"} completes a proof script, provided that the
  current goal state is solved completely.  Note that actual
  structured proof commands (e.g.\ ``@{command "."}'' or @{command
  "sorry"}) may be used to conclude proof scripts as well.

  \item @{command "defer"}~@{text n} and @{command "prefer"}~@{text n}
  shuffle the list of pending goals: @{command "defer"} puts off
  sub-goal @{text n} to the end of the list (@{text "n = 1"} by
  default), while @{command "prefer"} brings sub-goal @{text n} to the
  front.
  
  \item @{command "back"} does back-tracking over the result sequence
  of the latest proof command.  Basically, any proof command may
  return multiple results.
  
  \end{description}

  Any proper Isar proof method may be used with tactic script commands
  such as @{command "apply"}.  A few additional emulations of actual
  tactics are provided as well; these would be never used in actual
  structured proofs, of course.
*}


subsection {* Defining proof methods *}

text {*
  \begin{matharray}{rcl}
    @{command_def "method_setup"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
    @@{command method_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
    ;
  "}

  \begin{description}

  \item @{command "method_setup"}~@{text "name = text description"}
  defines a proof method in the current theory.  The given @{text
  "text"} has to be an ML expression of type
  @{ML_type "(Proof.context -> Proof.method) context_parser"}, cf.\
  basic parsers defined in structure @{ML_struct Args} and @{ML_struct
  Attrib}.  There are also combinators like @{ML METHOD} and @{ML
  SIMPLE_METHOD} to turn certain tactic forms into official proof
  methods; the primed versions refer to tactics with explicit goal
  addressing.

  Here are some example method definitions:

  \end{description}
*}

  method_setup my_method1 = {*
    Scan.succeed (K (SIMPLE_METHOD' (fn i: int => no_tac)))
  *}  "my first method (without any arguments)"

  method_setup my_method2 = {*
    Scan.succeed (fn ctxt: Proof.context =>
      SIMPLE_METHOD' (fn i: int => no_tac))
  *}  "my second method (with context)"

  method_setup my_method3 = {*
    Attrib.thms >> (fn thms: thm list => fn ctxt: Proof.context =>
      SIMPLE_METHOD' (fn i: int => no_tac))
  *}  "my third method (with theorem arguments and context)"


section {* Generalized elimination \label{sec:obtain} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "obtain"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
    @{command_def "guess"}@{text "\<^sup>*"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
  \end{matharray}

  Generalized elimination means that additional elements with certain
  properties may be introduced in the current context, by virtue of a
  locally proven ``soundness statement''.  Technically speaking, the
  @{command "obtain"} language element is like a declaration of
  @{command "fix"} and @{command "assume"} (see also see
  \secref{sec:proof-context}), together with a soundness proof of its
  additional claim.  According to the nature of existential reasoning,
  assumptions get eliminated from any result exported from the context
  later, provided that the corresponding parameters do \emph{not}
  occur in the conclusion.

  @{rail "
    @@{command obtain} @{syntax parname}? (@{syntax vars} + @'and')
      @'where' (@{syntax props} + @'and')
    ;
    @@{command guess} (@{syntax vars} + @'and')
  "}

  The derived Isar command @{command "obtain"} is defined as follows
  (where @{text "b\<^sub>1, \<dots>, b\<^sub>k"} shall refer to (optional)
  facts indicated for forward chaining).
  \begin{matharray}{l}
    @{text "\<langle>using b\<^sub>1 \<dots> b\<^sub>k\<rangle>"}~~@{command "obtain"}~@{text "x\<^sub>1 \<dots> x\<^sub>m \<WHERE> a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n  \<langle>proof\<rangle> \<equiv>"} \\[1ex]
    \quad @{command "have"}~@{text "\<And>thesis. (\<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> thesis) \<Longrightarrow> thesis"} \\
    \quad @{command "proof"}~@{method succeed} \\
    \qquad @{command "fix"}~@{text thesis} \\
    \qquad @{command "assume"}~@{text "that [Pure.intro?]: \<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> thesis"} \\
    \qquad @{command "then"}~@{command "show"}~@{text thesis} \\
    \quad\qquad @{command "apply"}~@{text -} \\
    \quad\qquad @{command "using"}~@{text "b\<^sub>1 \<dots> b\<^sub>k  \<langle>proof\<rangle>"} \\
    \quad @{command "qed"} \\
    \quad @{command "fix"}~@{text "x\<^sub>1 \<dots> x\<^sub>m"}~@{command "assume"}@{text "\<^sup>* a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"} \\
  \end{matharray}

  Typically, the soundness proof is relatively straight-forward, often
  just by canonical automated tools such as ``@{command "by"}~@{text
  simp}'' or ``@{command "by"}~@{text blast}''.  Accordingly, the
  ``@{text that}'' reduction above is declared as simplification and
  introduction rule.

  In a sense, @{command "obtain"} represents at the level of Isar
  proofs what would be meta-logical existential quantifiers and
  conjunctions.  This concept has a broad range of useful
  applications, ranging from plain elimination (or introduction) of
  object-level existential and conjunctions, to elimination over
  results of symbolic evaluation of recursive definitions, for
  example.  Also note that @{command "obtain"} without parameters acts
  much like @{command "have"}, where the result is treated as a
  genuine assumption.

  An alternative name to be used instead of ``@{text that}'' above may
  be given in parentheses.

  \medskip The improper variant @{command "guess"} is similar to
  @{command "obtain"}, but derives the obtained statement from the
  course of reasoning!  The proof starts with a fixed goal @{text
  thesis}.  The subsequent proof may refine this to anything of the
  form like @{text "\<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots>
  \<phi>\<^sub>n \<Longrightarrow> thesis"}, but must not introduce new subgoals.  The
  final goal state is then used as reduction rule for the obtain
  scheme described above.  Obtained parameters @{text "x\<^sub>1, \<dots>,
  x\<^sub>m"} are marked as internal by default, which prevents the
  proof context from being polluted by ad-hoc variables.  The variable
  names and type constraints given as arguments for @{command "guess"}
  specify a prefix of obtained parameters explicitly in the text.

  It is important to note that the facts introduced by @{command
  "obtain"} and @{command "guess"} may not be polymorphic: any
  type-variables occurring here are fixed in the present context!
*}


section {* Calculational reasoning \label{sec:calculation} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "also"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "finally"} & : & @{text "proof(state) \<rightarrow> proof(chain)"} \\
    @{command_def "moreover"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "ultimately"} & : & @{text "proof(state) \<rightarrow> proof(chain)"} \\
    @{command_def "print_trans_rules"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute trans} & : & @{text attribute} \\
    @{attribute sym} & : & @{text attribute} \\
    @{attribute symmetric} & : & @{text attribute} \\
  \end{matharray}

  Calculational proof is forward reasoning with implicit application
  of transitivity rules (such those of @{text "="}, @{text "\<le>"},
  @{text "<"}).  Isabelle/Isar maintains an auxiliary fact register
  @{fact_ref calculation} for accumulating results obtained by
  transitivity composed with the current result.  Command @{command
  "also"} updates @{fact calculation} involving @{fact this}, while
  @{command "finally"} exhibits the final @{fact calculation} by
  forward chaining towards the next goal statement.  Both commands
  require valid current facts, i.e.\ may occur only after commands
  that produce theorems such as @{command "assume"}, @{command
  "note"}, or some finished proof of @{command "have"}, @{command
  "show"} etc.  The @{command "moreover"} and @{command "ultimately"}
  commands are similar to @{command "also"} and @{command "finally"},
  but only collect further results in @{fact calculation} without
  applying any rules yet.

  Also note that the implicit term abbreviation ``@{text "\<dots>"}'' has
  its canonical application with calculational proofs.  It refers to
  the argument of the preceding statement. (The argument of a curried
  infix expression happens to be its right-hand side.)

  Isabelle/Isar calculations are implicitly subject to block structure
  in the sense that new threads of calculational reasoning are
  commenced for any new block (as opened by a local goal, for
  example).  This means that, apart from being able to nest
  calculations, there is no separate \emph{begin-calculation} command
  required.

  \medskip The Isar calculation proof commands may be defined as
  follows:\footnote{We suppress internal bookkeeping such as proper
  handling of block-structure.}

  \begin{matharray}{rcl}
    @{command "also"}@{text "\<^sub>0"} & \equiv & @{command "note"}~@{text "calculation = this"} \\
    @{command "also"}@{text "\<^sub>n+1"} & \equiv & @{command "note"}~@{text "calculation = trans [OF calculation this]"} \\[0.5ex]
    @{command "finally"} & \equiv & @{command "also"}~@{command "from"}~@{text calculation} \\[0.5ex]
    @{command "moreover"} & \equiv & @{command "note"}~@{text "calculation = calculation this"} \\
    @{command "ultimately"} & \equiv & @{command "moreover"}~@{command "from"}~@{text calculation} \\
  \end{matharray}

  @{rail "
    (@@{command also} | @@{command finally}) ('(' @{syntax thmrefs} ')')?
    ;
    @@{attribute trans} (() | 'add' | 'del')
  "}

  \begin{description}

  \item @{command "also"}~@{text "(a\<^sub>1 \<dots> a\<^sub>n)"} maintains the auxiliary
  @{fact calculation} register as follows.  The first occurrence of
  @{command "also"} in some calculational thread initializes @{fact
  calculation} by @{fact this}. Any subsequent @{command "also"} on
  the same level of block-structure updates @{fact calculation} by
  some transitivity rule applied to @{fact calculation} and @{fact
  this} (in that order).  Transitivity rules are picked from the
  current context, unless alternative rules are given as explicit
  arguments.

  \item @{command "finally"}~@{text "(a\<^sub>1 \<dots> a\<^sub>n)"} maintaining @{fact
  calculation} in the same way as @{command "also"}, and concludes the
  current calculational thread.  The final result is exhibited as fact
  for forward chaining towards the next goal. Basically, @{command
  "finally"} just abbreviates @{command "also"}~@{command
  "from"}~@{fact calculation}.  Typical idioms for concluding
  calculational proofs are ``@{command "finally"}~@{command
  "show"}~@{text ?thesis}~@{command "."}'' and ``@{command
  "finally"}~@{command "have"}~@{text \<phi>}~@{command "."}''.

  \item @{command "moreover"} and @{command "ultimately"} are
  analogous to @{command "also"} and @{command "finally"}, but collect
  results only, without applying rules.

  \item @{command "print_trans_rules"} prints the list of transitivity
  rules (for calculational commands @{command "also"} and @{command
  "finally"}) and symmetry rules (for the @{attribute symmetric}
  operation and single step elimination patters) of the current
  context.

  \item @{attribute trans} declares theorems as transitivity rules.

  \item @{attribute sym} declares symmetry rules, as well as
  @{attribute "Pure.elim"}@{text "?"} rules.

  \item @{attribute symmetric} resolves a theorem with some rule
  declared as @{attribute sym} in the current context.  For example,
  ``@{command "assume"}~@{text "[symmetric]: x = y"}'' produces a
  swapped fact derived from that assumption.

  In structured proof texts it is often more appropriate to use an
  explicit single-step elimination proof, such as ``@{command
  "assume"}~@{text "x = y"}~@{command "then"}~@{command "have"}~@{text
  "y = x"}~@{command ".."}''.

  \end{description}
*}


section {* Proof by cases and induction \label{sec:cases-induct} *}

subsection {* Rule contexts *}

text {*
  \begin{matharray}{rcl}
    @{command_def "case"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "print_cases"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def case_names} & : & @{text attribute} \\
    @{attribute_def case_conclusion} & : & @{text attribute} \\
    @{attribute_def params} & : & @{text attribute} \\
    @{attribute_def consumes} & : & @{text attribute} \\
  \end{matharray}

  The puristic way to build up Isar proof contexts is by explicit
  language elements like @{command "fix"}, @{command "assume"},
  @{command "let"} (see \secref{sec:proof-context}).  This is adequate
  for plain natural deduction, but easily becomes unwieldy in concrete
  verification tasks, which typically involve big induction rules with
  several cases.

  The @{command "case"} command provides a shorthand to refer to a
  local context symbolically: certain proof methods provide an
  environment of named ``cases'' of the form @{text "c: x\<^sub>1, \<dots>,
  x\<^sub>m, \<phi>\<^sub>1, \<dots>, \<phi>\<^sub>n"}; the effect of ``@{command
  "case"}~@{text c}'' is then equivalent to ``@{command "fix"}~@{text
  "x\<^sub>1 \<dots> x\<^sub>m"}~@{command "assume"}~@{text "c: \<phi>\<^sub>1 \<dots>
  \<phi>\<^sub>n"}''.  Term bindings may be covered as well, notably
  @{variable ?case} for the main conclusion.

  By default, the ``terminology'' @{text "x\<^sub>1, \<dots>, x\<^sub>m"} of
  a case value is marked as hidden, i.e.\ there is no way to refer to
  such parameters in the subsequent proof text.  After all, original
  rule parameters stem from somewhere outside of the current proof
  text.  By using the explicit form ``@{command "case"}~@{text "(c
  y\<^sub>1 \<dots> y\<^sub>m)"}'' instead, the proof author is able to
  chose local names that fit nicely into the current context.

  \medskip It is important to note that proper use of @{command
  "case"} does not provide means to peek at the current goal state,
  which is not directly observable in Isar!  Nonetheless, goal
  refinement commands do provide named cases @{text "goal\<^sub>i"}
  for each subgoal @{text "i = 1, \<dots>, n"} of the resulting goal state.
  Using this extra feature requires great care, because some bits of
  the internal tactical machinery intrude the proof text.  In
  particular, parameter names stemming from the left-over of automated
  reasoning tools are usually quite unpredictable.

  Under normal circumstances, the text of cases emerge from standard
  elimination or induction rules, which in turn are derived from
  previous theory specifications in a canonical way (say from
  @{command "inductive"} definitions).

  \medskip Proper cases are only available if both the proof method
  and the rules involved support this.  By using appropriate
  attributes, case names, conclusions, and parameters may be also
  declared by hand.  Thus variant versions of rules that have been
  derived manually become ready to use in advanced case analysis
  later.

  @{rail "
    @@{command case} (caseref | '(' caseref (('_' | @{syntax name}) +) ')')
    ;
    caseref: nameref attributes?
    ;

    @@{attribute case_names} ((@{syntax name} ( '[' (('_' | @{syntax name}) +) ']' ) ? ) +)
    ;
    @@{attribute case_conclusion} @{syntax name} (@{syntax name} * )
    ;
    @@{attribute params} ((@{syntax name} * ) + @'and')
    ;
    @@{attribute consumes} @{syntax nat}?
  "}

  \begin{description}
  
  \item @{command "case"}~@{text "(c x\<^sub>1 \<dots> x\<^sub>m)"} invokes a named local
  context @{text "c: x\<^sub>1, \<dots>, x\<^sub>m, \<phi>\<^sub>1, \<dots>, \<phi>\<^sub>m"}, as provided by an
  appropriate proof method (such as @{method_ref cases} and
  @{method_ref induct}).  The command ``@{command "case"}~@{text "(c
  x\<^sub>1 \<dots> x\<^sub>m)"}'' abbreviates ``@{command "fix"}~@{text "x\<^sub>1 \<dots>
  x\<^sub>m"}~@{command "assume"}~@{text "c: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}''.

  \item @{command "print_cases"} prints all local contexts of the
  current state, using Isar proof language notation.
  
  \item @{attribute case_names}~@{text "c\<^sub>1 \<dots> c\<^sub>k"} declares names for
  the local contexts of premises of a theorem; @{text "c\<^sub>1, \<dots>, c\<^sub>k"}
  refers to the \emph{prefix} of the list of premises. Each of the
  cases @{text "c\<^isub>i"} can be of the form @{text "c[h\<^isub>1 \<dots> h\<^isub>n]"} where
  the @{text "h\<^isub>1 \<dots> h\<^isub>n"} are the names of the hypotheses in case @{text "c\<^isub>i"}
  from left to right.
  
  \item @{attribute case_conclusion}~@{text "c d\<^sub>1 \<dots> d\<^sub>k"} declares
  names for the conclusions of a named premise @{text c}; here @{text
  "d\<^sub>1, \<dots>, d\<^sub>k"} refers to the prefix of arguments of a logical formula
  built by nesting a binary connective (e.g.\ @{text "\<or>"}).
  
  Note that proof methods such as @{method induct} and @{method
  coinduct} already provide a default name for the conclusion as a
  whole.  The need to name subformulas only arises with cases that
  split into several sub-cases, as in common co-induction rules.

  \item @{attribute params}~@{text "p\<^sub>1 \<dots> p\<^sub>m \<AND> \<dots> q\<^sub>1 \<dots> q\<^sub>n"} renames
  the innermost parameters of premises @{text "1, \<dots>, n"} of some
  theorem.  An empty list of names may be given to skip positions,
  leaving the present parameters unchanged.
  
  Note that the default usage of case rules does \emph{not} directly
  expose parameters to the proof context.
  
  \item @{attribute consumes}~@{text n} declares the number of ``major
  premises'' of a rule, i.e.\ the number of facts to be consumed when
  it is applied by an appropriate proof method.  The default value of
  @{attribute consumes} is @{text "n = 1"}, which is appropriate for
  the usual kind of cases and induction rules for inductive sets (cf.\
  \secref{sec:hol-inductive}).  Rules without any @{attribute
  consumes} declaration given are treated as if @{attribute
  consumes}~@{text 0} had been specified.
  
  Note that explicit @{attribute consumes} declarations are only
  rarely needed; this is already taken care of automatically by the
  higher-level @{attribute cases}, @{attribute induct}, and
  @{attribute coinduct} declarations.

  \end{description}
*}


subsection {* Proof methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def cases} & : & @{text method} \\
    @{method_def induct} & : & @{text method} \\
    @{method_def induction} & : & @{text method} \\
    @{method_def coinduct} & : & @{text method} \\
  \end{matharray}

  The @{method cases}, @{method induct}, @{method induction},
  and @{method coinduct}
  methods provide a uniform interface to common proof techniques over
  datatypes, inductive predicates (or sets), recursive functions etc.
  The corresponding rules may be specified and instantiated in a
  casual manner.  Furthermore, these methods provide named local
  contexts that may be invoked via the @{command "case"} proof command
  within the subsequent proof text.  This accommodates compact proof
  texts even when reasoning about large specifications.

  The @{method induct} method also provides some additional
  infrastructure in order to be applicable to structure statements
  (either using explicit meta-level connectives, or including facts
  and parameters separately).  This avoids cumbersome encoding of
  ``strengthened'' inductive statements within the object-logic.

  Method @{method induction} differs from @{method induct} only in
  the names of the facts in the local context invoked by the @{command "case"}
  command.

  @{rail "
    @@{method cases} ('(' 'no_simp' ')')? \\
      (@{syntax insts} * @'and') rule?
    ;
    (@@{method induct} | @@{method induction}) ('(' 'no_simp' ')')? (definsts * @'and') \\ arbitrary? taking? rule?
    ;
    @@{method coinduct} @{syntax insts} taking rule?
    ;

    rule: ('type' | 'pred' | 'set') ':' (@{syntax nameref} +) | 'rule' ':' (@{syntax thmref} +)
    ;
    definst: @{syntax name} ('==' | '\<equiv>') @{syntax term} | '(' @{syntax term} ')' | @{syntax inst}
    ;
    definsts: ( definst * )
    ;
    arbitrary: 'arbitrary' ':' ((@{syntax term} * ) @'and' +)
    ;
    taking: 'taking' ':' @{syntax insts}
  "}

  \begin{description}

  \item @{method cases}~@{text "insts R"} applies method @{method
  rule} with an appropriate case distinction theorem, instantiated to
  the subjects @{text insts}.  Symbolic case names are bound according
  to the rule's local contexts.

  The rule is determined as follows, according to the facts and
  arguments passed to the @{method cases} method:

  \medskip
  \begin{tabular}{llll}
    facts           &                 & arguments   & rule \\\hline
                    & @{method cases} &             & classical case split \\
                    & @{method cases} & @{text t}   & datatype exhaustion (type of @{text t}) \\
    @{text "\<turnstile> A t"} & @{method cases} & @{text "\<dots>"} & inductive predicate/set elimination (of @{text A}) \\
    @{text "\<dots>"}     & @{method cases} & @{text "\<dots> rule: R"} & explicit rule @{text R} \\
  \end{tabular}
  \medskip

  Several instantiations may be given, referring to the \emph{suffix}
  of premises of the case rule; within each premise, the \emph{prefix}
  of variables is instantiated.  In most situations, only a single
  term needs to be specified; this refers to the first variable of the
  last premise (it is usually the same for all cases).  The @{text
  "(no_simp)"} option can be used to disable pre-simplification of
  cases (see the description of @{method induct} below for details).

  \item @{method induct}~@{text "insts R"} and
  @{method induction}~@{text "insts R"} are analogous to the
  @{method cases} method, but refer to induction rules, which are
  determined as follows:

  \medskip
  \begin{tabular}{llll}
    facts           &                  & arguments            & rule \\\hline
                    & @{method induct} & @{text "P x"}        & datatype induction (type of @{text x}) \\
    @{text "\<turnstile> A x"} & @{method induct} & @{text "\<dots>"}          & predicate/set induction (of @{text A}) \\
    @{text "\<dots>"}     & @{method induct} & @{text "\<dots> rule: R"} & explicit rule @{text R} \\
  \end{tabular}
  \medskip
  
  Several instantiations may be given, each referring to some part of
  a mutual inductive definition or datatype --- only related partial
  induction rules may be used together, though.  Any of the lists of
  terms @{text "P, x, \<dots>"} refers to the \emph{suffix} of variables
  present in the induction rule.  This enables the writer to specify
  only induction variables, or both predicates and variables, for
  example.

  Instantiations may be definitional: equations @{text "x \<equiv> t"}
  introduce local definitions, which are inserted into the claim and
  discharged after applying the induction rule.  Equalities reappear
  in the inductive cases, but have been transformed according to the
  induction principle being involved here.  In order to achieve
  practically useful induction hypotheses, some variables occurring in
  @{text t} need to be fixed (see below).  Instantiations of the form
  @{text t}, where @{text t} is not a variable, are taken as a
  shorthand for \mbox{@{text "x \<equiv> t"}}, where @{text x} is a fresh
  variable. If this is not intended, @{text t} has to be enclosed in
  parentheses.  By default, the equalities generated by definitional
  instantiations are pre-simplified using a specific set of rules,
  usually consisting of distinctness and injectivity theorems for
  datatypes. This pre-simplification may cause some of the parameters
  of an inductive case to disappear, or may even completely delete
  some of the inductive cases, if one of the equalities occurring in
  their premises can be simplified to @{text False}.  The @{text
  "(no_simp)"} option can be used to disable pre-simplification.
  Additional rules to be used in pre-simplification can be declared
  using the @{attribute_def induct_simp} attribute.

  The optional ``@{text "arbitrary: x\<^sub>1 \<dots> x\<^sub>m"}''
  specification generalizes variables @{text "x\<^sub>1, \<dots>,
  x\<^sub>m"} of the original goal before applying induction.  One can
  separate variables by ``@{text "and"}'' to generalize them in other
  goals then the first. Thus induction hypotheses may become
  sufficiently general to get the proof through.  Together with
  definitional instantiations, one may effectively perform induction
  over expressions of a certain structure.
  
  The optional ``@{text "taking: t\<^sub>1 \<dots> t\<^sub>n"}''
  specification provides additional instantiations of a prefix of
  pending variables in the rule.  Such schematic induction rules
  rarely occur in practice, though.

  \item @{method coinduct}~@{text "inst R"} is analogous to the
  @{method induct} method, but refers to coinduction rules, which are
  determined as follows:

  \medskip
  \begin{tabular}{llll}
    goal          &                    & arguments & rule \\\hline
                  & @{method coinduct} & @{text x} & type coinduction (type of @{text x}) \\
    @{text "A x"} & @{method coinduct} & @{text "\<dots>"} & predicate/set coinduction (of @{text A}) \\
    @{text "\<dots>"}   & @{method coinduct} & @{text "\<dots> rule: R"} & explicit rule @{text R} \\
  \end{tabular}
  
  Coinduction is the dual of induction.  Induction essentially
  eliminates @{text "A x"} towards a generic result @{text "P x"},
  while coinduction introduces @{text "A x"} starting with @{text "B
  x"}, for a suitable ``bisimulation'' @{text B}.  The cases of a
  coinduct rule are typically named after the predicates or sets being
  covered, while the conclusions consist of several alternatives being
  named after the individual destructor patterns.
  
  The given instantiation refers to the \emph{suffix} of variables
  occurring in the rule's major premise, or conclusion if unavailable.
  An additional ``@{text "taking: t\<^sub>1 \<dots> t\<^sub>n"}''
  specification may be required in order to specify the bisimulation
  to be used in the coinduction step.

  \end{description}

  Above methods produce named local contexts, as determined by the
  instantiated rule as given in the text.  Beyond that, the @{method
  induct} and @{method coinduct} methods guess further instantiations
  from the goal specification itself.  Any persisting unresolved
  schematic variables of the resulting rule will render the the
  corresponding case invalid.  The term binding @{variable ?case} for
  the conclusion will be provided with each case, provided that term
  is fully specified.

  The @{command "print_cases"} command prints all named cases present
  in the current proof state.

  \medskip Despite the additional infrastructure, both @{method cases}
  and @{method coinduct} merely apply a certain rule, after
  instantiation, while conforming due to the usual way of monotonic
  natural deduction: the context of a structured statement @{text
  "\<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> \<dots>"}
  reappears unchanged after the case split.

  The @{method induct} method is fundamentally different in this
  respect: the meta-level structure is passed through the
  ``recursive'' course involved in the induction.  Thus the original
  statement is basically replaced by separate copies, corresponding to
  the induction hypotheses and conclusion; the original goal context
  is no longer available.  Thus local assumptions, fixed parameters
  and definitions effectively participate in the inductive rephrasing
  of the original statement.

  In @{method induct} proofs, local assumptions introduced by cases are split
  into two different kinds: @{text hyps} stemming from the rule and
  @{text prems} from the goal statement.  This is reflected in the
  extracted cases accordingly, so invoking ``@{command "case"}~@{text
  c}'' will provide separate facts @{text c.hyps} and @{text c.prems},
  as well as fact @{text c} to hold the all-inclusive list.

  In @{method induction} proofs, local assumptions introduced by cases are
  split into three different kinds: @{text IH}, the induction hypotheses,
  @{text hyps}, the remaining hypotheses stemming from the rule, and
  @{text prems}, the assumptions from the goal statement. The names are
  @{text c.IH}, @{text c.hyps} and @{text c.prems}, as above.


  \medskip Facts presented to either method are consumed according to
  the number of ``major premises'' of the rule involved, which is
  usually 0 for plain cases and induction rules of datatypes etc.\ and
  1 for rules of inductive predicates or sets and the like.  The
  remaining facts are inserted into the goal verbatim before the
  actual @{text cases}, @{text induct}, or @{text coinduct} rule is
  applied.
*}


subsection {* Declaring rules *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_induct_rules"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def cases} & : & @{text attribute} \\
    @{attribute_def induct} & : & @{text attribute} \\
    @{attribute_def coinduct} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{attribute cases} spec
    ;
    @@{attribute induct} spec
    ;
    @@{attribute coinduct} spec
    ;

    spec: (('type' | 'pred' | 'set') ':' @{syntax nameref}) | 'del'
  "}

  \begin{description}

  \item @{command "print_induct_rules"} prints cases and induct rules
  for predicates (or sets) and types of the current context.

  \item @{attribute cases}, @{attribute induct}, and @{attribute
  coinduct} (as attributes) declare rules for reasoning about
  (co)inductive predicates (or sets) and types, using the
  corresponding methods of the same name.  Certain definitional
  packages of object-logics usually declare emerging cases and
  induction rules as expected, so users rarely need to intervene.

  Rules may be deleted via the @{text "del"} specification, which
  covers all of the @{text "type"}/@{text "pred"}/@{text "set"}
  sub-categories simultaneously.  For example, @{attribute
  cases}~@{text del} removes any @{attribute cases} rules declared for
  some type, predicate, or set.
  
  Manual rule declarations usually refer to the @{attribute
  case_names} and @{attribute params} attributes to adjust names of
  cases and parameters of a rule; the @{attribute consumes}
  declaration is taken care of automatically: @{attribute
  consumes}~@{text 0} is specified for ``type'' rules and @{attribute
  consumes}~@{text 1} for ``predicate'' / ``set'' rules.

  \end{description}
*}

end

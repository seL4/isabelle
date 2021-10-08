(*:maxLineLen=78:*)

theory Proof
  imports Main Base
begin

chapter \<open>Proofs \label{ch:proofs}\<close>

text \<open>
  Proof commands perform transitions of Isar/VM machine configurations, which
  are block-structured, consisting of a stack of nodes with three main
  components: logical proof context, current facts, and open goals. Isar/VM
  transitions are typed according to the following three different modes of
  operation:

    \<^descr> \<open>proof(prove)\<close> means that a new goal has just been stated that is now to
    be \<^emph>\<open>proven\<close>; the next command may refine it by some proof method, and
    enter a sub-proof to establish the actual result.

    \<^descr> \<open>proof(state)\<close> is like a nested theory mode: the context may be
    augmented by \<^emph>\<open>stating\<close> additional assumptions, intermediate results etc.

    \<^descr> \<open>proof(chain)\<close> is intermediate between \<open>proof(state)\<close> and
    \<open>proof(prove)\<close>: existing facts (i.e.\ the contents of the special
    @{fact_ref this} register) have been just picked up in order to be used
    when refining the goal claimed next.

  The proof mode indicator may be understood as an instruction to the writer,
  telling what kind of operation may be performed next. The corresponding
  typings of proof commands restricts the shape of well-formed proof texts to
  particular command sequences. So dynamic arrangements of commands eventually
  turn out as static texts of a certain structure.

  \Appref{ap:refcard} gives a simplified grammar of the (extensible) language
  emerging that way from the different types of proof commands. The main ideas
  of the overall Isar framework are explained in \chref{ch:isar-framework}.
\<close>


section \<open>Proof structure\<close>

subsection \<open>Formal notepad\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "notepad"} & : & \<open>local_theory \<rightarrow> proof(state)\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command notepad} @'begin'
    ;
    @@{command end}
  \<close>

  \<^descr> @{command "notepad"}~@{keyword "begin"} opens a proof state without any
  goal statement. This allows to experiment with Isar, without producing any
  persistent result. The notepad is closed by @{command "end"}.
\<close>


subsection \<open>Blocks\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "next"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "{"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "}"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
  \end{matharray}

  While Isar is inherently block-structured, opening and closing blocks is
  mostly handled rather casually, with little explicit user-intervention. Any
  local goal statement automatically opens \<^emph>\<open>two\<close> internal blocks, which are
  closed again when concluding the sub-proof (by @{command "qed"} etc.).
  Sections of different context within a sub-proof may be switched via
  @{command "next"}, which is just a single block-close followed by block-open
  again. The effect of @{command "next"} is to reset the local proof context;
  there is no goal focus involved here!

  For slightly more advanced applications, there are explicit block
  parentheses as well. These typically achieve a stronger forward style of
  reasoning.

  \<^descr> @{command "next"} switches to a fresh block within a sub-proof, resetting
  the local context to the initial one.

  \<^descr> @{command "{"} and @{command "}"} explicitly open and close blocks. Any
  current facts pass through ``@{command "{"}'' unchanged, while ``@{command
  "}"}'' causes any result to be \<^emph>\<open>exported\<close> into the enclosing context. Thus
  fixed variables are generalized, assumptions discharged, and local
  definitions unfolded (cf.\ \secref{sec:proof-context}). There is no
  difference of @{command "assume"} and @{command "presume"} in this mode of
  forward reasoning --- in contrast to plain backward reasoning with the
  result exported at @{command "show"} time.
\<close>


subsection \<open>Omitting proofs\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "oops"} & : & \<open>proof \<rightarrow> local_theory | theory\<close> \\
  \end{matharray}

  The @{command "oops"} command discontinues the current proof attempt, while
  considering the partial proof text as properly processed. This is
  conceptually quite different from ``faking'' actual proofs via @{command_ref
  "sorry"} (see \secref{sec:proof-steps}): @{command "oops"} does not observe
  the proof structure at all, but goes back right to the theory level.
  Furthermore, @{command "oops"} does not produce any result theorem --- there
  is no intended claim to be able to complete the proof in any way.

  A typical application of @{command "oops"} is to explain Isar proofs
  \<^emph>\<open>within\<close> the system itself, in conjunction with the document preparation
  tools of Isabelle described in \chref{ch:document-prep}. Thus partial or
  even wrong proof attempts can be discussed in a logically sound manner. Note
  that the Isabelle {\LaTeX} macros can be easily adapted to print something
  like ``\<open>\<dots>\<close>'' instead of the keyword ``@{command "oops"}''.
\<close>


section \<open>Statements\<close>

subsection \<open>Context elements \label{sec:proof-context}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "fix"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "assume"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "presume"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "define"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
  \end{matharray}

  The logical proof context consists of fixed variables and assumptions. The
  former closely correspond to Skolem constants, or meta-level universal
  quantification as provided by the Isabelle/Pure logical framework.
  Introducing some \<^emph>\<open>arbitrary, but fixed\<close> variable via ``@{command
  "fix"}~\<open>x\<close>'' results in a local value that may be used in the subsequent
  proof as any other variable or constant. Furthermore, any result \<open>\<turnstile> \<phi>[x]\<close>
  exported from the context will be universally closed wrt.\ \<open>x\<close> at the
  outermost level: \<open>\<turnstile> \<And>x. \<phi>[x]\<close> (this is expressed in normal form using
  Isabelle's meta-variables).

  Similarly, introducing some assumption \<open>\<chi>\<close> has two effects. On the one hand,
  a local theorem is created that may be used as a fact in subsequent proof
  steps. On the other hand, any result \<open>\<chi> \<turnstile> \<phi>\<close> exported from the context
  becomes conditional wrt.\ the assumption: \<open>\<turnstile> \<chi> \<Longrightarrow> \<phi>\<close>. Thus, solving an
  enclosing goal using such a result would basically introduce a new subgoal
  stemming from the assumption. How this situation is handled depends on the
  version of assumption command used: while @{command "assume"} insists on
  solving the subgoal by unification with some premise of the goal, @{command
  "presume"} leaves the subgoal unchanged in order to be proved later by the
  user.

  Local definitions, introduced by ``\<^theory_text>\<open>define x where x = t\<close>'', are achieved
  by combining ``@{command "fix"}~\<open>x\<close>'' with another version of assumption
  that causes any hypothetical equation \<open>x \<equiv> t\<close> to be eliminated by the
  reflexivity rule. Thus, exporting some result \<open>x \<equiv> t \<turnstile> \<phi>[x]\<close> yields \<open>\<turnstile>
  \<phi>[t]\<close>.

  \<^rail>\<open>
    @@{command fix} @{syntax vars}
    ;
    (@@{command assume} | @@{command presume}) concl prems @{syntax for_fixes}
    ;
    concl: (@{syntax props} + @'and')
    ;
    prems: (@'if' (@{syntax props'} + @'and'))?
    ;
    @@{command define} @{syntax vars} @'where'
      (@{syntax props} + @'and') @{syntax for_fixes}
  \<close>

  \<^descr> @{command "fix"}~\<open>x\<close> introduces a local variable \<open>x\<close> that is \<^emph>\<open>arbitrary,
  but fixed\<close>.

  \<^descr> @{command "assume"}~\<open>a: \<phi>\<close> and @{command "presume"}~\<open>a: \<phi>\<close> introduce a
  local fact \<open>\<phi> \<turnstile> \<phi>\<close> by assumption. Subsequent results applied to an enclosing
  goal (e.g.\ by @{command_ref "show"}) are handled as follows: @{command
  "assume"} expects to be able to unify with existing premises in the goal,
  while @{command "presume"} leaves \<open>\<phi>\<close> as new subgoals.

  Several lists of assumptions may be given (separated by @{keyword_ref
  "and"}; the resulting list of current facts consists of all of these
  concatenated.

  A structured assumption like \<^theory_text>\<open>assume "B x" if "A x" for x\<close> is equivalent to
  \<^theory_text>\<open>assume "\<And>x. A x \<Longrightarrow> B x"\<close>, but vacuous quantification is avoided: a
  for-context only effects propositions according to actual use of variables.

  \<^descr> \<^theory_text>\<open>define x where "x = t"\<close> introduces a local (non-polymorphic) definition.
  In results that are exported from the context, \<open>x\<close> is replaced by \<open>t\<close>.

  Internally, equational assumptions are added to the context in Pure form,
  using \<open>x \<equiv> t\<close> instead of \<open>x = t\<close> or \<open>x \<longleftrightarrow> t\<close> from the object-logic. When
  exporting results from the context, \<open>x\<close> is generalized and the assumption
  discharged by reflexivity, causing the replacement by \<open>t\<close>.

  The default name for the definitional fact is \<open>x_def\<close>. Several simultaneous
  definitions may be given as well, with a collective default name.

  \<^medskip>
  It is also possible to abstract over local parameters as follows: \<^theory_text>\<open>define f
  :: "'a \<Rightarrow> 'b" where "f x = t" for x :: 'a\<close>.
\<close>


subsection \<open>Term abbreviations \label{sec:term-abbrev}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "let"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{keyword_def "is"} & : & syntax \\
  \end{matharray}

  Abbreviations may be either bound by explicit @{command "let"}~\<open>p \<equiv> t\<close>
  statements, or by annotating assumptions or goal statements with a list of
  patterns ``\<^theory_text>\<open>(is p\<^sub>1 \<dots> p\<^sub>n)\<close>''. In both cases, higher-order matching is
  invoked to bind extra-logical term variables, which may be either named
  schematic variables of the form \<open>?x\<close>, or nameless dummies ``@{variable _}''
  (underscore). Note that in the @{command "let"} form the patterns occur on
  the left-hand side, while the @{keyword "is"} patterns are in postfix
  position.

  Polymorphism of term bindings is handled in Hindley-Milner style, similar to
  ML. Type variables referring to local assumptions or open goal statements
  are \<^emph>\<open>fixed\<close>, while those of finished results or bound by @{command "let"}
  may occur in \<^emph>\<open>arbitrary\<close> instances later. Even though actual polymorphism
  should be rarely used in practice, this mechanism is essential to achieve
  proper incremental type-inference, as the user proceeds to build up the Isar
  proof text from left to right.

  \<^medskip>
  Term abbreviations are quite different from local definitions as introduced
  via @{command "define"} (see \secref{sec:proof-context}). The latter are
  visible within the logic as actual equations, while abbreviations disappear
  during the input process just after type checking. Also note that @{command
  "define"} does not support polymorphism.

  \<^rail>\<open>
    @@{command let} ((@{syntax term} + @'and') '=' @{syntax term} + @'and')
  \<close>

  The syntax of @{keyword "is"} patterns follows @{syntax term_pat} or
  @{syntax prop_pat} (see \secref{sec:term-decls}).

    \<^descr> \<^theory_text>\<open>let p\<^sub>1 = t\<^sub>1 and \<dots> p\<^sub>n = t\<^sub>n\<close> binds any text variables in patterns
    \<open>p\<^sub>1, \<dots>, p\<^sub>n\<close> by simultaneous higher-order matching against terms \<open>t\<^sub>1, \<dots>,
    t\<^sub>n\<close>.

    \<^descr> \<^theory_text>\<open>(is p\<^sub>1 \<dots> p\<^sub>n)\<close> resembles @{command "let"}, but matches \<open>p\<^sub>1, \<dots>, p\<^sub>n\<close>
    against the preceding statement. Also note that @{keyword "is"} is not a
    separate command, but part of others (such as @{command "assume"},
    @{command "have"} etc.).

  Some \<^emph>\<open>implicit\<close> term abbreviations\index{term abbreviations} for goals and
  facts are available as well. For any open goal, @{variable_ref thesis}
  refers to its object-level statement, abstracted over any meta-level
  parameters (if present). Likewise, @{variable_ref this} is bound for fact
  statements resulting from assumptions or finished goals. In case @{variable
  this} refers to an object-logic statement that is an application \<open>f t\<close>, then
  \<open>t\<close> is bound to the special text variable ``@{variable "\<dots>"}'' (three dots).
  The canonical application of this convenience are calculational proofs (see
  \secref{sec:calculation}).
\<close>


subsection \<open>Facts and forward chaining \label{sec:proof-facts}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "note"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "then"} & : & \<open>proof(state) \<rightarrow> proof(chain)\<close> \\
    @{command_def "from"} & : & \<open>proof(state) \<rightarrow> proof(chain)\<close> \\
    @{command_def "with"} & : & \<open>proof(state) \<rightarrow> proof(chain)\<close> \\
    @{command_def "using"} & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{command_def "unfolding"} & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{method_def "use"} & : & \<open>method\<close> \\
    @{fact_def "method_facts"} & : & \<open>fact\<close> \\
  \end{matharray}

  New facts are established either by assumption or proof of local statements.
  Any fact will usually be involved in further proofs, either as explicit
  arguments of proof methods, or when forward chaining towards the next goal
  via @{command "then"} (and variants); @{command "from"} and @{command
  "with"} are composite forms involving @{command "note"}. The @{command
  "using"} elements augments the collection of used facts \<^emph>\<open>after\<close> a goal has
  been stated. Note that the special theorem name @{fact_ref this} refers to
  the most recently established facts, but only \<^emph>\<open>before\<close> issuing a follow-up
  claim.

  \<^rail>\<open>
    @@{command note} (@{syntax thmdef}? @{syntax thms} + @'and')
    ;
    (@@{command from} | @@{command with} | @@{command using} | @@{command unfolding})
      (@{syntax thms} + @'and')
    ;
    @{method use} @{syntax thms} @'in' @{syntax method}
  \<close>

  \<^descr> @{command "note"}~\<open>a = b\<^sub>1 \<dots> b\<^sub>n\<close> recalls existing facts \<open>b\<^sub>1, \<dots>, b\<^sub>n\<close>,
  binding the result as \<open>a\<close>. Note that attributes may be involved as well,
  both on the left and right hand sides.

  \<^descr> @{command "then"} indicates forward chaining by the current facts in order
  to establish the goal to be claimed next. The initial proof method invoked
  to refine that will be offered the facts to do ``anything appropriate'' (see
  also \secref{sec:proof-steps}). For example, method @{method (Pure) rule}
  (see \secref{sec:pure-meth-att}) would typically do an elimination rather
  than an introduction. Automatic methods usually insert the facts into the
  goal state before operation. This provides a simple scheme to control
  relevance of facts in automated proof search.

  \<^descr> @{command "from"}~\<open>b\<close> abbreviates ``@{command "note"}~\<open>b\<close>~@{command
  "then"}''; thus @{command "then"} is equivalent to ``@{command
  "from"}~\<open>this\<close>''.

  \<^descr> @{command "with"}~\<open>b\<^sub>1 \<dots> b\<^sub>n\<close> abbreviates ``@{command "from"}~\<open>b\<^sub>1 \<dots> b\<^sub>n
  \<AND> this\<close>''; thus the forward chaining is from earlier facts together
  with the current ones.

  \<^descr> @{command "using"}~\<open>b\<^sub>1 \<dots> b\<^sub>n\<close> augments the facts to be used by a
  subsequent refinement step (such as @{command_ref "apply"} or @{command_ref
  "proof"}).

  \<^descr> @{command "unfolding"}~\<open>b\<^sub>1 \<dots> b\<^sub>n\<close> is structurally similar to @{command
  "using"}, but unfolds definitional equations \<open>b\<^sub>1 \<dots> b\<^sub>n\<close> throughout the goal
  state and facts. See also the proof method @{method_ref unfold}.

  \<^descr> \<^theory_text>\<open>(use b\<^sub>1 \<dots> b\<^sub>n in method)\<close> uses the facts in the given method
  expression. The facts provided by the proof state (via @{command "using"}
  etc.) are ignored, but it is possible to refer to @{fact method_facts}
  explicitly.

  \<^descr> @{fact method_facts} is a dynamic fact that refers to the currently used
  facts of the goal state.


  Forward chaining with an empty list of theorems is the same as not chaining
  at all. Thus ``@{command "from"}~\<open>nothing\<close>'' has no effect apart from
  entering \<open>prove(chain)\<close> mode, since @{fact_ref nothing} is bound to the
  empty list of theorems.

  Basic proof methods (such as @{method_ref (Pure) rule}) expect multiple
  facts to be given in their proper order, corresponding to a prefix of the
  premises of the rule involved. Note that positions may be easily skipped
  using something like @{command "from"}~\<open>_ \<AND> a \<AND> b\<close>, for example.
  This involves the trivial rule \<open>PROP \<psi> \<Longrightarrow> PROP \<psi>\<close>, which is bound in
  Isabelle/Pure as ``@{fact_ref "_"}'' (underscore).

  Automated methods (such as @{method simp} or @{method auto}) just insert any
  given facts before their usual operation. Depending on the kind of procedure
  involved, the order of facts is less significant here.
\<close>


subsection \<open>Goals \label{sec:goals}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "lemma"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "theorem"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "corollary"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "proposition"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "schematic_goal"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "have"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
    @{command_def "show"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
    @{command_def "hence"} & : & \<open>proof(state) \<rightarrow> proof(prove)\<close> \\
    @{command_def "thus"} & : & \<open>proof(state) \<rightarrow> proof(prove)\<close> \\
    @{command_def "print_statement"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  From a theory context, proof mode is entered by an initial goal command such
  as @{command "lemma"}. Within a proof context, new claims may be introduced
  locally; there are variants to interact with the overall proof structure
  specifically, such as @{command have} or @{command show}.

  Goals may consist of multiple statements, resulting in a list of facts
  eventually. A pending multi-goal is internally represented as a meta-level
  conjunction (\<open>&&&\<close>), which is usually split into the corresponding number of
  sub-goals prior to an initial method application, via @{command_ref "proof"}
  (\secref{sec:proof-steps}) or @{command_ref "apply"}
  (\secref{sec:tactic-commands}). The @{method_ref induct} method covered in
  \secref{sec:cases-induct} acts on multiple claims simultaneously.

  Claims at the theory level may be either in short or long form. A short goal
  merely consists of several simultaneous propositions (often just one). A
  long goal includes an explicit context specification for the subsequent
  conclusion, involving local parameters and assumptions. Here the role of
  each part of the statement is explicitly marked by separate keywords (see
  also \secref{sec:locale}); the local assumptions being introduced here are
  available as @{fact_ref assms} in the proof. Moreover, there are two kinds
  of conclusions: @{element_def "shows"} states several simultaneous
  propositions (essentially a big conjunction), while @{element_def "obtains"}
  claims several simultaneous contexts --- essentially a big disjunction of
  eliminated parameters and assumptions (see \secref{sec:obtain}).

  \<^rail>\<open>
    (@@{command lemma} | @@{command theorem} | @@{command corollary} |
     @@{command proposition} | @@{command schematic_goal})
      (long_statement | short_statement)
    ;
    (@@{command have} | @@{command show} | @@{command hence} | @@{command thus})
      stmt cond_stmt @{syntax for_fixes}
    ;
    @@{command print_statement} @{syntax modes}? @{syntax thms}
    ;

    stmt: (@{syntax props} + @'and')
    ;
    cond_stmt: ((@'if' | @'when') stmt)?
    ;
    short_statement: stmt (@'if' stmt)? @{syntax for_fixes}
    ;
    long_statement: @{syntax thmdecl}? context conclusion
    ;
    context: (@{syntax_ref "includes"}?) (@{syntax context_elem} *)
    ;
    conclusion: @'shows' stmt | @'obtains' @{syntax obtain_clauses}
    ;
    @{syntax_def obtain_clauses}: (@{syntax par_name}? obtain_case + '|')
    ;
    @{syntax_def obtain_case}: @{syntax vars} @'where'
      (@{syntax thmdecl}? (@{syntax prop}+) + @'and')
  \<close>

  \<^descr> @{command "lemma"}~\<open>a: \<phi>\<close> enters proof mode with \<open>\<phi>\<close> as main goal,
  eventually resulting in some fact \<open>\<turnstile> \<phi>\<close> to be put back into the target
  context.

  A @{syntax long_statement} may build up an initial proof context for the
  subsequent claim, potentially including local definitions and syntax; see
  also @{syntax "includes"} in \secref{sec:bundle} and @{syntax context_elem}
  in \secref{sec:locale}.

  A @{syntax short_statement} consists of propositions as conclusion, with an
  option context of premises and parameters, via \<^verbatim>\<open>if\<close>/\<^verbatim>\<open>for\<close> in postfix
  notation, corresponding to \<^verbatim>\<open>assumes\<close>/\<^verbatim>\<open>fixes\<close> in the long prefix notation.

  Local premises (if present) are called ``\<open>assms\<close>'' for @{syntax
  long_statement}, and ``\<open>that\<close>'' for @{syntax short_statement}.

  \<^descr> @{command "theorem"}, @{command "corollary"}, and @{command "proposition"}
  are the same as @{command "lemma"}. The different command names merely serve
  as a formal comment in the theory source.

  \<^descr> @{command "schematic_goal"} is similar to @{command "theorem"}, but allows
  the statement to contain unbound schematic variables.

  Under normal circumstances, an Isar proof text needs to specify claims
  explicitly. Schematic goals are more like goals in Prolog, where certain
  results are synthesized in the course of reasoning. With schematic
  statements, the inherent compositionality of Isar proofs is lost, which also
  impacts performance, because proof checking is forced into sequential mode.

  \<^descr> @{command "have"}~\<open>a: \<phi>\<close> claims a local goal, eventually resulting in a
  fact within the current logical context. This operation is completely
  independent of any pending sub-goals of an enclosing goal statements, so
  @{command "have"} may be freely used for experimental exploration of
  potential results within a proof body.

  \<^descr> @{command "show"}~\<open>a: \<phi>\<close> is like @{command "have"}~\<open>a: \<phi>\<close> plus a second
  stage to refine some pending sub-goal for each one of the finished result,
  after having been exported into the corresponding context (at the head of
  the sub-proof of this @{command "show"} command).

  To accommodate interactive debugging, resulting rules are printed before
  being applied internally. Even more, interactive execution of @{command
  "show"} predicts potential failure and displays the resulting error as a
  warning beforehand. Watch out for the following message:
  @{verbatim [display] \<open>Local statement fails to refine any pending goal\<close>}

  \<^descr> @{command "hence"} expands to ``@{command "then"}~@{command "have"}'' and
  @{command "thus"} expands to ``@{command "then"}~@{command "show"}''. These
  conflations are left-over from early history of Isar. The expanded syntax is
  more orthogonal and improves readability and maintainability of proofs.

  \<^descr> @{command "print_statement"}~\<open>a\<close> prints facts from the current theory or
  proof context in long statement form, according to the syntax for @{command
  "lemma"} given above.


  Any goal statement causes some term abbreviations (such as @{variable_ref
  "?thesis"}) to be bound automatically, see also \secref{sec:term-abbrev}.

  Structured goal statements involving @{keyword_ref "if"} or @{keyword_ref
  "when"} define the special fact @{fact_ref that} to refer to these
  assumptions in the proof body. The user may provide separate names according
  to the syntax of the statement.
\<close>


section \<open>Calculational reasoning \label{sec:calculation}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "also"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "finally"} & : & \<open>proof(state) \<rightarrow> proof(chain)\<close> \\
    @{command_def "moreover"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "ultimately"} & : & \<open>proof(state) \<rightarrow> proof(chain)\<close> \\
    @{command_def "print_trans_rules"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{attribute trans} & : & \<open>attribute\<close> \\
    @{attribute sym} & : & \<open>attribute\<close> \\
    @{attribute symmetric} & : & \<open>attribute\<close> \\
  \end{matharray}

  Calculational proof is forward reasoning with implicit application of
  transitivity rules (such those of \<open>=\<close>, \<open>\<le>\<close>, \<open><\<close>). Isabelle/Isar maintains an
  auxiliary fact register @{fact_ref calculation} for accumulating results
  obtained by transitivity composed with the current result. Command @{command
  "also"} updates @{fact calculation} involving @{fact this}, while @{command
  "finally"} exhibits the final @{fact calculation} by forward chaining
  towards the next goal statement. Both commands require valid current facts,
  i.e.\ may occur only after commands that produce theorems such as @{command
  "assume"}, @{command "note"}, or some finished proof of @{command "have"},
  @{command "show"} etc. The @{command "moreover"} and @{command "ultimately"}
  commands are similar to @{command "also"} and @{command "finally"}, but only
  collect further results in @{fact calculation} without applying any rules
  yet.

  Also note that the implicit term abbreviation ``\<open>\<dots>\<close>'' has its canonical
  application with calculational proofs. It refers to the argument of the
  preceding statement. (The argument of a curried infix expression happens to
  be its right-hand side.)

  Isabelle/Isar calculations are implicitly subject to block structure in the
  sense that new threads of calculational reasoning are commenced for any new
  block (as opened by a local goal, for example). This means that, apart from
  being able to nest calculations, there is no separate \<^emph>\<open>begin-calculation\<close>
  command required.

  \<^medskip>
  The Isar calculation proof commands may be defined as follows:\<^footnote>\<open>We suppress
  internal bookkeeping such as proper handling of block-structure.\<close>

  \begin{matharray}{rcl}
    @{command "also"}\<open>\<^sub>0\<close> & \equiv & @{command "note"}~\<open>calculation = this\<close> \\
    @{command "also"}\<open>\<^sub>n\<^sub>+\<^sub>1\<close> & \equiv & @{command "note"}~\<open>calculation = trans [OF calculation this]\<close> \\[0.5ex]
    @{command "finally"} & \equiv & @{command "also"}~@{command "from"}~\<open>calculation\<close> \\[0.5ex]
    @{command "moreover"} & \equiv & @{command "note"}~\<open>calculation = calculation this\<close> \\
    @{command "ultimately"} & \equiv & @{command "moreover"}~@{command "from"}~\<open>calculation\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{command also} | @@{command finally}) ('(' @{syntax thms} ')')?
    ;
    @@{attribute trans} (() | 'add' | 'del')
  \<close>

  \<^descr> @{command "also"}~\<open>(a\<^sub>1 \<dots> a\<^sub>n)\<close> maintains the auxiliary @{fact
  calculation} register as follows. The first occurrence of @{command "also"}
  in some calculational thread initializes @{fact calculation} by @{fact
  this}. Any subsequent @{command "also"} on the same level of block-structure
  updates @{fact calculation} by some transitivity rule applied to @{fact
  calculation} and @{fact this} (in that order). Transitivity rules are picked
  from the current context, unless alternative rules are given as explicit
  arguments.

  \<^descr> @{command "finally"}~\<open>(a\<^sub>1 \<dots> a\<^sub>n)\<close> maintains @{fact calculation} in the
  same way as @{command "also"} and then concludes the current calculational
  thread. The final result is exhibited as fact for forward chaining towards
  the next goal. Basically, @{command "finally"} abbreviates @{command
  "also"}~@{command "from"}~@{fact calculation}. Typical idioms for concluding
  calculational proofs are ``@{command "finally"}~@{command
  "show"}~\<open>?thesis\<close>~@{command "."}'' and ``@{command "finally"}~@{command
  "have"}~\<open>\<phi>\<close>~@{command "."}''.

  \<^descr> @{command "moreover"} and @{command "ultimately"} are analogous to
  @{command "also"} and @{command "finally"}, but collect results only,
  without applying rules.

  \<^descr> @{command "print_trans_rules"} prints the list of transitivity rules (for
  calculational commands @{command "also"} and @{command "finally"}) and
  symmetry rules (for the @{attribute symmetric} operation and single step
  elimination patters) of the current context.

  \<^descr> @{attribute trans} declares theorems as transitivity rules.

  \<^descr> @{attribute sym} declares symmetry rules, as well as @{attribute
  "Pure.elim"}\<open>?\<close> rules.

  \<^descr> @{attribute symmetric} resolves a theorem with some rule declared as
  @{attribute sym} in the current context. For example, ``@{command
  "assume"}~\<open>[symmetric]: x = y\<close>'' produces a swapped fact derived from that
  assumption.

  In structured proof texts it is often more appropriate to use an explicit
  single-step elimination proof, such as ``@{command "assume"}~\<open>x =
  y\<close>~@{command "then"}~@{command "have"}~\<open>y = x\<close>~@{command ".."}''.
\<close>


section \<open>Refinement steps\<close>

subsection \<open>Proof method expressions \label{sec:proof-meth}\<close>

text \<open>
  Proof methods are either basic ones, or expressions composed of methods via
  ``\<^verbatim>\<open>,\<close>'' (sequential composition), ``\<^verbatim>\<open>;\<close>'' (structural composition),
  ``\<^verbatim>\<open>|\<close>'' (alternative choices), ``\<^verbatim>\<open>?\<close>'' (try), ``\<^verbatim>\<open>+\<close>'' (repeat at least
  once), ``\<^verbatim>\<open>[\<close>\<open>n\<close>\<^verbatim>\<open>]\<close>'' (restriction to first \<open>n\<close> subgoals). In practice,
  proof methods are usually just a comma separated list of @{syntax
  name}~@{syntax args} specifications. Note that parentheses may be dropped
  for single method specifications (with no arguments). The syntactic
  precedence of method combinators is \<^verbatim>\<open>|\<close> \<^verbatim>\<open>;\<close> \<^verbatim>\<open>,\<close> \<^verbatim>\<open>[]\<close> \<^verbatim>\<open>+\<close> \<^verbatim>\<open>?\<close> (from low
  to high).

  \<^rail>\<open>
    @{syntax_def method}:
      (@{syntax name} | '(' methods ')') (() | '?' | '+' | '[' @{syntax nat}? ']')
    ;
    methods: (@{syntax name} @{syntax args} | @{syntax method}) + (',' | ';' | '|')
  \<close>

  Regular Isar proof methods do \<^emph>\<open>not\<close> admit direct goal addressing, but refer
  to the first subgoal or to all subgoals uniformly. Nonetheless, the
  subsequent mechanisms allow to imitate the effect of subgoal addressing that
  is known from ML tactics.

  \<^medskip>
  Goal \<^emph>\<open>restriction\<close> means the proof state is wrapped-up in a way that
  certain subgoals are exposed, and other subgoals are ``parked'' elsewhere.
  Thus a proof method has no other chance than to operate on the subgoals that
  are presently exposed.

  Structural composition ``\<open>m\<^sub>1\<close>\<^verbatim>\<open>;\<close>~\<open>m\<^sub>2\<close>'' means that method \<open>m\<^sub>1\<close> is
  applied with restriction to the first subgoal, then \<open>m\<^sub>2\<close> is applied
  consecutively with restriction to each subgoal that has newly emerged due to
  \<open>m\<^sub>1\<close>. This is analogous to the tactic combinator \<^ML_infix>\<open>THEN_ALL_NEW\<close> in
  Isabelle/ML, see also @{cite "isabelle-implementation"}. For example, \<open>(rule
  r; blast)\<close> applies rule \<open>r\<close> and then solves all new subgoals by \<open>blast\<close>.

  Moreover, the explicit goal restriction operator ``\<open>[n]\<close>'' exposes only the
  first \<open>n\<close> subgoals (which need to exist), with default \<open>n = 1\<close>. For example,
  the method expression ``\<open>simp_all[3]\<close>'' simplifies the first three subgoals,
  while ``\<open>(rule r, simp_all)[]\<close>'' simplifies all new goals that emerge from
  applying rule \<open>r\<close> to the originally first one.

  \<^medskip>
  Improper methods, notably tactic emulations, offer low-level goal addressing
  as explicit argument to the individual tactic being involved. Here ``\<open>[!]\<close>''
  refers to all goals, and ``\<open>[n-]\<close>'' to all goals starting from \<open>n\<close>.

  \<^rail>\<open>
    @{syntax_def goal_spec}:
      '[' (@{syntax nat} '-' @{syntax nat} | @{syntax nat} '-' | @{syntax nat} | '!' ) ']'
  \<close>
\<close>


subsection \<open>Initial and terminal proof steps \label{sec:proof-steps}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "proof"} & : & \<open>proof(prove) \<rightarrow> proof(state)\<close> \\
    @{command_def "qed"} & : & \<open>proof(state) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{command_def "by"} & : & \<open>proof(prove) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{command_def ".."} & : & \<open>proof(prove) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{command_def "."} & : & \<open>proof(prove) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{command_def "sorry"} & : & \<open>proof(prove) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{method_def standard} & : & \<open>method\<close> \\
  \end{matharray}

  Arbitrary goal refinement via tactics is considered harmful. Structured
  proof composition in Isar admits proof methods to be invoked in two places
  only.

    \<^enum> An \<^emph>\<open>initial\<close> refinement step @{command_ref "proof"}~\<open>m\<^sub>1\<close> reduces a
    newly stated goal to a number of sub-goals that are to be solved later.
    Facts are passed to \<open>m\<^sub>1\<close> for forward chaining, if so indicated by
    \<open>proof(chain)\<close> mode.

    \<^enum> A \<^emph>\<open>terminal\<close> conclusion step @{command_ref "qed"}~\<open>m\<^sub>2\<close> is intended to
    solve remaining goals. No facts are passed to \<open>m\<^sub>2\<close>.

  The only other (proper) way to affect pending goals in a proof body is by
  @{command_ref "show"}, which involves an explicit statement of what is to be
  solved eventually. Thus we avoid the fundamental problem of unstructured
  tactic scripts that consist of numerous consecutive goal transformations,
  with invisible effects.

  \<^medskip>
  As a general rule of thumb for good proof style, initial proof methods
  should either solve the goal completely, or constitute some well-understood
  reduction to new sub-goals. Arbitrary automatic proof tools that are prone
  leave a large number of badly structured sub-goals are no help in continuing
  the proof document in an intelligible manner.

  Unless given explicitly by the user, the default initial method is @{method
  standard}, which subsumes at least @{method_ref (Pure) rule} or its
  classical variant @{method_ref (HOL) rule}. These methods apply a single
  standard elimination or introduction rule according to the topmost logical
  connective involved. There is no separate default terminal method. Any
  remaining goals are always solved by assumption in the very last step.

  \<^rail>\<open>
    @@{command proof} method?
    ;
    @@{command qed} method?
    ;
    @@{command "by"} method method?
    ;
    (@@{command "."} | @@{command ".."} | @@{command sorry})
  \<close>

  \<^descr> @{command "proof"}~\<open>m\<^sub>1\<close> refines the goal by proof method \<open>m\<^sub>1\<close>; facts for
  forward chaining are passed if so indicated by \<open>proof(chain)\<close> mode.

  \<^descr> @{command "qed"}~\<open>m\<^sub>2\<close> refines any remaining goals by proof method \<open>m\<^sub>2\<close>
  and concludes the sub-proof by assumption. If the goal had been \<open>show\<close>, some
  pending sub-goal is solved as well by the rule resulting from the result
  \<^emph>\<open>exported\<close> into the enclosing goal context. Thus \<open>qed\<close> may fail for two
  reasons: either \<open>m\<^sub>2\<close> fails, or the resulting rule does not fit to any
  pending goal\<^footnote>\<open>This includes any additional ``strong'' assumptions as
  introduced by @{command "assume"}.\<close> of the enclosing context. Debugging such
  a situation might involve temporarily changing @{command "show"} into
  @{command "have"}, or weakening the local context by replacing occurrences
  of @{command "assume"} by @{command "presume"}.

  \<^descr> @{command "by"}~\<open>m\<^sub>1 m\<^sub>2\<close> is a \<^emph>\<open>terminal proof\<close>\index{proof!terminal}; it
  abbreviates @{command "proof"}~\<open>m\<^sub>1\<close>~@{command "qed"}~\<open>m\<^sub>2\<close>, but with
  backtracking across both methods. Debugging an unsuccessful @{command
  "by"}~\<open>m\<^sub>1 m\<^sub>2\<close> command can be done by expanding its definition; in many
  cases @{command "proof"}~\<open>m\<^sub>1\<close> (or even \<open>apply\<close>~\<open>m\<^sub>1\<close>) is already sufficient
  to see the problem.

  \<^descr> ``@{command ".."}'' is a \<^emph>\<open>standard proof\<close>\index{proof!standard}; it
  abbreviates @{command "by"}~\<open>standard\<close>.

  \<^descr> ``@{command "."}'' is a \<^emph>\<open>trivial proof\<close>\index{proof!trivial}; it
  abbreviates @{command "by"}~\<open>this\<close>.

  \<^descr> @{command "sorry"} is a \<^emph>\<open>fake proof\<close>\index{proof!fake} pretending to
  solve the pending claim without further ado. This only works in interactive
  development, or if the @{attribute quick_and_dirty} is enabled. Facts
  emerging from fake proofs are not the real thing. Internally, the derivation
  object is tainted by an oracle invocation, which may be inspected via the
  command @{command "thm_oracles"} (\secref{sec:oracles}).

  The most important application of @{command "sorry"} is to support
  experimentation and top-down proof development.

  \<^descr> @{method standard} refers to the default refinement step of some Isar
  language elements (notably @{command proof} and ``@{command ".."}''). It is
  \<^emph>\<open>dynamically scoped\<close>, so the behaviour depends on the application
  environment.

  In Isabelle/Pure, @{method standard} performs elementary introduction~/
  elimination steps (@{method_ref (Pure) rule}), introduction of type classes
  (@{method_ref intro_classes}) and locales (@{method_ref intro_locales}).

  In Isabelle/HOL, @{method standard} also takes classical rules into account
  (cf.\ \secref{sec:classical}).
\<close>


subsection \<open>Fundamental methods and attributes \label{sec:pure-meth-att}\<close>

text \<open>
  The following proof methods and attributes refer to basic logical operations
  of Isar. Further methods and attributes are provided by several generic and
  object-logic specific tools and packages (see \chref{ch:gen-tools} and
  \partref{part:hol}).

  \begin{matharray}{rcl}
    @{command_def "print_rules"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\[0.5ex]
    @{method_def "-"} & : & \<open>method\<close> \\
    @{method_def "goal_cases"} & : & \<open>method\<close> \\
    @{method_def "subproofs"} & : & \<open>method\<close> \\
    @{method_def "fact"} & : & \<open>method\<close> \\
    @{method_def "assumption"} & : & \<open>method\<close> \\
    @{method_def "this"} & : & \<open>method\<close> \\
    @{method_def (Pure) "rule"} & : & \<open>method\<close> \\
    @{attribute_def (Pure) "intro"} & : & \<open>attribute\<close> \\
    @{attribute_def (Pure) "elim"} & : & \<open>attribute\<close> \\
    @{attribute_def (Pure) "dest"} & : & \<open>attribute\<close> \\
    @{attribute_def (Pure) "rule"} & : & \<open>attribute\<close> \\[0.5ex]
    @{attribute_def "OF"} & : & \<open>attribute\<close> \\
    @{attribute_def "of"} & : & \<open>attribute\<close> \\
    @{attribute_def "where"} & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{method goal_cases} (@{syntax name}*)
    ;
    @@{method subproofs} @{syntax method}
    ;
    @@{method fact} @{syntax thms}?
    ;
    @@{method (Pure) rule} @{syntax thms}?
    ;
    rulemod: ('intro' | 'elim' | 'dest')
      ((('!' | () | '?') @{syntax nat}?) | 'del') ':' @{syntax thms}
    ;
    (@@{attribute intro} | @@{attribute elim} | @@{attribute dest})
      ('!' | () | '?') @{syntax nat}?
    ;
    @@{attribute (Pure) rule} 'del'
    ;
    @@{attribute OF} @{syntax thms}
    ;
    @@{attribute of} @{syntax insts} ('concl' ':' @{syntax insts})? @{syntax for_fixes}
    ;
    @@{attribute "where"} @{syntax named_insts} @{syntax for_fixes}
  \<close>

  \<^descr> @{command "print_rules"} prints rules declared via attributes @{attribute
  (Pure) intro}, @{attribute (Pure) elim}, @{attribute (Pure) dest} of
  Isabelle/Pure.

  See also the analogous @{command "print_claset"} command for similar rule
  declarations of the classical reasoner (\secref{sec:classical}).

  \<^descr> ``@{method "-"}'' (minus) inserts the forward chaining facts as premises
  into the goal, and nothing else.

  Note that command @{command_ref "proof"} without any method actually
  performs a single reduction step using the @{method_ref (Pure) rule} method;
  thus a plain \<^emph>\<open>do-nothing\<close> proof step would be ``@{command "proof"}~\<open>-\<close>''
  rather than @{command "proof"} alone.

  \<^descr> @{method "goal_cases"}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> turns the current subgoals into cases
  within the context (see also \secref{sec:cases-induct}). The specified case
  names are used if present; otherwise cases are numbered starting from 1.

  Invoking cases in the subsequent proof body via the @{command_ref case}
  command will @{command fix} goal parameters, @{command assume} goal
  premises, and @{command let} variable @{variable_ref ?case} refer to the
  conclusion.

  \<^descr> @{method "subproofs"}~\<open>m\<close> applies the method expression \<open>m\<close> consecutively
  to each subgoal, constructing individual subproofs internally (analogous to
  ``\<^theory_text>\<open>show goal by m\<close>'' for each subgoal of the proof state). Search
  alternatives of \<open>m\<close> are truncated: the method is forced to be deterministic.
  This method combinator impacts the internal construction of proof terms: it
  makes a cascade of let-expressions within the derivation tree and may thus
  improve scalability.

  \<^descr> @{method "fact"}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> composes some fact from \<open>a\<^sub>1, \<dots>, a\<^sub>n\<close> (or
  implicitly from the current proof context) modulo unification of schematic
  type and term variables. The rule structure is not taken into account, i.e.\
  meta-level implication is considered atomic. This is the same principle
  underlying literal facts (cf.\ \secref{sec:syn-att}): ``@{command
  "have"}~\<open>\<phi>\<close>~@{command "by"}~\<open>fact\<close>'' is equivalent to ``@{command
  "note"}~\<^verbatim>\<open>`\<close>\<open>\<phi>\<close>\<^verbatim>\<open>`\<close>'' provided that \<open>\<turnstile> \<phi>\<close> is an instance of some known \<open>\<turnstile> \<phi>\<close>
  in the proof context.

  \<^descr> @{method assumption} solves some goal by a single assumption step. All
  given facts are guaranteed to participate in the refinement; this means
  there may be only 0 or 1 in the first place. Recall that @{command "qed"}
  (\secref{sec:proof-steps}) already concludes any remaining sub-goals by
  assumption, so structured proofs usually need not quote the @{method
  assumption} method at all.

  \<^descr> @{method this} applies all of the current facts directly as rules. Recall
  that ``@{command "."}'' (dot) abbreviates ``@{command "by"}~\<open>this\<close>''.

  \<^descr> @{method (Pure) rule}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> applies some rule given as argument in
  backward manner; facts are used to reduce the rule before applying it to the
  goal. Thus @{method (Pure) rule} without facts is plain introduction, while
  with facts it becomes elimination.

  When no arguments are given, the @{method (Pure) rule} method tries to pick
  appropriate rules automatically, as declared in the current context using
  the @{attribute (Pure) intro}, @{attribute (Pure) elim}, @{attribute (Pure)
  dest} attributes (see below). This is included in the standard behaviour of
  @{command "proof"} and ``@{command ".."}'' (double-dot) steps (see
  \secref{sec:proof-steps}).

  \<^descr> @{attribute (Pure) intro}, @{attribute (Pure) elim}, and @{attribute
  (Pure) dest} declare introduction, elimination, and destruct rules, to be
  used with method @{method (Pure) rule}, and similar tools. Note that the
  latter will ignore rules declared with ``\<open>?\<close>'', while ``\<open>!\<close>'' are used most
  aggressively.

  The classical reasoner (see \secref{sec:classical}) introduces its own
  variants of these attributes; use qualified names to access the present
  versions of Isabelle/Pure, i.e.\ @{attribute (Pure) "Pure.intro"}.

  \<^descr> @{attribute (Pure) rule}~\<open>del\<close> undeclares introduction, elimination, or
  destruct rules.

  \<^descr> @{attribute OF}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> applies some theorem to all of the given rules
  \<open>a\<^sub>1, \<dots>, a\<^sub>n\<close> in canonical right-to-left order, which means that premises
  stemming from the \<open>a\<^sub>i\<close> emerge in parallel in the result, without
  interfering with each other. In many practical situations, the \<open>a\<^sub>i\<close> do not
  have premises themselves, so \<open>rule [OF a\<^sub>1 \<dots> a\<^sub>n]\<close> can be actually read as
  functional application (modulo unification).

  Argument positions may be effectively skipped by using ``\<open>_\<close>'' (underscore),
  which refers to the propositional identity rule in the Pure theory.

  \<^descr> @{attribute of}~\<open>t\<^sub>1 \<dots> t\<^sub>n\<close> performs positional instantiation of term
  variables. The terms \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close> are substituted for any schematic
  variables occurring in a theorem from left to right; ``\<open>_\<close>'' (underscore)
  indicates to skip a position. Arguments following a ``\<open>concl:\<close>''
  specification refer to positions of the conclusion of a rule.

  An optional context of local variables \<open>\<FOR> x\<^sub>1 \<dots> x\<^sub>m\<close> may be specified:
  the instantiated theorem is exported, and these variables become schematic
  (usually with some shifting of indices).

  \<^descr> @{attribute "where"}~\<open>x\<^sub>1 = t\<^sub>1 \<AND> \<dots> x\<^sub>n = t\<^sub>n\<close> performs named
  instantiation of schematic type and term variables occurring in a theorem.
  Schematic variables have to be specified on the left-hand side (e.g.\
  \<open>?x1.3\<close>). The question mark may be omitted if the variable name is a plain
  identifier without index. As type instantiations are inferred from term
  instantiations, explicit type instantiations are seldom necessary.

  An optional context of local variables \<open>\<FOR> x\<^sub>1 \<dots> x\<^sub>m\<close> may be specified
  as for @{attribute "of"} above.
\<close>


subsection \<open>Defining proof methods\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "method_setup"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command method_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
  \<close>

  \<^descr> @{command "method_setup"}~\<open>name = text description\<close> defines a proof method
  in the current context. The given \<open>text\<close> has to be an ML expression of type
  \<^ML_type>\<open>(Proof.context -> Proof.method) context_parser\<close>, cf.\ basic
  parsers defined in structure \<^ML_structure>\<open>Args\<close> and \<^ML_structure>\<open>Attrib\<close>. There are also combinators like \<^ML>\<open>METHOD\<close> and \<^ML>\<open>SIMPLE_METHOD\<close> to turn certain tactic forms into official proof methods; the
  primed versions refer to tactics with explicit goal addressing.

  Here are some example method definitions:
\<close>

(*<*)experiment begin(*>*)
  method_setup my_method1 =
    \<open>Scan.succeed (K (SIMPLE_METHOD' (fn i: int => no_tac)))\<close>
    "my first method (without any arguments)"

  method_setup my_method2 =
    \<open>Scan.succeed (fn ctxt: Proof.context =>
      SIMPLE_METHOD' (fn i: int => no_tac))\<close>
    "my second method (with context)"

  method_setup my_method3 =
    \<open>Attrib.thms >> (fn thms: thm list => fn ctxt: Proof.context =>
      SIMPLE_METHOD' (fn i: int => no_tac))\<close>
    "my third method (with theorem arguments and context)"
(*<*)end(*>*)


section \<open>Proof by cases and induction \label{sec:cases-induct}\<close>

subsection \<open>Rule contexts\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "case"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "print_cases"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{attribute_def case_names} & : & \<open>attribute\<close> \\
    @{attribute_def case_conclusion} & : & \<open>attribute\<close> \\
    @{attribute_def params} & : & \<open>attribute\<close> \\
    @{attribute_def consumes} & : & \<open>attribute\<close> \\
  \end{matharray}

  The puristic way to build up Isar proof contexts is by explicit language
  elements like @{command "fix"}, @{command "assume"}, @{command "let"} (see
  \secref{sec:proof-context}). This is adequate for plain natural deduction,
  but easily becomes unwieldy in concrete verification tasks, which typically
  involve big induction rules with several cases.

  The @{command "case"} command provides a shorthand to refer to a local
  context symbolically: certain proof methods provide an environment of named
  ``cases'' of the form \<open>c: x\<^sub>1, \<dots>, x\<^sub>m, \<phi>\<^sub>1, \<dots>, \<phi>\<^sub>n\<close>; the effect of
  ``@{command "case"}~\<open>c\<close>'' is then equivalent to ``@{command "fix"}~\<open>x\<^sub>1 \<dots>
  x\<^sub>m\<close>~@{command "assume"}~\<open>c: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close>''. Term bindings may be covered as
  well, notably @{variable ?case} for the main conclusion.

  By default, the ``terminology'' \<open>x\<^sub>1, \<dots>, x\<^sub>m\<close> of a case value is marked as
  hidden, i.e.\ there is no way to refer to such parameters in the subsequent
  proof text. After all, original rule parameters stem from somewhere outside
  of the current proof text. By using the explicit form ``@{command
  "case"}~\<open>(c y\<^sub>1 \<dots> y\<^sub>m)\<close>'' instead, the proof author is able to chose local
  names that fit nicely into the current context.

  \<^medskip>
  It is important to note that proper use of @{command "case"} does not
  provide means to peek at the current goal state, which is not directly
  observable in Isar! Nonetheless, goal refinement commands do provide named
  cases \<open>goal\<^sub>i\<close> for each subgoal \<open>i = 1, \<dots>, n\<close> of the resulting goal state.
  Using this extra feature requires great care, because some bits of the
  internal tactical machinery intrude the proof text. In particular, parameter
  names stemming from the left-over of automated reasoning tools are usually
  quite unpredictable.

  Under normal circumstances, the text of cases emerge from standard
  elimination or induction rules, which in turn are derived from previous
  theory specifications in a canonical way (say from @{command "inductive"}
  definitions).

  \<^medskip>
  Proper cases are only available if both the proof method and the rules
  involved support this. By using appropriate attributes, case names,
  conclusions, and parameters may be also declared by hand. Thus variant
  versions of rules that have been derived manually become ready to use in
  advanced case analysis later.

  \<^rail>\<open>
    @@{command case} @{syntax thmdecl}? (name | '(' name (('_' | @{syntax name}) *) ')')
    ;
    @@{attribute case_names} ((@{syntax name} ( '[' (('_' | @{syntax name}) *) ']' ) ? ) +)
    ;
    @@{attribute case_conclusion} @{syntax name} (@{syntax name} * )
    ;
    @@{attribute params} ((@{syntax name} * ) + @'and')
    ;
    @@{attribute consumes} @{syntax int}?
  \<close>

  \<^descr> @{command "case"}~\<open>a: (c x\<^sub>1 \<dots> x\<^sub>m)\<close> invokes a named local context \<open>c:
  x\<^sub>1, \<dots>, x\<^sub>m, \<phi>\<^sub>1, \<dots>, \<phi>\<^sub>m\<close>, as provided by an appropriate proof method (such
  as @{method_ref cases} and @{method_ref induct}). The command ``@{command
  "case"}~\<open>a: (c x\<^sub>1 \<dots> x\<^sub>m)\<close>'' abbreviates ``@{command "fix"}~\<open>x\<^sub>1 \<dots>
  x\<^sub>m\<close>~@{command "assume"}~\<open>a.c: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close>''. Each local fact is qualified by
  the prefix \<open>a\<close>, and all such facts are collectively bound to the name \<open>a\<close>.

  The fact name is specification \<open>a\<close> is optional, the default is to re-use
  \<open>c\<close>. So @{command "case"}~\<open>(c x\<^sub>1 \<dots> x\<^sub>m)\<close> is the same as @{command
  "case"}~\<open>c: (c x\<^sub>1 \<dots> x\<^sub>m)\<close>.

  \<^descr> @{command "print_cases"} prints all local contexts of the current state,
  using Isar proof language notation.

  \<^descr> @{attribute case_names}~\<open>c\<^sub>1 \<dots> c\<^sub>k\<close> declares names for the local contexts
  of premises of a theorem; \<open>c\<^sub>1, \<dots>, c\<^sub>k\<close> refers to the \<^emph>\<open>prefix\<close> of the list
  of premises. Each of the cases \<open>c\<^sub>i\<close> can be of the form \<open>c[h\<^sub>1 \<dots> h\<^sub>n]\<close> where
  the \<open>h\<^sub>1 \<dots> h\<^sub>n\<close> are the names of the hypotheses in case \<open>c\<^sub>i\<close> from left to
  right.

  \<^descr> @{attribute case_conclusion}~\<open>c d\<^sub>1 \<dots> d\<^sub>k\<close> declares names for the
  conclusions of a named premise \<open>c\<close>; here \<open>d\<^sub>1, \<dots>, d\<^sub>k\<close> refers to the prefix
  of arguments of a logical formula built by nesting a binary connective
  (e.g.\ \<open>\<or>\<close>).

  Note that proof methods such as @{method induct} and @{method coinduct}
  already provide a default name for the conclusion as a whole. The need to
  name subformulas only arises with cases that split into several sub-cases,
  as in common co-induction rules.

  \<^descr> @{attribute params}~\<open>p\<^sub>1 \<dots> p\<^sub>m \<AND> \<dots> q\<^sub>1 \<dots> q\<^sub>n\<close> renames the innermost
  parameters of premises \<open>1, \<dots>, n\<close> of some theorem. An empty list of names may
  be given to skip positions, leaving the present parameters unchanged.

  Note that the default usage of case rules does \<^emph>\<open>not\<close> directly expose
  parameters to the proof context.

  \<^descr> @{attribute consumes}~\<open>n\<close> declares the number of ``major premises'' of a
  rule, i.e.\ the number of facts to be consumed when it is applied by an
  appropriate proof method. The default value of @{attribute consumes} is \<open>n =
  1\<close>, which is appropriate for the usual kind of cases and induction rules for
  inductive sets (cf.\ \secref{sec:hol-inductive}). Rules without any
  @{attribute consumes} declaration given are treated as if @{attribute
  consumes}~\<open>0\<close> had been specified.

  A negative \<open>n\<close> is interpreted relatively to the total number of premises of
  the rule in the target context. Thus its absolute value specifies the
  remaining number of premises, after subtracting the prefix of major premises
  as indicated above. This form of declaration has the technical advantage of
  being stable under more morphisms, notably those that export the result from
  a nested @{command_ref context} with additional assumptions.

  Note that explicit @{attribute consumes} declarations are only rarely
  needed; this is already taken care of automatically by the higher-level
  @{attribute cases}, @{attribute induct}, and @{attribute coinduct}
  declarations.
\<close>


subsection \<open>Proof methods\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def cases} & : & \<open>method\<close> \\
    @{method_def induct} & : & \<open>method\<close> \\
    @{method_def induction} & : & \<open>method\<close> \\
    @{method_def coinduct} & : & \<open>method\<close> \\
  \end{matharray}

  The @{method cases}, @{method induct}, @{method induction}, and @{method
  coinduct} methods provide a uniform interface to common proof techniques
  over datatypes, inductive predicates (or sets), recursive functions etc. The
  corresponding rules may be specified and instantiated in a casual manner.
  Furthermore, these methods provide named local contexts that may be invoked
  via the @{command "case"} proof command within the subsequent proof text.
  This accommodates compact proof texts even when reasoning about large
  specifications.

  The @{method induct} method also provides some infrastructure to work with
  structured statements (either using explicit meta-level connectives, or
  including facts and parameters separately). This avoids cumbersome encoding
  of ``strengthened'' inductive statements within the object-logic.

  Method @{method induction} differs from @{method induct} only in the names
  of the facts in the local context invoked by the @{command "case"} command.

  \<^rail>\<open>
    @@{method cases} ('(' 'no_simp' ')')? \<newline>
      (@{syntax insts} * @'and') rule?
    ;
    (@@{method induct} | @@{method induction})
      ('(' 'no_simp' ')')? (definsts * @'and') \<newline> arbitrary? taking? rule?
    ;
    @@{method coinduct} @{syntax insts} taking rule?
    ;

    rule: ('type' | 'pred' | 'set') ':' (@{syntax name} +) | 'rule' ':' (@{syntax thm} +)
    ;
    definst: @{syntax name} ('==' | '\<equiv>') @{syntax term} | '(' @{syntax term} ')' | @{syntax inst}
    ;
    definsts: ( definst * )
    ;
    arbitrary: 'arbitrary' ':' ((@{syntax term} * ) @'and' +)
    ;
    taking: 'taking' ':' @{syntax insts}
  \<close>

  \<^descr> @{method cases}~\<open>insts R\<close> applies method @{method rule} with an
  appropriate case distinction theorem, instantiated to the subjects \<open>insts\<close>.
  Symbolic case names are bound according to the rule's local contexts.

  The rule is determined as follows, according to the facts and arguments
  passed to the @{method cases} method:

  \<^medskip>
  \begin{tabular}{llll}
    facts           &                 & arguments   & rule \\\hline
    \<open>\<turnstile> R\<close>   & @{method cases} &             & implicit rule \<open>R\<close> \\
                    & @{method cases} &             & classical case split \\
                    & @{method cases} & \<open>t\<close>   & datatype exhaustion (type of \<open>t\<close>) \\
    \<open>\<turnstile> A t\<close> & @{method cases} & \<open>\<dots>\<close> & inductive predicate/set elimination (of \<open>A\<close>) \\
    \<open>\<dots>\<close>     & @{method cases} & \<open>\<dots> rule: R\<close> & explicit rule \<open>R\<close> \\
  \end{tabular}
  \<^medskip>

  Several instantiations may be given, referring to the \<^emph>\<open>suffix\<close> of premises
  of the case rule; within each premise, the \<^emph>\<open>prefix\<close> of variables is
  instantiated. In most situations, only a single term needs to be specified;
  this refers to the first variable of the last premise (it is usually the
  same for all cases). The \<open>(no_simp)\<close> option can be used to disable
  pre-simplification of cases (see the description of @{method induct} below
  for details).

  \<^descr> @{method induct}~\<open>insts R\<close> and @{method induction}~\<open>insts R\<close> are analogous
  to the @{method cases} method, but refer to induction rules, which are
  determined as follows:

  \<^medskip>
  \begin{tabular}{llll}
    facts   &                  & arguments     & rule \\\hline
            & @{method induct} & \<open>P x\<close>         & datatype induction (type of \<open>x\<close>) \\
    \<open>\<turnstile> A x\<close> & @{method induct} & \<open>\<dots>\<close>          & predicate/set induction (of \<open>A\<close>) \\
    \<open>\<dots>\<close>    & @{method induct} & \<open>\<dots> rule: R\<close>  & explicit rule \<open>R\<close> \\
  \end{tabular}
  \<^medskip>

  Several instantiations may be given, each referring to some part of a mutual
  inductive definition or datatype --- only related partial induction rules
  may be used together, though. Any of the lists of terms \<open>P, x, \<dots>\<close> refers to
  the \<^emph>\<open>suffix\<close> of variables present in the induction rule. This enables the
  writer to specify only induction variables, or both predicates and
  variables, for example.

  Instantiations may be definitional: equations \<open>x \<equiv> t\<close> introduce local
  definitions, which are inserted into the claim and discharged after applying
  the induction rule. Equalities reappear in the inductive cases, but have
  been transformed according to the induction principle being involved here.
  In order to achieve practically useful induction hypotheses, some variables
  occurring in \<open>t\<close> need to generalized (see below). Instantiations of
  the form \<open>t\<close>, where \<open>t\<close> is not a variable, are taken as a shorthand for \<open>x \<equiv>
  t\<close>, where \<open>x\<close> is a fresh variable. If this is not intended, \<open>t\<close> has to be
  enclosed in parentheses. By default, the equalities generated by
  definitional instantiations are pre-simplified using a specific set of
  rules, usually consisting of distinctness and injectivity theorems for
  datatypes. This pre-simplification may cause some of the parameters of an
  inductive case to disappear, or may even completely delete some of the
  inductive cases, if one of the equalities occurring in their premises can be
  simplified to \<open>False\<close>. The \<open>(no_simp)\<close> option can be used to disable
  pre-simplification. Additional rules to be used in pre-simplification can be
  declared using the @{attribute_def induct_simp} attribute.

  The optional ``\<open>arbitrary: x\<^sub>1 \<dots> x\<^sub>m\<close>'' specification generalizes variables
  \<open>x\<^sub>1, \<dots>, x\<^sub>m\<close> of the original goal before applying induction. It is possible
  to separate variables by ``\<open>and\<close>'' to generalize in goals other than
  the first. Thus induction hypotheses may become sufficiently general to get
  the proof through. Together with definitional instantiations, one may
  effectively perform induction over expressions of a certain structure.

  The optional ``\<open>taking: t\<^sub>1 \<dots> t\<^sub>n\<close>'' specification provides additional
  instantiations of a prefix of pending variables in the rule. Such schematic
  induction rules rarely occur in practice, though.

  \<^descr> @{method coinduct}~\<open>inst R\<close> is analogous to the @{method induct} method,
  but refers to coinduction rules, which are determined as follows:

  \<^medskip>
  \begin{tabular}{llll}
    goal  &                    & arguments & rule \\\hline
          & @{method coinduct} & \<open>x\<close> & type coinduction (type of \<open>x\<close>) \\
    \<open>A x\<close> & @{method coinduct} & \<open>\<dots>\<close> & predicate/set coinduction (of \<open>A\<close>) \\
    \<open>\<dots>\<close>   & @{method coinduct} & \<open>\<dots> rule: R\<close> & explicit rule \<open>R\<close> \\
  \end{tabular}
  \<^medskip>

  Coinduction is the dual of induction. Induction essentially eliminates \<open>A x\<close>
  towards a generic result \<open>P x\<close>, while coinduction introduces \<open>A x\<close> starting
  with \<open>B x\<close>, for a suitable ``bisimulation'' \<open>B\<close>. The cases of a coinduct
  rule are typically named after the predicates or sets being covered, while
  the conclusions consist of several alternatives being named after the
  individual destructor patterns.

  The given instantiation refers to the \<^emph>\<open>suffix\<close> of variables occurring in
  the rule's major premise, or conclusion if unavailable. An additional
  ``\<open>taking: t\<^sub>1 \<dots> t\<^sub>n\<close>'' specification may be required in order to specify
  the bisimulation to be used in the coinduction step.


  Above methods produce named local contexts, as determined by the
  instantiated rule as given in the text. Beyond that, the @{method induct}
  and @{method coinduct} methods guess further instantiations from the goal
  specification itself. Any persisting unresolved schematic variables of the
  resulting rule will render the the corresponding case invalid. The term
  binding @{variable ?case} for the conclusion will be provided with each
  case, provided that term is fully specified.

  The @{command "print_cases"} command prints all named cases present in the
  current proof state.

  \<^medskip>
  Despite the additional infrastructure, both @{method cases} and @{method
  coinduct} merely apply a certain rule, after instantiation, while conforming
  due to the usual way of monotonic natural deduction: the context of a
  structured statement \<open>\<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> \<dots>\<close> reappears unchanged after
  the case split.

  The @{method induct} method is fundamentally different in this respect: the
  meta-level structure is passed through the ``recursive'' course involved in
  the induction. Thus the original statement is basically replaced by separate
  copies, corresponding to the induction hypotheses and conclusion; the
  original goal context is no longer available. Thus local assumptions, fixed
  parameters and definitions effectively participate in the inductive
  rephrasing of the original statement.

  In @{method induct} proofs, local assumptions introduced by cases are split
  into two different kinds: \<open>hyps\<close> stemming from the rule and \<open>prems\<close> from the
  goal statement. This is reflected in the extracted cases accordingly, so
  invoking ``@{command "case"}~\<open>c\<close>'' will provide separate facts \<open>c.hyps\<close> and
  \<open>c.prems\<close>, as well as fact \<open>c\<close> to hold the all-inclusive list.

  In @{method induction} proofs, local assumptions introduced by cases are
  split into three different kinds: \<open>IH\<close>, the induction hypotheses, \<open>hyps\<close>,
  the remaining hypotheses stemming from the rule, and \<open>prems\<close>, the
  assumptions from the goal statement. The names are \<open>c.IH\<close>, \<open>c.hyps\<close> and
  \<open>c.prems\<close>, as above.

  \<^medskip>
  Facts presented to either method are consumed according to the number of
  ``major premises'' of the rule involved, which is usually 0 for plain cases
  and induction rules of datatypes etc.\ and 1 for rules of inductive
  predicates or sets and the like. The remaining facts are inserted into the
  goal verbatim before the actual \<open>cases\<close>, \<open>induct\<close>, or \<open>coinduct\<close> rule is
  applied.
\<close>


subsection \<open>Declaring rules\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "print_induct_rules"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{attribute_def cases} & : & \<open>attribute\<close> \\
    @{attribute_def induct} & : & \<open>attribute\<close> \\
    @{attribute_def coinduct} & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{attribute cases} spec
    ;
    @@{attribute induct} spec
    ;
    @@{attribute coinduct} spec
    ;

    spec: (('type' | 'pred' | 'set') ':' @{syntax name}) | 'del'
  \<close>

  \<^descr> @{command "print_induct_rules"} prints cases and induct rules for
  predicates (or sets) and types of the current context.

  \<^descr> @{attribute cases}, @{attribute induct}, and @{attribute coinduct} (as
  attributes) declare rules for reasoning about (co)inductive predicates (or
  sets) and types, using the corresponding methods of the same name. Certain
  definitional packages of object-logics usually declare emerging cases and
  induction rules as expected, so users rarely need to intervene.

  Rules may be deleted via the \<open>del\<close> specification, which covers all of the
  \<open>type\<close>/\<open>pred\<close>/\<open>set\<close> sub-categories simultaneously. For example, @{attribute
  cases}~\<open>del\<close> removes any @{attribute cases} rules declared for some type,
  predicate, or set.

  Manual rule declarations usually refer to the @{attribute case_names} and
  @{attribute params} attributes to adjust names of cases and parameters of a
  rule; the @{attribute consumes} declaration is taken care of automatically:
  @{attribute consumes}~\<open>0\<close> is specified for ``type'' rules and @{attribute
  consumes}~\<open>1\<close> for ``predicate'' / ``set'' rules.
\<close>


section \<open>Generalized elimination and case splitting \label{sec:obtain}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "consider"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
    @{command_def "obtain"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
  \end{matharray}

  Generalized elimination means that hypothetical parameters and premises may
  be introduced in the current context, potentially with a split into cases.
  This works by virtue of a locally proven rule that establishes the soundness
  of this temporary context extension. As representative examples, one may
  think of standard rules from Isabelle/HOL like this:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>\<exists>x. B x \<Longrightarrow> (\<And>x. B x \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \\
  \<open>A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \\
  \<open>A \<or> B \<Longrightarrow> (A \<Longrightarrow> thesis) \<Longrightarrow> (B \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \\
  \end{tabular}
  \<^medskip>

  In general, these particular rules and connectives need to get involved at
  all: this concept works directly in Isabelle/Pure via Isar commands defined
  below. In particular, the logic of elimination and case splitting is
  delegated to an Isar proof, which often involves automated tools.

  \<^rail>\<open>
    @@{command consider} @{syntax obtain_clauses}
    ;
    @@{command obtain} @{syntax par_name}? @{syntax vars} \<newline>
      @'where' concl prems @{syntax for_fixes}
    ;
    concl: (@{syntax props} + @'and')
    ;
    prems: (@'if' (@{syntax props'} + @'and'))?
  \<close>

  \<^descr> @{command consider}~\<open>(a) \<^vec>x \<WHERE> \<^vec>A \<^vec>x | (b)
  \<^vec>y \<WHERE> \<^vec>B \<^vec>y | \<dots>\<close> states a rule for case splitting
  into separate subgoals, such that each case involves new parameters and
  premises. After the proof is finished, the resulting rule may be used
  directly with the @{method cases} proof method (\secref{sec:cases-induct}),
  in order to perform actual case-splitting of the proof text via @{command
  case} and @{command next} as usual.

  Optional names in round parentheses refer to case names: in the proof of the
  rule this is a fact name, in the resulting rule it is used as annotation
  with the @{attribute_ref case_names} attribute.

  \<^medskip>
  Formally, the command @{command consider} is defined as derived Isar
  language element as follows:

  \begin{matharray}{l}
    @{command "consider"}~\<open>(a) \<^vec>x \<WHERE> \<^vec>A \<^vec>x | (b) \<^vec>y \<WHERE> \<^vec>B \<^vec>y | \<dots> \<equiv>\<close> \\[1ex]
    \quad @{command "have"}~\<open>[case_names a b \<dots>]: thesis\<close> \\
    \qquad \<open>\<IF> a [Pure.intro?]: \<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis\<close> \\
    \qquad \<open>\<AND> b [Pure.intro?]: \<And>\<^vec>y. \<^vec>B \<^vec>y \<Longrightarrow> thesis\<close> \\
    \qquad \<open>\<AND> \<dots>\<close> \\
    \qquad \<open>\<FOR> thesis\<close> \\
    \qquad @{command "apply"}~\<open>(insert a b \<dots>)\<close> \\
  \end{matharray}

  See also \secref{sec:goals} for @{keyword "obtains"} in toplevel goal
  statements, as well as @{command print_statement} to print existing rules in
  a similar format.

  \<^descr> @{command obtain}~\<open>\<^vec>x \<WHERE> \<^vec>A \<^vec>x\<close> states a
  generalized elimination rule with exactly one case. After the proof is
  finished, it is activated for the subsequent proof text: the context is
  augmented via @{command fix}~\<open>\<^vec>x\<close> @{command assume}~\<open>\<^vec>A
  \<^vec>x\<close>, with special provisions to export later results by discharging
  these assumptions again.

  Note that according to the parameter scopes within the elimination rule,
  results \<^emph>\<open>must not\<close> refer to hypothetical parameters; otherwise the export
  will fail! This restriction conforms to the usual manner of existential
  reasoning in Natural Deduction.

  \<^medskip>
  Formally, the command @{command obtain} is defined as derived Isar language
  element as follows, using an instrumented variant of @{command assume}:

  \begin{matharray}{l}
    @{command "obtain"}~\<open>\<^vec>x \<WHERE> a: \<^vec>A \<^vec>x  \<langle>proof\<rangle> \<equiv>\<close> \\[1ex]
    \quad @{command "have"}~\<open>thesis\<close> \\
    \qquad \<open>\<IF> that [Pure.intro?]: \<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis\<close> \\
    \qquad \<open>\<FOR> thesis\<close> \\
    \qquad @{command "apply"}~\<open>(insert that)\<close> \\
    \qquad \<open>\<langle>proof\<rangle>\<close> \\
    \quad @{command "fix"}~\<open>\<^vec>x\<close>~@{command "assume"}\<open>\<^sup>* a: \<^vec>A \<^vec>x\<close> \\
  \end{matharray}

  In the proof of @{command consider} and @{command obtain} the local premises
  are always bound to the fact name @{fact_ref that}, according to structured
  Isar statements involving @{keyword_ref "if"} (\secref{sec:goals}).

  Facts that are established by @{command "obtain"} cannot be polymorphic: any
  type-variables occurring here are fixed in the present context. This is a
  natural consequence of the role of @{command fix} and @{command assume} in
  this construct.
\<close>

end

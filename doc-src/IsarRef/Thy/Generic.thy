theory Generic
imports Base Main
begin

chapter {* Generic tools and packages \label{ch:gen-tools} *}

section {* Configuration options \label{sec:config} *}

text {* Isabelle/Pure maintains a record of named configuration
  options within the theory or proof context, with values of type
  @{ML_type bool}, @{ML_type int}, @{ML_type real}, or @{ML_type
  string}.  Tools may declare options in ML, and then refer to these
  values (relative to the context).  Thus global reference variables
  are easily avoided.  The user may change the value of a
  configuration option by means of an associated attribute of the same
  name.  This form of context declaration works particularly well with
  commands such as @{command "declare"} or @{command "using"} like
  this:
*}

declare [[show_main_goal = false]]

notepad
begin
  note [[show_main_goal = true]]
end

text {* For historical reasons, some tools cannot take the full proof
  context into account and merely refer to the background theory.
  This is accommodated by configuration options being declared as
  ``global'', which may not be changed within a local context.

  \begin{matharray}{rcll}
    @{command_def "print_configs"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  @{rail "
    @{syntax name} ('=' ('true' | 'false' | @{syntax int} | @{syntax float} | @{syntax name}))?
  "}

  \begin{description}
  
  \item @{command "print_configs"} prints the available configuration
  options, with names, types, and current values.
  
  \item @{text "name = value"} as an attribute expression modifies the
  named option, with the syntax of the value depending on the option's
  type.  For @{ML_type bool} the default value is @{text true}.  Any
  attempt to change a global option in a local context is ignored.

  \end{description}
*}


section {* Basic proof tools *}

subsection {* Miscellaneous methods and attributes \label{sec:misc-meth-att} *}

text {*
  \begin{matharray}{rcl}
    @{method_def unfold} & : & @{text method} \\
    @{method_def fold} & : & @{text method} \\
    @{method_def insert} & : & @{text method} \\[0.5ex]
    @{method_def erule}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def drule}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def frule}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def intro} & : & @{text method} \\
    @{method_def elim} & : & @{text method} \\
    @{method_def succeed} & : & @{text method} \\
    @{method_def fail} & : & @{text method} \\
  \end{matharray}

  @{rail "
    (@@{method fold} | @@{method unfold} | @@{method insert}) @{syntax thmrefs}
    ;
    (@@{method erule} | @@{method drule} | @@{method frule})
      ('(' @{syntax nat} ')')? @{syntax thmrefs}
    ;
    (@@{method intro} | @@{method elim}) @{syntax thmrefs}?
  "}

  \begin{description}
  
  \item @{method unfold}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} and @{method fold}~@{text
  "a\<^sub>1 \<dots> a\<^sub>n"} expand (or fold back) the given definitions throughout
  all goals; any chained facts provided are inserted into the goal and
  subject to rewriting as well.

  \item @{method insert}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} inserts theorems as facts
  into all goals of the proof state.  Note that current facts
  indicated for forward chaining are ignored.

  \item @{method erule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}, @{method
  drule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}, and @{method frule}~@{text
  "a\<^sub>1 \<dots> a\<^sub>n"} are similar to the basic @{method rule}
  method (see \secref{sec:pure-meth-att}), but apply rules by
  elim-resolution, destruct-resolution, and forward-resolution,
  respectively \cite{isabelle-implementation}.  The optional natural
  number argument (default 0) specifies additional assumption steps to
  be performed here.

  Note that these methods are improper ones, mainly serving for
  experimentation and tactic script emulation.  Different modes of
  basic rule application are usually expressed in Isar at the proof
  language level, rather than via implicit proof state manipulations.
  For example, a proper single-step elimination would be done using
  the plain @{method rule} method, with forward chaining of current
  facts.

  \item @{method intro} and @{method elim} repeatedly refine some goal
  by intro- or elim-resolution, after having inserted any chained
  facts.  Exactly the rules given as arguments are taken into account;
  this allows fine-tuned decomposition of a proof problem, in contrast
  to common automated tools.

  \item @{method succeed} yields a single (unchanged) result; it is
  the identity of the ``@{text ","}'' method combinator (cf.\
  \secref{sec:proof-meth}).

  \item @{method fail} yields an empty result sequence; it is the
  identity of the ``@{text "|"}'' method combinator (cf.\
  \secref{sec:proof-meth}).

  \end{description}

  \begin{matharray}{rcl}
    @{attribute_def tagged} & : & @{text attribute} \\
    @{attribute_def untagged} & : & @{text attribute} \\[0.5ex]
    @{attribute_def THEN} & : & @{text attribute} \\
    @{attribute_def COMP} & : & @{text attribute} \\[0.5ex]
    @{attribute_def unfolded} & : & @{text attribute} \\
    @{attribute_def folded} & : & @{text attribute} \\
    @{attribute_def abs_def} & : & @{text attribute} \\[0.5ex]
    @{attribute_def rotated} & : & @{text attribute} \\
    @{attribute_def (Pure) elim_format} & : & @{text attribute} \\
    @{attribute_def standard}@{text "\<^sup>*"} & : & @{text attribute} \\
    @{attribute_def no_vars}@{text "\<^sup>*"} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{attribute tagged} @{syntax name} @{syntax name}
    ;
    @@{attribute untagged} @{syntax name}
    ;
    (@@{attribute THEN} | @@{attribute COMP}) ('[' @{syntax nat} ']')? @{syntax thmref}
    ;
    (@@{attribute unfolded} | @@{attribute folded}) @{syntax thmrefs}
    ;
    @@{attribute rotated} @{syntax int}?
  "}

  \begin{description}

  \item @{attribute tagged}~@{text "name value"} and @{attribute
  untagged}~@{text name} add and remove \emph{tags} of some theorem.
  Tags may be any list of string pairs that serve as formal comment.
  The first string is considered the tag name, the second its value.
  Note that @{attribute untagged} removes any tags of the same name.

  \item @{attribute THEN}~@{text a} and @{attribute COMP}~@{text a}
  compose rules by resolution.  @{attribute THEN} resolves with the
  first premise of @{text a} (an alternative position may be also
  specified); the @{attribute COMP} version skips the automatic
  lifting process that is normally intended (cf.\ @{ML_op "RS"} and
  @{ML_op "COMP"} in \cite{isabelle-implementation}).
  
  \item @{attribute unfolded}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} and @{attribute
  folded}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} expand and fold back again the given
  definitions throughout a rule.

  \item @{attribute abs_def} turns an equation of the form @{prop "f x
  y \<equiv> t"} into @{prop "f \<equiv> \<lambda>x y. t"}, which ensures that @{method
  simp} or @{method unfold} steps always expand it.  This also works
  for object-logic equality.

  \item @{attribute rotated}~@{text n} rotate the premises of a
  theorem by @{text n} (default 1).

  \item @{attribute (Pure) elim_format} turns a destruction rule into
  elimination rule format, by resolving with the rule @{prop "PROP A \<Longrightarrow>
  (PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP B"}.
  
  Note that the Classical Reasoner (\secref{sec:classical}) provides
  its own version of this operation.

  \item @{attribute standard} puts a theorem into the standard form of
  object-rules at the outermost theory level.  Note that this
  operation violates the local proof context (including active
  locales).

  \item @{attribute no_vars} replaces schematic variables by free
  ones; this is mainly for tuning output of pretty printed theorems.

  \end{description}
*}


subsection {* Low-level equational reasoning *}

text {*
  \begin{matharray}{rcl}
    @{method_def subst} & : & @{text method} \\
    @{method_def hypsubst} & : & @{text method} \\
    @{method_def split} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method subst} ('(' 'asm' ')')? \\ ('(' (@{syntax nat}+) ')')? @{syntax thmref}
    ;
    @@{method split} @{syntax thmrefs}
  "}

  These methods provide low-level facilities for equational reasoning
  that are intended for specialized applications only.  Normally,
  single step calculations would be performed in a structured text
  (see also \secref{sec:calculation}), while the Simplifier methods
  provide the canonical way for automated normalization (see
  \secref{sec:simplifier}).

  \begin{description}

  \item @{method subst}~@{text eq} performs a single substitution step
  using rule @{text eq}, which may be either a meta or object
  equality.

  \item @{method subst}~@{text "(asm) eq"} substitutes in an
  assumption.

  \item @{method subst}~@{text "(i \<dots> j) eq"} performs several
  substitutions in the conclusion. The numbers @{text i} to @{text j}
  indicate the positions to substitute at.  Positions are ordered from
  the top of the term tree moving down from left to right. For
  example, in @{text "(a + b) + (c + d)"} there are three positions
  where commutativity of @{text "+"} is applicable: 1 refers to @{text
  "a + b"}, 2 to the whole term, and 3 to @{text "c + d"}.

  If the positions in the list @{text "(i \<dots> j)"} are non-overlapping
  (e.g.\ @{text "(2 3)"} in @{text "(a + b) + (c + d)"}) you may
  assume all substitutions are performed simultaneously.  Otherwise
  the behaviour of @{text subst} is not specified.

  \item @{method subst}~@{text "(asm) (i \<dots> j) eq"} performs the
  substitutions in the assumptions. The positions refer to the
  assumptions in order from left to right.  For example, given in a
  goal of the form @{text "P (a + b) \<Longrightarrow> P (c + d) \<Longrightarrow> \<dots>"}, position 1 of
  commutativity of @{text "+"} is the subterm @{text "a + b"} and
  position 2 is the subterm @{text "c + d"}.

  \item @{method hypsubst} performs substitution using some
  assumption; this only works for equations of the form @{text "x =
  t"} where @{text x} is a free or bound variable.

  \item @{method split}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} performs single-step case
  splitting using the given rules.  Splitting is performed in the
  conclusion or some assumption of the subgoal, depending of the
  structure of the rule.
  
  Note that the @{method simp} method already involves repeated
  application of split rules as declared in the current context, using
  @{attribute split}, for example.

  \end{description}
*}


subsection {* Further tactic emulations \label{sec:tactics} *}

text {*
  The following improper proof methods emulate traditional tactics.
  These admit direct access to the goal state, which is normally
  considered harmful!  In particular, this may involve both numbered
  goal addressing (default 1), and dynamic instantiation within the
  scope of some subgoal.

  \begin{warn}
    Dynamic instantiations refer to universally quantified parameters
    of a subgoal (the dynamic context) rather than fixed variables and
    term abbreviations of a (static) Isar context.
  \end{warn}

  Tactic emulation methods, unlike their ML counterparts, admit
  simultaneous instantiation from both dynamic and static contexts.
  If names occur in both contexts goal parameters hide locally fixed
  variables.  Likewise, schematic variables refer to term
  abbreviations, if present in the static context.  Otherwise the
  schematic variable is interpreted as a schematic variable and left
  to be solved by unification with certain parts of the subgoal.

  Note that the tactic emulation proof methods in Isabelle/Isar are
  consistently named @{text foo_tac}.  Note also that variable names
  occurring on left hand sides of instantiations must be preceded by a
  question mark if they coincide with a keyword or contain dots.  This
  is consistent with the attribute @{attribute "where"} (see
  \secref{sec:pure-meth-att}).

  \begin{matharray}{rcl}
    @{method_def rule_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def erule_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def drule_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def frule_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def cut_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def thin_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def subgoal_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def rename_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def rotate_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def tactic}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def raw_tactic}@{text "\<^sup>*"} & : & @{text method} \\
  \end{matharray}

  @{rail "
    (@@{method rule_tac} | @@{method erule_tac} | @@{method drule_tac} |
      @@{method frule_tac} | @@{method cut_tac} | @@{method thin_tac}) @{syntax goal_spec}? \\
    ( dynamic_insts @'in' @{syntax thmref} | @{syntax thmrefs} )
    ;
    @@{method subgoal_tac} @{syntax goal_spec}? (@{syntax prop} +)
    ;
    @@{method rename_tac} @{syntax goal_spec}? (@{syntax name} +)
    ;
    @@{method rotate_tac} @{syntax goal_spec}? @{syntax int}?
    ;
    (@@{method tactic} | @@{method raw_tactic}) @{syntax text}
    ;

    dynamic_insts: ((@{syntax name} '=' @{syntax term}) + @'and')
  "}

\begin{description}

  \item @{method rule_tac} etc. do resolution of rules with explicit
  instantiation.  This works the same way as the ML tactics @{ML
  res_inst_tac} etc. (see \cite{isabelle-implementation})

  Multiple rules may be only given if there is no instantiation; then
  @{method rule_tac} is the same as @{ML resolve_tac} in ML (see
  \cite{isabelle-implementation}).

  \item @{method cut_tac} inserts facts into the proof state as
  assumption of a subgoal; instantiations may be given as well.  Note
  that the scope of schematic variables is spread over the main goal
  statement and rule premises are turned into new subgoals.  This is
  in contrast to the regular method @{method insert} which inserts
  closed rule statements.

  \item @{method thin_tac}~@{text \<phi>} deletes the specified premise
  from a subgoal.  Note that @{text \<phi>} may contain schematic
  variables, to abbreviate the intended proposition; the first
  matching subgoal premise will be deleted.  Removing useless premises
  from a subgoal increases its readability and can make search tactics
  run faster.

  \item @{method subgoal_tac}~@{text "\<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"} adds the propositions
  @{text "\<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"} as local premises to a subgoal, and poses the same
  as new subgoals (in the original context).

  \item @{method rename_tac}~@{text "x\<^sub>1 \<dots> x\<^sub>n"} renames parameters of a
  goal according to the list @{text "x\<^sub>1, \<dots>, x\<^sub>n"}, which refers to the
  \emph{suffix} of variables.

  \item @{method rotate_tac}~@{text n} rotates the premises of a
  subgoal by @{text n} positions: from right to left if @{text n} is
  positive, and from left to right if @{text n} is negative; the
  default value is 1.

  \item @{method tactic}~@{text "text"} produces a proof method from
  any ML text of type @{ML_type tactic}.  Apart from the usual ML
  environment and the current proof context, the ML code may refer to
  the locally bound values @{ML_text facts}, which indicates any
  current facts used for forward-chaining.

  \item @{method raw_tactic} is similar to @{method tactic}, but
  presents the goal state in its raw internal form, where simultaneous
  subgoals appear as conjunction of the logical framework instead of
  the usual split into several subgoals.  While feature this is useful
  for debugging of complex method definitions, it should not never
  appear in production theories.

  \end{description}
*}


section {* The Simplifier \label{sec:simplifier} *}

subsection {* Simplification methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def simp} & : & @{text method} \\
    @{method_def simp_all} & : & @{text method} \\
  \end{matharray}

  @{rail "
    (@@{method simp} | @@{method simp_all}) opt? (@{syntax simpmod} * )
    ;

    opt: '(' ('no_asm' | 'no_asm_simp' | 'no_asm_use' | 'asm_lr' ) ')'
    ;
    @{syntax_def simpmod}: ('add' | 'del' | 'only' | 'cong' (() | 'add' | 'del') |
      'split' (() | 'add' | 'del')) ':' @{syntax thmrefs}
  "}

  \begin{description}

  \item @{method simp} invokes the Simplifier, after declaring
  additional rules according to the arguments given.  Note that the
  @{text only} modifier first removes all other rewrite rules,
  congruences, and looper tactics (including splits), and then behaves
  like @{text add}.

  \medskip The @{text cong} modifiers add or delete Simplifier
  congruence rules (see also \secref{sec:simp-cong}), the default is
  to add.

  \medskip The @{text split} modifiers add or delete rules for the
  Splitter (see also \cite{isabelle-ref}), the default is to add.
  This works only if the Simplifier method has been properly setup to
  include the Splitter (all major object logics such HOL, HOLCF, FOL,
  ZF do this already).

  \item @{method simp_all} is similar to @{method simp}, but acts on
  all goals (backwards from the last to the first one).

  \end{description}

  By default the Simplifier methods take local assumptions fully into
  account, using equational assumptions in the subsequent
  normalization process, or simplifying assumptions themselves (cf.\
  @{ML asm_full_simp_tac} in \cite{isabelle-ref}).  In structured
  proofs this is usually quite well behaved in practice: just the
  local premises of the actual goal are involved, additional facts may
  be inserted via explicit forward-chaining (via @{command "then"},
  @{command "from"}, @{command "using"} etc.).

  Additional Simplifier options may be specified to tune the behavior
  further (mostly for unstructured scripts with many accidental local
  facts): ``@{text "(no_asm)"}'' means assumptions are ignored
  completely (cf.\ @{ML simp_tac}), ``@{text "(no_asm_simp)"}'' means
  assumptions are used in the simplification of the conclusion but are
  not themselves simplified (cf.\ @{ML asm_simp_tac}), and ``@{text
  "(no_asm_use)"}'' means assumptions are simplified but are not used
  in the simplification of each other or the conclusion (cf.\ @{ML
  full_simp_tac}).  For compatibility reasons, there is also an option
  ``@{text "(asm_lr)"}'', which means that an assumption is only used
  for simplifying assumptions which are to the right of it (cf.\ @{ML
  asm_lr_simp_tac}).

  The configuration option @{text "depth_limit"} limits the number of
  recursive invocations of the simplifier during conditional
  rewriting.

  \medskip The Splitter package is usually configured to work as part
  of the Simplifier.  The effect of repeatedly applying @{ML
  split_tac} can be simulated by ``@{text "(simp only: split:
  a\<^sub>1 \<dots> a\<^sub>n)"}''.  There is also a separate @{text split}
  method available for single-step case splitting.
*}


subsection {* Declaring rules *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_simpset"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def simp} & : & @{text attribute} \\
    @{attribute_def split} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    (@@{attribute simp} | @@{attribute split}) (() | 'add' | 'del')
  "}

  \begin{description}

  \item @{command "print_simpset"} prints the collection of rules
  declared to the Simplifier, which is also known as ``simpset''
  internally \cite{isabelle-ref}.

  \item @{attribute simp} declares simplification rules.

  \item @{attribute split} declares case split rules.

  \end{description}
*}


subsection {* Congruence rules\label{sec:simp-cong} *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def cong} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{attribute cong} (() | 'add' | 'del')
  "}

  \begin{description}

  \item @{attribute cong} declares congruence rules to the Simplifier
  context.

  \end{description}

  Congruence rules are equalities of the form @{text [display]
  "\<dots> \<Longrightarrow> f ?x\<^sub>1 \<dots> ?x\<^sub>n = f ?y\<^sub>1 \<dots> ?y\<^sub>n"}

  This controls the simplification of the arguments of @{text f}.  For
  example, some arguments can be simplified under additional
  assumptions: @{text [display] "?P\<^sub>1 \<longleftrightarrow> ?Q\<^sub>1 \<Longrightarrow> (?Q\<^sub>1 \<Longrightarrow> ?P\<^sub>2 \<longleftrightarrow> ?Q\<^sub>2) \<Longrightarrow>
  (?P\<^sub>1 \<longrightarrow> ?P\<^sub>2) \<longleftrightarrow> (?Q\<^sub>1 \<longrightarrow> ?Q\<^sub>2)"}

  Given this rule, the simplifier assumes @{text "?Q\<^sub>1"} and extracts
  rewrite rules from it when simplifying @{text "?P\<^sub>2"}.  Such local
  assumptions are effective for rewriting formulae such as @{text "x =
  0 \<longrightarrow> y + x = y"}.

  %FIXME
  %The local assumptions are also provided as theorems to the solver;
  %see \secref{sec:simp-solver} below.

  \medskip The following congruence rule for bounded quantifiers also
  supplies contextual information --- about the bound variable:
  @{text [display] "(?A = ?B) \<Longrightarrow> (\<And>x. x \<in> ?B \<Longrightarrow> ?P x \<longleftrightarrow> ?Q x) \<Longrightarrow>
    (\<forall>x \<in> ?A. ?P x) \<longleftrightarrow> (\<forall>x \<in> ?B. ?Q x)"}

  \medskip This congruence rule for conditional expressions can
  supply contextual information for simplifying the arms:
  @{text [display] "?p = ?q \<Longrightarrow> (?q \<Longrightarrow> ?a = ?c) \<Longrightarrow> (\<not> ?q \<Longrightarrow> ?b = ?d) \<Longrightarrow>
    (if ?p then ?a else ?b) = (if ?q then ?c else ?d)"}

  A congruence rule can also \emph{prevent} simplification of some
  arguments.  Here is an alternative congruence rule for conditional
  expressions that conforms to non-strict functional evaluation:
  @{text [display] "?p = ?q \<Longrightarrow> (if ?p then ?a else ?b) = (if ?q then ?a else ?b)"}

  Only the first argument is simplified; the others remain unchanged.
  This can make simplification much faster, but may require an extra
  case split over the condition @{text "?q"} to prove the goal.
*}


subsection {* Simplification procedures *}

text {* Simplification procedures are ML functions that produce proven
  rewrite rules on demand.  They are associated with higher-order
  patterns that approximate the left-hand sides of equations.  The
  Simplifier first matches the current redex against one of the LHS
  patterns; if this succeeds, the corresponding ML function is
  invoked, passing the Simplifier context and redex term.  Thus rules
  may be specifically fashioned for particular situations, resulting
  in a more powerful mechanism than term rewriting by a fixed set of
  rules.

  Any successful result needs to be a (possibly conditional) rewrite
  rule @{text "t \<equiv> u"} that is applicable to the current redex.  The
  rule will be applied just as any ordinary rewrite rule.  It is
  expected to be already in \emph{internal form}, bypassing the
  automatic preprocessing of object-level equivalences.

  \begin{matharray}{rcl}
    @{command_def "simproc_setup"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    simproc & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{command simproc_setup} @{syntax name} '(' (@{syntax term} + '|') ')' '='
      @{syntax text} \\ (@'identifier' (@{syntax nameref}+))?
    ;

    @@{attribute simproc} (('add' ':')? | 'del' ':') (@{syntax name}+)
  "}

  \begin{description}

  \item @{command "simproc_setup"} defines a named simplification
  procedure that is invoked by the Simplifier whenever any of the
  given term patterns match the current redex.  The implementation,
  which is provided as ML source text, needs to be of type @{ML_type
  "morphism -> simpset -> cterm -> thm option"}, where the @{ML_type
  cterm} represents the current redex @{text r} and the result is
  supposed to be some proven rewrite rule @{text "r \<equiv> r'"} (or a
  generalized version), or @{ML NONE} to indicate failure.  The
  @{ML_type simpset} argument holds the full context of the current
  Simplifier invocation, including the actual Isar proof context.  The
  @{ML_type morphism} informs about the difference of the original
  compilation context wrt.\ the one of the actual application later
  on.  The optional @{keyword "identifier"} specifies theorems that
  represent the logical content of the abstract theory of this
  simproc.

  Morphisms and identifiers are only relevant for simprocs that are
  defined within a local target context, e.g.\ in a locale.

  \item @{text "simproc add: name"} and @{text "simproc del: name"}
  add or delete named simprocs to the current Simplifier context.  The
  default is to add a simproc.  Note that @{command "simproc_setup"}
  already adds the new simproc to the subsequent context.

  \end{description}
*}


subsubsection {* Example *}

text {* The following simplification procedure for @{thm
  [source=false, show_types] unit_eq} in HOL performs fine-grained
  control over rule application, beyond higher-order pattern matching.
  Declaring @{thm unit_eq} as @{attribute simp} directly would make
  the simplifier loop!  Note that a version of this simplification
  procedure is already active in Isabelle/HOL.  *}

simproc_setup unit ("x::unit") = {*
  fn _ => fn _ => fn ct =>
    if HOLogic.is_unit (term_of ct) then NONE
    else SOME (mk_meta_eq @{thm unit_eq})
*}

text {* Since the Simplifier applies simplification procedures
  frequently, it is important to make the failure check in ML
  reasonably fast. *}


subsection {* Forward simplification *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def simplified} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{attribute simplified} opt? @{syntax thmrefs}?
    ;

    opt: '(' ('no_asm' | 'no_asm_simp' | 'no_asm_use') ')'
  "}

  \begin{description}
  
  \item @{attribute simplified}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} causes a theorem to
  be simplified, either by exactly the specified rules @{text "a\<^sub>1, \<dots>,
  a\<^sub>n"}, or the implicit Simplifier context if no arguments are given.
  The result is fully simplified by default, including assumptions and
  conclusion; the options @{text no_asm} etc.\ tune the Simplifier in
  the same way as the for the @{text simp} method.

  Note that forward simplification restricts the simplifier to its
  most basic operation of term rewriting; solver and looper tactics
  \cite{isabelle-ref} are \emph{not} involved here.  The @{text
  simplified} attribute should be only rarely required under normal
  circumstances.

  \end{description}
*}


section {* The Classical Reasoner \label{sec:classical} *}

subsection {* Basic concepts *}

text {* Although Isabelle is generic, many users will be working in
  some extension of classical first-order logic.  Isabelle/ZF is built
  upon theory FOL, while Isabelle/HOL conceptually contains
  first-order logic as a fragment.  Theorem-proving in predicate logic
  is undecidable, but many automated strategies have been developed to
  assist in this task.

  Isabelle's classical reasoner is a generic package that accepts
  certain information about a logic and delivers a suite of automatic
  proof tools, based on rules that are classified and declared in the
  context.  These proof procedures are slow and simplistic compared
  with high-end automated theorem provers, but they can save
  considerable time and effort in practice.  They can prove theorems
  such as Pelletier's \cite{pelletier86} problems 40 and 41 in a few
  milliseconds (including full proof reconstruction): *}

lemma "(\<exists>y. \<forall>x. F x y \<longleftrightarrow> F x x) \<longrightarrow> \<not> (\<forall>x. \<exists>y. \<forall>z. F z y \<longleftrightarrow> \<not> F z x)"
  by blast

lemma "(\<forall>z. \<exists>y. \<forall>x. f x y \<longleftrightarrow> f x z \<and> \<not> f x x) \<longrightarrow> \<not> (\<exists>z. \<forall>x. f x z)"
  by blast

text {* The proof tools are generic.  They are not restricted to
  first-order logic, and have been heavily used in the development of
  the Isabelle/HOL library and applications.  The tactics can be
  traced, and their components can be called directly; in this manner,
  any proof can be viewed interactively.  *}


subsubsection {* The sequent calculus *}

text {* Isabelle supports natural deduction, which is easy to use for
  interactive proof.  But natural deduction does not easily lend
  itself to automation, and has a bias towards intuitionism.  For
  certain proofs in classical logic, it can not be called natural.
  The \emph{sequent calculus}, a generalization of natural deduction,
  is easier to automate.

  A \textbf{sequent} has the form @{text "\<Gamma> \<turnstile> \<Delta>"}, where @{text "\<Gamma>"}
  and @{text "\<Delta>"} are sets of formulae.\footnote{For first-order
  logic, sequents can equivalently be made from lists or multisets of
  formulae.} The sequent @{text "P\<^sub>1, \<dots>, P\<^sub>m \<turnstile> Q\<^sub>1, \<dots>, Q\<^sub>n"} is
  \textbf{valid} if @{text "P\<^sub>1 \<and> \<dots> \<and> P\<^sub>m"} implies @{text "Q\<^sub>1 \<or> \<dots> \<or>
  Q\<^sub>n"}.  Thus @{text "P\<^sub>1, \<dots>, P\<^sub>m"} represent assumptions, each of which
  is true, while @{text "Q\<^sub>1, \<dots>, Q\<^sub>n"} represent alternative goals.  A
  sequent is \textbf{basic} if its left and right sides have a common
  formula, as in @{text "P, Q \<turnstile> Q, R"}; basic sequents are trivially
  valid.

  Sequent rules are classified as \textbf{right} or \textbf{left},
  indicating which side of the @{text "\<turnstile>"} symbol they operate on.
  Rules that operate on the right side are analogous to natural
  deduction's introduction rules, and left rules are analogous to
  elimination rules.  The sequent calculus analogue of @{text "(\<longrightarrow>I)"}
  is the rule
  \[
  \infer[@{text "(\<longrightarrow>R)"}]{@{text "\<Gamma> \<turnstile> \<Delta>, P \<longrightarrow> Q"}}{@{text "P, \<Gamma> \<turnstile> \<Delta>, Q"}}
  \]
  Applying the rule backwards, this breaks down some implication on
  the right side of a sequent; @{text "\<Gamma>"} and @{text "\<Delta>"} stand for
  the sets of formulae that are unaffected by the inference.  The
  analogue of the pair @{text "(\<or>I1)"} and @{text "(\<or>I2)"} is the
  single rule
  \[
  \infer[@{text "(\<or>R)"}]{@{text "\<Gamma> \<turnstile> \<Delta>, P \<or> Q"}}{@{text "\<Gamma> \<turnstile> \<Delta>, P, Q"}}
  \]
  This breaks down some disjunction on the right side, replacing it by
  both disjuncts.  Thus, the sequent calculus is a kind of
  multiple-conclusion logic.

  To illustrate the use of multiple formulae on the right, let us
  prove the classical theorem @{text "(P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)"}.  Working
  backwards, we reduce this formula to a basic sequent:
  \[
  \infer[@{text "(\<or>R)"}]{@{text "\<turnstile> (P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)"}}
    {\infer[@{text "(\<longrightarrow>R)"}]{@{text "\<turnstile> (P \<longrightarrow> Q), (Q \<longrightarrow> P)"}}
      {\infer[@{text "(\<longrightarrow>R)"}]{@{text "P \<turnstile> Q, (Q \<longrightarrow> P)"}}
        {@{text "P, Q \<turnstile> Q, P"}}}}
  \]

  This example is typical of the sequent calculus: start with the
  desired theorem and apply rules backwards in a fairly arbitrary
  manner.  This yields a surprisingly effective proof procedure.
  Quantifiers add only few complications, since Isabelle handles
  parameters and schematic variables.  See \cite[Chapter
  10]{paulson-ml2} for further discussion.  *}


subsubsection {* Simulating sequents by natural deduction *}

text {* Isabelle can represent sequents directly, as in the
  object-logic LK.  But natural deduction is easier to work with, and
  most object-logics employ it.  Fortunately, we can simulate the
  sequent @{text "P\<^sub>1, \<dots>, P\<^sub>m \<turnstile> Q\<^sub>1, \<dots>, Q\<^sub>n"} by the Isabelle formula
  @{text "P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>m \<Longrightarrow> \<not> Q\<^sub>2 \<Longrightarrow> ... \<Longrightarrow> \<not> Q\<^sub>n \<Longrightarrow> Q\<^sub>1"} where the order of
  the assumptions and the choice of @{text "Q\<^sub>1"} are arbitrary.
  Elim-resolution plays a key role in simulating sequent proofs.

  We can easily handle reasoning on the left.  Elim-resolution with
  the rules @{text "(\<or>E)"}, @{text "(\<bottom>E)"} and @{text "(\<exists>E)"} achieves
  a similar effect as the corresponding sequent rules.  For the other
  connectives, we use sequent-style elimination rules instead of
  destruction rules such as @{text "(\<and>E1, 2)"} and @{text "(\<forall>E)"}.
  But note that the rule @{text "(\<not>L)"} has no effect under our
  representation of sequents!
  \[
  \infer[@{text "(\<not>L)"}]{@{text "\<not> P, \<Gamma> \<turnstile> \<Delta>"}}{@{text "\<Gamma> \<turnstile> \<Delta>, P"}}
  \]

  What about reasoning on the right?  Introduction rules can only
  affect the formula in the conclusion, namely @{text "Q\<^sub>1"}.  The
  other right-side formulae are represented as negated assumptions,
  @{text "\<not> Q\<^sub>2, \<dots>, \<not> Q\<^sub>n"}.  In order to operate on one of these, it
  must first be exchanged with @{text "Q\<^sub>1"}.  Elim-resolution with the
  @{text swap} rule has this effect: @{text "\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R"}

  To ensure that swaps occur only when necessary, each introduction
  rule is converted into a swapped form: it is resolved with the
  second premise of @{text "(swap)"}.  The swapped form of @{text
  "(\<and>I)"}, which might be called @{text "(\<not>\<and>E)"}, is
  @{text [display] "\<not> (P \<and> Q) \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (\<not> R \<Longrightarrow> Q) \<Longrightarrow> R"}

  Similarly, the swapped form of @{text "(\<longrightarrow>I)"} is
  @{text [display] "\<not> (P \<longrightarrow> Q) \<Longrightarrow> (\<not> R \<Longrightarrow> P \<Longrightarrow> Q) \<Longrightarrow> R"}

  Swapped introduction rules are applied using elim-resolution, which
  deletes the negated formula.  Our representation of sequents also
  requires the use of ordinary introduction rules.  If we had no
  regard for readability of intermediate goal states, we could treat
  the right side more uniformly by representing sequents as @{text
  [display] "P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>m \<Longrightarrow> \<not> Q\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<not> Q\<^sub>n \<Longrightarrow> \<bottom>"}
*}


subsubsection {* Extra rules for the sequent calculus *}

text {* As mentioned, destruction rules such as @{text "(\<and>E1, 2)"} and
  @{text "(\<forall>E)"} must be replaced by sequent-style elimination rules.
  In addition, we need rules to embody the classical equivalence
  between @{text "P \<longrightarrow> Q"} and @{text "\<not> P \<or> Q"}.  The introduction
  rules @{text "(\<or>I1, 2)"} are replaced by a rule that simulates
  @{text "(\<or>R)"}: @{text [display] "(\<not> Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q"}

  The destruction rule @{text "(\<longrightarrow>E)"} is replaced by @{text [display]
  "(P \<longrightarrow> Q) \<Longrightarrow> (\<not> P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"}

  Quantifier replication also requires special rules.  In classical
  logic, @{text "\<exists>x. P x"} is equivalent to @{text "\<not> (\<forall>x. \<not> P x)"};
  the rules @{text "(\<exists>R)"} and @{text "(\<forall>L)"} are dual:
  \[
  \infer[@{text "(\<exists>R)"}]{@{text "\<Gamma> \<turnstile> \<Delta>, \<exists>x. P x"}}{@{text "\<Gamma> \<turnstile> \<Delta>, \<exists>x. P x, P t"}}
  \qquad
  \infer[@{text "(\<forall>L)"}]{@{text "\<forall>x. P x, \<Gamma> \<turnstile> \<Delta>"}}{@{text "P t, \<forall>x. P x, \<Gamma> \<turnstile> \<Delta>"}}
  \]
  Thus both kinds of quantifier may be replicated.  Theorems requiring
  multiple uses of a universal formula are easy to invent; consider
  @{text [display] "(\<forall>x. P x \<longrightarrow> P (f x)) \<and> P a \<longrightarrow> P (f\<^sup>n a)"} for any
  @{text "n > 1"}.  Natural examples of the multiple use of an
  existential formula are rare; a standard one is @{text "\<exists>x. \<forall>y. P x
  \<longrightarrow> P y"}.

  Forgoing quantifier replication loses completeness, but gains
  decidability, since the search space becomes finite.  Many useful
  theorems can be proved without replication, and the search generally
  delivers its verdict in a reasonable time.  To adopt this approach,
  represent the sequent rules @{text "(\<exists>R)"}, @{text "(\<exists>L)"} and
  @{text "(\<forall>R)"} by @{text "(\<exists>I)"}, @{text "(\<exists>E)"} and @{text "(\<forall>I)"},
  respectively, and put @{text "(\<forall>E)"} into elimination form: @{text
  [display] "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> Q) \<Longrightarrow> Q"}

  Elim-resolution with this rule will delete the universal formula
  after a single use.  To replicate universal quantifiers, replace the
  rule by @{text [display] "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> \<forall>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q"}

  To replicate existential quantifiers, replace @{text "(\<exists>I)"} by
  @{text [display] "(\<not> (\<exists>x. P x) \<Longrightarrow> P t) \<Longrightarrow> \<exists>x. P x"}

  All introduction rules mentioned above are also useful in swapped
  form.

  Replication makes the search space infinite; we must apply the rules
  with care.  The classical reasoner distinguishes between safe and
  unsafe rules, applying the latter only when there is no alternative.
  Depth-first search may well go down a blind alley; best-first search
  is better behaved in an infinite search space.  However, quantifier
  replication is too expensive to prove any but the simplest theorems.
*}


subsection {* Rule declarations *}

text {* The proof tools of the Classical Reasoner depend on
  collections of rules declared in the context, which are classified
  as introduction, elimination or destruction and as \emph{safe} or
  \emph{unsafe}.  In general, safe rules can be attempted blindly,
  while unsafe rules must be used with care.  A safe rule must never
  reduce a provable goal to an unprovable set of subgoals.

  The rule @{text "P \<Longrightarrow> P \<or> Q"} is unsafe because it reduces @{text "P
  \<or> Q"} to @{text "P"}, which might turn out as premature choice of an
  unprovable subgoal.  Any rule is unsafe whose premises contain new
  unknowns.  The elimination rule @{text "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> Q) \<Longrightarrow> Q"} is
  unsafe, since it is applied via elim-resolution, which discards the
  assumption @{text "\<forall>x. P x"} and replaces it by the weaker
  assumption @{text "P t"}.  The rule @{text "P t \<Longrightarrow> \<exists>x. P x"} is
  unsafe for similar reasons.  The quantifier duplication rule @{text
  "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> \<forall>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q"} is unsafe in a different sense:
  since it keeps the assumption @{text "\<forall>x. P x"}, it is prone to
  looping.  In classical first-order logic, all rules are safe except
  those mentioned above.

  The safe~/ unsafe distinction is vague, and may be regarded merely
  as a way of giving some rules priority over others.  One could argue
  that @{text "(\<or>E)"} is unsafe, because repeated application of it
  could generate exponentially many subgoals.  Induction rules are
  unsafe because inductive proofs are difficult to set up
  automatically.  Any inference is unsafe that instantiates an unknown
  in the proof state --- thus matching must be used, rather than
  unification.  Even proof by assumption is unsafe if it instantiates
  unknowns shared with other subgoals.

  \begin{matharray}{rcl}
    @{command_def "print_claset"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def intro} & : & @{text attribute} \\
    @{attribute_def elim} & : & @{text attribute} \\
    @{attribute_def dest} & : & @{text attribute} \\
    @{attribute_def rule} & : & @{text attribute} \\
    @{attribute_def iff} & : & @{text attribute} \\
    @{attribute_def swapped} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    (@@{attribute intro} | @@{attribute elim} | @@{attribute dest}) ('!' | () | '?') @{syntax nat}?
    ;
    @@{attribute rule} 'del'
    ;
    @@{attribute iff} (((() | 'add') '?'?) | 'del')
  "}

  \begin{description}

  \item @{command "print_claset"} prints the collection of rules
  declared to the Classical Reasoner, i.e.\ the @{ML_type claset}
  within the context.

  \item @{attribute intro}, @{attribute elim}, and @{attribute dest}
  declare introduction, elimination, and destruction rules,
  respectively.  By default, rules are considered as \emph{unsafe}
  (i.e.\ not applied blindly without backtracking), while ``@{text
  "!"}'' classifies as \emph{safe}.  Rule declarations marked by
  ``@{text "?"}'' coincide with those of Isabelle/Pure, cf.\
  \secref{sec:pure-meth-att} (i.e.\ are only applied in single steps
  of the @{method rule} method).  The optional natural number
  specifies an explicit weight argument, which is ignored by the
  automated reasoning tools, but determines the search order of single
  rule steps.

  Introduction rules are those that can be applied using ordinary
  resolution.  Their swapped forms are generated internally, which
  will be applied using elim-resolution.  Elimination rules are
  applied using elim-resolution.  Rules are sorted by the number of
  new subgoals they will yield; rules that generate the fewest
  subgoals will be tried first.  Otherwise, later declarations take
  precedence over earlier ones.

  Rules already present in the context with the same classification
  are ignored.  A warning is printed if the rule has already been
  added with some other classification, but the rule is added anyway
  as requested.

  \item @{attribute rule}~@{text del} deletes all occurrences of a
  rule from the classical context, regardless of its classification as
  introduction~/ elimination~/ destruction and safe~/ unsafe.

  \item @{attribute iff} declares logical equivalences to the
  Simplifier and the Classical reasoner at the same time.
  Non-conditional rules result in a safe introduction and elimination
  pair; conditional ones are considered unsafe.  Rules with negative
  conclusion are automatically inverted (using @{text "\<not>"}-elimination
  internally).

  The ``@{text "?"}'' version of @{attribute iff} declares rules to
  the Isabelle/Pure context only, and omits the Simplifier
  declaration.

  \item @{attribute swapped} turns an introduction rule into an
  elimination, by resolving with the classical swap principle @{text
  "\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R"} in the second position.  This is mainly for
  illustrative purposes: the Classical Reasoner already swaps rules
  internally as explained above.

  \end{description}
*}


subsection {* Structured methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def rule} & : & @{text method} \\
    @{method_def contradiction} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method rule} @{syntax thmrefs}?
  "}

  \begin{description}

  \item @{method rule} as offered by the Classical Reasoner is a
  refinement over the Pure one (see \secref{sec:pure-meth-att}).  Both
  versions work the same, but the classical version observes the
  classical rule context in addition to that of Isabelle/Pure.

  Common object logics (HOL, ZF, etc.) declare a rich collection of
  classical rules (even if these would qualify as intuitionistic
  ones), but only few declarations to the rule context of
  Isabelle/Pure (\secref{sec:pure-meth-att}).

  \item @{method contradiction} solves some goal by contradiction,
  deriving any result from both @{text "\<not> A"} and @{text A}.  Chained
  facts, which are guaranteed to participate, may appear in either
  order.

  \end{description}
*}


subsection {* Automated methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def blast} & : & @{text method} \\
    @{method_def auto} & : & @{text method} \\
    @{method_def force} & : & @{text method} \\
    @{method_def fast} & : & @{text method} \\
    @{method_def slow} & : & @{text method} \\
    @{method_def best} & : & @{text method} \\
    @{method_def fastforce} & : & @{text method} \\
    @{method_def slowsimp} & : & @{text method} \\
    @{method_def bestsimp} & : & @{text method} \\
    @{method_def deepen} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method blast} @{syntax nat}? (@{syntax clamod} * )
    ;
    @@{method auto} (@{syntax nat} @{syntax nat})? (@{syntax clasimpmod} * )
    ;
    @@{method force} (@{syntax clasimpmod} * )
    ;
    (@@{method fast} | @@{method slow} | @@{method best}) (@{syntax clamod} * )
    ;
    (@@{method fastforce} | @@{method slowsimp} | @@{method bestsimp})
      (@{syntax clasimpmod} * )
    ;
    @@{method deepen} (@{syntax nat} ?) (@{syntax clamod} * )
    ;
    @{syntax_def clamod}:
      (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del') ':' @{syntax thmrefs}
    ;
    @{syntax_def clasimpmod}: ('simp' (() | 'add' | 'del' | 'only') |
      ('cong' | 'split') (() | 'add' | 'del') |
      'iff' (((() | 'add') '?'?) | 'del') |
      (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del')) ':' @{syntax thmrefs}
  "}

  \begin{description}

  \item @{method blast} is a separate classical tableau prover that
  uses the same classical rule declarations as explained before.

  Proof search is coded directly in ML using special data structures.
  A successful proof is then reconstructed using regular Isabelle
  inferences.  It is faster and more powerful than the other classical
  reasoning tools, but has major limitations too.

  \begin{itemize}

  \item It does not use the classical wrapper tacticals, such as the
  integration with the Simplifier of @{method fastforce}.

  \item It does not perform higher-order unification, as needed by the
  rule @{thm [source=false] rangeI} in HOL.  There are often
  alternatives to such rules, for example @{thm [source=false]
  range_eqI}.

  \item Function variables may only be applied to parameters of the
  subgoal.  (This restriction arises because the prover does not use
  higher-order unification.)  If other function variables are present
  then the prover will fail with the message \texttt{Function Var's
  argument not a bound variable}.

  \item Its proof strategy is more general than @{method fast} but can
  be slower.  If @{method blast} fails or seems to be running forever,
  try @{method fast} and the other proof tools described below.

  \end{itemize}

  The optional integer argument specifies a bound for the number of
  unsafe steps used in a proof.  By default, @{method blast} starts
  with a bound of 0 and increases it successively to 20.  In contrast,
  @{text "(blast lim)"} tries to prove the goal using a search bound
  of @{text "lim"}.  Sometimes a slow proof using @{method blast} can
  be made much faster by supplying the successful search bound to this
  proof method instead.

  \item @{method auto} combines classical reasoning with
  simplification.  It is intended for situations where there are a lot
  of mostly trivial subgoals; it proves all the easy ones, leaving the
  ones it cannot prove.  Occasionally, attempting to prove the hard
  ones may take a long time.

  The optional depth arguments in @{text "(auto m n)"} refer to its
  builtin classical reasoning procedures: @{text m} (default 4) is for
  @{method blast}, which is tried first, and @{text n} (default 2) is
  for a slower but more general alternative that also takes wrappers
  into account.

  \item @{method force} is intended to prove the first subgoal
  completely, using many fancy proof tools and performing a rather
  exhaustive search.  As a result, proof attempts may take rather long
  or diverge easily.

  \item @{method fast}, @{method best}, @{method slow} attempt to
  prove the first subgoal using sequent-style reasoning as explained
  before.  Unlike @{method blast}, they construct proofs directly in
  Isabelle.

  There is a difference in search strategy and back-tracking: @{method
  fast} uses depth-first search and @{method best} uses best-first
  search (guided by a heuristic function: normally the total size of
  the proof state).

  Method @{method slow} is like @{method fast}, but conducts a broader
  search: it may, when backtracking from a failed proof attempt, undo
  even the step of proving a subgoal by assumption.

  \item @{method fastforce}, @{method slowsimp}, @{method bestsimp}
  are like @{method fast}, @{method slow}, @{method best},
  respectively, but use the Simplifier as additional wrapper. The name
  @{method fastforce}, reflects the behaviour of this popular method
  better without requiring an understanding of its implementation.

  \item @{method deepen} works by exhaustive search up to a certain
  depth.  The start depth is 4 (unless specified explicitly), and the
  depth is increased iteratively up to 10.  Unsafe rules are modified
  to preserve the formula they act on, so that it be used repeatedly.
  This method can prove more goals than @{method fast}, but is much
  slower, for example if the assumptions have many universal
  quantifiers.

  \end{description}

  Any of the above methods support additional modifiers of the context
  of classical (and simplifier) rules, but the ones related to the
  Simplifier are explicitly prefixed by @{text simp} here.  The
  semantics of these ad-hoc rule declarations is analogous to the
  attributes given before.  Facts provided by forward chaining are
  inserted into the goal before commencing proof search.
*}


subsection {* Semi-automated methods *}

text {* These proof methods may help in situations when the
  fully-automated tools fail.  The result is a simpler subgoal that
  can be tackled by other means, such as by manual instantiation of
  quantifiers.

  \begin{matharray}{rcl}
    @{method_def safe} & : & @{text method} \\
    @{method_def clarify} & : & @{text method} \\
    @{method_def clarsimp} & : & @{text method} \\
  \end{matharray}

  @{rail "
    (@@{method safe} | @@{method clarify}) (@{syntax clamod} * )
    ;
    @@{method clarsimp} (@{syntax clasimpmod} * )
  "}

  \begin{description}

  \item @{method safe} repeatedly performs safe steps on all subgoals.
  It is deterministic, with at most one outcome.

  \item @{method clarify} performs a series of safe steps without
  splitting subgoals; see also @{ML clarify_step_tac}.

  \item @{method clarsimp} acts like @{method clarify}, but also does
  simplification.  Note that if the Simplifier context includes a
  splitter for the premises, the subgoal may still be split.

  \end{description}
*}


subsection {* Single-step tactics *}

text {*
  \begin{matharray}{rcl}
    @{index_ML safe_step_tac: "Proof.context -> int -> tactic"} \\
    @{index_ML inst_step_tac: "Proof.context -> int -> tactic"} \\
    @{index_ML step_tac: "Proof.context -> int -> tactic"} \\
    @{index_ML slow_step_tac: "Proof.context -> int -> tactic"} \\
    @{index_ML clarify_step_tac: "Proof.context -> int -> tactic"} \\
  \end{matharray}

  These are the primitive tactics behind the (semi)automated proof
  methods of the Classical Reasoner.  By calling them yourself, you
  can execute these procedures one step at a time.

  \begin{description}

  \item @{ML safe_step_tac}~@{text "ctxt i"} performs a safe step on
  subgoal @{text i}.  The safe wrapper tacticals are applied to a
  tactic that may include proof by assumption or Modus Ponens (taking
  care not to instantiate unknowns), or substitution.

  \item @{ML inst_step_tac} is like @{ML safe_step_tac}, but allows
  unknowns to be instantiated.

  \item @{ML step_tac}~@{text "ctxt i"} is the basic step of the proof
  procedure.  The unsafe wrapper tacticals are applied to a tactic
  that tries @{ML safe_tac}, @{ML inst_step_tac}, or applies an unsafe
  rule from the context.

  \item @{ML slow_step_tac} resembles @{ML step_tac}, but allows
  backtracking between using safe rules with instantiation (@{ML
  inst_step_tac}) and using unsafe rules.  The resulting search space
  is larger.

  \item @{ML clarify_step_tac}~@{text "ctxt i"} performs a safe step
  on subgoal @{text i}.  No splitting step is applied; for example,
  the subgoal @{text "A \<and> B"} is left as a conjunction.  Proof by
  assumption, Modus Ponens, etc., may be performed provided they do
  not instantiate unknowns.  Assumptions of the form @{text "x = t"}
  may be eliminated.  The safe wrapper tactical is applied.

  \end{description}
*}


section {* Object-logic setup \label{sec:object-logic} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "judgment"} & : & @{text "theory \<rightarrow> theory"} \\
    @{method_def atomize} & : & @{text method} \\
    @{attribute_def atomize} & : & @{text attribute} \\
    @{attribute_def rule_format} & : & @{text attribute} \\
    @{attribute_def rulify} & : & @{text attribute} \\
  \end{matharray}

  The very starting point for any Isabelle object-logic is a ``truth
  judgment'' that links object-level statements to the meta-logic
  (with its minimal language of @{text prop} that covers universal
  quantification @{text "\<And>"} and implication @{text "\<Longrightarrow>"}).

  Common object-logics are sufficiently expressive to internalize rule
  statements over @{text "\<And>"} and @{text "\<Longrightarrow>"} within their own
  language.  This is useful in certain situations where a rule needs
  to be viewed as an atomic statement from the meta-level perspective,
  e.g.\ @{text "\<And>x. x \<in> A \<Longrightarrow> P x"} versus @{text "\<forall>x \<in> A. P x"}.

  From the following language elements, only the @{method atomize}
  method and @{attribute rule_format} attribute are occasionally
  required by end-users, the rest is for those who need to setup their
  own object-logic.  In the latter case existing formulations of
  Isabelle/FOL or Isabelle/HOL may be taken as realistic examples.

  Generic tools may refer to the information provided by object-logic
  declarations internally.

  @{rail "
    @@{command judgment} @{syntax name} '::' @{syntax type} @{syntax mixfix}?
    ;
    @@{attribute atomize} ('(' 'full' ')')?
    ;
    @@{attribute rule_format} ('(' 'noasm' ')')?
  "}

  \begin{description}
  
  \item @{command "judgment"}~@{text "c :: \<sigma> (mx)"} declares constant
  @{text c} as the truth judgment of the current object-logic.  Its
  type @{text \<sigma>} should specify a coercion of the category of
  object-level propositions to @{text prop} of the Pure meta-logic;
  the mixfix annotation @{text "(mx)"} would typically just link the
  object language (internally of syntactic category @{text logic})
  with that of @{text prop}.  Only one @{command "judgment"}
  declaration may be given in any theory development.
  
  \item @{method atomize} (as a method) rewrites any non-atomic
  premises of a sub-goal, using the meta-level equations declared via
  @{attribute atomize} (as an attribute) beforehand.  As a result,
  heavily nested goals become amenable to fundamental operations such
  as resolution (cf.\ the @{method (Pure) rule} method).  Giving the ``@{text
  "(full)"}'' option here means to turn the whole subgoal into an
  object-statement (if possible), including the outermost parameters
  and assumptions as well.

  A typical collection of @{attribute atomize} rules for a particular
  object-logic would provide an internalization for each of the
  connectives of @{text "\<And>"}, @{text "\<Longrightarrow>"}, and @{text "\<equiv>"}.
  Meta-level conjunction should be covered as well (this is
  particularly important for locales, see \secref{sec:locale}).

  \item @{attribute rule_format} rewrites a theorem by the equalities
  declared as @{attribute rulify} rules in the current object-logic.
  By default, the result is fully normalized, including assumptions
  and conclusions at any depth.  The @{text "(no_asm)"} option
  restricts the transformation to the conclusion of a rule.

  In common object-logics (HOL, FOL, ZF), the effect of @{attribute
  rule_format} is to replace (bounded) universal quantification
  (@{text "\<forall>"}) and implication (@{text "\<longrightarrow>"}) by the corresponding
  rule statements over @{text "\<And>"} and @{text "\<Longrightarrow>"}.

  \end{description}
*}

end

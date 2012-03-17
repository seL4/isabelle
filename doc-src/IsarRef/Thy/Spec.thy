theory Spec
imports Base Main
begin

chapter {* Specifications *}

text {*
  The Isabelle/Isar theory format integrates specifications and
  proofs, supporting interactive development with unlimited undo
  operation.  There is an integrated document preparation system (see
  \chref{ch:document-prep}), for typesetting formal developments
  together with informal text.  The resulting hyper-linked PDF
  documents can be used both for WWW presentation and printed copies.

  The Isar proof language (see \chref{ch:proofs}) is embedded into the
  theory language as a proper sub-language.  Proof mode is entered by
  stating some @{command theorem} or @{command lemma} at the theory
  level, and left again with the final conclusion (e.g.\ via @{command
  qed}).  Some theory specification mechanisms also require a proof,
  such as @{command typedef} in HOL, which demands non-emptiness of
  the representing sets.
*}


section {* Defining theories \label{sec:begin-thy} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "theory"} & : & @{text "toplevel \<rightarrow> theory"} \\
    @{command_def (global) "end"} & : & @{text "theory \<rightarrow> toplevel"} \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory files, which may
  contain both specifications and proofs; occasionally definitional
  mechanisms also require some explicit proof.  The theory body may be
  sub-structured by means of \emph{local theory targets}, such as
  @{command "locale"} and @{command "class"}.

  The first proper command of a theory is @{command "theory"}, which
  indicates imports of previous theories and optional dependencies on
  other source files (usually in ML).  Just preceding the initial
  @{command "theory"} command there may be an optional @{command
  "header"} declaration, which is only relevant to document
  preparation: see also the other section markup commands in
  \secref{sec:markup}.

  A theory is concluded by a final @{command (global) "end"} command,
  one that does not belong to a local theory target.  No further
  commands may follow such a global @{command (global) "end"},
  although some user-interfaces might pretend that trailing input is
  admissible.

  @{rail "
    @@{command theory} @{syntax name} \\ @'imports' (@{syntax name} +) uses? @'begin'
    ;

    uses: @'uses' ((@{syntax name} | @{syntax parname}) +)
  "}

  \begin{description}

  \item @{command "theory"}~@{text "A \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>"}
  starts a new theory @{text A} based on the merge of existing
  theories @{text "B\<^sub>1 \<dots> B\<^sub>n"}.
  
  Due to the possibility to import more than one ancestor, the
  resulting theory structure of an Isabelle session forms a directed
  acyclic graph (DAG).  Isabelle's theory loader ensures that the
  sources contributing to the development graph are always up-to-date:
  changed files are automatically reloaded whenever a theory header
  specification is processed.
  
  The optional @{keyword_def "uses"} specification declares additional
  dependencies on extra files (usually ML sources).  Files will be
  loaded immediately (as ML), unless the name is parenthesized.  The
  latter case records a dependency that needs to be resolved later in
  the text, usually via explicit @{command_ref "use"} for ML files;
  other file formats require specific load commands defined by the
  corresponding tools or packages.
  
  \item @{command (global) "end"} concludes the current theory
  definition.  Note that local theory targets involve a local
  @{command (local) "end"}, which is clear from the nesting.

  \end{description}
*}


section {* Local theory targets \label{sec:target} *}

text {*
  A local theory target is a context managed separately within the
  enclosing theory.  Contexts may introduce parameters (fixed
  variables) and assumptions (hypotheses).  Definitions and theorems
  depending on the context may be added incrementally later on.  Named
  contexts refer to locales (cf.\ \secref{sec:locale}) or type classes
  (cf.\ \secref{sec:class}); the name ``@{text "-"}'' signifies the
  global theory context.

  \begin{matharray}{rcll}
    @{command_def "context"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def (local) "end"} & : & @{text "local_theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
    @@{command context} @{syntax nameref} @'begin'
    ;

    @{syntax_def target}: '(' @'in' @{syntax nameref} ')'
  "}

  \begin{description}
  
  \item @{command "context"}~@{text "c \<BEGIN>"} recommences an
  existing locale or class context @{text c}.  Note that locale and
  class definitions allow to include the @{keyword "begin"} keyword as
  well, in order to continue the local theory immediately after the
  initial specification.
  
  \item @{command (local) "end"} concludes the current local theory
  and continues the enclosing global theory.  Note that a global
  @{command (global) "end"} has a different meaning: it concludes the
  theory itself (\secref{sec:begin-thy}).
  
  \item @{text "("}@{keyword_def "in"}~@{text "c)"} given after any
  local theory command specifies an immediate target, e.g.\
  ``@{command "definition"}~@{text "(\<IN> c) \<dots>"}'' or ``@{command
  "theorem"}~@{text "(\<IN> c) \<dots>"}''.  This works both in a local or
  global theory context; the current target context will be suspended
  for this command only.  Note that ``@{text "(\<IN> -)"}'' will
  always produce a global result independently of the current target
  context.

  \end{description}

  The exact meaning of results produced within a local theory context
  depends on the underlying target infrastructure (locale, type class
  etc.).  The general idea is as follows, considering a context named
  @{text c} with parameter @{text x} and assumption @{text "A[x]"}.
  
  Definitions are exported by introducing a global version with
  additional arguments; a syntactic abbreviation links the long form
  with the abstract version of the target context.  For example,
  @{text "a \<equiv> t[x]"} becomes @{text "c.a ?x \<equiv> t[?x]"} at the theory
  level (for arbitrary @{text "?x"}), together with a local
  abbreviation @{text "c \<equiv> c.a x"} in the target context (for the
  fixed parameter @{text x}).

  Theorems are exported by discharging the assumptions and
  generalizing the parameters of the context.  For example, @{text "a:
  B[x]"} becomes @{text "c.a: A[?x] \<Longrightarrow> B[?x]"}, again for arbitrary
  @{text "?x"}.
*}


section {* Basic specification elements *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
    @{command_def "definition"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def "defn"} & : & @{text attribute} \\
    @{command_def "abbreviation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_abbrevs"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow> "} \\
  \end{matharray}

  These specification mechanisms provide a slightly more abstract view
  than the underlying primitives of @{command "consts"}, @{command
  "defs"} (see \secref{sec:consts}), and @{command "axioms"} (see
  \secref{sec:axms-thms}).  In particular, type-inference is commonly
  available, and result names need not be given.

  @{rail "
    @@{command axiomatization} @{syntax \"fixes\"}? (@'where' specs)?
    ;
    @@{command definition} @{syntax target}? \\
      (decl @'where')? @{syntax thmdecl}? @{syntax prop}
    ;
    @@{command abbreviation} @{syntax target}? @{syntax mode}? \\
      (decl @'where')? @{syntax prop}
    ;

    @{syntax_def \"fixes\"}: ((@{syntax name} ('::' @{syntax type})?
      @{syntax mixfix}? | @{syntax vars}) + @'and')
    ;
    specs: (@{syntax thmdecl}? @{syntax props} + @'and')
    ;
    decl: @{syntax name} ('::' @{syntax type})? @{syntax mixfix}?
  "}

  \begin{description}
  
  \item @{command "axiomatization"}~@{text "c\<^sub>1 \<dots> c\<^sub>m \<WHERE> \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}
  introduces several constants simultaneously and states axiomatic
  properties for these.  The constants are marked as being specified
  once and for all, which prevents additional specifications being
  issued later on.
  
  Note that axiomatic specifications are only appropriate when
  declaring a new logical system; axiomatic specifications are
  restricted to global theory contexts.  Normal applications should
  only use definitional mechanisms!

  \item @{command "definition"}~@{text "c \<WHERE> eq"} produces an
  internal definition @{text "c \<equiv> t"} according to the specification
  given as @{text eq}, which is then turned into a proven fact.  The
  given proposition may deviate from internal meta-level equality
  according to the rewrite rules declared as @{attribute defn} by the
  object-logic.  This usually covers object-level equality @{text "x =
  y"} and equivalence @{text "A \<leftrightarrow> B"}.  End-users normally need not
  change the @{attribute defn} setup.
  
  Definitions may be presented with explicit arguments on the LHS, as
  well as additional conditions, e.g.\ @{text "f x y = t"} instead of
  @{text "f \<equiv> \<lambda>x y. t"} and @{text "y \<noteq> 0 \<Longrightarrow> g x y = u"} instead of an
  unrestricted @{text "g \<equiv> \<lambda>x y. u"}.
  
  \item @{command "abbreviation"}~@{text "c \<WHERE> eq"} introduces a
  syntactic constant which is associated with a certain term according
  to the meta-level equality @{text eq}.
  
  Abbreviations participate in the usual type-inference process, but
  are expanded before the logic ever sees them.  Pretty printing of
  terms involves higher-order rewriting with rules stemming from
  reverted abbreviations.  This needs some care to avoid overlapping
  or looping syntactic replacements!
  
  The optional @{text mode} specification restricts output to a
  particular print mode; using ``@{text input}'' here achieves the
  effect of one-way abbreviations.  The mode may also include an
  ``@{keyword "output"}'' qualifier that affects the concrete syntax
  declared for abbreviations, cf.\ @{command "syntax"} in
  \secref{sec:syn-trans}.
  
  \item @{command "print_abbrevs"} prints all constant abbreviations
  of the current context.
  
  \end{description}
*}


section {* Generic declarations *}

text {*
  Arbitrary operations on the background context may be wrapped-up as
  generic declaration elements.  Since the underlying concept of local
  theories may be subject to later re-interpretation, there is an
  additional dependency on a morphism that tells the difference of the
  original declaration context wrt.\ the application context
  encountered later on.  A fact declaration is an important special
  case: it consists of a theorem which is applied to the context by
  means of an attribute.

  \begin{matharray}{rcl}
    @{command_def "declaration"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "syntax_declaration"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "declare"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail "
    (@@{command declaration} | @@{command syntax_declaration})
      ('(' @'pervasive' ')')? \\ @{syntax target}? @{syntax text}
    ;
    @@{command declare} @{syntax target}? (@{syntax thmrefs} + @'and')
  "}

  \begin{description}

  \item @{command "declaration"}~@{text d} adds the declaration
  function @{text d} of ML type @{ML_type declaration}, to the current
  local theory under construction.  In later application contexts, the
  function is transformed according to the morphisms being involved in
  the interpretation hierarchy.

  If the @{text "(pervasive)"} option is given, the corresponding
  declaration is applied to all possible contexts involved, including
  the global background theory.

  \item @{command "syntax_declaration"} is similar to @{command
  "declaration"}, but is meant to affect only ``syntactic'' tools by
  convention (such as notation and type-checking information).

  \item @{command "declare"}~@{text thms} declares theorems to the
  current local theory context.  No theorem binding is involved here,
  unlike @{command "theorems"} or @{command "lemmas"} (cf.\
  \secref{sec:axms-thms}), so @{command "declare"} only has the effect
  of applying attributes as included in the theorem specification.

  \end{description}
*}


section {* Locales \label{sec:locale} *}

text {*
  Locales are parametric named local contexts, consisting of a list of
  declaration elements that are modeled after the Isar proof context
  commands (cf.\ \secref{sec:proof-context}).
*}


subsection {* Locale expressions \label{sec:locale-expr} *}

text {*
  A \emph{locale expression} denotes a structured context composed of
  instances of existing locales.  The context consists of a list of
  instances of declaration elements from the locales.  Two locale
  instances are equal if they are of the same locale and the
  parameters are instantiated with equivalent terms.  Declaration
  elements from equal instances are never repeated, thus avoiding
  duplicate declarations.

  @{rail "
    @{syntax_def locale_expr}: (instance + '+') (@'for' (@{syntax \"fixes\"} + @'and'))?
    ;
    instance: (qualifier ':')? @{syntax nameref} (pos_insts | named_insts)
    ;
    qualifier: @{syntax name} ('?' | '!')?
    ;
    pos_insts: ('_' | @{syntax term})*
    ;
    named_insts: @'where' (@{syntax name} '=' @{syntax term} + @'and')
  "}

  A locale instance consists of a reference to a locale and either
  positional or named parameter instantiations.  Identical
  instantiations (that is, those that instante a parameter by itself)
  may be omitted.  The notation `@{text "_"}' enables to omit the
  instantiation for a parameter inside a positional instantiation.

  Terms in instantiations are from the context the locale expressions
  is declared in.  Local names may be added to this context with the
  optional for clause.  In addition, syntax declarations from one
  instance are effective when parsing subsequent instances of the same
  expression.

  Instances have an optional qualifier which applies to names in
  declarations.  Names include local definitions and theorem names.
  If present, the qualifier itself is either optional
  (``\texttt{?}''), which means that it may be omitted on input of the
  qualified name, or mandatory (``\texttt{!}'').  If neither
  ``\texttt{?}'' nor ``\texttt{!}'' are present, the command's default
  is used.  For @{command "interpretation"} and @{command "interpret"}
  the default is ``mandatory'', for @{command "locale"} and @{command
  "sublocale"} the default is ``optional''.
*}


subsection {* Locale declarations *}

text {*
  \begin{matharray}{rcl}
    @{command_def "locale"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "print_locale"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_locales"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{method_def intro_locales} & : & @{text method} \\
    @{method_def unfold_locales} & : & @{text method} \\
  \end{matharray}

  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}
  @{rail "
    @@{command locale} @{syntax name} ('=' @{syntax locale})? @'begin'?
    ;
    @@{command print_locale} '!'? @{syntax nameref}
    ;
    @{syntax_def locale}: @{syntax context_elem}+ |
      @{syntax locale_expr} ('+' (@{syntax context_elem}+))?
    ;
    @{syntax_def context_elem}:
      @'fixes' (@{syntax \"fixes\"} + @'and') |
      @'constrains' (@{syntax name} '::' @{syntax type} + @'and') |
      @'assumes' (@{syntax props} + @'and') |
      @'defines' (@{syntax thmdecl}? @{syntax prop} @{syntax prop_pat}? + @'and') |
      @'notes' (@{syntax thmdef}? @{syntax thmrefs} + @'and')
  "}

  \begin{description}
  
  \item @{command "locale"}~@{text "loc = import + body"} defines a
  new locale @{text loc} as a context consisting of a certain view of
  existing locales (@{text import}) plus some additional elements
  (@{text body}).  Both @{text import} and @{text body} are optional;
  the degenerate form @{command "locale"}~@{text loc} defines an empty
  locale, which may still be useful to collect declarations of facts
  later on.  Type-inference on locale expressions automatically takes
  care of the most general typing that the combined context elements
  may acquire.

  The @{text import} consists of a structured locale expression; see
  \secref{sec:proof-context} above.  Its for clause defines the local
  parameters of the @{text import}.  In addition, locale parameters
  whose instantance is omitted automatically extend the (possibly
  empty) for clause: they are inserted at its beginning.  This means
  that these parameters may be referred to from within the expression
  and also in the subsequent context elements and provides a
  notational convenience for the inheritance of parameters in locale
  declarations.

  The @{text body} consists of context elements.

  \begin{description}

  \item @{element "fixes"}~@{text "x :: \<tau> (mx)"} declares a local
  parameter of type @{text \<tau>} and mixfix annotation @{text mx} (both
  are optional).  The special syntax declaration ``@{text
  "(\<STRUCTURE>)"}'' means that @{text x} may be referenced
  implicitly in this context.

  \item @{element "constrains"}~@{text "x :: \<tau>"} introduces a type
  constraint @{text \<tau>} on the local parameter @{text x}.  This
  element is deprecated.  The type constraint should be introduced in
  the for clause or the relevant @{element "fixes"} element.

  \item @{element "assumes"}~@{text "a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}
  introduces local premises, similar to @{command "assume"} within a
  proof (cf.\ \secref{sec:proof-context}).

  \item @{element "defines"}~@{text "a: x \<equiv> t"} defines a previously
  declared parameter.  This is similar to @{command "def"} within a
  proof (cf.\ \secref{sec:proof-context}), but @{element "defines"}
  takes an equational proposition instead of variable-term pair.  The
  left-hand side of the equation may have additional arguments, e.g.\
  ``@{element "defines"}~@{text "f x\<^sub>1 \<dots> x\<^sub>n \<equiv> t"}''.

  \item @{element "notes"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}
  reconsiders facts within a local context.  Most notably, this may
  include arbitrary declarations in any attribute specifications
  included here, e.g.\ a local @{attribute simp} rule.

  The initial @{text import} specification of a locale expression
  maintains a dynamic relation to the locales being referenced
  (benefiting from any later fact declarations in the obvious manner).

  \end{description}
  
  Note that ``@{text "(\<IS> p\<^sub>1 \<dots> p\<^sub>n)"}'' patterns given
  in the syntax of @{element "assumes"} and @{element "defines"} above
  are illegal in locale definitions.  In the long goal format of
  \secref{sec:goals}, term bindings may be included as expected,
  though.
  
  \medskip Locale specifications are ``closed up'' by
  turning the given text into a predicate definition @{text
  loc_axioms} and deriving the original assumptions as local lemmas
  (modulo local definitions).  The predicate statement covers only the
  newly specified assumptions, omitting the content of included locale
  expressions.  The full cumulative view is only provided on export,
  involving another predicate @{text loc} that refers to the complete
  specification text.
  
  In any case, the predicate arguments are those locale parameters
  that actually occur in the respective piece of text.  Also note that
  these predicates operate at the meta-level in theory, but the locale
  packages attempts to internalize statements according to the
  object-logic setup (e.g.\ replacing @{text \<And>} by @{text \<forall>}, and
  @{text "\<Longrightarrow>"} by @{text "\<longrightarrow>"} in HOL; see also
  \secref{sec:object-logic}).  Separate introduction rules @{text
  loc_axioms.intro} and @{text loc.intro} are provided as well.
  
  \item @{command "print_locale"}~@{text "locale"} prints the
  contents of the named locale.  The command omits @{element "notes"}
  elements by default.  Use @{command "print_locale"}@{text "!"} to
  have them included.

  \item @{command "print_locales"} prints the names of all locales
  of the current theory.

  \item @{method intro_locales} and @{method unfold_locales}
  repeatedly expand all introduction rules of locale predicates of the
  theory.  While @{method intro_locales} only applies the @{text
  loc.intro} introduction rules and therefore does not decend to
  assumptions, @{method unfold_locales} is more aggressive and applies
  @{text loc_axioms.intro} as well.  Both methods are aware of locale
  specifications entailed by the context, both from target statements,
  and from interpretations (see below).  New goals that are entailed
  by the current context are discharged automatically.

  \end{description}
*}


subsection {* Locale interpretations *}

text {*
  Locale expressions may be instantiated, and the instantiated facts
  added to the current context.  This requires a proof of the
  instantiated specification and is called \emph{locale
  interpretation}.  Interpretation is possible in locales @{command
  "sublocale"}, theories (command @{command "interpretation"}) and
  also within a proof body (command @{command "interpret"}).

  \begin{matharray}{rcl}
    @{command_def "interpretation"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def "interpret"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
    @{command_def "sublocale"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def "print_dependencies"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_interps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  @{rail "
    @@{command interpretation} @{syntax locale_expr} equations?
    ;
    @@{command interpret} @{syntax locale_expr} equations?
    ;
    @@{command sublocale} @{syntax nameref} ('<' | '\<subseteq>') @{syntax locale_expr} \\
      equations?
    ;
    @@{command print_dependencies} '!'? @{syntax locale_expr}
    ;
    @@{command print_interps} @{syntax nameref}
    ;

    equations: @'where' (@{syntax thmdecl}? @{syntax prop} + @'and')
  "}

  \begin{description}

  \item @{command "interpretation"}~@{text "expr \<WHERE> eqns"}
  interprets @{text expr} in the theory.  The command generates proof
  obligations for the instantiated specifications (assumes and defines
  elements).  Once these are discharged by the user, instantiated
  facts are added to the theory in a post-processing phase.

  Additional equations, which are unfolded during
  post-processing, may be given after the keyword @{keyword "where"}.
  This is useful for interpreting concepts introduced through
  definitions.  The equations must be proved.

  The command is aware of interpretations already active in the
  theory, but does not simplify the goal automatically.  In order to
  simplify the proof obligations use methods @{method intro_locales}
  or @{method unfold_locales}.  Post-processing is not applied to
  facts of interpretations that are already active.  This avoids
  duplication of interpreted facts, in particular.  Note that, in the
  case of a locale with import, parts of the interpretation may
  already be active.  The command will only process facts for new
  parts.

  Adding facts to locales has the effect of adding interpreted facts
  to the theory for all interpretations as well.  That is,
  interpretations dynamically participate in any facts added to
  locales.  Note that if a theory inherits additional facts for a
  locale through one parent and an interpretation of that locale
  through another parent, the additional facts will not be
  interpreted.

  \item @{command "interpret"}~@{text "expr \<WHERE> eqns"} interprets
  @{text expr} in the proof context and is otherwise similar to
  interpretation in theories.  Note that rewrite rules given to
  @{command "interpret"} after the @{keyword "where"} keyword should be
  explicitly universally quantified.

  \item @{command "sublocale"}~@{text "name \<subseteq> expr \<WHERE>
  eqns"}
  interprets @{text expr} in the locale @{text name}.  A proof that
  the specification of @{text name} implies the specification of
  @{text expr} is required.  As in the localized version of the
  theorem command, the proof is in the context of @{text name}.  After
  the proof obligation has been discharged, the facts of @{text expr}
  become part of locale @{text name} as \emph{derived} context
  elements and are available when the context @{text name} is
  subsequently entered.  Note that, like import, this is dynamic:
  facts added to a locale part of @{text expr} after interpretation
  become also available in @{text name}.

  Only specification fragments of @{text expr} that are not already
  part of @{text name} (be it imported, derived or a derived fragment
  of the import) are considered in this process.  This enables
  circular interpretations provided that no infinite chains are
  generated in the locale hierarchy.

  If interpretations of @{text name} exist in the current theory, the
  command adds interpretations for @{text expr} as well, with the same
  qualifier, although only for fragments of @{text expr} that are not
  interpreted in the theory already.

  Equations given after @{keyword "where"} amend the morphism through
  which @{text expr} is interpreted.  This enables to map definitions
  from the interpreted locales to entities of @{text name}.  This
  feature is experimental.

  \item @{command "print_dependencies"}~@{text "expr"} is useful for
  understanding the effect of an interpretation of @{text "expr"}.  It
  lists all locale instances for which interpretations would be added
  to the current context.  Variant @{command
  "print_dependencies"}@{text "!"} prints all locale instances that
  would be considered for interpretation, and would be interpreted in
  an empty context (that is, without interpretations).

  \item @{command "print_interps"}~@{text "locale"} lists all
  interpretations of @{text "locale"} in the current theory or proof
  context, including those due to a combination of a @{command
  "interpretation"} or @{command "interpret"} and one or several
  @{command "sublocale"} declarations.

  \end{description}

  \begin{warn}
    Since attributes are applied to interpreted theorems,
    interpretation may modify the context of common proof tools, e.g.\
    the Simplifier or Classical Reasoner.  As the behavior of such
    tools is \emph{not} stable under interpretation morphisms, manual
    declarations might have to be added to the target context of the
    interpretation to revert such declarations.
  \end{warn}

  \begin{warn}
    An interpretation in a theory or proof context may subsume previous
    interpretations.  This happens if the same specification fragment
    is interpreted twice and the instantiation of the second
    interpretation is more general than the interpretation of the
    first.  The locale package does not attempt to remove subsumed
    interpretations.
  \end{warn}
*}


section {* Classes \label{sec:class} *}

text {*
  A class is a particular locale with \emph{exactly one} type variable
  @{text \<alpha>}.  Beyond the underlying locale, a corresponding type class
  is established which is interpreted logically as axiomatic type
  class \cite{Wenzel:1997:TPHOL} whose logical content are the
  assumptions of the locale.  Thus, classes provide the full
  generality of locales combined with the commodity of type classes
  (notably type-inference).  See \cite{isabelle-classes} for a short
  tutorial.

  \begin{matharray}{rcl}
    @{command_def "class"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "instantiation"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "instance"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command "instance"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def "subclass"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_classes"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "class_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{method_def intro_classes} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{command class} class_spec @'begin'?
    ;
    class_spec: @{syntax name} '='
      ((@{syntax nameref} '+' (@{syntax context_elem}+)) |
        @{syntax nameref} | (@{syntax context_elem}+))      
    ;
    @@{command instantiation} (@{syntax nameref} + @'and') '::' @{syntax arity} @'begin'
    ;
    @@{command instance} (() | (@{syntax nameref} + @'and') '::' @{syntax arity} |
      @{syntax nameref} ('<' | '\<subseteq>') @{syntax nameref} )
    ;
    @@{command subclass} @{syntax target}? @{syntax nameref}
  "}

  \begin{description}

  \item @{command "class"}~@{text "c = superclasses + body"} defines
  a new class @{text c}, inheriting from @{text superclasses}.  This
  introduces a locale @{text c} with import of all locales @{text
  superclasses}.

  Any @{element "fixes"} in @{text body} are lifted to the global
  theory level (\emph{class operations} @{text "f\<^sub>1, \<dots>,
  f\<^sub>n"} of class @{text c}), mapping the local type parameter
  @{text \<alpha>} to a schematic type variable @{text "?\<alpha> :: c"}.

  Likewise, @{element "assumes"} in @{text body} are also lifted,
  mapping each local parameter @{text "f :: \<tau>[\<alpha>]"} to its
  corresponding global constant @{text "f :: \<tau>[?\<alpha> :: c]"}.  The
  corresponding introduction rule is provided as @{text
  c_class_axioms.intro}.  This rule should be rarely needed directly
  --- the @{method intro_classes} method takes care of the details of
  class membership proofs.

  \item @{command "instantiation"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n)s
  \<BEGIN>"} opens a theory target (cf.\ \secref{sec:target}) which
  allows to specify class operations @{text "f\<^sub>1, \<dots>, f\<^sub>n"} corresponding
  to sort @{text s} at the particular type instance @{text "(\<alpha>\<^sub>1 :: s\<^sub>1,
  \<dots>, \<alpha>\<^sub>n :: s\<^sub>n) t"}.  A plain @{command "instance"} command in the
  target body poses a goal stating these type arities.  The target is
  concluded by an @{command_ref (local) "end"} command.

  Note that a list of simultaneous type constructors may be given;
  this corresponds nicely to mutually recursive type definitions, e.g.\
  in Isabelle/HOL.

  \item @{command "instance"} in an instantiation target body sets
  up a goal stating the type arities claimed at the opening @{command
  "instantiation"}.  The proof would usually proceed by @{method
  intro_classes}, and then establish the characteristic theorems of
  the type classes involved.  After finishing the proof, the
  background theory will be augmented by the proven type arities.

  On the theory level, @{command "instance"}~@{text "t :: (s\<^sub>1, \<dots>,
  s\<^sub>n)s"} provides a convenient way to instantiate a type class with no
  need to specify operations: one can continue with the
  instantiation proof immediately.

  \item @{command "subclass"}~@{text c} in a class context for class
  @{text d} sets up a goal stating that class @{text c} is logically
  contained in class @{text d}.  After finishing the proof, class
  @{text d} is proven to be subclass @{text c} and the locale @{text
  c} is interpreted into @{text d} simultaneously.

  A weakend form of this is available through a further variant of
  @{command instance}:  @{command instance}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} opens
  a proof that class @{text "c\<^isub>2"} implies @{text "c\<^isub>1"} without reference
  to the underlying locales;  this is useful if the properties to prove
  the logical connection are not sufficent on the locale level but on
  the theory level.

  \item @{command "print_classes"} prints all classes in the current
  theory.

  \item @{command "class_deps"} visualizes all classes and their
  subclass relations as a Hasse diagram.

  \item @{method intro_classes} repeatedly expands all class
  introduction rules of this theory.  Note that this method usually
  needs not be named explicitly, as it is already included in the
  default proof step (e.g.\ of @{command "proof"}).  In particular,
  instantiation of trivial (syntactic) classes may be performed by a
  single ``@{command ".."}'' proof step.

  \end{description}
*}


subsection {* The class target *}

text {*
  %FIXME check

  A named context may refer to a locale (cf.\ \secref{sec:target}).
  If this locale is also a class @{text c}, apart from the common
  locale target behaviour the following happens.

  \begin{itemize}

  \item Local constant declarations @{text "g[\<alpha>]"} referring to the
  local type parameter @{text \<alpha>} and local parameters @{text "f[\<alpha>]"}
  are accompanied by theory-level constants @{text "g[?\<alpha> :: c]"}
  referring to theory-level class operations @{text "f[?\<alpha> :: c]"}.

  \item Local theorem bindings are lifted as are assumptions.

  \item Local syntax refers to local operations @{text "g[\<alpha>]"} and
  global operations @{text "g[?\<alpha> :: c]"} uniformly.  Type inference
  resolves ambiguities.  In rare cases, manual type annotations are
  needed.
  
  \end{itemize}
*}


subsection {* Co-regularity of type classes and arities *}

text {* The class relation together with the collection of
  type-constructor arities must obey the principle of
  \emph{co-regularity} as defined below.

  \medskip For the subsequent formulation of co-regularity we assume
  that the class relation is closed by transitivity and reflexivity.
  Moreover the collection of arities @{text "t :: (\<^vec>s)c"} is
  completed such that @{text "t :: (\<^vec>s)c"} and @{text "c \<subseteq> c'"}
  implies @{text "t :: (\<^vec>s)c'"} for all such declarations.

  Treating sorts as finite sets of classes (meaning the intersection),
  the class relation @{text "c\<^sub>1 \<subseteq> c\<^sub>2"} is extended to sorts as
  follows:
  \[
    @{text "s\<^sub>1 \<subseteq> s\<^sub>2 \<equiv> \<forall>c\<^sub>2 \<in> s\<^sub>2. \<exists>c\<^sub>1 \<in> s\<^sub>1. c\<^sub>1 \<subseteq> c\<^sub>2"}
  \]

  This relation on sorts is further extended to tuples of sorts (of
  the same length) in the component-wise way.

  \smallskip Co-regularity of the class relation together with the
  arities relation means:
  \[
    @{text "t :: (\<^vec>s\<^sub>1)c\<^sub>1 \<Longrightarrow> t :: (\<^vec>s\<^sub>2)c\<^sub>2 \<Longrightarrow> c\<^sub>1 \<subseteq> c\<^sub>2 \<Longrightarrow> \<^vec>s\<^sub>1 \<subseteq> \<^vec>s\<^sub>2"}
  \]
  \noindent for all such arities.  In other words, whenever the result
  classes of some type-constructor arities are related, then the
  argument sorts need to be related in the same way.

  \medskip Co-regularity is a very fundamental property of the
  order-sorted algebra of types.  For example, it entails principle
  types and most general unifiers, e.g.\ see \cite{nipkow-prehofer}.
*}


section {* Unrestricted overloading *}

text {*
  Isabelle/Pure's definitional schemes support certain forms of
  overloading (see \secref{sec:consts}).  Overloading means that a
  constant being declared as @{text "c :: \<alpha> decl"} may be
  defined separately on type instances
  @{text "c :: (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t decl"}
  for each type constructor @{text t}.  At most occassions
  overloading will be used in a Haskell-like fashion together with
  type classes by means of @{command "instantiation"} (see
  \secref{sec:class}).  Sometimes low-level overloading is desirable.
  The @{command "overloading"} target provides a convenient view for
  end-users.

  \begin{matharray}{rcl}
    @{command_def "overloading"} & : & @{text "theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail "
    @@{command overloading} ( spec + ) @'begin'
    ;
    spec: @{syntax name} ( '==' | '\<equiv>' ) @{syntax term} ( '(' @'unchecked' ')' )?
  "}

  \begin{description}

  \item @{command "overloading"}~@{text "x\<^sub>1 \<equiv> c\<^sub>1 :: \<tau>\<^sub>1 \<AND> \<dots> x\<^sub>n \<equiv> c\<^sub>n :: \<tau>\<^sub>n \<BEGIN>"}
  opens a theory target (cf.\ \secref{sec:target}) which allows to
  specify constants with overloaded definitions.  These are identified
  by an explicitly given mapping from variable names @{text "x\<^sub>i"} to
  constants @{text "c\<^sub>i"} at particular type instances.  The
  definitions themselves are established using common specification
  tools, using the names @{text "x\<^sub>i"} as reference to the
  corresponding constants.  The target is concluded by @{command
  (local) "end"}.

  A @{text "(unchecked)"} option disables global dependency checks for
  the corresponding definition, which is occasionally useful for
  exotic overloading (see \secref{sec:consts} for a precise description).
  It is at the discretion of the user to avoid
  malformed theory specifications!

  \end{description}
*}


section {* Incorporating ML code \label{sec:ML} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "use"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML_prf"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "ML_val"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "ML_command"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "setup"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "local_setup"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "attribute_setup"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
    @@{command use} @{syntax name}
    ;
    (@@{command ML} | @@{command ML_prf} | @@{command ML_val} |
      @@{command ML_command} | @@{command setup} | @@{command local_setup}) @{syntax text}
    ;
    @@{command attribute_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
  "}

  \begin{description}

  \item @{command "use"}~@{text "file"} reads and executes ML
  commands from @{text "file"}.  The current theory context is passed
  down to the ML toplevel and may be modified, using @{ML
  "Context.>>"} or derived ML commands.  The file name is checked with
  the @{keyword_ref "uses"} dependency declaration given in the theory
  header (see also \secref{sec:begin-thy}).

  Top-level ML bindings are stored within the (global or local) theory
  context.
  
  \item @{command "ML"}~@{text "text"} is similar to @{command "use"},
  but executes ML commands directly from the given @{text "text"}.
  Top-level ML bindings are stored within the (global or local) theory
  context.

  \item @{command "ML_prf"} is analogous to @{command "ML"} but works
  within a proof context.

  Top-level ML bindings are stored within the proof context in a
  purely sequential fashion, disregarding the nested proof structure.
  ML bindings introduced by @{command "ML_prf"} are discarded at the
  end of the proof.

  \item @{command "ML_val"} and @{command "ML_command"} are diagnostic
  versions of @{command "ML"}, which means that the context may not be
  updated.  @{command "ML_val"} echos the bindings produced at the ML
  toplevel, but @{command "ML_command"} is silent.
  
  \item @{command "setup"}~@{text "text"} changes the current theory
  context by applying @{text "text"}, which refers to an ML expression
  of type @{ML_type "theory -> theory"}.  This enables to initialize
  any object-logic specific tools and packages written in ML, for
  example.

  \item @{command "local_setup"} is similar to @{command "setup"} for
  a local theory context, and an ML expression of type @{ML_type
  "local_theory -> local_theory"}.  This allows to
  invoke local theory specification packages without going through
  concrete outer syntax, for example.

  \item @{command "attribute_setup"}~@{text "name = text description"}
  defines an attribute in the current theory.  The given @{text
  "text"} has to be an ML expression of type
  @{ML_type "attribute context_parser"}, cf.\ basic parsers defined in
  structure @{ML_struct Args} and @{ML_struct Attrib}.

  In principle, attributes can operate both on a given theorem and the
  implicit context, although in practice only one is modified and the
  other serves as parameter.  Here are examples for these two cases:

  \end{description}
*}

  attribute_setup my_rule = {*
    Attrib.thms >> (fn ths =>
      Thm.rule_attribute
        (fn context: Context.generic => fn th: thm =>
          let val th' = th OF ths
          in th' end)) *}

  attribute_setup my_declaration = {*
    Attrib.thms >> (fn ths =>
      Thm.declaration_attribute
        (fn th: thm => fn context: Context.generic =>
          let val context' = context
          in context' end)) *}


section {* Primitive specification elements *}

subsection {* Type classes and sorts \label{sec:classes} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "classes"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "classrel"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
    @{command_def "default_sort"} & : & @{text "local_theory \<rightarrow> local_theory"}
  \end{matharray}

  @{rail "
    @@{command classes} (@{syntax classdecl} +)
    ;
    @@{command classrel} (@{syntax nameref} ('<' | '\<subseteq>') @{syntax nameref} + @'and')
    ;
    @@{command default_sort} @{syntax sort}
  "}

  \begin{description}

  \item @{command "classes"}~@{text "c \<subseteq> c\<^sub>1, \<dots>, c\<^sub>n"} declares class
  @{text c} to be a subclass of existing classes @{text "c\<^sub>1, \<dots>, c\<^sub>n"}.
  Isabelle implicitly maintains the transitive closure of the class
  hierarchy.  Cyclic class structures are not permitted.

  \item @{command "classrel"}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} states subclass
  relations between existing classes @{text "c\<^sub>1"} and @{text "c\<^sub>2"}.
  This is done axiomatically!  The @{command_ref "subclass"} and
  @{command_ref "instance"} commands (see \secref{sec:class}) provide
  a way to introduce proven class relations.

  \item @{command "default_sort"}~@{text s} makes sort @{text s} the
  new default sort for any type variable that is given explicitly in
  the text, but lacks a sort constraint (wrt.\ the current context).
  Type variables generated by type inference are not affected.

  Usually the default sort is only changed when defining a new
  object-logic.  For example, the default sort in Isabelle/HOL is
  @{class type}, the class of all HOL types.

  When merging theories, the default sorts of the parents are
  logically intersected, i.e.\ the representations as lists of classes
  are joined.

  \end{description}
*}


subsection {* Types and type abbreviations \label{sec:types-pure} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "type_synonym"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "typedecl"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "arities"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
  \end{matharray}

  @{rail "
    @@{command type_synonym} (@{syntax typespec} '=' @{syntax type} @{syntax mixfix}?)
    ;
    @@{command typedecl} @{syntax typespec} @{syntax mixfix}?
    ;
    @@{command arities} (@{syntax nameref} '::' @{syntax arity} +)
  "}

  \begin{description}

  \item @{command "type_synonym"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>"}
  introduces a \emph{type synonym} @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} for the
  existing type @{text "\<tau>"}.  Unlike actual type definitions, as are
  available in Isabelle/HOL for example, type synonyms are merely
  syntactic abbreviations without any logical significance.
  Internally, type synonyms are fully expanded.
  
  \item @{command "typedecl"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} declares a new
  type constructor @{text t}.  If the object-logic defines a base sort
  @{text s}, then the constructor is declared to operate on that, via
  the axiomatic specification @{command arities}~@{text "t :: (s, \<dots>,
  s)s"}.

  \item @{command "arities"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n)s"} augments
  Isabelle's order-sorted signature of types by new type constructor
  arities.  This is done axiomatically!  The @{command_ref "instantiation"}
  target (see \secref{sec:class}) provides a way to introduce
  proven type arities.

  \end{description}
*}


subsection {* Constants and definitions \label{sec:consts} *}

text {*
  Definitions essentially express abbreviations within the logic.  The
  simplest form of a definition is @{text "c :: \<sigma> \<equiv> t"}, where @{text
  c} is a newly declared constant.  Isabelle also allows derived forms
  where the arguments of @{text c} appear on the left, abbreviating a
  prefix of @{text \<lambda>}-abstractions, e.g.\ @{text "c \<equiv> \<lambda>x y. t"} may be
  written more conveniently as @{text "c x y \<equiv> t"}.  Moreover,
  definitions may be weakened by adding arbitrary pre-conditions:
  @{text "A \<Longrightarrow> c x y \<equiv> t"}.

  \medskip The built-in well-formedness conditions for definitional
  specifications are:

  \begin{itemize}

  \item Arguments (on the left-hand side) must be distinct variables.

  \item All variables on the right-hand side must also appear on the
  left-hand side.

  \item All type variables on the right-hand side must also appear on
  the left-hand side; this prohibits @{text "0 :: nat \<equiv> length ([] ::
  \<alpha> list)"} for example.

  \item The definition must not be recursive.  Most object-logics
  provide definitional principles that can be used to express
  recursion safely.

  \end{itemize}

  The right-hand side of overloaded definitions may mention overloaded constants
  recursively at type instances corresponding to the immediate
  argument types @{text "\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n"}.  Incomplete
  specification patterns impose global constraints on all occurrences,
  e.g.\ @{text "d :: \<alpha> \<times> \<alpha>"} on the left-hand side means that all
  corresponding occurrences on some right-hand side need to be an
  instance of this, general @{text "d :: \<alpha> \<times> \<beta>"} will be disallowed.

  \begin{matharray}{rcl}
    @{command_def "consts"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "defs"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
    @@{command consts} ((@{syntax name} '::' @{syntax type} @{syntax mixfix}?) +)
    ;
    @@{command defs} opt? (@{syntax axmdecl} @{syntax prop} +)
    ;
    opt: '(' @'unchecked'? @'overloaded'? ')'
  "}

  \begin{description}

  \item @{command "consts"}~@{text "c :: \<sigma>"} declares constant @{text
  c} to have any instance of type scheme @{text \<sigma>}.  The optional
  mixfix annotations may attach concrete syntax to the constants
  declared.
  
  \item @{command "defs"}~@{text "name: eqn"} introduces @{text eqn}
  as a definitional axiom for some existing constant.
  
  The @{text "(unchecked)"} option disables global dependency checks
  for this definition, which is occasionally useful for exotic
  overloading.  It is at the discretion of the user to avoid malformed
  theory specifications!
  
  The @{text "(overloaded)"} option declares definitions to be
  potentially overloaded.  Unless this option is given, a warning
  message would be issued for any definitional equation with a more
  special type than that of the corresponding constant declaration.
  
  \end{description}
*}


section {* Axioms and theorems \label{sec:axms-thms} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axioms"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
    @{command_def "lemmas"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "theorems"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail "
    @@{command axioms} (@{syntax axmdecl} @{syntax prop} +)
    ;
    (@@{command lemmas} | @@{command theorems}) @{syntax target}? \\
      (@{syntax thmdef}? @{syntax thmrefs} + @'and')
      (@'for' (@{syntax vars} + @'and'))?
  "}

  \begin{description}
  
  \item @{command "axioms"}~@{text "a: \<phi>"} introduces arbitrary
  statements as axioms of the meta-logic.  In fact, axioms are
  ``axiomatic theorems'', and may be referred later just as any other
  theorem.
  
  Axioms are usually only introduced when declaring new logical
  systems.  Everyday work is typically done the hard way, with proper
  definitions and proven theorems.
  
  \item @{command "lemmas"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}~@{keyword_def
  "for"}~@{text "x\<^sub>1 \<dots> x\<^sub>m"} evaluates given facts (with attributes) in
  the current context, which may be augmented by local variables.
  Results are standardized before being stored, i.e.\ schematic
  variables are renamed to enforce index @{text "0"} uniformly.

  \item @{command "theorems"} is the same as @{command "lemmas"}, but
  marks the result as a different kind of facts.

  \end{description}
*}


section {* Oracles *}

text {* Oracles allow Isabelle to take advantage of external reasoners
  such as arithmetic decision procedures, model checkers, fast
  tautology checkers or computer algebra systems.  Invoked as an
  oracle, an external reasoner can create arbitrary Isabelle theorems.

  It is the responsibility of the user to ensure that the external
  reasoner is as trustworthy as the application requires.  Another
  typical source of errors is the linkup between Isabelle and the
  external tool, not just its concrete implementation, but also the
  required translation between two different logical environments.

  Isabelle merely guarantees well-formedness of the propositions being
  asserted, and records within the internal derivation object how
  presumed theorems depend on unproven suppositions.

  \begin{matharray}{rcll}
    @{command_def "oracle"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
  \end{matharray}

  @{rail "
    @@{command oracle} @{syntax name} '=' @{syntax text}
  "}

  \begin{description}

  \item @{command "oracle"}~@{text "name = text"} turns the given ML
  expression @{text "text"} of type @{ML_text "'a -> cterm"} into an
  ML function of type @{ML_text "'a -> thm"}, which is bound to the
  global identifier @{ML_text name}.  This acts like an infinitary
  specification of axioms!  Invoking the oracle only works within the
  scope of the resulting theory.

  \end{description}

  See @{file "~~/src/HOL/ex/Iff_Oracle.thy"} for a worked example of
  defining a new primitive rule as oracle, and turning it into a proof
  method.
*}


section {* Name spaces *}

text {*
  \begin{matharray}{rcl}
    @{command_def "hide_class"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_type"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_const"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_fact"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
    ( @{command hide_class} | @{command hide_type} |
      @{command hide_const} | @{command hide_fact} ) ('(' @'open' ')')? (@{syntax nameref} + )
  "}

  Isabelle organizes any kind of name declarations (of types,
  constants, theorems etc.) by separate hierarchically structured name
  spaces.  Normally the user does not have to control the behavior of
  name spaces by hand, yet the following commands provide some way to
  do so.

  \begin{description}

  \item @{command "hide_class"}~@{text names} fully removes class
  declarations from a given name space; with the @{text "(open)"}
  option, only the base name is hidden.

  Note that hiding name space accesses has no impact on logical
  declarations --- they remain valid internally.  Entities that are no
  longer accessible to the user are printed with the special qualifier
  ``@{text "??"}'' prefixed to the full internal name.

  \item @{command "hide_type"}, @{command "hide_const"}, and @{command
  "hide_fact"} are similar to @{command "hide_class"}, but hide types,
  constants, and facts, respectively.
  
  \end{description}
*}

end

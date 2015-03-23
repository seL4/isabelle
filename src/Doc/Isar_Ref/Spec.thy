theory Spec
imports Base Main "~~/src/Tools/Permanent_Interpretation"
begin

chapter \<open>Specifications\<close>

text \<open>The Isabelle/Isar theory format integrates specifications and proofs,
  with support for interactive development by continuous document editing.
  There is a separate document preparation system (see
  \chref{ch:document-prep}), for typesetting formal developments together
  with informal text. The resulting hyper-linked PDF documents can be used
  both for WWW presentation and printed copies.

  The Isar proof language (see \chref{ch:proofs}) is embedded into the
  theory language as a proper sub-language.  Proof mode is entered by
  stating some @{command theorem} or @{command lemma} at the theory
  level, and left again with the final conclusion (e.g.\ via @{command
  qed}).
\<close>


section \<open>Defining theories \label{sec:begin-thy}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "theory"} & : & @{text "toplevel \<rightarrow> theory"} \\
    @{command_def (global) "end"} & : & @{text "theory \<rightarrow> toplevel"} \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory files, which consist of an
  outermost sequence of definition--statement--proof elements. Some
  definitions are self-sufficient (e.g.\ @{command fun} in Isabelle/HOL),
  with foundational proofs performed internally. Other definitions require
  an explicit proof as justification (e.g.\ @{command function} and
  @{command termination} in Isabelle/HOL). Plain statements like @{command
  theorem} or @{command lemma} are merely a special case of that, defining a
  theorem from a given proposition and its proof.

  The theory body may be sub-structured by means of \emph{local theory
  targets}, such as @{command "locale"} and @{command "class"}. It is also
  possible to use @{command context}~@{keyword "begin"}~\dots~@{command end}
  blocks to delimited a local theory context: a \emph{named context} to
  augment a locale or class specification, or an \emph{unnamed context} to
  refer to local parameters and assumptions that are discharged later. See
  \secref{sec:target} for more details.

  \medskip A theory is commenced by the @{command "theory"} command, which
  indicates imports of previous theories, according to an acyclic
  foundational order. Before the initial @{command "theory"} command, there
  may be optional document header material (like @{command section} or
  @{command text}, see \secref{sec:markup}). The document header is outside
  of the formal theory context, though.

  A theory is concluded by a final @{command (global) "end"} command, one
  that does not belong to a local theory target. No further commands may
  follow such a global @{command (global) "end"}.

  @{rail \<open>
    @@{command theory} @{syntax name} imports? keywords? \<newline> @'begin'
    ;
    imports: @'imports' (@{syntax name} +)
    ;
    keywords: @'keywords' (keyword_decls + @'and')
    ;
    keyword_decls: (@{syntax string} +)
      ('::' @{syntax name} @{syntax tags})? ('==' @{syntax name})?
  \<close>}

  \begin{description}

  \item @{command "theory"}~@{text "A \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>"}
  starts a new theory @{text A} based on the merge of existing
  theories @{text "B\<^sub>1 \<dots> B\<^sub>n"}.  Due to the possibility to import more
  than one ancestor, the resulting theory structure of an Isabelle
  session forms a directed acyclic graph (DAG).  Isabelle takes care
  that sources contributing to the development graph are always
  up-to-date: changed files are automatically rechecked whenever a
  theory header specification is processed.

  Empty imports are only allowed in the bootstrap process of the special
  theory @{theory Pure}, which is the start of any other formal development
  based on Isabelle. Regular user theories usually refer to some more
  complex entry point, such as theory @{theory Main} in Isabelle/HOL.

  The optional @{keyword_def "keywords"} specification declares outer
  syntax (\chref{ch:outer-syntax}) that is introduced in this theory
  later on (rare in end-user applications).  Both minor keywords and
  major keywords of the Isar command language need to be specified, in
  order to make parsing of proof documents work properly.  Command
  keywords need to be classified according to their structural role in
  the formal text.  Examples may be seen in Isabelle/HOL sources
  itself, such as @{keyword "keywords"}~@{verbatim \<open>"typedef"\<close>}
  @{text ":: thy_goal"} or @{keyword "keywords"}~@{verbatim
  \<open>"datatype"\<close>} @{text ":: thy_decl"} for theory-level declarations
  with and without proof, respectively.  Additional @{syntax tags}
  provide defaults for document preparation (\secref{sec:tags}).

  It is possible to specify an alternative completion via @{verbatim
  "=="}~@{text "text"}, while the default is the corresponding keyword name.
  
  \item @{command (global) "end"} concludes the current theory
  definition.  Note that some other commands, e.g.\ local theory
  targets @{command locale} or @{command class} may involve a
  @{keyword "begin"} that needs to be matched by @{command (local)
  "end"}, according to the usual rules for nested blocks.

  \end{description}
\<close>


section \<open>Local theory targets \label{sec:target}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "context"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def (local) "end"} & : & @{text "local_theory \<rightarrow> theory"} \\
  \end{matharray}

  A local theory target is a specification context that is managed
  separately within the enclosing theory. Contexts may introduce parameters
  (fixed variables) and assumptions (hypotheses). Definitions and theorems
  depending on the context may be added incrementally later on.

  \emph{Named contexts} refer to locales (cf.\ \secref{sec:locale}) or
  type classes (cf.\ \secref{sec:class}); the name ``@{text "-"}''
  signifies the global theory context.

  \emph{Unnamed contexts} may introduce additional parameters and
  assumptions, and results produced in the context are generalized
  accordingly.  Such auxiliary contexts may be nested within other
  targets, like @{command "locale"}, @{command "class"}, @{command
  "instantiation"}, @{command "overloading"}.

  @{rail \<open>
    @@{command context} @{syntax nameref} @'begin'
    ;
    @@{command context} @{syntax_ref "includes"}? (@{syntax context_elem} * ) @'begin'
    ;
    @{syntax_def target}: '(' @'in' @{syntax nameref} ')'
  \<close>}

  \begin{description}
  
  \item @{command "context"}~@{text "c \<BEGIN>"} opens a named
  context, by recommencing an existing locale or class @{text c}.
  Note that locale and class definitions allow to include the
  @{keyword "begin"} keyword as well, in order to continue the local
  theory immediately after the initial specification.

  \item @{command "context"}~@{text "bundles elements \<BEGIN>"} opens
  an unnamed context, by extending the enclosing global or local
  theory target by the given declaration bundles (\secref{sec:bundle})
  and context elements (@{text "\<FIXES>"}, @{text "\<ASSUMES>"}
  etc.).  This means any results stemming from definitions and proofs
  in the extended context will be exported into the enclosing target
  by lifting over extra parameters and premises.
  
  \item @{command (local) "end"} concludes the current local theory,
  according to the nesting of contexts.  Note that a global @{command
  (global) "end"} has a different meaning: it concludes the theory
  itself (\secref{sec:begin-thy}).
  
  \item @{text "("}@{keyword_def "in"}~@{text "c)"} given after any local
  theory command specifies an immediate target, e.g.\ ``@{command
  "definition"}~@{text "(\<IN> c)"}'' or ``@{command "theorem"}~@{text
  "(\<IN> c)"}''. This works both in a local or global theory context; the
  current target context will be suspended for this command only. Note that
  ``@{text "(\<IN> -)"}'' will always produce a global result independently
  of the current target context.

  \end{description}

  Any specification element that operates on @{text local_theory} according
  to this manual implicitly allows the above target syntax @{text
  "("}@{keyword "in"}~@{text "c)"}, but individual syntax diagrams omit that
  aspect for clarity.

  \medskip The exact meaning of results produced within a local theory
  context depends on the underlying target infrastructure (locale, type
  class etc.). The general idea is as follows, considering a context named
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
\<close>


section \<open>Bundled declarations \label{sec:bundle}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "bundle"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_bundles"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow> "} \\
    @{command_def "include"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
    @{command_def "including"} & : & @{text "proof(prove) \<rightarrow> proof(prove)"} \\
    @{keyword_def "includes"} & : & syntax \\
  \end{matharray}

  The outer syntax of fact expressions (\secref{sec:syn-att}) involves
  theorems and attributes, which are evaluated in the context and
  applied to it.  Attributes may declare theorems to the context, as
  in @{text "this_rule [intro] that_rule [elim]"} for example.
  Configuration options (\secref{sec:config}) are special declaration
  attributes that operate on the context without a theorem, as in
  @{text "[[show_types = false]]"} for example.

  Expressions of this form may be defined as \emph{bundled
  declarations} in the context, and included in other situations later
  on.  Including declaration bundles augments a local context casually
  without logical dependencies, which is in contrast to locales and
  locale interpretation (\secref{sec:locale}).

  @{rail \<open>
    @@{command bundle} @{syntax name} '=' @{syntax thmrefs} @{syntax for_fixes}
    ;
    (@@{command include} | @@{command including}) (@{syntax nameref}+)
    ;
    @{syntax_def "includes"}: @'includes' (@{syntax nameref}+)
  \<close>}

  \begin{description}

  \item @{command bundle}~@{text "b = decls"} defines a bundle of
  declarations in the current context.  The RHS is similar to the one
  of the @{command declare} command.  Bundles defined in local theory
  targets are subject to transformations via morphisms, when moved
  into different application contexts; this works analogously to any
  other local theory specification.

  \item @{command print_bundles} prints the named bundles that are
  available in the current context.

  \item @{command include}~@{text "b\<^sub>1 \<dots> b\<^sub>n"} includes the declarations
  from the given bundles into the current proof body context.  This is
  analogous to @{command "note"} (\secref{sec:proof-facts}) with the
  expanded bundles.

  \item @{command including} is similar to @{command include}, but
  works in proof refinement (backward mode).  This is analogous to
  @{command "using"} (\secref{sec:proof-facts}) with the expanded
  bundles.

  \item @{keyword "includes"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"} is similar to
  @{command include}, but works in situations where a specification
  context is constructed, notably for @{command context} and long
  statements of @{command theorem} etc.

  \end{description}

  Here is an artificial example of bundling various configuration
  options:\<close>

bundle trace = [[simp_trace, linarith_trace, metis_trace, smt_trace]]

lemma "x = x"
  including trace by metis


section \<open>Term definitions \label{sec:term-definitions}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "definition"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def "defn"} & : & @{text attribute} \\
    @{command_def "print_defn_rules"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow> "} \\
    @{command_def "abbreviation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_abbrevs"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow> "} \\
  \end{matharray}

  Term definitions may either happen within the logic (as equational axioms
  of a certain form, see also see \secref{sec:consts}), or outside of it as
  rewrite system on abstract syntax. The second form is called
  ``abbreviation''.

  @{rail \<open>
    @@{command definition} (decl @'where')? @{syntax thmdecl}? @{syntax prop}
    ;
    @@{command abbreviation} @{syntax mode}? \<newline>
      (decl @'where')? @{syntax prop}
    ;

    decl: @{syntax name} ('::' @{syntax type})? @{syntax mixfix}?
  \<close>}

  \begin{description}
  
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

  \item @{command "print_defn_rules"} prints the definitional rewrite rules
  declared via @{attribute defn} in the current context.

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
\<close>


section \<open>Axiomatizations \label{sec:axiomatizations}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
  \end{matharray}

  @{rail \<open>
    @@{command axiomatization} @{syntax "fixes"}? (@'where' specs)?
    ;
    specs: (@{syntax thmdecl}? @{syntax props} + @'and')
  \<close>}

  \begin{description}

  \item @{command "axiomatization"}~@{text "c\<^sub>1 \<dots> c\<^sub>m \<WHERE> \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}
  introduces several constants simultaneously and states axiomatic
  properties for these. The constants are marked as being specified once and
  for all, which prevents additional specifications for the same constants
  later on, but it is always possible do emit axiomatizations without
  referring to particular constants. Note that lack of precise dependency
  tracking of axiomatizations may disrupt the well-formedness of an
  otherwise definitional theory.

  Axiomatization is restricted to a global theory context: support for local
  theory targets \secref{sec:target} would introduce an extra dimension of
  uncertainty what the written specifications really are, and make it
  infeasible to argue why they are correct.

  Axiomatic specifications are required when declaring a new logical system
  within Isabelle/Pure, but in an application environment like Isabelle/HOL
  the user normally stays within definitional mechanisms provided by the
  logic and its libraries.

  \end{description}
\<close>


section \<open>Generic declarations\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "declaration"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "syntax_declaration"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "declare"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  Arbitrary operations on the background context may be wrapped-up as
  generic declaration elements.  Since the underlying concept of local
  theories may be subject to later re-interpretation, there is an
  additional dependency on a morphism that tells the difference of the
  original declaration context wrt.\ the application context
  encountered later on.  A fact declaration is an important special
  case: it consists of a theorem which is applied to the context by
  means of an attribute.

  @{rail \<open>
    (@@{command declaration} | @@{command syntax_declaration})
      ('(' @'pervasive' ')')? \<newline> @{syntax text}
    ;
    @@{command declare} (@{syntax thmrefs} + @'and')
  \<close>}

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
  \secref{sec:theorems}), so @{command "declare"} only has the effect
  of applying attributes as included in the theorem specification.

  \end{description}
\<close>


section \<open>Locales \label{sec:locale}\<close>

text \<open>
  A locale is a functor that maps parameters (including implicit type
  parameters) and a specification to a list of declarations.  The
  syntax of locales is modeled after the Isar proof context commands
  (cf.\ \secref{sec:proof-context}).

  Locale hierarchies are supported by maintaining a graph of
  dependencies between locale instances in the global theory.
  Dependencies may be introduced through import (where a locale is
  defined as sublocale of the imported instances) or by proving that
  an existing locale is a sublocale of one or several locale
  instances.

  A locale may be opened with the purpose of appending to its list of
  declarations (cf.\ \secref{sec:target}).  When opening a locale
  declarations from all dependencies are collected and are presented
  as a local theory.  In this process, which is called \emph{roundup},
  redundant locale instances are omitted.  A locale instance is
  redundant if it is subsumed by an instance encountered earlier.  A
  more detailed description of this process is available elsewhere
  @{cite Ballarin2014}.
\<close>


subsection \<open>Locale expressions \label{sec:locale-expr}\<close>

text \<open>
  A \emph{locale expression} denotes a context composed of instances
  of existing locales.  The context consists of the declaration
  elements from the locale instances.  Redundant locale instances are
  omitted according to roundup.

  @{rail \<open>
    @{syntax_def locale_expr}: (instance + '+') @{syntax for_fixes}
    ;
    instance: (qualifier ':')? @{syntax nameref} (pos_insts | named_insts)
    ;
    qualifier: @{syntax name} ('?' | '!')?
    ;
    pos_insts: ('_' | @{syntax term})*
    ;
    named_insts: @'where' (@{syntax name} '=' @{syntax term} + @'and')
  \<close>}

  A locale instance consists of a reference to a locale and either
  positional or named parameter instantiations.  Identical
  instantiations (that is, those that instantiate a parameter by itself)
  may be omitted.  The notation `@{text "_"}' enables to omit the
  instantiation for a parameter inside a positional instantiation.

  Terms in instantiations are from the context the locale expressions
  is declared in.  Local names may be added to this context with the
  optional @{keyword "for"} clause.  This is useful for shadowing names
  bound in outer contexts, and for declaring syntax.  In addition,
  syntax declarations from one instance are effective when parsing
  subsequent instances of the same expression.

  Instances have an optional qualifier which applies to names in
  declarations.  Names include local definitions and theorem names.
  If present, the qualifier itself is either optional
  (``\texttt{?}''), which means that it may be omitted on input of the
  qualified name, or mandatory (``\texttt{!}'').  If neither
  ``\texttt{?}'' nor ``\texttt{!}'' are present, the command's default
  is used.  For @{command "interpretation"} and @{command "interpret"}
  the default is ``mandatory'', for @{command "locale"} and @{command
  "sublocale"} the default is ``optional''.  Qualifiers play no role
  in determining whether one locale instance subsumes another.
\<close>


subsection \<open>Locale declarations\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "locale"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "print_locale"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_locales"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "locale_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{method_def intro_locales} & : & @{text method} \\
    @{method_def unfold_locales} & : & @{text method} \\
  \end{matharray}

  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}
  @{rail \<open>
    @@{command locale} @{syntax name} ('=' @{syntax locale})? @'begin'?
    ;
    @@{command print_locale} '!'? @{syntax nameref}
    ;
    @{syntax_def locale}: @{syntax context_elem}+ |
      @{syntax locale_expr} ('+' (@{syntax context_elem}+))?
    ;
    @{syntax_def context_elem}:
      @'fixes' @{syntax "fixes"} |
      @'constrains' (@{syntax name} '::' @{syntax type} + @'and') |
      @'assumes' (@{syntax props} + @'and') |
      @'defines' (@{syntax thmdecl}? @{syntax prop} @{syntax prop_pat}? + @'and') |
      @'notes' (@{syntax thmdef}? @{syntax thmrefs} + @'and')
  \<close>}

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

  The @{text import} consists of a locale expression; see
  \secref{sec:proof-context} above.  Its @{keyword "for"} clause defines
  the parameters of @{text import}.  These are parameters of
  the defined locale.  Locale parameters whose instantiation is
  omitted automatically extend the (possibly empty) @{keyword "for"}
  clause: they are inserted at its beginning.  This means that these
  parameters may be referred to from within the expression and also in
  the subsequent context elements and provides a notational
  convenience for the inheritance of parameters in locale
  declarations.

  The @{text body} consists of context elements.

  \begin{description}

  \item @{element "fixes"}~@{text "x :: \<tau> (mx)"} declares a local
  parameter of type @{text \<tau>} and mixfix annotation @{text mx} (both
  are optional).  The special syntax declaration ``@{text
  "("}@{keyword_ref "structure"}@{text ")"}'' means that @{text x} may
  be referenced implicitly in this context.

  \item @{element "constrains"}~@{text "x :: \<tau>"} introduces a type
  constraint @{text \<tau>} on the local parameter @{text x}.  This
  element is deprecated.  The type constraint should be introduced in
  the @{keyword "for"} clause or the relevant @{element "fixes"} element.

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

  \end{description}

  Both @{element "assumes"} and @{element "defines"} elements
  contribute to the locale specification.  When defining an operation
  derived from the parameters, @{command "definition"}
  (\secref{sec:term-definitions}) is usually more appropriate.
  
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
  that actually occur in the respective piece of text.  Also these
  predicates operate at the meta-level in theory, but the locale
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

  \item @{command "locale_deps"} visualizes all locales and their
  relations as a Hasse diagram. This includes locales defined as type
  classes (\secref{sec:class}).  See also @{command
  "print_dependencies"} below.

  \item @{method intro_locales} and @{method unfold_locales}
  repeatedly expand all introduction rules of locale predicates of the
  theory.  While @{method intro_locales} only applies the @{text
  loc.intro} introduction rules and therefore does not descend to
  assumptions, @{method unfold_locales} is more aggressive and applies
  @{text loc_axioms.intro} as well.  Both methods are aware of locale
  specifications entailed by the context, both from target statements,
  and from interpretations (see below).  New goals that are entailed
  by the current context are discharged automatically.

  \end{description}
\<close>


subsection \<open>Locale interpretation\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "interpretation"} & : & @{text "theory | local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "interpret"} & : & @{text "proof(state) | proof(chain) \<rightarrow> proof(prove)"} \\
    @{command_def "sublocale"} & : & @{text "theory | local_theory \<rightarrow> proof(prove)"} \\
    @{command_def "print_dependencies"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_interps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  Locales may be instantiated, and the resulting instantiated
  declarations added to the current context.  This requires proof (of
  the instantiated specification) and is called \emph{locale
  interpretation}.  Interpretation is possible in locales (@{command
  "sublocale"}), global and local theories (@{command
  "interpretation"}) and also within proof bodies (@{command
  "interpret"}).

  @{rail \<open>
    @@{command interpretation} @{syntax locale_expr} equations?
    ;
    @@{command interpret} @{syntax locale_expr} equations?
    ;
    @@{command sublocale} (@{syntax nameref} ('<' | '\<subseteq>'))? @{syntax locale_expr} \<newline>
      equations?
    ;
    @@{command print_dependencies} '!'? @{syntax locale_expr}
    ;
    @@{command print_interps} @{syntax nameref}
    ;

    equations: @'where' (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>}

  \begin{description}

  \item @{command "interpretation"}~@{text "expr \<WHERE> eqns"}
  interprets @{text expr} in a global or local theory.  The command
  generates proof obligations for the instantiated specifications.
  Once these are discharged by the user, instantiated declarations (in
  particular, facts) are added to the theory in a post-processing
  phase.

  The command is aware of interpretations that are already active.
  Post-processing is achieved through a variant of roundup that takes
  the interpretations of the current global or local theory into
  account.  In order to simplify the proof obligations according to
  existing interpretations use methods @{method intro_locales} or
  @{method unfold_locales}.

  When adding declarations to locales, interpreted versions of these
  declarations are added to the global theory for all interpretations
  in the global theory as well. That is, interpretations in global
  theories dynamically participate in any declarations added to
  locales.

  In contrast, the lifetime of an interpretation in a local theory is
  limited to the current context block.  At the closing @{command end}
  of the block the interpretation and its declarations disappear.
  This enables establishing facts based on interpretations without
  creating permanent links to the interpreted locale instances, as
  would be the case with @{command sublocale}.
  While @{command "interpretation"}~@{text "(\<IN> c)
  \<dots>"} is technically possible, it is not useful since its result is
  discarded immediately.

  Free variables in the interpreted expression are allowed.  They are
  turned into schematic variables in the generated declarations.  In
  order to use a free variable whose name is already bound in the
  context --- for example, because a constant of that name exists ---
  add it to the @{keyword "for"} clause.

  The equations @{text eqns} yield \emph{rewrite morphisms}, which are
  unfolded during post-processing and are useful for interpreting
  concepts introduced through definitions.  The equations must be
  proved.

  \item @{command "interpret"}~@{text "expr \<WHERE> eqns"} interprets
  @{text expr} in the proof context and is otherwise similar to
  interpretation in local theories.  Note that for @{command
  "interpret"} the @{text eqns} should be
  explicitly universally quantified.

  \item @{command "sublocale"}~@{text "name \<subseteq> expr \<WHERE>
  eqns"}
  interprets @{text expr} in the locale @{text name}.  A proof that
  the specification of @{text name} implies the specification of
  @{text expr} is required.  As in the localized version of the
  theorem command, the proof is in the context of @{text name}.  After
  the proof obligation has been discharged, the locale hierarchy is
  changed as if @{text name} imported @{text expr} (hence the name
  @{command "sublocale"}).  When the context of @{text name} is
  subsequently entered, traversing the locale hierarchy will involve
  the locale instances of @{text expr}, and their declarations will be
  added to the context.  This makes @{command "sublocale"}
  dynamic: extensions of a locale that is instantiated in @{text expr}
  may take place after the @{command "sublocale"} declaration and
  still become available in the context.  Circular @{command
  "sublocale"} declarations are allowed as long as they do not lead to
  infinite chains.

  If interpretations of @{text name} exist in the current global
  theory, the command adds interpretations for @{text expr} as well,
  with the same qualifier, although only for fragments of @{text expr}
  that are not interpreted in the theory already.

  The equations @{text eqns} amend the morphism through
  which @{text expr} is interpreted.  This enables mapping definitions
  from the interpreted locales to entities of @{text name} and can
  help break infinite chains induced by circular @{command
  "sublocale"} declarations.

  In a named context block the @{command sublocale} command may also
  be used, but the locale argument must be omitted.  The command then
  refers to the locale (or class) target of the context block.

  \item @{command "print_dependencies"}~@{text "expr"} is useful for
  understanding the effect of an interpretation of @{text "expr"} in
  the current context.  It lists all locale instances for which
  interpretations would be added to the current context.  Variant
  @{command "print_dependencies"}@{text "!"} does not generalize
  parameters and assumes an empty context --- that is, it prints all
  locale instances that would be considered for interpretation.  The
  latter is useful for understanding the dependencies of a locale
  expression.

  \item @{command "print_interps"}~@{text "locale"} lists all
  interpretations of @{text "locale"} in the current theory or proof
  context, including those due to a combination of an @{command
  "interpretation"} or @{command "interpret"} and one or several
  @{command "sublocale"} declarations.

  \end{description}

  \begin{warn}
    If a global theory inherits declarations (body elements) for a
    locale from one parent and an interpretation of that locale from
    another parent, the interpretation will not be applied to the
    declarations.
  \end{warn}

  \begin{warn}
    Since attributes are applied to interpreted theorems,
    interpretation may modify the context of common proof tools, e.g.\
    the Simplifier or Classical Reasoner.  As the behavior of such
    tools is \emph{not} stable under interpretation morphisms, manual
    declarations might have to be added to the target context of the
    interpretation to revert such declarations.
  \end{warn}

  \begin{warn}
    An interpretation in a local theory or proof context may subsume previous
    interpretations.  This happens if the same specification fragment
    is interpreted twice and the instantiation of the second
    interpretation is more general than the interpretation of the
    first.  The locale package does not attempt to remove subsumed
    interpretations.
  \end{warn}
\<close>


subsubsection \<open>Permanent locale interpretation\<close>

text \<open>
  Permanent locale interpretation is a library extension on top
  of @{command "interpretation"} and @{command "sublocale"}.  It is
  available by importing theory @{file "~~/src/Tools/Permanent_Interpretation.thy"}
  and provides
  \begin{enumerate}
    \item a unified view on arbitrary suitable local theories as interpretation target; 
    \item rewrite morphisms by means of \emph{rewrite definitions}. 
  \end{enumerate}
  
  \begin{matharray}{rcl}
    @{command_def "permanent_interpretation"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
  \end{matharray}

  @{rail \<open>
    @@{command permanent_interpretation} @{syntax locale_expr} \<newline>
      definitions? equations?
    ;

    definitions: @'defining' (@{syntax thmdecl}? @{syntax name} \<newline>
      @{syntax mixfix}? @'=' @{syntax term} + @'and');
    equations: @'where' (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>}

  \begin{description}

  \item @{command "permanent_interpretation"}~@{text "expr \<DEFINING> defs \<WHERE> eqns"}
  interprets @{text expr} in the current local theory.  The command
  generates proof obligations for the instantiated specifications.
  Instantiated declarations (in particular, facts) are added to the
  local theory's underlying target in a post-processing phase.  When
  adding declarations to locales, interpreted versions of these
  declarations are added to any target for all interpretations
  in that target as well. That is, permanent interpretations
  dynamically participate in any declarations added to
  locales.
  
  The local theory's underlying target must explicitly support
  permanent interpretations.  Prominent examples are global theories
  (where @{command "permanent_interpretation"} is technically
  corresponding to @{command "interpretation"}) and locales
  (where @{command "permanent_interpretation"} is technically
  corresponding to @{command "sublocale"}).  Unnamed contexts
  (see \secref{sec:target}) are not admissible since they are
  non-permanent due to their very nature.  

  In additions to \emph{rewrite morphisms} specified by @{text eqns},
  also \emph{rewrite definitions} may be specified.  Semantically, a
  rewrite definition
  
  \begin{itemize}
  
    \item produces a corresponding definition in
      the local theory's underlying target \emph{and}
    
    \item augments the rewrite morphism with the equation
      stemming from the symmetric of the corresponding definition.
  
  \end{itemize}
  
  This is technically different to to a naive combination
  of a conventional definition and an explicit rewrite equation:
  
  \begin{itemize}
  
    \item Definitions are parsed in the syntactic interpretation
      context, just like equations.
  
    \item The proof needs not consider the equations stemming from
      definitions -- they are proved implicitly by construction.
      
  \end{itemize}
  
  Rewrite definitions yield a pattern for introducing new explicit
  operations for existing terms after interpretation.
  
  \end{description}
\<close>


section \<open>Classes \label{sec:class}\<close>

text \<open>
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

  A class is a particular locale with \emph{exactly one} type variable
  @{text \<alpha>}.  Beyond the underlying locale, a corresponding type class
  is established which is interpreted logically as axiomatic type
  class @{cite "Wenzel:1997:TPHOL"} whose logical content are the
  assumptions of the locale.  Thus, classes provide the full
  generality of locales combined with the commodity of type classes
  (notably type-inference).  See @{cite "isabelle-classes"} for a short
  tutorial.

  @{rail \<open>
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
    @@{command subclass} @{syntax nameref}
    ;
    @@{command class_deps} ( ( @{syntax sort} | ( '(' ( @{syntax sort} + @'|' ) ')' ) ) \<newline>
      ( @{syntax sort} | ( '(' ( @{syntax sort} + @'|' ) ')' ) )? )?
  \<close>}

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
  \<BEGIN>"} opens a target (cf.\ \secref{sec:target}) which
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

  A weakened form of this is available through a further variant of
  @{command instance}:  @{command instance}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} opens
  a proof that class @{text "c\<^sub>2"} implies @{text "c\<^sub>1"} without reference
  to the underlying locales;  this is useful if the properties to prove
  the logical connection are not sufficient on the locale level but on
  the theory level.

  \item @{command "print_classes"} prints all classes in the current
  theory.

  \item @{command "class_deps"} visualizes all classes and their
  subclass relations as a Hasse diagram.  An optional first argument
  constrains the set of classes to all subclasses of at least one given
  sort, an optional second rgument to all superclasses of at least one given
  sort.

  \item @{method intro_classes} repeatedly expands all class
  introduction rules of this theory.  Note that this method usually
  needs not be named explicitly, as it is already included in the
  default proof step (e.g.\ of @{command "proof"}).  In particular,
  instantiation of trivial (syntactic) classes may be performed by a
  single ``@{command ".."}'' proof step.

  \end{description}
\<close>


subsection \<open>The class target\<close>

text \<open>
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
\<close>


subsection \<open>Co-regularity of type classes and arities\<close>

text \<open>The class relation together with the collection of
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
  types and most general unifiers, e.g.\ see @{cite "nipkow-prehofer"}.
\<close>


section \<open>Unrestricted overloading\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "overloading"} & : & @{text "theory \<rightarrow> local_theory"} \\
  \end{matharray}

  Isabelle/Pure's definitional schemes support certain forms of
  overloading (see \secref{sec:consts}).  Overloading means that a
  constant being declared as @{text "c :: \<alpha> decl"} may be
  defined separately on type instances
  @{text "c :: (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t decl"}
  for each type constructor @{text t}.  At most occasions
  overloading will be used in a Haskell-like fashion together with
  type classes by means of @{command "instantiation"} (see
  \secref{sec:class}).  Sometimes low-level overloading is desirable.
  The @{command "overloading"} target provides a convenient view for
  end-users.

  @{rail \<open>
    @@{command overloading} ( spec + ) @'begin'
    ;
    spec: @{syntax name} ( '==' | '\<equiv>' ) @{syntax term} ( '(' @'unchecked' ')' )?
  \<close>}

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
\<close>


section \<open>Incorporating ML code \label{sec:ML}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "SML_file"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "ML_file"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML_prf"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "ML_val"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "ML_command"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "setup"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "local_setup"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "attribute_setup"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}
  \begin{tabular}{rcll}
    @{attribute_def ML_print_depth} & : & @{text attribute} & default 10 \\
    @{attribute_def ML_source_trace} & : & @{text attribute} & default @{text false} \\
    @{attribute_def ML_exception_trace} & : & @{text attribute} & default @{text false} \\
  \end{tabular}

  @{rail \<open>
    (@@{command SML_file} | @@{command ML_file}) @{syntax name}
    ;
    (@@{command ML} | @@{command ML_prf} | @@{command ML_val} |
      @@{command ML_command} | @@{command setup} | @@{command local_setup}) @{syntax text}
    ;
    @@{command attribute_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
  \<close>}

  \begin{description}

  \item @{command "SML_file"}~@{text "name"} reads and evaluates the
  given Standard ML file.  Top-level SML bindings are stored within
  the theory context; the initial environment is restricted to the
  Standard ML implementation of Poly/ML, without the many add-ons of
  Isabelle/ML.  Multiple @{command "SML_file"} commands may be used to
  build larger Standard ML projects, independently of the regular
  Isabelle/ML environment.

  \item @{command "ML_file"}~@{text "name"} reads and evaluates the
  given ML file.  The current theory context is passed down to the ML
  toplevel and may be modified, using @{ML "Context.>>"} or derived ML
  commands.  Top-level ML bindings are stored within the (global or
  local) theory context.
  
  \item @{command "ML"}~@{text "text"} is similar to @{command
  "ML_file"}, but evaluates directly the given @{text "text"}.
  Top-level ML bindings are stored within the (global or local) theory
  context.

  \item @{command "ML_prf"} is analogous to @{command "ML"} but works
  within a proof context.  Top-level ML bindings are stored within the
  proof context in a purely sequential fashion, disregarding the
  nested proof structure.  ML bindings introduced by @{command
  "ML_prf"} are discarded at the end of the proof.

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
  defines an attribute in the current context.  The given @{text
  "text"} has to be an ML expression of type
  @{ML_type "attribute context_parser"}, cf.\ basic parsers defined in
  structure @{ML_structure Args} and @{ML_structure Attrib}.

  In principle, attributes can operate both on a given theorem and the
  implicit context, although in practice only one is modified and the
  other serves as parameter.  Here are examples for these two cases:

  \end{description}
\<close>

  attribute_setup my_rule =
    \<open>Attrib.thms >> (fn ths =>
      Thm.rule_attribute
        (fn context: Context.generic => fn th: thm =>
          let val th' = th OF ths
          in th' end))\<close>

  attribute_setup my_declaration =
    \<open>Attrib.thms >> (fn ths =>
      Thm.declaration_attribute
        (fn th: thm => fn context: Context.generic =>
          let val context' = context
          in context' end))\<close>

text \<open>
  \begin{description}

  \item @{attribute ML_print_depth} controls the printing depth of the ML
  toplevel pretty printer; the precise effect depends on the ML compiler and
  run-time system. Typically the limit should be less than 10. Bigger values
  such as 100--1000 are occasionally useful for debugging.

  \item @{attribute ML_source_trace} indicates whether the source text that
  is given to the ML compiler should be output: it shows the raw Standard ML
  after expansion of Isabelle/ML antiquotations.

  \item @{attribute ML_exception_trace} indicates whether the ML run-time
  system should print a detailed stack trace on exceptions. The result is
  dependent on the particular ML compiler version. Note that after Poly/ML
  5.3 some optimizations in the run-time systems may hinder exception
  traces.

  The boundary for the exception trace is the current Isar command
  transactions. It is occasionally better to insert the combinator @{ML
  Runtime.exn_trace} into ML code for debugging @{cite
  "isabelle-implementation"}, closer to the point where it actually
  happens.

  \end{description}
\<close>


section \<open>Primitive specification elements\<close>

subsection \<open>Sorts\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "default_sort"} & : & @{text "local_theory \<rightarrow> local_theory"}
  \end{matharray}

  @{rail \<open>
    @@{command default_sort} @{syntax sort}
  \<close>}

  \begin{description}

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
\<close>


subsection \<open>Types \label{sec:types-pure}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "type_synonym"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "typedecl"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail \<open>
    @@{command type_synonym} (@{syntax typespec} '=' @{syntax type} @{syntax mixfix}?)
    ;
    @@{command typedecl} @{syntax typespec} @{syntax mixfix}?
  \<close>}

  \begin{description}

  \item @{command "type_synonym"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>"} introduces a
  \emph{type synonym} @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} for the existing type @{text
  "\<tau>"}. Unlike the semantic type definitions in Isabelle/HOL, type synonyms
  are merely syntactic abbreviations without any logical significance.
  Internally, type synonyms are fully expanded.
  
  \item @{command "typedecl"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} declares a new
  type constructor @{text t}.  If the object-logic defines a base sort
  @{text s}, then the constructor is declared to operate on that, via
  the axiomatic type-class instance @{text "t :: (s, \<dots>, s)s"}.

  \end{description}

  \begin{warn}
  If you introduce a new type axiomatically, i.e.\ via @{command_ref
  typedecl} and @{command_ref axiomatization}
  (\secref{sec:axiomatizations}), the minimum requirement is that it has a
  non-empty model, to avoid immediate collapse of the logical environment.
  Moreover, one needs to demonstrate that the interpretation of such
  free-form axiomatizations can coexist with other axiomatization schemes
  for types, notably @{command_def typedef} in Isabelle/HOL
  (\secref{sec:hol-typedef}), or any other extension that people might have
  introduced elsewhere.
  \end{warn}
\<close>


subsection \<open>Constants and definitions \label{sec:consts}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "consts"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "defs"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

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

  @{rail \<open>
    @@{command consts} ((@{syntax name} '::' @{syntax type} @{syntax mixfix}?) +)
    ;
    @@{command defs} opt? (@{syntax axmdecl} @{syntax prop} +)
    ;
    opt: '(' @'unchecked'? @'overloaded'? ')'
  \<close>}

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
\<close>


section \<open>Naming existing theorems \label{sec:theorems}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "lemmas"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "theorems"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "named_theorems"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  @{rail \<open>
    (@@{command lemmas} | @@{command theorems}) (@{syntax thmdef}? @{syntax thmrefs} + @'and')
      @{syntax for_fixes}
    ;
    @@{command named_theorems} (@{syntax name} @{syntax text}? + @'and')
  \<close>}

  \begin{description}
  
  \item @{command "lemmas"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}~@{keyword_def
  "for"}~@{text "x\<^sub>1 \<dots> x\<^sub>m"} evaluates given facts (with attributes) in
  the current context, which may be augmented by local variables.
  Results are standardized before being stored, i.e.\ schematic
  variables are renamed to enforce index @{text "0"} uniformly.

  \item @{command "theorems"} is the same as @{command "lemmas"}, but
  marks the result as a different kind of facts.

  \item @{command "named_theorems"}~@{text "name description"} declares a
  dynamic fact within the context. The same @{text name} is used to define
  an attribute with the usual @{text add}/@{text del} syntax (e.g.\ see
  \secref{sec:simp-rules}) to maintain the content incrementally, in
  canonical declaration order of the text structure.

  \end{description}
\<close>


section \<open>Oracles\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "oracle"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
  \end{matharray}

  Oracles allow Isabelle to take advantage of external reasoners such
  as arithmetic decision procedures, model checkers, fast tautology
  checkers or computer algebra systems.  Invoked as an oracle, an
  external reasoner can create arbitrary Isabelle theorems.

  It is the responsibility of the user to ensure that the external
  reasoner is as trustworthy as the application requires.  Another
  typical source of errors is the linkup between Isabelle and the
  external tool, not just its concrete implementation, but also the
  required translation between two different logical environments.

  Isabelle merely guarantees well-formedness of the propositions being
  asserted, and records within the internal derivation object how
  presumed theorems depend on unproven suppositions.

  @{rail \<open>
    @@{command oracle} @{syntax name} '=' @{syntax text}
  \<close>}

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
\<close>


section \<open>Name spaces\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "hide_class"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_type"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_const"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide_fact"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail \<open>
    ( @{command hide_class} | @{command hide_type} |
      @{command hide_const} | @{command hide_fact} ) ('(' @'open' ')')? (@{syntax nameref} + )
  \<close>}

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
\<close>

end

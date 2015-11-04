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
    @{command_def "theory"} & : & \<open>toplevel \<rightarrow> theory\<close> \\
    @{command_def (global) "end"} & : & \<open>theory \<rightarrow> toplevel\<close> \\
    @{command_def "thy_deps"}\<open>\<^sup>*\<close> & : & \<open>theory \<rightarrow>\<close> \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory files, which consist of an
  outermost sequence of definition--statement--proof elements. Some
  definitions are self-sufficient (e.g.\ @{command fun} in Isabelle/HOL),
  with foundational proofs performed internally. Other definitions require
  an explicit proof as justification (e.g.\ @{command function} and
  @{command termination} in Isabelle/HOL). Plain statements like @{command
  theorem} or @{command lemma} are merely a special case of that, defining a
  theorem from a given proposition and its proof.

  The theory body may be sub-structured by means of \<^emph>\<open>local theory
  targets\<close>, such as @{command "locale"} and @{command "class"}. It is also
  possible to use @{command context}~@{keyword "begin"}~\dots~@{command end}
  blocks to delimited a local theory context: a \<^emph>\<open>named context\<close> to
  augment a locale or class specification, or an \<^emph>\<open>unnamed context\<close> to
  refer to local parameters and assumptions that are discharged later. See
  \secref{sec:target} for more details.

  \<^medskip>
  A theory is commenced by the @{command "theory"} command, which
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
    ;
    @@{command thy_deps} (thy_bounds thy_bounds?)?
    ;
    thy_bounds: @{syntax name} | '(' (@{syntax name} + @'|') ')'
  \<close>}

  \<^descr> @{command "theory"}~\<open>A \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>\<close>
  starts a new theory \<open>A\<close> based on the merge of existing
  theories \<open>B\<^sub>1 \<dots> B\<^sub>n\<close>.  Due to the possibility to import more
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
  itself, such as @{keyword "keywords"}~\<^verbatim>\<open>"typedef"\<close>
  \<open>:: thy_goal\<close> or @{keyword "keywords"}~\<^verbatim>\<open>"datatype"\<close> \<open>:: thy_decl\<close>
  for theory-level declarations
  with and without proof, respectively.  Additional @{syntax tags}
  provide defaults for document preparation (\secref{sec:tags}).

  It is possible to specify an alternative completion via \<^verbatim>\<open>==\<close>~\<open>text\<close>,
  while the default is the corresponding keyword name.
  
  \<^descr> @{command (global) "end"} concludes the current theory
  definition.  Note that some other commands, e.g.\ local theory
  targets @{command locale} or @{command class} may involve a
  @{keyword "begin"} that needs to be matched by @{command (local)
  "end"}, according to the usual rules for nested blocks.

  \<^descr> @{command thy_deps} visualizes the theory hierarchy as a directed
  acyclic graph. By default, all imported theories are shown, taking the
  base session as a starting point. Alternatively, it is possibly to
  restrict the full theory graph by giving bounds, analogously to
  @{command_ref class_deps}.
\<close>


section \<open>Local theory targets \label{sec:target}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "context"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def (local) "end"} & : & \<open>local_theory \<rightarrow> theory\<close> \\
    @{keyword_def "private"} \\
    @{keyword_def "qualified"} \\
  \end{matharray}

  A local theory target is a specification context that is managed
  separately within the enclosing theory. Contexts may introduce parameters
  (fixed variables) and assumptions (hypotheses). Definitions and theorems
  depending on the context may be added incrementally later on.

  \<^emph>\<open>Named contexts\<close> refer to locales (cf.\ \secref{sec:locale}) or
  type classes (cf.\ \secref{sec:class}); the name ``\<open>-\<close>''
  signifies the global theory context.

  \<^emph>\<open>Unnamed contexts\<close> may introduce additional parameters and
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

  \<^descr> @{command "context"}~\<open>c \<BEGIN>\<close> opens a named
  context, by recommencing an existing locale or class \<open>c\<close>.
  Note that locale and class definitions allow to include the
  @{keyword "begin"} keyword as well, in order to continue the local
  theory immediately after the initial specification.

  \<^descr> @{command "context"}~\<open>bundles elements \<BEGIN>\<close> opens
  an unnamed context, by extending the enclosing global or local
  theory target by the given declaration bundles (\secref{sec:bundle})
  and context elements (\<open>\<FIXES>\<close>, \<open>\<ASSUMES>\<close>
  etc.).  This means any results stemming from definitions and proofs
  in the extended context will be exported into the enclosing target
  by lifting over extra parameters and premises.
  
  \<^descr> @{command (local) "end"} concludes the current local theory,
  according to the nesting of contexts.  Note that a global @{command
  (global) "end"} has a different meaning: it concludes the theory
  itself (\secref{sec:begin-thy}).
  
  \<^descr> @{keyword "private"} or @{keyword "qualified"} may be given as
  modifiers before any local theory command. This restricts name space
  accesses to the local scope, as determined by the enclosing @{command
  "context"}~@{keyword "begin"}~\dots~@{command "end"} block. Outside its
  scope, a @{keyword "private"} name is inaccessible, and a @{keyword
  "qualified"} name is only accessible with some qualification.

  Neither a global @{command theory} nor a @{command locale} target provides
  a local scope by itself: an extra unnamed context is required to use
  @{keyword "private"} or @{keyword "qualified"} here.

  \<^descr> \<open>(\<close>@{keyword_def "in"}~\<open>c)\<close> given after any local
  theory command specifies an immediate target, e.g.\ ``@{command
  "definition"}~\<open>(\<IN> c)\<close>'' or ``@{command "theorem"}~\<open>(\<IN> c)\<close>''. This works both in a local or global theory context; the
  current target context will be suspended for this command only. Note that
  ``\<open>(\<IN> -)\<close>'' will always produce a global result independently
  of the current target context.


  Any specification element that operates on \<open>local_theory\<close> according
  to this manual implicitly allows the above target syntax \<open>(\<close>@{keyword "in"}~\<open>c)\<close>, but individual syntax diagrams omit that
  aspect for clarity.

  \<^medskip>
  The exact meaning of results produced within a local theory
  context depends on the underlying target infrastructure (locale, type
  class etc.). The general idea is as follows, considering a context named
  \<open>c\<close> with parameter \<open>x\<close> and assumption \<open>A[x]\<close>.
  
  Definitions are exported by introducing a global version with
  additional arguments; a syntactic abbreviation links the long form
  with the abstract version of the target context.  For example,
  \<open>a \<equiv> t[x]\<close> becomes \<open>c.a ?x \<equiv> t[?x]\<close> at the theory
  level (for arbitrary \<open>?x\<close>), together with a local
  abbreviation \<open>c \<equiv> c.a x\<close> in the target context (for the
  fixed parameter \<open>x\<close>).

  Theorems are exported by discharging the assumptions and
  generalizing the parameters of the context.  For example, \<open>a:
  B[x]\<close> becomes \<open>c.a: A[?x] \<Longrightarrow> B[?x]\<close>, again for arbitrary
  \<open>?x\<close>.
\<close>


section \<open>Bundled declarations \label{sec:bundle}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "bundle"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_bundles"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "include"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "including"} & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{keyword_def "includes"} & : & syntax \\
  \end{matharray}

  The outer syntax of fact expressions (\secref{sec:syn-att}) involves
  theorems and attributes, which are evaluated in the context and
  applied to it.  Attributes may declare theorems to the context, as
  in \<open>this_rule [intro] that_rule [elim]\<close> for example.
  Configuration options (\secref{sec:config}) are special declaration
  attributes that operate on the context without a theorem, as in
  \<open>[[show_types = false]]\<close> for example.

  Expressions of this form may be defined as \<^emph>\<open>bundled
  declarations\<close> in the context, and included in other situations later
  on.  Including declaration bundles augments a local context casually
  without logical dependencies, which is in contrast to locales and
  locale interpretation (\secref{sec:locale}).

  @{rail \<open>
    @@{command bundle} @{syntax name} '=' @{syntax thmrefs} @{syntax for_fixes}
    ;
    @@{command print_bundles} ('!'?)
    ;
    (@@{command include} | @@{command including}) (@{syntax nameref}+)
    ;
    @{syntax_def "includes"}: @'includes' (@{syntax nameref}+)
  \<close>}

  \<^descr> @{command bundle}~\<open>b = decls\<close> defines a bundle of
  declarations in the current context.  The RHS is similar to the one
  of the @{command declare} command.  Bundles defined in local theory
  targets are subject to transformations via morphisms, when moved
  into different application contexts; this works analogously to any
  other local theory specification.

  \<^descr> @{command print_bundles} prints the named bundles that are available
  in the current context; the ``\<open>!\<close>'' option indicates extra
  verbosity.

  \<^descr> @{command include}~\<open>b\<^sub>1 \<dots> b\<^sub>n\<close> includes the declarations
  from the given bundles into the current proof body context.  This is
  analogous to @{command "note"} (\secref{sec:proof-facts}) with the
  expanded bundles.

  \<^descr> @{command including} is similar to @{command include}, but
  works in proof refinement (backward mode).  This is analogous to
  @{command "using"} (\secref{sec:proof-facts}) with the expanded
  bundles.

  \<^descr> @{keyword "includes"}~\<open>b\<^sub>1 \<dots> b\<^sub>n\<close> is similar to
  @{command include}, but works in situations where a specification
  context is constructed, notably for @{command context} and long
  statements of @{command theorem} etc.


  Here is an artificial example of bundling various configuration
  options:
\<close>

(*<*)experiment begin(*>*)
bundle trace = [[simp_trace, linarith_trace, metis_trace, smt_trace]]

lemma "x = x"
  including trace by metis
(*<*)end(*>*)


section \<open>Term definitions \label{sec:term-definitions}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "definition"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{attribute_def "defn"} & : & \<open>attribute\<close> \\
    @{command_def "print_defn_rules"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "abbreviation"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_abbrevs"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
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
    ;
    @@{command print_abbrevs} ('!'?)
  \<close>}

  \<^descr> @{command "definition"}~\<open>c \<WHERE> eq\<close> produces an
  internal definition \<open>c \<equiv> t\<close> according to the specification
  given as \<open>eq\<close>, which is then turned into a proven fact.  The
  given proposition may deviate from internal meta-level equality
  according to the rewrite rules declared as @{attribute defn} by the
  object-logic.  This usually covers object-level equality \<open>x =
  y\<close> and equivalence \<open>A \<leftrightarrow> B\<close>.  End-users normally need not
  change the @{attribute defn} setup.
  
  Definitions may be presented with explicit arguments on the LHS, as
  well as additional conditions, e.g.\ \<open>f x y = t\<close> instead of
  \<open>f \<equiv> \<lambda>x y. t\<close> and \<open>y \<noteq> 0 \<Longrightarrow> g x y = u\<close> instead of an
  unrestricted \<open>g \<equiv> \<lambda>x y. u\<close>.

  \<^descr> @{command "print_defn_rules"} prints the definitional rewrite rules
  declared via @{attribute defn} in the current context.

  \<^descr> @{command "abbreviation"}~\<open>c \<WHERE> eq\<close> introduces a
  syntactic constant which is associated with a certain term according
  to the meta-level equality \<open>eq\<close>.
  
  Abbreviations participate in the usual type-inference process, but
  are expanded before the logic ever sees them.  Pretty printing of
  terms involves higher-order rewriting with rules stemming from
  reverted abbreviations.  This needs some care to avoid overlapping
  or looping syntactic replacements!
  
  The optional \<open>mode\<close> specification restricts output to a
  particular print mode; using ``\<open>input\<close>'' here achieves the
  effect of one-way abbreviations.  The mode may also include an
  ``@{keyword "output"}'' qualifier that affects the concrete syntax
  declared for abbreviations, cf.\ @{command "syntax"} in
  \secref{sec:syn-trans}.
  
  \<^descr> @{command "print_abbrevs"} prints all constant abbreviations of the
  current context; the ``\<open>!\<close>'' option indicates extra verbosity.
\<close>


section \<open>Axiomatizations \label{sec:axiomatizations}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & \<open>theory \<rightarrow> theory\<close> & (axiomatic!) \\
  \end{matharray}

  @{rail \<open>
    @@{command axiomatization} @{syntax "fixes"}? (@'where' specs)?
    ;
    specs: (@{syntax thmdecl}? @{syntax props} + @'and')
  \<close>}

  \<^descr> @{command "axiomatization"}~\<open>c\<^sub>1 \<dots> c\<^sub>m \<WHERE> \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close>
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
\<close>


section \<open>Generic declarations\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "declaration"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "syntax_declaration"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "declare"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
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

  \<^descr> @{command "declaration"}~\<open>d\<close> adds the declaration
  function \<open>d\<close> of ML type @{ML_type declaration}, to the current
  local theory under construction.  In later application contexts, the
  function is transformed according to the morphisms being involved in
  the interpretation hierarchy.

  If the \<open>(pervasive)\<close> option is given, the corresponding
  declaration is applied to all possible contexts involved, including
  the global background theory.

  \<^descr> @{command "syntax_declaration"} is similar to @{command
  "declaration"}, but is meant to affect only ``syntactic'' tools by
  convention (such as notation and type-checking information).

  \<^descr> @{command "declare"}~\<open>thms\<close> declares theorems to the
  current local theory context.  No theorem binding is involved here,
  unlike @{command "lemmas"} (cf.\ \secref{sec:theorems}), so
  @{command "declare"} only has the effect of applying attributes as
  included in the theorem specification.
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
  as a local theory.  In this process, which is called \<^emph>\<open>roundup\<close>,
  redundant locale instances are omitted.  A locale instance is
  redundant if it is subsumed by an instance encountered earlier.  A
  more detailed description of this process is available elsewhere
  @{cite Ballarin2014}.
\<close>


subsection \<open>Locale expressions \label{sec:locale-expr}\<close>

text \<open>
  A \<^emph>\<open>locale expression\<close> denotes a context composed of instances
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
  may be omitted.  The notation `\<open>_\<close>' enables to omit the
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
  (``\<^verbatim>\<open>?\<close>''), which means that it may be omitted on input of the
  qualified name, or mandatory (``\<^verbatim>\<open>!\<close>'').  If neither
  ``\<^verbatim>\<open>?\<close>'' nor ``\<^verbatim>\<open>!\<close>'' are present the default
  is used, which is ``mandatory''.  Qualifiers play no role
  in determining whether one locale instance subsumes another.
\<close>


subsection \<open>Locale declarations\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "locale"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "experiment"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_locale"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_locales"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "locale_deps"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{method_def intro_locales} & : & \<open>method\<close> \\
    @{method_def unfold_locales} & : & \<open>method\<close> \\
  \end{matharray}

  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}
  @{rail \<open>
    @@{command locale} @{syntax name} ('=' @{syntax locale})? @'begin'?
    ;
    @@{command experiment} (@{syntax context_elem}*) @'begin'
    ;
    @@{command print_locale} '!'? @{syntax nameref}
    ;
    @@{command print_locales} ('!'?)
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

  \<^descr> @{command "locale"}~\<open>loc = import + body\<close> defines a
  new locale \<open>loc\<close> as a context consisting of a certain view of
  existing locales (\<open>import\<close>) plus some additional elements
  (\<open>body\<close>).  Both \<open>import\<close> and \<open>body\<close> are optional;
  the degenerate form @{command "locale"}~\<open>loc\<close> defines an empty
  locale, which may still be useful to collect declarations of facts
  later on.  Type-inference on locale expressions automatically takes
  care of the most general typing that the combined context elements
  may acquire.

  The \<open>import\<close> consists of a locale expression; see
  \secref{sec:proof-context} above.  Its @{keyword "for"} clause defines
  the parameters of \<open>import\<close>.  These are parameters of
  the defined locale.  Locale parameters whose instantiation is
  omitted automatically extend the (possibly empty) @{keyword "for"}
  clause: they are inserted at its beginning.  This means that these
  parameters may be referred to from within the expression and also in
  the subsequent context elements and provides a notational
  convenience for the inheritance of parameters in locale
  declarations.

  The \<open>body\<close> consists of context elements.

    \<^descr> @{element "fixes"}~\<open>x :: \<tau> (mx)\<close> declares a local
    parameter of type \<open>\<tau>\<close> and mixfix annotation \<open>mx\<close> (both
    are optional).  The special syntax declaration ``\<open>(\<close>@{keyword_ref "structure"}\<open>)\<close>'' means that \<open>x\<close> may
    be referenced implicitly in this context.

    \<^descr> @{element "constrains"}~\<open>x :: \<tau>\<close> introduces a type
    constraint \<open>\<tau>\<close> on the local parameter \<open>x\<close>.  This
    element is deprecated.  The type constraint should be introduced in
    the @{keyword "for"} clause or the relevant @{element "fixes"} element.

    \<^descr> @{element "assumes"}~\<open>a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close>
    introduces local premises, similar to @{command "assume"} within a
    proof (cf.\ \secref{sec:proof-context}).

    \<^descr> @{element "defines"}~\<open>a: x \<equiv> t\<close> defines a previously
    declared parameter.  This is similar to @{command "def"} within a
    proof (cf.\ \secref{sec:proof-context}), but @{element "defines"}
    takes an equational proposition instead of variable-term pair.  The
    left-hand side of the equation may have additional arguments, e.g.\
    ``@{element "defines"}~\<open>f x\<^sub>1 \<dots> x\<^sub>n \<equiv> t\<close>''.

    \<^descr> @{element "notes"}~\<open>a = b\<^sub>1 \<dots> b\<^sub>n\<close>
    reconsiders facts within a local context.  Most notably, this may
    include arbitrary declarations in any attribute specifications
    included here, e.g.\ a local @{attribute simp} rule.

  Both @{element "assumes"} and @{element "defines"} elements
  contribute to the locale specification.  When defining an operation
  derived from the parameters, @{command "definition"}
  (\secref{sec:term-definitions}) is usually more appropriate.
  
  Note that ``\<open>(\<IS> p\<^sub>1 \<dots> p\<^sub>n)\<close>'' patterns given
  in the syntax of @{element "assumes"} and @{element "defines"} above
  are illegal in locale definitions.  In the long goal format of
  \secref{sec:goals}, term bindings may be included as expected,
  though.
  
  \<^medskip>
  Locale specifications are ``closed up'' by
  turning the given text into a predicate definition \<open>loc_axioms\<close> and deriving the original assumptions as local lemmas
  (modulo local definitions).  The predicate statement covers only the
  newly specified assumptions, omitting the content of included locale
  expressions.  The full cumulative view is only provided on export,
  involving another predicate \<open>loc\<close> that refers to the complete
  specification text.
  
  In any case, the predicate arguments are those locale parameters
  that actually occur in the respective piece of text.  Also these
  predicates operate at the meta-level in theory, but the locale
  packages attempts to internalize statements according to the
  object-logic setup (e.g.\ replacing \<open>\<And>\<close> by \<open>\<forall>\<close>, and
  \<open>\<Longrightarrow>\<close> by \<open>\<longrightarrow>\<close> in HOL; see also
  \secref{sec:object-logic}).  Separate introduction rules \<open>loc_axioms.intro\<close> and \<open>loc.intro\<close> are provided as well.

  \<^descr> @{command experiment}~\<open>exprs\<close>~@{keyword "begin"} opens an
  anonymous locale context with private naming policy. Specifications in its
  body are inaccessible from outside. This is useful to perform experiments,
  without polluting the name space.

  \<^descr> @{command "print_locale"}~\<open>locale\<close> prints the
  contents of the named locale.  The command omits @{element "notes"}
  elements by default.  Use @{command "print_locale"}\<open>!\<close> to
  have them included.

  \<^descr> @{command "print_locales"} prints the names of all locales of the
  current theory; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> @{command "locale_deps"} visualizes all locales and their
  relations as a Hasse diagram. This includes locales defined as type
  classes (\secref{sec:class}).  See also @{command
  "print_dependencies"} below.

  \<^descr> @{method intro_locales} and @{method unfold_locales}
  repeatedly expand all introduction rules of locale predicates of the
  theory.  While @{method intro_locales} only applies the \<open>loc.intro\<close> introduction rules and therefore does not descend to
  assumptions, @{method unfold_locales} is more aggressive and applies
  \<open>loc_axioms.intro\<close> as well.  Both methods are aware of locale
  specifications entailed by the context, both from target statements,
  and from interpretations (see below).  New goals that are entailed
  by the current context are discharged automatically.
\<close>


subsection \<open>Locale interpretation\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "interpretation"} & : & \<open>theory | local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "interpret"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
    @{command_def "sublocale"} & : & \<open>theory | local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "print_dependencies"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_interps"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  Locales may be instantiated, and the resulting instantiated
  declarations added to the current context.  This requires proof (of
  the instantiated specification) and is called \<^emph>\<open>locale
  interpretation\<close>.  Interpretation is possible in locales (@{command
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

    equations: @'rewrites' (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>}

  \<^descr> @{command "interpretation"}~\<open>expr\<close>~@{keyword "rewrites"}~\<open>eqns\<close>
  interprets \<open>expr\<close> in a global or local theory.  The command
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
  While @{command "interpretation"}~\<open>(\<IN> c)
  \<dots>\<close> is technically possible, it is not useful since its result is
  discarded immediately.

  Free variables in the interpreted expression are allowed.  They are
  turned into schematic variables in the generated declarations.  In
  order to use a free variable whose name is already bound in the
  context --- for example, because a constant of that name exists ---
  add it to the @{keyword "for"} clause.

  The equations \<open>eqns\<close> yield \<^emph>\<open>rewrite morphisms\<close>, which are
  unfolded during post-processing and are useful for interpreting
  concepts introduced through definitions.  The equations must be
  proved.

  \<^descr> @{command "interpret"}~\<open>expr\<close>~@{keyword "rewrites"}~\<open>eqns\<close> interprets
  \<open>expr\<close> in the proof context and is otherwise similar to
  interpretation in local theories.  Note that for @{command
  "interpret"} the \<open>eqns\<close> should be
  explicitly universally quantified.

  \<^descr> @{command "sublocale"}~\<open>name \<subseteq> expr\<close>~@{keyword "rewrites"}~\<open>eqns\<close>
  interprets \<open>expr\<close> in the locale \<open>name\<close>.  A proof that
  the specification of \<open>name\<close> implies the specification of
  \<open>expr\<close> is required.  As in the localized version of the
  theorem command, the proof is in the context of \<open>name\<close>.  After
  the proof obligation has been discharged, the locale hierarchy is
  changed as if \<open>name\<close> imported \<open>expr\<close> (hence the name
  @{command "sublocale"}).  When the context of \<open>name\<close> is
  subsequently entered, traversing the locale hierarchy will involve
  the locale instances of \<open>expr\<close>, and their declarations will be
  added to the context.  This makes @{command "sublocale"}
  dynamic: extensions of a locale that is instantiated in \<open>expr\<close>
  may take place after the @{command "sublocale"} declaration and
  still become available in the context.  Circular @{command
  "sublocale"} declarations are allowed as long as they do not lead to
  infinite chains.

  If interpretations of \<open>name\<close> exist in the current global
  theory, the command adds interpretations for \<open>expr\<close> as well,
  with the same qualifier, although only for fragments of \<open>expr\<close>
  that are not interpreted in the theory already.

  The equations \<open>eqns\<close> amend the morphism through
  which \<open>expr\<close> is interpreted.  This enables mapping definitions
  from the interpreted locales to entities of \<open>name\<close> and can
  help break infinite chains induced by circular @{command
  "sublocale"} declarations.

  In a named context block the @{command sublocale} command may also
  be used, but the locale argument must be omitted.  The command then
  refers to the locale (or class) target of the context block.

  \<^descr> @{command "print_dependencies"}~\<open>expr\<close> is useful for
  understanding the effect of an interpretation of \<open>expr\<close> in
  the current context.  It lists all locale instances for which
  interpretations would be added to the current context.  Variant
  @{command "print_dependencies"}\<open>!\<close> does not generalize
  parameters and assumes an empty context --- that is, it prints all
  locale instances that would be considered for interpretation.  The
  latter is useful for understanding the dependencies of a locale
  expression.

  \<^descr> @{command "print_interps"}~\<open>locale\<close> lists all
  interpretations of \<open>locale\<close> in the current theory or proof
  context, including those due to a combination of an @{command
  "interpretation"} or @{command "interpret"} and one or several
  @{command "sublocale"} declarations.


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
    tools is \<^emph>\<open>not\<close> stable under interpretation morphisms, manual
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

  \<^enum> a unified view on arbitrary suitable local theories as interpretation target;

  \<^enum> rewrite morphisms by means of \<^emph>\<open>rewrite definitions\<close>.

  
  \begin{matharray}{rcl}
    @{command_def "permanent_interpretation"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close>
  \end{matharray}

  @{rail \<open>
    @@{command permanent_interpretation} @{syntax locale_expr} \<newline>
      definitions? equations?
    ;
    definitions: @'defining' (@{syntax thmdecl}? @{syntax name} \<newline>
      @{syntax mixfix}? @'=' @{syntax term} + @'and');
    equations: @'rewrites' (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>}

  \<^descr> @{command "permanent_interpretation"}~\<open>expr \<DEFINING> defs\<close>~@{keyword "rewrites"}~\<open>eqns\<close>
  interprets \<open>expr\<close> in the current local theory.  The command
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

  In additions to \<^emph>\<open>rewrite morphisms\<close> specified by \<open>eqns\<close>,
  also \<^emph>\<open>rewrite definitions\<close> may be specified.  Semantically, a
  rewrite definition
  
    \<^item> produces a corresponding definition in
    the local theory's underlying target \<^emph>\<open>and\<close>

    \<^item> augments the rewrite morphism with the equation
    stemming from the symmetric of the corresponding definition.
  
  This is technically different to to a naive combination
  of a conventional definition and an explicit rewrite equation:
  
    \<^item> Definitions are parsed in the syntactic interpretation
    context, just like equations.

    \<^item> The proof needs not consider the equations stemming from
    definitions -- they are proved implicitly by construction.
  
  Rewrite definitions yield a pattern for introducing new explicit
  operations for existing terms after interpretation.
\<close>


section \<open>Classes \label{sec:class}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "class"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "instantiation"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "instance"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command "instance"} & : & \<open>theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "subclass"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_classes"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "class_deps"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{method_def intro_classes} & : & \<open>method\<close> \\
  \end{matharray}

  A class is a particular locale with \<^emph>\<open>exactly one\<close> type variable
  \<open>\<alpha>\<close>.  Beyond the underlying locale, a corresponding type class
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
    @@{command class_deps} (class_bounds class_bounds?)?
    ;
    class_bounds: @{syntax sort} | '(' (@{syntax sort} + @'|') ')'
  \<close>}

  \<^descr> @{command "class"}~\<open>c = superclasses + body\<close> defines
  a new class \<open>c\<close>, inheriting from \<open>superclasses\<close>.  This
  introduces a locale \<open>c\<close> with import of all locales \<open>superclasses\<close>.

  Any @{element "fixes"} in \<open>body\<close> are lifted to the global
  theory level (\<^emph>\<open>class operations\<close> \<open>f\<^sub>1, \<dots>,
  f\<^sub>n\<close> of class \<open>c\<close>), mapping the local type parameter
  \<open>\<alpha>\<close> to a schematic type variable \<open>?\<alpha> :: c\<close>.

  Likewise, @{element "assumes"} in \<open>body\<close> are also lifted,
  mapping each local parameter \<open>f :: \<tau>[\<alpha>]\<close> to its
  corresponding global constant \<open>f :: \<tau>[?\<alpha> :: c]\<close>.  The
  corresponding introduction rule is provided as \<open>c_class_axioms.intro\<close>.  This rule should be rarely needed directly
  --- the @{method intro_classes} method takes care of the details of
  class membership proofs.

  \<^descr> @{command "instantiation"}~\<open>t :: (s\<^sub>1, \<dots>, s\<^sub>n)s
  \<BEGIN>\<close> opens a target (cf.\ \secref{sec:target}) which
  allows to specify class operations \<open>f\<^sub>1, \<dots>, f\<^sub>n\<close> corresponding
  to sort \<open>s\<close> at the particular type instance \<open>(\<alpha>\<^sub>1 :: s\<^sub>1,
  \<dots>, \<alpha>\<^sub>n :: s\<^sub>n) t\<close>.  A plain @{command "instance"} command in the
  target body poses a goal stating these type arities.  The target is
  concluded by an @{command_ref (local) "end"} command.

  Note that a list of simultaneous type constructors may be given;
  this corresponds nicely to mutually recursive type definitions, e.g.\
  in Isabelle/HOL.

  \<^descr> @{command "instance"} in an instantiation target body sets
  up a goal stating the type arities claimed at the opening @{command
  "instantiation"}.  The proof would usually proceed by @{method
  intro_classes}, and then establish the characteristic theorems of
  the type classes involved.  After finishing the proof, the
  background theory will be augmented by the proven type arities.

  On the theory level, @{command "instance"}~\<open>t :: (s\<^sub>1, \<dots>,
  s\<^sub>n)s\<close> provides a convenient way to instantiate a type class with no
  need to specify operations: one can continue with the
  instantiation proof immediately.

  \<^descr> @{command "subclass"}~\<open>c\<close> in a class context for class
  \<open>d\<close> sets up a goal stating that class \<open>c\<close> is logically
  contained in class \<open>d\<close>.  After finishing the proof, class
  \<open>d\<close> is proven to be subclass \<open>c\<close> and the locale \<open>c\<close> is interpreted into \<open>d\<close> simultaneously.

  A weakened form of this is available through a further variant of
  @{command instance}:  @{command instance}~\<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close> opens
  a proof that class \<open>c\<^sub>2\<close> implies \<open>c\<^sub>1\<close> without reference
  to the underlying locales;  this is useful if the properties to prove
  the logical connection are not sufficient on the locale level but on
  the theory level.

  \<^descr> @{command "print_classes"} prints all classes in the current
  theory.

  \<^descr> @{command "class_deps"} visualizes classes and their subclass
  relations as a directed acyclic graph. By default, all classes from the
  current theory context are show. This may be restricted by optional bounds
  as follows: @{command "class_deps"}~\<open>upper\<close> or @{command
  "class_deps"}~\<open>upper lower\<close>. A class is visualized, iff it is a
  subclass of some sort from \<open>upper\<close> and a superclass of some sort
  from \<open>lower\<close>.

  \<^descr> @{method intro_classes} repeatedly expands all class
  introduction rules of this theory.  Note that this method usually
  needs not be named explicitly, as it is already included in the
  default proof step (e.g.\ of @{command "proof"}).  In particular,
  instantiation of trivial (syntactic) classes may be performed by a
  single ``@{command ".."}'' proof step.
\<close>


subsection \<open>The class target\<close>

text \<open>
  %FIXME check

  A named context may refer to a locale (cf.\ \secref{sec:target}).
  If this locale is also a class \<open>c\<close>, apart from the common
  locale target behaviour the following happens.

  \<^item> Local constant declarations \<open>g[\<alpha>]\<close> referring to the
  local type parameter \<open>\<alpha>\<close> and local parameters \<open>f[\<alpha>]\<close>
  are accompanied by theory-level constants \<open>g[?\<alpha> :: c]\<close>
  referring to theory-level class operations \<open>f[?\<alpha> :: c]\<close>.

  \<^item> Local theorem bindings are lifted as are assumptions.

  \<^item> Local syntax refers to local operations \<open>g[\<alpha>]\<close> and
  global operations \<open>g[?\<alpha> :: c]\<close> uniformly.  Type inference
  resolves ambiguities.  In rare cases, manual type annotations are
  needed.
\<close>


subsection \<open>Co-regularity of type classes and arities\<close>

text \<open>The class relation together with the collection of
  type-constructor arities must obey the principle of
  \<^emph>\<open>co-regularity\<close> as defined below.

  \<^medskip>
  For the subsequent formulation of co-regularity we assume
  that the class relation is closed by transitivity and reflexivity.
  Moreover the collection of arities \<open>t :: (\<^vec>s)c\<close> is
  completed such that \<open>t :: (\<^vec>s)c\<close> and \<open>c \<subseteq> c'\<close>
  implies \<open>t :: (\<^vec>s)c'\<close> for all such declarations.

  Treating sorts as finite sets of classes (meaning the intersection),
  the class relation \<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close> is extended to sorts as
  follows:
  \[
    \<open>s\<^sub>1 \<subseteq> s\<^sub>2 \<equiv> \<forall>c\<^sub>2 \<in> s\<^sub>2. \<exists>c\<^sub>1 \<in> s\<^sub>1. c\<^sub>1 \<subseteq> c\<^sub>2\<close>
  \]

  This relation on sorts is further extended to tuples of sorts (of
  the same length) in the component-wise way.

  \<^medskip>
  Co-regularity of the class relation together with the
  arities relation means:
  \[
    \<open>t :: (\<^vec>s\<^sub>1)c\<^sub>1 \<Longrightarrow> t :: (\<^vec>s\<^sub>2)c\<^sub>2 \<Longrightarrow> c\<^sub>1 \<subseteq> c\<^sub>2 \<Longrightarrow> \<^vec>s\<^sub>1 \<subseteq> \<^vec>s\<^sub>2\<close>
  \]
  for all such arities.  In other words, whenever the result
  classes of some type-constructor arities are related, then the
  argument sorts need to be related in the same way.

  \<^medskip>
  Co-regularity is a very fundamental property of the
  order-sorted algebra of types.  For example, it entails principle
  types and most general unifiers, e.g.\ see @{cite "nipkow-prehofer"}.
\<close>


section \<open>Unrestricted overloading\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "overloading"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  Isabelle/Pure's definitional schemes support certain forms of
  overloading (see \secref{sec:consts}).  Overloading means that a
  constant being declared as \<open>c :: \<alpha> decl\<close> may be
  defined separately on type instances
  \<open>c :: (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t decl\<close>
  for each type constructor \<open>t\<close>.  At most occasions
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

  \<^descr> @{command "overloading"}~\<open>x\<^sub>1 \<equiv> c\<^sub>1 :: \<tau>\<^sub>1 \<AND> \<dots> x\<^sub>n \<equiv> c\<^sub>n :: \<tau>\<^sub>n \<BEGIN>\<close>
  opens a theory target (cf.\ \secref{sec:target}) which allows to
  specify constants with overloaded definitions.  These are identified
  by an explicitly given mapping from variable names \<open>x\<^sub>i\<close> to
  constants \<open>c\<^sub>i\<close> at particular type instances.  The
  definitions themselves are established using common specification
  tools, using the names \<open>x\<^sub>i\<close> as reference to the
  corresponding constants.  The target is concluded by @{command
  (local) "end"}.

  A \<open>(unchecked)\<close> option disables global dependency checks for
  the corresponding definition, which is occasionally useful for
  exotic overloading (see \secref{sec:consts} for a precise description).
  It is at the discretion of the user to avoid
  malformed theory specifications!
\<close>


section \<open>Incorporating ML code \label{sec:ML}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "SML_file"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "ML_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML_prf"} & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "ML_val"} & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "ML_command"} & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "setup"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "local_setup"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "attribute_setup"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}
  \begin{tabular}{rcll}
    @{attribute_def ML_print_depth} & : & \<open>attribute\<close> & default 10 \\
    @{attribute_def ML_source_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def ML_exception_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
  \end{tabular}

  @{rail \<open>
    (@@{command SML_file} | @@{command ML_file}) @{syntax name}
    ;
    (@@{command ML} | @@{command ML_prf} | @@{command ML_val} |
      @@{command ML_command} | @@{command setup} | @@{command local_setup}) @{syntax text}
    ;
    @@{command attribute_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
  \<close>}

  \<^descr> @{command "SML_file"}~\<open>name\<close> reads and evaluates the
  given Standard ML file.  Top-level SML bindings are stored within
  the theory context; the initial environment is restricted to the
  Standard ML implementation of Poly/ML, without the many add-ons of
  Isabelle/ML.  Multiple @{command "SML_file"} commands may be used to
  build larger Standard ML projects, independently of the regular
  Isabelle/ML environment.

  \<^descr> @{command "ML_file"}~\<open>name\<close> reads and evaluates the
  given ML file.  The current theory context is passed down to the ML
  toplevel and may be modified, using @{ML "Context.>>"} or derived ML
  commands.  Top-level ML bindings are stored within the (global or
  local) theory context.
  
  \<^descr> @{command "ML"}~\<open>text\<close> is similar to @{command
  "ML_file"}, but evaluates directly the given \<open>text\<close>.
  Top-level ML bindings are stored within the (global or local) theory
  context.

  \<^descr> @{command "ML_prf"} is analogous to @{command "ML"} but works
  within a proof context.  Top-level ML bindings are stored within the
  proof context in a purely sequential fashion, disregarding the
  nested proof structure.  ML bindings introduced by @{command
  "ML_prf"} are discarded at the end of the proof.

  \<^descr> @{command "ML_val"} and @{command "ML_command"} are diagnostic
  versions of @{command "ML"}, which means that the context may not be
  updated.  @{command "ML_val"} echos the bindings produced at the ML
  toplevel, but @{command "ML_command"} is silent.
  
  \<^descr> @{command "setup"}~\<open>text\<close> changes the current theory
  context by applying \<open>text\<close>, which refers to an ML expression
  of type @{ML_type "theory -> theory"}.  This enables to initialize
  any object-logic specific tools and packages written in ML, for
  example.

  \<^descr> @{command "local_setup"} is similar to @{command "setup"} for
  a local theory context, and an ML expression of type @{ML_type
  "local_theory -> local_theory"}.  This allows to
  invoke local theory specification packages without going through
  concrete outer syntax, for example.

  \<^descr> @{command "attribute_setup"}~\<open>name = text description\<close>
  defines an attribute in the current context.  The given \<open>text\<close> has to be an ML expression of type
  @{ML_type "attribute context_parser"}, cf.\ basic parsers defined in
  structure @{ML_structure Args} and @{ML_structure Attrib}.

  In principle, attributes can operate both on a given theorem and the
  implicit context, although in practice only one is modified and the
  other serves as parameter.  Here are examples for these two cases:
\<close>

(*<*)experiment begin(*>*)
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
(*<*)end(*>*)

text \<open>
  \<^descr> @{attribute ML_print_depth} controls the printing depth of the ML
  toplevel pretty printer; the precise effect depends on the ML compiler and
  run-time system. Typically the limit should be less than 10. Bigger values
  such as 100--1000 are occasionally useful for debugging.

  \<^descr> @{attribute ML_source_trace} indicates whether the source text that
  is given to the ML compiler should be output: it shows the raw Standard ML
  after expansion of Isabelle/ML antiquotations.

  \<^descr> @{attribute ML_exception_trace} indicates whether the ML run-time
  system should print a detailed stack trace on exceptions. The result is
  dependent on the particular ML compiler version. Note that after Poly/ML
  5.3 some optimizations in the run-time systems may hinder exception
  traces.

  The boundary for the exception trace is the current Isar command
  transactions. It is occasionally better to insert the combinator @{ML
  Runtime.exn_trace} into ML code for debugging @{cite
  "isabelle-implementation"}, closer to the point where it actually
  happens.
\<close>


section \<open>Primitive specification elements\<close>

subsection \<open>Sorts\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "default_sort"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
  \end{matharray}

  @{rail \<open>
    @@{command default_sort} @{syntax sort}
  \<close>}

  \<^descr> @{command "default_sort"}~\<open>s\<close> makes sort \<open>s\<close> the
  new default sort for any type variable that is given explicitly in
  the text, but lacks a sort constraint (wrt.\ the current context).
  Type variables generated by type inference are not affected.

  Usually the default sort is only changed when defining a new
  object-logic.  For example, the default sort in Isabelle/HOL is
  @{class type}, the class of all HOL types.

  When merging theories, the default sorts of the parents are
  logically intersected, i.e.\ the representations as lists of classes
  are joined.
\<close>


subsection \<open>Types \label{sec:types-pure}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "type_synonym"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "typedecl"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  @{rail \<open>
    @@{command type_synonym} (@{syntax typespec} '=' @{syntax type} @{syntax mixfix}?)
    ;
    @@{command typedecl} @{syntax typespec} @{syntax mixfix}?
  \<close>}

  \<^descr> @{command "type_synonym"}~\<open>(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>\<close> introduces a
  \<^emph>\<open>type synonym\<close> \<open>(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t\<close> for the existing type \<open>\<tau>\<close>. Unlike the semantic type definitions in Isabelle/HOL, type synonyms
  are merely syntactic abbreviations without any logical significance.
  Internally, type synonyms are fully expanded.
  
  \<^descr> @{command "typedecl"}~\<open>(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t\<close> declares a new
  type constructor \<open>t\<close>.  If the object-logic defines a base sort
  \<open>s\<close>, then the constructor is declared to operate on that, via
  the axiomatic type-class instance \<open>t :: (s, \<dots>, s)s\<close>.


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
    @{command_def "consts"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "defs"} & : & \<open>theory \<rightarrow> theory\<close> \\
  \end{matharray}

  Definitions essentially express abbreviations within the logic.  The
  simplest form of a definition is \<open>c :: \<sigma> \<equiv> t\<close>, where \<open>c\<close> is a newly declared constant.  Isabelle also allows derived forms
  where the arguments of \<open>c\<close> appear on the left, abbreviating a
  prefix of \<open>\<lambda>\<close>-abstractions, e.g.\ \<open>c \<equiv> \<lambda>x y. t\<close> may be
  written more conveniently as \<open>c x y \<equiv> t\<close>.  Moreover,
  definitions may be weakened by adding arbitrary pre-conditions:
  \<open>A \<Longrightarrow> c x y \<equiv> t\<close>.

  \<^medskip>
  The built-in well-formedness conditions for definitional
  specifications are:

  \<^item> Arguments (on the left-hand side) must be distinct variables.

  \<^item> All variables on the right-hand side must also appear on the
  left-hand side.

  \<^item> All type variables on the right-hand side must also appear on
  the left-hand side; this prohibits \<open>0 :: nat \<equiv> length ([] ::
  \<alpha> list)\<close> for example.

  \<^item> The definition must not be recursive.  Most object-logics
  provide definitional principles that can be used to express
  recursion safely.


  The right-hand side of overloaded definitions may mention overloaded constants
  recursively at type instances corresponding to the immediate
  argument types \<open>\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n\<close>.  Incomplete
  specification patterns impose global constraints on all occurrences,
  e.g.\ \<open>d :: \<alpha> \<times> \<alpha>\<close> on the left-hand side means that all
  corresponding occurrences on some right-hand side need to be an
  instance of this, general \<open>d :: \<alpha> \<times> \<beta>\<close> will be disallowed.

  @{rail \<open>
    @@{command consts} ((@{syntax name} '::' @{syntax type} @{syntax mixfix}?) +)
    ;
    @@{command defs} opt? (@{syntax axmdecl} @{syntax prop} +)
    ;
    opt: '(' @'unchecked'? @'overloaded'? ')'
  \<close>}

  \<^descr> @{command "consts"}~\<open>c :: \<sigma>\<close> declares constant \<open>c\<close> to have any instance of type scheme \<open>\<sigma>\<close>.  The optional
  mixfix annotations may attach concrete syntax to the constants
  declared.
  
  \<^descr> @{command "defs"}~\<open>name: eqn\<close> introduces \<open>eqn\<close>
  as a definitional axiom for some existing constant.
  
  The \<open>(unchecked)\<close> option disables global dependency checks
  for this definition, which is occasionally useful for exotic
  overloading.  It is at the discretion of the user to avoid malformed
  theory specifications!
  
  The \<open>(overloaded)\<close> option declares definitions to be
  potentially overloaded.  Unless this option is given, a warning
  message would be issued for any definitional equation with a more
  special type than that of the corresponding constant declaration.
\<close>


section \<open>Naming existing theorems \label{sec:theorems}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "lemmas"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "named_theorems"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  @{rail \<open>
    @@{command lemmas} (@{syntax thmdef}? @{syntax thmrefs} + @'and')
      @{syntax for_fixes}
    ;
    @@{command named_theorems} (@{syntax name} @{syntax text}? + @'and')
  \<close>}

  \<^descr> @{command "lemmas"}~\<open>a = b\<^sub>1 \<dots> b\<^sub>n\<close>~@{keyword_def
  "for"}~\<open>x\<^sub>1 \<dots> x\<^sub>m\<close> evaluates given facts (with attributes) in
  the current context, which may be augmented by local variables.
  Results are standardized before being stored, i.e.\ schematic
  variables are renamed to enforce index \<open>0\<close> uniformly.

  \<^descr> @{command "named_theorems"}~\<open>name description\<close> declares a
  dynamic fact within the context. The same \<open>name\<close> is used to define
  an attribute with the usual \<open>add\<close>/\<open>del\<close> syntax (e.g.\ see
  \secref{sec:simp-rules}) to maintain the content incrementally, in
  canonical declaration order of the text structure.
\<close>


section \<open>Oracles\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "oracle"} & : & \<open>theory \<rightarrow> theory\<close> & (axiomatic!) \\
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

  \<^descr> @{command "oracle"}~\<open>name = text\<close> turns the given ML
  expression \<open>text\<close> of type @{ML_text "'a -> cterm"} into an
  ML function of type @{ML_text "'a -> thm"}, which is bound to the
  global identifier @{ML_text name}.  This acts like an infinitary
  specification of axioms!  Invoking the oracle only works within the
  scope of the resulting theory.


  See @{file "~~/src/HOL/ex/Iff_Oracle.thy"} for a worked example of
  defining a new primitive rule as oracle, and turning it into a proof
  method.
\<close>


section \<open>Name spaces\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "hide_class"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_type"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_const"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_fact"} & : & \<open>theory \<rightarrow> theory\<close> \\
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

  \<^descr> @{command "hide_class"}~\<open>names\<close> fully removes class
  declarations from a given name space; with the \<open>(open)\<close>
  option, only the unqualified base name is hidden.

  Note that hiding name space accesses has no impact on logical
  declarations --- they remain valid internally.  Entities that are no
  longer accessible to the user are printed with the special qualifier
  ``\<open>??\<close>'' prefixed to the full internal name.

  \<^descr> @{command "hide_type"}, @{command "hide_const"}, and @{command
  "hide_fact"} are similar to @{command "hide_class"}, but hide types,
  constants, and facts, respectively.
\<close>

end

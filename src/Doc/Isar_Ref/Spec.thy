(*:maxLineLen=78:*)

theory Spec
  imports Main Base
begin

chapter \<open>Specifications\<close>

text \<open>
  The Isabelle/Isar theory format integrates specifications and proofs, with
  support for interactive development by continuous document editing. There is
  a separate document preparation system (see \chref{ch:document-prep}), for
  typesetting formal developments together with informal text. The resulting
  hyper-linked PDF documents can be used both for WWW presentation and printed
  copies.

  The Isar proof language (see \chref{ch:proofs}) is embedded into the theory
  language as a proper sub-language. Proof mode is entered by stating some
  \<^theory_text>\<open>theorem\<close> or \<^theory_text>\<open>lemma\<close> at the theory level, and left again with the final
  conclusion (e.g.\ via \<^theory_text>\<open>qed\<close>).
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
  definitions are self-sufficient (e.g.\ \<^theory_text>\<open>fun\<close> in Isabelle/HOL), with
  foundational proofs performed internally. Other definitions require an
  explicit proof as justification (e.g.\ \<^theory_text>\<open>function\<close> and \<^theory_text>\<open>termination\<close> in
  Isabelle/HOL). Plain statements like \<^theory_text>\<open>theorem\<close> or \<^theory_text>\<open>lemma\<close> are merely a
  special case of that, defining a theorem from a given proposition and its
  proof.

  The theory body may be sub-structured by means of \<^emph>\<open>local theory targets\<close>,
  such as \<^theory_text>\<open>locale\<close> and \<^theory_text>\<open>class\<close>. It is also possible to use \<^theory_text>\<open>context begin \<dots>
  end\<close> blocks to delimited a local theory context: a \<^emph>\<open>named context\<close> to
  augment a locale or class specification, or an \<^emph>\<open>unnamed context\<close> to refer
  to local parameters and assumptions that are discharged later. See
  \secref{sec:target} for more details.

  \<^medskip>
  A theory is commenced by the \<^theory_text>\<open>theory\<close> command, which indicates imports of
  previous theories, according to an acyclic foundational order. Before the
  initial \<^theory_text>\<open>theory\<close> command, there may be optional document header material
  (like \<^theory_text>\<open>section\<close> or \<^theory_text>\<open>text\<close>, see \secref{sec:markup}). The document header
  is outside of the formal theory context, though.

  A theory is concluded by a final @{command (global) "end"} command, one that
  does not belong to a local theory target. No further commands may follow
  such a global @{command (global) "end"}.

  \<^rail>\<open>
    @@{command theory} @{syntax system_name}
      @'imports' (@{syntax system_name} +) \<newline>
      keywords? abbrevs? @'begin'
    ;
    keywords: @'keywords' (keyword_decls + @'and')
    ;
    keyword_decls: (@{syntax string} +) ('::' @{syntax name} @{syntax tags})?
    ;
    abbrevs: @'abbrevs' (((text+) '=' (text+)) + @'and')
    ;
    @@{command thy_deps} (thy_bounds thy_bounds?)?
    ;
    thy_bounds: @{syntax name} | '(' (@{syntax name} + @'|') ')'
  \<close>

  \<^descr> \<^theory_text>\<open>theory A imports B\<^sub>1 \<dots> B\<^sub>n begin\<close> starts a new theory \<open>A\<close> based on the
  merge of existing theories \<open>B\<^sub>1 \<dots> B\<^sub>n\<close>. Due to the possibility to import
  more than one ancestor, the resulting theory structure of an Isabelle
  session forms a directed acyclic graph (DAG). Isabelle takes care that
  sources contributing to the development graph are always up-to-date: changed
  files are automatically rechecked whenever a theory header specification is
  processed.

  Empty imports are only allowed in the bootstrap process of the special
  theory \<^theory>\<open>Pure\<close>, which is the start of any other formal development
  based on Isabelle. Regular user theories usually refer to some more complex
  entry point, such as theory \<^theory>\<open>Main\<close> in Isabelle/HOL.

  The @{keyword_def "keywords"} specification declares outer syntax
  (\chref{ch:outer-syntax}) that is introduced in this theory later on (rare
  in end-user applications). Both minor keywords and major keywords of the
  Isar command language need to be specified, in order to make parsing of
  proof documents work properly. Command keywords need to be classified
  according to their structural role in the formal text. Examples may be seen
  in Isabelle/HOL sources itself, such as @{keyword "keywords"}~\<^verbatim>\<open>"typedef"\<close>
  \<open>:: thy_goal_defn\<close> or @{keyword "keywords"}~\<^verbatim>\<open>"datatype"\<close> \<open>:: thy_defn\<close> for
  theory-level definitions with and without proof, respectively. Additional
  @{syntax tags} provide defaults for document preparation
  (\secref{sec:document-markers}).

  The @{keyword_def "abbrevs"} specification declares additional abbreviations
  for syntactic completion. The default for a new keyword is just its name,
  but completion may be avoided by defining @{keyword "abbrevs"} with empty
  text.

  \<^descr> @{command (global) "end"} concludes the current theory definition. Note
  that some other commands, e.g.\ local theory targets \<^theory_text>\<open>locale\<close> or \<^theory_text>\<open>class\<close>
  may involve a \<^theory_text>\<open>begin\<close> that needs to be matched by @{command (local) "end"},
  according to the usual rules for nested blocks.

  \<^descr> \<^theory_text>\<open>thy_deps\<close> visualizes the theory hierarchy as a directed acyclic graph.
  By default, all imported theories are shown. This may be restricted by
  specifying bounds wrt. the theory inclusion relation.
\<close>


section \<open>Local theory targets \label{sec:target}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "context"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def (local) "end"} & : & \<open>local_theory \<rightarrow> theory\<close> \\
    @{keyword_def "private"} \\
    @{keyword_def "qualified"} \\
  \end{matharray}

  A local theory target is a specification context that is managed separately
  within the enclosing theory. Contexts may introduce parameters (fixed
  variables) and assumptions (hypotheses). Definitions and theorems depending
  on the context may be added incrementally later on.

  \<^emph>\<open>Named contexts\<close> refer to locales (cf.\ \secref{sec:locale}) or type
  classes (cf.\ \secref{sec:class}); the name ``\<open>-\<close>'' signifies the global
  theory context.

  \<^emph>\<open>Unnamed contexts\<close> may introduce additional parameters and assumptions, and
  results produced in the context are generalized accordingly. Such auxiliary
  contexts may be nested within other targets, like \<^theory_text>\<open>locale\<close>, \<^theory_text>\<open>class\<close>,
  \<^theory_text>\<open>instantiation\<close>, \<^theory_text>\<open>overloading\<close>.

  \<^rail>\<open>
    @@{command context} @{syntax name} @{syntax_ref "opening"}? @'begin'
    ;
    @@{command context} @{syntax_ref "includes"}? (@{syntax context_elem} * ) @'begin'
    ;
    @{syntax_def target}: '(' @'in' @{syntax name} ')'
  \<close>

  \<^descr> \<^theory_text>\<open>context c bundles begin\<close> opens a named context, by recommencing an existing
  locale or class \<open>c\<close>. Note that locale and class definitions allow to include
  the \<^theory_text>\<open>begin\<close> keyword as well, in order to continue the local theory
  immediately after the initial specification.  Optionally given
  \<open>bundles\<close> only take effect in the surface context within the \<^theory_text>\<open>begin\<close> /
  \<^theory_text>\<open>end\<close> block.

  \<^descr> \<^theory_text>\<open>context bundles elements begin\<close> opens an unnamed context, by extending
  the enclosing global or local theory target by the given declaration bundles
  (\secref{sec:bundle}) and context elements (\<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close> etc.). This
  means any results stemming from definitions and proofs in the extended
  context will be exported into the enclosing target by lifting over extra
  parameters and premises.

  \<^descr> @{command (local) "end"} concludes the current local theory, according to
  the nesting of contexts. Note that a global @{command (global) "end"} has a
  different meaning: it concludes the theory itself (\secref{sec:begin-thy}).

  \<^descr> \<^theory_text>\<open>private\<close> or \<^theory_text>\<open>qualified\<close> may be given as modifiers before any local
  theory command. This restricts name space accesses to the local scope, as
  determined by the enclosing \<^theory_text>\<open>context begin \<dots> end\<close> block. Outside its scope,
  a \<^theory_text>\<open>private\<close> name is inaccessible, and a \<^theory_text>\<open>qualified\<close> name is only
  accessible with some qualification.

  Neither a global \<^theory_text>\<open>theory\<close> nor a \<^theory_text>\<open>locale\<close> target provides a local scope by
  itself: an extra unnamed context is required to use \<^theory_text>\<open>private\<close> or
  \<^theory_text>\<open>qualified\<close> here.

  \<^descr> \<open>(\<close>@{keyword_def "in"}~\<open>c)\<close> given after any local theory command specifies
  an immediate target, e.g.\ ``\<^theory_text>\<open>definition (in c)\<close>'' or
  ``\<^theory_text>\<open>theorem (in c)\<close>''. This works both in a local or global theory context;
  the current target context will be suspended for this command only. Note
  that ``\<^theory_text>\<open>(in -)\<close>'' will always produce a global result independently of the
  current target context.


  Any specification element that operates on \<open>local_theory\<close> according to this
  manual implicitly allows the above target syntax \<^theory_text>\<open>(in c)\<close>, but individual
  syntax diagrams omit that aspect for clarity.

  \<^medskip>
  The exact meaning of results produced within a local theory context depends
  on the underlying target infrastructure (locale, type class etc.). The
  general idea is as follows, considering a context named \<open>c\<close> with parameter
  \<open>x\<close> and assumption \<open>A[x]\<close>.

  Definitions are exported by introducing a global version with additional
  arguments; a syntactic abbreviation links the long form with the abstract
  version of the target context. For example, \<open>a \<equiv> t[x]\<close> becomes \<open>c.a ?x \<equiv>
  t[?x]\<close> at the theory level (for arbitrary \<open>?x\<close>), together with a local
  abbreviation \<open>a \<equiv> c.a x\<close> in the target context (for the fixed parameter
  \<open>x\<close>).

  Theorems are exported by discharging the assumptions and generalizing the
  parameters of the context. For example, \<open>a: B[x]\<close> becomes \<open>c.a: A[?x] \<Longrightarrow>
  B[?x]\<close>, again for arbitrary \<open>?x\<close>.
\<close>


section \<open>Bundled declarations \label{sec:bundle}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "bundle"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command "bundle"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_bundles"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "include"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "including"} & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{keyword_def "includes"} & : & syntax \\
  \end{matharray}

  The outer syntax of fact expressions (\secref{sec:syn-att}) involves
  theorems and attributes, which are evaluated in the context and applied to
  it. Attributes may declare theorems to the context, as in \<open>this_rule [intro]
  that_rule [elim]\<close> for example. Configuration options (\secref{sec:config})
  are special declaration attributes that operate on the context without a
  theorem, as in \<open>[[show_types = false]]\<close> for example.

  Expressions of this form may be defined as \<^emph>\<open>bundled declarations\<close> in the
  context, and included in other situations later on. Including declaration
  bundles augments a local context casually without logical dependencies,
  which is in contrast to locales and locale interpretation
  (\secref{sec:locale}).

  \<^rail>\<open>
    @@{command bundle} @{syntax name}
      ( '=' @{syntax thms} @{syntax for_fixes} | @'begin')
    ;
    @@{command print_bundles} ('!'?)
    ;
    (@@{command include} | @@{command including}) (@{syntax name}+)
    ;
    @{syntax_def "includes"}: @'includes' (@{syntax name}+)
    ;
    @{syntax_def "opening"}: @'opening' (@{syntax name}+)
    ;
    @@{command unbundle} (@{syntax name}+)
  \<close>

  \<^descr> \<^theory_text>\<open>bundle b = decls\<close> defines a bundle of declarations in the current
  context. The RHS is similar to the one of the \<^theory_text>\<open>declare\<close> command. Bundles
  defined in local theory targets are subject to transformations via
  morphisms, when moved into different application contexts; this works
  analogously to any other local theory specification.

  \<^descr> \<^theory_text>\<open>bundle b begin body end\<close> defines a bundle of declarations from the
  \<open>body\<close> of local theory specifications. It may consist of commands that are
  technically equivalent to \<^theory_text>\<open>declare\<close> or \<^theory_text>\<open>declaration\<close>, which also includes
  \<^theory_text>\<open>notation\<close>, for example. Named fact declarations like ``\<^theory_text>\<open>lemmas a [simp] =
  b\<close>'' or ``\<^theory_text>\<open>lemma a [simp]: B \<proof>\<close>'' are also admitted, but the name
  bindings are not recorded in the bundle.

  \<^descr> \<^theory_text>\<open>print_bundles\<close> prints the named bundles that are available in the
  current context; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> \<^theory_text>\<open>include b\<^sub>1 \<dots> b\<^sub>n\<close> activates the declarations from the given bundles
  in a proof body (forward mode). This is analogous to \<^theory_text>\<open>note\<close>
  (\secref{sec:proof-facts}) with the expanded bundles.

  \<^descr> \<^theory_text>\<open>including b\<^sub>1 \<dots> b\<^sub>n\<close> is similar to \<^theory_text>\<open>include\<close>, but works in proof refinement
  (backward mode). This is analogous to \<^theory_text>\<open>using\<close> (\secref{sec:proof-facts})
  with the expanded bundles.

  \<^descr> \<^theory_text>\<open>includes b\<^sub>1 \<dots> b\<^sub>n\<close> is similar to \<^theory_text>\<open>include\<close>, but applies to a
  confined specification context: unnamed \<^theory_text>\<open>context\<close>s and
  long statements of \<^theory_text>\<open>theorem\<close>.

  \<^descr> \<^theory_text>\<open>opening b\<^sub>1 \<dots> b\<^sub>n\<close> is similar to \<^theory_text>\<open>includes\<close>, but applies to
  a named specification context: \<^theory_text>\<open>locale\<close>s, \<^theory_text>\<open>class\<close>es and
  named \<^theory_text>\<open>context\<close>s. The effect is confined to the surface context within the
  specification block itself and the corresponding \<^theory_text>\<open>begin\<close> / \<^theory_text>\<open>end\<close> block.

  \<^descr> \<^theory_text>\<open>unbundle b\<^sub>1 \<dots> b\<^sub>n\<close> activates the declarations from the given bundles in
  the current local theory context. This is analogous to \<^theory_text>\<open>lemmas\<close>
  (\secref{sec:theorems}) with the expanded bundles.


  Here is an artificial example of bundling various configuration options:
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

  Term definitions may either happen within the logic (as equational axioms of
  a certain form (see also \secref{sec:overloading}), or outside of it as
  rewrite system on abstract syntax. The second form is called
  ``abbreviation''.

  \<^rail>\<open>
    @@{command definition} decl? definition
    ;
    @@{command abbreviation} @{syntax mode}? decl? abbreviation
    ;
    @@{command print_abbrevs} ('!'?)
    ;
    decl: @{syntax name} ('::' @{syntax type})? @{syntax mixfix}? @'where'
    ;
    definition: @{syntax thmdecl}? @{syntax prop}
      @{syntax spec_prems} @{syntax for_fixes}
    ;
    abbreviation: @{syntax prop} @{syntax for_fixes}
  \<close>

  \<^descr> \<^theory_text>\<open>definition c where eq\<close> produces an internal definition \<open>c \<equiv> t\<close> according
  to the specification given as \<open>eq\<close>, which is then turned into a proven fact.
  The given proposition may deviate from internal meta-level equality
  according to the rewrite rules declared as @{attribute defn} by the
  object-logic. This usually covers object-level equality \<open>x = y\<close> and
  equivalence \<open>A \<longleftrightarrow> B\<close>. End-users normally need not change the @{attribute
  defn} setup.

  Definitions may be presented with explicit arguments on the LHS, as well as
  additional conditions, e.g.\ \<open>f x y = t\<close> instead of \<open>f \<equiv> \<lambda>x y. t\<close> and \<open>y \<noteq> 0
  \<Longrightarrow> g x y = u\<close> instead of an unrestricted \<open>g \<equiv> \<lambda>x y. u\<close>.

  \<^descr> \<^theory_text>\<open>print_defn_rules\<close> prints the definitional rewrite rules declared via
  @{attribute defn} in the current context.

  \<^descr> \<^theory_text>\<open>abbreviation c where eq\<close> introduces a syntactic constant which is
  associated with a certain term according to the meta-level equality \<open>eq\<close>.

  Abbreviations participate in the usual type-inference process, but are
  expanded before the logic ever sees them. Pretty printing of terms involves
  higher-order rewriting with rules stemming from reverted abbreviations. This
  needs some care to avoid overlapping or looping syntactic replacements!

  The optional \<open>mode\<close> specification restricts output to a particular print
  mode; using ``\<open>input\<close>'' here achieves the effect of one-way abbreviations.
  The mode may also include an ``\<^theory_text>\<open>output\<close>'' qualifier that affects the
  concrete syntax declared for abbreviations, cf.\ \<^theory_text>\<open>syntax\<close> in
  \secref{sec:syn-trans}.

  \<^descr> \<^theory_text>\<open>print_abbrevs\<close> prints all constant abbreviations of the current context;
  the ``\<open>!\<close>'' option indicates extra verbosity.
\<close>


section \<open>Axiomatizations \label{sec:axiomatizations}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & \<open>theory \<rightarrow> theory\<close> & (axiomatic!) \\
  \end{matharray}

  \<^rail>\<open>
    @@{command axiomatization} @{syntax vars}? (@'where' axiomatization)?
    ;
    axiomatization: (@{syntax thmdecl} @{syntax prop} + @'and')
      @{syntax spec_prems} @{syntax for_fixes}
  \<close>

  \<^descr> \<^theory_text>\<open>axiomatization c\<^sub>1 \<dots> c\<^sub>m where \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close> introduces several constants
  simultaneously and states axiomatic properties for these. The constants are
  marked as being specified once and for all, which prevents additional
  specifications for the same constants later on, but it is always possible to
  emit axiomatizations without referring to particular constants. Note that
  lack of precise dependency tracking of axiomatizations may disrupt the
  well-formedness of an otherwise definitional theory.

  Axiomatization is restricted to a global theory context: support for local
  theory targets \secref{sec:target} would introduce an extra dimension of
  uncertainty what the written specifications really are, and make it
  infeasible to argue why they are correct.

  Axiomatic specifications are required when declaring a new logical system
  within Isabelle/Pure, but in an application environment like Isabelle/HOL
  the user normally stays within definitional mechanisms provided by the logic
  and its libraries.
\<close>


section \<open>Generic declarations\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "declaration"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "syntax_declaration"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "declare"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  Arbitrary operations on the background context may be wrapped-up as generic
  declaration elements. Since the underlying concept of local theories may be
  subject to later re-interpretation, there is an additional dependency on a
  morphism that tells the difference of the original declaration context wrt.\
  the application context encountered later on. A fact declaration is an
  important special case: it consists of a theorem which is applied to the
  context by means of an attribute.

  \<^rail>\<open>
    (@@{command declaration} | @@{command syntax_declaration})
      ('(' @'pervasive' ')')? \<newline> @{syntax text}
    ;
    @@{command declare} (@{syntax thms} + @'and')
  \<close>

  \<^descr> \<^theory_text>\<open>declaration d\<close> adds the declaration function \<open>d\<close> of ML type \<^ML_type>\<open>declaration\<close>, to the current local theory under construction. In later
  application contexts, the function is transformed according to the morphisms
  being involved in the interpretation hierarchy.

  If the \<^theory_text>\<open>(pervasive)\<close> option is given, the corresponding declaration is
  applied to all possible contexts involved, including the global background
  theory.

  \<^descr> \<^theory_text>\<open>syntax_declaration\<close> is similar to \<^theory_text>\<open>declaration\<close>, but is meant to affect
  only ``syntactic'' tools by convention (such as notation and type-checking
  information).

  \<^descr> \<^theory_text>\<open>declare thms\<close> declares theorems to the current local theory context. No
  theorem binding is involved here, unlike \<^theory_text>\<open>lemmas\<close> (cf.\
  \secref{sec:theorems}), so \<^theory_text>\<open>declare\<close> only has the effect of applying
  attributes as included in the theorem specification.
\<close>


section \<open>Locales \label{sec:locale}\<close>

text \<open>
  A locale is a functor that maps parameters (including implicit type
  parameters) and a specification to a list of declarations. The syntax of
  locales is modeled after the Isar proof context commands (cf.\
  \secref{sec:proof-context}).

  Locale hierarchies are supported by maintaining a graph of dependencies
  between locale instances in the global theory. Dependencies may be
  introduced through import (where a locale is defined as sublocale of the
  imported instances) or by proving that an existing locale is a sublocale of
  one or several locale instances.

  A locale may be opened with the purpose of appending to its list of
  declarations (cf.\ \secref{sec:target}). When opening a locale declarations
  from all dependencies are collected and are presented as a local theory. In
  this process, which is called \<^emph>\<open>roundup\<close>, redundant locale instances are
  omitted. A locale instance is redundant if it is subsumed by an instance
  encountered earlier. A more detailed description of this process is
  available elsewhere @{cite Ballarin2014}.
\<close>


subsection \<open>Locale expressions \label{sec:locale-expr}\<close>

text \<open>
  A \<^emph>\<open>locale expression\<close> denotes a context composed of instances of existing
  locales. The context consists of the declaration elements from the locale
  instances. Redundant locale instances are omitted according to roundup.

  \<^rail>\<open>
    @{syntax_def locale_expr}: (instance + '+') @{syntax for_fixes}
    ;
    instance: (qualifier ':')? @{syntax name} (pos_insts | named_insts) \<newline>
      rewrites?
    ;
    qualifier: @{syntax name} ('?')?
    ;
    pos_insts: ('_' | @{syntax term})*
    ;
    named_insts: @'where' (@{syntax name} '=' @{syntax term} + @'and')
    ;
    rewrites: @'rewrites' (@{syntax thmdecl}? @{syntax prop} + @'and')
  \<close>

  A locale instance consists of a reference to a locale and either positional
  or named parameter instantiations optionally followed by rewrites clauses.
  Identical instantiations (that is, those
  that instantiate a parameter by itself) may be omitted. The notation ``\<open>_\<close>''
  enables to omit the instantiation for a parameter inside a positional
  instantiation.

  Terms in instantiations are from the context the locale expressions is
  declared in. Local names may be added to this context with the optional
  \<^theory_text>\<open>for\<close> clause. This is useful for shadowing names bound in outer contexts,
  and for declaring syntax. In addition, syntax declarations from one instance
  are effective when parsing subsequent instances of the same expression.

  Instances have an optional qualifier which applies to names in declarations.
  Names include local definitions and theorem names. If present, the qualifier
  itself is either mandatory (default) or non-mandatory (when followed by
  ``\<^verbatim>\<open>?\<close>''). Non-mandatory means that the qualifier may be omitted on input.
  Qualifiers only affect name spaces; they play no role in determining whether
  one locale instance subsumes another.

  Rewrite clauses amend instances with equations that act as rewrite rules.
  This is particularly useful for changing concepts introduced through
  definitions. Rewrite clauses are available only in interpretation commands
  (see \secref{sec:locale-interpretation} below) and must be proved the user.
\<close>


subsection \<open>Locale declarations\<close>

text \<open>
  \begin{tabular}{rcl}
    @{command_def "locale"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "experiment"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
    @{command_def "print_locale"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_locales"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "locale_deps"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{tabular}

  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}
  \<^rail>\<open>
    @@{command locale} @{syntax name} ('=' @{syntax locale})? @'begin'?
    ;
    @@{command experiment} (@{syntax context_elem}*) @'begin'
    ;
    @@{command print_locale} '!'? @{syntax name}
    ;
    @@{command print_locales} ('!'?)
    ;
    @{syntax_def locale}: @{syntax context_elem}+ |
      @{syntax_ref "opening"} ('+' (@{syntax context_elem}+))? |
      @{syntax locale_expr} @{syntax_ref "opening"}? ('+' (@{syntax context_elem}+))?
    ;
    @{syntax_def context_elem}:
      @'fixes' @{syntax vars} |
      @'constrains' (@{syntax name} '::' @{syntax type} + @'and') |
      @'assumes' (@{syntax props} + @'and') |
      @'defines' (@{syntax thmdecl}? @{syntax prop} @{syntax prop_pat}? + @'and') |
      @'notes' (@{syntax thmdef}? @{syntax thms} + @'and')
  \<close>

  \<^descr> \<^theory_text>\<open>locale loc = import opening bundles + body\<close> defines a new locale \<open>loc\<close>
  as a context consisting of a certain view of existing locales (\<open>import\<close>) plus some
  additional elements (\<open>body\<close>) with declaration \<open>bundles\<close> enriching the context
  of the command itself. All \<open>import\<close>, \<open>bundles\<close> and \<open>body\<close> are optional; the
  degenerate form \<^theory_text>\<open>locale loc\<close> defines an empty locale, which may still be
  useful to collect declarations of facts later on. Type-inference on locale
  expressions automatically takes care of the most general typing that the
  combined context elements may acquire.

  The \<open>import\<close> consists of a locale expression; see \secref{sec:locale-expr}
  above. Its \<^theory_text>\<open>for\<close> clause defines the parameters of \<open>import\<close>. These are
  parameters of the defined locale. Locale parameters whose instantiation is
  omitted automatically extend the (possibly empty) \<^theory_text>\<open>for\<close> clause: they are
  inserted at its beginning. This means that these parameters may be referred
  to from within the expression and also in the subsequent context elements
  and provides a notational convenience for the inheritance of parameters in
  locale declarations.

  Declarations from \<open>bundles\<close>, see \secref{sec:bundle}, are effective in the
  entire command including a subsequent \<^theory_text>\<open>begin\<close> / \<^theory_text>\<open>end\<close> block, but they do
  not contribute to the declarations stored in the locale.

  The \<open>body\<close> consists of context elements:

    \<^descr> @{element "fixes"}~\<open>x :: \<tau> (mx)\<close> declares a local parameter of type \<open>\<tau>\<close>
    and mixfix annotation \<open>mx\<close> (both are optional). The special syntax
    declaration ``\<open>(\<close>@{keyword_ref "structure"}\<open>)\<close>'' means that \<open>x\<close> may be
    referenced implicitly in this context.

    \<^descr> @{element "constrains"}~\<open>x :: \<tau>\<close> introduces a type constraint \<open>\<tau>\<close> on the
    local parameter \<open>x\<close>. This element is deprecated. The type constraint
    should be introduced in the \<^theory_text>\<open>for\<close> clause or the relevant @{element
    "fixes"} element.

    \<^descr> @{element "assumes"}~\<open>a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close> introduces local premises, similar
    to \<^theory_text>\<open>assume\<close> within a proof (cf.\ \secref{sec:proof-context}).

    \<^descr> @{element "defines"}~\<open>a: x \<equiv> t\<close> defines a previously declared parameter.
    This is similar to \<^theory_text>\<open>define\<close> within a proof (cf.\
    \secref{sec:proof-context}), but @{element "defines"} is restricted to
    Pure equalities and the defined variable needs to be declared beforehand
    via @{element "fixes"}. The left-hand side of the equation may have
    additional arguments, e.g.\ ``@{element "defines"}~\<open>f x\<^sub>1 \<dots> x\<^sub>n \<equiv> t\<close>'',
    which need to be free in the context.

    \<^descr> @{element "notes"}~\<open>a = b\<^sub>1 \<dots> b\<^sub>n\<close> reconsiders facts within a local
    context. Most notably, this may include arbitrary declarations in any
    attribute specifications included here, e.g.\ a local @{attribute simp}
    rule.

  Both @{element "assumes"} and @{element "defines"} elements contribute to
  the locale specification. When defining an operation derived from the
  parameters, \<^theory_text>\<open>definition\<close> (\secref{sec:term-definitions}) is usually more
  appropriate.

  Note that ``\<^theory_text>\<open>(is p\<^sub>1 \<dots> p\<^sub>n)\<close>'' patterns given in the syntax of @{element
  "assumes"} and @{element "defines"} above are illegal in locale definitions.
  In the long goal format of \secref{sec:goals}, term bindings may be included
  as expected, though.

  \<^medskip>
  Locale specifications are ``closed up'' by turning the given text into a
  predicate definition \<open>loc_axioms\<close> and deriving the original assumptions as
  local lemmas (modulo local definitions). The predicate statement covers only
  the newly specified assumptions, omitting the content of included locale
  expressions. The full cumulative view is only provided on export, involving
  another predicate \<open>loc\<close> that refers to the complete specification text.

  In any case, the predicate arguments are those locale parameters that
  actually occur in the respective piece of text. Also these predicates
  operate at the meta-level in theory, but the locale packages attempts to
  internalize statements according to the object-logic setup (e.g.\ replacing
  \<open>\<And>\<close> by \<open>\<forall>\<close>, and \<open>\<Longrightarrow>\<close> by \<open>\<longrightarrow>\<close> in HOL; see also \secref{sec:object-logic}).
  Separate introduction rules \<open>loc_axioms.intro\<close> and \<open>loc.intro\<close> are provided
  as well.

  \<^descr> \<^theory_text>\<open>experiment body begin\<close> opens an anonymous locale context with private
  naming policy. Specifications in its body are inaccessible from outside.
  This is useful to perform experiments, without polluting the name space.

  \<^descr> \<^theory_text>\<open>print_locale "locale"\<close> prints the contents of the named locale. The
  command omits @{element "notes"} elements by default. Use \<^theory_text>\<open>print_locale!\<close>
  to have them included.

  \<^descr> \<^theory_text>\<open>print_locales\<close> prints the names of all locales of the current theory;
  the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> \<^theory_text>\<open>locale_deps\<close> visualizes all locales and their relations as a Hasse
  diagram. This includes locales defined as type classes (\secref{sec:class}).
\<close>


subsection \<open>Locale interpretation \label{sec:locale-interpretation}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command "interpretation"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "interpret"} & : & \<open>proof(state) | proof(chain) \<rightarrow> proof(prove)\<close> \\
    @{command_def "global_interpretation"} & : & \<open>theory | local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "sublocale"} & : & \<open>theory | local_theory \<rightarrow> proof(prove)\<close> \\
    @{command_def "print_interps"}\<open>\<^sup>*\<close> & :  & \<open>context \<rightarrow>\<close> \\
    @{method_def intro_locales} & : & \<open>method\<close> \\
    @{method_def unfold_locales} & : & \<open>method\<close> \\
    @{attribute_def trace_locales} & : & \mbox{\<open>attribute\<close> \quad default \<open>false\<close>} \\
  \end{matharray}

  Locales may be instantiated, and the resulting instantiated declarations
  added to the current context. This requires proof (of the instantiated
  specification) and is called \<^emph>\<open>locale interpretation\<close>. Interpretation is
  possible within arbitrary local theories (\<^theory_text>\<open>interpretation\<close>), within proof
  bodies (\<^theory_text>\<open>interpret\<close>), into global theories (\<^theory_text>\<open>global_interpretation\<close>) and
  into locales (\<^theory_text>\<open>sublocale\<close>).

  \<^rail>\<open>
    @@{command interpretation} @{syntax locale_expr}
    ;
    @@{command interpret} @{syntax locale_expr}
    ;
    @@{command global_interpretation} @{syntax locale_expr} definitions?
    ;
    @@{command sublocale} (@{syntax name} ('<' | '\<subseteq>'))? @{syntax locale_expr} \<newline>
      definitions?
    ;
    @@{command print_interps} @{syntax name}
    ;

    definitions: @'defines' (@{syntax thmdecl}? @{syntax name} \<newline>
      @{syntax mixfix}? '=' @{syntax term} + @'and');
  \<close>

  The core of each interpretation command is a locale expression \<open>expr\<close>; the
  command generates proof obligations for the instantiated specifications.
  Once these are discharged by the user, instantiated declarations (in
  particular, facts) are added to the context in a post-processing phase, in a
  manner specific to each command.

  Interpretation commands are aware of interpretations that are already
  active: post-processing is achieved through a variant of roundup that takes
  interpretations of the current global or local theory into account. In order
  to simplify the proof obligations according to existing interpretations use
  methods @{method intro_locales} or @{method unfold_locales}.

  Rewrites clauses \<^theory_text>\<open>rewrites eqns\<close> occur within expressions. They amend the
  morphism through which a locale instance is interpreted with rewrite rules,
  also called rewrite morphisms. This is particularly useful for interpreting
  concepts introduced through definitions. The equations must be proved the
  user. To enable syntax of the instantiated locale within the equation, while
  reading a locale expression, equations of a locale instance are read in a
  temporary context where the instance is already activated. If activation
  fails, typically due to duplicate constant declarations, processing falls
  back to reading the equation first.

  Given definitions \<open>defs\<close> produce corresponding definitions in the local
  theory's underlying target \<^emph>\<open>and\<close> amend the morphism with rewrite rules
  stemming from the symmetric of those definitions. Hence these need not be
  proved explicitly the user. Such rewrite definitions are a even more useful
  device for interpreting concepts introduced through definitions, but they
  are only supported for interpretation commands operating in a local theory
  whose implementing target actually supports this.  Note that despite
  the suggestive \<^theory_text>\<open>and\<close> connective, \<open>defs\<close>
  are processed sequentially without mutual recursion.

  \<^descr> \<^theory_text>\<open>interpretation expr\<close> interprets \<open>expr\<close> into a local theory
  such that its lifetime is limited to the current context block (e.g. a
  locale or unnamed context). At the closing @{command end} of the block the
  interpretation and its declarations disappear. Hence facts based on
  interpretation can be established without creating permanent links to the
  interpreted locale instances, as would be the case with @{command
  sublocale}.

  When used on the level of a global theory, there is no end of a current
  context block, hence \<^theory_text>\<open>interpretation\<close> behaves identically to
  \<^theory_text>\<open>global_interpretation\<close> then.

  \<^descr> \<^theory_text>\<open>interpret expr\<close> interprets \<open>expr\<close> into a proof context:
  the interpretation and its declarations disappear when closing the current
  proof block. Note that for \<^theory_text>\<open>interpret\<close> the \<open>eqns\<close> should be explicitly
  universally quantified.

  \<^descr> \<^theory_text>\<open>global_interpretation expr defines defs\<close> interprets \<open>expr\<close>
  into a global theory.

  When adding declarations to locales, interpreted versions of these
  declarations are added to the global theory for all interpretations in the
  global theory as well. That is, interpretations into global theories
  dynamically participate in any declarations added to locales.

  Free variables in the interpreted expression are allowed. They are turned
  into schematic variables in the generated declarations. In order to use a
  free variable whose name is already bound in the context --- for example,
  because a constant of that name exists --- add it to the \<^theory_text>\<open>for\<close> clause.

  \<^descr> \<^theory_text>\<open>sublocale name \<subseteq> expr defines defs\<close> interprets \<open>expr\<close>
  into the locale \<open>name\<close>. A proof that the specification of \<open>name\<close> implies the
  specification of \<open>expr\<close> is required. As in the localized version of the
  theorem command, the proof is in the context of \<open>name\<close>. After the proof
  obligation has been discharged, the locale hierarchy is changed as if \<open>name\<close>
  imported \<open>expr\<close> (hence the name \<^theory_text>\<open>sublocale\<close>). When the context of \<open>name\<close> is
  subsequently entered, traversing the locale hierarchy will involve the
  locale instances of \<open>expr\<close>, and their declarations will be added to the
  context. This makes \<^theory_text>\<open>sublocale\<close> dynamic: extensions of a locale that is
  instantiated in \<open>expr\<close> may take place after the \<^theory_text>\<open>sublocale\<close> declaration and
  still become available in the context. Circular \<^theory_text>\<open>sublocale\<close> declarations
  are allowed as long as they do not lead to infinite chains.

  If interpretations of \<open>name\<close> exist in the current global theory, the command
  adds interpretations for \<open>expr\<close> as well, with the same qualifier, although
  only for fragments of \<open>expr\<close> that are not interpreted in the theory already.

  Rewrites clauses in the expression or rewrite definitions \<open>defs\<close> can help break
  infinite chains induced by circular \<^theory_text>\<open>sublocale\<close> declarations.

  In a named context block the \<^theory_text>\<open>sublocale\<close> command may also be used, but the
  locale argument must be omitted. The command then refers to the locale (or
  class) target of the context block.

  \<^descr> \<^theory_text>\<open>print_interps name\<close> lists all interpretations of locale \<open>name\<close> in the
  current theory or proof context, including those due to a combination of an
  \<^theory_text>\<open>interpretation\<close> or \<^theory_text>\<open>interpret\<close> and one or several \<^theory_text>\<open>sublocale\<close>
  declarations.

  \<^descr> @{method intro_locales} and @{method unfold_locales} repeatedly expand all
  introduction rules of locale predicates of the theory. While @{method
  intro_locales} only applies the \<open>loc.intro\<close> introduction rules and therefore
  does not descend to assumptions, @{method unfold_locales} is more aggressive
  and applies \<open>loc_axioms.intro\<close> as well. Both methods are aware of locale
  specifications entailed by the context, both from target statements, and
  from interpretations (see below). New goals that are entailed by the current
  context are discharged automatically.

  While @{method unfold_locales} is part of the default method for \<^theory_text>\<open>proof\<close>
  and often invoked ``behind the scenes'', @{method intro_locales} helps
  understand which proof obligations originated from which locale instances.
  The latter method is useful while developing proofs but rare in finished
  developments.

  \<^descr> @{attribute trace_locales}, when set to \<open>true\<close>, prints the locale
  instances activated during roundup. Use this when locale commands yield
  obscure errors or for understanding local theories created by complex locale
  hierarchies.

  \begin{warn}
    If a global theory inherits declarations (body elements) for a locale from
    one parent and an interpretation of that locale from another parent, the
    interpretation will not be applied to the declarations.
  \end{warn}

  \begin{warn}
    Since attributes are applied to interpreted theorems, interpretation may
    modify the context of common proof tools, e.g.\ the Simplifier or
    Classical Reasoner. As the behaviour of such tools is \<^emph>\<open>not\<close> stable under
    interpretation morphisms, manual declarations might have to be added to
    the target context of the interpretation to revert such declarations.
  \end{warn}

  \begin{warn}
    An interpretation in a local theory or proof context may subsume previous
    interpretations. This happens if the same specification fragment is
    interpreted twice and the instantiation of the second interpretation is
    more general than the interpretation of the first. The locale package does
    not attempt to remove subsumed interpretations.
  \end{warn}

  \begin{warn}
    While \<^theory_text>\<open>interpretation (in c) \<dots>\<close> is admissible, it is not useful since
    its result is discarded immediately.
  \end{warn}
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

  A class is a particular locale with \<^emph>\<open>exactly one\<close> type variable \<open>\<alpha>\<close>. Beyond
  the underlying locale, a corresponding type class is established which is
  interpreted logically as axiomatic type class @{cite "Wenzel:1997:TPHOL"}
  whose logical content are the assumptions of the locale. Thus, classes
  provide the full generality of locales combined with the commodity of type
  classes (notably type-inference). See @{cite "isabelle-classes"} for a short
  tutorial.

  \<^rail>\<open>
    @@{command class} class_spec @'begin'?
    ;
    class_spec: @{syntax name} '='
      ((@{syntax name} @{syntax_ref "opening"}? '+' (@{syntax context_elem}+)) |
        @{syntax name} @{syntax_ref "opening"}? |
        @{syntax_ref "opening"}? '+' (@{syntax context_elem}+))
    ;
    @@{command instantiation} (@{syntax name} + @'and') '::' @{syntax arity} @'begin'
    ;
    @@{command instance} (() | (@{syntax name} + @'and') '::' @{syntax arity} |
      @{syntax name} ('<' | '\<subseteq>') @{syntax name} )
    ;
    @@{command subclass} @{syntax name}
    ;
    @@{command class_deps} (class_bounds class_bounds?)?
    ;
    class_bounds: @{syntax sort} | '(' (@{syntax sort} + @'|') ')'
  \<close>

  \<^descr> \<^theory_text>\<open>class c = superclasses bundles + body\<close> defines a new class \<open>c\<close>, inheriting from
  \<open>superclasses\<close>. This introduces a locale \<open>c\<close> with import of all locales
  \<open>superclasses\<close>.

  Any @{element "fixes"} in \<open>body\<close> are lifted to the global theory level
  (\<^emph>\<open>class operations\<close> \<open>f\<^sub>1, \<dots>, f\<^sub>n\<close> of class \<open>c\<close>), mapping the local type
  parameter \<open>\<alpha>\<close> to a schematic type variable \<open>?\<alpha> :: c\<close>.

  Likewise, @{element "assumes"} in \<open>body\<close> are also lifted, mapping each local
  parameter \<open>f :: \<tau>[\<alpha>]\<close> to its corresponding global constant \<open>f :: \<tau>[?\<alpha> ::
  c]\<close>. The corresponding introduction rule is provided as
  \<open>c_class_axioms.intro\<close>. This rule should be rarely needed directly --- the
  @{method intro_classes} method takes care of the details of class membership
  proofs.

  Optionally given \<open>bundles\<close> take effect in the surface context within the
  \<open>body\<close> and the potentially following \<^theory_text>\<open>begin\<close> / \<^theory_text>\<open>end\<close> block.

  \<^descr> \<^theory_text>\<open>instantiation t :: (s\<^sub>1, \<dots>, s\<^sub>n)s begin\<close> opens a target (cf.\
  \secref{sec:target}) which allows to specify class operations \<open>f\<^sub>1, \<dots>, f\<^sub>n\<close>
  corresponding to sort \<open>s\<close> at the particular type instance \<open>(\<alpha>\<^sub>1 :: s\<^sub>1, \<dots>,
  \<alpha>\<^sub>n :: s\<^sub>n) t\<close>. A plain \<^theory_text>\<open>instance\<close> command in the target body poses a goal
  stating these type arities. The target is concluded by an @{command_ref
  (local) "end"} command.

  Note that a list of simultaneous type constructors may be given; this
  corresponds nicely to mutually recursive type definitions, e.g.\ in
  Isabelle/HOL.

  \<^descr> \<^theory_text>\<open>instance\<close> in an instantiation target body sets up a goal stating the
  type arities claimed at the opening \<^theory_text>\<open>instantiation\<close>. The proof would
  usually proceed by @{method intro_classes}, and then establish the
  characteristic theorems of the type classes involved. After finishing the
  proof, the background theory will be augmented by the proven type arities.

  On the theory level, \<^theory_text>\<open>instance t :: (s\<^sub>1, \<dots>, s\<^sub>n)s\<close> provides a convenient
  way to instantiate a type class with no need to specify operations: one can
  continue with the instantiation proof immediately.

  \<^descr> \<^theory_text>\<open>subclass c\<close> in a class context for class \<open>d\<close> sets up a goal stating that
  class \<open>c\<close> is logically contained in class \<open>d\<close>. After finishing the proof,
  class \<open>d\<close> is proven to be subclass \<open>c\<close> and the locale \<open>c\<close> is interpreted
  into \<open>d\<close> simultaneously.

  A weakened form of this is available through a further variant of @{command
  instance}: \<^theory_text>\<open>instance c\<^sub>1 \<subseteq> c\<^sub>2\<close> opens a proof that class \<open>c\<^sub>2\<close> implies
  \<open>c\<^sub>1\<close> without reference to the underlying locales; this is useful if the
  properties to prove the logical connection are not sufficient on the locale
  level but on the theory level.

  \<^descr> \<^theory_text>\<open>print_classes\<close> prints all classes in the current theory.

  \<^descr> \<^theory_text>\<open>class_deps\<close> visualizes classes and their subclass relations as a
  directed acyclic graph. By default, all classes from the current theory
  context are show. This may be restricted by optional bounds as follows:
  \<^theory_text>\<open>class_deps upper\<close> or \<^theory_text>\<open>class_deps upper lower\<close>. A class is visualized, iff
  it is a subclass of some sort from \<open>upper\<close> and a superclass of some sort
  from \<open>lower\<close>.

  \<^descr> @{method intro_classes} repeatedly expands all class introduction rules of
  this theory. Note that this method usually needs not be named explicitly, as
  it is already included in the default proof step (e.g.\ of \<^theory_text>\<open>proof\<close>). In
  particular, instantiation of trivial (syntactic) classes may be performed by
  a single ``\<^theory_text>\<open>..\<close>'' proof step.
\<close>


subsection \<open>The class target\<close>

text \<open>
  %FIXME check

  A named context may refer to a locale (cf.\ \secref{sec:target}). If this
  locale is also a class \<open>c\<close>, apart from the common locale target behaviour
  the following happens.

    \<^item> Local constant declarations \<open>g[\<alpha>]\<close> referring to the local type parameter
    \<open>\<alpha>\<close> and local parameters \<open>f[\<alpha>]\<close> are accompanied by theory-level constants
    \<open>g[?\<alpha> :: c]\<close> referring to theory-level class operations \<open>f[?\<alpha> :: c]\<close>.

    \<^item> Local theorem bindings are lifted as are assumptions.

    \<^item> Local syntax refers to local operations \<open>g[\<alpha>]\<close> and global operations
    \<open>g[?\<alpha> :: c]\<close> uniformly. Type inference resolves ambiguities. In rare
    cases, manual type annotations are needed.
\<close>


subsection \<open>Co-regularity of type classes and arities\<close>

text \<open>
  The class relation together with the collection of type-constructor arities
  must obey the principle of \<^emph>\<open>co-regularity\<close> as defined below.

  \<^medskip>
  For the subsequent formulation of co-regularity we assume that the class
  relation is closed by transitivity and reflexivity. Moreover the collection
  of arities \<open>t :: (\<^vec>s)c\<close> is completed such that \<open>t :: (\<^vec>s)c\<close> and
  \<open>c \<subseteq> c'\<close> implies \<open>t :: (\<^vec>s)c'\<close> for all such declarations.

  Treating sorts as finite sets of classes (meaning the intersection), the
  class relation \<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close> is extended to sorts as follows:
  \[
    \<open>s\<^sub>1 \<subseteq> s\<^sub>2 \<equiv> \<forall>c\<^sub>2 \<in> s\<^sub>2. \<exists>c\<^sub>1 \<in> s\<^sub>1. c\<^sub>1 \<subseteq> c\<^sub>2\<close>
  \]

  This relation on sorts is further extended to tuples of sorts (of the same
  length) in the component-wise way.

  \<^medskip>
  Co-regularity of the class relation together with the arities relation
  means:
  \[
    \<open>t :: (\<^vec>s\<^sub>1)c\<^sub>1 \<Longrightarrow> t :: (\<^vec>s\<^sub>2)c\<^sub>2 \<Longrightarrow> c\<^sub>1 \<subseteq> c\<^sub>2 \<Longrightarrow> \<^vec>s\<^sub>1 \<subseteq> \<^vec>s\<^sub>2\<close>
  \]
  for all such arities. In other words, whenever the result classes of some
  type-constructor arities are related, then the argument sorts need to be
  related in the same way.

  \<^medskip>
  Co-regularity is a very fundamental property of the order-sorted algebra of
  types. For example, it entails principal types and most general unifiers,
  e.g.\ see @{cite "nipkow-prehofer"}.
\<close>


section \<open>Overloaded constant definitions \label{sec:overloading}\<close>

text \<open>
  Definitions essentially express abbreviations within the logic. The simplest
  form of a definition is \<open>c :: \<sigma> \<equiv> t\<close>, where \<open>c\<close> is a new constant and \<open>t\<close> is
  a closed term that does not mention \<open>c\<close>. Moreover, so-called \<^emph>\<open>hidden
  polymorphism\<close> is excluded: all type variables in \<open>t\<close> need to occur in its
  type \<open>\<sigma>\<close>.

  \<^emph>\<open>Overloading\<close> means that a constant being declared as \<open>c :: \<alpha> decl\<close> may be
  defined separately on type instances \<open>c :: (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n)\<kappa> decl\<close> for each
  type constructor \<open>\<kappa>\<close>. At most occasions overloading will be used in a
  Haskell-like fashion together with type classes by means of \<^theory_text>\<open>instantiation\<close>
  (see \secref{sec:class}). Sometimes low-level overloading is desirable; this
  is supported by \<^theory_text>\<open>consts\<close> and \<^theory_text>\<open>overloading\<close> explained below.

  The right-hand side of overloaded definitions may mention overloaded
  constants recursively at type instances corresponding to the immediate
  argument types \<open>\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n\<close>. Incomplete specification patterns impose
  global constraints on all occurrences. E.g.\ \<open>d :: \<alpha> \<times> \<alpha>\<close> on the left-hand
  side means that all corresponding occurrences on some right-hand side need
  to be an instance of this, and general \<open>d :: \<alpha> \<times> \<beta>\<close> will be disallowed. Full
  details are given by Kun\v{c}ar @{cite "Kuncar:2015"}.

  \<^medskip>
  The \<^theory_text>\<open>consts\<close> command and the \<^theory_text>\<open>overloading\<close> target provide a convenient
  interface for end-users. Regular specification elements such as @{command
  definition}, @{command inductive}, @{command function} may be used in the
  body. It is also possible to use \<^theory_text>\<open>consts c :: \<sigma>\<close> with later \<^theory_text>\<open>overloading c
  \<equiv> c :: \<sigma>\<close> to keep the declaration and definition of a constant separate.

  \begin{matharray}{rcl}
    @{command_def "consts"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "overloading"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command consts} ((@{syntax name} '::' @{syntax type} @{syntax mixfix}?) +)
    ;
    @@{command overloading} ( spec + ) @'begin'
    ;
    spec: @{syntax name} ( '\<equiv>' | '==' ) @{syntax term} ( '(' @'unchecked' ')' )?
  \<close>

  \<^descr> \<^theory_text>\<open>consts c :: \<sigma>\<close> declares constant \<open>c\<close> to have any instance of type scheme
  \<open>\<sigma>\<close>. The optional mixfix annotations may attach concrete syntax to the
  constants declared.

  \<^descr> \<^theory_text>\<open>overloading x\<^sub>1 \<equiv> c\<^sub>1 :: \<tau>\<^sub>1 \<dots> x\<^sub>n \<equiv> c\<^sub>n :: \<tau>\<^sub>n begin \<dots> end\<close> defines
  a theory target (cf.\ \secref{sec:target}) which allows to specify already
  declared constants via definitions in the body. These are identified by an
  explicitly given mapping from variable names \<open>x\<^sub>i\<close> to constants \<open>c\<^sub>i\<close> at
  particular type instances. The definitions themselves are established using
  common specification tools, using the names \<open>x\<^sub>i\<close> as reference to the
  corresponding constants.

  Option \<^theory_text>\<open>(unchecked)\<close> disables global dependency checks for the
  corresponding definition, which is occasionally useful for exotic
  overloading; this is a form of axiomatic specification. It is at the
  discretion of the user to avoid malformed theory specifications!
\<close>


subsubsection \<open>Example\<close>

consts Length :: "'a \<Rightarrow> nat"

overloading
  Length\<^sub>0 \<equiv> "Length :: unit \<Rightarrow> nat"
  Length\<^sub>1 \<equiv> "Length :: 'a \<times> unit \<Rightarrow> nat"
  Length\<^sub>2 \<equiv> "Length :: 'a \<times> 'b \<times> unit \<Rightarrow> nat"
  Length\<^sub>3 \<equiv> "Length :: 'a \<times> 'b \<times> 'c \<times> unit \<Rightarrow> nat"
begin

fun Length\<^sub>0 :: "unit \<Rightarrow> nat" where "Length\<^sub>0 () = 0"
fun Length\<^sub>1 :: "'a \<times> unit \<Rightarrow> nat" where "Length\<^sub>1 (a, ()) = 1"
fun Length\<^sub>2 :: "'a \<times> 'b \<times> unit \<Rightarrow> nat" where "Length\<^sub>2 (a, b, ()) = 2"
fun Length\<^sub>3 :: "'a \<times> 'b \<times> 'c \<times> unit \<Rightarrow> nat" where "Length\<^sub>3 (a, b, c, ()) = 3"

end

lemma "Length (a, b, c, ()) = 3" by simp
lemma "Length ((a, b), (c, d), ()) = 2" by simp
lemma "Length ((a, b, c, d, e), ()) = 1" by simp


section \<open>Incorporating ML code \label{sec:ML}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "SML_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "SML_file_debug"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "SML_file_no_debug"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML_file_debug"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML_file_no_debug"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "ML_export"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
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
    @{attribute_def ML_debugger} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def ML_exception_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def ML_exception_debugger} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def ML_environment} & : & \<open>attribute\<close> & default \<open>Isabelle\<close> \\
  \end{tabular}

  \<^rail>\<open>
    (@@{command SML_file} |
      @@{command SML_file_debug} |
      @@{command SML_file_no_debug} |
      @@{command ML_file} |
      @@{command ML_file_debug} |
      @@{command ML_file_no_debug}) @{syntax name} ';'?
    ;
    (@@{command ML} | @@{command ML_export} | @@{command ML_prf} |
      @@{command ML_val} | @@{command ML_command} | @@{command setup} |
      @@{command local_setup}) @{syntax text}
    ;
    @@{command attribute_setup} @{syntax name} '=' @{syntax text} @{syntax text}?
  \<close>

  \<^descr> \<^theory_text>\<open>SML_file name\<close> reads and evaluates the given Standard ML file. Top-level
  SML bindings are stored within the (global or local) theory context; the
  initial environment is restricted to the Standard ML implementation of
  Poly/ML, without the many add-ons of Isabelle/ML. Multiple \<^theory_text>\<open>SML_file\<close>
  commands may be used to build larger Standard ML projects, independently of
  the regular Isabelle/ML environment.

  \<^descr> \<^theory_text>\<open>ML_file name\<close> reads and evaluates the given ML file. The current theory
  context is passed down to the ML toplevel and may be modified, using \<^ML>\<open>Context.>>\<close> or derived ML commands. Top-level ML bindings are stored
  within the (global or local) theory context.

  \<^descr> \<^theory_text>\<open>SML_file_debug\<close>, \<^theory_text>\<open>SML_file_no_debug\<close>, \<^theory_text>\<open>ML_file_debug\<close>, and
  \<^theory_text>\<open>ML_file_no_debug\<close> change the @{attribute ML_debugger} option locally while
  the given file is compiled.

  \<^descr> \<^theory_text>\<open>ML\<close> is similar to \<^theory_text>\<open>ML_file\<close>, but evaluates directly the given \<open>text\<close>.
  Top-level ML bindings are stored within the (global or local) theory
  context.

  \<^descr> \<^theory_text>\<open>ML_export\<close> is similar to \<^theory_text>\<open>ML\<close>, but the resulting toplevel bindings are
  exported to the global bootstrap environment of the ML process --- it has
  a lasting effect that cannot be retracted. This allows ML evaluation
  without a formal theory context, e.g. for command-line tools via @{tool
  process} @{cite "isabelle-system"}.

  \<^descr> \<^theory_text>\<open>ML_prf\<close> is analogous to \<^theory_text>\<open>ML\<close> but works within a proof context.
  Top-level ML bindings are stored within the proof context in a purely
  sequential fashion, disregarding the nested proof structure. ML bindings
  introduced by \<^theory_text>\<open>ML_prf\<close> are discarded at the end of the proof.

  \<^descr> \<^theory_text>\<open>ML_val\<close> and \<^theory_text>\<open>ML_command\<close> are diagnostic versions of \<^theory_text>\<open>ML\<close>, which means
  that the context may not be updated. \<^theory_text>\<open>ML_val\<close> echos the bindings produced
  at the ML toplevel, but \<^theory_text>\<open>ML_command\<close> is silent.

  \<^descr> \<^theory_text>\<open>setup "text"\<close> changes the current theory context by applying \<open>text\<close>,
  which refers to an ML expression of type \<^ML_type>\<open>theory -> theory\<close>. This
  enables to initialize any object-logic specific tools and packages written
  in ML, for example.

  \<^descr> \<^theory_text>\<open>local_setup\<close> is similar to \<^theory_text>\<open>setup\<close> for a local theory context, and an
  ML expression of type \<^ML_type>\<open>local_theory -> local_theory\<close>. This allows
  to invoke local theory specification packages without going through concrete
  outer syntax, for example.

  \<^descr> \<^theory_text>\<open>attribute_setup name = "text" description\<close> defines an attribute in the
  current context. The given \<open>text\<close> has to be an ML expression of type
  \<^ML_type>\<open>attribute context_parser\<close>, cf.\ basic parsers defined in
  structure \<^ML_structure>\<open>Args\<close> and \<^ML_structure>\<open>Attrib\<close>.

  In principle, attributes can operate both on a given theorem and the
  implicit context, although in practice only one is modified and the other
  serves as parameter. Here are examples for these two cases:
\<close>

(*<*)experiment begin(*>*)
        attribute_setup my_rule =
          \<open>Attrib.thms >> (fn ths =>
            Thm.rule_attribute ths
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
  \<^descr> @{attribute ML_print_depth} controls the printing depth of the ML toplevel
  pretty printer. Typically the limit should be less than 10. Bigger values
  such as 100--1000 are occasionally useful for debugging.

  \<^descr> @{attribute ML_source_trace} indicates whether the source text that is
  given to the ML compiler should be output: it shows the raw Standard ML
  after expansion of Isabelle/ML antiquotations.

  \<^descr> @{attribute ML_debugger} controls compilation of sources with or without
  debugging information. The global system option @{system_option_ref
  ML_debugger} does the same when building a session image. It is also
  possible use commands like \<^theory_text>\<open>ML_file_debug\<close> etc. The ML debugger is
  explained further in @{cite "isabelle-jedit"}.

  \<^descr> @{attribute ML_exception_trace} indicates whether the ML run-time system
  should print a detailed stack trace on exceptions. The result is dependent
  on various ML compiler optimizations. The boundary for the exception trace
  is the current Isar command transactions: it is occasionally better to
  insert the combinator \<^ML>\<open>Runtime.exn_trace\<close> into ML code for debugging
  @{cite "isabelle-implementation"}, closer to the point where it actually
  happens.

  \<^descr> @{attribute ML_exception_debugger} controls detailed exception trace via
  the Poly/ML debugger, at the cost of extra compile-time and run-time
  overhead. Relevant ML modules need to be compiled beforehand with debugging
  enabled, see @{attribute ML_debugger} above.

  \<^descr> @{attribute ML_environment} determines the named ML environment for
  toplevel declarations, e.g.\ in command \<^theory_text>\<open>ML\<close> or \<^theory_text>\<open>ML_file\<close>. The following
  ML environments are predefined in Isabelle/Pure:

    \<^item> \<open>Isabelle\<close> for Isabelle/ML. It contains all modules of Isabelle/Pure and
    further add-ons, e.g. material from Isabelle/HOL.

    \<^item> \<open>SML\<close> for official Standard ML. It contains only the initial basis
    according to \<^url>\<open>http://sml-family.org/Basis/overview.html\<close>.

  The Isabelle/ML function \<^ML>\<open>ML_Env.setup\<close> defines a new ML environment.
  This is useful to incorporate big SML projects in an isolated name space,
  possibly with variations on ML syntax; the existing setup of
  \<^ML>\<open>ML_Env.SML_operations\<close> follows the official standard.

  It is also possible to move toplevel bindings between ML environments, using
  a notation with ``\<open>>\<close>'' as separator. For example:
\<close>

(*<*)experiment begin(*>*)
        declare [[ML_environment = "Isabelle>SML"]]
        ML \<open>val println = writeln\<close>

        declare [[ML_environment = "SML"]]
        ML \<open>println "test"\<close>

        declare [[ML_environment = "Isabelle"]]
        ML \<open>ML \<open>println\<close> (*bad*) handle ERROR msg => warning msg\<close>
(*<*)end(*>*)


section \<open>Generated files and exported files\<close>

text \<open>
  Write access to the physical file-system is incompatible with the stateless
  model of processing Isabelle documents. To avoid bad effects, the following
  concepts for abstract file-management are provided by Isabelle:

    \<^descr>[Generated files] are stored within the theory context in Isabelle/ML.
    This allows to operate on the content in Isabelle/ML, e.g. via the command
    @{command compile_generated_files}.

    \<^descr>[Exported files] are stored within the session database in
    Isabelle/Scala. This allows to deliver artefacts to external tools, see
    also @{cite "isabelle-system"} for session \<^verbatim>\<open>ROOT\<close> declaration
    \<^theory_text>\<open>export_files\<close>, and @{tool build} option \<^verbatim>\<open>-e\<close>.

  A notable example is the command @{command_ref export_code}
  (\chref{ch:export-code}): it uses both concepts simultaneously.

  File names are hierarchically structured, using a slash as separator. The
  (long) theory name is used as a prefix: the resulting name needs to be
  globally unique.

  \begin{matharray}{rcll}
    @{command_def "generate_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "export_generated_files"} & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "compile_generated_files"} & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "external_file"} & : & \<open>any \<rightarrow> any\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command generate_file} path '=' content
    ;
    path: @{syntax embedded}
    ;
    content: @{syntax embedded}
    ;
    @@{command export_generated_files} (files_in_theory + @'and')
    ;
    files_in_theory: (@'_' | (path+)) (('(' @'in' @{syntax name} ')')?)
    ;
    @@{command compile_generated_files} (files_in_theory + @'and') \<newline>
      (@'external_files' (external_files + @'and'))? \<newline>
      (@'export_files' (export_files + @'and'))? \<newline>
      (@'export_prefix' path)?
    ;
    external_files: (path+) (('(' @'in' path ')')?)
    ;
    export_files: (path+) (executable?)
    ;
    executable: '(' ('exe' | 'executable') ')'
    ;
    @@{command external_file} @{syntax name} ';'?
  \<close>

  \<^descr> \<^theory_text>\<open>generate_file path = content\<close> augments the table of generated files
  within the current theory by a new entry: duplicates are not allowed. The
  name extension determines a pre-existent file-type; the \<open>content\<close> is a
  string that is preprocessed according to rules of this file-type.

  For example, Isabelle/Pure supports \<^verbatim>\<open>.hs\<close> as file-type for Haskell:
  embedded cartouches are evaluated as Isabelle/ML expressions of type
  \<^ML_type>\<open>string\<close>, the result is inlined in Haskell string syntax.

  \<^descr> \<^theory_text>\<open>export_generated_files paths (in thy)\<close> retrieves named generated files
  from the given theory (that needs be reachable via imports of the current
  one). By default, the current theory node is used. Using ``\<^verbatim>\<open>_\<close>''
  (underscore) instead of explicit path names refers to \emph{all} files of a
  theory node.

  The overall list of files is prefixed with the respective (long) theory name
  and exported to the session database. In Isabelle/jEdit the result can be
  browsed via the virtual file-system with prefix ``\<^verbatim>\<open>isabelle-export:\<close>''
  (using the regular file-browser).

  \<^descr> \<^theory_text>\<open>compile_generated_files paths (in thy) where compile_body\<close> retrieves
  named generated files as for \<^theory_text>\<open>export_generated_files\<close> and writes them into
  a temporary directory, such that the \<open>compile_body\<close> may operate on them as
  an ML function of type \<^ML_type>\<open>Path.T -> unit\<close>. This may create further
  files, e.g.\ executables produced by a compiler that is invoked as external
  process (e.g.\ via \<^ML>\<open>Isabelle_System.bash\<close>), or any other files.

  The option ``\<^theory_text>\<open>external_files paths (in base_dir)\<close>'' copies files from the
  physical file-system into the temporary directory, \emph{before} invoking
  \<open>compile_body\<close>. The \<open>base_dir\<close> prefix is removed from each of the \<open>paths\<close>,
  but the remaining sub-directory structure is reconstructed in the target
  directory.

  The option ``\<^theory_text>\<open>export_files paths\<close>'' exports the specified files from the
  temporary directory to the session database, \emph{after} invoking
  \<open>compile_body\<close>. Entries may be decorated with ``\<^theory_text>\<open>(exe)\<close>'' to say that it is
  a platform-specific executable program: the executable file-attribute will
  be set, and on Windows the \<^verbatim>\<open>.exe\<close> file-extension will be included;
  ``\<^theory_text>\<open>(executable)\<close>'' only refers to the file-attribute, without special
  treatment of the \<^verbatim>\<open>.exe\<close> extension.

  The option ``\<^theory_text>\<open>export_prefix path\<close>'' specifies an extra path prefix for all
  exports of \<^theory_text>\<open>export_files\<close> above.

  \<^descr> \<^theory_text>\<open>external_file name\<close> declares the formal dependency on the given file
  name, such that the Isabelle build process knows about it (see also @{cite
  "isabelle-system"}). This is required for any files mentioned in
  \<^theory_text>\<open>compile_generated_files / external_files\<close> above, in order to document
  source dependencies properly. It is also possible to use \<^theory_text>\<open>external_file\<close>
  alone, e.g.\ when other Isabelle/ML tools use \<^ML>\<open>File.read\<close>, without
  specific management of content by the Prover IDE.
\<close>


section \<open>Primitive specification elements\<close>

subsection \<open>Sorts\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "default_sort"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
  \end{matharray}

  \<^rail>\<open>
    @@{command default_sort} @{syntax sort}
  \<close>

  \<^descr> \<^theory_text>\<open>default_sort s\<close> makes sort \<open>s\<close> the new default sort for any type
  variable that is given explicitly in the text, but lacks a sort constraint
  (wrt.\ the current context). Type variables generated by type inference are
  not affected.

  Usually the default sort is only changed when defining a new object-logic.
  For example, the default sort in Isabelle/HOL is \<^class>\<open>type\<close>, the class of
  all HOL types.

  When merging theories, the default sorts of the parents are logically
  intersected, i.e.\ the representations as lists of classes are joined.
\<close>


subsection \<open>Types \label{sec:types-pure}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "type_synonym"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "typedecl"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command type_synonym} (@{syntax typespec} '=' @{syntax type} @{syntax mixfix}?)
    ;
    @@{command typedecl} @{syntax typespec} @{syntax mixfix}?
  \<close>

  \<^descr> \<^theory_text>\<open>type_synonym (\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>\<close> introduces a \<^emph>\<open>type synonym\<close> \<open>(\<alpha>\<^sub>1, \<dots>,
  \<alpha>\<^sub>n) t\<close> for the existing type \<open>\<tau>\<close>. Unlike the semantic type definitions in
  Isabelle/HOL, type synonyms are merely syntactic abbreviations without any
  logical significance. Internally, type synonyms are fully expanded.

  \<^descr> \<^theory_text>\<open>typedecl (\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t\<close> declares a new type constructor \<open>t\<close>. If the
  object-logic defines a base sort \<open>s\<close>, then the constructor is declared to
  operate on that, via the axiomatic type-class instance \<open>t :: (s, \<dots>, s)s\<close>.


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


section \<open>Naming existing theorems \label{sec:theorems}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "lemmas"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "named_theorems"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command lemmas} (@{syntax thmdef}? @{syntax thms} + @'and')
      @{syntax for_fixes}
    ;
    @@{command named_theorems} (@{syntax name} @{syntax text}? + @'and')
  \<close>

  \<^descr> \<^theory_text>\<open>lemmas a = b\<^sub>1 \<dots> b\<^sub>n\<close>~@{keyword_def "for"}~\<open>x\<^sub>1 \<dots> x\<^sub>m\<close> evaluates given
  facts (with attributes) in the current context, which may be augmented by
  local variables. Results are standardized before being stored, i.e.\
  schematic variables are renamed to enforce index \<open>0\<close> uniformly.

  \<^descr> \<^theory_text>\<open>named_theorems name description\<close> declares a dynamic fact within the
  context. The same \<open>name\<close> is used to define an attribute with the usual
  \<open>add\<close>/\<open>del\<close> syntax (e.g.\ see \secref{sec:simp-rules}) to maintain the
  content incrementally, in canonical declaration order of the text structure.
\<close>


section \<open>Oracles \label{sec:oracles}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "oracle"} & : & \<open>theory \<rightarrow> theory\<close> & (axiomatic!) \\
    @{command_def "thm_oracles"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  Oracles allow Isabelle to take advantage of external reasoners such as
  arithmetic decision procedures, model checkers, fast tautology checkers or
  computer algebra systems. Invoked as an oracle, an external reasoner can
  create arbitrary Isabelle theorems.

  It is the responsibility of the user to ensure that the external reasoner is
  as trustworthy as the application requires. Another typical source of errors
  is the linkup between Isabelle and the external tool, not just its concrete
  implementation, but also the required translation between two different
  logical environments.

  Isabelle merely guarantees well-formedness of the propositions being
  asserted, and records within the internal derivation object how presumed
  theorems depend on unproven suppositions. This also includes implicit
  type-class reasoning via the order-sorted algebra of class relations and
  type arities (see also @{command_ref instantiation} and @{command_ref
  instance}).

  \<^rail>\<open>
    @@{command oracle} @{syntax name} '=' @{syntax text}
    ;
    @@{command thm_oracles} @{syntax thms}
  \<close>

  \<^descr> \<^theory_text>\<open>oracle name = "text"\<close> turns the given ML expression \<open>text\<close> of type
  \<^ML_text>\<open>'a -> cterm\<close> into an ML function of type \<^ML_text>\<open>'a -> thm\<close>,
  which is bound to the global identifier \<^ML_text>\<open>name\<close>. This acts like an
  infinitary specification of axioms! Invoking the oracle only works within
  the scope of the resulting theory.

  See \<^file>\<open>~~/src/HOL/Examples/Iff_Oracle.thy\<close> for a worked example of defining
  a new primitive rule as oracle, and turning it into a proof method.

  \<^descr> \<^theory_text>\<open>thm_oracles thms\<close> displays all oracles used in the internal derivation
  of the given theorems; this covers the full graph of transitive
  dependencies.
\<close>


section \<open>Name spaces\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "alias"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "type_alias"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "hide_class"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_type"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_const"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "hide_fact"} & : & \<open>theory \<rightarrow> theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@{command alias} | @{command type_alias}) @{syntax name} '=' @{syntax name}
    ;
    (@{command hide_class} | @{command hide_type} |
      @{command hide_const} | @{command hide_fact}) ('(' @'open' ')')? (@{syntax name} + )
  \<close>

  Isabelle organizes any kind of name declarations (of types, constants,
  theorems etc.) by separate hierarchically structured name spaces. Normally
  the user does not have to control the behaviour of name spaces by hand, yet
  the following commands provide some way to do so.

  \<^descr> \<^theory_text>\<open>alias\<close> and \<^theory_text>\<open>type_alias\<close> introduce aliases for constants and type
  constructors, respectively. This allows adhoc changes to name-space
  accesses.

  \<^descr> \<^theory_text>\<open>type_alias b = c\<close> introduces an alias for an existing type constructor.

  \<^descr> \<^theory_text>\<open>hide_class names\<close> fully removes class declarations from a given name
  space; with the \<open>(open)\<close> option, only the unqualified base name is hidden.

  Note that hiding name space accesses has no impact on logical declarations
  --- they remain valid internally. Entities that are no longer accessible to
  the user are printed with the special qualifier ``\<open>??\<close>'' prefixed to the
  full internal name.

  \<^descr> \<^theory_text>\<open>hide_type\<close>, \<^theory_text>\<open>hide_const\<close>, and \<^theory_text>\<open>hide_fact\<close> are similar to
  \<^theory_text>\<open>hide_class\<close>, but hide types, constants, and facts, respectively.
\<close>

end

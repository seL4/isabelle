(* $Id$ *)

theory Generic
imports CPure
begin

chapter {* Generic tools and packages \label{ch:gen-tools} *}

section {* Specification commands *}

subsection {* Derived specifications *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & \isarkeep{local{\dsh}theory} & (axiomatic!)\\
    @{command_def "definition"} & : & \isarkeep{local{\dsh}theory} \\
    @{attribute_def "defn"} & : & \isaratt \\
    @{command_def "abbreviation"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "print_abbrevs"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "notation"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "no_notation"} & : & \isarkeep{local{\dsh}theory} \\
  \end{matharray}

  These specification mechanisms provide a slightly more abstract view
  than the underlying primitives of @{command "consts"}, @{command
  "defs"} (see \secref{sec:consts}), and @{command "axioms"} (see
  \secref{sec:axms-thms}).  In particular, type-inference is commonly
  available, and result names need not be given.

  \begin{rail}
    'axiomatization' target? fixes? ('where' specs)?
    ;
    'definition' target? (decl 'where')? thmdecl? prop
    ;
    'abbreviation' target? mode? (decl 'where')? prop
    ;
    ('notation' | 'no\_notation') target? mode? (nameref structmixfix + 'and')
    ;

    fixes: ((name ('::' type)? mixfix? | vars) + 'and')
    ;
    specs: (thmdecl? props + 'and')
    ;
    decl: name ('::' type)? mixfix?
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "axiomatization"}~@{text "c\<^sub>1 \<dots> c\<^sub>m
  \<WHERE> \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}] introduces several constants
  simultaneously and states axiomatic properties for these.  The
  constants are marked as being specified once and for all, which
  prevents additional specifications being issued later on.
  
  Note that axiomatic specifications are only appropriate when
  declaring a new logical system.  Normal applications should only use
  definitional mechanisms!

  \item [@{command "definition"}~@{text "c \<WHERE> eq"}] produces an
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
  
  \item [@{command "abbreviation"}~@{text "c \<WHERE> eq"}] introduces
  a syntactic constant which is associated with a certain term
  according to the meta-level equality @{text eq}.
  
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
  
  \item [@{command "print_abbrevs"}] prints all constant abbreviations
  of the current context.
  
  \item [@{command "notation"}~@{text "c (mx)"}] associates mixfix
  syntax with an existing constant or fixed variable.  This is a
  robust interface to the underlying @{command "syntax"} primitive
  (\secref{sec:syn-trans}).  Type declaration and internal syntactic
  representation of the given entity is retrieved from the context.
  
  \item [@{command "no_notation"}] is similar to @{command
  "notation"}, but removes the specified syntax annotation from the
  present context.

  \end{descr}

  All of these specifications support local theory targets (cf.\
  \secref{sec:target}).
*}


subsection {* Generic declarations *}

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
    @{command_def "declaration"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "declare"} & : & \isarkeep{local{\dsh}theory} \\
  \end{matharray}

  \begin{rail}
    'declaration' target? text
    ;
    'declare' target? (thmrefs + 'and')
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "declaration"}~@{text d}] adds the declaration
  function @{text d} of ML type @{ML_type declaration}, to the current
  local theory under construction.  In later application contexts, the
  function is transformed according to the morphisms being involved in
  the interpretation hierarchy.

  \item [@{command "declare"}~@{text thms}] declares theorems to the
  current local theory context.  No theorem binding is involved here,
  unlike @{command "theorems"} or @{command "lemmas"} (cf.\
  \secref{sec:axms-thms}), so @{command "declare"} only has the effect
  of applying attributes as included in the theorem specification.

  \end{descr}
*}


subsection {* Local theory targets \label{sec:target} *}

text {*
  A local theory target is a context managed separately within the
  enclosing theory.  Contexts may introduce parameters (fixed
  variables) and assumptions (hypotheses).  Definitions and theorems
  depending on the context may be added incrementally later on.  Named
  contexts refer to locales (cf.\ \secref{sec:locale}) or type classes
  (cf.\ \secref{sec:class}); the name ``@{text "-"}'' signifies the
  global theory context.

  \begin{matharray}{rcll}
    @{command_def "context"} & : & \isartrans{theory}{local{\dsh}theory} \\
    @{command_def "end"} & : & \isartrans{local{\dsh}theory}{theory} \\
  \end{matharray}

  \indexouternonterm{target}
  \begin{rail}
    'context' name 'begin'
    ;

    target: '(' 'in' name ')'
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "context"}~@{text "c \<BEGIN>"}] recommences an
  existing locale or class context @{text c}.  Note that locale and
  class definitions allow to include the @{keyword_ref "begin"}
  keyword as well, in order to continue the local theory immediately
  after the initial specification.
  
  \item [@{command "end"}] concludes the current local theory and
  continues the enclosing global theory.  Note that a non-local
  @{command "end"} has a different meaning: it concludes the theory
  itself (\secref{sec:begin-thy}).
  
  \item [@{text "(\<IN> c)"}] given after any local theory command
  specifies an immediate target, e.g.\ ``@{command
  "definition"}~@{text "(\<IN> c) \<dots>"}'' or ``@{command
  "theorem"}~@{text "(\<IN> c) \<dots>"}''.  This works both in a local or
  global theory context; the current target context will be suspended
  for this command only.  Note that ``@{text "(\<IN> -)"}'' will
  always produce a global result independently of the current target
  context.

  \end{descr}

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


subsection {* Locales \label{sec:locale} *}

text {*
  Locales are named local contexts, consisting of a list of
  declaration elements that are modeled after the Isar proof context
  commands (cf.\ \secref{sec:proof-context}).
*}


subsubsection {* Locale specifications *}

text {*
  \begin{matharray}{rcl}
    @{command_def "locale"} & : & \isartrans{theory}{local{\dsh}theory} \\
    @{command_def "print_locale"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_locales"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{method_def intro_locales} & : & \isarmeth \\
    @{method_def unfold_locales} & : & \isarmeth \\
  \end{matharray}

  \indexouternonterm{contextexpr}\indexouternonterm{contextelem}
  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}\indexisarelem{includes}
  \begin{rail}
    'locale' ('(open)')? name ('=' localeexpr)? 'begin'?
    ;
    'print\_locale' '!'? localeexpr
    ;
    localeexpr: ((contextexpr '+' (contextelem+)) | contextexpr | (contextelem+))
    ;

    contextexpr: nameref | '(' contextexpr ')' |
    (contextexpr (name mixfix? +)) | (contextexpr + '+')
    ;
    contextelem: fixes | constrains | assumes | defines | notes
    ;
    fixes: 'fixes' ((name ('::' type)? structmixfix? | vars) + 'and')
    ;
    constrains: 'constrains' (name '::' type + 'and')
    ;
    assumes: 'assumes' (thmdecl? props + 'and')
    ;
    defines: 'defines' (thmdecl? prop proppat? + 'and')
    ;
    notes: 'notes' (thmdef? thmrefs + 'and')
    ;
    includes: 'includes' contextexpr
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "locale"}~@{text "loc = import + body"}] defines a
  new locale @{text loc} as a context consisting of a certain view of
  existing locales (@{text import}) plus some additional elements
  (@{text body}).  Both @{text import} and @{text body} are optional;
  the degenerate form @{command "locale"}~@{text loc} defines an empty
  locale, which may still be useful to collect declarations of facts
  later on.  Type-inference on locale expressions automatically takes
  care of the most general typing that the combined context elements
  may acquire.

  The @{text import} consists of a structured context expression,
  consisting of references to existing locales, renamed contexts, or
  merged contexts.  Renaming uses positional notation: @{text "c
  x\<^sub>1 \<dots> x\<^sub>n"} means that (a prefix of) the fixed
  parameters of context @{text c} are named @{text "x\<^sub>1, \<dots>,
  x\<^sub>n"}; a ``@{text _}'' (underscore) means to skip that
  position.  Renaming by default deletes concrete syntax, but new
  syntax may by specified with a mixfix annotation.  An exeption of
  this rule is the special syntax declared with ``@{text
  "(\<STRUCTURE>)"}'' (see below), which is neither deleted nor can it
  be changed.  Merging proceeds from left-to-right, suppressing any
  duplicates stemming from different paths through the import
  hierarchy.

  The @{text body} consists of basic context elements, further context
  expressions may be included as well.

  \begin{descr}

  \item [@{element "fixes"}~@{text "x :: \<tau> (mx)"}] declares a local
  parameter of type @{text \<tau>} and mixfix annotation @{text mx} (both
  are optional).  The special syntax declaration ``@{text
  "(\<STRUCTURE>)"}'' means that @{text x} may be referenced
  implicitly in this context.

  \item [@{element "constrains"}~@{text "x :: \<tau>"}] introduces a type
  constraint @{text \<tau>} on the local parameter @{text x}.

  \item [@{element "assumes"}~@{text "a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}]
  introduces local premises, similar to @{command "assume"} within a
  proof (cf.\ \secref{sec:proof-context}).

  \item [@{element "defines"}~@{text "a: x \<equiv> t"}] defines a previously
  declared parameter.  This is similar to @{command "def"} within a
  proof (cf.\ \secref{sec:proof-context}), but @{element "defines"}
  takes an equational proposition instead of variable-term pair.  The
  left-hand side of the equation may have additional arguments, e.g.\
  ``@{element "defines"}~@{text "f x\<^sub>1 \<dots> x\<^sub>n \<equiv> t"}''.

  \item [@{element "notes"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}]
  reconsiders facts within a local context.  Most notably, this may
  include arbitrary declarations in any attribute specifications
  included here, e.g.\ a local @{attribute simp} rule.

  \item [@{element "includes"}~@{text c}] copies the specified context
  in a statically scoped manner.  Only available in the long goal
  format of \secref{sec:goals}.

  In contrast, the initial @{text import} specification of a locale
  expression maintains a dynamic relation to the locales being
  referenced (benefiting from any later fact declarations in the
  obvious manner).

  \end{descr}
  
  Note that ``@{text "(\<IS> p\<^sub>1 \<dots> p\<^sub>n)"}'' patterns given
  in the syntax of @{element "assumes"} and @{element "defines"} above
  are illegal in locale definitions.  In the long goal format of
  \secref{sec:goals}, term bindings may be included as expected,
  though.
  
  \medskip By default, locale specifications are ``closed up'' by
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
  
  The @{text "(open)"} option of a locale specification prevents both
  the current @{text loc_axioms} and cumulative @{text loc} predicate
  constructions.  Predicates are also omitted for empty specification
  texts.

  \item [@{command "print_locale"}~@{text "import + body"}] prints the
  specified locale expression in a flattened form.  The notable
  special case @{command "print_locale"}~@{text loc} just prints the
  contents of the named locale, but keep in mind that type-inference
  will normalize type variables according to the usual alphabetical
  order.  The command omits @{element "notes"} elements by default.
  Use @{command "print_locale"}@{text "!"} to get them included.

  \item [@{command "print_locales"}] prints the names of all locales
  of the current theory.

  \item [@{method intro_locales} and @{method unfold_locales}]
  repeatedly expand all introduction rules of locale predicates of the
  theory.  While @{method intro_locales} only applies the @{text
  loc.intro} introduction rules and therefore does not decend to
  assumptions, @{method unfold_locales} is more aggressive and applies
  @{text loc_axioms.intro} as well.  Both methods are aware of locale
  specifications entailed by the context, both from target and
  @{element "includes"} statements, and from interpretations (see
  below).  New goals that are entailed by the current context are
  discharged automatically.

  \end{descr}
*}


subsubsection {* Interpretation of locales *}

text {*
  Locale expressions (more precisely, \emph{context expressions}) may
  be instantiated, and the instantiated facts added to the current
  context.  This requires a proof of the instantiated specification
  and is called \emph{locale interpretation}.  Interpretation is
  possible in theories and locales (command @{command
  "interpretation"}) and also within a proof body (command @{command
  "interpret"}).

  \begin{matharray}{rcl}
    @{command_def "interpretation"} & : & \isartrans{theory}{proof(prove)} \\
    @{command_def "interpret"} & : & \isartrans{proof(state) ~|~ proof(chain)}{proof(prove)} \\
    @{command_def "print_interps"}@{text "\<^sup>*"} & : &  \isarkeep{theory~|~proof} \\
  \end{matharray}

  \indexouternonterm{interp}
  \begin{rail}
    'interpretation' (interp | name ('<' | subseteq) contextexpr)
    ;
    'interpret' interp
    ;
    'print\_interps' '!'? name
    ;
    instantiation: ('[' (inst+) ']')?
    ;
    interp: thmdecl? \\ (contextexpr instantiation |
      name instantiation 'where' (thmdecl? prop + 'and'))
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "interpretation"}~@{text "expr insts \<WHERE> eqns"}]

  The first form of @{command "interpretation"} interprets @{text
  expr} in the theory.  The instantiation is given as a list of terms
  @{text insts} and is positional.  All parameters must receive an
  instantiation term --- with the exception of defined parameters.
  These are, if omitted, derived from the defining equation and other
  instantiations.  Use ``@{text _}'' to omit an instantiation term.

  The command generates proof obligations for the instantiated
  specifications (assumes and defines elements).  Once these are
  discharged by the user, instantiated facts are added to the theory
  in a post-processing phase.

  Additional equations, which are unfolded in facts during
  post-processing, may be given after the keyword @{keyword "where"}.
  This is useful for interpreting concepts introduced through
  definition specification elements.  The equations must be proved.
  Note that if equations are present, the context expression is
  restricted to a locale name.

  The command is aware of interpretations already active in the
  theory.  No proof obligations are generated for those, neither is
  post-processing applied to their facts.  This avoids duplication of
  interpreted facts, in particular.  Note that, in the case of a
  locale with import, parts of the interpretation may already be
  active.  The command will only generate proof obligations and
  process facts for new parts.

  The context expression may be preceded by a name and/or attributes.
  These take effect in the post-processing of facts.  The name is used
  to prefix fact names, for example to avoid accidental hiding of
  other facts.  Attributes are applied after attributes of the
  interpreted facts.

  Adding facts to locales has the effect of adding interpreted facts
  to the theory for all active interpretations also.  That is,
  interpretations dynamically participate in any facts added to
  locales.

  \item [@{command "interpretation"}~@{text "name \<subseteq> expr"}]

  This form of the command interprets @{text expr} in the locale
  @{text name}.  It requires a proof that the specification of @{text
  name} implies the specification of @{text expr}.  As in the
  localized version of the theorem command, the proof is in the
  context of @{text name}.  After the proof obligation has been
  dischared, the facts of @{text expr} become part of locale @{text
  name} as \emph{derived} context elements and are available when the
  context @{text name} is subsequently entered.  Note that, like
  import, this is dynamic: facts added to a locale part of @{text
  expr} after interpretation become also available in @{text name}.
  Like facts of renamed context elements, facts obtained by
  interpretation may be accessed by prefixing with the parameter
  renaming (where the parameters are separated by ``@{text _}'').

  Unlike interpretation in theories, instantiation is confined to the
  renaming of parameters, which may be specified as part of the
  context expression @{text expr}.  Using defined parameters in @{text
  name} one may achieve an effect similar to instantiation, though.

  Only specification fragments of @{text expr} that are not already
  part of @{text name} (be it imported, derived or a derived fragment
  of the import) are considered by interpretation.  This enables
  circular interpretations.

  If interpretations of @{text name} exist in the current theory, the
  command adds interpretations for @{text expr} as well, with the same
  prefix and attributes, although only for fragments of @{text expr}
  that are not interpreted in the theory already.

  \item [@{command "interpret"}~@{text "expr insts \<WHERE> eqns"}]
  interprets @{text expr} in the proof context and is otherwise
  similar to interpretation in theories.

  \item [@{command "print_interps"}~@{text loc}] prints the
  interpretations of a particular locale @{text loc} that are active
  in the current context, either theory or proof context.  The
  exclamation point argument triggers printing of \emph{witness}
  theorems justifying interpretations.  These are normally omitted
  from the output.
  
  \end{descr}

  \begin{warn}
    Since attributes are applied to interpreted theorems,
    interpretation may modify the context of common proof tools, e.g.\
    the Simplifier or Classical Reasoner.  Since the behavior of such
    automated reasoning tools is \emph{not} stable under
    interpretation morphisms, manual declarations might have to be
    issued.
  \end{warn}

  \begin{warn}
    An interpretation in a theory may subsume previous
    interpretations.  This happens if the same specification fragment
    is interpreted twice and the instantiation of the second
    interpretation is more general than the interpretation of the
    first.  A warning is issued, since it is likely that these could
    have been generalized in the first place.  The locale package does
    not attempt to remove subsumed interpretations.
  \end{warn}
*}


subsection {* Classes \label{sec:class} *}

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
    @{command_def "class"} & : & \isartrans{theory}{local{\dsh}theory} \\
    @{command_def "instantiation"} & : & \isartrans{theory}{local{\dsh}theory} \\
    @{command_def "instance"} & : & \isartrans{local{\dsh}theory}{local{\dsh}theory} \\
    @{command_def "subclass"} & : & \isartrans{local{\dsh}theory}{local{\dsh}theory} \\
    @{command_def "print_classes"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{method_def intro_classes} & : & \isarmeth \\
  \end{matharray}

  \begin{rail}
    'class' name '=' ((superclassexpr '+' (contextelem+)) | superclassexpr | (contextelem+)) \\
      'begin'?
    ;
    'instantiation' (nameref + 'and') '::' arity 'begin'
    ;
    'instance'
    ;
    'subclass' target? nameref
    ;
    'print\_classes'
    ;

    superclassexpr: nameref | (nameref '+' superclassexpr)
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "class"}~@{text "c = superclasses + body"}] defines
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

  \item [@{command "instantiation"}~@{text "t :: (s\<^sub>1, \<dots>,
  s\<^sub>n) s \<BEGIN>"}] opens a theory target (cf.\
  \secref{sec:target}) which allows to specify class operations @{text
  "f\<^sub>1, \<dots>, f\<^sub>n"} corresponding to sort @{text s} at the
  particular type instance @{text "(\<alpha>\<^sub>1 :: s\<^sub>1, \<dots>,
  \<alpha>\<^sub>n :: s\<^sub>n) t"}.  A plain @{command "instance"} command
  in the target body poses a goal stating these type arities.  The
  target is concluded by an @{command_ref "end"} command.

  Note that a list of simultaneous type constructors may be given;
  this corresponds nicely to mutual recursive type definitions, e.g.\
  in Isabelle/HOL.

  \item [@{command "instance"}] in an instantiation target body sets
  up a goal stating the type arities claimed at the opening @{command
  "instantiation"}.  The proof would usually proceed by @{method
  intro_classes}, and then establish the characteristic theorems of
  the type classes involved.  After finishing the proof, the
  background theory will be augmented by the proven type arities.

  \item [@{command "subclass"}~@{text c}] in a class context for class
  @{text d} sets up a goal stating that class @{text c} is logically
  contained in class @{text d}.  After finishing the proof, class
  @{text d} is proven to be subclass @{text c} and the locale @{text
  c} is interpreted into @{text d} simultaneously.

  \item [@{command "print_classes"}] prints all classes in the current
  theory.

  \item [@{method intro_classes}] repeatedly expands all class
  introduction rules of this theory.  Note that this method usually
  needs not be named explicitly, as it is already included in the
  default proof step (e.g.\ of @{command "proof"}).  In particular,
  instantiation of trivial (syntactic) classes may be performed by a
  single ``@{command ".."}'' proof step.

  \end{descr}
*}


subsubsection {* The class target *}

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


subsection {* Axiomatic type classes \label{sec:axclass} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "axclass"} & : & \isartrans{theory}{theory} \\
    @{command_def "instance"} & : & \isartrans{theory}{proof(prove)} \\
  \end{matharray}

  Axiomatic type classes are Isabelle/Pure's primitive
  \emph{definitional} interface to type classes.  For practical
  applications, you should consider using classes
  (cf.~\secref{sec:classes}) which provide high level interface.

  \begin{rail}
    'axclass' classdecl (axmdecl prop +)
    ;
    'instance' (nameref ('<' | subseteq) nameref | nameref '::' arity)
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "axclass"}~@{text "c \<subseteq> c\<^sub>1, \<dots>, c\<^sub>n
  axms"}] defines an axiomatic type class as the intersection of
  existing classes, with additional axioms holding.  Class axioms may
  not contain more than one type variable.  The class axioms (with
  implicit sort constraints added) are bound to the given names.
  Furthermore a class introduction rule is generated (being bound as
  @{text c_class.intro}); this rule is employed by method @{method
  intro_classes} to support instantiation proofs of this class.
  
  The ``class axioms'' are stored as theorems according to the given
  name specifications, adding @{text "c_class"} as name space prefix;
  the same facts are also stored collectively as @{text
  c_class.axioms}.
  
  \item [@{command "instance"}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} and
  @{command "instance"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n) s"}]
  setup a goal stating a class relation or type arity.  The proof
  would usually proceed by @{method intro_classes}, and then establish
  the characteristic theorems of the type classes involved.  After
  finishing the proof, the theory will be augmented by a type
  signature declaration corresponding to the resulting theorem.

  \end{descr}
*}


subsection {* Arbitrary overloading *}

text {*
  Isabelle/Pure's definitional schemes support certain forms of
  overloading (see \secref{sec:consts}).  At most occassions
  overloading will be used in a Haskell-like fashion together with
  type classes by means of @{command "instantiation"} (see
  \secref{sec:class}).  Sometimes low-level overloading is desirable.
  The @{command "overloading"} target provides a convenient view for
  end-users.

  \begin{matharray}{rcl}
    @{command_def "overloading"} & : & \isartrans{theory}{local{\dsh}theory} \\
  \end{matharray}

  \begin{rail}
    'overloading' \\
    ( string ( '==' | equiv ) term ( '(' 'unchecked' ')' )? + ) 'begin'
  \end{rail}

  \begin{descr}

  \item [@{command "overloading"}~@{text "x\<^sub>1 \<equiv> c\<^sub>1 ::
  \<tau>\<^sub>1 \<AND> \<dots> x\<^sub>n \<equiv> c\<^sub>n :: \<tau>\<^sub>n \<BEGIN>"}]
  opens a theory target (cf.\ \secref{sec:target}) which allows to
  specify constants with overloaded definitions.  These are identified
  by an explicitly given mapping from variable names @{text
  "x\<^sub>i"} to constants @{text "c\<^sub>i"} at particular type
  instances.  The definitions themselves are established using common
  specification tools, using the names @{text "x\<^sub>i"} as
  reference to the corresponding constants.  The target is concluded
  by @{command "end"}.

  A @{text "(unchecked)"} option disables global dependency checks for
  the corresponding definition, which is occasionally useful for
  exotic overloading.  It is at the discretion of the user to avoid
  malformed theory specifications!

  \end{descr}
*}


subsection {* Configuration options *}

text {*
  Isabelle/Pure maintains a record of named configuration options
  within the theory or proof context, with values of type @{ML_type
  bool}, @{ML_type int}, or @{ML_type string}.  Tools may declare
  options in ML, and then refer to these values (relative to the
  context).  Thus global reference variables are easily avoided.  The
  user may change the value of a configuration option by means of an
  associated attribute of the same name.  This form of context
  declaration works particularly well with commands such as @{command
  "declare"} or @{command "using"}.

  For historical reasons, some tools cannot take the full proof
  context into account and merely refer to the background theory.
  This is accommodated by configuration options being declared as
  ``global'', which may not be changed within a local context.

  \begin{matharray}{rcll}
    @{command_def "print_configs"} & : & \isarkeep{theory~|~proof} \\
  \end{matharray}

  \begin{rail}
    name ('=' ('true' | 'false' | int | name))?
  \end{rail}

  \begin{descr}
  
  \item [@{command "print_configs"}] prints the available
  configuration options, with names, types, and current values.
  
  \item [@{text "name = value"}] as an attribute expression modifies
  the named option, with the syntax of the value depending on the
  option's type.  For @{ML_type bool} the default value is @{text
  true}.  Any attempt to change a global option in a local context is
  ignored.

  \end{descr}
*}


section {* Derived proof schemes *}

subsection {* Generalized elimination \label{sec:obtain} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "obtain"} & : & \isartrans{proof(state)}{proof(prove)} \\
    @{command_def "guess"}@{text "\<^sup>*"} & : & \isartrans{proof(state)}{proof(prove)} \\
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

  \begin{rail}
    'obtain' parname? (vars + 'and') 'where' (props + 'and')
    ;
    'guess' (vars + 'and')
    ;
  \end{rail}

  The derived Isar command @{command "obtain"} is defined as follows
  (where @{text "b\<^sub>1, \<dots>, b\<^sub>k"} shall refer to (optional)
  facts indicated for forward chaining).
  \begin{matharray}{l}
    @{text "\<langle>using b\<^sub>1 \<dots> b\<^sub>k\<rangle>"}~~@{command "obtain"}~@{text "x\<^sub>1 \<dots> x\<^sub>m \<WHERE> a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n  \<langle>proof\<rangle> \<equiv>"} \\[1ex]
    \quad @{command "have"}~@{text "\<And>thesis. (\<And>x\<^sub>1 \<dots> x\<^sub>m. \<phi>\<^sub>1 \<Longrightarrow> \<dots> \<phi>\<^sub>n \<Longrightarrow> thesis) \<Longrightarrow> thesis"} \\
    \quad @{command "proof"}~@{text succeed} \\
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


subsection {* Calculational reasoning \label{sec:calculation} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "also"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "finally"} & : & \isartrans{proof(state)}{proof(chain)} \\
    @{command_def "moreover"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "ultimately"} & : & \isartrans{proof(state)}{proof(chain)} \\
    @{command_def "print_trans_rules"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{attribute trans} & : & \isaratt \\
    @{attribute sym} & : & \isaratt \\
    @{attribute symmetric} & : & \isaratt \\
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
    @{command "also"}@{text "\<^sub>n\<^sub>+\<^sub>1"} & \equiv & @{command "note"}~@{text "calculation = trans [OF calculation this]"} \\[0.5ex]
    @{command "finally"} & \equiv & @{command "also"}~@{command "from"}~@{text calculation} \\[0.5ex]
    @{command "moreover"} & \equiv & @{command "note"}~@{text "calculation = calculation this"} \\
    @{command "ultimately"} & \equiv & @{command "moreover"}~@{command "from"}~@{text calculation} \\
  \end{matharray}

  \begin{rail}
    ('also' | 'finally') ('(' thmrefs ')')?
    ;
    'trans' (() | 'add' | 'del')
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "also"}~@{text "(a\<^sub>1 \<dots> a\<^sub>n)"}]
  maintains the auxiliary @{fact calculation} register as follows.
  The first occurrence of @{command "also"} in some calculational
  thread initializes @{fact calculation} by @{fact this}. Any
  subsequent @{command "also"} on the same level of block-structure
  updates @{fact calculation} by some transitivity rule applied to
  @{fact calculation} and @{fact this} (in that order).  Transitivity
  rules are picked from the current context, unless alternative rules
  are given as explicit arguments.

  \item [@{command "finally"}~@{text "(a\<^sub>1 \<dots> a\<^sub>n)"}]
  maintaining @{fact calculation} in the same way as @{command
  "also"}, and concludes the current calculational thread.  The final
  result is exhibited as fact for forward chaining towards the next
  goal. Basically, @{command "finally"} just abbreviates @{command
  "also"}~@{command "from"}~@{fact calculation}.  Typical idioms for
  concluding calculational proofs are ``@{command "finally"}~@{command
  "show"}~@{text ?thesis}~@{command "."}'' and ``@{command
  "finally"}~@{command "have"}~@{text \<phi>}~@{command "."}''.

  \item [@{command "moreover"} and @{command "ultimately"}] are
  analogous to @{command "also"} and @{command "finally"}, but collect
  results only, without applying rules.

  \item [@{command "print_trans_rules"}] prints the list of
  transitivity rules (for calculational commands @{command "also"} and
  @{command "finally"}) and symmetry rules (for the @{attribute
  symmetric} operation and single step elimination patters) of the
  current context.

  \item [@{attribute trans}] declares theorems as transitivity rules.

  \item [@{attribute sym}] declares symmetry rules, as well as
  @{attribute "Pure.elim?"} rules.

  \item [@{attribute symmetric}] resolves a theorem with some rule
  declared as @{attribute sym} in the current context.  For example,
  ``@{command "assume"}~@{text "[symmetric]: x = y"}'' produces a
  swapped fact derived from that assumption.

  In structured proof texts it is often more appropriate to use an
  explicit single-step elimination proof, such as ``@{command
  "assume"}~@{text "x = y"}~@{command "then"}~@{command "have"}~@{text
  "y = x"}~@{command ".."}''.

  \end{descr}
*}


section {* Proof tools *}

subsection {* Miscellaneous methods and attributes \label{sec:misc-meth-att} *}

text {*
  \begin{matharray}{rcl}
    @{method_def unfold} & : & \isarmeth \\
    @{method_def fold} & : & \isarmeth \\
    @{method_def insert} & : & \isarmeth \\[0.5ex]
    @{method_def erule}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def drule}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def frule}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def succeed} & : & \isarmeth \\
    @{method_def fail} & : & \isarmeth \\
  \end{matharray}

  \begin{rail}
    ('fold' | 'unfold' | 'insert') thmrefs
    ;
    ('erule' | 'drule' | 'frule') ('('nat')')? thmrefs
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{method unfold}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} and @{method
  fold}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] expand (or fold back) the
  given definitions throughout all goals; any chained facts provided
  are inserted into the goal and subject to rewriting as well.

  \item [@{method insert}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] inserts
  theorems as facts into all goals of the proof state.  Note that
  current facts indicated for forward chaining are ignored.

  \item [@{method erule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}, @{method
  drule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}, and @{method frule}~@{text
  "a\<^sub>1 \<dots> a\<^sub>n"}] are similar to the basic @{method rule}
  method (see \secref{sec:pure-meth-att}), but apply rules by
  elim-resolution, destruct-resolution, and forward-resolution,
  respectively \cite{isabelle-ref}.  The optional natural number
  argument (default 0) specifies additional assumption steps to be
  performed here.

  Note that these methods are improper ones, mainly serving for
  experimentation and tactic script emulation.  Different modes of
  basic rule application are usually expressed in Isar at the proof
  language level, rather than via implicit proof state manipulations.
  For example, a proper single-step elimination would be done using
  the plain @{method rule} method, with forward chaining of current
  facts.

  \item [@{method succeed}] yields a single (unchanged) result; it is
  the identity of the ``@{text ","}'' method combinator (cf.\
  \secref{sec:syn-meth}).

  \item [@{method fail}] yields an empty result sequence; it is the
  identity of the ``@{text "|"}'' method combinator (cf.\
  \secref{sec:syn-meth}).

  \end{descr}

  \begin{matharray}{rcl}
    @{attribute_def tagged} & : & \isaratt \\
    @{attribute_def untagged} & : & \isaratt \\[0.5ex]
    @{attribute_def THEN} & : & \isaratt \\
    @{attribute_def COMP} & : & \isaratt \\[0.5ex]
    @{attribute_def unfolded} & : & \isaratt \\
    @{attribute_def folded} & : & \isaratt \\[0.5ex]
    @{attribute_def rotated} & : & \isaratt \\
    @{attribute_def (Pure) elim_format} & : & \isaratt \\
    @{attribute_def standard}@{text "\<^sup>*"} & : & \isaratt \\
    @{attribute_def no_vars}@{text "\<^sup>*"} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    'tagged' nameref
    ;
    'untagged' name
    ;
    ('THEN' | 'COMP') ('[' nat ']')? thmref
    ;
    ('unfolded' | 'folded') thmrefs
    ;
    'rotated' ( int )?
  \end{rail}

  \begin{descr}

  \item [@{attribute tagged}~@{text "name arg"} and @{attribute
  untagged}~@{text name}] add and remove \emph{tags} of some theorem.
  Tags may be any list of string pairs that serve as formal comment.
  The first string is considered the tag name, the second its
  argument.  Note that @{attribute untagged} removes any tags of the
  same name.

  \item [@{attribute THEN}~@{text a} and @{attribute COMP}~@{text a}]
  compose rules by resolution.  @{attribute THEN} resolves with the
  first premise of @{text a} (an alternative position may be also
  specified); the @{attribute COMP} version skips the automatic
  lifting process that is normally intended (cf.\ @{ML "op RS"} and
  @{ML "op COMP"} in \cite[\S5]{isabelle-ref}).
  
  \item [@{attribute unfolded}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} and
  @{attribute folded}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] expand and fold
  back again the given definitions throughout a rule.

  \item [@{attribute rotated}~@{text n}] rotate the premises of a
  theorem by @{text n} (default 1).

  \item [@{attribute Pure.elim_format}] turns a destruction rule into
  elimination rule format, by resolving with the rule @{prop "PROP A \<Longrightarrow>
  (PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP B"}.
  
  Note that the Classical Reasoner (\secref{sec:classical}) provides
  its own version of this operation.

  \item [@{attribute standard}] puts a theorem into the standard form
  of object-rules at the outermost theory level.  Note that this
  operation violates the local proof context (including active
  locales).

  \item [@{attribute no_vars}] replaces schematic variables by free
  ones; this is mainly for tuning output of pretty printed theorems.

  \end{descr}
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
    @{method_def rule_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def erule_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def drule_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def frule_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def cut_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def thin_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def subgoal_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def rename_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def rotate_tac}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def tactic}@{text "\<^sup>*"} & : & \isarmeth \\
  \end{matharray}

  \begin{rail}
    ( 'rule\_tac' | 'erule\_tac' | 'drule\_tac' | 'frule\_tac' | 'cut\_tac' | 'thin\_tac' ) goalspec?
    ( insts thmref | thmrefs )
    ;
    'subgoal\_tac' goalspec? (prop +)
    ;
    'rename\_tac' goalspec? (name +)
    ;
    'rotate\_tac' goalspec? int?
    ;
    'tactic' text
    ;

    insts: ((name '=' term) + 'and') 'in'
    ;
  \end{rail}

\begin{descr}

  \item [@{method rule_tac} etc.] do resolution of rules with explicit
  instantiation.  This works the same way as the ML tactics @{ML
  res_inst_tac} etc. (see \cite[\S3]{isabelle-ref}).

  Multiple rules may be only given if there is no instantiation; then
  @{method rule_tac} is the same as @{ML resolve_tac} in ML (see
  \cite[\S3]{isabelle-ref}).

  \item [@{method cut_tac}] inserts facts into the proof state as
  assumption of a subgoal, see also @{ML cut_facts_tac} in
  \cite[\S3]{isabelle-ref}.  Note that the scope of schematic
  variables is spread over the main goal statement.  Instantiations
  may be given as well, see also ML tactic @{ML cut_inst_tac} in
  \cite[\S3]{isabelle-ref}.

  \item [@{method thin_tac}~@{text \<phi>}] deletes the specified
  assumption from a subgoal; note that @{text \<phi>} may contain schematic
  variables.  See also @{ML thin_tac} in \cite[\S3]{isabelle-ref}.

  \item [@{method subgoal_tac}~@{text \<phi>}] adds @{text \<phi>} as an
  assumption to a subgoal.  See also @{ML subgoal_tac} and @{ML
  subgoals_tac} in \cite[\S3]{isabelle-ref}.

  \item [@{method rename_tac}~@{text "x\<^sub>1 \<dots> x\<^sub>n"}] renames
  parameters of a goal according to the list @{text "x\<^sub>1, \<dots>,
  x\<^sub>n"}, which refers to the \emph{suffix} of variables.

  \item [@{method rotate_tac}~@{text n}] rotates the assumptions of a
  goal by @{text n} positions: from right to left if @{text n} is
  positive, and from left to right if @{text n} is negative; the
  default value is 1.  See also @{ML rotate_tac} in
  \cite[\S3]{isabelle-ref}.

  \item [@{method tactic}~@{text "text"}] produces a proof method from
  any ML text of type @{ML_type tactic}.  Apart from the usual ML
  environment and the current implicit theory context, the ML code may
  refer to the following locally bound values:

%FIXME check
{\footnotesize\begin{verbatim}
val ctxt  : Proof.context
val facts : thm list
val thm   : string -> thm
val thms  : string -> thm list
\end{verbatim}}

  Here @{ML_text ctxt} refers to the current proof context, @{ML_text
  facts} indicates any current facts for forward-chaining, and @{ML
  thm}~/~@{ML thms} retrieve named facts (including global theorems)
  from the context.

  \end{descr}
*}


subsection {* The Simplifier \label{sec:simplifier} *}

subsubsection {* Simplification methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def simp} & : & \isarmeth \\
    @{method_def simp_all} & : & \isarmeth \\
  \end{matharray}

  \indexouternonterm{simpmod}
  \begin{rail}
    ('simp' | 'simp\_all') ('!' ?) opt? (simpmod *)
    ;

    opt: '(' ('no\_asm' | 'no\_asm\_simp' | 'no\_asm\_use' | 'asm\_lr' | 'depth\_limit' ':' nat) ')'
    ;
    simpmod: ('add' | 'del' | 'only' | 'cong' (() | 'add' | 'del') |
      'split' (() | 'add' | 'del')) ':' thmrefs
    ;
  \end{rail}

  \begin{descr}

  \item [@{method simp}] invokes the Simplifier, after declaring
  additional rules according to the arguments given.  Note that the
  \railtterm{only} modifier first removes all other rewrite rules,
  congruences, and looper tactics (including splits), and then behaves
  like \railtterm{add}.

  \medskip The \railtterm{cong} modifiers add or delete Simplifier
  congruence rules (see also \cite{isabelle-ref}), the default is to
  add.

  \medskip The \railtterm{split} modifiers add or delete rules for the
  Splitter (see also \cite{isabelle-ref}), the default is to add.
  This works only if the Simplifier method has been properly setup to
  include the Splitter (all major object logics such HOL, HOLCF, FOL,
  ZF do this already).

  \item [@{method simp_all}] is similar to @{method simp}, but acts on
  all goals (backwards from the last to the first one).

  \end{descr}

  By default the Simplifier methods take local assumptions fully into
  account, using equational assumptions in the subsequent
  normalization process, or simplifying assumptions themselves (cf.\
  @{ML asm_full_simp_tac} in \cite[\S10]{isabelle-ref}).  In
  structured proofs this is usually quite well behaved in practice:
  just the local premises of the actual goal are involved, additional
  facts may be inserted via explicit forward-chaining (via @{command
  "then"}, @{command "from"}, @{command "using"} etc.).  The full
  context of premises is only included if the ``@{text "!"}'' (bang)
  argument is given, which should be used with some care, though.

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

  Giving an option ``@{text "(depth_limit: n)"}'' limits the number of
  recursive invocations of the simplifier during conditional
  rewriting.

  \medskip The Splitter package is usually configured to work as part
  of the Simplifier.  The effect of repeatedly applying @{ML
  split_tac} can be simulated by ``@{text "(simp only: split:
  a\<^sub>1 \<dots> a\<^sub>n)"}''.  There is also a separate @{text split}
  method available for single-step case splitting.
*}


subsubsection {* Declaring rules *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_simpset"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{attribute_def simp} & : & \isaratt \\
    @{attribute_def cong} & : & \isaratt \\
    @{attribute_def split} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    ('simp' | 'cong' | 'split') (() | 'add' | 'del')
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "print_simpset"}] prints the collection of rules
  declared to the Simplifier, which is also known as ``simpset''
  internally \cite{isabelle-ref}.

  \item [@{attribute simp}] declares simplification rules.

  \item [@{attribute cong}] declares congruence rules.

  \item [@{attribute split}] declares case split rules.

  \end{descr}
*}


subsubsection {* Simplification procedures *}

text {*
  \begin{matharray}{rcl}
    @{command_def "simproc_setup"} & : & \isarkeep{local{\dsh}theory} \\
    simproc & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    'simproc\_setup' name '(' (term + '|') ')' '=' text \\ ('identifier' (nameref+))?
    ;

    'simproc' (('add' ':')? | 'del' ':') (name+)
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "simproc_setup"}] defines a named simplification
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

  \item [@{text "simproc add: name"} and @{text "simproc del: name"}]
  add or delete named simprocs to the current Simplifier context.  The
  default is to add a simproc.  Note that @{command "simproc_setup"}
  already adds the new simproc to the subsequent context.

  \end{descr}
*}


subsubsection {* Forward simplification *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def simplified} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    'simplified' opt? thmrefs?
    ;

    opt: '(' ('no\_asm' | 'no\_asm\_simp' | 'no\_asm\_use') ')'
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{attribute simplified}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}]
  causes a theorem to be simplified, either by exactly the specified
  rules @{text "a\<^sub>1, \<dots>, a\<^sub>n"}, or the implicit Simplifier
  context if no arguments are given.  The result is fully simplified
  by default, including assumptions and conclusion; the options @{text
  no_asm} etc.\ tune the Simplifier in the same way as the for the
  @{text simp} method.

  Note that forward simplification restricts the simplifier to its
  most basic operation of term rewriting; solver and looper tactics
  \cite{isabelle-ref} are \emph{not} involved here.  The @{text
  simplified} attribute should be only rarely required under normal
  circumstances.

  \end{descr}
*}


subsubsection {* Low-level equational reasoning *}

text {*
  \begin{matharray}{rcl}
    @{method_def subst}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def hypsubst}@{text "\<^sup>*"} & : & \isarmeth \\
    @{method_def split}@{text "\<^sup>*"} & : & \isarmeth \\
  \end{matharray}

  \begin{rail}
    'subst' ('(' 'asm' ')')? ('(' (nat+) ')')? thmref
    ;
    'split' ('(' 'asm' ')')? thmrefs
    ;
  \end{rail}

  These methods provide low-level facilities for equational reasoning
  that are intended for specialized applications only.  Normally,
  single step calculations would be performed in a structured text
  (see also \secref{sec:calculation}), while the Simplifier methods
  provide the canonical way for automated normalization (see
  \secref{sec:simplifier}).

  \begin{descr}

  \item [@{method subst}~@{text eq}] performs a single substitution
  step using rule @{text eq}, which may be either a meta or object
  equality.

  \item [@{method subst}~@{text "(asm) eq"}] substitutes in an
  assumption.

  \item [@{method subst}~@{text "(i \<dots> j) eq"}] performs several
  substitutions in the conclusion. The numbers @{text i} to @{text j}
  indicate the positions to substitute at.  Positions are ordered from
  the top of the term tree moving down from left to right. For
  example, in @{text "(a + b) + (c + d)"} there are three positions
  where commutativity of @{text "+"} is applicable: 1 refers to the
  whole term, 2 to @{text "a + b"} and 3 to @{text "c + d"}.

  If the positions in the list @{text "(i \<dots> j)"} are non-overlapping
  (e.g.\ @{text "(2 3)"} in @{text "(a + b) + (c + d)"}) you may
  assume all substitutions are performed simultaneously.  Otherwise
  the behaviour of @{text subst} is not specified.

  \item [@{method subst}~@{text "(asm) (i \<dots> j) eq"}] performs the
  substitutions in the assumptions.  Positions @{text "1 \<dots> i\<^sub>1"}
  refer to assumption 1, positions @{text "i\<^sub>1 + 1 \<dots> i\<^sub>2"}
  to assumption 2, and so on.

  \item [@{method hypsubst}] performs substitution using some
  assumption; this only works for equations of the form @{text "x =
  t"} where @{text x} is a free or bound variable.

  \item [@{method split}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] performs
  single-step case splitting using the given rules.  By default,
  splitting is performed in the conclusion of a goal; the @{text
  "(asm)"} option indicates to operate on assumptions instead.
  
  Note that the @{method simp} method already involves repeated
  application of split rules as declared in the current context.

  \end{descr}
*}


subsection {* The Classical Reasoner \label{sec:classical} *}

subsubsection {* Basic methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def rule} & : & \isarmeth \\
    @{method_def contradiction} & : & \isarmeth \\
    @{method_def intro} & : & \isarmeth \\
    @{method_def elim} & : & \isarmeth \\
  \end{matharray}

  \begin{rail}
    ('rule' | 'intro' | 'elim') thmrefs?
    ;
  \end{rail}

  \begin{descr}

  \item [@{method rule}] as offered by the Classical Reasoner is a
  refinement over the primitive one (see \secref{sec:pure-meth-att}).
  Both versions essentially work the same, but the classical version
  observes the classical rule context in addition to that of
  Isabelle/Pure.

  Common object logics (HOL, ZF, etc.) declare a rich collection of
  classical rules (even if these would qualify as intuitionistic
  ones), but only few declarations to the rule context of
  Isabelle/Pure (\secref{sec:pure-meth-att}).

  \item [@{method contradiction}] solves some goal by contradiction,
  deriving any result from both @{text "\<not> A"} and @{text A}.  Chained
  facts, which are guaranteed to participate, may appear in either
  order.

  \item [@{attribute intro} and @{attribute elim}] repeatedly refine
  some goal by intro- or elim-resolution, after having inserted any
  chained facts.  Exactly the rules given as arguments are taken into
  account; this allows fine-tuned decomposition of a proof problem, in
  contrast to common automated tools.

  \end{descr}
*}


subsubsection {* Automated methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def blast} & : & \isarmeth \\
    @{method_def fast} & : & \isarmeth \\
    @{method_def slow} & : & \isarmeth \\
    @{method_def best} & : & \isarmeth \\
    @{method_def safe} & : & \isarmeth \\
    @{method_def clarify} & : & \isarmeth \\
  \end{matharray}

  \indexouternonterm{clamod}
  \begin{rail}
    'blast' ('!' ?) nat? (clamod *)
    ;
    ('fast' | 'slow' | 'best' | 'safe' | 'clarify') ('!' ?) (clamod *)
    ;

    clamod: (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del') ':' thmrefs
    ;
  \end{rail}

  \begin{descr}

  \item [@{method blast}] refers to the classical tableau prover (see
  @{ML blast_tac} in \cite[\S11]{isabelle-ref}).  The optional
  argument specifies a user-supplied search bound (default 20).

  \item [@{method fast}, @{method slow}, @{method best}, @{method
  safe}, and @{method clarify}] refer to the generic classical
  reasoner.  See @{ML fast_tac}, @{ML slow_tac}, @{ML best_tac}, @{ML
  safe_tac}, and @{ML clarify_tac} in \cite[\S11]{isabelle-ref} for
  more information.

  \end{descr}

  Any of the above methods support additional modifiers of the context
  of classical rules.  Their semantics is analogous to the attributes
  given before.  Facts provided by forward chaining are inserted into
  the goal before commencing proof search.  The ``@{text
  "!"}''~argument causes the full context of assumptions to be
  included as well.
*}


subsubsection {* Combined automated methods \label{sec:clasimp} *}

text {*
  \begin{matharray}{rcl}
    @{method_def auto} & : & \isarmeth \\
    @{method_def force} & : & \isarmeth \\
    @{method_def clarsimp} & : & \isarmeth \\
    @{method_def fastsimp} & : & \isarmeth \\
    @{method_def slowsimp} & : & \isarmeth \\
    @{method_def bestsimp} & : & \isarmeth \\
  \end{matharray}

  \indexouternonterm{clasimpmod}
  \begin{rail}
    'auto' '!'? (nat nat)? (clasimpmod *)
    ;
    ('force' | 'clarsimp' | 'fastsimp' | 'slowsimp' | 'bestsimp') '!'? (clasimpmod *)
    ;

    clasimpmod: ('simp' (() | 'add' | 'del' | 'only') |
      ('cong' | 'split') (() | 'add' | 'del') |
      'iff' (((() | 'add') '?'?) | 'del') |
      (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del')) ':' thmrefs
  \end{rail}

  \begin{descr}

  \item [@{method auto}, @{method force}, @{method clarsimp}, @{method
  fastsimp}, @{method slowsimp}, and @{method bestsimp}] provide
  access to Isabelle's combined simplification and classical reasoning
  tactics.  These correspond to @{ML auto_tac}, @{ML force_tac}, @{ML
  clarsimp_tac}, and Classical Reasoner tactics with the Simplifier
  added as wrapper, see \cite[\S11]{isabelle-ref} for more
  information.  The modifier arguments correspond to those given in
  \secref{sec:simplifier} and \secref{sec:classical}.  Just note that
  the ones related to the Simplifier are prefixed by \railtterm{simp}
  here.

  Facts provided by forward chaining are inserted into the goal before
  doing the search.  The ``@{text "!"}'' argument causes the full
  context of assumptions to be included as well.

  \end{descr}
*}


subsubsection {* Declaring rules *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_claset"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{attribute_def intro} & : & \isaratt \\
    @{attribute_def elim} & : & \isaratt \\
    @{attribute_def dest} & : & \isaratt \\
    @{attribute_def rule} & : & \isaratt \\
    @{attribute_def iff} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    ('intro' | 'elim' | 'dest') ('!' | () | '?') nat?
    ;
    'rule' 'del'
    ;
    'iff' (((() | 'add') '?'?) | 'del')
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "print_claset"}] prints the collection of rules
  declared to the Classical Reasoner, which is also known as
  ``claset'' internally \cite{isabelle-ref}.
  
  \item [@{attribute intro}, @{attribute elim}, and @{attribute dest}]
  declare introduction, elimination, and destruction rules,
  respectively.  By default, rules are considered as \emph{unsafe}
  (i.e.\ not applied blindly without backtracking), while ``@{text
  "!"}'' classifies as \emph{safe}.  Rule declarations marked by
  ``@{text "?"}'' coincide with those of Isabelle/Pure, cf.\
  \secref{sec:pure-meth-att} (i.e.\ are only applied in single steps
  of the @{method rule} method).  The optional natural number
  specifies an explicit weight argument, which is ignored by automated
  tools, but determines the search order of single rule steps.

  \item [@{attribute rule}~@{text del}] deletes introduction,
  elimination, or destruction rules from the context.

  \item [@{attribute iff}] declares logical equivalences to the
  Simplifier and the Classical reasoner at the same time.
  Non-conditional rules result in a ``safe'' introduction and
  elimination pair; conditional ones are considered ``unsafe''.  Rules
  with negative conclusion are automatically inverted (using @{text
  "\<not>"}-elimination internally).

  The ``@{text "?"}'' version of @{attribute iff} declares rules to
  the Isabelle/Pure context only, and omits the Simplifier
  declaration.

  \end{descr}
*}


subsubsection {* Classical operations *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def swapped} & : & \isaratt \\
  \end{matharray}

  \begin{descr}

  \item [@{attribute swapped}] turns an introduction rule into an
  elimination, by resolving with the classical swap principle @{text
  "(\<not> B \<Longrightarrow> A) \<Longrightarrow> (\<not> A \<Longrightarrow> B)"}.

  \end{descr}
*}


subsection {* Proof by cases and induction \label{sec:cases-induct} *}

subsubsection {* Rule contexts *}

text {*
  \begin{matharray}{rcl}
    @{command_def "case"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "print_cases"}@{text "\<^sup>*"} & : & \isarkeep{proof} \\
    @{attribute_def case_names} & : & \isaratt \\
    @{attribute_def case_conclusion} & : & \isaratt \\
    @{attribute_def params} & : & \isaratt \\
    @{attribute_def consumes} & : & \isaratt \\
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

  \begin{rail}
    'case' (caseref | '(' caseref ((name | underscore) +) ')')
    ;
    caseref: nameref attributes?
    ;

    'case\_names' (name +)
    ;
    'case\_conclusion' name (name *)
    ;
    'params' ((name *) + 'and')
    ;
    'consumes' nat?
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "case"}~@{text "(c x\<^sub>1 \<dots> x\<^sub>m)"}]
  invokes a named local context @{text "c: x\<^sub>1, \<dots>, x\<^sub>m,
  \<phi>\<^sub>1, \<dots>, \<phi>\<^sub>m"}, as provided by an appropriate
  proof method (such as @{method_ref cases} and @{method_ref induct}).
  The command ``@{command "case"}~@{text "(c x\<^sub>1 \<dots>
  x\<^sub>m)"}'' abbreviates ``@{command "fix"}~@{text "x\<^sub>1 \<dots>
  x\<^sub>m"}~@{command "assume"}~@{text "c: \<phi>\<^sub>1 \<dots>
  \<phi>\<^sub>n"}''.

  \item [@{command "print_cases"}] prints all local contexts of the
  current state, using Isar proof language notation.
  
  \item [@{attribute case_names}~@{text "c\<^sub>1 \<dots> c\<^sub>k"}]
  declares names for the local contexts of premises of a theorem;
  @{text "c\<^sub>1, \<dots>, c\<^sub>k"} refers to the \emph{suffix} of the
  list of premises.
  
  \item [@{attribute case_conclusion}~@{text "c d\<^sub>1 \<dots>
  d\<^sub>k"}] declares names for the conclusions of a named premise
  @{text c}; here @{text "d\<^sub>1, \<dots>, d\<^sub>k"} refers to the
  prefix of arguments of a logical formula built by nesting a binary
  connective (e.g.\ @{text "\<or>"}).
  
  Note that proof methods such as @{method induct} and @{method
  coinduct} already provide a default name for the conclusion as a
  whole.  The need to name subformulas only arises with cases that
  split into several sub-cases, as in common co-induction rules.

  \item [@{attribute params}~@{text "p\<^sub>1 \<dots> p\<^sub>m \<AND> \<dots>
  q\<^sub>1 \<dots> q\<^sub>n"}] renames the innermost parameters of
  premises @{text "1, \<dots>, n"} of some theorem.  An empty list of names
  may be given to skip positions, leaving the present parameters
  unchanged.
  
  Note that the default usage of case rules does \emph{not} directly
  expose parameters to the proof context.
  
  \item [@{attribute consumes}~@{text n}] declares the number of
  ``major premises'' of a rule, i.e.\ the number of facts to be
  consumed when it is applied by an appropriate proof method.  The
  default value of @{attribute consumes} is @{text "n = 1"}, which is
  appropriate for the usual kind of cases and induction rules for
  inductive sets (cf.\ \secref{sec:hol-inductive}).  Rules without any
  @{attribute consumes} declaration given are treated as if
  @{attribute consumes}~@{text 0} had been specified.
  
  Note that explicit @{attribute consumes} declarations are only
  rarely needed; this is already taken care of automatically by the
  higher-level @{attribute cases}, @{attribute induct}, and
  @{attribute coinduct} declarations.

  \end{descr}
*}


subsubsection {* Proof methods *}

text {*
  \begin{matharray}{rcl}
    @{method_def cases} & : & \isarmeth \\
    @{method_def induct} & : & \isarmeth \\
    @{method_def coinduct} & : & \isarmeth \\
  \end{matharray}

  The @{method cases}, @{method induct}, and @{method coinduct}
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

  \begin{rail}
    'cases' (insts * 'and') rule?
    ;
    'induct' (definsts * 'and') \\ arbitrary? taking? rule?
    ;
    'coinduct' insts taking rule?
    ;

    rule: ('type' | 'pred' | 'set') ':' (nameref +) | 'rule' ':' (thmref +)
    ;
    definst: name ('==' | equiv) term | inst
    ;
    definsts: ( definst *)
    ;
    arbitrary: 'arbitrary' ':' ((term *) 'and' +)
    ;
    taking: 'taking' ':' insts
    ;
  \end{rail}

  \begin{descr}

  \item [@{method cases}~@{text "insts R"}] applies method @{method
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
  last premise (it is usually the same for all cases).

  \item [@{method induct}~@{text "insts R"}] is analogous to the
  @{method cases} method, but refers to induction rules, which are
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
  @{text t} need to be fixed (see below).
  
  The optional ``@{text "arbitrary: x\<^sub>1 \<dots> x\<^sub>m"}''
  specification generalizes variables @{text "x\<^sub>1, \<dots>,
  x\<^sub>m"} of the original goal before applying induction.  Thus
  induction hypotheses may become sufficiently general to get the
  proof through.  Together with definitional instantiations, one may
  effectively perform induction over expressions of a certain
  structure.
  
  The optional ``@{text "taking: t\<^sub>1 \<dots> t\<^sub>n"}''
  specification provides additional instantiations of a prefix of
  pending variables in the rule.  Such schematic induction rules
  rarely occur in practice, though.

  \item [@{method coinduct}~@{text "inst R"}] is analogous to the
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

  \end{descr}

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

  In induction proofs, local assumptions introduced by cases are split
  into two different kinds: @{text hyps} stemming from the rule and
  @{text prems} from the goal statement.  This is reflected in the
  extracted cases accordingly, so invoking ``@{command "case"}~@{text
  c}'' will provide separate facts @{text c.hyps} and @{text c.prems},
  as well as fact @{text c} to hold the all-inclusive list.

  \medskip Facts presented to either method are consumed according to
  the number of ``major premises'' of the rule involved, which is
  usually 0 for plain cases and induction rules of datatypes etc.\ and
  1 for rules of inductive predicates or sets and the like.  The
  remaining facts are inserted into the goal verbatim before the
  actual @{text cases}, @{text induct}, or @{text coinduct} rule is
  applied.
*}


subsubsection {* Declaring rules *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_induct_rules"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{attribute_def cases} & : & \isaratt \\
    @{attribute_def induct} & : & \isaratt \\
    @{attribute_def coinduct} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    'cases' spec
    ;
    'induct' spec
    ;
    'coinduct' spec
    ;

    spec: ('type' | 'pred' | 'set') ':' nameref
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "print_induct_rules"}] prints cases and induct
  rules for predicates (or sets) and types of the current context.
  
  \item [@{attribute cases}, @{attribute induct}, and @{attribute
  coinduct}] (as attributes) augment the corresponding context of
  rules for reasoning about (co)inductive predicates (or sets) and
  types, using the corresponding methods of the same name.  Certain
  definitional packages of object-logics usually declare emerging
  cases and induction rules as expected, so users rarely need to
  intervene.
  
  Manual rule declarations usually refer to the @{attribute
  case_names} and @{attribute params} attributes to adjust names of
  cases and parameters of a rule; the @{attribute consumes}
  declaration is taken care of automatically: @{attribute
  consumes}~@{text 0} is specified for ``type'' rules and @{attribute
  consumes}~@{text 1} for ``predicate'' / ``set'' rules.

  \end{descr}
*}


section {* General logic setup \label{sec:object-logic} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "judgment"} & : & \isartrans{theory}{theory} \\
    @{method_def atomize} & : & \isarmeth \\
    @{attribute_def atomize} & : & \isaratt \\
    @{attribute_def rule_format} & : & \isaratt \\
    @{attribute_def rulify} & : & \isaratt \\
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

  \begin{rail}
    'judgment' constdecl
    ;
    'atomize' ('(' 'full' ')')?
    ;
    'rule\_format' ('(' 'noasm' ')')?
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "judgment"}~@{text "c :: \<sigma> (mx)"}] declares
  constant @{text c} as the truth judgment of the current
  object-logic.  Its type @{text \<sigma>} should specify a coercion of the
  category of object-level propositions to @{text prop} of the Pure
  meta-logic; the mixfix annotation @{text "(mx)"} would typically
  just link the object language (internally of syntactic category
  @{text logic}) with that of @{text prop}.  Only one @{command
  "judgment"} declaration may be given in any theory development.
  
  \item [@{method atomize} (as a method)] rewrites any non-atomic
  premises of a sub-goal, using the meta-level equations declared via
  @{attribute atomize} (as an attribute) beforehand.  As a result,
  heavily nested goals become amenable to fundamental operations such
  as resolution (cf.\ the @{method rule} method).  Giving the ``@{text
  "(full)"}'' option here means to turn the whole subgoal into an
  object-statement (if possible), including the outermost parameters
  and assumptions as well.

  A typical collection of @{attribute atomize} rules for a particular
  object-logic would provide an internalization for each of the
  connectives of @{text "\<And>"}, @{text "\<Longrightarrow>"}, and @{text "\<equiv>"}.
  Meta-level conjunction should be covered as well (this is
  particularly important for locales, see \secref{sec:locale}).

  \item [@{attribute rule_format}] rewrites a theorem by the
  equalities declared as @{attribute rulify} rules in the current
  object-logic.  By default, the result is fully normalized, including
  assumptions and conclusions at any depth.  The @{text "(no_asm)"}
  option restricts the transformation to the conclusion of a rule.

  In common object-logics (HOL, FOL, ZF), the effect of @{attribute
  rule_format} is to replace (bounded) universal quantification
  (@{text "\<forall>"}) and implication (@{text "\<longrightarrow>"}) by the corresponding
  rule statements over @{text "\<And>"} and @{text "\<Longrightarrow>"}.

  \end{descr}
*}

end

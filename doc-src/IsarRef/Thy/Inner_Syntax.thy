theory Inner_Syntax
imports Base Main
begin

chapter {* Inner syntax --- the term language \label{ch:inner-syntax} *}

text {* The inner syntax of Isabelle provides concrete notation for
  the main entities of the logical framework, notably @{text
  "\<lambda>"}-terms with types and type classes.  Applications may either
  extend existing syntactic categories by additional notation, or
  define new sub-languages that are linked to the standard term
  language via some explicit markers.  For example @{verbatim
  FOO}~@{text "foo"} could embed the syntax corresponding for some
  user-defined nonterminal @{text "foo"} --- within the bounds of the
  given lexical syntax of Isabelle/Pure.

  The most basic way to specify concrete syntax for logical entities
  works via mixfix annotations (\secref{sec:mixfix}), which may be
  usually given as part of the original declaration or via explicit
  notation commands later on (\secref{sec:notation}).  This already
  covers many needs of concrete syntax without having to understand
  the full complexity of inner syntax layers.

  Further details of the syntax engine involves the classical
  distinction of lexical language versus context-free grammar (see
  \secref{sec:pure-syntax}), and various mechanisms for \emph{syntax
  transformations} (see \secref{sec:syntax-transformations}).
*}


section {* Printing logical entities *}

subsection {* Diagnostic commands \label{sec:print-diag} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "typ"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "term"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "prop"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "thm"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "prf"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "full_prf"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "pr"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
  \end{matharray}

  These diagnostic commands assist interactive development by printing
  internal logical entities in a human-readable fashion.

  @{rail "
    @@{command typ} @{syntax modes}? @{syntax type}
    ;
    @@{command term} @{syntax modes}? @{syntax term}
    ;
    @@{command prop} @{syntax modes}? @{syntax prop}
    ;
    @@{command thm} @{syntax modes}? @{syntax thmrefs}
    ;
    ( @@{command prf} | @@{command full_prf} ) @{syntax modes}? @{syntax thmrefs}?
    ;
    @@{command pr} @{syntax modes}? @{syntax nat}?
    ;

    @{syntax_def modes}: '(' (@{syntax name} + ) ')'
  "}

  \begin{description}

  \item @{command "typ"}~@{text \<tau>} reads and prints types of the
  meta-logic according to the current theory or proof context.

  \item @{command "term"}~@{text t} and @{command "prop"}~@{text \<phi>}
  read, type-check and print terms or propositions according to the
  current theory or proof context; the inferred type of @{text t} is
  output as well.  Note that these commands are also useful in
  inspecting the current environment of term abbreviations.

  \item @{command "thm"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} retrieves
  theorems from the current theory or proof context.  Note that any
  attributes included in the theorem specifications are applied to a
  temporary context derived from the current theory or proof; the
  result is discarded, i.e.\ attributes involved in @{text "a\<^sub>1,
  \<dots>, a\<^sub>n"} do not have any permanent effect.

  \item @{command "prf"} displays the (compact) proof term of the
  current proof state (if present), or of the given theorems. Note
  that this requires proof terms to be switched on for the current
  object logic (see the ``Proof terms'' section of the Isabelle
  reference manual for information on how to do this).

  \item @{command "full_prf"} is like @{command "prf"}, but displays
  the full proof term, i.e.\ also displays information omitted in the
  compact proof term, which is denoted by ``@{text _}'' placeholders
  there.

  \item @{command "pr"}~@{text "goals"} prints the current proof state
  (if present), including current facts and goals.  The optional limit
  arguments affect the number of goals to be displayed, which is
  initially 10.  Omitting limit value leaves the current setting
  unchanged.

  \end{description}

  All of the diagnostic commands above admit a list of @{text modes}
  to be specified, which is appended to the current print mode; see
  also \secref{sec:print-modes}.  Thus the output behavior may be
  modified according particular print mode features.  For example,
  @{command "pr"}~@{text "(latex xsymbols)"} would print the current
  proof state with mathematical symbols and special characters
  represented in {\LaTeX} source, according to the Isabelle style
  \cite{isabelle-sys}.

  Note that antiquotations (cf.\ \secref{sec:antiq}) provide a more
  systematic way to include formal items into the printed text
  document.
*}


subsection {* Details of printed content *}

text {*
  \begin{tabular}{rcll}
    @{attribute_def show_types} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_sorts} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_consts} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_abbrevs} & : & @{text attribute} & default @{text true} \\
    @{attribute_def show_brackets} & : & @{text attribute} & default @{text false} \\
    @{attribute_def names_long} & : & @{text attribute} & default @{text false} \\
    @{attribute_def names_short} & : & @{text attribute} & default @{text false} \\
    @{attribute_def names_unique} & : & @{text attribute} & default @{text true} \\
    @{attribute_def eta_contract} & : & @{text attribute} & default @{text true} \\
    @{attribute_def goals_limit} & : & @{text attribute} & default @{text 10} \\
    @{attribute_def show_main_goal} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_hyps} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_tags} & : & @{text attribute} & default @{text false} \\
    @{attribute_def show_question_marks} & : & @{text attribute} & default @{text true} \\
  \end{tabular}
  \medskip

  These configuration options control the detail of information that
  is displayed for types, terms, theorems, goals etc.  See also
  \secref{sec:config}.

  \begin{description}

  \item @{attribute show_types} and @{attribute show_sorts} control
  printing of type constraints for term variables, and sort
  constraints for type variables.  By default, neither of these are
  shown in output.  If @{attribute show_sorts} is enabled, types are
  always shown as well.

  Note that displaying types and sorts may explain why a polymorphic
  inference rule fails to resolve with some goal, or why a rewrite
  rule does not apply as expected.

  \item @{attribute show_consts} controls printing of types of
  constants when displaying a goal state.

  Note that the output can be enormous, because polymorphic constants
  often occur at several different type instances.

  \item @{attribute show_abbrevs} controls folding of constant
  abbreviations.

  \item @{attribute show_brackets} controls bracketing in pretty
  printed output.  If enabled, all sub-expressions of the pretty
  printing tree will be parenthesized, even if this produces malformed
  term syntax!  This crude way of showing the internal structure of
  pretty printed entities may occasionally help to diagnose problems
  with operator priorities, for example.

  \item @{attribute names_long}, @{attribute names_short}, and
  @{attribute names_unique} control the way of printing fully
  qualified internal names in external form.  See also
  \secref{sec:antiq} for the document antiquotation options of the
  same names.

  \item @{attribute eta_contract} controls @{text "\<eta>"}-contracted
  printing of terms.

  The @{text \<eta>}-contraction law asserts @{prop "(\<lambda>x. f x) \<equiv> f"},
  provided @{text x} is not free in @{text f}.  It asserts
  \emph{extensionality} of functions: @{prop "f \<equiv> g"} if @{prop "f x \<equiv>
  g x"} for all @{text x}.  Higher-order unification frequently puts
  terms into a fully @{text \<eta>}-expanded form.  For example, if @{text
  F} has type @{text "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> \<tau>"} then its expanded form is @{term
  "\<lambda>h. F (\<lambda>x. h x)"}.

  Enabling @{attribute eta_contract} makes Isabelle perform @{text
  \<eta>}-contractions before printing, so that @{term "\<lambda>h. F (\<lambda>x. h x)"}
  appears simply as @{text F}.

  Note that the distinction between a term and its @{text \<eta>}-expanded
  form occasionally matters.  While higher-order resolution and
  rewriting operate modulo @{text "\<alpha>\<beta>\<eta>"}-conversion, some other tools
  might look at terms more discretely.

  \item @{attribute goals_limit} controls the maximum number of
  subgoals to be shown in goal output.

  \item @{attribute show_main_goal} controls whether the main result
  to be proven should be displayed.  This information might be
  relevant for schematic goals, to inspect the current claim that has
  been synthesized so far.

  \item @{attribute show_hyps} controls printing of implicit
  hypotheses of local facts.  Normally, only those hypotheses are
  displayed that are \emph{not} covered by the assumptions of the
  current context: this situation indicates a fault in some tool being
  used.

  By enabling @{attribute show_hyps}, output of \emph{all} hypotheses
  can be enforced, which is occasionally useful for diagnostic
  purposes.

  \item @{attribute show_tags} controls printing of extra annotations
  within theorems, such as internal position information, or the case
  names being attached by the attribute @{attribute case_names}.

  Note that the @{attribute tagged} and @{attribute untagged}
  attributes provide low-level access to the collection of tags
  associated with a theorem.

  \item @{attribute show_question_marks} controls printing of question
  marks for schematic variables, such as @{text ?x}.  Only the leading
  question mark is affected, the remaining text is unchanged
  (including proper markup for schematic variables that might be
  relevant for user interfaces).

  \end{description}
*}


subsection {* Alternative print modes \label{sec:print-modes} *}

text {*
  \begin{mldecls}
    @{index_ML print_mode_value: "unit -> string list"} \\
    @{index_ML Print_Mode.with_modes: "string list -> ('a -> 'b) -> 'a -> 'b"} \\
  \end{mldecls}

  The \emph{print mode} facility allows to modify various operations
  for printing.  Commands like @{command typ}, @{command term},
  @{command thm} (see \secref{sec:print-diag}) take additional print
  modes as optional argument.  The underlying ML operations are as
  follows.

  \begin{description}

  \item @{ML "print_mode_value ()"} yields the list of currently
  active print mode names.  This should be understood as symbolic
  representation of certain individual features for printing (with
  precedence from left to right).

  \item @{ML Print_Mode.with_modes}~@{text "modes f x"} evaluates
  @{text "f x"} in an execution context where the print mode is
  prepended by the given @{text "modes"}.  This provides a thread-safe
  way to augment print modes.  It is also monotonic in the set of mode
  names: it retains the default print mode that certain
  user-interfaces might have installed for their proper functioning!

  \end{description}

  \begin{warn}
  The old global reference @{ML print_mode} should never be used
  directly in applications.  Its main reason for being publicly
  accessible is to support historic versions of Proof~General.
  \end{warn}

  \medskip The pretty printer for inner syntax maintains alternative
  mixfix productions for any print mode name invented by the user, say
  in commands like @{command notation} or @{command abbreviation}.
  Mode names can be arbitrary, but the following ones have a specific
  meaning by convention:

  \begin{itemize}

  \item @{verbatim "\"\""} (the empty string): default mode;
  implicitly active as last element in the list of modes.

  \item @{verbatim input}: dummy print mode that is never active; may
  be used to specify notation that is only available for input.

  \item @{verbatim internal} dummy print mode that is never active;
  used internally in Isabelle/Pure.

  \item @{verbatim xsymbols}: enable proper mathematical symbols
  instead of ASCII art.\footnote{This traditional mode name stems from
  the ``X-Symbol'' package for old versions Proof~General with XEmacs,
  although that package has been superseded by Unicode in recent
  years.}

  \item @{verbatim HTML}: additional mode that is active in HTML
  presentation of Isabelle theory sources; allows to provide
  alternative output notation.

  \item @{verbatim latex}: additional mode that is active in {\LaTeX}
  document preparation of Isabelle theory sources; allows to provide
  alternative output notation.

  \end{itemize}
*}


subsection {* Printing limits *}

text {*
  \begin{mldecls}
    @{index_ML Pretty.margin_default: "int Unsynchronized.ref"} \\
    @{index_ML print_depth: "int -> unit"} \\
  \end{mldecls}

  These ML functions set limits for pretty printed text.

  \begin{description}

  \item @{ML Pretty.margin_default} indicates the global default for
  the right margin of the built-in pretty printer, with initial value
  76.  Note that user-interfaces typically control margins
  automatically when resizing windows, or even bypass the formatting
  engine of Isabelle/ML altogether and do it within the front end via
  Isabelle/Scala.

  \item @{ML print_depth}~@{text n} limits the printing depth of the
  ML toplevel pretty printer; the precise effect depends on the ML
  compiler and run-time system.  Typically @{text n} should be less
  than 10.  Bigger values such as 100--1000 are useful for debugging.

  \end{description}
*}


section {* Mixfix annotations \label{sec:mixfix} *}

text {* Mixfix annotations specify concrete \emph{inner syntax} of
  Isabelle types and terms.  Locally fixed parameters in toplevel
  theorem statements, locale and class specifications also admit
  mixfix annotations in a fairly uniform manner.  A mixfix annotation
  describes describes the concrete syntax, the translation to abstract
  syntax, and the pretty printing.  Special case annotations provide a
  simple means of specifying infix operators and binders.

  Isabelle mixfix syntax is inspired by {\OBJ} \cite{OBJ}.  It allows
  to specify any context-free priority grammar, which is more general
  than the fixity declarations of ML and Prolog.

  @{rail "
    @{syntax_def mixfix}: '(' mfix ')'
    ;
    @{syntax_def struct_mixfix}: '(' ( mfix | @'structure' ) ')'
    ;

    mfix: @{syntax template} prios? @{syntax nat}? |
      (@'infix' | @'infixl' | @'infixr') @{syntax template} @{syntax nat} |
      @'binder' @{syntax template} prios? @{syntax nat}
    ;
    template: string
    ;
    prios: '[' (@{syntax nat} + ',') ']'
  "}

  The string given as @{text template} may include literal text,
  spacing, blocks, and arguments (denoted by ``@{text _}''); the
  special symbol ``@{verbatim "\<index>"}'' (printed as ``@{text "\<index>"}'')
  represents an index argument that specifies an implicit structure
  reference (see also \secref{sec:locale}).  Infix and binder
  declarations provide common abbreviations for particular mixfix
  declarations.  So in practice, mixfix templates mostly degenerate to
  literal text for concrete syntax, such as ``@{verbatim "++"}'' for
  an infix symbol.
*}


subsection {* The general mixfix form *}

text {* In full generality, mixfix declarations work as follows.
  Suppose a constant @{text "c :: \<tau>\<^sub>1 \<Rightarrow> \<dots> \<tau>\<^sub>n \<Rightarrow> \<tau>"} is annotated by
  @{text "(mixfix [p\<^sub>1, \<dots>, p\<^sub>n] p)"}, where @{text "mixfix"} is a string
  @{text "d\<^sub>0 _ d\<^sub>1 _ \<dots> _ d\<^sub>n"} consisting of delimiters that surround
  argument positions as indicated by underscores.

  Altogether this determines a production for a context-free priority
  grammar, where for each argument @{text "i"} the syntactic category
  is determined by @{text "\<tau>\<^sub>i"} (with priority @{text "p\<^sub>i"}), and the
  result category is determined from @{text "\<tau>"} (with priority @{text
  "p"}).  Priority specifications are optional, with default 0 for
  arguments and 1000 for the result.\footnote{Omitting priorities is
  prone to syntactic ambiguities unless the delimiter tokens determine
  fully bracketed notation, as in @{text "if _ then _ else _ fi"}.}

  Since @{text "\<tau>"} may be again a function type, the constant
  type scheme may have more argument positions than the mixfix
  pattern.  Printing a nested application @{text "c t\<^sub>1 \<dots> t\<^sub>m"} for
  @{text "m > n"} works by attaching concrete notation only to the
  innermost part, essentially by printing @{text "(c t\<^sub>1 \<dots> t\<^sub>n) \<dots> t\<^sub>m"}
  instead.  If a term has fewer arguments than specified in the mixfix
  template, the concrete syntax is ignored.

  \medskip A mixfix template may also contain additional directives
  for pretty printing, notably spaces, blocks, and breaks.  The
  general template format is a sequence over any of the following
  entities.

  \begin{description}

  \item @{text "d"} is a delimiter, namely a non-empty sequence of
  characters other than the following special characters:

  \smallskip
  \begin{tabular}{ll}
    @{verbatim "'"} & single quote \\
    @{verbatim "_"} & underscore \\
    @{text "\<index>"} & index symbol \\
    @{verbatim "("} & open parenthesis \\
    @{verbatim ")"} & close parenthesis \\
    @{verbatim "/"} & slash \\
  \end{tabular}
  \medskip

  \item @{verbatim "'"} escapes the special meaning of these
  meta-characters, producing a literal version of the following
  character, unless that is a blank.

  A single quote followed by a blank separates delimiters, without
  affecting printing, but input tokens may have additional white space
  here.

  \item @{verbatim "_"} is an argument position, which stands for a
  certain syntactic category in the underlying grammar.

  \item @{text "\<index>"} is an indexed argument position; this is the place
  where implicit structure arguments can be attached.

  \item @{text "s"} is a non-empty sequence of spaces for printing.
  This and the following specifications do not affect parsing at all.

  \item @{verbatim "("}@{text n} opens a pretty printing block.  The
  optional number specifies how much indentation to add when a line
  break occurs within the block.  If the parenthesis is not followed
  by digits, the indentation defaults to 0.  A block specified via
  @{verbatim "(00"} is unbreakable.

  \item @{verbatim ")"} closes a pretty printing block.

  \item @{verbatim "//"} forces a line break.

  \item @{verbatim "/"}@{text s} allows a line break.  Here @{text s}
  stands for the string of spaces (zero or more) right after the
  slash.  These spaces are printed if the break is \emph{not} taken.

  \end{description}

  The general idea of pretty printing with blocks and breaks is also
  described in \cite{paulson-ml2}; it goes back to \cite{Oppen:1980}.
*}


subsection {* Infixes *}

text {* Infix operators are specified by convenient short forms that
  abbreviate general mixfix annotations as follows:

  \begin{center}
  \begin{tabular}{lll}

  @{verbatim "("}@{keyword_def "infix"}~@{verbatim "\""}@{text sy}@{verbatim "\""} @{text "p"}@{verbatim ")"}
  & @{text "\<mapsto>"} &
  @{verbatim "(\"(_ "}@{text sy}@{verbatim "/ _)\" ["}@{text "p + 1"}@{verbatim ", "}@{text "p + 1"}@{verbatim "]"}@{text " p"}@{verbatim ")"} \\
  @{verbatim "("}@{keyword_def "infixl"}~@{verbatim "\""}@{text sy}@{verbatim "\""} @{text "p"}@{verbatim ")"}
  & @{text "\<mapsto>"} &
  @{verbatim "(\"(_ "}@{text sy}@{verbatim "/ _)\" ["}@{text "p"}@{verbatim ", "}@{text "p + 1"}@{verbatim "]"}@{text " p"}@{verbatim ")"} \\
  @{verbatim "("}@{keyword_def "infixr"}~@{verbatim "\""}@{text sy}@{verbatim "\""} @{text "p"}@{verbatim ")"}
  & @{text "\<mapsto>"} &
  @{verbatim "(\"(_ "}@{text sy}@{verbatim "/ _)\" ["}@{text "p + 1"}@{verbatim ", "}@{text "p"}@{verbatim "]"}@{text " p"}@{verbatim ")"} \\

  \end{tabular}
  \end{center}

  The mixfix template @{verbatim "\"(_ "}@{text sy}@{verbatim "/ _)\""}
  specifies two argument positions; the delimiter is preceded by a
  space and followed by a space or line break; the entire phrase is a
  pretty printing block.

  The alternative notation @{verbatim "op"}~@{text sy} is introduced
  in addition.  Thus any infix operator may be written in prefix form
  (as in ML), independently of the number of arguments in the term.
*}


subsection {* Binders *}

text {* A \emph{binder} is a variable-binding construct such as a
  quantifier.  The idea to formalize @{text "\<forall>x. b"} as @{text "All
  (\<lambda>x. b)"} for @{text "All :: ('a \<Rightarrow> bool) \<Rightarrow> bool"} already goes back
  to \cite{church40}.  Isabelle declarations of certain higher-order
  operators may be annotated with @{keyword_def "binder"} annotations
  as follows:

  \begin{center}
  @{text "c :: "}@{verbatim "\""}@{text "(\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2) \<Rightarrow> \<tau>\<^sub>3"}@{verbatim "\"  ("}@{keyword "binder"}@{verbatim " \""}@{text "sy"}@{verbatim "\" ["}@{text "p"}@{verbatim "] "}@{text "q"}@{verbatim ")"}
  \end{center}

  This introduces concrete binder syntax @{text "sy x. b"}, where
  @{text x} is a bound variable of type @{text "\<tau>\<^sub>1"}, the body @{text
  b} has type @{text "\<tau>\<^sub>2"} and the whole term has type @{text "\<tau>\<^sub>3"}.
  The optional integer @{text p} specifies the syntactic priority of
  the body; the default is @{text "q"}, which is also the priority of
  the whole construct.

  Internally, the binder syntax is expanded to something like this:
  \begin{center}
  @{text "c_binder :: "}@{verbatim "\""}@{text "idts \<Rightarrow> \<tau>\<^sub>2 \<Rightarrow> \<tau>\<^sub>3"}@{verbatim "\"  (\"(3"}@{text sy}@{verbatim "_./ _)\" [0, "}@{text "p"}@{verbatim "] "}@{text "q"}@{verbatim ")"}
  \end{center}

  Here @{syntax (inner) idts} is the nonterminal symbol for a list of
  identifiers with optional type constraints (see also
  \secref{sec:pure-grammar}).  The mixfix template @{verbatim
  "\"(3"}@{text sy}@{verbatim "_./ _)\""} defines argument positions
  for the bound identifiers and the body, separated by a dot with
  optional line break; the entire phrase is a pretty printing block of
  indentation level 3.  Note that there is no extra space after @{text
  "sy"}, so it needs to be included user specification if the binder
  syntax ends with a token that may be continued by an identifier
  token at the start of @{syntax (inner) idts}.

  Furthermore, a syntax translation to transforms @{text "c_binder x\<^sub>1
  \<dots> x\<^sub>n b"} into iterated application @{text "c (\<lambda>x\<^sub>1. \<dots> c (\<lambda>x\<^sub>n. b)\<dots>)"}.
  This works in both directions, for parsing and printing.  *}


section {* Explicit notation \label{sec:notation} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "type_notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "no_type_notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "no_notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "write"} & : & @{text "proof(state) \<rightarrow> proof(state)"} \\
  \end{matharray}

  Commands that introduce new logical entities (terms or types)
  usually allow to provide mixfix annotations on the spot, which is
  convenient for default notation.  Nonetheless, the syntax may be
  modified later on by declarations for explicit notation.  This
  allows to add or delete mixfix annotations for of existing logical
  entities within the current context.

  @{rail "
    (@@{command type_notation} | @@{command no_type_notation}) @{syntax target}?
      @{syntax mode}? \\ (@{syntax nameref} @{syntax mixfix} + @'and')
    ;
    (@@{command notation} | @@{command no_notation}) @{syntax target}? @{syntax mode}? \\
      (@{syntax nameref} @{syntax struct_mixfix} + @'and')
    ;
    @@{command write} @{syntax mode}? (@{syntax nameref} @{syntax struct_mixfix} + @'and')
  "}

  \begin{description}

  \item @{command "type_notation"}~@{text "c (mx)"} associates mixfix
  syntax with an existing type constructor.  The arity of the
  constructor is retrieved from the context.

  \item @{command "no_type_notation"} is similar to @{command
  "type_notation"}, but removes the specified syntax annotation from
  the present context.

  \item @{command "notation"}~@{text "c (mx)"} associates mixfix
  syntax with an existing constant or fixed variable.  The type
  declaration of the given entity is retrieved from the context.

  \item @{command "no_notation"} is similar to @{command "notation"},
  but removes the specified syntax annotation from the present
  context.

  \item @{command "write"} is similar to @{command "notation"}, but
  works within an Isar proof body.

  \end{description}
*}


section {* The Pure syntax \label{sec:pure-syntax} *}

subsection {* Lexical matters \label{sec:inner-lex} *}

text {* The inner lexical syntax vaguely resembles the outer one
  (\secref{sec:outer-lex}), but some details are different.  There are
  two main categories of inner syntax tokens:

  \begin{enumerate}

  \item \emph{delimiters} --- the literal tokens occurring in
  productions of the given priority grammar (cf.\
  \secref{sec:priority-grammar});

  \item \emph{named tokens} --- various categories of identifiers etc.

  \end{enumerate}

  Delimiters override named tokens and may thus render certain
  identifiers inaccessible.  Sometimes the logical context admits
  alternative ways to refer to the same entity, potentially via
  qualified names.

  \medskip The categories for named tokens are defined once and for
  all as follows, reusing some categories of the outer token syntax
  (\secref{sec:outer-lex}).

  \begin{center}
  \begin{supertabular}{rcl}
    @{syntax_def (inner) id} & = & @{syntax_ref ident} \\
    @{syntax_def (inner) longid} & = & @{syntax_ref longident} \\
    @{syntax_def (inner) var} & = & @{syntax_ref var} \\
    @{syntax_def (inner) tid} & = & @{syntax_ref typefree} \\
    @{syntax_def (inner) tvar} & = & @{syntax_ref typevar} \\
    @{syntax_def (inner) num_token} & = & @{syntax_ref nat}@{text "  |  "}@{verbatim "-"}@{syntax_ref nat} \\
    @{syntax_def (inner) float_token} & = & @{syntax_ref nat}@{verbatim "."}@{syntax_ref nat}@{text "  |  "}@{verbatim "-"}@{syntax_ref nat}@{verbatim "."}@{syntax_ref nat} \\
    @{syntax_def (inner) xnum_token} & = & @{verbatim "#"}@{syntax_ref nat}@{text "  |  "}@{verbatim "#-"}@{syntax_ref nat} \\

    @{syntax_def (inner) str_token} & = & @{verbatim "''"} @{text "\<dots>"} @{verbatim "''"} \\
  \end{supertabular}
  \end{center}

  The token categories @{syntax (inner) num_token}, @{syntax (inner)
  float_token}, @{syntax (inner) xnum_token}, and @{syntax (inner)
  str_token} are not used in Pure.  Object-logics may implement numerals
  and string constants by adding appropriate syntax declarations,
  together with some translation functions (e.g.\ see Isabelle/HOL).

  The derived categories @{syntax_def (inner) num_const}, @{syntax_def
  (inner) float_const}, and @{syntax_def (inner) num_const} provide
  robust access to the respective tokens: the syntax tree holds a
  syntactic constant instead of a free variable.
*}


subsection {* Priority grammars \label{sec:priority-grammar} *}

text {* A context-free grammar consists of a set of \emph{terminal
  symbols}, a set of \emph{nonterminal symbols} and a set of
  \emph{productions}.  Productions have the form @{text "A = \<gamma>"},
  where @{text A} is a nonterminal and @{text \<gamma>} is a string of
  terminals and nonterminals.  One designated nonterminal is called
  the \emph{root symbol}.  The language defined by the grammar
  consists of all strings of terminals that can be derived from the
  root symbol by applying productions as rewrite rules.

  The standard Isabelle parser for inner syntax uses a \emph{priority
  grammar}.  Each nonterminal is decorated by an integer priority:
  @{text "A\<^sup>(\<^sup>p\<^sup>)"}.  In a derivation, @{text "A\<^sup>(\<^sup>p\<^sup>)"} may be rewritten
  using a production @{text "A\<^sup>(\<^sup>q\<^sup>) = \<gamma>"} only if @{text "p \<le> q"}.  Any
  priority grammar can be translated into a normal context-free
  grammar by introducing new nonterminals and productions.

  \medskip Formally, a set of context free productions @{text G}
  induces a derivation relation @{text "\<longrightarrow>\<^sub>G"} as follows.  Let @{text
  \<alpha>} and @{text \<beta>} denote strings of terminal or nonterminal symbols.
  Then @{text "\<alpha> A\<^sup>(\<^sup>p\<^sup>) \<beta> \<longrightarrow>\<^sub>G \<alpha> \<gamma> \<beta>"} holds if and only if @{text G}
  contains some production @{text "A\<^sup>(\<^sup>q\<^sup>) = \<gamma>"} for @{text "p \<le> q"}.

  \medskip The following grammar for arithmetic expressions
  demonstrates how binding power and associativity of operators can be
  enforced by priorities.

  \begin{center}
  \begin{tabular}{rclr}
  @{text "A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "="} & @{verbatim "("} @{text "A\<^sup>(\<^sup>0\<^sup>)"} @{verbatim ")"} \\
  @{text "A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "="} & @{verbatim 0} \\
  @{text "A\<^sup>(\<^sup>0\<^sup>)"} & @{text "="} & @{text "A\<^sup>(\<^sup>0\<^sup>)"} @{verbatim "+"} @{text "A\<^sup>(\<^sup>1\<^sup>)"} \\
  @{text "A\<^sup>(\<^sup>2\<^sup>)"} & @{text "="} & @{text "A\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "*"} @{text "A\<^sup>(\<^sup>2\<^sup>)"} \\
  @{text "A\<^sup>(\<^sup>3\<^sup>)"} & @{text "="} & @{verbatim "-"} @{text "A\<^sup>(\<^sup>3\<^sup>)"} \\
  \end{tabular}
  \end{center}
  The choice of priorities determines that @{verbatim "-"} binds
  tighter than @{verbatim "*"}, which binds tighter than @{verbatim
  "+"}.  Furthermore @{verbatim "+"} associates to the left and
  @{verbatim "*"} to the right.

  \medskip For clarity, grammars obey these conventions:
  \begin{itemize}

  \item All priorities must lie between 0 and 1000.

  \item Priority 0 on the right-hand side and priority 1000 on the
  left-hand side may be omitted.

  \item The production @{text "A\<^sup>(\<^sup>p\<^sup>) = \<alpha>"} is written as @{text "A = \<alpha>
  (p)"}, i.e.\ the priority of the left-hand side actually appears in
  a column on the far right.

  \item Alternatives are separated by @{text "|"}.

  \item Repetition is indicated by dots @{text "(\<dots>)"} in an informal
  but obvious way.

  \end{itemize}

  Using these conventions, the example grammar specification above
  takes the form:
  \begin{center}
  \begin{tabular}{rclc}
    @{text A} & @{text "="} & @{verbatim "("} @{text A} @{verbatim ")"} \\
              & @{text "|"} & @{verbatim 0} & \qquad\qquad \\
              & @{text "|"} & @{text A} @{verbatim "+"} @{text "A\<^sup>(\<^sup>1\<^sup>)"} & @{text "(0)"} \\
              & @{text "|"} & @{text "A\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "*"} @{text "A\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
              & @{text "|"} & @{verbatim "-"} @{text "A\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
  \end{tabular}
  \end{center}
*}


subsection {* The Pure grammar \label{sec:pure-grammar} *}

text {* The priority grammar of the @{text "Pure"} theory is defined
  approximately like this:

  \begin{center}
  \begin{supertabular}{rclr}

  @{syntax_def (inner) any} & = & @{text "prop  |  logic"} \\\\

  @{syntax_def (inner) prop} & = & @{verbatim "("} @{text prop} @{verbatim ")"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>4\<^sup>)"} @{verbatim "::"} @{text type} & @{text "(3)"} \\
    & @{text "|"} & @{text "any\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "=="} @{text "any\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "any\<^sup>(\<^sup>3\<^sup>)"} @{text "\<equiv>"} @{text "any\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "&&&"} @{text "prop\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>2\<^sup>)"} @{verbatim "==>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>2\<^sup>)"} @{text "\<Longrightarrow>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{verbatim "[|"} @{text prop} @{verbatim ";"} @{text "\<dots>"} @{verbatim ";"} @{text prop} @{verbatim "|]"} @{verbatim "==>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{text "\<lbrakk>"} @{text prop} @{verbatim ";"} @{text "\<dots>"} @{verbatim ";"} @{text prop} @{text "\<rbrakk>"} @{text "\<Longrightarrow>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{verbatim "!!"} @{text idts} @{verbatim "."} @{text prop} & @{text "(0)"} \\
    & @{text "|"} & @{text "\<And>"} @{text idts} @{verbatim "."} @{text prop} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim OFCLASS} @{verbatim "("} @{text type} @{verbatim ","} @{text logic} @{verbatim ")"} \\
    & @{text "|"} & @{verbatim SORT_CONSTRAINT} @{verbatim "("} @{text type} @{verbatim ")"} \\
    & @{text "|"} & @{verbatim TERM} @{text logic} \\
    & @{text "|"} & @{verbatim PROP} @{text aprop} \\\\

  @{syntax_def (inner) aprop} & = & @{verbatim "("} @{text aprop} @{verbatim ")"} \\
    & @{text "|"} & @{text "id  |  longid  |  var  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "..."} \\
    & @{text "|"} & @{verbatim CONST} @{text "id  |  "}@{verbatim CONST} @{text "longid"} \\
    & @{text "|"} & @{verbatim XCONST} @{text "id  |  "}@{verbatim XCONST} @{text "longid"} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "(999)"} \\\\

  @{syntax_def (inner) logic} & = & @{verbatim "("} @{text logic} @{verbatim ")"} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>4\<^sup>)"} @{verbatim "::"} @{text type} & @{text "(3)"} \\
    & @{text "|"} & @{text "id  |  longid  |  var  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "..."} \\
    & @{text "|"} & @{verbatim CONST} @{text "id  |  "}@{verbatim CONST} @{text "longid"} \\
    & @{text "|"} & @{verbatim XCONST} @{text "id  |  "}@{verbatim XCONST} @{text "longid"} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "(999)"} \\
    & @{text "|"} & @{text "\<struct> index\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} \\
    & @{text "|"} & @{verbatim "%"} @{text pttrns} @{verbatim "."} @{text "any\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
    & @{text "|"} & @{text \<lambda>} @{text pttrns} @{verbatim "."} @{text "any\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
    & @{text "|"} & @{verbatim op} @{verbatim "=="}@{text "  |  "}@{verbatim op} @{text "\<equiv>"}@{text "  |  "}@{verbatim op} @{verbatim "&&&"} \\
    & @{text "|"} & @{verbatim op} @{verbatim "==>"}@{text "  |  "}@{verbatim op} @{text "\<Longrightarrow>"} \\
    & @{text "|"} & @{verbatim TYPE} @{verbatim "("} @{text type} @{verbatim ")"} \\\\

  @{syntax_def (inner) idt} & = & @{verbatim "("} @{text idt} @{verbatim ")"}@{text "  |  id  |  "}@{verbatim "_"} \\
    & @{text "|"} & @{text id} @{verbatim "::"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "_"} @{verbatim "::"} @{text type} & @{text "(0)"} \\\\

  @{syntax_def (inner) index} & = & @{verbatim "\<^bsub>"} @{text "logic\<^sup>(\<^sup>0\<^sup>)"} @{verbatim "\<^esub>"}@{text "  |  |  \<index>"} \\\\

  @{syntax_def (inner) idts} & = & @{text "idt  |  idt\<^sup>(\<^sup>1\<^sup>) idts"} & @{text "(0)"} \\\\

  @{syntax_def (inner) pttrn} & = & @{text idt} \\\\

  @{syntax_def (inner) pttrns} & = & @{text "pttrn  |  pttrn\<^sup>(\<^sup>1\<^sup>) pttrns"} & @{text "(0)"} \\\\

  @{syntax_def (inner) type} & = & @{verbatim "("} @{text type} @{verbatim ")"} \\
    & @{text "|"} & @{text "tid  |  tvar  |  "}@{verbatim "_"} \\
    & @{text "|"} & @{text "tid"} @{verbatim "::"} @{text "sort  |  tvar  "}@{verbatim "::"} @{text "sort  |  "}@{verbatim "_"} @{verbatim "::"} @{text "sort"} \\
    & @{text "|"} & @{text "type_name  |  type\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) type_name"} \\
    & @{text "|"} & @{verbatim "("} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim ")"} @{text type_name} \\
    & @{text "|"} & @{text "type\<^sup>(\<^sup>1\<^sup>)"} @{verbatim "=>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{text "type\<^sup>(\<^sup>1\<^sup>)"} @{text "\<Rightarrow>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "["} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim "]"} @{verbatim "=>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "["} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim "]"} @{text "\<Rightarrow>"} @{text type} & @{text "(0)"} \\
  @{syntax_def (inner) type_name} & = & @{text "id  |  longid"} \\\\

  @{syntax_def (inner) sort} & = & @{syntax class_name}~@{text "  |  "}@{verbatim "{}"} \\
    & @{text "|"} & @{verbatim "{"} @{syntax class_name} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{syntax class_name} @{verbatim "}"} \\
  @{syntax_def (inner) class_name} & = & @{text "id  |  longid"} \\
  \end{supertabular}
  \end{center}

  \medskip Here literal terminals are printed @{verbatim "verbatim"};
  see also \secref{sec:inner-lex} for further token categories of the
  inner syntax.  The meaning of the nonterminals defined by the above
  grammar is as follows:

  \begin{description}

  \item @{syntax_ref (inner) any} denotes any term.

  \item @{syntax_ref (inner) prop} denotes meta-level propositions,
  which are terms of type @{typ prop}.  The syntax of such formulae of
  the meta-logic is carefully distinguished from usual conventions for
  object-logics.  In particular, plain @{text "\<lambda>"}-term notation is
  \emph{not} recognized as @{syntax (inner) prop}.

  \item @{syntax_ref (inner) aprop} denotes atomic propositions, which
  are embedded into regular @{syntax (inner) prop} by means of an
  explicit @{verbatim PROP} token.

  Terms of type @{typ prop} with non-constant head, e.g.\ a plain
  variable, are printed in this form.  Constants that yield type @{typ
  prop} are expected to provide their own concrete syntax; otherwise
  the printed version will appear like @{syntax (inner) logic} and
  cannot be parsed again as @{syntax (inner) prop}.

  \item @{syntax_ref (inner) logic} denotes arbitrary terms of a
  logical type, excluding type @{typ prop}.  This is the main
  syntactic category of object-logic entities, covering plain @{text
  \<lambda>}-term notation (variables, abstraction, application), plus
  anything defined by the user.

  When specifying notation for logical entities, all logical types
  (excluding @{typ prop}) are \emph{collapsed} to this single category
  of @{syntax (inner) logic}.

  \item @{syntax_ref (inner) index} denotes an optional index term for
  indexed syntax.  If omitted, it refers to the first @{keyword
  "structure"} variable in the context.  The special dummy ``@{text
  "\<index>"}'' serves as pattern variable in mixfix annotations that
  introduce indexed notation.

  \item @{syntax_ref (inner) idt} denotes identifiers, possibly
  constrained by types.

  \item @{syntax_ref (inner) idts} denotes a sequence of @{syntax_ref
  (inner) idt}.  This is the most basic category for variables in
  iterated binders, such as @{text "\<lambda>"} or @{text "\<And>"}.

  \item @{syntax_ref (inner) pttrn} and @{syntax_ref (inner) pttrns}
  denote patterns for abstraction, cases bindings etc.  In Pure, these
  categories start as a merely copy of @{syntax (inner) idt} and
  @{syntax (inner) idts}, respectively.  Object-logics may add
  additional productions for binding forms.

  \item @{syntax_ref (inner) type} denotes types of the meta-logic.

  \item @{syntax_ref (inner) sort} denotes meta-level sorts.

  \end{description}

  Here are some further explanations of certain syntax features.

  \begin{itemize}

  \item In @{syntax (inner) idts}, note that @{text "x :: nat y"} is
  parsed as @{text "x :: (nat y)"}, treating @{text y} like a type
  constructor applied to @{text nat}.  To avoid this interpretation,
  write @{text "(x :: nat) y"} with explicit parentheses.

  \item Similarly, @{text "x :: nat y :: nat"} is parsed as @{text "x ::
  (nat y :: nat)"}.  The correct form is @{text "(x :: nat) (y ::
  nat)"}, or @{text "(x :: nat) y :: nat"} if @{text y} is last in the
  sequence of identifiers.

  \item Type constraints for terms bind very weakly.  For example,
  @{text "x < y :: nat"} is normally parsed as @{text "(x < y) ::
  nat"}, unless @{text "<"} has a very low priority, in which case the
  input is likely to be ambiguous.  The correct form is @{text "x < (y
  :: nat)"}.

  \item Constraints may be either written with two literal colons
  ``@{verbatim "::"}'' or the double-colon symbol @{verbatim "\<Colon>"},
  which actually looks exactly the same in some {\LaTeX} styles.

  \item Dummy variables (written as underscore) may occur in different
  roles.

  \begin{description}

  \item A type ``@{text "_"}'' or ``@{text "_ :: sort"}'' acts like an
  anonymous inference parameter, which is filled-in according to the
  most general type produced by the type-checking phase.

  \item A bound ``@{text "_"}'' refers to a vacuous abstraction, where
  the body does not refer to the binding introduced here.  As in the
  term @{term "\<lambda>x _. x"}, which is @{text "\<alpha>"}-equivalent to @{text
  "\<lambda>x y. x"}.

  \item A free ``@{text "_"}'' refers to an implicit outer binding.
  Higher definitional packages usually allow forms like @{text "f x _
  = x"}.

  \item A schematic ``@{text "_"}'' (within a term pattern, see
  \secref{sec:term-decls}) refers to an anonymous variable that is
  implicitly abstracted over its context of locally bound variables.
  For example, this allows pattern matching of @{text "{x. f x = g
  x}"} against @{text "{x. _ = _}"}, or even @{text "{_. _ = _}"} by
  using both bound and schematic dummies.

  \end{description}

  \item The three literal dots ``@{verbatim "..."}'' may be also
  written as ellipsis symbol @{verbatim "\<dots>"}.  In both cases this
  refers to a special schematic variable, which is bound in the
  context.  This special term abbreviation works nicely with
  calculational reasoning (\secref{sec:calculation}).

  \item @{verbatim CONST} ensures that the given identifier is treated
  as constant term, and passed through the parse tree in fully
  internalized form.  This is particularly relevant for translation
  rules (\secref{sec:syn-trans}), notably on the RHS.

  \item @{verbatim XCONST} is similar to @{verbatim CONST}, but
  retains the constant name as given.  This is only relevant to
  translation rules (\secref{sec:syn-trans}), notably on the LHS.

  \end{itemize}
*}


subsection {* Inspecting the syntax *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_syntax"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  \begin{description}

  \item @{command "print_syntax"} prints the inner syntax of the
  current context.  The output can be quite large; the most important
  sections are explained below.

  \begin{description}

  \item @{text "lexicon"} lists the delimiters of the inner token
  language; see \secref{sec:inner-lex}.

  \item @{text "prods"} lists the productions of the underlying
  priority grammar; see \secref{sec:priority-grammar}.

  The nonterminal @{text "A\<^sup>(\<^sup>p\<^sup>)"} is rendered in plain text as @{text
  "A[p]"}; delimiters are quoted.  Many productions have an extra
  @{text "\<dots> => name"}.  These names later become the heads of parse
  trees; they also guide the pretty printer.

  Productions without such parse tree names are called \emph{copy
  productions}.  Their right-hand side must have exactly one
  nonterminal symbol (or named token).  The parser does not create a
  new parse tree node for copy productions, but simply returns the
  parse tree of the right-hand symbol.

  If the right-hand side of a copy production consists of a single
  nonterminal without any delimiters, then it is called a \emph{chain
  production}.  Chain productions act as abbreviations: conceptually,
  they are removed from the grammar by adding new productions.
  Priority information attached to chain productions is ignored; only
  the dummy value @{text "-1"} is displayed.

  \item @{text "print modes"} lists the alternative print modes
  provided by this grammar; see \secref{sec:print-modes}.

  \item @{text "parse_rules"} and @{text "print_rules"} relate to
  syntax translations (macros); see \secref{sec:syn-trans}.

  \item @{text "parse_ast_translation"} and @{text
  "print_ast_translation"} list sets of constants that invoke
  translation functions for abstract syntax trees, which are only
  required in very special situations; see \secref{sec:tr-funs}.

  \item @{text "parse_translation"} and @{text "print_translation"}
  list the sets of constants that invoke regular translation
  functions; see \secref{sec:tr-funs}.

  \end{description}

  \end{description}
*}


subsection {* Ambiguity of parsed expressions *}

text {*
  \begin{tabular}{rcll}
    @{attribute_def syntax_ambiguity_warning} & : & @{text attribute} & default @{text true} \\
    @{attribute_def syntax_ambiguity_limit} & : & @{text attribute} & default @{text 10} \\
  \end{tabular}

  Depending on the grammar and the given input, parsing may be
  ambiguous.  Isabelle lets the Earley parser enumerate all possible
  parse trees, and then tries to make the best out of the situation.
  Terms that cannot be type-checked are filtered out, which often
  leads to a unique result in the end.  Unlike regular type
  reconstruction, which is applied to the whole collection of input
  terms simultaneously, the filtering stage only treats each given
  term in isolation.  Filtering is also not attempted for individual
  types or raw ASTs (as required for @{command translations}).

  Certain warning or error messages are printed, depending on the
  situation and the given configuration options.  Parsing ultimately
  fails, if multiple results remain after the filtering phase.

  \begin{description}

  \item @{attribute syntax_ambiguity_warning} controls output of
  explicit warning messages about syntax ambiguity.

  \item @{attribute syntax_ambiguity_limit} determines the number of
  resulting parse trees that are shown as part of the printed message
  in case of an ambiguity.

  \end{description}
*}


section {* Syntax transformations \label{sec:syntax-transformations} *}

text {* The inner syntax engine of Isabelle provides separate
  mechanisms to transform parse trees either as rewrite systems on
  first-order ASTs (\secref{sec:syn-trans}), or ML functions on ASTs
  or syntactic @{text "\<lambda>"}-terms (\secref{sec:tr-funs}).  This works
  both for parsing and printing, as outlined in
  \figref{fig:parse-print}.

  \begin{figure}[htbp]
  \begin{center}
  \begin{tabular}{cl}
  string          & \\
  @{text "\<down>"}     & lexer + parser \\
  parse tree      & \\
  @{text "\<down>"}     & parse AST translation \\
  AST             & \\
  @{text "\<down>"}     & AST rewriting (macros) \\
  AST             & \\
  @{text "\<down>"}     & parse translation \\
  --- pre-term ---    & \\
  @{text "\<down>"}     & print translation \\
  AST             & \\
  @{text "\<down>"}     & AST rewriting (macros) \\
  AST             & \\
  @{text "\<down>"}     & print AST translation \\
  string          &
  \end{tabular}
  \end{center}
  \caption{Parsing and printing with translations}\label{fig:parse-print}
  \end{figure}

  These intermediate syntax tree formats eventually lead to a pre-term
  with all names and binding scopes resolved, but most type
  information still missing.  Explicit type constraints might be given by
  the user, or implicit position information by the system --- both
  needs to be passed-through carefully by syntax transformations.

  Pre-terms are further processed by the so-called \emph{check} and
  \emph{unckeck} phases that are intertwined with type-inference (see
  also \cite{isabelle-implementation}).  The latter allows to operate
  on higher-order abstract syntax with proper binding and type
  information already available.

  As a rule of thumb, anything that manipulates bindings of variables
  or constants needs to be implemented as syntax transformation (see
  below).  Anything else is better done via check/uncheck: a prominent
  example application is the @{command abbreviation} concept of
  Isabelle/Pure. *}


subsection {* Abstract syntax trees \label{sec:ast} *}

text {* The ML datatype @{ML_type Ast.ast} explicitly represents the
  intermediate AST format that is used for syntax rewriting
  (\secref{sec:syn-trans}).  It is defined in ML as follows:
  \begin{ttbox}
  datatype ast =
    Constant of string |
    Variable of string |
    Appl of ast list
  \end{ttbox}

  An AST is either an atom (constant or variable) or a list of (at
  least two) subtrees.  Occasional diagnostic output of ASTs uses
  notation that resembles S-expression of LISP.  Constant atoms are
  shown as quoted strings, variable atoms as non-quoted strings and
  applications as a parenthesized list of subtrees.  For example, the
  AST
  @{ML [display] "Ast.Appl
  [Ast.Constant \"_abs\", Ast.Variable \"x\", Ast.Variable \"t\"]"}
  is pretty-printed as @{verbatim "(\"_abs\" x t)"}.  Note that
  @{verbatim "()"} and @{verbatim "(x)"} are excluded as ASTs, because
  they have too few subtrees.

  \medskip AST application is merely a pro-forma mechanism to indicate
  certain syntactic structures.  Thus @{verbatim "(c a b)"} could mean
  either term application or type application, depending on the
  syntactic context.

  Nested application like @{verbatim "((\"_abs\" x t) u)"} is also
  possible, but ASTs are definitely first-order: the syntax constant
  @{verbatim "\"_abs\""} does not bind the @{verbatim x} in any way.
  Proper bindings are introduced in later stages of the term syntax,
  where @{verbatim "(\"_abs\" x t)"} becomes an @{ML Abs} node and
  occurrences of @{verbatim x} in @{verbatim t} are replaced by bound
  variables (represented as de-Bruijn indices).
*}


subsubsection {* AST constants versus variables *}

text {* Depending on the situation --- input syntax, output syntax,
  translation patterns --- the distinction of atomic asts as @{ML
  Ast.Constant} versus @{ML Ast.Variable} serves slightly different
  purposes.

  Input syntax of a term such as @{text "f a b = c"} does not yet
  indicate the scopes of atomic entities @{text "f, a, b, c"}: they
  could be global constants or local variables, even bound ones
  depending on the context of the term.  @{ML Ast.Variable} leaves
  this choice still open: later syntax layers (or translation
  functions) may capture such a variable to determine its role
  specifically, to make it a constant, bound variable, free variable
  etc.  In contrast, syntax translations that introduce already known
  constants would rather do it via @{ML Ast.Constant} to prevent
  accidental re-interpretation later on.

  Output syntax turns term constants into @{ML Ast.Constant} and
  variables (free or schematic) into @{ML Ast.Variable}.  This
  information is precise when printing fully formal @{text "\<lambda>"}-terms.

  In AST translation patterns (\secref{sec:syn-trans}) the system
  guesses from the current theory context which atoms should be
  treated as constant versus variable for the matching process.
  Sometimes this needs to be indicated more explicitly using @{text
  "CONST c"} inside the term language.  It is also possible to use
  @{command syntax} declarations (without mixfix annotation) to
  enforce that certain unqualified names are always treated as
  constant within the syntax machinery.

  \medskip For ASTs that represent the language of types or sorts, the
  situation is much simpler, since the concrete syntax already
  distinguishes type variables from type constants (constructors).  So
  @{text "('a, 'b) foo"} corresponds to an AST application of some
  constant for @{text foo} and variable arguments for @{text "'a"} and
  @{text "'b"}.  Note that the postfix application is merely a feature
  of the concrete syntax, while in the AST the constructor occurs in
  head position.  *}


subsubsection {* Authentic syntax names *}

text {* Naming constant entities within ASTs is another delicate
  issue.  Unqualified names are looked up in the name space tables in
  the last stage of parsing, after all translations have been applied.
  Since syntax transformations do not know about this later name
  resolution yet, there can be surprises in boundary cases.

  \emph{Authentic syntax names} for @{ML Ast.Constant} avoid this
  problem: the fully-qualified constant name with a special prefix for
  its formal category (@{text "class"}, @{text "type"}, @{text
  "const"}, @{text "fixed"}) represents the information faithfully
  within the untyped AST format.  Accidental overlap with free or
  bound variables is excluded as well.  Authentic syntax names work
  implicitly in the following situations:

  \begin{itemize}

  \item Input of term constants (or fixed variables) that are
  introduced by concrete syntax via @{command notation}: the
  correspondence of a particular grammar production to some known term
  entity is preserved.

  \item Input type constants (constructors) and type classes ---
  thanks to explicit syntactic distinction independently on the
  context.

  \item Output of term constants, type constants, type classes ---
  this information is already available from the internal term to be
  printed.

  \end{itemize}

  In other words, syntax transformations that operate on input terms
  written as prefix applications are difficult to achieve.  Luckily,
  this case rarely occurs in practice, because syntax forms to be
  translated usually correspond to some bits of concrete notation. *}


subsection {* Raw syntax and translations \label{sec:syn-trans} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "nonterminal"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "translations"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_translations"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  Unlike mixfix notation for existing formal entities
  (\secref{sec:notation}), raw syntax declarations provide full access
  to the priority grammar of the inner syntax, without any sanity
  checks.  This includes additional syntactic categories (via
  @{command nonterminal}) and free-form grammar productions (via
  @{command syntax}).  Additional syntax translations (or macros, via
  @{command translations}) are required to turn resulting parse trees
  into proper representations of formal entities again.

  @{rail "
    @@{command nonterminal} (@{syntax name} + @'and')
    ;
    (@@{command syntax} | @@{command no_syntax}) @{syntax mode}? (constdecl +)
    ;
    (@@{command translations} | @@{command no_translations})
      (transpat ('==' | '=>' | '<=' | '\<rightleftharpoons>' | '\<rightharpoonup>' | '\<leftharpoondown>') transpat +)
    ;

    constdecl: @{syntax name} '::' @{syntax type} @{syntax mixfix}?
    ;
    mode: ('(' ( @{syntax name} | @'output' | @{syntax name} @'output' ) ')')
    ;
    transpat: ('(' @{syntax nameref} ')')? @{syntax string}
  "}

  \begin{description}

  \item @{command "nonterminal"}~@{text c} declares a type
  constructor @{text c} (without arguments) to act as purely syntactic
  type: a nonterminal symbol of the inner syntax.

  \item @{command "syntax"}~@{text "(mode) c :: \<sigma> (mx)"} augments the
  priority grammar and the pretty printer table for the given print
  mode (default @{verbatim "\"\""}). An optional keyword @{keyword_ref
  "output"} means that only the pretty printer table is affected.

  Following \secref{sec:mixfix}, the mixfix annotation @{text "mx =
  template ps q"} together with type @{text "\<sigma> = \<tau>\<^sub>1 \<Rightarrow> \<dots> \<tau>\<^sub>n \<Rightarrow> \<tau>"} and
  specify a grammar production.  The @{text template} contains
  delimiter tokens that surround @{text "n"} argument positions
  (@{verbatim "_"}).  The latter correspond to nonterminal symbols
  @{text "A\<^sub>i"} derived from the argument types @{text "\<tau>\<^sub>i"} as
  follows:
  \begin{itemize}

  \item @{text "prop"} if @{text "\<tau>\<^sub>i = prop"}

  \item @{text "logic"} if @{text "\<tau>\<^sub>i = (\<dots>)\<kappa>"} for logical type
  constructor @{text "\<kappa> \<noteq> prop"}

  \item @{text any} if @{text "\<tau>\<^sub>i = \<alpha>"} for type variables

  \item @{text "\<kappa>"} if @{text "\<tau>\<^sub>i = \<kappa>"} for nonterminal @{text "\<kappa>"}
  (syntactic type constructor)

  \end{itemize}

  Each @{text "A\<^sub>i"} is decorated by priority @{text "p\<^sub>i"} from the
  given list @{text "ps"}; misssing priorities default to 0.

  The resulting nonterminal of the production is determined similarly
  from type @{text "\<tau>"}, with priority @{text "q"} and default 1000.

  \medskip Parsing via this production produces parse trees @{text
  "t\<^sub>1, \<dots>, t\<^sub>n"} for the argument slots.  The resulting parse tree is
  composed as @{text "c t\<^sub>1 \<dots> t\<^sub>n"}, by using the syntax constant @{text
  "c"} of the syntax declaration.

  Such syntactic constants are invented on the spot, without formal
  check wrt.\ existing declarations.  It is conventional to use plain
  identifiers prefixed by a single underscore (e.g.\ @{text
  "_foobar"}).  Names should be chosen with care, to avoid clashes
  with unrelated syntax declarations.

  \medskip The special case of copy production is specified by @{text
  "c = "}@{verbatim "\"\""} (empty string).  It means that the
  resulting parse tree @{text "t"} is copied directly, without any
  further decoration.

  \item @{command "no_syntax"}~@{text "(mode) decls"} removes grammar
  declarations (and translations) resulting from @{text decls}, which
  are interpreted in the same manner as for @{command "syntax"} above.

  \item @{command "translations"}~@{text rules} specifies syntactic
  translation rules (i.e.\ macros) as first-order rewrite rules on
  ASTs (see also \secref{sec:ast}).  The theory context maintains two
  independent lists translation rules: parse rules (@{verbatim "=>"}
  or @{text "\<rightharpoonup>"}) and print rules (@{verbatim "<="} or @{text "\<leftharpoondown>"}).
  For convenience, both can be specified simultaneously as parse~/
  print rules (@{verbatim "=="} or @{text "\<rightleftharpoons>"}).

  Translation patterns may be prefixed by the syntactic category to be
  used for parsing; the default is @{text logic} which means that
  regular term syntax is used.  Both sides of the syntax translation
  rule undergo parsing and parse AST translations
  \secref{sec:tr-funs}, in order to perform some fundamental
  normalization like @{text "\<lambda>x y. b \<leadsto> \<lambda>x. \<lambda>y. b"}, but other AST
  translation rules are \emph{not} applied recursively here.

  When processing AST patterns, the inner syntax lexer runs in a
  different mode that allows identifiers to start with underscore.
  This accommodates the usual naming convention for auxiliary syntax
  constants --- those that do not have a logical counter part --- by
  allowing to specify arbitrary AST applications within the term
  syntax, independently of the corresponding concrete syntax.

  Atomic ASTs are distinguished as @{ML Ast.Constant} versus @{ML
  Ast.Variable} as follows: a qualified name or syntax constant
  declared via @{command syntax}, or parse tree head of concrete
  notation becomes @{ML Ast.Constant}, anything else @{ML
  Ast.Variable}.  Note that @{text CONST} and @{text XCONST} within
  the term language (\secref{sec:pure-grammar}) allow to enforce
  treatment as constants.

  AST rewrite rules @{text "(lhs, rhs)"} need to obey the following
  side-conditions:

  \begin{itemize}

  \item Rules must be left linear: @{text "lhs"} must not contain
  repeated variables.\footnote{The deeper reason for this is that AST
  equality is not well-defined: different occurrences of the ``same''
  AST could be decorated differently by accidental type-constraints or
  source position information, for example.}

  \item Every variable in @{text "rhs"} must also occur in @{text
  "lhs"}.

  \end{itemize}

  \item @{command "no_translations"}~@{text rules} removes syntactic
  translation rules, which are interpreted in the same manner as for
  @{command "translations"} above.

  \end{description}

  Raw syntax and translations provides a slightly more low-level
  access to the grammar and the form of resulting parse trees.  It is
  often possible to avoid this untyped macro mechanism, and use
  type-safe @{command abbreviation} or @{command notation} instead.
  Some important situations where @{command syntax} and @{command
  translations} are really need are as follows:

  \begin{itemize}

  \item Iterated replacement via recursive @{command translations}.
  For example, consider list enumeration @{term "[a, b, c, d]"} as
  defined in theory @{theory List} in Isabelle/HOL.

  \item Change of binding status of variables: anything beyond the
  built-in @{keyword "binder"} mixfix annotation requires explicit
  syntax translations.  For example, consider list filter
  comprehension @{term "[x \<leftarrow> xs . P]"} as defined in theory @{theory
  List} in Isabelle/HOL.

  \end{itemize}
*}


subsection {* Syntax translation functions \label{sec:tr-funs} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "parse_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "parse_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "typed_print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  @{rail "
  ( @@{command parse_ast_translation} | @@{command parse_translation} |
    @@{command print_translation} | @@{command typed_print_translation} |
    @@{command print_ast_translation}) ('(' @'advanced' ')')? @{syntax text}
  "}

  Syntax translation functions written in ML admit almost arbitrary
  manipulations of Isabelle's inner syntax.  Any of the above commands
  have a single @{syntax text} argument that refers to an ML
  expression of appropriate type, which are as follows by default:

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation   : (string * (ast list -> ast)) list
val parse_translation       : (string * (term list -> term)) list
val print_translation       : (string * (term list -> term)) list
val typed_print_translation : (string * (typ -> term list -> term)) list
val print_ast_translation   : (string * (ast list -> ast)) list
\end{ttbox}

  If the @{text "(advanced)"} option is given, the corresponding
  translation functions may depend on the current theory or proof
  context.  This allows to implement advanced syntax mechanisms, as
  translations functions may refer to specific theory declarations or
  auxiliary proof data.

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
val parse_translation:
  (string * (Proof.context -> term list -> term)) list
val print_translation:
  (string * (Proof.context -> term list -> term)) list
val typed_print_translation:
  (string * (Proof.context -> typ -> term list -> term)) list
val print_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
\end{ttbox}

  \medskip See also the chapter on ``Syntax Transformations'' in old
  \cite{isabelle-ref} for further details on translations on parse
  trees.
*}

end

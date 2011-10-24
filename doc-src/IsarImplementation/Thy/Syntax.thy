theory Syntax
imports Base
begin

chapter {* Concrete syntax and type-checking *}

text {* Pure @{text "\<lambda>"}-calculus as introduced in \chref{ch:logic} is
  an adequate foundation for logical languages --- in the tradition of
  \emph{higher-order abstract syntax} --- but end-users require
  additional means for reading and printing of terms and types.  This
  important add-on outside the logical core is called \emph{inner
  syntax} in Isabelle jargon, as opposed to the \emph{outer syntax} of
  the theory and proof language (cf.\ \chref{FIXME}).

  For example, according to \cite{church40} quantifiers are
  represented as higher-order constants @{text "All :: ('a \<Rightarrow> bool) \<Rightarrow>
  bool"} such that @{text "All (\<lambda>x::'a. B x)"} faithfully represents
  the idea that is displayed as @{text "\<forall>x::'a. B x"} via @{keyword
  "binder"} notation.  Moreover, type-inference in the style of
  Hindley-Milner \cite{hindleymilner} (and extensions) enables users
  to write @{text "\<forall>x. B x"} concisely, when the type @{text "'a"} is
  already clear from the context.\footnote{Type-inference taken to the
  extreme can easily confuse users, though.  Beginners often stumble
  over unexpectedly general types inferred by the system.}

  \medskip The main inner syntax operations are \emph{read} for
  parsing together with type-checking, and \emph{pretty} for formatted
  output.  See also \secref{sec:read-print}.

  Furthermore, the input and output syntax layers are sub-divided into
  separate phases for \emph{concrete syntax} versus \emph{abstract
  syntax}, see also \secref{sec:parse-unparse} and
  \secref{sec:term-check}, respectively.  This results in the
  following decomposition of the main operations:

  \begin{itemize}

  \item @{text "read = parse; check"}

  \item @{text "pretty = uncheck; unparse"}

  \end{itemize}

  Some specification package might thus intercept syntax processing at
  a well-defined stage after @{text "parse"}, to a augment the
  resulting pre-term before full type-reconstruction is performed by
  @{text "check"}, for example.  Note that the formal status of bound
  variables, versus free variables, versus constants must not be
  changed here! *}


section {* Reading and pretty printing \label{sec:read-print} *}

text {* Read and print operations are roughly dual to each other, such
  that for the user @{text "s' = pretty (read s)"} looks similar to
  the original source text @{text "s"}, but the details depend on many
  side-conditions.  There are also explicit options to control
  suppressing of type information in the output.  The default
  configuration routinely looses information, so @{text "t' = read
  (pretty t)"} might fail, produce a differently typed term, or a
  completely different term in the face of syntactic overloading!  *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.read_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.read_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.read_prop: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.pretty_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.pretty_term: "Proof.context -> term -> Pretty.T"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Parsing and unparsing \label{sec:parse-unparse} *}

text {* Parsing and unparsing converts between actual source text and
  a certain \emph{pre-term} format, where all bindings and scopes are
  resolved faithfully.  Thus the names of free variables or constants
  are already determined in the sense of the logical context, but type
  information might is still missing.  Pre-terms support an explicit
  language of \emph{type constraints} that may be augmented by user
  code to guide the later \emph{check} phase, for example.

  Actual parsing is based on traditional lexical analysis and Earley
  parsing for arbitrary context-free grammars.  The user can specify
  this via mixfix annotations.  Moreover, there are \emph{syntax
  translations} that can be augmented by the user, either
  declaratively via @{command translations} or programmatically via
  @{command parse_translation}, @{command print_translation} etc.  The
  final scope resolution is performed by the system, according to name
  spaces for types, constants etc.\ determined by the context.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.parse_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.parse_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.parse_prop: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.unparse_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.unparse_term: "Proof.context -> term -> Pretty.T"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Checking and unchecking \label{sec:term-check} *}

text {* These operations define the transition from pre-terms and
  fully-annotated terms in the sense of the logical core
  (\chref{ch:logic}).

  The \emph{check} phase is meant to subsume a variety of mechanisms
  in the manner of ``type-inference'' or ``type-reconstruction'' or
  ``type-improvement'', not just type-checking in the narrow sense.
  The \emph{uncheck} phase is roughly dual, it prunes type-information
  before pretty printing.

  A typical add-on for the check/uncheck syntax layer is the @{command
  abbreviation} mechanism.  Here the user specifies syntactic
  definitions that are managed by the system as polymorphic @{text
  "let"} bindings.  These are expanded during the @{text "check"}
  phase, and contracted during the @{text "uncheck"} phase, without
  affecting the type-assignment of the given terms.

  \medskip The precise meaning of type checking depends on the context
  --- additional check/uncheck plugins might be defined in user space!

  For example, the @{command class} command defines a context where
  @{text "check"} treats certain type instances of overloaded
  constants according to the ``dictionary construction'' of its
  logical foundation.  This involves ``type improvement''
  (specialization of slightly too general types) and replacement by
  certain locale parameters.  See also \cite{Haftmann-Wenzel:2009}.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.check_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.check_terms: "Proof.context -> term list -> term list"} \\
  @{index_ML Syntax.check_props: "Proof.context -> term list -> term list"} \\
  @{index_ML Syntax.uncheck_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.uncheck_terms: "Proof.context -> term list -> term list"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Syntax translations *}

text FIXME

text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "class_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "type_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "const_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "syntax_const"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  @{rail "
  (@@{ML_antiquotation class_syntax} |
   @@{ML_antiquotation type_syntax} |
   @@{ML_antiquotation const_syntax} |
   @@{ML_antiquotation syntax_const}) name
  "}

  \begin{description}

  \item FIXME

  \end{description}
*}

end

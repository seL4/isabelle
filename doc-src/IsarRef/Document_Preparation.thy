theory Document_Preparation
imports Base Main
begin

chapter {* Document preparation \label{ch:document-prep} *}

text {* Isabelle/Isar provides a simple document preparation system
  based on regular {PDF-\LaTeX} technology, with full support for
  hyper-links and bookmarks.  Thus the results are well suited for WWW
  browsing and as printed copies.

  \medskip Isabelle generates {\LaTeX} output while running a
  \emph{logic session} (see also \cite{isabelle-sys}).  Getting
  started with a working configuration for common situations is quite
  easy by using the Isabelle @{verbatim mkdir} and @{verbatim make}
  tools.  First invoke
\begin{ttbox}
  isabelle mkdir Foo
\end{ttbox}
  to initialize a separate directory for session @{verbatim Foo} (it
  is safe to experiment, since @{verbatim "isabelle mkdir"} never
  overwrites existing files).  Ensure that @{verbatim "Foo/ROOT.ML"}
  holds ML commands to load all theories required for this session;
  furthermore @{verbatim "Foo/document/root.tex"} should include any
  special {\LaTeX} macro packages required for your document (the
  default is usually sufficient as a start).

  The session is controlled by a separate @{verbatim IsaMakefile}
  (with crude source dependencies by default).  This file is located
  one level up from the @{verbatim Foo} directory location.  Now
  invoke
\begin{ttbox}
  isabelle make Foo
\end{ttbox}
  to run the @{verbatim Foo} session, with browser information and
  document preparation enabled.  Unless any errors are reported by
  Isabelle or {\LaTeX}, the output will appear inside the directory
  defined by the @{verbatim ISABELLE_BROWSER_INFO} setting (as
  reported by the batch job in verbose mode).

  \medskip You may also consider to tune the @{verbatim usedir}
  options in @{verbatim IsaMakefile}, for example to switch the output
  format between @{verbatim pdf} and @{verbatim dvi}, or activate the
  @{verbatim "-D"} option to retain a second copy of the generated
  {\LaTeX} sources (for manual inspection or separate runs of
  @{executable latex}).

  \medskip See \emph{The Isabelle System Manual} \cite{isabelle-sys}
  for further details on Isabelle logic sessions and theory
  presentation.  The Isabelle/HOL tutorial \cite{isabelle-hol-book}
  also covers theory presentation to some extent.
*}


section {* Markup commands \label{sec:markup} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "header"} & : & @{text "toplevel \<rightarrow> toplevel"} \\[0.5ex]
    @{command_def "chapter"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "section"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "subsection"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "subsubsection"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "text"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "text_raw"} & : & @{text "local_theory \<rightarrow> local_theory"} \\[0.5ex]
    @{command_def "sect"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "subsect"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "subsubsect"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "txt"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "txt_raw"} & : & @{text "proof \<rightarrow> proof"} \\
  \end{matharray}

  Markup commands provide a structured way to insert text into the
  document generated from a theory.  Each markup command takes a
  single @{syntax text} argument, which is passed as argument to a
  corresponding {\LaTeX} macro.  The default macros provided by
  @{file "~~/lib/texinputs/isabelle.sty"} can be redefined according
  to the needs of the underlying document and {\LaTeX} styles.

  Note that formal comments (\secref{sec:comments}) are similar to
  markup commands, but have a different status within Isabelle/Isar
  syntax.

  @{rail "
    (@@{command chapter} | @@{command section} | @@{command subsection} |
      @@{command subsubsection} | @@{command text}) @{syntax target}? @{syntax text}
    ;
    (@@{command header} | @@{command text_raw} | @@{command sect} | @@{command subsect} |
      @@{command subsubsect} | @@{command txt} | @@{command txt_raw}) @{syntax text}
  "}

  \begin{description}

  \item @{command header} provides plain text markup just preceding
  the formal beginning of a theory.  The corresponding {\LaTeX} macro
  is @{verbatim "\\isamarkupheader"}, which acts like @{command
  section} by default.
  
  \item @{command chapter}, @{command section}, @{command subsection},
  and @{command subsubsection} mark chapter and section headings
  within the main theory body or local theory targets.  The
  corresponding {\LaTeX} macros are @{verbatim "\\isamarkupchapter"},
  @{verbatim "\\isamarkupsection"}, @{verbatim
  "\\isamarkupsubsection"} etc.

  \item @{command sect}, @{command subsect}, and @{command subsubsect}
  mark section headings within proofs.  The corresponding {\LaTeX}
  macros are @{verbatim "\\isamarkupsect"}, @{verbatim
  "\\isamarkupsubsect"} etc.

  \item @{command text} and @{command txt} specify paragraphs of plain
  text.  This corresponds to a {\LaTeX} environment @{verbatim
  "\\begin{isamarkuptext}"} @{text "\<dots>"} @{verbatim
  "\\end{isamarkuptext}"} etc.

  \item @{command text_raw} and @{command txt_raw} insert {\LaTeX}
  source into the output, without additional markup.  Thus the full
  range of document manipulations becomes available, at the risk of
  messing up document output.

  \end{description}

  Except for @{command "text_raw"} and @{command "txt_raw"}, the text
  passed to any of the above markup commands may refer to formal
  entities via \emph{document antiquotations}, see also
  \secref{sec:antiq}.  These are interpreted in the present theory or
  proof context, or the named @{text "target"}.

  \medskip The proof markup commands closely resemble those for theory
  specifications, but have a different formal status and produce
  different {\LaTeX} macros.  The default definitions coincide for
  analogous commands such as @{command section} and @{command sect}.
*}


section {* Document Antiquotations \label{sec:antiq} *}

text {*
  \begin{matharray}{rcl}
    @{antiquotation_def "theory"} & : & @{text antiquotation} \\
    @{antiquotation_def "thm"} & : & @{text antiquotation} \\
    @{antiquotation_def "lemma"} & : & @{text antiquotation} \\
    @{antiquotation_def "prop"} & : & @{text antiquotation} \\
    @{antiquotation_def "term"} & : & @{text antiquotation} \\
    @{antiquotation_def term_type} & : & @{text antiquotation} \\
    @{antiquotation_def typeof} & : & @{text antiquotation} \\
    @{antiquotation_def const} & : & @{text antiquotation} \\
    @{antiquotation_def abbrev} & : & @{text antiquotation} \\
    @{antiquotation_def typ} & : & @{text antiquotation} \\
    @{antiquotation_def type} & : & @{text antiquotation} \\
    @{antiquotation_def class} & : & @{text antiquotation} \\
    @{antiquotation_def "text"} & : & @{text antiquotation} \\
    @{antiquotation_def goals} & : & @{text antiquotation} \\
    @{antiquotation_def subgoals} & : & @{text antiquotation} \\
    @{antiquotation_def prf} & : & @{text antiquotation} \\
    @{antiquotation_def full_prf} & : & @{text antiquotation} \\
    @{antiquotation_def ML} & : & @{text antiquotation} \\
    @{antiquotation_def ML_op} & : & @{text antiquotation} \\
    @{antiquotation_def ML_type} & : & @{text antiquotation} \\
    @{antiquotation_def ML_struct} & : & @{text antiquotation} \\
    @{antiquotation_def "file"} & : & @{text antiquotation} \\
  \end{matharray}

  The overall content of an Isabelle/Isar theory may alternate between
  formal and informal text.  The main body consists of formal
  specification and proof commands, interspersed with markup commands
  (\secref{sec:markup}) or document comments (\secref{sec:comments}).
  The argument of markup commands quotes informal text to be printed
  in the resulting document, but may again refer to formal entities
  via \emph{document antiquotations}.

  For example, embedding of ``@{text [source=false] "@{term [show_types] \"f x = a + x\"}"}''
  within a text block makes
  \isa{{\isacharparenleft}f{\isasymColon}{\isacharprime}a\ {\isasymRightarrow}\ {\isacharprime}a{\isacharparenright}\ {\isacharparenleft}x{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}a{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharplus}\ x} appear in the final {\LaTeX} document.

  Antiquotations usually spare the author tedious typing of logical
  entities in full detail.  Even more importantly, some degree of
  consistency-checking between the main body of formal text and its
  informal explanation is achieved, since terms and types appearing in
  antiquotations are checked within the current theory or proof
  context.

  %% FIXME less monolithic presentation, move to individual sections!?
  @{rail "
    '@{' antiquotation '}'
    ;
    @{syntax_def antiquotation}:
      @@{antiquotation theory} options @{syntax name} |
      @@{antiquotation thm} options styles @{syntax thmrefs} |
      @@{antiquotation lemma} options @{syntax prop} @'by' @{syntax method} @{syntax method}? |
      @@{antiquotation prop} options styles @{syntax prop} |
      @@{antiquotation term} options styles @{syntax term} |
      @@{antiquotation (HOL) value} options styles @{syntax term} |
      @@{antiquotation term_type} options styles @{syntax term} |
      @@{antiquotation typeof} options styles @{syntax term} |
      @@{antiquotation const} options @{syntax term} |
      @@{antiquotation abbrev} options @{syntax term} |
      @@{antiquotation typ} options @{syntax type} |
      @@{antiquotation type} options @{syntax name} |
      @@{antiquotation class} options @{syntax name} |
      @@{antiquotation text} options @{syntax name}
    ;
    @{syntax antiquotation}:
      @@{antiquotation goals} options |
      @@{antiquotation subgoals} options |
      @@{antiquotation prf} options @{syntax thmrefs} |
      @@{antiquotation full_prf} options @{syntax thmrefs} |
      @@{antiquotation ML} options @{syntax name} |
      @@{antiquotation ML_op} options @{syntax name} |
      @@{antiquotation ML_type} options @{syntax name} |
      @@{antiquotation ML_struct} options @{syntax name} |
      @@{antiquotation \"file\"} options @{syntax name}
    ;
    options: '[' (option * ',') ']'
    ;
    option: @{syntax name} | @{syntax name} '=' @{syntax name}
    ;
    styles: '(' (style + ',') ')'
    ;
    style: (@{syntax name} +)
  "}

  Note that the syntax of antiquotations may \emph{not} include source
  comments @{verbatim "(*"}~@{text "\<dots>"}~@{verbatim "*)"} nor verbatim
  text @{verbatim "{"}@{verbatim "*"}~@{text "\<dots>"}~@{verbatim
  "*"}@{verbatim "}"}.

  \begin{description}
  
  \item @{text "@{theory A}"} prints the name @{text "A"}, which is
  guaranteed to refer to a valid ancestor theory in the current
  context.

  \item @{text "@{thm a\<^sub>1 \<dots> a\<^sub>n}"} prints theorems @{text "a\<^sub>1 \<dots> a\<^sub>n"}.
  Full fact expressions are allowed here, including attributes
  (\secref{sec:syn-att}).

  \item @{text "@{prop \<phi>}"} prints a well-typed proposition @{text
  "\<phi>"}.

  \item @{text "@{lemma \<phi> by m}"} proves a well-typed proposition
  @{text "\<phi>"} by method @{text m} and prints the original @{text "\<phi>"}.

  \item @{text "@{term t}"} prints a well-typed term @{text "t"}.
  
  \item @{text "@{value t}"} evaluates a term @{text "t"} and prints
  its result, see also @{command_ref (HOL) value}.

  \item @{text "@{term_type t}"} prints a well-typed term @{text "t"}
  annotated with its type.

  \item @{text "@{typeof t}"} prints the type of a well-typed term
  @{text "t"}.

  \item @{text "@{const c}"} prints a logical or syntactic constant
  @{text "c"}.
  
  \item @{text "@{abbrev c x\<^sub>1 \<dots> x\<^sub>n}"} prints a constant abbreviation
  @{text "c x\<^sub>1 \<dots> x\<^sub>n \<equiv> rhs"} as defined in the current context.

  \item @{text "@{typ \<tau>}"} prints a well-formed type @{text "\<tau>"}.

  \item @{text "@{type \<kappa>}"} prints a (logical or syntactic) type
    constructor @{text "\<kappa>"}.

  \item @{text "@{class c}"} prints a class @{text c}.

  \item @{text "@{text s}"} prints uninterpreted source text @{text
  s}.  This is particularly useful to print portions of text according
  to the Isabelle document style, without demanding well-formedness,
  e.g.\ small pieces of terms that should not be parsed or
  type-checked yet.

  \item @{text "@{goals}"} prints the current \emph{dynamic} goal
  state.  This is mainly for support of tactic-emulation scripts
  within Isar.  Presentation of goal states does not conform to the
  idea of human-readable proof documents!

  When explaining proofs in detail it is usually better to spell out
  the reasoning via proper Isar proof commands, instead of peeking at
  the internal machine configuration.
  
  \item @{text "@{subgoals}"} is similar to @{text "@{goals}"}, but
  does not print the main goal.
  
  \item @{text "@{prf a\<^sub>1 \<dots> a\<^sub>n}"} prints the (compact) proof terms
  corresponding to the theorems @{text "a\<^sub>1 \<dots> a\<^sub>n"}. Note that this
  requires proof terms to be switched on for the current logic
  session.
  
  \item @{text "@{full_prf a\<^sub>1 \<dots> a\<^sub>n}"} is like @{text "@{prf a\<^sub>1 \<dots>
  a\<^sub>n}"}, but prints the full proof terms, i.e.\ also displays
  information omitted in the compact proof term, which is denoted by
  ``@{text _}'' placeholders there.
  
  \item @{text "@{ML s}"}, @{text "@{ML_op s}"}, @{text "@{ML_type
  s}"}, and @{text "@{ML_struct s}"} check text @{text s} as ML value,
  infix operator, type, and structure, respectively.  The source is
  printed verbatim.

  \item @{text "@{file path}"} checks that @{text "path"} refers to a
  file (or directory) and prints it verbatim.

  \end{description}
*}


subsection {* Styled antiquotations *}

text {* The antiquotations @{text thm}, @{text prop} and @{text
  term} admit an extra \emph{style} specification to modify the
  printed result.  A style is specified by a name with a possibly
  empty number of arguments;  multiple styles can be sequenced with
  commas.  The following standard styles are available:

  \begin{description}
  
  \item @{text lhs} extracts the first argument of any application
  form with at least two arguments --- typically meta-level or
  object-level equality, or any other binary relation.
  
  \item @{text rhs} is like @{text lhs}, but extracts the second
  argument.
  
  \item @{text "concl"} extracts the conclusion @{text C} from a rule
  in Horn-clause normal form @{text "A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C"}.
  
  \item @{text "prem"} @{text n} extract premise number
  @{text "n"} from from a rule in Horn-clause
  normal form @{text "A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C"}

  \end{description}
*}


subsection {* General options *}

text {* The following options are available to tune the printed output
  of antiquotations.  Note that many of these coincide with global ML
  flags of the same names.

  \begin{description}

  \item @{antiquotation_option_def show_types}~@{text "= bool"} and
  @{antiquotation_option_def show_sorts}~@{text "= bool"} control
  printing of explicit type and sort constraints.

  \item @{antiquotation_option_def show_structs}~@{text "= bool"}
  controls printing of implicit structures.

  \item @{antiquotation_option_def show_abbrevs}~@{text "= bool"}
  controls folding of abbreviations.

  \item @{antiquotation_option_def names_long}~@{text "= bool"} forces
  names of types and constants etc.\ to be printed in their fully
  qualified internal form.

  \item @{antiquotation_option_def names_short}~@{text "= bool"}
  forces names of types and constants etc.\ to be printed unqualified.
  Note that internalizing the output again in the current context may
  well yield a different result.

  \item @{antiquotation_option_def names_unique}~@{text "= bool"}
  determines whether the printed version of qualified names should be
  made sufficiently long to avoid overlap with names declared further
  back.  Set to @{text false} for more concise output.

  \item @{antiquotation_option_def eta_contract}~@{text "= bool"}
  prints terms in @{text \<eta>}-contracted form.

  \item @{antiquotation_option_def display}~@{text "= bool"} indicates
  if the text is to be output as multi-line ``display material'',
  rather than a small piece of text without line breaks (which is the
  default).

  In this mode the embedded entities are printed in the same style as
  the main theory text.

  \item @{antiquotation_option_def break}~@{text "= bool"} controls
  line breaks in non-display material.

  \item @{antiquotation_option_def quotes}~@{text "= bool"} indicates
  if the output should be enclosed in double quotes.

  \item @{antiquotation_option_def mode}~@{text "= name"} adds @{text
  name} to the print mode to be used for presentation.  Note that the
  standard setup for {\LaTeX} output is already present by default,
  including the modes @{text latex} and @{text xsymbols}.

  \item @{antiquotation_option_def margin}~@{text "= nat"} and
  @{antiquotation_option_def indent}~@{text "= nat"} change the margin
  or indentation for pretty printing of display material.

  \item @{antiquotation_option_def goals_limit}~@{text "= nat"}
  determines the maximum number of goals to be printed (for goal-based
  antiquotation).

  \item @{antiquotation_option_def source}~@{text "= bool"} prints the
  original source text of the antiquotation arguments, rather than its
  internal representation.  Note that formal checking of
  @{antiquotation "thm"}, @{antiquotation "term"}, etc. is still
  enabled; use the @{antiquotation "text"} antiquotation for unchecked
  output.

  Regular @{text "term"} and @{text "typ"} antiquotations with @{text
  "source = false"} involve a full round-trip from the original source
  to an internalized logical entity back to a source form, according
  to the syntax of the current context.  Thus the printed output is
  not under direct control of the author, it may even fluctuate a bit
  as the underlying theory is changed later on.

  In contrast, @{antiquotation_option source}~@{text "= true"}
  admits direct printing of the given source text, with the desirable
  well-formedness check in the background, but without modification of
  the printed text.

  \end{description}

  For boolean flags, ``@{text "name = true"}'' may be abbreviated as
  ``@{text name}''.  All of the above flags are disabled by default,
  unless changed from ML, say in the @{verbatim "ROOT.ML"} of the
  logic session.
*}


section {* Markup via command tags \label{sec:tags} *}

text {* Each Isabelle/Isar command may be decorated by additional
  presentation tags, to indicate some modification in the way it is
  printed in the document.

  @{rail "
    @{syntax_def tags}: ( tag * )
    ;
    tag: '%' (@{syntax ident} | @{syntax string})
  "}

  Some tags are pre-declared for certain classes of commands, serving
  as default markup if no tags are given in the text:

  \medskip
  \begin{tabular}{ll}
    @{text "theory"} & theory begin/end \\
    @{text "proof"} & all proof commands \\
    @{text "ML"} & all commands involving ML code \\
  \end{tabular}

  \medskip The Isabelle document preparation system
  \cite{isabelle-sys} allows tagged command regions to be presented
  specifically, e.g.\ to fold proof texts, or drop parts of the text
  completely.

  For example ``@{command "by"}~@{text "%invisible auto"}'' causes
  that piece of proof to be treated as @{text invisible} instead of
  @{text "proof"} (the default), which may be shown or hidden
  depending on the document setup.  In contrast, ``@{command
  "by"}~@{text "%visible auto"}'' forces this text to be shown
  invariably.

  Explicit tag specifications within a proof apply to all subsequent
  commands of the same level of nesting.  For example, ``@{command
  "proof"}~@{text "%visible \<dots>"}~@{command "qed"}'' forces the whole
  sub-proof to be typeset as @{text visible} (unless some of its parts
  are tagged differently).

  \medskip Command tags merely produce certain markup environments for
  type-setting.  The meaning of these is determined by {\LaTeX}
  macros, as defined in @{file "~~/lib/texinputs/isabelle.sty"} or
  by the document author.  The Isabelle document preparation tools
  also provide some high-level options to specify the meaning of
  arbitrary tags to ``keep'', ``drop'', or ``fold'' the corresponding
  parts of the text.  Logic sessions may also specify ``document
  versions'', where given tags are interpreted in some particular way.
  Again see \cite{isabelle-sys} for further details.
*}


section {* Railroad diagrams *}

text {*
  \begin{matharray}{rcl}
    @{antiquotation_def "rail"} & : & @{text antiquotation} \\
  \end{matharray}

  @{rail "'rail' string"}

  The @{antiquotation rail} antiquotation allows to include syntax
  diagrams into Isabelle documents.  {\LaTeX} requires the style file
  @{"file" "~~/lib/texinputs/pdfsetup.sty"}, which can be used via
  @{verbatim "\\usepackage{pdfsetup}"} in @{verbatim "root.tex"}, for
  example.

  The rail specification language is quoted here as Isabelle @{syntax
  string}; it has its own grammar given below.

  @{rail "
  rule? + ';'
  ;
  rule: ((identifier | @{syntax antiquotation}) ':')? body
  ;
  body: concatenation + '|'
  ;
  concatenation: ((atom '?'?) +) (('*' | '+') atom?)?
  ;
  atom: '(' body? ')' | identifier |
    '@'? (string | @{syntax antiquotation}) |
    '\\\\\\\\'
  "}

  The lexical syntax of @{text "identifier"} coincides with that of
  @{syntax ident} in regular Isabelle syntax, but @{text string} uses
  single quotes instead of double quotes of the standard @{syntax
  string} category, to avoid extra escapes.

  Each @{text rule} defines a formal language (with optional name),
  using a notation that is similar to EBNF or regular expressions with
  recursion.  The meaning and visual appearance of these rail language
  elements is illustrated by the following representative examples.

  \begin{itemize}

  \item Empty @{verbatim "()"}

  @{rail "()"}

  \item Nonterminal @{verbatim "A"}

  @{rail "A"}

  \item Nonterminal via Isabelle antiquotation
  @{verbatim "@{syntax method}"}

  @{rail "@{syntax method}"}

  \item Terminal @{verbatim "'xyz'"}

  @{rail "'xyz'"}

  \item Terminal in keyword style @{verbatim "@'xyz'"}

  @{rail "@'xyz'"}

  \item Terminal via Isabelle antiquotation
  @{verbatim "@@{method rule}"}

  @{rail "@@{method rule}"}

  \item Concatenation @{verbatim "A B C"}

  @{rail "A B C"}

  \item Linebreak @{verbatim "\\\\"} inside
  concatenation\footnote{Strictly speaking, this is only a single
  backslash, but the enclosing @{syntax string} syntax requires a
  second one for escaping.} @{verbatim "A B C \\\\ D E F"}

  @{rail "A B C \\ D E F"}

  \item Variants @{verbatim "A | B | C"}

  @{rail "A | B | C"}

  \item Option @{verbatim "A ?"}

  @{rail "A ?"}

  \item Repetition @{verbatim "A *"}

  @{rail "A *"}

  \item Repetition with separator @{verbatim "A * sep"}

  @{rail "A * sep"}

  \item Strict repetition @{verbatim "A +"}

  @{rail "A +"}

  \item Strict repetition with separator @{verbatim "A + sep"}

  @{rail "A + sep"}

  \end{itemize}
*}


section {* Draft presentation *}

text {*
  \begin{matharray}{rcl}
    @{command_def "display_drafts"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "print_drafts"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
  \end{matharray}

  @{rail "
    (@@{command display_drafts} | @@{command print_drafts}) (@{syntax name} +)

  "}

  \begin{description}

  \item @{command "display_drafts"}~@{text paths} and @{command
  "print_drafts"}~@{text paths} perform simple output of a given list
  of raw source files.  Only those symbols that do not require
  additional {\LaTeX} packages are displayed properly, everything else
  is left verbatim.

  \end{description}
*}

end

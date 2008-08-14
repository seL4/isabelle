(* $Id$ *)

theory Document_Preparation
imports Main
begin

chapter {* Document preparation \label{ch:document-prep} *}

text {*
  Isabelle/Isar provides a simple document preparation system based on
  existing {PDF-\LaTeX} technology, with full support of hyper-links
  (both local references and URLs) and bookmarks.  Thus the results
  are equally well suited for WWW browsing and as printed copies.

  \medskip Isabelle generates {\LaTeX} output as part of the run of a
  \emph{logic session} (see also \cite{isabelle-sys}).  Getting
  started with a working configuration for common situations is quite
  easy by using the Isabelle @{verbatim mkdir} and @{verbatim make}
  tools.  First invoke
\begin{ttbox}
  isatool mkdir Foo
\end{ttbox}
  to initialize a separate directory for session @{verbatim Foo} ---
  it is safe to experiment, since @{verbatim "isatool mkdir"} never
  overwrites existing files.  Ensure that @{verbatim "Foo/ROOT.ML"}
  holds ML commands to load all theories required for this session;
  furthermore @{verbatim "Foo/document/root.tex"} should include any
  special {\LaTeX} macro packages required for your document (the
  default is usually sufficient as a start).

  The session is controlled by a separate @{verbatim IsaMakefile}
  (with crude source dependencies by default).  This file is located
  one level up from the @{verbatim Foo} directory location.  Now
  invoke
\begin{ttbox}
  isatool make Foo
\end{ttbox}
  to run the @{verbatim Foo} session, with browser information and
  document preparation enabled.  Unless any errors are reported by
  Isabelle or {\LaTeX}, the output will appear inside the directory
  @{verbatim ISABELLE_BROWSER_INFO}, as reported by the batch job in
  verbose mode.

  \medskip You may also consider to tune the @{verbatim usedir}
  options in @{verbatim IsaMakefile}, for example to change the output
  format from @{verbatim pdf} to @{verbatim dvi}, or activate the
  @{verbatim "-D"} option to retain a second copy of the generated
  {\LaTeX} sources.

  \medskip See \emph{The Isabelle System Manual} \cite{isabelle-sys}
  for further details on Isabelle logic sessions and theory
  presentation.  The Isabelle/HOL tutorial \cite{isabelle-hol-book}
  also covers theory presentation issues.
*}


section {* Markup commands \label{sec:markup} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "header"} & : & \isarkeep{toplevel} \\[0.5ex]
    @{command_def "chapter"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "section"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "subsection"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "subsubsection"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "text"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "text_raw"} & : & \isarkeep{local{\dsh}theory} \\[0.5ex]
    @{command_def "sect"} & : & \isartrans{proof}{proof} \\
    @{command_def "subsect"} & : & \isartrans{proof}{proof} \\
    @{command_def "subsubsect"} & : & \isartrans{proof}{proof} \\
    @{command_def "txt"} & : & \isartrans{proof}{proof} \\
    @{command_def "txt_raw"} & : & \isartrans{proof}{proof} \\
  \end{matharray}

  Apart from formal comments (see \secref{sec:comments}), markup
  commands provide a structured way to insert text into the document
  generated from a theory (see \cite{isabelle-sys} for more
  information on Isabelle's document preparation tools).

  \begin{rail}
    ('chapter' | 'section' | 'subsection' | 'subsubsection' | 'text') target? text
    ;
    ('header' | 'text\_raw' | 'sect' | 'subsect' | 'subsubsect' | 'txt' | 'txt\_raw') text
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "header"}~@{text "text"}] provides plain text
  markup just preceding the formal beginning of a theory.  In actual
  document preparation the corresponding {\LaTeX} macro @{verbatim
  "\\isamarkupheader"} may be redefined to produce chapter or section
  headings.
  
  \item [@{command "chapter"}, @{command "section"}, @{command
  "subsection"}, and @{command "subsubsection"}] mark chapter and
  section headings.  The corresponding {\LaTeX} macros are @{verbatim
  "\\isamarkupchapter"}, @{verbatim "\\isamarkupsection"} etc.

  \item [@{command "text"} and @{command "txt"}] specify paragraphs of
  plain text.

  \item [@{command "text_raw"} and @{command "txt_raw"}] insert
  {\LaTeX} source into the output, without additional markup.  Thus
  the full range of document manipulations becomes available.

  \end{descr}

  The @{text "text"} argument of these markup commands (except for
  @{command "text_raw"}) may contain references to formal entities
  (``antiquotations'', see also \secref{sec:antiq}).  These are
  interpreted in the present theory context, or the named @{text
  "target"}.

  Any of these markup elements corresponds to a {\LaTeX} command with
  the name prefixed by @{verbatim "\\isamarkup"}.  For the sectioning
  commands this is a plain macro with a single argument, e.g.\
  @{verbatim "\\isamarkupchapter{"}@{text "\<dots>"}@{verbatim "}"} for
  @{command "chapter"}.  The @{command "text"} markup results in a
  {\LaTeX} environment @{verbatim "\\begin{isamarkuptext}"} @{text
  "\<dots>"} @{verbatim "\\end{isamarkuptext}"}, while @{command "text_raw"}
  causes the text to be inserted directly into the {\LaTeX} source.

  \medskip The proof markup commands closely resemble those for theory
  specifications, but have a different formal status and produce
  different {\LaTeX} macros.  Also note that the @{command_ref
  "header"} declaration (see \secref{sec:begin-thy}) admits to insert
  section markup just preceding the actual theory definition.
*}


section {* Antiquotations \label{sec:antiq} *}

text {*
  \begin{matharray}{rcl}
    @{antiquotation_def "theory"} & : & \isarantiq \\
    @{antiquotation_def "thm"} & : & \isarantiq \\
    @{antiquotation_def "lemma"} & : & \isarantiq \\
    @{antiquotation_def "prop"} & : & \isarantiq \\
    @{antiquotation_def "term"} & : & \isarantiq \\
    @{antiquotation_def const} & : & \isarantiq \\
    @{antiquotation_def abbrev} & : & \isarantiq \\
    @{antiquotation_def typeof} & : & \isarantiq \\
    @{antiquotation_def typ} & : & \isarantiq \\
    @{antiquotation_def thm_style} & : & \isarantiq \\
    @{antiquotation_def term_style} & : & \isarantiq \\
    @{antiquotation_def "text"} & : & \isarantiq \\
    @{antiquotation_def goals} & : & \isarantiq \\
    @{antiquotation_def subgoals} & : & \isarantiq \\
    @{antiquotation_def prf} & : & \isarantiq \\
    @{antiquotation_def full_prf} & : & \isarantiq \\
    @{antiquotation_def ML} & : & \isarantiq \\
    @{antiquotation_def ML_type} & : & \isarantiq \\
    @{antiquotation_def ML_struct} & : & \isarantiq \\
  \end{matharray}

  The text body of formal comments (see also \secref{sec:comments})
  may contain antiquotations of logical entities, such as theorems,
  terms and types, which are to be presented in the final output
  produced by the Isabelle document preparation system.

  Thus embedding of ``@{text [source=false] "@{term [show_types] \"f x = a + x\"}"}''
  within a text block would cause
  \isa{{\isacharparenleft}f{\isasymColon}{\isacharprime}a\ {\isasymRightarrow}\ {\isacharprime}a{\isacharparenright}\ {\isacharparenleft}x{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}a{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharplus}\ x} to appear in the final {\LaTeX} document.  Also note that theorem
  antiquotations may involve attributes as well.  For example,
  @{text "@{thm sym [no_vars]}"} would print the theorem's
  statement where all schematic variables have been replaced by fixed
  ones, which are easier to read.

  \begin{rail}
    atsign lbrace antiquotation rbrace
    ;

    antiquotation:
      'theory' options name |
      'thm' options thmrefs |
      'lemma' options prop 'by' method |
      'prop' options prop |
      'term' options term |
      'const' options term |
      'abbrev' options term |
      'typeof' options term |
      'typ' options type |
      'thm\_style' options name thmref |
      'term\_style' options name term |
      'text' options name |
      'goals' options |
      'subgoals' options |
      'prf' options thmrefs |
      'full\_prf' options thmrefs |
      'ML' options name |
      'ML\_type' options name |
      'ML\_struct' options name
    ;
    options: '[' (option * ',') ']'
    ;
    option: name | name '=' name
    ;
  \end{rail}

  Note that the syntax of antiquotations may \emph{not} include source
  comments @{verbatim "(*"}~@{text "\<dots>"}~@{verbatim "*)"} or verbatim
  text @{verbatim "{"}@{verbatim "*"}~@{text "\<dots>"}~@{verbatim
  "*"}@{verbatim "}"}.

  \begin{descr}
  
  \item [@{text "@{theory A}"}] prints the name @{text "A"}, which is
  guaranteed to refer to a valid ancestor theory in the current
  context.

  \item [@{text "@{thm a\<^sub>1 \<dots> a\<^sub>n}"}] prints theorems
  @{text "a\<^sub>1 \<dots> a\<^sub>n"}.  Note that attribute specifications
  may be included as well (see also \secref{sec:syn-att}); the
  @{attribute_ref no_vars} rule (see \secref{sec:misc-meth-att}) would
  be particularly useful to suppress printing of schematic variables.

  \item [@{text "@{prop \<phi>}"}] prints a well-typed proposition @{text
  "\<phi>"}.

  \item [@{text "@{lemma \<phi> by m}"}] asserts a well-typed proposition @{text
  "\<phi>"} to be provable by method @{text m} and prints @{text "\<phi>"}.

  \item [@{text "@{term t}"}] prints a well-typed term @{text "t"}.

  \item [@{text "@{const c}"}] prints a logical or syntactic constant
  @{text "c"}.
  
  \item [@{text "@{abbrev c x\<^sub>1 \<dots> x\<^sub>n}"}] prints a constant
  abbreviation @{text "c x\<^sub>1 \<dots> x\<^sub>n \<equiv> rhs"} as defined in
  the current context.

  \item [@{text "@{typeof t}"}] prints the type of a well-typed term
  @{text "t"}.

  \item [@{text "@{typ \<tau>}"}] prints a well-formed type @{text "\<tau>"}.
  
  \item [@{text "@{thm_style s a}"}] prints theorem @{text a},
  previously applying a style @{text s} to it (see below).
  
  \item [@{text "@{term_style s t}"}] prints a well-typed term @{text
  t} after applying a style @{text s} to it (see below).

  \item [@{text "@{text s}"}] prints uninterpreted source text @{text
  s}.  This is particularly useful to print portions of text according
  to the Isabelle {\LaTeX} output style, without demanding
  well-formedness (e.g.\ small pieces of terms that should not be
  parsed or type-checked yet).

  \item [@{text "@{goals}"}] prints the current \emph{dynamic} goal
  state.  This is mainly for support of tactic-emulation scripts
  within Isar --- presentation of goal states does not conform to
  actual human-readable proof documents.

  Please do not include goal states into document output unless you
  really know what you are doing!
  
  \item [@{text "@{subgoals}"}] is similar to @{text "@{goals}"}, but
  does not print the main goal.
  
  \item [@{text "@{prf a\<^sub>1 \<dots> a\<^sub>n}"}] prints the (compact)
  proof terms corresponding to the theorems @{text "a\<^sub>1 \<dots>
  a\<^sub>n"}. Note that this requires proof terms to be switched on
  for the current object logic (see the ``Proof terms'' section of the
  Isabelle reference manual for information on how to do this).
  
  \item [@{text "@{full_prf a\<^sub>1 \<dots> a\<^sub>n}"}] is like @{text
  "@{prf a\<^sub>1 \<dots> a\<^sub>n}"}, but displays the full proof terms,
  i.e.\ also displays information omitted in the compact proof term,
  which is denoted by ``@{text _}'' placeholders there.
  
  \item [@{text "@{ML s}"}, @{text "@{ML_type s}"}, and @{text
  "@{ML_struct s}"}] check text @{text s} as ML value, type, and
  structure, respectively.  The source is displayed verbatim.

  \end{descr}

  \medskip The following standard styles for use with @{text
  thm_style} and @{text term_style} are available:

  \begin{descr}
  
  \item [@{text lhs}] extracts the first argument of any application
  form with at least two arguments -- typically meta-level or
  object-level equality, or any other binary relation.
  
  \item [@{text rhs}] is like @{text lhs}, but extracts the second
  argument.
  
  \item [@{text "concl"}] extracts the conclusion @{text C} from a rule
  in Horn-clause normal form @{text "A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C"}.
  
  \item [@{text "prem1"}, \dots, @{text "prem9"}] extract premise
  number @{text "1, \<dots>, 9"}, respectively, from from a rule in
  Horn-clause normal form @{text "A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C"}

  \end{descr}

  \medskip
  The following options are available to tune the output.  Note that most of
  these coincide with ML flags of the same names (see also \cite{isabelle-ref}).

  \begin{descr}

  \item[@{text "show_types = bool"} and @{text "show_sorts = bool"}]
  control printing of explicit type and sort constraints.

  \item[@{text "show_structs = bool"}] controls printing of implicit
  structures.

  \item[@{text "long_names = bool"}] forces names of types and
  constants etc.\ to be printed in their fully qualified internal
  form.

  \item[@{text "short_names = bool"}] forces names of types and
  constants etc.\ to be printed unqualified.  Note that internalizing
  the output again in the current context may well yield a different
  result.

  \item[@{text "unique_names = bool"}] determines whether the printed
  version of qualified names should be made sufficiently long to avoid
  overlap with names declared further back.  Set to @{text false} for
  more concise output.

  \item[@{text "eta_contract = bool"}] prints terms in @{text
  \<eta>}-contracted form.

  \item[@{text "display = bool"}] indicates if the text is to be
  output as multi-line ``display material'', rather than a small piece
  of text without line breaks (which is the default).

  \item[@{text "break = bool"}] controls line breaks in non-display
  material.

  \item[@{text "quotes = bool"}] indicates if the output should be
  enclosed in double quotes.

  \item[@{text "mode = name"}] adds @{text name} to the print mode to
  be used for presentation (see also \cite{isabelle-ref}).  Note that
  the standard setup for {\LaTeX} output is already present by
  default, including the modes @{text latex} and @{text xsymbols}.

  \item[@{text "margin = nat"} and @{text "indent = nat"}] change the
  margin or indentation for pretty printing of display material.

  \item[@{text "source = bool"}] prints the source text of the
  antiquotation arguments, rather than the actual value.  Note that
  this does not affect well-formedness checks of @{antiquotation
  "thm"}, @{antiquotation "term"}, etc. (only the @{antiquotation
  "text"} antiquotation admits arbitrary output).

  \item[@{text "goals_limit = nat"}] determines the maximum number of
  goals to be printed.

  \item[@{text "locale = name"}] specifies an alternative locale
  context used for evaluating and printing the subsequent argument.

  \end{descr}

  For boolean flags, ``@{text "name = true"}'' may be abbreviated as
  ``@{text name}''.  All of the above flags are disabled by default,
  unless changed from ML.

  \medskip Note that antiquotations do not only spare the author from
  tedious typing of logical entities, but also achieve some degree of
  consistency-checking of informal explanations with formal
  developments: well-formedness of terms and types with respect to the
  current theory or proof context is ensured here.
*}


section {* Tagged commands \label{sec:tags} *}

text {*
  Each Isabelle/Isar command may be decorated by presentation tags:

  \indexouternonterm{tags}
  \begin{rail}
    tags: ( tag * )
    ;
    tag: '\%' (ident | string)
  \end{rail}

  The tags @{text "theory"}, @{text "proof"}, @{text "ML"} are already
  pre-declared for certain classes of commands:

 \medskip

  \begin{tabular}{ll}
    @{text "theory"} & theory begin/end \\
    @{text "proof"} & all proof commands \\
    @{text "ML"} & all commands involving ML code \\
  \end{tabular}

  \medskip The Isabelle document preparation system (see also
  \cite{isabelle-sys}) allows tagged command regions to be presented
  specifically, e.g.\ to fold proof texts, or drop parts of the text
  completely.

  For example ``@{command "by"}~@{text "%invisible auto"}'' would
  cause that piece of proof to be treated as @{text invisible} instead
  of @{text "proof"} (the default), which may be either show or hidden
  depending on the document setup.  In contrast, ``@{command
  "by"}~@{text "%visible auto"}'' would force this text to be shown
  invariably.

  Explicit tag specifications within a proof apply to all subsequent
  commands of the same level of nesting.  For example, ``@{command
  "proof"}~@{text "%visible \<dots>"}~@{command "qed"}'' would force the
  whole sub-proof to be typeset as @{text visible} (unless some of its
  parts are tagged differently).
*}


section {* Draft presentation *}

text {*
  \begin{matharray}{rcl}
    @{command_def "display_drafts"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "print_drafts"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
  \end{matharray}

  \begin{rail}
    ('display\_drafts' | 'print\_drafts') (name +)
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "display_drafts"}~@{text paths} and @{command
  "print_drafts"}~@{text paths}] perform simple output of a given list
  of raw source files.  Only those symbols that do not require
  additional {\LaTeX} packages are displayed properly, everything else
  is left verbatim.

  \end{descr}
*}

end

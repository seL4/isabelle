(*:maxLineLen=78:*)

theory Document_Preparation
  imports Main Base
begin

chapter \<open>Document preparation \label{ch:document-prep}\<close>

text \<open>
  Isabelle/Isar provides a simple document preparation system based on
  {PDF-\LaTeX}, with support for hyperlinks and bookmarks within that format.
  This allows to produce papers, books, theses etc.\ from Isabelle theory
  sources.

  {\LaTeX} output is generated while processing a \<^emph>\<open>session\<close> in batch mode, as
  explained in the \<^emph>\<open>The Isabelle System Manual\<close> @{cite "isabelle-system"}.
  The main Isabelle tools to get started with document preparation are
  @{tool_ref mkroot} and @{tool_ref build}.

  The classic Isabelle/HOL tutorial @{cite "isabelle-hol-book"} also explains
  some aspects of theory presentation.
\<close>


section \<open>Markup commands \label{sec:markup}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "chapter"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "section"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "subsection"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "subsubsection"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "paragraph"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "subparagraph"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "text"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "txt"} & : & \<open>any \<rightarrow> any\<close> \\
    @{command_def "text_raw"} & : & \<open>any \<rightarrow> any\<close> \\
  \end{matharray}

  Markup commands provide a structured way to insert text into the document
  generated from a theory. Each markup command takes a single @{syntax text}
  argument, which is passed as argument to a corresponding {\LaTeX} macro. The
  default macros provided by \<^file>\<open>~~/lib/texinputs/isabelle.sty\<close> can be
  redefined according to the needs of the underlying document and {\LaTeX}
  styles.

  Note that formal comments (\secref{sec:comments}) are similar to markup
  commands, but have a different status within Isabelle/Isar syntax.

  \<^rail>\<open>
    (@@{command chapter} | @@{command section} | @@{command subsection} |
      @@{command subsubsection} | @@{command paragraph} | @@{command subparagraph})
      @{syntax text} ';'? |
    (@@{command text} | @@{command txt} | @@{command text_raw}) @{syntax text}
  \<close>

    \<^descr> @{command chapter}, @{command section}, @{command subsection} etc.\ mark
    section headings within the theory source. This works in any context, even
    before the initial @{command theory} command. The corresponding {\LaTeX}
    macros are \<^verbatim>\<open>\isamarkupchapter\<close>, \<^verbatim>\<open>\isamarkupsection\<close>,
    \<^verbatim>\<open>\isamarkupsubsection\<close> etc.\

    \<^descr> @{command text} and @{command txt} specify paragraphs of plain text.
    This corresponds to a {\LaTeX} environment \<^verbatim>\<open>\begin{isamarkuptext}\<close> \<open>\<dots>\<close>
    \<^verbatim>\<open>\end{isamarkuptext}\<close> etc.

    \<^descr> @{command text_raw} is similar to @{command text}, but without any
    surrounding markup environment. This allows to inject arbitrary {\LaTeX}
    source into the generated document.

  All text passed to any of the above markup commands may refer to formal
  entities via \<^emph>\<open>document antiquotations\<close>, see also \secref{sec:antiq}. These
  are interpreted in the present theory or proof context.

  \<^medskip>
  The proof markup commands closely resemble those for theory specifications,
  but have a different formal status and produce different {\LaTeX} macros.
\<close>


section \<open>Document antiquotations \label{sec:antiq}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{antiquotation_def "theory"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "thm"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "lemma"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "prop"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "term"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def term_type} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def typeof} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def const} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def abbrev} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def typ} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def type} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def class} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def locale} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def bundle} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "text"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def goals} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def subgoals} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def prf} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def full_prf} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_text} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_def} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_ref} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_infix} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_infix_def} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_infix_ref} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_type} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_type_def} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_type_ref} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_structure} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_structure_def} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_structure_ref} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_functor} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_functor_def} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def ML_functor_ref} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def emph} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def bold} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def verbatim} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def bash_function} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def system_option} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def session} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "file"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "url"} & : & \<open>antiquotation\<close> \\
    @{antiquotation_def "cite"} & : & \<open>antiquotation\<close> \\
    @{command_def "print_antiquotations"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  The overall content of an Isabelle/Isar theory may alternate between formal
  and informal text. The main body consists of formal specification and proof
  commands, interspersed with markup commands (\secref{sec:markup}) or
  document comments (\secref{sec:comments}). The argument of markup commands
  quotes informal text to be printed in the resulting document, but may again
  refer to formal entities via \<^emph>\<open>document antiquotations\<close>.

  For example, embedding \<^verbatim>\<open>@{term [show_types] "f x = a + x"}\<close>
  within a text block makes
  \isa{{\isacharparenleft}f{\isasymColon}{\isacharprime}a\ {\isasymRightarrow}\ {\isacharprime}a{\isacharparenright}\ {\isacharparenleft}x{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}a{\isasymColon}{\isacharprime}a{\isacharparenright}\ {\isacharplus}\ x} appear in the final {\LaTeX} document.

  Antiquotations usually spare the author tedious typing of logical entities
  in full detail. Even more importantly, some degree of consistency-checking
  between the main body of formal text and its informal explanation is
  achieved, since terms and types appearing in antiquotations are checked
  within the current theory or proof context.

  \<^medskip>
  Antiquotations are in general written as
  \<^verbatim>\<open>@{\<close>\<open>name\<close>~\<^verbatim>\<open>[\<close>\<open>options\<close>\<^verbatim>\<open>]\<close>~\<open>arguments\<close>\<^verbatim>\<open>}\<close>. The short form
  \<^verbatim>\<open>\\<close>\<^verbatim>\<open><^\<close>\<open>name\<close>\<^verbatim>\<open>>\<close>\<open>\<open>argument_content\<close>\<close> (without surrounding \<^verbatim>\<open>@{\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close>)
  works for a single argument that is a cartouche. A cartouche without special
  decoration is equivalent to \<^verbatim>\<open>\<^cartouche>\<close>\<open>\<open>argument_content\<close>\<close>, which is
  equivalent to \<^verbatim>\<open>@{cartouche\<close>~\<open>\<open>argument_content\<close>\<close>\<^verbatim>\<open>}\<close>. The special name
  @{antiquotation_def cartouche} is defined in the context: Isabelle/Pure
  introduces that as an alias to @{antiquotation_ref text} (see below).
  Consequently, \<open>\<open>foo_bar + baz \<le> bazar\<close>\<close> prints literal quasi-formal text
  (unchecked). A control symbol \<^verbatim>\<open>\\<close>\<^verbatim>\<open><^\<close>\<open>name\<close>\<^verbatim>\<open>>\<close> within the body text, but
  without a subsequent cartouche, is equivalent to \<^verbatim>\<open>@{\<close>\<open>name\<close>\<^verbatim>\<open>}\<close>.

  \begingroup
  \def\isasymcontrolstart{\isatt{\isacharbackslash\isacharless\isacharcircum}}
  \<^rail>\<open>
    @{syntax_def antiquotation}:
      '@{' antiquotation_body '}' |
      '\<controlstart>' @{syntax_ref name} '>' @{syntax_ref cartouche} |
      @{syntax_ref cartouche}
    ;
    options: '[' (option * ',') ']'
    ;
    option: @{syntax name} | @{syntax name} '=' @{syntax name}
    ;
  \<close>
  \endgroup

  Note that the syntax of antiquotations may \<^emph>\<open>not\<close> include source comments
  \<^verbatim>\<open>(*\<close>~\<open>\<dots>\<close>~\<^verbatim>\<open>*)\<close> nor verbatim text \<^verbatim>\<open>{*\<close>~\<open>\<dots>\<close>~\<^verbatim>\<open>*}\<close>.

  %% FIXME less monolithic presentation, move to individual sections!?
  \<^rail>\<open>
    @{syntax_def antiquotation_body}:
      (@@{antiquotation text} | @@{antiquotation cartouche} | @@{antiquotation theory_text})
        options @{syntax text} |
      @@{antiquotation theory} options @{syntax embedded} |
      @@{antiquotation thm} options styles @{syntax thms} |
      @@{antiquotation lemma} options @{syntax prop} @'by' @{syntax method} @{syntax method}? |
      @@{antiquotation prop} options styles @{syntax prop} |
      @@{antiquotation term} options styles @{syntax term} |
      @@{antiquotation (HOL) value} options styles @{syntax term} |
      @@{antiquotation term_type} options styles @{syntax term} |
      @@{antiquotation typeof} options styles @{syntax term} |
      @@{antiquotation const} options @{syntax term} |
      @@{antiquotation abbrev} options @{syntax term} |
      @@{antiquotation typ} options @{syntax type} |
      @@{antiquotation type} options @{syntax embedded} |
      @@{antiquotation class} options @{syntax embedded} |
      @@{antiquotation locale} options @{syntax embedded} |
      @@{antiquotation bundle} options @{syntax embedded} |
      (@@{antiquotation command} | @@{antiquotation method} | @@{antiquotation attribute})
        options @{syntax name}
    ;
    @{syntax antiquotation}:
      @@{antiquotation goals} options |
      @@{antiquotation subgoals} options |
      @@{antiquotation prf} options @{syntax thms} |
      @@{antiquotation full_prf} options @{syntax thms} |
      @@{antiquotation ML_text} options @{syntax text} |
      @@{antiquotation ML} options @{syntax text} |
      @@{antiquotation ML_infix} options @{syntax text} |
      @@{antiquotation ML_type} options @{syntax typeargs} @{syntax text} |
      @@{antiquotation ML_structure} options @{syntax text} |
      @@{antiquotation ML_functor} options @{syntax text} |
      @@{antiquotation emph} options @{syntax text} |
      @@{antiquotation bold} options @{syntax text} |
      @@{antiquotation verbatim} options @{syntax text} |
      @@{antiquotation bash_function} options @{syntax embedded} |
      @@{antiquotation system_option} options @{syntax embedded} |
      @@{antiquotation session} options @{syntax embedded} |
      @@{antiquotation path} options @{syntax embedded} |
      @@{antiquotation "file"} options @{syntax name} |
      @@{antiquotation dir} options @{syntax name} |
      @@{antiquotation url} options @{syntax embedded} |
      @@{antiquotation cite} options @{syntax cartouche}? (@{syntax name} + @'and')
    ;
    styles: '(' (style + ',') ')'
    ;
    style: (@{syntax name} +)
    ;
    @@{command print_antiquotations} ('!'?)
  \<close>

  \<^descr> \<open>@{text s}\<close> prints uninterpreted source text \<open>s\<close>, i.e.\ inner syntax. This
  is particularly useful to print portions of text according to the Isabelle
  document style, without demanding well-formedness, e.g.\ small pieces of
  terms that should not be parsed or type-checked yet.

  It is also possible to write this in the short form \<open>\<open>s\<close>\<close> without any
  further decoration.

  \<^descr> \<open>@{theory_text s}\<close> prints uninterpreted theory source text \<open>s\<close>, i.e.\
  outer syntax with command keywords and other tokens.

  \<^descr> \<open>@{theory A}\<close> prints the session-qualified theory name \<open>A\<close>, which is
  guaranteed to refer to a valid ancestor theory in the current context.

  \<^descr> \<open>@{thm a\<^sub>1 \<dots> a\<^sub>n}\<close> prints theorems \<open>a\<^sub>1 \<dots> a\<^sub>n\<close>. Full fact expressions are
  allowed here, including attributes (\secref{sec:syn-att}).

  \<^descr> \<open>@{prop \<phi>}\<close> prints a well-typed proposition \<open>\<phi>\<close>.

  \<^descr> \<open>@{lemma \<phi> by m}\<close> proves a well-typed proposition \<open>\<phi>\<close> by method \<open>m\<close> and
  prints the original \<open>\<phi>\<close>.

  \<^descr> \<open>@{term t}\<close> prints a well-typed term \<open>t\<close>.
  
  \<^descr> \<open>@{value t}\<close> evaluates a term \<open>t\<close> and prints its result, see also
  @{command_ref (HOL) value}.

  \<^descr> \<open>@{term_type t}\<close> prints a well-typed term \<open>t\<close> annotated with its type.

  \<^descr> \<open>@{typeof t}\<close> prints the type of a well-typed term \<open>t\<close>.

  \<^descr> \<open>@{const c}\<close> prints a logical or syntactic constant \<open>c\<close>.
  
  \<^descr> \<open>@{abbrev c x\<^sub>1 \<dots> x\<^sub>n}\<close> prints a constant abbreviation \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> rhs\<close>
  as defined in the current context.

  \<^descr> \<open>@{typ \<tau>}\<close> prints a well-formed type \<open>\<tau>\<close>.

  \<^descr> \<open>@{type \<kappa>}\<close> prints a (logical or syntactic) type constructor \<open>\<kappa>\<close>.

  \<^descr> \<open>@{class c}\<close> prints a class \<open>c\<close>.

  \<^descr> \<open>@{locale c}\<close> prints a locale \<open>c\<close>.

  \<^descr> \<open>@{bundle c}\<close> prints a bundle \<open>c\<close>.

  \<^descr> \<open>@{command name}\<close>, \<open>@{method name}\<close>, \<open>@{attribute name}\<close> print checked
  entities of the Isar language.

  \<^descr> \<open>@{goals}\<close> prints the current \<^emph>\<open>dynamic\<close> goal state. This is mainly for
  support of tactic-emulation scripts within Isar. Presentation of goal states
  does not conform to the idea of human-readable proof documents!

  When explaining proofs in detail it is usually better to spell out the
  reasoning via proper Isar proof commands, instead of peeking at the internal
  machine configuration.
  
  \<^descr> \<open>@{subgoals}\<close> is similar to \<open>@{goals}\<close>, but does not print the main goal.
  
  \<^descr> \<open>@{prf a\<^sub>1 \<dots> a\<^sub>n}\<close> prints the (compact) proof terms corresponding to the
  theorems \<open>a\<^sub>1 \<dots> a\<^sub>n\<close>. Note that this requires proof terms to be switched on
  for the current logic session.
  
  \<^descr> \<open>@{full_prf a\<^sub>1 \<dots> a\<^sub>n}\<close> is like \<open>@{prf a\<^sub>1 \<dots> a\<^sub>n}\<close>, but prints the full
  proof terms, i.e.\ also displays information omitted in the compact proof
  term, which is denoted by ``\<open>_\<close>'' placeholders there.

  \<^descr> \<open>@{ML_text s}\<close> prints ML text verbatim: only the token language is
  checked.

  \<^descr> \<open>@{ML s}\<close>, \<open>@{ML_infix s}\<close>, \<open>@{ML_type s}\<close>, \<open>@{ML_structure s}\<close>, and
  \<open>@{ML_functor s}\<close> check text \<open>s\<close> as ML value, infix operator, type,
  exception, structure, and functor respectively. The source is printed
  verbatim. The variants \<open>@{ML_def s}\<close> and \<open>@{ML_ref s}\<close> etc. maintain the
  document index: ``def'' means to make a bold entry, ``ref'' means to make a
  regular entry.

  There are two forms for type constructors, with or without separate type
  arguments: this impacts only the index entry. For example, \<open>@{ML_type_ref
  \<open>'a list\<close>}\<close> makes an entry literally for ``\<open>'a list\<close>'' (sorted under the
  letter ``a''), but \<open>@{ML_type_ref 'a \<open>list\<close>}\<close> makes an entry for the
  constructor name ``\<open>list\<close>''.

  \<^descr> \<open>@{emph s}\<close> prints document source recursively, with {\LaTeX} markup
  \<^verbatim>\<open>\emph{\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close>.

  \<^descr> \<open>@{bold s}\<close> prints document source recursively, with {\LaTeX} markup
  \<^verbatim>\<open>\textbf{\<close>\<open>\<dots>\<close>\<^verbatim>\<open>}\<close>.

  \<^descr> \<open>@{verbatim s}\<close> prints uninterpreted source text literally as ASCII
  characters, using some type-writer font style.

  \<^descr> \<open>@{bash_function name}\<close> prints the given GNU bash function verbatim. The
  name is checked wrt.\ the Isabelle system environment @{cite
  "isabelle-system"}.

  \<^descr> \<open>@{system_option name}\<close> prints the given system option verbatim. The name
  is checked wrt.\ cumulative \<^verbatim>\<open>etc/options\<close> of all Isabelle components,
  notably \<^file>\<open>~~/etc/options\<close>.

  \<^descr> \<open>@{session name}\<close> prints given session name verbatim. The name is checked
  wrt.\ the dependencies of the current session.

  \<^descr> \<open>@{path name}\<close> prints the file-system path name verbatim.

  \<^descr> \<open>@{file name}\<close> is like \<open>@{path name}\<close>, but ensures that \<open>name\<close> refers to a
  plain file.

  \<^descr> \<open>@{dir name}\<close> is like \<open>@{path name}\<close>, but ensures that \<open>name\<close> refers to a
  directory.

  \<^descr> \<open>@{url name}\<close> produces markup for the given URL, which results in an
  active hyperlink within the text.

  \<^descr> \<open>@{cite name}\<close> produces a citation \<^verbatim>\<open>\cite{name}\<close> in {\LaTeX}, where the
  name refers to some Bib{\TeX} database entry. This is only checked in
  batch-mode session builds.

  The variant \<open>@{cite \<open>opt\<close> name}\<close> produces \<^verbatim>\<open>\cite[opt]{name}\<close> with some
  free-form optional argument. Multiple names are output with commas, e.g.
  \<open>@{cite foo \<AND> bar}\<close> becomes \<^verbatim>\<open>\cite{foo,bar}\<close>.

  The {\LaTeX} macro name is determined by the antiquotation option
  @{antiquotation_option_def cite_macro}, or the configuration option
  @{attribute cite_macro} in the context. For example, \<open>@{cite [cite_macro =
  nocite] foobar}\<close> produces \<^verbatim>\<open>\nocite{foobar}\<close>.

  \<^descr> @{command "print_antiquotations"} prints all document antiquotations that
  are defined in the current context; the ``\<open>!\<close>'' option indicates extra
  verbosity.
\<close>


subsection \<open>Styled antiquotations\<close>

text \<open>
  The antiquotations \<open>thm\<close>, \<open>prop\<close> and \<open>term\<close> admit an extra \<^emph>\<open>style\<close>
  specification to modify the printed result. A style is specified by a name
  with a possibly empty number of arguments; multiple styles can be sequenced
  with commas. The following standard styles are available:

  \<^descr> \<open>lhs\<close> extracts the first argument of any application form with at least
  two arguments --- typically meta-level or object-level equality, or any
  other binary relation.
  
  \<^descr> \<open>rhs\<close> is like \<open>lhs\<close>, but extracts the second argument.
  
  \<^descr> \<open>concl\<close> extracts the conclusion \<open>C\<close> from a rule in Horn-clause normal form
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C\<close>.
  
  \<^descr> \<open>prem\<close> \<open>n\<close> extract premise number \<open>n\<close> from from a rule in Horn-clause
  normal form \<open>A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C\<close>.
\<close>


subsection \<open>General options\<close>

text \<open>
  The following options are available to tune the printed output of
  antiquotations. Note that many of these coincide with system and
  configuration options of the same names.

    \<^descr> @{antiquotation_option_def show_types}~\<open>= bool\<close> and
    @{antiquotation_option_def show_sorts}~\<open>= bool\<close> control printing of
    explicit type and sort constraints.

    \<^descr> @{antiquotation_option_def show_structs}~\<open>= bool\<close> controls printing of
    implicit structures.

    \<^descr> @{antiquotation_option_def show_abbrevs}~\<open>= bool\<close> controls folding of
    abbreviations.

    \<^descr> @{antiquotation_option_def names_long}~\<open>= bool\<close> forces names of types
    and constants etc.\ to be printed in their fully qualified internal form.

    \<^descr> @{antiquotation_option_def names_short}~\<open>= bool\<close> forces names of types
    and constants etc.\ to be printed unqualified. Note that internalizing the
    output again in the current context may well yield a different result.

    \<^descr> @{antiquotation_option_def names_unique}~\<open>= bool\<close> determines whether the
    printed version of qualified names should be made sufficiently long to
    avoid overlap with names declared further back. Set to \<open>false\<close> for more
    concise output.

    \<^descr> @{antiquotation_option_def eta_contract}~\<open>= bool\<close> prints terms in
    \<open>\<eta>\<close>-contracted form.

    \<^descr> @{antiquotation_option_def display}~\<open>= bool\<close> indicates if the text is to
    be output as multi-line ``display material'', rather than a small piece of
    text without line breaks (which is the default).

    In this mode the embedded entities are printed in the same style as the
    main theory text.

    \<^descr> @{antiquotation_option_def break}~\<open>= bool\<close> controls line breaks in
    non-display material.

    \<^descr> @{antiquotation_option_def cartouche}~\<open>= bool\<close> indicates if the output
    should be delimited as cartouche.

    \<^descr> @{antiquotation_option_def quotes}~\<open>= bool\<close> indicates if the output
    should be delimited via double quotes (option @{antiquotation_option
    cartouche} takes precedence). Note that the Isabelle {\LaTeX} styles may
    suppress quotes on their own account.

    \<^descr> @{antiquotation_option_def mode}~\<open>= name\<close> adds \<open>name\<close> to the print mode
    to be used for presentation. Note that the standard setup for {\LaTeX}
    output is already present by default, with mode ``\<open>latex\<close>''.

    \<^descr> @{antiquotation_option_def margin}~\<open>= nat\<close> and
    @{antiquotation_option_def indent}~\<open>= nat\<close> change the margin or
    indentation for pretty printing of display material.

    \<^descr> @{antiquotation_option_def goals_limit}~\<open>= nat\<close> determines the maximum
    number of subgoals to be printed (for goal-based antiquotation).

    \<^descr> @{antiquotation_option_def source}~\<open>= bool\<close> prints the original source
    text of the antiquotation arguments, rather than its internal
    representation. Note that formal checking of @{antiquotation "thm"},
    @{antiquotation "term"}, etc. is still enabled; use the @{antiquotation
    "text"} antiquotation for unchecked output.

    Regular \<open>term\<close> and \<open>typ\<close> antiquotations with \<open>source = false\<close> involve a
    full round-trip from the original source to an internalized logical entity
    back to a source form, according to the syntax of the current context.
    Thus the printed output is not under direct control of the author, it may
    even fluctuate a bit as the underlying theory is changed later on.

    In contrast, @{antiquotation_option source}~\<open>= true\<close> admits direct
    printing of the given source text, with the desirable well-formedness
    check in the background, but without modification of the printed text.

    Cartouche delimiters of the argument are stripped for antiquotations that
    are internally categorized as ``embedded''.

    \<^descr> @{antiquotation_option_def source_cartouche} is like
    @{antiquotation_option source}, but cartouche delimiters are always
    preserved in the output.

  For Boolean flags, ``\<open>name = true\<close>'' may be abbreviated as ``\<open>name\<close>''. All
  of the above flags are disabled by default, unless changed specifically for
  a logic session in the corresponding \<^verbatim>\<open>ROOT\<close> file.
\<close>


section \<open>Markdown-like text structure\<close>

text \<open>
  The markup commands @{command_ref text}, @{command_ref txt}, @{command_ref
  text_raw} (\secref{sec:markup}) consist of plain text. Its internal
  structure consists of paragraphs and (nested) lists, using special Isabelle
  symbols and some rules for indentation and blank lines. This quasi-visual
  format resembles \<^emph>\<open>Markdown\<close>\<^footnote>\<open>\<^url>\<open>http://commonmark.org\<close>\<close>, but the full
  complexity of that notation is avoided.

  This is a summary of the main principles of minimal Markdown in Isabelle:

    \<^item> List items start with the following markers
      \<^descr>[itemize:] \<^verbatim>\<open>\<^item>\<close>
      \<^descr>[enumerate:] \<^verbatim>\<open>\<^enum>\<close>
      \<^descr>[description:] \<^verbatim>\<open>\<^descr>\<close>

    \<^item> Adjacent list items with same indentation and same marker are grouped
    into a single list.

    \<^item> Singleton blank lines separate paragraphs.

    \<^item> Multiple blank lines escape from the current list hierarchy.

  Notable differences to official Markdown:

    \<^item> Indentation of list items needs to match exactly.

    \<^item> Indentation is unlimited (official Markdown interprets four spaces as
    block quote).

    \<^item> List items always consist of paragraphs --- there is no notion of
    ``tight'' list.

    \<^item> Section headings are expressed via Isar document markup commands
    (\secref{sec:markup}).

    \<^item> URLs, font styles, other special content is expressed via antiquotations
    (\secref{sec:antiq}), usually with proper nesting of sub-languages via
    text cartouches.
\<close>


section \<open>Document markers and command tags \label{sec:document-markers}\<close>

text \<open>
  \emph{Document markers} are formal comments of the form \<open>\<^marker>\<open>marker_body\<close>\<close>
  (using the control symbol \<^verbatim>\<open>\<^marker>\<close>) and may occur anywhere within the
  outer syntax of a command: the inner syntax of a marker body resembles that
  for attributes (\secref{sec:syn-att}). In contrast, \emph{Command tags} may
  only occur after a command keyword and are treated as special markers as
  explained below.

  \<^rail>\<open>
    @{syntax_def marker}: '\<^marker>' @{syntax cartouche}
    ;
    @{syntax_def marker_body}: (@{syntax name} @{syntax args} * ',')
    ;
    @{syntax_def tags}: tag*
    ;
    tag: '%' (@{syntax short_ident} | @{syntax string})
  \<close>

  Document markers are stripped from the document output, but surrounding
  white-space is preserved: e.g.\ a marker at the end of a line does not
  affect the subsequent line break. Markers operate within the semantic
  presentation context of a command, and may modify it to change the overall
  appearance of a command span (e.g.\ by adding tags).

  Each document marker has its own syntax defined in the theory context; the
  following markers are predefined in Isabelle/Pure:

  \<^rail>\<open>
    (@@{document_marker_def title} |
     @@{document_marker_def creator} |
     @@{document_marker_def contributor} |
     @@{document_marker_def date} |
     @@{document_marker_def license} |
     @@{document_marker_def description}) @{syntax embedded}
    ;
    @@{document_marker_def tag} (scope?) @{syntax name}
    ;
    scope: '(' ('proof' | 'command') ')'
  \<close>

    \<^descr> \<open>\<^marker>\<open>title arg\<close>\<close>, \<open>\<^marker>\<open>creator arg\<close>\<close>, \<open>\<^marker>\<open>contributor arg\<close>\<close>, \<open>\<^marker>\<open>date arg\<close>\<close>,
    \<open>\<^marker>\<open>license arg\<close>\<close>, and \<open>\<^marker>\<open>description arg\<close>\<close> produce markup in the PIDE
    document, without any immediate effect on typesetting. This vocabulary is
    taken from the Dublin Core Metadata
    Initiative\<^footnote>\<open>\<^url>\<open>https://www.dublincore.org/specifications/dublin-core/dcmi-terms\<close>\<close>.
    The argument is an uninterpreted string, except for @{document_marker
    description}, which consists of words that are subject to spell-checking.

    \<^descr> \<open>\<^marker>\<open>tag name\<close>\<close> updates the list of command tags in the presentation
    context: later declarations take precedence, so \<open>\<^marker>\<open>tag a, tag b, tag c\<close>\<close>
    produces a reversed list. The default tags are given by the original
    \<^theory_text>\<open>keywords\<close> declaration of a command, and the system option
    @{system_option_ref document_tags}.

    The optional \<open>scope\<close> tells how far the tagging is applied to subsequent
    proof structure: ``\<^theory_text>\<open>("proof")\<close>'' means it applies to the following proof
    text, and ``\<^theory_text>\<open>(command)\<close>'' means it only applies to the current command.
    The default within a proof body is ``\<^theory_text>\<open>("proof")\<close>'', but for toplevel goal
    statements it is ``\<^theory_text>\<open>(command)\<close>''. Thus a \<open>tag\<close> marker for \<^theory_text>\<open>theorem\<close>,
    \<^theory_text>\<open>lemma\<close> etc. does \emph{not} affect its proof by default.

    An old-style command tag \<^verbatim>\<open>%\<close>\<open>name\<close> is treated like a document marker
    \<open>\<^marker>\<open>tag (proof) name\<close>\<close>: the list of command tags precedes the list of
    document markers. The head of the resulting tags in the presentation
    context is turned into {\LaTeX} environments to modify the type-setting.
    The following tags are pre-declared for certain classes of commands, and
    serve as default markup for certain kinds of commands:

    \<^medskip>
    \begin{tabular}{ll}
      \<open>document\<close> & document markup commands \\
      \<open>theory\<close> & theory begin/end \\
      \<open>proof\<close> & all proof commands \\
      \<open>ML\<close> & all commands involving ML code \\
    \end{tabular}
    \<^medskip>

  The Isabelle document preparation system @{cite "isabelle-system"} allows
  tagged command regions to be presented specifically, e.g.\ to fold proof
  texts, or drop parts of the text completely.

  For example ``\<^theory_text>\<open>by auto\<close>~\<open>\<^marker>\<open>tag invisible\<close>\<close>'' causes that piece of proof to
  be treated as \<open>invisible\<close> instead of \<open>proof\<close> (the default), which may be
  shown or hidden depending on the document setup. In contrast, ``\<^theory_text>\<open>by
  auto\<close>~\<open>\<^marker>\<open>tag visible\<close>\<close>'' forces this text to be shown invariably.

  Explicit tag specifications within a proof apply to all subsequent commands
  of the same level of nesting. For example, ``\<^theory_text>\<open>proof\<close>~\<open>\<^marker>\<open>tag invisible\<close>
  \<dots>\<close>~\<^theory_text>\<open>qed\<close>'' forces the whole sub-proof to be typeset as \<open>visible\<close> (unless
  some of its parts are tagged differently).

  \<^medskip>
  Command tags merely produce certain markup environments for type-setting.
  The meaning of these is determined by {\LaTeX} macros, as defined in
  \<^file>\<open>~~/lib/texinputs/isabelle.sty\<close> or by the document author. The Isabelle
  document preparation tools also provide some high-level options to specify
  the meaning of arbitrary tags to ``keep'', ``drop'', or ``fold'' the
  corresponding parts of the text. Logic sessions may also specify ``document
  versions'', where given tags are interpreted in some particular way. Again
  see @{cite "isabelle-system"} for further details.
\<close>


section \<open>Railroad diagrams\<close>

text \<open>
  \begin{matharray}{rcl}
    @{antiquotation_def "rail"} & : & \<open>antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
    'rail' @{syntax text}
  \<close>

  The @{antiquotation rail} antiquotation allows to include syntax diagrams
  into Isabelle documents. {\LaTeX} requires the style file
  \<^file>\<open>~~/lib/texinputs/railsetup.sty\<close>, which can be used via
  \<^verbatim>\<open>\usepackage{railsetup}\<close> in \<^verbatim>\<open>root.tex\<close>, for example.

  The rail specification language is quoted here as Isabelle @{syntax string}
  or text @{syntax "cartouche"}; it has its own grammar given below.

  \begingroup
  \def\isasymnewline{\isatt{\isacharbackslash\isacharless newline\isachargreater}}
  \<^rail>\<open>
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
    '\<newline>'
  \<close>
  \endgroup

  The lexical syntax of \<open>identifier\<close> coincides with that of @{syntax
  short_ident} in regular Isabelle syntax, but \<open>string\<close> uses single quotes
  instead of double quotes of the standard @{syntax string} category.

  Each \<open>rule\<close> defines a formal language (with optional name), using a notation
  that is similar to EBNF or regular expressions with recursion. The meaning
  and visual appearance of these rail language elements is illustrated by the
  following representative examples.

  \<^item> Empty \<^verbatim>\<open>()\<close>

  \<^rail>\<open>()\<close>

  \<^item> Nonterminal \<^verbatim>\<open>A\<close>

  \<^rail>\<open>A\<close>

  \<^item> Nonterminal via Isabelle antiquotation \<^verbatim>\<open>@{syntax method}\<close>

  \<^rail>\<open>@{syntax method}\<close>

  \<^item> Terminal \<^verbatim>\<open>'xyz'\<close>

  \<^rail>\<open>'xyz'\<close>

  \<^item> Terminal in keyword style \<^verbatim>\<open>@'xyz'\<close>

  \<^rail>\<open>@'xyz'\<close>

  \<^item> Terminal via Isabelle antiquotation \<^verbatim>\<open>@@{method rule}\<close>

  \<^rail>\<open>@@{method rule}\<close>

  \<^item> Concatenation \<^verbatim>\<open>A B C\<close>

  \<^rail>\<open>A B C\<close>

  \<^item> Newline inside concatenation \<^verbatim>\<open>A B C \<newline> D E F\<close>

  \<^rail>\<open>A B C \<newline> D E F\<close>

  \<^item> Variants \<^verbatim>\<open>A | B | C\<close>

  \<^rail>\<open>A | B | C\<close>

  \<^item> Option \<^verbatim>\<open>A ?\<close>

  \<^rail>\<open>A ?\<close>

  \<^item> Repetition \<^verbatim>\<open>A *\<close>

  \<^rail>\<open>A *\<close>

  \<^item> Repetition with separator \<^verbatim>\<open>A * sep\<close>

  \<^rail>\<open>A * sep\<close>

  \<^item> Strict repetition \<^verbatim>\<open>A +\<close>

  \<^rail>\<open>A +\<close>

  \<^item> Strict repetition with separator \<^verbatim>\<open>A + sep\<close>

  \<^rail>\<open>A + sep\<close>
\<close>

end

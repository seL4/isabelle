(*<*)
theory Documents = Main:
(*>*)

section {* Concrete Syntax \label{sec:concrete-syntax} *}

text {*
  Concerning Isabelle's ``inner'' language of simply-typed @{text
  \<lambda>}-calculus, the core concept of Isabelle's elaborate infrastructure
  for concrete syntax is that of general \bfindex{mixfix annotations}.
  Associated with any kind of name and type declaration, mixfixes give
  rise both to grammar productions for the parser and output templates
  for the pretty printer.

  In full generality, the whole affair of parser and pretty printer
  configuration is rather subtle.  Any syntax specifications given by
  end-users need to interact properly with the existing setup of
  Isabelle/Pure and Isabelle/HOL; see \cite{isabelle-ref} for further
  details.  It is particularly important to get the precedence of new
  syntactic constructs right, avoiding ambiguities with existing
  elements.

  \medskip Subsequently we introduce a few simple declaration forms
  that already cover the most common situations fairly well.
*}


subsection {* Infix Annotations *}

text {*
  Syntax annotations may be included wherever constants are declared
  directly or indirectly, including \isacommand{consts},
  \isacommand{constdefs}, or \isacommand{datatype} (for the
  constructor operations).  Type-constructors may be annotated as
  well, although this is less frequently encountered in practice
  (@{text "*"} and @{text "+"} types may come to mind).

  Infix declarations\index{infix annotations} provide a useful special
  case of mixfixes, where users need not care about the full details
  of priorities, nesting, spacing, etc.  The subsequent example of the
  exclusive-or operation on boolean values illustrates typical infix
  declarations.
*}

constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
  "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

text {*
  Any curried function with at least two arguments may be associated
  with infix syntax: @{text "xor A B"} and @{text "A [+] B"} refer to
  the same expression internally.  In partial applications with less
  than two operands there is a special notation with \isa{op} prefix:
  @{text xor} without arguments is represented as @{text "op [+]"};
  combined with plain prefix application this turns @{text "xor A"}
  into @{text "op [+] A"}.

  \medskip The string @{text [source] "[+]"} in the above declaration
  refers to the bit of concrete syntax to represent the operator,
  while the number @{text 60} determines the precedence of the whole
  construct.

  As it happens, Isabelle/HOL already spends many popular combinations
  of ASCII symbols for its own use, including both @{text "+"} and
  @{text "++"}.  Slightly more awkward combinations like the present
  @{text "[+]"} tend to be available for user extensions.  The current
  arrangement of inner syntax may be inspected via
  \commdx{print\protect\_syntax}, albeit its output is enormous.

  Operator precedence also needs some special considerations.  The
  admissible range is 0--1000.  Very low or high priorities are
  basically reserved for the meta-logic.  Syntax of Isabelle/HOL
  mainly uses the range of 10--100: the equality infix @{text "="} is
  centered at 50, logical connectives (like @{text "\<or>"} and @{text
  "\<and>"}) are below 50, and algebraic ones (like @{text "+"} and @{text
  "*"}) above 50.  User syntax should strive to coexist with common
  HOL forms, or use the mostly unused range 100--900.

  \medskip The keyword \isakeyword{infixl} specifies an operator that
  is nested to the \emph{left}: in iterated applications the more
  complex expression appears on the left-hand side: @{term "A [+] B
  [+] C"} stands for @{text "(A [+] B) [+] C"}.  Similarly,
  \isakeyword{infixr} refers to nesting to the \emph{right}, reading
  @{term "A [+] B [+] C"} as @{text "A [+] (B [+] C)"}.  In contrast,
  a \emph{non-oriented} declaration via \isakeyword{infix} would
  always demand explicit parentheses.

  Many binary operations observe the associative law, so the exact
  grouping does not matter.  Nevertheless, formal statements need be
  given in a particular format, associativity needs to be treated
  explicitly within the logic.  Exclusive-or is happens to be
  associative, as shown below.
*}

lemma xor_assoc: "(A [+] B) [+] C = A [+] (B [+] C)"
  by (auto simp add: xor_def)

text {*
  Such rules may be used in simplification to regroup nested
  expressions as required.  Note that the system would actually print
  the above statement as @{term "A [+] B [+] C = A [+] (B [+] C)"}
  (due to nesting to the left).  We have preferred to give the fully
  parenthesized form in the text for clarity.  Only in rare situations
  one may consider to force parentheses by use of non-oriented infix
  syntax; equality would probably be a typical candidate.
*}


subsection {* Mathematical Symbols \label{sec:thy-present-symbols} *}

text {*
  Concrete syntax based on plain ASCII characters has its inherent
  limitations.  Rich mathematical notation demands a larger repertoire
  of symbols.  Several standards of extended character sets have been
  proposed over decades, but none has become universally available so
  far, not even Unicode\index{Unicode}.

  Isabelle supports a generic notion of \bfindex{symbols} as the
  smallest entities of source text, without referring to internal
  encodings.  Such ``generalized characters'' may be of one of the
  following three kinds:

  \begin{enumerate}

  \item Traditional 7-bit ASCII characters.

  \item Named symbols: \verb,\,\verb,<,$ident$\verb,>, (or
  \verb,\\,\verb,<,$ident$\verb,>,).

  \item Named control symbols: \verb,\,\verb,<^,$ident$\verb,>, (or
  \verb,\\,\verb,<^,$ident$\verb,>,).

  \end{enumerate}

  Here $ident$ may be any identifier according to the usual Isabelle
  conventions.  This results in an infinite store of symbols, whose
  interpretation is left to further front-end tools.  For example, the
  \verb,\,\verb,<forall>, symbol of Isabelle is really displayed as
  $\forall$ --- both by the user-interface of Proof~General + X-Symbol
  and the Isabelle document processor (see \S\ref{FIXME}).

  A list of standard Isabelle symbols is given in
  \cite[appendix~A]{isabelle-sys}.  Users may introduce their own
  interpretation of further symbols by configuring the appropriate
  front-end tool accordingly, e.g.\ defining appropriate {\LaTeX}
  macros for document preparation.  There are also a few predefined
  control symbols, such as \verb,\,\verb,<^sub>, and
  \verb,\,\verb,<^sup>, for sub- and superscript of the subsequent
  (printable) symbol, respectively.

  \medskip The following version of our @{text xor} definition uses a
  standard Isabelle symbol to achieve typographically pleasing output.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "1") *}
(*>*)
constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>" 60)
  "A \<oplus> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"
(*<*)
local
(*>*)

text {*
  The X-Symbol package within Proof~General provides several input
  methods to enter @{text \<oplus>} in the text.  If all fails one may just
  type \verb,\,\verb,<oplus>, by hand; the display is adapted
  immediately after continuing further input.

  \medskip A slightly more refined scheme is to provide alternative
  syntax via the \bfindex{print mode} concept of Isabelle (see also
  \cite{isabelle-ref}).  By convention, the mode ``$xsymbols$'' is
  enabled whenever X-Symbol is active.  Consider the following hybrid
  declaration of @{text xor}.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "2") *}
(*>*)
constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]\<ignore>" 60)
  "A [+]\<ignore> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

syntax (xsymbols)
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>\<ignore>" 60)
(*<*)
local
(*>*)

text {*
  Here the \commdx{syntax} command acts like \isakeyword{consts}, but
  without declaring a logical constant, and with an optional print
  mode specification.  Note that the type declaration given here
  merely serves for syntactic purposes, and is not checked for
  consistency with the real constant.

  \medskip Now we may write either @{text "[+]"} or @{text "\<oplus>"} in
  input, while output uses the nicer syntax of $xsymbols$, provided
  that print mode is presently active.  This scheme is particularly
  useful for interactive development, with the user typing plain ASCII
  text, but gaining improved visual feedback from the system (say in
  current goal output).

  \begin{warn}
  Using alternative syntax declarations easily results in varying
  versions of input sources.  Isabelle provides no systematic way to
  convert alternative expressions back and forth.  Print modes only
  affect situations where formal entities are pretty printed by the
  Isabelle process (e.g.\ output of terms and types), but not the
  original theory text.
  \end{warn}

  \medskip The following variant makes the alternative @{text \<oplus>}
  notation only available for output.  Thus we may enforce input
  sources to refer to plain ASCII only.
*}

syntax (xsymbols output)
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>\<ignore>" 60)


subsection {* Prefix Annotations *}

text {*
  Prefix syntax annotations\index{prefix annotation} are just a very
  degenerate of the general mixfix form \cite{isabelle-ref}, without
  any template arguments or priorities --- just some piece of literal
  syntax.

  The following example illustrates this idea idea by associating
  common symbols with the constructors of a currency datatype.
*}

datatype currency =
    Euro nat    ("\<euro>")
  | Pounds nat  ("\<pounds>")
  | Yen nat     ("\<yen>")
  | Dollar nat  ("$")

text {*
  Here the degenerate mixfix annotations on the rightmost column
  happen to consist of a single Isabelle symbol each:
  \verb,\,\verb,<euro>,, \verb,\,\verb,<pounds>,,
  \verb,\,\verb,<yen>,, \verb,$,.

  Recall that a constructor like @{text Euro} actually is a function
  @{typ "nat \<Rightarrow> currency"}.  An expression like @{text "Euro 10"} will
  be printed as @{term "\<euro> 10"}.  Only the head of the application is
  subject to our concrete syntax; this simple form already achieves
  conformance with notational standards of the European Commission.

  \medskip Certainly, the same idea of prefix syntax also works for
  \isakeyword{consts}, \isakeyword{constdefs} etc.  For example, we
  might introduce a (slightly unrealistic) function to calculate an
  abstract currency value, by cases on the datatype constructors and
  fixed exchange rates.  The funny symbol used here is that of
  \verb,\<currency>,.
*}

consts
  currency :: "currency \<Rightarrow> nat"    ("\<currency>")


subsection {* Syntax Translations \label{sec:def-translations} *}

text{*
  FIXME

\index{syntax translations|(}%
\index{translations@\isacommand {translations} (command)|(}
Isabelle offers an additional definitional facility,
\textbf{syntax translations}.
They resemble macros: upon parsing, the defined concept is immediately
replaced by its definition.  This effect is reversed upon printing.  For example,
the symbol @{text"\<noteq>"} is defined via a syntax translation:
*}

translations "x \<noteq> y" \<rightleftharpoons> "\<not>(x = y)"

text{*\index{$IsaEqTrans@\isasymrightleftharpoons}
\noindent
Internally, @{text"\<noteq>"} never appears.

In addition to @{text"\<rightleftharpoons>"} there are
@{text"\<rightharpoonup>"}\index{$IsaEqTrans1@\isasymrightharpoonup}
and @{text"\<leftharpoondown>"}\index{$IsaEqTrans2@\isasymleftharpoondown}
for uni-directional translations, which only affect
parsing or printing.  This tutorial will not cover the details of
translations.  We have mentioned the concept merely because it
crops up occasionally; a number of HOL's built-in constructs are defined
via translations.  Translations are preferable to definitions when the new
concept is a trivial variation on an existing one.  For example, we
don't need to derive new theorems about @{text"\<noteq>"}, since existing theorems
about @{text"="} still apply.%
\index{syntax translations|)}%
\index{translations@\isacommand {translations} (command)|)}
*}


section {* Document Preparation *}

text {*
  Isabelle/Isar is centered around a certain notion of \bfindex{formal
  proof documents}\index{documents|bold}: ultimately the result of the
  user's theory development efforts is a human-readable record --- as
  a browsable PDF file or printed on paper.  The overall document
  structure follows traditional mathematical articles, with
  sectioning, explanations, definitions, theorem statements, and
  proofs.

  The Isar proof language \cite{Wenzel-PhD}, which is not covered in
  this book, admits to write formal proof texts that are acceptable
  both to the machine and human readers at the same time.  Thus
  marginal comments and explanations may be kept at a minimum.
  Nevertheless, Isabelle document output is still useful without
  actual Isar proof texts; formal specifications usually deserve their
  own coverage in the text, while unstructured proof scripts may be
  just ignore by readers (or intentionally suppressed from the text).

  \medskip The Isabelle document preparation system essentially acts
  like a formal front-end for {\LaTeX}.  After checking definitions
  and proofs the theory sources are turned into typesetting
  instructions, so the final document is known to observe quite strong
  ``soundness'' properties.  This enables users to write authentic
  reports on formal theory developments with little additional effort,
  the most tedious consistency checks are handled by the system.
*}


subsection {* Isabelle Sessions *}

text {*
  In contrast to the highly interactive mode of the formal parts of
  Isabelle/Isar theory development, the document preparation stage
  essentially works in batch-mode.  This revolves around the concept
  of a \bfindex{session}, which essentially consists of a collection
  of theory source files that contribute to a single output document.
  Each session is derived from a parent one (usually an object-logic
  image such as \texttt{HOL}); this results in an overall tree
  structure of Isabelle sessions.

  The canonical arrangement of source files of a session called
  \texttt{MySession} is as follows:

  \begin{itemize}

  \item Directory \texttt{MySession} contains the required theory
  files, say $A@1$\texttt{.thy}, \dots, $A@n$\texttt{.thy}.

  \item File \texttt{MySession/ROOT.ML} holds appropriate ML commands
  for loading all wanted theories, usually just
  \texttt{use_thy~"$A@i$"} for any $A@i$ in leaf position of the
  theory dependency graph.

  \item Directory \texttt{MySession/document} contains everything
  required for the {\LaTeX} stage, but only \texttt{root.tex} needs to
  be provided initially.  The latter file holds appropriate {\LaTeX}
  code to commence a document (\verb,\documentclass, etc.), and to
  include the generated files $A@i$\texttt{.tex} for each theory.  The
  generated file \texttt{session.tex} holds {\LaTeX} commands to
  include \emph{all} theory output files in topologically sorted
  order.

  \item In addition an \texttt{IsaMakefile} outside of directory
  \texttt{MySession} holds appropriate dependencies and invocations of
  Isabelle tools to control the batch job.  The details are covered in
  \cite{isabelle-sys}; \texttt{isatool usedir} is the most important
  entry point.

  \end{itemize}

  With everything put in its proper place, \texttt{isatool make}
  should be sufficient to process the Isabelle session completely,
  with the generated document appearing in its proper place (within
  \verb,~/isabelle/browser_info,).

  In practice, users may want to have \texttt{isatool mkdir} generate
  an initial working setup without further ado.  For example, an empty
  session \texttt{MySession} derived from \texttt{HOL} may be produced
  as follows:

\begin{verbatim}
  isatool mkdir HOL MySession
  isatool make
\end{verbatim}

  This runs the session with sensible default options, including
  verbose mode to tell the user where the result will appear.  The
  above dry run should produce should produce a single page of output
  (with a dummy title, empty table of contents etc.).  Any failure at
  that stage is likely to indicate some technical problems with your
  {\LaTeX} installation.\footnote{Especially make sure that
  \texttt{pdflatex} is present.}

  \medskip Users may now start to populate the directory
  \texttt{MySession}, and the file \texttt{MySession/ROOT.ML}
  accordingly.  \texttt{MySession/document/root.tex} should be also
  adapted at some point; the generated version is mostly
  self-explanatory.  The default versions includes the
  \texttt{isabelle} (mandatory) and \texttt{isabellesym} (required for
  mathematical symbols); further packages may required, e.g.\ for
  unusual Isabelle symbols.

  Realistic applications may demand additional files in
  \texttt{MySession/document} for the {\LaTeX} stage, such as
  \texttt{root.bib} for the bibliographic database.\footnote{Using
  that particular name of \texttt{root.bib}, the Isabelle document
  processor (actually \texttt{isatool document} \cite{isabelle-sys})
  will be smart enough to invoke \texttt{bibtex} accordingly.}

  \medskip Failure of the document preparation phase in an Isabelle
  batch session leaves the generated sources in there target location
  (as pointed out by the accompanied error message).  In case of
  {\LaTeX} errors, users may trace error messages at the file position
  of the generated text.
*}


subsection {* Structure Markup *}

subsubsection {* Sections *}

text {*
  FIXME \verb,\label, within sections;

  The large-scale structure of Isabelle documents closely follows
  {\LaTeX} convention, with chapters, sections, subsubsections etc.
  The formal Isar language includes separate structure \bfindex{markup
  commands}, which do not effect the formal content of a theory (or
  proof), but results in corresponding {\LaTeX} elements issued to the
  output.

  There are different markup commands for different formal contexts:
  in header position (just before a \isakeyword{theory} command),
  within the theory body, or within a proof.  Note that the header
  needs to be treated specially, since ordinary theory and proof
  commands may only occur \emph{after} the initial \isakeyword{theory}
  specification.

  \smallskip

  \begin{tabular}{llll}
  header & theory & proof & default meaning \\\hline
    & \commdx{chapter} & & \verb,\chapter, \\
  \commdx{header} & \commdx{section} & \commdx{sect} & \verb,\section, \\
    & \commdx{subsection} & \commdx{subsect} & \verb,\subsection, \\
    & \commdx{subsubsection} & \commdx{subsubsect} & \verb,\subsubsection, \\
  \end{tabular}

  \medskip

  From the Isabelle perspective, each markup command takes a single
  text argument (delimited by \verb,",\dots\verb,", or
  \verb,{,\verb,*,~\dots~\verb,*,\verb,},).  After stripping
  surrounding white space, the argument is passed to a {\LaTeX} macro
  \verb,\isamarkupXXX, for any command \isakeyword{XXX}.  The latter
  are defined in \verb,isabelle.sty, according to the rightmost column
  above.

  \medskip The following source fragment illustrates structure markup
  of a theory.  Note that {\LaTeX} labels may well be included inside
  of section headings as well.

  \begin{ttbox}
  header {\ttlbrace}* Some properties of Foo Bar elements *{\ttrbrace}

  theory Foo_Bar = Main:

  subsection {\ttlbrace}* Basic definitions *{\ttrbrace}

  consts
    foo :: \dots
    bar :: \dots

  defs \dots

  subsection {\ttlbrace}* Derived rules *{\ttrbrace}

  lemma fooI: \dots
  lemma fooE: \dots

  subsection {\ttlbrace}* Main theorem {\ttback}label{\ttlbrace}sec:main-theorem{\ttrbrace} *{\ttrbrace}

  theorem main: \dots

  end
  \end{ttbox}

  Users may occasionally want to change the meaning of some markup
  commands, typically via appropriate use of \verb,\renewcommand, in
  \texttt{root.tex}.  The \verb,\isamarkupheader, is a good candidate
  for some adaption, e.g.\ moving it up in the hierarchy to become
  \verb,\chapter,.

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]{\chapter{#1}}
\end{verbatim}

  Certainly, this requires to change the default
  \verb,\documentclass{article}, in \texttt{root.tex} to something
  that supports the notion of chapters in the first place, e.g.\
  \verb,\documentclass{report},.

  \medskip The {\LaTeX} macro \verb,\isabellecontext, is maintained to
  hold the name of the current theory context.  This is particularly
  useful for document headings or footings, e.g.\ like this:

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]%
  {\chapter{#1}\markright{THEORY~\isabellecontext}}
\end{verbatim}

  \noindent Make sure to include something like
  \verb,\pagestyle{headings}, in \texttt{root.tex}; the document
  should have more than 2 pages to show the effect.
*}


subsection {* Formal Comments and Antiquotations *}

text {*
  Comments of the form \verb,(,\verb,*,~\dots~\verb,*,\verb,),

*}


subsection {* Symbols and Characters *}

text {*
  FIXME \verb,\isabellestyle,
*}


subsection {* Suppressing Output *}

text {*
  By default Isabelle's document system generates a {\LaTeX} source
  file for each theory that happens to get loaded during the session.
  The generated \texttt{session.tex} file will include all of these in
  order of appearance, which in turn gets included by the standard
  \texttt{root.tex} file.  Certainly one may change the order of
  appearance or suppress unwanted theories by ignoring
  \texttt{session.tex} and include individual files in
  \texttt{root.tex} by hand.  On the other hand, such an arrangement
  requires additional efforts for maintenance.

  Alternatively, one may tune the theory loading process in
  \texttt{ROOT.ML}: traversal of the theory dependency graph may be
  fine-tuned by adding further \verb,use_thy, invocations, although
  topological sorting needs to be preserved.  Moreover, the ML
  operator \verb,no_document, temporarily disables document generation
  while executing a theory loader command; the usage is like this:

\begin{verbatim}
  no_document use_thy "Aux";
\end{verbatim}

  Theory output may be also suppressed \emph{partially} as well.
  Typical applications include research papers or slides based on
  formal developments --- these usually do not show the full formal
  content.  The special source comments
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), and
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), are interpreted by the
  document generator as open and close parenthesis for
  \bfindex{ignored material}.  Any text inside of (potentially nested)
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,),~\dots~\verb,(,\verb,*,\verb,>,\verb,*,\verb,),
  parentheses is just ignored from the output --- after correct formal
  checking.

  In the following example we suppress the slightly formalistic
  \isakeyword{theory} and \isakeyword{end} part of a theory text.

  \medskip

  \begin{tabular}{l}
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{theory A = Main:} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  ~~$\vdots$ \\
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{end} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  \end{tabular}

  \medskip

  Ignoring portions of printed text like this demands some special
  care. FIXME
*}

(*<*)
end
(*>*)

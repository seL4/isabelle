(*<*)
theory Documents = Main:
(*>*)

section {* Concrete Syntax \label{sec:concrete-syntax} *}

text {*
  Concerning Isabelle's ``inner'' language of simply-typed @{text
  \<lambda>}-calculus, the core concept of Isabelle's elaborate
  infrastructure for concrete syntax is that of general
  \bfindex{mixfix annotations}.  Associated with any kind of constant
  declaration, mixfixes affect both the grammar productions for the
  parser and output templates for the pretty printer.

  In full generality, the whole affair of parser and pretty printer
  configuration is rather subtle, see also \cite{isabelle-ref}.
  Syntax specifications given by end-users need to interact properly
  with the existing setup of Isabelle/Pure and Isabelle/HOL.  It is
  particularly important to get the precedence of new syntactic
  constructs right, avoiding ambiguities with existing elements.

  \medskip Subsequently we introduce a few simple syntax declaration
  forms that already cover most common situations fairly well.
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
  of priorities, nesting, spacing, etc.  The following example of the
  exclusive-or operation on boolean values illustrates typical infix
  declarations arising in practice.
*}

constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
  "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

text {*
  \noindent Now @{text "xor A B"} and @{text "A [+] B"} refer to the
  same expression internally.  Any curried function with at least two
  arguments may be associated with infix syntax.  For partial
  applications with less than two operands there is a special notation
  with \isa{op} prefix: @{text xor} without arguments is represented
  as @{text "op [+]"}; together with plain prefix application this
  turns @{text "xor A"} into @{text "op [+] A"}.

  \medskip The string @{text [source] "[+]"} in the above annotation
  refers to the bit of concrete syntax to represent the operator,
  while the number @{text 60} determines the precedence of the
  construct (i.e.\ the syntactic priorities of the arguments and
  result).

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

  The keyword \isakeyword{infixl} specifies an infix operator that is
  nested to the \emph{left}: in iterated applications the more complex
  expression appears on the left-hand side: @{term "A [+] B [+] C"}
  stands for @{text "(A [+] B) [+] C"}.  Similarly,
  \isakeyword{infixr} specifies to nesting to the \emph{right},
  reading @{term "A [+] B [+] C"} as @{text "A [+] (B [+] C)"}.  In
  contrast, a \emph{non-oriented} declaration via \isakeyword{infix}
  would render @{term "A [+] B [+] C"} illegal, but demand explicit
  parentheses to indicate the intended grouping.
*}


subsection {* Mathematical Symbols \label{sec:syntax-symbols} *}

text {*
  Concrete syntax based on plain ASCII characters has its inherent
  limitations.  Rich mathematical notation demands a larger repertoire
  of glyphs.  Several standards of extended character sets have been
  proposed over decades, but none has become universally available so
  far.  Isabelle supports a generic notion of \bfindex{symbols} as the
  smallest entities of source text, without referring to internal
  encodings.  There are three kinds of such ``generalized
  characters'':

  \begin{enumerate}

  \item 7-bit ASCII characters

  \item named symbols: \verb,\,\verb,<,$ident$\verb,>,

  \item named control symbols: \verb,\,\verb,<^,$ident$\verb,>,

  \end{enumerate}

  Here $ident$ may be any identifier according to the usual Isabelle
  conventions.  This results in an infinite store of symbols, whose
  interpretation is left to further front-end tools.  For example,
  both the user-interface of Proof~General + X-Symbol and the Isabelle
  document processor (see \S\ref{sec:document-preparation}) display
  the \verb,\,\verb,<forall>, symbol really as @{text \<forall>}.

  A list of standard Isabelle symbols is given in
  \cite[appendix~A]{isabelle-sys}.  Users may introduce their own
  interpretation of further symbols by configuring the appropriate
  front-end tool accordingly, e.g.\ by defining certain {\LaTeX}
  macros (see also \S\ref{sec:doc-prep-symbols}).  There are also a
  few predefined control symbols, such as \verb,\,\verb,<^sub>, and
  \verb,\,\verb,<^sup>, for sub- and superscript of the subsequent
  (printable) symbol, respectively.  For example, \verb,A\<^sup>\<star>, is
  output as @{text "A\<^sup>\<star>"}.

  \medskip The following version of our @{text xor} definition uses a
  standard Isabelle symbol to achieve typographically more pleasing
  output than before.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "version1") *}
(*>*)
constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>" 60)
  "A \<oplus> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"
(*<*)
local
(*>*)

text {*
  \noindent The X-Symbol package within Proof~General provides several
  input methods to enter @{text \<oplus>} in the text.  If all fails one may
  just type a named entity \verb,\,\verb,<oplus>, by hand; the display
  will be adapted immediately after continuing input.

  \medskip A slightly more refined scheme is to provide alternative
  syntax via the \bfindex{print mode} concept of Isabelle (see also
  \cite{isabelle-ref}).  By convention, the mode of ``$xsymbols$'' is
  enabled whenever Proof~General's X-Symbol mode (or {\LaTeX} output)
  is active.  Now consider the following hybrid declaration of @{text
  xor}.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "version2") *}
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
  The \commdx{syntax} command introduced here acts like
  \isakeyword{consts}, but without declaring a logical constant; an
  optional print mode specification may be given, too.  Note that the
  type declaration given above merely serves for syntactic purposes,
  and is not checked for consistency with the real constant.

  \medskip We may now write @{text "A [+] B"} or @{text "A \<oplus> B"} in
  input, while output uses the nicer syntax of $xsymbols$, provided
  that print mode is active.  Such an arrangement is particularly
  useful for interactive development, where users may type plain ASCII
  text, but gain improved visual feedback from the system.

  \begin{warn}
  Alternative syntax declarations are apt to result in varying
  occurrences of concrete syntax in the input sources.  Isabelle
  provides no systematic way to convert alternative syntax expressions
  back and forth; print modes only affect situations where formal
  entities are pretty printed by the Isabelle process (e.g.\ output of
  terms and types), but not the original theory text.
  \end{warn}

  \medskip The following variant makes the alternative @{text \<oplus>}
  notation only available for output.  Thus we may enforce input
  sources to refer to plain ASCII only, but effectively disable
  cut-and-paste from output at the same time.
*}

syntax (xsymbols output)
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>\<ignore>" 60)


subsection {* Prefix Annotations *}

text {*
  Prefix syntax annotations\index{prefix annotation} are just another
  degenerate form of mixfixes \cite{isabelle-ref}, without any
  template arguments or priorities --- just some bits of literal
  syntax.  The following example illustrates this idea idea by
  associating common symbols with the constructors of a datatype.
*}

datatype currency =
    Euro nat    ("\<euro>")
  | Pounds nat  ("\<pounds>")
  | Yen nat     ("\<yen>")
  | Dollar nat  ("$")

text {*
  \noindent Here the mixfix annotations on the rightmost column happen
  to consist of a single Isabelle symbol each: \verb,\,\verb,<euro>,,
  \verb,\,\verb,<pounds>,, \verb,\,\verb,<yen>,, and \verb,$,.  Recall
  that a constructor like @{text Euro} actually is a function @{typ
  "nat \<Rightarrow> currency"}.  An expression like @{text "Euro 10"} will be
  printed as @{term "\<euro> 10"}; only the head of the application is
  subject to our concrete syntax.  This simple form already achieves
  conformance with notational standards of the European Commission.

  Prefix syntax also works for plain \isakeyword{consts} or
  \isakeyword{constdefs}, of course.
*}


subsection {* Syntax Translations \label{sec:syntax-translations} *}

text{*
  Mixfix syntax annotations work well in those situations where
  particular constant application forms need to be decorated by
  concrete syntax; just reconsider @{text "xor A B"} versus @{text "A
  \<oplus> B"} covered before.  Occasionally the relationship between some
  piece of notation and its internal form is slightly more involved.
  Here the concept of \bfindex{syntax translations} enters the scene.

  Using the raw \isakeyword{syntax}\index{syntax (command)} command we
  may introduce uninterpreted notational elements, while
  \commdx{translations} relates input forms with more complex logical
  expressions.  This essentially provides a simple mechanism for
  syntactic macros; even heavier transformations may be written in ML
  \cite{isabelle-ref}.

  \medskip A typical example of syntax translations is to decorate
  relational expressions (i.e.\ set-membership of tuples) with
  handsome symbolic notation, such as @{text "(x, y) \<in> sim"} versus
  @{text "x \<approx> y"}.
*}

consts
  sim :: "('a \<times> 'a) set"

syntax
  "_sim" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infix "\<approx>" 50)
translations
  "x \<approx> y" \<rightleftharpoons> "(x, y) \<in> sim"

text {*
  \noindent Here the name of the dummy constant @{text "_sim"} does
  not really matter, as long as it is not used elsewhere.  Prefixing
  an underscore is a common convention.  The \isakeyword{translations}
  declaration already uses concrete syntax on the left-hand side;
  internally we relate a raw application @{text "_sim x y"} with
  @{text "(x, y) \<in> sim"}.

  \medskip Another common application of syntax translations is to
  provide variant versions of fundamental relational expressions, such
  as @{text \<noteq>} for negated equalities.  The following declaration
  stems from Isabelle/HOL itself:
*}

syntax "_not_equal" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infixl "\<noteq>\<ignore>" 50)
translations "x \<noteq>\<ignore> y" \<rightleftharpoons> "\<not> (x = y)"

text {*
  \noindent Normally one would introduce derived concepts like this
  within the logic, using \isakeyword{consts} + \isakeyword{defs}
  instead of \isakeyword{syntax} + \isakeyword{translations}.  The
  present formulation has the virtue that expressions are immediately
  replaced by the ``definition'' upon parsing; the effect is reversed
  upon printing.

  Simulating definitions via translations is adequate for very basic
  principles, where a new representation is a trivial variation on an
  existing one.  On the other hand, syntax translations do not scale
  up well to large hierarchies of concepts built on each other.
*}


section {* Document Preparation \label{sec:document-preparation} *}

text {*
  Isabelle/Isar is centered around the concept of \bfindex{formal
  proof documents}\index{documents|bold}.  The ultimate result of a
  formal development effort is meant to be a human-readable record,
  presented as browsable PDF file or printed on paper.  The overall
  document structure follows traditional mathematical articles, with
  sections, intermediate explanations, definitions, theorems and
  proofs.

  The Isar proof language \cite{Wenzel-PhD}, which is not covered in
  this book, admits to write formal proof texts that are acceptable
  both to the machine and human readers at the same time.  Thus
  marginal comments and explanations may be kept at a minimum.  Even
  without proper coverage of human-readable proofs, Isabelle document
  preparation is very useful to produce formally derived texts.
  Unstructured proof scripts given here may be just ignored by
  readers, or intentionally suppressed from the text by the writer
  (see also \S\ref{sec:doc-prep-suppress}).

  \medskip The Isabelle document preparation system essentially acts
  as a front-end to {\LaTeX}.  After checking specifications and
  proofs formally, the theory sources are turned into typesetting
  instructions in a schematic manner.  This enables users to write
  authentic reports on theory developments with little effort, where
  most consistency checks are handled by the system.
*}


subsection {* Isabelle Sessions *}

text {*
  In contrast to the highly interactive mode of Isabelle/Isar theory
  development, the document preparation stage essentially works in
  batch-mode.  An Isabelle \bfindex{session} consists of a collection
  of theory source files that may contribute to an output document
  eventually.  Each session is derived from a single parent, usually
  an object-logic image like \texttt{HOL}.  This results in an overall
  tree structure, which is reflected by the output location in the
  file system (usually rooted at \verb,~/isabelle/browser_info,).

  \medskip The easiest way to manage Isabelle sessions is via
  \texttt{isatool mkdir} (generates an initial session source setup)
  and \texttt{isatool make} (run sessions controlled by
  \texttt{IsaMakefile}).  For example, a new session
  \texttt{MySession} derived from \texttt{HOL} may be produced as
  follows:

\begin{verbatim}
  isatool mkdir HOL MySession
  isatool make
\end{verbatim}

  The \texttt{isatool make} job also informs about the file-system
  location of the ultimate results.  The above dry run should be able
  to produce some \texttt{document.pdf} (with dummy title, empty table
  of contents etc.).  Any failure at that stage usually indicates
  technical problems of the {\LaTeX} installation.\footnote{Especially
  make sure that \texttt{pdflatex} is present; if all fails one may
  fall back on DVI output by changing \texttt{usedir} options in
  \texttt{IsaMakefile} \cite{isabelle-sys}.}

  \medskip The detailed arrangement of the session sources is as
  follows:

  \begin{itemize}

  \item Directory \texttt{MySession} holds the required theory files
  $T@1$\texttt{.thy}, \dots, $T@n$\texttt{.thy}.

  \item File \texttt{MySession/ROOT.ML} holds appropriate ML commands
  for loading all wanted theories, usually just
  ``\texttt{use_thy"$T@i$";}'' for any $T@i$ in leaf position of the
  dependency graph.

  \item Directory \texttt{MySession/document} contains everything
  required for the {\LaTeX} stage; only \texttt{root.tex} needs to be
  provided initially.

  The latter file holds appropriate {\LaTeX} code to commence a
  document (\verb,\documentclass, etc.), and to include the generated
  files $T@i$\texttt{.tex} for each theory.  The generated
  \texttt{session.tex} will contain {\LaTeX} commands to include all
  generated files in topologically sorted order, so
  \verb,\input{session}, in \texttt{root.tex} does the job in most
  situations.

  \item \texttt{IsaMakefile} holds appropriate dependencies and
  invocations of Isabelle tools to control the batch job.  In fact,
  several sessions may be controlled by the same \texttt{IsaMakefile}.
  See also \cite{isabelle-sys} for further details, especially on
  \texttt{isatool usedir} and \texttt{isatool make}.

  \end{itemize}

  One may now start to populate the directory \texttt{MySession}, and
  the file \texttt{MySession/ROOT.ML} accordingly.
  \texttt{MySession/document/root.tex} should also be adapted at some
  point; the default version is mostly self-explanatory.  Note that
  \verb,\isabellestyle, enables fine-tuning of the general appearance
  of characters and mathematical symbols (see also
  \S\ref{sec:doc-prep-symbols}).

  Especially observe the included {\LaTeX} packages \texttt{isabelle}
  (mandatory), \texttt{isabellesym} (required for mathematical
  symbols), and the final \texttt{pdfsetup} (provides handsome
  defaults for \texttt{hyperref}, including URL markup) --- all three
  are distributed with Isabelle. Further packages may be required in
  particular applications, e.g.\ for unusual mathematical symbols.

  \medskip Additional files for the {\LaTeX} stage may be put into the
  \texttt{MySession/document} directory, too.  In particular, adding
  \texttt{root.bib} here (with that specific name) causes an automatic
  run of \texttt{bibtex} to process a bibliographic database; see also
  \texttt{isatool document} covered in \cite{isabelle-sys}.

  \medskip Any failure of the document preparation phase in an
  Isabelle batch session leaves the generated sources in their target
  location (as pointed out by the accompanied error message).  This
  enables users to trace {\LaTeX} problems with the target files at
  hand.
*}


subsection {* Structure Markup *}

text {*
  The large-scale structure of Isabelle documents follows existing
  {\LaTeX} conventions, with chapters, sections, subsubsections etc.
  The Isar language includes separate \bfindex{markup commands}, which
  do not affect the formal meaning of a theory (or proof), but result
  in corresponding {\LaTeX} elements.

  There are separate markup commands depending on the textual context:
  in header position (just before \isakeyword{theory}), within the
  theory body, or within a proof.  The header needs to be treated
  specially here, since ordinary theory and proof commands may only
  occur \emph{after} the initial \isakeyword{theory} specification.

  \medskip

  \begin{tabular}{llll}
  header & theory & proof & default meaning \\\hline
    & \commdx{chapter} & & \verb,\chapter, \\
  \commdx{header} & \commdx{section} & \commdx{sect} & \verb,\section, \\
    & \commdx{subsection} & \commdx{subsect} & \verb,\subsection, \\
    & \commdx{subsubsection} & \commdx{subsubsect} & \verb,\subsubsection, \\
  \end{tabular}

  \medskip

  From the Isabelle perspective, each markup command takes a single
  $text$ argument (delimited by \verb,",\dots\verb,", or
  \verb,{,\verb,*,~\dots~\verb,*,\verb,},).  After stripping any
  surrounding white space, the argument is passed to a {\LaTeX} macro
  \verb,\isamarkupXYZ, for any command \isakeyword{XYZ}.  These macros
  are defined in \verb,isabelle.sty, according to the meaning given in
  the rightmost column above.

  \medskip The following source fragment illustrates structure markup
  of a theory.  Note that {\LaTeX} labels may be included inside of
  section headings as well.

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

  Users may occasionally want to change the meaning of markup
  commands, say via \verb,\renewcommand, in \texttt{root.tex};
  \verb,\isamarkupheader, is a good candidate for some tuning, e.g.\
  moving it up in the hierarchy to become \verb,\chapter,.

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]{\chapter{#1}}
\end{verbatim}

  \noindent Certainly, this requires to change the default
  \verb,\documentclass{article}, in \texttt{root.tex} to something
  that supports the notion of chapters in the first place, e.g.\
  \verb,\documentclass{report},.

  \medskip The {\LaTeX} macro \verb,\isabellecontext, is maintained to
  hold the name of the current theory context.  This is particularly
  useful for document headings:

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]
  {\chapter{#1}\markright{THEORY~\isabellecontext}}
\end{verbatim}

  \noindent Make sure to include something like
  \verb,\pagestyle{headings}, in \texttt{root.tex}; the document
  should have more than 2 pages to show the effect.
*}


subsection {* Formal Comments and Antiquotations *}

text {*
  Isabelle source comments, which are of the form
  \verb,(,\verb,*,~\dots~\verb,*,\verb,),, essentially act like white
  space and do not really contribute to the content.  They mainly
  serve technical purposes to mark certain oddities in the raw input
  text.  In contrast, \bfindex{formal comments} are portions of text
  that are associated with formal Isabelle/Isar commands
  (\bfindex{marginal comments}), or as standalone paragraphs within a
  theory or proof context (\bfindex{text blocks}).

  \medskip Marginal comments are part of each command's concrete
  syntax \cite{isabelle-ref}; the common form is ``\verb,--,~$text$''
  where $text$ is delimited by \verb,",\dots\verb,", or
  \verb,{,\verb,*,~\dots~\verb,*,\verb,}, as before.  Multiple
  marginal comments may be given at the same time.  Here is a simple
  example:
*}

lemma "A --> A"
  -- "a triviality of propositional logic"
  -- "(should not really bother)"
  by (rule impI) -- "implicit assumption step involved here"

text {*
  \noindent The above output has been produced as follows:

\begin{verbatim}
  lemma "A --> A"
    -- "a triviality of propositional logic"
    -- "(should not really bother)"
    by (rule impI) -- "implicit assumption step involved here"
\end{verbatim}

  From the {\LaTeX} viewpoint, ``\verb,--,'' acts like a markup
  command, associated with the macro \verb,\isamarkupcmt, (taking a
  single argument).

  \medskip Text blocks are introduced by the commands \bfindex{text}
  and \bfindex{txt}, for theory and proof contexts, respectively.
  Each takes again a single $text$ argument, which is interpreted as a
  free-form paragraph in {\LaTeX} (surrounded by some additional
  vertical space).  This behavior may be changed by redefining the
  {\LaTeX} environments of \verb,isamarkuptext, or
  \verb,isamarkuptxt,, respectively (via \verb,\renewenvironment,) The
  text style of the body is determined by \verb,\isastyletext, and
  \verb,\isastyletxt,; the default setup uses a smaller font within
  proofs.

  \medskip The $text$ part of each of the various markup commands
  considered so far essentially inserts \emph{quoted material} into a
  formal text, mainly for instruction of the reader.  An
  \bfindex{antiquotation} is again a formal object embedded into such
  an informal portion.  The interpretation of antiquotations is
  limited to some well-formedness checks, with the result being pretty
  printed to the resulting document.  So quoted text blocks together
  with antiquotations provide very handsome means to reference formal
  entities with good confidence in getting the technical details right
  (especially syntax and types).

  The general syntax of antiquotations is as follows:
  \texttt{{\at}{\ttlbrace}$name$ $arguments${\ttrbrace}}, or
  \texttt{{\at}{\ttlbrace}$name$ [$options$] $arguments${\ttrbrace}}
  for a comma-separated list of options consisting of a $name$ or
  \texttt{$name$=$value$}.  The syntax of $arguments$ depends on the
  kind of antiquotation, it generally follows the same conventions for
  types, terms, or theorems as in the formal part of a theory.

  \medskip Here is an example of the quotation-antiquotation
  technique: @{term "%x y. x"} is a well-typed term.

  \medskip\noindent The above output has been produced as follows:
  \begin{ttbox}
text {\ttlbrace}*
  Here is an example of the quotation-antiquotation technique:
  {\at}{\ttlbrace}term "%x y. x"{\ttrbrace} is a well-typed term.
*{\ttrbrace}
  \end{ttbox}

  From the notational change of the ASCII character \verb,%, to the
  symbol @{text \<lambda>} we see that the term really got printed by the
  system (after parsing and type-checking) --- document preparation
  enables symbolic output by default.

  \medskip The next example includes an option to modify the
  \verb,show_types, flag of Isabelle:
  \texttt{{\at}}\verb,{term [show_types] "%x y. x"}, produces @{term
  [show_types] "%x y. x"}.  Type-inference has figured out the most
  general typings in the present (theory) context.  Note that term
  fragments may acquire different typings due to constraints imposed
  by previous text (say within a proof), e.g.\ due to the main goal
  statement given beforehand.

  \medskip Several further kinds of antiquotations (and options) are
  available \cite{isabelle-sys}.  Here are a few commonly used
  combinations:

  \medskip

  \begin{tabular}{ll}
  \texttt{\at}\verb,{typ,~$\tau$\verb,}, & print type $\tau$ \\
  \texttt{\at}\verb,{term,~$t$\verb,}, & print term $t$ \\
  \texttt{\at}\verb,{prop,~$\phi$\verb,}, & print proposition $\phi$ \\
  \texttt{\at}\verb,{prop [display],~$\phi$\verb,}, & print large proposition $\phi$ (with linebreaks) \\
  \texttt{\at}\verb,{prop [source],~$\phi$\verb,}, & check proposition $\phi$, print its input \\
  \texttt{\at}\verb,{thm,~$a$\verb,}, & print fact $a$ \\
  \texttt{\at}\verb,{thm,~$a$~\verb,[no_vars]}, & print fact $a$, fixing schematic variables \\
  \texttt{\at}\verb,{thm [source],~$a$\verb,}, & check validity of fact $a$, print its name \\
  \texttt{\at}\verb,{text,~$s$\verb,}, & print uninterpreted text $s$ \\
  \end{tabular}

  \medskip

  Note that \attrdx{no_vars} given above is \emph{not} an
  antiquotation option, but an attribute of the theorem argument given
  here.  This might be useful with a diagnostic command like
  \isakeyword{thm}, too.

  \medskip The \texttt{\at}\verb,{text, $s$\verb,}, antiquotation is
  particularly interesting.  Embedding uninterpreted text within an
  informal body might appear useless at first sight.  Here the key
  virtue is that the string $s$ is processed as Isabelle output,
  interpreting Isabelle symbols appropriately.

  For example, \texttt{\at}\verb,{text "\<forall>\<exists>"}, produces @{text
  "\<forall>\<exists>"}, according to the standard interpretation of these symbol
  (cf.\ \S\ref{sec:doc-prep-symbols}).  Thus we achieve consistent
  mathematical notation in both the formal and informal parts of the
  document very easily.  Manual {\LaTeX} code would leave more control
  over the typesetting, but is also slightly more tedious.
*}


subsection {* Interpretation of Symbols \label{sec:doc-prep-symbols} *}

text {*
  As has been pointed out before (\S\ref{sec:syntax-symbols}),
  Isabelle symbols are the smallest syntactic entities --- a
  straightforward generalization of ASCII characters.  While Isabelle
  does not impose any interpretation of the infinite collection of
  named symbols, {\LaTeX} documents show canonical glyphs for certain
  standard symbols \cite[appendix~A]{isabelle-sys}.

  The {\LaTeX} code produced from Isabelle text follows a relatively
  simple scheme.  Users may wish to tune the final appearance by
  redefining certain macros, say in \texttt{root.tex} of the document.

  \begin{enumerate}

  \item 7-bit ASCII characters: letters \texttt{A\dots Z} and
  \texttt{a\dots z} are output verbatim, digits are passed as an
  argument to the \verb,\isadigit, macro, other characters are
  replaced by specifically named macros of the form
  \verb,\isacharXYZ,.

  \item Named symbols: \verb,\,\verb,<,$XYZ$\verb,>, become
  \verb,{\isasym,$XYZ$\verb,}, each (note the additional braces).

  \item Named control symbols: \verb,{\isasym,$XYZ$\verb,}, become
  \verb,\isactrl,$XYZ$ each; subsequent symbols may act as arguments
  if the corresponding macro is defined accordingly.

  \end{enumerate}

  Users may occasionally wish to give new {\LaTeX} interpretations of
  named symbols; this merely requires an appropriate definition of
  \verb,\,\verb,<,$XYZ$\verb,>, (see \texttt{isabelle.sty} for working
  examples).  Control symbols are slightly more difficult to get
  right, though.

  \medskip The \verb,\isabellestyle, macro provides a high-level
  interface to tune the general appearance of individual symbols.  For
  example, \verb,\isabellestyle{it}, uses the italics text style to
  mimic the general appearance of the {\LaTeX} math mode; double
  quotes are not printed at all.  The resulting quality of
  typesetting is quite good, so this should usually be the default
  style for real production work that gets distributed to a broader
  audience.
*}


subsection {* Suppressing Output \label{sec:doc-prep-suppress} *}

text {*
  By default, Isabelle's document system generates a {\LaTeX} source
  file for each theory that happens to get loaded while running the
  session.  The generated \texttt{session.tex} will include all of
  these in order of appearance, which in turn gets included by the
  standard \texttt{root.tex}.  Certainly one may change the order or
  suppress unwanted theories by ignoring \texttt{session.tex} and
  include individual files in \texttt{root.tex} by hand.  On the other
  hand, such an arrangement requires additional maintenance chores
  whenever the collection of theories changes.

  Alternatively, one may tune the theory loading process in
  \texttt{ROOT.ML} itself: traversal of the theory dependency graph
  may be fine-tuned by adding \verb,use_thy, invocations, although
  topological sorting still has to be observed.  Moreover, the ML
  operator \verb,no_document, temporarily disables document generation
  while executing a theory loader command; its usage is like this:

\begin{verbatim}
  no_document use_thy "T";
\end{verbatim}

  \medskip Theory output may also be suppressed in smaller portions.
  For example, research articles, or slides usually do not include the
  formal content in full.  In order to delimit \bfindex{ignored
  material} special source comments
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), and
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), may be included in the
  text.  Only the document preparation system is affected, the formal
  checking the theory is performed unchanged.

  In the following example we suppress the slightly formalistic
  \isakeyword{theory} + \isakeyword{end} surroundings a theory.

  \medskip

  \begin{tabular}{l}
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{theory T = Main:} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  ~~$\vdots$ \\
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{end} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  \end{tabular}

  \medskip

  Text may be suppressed in a fine-grained manner.  We may even drop
  vital parts of a formal proof, pretending that things have been
  simpler than in reality.  For example, the following ``fully
  automatic'' proof is actually a fake:
*}

lemma "x \<noteq> (0::int) \<Longrightarrow> 0 < x * x"
  by (auto(*<*)simp add: int_less_le(*>*))

text {*
  \noindent Here the real source of the proof has been as follows:

\begin{verbatim}
  by (auto(*<*)simp add: int_less_le(*>*))
\end{verbatim}
%(*

  \medskip Ignoring portions of printed text does demand some care by
  the writer.  First of all, the writer is responsible not to
  obfuscate the underlying formal development in an unduly manner.  It
  is fairly easy to invalidate the remaining visible text, e.g.\ by
  referencing questionable formal items (strange definitions,
  arbitrary axioms etc.) that have been hidden from sight beforehand.

  Authentic reports of formal theories, say as part of a library,
  usually should refrain from suppressing parts of the text at all.
  Other users may need the full information for their own derivative
  work.  If a particular formalization appears inadequate for general
  public coverage, it is often more appropriate to think of a better
  way in the first place.

  \medskip Some technical subtleties of the
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,),~\verb,(,\verb,*,\verb,>,\verb,*,\verb,),
  elements need to be kept in mind, too --- the system performs little
  sanity checks here.  Arguments of markup commands and formal
  comments must not be hidden, otherwise presentation fails.  Open and
  close parentheses need to be inserted carefully; it is fairly easy
  to hide the wrong parts, especially after rearranging the sources.

*}

(*<*)
end
(*>*)

(*<*)
theory Documents = Main:
(*>*)

section {* Concrete Syntax \label{sec:concrete-syntax} *}

text {*
  The core concept of Isabelle's framework for concrete syntax is that
  of \bfindex{mixfix annotations}.  Associated with any kind of
  constant declaration, mixfixes affect both the grammar productions
  for the parser and output templates for the pretty printer.

  In full generality, parser and pretty printer configuration is a
  subtle affair \cite{isabelle-ref}.  Your syntax specifications need
  to interact properly with the existing setup of Isabelle/Pure and
  Isabelle/HOL\@.  To avoid creating ambiguities with existing
  elements, it is particularly important to give new syntactic
  constructs the right precedence.

  \medskip Subsequently we introduce a few simple syntax declaration
  forms that already cover many common situations fairly well.
*}


subsection {* Infix Annotations *}

text {*
  Syntax annotations may be included wherever constants are declared,
  such as \isacommand{consts} and \isacommand{constdefs} --- and also
  \isacommand{datatype}, which declares constructor operations.
  Type-constructors may be annotated as well, although this is less
  frequently encountered in practice (the infix type @{text "\<times>"} comes
  to mind).

  Infix declarations\index{infix annotations} provide a useful special
  case of mixfixes.  The following example of the exclusive-or
  operation on boolean values illustrates typical infix declarations.
*}

constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
  "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

text {*
  \noindent Now @{text "xor A B"} and @{text "A [+] B"} refer to the
  same expression internally.  Any curried function with at least two
  arguments may be given infix syntax.  For partial applications with
  fewer than two operands, there is a notation using the prefix~@{text
  op}.  For instance, @{text xor} without arguments is represented as
  @{text "op [+]"}; together with ordinary function application, this
  turns @{text "xor A"} into @{text "op [+] A"}.

  \medskip The keyword \isakeyword{infixl} seen above specifies an
  infix operator that is nested to the \emph{left}: in iterated
  applications the more complex expression appears on the left-hand
  side, and @{term "A [+] B [+] C"} stands for @{text "(A [+] B) [+]
  C"}.  Similarly, \isakeyword{infixr} means nesting to the
  \emph{right}, reading @{term "A [+] B [+] C"} as @{text "A [+] (B
  [+] C)"}.  A \emph{non-oriented} declaration via \isakeyword{infix}
  would render @{term "A [+] B [+] C"} illegal, but demand explicit
  parentheses to indicate the intended grouping.

  The string @{text [source] "[+]"} in our annotation refers to the
  concrete syntax to represent the operator (a literal token), while
  the number @{text 60} determines the precedence of the construct:
  the syntactic priorities of the arguments and result.  Isabelle/HOL
  already uses up many popular combinations of ASCII symbols for its
  own use, including both @{text "+"} and @{text "++"}.  Longer
  character combinations are more likely to be still available for
  user extensions, such as our~@{text "[+]"}.

  Operator precedences have a range of 0--1000.  Very low or high
  priorities are reserved for the meta-logic.  HOL syntax mainly uses
  the range of 10--100: the equality infix @{text "="} is centered at
  50; logical connectives (like @{text "\<or>"} and @{text "\<and>"}) are
  below 50; algebraic ones (like @{text "+"} and @{text "*"}) are
  above 50.  User syntax should strive to coexist with common HOL
  forms, or use the mostly unused range 100--900.
*}


subsection {* Mathematical Symbols \label{sec:syntax-symbols} *}

text {*
  Concrete syntax based on ASCII characters has inherent limitations.
  Mathematical notation demands a larger repertoire of glyphs.
  Several standards of extended character sets have been proposed over
  decades, but none has become universally available so far.  Isabelle
  has its own notion of \bfindex{symbols} as the smallest entities of
  source text, without referring to internal encodings.  There are
  three kinds of such ``generalized characters'':

  \begin{enumerate}

  \item 7-bit ASCII characters

  \item named symbols: \verb,\,\verb,<,$ident$\verb,>,

  \item named control symbols: \verb,\,\verb,<^,$ident$\verb,>,

  \end{enumerate}

  Here $ident$ is any sequence of letters. 
  This results in an infinite store of symbols, whose
  interpretation is left to further front-end tools.  For example, the
  user-interface of Proof~General + X-Symbol and the Isabelle document
  processor (see \S\ref{sec:document-preparation}) display the
  \verb,\,\verb,<forall>, symbol as~@{text \<forall>}.

  A list of standard Isabelle symbols is given in
  \cite[appendix~A]{isabelle-sys}.  You may introduce your own
  interpretation of further symbols by configuring the appropriate
  front-end tool accordingly, e.g.\ by defining certain {\LaTeX}
  macros (see also \S\ref{sec:doc-prep-symbols}).  There are also a
  few predefined control symbols, such as \verb,\,\verb,<^sub>, and
  \verb,\,\verb,<^sup>, for sub- and superscript of the subsequent
  printable symbol, respectively.  For example, \verb,A\<^sup>\<star>, is
  output as @{text "A\<^sup>\<star>"}.

  A number of symbols are considered letters by the Isabelle lexer 
  and can be used as part of identifiers. These are the greek letters
  @{text "\<alpha>"} (\verb+\+\verb+<alpha>+), @{text "\<beta>"}, etc apart from
  @{text "\<lambda>"}, caligraphic letters like @{text "\<A>"}
  (\verb+\+\verb+<A>+) and @{text "\<AA>"} (\verb+\+\verb+<AA>+), 
  and the special control symbols \verb+\+\verb+<^isub>+ and 
  \verb+\+\verb+<^isup>+ for single letter sub and super scripts. This
  means that the input 

  \medskip
  {\small\noindent \verb,\,\verb,<forall>\,\verb,<alpha>\<^isub>1.\,\verb,<alpha>\<^isub>1=\,\verb,<Pi>\<^isup>\<A>,}

  \medskip
  \noindent is recognized as the term @{term "\<forall>\<alpha>\<^isub>1. \<alpha>\<^isub>1 = \<Pi>\<^isup>\<A>"} 
  by Isabelle. Note that @{text "\<Pi>\<^isup>\<A>"} is a single entity like 
  @{text "PA"}, not an exponentiation.


  \medskip Replacing our definition of @{text xor} by the following
  specifies an Isabelle symbol for the new operator:
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
  just type a named entity \verb,\,\verb,<oplus>, by hand; the
  corresponding symbol will be displayed after further input.

  \medskip More flexible is to provide alternative syntax forms
  through the \bfindex{print mode} concept~\cite{isabelle-ref}.  By
  convention, the mode of ``$xsymbols$'' is enabled whenever
  Proof~General's X-Symbol mode or {\LaTeX} output is active.  Now
  consider the following hybrid declaration of @{text xor}:
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
  \isakeyword{consts}, but without declaring a logical constant.  The
  print mode specification of \isakeyword{syntax}, here @{text
  "(xsymbols)"}, is optional.  Also note that its type merely serves
  for syntactic purposes, and is \emph{not} checked for consistency
  with the real constant.

  \medskip We may now write @{text "A [+] B"} or @{text "A \<oplus> B"} in
  input, while output uses the nicer syntax of $xsymbols$ whenever
  that print mode is active.  Such an arrangement is particularly
  useful for interactive development, where users may type ASCII text
  and see mathematical symbols displayed during proofs.
*}


subsection {* Prefix Annotations *}

text {*
  Prefix syntax annotations\index{prefix annotation} are another form
  of mixfixes \cite{isabelle-ref}, without any template arguments or
  priorities --- just some literal syntax.  The following example
  associates common symbols with the constructors of a datatype.
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
  "nat \<Rightarrow> currency"}.  The expression @{text "Euro 10"} will be
  printed as @{term "\<euro> 10"}; only the head of the application is
  subject to our concrete syntax.  This rather simple form already
  achieves conformance with notational standards of the European
  Commission.

  Prefix syntax works the same way for \isakeyword{consts} or
  \isakeyword{constdefs}.
*}


subsection {* Syntax Translations \label{sec:syntax-translations} *}

text{*
  Mixfix syntax annotations merely decorate particular constant
  application forms with concrete syntax, for instance replacing \
  @{text "xor A B"} by @{text "A \<oplus> B"}.  Occasionally, the
  relationship between some piece of notation and its internal form is
  more complicated.  Here we need \bfindex{syntax translations}.

  Using the \isakeyword{syntax}\index{syntax (command)}, command we
  introduce uninterpreted notational elements.  Then
  \commdx{translations} relate input forms to complex logical
  expressions.  This provides a simple mechanism for syntactic macros;
  even heavier transformations may be written in ML
  \cite{isabelle-ref}.

  \medskip A typical use of syntax translations is to introduce
  relational notation for membership in a set of pair, replacing \
  @{text "(x, y) \<in> sim"} by @{text "x \<approx> y"}.
*}

consts
  sim :: "('a \<times> 'a) set"

syntax
  "_sim" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infix "\<approx>" 50)
translations
  "x \<approx> y" \<rightleftharpoons> "(x, y) \<in> sim"

text {*
  \noindent Here the name of the dummy constant @{text "_sim"} does
  not matter, as long as it is not used elsewhere.  Prefixing an
  underscore is a common convention.  The \isakeyword{translations}
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

  This sort of translation is appropriate when the defined concept is
  a trivial variation on an existing one.  On the other hand, syntax
  translations do not scale up well to large hierarchies of concepts.
  Translations do not replace definitions!
*}


section {* Document Preparation \label{sec:document-preparation} *}

text {*
  Isabelle/Isar is centered around the concept of \bfindex{formal
  proof documents}\index{documents|bold}.  The outcome of a formal
  development effort is meant to be a human-readable record, presented
  as browsable PDF file or printed on paper.  The overall document
  structure follows traditional mathematical articles, with sections,
  intermediate explanations, definitions, theorems and proofs.

  \medskip The Isabelle document preparation system essentially acts
  as a front-end to {\LaTeX}.  After checking specifications and
  proofs formally, the theory sources are turned into typesetting
  instructions in a schematic manner.  This lets you write authentic
  reports on theory developments with little effort: many technical
  consistency checks are handled by the system.

  Here is an example to illustrate the idea of Isabelle document
  preparation.
*}

text_raw {* \begin{quotation} *}

text {*
  The following datatype definition of @{text "'a bintree"} models
  binary trees with nodes being decorated by elements of type @{typ
  'a}.
*}

datatype 'a bintree =
     Leaf | Branch 'a  "'a bintree"  "'a bintree"

text {*
  \noindent The datatype induction rule generated here is of the form
  @{thm [indent = 1, display] bintree.induct [no_vars]}
*}

text_raw {* \end{quotation} *}

text {*
  \noindent The above document output has been produced as follows:

  \begin{ttbox}
  text {\ttlbrace}*
    The following datatype definition of {\at}{\ttlbrace}text "'a bintree"{\ttrbrace}
    models binary trees with nodes being decorated by elements
    of type {\at}{\ttlbrace}typ 'a{\ttrbrace}.
  *{\ttrbrace}

  datatype 'a bintree =
    Leaf | Branch 'a  "'a bintree"  "'a bintree"
  \end{ttbox}
  \begin{ttbox}
  text {\ttlbrace}*
    {\ttback}noindent The datatype induction rule generated here is
    of the form {\at}{\ttlbrace}thm [display] bintree.induct [no_vars]{\ttrbrace}
  *{\ttrbrace}
  \end{ttbox}\vspace{-\medskipamount}

  \noindent Here we have augmented the theory by formal comments
  (using \isakeyword{text} blocks), the informal parts may again refer
  to formal entities by means of ``antiquotations'' (such as
  \texttt{\at}\verb,{text "'a bintree"}, or
  \texttt{\at}\verb,{typ 'a},), see also \S\ref{sec:doc-prep-text}.
*}


subsection {* Isabelle Sessions *}

text {*
  In contrast to the highly interactive mode of Isabelle/Isar theory
  development, the document preparation stage essentially works in
  batch-mode.  An Isabelle \bfindex{session} consists of a collection
  of source files that may contribute to an output document.  Each
  session is derived from a single parent, usually an object-logic
  image like \texttt{HOL}.  This results in an overall tree structure,
  which is reflected by the output location in the file system
  (usually rooted at \verb,~/isabelle/browser_info,).

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
  of contents etc.).  Any failure at this stage usually indicates
  technical problems of the {\LaTeX} installation.\footnote{Especially
  make sure that \texttt{pdflatex} is present; if in doubt one may
  fall back on DVI output by changing \texttt{usedir} options in
  \texttt{IsaMakefile} \cite{isabelle-sys}.}

  \medskip The detailed arrangement of the session sources is as
  follows.

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
  files $T@i$\texttt{.tex} for each theory.  Isabelle will generate a
  file \texttt{session.tex} holding {\LaTeX} commands to include all
  generated theory output files in topologically sorted order, so
  \verb,\input{session}, in the body of \texttt{root.tex} does the job
  in most situations.

  \item \texttt{IsaMakefile} holds appropriate dependencies and
  invocations of Isabelle tools to control the batch job.  In fact,
  several sessions may be managed by the same \texttt{IsaMakefile}.
  See the \emph{Isabelle System Manual} \cite{isabelle-sys} 
  for further details, especially on
  \texttt{isatool usedir} and \texttt{isatool make}.

  \end{itemize}

  One may now start to populate the directory \texttt{MySession}, and
  the file \texttt{MySession/ROOT.ML} accordingly.  The file
  \texttt{MySession/document/root.tex} should also be adapted at some
  point; the default version is mostly self-explanatory.  Note that
  \verb,\isabellestyle, enables fine-tuning of the general appearance
  of characters and mathematical symbols (see also
  \S\ref{sec:doc-prep-symbols}).

  Especially observe the included {\LaTeX} packages \texttt{isabelle}
  (mandatory), \texttt{isabellesym} (required for mathematical
  symbols), and the final \texttt{pdfsetup} (provides sane defaults
  for \texttt{hyperref}, including URL markup).  All three are
  distributed with Isabelle. Further packages may be required in
  particular applications, say for unusual mathematical symbols.

  \medskip Any additional files for the {\LaTeX} stage go into the
  \texttt{MySession/document} directory as well.  In particular,
  adding a file named \texttt{root.bib} causes an automatic run of
  \texttt{bibtex} to process a bibliographic database; see also
  \texttt{isatool document} \cite{isabelle-sys}.

  \medskip Any failure of the document preparation phase in an
  Isabelle batch session leaves the generated sources in their target
  location, identified by the accompanying error message.  This lets
  you trace {\LaTeX} problems with the generated files at hand.
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
  $text$ argument (delimited by \verb,",~@{text \<dots>}~\verb,", or
  \verb,{,\verb,*,~@{text \<dots>}~\verb,*,\verb,},).  After stripping any
  surrounding white space, the argument is passed to a {\LaTeX} macro
  \verb,\isamarkupXYZ, for command \isakeyword{XYZ}.  These macros are
  defined in \verb,isabelle.sty, according to the meaning given in the
  rightmost column above.

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
  \end{ttbox}\vspace{-\medskipamount}

  You may occasionally want to change the meaning of markup commands,
  say via \verb,\renewcommand, in \texttt{root.tex}.  For example,
  \verb,\isamarkupheader, is a good candidate for some tuning.  We
  could move it up in the hierarchy to become \verb,\chapter,.

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]{\chapter{#1}}
\end{verbatim}

  \noindent Now we must change the document class given in
  \texttt{root.tex} to something that supports chapters.  A suitable
  command is \verb,\documentclass{report},.

  \medskip The {\LaTeX} macro \verb,\isabellecontext, is maintained to
  hold the name of the current theory context.  This is particularly
  useful for document headings:

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]
  {\chapter{#1}\markright{THEORY~\isabellecontext}}
\end{verbatim}

  \noindent Make sure to include something like
  \verb,\pagestyle{headings}, in \texttt{root.tex}; the document
  should have more than two pages to show the effect.
*}


subsection {* Formal Comments and Antiquotations \label{sec:doc-prep-text} *}

text {*
  Isabelle \bfindex{source comments}, which are of the form
  \verb,(,\verb,*,~@{text \<dots>}~\verb,*,\verb,),, essentially act like
  white space and do not really contribute to the content.  They
  mainly serve technical purposes to mark certain oddities in the raw
  input text.  In contrast, \bfindex{formal comments} are portions of
  text that are associated with formal Isabelle/Isar commands
  (\bfindex{marginal comments}), or as standalone paragraphs within a
  theory or proof context (\bfindex{text blocks}).

  \medskip Marginal comments are part of each command's concrete
  syntax \cite{isabelle-ref}; the common form is ``\verb,--,~$text$''
  where $text$ is delimited by \verb,",@{text \<dots>}\verb,", or
  \verb,{,\verb,*,~@{text \<dots>}~\verb,*,\verb,}, as before.  Multiple
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
  proofs.  This may be changed as follows:

\begin{verbatim}
  \renewcommand{\isastyletxt}{\isastyletext}
\end{verbatim}

  \medskip The $text$ part of Isabelle markup commands essentially
  inserts \emph{quoted material} into a formal text, mainly for
  instruction of the reader.  An \bfindex{antiquotation} is again a
  formal object embedded into such an informal portion.  The
  interpretation of antiquotations is limited to some well-formedness
  checks, with the result being pretty printed to the resulting
  document.  Quoted text blocks together with antiquotations provide
  an attractive means of referring to formal entities, with good
  confidence in getting the technical details right (especially syntax
  and types).

  The general syntax of antiquotations is as follows:
  \texttt{{\at}{\ttlbrace}$name$ $arguments${\ttrbrace}}, or
  \texttt{{\at}{\ttlbrace}$name$ [$options$] $arguments${\ttrbrace}}
  for a comma-separated list of options consisting of a $name$ or
  \texttt{$name$=$value$} each.  The syntax of $arguments$ depends on
  the kind of antiquotation, it generally follows the same conventions
  for types, terms, or theorems as in the formal part of a theory.

  \medskip This sentence demonstrates quotations and antiquotations:
  @{term "%x y. x"} is a well-typed term.

  \medskip\noindent The output above was produced as follows:
  \begin{ttbox}
text {\ttlbrace}*
  This sentence demonstrates quotations and antiquotations:
  {\at}{\ttlbrace}term "%x y. x"{\ttrbrace} is a well-typed term.
*{\ttrbrace}
  \end{ttbox}\vspace{-\medskipamount}

  The notational change from the ASCII character~\verb,%, to the
  symbol~@{text \<lambda>} reveals that Isabelle printed this term, after
  parsing and type-checking.  Document preparation enables symbolic
  output by default.

  \medskip The next example includes an option to modify Isabelle's
  \verb,show_types, flag.  The antiquotation
  \texttt{{\at}}\verb,{term [show_types] "%x y. x"}, produces the
  output @{term [show_types] "%x y. x"}.  Type inference has figured
  out the most general typings in the present theory context.  Terms
  may acquire different typings due to constraints imposed by their
  environment; within a proof, for example, variables are given the
  same types as they have in the main goal statement.

  \medskip Several further kinds of antiquotations and options are
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
  \texttt{\at}\verb,{thm [source],~$a$\verb,}, & check availability of fact $a$, print its name \\
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
  document very easily, independently of the term language of
  Isabelle.  Manual {\LaTeX} code would leave more control over the
  typesetting, but is also slightly more tedious.
*}


subsection {* Interpretation of Symbols \label{sec:doc-prep-symbols} *}

text {*
  As has been pointed out before (\S\ref{sec:syntax-symbols}),
  Isabelle symbols are the smallest syntactic entities --- a
  straightforward generalization of ASCII characters.  While Isabelle
  does not impose any interpretation of the infinite collection of
  named symbols, {\LaTeX} documents use canonical glyphs for certain
  standard symbols \cite[appendix~A]{isabelle-sys}.

  The {\LaTeX} code produced from Isabelle text follows a simple
  scheme.  You can tune the final appearance by redefining certain
  macros, say in \texttt{root.tex} of the document.

  \begin{enumerate}

  \item 7-bit ASCII characters: letters \texttt{A\dots Z} and
  \texttt{a\dots z} are output directly, digits are passed as an
  argument to the \verb,\isadigit, macro, other characters are
  replaced by specifically named macros of the form
  \verb,\isacharXYZ,.

  \item Named symbols: \verb,\,\verb,<XYZ>, is turned into
  \verb,{\isasymXYZ},; note the additional braces.

  \item Named control symbols: \verb,\,\verb,<^XYZ>, is turned into
  \verb,\isactrlXYZ,; subsequent symbols may act as arguments if the
  control macro is defined accordingly.

  \end{enumerate}

  You may occasionally wish to give new {\LaTeX} interpretations of
  named symbols.  This merely requires an appropriate definition of
  \verb,\isasymXYZ,, for \verb,\,\verb,<XYZ>, (see
  \texttt{isabelle.sty} for working examples).  Control symbols are
  slightly more difficult to get right, though.

  \medskip The \verb,\isabellestyle, macro provides a high-level
  interface to tune the general appearance of individual symbols.  For
  example, \verb,\isabellestyle{it}, uses the italics text style to
  mimic the general appearance of the {\LaTeX} math mode; double
  quotes are not printed at all.  The resulting quality of typesetting
  is quite good, so this should be the default style for work that
  gets distributed to a broader audience.
*}


subsection {* Suppressing Output \label{sec:doc-prep-suppress} *}

text {*
  By default, Isabelle's document system generates a {\LaTeX} file for
  each theory that gets loaded while running the session.  The
  generated \texttt{session.tex} will include all of these in order of
  appearance, which in turn gets included by the standard
  \texttt{root.tex}.  Certainly one may change the order or suppress
  unwanted theories by ignoring \texttt{session.tex} and load
  individual files directly in \texttt{root.tex}.  On the other hand,
  such an arrangement requires additional maintenance whenever the
  collection of theories changes.

  Alternatively, one may tune the theory loading process in
  \texttt{ROOT.ML} itself: traversal of the theory dependency graph
  may be fine-tuned by adding \verb,use_thy, invocations, although
  topological sorting still has to be observed.  Moreover, the ML
  operator \verb,no_document, temporarily disables document generation
  while executing a theory loader command.  Its usage is like this:

\begin{verbatim}
  no_document use_thy "T";
\end{verbatim}

  \medskip Theory output may be suppressed more selectively.  Research
  articles and slides usually do not include the formal content in
  full.  Delimiting \bfindex{ignored material} by the special source
  comments \verb,(,\verb,*,\verb,<,\verb,*,\verb,), and
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), tells the document
  preparation system to suppress these parts; the formal checking of
  the theory is unchanged, of course.

  In this example, we hide a theory's \isakeyword{theory} and
  \isakeyword{end} brackets:

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

  Text may be suppressed in a fine-grained manner.  We may even hide
  vital parts of a proof, pretending that things have been simpler
  than they really were.  For example, this ``fully automatic'' proof
  is actually a fake:
*}

lemma "x \<noteq> (0::int) \<Longrightarrow> 0 < x * x"
  by (auto(*<*)simp add: zero_less_mult_iff(*>*))

text {*
  \noindent Here the real source of the proof has been as follows:

\begin{verbatim}
  by (auto(*<*)simp add: zero_less_mult_iff(*>*))
\end{verbatim}
%(*

  \medskip Suppressing portions of printed text demands care.  You
  should not misrepresent the underlying theory development.  It is
  easy to invalidate the visible text by hiding references to
  questionable axioms.

  Authentic reports of Isabelle/Isar theories, say as part of a
  library, should suppress nothing.  Other users may need the full
  information for their own derivative work.  If a particular
  formalization appears inadequate for general public coverage, it is
  often more appropriate to think of a better way in the first place.

  \medskip Some technical subtleties of the
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,),~\verb,(,\verb,*,\verb,>,\verb,*,\verb,),
  elements need to be kept in mind, too --- the system performs few
  sanity checks here.  Arguments of markup commands and formal
  comments must not be hidden, otherwise presentation fails.  Open and
  close parentheses need to be inserted carefully; it is easy to hide
  the wrong parts, especially after rearranging the theory text.
*}

(*<*)
end
(*>*)

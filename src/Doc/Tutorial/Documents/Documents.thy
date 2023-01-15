(*<*)
theory Documents imports Main begin
(*>*)

section \<open>Concrete Syntax \label{sec:concrete-syntax}\<close>

text \<open>
  The core concept of Isabelle's framework for concrete syntax is that
  of \bfindex{mixfix annotations}.  Associated with any kind of
  constant declaration, mixfixes affect both the grammar productions
  for the parser and output templates for the pretty printer.

  In full generality, parser and pretty printer configuration is a
  subtle affair~\<^cite>\<open>"isabelle-isar-ref"\<close>.  Your syntax specifications need
  to interact properly with the existing setup of Isabelle/Pure and
  Isabelle/HOL\@.  To avoid creating ambiguities with existing
  elements, it is particularly important to give new syntactic
  constructs the right precedence.

  Below we introduce a few simple syntax declaration
  forms that already cover many common situations fairly well.
\<close>


subsection \<open>Infix Annotations\<close>

text \<open>
  Syntax annotations may be included wherever constants are declared,
  such as \isacommand{definition} and \isacommand{primrec} --- and also
  \isacommand{datatype}, which declares constructor operations.
  Type-constructors may be annotated as well, although this is less
  frequently encountered in practice (the infix type \<open>\<times>\<close> comes
  to mind).

  Infix declarations\index{infix annotations} provide a useful special
  case of mixfixes.  The following example of the exclusive-or
  operation on boolean values illustrates typical infix declarations.
\<close>

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
where "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

text \<open>
  \noindent Now \<open>xor A B\<close> and \<open>A [+] B\<close> refer to the
  same expression internally.  Any curried function with at least two
  arguments may be given infix syntax.  For partial applications with
  fewer than two operands, the operator is enclosed in parentheses.
  For instance, \<open>xor\<close> without arguments is represented as
  \<open>([+])\<close>; together with ordinary function application, this
  turns \<open>xor A\<close> into \<open>([+]) A\<close>.

  The keyword \isakeyword{infixl} seen above specifies an
  infix operator that is nested to the \emph{left}: in iterated
  applications the more complex expression appears on the left-hand
  side, and \<^term>\<open>A [+] B [+] C\<close> stands for \<open>(A [+] B) [+]
  C\<close>.  Similarly, \isakeyword{infixr} means nesting to the
  \emph{right}, reading \<^term>\<open>A [+] B [+] C\<close> as \<open>A [+] (B
  [+] C)\<close>.  A \emph{non-oriented} declaration via \isakeyword{infix}
  would render \<^term>\<open>A [+] B [+] C\<close> illegal, but demand explicit
  parentheses to indicate the intended grouping.

  The string @{text [source] "[+]"} in our annotation refers to the
  concrete syntax to represent the operator (a literal token), while
  the number \<open>60\<close> determines the precedence of the construct:
  the syntactic priorities of the arguments and result.  Isabelle/HOL
  already uses up many popular combinations of ASCII symbols for its
  own use, including both \<open>+\<close> and \<open>++\<close>.  Longer
  character combinations are more likely to be still available for
  user extensions, such as our~\<open>[+]\<close>.

  Operator precedences have a range of 0--1000.  Very low or high
  priorities are reserved for the meta-logic.  HOL syntax mainly uses
  the range of 10--100: the equality infix \<open>=\<close> is centered at
  50; logical connectives (like \<open>\<or>\<close> and \<open>\<and>\<close>) are
  below 50; algebraic ones (like \<open>+\<close> and \<open>*\<close>) are
  above 50.  User syntax should strive to coexist with common HOL
  forms, or use the mostly unused range 100--900.
\<close>


subsection \<open>Mathematical Symbols \label{sec:syntax-symbols}\<close>

text \<open>
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
  Isabelle document processor (see \S\ref{sec:document-preparation})
  display the \verb,\,\verb,<forall>, symbol as~\<open>\<forall>\<close>.

  A list of standard Isabelle symbols is given in
  \<^cite>\<open>"isabelle-isar-ref"\<close>.  You may introduce your own
  interpretation of further symbols by configuring the appropriate
  front-end tool accordingly, e.g.\ by defining certain {\LaTeX}
  macros (see also \S\ref{sec:doc-prep-symbols}).  There are also a
  few predefined control symbols, such as \verb,\,\verb,<^sub>, and
  \verb,\,\verb,<^sup>, for sub- and superscript of the subsequent
  printable symbol, respectively.  For example, \<^verbatim>\<open>A\<^sup>\<star>\<close>, is
  output as \<open>A\<^sup>\<star>\<close>.

  A number of symbols are considered letters by the Isabelle lexer and
  can be used as part of identifiers. These are the greek letters
  \<open>\<alpha>\<close> (\verb+\+\verb+<alpha>+), \<open>\<beta>\<close>
  (\verb+\+\verb+<beta>+), etc. (excluding \<open>\<lambda>\<close>),
  special letters like \<open>\<A>\<close> (\verb+\+\verb+<A>+) and \<open>\<AA>\<close> (\verb+\+\verb+<AA>+).  Moreover the control symbol
  \verb+\+\verb+<^sub>+ may be used to subscript a single letter or digit
  in the trailing part of an identifier. This means that the input

  \medskip
  {\small\noindent \<^verbatim>\<open>\<forall>\<alpha>\<^sub>1. \<alpha>\<^sub>1 = \<Pi>\<^sub>\<A>\<close>}

  \medskip
  \noindent is recognized as the term \<^term>\<open>\<forall>\<alpha>\<^sub>1. \<alpha>\<^sub>1 = \<Pi>\<^sub>\<A>\<close> 
  by Isabelle.

  Replacing our previous definition of \<open>xor\<close> by the
  following specifies an Isabelle symbol for the new operator:
\<close>

(*<*)
hide_const xor
setup \<open>Sign.add_path "version1"\<close>
(*>*)
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>" 60)
where "A \<oplus> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"
(*<*)
setup \<open>Sign.local_path\<close>
(*>*)

text \<open>
  It is possible to provide alternative syntax forms
  through the \bfindex{print mode} concept~\<^cite>\<open>"isabelle-isar-ref"\<close>.  By
  convention, the mode of ``$xsymbols$'' is enabled whenever
  Proof~General's X-Symbol mode or {\LaTeX} output is active.  Now
  consider the following hybrid declaration of \<open>xor\<close>:
\<close>

(*<*)
hide_const xor
setup \<open>Sign.add_path "version2"\<close>
(*>*)
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]\<ignore>" 60)
where "A [+]\<ignore> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

notation (xsymbols) xor (infixl "\<oplus>\<ignore>" 60)
(*<*)
setup \<open>Sign.local_path\<close>
(*>*)

text \<open>\noindent
The \commdx{notation} command associates a mixfix
annotation with a known constant.  The print mode specification,
here \<open>(xsymbols)\<close>, is optional.

We may now write \<open>A [+] B\<close> or \<open>A \<oplus> B\<close> in input, while
output uses the nicer syntax of $xsymbols$ whenever that print mode is
active.  Such an arrangement is particularly useful for interactive
development, where users may type ASCII text and see mathematical
symbols displayed during proofs.\<close>


subsection \<open>Prefix Annotations\<close>

text \<open>
  Prefix syntax annotations\index{prefix annotation} are another form
  of mixfixes \<^cite>\<open>"isabelle-isar-ref"\<close>, without any template arguments or
  priorities --- just some literal syntax.  The following example
  associates common symbols with the constructors of a datatype.
\<close>

datatype currency =
    Euro nat    ("\<euro>")
  | Pounds nat  ("\<pounds>")
  | Yen nat     ("\<yen>")
  | Dollar nat  ("$")

text \<open>
  \noindent Here the mixfix annotations on the rightmost column happen
  to consist of a single Isabelle symbol each: \verb,\,\verb,<euro>,,
  \verb,\,\verb,<pounds>,, \verb,\,\verb,<yen>,, and \verb,$,.  Recall
  that a constructor like \<open>Euro\<close> actually is a function \<^typ>\<open>nat \<Rightarrow> currency\<close>.  The expression \<open>Euro 10\<close> will be
  printed as \<^term>\<open>\<euro> 10\<close>; only the head of the application is
  subject to our concrete syntax.  This rather simple form already
  achieves conformance with notational standards of the European
  Commission.

  Prefix syntax works the same way for other commands that introduce new constants, e.g. \isakeyword{primrec}.
\<close>


subsection \<open>Abbreviations \label{sec:abbreviations}\<close>

text\<open>Mixfix syntax annotations merely decorate particular constant
application forms with concrete syntax, for instance replacing
\<open>xor A B\<close> by \<open>A \<oplus> B\<close>.  Occasionally, the relationship
between some piece of notation and its internal form is more
complicated.  Here we need \emph{abbreviations}.

Command \commdx{abbreviation} introduces an uninterpreted notational
constant as an abbreviation for a complex term. Abbreviations are
unfolded upon parsing and re-introduced upon printing. This provides a
simple mechanism for syntactic macros.

A typical use of abbreviations is to introduce relational notation for
membership in a set of pairs, replacing \<open>(x, y) \<in> sim\<close> by
\<open>x \<approx> y\<close>. We assume that a constant \<open>sim\<close> of type
\<^typ>\<open>('a \<times> 'a) set\<close> has been introduced at this point.\<close>
(*<*)consts sim :: "('a \<times> 'a) set"(*>*)
abbreviation sim2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"   (infix "\<approx>" 50)
where "x \<approx> y  \<equiv>  (x, y) \<in> sim"

text \<open>\noindent The given meta-equality is used as a rewrite rule
after parsing (replacing \mbox{\<^prop>\<open>x \<approx> y\<close>} by \<open>(x,y) \<in>
sim\<close>) and before printing (turning \<open>(x,y) \<in> sim\<close> back into
\mbox{\<^prop>\<open>x \<approx> y\<close>}). The name of the dummy constant \<open>sim2\<close>
does not matter, as long as it is unique.

Another common application of abbreviations is to
provide variant versions of fundamental relational expressions, such
as \<open>\<noteq>\<close> for negated equalities.  The following declaration
stems from Isabelle/HOL itself:
\<close>

abbreviation not_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infixl "~=\<ignore>" 50)
where "x ~=\<ignore> y  \<equiv>  \<not> (x = y)"

notation (xsymbols) not_equal (infix "\<noteq>\<ignore>" 50)

text \<open>\noindent The notation \<open>\<noteq>\<close> is introduced separately to restrict it
to the \emph{xsymbols} mode.

Abbreviations are appropriate when the defined concept is a
simple variation on an existing one.  But because of the automatic
folding and unfolding of abbreviations, they do not scale up well to
large hierarchies of concepts. Abbreviations do not replace
definitions.

Abbreviations are a simplified form of the general concept of
\emph{syntax translations}; even heavier transformations may be
written in ML \<^cite>\<open>"isabelle-isar-ref"\<close>.
\<close>


section \<open>Document Preparation \label{sec:document-preparation}\<close>

text \<open>
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
\<close>

text_raw \<open>\begin{quotation}\<close>

text \<open>
  The following datatype definition of \<open>'a bintree\<close> models
  binary trees with nodes being decorated by elements of type \<^typ>\<open>'a\<close>.
\<close>

datatype 'a bintree =
     Leaf | Branch 'a  "'a bintree"  "'a bintree"

text \<open>
  \noindent The datatype induction rule generated here is of the form
  @{thm [indent = 1, display] bintree.induct [no_vars]}
\<close>

text_raw \<open>\end{quotation}\<close>

text \<open>
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
\<close>


subsection \<open>Isabelle Sessions\<close>

text \<open>
  In contrast to the highly interactive mode of Isabelle/Isar theory
  development, the document preparation stage essentially works in
  batch-mode.  An Isabelle \bfindex{session} consists of a collection
  of source files that may contribute to an output document.  Each
  session is derived from a single parent, usually an object-logic
  image like \texttt{HOL}.  This results in an overall tree structure,
  which is reflected by the output location in the file system
  (the root directory is determined by the Isabelle settings variable
  \verb,ISABELLE_BROWSER_INFO,).

  \medskip The easiest way to manage Isabelle sessions is via
  \texttt{isabelle mkroot} (to generate an initial session source
  setup) and \texttt{isabelle build} (to run sessions as specified in
  the corresponding \texttt{ROOT} file).  These Isabelle tools are
  described in further detail in the \emph{Isabelle System Manual}
  \<^cite>\<open>"isabelle-system"\<close>.

  For example, a new session \texttt{MySession} (with document
  preparation) may be produced as follows:

\begin{verbatim}
  isabelle mkroot MySession
  isabelle build -D MySession
\end{verbatim}

  The \texttt{isabelle build} job also informs about the file-system
  location of the ultimate results.  The above dry run should be able
  to produce some \texttt{document.pdf} (with dummy title, empty table
  of contents etc.).  Any failure at this stage usually indicates
  technical problems of the {\LaTeX} installation.

  \medskip The detailed arrangement of the session sources is as
  follows.

  \begin{itemize}

  \item Directory \texttt{MySession} holds the required theory files
  $T@1$\texttt{.thy}, \dots, $T@n$\texttt{.thy}.

  \item File \texttt{MySession/ROOT} specifies the session options and
  content, with declarations for all wanted theories; it is sufficient
  to specify the terminal nodes of the theory dependency graph.

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

  \end{itemize}

  One may now start to populate the directory \texttt{MySession} and
  its \texttt{ROOT} file accordingly.  The file
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
  \texttt{isabelle document} \<^cite>\<open>"isabelle-system"\<close>.

  \medskip Any failure of the document preparation phase in an
  Isabelle batch session leaves the generated sources in their target
  location, identified by the accompanying error message.  This lets
  you trace {\LaTeX} problems with the generated files at hand.
\<close>


subsection \<open>Structure Markup\<close>

text \<open>
  The large-scale structure of Isabelle documents follows existing
  {\LaTeX} conventions, with chapters, sections, subsubsections etc.
  The Isar language includes separate \bfindex{markup commands}, which
  do not affect the formal meaning of a theory (or proof), but result
  in corresponding {\LaTeX} elements.

  From the Isabelle perspective, each markup command takes a single
  $text$ argument (delimited by \verb,",~\<open>\<dots>\<close>~\verb,", or
  \verb,{,\verb,*,~\<open>\<dots>\<close>~\verb,*,\verb,},).  After stripping any
  surrounding white space, the argument is passed to a {\LaTeX} macro
  \verb,\isamarkupXYZ, for command \isakeyword{XYZ}.  These macros are
  defined in \verb,isabelle.sty, according to the meaning given in the
  rightmost column above.

  \medskip The following source fragment illustrates structure markup
  of a theory.  Note that {\LaTeX} labels may be included inside of
  section headings as well.

  \begin{ttbox}
  section {\ttlbrace}* Some properties of Foo Bar elements *{\ttrbrace}

  theory Foo_Bar
  imports Main
  begin

  subsection {\ttlbrace}* Basic definitions *{\ttrbrace}

  definition foo :: \dots

  definition bar :: \dots

  subsection {\ttlbrace}* Derived rules *{\ttrbrace}

  lemma fooI: \dots
  lemma fooE: \dots

  subsection {\ttlbrace}* Main theorem {\ttback}label{\ttlbrace}sec:main-theorem{\ttrbrace} *{\ttrbrace}

  theorem main: \dots

  end
  \end{ttbox}
\<close>


subsection \<open>Formal Comments and Antiquotations \label{sec:doc-prep-text}\<close>

text \<open>
  Isabelle \bfindex{source comments}, which are of the form
  \verb,(,\verb,*,~\<open>\<dots>\<close>~\verb,*,\verb,),, essentially act like
  white space and do not really contribute to the content.  They
  mainly serve technical purposes to mark certain oddities in the raw
  input text.  In contrast, \bfindex{formal comments} are portions of
  text that are associated with formal Isabelle/Isar commands
  (\bfindex{marginal comments}), or as standalone paragraphs within a
  theory or proof context (\bfindex{text blocks}).

  \medskip Marginal comments are part of each command's concrete
  syntax \<^cite>\<open>"isabelle-isar-ref"\<close>; the common form is ``\verb,--,~$text$''
  where $text$ is delimited by \verb,",\<open>\<dots>\<close>\verb,", or
  \verb,{,\verb,*,~\<open>\<dots>\<close>~\verb,*,\verb,}, as before.  Multiple
  marginal comments may be given at the same time.  Here is a simple
  example:
\<close>

lemma "A --> A"
  \<comment> \<open>a triviality of propositional logic\<close>
  \<comment> \<open>(should not really bother)\<close>
  by (rule impI) \<comment> \<open>implicit assumption step involved here\<close>

text \<open>
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
  and \bfindex{txt}. Each takes again a single $text$ argument,
  which is interpreted as a free-form paragraph in {\LaTeX}
  (surrounded by some additional vertical space).  The typesetting
  may be changed by redefining the {\LaTeX} environments of
  \verb,isamarkuptext, or \verb,isamarkuptxt,, respectively
  (via \verb,\renewenvironment,).

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
  \<^term>\<open>%x y. x\<close> is a well-typed term.

  \medskip\noindent The output above was produced as follows:
  \begin{ttbox}
text {\ttlbrace}*
  This sentence demonstrates quotations and antiquotations:
  {\at}{\ttlbrace}term "%x y. x"{\ttrbrace} is a well-typed term.
*{\ttrbrace}
  \end{ttbox}\vspace{-\medskipamount}

  The notational change from the ASCII character~\verb,%, to the
  symbol~\<open>\<lambda>\<close> reveals that Isabelle printed this term, after
  parsing and type-checking.  Document preparation enables symbolic
  output by default.

  \medskip The next example includes an option to show the type of all
  variables.  The antiquotation
  \texttt{{\at}}\verb,{term [show_types] "%x y. x"}, produces the
  output @{term [show_types] "%x y. x"}.  Type inference has figured
  out the most general typings in the present theory context.  Terms
  may acquire different typings due to constraints imposed by their
  environment; within a proof, for example, variables are given the
  same types as they have in the main goal statement.

  \medskip Several further kinds of antiquotations and options are
  available \<^cite>\<open>"isabelle-isar-ref"\<close>.  Here are a few commonly used
  combinations:

  \medskip

  \begin{tabular}{ll}
  \texttt{\at}\verb,{typ,~$\tau$\verb,}, & print type $\tau$ \\
  \texttt{\at}\verb,{const,~$c$\verb,}, & check existence of $c$ and print it \\
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

  For example, \texttt{\at}\verb,{text "\<forall>\<exists>"}, produces \<open>\<forall>\<exists>\<close>, according to the standard interpretation of these symbol
  (cf.\ \S\ref{sec:doc-prep-symbols}).  Thus we achieve consistent
  mathematical notation in both the formal and informal parts of the
  document very easily, independently of the term language of
  Isabelle.  Manual {\LaTeX} code would leave more control over the
  typesetting, but is also slightly more tedious.
\<close>


subsection \<open>Interpretation of Symbols \label{sec:doc-prep-symbols}\<close>

text \<open>
  As has been pointed out before (\S\ref{sec:syntax-symbols}),
  Isabelle symbols are the smallest syntactic entities --- a
  straightforward generalization of ASCII characters.  While Isabelle
  does not impose any interpretation of the infinite collection of
  named symbols, {\LaTeX} documents use canonical glyphs for certain
  standard symbols \<^cite>\<open>"isabelle-isar-ref"\<close>.

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
\<close>


subsection \<open>Suppressing Output \label{sec:doc-prep-suppress}\<close>

text \<open>
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
  \texttt{ROOT} itself: some sequential order of \textbf{theories}
  sections may enforce a certain traversal of the dependency graph,
  although this could degrade parallel processing.  The nodes of each
  sub-graph that is specified here are presented in some topological
  order of their formal dependencies.

  Moreover, the system build option \verb,document=false, allows to
  disable document generation for some theories.  Its usage in the
  session \texttt{ROOT} is like this:

\begin{verbatim}
  theories [document = false] T
\end{verbatim}

  \medskip Theory output may be suppressed more selectively, either
  via \bfindex{tagged command regions} or \bfindex{ignored material}.

  Tagged command regions works by annotating commands with named tags,
  which correspond to certain {\LaTeX} markup that tells how to treat
  particular parts of a document when doing the actual type-setting.
  By default, certain Isabelle/Isar commands are implicitly marked up
  using the predefined tags ``\emph{theory}'' (for theory begin and
  end), ``\emph{proof}'' (for proof commands), and ``\emph{ML}'' (for
  commands involving ML code).  Users may add their own tags using the
  \verb,%,\emph{tag} notation right after a command name.  In the
  subsequent example we hide a particularly irrelevant proof:
\<close>

lemma "x = x" by %invisible (simp)

text \<open>
  The original source has been ``\verb,lemma "x = x" by %invisible (simp),''.
  Tags observe the structure of proofs; adjacent commands with the
  same tag are joined into a single region.  The Isabelle document
  preparation system allows the user to specify how to interpret a
  tagged region, in order to keep, drop, or fold the corresponding
  parts of the document.  See the \emph{Isabelle System Manual}
  \<^cite>\<open>"isabelle-system"\<close> for further details, especially on
  \texttt{isabelle build} and \texttt{isabelle document}.

  Ignored material is specified by delimiting the original formal
  source with special source comments
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), and
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,),.  These parts are stripped
  before the type-setting phase, without affecting the formal checking
  of the theory, of course.  For example, we may hide parts of a proof
  that seem unfit for general public inspection.  The following
  ``fully automatic'' proof is actually a fake:
\<close>

lemma "x \<noteq> (0::int) \<Longrightarrow> 0 < x * x"
  by (auto(*<*)simp add: zero_less_mult_iff(*>*))

text \<open>
  \noindent The real source of the proof has been as follows:

\begin{verbatim}
  by (auto(*<*)simp add: zero_less_mult_iff(*>*))
\end{verbatim}
%(*

  \medskip Suppressing portions of printed text demands care.  You
  should not misrepresent the underlying theory development.  It is
  easy to invalidate the visible text by hiding references to
  questionable axioms, for example.
\<close>

(*<*)
end
(*>*)

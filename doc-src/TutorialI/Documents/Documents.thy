(*<*)
theory Documents = Main:
(*>*)

section {* Concrete syntax \label{sec:concrete-syntax} *}

text {*
  Concerning Isabelle's ``inner'' language of simply-typed @{text
  \<lambda>}-calculus, the core concept of Isabelle's elaborate infrastructure
  for concrete syntax is that of general \emph{mixfix
  annotations}\index{mixfix annotations|bold}.  Associated with any
  kind of name and type declaration, mixfixes give rise both to
  grammar productions for the parser and output templates for the
  pretty printer.

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


subsection {* Infixes *}

text {*
  Syntax annotations may be included wherever constants are declared
  directly or indirectly, including \isacommand{consts},
  \isacommand{constdefs}, or \isacommand{datatype} (for the
  constructor operations).  Type-constructors may be annotated as
  well, although this is less frequently encountered in practice
  (@{text "*"} and @{text "+"} types may come to mind).

  Infix declarations\index{infix annotations|bold} provide a useful
  special case of mixfixes, where users need not care about the full
  details of priorities, nesting, spacing, etc.  The subsequent
  example of the exclusive-or operation on boolean values illustrates
  typical infix declarations.
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
  \isakeyword{infixr} refers to nesting to the \emph{right}, which
  would turn @{term "A [+] B [+] C"} into @{text "A [+] (B [+] C)"}.
  In contrast, a \emph{non-oriented} declaration via
  \isakeyword{infix} would always demand explicit parentheses.
  
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
  parenthesized form in the text for clarity.
*}

(*<*)(*FIXME*)
subsection {* Mathematical symbols \label{sec:thy-present-symbols} *}

text {*
  The limitations of the ASCII character set pose a serious
  limitations for representing mathematical notation.  Even worse 
  many handsome combinations have already been used up by HOL
  itself.  Luckily, Isabelle supports infinitely many \emph{named
  symbols}.  FIXME

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


subsection {* Prefixes *}

text {*
  Prefix declarations are an even more degenerate form of mixfix
  annotation, which allow a arbitrary symbolic token to be used for FIXME
*}

datatype currency =
    Euro nat    ("\<euro>")
  | Pounds nat  ("\<pounds>")
  | Yen nat     ("\<yen>")
  | Dollar nat  ("$")

text {*
  FIXME The predefined Isabelle symbols used above are \verb,\<euro>,,
  \verb,\<pounds>,, \verb,\<yen>,, and \verb,\<dollar>,.

  The above syntax annotation makes \verb,\<euro>, stand for the
  datatype constructor constant @{text Euro}, which happens to be a
  function @{typ "nat \<Rightarrow> currency"}.  Using plain application syntax
  we may write @{text "Euro 10"} as @{term "\<euro> 10"}.  So we already
  achieve a decent syntactic representation without having to consider
  arguments and precedences of general mixfix annotations -- prefixes
  are already sufficient.
*}


subsection {* Syntax translations \label{sec:def-translations} *}

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


section {* Document preparation *}

subsection {* Batch-mode sessions *}

subsection {* {\LaTeX} macros *}

subsubsection {* Structure markup *}

subsubsection {* Symbols and characters *}

text {*
  FIXME

  
*}

(*<*)
end
(*>*)
(*>*)

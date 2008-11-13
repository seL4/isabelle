(* $Id$ *)

theory Inner_Syntax
imports Main
begin

chapter {* Inner syntax --- the term language *}

section {* Printing logical entities *}

subsection {* Diagnostic commands *}

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

  \begin{rail}
    'typ' modes? type
    ;
    'term' modes? term
    ;
    'prop' modes? prop
    ;
    'thm' modes? thmrefs
    ;
    ( 'prf' | 'full\_prf' ) modes? thmrefs?
    ;
    'pr' modes? nat? (',' nat)?
    ;

    modes: '(' (name + ) ')'
    ;
  \end{rail}

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

  \item @{command "pr"}~@{text "goals, prems"} prints the current
  proof state (if present), including the proof context, current facts
  and goals.  The optional limit arguments affect the number of goals
  and premises to be displayed, which is initially 10 for both.
  Omitting limit values leaves the current setting unchanged.

  \end{description}

  All of the diagnostic commands above admit a list of @{text modes}
  to be specified, which is appended to the current print mode (see
  also \cite{isabelle-ref}).  Thus the output behavior may be modified
  according particular print mode features.  For example, @{command
  "pr"}~@{text "(latex xsymbols)"} would print the current proof state
  with mathematical symbols and special characters represented in
  {\LaTeX} source, according to the Isabelle style
  \cite{isabelle-sys}.

  Note that antiquotations (cf.\ \secref{sec:antiq}) provide a more
  systematic way to include formal items into the printed text
  document.
*}


subsection {* Details of printed content *}

text {*
  \begin{mldecls} 
    @{index_ML show_types: "bool ref"} & default @{ML false} \\
    @{index_ML show_sorts: "bool ref"} & default @{ML false} \\
    @{index_ML show_consts: "bool ref"} & default @{ML false} \\
    @{index_ML long_names: "bool ref"} & default @{ML false} \\
    @{index_ML short_names: "bool ref"} & default @{ML false} \\
    @{index_ML unique_names: "bool ref"} & default @{ML true} \\
    @{index_ML show_brackets: "bool ref"} & default @{ML false} \\
    @{index_ML eta_contract: "bool ref"} & default @{ML true} \\
    @{index_ML goals_limit: "int ref"} & default @{ML 10} \\
    @{index_ML Proof.show_main_goal: "bool ref"} & default @{ML false} \\
    @{index_ML show_hyps: "bool ref"} & default @{ML false} \\
    @{index_ML show_tags: "bool ref"} & default @{ML false} \\
    @{index_ML show_question_marks: "bool ref"} & default @{ML true} \\
  \end{mldecls}

  These global ML variables control the detail of information that is
  displayed for types, terms, theorems, goals etc.

  In interactive sessions, the user interface usually manages these
  global parameters of the Isabelle process, even with some concept of
  persistence.  Nonetheless it is occasionally useful to manipulate ML
  variables directly, e.g.\ using @{command "ML_val"} or @{command
  "ML_command"}.

  Batch-mode logic sessions may be configured by putting appropriate
  ML text directly into the @{verbatim ROOT.ML} file.

  \begin{description}

  \item @{ML show_types} and @{ML show_sorts} control printing of type
  constraints for term variables, and sort constraints for type
  variables.  By default, neither of these are shown in output.  If
  @{ML show_sorts} is set to @{ML true}, types are always shown as
  well.

  Note that displaying types and sorts may explain why a polymorphic
  inference rule fails to resolve with some goal, or why a rewrite
  rule does not apply as expected.

  \item @{ML show_consts} controls printing of types of constants when
  displaying a goal state.

  Note that the output can be enormous, because polymorphic constants
  often occur at several different type instances.

  \item @{ML long_names}, @{ML short_names}, and @{ML unique_names}
  control the way of printing fully qualified internal names in
  external form.  See also \secref{sec:antiq} for the document
  antiquotation options of the same names.

  \item @{ML show_brackets} controls bracketing in pretty printed
  output.  If set to @{ML true}, all sub-expressions of the pretty
  printing tree will be parenthesized, even if this produces malformed
  term syntax!  This crude way of showing the internal structure of
  pretty printed entities may occasionally help to diagnose problems
  with operator priorities, for example.

  \item @{ML eta_contract} controls @{text "\<eta>"}-contracted printing of
  terms.

  The @{text \<eta>}-contraction law asserts @{prop "(\<lambda>x. f x) \<equiv> f"},
  provided @{text x} is not free in @{text f}.  It asserts
  \emph{extensionality} of functions: @{prop "f \<equiv> g"} if @{prop "f x \<equiv>
  g x"} for all @{text x}.  Higher-order unification frequently puts
  terms into a fully @{text \<eta>}-expanded form.  For example, if @{text
  F} has type @{text "(\<tau> \<Rightarrow> \<tau>) \<Rightarrow> \<tau>"} then its expanded form is @{term
  "\<lambda>h. F (\<lambda>x. h x)"}.

  Setting @{ML eta_contract} makes Isabelle perform @{text
  \<eta>}-contractions before printing, so that @{term "\<lambda>h. F (\<lambda>x. h x)"}
  appears simply as @{text F}.

  Note that the distinction between a term and its @{text \<eta>}-expanded
  form occasionally matters.  While higher-order resolution and
  rewriting operate modulo @{text "\<alpha>\<beta>\<eta>"}-conversion, some other tools
  might look at terms more discretely.

  \item @{ML goals_limit} controls the maximum number of subgoals to
  be shown in goal output.

  \item @{ML Proof.show_main_goal} controls whether the main result to
  be proven should be displayed.  This information might be relevant
  for schematic goals, to inspect the current claim that has been
  synthesized so far.

  \item @{ML show_hyps} controls printing of implicit hypotheses of
  local facts.  Normally, only those hypotheses are displayed that are
  \emph{not} covered by the assumptions of the current context: this
  situation indicates a fault in some tool being used.

  By setting @{ML show_hyps} to @{ML true}, output of \emph{all}
  hypotheses can be enforced, which is occasionally useful for
  diagnostic purposes.

  \item @{ML show_tags} controls printing of extra annotations within
  theorems, such as internal position information, or the case names
  being attached by the attribute @{attribute case_names}.

  Note that the @{attribute tagged} and @{attribute untagged}
  attributes provide low-level access to the collection of tags
  associated with a theorem.

  \item @{ML show_question_marks} controls printing of question marks
  for schematic variables, such as @{text ?x}.  Only the leading
  question mark is affected, the remaining text is unchanged
  (including proper markup for schematic variables that might be
  relevant for user interfaces).

  \end{description}
*}


subsection {* Printing limits *}

text {*
  \begin{mldecls}
    @{index_ML Pretty.setdepth: "int -> unit"} \\
    @{index_ML Pretty.setmargin: "int -> unit"} \\
    @{index_ML print_depth: "int -> unit"} \\
  \end{mldecls}

  These ML functions set limits for pretty printed text.

  \begin{description}

  \item @{ML Pretty.setdepth}~@{text d} tells the pretty printer to
  limit the printing depth to @{text d}.  This affects the display of
  types, terms, theorems etc.  The default value is 0, which permits
  printing to an arbitrary depth.  Other useful values for @{text d}
  are 10 and 20.

  \item @{ML Pretty.setmargin}~@{text m} tells the pretty printer to
  assume a right margin (page width) of @{text m}.  The initial margin
  is 76, but user interfaces might adapt the margin automatically when
  resizing windows.

  \item @{ML print_depth}~@{text n} limits the printing depth of the
  ML toplevel pretty printer; the precise effect depends on the ML
  compiler and run-time system.  Typically @{text n} should be less
  than 10.  Bigger values such as 100--1000 are useful for debugging.

  \end{description}
*}


section {* Mixfix annotations *}

text {* Mixfix annotations specify concrete \emph{inner syntax} of
  Isabelle types and terms.  Some commands such as @{command
  "typedecl"} admit infixes only, while @{command "definition"} etc.\
  support the full range of general mixfixes and binders.  Fixed
  parameters in toplevel theorem statements, locale specifications
  also admit mixfix annotations.

  \indexouternonterm{infix}\indexouternonterm{mixfix}\indexouternonterm{structmixfix}
  \begin{rail}
    infix: '(' ('infix' | 'infixl' | 'infixr') string nat ')'
    ;
    mixfix: infix | '(' string prios? nat? ')' | '(' 'binder' string prios? nat ')'
    ;
    structmixfix: mixfix | '(' 'structure' ')'
    ;

    prios: '[' (nat + ',') ']'
    ;
  \end{rail}

  Here the \railtok{string} specifications refer to the actual mixfix
  template, which may include literal text, spacing, blocks, and
  arguments (denoted by ``@{text _}''); the special symbol
  ``@{verbatim "\<index>"}'' (printed as ``@{text "\<index>"}'') represents an index
  argument that specifies an implicit structure reference (see also
  \secref{sec:locale}).  Infix and binder declarations provide common
  abbreviations for particular mixfix declarations.  So in practice,
  mixfix templates mostly degenerate to literal text for concrete
  syntax, such as ``@{verbatim "++"}'' for an infix symbol.

  \medskip In full generality, mixfix declarations work as follows.
  Suppose a constant @{text "c :: \<tau>\<^sub>1 \<Rightarrow> \<dots> \<tau>\<^sub>n \<Rightarrow> \<tau>"} is
  annotated by @{text "(mixfix [p\<^sub>1, \<dots>, p\<^sub>n] p)"}, where @{text
  "mixfix"} is a string @{text "d\<^sub>0 _ d\<^sub>1 _ \<dots> _ d\<^sub>n"} consisting of
  delimiters that surround argument positions as indicated by
  underscores.

  Altogether this determines a production for a context-free priority
  grammar, where for each argument @{text "i"} the syntactic category
  is determined by @{text "\<tau>\<^sub>i"} (with priority @{text "p\<^sub>i"}), and
  the result category is determined from @{text "\<tau>"} (with
  priority @{text "p"}).  Priority specifications are optional, with
  default 0 for arguments and 1000 for the result.

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

  \begin{itemize}

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

  \end{itemize}

  For example, the template @{verbatim "(_ +/ _)"} specifies an infix
  operator.  There are two argument positions; the delimiter
  @{verbatim "+"} is preceded by a space and followed by a space or
  line break; the entire phrase is a pretty printing block.

  The general idea of pretty printing with blocks and breaks is also
  described in \cite{paulson-ml2}.
*}


section {* Explicit term notation *}

text {*
  \begin{matharray}{rcll}
    @{command_def "notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "no_notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  \begin{rail}
    ('notation' | 'no\_notation') target? mode? (nameref structmixfix + 'and')
    ;
  \end{rail}

  \begin{description}

  \item @{command "notation"}~@{text "c (mx)"} associates mixfix
  syntax with an existing constant or fixed variable.  This is a
  robust interface to the underlying @{command "syntax"} primitive
  (\secref{sec:syn-trans}).  Type declaration and internal syntactic
  representation of the given entity is retrieved from the context.
  
  \item @{command "no_notation"} is similar to @{command "notation"},
  but removes the specified syntax annotation from the present
  context.

  \end{description}
*}

section {* The Pure syntax *}

subsection {* Priority grammars *}

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
  Then
  \[
    @{text "\<alpha> A\<^sup>(\<^sup>p\<^sup>) \<beta> \<longrightarrow>\<^sub>G \<alpha> \<gamma> \<beta>"}
  \]
  if and only if @{text G} contains some production @{text "A\<^sup>(\<^sup>q\<^sup>) = \<gamma>"}
  for @{text "p \<le> q"}.

  \medskip The following grammar for arithmetic expressions
  demonstrates how binding power and associativity of operators can be
  enforced by priorities.

  \begin{center}
  \begin{tabular}{rclr}
  @{text "A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "="} & @{verbatim 0} \\
  @{text "A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "="} & @{verbatim "("} @{text "A\<^sup>(\<^sup>0\<^sup>)"} @{verbatim ")"} \\
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
    @{text A} & @{text "="} & @{verbatim 0} & \qquad\qquad \\
              & @{text "|"} & @{verbatim "("} @{text A} @{verbatim ")"} \\
              & @{text "|"} & @{text A} @{verbatim "+"} @{text "A\<^sup>(\<^sup>1\<^sup>)"} & @{text "(0)"} \\
              & @{text "|"} & @{text "A\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "*"} @{text "A\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
              & @{text "|"} & @{verbatim "-"} @{text "A\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
  \end{tabular}
  \end{center}
*}


subsection {* The Pure grammar *}

text {*
  The priority grammar of the @{text "Pure"} theory is defined as follows:

  \begin{center}
  \begin{supertabular}{rclr}

  @{text any} & = & @{text "prop  |  logic"} \\\\

  @{text prop} & = & @{verbatim "("} @{text prop} @{verbatim ")"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>4\<^sup>)"} @{verbatim "::"} @{text type} & @{text "(3)"} \\
    & @{text "|"} & @{text "any\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "=?="} @{text "any\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "any\<^sup>(\<^sup>3\<^sup>)"} @{verbatim "=="} @{text "any\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "any\<^sup>(\<^sup>3\<^sup>)"} @{text "\<equiv>"} @{text "any\<^sup>(\<^sup>2\<^sup>)"} & @{text "(2)"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>2\<^sup>)"} @{verbatim "==>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{text "prop\<^sup>(\<^sup>2\<^sup>)"} @{text "\<Longrightarrow>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{verbatim "[|"} @{text prop} @{verbatim ";"} @{text "\<dots>"} @{verbatim ";"} @{text prop} @{verbatim "|]"} @{verbatim "==>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{text "\<lbrakk>"} @{text prop} @{verbatim ";"} @{text "\<dots>"} @{verbatim ";"} @{text prop} @{text "\<rbrakk>"} @{text "\<Longrightarrow>"} @{text "prop\<^sup>(\<^sup>1\<^sup>)"} & @{text "(1)"} \\
    & @{text "|"} & @{verbatim "!!"} @{text idts} @{verbatim "."} @{text prop} & @{text "(0)"} \\
    & @{text "|"} & @{text "\<And>"} @{text idts} @{verbatim "."} @{text prop} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim OFCLASS} @{verbatim "("} @{text type} @{verbatim ","} @{text logic} @{verbatim ")"} \\
    & @{text "|"} & @{verbatim SORT_CONSTRAINT} @{verbatim "("} @{text type} @{verbatim ")"} \\
    & @{text "|"} & @{verbatim PROP} @{text aprop} \\\\

  @{text aprop} & = & @{text "id  |  longid  |  var  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "..."} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "(999)"} \\\\

  @{text logic} & = & @{verbatim "("} @{text logic} @{verbatim ")"} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>4\<^sup>)"} @{verbatim "::"} @{text type} & @{text "(3)"} \\
    & @{text "|"} & @{text "id  |  longid  |  var  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "..."} \\
    & @{text "|"} & @{text "logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)"} & @{text "(999)"} \\
    & @{text "|"} & @{verbatim "%"} @{text pttrns} @{verbatim "."} @{text "any\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
    & @{text "|"} & @{text \<lambda>} @{text pttrns} @{verbatim "."} @{text "any\<^sup>(\<^sup>3\<^sup>)"} & @{text "(3)"} \\
    & @{text "|"} & @{verbatim CONST} @{text "id  |  "}@{verbatim CONST} @{text "longid"} \\
    & @{text "|"} & @{verbatim TYPE} @{verbatim "("} @{text type} @{verbatim ")"} \\\\

  @{text idts} & = & @{text "idt  |  idt\<^sup>(\<^sup>1\<^sup>) idts"} & @{text "(0)"} \\\\

  @{text idt} & = & @{verbatim "("} @{text idt} @{verbatim ")"}@{text "  |  id  |  "}@{verbatim "_"} \\
    & @{text "|"} & @{text id} @{verbatim "::"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "_"} @{verbatim "::"} @{text type} & @{text "(0)"} \\\\

  @{text pttrns} & = & @{text "pttrn  |  pttrn\<^sup>(\<^sup>1\<^sup>) pttrns"} & @{text "(0)"} \\\\

  @{text pttrn} & = & @{text idt} \\\\

  @{text type} & = & @{verbatim "("} @{text type} @{verbatim ")"} \\
    & @{text "|"} & @{text "tid  |  tvar  |  "}@{verbatim "_"} \\
    & @{text "|"} & @{text "tid"} @{verbatim "::"} @{text "sort  |  tvar  "}@{verbatim "::"} @{text "sort  |  "}@{verbatim "_"} @{verbatim "::"} @{text "sort"} \\
    & @{text "|"} & @{text "id  |  type\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) id  |  "}@{verbatim "("} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim ")"} @{text id} \\
    & @{text "|"} & @{text "longid  |  type\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) longid  |  "}@{verbatim "("} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim ")"} @{text longid} \\
    & @{text "|"} & @{text "type\<^sup>(\<^sup>1\<^sup>)"} @{verbatim "=>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{text "type\<^sup>(\<^sup>1\<^sup>)"} @{text "\<Rightarrow>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "["} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim "]"} @{verbatim "=>"} @{text type} & @{text "(0)"} \\
    & @{text "|"} & @{verbatim "["} @{text type} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text type} @{verbatim "]"} @{text "\<Rightarrow>"} @{text type} & @{text "(0)"} \\\\

  @{text sort} & = & @{text "id  |  longid  |  "}@{verbatim "{}"}@{text "  |  "}@{verbatim "{"} @{text "id | longid"} @{verbatim ","} @{text "\<dots>"} @{verbatim ","} @{text "id | longid"} @{verbatim "}"} \\
  \end{supertabular}
  \end{center}

  \medskip The following nonterminals are introduced here:

  \begin{description}

  \item @{text "any"} denotes any term.

  \item @{text "prop"} denotes meta-level propositions, which are
  terms of type @{typ prop}.  The syntax of such formulae of the
  meta-logic is carefully distinguished from usual conventions for
  object-logics.  In particular, plain @{text "\<lambda>"}-term
  notation is \emph{not} recognized as @{text "prop"}.

  \item @{text aprop} denotes atomic propositions, which are embedded
  into regular @{typ prop} by means of an explicit @{text "PROP"}
  token.

  Terms of type @{typ prop} with non-constant head, e.g.\ a plain
  variable, are printed in this form.  Constants that yield type @{typ
  prop} are expected to provide their own concrete syntax; otherwise
  the printed version will appear like @{typ logic} and cannot be
  parsed again as @{typ prop}.

  \item @{text logic} denotes arbitrary terms of a logical type,
  excluding type @{typ prop}.  This is the main syntactic category of
  object-logic entities, covering plain @{text \<lambda>}-term notation
  (variables, abstraction, application), plus anything defined by the
  user.

  When specifying notation for logical entities, all logical types
  (excluding @{typ prop}) are \emph{collapsed} to this single category
  of @{typ logic}.

  \item @{text idt} denotes identifiers, possibly constrained by
  types.

  \item @{text idts} denotes a sequence of @{text idt}.  This is the
  most basic category for variables in iterated binders, such as
  @{text "\<lambda>"} or @{text "\<And>"}.

  \item @{text pttrn} and @{text pttrns} denote patterns for
  abstraction, cases bindings etc.  In Pure, these categories start as
  a merely copy of @{text idt} and @{text idts}, respectively.
  Object-logics may add additional productions for binding forms.

  \item @{text type} denotes types of the meta-logic.

  \item @{text sort} denotes meta-level sorts.

  \end{description}

  Some further explanations of certain syntax features are required.

  \begin{itemize}

  \item In @{text idts}, note that @{text "x :: nat y"} is parsed as
  @{text "x :: (nat y)"}, treating @{text y} like a type constructor
  applied to @{text nat}.  To avoid this interpretation, write @{text
  "(x :: nat) y"} with explicit parentheses.

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
  which actually look exactly the same in some {\LaTeX} styles.

  \item Placeholders @{verbatim "_"} may occur in different roles:

  \begin{description}

  \item A type @{text "_"} or @{text "_::sort"} acts like an anonymous
  type-inference parameter, which is filled-in according to the most
  general type produced by the type-checking phase.

  \item A bound @{text "_"} refers to a vacuous abstraction, where the
  body does not refer to the binding introduced here.  As in @{term
  "\<lambda>x _. x"} (which is @{text "\<alpha>"}-equivalent to @{text "\<lambda>x y. x"}).

  \item A free @{text "_"} refers to an implicit outer binding.
  Higher definitional packages usually allow forms like @{text "f x _
  = a"}.

  \item A free @{text "_"} within a term pattern
  (\secref{sec:term-decls}) refers to an anonymous schematic variable
  that is implicitly abstracted over its context of locally bound
  variables.  This allows pattern matching of @{text "{x. x = a}
  (\<IS> {x. x = _})"}, for example.

  \item The three literal dots ``@{verbatim "..."}'' may be also
  written as ellipsis symbol @{verbatim "\<dots>"}.  In both cases it refers
  to a special schematic variable, which is bound in the context.
  This special term abbreviation works nicely calculational resoning
  (\secref{sec:calculation}).

  \end{description}

  \end{itemize}
*}


section {* Syntax and translations \label{sec:syn-trans} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "nonterminals"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "translations"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_translations"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'nonterminals' (name +)
    ;
    ('syntax' | 'no\_syntax') mode? (constdecl +)
    ;
    ('translations' | 'no\_translations') (transpat ('==' | '=>' | '<=' | rightleftharpoons | rightharpoonup | leftharpoondown) transpat +)
    ;

    mode: ('(' ( name | 'output' | name 'output' ) ')')
    ;
    transpat: ('(' nameref ')')? string
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "nonterminals"}~@{text c} declares a type
  constructor @{text c} (without arguments) to act as purely syntactic
  type: a nonterminal symbol of the inner syntax.

  \item @{command "syntax"}~@{text "(mode) decls"} is similar to
  @{command "consts"}~@{text decls}, except that the actual logical
  signature extension is omitted.  Thus the context free grammar of
  Isabelle's inner syntax may be augmented in arbitrary ways,
  independently of the logic.  The @{text mode} argument refers to the
  print mode that the grammar rules belong; unless the @{keyword_ref
  "output"} indicator is given, all productions are added both to the
  input and output grammar.
  
  \item @{command "no_syntax"}~@{text "(mode) decls"} removes grammar
  declarations (and translations) resulting from @{text decls}, which
  are interpreted in the same manner as for @{command "syntax"} above.
  
  \item @{command "translations"}~@{text rules} specifies syntactic
  translation rules (i.e.\ macros): parse~/ print rules (@{text "\<rightleftharpoons>"}),
  parse rules (@{text "\<rightharpoonup>"}), or print rules (@{text "\<leftharpoondown>"}).
  Translation patterns may be prefixed by the syntactic category to be
  used for parsing; the default is @{text logic}.
  
  \item @{command "no_translations"}~@{text rules} removes syntactic
  translation rules, which are interpreted in the same manner as for
  @{command "translations"} above.

  \end{description}
*}


section {* Syntax translation functions *}

text {*
  \begin{matharray}{rcl}
    @{command_def "parse_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "parse_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "typed_print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
  ( 'parse\_ast\_translation' | 'parse\_translation' | 'print\_translation' |
    'typed\_print\_translation' | 'print\_ast\_translation' ) ('(advanced)')? text
  ;
  \end{rail}

  Syntax translation functions written in ML admit almost arbitrary
  manipulations of Isabelle's inner syntax.  Any of the above commands
  have a single \railqtok{text} argument that refers to an ML
  expression of appropriate type, which are as follows by default:

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation   : (string * (ast list -> ast)) list
val parse_translation       : (string * (term list -> term)) list
val print_translation       : (string * (term list -> term)) list
val typed_print_translation :
  (string * (bool -> typ -> term list -> term)) list
val print_ast_translation   : (string * (ast list -> ast)) list
\end{ttbox}

  If the @{text "(advanced)"} option is given, the corresponding
  translation functions may depend on the current theory or proof
  context.  This allows to implement advanced syntax mechanisms, as
  translations functions may refer to specific theory declarations or
  auxiliary proof data.

  See also \cite[\S8]{isabelle-ref} for more information on the
  general concept of syntax transformations in Isabelle.

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
val parse_translation:
  (string * (Proof.context -> term list -> term)) list
val print_translation:
  (string * (Proof.context -> term list -> term)) list
val typed_print_translation:
  (string * (Proof.context -> bool -> typ -> term list -> term)) list
val print_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
\end{ttbox}
*}

end

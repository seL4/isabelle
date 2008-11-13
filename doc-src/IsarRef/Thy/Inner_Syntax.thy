(* $Id$ *)

theory Inner_Syntax
imports Main
begin

chapter {* Inner syntax --- the term language *}

section {* Printing logical entities *}

subsection {* Diagnostic commands *}

text {*
  \begin{matharray}{rcl}
    @{command_def "pr"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "thm"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "term"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "prop"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "typ"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "prf"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "full_prf"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  These diagnostic commands assist interactive development by printing
  internal logical entities in a human-readable fashion.

  \begin{rail}
    'pr' modes? nat? (',' nat)?
    ;
    'thm' modes? thmrefs
    ;
    'term' modes? term
    ;
    'prop' modes? prop
    ;
    'typ' modes? type
    ;
    'prf' modes? thmrefs?
    ;
    'full\_prf' modes? thmrefs?
    ;

    modes: '(' (name + ) ')'
    ;
  \end{rail}

  \begin{description}

  \item @{command "pr"}~@{text "goals, prems"} prints the current
  proof state (if present), including the proof context, current facts
  and goals.  The optional limit arguments affect the number of goals
  and premises to be displayed, which is initially 10 for both.
  Omitting limit values leaves the current setting unchanged.

  \item @{command "thm"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} retrieves
  theorems from the current theory or proof context.  Note that any
  attributes included in the theorem specifications are applied to a
  temporary context derived from the current theory or proof; the
  result is discarded, i.e.\ attributes involved in @{text "a\<^sub>1,
  \<dots>, a\<^sub>n"} do not have any permanent effect.

  \item @{command "term"}~@{text t} and @{command "prop"}~@{text \<phi>}
  read, type-check and print terms or propositions according to the
  current theory or proof context; the inferred type of @{text t} is
  output as well.  Note that these commands are also useful in
  inspecting the current environment of term abbreviations.

  \item @{command "typ"}~@{text \<tau>} reads and prints types of the
  meta-logic according to the current theory or proof context.

  \item @{command "prf"} displays the (compact) proof term of the
  current proof state (if present), or of the given theorems. Note
  that this requires proof terms to be switched on for the current
  object logic (see the ``Proof terms'' section of the Isabelle
  reference manual for information on how to do this).

  \item @{command "full_prf"} is like @{command "prf"}, but displays
  the full proof term, i.e.\ also displays information omitted in the
  compact proof term, which is denoted by ``@{text _}'' placeholders
  there.

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


section {* Mixfix annotations *}

text {* Mixfix annotations specify concrete \emph{inner syntax} of
  Isabelle types and terms.  Some commands such as @{command "types"}
  (see \secref{sec:types-pure}) admit infixes only, while @{command
  "consts"} (see \secref{sec:consts}) and @{command "syntax"} (see
  \secref{sec:syn-trans}) support the full range of general mixfixes
  and binders.

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

  \item @{text "\<^bold>d"} is a delimiter, namely a non-empty
  sequence of characters other than the special characters @{text "'"}
  (single quote), @{text "_"} (underscore), @{text "\<index>"} (index
  symbol), @{text "/"} (slash), @{text "("} and @{text ")"}
  (parentheses).

  A single quote escapes the special meaning of these meta-characters,
  producing a literal version of the following character, unless that
  is a blank.  A single quote followed by a blank separates
  delimiters, without affecting printing, but input tokens may have
  additional white space here.

  \item @{text "_"} is an argument position, which stands for a
  certain syntactic category in the underlying grammar.

  \item @{text "\<index>"} is an indexed argument position; this is
  the place where implicit structure arguments can be attached.

  \item @{text "\<^bold>s"} is a non-empty sequence of spaces for
  printing.  This and the following specifications do not affect
  parsing at all.

  \item @{text "(\<^bold>n"} opens a pretty printing block.  The
  optional number specifies how much indentation to add when a line
  break occurs within the block.  If the parenthesis is not followed
  by digits, the indentation defaults to 0.  A block specified via
  @{text "(00"} is unbreakable.

  \item @{text ")"} closes a pretty printing block.

  \item @{text "//"} forces a line break.

  \item @{text "/\<^bold>s"} allows a line break.  Here @{text
  "\<^bold>s"} stands for the string of spaces (zero or more) right
  after the slash.  These spaces are printed if the break is
  \emph{not} taken.

  \end{itemize}

  For example, the template @{text "(_ +/ _)"} specifies an infix
  operator.  There are two argument positions; the delimiter @{text
  "+"} is preceded by a space and followed by a space or line break;
  the entire phrase is a pretty printing block.

  The general idea of pretty printing with blocks and breaks is also
  described in \cite{paulson-ml2}.
*}


section {* Additional term notation *}

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

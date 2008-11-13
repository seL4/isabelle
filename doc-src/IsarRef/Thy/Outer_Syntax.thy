(* $Id$ *)

theory Outer_Syntax
imports Main
begin

chapter {* Outer syntax *}

text {*
  The rather generic framework of Isabelle/Isar syntax emerges from
  three main syntactic categories: \emph{commands} of the top-level
  Isar engine (covering theory and proof elements), \emph{methods} for
  general goal refinements (analogous to traditional ``tactics''), and
  \emph{attributes} for operations on facts (within a certain
  context).  Subsequently we give a reference of basic syntactic
  entities underlying Isabelle/Isar syntax in a bottom-up manner.
  Concrete theory and proof language elements will be introduced later
  on.

  \medskip In order to get started with writing well-formed
  Isabelle/Isar documents, the most important aspect to be noted is
  the difference of \emph{inner} versus \emph{outer} syntax.  Inner
  syntax is that of Isabelle types and terms of the logic, while outer
  syntax is that of Isabelle/Isar theory sources (specifications and
  proofs).  As a general rule, inner syntax entities may occur only as
  \emph{atomic entities} within outer syntax.  For example, the string
  @{verbatim "\"x + y\""} and identifier @{verbatim z} are legal term
  specifications within a theory, while @{verbatim "x + y"} without
  quotes is not.

  Printed theory documents usually omit quotes to gain readability
  (this is a matter of {\LaTeX} macro setup, say via @{verbatim
  "\\isabellestyle"}, see also \cite{isabelle-sys}).  Experienced
  users of Isabelle/Isar may easily reconstruct the lost technical
  information, while mere readers need not care about quotes at all.

  \medskip Isabelle/Isar input may contain any number of input
  termination characters ``@{verbatim ";"}'' (semicolon) to separate
  commands explicitly.  This is particularly useful in interactive
  shell sessions to make clear where the current command is intended
  to end.  Otherwise, the interpreter loop will continue to issue a
  secondary prompt ``@{verbatim "#"}'' until an end-of-command is
  clearly recognized from the input syntax, e.g.\ encounter of the
  next command keyword.

  More advanced interfaces such as Proof~General \cite{proofgeneral}
  do not require explicit semicolons, the amount of input text is
  determined automatically by inspecting the present content of the
  Emacs text buffer.  In the printed presentation of Isabelle/Isar
  documents semicolons are omitted altogether for readability.

  \begin{warn}
    Proof~General requires certain syntax classification tables in
    order to achieve properly synchronized interaction with the
    Isabelle/Isar process.  These tables need to be consistent with
    the Isabelle version and particular logic image to be used in a
    running session (common object-logics may well change the outer
    syntax).  The standard setup should work correctly with any of the
    ``official'' logic images derived from Isabelle/HOL (including
    HOLCF etc.).  Users of alternative logics may need to tell
    Proof~General explicitly, e.g.\ by giving an option @{verbatim "-k ZF"}
    (in conjunction with @{verbatim "-l ZF"}, to specify the default
    logic image).  Note that option @{verbatim "-L"} does both
    of this at the same time.
  \end{warn}
*}


section {* Lexical matters \label{sec:lex-syntax} *}

text {*
  The Isabelle/Isar outer syntax provides token classes as presented
  below; most of these coincide with the inner lexical syntax as
  presented in \cite{isabelle-ref}.

  \begin{matharray}{rcl}
    @{syntax_def ident} & = & letter\,quasiletter^* \\
    @{syntax_def longident} & = & ident (\verb,.,ident)^+ \\
    @{syntax_def symident} & = & sym^+ ~|~ \verb,\,\verb,<,ident\verb,>, \\
    @{syntax_def nat} & = & digit^+ \\
    @{syntax_def var} & = & ident ~|~ \verb,?,ident ~|~ \verb,?,ident\verb,.,nat \\
    @{syntax_def typefree} & = & \verb,',ident \\
    @{syntax_def typevar} & = & typefree ~|~ \verb,?,typefree ~|~ \verb,?,typefree\verb,.,nat \\
    @{syntax_def string} & = & \verb,", ~\dots~ \verb,", \\
    @{syntax_def altstring} & = & \backquote ~\dots~ \backquote \\
    @{syntax_def verbatim} & = & \verb,{*, ~\dots~ \verb,*,\verb,}, \\[1ex]

    letter & = & latin ~|~ \verb,\,\verb,<,latin\verb,>, ~|~ \verb,\,\verb,<,latin\,latin\verb,>, ~|~ greek ~|~ \\
           &   & \verb,\<^isub>, ~|~ \verb,\<^isup>, \\
    quasiletter & = & letter ~|~ digit ~|~ \verb,_, ~|~ \verb,', \\
    latin & = & \verb,a, ~|~ \dots ~|~ \verb,z, ~|~ \verb,A, ~|~ \dots ~|~ \verb,Z, \\
    digit & = & \verb,0, ~|~ \dots ~|~ \verb,9, \\
    sym & = & \verb,!, ~|~ \verb,#, ~|~ \verb,$, ~|~ \verb,%, ~|~ \verb,&, ~|~
     \verb,*, ~|~ \verb,+, ~|~ \verb,-, ~|~ \verb,/, ~|~ \\
    & & \verb,<, ~|~ \verb,=, ~|~ \verb,>, ~|~ \verb,?, ~|~ \texttt{\at} ~|~
    \verb,^, ~|~ \verb,_, ~|~ \verb,|, ~|~ \verb,~, \\
    greek & = & \verb,\<alpha>, ~|~ \verb,\<beta>, ~|~ \verb,\<gamma>, ~|~ \verb,\<delta>, ~| \\
          &   & \verb,\<epsilon>, ~|~ \verb,\<zeta>, ~|~ \verb,\<eta>, ~|~ \verb,\<theta>, ~| \\
          &   & \verb,\<iota>, ~|~ \verb,\<kappa>, ~|~ \verb,\<mu>, ~|~ \verb,\<nu>, ~| \\
          &   & \verb,\<xi>, ~|~ \verb,\<pi>, ~|~ \verb,\<rho>, ~|~ \verb,\<sigma>, ~|~ \verb,\<tau>, ~| \\
          &   & \verb,\<upsilon>, ~|~ \verb,\<phi>, ~|~ \verb,\<chi>, ~|~ \verb,\<psi>, ~| \\
          &   & \verb,\<omega>, ~|~ \verb,\<Gamma>, ~|~ \verb,\<Delta>, ~|~ \verb,\<Theta>, ~| \\
          &   & \verb,\<Lambda>, ~|~ \verb,\<Xi>, ~|~ \verb,\<Pi>, ~|~ \verb,\<Sigma>, ~| \\
          &   & \verb,\<Upsilon>, ~|~ \verb,\<Phi>, ~|~ \verb,\<Psi>, ~|~ \verb,\<Omega>, \\
  \end{matharray}

  The syntax of @{syntax string} admits any characters, including
  newlines; ``@{verbatim "\""}'' (double-quote) and ``@{verbatim
  "\\"}'' (backslash) need to be escaped by a backslash; arbitrary
  character codes may be specified as ``@{verbatim "\\"}@{text ddd}'',
  with three decimal digits.  Alternative strings according to
  @{syntax altstring} are analogous, using single back-quotes instead.
  The body of @{syntax verbatim} may consist of any text not
  containing ``@{verbatim "*"}@{verbatim "}"}''; this allows
  convenient inclusion of quotes without further escapes.  The greek
  letters do \emph{not} include @{verbatim "\<lambda>"}, which is already used
  differently in the meta-logic.

  Common mathematical symbols such as @{text \<forall>} are represented in
  Isabelle as @{verbatim \<forall>}.  There are infinitely many Isabelle
  symbols like this, although proper presentation is left to front-end
  tools such as {\LaTeX} or Proof~General with the X-Symbol package.
  A list of standard Isabelle symbols that work well with these tools
  is given in \cite[appendix~A]{isabelle-sys}.
  
  Source comments take the form @{verbatim "(*"}~@{text
  "\<dots>"}~@{verbatim "*)"} and may be nested, although user-interface
  tools might prevent this.  Note that this form indicates source
  comments only, which are stripped after lexical analysis of the
  input.  The Isar syntax also provides proper \emph{document
  comments} that are considered as part of the text (see
  \secref{sec:comments}).
*}


section {* Common syntax entities *}

text {*
  We now introduce several basic syntactic entities, such as names,
  terms, and theorem specifications, which are factored out of the
  actual Isar language elements to be described later.
*}


subsection {* Names *}

text {*
  Entity \railqtok{name} usually refers to any name of types,
  constants, theorems etc.\ that are to be \emph{declared} or
  \emph{defined} (so qualified identifiers are excluded here).  Quoted
  strings provide an escape for non-identifier names or those ruled
  out by outer syntax keywords (e.g.\ quoted @{verbatim "\"let\""}).
  Already existing objects are usually referenced by
  \railqtok{nameref}.

  \indexoutertoken{name}\indexoutertoken{parname}\indexoutertoken{nameref}
  \indexoutertoken{int}
  \begin{rail}
    name: ident | symident | string | nat
    ;
    parname: '(' name ')'
    ;
    nameref: name | longident
    ;
    int: nat | '-' nat
    ;
  \end{rail}
*}


subsection {* Comments \label{sec:comments} *}

text {*
  Large chunks of plain \railqtok{text} are usually given
  \railtok{verbatim}, i.e.\ enclosed in @{verbatim "{"}@{verbatim
  "*"}~@{text "\<dots>"}~@{verbatim "*"}@{verbatim "}"}.  For convenience,
  any of the smaller text units conforming to \railqtok{nameref} are
  admitted as well.  A marginal \railnonterm{comment} is of the form
  @{verbatim "--"} \railqtok{text}.  Any number of these may occur
  within Isabelle/Isar commands.

  \indexoutertoken{text}\indexouternonterm{comment}
  \begin{rail}
    text: verbatim | nameref
    ;
    comment: '--' text
    ;
  \end{rail}
*}


subsection {* Type classes, sorts and arities *}

text {*
  Classes are specified by plain names.  Sorts have a very simple
  inner syntax, which is either a single class name @{text c} or a
  list @{text "{c\<^sub>1, \<dots>, c\<^sub>n}"} referring to the
  intersection of these classes.  The syntax of type arities is given
  directly at the outer level.

  \indexouternonterm{sort}\indexouternonterm{arity}
  \indexouternonterm{classdecl}
  \begin{rail}
    classdecl: name (('<' | subseteq) (nameref + ','))?
    ;
    sort: nameref
    ;
    arity: ('(' (sort + ',') ')')? sort
    ;
  \end{rail}
*}


subsection {* Types and terms \label{sec:types-terms} *}

text {*
  The actual inner Isabelle syntax, that of types and terms of the
  logic, is far too sophisticated in order to be modelled explicitly
  at the outer theory level.  Basically, any such entity has to be
  quoted to turn it into a single token (the parsing and type-checking
  is performed internally later).  For convenience, a slightly more
  liberal convention is adopted: quotes may be omitted for any type or
  term that is already atomic at the outer level.  For example, one
  may just write @{verbatim x} instead of quoted @{verbatim "\"x\""}.
  Note that symbolic identifiers (e.g.\ @{verbatim "++"} or @{text
  "\<forall>"} are available as well, provided these have not been superseded
  by commands or other keywords already (such as @{verbatim "="} or
  @{verbatim "+"}).

  \indexoutertoken{type}\indexoutertoken{term}\indexoutertoken{prop}
  \begin{rail}
    type: nameref | typefree | typevar
    ;
    term: nameref | var
    ;
    prop: term
    ;
  \end{rail}

  Positional instantiations are indicated by giving a sequence of
  terms, or the placeholder ``@{text _}'' (underscore), which means to
  skip a position.

  \indexoutertoken{inst}\indexoutertoken{insts}
  \begin{rail}
    inst: underscore | term
    ;
    insts: (inst *)
    ;
  \end{rail}

  Type declarations and definitions usually refer to
  \railnonterm{typespec} on the left-hand side.  This models basic
  type constructor application at the outer syntax level.  Note that
  only plain postfix notation is available here, but no infixes.

  \indexouternonterm{typespec}
  \begin{rail}
    typespec: (() | typefree | '(' ( typefree + ',' ) ')') name
    ;
  \end{rail}
*}


subsection {* Term patterns and declarations \label{sec:term-decls} *}

text {*
  Wherever explicit propositions (or term fragments) occur in a proof
  text, casual binding of schematic term variables may be given
  specified via patterns of the form ``@{text "(\<IS> p\<^sub>1 \<dots>
  p\<^sub>n)"}''.  This works both for \railqtok{term} and \railqtok{prop}.

  \indexouternonterm{termpat}\indexouternonterm{proppat}
  \begin{rail}
    termpat: '(' ('is' term +) ')'
    ;
    proppat: '(' ('is' prop +) ')'
    ;
  \end{rail}

  \medskip Declarations of local variables @{text "x :: \<tau>"} and
  logical propositions @{text "a : \<phi>"} represent different views on
  the same principle of introducing a local scope.  In practice, one
  may usually omit the typing of \railnonterm{vars} (due to
  type-inference), and the naming of propositions (due to implicit
  references of current facts).  In any case, Isar proof elements
  usually admit to introduce multiple such items simultaneously.

  \indexouternonterm{vars}\indexouternonterm{props}
  \begin{rail}
    vars: (name+) ('::' type)?
    ;
    props: thmdecl? (prop proppat? +)
    ;
  \end{rail}

  The treatment of multiple declarations corresponds to the
  complementary focus of \railnonterm{vars} versus
  \railnonterm{props}.  In ``@{text "x\<^sub>1 \<dots> x\<^sub>n :: \<tau>"}''
  the typing refers to all variables, while in @{text "a: \<phi>\<^sub>1 \<dots>
  \<phi>\<^sub>n"} the naming refers to all propositions collectively.
  Isar language elements that refer to \railnonterm{vars} or
  \railnonterm{props} typically admit separate typings or namings via
  another level of iteration, with explicit @{keyword_ref "and"}
  separators; e.g.\ see @{command "fix"} and @{command "assume"} in
  \secref{sec:proof-context}.
*}


subsection {* Mixfix annotations *}

text {*
  Mixfix annotations specify concrete \emph{inner} syntax of Isabelle
  types and terms.  Some commands such as @{command "types"} (see
  \secref{sec:types-pure}) admit infixes only, while @{command
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


subsection {* Attributes and theorems \label{sec:syn-att} *}

text {* Attributes have their own ``semi-inner'' syntax, in the sense
  that input conforming to \railnonterm{args} below is parsed by the
  attribute a second time.  The attribute argument specifications may
  be any sequence of atomic entities (identifiers, strings etc.), or
  properly bracketed argument lists.  Below \railqtok{atom} refers to
  any atomic entity, including any \railtok{keyword} conforming to
  \railtok{symident}.

  \indexoutertoken{atom}\indexouternonterm{args}\indexouternonterm{attributes}
  \begin{rail}
    atom: nameref | typefree | typevar | var | nat | keyword
    ;
    arg: atom | '(' args ')' | '[' args ']'
    ;
    args: arg *
    ;
    attributes: '[' (nameref args * ',') ']'
    ;
  \end{rail}

  Theorem specifications come in several flavors:
  \railnonterm{axmdecl} and \railnonterm{thmdecl} usually refer to
  axioms, assumptions or results of goal statements, while
  \railnonterm{thmdef} collects lists of existing theorems.  Existing
  theorems are given by \railnonterm{thmref} and
  \railnonterm{thmrefs}, the former requires an actual singleton
  result.

  There are three forms of theorem references:
  \begin{enumerate}
  
  \item named facts @{text "a"},

  \item selections from named facts @{text "a(i)"} or @{text "a(j - k)"},

  \item literal fact propositions using @{syntax_ref altstring} syntax
  @{verbatim "`"}@{text "\<phi>"}@{verbatim "`"} (see also method
  @{method_ref fact}).

  \end{enumerate}

  Any kind of theorem specification may include lists of attributes
  both on the left and right hand sides; attributes are applied to any
  immediately preceding fact.  If names are omitted, the theorems are
  not stored within the theorem database of the theory or proof
  context, but any given attributes are applied nonetheless.

  An extra pair of brackets around attributes (like ``@{text
  "[[simproc a]]"}'') abbreviates a theorem reference involving an
  internal dummy fact, which will be ignored later on.  So only the
  effect of the attribute on the background context will persist.
  This form of in-place declarations is particularly useful with
  commands like @{command "declare"} and @{command "using"}.

  \indexouternonterm{axmdecl}\indexouternonterm{thmdecl}
  \indexouternonterm{thmdef}\indexouternonterm{thmref}
  \indexouternonterm{thmrefs}\indexouternonterm{selection}
  \begin{rail}
    axmdecl: name attributes? ':'
    ;
    thmdecl: thmbind ':'
    ;
    thmdef: thmbind '='
    ;
    thmref: (nameref selection? | altstring) attributes? | '[' attributes ']'
    ;
    thmrefs: thmref +
    ;

    thmbind: name attributes | name | attributes
    ;
    selection: '(' ((nat | nat '-' nat?) + ',') ')'
    ;
  \end{rail}
*}

end

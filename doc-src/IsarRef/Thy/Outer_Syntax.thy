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


section {* Lexical matters \label{sec:outer-lex} *}

text {* The outer lexical syntax consists of three main categories of
  syntax tokens:

  \begin{enumerate}

  \item \emph{major keywords} --- the command names that are available
  in the present logic session;

  \item \emph{minor keywords} --- additional literal tokens required
  by the syntax of commands;

  \item \emph{named tokens} --- various categories of identifiers etc.

  \end{enumerate}

  Major keywords and minor keywords are guaranteed to be disjoint.
  This helps user-interfaces to determine the overall structure of a
  theory text, without knowing the full details of command syntax.
  Internally, there is some additional information about the kind of
  major keywords, which approximates the command type (theory command,
  proof command etc.).

  Keywords override named tokens.  For example, the presence of a
  command called @{verbatim term} inhibits the identifier @{verbatim
  term}, but the string @{verbatim "\"term\""} can be used instead.
  By convention, the outer syntax always allows quoted strings in
  addition to identifiers, wherever a named entity is expected.

  When tokenizing a given input sequence, the lexer repeatedly takes
  the longest prefix of the input that forms a valid token.  Spaces,
  tabs, newlines and formfeeds between tokens serve as explicit
  separators.

  \medskip The categories for named tokens are defined once and for
  all as follows.

  \begin{center}
  \begin{supertabular}{rcl}
    @{syntax_def ident} & = & @{text "letter quasiletter\<^sup>*"} \\
    @{syntax_def longident} & = & @{text "ident("}@{verbatim "."}@{text "ident)\<^sup>+"} \\
    @{syntax_def symident} & = & @{text "sym\<^sup>+  |  "}@{verbatim "\\"}@{verbatim "<"}@{text ident}@{verbatim ">"} \\
    @{syntax_def nat} & = & @{text "digit\<^sup>+"} \\
    @{syntax_def var} & = & @{verbatim "?"}@{text "ident  |  "}@{verbatim "?"}@{text ident}@{verbatim "."}@{text nat} \\
    @{syntax_def typefree} & = & @{verbatim "'"}@{text ident} \\
    @{syntax_def typevar} & = & @{verbatim "?"}@{text "typefree  |  "}@{verbatim "?"}@{text typefree}@{verbatim "."}@{text nat} \\
    @{syntax_def string} & = & @{verbatim "\""} @{text "\<dots>"} @{verbatim "\""} \\
    @{syntax_def altstring} & = & @{verbatim "`"} @{text "\<dots>"} @{verbatim "`"} \\
    @{syntax_def verbatim} & = & @{verbatim "{*"} @{text "\<dots>"} @{verbatim "*"}@{verbatim "}"} \\[1ex]

    @{text letter} & = & @{text "latin  |  "}@{verbatim "\\"}@{verbatim "<"}@{text latin}@{verbatim ">"}@{text "  |  "}@{verbatim "\\"}@{verbatim "<"}@{text "latin latin"}@{verbatim ">"}@{text "  |  greek  |"} \\
          &   & @{verbatim "\<^isub>"}@{text "  |  "}@{verbatim "\<^isup>"} \\
    @{text quasiletter} & = & @{text "letter  |  digit  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "'"} \\
    @{text latin} & = & @{verbatim a}@{text "  | \<dots> |  "}@{verbatim z}@{text "  |  "}@{verbatim A}@{text "  |  \<dots> |  "}@{verbatim Z} \\
    @{text digit} & = & @{verbatim "0"}@{text "  |  \<dots> |  "}@{verbatim "9"} \\
    @{text sym} & = & @{verbatim "!"}@{text "  |  "}@{verbatim "#"}@{text "  |  "}@{verbatim "$"}@{text "  |  "}@{verbatim "%"}@{text "  |  "}@{verbatim "&"}@{text "  |  "}@{verbatim "*"}@{text "  |  "}@{verbatim "+"}@{text "  |  "}@{verbatim "-"}@{text "  |  "}@{verbatim "/"}@{text "  |"} \\
    & & @{verbatim "<"}@{text "  |  "}@{verbatim "="}@{text "  |  "}@{verbatim ">"}@{text "  |  "}@{verbatim "?"}@{text "  |  "}@{verbatim "@"}@{text "  |  "}@{verbatim "^"}@{text "  |  "}@{verbatim "_"}@{text "  |  "}@{verbatim "|"}@{text "  |  "}@{verbatim "~"} \\
    @{text greek} & = & @{verbatim "\<alpha>"}@{text "  |  "}@{verbatim "\<beta>"}@{text "  |  "}@{verbatim "\<gamma>"}@{text "  |  "}@{verbatim "\<delta>"}@{text "  |"} \\
          &   & @{verbatim "\<epsilon>"}@{text "  |  "}@{verbatim "\<zeta>"}@{text "  |  "}@{verbatim "\<eta>"}@{text "  |  "}@{verbatim "\<theta>"}@{text "  |"} \\
          &   & @{verbatim "\<iota>"}@{text "  |  "}@{verbatim "\<kappa>"}@{text "  |  "}@{verbatim "\<mu>"}@{text "  |  "}@{verbatim "\<nu>"}@{text "  |"} \\
          &   & @{verbatim "\<xi>"}@{text "  |  "}@{verbatim "\<pi>"}@{text "  |  "}@{verbatim "\<rho>"}@{text "  |  "}@{verbatim "\<sigma>"}@{text "  |  "}@{verbatim "\<tau>"}@{text "  |"} \\
          &   & @{verbatim "\<upsilon>"}@{text "  |  "}@{verbatim "\<phi>"}@{text "  |  "}@{verbatim "\<chi>"}@{text "  |  "}@{verbatim "\<psi>"}@{text "  |"} \\
          &   & @{verbatim "\<omega>"}@{text "  |  "}@{verbatim "\<Gamma>"}@{text "  |  "}@{verbatim "\<Delta>"}@{text "  |  "}@{verbatim "\<Theta>"}@{text "  |"} \\
          &   & @{verbatim "\<Lambda>"}@{text "  |  "}@{verbatim "\<Xi>"}@{text "  |  "}@{verbatim "\<Pi>"}@{text "  |  "}@{verbatim "\<Sigma>"}@{text "  |"} \\
          &   & @{verbatim "\<Upsilon>"}@{text "  |  "}@{verbatim "\<Phi>"}@{text "  |  "}@{verbatim "\<Psi>"}@{text "  |  "}@{verbatim "\<Omega>"} \\
  \end{supertabular}
  \end{center}

  A @{syntax_ref var} or @{syntax_ref typevar} describes an unknown,
  which is internally a pair of base name and index (ML type @{ML_type
  indexname}).  These components are either separated by a dot as in
  @{text "?x.1"} or @{text "?x7.3"} or run together as in @{text
  "?x1"}.  The latter form is possible if the base name does not end
  with digits.  If the index is 0, it may be dropped altogether:
  @{text "?x"} and @{text "?x0"} and @{text "?x.0"} all refer to the
  same unknown, with basename @{text "x"} and index 0.

  The syntax of @{syntax_ref string} admits any characters, including
  newlines; ``@{verbatim "\""}'' (double-quote) and ``@{verbatim
  "\\"}'' (backslash) need to be escaped by a backslash; arbitrary
  character codes may be specified as ``@{verbatim "\\"}@{text ddd}'',
  with three decimal digits.  Alternative strings according to
  @{syntax_ref altstring} are analogous, using single back-quotes
  instead.

  The body of @{syntax_ref verbatim} may consist of any text not
  containing ``@{verbatim "*"}@{verbatim "}"}''; this allows
  convenient inclusion of quotes without further escapes.  There is no
  way to escape ``@{verbatim "*"}@{verbatim "}"}''.  If the quoted
  text is {\LaTeX} source, one may usually add some blank or comment
  to avoid the critical character sequence.

  Source comments take the form @{verbatim "(*"}~@{text
  "\<dots>"}~@{verbatim "*)"} and may be nested, although the user-interface
  might prevent this.  Note that this form indicates source comments
  only, which are stripped after lexical analysis of the input.  The
  Isar syntax also provides proper \emph{document comments} that are
  considered as part of the text (see \secref{sec:comments}).

  Common mathematical symbols such as @{text \<forall>} are represented in
  Isabelle as @{verbatim \<forall>}.  There are infinitely many Isabelle
  symbols like this, although proper presentation is left to front-end
  tools such as {\LaTeX} or Proof~General with the X-Symbol package.
  A list of predefined Isabelle symbols that work well with these
  tools is given in \appref{app:symbols}.  Note that @{verbatim "\<lambda>"}
  does not belong to the @{text letter} category, since it is already
  used differently in the Pure term language.
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

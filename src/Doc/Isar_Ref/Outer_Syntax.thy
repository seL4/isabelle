(*:maxLineLen=78:*)

theory Outer_Syntax
  imports Main Base
begin

chapter \<open>Outer syntax --- the theory language \label{ch:outer-syntax}\<close>

text \<open>
  The rather generic framework of Isabelle/Isar syntax emerges from three main
  syntactic categories: \<^emph>\<open>commands\<close> of the top-level Isar engine (covering
  theory and proof elements), \<^emph>\<open>methods\<close> for general goal refinements
  (analogous to traditional ``tactics''), and \<^emph>\<open>attributes\<close> for operations on
  facts (within a certain context). Subsequently we give a reference of basic
  syntactic entities underlying Isabelle/Isar syntax in a bottom-up manner.
  Concrete theory and proof language elements will be introduced later on.

  \<^medskip>
  In order to get started with writing well-formed Isabelle/Isar documents,
  the most important aspect to be noted is the difference of \<^emph>\<open>inner\<close> versus
  \<^emph>\<open>outer\<close> syntax. Inner syntax is that of Isabelle types and terms of the
  logic, while outer syntax is that of Isabelle/Isar theory sources
  (specifications and proofs). As a general rule, inner syntax entities may
  occur only as \<^emph>\<open>atomic entities\<close> within outer syntax. For example, the
  string \<^verbatim>\<open>"x + y"\<close> and identifier \<^verbatim>\<open>z\<close> are legal term specifications within a
  theory, while \<^verbatim>\<open>x + y\<close> without quotes is not.

  Printed theory documents usually omit quotes to gain readability (this is a
  matter of {\LaTeX} macro setup, say via \<^verbatim>\<open>\isabellestyle\<close>, see also @{cite
  "isabelle-system"}). Experienced users of Isabelle/Isar may easily
  reconstruct the lost technical information, while mere readers need not care
  about quotes at all.
\<close>


section \<open>Commands\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "print_commands"}\<open>\<^sup>*\<close> & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "help"}\<open>\<^sup>*\<close> & : & \<open>any \<rightarrow>\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command help} (@{syntax name} * )
  \<close>

  \<^descr> @{command "print_commands"} prints all outer syntax keywords
  and commands.

  \<^descr> @{command "help"}~\<open>pats\<close> retrieves outer syntax
  commands according to the specified name patterns.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Some common diagnostic commands are retrieved like this (according to usual
  naming conventions):
\<close>

help "print"
help "find"


section \<open>Lexical matters \label{sec:outer-lex}\<close>

text \<open>
  The outer lexical syntax consists of three main categories of syntax tokens:

    \<^enum> \<^emph>\<open>major keywords\<close> --- the command names that are available
    in the present logic session;

    \<^enum> \<^emph>\<open>minor keywords\<close> --- additional literal tokens required
    by the syntax of commands;

    \<^enum> \<^emph>\<open>named tokens\<close> --- various categories of identifiers etc.

  Major keywords and minor keywords are guaranteed to be disjoint. This helps
  user-interfaces to determine the overall structure of a theory text, without
  knowing the full details of command syntax. Internally, there is some
  additional information about the kind of major keywords, which approximates
  the command type (theory command, proof command etc.).

  Keywords override named tokens. For example, the presence of a command
  called \<^verbatim>\<open>term\<close> inhibits the identifier \<^verbatim>\<open>term\<close>, but the string \<^verbatim>\<open>"term"\<close> can
  be used instead. By convention, the outer syntax always allows quoted
  strings in addition to identifiers, wherever a named entity is expected.

  When tokenizing a given input sequence, the lexer repeatedly takes the
  longest prefix of the input that forms a valid token. Spaces, tabs, newlines
  and formfeeds between tokens serve as explicit separators.

  \<^medskip>
  The categories for named tokens are defined once and for all as follows.

  \begin{center}
  \begin{supertabular}{rcl}
    @{syntax_def short_ident} & = & \<open>letter (subscript\<^sup>? quasiletter)\<^sup>*\<close> \\
    @{syntax_def long_ident} & = & \<open>short_ident(\<close>\<^verbatim>\<open>.\<close>\<open>short_ident)\<^sup>+\<close> \\
    @{syntax_def sym_ident} & = & \<open>sym\<^sup>+  |\<close>~~\<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>short_ident\<close>\<^verbatim>\<open>>\<close> \\
    @{syntax_def nat} & = & \<open>digit\<^sup>+\<close> \\
    @{syntax_def float} & = & @{syntax_ref nat}\<^verbatim>\<open>.\<close>@{syntax_ref nat}~~\<open>|\<close>~~\<^verbatim>\<open>-\<close>@{syntax_ref nat}\<^verbatim>\<open>.\<close>@{syntax_ref nat} \\
    @{syntax_def term_var} & = & \<^verbatim>\<open>?\<close>\<open>short_ident  |\<close>~~\<^verbatim>\<open>?\<close>\<open>short_ident\<close>\<^verbatim>\<open>.\<close>\<open>nat\<close> \\
    @{syntax_def type_ident} & = & \<^verbatim>\<open>'\<close>\<open>short_ident\<close> \\
    @{syntax_def type_var} & = & \<^verbatim>\<open>?\<close>\<open>type_ident  |\<close>~~\<^verbatim>\<open>?\<close>\<open>type_ident\<close>\<^verbatim>\<open>.\<close>\<open>nat\<close> \\
    @{syntax_def string} & = & \<^verbatim>\<open>"\<close> \<open>\<dots>\<close> \<^verbatim>\<open>"\<close> \\
    @{syntax_def altstring} & = & \<^verbatim>\<open>`\<close> \<open>\<dots>\<close> \<^verbatim>\<open>`\<close> \\
    @{syntax_def cartouche} & = & \<^verbatim>\<open>\<open>\<close> \<open>\<dots>\<close> \<^verbatim>\<open>\<close>\<close> \\
    @{syntax_def verbatim} & = & \<^verbatim>\<open>{*\<close> \<open>\<dots>\<close> \<^verbatim>\<open>*}\<close> \\[1ex]

    \<open>letter\<close> & = & \<open>latin  |\<close>~~\<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>latin\<close>\<^verbatim>\<open>>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>latin latin\<close>\<^verbatim>\<open>>\<close>~~\<open>|  greek  |\<close> \\
    \<open>subscript\<close> & = & \<^verbatim>\<open>\<^sub>\<close> \\
    \<open>quasiletter\<close> & = & \<open>letter  |  digit  |\<close>~~\<^verbatim>\<open>_\<close>~~\<open>|\<close>~~\<^verbatim>\<open>'\<close> \\
    \<open>latin\<close> & = & \<^verbatim>\<open>a\<close>~~\<open>| \<dots> |\<close>~~\<^verbatim>\<open>z\<close>~~\<open>|\<close>~~\<^verbatim>\<open>A\<close>~~\<open>|  \<dots> |\<close>~~\<^verbatim>\<open>Z\<close> \\
    \<open>digit\<close> & = & \<^verbatim>\<open>0\<close>~~\<open>|  \<dots> |\<close>~~\<^verbatim>\<open>9\<close> \\
    \<open>sym\<close> & = & \<^verbatim>\<open>!\<close>~~\<open>|\<close>~~\<^verbatim>\<open>#\<close>~~\<open>|\<close>~~\<^verbatim>\<open>$\<close>~~\<open>|\<close>~~\<^verbatim>\<open>%\<close>~~\<open>|\<close>~~\<^verbatim>\<open>&\<close>~~\<open>|\<close>~~\<^verbatim>\<open>*\<close>~~\<open>|\<close>~~\<^verbatim>\<open>+\<close>~~\<open>|\<close>~~\<^verbatim>\<open>-\<close>~~\<open>|\<close>~~\<^verbatim>\<open>/\<close>~~\<open>|\<close> \\
    & & \<^verbatim>\<open><\<close>~~\<open>|\<close>~~\<^verbatim>\<open>=\<close>~~\<open>|\<close>~~\<^verbatim>\<open>>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>?\<close>~~\<open>|\<close>~~\<^verbatim>\<open>@\<close>~~\<open>|\<close>~~\<^verbatim>\<open>^\<close>~~\<open>|\<close>~~\<^verbatim>\<open>_\<close>~~\<open>|\<close>~~\<^verbatim>\<open>|\<close>~~\<open>|\<close>~~\<^verbatim>\<open>~\<close> \\
    \<open>greek\<close> & = & \<^verbatim>\<open>\<alpha>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<beta>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<gamma>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<delta>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<epsilon>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<zeta>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<eta>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<theta>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<iota>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<kappa>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<mu>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<nu>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<xi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<pi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<rho>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<sigma>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<tau>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<upsilon>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<phi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<chi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<psi>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<omega>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Gamma>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Delta>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Theta>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<Lambda>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Xi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Pi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Sigma>\<close>~~\<open>|\<close> \\
          &   & \<^verbatim>\<open>\<Upsilon>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Phi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Psi>\<close>~~\<open>|\<close>~~\<^verbatim>\<open>\<Omega>\<close> \\
  \end{supertabular}
  \end{center}

  A @{syntax_ref term_var} or @{syntax_ref type_var} describes an unknown,
  which is internally a pair of base name and index (ML type \<^ML_type>\<open>indexname\<close>). These components are either separated by a dot as in \<open>?x.1\<close> or
  \<open>?x7.3\<close> or run together as in \<open>?x1\<close>. The latter form is possible if the base
  name does not end with digits. If the index is 0, it may be dropped
  altogether: \<open>?x\<close> and \<open>?x0\<close> and \<open>?x.0\<close> all refer to the same unknown, with
  basename \<open>x\<close> and index 0.

  The syntax of @{syntax_ref string} admits any characters, including
  newlines; ``\<^verbatim>\<open>"\<close>'' (double-quote) and ``\<^verbatim>\<open>\\<close>'' (backslash) need to be
  escaped by a backslash; arbitrary character codes may be specified as
  ``\<^verbatim>\<open>\\<close>\<open>ddd\<close>'', with three decimal digits. Alternative strings according to
  @{syntax_ref altstring} are analogous, using single back-quotes instead.

  The body of @{syntax_ref verbatim} may consist of any text not containing
  ``\<^verbatim>\<open>*}\<close>''; this allows to include quotes without further escapes, but there
  is no way to escape ``\<^verbatim>\<open>*}\<close>''. Cartouches do not have this limitation.

  A @{syntax_ref cartouche} consists of arbitrary text, with properly balanced
  blocks of ``@{verbatim "\<open>"}~\<open>\<dots>\<close>~@{verbatim "\<close>"}''. Note that the rendering
  of cartouche delimiters is usually like this: ``\<open>\<open> \<dots> \<close>\<close>''.

  Source comments take the form \<^verbatim>\<open>(*\<close>~\<open>\<dots>\<close>~\<^verbatim>\<open>*)\<close> and may be nested: the text is
  removed after lexical analysis of the input and thus not suitable for
  documentation. The Isar syntax also provides proper \<^emph>\<open>document comments\<close>
  that are considered as part of the text (see \secref{sec:comments}).

  Common mathematical symbols such as \<open>\<forall>\<close> are represented in Isabelle as \<^verbatim>\<open>\<forall>\<close>.
  There are infinitely many Isabelle symbols like this, although proper
  presentation is left to front-end tools such as {\LaTeX} or Isabelle/jEdit.
  A list of predefined Isabelle symbols that work well with these tools is
  given in \appref{app:symbols}. Note that \<^verbatim>\<open>\<lambda>\<close> does not belong to the
  \<open>letter\<close> category, since it is already used differently in the Pure term
  language.
\<close>


section \<open>Common syntax entities\<close>

text \<open>
  We now introduce several basic syntactic entities, such as names, terms, and
  theorem specifications, which are factored out of the actual Isar language
  elements to be described later.
\<close>


subsection \<open>Names\<close>

text \<open>
  Entity @{syntax name} usually refers to any name of types, constants,
  theorems etc.\ Quoted strings provide an escape for non-identifier names or
  those ruled out by outer syntax keywords (e.g.\ quoted \<^verbatim>\<open>"let"\<close>).

  \<^rail>\<open>
    @{syntax_def name}: @{syntax short_ident} | @{syntax long_ident} |
      @{syntax sym_ident} | @{syntax nat} | @{syntax string}
    ;
    @{syntax_def par_name}: '(' @{syntax name} ')'
  \<close>

  A @{syntax_def system_name} is like @{syntax name}, but it excludes
  white-space characters and needs to conform to file-name notation. Name
  components that are special on Windows (e.g.\ \<^verbatim>\<open>CON\<close>, \<^verbatim>\<open>PRN\<close>, \<^verbatim>\<open>AUX\<close>) are
  excluded on all platforms.
\<close>


subsection \<open>Numbers\<close>

text \<open>
  The outer lexical syntax (\secref{sec:outer-lex}) admits natural numbers and
  floating point numbers. These are combined as @{syntax int} and @{syntax
  real} as follows.

  \<^rail>\<open>
    @{syntax_def int}: @{syntax nat} | '-' @{syntax nat}
    ;
    @{syntax_def real}: @{syntax float} | @{syntax int}
  \<close>

  Note that there is an overlap with the category @{syntax name}, which also
  includes @{syntax nat}.
\<close>


subsection \<open>Embedded content\<close>

text \<open>
  Entity @{syntax embedded} refers to content of other languages: cartouches
  allow arbitrary nesting of sub-languages that respect the recursive
  balancing of cartouche delimiters. Quoted strings are possible as well, but
  require escaped quotes when nested. As a shortcut, tokens that appear as
  plain identifiers in the outer language may be used as inner language
  content without delimiters.

  \<^rail>\<open>
    @{syntax_def embedded}: @{syntax cartouche} | @{syntax string} |
      @{syntax short_ident} | @{syntax long_ident} | @{syntax sym_ident} |
      @{syntax term_var} | @{syntax type_ident} | @{syntax type_var} | @{syntax nat}
  \<close>
\<close>


subsection \<open>Document text\<close>

text \<open>
  A chunk of document @{syntax text} is usually given as @{syntax cartouche}
  \<open>\<open>\<dots>\<close>\<close> or @{syntax verbatim}, i.e.\ enclosed in \<^verbatim>\<open>{*\<close>~\<open>\<dots>\<close>~\<^verbatim>\<open>*}\<close>. For
  convenience, any of the smaller text unit that conforms to @{syntax name} is
  admitted as well.

  \<^rail>\<open>
    @{syntax_def text}: @{syntax embedded} | @{syntax verbatim}
  \<close>

  Typical uses are document markup commands, like \<^theory_text>\<open>chapter\<close>, \<^theory_text>\<open>section\<close> etc.
  (\secref{sec:markup}).
\<close>


subsection \<open>Document comments \label{sec:comments}\<close>

text \<open>
  Formal comments are an integral part of the document, but are logically void
  and removed from the resulting theory or term content. The output of
  document preparation (\chref{ch:document-prep}) supports various styles,
  according to the following kinds of comments.

    \<^item> Marginal comment of the form \<^verbatim>\<open>\<comment>\<close>~\<open>\<open>text\<close>\<close> or \<open>\<comment>\<close>~\<open>\<open>text\<close>\<close>, usually with
    a single space between the comment symbol and the argument cartouche. The
    given argument is typeset as regular text, with formal antiquotations
    (\secref{sec:antiq}).

    \<^item> Canceled text of the form \<^verbatim>\<open>\<^cancel>\<close>\<open>\<open>text\<close>\<close> (no white space between the
    control symbol and the argument cartouche). The argument is typeset as
    formal Isabelle source and overlaid with a ``strike-through'' pattern,
    e.g. \<^theory_text>\<open>\<^cancel>\<open>bad\<close>\<close>.

    \<^item> Raw {\LaTeX} source of the form \<^verbatim>\<open>\<^latex>\<close>\<open>\<open>argument\<close>\<close> (no white space
    between the control symbol and the argument cartouche). This allows to
    augment the generated {\TeX} source arbitrarily, without any sanity
    checks!

  These formal comments work uniformly in outer syntax, inner syntax (term
  language), Isabelle/ML, and some other embedded languages of Isabelle.
\<close>


subsection \<open>Type classes, sorts and arities\<close>

text \<open>
  Classes are specified by plain names. Sorts have a very simple inner syntax,
  which is either a single class name \<open>c\<close> or a list \<open>{c\<^sub>1, \<dots>, c\<^sub>n}\<close> referring
  to the intersection of these classes. The syntax of type arities is given
  directly at the outer level.

  \<^rail>\<open>
    @{syntax_def classdecl}: @{syntax name} (('<' | '\<subseteq>') (@{syntax name} + ','))?
    ;
    @{syntax_def sort}: @{syntax embedded}
    ;
    @{syntax_def arity}: ('(' (@{syntax sort} + ',') ')')? @{syntax sort}
  \<close>
\<close>


subsection \<open>Types and terms \label{sec:types-terms}\<close>

text \<open>
  The actual inner Isabelle syntax, that of types and terms of the logic, is
  far too sophisticated in order to be modelled explicitly at the outer theory
  level. Basically, any such entity has to be quoted to turn it into a single
  token (the parsing and type-checking is performed internally later). For
  convenience, a slightly more liberal convention is adopted: quotes may be
  omitted for any type or term that is already atomic at the outer level. For
  example, one may just write \<^verbatim>\<open>x\<close> instead of quoted \<^verbatim>\<open>"x"\<close>. Note that
  symbolic identifiers (e.g.\ \<^verbatim>\<open>++\<close> or \<open>\<forall>\<close> are available as well, provided
  these have not been superseded by commands or other keywords already (such
  as \<^verbatim>\<open>=\<close> or \<^verbatim>\<open>+\<close>).

  \<^rail>\<open>
    @{syntax_def type}: @{syntax embedded}
    ;
    @{syntax_def term}: @{syntax embedded}
    ;
    @{syntax_def prop}: @{syntax embedded}
  \<close>

  Positional instantiations are specified as a sequence of terms, or the
  placeholder ``\<open>_\<close>'' (underscore), which means to skip a position.

  \<^rail>\<open>
    @{syntax_def inst}: '_' | @{syntax term}
    ;
    @{syntax_def insts}: (@{syntax inst} *)
  \<close>

  Named instantiations are specified as pairs of assignments \<open>v = t\<close>, which
  refer to schematic variables in some theorem that is instantiated. Both type
  and terms instantiations are admitted, and distinguished by the usual syntax
  of variable names.

  \<^rail>\<open>
    @{syntax_def named_inst}: variable '=' (type | term)
    ;
    @{syntax_def named_insts}: (named_inst @'and' +)
    ;
    variable: @{syntax name} | @{syntax term_var} | @{syntax type_ident} | @{syntax type_var}
  \<close>

  Type declarations and definitions usually refer to @{syntax typespec} on the
  left-hand side. This models basic type constructor application at the outer
  syntax level. Note that only plain postfix notation is available here, but
  no infixes.

  \<^rail>\<open>
    @{syntax_def typespec}:
      (() | @{syntax type_ident} | '(' ( @{syntax type_ident} + ',' ) ')') @{syntax name}
    ;
    @{syntax_def typespec_sorts}:
      (() | (@{syntax type_ident} ('::' @{syntax sort})?) |
        '(' ( (@{syntax type_ident} ('::' @{syntax sort})?) + ',' ) ')') @{syntax name}
  \<close>
\<close>


subsection \<open>Term patterns and declarations \label{sec:term-decls}\<close>

text \<open>
  Wherever explicit propositions (or term fragments) occur in a proof text,
  casual binding of schematic term variables may be given specified via
  patterns of the form ``\<^theory_text>\<open>(is p\<^sub>1 \<dots> p\<^sub>n)\<close>''. This works both for @{syntax
  term} and @{syntax prop}.

  \<^rail>\<open>
    @{syntax_def term_pat}: '(' (@'is' @{syntax term} +) ')'
    ;
    @{syntax_def prop_pat}: '(' (@'is' @{syntax prop} +) ')'
  \<close>

  \<^medskip>
  Declarations of local variables \<open>x :: \<tau>\<close> and logical propositions \<open>a : \<phi>\<close>
  represent different views on the same principle of introducing a local
  scope. In practice, one may usually omit the typing of @{syntax vars} (due
  to type-inference), and the naming of propositions (due to implicit
  references of current facts). In any case, Isar proof elements usually admit
  to introduce multiple such items simultaneously.

  \<^rail>\<open>
    @{syntax_def vars}:
      (((@{syntax name} +) ('::' @{syntax type})? |
        @{syntax name} ('::' @{syntax type})? @{syntax mixfix}) + @'and')
    ;
    @{syntax_def props}: @{syntax thmdecl}? (@{syntax prop} @{syntax prop_pat}? +)
    ;
    @{syntax_def props'}: (@{syntax prop} @{syntax prop_pat}? +)
  \<close>

  The treatment of multiple declarations corresponds to the complementary
  focus of @{syntax vars} versus @{syntax props}. In ``\<open>x\<^sub>1 \<dots> x\<^sub>n :: \<tau>\<close>'' the
  typing refers to all variables, while in \<open>a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close> the naming refers to
  all propositions collectively. Isar language elements that refer to @{syntax
  vars} or @{syntax props} typically admit separate typings or namings via
  another level of iteration, with explicit @{keyword_ref "and"} separators;
  e.g.\ see @{command "fix"} and @{command "assume"} in
  \secref{sec:proof-context}.
\<close>


subsection \<open>Attributes and theorems \label{sec:syn-att}\<close>

text \<open>
  Attributes have their own ``semi-inner'' syntax, in the sense that input
  conforming to @{syntax args} below is parsed by the attribute a second time.
  The attribute argument specifications may be any sequence of atomic entities
  (identifiers, strings etc.), or properly bracketed argument lists. Below
  @{syntax atom} refers to any atomic entity, including any @{syntax keyword}
  conforming to @{syntax sym_ident}.

  \<^rail>\<open>
    @{syntax_def atom}: @{syntax name} | @{syntax type_ident} |
      @{syntax type_var} | @{syntax term_var} | @{syntax nat} | @{syntax float} |
      @{syntax keyword} | @{syntax cartouche}
    ;
    arg: @{syntax atom} | '(' @{syntax args} ')' | '[' @{syntax args} ']'
    ;
    @{syntax_def args}: arg *
    ;
    @{syntax_def attributes}: '[' (@{syntax name} @{syntax args} * ',') ']'
  \<close>

  Theorem specifications come in several flavors: @{syntax axmdecl} and
  @{syntax thmdecl} usually refer to axioms, assumptions or results of goal
  statements, while @{syntax thmdef} collects lists of existing theorems.
  Existing theorems are given by @{syntax thm} and @{syntax thms}, the
  former requires an actual singleton result.

  There are three forms of theorem references:

    \<^enum> named facts \<open>a\<close>,

    \<^enum> selections from named facts \<open>a(i)\<close> or \<open>a(j - k)\<close>,

    \<^enum> literal fact propositions using token syntax @{syntax_ref altstring}
    \<^verbatim>\<open>`\<close>\<open>\<phi>\<close>\<^verbatim>\<open>`\<close> or @{syntax_ref cartouche}
    \<open>\<open>\<phi>\<close>\<close> (see also method @{method_ref fact}).

  Any kind of theorem specification may include lists of attributes both on
  the left and right hand sides; attributes are applied to any immediately
  preceding fact. If names are omitted, the theorems are not stored within the
  theorem database of the theory or proof context, but any given attributes
  are applied nonetheless.

  An extra pair of brackets around attributes (like ``\<open>[[simproc a]]\<close>'')
  abbreviates a theorem reference involving an internal dummy fact, which will
  be ignored later on. So only the effect of the attribute on the background
  context will persist. This form of in-place declarations is particularly
  useful with commands like @{command "declare"} and @{command "using"}.

  \<^rail>\<open>
    @{syntax_def axmdecl}: @{syntax name} @{syntax attributes}? ':'
    ;
    @{syntax_def thmbind}:
      @{syntax name} @{syntax attributes} | @{syntax name} | @{syntax attributes}
    ;
    @{syntax_def thmdecl}: thmbind ':'
    ;
    @{syntax_def thmdef}: thmbind '='
    ;
    @{syntax_def thm}:
      (@{syntax name} selection? | @{syntax altstring} | @{syntax cartouche})
        @{syntax attributes}? |
      '[' @{syntax attributes} ']'
    ;
    @{syntax_def thms}: @{syntax thm} +
    ;
    selection: '(' ((@{syntax nat} | @{syntax nat} '-' @{syntax nat}?) + ',') ')'
  \<close>
\<close>


subsection \<open>Structured specifications\<close>

text \<open>
  Structured specifications use propositions with explicit notation for the
  ``eigen-context'' to describe rule structure: \<open>\<And>x. A x \<Longrightarrow> \<dots> \<Longrightarrow> B x\<close> is
  expressed as \<^theory_text>\<open>B x if A x and \<dots> for x\<close>. It is also possible to use dummy
  terms ``\<open>_\<close>'' (underscore) to refer to locally fixed variables anonymously.

  Multiple specifications are delimited by ``\<open>|\<close>'' to emphasize separate
  cases: each with its own scope of inferred types for free variables.


  \<^rail>\<open>
    @{syntax_def for_fixes}: (@'for' @{syntax vars})?
    ;
    @{syntax_def multi_specs}: (@{syntax structured_spec} + '|')
    ;
    @{syntax_def structured_spec}:
      @{syntax thmdecl}? @{syntax prop} @{syntax spec_prems} @{syntax for_fixes}
    ;
    @{syntax_def spec_prems}: (@'if' ((@{syntax prop}+) + @'and'))?
    ;
    @{syntax_def specification}: @{syntax vars} @'where' @{syntax multi_specs}
  \<close>
\<close>


section \<open>Diagnostic commands\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "print_theory"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_definitions"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_methods"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_attributes"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_theorems"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "find_theorems"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "find_consts"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "thm_deps"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "unused_thms"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_facts"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_term_bindings"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{command print_theory} |
      @@{command print_definitions} |
      @@{command print_methods} |
      @@{command print_attributes} |
      @@{command print_theorems} |
      @@{command print_facts}) ('!'?)
    ;
    @@{command find_theorems} ('(' @{syntax nat}? 'with_dups'? ')')? \<newline> (thm_criterion*)
    ;
    thm_criterion: ('-'?) ('name' ':' @{syntax name} | 'intro' | 'elim' | 'dest' |
      'solves' | 'simp' ':' @{syntax term} | @{syntax term})
    ;
    @@{command find_consts} (const_criterion*)
    ;
    const_criterion: ('-'?)
      ('name' ':' @{syntax name} | 'strict' ':' @{syntax type} | @{syntax type})
    ;
    @@{command thm_deps} @{syntax thmrefs}
    ;
    @@{command unused_thms} ((@{syntax name} +) '-' (@{syntax name} * ))?
  \<close>

  These commands print certain parts of the theory and proof context. Note
  that there are some further ones available, such as for the set of rules
  declared for simplifications.

  \<^descr> @{command "print_theory"} prints the main logical content of the
  background theory; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> @{command "print_definitions"} prints dependencies of definitional
  specifications within the background theory, which may be constants
  (\secref{sec:term-definitions}, \secref{sec:overloading}) or types
  (\secref{sec:types-pure}, \secref{sec:hol-typedef}); the ``\<open>!\<close>'' option
  indicates extra verbosity.

  \<^descr> @{command "print_methods"} prints all proof methods available in the
  current theory context; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> @{command "print_attributes"} prints all attributes available in the
  current theory context; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> @{command "print_theorems"} prints theorems of the background theory
  resulting from the last command; the ``\<open>!\<close>'' option indicates extra
  verbosity.

  \<^descr> @{command "print_facts"} prints all local facts of the current context,
  both named and unnamed ones; the ``\<open>!\<close>'' option indicates extra verbosity.

  \<^descr> @{command "print_term_bindings"} prints all term bindings that are present
  in the context.

  \<^descr> @{command "find_theorems"}~\<open>criteria\<close> retrieves facts from the theory or
  proof context matching all of given search criteria. The criterion \<open>name: p\<close>
  selects all theorems whose fully qualified name matches pattern \<open>p\<close>, which
  may contain ``\<open>*\<close>'' wildcards. The criteria \<open>intro\<close>, \<open>elim\<close>, and \<open>dest\<close>
  select theorems that match the current goal as introduction, elimination or
  destruction rules, respectively. The criterion \<open>solves\<close> returns all rules
  that would directly solve the current goal. The criterion \<open>simp: t\<close> selects
  all rewrite rules whose left-hand side matches the given term. The criterion
  term \<open>t\<close> selects all theorems that contain the pattern \<open>t\<close> -- as usual,
  patterns may contain occurrences of the dummy ``\<open>_\<close>'', schematic variables,
  and type constraints.

  Criteria can be preceded by ``\<open>-\<close>'' to select theorems that do \<^emph>\<open>not\<close> match.
  Note that giving the empty list of criteria yields \<^emph>\<open>all\<close> currently known
  facts. An optional limit for the number of printed facts may be given; the
  default is 40. By default, duplicates are removed from the search result.
  Use \<open>with_dups\<close> to display duplicates.

  \<^descr> @{command "find_consts"}~\<open>criteria\<close> prints all constants whose type meets
  all of the given criteria. The criterion \<open>strict: ty\<close> is met by any type
  that matches the type pattern \<open>ty\<close>. Patterns may contain both the dummy type
  ``\<open>_\<close>'' and sort constraints. The criterion \<open>ty\<close> is similar, but it also
  matches against subtypes. The criterion \<open>name: p\<close> and the prefix ``\<open>-\<close>''
  function as described for @{command "find_theorems"}.

  \<^descr> @{command "thm_deps"}~\<open>thms\<close> prints immediate theorem dependencies, i.e.\
  the union of all theorems that are used directly to prove the argument
  facts, without going deeper into the dependency graph.

  \<^descr> @{command "unused_thms"}~\<open>A\<^sub>1 \<dots> A\<^sub>m - B\<^sub>1 \<dots> B\<^sub>n\<close> displays all theorems
  that are proved in theories \<open>B\<^sub>1 \<dots> B\<^sub>n\<close> or their parents but not in \<open>A\<^sub>1 \<dots>
  A\<^sub>m\<close> or their parents and that are never used. If \<open>n\<close> is \<open>0\<close>, the end of the
  range of theories defaults to the current theory. If no range is specified,
  only the unused theorems in the current theory are displayed.
\<close>

end

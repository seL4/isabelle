(* $Id$ *)

theory pure
imports CPure
begin

chapter {* Basic language elements \label{ch:pure-syntax} *}

text {*
  Subsequently, we introduce the main part of Pure theory and proof
  commands, together with fundamental proof methods and attributes.
  \Chref{ch:gen-tools} describes further Isar elements provided by
  generic tools and packages (such as the Simplifier) that are either
  part of Pure Isabelle or pre-installed in most object logics.
  Specific language elements introduced by the major object-logics are
  described in \chref{ch:hol} (Isabelle/HOL), \chref{ch:holcf}
  (Isabelle/HOLCF), and \chref{ch:zf} (Isabelle/ZF).  Nevertheless,
  examples given in the generic parts will usually refer to
  Isabelle/HOL as well.

  \medskip Isar commands may be either \emph{proper} document
  constructors, or \emph{improper commands}.  Some proof methods and
  attributes introduced later are classified as improper as well.
  Improper Isar language elements, which are subsequently marked by
  ``@{text "\<^sup>*"}'', are often helpful when developing proof
  documents, while their use is discouraged for the final
  human-readable outcome.  Typical examples are diagnostic commands
  that print terms or theorems according to the current context; other
  commands emulate old-style tactical theorem proving.
*}


section {* Theory commands *}

subsection {* Defining theories \label{sec:begin-thy} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "header"} & : & \isarkeep{toplevel} \\
    @{command_def "theory"} & : & \isartrans{toplevel}{theory} \\
    @{command_def "end"} & : & \isartrans{theory}{toplevel} \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory, which contain both
  specifications and proofs; occasionally definitional mechanisms also
  require some explicit proof.

  The first ``real'' command of any theory has to be @{command
  "theory"}, which starts a new theory based on the merge of existing
  ones.  Just preceding the @{command "theory"} keyword, there may be
  an optional @{command "header"} declaration, which is relevant to
  document preparation only; it acts very much like a special
  pre-theory markup command (cf.\ \secref{sec:markup-thy} and
  \secref{sec:markup-thy}).  The @{command "end"} command concludes a
  theory development; it has to be the very last command of any theory
  file loaded in batch-mode.

  \begin{rail}
    'header' text
    ;
    'theory' name 'imports' (name +) uses? 'begin'
    ;

    uses: 'uses' ((name | parname) +);
  \end{rail}

  \begin{descr}

  \item [@{command "header"}~@{text "text"}] provides plain text
  markup just preceding the formal beginning of a theory.  In actual
  document preparation the corresponding {\LaTeX} macro @{verbatim
  "\\isamarkupheader"} may be redefined to produce chapter or section
  headings.  See also \secref{sec:markup-thy} and
  \secref{sec:markup-prf} for further markup commands.
  
  \item [@{command "theory"}~@{text "A \<IMPORTS> B\<^sub>1 \<dots>
  B\<^sub>n \<BEGIN>"}] starts a new theory @{text A} based on the
  merge of existing theories @{text "B\<^sub>1 \<dots> B\<^sub>n"}.
  
  Due to inclusion of several ancestors, the overall theory structure
  emerging in an Isabelle session forms a directed acyclic graph
  (DAG).  Isabelle's theory loader ensures that the sources
  contributing to the development graph are always up-to-date.
  Changed files are automatically reloaded when processing theory
  headers.
  
  The optional @{keyword_def "uses"} specification declares additional
  dependencies on extra files (usually ML sources).  Files will be
  loaded immediately (as ML), unless the name is put in parentheses,
  which merely documents the dependency to be resolved later in the
  text (typically via explicit @{command_ref "use"} in the body text,
  see \secref{sec:ML}).
  
  \item [@{command "end"}] concludes the current theory definition or
  context switch.

  \end{descr}
*}


subsection {* Markup commands \label{sec:markup-thy} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "chapter"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "section"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "subsection"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "subsubsection"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "text"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "text_raw"} & : & \isarkeep{local{\dsh}theory} \\
  \end{matharray}

  Apart from formal comments (see \secref{sec:comments}), markup
  commands provide a structured way to insert text into the document
  generated from a theory (see \cite{isabelle-sys} for more
  information on Isabelle's document preparation tools).

  \begin{rail}
    ('chapter' | 'section' | 'subsection' | 'subsubsection' | 'text') target? text
    ;
    'text\_raw' text
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "chapter"}, @{command "section"}, @{command
  "subsection"}, and @{command "subsubsection"}] mark chapter and
  section headings.

  \item [@{command "text"}] specifies paragraphs of plain text.

  \item [@{command "text_raw"}] inserts {\LaTeX} source into the
  output, without additional markup.  Thus the full range of document
  manipulations becomes available.

  \end{descr}

  The @{text "text"} argument of these markup commands (except for
  @{command "text_raw"}) may contain references to formal entities
  (``antiquotations'', see also \secref{sec:antiq}).  These are
  interpreted in the present theory context, or the named @{text
  "target"}.

  Any of these markup elements corresponds to a {\LaTeX} command with
  the name prefixed by @{verbatim "\\isamarkup"}.  For the sectioning
  commands this is a plain macro with a single argument, e.g.\
  @{verbatim "\\isamarkupchapter{"}@{text "\<dots>"}@{verbatim "}"} for
  @{command "chapter"}.  The @{command "text"} markup results in a
  {\LaTeX} environment @{verbatim "\\begin{isamarkuptext}"} @{text
  "\<dots>"} @{verbatim "\\end{isamarkuptext}"}, while @{command "text_raw"}
  causes the text to be inserted directly into the {\LaTeX} source.

  \medskip Additional markup commands are available for proofs (see
  \secref{sec:markup-prf}).  Also note that the @{command_ref
  "header"} declaration (see \secref{sec:begin-thy}) admits to insert
  section markup just preceding the actual theory definition.
*}


subsection {* Type classes and sorts \label{sec:classes} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "classes"} & : & \isartrans{theory}{theory} \\
    @{command_def "classrel"} & : & \isartrans{theory}{theory} & (axiomatic!) \\
    @{command_def "defaultsort"} & : & \isartrans{theory}{theory} \\
    @{command_def "class_deps"} & : & \isarkeep{theory~|~proof} \\
  \end{matharray}

  \begin{rail}
    'classes' (classdecl +)
    ;
    'classrel' (nameref ('<' | subseteq) nameref + 'and')
    ;
    'defaultsort' sort
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "classes"}~@{text "c \<subseteq> c\<^sub>1, \<dots>, c\<^sub>n"}]
  declares class @{text c} to be a subclass of existing classes @{text
  "c\<^sub>1, \<dots>, c\<^sub>n"}.  Cyclic class structures are not permitted.

  \item [@{command "classrel"}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"}] states
  subclass relations between existing classes @{text "c\<^sub>1"} and
  @{text "c\<^sub>2"}.  This is done axiomatically!  The @{command_ref
  "instance"} command (see \secref{sec:axclass}) provides a way to
  introduce proven class relations.

  \item [@{command "defaultsort"}~@{text s}] makes sort @{text s} the
  new default sort for any type variables given without sort
  constraints.  Usually, the default sort would be only changed when
  defining a new object-logic.

  \item [@{command "class_deps"}] visualizes the subclass relation,
  using Isabelle's graph browser tool (see also \cite{isabelle-sys}).

  \end{descr}
*}


subsection {* Primitive types and type abbreviations \label{sec:types-pure} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "types"} & : & \isartrans{theory}{theory} \\
    @{command_def "typedecl"} & : & \isartrans{theory}{theory} \\
    @{command_def "nonterminals"} & : & \isartrans{theory}{theory} \\
    @{command_def "arities"} & : & \isartrans{theory}{theory} & (axiomatic!) \\
  \end{matharray}

  \begin{rail}
    'types' (typespec '=' type infix? +)
    ;
    'typedecl' typespec infix?
    ;
    'nonterminals' (name +)
    ;
    'arities' (nameref '::' arity +)
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "types"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>"}]
  introduces \emph{type synonym} @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"}
  for existing type @{text "\<tau>"}.  Unlike actual type definitions, as
  are available in Isabelle/HOL for example, type synonyms are just
  purely syntactic abbreviations without any logical significance.
  Internally, type synonyms are fully expanded.
  
  \item [@{command "typedecl"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"}]
  declares a new type constructor @{text t}, intended as an actual
  logical type (of the object-logic, if available).

  \item [@{command "nonterminals"}~@{text c}] declares type
  constructors @{text c} (without arguments) to act as purely
  syntactic types, i.e.\ nonterminal symbols of Isabelle's inner
  syntax of terms or types.

  \item [@{command "arities"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n)
  s"}] augments Isabelle's order-sorted signature of types by new type
  constructor arities.  This is done axiomatically!  The @{command_ref
  "instance"} command (see \S\ref{sec:axclass}) provides a way to
  introduce proven type arities.

  \end{descr}
*}


subsection {* Primitive constants and definitions \label{sec:consts} *}

text {*
  Definitions essentially express abbreviations within the logic.  The
  simplest form of a definition is @{text "c :: \<sigma> \<equiv> t"}, where @{text
  c} is a newly declared constant.  Isabelle also allows derived forms
  where the arguments of @{text c} appear on the left, abbreviating a
  prefix of @{text \<lambda>}-abstractions, e.g.\ @{text "c \<equiv> \<lambda>x y. t"} may be
  written more conveniently as @{text "c x y \<equiv> t"}.  Moreover,
  definitions may be weakened by adding arbitrary pre-conditions:
  @{text "A \<Longrightarrow> c x y \<equiv> t"}.

  \medskip The built-in well-formedness conditions for definitional
  specifications are:

  \begin{itemize}

  \item Arguments (on the left-hand side) must be distinct variables.

  \item All variables on the right-hand side must also appear on the
  left-hand side.

  \item All type variables on the right-hand side must also appear on
  the left-hand side; this prohibits @{text "0 :: nat \<equiv> length ([] ::
  \<alpha> list)"} for example.

  \item The definition must not be recursive.  Most object-logics
  provide definitional principles that can be used to express
  recursion safely.

  \end{itemize}

  Overloading means that a constant being declared as @{text "c :: \<alpha>
  decl"} may be defined separately on type instances @{text "c ::
  (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t decl"} for each type constructor @{text
  t}.  The right-hand side may mention overloaded constants
  recursively at type instances corresponding to the immediate
  argument types @{text "\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n"}.  Incomplete
  specification patterns impose global constraints on all occurrences,
  e.g.\ @{text "d :: \<alpha> \<times> \<alpha>"} on the left-hand side means that all
  corresponding occurrences on some right-hand side need to be an
  instance of this, general @{text "d :: \<alpha> \<times> \<beta>"} will be disallowed.

  \begin{matharray}{rcl}
    @{command_def "consts"} & : & \isartrans{theory}{theory} \\
    @{command_def "defs"} & : & \isartrans{theory}{theory} \\
    @{command_def "constdefs"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  \begin{rail}
    'consts' ((name '::' type mixfix?) +)
    ;
    'defs' ('(' 'unchecked'? 'overloaded'? ')')? \\ (axmdecl prop +)
    ;
  \end{rail}

  \begin{rail}
    'constdefs' structs? (constdecl? constdef +)
    ;

    structs: '(' 'structure' (vars + 'and') ')'
    ;
    constdecl:  ((name '::' type mixfix | name '::' type | name mixfix) 'where'?) | name 'where'
    ;
    constdef: thmdecl? prop
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "consts"}~@{text "c :: \<sigma>"}] declares constant
  @{text c} to have any instance of type scheme @{text \<sigma>}.  The
  optional mixfix annotations may attach concrete syntax to the
  constants declared.
  
  \item [@{command "defs"}~@{text "name: eqn"}] introduces @{text eqn}
  as a definitional axiom for some existing constant.
  
  The @{text "(unchecked)"} option disables global dependency checks
  for this definition, which is occasionally useful for exotic
  overloading.  It is at the discretion of the user to avoid malformed
  theory specifications!
  
  The @{text "(overloaded)"} option declares definitions to be
  potentially overloaded.  Unless this option is given, a warning
  message would be issued for any definitional equation with a more
  special type than that of the corresponding constant declaration.
  
  \item [@{command "constdefs"}] provides a streamlined combination of
  constants declarations and definitions: type-inference takes care of
  the most general typing of the given specification (the optional
  type constraint may refer to type-inference dummies ``@{text
  _}'' as usual).  The resulting type declaration needs to agree with
  that of the specification; overloading is \emph{not} supported here!
  
  The constant name may be omitted altogether, if neither type nor
  syntax declarations are given.  The canonical name of the
  definitional axiom for constant @{text c} will be @{text c_def},
  unless specified otherwise.  Also note that the given list of
  specifications is processed in a strictly sequential manner, with
  type-checking being performed independently.
  
  An optional initial context of @{text "(structure)"} declarations
  admits use of indexed syntax, using the special symbol @{verbatim
  "\<index>"} (printed as ``@{text "\<index>"}'').  The latter concept is
  particularly useful with locales (see also \S\ref{sec:locale}).

  \end{descr}
*}


subsection {* Syntax and translations \label{sec:syn-trans} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "syntax"} & : & \isartrans{theory}{theory} \\
    @{command_def "no_syntax"} & : & \isartrans{theory}{theory} \\
    @{command_def "translations"} & : & \isartrans{theory}{theory} \\
    @{command_def "no_translations"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  \begin{rail}
    ('syntax' | 'no\_syntax') mode? (constdecl +)
    ;
    ('translations' | 'no\_translations') (transpat ('==' | '=>' | '<=' | rightleftharpoons | rightharpoonup | leftharpoondown) transpat +)
    ;

    mode: ('(' ( name | 'output' | name 'output' ) ')')
    ;
    transpat: ('(' nameref ')')? string
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "syntax"}~@{text "(mode) decls"}] is similar to
  @{command "consts"}~@{text decls}, except that the actual logical
  signature extension is omitted.  Thus the context free grammar of
  Isabelle's inner syntax may be augmented in arbitrary ways,
  independently of the logic.  The @{text mode} argument refers to the
  print mode that the grammar rules belong; unless the @{keyword_ref
  "output"} indicator is given, all productions are added both to the
  input and output grammar.
  
  \item [@{command "no_syntax"}~@{text "(mode) decls"}] removes
  grammar declarations (and translations) resulting from @{text
  decls}, which are interpreted in the same manner as for @{command
  "syntax"} above.
  
  \item [@{command "translations"}~@{text rules}] specifies syntactic
  translation rules (i.e.\ macros): parse~/ print rules (@{text "\<rightleftharpoons>"}),
  parse rules (@{text "\<rightharpoonup>"}), or print rules (@{text "\<leftharpoondown>"}).
  Translation patterns may be prefixed by the syntactic category to be
  used for parsing; the default is @{text logic}.
  
  \item [@{command "no_translations"}~@{text rules}] removes syntactic
  translation rules, which are interpreted in the same manner as for
  @{command "translations"} above.

  \end{descr}
*}


subsection {* Axioms and theorems \label{sec:axms-thms} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axioms"} & : & \isartrans{theory}{theory} & (axiomatic!) \\
    @{command_def "lemmas"} & : & \isarkeep{local{\dsh}theory} \\
    @{command_def "theorems"} & : & isarkeep{local{\dsh}theory} \\
  \end{matharray}

  \begin{rail}
    'axioms' (axmdecl prop +)
    ;
    ('lemmas' | 'theorems') target? (thmdef? thmrefs + 'and')
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "axioms"}~@{text "a: \<phi>"}] introduces arbitrary
  statements as axioms of the meta-logic.  In fact, axioms are
  ``axiomatic theorems'', and may be referred later just as any other
  theorem.
  
  Axioms are usually only introduced when declaring new logical
  systems.  Everyday work is typically done the hard way, with proper
  definitions and proven theorems.
  
  \item [@{command "lemmas"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}]
  retrieves and stores existing facts in the theory context, or the
  specified target context (see also \secref{sec:target}).  Typical
  applications would also involve attributes, to declare Simplifier
  rules, for example.
  
  \item [@{command "theorems"}] is essentially the same as @{command
  "lemmas"}, but marks the result as a different kind of facts.

  \end{descr}
*}


subsection {* Name spaces *}

text {*
  \begin{matharray}{rcl}
    @{command_def "global"} & : & \isartrans{theory}{theory} \\
    @{command_def "local"} & : & \isartrans{theory}{theory} \\
    @{command_def "hide"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  \begin{rail}
    'hide' ('(open)')? name (nameref + )
    ;
  \end{rail}

  Isabelle organizes any kind of name declarations (of types,
  constants, theorems etc.) by separate hierarchically structured name
  spaces.  Normally the user does not have to control the behavior of
  name spaces by hand, yet the following commands provide some way to
  do so.

  \begin{descr}

  \item [@{command "global"} and @{command "local"}] change the
  current name declaration mode.  Initially, theories start in
  @{command "local"} mode, causing all names to be automatically
  qualified by the theory name.  Changing this to @{command "global"}
  causes all names to be declared without the theory prefix, until
  @{command "local"} is declared again.
  
  Note that global names are prone to get hidden accidently later,
  when qualified names of the same base name are introduced.
  
  \item [@{command "hide"}~@{text "space names"}] fully removes
  declarations from a given name space (which may be @{text "class"},
  @{text "type"}, @{text "const"}, or @{text "fact"}); with the @{text
  "(open)"} option, only the base name is hidden.  Global
  (unqualified) names may never be hidden.
  
  Note that hiding name space accesses has no impact on logical
  declarations -- they remain valid internally.  Entities that are no
  longer accessible to the user are printed with the special qualifier
  ``@{text "??"}'' prefixed to the full internal name.

  \end{descr}
*}


subsection {* Incorporating ML code \label{sec:ML} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "use"} & : & \isarkeep{theory~|~local{\dsh}theory} \\
    @{command_def "ML"} & : & \isarkeep{theory~|~local{\dsh}theory} \\
    @{command_def "ML_val"} & : & \isartrans{\cdot}{\cdot} \\
    @{command_def "ML_command"} & : & \isartrans{\cdot}{\cdot} \\
    @{command_def "setup"} & : & \isartrans{theory}{theory} \\
    @{command_def "method_setup"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  \begin{rail}
    'use' name
    ;
    ('ML' | 'ML\_val' | 'ML\_command' | 'setup') text
    ;
    'method\_setup' name '=' text text
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "use"}~@{text "file"}] reads and executes ML
  commands from @{text "file"}.  The current theory context is passed
  down to the ML toplevel and may be modified, using @{ML
  "Context.>>"} or derived ML commands.  The file name is checked with
  the @{keyword_ref "uses"} dependency declaration given in the theory
  header (see also \secref{sec:begin-thy}).
  
  \item [@{command "ML"}~@{text "text"}] is similar to @{command
  "use"}, but executes ML commands directly from the given @{text
  "text"}.

  \item [@{command "ML_val"} and @{command "ML_command"}] are
  diagnostic versions of @{command "ML"}, which means that the context
  may not be updated.  @{command "ML_val"} echos the bindings produced
  at the ML toplevel, but @{command "ML_command"} is silent.
  
  \item [@{command "setup"}~@{text "text"}] changes the current theory
  context by applying @{text "text"}, which refers to an ML expression
  of type @{ML_type "theory -> theory"}.  This enables to initialize
  any object-logic specific tools and packages written in ML, for
  example.
  
  \item [@{command "method_setup"}~@{text "name = text description"}]
  defines a proof method in the current theory.  The given @{text
  "text"} has to be an ML expression of type @{ML_type "Args.src ->
  Proof.context -> Proof.method"}.  Parsing concrete method syntax
  from @{ML_type Args.src} input can be quite tedious in general.  The
  following simple examples are for methods without any explicit
  arguments, or a list of theorems, respectively.

%FIXME proper antiquotations
{\footnotesize
\begin{verbatim}
 Method.no_args (Method.METHOD (fn facts => foobar_tac))
 Method.thms_args (fn thms => Method.METHOD (fn facts => foobar_tac))
 Method.ctxt_args (fn ctxt => Method.METHOD (fn facts => foobar_tac))
 Method.thms_ctxt_args (fn thms => fn ctxt =>
    Method.METHOD (fn facts => foobar_tac))
\end{verbatim}
}

  Note that mere tactic emulations may ignore the @{text facts}
  parameter above.  Proper proof methods would do something
  appropriate with the list of current facts, though.  Single-rule
  methods usually do strict forward-chaining (e.g.\ by using @{ML
  Drule.multi_resolves}), while automatic ones just insert the facts
  using @{ML Method.insert_tac} before applying the main tactic.

  \end{descr}
*}


subsection {* Syntax translation functions *}

text {*
  \begin{matharray}{rcl}
    @{command_def "parse_ast_translation"} & : & \isartrans{theory}{theory} \\
    @{command_def "parse_translation"} & : & \isartrans{theory}{theory} \\
    @{command_def "print_translation"} & : & \isartrans{theory}{theory} \\
    @{command_def "typed_print_translation"} & : & \isartrans{theory}{theory} \\
    @{command_def "print_ast_translation"} & : & \isartrans{theory}{theory} \\
    @{command_def "token_translation"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  \begin{rail}
  ( 'parse\_ast\_translation' | 'parse\_translation' | 'print\_translation' |
    'typed\_print\_translation' | 'print\_ast\_translation' ) ('(advanced)')? text
  ;

  'token\_translation' text
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
val token_translation       :
  (string * string * (string -> string * real)) list
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
  (string * (Context.generic -> ast list -> ast)) list
val parse_translation:
  (string * (Context.generic -> term list -> term)) list
val print_translation:
  (string * (Context.generic -> term list -> term)) list
val typed_print_translation:
  (string * (Context.generic -> bool -> typ -> term list -> term)) list
val print_ast_translation:
  (string * (Context.generic -> ast list -> ast)) list
\end{ttbox}
*}


subsection {* Oracles *}

text {*
  \begin{matharray}{rcl}
    @{command_def "oracle"} & : & \isartrans{theory}{theory} \\
  \end{matharray}

  The oracle interface promotes a given ML function @{ML_text
  "theory -> T -> term"} to @{ML_text "theory -> T -> thm"}, for some
  type @{ML_text T} given by the user.  This acts like an infinitary
  specification of axioms -- there is no internal check of the
  correctness of the results!  The inference kernel records oracle
  invocations within the internal derivation object of theorems, and
  the pretty printer attaches ``@{text "[!]"}'' to indicate results
  that are not fully checked by Isabelle inferences.

  \begin{rail}
    'oracle' name '(' type ')' '=' text
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "oracle"}~@{text "name (type) = text"}] turns the
  given ML expression @{text "text"} of type
  @{ML_text "theory ->"}~@{text "type"}~@{ML_text "-> term"} into an
  ML function of type
  @{ML_text "theory ->"}~@{text "type"}~@{ML_text "-> thm"}, which is
  bound to the global identifier @{ML_text name}.

  \end{descr}
*}


section {* Proof commands *}

text {*
  Proof commands perform transitions of Isar/VM machine
  configurations, which are block-structured, consisting of a stack of
  nodes with three main components: logical proof context, current
  facts, and open goals.  Isar/VM transitions are \emph{typed}
  according to the following three different modes of operation:

  \begin{descr}

  \item [@{text "proof(prove)"}] means that a new goal has just been
  stated that is now to be \emph{proven}; the next command may refine
  it by some proof method, and enter a sub-proof to establish the
  actual result.

  \item [@{text "proof(state)"}] is like a nested theory mode: the
  context may be augmented by \emph{stating} additional assumptions,
  intermediate results etc.

  \item [@{text "proof(chain)"}] is intermediate between @{text
  "proof(state)"} and @{text "proof(prove)"}: existing facts (i.e.\
  the contents of the special ``@{fact_ref this}'' register) have been
  just picked up in order to be used when refining the goal claimed
  next.

  \end{descr}

  The proof mode indicator may be read as a verb telling the writer
  what kind of operation may be performed next.  The corresponding
  typings of proof commands restricts the shape of well-formed proof
  texts to particular command sequences.  So dynamic arrangements of
  commands eventually turn out as static texts of a certain structure.
  \Appref{ap:refcard} gives a simplified grammar of the overall
  (extensible) language emerging that way.
*}


subsection {* Markup commands \label{sec:markup-prf} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "sect"} & : & \isartrans{proof}{proof} \\
    @{command_def "subsect"} & : & \isartrans{proof}{proof} \\
    @{command_def "subsubsect"} & : & \isartrans{proof}{proof} \\
    @{command_def "txt"} & : & \isartrans{proof}{proof} \\
    @{command_def "txt_raw"} & : & \isartrans{proof}{proof} \\
  \end{matharray}

  These markup commands for proof mode closely correspond to the ones
  of theory mode (see \S\ref{sec:markup-thy}).

  \begin{rail}
    ('sect' | 'subsect' | 'subsubsect' | 'txt' | 'txt\_raw') text
    ;
  \end{rail}
*}


subsection {* Context elements \label{sec:proof-context} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "fix"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "assume"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "presume"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "def"} & : & \isartrans{proof(state)}{proof(state)} \\
  \end{matharray}

  The logical proof context consists of fixed variables and
  assumptions.  The former closely correspond to Skolem constants, or
  meta-level universal quantification as provided by the Isabelle/Pure
  logical framework.  Introducing some \emph{arbitrary, but fixed}
  variable via ``@{command "fix"}~@{text x}'' results in a local value
  that may be used in the subsequent proof as any other variable or
  constant.  Furthermore, any result @{text "\<turnstile> \<phi>[x]"} exported from
  the context will be universally closed wrt.\ @{text x} at the
  outermost level: @{text "\<turnstile> \<And>x. \<phi>[x]"} (this is expressed in normal
  form using Isabelle's meta-variables).

  Similarly, introducing some assumption @{text \<chi>} has two effects.
  On the one hand, a local theorem is created that may be used as a
  fact in subsequent proof steps.  On the other hand, any result
  @{text "\<chi> \<turnstile> \<phi>"} exported from the context becomes conditional wrt.\
  the assumption: @{text "\<turnstile> \<chi> \<Longrightarrow> \<phi>"}.  Thus, solving an enclosing goal
  using such a result would basically introduce a new subgoal stemming
  from the assumption.  How this situation is handled depends on the
  version of assumption command used: while @{command "assume"}
  insists on solving the subgoal by unification with some premise of
  the goal, @{command "presume"} leaves the subgoal unchanged in order
  to be proved later by the user.

  Local definitions, introduced by ``@{command "def"}~@{text "x \<equiv>
  t"}'', are achieved by combining ``@{command "fix"}~@{text x}'' with
  another version of assumption that causes any hypothetical equation
  @{text "x \<equiv> t"} to be eliminated by the reflexivity rule.  Thus,
  exporting some result @{text "x \<equiv> t \<turnstile> \<phi>[x]"} yields @{text "\<turnstile>
  \<phi>[t]"}.

  \begin{rail}
    'fix' (vars + 'and')
    ;
    ('assume' | 'presume') (props + 'and')
    ;
    'def' (def + 'and')
    ;
    def: thmdecl? \\ name ('==' | equiv) term termpat?
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "fix"}~@{text x}] introduces a local variable
  @{text x} that is \emph{arbitrary, but fixed.}
  
  \item [@{command "assume"}~@{text "a: \<phi>"} and @{command
  "presume"}~@{text "a: \<phi>"}] introduce a local fact @{text "\<phi> \<turnstile> \<phi>"} by
  assumption.  Subsequent results applied to an enclosing goal (e.g.\
  by @{command_ref "show"}) are handled as follows: @{command
  "assume"} expects to be able to unify with existing premises in the
  goal, while @{command "presume"} leaves @{text \<phi>} as new subgoals.
  
  Several lists of assumptions may be given (separated by
  @{keyword_ref "and"}; the resulting list of current facts consists
  of all of these concatenated.
  
  \item [@{command "def"}~@{text "x \<equiv> t"}] introduces a local
  (non-polymorphic) definition.  In results exported from the context,
  @{text x} is replaced by @{text t}.  Basically, ``@{command
  "def"}~@{text "x \<equiv> t"}'' abbreviates ``@{command "fix"}~@{text
  x}~@{command "assume"}~@{text "x \<equiv> t"}'', with the resulting
  hypothetical equation solved by reflexivity.
  
  The default name for the definitional equation is @{text x_def}.
  Several simultaneous definitions may be given at the same time.

  \end{descr}

  The special name @{fact_ref prems} refers to all assumptions of the
  current context as a list of theorems.  This feature should be used
  with great care!  It is better avoided in final proof texts.
*}


subsection {* Facts and forward chaining *}

text {*
  \begin{matharray}{rcl}
    @{command_def "note"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "then"} & : & \isartrans{proof(state)}{proof(chain)} \\
    @{command_def "from"} & : & \isartrans{proof(state)}{proof(chain)} \\
    @{command_def "with"} & : & \isartrans{proof(state)}{proof(chain)} \\
    @{command_def "using"} & : & \isartrans{proof(prove)}{proof(prove)} \\
    @{command_def "unfolding"} & : & \isartrans{proof(prove)}{proof(prove)} \\
  \end{matharray}

  New facts are established either by assumption or proof of local
  statements.  Any fact will usually be involved in further proofs,
  either as explicit arguments of proof methods, or when forward
  chaining towards the next goal via @{command "then"} (and variants);
  @{command "from"} and @{command "with"} are composite forms
  involving @{command "note"}.  The @{command "using"} elements
  augments the collection of used facts \emph{after} a goal has been
  stated.  Note that the special theorem name @{fact_ref this} refers
  to the most recently established facts, but only \emph{before}
  issuing a follow-up claim.

  \begin{rail}
    'note' (thmdef? thmrefs + 'and')
    ;
    ('from' | 'with' | 'using' | 'unfolding') (thmrefs + 'and')
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "note"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}]
  recalls existing facts @{text "b\<^sub>1, \<dots>, b\<^sub>n"}, binding
  the result as @{text a}.  Note that attributes may be involved as
  well, both on the left and right hand sides.

  \item [@{command "then"}] indicates forward chaining by the current
  facts in order to establish the goal to be claimed next.  The
  initial proof method invoked to refine that will be offered the
  facts to do ``anything appropriate'' (see also
  \secref{sec:proof-steps}).  For example, method @{method_ref rule}
  (see \secref{sec:pure-meth-att}) would typically do an elimination
  rather than an introduction.  Automatic methods usually insert the
  facts into the goal state before operation.  This provides a simple
  scheme to control relevance of facts in automated proof search.
  
  \item [@{command "from"}~@{text b}] abbreviates ``@{command
  "note"}~@{text b}~@{command "then"}''; thus @{command "then"} is
  equivalent to ``@{command "from"}~@{text this}''.
  
  \item [@{command "with"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"}]
  abbreviates ``@{command "from"}~@{text "b\<^sub>1 \<dots> b\<^sub>n \<AND>
  this"}''; thus the forward chaining is from earlier facts together
  with the current ones.
  
  \item [@{command "using"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"}] augments
  the facts being currently indicated for use by a subsequent
  refinement step (such as @{command_ref "apply"} or @{command_ref
  "proof"}).
  
  \item [@{command "unfolding"}~@{text "b\<^sub>1 \<dots> b\<^sub>n"}] is
  structurally similar to @{command "using"}, but unfolds definitional
  equations @{text "b\<^sub>1, \<dots> b\<^sub>n"} throughout the goal state
  and facts.

  \end{descr}

  Forward chaining with an empty list of theorems is the same as not
  chaining at all.  Thus ``@{command "from"}~@{text nothing}'' has no
  effect apart from entering @{text "prove(chain)"} mode, since
  @{fact_ref nothing} is bound to the empty list of theorems.

  Basic proof methods (such as @{method_ref rule}) expect multiple
  facts to be given in their proper order, corresponding to a prefix
  of the premises of the rule involved.  Note that positions may be
  easily skipped using something like @{command "from"}~@{text "_
  \<AND> a \<AND> b"}, for example.  This involves the trivial rule
  @{text "PROP \<psi> \<Longrightarrow> PROP \<psi>"}, which is bound in Isabelle/Pure as
  ``@{fact_ref "_"}'' (underscore).

  Automated methods (such as @{method simp} or @{method auto}) just
  insert any given facts before their usual operation.  Depending on
  the kind of procedure involved, the order of facts is less
  significant here.
*}


subsection {* Goal statements \label{sec:goals} *}

text {*
  \begin{matharray}{rcl}
    \isarcmd{lemma} & : & \isartrans{local{\dsh}theory}{proof(prove)} \\
    \isarcmd{theorem} & : & \isartrans{local{\dsh}theory}{proof(prove)} \\
    \isarcmd{corollary} & : & \isartrans{local{\dsh}theory}{proof(prove)} \\
    \isarcmd{have} & : & \isartrans{proof(state) ~|~ proof(chain)}{proof(prove)} \\
    \isarcmd{show} & : & \isartrans{proof(state) ~|~ proof(chain)}{proof(prove)} \\
    \isarcmd{hence} & : & \isartrans{proof(state)}{proof(prove)} \\
    \isarcmd{thus} & : & \isartrans{proof(state)}{proof(prove)} \\
    \isarcmd{print_statement}^* & : & \isarkeep{theory~|~proof} \\
  \end{matharray}

  From a theory context, proof mode is entered by an initial goal
  command such as @{command "lemma"}, @{command "theorem"}, or
  @{command "corollary"}.  Within a proof, new claims may be
  introduced locally as well; four variants are available here to
  indicate whether forward chaining of facts should be performed
  initially (via @{command_ref "then"}), and whether the final result
  is meant to solve some pending goal.

  Goals may consist of multiple statements, resulting in a list of
  facts eventually.  A pending multi-goal is internally represented as
  a meta-level conjunction (printed as @{text "&&"}), which is usually
  split into the corresponding number of sub-goals prior to an initial
  method application, via @{command_ref "proof"}
  (\secref{sec:proof-steps}) or @{command_ref "apply"}
  (\secref{sec:tactic-commands}).  The @{method_ref induct} method
  covered in \secref{sec:cases-induct} acts on multiple claims
  simultaneously.

  Claims at the theory level may be either in short or long form.  A
  short goal merely consists of several simultaneous propositions
  (often just one).  A long goal includes an explicit context
  specification for the subsequent conclusion, involving local
  parameters and assumptions.  Here the role of each part of the
  statement is explicitly marked by separate keywords (see also
  \secref{sec:locale}); the local assumptions being introduced here
  are available as @{fact_ref assms} in the proof.  Moreover, there
  are two kinds of conclusions: @{element_def "shows"} states several
  simultaneous propositions (essentially a big conjunction), while
  @{element_def "obtains"} claims several simultaneous simultaneous
  contexts of (essentially a big disjunction of eliminated parameters
  and assumptions, cf.\ \secref{sec:obtain}).

  \begin{rail}
    ('lemma' | 'theorem' | 'corollary') target? (goal | longgoal)
    ;
    ('have' | 'show' | 'hence' | 'thus') goal
    ;
    'print\_statement' modes? thmrefs
    ;
  
    goal: (props + 'and')
    ;
    longgoal: thmdecl? (contextelem *) conclusion
    ;
    conclusion: 'shows' goal | 'obtains' (parname? case + '|')
    ;
    case: (vars + 'and') 'where' (props + 'and')
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "lemma"}~@{text "a: \<phi>"}] enters proof mode with
  @{text \<phi>} as main goal, eventually resulting in some fact @{text "\<turnstile>
  \<phi>"} to be put back into the target context.  An additional
  \railnonterm{context} specification may build up an initial proof
  context for the subsequent claim; this includes local definitions
  and syntax as well, see the definition of @{syntax contextelem} in
  \secref{sec:locale}.
  
  \item [@{command "theorem"}~@{text "a: \<phi>"} and @{command
  "corollary"}~@{text "a: \<phi>"}] are essentially the same as @{command
  "lemma"}~@{text "a: \<phi>"}, but the facts are internally marked as
  being of a different kind.  This discrimination acts like a formal
  comment.
  
  \item [@{command "have"}~@{text "a: \<phi>"}] claims a local goal,
  eventually resulting in a fact within the current logical context.
  This operation is completely independent of any pending sub-goals of
  an enclosing goal statements, so @{command "have"} may be freely
  used for experimental exploration of potential results within a
  proof body.
  
  \item [@{command "show"}~@{text "a: \<phi>"}] is like @{command
  "have"}~@{text "a: \<phi>"} plus a second stage to refine some pending
  sub-goal for each one of the finished result, after having been
  exported into the corresponding context (at the head of the
  sub-proof of this @{command "show"} command).
  
  To accommodate interactive debugging, resulting rules are printed
  before being applied internally.  Even more, interactive execution
  of @{command "show"} predicts potential failure and displays the
  resulting error as a warning beforehand.  Watch out for the
  following message:

  %FIXME proper antiquitation
  \begin{ttbox}
  Problem! Local statement will fail to solve any pending goal
  \end{ttbox}
  
  \item [@{command "hence"}] abbreviates ``@{command "then"}~@{command
  "have"}'', i.e.\ claims a local goal to be proven by forward
  chaining the current facts.  Note that @{command "hence"} is also
  equivalent to ``@{command "from"}~@{text this}~@{command "have"}''.
  
  \item [@{command "thus"}] abbreviates ``@{command "then"}~@{command
  "show"}''.  Note that @{command "thus"} is also equivalent to
  ``@{command "from"}~@{text this}~@{command "show"}''.
  
  \item [@{command "print_statement"}~@{text a}] prints facts from the
  current theory or proof context in long statement form, according to
  the syntax for @{command "lemma"} given above.

  \end{descr}

  Any goal statement causes some term abbreviations (such as
  @{variable_ref "?thesis"}) to be bound automatically, see also
  \secref{sec:term-abbrev}.  Furthermore, the local context of a
  (non-atomic) goal is provided via the @{case_ref rule_context} case.

  The optional case names of @{element_ref "obtains"} have a twofold
  meaning: (1) during the of this claim they refer to the the local
  context introductions, (2) the resulting rule is annotated
  accordingly to support symbolic case splits when used with the
  @{method_ref cases} method (cf.  \secref{sec:cases-induct}).

  \medskip

  \begin{warn}
    Isabelle/Isar suffers theory-level goal statements to contain
    \emph{unbound schematic variables}, although this does not conform
    to the aim of human-readable proof documents!  The main problem
    with schematic goals is that the actual outcome is usually hard to
    predict, depending on the behavior of the proof methods applied
    during the course of reasoning.  Note that most semi-automated
    methods heavily depend on several kinds of implicit rule
    declarations within the current theory context.  As this would
    also result in non-compositional checking of sub-proofs,
    \emph{local goals} are not allowed to be schematic at all.
    Nevertheless, schematic goals do have their use in Prolog-style
    interactive synthesis of proven results, usually by stepwise
    refinement via emulation of traditional Isabelle tactic scripts
    (see also \secref{sec:tactic-commands}).  In any case, users
    should know what they are doing.
  \end{warn}
*}


subsection {* Initial and terminal proof steps \label{sec:proof-steps} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "proof"} & : & \isartrans{proof(prove)}{proof(state)} \\
    @{command_def "qed"} & : & \isartrans{proof(state)}{proof(state) ~|~ theory} \\
    @{command_def "by"} & : & \isartrans{proof(prove)}{proof(state) ~|~ theory} \\
    @{command_def ".."} & : & \isartrans{proof(prove)}{proof(state) ~|~ theory} \\
    @{command_def "."} & : & \isartrans{proof(prove)}{proof(state) ~|~ theory} \\
    @{command_def "sorry"} & : & \isartrans{proof(prove)}{proof(state) ~|~ theory} \\
  \end{matharray}

  Arbitrary goal refinement via tactics is considered harmful.
  Structured proof composition in Isar admits proof methods to be
  invoked in two places only.

  \begin{enumerate}

  \item An \emph{initial} refinement step @{command_ref
  "proof"}~@{text "m\<^sub>1"} reduces a newly stated goal to a number
  of sub-goals that are to be solved later.  Facts are passed to
  @{text "m\<^sub>1"} for forward chaining, if so indicated by @{text
  "proof(chain)"} mode.
  
  \item A \emph{terminal} conclusion step @{command_ref "qed"}~@{text
  "m\<^sub>2"} is intended to solve remaining goals.  No facts are
  passed to @{text "m\<^sub>2"}.

  \end{enumerate}

  The only other (proper) way to affect pending goals in a proof body
  is by @{command_ref "show"}, which involves an explicit statement of
  what is to be solved eventually.  Thus we avoid the fundamental
  problem of unstructured tactic scripts that consist of numerous
  consecutive goal transformations, with invisible effects.

  \medskip As a general rule of thumb for good proof style, initial
  proof methods should either solve the goal completely, or constitute
  some well-understood reduction to new sub-goals.  Arbitrary
  automatic proof tools that are prone leave a large number of badly
  structured sub-goals are no help in continuing the proof document in
  an intelligible manner.

  Unless given explicitly by the user, the default initial method is
  ``@{method_ref rule}'', which applies a single standard elimination
  or introduction rule according to the topmost symbol involved.
  There is no separate default terminal method.  Any remaining goals
  are always solved by assumption in the very last step.

  \begin{rail}
    'proof' method?
    ;
    'qed' method?
    ;
    'by' method method?
    ;
    ('.' | '..' | 'sorry')
    ;
  \end{rail}

  \begin{descr}
  
  \item [@{command "proof"}~@{text "m\<^sub>1"}] refines the goal by
  proof method @{text "m\<^sub>1"}; facts for forward chaining are
  passed if so indicated by @{text "proof(chain)"} mode.
  
  \item [@{command "qed"}~@{text "m\<^sub>2"}] refines any remaining
  goals by proof method @{text "m\<^sub>2"} and concludes the
  sub-proof by assumption.  If the goal had been @{text "show"} (or
  @{text "thus"}), some pending sub-goal is solved as well by the rule
  resulting from the result \emph{exported} into the enclosing goal
  context.  Thus @{text "qed"} may fail for two reasons: either @{text
  "m\<^sub>2"} fails, or the resulting rule does not fit to any
  pending goal\footnote{This includes any additional ``strong''
  assumptions as introduced by @{command "assume"}.} of the enclosing
  context.  Debugging such a situation might involve temporarily
  changing @{command "show"} into @{command "have"}, or weakening the
  local context by replacing occurrences of @{command "assume"} by
  @{command "presume"}.
  
  \item [@{command "by"}~@{text "m\<^sub>1 m\<^sub>2"}] is a
  \emph{terminal proof}\index{proof!terminal}; it abbreviates
  @{command "proof"}~@{text "m\<^sub>1"}~@{text "qed"}~@{text
  "m\<^sub>2"}, but with backtracking across both methods.  Debugging
  an unsuccessful @{command "by"}~@{text "m\<^sub>1 m\<^sub>2"}
  command can be done by expanding its definition; in many cases
  @{command "proof"}~@{text "m\<^sub>1"} (or even @{text
  "apply"}~@{text "m\<^sub>1"}) is already sufficient to see the
  problem.

  \item [``@{command ".."}''] is a \emph{default
  proof}\index{proof!default}; it abbreviates @{command "by"}~@{text
  "rule"}.

  \item [``@{command "."}''] is a \emph{trivial
  proof}\index{proof!trivial}; it abbreviates @{command "by"}~@{text
  "this"}.
  
  \item [@{command "sorry"}] is a \emph{fake proof}\index{proof!fake}
  pretending to solve the pending claim without further ado.  This
  only works in interactive development, or if the @{ML
  quick_and_dirty} flag is enabled (in ML).  Facts emerging from fake
  proofs are not the real thing.  Internally, each theorem container
  is tainted by an oracle invocation, which is indicated as ``@{text
  "[!]"}'' in the printed result.
  
  The most important application of @{command "sorry"} is to support
  experimentation and top-down proof development.

  \end{descr}
*}


subsection {* Fundamental methods and attributes \label{sec:pure-meth-att} *}

text {*
  The following proof methods and attributes refer to basic logical
  operations of Isar.  Further methods and attributes are provided by
  several generic and object-logic specific tools and packages (see
  \chref{ch:gen-tools} and \chref{ch:hol}).

  \begin{matharray}{rcl}
    @{method_def "-"} & : & \isarmeth \\
    @{method_def "fact"} & : & \isarmeth \\
    @{method_def "assumption"} & : & \isarmeth \\
    @{method_def "this"} & : & \isarmeth \\
    @{method_def "rule"} & : & \isarmeth \\
    @{method_def "iprover"} & : & \isarmeth \\[0.5ex]
    @{attribute_def "intro"} & : & \isaratt \\
    @{attribute_def "elim"} & : & \isaratt \\
    @{attribute_def "dest"} & : & \isaratt \\
    @{attribute_def "rule"} & : & \isaratt \\[0.5ex]
    @{attribute_def "OF"} & : & \isaratt \\
    @{attribute_def "of"} & : & \isaratt \\
    @{attribute_def "where"} & : & \isaratt \\
  \end{matharray}

  \begin{rail}
    'fact' thmrefs?
    ;
    'rule' thmrefs?
    ;
    'iprover' ('!' ?) (rulemod *)
    ;
    rulemod: ('intro' | 'elim' | 'dest') ((('!' | () | '?') nat?) | 'del') ':' thmrefs
    ;
    ('intro' | 'elim' | 'dest') ('!' | () | '?') nat?
    ;
    'rule' 'del'
    ;
    'OF' thmrefs
    ;
    'of' insts ('concl' ':' insts)?
    ;
    'where' ((name | var | typefree | typevar) '=' (type | term) * 'and')
    ;
  \end{rail}

  \begin{descr}
  
  \item [``@{method "-"}'' (minus)] does nothing but insert the
  forward chaining facts as premises into the goal.  Note that command
  @{command_ref "proof"} without any method actually performs a single
  reduction step using the @{method_ref rule} method; thus a plain
  \emph{do-nothing} proof step would be ``@{command "proof"}~@{text
  "-"}'' rather than @{command "proof"} alone.
  
  \item [@{method "fact"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] composes
  some fact from @{text "a\<^sub>1, \<dots>, a\<^sub>n"} (or implicitly from
  the current proof context) modulo unification of schematic type and
  term variables.  The rule structure is not taken into account, i.e.\
  meta-level implication is considered atomic.  This is the same
  principle underlying literal facts (cf.\ \secref{sec:syn-att}):
  ``@{command "have"}~@{text "\<phi>"}~@{command "by"}~@{text fact}'' is
  equivalent to ``@{command "note"}~@{verbatim "`"}@{text \<phi>}@{verbatim
  "`"}'' provided that @{text "\<turnstile> \<phi>"} is an instance of some known
  @{text "\<turnstile> \<phi>"} in the proof context.
  
  \item [@{method assumption}] solves some goal by a single assumption
  step.  All given facts are guaranteed to participate in the
  refinement; this means there may be only 0 or 1 in the first place.
  Recall that @{command "qed"} (\secref{sec:proof-steps}) already
  concludes any remaining sub-goals by assumption, so structured
  proofs usually need not quote the @{method assumption} method at
  all.
  
  \item [@{method this}] applies all of the current facts directly as
  rules.  Recall that ``@{command "."}'' (dot) abbreviates ``@{command
  "by"}~@{text this}''.
  
  \item [@{method rule}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] applies some
  rule given as argument in backward manner; facts are used to reduce
  the rule before applying it to the goal.  Thus @{method rule}
  without facts is plain introduction, while with facts it becomes
  elimination.
  
  When no arguments are given, the @{method rule} method tries to pick
  appropriate rules automatically, as declared in the current context
  using the @{attribute intro}, @{attribute elim}, @{attribute dest}
  attributes (see below).  This is the default behavior of @{command
  "proof"} and ``@{command ".."}'' (double-dot) steps (see
  \secref{sec:proof-steps}).
  
  \item [@{method iprover}] performs intuitionistic proof search,
  depending on specifically declared rules from the context, or given
  as explicit arguments.  Chained facts are inserted into the goal
  before commencing proof search; ``@{method iprover}@{text "!"}'' 
  means to include the current @{fact prems} as well.
  
  Rules need to be classified as @{attribute intro}, @{attribute
  elim}, or @{attribute dest}; here the ``@{text "!"}'' indicator
  refers to ``safe'' rules, which may be applied aggressively (without
  considering back-tracking later).  Rules declared with ``@{text
  "?"}'' are ignored in proof search (the single-step @{method rule}
  method still observes these).  An explicit weight annotation may be
  given as well; otherwise the number of rule premises will be taken
  into account here.
  
  \item [@{attribute intro}, @{attribute elim}, and @{attribute dest}]
  declare introduction, elimination, and destruct rules, to be used
  with the @{method rule} and @{method iprover} methods.  Note that
  the latter will ignore rules declared with ``@{text "?"}'', while
  ``@{text "!"}''  are used most aggressively.
  
  The classical reasoner (see \secref{sec:classical}) introduces its
  own variants of these attributes; use qualified names to access the
  present versions of Isabelle/Pure, i.e.\ @{attribute "Pure.intro"}.
  
  \item [@{attribute rule}~@{text del}] undeclares introduction,
  elimination, or destruct rules.
  
  \item [@{attribute OF}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] applies some
  theorem to all of the given rules @{text "a\<^sub>1, \<dots>, a\<^sub>n"}
  (in parallel).  This corresponds to the @{ML "op MRS"} operation in
  ML, but note the reversed order.  Positions may be effectively
  skipped by including ``@{text _}'' (underscore) as argument.
  
  \item [@{attribute of}~@{text "t\<^sub>1 \<dots> t\<^sub>n"}] performs
  positional instantiation of term variables.  The terms @{text
  "t\<^sub>1, \<dots>, t\<^sub>n"} are substituted for any schematic
  variables occurring in a theorem from left to right; ``@{text
  _}'' (underscore) indicates to skip a position.  Arguments following
  a ``@{keyword "concl"}@{text ":"}'' specification refer to positions
  of the conclusion of a rule.
  
  \item [@{attribute "where"}~@{text "x\<^sub>1 = t\<^sub>1 \<AND> \<dots>
  x\<^sub>n = t\<^sub>n"}] performs named instantiation of schematic
  type and term variables occurring in a theorem.  Schematic variables
  have to be specified on the left-hand side (e.g.\ @{text "?x1.3"}).
  The question mark may be omitted if the variable name is a plain
  identifier without index.  As type instantiations are inferred from
  term instantiations, explicit type instantiations are seldom
  necessary.

  \end{descr}
*}


subsection {* Term abbreviations \label{sec:term-abbrev} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "let"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{keyword_def "is"} & : & syntax \\
  \end{matharray}

  Abbreviations may be either bound by explicit @{command
  "let"}~@{text "p \<equiv> t"} statements, or by annotating assumptions or
  goal statements with a list of patterns ``@{text "(\<IS> p\<^sub>1 \<dots>
  p\<^sub>n)"}''.  In both cases, higher-order matching is invoked to
  bind extra-logical term variables, which may be either named
  schematic variables of the form @{text ?x}, or nameless dummies
  ``@{variable _}'' (underscore). Note that in the @{command "let"}
  form the patterns occur on the left-hand side, while the @{keyword
  "is"} patterns are in postfix position.

  Polymorphism of term bindings is handled in Hindley-Milner style,
  similar to ML.  Type variables referring to local assumptions or
  open goal statements are \emph{fixed}, while those of finished
  results or bound by @{command "let"} may occur in \emph{arbitrary}
  instances later.  Even though actual polymorphism should be rarely
  used in practice, this mechanism is essential to achieve proper
  incremental type-inference, as the user proceeds to build up the
  Isar proof text from left to right.

  \medskip Term abbreviations are quite different from local
  definitions as introduced via @{command "def"} (see
  \secref{sec:proof-context}).  The latter are visible within the
  logic as actual equations, while abbreviations disappear during the
  input process just after type checking.  Also note that @{command
  "def"} does not support polymorphism.

  \begin{rail}
    'let' ((term + 'and') '=' term + 'and')
    ;  
  \end{rail}

  The syntax of @{keyword "is"} patterns follows \railnonterm{termpat}
  or \railnonterm{proppat} (see \secref{sec:term-decls}).

  \begin{descr}

  \item [@{command "let"}~@{text "p\<^sub>1 = t\<^sub>1 \<AND> \<dots>
  p\<^sub>n = t\<^sub>n"}] binds any text variables in patterns @{text
  "p\<^sub>1, \<dots>, p\<^sub>n"} by simultaneous higher-order matching
  against terms @{text "t\<^sub>1, \<dots>, t\<^sub>n"}.

  \item [@{text "(\<IS> p\<^sub>1 \<dots> p\<^sub>n)"}] resembles @{command
  "let"}, but matches @{text "p\<^sub>1, \<dots>, p\<^sub>n"} against the
  preceding statement.  Also note that @{keyword "is"} is not a
  separate command, but part of others (such as @{command "assume"},
  @{command "have"} etc.).

  \end{descr}

  Some \emph{implicit} term abbreviations\index{term abbreviations}
  for goals and facts are available as well.  For any open goal,
  @{variable_ref thesis} refers to its object-level statement,
  abstracted over any meta-level parameters (if present).  Likewise,
  @{variable_ref this} is bound for fact statements resulting from
  assumptions or finished goals.  In case @{variable this} refers to
  an object-logic statement that is an application @{text "f t"}, then
  @{text t} is bound to the special text variable ``@{variable "\<dots>"}''
  (three dots).  The canonical application of this convenience are
  calculational proofs (see \secref{sec:calculation}).
*}


subsection {* Block structure *}

text {*
  \begin{matharray}{rcl}
    @{command_def "next"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "{"} & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "}"} & : & \isartrans{proof(state)}{proof(state)} \\
  \end{matharray}

  While Isar is inherently block-structured, opening and closing
  blocks is mostly handled rather casually, with little explicit
  user-intervention.  Any local goal statement automatically opens
  \emph{two} internal blocks, which are closed again when concluding
  the sub-proof (by @{command "qed"} etc.).  Sections of different
  context within a sub-proof may be switched via @{command "next"},
  which is just a single block-close followed by block-open again.
  The effect of @{command "next"} is to reset the local proof context;
  there is no goal focus involved here!

  For slightly more advanced applications, there are explicit block
  parentheses as well.  These typically achieve a stronger forward
  style of reasoning.

  \begin{descr}

  \item [@{command "next"}] switches to a fresh block within a
  sub-proof, resetting the local context to the initial one.

  \item [@{command "{"} and @{command "}"}] explicitly open and close
  blocks.  Any current facts pass through ``@{command "{"}''
  unchanged, while ``@{command "}"}'' causes any result to be
  \emph{exported} into the enclosing context.  Thus fixed variables
  are generalized, assumptions discharged, and local definitions
  unfolded (cf.\ \secref{sec:proof-context}).  There is no difference
  of @{command "assume"} and @{command "presume"} in this mode of
  forward reasoning --- in contrast to plain backward reasoning with
  the result exported at @{command "show"} time.

  \end{descr}
*}


subsection {* Emulating tactic scripts \label{sec:tactic-commands} *}

text {*
  The Isar provides separate commands to accommodate tactic-style
  proof scripts within the same system.  While being outside the
  orthodox Isar proof language, these might come in handy for
  interactive exploration and debugging, or even actual tactical proof
  within new-style theories (to benefit from document preparation, for
  example).  See also \secref{sec:tactics} for actual tactics, that
  have been encapsulated as proof methods.  Proper proof methods may
  be used in scripts, too.

  \begin{matharray}{rcl}
    @{command_def "apply"}^* & : & \isartrans{proof(prove)}{proof(prove)} \\
    @{command_def "apply_end"}^* & : & \isartrans{proof(state)}{proof(state)} \\
    @{command_def "done"}^* & : & \isartrans{proof(prove)}{proof(state)} \\
    @{command_def "defer"}^* & : & \isartrans{proof}{proof} \\
    @{command_def "prefer"}^* & : & \isartrans{proof}{proof} \\
    @{command_def "back"}^* & : & \isartrans{proof}{proof} \\
  \end{matharray}

  \begin{rail}
    ( 'apply' | 'apply\_end' ) method
    ;
    'defer' nat?
    ;
    'prefer' nat
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "apply"}~@{text m}] applies proof method @{text m}
  in initial position, but unlike @{command "proof"} it retains
  ``@{text "proof(prove)"}'' mode.  Thus consecutive method
  applications may be given just as in tactic scripts.
  
  Facts are passed to @{text m} as indicated by the goal's
  forward-chain mode, and are \emph{consumed} afterwards.  Thus any
  further @{command "apply"} command would always work in a purely
  backward manner.
  
  \item [@{command "apply_end"}~@{text "m"}] applies proof method
  @{text m} as if in terminal position.  Basically, this simulates a
  multi-step tactic script for @{command "qed"}, but may be given
  anywhere within the proof body.
  
  No facts are passed to @{method m} here.  Furthermore, the static
  context is that of the enclosing goal (as for actual @{command
  "qed"}).  Thus the proof method may not refer to any assumptions
  introduced in the current body, for example.
  
  \item [@{command "done"}] completes a proof script, provided that
  the current goal state is solved completely.  Note that actual
  structured proof commands (e.g.\ ``@{command "."}'' or @{command
  "sorry"}) may be used to conclude proof scripts as well.

  \item [@{command "defer"}~@{text n} and @{command "prefer"}~@{text
  n}] shuffle the list of pending goals: @{command "defer"} puts off
  sub-goal @{text n} to the end of the list (@{text "n = 1"} by
  default), while @{command "prefer"} brings sub-goal @{text n} to the
  front.
  
  \item [@{command "back"}] does back-tracking over the result
  sequence of the latest proof command.  Basically, any proof command
  may return multiple results.
  
  \end{descr}

  Any proper Isar proof method may be used with tactic script commands
  such as @{command "apply"}.  A few additional emulations of actual
  tactics are provided as well; these would be never used in actual
  structured proofs, of course.
*}


subsection {* Meta-linguistic features *}

text {*
  \begin{matharray}{rcl}
    @{command_def "oops"} & : & \isartrans{proof}{theory} \\
  \end{matharray}

  The @{command "oops"} command discontinues the current proof
  attempt, while considering the partial proof text as properly
  processed.  This is conceptually quite different from ``faking''
  actual proofs via @{command_ref "sorry"} (see
  \secref{sec:proof-steps}): @{command "oops"} does not observe the
  proof structure at all, but goes back right to the theory level.
  Furthermore, @{command "oops"} does not produce any result theorem
  --- there is no intended claim to be able to complete the proof
  anyhow.

  A typical application of @{command "oops"} is to explain Isar proofs
  \emph{within} the system itself, in conjunction with the document
  preparation tools of Isabelle described in \cite{isabelle-sys}.
  Thus partial or even wrong proof attempts can be discussed in a
  logically sound manner.  Note that the Isabelle {\LaTeX} macros can
  be easily adapted to print something like ``@{text "\<dots>"}'' instead of
  the keyword ``@{command "oops"}''.

  \medskip The @{command "oops"} command is undo-able, unlike
  @{command_ref "kill"} (see \secref{sec:history}).  The effect is to
  get back to the theory just before the opening of the proof.
*}


section {* Other commands *}

subsection {* Diagnostics *}

text {*
  \begin{matharray}{rcl}
    \isarcmd{pr}^* & : & \isarkeep{\cdot} \\
    \isarcmd{thm}^* & : & \isarkeep{theory~|~proof} \\
    \isarcmd{term}^* & : & \isarkeep{theory~|~proof} \\
    \isarcmd{prop}^* & : & \isarkeep{theory~|~proof} \\
    \isarcmd{typ}^* & : & \isarkeep{theory~|~proof} \\
    \isarcmd{prf}^* & : & \isarkeep{theory~|~proof} \\
    \isarcmd{full_prf}^* & : & \isarkeep{theory~|~proof} \\
  \end{matharray}

  These diagnostic commands assist interactive development.  Note that
  @{command undo} does not apply here, the theory or proof
  configuration is not changed.

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

  \begin{descr}

  \item [@{command "pr"}~@{text "goals, prems"}] prints the current
  proof state (if present), including the proof context, current facts
  and goals.  The optional limit arguments affect the number of goals
  and premises to be displayed, which is initially 10 for both.
  Omitting limit values leaves the current setting unchanged.

  \item [@{command "thm"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}] retrieves
  theorems from the current theory or proof context.  Note that any
  attributes included in the theorem specifications are applied to a
  temporary context derived from the current theory or proof; the
  result is discarded, i.e.\ attributes involved in @{text "a\<^sub>1,
  \<dots>, a\<^sub>n"} do not have any permanent effect.

  \item [@{command "term"}~@{text t} and @{command "prop"}~@{text \<phi>}]
  read, type-check and print terms or propositions according to the
  current theory or proof context; the inferred type of @{text t} is
  output as well.  Note that these commands are also useful in
  inspecting the current environment of term abbreviations.

  \item [@{command "typ"}~@{text \<tau>}] reads and prints types of the
  meta-logic according to the current theory or proof context.

  \item [@{command "prf"}] displays the (compact) proof term of the
  current proof state (if present), or of the given theorems. Note
  that this requires proof terms to be switched on for the current
  object logic (see the ``Proof terms'' section of the Isabelle
  reference manual for information on how to do this).

  \item [@{command "full_prf"}] is like @{command "prf"}, but displays
  the full proof term, i.e.\ also displays information omitted in the
  compact proof term, which is denoted by ``@{text _}'' placeholders
  there.

  \end{descr}

  All of the diagnostic commands above admit a list of @{text modes}
  to be specified, which is appended to the current print mode (see
  also \cite{isabelle-ref}).  Thus the output behavior may be modified
  according particular print mode features.  For example, @{command
  "pr"}~@{text "(latex xsymbols symbols)"} would print the current
  proof state with mathematical symbols and special characters
  represented in {\LaTeX} source, according to the Isabelle style
  \cite{isabelle-sys}.

  Note that antiquotations (cf.\ \secref{sec:antiq}) provide a more
  systematic way to include formal items into the printed text
  document.
*}


subsection {* Inspecting the context *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_commands"}^* & : & \isarkeep{\cdot} \\
    @{command_def "print_theory"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_syntax"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_methods"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_attributes"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_theorems"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "find_theorems"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "thms_deps"}^* & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_facts"}^* & : & \isarkeep{proof} \\
    @{command_def "print_binds"}^* & : & \isarkeep{proof} \\
  \end{matharray}

  \begin{rail}
    'print\_theory' ( '!'?)
    ;

    'find\_theorems' (('(' (nat)? ('with\_dups')? ')')?) (criterion *)
    ;
    criterion: ('-'?) ('name' ':' nameref | 'intro' | 'elim' | 'dest' |
      'simp' ':' term | term)
    ;
    'thm\_deps' thmrefs
    ;
  \end{rail}

  These commands print certain parts of the theory and proof context.
  Note that there are some further ones available, such as for the set
  of rules declared for simplifications.

  \begin{descr}
  
  \item [@{command "print_commands"}] prints Isabelle's outer theory
  syntax, including keywords and command.
  
  \item [@{command "print_theory"}] prints the main logical content of
  the theory context; the ``@{text "!"}'' option indicates extra
  verbosity.

  \item [@{command "print_syntax"}] prints the inner syntax of types
  and terms, depending on the current context.  The output can be very
  verbose, including grammar tables and syntax translation rules.  See
  \cite[\S7, \S8]{isabelle-ref} for further information on Isabelle's
  inner syntax.
  
  \item [@{command "print_methods"}] prints all proof methods
  available in the current theory context.
  
  \item [@{command "print_attributes"}] prints all attributes
  available in the current theory context.
  
  \item [@{command "print_theorems"}] prints theorems resulting from
  the last command.
  
  \item [@{command "find_theorems"}~@{text criteria}] retrieves facts
  from the theory or proof context matching all of given search
  criteria.  The criterion @{text "name: p"} selects all theorems
  whose fully qualified name matches pattern @{text p}, which may
  contain ``@{text "*"}'' wildcards.  The criteria @{text intro},
  @{text elim}, and @{text dest} select theorems that match the
  current goal as introduction, elimination or destruction rules,
  respectively.  The criterion @{text "simp: t"} selects all rewrite
  rules whose left-hand side matches the given term.  The criterion
  term @{text t} selects all theorems that contain the pattern @{text
  t} -- as usual, patterns may contain occurrences of the dummy
  ``@{text _}'', schematic variables, and type constraints.
  
  Criteria can be preceded by ``@{text "-"}'' to select theorems that
  do \emph{not} match. Note that giving the empty list of criteria
  yields \emph{all} currently known facts.  An optional limit for the
  number of printed facts may be given; the default is 40.  By
  default, duplicates are removed from the search result. Use
  @{keyword "with_dups"} to display duplicates.
  
  \item [@{command "thm_deps"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}]
  visualizes dependencies of facts, using Isabelle's graph browser
  tool (see also \cite{isabelle-sys}).
  
  \item [@{command "print_facts"}] prints all local facts of the
  current context, both named and unnamed ones.
  
  \item [@{command "print_binds"}] prints all term abbreviations
  present in the context.

  \end{descr}
*}


subsection {* History commands \label{sec:history} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "undo"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
    @{command_def "redo"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
    @{command_def "kill"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
  \end{matharray}

  The Isabelle/Isar top-level maintains a two-stage history, for
  theory and proof state transformation.  Basically, any command can
  be undone using @{command "undo"}, excluding mere diagnostic
  elements.  Its effect may be revoked via @{command "redo"}, unless
  the corresponding @{command "undo"} step has crossed the beginning
  of a proof or theory.  The @{command "kill"} command aborts the
  current history node altogether, discontinuing a proof or even the
  whole theory.  This operation is \emph{not} undo-able.

  \begin{warn}
    History commands should never be used with user interfaces such as
    Proof~General \cite{proofgeneral,Aspinall:TACAS:2000}, which takes
    care of stepping forth and back itself.  Interfering by manual
    @{command "undo"}, @{command "redo"}, or even @{command "kill"}
    commands would quickly result in utter confusion.
  \end{warn}
*}


subsection {* System operations *}

text {*
  \begin{matharray}{rcl}
    @{command_def "cd"}^* & : & \isarkeep{\cdot} \\
    @{command_def "pwd"}^* & : & \isarkeep{\cdot} \\
    @{command_def "use_thy"}^* & : & \isarkeep{\cdot} \\
    @{command_def "display_drafts"}^* & : & \isarkeep{\cdot} \\
    @{command_def "print_drafts"}^* & : & \isarkeep{\cdot} \\
  \end{matharray}

  \begin{rail}
    ('cd' | 'use\_thy' | 'update\_thy') name
    ;
    ('display\_drafts' | 'print\_drafts') (name +)
    ;
  \end{rail}

  \begin{descr}

  \item [@{command "cd"}~@{text path}] changes the current directory
  of the Isabelle process.

  \item [@{command "pwd"}] prints the current working directory.

  \item [@{command "use_thy"}~@{text A}] preload theory @{text A}.
  These system commands are scarcely used when working interactively,
  since loading of theories is done automatically as required.

  \item [@{command "display_drafts"}~@{text paths} and @{command
  "print_drafts"}~@{text paths}] perform simple output of a given list
  of raw source files.  Only those symbols that do not require
  additional {\LaTeX} packages are displayed properly, everything else
  is left verbatim.

  \end{descr}
*}

end

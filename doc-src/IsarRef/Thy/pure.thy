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


section {* Other commands *}

subsection {* Diagnostics *}

text {*
  \begin{matharray}{rcl}
    @{command_def "pr"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "thm"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "term"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "prop"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "typ"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "prf"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "full_prf"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
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
    @{command_def "print_commands"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "print_theory"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_syntax"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_methods"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_attributes"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_theorems"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "find_theorems"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "thm_deps"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_facts"}@{text "\<^sup>*"} & : & \isarkeep{proof} \\
    @{command_def "print_binds"}@{text "\<^sup>*"} & : & \isarkeep{proof} \\
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
  @{text with_dups} to display duplicates.
  
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
    @{command_def "cd"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "pwd"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "use_thy"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "display_drafts"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "print_drafts"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
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

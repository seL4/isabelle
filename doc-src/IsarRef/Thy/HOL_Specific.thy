theory HOL_Specific
imports Main
begin

chapter {* Isabelle/HOL \label{ch:hol} *}

section {* Typedef axiomatization \label{sec:hol-typedef} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "typedef"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  \begin{rail}
    'typedef' altname? abstype '=' repset
    ;

    altname: '(' (name | 'open' | 'open' name) ')'
    ;
    abstype: typespecsorts mixfix?
    ;
    repset: term ('morphisms' name name)?
    ;
  \end{rail}

  \begin{description}
  
  \item @{command (HOL) "typedef"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = A"}
  axiomatizes a Gordon/HOL-style type definition in the background
  theory of the current context, depending on a non-emptiness result
  of the set @{text A} (which needs to be proven interactively).

  The raw type may not depend on parameters or assumptions of the
  context --- this is logically impossible in Isabelle/HOL --- but the
  non-emptiness property can be local, potentially resulting in
  multiple interpretations in target contexts.  Thus the established
  bijection between the representing set @{text A} and the new type
  @{text t} may semantically depend on local assumptions.
  
  By default, @{command (HOL) "typedef"} defines both a type @{text t}
  and a set (term constant) of the same name, unless an alternative
  base name is given in parentheses, or the ``@{text "(open)"}''
  declaration is used to suppress a separate constant definition
  altogether.  The injection from type to set is called @{text Rep_t},
  its inverse @{text Abs_t} --- this may be changed via an explicit
  @{keyword (HOL) "morphisms"} declaration.
  
  Theorems @{text Rep_t}, @{text Rep_t_inverse}, and @{text
  Abs_t_inverse} provide the most basic characterization as a
  corresponding injection/surjection pair (in both directions).  Rules
  @{text Rep_t_inject} and @{text Abs_t_inject} provide a slightly
  more convenient view on the injectivity part, suitable for automated
  proof tools (e.g.\ in @{attribute simp} or @{attribute iff}
  declarations).  Rules @{text Rep_t_cases}/@{text Rep_t_induct}, and
  @{text Abs_t_cases}/@{text Abs_t_induct} provide alternative views
  on surjectivity; these are already declared as set or type rules for
  the generic @{method cases} and @{method induct} methods.
  
  An alternative name for the set definition (and other derived
  entities) may be specified in parentheses; the default is to use
  @{text t} as indicated before.

  \end{description}
*}


section {* Adhoc tuples *}

text {*
  \begin{matharray}{rcl}
    @{attribute (HOL) split_format}@{text "\<^sup>*"} & : & @{text attribute} \\
  \end{matharray}

  \begin{rail}
    'split\_format' ((( name * ) + 'and') | ('(' 'complete' ')'))
    ;
  \end{rail}

  \begin{description}
  
  \item @{attribute (HOL) split_format}~@{text "p\<^sub>1 \<dots> p\<^sub>m \<AND> \<dots>
  \<AND> q\<^sub>1 \<dots> q\<^sub>n"} puts expressions of low-level tuple types into
  canonical form as specified by the arguments given; the @{text i}-th
  collection of arguments refers to occurrences in premise @{text i}
  of the rule.  The ``@{text "(complete)"}'' option causes \emph{all}
  arguments in function applications to be represented canonically
  according to their tuple type structure.

  Note that these operations tend to invent funny names for new local
  parameters to be introduced.

  \end{description}
*}


section {* Records \label{sec:hol-record} *}

text {*
  In principle, records merely generalize the concept of tuples, where
  components may be addressed by labels instead of just position.  The
  logical infrastructure of records in Isabelle/HOL is slightly more
  advanced, though, supporting truly extensible record schemes.  This
  admits operations that are polymorphic with respect to record
  extension, yielding ``object-oriented'' effects like (single)
  inheritance.  See also \cite{NaraschewskiW-TPHOLs98} for more
  details on object-oriented verification and record subtyping in HOL.
*}


subsection {* Basic concepts *}

text {*
  Isabelle/HOL supports both \emph{fixed} and \emph{schematic} records
  at the level of terms and types.  The notation is as follows:

  \begin{center}
  \begin{tabular}{l|l|l}
    & record terms & record types \\ \hline
    fixed & @{text "\<lparr>x = a, y = b\<rparr>"} & @{text "\<lparr>x :: A, y :: B\<rparr>"} \\
    schematic & @{text "\<lparr>x = a, y = b, \<dots> = m\<rparr>"} &
      @{text "\<lparr>x :: A, y :: B, \<dots> :: M\<rparr>"} \\
  \end{tabular}
  \end{center}

  \noindent The ASCII representation of @{text "\<lparr>x = a\<rparr>"} is @{text
  "(| x = a |)"}.

  A fixed record @{text "\<lparr>x = a, y = b\<rparr>"} has field @{text x} of value
  @{text a} and field @{text y} of value @{text b}.  The corresponding
  type is @{text "\<lparr>x :: A, y :: B\<rparr>"}, assuming that @{text "a :: A"}
  and @{text "b :: B"}.

  A record scheme like @{text "\<lparr>x = a, y = b, \<dots> = m\<rparr>"} contains fields
  @{text x} and @{text y} as before, but also possibly further fields
  as indicated by the ``@{text "\<dots>"}'' notation (which is actually part
  of the syntax).  The improper field ``@{text "\<dots>"}'' of a record
  scheme is called the \emph{more part}.  Logically it is just a free
  variable, which is occasionally referred to as ``row variable'' in
  the literature.  The more part of a record scheme may be
  instantiated by zero or more further components.  For example, the
  previous scheme may get instantiated to @{text "\<lparr>x = a, y = b, z =
  c, \<dots> = m'\<rparr>"}, where @{text m'} refers to a different more part.
  Fixed records are special instances of record schemes, where
  ``@{text "\<dots>"}'' is properly terminated by the @{text "() :: unit"}
  element.  In fact, @{text "\<lparr>x = a, y = b\<rparr>"} is just an abbreviation
  for @{text "\<lparr>x = a, y = b, \<dots> = ()\<rparr>"}.
  
  \medskip Two key observations make extensible records in a simply
  typed language like HOL work out:

  \begin{enumerate}

  \item the more part is internalized, as a free term or type
  variable,

  \item field names are externalized, they cannot be accessed within
  the logic as first-class values.

  \end{enumerate}

  \medskip In Isabelle/HOL record types have to be defined explicitly,
  fixing their field names and types, and their (optional) parent
  record.  Afterwards, records may be formed using above syntax, while
  obeying the canonical order of fields as given by their declaration.
  The record package provides several standard operations like
  selectors and updates.  The common setup for various generic proof
  tools enable succinct reasoning patterns.  See also the Isabelle/HOL
  tutorial \cite{isabelle-hol-book} for further instructions on using
  records in practice.
*}


subsection {* Record specifications *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "record"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'record' typespecsorts '=' (type '+')? (constdecl +)
    ;
  \end{rail}

  \begin{description}

  \item @{command (HOL) "record"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t = \<tau> + c\<^sub>1 :: \<sigma>\<^sub>1
  \<dots> c\<^sub>n :: \<sigma>\<^sub>n"} defines extensible record type @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"},
  derived from the optional parent record @{text "\<tau>"} by adding new
  field components @{text "c\<^sub>i :: \<sigma>\<^sub>i"} etc.

  The type variables of @{text "\<tau>"} and @{text "\<sigma>\<^sub>i"} need to be
  covered by the (distinct) parameters @{text "\<alpha>\<^sub>1, \<dots>,
  \<alpha>\<^sub>m"}.  Type constructor @{text t} has to be new, while @{text
  \<tau>} needs to specify an instance of an existing record type.  At
  least one new field @{text "c\<^sub>i"} has to be specified.
  Basically, field names need to belong to a unique record.  This is
  not a real restriction in practice, since fields are qualified by
  the record name internally.

  The parent record specification @{text \<tau>} is optional; if omitted
  @{text t} becomes a root record.  The hierarchy of all records
  declared within a theory context forms a forest structure, i.e.\ a
  set of trees starting with a root record each.  There is no way to
  merge multiple parent records!

  For convenience, @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"} is made a
  type abbreviation for the fixed record type @{text "\<lparr>c\<^sub>1 ::
  \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n\<rparr>"}, likewise is @{text
  "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m, \<zeta>) t_scheme"} made an abbreviation for
  @{text "\<lparr>c\<^sub>1 :: \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n, \<dots> ::
  \<zeta>\<rparr>"}.

  \end{description}
*}


subsection {* Record operations *}

text {*
  Any record definition of the form presented above produces certain
  standard operations.  Selectors and updates are provided for any
  field, including the improper one ``@{text more}''.  There are also
  cumulative record constructor functions.  To simplify the
  presentation below, we assume for now that @{text "(\<alpha>\<^sub>1, \<dots>,
  \<alpha>\<^sub>m) t"} is a root record with fields @{text "c\<^sub>1 ::
  \<sigma>\<^sub>1, \<dots>, c\<^sub>n :: \<sigma>\<^sub>n"}.

  \medskip \textbf{Selectors} and \textbf{updates} are available for
  any field (including ``@{text more}''):

  \begin{matharray}{lll}
    @{text "c\<^sub>i"} & @{text "::"} & @{text "\<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<sigma>\<^sub>i"} \\
    @{text "c\<^sub>i_update"} & @{text "::"} & @{text "\<sigma>\<^sub>i \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
  \end{matharray}

  There is special syntax for application of updates: @{text "r\<lparr>x :=
  a\<rparr>"} abbreviates term @{text "x_update a r"}.  Further notation for
  repeated updates is also available: @{text "r\<lparr>x := a\<rparr>\<lparr>y := b\<rparr>\<lparr>z :=
  c\<rparr>"} may be written @{text "r\<lparr>x := a, y := b, z := c\<rparr>"}.  Note that
  because of postfix notation the order of fields shown here is
  reverse than in the actual term.  Since repeated updates are just
  function applications, fields may be freely permuted in @{text "\<lparr>x
  := a, y := b, z := c\<rparr>"}, as far as logical equality is concerned.
  Thus commutativity of independent updates can be proven within the
  logic for any two fields, but not as a general theorem.

  \medskip The \textbf{make} operation provides a cumulative record
  constructor function:

  \begin{matharray}{lll}
    @{text "t.make"} & @{text "::"} & @{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{matharray}

  \medskip We now reconsider the case of non-root records, which are
  derived of some parent.  In general, the latter may depend on
  another parent as well, resulting in a list of \emph{ancestor
  records}.  Appending the lists of fields of all ancestors results in
  a certain field prefix.  The record package automatically takes care
  of this by lifting operations over this context of ancestor fields.
  Assuming that @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>m) t"} has ancestor
  fields @{text "b\<^sub>1 :: \<rho>\<^sub>1, \<dots>, b\<^sub>k :: \<rho>\<^sub>k"},
  the above record operations will get the following types:

  \medskip
  \begin{tabular}{lll}
    @{text "c\<^sub>i"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<sigma>\<^sub>i"} \\
    @{text "c\<^sub>i_update"} & @{text "::"} & @{text "\<sigma>\<^sub>i \<Rightarrow> 
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow>
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
    @{text "t.make"} & @{text "::"} & @{text "\<rho>\<^sub>1 \<Rightarrow> \<dots> \<rho>\<^sub>k \<Rightarrow> \<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow>
      \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{tabular}
  \medskip

  \noindent Some further operations address the extension aspect of a
  derived record scheme specifically: @{text "t.fields"} produces a
  record fragment consisting of exactly the new fields introduced here
  (the result may serve as a more part elsewhere); @{text "t.extend"}
  takes a fixed record and adds a given more part; @{text
  "t.truncate"} restricts a record scheme to a fixed record.

  \medskip
  \begin{tabular}{lll}
    @{text "t.fields"} & @{text "::"} & @{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<sigma>\<^sub>n \<Rightarrow> \<lparr>\<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
    @{text "t.extend"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr> \<Rightarrow>
      \<zeta> \<Rightarrow> \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr>"} \\
    @{text "t.truncate"} & @{text "::"} & @{text "\<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>, \<dots> :: \<zeta>\<rparr> \<Rightarrow> \<lparr>\<^vec>b :: \<^vec>\<rho>, \<^vec>c :: \<^vec>\<sigma>\<rparr>"} \\
  \end{tabular}
  \medskip

  \noindent Note that @{text "t.make"} and @{text "t.fields"} coincide
  for root records.
*}


subsection {* Derived rules and proof tools *}

text {*
  The record package proves several results internally, declaring
  these facts to appropriate proof tools.  This enables users to
  reason about record structures quite conveniently.  Assume that
  @{text t} is a record type as specified above.

  \begin{enumerate}
  
  \item Standard conversions for selectors or updates applied to
  record constructor terms are made part of the default Simplifier
  context; thus proofs by reduction of basic operations merely require
  the @{method simp} method without further arguments.  These rules
  are available as @{text "t.simps"}, too.
  
  \item Selectors applied to updated records are automatically reduced
  by an internal simplification procedure, which is also part of the
  standard Simplifier setup.

  \item Inject equations of a form analogous to @{prop "(x, y) = (x',
  y') \<equiv> x = x' \<and> y = y'"} are declared to the Simplifier and Classical
  Reasoner as @{attribute iff} rules.  These rules are available as
  @{text "t.iffs"}.

  \item The introduction rule for record equality analogous to @{text
  "x r = x r' \<Longrightarrow> y r = y r' \<dots> \<Longrightarrow> r = r'"} is declared to the Simplifier,
  and as the basic rule context as ``@{attribute intro}@{text "?"}''.
  The rule is called @{text "t.equality"}.

  \item Representations of arbitrary record expressions as canonical
  constructor terms are provided both in @{method cases} and @{method
  induct} format (cf.\ the generic proof methods of the same name,
  \secref{sec:cases-induct}).  Several variations are available, for
  fixed records, record schemes, more parts etc.
  
  The generic proof methods are sufficiently smart to pick the most
  sensible rule according to the type of the indicated record
  expression: users just need to apply something like ``@{text "(cases
  r)"}'' to a certain proof problem.

  \item The derived record operations @{text "t.make"}, @{text
  "t.fields"}, @{text "t.extend"}, @{text "t.truncate"} are \emph{not}
  treated automatically, but usually need to be expanded by hand,
  using the collective fact @{text "t.defs"}.

  \end{enumerate}
*}


section {* Datatypes \label{sec:hol-datatype} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "datatype"} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def (HOL) "rep_datatype"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  \begin{rail}
    'datatype' (dtspec + 'and')
    ;
    'rep\_datatype' ('(' (name +) ')')? (term +)
    ;

    dtspec: parname? typespec mixfix? '=' (cons + '|')
    ;
    cons: name ( type * ) mixfix?
  \end{rail}

  \begin{description}

  \item @{command (HOL) "datatype"} defines inductive datatypes in
  HOL.

  \item @{command (HOL) "rep_datatype"} represents existing types as
  inductive ones, generating the standard infrastructure of derived
  concepts (primitive recursion etc.).

  \end{description}

  The induction and exhaustion theorems generated provide case names
  according to the constructors involved, while parameters are named
  after the types (see also \secref{sec:cases-induct}).

  See \cite{isabelle-HOL} for more details on datatypes, but beware of
  the old-style theory syntax being used there!  Apart from proper
  proof methods for case-analysis and induction, there are also
  emulations of ML tactics @{method (HOL) case_tac} and @{method (HOL)
  induct_tac} available, see \secref{sec:hol-induct-tac}; these admit
  to refer directly to the internal structure of subgoals (including
  internally bound parameters).
*}


section {* Recursive functions \label{sec:recursion} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "primrec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "fun"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "function"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "termination"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  \begin{rail}
    'primrec' target? fixes 'where' equations
    ;
    equations: (thmdecl? prop + '|')
    ;
    ('fun' | 'function') target? functionopts? fixes 'where' clauses
    ;
    clauses: (thmdecl? prop ('(' 'otherwise' ')')? + '|')
    ;
    functionopts: '(' (('sequential' | 'domintros' | 'tailrec' | 'default' term) + ',') ')'
    ;
    'termination' ( term )?
  \end{rail}

  \begin{description}

  \item @{command (HOL) "primrec"} defines primitive recursive
  functions over datatypes, see also \cite{isabelle-HOL}.

  \item @{command (HOL) "function"} defines functions by general
  wellfounded recursion. A detailed description with examples can be
  found in \cite{isabelle-function}. The function is specified by a
  set of (possibly conditional) recursive equations with arbitrary
  pattern matching. The command generates proof obligations for the
  completeness and the compatibility of patterns.

  The defined function is considered partial, and the resulting
  simplification rules (named @{text "f.psimps"}) and induction rule
  (named @{text "f.pinduct"}) are guarded by a generated domain
  predicate @{text "f_dom"}. The @{command (HOL) "termination"}
  command can then be used to establish that the function is total.

  \item @{command (HOL) "fun"} is a shorthand notation for ``@{command
  (HOL) "function"}~@{text "(sequential)"}, followed by automated
  proof attempts regarding pattern matching and termination.  See
  \cite{isabelle-function} for further details.

  \item @{command (HOL) "termination"}~@{text f} commences a
  termination proof for the previously defined function @{text f}.  If
  this is omitted, the command refers to the most recent function
  definition.  After the proof is closed, the recursive equations and
  the induction principle is established.

  \end{description}

  Recursive definitions introduced by the @{command (HOL) "function"}
  command accommodate
  reasoning by induction (cf.\ \secref{sec:cases-induct}): rule @{text
  "c.induct"} (where @{text c} is the name of the function definition)
  refers to a specific induction rule, with parameters named according
  to the user-specified equations. Cases are numbered (starting from 1).

  For @{command (HOL) "primrec"}, the induction principle coincides
  with structural recursion on the datatype the recursion is carried
  out.

  The equations provided by these packages may be referred later as
  theorem list @{text "f.simps"}, where @{text f} is the (collective)
  name of the functions defined.  Individual equations may be named
  explicitly as well.

  The @{command (HOL) "function"} command accepts the following
  options.

  \begin{description}

  \item @{text sequential} enables a preprocessor which disambiguates
  overlapping patterns by making them mutually disjoint.  Earlier
  equations take precedence over later ones.  This allows to give the
  specification in a format very similar to functional programming.
  Note that the resulting simplification and induction rules
  correspond to the transformed specification, not the one given
  originally. This usually means that each equation given by the user
  may result in several theorems.  Also note that this automatic
  transformation only works for ML-style datatype patterns.

  \item @{text domintros} enables the automated generation of
  introduction rules for the domain predicate. While mostly not
  needed, they can be helpful in some proofs about partial functions.

  \item @{text tailrec} generates the unconstrained recursive
  equations even without a termination proof, provided that the
  function is tail-recursive. This currently only works

  \item @{text "default d"} allows to specify a default value for a
  (partial) function, which will ensure that @{text "f x = d x"}
  whenever @{text "x \<notin> f_dom"}.

  \end{description}
*}


subsection {* Proof methods related to recursive definitions *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) pat_completeness} & : & @{text method} \\
    @{method_def (HOL) relation} & : & @{text method} \\
    @{method_def (HOL) lexicographic_order} & : & @{text method} \\
    @{method_def (HOL) size_change} & : & @{text method} \\
  \end{matharray}

  \begin{rail}
    'relation' term
    ;
    'lexicographic\_order' ( clasimpmod * )
    ;
    'size\_change' ( orders ( clasimpmod * ) )
    ;
    orders: ( 'max' | 'min' | 'ms' ) *
  \end{rail}

  \begin{description}

  \item @{method (HOL) pat_completeness} is a specialized method to
  solve goals regarding the completeness of pattern matching, as
  required by the @{command (HOL) "function"} package (cf.\
  \cite{isabelle-function}).

  \item @{method (HOL) relation}~@{text R} introduces a termination
  proof using the relation @{text R}.  The resulting proof state will
  contain goals expressing that @{text R} is wellfounded, and that the
  arguments of recursive calls decrease with respect to @{text R}.
  Usually, this method is used as the initial proof step of manual
  termination proofs.

  \item @{method (HOL) "lexicographic_order"} attempts a fully
  automated termination proof by searching for a lexicographic
  combination of size measures on the arguments of the function. The
  method accepts the same arguments as the @{method auto} method,
  which it uses internally to prove local descents.  The same context
  modifiers as for @{method auto} are accepted, see
  \secref{sec:clasimp}.

  In case of failure, extensive information is printed, which can help
  to analyse the situation (cf.\ \cite{isabelle-function}).

  \item @{method (HOL) "size_change"} also works on termination goals,
  using a variation of the size-change principle, together with a
  graph decomposition technique (see \cite{krauss_phd} for details).
  Three kinds of orders are used internally: @{text max}, @{text min},
  and @{text ms} (multiset), which is only available when the theory
  @{text Multiset} is loaded. When no order kinds are given, they are
  tried in order. The search for a termination proof uses SAT solving
  internally.

 For local descent proofs, the same context modifiers as for @{method
  auto} are accepted, see \secref{sec:clasimp}.

  \end{description}
*}


subsection {* Old-style recursive function definitions (TFL) *}

text {*
  The old TFL commands @{command (HOL) "recdef"} and @{command (HOL)
  "recdef_tc"} for defining recursive are mostly obsolete; @{command
  (HOL) "function"} or @{command (HOL) "fun"} should be used instead.

  \begin{matharray}{rcl}
    @{command_def (HOL) "recdef"} & : & @{text "theory \<rightarrow> theory)"} \\
    @{command_def (HOL) "recdef_tc"}@{text "\<^sup>*"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  \begin{rail}
    'recdef' ('(' 'permissive' ')')? \\ name term (prop +) hints?
    ;
    recdeftc thmdecl? tc
    ;
    hints: '(' 'hints' ( recdefmod * ) ')'
    ;
    recdefmod: (('recdef\_simp' | 'recdef\_cong' | 'recdef\_wf') (() | 'add' | 'del') ':' thmrefs) | clasimpmod
    ;
    tc: nameref ('(' nat ')')?
    ;
  \end{rail}

  \begin{description}
  
  \item @{command (HOL) "recdef"} defines general well-founded
  recursive functions (using the TFL package), see also
  \cite{isabelle-HOL}.  The ``@{text "(permissive)"}'' option tells
  TFL to recover from failed proof attempts, returning unfinished
  results.  The @{text recdef_simp}, @{text recdef_cong}, and @{text
  recdef_wf} hints refer to auxiliary rules to be used in the internal
  automated proof process of TFL.  Additional @{syntax clasimpmod}
  declarations (cf.\ \secref{sec:clasimp}) may be given to tune the
  context of the Simplifier (cf.\ \secref{sec:simplifier}) and
  Classical reasoner (cf.\ \secref{sec:classical}).
  
  \item @{command (HOL) "recdef_tc"}~@{text "c (i)"} recommences the
  proof for leftover termination condition number @{text i} (default
  1) as generated by a @{command (HOL) "recdef"} definition of
  constant @{text c}.
  
  Note that in most cases, @{command (HOL) "recdef"} is able to finish
  its internal proofs without manual intervention.

  \end{description}

  \medskip Hints for @{command (HOL) "recdef"} may be also declared
  globally, using the following attributes.

  \begin{matharray}{rcl}
    @{attribute_def (HOL) recdef_simp} & : & @{text attribute} \\
    @{attribute_def (HOL) recdef_cong} & : & @{text attribute} \\
    @{attribute_def (HOL) recdef_wf} & : & @{text attribute} \\
  \end{matharray}

  \begin{rail}
    ('recdef\_simp' | 'recdef\_cong' | 'recdef\_wf') (() | 'add' | 'del')
    ;
  \end{rail}
*}


section {* Inductive and coinductive definitions \label{sec:hol-inductive} *}

text {*
  An \textbf{inductive definition} specifies the least predicate (or
  set) @{text R} closed under given rules: applying a rule to elements
  of @{text R} yields a result within @{text R}.  For example, a
  structural operational semantics is an inductive definition of an
  evaluation relation.

  Dually, a \textbf{coinductive definition} specifies the greatest
  predicate~/ set @{text R} that is consistent with given rules: every
  element of @{text R} can be seen as arising by applying a rule to
  elements of @{text R}.  An important example is using bisimulation
  relations to formalise equivalence of processes and infinite data
  structures.

  \medskip The HOL package is related to the ZF one, which is
  described in a separate paper,\footnote{It appeared in CADE
  \cite{paulson-CADE}; a longer version is distributed with Isabelle.}
  which you should refer to in case of difficulties.  The package is
  simpler than that of ZF thanks to implicit type-checking in HOL.
  The types of the (co)inductive predicates (or sets) determine the
  domain of the fixedpoint definition, and the package does not have
  to use inference rules for type-checking.

  \begin{matharray}{rcl}
    @{command_def (HOL) "inductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "inductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def (HOL) mono} & : & @{text attribute} \\
  \end{matharray}

  \begin{rail}
    ('inductive' | 'inductive\_set' | 'coinductive' | 'coinductive\_set') target? fixes ('for' fixes)? \\
    ('where' clauses)? ('monos' thmrefs)?
    ;
    clauses: (thmdecl? prop + '|')
    ;
    'mono' (() | 'add' | 'del')
    ;
  \end{rail}

  \begin{description}

  \item @{command (HOL) "inductive"} and @{command (HOL)
  "coinductive"} define (co)inductive predicates from the
  introduction rules given in the @{keyword "where"} part.  The
  optional @{keyword "for"} part contains a list of parameters of the
  (co)inductive predicates that remain fixed throughout the
  definition.  The optional @{keyword "monos"} section contains
  \emph{monotonicity theorems}, which are required for each operator
  applied to a recursive set in the introduction rules.  There
  \emph{must} be a theorem of the form @{text "A \<le> B \<Longrightarrow> M A \<le> M B"},
  for each premise @{text "M R\<^sub>i t"} in an introduction rule!

  \item @{command (HOL) "inductive_set"} and @{command (HOL)
  "coinductive_set"} are wrappers for to the previous commands,
  allowing the definition of (co)inductive sets.

  \item @{attribute (HOL) mono} declares monotonicity rules.  These
  rule are involved in the automated monotonicity proof of @{command
  (HOL) "inductive"}.

  \end{description}
*}


subsection {* Derived rules *}

text {*
  Each (co)inductive definition @{text R} adds definitions to the
  theory and also proves some theorems:

  \begin{description}

  \item @{text R.intros} is the list of introduction rules as proven
  theorems, for the recursive predicates (or sets).  The rules are
  also available individually, using the names given them in the
  theory file;

  \item @{text R.cases} is the case analysis (or elimination) rule;

  \item @{text R.induct} or @{text R.coinduct} is the (co)induction
  rule.

  \end{description}

  When several predicates @{text "R\<^sub>1, \<dots>, R\<^sub>n"} are
  defined simultaneously, the list of introduction rules is called
  @{text "R\<^sub>1_\<dots>_R\<^sub>n.intros"}, the case analysis rules are
  called @{text "R\<^sub>1.cases, \<dots>, R\<^sub>n.cases"}, and the list
  of mutual induction rules is called @{text
  "R\<^sub>1_\<dots>_R\<^sub>n.inducts"}.
*}


subsection {* Monotonicity theorems *}

text {*
  Each theory contains a default set of theorems that are used in
  monotonicity proofs.  New rules can be added to this set via the
  @{attribute (HOL) mono} attribute.  The HOL theory @{text Inductive}
  shows how this is done.  In general, the following monotonicity
  theorems may be added:

  \begin{itemize}

  \item Theorems of the form @{text "A \<le> B \<Longrightarrow> M A \<le> M B"}, for proving
  monotonicity of inductive definitions whose introduction rules have
  premises involving terms such as @{text "M R\<^sub>i t"}.

  \item Monotonicity theorems for logical operators, which are of the
  general form @{text "(\<dots> \<longrightarrow> \<dots>) \<Longrightarrow> \<dots> (\<dots> \<longrightarrow> \<dots>) \<Longrightarrow> \<dots> \<longrightarrow> \<dots>"}.  For example, in
  the case of the operator @{text "\<or>"}, the corresponding theorem is
  \[
  \infer{@{text "P\<^sub>1 \<or> P\<^sub>2 \<longrightarrow> Q\<^sub>1 \<or> Q\<^sub>2"}}{@{text "P\<^sub>1 \<longrightarrow> Q\<^sub>1"} & @{text "P\<^sub>2 \<longrightarrow> Q\<^sub>2"}}
  \]

  \item De Morgan style equations for reasoning about the ``polarity''
  of expressions, e.g.
  \[
  @{prop "\<not> \<not> P \<longleftrightarrow> P"} \qquad\qquad
  @{prop "\<not> (P \<and> Q) \<longleftrightarrow> \<not> P \<or> \<not> Q"}
  \]

  \item Equations for reducing complex operators to more primitive
  ones whose monotonicity can easily be proved, e.g.
  \[
  @{prop "(P \<longrightarrow> Q) \<longleftrightarrow> \<not> P \<or> Q"} \qquad\qquad
  @{prop "Ball A P \<equiv> \<forall>x. x \<in> A \<longrightarrow> P x"}
  \]

  \end{itemize}

  %FIXME: Example of an inductive definition
*}


section {* Arithmetic proof support *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) arith} & : & @{text method} \\
    @{attribute_def (HOL) arith} & : & @{text attribute} \\
    @{attribute_def (HOL) arith_split} & : & @{text attribute} \\
  \end{matharray}

  The @{method (HOL) arith} method decides linear arithmetic problems
  (on types @{text nat}, @{text int}, @{text real}).  Any current
  facts are inserted into the goal before running the procedure.

  The @{attribute (HOL) arith} attribute declares facts that are
  always supplied to the arithmetic provers implicitly.

  The @{attribute (HOL) arith_split} attribute declares case split
  rules to be expanded before @{method (HOL) arith} is invoked.

  Note that a simpler (but faster) arithmetic prover is
  already invoked by the Simplifier.
*}


section {* Intuitionistic proof search *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) iprover} & : & @{text method} \\
  \end{matharray}

  \begin{rail}
    'iprover' ( rulemod * )
    ;
  \end{rail}

  The @{method (HOL) iprover} method performs intuitionistic proof
  search, depending on specifically declared rules from the context,
  or given as explicit arguments.  Chained facts are inserted into the
  goal before commencing proof search.

  Rules need to be classified as @{attribute (Pure) intro},
  @{attribute (Pure) elim}, or @{attribute (Pure) dest}; here the
  ``@{text "!"}'' indicator refers to ``safe'' rules, which may be
  applied aggressively (without considering back-tracking later).
  Rules declared with ``@{text "?"}'' are ignored in proof search (the
  single-step @{method rule} method still observes these).  An
  explicit weight annotation may be given as well; otherwise the
  number of rule premises will be taken into account here.
*}


section {* Coherent Logic *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) "coherent"} & : & @{text method} \\
  \end{matharray}

  \begin{rail}
    'coherent' thmrefs?
    ;
  \end{rail}

  The @{method (HOL) coherent} method solves problems of
  \emph{Coherent Logic} \cite{Bezem-Coquand:2005}, which covers
  applications in confluence theory, lattice theory and projective
  geometry.  See @{"file" "~~/src/HOL/ex/Coherent.thy"} for some
  examples.
*}


section {* Checking and refuting propositions *}

text {*
  Identifying incorrect propositions usually involves evaluation of
  particular assignments and systematic counter example search.  This
  is supported by the following commands.

  \begin{matharray}{rcl}
    @{command_def (HOL) "value"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck_params"} & : & @{text "theory \<rightarrow> theory"}
  \end{matharray}

  \begin{rail}
    'value' ( ( '[' name ']' ) ? ) modes? term
    ;

    'quickcheck' ( ( '[' args ']' ) ? ) nat?
    ;

    'quickcheck_params' ( ( '[' args ']' ) ? )
    ;

    modes: '(' (name + ) ')'
    ;

    args: ( name '=' value + ',' )
    ;
  \end{rail}

  \begin{description}

  \item @{command (HOL) "value"}~@{text t} evaluates and prints a
    term; optionally @{text modes} can be specified, which are
    appended to the current print mode (see also \cite{isabelle-ref}).
    Internally, the evaluation is performed by registered evaluators,
    which are invoked sequentially until a result is returned.
    Alternatively a specific evaluator can be selected using square
    brackets; typical evaluators use the current set of code equations
    to normalize and include @{text simp} for fully symbolic evaluation
    using the simplifier, @{text nbe} for \emph{normalization by evaluation}
    and \emph{code} for code generation in SML.

  \item @{command (HOL) "quickcheck"} tests the current goal for
    counter examples using a series of arbitrary assignments for its
    free variables; by default the first subgoal is tested, an other
    can be selected explicitly using an optional goal index.
    A number of configuration options are supported for
    @{command (HOL) "quickcheck"}, notably:

    \begin{description}

      \item[size] specifies the maximum size of the search space for
        assignment values.

      \item[iterations] sets how many sets of assignments are
        generated for each particular size.

      \item[no\_assms] specifies whether assumptions in
        structured proofs should be ignored.

    \end{description}

    These option can be given within square brackets.

  \item @{command (HOL) "quickcheck_params"} changes quickcheck
    configuration options persitently.

  \end{description}
*}


section {* Unstructured case analysis and induction \label{sec:hol-induct-tac} *}

text {*
  The following tools of Isabelle/HOL support cases analysis and
  induction in unstructured tactic scripts; see also
  \secref{sec:cases-induct} for proper Isar versions of similar ideas.

  \begin{matharray}{rcl}
    @{method_def (HOL) case_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def (HOL) induct_tac}@{text "\<^sup>*"} & : & @{text method} \\
    @{method_def (HOL) ind_cases}@{text "\<^sup>*"} & : & @{text method} \\
    @{command_def (HOL) "inductive_cases"}@{text "\<^sup>*"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  \begin{rail}
    'case\_tac' goalspec? term rule?
    ;
    'induct\_tac' goalspec? (insts * 'and') rule?
    ;
    'ind\_cases' (prop +) ('for' (name +)) ?
    ;
    'inductive\_cases' (thmdecl? (prop +) + 'and')
    ;

    rule: ('rule' ':' thmref)
    ;
  \end{rail}

  \begin{description}

  \item @{method (HOL) case_tac} and @{method (HOL) induct_tac} admit
  to reason about inductive types.  Rules are selected according to
  the declarations by the @{attribute cases} and @{attribute induct}
  attributes, cf.\ \secref{sec:cases-induct}.  The @{command (HOL)
  datatype} package already takes care of this.

  These unstructured tactics feature both goal addressing and dynamic
  instantiation.  Note that named rule cases are \emph{not} provided
  as would be by the proper @{method cases} and @{method induct} proof
  methods (see \secref{sec:cases-induct}).  Unlike the @{method
  induct} method, @{method induct_tac} does not handle structured rule
  statements, only the compact object-logic conclusion of the subgoal
  being addressed.
  
  \item @{method (HOL) ind_cases} and @{command (HOL)
  "inductive_cases"} provide an interface to the internal @{ML_text
  mk_cases} operation.  Rules are simplified in an unrestricted
  forward manner.

  While @{method (HOL) ind_cases} is a proof method to apply the
  result immediately as elimination rules, @{command (HOL)
  "inductive_cases"} provides case split theorems at the theory level
  for later use.  The @{keyword "for"} argument of the @{method (HOL)
  ind_cases} method allows to specify a list of variables that should
  be generalized before applying the resulting rule.

  \end{description}
*}


section {* Executable code *}

text {*
  Isabelle/Pure provides two generic frameworks to support code
  generation from executable specifications.  Isabelle/HOL
  instantiates these mechanisms in a way that is amenable to end-user
  applications.

  \medskip One framework generates code from functional programs
  (including overloading using type classes) to SML \cite{SML}, OCaml
  \cite{OCaml} and Haskell \cite{haskell-revised-report}.
  Conceptually, code generation is split up in three steps:
  \emph{selection} of code theorems, \emph{translation} into an
  abstract executable view and \emph{serialization} to a specific
  \emph{target language}.  Inductive specifications can be executed
  using the predicate compiler which operates within HOL.
  See \cite{isabelle-codegen} for an introduction.

  \begin{matharray}{rcl}
    @{command_def (HOL) "export_code"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code} & : & @{text attribute} \\
    @{command_def (HOL) "code_abort"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_datatype"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "print_codesetup"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code_inline} & : & @{text attribute} \\
    @{attribute_def (HOL) code_post} & : & @{text attribute} \\
    @{command_def (HOL) "print_codeproc"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_thms"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "code_const"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_type"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_class"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_instance"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_reserved"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_monad"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_include"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_modulename"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
     'export\_code' ( constexpr + ) \\
       ( ( 'in' target ( 'module\_name' string ) ? \\
        ( 'file' ( string | '-' ) ) ? ( '(' args ')' ) ?) + ) ?
    ;

    const: term
    ;

    constexpr: ( const | 'name.*' | '*' )
    ;

    typeconstructor: nameref
    ;

    class: nameref
    ;

    target: 'OCaml' | 'SML' | 'Haskell'
    ;

    'code' ( 'del' | 'abstype' | 'abstract' ) ?
    ;

    'code\_abort' ( const + )
    ;

    'code\_datatype' ( const + )
    ;

    'code_inline' ( 'del' ) ?
    ;

    'code_post' ( 'del' ) ?
    ;

    'code\_thms' ( constexpr + ) ?
    ;

    'code\_deps' ( constexpr + ) ?
    ;

    'code\_const' (const + 'and') \\
      ( ( '(' target ( syntax ? + 'and' ) ')' ) + )
    ;

    'code\_type' (typeconstructor + 'and') \\
      ( ( '(' target ( syntax ? + 'and' ) ')' ) + )
    ;

    'code\_class' (class + 'and') \\
      ( ( '(' target \\ ( string ? + 'and' ) ')' ) + )
    ;

    'code\_instance' (( typeconstructor '::' class ) + 'and') \\
      ( ( '(' target ( '-' ? + 'and' ) ')' ) + )
    ;

    'code\_reserved' target ( string + )
    ;

    'code\_monad' const const target
    ;

    'code\_include' target ( string ( string | '-') )
    ;

    'code\_modulename' target ( ( string string ) + )
    ;

    syntax: string | ( 'infix' | 'infixl' | 'infixr' ) nat string
    ;

  \end{rail}

  \begin{description}

  \item @{command (HOL) "export_code"} generates code for a given list
  of constants in the specified target language(s).  If no serialization
  instruction is given, only abstract code is generated internally.

  Constants may be specified by giving them literally, referring to
  all executable contants within a certain theory by giving @{text
  "name.*"}, or referring to \emph{all} executable constants currently
  available by giving @{text "*"}.

  By default, for each involved theory one corresponding name space
  module is generated.  Alternativly, a module name may be specified
  after the @{keyword "module_name"} keyword; then \emph{all} code is
  placed in this module.

  For \emph{SML} and \emph{OCaml}, the file specification refers to a
  single file; for \emph{Haskell}, it refers to a whole directory,
  where code is generated in multiple files reflecting the module
  hierarchy.  Omitting the file specification denotes standard
  output.

  Serializers take an optional list of arguments in parentheses.  For
  \emph{SML} and \emph{OCaml}, ``@{text no_signatures}`` omits
  explicit module signatures.
  
  For \emph{Haskell} a module name prefix may be given using the ``@{text
  "root:"}'' argument; ``@{text string_classes}'' adds a ``@{verbatim
  "deriving (Read, Show)"}'' clause to each appropriate datatype
  declaration.

  \item @{attribute (HOL) code} explicitly selects (or with option
  ``@{text "del"}'' deselects) a code equation for code generation.
  Usually packages introducing code equations provide a reasonable
  default setup for selection.  Variants @{text "code abstype"} and
  @{text "code abstract"} declare abstract datatype certificates or
  code equations on abstract datatype representations respectively.

  \item @{command (HOL) "code_abort"} declares constants which are not
  required to have a definition by means of code equations; if
  needed these are implemented by program abort instead.

  \item @{command (HOL) "code_datatype"} specifies a constructor set
  for a logical type.

  \item @{command (HOL) "print_codesetup"} gives an overview on
  selected code equations and code generator datatypes.

  \item @{attribute (HOL) code_inline} declares (or with
  option ``@{text "del"}'' removes) inlining theorems which are
  applied as rewrite rules to any code equation during
  preprocessing.

  \item @{attribute (HOL) code_post} declares (or with
  option ``@{text "del"}'' removes) theorems which are
  applied as rewrite rules to any result of an evaluation.

  \item @{command (HOL) "print_codeproc"} prints the setup
  of the code generator preprocessor.

  \item @{command (HOL) "code_thms"} prints a list of theorems
  representing the corresponding program containing all given
  constants after preprocessing.

  \item @{command (HOL) "code_deps"} visualizes dependencies of
  theorems representing the corresponding program containing all given
  constants after preprocessing.

  \item @{command (HOL) "code_const"} associates a list of constants
  with target-specific serializations; omitting a serialization
  deletes an existing serialization.

  \item @{command (HOL) "code_type"} associates a list of type
  constructors with target-specific serializations; omitting a
  serialization deletes an existing serialization.

  \item @{command (HOL) "code_class"} associates a list of classes
  with target-specific class names; omitting a serialization deletes
  an existing serialization.  This applies only to \emph{Haskell}.

  \item @{command (HOL) "code_instance"} declares a list of type
  constructor / class instance relations as ``already present'' for a
  given target.  Omitting a ``@{text "-"}'' deletes an existing
  ``already present'' declaration.  This applies only to
  \emph{Haskell}.

  \item @{command (HOL) "code_reserved"} declares a list of names as
  reserved for a given target, preventing it to be shadowed by any
  generated code.

  \item @{command (HOL) "code_monad"} provides an auxiliary mechanism
  to generate monadic code for Haskell.

  \item @{command (HOL) "code_include"} adds arbitrary named content
  (``include'') to generated code.  A ``@{text "-"}'' as last argument
  will remove an already added ``include''.

  \item @{command (HOL) "code_modulename"} declares aliasings from one
  module name onto another.

  \end{description}

  The other framework generates code from both functional and relational
  programs to SML.  See \cite{isabelle-HOL} for further information
  (this actually covers the new-style theory format as well).

  \begin{matharray}{rcl}
    @{command_def (HOL) "code_module"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_library"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "consts_code"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "types_code"} & : & @{text "theory \<rightarrow> theory"} \\  
    @{attribute_def (HOL) code} & : & @{text attribute} \\
  \end{matharray}

  \begin{rail}
  ( 'code\_module' | 'code\_library' ) modespec ? name ? \\
    ( 'file' name ) ? ( 'imports' ( name + ) ) ? \\
    'contains' ( ( name '=' term ) + | term + )
  ;

  modespec: '(' ( name * ) ')'
  ;

  'consts\_code' (codespec +)
  ;

  codespec: const template attachment ?
  ;

  'types\_code' (tycodespec +)
  ;

  tycodespec: name template attachment ?
  ;

  const: term
  ;

  template: '(' string ')'
  ;

  attachment: 'attach' modespec ? verblbrace text verbrbrace
  ;

  'code' (name)?
  ;
  \end{rail}

*}


section {* Definition by specification \label{sec:hol-specification} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "specification"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "ax_specification"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  \begin{rail}
  ('specification' | 'ax\_specification') '(' (decl +) ')' \\ (thmdecl? prop +)
  ;
  decl: ((name ':')? term '(' 'overloaded' ')'?)
  \end{rail}

  \begin{description}

  \item @{command (HOL) "specification"}~@{text "decls \<phi>"} sets up a
  goal stating the existence of terms with the properties specified to
  hold for the constants given in @{text decls}.  After finishing the
  proof, the theory will be augmented with definitions for the given
  constants, as well as with theorems stating the properties for these
  constants.

  \item @{command (HOL) "ax_specification"}~@{text "decls \<phi>"} sets up
  a goal stating the existence of terms with the properties specified
  to hold for the constants given in @{text decls}.  After finishing
  the proof, the theory will be augmented with axioms expressing the
  properties given in the first place.

  \item @{text decl} declares a constant to be defined by the
  specification given.  The definition for the constant @{text c} is
  bound to the name @{text c_def} unless a theorem name is given in
  the declaration.  Overloaded constants should be declared as such.

  \end{description}

  Whether to use @{command (HOL) "specification"} or @{command (HOL)
  "ax_specification"} is to some extent a matter of style.  @{command
  (HOL) "specification"} introduces no new axioms, and so by
  construction cannot introduce inconsistencies, whereas @{command
  (HOL) "ax_specification"} does introduce axioms, but only after the
  user has explicitly proven it to be safe.  A practical issue must be
  considered, though: After introducing two constants with the same
  properties using @{command (HOL) "specification"}, one can prove
  that the two constants are, in fact, equal.  If this might be a
  problem, one should use @{command (HOL) "ax_specification"}.
*}

end

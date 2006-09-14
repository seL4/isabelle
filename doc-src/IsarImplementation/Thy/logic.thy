
(* $Id$ *)

theory logic imports base begin

chapter {* Primitive logic \label{ch:logic} *}

text {*
  The logical foundations of Isabelle/Isar are that of the Pure logic,
  which has been introduced as a natural-deduction framework in
  \cite{paulson700}.  This is essentially the same logic as ``@{text
  "\<lambda>HOL"}'' in the more abstract setting of Pure Type Systems (PTS)
  \cite{Barendregt-Geuvers:2001}, although there are some key
  differences in the specific treatment of simple types in
  Isabelle/Pure.

  Following type-theoretic parlance, the Pure logic consists of three
  levels of @{text "\<lambda>"}-calculus with corresponding arrows: @{text
  "\<Rightarrow>"} for syntactic function space (terms depending on terms), @{text
  "\<And>"} for universal quantification (proofs depending on terms), and
  @{text "\<Longrightarrow>"} for implication (proofs depending on proofs).

  Derivations are relative to a logical theory, which declares type
  constructors, constants, and axioms.  Theory declarations support
  schematic polymorphism, which is strictly speaking outside the
  logic.\footnote{This is the deeper logical reason, why the theory
  context @{text "\<Theta>"} is separate from the proof context @{text "\<Gamma>"}
  of the core calculus.}
*}


section {* Types \label{sec:types} *}

text {*
  The language of types is an uninterpreted order-sorted first-order
  algebra; types are qualified by ordered type classes.

  \medskip A \emph{type class} is an abstract syntactic entity
  declared in the theory context.  The \emph{subclass relation} @{text
  "c\<^isub>1 \<subseteq> c\<^isub>2"} is specified by stating an acyclic
  generating relation; the transitive closure is maintained
  internally.  The resulting relation is an ordering: reflexive,
  transitive, and antisymmetric.

  A \emph{sort} is a list of type classes written as @{text "s =
  {c\<^isub>1, \<dots>, c\<^isub>m}"}, which represents symbolic
  intersection.  Notationally, the curly braces are omitted for
  singleton intersections, i.e.\ any class @{text "c"} may be read as
  a sort @{text "{c}"}.  The ordering on type classes is extended to
  sorts according to the meaning of intersections: @{text
  "{c\<^isub>1, \<dots> c\<^isub>m} \<subseteq> {d\<^isub>1, \<dots>, d\<^isub>n}"} iff
  @{text "\<forall>j. \<exists>i. c\<^isub>i \<subseteq> d\<^isub>j"}.  The empty intersection
  @{text "{}"} refers to the universal sort, which is the largest
  element wrt.\ the sort order.  The intersections of all (finitely
  many) classes declared in the current theory are the minimal
  elements wrt.\ the sort order.

  \medskip A \emph{fixed type variable} is a pair of a basic name
  (starting with a @{text "'"} character) and a sort constraint, e.g.\
  @{text "('a, s)"} which is usually printed as @{text "\<alpha>\<^isub>s"}.
  A \emph{schematic type variable} is a pair of an indexname and a
  sort constraint, e.g.\ @{text "(('a, 0), s)"} which is usually
  printed as @{text "?\<alpha>\<^isub>s"}.

  Note that \emph{all} syntactic components contribute to the identity
  of type variables, including the sort constraint.  The core logic
  handles type variables with the same name but different sorts as
  different, although some outer layers of the system make it hard to
  produce anything like this.

  A \emph{type constructor} @{text "\<kappa>"} is a @{text "k"}-ary operator
  on types declared in the theory.  Type constructor application is
  written postfix as @{text "(\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>k)\<kappa>"}.  For
  @{text "k = 0"} the argument tuple is omitted, e.g.\ @{text "prop"}
  instead of @{text "()prop"}.  For @{text "k = 1"} the parentheses
  are omitted, e.g.\ @{text "\<alpha> list"} instead of @{text "(\<alpha>)list"}.
  Further notation is provided for specific constructors, notably the
  right-associative infix @{text "\<alpha> \<Rightarrow> \<beta>"} instead of @{text "(\<alpha>,
  \<beta>)fun"}.
  
  A \emph{type} is defined inductively over type variables and type
  constructors as follows: @{text "\<tau> = \<alpha>\<^isub>s | ?\<alpha>\<^isub>s |
  (\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>k)k"}.

  A \emph{type abbreviation} is a syntactic definition @{text
  "(\<^vec>\<alpha>)\<kappa> = \<tau>"} of an arbitrary type expression @{text "\<tau>"} over
  variables @{text "\<^vec>\<alpha>"}.  Type abbreviations appear as type
  constructors in the syntax, but are expanded before entering the
  logical core.

  A \emph{type arity} declares the image behavior of a type
  constructor wrt.\ the algebra of sorts: @{text "\<kappa> :: (s\<^isub>1, \<dots>,
  s\<^isub>k)s"} means that @{text "(\<tau>\<^isub>1, \<dots>, \<tau>\<^isub>k)\<kappa>"} is
  of sort @{text "s"} if every argument type @{text "\<tau>\<^isub>i"} is
  of sort @{text "s\<^isub>i"}.  Arity declarations are implicitly
  completed, i.e.\ @{text "\<kappa> :: (\<^vec>s)c"} entails @{text "\<kappa> ::
  (\<^vec>s)c'"} for any @{text "c' \<supseteq> c"}.

  \medskip The sort algebra is always maintained as \emph{coregular},
  which means that type arities are consistent with the subclass
  relation: for any type constructor @{text "\<kappa>"}, and classes @{text
  "c\<^isub>1 \<subseteq> c\<^isub>2"}, and arities @{text "\<kappa> ::
  (\<^vec>s\<^isub>1)c\<^isub>1"} and @{text "\<kappa> ::
  (\<^vec>s\<^isub>2)c\<^isub>2"} holds @{text "\<^vec>s\<^isub>1 \<subseteq>
  \<^vec>s\<^isub>2"} component-wise.

  The key property of a coregular order-sorted algebra is that sort
  constraints can be solved in a most general fashion: for each type
  constructor @{text "\<kappa>"} and sort @{text "s"} there is a most general
  vector of argument sorts @{text "(s\<^isub>1, \<dots>, s\<^isub>k)"} such
  that a type scheme @{text "(\<alpha>\<^bsub>s\<^isub>1\<^esub>, \<dots>,
  \<alpha>\<^bsub>s\<^isub>k\<^esub>)\<kappa>"} is of sort @{text "s"}.
  Consequently, unification on the algebra of types has most general
  solutions (modulo equivalence of sorts).  This means that
  type-inference will produce primary types as expected
  \cite{nipkow-prehofer}.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type class} \\
  @{index_ML_type sort} \\
  @{index_ML_type arity} \\
  @{index_ML_type typ} \\
  @{index_ML map_atyps: "(typ -> typ) -> typ -> typ"} \\
  @{index_ML fold_atyps: "(typ -> 'a -> 'a) -> typ -> 'a -> 'a"} \\
  @{index_ML Sign.subsort: "theory -> sort * sort -> bool"} \\
  @{index_ML Sign.of_sort: "theory -> typ * sort -> bool"} \\
  @{index_ML Sign.add_types: "(string * int * mixfix) list -> theory -> theory"} \\
  @{index_ML Sign.add_tyabbrs_i: "
  (string * string list * typ * mixfix) list -> theory -> theory"} \\
  @{index_ML Sign.primitive_class: "string * class list -> theory -> theory"} \\
  @{index_ML Sign.primitive_classrel: "class * class -> theory -> theory"} \\
  @{index_ML Sign.primitive_arity: "arity -> theory -> theory"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type class} represents type classes; this is an alias for
  @{ML_type string}.

  \item @{ML_type sort} represents sorts; this is an alias for
  @{ML_type "class list"}.

  \item @{ML_type arity} represents type arities; this is an alias for
  triples of the form @{text "(\<kappa>, \<^vec>s, s)"} for @{text "\<kappa> ::
  (\<^vec>s)s"} described above.

  \item @{ML_type typ} represents types; this is a datatype with
  constructors @{ML TFree}, @{ML TVar}, @{ML Type}.

  \item @{ML map_atyps}~@{text "f \<tau>"} applies the mapping @{text "f"}
  to all atomic types (@{ML TFree}, @{ML TVar}) occurring in @{text
  "\<tau>"}.

  \item @{ML fold_atyps}~@{text "f \<tau>"} iterates the operation @{text
  "f"} over all occurrences of atomic types (@{ML TFree}, @{ML TVar})
  in @{text "\<tau>"}; the type structure is traversed from left to right.

  \item @{ML Sign.subsort}~@{text "thy (s\<^isub>1, s\<^isub>2)"}
  tests the subsort relation @{text "s\<^isub>1 \<subseteq> s\<^isub>2"}.

  \item @{ML Sign.of_sort}~@{text "thy (\<tau>, s)"} tests whether type
  @{text "\<tau>"} is of sort @{text "s"}.

  \item @{ML Sign.add_types}~@{text "[(\<kappa>, k, mx), \<dots>]"} declares a new
  type constructors @{text "\<kappa>"} with @{text "k"} arguments and
  optional mixfix syntax.

  \item @{ML Sign.add_tyabbrs_i}~@{text "[(\<kappa>, \<^vec>\<alpha>, \<tau>, mx), \<dots>]"}
  defines a new type abbreviation @{text "(\<^vec>\<alpha>)\<kappa> = \<tau>"} with
  optional mixfix syntax.

  \item @{ML Sign.primitive_class}~@{text "(c, [c\<^isub>1, \<dots>,
  c\<^isub>n])"} declares a new class @{text "c"}, together with class
  relations @{text "c \<subseteq> c\<^isub>i"}, for @{text "i = 1, \<dots>, n"}.

  \item @{ML Sign.primitive_classrel}~@{text "(c\<^isub>1,
  c\<^isub>2)"} declares class relation @{text "c\<^isub>1 \<subseteq>
  c\<^isub>2"}.

  \item @{ML Sign.primitive_arity}~@{text "(\<kappa>, \<^vec>s, s)"} declares
  the arity @{text "\<kappa> :: (\<^vec>s)s"}.

  \end{description}
*}



section {* Terms \label{sec:terms} *}

text {*
  \glossary{Term}{FIXME}

  The language of terms is that of simply-typed @{text "\<lambda>"}-calculus
  with de-Bruijn indices for bound variables (cf.\ \cite{debruijn72}
  or \cite{paulson-ml2}), with the types being determined determined
  by the corresponding binders.  In contrast, free variables and
  constants are have an explicit name and type in each occurrence.

  \medskip A \emph{bound variable} is a natural number @{text "b"},
  which accounts for the number of intermediate binders between the
  variable occurrence in the body and its binding position.  For
  example, the de-Bruijn term @{text "\<lambda>\<^isub>\<tau>. \<lambda>\<^isub>\<tau>. 1 + 0"}
  would correspond to @{text "\<lambda>x\<^isub>\<tau>. \<lambda>y\<^isub>\<tau>. x + y"} in a
  named representation.  Note that a bound variable may be represented
  by different de-Bruijn indices at different occurrences, depending
  on the nesting of abstractions.

  A \emph{loose variables} is a bound variable that is outside the
  scope of local binders.  The types (and names) for loose variables
  can be managed as a separate context, that is maintained inside-out
  like a stack of hypothetical binders.  The core logic only operates
  on closed terms, without any loose variables.

  A \emph{fixed variable} is a pair of a basic name and a type, e.g.\
  @{text "(x, \<tau>)"} which is usually printed @{text "x\<^isub>\<tau>"}.  A
  \emph{schematic variable} is a pair of an indexname and a type,
  e.g.\ @{text "((x, 0), \<tau>)"} which is usually printed as @{text
  "?x\<^isub>\<tau>"}.

  \medskip A \emph{constant} is a pair of a basic name and a type,
  e.g.\ @{text "(c, \<tau>)"} which is usually printed as @{text
  "c\<^isub>\<tau>"}.  Constants are declared in the context as polymorphic
  families @{text "c :: \<sigma>"}, meaning that valid all substitution
  instances @{text "c\<^isub>\<tau>"} for @{text "\<tau> = \<sigma>\<vartheta>"} are valid.

  The vector of \emph{type arguments} of constant @{text "c\<^isub>\<tau>"}
  wrt.\ the declaration @{text "c :: \<sigma>"} is defined as the codomain of
  the matcher @{text "\<vartheta> = {?\<alpha>\<^isub>1 \<mapsto> \<tau>\<^isub>1, \<dots>,
  ?\<alpha>\<^isub>n \<mapsto> \<tau>\<^isub>n}"} presented in canonical order @{text
  "(\<tau>\<^isub>1, \<dots>, \<tau>\<^isub>n)"}.  Within a given theory context,
  there is a one-to-one correspondence between any constant @{text
  "c\<^isub>\<tau>"} and the application @{text "c(\<tau>\<^isub>1, \<dots>,
  \<tau>\<^isub>n)"} of its type arguments.  For example, with @{text "plus
  :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"}, the instance @{text "plus\<^bsub>nat \<Rightarrow> nat \<Rightarrow>
  nat\<^esub>"} corresponds to @{text "plus(nat)"}.

  Constant declarations @{text "c :: \<sigma>"} may contain sort constraints
  for type variables in @{text "\<sigma>"}.  These are observed by
  type-inference as expected, but \emph{ignored} by the core logic.
  This means the primitive logic is able to reason with instances of
  polymorphic constants that the user-level type-checker would reject
  due to violation of type class restrictions.

  \medskip A \emph{term} is defined inductively over variables and
  constants, with abstraction and application as follows: @{text "t =
  b | x\<^isub>\<tau> | ?x\<^isub>\<tau> | c\<^isub>\<tau> | \<lambda>\<^isub>\<tau>. t |
  t\<^isub>1 t\<^isub>2"}.  Parsing and printing takes care of
  converting between an external representation with named bound
  variables.  Subsequently, we shall use the latter notation instead
  of internal de-Bruijn representation.

  The inductive relation @{text "t :: \<tau>"} assigns a (unique) type to a
  term according to the structure of atomic terms, abstractions, and
  applicatins:
  \[
  \infer{@{text "a\<^isub>\<tau> :: \<tau>"}}{}
  \qquad
  \infer{@{text "(\<lambda>x\<^sub>\<tau>. t) :: \<tau> \<Rightarrow> \<sigma>"}}{@{text "t :: \<sigma>"}}
  \qquad
  \infer{@{text "t u :: \<sigma>"}}{@{text "t :: \<tau> \<Rightarrow> \<sigma>"} & @{text "u :: \<tau>"}}
  \]
  A \emph{well-typed term} is a term that can be typed according to these rules.

  Typing information can be omitted: type-inference is able to
  reconstruct the most general type of a raw term, while assigning
  most general types to all of its variables and constants.
  Type-inference depends on a context of type constraints for fixed
  variables, and declarations for polymorphic constants.

  The identity of atomic terms consists both of the name and the type
  component.  This means that different variables @{text
  "x\<^bsub>\<tau>\<^isub>1\<^esub>"} and @{text
  "x\<^bsub>\<tau>\<^isub>2\<^esub>"} may become the same after type
  instantiation.  Some outer layers of the system make it hard to
  produce variables of the same name, but different types.  In
  particular, type-inference always demands ``consistent'' type
  constraints for free variables.  In contrast, mixed instances of
  polymorphic constants occur frequently.

  \medskip The \emph{hidden polymorphism} of a term @{text "t :: \<sigma>"}
  is the set of type variables occurring in @{text "t"}, but not in
  @{text "\<sigma>"}.  This means that the term implicitly depends on type
  arguments that are not accounted in result type, i.e.\ there are
  different type instances @{text "t\<vartheta> :: \<sigma>"} and @{text
  "t\<vartheta>' :: \<sigma>"} with the same type.  This slightly
  pathological situation demands special care.

  \medskip A \emph{term abbreviation} is a syntactic definition @{text
  "c\<^isub>\<sigma> \<equiv> t"} of a closed term @{text "t"} of type @{text "\<sigma>"},
  without any hidden polymorphism.  A term abbreviation looks like a
  constant in the syntax, but is fully expanded before entering the
  logical core.  Abbreviations are usually reverted when printing
  terms, using the collective @{text "t \<rightarrow> c\<^isub>\<sigma>"} as rules for
  higher-order rewriting.

  \medskip Canonical operations on @{text "\<lambda>"}-terms include @{text
  "\<alpha>\<beta>\<eta>"}-conversion: @{text "\<alpha>"}-conversion refers to capture-free
  renaming of bound variables; @{text "\<beta>"}-conversion contracts an
  abstraction applied to an argument term, substituting the argument
  in the body: @{text "(\<lambda>x. b)a"} becomes @{text "b[a/x]"}; @{text
  "\<eta>"}-conversion contracts vacuous application-abstraction: @{text
  "\<lambda>x. f x"} becomes @{text "f"}, provided that the bound variable
  does not occur in @{text "f"}.

  Terms are normally treated modulo @{text "\<alpha>"}-conversion, which is
  implicit in the de-Bruijn representation.  Names for bound variables
  in abstractions are maintained separately as (meaningless) comments,
  mostly for parsing and printing.  Full @{text "\<alpha>\<beta>\<eta>"}-conversion is
  commonplace in various higher operations (\secref{sec:rules}) that
  are based on higher-order unification and matching.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type term} \\
  @{index_ML "op aconv": "term * term -> bool"} \\
  @{index_ML map_term_types: "(typ -> typ) -> term -> term"} \\  %FIXME rename map_types
  @{index_ML fold_types: "(typ -> 'a -> 'a) -> term -> 'a -> 'a"} \\
  @{index_ML map_aterms: "(term -> term) -> term -> term"} \\
  @{index_ML fold_aterms: "(term -> 'a -> 'a) -> term -> 'a -> 'a"} \\
  @{index_ML fastype_of: "term -> typ"} \\
  @{index_ML lambda: "term -> term -> term"} \\
  @{index_ML betapply: "term * term -> term"} \\
  @{index_ML Sign.add_consts_i: "(string * typ * mixfix) list -> theory -> theory"} \\
  @{index_ML Sign.add_abbrevs: "string * bool ->
  ((string * mixfix) * term) list -> theory -> theory"} \\
  @{index_ML Sign.const_typargs: "theory -> string * typ -> typ list"} \\
  @{index_ML Sign.const_instance: "theory -> string * typ list -> typ"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type term} represents de-Bruijn terms, with comments in
  abstractions, and explicitly named free variables and constants;
  this is a datatype with constructors @{ML Bound}, @{ML Free}, @{ML
  Var}, @{ML Const}, @{ML Abs}, @{ML "op $"}.

  \item @{text "t"}~@{ML aconv}~@{text "u"} checks @{text
  "\<alpha>"}-equivalence of two terms.  This is the basic equality relation
  on type @{ML_type term}; raw datatype equality should only be used
  for operations related to parsing or printing!

  \item @{ML map_term_types}~@{text "f t"} applies the mapping @{text
  "f"} to all types occurring in @{text "t"}.

  \item @{ML fold_types}~@{text "f t"} iterates the operation @{text
  "f"} over all occurrences of types in @{text "t"}; the term
  structure is traversed from left to right.

  \item @{ML map_aterms}~@{text "f t"} applies the mapping @{text "f"}
  to all atomic terms (@{ML Bound}, @{ML Free}, @{ML Var}, @{ML
  Const}) occurring in @{text "t"}.

  \item @{ML fold_aterms}~@{text "f t"} iterates the operation @{text
  "f"} over all occurrences of atomic terms (@{ML Bound}, @{ML Free},
  @{ML Var}, @{ML Const}) in @{text "t"}; the term structure is
  traversed from left to right.

  \item @{ML fastype_of}~@{text "t"} determines the type of a
  well-typed term.  This operation is relatively slow, despite the
  omission of any sanity checks.

  \item @{ML lambda}~@{text "a b"} produces an abstraction @{text
  "\<lambda>a. b"}, where occurrences of the atomic term @{text "a"} in the
  body @{text "b"} are replaced by bound variables.

  \item @{ML betapply}~@{text "(t, u)"} produces an application @{text
  "t u"}, with topmost @{text "\<beta>"}-conversion if @{text "t"} is an
  abstraction.

  \item @{ML Sign.add_consts_i}~@{text "[(c, \<sigma>, mx), \<dots>]"} declares a
  new constant @{text "c :: \<sigma>"} with optional mixfix syntax.

  \item @{ML Sign.add_abbrevs}~@{text "print_mode [((c, t), mx), \<dots>]"}
  declares a new term abbreviation @{text "c \<equiv> t"} with optional
  mixfix syntax.

  \item @{ML Sign.const_typargs}~@{text "thy (c, \<tau>)"} and @{ML
  Sign.const_instance}~@{text "thy (c, [\<tau>\<^isub>1, \<dots>, \<tau>\<^isub>n])"}
  convert between the representations of polymorphic constants: the
  full type instance vs.\ the compact type arguments form (depending
  on the most general declaration given in the context).

  \end{description}
*}


section {* Theorems \label{sec:thms} *}

text {*
  \glossary{Proposition}{FIXME A \seeglossary{term} of
  \seeglossary{type} @{text "prop"}.  Internally, there is nothing
  special about propositions apart from their type, but the concrete
  syntax enforces a clear distinction.  Propositions are structured
  via implication @{text "A \<Longrightarrow> B"} or universal quantification @{text
  "\<And>x. B x"} --- anything else is considered atomic.  The canonical
  form for propositions is that of a \seeglossary{Hereditary Harrop
  Formula}. FIXME}

  \glossary{Theorem}{A proven proposition within a certain theory and
  proof context, formally @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}; both contexts are
  rarely spelled out explicitly.  Theorems are usually normalized
  according to the \seeglossary{HHF} format. FIXME}

  \glossary{Fact}{Sometimes used interchangeably for
  \seeglossary{theorem}.  Strictly speaking, a list of theorems,
  essentially an extra-logical conjunction.  Facts emerge either as
  local assumptions, or as results of local goal statements --- both
  may be simultaneous, hence the list representation. FIXME}

  \glossary{Schematic variable}{FIXME}

  \glossary{Fixed variable}{A variable that is bound within a certain
  proof context; an arbitrary-but-fixed entity within a portion of
  proof text. FIXME}

  \glossary{Free variable}{Synonymous for \seeglossary{fixed
  variable}. FIXME}

  \glossary{Bound variable}{FIXME}

  \glossary{Variable}{See \seeglossary{schematic variable},
  \seeglossary{fixed variable}, \seeglossary{bound variable}, or
  \seeglossary{type variable}.  The distinguishing feature of
  different variables is their binding scope. FIXME}

  A \emph{proposition} is a well-formed term of type @{text "prop"}, a
  \emph{theorem} is a proven proposition (depending on a context of
  hypotheses and the background theory).  Primitive inferences include
  plain natural deduction rules for the primary connectives @{text
  "\<And>"} and @{text "\<Longrightarrow>"} of the framework.  There is also a builtin
  notion of equality/equivalence @{text "\<equiv>"}.
*}

subsection {* Primitive connectives and rules *}

text {*
  The theory @{text "Pure"} contains declarations for the standard
  connectives @{text "\<And>"}, @{text "\<Longrightarrow>"}, and @{text "\<equiv>"} of the logical
  framework, see \figref{fig:pure-connectives}.  The derivability
  judgment @{text "A\<^isub>1, \<dots>, A\<^isub>n \<turnstile> B"} is defined
  inductively by the primitive inferences given in
  \figref{fig:prim-rules}, with the global restriction that hypotheses
  @{text "\<Gamma>"} may \emph{not} contain schematic variables.  The builtin
  equality is conceptually axiomatized as shown in
  \figref{fig:pure-equality}, although the implementation works
  directly with derived inference rules.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  @{text "all :: (\<alpha> \<Rightarrow> prop) \<Rightarrow> prop"} & universal quantification (binder @{text "\<And>"}) \\
  @{text "\<Longrightarrow> :: prop \<Rightarrow> prop \<Rightarrow> prop"} & implication (right associative infix) \\
  @{text "\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop"} & equality relation (infix) \\
  \end{tabular}
  \caption{Primitive connectives of Pure}\label{fig:pure-connectives}
  \end{center}
  \end{figure}

  \begin{figure}[htb]
  \begin{center}
  \[
  \infer[@{text "(axiom)"}]{@{text "\<turnstile> A"}}{@{text "A \<in> \<Theta>"}}
  \qquad
  \infer[@{text "(assume)"}]{@{text "A \<turnstile> A"}}{}
  \]
  \[
  \infer[@{text "(\<And>_intro)"}]{@{text "\<Gamma> \<turnstile> \<And>x. b[x]"}}{@{text "\<Gamma> \<turnstile> b[x]"} & @{text "x \<notin> \<Gamma>"}}
  \qquad
  \infer[@{text "(\<And>_elim)"}]{@{text "\<Gamma> \<turnstile> b[a]"}}{@{text "\<Gamma> \<turnstile> \<And>x. b[x]"}}
  \]
  \[
  \infer[@{text "(\<Longrightarrow>_intro)"}]{@{text "\<Gamma> - A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \qquad
  \infer[@{text "(\<Longrightarrow>_elim)"}]{@{text "\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile> B"}}{@{text "\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B"} & @{text "\<Gamma>\<^sub>2 \<turnstile> A"}}
  \]
  \caption{Primitive inferences of Pure}\label{fig:prim-rules}
  \end{center}
  \end{figure}

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  @{text "\<turnstile> (\<lambda>x. b[x]) a \<equiv> b[a]"} & @{text "\<beta>"}-conversion \\
  @{text "\<turnstile> x \<equiv> x"} & reflexivity \\
  @{text "\<turnstile> x \<equiv> y \<Longrightarrow> P x \<Longrightarrow> P y"} & substitution \\
  @{text "\<turnstile> (\<And>x. f x \<equiv> g x) \<Longrightarrow> f \<equiv> g"} & extensionality \\
  @{text "\<turnstile> (A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<equiv> B"} & logical equivalence \\
  \end{tabular}
  \caption{Conceptual axiomatization of @{text "\<equiv>"}}\label{fig:pure-equality}
  \end{center}
  \end{figure}

  The introduction and elimination rules for @{text "\<And>"} and @{text
  "\<Longrightarrow>"} are analogous to formation of dependently typed @{text
  "\<lambda>"}-terms representing the underlying proof objects.  Proof terms
  are irrelevant in the Pure logic, though, they may never occur
  within propositions.  The system provides a runtime option to record
  explicit proof terms for primitive inferences.  Thus all three
  levels of @{text "\<lambda>"}-calculus become explicit: @{text "\<Rightarrow>"} for
  terms, and @{text "\<And>/\<Longrightarrow>"} for proofs (cf.\
  \cite{Berghofer-Nipkow:2000:TPHOL}).

  Observe that locally fixed parameters (as in @{text "\<And>_intro"}) need
  not be recorded in the hypotheses, because the simple syntactic
  types of Pure are always inhabitable.  Typing ``assumptions'' @{text
  "x :: \<tau>"} are (implicitly) present only with occurrences of @{text
  "x\<^isub>\<tau>"} in the statement body.\footnote{This is the key
  difference ``@{text "\<lambda>HOL"}'' in the PTS framework
  \cite{Barendregt-Geuvers:2001}, where @{text "x : A"} hypotheses are
  treated explicitly for types, in the same way as propositions.}

  \medskip FIXME @{text "\<alpha>\<beta>\<eta>"}-equivalence and primitive definitions

  Since the basic representation of terms already accounts for @{text
  "\<alpha>"}-conversion, Pure equality essentially acts like @{text
  "\<alpha>\<beta>\<eta>"}-equivalence on terms, while coinciding with bi-implication.

  \medskip The axiomatization of a theory is implicitly closed by
  forming all instances of type and term variables: @{text "\<turnstile>
  A\<vartheta>"} holds for any substitution instance of an axiom
  @{text "\<turnstile> A"}.  By pushing substitution through derivations
  inductively, we get admissible @{text "generalize"} and @{text
  "instance"} rules shown in \figref{fig:subst-rules}.

  \begin{figure}[htb]
  \begin{center}
  \[
  \infer{@{text "\<Gamma> \<turnstile> B[?\<alpha>]"}}{@{text "\<Gamma> \<turnstile> B[\<alpha>]"} & @{text "\<alpha> \<notin> \<Gamma>"}}
  \quad
  \infer[\quad@{text "(generalize)"}]{@{text "\<Gamma> \<turnstile> B[?x]"}}{@{text "\<Gamma> \<turnstile> B[x]"} & @{text "x \<notin> \<Gamma>"}}
  \]
  \[
  \infer{@{text "\<Gamma> \<turnstile> B[\<tau>]"}}{@{text "\<Gamma> \<turnstile> B[?\<alpha>]"}}
  \quad
  \infer[\quad@{text "(instantiate)"}]{@{text "\<Gamma> \<turnstile> B[t]"}}{@{text "\<Gamma> \<turnstile> B[?x]"}}
  \]
  \caption{Admissible substitution rules}\label{fig:subst-rules}
  \end{center}
  \end{figure}

  Note that @{text "instantiate"} does not require an explicit
  side-condition, because @{text "\<Gamma>"} may never contain schematic
  variables.

  In principle, variables could be substituted in hypotheses as well,
  but this would disrupt monotonicity reasoning: deriving @{text
  "\<Gamma>\<vartheta> \<turnstile> B\<vartheta>"} from @{text "\<Gamma> \<turnstile> B"} is correct, but
  @{text "\<Gamma>\<vartheta> \<supseteq> \<Gamma>"} does not necessarily hold --- the result
  belongs to a different proof context.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type ctyp} \\
  @{index_ML_type cterm} \\
  @{index_ML_type thm} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type ctyp} FIXME

  \item @{ML_type cterm} FIXME

  \item @{ML_type thm} FIXME

  \end{description}
*}


subsection {* Auxiliary connectives *}

text {*
  Theory @{text "Pure"} also defines a few auxiliary connectives, see
  \figref{fig:pure-aux}.  These are normally not exposed to the user,
  but appear in internal encodings only.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  @{text "conjunction :: prop \<Rightarrow> prop \<Rightarrow> prop"} & (infix @{text "&"}) \\
  @{text "\<turnstile> A & B \<equiv> (\<And>C. (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C)"} \\[1ex]
  @{text "prop :: prop \<Rightarrow> prop"} & (prefix @{text "#"}, hidden) \\
  @{text "#A \<equiv> A"} \\[1ex]
  @{text "term :: \<alpha> \<Rightarrow> prop"} & (prefix @{text "TERM"}) \\
  @{text "term x \<equiv> (\<And>A. A \<Longrightarrow> A)"} \\[1ex]
  @{text "TYPE :: \<alpha> itself"} & (prefix @{text "TYPE"}) \\
  @{text "(unspecified)"} \\
  \end{tabular}
  \caption{Definitions of auxiliary connectives}\label{fig:pure-aux}
  \end{center}
  \end{figure}

  Derived conjunction rules include introduction @{text "A \<Longrightarrow> B \<Longrightarrow> A &
  B"}, and destructions @{text "A & B \<Longrightarrow> A"} and @{text "A & B \<Longrightarrow> B"}.
  Conjunction allows to treat simultaneous assumptions and conclusions
  uniformly.  For example, multiple claims are intermediately
  represented as explicit conjunction, but this is usually refined
  into separate sub-goals before the user continues the proof; the
  final result is projected into a list of theorems (cf.\
  \secref{sec:tactical-goals}).

  The @{text "prop"} marker (@{text "#"}) makes arbitrarily complex
  propositions appear as atomic, without changing the meaning: @{text
  "\<Gamma> \<turnstile> A"} and @{text "\<Gamma> \<turnstile> #A"} are interchangeable.  See
  \secref{sec:tactical-goals} for specific operations.

  The @{text "term"} marker turns any well-formed term into a
  derivable proposition: @{text "\<turnstile> TERM t"} holds unconditionally.
  Although this is logically vacuous, it allows to treat terms and
  proofs uniformly, similar to a type-theoretic framework.

  The @{text "TYPE"} constructor is the canonical representative of
  the unspecified type @{text "\<alpha> itself"}; it essentially injects the
  language of types into that of terms.  There is specific notation
  @{text "TYPE(\<tau>)"} for @{text "TYPE\<^bsub>\<tau>
 itself\<^esub>"}.
  Although being devoid of any particular meaning, the @{text
  "TYPE(\<tau>)"} accounts for the type @{text "\<tau>"} within the term
  language.  In particular, @{text "TYPE(\<alpha>)"} may be used as formal
  argument in primitive definitions, in order to circumvent hidden
  polymorphism (cf.\ \secref{sec:terms}).  For example, @{text "c
  TYPE(\<alpha>) \<equiv> A[\<alpha>]"} defines @{text "c :: \<alpha> itself \<Rightarrow> prop"} in terms of
  a proposition @{text "A"} that depends on an additional type
  argument, which is essentially a predicate on types.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Conjunction.intr: "thm -> thm -> thm"} \\
  @{index_ML Conjunction.elim: "thm -> thm * thm"} \\
  @{index_ML Drule.mk_term: "cterm -> thm"} \\
  @{index_ML Drule.dest_term: "thm -> cterm"} \\
  @{index_ML Logic.mk_type: "typ -> term"} \\
  @{index_ML Logic.dest_type: "term -> typ"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Rules \label{sec:rules} *}

text {*

FIXME

  A \emph{rule} is any Pure theorem in HHF normal form; there is a
  separate calculus for rule composition, which is modeled after
  Gentzen's Natural Deduction \cite{Gentzen:1935}, but allows
  rules to be nested arbitrarily, similar to \cite{extensions91}.

  Normally, all theorems accessible to the user are proper rules.
  Low-level inferences are occasional required internally, but the
  result should be always presented in canonical form.  The higher
  interfaces of Isabelle/Isar will always produce proper rules.  It is
  important to maintain this invariant in add-on applications!

  There are two main principles of rule composition: @{text
  "resolution"} (i.e.\ backchaining of rules) and @{text
  "by-assumption"} (i.e.\ closing a branch); both principles are
  combined in the variants of @{text "elim-resolution"} and @{text
  "dest-resolution"}.  Raw @{text "composition"} is occasionally
  useful as well, also it is strictly speaking outside of the proper
  rule calculus.

  Rules are treated modulo general higher-order unification, which is
  unification modulo the equational theory of @{text "\<alpha>\<beta>\<eta>"}-conversion
  on @{text "\<lambda>"}-terms.  Moreover, propositions are understood modulo
  the (derived) equivalence @{text "(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)"}.

  This means that any operations within the rule calculus may be
  subject to spontaneous @{text "\<alpha>\<beta>\<eta>"}-HHF conversions.  It is common
  practice not to contract or expand unnecessarily.  Some mechanisms
  prefer an one form, others the opposite, so there is a potential
  danger to produce some oscillation!

  Only few operations really work \emph{modulo} HHF conversion, but
  expect a normal form: quantifiers @{text "\<And>"} before implications
  @{text "\<Longrightarrow>"} at each level of nesting.

\glossary{Hereditary Harrop Formula}{The set of propositions in HHF
format is defined inductively as @{text "H = (\<And>x\<^sup>*. H\<^sup>* \<Longrightarrow>
A)"}, for variables @{text "x"} and atomic propositions @{text "A"}.
Any proposition may be put into HHF form by normalizing with the rule
@{text "(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)"}.  In Isabelle, the outermost
quantifier prefix is represented via \seeglossary{schematic
variables}, such that the top-level structure is merely that of a
\seeglossary{Horn Clause}}.

\glossary{HHF}{See \seeglossary{Hereditary Harrop Formula}.}


  \[
  \infer[@{text "(assumption)"}]{@{text "C\<vartheta>"}}
  {@{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> A \<^vec>x) \<Longrightarrow> C"} & @{text "A\<vartheta> = H\<^sub>i\<vartheta>"}~~\text{(for some~@{text i})}}
  \]


  \[
  \infer[@{text "(compose)"}]{@{text "\<^vec>A\<vartheta> \<Longrightarrow> C\<vartheta>"}}
  {@{text "\<^vec>A \<Longrightarrow> B"} & @{text "B' \<Longrightarrow> C"} & @{text "B\<vartheta> = B'\<vartheta>"}}
  \]


  \[
  \infer[@{text "(\<And>_lift)"}]{@{text "(\<And>\<^vec>x. \<^vec>A (?\<^vec>a \<^vec>x)) \<Longrightarrow> (\<And>\<^vec>x. B (?\<^vec>a \<^vec>x))"}}{@{text "\<^vec>A ?\<^vec>a \<Longrightarrow> B ?\<^vec>a"}}
  \]
  \[
  \infer[@{text "(\<Longrightarrow>_lift)"}]{@{text "(\<^vec>H \<Longrightarrow> \<^vec>A) \<Longrightarrow> (\<^vec>H \<Longrightarrow> B)"}}{@{text "\<^vec>A \<Longrightarrow> B"}}
  \]

  The @{text resolve} scheme is now acquired from @{text "\<And>_lift"},
  @{text "\<Longrightarrow>_lift"}, and @{text compose}.

  \[
  \infer[@{text "(resolution)"}]
  {@{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> \<^vec>A (?\<^vec>a \<^vec>x))\<vartheta> \<Longrightarrow> C\<vartheta>"}}
  {\begin{tabular}{l}
    @{text "\<^vec>A ?\<^vec>a \<Longrightarrow> B ?\<^vec>a"} \\
    @{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C"} \\
    @{text "(\<lambda>\<^vec>x. B (?\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>"} \\
   \end{tabular}}
  \]


  FIXME @{text "elim_resolution"}, @{text "dest_resolution"}
*}


end

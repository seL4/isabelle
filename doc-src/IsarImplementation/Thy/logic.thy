
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

  Pure derivations are relative to a logical theory, which declares
  type constructors, term constants, and axioms.  Theory declarations
  support schematic polymorphism, which is strictly speaking outside
  the logic.\footnote{Incidently, this is the main logical reason, why
  the theory context @{text "\<Theta>"} is separate from the context @{text
  "\<Gamma>"} of the core calculus.}
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

  A \emph{sort} is a list of type classes written as @{text
  "{c\<^isub>1, \<dots>, c\<^isub>m}"}, which represents symbolic
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
  (starting with a @{text "'"} character) and a sort constraint.  For
  example, @{text "('a, s)"} which is usually printed as @{text
  "\<alpha>\<^isub>s"}.  A \emph{schematic type variable} is a pair of an
  indexname and a sort constraint.  For example, @{text "(('a, 0),
  s)"} which is usually printed as @{text "?\<alpha>\<^isub>s"}.

  Note that \emph{all} syntactic components contribute to the identity
  of type variables, including the sort constraint.  The core logic
  handles type variables with the same name but different sorts as
  different, although some outer layers of the system make it hard to
  produce anything like this.

  A \emph{type constructor} @{text "\<kappa>"} is a @{text "k"}-ary operator
  on types declared in the theory.  Type constructor application is
  usually written postfix as @{text "(\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>k)\<kappa>"}.
  For @{text "k = 0"} the argument tuple is omitted, e.g.\ @{text
  "prop"} instead of @{text "()prop"}.  For @{text "k = 1"} the
  parentheses are omitted, e.g.\ @{text "\<alpha> list"} instead of @{text
  "(\<alpha>)list"}.  Further notation is provided for specific constructors,
  notably the right-associative infix @{text "\<alpha> \<Rightarrow> \<beta>"} instead of
  @{text "(\<alpha>, \<beta>)fun"}.
  
  A \emph{type} is defined inductively over type variables and type
  constructors as follows: @{text "\<tau> = \<alpha>\<^isub>s | ?\<alpha>\<^isub>s |
  (\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>k)k"}.

  A \emph{type abbreviation} is a syntactic abbreviation @{text
  "(\<^vec>\<alpha>)\<kappa> = \<tau>"} of an arbitrary type expression @{text "\<tau>"} over
  variables @{text "\<^vec>\<alpha>"}.  Type abbreviations looks like type
  constructors at the surface, but are fully expanded before entering
  the logical core.

  A \emph{type arity} declares the image behavior of a type
  constructor wrt.\ the algebra of sorts: @{text "\<kappa> :: (s\<^isub>1, \<dots>,
  s\<^isub>k)s"} means that @{text "(\<tau>\<^isub>1, \<dots>, \<tau>\<^isub>k)\<kappa>"} is
  of sort @{text "s"} if every argument type @{text "\<tau>\<^isub>i"} is
  of sort @{text "s\<^isub>i"}.  Arity declarations are implicitly
  completed, i.e.\ @{text "\<kappa> :: (\<^vec>s)c"} entails @{text "\<kappa> ::
  (\<^vec>s)c'"} for any @{text "c' \<supseteq> c"}.

  \medskip The sort algebra is always maintained as \emph{coregular},
  which means that type arities are consistent with the subclass
  relation: for each type constructor @{text "\<kappa>"} and classes @{text
  "c\<^isub>1 \<subseteq> c\<^isub>2"}, any arity @{text "\<kappa> ::
  (\<^vec>s\<^isub>1)c\<^isub>1"} has a corresponding arity @{text "\<kappa>
  :: (\<^vec>s\<^isub>2)c\<^isub>2"} where @{text "\<^vec>s\<^isub>1 \<subseteq>
  \<^vec>s\<^isub>2"} holds componentwise.

  The key property of a coregular order-sorted algebra is that sort
  constraints may be always solved in a most general fashion: for each
  type constructor @{text "\<kappa>"} and sort @{text "s"} there is a most
  general vector of argument sorts @{text "(s\<^isub>1, \<dots>,
  s\<^isub>k)"} such that a type scheme @{text
  "(\<alpha>\<^bsub>s\<^isub>1\<^esub>, \<dots>, \<alpha>\<^bsub>s\<^isub>k\<^esub>)\<kappa>"} is
  of sort @{text "s"}.  Consequently, the unification problem on the
  algebra of types has most general solutions (modulo renaming and
  equivalence of sorts).  Moreover, the usual type-inference algorithm
  will produce primary types as expected \cite{nipkow-prehofer}.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type class} \\
  @{index_ML_type sort} \\
  @{index_ML_type arity} \\
  @{index_ML_type typ} \\
  @{index_ML fold_atyps: "(typ -> 'a -> 'a) -> typ -> 'a -> 'a"} \\
  @{index_ML Sign.subsort: "theory -> sort * sort -> bool"} \\
  @{index_ML Sign.of_sort: "theory -> typ * sort -> bool"} \\
  @{index_ML Sign.add_types: "(bstring * int * mixfix) list -> theory -> theory"} \\
  @{index_ML Sign.add_tyabbrs_i: "
  (bstring * string list * typ * mixfix) list -> theory -> theory"} \\
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

  \item @{ML fold_atyps}~@{text "f \<tau>"} iterates function @{text "f"}
  over all occurrences of atoms (@{ML TFree} or @{ML TVar}) of @{text
  "\<tau>"}; the type structure is traversed from left to right.

  \item @{ML Sign.subsort}~@{text "thy (s\<^isub>1, s\<^isub>2)"}
  tests the subsort relation @{text "s\<^isub>1 \<subseteq> s\<^isub>2"}.

  \item @{ML Sign.of_sort}~@{text "thy (\<tau>, s)"} tests whether a type
  is of a given sort.

  \item @{ML Sign.add_types}~@{text "[(\<kappa>, k, mx), \<dots>]"} declares new
  type constructors @{text "\<kappa>"} with @{text "k"} arguments and
  optional mixfix syntax.

  \item @{ML Sign.add_tyabbrs_i}~@{text "[(\<kappa>, \<^vec>\<alpha>, \<tau>, mx), \<dots>]"}
  defines a new type abbreviation @{text "(\<^vec>\<alpha>)\<kappa> = \<tau>"} with
  optional mixfix syntax.

  \item @{ML Sign.primitive_class}~@{text "(c, [c\<^isub>1, \<dots>,
  c\<^isub>n])"} declares new class @{text "c"}, together with class
  relations @{text "c \<subseteq> c\<^isub>i"}, for @{text "i = 1, \<dots>, n"}.

  \item @{ML Sign.primitive_classrel}~@{text "(c\<^isub>1,
  c\<^isub>2)"} declares class relation @{text "c\<^isub>1 \<subseteq>
  c\<^isub>2"}.

  \item @{ML Sign.primitive_arity}~@{text "(\<kappa>, \<^vec>s, s)"} declares
  arity @{text "\<kappa> :: (\<^vec>s)s"}.

  \end{description}
*}



section {* Terms \label{sec:terms} *}

text {*
  \glossary{Term}{FIXME}

  The language of terms is that of simply-typed @{text "\<lambda>"}-calculus
  with de-Bruijn indices for bound variables, and named free
  variables, and constants.  Terms with loose bound variables are
  usually considered malformed.  The types of variables and constants
  is stored explicitly at each occurrence in the term (which is a
  known performance issue).

  FIXME de-Bruijn representation of lambda terms

  Term syntax provides explicit abstraction @{text "\<lambda>x :: \<alpha>. b(x)"}
  and application @{text "t u"}, while types are usually implicit
  thanks to type-inference.


  \[
  \infer{@{text "a\<^isub>\<tau> :: \<tau>"}}{}
  \qquad
  \infer{@{text "(\<lambda>x\<^sub>\<tau>. t) :: \<tau> \<Rightarrow> \<sigma>"}}{@{text "t :: \<sigma>"}}
  \qquad
  \infer{@{text "t u :: \<sigma>"}}{@{text "t :: \<tau> \<Rightarrow> \<sigma>"} & @{text "u :: \<tau>"}}
  \]

*}


text {*

FIXME

\glossary{Schematic polymorphism}{FIXME}

\glossary{Type variable}{FIXME}

*}


section {* Theorems \label{sec:thms} *}

text {*
  \glossary{Proposition}{A \seeglossary{term} of \seeglossary{type}
  @{text "prop"}.  Internally, there is nothing special about
  propositions apart from their type, but the concrete syntax enforces
  a clear distinction.  Propositions are structured via implication
  @{text "A \<Longrightarrow> B"} or universal quantification @{text "\<And>x. B x"} ---
  anything else is considered atomic.  The canonical form for
  propositions is that of a \seeglossary{Hereditary Harrop Formula}. FIXME}

  \glossary{Theorem}{A proven proposition within a certain theory and
  proof context, formally @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}; both contexts are
  rarely spelled out explicitly.  Theorems are usually normalized
  according to the \seeglossary{HHF} format. FIXME}

  \glossary{Fact}{Sometimes used interchangably for
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

  A \emph{proposition} is a well-formed term of type @{text "prop"}.
  The connectives of minimal logic are declared as constants of the
  basic theory:

  \smallskip
  \begin{tabular}{ll}
  @{text "all :: (\<alpha> \<Rightarrow> prop) \<Rightarrow> prop"} & universal quantification (binder @{text "\<And>"}) \\
  @{text "\<Longrightarrow> :: prop \<Rightarrow> prop \<Rightarrow> prop"} & implication (right associative infix) \\
  \end{tabular}

  \medskip A \emph{theorem} is a proven proposition, depending on a
  collection of assumptions, and axioms from the theory context.  The
  judgment @{text "A\<^isub>1, \<dots>, A\<^isub>n \<turnstile> B"} is defined
  inductively by the primitive inferences given in
  \figref{fig:prim-rules}; there is a global syntactic restriction
  that the hypotheses may not contain schematic variables.

  \begin{figure}[htb]
  \begin{center}
  \[
  \infer[@{text "(axiom)"}]{@{text "\<turnstile> A"}}{@{text "A \<in> \<Theta>"}}
  \qquad
  \infer[@{text "(assume)"}]{@{text "A \<turnstile> A"}}{}
  \]
  \[
  \infer[@{text "(\<And>_intro)"}]{@{text "\<Gamma> \<turnstile> \<And>x. b x"}}{@{text "\<Gamma> \<turnstile> b x"} & @{text "x \<notin> \<Gamma>"}}
  \qquad
  \infer[@{text "(\<And>_elim)"}]{@{text "\<Gamma> \<turnstile> b a"}}{@{text "\<Gamma> \<turnstile> \<And>x. b x"}}
  \]
  \[
  \infer[@{text "(\<Longrightarrow>_intro)"}]{@{text "\<Gamma> - A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \qquad
  \infer[@{text "(\<Longrightarrow>_elim)"}]{@{text "\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile> B"}}{@{text "\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B"} & @{text "\<Gamma>\<^sub>2 \<turnstile> A"}}
  \]
  \caption{Primitive inferences of the Pure logic}\label{fig:prim-rules}
  \end{center}
  \end{figure}

  The introduction and elimination rules for @{text "\<And>"} and @{text
  "\<Longrightarrow>"} are analogous to formation of (dependently typed) @{text
  "\<lambda>"}-terms representing the underlying proof objects.  Proof terms
  are \emph{irrelevant} in the Pure logic, they may never occur within
  propositions, i.e.\ the @{text "\<Longrightarrow>"} arrow of the framework is a
  non-dependent one.

  Also note that fixed parameters as in @{text "\<And>_intro"} need not be
  recorded in the context @{text "\<Gamma>"}, since syntactic types are
  always inhabitable.  An ``assumption'' @{text "x :: \<tau>"} is logically
  vacuous, because @{text "\<tau>"} is always non-empty.  This is the deeper
  reason why @{text "\<Gamma>"} only consists of hypothetical proofs, but no
  hypothetical terms.

  The corresponding proof terms are left implicit in the classic
  ``LCF-approach'', although they could be exploited separately
  \cite{Berghofer-Nipkow:2000}.  The implementation provides a runtime
  option to control the generation of full proof terms.

  \medskip The axiomatization of a theory is implicitly closed by
  forming all instances of type and term variables: @{text "\<turnstile> A\<theta>"} for
  any substirution instance of axiom @{text "\<turnstile> A"}.  By pushing
  substitution through derivations inductively, we get admissible
  substitution rules for theorems shown in \figref{fig:subst-rules}.

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

  Note that @{text "instantiate_term"} could be derived using @{text
  "\<And>_intro/elim"}, but this is not how it is implemented.  The type
  instantiation rule is a genuine admissible one, due to the lack of
  true polymorphism in the logic.

  Since @{text "\<Gamma>"} may never contain any schematic variables, the
  @{text "instantiate"} do not require an explicit side-condition.  In
  principle, variables could be substituted in hypotheses as well, but
  this could disrupt monotonicity of the basic calculus: derivations
  could leave the current proof context.

  \medskip The framework also provides builtin equality @{text "\<equiv>"},
  which is conceptually axiomatized shown in \figref{fig:equality},
  although the implementation provides derived rules directly:

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  @{text "\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop"} & equality relation (infix) \\
  @{text "\<turnstile> (\<lambda>x. b x) a \<equiv> b a"} & @{text "\<beta>"}-conversion \\
  @{text "\<turnstile> x \<equiv> x"} & reflexivity law \\
  @{text "\<turnstile> x \<equiv> y \<Longrightarrow> P x \<Longrightarrow> P y"} & substitution law \\
  @{text "\<turnstile> (\<And>x. f x \<equiv> g x) \<Longrightarrow> f \<equiv> g"} & extensionality \\
  @{text "\<turnstile> (A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<equiv> B"} & coincidence with equivalence \\
  \end{tabular}
  \caption{Conceptual axiomatization of equality.}\label{fig:equality}
  \end{center}
  \end{figure}

  Since the basic representation of terms already accounts for @{text
  "\<alpha>"}-conversion, Pure equality essentially acts like @{text
  "\<alpha>\<beta>\<eta>"}-equivalence on terms, while coinciding with bi-implication.


  \medskip Conjunction is defined in Pure as a derived connective, see
  \figref{fig:conjunction}.  This is occasionally useful to represent
  simultaneous statements behind the scenes --- framework conjunction
  is usually not exposed to the user.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  @{text "& :: prop \<Rightarrow> prop \<Rightarrow> prop"} & conjunction (hidden) \\
  @{text "\<turnstile> A & B \<equiv> (\<And>C. (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C)"} \\
  \end{tabular}
  \caption{Definition of conjunction.}\label{fig:equality}
  \end{center}
  \end{figure}

  The definition allows to derive the usual introduction @{text "\<turnstile> A \<Longrightarrow>
  B \<Longrightarrow> A & B"}, and destructions @{text "A & B \<Longrightarrow> A"} and @{text "A & B
  \<Longrightarrow> B"}.
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
  combined in the variants of @{text "elim-resosultion"} and @{text
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

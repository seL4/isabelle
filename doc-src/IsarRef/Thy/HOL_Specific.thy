theory HOL_Specific
imports Base Main "~~/src/HOL/Library/Old_Recdef"
begin

chapter {* Isabelle/HOL \label{ch:hol} *}

section {* Higher-Order Logic *}

text {* Isabelle/HOL is based on Higher-Order Logic, a polymorphic
  version of Church's Simple Theory of Types.  HOL can be best
  understood as a simply-typed version of classical set theory.  The
  logic was first implemented in Gordon's HOL system
  \cite{mgordon-hol}.  It extends Church's original logic
  \cite{church40} by explicit type variables (naive polymorphism) and
  a sound axiomatization scheme for new types based on subsets of
  existing types.

  Andrews's book \cite{andrews86} is a full description of the
  original Church-style higher-order logic, with proofs of correctness
  and completeness wrt.\ certain set-theoretic interpretations.  The
  particular extensions of Gordon-style HOL are explained semantically
  in two chapters of the 1993 HOL book \cite{pitts93}.

  Experience with HOL over decades has demonstrated that higher-order
  logic is widely applicable in many areas of mathematics and computer
  science.  In a sense, Higher-Order Logic is simpler than First-Order
  Logic, because there are fewer restrictions and special cases.  Note
  that HOL is \emph{weaker} than FOL with axioms for ZF set theory,
  which is traditionally considered the standard foundation of regular
  mathematics, but for most applications this does not matter.  If you
  prefer ML to Lisp, you will probably prefer HOL to ZF.

  \medskip The syntax of HOL follows @{text "\<lambda>"}-calculus and
  functional programming.  Function application is curried.  To apply
  the function @{text f} of type @{text "\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2 \<Rightarrow> \<tau>\<^sub>3"} to the
  arguments @{text a} and @{text b} in HOL, you simply write @{text "f
  a b"} (as in ML or Haskell).  There is no ``apply'' operator; the
  existing application of the Pure @{text "\<lambda>"}-calculus is re-used.
  Note that in HOL @{text "f (a, b)"} means ``@{text "f"} applied to
  the pair @{text "(a, b)"} (which is notation for @{text "Pair a
  b"}).  The latter typically introduces extra formal efforts that can
  be avoided by currying functions by default.  Explicit tuples are as
  infrequent in HOL formalizations as in good ML or Haskell programs.

  \medskip Isabelle/HOL has a distinct feel, compared to other
  object-logics like Isabelle/ZF.  It identifies object-level types
  with meta-level types, taking advantage of the default
  type-inference mechanism of Isabelle/Pure.  HOL fully identifies
  object-level functions with meta-level functions, with native
  abstraction and application.

  These identifications allow Isabelle to support HOL particularly
  nicely, but they also mean that HOL requires some sophistication
  from the user.  In particular, an understanding of Hindley-Milner
  type-inference with type-classes, which are both used extensively in
  the standard libraries and applications.  Beginners can set
  @{attribute show_types} or even @{attribute show_sorts} to get more
  explicit information about the result of type-inference.  *}


section {* Inductive and coinductive definitions \label{sec:hol-inductive} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "inductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "inductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "coinductive_set"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def (HOL) mono} & : & @{text attribute} \\
  \end{matharray}

  An \emph{inductive definition} specifies the least predicate or set
  @{text R} closed under given rules: applying a rule to elements of
  @{text R} yields a result within @{text R}.  For example, a
  structural operational semantics is an inductive definition of an
  evaluation relation.

  Dually, a \emph{coinductive definition} specifies the greatest
  predicate or set @{text R} that is consistent with given rules:
  every element of @{text R} can be seen as arising by applying a rule
  to elements of @{text R}.  An important example is using
  bisimulation relations to formalise equivalence of processes and
  infinite data structures.
  
  Both inductive and coinductive definitions are based on the
  Knaster-Tarski fixed-point theorem for complete lattices.  The
  collection of introduction rules given by the user determines a
  functor on subsets of set-theoretic relations.  The required
  monotonicity of the recursion scheme is proven as a prerequisite to
  the fixed-point definition and the resulting consequences.  This
  works by pushing inclusion through logical connectives and any other
  operator that might be wrapped around recursive occurrences of the
  defined relation: there must be a monotonicity theorem of the form
  @{text "A \<le> B \<Longrightarrow> \<M> A \<le> \<M> B"}, for each premise @{text "\<M> R t"} in an
  introduction rule.  The default rule declarations of Isabelle/HOL
  already take care of most common situations.

  @{rail "
    (@@{command (HOL) inductive} | @@{command (HOL) inductive_set} |
      @@{command (HOL) coinductive} | @@{command (HOL) coinductive_set})
    @{syntax target}? \\
    @{syntax \"fixes\"} (@'for' @{syntax \"fixes\"})? (@'where' clauses)? \\
    (@'monos' @{syntax thmrefs})?
    ;
    clauses: (@{syntax thmdecl}? @{syntax prop} + '|')
    ;
    @@{attribute (HOL) mono} (() | 'add' | 'del')
  "}

  \begin{description}

  \item @{command (HOL) "inductive"} and @{command (HOL)
  "coinductive"} define (co)inductive predicates from the introduction
  rules.

  The propositions given as @{text "clauses"} in the @{keyword
  "where"} part are either rules of the usual @{text "\<And>/\<Longrightarrow>"} format
  (with arbitrary nesting), or equalities using @{text "\<equiv>"}.  The
  latter specifies extra-logical abbreviations in the sense of
  @{command_ref abbreviation}.  Introducing abstract syntax
  simultaneously with the actual introduction rules is occasionally
  useful for complex specifications.

  The optional @{keyword "for"} part contains a list of parameters of
  the (co)inductive predicates that remain fixed throughout the
  definition, in contrast to arguments of the relation that may vary
  in each occurrence within the given @{text "clauses"}.

  The optional @{keyword "monos"} declaration contains additional
  \emph{monotonicity theorems}, which are required for each operator
  applied to a recursive set in the introduction rules.

  \item @{command (HOL) "inductive_set"} and @{command (HOL)
  "coinductive_set"} are wrappers for to the previous commands for
  native HOL predicates.  This allows to define (co)inductive sets,
  where multiple arguments are simulated via tuples.

  \item @{attribute (HOL) mono} declares monotonicity rules in the
  context.  These rule are involved in the automated monotonicity
  proof of the above inductive and coinductive definitions.

  \end{description}
*}


subsection {* Derived rules *}

text {* A (co)inductive definition of @{text R} provides the following
  main theorems:

  \begin{description}

  \item @{text R.intros} is the list of introduction rules as proven
  theorems, for the recursive predicates (or sets).  The rules are
  also available individually, using the names given them in the
  theory file;

  \item @{text R.cases} is the case analysis (or elimination) rule;

  \item @{text R.induct} or @{text R.coinduct} is the (co)induction
  rule;

  \item @{text R.simps} is the equation unrolling the fixpoint of the
  predicate one step.
 
  \end{description}

  When several predicates @{text "R\<^sub>1, \<dots>, R\<^sub>n"} are
  defined simultaneously, the list of introduction rules is called
  @{text "R\<^sub>1_\<dots>_R\<^sub>n.intros"}, the case analysis rules are
  called @{text "R\<^sub>1.cases, \<dots>, R\<^sub>n.cases"}, and the list
  of mutual induction rules is called @{text
  "R\<^sub>1_\<dots>_R\<^sub>n.inducts"}.
*}


subsection {* Monotonicity theorems *}

text {* The context maintains a default set of theorems that are used
  in monotonicity proofs.  New rules can be declared via the
  @{attribute (HOL) mono} attribute.  See the main Isabelle/HOL
  sources for some examples.  The general format of such monotonicity
  theorems is as follows:

  \begin{itemize}

  \item Theorems of the form @{text "A \<le> B \<Longrightarrow> \<M> A \<le> \<M> B"}, for proving
  monotonicity of inductive definitions whose introduction rules have
  premises involving terms such as @{text "\<M> R t"}.

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
*}

subsubsection {* Examples *}

text {* The finite powerset operator can be defined inductively like this: *}

inductive_set Fin :: "'a set \<Rightarrow> 'a set set" for A :: "'a set"
where
  empty: "{} \<in> Fin A"
| insert: "a \<in> A \<Longrightarrow> B \<in> Fin A \<Longrightarrow> insert a B \<in> Fin A"

text {* The accessible part of a relation is defined as follows: *}

inductive acc :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<prec>" 50)
where acc: "(\<And>y. y \<prec> x \<Longrightarrow> acc r y) \<Longrightarrow> acc r x"

text {* Common logical connectives can be easily characterized as
non-recursive inductive definitions with parameters, but without
arguments. *}

inductive AND for A B :: bool
where "A \<Longrightarrow> B \<Longrightarrow> AND A B"

inductive OR for A B :: bool
where "A \<Longrightarrow> OR A B"
  | "B \<Longrightarrow> OR A B"

inductive EXISTS for B :: "'a \<Rightarrow> bool"
where "B a \<Longrightarrow> EXISTS B"

text {* Here the @{text "cases"} or @{text "induct"} rules produced by
  the @{command inductive} package coincide with the expected
  elimination rules for Natural Deduction.  Already in the original
  article by Gerhard Gentzen \cite{Gentzen:1935} there is a hint that
  each connective can be characterized by its introductions, and the
  elimination can be constructed systematically. *}


section {* Recursive functions \label{sec:recursion} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "primrec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "fun"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def (HOL) "function"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "termination"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  @{rail "
    @@{command (HOL) primrec} @{syntax target}? @{syntax \"fixes\"} @'where' equations
    ;
    (@@{command (HOL) fun} | @@{command (HOL) function}) @{syntax target}? functionopts?
      @{syntax \"fixes\"} \\ @'where' equations
    ;

    equations: (@{syntax thmdecl}? @{syntax prop} + '|')
    ;
    functionopts: '(' (('sequential' | 'domintros') + ',') ')'
    ;
    @@{command (HOL) termination} @{syntax term}?
  "}

  \begin{description}

  \item @{command (HOL) "primrec"} defines primitive recursive
  functions over datatypes (see also @{command_ref (HOL) datatype} and
  @{command_ref (HOL) rep_datatype}).  The given @{text equations}
  specify reduction rules that are produced by instantiating the
  generic combinator for primitive recursion that is available for
  each datatype.

  Each equation needs to be of the form:

  @{text [display] "f x\<^sub>1 \<dots> x\<^sub>m (C y\<^sub>1 \<dots> y\<^sub>k) z\<^sub>1 \<dots> z\<^sub>n = rhs"}

  such that @{text C} is a datatype constructor, @{text rhs} contains
  only the free variables on the left-hand side (or from the context),
  and all recursive occurrences of @{text "f"} in @{text "rhs"} are of
  the form @{text "f \<dots> y\<^sub>i \<dots>"} for some @{text i}.  At most one
  reduction rule for each constructor can be given.  The order does
  not matter.  For missing constructors, the function is defined to
  return a default value, but this equation is made difficult to
  access for users.

  The reduction rules are declared as @{attribute simp} by default,
  which enables standard proof methods like @{method simp} and
  @{method auto} to normalize expressions of @{text "f"} applied to
  datatype constructions, by simulating symbolic computation via
  rewriting.

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
  command accommodate reasoning by induction (cf.\ @{method induct}):
  rule @{text "f.induct"} refers to a specific induction rule, with
  parameters named according to the user-specified equations. Cases
  are numbered starting from 1.  For @{command (HOL) "primrec"}, the
  induction principle coincides with structural recursion on the
  datatype where the recursion is carried out.

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

  \end{description}
*}

subsubsection {* Example: evaluation of expressions *}

text {* Subsequently, we define mutual datatypes for arithmetic and
  boolean expressions, and use @{command primrec} for evaluation
  functions that follow the same recursive structure. *}

datatype 'a aexp =
    IF "'a bexp"  "'a aexp"  "'a aexp"
  | Sum "'a aexp"  "'a aexp"
  | Diff "'a aexp"  "'a aexp"
  | Var 'a
  | Num nat
and 'a bexp =
    Less "'a aexp"  "'a aexp"
  | And "'a bexp"  "'a bexp"
  | Neg "'a bexp"


text {* \medskip Evaluation of arithmetic and boolean expressions *}

primrec evala :: "('a \<Rightarrow> nat) \<Rightarrow> 'a aexp \<Rightarrow> nat"
  and evalb :: "('a \<Rightarrow> nat) \<Rightarrow> 'a bexp \<Rightarrow> bool"
where
  "evala env (IF b a1 a2) = (if evalb env b then evala env a1 else evala env a2)"
| "evala env (Sum a1 a2) = evala env a1 + evala env a2"
| "evala env (Diff a1 a2) = evala env a1 - evala env a2"
| "evala env (Var v) = env v"
| "evala env (Num n) = n"
| "evalb env (Less a1 a2) = (evala env a1 < evala env a2)"
| "evalb env (And b1 b2) = (evalb env b1 \<and> evalb env b2)"
| "evalb env (Neg b) = (\<not> evalb env b)"

text {* Since the value of an expression depends on the value of its
  variables, the functions @{const evala} and @{const evalb} take an
  additional parameter, an \emph{environment} that maps variables to
  their values.

  \medskip Substitution on expressions can be defined similarly.  The
  mapping @{text f} of type @{typ "'a \<Rightarrow> 'a aexp"} given as a
  parameter is lifted canonically on the types @{typ "'a aexp"} and
  @{typ "'a bexp"}, respectively.
*}

primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp"
  and substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp"
where
  "substa f (IF b a1 a2) = IF (substb f b) (substa f a1) (substa f a2)"
| "substa f (Sum a1 a2) = Sum (substa f a1) (substa f a2)"
| "substa f (Diff a1 a2) = Diff (substa f a1) (substa f a2)"
| "substa f (Var v) = f v"
| "substa f (Num n) = Num n"
| "substb f (Less a1 a2) = Less (substa f a1) (substa f a2)"
| "substb f (And b1 b2) = And (substb f b1) (substb f b2)"
| "substb f (Neg b) = Neg (substb f b)"

text {* In textbooks about semantics one often finds substitution
  theorems, which express the relationship between substitution and
  evaluation.  For @{typ "'a aexp"} and @{typ "'a bexp"}, we can prove
  such a theorem by mutual induction, followed by simplification.
*}

lemma subst_one:
  "evala env (substa (Var (v := a')) a) = evala (env (v := evala env a')) a"
  "evalb env (substb (Var (v := a')) b) = evalb (env (v := evala env a')) b"
  by (induct a and b) simp_all

lemma subst_all:
  "evala env (substa s a) = evala (\<lambda>x. evala env (s x)) a"
  "evalb env (substb s b) = evalb (\<lambda>x. evala env (s x)) b"
  by (induct a and b) simp_all


subsubsection {* Example: a substitution function for terms *}

text {* Functions on datatypes with nested recursion are also defined
  by mutual primitive recursion. *}

datatype ('a, 'b) "term" = Var 'a | App 'b "('a, 'b) term list"

text {* A substitution function on type @{typ "('a, 'b) term"} can be
  defined as follows, by working simultaneously on @{typ "('a, 'b)
  term list"}: *}

primrec subst_term :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term" and
  subst_term_list :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term list \<Rightarrow> ('a, 'b) term list"
where
  "subst_term f (Var a) = f a"
| "subst_term f (App b ts) = App b (subst_term_list f ts)"
| "subst_term_list f [] = []"
| "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"

text {* The recursion scheme follows the structure of the unfolded
  definition of type @{typ "('a, 'b) term"}.  To prove properties of this
  substitution function, mutual induction is needed:
*}

lemma "subst_term (subst_term f1 \<circ> f2) t = subst_term f1 (subst_term f2 t)" and
  "subst_term_list (subst_term f1 \<circ> f2) ts = subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts) simp_all


subsubsection {* Example: a map function for infinitely branching trees *}

text {* Defining functions on infinitely branching datatypes by
  primitive recursion is just as easy.
*}

datatype 'a tree = Atom 'a | Branch "nat \<Rightarrow> 'a tree"

primrec map_tree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
where
  "map_tree f (Atom a) = Atom (f a)"
| "map_tree f (Branch ts) = Branch (\<lambda>x. map_tree f (ts x))"

text {* Note that all occurrences of functions such as @{text ts}
  above must be applied to an argument.  In particular, @{term
  "map_tree f \<circ> ts"} is not allowed here. *}

text {* Here is a simple composition lemma for @{term map_tree}: *}

lemma "map_tree g (map_tree f t) = map_tree (g \<circ> f) t"
  by (induct t) simp_all


subsection {* Proof methods related to recursive definitions *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) pat_completeness} & : & @{text method} \\
    @{method_def (HOL) relation} & : & @{text method} \\
    @{method_def (HOL) lexicographic_order} & : & @{text method} \\
    @{method_def (HOL) size_change} & : & @{text method} \\
    @{method_def (HOL) induction_schema} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method (HOL) relation} @{syntax term}
    ;
    @@{method (HOL) lexicographic_order} (@{syntax clasimpmod} * )
    ;
    @@{method (HOL) size_change} ( orders (@{syntax clasimpmod} * ) )
    ;
    @@{method (HOL) induction_schema}
    ;
    orders: ( 'max' | 'min' | 'ms' ) *
  "}

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
  which it uses internally to prove local descents.  The @{syntax
  clasimpmod} modifiers are accepted (as for @{method auto}).

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

  For local descent proofs, the @{syntax clasimpmod} modifiers are
  accepted (as for @{method auto}).

  \item @{method (HOL) induction_schema} derives user-specified
  induction rules from well-founded induction and completeness of
  patterns. This factors out some operations that are done internally
  by the function package and makes them available separately. See
  @{file "~~/src/HOL/ex/Induction_Schema.thy"} for examples.

  \end{description}
*}


subsection {* Functions with explicit partiality *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "partial_function"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def (HOL) "partial_function_mono"} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{command (HOL) partial_function} @{syntax target}?
      '(' @{syntax nameref} ')' @{syntax \"fixes\"} \\
      @'where' @{syntax thmdecl}? @{syntax prop}
  "}

  \begin{description}

  \item @{command (HOL) "partial_function"}~@{text "(mode)"} defines
  recursive functions based on fixpoints in complete partial
  orders. No termination proof is required from the user or
  constructed internally. Instead, the possibility of non-termination
  is modelled explicitly in the result type, which contains an
  explicit bottom element.

  Pattern matching and mutual recursion are currently not supported.
  Thus, the specification consists of a single function described by a
  single recursive equation.

  There are no fixed syntactic restrictions on the body of the
  function, but the induced functional must be provably monotonic
  wrt.\ the underlying order.  The monotonicitity proof is performed
  internally, and the definition is rejected when it fails. The proof
  can be influenced by declaring hints using the
  @{attribute (HOL) partial_function_mono} attribute.

  The mandatory @{text mode} argument specifies the mode of operation
  of the command, which directly corresponds to a complete partial
  order on the result type. By default, the following modes are
  defined:

  \begin{description}

  \item @{text option} defines functions that map into the @{type
  option} type. Here, the value @{term None} is used to model a
  non-terminating computation. Monotonicity requires that if @{term
  None} is returned by a recursive call, then the overall result must
  also be @{term None}. This is best achieved through the use of the
  monadic operator @{const "Option.bind"}.

  \item @{text tailrec} defines functions with an arbitrary result
  type and uses the slightly degenerated partial order where @{term
  "undefined"} is the bottom element.  Now, monotonicity requires that
  if @{term undefined} is returned by a recursive call, then the
  overall result must also be @{term undefined}. In practice, this is
  only satisfied when each recursive call is a tail call, whose result
  is directly returned. Thus, this mode of operation allows the
  definition of arbitrary tail-recursive functions.

  \end{description}

  Experienced users may define new modes by instantiating the locale
  @{const "partial_function_definitions"} appropriately.

  \item @{attribute (HOL) partial_function_mono} declares rules for
  use in the internal monononicity proofs of partial function
  definitions.

  \end{description}

*}


subsection {* Old-style recursive function definitions (TFL) *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "recdef"} & : & @{text "theory \<rightarrow> theory)"} \\
    @{command_def (HOL) "recdef_tc"}@{text "\<^sup>*"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  The old TFL commands @{command (HOL) "recdef"} and @{command (HOL)
  "recdef_tc"} for defining recursive are mostly obsolete; @{command
  (HOL) "function"} or @{command (HOL) "fun"} should be used instead.

  @{rail "
    @@{command (HOL) recdef} ('(' @'permissive' ')')? \\
      @{syntax name} @{syntax term} (@{syntax prop} +) hints?
    ;
    recdeftc @{syntax thmdecl}? tc
    ;
    hints: '(' @'hints' ( recdefmod * ) ')'
    ;
    recdefmod: (('recdef_simp' | 'recdef_cong' | 'recdef_wf')
      (() | 'add' | 'del') ':' @{syntax thmrefs}) | @{syntax clasimpmod}
    ;
    tc: @{syntax nameref} ('(' @{syntax nat} ')')?
  "}

  \begin{description}

  \item @{command (HOL) "recdef"} defines general well-founded
  recursive functions (using the TFL package), see also
  \cite{isabelle-HOL}.  The ``@{text "(permissive)"}'' option tells
  TFL to recover from failed proof attempts, returning unfinished
  results.  The @{text recdef_simp}, @{text recdef_cong}, and @{text
  recdef_wf} hints refer to auxiliary rules to be used in the internal
  automated proof process of TFL.  Additional @{syntax clasimpmod}
  declarations may be given to tune the context of the Simplifier
  (cf.\ \secref{sec:simplifier}) and Classical reasoner (cf.\
  \secref{sec:classical}).

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

  @{rail "
    (@@{attribute (HOL) recdef_simp} | @@{attribute (HOL) recdef_cong} |
      @@{attribute (HOL) recdef_wf}) (() | 'add' | 'del')
  "}
*}


section {* Datatypes \label{sec:hol-datatype} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "datatype"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "rep_datatype"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  @{rail "
    @@{command (HOL) datatype} (spec + @'and')
    ;
    @@{command (HOL) rep_datatype} ('(' (@{syntax name} +) ')')? (@{syntax term} +)
    ;

    spec: @{syntax typespec_sorts} @{syntax mixfix}? '=' (cons + '|')
    ;
    cons: @{syntax name} (@{syntax type} * ) @{syntax mixfix}?
  "}

  \begin{description}

  \item @{command (HOL) "datatype"} defines inductive datatypes in
  HOL.

  \item @{command (HOL) "rep_datatype"} represents existing types as
  datatypes.

  For foundational reasons, some basic types such as @{typ nat}, @{typ
  "'a \<times> 'b"}, @{typ "'a + 'b"}, @{typ bool} and @{typ unit} are
  introduced by more primitive means using @{command_ref typedef}.  To
  recover the rich infrastructure of @{command datatype} (e.g.\ rules
  for @{method cases} and @{method induct} and the primitive recursion
  combinators), such types may be represented as actual datatypes
  later.  This is done by specifying the constructors of the desired
  type, and giving a proof of the induction rule, distinctness and
  injectivity of constructors.

  For example, see @{file "~~/src/HOL/Sum_Type.thy"} for the
  representation of the primitive sum type as fully-featured datatype.

  \end{description}

  The generated rules for @{method induct} and @{method cases} provide
  case names according to the given constructors, while parameters are
  named after the types (see also \secref{sec:cases-induct}).

  See \cite{isabelle-HOL} for more details on datatypes, but beware of
  the old-style theory syntax being used there!  Apart from proper
  proof methods for case-analysis and induction, there are also
  emulations of ML tactics @{method (HOL) case_tac} and @{method (HOL)
  induct_tac} available, see \secref{sec:hol-induct-tac}; these admit
  to refer directly to the internal structure of subgoals (including
  internally bound parameters).
*}


subsubsection {* Examples *}

text {* We define a type of finite sequences, with slightly different
  names than the existing @{typ "'a list"} that is already in @{theory
  Main}: *}

datatype 'a seq = Empty | Seq 'a "'a seq"

text {* We can now prove some simple lemma by structural induction: *}

lemma "Seq x xs \<noteq> xs"
proof (induct xs arbitrary: x)
  case Empty
  txt {* This case can be proved using the simplifier: the freeness
    properties of the datatype are already declared as @{attribute
    simp} rules. *}
  show "Seq x Empty \<noteq> Empty"
    by simp
next
  case (Seq y ys)
  txt {* The step case is proved similarly. *}
  show "Seq x (Seq y ys) \<noteq> Seq y ys"
    using `Seq y ys \<noteq> ys` by simp
qed

text {* Here is a more succinct version of the same proof: *}

lemma "Seq x xs \<noteq> xs"
  by (induct xs arbitrary: x) simp_all


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

  @{rail "
    @@{command (HOL) record} @{syntax typespec_sorts} '=' \\
      (@{syntax type} '+')? (@{syntax constdecl} +)
  "}

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


subsubsection {* Examples *}

text {* See @{file "~~/src/HOL/ex/Records.thy"}, for example. *}


section {* Adhoc tuples *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def (HOL) split_format}@{text "\<^sup>*"} & : & @{text attribute} \\
  \end{matharray}

  @{rail "
    @@{attribute (HOL) split_format} ('(' 'complete' ')')?
  "}

  \begin{description}

  \item @{attribute (HOL) split_format}\ @{text "(complete)"} causes
  arguments in function applications to be represented canonically
  according to their tuple type structure.

  Note that this operation tends to invent funny names for new local
  parameters introduced.

  \end{description}
*}


section {* Typedef axiomatization \label{sec:hol-typedef} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "typedef"} & : & @{text "local_theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  A Gordon/HOL-style type definition is a certain axiom scheme that
  identifies a new type with a subset of an existing type.  More
  precisely, the new type is defined by exhibiting an existing type
  @{text \<tau>}, a set @{text "A :: \<tau> set"}, and a theorem that proves
  @{prop "\<exists>x. x \<in> A"}.  Thus @{text A} is a non-empty subset of @{text
  \<tau>}, and the new type denotes this subset.  New functions are
  postulated that establish an isomorphism between the new type and
  the subset.  In general, the type @{text \<tau>} may involve type
  variables @{text "\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n"} which means that the type definition
  produces a type constructor @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} depending on
  those type arguments.

  The axiomatization can be considered a ``definition'' in the sense
  of the particular set-theoretic interpretation of HOL
  \cite{pitts93}, where the universe of types is required to be
  downwards-closed wrt.\ arbitrary non-empty subsets.  Thus genuinely
  new types introduced by @{command "typedef"} stay within the range
  of HOL models by construction.  Note that @{command_ref
  type_synonym} from Isabelle/Pure merely introduces syntactic
  abbreviations, without any logical significance.
  
  @{rail "
    @@{command (HOL) typedef} alt_name? abs_type '=' rep_set
    ;

    alt_name: '(' (@{syntax name} | @'open' | @'open' @{syntax name}) ')'
    ;
    abs_type: @{syntax typespec_sorts} @{syntax mixfix}?
    ;
    rep_set: @{syntax term} (@'morphisms' @{syntax name} @{syntax name})?
  "}

  \begin{description}

  \item @{command (HOL) "typedef"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = A"}
  axiomatizes a type definition in the background theory of the
  current context, depending on a non-emptiness result of the set
  @{text A} that needs to be proven here.  The set @{text A} may
  contain type variables @{text "\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n"} as specified on the LHS,
  but no term variables.

  Even though a local theory specification, the newly introduced type
  constructor cannot depend on parameters or assumptions of the
  context: this is structurally impossible in HOL.  In contrast, the
  non-emptiness proof may use local assumptions in unusual situations,
  which could result in different interpretations in target contexts:
  the meaning of the bijection between the representing set @{text A}
  and the new type @{text t} may then change in different application
  contexts.

  By default, @{command (HOL) "typedef"} defines both a type
  constructor @{text t} for the new type, and a term constant @{text
  t} for the representing set within the old type.  Use the ``@{text
  "(open)"}'' option to suppress a separate constant definition
  altogether.  The injection from type to set is called @{text Rep_t},
  its inverse @{text Abs_t}, unless explicit @{keyword (HOL)
  "morphisms"} specification provides alternative names.

  The core axiomatization uses the locale predicate @{const
  type_definition} as defined in Isabelle/HOL.  Various basic
  consequences of that are instantiated accordingly, re-using the
  locale facts with names derived from the new type constructor.  Thus
  the generic @{thm type_definition.Rep} is turned into the specific
  @{text "Rep_t"}, for example.

  Theorems @{thm type_definition.Rep}, @{thm
  type_definition.Rep_inverse}, and @{thm type_definition.Abs_inverse}
  provide the most basic characterization as a corresponding
  injection/surjection pair (in both directions).  The derived rules
  @{thm type_definition.Rep_inject} and @{thm
  type_definition.Abs_inject} provide a more convenient version of
  injectivity, suitable for automated proof tools (e.g.\ in
  declarations involving @{attribute simp} or @{attribute iff}).
  Furthermore, the rules @{thm type_definition.Rep_cases}~/ @{thm
  type_definition.Rep_induct}, and @{thm type_definition.Abs_cases}~/
  @{thm type_definition.Abs_induct} provide alternative views on
  surjectivity.  These rules are already declared as set or type rules
  for the generic @{method cases} and @{method induct} methods,
  respectively.

  An alternative name for the set definition (and other derived
  entities) may be specified in parentheses; the default is to use
  @{text t} directly.

  \end{description}

  \begin{warn}
  If you introduce a new type axiomatically, i.e.\ via @{command_ref
  typedecl} and @{command_ref axiomatization}, the minimum requirement
  is that it has a non-empty model, to avoid immediate collapse of the
  HOL logic.  Moreover, one needs to demonstrate that the
  interpretation of such free-form axiomatizations can coexist with
  that of the regular @{command_def typedef} scheme, and any extension
  that other people might have introduced elsewhere (e.g.\ in HOLCF
  \cite{MuellerNvOS99}).
  \end{warn}
*}

subsubsection {* Examples *}

text {* Type definitions permit the introduction of abstract data
  types in a safe way, namely by providing models based on already
  existing types.  Given some abstract axiomatic description @{text P}
  of a type, this involves two steps:

  \begin{enumerate}

  \item Find an appropriate type @{text \<tau>} and subset @{text A} which
  has the desired properties @{text P}, and make a type definition
  based on this representation.

  \item Prove that @{text P} holds for @{text \<tau>} by lifting @{text P}
  from the representation.

  \end{enumerate}

  You can later forget about the representation and work solely in
  terms of the abstract properties @{text P}.

  \medskip The following trivial example pulls a three-element type
  into existence within the formal logical environment of HOL. *}

typedef three = "{(True, True), (True, False), (False, True)}"
  by blast

definition "One = Abs_three (True, True)"
definition "Two = Abs_three (True, False)"
definition "Three = Abs_three (False, True)"

lemma three_distinct: "One \<noteq> Two"  "One \<noteq> Three"  "Two \<noteq> Three"
  by (simp_all add: One_def Two_def Three_def Abs_three_inject three_def)

lemma three_cases:
  fixes x :: three obtains "x = One" | "x = Two" | "x = Three"
  by (cases x) (auto simp: One_def Two_def Three_def Abs_three_inject three_def)

text {* Note that such trivial constructions are better done with
  derived specification mechanisms such as @{command datatype}: *}

datatype three' = One' | Two' | Three'

text {* This avoids re-doing basic definitions and proofs from the
  primitive @{command typedef} above. *}


section {* Functorial structure of types *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "enriched_type"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
  \end{matharray}

  @{rail "
    @@{command (HOL) enriched_type} (@{syntax name} ':')? @{syntax term}
    ;
  "}

  \begin{description}

  \item @{command (HOL) "enriched_type"}~@{text "prefix: m"} allows to
  prove and register properties about the functorial structure of type
  constructors.  These properties then can be used by other packages
  to deal with those type constructors in certain type constructions.
  Characteristic theorems are noted in the current local theory.  By
  default, they are prefixed with the base name of the type
  constructor, an explicit prefix can be given alternatively.

  The given term @{text "m"} is considered as \emph{mapper} for the
  corresponding type constructor and must conform to the following
  type pattern:

  \begin{matharray}{lll}
    @{text "m"} & @{text "::"} &
      @{text "\<sigma>\<^isub>1 \<Rightarrow> \<dots> \<sigma>\<^isub>k \<Rightarrow> (\<^vec>\<alpha>\<^isub>n) t \<Rightarrow> (\<^vec>\<beta>\<^isub>n) t"} \\
  \end{matharray}

  \noindent where @{text t} is the type constructor, @{text
  "\<^vec>\<alpha>\<^isub>n"} and @{text "\<^vec>\<beta>\<^isub>n"} are distinct
  type variables free in the local theory and @{text "\<sigma>\<^isub>1"},
  \ldots, @{text "\<sigma>\<^isub>k"} is a subsequence of @{text "\<alpha>\<^isub>1 \<Rightarrow>
  \<beta>\<^isub>1"}, @{text "\<beta>\<^isub>1 \<Rightarrow> \<alpha>\<^isub>1"}, \ldots,
  @{text "\<alpha>\<^isub>n \<Rightarrow> \<beta>\<^isub>n"}, @{text "\<beta>\<^isub>n \<Rightarrow>
  \<alpha>\<^isub>n"}.

  \end{description}
*}

section {* Quotient types *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "quotient_type"} & : & @{text "local_theory \<rightarrow> proof(prove)"}\\
    @{command_def (HOL) "quotient_definition"} & : & @{text "local_theory \<rightarrow> proof(prove)"}\\
    @{command_def (HOL) "print_quotmaps"} & : & @{text "context \<rightarrow>"}\\
    @{command_def (HOL) "print_quotients"} & : & @{text "context \<rightarrow>"}\\
    @{command_def (HOL) "print_quotconsts"} & : & @{text "context \<rightarrow>"}\\
  \end{matharray}

  The quotient package defines a new quotient type given a raw type
  and a partial equivalence relation.  It also includes automation for
  transporting definitions and theorems.  It can automatically produce
  definitions and theorems on the quotient type, given the
  corresponding constants and facts on the raw type.

  @{rail "
    @@{command (HOL) quotient_type} (spec + @'and');

    spec: @{syntax typespec} @{syntax mixfix}? '=' \\
     @{syntax type} '/' ('partial' ':')? @{syntax term} \\
     (@'morphisms' @{syntax name} @{syntax name})?; 
  "}

  @{rail "
    @@{command (HOL) quotient_definition} constdecl? @{syntax thmdecl}? \\
    @{syntax term} 'is' @{syntax term};
 
    constdecl: @{syntax name} ('::' @{syntax type})? @{syntax mixfix}?
  "}

  \begin{description}
  
  \item @{command (HOL) "quotient_type"} defines quotient types.  The
  injection from a quotient type to a raw type is called @{text
  rep_t}, its inverse @{text abs_t} unless explicit @{keyword (HOL)
  "morphisms"} specification provides alternative names.

  \item @{command (HOL) "quotient_definition"} defines a constant on
  the quotient type.

  \item @{command (HOL) "print_quotmaps"} prints quotient map
  functions.

  \item @{command (HOL) "print_quotients"} prints quotients.

  \item @{command (HOL) "print_quotconsts"} prints quotient constants.

  \end{description}
*}


section {* Coercive subtyping *}

text {*
  \begin{matharray}{rcl}
    @{attribute_def (HOL) coercion} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_enabled} & : & @{text attribute} \\
    @{attribute_def (HOL) coercion_map} & : & @{text attribute} \\
  \end{matharray}

  Coercive subtyping allows the user to omit explicit type
  conversions, also called \emph{coercions}.  Type inference will add
  them as necessary when parsing a term. See
  \cite{traytel-berghofer-nipkow-2011} for details.

  @{rail "
    @@{attribute (HOL) coercion} (@{syntax term})?
    ;
  "}
  @{rail "
    @@{attribute (HOL) coercion_map} (@{syntax term})?
    ;
  "}

  \begin{description}

  \item @{attribute (HOL) "coercion"}~@{text "f"} registers a new
  coercion function @{text "f :: \<sigma>\<^isub>1 \<Rightarrow> \<sigma>\<^isub>2"} where @{text "\<sigma>\<^isub>1"} and
  @{text "\<sigma>\<^isub>2"} are type constructors without arguments.  Coercions are
  composed by the inference algorithm if needed.  Note that the type
  inference algorithm is complete only if the registered coercions
  form a lattice.

  \item @{attribute (HOL) "coercion_map"}~@{text "map"} registers a
  new map function to lift coercions through type constructors. The
  function @{text "map"} must conform to the following type pattern

  \begin{matharray}{lll}
    @{text "map"} & @{text "::"} &
      @{text "f\<^isub>1 \<Rightarrow> \<dots> \<Rightarrow> f\<^isub>n \<Rightarrow> (\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>n) t \<Rightarrow> (\<beta>\<^isub>1, \<dots>, \<beta>\<^isub>n) t"} \\
  \end{matharray}

  where @{text "t"} is a type constructor and @{text "f\<^isub>i"} is of type
  @{text "\<alpha>\<^isub>i \<Rightarrow> \<beta>\<^isub>i"} or @{text "\<beta>\<^isub>i \<Rightarrow> \<alpha>\<^isub>i"}.  Registering a map function
  overwrites any existing map function for this particular type
  constructor.

  \item @{attribute (HOL) "coercion_enabled"} enables the coercion
  inference algorithm.

  \end{description}
*}


section {* Arithmetic proof support *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) arith} & : & @{text method} \\
    @{attribute_def (HOL) arith} & : & @{text attribute} \\
    @{attribute_def (HOL) arith_split} & : & @{text attribute} \\
  \end{matharray}

  \begin{description}

  \item @{method (HOL) arith} decides linear arithmetic problems (on
  types @{text nat}, @{text int}, @{text real}).  Any current facts
  are inserted into the goal before running the procedure.

  \item @{attribute (HOL) arith} declares facts that are supplied to
  the arithmetic provers implicitly.

  \item @{attribute (HOL) arith_split} attribute declares case split
  rules to be expanded before @{method (HOL) arith} is invoked.

  \end{description}

  Note that a simpler (but faster) arithmetic prover is already
  invoked by the Simplifier.
*}


section {* Intuitionistic proof search *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) iprover} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method (HOL) iprover} ( @{syntax rulemod} * )
  "}

  \begin{description}

  \item @{method (HOL) iprover} performs intuitionistic proof search,
  depending on specifically declared rules from the context, or given
  as explicit arguments.  Chained facts are inserted into the goal
  before commencing proof search.

  Rules need to be classified as @{attribute (Pure) intro},
  @{attribute (Pure) elim}, or @{attribute (Pure) dest}; here the
  ``@{text "!"}'' indicator refers to ``safe'' rules, which may be
  applied aggressively (without considering back-tracking later).
  Rules declared with ``@{text "?"}'' are ignored in proof search (the
  single-step @{method (Pure) rule} method still observes these).  An
  explicit weight annotation may be given as well; otherwise the
  number of rule premises will be taken into account here.

  \end{description}
*}


section {* Model Elimination and Resolution *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) "meson"} & : & @{text method} \\
    @{method_def (HOL) "metis"} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method (HOL) meson} @{syntax thmrefs}?
    ;

    @@{method (HOL) metis}
      ('(' ('partial_types' | 'full_types' | 'no_types' | @{syntax name}) ')')?
      @{syntax thmrefs}?
  "}

  \begin{description}

  \item @{method (HOL) meson} implements Loveland's model elimination
  procedure \cite{loveland-78}.  See @{file
  "~~/src/HOL/ex/Meson_Test.thy"} for examples.

  \item @{method (HOL) metis} combines ordered resolution and ordered
  paramodulation to find first-order (or mildly higher-order) proofs.
  The first optional argument specifies a type encoding; see the
  Sledgehammer manual \cite{isabelle-sledgehammer} for details.  The
  directory @{file "~~/src/HOL/Metis_Examples"} contains several small
  theories developed to a large extent using @{method (HOL) metis}.

  \end{description}
*}


section {* Coherent Logic *}

text {*
  \begin{matharray}{rcl}
    @{method_def (HOL) "coherent"} & : & @{text method} \\
  \end{matharray}

  @{rail "
    @@{method (HOL) coherent} @{syntax thmrefs}?
  "}

  \begin{description}

  \item @{method (HOL) coherent} solves problems of \emph{Coherent
  Logic} \cite{Bezem-Coquand:2005}, which covers applications in
  confluence theory, lattice theory and projective geometry.  See
  @{file "~~/src/HOL/ex/Coherent.thy"} for some examples.

  \end{description}
*}


section {* Proving propositions *}

text {*
  In addition to the standard proof methods, a number of diagnosis
  tools search for proofs and provide an Isar proof snippet on success.
  These tools are available via the following commands.

  \begin{matharray}{rcl}
    @{command_def (HOL) "solve_direct"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "try"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "try_methods"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "sledgehammer"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "sledgehammer_params"} & : & @{text "theory \<rightarrow> theory"}
  \end{matharray}

  @{rail "
    @@{command (HOL) try}
    ;

    @@{command (HOL) try_methods} ( ( ( 'simp' | 'intro' | 'elim' | 'dest' ) ':' @{syntax thmrefs} ) + ) ?
      @{syntax nat}?
    ;

    @@{command (HOL) sledgehammer} ( '[' args ']' )? facts? @{syntax nat}?
    ;

    @@{command (HOL) sledgehammer_params} ( ( '[' args ']' ) ? )
    ;

    args: ( @{syntax name} '=' value + ',' )
    ;

    facts: '(' ( ( ( ( 'add' | 'del' ) ':' ) ? @{syntax thmrefs} ) + ) ? ')'
    ;
  "} % FIXME check args "value"

  \begin{description}

  \item @{command (HOL) "solve_direct"} checks whether the current
  subgoals can be solved directly by an existing theorem. Duplicate
  lemmas can be detected in this way.

  \item @{command (HOL) "try_methods"} attempts to prove a subgoal
  using a combination of standard proof methods (@{method auto},
  @{method simp}, @{method blast}, etc.).  Additional facts supplied
  via @{text "simp:"}, @{text "intro:"}, @{text "elim:"}, and @{text
  "dest:"} are passed to the appropriate proof methods.

  \item @{command (HOL) "try"} attempts to prove or disprove a subgoal
  using a combination of provers and disprovers (@{command (HOL)
  "solve_direct"}, @{command (HOL) "quickcheck"}, @{command (HOL)
  "try_methods"}, @{command (HOL) "sledgehammer"}, @{command (HOL)
  "nitpick"}).

  \item @{command (HOL) "sledgehammer"} attempts to prove a subgoal
  using external automatic provers (resolution provers and SMT
  solvers). See the Sledgehammer manual \cite{isabelle-sledgehammer}
  for details.

  \item @{command (HOL) "sledgehammer_params"} changes @{command (HOL)
  "sledgehammer"} configuration options persistently.

  \end{description}
*}


section {* Checking and refuting propositions *}

text {*
  Identifying incorrect propositions usually involves evaluation of
  particular assignments and systematic counterexample search.  This
  is supported by the following commands.

  \begin{matharray}{rcl}
    @{command_def (HOL) "value"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "values"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "refute"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "nitpick"}@{text "\<^sup>*"} & : & @{text "proof \<rightarrow>"} \\
    @{command_def (HOL) "quickcheck_params"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "refute_params"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "nitpick_params"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "quickcheck_generator"} & : & @{text "theory \<rightarrow> theory"}
  \end{matharray}

  @{rail "
    @@{command (HOL) value} ( '[' name ']' )? modes? @{syntax term}
    ;

    @@{command (HOL) values} modes? @{syntax nat}? @{syntax term}
    ;

    (@@{command (HOL) quickcheck} | @@{command (HOL) refute} | @@{command (HOL) nitpick})
      ( '[' args ']' )? @{syntax nat}?
    ;

    (@@{command (HOL) quickcheck_params} | @@{command (HOL) refute_params} |
      @@{command (HOL) nitpick_params}) ( '[' args ']' )?
    ;
    @@{command (HOL) quickcheck_generator} typeconstructor \\
      'operations:' ( @{syntax term} +)
    ;

    modes: '(' (@{syntax name} +) ')'
    ;

    args: ( @{syntax name} '=' value + ',' )
    ;
  "} % FIXME check "value"

  \begin{description}

  \item @{command (HOL) "value"}~@{text t} evaluates and prints a
  term; optionally @{text modes} can be specified, which are appended
  to the current print mode; see \secref{sec:print-modes}.
  Internally, the evaluation is performed by registered evaluators,
  which are invoked sequentially until a result is returned.
  Alternatively a specific evaluator can be selected using square
  brackets; typical evaluators use the current set of code equations
  to normalize and include @{text simp} for fully symbolic evaluation
  using the simplifier, @{text nbe} for \emph{normalization by
  evaluation} and \emph{code} for code generation in SML.

  \item @{command (HOL) "values"}~@{text t} enumerates a set
  comprehension by evaluation and prints its values up to the given
  number of solutions; optionally @{text modes} can be specified,
  which are appended to the current print mode; see
  \secref{sec:print-modes}.

  \item @{command (HOL) "quickcheck"} tests the current goal for
  counterexamples using a series of assignments for its free
  variables; by default the first subgoal is tested, an other can be
  selected explicitly using an optional goal index.  Assignments can
  be chosen exhausting the search space upto a given size, or using a
  fixed number of random assignments in the search space, or exploring
  the search space symbolically using narrowing.  By default,
  quickcheck uses exhaustive testing.  A number of configuration
  options are supported for @{command (HOL) "quickcheck"}, notably:

    \begin{description}

    \item[@{text tester}] specifies which testing approach to apply.
    There are three testers, @{text exhaustive}, @{text random}, and
    @{text narrowing}.  An unknown configuration option is treated as
    an argument to tester, making @{text "tester ="} optional.  When
    multiple testers are given, these are applied in parallel.  If no
    tester is specified, quickcheck uses the testers that are set
    active, i.e., configurations @{attribute
    quickcheck_exhaustive_active}, @{attribute
    quickcheck_random_active}, @{attribute
    quickcheck_narrowing_active} are set to true.

    \item[@{text size}] specifies the maximum size of the search space
    for assignment values.

    \item[@{text genuine_only}] sets quickcheck only to return genuine
    counterexample, but not potentially spurious counterexamples due
    to underspecified functions.
    
    \item[@{text eval}] takes a term or a list of terms and evaluates
    these terms under the variable assignment found by quickcheck.

    \item[@{text iterations}] sets how many sets of assignments are
    generated for each particular size.

    \item[@{text no_assms}] specifies whether assumptions in
    structured proofs should be ignored.

    \item[@{text timeout}] sets the time limit in seconds.

    \item[@{text default_type}] sets the type(s) generally used to
    instantiate type variables.

    \item[@{text report}] if set quickcheck reports how many tests
    fulfilled the preconditions.

    \item[@{text quiet}] if set quickcheck does not output anything
    while testing.
    
    \item[@{text verbose}] if set quickcheck informs about the current
    size and cardinality while testing.

    \item[@{text expect}] can be used to check if the user's
    expectation was met (@{text no_expectation}, @{text
    no_counterexample}, or @{text counterexample}).

    \end{description}

  These option can be given within square brackets.

  \item @{command (HOL) "quickcheck_params"} changes @{command (HOL)
  "quickcheck"} configuration options persistently.

  \item @{command (HOL) "quickcheck_generator"} creates random and
  exhaustive value generators for a given type and operations.  It
  generates values by using the operations as if they were
  constructors of that type.

  \item @{command (HOL) "refute"} tests the current goal for
  counterexamples using a reduction to SAT. The following
  configuration options are supported:

    \begin{description}

    \item[@{text minsize}] specifies the minimum size (cardinality) of
    the models to search for.

    \item[@{text maxsize}] specifies the maximum size (cardinality) of
    the models to search for. Nonpositive values mean @{text "\<infinity>"}.

    \item[@{text maxvars}] specifies the maximum number of Boolean
    variables to use when transforming the term into a propositional
    formula.  Nonpositive values mean @{text "\<infinity>"}.

    \item[@{text satsolver}] specifies the SAT solver to use.

    \item[@{text no_assms}] specifies whether assumptions in
    structured proofs should be ignored.

    \item[@{text maxtime}] sets the time limit in seconds.

    \item[@{text expect}] can be used to check if the user's
    expectation was met (@{text genuine}, @{text potential}, @{text
    none}, or @{text unknown}).

    \end{description}

  These option can be given within square brackets.

  \item @{command (HOL) "refute_params"} changes @{command (HOL)
  "refute"} configuration options persistently.

  \item @{command (HOL) "nitpick"} tests the current goal for
  counterexamples using a reduction to first-order relational
  logic. See the Nitpick manual \cite{isabelle-nitpick} for details.

  \item @{command (HOL) "nitpick_params"} changes @{command (HOL)
  "nitpick"} configuration options persistently.

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

  @{rail "
    @@{method (HOL) case_tac} @{syntax goal_spec}? @{syntax term} rule?
    ;
    @@{method (HOL) induct_tac} @{syntax goal_spec}? (@{syntax insts} * @'and') rule?
    ;
    @@{method (HOL) ind_cases} (@{syntax prop}+) (@'for' (@{syntax name}+))?
    ;
    @@{command (HOL) inductive_cases} (@{syntax thmdecl}? (@{syntax prop}+) + @'and')
    ;

    rule: 'rule' ':' @{syntax thmref}
  "}

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

text {* For validation purposes, it is often useful to \emph{execute}
  specifications.  In principle, execution could be simulated by
  Isabelle's inference kernel, i.e. by a combination of resolution and
  simplification.  Unfortunately, this approach is rather inefficient.
  A more efficient way of executing specifications is to translate
  them into a functional programming language such as ML.

  Isabelle provides a generic framework to support code generation
  from executable specifications.  Isabelle/HOL instantiates these
  mechanisms in a way that is amenable to end-user applications.  Code
  can be generated for functional programs (including overloading
  using type classes) targeting SML \cite{SML}, OCaml \cite{OCaml},
  Haskell \cite{haskell-revised-report} and Scala
  \cite{scala-overview-tech-report}.  Conceptually, code generation is
  split up in three steps: \emph{selection} of code theorems,
  \emph{translation} into an abstract executable view and
  \emph{serialization} to a specific \emph{target language}.
  Inductive specifications can be executed using the predicate
  compiler which operates within HOL.  See \cite{isabelle-codegen} for
  an introduction.

  \begin{matharray}{rcl}
    @{command_def (HOL) "export_code"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code} & : & @{text attribute} \\
    @{command_def (HOL) "code_abort"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_datatype"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "print_codesetup"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{attribute_def (HOL) code_unfold} & : & @{text attribute} \\
    @{attribute_def (HOL) code_post} & : & @{text attribute} \\
    @{attribute_def (HOL) code_abbrev} & : & @{text attribute} \\
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
    @{command_def (HOL) "code_reflect"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def (HOL) "code_pred"} & : & @{text "theory \<rightarrow> proof(prove)"}
  \end{matharray}

  @{rail "
    @@{command (HOL) export_code} ( constexpr + ) \\
       ( ( @'in' target ( @'module_name' @{syntax string} ) ? \\
        ( @'file' ( @{syntax string} | '-' ) ) ? ( '(' args ')' ) ?) + ) ?
    ;

    const: @{syntax term}
    ;

    constexpr: ( const | 'name._' | '_' )
    ;

    typeconstructor: @{syntax nameref}
    ;

    class: @{syntax nameref}
    ;

    target: 'SML' | 'OCaml' | 'Haskell' | 'Scala'
    ;

    @@{attribute (HOL) code} ( 'del' | 'abstype' | 'abstract' )?
    ;

    @@{command (HOL) code_abort} ( const + )
    ;

    @@{command (HOL) code_datatype} ( const + )
    ;

    @@{attribute (HOL) code_unfold} ( 'del' ) ?
    ;

    @@{attribute (HOL) code_post} ( 'del' ) ?
    ;

    @@{attribute (HOL) code_abbrev}
    ;

    @@{command (HOL) code_thms} ( constexpr + ) ?
    ;

    @@{command (HOL) code_deps} ( constexpr + ) ?
    ;

    @@{command (HOL) code_const} (const + @'and') \\
      ( ( '(' target ( syntax ? + @'and' ) ')' ) + )
    ;

    @@{command (HOL) code_type} (typeconstructor + @'and') \\
      ( ( '(' target ( syntax ? + @'and' ) ')' ) + )
    ;

    @@{command (HOL) code_class} (class + @'and') \\
      ( ( '(' target \\ ( @{syntax string} ? + @'and' ) ')' ) + )
    ;

    @@{command (HOL) code_instance} (( typeconstructor '::' class ) + @'and') \\
      ( ( '(' target ( '-' ? + @'and' ) ')' ) + )
    ;

    @@{command (HOL) code_reserved} target ( @{syntax string} + )
    ;

    @@{command (HOL) code_monad} const const target
    ;

    @@{command (HOL) code_include} target ( @{syntax string} ( @{syntax string} | '-') )
    ;

    @@{command (HOL) code_modulename} target ( ( @{syntax string} @{syntax string} ) + )
    ;

    @@{command (HOL) code_reflect} @{syntax string} \\
      ( @'datatypes' ( @{syntax string} '=' ( '_' | ( @{syntax string} + '|' ) + @'and' ) ) ) ? \\
      ( @'functions' ( @{syntax string} + ) ) ? ( @'file' @{syntax string} ) ?
    ;

    @@{command (HOL) code_pred} \\( '(' @'modes' ':' modedecl ')')? \\ const
    ;

    syntax: @{syntax string} | ( @'infix' | @'infixl' | @'infixr' ) @{syntax nat} @{syntax string}
    ;
    
    modedecl: (modes | ((const ':' modes) \\
         (@'and' ((const ':' modes @'and') +))?))
    ;
    
    modes: mode @'as' const
  "}

  \begin{description}

  \item @{command (HOL) "export_code"} generates code for a given list
  of constants in the specified target language(s).  If no
  serialization instruction is given, only abstract code is generated
  internally.

  Constants may be specified by giving them literally, referring to
  all executable contants within a certain theory by giving @{text
  "name.*"}, or referring to \emph{all} executable constants currently
  available by giving @{text "*"}.

  By default, for each involved theory one corresponding name space
  module is generated.  Alternativly, a module name may be specified
  after the @{keyword "module_name"} keyword; then \emph{all} code is
  placed in this module.

  For \emph{SML}, \emph{OCaml} and \emph{Scala} the file specification
  refers to a single file; for \emph{Haskell}, it refers to a whole
  directory, where code is generated in multiple files reflecting the
  module hierarchy.  Omitting the file specification denotes standard
  output.

  Serializers take an optional list of arguments in parentheses.  For
  \emph{SML} and \emph{OCaml}, ``@{text no_signatures}`` omits
  explicit module signatures.

  For \emph{Haskell} a module name prefix may be given using the
  ``@{text "root:"}'' argument; ``@{text string_classes}'' adds a
  ``@{verbatim "deriving (Read, Show)"}'' clause to each appropriate
  datatype declaration.

  \item @{attribute (HOL) code} explicitly selects (or with option
  ``@{text "del"}'' deselects) a code equation for code generation.
  Usually packages introducing code equations provide a reasonable
  default setup for selection.  Variants @{text "code abstype"} and
  @{text "code abstract"} declare abstract datatype certificates or
  code equations on abstract datatype representations respectively.

  \item @{command (HOL) "code_abort"} declares constants which are not
  required to have a definition by means of code equations; if needed
  these are implemented by program abort instead.

  \item @{command (HOL) "code_datatype"} specifies a constructor set
  for a logical type.

  \item @{command (HOL) "print_codesetup"} gives an overview on
  selected code equations and code generator datatypes.

  \item @{attribute (HOL) code_unfold} declares (or with option
  ``@{text "del"}'' removes) theorems which during preprocessing
  are applied as rewrite rules to any code equation or evaluation
  input.

  \item @{attribute (HOL) code_post} declares (or with option ``@{text
  "del"}'' removes) theorems which are applied as rewrite rules to any
  result of an evaluation.

  \item @{attribute (HOL) code_abbrev} declares equations which are
  applied as rewrite rules to any result of an evaluation and
  symmetrically during preprocessing to any code equation or evaluation
  input.

  \item @{command (HOL) "print_codeproc"} prints the setup of the code
  generator preprocessor.

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

  \item @{command (HOL) "code_reflect"} without a ``@{text "file"}''
  argument compiles code into the system runtime environment and
  modifies the code generator setup that future invocations of system
  runtime code generation referring to one of the ``@{text
  "datatypes"}'' or ``@{text "functions"}'' entities use these precompiled
  entities.  With a ``@{text "file"}'' argument, the corresponding code
  is generated into that specified file without modifying the code
  generator setup.

  \item @{command (HOL) "code_pred"} creates code equations for a predicate
    given a set of introduction rules. Optional mode annotations determine
    which arguments are supposed to be input or output. If alternative 
    introduction rules are declared, one must prove a corresponding elimination
    rule.

  \end{description}
*}


section {* Definition by specification \label{sec:hol-specification} *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOL) "specification"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def (HOL) "ax_specification"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  @{rail "
  (@@{command (HOL) specification} | @@{command (HOL) ax_specification})
    '(' (decl +) ')' \\ (@{syntax thmdecl}? @{syntax prop} +)
  ;
  decl: ((@{syntax name} ':')? @{syntax term} '(' @'overloaded' ')'?)
  "}

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

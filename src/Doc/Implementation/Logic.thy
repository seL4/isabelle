(*:maxLineLen=78:*)

theory Logic
imports Base
begin

chapter \<open>Primitive logic \label{ch:logic}\<close>

text \<open>
  The logical foundations of Isabelle/Isar are that of the Pure logic, which
  has been introduced as a Natural Deduction framework in @{cite paulson700}.
  This is essentially the same logic as ``\<open>\<lambda>HOL\<close>'' in the more abstract
  setting of Pure Type Systems (PTS) @{cite "Barendregt-Geuvers:2001"},
  although there are some key differences in the specific treatment of simple
  types in Isabelle/Pure.

  Following type-theoretic parlance, the Pure logic consists of three levels
  of \<open>\<lambda>\<close>-calculus with corresponding arrows, \<open>\<Rightarrow>\<close> for syntactic function space
  (terms depending on terms), \<open>\<And>\<close> for universal quantification (proofs
  depending on terms), and \<open>\<Longrightarrow>\<close> for implication (proofs depending on proofs).

  Derivations are relative to a logical theory, which declares type
  constructors, constants, and axioms. Theory declarations support schematic
  polymorphism, which is strictly speaking outside the logic.\<^footnote>\<open>This is the
  deeper logical reason, why the theory context \<open>\<Theta>\<close> is separate from the proof
  context \<open>\<Gamma>\<close> of the core calculus: type constructors, term constants, and
  facts (proof constants) may involve arbitrary type schemes, but the type of
  a locally fixed term parameter is also fixed!\<close>
\<close>


section \<open>Types \label{sec:types}\<close>

text \<open>
  The language of types is an uninterpreted order-sorted first-order algebra;
  types are qualified by ordered type classes.

  \<^medskip>
  A \<^emph>\<open>type class\<close> is an abstract syntactic entity declared in the theory
  context. The \<^emph>\<open>subclass relation\<close> \<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close> is specified by stating an
  acyclic generating relation; the transitive closure is maintained
  internally. The resulting relation is an ordering: reflexive, transitive,
  and antisymmetric.

  A \<^emph>\<open>sort\<close> is a list of type classes written as \<open>s = {c\<^sub>1, \<dots>, c\<^sub>m}\<close>, it
  represents symbolic intersection. Notationally, the curly braces are omitted
  for singleton intersections, i.e.\ any class \<open>c\<close> may be read as a sort
  \<open>{c}\<close>. The ordering on type classes is extended to sorts according to the
  meaning of intersections: \<open>{c\<^sub>1, \<dots> c\<^sub>m} \<subseteq> {d\<^sub>1, \<dots>, d\<^sub>n}\<close> iff \<open>\<forall>j. \<exists>i. c\<^sub>i \<subseteq>
  d\<^sub>j\<close>. The empty intersection \<open>{}\<close> refers to the universal sort, which is the
  largest element wrt.\ the sort order. Thus \<open>{}\<close> represents the ``full
  sort'', not the empty one! The intersection of all (finitely many) classes
  declared in the current theory is the least element wrt.\ the sort ordering.

  \<^medskip>
  A \<^emph>\<open>fixed type variable\<close> is a pair of a basic name (starting with a \<open>'\<close>
  character) and a sort constraint, e.g.\ \<open>('a, s)\<close> which is usually printed
  as \<open>\<alpha>\<^sub>s\<close>. A \<^emph>\<open>schematic type variable\<close> is a pair of an indexname and a sort
  constraint, e.g.\ \<open>(('a, 0), s)\<close> which is usually printed as \<open>?\<alpha>\<^sub>s\<close>.

  Note that \<^emph>\<open>all\<close> syntactic components contribute to the identity of type
  variables: basic name, index, and sort constraint. The core logic handles
  type variables with the same name but different sorts as different, although
  the type-inference layer (which is outside the core) rejects anything like
  that.

  A \<^emph>\<open>type constructor\<close> \<open>\<kappa>\<close> is a \<open>k\<close>-ary operator on types declared in the
  theory. Type constructor application is written postfix as \<open>(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>k)\<kappa>\<close>.
  For \<open>k = 0\<close> the argument tuple is omitted, e.g.\ \<open>prop\<close> instead of \<open>()prop\<close>.
  For \<open>k = 1\<close> the parentheses are omitted, e.g.\ \<open>\<alpha> list\<close> instead of
  \<open>(\<alpha>)list\<close>. Further notation is provided for specific constructors, notably
  the right-associative infix \<open>\<alpha> \<Rightarrow> \<beta>\<close> instead of \<open>(\<alpha>, \<beta>)fun\<close>.

  The logical category \<^emph>\<open>type\<close> is defined inductively over type variables and
  type constructors as follows: \<open>\<tau> = \<alpha>\<^sub>s | ?\<alpha>\<^sub>s | (\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>k)\<kappa>\<close>.

  A \<^emph>\<open>type abbreviation\<close> is a syntactic definition \<open>(\<^vec>\<alpha>)\<kappa> = \<tau>\<close> of an
  arbitrary type expression \<open>\<tau>\<close> over variables \<open>\<^vec>\<alpha>\<close>. Type abbreviations
  appear as type constructors in the syntax, but are expanded before entering
  the logical core.

  A \<^emph>\<open>type arity\<close> declares the image behavior of a type constructor wrt.\ the
  algebra of sorts: \<open>\<kappa> :: (s\<^sub>1, \<dots>, s\<^sub>k)s\<close> means that \<open>(\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>k)\<kappa>\<close> is of
  sort \<open>s\<close> if every argument type \<open>\<tau>\<^sub>i\<close> is of sort \<open>s\<^sub>i\<close>. Arity declarations
  are implicitly completed, i.e.\ \<open>\<kappa> :: (\<^vec>s)c\<close> entails \<open>\<kappa> ::
  (\<^vec>s)c'\<close> for any \<open>c' \<supseteq> c\<close>.

  \<^medskip>
  The sort algebra is always maintained as \<^emph>\<open>coregular\<close>, which means that type
  arities are consistent with the subclass relation: for any type constructor
  \<open>\<kappa>\<close>, and classes \<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close>, and arities \<open>\<kappa> :: (\<^vec>s\<^sub>1)c\<^sub>1\<close> and \<open>\<kappa> ::
  (\<^vec>s\<^sub>2)c\<^sub>2\<close> holds \<open>\<^vec>s\<^sub>1 \<subseteq> \<^vec>s\<^sub>2\<close> component-wise.

  The key property of a coregular order-sorted algebra is that sort
  constraints can be solved in a most general fashion: for each type
  constructor \<open>\<kappa>\<close> and sort \<open>s\<close> there is a most general vector of argument
  sorts \<open>(s\<^sub>1, \<dots>, s\<^sub>k)\<close> such that a type scheme \<open>(\<alpha>\<^bsub>s\<^sub>1\<^esub>, \<dots>, \<alpha>\<^bsub>s\<^sub>k\<^esub>)\<kappa>\<close> is of
  sort \<open>s\<close>. Consequently, type unification has most general solutions (modulo
  equivalence of sorts), so type-inference produces primary types as expected
  @{cite "nipkow-prehofer"}.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type class = string} \\
  @{define_ML_type sort = "class list"} \\
  @{define_ML_type arity = "string * sort list * sort"} \\
  @{define_ML_type typ} \\
  @{define_ML Term.map_atyps: "(typ -> typ) -> typ -> typ"} \\
  @{define_ML Term.fold_atyps: "(typ -> 'a -> 'a) -> typ -> 'a -> 'a"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML Sign.subsort: "theory -> sort * sort -> bool"} \\
  @{define_ML Sign.of_sort: "theory -> typ * sort -> bool"} \\
  @{define_ML Sign.add_type: "Proof.context -> binding * int * mixfix -> theory -> theory"} \\
  @{define_ML Sign.add_type_abbrev: "Proof.context ->
  binding * string list * typ -> theory -> theory"} \\
  @{define_ML Sign.primitive_class: "binding * class list -> theory -> theory"} \\
  @{define_ML Sign.primitive_classrel: "class * class -> theory -> theory"} \\
  @{define_ML Sign.primitive_arity: "arity -> theory -> theory"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>class\<close> represents type classes.

  \<^descr> Type \<^ML_type>\<open>sort\<close> represents sorts, i.e.\ finite intersections of
  classes. The empty list \<^ML>\<open>[]: sort\<close> refers to the empty class
  intersection, i.e.\ the ``full sort''.

  \<^descr> Type \<^ML_type>\<open>arity\<close> represents type arities. A triple \<open>(\<kappa>, \<^vec>s, s)
  : arity\<close> represents \<open>\<kappa> :: (\<^vec>s)s\<close> as described above.

  \<^descr> Type \<^ML_type>\<open>typ\<close> represents types; this is a datatype with constructors
  \<^ML>\<open>TFree\<close>, \<^ML>\<open>TVar\<close>, \<^ML>\<open>Type\<close>.

  \<^descr> \<^ML>\<open>Term.map_atyps\<close>~\<open>f \<tau>\<close> applies the mapping \<open>f\<close> to all atomic types
  (\<^ML>\<open>TFree\<close>, \<^ML>\<open>TVar\<close>) occurring in \<open>\<tau>\<close>.

  \<^descr> \<^ML>\<open>Term.fold_atyps\<close>~\<open>f \<tau>\<close> iterates the operation \<open>f\<close> over all
  occurrences of atomic types (\<^ML>\<open>TFree\<close>, \<^ML>\<open>TVar\<close>) in \<open>\<tau>\<close>; the type
  structure is traversed from left to right.

  \<^descr> \<^ML>\<open>Sign.subsort\<close>~\<open>thy (s\<^sub>1, s\<^sub>2)\<close> tests the subsort relation \<open>s\<^sub>1 \<subseteq>
  s\<^sub>2\<close>.

  \<^descr> \<^ML>\<open>Sign.of_sort\<close>~\<open>thy (\<tau>, s)\<close> tests whether type \<open>\<tau>\<close> is of sort \<open>s\<close>.

  \<^descr> \<^ML>\<open>Sign.add_type\<close>~\<open>ctxt (\<kappa>, k, mx)\<close> declares a new type constructors \<open>\<kappa>\<close>
  with \<open>k\<close> arguments and optional mixfix syntax.

  \<^descr> \<^ML>\<open>Sign.add_type_abbrev\<close>~\<open>ctxt (\<kappa>, \<^vec>\<alpha>, \<tau>)\<close> defines a new type
  abbreviation \<open>(\<^vec>\<alpha>)\<kappa> = \<tau>\<close>.

  \<^descr> \<^ML>\<open>Sign.primitive_class\<close>~\<open>(c, [c\<^sub>1, \<dots>, c\<^sub>n])\<close> declares a new class \<open>c\<close>,
  together with class relations \<open>c \<subseteq> c\<^sub>i\<close>, for \<open>i = 1, \<dots>, n\<close>.

  \<^descr> \<^ML>\<open>Sign.primitive_classrel\<close>~\<open>(c\<^sub>1, c\<^sub>2)\<close> declares the class relation
  \<open>c\<^sub>1 \<subseteq> c\<^sub>2\<close>.

  \<^descr> \<^ML>\<open>Sign.primitive_arity\<close>~\<open>(\<kappa>, \<^vec>s, s)\<close> declares the arity \<open>\<kappa> ::
  (\<^vec>s)s\<close>.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "class"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "sort"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "type_name"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "type_abbrev"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "nonterminal"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "typ"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation class} embedded
  ;
  @@{ML_antiquotation sort} sort
  ;
  (@@{ML_antiquotation type_name} |
   @@{ML_antiquotation type_abbrev} |
   @@{ML_antiquotation nonterminal}) embedded
  ;
  @@{ML_antiquotation typ} type
  \<close>

  \<^descr> \<open>@{class c}\<close> inlines the internalized class \<open>c\<close> --- as \<^ML_type>\<open>string\<close>
  literal.

  \<^descr> \<open>@{sort s}\<close> inlines the internalized sort \<open>s\<close> --- as \<^ML_type>\<open>string
  list\<close> literal.

  \<^descr> \<open>@{type_name c}\<close> inlines the internalized type constructor \<open>c\<close> --- as
  \<^ML_type>\<open>string\<close> literal.

  \<^descr> \<open>@{type_abbrev c}\<close> inlines the internalized type abbreviation \<open>c\<close> --- as
  \<^ML_type>\<open>string\<close> literal.

  \<^descr> \<open>@{nonterminal c}\<close> inlines the internalized syntactic type~/ grammar
  nonterminal \<open>c\<close> --- as \<^ML_type>\<open>string\<close> literal.

  \<^descr> \<open>@{typ \<tau>}\<close> inlines the internalized type \<open>\<tau>\<close> --- as constructor term for
  datatype \<^ML_type>\<open>typ\<close>.
\<close>


section \<open>Terms \label{sec:terms}\<close>

text \<open>
  The language of terms is that of simply-typed \<open>\<lambda>\<close>-calculus with de-Bruijn
  indices for bound variables (cf.\ @{cite debruijn72} or @{cite
  "paulson-ml2"}), with the types being determined by the corresponding
  binders. In contrast, free variables and constants have an explicit name and
  type in each occurrence.

  \<^medskip>
  A \<^emph>\<open>bound variable\<close> is a natural number \<open>b\<close>, which accounts for the number
  of intermediate binders between the variable occurrence in the body and its
  binding position. For example, the de-Bruijn term \<open>\<lambda>\<^bsub>bool\<^esub>. \<lambda>\<^bsub>bool\<^esub>. 1 \<and> 0\<close>
  would correspond to \<open>\<lambda>x\<^bsub>bool\<^esub>. \<lambda>y\<^bsub>bool\<^esub>. x \<and> y\<close> in a named representation.
  Note that a bound variable may be represented by different de-Bruijn indices
  at different occurrences, depending on the nesting of abstractions.

  A \<^emph>\<open>loose variable\<close> is a bound variable that is outside the scope of local
  binders. The types (and names) for loose variables can be managed as a
  separate context, that is maintained as a stack of hypothetical binders. The
  core logic operates on closed terms, without any loose variables.

  A \<^emph>\<open>fixed variable\<close> is a pair of a basic name and a type, e.g.\ \<open>(x, \<tau>)\<close>
  which is usually printed \<open>x\<^sub>\<tau>\<close> here. A \<^emph>\<open>schematic variable\<close> is a pair of an
  indexname and a type, e.g.\ \<open>((x, 0), \<tau>)\<close> which is likewise printed as
  \<open>?x\<^sub>\<tau>\<close>.

  \<^medskip>
  A \<^emph>\<open>constant\<close> is a pair of a basic name and a type, e.g.\ \<open>(c, \<tau>)\<close> which is
  usually printed as \<open>c\<^sub>\<tau>\<close> here. Constants are declared in the context as
  polymorphic families \<open>c :: \<sigma>\<close>, meaning that all substitution instances \<open>c\<^sub>\<tau>\<close>
  for \<open>\<tau> = \<sigma>\<vartheta>\<close> are valid.

  The vector of \<^emph>\<open>type arguments\<close> of constant \<open>c\<^sub>\<tau>\<close> wrt.\ the declaration \<open>c
  :: \<sigma>\<close> is defined as the codomain of the matcher \<open>\<vartheta> = {?\<alpha>\<^sub>1 \<mapsto> \<tau>\<^sub>1,
  \<dots>, ?\<alpha>\<^sub>n \<mapsto> \<tau>\<^sub>n}\<close> presented in canonical order \<open>(\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>n)\<close>, corresponding
  to the left-to-right occurrences of the \<open>\<alpha>\<^sub>i\<close> in \<open>\<sigma>\<close>. Within a given theory
  context, there is a one-to-one correspondence between any constant \<open>c\<^sub>\<tau>\<close> and
  the application \<open>c(\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>n)\<close> of its type arguments. For example, with
  \<open>plus :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>\<close>, the instance \<open>plus\<^bsub>nat \<Rightarrow> nat \<Rightarrow> nat\<^esub>\<close> corresponds to
  \<open>plus(nat)\<close>.

  Constant declarations \<open>c :: \<sigma>\<close> may contain sort constraints for type
  variables in \<open>\<sigma>\<close>. These are observed by type-inference as expected, but
  \<^emph>\<open>ignored\<close> by the core logic. This means the primitive logic is able to
  reason with instances of polymorphic constants that the user-level
  type-checker would reject due to violation of type class restrictions.

  \<^medskip>
  An \<^emph>\<open>atomic term\<close> is either a variable or constant. The logical category
  \<^emph>\<open>term\<close> is defined inductively over atomic terms, with abstraction and
  application as follows: \<open>t = b | x\<^sub>\<tau> | ?x\<^sub>\<tau> | c\<^sub>\<tau> | \<lambda>\<^sub>\<tau>. t | t\<^sub>1 t\<^sub>2\<close>.
  Parsing and printing takes care of converting between an external
  representation with named bound variables. Subsequently, we shall use the
  latter notation instead of internal de-Bruijn representation.

  The inductive relation \<open>t :: \<tau>\<close> assigns a (unique) type to a term according
  to the structure of atomic terms, abstractions, and applications:
  \[
  \infer{\<open>a\<^sub>\<tau> :: \<tau>\<close>}{}
  \qquad
  \infer{\<open>(\<lambda>x\<^sub>\<tau>. t) :: \<tau> \<Rightarrow> \<sigma>\<close>}{\<open>t :: \<sigma>\<close>}
  \qquad
  \infer{\<open>t u :: \<sigma>\<close>}{\<open>t :: \<tau> \<Rightarrow> \<sigma>\<close> & \<open>u :: \<tau>\<close>}
  \]
  A \<^emph>\<open>well-typed term\<close> is a term that can be typed according to these rules.

  Typing information can be omitted: type-inference is able to reconstruct the
  most general type of a raw term, while assigning most general types to all
  of its variables and constants. Type-inference depends on a context of type
  constraints for fixed variables, and declarations for polymorphic constants.

  The identity of atomic terms consists both of the name and the type
  component. This means that different variables \<open>x\<^bsub>\<tau>\<^sub>1\<^esub>\<close> and \<open>x\<^bsub>\<tau>\<^sub>2\<^esub>\<close> may
  become the same after type instantiation. Type-inference rejects variables
  of the same name, but different types. In contrast, mixed instances of
  polymorphic constants occur routinely.

  \<^medskip>
  The \<^emph>\<open>hidden polymorphism\<close> of a term \<open>t :: \<sigma>\<close> is the set of type variables
  occurring in \<open>t\<close>, but not in its type \<open>\<sigma>\<close>. This means that the term
  implicitly depends on type arguments that are not accounted in the result
  type, i.e.\ there are different type instances \<open>t\<vartheta> :: \<sigma>\<close> and
  \<open>t\<vartheta>' :: \<sigma>\<close> with the same type. This slightly pathological
  situation notoriously demands additional care.

  \<^medskip>
  A \<^emph>\<open>term abbreviation\<close> is a syntactic definition \<open>c\<^sub>\<sigma> \<equiv> t\<close> of a closed term
  \<open>t\<close> of type \<open>\<sigma>\<close>, without any hidden polymorphism. A term abbreviation looks
  like a constant in the syntax, but is expanded before entering the logical
  core. Abbreviations are usually reverted when printing terms, using \<open>t \<rightarrow>
  c\<^sub>\<sigma>\<close> as rules for higher-order rewriting.

  \<^medskip>
  Canonical operations on \<open>\<lambda>\<close>-terms include \<open>\<alpha>\<beta>\<eta>\<close>-conversion: \<open>\<alpha>\<close>-conversion
  refers to capture-free renaming of bound variables; \<open>\<beta>\<close>-conversion contracts
  an abstraction applied to an argument term, substituting the argument in the
  body: \<open>(\<lambda>x. b)a\<close> becomes \<open>b[a/x]\<close>; \<open>\<eta>\<close>-conversion contracts vacuous
  application-abstraction: \<open>\<lambda>x. f x\<close> becomes \<open>f\<close>, provided that the bound
  variable does not occur in \<open>f\<close>.

  Terms are normally treated modulo \<open>\<alpha>\<close>-conversion, which is implicit in the
  de-Bruijn representation. Names for bound variables in abstractions are
  maintained separately as (meaningless) comments, mostly for parsing and
  printing. Full \<open>\<alpha>\<beta>\<eta>\<close>-conversion is commonplace in various standard
  operations (\secref{sec:obj-rules}) that are based on higher-order
  unification and matching.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type term} \\
  @{define_ML_infix "aconv": "term * term -> bool"} \\
  @{define_ML Term.map_types: "(typ -> typ) -> term -> term"} \\
  @{define_ML Term.fold_types: "(typ -> 'a -> 'a) -> term -> 'a -> 'a"} \\
  @{define_ML Term.map_aterms: "(term -> term) -> term -> term"} \\
  @{define_ML Term.fold_aterms: "(term -> 'a -> 'a) -> term -> 'a -> 'a"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML fastype_of: "term -> typ"} \\
  @{define_ML lambda: "term -> term -> term"} \\
  @{define_ML betapply: "term * term -> term"} \\
  @{define_ML incr_boundvars: "int -> term -> term"} \\
  @{define_ML Sign.declare_const: "Proof.context ->
  (binding * typ) * mixfix -> theory -> term * theory"} \\
  @{define_ML Sign.add_abbrev: "string -> binding * term ->
  theory -> (term * term) * theory"} \\
  @{define_ML Sign.const_typargs: "theory -> string * typ -> typ list"} \\
  @{define_ML Sign.const_instance: "theory -> string * typ list -> typ"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>term\<close> represents de-Bruijn terms, with comments in
  abstractions, and explicitly named free variables and constants; this is a
  datatype with constructors @{define_ML Bound}, @{define_ML Free}, @{define_ML
  Var}, @{define_ML Const}, @{define_ML Abs}, @{define_ML_infix "$"}.

  \<^descr> \<open>t\<close>~\<^ML_text>\<open>aconv\<close>~\<open>u\<close> checks \<open>\<alpha>\<close>-equivalence of two terms. This is the
  basic equality relation on type \<^ML_type>\<open>term\<close>; raw datatype equality
  should only be used for operations related to parsing or printing!

  \<^descr> \<^ML>\<open>Term.map_types\<close>~\<open>f t\<close> applies the mapping \<open>f\<close> to all types occurring
  in \<open>t\<close>.

  \<^descr> \<^ML>\<open>Term.fold_types\<close>~\<open>f t\<close> iterates the operation \<open>f\<close> over all
  occurrences of types in \<open>t\<close>; the term structure is traversed from left to
  right.

  \<^descr> \<^ML>\<open>Term.map_aterms\<close>~\<open>f t\<close> applies the mapping \<open>f\<close> to all atomic terms
  (\<^ML>\<open>Bound\<close>, \<^ML>\<open>Free\<close>, \<^ML>\<open>Var\<close>, \<^ML>\<open>Const\<close>) occurring in \<open>t\<close>.

  \<^descr> \<^ML>\<open>Term.fold_aterms\<close>~\<open>f t\<close> iterates the operation \<open>f\<close> over all
  occurrences of atomic terms (\<^ML>\<open>Bound\<close>, \<^ML>\<open>Free\<close>, \<^ML>\<open>Var\<close>, \<^ML>\<open>Const\<close>) in \<open>t\<close>; the term structure is traversed from left to right.

  \<^descr> \<^ML>\<open>fastype_of\<close>~\<open>t\<close> determines the type of a well-typed term. This
  operation is relatively slow, despite the omission of any sanity checks.

  \<^descr> \<^ML>\<open>lambda\<close>~\<open>a b\<close> produces an abstraction \<open>\<lambda>a. b\<close>, where occurrences of
  the atomic term \<open>a\<close> in the body \<open>b\<close> are replaced by bound variables.

  \<^descr> \<^ML>\<open>betapply\<close>~\<open>(t, u)\<close> produces an application \<open>t u\<close>, with topmost
  \<open>\<beta>\<close>-conversion if \<open>t\<close> is an abstraction.

  \<^descr> \<^ML>\<open>incr_boundvars\<close>~\<open>j\<close> increments a term's dangling bound variables by
  the offset \<open>j\<close>. This is required when moving a subterm into a context where
  it is enclosed by a different number of abstractions. Bound variables with a
  matching abstraction are unaffected.

  \<^descr> \<^ML>\<open>Sign.declare_const\<close>~\<open>ctxt ((c, \<sigma>), mx)\<close> declares a new constant \<open>c ::
  \<sigma>\<close> with optional mixfix syntax.

  \<^descr> \<^ML>\<open>Sign.add_abbrev\<close>~\<open>print_mode (c, t)\<close> introduces a new term
  abbreviation \<open>c \<equiv> t\<close>.

  \<^descr> \<^ML>\<open>Sign.const_typargs\<close>~\<open>thy (c, \<tau>)\<close> and \<^ML>\<open>Sign.const_instance\<close>~\<open>thy
  (c, [\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>n])\<close> convert between two representations of polymorphic
  constants: full type instance vs.\ compact type arguments form.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "const_name"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "const_abbrev"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "const"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "term"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "prop"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  (@@{ML_antiquotation const_name} |
   @@{ML_antiquotation const_abbrev}) embedded
  ;
  @@{ML_antiquotation const} ('(' (type + ',') ')')?
  ;
  @@{ML_antiquotation term} term
  ;
  @@{ML_antiquotation prop} prop
  \<close>

  \<^descr> \<open>@{const_name c}\<close> inlines the internalized logical constant name \<open>c\<close> ---
  as \<^ML_type>\<open>string\<close> literal.

  \<^descr> \<open>@{const_abbrev c}\<close> inlines the internalized abbreviated constant name \<open>c\<close>
  --- as \<^ML_type>\<open>string\<close> literal.

  \<^descr> \<open>@{const c(\<^vec>\<tau>)}\<close> inlines the internalized constant \<open>c\<close> with precise
  type instantiation in the sense of \<^ML>\<open>Sign.const_instance\<close> --- as \<^ML>\<open>Const\<close> constructor term for datatype \<^ML_type>\<open>term\<close>.

  \<^descr> \<open>@{term t}\<close> inlines the internalized term \<open>t\<close> --- as constructor term for
  datatype \<^ML_type>\<open>term\<close>.

  \<^descr> \<open>@{prop \<phi>}\<close> inlines the internalized proposition \<open>\<phi>\<close> --- as constructor
  term for datatype \<^ML_type>\<open>term\<close>.
\<close>


section \<open>Theorems \label{sec:thms}\<close>

text \<open>
  A \<^emph>\<open>proposition\<close> is a well-typed term of type \<open>prop\<close>, a \<^emph>\<open>theorem\<close> is a
  proven proposition (depending on a context of hypotheses and the background
  theory). Primitive inferences include plain Natural Deduction rules for the
  primary connectives \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> of the framework. There is also a builtin
  notion of equality/equivalence \<open>\<equiv>\<close>.
\<close>


subsection \<open>Primitive connectives and rules \label{sec:prim-rules}\<close>

text \<open>
  The theory \<open>Pure\<close> contains constant declarations for the primitive
  connectives \<open>\<And>\<close>, \<open>\<Longrightarrow>\<close>, and \<open>\<equiv>\<close> of the logical framework, see
  \figref{fig:pure-connectives}. The derivability judgment \<open>A\<^sub>1, \<dots>, A\<^sub>n \<turnstile> B\<close>
  is defined inductively by the primitive inferences given in
  \figref{fig:prim-rules}, with the global restriction that the hypotheses
  must \<^emph>\<open>not\<close> contain any schematic variables. The builtin equality is
  conceptually axiomatized as shown in \figref{fig:pure-equality}, although
  the implementation works directly with derived inferences.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  \<open>all :: (\<alpha> \<Rightarrow> prop) \<Rightarrow> prop\<close> & universal quantification (binder \<open>\<And>\<close>) \\
  \<open>\<Longrightarrow> :: prop \<Rightarrow> prop \<Rightarrow> prop\<close> & implication (right associative infix) \\
  \<open>\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop\<close> & equality relation (infix) \\
  \end{tabular}
  \caption{Primitive connectives of Pure}\label{fig:pure-connectives}
  \end{center}
  \end{figure}

  \begin{figure}[htb]
  \begin{center}
  \[
  \infer[\<open>(axiom)\<close>]{\<open>\<turnstile> A\<close>}{\<open>A \<in> \<Theta>\<close>}
  \qquad
  \infer[\<open>(assume)\<close>]{\<open>A \<turnstile> A\<close>}{}
  \]
  \[
  \infer[\<open>(\<And>\<hyphen>intro)\<close>]{\<open>\<Gamma> \<turnstile> \<And>x. B[x]\<close>}{\<open>\<Gamma> \<turnstile> B[x]\<close> & \<open>x \<notin> \<Gamma>\<close>}
  \qquad
  \infer[\<open>(\<And>\<hyphen>elim)\<close>]{\<open>\<Gamma> \<turnstile> B[a]\<close>}{\<open>\<Gamma> \<turnstile> \<And>x. B[x]\<close>}
  \]
  \[
  \infer[\<open>(\<Longrightarrow>\<hyphen>intro)\<close>]{\<open>\<Gamma> - A \<turnstile> A \<Longrightarrow> B\<close>}{\<open>\<Gamma> \<turnstile> B\<close>}
  \qquad
  \infer[\<open>(\<Longrightarrow>\<hyphen>elim)\<close>]{\<open>\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile> B\<close>}{\<open>\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B\<close> & \<open>\<Gamma>\<^sub>2 \<turnstile> A\<close>}
  \]
  \caption{Primitive inferences of Pure}\label{fig:prim-rules}
  \end{center}
  \end{figure}

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  \<open>\<turnstile> (\<lambda>x. b[x]) a \<equiv> b[a]\<close> & \<open>\<beta>\<close>-conversion \\
  \<open>\<turnstile> x \<equiv> x\<close> & reflexivity \\
  \<open>\<turnstile> x \<equiv> y \<Longrightarrow> P x \<Longrightarrow> P y\<close> & substitution \\
  \<open>\<turnstile> (\<And>x. f x \<equiv> g x) \<Longrightarrow> f \<equiv> g\<close> & extensionality \\
  \<open>\<turnstile> (A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<equiv> B\<close> & logical equivalence \\
  \end{tabular}
  \caption{Conceptual axiomatization of Pure equality}\label{fig:pure-equality}
  \end{center}
  \end{figure}

  The introduction and elimination rules for \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> are analogous to
  formation of dependently typed \<open>\<lambda>\<close>-terms representing the underlying proof
  objects. Proof terms are irrelevant in the Pure logic, though; they cannot
  occur within propositions. The system provides a runtime option to record
  explicit proof terms for primitive inferences, see also
  \secref{sec:proof-terms}. Thus all three levels of \<open>\<lambda>\<close>-calculus become
  explicit: \<open>\<Rightarrow>\<close> for terms, and \<open>\<And>/\<Longrightarrow>\<close> for proofs (cf.\ @{cite
  "Berghofer-Nipkow:2000:TPHOL"}).

  Observe that locally fixed parameters (as in \<open>\<And>\<hyphen>intro\<close>) need not be recorded
  in the hypotheses, because the simple syntactic types of Pure are always
  inhabitable. ``Assumptions'' \<open>x :: \<tau>\<close> for type-membership are only present
  as long as some \<open>x\<^sub>\<tau>\<close> occurs in the statement body.\<^footnote>\<open>This is the key
  difference to ``\<open>\<lambda>HOL\<close>'' in the PTS framework @{cite
  "Barendregt-Geuvers:2001"}, where hypotheses \<open>x : A\<close> are treated uniformly
  for propositions and types.\<close>

  \<^medskip>
  The axiomatization of a theory is implicitly closed by forming all instances
  of type and term variables: \<open>\<turnstile> A\<vartheta>\<close> holds for any substitution
  instance of an axiom \<open>\<turnstile> A\<close>. By pushing substitutions through derivations
  inductively, we also get admissible \<open>generalize\<close> and \<open>instantiate\<close> rules as
  shown in \figref{fig:subst-rules}.

  \begin{figure}[htb]
  \begin{center}
  \[
  \infer{\<open>\<Gamma> \<turnstile> B[?\<alpha>]\<close>}{\<open>\<Gamma> \<turnstile> B[\<alpha>]\<close> & \<open>\<alpha> \<notin> \<Gamma>\<close>}
  \quad
  \infer[\quad\<open>(generalize)\<close>]{\<open>\<Gamma> \<turnstile> B[?x]\<close>}{\<open>\<Gamma> \<turnstile> B[x]\<close> & \<open>x \<notin> \<Gamma>\<close>}
  \]
  \[
  \infer{\<open>\<Gamma> \<turnstile> B[\<tau>]\<close>}{\<open>\<Gamma> \<turnstile> B[?\<alpha>]\<close>}
  \quad
  \infer[\quad\<open>(instantiate)\<close>]{\<open>\<Gamma> \<turnstile> B[t]\<close>}{\<open>\<Gamma> \<turnstile> B[?x]\<close>}
  \]
  \caption{Admissible substitution rules}\label{fig:subst-rules}
  \end{center}
  \end{figure}

  Note that \<open>instantiate\<close> does not require an explicit side-condition, because
  \<open>\<Gamma>\<close> may never contain schematic variables.

  In principle, variables could be substituted in hypotheses as well, but this
  would disrupt the monotonicity of reasoning: deriving \<open>\<Gamma>\<vartheta> \<turnstile>
  B\<vartheta>\<close> from \<open>\<Gamma> \<turnstile> B\<close> is correct, but \<open>\<Gamma>\<vartheta> \<supseteq> \<Gamma>\<close> does not
  necessarily hold: the result belongs to a different proof context.

  \<^medskip> An \<^emph>\<open>oracle\<close> is a function that produces axioms on the fly. Logically,
  this is an instance of the \<open>axiom\<close> rule (\figref{fig:prim-rules}), but there
  is an operational difference. The inference kernel records oracle
  invocations within derivations of theorems by a unique tag. This also
  includes implicit type-class reasoning via the order-sorted algebra of class
  relations and type arities (see also @{command_ref instantiation} and
  @{command_ref instance}).

  Axiomatizations should be limited to the bare minimum, typically as part of
  the initial logical basis of an object-logic formalization. Later on,
  theories are usually developed in a strictly definitional fashion, by
  stating only certain equalities over new constants.

  A \<^emph>\<open>simple definition\<close> consists of a constant declaration \<open>c :: \<sigma>\<close> together
  with an axiom \<open>\<turnstile> c \<equiv> t\<close>, where \<open>t :: \<sigma>\<close> is a closed term without any hidden
  polymorphism. The RHS may depend on further defined constants, but not \<open>c\<close>
  itself. Definitions of functions may be presented as \<open>c \<^vec>x \<equiv> t\<close>
  instead of the puristic \<open>c \<equiv> \<lambda>\<^vec>x. t\<close>.

  An \<^emph>\<open>overloaded definition\<close> consists of a collection of axioms for the same
  constant, with zero or one equations \<open>c((\<^vec>\<alpha>)\<kappa>) \<equiv> t\<close> for each type
  constructor \<open>\<kappa>\<close> (for distinct variables \<open>\<^vec>\<alpha>\<close>). The RHS may mention
  previously defined constants as above, or arbitrary constants \<open>d(\<alpha>\<^sub>i)\<close> for
  some \<open>\<alpha>\<^sub>i\<close> projected from \<open>\<^vec>\<alpha>\<close>. Thus overloaded definitions
  essentially work by primitive recursion over the syntactic structure of a
  single type argument. See also @{cite \<open>\S4.3\<close>
  "Haftmann-Wenzel:2006:classes"}.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Logic.all: "term -> term -> term"} \\
  @{define_ML Logic.mk_implies: "term * term -> term"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML_type ctyp} \\
  @{define_ML_type cterm} \\
  @{define_ML Thm.ctyp_of: "Proof.context -> typ -> ctyp"} \\
  @{define_ML Thm.cterm_of: "Proof.context -> term -> cterm"} \\
  @{define_ML Thm.apply: "cterm -> cterm -> cterm"} \\
  @{define_ML Thm.lambda: "cterm -> cterm -> cterm"} \\
  @{define_ML Thm.all: "Proof.context -> cterm -> cterm -> cterm"} \\
  @{define_ML Drule.mk_implies: "cterm * cterm -> cterm"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML_type thm} \\
  @{define_ML Thm.transfer: "theory -> thm -> thm"} \\
  @{define_ML Thm.assume: "cterm -> thm"} \\
  @{define_ML Thm.forall_intr: "cterm -> thm -> thm"} \\
  @{define_ML Thm.forall_elim: "cterm -> thm -> thm"} \\
  @{define_ML Thm.implies_intr: "cterm -> thm -> thm"} \\
  @{define_ML Thm.implies_elim: "thm -> thm -> thm"} \\
  @{define_ML Thm.generalize: "string list * string list -> int -> thm -> thm"} \\
  @{define_ML Thm.instantiate: "((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list
  -> thm -> thm"} \\
  @{define_ML Thm.add_axiom: "Proof.context ->
  binding * term -> theory -> (string * thm) * theory"} \\
  @{define_ML Thm.add_oracle: "binding * ('a -> cterm) -> theory ->
  (string * ('a -> thm)) * theory"} \\
  @{define_ML Thm.add_def: "Defs.context -> bool -> bool ->
  binding * term -> theory -> (string * thm) * theory"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML Theory.add_deps: "Defs.context -> string ->
  Defs.entry -> Defs.entry list -> theory -> theory"} \\
  @{define_ML Thm_Deps.all_oracles: "thm list -> Proofterm.oracle list"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Logic.all\<close>~\<open>a B\<close> produces a Pure quantification \<open>\<And>a. B\<close>, where
  occurrences of the atomic term \<open>a\<close> in the body proposition \<open>B\<close> are replaced
  by bound variables. (See also \<^ML>\<open>lambda\<close> on terms.)

  \<^descr> \<^ML>\<open>Logic.mk_implies\<close>~\<open>(A, B)\<close> produces a Pure implication \<open>A \<Longrightarrow> B\<close>.

  \<^descr> Types \<^ML_type>\<open>ctyp\<close> and \<^ML_type>\<open>cterm\<close> represent certified types and
  terms, respectively. These are abstract datatypes that guarantee that its
  values have passed the full well-formedness (and well-typedness) checks,
  relative to the declarations of type constructors, constants etc.\ in the
  background theory. The abstract types \<^ML_type>\<open>ctyp\<close> and \<^ML_type>\<open>cterm\<close>
  are part of the same inference kernel that is mainly responsible for
  \<^ML_type>\<open>thm\<close>. Thus syntactic operations on \<^ML_type>\<open>ctyp\<close> and \<^ML_type>\<open>cterm\<close> are located in the \<^ML_structure>\<open>Thm\<close> module, even though theorems
  are not yet involved at that stage.

  \<^descr> \<^ML>\<open>Thm.ctyp_of\<close>~\<open>ctxt \<tau>\<close> and \<^ML>\<open>Thm.cterm_of\<close>~\<open>ctxt t\<close> explicitly
  check types and terms, respectively. This also involves some basic
  normalizations, such expansion of type and term abbreviations from the
  underlying theory context. Full re-certification is relatively slow and
  should be avoided in tight reasoning loops.

  \<^descr> \<^ML>\<open>Thm.apply\<close>, \<^ML>\<open>Thm.lambda\<close>, \<^ML>\<open>Thm.all\<close>, \<^ML>\<open>Drule.mk_implies\<close>
  etc.\ compose certified terms (or propositions) incrementally. This is
  equivalent to \<^ML>\<open>Thm.cterm_of\<close> after unchecked \<^ML_op>\<open>$\<close>, \<^ML>\<open>lambda\<close>,
  \<^ML>\<open>Logic.all\<close>, \<^ML>\<open>Logic.mk_implies\<close> etc., but there can be a big
  difference in performance when large existing entities are composed by a few
  extra constructions on top. There are separate operations to decompose
  certified terms and theorems to produce certified terms again.

  \<^descr> Type \<^ML_type>\<open>thm\<close> represents proven propositions. This is an abstract
  datatype that guarantees that its values have been constructed by basic
  principles of the \<^ML_structure>\<open>Thm\<close> module. Every \<^ML_type>\<open>thm\<close> value
  refers its background theory, cf.\ \secref{sec:context-theory}.

  \<^descr> \<^ML>\<open>Thm.transfer\<close>~\<open>thy thm\<close> transfers the given theorem to a \<^emph>\<open>larger\<close>
  theory, see also \secref{sec:context}. This formal adjustment of the
  background context has no logical significance, but is occasionally required
  for formal reasons, e.g.\ when theorems that are imported from more basic
  theories are used in the current situation.

  \<^descr> \<^ML>\<open>Thm.assume\<close>, \<^ML>\<open>Thm.forall_intr\<close>, \<^ML>\<open>Thm.forall_elim\<close>, \<^ML>\<open>Thm.implies_intr\<close>, and \<^ML>\<open>Thm.implies_elim\<close> correspond to the primitive
  inferences of \figref{fig:prim-rules}.

  \<^descr> \<^ML>\<open>Thm.generalize\<close>~\<open>(\<^vec>\<alpha>, \<^vec>x)\<close> corresponds to the
  \<open>generalize\<close> rules of \figref{fig:subst-rules}. Here collections of type and
  term variables are generalized simultaneously, specified by the given basic
  names.

  \<^descr> \<^ML>\<open>Thm.instantiate\<close>~\<open>(\<^vec>\<alpha>\<^sub>s, \<^vec>x\<^sub>\<tau>)\<close> corresponds to the
  \<open>instantiate\<close> rules of \figref{fig:subst-rules}. Type variables are
  substituted before term variables. Note that the types in \<open>\<^vec>x\<^sub>\<tau>\<close> refer
  to the instantiated versions.

  \<^descr> \<^ML>\<open>Thm.add_axiom\<close>~\<open>ctxt (name, A)\<close> declares an arbitrary proposition as
  axiom, and retrieves it as a theorem from the resulting theory, cf.\ \<open>axiom\<close>
  in \figref{fig:prim-rules}. Note that the low-level representation in the
  axiom table may differ slightly from the returned theorem.

  \<^descr> \<^ML>\<open>Thm.add_oracle\<close>~\<open>(binding, oracle)\<close> produces a named oracle rule,
  essentially generating arbitrary axioms on the fly, cf.\ \<open>axiom\<close> in
  \figref{fig:prim-rules}.

  \<^descr> \<^ML>\<open>Thm.add_def\<close>~\<open>ctxt unchecked overloaded (name, c \<^vec>x \<equiv> t)\<close>
  states a definitional axiom for an existing constant \<open>c\<close>. Dependencies are
  recorded via \<^ML>\<open>Theory.add_deps\<close>, unless the \<open>unchecked\<close> option is set.
  Note that the low-level representation in the axiom table may differ
  slightly from the returned theorem.

  \<^descr> \<^ML>\<open>Theory.add_deps\<close>~\<open>ctxt name c\<^sub>\<tau> \<^vec>d\<^sub>\<sigma>\<close> declares dependencies of
  a named specification for constant \<open>c\<^sub>\<tau>\<close>, relative to existing
  specifications for constants \<open>\<^vec>d\<^sub>\<sigma>\<close>. This also works for type
  constructors.

  \<^descr> \<^ML>\<open>Thm_Deps.all_oracles\<close>~\<open>thms\<close> returns all oracles used in the
  internal derivation of the given theorems; this covers the full graph of
  transitive dependencies. The result contains an authentic oracle name; if
  @{ML Proofterm.proofs} was at least @{ML 1} during the oracle inference, it
  also contains the position of the oracle invocation and its proposition. See
  also the command @{command_ref "thm_oracles"}.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "ctyp"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "cterm"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "cprop"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "thm"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "thms"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "lemma"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "oracle_name"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation ctyp} typ
  ;
  @@{ML_antiquotation cterm} term
  ;
  @@{ML_antiquotation cprop} prop
  ;
  @@{ML_antiquotation thm} thm
  ;
  @@{ML_antiquotation thms} thms
  ;
  @@{ML_antiquotation lemma} ('(' @'open' ')')? ((prop +) + @'and') \<newline>
    @'by' method method?
  ;
  @@{ML_antiquotation oracle_name} embedded
  \<close>

  \<^descr> \<open>@{ctyp \<tau>}\<close> produces a certified type wrt.\ the current background theory
  --- as abstract value of type \<^ML_type>\<open>ctyp\<close>.

  \<^descr> \<open>@{cterm t}\<close> and \<open>@{cprop \<phi>}\<close> produce a certified term wrt.\ the current
  background theory --- as abstract value of type \<^ML_type>\<open>cterm\<close>.

  \<^descr> \<open>@{thm a}\<close> produces a singleton fact --- as abstract value of type
  \<^ML_type>\<open>thm\<close>.

  \<^descr> \<open>@{thms a}\<close> produces a general fact --- as abstract value of type
  \<^ML_type>\<open>thm list\<close>.

  \<^descr> \<open>@{lemma \<phi> by meth}\<close> produces a fact that is proven on the spot according
  to the minimal proof, which imitates a terminal Isar proof. The result is an
  abstract value of type \<^ML_type>\<open>thm\<close> or \<^ML_type>\<open>thm list\<close>, depending on
  the number of propositions given here.

  The internal derivation object lacks a proper theorem name, but it is
  formally closed, unless the \<open>(open)\<close> option is specified (this may impact
  performance of applications with proof terms).

  Since ML antiquotations are always evaluated at compile-time, there is no
  run-time overhead even for non-trivial proofs. Nonetheless, the
  justification is syntactically limited to a single @{command "by"} step.
  More complex Isar proofs should be done in regular theory source, before
  compiling the corresponding ML text that uses the result.

  \<^descr> \<open>@{oracle_name a}\<close> inlines the internalized oracle name \<open>a\<close> --- as
  \<^ML_type>\<open>string\<close> literal.
\<close>


subsection \<open>Auxiliary connectives \label{sec:logic-aux}\<close>

text \<open>
  Theory \<open>Pure\<close> provides a few auxiliary connectives that are defined on top
  of the primitive ones, see \figref{fig:pure-aux}. These special constants
  are useful in certain internal encodings, and are normally not directly
  exposed to the user.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{ll}
  \<open>conjunction :: prop \<Rightarrow> prop \<Rightarrow> prop\<close> & (infix \<open>&&&\<close>) \\
  \<open>\<turnstile> A &&& B \<equiv> (\<And>C. (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C)\<close> \\[1ex]
  \<open>prop :: prop \<Rightarrow> prop\<close> & (prefix \<open>#\<close>, suppressed) \\
  \<open>#A \<equiv> A\<close> \\[1ex]
  \<open>term :: \<alpha> \<Rightarrow> prop\<close> & (prefix \<open>TERM\<close>) \\
  \<open>term x \<equiv> (\<And>A. A \<Longrightarrow> A)\<close> \\[1ex]
  \<open>type :: \<alpha> itself\<close> & (prefix \<open>TYPE\<close>) \\
  \<open>(unspecified)\<close> \\
  \end{tabular}
  \caption{Definitions of auxiliary connectives}\label{fig:pure-aux}
  \end{center}
  \end{figure}

  The introduction \<open>A \<Longrightarrow> B \<Longrightarrow> A &&& B\<close>, and eliminations (projections) \<open>A &&& B
  \<Longrightarrow> A\<close> and \<open>A &&& B \<Longrightarrow> B\<close> are available as derived rules. Conjunction allows to
  treat simultaneous assumptions and conclusions uniformly, e.g.\ consider \<open>A
  \<Longrightarrow> B \<Longrightarrow> C &&& D\<close>. In particular, the goal mechanism represents multiple claims
  as explicit conjunction internally, but this is refined (via backwards
  introduction) into separate sub-goals before the user commences the proof;
  the final result is projected into a list of theorems using eliminations
  (cf.\ \secref{sec:tactical-goals}).

  The \<open>prop\<close> marker (\<open>#\<close>) makes arbitrarily complex propositions appear as
  atomic, without changing the meaning: \<open>\<Gamma> \<turnstile> A\<close> and \<open>\<Gamma> \<turnstile> #A\<close> are
  interchangeable. See \secref{sec:tactical-goals} for specific operations.

  The \<open>term\<close> marker turns any well-typed term into a derivable proposition: \<open>\<turnstile>
  TERM t\<close> holds unconditionally. Although this is logically vacuous, it allows
  to treat terms and proofs uniformly, similar to a type-theoretic framework.

  The \<open>TYPE\<close> constructor is the canonical representative of the unspecified
  type \<open>\<alpha> itself\<close>; it essentially injects the language of types into that of
  terms. There is specific notation \<open>TYPE(\<tau>)\<close> for \<open>TYPE\<^bsub>\<tau> itself\<^esub>\<close>. Although
  being devoid of any particular meaning, the term \<open>TYPE(\<tau>)\<close> accounts for the
  type \<open>\<tau>\<close> within the term language. In particular, \<open>TYPE(\<alpha>)\<close> may be used as
  formal argument in primitive definitions, in order to circumvent hidden
  polymorphism (cf.\ \secref{sec:terms}). For example, \<open>c TYPE(\<alpha>) \<equiv> A[\<alpha>]\<close>
  defines \<open>c :: \<alpha> itself \<Rightarrow> prop\<close> in terms of a proposition \<open>A\<close> that depends on
  an additional type argument, which is essentially a predicate on types.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Conjunction.intr: "thm -> thm -> thm"} \\
  @{define_ML Conjunction.elim: "thm -> thm * thm"} \\
  @{define_ML Drule.mk_term: "cterm -> thm"} \\
  @{define_ML Drule.dest_term: "thm -> cterm"} \\
  @{define_ML Logic.mk_type: "typ -> term"} \\
  @{define_ML Logic.dest_type: "term -> typ"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Conjunction.intr\<close> derives \<open>A &&& B\<close> from \<open>A\<close> and \<open>B\<close>.

  \<^descr> \<^ML>\<open>Conjunction.elim\<close> derives \<open>A\<close> and \<open>B\<close> from \<open>A &&& B\<close>.

  \<^descr> \<^ML>\<open>Drule.mk_term\<close> derives \<open>TERM t\<close>.

  \<^descr> \<^ML>\<open>Drule.dest_term\<close> recovers term \<open>t\<close> from \<open>TERM t\<close>.

  \<^descr> \<^ML>\<open>Logic.mk_type\<close>~\<open>\<tau>\<close> produces the term \<open>TYPE(\<tau>)\<close>.

  \<^descr> \<^ML>\<open>Logic.dest_type\<close>~\<open>TYPE(\<tau>)\<close> recovers the type \<open>\<tau>\<close>.
\<close>


subsection \<open>Sort hypotheses\<close>

text \<open>
  Type variables are decorated with sorts, as explained in \secref{sec:types}.
  This constrains type instantiation to certain ranges of types: variable
  \<open>\<alpha>\<^sub>s\<close> may only be assigned to types \<open>\<tau>\<close> that belong to sort \<open>s\<close>. Within the
  logic, sort constraints act like implicit preconditions on the result \<open>\<lparr>\<alpha>\<^sub>1
  : s\<^sub>1\<rparr>, \<dots>, \<lparr>\<alpha>\<^sub>n : s\<^sub>n\<rparr>, \<Gamma> \<turnstile> \<phi>\<close> where the type variables \<open>\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n\<close> cover
  the propositions \<open>\<Gamma>\<close>, \<open>\<phi>\<close>, as well as the proof of \<open>\<Gamma> \<turnstile> \<phi>\<close>.

  These \<^emph>\<open>sort hypothesis\<close> of a theorem are passed monotonically through
  further derivations. They are redundant, as long as the statement of a
  theorem still contains the type variables that are accounted here. The
  logical significance of sort hypotheses is limited to the boundary case
  where type variables disappear from the proposition, e.g.\ \<open>\<lparr>\<alpha>\<^sub>s : s\<rparr> \<turnstile> \<phi>\<close>.
  Since such dangling type variables can be renamed arbitrarily without
  changing the proposition \<open>\<phi>\<close>, the inference kernel maintains sort hypotheses
  in anonymous form \<open>s \<turnstile> \<phi>\<close>.

  In most practical situations, such extra sort hypotheses may be stripped in
  a final bookkeeping step, e.g.\ at the end of a proof: they are typically
  left over from intermediate reasoning with type classes that can be
  satisfied by some concrete type \<open>\<tau>\<close> of sort \<open>s\<close> to replace the hypothetical
  type variable \<open>\<alpha>\<^sub>s\<close>.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Thm.extra_shyps: "thm -> sort list"} \\
  @{define_ML Thm.strip_shyps: "thm -> thm"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Thm.extra_shyps\<close>~\<open>thm\<close> determines the extraneous sort hypotheses of
  the given theorem, i.e.\ the sorts that are not present within type
  variables of the statement.

  \<^descr> \<^ML>\<open>Thm.strip_shyps\<close>~\<open>thm\<close> removes any extraneous sort hypotheses that
  can be witnessed from the type signature.
\<close>

text %mlex \<open>
  The following artificial example demonstrates the derivation of \<^prop>\<open>False\<close> with a pending sort hypothesis involving a logically empty sort.
\<close>

class empty =
  assumes bad: "\<And>(x::'a) y. x \<noteq> y"

theorem (in empty) false: False
  using bad by blast

ML_val \<open>\<^assert> (Thm.extra_shyps @{thm false} = [\<^sort>\<open>empty\<close>])\<close>

text \<open>
  Thanks to the inference kernel managing sort hypothesis according to their
  logical significance, this example is merely an instance of \<^emph>\<open>ex falso
  quodlibet consequitur\<close> --- not a collapse of the logical framework!
\<close>


section \<open>Object-level rules \label{sec:obj-rules}\<close>

text \<open>
  The primitive inferences covered so far mostly serve foundational purposes.
  User-level reasoning usually works via object-level rules that are
  represented as theorems of Pure. Composition of rules involves
  \<^emph>\<open>backchaining\<close>, \<^emph>\<open>higher-order unification\<close> modulo \<open>\<alpha>\<beta>\<eta>\<close>-conversion of
  \<open>\<lambda>\<close>-terms, and so-called \<^emph>\<open>lifting\<close> of rules into a context of \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close>
  connectives. Thus the full power of higher-order Natural Deduction in
  Isabelle/Pure becomes readily available.
\<close>


subsection \<open>Hereditary Harrop Formulae\<close>

text \<open>
  The idea of object-level rules is to model Natural Deduction inferences in
  the style of Gentzen @{cite "Gentzen:1935"}, but we allow arbitrary nesting
  similar to @{cite "Schroeder-Heister:1984"}. The most basic rule format is
  that of a \<^emph>\<open>Horn Clause\<close>:
  \[
  \infer{\<open>A\<close>}{\<open>A\<^sub>1\<close> & \<open>\<dots>\<close> & \<open>A\<^sub>n\<close>}
  \]
  where \<open>A, A\<^sub>1, \<dots>, A\<^sub>n\<close> are atomic propositions of the framework, usually of
  the form \<open>Trueprop B\<close>, where \<open>B\<close> is a (compound) object-level statement.
  This object-level inference corresponds to an iterated implication in Pure
  like this:
  \[
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> A\<close>
  \]
  As an example consider conjunction introduction: \<open>A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>. Any
  parameters occurring in such rule statements are conceptionally treated as
  arbitrary:
  \[
  \<open>\<And>x\<^sub>1 \<dots> x\<^sub>m. A\<^sub>1 x\<^sub>1 \<dots> x\<^sub>m \<Longrightarrow> \<dots> A\<^sub>n x\<^sub>1 \<dots> x\<^sub>m \<Longrightarrow> A x\<^sub>1 \<dots> x\<^sub>m\<close>
  \]

  Nesting of rules means that the positions of \<open>A\<^sub>i\<close> may again hold compound
  rules, not just atomic propositions. Propositions of this format are called
  \<^emph>\<open>Hereditary Harrop Formulae\<close> in the literature @{cite "Miller:1991"}. Here
  we give an inductive characterization as follows:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>\<^bold>x\<close> & set of variables \\
  \<open>\<^bold>A\<close> & set of atomic propositions \\
  \<open>\<^bold>H  =  \<And>\<^bold>x\<^sup>*. \<^bold>H\<^sup>* \<Longrightarrow> \<^bold>A\<close> & set of Hereditary Harrop Formulas \\
  \end{tabular}
  \<^medskip>

  Thus we essentially impose nesting levels on propositions formed from \<open>\<And>\<close>
  and \<open>\<Longrightarrow>\<close>. At each level there is a prefix of parameters and compound
  premises, concluding an atomic proposition. Typical examples are
  \<open>\<longrightarrow>\<close>-introduction \<open>(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B\<close> or mathematical induction \<open>P 0 \<Longrightarrow> (\<And>n. P n
  \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n\<close>. Even deeper nesting occurs in well-founded induction
  \<open>(\<And>x. (\<And>y. y \<prec> x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P x\<close>, but this already marks the limit of
  rule complexity that is usually seen in practice.

  \<^medskip>
  Regular user-level inferences in Isabelle/Pure always maintain the following
  canonical form of results:

  \<^item> Normalization by \<open>(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)\<close>, which is a theorem of
  Pure, means that quantifiers are pushed in front of implication at each
  level of nesting. The normal form is a Hereditary Harrop Formula.

  \<^item> The outermost prefix of parameters is represented via schematic variables:
  instead of \<open>\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> A \<^vec>x\<close> we have \<open>\<^vec>H
  ?\<^vec>x \<Longrightarrow> A ?\<^vec>x\<close>. Note that this representation looses information
  about the order of parameters, and vacuous quantifiers vanish automatically.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Simplifier.norm_hhf: "Proof.context -> thm -> thm"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Simplifier.norm_hhf\<close>~\<open>ctxt thm\<close> normalizes the given theorem
  according to the canonical form specified above. This is occasionally
  helpful to repair some low-level tools that do not handle Hereditary Harrop
  Formulae properly.
\<close>


subsection \<open>Rule composition\<close>

text \<open>
  The rule calculus of Isabelle/Pure provides two main inferences: @{inference
  resolution} (i.e.\ back-chaining of rules) and @{inference assumption}
  (i.e.\ closing a branch), both modulo higher-order unification. There are
  also combined variants, notably @{inference elim_resolution} and @{inference
  dest_resolution}.

  To understand the all-important @{inference resolution} principle, we first
  consider raw @{inference_def composition} (modulo higher-order unification
  with substitution \<open>\<vartheta>\<close>):
  \[
  \infer[(@{inference_def composition})]{\<open>\<^vec>A\<vartheta> \<Longrightarrow> C\<vartheta>\<close>}
  {\<open>\<^vec>A \<Longrightarrow> B\<close> & \<open>B' \<Longrightarrow> C\<close> & \<open>B\<vartheta> = B'\<vartheta>\<close>}
  \]
  Here the conclusion of the first rule is unified with the premise of the
  second; the resulting rule instance inherits the premises of the first and
  conclusion of the second. Note that \<open>C\<close> can again consist of iterated
  implications. We can also permute the premises of the second rule
  back-and-forth in order to compose with \<open>B'\<close> in any position (subsequently
  we shall always refer to position 1 w.l.o.g.).

  In @{inference composition} the internal structure of the common part \<open>B\<close>
  and \<open>B'\<close> is not taken into account. For proper @{inference resolution} we
  require \<open>B\<close> to be atomic, and explicitly observe the structure \<open>\<And>\<^vec>x.
  \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x\<close> of the premise of the second rule. The idea
  is to adapt the first rule by ``lifting'' it into this context, by means of
  iterated application of the following inferences:
  \[
  \infer[(@{inference_def imp_lift})]{\<open>(\<^vec>H \<Longrightarrow> \<^vec>A) \<Longrightarrow> (\<^vec>H \<Longrightarrow> B)\<close>}{\<open>\<^vec>A \<Longrightarrow> B\<close>}
  \]
  \[
  \infer[(@{inference_def all_lift})]{\<open>(\<And>\<^vec>x. \<^vec>A (?\<^vec>a \<^vec>x)) \<Longrightarrow> (\<And>\<^vec>x. B (?\<^vec>a \<^vec>x))\<close>}{\<open>\<^vec>A ?\<^vec>a \<Longrightarrow> B ?\<^vec>a\<close>}
  \]
  By combining raw composition with lifting, we get full @{inference
  resolution} as follows:
  \[
  \infer[(@{inference_def resolution})]
  {\<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> \<^vec>A (?\<^vec>a \<^vec>x))\<vartheta> \<Longrightarrow> C\<vartheta>\<close>}
  {\begin{tabular}{l}
    \<open>\<^vec>A ?\<^vec>a \<Longrightarrow> B ?\<^vec>a\<close> \\
    \<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C\<close> \\
    \<open>(\<lambda>\<^vec>x. B (?\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>\<close> \\
   \end{tabular}}
  \]

  Continued resolution of rules allows to back-chain a problem towards more
  and sub-problems. Branches are closed either by resolving with a rule of 0
  premises, or by producing a ``short-circuit'' within a solved situation
  (again modulo unification):
  \[
  \infer[(@{inference_def assumption})]{\<open>C\<vartheta>\<close>}
  {\<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> A \<^vec>x) \<Longrightarrow> C\<close> & \<open>A\<vartheta> = H\<^sub>i\<vartheta>\<close>~~\mbox{(for some~\<open>i\<close>)}}
  \]

  %FIXME @{inference_def elim_resolution}, @{inference_def dest_resolution}
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_infix "RSN": "thm * (int * thm) -> thm"} \\
  @{define_ML_infix "RS": "thm * thm -> thm"} \\

  @{define_ML_infix "RLN": "thm list * (int * thm list) -> thm list"} \\
  @{define_ML_infix "RL": "thm list * thm list -> thm list"} \\

  @{define_ML_infix "MRS": "thm list * thm -> thm"} \\
  @{define_ML_infix "OF": "thm * thm list -> thm"} \\
  \end{mldecls}

  \<^descr> \<open>rule\<^sub>1 RSN (i, rule\<^sub>2)\<close> resolves the conclusion of \<open>rule\<^sub>1\<close> with the
  \<open>i\<close>-th premise of \<open>rule\<^sub>2\<close>, according to the @{inference resolution}
  principle explained above. Unless there is precisely one resolvent it raises
  exception \<^ML>\<open>THM\<close>.

  This corresponds to the rule attribute @{attribute THEN} in Isar source
  language.

  \<^descr> \<open>rule\<^sub>1 RS rule\<^sub>2\<close> abbreviates \<open>rule\<^sub>1 RSN (1, rule\<^sub>2)\<close>.

  \<^descr> \<open>rules\<^sub>1 RLN (i, rules\<^sub>2)\<close> joins lists of rules. For every \<open>rule\<^sub>1\<close> in
  \<open>rules\<^sub>1\<close> and \<open>rule\<^sub>2\<close> in \<open>rules\<^sub>2\<close>, it resolves the conclusion of \<open>rule\<^sub>1\<close>
  with the \<open>i\<close>-th premise of \<open>rule\<^sub>2\<close>, accumulating multiple results in one
  big list. Note that such strict enumerations of higher-order unifications
  can be inefficient compared to the lazy variant seen in elementary tactics
  like \<^ML>\<open>resolve_tac\<close>.

  \<^descr> \<open>rules\<^sub>1 RL rules\<^sub>2\<close> abbreviates \<open>rules\<^sub>1 RLN (1, rules\<^sub>2)\<close>.

  \<^descr> \<open>[rule\<^sub>1, \<dots>, rule\<^sub>n] MRS rule\<close> resolves \<open>rule\<^sub>i\<close> against premise \<open>i\<close> of
  \<open>rule\<close>, for \<open>i = n, \<dots>, 1\<close>. By working from right to left, newly emerging
  premises are concatenated in the result, without interfering.

  \<^descr> \<open>rule OF rules\<close> is an alternative notation for \<open>rules MRS rule\<close>, which
  makes rule composition look more like function application. Note that the
  argument \<open>rules\<close> need not be atomic.

  This corresponds to the rule attribute @{attribute OF} in Isar source
  language.
\<close>


section \<open>Proof terms \label{sec:proof-terms}\<close>

text \<open>
  The Isabelle/Pure inference kernel can record the proof of each theorem as a
  proof term that contains all logical inferences in detail. Rule composition
  by resolution (\secref{sec:obj-rules}) and type-class reasoning is broken
  down to primitive rules of the logical framework. The proof term can be
  inspected by a separate proof-checker, for example.

  According to the well-known \<^emph>\<open>Curry-Howard isomorphism\<close>, a proof can be
  viewed as a \<open>\<lambda>\<close>-term. Following this idea, proofs in Isabelle are internally
  represented by a datatype similar to the one for terms described in
  \secref{sec:terms}. On top of these syntactic terms, two more layers of
  \<open>\<lambda>\<close>-calculus are added, which correspond to \<open>\<And>x :: \<alpha>. B x\<close> and \<open>A \<Longrightarrow> B\<close>
  according to the propositions-as-types principle. The resulting 3-level
  \<open>\<lambda>\<close>-calculus resembles ``\<open>\<lambda>HOL\<close>'' in the more abstract setting of Pure Type
  Systems (PTS) @{cite "Barendregt-Geuvers:2001"}, if some fine points like
  schematic polymorphism and type classes are ignored.

  \<^medskip>
  \<^emph>\<open>Proof abstractions\<close> of the form \<open>\<^bold>\<lambda>x :: \<alpha>. prf\<close> or \<open>\<^bold>\<lambda>p : A. prf\<close>
  correspond to introduction of \<open>\<And>\<close>/\<open>\<Longrightarrow>\<close>, and \<^emph>\<open>proof applications\<close> of the form
  \<open>p \<cdot> t\<close> or \<open>p \<bullet> q\<close> correspond to elimination of \<open>\<And>\<close>/\<open>\<Longrightarrow>\<close>. Actual types \<open>\<alpha>\<close>,
  propositions \<open>A\<close>, and terms \<open>t\<close> might be suppressed and reconstructed from
  the overall proof term.

  \<^medskip>
  Various atomic proofs indicate special situations within the proof
  construction as follows.

  A \<^emph>\<open>bound proof variable\<close> is a natural number \<open>b\<close> that acts as de-Bruijn
  index for proof term abstractions.

  A \<^emph>\<open>minimal proof\<close> ``\<open>?\<close>'' is a dummy proof term. This indicates some
  unrecorded part of the proof.

  \<open>Hyp A\<close> refers to some pending hypothesis by giving its proposition. This
  indicates an open context of implicit hypotheses, similar to loose bound
  variables or free variables within a term (\secref{sec:terms}).

  An \<^emph>\<open>axiom\<close> or \<^emph>\<open>oracle\<close> \<open>a : A[\<^vec>\<tau>]\<close> refers some postulated \<open>proof
  constant\<close>, which is subject to schematic polymorphism of theory content, and
  the particular type instantiation may be given explicitly. The vector of
  types \<open>\<^vec>\<tau>\<close> refers to the schematic type variables in the generic
  proposition \<open>A\<close> in canonical order.

  A \<^emph>\<open>proof promise\<close> \<open>a : A[\<^vec>\<tau>]\<close> is a placeholder for some proof of
  polymorphic proposition \<open>A\<close>, with explicit type instantiation as given by
  the vector \<open>\<^vec>\<tau>\<close>, as above. Unlike axioms or oracles, proof promises
  may be \<^emph>\<open>fulfilled\<close> eventually, by substituting \<open>a\<close> by some particular proof
  \<open>q\<close> at the corresponding type instance. This acts like Hindley-Milner
  \<open>let\<close>-polymorphism: a generic local proof definition may get used at
  different type instances, and is replaced by the concrete instance
  eventually.

  A \<^emph>\<open>named theorem\<close> wraps up some concrete proof as a closed formal entity,
  in the manner of constant definitions for proof terms. The \<^emph>\<open>proof body\<close> of
  such boxed theorems involves some digest about oracles and promises
  occurring in the original proof. This allows the inference kernel to manage
  this critical information without the full overhead of explicit proof terms.
\<close>


subsection \<open>Reconstructing and checking proof terms\<close>

text \<open>
  Fully explicit proof terms can be large, but most of this information is
  redundant and can be reconstructed from the context. Therefore, the
  Isabelle/Pure inference kernel records only \<^emph>\<open>implicit\<close> proof terms, by
  omitting all typing information in terms, all term and type labels of proof
  abstractions, and some argument terms of applications \<open>p \<cdot> t\<close> (if possible).

  There are separate operations to reconstruct the full proof term later on,
  using \<^emph>\<open>higher-order pattern unification\<close> @{cite "nipkow-patterns" and
  "Berghofer-Nipkow:2000:TPHOL"}.

  The \<^emph>\<open>proof checker\<close> expects a fully reconstructed proof term, and can turn
  it into a theorem by replaying its primitive inferences within the kernel.
\<close>


subsection \<open>Concrete syntax of proof terms\<close>

text \<open>
  The concrete syntax of proof terms is a slight extension of the regular
  inner syntax of Isabelle/Pure @{cite "isabelle-isar-ref"}. Its main
  syntactic category @{syntax (inner) proof} is defined as follows:

  \begin{center}
  \begin{supertabular}{rclr}

  @{syntax_def (inner) proof} & = & \<open>\<^bold>\<lambda>\<close> \<open>params\<close> \<^verbatim>\<open>.\<close> \<open>proof\<close> \\
    & \<open>|\<close> & \<open>proof\<close> \<open>\<cdot>\<close> \<open>any\<close> \\
    & \<open>|\<close> & \<open>proof\<close> \<open>\<bullet>\<close> \<open>proof\<close> \\
    & \<open>|\<close> & \<open>id  |  longid\<close> \\
  \\

  \<open>param\<close> & = & \<open>idt\<close> \\
    & \<open>|\<close> & \<open>idt\<close> \<^verbatim>\<open>:\<close> \<open>prop\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>(\<close> \<open>param\<close> \<^verbatim>\<open>)\<close> \\
  \\

  \<open>params\<close> & = & \<open>param\<close> \\
    & \<open>|\<close> & \<open>param\<close> \<open>params\<close> \\

  \end{supertabular}
  \end{center}

  Implicit term arguments in partial proofs are indicated by ``\<open>_\<close>''. Type
  arguments for theorems and axioms may be specified using \<open>p \<cdot> TYPE(type)\<close>
  (they must appear before any other term argument of a theorem or axiom, but
  may be omitted altogether).

  \<^medskip>
  There are separate read and print operations for proof terms, in order to
  avoid conflicts with the regular term language.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type proof} \\
  @{define_ML_type proof_body} \\
  @{define_ML Proofterm.proofs: "int Unsynchronized.ref"} \\
  @{define_ML Proofterm.reconstruct_proof:
  "theory -> term -> proof -> proof"} \\
  @{define_ML Proofterm.expand_proof: "theory ->
  (Proofterm.thm_header -> string option) -> proof -> proof"} \\
  @{define_ML Proof_Checker.thm_of_proof: "theory -> proof -> thm"} \\
  @{define_ML Proof_Syntax.read_proof: "theory -> bool -> bool -> string -> proof"} \\
  @{define_ML Proof_Syntax.pretty_proof: "Proof.context -> proof -> Pretty.T"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>proof\<close> represents proof terms; this is a datatype with
  constructors @{define_ML Abst}, @{define_ML AbsP}, @{define_ML_infix "%"},
  @{define_ML_infix "%%"}, @{define_ML PBound}, @{define_ML MinProof}, @{define_ML
  Hyp}, @{define_ML PAxm}, @{define_ML Oracle}, @{define_ML PThm} as explained
  above. %FIXME PClass (!?)

  \<^descr> Type \<^ML_type>\<open>proof_body\<close> represents the nested proof information of a
  named theorem, consisting of a digest of oracles and named theorem over some
  proof term. The digest only covers the directly visible part of the proof:
  in order to get the full information, the implicit graph of nested theorems
  needs to be traversed (e.g.\ using \<^ML>\<open>Proofterm.fold_body_thms\<close>).

  \<^descr> \<^ML>\<open>Thm.proof_of\<close>~\<open>thm\<close> and \<^ML>\<open>Thm.proof_body_of\<close>~\<open>thm\<close> produce the
  proof term or proof body (with digest of oracles and theorems) from a given
  theorem. Note that this involves a full join of internal futures that
  fulfill pending proof promises, and thus disrupts the natural bottom-up
  construction of proofs by introducing dynamic ad-hoc dependencies. Parallel
  performance may suffer by inspecting proof terms at run-time.

  \<^descr> \<^ML>\<open>Proofterm.proofs\<close> specifies the detail of proof recording within
  \<^ML_type>\<open>thm\<close> values produced by the inference kernel: \<^ML>\<open>0\<close> records only
  the names of oracles, \<^ML>\<open>1\<close> records oracle names and propositions, \<^ML>\<open>2\<close>
  additionally records full proof terms. Officially named theorems that
  contribute to a result are recorded in any case.

  \<^descr> \<^ML>\<open>Proofterm.reconstruct_proof\<close>~\<open>thy prop prf\<close> turns the implicit
  proof term \<open>prf\<close> into a full proof of the given proposition.

  Reconstruction may fail if \<open>prf\<close> is not a proof of \<open>prop\<close>, or if it does not
  contain sufficient information for reconstruction. Failure may only happen
  for proofs that are constructed manually, but not for those produced
  automatically by the inference kernel.

  \<^descr> \<^ML>\<open>Proofterm.expand_proof\<close>~\<open>thy expand prf\<close> reconstructs and expands
  the proofs of nested theorems according to the given \<open>expand\<close> function: a
  result of @{ML \<open>SOME ""\<close>} means full expansion, @{ML \<open>SOME\<close>}~\<open>name\<close> means to
  keep the theorem node but replace its internal name, @{ML NONE} means no
  change.

  \<^descr> \<^ML>\<open>Proof_Checker.thm_of_proof\<close>~\<open>thy prf\<close> turns the given (full) proof
  into a theorem, by replaying it using only primitive rules of the inference
  kernel.

  \<^descr> \<^ML>\<open>Proof_Syntax.read_proof\<close>~\<open>thy b\<^sub>1 b\<^sub>2 s\<close> reads in a proof term. The
  Boolean flags indicate the use of sort and type information. Usually, typing
  information is left implicit and is inferred during proof reconstruction.
  %FIXME eliminate flags!?

  \<^descr> \<^ML>\<open>Proof_Syntax.pretty_proof\<close>~\<open>ctxt prf\<close> pretty-prints the given proof
  term.
\<close>

text %mlex \<open>
  \<^item> \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close> provides basic examples involving
  proof terms.

  \<^item> \<^file>\<open>~~/src/HOL/Proofs/ex/XML_Data.thy\<close> demonstrates export and import of
  proof terms via XML/ML data representation.
\<close>

end

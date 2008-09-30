theory Program
imports Introduction
begin

section {* Turning Theories into Programs \label{sec:program} *}

subsection {* The @{text "Isabelle/HOL"} default setup *}

subsection {* Selecting code equations *}

text {*
  We have already seen how by default equations stemming from
  @{command definition}/@{command primrec}/@{command fun}
  statements are used for code generation.  Deviating from this
  \emph{default} behaviour is always possible -- e.g.~we
  could provide an alternative @{text fun} for @{const dequeue} proving
  the following equations explicitly:
*}

lemma %quoteme [code func]:
  "dequeue (Queue xs []) = (if xs = [] then (None, Queue [] []) else dequeue (Queue [] (rev xs)))"
  "dequeue (Queue xs (y # ys)) = (Some y, Queue xs ys)"
  by (cases xs, simp_all) (cases "rev xs", simp_all)

text {*
  \noindent The annotation @{text "[code func]"} is an @{text Isar}
  @{text attribute} which states that the given theorems should be
  considered as defining equations for a @{text fun} statement --
  the corresponding constant is determined syntactically.  The resulting code:
*}

text %quoteme {*@{code_stmts empty enqueue dequeue (Haskell)}*}

text {*
  \noindent You may note that the equality test @{term "xs = []"} has been
  replaced by the predicate @{term "null xs"}.  This is due to the default
  setup in the \qn{preprocessor} to be discussed further below (\secref{sec:preproc}).

  Changing the default constructor set of datatypes is also
  possible but rarely desired in practice.  See \secref{sec:datatypes} for an example.

  As told in \secref{sec:concept}, code generation is based
  on a structured collection of code theorems.
  For explorative purpose, this collection
  may be inspected using the @{command code_thms} command:
*}

code_thms %quoteme dequeue

text {*
  \noindent prints a table with \emph{all} defining equations
  for @{const dequeue}, including
  \emph{all} defining equations those equations depend
  on recursively.
  
  Similarly, the @{command code_deps} command shows a graph
  visualising dependencies between defining equations.
*}

subsection {* @{text class} and @{text instantiation} *}

text {*
  Concerning type classes and code generation, let us again examine an example
  from abstract algebra:
*}

class %quoteme semigroup = type +
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class %quoteme monoid = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"
    and neutr: "x \<otimes> \<one> = x"

instantiation %quoteme nat :: monoid
begin

primrec %quoteme mult_nat where
    "0 \<otimes> n = (0\<Colon>nat)"
  | "Suc m \<otimes> n = n + m \<otimes> n"

definition %quoteme neutral_nat where
  "\<one> = Suc 0"

lemma %quoteme add_mult_distrib:
  fixes n m q :: nat
  shows "(n + m) \<otimes> q = n \<otimes> q + m \<otimes> q"
  by (induct n) simp_all

instance %quoteme proof
  fix m n q :: nat
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) (simp_all add: add_mult_distrib)
  show "\<one> \<otimes> n = n"
    by (simp add: neutral_nat_def)
  show "m \<otimes> \<one> = m"
    by (induct m) (simp_all add: neutral_nat_def)
qed

end %quoteme

text {*
  \noindent We define the natural operation of the natural numbers
  on monoids:
*}

primrec %quoteme pow :: "nat \<Rightarrow> 'a\<Colon>monoid \<Rightarrow> 'a\<Colon>monoid" where
    "pow 0 a = \<one>"
  | "pow (Suc n) a = a \<otimes> pow n a"

text {*
  \noindent This we use to define the discrete exponentiation function:
*}

definition %quoteme bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

text {*
  \noindent The corresponding code:
*}

text %quoteme {*@{code_stmts bexp (Haskell)}*}

text {*
  \noindent An inspection reveals that the equations stemming from the
  @{text primrec} statement within instantiation of class
  @{class semigroup} with type @{typ nat} are mapped to a separate
  function declaration @{text mult_nat} which in turn is used
  to provide the right hand side for the @{text "instance Semigroup Nat"}
  \fixme[courier fuer code text, isastyle fuer class].  This perfectly
  agrees with the restriction that @{text inst} statements may
  only contain one single equation for each class class parameter
  The @{text instantiation} mechanism manages that for each
  overloaded constant @{text "f [\<kappa> \<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>]"}
  a \emph{shadow constant} @{text "f\<^isub>\<kappa> [\<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>]"} is
  declared satisfying @{text "f [\<kappa> \<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>] \<equiv> f\<^isub>\<kappa> [\<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>]"}.
  this equation is indeed the one used for the statement;
  using it as a rewrite rule, defining equations for 
  @{text "f [\<kappa> \<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>]"} can be turned into
  defining equations for @{text "f\<^isub>\<kappa> [\<^bvec>\<alpha>\<Colon>s\<^isub>k\<^evec>]"}.  This
  happens transparently, providing the illusion that class parameters
  can be instantiated with more than one equation.

  This is a convenient place to show how explicit dictionary construction
  manifests in generated code (here, the same example in @{text SML}):
*}

text %quoteme {*@{code_stmts bexp (SML)}*}


subsection {* The preprocessor \label{sec:preproc} *}

text {*
  Before selected function theorems are turned into abstract
  code, a chain of definitional transformation steps is carried
  out: \emph{preprocessing}.  In essence, the preprocessor
  consists of two components: a \emph{simpset} and \emph{function transformers}.

  The \emph{simpset} allows to employ the full generality of the Isabelle
  simplifier.  Due to the interpretation of theorems
  as defining equations, rewrites are applied to the right
  hand side and the arguments of the left hand side of an
  equation, but never to the constant heading the left hand side.
  An important special case are \emph{inline theorems} which may be
  declared and undeclared using the
  \emph{code inline} or \emph{code inline del} attribute respectively.

  Some common applications:
*}

text_raw {*
  \begin{itemize}
*}

text {*
     \item replacing non-executable constructs by executable ones:
*}     

lemma %quoteme [code inline]:
  "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

text {*
     \item eliminating superfluous constants:
*}

lemma %quoteme [code inline]:
  "1 = Suc 0" by simp

text {*
     \item replacing executable but inconvenient constructs:
*}

lemma %quoteme [code inline]:
  "xs = [] \<longleftrightarrow> List.null xs" by (induct xs) simp_all

text_raw {*
  \end{itemize}
*}

text {*
  \emph{Function transformers} provide a very general interface,
  transforming a list of function theorems to another
  list of function theorems, provided that neither the heading
  constant nor its type change.  The @{term "0\<Colon>nat"} / @{const Suc}
  pattern elimination implemented in
  theory @{text Efficient_Nat} (see \secref{eff_nat}) uses this
  interface.

  \noindent The current setup of the preprocessor may be inspected using
  the @{command print_codesetup} command.
  @{command code_thms} provides a convenient
  mechanism to inspect the impact of a preprocessor setup
  on defining equations.

  \begin{warn}
    The attribute \emph{code unfold}
    associated with the existing code generator also applies to
    the new one: \emph{code unfold} implies \emph{code inline}.
  \end{warn}
*}

subsection {* Datatypes \label{sec:datatypes} *}

text {*
  Conceptually, any datatype is spanned by a set of
  \emph{constructors} of type @{text "\<tau> = \<dots> \<Rightarrow> \<kappa> \<alpha>\<^isub>1 \<dots> \<alpha>\<^isub>n"}
  where @{text "{\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>n}"} is excactly the set of \emph{all}
  type variables in @{text "\<tau>"}.  The HOL datatype package
  by default registers any new datatype in the table
  of datatypes, which may be inspected using
  the @{command print_codesetup} command.

  In some cases, it may be convenient to alter or
  extend this table;  as an example, we will develop an alternative
  representation of natural numbers as binary digits, whose
  size does increase logarithmically with its value, not linear
  \footnote{Indeed, the @{theory Efficient_Nat} theory (see \ref{eff_nat})
    does something similar}.  First, the digit representation:
*}

definition %quoteme Dig0 :: "nat \<Rightarrow> nat" where
  "Dig0 n = 2 * n"

definition %quoteme  Dig1 :: "nat \<Rightarrow> nat" where
  "Dig1 n = Suc (2 * n)"

text {*
  \noindent We will use these two ">digits"< to represent natural numbers
  in binary digits, e.g.:
*}

lemma %quoteme 42: "42 = Dig0 (Dig1 (Dig0 (Dig1 (Dig0 1))))"
  by (simp add: Dig0_def Dig1_def)

text {*
  \noindent Of course we also have to provide proper code equations for
  the operations, e.g. @{term "op + \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"}:
*}

lemma %quoteme plus_Dig [code func]:
  "0 + n = n"
  "m + 0 = m"
  "1 + Dig0 n = Dig1 n"
  "Dig0 m + 1 = Dig1 m"
  "1 + Dig1 n = Dig0 (n + 1)"
  "Dig1 m + 1 = Dig0 (m + 1)"
  "Dig0 m + Dig0 n = Dig0 (m + n)"
  "Dig0 m + Dig1 n = Dig1 (m + n)"
  "Dig1 m + Dig0 n = Dig1 (m + n)"
  "Dig1 m + Dig1 n = Dig0 (m + n + 1)"
  by (simp_all add: Dig0_def Dig1_def)

text {*
  \noindent We then instruct the code generator to view @{term "0\<Colon>nat"},
  @{term "1\<Colon>nat"}, @{term Dig0} and @{term Dig1} as
  datatype constructors:
*}

code_datatype %quoteme "0\<Colon>nat" "1\<Colon>nat" Dig0 Dig1

text {*
  \noindent For the former constructor @{term Suc}, we provide a code
  equation and remove some parts of the default code generator setup
  which are an obstacle here:
*}

lemma %quoteme Suc_Dig [code func]:
  "Suc n = n + 1"
  by simp

declare %quoteme One_nat_def [code inline del]
declare %quoteme add_Suc_shift [code func del] 

text {*
  \noindent This yields the following code:
*}

text %quoteme {*@{code_stmts "op + \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat" (SML)}*}

text {*
  \medskip

  From this example, it can be easily glimpsed that using own constructor sets
  is a little delicate since it changes the set of valid patterns for values
  of that type.  Without going into much detail, here some practical hints:

  \begin{itemize}
    \item When changing the constructor set for datatypes, take care to
      provide an alternative for the @{text case} combinator (e.g.~by replacing
      it using the preprocessor).
    \item Values in the target language need not to be normalised -- different
      values in the target language may represent the same value in the
      logic (e.g. @{term "Dig1 0 = 1"}).
    \item Usually, a good methodology to deal with the subtleties of pattern
      matching is to see the type as an abstract type: provide a set
      of operations which operate on the concrete representation of the type,
      and derive further operations by combinations of these primitive ones,
      without relying on a particular representation.
  \end{itemize}
*}

code_datatype %invisible "0::nat" Suc
declare %invisible plus_Dig [code func del]
declare %invisible One_nat_def [code inline]
declare %invisible add_Suc_shift [code func] 
lemma %invisible [code func]: "0 + n = (n \<Colon> nat)" by simp


subsection {* Equality and wellsortedness *}

text {*
  Surely you have already noticed how equality is treated
  by the code generator:
*}

primrec %quoteme
  collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "collect_duplicates xs ys [] = xs"
  | "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
      then if z \<in> set ys
        then collect_duplicates xs ys zs
        else collect_duplicates xs (z#ys) zs
      else collect_duplicates (z#xs) (z#ys) zs)"

text {*
  The membership test during preprocessing is rewritten,
  resulting in @{const List.member}, which itself
  performs an explicit equality check.
*}

text %quoteme {*@{code_stmts collect_duplicates (SML)}*}

text {*
  \noindent Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  HOL introduces
  an explicit class @{class eq} with a corresponding operation
  @{const eq_class.eq} such that @{thm eq [no_vars]}.
  The preprocessing framework does the rest.
  For datatypes, instances of @{class eq} are implicitly derived
  when possible.  For other types, you may instantiate @{text eq}
  manually like any other type class.

  Though this @{text eq} class is designed to get rarely in
  the way, a subtlety
  enters the stage when definitions of overloaded constants
  are dependent on operational equality.  For example, let
  us define a lexicographic ordering on tuples:
*}

instantiation * :: (ord, ord) ord
begin

definition
  [code func del]: "p1 < p2 \<longleftrightarrow> (let (x1, y1) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2))"

definition
  [code func del]: "p1 \<le> p2 \<longleftrightarrow> (let (x1, y1) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2))"

instance ..

end

lemma ord_prod [code func(*<*), code func del(*>*)]:
  "(x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "(x1 \<Colon> 'a\<Colon>ord, y1 \<Colon> 'b\<Colon>ord) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2)"
  unfolding less_prod_def less_eq_prod_def by simp_all

text {*
  Then code generation will fail.  Why?  The definition
  of @{term "op \<le>"} depends on equality on both arguments,
  which are polymorphic and impose an additional @{class eq}
  class constraint, thus violating the type discipline
  for class operations.

  The solution is to add @{class eq} explicitly to the first sort arguments in the
  code theorems:
*}

lemma ord_prod_code [code func]:
  "(x1 \<Colon> 'a\<Colon>{ord, eq}, y1 \<Colon> 'b\<Colon>ord) < (x2, y2) \<longleftrightarrow>
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "(x1 \<Colon> 'a\<Colon>{ord, eq}, y1 \<Colon> 'b\<Colon>ord) \<le> (x2, y2) \<longleftrightarrow>
    x1 < x2 \<or> (x1 = x2 \<and> y1 \<le> y2)"
  unfolding ord_prod by rule+

text {*
  \noindent Then code generation succeeds:
*}

text %quoteme {*@{code_stmts "op \<le> \<Colon> 'a\<Colon>{eq, ord} \<times> 'b\<Colon>ord \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" (SML)}*}

text {*
  In general, code theorems for overloaded constants may have more
  restrictive sort constraints than the underlying instance relation
  between class and type constructor as long as the whole system of
  constraints is coregular; code theorems violating coregularity
  are rejected immediately.  Consequently, it might be necessary
  to delete disturbing theorems in the code theorem table,
  as we have done here with the original definitions @{fact less_prod_def}
  and @{fact less_eq_prod_def}.

  In some cases, the automatically derived defining equations
  for equality on a particular type may not be appropriate.
  As example, watch the following datatype representing
  monomorphic parametric types (where type constructors
  are referred to by natural numbers):
*}

datatype %quoteme monotype = Mono nat "monotype list"
(*<*)
lemma monotype_eq:
  "Mono tyco1 typargs1 = Mono tyco2 typargs2 \<equiv> 
     tyco1 = tyco2 \<and> typargs1 = typargs2" by simp
(*>*)

text {*
  Then code generation for SML would fail with a message
  that the generated code contains illegal mutual dependencies:
  the theorem @{thm monotype_eq [no_vars]} already requires the
  instance @{text "monotype \<Colon> eq"}, which itself requires
  @{thm monotype_eq [no_vars]};  Haskell has no problem with mutually
  recursive @{text instance} and @{text function} definitions,
  but the SML serializer does not support this.

  In such cases, you have to provide you own equality equations
  involving auxiliary constants.  In our case,
  @{const [show_types] list_all2} can do the job:
*}

lemma %quoteme monotype_eq_list_all2 [code func]:
  "eq_class.eq (Mono tyco1 typargs1) (Mono tyco2 typargs2) \<longleftrightarrow>
     tyco1 = tyco2 \<and> list_all2 eq_class.eq typargs1 typargs2"
  by (simp add: eq list_all2_eq [symmetric])

text {*
  \noindent does not depend on instance @{text "monotype \<Colon> eq"}:
*}

text %quoteme {*@{code_stmts "eq_class.eq :: monotype \<Rightarrow> monotype \<Rightarrow> bool" (SML)}*}


subsection {* Partiality *}

text {* @{command "code_abort"}, examples: maps *}

end

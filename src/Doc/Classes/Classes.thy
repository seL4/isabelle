theory Classes
imports Main Setup
begin

section \<open>Introduction\<close>

text \<open>
  Type classes were introduced by Wadler and Blott @{cite wadler89how}
  into the Haskell language to allow for a reasonable implementation
  of overloading\footnote{throughout this tutorial, we are referring
  to classical Haskell 1.0 type classes, not considering later
  additions in expressiveness}.  As a canonical example, a polymorphic
  equality function \<open>eq :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool\<close> which is overloaded on
  different types for \<open>\<alpha>\<close>, which is achieved by splitting
  introduction of the \<open>eq\<close> function from its overloaded
  definitions by means of \<open>class\<close> and \<open>instance\<close>
  declarations: \footnote{syntax here is a kind of isabellized
  Haskell}

  \begin{quote}

  \<^noindent> \<open>class eq where\<close> \\
  \hspace*{2ex}\<open>eq :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool\<close>

  \<^medskip>\<^noindent> \<open>instance nat :: eq where\<close> \\
  \hspace*{2ex}\<open>eq 0 0 = True\<close> \\
  \hspace*{2ex}\<open>eq 0 _ = False\<close> \\
  \hspace*{2ex}\<open>eq _ 0 = False\<close> \\
  \hspace*{2ex}\<open>eq (Suc n) (Suc m) = eq n m\<close>

  \<^medskip>\<^noindent> \<open>instance (\<alpha>::eq, \<beta>::eq) pair :: eq where\<close> \\
  \hspace*{2ex}\<open>eq (x1, y1) (x2, y2) = eq x1 x2 \<and> eq y1 y2\<close>

  \<^medskip>\<^noindent> \<open>class ord extends eq where\<close> \\
  \hspace*{2ex}\<open>less_eq :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool\<close> \\
  \hspace*{2ex}\<open>less :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool\<close>

  \end{quote}

  \<^noindent> Type variables are annotated with (finitely many) classes;
  these annotations are assertions that a particular polymorphic type
  provides definitions for overloaded functions.

  Indeed, type classes not only allow for simple overloading but form
  a generic calculus, an instance of order-sorted algebra
  @{cite "nipkow-sorts93" and "Nipkow-Prehofer:1993" and "Wenzel:1997:TPHOL"}.

  From a software engineering point of view, type classes roughly
  correspond to interfaces in object-oriented languages like Java; so,
  it is naturally desirable that type classes do not only provide
  functions (class parameters) but also state specifications
  implementations must obey.  For example, the \<open>class eq\<close>
  above could be given the following specification, demanding that
  \<open>class eq\<close> is an equivalence relation obeying reflexivity,
  symmetry and transitivity:

  \begin{quote}

  \<^noindent> \<open>class eq where\<close> \\
  \hspace*{2ex}\<open>eq :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool\<close> \\
  \<open>satisfying\<close> \\
  \hspace*{2ex}\<open>refl: eq x x\<close> \\
  \hspace*{2ex}\<open>sym: eq x y \<longleftrightarrow> eq x y\<close> \\
  \hspace*{2ex}\<open>trans: eq x y \<and> eq y z \<longrightarrow> eq x z\<close>

  \end{quote}

  \<^noindent> From a theoretical point of view, type classes are
  lightweight modules; Haskell type classes may be emulated by SML
  functors @{cite classes_modules}.  Isabelle/Isar offers a discipline
  of type classes which brings all those aspects together:

  \begin{enumerate}
    \item specifying abstract parameters together with
       corresponding specifications,
    \item instantiating those abstract parameters by a particular
       type
    \item in connection with a ``less ad-hoc'' approach to overloading,
    \item with a direct link to the Isabelle module system:
      locales @{cite "kammueller-locales"}.
  \end{enumerate}

  \<^noindent> Isar type classes also directly support code generation in
  a Haskell like fashion. Internally, they are mapped to more
  primitive Isabelle concepts @{cite "Haftmann-Wenzel:2006:classes"}.

  This tutorial demonstrates common elements of structured
  specifications and abstract reasoning with type classes by the
  algebraic hierarchy of semigroups, monoids and groups.  Our
  background theory is that of Isabelle/HOL @{cite "isa-tutorial"}, for
  which some familiarity is assumed.
\<close>

section \<open>A simple algebra example \label{sec:example}\<close>

subsection \<open>Class definition\<close>

text \<open>
  Depending on an arbitrary type \<open>\<alpha>\<close>, class \<open>semigroup\<close> introduces a binary operator \<open>(\<otimes>)\<close> that is
  assumed to be associative:
\<close>

class %quote semigroup =
  fixes mult :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"    (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

text \<open>
  \<^noindent> This @{command class} specification consists of two parts:
  the \qn{operational} part names the class parameter (@{element
  "fixes"}), the \qn{logical} part specifies properties on them
  (@{element "assumes"}).  The local @{element "fixes"} and @{element
  "assumes"} are lifted to the theory toplevel, yielding the global
  parameter @{term [source] "mult :: \<alpha>::semigroup \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"} and the
  global theorem @{fact "semigroup.assoc:"}~@{prop [source] "\<And>x y z ::
  \<alpha>::semigroup. (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"}.
\<close>


subsection \<open>Class instantiation \label{sec:class_inst}\<close>

text \<open>
  The concrete type \<^typ>\<open>int\<close> is made a \<^class>\<open>semigroup\<close> instance
  by providing a suitable definition for the class parameter \<open>(\<otimes>)\<close> and a proof for the specification of @{fact assoc}.  This is
  accomplished by the @{command instantiation} target:
\<close>

instantiation %quote int :: semigroup
begin

definition %quote
  mult_int_def: "i \<otimes> j = i + (j::int)"

instance %quote proof
  fix i j k :: int have "(i + j) + k = i + (j + k)" by simp
  then show "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
    unfolding mult_int_def .
qed

end %quote

text \<open>
  \<^noindent> @{command instantiation} defines class parameters at a
  particular instance using common specification tools (here,
  @{command definition}).  The concluding @{command instance} opens a
  proof that the given parameters actually conform to the class
  specification.  Note that the first proof step is the @{method
  standard} method, which for such instance proofs maps to the @{method
  intro_classes} method.  This reduces an instance judgement to the
  relevant primitive proof goals; typically it is the first method
  applied in an instantiation proof.

  From now on, the type-checker will consider \<^typ>\<open>int\<close> as a \<^class>\<open>semigroup\<close> automatically, i.e.\ any general results are immediately
  available on concrete instances.

  \<^medskip> Another instance of \<^class>\<open>semigroup\<close> yields the natural
  numbers:
\<close>

instantiation %quote nat :: semigroup
begin

primrec %quote mult_nat where
  "(0::nat) \<otimes> n = n"
  | "Suc m \<otimes> n = Suc (m \<otimes> n)"

instance %quote proof
  fix m n q :: nat 
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) auto
qed

end %quote

text \<open>
  \<^noindent> Note the occurrence of the name \<open>mult_nat\<close> in the
  primrec declaration; by default, the local name of a class operation
  \<open>f\<close> to be instantiated on type constructor \<open>\<kappa>\<close> is
  mangled as \<open>f_\<kappa>\<close>.  In case of uncertainty, these names may be
  inspected using the @{command "print_context"} command.
\<close>

subsection \<open>Lifting and parametric types\<close>

text \<open>
  Overloaded definitions given at a class instantiation may include
  recursion over the syntactic structure of types.  As a canonical
  example, we model product semigroups using our simple algebra:
\<close>

instantiation %quote prod :: (semigroup, semigroup) semigroup
begin

definition %quote
  mult_prod_def: "p\<^sub>1 \<otimes> p\<^sub>2 = (fst p\<^sub>1 \<otimes> fst p\<^sub>2, snd p\<^sub>1 \<otimes> snd p\<^sub>2)"

instance %quote proof
  fix p\<^sub>1 p\<^sub>2 p\<^sub>3 :: "\<alpha>::semigroup \<times> \<beta>::semigroup"
  show "p\<^sub>1 \<otimes> p\<^sub>2 \<otimes> p\<^sub>3 = p\<^sub>1 \<otimes> (p\<^sub>2 \<otimes> p\<^sub>3)"
    unfolding mult_prod_def by (simp add: assoc)
qed      

end %quote

text \<open>
  \<^noindent> Associativity of product semigroups is established using
  the definition of \<open>(\<otimes>)\<close> on products and the hypothetical
  associativity of the type components; these hypotheses are
  legitimate due to the \<^class>\<open>semigroup\<close> constraints imposed on the
  type components by the @{command instance} proposition.  Indeed,
  this pattern often occurs with parametric types and type classes.
\<close>


subsection \<open>Subclassing\<close>

text \<open>
  We define a subclass \<open>monoidl\<close> (a semigroup with a left-hand
  neutral) by extending \<^class>\<open>semigroup\<close> with one additional
  parameter \<open>neutral\<close> together with its characteristic property:
\<close>

class %quote monoidl = semigroup +
  fixes neutral :: "\<alpha>" ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"

text \<open>
  \<^noindent> Again, we prove some instances, by providing suitable
  parameter definitions and proofs for the additional specifications.
  Observe that instantiations for types with the same arity may be
  simultaneous:
\<close>

instantiation %quote nat and int :: monoidl
begin

definition %quote
  neutral_nat_def: "\<one> = (0::nat)"

definition %quote
  neutral_int_def: "\<one> = (0::int)"

instance %quote proof
  fix n :: nat
  show "\<one> \<otimes> n = n"
    unfolding neutral_nat_def by simp
next
  fix k :: int
  show "\<one> \<otimes> k = k"
    unfolding neutral_int_def mult_int_def by simp
qed

end %quote

instantiation %quote prod :: (monoidl, monoidl) monoidl
begin

definition %quote
  neutral_prod_def: "\<one> = (\<one>, \<one>)"

instance %quote proof
  fix p :: "\<alpha>::monoidl \<times> \<beta>::monoidl"
  show "\<one> \<otimes> p = p"
    unfolding neutral_prod_def mult_prod_def by (simp add: neutl)
qed

end %quote

text \<open>
  \<^noindent> Fully-fledged monoids are modelled by another subclass,
  which does not add new parameters but tightens the specification:
\<close>

class %quote monoid = monoidl +
  assumes neutr: "x \<otimes> \<one> = x"

instantiation %quote nat and int :: monoid 
begin

instance %quote proof
  fix n :: nat
  show "n \<otimes> \<one> = n"
    unfolding neutral_nat_def by (induct n) simp_all
next
  fix k :: int
  show "k \<otimes> \<one> = k"
    unfolding neutral_int_def mult_int_def by simp
qed

end %quote

instantiation %quote prod :: (monoid, monoid) monoid
begin

instance %quote proof 
  fix p :: "\<alpha>::monoid \<times> \<beta>::monoid"
  show "p \<otimes> \<one> = p"
    unfolding neutral_prod_def mult_prod_def by (simp add: neutr)
qed

end %quote

text \<open>
  \<^noindent> To finish our small algebra example, we add a \<open>group\<close> class with a corresponding instance:
\<close>

class %quote group = monoidl +
  fixes inverse :: "\<alpha> \<Rightarrow> \<alpha>"    ("(_\<div>)" [1000] 999)
  assumes invl: "x\<div> \<otimes> x = \<one>"

instantiation %quote int :: group
begin

definition %quote
  inverse_int_def: "i\<div> = - (i::int)"

instance %quote proof
  fix i :: int
  have "-i + i = 0" by simp
  then show "i\<div> \<otimes> i = \<one>"
    unfolding mult_int_def neutral_int_def inverse_int_def .
qed

end %quote


section \<open>Type classes as locales\<close>

subsection \<open>A look behind the scenes\<close>

text \<open>
  The example above gives an impression how Isar type classes work in
  practice.  As stated in the introduction, classes also provide a
  link to Isar's locale system.  Indeed, the logical core of a class
  is nothing other than a locale:
\<close>

class %quote idem =
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text \<open>
  \<^noindent> essentially introduces the locale
\<close> (*<*)setup %invisible \<open>Sign.add_path "foo"\<close>
(*>*)
locale %quote idem =
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text \<open>\<^noindent> together with corresponding constant(s):\<close>

consts %quote f :: "\<alpha> \<Rightarrow> \<alpha>"

text \<open>
  \<^noindent> The connection to the type system is done by means of a
  primitive type class \<open>idem\<close>, together with a corresponding
  interpretation:
\<close>

interpretation %quote idem_class:
  idem "f :: (\<alpha>::idem) \<Rightarrow> \<alpha>"
(*<*)sorry(*>*)

text \<open>
  \<^noindent> This gives you the full power of the Isabelle module system;
  conclusions in locale \<open>idem\<close> are implicitly propagated
  to class \<open>idem\<close>.
\<close> (*<*)setup %invisible \<open>Sign.parent_path\<close>
(*>*)
subsection \<open>Abstract reasoning\<close>

text \<open>
  Isabelle locales enable reasoning at a general level, while results
  are implicitly transferred to all instances.  For example, we can
  now establish the \<open>left_cancel\<close> lemma for groups, which
  states that the function \<open>(x \<otimes>)\<close> is injective:
\<close>

lemma %quote (in group) left_cancel: "x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"
proof
  assume "x \<otimes> y = x \<otimes> z"
  then have "x\<div> \<otimes> (x \<otimes> y) = x\<div> \<otimes> (x \<otimes> z)" by simp
  then have "(x\<div> \<otimes> x) \<otimes> y = (x\<div> \<otimes> x) \<otimes> z" using assoc by simp
  then show "y = z" using neutl and invl by simp
next
  assume "y = z"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

text \<open>
  \<^noindent> Here the \qt{@{keyword "in"} \<^class>\<open>group\<close>} target
  specification indicates that the result is recorded within that
  context for later use.  This local theorem is also lifted to the
  global one @{fact "group.left_cancel:"} @{prop [source] "\<And>x y z ::
  \<alpha>::group. x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"}.  Since type \<open>int\<close> has been
  made an instance of \<open>group\<close> before, we may refer to that
  fact as well: @{prop [source] "\<And>x y z :: int. x \<otimes> y = x \<otimes> z \<longleftrightarrow> y =
  z"}.
\<close>


subsection \<open>Derived definitions\<close>

text \<open>
  Isabelle locales are targets which support local definitions:
\<close>

primrec %quote (in monoid) pow_nat :: "nat \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
  "pow_nat 0 x = \<one>"
  | "pow_nat (Suc n) x = x \<otimes> pow_nat n x"

text \<open>
  \<^noindent> If the locale \<open>group\<close> is also a class, this local
  definition is propagated onto a global definition of @{term [source]
  "pow_nat :: nat \<Rightarrow> \<alpha>::monoid \<Rightarrow> \<alpha>::monoid"} with corresponding theorems

  @{thm pow_nat.simps [no_vars]}.

  \<^noindent> As you can see from this example, for local definitions
  you may use any specification tool which works together with
  locales, such as Krauss's recursive function package
  @{cite krauss2006}.
\<close>


subsection \<open>A functor analogy\<close>

text \<open>
  We introduced Isar classes by analogy to type classes in functional
  programming; if we reconsider this in the context of what has been
  said about type classes and locales, we can drive this analogy
  further by stating that type classes essentially correspond to
  functors that have a canonical interpretation as type classes.
  There is also the possibility of other interpretations.  For
  example, \<open>list\<close>s also form a monoid with \<open>append\<close> and
  \<^term>\<open>[]\<close> as operations, but it seems inappropriate to apply to
  lists the same operations as for genuinely algebraic types.  In such
  a case, we can simply make a particular interpretation of monoids
  for lists:
\<close>

interpretation %quote list_monoid: monoid append "[]"
  proof qed auto

text \<open>
  \<^noindent> This enables us to apply facts on monoids
  to lists, e.g. @{thm list_monoid.neutl [no_vars]}.

  When using this interpretation pattern, it may also
  be appropriate to map derived definitions accordingly:
\<close>

primrec %quote replicate :: "nat \<Rightarrow> \<alpha> list \<Rightarrow> \<alpha> list" where
  "replicate 0 _ = []"
  | "replicate (Suc n) xs = xs @ replicate n xs"

interpretation %quote list_monoid: monoid append "[]" rewrites
  "monoid.pow_nat append [] = replicate"
proof -
  interpret monoid append "[]" ..
  show "monoid.pow_nat append [] = replicate"
  proof
    fix n
    show "monoid.pow_nat append [] n = replicate n"
      by (induct n) auto
  qed
qed intro_locales

text \<open>
  \<^noindent> This pattern is also helpful to reuse abstract
  specifications on the \emph{same} type.  For example, think of a
  class \<open>preorder\<close>; for type \<^typ>\<open>nat\<close>, there are at least two
  possible instances: the natural order or the order induced by the
  divides relation.  But only one of these instances can be used for
  @{command instantiation}; using the locale behind the class \<open>preorder\<close>, it is still possible to utilise the same abstract
  specification again using @{command interpretation}.
\<close>

subsection \<open>Additional subclass relations\<close>

text \<open>
  Any \<open>group\<close> is also a \<open>monoid\<close>; this can be made
  explicit by claiming an additional subclass relation, together with
  a proof of the logical difference:
\<close>

subclass %quote (in group) monoid
proof
  fix x
  from invl have "x\<div> \<otimes> x = \<one>" by simp
  with assoc [symmetric] neutl invl have "x\<div> \<otimes> (x \<otimes> \<one>) = x\<div> \<otimes> x" by simp
  with left_cancel show "x \<otimes> \<one> = x" by simp
qed

text \<open>
  The logical proof is carried out on the locale level.  Afterwards it
  is propagated to the type system, making \<open>group\<close> an instance
  of \<open>monoid\<close> by adding an additional edge to the graph of
  subclass relations (\figref{fig:subclass}).

  \begin{figure}[htbp]
   \begin{center}
     \small
     \unitlength 0.6mm
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){\<open>semigroup\<close>}}
       \put(20,40){\makebox(0,0){\<open>monoidl\<close>}}
       \put(00,20){\makebox(0,0){\<open>monoid\<close>}}
       \put(40,00){\makebox(0,0){\<open>group\<close>}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(25,35){\vector(1,-3){10}}
     \end{picture}
     \hspace{8em}
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){\<open>semigroup\<close>}}
       \put(20,40){\makebox(0,0){\<open>monoidl\<close>}}
       \put(00,20){\makebox(0,0){\<open>monoid\<close>}}
       \put(40,00){\makebox(0,0){\<open>group\<close>}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(05,15){\vector(3,-1){30}}
     \end{picture}
     \caption{Subclass relationship of monoids and groups:
        before and after establishing the relationship
        \<open>group \<subseteq> monoid\<close>;  transitive edges are left out.}
     \label{fig:subclass}
   \end{center}
  \end{figure}

  For illustration, a derived definition in \<open>group\<close> using \<open>pow_nat\<close>
\<close>

definition %quote (in group) pow_int :: "int \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
  "pow_int k x = (if k >= 0
    then pow_nat (nat k) x
    else (pow_nat (nat (- k)) x)\<div>)"

text \<open>
  \<^noindent> yields the global definition of @{term [source] "pow_int ::
  int \<Rightarrow> \<alpha>::group \<Rightarrow> \<alpha>::group"} with the corresponding theorem @{thm
  pow_int_def [no_vars]}.
\<close>

subsection \<open>A note on syntax\<close>

text \<open>
  As a convenience, class context syntax allows references to local
  class operations and their global counterparts uniformly; type
  inference resolves ambiguities.  For example:
\<close>

context %quote semigroup
begin

term %quote "x \<otimes> y" \<comment> \<open>example 1\<close>
term %quote "(x::nat) \<otimes> y" \<comment> \<open>example 2\<close>

end  %quote

term %quote "x \<otimes> y" \<comment> \<open>example 3\<close>

text \<open>
  \<^noindent> Here in example 1, the term refers to the local class
  operation \<open>mult [\<alpha>]\<close>, whereas in example 2 the type
  constraint enforces the global class operation \<open>mult [nat]\<close>.
  In the global context in example 3, the reference is to the
  polymorphic global class operation \<open>mult [?\<alpha> :: semigroup]\<close>.
\<close>

section \<open>Further issues\<close>

subsection \<open>Type classes and code generation\<close>

text \<open>
  Turning back to the first motivation for type classes, namely
  overloading, it is obvious that overloading stemming from @{command
  class} statements and @{command instantiation} targets naturally
  maps to Haskell type classes.  The code generator framework
  @{cite "isabelle-codegen"} takes this into account.  If the target
  language (e.g.~SML) lacks type classes, then they are implemented by
  an explicit dictionary construction.  As example, let's go back to
  the power function:
\<close>

definition %quote example :: int where
  "example = pow_int 10 (-2)"

text \<open>
  \<^noindent> This maps to Haskell as follows:
\<close>
text %quote \<open>
  @{code_stmts example (Haskell)}
\<close>

text \<open>
  \<^noindent> The code in SML has explicit dictionary passing:
\<close>
text %quote \<open>
  @{code_stmts example (SML)}
\<close>


text \<open>
  \<^noindent> In Scala, implicits are used as dictionaries:
\<close>
text %quote \<open>
  @{code_stmts example (Scala)}
\<close>


subsection \<open>Inspecting the type class universe\<close>

text \<open>
  To facilitate orientation in complex subclass structures, two
  diagnostics commands are provided:

  \begin{description}

    \item[@{command "print_classes"}] print a list of all classes
      together with associated operations etc.

    \item[@{command "class_deps"}] visualizes the subclass relation
      between all classes as a Hasse diagram.  An optional first sort argument
      constrains the set of classes to all subclasses of this sort,
      an optional second sort argument to all superclasses of this sort.

  \end{description}
\<close>

end


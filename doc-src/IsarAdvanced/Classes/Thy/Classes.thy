(* $Id$ *)

(*<*)
theory Classes
imports Main Code_Integer
begin

ML {*
CodeTarget.code_width := 74;
*}

syntax
  "_alpha" :: "type"  ("\<alpha>")
  "_alpha_ofsort" :: "sort \<Rightarrow> type"  ("\<alpha>()\<Colon>_" [0] 1000)

parse_ast_translation {*
  let
    fun alpha_ast_tr [] = Syntax.Variable "'a"
      | alpha_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
    fun alpha_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'a", ast]
      | alpha_ofsort_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
  in [
    ("_alpha", alpha_ast_tr), ("_alpha_ofsort", alpha_ofsort_ast_tr)
  ] end
*}
(*>*)


chapter {* Haskell-style classes with Isabelle/Isar *}

section {* Introduction *}

text {*
  Type classes were introduces by Wadler and Blott \cite{wadler89how}
  into the Haskell language, to allow for a reasonable implementation
  of overloading\footnote{throughout this tutorial, we are referring
  to classical Haskell 1.0 type classes, not considering
  later additions in expressiveness}.
  As a canonical example, a polymorphic equality function
  @{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} which is overloaded on different
  types for @{text "\<alpha>"}, which is achieved by splitting introduction
  of the @{text eq} function from its overloaded definitions by means
  of @{text class} and @{text instance} declarations:

  \medskip\noindent\hspace*{2ex}@{text "class eq where"}\footnote{syntax here is a kind of isabellized Haskell} \\
  \hspace*{4ex}@{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"}

  \medskip\noindent\hspace*{2ex}@{text "instance nat \<Colon> eq where"} \\
  \hspace*{4ex}@{text "eq 0 0 = True"} \\
  \hspace*{4ex}@{text "eq 0 _ = False"} \\
  \hspace*{4ex}@{text "eq _ 0 = False"} \\
  \hspace*{4ex}@{text "eq (Suc n) (Suc m) = eq n m"}

  \medskip\noindent\hspace*{2ex}@{text "instance (\<alpha>\<Colon>eq, \<beta>\<Colon>eq) pair \<Colon> eq where"} \\
  \hspace*{4ex}@{text "eq (x1, y1) (x2, y2) = eq x1 x2 \<and> eq y1 y2"}

  \medskip\noindent\hspace*{2ex}@{text "class ord extends eq where"} \\
  \hspace*{4ex}@{text "less_eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  \hspace*{4ex}@{text "less \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"}

  \medskip\noindent Type variables are annotated with (finitly many) classes;
  these annotations are assertions that a particular polymorphic type
  provides definitions for overloaded functions.

  Indeed, type classes not only allow for simple overloading
  but form a generic calculus, an instance of order-sorted
  algebra \cite{Nipkow-Prehofer:1993,nipkow-sorts93,Wenzel:1997:TPHOL}.

  From a software enigineering point of view, type classes
  correspond to interfaces in object-oriented languages like Java;
  so, it is naturally desirable that type classes do not only
  provide functions (class parameters) but also state specifications
  implementations must obey.  For example, the @{text "class eq"}
  above could be given the following specification, demanding that
  @{text "class eq"} is an equivalence relation obeying reflexivity,
  symmetry and transitivity:

  \medskip\noindent\hspace*{2ex}@{text "class eq where"} \\
  \hspace*{4ex}@{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  \hspace*{2ex}@{text "satisfying"} \\
  \hspace*{4ex}@{text "refl: eq x x"} \\
  \hspace*{4ex}@{text "sym: eq x y \<longleftrightarrow> eq x y"} \\
  \hspace*{4ex}@{text "trans: eq x y \<and> eq y z \<longrightarrow> eq x z"}

  \medskip\noindent From a theoretic point of view, type classes are leightweight
  modules; Haskell type classes may be emulated by
  SML functors \cite{classes_modules}. 
  Isabelle/Isar offers a discipline of type classes which brings
  all those aspects together:

  \begin{enumerate}
    \item specifying abstract parameters together with
       corresponding specifications,
    \item instantating those abstract parameters by a particular
       type
    \item in connection with a ``less ad-hoc'' approach to overloading,
    \item with a direct link to the Isabelle module system
      (aka locales \cite{kammueller-locales}).
  \end{enumerate}

  \noindent Isar type classes also directly support code generation
  in a Haskell like fashion.

  This tutorial demonstrates common elements of structured specifications
  and abstract reasoning with type classes by the algebraic hierarchy of
  semigroups, monoids and groups.  Our background theory is that of
  Isabelle/HOL \cite{isa-tutorial}, for which some
  familiarity is assumed.

  Here we merely present the look-and-feel for end users.
  Internally, those are mapped to more primitive Isabelle concepts.
  See \cite{Haftmann-Wenzel:2006:classes} for more detail.
*}

section {* A simple algebra example \label{sec:example} *}

subsection {* Class definition *}

text {*
  Depending on an arbitrary type @{text "\<alpha>"}, class @{text
  "semigroup"} introduces a binary operator @{text "\<otimes>"} that is
  assumed to be associative:
*}

    class semigroup = type +
      fixes mult :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"    (infixl "\<otimes>" 70)
      assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

text {*
  \noindent This @{text "\<CLASS>"} specification consists of two
  parts: the \qn{operational} part names the class parameter (@{text
  "\<FIXES>"}), the \qn{logical} part specifies properties on them
  (@{text "\<ASSUMES>"}).  The local @{text "\<FIXES>"} and @{text
  "\<ASSUMES>"} are lifted to the theory toplevel, yielding the global
  parameter @{term [source] "mult \<Colon> \<alpha>\<Colon>semigroup \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"} and the
  global theorem @{text "semigroup.assoc:"}~@{prop [source] "\<And>x y
  z \<Colon> \<alpha>\<Colon>semigroup. (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"}.
*}


subsection {* Class instantiation \label{sec:class_inst} *}

text {*
  The concrete type @{text "int"} is made a @{text "semigroup"}
  instance by providing a suitable definition for the class parameter
  @{text "mult"} and a proof for the specification of @{text "assoc"}.
*}

    instance int :: semigroup
      mult_int_def: "i \<otimes> j \<equiv> i + j"
    proof
      fix i j k :: int have "(i + j) + k = i + (j + k)" by simp
      then show "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
	unfolding mult_int_def .
    qed

text {*
  \noindent From now on, the type-checker will consider @{text "int"}
  as a @{text "semigroup"} automatically, i.e.\ any general results
  are immediately available on concrete instances.

  Note that the first proof step is the @{text default} method,
  which for instantiation proofs maps to the @{text intro_classes} method.
  This boils down an instantiation judgement to the relevant primitive
  proof goals and should conveniently always be the first method applied
  in an instantiation proof.

  \medskip Another instance of @{text "semigroup"} are the natural numbers:
*}

    instance nat :: semigroup
      mult_nat_def: "m \<otimes> n \<equiv> m + n"
    proof
      fix m n q :: nat 
      show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
	unfolding mult_nat_def by simp
    qed


subsection {* Lifting and parametric types *}

text {*
  Overloaded definitions giving on class instantiation
  may include recursion over the syntactic structure of types.
  As a canonical example, we model product semigroups
  using our simple algebra:
*}

    instance * :: (semigroup, semigroup) semigroup
      mult_prod_def: "p\<^isub>1 \<otimes> p\<^isub>2 \<equiv> (fst p\<^isub>1 \<otimes> fst p\<^isub>2, snd p\<^isub>1 \<otimes> snd p\<^isub>2)"
    proof
      fix p\<^isub>1 p\<^isub>2 p\<^isub>3 :: "'a\<Colon>semigroup \<times> 'b\<Colon>semigroup"
      show "p\<^isub>1 \<otimes> p\<^isub>2 \<otimes> p\<^isub>3 = p\<^isub>1 \<otimes> (p\<^isub>2 \<otimes> p\<^isub>3)"
	unfolding mult_prod_def by (simp add: assoc)
    qed      

text {*
  \noindent Associativity from product semigroups is
  established using
  the definition of @{text \<otimes>} on products and the hypothetical
  associativety of the type components;  these hypothesis
  are facts due to the @{text semigroup} constraints imposed
  on the type components by the @{text instance} proposition.
  Indeed, this pattern often occurs with parametric types
  and type classes.
*}


subsection {* Subclassing *}

text {*
  We define a subclass @{text "monoidl"} (a semigroup with a left-hand neutral)
  by extending @{text "semigroup"}
  with one additional parameter @{text "neutral"} together
  with its property:
*}

    class monoidl = semigroup +
      fixes neutral :: "\<alpha>" ("\<one>")
      assumes neutl: "\<one> \<otimes> x = x"

text {*
  \noindent Again, we prove some instances, by
  providing suitable parameter definitions and proofs for the
  additional specifications:
*}

    instance nat :: monoidl
      neutral_nat_def: "\<one> \<equiv> 0"
    proof
      fix n :: nat
      show "\<one> \<otimes> n = n"
	unfolding neutral_nat_def mult_nat_def by simp
    qed

    instance int :: monoidl
      neutral_int_def: "\<one> \<equiv> 0"
    proof
      fix k :: int
      show "\<one> \<otimes> k = k"
	unfolding neutral_int_def mult_int_def by simp
    qed

    instance * :: (monoidl, monoidl) monoidl
      neutral_prod_def: "\<one> \<equiv> (\<one>, \<one>)"
    proof
      fix p :: "'a\<Colon>monoidl \<times> 'b\<Colon>monoidl"
      show "\<one> \<otimes> p = p"
	unfolding neutral_prod_def mult_prod_def by (simp add: neutl)
    qed

text {*
  \noindent Fully-fledged monoids are modelled by another subclass
  which does not add new parameters but tightens the specification:
*}

    class monoid = monoidl +
      assumes neutr: "x \<otimes> \<one> = x"

    instance nat :: monoid 
    proof
      fix n :: nat
      show "n \<otimes> \<one> = n"
	unfolding neutral_nat_def mult_nat_def by simp
    qed

    instance int :: monoid
    proof
      fix k :: int
      show "k \<otimes> \<one> = k"
	unfolding neutral_int_def mult_int_def by simp
    qed

    instance * :: (monoid, monoid) monoid
    proof 
      fix p :: "'a\<Colon>monoid \<times> 'b\<Colon>monoid"
      show "p \<otimes> \<one> = p"
	unfolding neutral_prod_def mult_prod_def by (simp add: neutr)
    qed

text {*
  \noindent To finish our small algebra example, we add a @{text "group"} class
  with a corresponding instance:
*}

    class group = monoidl +
      fixes inverse :: "\<alpha> \<Rightarrow> \<alpha>"    ("(_\<div>)" [1000] 999)
      assumes invl: "x\<div> \<otimes> x = \<one>"

    instance int :: group
      inverse_int_def: "i\<div> \<equiv> - i"
    proof
      fix i :: int
      have "-i + i = 0" by simp
      then show "i\<div> \<otimes> i = \<one>"
	unfolding mult_int_def neutral_int_def inverse_int_def .
    qed

section {* Type classes as locales *}

subsection {* A look behind the scene *}

text {*
  The example above gives an impression how Isar type classes work
  in practice.  As stated in the introduction, classes also provide
  a link to Isar's locale system.  Indeed, the logical core of a class
  is nothing else than a locale:
*}

class idem = type +
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text {*
  \noindent essentially introduces the locale
*}
(*<*) setup {* Sign.add_path "foo" *} (*>*)
locale idem =
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text {* \noindent together with corresponding constant(s): *}

consts f :: "\<alpha> \<Rightarrow> \<alpha>"

text {*
  \noindent The connection to the type system is done by means
  of a primitive axclass
*}

axclass idem < type
  idem: "f (f x) = f x"

text {* \noindent together with a corresponding interpretation: *}

interpretation idem_class:
  idem ["f \<Colon> ('a\<Colon>idem) \<Rightarrow> \<alpha>"]
by unfold_locales (rule idem)
(*<*) setup {* Sign.parent_path *} (*>*)
text {*
  This give you at hand the full power of the Isabelle module system;
  conclusions in locale @{text idem} are implicitly propagated
  to class @{text idem}.
*}

subsection {* Abstract reasoning *}

text {*
  Isabelle locales enable reasoning at a general level, while results
  are implicitly transferred to all instances.  For example, we can
  now establish the @{text "left_cancel"} lemma for groups, which
  states that the function @{text "(x \<otimes>)"} is injective:
*}

    lemma (in group) left_cancel: "x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"
    proof
      assume "x \<otimes> y = x \<otimes> z"
      then have "x\<div> \<otimes> (x \<otimes> y) = x\<div> \<otimes> (x \<otimes> z)" by simp
      then have "(x\<div> \<otimes> x) \<otimes> y = (x\<div> \<otimes> x) \<otimes> z" using assoc by simp
      then show "y = z" using neutl and invl by simp
    next
      assume "y = z"
      then show "x \<otimes> y = x \<otimes> z" by simp
    qed

text {*
  \noindent Here the \qt{@{text "\<IN> group"}} target specification
  indicates that the result is recorded within that context for later
  use.  This local theorem is also lifted to the global one @{text
  "group.left_cancel:"} @{prop [source] "\<And>x y z \<Colon> \<alpha>\<Colon>group. x \<otimes> y = x \<otimes>
  z \<longleftrightarrow> y = z"}.  Since type @{text "int"} has been made an instance of
  @{text "group"} before, we may refer to that fact as well: @{prop
  [source] "\<And>x y z \<Colon> int. x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"}.
*}


subsection {* Derived definitions *}

text {*
  Isabelle locales support a concept of local definitions
  in locales:
*}

    fun (in monoid)
      pow_nat :: "nat \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
      "pow_nat 0 x = \<one>"
      | "pow_nat (Suc n) x = x \<otimes> pow_nat n x"

text {*
  \noindent If the locale @{text group} is also a class, this local
  definition is propagated onto a global definition of
  @{term [source] "pow_nat \<Colon> nat \<Rightarrow> \<alpha>\<Colon>monoid \<Rightarrow> \<alpha>\<Colon>monoid"}
  with corresponding theorems

  @{thm pow_nat.simps [no_vars]}.

  \noindent As you can see from this example, for local
  definitions you may use any specification tool
  which works together with locales (e.g. \cite{krauss2006}).
*}


subsection {* A functor analogy *}

text {*
  We introduced Isar classes by analogy to type classes
  functional programming;  if we reconsider this in the
  context of what has been said about type classes and locales,
  we can drive this analogy further by stating that type
  classes essentially correspond to functors which have
  a canonical interpretation as type classes.
  Anyway, there is also the possibility of other interpretations.
  For example, also @{text "list"}s form a monoid with
  @{const "op @"} and @{const "[]"} as operations, but it
  seems inappropriate to apply to lists
  the same operations as for genuinly algebraic types.
  In such a case, we simply can do a particular interpretation
  of monoids for lists:
*}

    interpretation list_monoid: monoid ["op @" "[]"]
      by unfold_locales auto

text {*
  \noindent This enables us to apply facts on monoids
  to lists, e.g. @{thm list_monoid.neutl [no_vars]}.

  When using this interpretation pattern, it may also
  be appropriate to map derived definitions accordingly:
*}

    fun
      replicate :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
    where
      "replicate 0 _ = []"
      | "replicate (Suc n) xs = xs @ replicate n xs"

    interpretation list_monoid: monoid ["op @" "[]"] where
      "monoid.pow_nat (op @) [] = replicate"
    proof
      fix n :: nat
      show "monoid.pow_nat (op @) [] n = replicate n"
	by (induct n) auto
    qed


subsection {* Additional subclass relations *}

text {*
  Any @{text "group"} is also a @{text "monoid"};  this
  can be made explicit by claiming an additional
  subclass relation,
  together with a proof of the logical difference:
*}

    subclass (in group) monoid
    proof unfold_locales
      fix x
      from invl have "x\<div> \<otimes> x = \<one>" by simp
      with assoc [symmetric] neutl invl have "x\<div> \<otimes> (x \<otimes> \<one>) = x\<div> \<otimes> x" by simp
      with left_cancel show "x \<otimes> \<one> = x" by simp
    qed

text {*
  \noindent The logical proof is carried out on the locale level
  and thus conveniently is opened using the @{text unfold_locales}
  method which only leaves the logical differences still
  open to proof to the user.  Afterwards it is propagated
  to the type system, making @{text group} an instance of
  @{text monoid} by adding an additional edge
  to the graph of subclass relations
  (cf.\ \figref{fig:subclass}).

  \begin{figure}[htbp]
   \begin{center}
     \small
     \unitlength 0.6mm
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){@{text semigroup}}}
       \put(20,40){\makebox(0,0){@{text monoidl}}}
       \put(00,20){\makebox(0,0){@{text monoid}}}
       \put(40,00){\makebox(0,0){@{text group}}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(25,35){\vector(1,-3){10}}
     \end{picture}
     \hspace{8em}
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){@{text semigroup}}}
       \put(20,40){\makebox(0,0){@{text monoidl}}}
       \put(00,20){\makebox(0,0){@{text monoid}}}
       \put(40,00){\makebox(0,0){@{text group}}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(05,15){\vector(3,-1){30}}
     \end{picture}
     \caption{Subclass relationship of monoids and groups:
        before and after establishing the relationship
        @{text "group \<subseteq> monoid"};  transitive edges left out.}
     \label{fig:subclass}
   \end{center}
  \end{figure}

  For illustration, a derived definition
  in @{text group} which uses @{text pow_nat}:
*}

    definition (in group)
      pow_int :: "int \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
      "pow_int k x = (if k >= 0
        then pow_nat (nat k) x
        else (pow_nat (nat (- k)) x)\<div>)"

text {*
  \noindent yields the global definition of
  @{term [source] "pow_int \<Colon> int \<Rightarrow> \<alpha>\<Colon>group \<Rightarrow> \<alpha>\<Colon>group"}
  with the corresponding theorem @{thm pow_int_def [no_vars]}.
*}


section {* Type classes and code generation *}

text {*
  Turning back to the first motivation for type classes,
  namely overloading, it is obvious that overloading
  stemming from @{text "\<CLASS>"} and @{text "\<INSTANCE>"}
  statements naturally maps to Haskell type classes.
  The code generator framework \cite{isabelle-codegen} 
  takes this into account.  Concerning target languages
  lacking type classes (e.g.~SML), type classes
  are implemented by explicit dictionary construction.
  For example, lets go back to the power function:
*}

(*    fun
      pow_nat :: "nat \<Rightarrow> \<alpha>\<Colon>group \<Rightarrow> \<alpha>\<Colon>group" where
      "pow_nat 0 x = \<one>"
      | "pow_nat (Suc n) x = x \<otimes> pow_nat n x"

    definition
      pow_int :: "int \<Rightarrow> \<alpha>\<Colon>group \<Rightarrow> \<alpha>\<Colon>group" where
      "pow_int k x = (if k >= 0
        then pow_nat (nat k) x
        else (pow_nat (nat (- k)) x)\<div>)"*)

    definition
      example :: int where
      "example = pow_int 10 (-2)"

text {*
  \noindent This maps to Haskell as:
*}

export_code example in Haskell module_name Classes file "code_examples/"
  (* NOTE: you may use Haskell only once in this document, otherwise
  you have to work in distinct subdirectories *)

text {*
  \lsthaskell{Thy/code_examples/Classes.hs}

  \noindent The whole code in SML with explicit dictionary passing:
*}

export_code example (*<*)in SML module_name Classes(*>*)in SML module_name Classes file "code_examples/classes.ML"

text {*
  \lstsml{Thy/code_examples/classes.ML}
*}


(* subsection {* Different syntax for same specifications *}

text {*

subsection {* Syntactic classes *}

*} *)

end

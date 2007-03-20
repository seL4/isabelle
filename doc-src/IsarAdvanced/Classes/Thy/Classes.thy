
(* $Id$ *)

(*<*)
theory Classes
imports Main
begin

ML {*
CodegenSerializer.code_width := 74;
*}

syntax
  "_alpha" :: "type"  ("\<alpha>")
  "_alpha_ofsort" :: "sort \<Rightarrow> type"  ("\<alpha>()::_" [0] 1000)
  "_beta" :: "type"  ("\<beta>")
  "_beta_ofsort" :: "sort \<Rightarrow> type"  ("\<beta>()::_" [0] 1000)
  "_gamma" :: "type"  ("\<gamma>")
  "_gamma_ofsort" :: "sort \<Rightarrow> type"  ("\<gamma>()::_" [0] 1000)
  "_alpha_f" :: "type"  ("\<alpha>\<^sub>f")
  "_alpha_f_ofsort" :: "sort \<Rightarrow> type"  ("\<alpha>\<^sub>f()::_" [0] 1000)
  "_beta_f" :: "type"  ("\<beta>\<^sub>f")
  "_beta_f_ofsort" :: "sort \<Rightarrow> type"  ("\<beta>\<^sub>f()::_" [0] 1000)
  "_gamma_f" :: "type"  ("\<gamma>\<^sub>f")
  "_gamma_ofsort_f" :: "sort \<Rightarrow> type"  ("\<gamma>\<^sub>f()::_" [0] 1000)

parse_ast_translation {*
  let
    fun alpha_ast_tr [] = Syntax.Variable "'a"
      | alpha_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
    fun alpha_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'a", ast]
      | alpha_ofsort_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
    fun beta_ast_tr [] = Syntax.Variable "'b"
      | beta_ast_tr asts = raise Syntax.AST ("beta_ast_tr", asts);
    fun beta_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'b", ast]
      | beta_ofsort_ast_tr asts = raise Syntax.AST ("beta_ast_tr", asts);
    fun gamma_ast_tr [] = Syntax.Variable "'c"
      | gamma_ast_tr asts = raise Syntax.AST ("gamma_ast_tr", asts);
    fun gamma_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'c", ast]
      | gamma_ofsort_ast_tr asts = raise Syntax.AST ("gamma_ast_tr", asts);
    fun alpha_f_ast_tr [] = Syntax.Variable "'a_f"
      | alpha_f_ast_tr asts = raise Syntax.AST ("alpha_f_ast_tr", asts);
    fun alpha_f_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'a_f", ast]
      | alpha_f_ofsort_ast_tr asts = raise Syntax.AST ("alpha_f_ast_tr", asts);
    fun beta_f_ast_tr [] = Syntax.Variable "'b_f"
      | beta_f_ast_tr asts = raise Syntax.AST ("beta_f_ast_tr", asts);
    fun beta_f_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'b_f", ast]
      | beta_f_ofsort_ast_tr asts = raise Syntax.AST ("beta_f_ast_tr", asts);
    fun gamma_f_ast_tr [] = Syntax.Variable "'c_f"
      | gamma_f_ast_tr asts = raise Syntax.AST ("gamma_f_ast_tr", asts);
    fun gamma_f_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant "_ofsort", Syntax.Variable "'c_f", ast]
      | gamma_f_ofsort_ast_tr asts = raise Syntax.AST ("gamma_f_ast_tr", asts);
  in [
    ("_alpha", alpha_ast_tr), ("_alpha_ofsort", alpha_ofsort_ast_tr),
    ("_beta", beta_ast_tr), ("_beta_ofsort", beta_ofsort_ast_tr),
    ("_gamma", gamma_ast_tr), ("_gamma_ofsort", gamma_ofsort_ast_tr),
    ("_alpha_f", alpha_f_ast_tr), ("_alpha_f_ofsort", alpha_f_ofsort_ast_tr),
    ("_beta_f", beta_f_ast_tr), ("_beta_f_ofsort", beta_f_ofsort_ast_tr),
    ("_gamma_f", gamma_f_ast_tr), ("_gamma_f_ofsort", gamma_f_ofsort_ast_tr)
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
  types for @{text "\<alpha>"}, which is achieves by splitting introduction
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
  \hspace*{4ex}@{text "eq (x1, y1) (x2, y2) = eq x1 x2 && eq y1 y2"}

  \medskip\noindent\hspace*{2ex}@{text "class ord extends eq where"} \\
  \hspace*{4ex}@{text "less_eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  \hspace*{4ex}@{text "less \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"}

  \medskip Type variables are annotated with (finitly many) classes;
  these annotations are assertions that a particular polymorphic type
  provides definitions for overloaded functions.

  Indeed, type classes not only allow for simple overloading
  but form a generic calculus, an instance of order-sorted
  algebra \cite{Nipkow-Prehofer:1993,Nipkow:1993,Wenzel:1997}.

  From a software enigineering point of view, type classes
  correspond to interfaces in object-oriented languages like Java;
  so, it is naturally desirable that type classes do not only
  provide functions (class operations) but also state specifications
  implementations must obey.  For example, the @{text "class eq"}
  above could be given the following specification:

  \medskip\noindent\hspace*{2ex}@{text "class eq where"} \\
  \hspace*{4ex}@{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  \hspace*{2ex}@{text "satisfying"} \\
  \hspace*{4ex}@{text "refl: eq x x"} \\
  \hspace*{4ex}@{text "sym: eq x y \<longleftrightarrow> eq x y"} \\
  \hspace*{4ex}@{text "trans: eq x y \<and> eq y z \<longrightarrow> eq x z"}

  \medskip From a theoretic point of view, type classes are leightweight
  modules; Haskell type classes may be emulated by
  SML functors \cite{classes_modules}. 
  Isabelle/Isar offers a discipline of type classes which brings
  all those aspects together:

  \begin{enumerate}
    \item specifying abstract operations togehter with
       corresponding specifications,
    \item instantating those abstract operations by a particular
       type
    \item in connection with a ``less ad-hoc'' approach to overloading,
    \item with a direct link to the Isabelle module system (aka locales).
  \end{enumerate}

  Isar type classes also directly support code generation
  in as Haskell like fashion.

  This tutorial demonstrates common elements of structured specifications
  and abstract reasoning with type classes by the algebraic hierarchy of
  semigroups, monoids and groups.  Our background theory is that of
  Isabelle/HOL \cite{Nipkow-et-al:2002:tutorial}, for which some
  familiarity is assumed.

  Here we merely present the look-and-feel for end users.
  Internally, those are mapped to more primitive Isabelle concepts.
  See \cite{haftmann_wenzel2006classes} for more detail.
*}

section {* A simple algebra example \label{sec:example} *}

subsection {* Class definition *}

text {*
  Depending on an arbitrary type @{text "\<alpha>"}, class @{text
  "semigroup"} introduces a binary operation @{text "\<circ>"} that is
  assumed to be associative:
*}

    class semigroup = type +
      fixes mult :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"    (infixl "\<^loc>\<otimes>" 70)
      assumes assoc: "(x \<^loc>\<otimes> y) \<^loc>\<otimes> z = x \<^loc>\<otimes> (y \<^loc>\<otimes> z)"

text {*
  \noindent This @{text "\<CLASS>"} specification consists of two
  parts: the \qn{operational} part names the class operation (@{text
  "\<FIXES>"}), the \qn{logical} part specifies properties on them
  (@{text "\<ASSUMES>"}).  The local @{text "\<FIXES>"} and @{text
  "\<ASSUMES>"} are lifted to the theory toplevel, yielding the global
  operation @{term [source] "mult :: \<alpha>::semigroup \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"} and the
  global theorem @{text "semigroup.assoc:"}~@{prop [source] "\<And>x y
  z::\<alpha>::semigroup. (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"}.
*}


subsection {* Class instantiation \label{sec:class_inst} *}

text {*
  The concrete type @{text "int"} is made a @{text "semigroup"}
  instance by providing a suitable definition for the class operation
  @{text "mult"} and a proof for the specification of @{text "assoc"}.
*}

    instance int :: semigroup
      mult_int_def: "\<And>i j :: int. i \<otimes> j \<equiv> i + j"
    proof
      fix i j k :: int have "(i + j) + k = i + (j + k)" by simp
      then show "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)" unfolding mult_int_def .
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

  Another instance of @{text "semigroup"} are the natural numbers:
*}

    instance nat :: semigroup
      mult_nat_def: "m \<otimes> n \<equiv> m + n"
    proof
      fix m n q :: nat 
      show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" unfolding mult_nat_def by simp
    qed

text {*
  Also @{text "list"}s form a semigroup with @{const "op @"} as
  operation:
*}

    instance list :: (type) semigroup
      mult_list_def: "xs \<otimes> ys \<equiv> xs @ ys"
    proof
      fix xs ys zs :: "\<alpha> list"
      show "xs \<otimes> ys \<otimes> zs = xs \<otimes> (ys \<otimes> zs)"
      proof -
        from mult_list_def have "\<And>xs ys\<Colon>\<alpha> list. xs \<otimes> ys \<equiv> xs @ ys" .
        thus ?thesis by simp
      qed
    qed


subsection {* Subclasses *}

text {*
  We define a subclass @{text "monoidl"} (a semigroup with a left-hand neutral)
  by extending @{text "semigroup"}
  with one additional operation @{text "neutral"} together
  with its property:
*}

    class monoidl = semigroup +
      fixes neutral :: "\<alpha>" ("\<^loc>\<one>")
      assumes neutl: "\<^loc>\<one> \<^loc>\<otimes> x = x"

text {*
  \noindent Again, we make some instances, by
  providing suitable operation definitions and proofs for the
  additional specifications.
*}

    instance nat :: monoidl
      neutral_nat_def: "\<one> \<equiv> 0"
    proof
      fix n :: nat
      show "\<one> \<otimes> n = n" unfolding neutral_nat_def mult_nat_def by simp
    qed

    instance int :: monoidl
      neutral_int_def: "\<one> \<equiv> 0"
    proof
      fix k :: int
      show "\<one> \<otimes> k = k" unfolding neutral_int_def mult_int_def by simp
    qed

    instance list :: (type) monoidl
      neutral_list_def: "\<one> \<equiv> []"
    proof
      fix xs :: "\<alpha> list"
      show "\<one> \<otimes> xs = xs"
      proof -
	from mult_list_def have "\<And>xs ys\<Colon>\<alpha> list. xs \<otimes> ys \<equiv> xs @ ys" .
	moreover from mult_list_def neutral_list_def have "\<one> \<equiv> []\<Colon>\<alpha> list" by simp
	ultimately show ?thesis by simp
      qed
    qed  

text {*
  \noindent Fully-fledged monoids are modelled by another subclass
  which does not add new operations but tightens the specification:
*}

    class monoid = monoidl +
      assumes neutr: "x \<^loc>\<otimes> \<^loc>\<one> = x"

text {*
  \noindent Instantiations may also be given simultaneously for different
  type constructors:
*}

    instance nat :: monoid and int :: monoid and list :: (type) monoid
    proof
      fix n :: nat
      show "n \<otimes> \<one> = n" unfolding neutral_nat_def mult_nat_def by simp
    next
      fix k :: int
      show "k \<otimes> \<one> = k" unfolding neutral_int_def mult_int_def by simp
    next
      fix xs :: "\<alpha> list"
      show "xs \<otimes> \<one> = xs"
      proof -
	from mult_list_def have "\<And>xs ys\<Colon>\<alpha> list. xs \<otimes> ys \<equiv> xs @ ys" .
	moreover from mult_list_def neutral_list_def have "\<one> \<equiv> []\<Colon>\<alpha> list" by simp
	ultimately show ?thesis by simp
      qed
    qed

text {*
  \noindent To finish our small algebra example, we add a @{text "group"} class
  with a corresponding instance:
*}

    class group = monoidl +
      fixes inverse :: "\<alpha> \<Rightarrow> \<alpha>"    ("(_\<^loc>\<div>)" [1000] 999)
      assumes invl: "x\<^loc>\<div> \<^loc>\<otimes> x = \<^loc>\<one>"

    instance int :: group
      inverse_int_def: "i\<div> \<equiv> - i"
    proof
      fix i :: int
      have "-i + i = 0" by simp
      then show "i\<div> \<otimes> i = \<one>" unfolding mult_int_def and neutral_int_def and inverse_int_def .
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

text {* \noindent together with corresponding constant(s) and axclass *}

consts f :: "\<alpha> \<Rightarrow> \<alpha>"

axclass idem < type
  idem: "f (f x) = f x"

text {* This axclass is coupled to the locale by means of an interpretation: *}

interpretation idem_class:
  idem ["f \<Colon> ('a\<Colon>idem) \<Rightarrow> \<alpha>"]
by unfold_locales (rule idem)

(*<*) setup {* Sign.parent_path *} (*>*)

text {*
  This give you at hand the full power of the Isabelle module system;
  conclusions in locale @{text idem} are implicitly propagated
  to class @{idem}.
*}

subsection {* Abstract reasoning *}

text {*
  Isabelle locales enable reasoning at a general level, while results
  are implicitly transferred to all instances.  For example, we can
  now establish the @{text "left_cancel"} lemma for groups, which
  states that the function @{text "(x \<circ>)"} is injective:
*}

    lemma (in group) left_cancel: "x \<^loc>\<otimes> y = x \<^loc>\<otimes> z \<longleftrightarrow> y = z"
    proof
    assume "x \<^loc>\<otimes> y = x \<^loc>\<otimes> z"
      then have "x\<^loc>\<div> \<^loc>\<otimes> (x \<^loc>\<otimes> y) = x\<^loc>\<div> \<^loc>\<otimes> (x \<^loc>\<otimes> z)" by simp
      then have "(x\<^loc>\<div> \<^loc>\<otimes> x) \<^loc>\<otimes> y = (x\<^loc>\<div> \<^loc>\<otimes> x) \<^loc>\<otimes> z" using assoc by simp
      then show "y = z" using neutl and invl by simp
    next
    assume "y = z"
      then show "x \<^loc>\<otimes> y = x \<^loc>\<otimes> z" by simp
    qed

text {*
  \noindent Here the \qt{@{text "\<IN> group"}} target specification
  indicates that the result is recorded within that context for later
  use.  This local theorem is also lifted to the global one @{text
  "group.left_cancel:"} @{prop [source] "\<And>x y z::\<alpha>::group. x \<otimes> y = x \<otimes>
  z \<longleftrightarrow> y = z"}.  Since type @{text "int"} has been made an instance of
  @{text "group"} before, we may refer to that fact as well: @{prop
  [source] "\<And>x y z::int. x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"}.
*}


(*subsection {* Derived definitions *}

text {*
*}*)

(* subsection {* Additional subclass relations *}

text {*
  Any @{text "group"} is also a @{text "monoid"};  this
  can be made explicit by claiming an additional subclass relation,
  together with a proof of the logical difference:
*}

    instance group < monoid
    proof -
      fix x
      from invl have "x\<^loc>\<div> \<^loc>\<otimes> x = \<^loc>\<one>" by simp
      with assoc [symmetric] neutl invl have "x\<^loc>\<div> \<^loc>\<otimes> (x \<^loc>\<otimes> \<^loc>\<one>) = x\<^loc>\<div> \<^loc>\<otimes> x" by simp
      with left_cancel show "x \<^loc>\<otimes> \<^loc>\<one> = x" by simp
    qed *)

section {* Further issues *}

subsection {* Code generation *}

text {*
  Turning back to the first motivation for type classes,
  namely overloading, it is obvious that overloading
  stemming from @{text "\<CLASS>"} and @{text "\<INSTANCE>"}
  statements naturally maps to Haskell type classes.
  The code generator framework \cite{isabelle-codegen} 
  takes this into account.  Concerning target languages
  lacking type classes (e.g.~SML), type classes
  are implemented by explicit dictionary construction.
  As example, the natural power function on groups:
*}

    fun
      pow_nat :: "nat \<Rightarrow> \<alpha>\<Colon>monoidl \<Rightarrow> \<alpha>\<Colon>monoidl" where
      "pow_nat 0 x = \<one>"
      "pow_nat (Suc n) x = x \<otimes> pow_nat n x"

    definition
      pow_int :: "int \<Rightarrow> \<alpha>\<Colon>group \<Rightarrow> \<alpha>\<Colon>group" where
      "pow_int k x = (if k >= 0
        then pow_nat (nat k) x
        else (pow_nat (nat (- k)) x)\<div>)"

    definition
      example :: int where
      "example = pow_int 10 (-2)"

text {*
  \noindent This maps to Haskell as:
*}

code_gen example (Haskell "code_examples/")
  (* NOTE: you may use Haskell only once in this document, otherwise
  you have to work in distinct subdirectories *)

text {*
  \lsthaskell{Thy/code_examples/Classes.hs}

  \noindent (we have left out all other modules).

  \noindent The whole code in SML with explicit dictionary passing:
*}

code_gen example (*<*)(SML #)(*>*)(SML "code_examples/classes.ML")

text {*
  \lstsml{Thy/code_examples/classes.ML}
*}


(* subsection {* Different syntax for same specifications *}

text {*

(* subsection {* Syntactic classes *}
*)

*} *)

end

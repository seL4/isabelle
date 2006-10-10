
(* $Id$ *)

theory Classes
imports Main
begin

(*<*)
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
  The well-known concept of type classes
  \cite{wadler89how,peterson93implementing,hall96type,Nipkow-Prehofer:1993,Nipkow:1993,Wenzel:1997}
  offers a useful structuring mechanism for programs and proofs, which
  is more light-weight than a fully featured module mechanism.  Type
  classes are able to qualify types by associating operations and
  logical properties.  For example, class @{text "eq"} could provide
  an equivalence relation @{text "="} on type @{text "\<alpha>"}, and class
  @{text "ord"} could extend @{text "eq"} by providing a strict order
  @{text "<"} etc.

  Isabelle/Isar offers Haskell-style type classes, combining operational
  and logical specifications.
*}

section {* A simple algebra example \label{sec:example} *}

text {*
  We demonstrate common elements of structured specifications and
  abstract reasoning with type classes by the algebraic hierarchy of
  semigroups, monoids and groups.  Our background theory is that of
  Isabelle/HOL \cite{Nipkow-et-al:2002:tutorial}, which uses fairly
  standard notation from mathematics and functional programming.  We
  also refer to basic vernacular commands for definitions and
  statements, e.g.\ @{text "\<DEFINITION>"} and @{text "\<LEMMA>"};
  proofs will be recorded using structured elements of Isabelle/Isar
  \cite{Wenzel-PhD,Nipkow:2002}, notably @{text "\<PROOF>"}/@{text
  "\<QED>"} and @{text "\<FIX>"}/@{text "\<ASSUME>"}/@{text
  "\<SHOW>"}.

  Our main concern are the new @{text "\<CLASS>"}
  and @{text "\<INSTANCE>"} elements used below.
  Here we merely present the
  look-and-feel for end users, which is quite similar to Haskell's
  \texttt{class} and \texttt{instance} \cite{hall96type}, but
  augmented by logical specifications and proofs;
  Internally, those are mapped to more primitive Isabelle concepts.
  See \cite{haftmann_wenzel2006classes} for more detail.
*}


subsection {* Class definition *}

text {*
  Depending on an arbitrary type @{text "\<alpha>"}, class @{text
  "semigroup"} introduces a binary operation @{text "\<circ>"} that is
  assumed to be associative:
*}

    class semigroup =
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

  Another instance of @{text "semigroup"} are the natural numbers:
*}

    instance nat :: semigroup
      "m \<otimes> n \<equiv> m + n"
    proof
      fix m n q :: nat 
      show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)" unfolding semigroup_nat_def by simp
    qed

text {*
  Also @{text "list"}s form a semigroup with @{const "op @"} as
  operation:
*}

    instance list :: (type) semigroup
      "xs \<otimes> ys \<equiv> xs @ ys"
    proof
      fix xs ys zs :: "\<alpha> list"
      show "xs \<otimes> ys \<otimes> zs = xs \<otimes> (ys \<otimes> zs)"
      proof -
        from semigroup_list_def have "\<And>xs ys\<Colon>\<alpha> list. xs \<otimes> ys \<equiv> xs @ ys" .
        thus ?thesis by simp
      qed
    qed


subsection {* Subclasses *}

text {*
  We define a subclass @{text "monoidl"} (a semigroup with an left-hand neutral)
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
      "\<one> \<equiv> 0"
    proof
      fix n :: nat
      show "\<one> \<otimes> n = n" unfolding neutral_nat_def mult_nat_def by simp
    qed

    instance int :: monoidl
      "\<one> \<equiv> 0"
    proof
      fix k :: int
      show "\<one> \<otimes> k = k" unfolding neutral_int_def mult_int_def by simp
    qed

    instance list :: (type) monoidl
      "\<one> \<equiv> []"
    proof
      fix xs :: "\<alpha> list"
      show "\<one> \<otimes> xs = xs"
      proof -
	from mult_list_def have "\<And>xs ys\<Colon>'a list. xs \<otimes> ys \<equiv> xs @ ys" .
	moreover from mult_list_def neutral_list_def have "\<one> \<equiv> []\<Colon>\<alpha> list" by simp
	ultimately show ?thesis by simp
      qed
    qed  

text {*
  To finish our small algebra example, we add @{text "monoid"}
  and @{text "group"} classes with corresponding instances
*}

    class monoid = monoidl +
      assumes neutr: "x \<^loc>\<otimes> \<^loc>\<one> = x"

    instance nat :: monoid
    proof
      fix n :: nat
      show "n \<otimes> \<one> = n" unfolding neutral_nat_def mult_nat_def by simp
    qed

    instance int :: monoid
    proof
      fix k :: int
      show "k \<otimes> \<one> = k" unfolding neutral_int_def mult_int_def by simp
    qed

    instance list :: (type) monoid
    proof
      fix xs :: "\<alpha> list"
      show "xs \<otimes> \<one> = xs"
      proof -
	from mult_list_def have "\<And>xs ys\<Colon>\<alpha> list. xs \<otimes> ys \<equiv> xs @ ys" .
	moreover from mult_list_def neutral_list_def have "\<one> \<equiv> []\<Colon>'a list" by simp
	ultimately show ?thesis by simp
      qed
    qed  

    class group = monoidl +
      fixes inverse :: "\<alpha> \<Rightarrow> \<alpha>"    ("(_\<^loc>\<div>)" [1000] 999)
      assumes invl: "x\<^loc>\<div> \<^loc>\<otimes> x = \<^loc>\<one>"

    instance int :: group
      "i\<div> \<equiv> - i"
    proof
      fix i :: int
      have "-i + i = 0" by simp
      then show "i\<div> \<otimes> i = \<one>" unfolding mult_int_def and neutral_int_def and inverse_int_def .
    qed


subsection {* Abstract reasoning *}

text {*
  Abstract theories enable reasoning at a general level, while results
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


subsection {* Additional subclass relations *}

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
    qed


(* subsection {* Same logical content -- different syntax *}

text {*

*} *)


section {* Code generation *}

text {*
  Code generation takes account of type classes,
  resulting either in Haskell type classes or SML dictionaries.
  As example, we define the natural power function on groups:
*}

    function
      pow_nat :: "nat \<Rightarrow> 'a\<Colon>monoidl \<Rightarrow> 'a\<Colon>monoidl" where
      "pow_nat 0 x = \<one>"
      "pow_nat (Suc n) x = x \<otimes> pow_nat n x"
      by pat_completeness auto
    termination pow_nat by (auto_term "measure fst")
    declare pow_nat.simps [code func]

    definition
      pow_int :: "int \<Rightarrow> 'a\<Colon>group \<Rightarrow> 'a\<Colon>group"
      "pow_int k x = (if k >= 0
        then pow_nat (nat k) x
        else (pow_nat (nat (- k)) x)\<div>)"

    definition
      example :: int
      "example = pow_int 10 (-2)"

text {*
  \noindent Now we generate and compile code for SML:
*}

    code_gen example (SML -)

text {*
  \noindent The result is as expected:
*}

    ML {*
      if ROOT.Classes.example = ~20 then () else error "Wrong result"
    *}

end

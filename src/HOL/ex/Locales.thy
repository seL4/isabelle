(*  Title:      HOL/ex/Locales.thy
    ID:         $Id$
    Author:     Markus Wenzel, LMU München
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Using locales in Isabelle/Isar *}

theory Locales = Main:

text_raw {*
  \newcommand{\isasyminv}{\isasyminverse}
  \newcommand{\isasymIN}{\isatext{\isakeyword{in}}}
  \newcommand{\isasymINCLUDES}{\isatext{\isakeyword{includes}}}
*}

subsection {* Overview *}

text {*
  Locales provide a mechanism for encapsulating local contexts.  The
  original version due to Florian Kammüller \cite{Kamm-et-al:1999}
  refers directly to the raw meta-logic of Isabelle.  Semantically, a
  locale is just a (curried) predicate of the pure meta-logic
  \cite{Paulson:1989}.

  The present version for Isabelle/Isar builds on top of the rich
  infrastructure of proof contexts
  \cite{Wenzel:1999,Wenzel:2001:isar-ref,Wenzel:2001:Thesis},
  achieving a tight integration with Isar proof texts, and a slightly
  more abstract view of the underlying concepts.  An Isar proof
  context encapsulates certain language elements that correspond to
  @{text \<And>} (universal quantification), @{text \<Longrightarrow>} (implication), and
  @{text "\<equiv>"} (definitions) of the pure Isabelle framework.  Moreover,
  there are extra-logical concepts like term abbreviations or local
  theorem attributes (declarations of simplification rules etc.) that
  are indispensable in realistic applications.

  Locales support concrete syntax, providing a localized version of
  the existing concept of mixfix annotations of Isabelle
  \cite{Paulson:1994:Isabelle}.  Furthermore, there is a separate
  concept of ``implicit structures'' that admits to refer to
  particular locale parameters in a casual manner (essentially derived
  from the basic idea of ``anti-quotations'' or generalized de-Bruijn
  indexes demonstrated in \cite[\S13--14]{Wenzel:2001:Isar-examples}).

  Implicit structures work particular well together with extensible
  records in HOL \cite{Naraschewski-Wenzel:1998} (the
  ``object-oriented'' features discussed there are not required here).
  Thus we shall essentially use record types to represent polymorphic
  signatures of mathematical structures, while locales describe their
  logical properties as a predicate.  Due to type inference of
  simply-typed records we are able to give succinct specifications,
  without caring about signature morphisms ourselves.  Further
  eye-candy is provided by the independent concept of ``indexed
  concrete syntax'' for record selectors.

  Operations for building up locale contexts from existing definitions
  cover common operations of \emph{merge} (disjunctive union in
  canonical order) and \emph{rename} (of term parameters; types are
  always inferred automatically).

  \medskip Note that the following further concepts are still
  \emph{absent}:
  \begin{itemize}

  \item Specific language elements for \emph{instantiation} of
  locales.

  Currently users may simulate this to some extend by having primitive
  Isabelle/Isar operations (@{text of} for substitution and @{text OF}
  for composition, \cite{Wenzel:2001:isar-ref}) act on the
  automatically exported results stemming from different contexts.

  \item Interpretation of locales, analogous to ``functors'' in
  abstract algebra.

  In principle one could directly work with functions over structures
  (extensible records), and predicates being derived from locale
  definitions.

  \end{itemize}

  \medskip Subsequently, we demonstrate some readily available
  concepts of Isabelle/Isar locales by some simple examples of
  abstract algebraic reasoning.
*}

subsection {* Local contexts as mathematical structures *}

text {*
  The following definitions of @{text group} and @{text abelian_group}
  merely encapsulate local parameters (with private syntax) and
  assumptions; local definitions may be given as well, but are not
  shown here.
*}

locale group_context =
  fixes prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
    and inv :: "'a \<Rightarrow> 'a"    ("(_\<inv>)" [1000] 999)
    and one :: 'a    ("\<one>")
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and left_inv: "x\<inv> \<cdot> x = \<one>"
    and left_one: "\<one> \<cdot> x = x"

locale abelian_group_context = group_context +
  assumes commute: "x \<cdot> y = y \<cdot> x"

text {*
  \medskip We may now prove theorems within a local context, just by
  including a directive ``@{text "(\<IN> name)"}'' in the goal
  specification.  The final result will be stored within the named
  locale; a second copy is exported to the enclosing theory context.
*}

theorem (in group_context)
  right_inv: "x \<cdot> x\<inv> = \<one>"
proof -
  have "x \<cdot> x\<inv> = \<one> \<cdot> (x \<cdot> x\<inv>)" by (simp only: left_one)
  also have "\<dots> = \<one> \<cdot> x \<cdot> x\<inv>" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> x\<inv> \<cdot> x \<cdot> x\<inv>" by (simp only: left_inv)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> (x\<inv> \<cdot> x) \<cdot> x\<inv>" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> \<one> \<cdot> x\<inv>" by (simp only: left_inv)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> (\<one> \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> x\<inv>" by (simp only: left_one)
  also have "\<dots> = \<one>" by (simp only: left_inv)
  finally show ?thesis .
qed

theorem (in group_context)
  right_one: "x \<cdot> \<one> = x"
proof -
  have "x \<cdot> \<one> = x \<cdot> (x\<inv> \<cdot> x)" by (simp only: left_inv)
  also have "\<dots> = x \<cdot> x\<inv> \<cdot> x" by (simp only: assoc)
  also have "\<dots> = \<one> \<cdot> x" by (simp only: right_inv)
  also have "\<dots> = x" by (simp only: left_one)
  finally show ?thesis .
qed

text {*
  \medskip Apart from the named context we may also refer to further
  context elements (parameters, assumptions, etc.) in a casual manner;
  these are discharged when the proof is finished.
*}

theorem (in group_context)
  assumes eq: "e \<cdot> x = x"
  shows one_equality: "\<one> = e"
proof -
  have "\<one> = x \<cdot> x\<inv>" by (simp only: right_inv)
  also have "\<dots> = (e \<cdot> x) \<cdot> x\<inv>" by (simp only: eq)
  also have "\<dots> = e \<cdot> (x \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = e \<cdot> \<one>" by (simp only: right_inv)
  also have "\<dots> = e" by (simp only: right_one)
  finally show ?thesis .
qed

theorem (in group_context)
  assumes eq: "x' \<cdot> x = \<one>"
  shows inv_equality: "x\<inv> = x'"
proof -
  have "x\<inv> = \<one> \<cdot> x\<inv>" by (simp only: left_one)
  also have "\<dots> = (x' \<cdot> x) \<cdot> x\<inv>" by (simp only: eq)
  also have "\<dots> = x' \<cdot> (x \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = x' \<cdot> \<one>" by (simp only: right_inv)
  also have "\<dots> = x'" by (simp only: right_one)
  finally show ?thesis .
qed

theorem (in group_context)
  inv_prod: "(x \<cdot> y)\<inv> = y\<inv> \<cdot> x\<inv>"
proof (rule inv_equality)
  show "(y\<inv> \<cdot> x\<inv>) \<cdot> (x \<cdot> y) = \<one>"
  proof -
    have "(y\<inv> \<cdot> x\<inv>) \<cdot> (x \<cdot> y) = (y\<inv> \<cdot> (x\<inv> \<cdot> x)) \<cdot> y" by (simp only: assoc)
    also have "\<dots> = (y\<inv> \<cdot> \<one>) \<cdot> y" by (simp only: left_inv)
    also have "\<dots> = y\<inv> \<cdot> y" by (simp only: right_one)
    also have "\<dots> = \<one>" by (simp only: left_inv)
    finally show ?thesis .
  qed
qed

text {*
  \medskip Established results are automatically propagated through
  the hierarchy of locales.  Below we establish a trivial fact in
  commutative groups, while referring both to theorems of @{text
  group} and the additional assumption of @{text abelian_group}.
*}

theorem (in abelian_group_context)
  inv_prod': "(x \<cdot> y)\<inv> = x\<inv> \<cdot> y\<inv>"
proof -
  have "(x \<cdot> y)\<inv> = y\<inv> \<cdot> x\<inv>" by (rule inv_prod)
  also have "\<dots> = x\<inv> \<cdot> y\<inv>" by (rule commute)
  finally show ?thesis .
qed

text {*
  We see that the initial import of @{text group} within the
  definition of @{text abelian_group} is actually evaluated
  dynamically.  Thus any results in @{text group} are made available
  to the derived context of @{text abelian_group} as well.  Note that
  the alternative context element @{text \<INCLUDES>} would import
  existing locales in a static fashion, without participating in
  further facts emerging later on.

  \medskip Some more properties of inversion in general group theory
  follow.
*}

theorem (in group_context)
  inv_inv: "(x\<inv>)\<inv> = x"
proof (rule inv_equality)
  show "x \<cdot> x\<inv> = \<one>" by (simp only: right_inv)
qed

theorem (in group_context)
  assumes eq: "x\<inv> = y\<inv>"
  shows inv_inject: "x = y"
proof -
  have "x = x \<cdot> \<one>" by (simp only: right_one)
  also have "\<dots> = x \<cdot> (y\<inv> \<cdot> y)" by (simp only: left_inv)
  also have "\<dots> = x \<cdot> (x\<inv> \<cdot> y)" by (simp only: eq)
  also have "\<dots> = (x \<cdot> x\<inv>) \<cdot> y" by (simp only: assoc)
  also have "\<dots> = \<one> \<cdot> y" by (simp only: right_inv)
  also have "\<dots> = y" by (simp only: left_one)
  finally show ?thesis .
qed

text {*
  \bigskip We see that this representation of structures as local
  contexts is rather light-weight and convenient to use for abstract
  reasoning.  Here the ``components'' (the group operations) have been
  exhibited directly as context parameters; logically this corresponds
  to a curried predicate definition:

  @{thm [display] group_context_axioms_def [no_vars]}

  Occasionally, this ``externalized'' version of the informal idea of
  classes of tuple structures may cause some inconveniences,
  especially in meta-theoretical studies (involving functors from
  groups to groups, for example).

  Another minor drawback of the naive approach above is that concrete
  syntax will get lost on any kind of operation on the locale itself
  (such as renaming, copying, or instantiation).  Whenever the
  particular terminology of local parameters is affected the
  associated syntax would have to be changed as well, which is hard to
  achieve formally.
*}


subsection {* Explicit structures referenced implicitly *}

text {*
  We introduce the same hierarchy of basic group structures as above,
  this time using extensible record types for the signature part,
  together with concrete syntax for selector functions.
*}

record 'a semigroup =
  prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>\<index>" 70)

record 'a group = "'a semigroup" +
  inv :: "'a \<Rightarrow> 'a"    ("(_\<inv>\<index>)" [1000] 999)
  one :: 'a    ("\<one>\<index>")

text {*
  The mixfix annotations above include a special ``structure index
  indicator'' @{text \<index>} that makes gammer productions dependent on
  certain parameters that have been declared as ``structure'' in a
  locale context later on.  Thus we achieve casual notation as
  encountered in informal mathematics, e.g.\ @{text "x \<cdot> y"} for
  @{text "prod G x y"}.

  \medskip The following locale definitions introduce operate on a
  single parameter declared as ``\isakeyword{structure}''.  Type
  inference takes care to fill in the appropriate record type schemes
  internally.
*}

locale semigroup =
  fixes S :: "'a group"    (structure)
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale group = semigroup G +
  assumes left_inv: "x\<inv> \<cdot> x = \<one>"
    and left_one: "\<one> \<cdot> x = x"

text {*
  Note that we prefer to call the @{text group} record structure
  @{text G} rather than @{text S} inherited from @{text semigroup}.
  This does not affect our concrete syntax, which is only dependent on
  the \emph{positional} arrangements of currently active structures
  (actually only one above), rather than names.  In fact, these
  parameter names rarely occur in the term language at all (due to the
  ``indexed syntax'' facility of Isabelle).  On the other hand, names
  of locale facts will get qualified accordingly, e.g. @{text S.assoc}
  versus @{text G.assoc}.

  \medskip We may now proceed to prove results within @{text group}
  just as before for @{text group}.  The subsequent proof texts are
  exactly the same as despite the more advanced internal arrangement.
*}

theorem (in group)
  right_inv: "x \<cdot> x\<inv> = \<one>"
proof -
  have "x \<cdot> x\<inv> = \<one> \<cdot> (x \<cdot> x\<inv>)" by (simp only: left_one)
  also have "\<dots> = \<one> \<cdot> x \<cdot> x\<inv>" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> x\<inv> \<cdot> x \<cdot> x\<inv>" by (simp only: left_inv)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> (x\<inv> \<cdot> x) \<cdot> x\<inv>" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> \<one> \<cdot> x\<inv>" by (simp only: left_inv)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> (\<one> \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = (x\<inv>)\<inv> \<cdot> x\<inv>" by (simp only: left_one)
  also have "\<dots> = \<one>" by (simp only: left_inv)
  finally show ?thesis .
qed

theorem (in group)
  right_one: "x \<cdot> \<one> = x"
proof -
  have "x \<cdot> \<one> = x \<cdot> (x\<inv> \<cdot> x)" by (simp only: left_inv)
  also have "\<dots> = x \<cdot> x\<inv> \<cdot> x" by (simp only: assoc)
  also have "\<dots> = \<one> \<cdot> x" by (simp only: right_inv)
  also have "\<dots> = x" by (simp only: left_one)
  finally show ?thesis .
qed

text {*
  \medskip Several implicit structures may be active at the same time.
  The concrete syntax facility for locales actually maintains indexed
  structures that may be references implicitly --- via mixfix
  annotations that have been decorated by an ``index argument''
  (@{text \<index>}).

  The following synthetic example demonstrates how to refer to several
  structures of type @{text group} succinctly.  We work with two
  versions of the @{text group} locale above.
*}

lemma
  includes group G
  includes group H
  shows "x \<cdot> y \<cdot> \<one> = prod G (prod G x y) (one G)"
    and "x \<cdot>\<^sub>2 y \<cdot>\<^sub>2 \<one>\<^sub>2 = prod H (prod H x y) (one H)"
    and "x \<cdot> \<one>\<^sub>2 = prod G x (one H)"
  by (rule refl)+

text {*
  Note that the trivial statements above need to be given as a
  simultaneous goal in order to have type-inference make the implicit
  typing of structures @{text G} and @{text H} agree.
*}

end

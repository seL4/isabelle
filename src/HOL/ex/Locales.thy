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
  refers directly to Isabelle's meta-logic \cite{Paulson:1989}, which
  is minimal higher-order logic with connectives @{text "\<And>"}
  (universal quantification), @{text "\<Longrightarrow>"} (implication), and @{text
  "\<equiv>"} (equality).

  From this perspective, a locale is essentially a meta-level
  predicate, together with some infrastructure to manage the
  abstracted parameters (@{text "\<And>"}), assumptions (@{text "\<Longrightarrow>"}), and
  definitions for (@{text "\<equiv>"}) in a reasonable way during the proof
  process.  This simple predicate view also provides a solid
  semantical basis for our specification concepts to be developed
  later.

  \medskip The present version of locales for Isabelle/Isar builds on
  top of the rich infrastructure of proof contexts
  \cite{Wenzel:1999,Wenzel:2001:isar-ref,Wenzel:2001:Thesis}, which in
  turn is based on the same meta-logic.  Thus we achieve a tight
  integration with Isar proof texts, and a slightly more abstract view
  of the underlying logical concepts.  An Isar proof context
  encapsulates certain language elements that correspond to @{text
  "\<And>/\<Longrightarrow>/\<equiv>"} at the level of structure proof texts.  Moreover, there are
  extra-logical concepts like term abbreviations or local theorem
  attributes (declarations of simplification rules etc.) that are
  useful in applications (e.g.\ consider standard simplification rules
  declared in a group context).

  Locales also support concrete syntax, i.e.\ a localized version of
  the existing concept of mixfix annotations of Isabelle
  \cite{Paulson:1994:Isabelle}.  Furthermore, there is a separate
  concept of ``implicit structures'' that admits to refer to
  particular locale parameters in a casual manner (basically a
  simplified version of the idea of ``anti-quotations'', or
  generalized de-Bruijn indexes as demonstrated elsewhere
  \cite[\S13--14]{Wenzel:2001:Isar-examples}).

  Implicit structures work particular well together with extensible
  records in HOL \cite{Naraschewski-Wenzel:1998} (without the
  ``object-oriented'' features discussed there as well).  Thus we
  achieve a specification technique where record type schemes
  represent polymorphic signatures of mathematical structures, and
  actual locales describe the corresponding logical properties.
  Semantically speaking, such abstract mathematical structures are
  just predicates over record types.  Due to type inference of
  simply-typed records (which subsumes structural subtyping) we arrive
  at succinct specification texts --- ``signature morphisms''
  degenerate to implicit type-instantiations.  Additional eye-candy is
  provided by the separate concept of ``indexed concrete syntax'' used
  for record selectors, so we get close to informal mathematical
  notation.

  \medskip Operations for building up locale contexts from existing
  ones include \emph{merge} (disjoint union) and \emph{rename} (of
  term parameters only, types are inferred automatically).  Here we
  draw from existing traditions of algebraic specification languages.
  A structured specification corresponds to a directed acyclic graph
  of potentially renamed nodes (due to distributivity renames may
  pushed inside of merges).  The result is a ``flattened'' list of
  primitive context elements in canonical order (corresponding to
  left-to-right reading of merges, while suppressing duplicates).

  \medskip The present version of Isabelle/Isar locales still lacks
  some important specification concepts.

  \begin{itemize}

  \item Separate language elements for \emph{instantiation} of
  locales.

  Currently users may simulate this to some extend by having primitive
  Isabelle/Isar operations (@{text of} for substitution and @{text OF}
  for composition, \cite{Wenzel:2001:isar-ref}) act on the
  automatically exported results stemming from different contexts.

  \item Interpretation of locales (think of ``views'', ``functors''
  etc.).

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
  The following definitions of @{text group_context} and @{text
  abelian_group_context} merely encapsulate local parameters (with
  private syntax) and assumptions; local definitions of derived
  concepts could be given, too, but are unused below.
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
  locale, still holding the context; a second copy is exported to the
  enclosing theory context (with qualified name).
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
  Facts like @{text right_one} are available @{text group_context} as
  stated above.  The exported version looses the additional
  infrastructure of Isar proof contexts (syntax etc.) retaining only
  the pure logical content: @{thm [source] group_context.right_one}
  becomes @{thm group_context.right_one} (in Isabelle outermost @{text
  \<And>} quantification is replaced by schematic variables).

  \medskip Apart from a named locale we may also refer to further
  context elements (parameters, assumptions, etc.) in an ad-hoc
  fashion, just for this particular statement.  In the result (local
  or global), any additional elements are discharged as usual.
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

  @{thm [display] group_context_def [no_vars]}

  The corresponding introduction rule is as follows:

  @{thm [display, mode = no_brackets] group_context.intro [no_vars]}

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
  indicator'' @{text \<index>} that makes grammar productions dependent on
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
  fixes S    (structure)
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale group = semigroup G +
  assumes left_inv: "x\<inv> \<cdot> x = \<one>"
    and left_one: "\<one> \<cdot> x = x"

declare semigroup.intro [intro?]
  group.intro [intro?] group_axioms.intro [intro?]

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


subsection {* Simple meta-theory of structures *}

text {*
  The packaging of the logical specification as a predicate and the
  syntactic structure as a record type provides a reasonable starting
  point for simple meta-theoretic studies of mathematical structures.
  This includes operations on structures (also known as ``functors''),
  and statements about such constructions.

  For example, the direct product of semigroups works as follows.
*}

constdefs
  semigroup_product :: "'a semigroup \<Rightarrow> 'b semigroup \<Rightarrow> ('a \<times> 'b) semigroup"
  "semigroup_product S T \<equiv>
    \<lparr>prod = \<lambda>p q. (prod S (fst p) (fst q), prod T (snd p) (snd q))\<rparr>"

lemma semigroup_product [intro]:
  assumes S: "semigroup S"
    and T: "semigroup T"
  shows "semigroup (semigroup_product S T)"
proof
  fix p q r :: "'a \<times> 'b"
  have "prod S (prod S (fst p) (fst q)) (fst r) =
      prod S (fst p) (prod S (fst q) (fst r))"
    by (rule semigroup.assoc [OF S])
  moreover have "prod T (prod T (snd p) (snd q)) (snd r) =
      prod T (snd p) (prod T (snd q) (snd r))"
    by (rule semigroup.assoc [OF T])
  ultimately
  show "prod (semigroup_product S T) (prod (semigroup_product S T) p q) r =
      prod (semigroup_product S T) p (prod (semigroup_product S T) q r)"
    by (simp add: semigroup_product_def)
qed

text {*
  The above proof is fairly easy, but obscured by the lack of concrete
  syntax.  In fact, we didn't make use of the infrastructure of
  locales, apart from the raw predicate definition of @{text
  semigroup}.

  The alternative version below uses local context expressions to
  achieve a succinct proof body.  The resulting statement is exactly
  the same as before, even though its specification is a bit more
  complex.
*}

lemma
  includes semigroup S + semigroup T
  fixes U    (structure)
  defines "U \<equiv> semigroup_product S T"
  shows "semigroup U"
proof
  fix p q r :: "'a \<times> 'b"
  have "(fst p \<cdot>\<^sub>1 fst q) \<cdot>\<^sub>1 fst r = fst p \<cdot>\<^sub>1 (fst q \<cdot>\<^sub>1 fst r)"
    by (rule S.assoc)
  moreover have "(snd p \<cdot>\<^sub>2 snd q) \<cdot>\<^sub>2 snd r = snd p \<cdot>\<^sub>2 (snd q \<cdot>\<^sub>2 snd r)"
    by (rule T.assoc)
  ultimately show "(p \<cdot>\<^sub>3 q) \<cdot>\<^sub>3 r = p \<cdot>\<^sub>3 (q \<cdot>\<^sub>3 r)"
    by (simp add: U_def semigroup_product_def semigroup.defs)
qed

text {*
  Direct products of group structures may be defined in a similar
  manner, taking two further operations into account.  Subsequently,
  we use high-level record operations to convert between different
  signature types explicitly; see also
  \cite[\S8.3]{isabelle-hol-book}.
*}

constdefs
  group_product :: "'a group \<Rightarrow> 'b group \<Rightarrow> ('a \<times> 'b) group"
  "group_product G H \<equiv>
    semigroup.extend
      (semigroup_product (semigroup.truncate G) (semigroup.truncate H))
      (group.fields (\<lambda>p. (inv G (fst p), inv H (snd p))) (one G, one H))"

lemma group_product_aux:
  includes group G + group H
  fixes I    (structure)
  defines "I \<equiv> group_product G H"
  shows "group I"
proof
  show "semigroup I"
  proof -
    let ?G' = "semigroup.truncate G" and ?H' = "semigroup.truncate H"
    have "prod (semigroup_product ?G' ?H') = prod I"
      by (simp add: I_def group_product_def group.defs
	semigroup_product_def semigroup.defs)
    moreover
    have "semigroup ?G'" and "semigroup ?H'"
      using prems by (simp_all add: semigroup_def semigroup.defs)
    then have "semigroup (semigroup_product ?G' ?H')" ..
    ultimately show ?thesis by (simp add: I_def semigroup_def)
  qed
  show "group_axioms I"
  proof
    fix p :: "'a \<times> 'b"
    have "(fst p)\<inv>\<^sub>1 \<cdot>\<^sub>1 fst p = \<one>\<^sub>1"
      by (rule G.left_inv)
    moreover have "(snd p)\<inv>\<^sub>2 \<cdot>\<^sub>2 snd p = \<one>\<^sub>2"
      by (rule H.left_inv)
    ultimately show "p\<inv>\<^sub>3 \<cdot>\<^sub>3 p = \<one>\<^sub>3"
      by (simp add: I_def group_product_def group.defs
	semigroup_product_def semigroup.defs)
    have "\<one>\<^sub>1 \<cdot>\<^sub>1 fst p = fst p" by (rule G.left_one)
    moreover have "\<one>\<^sub>2 \<cdot>\<^sub>2 snd p = snd p" by (rule H.left_one)
    ultimately show "\<one>\<^sub>3 \<cdot>\<^sub>3 p = p"
      by (simp add: I_def group_product_def group.defs
	semigroup_product_def semigroup.defs)
  qed
qed

theorem group_product: "group G \<Longrightarrow> group H \<Longrightarrow> group (group_product G H)"
  by (rule group_product_aux) (assumption | rule group.axioms)+

end

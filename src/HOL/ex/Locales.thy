(*  Title:      HOL/ex/Locales.thy
    ID:         $Id$
    Author:     Markus Wenzel, LMU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Basic use of locales in Isabelle/Isar *}

theory Locales = Main:

text {*
  Locales provide a mechanism for encapsulating local contexts.  The
  original version due to Florian Kamm\"uller \cite{Kamm-et-al:1999}
  refers directly to the raw meta-logic of Isabelle.  The present
  version for Isabelle/Isar
  \cite{Wenzel:1999,Wenzel:2001:isar-ref,Wenzel:2001:Thesis} builds on
  top of the rich infrastructure of proof contexts instead; this also
  covers essential extra-logical concepts like term abbreviations or
  local theorem attributes (e.g.\ declarations of simplification
  rules).

  Subsequently, we demonstrate basic use of locales to model
  mathematical structures (by the inevitable group theory example).
*}

text_raw {*
  \newcommand{\isasyminv}{\isasyminverse}
  \newcommand{\isasymIN}{\isatext{\isakeyword{in}}}
*}


subsection {* Local contexts as mathematical structures *}

text {*
  The following definitions of @{text group} and @{text abelian_group}
  merely encapsulate local parameters (with private syntax) and
  assumptions; local definitions may be given as well, but are not
  shown here.
*}

locale group =
  fixes prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
    and inv :: "'a \<Rightarrow> 'a"    ("(_\<inv>)" [1000] 999)
    and one :: 'a    ("\<one>")
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and left_inv: "x\<inv> \<cdot> x = \<one>"
    and left_one: "\<one> \<cdot> x = x"

locale abelian_group = group +
  assumes commute: "x \<cdot> y = y \<cdot> x"

text {*
  \medskip We may now prove theorems within a local context, just by
  including a directive ``@{text "(\<IN> name)"}'' in the goal
  specification.  The final result will be stored within the named
  locale; a second copy is exported to the enclosing theory context.
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
  \medskip Apart from the named context we may also refer to further
  context elements (parameters, assumptions, etc.) in a casual manner;
  these are discharged when the proof is finished.
*}

theorem (in group)
  (assumes eq: "e \<cdot> x = x")
  one_equality: "\<one> = e"
proof -
  have "\<one> = x \<cdot> x\<inv>" by (simp only: right_inv)
  also have "\<dots> = (e \<cdot> x) \<cdot> x\<inv>" by (simp only: eq)
  also have "\<dots> = e \<cdot> (x \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = e \<cdot> \<one>" by (simp only: right_inv)
  also have "\<dots> = e" by (simp only: right_one)
  finally show ?thesis .
qed

theorem (in group)
  (assumes eq: "x' \<cdot> x = \<one>")
  inv_equality: "x\<inv> = x'"
proof -
  have "x\<inv> = \<one> \<cdot> x\<inv>" by (simp only: left_one)
  also have "\<dots> = (x' \<cdot> x) \<cdot> x\<inv>" by (simp only: eq)
  also have "\<dots> = x' \<cdot> (x \<cdot> x\<inv>)" by (simp only: assoc)
  also have "\<dots> = x' \<cdot> \<one>" by (simp only: right_inv)
  also have "\<dots> = x'" by (simp only: right_one)
  finally show ?thesis .
qed

theorem (in group)
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

theorem (in abelian_group)
  inv_prod': "(x \<cdot> y)\<inv> = x\<inv> \<cdot> y\<inv>"
proof -
  have "(x \<cdot> y)\<inv> = y\<inv> \<cdot> x\<inv>" by (rule inv_prod)
  also have "\<dots> = x\<inv> \<cdot> y\<inv>" by (rule commute)
  finally show ?thesis .
qed

text {*
  \medskip Some further properties of inversion in general group
  theory follow.
*}

theorem (in group)
  inv_inv: "(x\<inv>)\<inv> = x"
proof (rule inv_equality)
  show "x \<cdot> x\<inv> = \<one>" by (simp only: right_inv)
qed

theorem (in group)
  (assumes eq: "x\<inv> = y\<inv>")
  inv_inject: "x = y"
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
  to a curried predicate definition.  Occasionally, this
  ``externalized'' version of the informal idea of classes of tuple
  structures may cause some inconveniences, especially in
  meta-theoretical studies (involving functors from groups to groups,
  for example).

  Another drawback of the naive approach above is that concrete syntax
  will get lost on any kind of operation on the locale itself (such as
  renaming, copying, or instantiation).  Whenever the particular
  terminology of local parameters is affected the associated syntax
  would have to be changed as well, which is hard to achieve formally.
*}


subsection {* Explicit structures referenced implicitly *}

text {*
  The issue of multiple parameters raised above may be easily
  addressed by stating properties over a record of group operations,
  instead of the individual constituents.  See
  \cite{Naraschewski-Wenzel:1998,Nipkow-et-al:2001:HOL} on
  (extensible) record types in Isabelle/HOL.
*}

record 'a group =
  prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  inv :: "'a \<Rightarrow> 'a"
  one :: 'a

text {*
  Now concrete syntax essentially needs refer to record selections;
  this is possible by giving defined operations with private syntax
  within the locale (e.g.\ see appropriate examples by Kamm\"uller).

  In the subsequent formulation of group structures we go one step
  further by using \emph{implicit} references to the underlying
  abstract entity.  To this end we define global syntax, which is
  translated to refer to the ``current'' structure at hand, denoted by
  the dummy item ``@{text \<struct>}'' (according to the builtin syntax
  mechanism for locales).
*}

syntax
  "_prod" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
  "_inv" :: "'a \<Rightarrow> 'a"    ("(_\<inv>)" [1000] 999)
  "_one" :: 'a    ("\<one>")
translations
  "x \<cdot> y"  \<rightleftharpoons>  "prod \<struct> x y"
  "x\<inv>"  \<rightleftharpoons>  "inv \<struct> x"
  "\<one>"  \<rightleftharpoons>  "one \<struct>"

text {*
  The following locale definition introduces a single parameter, which
  is declared as a ``\isakeyword{structure}''. In its context the
  dummy ``@{text \<struct>}'' refers to this very parameter, independently of
  the present naming.
*}

locale group_struct =
  fixes G :: "'a group"    (structure)
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and left_inv: "x\<inv> \<cdot> x = \<one>"
    and left_one: "\<one> \<cdot> x = x"

text {*
  We may now proceed to prove results within @{text group_struct} just
  as before for @{text group}.  Proper treatment of ``@{text \<struct>}'' is
  hidden in concrete syntax, so the proof text is exactly the same as
  before.
*}

theorem (in group_struct)
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

theorem (in group_struct)
  right_one: "x \<cdot> \<one> = x"
proof -
  have "x \<cdot> \<one> = x \<cdot> (x\<inv> \<cdot> x)" by (simp only: left_inv)
  also have "\<dots> = x \<cdot> x\<inv> \<cdot> x" by (simp only: assoc)
  also have "\<dots> = \<one> \<cdot> x" by (simp only: right_inv)
  also have "\<dots> = x" by (simp only: left_one)
  finally show ?thesis .
qed

text {*
  \medskip Several implicit structures may be active at the same time
  (say up to 3 in practice).  The concrete syntax facility for locales
  actually maintains indexed dummies @{text "\<struct>\<^sub>1"}, @{text
  "\<struct>\<^sub>2"}, @{text "\<struct>\<^sub>3"}, \dots (@{text \<struct>} is the same as
  @{text "\<struct>\<^sub>1"}).  So we are able to provide concrete syntax to
  cover the 2nd and 3rd group structure as well.
*}

syntax
  "_prod'" :: "'a \<Rightarrow> index \<Rightarrow> 'a \<Rightarrow> 'a"    ("(_ \<cdot>_/ _)" [70, 1000, 71] 70)
  "_inv'" :: "'a \<Rightarrow> index \<Rightarrow> 'a"    ("(_\<inv>_)" [1000] 999)
  "_one'" :: "index \<Rightarrow> 'a"    ("\<one>_")
translations
  "x \<cdot>\<^sub>2 y"  \<rightleftharpoons>  "prod \<struct>\<^sub>2 x y"
  "x \<cdot>\<^sub>3 y"  \<rightleftharpoons>  "prod \<struct>\<^sub>3 x y"
  "x\<inv>\<^sub>2"  \<rightleftharpoons>  "inv \<struct>\<^sub>2 x"
  "x\<inv>\<^sub>3"  \<rightleftharpoons>  "inv \<struct>\<^sub>3 x"
  "\<one>\<^sub>2"  \<rightleftharpoons>  "one \<struct>\<^sub>2"
  "\<one>\<^sub>3"  \<rightleftharpoons>  "one \<struct>\<^sub>3"

text {*
  \medskip The following synthetic example demonstrates how to refer
  to several structures of type @{text group} succinctly; one might
  also think of working with several renamed versions of the @{text
  group_struct} locale above.
*}

lemma
  (fixes G :: "'a group" (structure)
    and H :: "'a group" (structure))
  True
proof
  have "x \<cdot> y \<cdot> \<one> = prod G (prod G x y) (one G)" ..
  have "x \<cdot>\<^sub>2 y \<cdot>\<^sub>2 \<one>\<^sub>2 = prod H (prod H x y) (one H)" ..
  have "x \<cdot> \<one>\<^sub>2 = prod G x (one H)" ..
qed

text {*
  \medskip As a minor drawback of this advanced technique we require
  slightly more work to setup abstract and concrete syntax properly
  (but only once in the beginning).  The resulting casual mode of
  writing @{text "x \<cdot> y"} for @{text "prod G x y"} etc.\ mimics common
  practice of informal mathematics quite nicely, while using a simple
  and robust formal representation.
*}

end

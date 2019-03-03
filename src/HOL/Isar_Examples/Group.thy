(*  Title:      HOL/Isar_Examples/Group.thy
    Author:     Makarius
*)

section \<open>Basic group theory\<close>

theory Group
  imports Main
begin

subsection \<open>Groups and calculational reasoning\<close> 

text \<open>
  Groups over signature \<open>(* :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>, 1 :: \<alpha>, inverse :: \<alpha> \<Rightarrow> \<alpha>)\<close> are
  defined as an axiomatic type class as follows. Note that the parent classes
  \<^class>\<open>times\<close>, \<^class>\<open>one\<close>, \<^class>\<open>inverse\<close> is provided by the basic HOL theory.
\<close>

class group = times + one + inverse +
  assumes group_assoc: "(x * y) * z = x * (y * z)"
    and group_left_one: "1 * x = x"
    and group_left_inverse: "inverse x * x = 1"

text \<open>
  The group axioms only state the properties of left one and inverse, the
  right versions may be derived as follows.
\<close>

theorem (in group) group_right_inverse: "x * inverse x = 1"
proof -
  have "x * inverse x = 1 * (x * inverse x)"
    by (simp only: group_left_one)
  also have "\<dots> = 1 * x * inverse x"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * inverse x * x * inverse x"
    by (simp only: group_left_inverse)
  also have "\<dots> = inverse (inverse x) * (inverse x * x) * inverse x"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * 1 * inverse x"
    by (simp only: group_left_inverse)
  also have "\<dots> = inverse (inverse x) * (1 * inverse x)"
    by (simp only: group_assoc)
  also have "\<dots> = inverse (inverse x) * inverse x"
    by (simp only: group_left_one)
  also have "\<dots> = 1"
    by (simp only: group_left_inverse)
  finally show ?thesis .
qed

text \<open>
  With \<open>group_right_inverse\<close> already available, \<open>group_right_one\<close>
  is now established much easier.
\<close>

theorem (in group) group_right_one: "x * 1 = x"
proof -
  have "x * 1 = x * (inverse x * x)"
    by (simp only: group_left_inverse)
  also have "\<dots> = x * inverse x * x"
    by (simp only: group_assoc)
  also have "\<dots> = 1 * x"
    by (simp only: group_right_inverse)
  also have "\<dots> = x"
    by (simp only: group_left_one)
  finally show ?thesis .
qed

text \<open>
  \<^medskip>
  The calculational proof style above follows typical presentations given in
  any introductory course on algebra. The basic technique is to form a
  transitive chain of equations, which in turn are established by simplifying
  with appropriate rules. The low-level logical details of equational
  reasoning are left implicit.

  Note that ``\<open>\<dots>\<close>'' is just a special term variable that is bound
  automatically to the argument\<^footnote>\<open>The argument of a curried infix expression
  happens to be its right-hand side.\<close> of the last fact achieved by any local
  assumption or proven statement. In contrast to \<open>?thesis\<close>, the ``\<open>\<dots>\<close>''
  variable is bound \<^emph>\<open>after\<close> the proof is finished.

  There are only two separate Isar language elements for calculational proofs:
  ``\<^theory_text>\<open>also\<close>'' for initial or intermediate calculational steps, and
  ``\<^theory_text>\<open>finally\<close>'' for exhibiting the result of a calculation. These constructs
  are not hardwired into Isabelle/Isar, but defined on top of the basic
  Isar/VM interpreter. Expanding the \<^theory_text>\<open>also\<close> and \<^theory_text>\<open>finally\<close> derived language
  elements, calculations may be simulated by hand as demonstrated below.
\<close>

theorem (in group) "x * 1 = x"
proof -
  have "x * 1 = x * (inverse x * x)"
    by (simp only: group_left_inverse)

  note calculation = this
    \<comment> \<open>first calculational step: init calculation register\<close>

  have "\<dots> = x * inverse x * x"
    by (simp only: group_assoc)

  note calculation = trans [OF calculation this]
    \<comment> \<open>general calculational step: compose with transitivity rule\<close>

  have "\<dots> = 1 * x"
    by (simp only: group_right_inverse)

  note calculation = trans [OF calculation this]
    \<comment> \<open>general calculational step: compose with transitivity rule\<close>

  have "\<dots> = x"
    by (simp only: group_left_one)

  note calculation = trans [OF calculation this]
    \<comment> \<open>final calculational step: compose with transitivity rule \dots\<close>
  from calculation
    \<comment> \<open>\dots\ and pick up the final result\<close>

  show ?thesis .
qed

text \<open>
  Note that this scheme of calculations is not restricted to plain
  transitivity. Rules like anti-symmetry, or even forward and backward
  substitution work as well. For the actual implementation of \<^theory_text>\<open>also\<close> and
  \<^theory_text>\<open>finally\<close>, Isabelle/Isar maintains separate context information of
  ``transitivity'' rules. Rule selection takes place automatically by
  higher-order unification.
\<close>


subsection \<open>Groups as monoids\<close>

text \<open>
  Monoids over signature \<open>(* :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>, 1 :: \<alpha>)\<close> are defined like this.
\<close>

class monoid = times + one +
  assumes monoid_assoc: "(x * y) * z = x * (y * z)"
    and monoid_left_one: "1 * x = x"
    and monoid_right_one: "x * 1 = x"

text \<open>
  Groups are \<^emph>\<open>not\<close> yet monoids directly from the definition. For monoids,
  \<open>right_one\<close> had to be included as an axiom, but for groups both \<open>right_one\<close>
  and \<open>right_inverse\<close> are derivable from the other axioms. With
  \<open>group_right_one\<close> derived as a theorem of group theory (see @{thm
  group_right_one}), we may still instantiate \<open>group \<subseteq> monoid\<close> properly as
  follows.
\<close>

instance group \<subseteq> monoid
  by intro_classes
    (rule group_assoc,
      rule group_left_one,
      rule group_right_one)

text \<open>
  The \<^theory_text>\<open>instance\<close> command actually is a version of \<^theory_text>\<open>theorem\<close>, setting up a
  goal that reflects the intended class relation (or type constructor arity).
  Thus any Isar proof language element may be involved to establish this
  statement. When concluding the proof, the result is transformed into the
  intended type signature extension behind the scenes.
\<close>


subsection \<open>More theorems of group theory\<close>

text \<open>
  The one element is already uniquely determined by preserving an \<^emph>\<open>arbitrary\<close>
  group element.
\<close>

theorem (in group) group_one_equality:
  assumes eq: "e * x = x"
  shows "1 = e"
proof -
  have "1 = x * inverse x"
    by (simp only: group_right_inverse)
  also have "\<dots> = (e * x) * inverse x"
    by (simp only: eq)
  also have "\<dots> = e * (x * inverse x)"
    by (simp only: group_assoc)
  also have "\<dots> = e * 1"
    by (simp only: group_right_inverse)
  also have "\<dots> = e"
    by (simp only: group_right_one)
  finally show ?thesis .
qed

text \<open>
  Likewise, the inverse is already determined by the cancel property.
\<close>

theorem (in group) group_inverse_equality:
  assumes eq: "x' * x = 1"
  shows "inverse x = x'"
proof -
  have "inverse x = 1 * inverse x"
    by (simp only: group_left_one)
  also have "\<dots> = (x' * x) * inverse x"
    by (simp only: eq)
  also have "\<dots> = x' * (x * inverse x)"
    by (simp only: group_assoc)
  also have "\<dots> = x' * 1"
    by (simp only: group_right_inverse)
  also have "\<dots> = x'"
    by (simp only: group_right_one)
  finally show ?thesis .
qed

text \<open>
  The inverse operation has some further characteristic properties.
\<close>

theorem (in group) group_inverse_times: "inverse (x * y) = inverse y * inverse x"
proof (rule group_inverse_equality)
  show "(inverse y * inverse x) * (x * y) = 1"
  proof -
    have "(inverse y * inverse x) * (x * y) =
        (inverse y * (inverse x * x)) * y"
      by (simp only: group_assoc)
    also have "\<dots> = (inverse y * 1) * y"
      by (simp only: group_left_inverse)
    also have "\<dots> = inverse y * y"
      by (simp only: group_right_one)
    also have "\<dots> = 1"
      by (simp only: group_left_inverse)
    finally show ?thesis .
  qed
qed

theorem (in group) inverse_inverse: "inverse (inverse x) = x"
proof (rule group_inverse_equality)
  show "x * inverse x = one"
    by (simp only: group_right_inverse)
qed

theorem (in group) inverse_inject:
  assumes eq: "inverse x = inverse y"
  shows "x = y"
proof -
  have "x = x * 1"
    by (simp only: group_right_one)
  also have "\<dots> = x * (inverse y * y)"
    by (simp only: group_left_inverse)
  also have "\<dots> = x * (inverse x * y)"
    by (simp only: eq)
  also have "\<dots> = (x * inverse x) * y"
    by (simp only: group_assoc)
  also have "\<dots> = 1 * y"
    by (simp only: group_right_inverse)
  also have "\<dots> = y"
    by (simp only: group_left_one)
  finally show ?thesis .
qed

end

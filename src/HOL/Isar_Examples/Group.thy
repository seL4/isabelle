(*  Title:      HOL/Isar_Examples/Group.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Basic group theory *}

theory Group
imports Main
begin

subsection {* Groups and calculational reasoning *} 

text {* Groups over signature $({\times} :: \alpha \To \alpha \To
  \alpha, \idt{one} :: \alpha, \idt{inverse} :: \alpha \To \alpha)$
  are defined as an axiomatic type class as follows.  Note that the
  parent class $\idt{times}$ is provided by the basic HOL theory. *}

class group = times + one + inverse +
  assumes group_assoc: "(x * y) * z = x * (y * z)"
    and group_left_one: "1 * x = x"
    and group_left_inverse: "inverse x * x = 1"

text {* The group axioms only state the properties of left one and
  inverse, the right versions may be derived as follows. *}

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

text {* With \name{group-right-inverse} already available,
  \name{group-right-one}\label{thm:group-right-one} is now established
  much easier. *}

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

text {* \medskip The calculational proof style above follows typical
  presentations given in any introductory course on algebra.  The
  basic technique is to form a transitive chain of equations, which in
  turn are established by simplifying with appropriate rules.  The
  low-level logical details of equational reasoning are left implicit.

  Note that ``$\dots$'' is just a special term variable that is bound
  automatically to the argument\footnote{The argument of a curried
  infix expression happens to be its right-hand side.} of the last
  fact achieved by any local assumption or proven statement.  In
  contrast to $\var{thesis}$, the ``$\dots$'' variable is bound
  \emph{after} the proof is finished, though.

  There are only two separate Isar language elements for calculational
  proofs: ``\isakeyword{also}'' for initial or intermediate
  calculational steps, and ``\isakeyword{finally}'' for exhibiting the
  result of a calculation.  These constructs are not hardwired into
  Isabelle/Isar, but defined on top of the basic Isar/VM interpreter.
  Expanding the \isakeyword{also} and \isakeyword{finally} derived
  language elements, calculations may be simulated by hand as
  demonstrated below.
*}

theorem (in group) "x * 1 = x"
proof -
  have "x * 1 = x * (inverse x * x)"
    by (simp only: group_left_inverse)

  note calculation = this
    -- {* first calculational step: init calculation register *}

  have "\<dots> = x * inverse x * x"
    by (simp only: group_assoc)

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *}

  have "\<dots> = 1 * x"
    by (simp only: group_right_inverse)

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *}

  have "\<dots> = x"
    by (simp only: group_left_one)

  note calculation = trans [OF calculation this]
    -- {* final calculational step: compose with transitivity rule \dots *}
  from calculation
    -- {* \dots\ and pick up the final result *}

  show ?thesis .
qed

text {* Note that this scheme of calculations is not restricted to
  plain transitivity.  Rules like anti-symmetry, or even forward and
  backward substitution work as well.  For the actual implementation
  of \isacommand{also} and \isacommand{finally}, Isabelle/Isar
  maintains separate context information of ``transitivity'' rules.
  Rule selection takes place automatically by higher-order
  unification. *}


subsection {* Groups as monoids *}

text {* Monoids over signature $({\times} :: \alpha \To \alpha \To
  \alpha, \idt{one} :: \alpha)$ are defined like this.
*}

class monoid = times + one +
  assumes monoid_assoc: "(x * y) * z = x * (y * z)"
    and monoid_left_one: "1 * x = x"
    and monoid_right_one: "x * 1 = x"

text {* Groups are \emph{not} yet monoids directly from the
  definition.  For monoids, \name{right-one} had to be included as an
  axiom, but for groups both \name{right-one} and \name{right-inverse}
  are derivable from the other axioms.  With \name{group-right-one}
  derived as a theorem of group theory (see
  page~\pageref{thm:group-right-one}), we may still instantiate
  $\idt{group} \subseteq \idt{monoid}$ properly as follows. *}

instance group < monoid
  by intro_classes
    (rule group_assoc,
      rule group_left_one,
      rule group_right_one)

text {* The \isacommand{instance} command actually is a version of
  \isacommand{theorem}, setting up a goal that reflects the intended
  class relation (or type constructor arity).  Thus any Isar proof
  language element may be involved to establish this statement.  When
  concluding the proof, the result is transformed into the intended
  type signature extension behind the scenes. *}


subsection {* More theorems of group theory *}

text {* The one element is already uniquely determined by preserving
  an \emph{arbitrary} group element. *}

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

text {* Likewise, the inverse is already determined by the cancel property. *}

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

text {* The inverse operation has some further characteristic properties. *}

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
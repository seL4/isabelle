(*  Title:      HOL/Isar_examples/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Basic group theory *}

theory Group = Main:

subsection {* Groups and calculational reasoning *} 

text {*
 Groups over signature $({\times} :: \alpha \To \alpha \To \alpha,
 \idt{one} :: \alpha, \idt{inverse} :: \alpha \To \alpha)$ are defined
 as an axiomatic type class as follows.  Note that the parent class
 $\idt{times}$ is provided by the basic HOL theory.
*}

consts
  one :: "'a"
  inverse :: "'a => 'a"

axclass
  group < times
  group_assoc:         "(x * y) * z = x * (y * z)"
  group_left_one:      "one * x = x"
  group_left_inverse:  "inverse x * x = one"

text {*
 The group axioms only state the properties of left one and inverse,
 the right versions may be derived as follows.
*}

theorem group_right_inverse: "x * inverse x = (one::'a::group)"
proof -
  have "x * inverse x = one * (x * inverse x)"
    by (simp only: group_left_one)
  also have "... = one * x * inverse x"
    by (simp only: group_assoc)
  also have "... = inverse (inverse x) * inverse x * x * inverse x"
    by (simp only: group_left_inverse)
  also have "... = inverse (inverse x) * (inverse x * x) * inverse x"
    by (simp only: group_assoc)
  also have "... = inverse (inverse x) * one * inverse x"
    by (simp only: group_left_inverse)
  also have "... = inverse (inverse x) * (one * inverse x)"
    by (simp only: group_assoc)
  also have "... = inverse (inverse x) * inverse x"
    by (simp only: group_left_one)
  also have "... = one"
    by (simp only: group_left_inverse)
  finally show ?thesis .
qed

text {*
 With \name{group-right-inverse} already available,
 \name{group-right-one}\label{thm:group-right-one} is now established
 much easier.
*}

theorem group_right_one: "x * one = (x::'a::group)"
proof -
  have "x * one = x * (inverse x * x)"
    by (simp only: group_left_inverse)
  also have "... = x * inverse x * x"
    by (simp only: group_assoc)
  also have "... = one * x"
    by (simp only: group_right_inverse)
  also have "... = x"
    by (simp only: group_left_one)
  finally show ?thesis .
qed

text {*
 \medskip The calculational proof style above follows typical
 presentations given in any introductory course on algebra.  The basic
 technique is to form a transitive chain of equations, which in turn
 are established by simplifying with appropriate rules.  The low-level
 logical details of equational reasoning are left implicit.

 Note that ``$\dots$'' is just a special term variable that is bound
 automatically to the argument\footnote{The argument of a curried
 infix expression happens to be its right-hand side.} of the last fact
 achieved by any local assumption or proven statement.  In contrast to
 $\var{thesis}$, the ``$\dots$'' variable is bound \emph{after} the
 proof is finished, though.

 There are only two separate Isar language elements for calculational
 proofs: ``\isakeyword{also}'' for initial or intermediate
 calculational steps, and ``\isakeyword{finally}'' for exhibiting the
 result of a calculation.  These constructs are not hardwired into
 Isabelle/Isar, but defined on top of the basic Isar/VM interpreter.
 Expanding the \isakeyword{also} and \isakeyword{finally} derived
 language elements, calculations may be simulated by hand as
 demonstrated below.
*}

theorem "x * one = (x::'a::group)"
proof -
  have "x * one = x * (inverse x * x)"
    by (simp only: group_left_inverse)

  note calculation = this
    -- {* first calculational step: init calculation register *}

  have "... = x * inverse x * x"
    by (simp only: group_assoc)

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *}

  have "... = one * x"
    by (simp only: group_right_inverse)

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *}

  have "... = x"
    by (simp only: group_left_one)

  note calculation = trans [OF calculation this]
    -- {* final calculational step: compose with transitivity rule ... *}
  from calculation
    -- {* ... and pick up the final result *}

  show ?thesis .
qed

text {*
 Note that this scheme of calculations is not restricted to plain
 transitivity.  Rules like anti-symmetry, or even forward and backward
 substitution work as well.  For the actual implementation of
 \isacommand{also} and \isacommand{finally}, Isabelle/Isar maintains
 separate context information of ``transitivity'' rules.  Rule
 selection takes place automatically by higher-order unification.
*}


subsection {* Groups as monoids *}

text {*
 Monoids over signature $({\times} :: \alpha \To \alpha \To \alpha,
 \idt{one} :: \alpha)$ are defined like this.
*}

axclass monoid < times
  monoid_assoc:       "(x * y) * z = x * (y * z)"
  monoid_left_one:   "one * x = x"
  monoid_right_one:  "x * one = x"

text {*
 Groups are \emph{not} yet monoids directly from the definition.  For
 monoids, \name{right-one} had to be included as an axiom, but for
 groups both \name{right-one} and \name{right-inverse} are derivable
 from the other axioms.  With \name{group-right-one} derived as a
 theorem of group theory (see page~\pageref{thm:group-right-one}), we
 may still instantiate $\idt{group} \subseteq \idt{monoid}$ properly
 as follows.
*}

instance group < monoid
  by (intro_classes,
       rule group_assoc,
       rule group_left_one,
       rule group_right_one)

text {*
 The \isacommand{instance} command actually is a version of
 \isacommand{theorem}, setting up a goal that reflects the intended
 class relation (or type constructor arity).  Thus any Isar proof
 language element may be involved to establish this statement.  When
 concluding the proof, the result is transformed into the intended
 type signature extension behind the scenes.
*}

subsection {* More theorems of group theory *}

text {*
 The one element is already uniquely determined by preserving an
 \emph{arbitrary} group element.
*}

theorem group_one_equality: "e * x = x ==> one = (e::'a::group)"
proof -
  assume eq: "e * x = x"
  have "one = x * inverse x"
    by (simp only: group_right_inverse)
  also have "... = (e * x) * inverse x"
    by (simp only: eq)
  also have "... = e * (x * inverse x)"
    by (simp only: group_assoc)
  also have "... = e * one"
    by (simp only: group_right_inverse)
  also have "... = e"
    by (simp only: group_right_one)
  finally show ?thesis .
qed

text {*
 Likewise, the inverse is already determined by the cancel property.
*}

theorem group_inverse_equality:
  "x' * x = one ==> inverse x = (x'::'a::group)"
proof -
  assume eq: "x' * x = one"
  have "inverse x = one * inverse x"
    by (simp only: group_left_one)
  also have "... = (x' * x) * inverse x"
    by (simp only: eq)
  also have "... = x' * (x * inverse x)"
    by (simp only: group_assoc)
  also have "... = x' * one"
    by (simp only: group_right_inverse)
  also have "... = x'"
    by (simp only: group_right_one)
  finally show ?thesis .
qed

text {*
 The inverse operation has some further characteristic properties.
*}

theorem group_inverse_times:
  "inverse (x * y) = inverse y * inverse (x::'a::group)"
proof (rule group_inverse_equality)
  show "(inverse y * inverse x) * (x * y) = one"
  proof -
    have "(inverse y * inverse x) * (x * y) =
        (inverse y * (inverse x * x)) * y"
      by (simp only: group_assoc)
    also have "... = (inverse y * one) * y"
      by (simp only: group_left_inverse)
    also have "... = inverse y * y"
      by (simp only: group_right_one)
    also have "... = one"
      by (simp only: group_left_inverse)
    finally show ?thesis .
  qed
qed

theorem inverse_inverse: "inverse (inverse x) = (x::'a::group)"
proof (rule group_inverse_equality)
  show "x * inverse x = one"
    by (simp only: group_right_inverse)
qed

theorem inverse_inject: "inverse x = inverse y ==> x = (y::'a::group)"
proof -
  assume eq: "inverse x = inverse y"
  have "x = x * one"
    by (simp only: group_right_one)
  also have "... = x * (inverse y * y)"
    by (simp only: group_left_inverse)
  also have "... = x * (inverse x * y)"
    by (simp only: eq)
  also have "... = (x * inverse x) * y"
    by (simp only: group_assoc)
  also have "... = one * y"
    by (simp only: group_right_inverse)
  also have "... = y"
    by (simp only: group_left_one)
  finally show ?thesis .
qed

end
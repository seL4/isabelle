(*  Title:      HOL/Isar_examples/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Basic group theory *};

theory Group = Main:;

subsection {* Groups and calculational reasoning *}; 

text {*
 Groups over signature $({\times} :: \alpha \To \alpha \To \alpha,
 \idt{one} :: \alpha, \idt{inv} :: \alpha \To \alpha)$ are defined as
 an axiomatic type class as follows.  Note that the parent class
 $\idt{times}$ is provided by the basic HOL theory.
*};

consts
  one :: "'a"
  inv :: "'a => 'a";

axclass
  group < times
  group_assoc:         "(x * y) * z = x * (y * z)"
  group_left_unit:     "one * x = x"
  group_left_inverse:  "inv x * x = one";

text {*
 The group axioms only state the properties of left unit and inverse,
 the right versions may be derived as follows.
*};

theorem group_right_inverse: "x * inv x = (one::'a::group)";
proof -;
  have "x * inv x = one * (x * inv x)";
    by (simp only: group_left_unit);
  also; have "... = one * x * inv x";
    by (simp only: group_assoc);
  also; have "... = inv (inv x) * inv x * x * inv x";
    by (simp only: group_left_inverse);
  also; have "... = inv (inv x) * (inv x * x) * inv x";
    by (simp only: group_assoc);
  also; have "... = inv (inv x) * one * inv x";
    by (simp only: group_left_inverse);
  also; have "... = inv (inv x) * (one * inv x)";
    by (simp only: group_assoc);
  also; have "... = inv (inv x) * inv x";
    by (simp only: group_left_unit);
  also; have "... = one";
    by (simp only: group_left_inverse);
  finally; show ?thesis; .;
qed;

text {*
 With \name{group-right-inverse} already available,
 \name{group-right-unit}\label{thm:group-right-unit} is now
 established much easier.
*};

theorem group_right_unit: "x * one = (x::'a::group)";
proof -;
  have "x * one = x * (inv x * x)";
    by (simp only: group_left_inverse);
  also; have "... = x * inv x * x";
    by (simp only: group_assoc);
  also; have "... = one * x";
    by (simp only: group_right_inverse);
  also; have "... = x";
    by (simp only: group_left_unit);
  finally; show ?thesis; .;
qed;

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
*};

theorem "x * one = (x::'a::group)";
proof -;
  have "x * one = x * (inv x * x)";
    by (simp only: group_left_inverse);

  note calculation = this
    -- {* first calculational step: init calculation register *};

  have "... = x * inv x * x";
    by (simp only: group_assoc);

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *};

  have "... = one * x";
    by (simp only: group_right_inverse);

  note calculation = trans [OF calculation this]
    -- {* general calculational step: compose with transitivity rule *};

  have "... = x";
    by (simp only: group_left_unit);

  note calculation = trans [OF calculation this]
    -- {* final calculational step: compose with transitivity rule ... *};
  from calculation
    -- {* ... and pick up the final result *};

  show ?thesis; .;
qed;

text {*
 Note that this scheme of calculations is not restricted to plain
 transitivity.  Rules like anti-symmetry, or even forward and backward
 substitution work as well.  For the actual implementation of
 \isacommand{also} and \isacommand{finally}, Isabelle/Isar maintains
 separate context information of ``transitivity'' rules.  Rule
 selection takes place automatically by higher-order unification.
*};


subsection {* Groups as monoids *};

text {*
 Monoids over signature $({\times} :: \alpha \To \alpha \To \alpha,
 \idt{one} :: \alpha)$ are defined like this.
*};

axclass monoid < times
  monoid_assoc:       "(x * y) * z = x * (y * z)"
  monoid_left_unit:   "one * x = x"
  monoid_right_unit:  "x * one = x";

text {*
 Groups are \emph{not} yet monoids directly from the definition.  For
 monoids, \name{right-unit} had to be included as an axiom, but for
 groups both \name{right-unit} and \name{right-inverse} are derivable
 from the other axioms.  With \name{group-right-unit} derived as a
 theorem of group theory (see page~\pageref{thm:group-right-unit}), we
 may still instantiate $\idt{group} \subset \idt{monoid}$ properly as
 follows.
*};

instance group < monoid;
  by (intro_classes,
       rule group_assoc,
       rule group_left_unit,
       rule group_right_unit);

text {*
 The \isacommand{instance} command actually is a version of
 \isacommand{theorem}, setting up a goal that reflects the intended
 class relation (or type constructor arity).  Thus any Isar proof
 language element may be involved to establish this statement.  When
 concluding the proof, the result is transformed into the intended
 type signature extension behind the scenes.
*};

end;

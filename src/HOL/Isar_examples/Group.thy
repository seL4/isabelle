(*  Title:      HOL/Isar_examples/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Group = Main:;

title {* Basic group theory -- demonstrating calculational proofs *};

section {* Groups *}; 

text {*
 We define an axiomatic type class of general groupes over signature
 (op *, one, inv).
*};

consts
  one :: "'a"
  inv :: "'a => 'a";

axclass
  group < times
  assoc:         "(x * y) * z = x * (y * z)"
  left_unit:     "one * x = x"
  left_inverse:  "inv x * x = one";

text {*
 The group axioms only state the properties of left unit and inverse, the
 right versions are derivable as follows.  The calculational proof style below
 closely follows a typical presentation given in any basic course on
 algebra.
*};

theorem right_inverse: "x * inv x = (one::'a::group)";
proof same;
  have "x * inv x = one * (x * inv x)";
    by (simp add: left_unit);
  also; have "... = (one * x) * inv x";
    by (simp add: assoc);
  also; have "... = inv (inv x) * inv x * x * inv x";
    by (simp add: left_inverse);
  also; have "... = inv (inv x) * (inv x * x) * inv x";
    by (simp add: assoc);
  also; have "... = inv (inv x) * one * inv x";
    by (simp add: left_inverse);
  also; have "... = inv (inv x) * (one * inv x)";
    by (simp add: assoc);
  also; have "... = inv (inv x) * inv x";
    by (simp add: left_unit);
  also; have "... = one";
    by (simp add: left_inverse);
  finally; show ??thesis; .;
qed;

text {*
  With right_inverse already at our disposel, right_unit is now
  obtained much simpler.
*};

theorem right_unit: "x * one = (x::'a::group)";
proof same;
  have "x * one = x * (inv x * x)";
    by (simp add: left_inverse);
  also; have "... = x * inv x * x";
    by (simp add: assoc);
  also; have "... = one * x";
    by (simp add: right_inverse);
  also; have "... = x";
    by (simp add: left_unit);
  finally; show ??thesis; .;
qed;

text {*
 There are only two language elements 'also' (for initial or
 intermediate calculational steps), and 'finally' (for picking up the
 result of a calculation).  These constructs are not hardwired into
 Isabelle/Isar, but defined on top of the basic Isar/VM interpreter.

 Without referring to 'also' or 'finally', calculations may be
 simulated as follows.  This can be also understood as an expansion of these
 two derived language elements.

 Also note that "..." is just a special term binding that happens to
 be bound automatically to the argument of the last fact established by
 assume or any local goal.  Unlike ??thesis, "..." is bound after the
 proof is finished.
*};

theorem right_unit': "x * one = (x::'a::group)";
proof same;

  have "x * one = x * (inv x * x)";
    by (simp add: left_inverse);

  note calculation = facts
    -- {* first calculational step: init register *};

  have "... = x * inv x * x";
    by (simp add: assoc);

  note calculation = trans[APP calculation facts]
    -- {* general calculational step: compose with transitivity rule *};

  have "... = one * x";
    by (simp add: right_inverse);

  note calculation = trans[APP calculation facts]
    -- {* general calculational step: compose with transitivity rule *};

  have "... = x";
    by (simp add: left_unit);

  note calculation = trans[APP calculation facts]
    -- {* final calculational step: compose with transitivity rule ... *};
  from calculation
    -- {* ... and pick up final result *};

  show ??thesis; .;

qed;


end;

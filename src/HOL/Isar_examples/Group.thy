(*  Title:      HOL/Isar_examples/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some bits of group theory.  Demonstrate calculational proofs.
*)

theory Group = Main:;


subsection {* axiomatic type class of groups over signature (*, inv, one) *};

consts
  inv :: "'a => 'a"
  one :: "'a";

axclass
  group < times
  assoc:         "(x * y) * z = x * (y * z)"
  left_unit:     "one * x = x"
  left_inverse:  "inverse x * x = one";


subsection {* some basic theorems of group theory *};

text {* We simulate *};

theorem right_inverse: "x * inverse x = (one::'a::group)";
proof same;
  have "x * inverse x = one * (x * inverse x)";
    by (simp add: left_unit);

  note calculation = facts;
  let "_ = ..." = ??facts;

  have "... = (one * x) * inverse x";
    by (simp add: assoc);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = inverse (inverse x) * inverse x * x * inverse x";
    by (simp add: left_inverse);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = inverse (inverse x) * (inverse x * x) * inverse x";
    by (simp add: assoc);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = inverse (inverse x) * one * inverse x";
    by (simp add: left_inverse);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = inverse (inverse x) * (one * inverse x)";
    by (simp add: assoc);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = inverse (inverse x) * inverse x";
    by (simp add: left_unit);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = one";
    by (simp add: left_inverse);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;
  from calculation;

  show ??thesis; .;
qed;


theorem right_inverse: "x * one = (x::'a::group)";
proof same;

  have "x * one = x * (inverse x * x)";
    by (simp add: left_inverse);

  note calculation = facts;
  let "_ = ..." = ??facts;

  have "... = x * inverse x * x";
    by (simp add: assoc);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = one * x";
    by (simp add: right_inverse);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;

  have "... = x";
    by (simp add: left_unit);

  note calculation = trans[APP calculation facts];
  let "_ = ..." = ??facts;
  from calculation;

  show ??thesis; .;
qed;


end;

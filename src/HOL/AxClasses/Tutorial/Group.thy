(*  Title:      HOL/AxClasses/Tutorial/Group.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Group = Main:;

subsection {* Monoids and Groups *};

consts
  times :: "'a => 'a => 'a"    (infixl "[*]" 70)
  inverse :: "'a => 'a"
  one :: 'a;


axclass
  monoid < "term"
  assoc:      "(x [*] y) [*] z = x [*] (y [*] z)"
  left_unit:  "one [*] x = x"
  right_unit: "x [*] one = x";


axclass
  semigroup < "term"
  assoc: "(x [*] y) [*] z = x [*] (y [*] z)";

axclass
  group < semigroup
  left_unit:    "one [*] x = x"
  left_inverse: "inverse x [*] x = one";

axclass
  agroup < group
  commute: "x [*] y = y [*] x";


subsection {* Abstract reasoning *};

theorem group_right_inverse: "x [*] inverse x = (one::'a::group)";
proof -;
  have "x [*] inverse x = one [*] (x [*] inverse x)";
    by (simp only: group.left_unit);
  also; have "... = one [*] x [*] inverse x";
    by (simp only: semigroup.assoc);
  also; have "... = inverse (inverse x) [*] inverse x [*] x [*] inverse x";
    by (simp only: group.left_inverse);
  also; have "... = inverse (inverse x) [*] (inverse x [*] x) [*] inverse x";
    by (simp only: semigroup.assoc);
  also; have "... = inverse (inverse x) [*] one [*] inverse x";
    by (simp only: group.left_inverse);
  also; have "... = inverse (inverse x) [*] (one [*] inverse x)";
    by (simp only: semigroup.assoc);
  also; have "... = inverse (inverse x) [*] inverse x";
    by (simp only: group.left_unit);
  also; have "... = one";
    by (simp only: group.left_inverse);
  finally; show ?thesis; .;
qed;

theorem group_right_unit: "x [*] one = (x::'a::group)";
proof -;
  have "x [*] one = x [*] (inverse x [*] x)";
    by (simp only: group.left_inverse);
  also; have "... = x [*] inverse x [*] x";
    by (simp only: semigroup.assoc);
  also; have "... = one [*] x";
    by (simp only: group_right_inverse);
  also; have "... = x";
    by (simp only: group.left_unit);
  finally; show ?thesis; .;
qed;


subsection {* Abstract instantiation *};

instance monoid < semigroup;
proof intro_classes;
  fix x y z :: "'a::monoid";
  show "x [*] y [*] z = x [*] (y [*] z)";
    by (rule monoid.assoc);
qed;

instance group < monoid;
proof intro_classes;
  fix x y z :: "'a::group";
  show "x [*] y [*] z = x [*] (y [*] z)";
    by (rule semigroup.assoc);
  show "one [*] x = x";
    by (rule group.left_unit);
  show "x [*] one = x";
    by (rule group_right_unit);
qed;


subsection {* Concrete instantiation \label{sec:inst-arity} *};

defs
  times_bool_def:   "x [*] y == x ~= (y::bool)"
  inverse_bool_def: "inverse x == x::bool"
  unit_bool_def:    "one == False";

instance bool :: agroup;
proof (intro_classes,
    unfold times_bool_def inverse_bool_def unit_bool_def);
  fix x y z;
  show "((x ~= y) ~= z) = (x ~= (y ~= z))"; by blast;
  show "(False ~= x) = x"; by blast;
  show "(x ~= x) = False"; by blast;
  show "(x ~= y) = (y ~= x)"; by blast;
qed;


subsection {* Lifting and Functors *};

defs
  times_prod_def: "p [*] q == (fst p [*] fst q, snd p [*] snd q)";

instance * :: (semigroup, semigroup) semigroup;
proof (intro_classes, unfold times_prod_def);
  fix p q r :: "'a::semigroup * 'b::semigroup";
  show
    "(fst (fst p [*] fst q, snd p [*] snd q) [*] fst r,
      snd (fst p [*] fst q, snd p [*] snd q) [*] snd r) =
       (fst p [*] fst (fst q [*] fst r, snd q [*] snd r),
        snd p [*] snd (fst q [*] fst r, snd q [*] snd r))";
    by (simp add: semigroup.assoc);
qed;

end;

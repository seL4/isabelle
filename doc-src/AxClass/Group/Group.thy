
theory Group = Main:;


consts
  times :: "'a => 'a => 'a"    (infixl "\<Otimes>" 70)
  inverse :: "'a => 'a"        ("(_\<inv>)" [1000] 999)
  one :: 'a                    ("\<unit>");


axclass
  monoid < "term"
  assoc:      "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)"
  left_unit:  "\<unit> \<Otimes> x = x"
  right_unit: "x \<Otimes> \<unit> = x";


axclass
  semigroup < "term"
  assoc: "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)";

axclass
  group < semigroup
  left_unit:    "\<unit> \<Otimes> x = x"
  left_inverse: "inverse x \<Otimes> x = \<unit>";


text {*
 The group axioms only state the properties of left unit and inverse,
 the right versions may be derived as follows.
*};

theorem group_right_inverse: "x \<Otimes> x\<inv> = (\<unit>::'a::group)";
proof -;
  have "x \<Otimes> x\<inv> = \<unit> \<Otimes> (x \<Otimes> x\<inv>)";
    by (simp only: group.left_unit);
  also; have "... = (\<unit> \<Otimes> x) \<Otimes> x\<inv>";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> x\<inv> \<Otimes> x \<Otimes> x\<inv>";
    by (simp only: group.left_inverse);
  also; have "... = (x\<inv>)\<inv> \<Otimes> (x\<inv> \<Otimes> x) \<Otimes> x\<inv>";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> \<unit> \<Otimes> x\<inv>";
    by (simp only: group.left_inverse);
  also; have "... = (x\<inv>)\<inv> \<Otimes> (\<unit> \<Otimes> x\<inv>)";
    by (simp only: semigroup.assoc);
  also; have "... = (x\<inv>)\<inv> \<Otimes> x\<inv>";
    by (simp only: group.left_unit);
  also; have "... = \<unit>";
    by (simp only: group.left_inverse);
  finally; show ?thesis; .;
qed;

text {*
 With $group_right_inverse$ already available,
 $group_right_unit$\label{thm:group-right-unit} is now established
 much easier.
*};

theorem group_right_unit: "x \<Otimes> \<unit> = (x::'a::group)";
proof -;
  have "x \<Otimes> \<unit> = x \<Otimes> (x\<inv> \<Otimes> x)";
    by (simp only: group.left_inverse);
  also; have "... = x \<Otimes> x\<inv> \<Otimes> x";
    by (simp only: semigroup.assoc);
  also; have "... = \<unit> \<Otimes> x";
    by (simp only: group_right_inverse);
  also; have "... = x";
    by (simp only: group.left_unit);
  finally; show ?thesis; .;
qed;


axclass
  agroup < group
  commute: "x \<Otimes> y = y \<Otimes> x";



instance monoid < semigroup;
proof intro_classes;
  fix x y z :: "'a::monoid";
  show "x \<Otimes> y \<Otimes> z = x \<Otimes> (y \<Otimes> z)";
    by (rule monoid.assoc);
qed;


instance group < monoid;
proof intro_classes;
  fix x y z :: "'a::group";
  show "x \<Otimes> y \<Otimes> z = x \<Otimes> (y \<Otimes> z)";
    by (rule semigroup.assoc);
  show "\<unit> \<Otimes> x = x";
    by (rule group.left_unit);
  show "x \<Otimes> \<unit> = x";
    by (rule group_right_unit);
qed;



defs
  times_bool_def:   "x \<Otimes> y \\<equiv> x \\<noteq> (y\\<Colon>bool)"
  inverse_bool_def: "x\<inv> \\<equiv> x\\<Colon>bool"
  unit_bool_def:    "\<unit> \\<equiv> False";

instance bool :: agroup;
proof (intro_classes,
    unfold times_bool_def inverse_bool_def unit_bool_def);
  fix x y z :: bool;
  show "((x \\<noteq> y) \\<noteq> z) = (x \\<noteq> (y \\<noteq> z))"; by blast;
  show "(False \\<noteq> x) = x"; by blast;
  show "(x \\<noteq> x) = False"; by blast;
  show "(x \\<noteq> y) = (y \\<noteq> x)"; by blast;
qed;


defs
  prod_prod_def: "p \<Otimes> q \\<equiv> (fst p \<Otimes> fst q, snd p \<Otimes> snd q)";

instance * :: (semigroup, semigroup) semigroup;
proof (intro_classes, unfold prod_prod_def);
  fix p q r :: "'a::semigroup * 'b::semigroup";
  show
    "(fst (fst p \<Otimes> fst q, snd p \<Otimes> snd q) \<Otimes> fst r,
      snd (fst p \<Otimes> fst q, snd p \<Otimes> snd q) \<Otimes> snd r) =
       (fst p \<Otimes> fst (fst q \<Otimes> fst r, snd q \<Otimes> snd r),
        snd p \<Otimes> snd (fst q \<Otimes> fst r, snd q \<Otimes> snd r))";
    by (simp add: semigroup.assoc);
qed;

end;
(*  Title       : HOL/Hyperreal/StarClasses.thy
    ID          : $Id$
    Author      : Brian Huffman
*)

header {* Class Instances *}

theory StarClasses
imports Transfer
begin

subsection {* Syntactic classes *}

instance star :: (ord) ord ..
instance star :: (zero) zero ..
instance star :: (one) one ..
instance star :: (plus) plus ..
instance star :: (times) times ..
instance star :: (minus) minus ..
instance star :: (inverse) inverse ..
instance star :: (number) number ..
instance star :: ("Divides.div") "Divides.div" ..
instance star :: (power) power ..

defs (overloaded)
  star_zero_def:    "0 \<equiv> star_of 0"
  star_one_def:     "1 \<equiv> star_of 1"
  star_number_def:  "number_of b \<equiv> star_of (number_of b)"
  star_add_def:     "(op +) \<equiv> Ifun2_of (op +)"
  star_diff_def:    "(op -) \<equiv> Ifun2_of (op -)"
  star_minus_def:   "uminus \<equiv> Ifun_of uminus"
  star_mult_def:    "(op *) \<equiv> Ifun2_of (op *)"
  star_divide_def:  "(op /) \<equiv> Ifun2_of (op /)"
  star_inverse_def: "inverse \<equiv> Ifun_of inverse"
  star_le_def:      "(op \<le>) \<equiv> Ipred2_of (op \<le>)"
  star_less_def:    "(op <) \<equiv> Ipred2_of (op <)"
  star_abs_def:     "abs \<equiv> Ifun_of abs"
  star_div_def:     "(op div) \<equiv> Ifun2_of (op div)"
  star_mod_def:     "(op mod) \<equiv> Ifun2_of (op mod)"
  star_power_def:   "(op ^) \<equiv> \<lambda>x n. Ifun_of (\<lambda>x. x ^ n) x"

lemmas star_class_defs [transfer_unfold] =
  star_zero_def     star_one_def      star_number_def
  star_add_def      star_diff_def     star_minus_def
  star_mult_def     star_divide_def   star_inverse_def
  star_le_def       star_less_def     star_abs_def
  star_div_def      star_mod_def      star_power_def

text {* @{term star_of} preserves class operations *}

lemma star_of_add: "star_of (x + y) = star_of x + star_of y"
by transfer (rule refl)

lemma star_of_diff: "star_of (x - y) = star_of x - star_of y"
by transfer (rule refl)

lemma star_of_minus: "star_of (-x) = - star_of x"
by transfer (rule refl)

lemma star_of_mult: "star_of (x * y) = star_of x * star_of y"
by transfer (rule refl)

lemma star_of_divide: "star_of (x / y) = star_of x / star_of y"
by transfer (rule refl)

lemma star_of_inverse: "star_of (inverse x) = inverse (star_of x)"
by transfer (rule refl)

lemma star_of_div: "star_of (x div y) = star_of x div star_of y"
by transfer (rule refl)

lemma star_of_mod: "star_of (x mod y) = star_of x mod star_of y"
by transfer (rule refl)

lemma star_of_power: "star_of (x ^ n) = star_of x ^ n"
by transfer (rule refl)

lemma star_of_abs: "star_of (abs x) = abs (star_of x)"
by transfer (rule refl)

text {* @{term star_of} preserves numerals *}

lemma star_of_zero: "star_of 0 = 0"
by transfer (rule refl)

lemma star_of_one: "star_of 1 = 1"
by transfer (rule refl)

lemma star_of_number_of: "star_of (number_of x) = number_of x"
by transfer (rule refl)

text {* @{term star_of} preserves orderings *}

lemma star_of_less: "(star_of x < star_of y) = (x < y)"
by transfer (rule refl)

lemma star_of_le: "(star_of x \<le> star_of y) = (x \<le> y)"
by transfer (rule refl)

lemma star_of_eq: "(star_of x = star_of y) = (x = y)"
by transfer (rule refl)

text{*As above, for 0*}

lemmas star_of_0_less = star_of_less [of 0, simplified star_of_zero]
lemmas star_of_0_le   = star_of_le   [of 0, simplified star_of_zero]
lemmas star_of_0_eq   = star_of_eq   [of 0, simplified star_of_zero]

lemmas star_of_less_0 = star_of_less [of _ 0, simplified star_of_zero]
lemmas star_of_le_0   = star_of_le   [of _ 0, simplified star_of_zero]
lemmas star_of_eq_0   = star_of_eq   [of _ 0, simplified star_of_zero]

text{*As above, for 1*}

lemmas star_of_1_less = star_of_less [of 1, simplified star_of_one]
lemmas star_of_1_le   = star_of_le   [of 1, simplified star_of_one]
lemmas star_of_1_eq   = star_of_eq   [of 1, simplified star_of_one]

lemmas star_of_less_1 = star_of_less [of _ 1, simplified star_of_one]
lemmas star_of_le_1   = star_of_le   [of _ 1, simplified star_of_one]
lemmas star_of_eq_1   = star_of_eq   [of _ 1, simplified star_of_one]

text{*As above, for numerals*}

lemmas star_of_number_less =
  star_of_less [of "number_of w", standard, simplified star_of_number_of]
lemmas star_of_number_le   =
  star_of_le   [of "number_of w", standard, simplified star_of_number_of]
lemmas star_of_number_eq   =
  star_of_eq   [of "number_of w", standard, simplified star_of_number_of]

lemmas star_of_less_number =
  star_of_less [of _ "number_of w", standard, simplified star_of_number_of]
lemmas star_of_le_number   =
  star_of_le   [of _ "number_of w", standard, simplified star_of_number_of]
lemmas star_of_eq_number   =
  star_of_eq   [of _ "number_of w", standard, simplified star_of_number_of]

lemmas star_of_simps [simp] =
  star_of_add     star_of_diff    star_of_minus
  star_of_mult    star_of_divide  star_of_inverse
  star_of_div     star_of_mod
  star_of_power   star_of_abs
  star_of_zero    star_of_one     star_of_number_of
  star_of_less    star_of_le      star_of_eq
  star_of_0_less  star_of_0_le    star_of_0_eq
  star_of_less_0  star_of_le_0    star_of_eq_0
  star_of_1_less  star_of_1_le    star_of_1_eq
  star_of_less_1  star_of_le_1    star_of_eq_1
  star_of_number_less star_of_number_le star_of_number_eq
  star_of_less_number star_of_le_number star_of_eq_number

subsection {* Ordering classes *}

instance star :: (order) order
apply (intro_classes)
apply (transfer, rule order_refl)
apply (transfer, erule (1) order_trans)
apply (transfer, erule (1) order_antisym)
apply (transfer, rule order_less_le)
done

instance star :: (linorder) linorder
by (intro_classes, transfer, rule linorder_linear)


subsection {* Lattice ordering classes *}

text {*
  Some extra trouble is necessary because the class axioms 
  for @{term meet} and @{term join} use quantification over
  function spaces.
*}

lemma ex_star_fun:
  "\<exists>f::('a \<Rightarrow> 'b) star. P (Ifun f)
   \<Longrightarrow> \<exists>f::'a star \<Rightarrow> 'b star. P f"
by (erule exE, erule exI)

lemma ex_star_fun2:
  "\<exists>f::('a \<Rightarrow> 'b \<Rightarrow> 'c) star. P (Ifun2 f)
   \<Longrightarrow> \<exists>f::'a star \<Rightarrow> 'b star \<Rightarrow> 'c star. P f"
by (erule exE, erule exI)

instance star :: (join_semilorder) join_semilorder
apply (intro_classes)
apply (rule ex_star_fun2)
apply (transfer is_join_def)
apply (rule join_exists)
done

instance star :: (meet_semilorder) meet_semilorder
apply (intro_classes)
apply (rule ex_star_fun2)
apply (transfer is_meet_def)
apply (rule meet_exists)
done

instance star :: (lorder) lorder ..

lemma star_join_def [transfer_unfold]: "join \<equiv> Ifun2_of join"
 apply (rule is_join_unique[OF is_join_join, THEN eq_reflection])
 apply (transfer is_join_def, rule is_join_join)
done

lemma star_meet_def [transfer_unfold]: "meet \<equiv> Ifun2_of meet"
 apply (rule is_meet_unique[OF is_meet_meet, THEN eq_reflection])
 apply (transfer is_meet_def, rule is_meet_meet)
done

subsection {* Ordered group classes *}

instance star :: (semigroup_add) semigroup_add
by (intro_classes, transfer, rule add_assoc)

instance star :: (ab_semigroup_add) ab_semigroup_add
by (intro_classes, transfer, rule add_commute)

instance star :: (semigroup_mult) semigroup_mult
by (intro_classes, transfer, rule mult_assoc)

instance star :: (ab_semigroup_mult) ab_semigroup_mult
by (intro_classes, transfer, rule mult_commute)

instance star :: (comm_monoid_add) comm_monoid_add
by (intro_classes, transfer, rule comm_monoid_add_class.add_0)

instance star :: (monoid_mult) monoid_mult
apply (intro_classes)
apply (transfer, rule mult_1_left)
apply (transfer, rule mult_1_right)
done

instance star :: (comm_monoid_mult) comm_monoid_mult
by (intro_classes, transfer, rule mult_1)

instance star :: (cancel_semigroup_add) cancel_semigroup_add
apply (intro_classes)
apply (transfer, erule add_left_imp_eq)
apply (transfer, erule add_right_imp_eq)
done

instance star :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
by (intro_classes, transfer, rule add_imp_eq)

instance star :: (ab_group_add) ab_group_add
apply (intro_classes)
apply (transfer, rule left_minus)
apply (transfer, rule diff_minus)
done

instance star :: (pordered_ab_semigroup_add) pordered_ab_semigroup_add
by (intro_classes, transfer, rule add_left_mono)

instance star :: (pordered_cancel_ab_semigroup_add) pordered_cancel_ab_semigroup_add ..

instance star :: (pordered_ab_semigroup_add_imp_le) pordered_ab_semigroup_add_imp_le
by (intro_classes, transfer, rule add_le_imp_le_left)

instance star :: (pordered_ab_group_add) pordered_ab_group_add ..
instance star :: (ordered_cancel_ab_semigroup_add) ordered_cancel_ab_semigroup_add ..
instance star :: (lordered_ab_group_meet) lordered_ab_group_meet ..
instance star :: (lordered_ab_group_meet) lordered_ab_group_meet ..
instance star :: (lordered_ab_group) lordered_ab_group ..

instance star :: (lordered_ab_group_abs) lordered_ab_group_abs
by (intro_classes, transfer, rule abs_lattice)

text "Ring-and-Field.thy"

instance star :: (semiring) semiring
apply (intro_classes)
apply (transfer, rule left_distrib)
apply (transfer, rule right_distrib)
done

instance star :: (semiring_0) semiring_0 ..
instance star :: (semiring_0_cancel) semiring_0_cancel ..

instance star :: (comm_semiring) comm_semiring
by (intro_classes, transfer, rule distrib)

instance star :: (comm_semiring_0) comm_semiring_0 ..
instance star :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance star :: (axclass_0_neq_1) axclass_0_neq_1
by (intro_classes, transfer, rule zero_neq_one)

instance star :: (semiring_1) semiring_1 ..
instance star :: (comm_semiring_1) comm_semiring_1 ..

instance star :: (axclass_no_zero_divisors) axclass_no_zero_divisors
by (intro_classes, transfer, rule no_zero_divisors)

instance star :: (semiring_1_cancel) semiring_1_cancel ..
instance star :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..
instance star :: (ring) ring ..
instance star :: (comm_ring) comm_ring ..
instance star :: (ring_1) ring_1 ..
instance star :: (comm_ring_1) comm_ring_1 ..
instance star :: (idom) idom .. 

instance star :: (field) field
apply (intro_classes)
apply (transfer, erule left_inverse)
apply (transfer, rule divide_inverse)
done

instance star :: (division_by_zero) division_by_zero
by (intro_classes, transfer, rule inverse_zero)

instance star :: (pordered_semiring) pordered_semiring
apply (intro_classes)
apply (transfer, erule (1) mult_left_mono)
apply (transfer, erule (1) mult_right_mono)
done

instance star :: (pordered_cancel_semiring) pordered_cancel_semiring ..

instance star :: (ordered_semiring_strict) ordered_semiring_strict
apply (intro_classes)
apply (transfer, erule (1) mult_strict_left_mono)
apply (transfer, erule (1) mult_strict_right_mono)
done

instance star :: (pordered_comm_semiring) pordered_comm_semiring
by (intro_classes, transfer, rule pordered_comm_semiring_class.mult_mono)

instance star :: (pordered_cancel_comm_semiring) pordered_cancel_comm_semiring ..

instance star :: (ordered_comm_semiring_strict) ordered_comm_semiring_strict
by (intro_classes, transfer, rule ordered_comm_semiring_strict_class.mult_strict_mono)

instance star :: (pordered_ring) pordered_ring ..
instance star :: (lordered_ring) lordered_ring ..

instance star :: (axclass_abs_if) axclass_abs_if
by (intro_classes, transfer, rule abs_if)

instance star :: (ordered_ring_strict) ordered_ring_strict ..
instance star :: (pordered_comm_ring) pordered_comm_ring ..

instance star :: (ordered_semidom) ordered_semidom
by (intro_classes, transfer, rule zero_less_one)

instance star :: (ordered_idom) ordered_idom ..
instance star :: (ordered_field) ordered_field ..

subsection {* Power classes *}

text {*
  Proving the class axiom @{thm [source] power_Suc} for type
  @{typ "'a star"} is a little tricky, because it quantifies
  over values of type @{typ nat}. The transfer principle does
  not handle quantification over non-star types in general,
  but we can work around this by fixing an arbitrary @{typ nat}
  value, and then applying the transfer principle.
*}

instance star :: (recpower) recpower
proof
  show "\<And>a::'a star. a ^ 0 = 1"
    by transfer (rule power_0)
next
  fix n show "\<And>a::'a star. a ^ Suc n = a * a ^ n"
    by transfer (rule power_Suc)
qed

subsection {* Number classes *}

lemma star_of_nat_def [transfer_unfold]: "of_nat n \<equiv> star_of (of_nat n)"
by (rule eq_reflection, induct_tac n, simp_all)

lemma star_of_of_nat [simp]: "star_of (of_nat n) = of_nat n"
by transfer (rule refl)

lemma int_diff_cases:
assumes prem: "\<And>m n. z = int m - int n \<Longrightarrow> P" shows "P"
 apply (rule_tac z=z in int_cases)
  apply (rule_tac m=n and n=0 in prem, simp)
 apply (rule_tac m=0 and n="Suc n" in prem, simp)
done -- "Belongs in Integ/IntDef.thy"

lemma star_of_int_def [transfer_unfold]: "of_int z \<equiv> star_of (of_int z)"
by (rule eq_reflection, rule_tac z=z in int_diff_cases, simp)

lemma star_of_of_int [simp]: "star_of (of_int z) = of_int z"
by transfer (rule refl)

instance star :: (number_ring) number_ring
by (intro_classes, simp only: star_number_def star_of_int_def number_of_eq)

end

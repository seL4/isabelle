(*  Title       : HOL/Hyperreal/StarClasses.thy
    ID          : $Id$
    Author      : Brian Huffman
*)

header {* Class Instances *}

theory StarClasses
imports StarDef
begin

subsection {* Syntactic classes *}

instance star :: (zero) zero
  star_zero_def:    "0 \<equiv> star_of 0" ..

instance star :: (one) one
  star_one_def:     "1 \<equiv> star_of 1" ..

instance star :: (plus) plus
  star_add_def:     "(op +) \<equiv> *f2* (op +)" ..

instance star :: (times) times
  star_mult_def:    "(op *) \<equiv> *f2* (op *)" ..

instance star :: (minus) minus
  star_minus_def:   "uminus \<equiv> *f* uminus"
  star_diff_def:    "(op -) \<equiv> *f2* (op -)"
  star_abs_def:     "abs \<equiv> *f* abs" ..

instance star :: (inverse) inverse
  star_divide_def:  "(op /) \<equiv> *f2* (op /)"
  star_inverse_def: "inverse \<equiv> *f* inverse" ..

instance star :: (number) number
  star_number_def:  "number_of b \<equiv> star_of (number_of b)" ..

instance star :: (Divides.div) Divides.div
  star_div_def:     "(op div) \<equiv> *f2* (op div)"
  star_mod_def:     "(op mod) \<equiv> *f2* (op mod)" ..

instance star :: (power) power
  star_power_def:   "(op ^) \<equiv> \<lambda>x n. ( *f* (\<lambda>x. x ^ n)) x" ..

instance star :: (ord) ord
  star_le_def:      "(op \<le>) \<equiv> *p2* (op \<le>)"
  star_less_def:    "(op <) \<equiv> *p2* (op <)" ..

lemmas star_class_defs [transfer_unfold] =
  star_zero_def     star_one_def      star_number_def
  star_add_def      star_diff_def     star_minus_def
  star_mult_def     star_divide_def   star_inverse_def
  star_le_def       star_less_def     star_abs_def
  star_div_def      star_mod_def      star_power_def

text {* Class operations preserve standard elements *}

lemma Standard_zero: "0 \<in> Standard"
by (simp add: star_zero_def)

lemma Standard_one: "1 \<in> Standard"
by (simp add: star_one_def)

lemma Standard_number_of: "number_of b \<in> Standard"
by (simp add: star_number_def)

lemma Standard_add: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x + y \<in> Standard"
by (simp add: star_add_def)

lemma Standard_diff: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x - y \<in> Standard"
by (simp add: star_diff_def)

lemma Standard_minus: "x \<in> Standard \<Longrightarrow> - x \<in> Standard"
by (simp add: star_minus_def)

lemma Standard_mult: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x * y \<in> Standard"
by (simp add: star_mult_def)

lemma Standard_divide: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x / y \<in> Standard"
by (simp add: star_divide_def)

lemma Standard_inverse: "x \<in> Standard \<Longrightarrow> inverse x \<in> Standard"
by (simp add: star_inverse_def)

lemma Standard_abs: "x \<in> Standard \<Longrightarrow> abs x \<in> Standard"
by (simp add: star_abs_def)

lemma Standard_div: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x div y \<in> Standard"
by (simp add: star_div_def)

lemma Standard_mod: "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> x mod y \<in> Standard"
by (simp add: star_mod_def)

lemma Standard_power: "x \<in> Standard \<Longrightarrow> x ^ n \<in> Standard"
by (simp add: star_power_def)

lemmas Standard_simps [simp] =
  Standard_zero  Standard_one  Standard_number_of
  Standard_add  Standard_diff  Standard_minus
  Standard_mult  Standard_divide  Standard_inverse
  Standard_abs  Standard_div  Standard_mod
  Standard_power

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

subsection {* Ordering and lattice classes *}

instance star :: (order) order
apply (intro_classes)
apply (transfer, rule order_less_le)
apply (transfer, rule order_refl)
apply (transfer, erule (1) order_trans)
apply (transfer, erule (1) order_antisym)
done

instance star :: (lower_semilattice) lower_semilattice
  star_inf_def [transfer_unfold]: "inf \<equiv> *f2* inf"
  by default (transfer star_inf_def, auto)+

instance star :: (upper_semilattice) upper_semilattice
  star_sup_def [transfer_unfold]: "sup \<equiv> *f2* sup"
  by default (transfer star_sup_def, auto)+

instance star :: (lattice) lattice ..

instance star :: (distrib_lattice) distrib_lattice
  by default (transfer, auto simp add: sup_inf_distrib1)

lemma Standard_inf [simp]:
  "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> inf x y \<in> Standard"
by (simp add: star_inf_def)

lemma Standard_sup [simp]:
  "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> sup x y \<in> Standard"
by (simp add: star_sup_def)

lemma star_of_inf [simp]: "star_of (inf x y) = inf (star_of x) (star_of y)"
by transfer (rule refl)

lemma star_of_sup [simp]: "star_of (sup x y) = sup (star_of x) (star_of y)"
by transfer (rule refl)

instance star :: (linorder) linorder
by (intro_classes, transfer, rule linorder_linear)

lemma star_max_def [transfer_unfold]: "max = *f2* max"
apply (rule ext, rule ext)
apply (unfold max_def, transfer, fold max_def)
apply (rule refl)
done

lemma star_min_def [transfer_unfold]: "min = *f2* min"
apply (rule ext, rule ext)
apply (unfold min_def, transfer, fold min_def)
apply (rule refl)
done

lemma Standard_max [simp]:
  "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> max x y \<in> Standard"
by (simp add: star_max_def)

lemma Standard_min [simp]:
  "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> min x y \<in> Standard"
by (simp add: star_min_def)

lemma star_of_max [simp]: "star_of (max x y) = max (star_of x) (star_of y)"
by transfer (rule refl)

lemma star_of_min [simp]: "star_of (min x y) = min (star_of x) (star_of y)"
by transfer (rule refl)


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
by (intro_classes, transfer, rule comm_monoid_add_class.zero_plus.add_0)

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

subsection {* Ring and field classes *}

instance star :: (semiring) semiring
apply (intro_classes)
apply (transfer, rule left_distrib)
apply (transfer, rule right_distrib)
done

instance star :: (semiring_0) semiring_0 
by intro_classes (transfer, simp)+

instance star :: (semiring_0_cancel) semiring_0_cancel ..

instance star :: (comm_semiring) comm_semiring
by (intro_classes, transfer, rule distrib)

instance star :: (comm_semiring_0) comm_semiring_0 ..
instance star :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance star :: (zero_neq_one) zero_neq_one
by (intro_classes, transfer, rule zero_neq_one)

instance star :: (semiring_1) semiring_1 ..
instance star :: (comm_semiring_1) comm_semiring_1 ..

instance star :: (no_zero_divisors) no_zero_divisors
by (intro_classes, transfer, rule no_zero_divisors)

instance star :: (semiring_1_cancel) semiring_1_cancel ..
instance star :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..
instance star :: (ring) ring ..
instance star :: (comm_ring) comm_ring ..
instance star :: (ring_1) ring_1 ..
instance star :: (comm_ring_1) comm_ring_1 ..
instance star :: (ring_no_zero_divisors) ring_no_zero_divisors ..
instance star :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..
instance star :: (idom) idom .. 

instance star :: (division_ring) division_ring
apply (intro_classes)
apply (transfer, erule left_inverse)
apply (transfer, erule right_inverse)
done

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
by (intro_classes, transfer, rule mult_mono1_class.times_zero_less_eq_less.mult_mono)

instance star :: (pordered_cancel_comm_semiring) pordered_cancel_comm_semiring ..

instance star :: (ordered_comm_semiring_strict) ordered_comm_semiring_strict
by (intro_classes, transfer, rule ordered_comm_semiring_strict_class.plus_less_eq_less_zero_times.mult_strict_mono)

instance star :: (pordered_ring) pordered_ring ..
instance star :: (lordered_ring) lordered_ring ..

instance star :: (abs_if) abs_if
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

lemma star_of_nat_def [transfer_unfold]: "of_nat n = star_of (of_nat n)"
by (induct_tac n, simp_all)

lemma Standard_of_nat [simp]: "of_nat n \<in> Standard"
by (simp add: star_of_nat_def)

lemma star_of_of_nat [simp]: "star_of (of_nat n) = of_nat n"
by transfer (rule refl)

lemma star_of_int_def [transfer_unfold]: "of_int z = star_of (of_int z)"
by (rule_tac z=z in int_diff_cases, simp)

lemma Standard_of_int [simp]: "of_int z \<in> Standard"
by (simp add: star_of_int_def)

lemma star_of_of_int [simp]: "star_of (of_int z) = of_int z"
by transfer (rule refl)

instance star :: (semiring_char_0) semiring_char_0
by (intro_classes, simp only: star_of_nat_def star_of_eq of_nat_eq_iff)

instance star :: (ring_char_0) ring_char_0 ..

instance star :: (number_ring) number_ring
by (intro_classes, simp only: star_number_def star_of_int_def number_of_eq)

subsection {* Finite class *}

lemma starset_finite: "finite A \<Longrightarrow> *s* A = star_of ` A"
by (erule finite_induct, simp_all)

instance star :: (finite) finite
apply (intro_classes)
apply (subst starset_UNIV [symmetric])
apply (subst starset_finite [OF finite])
apply (rule finite_imageI [OF finite])
done

end

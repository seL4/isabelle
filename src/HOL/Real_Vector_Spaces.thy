(*  Title:      HOL/Real_Vector_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

section \<open>Vector Spaces and Algebras over the Reals\<close>

theory Real_Vector_Spaces              
imports Real Topological_Spaces Vector_Spaces
begin                                   

subsection \<open>Real vector spaces\<close>

class scaleR =
  fixes scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>R" 75)
begin

abbreviation divideR :: "'a \<Rightarrow> real \<Rightarrow> 'a"  (infixl "'/\<^sub>R" 70)
  where "x /\<^sub>R r \<equiv> inverse r *\<^sub>R x"

end

class real_vector = scaleR + ab_group_add +
  assumes scaleR_add_right: "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
  and scaleR_add_left: "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
  and scaleR_scaleR: "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
  and scaleR_one: "1 *\<^sub>R x = x"

class real_algebra = real_vector + ring +
  assumes mult_scaleR_left [simp]: "a *\<^sub>R x * y = a *\<^sub>R (x * y)"
    and mult_scaleR_right [simp]: "x * a *\<^sub>R y = a *\<^sub>R (x * y)"

class real_algebra_1 = real_algebra + ring_1

class real_div_algebra = real_algebra_1 + division_ring

class real_field = real_div_algebra + field

instantiation real :: real_field
begin

definition real_scaleR_def [simp]: "scaleR a x = a * x"

instance
  by standard (simp_all add: algebra_simps)

end

locale linear = Vector_Spaces.linear "scaleR::_\<Rightarrow>_\<Rightarrow>'a::real_vector" "scaleR::_\<Rightarrow>_\<Rightarrow>'b::real_vector"
begin

lemmas scaleR = scale

end

global_interpretation real_vector?: vector_space "scaleR :: real \<Rightarrow> 'a \<Rightarrow> 'a :: real_vector"
  rewrites "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) = linear"
    and "Vector_Spaces.linear (*) (*\<^sub>R) = linear"
  defines dependent_raw_def: dependent = real_vector.dependent
    and representation_raw_def: representation = real_vector.representation
    and subspace_raw_def: subspace = real_vector.subspace
    and span_raw_def: span = real_vector.span
    and extend_basis_raw_def: extend_basis = real_vector.extend_basis
    and dim_raw_def: dim = real_vector.dim
proof unfold_locales
  show "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) = linear" "Vector_Spaces.linear (*) (*\<^sub>R) = linear"
    by (force simp: linear_def real_scaleR_def[abs_def])+
qed (use scaleR_add_right scaleR_add_left scaleR_scaleR scaleR_one in auto)

hide_const (open)\<comment> \<open>locale constants\<close>
  real_vector.dependent
  real_vector.independent
  real_vector.representation
  real_vector.subspace
  real_vector.span
  real_vector.extend_basis
  real_vector.dim

abbreviation "independent x \<equiv> \<not> dependent x"

global_interpretation real_vector?: vector_space_pair "scaleR::_\<Rightarrow>_\<Rightarrow>'a::real_vector" "scaleR::_\<Rightarrow>_\<Rightarrow>'b::real_vector"
  rewrites  "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) = linear"
    and "Vector_Spaces.linear (*) (*\<^sub>R) = linear"
  defines construct_raw_def: construct = real_vector.construct
proof unfold_locales
  show "Vector_Spaces.linear (*) (*\<^sub>R) = linear"
  unfolding linear_def real_scaleR_def by auto
qed (auto simp: linear_def)

hide_const (open)\<comment> \<open>locale constants\<close>
  real_vector.construct

lemma linear_compose: "linear f \<Longrightarrow> linear g \<Longrightarrow> linear (g \<circ> f)"
  unfolding linear_def by (rule Vector_Spaces.linear_compose)

text \<open>Recover original theorem names\<close>

lemmas scaleR_left_commute = real_vector.scale_left_commute
lemmas scaleR_zero_left = real_vector.scale_zero_left
lemmas scaleR_minus_left = real_vector.scale_minus_left
lemmas scaleR_diff_left = real_vector.scale_left_diff_distrib
lemmas scaleR_sum_left = real_vector.scale_sum_left
lemmas scaleR_zero_right = real_vector.scale_zero_right
lemmas scaleR_minus_right = real_vector.scale_minus_right
lemmas scaleR_diff_right = real_vector.scale_right_diff_distrib
lemmas scaleR_sum_right = real_vector.scale_sum_right
lemmas scaleR_eq_0_iff = real_vector.scale_eq_0_iff
lemmas scaleR_left_imp_eq = real_vector.scale_left_imp_eq
lemmas scaleR_right_imp_eq = real_vector.scale_right_imp_eq
lemmas scaleR_cancel_left = real_vector.scale_cancel_left
lemmas scaleR_cancel_right = real_vector.scale_cancel_right

lemma [field_simps]:
  "c \<noteq> 0 \<Longrightarrow> a = b /\<^sub>R c \<longleftrightarrow> c *\<^sub>R a = b"
  "c \<noteq> 0 \<Longrightarrow> b /\<^sub>R c = a \<longleftrightarrow> b = c *\<^sub>R a"
  "c \<noteq> 0 \<Longrightarrow> a + b /\<^sub>R c = (c *\<^sub>R a + b) /\<^sub>R c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>R c + b = (a + c *\<^sub>R b) /\<^sub>R c"
  "c \<noteq> 0 \<Longrightarrow> a - b /\<^sub>R c = (c *\<^sub>R a - b) /\<^sub>R c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>R c - b = (a - c *\<^sub>R b) /\<^sub>R c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>R c) + b = (- a + c *\<^sub>R b) /\<^sub>R c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>R c) - b = (- a - c *\<^sub>R b) /\<^sub>R c"
  for a b :: "'a :: real_vector"
  by (auto simp add: scaleR_add_right scaleR_add_left scaleR_diff_right scaleR_diff_left)


text \<open>Legacy names\<close>

lemmas scaleR_left_distrib = scaleR_add_left
lemmas scaleR_right_distrib = scaleR_add_right
lemmas scaleR_left_diff_distrib = scaleR_diff_left
lemmas scaleR_right_diff_distrib = scaleR_diff_right

lemmas linear_injective_0 = linear_inj_iff_eq_0
  and linear_injective_on_subspace_0 = linear_inj_on_iff_eq_0
  and linear_cmul = linear_scale
  and linear_scaleR = linear_scale_self
  and subspace_mul = subspace_scale
  and span_linear_image = linear_span_image
  and span_0 = span_zero
  and span_mul = span_scale
  and injective_scaleR = injective_scale

lemma scaleR_minus1_left [simp]: "scaleR (-1) x = - x"
  for x :: "'a::real_vector"
  using scaleR_minus_left [of 1 x] by simp

lemma scaleR_2:
  fixes x :: "'a::real_vector"
  shows "scaleR 2 x = x + x"
  unfolding one_add_one [symmetric] scaleR_left_distrib by simp

lemma scaleR_half_double [simp]:
  fixes a :: "'a::real_vector"
  shows "(1 / 2) *\<^sub>R (a + a) = a"
proof -
  have "\<And>r. r *\<^sub>R (a + a) = (r * 2) *\<^sub>R a"
    by (metis scaleR_2 scaleR_scaleR)
  then show ?thesis
    by simp
qed

lemma linear_scale_real:
  fixes r::real shows "linear f \<Longrightarrow> f (r * b) = r * f b"
  using linear_scale by fastforce

interpretation scaleR_left: additive "(\<lambda>a. scaleR a x :: 'a::real_vector)"
  by standard (rule scaleR_left_distrib)

interpretation scaleR_right: additive "(\<lambda>x. scaleR a x :: 'a::real_vector)"
  by standard (rule scaleR_right_distrib)

lemma nonzero_inverse_scaleR_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
  for x :: "'a::real_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleR_distrib: "inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
  for x :: "'a::{real_div_algebra,division_ring}"
  by (metis inverse_zero nonzero_inverse_scaleR_distrib scale_eq_0_iff)

lemmas sum_constant_scaleR = real_vector.sum_constant_scale\<comment> \<open>legacy name\<close>

named_theorems vector_add_divide_simps "to simplify sums of scaled vectors"

lemma [vector_add_divide_simps]:
  "v + (b / z) *\<^sub>R w = (if z = 0 then v else (z *\<^sub>R v + b *\<^sub>R w) /\<^sub>R z)"
  "a *\<^sub>R v + (b / z) *\<^sub>R w = (if z = 0 then a *\<^sub>R v else ((a * z) *\<^sub>R v + b *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v + w = (if z = 0 then w else (a *\<^sub>R v + z *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v + b *\<^sub>R w = (if z = 0 then b *\<^sub>R w else (a *\<^sub>R v + (b * z) *\<^sub>R w) /\<^sub>R z)"
  "v - (b / z) *\<^sub>R w = (if z = 0 then v else (z *\<^sub>R v - b *\<^sub>R w) /\<^sub>R z)"
  "a *\<^sub>R v - (b / z) *\<^sub>R w = (if z = 0 then a *\<^sub>R v else ((a * z) *\<^sub>R v - b *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v - w = (if z = 0 then -w else (a *\<^sub>R v - z *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v - b *\<^sub>R w = (if z = 0 then -b *\<^sub>R w else (a *\<^sub>R v - (b * z) *\<^sub>R w) /\<^sub>R z)"
  for v :: "'a :: real_vector"
  by (simp_all add: divide_inverse_commute scaleR_add_right scaleR_diff_right)


lemma eq_vector_fraction_iff [vector_add_divide_simps]:
  fixes x :: "'a :: real_vector"
  shows "(x = (u / v) *\<^sub>R a) \<longleftrightarrow> (if v=0 then x = 0 else v *\<^sub>R x = u *\<^sub>R a)"
by auto (metis (no_types) divide_eq_1_iff divide_inverse_commute scaleR_one scaleR_scaleR)

lemma vector_fraction_eq_iff [vector_add_divide_simps]:
  fixes x :: "'a :: real_vector"
  shows "((u / v) *\<^sub>R a = x) \<longleftrightarrow> (if v=0 then x = 0 else u *\<^sub>R a = v *\<^sub>R x)"
by (metis eq_vector_fraction_iff)

lemma real_vector_affinity_eq:
  fixes x :: "'a :: real_vector"
  assumes m0: "m \<noteq> 0"
  shows "m *\<^sub>R x + c = y \<longleftrightarrow> x = inverse m *\<^sub>R y - (inverse m *\<^sub>R c)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "m *\<^sub>R x = y - c" by (simp add: field_simps)
  then have "inverse m *\<^sub>R (m *\<^sub>R x) = inverse m *\<^sub>R (y - c)" by simp
  then show "x = inverse m *\<^sub>R y - (inverse m *\<^sub>R c)"
    using m0
  by (simp add: scaleR_diff_right)
next
  assume ?rhs
  with m0 show "m *\<^sub>R x + c = y"
    by (simp add: scaleR_diff_right)
qed

lemma real_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>R x + c \<longleftrightarrow> inverse m *\<^sub>R y - (inverse m *\<^sub>R c) = x"
  for x :: "'a::real_vector"
  using real_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleR_eq_iff [simp]: "b + u *\<^sub>R a = a + u *\<^sub>R b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::real_vector"
proof (cases "u = 1")
  case True
  then show ?thesis by auto
next
  case False
  have "a = b" if "b + u *\<^sub>R a = a + u *\<^sub>R b"
  proof -
    from that have "(u - 1) *\<^sub>R a = (u - 1) *\<^sub>R b"
      by (simp add: algebra_simps)
    with False show ?thesis
      by auto
  qed
  then show ?thesis by auto
qed

lemma scaleR_collapse [simp]: "(1 - u) *\<^sub>R a + u *\<^sub>R a = a"
  for a :: "'a::real_vector"
  by (simp add: algebra_simps)


subsection \<open>Embedding of the Reals into any \<open>real_algebra_1\<close>: \<open>of_real\<close>\<close>

definition of_real :: "real \<Rightarrow> 'a::real_algebra_1"
  where "of_real r = scaleR r 1"

lemma scaleR_conv_of_real: "scaleR r x = of_real r * x"
  by (simp add: of_real_def)

lemma of_real_0 [simp]: "of_real 0 = 0"
  by (simp add: of_real_def)

lemma of_real_1 [simp]: "of_real 1 = 1"
  by (simp add: of_real_def)

lemma of_real_add [simp]: "of_real (x + y) = of_real x + of_real y"
  by (simp add: of_real_def scaleR_left_distrib)

lemma of_real_minus [simp]: "of_real (- x) = - of_real x"
  by (simp add: of_real_def)

lemma of_real_diff [simp]: "of_real (x - y) = of_real x - of_real y"
  by (simp add: of_real_def scaleR_left_diff_distrib)

lemma of_real_mult [simp]: "of_real (x * y) = of_real x * of_real y"
  by (simp add: of_real_def)

lemma of_real_sum[simp]: "of_real (sum f s) = (\<Sum>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_real_prod[simp]: "of_real (prod f s) = (\<Prod>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_real (inverse x) = inverse (of_real x :: 'a::real_div_algebra)"
  by (simp add: of_real_def nonzero_inverse_scaleR_distrib)

lemma of_real_inverse [simp]:
  "of_real (inverse x) = inverse (of_real x :: 'a::{real_div_algebra,division_ring})"
  by (simp add: of_real_def inverse_scaleR_distrib)

lemma nonzero_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> of_real (x / y) = (of_real x / of_real y :: 'a::real_field)"
  by (simp add: divide_inverse nonzero_of_real_inverse)

lemma of_real_divide [simp]:
  "of_real (x / y) = (of_real x / of_real y :: 'a::real_div_algebra)"
  by (simp add: divide_inverse)

lemma of_real_power [simp]:
  "of_real (x ^ n) = (of_real x :: 'a::{real_algebra_1}) ^ n"
  by (induct n) simp_all

lemma of_real_power_int [simp]:
  "of_real (power_int x n) = power_int (of_real x :: 'a :: {real_div_algebra,division_ring}) n"
  by (auto simp: power_int_def)

lemma of_real_eq_iff [simp]: "of_real x = of_real y \<longleftrightarrow> x = y"
  by (simp add: of_real_def)

lemma inj_of_real: "inj of_real"
  by (auto intro: injI)

lemmas of_real_eq_0_iff [simp] = of_real_eq_iff [of _ 0, simplified]
lemmas of_real_eq_1_iff [simp] = of_real_eq_iff [of _ 1, simplified]

lemma minus_of_real_eq_of_real_iff [simp]: "-of_real x = of_real y \<longleftrightarrow> -x = y"
  using of_real_eq_iff[of "-x" y] by (simp only: of_real_minus)

lemma of_real_eq_minus_of_real_iff [simp]: "of_real x = -of_real y \<longleftrightarrow> x = -y"
  using of_real_eq_iff[of x "-y"] by (simp only: of_real_minus)

lemma of_real_eq_id [simp]: "of_real = (id :: real \<Rightarrow> real)"
  by (rule ext) (simp add: of_real_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_real_of_nat_eq [simp]: "of_real (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_real_of_int_eq [simp]: "of_real (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_real_numeral [simp]: "of_real (numeral w) = numeral w"
  using of_real_of_int_eq [of "numeral w"] by simp

lemma of_real_neg_numeral [simp]: "of_real (- numeral w) = - numeral w"
  using of_real_of_int_eq [of "- numeral w"] by simp

lemma numeral_power_int_eq_of_real_cancel_iff [simp]:
  "power_int (numeral x) n = (of_real y :: 'a :: {real_div_algebra, division_ring}) \<longleftrightarrow>
     power_int (numeral x) n = y"
proof -
  have "power_int (numeral x) n = (of_real (power_int (numeral x) n) :: 'a)"
    by simp
  also have "\<dots> = of_real y \<longleftrightarrow> power_int (numeral x) n = y"
    by (subst of_real_eq_iff) auto
  finally show ?thesis .
qed

lemma of_real_eq_numeral_power_int_cancel_iff [simp]:
  "(of_real y :: 'a :: {real_div_algebra, division_ring}) = power_int (numeral x) n \<longleftrightarrow>
     y = power_int (numeral x) n"
  by (subst (1 2) eq_commute) simp

lemma of_real_eq_of_real_power_int_cancel_iff [simp]:
  "power_int (of_real b :: 'a :: {real_div_algebra, division_ring}) w = of_real x \<longleftrightarrow>
     power_int b w = x"
  by (metis of_real_power_int of_real_eq_iff)

lemma of_real_in_Ints_iff [simp]: "of_real x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
proof safe
  fix x assume "(of_real x :: 'a) \<in> \<int>"
  then obtain n where "(of_real x :: 'a) = of_int n"
    by (auto simp: Ints_def)
  also have "of_int n = of_real (real_of_int n)"
    by simp
  finally have "x = real_of_int n"
    by (subst (asm) of_real_eq_iff)
  thus "x \<in> \<int>"
    by auto
qed (auto simp: Ints_def)

lemma Ints_of_real [intro]: "x \<in> \<int> \<Longrightarrow> of_real x \<in> \<int>"
  by simp


text \<open>Every real algebra has characteristic zero.\<close>
instance real_algebra_1 < ring_char_0
proof
  from inj_of_real inj_of_nat have "inj (of_real \<circ> of_nat)"
    by (rule inj_compose)
  then show "inj (of_nat :: nat \<Rightarrow> 'a)"
    by (simp add: comp_def)
qed

lemma fraction_scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>R (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>R a"
by (metis (no_types, lifting) of_real_numeral scaleR_conv_of_real scaleR_scaleR times_divide_eq_left)

lemma inverse_scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(1 / numeral v) *\<^sub>R (numeral w * a) = (numeral w / numeral v) *\<^sub>R a"
by (metis divide_inverse_commute inverse_eq_divide of_real_numeral scaleR_conv_of_real scaleR_scaleR)

lemma scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(numeral u) *\<^sub>R (numeral w * a) = (numeral u * numeral w) *\<^sub>R a"
by (simp add: scaleR_conv_of_real)

instance real_field < field_char_0 ..


subsection \<open>The Set of Real Numbers\<close>

definition Reals :: "'a::real_algebra_1 set"  ("\<real>")
  where "\<real> = range of_real"

lemma Reals_of_real [simp]: "of_real r \<in> \<real>"
  by (simp add: Reals_def)

lemma Reals_of_int [simp]: "of_int z \<in> \<real>"
  by (subst of_real_of_int_eq [symmetric], rule Reals_of_real)

lemma Reals_of_nat [simp]: "of_nat n \<in> \<real>"
  by (subst of_real_of_nat_eq [symmetric], rule Reals_of_real)

lemma Reals_numeral [simp]: "numeral w \<in> \<real>"
  by (subst of_real_numeral [symmetric], rule Reals_of_real)

lemma Reals_0 [simp]: "0 \<in> \<real>" and Reals_1 [simp]: "1 \<in> \<real>"
  by (simp_all add: Reals_def)

lemma Reals_add [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a + b \<in> \<real>"
  by (metis (no_types, opaque_lifting) Reals_def Reals_of_real imageE of_real_add)

lemma Reals_minus [simp]: "a \<in> \<real> \<Longrightarrow> - a \<in> \<real>"
  by (auto simp: Reals_def)

lemma Reals_minus_iff [simp]: "- a \<in> \<real> \<longleftrightarrow> a \<in> \<real>"
  using Reals_minus by fastforce

lemma Reals_diff [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a - b \<in> \<real>"
  by (metis Reals_add Reals_minus_iff add_uminus_conv_diff)

lemma Reals_mult [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a * b \<in> \<real>"
  by (metis (no_types, lifting) Reals_def Reals_of_real imageE of_real_mult)

lemma nonzero_Reals_inverse: "a \<in> \<real> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<real>"
  for a :: "'a::real_div_algebra"
  by (metis Reals_def Reals_of_real imageE of_real_inverse)

lemma Reals_inverse: "a \<in> \<real> \<Longrightarrow> inverse a \<in> \<real>"
  for a :: "'a::{real_div_algebra,division_ring}"
  using nonzero_Reals_inverse by fastforce

lemma Reals_inverse_iff [simp]: "inverse x \<in> \<real> \<longleftrightarrow> x \<in> \<real>"
  for x :: "'a::{real_div_algebra,division_ring}"
  by (metis Reals_inverse inverse_inverse_eq)

lemma nonzero_Reals_divide: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<real>"
  for a b :: "'a::real_field"
  by (simp add: divide_inverse)

lemma Reals_divide [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a / b \<in> \<real>"
  for a b :: "'a::{real_field,field}"
  using nonzero_Reals_divide by fastforce

lemma Reals_power [simp]: "a \<in> \<real> \<Longrightarrow> a ^ n \<in> \<real>"
  for a :: "'a::real_algebra_1"
  by (metis Reals_def Reals_of_real imageE of_real_power)

lemma Reals_cases [cases set: Reals]:
  assumes "q \<in> \<real>"
  obtains (of_real) r where "q = of_real r"
  unfolding Reals_def
proof -
  from \<open>q \<in> \<real>\<close> have "q \<in> range of_real" unfolding Reals_def .
  then obtain r where "q = of_real r" ..
  then show thesis ..
qed

lemma sum_in_Reals [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>) \<Longrightarrow> sum f s \<in> \<real>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Reals_0 sum.infinite)
qed simp_all

lemma prod_in_Reals [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>) \<Longrightarrow> prod f s \<in> \<real>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Reals_1 prod.infinite)
qed simp_all

lemma Reals_induct [case_names of_real, induct set: Reals]:
  "q \<in> \<real> \<Longrightarrow> (\<And>r. P (of_real r)) \<Longrightarrow> P q"
  by (rule Reals_cases) auto


subsection \<open>Ordered real vector spaces\<close>

class ordered_real_vector = real_vector + ordered_ab_group_add +
  assumes scaleR_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>R x \<le> a *\<^sub>R y"
    and scaleR_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R x"
begin

lemma scaleR_mono:
  "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R y"
  by (meson order_trans scaleR_left_mono scaleR_right_mono)
  
lemma scaleR_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R d"
  by (rule scaleR_mono) (auto intro: order.trans)

lemma pos_le_divideR_eq [field_simps]:
  "a \<le> b /\<^sub>R c \<longleftrightarrow> c *\<^sub>R a \<le> b" (is "?P \<longleftrightarrow> ?Q") if "0 < c"
proof
  assume ?P
  with scaleR_left_mono that have "c *\<^sub>R a \<le> c *\<^sub>R (b /\<^sub>R c)"
    by simp
  with that show ?Q
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
next
  assume ?Q
  with scaleR_left_mono that have "c *\<^sub>R a /\<^sub>R c \<le> b /\<^sub>R c"
    by simp
  with that show ?P
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
qed

lemma pos_less_divideR_eq [field_simps]:
  "a < b /\<^sub>R c \<longleftrightarrow> c *\<^sub>R a < b" if "c > 0"
  using that pos_le_divideR_eq [of c a b]
  by (auto simp add: le_less scaleR_scaleR scaleR_one)

lemma pos_divideR_le_eq [field_simps]:
  "b /\<^sub>R c \<le> a \<longleftrightarrow> b \<le> c *\<^sub>R a" if "c > 0"
  using that pos_le_divideR_eq [of "inverse c" b a] by simp

lemma pos_divideR_less_eq [field_simps]:
  "b /\<^sub>R c < a \<longleftrightarrow> b < c *\<^sub>R a" if "c > 0"
  using that pos_less_divideR_eq [of "inverse c" b a] by simp

lemma pos_le_minus_divideR_eq [field_simps]:
  "a \<le> - (b /\<^sub>R c) \<longleftrightarrow> c *\<^sub>R a \<le> - b" if "c > 0"
  using that by (metis add_minus_cancel diff_0 left_minus minus_minus neg_le_iff_le
    scaleR_add_right uminus_add_conv_diff pos_le_divideR_eq)
  
lemma pos_less_minus_divideR_eq [field_simps]:
  "a < - (b /\<^sub>R c) \<longleftrightarrow> c *\<^sub>R a < - b" if "c > 0"
  using that by (metis le_less less_le_not_le pos_divideR_le_eq
    pos_divideR_less_eq pos_le_minus_divideR_eq)

lemma pos_minus_divideR_le_eq [field_simps]:
  "- (b /\<^sub>R c) \<le> a \<longleftrightarrow> - b \<le> c *\<^sub>R a" if "c > 0"
  using that by (metis pos_divideR_le_eq pos_le_minus_divideR_eq that
    inverse_positive_iff_positive le_imp_neg_le minus_minus)

lemma pos_minus_divideR_less_eq [field_simps]:
  "- (b /\<^sub>R c) < a \<longleftrightarrow> - b < c *\<^sub>R a" if "c > 0"
  using that by (simp add: less_le_not_le pos_le_minus_divideR_eq pos_minus_divideR_le_eq) 

lemma scaleR_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleR c ` {x..y} = {c *\<^sub>R x..c *\<^sub>R y}"
  apply (auto intro!: scaleR_left_mono simp: image_iff Bex_def)
  using pos_divideR_le_eq [of c] pos_le_divideR_eq [of c]
  apply (meson local.order_eq_iff) 
  done

end

lemma neg_le_divideR_eq [field_simps]:
  "a \<le> b /\<^sub>R c \<longleftrightarrow> b \<le> c *\<^sub>R a" (is "?P \<longleftrightarrow> ?Q") if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that pos_le_divideR_eq [of "- c" a "- b"] by simp

lemma neg_less_divideR_eq [field_simps]:
  "a < b /\<^sub>R c \<longleftrightarrow> b < c *\<^sub>R a" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that neg_le_divideR_eq [of c a b] by (auto simp add: le_less)

lemma neg_divideR_le_eq [field_simps]:
  "b /\<^sub>R c \<le> a \<longleftrightarrow> c *\<^sub>R a \<le> b" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that pos_divideR_le_eq [of "- c" "- b" a] by simp

lemma neg_divideR_less_eq [field_simps]:
  "b /\<^sub>R c < a \<longleftrightarrow> c *\<^sub>R a < b" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that neg_divideR_le_eq [of c b a] by (auto simp add: le_less)

lemma neg_le_minus_divideR_eq [field_simps]:
  "a \<le> - (b /\<^sub>R c) \<longleftrightarrow> - b \<le> c *\<^sub>R a" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that pos_le_minus_divideR_eq [of "- c" a "- b"] by (simp add: minus_le_iff)
  
lemma neg_less_minus_divideR_eq [field_simps]:
  "a < - (b /\<^sub>R c) \<longleftrightarrow> - b < c *\<^sub>R a" if "c < 0"
   for a b :: "'a :: ordered_real_vector"
proof -
  have *: "- b = c *\<^sub>R a \<longleftrightarrow> b = - (c *\<^sub>R a)"
    by (metis add.inverse_inverse)
  from that neg_le_minus_divideR_eq [of c a b]
  show ?thesis by (auto simp add: le_less *)
qed

lemma neg_minus_divideR_le_eq [field_simps]:
  "- (b /\<^sub>R c) \<le> a \<longleftrightarrow> c *\<^sub>R a \<le> - b" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that pos_minus_divideR_le_eq [of "- c" "- b" a] by (simp add: le_minus_iff) 

lemma neg_minus_divideR_less_eq [field_simps]:
  "- (b /\<^sub>R c) < a \<longleftrightarrow> c *\<^sub>R a < - b" if "c < 0"
    for a b :: "'a :: ordered_real_vector"
  using that by (simp add: less_le_not_le neg_le_minus_divideR_eq neg_minus_divideR_le_eq)

lemma [field_split_simps]:
  "a = b /\<^sub>R c \<longleftrightarrow> (if c = 0 then a = 0 else c *\<^sub>R a = b)"
  "b /\<^sub>R c = a \<longleftrightarrow> (if c = 0 then a = 0 else b = c *\<^sub>R a)"
  "a + b /\<^sub>R c = (if c = 0 then a else (c *\<^sub>R a + b) /\<^sub>R c)"
  "a /\<^sub>R c + b = (if c = 0 then b else (a + c *\<^sub>R b) /\<^sub>R c)"
  "a - b /\<^sub>R c = (if c = 0 then a else (c *\<^sub>R a - b) /\<^sub>R c)"
  "a /\<^sub>R c - b = (if c = 0 then - b else (a - c *\<^sub>R b) /\<^sub>R c)"
  "- (a /\<^sub>R c) + b = (if c = 0 then b else (- a + c *\<^sub>R b) /\<^sub>R c)"
  "- (a /\<^sub>R c) - b = (if c = 0 then - b else (- a - c *\<^sub>R b) /\<^sub>R c)"
    for a b :: "'a :: real_vector"
  by (auto simp add: field_simps)

lemma [field_split_simps]:
  "0 < c \<Longrightarrow> a \<le> b /\<^sub>R c \<longleftrightarrow> (if c > 0 then c *\<^sub>R a \<le> b else if c < 0 then b \<le> c *\<^sub>R a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < b /\<^sub>R c \<longleftrightarrow> (if c > 0 then c *\<^sub>R a < b else if c < 0 then b < c *\<^sub>R a else a < 0)"
  "0 < c \<Longrightarrow> b /\<^sub>R c \<le> a \<longleftrightarrow> (if c > 0 then b \<le> c *\<^sub>R a else if c < 0 then c *\<^sub>R a \<le> b else a \<ge> 0)"
  "0 < c \<Longrightarrow> b /\<^sub>R c < a \<longleftrightarrow> (if c > 0 then b < c *\<^sub>R a else if c < 0 then c *\<^sub>R a < b else a > 0)"
  "0 < c \<Longrightarrow> a \<le> - (b /\<^sub>R c) \<longleftrightarrow> (if c > 0 then c *\<^sub>R a \<le> - b else if c < 0 then - b \<le> c *\<^sub>R a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < - (b /\<^sub>R c) \<longleftrightarrow> (if c > 0 then c *\<^sub>R a < - b else if c < 0 then - b < c *\<^sub>R a else a < 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>R c) \<le> a \<longleftrightarrow> (if c > 0 then - b \<le> c *\<^sub>R a else if c < 0 then c *\<^sub>R a \<le> - b else a \<ge> 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>R c) < a \<longleftrightarrow> (if c > 0 then - b < c *\<^sub>R a else if c < 0 then c *\<^sub>R a < - b else a > 0)"
  for a b :: "'a :: ordered_real_vector"
  by (clarsimp intro!: field_simps)+

lemma scaleR_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> a *\<^sub>R x"
  for x :: "'a::ordered_real_vector"
  using scaleR_left_mono [of 0 x a] by simp

lemma scaleR_nonneg_nonpos: "0 \<le> a \<Longrightarrow> x \<le> 0 \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  using scaleR_left_mono [of x 0 a] by simp

lemma scaleR_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  using scaleR_right_mono [of a 0 x] by simp

lemma split_scaleR_neg_le: "(0 \<le> a \<and> x \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> x) \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  by (auto simp: scaleR_nonneg_nonpos scaleR_nonpos_nonneg)

lemma le_add_iff1: "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> (a - b) *\<^sub>R e + c \<le> d"
  for c d e :: "'a::ordered_real_vector"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>R e + d"
  for c d e :: "'a::ordered_real_vector"
  by (simp add: algebra_simps)

lemma scaleR_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b"
  for a b :: "'a::ordered_real_vector"
  by (drule scaleR_left_mono [of _ _ "- c"], simp_all)

lemma scaleR_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R c"
  for c :: "'a::ordered_real_vector"
  by (drule scaleR_right_mono [of _ _ "- c"], simp_all)

lemma scaleR_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>R b"
  for b :: "'a::ordered_real_vector"
  using scaleR_right_mono_neg [of a 0 b] by simp

lemma split_scaleR_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>R b"
  for b :: "'a::ordered_real_vector"
  by (auto simp: scaleR_nonneg_nonneg scaleR_nonpos_nonpos)

lemma zero_le_scaleR_iff:
  fixes b :: "'a::ordered_real_vector"
  shows "0 \<le> a *\<^sub>R b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0" by arith
    then show ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>R 0 \<le> inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>R 0 \<le> - inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    then show ?lhs
      by (auto simp: not_le \<open>a \<noteq> 0\<close> intro!: split_scaleR_pos_le)
  qed
qed

lemma scaleR_le_0_iff: "a *\<^sub>R b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  for b::"'a::ordered_real_vector"
  by (insert zero_le_scaleR_iff [of "-a" b]) force

lemma scaleR_le_cancel_left: "c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  for b :: "'a::ordered_real_vector"
  by (auto simp: neq_iff scaleR_left_mono scaleR_left_mono_neg
      dest: scaleR_left_mono[where a="inverse c"] scaleR_left_mono_neg[where c="inverse c"])

lemma scaleR_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_real_vector"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_real_vector"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>R x \<le> x"
  for x :: "'a::ordered_real_vector" and a :: real
  using scaleR_right_mono[of a 1 x] by simp


subsection \<open>Real normed vector spaces\<close>

class dist =
  fixes dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class norm =
  fixes norm :: "'a \<Rightarrow> real"

class sgn_div_norm = scaleR + norm + sgn +
  assumes sgn_div_norm: "sgn x = x /\<^sub>R norm x"

class dist_norm = dist + norm + minus +
  assumes dist_norm: "dist x y = norm (x - y)"

class uniformity_dist = dist + uniformity +
  assumes uniformity_dist: "uniformity = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"
begin

lemma eventually_uniformity_metric:
  "eventually P uniformity \<longleftrightarrow> (\<exists>e>0. \<forall>x y. dist x y < e \<longrightarrow> P (x, y))"
  unfolding uniformity_dist
  by (subst eventually_INF_base)
     (auto simp: eventually_principal subset_eq intro: bexI[of _ "min _ _"])

end

class real_normed_vector = real_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  assumes norm_eq_zero [simp]: "norm x = 0 \<longleftrightarrow> x = 0"
    and norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"
    and norm_scaleR [simp]: "norm (scaleR a x) = \<bar>a\<bar> * norm x"
begin

lemma norm_ge_zero [simp]: "0 \<le> norm x"
proof -
  have "0 = norm (x + -1 *\<^sub>R x)"
    using scaleR_add_left[of 1 "-1" x] norm_scaleR[of 0 x] by (simp add: scaleR_one)
  also have "\<dots> \<le> norm x + norm (-1 *\<^sub>R x)" by (rule norm_triangle_ineq)
  finally show ?thesis by simp
qed

lemma bdd_below_norm_image: "bdd_below (norm ` A)"
  by (meson bdd_belowI2 norm_ge_zero)

end

class real_normed_algebra = real_algebra + real_normed_vector +
  assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

class real_normed_algebra_1 = real_algebra_1 + real_normed_algebra +
  assumes norm_one [simp]: "norm 1 = 1"

lemma (in real_normed_algebra_1) scaleR_power [simp]: "(scaleR x y) ^ n = scaleR (x^n) (y^n)"
  by (induct n) (simp_all add: scaleR_one scaleR_scaleR mult_ac)

class real_normed_div_algebra = real_div_algebra + real_normed_vector +
  assumes norm_mult: "norm (x * y) = norm x * norm y"

class real_normed_field = real_field + real_normed_div_algebra

instance real_normed_div_algebra < real_normed_algebra_1
proof
  show "norm (x * y) \<le> norm x * norm y" for x y :: 'a
    by (simp add: norm_mult)
next
  have "norm (1 * 1::'a) = norm (1::'a) * norm (1::'a)"
    by (rule norm_mult)
  then show "norm (1::'a) = 1" by simp
qed

context real_normed_vector begin

lemma norm_zero [simp]: "norm (0::'a) = 0"
  by simp

lemma zero_less_norm_iff [simp]: "norm x > 0 \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma norm_not_less_zero [simp]: "\<not> norm x < 0"
  by (simp add: linorder_not_less)

lemma norm_le_zero_iff [simp]: "norm x \<le> 0 \<longleftrightarrow> x = 0"
  by (simp add: order_le_less)

lemma norm_minus_cancel [simp]: "norm (- x) = norm x"
proof -
  have "- 1 *\<^sub>R x = - (1 *\<^sub>R x)"
    unfolding add_eq_0_iff2[symmetric] scaleR_add_left[symmetric]
    using norm_eq_zero
    by fastforce
  then have "norm (- x) = norm (scaleR (- 1) x)"
    by (simp only: scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute: "norm (a - b) = norm (b - a)"
proof -
  have "norm (- (b - a)) = norm (b - a)"
    by (rule norm_minus_cancel)
  then show ?thesis by simp
qed

lemma dist_add_cancel [simp]: "dist (a + b) (a + c) = dist b c"
  by (simp add: dist_norm)

lemma dist_add_cancel2 [simp]: "dist (b + a) (c + a) = dist b c"
  by (simp add: dist_norm)

lemma norm_uminus_minus: "norm (- x - y) = norm (x + y)"
  by (subst (2) norm_minus_cancel[symmetric], subst minus_add_distrib) simp

lemma norm_triangle_ineq2: "norm a - norm b \<le> norm (a - b)"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  then show ?thesis by simp
qed

lemma norm_triangle_ineq3: "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
proof -
  have "norm a - norm b \<le> norm (a - b)"
    by (simp add: norm_triangle_ineq2)
  moreover have "norm b - norm a \<le> norm (a - b)"
    by (metis norm_minus_commute norm_triangle_ineq2)
  ultimately show ?thesis
    by (simp add: abs_le_iff)
qed

lemma norm_triangle_ineq4: "norm (a - b) \<le> norm a + norm b"
proof -
  have "norm (a + - b) \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  then show ?thesis by simp
qed

lemma norm_triangle_le_diff: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
    by (meson norm_triangle_ineq4 order_trans)

lemma norm_diff_ineq: "norm a - norm b \<le> norm (a + b)"
proof -
  have "norm a - norm (- b) \<le> norm (a - - b)"
    by (rule norm_triangle_ineq2)
  then show ?thesis by simp
qed

lemma norm_triangle_sub: "norm x \<le> norm y + norm (x - y)"
  using norm_triangle_ineq[of "y" "x - y"] by (simp add: field_simps)

lemma norm_triangle_le: "norm x + norm y \<le> e \<Longrightarrow> norm (x + y) \<le> e"
  by (rule norm_triangle_ineq [THEN order_trans])

lemma norm_triangle_lt: "norm x + norm y < e \<Longrightarrow> norm (x + y) < e"
  by (rule norm_triangle_ineq [THEN le_less_trans])

lemma norm_add_leD: "norm (a + b) \<le> c \<Longrightarrow> norm b \<le> norm a + c"
  by (metis ab_semigroup_add_class.add.commute add_commute diff_le_eq norm_diff_ineq order_trans)

lemma norm_diff_triangle_ineq: "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
proof -
  have "norm ((a + b) - (c + d)) = norm ((a - c) + (b - d))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> norm (a - c) + norm (b - d)"
    by (rule norm_triangle_ineq)
  finally show ?thesis .
qed

lemma norm_diff_triangle_le: "norm (x - z) \<le> e1 + e2"
  if "norm (x - y) \<le> e1"  "norm (y - z) \<le> e2"
proof -
  have "norm (x - (y + z - y)) \<le> norm (x - y) + norm (y - z)"
    using norm_diff_triangle_ineq that diff_diff_eq2 by presburger
  with that show ?thesis by simp
qed

lemma norm_diff_triangle_less: "norm (x - z) < e1 + e2"
  if "norm (x - y) < e1"  "norm (y - z) < e2"
proof -
  have "norm (x - z) \<le> norm (x - y) + norm (y - z)"
    by (metis norm_diff_triangle_ineq add_diff_cancel_left' diff_diff_eq2)
  with that show ?thesis by auto
qed

lemma norm_triangle_mono:
  "norm a \<le> r \<Longrightarrow> norm b \<le> s \<Longrightarrow> norm (a + b) \<le> r + s"
  by (metis (mono_tags) add_mono_thms_linordered_semiring(1) norm_triangle_ineq order.trans)

lemma norm_sum: "norm (sum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
  for f::"'b \<Rightarrow> 'a"
  by (induct A rule: infinite_finite_induct) (auto intro: norm_triangle_mono)

lemma sum_norm_le: "norm (sum f S) \<le> sum g S"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  for f::"'b \<Rightarrow> 'a"
  by (rule order_trans [OF norm_sum sum_mono]) (simp add: that)

lemma abs_norm_cancel [simp]: "\<bar>norm a\<bar> = norm a"
  by (rule abs_of_nonneg [OF norm_ge_zero])

lemma sum_norm_bound:
  "norm (sum f S) \<le> of_nat (card S)*K"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> K"
  for f :: "'b \<Rightarrow> 'a"
  using sum_norm_le[OF that] sum_constant[symmetric]
  by simp

lemma norm_add_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x + y) < r + s"
  by (rule order_le_less_trans [OF norm_triangle_ineq add_strict_mono])

end

lemma dist_scaleR [simp]: "dist (x *\<^sub>R a) (y *\<^sub>R a) = \<bar>x - y\<bar> * norm a"
  for a :: "'a::real_normed_vector"
  by (metis dist_norm norm_scaleR scaleR_left.diff)

lemma norm_mult_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x * y) < r * s"
  for x y :: "'a::real_normed_algebra"
  by (rule order_le_less_trans [OF norm_mult_ineq]) (simp add: mult_strict_mono')

lemma norm_of_real [simp]: "norm (of_real r :: 'a::real_normed_algebra_1) = \<bar>r\<bar>"
  by (simp add: of_real_def)

lemma norm_numeral [simp]: "norm (numeral w::'a::real_normed_algebra_1) = numeral w"
  by (subst of_real_numeral [symmetric], subst norm_of_real, simp)

lemma norm_neg_numeral [simp]: "norm (- numeral w::'a::real_normed_algebra_1) = numeral w"
  by (subst of_real_neg_numeral [symmetric], subst norm_of_real, simp)

lemma norm_of_real_add1 [simp]: "norm (of_real x + 1 :: 'a :: real_normed_div_algebra) = \<bar>x + 1\<bar>"
  by (metis norm_of_real of_real_1 of_real_add)

lemma norm_of_real_addn [simp]:
  "norm (of_real x + numeral b :: 'a :: real_normed_div_algebra) = \<bar>x + numeral b\<bar>"
  by (metis norm_of_real of_real_add of_real_numeral)

lemma norm_of_int [simp]: "norm (of_int z::'a::real_normed_algebra_1) = \<bar>of_int z\<bar>"
  by (subst of_real_of_int_eq [symmetric], rule norm_of_real)

lemma norm_of_nat [simp]: "norm (of_nat n::'a::real_normed_algebra_1) = of_nat n"
  by (metis abs_of_nat norm_of_real of_real_of_nat_eq)

lemma nonzero_norm_inverse: "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
  for a :: "'a::real_normed_div_algebra"
  by (metis inverse_unique norm_mult norm_one right_inverse)

lemma norm_inverse: "norm (inverse a) = inverse (norm a)"
  for a :: "'a::{real_normed_div_algebra,division_ring}"
  by (metis inverse_zero nonzero_norm_inverse norm_zero)

lemma nonzero_norm_divide: "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
  for a b :: "'a::real_normed_field"
  by (simp add: divide_inverse norm_mult nonzero_norm_inverse)

lemma norm_divide: "norm (a / b) = norm a / norm b"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: divide_inverse norm_mult norm_inverse)

lemma norm_inverse_le_norm:
  fixes x :: "'a::real_normed_div_algebra"
  shows "r \<le> norm x \<Longrightarrow> 0 < r \<Longrightarrow> norm (inverse x) \<le> inverse r"
  by (simp add: le_imp_inverse_le norm_inverse)

lemma norm_power_ineq: "norm (x ^ n) \<le> norm x ^ n"
  for x :: "'a::real_normed_algebra_1"
proof (induct n)
  case 0
  show "norm (x ^ 0) \<le> norm x ^ 0" by simp
next
  case (Suc n)
  have "norm (x * x ^ n) \<le> norm x * norm (x ^ n)"
    by (rule norm_mult_ineq)
  also from Suc have "\<dots> \<le> norm x * norm x ^ n"
    using norm_ge_zero by (rule mult_left_mono)
  finally show "norm (x ^ Suc n) \<le> norm x ^ Suc n"
    by simp
qed

lemma norm_power: "norm (x ^ n) = norm x ^ n"
  for x :: "'a::real_normed_div_algebra"
  by (induct n) (simp_all add: norm_mult)

lemma norm_power_int: "norm (power_int x n) = power_int (norm x) n"
  for x :: "'a::real_normed_div_algebra"
  by (cases n rule: int_cases4) (auto simp: norm_power power_int_minus norm_inverse)

lemma power_eq_imp_eq_norm:
  fixes w :: "'a::real_normed_div_algebra"
  assumes eq: "w ^ n = z ^ n" and "n > 0"
    shows "norm w = norm z"
proof -
  have "norm w ^ n = norm z ^ n"
    by (metis (no_types) eq norm_power)
  then show ?thesis
    using assms by (force intro: power_eq_imp_eq_base)
qed

lemma power_eq_1_iff:
  fixes w :: "'a::real_normed_div_algebra"
  shows "w ^ n = 1 \<Longrightarrow> norm w = 1 \<or> n = 0"
  by (metis norm_one power_0_left power_eq_0_iff power_eq_imp_eq_norm power_one)

lemma norm_mult_numeral1 [simp]: "norm (numeral w * a) = numeral w * norm a"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_mult_numeral2 [simp]: "norm (a * numeral w) = norm a * numeral w"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_divide_numeral [simp]: "norm (a / numeral w) = norm a / numeral w"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_divide)

lemma norm_of_real_diff [simp]:
  "norm (of_real b - of_real a :: 'a::real_normed_algebra_1) \<le> \<bar>b - a\<bar>"
  by (metis norm_of_real of_real_diff order_refl)

text \<open>Despite a superficial resemblance, \<open>norm_eq_1\<close> is not relevant.\<close>
lemma square_norm_one:
  fixes x :: "'a::real_normed_div_algebra"
  assumes "x\<^sup>2 = 1"
  shows "norm x = 1"
  by (metis assms norm_minus_cancel norm_one power2_eq_1_iff)

lemma norm_less_p1: "norm x < norm (of_real (norm x) + 1 :: 'a)"
  for x :: "'a::real_normed_algebra_1"
proof -
  have "norm x < norm (of_real (norm x + 1) :: 'a)"
    by (simp add: of_real_def)
  then show ?thesis
    by simp
qed

lemma prod_norm: "prod (\<lambda>x. norm (f x)) A = norm (prod f A)"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1,real_normed_div_algebra}"
  by (induct A rule: infinite_finite_induct) (auto simp: norm_mult)

lemma norm_prod_le:
  "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a :: 'a :: {real_normed_algebra_1,comm_monoid_mult}))"
proof (induct A rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "norm (prod f (insert a A)) \<le> norm (f a) * norm (prod f A)"
    by (simp add: norm_mult_ineq)
  also have "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a))"
    by (rule insert)
  finally show ?case
    by (simp add: insert mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_prod_diff:
  fixes z w :: "'i \<Rightarrow> 'a::{real_normed_algebra_1, comm_monoid_mult}"
  shows "(\<And>i. i \<in> I \<Longrightarrow> norm (z i) \<le> 1) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> norm (w i) \<le> 1) \<Longrightarrow>
    norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
proof (induction I rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  note insert.hyps[simp]

  have "norm ((\<Prod>i\<in>insert i I. z i) - (\<Prod>i\<in>insert i I. w i)) =
    norm ((\<Prod>i\<in>I. z i) * (z i - w i) + ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * w i)"
    (is "_ = norm (?t1 + ?t2)")
    by (auto simp: field_simps)
  also have "\<dots> \<le> norm ?t1 + norm ?t2"
    by (rule norm_triangle_ineq)
  also have "norm ?t1 \<le> norm (\<Prod>i\<in>I. z i) * norm (z i - w i)"
    by (rule norm_mult_ineq)
  also have "\<dots> \<le> (\<Prod>i\<in>I. norm (z i)) * norm(z i - w i)"
    by (rule mult_right_mono) (auto intro: norm_prod_le)
  also have "(\<Prod>i\<in>I. norm (z i)) \<le> (\<Prod>i\<in>I. 1)"
    by (intro prod_mono) (auto intro!: insert)
  also have "norm ?t2 \<le> norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * norm (w i)"
    by (rule norm_mult_ineq)
  also have "norm (w i) \<le> 1"
    by (auto intro: insert)
  also have "norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
    using insert by auto
  finally show ?case
    by (auto simp: ac_simps mult_right_mono mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_power_diff:
  fixes z w :: "'a::{real_normed_algebra_1, comm_monoid_mult}"
  assumes "norm z \<le> 1" "norm w \<le> 1"
  shows "norm (z^m - w^m) \<le> m * norm (z - w)"
proof -
  have "norm (z^m - w^m) = norm ((\<Prod> i < m. z) - (\<Prod> i < m. w))"
    by simp
  also have "\<dots> \<le> (\<Sum>i<m. norm (z - w))"
    by (intro norm_prod_diff) (auto simp: assms)
  also have "\<dots> = m * norm (z - w)"
    by simp
  finally show ?thesis .
qed


subsection \<open>Metric spaces\<close>

class metric_space = uniformity_dist + open_uniformity +
  assumes dist_eq_0_iff [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
    and dist_triangle2: "dist x y \<le> dist x z + dist y z"
begin

lemma dist_self [simp]: "dist x x = 0"
  by simp

lemma zero_le_dist [simp]: "0 \<le> dist x y"
  using dist_triangle2 [of x x y] by simp

lemma zero_less_dist_iff: "0 < dist x y \<longleftrightarrow> x \<noteq> y"
  by (simp add: less_le)

lemma dist_not_less_zero [simp]: "\<not> dist x y < 0"
  by (simp add: not_less)

lemma dist_le_zero_iff [simp]: "dist x y \<le> 0 \<longleftrightarrow> x = y"
  by (simp add: le_less)

lemma dist_commute: "dist x y = dist y x"
proof (rule order_antisym)
  show "dist x y \<le> dist y x"
    using dist_triangle2 [of x y x] by simp
  show "dist y x \<le> dist x y"
    using dist_triangle2 [of y x y] by simp
qed

lemma dist_commute_lessI: "dist y x < e \<Longrightarrow> dist x y < e"
  by (simp add: dist_commute)

lemma dist_triangle: "dist x z \<le> dist x y + dist y z"
  using dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma dist_triangle3: "dist x y \<le> dist a x + dist a y"
  using dist_triangle2 [of x y a] by (simp add: dist_commute)

lemma abs_dist_diff_le: "\<bar>dist a b - dist b c\<bar> \<le> dist a c"
  using dist_triangle3[of b c a] dist_triangle2[of a b c] by simp

lemma dist_pos_lt: "x \<noteq> y \<Longrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

lemma dist_nz: "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

declare dist_nz [symmetric, simp]

lemma dist_triangle_le: "dist x z + dist y z \<le> e \<Longrightarrow> dist x y \<le> e"
  by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt: "dist x z + dist y z < e \<Longrightarrow> dist x y < e"
  by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_less_add: "dist x1 y < e1 \<Longrightarrow> dist x2 y < e2 \<Longrightarrow> dist x1 x2 < e1 + e2"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_l: "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_r: "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_half_l) (simp_all add: dist_commute)

lemma dist_triangle_third:
  assumes "dist x1 x2 < e/3" "dist x2 x3 < e/3" "dist x3 x4 < e/3"
  shows "dist x1 x4 < e"
proof -
  have "dist x1 x3 < e/3 + e/3"
    by (metis assms(1) assms(2) dist_commute dist_triangle_less_add)
  then have "dist x1 x4 < (e/3 + e/3) + e/3"
    by (metis assms(3) dist_commute dist_triangle_less_add)
  then show ?thesis
    by simp
qed
  
subclass uniform_space
proof
  fix E x
  assume "eventually E uniformity"
  then obtain e where E: "0 < e" "\<And>x y. dist x y < e \<Longrightarrow> E (x, y)"
    by (auto simp: eventually_uniformity_metric)
  then show "E (x, x)" "\<forall>\<^sub>F (x, y) in uniformity. E (y, x)"
    by (auto simp: eventually_uniformity_metric dist_commute)
  show "\<exists>D. eventually D uniformity \<and> (\<forall>x y z. D (x, y) \<longrightarrow> D (y, z) \<longrightarrow> E (x, z))"
    using E dist_triangle_half_l[where e=e]
    unfolding eventually_uniformity_metric
    by (intro exI[of _ "\<lambda>(x, y). dist x y < e / 2"] exI[of _ "e/2"] conjI)
      (auto simp: dist_commute)
qed

lemma open_dist: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  by (simp add: dist_commute open_uniformity eventually_uniformity_metric)

lemma open_ball: "open {y. dist x y < d}"
  unfolding open_dist
proof (intro ballI)
  fix y
  assume *: "y \<in> {y. dist x y < d}"
  then show "\<exists>e>0. \<forall>z. dist z y < e \<longrightarrow> z \<in> {y. dist x y < d}"
    by (auto intro!: exI[of _ "d - dist x y"] simp: field_simps dist_triangle_lt)
qed

subclass first_countable_topology
proof
  fix x
  show "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (safe intro!: exI[of _ "\<lambda>n. {y. dist x y < inverse (Suc n)}"])
    fix S
    assume "open S" "x \<in> S"
    then obtain e where e: "0 < e" and "{y. dist x y < e} \<subseteq> S"
      by (auto simp: open_dist subset_eq dist_commute)
    moreover
    from e obtain i where "inverse (Suc i) < e"
      by (auto dest!: reals_Archimedean)
    then have "{y. dist x y < inverse (Suc i)} \<subseteq> {y. dist x y < e}"
      by auto
    ultimately show "\<exists>i. {y. dist x y < inverse (Suc i)} \<subseteq> S"
      by blast
  qed (auto intro: open_ball)
qed

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "{y'. dist x y' < dist x y / 2}"
  let ?V = "{x'. dist y x' < dist x y / 2}"
  have *: "d x z \<le> d x y + d y z \<Longrightarrow> d y z = d z y \<Longrightarrow> \<not> (d x y * 2 < d x z \<and> d z y * 2 < d x z)"
    for d :: "'a \<Rightarrow> 'a \<Rightarrow> real" and x y z :: 'a
    by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] *[of dist, OF dist_triangle dist_commute]
    using open_ball[of _ "dist x y / 2"] by auto
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

text \<open>Every normed vector space is a metric space.\<close>
instance real_normed_vector < metric_space
proof
  fix x y z :: 'a
  show "dist x y = 0 \<longleftrightarrow> x = y"
    by (simp add: dist_norm)
  show "dist x y \<le> dist x z + dist y z"
    using norm_triangle_ineq4 [of "x - z" "y - z"] by (simp add: dist_norm)
qed


subsection \<open>Class instances for real numbers\<close>

instantiation real :: real_normed_field
begin

definition dist_real_def: "dist x y = \<bar>x - y\<bar>"

definition uniformity_real_def [code del]:
  "(uniformity :: (real \<times> real) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_real_def [code del]:
  "open (U :: real set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

definition real_norm_def [simp]: "norm r = \<bar>r\<bar>"

instance
  by intro_classes (auto simp: abs_mult open_real_def dist_real_def sgn_real_def uniformity_real_def)

end

declare uniformity_Abort[where 'a=real, code]

lemma dist_of_real [simp]: "dist (of_real x :: 'a) (of_real y) = dist x y"
  for a :: "'a::real_normed_div_algebra"
  by (metis dist_norm norm_of_real of_real_diff real_norm_def)

declare [[code abort: "open :: real set \<Rightarrow> bool"]]

instance real :: linorder_topology
proof
  show "(open :: real set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"
  proof (rule ext, safe)
    fix S :: "real set"
    assume "open S"
    then obtain f where "\<forall>x\<in>S. 0 < f x \<and> (\<forall>y. dist y x < f x \<longrightarrow> y \<in> S)"
      unfolding open_dist bchoice_iff ..
    then have *: "(\<Union>x\<in>S. {x - f x <..} \<inter> {..< x + f x}) = S" (is "?S = S")
      by (fastforce simp: dist_real_def)
    moreover have "generate_topology (range lessThan \<union> range greaterThan) ?S"
      by (force intro: generate_topology.Basis generate_topology_Union generate_topology.Int)
    ultimately show "generate_topology (range lessThan \<union> range greaterThan) S"
      by simp
  next
    fix S :: "real set"
    assume "generate_topology (range lessThan \<union> range greaterThan) S"
    moreover have "\<And>a::real. open {..<a}"
      unfolding open_dist dist_real_def
    proof clarify
      fix x a :: real
      assume "x < a"
      then have "0 < a - x \<and> (\<forall>y. \<bar>y - x\<bar> < a - x \<longrightarrow> y \<in> {..<a})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {..<a}" ..
    qed
    moreover have "\<And>a::real. open {a <..}"
      unfolding open_dist dist_real_def
    proof clarify
      fix x a :: real
      assume "a < x"
      then have "0 < x - a \<and> (\<forall>y. \<bar>y - x\<bar> < x - a \<longrightarrow> y \<in> {a<..})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {a<..}" ..
    qed
    ultimately show "open S"
      by induct auto
  qed
qed

instance real :: linear_continuum_topology ..

lemmas open_real_greaterThan = open_greaterThan[where 'a=real]
lemmas open_real_lessThan = open_lessThan[where 'a=real]
lemmas open_real_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_real_atMost = closed_atMost[where 'a=real]
lemmas closed_real_atLeast = closed_atLeast[where 'a=real]
lemmas closed_real_atLeastAtMost = closed_atLeastAtMost[where 'a=real]

instance real :: ordered_real_vector
  by standard (auto intro: mult_left_mono mult_right_mono)


subsection \<open>Extra type constraints\<close>

text \<open>Only allow \<^term>\<open>open\<close> in class \<open>topological_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

text \<open>Only allow \<^term>\<open>uniformity\<close> in class \<open>uniform_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

text \<open>Only allow \<^term>\<open>dist\<close> in class \<open>metric_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

text \<open>Only allow \<^term>\<open>norm\<close> in class \<open>real_normed_vector\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>


subsection \<open>Sign function\<close>

lemma norm_sgn: "norm (sgn x) = (if x = 0 then 0 else 1)"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_zero [simp]: "sgn (0::'a::real_normed_vector) = 0"
  by (simp add: sgn_div_norm)

lemma sgn_zero_iff: "sgn x = 0 \<longleftrightarrow> x = 0"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_minus: "sgn (- x) = - sgn x"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_scaleR: "sgn (scaleR r x) = scaleR (sgn r) (sgn x)"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm ac_simps)

lemma sgn_one [simp]: "sgn (1::'a::real_normed_algebra_1) = 1"
  by (simp add: sgn_div_norm)

lemma sgn_of_real: "sgn (of_real r :: 'a::real_normed_algebra_1) = of_real (sgn r)"
  unfolding of_real_def by (simp only: sgn_scaleR sgn_one)

lemma sgn_mult: "sgn (x * y) = sgn x * sgn y"
  for x y :: "'a::real_normed_div_algebra"
  by (simp add: sgn_div_norm norm_mult)

hide_fact (open) sgn_mult

lemma real_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: real
  by (simp add: sgn_div_norm divide_inverse)

lemma zero_le_sgn_iff [simp]: "0 \<le> sgn x \<longleftrightarrow> 0 \<le> x"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma sgn_le_0_iff [simp]: "sgn x \<le> 0 \<longleftrightarrow> x \<le> 0"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

declare norm_conv_dist [symmetric, simp]

lemma dist_0_norm [simp]: "dist 0 x = norm x"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma dist_diff [simp]: "dist a (a - b) = norm b"  "dist (a - b) a = norm b"
  by (simp_all add: dist_norm)

lemma dist_of_int: "dist (of_int m) (of_int n :: 'a :: real_normed_algebra_1) = of_int \<bar>m - n\<bar>"
proof -
  have "dist (of_int m) (of_int n :: 'a) = dist (of_int m :: 'a) (of_int m - (of_int (m - n)))"
    by simp
  also have "\<dots> = of_int \<bar>m - n\<bar>" by (subst dist_diff, subst norm_of_int) simp
  finally show ?thesis .
qed

lemma dist_of_nat:
  "dist (of_nat m) (of_nat n :: 'a :: real_normed_algebra_1) = of_int \<bar>int m - int n\<bar>"
  by (subst (1 2) of_int_of_nat_eq [symmetric]) (rule dist_of_int)


subsection \<open>Bounded Linear and Bilinear Operators\<close>

lemma linearI: "linear f"
  if "\<And>b1 b2. f (b1 + b2) = f b1 + f b2"
    "\<And>r b. f (r *\<^sub>R b) = r *\<^sub>R f b"
  using that
  by unfold_locales (auto simp: algebra_simps)

lemma linear_iff:
  "linear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>R x) = c *\<^sub>R f x)"
  (is "linear f \<longleftrightarrow> ?rhs")
proof
  assume "linear f"
  then interpret f: linear f .
  show "?rhs" by (simp add: f.add f.scale)
next
  assume "?rhs"
  then show "linear f" by (intro linearI) auto
qed

lemmas linear_scaleR_left = linear_scale_left
lemmas linear_imp_scaleR = linear_imp_scale

corollary real_linearD:
  fixes f :: "real \<Rightarrow> real"
  assumes "linear f" obtains c where "f = (*) c"
  by (rule linear_imp_scaleR [OF assms]) (force simp: scaleR_conv_of_real)

lemma linear_times_of_real: "linear (\<lambda>x. a * of_real x)"
  by (auto intro!: linearI simp: distrib_left)
    (metis mult_scaleR_right scaleR_conv_of_real)

locale bounded_linear = linear f for f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by blast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma linear: "linear f"
  by (fact local.linear_axioms)

end

lemma bounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleR r x) = scaleR r (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  by standard (blast intro: assms)+

locale bounded_bilinear =
  fixes prod :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleR_left: "prod (scaleR r a) b = scaleR r (prod a b)"
    and scaleR_right: "prod a (scaleR r b) = scaleR r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using bounded by blast
  then have "norm (a ** b) \<le> norm a * norm b * (max 1 K)" for a b
    by (rule order.trans) (simp add: mult_left_mono)
  then show ?thesis
    by force
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma additive_right: "additive (\<lambda>b. prod a b)"
  by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. prod a b)"
  by (rule additive.intro, rule add_left)

lemma zero_left: "prod 0 b = 0"
  by (rule additive.zero [OF additive_left])

lemma zero_right: "prod a 0 = 0"
  by (rule additive.zero [OF additive_right])

lemma minus_left: "prod (- a) b = - prod a b"
  by (rule additive.minus [OF additive_left])

lemma minus_right: "prod a (- b) = - prod a b"
  by (rule additive.minus [OF additive_right])

lemma diff_left: "prod (a - a') b = prod a b - prod a' b"
  by (rule additive.diff [OF additive_left])

lemma diff_right: "prod a (b - b') = prod a b - prod a b'"
  by (rule additive.diff [OF additive_right])

lemma sum_left: "prod (sum g S) x = sum ((\<lambda>i. prod (g i) x)) S"
  by (rule additive.sum [OF additive_left])

lemma sum_right: "prod x (sum g S) = sum ((\<lambda>i. (prod x (g i)))) S"
  by (rule additive.sum [OF additive_right])


lemma bounded_linear_left: "bounded_linear (\<lambda>a. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm b * K" in bounded_linear_intro) (auto simp: algebra_simps scaleR_left add_left)
qed

lemma bounded_linear_right: "bounded_linear (\<lambda>b. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm a * K" in bounded_linear_intro) (auto simp: algebra_simps scaleR_right add_right)
qed

lemma prod_diff_prod: "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
  by (simp add: diff_left diff_right)

lemma flip: "bounded_bilinear (\<lambda>x y. y ** x)"
proof
  show "\<exists>K. \<forall>a b. norm (b ** a) \<le> norm a * norm b * K"
    by (metis bounded mult.commute)
qed (simp_all add: add_right add_left scaleR_right scaleR_left)

lemma comp1:
  assumes "bounded_linear g"
  shows "bounded_bilinear (\<lambda>x. (**) (g x))"
proof unfold_locales
  interpret g: bounded_linear g by fact
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>R a) ** b = r *\<^sub>R (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>R b) = r *\<^sub>R (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleR scaleR_left scaleR_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a ** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  then show "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_bilinear (\<lambda>x y. f x ** g y)"
  by (rule bounded_bilinear.flip[OF bounded_bilinear.comp1[OF bounded_bilinear.flip[OF comp1]]])

end

lemma bounded_linear_ident[simp]: "bounded_linear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_zero[simp]: "bounded_linear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_add:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
      by blast
    from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
      by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleR g.scaleR scaleR_right_distrib)
qed

lemma bounded_linear_minus:
  assumes "bounded_linear f"
  shows "bounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scaleR f.bounded)
qed

lemma bounded_linear_sub: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_linear (\<lambda>x. f x - g x)"
  using bounded_linear_add[of f "\<lambda>x. - g x"] bounded_linear_minus[of g]
  by (auto simp: algebra_simps)

lemma bounded_linear_sum:
  fixes f :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_linear (f i)) \<Longrightarrow> bounded_linear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_linear_add)

lemma bounded_linear_compose:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleR r x)) = scaleR r (f (g x))" for r x
      by (simp only: f.scaleR g.scaleR)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_bilinear_mult: "bounded_bilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::real_normed_algebra)"
proof (rule bounded_bilinear.intro)
  show "\<exists>K. \<forall>a b::'a. norm (a * b) \<le> norm a * norm b * K"
    by (rule_tac x=1 in exI) (simp add: norm_mult_ineq)
qed (auto simp: algebra_simps)

lemma bounded_linear_mult_left: "bounded_linear (\<lambda>x::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_mult_right: "bounded_linear (\<lambda>y::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_linear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma bounded_linear_divide: "bounded_linear (\<lambda>x. x / y)"
  for y :: "'a::real_normed_field"
  unfolding divide_inverse by (rule bounded_linear_mult_left)

lemma bounded_bilinear_scaleR: "bounded_bilinear scaleR"
proof (rule bounded_bilinear.intro)
  show "\<exists>K. \<forall>a b. norm (a *\<^sub>R b) \<le> norm a * norm b * K"
    using less_eq_real_def by auto
qed (auto simp: algebra_simps)

lemma bounded_linear_scaleR_left: "bounded_linear (\<lambda>r. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_scaleR_right: "bounded_linear (\<lambda>x. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_scaleR_const =
  bounded_linear_scaleR_left[THEN bounded_linear_compose]

lemmas bounded_linear_const_scaleR =
  bounded_linear_scaleR_right[THEN bounded_linear_compose]

lemma bounded_linear_of_real: "bounded_linear (\<lambda>r. of_real r)"
  unfolding of_real_def by (rule bounded_linear_scaleR_left)

lemma real_bounded_linear: "bounded_linear f \<longleftrightarrow> (\<exists>c::real. f = (\<lambda>x. x * c))"
  for f :: "real \<Rightarrow> real"
proof -
  {
    fix x
    assume "bounded_linear f"
    then interpret bounded_linear f .
    from scaleR[of x 1] have "f x = x * f 1"
      by simp
  }
  then show ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_linear_mult_left)
qed

instance real_normed_algebra_1 \<subseteq> perfect_space
proof
  fix x::'a
  have "\<And>e. 0 < e \<Longrightarrow> \<exists>y. norm (y - x) < e \<and> y \<noteq> x"
    by (rule_tac x = "x + of_real (e/2)" in exI) auto
  then show "\<not> open {x}" 
    by (clarsimp simp: open_dist dist_norm)
qed


subsection \<open>Filters and Limits on Metric Space\<close>

lemma (in metric_space) nhds_metric: "nhds x = (INF e\<in>{0 <..}. principal {y. dist y x < e})"
  unfolding nhds_def
proof (safe intro!: INF_eq)
  fix S
  assume "open S" "x \<in> S"
  then obtain e where "{y. dist y x < e} \<subseteq> S" "0 < e"
    by (auto simp: open_dist subset_eq)
  then show "\<exists>e\<in>{0<..}. principal {y. dist y x < e} \<le> principal S"
    by auto
qed (auto intro!: exI[of _ "{y. dist x y < e}" for e] open_ball simp: dist_commute)

lemma (in metric_space) tendsto_iff: "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  unfolding nhds_metric filterlim_INF filterlim_principal by auto

lemma tendsto_dist_iff:
  "((f \<longlongrightarrow> l) F) \<longleftrightarrow> (((\<lambda>x. dist (f x) l) \<longlongrightarrow> 0) F)"
  unfolding tendsto_iff by simp

lemma (in metric_space) tendstoI [intro?]:
  "(\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F) \<Longrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) tendstoD: "(f \<longlongrightarrow> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) eventually_nhds_metric:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
  unfolding nhds_metric
  by (subst eventually_INF_base)
     (auto simp: eventually_principal Bex_def subset_eq intro: exI[of _ "min a b" for a b])

lemma eventually_at: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
  for a :: "'a :: metric_space"
  by (auto simp: eventually_at_filter eventually_nhds_metric)

lemma frequently_at: "frequently P (at a within S) \<longleftrightarrow> (\<forall>d>0. \<exists>x\<in>S. x \<noteq> a \<and> dist x a < d \<and> P x)"
  for a :: "'a :: metric_space"
  unfolding frequently_def eventually_at by auto

lemma eventually_at_le: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a \<le> d \<longrightarrow> P x)"
  for a :: "'a::metric_space"
  unfolding eventually_at_filter eventually_nhds_metric
  apply safe
  apply (rule_tac x="d / 2" in exI, auto)
  done

lemma eventually_at_left_real: "a > (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_left a)"
  by (subst eventually_at, rule exI[of _ "a - b"]) (force simp: dist_real_def)

lemma eventually_at_right_real: "a < (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {a<..<b}) (at_right a)"
  by (subst eventually_at, rule exI[of _ "b - a"]) (force simp: dist_real_def)

lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space"
    and b :: "'b :: metric_space"
  assumes f: "(f \<longlongrightarrow> a) F"
    and le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g \<longlongrightarrow> b) F"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

lemma filterlim_real_sequentially: "LIM x sequentially. real x :> at_top"
proof (clarsimp simp: filterlim_at_top)
  fix Z
  show "\<forall>\<^sub>F x in sequentially. Z \<le> real x"
    by (meson eventually_sequentiallyI nat_ceiling_le_eq)
qed

lemma filterlim_nat_sequentially: "filterlim nat sequentially at_top"
proof -
  have "\<forall>\<^sub>F x in at_top. Z \<le> nat x" for Z
    by (auto intro!: eventually_at_top_linorderI[where c="int Z"])
  then show ?thesis
    unfolding filterlim_at_top ..
qed

lemma filterlim_floor_sequentially: "filterlim floor at_top at_top"
proof -
  have "\<forall>\<^sub>F x in at_top. Z \<le> \<lfloor>x\<rfloor>" for Z
    by (auto simp: le_floor_iff intro!: eventually_at_top_linorderI[where c="of_int Z"])
  then show ?thesis
    unfolding filterlim_at_top ..
qed

lemma filterlim_sequentially_iff_filterlim_real:
  "filterlim f sequentially F \<longleftrightarrow> filterlim (\<lambda>x. real (f x)) at_top F" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using filterlim_compose filterlim_real_sequentially by blast
next
  assume R: ?rhs
  show ?lhs
  proof -
    have "filterlim (\<lambda>x. nat (floor (real (f x)))) sequentially F"
      by (intro filterlim_compose[OF filterlim_nat_sequentially]
          filterlim_compose[OF filterlim_floor_sequentially] R)
    then show ?thesis by simp
  qed
qed


subsubsection \<open>Limits of Sequences\<close>

lemma lim_sequentially: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding tendsto_iff eventually_sequentially ..

lemmas LIMSEQ_def = lim_sequentially  (*legacy binding*)

lemma LIMSEQ_iff_nz: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding lim_sequentially by (metis Suc_leD zero_less_Suc)

lemma metric_LIMSEQ_I: "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X \<longlonglongrightarrow> L"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)

lemma metric_LIMSEQ_D: "X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)

lemma LIMSEQ_norm_0:
  assumes  "\<And>n::nat. norm (f n) < 1 / real (Suc n)"
  shows "f \<longlonglongrightarrow> 0"
proof (rule metric_LIMSEQ_I)
  fix \<epsilon> :: "real"
  assume "\<epsilon> > 0"
  then obtain N::nat where "\<epsilon> > inverse N" "N > 0"
    by (metis neq0_conv real_arch_inverse)
  then have "norm (f n) < \<epsilon>" if "n \<ge> N" for n
  proof -
    have "1 / (Suc n) \<le> 1 / N"
      using \<open>0 < N\<close> inverse_of_nat_le le_SucI that by blast
    also have "\<dots> < \<epsilon>"
      by (metis (no_types) \<open>inverse (real N) < \<epsilon>\<close> inverse_eq_divide)
    finally show ?thesis
      by (meson assms less_eq_real_def not_le order_trans)
  qed
  then show "\<exists>no. \<forall>n\<ge>no. dist (f n) 0 < \<epsilon>"
    by auto
qed


subsubsection \<open>Limits of Functions\<close>

lemma LIM_def: "f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  unfolding tendsto_iff eventually_at by simp

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r) \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_D: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_imp_LIM:
  fixes l :: "'a::metric_space"
    and m :: "'b::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> l"
    and le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g \<midarrow>a\<rightarrow> m"
  by (rule metric_tendsto_imp_tendsto [OF f]) (auto simp: eventually_at_topological le)

lemma metric_LIM_equal2:
  fixes a :: "'a::metric_space"
  assumes "g \<midarrow>a\<rightarrow> l" "0 < R"
    and "\<And>x. x \<noteq> a \<Longrightarrow> dist x a < R \<Longrightarrow> f x = g x"
  shows "f \<midarrow>a\<rightarrow> l"
proof -
  have "\<And>S. \<lbrakk>open S; l \<in> S; \<forall>\<^sub>F x in at a. g x \<in> S\<rbrakk> \<Longrightarrow> \<forall>\<^sub>F x in at a. f x \<in> S"
    apply (simp add: eventually_at)
    by (metis assms(2) assms(3) dual_order.strict_trans linorder_neqE_linordered_idom)
  then show ?thesis
    using assms by (simp add: tendsto_def)
qed

lemma metric_LIM_compose2:
  fixes a :: "'a::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> b"
    and g: "g \<midarrow>b\<rightarrow> c"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c"
  using inj by (intro tendsto_compose_eventually[OF g f]) (auto simp: eventually_at)

lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
    and g: "g \<midarrow>f a\<rightarrow> l"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> l"
  by (rule metric_LIM_compose2 [OF f g inj])


subsection \<open>Complete metric spaces\<close>

subsection \<open>Cauchy sequences\<close>

lemma (in metric_space) Cauchy_def: "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
proof -
  have *: "eventually P (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<longleftrightarrow>
    (\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. P (X m, X n))" for P
    apply (subst eventually_INF_base)
    subgoal by simp
    subgoal for a b
      by (intro bexI[of _ "max a b"]) (auto simp: eventually_principal subset_eq)
    subgoal by (auto simp: eventually_principal, blast)
    done
  have "Cauchy X \<longleftrightarrow> (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<le> uniformity"
    unfolding Cauchy_uniform_iff le_filter_def * ..
  also have "\<dots> = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
    unfolding uniformity_dist le_INF_iff by (auto simp: * le_principal)
  finally show ?thesis .
qed

lemma (in metric_space) Cauchy_altdef: "Cauchy f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  show ?lhs
    unfolding Cauchy_def
  proof (intro allI impI)
    fix e :: real assume e: "e > 0"
    with \<open>?rhs\<close> obtain M where M: "m \<ge> M \<Longrightarrow> n > m \<Longrightarrow> dist (f m) (f n) < e" for m n
      by blast
    have "dist (f m) (f n) < e" if "m \<ge> M" "n \<ge> M" for m n
      using M[of m n] M[of n m] e that by (cases m n rule: linorder_cases) (auto simp: dist_commute)
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e"
      by blast
  qed
next
  assume ?lhs
  show ?rhs
  proof (intro allI impI)
    fix e :: real
    assume e: "e > 0"
    with \<open>Cauchy f\<close> obtain M where "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> dist (f m) (f n) < e"
      unfolding Cauchy_def by blast
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e"
      by (intro exI[of _ M]) force
  qed
qed

lemma (in metric_space) Cauchy_altdef2: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. dist(s n)(s N) < e)" (is "?lhs = ?rhs")
proof 
  assume "Cauchy s"
  then show ?rhs by (force simp: Cauchy_def)
next
    assume ?rhs
    {
      fix e::real
      assume "e>0"
      with \<open>?rhs\<close> obtain N where N: "\<forall>n\<ge>N. dist (s n) (s N) < e/2"
        by (erule_tac x="e/2" in allE) auto
      {
        fix n m
        assume nm: "N \<le> m \<and> N \<le> n"
        then have "dist (s m) (s n) < e" using N
          using dist_triangle_half_l[of "s m" "s N" "e" "s n"]
          by blast
      }
      then have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < e"
        by blast
    }
    then have ?lhs
      unfolding Cauchy_def by blast
  then show ?lhs
    by blast
qed

lemma (in metric_space) metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  by (simp add: Cauchy_def)

lemma (in metric_space) CauchyI':
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  unfolding Cauchy_altdef by blast

lemma (in metric_space) metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
  by (simp add: Cauchy_def)

lemma (in metric_space) metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))"
  apply (auto simp add: Cauchy_def)
  by (metis less_trans of_nat_Suc reals_Archimedean)

lemma Cauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_real_def)

lemma lim_1_over_n [tendsto_intros]: "((\<lambda>n. 1 / of_nat n) \<longlongrightarrow> (0::'a::real_normed_field)) sequentially"
proof (subst lim_sequentially, intro allI impI exI)
  fix e::real and n
  assume e: "e > 0" 
  have "inverse e < of_nat (nat \<lceil>inverse e + 1\<rceil>)" by linarith
  also assume "n \<ge> nat \<lceil>inverse e + 1\<rceil>"
  finally show "dist (1 / of_nat n :: 'a) 0 < e"
    using e by (simp add: field_split_simps norm_divide)
qed

lemma (in metric_space) complete_def:
  shows "complete S = (\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l))"
  unfolding complete_uniform
proof safe
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> S" "Cauchy f"
    and *: "\<forall>F\<le>principal S. F \<noteq> bot \<longrightarrow> cauchy_filter F \<longrightarrow> (\<exists>x\<in>S. F \<le> nhds x)"
  then show "\<exists>l\<in>S. f \<longlonglongrightarrow> l"
    unfolding filterlim_def using f
    by (intro *[rule_format])
       (auto simp: filtermap_sequentually_ne_bot le_principal eventually_filtermap Cauchy_uniform)
next
  fix F :: "'a filter"
  assume "F \<le> principal S" "F \<noteq> bot" "cauchy_filter F"
  assume seq: "\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l)"

  from \<open>F \<le> principal S\<close> \<open>cauchy_filter F\<close>
  have FF_le: "F \<times>\<^sub>F F \<le> uniformity_on S"
    by (simp add: cauchy_filter_def principal_prod_principal[symmetric] prod_filter_mono)

  let ?P = "\<lambda>P e. eventually P F \<and> (\<forall>x. P x \<longrightarrow> x \<in> S) \<and> (\<forall>x y. P x \<longrightarrow> P y \<longrightarrow> dist x y < e)"
  have P: "\<exists>P. ?P P \<epsilon>" if "0 < \<epsilon>" for \<epsilon> :: real
  proof -
    from that have "eventually (\<lambda>(x, y). x \<in> S \<and> y \<in> S \<and> dist x y < \<epsilon>) (uniformity_on S)"
      by (auto simp: eventually_inf_principal eventually_uniformity_metric)
    from filter_leD[OF FF_le this] show ?thesis
      by (auto simp: eventually_prod_same)
  qed

  have "\<exists>P. \<forall>n. ?P (P n) (1 / Suc n) \<and> P (Suc n) \<le> P n"
  proof (rule dependent_nat_choice)
    show "\<exists>P. ?P P (1 / Suc 0)"
      using P[of 1] by auto
  next
    fix P n assume "?P P (1/Suc n)"
    moreover obtain Q where "?P Q (1 / Suc (Suc n))"
      using P[of "1/Suc (Suc n)"] by auto
    ultimately show "\<exists>Q. ?P Q (1 / Suc (Suc n)) \<and> Q \<le> P"
      by (intro exI[of _ "\<lambda>x. P x \<and> Q x"]) (auto simp: eventually_conj_iff)
  qed
  then obtain P where P: "eventually (P n) F" "P n x \<Longrightarrow> x \<in> S"
    "P n x \<Longrightarrow> P n y \<Longrightarrow> dist x y < 1 / Suc n" "P (Suc n) \<le> P n"
    for n x y
    by metis
  have "antimono P"
    using P(4) unfolding decseq_Suc_iff le_fun_def by blast

  obtain X where X: "P n (X n)" for n
    using P(1)[THEN eventually_happens'[OF \<open>F \<noteq> bot\<close>]] by metis
  have "Cauchy X"
    unfolding metric_Cauchy_iff2 inverse_eq_divide
  proof (intro exI allI impI)
    fix j m n :: nat
    assume "j \<le> m" "j \<le> n"
    with \<open>antimono P\<close> X have "P j (X m)" "P j (X n)"
      by (auto simp: antimono_def)
    then show "dist (X m) (X n) < 1 / Suc j"
      by (rule P)
  qed
  moreover have "\<forall>n. X n \<in> S"
    using P(2) X by auto
  ultimately obtain x where "X \<longlonglongrightarrow> x" "x \<in> S"
    using seq by blast

  show "\<exists>x\<in>S. F \<le> nhds x"
  proof (rule bexI)
    have "eventually (\<lambda>y. dist y x < e) F" if "0 < e" for e :: real
    proof -
      from that have "(\<lambda>n. 1 / Suc n :: real) \<longlonglongrightarrow> 0 \<and> 0 < e / 2"
        by (subst filterlim_sequentially_Suc) (auto intro!: lim_1_over_n)
      then have "\<forall>\<^sub>F n in sequentially. dist (X n) x < e / 2 \<and> 1 / Suc n < e / 2"
        using \<open>X \<longlonglongrightarrow> x\<close>
        unfolding tendsto_iff order_tendsto_iff[where 'a=real] eventually_conj_iff
        by blast
      then obtain n where "dist x (X n) < e / 2" "1 / Suc n < e / 2"
        by (auto simp: eventually_sequentially dist_commute)
      show ?thesis
        using \<open>eventually (P n) F\<close>
      proof eventually_elim
        case (elim y)
        then have "dist y (X n) < 1 / Suc n"
          by (intro X P)
        also have "\<dots> < e / 2" by fact
        finally show "dist y x < e"
          by (rule dist_triangle_half_l) fact
      qed
    qed
    then show "F \<le> nhds x"
      unfolding nhds_metric le_INF_iff le_principal by auto
  qed fact
qed

text\<open>apparently unused\<close>
lemma (in metric_space) totally_bounded_metric:
  "totally_bounded S \<longleftrightarrow> (\<forall>e>0. \<exists>k. finite k \<and> S \<subseteq> (\<Union>x\<in>k. {y. dist x y < e}))"
  unfolding totally_bounded_def eventually_uniformity_metric imp_ex
  apply (subst all_comm)
  apply (intro arg_cong[where f=All] ext, safe)
  subgoal for e
    apply (erule allE[of _ "\<lambda>(x, y). dist x y < e"])
    apply auto
    done
  subgoal for e P k
    apply (intro exI[of _ k])
    apply (force simp: subset_eq)
    done
  done


subsubsection \<open>Cauchy Sequences are Convergent\<close>

(* TODO: update to uniform_space *)
class complete_space = metric_space +
  assumes Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

lemma Cauchy_convergent_iff: "Cauchy X \<longleftrightarrow> convergent X"
  for X :: "nat \<Rightarrow> 'a::complete_space"
  by (blast intro: Cauchy_convergent convergent_Cauchy)

text \<open>To prove that a Cauchy sequence converges, it suffices to show that a subsequence converges.\<close>

lemma Cauchy_converges_subseq:
  fixes u::"nat \<Rightarrow> 'a::metric_space"
  assumes "Cauchy u"
    "strict_mono r"
    "(u \<circ> r) \<longlonglongrightarrow> l"
  shows "u \<longlonglongrightarrow> l"
proof -
  have *: "eventually (\<lambda>n. dist (u n) l < e) sequentially" if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
    then obtain N1 where N1: "\<And>m n. m \<ge> N1 \<Longrightarrow> n \<ge> N1 \<Longrightarrow> dist (u m) (u n) < e/2"
      using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
    obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> dist ((u \<circ> r) n) l < e / 2"
      using order_tendstoD(2)[OF iffD1[OF tendsto_dist_iff \<open>(u \<circ> r) \<longlonglongrightarrow> l\<close>] \<open>e/2 > 0\<close>]
      unfolding eventually_sequentially by auto
    have "dist (u n) l < e" if "n \<ge> max N1 N2" for n
    proof -
      have "dist (u n) l \<le> dist (u n) ((u \<circ> r) n) + dist ((u \<circ> r) n) l"
        by (rule dist_triangle)
      also have "\<dots> < e/2 + e/2"
      proof (intro add_strict_mono)
        show "dist (u n) ((u \<circ> r) n) < e / 2"
          using N1[of n "r n"] N2[of n] that unfolding comp_def
          by (meson assms(2) le_trans max.bounded_iff strict_mono_imp_increasing)
        show "dist ((u \<circ> r) n) l < e / 2"
          using N2 that by auto
      qed
      finally show ?thesis by simp
    qed 
    then show ?thesis unfolding eventually_sequentially by blast
  qed
  have "(\<lambda>n. dist (u n) l) \<longlonglongrightarrow> 0"
    by (simp add: less_le_trans * order_tendstoI)
  then show ?thesis using tendsto_dist_iff by auto
qed

subsection \<open>The set of real numbers is a complete metric space\<close>

text \<open>
  Proof that Cauchy sequences converge based on the one from
  \<^url>\<open>http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html\<close>
\<close>

text \<open>
  If sequence \<^term>\<open>X\<close> is Cauchy, then its limit is the lub of
  \<^term>\<open>{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}\<close>
\<close>
lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
    and bdd: "\<And>n. f n \<le> l"
    and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f \<longlonglongrightarrow> l"
proof (rule increasing_tendsto)
  fix x
  assume "x < l"
  with dense[of 0 "l - x"] obtain e where "0 < e" "e < l - x"
    by auto
  from en[OF \<open>0 < e\<close>] obtain n where "l - e \<le> f n"
    by (auto simp: field_simps)
  with \<open>e < l - x\<close> \<open>0 < e\<close> have "x < f n"
    by simp
  with incseq_SucI[of f, OF inc] show "eventually (\<lambda>n. x < f n) sequentially"
    by (auto simp: eventually_sequentially incseq_def intro: less_le_trans)
qed (use bdd in auto)

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  shows "convergent X"
proof -
  define S :: "real set" where "S = {x. \<exists>N. \<forall>n\<ge>N. x < X n}"
  then have mem_S: "\<And>N x. \<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S"
    by auto

  have bound_isUb: "y \<le> x" if N: "\<forall>n\<ge>N. X n < x" and "y \<in> S" for N and x y :: real
  proof -
    from that have "\<exists>M. \<forall>n\<ge>M. y < X n"
      by (simp add: S_def)
    then obtain M where "\<forall>n\<ge>M. y < X n" ..
    then have "y < X (max M N)" by simp
    also have "\<dots> < x" using N by simp
    finally show ?thesis by (rule order_less_imp_le)
  qed

  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < 1"
    using X[THEN metric_CauchyD, OF zero_less_one] by auto
  then have N: "\<forall>n\<ge>N. dist (X n) (X N) < 1" by simp
  have [simp]: "S \<noteq> {}"
  proof (intro exI ex_in_conv[THEN iffD1])
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff dist_real_def)
    then show "X N - 1 \<in> S" by (rule mem_S)
  qed
  have [simp]: "bdd_above S"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff dist_real_def)
    then show "\<And>s. s \<in> S \<Longrightarrow>  s \<le> X N + 1"
      by (rule bound_isUb)
  qed
  have "X \<longlonglongrightarrow> Sup S"
  proof (rule metric_LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    then have r: "0 < r/2" by simp
    obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (X n) (X m) < r/2"
      using metric_CauchyD [OF X r] by auto
    then have "\<forall>n\<ge>N. dist (X n) (X N) < r/2" by simp
    then have N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
      by (simp only: dist_real_def abs_diff_less_iff)

    from N have "\<forall>n\<ge>N. X N - r/2 < X n" by blast
    then have "X N - r/2 \<in> S" by (rule mem_S)
    then have 1: "X N - r/2 \<le> Sup S" by (simp add: cSup_upper)

    from N have "\<forall>n\<ge>N. X n < X N + r/2" by blast
    from bound_isUb[OF this]
    have 2: "Sup S \<le> X N + r/2"
      by (intro cSup_least) simp_all

    show "\<exists>N. \<forall>n\<ge>N. dist (X n) (Sup S) < r"
    proof (intro exI allI impI)
      fix n
      assume n: "N \<le> n"
      from N n have "X n < X N + r/2" and "X N - r/2 < X n"
        by simp_all
      then show "dist (X n) (Sup S) < r" using 1 2
        by (simp add: abs_diff_less_iff dist_real_def)
    qed
  qed
  then show ?thesis by (auto simp: convergent_def)
qed

instance real :: complete_space
  by intro_classes (rule real_Cauchy_convergent)

class banach = real_normed_vector + complete_space

instance real :: banach ..

lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_top sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof -
  obtain A where A: "decseq A" "open (A n)" "y \<in> A n" "nhds y = (INF n. principal (A n))" for n
    by (rule nhds_countable[of y]) (rule that)

  have "\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m"
  proof (rule ccontr)
    assume "\<not> (\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m)"
    then obtain m where "\<And>k. \<exists>x\<ge>k. f x \<notin> A m"
      by auto
    then have "\<exists>X. \<forall>n. (f (X n) \<notin> A m) \<and> max n (X n) + 1 \<le> X (Suc n)"
      by (intro dependent_nat_choice) (auto simp del: max.bounded_iff)
    then obtain X where X: "\<And>n. f (X n) \<notin> A m" "\<And>n. max n (X n) + 1 \<le> X (Suc n)"
      by auto
    have "1 \<le> n \<Longrightarrow> real n \<le> X n" for n
      using X[of "n - 1"] by auto
    then have "filterlim X at_top sequentially"
      by (force intro!: filterlim_at_top_mono[OF filterlim_real_sequentially]
          simp: eventually_sequentially)
    from topological_tendstoD[OF *[OF this] A(2, 3), of m] X(1) show False
      by auto
  qed
  then obtain k where "k m \<le> x \<Longrightarrow> f x \<in> A m" for m x
    by metis
  then show ?thesis
    unfolding at_top_def A by (intro filterlim_base[where i=k]) auto
qed

lemma tendsto_at_topI_sequentially_real:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
    and limseq: "(\<lambda>n. f (real n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with limseq obtain N :: nat where N: "N \<le> n \<Longrightarrow> \<bar>f (real n) - y\<bar> < e" for n
    by (auto simp: lim_sequentially dist_real_def)
  have le: "f x \<le> y" for x :: real
  proof -
    obtain n where "x \<le> real_of_nat n"
      using real_arch_simple[of x] ..
    note monoD[OF mono this]
    also have "f (real_of_nat n) \<le> y"
      by (rule LIMSEQ_le_const[OF limseq]) (auto intro!: exI[of _ n] monoD[OF mono])
    finally show ?thesis .
  qed
  have "eventually (\<lambda>x. real N \<le> x) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>x. dist (f x) y < e) at_top"
  proof eventually_elim
    case (elim x)
    with N[of N] le have "y - f (real N) < e" by auto
    moreover note monoD[OF mono elim]
    ultimately show "dist (f x) y < e"
      using le[of x] by (auto simp: dist_real_def field_simps)
  qed
qed

end

(*  Title:   HOL/Ring_and_Field.thy
    Author:  Gertrud Bauer, Steven Obua, Tobias Nipkow, Lawrence C Paulson, and Markus Wenzel,
             with contributions by Jeremy Avigad
*)

header {* (Ordered) Rings and Fields *}

theory Ring_and_Field
imports OrderedGroup
begin

text {*
  The theory of partially ordered rings is taken from the books:
  \begin{itemize}
  \item \emph{Lattice Theory} by Garret Birkhoff, American Mathematical Society 1979 
  \item \emph{Partially Ordered Algebraic Systems}, Pergamon Press 1963
  \end{itemize}
  Most of the used notions can also be looked up in 
  \begin{itemize}
  \item \url{http://www.mathworld.com} by Eric Weisstein et. al.
  \item \emph{Algebra I} by van der Waerden, Springer.
  \end{itemize}
*}

class semiring = ab_semigroup_add + semigroup_mult +
  assumes left_distrib[algebra_simps]: "(a + b) * c = a * c + b * c"
  assumes right_distrib[algebra_simps]: "a * (b + c) = a * b + a * c"
begin

text{*For the @{text combine_numerals} simproc*}
lemma combine_common_factor:
  "a * e + (b * e + c) = (a + b) * e + c"
by (simp add: left_distrib add_ac)

end

class mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"

class semiring_0 = semiring + comm_monoid_add + mult_zero

class semiring_0_cancel = semiring + cancel_comm_monoid_add
begin

subclass semiring_0
proof
  fix a :: 'a
  have "0 * a + 0 * a = 0 * a + 0" by (simp add: left_distrib [symmetric])
  thus "0 * a = 0" by (simp only: add_left_cancel)
next
  fix a :: 'a
  have "a * 0 + a * 0 = a * 0 + 0" by (simp add: right_distrib [symmetric])
  thus "a * 0 = 0" by (simp only: add_left_cancel)
qed

end

class comm_semiring = ab_semigroup_add + ab_semigroup_mult +
  assumes distrib: "(a + b) * c = a * c + b * c"
begin

subclass semiring
proof
  fix a b c :: 'a
  show "(a + b) * c = a * c + b * c" by (simp add: distrib)
  have "a * (b + c) = (b + c) * a" by (simp add: mult_ac)
  also have "... = b * a + c * a" by (simp only: distrib)
  also have "... = a * b + a * c" by (simp add: mult_ac)
  finally show "a * (b + c) = a * b + a * c" by blast
qed

end

class comm_semiring_0 = comm_semiring + comm_monoid_add + mult_zero
begin

subclass semiring_0 ..

end

class comm_semiring_0_cancel = comm_semiring + cancel_comm_monoid_add
begin

subclass semiring_0_cancel ..

subclass comm_semiring_0 ..

end

class zero_neq_one = zero + one +
  assumes zero_neq_one [simp]: "0 \<noteq> 1"
begin

lemma one_neq_zero [simp]: "1 \<noteq> 0"
by (rule not_sym) (rule zero_neq_one)

end

class semiring_1 = zero_neq_one + semiring_0 + monoid_mult

text {* Abstract divisibility *}

class dvd = times
begin

definition dvd :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "dvd" 50) where
  [code del]: "b dvd a \<longleftrightarrow> (\<exists>k. a = b * k)"

lemma dvdI [intro?]: "a = b * k \<Longrightarrow> b dvd a"
  unfolding dvd_def ..

lemma dvdE [elim?]: "b dvd a \<Longrightarrow> (\<And>k. a = b * k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding dvd_def by blast 

end

class comm_semiring_1 = zero_neq_one + comm_semiring_0 + comm_monoid_mult + dvd
  (*previously almost_semiring*)
begin

subclass semiring_1 ..

lemma dvd_refl[simp]: "a dvd a"
proof
  show "a = a * 1" by simp
qed

lemma dvd_trans:
  assumes "a dvd b" and "b dvd c"
  shows "a dvd c"
proof -
  from assms obtain v where "b = a * v" by (auto elim!: dvdE)
  moreover from assms obtain w where "c = b * w" by (auto elim!: dvdE)
  ultimately have "c = a * (v * w)" by (simp add: mult_assoc)
  then show ?thesis ..
qed

lemma dvd_0_left_iff [noatp, simp]: "0 dvd a \<longleftrightarrow> a = 0"
by (auto intro: dvd_refl elim!: dvdE)

lemma dvd_0_right [iff]: "a dvd 0"
proof
  show "0 = a * 0" by simp
qed

lemma one_dvd [simp]: "1 dvd a"
by (auto intro!: dvdI)

lemma dvd_mult[simp]: "a dvd c \<Longrightarrow> a dvd (b * c)"
by (auto intro!: mult_left_commute dvdI elim!: dvdE)

lemma dvd_mult2[simp]: "a dvd b \<Longrightarrow> a dvd (b * c)"
  apply (subst mult_commute)
  apply (erule dvd_mult)
  done

lemma dvd_triv_right [simp]: "a dvd b * a"
by (rule dvd_mult) (rule dvd_refl)

lemma dvd_triv_left [simp]: "a dvd a * b"
by (rule dvd_mult2) (rule dvd_refl)

lemma mult_dvd_mono:
  assumes "a dvd b"
    and "c dvd d"
  shows "a * c dvd b * d"
proof -
  from `a dvd b` obtain b' where "b = a * b'" ..
  moreover from `c dvd d` obtain d' where "d = c * d'" ..
  ultimately have "b * d = (a * c) * (b' * d')" by (simp add: mult_ac)
  then show ?thesis ..
qed

lemma dvd_mult_left: "a * b dvd c \<Longrightarrow> a dvd c"
by (simp add: dvd_def mult_assoc, blast)

lemma dvd_mult_right: "a * b dvd c \<Longrightarrow> b dvd c"
  unfolding mult_ac [of a] by (rule dvd_mult_left)

lemma dvd_0_left: "0 dvd a \<Longrightarrow> a = 0"
by simp

lemma dvd_add[simp]:
  assumes "a dvd b" and "a dvd c" shows "a dvd (b + c)"
proof -
  from `a dvd b` obtain b' where "b = a * b'" ..
  moreover from `a dvd c` obtain c' where "c = a * c'" ..
  ultimately have "b + c = a * (b' + c')" by (simp add: right_distrib)
  then show ?thesis ..
qed

end


class no_zero_divisors = zero + times +
  assumes no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"

class semiring_1_cancel = semiring + cancel_comm_monoid_add
  + zero_neq_one + monoid_mult
begin

subclass semiring_0_cancel ..

subclass semiring_1 ..

end

class comm_semiring_1_cancel = comm_semiring + cancel_comm_monoid_add
  + zero_neq_one + comm_monoid_mult
begin

subclass semiring_1_cancel ..
subclass comm_semiring_0_cancel ..
subclass comm_semiring_1 ..

end

class ring = semiring + ab_group_add
begin

subclass semiring_0_cancel ..

text {* Distribution rules *}

lemma minus_mult_left: "- (a * b) = - a * b"
by (rule equals_zero_I) (simp add: left_distrib [symmetric]) 

lemma minus_mult_right: "- (a * b) = a * - b"
by (rule equals_zero_I) (simp add: right_distrib [symmetric]) 

text{*Extract signs from products*}
lemmas mult_minus_left [simp, noatp] = minus_mult_left [symmetric]
lemmas mult_minus_right [simp,noatp] = minus_mult_right [symmetric]

lemma minus_mult_minus [simp]: "- a * - b = a * b"
by simp

lemma minus_mult_commute: "- a * b = a * - b"
by simp

lemma right_diff_distrib[algebra_simps]: "a * (b - c) = a * b - a * c"
by (simp add: right_distrib diff_minus)

lemma left_diff_distrib[algebra_simps]: "(a - b) * c = a * c - b * c"
by (simp add: left_distrib diff_minus)

lemmas ring_distribs[noatp] =
  right_distrib left_distrib left_diff_distrib right_diff_distrib

text{*Legacy - use @{text algebra_simps} *}
lemmas ring_simps[noatp] = algebra_simps

lemma eq_add_iff1:
  "a * e + c = b * e + d \<longleftrightarrow> (a - b) * e + c = d"
by (simp add: algebra_simps)

lemma eq_add_iff2:
  "a * e + c = b * e + d \<longleftrightarrow> c = (b - a) * e + d"
by (simp add: algebra_simps)

end

lemmas ring_distribs[noatp] =
  right_distrib left_distrib left_diff_distrib right_diff_distrib

class comm_ring = comm_semiring + ab_group_add
begin

subclass ring ..
subclass comm_semiring_0_cancel ..

end

class ring_1 = ring + zero_neq_one + monoid_mult
begin

subclass semiring_1_cancel ..

end

class comm_ring_1 = comm_ring + zero_neq_one + comm_monoid_mult
  (*previously ring*)
begin

subclass ring_1 ..
subclass comm_semiring_1_cancel ..

lemma dvd_minus_iff [simp]: "x dvd - y \<longleftrightarrow> x dvd y"
proof
  assume "x dvd - y"
  then have "x dvd - 1 * - y" by (rule dvd_mult)
  then show "x dvd y" by simp
next
  assume "x dvd y"
  then have "x dvd - 1 * y" by (rule dvd_mult)
  then show "x dvd - y" by simp
qed

lemma minus_dvd_iff [simp]: "- x dvd y \<longleftrightarrow> x dvd y"
proof
  assume "- x dvd y"
  then obtain k where "y = - x * k" ..
  then have "y = x * - k" by simp
  then show "x dvd y" ..
next
  assume "x dvd y"
  then obtain k where "y = x * k" ..
  then have "y = - x * - k" by simp
  then show "- x dvd y" ..
qed

lemma dvd_diff[simp]: "x dvd y \<Longrightarrow> x dvd z \<Longrightarrow> x dvd (y - z)"
by (simp add: diff_minus dvd_minus_iff)

end

class ring_no_zero_divisors = ring + no_zero_divisors
begin

lemma mult_eq_0_iff [simp]:
  shows "a * b = 0 \<longleftrightarrow> (a = 0 \<or> b = 0)"
proof (cases "a = 0 \<or> b = 0")
  case False then have "a \<noteq> 0" and "b \<noteq> 0" by auto
    then show ?thesis using no_zero_divisors by simp
next
  case True then show ?thesis by auto
qed

text{*Cancellation of equalities with a common factor*}
lemma mult_cancel_right [simp, noatp]:
  "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b"
proof -
  have "(a * c = b * c) = ((a - b) * c = 0)"
    by (simp add: algebra_simps right_minus_eq)
  thus ?thesis by (simp add: disj_commute right_minus_eq)
qed

lemma mult_cancel_left [simp, noatp]:
  "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
proof -
  have "(c * a = c * b) = (c * (a - b) = 0)"
    by (simp add: algebra_simps right_minus_eq)
  thus ?thesis by (simp add: right_minus_eq)
qed

end

class ring_1_no_zero_divisors = ring_1 + ring_no_zero_divisors
begin

lemma mult_cancel_right1 [simp]:
  "c = b * c \<longleftrightarrow> c = 0 \<or> b = 1"
by (insert mult_cancel_right [of 1 c b], force)

lemma mult_cancel_right2 [simp]:
  "a * c = c \<longleftrightarrow> c = 0 \<or> a = 1"
by (insert mult_cancel_right [of a c 1], simp)
 
lemma mult_cancel_left1 [simp]:
  "c = c * b \<longleftrightarrow> c = 0 \<or> b = 1"
by (insert mult_cancel_left [of c 1 b], force)

lemma mult_cancel_left2 [simp]:
  "c * a = c \<longleftrightarrow> c = 0 \<or> a = 1"
by (insert mult_cancel_left [of c a 1], simp)

end

class idom = comm_ring_1 + no_zero_divisors
begin

subclass ring_1_no_zero_divisors ..

lemma square_eq_iff: "a * a = b * b \<longleftrightarrow> (a = b \<or> a = - b)"
proof
  assume "a * a = b * b"
  then have "(a - b) * (a + b) = 0"
    by (simp add: algebra_simps)
  then show "a = b \<or> a = - b"
    by (simp add: right_minus_eq eq_neg_iff_add_eq_0)
next
  assume "a = b \<or> a = - b"
  then show "a * a = b * b" by auto
qed

lemma dvd_mult_cancel_right [simp]:
  "a * c dvd b * c \<longleftrightarrow> c = 0 \<or> a dvd b"
proof -
  have "a * c dvd b * c \<longleftrightarrow> (\<exists>k. b * c = (a * k) * c)"
    unfolding dvd_def by (simp add: mult_ac)
  also have "(\<exists>k. b * c = (a * k) * c) \<longleftrightarrow> c = 0 \<or> a dvd b"
    unfolding dvd_def by simp
  finally show ?thesis .
qed

lemma dvd_mult_cancel_left [simp]:
  "c * a dvd c * b \<longleftrightarrow> c = 0 \<or> a dvd b"
proof -
  have "c * a dvd c * b \<longleftrightarrow> (\<exists>k. b * c = (a * k) * c)"
    unfolding dvd_def by (simp add: mult_ac)
  also have "(\<exists>k. b * c = (a * k) * c) \<longleftrightarrow> c = 0 \<or> a dvd b"
    unfolding dvd_def by simp
  finally show ?thesis .
qed

end

class division_ring = ring_1 + inverse +
  assumes left_inverse [simp]:  "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes right_inverse [simp]: "a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
begin

subclass ring_1_no_zero_divisors
proof
  fix a b :: 'a
  assume a: "a \<noteq> 0" and b: "b \<noteq> 0"
  show "a * b \<noteq> 0"
  proof
    assume ab: "a * b = 0"
    hence "0 = inverse a * (a * b) * inverse b" by simp
    also have "\<dots> = (inverse a * a) * (b * inverse b)"
      by (simp only: mult_assoc)
    also have "\<dots> = 1" using a b by simp
    finally show False by simp
  qed
qed

lemma nonzero_imp_inverse_nonzero:
  "a \<noteq> 0 \<Longrightarrow> inverse a \<noteq> 0"
proof
  assume ianz: "inverse a = 0"
  assume "a \<noteq> 0"
  hence "1 = a * inverse a" by simp
  also have "... = 0" by (simp add: ianz)
  finally have "1 = 0" .
  thus False by (simp add: eq_commute)
qed

lemma inverse_zero_imp_zero:
  "inverse a = 0 \<Longrightarrow> a = 0"
apply (rule classical)
apply (drule nonzero_imp_inverse_nonzero)
apply auto
done

lemma inverse_unique: 
  assumes ab: "a * b = 1"
  shows "inverse a = b"
proof -
  have "a \<noteq> 0" using ab by (cases "a = 0") simp_all
  moreover have "inverse a * (a * b) = inverse a" by (simp add: ab)
  ultimately show ?thesis by (simp add: mult_assoc [symmetric])
qed

lemma nonzero_inverse_minus_eq:
  "a \<noteq> 0 \<Longrightarrow> inverse (- a) = - inverse a"
by (rule inverse_unique) simp

lemma nonzero_inverse_inverse_eq:
  "a \<noteq> 0 \<Longrightarrow> inverse (inverse a) = a"
by (rule inverse_unique) simp

lemma nonzero_inverse_eq_imp_eq:
  assumes "inverse a = inverse b" and "a \<noteq> 0" and "b \<noteq> 0"
  shows "a = b"
proof -
  from `inverse a = inverse b`
  have "inverse (inverse a) = inverse (inverse b)" by (rule arg_cong)
  with `a \<noteq> 0` and `b \<noteq> 0` show "a = b"
    by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_1 [simp]: "inverse 1 = 1"
by (rule inverse_unique) simp

lemma nonzero_inverse_mult_distrib: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "inverse (a * b) = inverse b * inverse a"
proof -
  have "a * (b * inverse b) * inverse a = 1" using assms by simp
  hence "a * b * (inverse b * inverse a) = 1" by (simp only: mult_assoc)
  thus ?thesis by (rule inverse_unique)
qed

lemma division_ring_inverse_add:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a + inverse b = inverse a * (a + b) * inverse b"
by (simp add: algebra_simps)

lemma division_ring_inverse_diff:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a - inverse b = inverse a * (b - a) * inverse b"
by (simp add: algebra_simps)

end

class field = comm_ring_1 + inverse +
  assumes field_inverse:  "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes divide_inverse: "a / b = a * inverse b"
begin

subclass division_ring
proof
  fix a :: 'a
  assume "a \<noteq> 0"
  thus "inverse a * a = 1" by (rule field_inverse)
  thus "a * inverse a = 1" by (simp only: mult_commute)
qed

subclass idom ..

lemma right_inverse_eq: "b \<noteq> 0 \<Longrightarrow> a / b = 1 \<longleftrightarrow> a = b"
proof
  assume neq: "b \<noteq> 0"
  {
    hence "a = (a / b) * b" by (simp add: divide_inverse mult_ac)
    also assume "a / b = 1"
    finally show "a = b" by simp
  next
    assume "a = b"
    with neq show "a / b = 1" by (simp add: divide_inverse)
  }
qed

lemma nonzero_inverse_eq_divide: "a \<noteq> 0 \<Longrightarrow> inverse a = 1 / a"
by (simp add: divide_inverse)

lemma divide_self [simp]: "a \<noteq> 0 \<Longrightarrow> a / a = 1"
by (simp add: divide_inverse)

lemma divide_zero_left [simp]: "0 / a = 0"
by (simp add: divide_inverse)

lemma inverse_eq_divide: "inverse a = 1 / a"
by (simp add: divide_inverse)

lemma add_divide_distrib: "(a+b) / c = a/c + b/c"
by (simp add: divide_inverse algebra_simps) 

end

class division_by_zero = zero + inverse +
  assumes inverse_zero [simp]: "inverse 0 = 0"

lemma divide_zero [simp]:
  "a / 0 = (0::'a::{field,division_by_zero})"
by (simp add: divide_inverse)

lemma divide_self_if [simp]:
  "a / (a::'a::{field,division_by_zero}) = (if a=0 then 0 else 1)"
by simp

class mult_mono = times + zero + ord +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"

class pordered_semiring = mult_mono + semiring_0 + pordered_ab_semigroup_add 
begin

lemma mult_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> c
     \<Longrightarrow> a * c \<le> b * d"
apply (erule mult_right_mono [THEN order_trans], assumption)
apply (erule mult_left_mono, assumption)
done

lemma mult_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c
     \<Longrightarrow> a * c \<le> b * d"
apply (rule mult_mono)
apply (fast intro: order_trans)+
done

end

class pordered_cancel_semiring = mult_mono + pordered_ab_semigroup_add
  + semiring + cancel_comm_monoid_add
begin

subclass semiring_0_cancel ..
subclass pordered_semiring ..

lemma mult_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * b"
by (drule mult_left_mono [of zero b], auto)

lemma mult_nonneg_nonpos: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> a * b \<le> 0"
by (drule mult_left_mono [of b zero], auto)

lemma mult_nonneg_nonpos2: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> b * a \<le> 0" 
by (drule mult_right_mono [of b zero], auto)

lemma split_mult_neg_le: "(0 \<le> a & b \<le> 0) | (a \<le> 0 & 0 \<le> b) \<Longrightarrow> a * b \<le> 0" 
by (auto simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)

end

class ordered_semiring = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add + mult_mono
begin

subclass pordered_cancel_semiring ..

subclass pordered_comm_monoid_add ..

lemma mult_left_less_imp_less:
  "c * a < c * b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
by (force simp add: mult_left_mono not_le [symmetric])
 
lemma mult_right_less_imp_less:
  "a * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
by (force simp add: mult_right_mono not_le [symmetric])

end

class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume A: "a \<le> b" "0 \<le> c"
  from A show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from A show "a * c \<le> b * c"
    unfolding le_less
    using mult_strict_right_mono by (cases "c = 0") auto
qed

lemma mult_left_le_imp_le:
  "c * a \<le> c * b \<Longrightarrow> 0 < c \<Longrightarrow> a \<le> b"
by (force simp add: mult_strict_left_mono _not_less [symmetric])
 
lemma mult_right_le_imp_le:
  "a * c \<le> b * c \<Longrightarrow> 0 < c \<Longrightarrow> a \<le> b"
by (force simp add: mult_strict_right_mono not_less [symmetric])

lemma mult_pos_pos:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
by (drule mult_strict_left_mono [of zero b], auto)

lemma mult_pos_neg:
  "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
by (drule mult_strict_left_mono [of b zero], auto)

lemma mult_pos_neg2:
  "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> b * a < 0" 
by (drule mult_strict_right_mono [of b zero], auto)

lemma zero_less_mult_pos:
  "0 < a * b \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b"
apply (cases "b\<le>0") 
 apply (auto simp add: le_less not_less)
apply (drule_tac mult_pos_neg [of a b]) 
 apply (auto dest: less_not_sym)
done

lemma zero_less_mult_pos2:
  "0 < b * a \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b"
apply (cases "b\<le>0") 
 apply (auto simp add: le_less not_less)
apply (drule_tac mult_pos_neg2 [of a b]) 
 apply (auto dest: less_not_sym)
done

text{*Strict monotonicity in both arguments*}
lemma mult_strict_mono:
  assumes "a < b" and "c < d" and "0 < b" and "0 \<le> c"
  shows "a * c < b * d"
  using assms apply (cases "c=0")
  apply (simp add: mult_pos_pos) 
  apply (erule mult_strict_right_mono [THEN less_trans])
  apply (force simp add: le_less) 
  apply (erule mult_strict_left_mono, assumption)
  done

text{*This weaker variant has more natural premises*}
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes "a < b" and "c \<le> d" and "0 \<le> a" and "0 < c"
  shows "a * c < b * d"
  using assms apply (subgoal_tac "a * c < b * c")
  apply (erule less_le_trans)
  apply (erule mult_left_mono)
  apply simp
  apply (erule mult_strict_right_mono)
  apply assumption
  done

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms apply (subgoal_tac "a * c \<le> b * c")
  apply (erule le_less_trans)
  apply (erule mult_strict_left_mono)
  apply simp
  apply (erule mult_right_mono)
  apply simp
  done

lemma mult_less_imp_less_left:
  assumes less: "c * a < c * b" and nonneg: "0 \<le> c"
  shows "a < b"
proof (rule ccontr)
  assume "\<not>  a < b"
  hence "b \<le> a" by (simp add: linorder_not_less)
  hence "c * b \<le> c * a" using nonneg by (rule mult_left_mono)
  with this and less show False by (simp add: not_less [symmetric])
qed

lemma mult_less_imp_less_right:
  assumes less: "a * c < b * c" and nonneg: "0 \<le> c"
  shows "a < b"
proof (rule ccontr)
  assume "\<not> a < b"
  hence "b \<le> a" by (simp add: linorder_not_less)
  hence "b * c \<le> a * c" using nonneg by (rule mult_right_mono)
  with this and less show False by (simp add: not_less [symmetric])
qed  

end

class mult_mono1 = times + zero + ord +
  assumes mult_mono1: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"

class pordered_comm_semiring = comm_semiring_0
  + pordered_ab_semigroup_add + mult_mono1
begin

subclass pordered_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b" by (rule mult_mono1)
  thus "a * c \<le> b * c" by (simp only: mult_commute)
qed

end

class pordered_cancel_comm_semiring = comm_semiring_0_cancel
  + pordered_ab_semigroup_add + mult_mono1
begin

subclass pordered_comm_semiring ..
subclass pordered_cancel_semiring ..

end

class ordered_comm_semiring_strict = comm_semiring_0 + ordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono_comm: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass ordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" "0 < c"
  thus "c * a < c * b" by (rule mult_strict_left_mono_comm)
  thus "a * c < b * c" by (simp only: mult_commute)
qed

subclass pordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

end

class pordered_ring = ring + pordered_cancel_semiring 
begin

subclass pordered_ab_group_add ..

text{*Legacy - use @{text algebra_simps} *}
lemmas ring_simps[noatp] = algebra_simps

lemma less_add_iff1:
  "a * e + c < b * e + d \<longleftrightarrow> (a - b) * e + c < d"
by (simp add: algebra_simps)

lemma less_add_iff2:
  "a * e + c < b * e + d \<longleftrightarrow> c < (b - a) * e + d"
by (simp add: algebra_simps)

lemma le_add_iff1:
  "a * e + c \<le> b * e + d \<longleftrightarrow> (a - b) * e + c \<le> d"
by (simp add: algebra_simps)

lemma le_add_iff2:
  "a * e + c \<le> b * e + d \<longleftrightarrow> c \<le> (b - a) * e + d"
by (simp add: algebra_simps)

lemma mult_left_mono_neg:
  "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c * a \<le> c * b"
  apply (drule mult_left_mono [of _ _ "uminus c"])
  apply (simp_all add: minus_mult_left [symmetric]) 
  done

lemma mult_right_mono_neg:
  "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a * c \<le> b * c"
  apply (drule mult_right_mono [of _ _ "uminus c"])
  apply (simp_all add: minus_mult_right [symmetric]) 
  done

lemma mult_nonpos_nonpos:
  "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a * b"
by (drule mult_right_mono_neg [of a zero b]) auto

lemma split_mult_pos_le:
  "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a * b"
by (auto simp add: mult_nonneg_nonneg mult_nonpos_nonpos)

end

class abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

class sgn_if = minus + uminus + zero + one + ord + sgn +
  assumes sgn_if: "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

lemma (in sgn_if) sgn0[simp]: "sgn 0 = 0"
by(simp add:sgn_if)

class ordered_ring = ring + ordered_semiring
  + ordered_ab_group_add + abs_if
begin

subclass pordered_ring ..

subclass pordered_ab_group_add_abs
proof
  fix a b
  show "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
by (auto simp add: abs_if not_less neg_less_eq_nonneg less_eq_neg_nonpos)
   (auto simp del: minus_add_distrib simp add: minus_add_distrib [symmetric]
     neg_less_eq_nonneg less_eq_neg_nonpos, auto intro: add_nonneg_nonneg,
      auto intro!: less_imp_le add_neg_neg)
qed (auto simp add: abs_if less_eq_neg_nonpos neg_equal_zero)

end

(* The "strict" suffix can be seen as describing the combination of ordered_ring and no_zero_divisors.
   Basically, ordered_ring + no_zero_divisors = ordered_ring_strict.
 *)
class ordered_ring_strict = ring + ordered_semiring_strict
  + ordered_ab_group_add + abs_if
begin

subclass ordered_ring ..

lemma mult_strict_left_mono_neg:
  "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
  apply (drule mult_strict_left_mono [of _ _ "uminus c"])
  apply (simp_all add: minus_mult_left [symmetric]) 
  done

lemma mult_strict_right_mono_neg:
  "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
  apply (drule mult_strict_right_mono [of _ _ "uminus c"])
  apply (simp_all add: minus_mult_right [symmetric]) 
  done

lemma mult_neg_neg:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
by (drule mult_strict_right_mono_neg, auto)

subclass ring_no_zero_divisors
proof
  fix a b
  assume "a \<noteq> 0" then have A: "a < 0 \<or> 0 < a" by (simp add: neq_iff)
  assume "b \<noteq> 0" then have B: "b < 0 \<or> 0 < b" by (simp add: neq_iff)
  have "a * b < 0 \<or> 0 < a * b"
  proof (cases "a < 0")
    case True note A' = this
    show ?thesis proof (cases "b < 0")
      case True with A'
      show ?thesis by (auto dest: mult_neg_neg)
    next
      case False with B have "0 < b" by auto
      with A' show ?thesis by (auto dest: mult_strict_right_mono)
    qed
  next
    case False with A have A': "0 < a" by auto
    show ?thesis proof (cases "b < 0")
      case True with A'
      show ?thesis by (auto dest: mult_strict_right_mono_neg)
    next
      case False with B have "0 < b" by auto
      with A' show ?thesis by (auto dest: mult_pos_pos)
    qed
  qed
  then show "a * b \<noteq> 0" by (simp add: neq_iff)
qed

lemma zero_less_mult_iff:
  "0 < a * b \<longleftrightarrow> 0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0"
  apply (auto simp add: mult_pos_pos mult_neg_neg)
  apply (simp_all add: not_less le_less)
  apply (erule disjE) apply assumption defer
  apply (erule disjE) defer apply (drule sym) apply simp
  apply (erule disjE) defer apply (drule sym) apply simp
  apply (erule disjE) apply assumption apply (drule sym) apply simp
  apply (drule sym) apply simp
  apply (blast dest: zero_less_mult_pos)
  apply (blast dest: zero_less_mult_pos2)
  done

lemma zero_le_mult_iff:
  "0 \<le> a * b \<longleftrightarrow> 0 \<le> a \<and> 0 \<le> b \<or> a \<le> 0 \<and> b \<le> 0"
by (auto simp add: eq_commute [of 0] le_less not_less zero_less_mult_iff)

lemma mult_less_0_iff:
  "a * b < 0 \<longleftrightarrow> 0 < a \<and> b < 0 \<or> a < 0 \<and> 0 < b"
  apply (insert zero_less_mult_iff [of "-a" b]) 
  apply (force simp add: minus_mult_left[symmetric]) 
  done

lemma mult_le_0_iff:
  "a * b \<le> 0 \<longleftrightarrow> 0 \<le> a \<and> b \<le> 0 \<or> a \<le> 0 \<and> 0 \<le> b"
  apply (insert zero_le_mult_iff [of "-a" b]) 
  apply (force simp add: minus_mult_left[symmetric]) 
  done

lemma zero_le_square [simp]: "0 \<le> a * a"
by (simp add: zero_le_mult_iff linear)

lemma not_square_less_zero [simp]: "\<not> (a * a < 0)"
by (simp add: not_less)

text{*Cancellation laws for @{term "c*a < c*b"} and @{term "a*c < b*c"},
   also with the relations @{text "\<le>"} and equality.*}

text{*These ``disjunction'' versions produce two cases when the comparison is
 an assumption, but effectively four when the comparison is a goal.*}

lemma mult_less_cancel_right_disj:
  "a * c < b * c \<longleftrightarrow> 0 < c \<and> a < b \<or> c < 0 \<and>  b < a"
  apply (cases "c = 0")
  apply (auto simp add: neq_iff mult_strict_right_mono 
                      mult_strict_right_mono_neg)
  apply (auto simp add: not_less 
                      not_le [symmetric, of "a*c"]
                      not_le [symmetric, of a])
  apply (erule_tac [!] notE)
  apply (auto simp add: less_imp_le mult_right_mono 
                      mult_right_mono_neg)
  done

lemma mult_less_cancel_left_disj:
  "c * a < c * b \<longleftrightarrow> 0 < c \<and> a < b \<or> c < 0 \<and>  b < a"
  apply (cases "c = 0")
  apply (auto simp add: neq_iff mult_strict_left_mono 
                      mult_strict_left_mono_neg)
  apply (auto simp add: not_less 
                      not_le [symmetric, of "c*a"]
                      not_le [symmetric, of a])
  apply (erule_tac [!] notE)
  apply (auto simp add: less_imp_le mult_left_mono 
                      mult_left_mono_neg)
  done

text{*The ``conjunction of implication'' lemmas produce two cases when the
comparison is a goal, but give four when the comparison is an assumption.*}

lemma mult_less_cancel_right:
  "a * c < b * c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < b) \<and> (c \<le> 0 \<longrightarrow> b < a)"
  using mult_less_cancel_right_disj [of a c b] by auto

lemma mult_less_cancel_left:
  "c * a < c * b \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < b) \<and> (c \<le> 0 \<longrightarrow> b < a)"
  using mult_less_cancel_left_disj [of c a b] by auto

lemma mult_le_cancel_right:
   "a * c \<le> b * c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
by (simp add: not_less [symmetric] mult_less_cancel_right_disj)

lemma mult_le_cancel_left:
  "c * a \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
by (simp add: not_less [symmetric] mult_less_cancel_left_disj)

end

text{*Legacy - use @{text algebra_simps} *}
lemmas ring_simps[noatp] = algebra_simps


class pordered_comm_ring = comm_ring + pordered_comm_semiring
begin

subclass pordered_ring ..
subclass pordered_cancel_comm_semiring ..

end

class ordered_semidom = comm_semiring_1_cancel + ordered_comm_semiring_strict +
  (*previously ordered_semiring*)
  assumes zero_less_one [simp]: "0 < 1"
begin

lemma pos_add_strict:
  shows "0 < a \<Longrightarrow> b < c \<Longrightarrow> b < a + c"
  using add_strict_mono [of zero a b c] by simp

lemma zero_le_one [simp]: "0 \<le> 1"
by (rule zero_less_one [THEN less_imp_le]) 

lemma not_one_le_zero [simp]: "\<not> 1 \<le> 0"
by (simp add: not_le) 

lemma not_one_less_zero [simp]: "\<not> 1 < 0"
by (simp add: not_less) 

lemma less_1_mult:
  assumes "1 < m" and "1 < n"
  shows "1 < m * n"
  using assms mult_strict_mono [of 1 m 1 n]
    by (simp add:  less_trans [OF zero_less_one]) 

end

class ordered_idom = comm_ring_1 +
  ordered_comm_semiring_strict + ordered_ab_group_add +
  abs_if + sgn_if
  (*previously ordered_ring*)
begin

subclass ordered_ring_strict ..
subclass pordered_comm_ring ..
subclass idom ..

subclass ordered_semidom
proof
  have "0 \<le> 1 * 1" by (rule zero_le_square)
  thus "0 < 1" by (simp add: le_less)
qed 

lemma linorder_neqE_ordered_idom:
  assumes "x \<noteq> y" obtains "x < y" | "y < x"
  using assms by (rule neqE)

text {* These cancellation simprules also produce two cases when the comparison is a goal. *}

lemma mult_le_cancel_right1:
  "c \<le> b * c \<longleftrightarrow> (0 < c \<longrightarrow> 1 \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> 1)"
by (insert mult_le_cancel_right [of 1 c b], simp)

lemma mult_le_cancel_right2:
  "a * c \<le> c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> 1) \<and> (c < 0 \<longrightarrow> 1 \<le> a)"
by (insert mult_le_cancel_right [of a c 1], simp)

lemma mult_le_cancel_left1:
  "c \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> 1 \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> 1)"
by (insert mult_le_cancel_left [of c 1 b], simp)

lemma mult_le_cancel_left2:
  "c * a \<le> c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> 1) \<and> (c < 0 \<longrightarrow> 1 \<le> a)"
by (insert mult_le_cancel_left [of c a 1], simp)

lemma mult_less_cancel_right1:
  "c < b * c \<longleftrightarrow> (0 \<le> c \<longrightarrow> 1 < b) \<and> (c \<le> 0 \<longrightarrow> b < 1)"
by (insert mult_less_cancel_right [of 1 c b], simp)

lemma mult_less_cancel_right2:
  "a * c < c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < 1) \<and> (c \<le> 0 \<longrightarrow> 1 < a)"
by (insert mult_less_cancel_right [of a c 1], simp)

lemma mult_less_cancel_left1:
  "c < c * b \<longleftrightarrow> (0 \<le> c \<longrightarrow> 1 < b) \<and> (c \<le> 0 \<longrightarrow> b < 1)"
by (insert mult_less_cancel_left [of c 1 b], simp)

lemma mult_less_cancel_left2:
  "c * a < c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < 1) \<and> (c \<le> 0 \<longrightarrow> 1 < a)"
by (insert mult_less_cancel_left [of c a 1], simp)

lemma sgn_sgn [simp]:
  "sgn (sgn a) = sgn a"
unfolding sgn_if by simp

lemma sgn_0_0:
  "sgn a = 0 \<longleftrightarrow> a = 0"
unfolding sgn_if by simp

lemma sgn_1_pos:
  "sgn a = 1 \<longleftrightarrow> a > 0"
unfolding sgn_if by (simp add: neg_equal_zero)

lemma sgn_1_neg:
  "sgn a = - 1 \<longleftrightarrow> a < 0"
unfolding sgn_if by (auto simp add: equal_neg_zero)

lemma sgn_pos [simp]:
  "0 < a \<Longrightarrow> sgn a = 1"
unfolding sgn_1_pos .

lemma sgn_neg [simp]:
  "a < 0 \<Longrightarrow> sgn a = - 1"
unfolding sgn_1_neg .

lemma sgn_times:
  "sgn (a * b) = sgn a * sgn b"
by (auto simp add: sgn_if zero_less_mult_iff)

lemma abs_sgn: "abs k = k * sgn k"
unfolding sgn_if abs_if by auto

lemma sgn_greater [simp]:
  "0 < sgn a \<longleftrightarrow> 0 < a"
  unfolding sgn_if by auto

lemma sgn_less [simp]:
  "sgn a < 0 \<longleftrightarrow> a < 0"
  unfolding sgn_if by auto

lemma abs_dvd_iff [simp]: "(abs m) dvd k \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

lemma dvd_abs_iff [simp]: "m dvd (abs k) \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

end

class ordered_field = field + ordered_idom

text {* Simprules for comparisons where common factors can be cancelled. *}

lemmas mult_compare_simps[noatp] =
    mult_le_cancel_right mult_le_cancel_left
    mult_le_cancel_right1 mult_le_cancel_right2
    mult_le_cancel_left1 mult_le_cancel_left2
    mult_less_cancel_right mult_less_cancel_left
    mult_less_cancel_right1 mult_less_cancel_right2
    mult_less_cancel_left1 mult_less_cancel_left2
    mult_cancel_right mult_cancel_left
    mult_cancel_right1 mult_cancel_right2
    mult_cancel_left1 mult_cancel_left2

-- {* FIXME continue localization here *}

lemma inverse_nonzero_iff_nonzero [simp]:
   "(inverse a = 0) = (a = (0::'a::{division_ring,division_by_zero}))"
by (force dest: inverse_zero_imp_zero) 

lemma inverse_minus_eq [simp]:
   "inverse(-a) = -inverse(a::'a::{division_ring,division_by_zero})"
proof cases
  assume "a=0" thus ?thesis by (simp add: inverse_zero)
next
  assume "a\<noteq>0" 
  thus ?thesis by (simp add: nonzero_inverse_minus_eq)
qed

lemma inverse_eq_imp_eq:
  "inverse a = inverse b ==> a = (b::'a::{division_ring,division_by_zero})"
apply (cases "a=0 | b=0") 
 apply (force dest!: inverse_zero_imp_zero
              simp add: eq_commute [of "0::'a"])
apply (force dest!: nonzero_inverse_eq_imp_eq) 
done

lemma inverse_eq_iff_eq [simp]:
  "(inverse a = inverse b) = (a = (b::'a::{division_ring,division_by_zero}))"
by (force dest!: inverse_eq_imp_eq)

lemma inverse_inverse_eq [simp]:
     "inverse(inverse (a::'a::{division_ring,division_by_zero})) = a"
  proof cases
    assume "a=0" thus ?thesis by simp
  next
    assume "a\<noteq>0" 
    thus ?thesis by (simp add: nonzero_inverse_inverse_eq)
  qed

text{*This version builds in division by zero while also re-orienting
      the right-hand side.*}
lemma inverse_mult_distrib [simp]:
     "inverse(a*b) = inverse(a) * inverse(b::'a::{field,division_by_zero})"
  proof cases
    assume "a \<noteq> 0 & b \<noteq> 0" 
    thus ?thesis by (simp add: nonzero_inverse_mult_distrib mult_commute)
  next
    assume "~ (a \<noteq> 0 & b \<noteq> 0)" 
    thus ?thesis by force
  qed

text{*There is no slick version using division by zero.*}
lemma inverse_add:
  "[|a \<noteq> 0;  b \<noteq> 0|]
   ==> inverse a + inverse b = (a+b) * inverse a * inverse (b::'a::field)"
by (simp add: division_ring_inverse_add mult_ac)

lemma inverse_divide [simp]:
  "inverse (a/b) = b / (a::'a::{field,division_by_zero})"
by (simp add: divide_inverse mult_commute)


subsection {* Calculations with fractions *}

text{* There is a whole bunch of simp-rules just for class @{text
field} but none for class @{text field} and @{text nonzero_divides}
because the latter are covered by a simproc. *}

lemma nonzero_mult_divide_mult_cancel_left[simp,noatp]:
assumes [simp]: "b\<noteq>0" and [simp]: "c\<noteq>0" shows "(c*a)/(c*b) = a/(b::'a::field)"
proof -
  have "(c*a)/(c*b) = c * a * (inverse b * inverse c)"
    by (simp add: divide_inverse nonzero_inverse_mult_distrib)
  also have "... =  a * inverse b * (inverse c * c)"
    by (simp only: mult_ac)
  also have "... =  a * inverse b" by simp
    finally show ?thesis by (simp add: divide_inverse)
qed

lemma mult_divide_mult_cancel_left:
  "c\<noteq>0 ==> (c*a) / (c*b) = a / (b::'a::{field,division_by_zero})"
apply (cases "b = 0")
apply (simp_all add: nonzero_mult_divide_mult_cancel_left)
done

lemma nonzero_mult_divide_mult_cancel_right [noatp]:
  "[|b\<noteq>0; c\<noteq>0|] ==> (a*c) / (b*c) = a/(b::'a::field)"
by (simp add: mult_commute [of _ c] nonzero_mult_divide_mult_cancel_left) 

lemma mult_divide_mult_cancel_right:
  "c\<noteq>0 ==> (a*c) / (b*c) = a / (b::'a::{field,division_by_zero})"
apply (cases "b = 0")
apply (simp_all add: nonzero_mult_divide_mult_cancel_right)
done

lemma divide_1 [simp]: "a/1 = (a::'a::field)"
by (simp add: divide_inverse)

lemma times_divide_eq_right: "a * (b/c) = (a*b) / (c::'a::field)"
by (simp add: divide_inverse mult_assoc)

lemma times_divide_eq_left: "(b/c) * a = (b*a) / (c::'a::field)"
by (simp add: divide_inverse mult_ac)

lemmas times_divide_eq[noatp] = times_divide_eq_right times_divide_eq_left

lemma divide_divide_eq_right [simp,noatp]:
  "a / (b/c) = (a*c) / (b::'a::{field,division_by_zero})"
by (simp add: divide_inverse mult_ac)

lemma divide_divide_eq_left [simp,noatp]:
  "(a / b) / (c::'a::{field,division_by_zero}) = a / (b*c)"
by (simp add: divide_inverse mult_assoc)

lemma add_frac_eq: "(y::'a::field) ~= 0 ==> z ~= 0 ==>
    x / y + w / z = (x * z + w * y) / (y * z)"
apply (subgoal_tac "x / y = (x * z) / (y * z)")
apply (erule ssubst)
apply (subgoal_tac "w / z = (w * y) / (y * z)")
apply (erule ssubst)
apply (rule add_divide_distrib [THEN sym])
apply (subst mult_commute)
apply (erule nonzero_mult_divide_mult_cancel_left [THEN sym])
apply assumption
apply (erule nonzero_mult_divide_mult_cancel_right [THEN sym])
apply assumption
done


subsubsection{*Special Cancellation Simprules for Division*}

lemma mult_divide_mult_cancel_left_if[simp,noatp]:
fixes c :: "'a :: {field,division_by_zero}"
shows "(c*a) / (c*b) = (if c=0 then 0 else a/b)"
by (simp add: mult_divide_mult_cancel_left)

lemma nonzero_mult_divide_cancel_right[simp,noatp]:
  "b \<noteq> 0 \<Longrightarrow> a * b / b = (a::'a::field)"
using nonzero_mult_divide_mult_cancel_right[of 1 b a] by simp

lemma nonzero_mult_divide_cancel_left[simp,noatp]:
  "a \<noteq> 0 \<Longrightarrow> a * b / a = (b::'a::field)"
using nonzero_mult_divide_mult_cancel_left[of 1 a b] by simp


lemma nonzero_divide_mult_cancel_right[simp,noatp]:
  "\<lbrakk> a\<noteq>0; b\<noteq>0 \<rbrakk> \<Longrightarrow> b / (a * b) = 1/(a::'a::field)"
using nonzero_mult_divide_mult_cancel_right[of a b 1] by simp

lemma nonzero_divide_mult_cancel_left[simp,noatp]:
  "\<lbrakk> a\<noteq>0; b\<noteq>0 \<rbrakk> \<Longrightarrow> a / (a * b) = 1/(b::'a::field)"
using nonzero_mult_divide_mult_cancel_left[of b a 1] by simp


lemma nonzero_mult_divide_mult_cancel_left2[simp,noatp]:
  "[|b\<noteq>0; c\<noteq>0|] ==> (c*a) / (b*c) = a/(b::'a::field)"
using nonzero_mult_divide_mult_cancel_left[of b c a] by(simp add:mult_ac)

lemma nonzero_mult_divide_mult_cancel_right2[simp,noatp]:
  "[|b\<noteq>0; c\<noteq>0|] ==> (a*c) / (c*b) = a/(b::'a::field)"
using nonzero_mult_divide_mult_cancel_right[of b c a] by(simp add:mult_ac)


subsection {* Division and Unary Minus *}

lemma nonzero_minus_divide_left: "b \<noteq> 0 ==> - (a/b) = (-a) / (b::'a::field)"
by (simp add: divide_inverse)

lemma nonzero_minus_divide_right: "b \<noteq> 0 ==> - (a/b) = a / -(b::'a::field)"
by (simp add: divide_inverse nonzero_inverse_minus_eq)

lemma nonzero_minus_divide_divide: "b \<noteq> 0 ==> (-a)/(-b) = a / (b::'a::field)"
by (simp add: divide_inverse nonzero_inverse_minus_eq)

lemma minus_divide_left: "- (a/b) = (-a) / (b::'a::field)"
by (simp add: divide_inverse)

lemma minus_divide_right: "- (a/b) = a / -(b::'a::{field,division_by_zero})"
by (simp add: divide_inverse)


text{*The effect is to extract signs from divisions*}
lemmas divide_minus_left[noatp] = minus_divide_left [symmetric]
lemmas divide_minus_right[noatp] = minus_divide_right [symmetric]
declare divide_minus_left [simp]   divide_minus_right [simp]

lemma minus_divide_divide [simp]:
  "(-a)/(-b) = a / (b::'a::{field,division_by_zero})"
apply (cases "b=0", simp) 
apply (simp add: nonzero_minus_divide_divide) 
done

lemma diff_divide_distrib: "(a-b)/(c::'a::field) = a/c - b/c"
by (simp add: diff_minus add_divide_distrib) 

lemma add_divide_eq_iff:
  "(z::'a::field) \<noteq> 0 \<Longrightarrow> x + y/z = (z*x + y)/z"
by(simp add:add_divide_distrib nonzero_mult_divide_cancel_left)

lemma divide_add_eq_iff:
  "(z::'a::field) \<noteq> 0 \<Longrightarrow> x/z + y = (x + z*y)/z"
by(simp add:add_divide_distrib nonzero_mult_divide_cancel_left)

lemma diff_divide_eq_iff:
  "(z::'a::field) \<noteq> 0 \<Longrightarrow> x - y/z = (z*x - y)/z"
by(simp add:diff_divide_distrib nonzero_mult_divide_cancel_left)

lemma divide_diff_eq_iff:
  "(z::'a::field) \<noteq> 0 \<Longrightarrow> x/z - y = (x - z*y)/z"
by(simp add:diff_divide_distrib nonzero_mult_divide_cancel_left)

lemma nonzero_eq_divide_eq: "c\<noteq>0 ==> ((a::'a::field) = b/c) = (a*c = b)"
proof -
  assume [simp]: "c\<noteq>0"
  have "(a = b/c) = (a*c = (b/c)*c)" by simp
  also have "... = (a*c = b)" by (simp add: divide_inverse mult_assoc)
  finally show ?thesis .
qed

lemma nonzero_divide_eq_eq: "c\<noteq>0 ==> (b/c = (a::'a::field)) = (b = a*c)"
proof -
  assume [simp]: "c\<noteq>0"
  have "(b/c = a) = ((b/c)*c = a*c)"  by simp
  also have "... = (b = a*c)"  by (simp add: divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma eq_divide_eq:
  "((a::'a::{field,division_by_zero}) = b/c) = (if c\<noteq>0 then a*c = b else a=0)"
by (simp add: nonzero_eq_divide_eq) 

lemma divide_eq_eq:
  "(b/c = (a::'a::{field,division_by_zero})) = (if c\<noteq>0 then b = a*c else a=0)"
by (force simp add: nonzero_divide_eq_eq) 

lemma divide_eq_imp: "(c::'a::{division_by_zero,field}) ~= 0 ==>
    b = a * c ==> b / c = a"
by (subst divide_eq_eq, simp)

lemma eq_divide_imp: "(c::'a::{division_by_zero,field}) ~= 0 ==>
    a * c = b ==> a = b / c"
by (subst eq_divide_eq, simp)


lemmas field_eq_simps[noatp] = algebra_simps
  (* pull / out*)
  add_divide_eq_iff divide_add_eq_iff
  diff_divide_eq_iff divide_diff_eq_iff
  (* multiply eqn *)
  nonzero_eq_divide_eq nonzero_divide_eq_eq
(* is added later:
  times_divide_eq_left times_divide_eq_right
*)

text{*An example:*}
lemma fixes a b c d e f :: "'a::field"
shows "\<lbrakk>a\<noteq>b; c\<noteq>d; e\<noteq>f \<rbrakk> \<Longrightarrow> ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) = 1"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) \<noteq> 0")
 apply(simp add:field_eq_simps)
apply(simp)
done


lemma diff_frac_eq: "(y::'a::field) ~= 0 ==> z ~= 0 ==>
    x / y - w / z = (x * z - w * y) / (y * z)"
by (simp add:field_eq_simps times_divide_eq)

lemma frac_eq_eq: "(y::'a::field) ~= 0 ==> z ~= 0 ==>
    (x / y = w / z) = (x * z = w * y)"
by (simp add:field_eq_simps times_divide_eq)


subsection {* Ordered Fields *}

lemma positive_imp_inverse_positive: 
assumes a_gt_0: "0 < a"  shows "0 < inverse (a::'a::ordered_field)"
proof -
  have "0 < a * inverse a" 
    by (simp add: a_gt_0 [THEN order_less_imp_not_eq2] zero_less_one)
  thus "0 < inverse a" 
    by (simp add: a_gt_0 [THEN order_less_not_sym] zero_less_mult_iff)
qed

lemma negative_imp_inverse_negative:
  "a < 0 ==> inverse a < (0::'a::ordered_field)"
by (insert positive_imp_inverse_positive [of "-a"], 
    simp add: nonzero_inverse_minus_eq order_less_imp_not_eq)

lemma inverse_le_imp_le:
assumes invle: "inverse a \<le> inverse b" and apos:  "0 < a"
shows "b \<le> (a::'a::ordered_field)"
proof (rule classical)
  assume "~ b \<le> a"
  hence "a < b"  by (simp add: linorder_not_le)
  hence bpos: "0 < b"  by (blast intro: apos order_less_trans)
  hence "a * inverse a \<le> a * inverse b"
    by (simp add: apos invle order_less_imp_le mult_left_mono)
  hence "(a * inverse a) * b \<le> (a * inverse b) * b"
    by (simp add: bpos order_less_imp_le mult_right_mono)
  thus "b \<le> a"  by (simp add: mult_assoc apos bpos order_less_imp_not_eq2)
qed

lemma inverse_positive_imp_positive:
assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
shows "0 < (a::'a::ordered_field)"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < (a::'a::{ordered_field,division_by_zero}))"
apply (cases "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done

lemma inverse_negative_imp_negative:
assumes inv_less_0: "inverse a < 0" and nz:  "a \<noteq> 0"
shows "a < (0::'a::ordered_field)"
proof -
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < (0::'a::{ordered_field,division_by_zero}))"
apply (cases "a = 0", simp)
apply (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)
done

lemma inverse_nonnegative_iff_nonnegative [simp]:
  "(0 \<le> inverse a) = (0 \<le> (a::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "(inverse a \<le> 0) = (a \<le> (0::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])

lemma ordered_field_no_lb: "\<forall> x. \<exists>y. y < (x::'a::ordered_field)"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x] 
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma ordered_field_no_ub: "\<forall> x. \<exists>y. y > (x::'a::ordered_field)"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x] 
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

subsection{*Anti-Monotonicity of @{term inverse}*}

lemma less_imp_inverse_less:
assumes less: "a < b" and apos:  "0 < a"
shows "inverse b < inverse (a::'a::ordered_field)"
proof (rule ccontr)
  assume "~ inverse b < inverse a"
  hence "inverse a \<le> inverse b" by (simp add: linorder_not_less)
  hence "~ (a < b)"
    by (simp add: linorder_not_less inverse_le_imp_le [OF _ apos])
  thus False by (rule notE [OF _ less])
qed

lemma inverse_less_imp_less:
  "[|inverse a < inverse b; 0 < a|] ==> b < (a::'a::ordered_field)"
apply (simp add: order_less_le [of "inverse a"] order_less_le [of "b"])
apply (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq) 
done

text{*Both premises are essential. Consider -1 and 1.*}
lemma inverse_less_iff_less [simp,noatp]:
  "[|0 < a; 0 < b|] ==> (inverse a < inverse b) = (b < (a::'a::ordered_field))"
by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less) 

lemma le_imp_inverse_le:
  "[|a \<le> b; 0 < a|] ==> inverse b \<le> inverse (a::'a::ordered_field)"
by (force simp add: order_le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp,noatp]:
 "[|0 < a; 0 < b|] ==> (inverse a \<le> inverse b) = (b \<le> (a::'a::ordered_field))"
by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le) 


text{*These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.*}
lemma inverse_le_imp_le_neg:
  "[|inverse a \<le> inverse b; b < 0|] ==> b \<le> (a::'a::ordered_field)"
apply (rule classical) 
apply (subgoal_tac "a < 0") 
 prefer 2 apply (force simp add: linorder_not_le intro: order_less_trans) 
apply (insert inverse_le_imp_le [of "-b" "-a"])
apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
done

lemma less_imp_inverse_less_neg:
   "[|a < b; b < 0|] ==> inverse b < inverse (a::'a::ordered_field)"
apply (subgoal_tac "a < 0") 
 prefer 2 apply (blast intro: order_less_trans) 
apply (insert less_imp_inverse_less [of "-b" "-a"])
apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
done

lemma inverse_less_imp_less_neg:
   "[|inverse a < inverse b; b < 0|] ==> b < (a::'a::ordered_field)"
apply (rule classical) 
apply (subgoal_tac "a < 0") 
 prefer 2
 apply (force simp add: linorder_not_less intro: order_le_less_trans) 
apply (insert inverse_less_imp_less [of "-b" "-a"])
apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
done

lemma inverse_less_iff_less_neg [simp,noatp]:
  "[|a < 0; b < 0|] ==> (inverse a < inverse b) = (b < (a::'a::ordered_field))"
apply (insert inverse_less_iff_less [of "-b" "-a"])
apply (simp del: inverse_less_iff_less 
            add: order_less_imp_not_eq nonzero_inverse_minus_eq)
done

lemma le_imp_inverse_le_neg:
  "[|a \<le> b; b < 0|] ==> inverse b \<le> inverse (a::'a::ordered_field)"
by (force simp add: order_le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp,noatp]:
 "[|a < 0; b < 0|] ==> (inverse a \<le> inverse b) = (b \<le> (a::'a::ordered_field))"
by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg) 


subsection{*Inverses and the Number One*}

lemma one_less_inverse_iff:
  "(1 < inverse x) = (0 < x & x < (1::'a::{ordered_field,division_by_zero}))"
proof cases
  assume "0 < x"
    with inverse_less_iff_less [OF zero_less_one, of x]
    show ?thesis by simp
next
  assume notless: "~ (0 < x)"
  have "~ (1 < inverse x)"
  proof
    assume "1 < inverse x"
    also with notless have "... \<le> 0" by (simp add: linorder_not_less)
    also have "... < 1" by (rule zero_less_one) 
    finally show False by auto
  qed
  with notless show ?thesis by simp
qed

lemma inverse_eq_1_iff [simp]:
  "(inverse x = 1) = (x = (1::'a::{field,division_by_zero}))"
by (insert inverse_eq_iff_eq [of x 1], simp) 

lemma one_le_inverse_iff:
  "(1 \<le> inverse x) = (0 < x & x \<le> (1::'a::{ordered_field,division_by_zero}))"
by (force simp add: order_le_less one_less_inverse_iff zero_less_one 
                    eq_commute [of 1]) 

lemma inverse_less_1_iff:
  "(inverse x < 1) = (x \<le> 0 | 1 < (x::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_le [symmetric] one_le_inverse_iff) 

lemma inverse_le_1_iff:
  "(inverse x \<le> 1) = (x \<le> 0 | 1 \<le> (x::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric] one_less_inverse_iff) 


subsection{*Simplification of Inequalities Involving Literal Divisors*}

lemma pos_le_divide_eq: "0 < (c::'a::ordered_field) ==> (a \<le> b/c) = (a*c \<le> b)"
proof -
  assume less: "0<c"
  hence "(a \<le> b/c) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_le_divide_eq: "c < (0::'a::ordered_field) ==> (a \<le> b/c) = (b \<le> a*c)"
proof -
  assume less: "c<0"
  hence "(a \<le> b/c) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma le_divide_eq:
  "(a \<le> b/c) = 
   (if 0 < c then a*c \<le> b
             else if c < 0 then b \<le> a*c
             else  a \<le> (0::'a::{ordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_le_divide_eq neg_le_divide_eq linorder_neq_iff) 
done

lemma pos_divide_le_eq: "0 < (c::'a::ordered_field) ==> (b/c \<le> a) = (b \<le> a*c)"
proof -
  assume less: "0<c"
  hence "(b/c \<le> a) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_le_eq: "c < (0::'a::ordered_field) ==> (b/c \<le> a) = (a*c \<le> b)"
proof -
  assume less: "c<0"
  hence "(b/c \<le> a) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma divide_le_eq:
  "(b/c \<le> a) = 
   (if 0 < c then b \<le> a*c
             else if c < 0 then a*c \<le> b
             else 0 \<le> (a::'a::{ordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_divide_le_eq neg_divide_le_eq linorder_neq_iff) 
done

lemma pos_less_divide_eq:
     "0 < (c::'a::ordered_field) ==> (a < b/c) = (a*c < b)"
proof -
  assume less: "0<c"
  hence "(a < b/c) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right_disj order_less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_less_divide_eq:
 "c < (0::'a::ordered_field) ==> (a < b/c) = (b < a*c)"
proof -
  assume less: "c<0"
  hence "(a < b/c) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right_disj order_less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma less_divide_eq:
  "(a < b/c) = 
   (if 0 < c then a*c < b
             else if c < 0 then b < a*c
             else  a < (0::'a::{ordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_less_divide_eq neg_less_divide_eq linorder_neq_iff) 
done

lemma pos_divide_less_eq:
     "0 < (c::'a::ordered_field) ==> (b/c < a) = (b < a*c)"
proof -
  assume less: "0<c"
  hence "(b/c < a) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right_disj order_less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_less_eq:
 "c < (0::'a::ordered_field) ==> (b/c < a) = (a*c < b)"
proof -
  assume less: "c<0"
  hence "(b/c < a) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right_disj order_less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma divide_less_eq:
  "(b/c < a) = 
   (if 0 < c then b < a*c
             else if c < 0 then a*c < b
             else 0 < (a::'a::{ordered_field,division_by_zero}))"
apply (cases "c=0", simp) 
apply (force simp add: pos_divide_less_eq neg_divide_less_eq linorder_neq_iff) 
done


subsection{*Field simplification*}

text{* Lemmas @{text field_simps} multiply with denominators in in(equations)
if they can be proved to be non-zero (for equations) or positive/negative
(for inequations). Can be too aggressive and is therefore separate from the
more benign @{text algebra_simps}. *}

lemmas field_simps[noatp] = field_eq_simps
  (* multiply ineqn *)
  pos_divide_less_eq neg_divide_less_eq
  pos_less_divide_eq neg_less_divide_eq
  pos_divide_le_eq neg_divide_le_eq
  pos_le_divide_eq neg_le_divide_eq

text{* Lemmas @{text sign_simps} is a first attempt to automate proofs
of positivity/negativity needed for @{text field_simps}. Have not added @{text
sign_simps} to @{text field_simps} because the former can lead to case
explosions. *}

lemmas sign_simps[noatp] = group_simps
  zero_less_mult_iff  mult_less_0_iff

(* Only works once linear arithmetic is installed:
text{*An example:*}
lemma fixes a b c d e f :: "'a::ordered_field"
shows "\<lbrakk>a>b; c<d; e<f; 0 < u \<rbrakk> \<Longrightarrow>
 ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) <
 ((e-f)*(a-b)*(c-d))/((e-f)*(a-b)*(c-d)) + u"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) > 0")
 prefer 2 apply(simp add:sign_simps)
apply(subgoal_tac "(c-d)*(e-f)*(a-b)*u > 0")
 prefer 2 apply(simp add:sign_simps)
apply(simp add:field_simps)
done
*)


subsection{*Division and Signs*}

lemma zero_less_divide_iff:
     "((0::'a::{ordered_field,division_by_zero}) < a/b) = (0 < a & 0 < b | a < 0 & b < 0)"
by (simp add: divide_inverse zero_less_mult_iff)

lemma divide_less_0_iff:
     "(a/b < (0::'a::{ordered_field,division_by_zero})) = 
      (0 < a & b < 0 | a < 0 & 0 < b)"
by (simp add: divide_inverse mult_less_0_iff)

lemma zero_le_divide_iff:
     "((0::'a::{ordered_field,division_by_zero}) \<le> a/b) =
      (0 \<le> a & 0 \<le> b | a \<le> 0 & b \<le> 0)"
by (simp add: divide_inverse zero_le_mult_iff)

lemma divide_le_0_iff:
     "(a/b \<le> (0::'a::{ordered_field,division_by_zero})) =
      (0 \<le> a & b \<le> 0 | a \<le> 0 & 0 \<le> b)"
by (simp add: divide_inverse mult_le_0_iff)

lemma divide_eq_0_iff [simp,noatp]:
     "(a/b = 0) = (a=0 | b=(0::'a::{field,division_by_zero}))"
by (simp add: divide_inverse)

lemma divide_pos_pos:
  "0 < (x::'a::ordered_field) ==> 0 < y ==> 0 < x / y"
by(simp add:field_simps)


lemma divide_nonneg_pos:
  "0 <= (x::'a::ordered_field) ==> 0 < y ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_neg_pos:
  "(x::'a::ordered_field) < 0 ==> 0 < y ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonpos_pos:
  "(x::'a::ordered_field) <= 0 ==> 0 < y ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < (x::'a::ordered_field) ==> y < 0 ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 <= (x::'a::ordered_field) ==> y < 0 ==> x / y <= 0" 
by(simp add:field_simps)

lemma divide_neg_neg:
  "(x::'a::ordered_field) < 0 ==> y < 0 ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonpos_neg:
  "(x::'a::ordered_field) <= 0 ==> y < 0 ==> 0 <= x / y"
by(simp add:field_simps)


subsection{*Cancellation Laws for Division*}

lemma divide_cancel_right [simp,noatp]:
     "(a/c = b/c) = (c = 0 | a = (b::'a::{field,division_by_zero}))"
apply (cases "c=0", simp)
apply (simp add: divide_inverse)
done

lemma divide_cancel_left [simp,noatp]:
     "(c/a = c/b) = (c = 0 | a = (b::'a::{field,division_by_zero}))" 
apply (cases "c=0", simp)
apply (simp add: divide_inverse)
done


subsection {* Division and the Number One *}

text{*Simplify expressions equated with 1*}
lemma divide_eq_1_iff [simp,noatp]:
     "(a/b = 1) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
apply (cases "b=0", simp)
apply (simp add: right_inverse_eq)
done

lemma one_eq_divide_iff [simp,noatp]:
     "(1 = a/b) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
by (simp add: eq_commute [of 1])

lemma zero_eq_1_divide_iff [simp,noatp]:
     "((0::'a::{ordered_field,division_by_zero}) = 1/a) = (a = 0)"
apply (cases "a=0", simp)
apply (auto simp add: nonzero_eq_divide_eq)
done

lemma one_divide_eq_0_iff [simp,noatp]:
     "(1/a = (0::'a::{ordered_field,division_by_zero})) = (a = 0)"
apply (cases "a=0", simp)
apply (insert zero_neq_one [THEN not_sym])
apply (auto simp add: nonzero_divide_eq_eq)
done

text{*Simplify expressions such as @{text "0 < 1/x"} to @{text "0 < x"}*}
lemmas zero_less_divide_1_iff = zero_less_divide_iff [of 1, simplified]
lemmas divide_less_0_1_iff = divide_less_0_iff [of 1, simplified]
lemmas zero_le_divide_1_iff = zero_le_divide_iff [of 1, simplified]
lemmas divide_le_0_1_iff = divide_le_0_iff [of 1, simplified]

declare zero_less_divide_1_iff [simp,noatp]
declare divide_less_0_1_iff [simp,noatp]
declare zero_le_divide_1_iff [simp,noatp]
declare divide_le_0_1_iff [simp,noatp]


subsection {* Ordering Rules for Division *}

lemma divide_strict_right_mono:
     "[|a < b; 0 < c|] ==> a / c < b / (c::'a::ordered_field)"
by (simp add: order_less_imp_not_eq2 divide_inverse mult_strict_right_mono 
              positive_imp_inverse_positive)

lemma divide_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/(c::'a::{ordered_field,division_by_zero})"
by (force simp add: divide_strict_right_mono order_le_less)

lemma divide_right_mono_neg: "(a::'a::{division_by_zero,ordered_field}) <= b 
    ==> c <= 0 ==> b / c <= a / c"
apply (drule divide_right_mono [of _ _ "- c"])
apply auto
done

lemma divide_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a / c < b / (c::'a::ordered_field)"
apply (drule divide_strict_right_mono [of _ _ "-c"], simp)
apply (simp add: order_less_imp_not_eq nonzero_minus_divide_right [symmetric])
done

text{*The last premise ensures that @{term a} and @{term b} 
      have the same sign*}
lemma divide_strict_left_mono:
  "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / (b::'a::ordered_field)"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_strict_right_mono)

lemma divide_left_mono:
  "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / (b::'a::ordered_field)"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_right_mono)

lemma divide_left_mono_neg: "(a::'a::{division_by_zero,ordered_field}) <= b 
    ==> c <= 0 ==> 0 < a * b ==> c / a <= c / b"
  apply (drule divide_left_mono [of _ _ "- c"])
  apply (auto simp add: mult_commute)
done

lemma divide_strict_left_mono_neg:
  "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / (b::'a::ordered_field)"
by(auto simp: field_simps times_divide_eq zero_less_mult_iff mult_strict_right_mono_neg)


text{*Simplify quotients that are compared with the value 1.*}

lemma le_divide_eq_1 [noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(1 \<le> b / a) = ((0 < a & a \<le> b) | (a < 0 & b \<le> a))"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1 [noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(b / a \<le> 1) = ((0 < a & b \<le> a) | (a < 0 & a \<le> b) | a=0)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1 [noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(1 < b / a) = ((0 < a & a < b) | (a < 0 & b < a))"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1 [noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(b / a < 1) = ((0 < a & b < a) | (a < 0 & a < b) | a=0)"
by (auto simp add: divide_less_eq)


subsection{*Conditional Simplification Rules: No Case Splits*}

lemma le_divide_eq_1_pos [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
by (auto simp add: le_divide_eq)

lemma le_divide_eq_1_neg [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1_pos [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
by (auto simp add: divide_le_eq)

lemma divide_le_eq_1_neg [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1_pos [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
by (auto simp add: less_divide_eq)

lemma less_divide_eq_1_neg [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1_pos [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
by (auto simp add: divide_less_eq)

lemma divide_less_eq_1_neg [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "a < 0 \<Longrightarrow> b/a < 1 <-> a < b"
by (auto simp add: divide_less_eq)

lemma eq_divide_eq_1 [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(1 = b/a) = ((a \<noteq> 0 & a = b))"
by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp,noatp]:
  fixes a :: "'a :: {ordered_field,division_by_zero}"
  shows "(b/a = 1) = ((a \<noteq> 0 & a = b))"
by (auto simp add: divide_eq_eq)


subsection {* Reasoning about inequalities with division *}

lemma mult_right_le_one_le: "0 <= (x::'a::ordered_idom) ==> 0 <= y ==> y <= 1
    ==> x * y <= x"
by (auto simp add: mult_compare_simps);

lemma mult_left_le_one_le: "0 <= (x::'a::ordered_idom) ==> 0 <= y ==> y <= 1
    ==> y * x <= x"
by (auto simp add: mult_compare_simps);

lemma mult_imp_div_pos_le: "0 < (y::'a::ordered_field) ==> x <= z * y ==>
    x / y <= z";
by (subst pos_divide_le_eq, assumption+);

lemma mult_imp_le_div_pos: "0 < (y::'a::ordered_field) ==> z * y <= x ==>
    z <= x / y"
by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < (y::'a::ordered_field) ==> x < z * y ==>
    x / y < z"
by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < (y::'a::ordered_field) ==> z * y < x ==>
    z < x / y"
by(simp add:field_simps)

lemma frac_le: "(0::'a::ordered_field) <= x ==> 
    x <= y ==> 0 < w ==> w <= z  ==> x / z <= y / w"
  apply (rule mult_imp_div_pos_le)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_le_div_pos, assumption)
  apply (rule mult_mono)
  apply simp_all
done

lemma frac_less: "(0::'a::ordered_field) <= x ==> 
    x < y ==> 0 < w ==> w <= z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp;
  apply (subst times_divide_eq_left);
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_less_le_imp_less)
  apply simp_all
done

lemma frac_less2: "(0::'a::ordered_field) < x ==> 
    x <= y ==> 0 < w ==> w < z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp_all
  apply (subst times_divide_eq_left);
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_le_less_imp_less)
  apply simp_all
done

text{*It's not obvious whether these should be simprules or not. 
  Their effect is to gather terms into one big fraction, like
  a*b*c / x*y*z. The rationale for that is unclear, but many proofs 
  seem to need them.*}

declare times_divide_eq [simp]


subsection {* Ordered Fields are Dense *}

context ordered_semidom
begin

lemma less_add_one: "a < a + 1"
proof -
  have "a + 0 < a + 1"
    by (blast intro: zero_less_one add_strict_left_mono)
  thus ?thesis by simp
qed

lemma zero_less_two: "0 < 1 + 1"
by (blast intro: less_trans zero_less_one less_add_one)

end

lemma less_half_sum: "a < b ==> a < (a+b) / (1+1::'a::ordered_field)"
by (simp add: field_simps zero_less_two)

lemma gt_half_sum: "a < b ==> (a+b)/(1+1::'a::ordered_field) < b"
by (simp add: field_simps zero_less_two)

instance ordered_field < dense_linear_order
proof
  fix x y :: 'a
  have "x < x + 1" by simp
  then show "\<exists>y. x < y" .. 
  have "x - 1 < x" by simp
  then show "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed


subsection {* Absolute Value *}

context ordered_idom
begin

lemma mult_sgn_abs: "sgn x * abs x = x"
  unfolding abs_if sgn_if by auto

end

lemma abs_one [simp]: "abs 1 = (1::'a::ordered_idom)"
by (simp add: abs_if zero_less_one [THEN order_less_not_sym])

class pordered_ring_abs = pordered_ring + pordered_ab_group_add_abs +
  assumes abs_eq_mult:
    "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0) \<Longrightarrow> \<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"


class lordered_ring = pordered_ring + lordered_ab_group_add_abs
begin

subclass lordered_ab_group_add_meet ..
subclass lordered_ab_group_add_join ..

end

lemma abs_le_mult: "abs (a * b) \<le> (abs a) * (abs (b::'a::lordered_ring))" 
proof -
  let ?x = "pprt a * pprt b - pprt a * nprt b - nprt a * pprt b + nprt a * nprt b"
  let ?y = "pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
  have a: "(abs a) * (abs b) = ?x"
    by (simp only: abs_prts[of a] abs_prts[of b] algebra_simps)
  {
    fix u v :: 'a
    have bh: "\<lbrakk>u = a; v = b\<rbrakk> \<Longrightarrow> 
              u * v = pprt a * pprt b + pprt a * nprt b + 
                      nprt a * pprt b + nprt a * nprt b"
      apply (subst prts[of u], subst prts[of v])
      apply (simp add: algebra_simps) 
      done
  }
  note b = this[OF refl[of a] refl[of b]]
  note addm = add_mono[of "0::'a" _ "0::'a", simplified]
  note addm2 = add_mono[of _ "0::'a" _ "0::'a", simplified]
  have xy: "- ?x <= ?y"
    apply (simp)
    apply (rule_tac y="0::'a" in order_trans)
    apply (rule addm2)
    apply (simp_all add: mult_nonneg_nonneg mult_nonpos_nonpos)
    apply (rule addm)
    apply (simp_all add: mult_nonneg_nonneg mult_nonpos_nonpos)
    done
  have yx: "?y <= ?x"
    apply (simp add:diff_def)
    apply (rule_tac y=0 in order_trans)
    apply (rule addm2, (simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)+)
    apply (rule addm, (simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)+)
    done
  have i1: "a*b <= abs a * abs b" by (simp only: a b yx)
  have i2: "- (abs a * abs b) <= a*b" by (simp only: a b xy)
  show ?thesis
    apply (rule abs_leI)
    apply (simp add: i1)
    apply (simp add: i2[simplified minus_le_iff])
    done
qed

instance lordered_ring \<subseteq> pordered_ring_abs
proof
  fix a b :: "'a\<Colon> lordered_ring"
  assume "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0)"
  show "abs (a*b) = abs a * abs b"
proof -
  have s: "(0 <= a*b) | (a*b <= 0)"
    apply (auto)    
    apply (rule_tac split_mult_pos_le)
    apply (rule_tac contrapos_np[of "a*b <= 0"])
    apply (simp)
    apply (rule_tac split_mult_neg_le)
    apply (insert prems)
    apply (blast)
    done
  have mulprts: "a * b = (pprt a + nprt a) * (pprt b + nprt b)"
    by (simp add: prts[symmetric])
  show ?thesis
  proof cases
    assume "0 <= a * b"
    then show ?thesis
      apply (simp_all add: mulprts abs_prts)
      apply (insert prems)
      apply (auto simp add: 
	algebra_simps 
	iffD1[OF zero_le_iff_zero_nprt] iffD1[OF le_zero_iff_zero_pprt]
	iffD1[OF le_zero_iff_pprt_id] iffD1[OF zero_le_iff_nprt_id])
	apply(drule (1) mult_nonneg_nonpos[of a b], simp)
	apply(drule (1) mult_nonneg_nonpos2[of b a], simp)
      done
  next
    assume "~(0 <= a*b)"
    with s have "a*b <= 0" by simp
    then show ?thesis
      apply (simp_all add: mulprts abs_prts)
      apply (insert prems)
      apply (auto simp add: algebra_simps)
      apply(drule (1) mult_nonneg_nonneg[of a b],simp)
      apply(drule (1) mult_nonpos_nonpos[of a b],simp)
      done
  qed
qed
qed

instance ordered_idom \<subseteq> pordered_ring_abs
by default (auto simp add: abs_if not_less
  equal_neg_zero neg_equal_zero mult_less_0_iff)

lemma abs_mult: "abs (a * b) = abs a * abs (b::'a::ordered_idom)" 
by (simp add: abs_eq_mult linorder_linear)

lemma abs_mult_self: "abs a * abs a = a * (a::'a::ordered_idom)"
by (simp add: abs_if) 

lemma nonzero_abs_inverse:
     "a \<noteq> 0 ==> abs (inverse (a::'a::ordered_field)) = inverse (abs a)"
apply (auto simp add: linorder_neq_iff abs_if nonzero_inverse_minus_eq 
                      negative_imp_inverse_negative)
apply (blast intro: positive_imp_inverse_positive elim: order_less_asym) 
done

lemma abs_inverse [simp]:
     "abs (inverse (a::'a::{ordered_field,division_by_zero})) = 
      inverse (abs a)"
apply (cases "a=0", simp) 
apply (simp add: nonzero_abs_inverse) 
done

lemma nonzero_abs_divide:
     "b \<noteq> 0 ==> abs (a / (b::'a::ordered_field)) = abs a / abs b"
by (simp add: divide_inverse abs_mult nonzero_abs_inverse) 

lemma abs_divide [simp]:
     "abs (a / (b::'a::{ordered_field,division_by_zero})) = abs a / abs b"
apply (cases "b=0", simp) 
apply (simp add: nonzero_abs_divide) 
done

lemma abs_mult_less:
     "[| abs a < c; abs b < d |] ==> abs a * abs b < c*(d::'a::ordered_idom)"
proof -
  assume ac: "abs a < c"
  hence cpos: "0<c" by (blast intro: order_le_less_trans abs_ge_zero)
  assume "abs b < d"
  thus ?thesis by (simp add: ac cpos mult_strict_mono) 
qed

lemmas eq_minus_self_iff[noatp] = equal_neg_zero

lemma less_minus_self_iff: "(a < -a) = (a < (0::'a::ordered_idom))"
  unfolding order_less_le less_eq_neg_nonpos equal_neg_zero ..

lemma abs_less_iff: "(abs a < b) = (a < b & -a < (b::'a::ordered_idom))" 
apply (simp add: order_less_le abs_le_iff)  
apply (auto simp add: abs_if neg_less_eq_nonneg less_eq_neg_nonpos)
done

lemma abs_mult_pos: "(0::'a::ordered_idom) <= x ==> 
    (abs y) * x = abs (y * x)"
  apply (subst abs_mult)
  apply simp
done

lemma abs_div_pos: "(0::'a::{division_by_zero,ordered_field}) < y ==> 
    abs x / y = abs (x / y)"
  apply (subst abs_divide)
  apply (simp add: order_less_imp_le)
done


subsection {* Bounds of products via negative and positive Part *}

lemma mult_le_prts:
  assumes
  "a1 <= (a::'a::lordered_ring)"
  "a <= a2"
  "b1 <= b"
  "b <= b2"
  shows
  "a * b <= pprt a2 * pprt b2 + pprt a1 * nprt b2 + nprt a2 * pprt b1 + nprt a1 * nprt b1"
proof - 
  have "a * b = (pprt a + nprt a) * (pprt b + nprt b)" 
    apply (subst prts[symmetric])+
    apply simp
    done
  then have "a * b = pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
    by (simp add: algebra_simps)
  moreover have "pprt a * pprt b <= pprt a2 * pprt b2"
    by (simp_all add: prems mult_mono)
  moreover have "pprt a * nprt b <= pprt a1 * nprt b2"
  proof -
    have "pprt a * nprt b <= pprt a * nprt b2"
      by (simp add: mult_left_mono prems)
    moreover have "pprt a * nprt b2 <= pprt a1 * nprt b2"
      by (simp add: mult_right_mono_neg prems)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * pprt b <= nprt a2 * pprt b1"
  proof - 
    have "nprt a * pprt b <= nprt a2 * pprt b"
      by (simp add: mult_right_mono prems)
    moreover have "nprt a2 * pprt b <= nprt a2 * pprt b1"
      by (simp add: mult_left_mono_neg prems)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * nprt b <= nprt a1 * nprt b1"
  proof -
    have "nprt a * nprt b <= nprt a * nprt b1"
      by (simp add: mult_left_mono_neg prems)
    moreover have "nprt a * nprt b1 <= nprt a1 * nprt b1"
      by (simp add: mult_right_mono_neg prems)
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by - (rule add_mono | simp)+
qed

lemma mult_ge_prts:
  assumes
  "a1 <= (a::'a::lordered_ring)"
  "a <= a2"
  "b1 <= b"
  "b <= b2"
  shows
  "a * b >= nprt a1 * pprt b2 + nprt a2 * nprt b2 + pprt a1 * pprt b1 + pprt a2 * nprt b1"
proof - 
  from prems have a1:"- a2 <= -a" by auto
  from prems have a2: "-a <= -a1" by auto
  from mult_le_prts[of "-a2" "-a" "-a1" "b1" b "b2", OF a1 a2 prems(3) prems(4), simplified nprt_neg pprt_neg] 
  have le: "- (a * b) <= - nprt a1 * pprt b2 + - nprt a2 * nprt b2 + - pprt a1 * pprt b1 + - pprt a2 * nprt b1" by simp  
  then have "-(- nprt a1 * pprt b2 + - nprt a2 * nprt b2 + - pprt a1 * pprt b1 + - pprt a2 * nprt b1) <= a * b"
    by (simp only: minus_le_iff)
  then show ?thesis by simp
qed

end

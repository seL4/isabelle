(*  Title:      HOL/Rings.thy
    Author:     Gertrud Bauer
    Author:     Steven Obua
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

header {* Rings *}

theory Rings
imports Groups
begin

class semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right[algebra_simps, field_simps]: "(a + b) * c = a * c + b * c"
  assumes distrib_left[algebra_simps, field_simps]: "a * (b + c) = a * b + a * c"
begin

text{*For the @{text combine_numerals} simproc*}
lemma combine_common_factor:
  "a * e + (b * e + c) = (a + b) * e + c"
by (simp add: distrib_right add_ac)

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
  have "0 * a + 0 * a = 0 * a + 0" by (simp add: distrib_right [symmetric])
  thus "0 * a = 0" by (simp only: add_left_cancel)
next
  fix a :: 'a
  have "a * 0 + a * 0 = a * 0 + 0" by (simp add: distrib_left [symmetric])
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
  "b dvd a \<longleftrightarrow> (\<exists>k. a = b * k)"

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

lemma dvd_0_left_iff [no_atp, simp]: "0 dvd a \<longleftrightarrow> a = 0"
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
  ultimately have "b + c = a * (b' + c')" by (simp add: distrib_left)
  then show ?thesis ..
qed

end

class no_zero_divisors = zero + times +
  assumes no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"
begin

lemma divisors_zero:
  assumes "a * b = 0"
  shows "a = 0 \<or> b = 0"
proof (rule classical)
  assume "\<not> (a = 0 \<or> b = 0)"
  then have "a \<noteq> 0" and "b \<noteq> 0" by auto
  with no_zero_divisors have "a * b \<noteq> 0" by blast
  with assms show ?thesis by simp
qed

end

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
by (rule minus_unique) (simp add: distrib_right [symmetric]) 

lemma minus_mult_right: "- (a * b) = a * - b"
by (rule minus_unique) (simp add: distrib_left [symmetric]) 

text{*Extract signs from products*}
lemmas mult_minus_left [simp, no_atp] = minus_mult_left [symmetric]
lemmas mult_minus_right [simp,no_atp] = minus_mult_right [symmetric]

lemma minus_mult_minus [simp]: "- a * - b = a * b"
by simp

lemma minus_mult_commute: "- a * b = a * - b"
by simp

lemma right_diff_distrib[algebra_simps, field_simps]: "a * (b - c) = a * b - a * c"
by (simp add: distrib_left diff_minus)

lemma left_diff_distrib[algebra_simps, field_simps]: "(a - b) * c = a * c - b * c"
by (simp add: distrib_right diff_minus)

lemmas ring_distribs[no_atp] =
  distrib_left distrib_right left_diff_distrib right_diff_distrib

lemma eq_add_iff1:
  "a * e + c = b * e + d \<longleftrightarrow> (a - b) * e + c = d"
by (simp add: algebra_simps)

lemma eq_add_iff2:
  "a * e + c = b * e + d \<longleftrightarrow> c = (b - a) * e + d"
by (simp add: algebra_simps)

end

lemmas ring_distribs[no_atp] =
  distrib_left distrib_right left_diff_distrib right_diff_distrib

class comm_ring = comm_semiring + ab_group_add
begin

subclass ring ..
subclass comm_semiring_0_cancel ..

lemma square_diff_square_factored:
  "x * x - y * y = (x + y) * (x - y)"
  by (simp add: algebra_simps)

end

class ring_1 = ring + zero_neq_one + monoid_mult
begin

subclass semiring_1_cancel ..

lemma square_diff_one_factored:
  "x * x - 1 = (x + 1) * (x - 1)"
  by (simp add: algebra_simps)

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
by (simp only: diff_minus dvd_add dvd_minus_iff)

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
lemma mult_cancel_right [simp, no_atp]:
  "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b"
proof -
  have "(a * c = b * c) = ((a - b) * c = 0)"
    by (simp add: algebra_simps)
  thus ?thesis by (simp add: disj_commute)
qed

lemma mult_cancel_left [simp, no_atp]:
  "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
proof -
  have "(c * a = c * b) = (c * (a - b) = 0)"
    by (simp add: algebra_simps)
  thus ?thesis by simp
qed

end

class ring_1_no_zero_divisors = ring_1 + ring_no_zero_divisors
begin

lemma square_eq_1_iff:
  "x * x = 1 \<longleftrightarrow> x = 1 \<or> x = - 1"
proof -
  have "(x - 1) * (x + 1) = x * x - 1"
    by (simp add: algebra_simps)
  hence "x * x = 1 \<longleftrightarrow> (x - 1) * (x + 1) = 0"
    by simp
  thus ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

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
    by (simp add: eq_neg_iff_add_eq_0)
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

class ordered_semiring = semiring + comm_monoid_add + ordered_ab_semigroup_add +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"
begin

lemma mult_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
apply (erule mult_right_mono [THEN order_trans], assumption)
apply (erule mult_left_mono, assumption)
done

lemma mult_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
apply (rule mult_mono)
apply (fast intro: order_trans)+
done

end

class ordered_cancel_semiring = ordered_semiring + cancel_comm_monoid_add
begin

subclass semiring_0_cancel ..

lemma mult_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * b"
using mult_left_mono [of 0 b a] by simp

lemma mult_nonneg_nonpos: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> a * b \<le> 0"
using mult_left_mono [of b 0 a] by simp

lemma mult_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> a * b \<le> 0"
using mult_right_mono [of a 0 b] by simp

text {* Legacy - use @{text mult_nonpos_nonneg} *}
lemma mult_nonneg_nonpos2: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> b * a \<le> 0" 
by (drule mult_right_mono [of b 0], auto)

lemma split_mult_neg_le: "(0 \<le> a & b \<le> 0) | (a \<le> 0 & 0 \<le> b) \<Longrightarrow> a * b \<le> 0" 
by (auto simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)

end

class linordered_semiring = ordered_semiring + linordered_cancel_ab_semigroup_add
begin

subclass ordered_cancel_semiring ..

subclass ordered_comm_monoid_add ..

lemma mult_left_less_imp_less:
  "c * a < c * b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
by (force simp add: mult_left_mono not_le [symmetric])
 
lemma mult_right_less_imp_less:
  "a * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
by (force simp add: mult_right_mono not_le [symmetric])

end

class linordered_semiring_1 = linordered_semiring + semiring_1
begin

lemma convex_bound_le:
  assumes "x \<le> a" "y \<le> a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y \<le> a"
proof-
  from assms have "u * x + v * y \<le> u * a + v * a"
    by (simp add: add_mono mult_left_mono)
  thus ?thesis using assms unfolding distrib_right[symmetric] by simp
qed

end

class linordered_semiring_strict = semiring + comm_monoid_add + linordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass linordered_semiring
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

lemma mult_pos_pos: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
using mult_strict_right_mono [of a 0 b] by simp

text {* Legacy - use @{text mult_neg_pos} *}
lemma mult_pos_neg2: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> b * a < 0" 
by (drule mult_strict_right_mono [of b 0], auto)

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

class linordered_semiring_1_strict = linordered_semiring_strict + semiring_1
begin

subclass linordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" "y < a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y < a"
proof -
  from assms have "u * x + v * y < u * a + v * a"
    by (cases "u = 0")
       (auto intro!: add_less_le_mono mult_strict_left_mono mult_left_mono)
  thus ?thesis using assms unfolding distrib_right[symmetric] by simp
qed

end

class ordered_comm_semiring = comm_semiring_0 + ordered_ab_semigroup_add + 
  assumes comm_mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
begin

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b" by (rule comm_mult_left_mono)
  thus "a * c \<le> b * c" by (simp only: mult_commute)
qed

end

class ordered_cancel_comm_semiring = ordered_comm_semiring + cancel_comm_monoid_add
begin

subclass comm_semiring_0_cancel ..
subclass ordered_comm_semiring ..
subclass ordered_cancel_semiring ..

end

class linordered_comm_semiring_strict = comm_semiring_0 + linordered_cancel_ab_semigroup_add +
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass linordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" "0 < c"
  thus "c * a < c * b" by (rule comm_mult_strict_left_mono)
  thus "a * c < b * c" by (simp only: mult_commute)
qed

subclass ordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

end

class ordered_ring = ring + ordered_cancel_semiring 
begin

subclass ordered_ab_group_add ..

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
  apply (drule mult_left_mono [of _ _ "- c"])
  apply simp_all
  done

lemma mult_right_mono_neg:
  "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a * c \<le> b * c"
  apply (drule mult_right_mono [of _ _ "- c"])
  apply simp_all
  done

lemma mult_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a * b"
using mult_right_mono_neg [of a 0 b] by simp

lemma split_mult_pos_le:
  "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a * b"
by (auto simp add: mult_nonneg_nonneg mult_nonpos_nonpos)

end

class linordered_ring = ring + linordered_semiring + linordered_ab_group_add + abs_if
begin

subclass ordered_ring ..

subclass ordered_ab_group_add_abs
proof
  fix a b
  show "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
    by (auto simp add: abs_if not_less)
    (auto simp del: minus_add_distrib simp add: minus_add_distrib [symmetric],
     auto intro!: less_imp_le add_neg_neg)
qed (auto simp add: abs_if)

lemma zero_le_square [simp]: "0 \<le> a * a"
  using linear [of 0 a]
  by (auto simp add: mult_nonneg_nonneg mult_nonpos_nonpos)

lemma not_square_less_zero [simp]: "\<not> (a * a < 0)"
  by (simp add: not_less)

end

(* The "strict" suffix can be seen as describing the combination of linordered_ring and no_zero_divisors.
   Basically, linordered_ring + no_zero_divisors = linordered_ring_strict.
 *)
class linordered_ring_strict = ring + linordered_semiring_strict
  + ordered_ab_group_add + abs_if
begin

subclass linordered_ring ..

lemma mult_strict_left_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
using mult_strict_left_mono [of b a "- c"] by simp

lemma mult_strict_right_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
using mult_strict_right_mono [of b a "- c"] by simp

lemma mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
using mult_strict_right_mono_neg [of a 0 b] by simp

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
  apply force
  done

lemma mult_le_0_iff:
  "a * b \<le> 0 \<longleftrightarrow> 0 \<le> a \<and> b \<le> 0 \<or> a \<le> 0 \<and> 0 \<le> b"
  apply (insert zero_le_mult_iff [of "-a" b]) 
  apply force
  done

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

lemma mult_le_cancel_left_pos:
  "0 < c \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> a \<le> b"
by (auto simp: mult_le_cancel_left)

lemma mult_le_cancel_left_neg:
  "c < 0 \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> b \<le> a"
by (auto simp: mult_le_cancel_left)

lemma mult_less_cancel_left_pos:
  "0 < c \<Longrightarrow> c * a < c * b \<longleftrightarrow> a < b"
by (auto simp: mult_less_cancel_left)

lemma mult_less_cancel_left_neg:
  "c < 0 \<Longrightarrow> c * a < c * b \<longleftrightarrow> b < a"
by (auto simp: mult_less_cancel_left)

end

lemmas mult_sign_intros =
  mult_nonneg_nonneg mult_nonneg_nonpos
  mult_nonpos_nonneg mult_nonpos_nonpos
  mult_pos_pos mult_pos_neg
  mult_neg_pos mult_neg_neg

class ordered_comm_ring = comm_ring + ordered_comm_semiring
begin

subclass ordered_ring ..
subclass ordered_cancel_comm_semiring ..

end

class linordered_semidom = comm_semiring_1_cancel + linordered_comm_semiring_strict +
  (*previously linordered_semiring*)
  assumes zero_less_one [simp]: "0 < 1"
begin

lemma pos_add_strict:
  shows "0 < a \<Longrightarrow> b < c \<Longrightarrow> b < a + c"
  using add_strict_mono [of 0 a b c] by simp

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

class linordered_idom = comm_ring_1 +
  linordered_comm_semiring_strict + ordered_ab_group_add +
  abs_if + sgn_if
  (*previously linordered_ring*)
begin

subclass linordered_semiring_1_strict ..
subclass linordered_ring_strict ..
subclass ordered_comm_ring ..
subclass idom ..

subclass linordered_semidom
proof
  have "0 \<le> 1 * 1" by (rule zero_le_square)
  thus "0 < 1" by (simp add: le_less)
qed 

lemma linorder_neqE_linordered_idom:
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
unfolding sgn_if by simp

lemma sgn_1_neg:
  "sgn a = - 1 \<longleftrightarrow> a < 0"
unfolding sgn_if by auto

lemma sgn_pos [simp]:
  "0 < a \<Longrightarrow> sgn a = 1"
unfolding sgn_1_pos .

lemma sgn_neg [simp]:
  "a < 0 \<Longrightarrow> sgn a = - 1"
unfolding sgn_1_neg .

lemma sgn_times:
  "sgn (a * b) = sgn a * sgn b"
by (auto simp add: sgn_if zero_less_mult_iff)

lemma abs_sgn: "\<bar>k\<bar> = k * sgn k"
unfolding sgn_if abs_if by auto

lemma sgn_greater [simp]:
  "0 < sgn a \<longleftrightarrow> 0 < a"
  unfolding sgn_if by auto

lemma sgn_less [simp]:
  "sgn a < 0 \<longleftrightarrow> a < 0"
  unfolding sgn_if by auto

lemma abs_dvd_iff [simp]: "\<bar>m\<bar> dvd k \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

lemma dvd_abs_iff [simp]: "m dvd \<bar>k\<bar> \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

lemma dvd_if_abs_eq:
  "\<bar>l\<bar> = \<bar>k\<bar> \<Longrightarrow> l dvd k"
by(subst abs_dvd_iff[symmetric]) simp

end

text {* Simprules for comparisons where common factors can be cancelled. *}

lemmas mult_compare_simps[no_atp] =
    mult_le_cancel_right mult_le_cancel_left
    mult_le_cancel_right1 mult_le_cancel_right2
    mult_le_cancel_left1 mult_le_cancel_left2
    mult_less_cancel_right mult_less_cancel_left
    mult_less_cancel_right1 mult_less_cancel_right2
    mult_less_cancel_left1 mult_less_cancel_left2
    mult_cancel_right mult_cancel_left
    mult_cancel_right1 mult_cancel_right2
    mult_cancel_left1 mult_cancel_left2

text {* Reasoning about inequalities with division *}

context linordered_semidom
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

context linordered_idom
begin

lemma mult_right_le_one_le:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> x * y \<le> x"
  by (auto simp add: mult_le_cancel_left2)

lemma mult_left_le_one_le:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> y * x \<le> x"
  by (auto simp add: mult_le_cancel_right2)

end

text {* Absolute Value *}

context linordered_idom
begin

lemma mult_sgn_abs:
  "sgn x * \<bar>x\<bar> = x"
  unfolding abs_if sgn_if by auto

lemma abs_one [simp]:
  "\<bar>1\<bar> = 1"
  by (simp add: abs_if)

end

class ordered_ring_abs = ordered_ring + ordered_ab_group_add_abs +
  assumes abs_eq_mult:
    "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0) \<Longrightarrow> \<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"

context linordered_idom
begin

subclass ordered_ring_abs proof
qed (auto simp add: abs_if not_less mult_less_0_iff)

lemma abs_mult:
  "\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>" 
  by (rule abs_eq_mult) auto

lemma abs_mult_self:
  "\<bar>a\<bar> * \<bar>a\<bar> = a * a"
  by (simp add: abs_if) 

lemma abs_mult_less:
  "\<bar>a\<bar> < c \<Longrightarrow> \<bar>b\<bar> < d \<Longrightarrow> \<bar>a\<bar> * \<bar>b\<bar> < c * d"
proof -
  assume ac: "\<bar>a\<bar> < c"
  hence cpos: "0<c" by (blast intro: le_less_trans abs_ge_zero)
  assume "\<bar>b\<bar> < d"
  thus ?thesis by (simp add: ac cpos mult_strict_mono) 
qed

lemma less_minus_self_iff:
  "a < - a \<longleftrightarrow> a < 0"
  by (simp only: less_le less_eq_neg_nonpos equal_neg_zero)

lemma abs_less_iff:
  "\<bar>a\<bar> < b \<longleftrightarrow> a < b \<and> - a < b" 
  by (simp add: less_le abs_le_iff) (auto simp add: abs_if)

lemma abs_mult_pos:
  "0 \<le> x \<Longrightarrow> \<bar>y\<bar> * x = \<bar>y * x\<bar>"
  by (simp add: abs_mult)

end

code_modulename SML
  Rings Arith

code_modulename OCaml
  Rings Arith

code_modulename Haskell
  Rings Arith

end

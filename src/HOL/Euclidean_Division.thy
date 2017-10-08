(*  Title:      HOL/Euclidean_Division.thy
    Author:     Manuel Eberl, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Uniquely determined division in euclidean (semi)rings\<close>

theory Euclidean_Division
  imports Nat_Transfer
begin

subsection \<open>Quotient and remainder in integral domains\<close>

class semidom_modulo = algebraic_semidom + semiring_modulo
begin

lemma mod_0 [simp]: "0 mod a = 0"
  using div_mult_mod_eq [of 0 a] by simp

lemma mod_by_0 [simp]: "a mod 0 = a"
  using div_mult_mod_eq [of a 0] by simp

lemma mod_by_1 [simp]:
  "a mod 1 = 0"
proof -
  from div_mult_mod_eq [of a one] div_by_1 have "a + a mod 1 = a" by simp
  then have "a + a mod 1 = a + 0" by simp
  then show ?thesis by (rule add_left_imp_eq)
qed

lemma mod_self [simp]:
  "a mod a = 0"
  using div_mult_mod_eq [of a a] by simp

lemma dvd_imp_mod_0 [simp]:
  assumes "a dvd b"
  shows "b mod a = 0"
  using assms minus_div_mult_eq_mod [of b a] by simp

lemma mod_0_imp_dvd: 
  assumes "a mod b = 0"
  shows   "b dvd a"
proof -
  have "b dvd ((a div b) * b)" by simp
  also have "(a div b) * b = a"
    using div_mult_mod_eq [of a b] by (simp add: assms)
  finally show ?thesis .
qed

lemma mod_eq_0_iff_dvd:
  "a mod b = 0 \<longleftrightarrow> b dvd a"
  by (auto intro: mod_0_imp_dvd)

lemma dvd_eq_mod_eq_0 [nitpick_unfold, code]:
  "a dvd b \<longleftrightarrow> b mod a = 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma dvd_mod_iff: 
  assumes "c dvd b"
  shows "c dvd a mod b \<longleftrightarrow> c dvd a"
proof -
  from assms have "(c dvd a mod b) \<longleftrightarrow> (c dvd ((a div b) * b + a mod b))" 
    by (simp add: dvd_add_right_iff)
  also have "(a div b) * b + a mod b = a"
    using div_mult_mod_eq [of a b] by simp
  finally show ?thesis .
qed

lemma dvd_mod_imp_dvd:
  assumes "c dvd a mod b" and "c dvd b"
  shows "c dvd a"
  using assms dvd_mod_iff [of c b a] by simp

end

class idom_modulo = idom + semidom_modulo
begin

subclass idom_divide ..

lemma div_diff [simp]:
  "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> (a - b) div c = a div c - b div c"
  using div_add [of _  _ "- b"] by (simp add: dvd_neg_div)

end

  
subsection \<open>Euclidean (semi)rings with explicit division and remainder\<close>
  
class euclidean_semiring = semidom_modulo + normalization_semidom + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  assumes size_0 [simp]: "euclidean_size 0 = 0"
  assumes mod_size_less: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (a * b)"
begin

lemma size_mult_mono': "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (b * a)"
  by (subst mult.commute) (rule size_mult_mono)

lemma euclidean_size_normalize [simp]:
  "euclidean_size (normalize a) = euclidean_size a"
proof (cases "a = 0")
  case True
  then show ?thesis
    by simp
next
  case [simp]: False
  have "euclidean_size (normalize a) \<le> euclidean_size (normalize a * unit_factor a)"
    by (rule size_mult_mono) simp
  moreover have "euclidean_size a \<le> euclidean_size (a * (1 div unit_factor a))"
    by (rule size_mult_mono) simp
  ultimately show ?thesis
    by simp
qed

lemma dvd_euclidean_size_eq_imp_dvd:
  assumes "a \<noteq> 0" and "euclidean_size a = euclidean_size b"
    and "b dvd a" 
  shows "a dvd b"
proof (rule ccontr)
  assume "\<not> a dvd b"
  hence "b mod a \<noteq> 0" using mod_0_imp_dvd [of b a] by blast
  then have "b mod a \<noteq> 0" by (simp add: mod_eq_0_iff_dvd)
  from \<open>b dvd a\<close> have "b dvd b mod a" by (simp add: dvd_mod_iff)
  then obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with \<open>b mod a \<noteq> 0\<close> have "c \<noteq> 0" by auto
  with \<open>b mod a = b * c\<close> have "euclidean_size (b mod a) \<ge> euclidean_size b"
    using size_mult_mono by force
  moreover from \<open>\<not> a dvd b\<close> and \<open>a \<noteq> 0\<close>
  have "euclidean_size (b mod a) < euclidean_size a"
    using mod_size_less by blast
  ultimately show False using \<open>euclidean_size a = euclidean_size b\<close>
    by simp
qed

lemma euclidean_size_times_unit:
  assumes "is_unit a"
  shows   "euclidean_size (a * b) = euclidean_size b"
proof (rule antisym)
  from assms have [simp]: "a \<noteq> 0" by auto
  thus "euclidean_size (a * b) \<ge> euclidean_size b" by (rule size_mult_mono')
  from assms have "is_unit (1 div a)" by simp
  hence "1 div a \<noteq> 0" by (intro notI) simp_all
  hence "euclidean_size (a * b) \<le> euclidean_size ((1 div a) * (a * b))"
    by (rule size_mult_mono')
  also from assms have "(1 div a) * (a * b) = b"
    by (simp add: algebra_simps unit_div_mult_swap)
  finally show "euclidean_size (a * b) \<le> euclidean_size b" .
qed

lemma euclidean_size_unit:
  "is_unit a \<Longrightarrow> euclidean_size a = euclidean_size 1"
  using euclidean_size_times_unit [of a 1] by simp

lemma unit_iff_euclidean_size: 
  "is_unit a \<longleftrightarrow> euclidean_size a = euclidean_size 1 \<and> a \<noteq> 0"
proof safe
  assume A: "a \<noteq> 0" and B: "euclidean_size a = euclidean_size 1"
  show "is_unit a"
    by (rule dvd_euclidean_size_eq_imp_dvd [OF A B]) simp_all
qed (auto intro: euclidean_size_unit)

lemma euclidean_size_times_nonunit:
  assumes "a \<noteq> 0" "b \<noteq> 0" "\<not> is_unit a"
  shows   "euclidean_size b < euclidean_size (a * b)"
proof (rule ccontr)
  assume "\<not>euclidean_size b < euclidean_size (a * b)"
  with size_mult_mono'[OF assms(1), of b] 
    have eq: "euclidean_size (a * b) = euclidean_size b" by simp
  have "a * b dvd b"
    by (rule dvd_euclidean_size_eq_imp_dvd [OF _ eq]) (insert assms, simp_all)
  hence "a * b dvd 1 * b" by simp
  with \<open>b \<noteq> 0\<close> have "is_unit a" by (subst (asm) dvd_times_right_cancel_iff)
  with assms(3) show False by contradiction
qed

lemma dvd_imp_size_le:
  assumes "a dvd b" "b \<noteq> 0" 
  shows   "euclidean_size a \<le> euclidean_size b"
  using assms by (auto elim!: dvdE simp: size_mult_mono)

lemma dvd_proper_imp_size_less:
  assumes "a dvd b" "\<not> b dvd a" "b \<noteq> 0" 
  shows   "euclidean_size a < euclidean_size b"
proof -
  from assms(1) obtain c where "b = a * c" by (erule dvdE)
  hence z: "b = c * a" by (simp add: mult.commute)
  from z assms have "\<not>is_unit c" by (auto simp: mult.commute mult_unit_dvd_iff)
  with z assms show ?thesis
    by (auto intro!: euclidean_size_times_nonunit)
qed

lemma unit_imp_mod_eq_0:
  "a mod b = 0" if "is_unit b"
  using that by (simp add: mod_eq_0_iff_dvd unit_imp_dvd)

end

class euclidean_ring = idom_modulo + euclidean_semiring

  
subsection \<open>Euclidean (semi)rings with cancel rules\<close>

class euclidean_semiring_cancel = euclidean_semiring +
  assumes div_mult_self1 [simp]: "b \<noteq> 0 \<Longrightarrow> (a + c * b) div b = c + a div b"
  and div_mult_mult1 [simp]: "c \<noteq> 0 \<Longrightarrow> (c * a) div (c * b) = a div b"
begin

lemma div_mult_self2 [simp]:
  assumes "b \<noteq> 0"
  shows "(a + b * c) div b = c + a div b"
  using assms div_mult_self1 [of b a c] by (simp add: mult.commute)

lemma div_mult_self3 [simp]:
  assumes "b \<noteq> 0"
  shows "(c * b + a) div b = c + a div b"
  using assms by (simp add: add.commute)

lemma div_mult_self4 [simp]:
  assumes "b \<noteq> 0"
  shows "(b * c + a) div b = c + a div b"
  using assms by (simp add: add.commute)

lemma mod_mult_self1 [simp]: "(a + c * b) mod b = a mod b"
proof (cases "b = 0")
  case True then show ?thesis by simp
next
  case False
  have "a + c * b = (a + c * b) div b * b + (a + c * b) mod b"
    by (simp add: div_mult_mod_eq)
  also from False div_mult_self1 [of b a c] have
    "\<dots> = (c + a div b) * b + (a + c * b) mod b"
      by (simp add: algebra_simps)
  finally have "a = a div b * b + (a + c * b) mod b"
    by (simp add: add.commute [of a] add.assoc distrib_right)
  then have "a div b * b + (a + c * b) mod b = a div b * b + a mod b"
    by (simp add: div_mult_mod_eq)
  then show ?thesis by simp
qed

lemma mod_mult_self2 [simp]:
  "(a + b * c) mod b = a mod b"
  by (simp add: mult.commute [of b])

lemma mod_mult_self3 [simp]:
  "(c * b + a) mod b = a mod b"
  by (simp add: add.commute)

lemma mod_mult_self4 [simp]:
  "(b * c + a) mod b = a mod b"
  by (simp add: add.commute)

lemma mod_mult_self1_is_0 [simp]:
  "b * a mod b = 0"
  using mod_mult_self2 [of 0 b a] by simp

lemma mod_mult_self2_is_0 [simp]:
  "a * b mod b = 0"
  using mod_mult_self1 [of 0 a b] by simp

lemma div_add_self1:
  assumes "b \<noteq> 0"
  shows "(b + a) div b = a div b + 1"
  using assms div_mult_self1 [of b a 1] by (simp add: add.commute)

lemma div_add_self2:
  assumes "b \<noteq> 0"
  shows "(a + b) div b = a div b + 1"
  using assms div_add_self1 [of b a] by (simp add: add.commute)

lemma mod_add_self1 [simp]:
  "(b + a) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by (simp add: add.commute)

lemma mod_add_self2 [simp]:
  "(a + b) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by simp

lemma mod_div_trivial [simp]:
  "a mod b div b = 0"
proof (cases "b = 0")
  assume "b = 0"
  thus ?thesis by simp
next
  assume "b \<noteq> 0"
  hence "a div b + a mod b div b = (a mod b + a div b * b) div b"
    by (rule div_mult_self1 [symmetric])
  also have "\<dots> = a div b"
    by (simp only: mod_div_mult_eq)
  also have "\<dots> = a div b + 0"
    by simp
  finally show ?thesis
    by (rule add_left_imp_eq)
qed

lemma mod_mod_trivial [simp]:
  "a mod b mod b = a mod b"
proof -
  have "a mod b mod b = (a mod b + a div b * b) mod b"
    by (simp only: mod_mult_self1)
  also have "\<dots> = a mod b"
    by (simp only: mod_div_mult_eq)
  finally show ?thesis .
qed

lemma mod_mod_cancel:
  assumes "c dvd b"
  shows "a mod b mod c = a mod c"
proof -
  from \<open>c dvd b\<close> obtain k where "b = c * k"
    by (rule dvdE)
  have "a mod b mod c = a mod (c * k) mod c"
    by (simp only: \<open>b = c * k\<close>)
  also have "\<dots> = (a mod (c * k) + a div (c * k) * k * c) mod c"
    by (simp only: mod_mult_self1)
  also have "\<dots> = (a div (c * k) * (c * k) + a mod (c * k)) mod c"
    by (simp only: ac_simps)
  also have "\<dots> = a mod c"
    by (simp only: div_mult_mod_eq)
  finally show ?thesis .
qed

lemma div_mult_mult2 [simp]:
  "c \<noteq> 0 \<Longrightarrow> (a * c) div (b * c) = a div b"
  by (drule div_mult_mult1) (simp add: mult.commute)

lemma div_mult_mult1_if [simp]:
  "(c * a) div (c * b) = (if c = 0 then 0 else a div b)"
  by simp_all

lemma mod_mult_mult1:
  "(c * a) mod (c * b) = c * (a mod b)"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False
  from div_mult_mod_eq
  have "((c * a) div (c * b)) * (c * b) + (c * a) mod (c * b) = c * a" .
  with False have "c * ((a div b) * b + a mod b) + (c * a) mod (c * b)
    = c * a + c * (a mod b)" by (simp add: algebra_simps)
  with div_mult_mod_eq show ?thesis by simp
qed

lemma mod_mult_mult2:
  "(a * c) mod (b * c) = (a mod b) * c"
  using mod_mult_mult1 [of c a b] by (simp add: mult.commute)

lemma mult_mod_left: "(a mod b) * c = (a * c) mod (b * c)"
  by (fact mod_mult_mult2 [symmetric])

lemma mult_mod_right: "c * (a mod b) = (c * a) mod (c * b)"
  by (fact mod_mult_mult1 [symmetric])

lemma dvd_mod: "k dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd (m mod n)"
  unfolding dvd_def by (auto simp add: mod_mult_mult1)

lemma div_plus_div_distrib_dvd_left:
  "c dvd a \<Longrightarrow> (a + b) div c = a div c + b div c"
  by (cases "c = 0") (auto elim: dvdE)

lemma div_plus_div_distrib_dvd_right:
  "c dvd b \<Longrightarrow> (a + b) div c = a div c + b div c"
  using div_plus_div_distrib_dvd_left [of c b a]
  by (simp add: ac_simps)

named_theorems mod_simps

text \<open>Addition respects modular equivalence.\<close>

lemma mod_add_left_eq [mod_simps]:
  "(a mod c + b) mod c = (a + b) mod c"
proof -
  have "(a + b) mod c = (a div c * c + a mod c + b) mod c"
    by (simp only: div_mult_mod_eq)
  also have "\<dots> = (a mod c + b + a div c * c) mod c"
    by (simp only: ac_simps)
  also have "\<dots> = (a mod c + b) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis
    by (rule sym)
qed

lemma mod_add_right_eq [mod_simps]:
  "(a + b mod c) mod c = (a + b) mod c"
  using mod_add_left_eq [of b c a] by (simp add: ac_simps)

lemma mod_add_eq:
  "(a mod c + b mod c) mod c = (a + b) mod c"
  by (simp add: mod_add_left_eq mod_add_right_eq)

lemma mod_sum_eq [mod_simps]:
  "(\<Sum>i\<in>A. f i mod a) mod a = sum f A mod a"
proof (induct A rule: infinite_finite_induct)
  case (insert i A)
  then have "(\<Sum>i\<in>insert i A. f i mod a) mod a
    = (f i mod a + (\<Sum>i\<in>A. f i mod a)) mod a"
    by simp
  also have "\<dots> = (f i + (\<Sum>i\<in>A. f i mod a) mod a) mod a"
    by (simp add: mod_simps)
  also have "\<dots> = (f i + (\<Sum>i\<in>A. f i) mod a) mod a"
    by (simp add: insert.hyps)
  finally show ?case
    by (simp add: insert.hyps mod_simps)
qed simp_all

lemma mod_add_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a + b) mod c = (a' + b') mod c"
proof -
  have "(a mod c + b mod c) mod c = (a' mod c + b' mod c) mod c"
    unfolding assms ..
  then show ?thesis
    by (simp add: mod_add_eq)
qed

text \<open>Multiplication respects modular equivalence.\<close>

lemma mod_mult_left_eq [mod_simps]:
  "((a mod c) * b) mod c = (a * b) mod c"
proof -
  have "(a * b) mod c = ((a div c * c + a mod c) * b) mod c"
    by (simp only: div_mult_mod_eq)
  also have "\<dots> = (a mod c * b + a div c * b * c) mod c"
    by (simp only: algebra_simps)
  also have "\<dots> = (a mod c * b) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis
    by (rule sym)
qed

lemma mod_mult_right_eq [mod_simps]:
  "(a * (b mod c)) mod c = (a * b) mod c"
  using mod_mult_left_eq [of b c a] by (simp add: ac_simps)

lemma mod_mult_eq:
  "((a mod c) * (b mod c)) mod c = (a * b) mod c"
  by (simp add: mod_mult_left_eq mod_mult_right_eq)

lemma mod_prod_eq [mod_simps]:
  "(\<Prod>i\<in>A. f i mod a) mod a = prod f A mod a"
proof (induct A rule: infinite_finite_induct)
  case (insert i A)
  then have "(\<Prod>i\<in>insert i A. f i mod a) mod a
    = (f i mod a * (\<Prod>i\<in>A. f i mod a)) mod a"
    by simp
  also have "\<dots> = (f i * ((\<Prod>i\<in>A. f i mod a) mod a)) mod a"
    by (simp add: mod_simps)
  also have "\<dots> = (f i * ((\<Prod>i\<in>A. f i) mod a)) mod a"
    by (simp add: insert.hyps)
  finally show ?case
    by (simp add: insert.hyps mod_simps)
qed simp_all

lemma mod_mult_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a * b) mod c = (a' * b') mod c"
proof -
  have "(a mod c * (b mod c)) mod c = (a' mod c * (b' mod c)) mod c"
    unfolding assms ..
  then show ?thesis
    by (simp add: mod_mult_eq)
qed

text \<open>Exponentiation respects modular equivalence.\<close>

lemma power_mod [mod_simps]: 
  "((a mod b) ^ n) mod b = (a ^ n) mod b"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(a mod b) ^ Suc n mod b = (a mod b) * ((a mod b) ^ n mod b) mod b"
    by (simp add: mod_mult_right_eq)
  with Suc show ?case
    by (simp add: mod_mult_left_eq mod_mult_right_eq)
qed

end


class euclidean_ring_cancel = euclidean_ring + euclidean_semiring_cancel
begin

subclass idom_divide ..

lemma div_minus_minus [simp]: "(- a) div (- b) = a div b"
  using div_mult_mult1 [of "- 1" a b] by simp

lemma mod_minus_minus [simp]: "(- a) mod (- b) = - (a mod b)"
  using mod_mult_mult1 [of "- 1" a b] by simp

lemma div_minus_right: "a div (- b) = (- a) div b"
  using div_minus_minus [of "- a" b] by simp

lemma mod_minus_right: "a mod (- b) = - ((- a) mod b)"
  using mod_minus_minus [of "- a" b] by simp

lemma div_minus1_right [simp]: "a div (- 1) = - a"
  using div_minus_right [of a 1] by simp

lemma mod_minus1_right [simp]: "a mod (- 1) = 0"
  using mod_minus_right [of a 1] by simp

text \<open>Negation respects modular equivalence.\<close>

lemma mod_minus_eq [mod_simps]:
  "(- (a mod b)) mod b = (- a) mod b"
proof -
  have "(- a) mod b = (- (a div b * b + a mod b)) mod b"
    by (simp only: div_mult_mod_eq)
  also have "\<dots> = (- (a mod b) + - (a div b) * b) mod b"
    by (simp add: ac_simps)
  also have "\<dots> = (- (a mod b)) mod b"
    by (rule mod_mult_self1)
  finally show ?thesis
    by (rule sym)
qed

lemma mod_minus_cong:
  assumes "a mod b = a' mod b"
  shows "(- a) mod b = (- a') mod b"
proof -
  have "(- (a mod b)) mod b = (- (a' mod b)) mod b"
    unfolding assms ..
  then show ?thesis
    by (simp add: mod_minus_eq)
qed

text \<open>Subtraction respects modular equivalence.\<close>

lemma mod_diff_left_eq [mod_simps]:
  "(a mod c - b) mod c = (a - b) mod c"
  using mod_add_cong [of a c "a mod c" "- b" "- b"]
  by simp

lemma mod_diff_right_eq [mod_simps]:
  "(a - b mod c) mod c = (a - b) mod c"
  using mod_add_cong [of a c a "- b" "- (b mod c)"] mod_minus_cong [of "b mod c" c b]
  by simp

lemma mod_diff_eq:
  "(a mod c - b mod c) mod c = (a - b) mod c"
  using mod_add_cong [of a c "a mod c" "- b" "- (b mod c)"] mod_minus_cong [of "b mod c" c b]
  by simp

lemma mod_diff_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a - b) mod c = (a' - b') mod c"
  using assms mod_add_cong [of a c a' "- b" "- b'"] mod_minus_cong [of b c "b'"]
  by simp

lemma minus_mod_self2 [simp]:
  "(a - b) mod b = a mod b"
  using mod_diff_right_eq [of a b b]
  by (simp add: mod_diff_right_eq)

lemma minus_mod_self1 [simp]:
  "(b - a) mod b = - a mod b"
  using mod_add_self2 [of "- a" b] by simp

lemma mod_eq_dvd_iff:
  "a mod c = b mod c \<longleftrightarrow> c dvd a - b" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "(a mod c - b mod c) mod c = 0"
    by simp
  then show ?Q
    by (simp add: dvd_eq_mod_eq_0 mod_simps)
next
  assume ?Q
  then obtain d where d: "a - b = c * d" ..
  then have "a = c * d + b"
    by (simp add: algebra_simps)
  then show ?P by simp
qed

end

  
subsection \<open>Uniquely determined division\<close>
  
class unique_euclidean_semiring = euclidean_semiring + 
  fixes uniqueness_constraint :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes size_mono_mult:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size a < euclidean_size c
      \<Longrightarrow> euclidean_size (a * b) < euclidean_size (c * b)"
    -- \<open>FIXME justify\<close>
  assumes uniqueness_constraint_mono_mult:
    "uniqueness_constraint a b \<Longrightarrow> uniqueness_constraint (a * c) (b * c)"
  assumes uniqueness_constraint_mod:
    "b \<noteq> 0 \<Longrightarrow> \<not> b dvd a \<Longrightarrow> uniqueness_constraint (a mod b) b"
  assumes div_bounded:
    "b \<noteq> 0 \<Longrightarrow> uniqueness_constraint r b
    \<Longrightarrow> euclidean_size r < euclidean_size b
    \<Longrightarrow> (q * b + r) div b = q"
begin

lemma divmod_cases [case_names divides remainder by0]:
  obtains 
    (divides) q where "b \<noteq> 0"
      and "a div b = q"
      and "a mod b = 0"
      and "a = q * b"
  | (remainder) q r where "b \<noteq> 0" and "r \<noteq> 0"
      and "uniqueness_constraint r b"
      and "euclidean_size r < euclidean_size b"
      and "a div b = q"
      and "a mod b = r"
      and "a = q * b + r"
  | (by0) "b = 0"
proof (cases "b = 0")
  case True
  then show thesis
  by (rule by0)
next
  case False
  show thesis
  proof (cases "b dvd a")
    case True
    then obtain q where "a = b * q" ..
    with \<open>b \<noteq> 0\<close> divides
    show thesis
      by (simp add: ac_simps)
  next
    case False
    then have "a mod b \<noteq> 0"
      by (simp add: mod_eq_0_iff_dvd)
    moreover from \<open>b \<noteq> 0\<close> \<open>\<not> b dvd a\<close> have "uniqueness_constraint (a mod b) b"
      by (rule uniqueness_constraint_mod)
    moreover have "euclidean_size (a mod b) < euclidean_size b"
      using \<open>b \<noteq> 0\<close> by (rule mod_size_less)
    moreover have "a = a div b * b + a mod b"
      by (simp add: div_mult_mod_eq)
    ultimately show thesis
      using \<open>b \<noteq> 0\<close> by (blast intro: remainder)
  qed
qed

lemma div_eqI:
  "a div b = q" if "b \<noteq> 0" "uniqueness_constraint r b"
    "euclidean_size r < euclidean_size b" "q * b + r = a"
proof -
  from that have "(q * b + r) div b = q"
    by (auto intro: div_bounded)
  with that show ?thesis
    by simp
qed

lemma mod_eqI:
  "a mod b = r" if "b \<noteq> 0" "uniqueness_constraint r b"
    "euclidean_size r < euclidean_size b" "q * b + r = a" 
proof -
  from that have "a div b = q"
    by (rule div_eqI)
  moreover have "a div b * b + a mod b = a"
    by (fact div_mult_mod_eq)
  ultimately have "a div b * b + a mod b = a div b * b + r"
    using \<open>q * b + r = a\<close> by simp
  then show ?thesis
    by simp
qed

subclass euclidean_semiring_cancel
proof
  show "(a + c * b) div b = c + a div b" if "b \<noteq> 0" for a b c
  proof (cases a b rule: divmod_cases)
    case by0
    with \<open>b \<noteq> 0\<close> show ?thesis
      by simp
  next
    case (divides q)
    then show ?thesis
      by (simp add: ac_simps)
  next
    case (remainder q r)
    then show ?thesis
      by (auto intro: div_eqI simp add: algebra_simps)
  qed
next
  show"(c * a) div (c * b) = a div b" if "c \<noteq> 0" for a b c
  proof (cases a b rule: divmod_cases)
    case by0
    then show ?thesis
      by simp
  next
    case (divides q)
    with \<open>c \<noteq> 0\<close> show ?thesis
      by (simp add: mult.left_commute [of c])
  next
    case (remainder q r)
    from \<open>b \<noteq> 0\<close> \<open>c \<noteq> 0\<close> have "b * c \<noteq> 0"
      by simp
    from remainder \<open>c \<noteq> 0\<close>
    have "uniqueness_constraint (r * c) (b * c)"
      and "euclidean_size (r * c) < euclidean_size (b * c)"
      by (simp_all add: uniqueness_constraint_mono_mult uniqueness_constraint_mod size_mono_mult)
    with remainder show ?thesis
      by (auto intro!: div_eqI [of _ "c * (a mod b)"] simp add: algebra_simps)
        (use \<open>b * c \<noteq> 0\<close> in simp)
  qed
qed

end

class unique_euclidean_ring = euclidean_ring + unique_euclidean_semiring
begin
  
subclass euclidean_ring_cancel ..

end

end

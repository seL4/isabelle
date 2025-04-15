(*  Title:      HOL/Euclidean_Rgins.thy
    Author:     Manuel Eberl, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Division in euclidean (semi)rings\<close>

theory Euclidean_Rings
  imports Int Lattices_Big
begin

subsection \<open>Euclidean (semi)rings with explicit division and remainder\<close>

class euclidean_semiring = semidom_modulo +
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  assumes size_0 [simp]: "euclidean_size 0 = 0"
  assumes mod_size_less:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (a * b)"
begin

lemma euclidean_size_eq_0_iff [simp]:
  "euclidean_size b = 0 \<longleftrightarrow> b = 0"
proof
  assume "b = 0"
  then show "euclidean_size b = 0"
    by simp
next
  assume "euclidean_size b = 0"
  show "b = 0"
  proof (rule ccontr)
    assume "b \<noteq> 0"
    with mod_size_less have "euclidean_size (b mod b) < euclidean_size b" .
    with \<open>euclidean_size b = 0\<close> show False
      by simp
  qed
qed

lemma euclidean_size_greater_0_iff [simp]:
  "euclidean_size b > 0 \<longleftrightarrow> b \<noteq> 0"
  using euclidean_size_eq_0_iff [symmetric, of b] by safe simp

lemma size_mult_mono': "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (b * a)"
  by (subst mult.commute) (rule size_mult_mono)

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
    by (rule dvd_euclidean_size_eq_imp_dvd [OF _ eq])
       (use assms in simp_all)
  hence "a * b dvd 1 * b" by simp
  with \<open>b \<noteq> 0\<close> have "is_unit a" by (subst (asm) dvd_times_right_cancel_iff)
  with assms(3) show False by contradiction
qed

lemma dvd_imp_size_le:
  assumes "a dvd b" "b \<noteq> 0"
  shows   "euclidean_size a \<le> euclidean_size b"
  using assms by (auto simp: size_mult_mono)

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

lemma mod_eq_self_iff_div_eq_0:
  "a mod b = a \<longleftrightarrow> a div b = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  with div_mult_mod_eq [of a b] show ?Q
    by auto
next
  assume ?Q
  with div_mult_mod_eq [of a b] show ?P
    by simp
qed

lemma coprime_mod_left_iff [simp]:
  "coprime (a mod b) b \<longleftrightarrow> coprime a b" if "b \<noteq> 0"
  by (rule iffI; rule coprimeI)
    (use that in \<open>auto dest!: dvd_mod_imp_dvd coprime_common_divisor simp add: dvd_mod_iff\<close>)

lemma coprime_mod_right_iff [simp]:
  "coprime a (b mod a) \<longleftrightarrow> coprime a b" if "a \<noteq> 0"
  using that coprime_mod_left_iff [of a b] by (simp add: ac_simps)

end

class euclidean_ring = idom_modulo + euclidean_semiring
begin

lemma dvd_diff_commute [ac_simps]:
  "a dvd c - b \<longleftrightarrow> a dvd b - c"
proof -
  have "a dvd c - b \<longleftrightarrow> a dvd (c - b) * - 1"
    by (subst dvd_mult_unit_iff) simp_all
  then show ?thesis
    by simp
qed

end


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
  by (cases "c = 0") auto

lemma div_plus_div_distrib_dvd_right:
  "c dvd b \<Longrightarrow> (a + b) div c = a div c + b div c"
  using div_plus_div_distrib_dvd_left [of c b a]
  by (simp add: ac_simps)

lemma sum_div_partition:
  \<open>(\<Sum>a\<in>A. f a) div b = (\<Sum>a\<in>A \<inter> {a. b dvd f a}. f a div b) + (\<Sum>a\<in>A \<inter> {a. \<not> b dvd f a}. f a) div b\<close>
    if \<open>finite A\<close>
proof -
  have \<open>A = A \<inter> {a. b dvd f a} \<union> A \<inter> {a. \<not> b dvd f a}\<close>
    by auto
  then have \<open>(\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A \<inter> {a. b dvd f a} \<union> A \<inter> {a. \<not> b dvd f a}. f a)\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>a\<in>A \<inter> {a. b dvd f a}. f a) + (\<Sum>a\<in>A \<inter> {a. \<not> b dvd f a}. f a)\<close>
    using \<open>finite A\<close> by (auto intro: sum.union_inter_neutral)
  finally have *: \<open>sum f A = sum f (A \<inter> {a. b dvd f a}) + sum f (A \<inter> {a. \<not> b dvd f a})\<close> .
  define B where B: \<open>B = A \<inter> {a. b dvd f a}\<close>
  with \<open>finite A\<close> have \<open>finite B\<close> and \<open>a \<in> B \<Longrightarrow> b dvd f a\<close> for a
    by simp_all
  then have \<open>(\<Sum>a\<in>B. f a) div b = (\<Sum>a\<in>B. f a div b)\<close> and \<open>b dvd (\<Sum>a\<in>B. f a)\<close>
    by induction (simp_all add: div_plus_div_distrib_dvd_left)
  then show ?thesis using *
    by (simp add: B div_plus_div_distrib_dvd_left)
qed

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

lemma power_diff_power_eq:
  \<open>a ^ m div a ^ n = (if n \<le> m then a ^ (m - n) else 1 div a ^ (n - m))\<close>
    if \<open>a \<noteq> 0\<close>
proof (cases \<open>n \<le> m\<close>)
  case True
  with that power_diff [symmetric, of a n m] show ?thesis by simp
next
  case False
  then obtain q where n: \<open>n = m + Suc q\<close>
    by (auto simp add: not_le dest: less_imp_Suc_add)
  then have \<open>a ^ m div a ^ n = (a ^ m * 1) div (a ^ m * a ^ Suc q)\<close>
    by (simp add: power_add ac_simps)
  moreover from that have \<open>a ^ m \<noteq> 0\<close>
    by simp
  ultimately have \<open>a ^ m div a ^ n = 1 div a ^ Suc q\<close>
    by (subst (asm) div_mult_mult1) simp
  with False n show ?thesis
    by simp
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

lemma mod_eqE:
  assumes "a mod c = b mod c"
  obtains d where "b = a + c * d"
proof -
  from assms have "c dvd a - b"
    by (simp add: mod_eq_dvd_iff)
  then obtain d where "a - b = c * d" ..
  then have "b = a + c * - d"
    by (simp add: algebra_simps)
  with that show thesis .
qed

lemma invertible_coprime:
  "coprime a c" if "a * b mod c = 1"
  by (rule coprimeI) (use that dvd_mod_iff [of _ c "a * b"] in auto)

end


subsection \<open>Uniquely determined division\<close>

class unique_euclidean_semiring = euclidean_semiring +
  assumes euclidean_size_mult: \<open>euclidean_size (a * b) = euclidean_size a * euclidean_size b\<close>
  fixes division_segment :: \<open>'a \<Rightarrow> 'a\<close>
  assumes is_unit_division_segment [simp]: \<open>is_unit (division_segment a)\<close>
    and division_segment_mult:
    \<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> division_segment (a * b) = division_segment a * division_segment b\<close>
    and division_segment_mod:
    \<open>b \<noteq> 0 \<Longrightarrow> \<not> b dvd a \<Longrightarrow> division_segment (a mod b) = division_segment b\<close>
  assumes div_bounded:
    \<open>b \<noteq> 0 \<Longrightarrow> division_segment r = division_segment b
    \<Longrightarrow> euclidean_size r < euclidean_size b
    \<Longrightarrow> (q * b + r) div b = q\<close>
begin

lemma division_segment_not_0 [simp]:
  \<open>division_segment a \<noteq> 0\<close>
  using is_unit_division_segment [of a] is_unitE [of \<open>division_segment a\<close>] by blast

lemma euclidean_relationI [case_names by0 divides euclidean_relation]:
  \<open>(a div b, a mod b) = (q, r)\<close>
    if by0: \<open>b = 0 \<Longrightarrow> q = 0 \<and> r = a\<close>
    and divides: \<open>b \<noteq> 0 \<Longrightarrow> b dvd a \<Longrightarrow> r = 0 \<and> a = q * b\<close>
    and euclidean_relation: \<open>b \<noteq> 0 \<Longrightarrow> \<not> b dvd a \<Longrightarrow> division_segment r = division_segment b
      \<and> euclidean_size r < euclidean_size b \<and> a = q * b + r\<close>
proof (cases \<open>b = 0\<close>)
  case True
  with by0 show ?thesis
    by simp
next
  case False
  show ?thesis
  proof (cases \<open>b dvd a\<close>)
    case True
    with \<open>b \<noteq> 0\<close> divides
    show ?thesis
      by simp
  next
    case False
    with \<open>b \<noteq> 0\<close> euclidean_relation
    have \<open>division_segment r = division_segment b\<close>
      \<open>euclidean_size r < euclidean_size b\<close> \<open>a = q * b + r\<close>
      by simp_all
    from \<open>b \<noteq> 0\<close> \<open>division_segment r = division_segment b\<close>
      \<open>euclidean_size r < euclidean_size b\<close>
    have \<open>(q * b + r) div b = q\<close>
      by (rule div_bounded)
    with \<open>a = q * b + r\<close>
    have \<open>q = a div b\<close>
      by simp
    from \<open>a = q * b + r\<close>
    have \<open>a div b * b + a mod b = q * b + r\<close>
      by (simp add: div_mult_mod_eq)
    with \<open>q = a div b\<close>
    have \<open>q * b + a mod b = q * b + r\<close>
      by simp
    then have \<open>r = a mod b\<close>
      by simp
    with \<open>q = a div b\<close>
    show ?thesis
      by simp
  qed
qed

subclass euclidean_semiring_cancel
proof
  fix a b c
  assume \<open>b \<noteq> 0\<close>
  have \<open>((a + c * b) div b, (a + c * b) mod b) = (c + a div b, a mod b)\<close>
  proof (induction rule: euclidean_relationI)
    case by0
    with \<open>b \<noteq> 0\<close>
    show ?case
      by simp
  next
    case divides
    then show ?case
      by (simp add: algebra_simps dvd_add_left_iff)
  next
    case euclidean_relation
    then have \<open>\<not> b dvd a\<close>
      by (simp add: dvd_add_left_iff)
    have \<open>a mod b + (b * c + b * (a div b)) = b * c + ((a div b) * b + a mod b)\<close>
      by (simp add: ac_simps)
    with \<open>b \<noteq> 0\<close> have *: \<open>a mod b + (b * c + b * (a div b)) = b * c + a\<close>
      by (simp add: div_mult_mod_eq)
    from \<open>\<not> b dvd a\<close> euclidean_relation show ?case
      by (simp_all add: algebra_simps division_segment_mod mod_size_less *)
  qed
  then show \<open>(a + c * b) div b = c + a div b\<close>
    by simp
next
  fix a b c
  assume \<open>c \<noteq> 0\<close>
  have \<open>((c * a) div (c * b), (c * a) mod (c * b)) = (a div b, c * (a mod b))\<close>
  proof (induction rule: euclidean_relationI)
    case by0
    with \<open>c \<noteq> 0\<close> show ?case
      by simp
  next
    case divides
    then show ?case
      by (auto simp add: algebra_simps)
  next
    case euclidean_relation
    then have \<open>b \<noteq> 0\<close> \<open>a mod b \<noteq> 0\<close>
      by (simp_all add: mod_eq_0_iff_dvd)
    have \<open>c * (a mod b) + b * (c * (a div b)) = c * ((a div b) * b + a mod b)\<close>
      by (simp add: algebra_simps)
    with \<open>b \<noteq> 0\<close> have *: \<open>c * (a mod b) + b * (c * (a div b)) = c * a\<close>
      by (simp add: div_mult_mod_eq)
    from \<open>b \<noteq> 0\<close> \<open>c \<noteq> 0\<close> have \<open>euclidean_size c * euclidean_size (a mod b)
      < euclidean_size c * euclidean_size b\<close>
      using mod_size_less [of b a] by simp
    with euclidean_relation \<open>b \<noteq> 0\<close> \<open>a mod b \<noteq> 0\<close> show ?case
      by (simp add: algebra_simps division_segment_mult division_segment_mod euclidean_size_mult *)
  qed
  then show \<open>(c * a) div (c * b) = a div b\<close>
    by simp
qed

lemma div_eq_0_iff:
  \<open>a div b = 0 \<longleftrightarrow> euclidean_size a < euclidean_size b \<or> b = 0\<close> (is "_ \<longleftrightarrow> ?P")
  if \<open>division_segment a = division_segment b\<close>
proof (cases \<open>a = 0 \<or> b = 0\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then have \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>
    by simp_all
  have \<open>a div b = 0 \<longleftrightarrow> euclidean_size a < euclidean_size b\<close>
  proof
    assume \<open>a div b = 0\<close>
    then have \<open>a mod b = a\<close>
      using div_mult_mod_eq [of a b] by simp
    with \<open>b \<noteq> 0\<close> mod_size_less [of b a]
    show \<open>euclidean_size a < euclidean_size b\<close>
      by simp
  next
    assume \<open>euclidean_size a < euclidean_size b\<close>
    have \<open>(a div b, a mod b) = (0, a)\<close>
    proof (induction rule: euclidean_relationI)
      case by0
      show ?case
        by simp
    next
      case divides
      with \<open>euclidean_size a < euclidean_size b\<close> show ?case
        using dvd_imp_size_le [of b a] \<open>a \<noteq> 0\<close> by simp
    next
      case euclidean_relation
      with \<open>euclidean_size a < euclidean_size b\<close> that
      show ?case
        by simp
    qed
    then show \<open>a div b = 0\<close>
      by simp
  qed
  with \<open>b \<noteq> 0\<close> show ?thesis
    by simp
qed

lemma div_mult1_eq:
  \<open>(a * b) div c = a * (b div c) + a * (b mod c) div c\<close>
proof -
  have *: \<open>(a * b) mod c + (a * (c * (b div c)) + c * (a * (b mod c) div c)) = a * b\<close> (is \<open>?A + (?B + ?C) = _\<close>)
  proof -
    have \<open>?A = a * (b mod c) mod c\<close>
      by (simp add: mod_mult_right_eq)
    then have \<open>?C + ?A = a * (b mod c)\<close>
      by (simp add: mult_div_mod_eq)
    then have \<open>?B + (?C + ?A) = a * (c * (b div c) + (b mod c))\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = a * b\<close>
      by (simp add: mult_div_mod_eq)
    finally show ?thesis
      by (simp add: algebra_simps)
  qed
  have \<open>((a * b) div c, (a * b) mod c) = (a * (b div c) + a * (b mod c) div c, (a * b) mod c)\<close>
  proof (induction rule: euclidean_relationI)
    case by0
    then show ?case by simp
  next
    case divides
    with * show ?case
      by (simp add: algebra_simps)
  next
    case euclidean_relation
    with * show ?case
      by (simp add: division_segment_mod mod_size_less algebra_simps)
  qed
  then show ?thesis
    by simp
qed

lemma div_add1_eq:
  \<open>(a + b) div c = a div c + b div c + (a mod c + b mod c) div c\<close>
proof -
  have *: \<open>(a + b) mod c + (c * (a div c) + (c * (b div c) + c * ((a mod c + b mod c) div c))) = a + b\<close>
    (is \<open>?A + (?B + (?C + ?D)) = _\<close>)
  proof -
    have \<open>?A + (?B + (?C + ?D)) = ?A + ?D + (?B + ?C)\<close>
      by (simp add: ac_simps)
    also have \<open>?A + ?D = (a mod c + b mod c) mod c + ?D\<close>
      by (simp add: mod_add_eq)
    also have \<open>\<dots> = a mod c + b mod c\<close>
      by (simp add: mod_mult_div_eq)
    finally have \<open>?A + (?B + (?C + ?D)) = (a mod c + ?B) + (b mod c + ?C)\<close>
      by (simp add: ac_simps)
    then show ?thesis
      by (simp add: mod_mult_div_eq)
  qed
  have \<open>((a + b) div c, (a + b) mod c) = (a div c + b div c + (a mod c + b mod c) div c, (a + b) mod c)\<close>
  proof (induction rule: euclidean_relationI)
    case by0
    then show ?case
      by simp
  next
    case divides
    with * show ?case
      by (simp add: algebra_simps)
  next
    case euclidean_relation
    with * show ?case
      by (simp add: division_segment_mod mod_size_less algebra_simps)
  qed
  then show ?thesis
    by simp
qed

end

class unique_euclidean_ring = euclidean_ring + unique_euclidean_semiring
begin

subclass euclidean_ring_cancel ..

end


subsection \<open>Division on \<^typ>\<open>nat\<close>\<close>

instantiation nat :: normalization_semidom
begin

definition normalize_nat :: \<open>nat \<Rightarrow> nat\<close>
  where [simp]: \<open>normalize = (id :: nat \<Rightarrow> nat)\<close>

definition unit_factor_nat :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>unit_factor n = of_bool (n > 0)\<close> for n :: nat

lemma unit_factor_simps [simp]:
  \<open>unit_factor 0 = (0::nat)\<close>
  \<open>unit_factor (Suc n) = 1\<close>
  by (simp_all add: unit_factor_nat_def)

definition divide_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m div n = (if n = 0 then 0 else Max {k. k * n \<le> m})\<close> for m n :: nat

instance
  by standard (auto simp add: divide_nat_def ac_simps unit_factor_nat_def intro: Max_eqI)

end

lemma coprime_Suc_0_left [simp]:
  "coprime (Suc 0) n"
  using coprime_1_left [of n] by simp

lemma coprime_Suc_0_right [simp]:
  "coprime n (Suc 0)"
  using coprime_1_right [of n] by simp

lemma coprime_common_divisor_nat: "coprime a b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> x = 1"
  for a b :: nat
  by (drule coprime_common_divisor [of _ _ x]) simp_all

instantiation nat :: unique_euclidean_semiring
begin

definition euclidean_size_nat :: \<open>nat \<Rightarrow> nat\<close>
  where [simp]: \<open>euclidean_size_nat = id\<close>

definition division_segment_nat :: \<open>nat \<Rightarrow> nat\<close>
  where [simp]: \<open>division_segment n = 1\<close> for n :: nat

definition modulo_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m mod n = m - (m div n * n)\<close> for m n :: nat

instance proof
  fix m n :: nat
  have ex: "\<exists>k. k * n \<le> l" for l :: nat
    by (rule exI [of _ 0]) simp
  have fin: "finite {k. k * n \<le> l}" if "n > 0" for l
  proof -
    from that have "{k. k * n \<le> l} \<subseteq> {k. k \<le> l}"
      by (cases n) auto
    then show ?thesis
      by (rule finite_subset) simp
  qed
  have mult_div_unfold: "n * (m div n) = Max {l. l \<le> m \<and> n dvd l}"
  proof (cases "n = 0")
    case True
    moreover have "{l. l = 0 \<and> l \<le> m} = {0::nat}"
      by auto
    ultimately show ?thesis
      by simp
  next
    case False
    with ex [of m] fin have "n * Max {k. k * n \<le> m} = Max (times n ` {k. k * n \<le> m})"
      by (auto simp add: nat_mult_max_right intro: hom_Max_commute)
    also have "times n ` {k. k * n \<le> m} = {l. l \<le> m \<and> n dvd l}"
      by (auto simp add: ac_simps elim!: dvdE)
    finally show ?thesis
      using False by (simp add: divide_nat_def ac_simps)
  qed
  have less_eq: "m div n * n \<le> m"
    by (auto simp add: mult_div_unfold ac_simps intro: Max.boundedI)
  then show "m div n * n + m mod n = m"
    by (simp add: modulo_nat_def)
  assume "n \<noteq> 0"
  show "euclidean_size (m mod n) < euclidean_size n"
  proof -
    have "m < Suc (m div n) * n"
    proof (rule ccontr)
      assume "\<not> m < Suc (m div n) * n"
      then have "Suc (m div n) * n \<le> m"
        by (simp add: not_less)
      moreover from \<open>n \<noteq> 0\<close> have "Max {k. k * n \<le> m} < Suc (m div n)"
        by (simp add: divide_nat_def)
      with \<open>n \<noteq> 0\<close> ex fin have "\<And>k. k * n \<le> m \<Longrightarrow> k < Suc (m div n)"
        by auto
      ultimately have "Suc (m div n) < Suc (m div n)"
        by blast
      then show False
        by simp
    qed
    with \<open>n \<noteq> 0\<close> show ?thesis
      by (simp add: modulo_nat_def)
  qed
  show "euclidean_size m \<le> euclidean_size (m * n)"
    using \<open>n \<noteq> 0\<close> by (cases n) simp_all
  fix q r :: nat
  show "(q * n + r) div n = q" if "euclidean_size r < euclidean_size n"
  proof -
    from that have "r < n"
      by simp
    have "k \<le> q" if "k * n \<le> q * n + r" for k
    proof (rule ccontr)
      assume "\<not> k \<le> q"
      then have "q < k"
        by simp
      then obtain l where "k = Suc (q + l)"
        by (auto simp add: less_iff_Suc_add)
      with \<open>r < n\<close> that show False
        by (simp add: algebra_simps)
    qed
    with \<open>n \<noteq> 0\<close> ex fin show ?thesis
      by (auto simp add: divide_nat_def Max_eq_iff)
  qed
qed simp_all

end

lemma euclidean_relation_natI [case_names by0 divides euclidean_relation]:
  \<open>(m div n, m mod n) = (q, r)\<close>
    if by0: \<open>n = 0 \<Longrightarrow> q = 0 \<and> r = m\<close>
    and divides: \<open>n > 0 \<Longrightarrow> n dvd m \<Longrightarrow> r = 0 \<and> m = q * n\<close>
    and euclidean_relation: \<open>n > 0 \<Longrightarrow> \<not> n dvd m \<Longrightarrow> r < n \<and> m = q * n + r\<close> for m n q r :: nat
  by (rule euclidean_relationI) (use that in simp_all)

lemma div_nat_eqI:
  \<open>m div n = q\<close> if \<open>n * q \<le> m\<close> and \<open>m < n * Suc q\<close> for m n q :: nat
proof -
  have \<open>(m div n, m mod n) = (q, m - n * q)\<close>
  proof (induction rule: euclidean_relation_natI)
    case by0
    with that show ?case
      by simp
  next
    case divides
    from \<open>n dvd m\<close> obtain s where \<open>m = n * s\<close> ..
    with \<open>n > 0\<close> that have \<open>s < Suc q\<close>
      by (simp only: mult_less_cancel1)
    with \<open>m = n * s\<close> \<open>n > 0\<close> that have \<open>q = s\<close>
      by simp
    with \<open>m = n * s\<close> show ?case
      by (simp add: ac_simps)
  next
    case euclidean_relation
    with that show ?case
      by (simp add: ac_simps)
  qed
  then show ?thesis
    by simp
qed

lemma mod_nat_eqI:
  \<open>m mod n = r\<close> if \<open>r < n\<close> and \<open>r \<le> m\<close> and \<open>n dvd m - r\<close> for m n r :: nat
proof -
  have \<open>(m div n, m mod n) = ((m - r) div n, r)\<close>
  proof (induction rule: euclidean_relation_natI)
    case by0
    with that show ?case
      by simp
  next
    case divides
    from that dvd_minus_add [of r \<open>m\<close> 1 n]
    have \<open>n dvd m + (n - r)\<close>
      by simp
    with divides have \<open>n dvd n - r\<close>
      by (simp add: dvd_add_right_iff)
    then have \<open>n \<le> n - r\<close>
      by (rule dvd_imp_le) (use \<open>r < n\<close> in simp)
    with \<open>n > 0\<close> have \<open>r = 0\<close>
      by simp
    with \<open>n > 0\<close> that show ?case
      by simp
  next
    case euclidean_relation
    with that show ?case
      by (simp add: ac_simps)
  qed
  then show ?thesis
    by simp
qed

text \<open>Tool support\<close>

ML \<open>
structure Cancel_Div_Mod_Nat = Cancel_Div_Mod
(
  val div_name = \<^const_name>\<open>divide\<close>;
  val mod_name = \<^const_name>\<open>modulo\<close>;
  val mk_binop = HOLogic.mk_binop;
  val dest_plus = HOLogic.dest_bin \<^const_name>\<open>Groups.plus\<close> HOLogic.natT;
  val mk_sum = Arith_Data.mk_sum;
  fun dest_sum tm =
    if HOLogic.is_zero tm then []
    else
      (case try HOLogic.dest_Suc tm of
        SOME t => HOLogic.Suc_zero :: dest_sum t
      | NONE =>
          (case try dest_plus tm of
            SOME (t, u) => dest_sum t @ dest_sum u
          | NONE => [tm]));

  val div_mod_eqs = map mk_meta_eq @{thms cancel_div_mod_rules};

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac
    (Arith_Data.simp_all_tac @{thms add_0_left add_0_right ac_simps})
)
\<close>

simproc_setup cancel_div_mod_nat ("(m::nat) + n") =
  \<open>K Cancel_Div_Mod_Nat.proc\<close>

lemma div_mult_self_is_m [simp]:
  "m * n div n = m" if "n > 0" for m n :: nat
  using that by simp

lemma div_mult_self1_is_m [simp]:
  "n * m div n = m" if "n > 0" for m n :: nat
  using that by simp

lemma mod_less_divisor [simp]:
  "m mod n < n" if "n > 0" for m n :: nat
  using mod_size_less [of n m] that by simp

lemma mod_le_divisor [simp]:
  "m mod n \<le> n" if "n > 0" for m n :: nat
  using that by (auto simp add: le_less)

lemma div_times_less_eq_dividend [simp]:
  "m div n * n \<le> m" for m n :: nat
  by (simp add: minus_mod_eq_div_mult [symmetric])

lemma times_div_less_eq_dividend [simp]:
  "n * (m div n) \<le> m" for m n :: nat
  using div_times_less_eq_dividend [of m n]
  by (simp add: ac_simps)

lemma dividend_less_div_times:
  "m < n + (m div n) * n" if "0 < n" for m n :: nat
proof -
  from that have "m mod n < n"
    by simp
  then show ?thesis
    by (simp add: minus_mod_eq_div_mult [symmetric])
qed

lemma dividend_less_times_div:
  "m < n + n * (m div n)" if "0 < n" for m n :: nat
  using dividend_less_div_times [of n m] that
  by (simp add: ac_simps)

lemma mod_Suc_le_divisor [simp]:
  "m mod Suc n \<le> n"
  using mod_less_divisor [of "Suc n" m] by arith

lemma mod_less_eq_dividend [simp]:
  "m mod n \<le> m" for m n :: nat
proof (rule add_leD2)
  from div_mult_mod_eq have "m div n * n + m mod n = m" .
  then show "m div n * n + m mod n \<le> m" by auto
qed

lemma
  div_less [simp]: "m div n = 0"
  and mod_less [simp]: "m mod n = m"
  if "m < n" for m n :: nat
  using that by (auto intro: div_nat_eqI mod_nat_eqI)

lemma split_div:
  \<open>P (m div n) \<longleftrightarrow>
    (n = 0 \<longrightarrow> P 0) \<and>
    (n \<noteq> 0 \<longrightarrow> (\<forall>i j. j < n \<and> m = n * i + j \<longrightarrow> P i))\<close> (is ?div)
  and split_mod:
  \<open>Q (m mod n) \<longleftrightarrow>
    (n = 0 \<longrightarrow> Q m) \<and>
    (n \<noteq> 0 \<longrightarrow> (\<forall>i j. j < n \<and> m = n * i + j \<longrightarrow> Q j))\<close> (is ?mod)
  for m n :: nat
proof -
  have *: \<open>R (m div n) (m mod n) \<longleftrightarrow>
    (n = 0 \<longrightarrow> R 0 m) \<and>
    (n \<noteq> 0 \<longrightarrow> (\<forall>i j. j < n \<and> m = n * i + j \<longrightarrow> R i j))\<close> for R
    by (cases \<open>n = 0\<close>) auto
  from * [of \<open>\<lambda>q _. P q\<close>] show ?div .
  from * [of \<open>\<lambda>_ r. Q r\<close>] show ?mod .
qed

declare split_div [of _ _ \<open>numeral n\<close>, linarith_split] for n
declare split_mod [of _ _ \<open>numeral n\<close>, linarith_split] for n

lemma split_div':
  "P (m div n) \<longleftrightarrow> n = 0 \<and> P 0 \<or> (\<exists>q. (n * q \<le> m \<and> m < n * Suc q) \<and> P q)"
proof (cases "n = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then have "n * q \<le> m \<and> m < n * Suc q \<longleftrightarrow> m div n = q" for q
    by (auto intro: div_nat_eqI dividend_less_times_div)
  then show ?thesis
    by auto
qed

lemma le_div_geq:
  "m div n = Suc ((m - n) div n)" if "0 < n" and "n \<le> m" for m n :: nat
proof -
  from \<open>n \<le> m\<close> obtain q where "m = n + q"
    by (auto simp add: le_iff_add)
  with \<open>0 < n\<close> show ?thesis
    by (simp add: div_add_self1)
qed

lemma le_mod_geq:
  "m mod n = (m - n) mod n" if "n \<le> m" for m n :: nat
proof -
  from \<open>n \<le> m\<close> obtain q where "m = n + q"
    by (auto simp add: le_iff_add)
  then show ?thesis
    by simp
qed

lemma div_if:
  "m div n = (if m < n \<or> n = 0 then 0 else Suc ((m - n) div n))"
  by (simp add: le_div_geq)

lemma mod_if:
  "m mod n = (if m < n then m else (m - n) mod n)" for m n :: nat
  by (simp add: le_mod_geq)

lemma div_eq_0_iff:
  "m div n = 0 \<longleftrightarrow> m < n \<or> n = 0" for m n :: nat
  by (simp add: div_eq_0_iff)

lemma div_greater_zero_iff:
  "m div n > 0 \<longleftrightarrow> n \<le> m \<and> n > 0" for m n :: nat
  using div_eq_0_iff [of m n] by auto

lemma mod_greater_zero_iff_not_dvd:
  "m mod n > 0 \<longleftrightarrow> \<not> n dvd m" for m n :: nat
  by (simp add: dvd_eq_mod_eq_0)

lemma div_by_Suc_0 [simp]:
  "m div Suc 0 = m"
  using div_by_1 [of m] by simp

lemma mod_by_Suc_0 [simp]:
  "m mod Suc 0 = 0"
  using mod_by_1 [of m] by simp

lemma div2_Suc_Suc [simp]:
  "Suc (Suc m) div 2 = Suc (m div 2)"
  by (simp add: numeral_2_eq_2 le_div_geq)

lemma Suc_n_div_2_gt_zero [simp]:
  "0 < Suc n div 2" if "n > 0" for n :: nat
  using that by (cases n) simp_all

lemma div_2_gt_zero [simp]:
  "0 < n div 2" if "Suc 0 < n" for n :: nat
  using that Suc_n_div_2_gt_zero [of "n - 1"] by simp

lemma mod2_Suc_Suc [simp]:
  "Suc (Suc m) mod 2 = m mod 2"
  by (simp add: numeral_2_eq_2 le_mod_geq)

lemma add_self_div_2 [simp]:
  "(m + m) div 2 = m" for m :: nat
  by (simp add: mult_2 [symmetric])

lemma add_self_mod_2 [simp]:
  "(m + m) mod 2 = 0" for m :: nat
  by (simp add: mult_2 [symmetric])

lemma mod2_gr_0 [simp]:
  "0 < m mod 2 \<longleftrightarrow> m mod 2 = 1" for m :: nat
proof -
  have "m mod 2 < 2"
    by (rule mod_less_divisor) simp
  then have "m mod 2 = 0 \<or> m mod 2 = 1"
    by arith
  then show ?thesis
    by auto
qed

lemma mod_Suc_eq [mod_simps]:
  "Suc (m mod n) mod n = Suc m mod n"
proof -
  have "(m mod n + 1) mod n = (m + 1) mod n"
    by (simp only: mod_simps)
  then show ?thesis
    by simp
qed

lemma mod_Suc_Suc_eq [mod_simps]:
  "Suc (Suc (m mod n)) mod n = Suc (Suc m) mod n"
proof -
  have "(m mod n + 2) mod n = (m + 2) mod n"
    by (simp only: mod_simps)
  then show ?thesis
    by simp
qed

lemma
  Suc_mod_mult_self1 [simp]: "Suc (m + k * n) mod n = Suc m mod n"
  and Suc_mod_mult_self2 [simp]: "Suc (m + n * k) mod n = Suc m mod n"
  and Suc_mod_mult_self3 [simp]: "Suc (k * n + m) mod n = Suc m mod n"
  and Suc_mod_mult_self4 [simp]: "Suc (n * k + m) mod n = Suc m mod n"
  by (subst mod_Suc_eq [symmetric], simp add: mod_simps)+

lemma Suc_0_mod_eq [simp]:
  "Suc 0 mod n = of_bool (n \<noteq> Suc 0)"
  by (cases n) simp_all

lemma div_mult2_eq:
    \<open>m div (n * q) = (m div n) div q\<close> (is ?Q)
  and mod_mult2_eq:
    \<open>m mod (n * q) = n * (m div n mod q) + m mod n\<close> (is ?R)
  for m n q :: nat
proof -
  have \<open>(m div (n * q), m mod (n * q)) = ((m div n) div q, n * (m div n mod q) + m mod n)\<close>
  proof (induction rule: euclidean_relation_natI)
    case by0
    then show ?case
      by auto
  next
    case divides
    from \<open>n * q dvd m\<close> obtain t where \<open>m = n * q * t\<close> ..
    with \<open>n * q > 0\<close> show ?case
      by (simp add: algebra_simps)
  next
    case euclidean_relation
    then have \<open>n > 0\<close> \<open>q > 0\<close>
      by simp_all
    from \<open>n > 0\<close> have \<open>m mod n < n\<close>
      by (rule mod_less_divisor)
    from \<open>q > 0\<close> have \<open>m div n mod q < q\<close>
      by (rule mod_less_divisor)
    then obtain s where \<open>q = Suc (m div n mod q + s)\<close>
      by (blast dest: less_imp_Suc_add)
    moreover have \<open>m mod n + n * (m div n mod q) < n * Suc (m div n mod q + s)\<close>
      using \<open>m mod n < n\<close> by (simp add: add_mult_distrib2)
    ultimately have \<open>m mod n + n * (m div n mod q) < n * q\<close>
      by simp
    then show ?case
      by (simp add: algebra_simps flip: add_mult_distrib2)
  qed
  then show ?Q and ?R
    by simp_all
qed

lemma div_le_mono:
  "m div k \<le> n div k" if "m \<le> n" for m n k :: nat
proof -
  from that obtain q where "n = m + q"
    by (auto simp add: le_iff_add)
  then show ?thesis
    by (simp add: div_add1_eq [of m q k])
qed

text \<open>Antimonotonicity of \<^const>\<open>divide\<close> in second argument\<close>

lemma div_le_mono2:
  "k div n \<le> k div m" if "0 < m" and "m \<le> n" for m n k :: nat
using that proof (induct k arbitrary: m rule: less_induct)
  case (less k)
  show ?case
  proof (cases "n \<le> k")
    case False
    then show ?thesis
      by simp
  next
    case True
    have "(k - n) div n \<le> (k - m) div n"
      using less.prems
      by (blast intro: div_le_mono diff_le_mono2)
    also have "\<dots> \<le> (k - m) div m"
      using \<open>n \<le> k\<close> less.prems less.hyps [of "k - m" m]
      by simp
    finally show ?thesis
      using \<open>n \<le> k\<close> less.prems
      by (simp add: le_div_geq)
  qed
qed

lemma div_le_dividend [simp]:
  "m div n \<le> m" for m n :: nat
  using div_le_mono2 [of 1 n m] by (cases "n = 0") simp_all

lemma div_less_dividend [simp]:
  "m div n < m" if "1 < n" and "0 < m" for m n :: nat
using that proof (induct m rule: less_induct)
  case (less m)
  show ?case
  proof (cases "n < m")
    case False
    with less show ?thesis
      by (cases "n = m") simp_all
  next
    case True
    then show ?thesis
      using less.hyps [of "m - n"] less.prems
      by (simp add: le_div_geq)
  qed
qed

lemma div_eq_dividend_iff:
  "m div n = m \<longleftrightarrow> n = 1" if "m > 0" for m n :: nat
proof
  assume "n = 1"
  then show "m div n = m"
    by simp
next
  assume P: "m div n = m"
  show "n = 1"
  proof (rule ccontr)
    have "n \<noteq> 0"
      by (rule ccontr) (use that P in auto)
    moreover assume "n \<noteq> 1"
    ultimately have "n > 1"
      by simp
    with that have "m div n < m"
      by simp
    with P show False
      by simp
  qed
qed

lemma less_mult_imp_div_less:
  "m div n < i" if "m < i * n" for m n i :: nat
proof -
  from that have "i * n > 0"
    by (cases "i * n = 0") simp_all
  then have "i > 0" and "n > 0"
    by simp_all
  have "m div n * n \<le> m"
    by simp
  then have "m div n * n < i * n"
    using that by (rule le_less_trans)
  with \<open>n > 0\<close> show ?thesis
    by simp
qed

lemma div_less_iff_less_mult:
  \<open>m div q < n \<longleftrightarrow> m < n * q\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  if \<open>q > 0\<close> for m n q :: nat
proof
  assume ?Q then show ?P
    by (rule less_mult_imp_div_less)
next
  assume ?P
  then obtain h where \<open>n = Suc (m div q + h)\<close>
    using less_natE by blast
  moreover have \<open>m < m + (Suc h * q - m mod q)\<close>
    using that by (simp add: trans_less_add1)
  ultimately show ?Q
    by (simp add: algebra_simps flip: minus_mod_eq_mult_div)
qed

lemma less_eq_div_iff_mult_less_eq:
  \<open>m \<le> n div q \<longleftrightarrow> m * q \<le> n\<close> if \<open>q > 0\<close> for m n q :: nat
  using div_less_iff_less_mult [of q n m] that by auto

lemma div_Suc:
  \<open>Suc m div n = (if Suc m mod n = 0 then Suc (m div n) else m div n)\<close>
proof (cases \<open>n = 0 \<or> n = 1\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then have \<open>n > 1\<close>
    by simp
  then have \<open>Suc m div n = m div n + Suc (m mod n) div n\<close>
    using div_add1_eq [of m 1 n] by simp
  also have \<open>Suc (m mod n) div n = of_bool (n dvd Suc m)\<close>
  proof (cases \<open>n dvd Suc m\<close>)
    case False
    moreover have \<open>Suc (m mod n) \<noteq> n\<close>
    proof (rule ccontr)
      assume \<open>\<not> Suc (m mod n) \<noteq> n\<close>
      then have \<open>m mod n = n - Suc 0\<close>
        by simp
      with \<open>n > 1\<close> have \<open>(m + 1) mod n = 0\<close>
        by (subst mod_add_left_eq [symmetric]) simp
      then have \<open>n dvd Suc m\<close>
        by auto
      with False show False ..
    qed
    moreover have \<open>Suc (m mod n) \<le> n\<close>
      using \<open>n > 1\<close> by (simp add: Suc_le_eq)
    ultimately show ?thesis
      by (simp add: div_eq_0_iff)
  next
    case True
    then obtain q where q: \<open>Suc m = n * q\<close> ..
    moreover have \<open>q > 0\<close> by (rule ccontr)
      (use q in simp)
    ultimately have \<open>m mod n = n - Suc 0\<close>
      using \<open>n > 1\<close> mult_le_cancel1 [of n \<open>Suc 0\<close> q]
      by (auto intro: mod_nat_eqI)
    with True \<open>n > 1\<close> show ?thesis
      by simp
  qed
  finally show ?thesis
    by (simp add: mod_greater_zero_iff_not_dvd)
qed

lemma mod_Suc:
  \<open>Suc m mod n = (if Suc (m mod n) = n then 0 else Suc (m mod n))\<close>
proof (cases \<open>n = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  moreover have \<open>Suc m mod n = Suc (m mod n) mod n\<close>
    by (simp add: mod_simps)
  ultimately show ?thesis
    by (auto intro!: mod_nat_eqI intro: neq_le_trans simp add: Suc_le_eq)
qed

lemma Suc_times_mod_eq:
  "Suc (m * n) mod m = 1" if "Suc 0 < m"
  using that by (simp add: mod_Suc)

lemma Suc_times_numeral_mod_eq [simp]:
  "Suc (numeral k * n) mod numeral k = 1" if "numeral k \<noteq> (1::nat)"
  by (rule Suc_times_mod_eq) (use that in simp)

lemma Suc_div_le_mono [simp]:
  "m div n \<le> Suc m div n"
  by (simp add: div_le_mono)

text \<open>These lemmas collapse some needless occurrences of Suc:
  at least three Sucs, since two and fewer are rewritten back to Suc again!
  We already have some rules to simplify operands smaller than 3.\<close>

lemma div_Suc_eq_div_add3 [simp]:
  "m div Suc (Suc (Suc n)) = m div (3 + n)"
  by (simp add: Suc3_eq_add_3)

lemma mod_Suc_eq_mod_add3 [simp]:
  "m mod Suc (Suc (Suc n)) = m mod (3 + n)"
  by (simp add: Suc3_eq_add_3)

lemma Suc_div_eq_add3_div:
  "Suc (Suc (Suc m)) div n = (3 + m) div n"
  by (simp add: Suc3_eq_add_3)

lemma Suc_mod_eq_add3_mod:
  "Suc (Suc (Suc m)) mod n = (3 + m) mod n"
  by (simp add: Suc3_eq_add_3)

lemmas Suc_div_eq_add3_div_numeral [simp] =
  Suc_div_eq_add3_div [of _ "numeral v"] for v

lemmas Suc_mod_eq_add3_mod_numeral [simp] =
  Suc_mod_eq_add3_mod [of _ "numeral v"] for v

lemma (in field_char_0) of_nat_div:
  "of_nat (m div n) = ((of_nat m - of_nat (m mod n)) / of_nat n)"
proof -
  have "of_nat (m div n) = ((of_nat (m div n * n + m mod n) - of_nat (m mod n)) / of_nat n :: 'a)"
    unfolding of_nat_add by (cases "n = 0") simp_all
  then show ?thesis
    by simp
qed

text \<open>An ``induction'' law for modulus arithmetic.\<close>

lemma mod_induct [consumes 3, case_names step]:
  "P m" if "P n" and "n < p" and "m < p"
    and step: "\<And>n. n < p \<Longrightarrow> P n \<Longrightarrow> P (Suc n mod p)"
using \<open>m < p\<close> proof (induct m)
  case 0
  show ?case
  proof (rule ccontr)
    assume "\<not> P 0"
    from \<open>n < p\<close> have "0 < p"
      by simp
    from \<open>n < p\<close> obtain m where "0 < m" and "p = n + m"
      by (blast dest: less_imp_add_positive)
    with \<open>P n\<close> have "P (p - m)"
      by simp
    moreover have "\<not> P (p - m)"
    using \<open>0 < m\<close> proof (induct m)
      case 0
      then show ?case
        by simp
    next
      case (Suc m)
      show ?case
      proof
        assume P: "P (p - Suc m)"
        with \<open>\<not> P 0\<close> have "Suc m < p"
          by (auto intro: ccontr)
        then have "Suc (p - Suc m) = p - m"
          by arith
        moreover from \<open>0 < p\<close> have "p - Suc m < p"
          by arith
        with P step have "P ((Suc (p - Suc m)) mod p)"
          by blast
        ultimately show False
          using \<open>\<not> P 0\<close> Suc.hyps by (cases "m = 0") simp_all
      qed
    qed
    ultimately show False
      by blast
  qed
next
  case (Suc m)
  then have "m < p" and mod: "Suc m mod p = Suc m"
    by simp_all
  from \<open>m < p\<close> have "P m"
    by (rule Suc.hyps)
  with \<open>m < p\<close> have "P (Suc m mod p)"
    by (rule step)
  with mod show ?case
    by simp
qed

lemma funpow_mod_eq: \<^marker>\<open>contributor \<open>Lars Noschinski\<close>\<close>
  \<open>(f ^^ (m mod n)) x = (f ^^ m) x\<close> if \<open>(f ^^ n) x = x\<close>
proof -
  have \<open>(f ^^ m) x = (f ^^ (m mod n + m div n * n)) x\<close>
    by simp
  also have \<open>\<dots> = (f ^^ (m mod n)) (((f ^^ n) ^^ (m div n)) x)\<close>
    by (simp only: funpow_add funpow_mult ac_simps) simp
  also have \<open>((f ^^ n) ^^ q) x = x\<close> for q
    by (induction q) (use \<open>(f ^^ n) x = x\<close> in simp_all)
  finally show ?thesis
    by simp
qed

lemma mod_eq_dvd_iff_nat:
  \<open>m mod q = n mod q \<longleftrightarrow> q dvd m - n\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
    if \<open>m \<ge> n\<close> for m n q :: nat
proof
  assume ?Q
  then obtain s where \<open>m - n = q * s\<close> ..
  with that have \<open>m = q * s + n\<close>
    by simp
  then show ?P
    by simp
next
  assume ?P
  have \<open>m - n = m div q * q + m mod q - (n div q * q + n mod q)\<close>
    by simp
  also have \<open>\<dots> = q * (m div q - n div q)\<close>
    by (simp only: algebra_simps \<open>?P\<close>)
  finally show ?Q ..
qed

lemma mod_eq_iff_dvd_symdiff_nat:
  \<open>m mod q = n mod q \<longleftrightarrow> q dvd nat \<bar>int m - int n\<bar>\<close>
  by (auto simp add: abs_if mod_eq_dvd_iff_nat nat_diff_distrib dest: sym intro: sym)

lemma mod_eq_nat1E:
  fixes m n q :: nat
  assumes "m mod q = n mod q" and "m \<ge> n"
  obtains s where "m = n + q * s"
proof -
  from assms have "q dvd m - n"
    by (simp add: mod_eq_dvd_iff_nat)
  then obtain s where "m - n = q * s" ..
  with \<open>m \<ge> n\<close> have "m = n + q * s"
    by simp
  with that show thesis .
qed

lemma mod_eq_nat2E:
  fixes m n q :: nat
  assumes "m mod q = n mod q" and "n \<ge> m"
  obtains s where "n = m + q * s"
  using assms mod_eq_nat1E [of n q m] by (auto simp add: ac_simps)

lemma nat_mod_eq_iff:
  "(x::nat) mod n = y mod n \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)"  (is "?lhs = ?rhs")
proof
  assume H: "x mod n = y mod n"
  { assume xy: "x \<le> y"
    from H have th: "y mod n = x mod n" by simp
    from mod_eq_nat1E [OF th xy] obtain q where "y = x + n * q" .
    then have "x + n * q = y + n * 0"
      by simp
    then have "\<exists>q1 q2. x + n * q1 = y + n * q2"
      by blast
  }
  moreover
  { assume xy: "y \<le> x"
    from mod_eq_nat1E [OF H xy] obtain q where "x = y + n * q" .
    then have "x + n * 0 = y + n * q"
      by simp
    then have "\<exists>q1 q2. x + n * q1 = y + n * q2"
      by blast
  }
  ultimately show ?rhs using linear[of x y] by blast
next
  assume ?rhs then obtain q1 q2 where q12: "x + n * q1 = y + n * q2" by blast
  hence "(x + n * q1) mod n = (y + n * q2) mod n" by simp
  thus  ?lhs by simp
qed


subsection \<open>Division on \<^typ>\<open>int\<close>\<close>

text \<open>
  The following specification of integer division rounds towards minus infinity
  and is advocated by Donald Knuth. See \cite{leijen01} for an overview and
  terminology of different possibilities to specify integer division;
  there division rounding towards minus infinitiy is named ``F-division''.
\<close>

subsubsection \<open>Basic instantiation\<close>

instantiation int :: "{normalization_semidom, idom_modulo}"
begin

definition normalize_int :: \<open>int \<Rightarrow> int\<close>
  where [simp]: \<open>normalize = (abs :: int \<Rightarrow> int)\<close>

definition unit_factor_int :: \<open>int \<Rightarrow> int\<close>
  where [simp]: \<open>unit_factor = (sgn :: int \<Rightarrow> int)\<close>

definition divide_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k div l = (sgn k * sgn l * int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)
    - of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k))\<close>

lemma divide_int_unfold:
  \<open>(sgn k * int m) div (sgn l * int n) = (sgn k * sgn l * int (m div n)
    - of_bool ((k = 0 \<longleftrightarrow> m = 0) \<and> l \<noteq> 0 \<and> n \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> n dvd m))\<close>
  by (simp add: divide_int_def sgn_mult nat_mult_distrib abs_mult sgn_eq_0_iff ac_simps)

definition modulo_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k mod l = sgn k * int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>) + l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>

lemma modulo_int_unfold:
  \<open>(sgn k * int m) mod (sgn l * int n) =
    sgn k * int (m mod (of_bool (l \<noteq> 0) * n)) + (sgn l * int n) * of_bool ((k = 0 \<longleftrightarrow> m = 0) \<and> sgn k \<noteq> sgn l \<and> \<not> n dvd m)\<close>
  by (auto simp add: modulo_int_def sgn_mult abs_mult)

instance proof
  fix k :: int show "k div 0 = 0"
  by (simp add: divide_int_def)
next
  fix k l :: int
  assume "l \<noteq> 0"
  obtain n m and s t where k: "k = sgn s * int n" and l: "l = sgn t * int m"
    by (blast intro: int_sgnE elim: that)
  then have "k * l = sgn (s * t) * int (n * m)"
    by (simp add: ac_simps sgn_mult)
  with k l \<open>l \<noteq> 0\<close> show "k * l div l = k"
    by (simp only: divide_int_unfold)
      (auto simp add: algebra_simps sgn_mult sgn_1_pos sgn_0_0)
next
  fix k l :: int
  obtain n m and s t where "k = sgn s * int n" and "l = sgn t * int m"
    by (blast intro: int_sgnE elim: that)
  then show "k div l * l + k mod l = k"
    by (simp add: divide_int_unfold modulo_int_unfold algebra_simps modulo_nat_def of_nat_diff)
qed (auto simp add: sgn_mult mult_sgn_abs abs_eq_iff')

end

lemma of_int_div: "b dvd a \<Longrightarrow> of_int (a div b) = (of_int a / of_int b :: 'a :: field_char_0)"
  by (elim dvdE) (auto simp: divide_simps mult_ac)


subsubsection \<open>Algebraic foundations\<close>

lemma coprime_int_iff [simp]:
  "coprime (int m) (int n) \<longleftrightarrow> coprime m n" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  show ?Q
  proof (rule coprimeI)
    fix q
    assume "q dvd m" "q dvd n"
    then have "int q dvd int m" "int q dvd int n"
      by simp_all
    with \<open>?P\<close> have "is_unit (int q)"
      by (rule coprime_common_divisor)
    then show "is_unit q"
      by simp
  qed
next
  assume ?Q
  show ?P
  proof (rule coprimeI)
    fix k
    assume "k dvd int m" "k dvd int n"
    then have "nat \<bar>k\<bar> dvd m" "nat \<bar>k\<bar> dvd n"
      by simp_all
    with \<open>?Q\<close> have "is_unit (nat \<bar>k\<bar>)"
      by (rule coprime_common_divisor)
    then show "is_unit k"
      by simp
  qed
qed

lemma coprime_abs_left_iff [simp]:
  "coprime \<bar>k\<bar> l \<longleftrightarrow> coprime k l" for k l :: int
  using coprime_normalize_left_iff [of k l] by simp

lemma coprime_abs_right_iff [simp]:
  "coprime k \<bar>l\<bar> \<longleftrightarrow> coprime k l" for k l :: int
  using coprime_abs_left_iff [of l k] by (simp add: ac_simps)

lemma coprime_nat_abs_left_iff [simp]:
  "coprime (nat \<bar>k\<bar>) n \<longleftrightarrow> coprime k (int n)"
proof -
  define m where "m = nat \<bar>k\<bar>"
  then have "\<bar>k\<bar> = int m"
    by simp
  moreover have "coprime k (int n) \<longleftrightarrow> coprime \<bar>k\<bar> (int n)"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma coprime_nat_abs_right_iff [simp]:
  "coprime n (nat \<bar>k\<bar>) \<longleftrightarrow> coprime (int n) k"
  using coprime_nat_abs_left_iff [of k n] by (simp add: ac_simps)

lemma coprime_common_divisor_int: "coprime a b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> \<bar>x\<bar> = 1"
  for a b :: int
  by (drule coprime_common_divisor [of _ _ x]) simp_all


subsubsection \<open>Basic conversions\<close>

lemma div_abs_eq_div_nat:
  "\<bar>k\<bar> div \<bar>l\<bar> = int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)"
  by (auto simp add: divide_int_def)

lemma div_eq_div_abs:
  \<open>k div l = sgn k * sgn l * (\<bar>k\<bar> div \<bar>l\<bar>)
    - of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: divide_int_def [of k l] div_abs_eq_div_nat)

lemma div_abs_eq:
  \<open>\<bar>k\<bar> div \<bar>l\<bar> = sgn k * sgn l * (k div l + of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k))\<close>
  for k l :: int
  by (simp add: div_eq_div_abs [of k l] ac_simps)

lemma mod_abs_eq_div_nat:
  "\<bar>k\<bar> mod \<bar>l\<bar> = int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)"
  by (simp add: modulo_int_def)

lemma mod_eq_mod_abs:
  \<open>k mod l = sgn k * (\<bar>k\<bar> mod \<bar>l\<bar>) + l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: modulo_int_def [of k l] mod_abs_eq_div_nat)

lemma mod_abs_eq:
  \<open>\<bar>k\<bar> mod \<bar>l\<bar> = sgn k * (k mod l - l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k))\<close>
  for k l :: int
  by (auto simp: mod_eq_mod_abs [of k l])

lemma div_sgn_abs_cancel:
  fixes k l v :: int
  assumes "v \<noteq> 0"
  shows "(sgn v * \<bar>k\<bar>) div (sgn v * \<bar>l\<bar>) = \<bar>k\<bar> div \<bar>l\<bar>"
  using assms by (simp add: sgn_mult abs_mult sgn_0_0
    divide_int_def [of "sgn v * \<bar>k\<bar>" "sgn v * \<bar>l\<bar>"] flip: div_abs_eq_div_nat)

lemma div_eq_sgn_abs:
  fixes k l v :: int
  assumes "sgn k = sgn l"
  shows "k div l = \<bar>k\<bar> div \<bar>l\<bar>"
  using assms by (auto simp add: div_abs_eq)

lemma div_dvd_sgn_abs:
  fixes k l :: int
  assumes "l dvd k"
  shows "k div l = (sgn k * sgn l) * (\<bar>k\<bar> div \<bar>l\<bar>)"
  using assms by (auto simp add: div_abs_eq ac_simps)

lemma div_noneq_sgn_abs:
  fixes k l :: int
  assumes "l \<noteq> 0"
  assumes "sgn k \<noteq> sgn l"
  shows "k div l = - (\<bar>k\<bar> div \<bar>l\<bar>) - of_bool (\<not> l dvd k)"
  using assms by (auto simp add: div_abs_eq ac_simps sgn_0_0 dest!: sgn_not_eq_imp)


subsubsection \<open>Euclidean division\<close>

instantiation int :: unique_euclidean_ring
begin

definition euclidean_size_int :: "int \<Rightarrow> nat"
  where [simp]: "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

definition division_segment_int :: "int \<Rightarrow> int"
  where "division_segment_int k = (if k \<ge> 0 then 1 else - 1)"

lemma division_segment_eq_sgn:
  "division_segment k = sgn k" if "k \<noteq> 0" for k :: int
  using that by (simp add: division_segment_int_def)

lemma abs_division_segment [simp]:
  "\<bar>division_segment k\<bar> = 1" for k :: int
  by (simp add: division_segment_int_def)

lemma abs_mod_less:
  "\<bar>k mod l\<bar> < \<bar>l\<bar>" if "l \<noteq> 0" for k l :: int
proof -
  obtain n m and s t where "k = sgn s * int n" and "l = sgn t * int m"
    by (blast intro: int_sgnE elim: that)
  with that show ?thesis
    by (auto simp add: modulo_int_unfold abs_mult mod_greater_zero_iff_not_dvd
        simp flip: right_diff_distrib dest!: sgn_not_eq_imp)
      (simp add: sgn_0_0)
qed

lemma sgn_mod:
  "sgn (k mod l) = sgn l" if "l \<noteq> 0" "\<not> l dvd k" for k l :: int
proof -
  obtain n m and s t where "k = sgn s * int n" and "l = sgn t * int m"
    by (blast intro: int_sgnE elim: that)
  with that show ?thesis
    by (auto simp add: modulo_int_unfold sgn_mult mod_greater_zero_iff_not_dvd
      simp flip: right_diff_distrib dest!: sgn_not_eq_imp)
qed

instance proof
  fix k l :: int
  show "division_segment (k mod l) = division_segment l" if
    "l \<noteq> 0" and "\<not> l dvd k"
    using that by (simp add: division_segment_eq_sgn dvd_eq_mod_eq_0 sgn_mod)
next
  fix l q r :: int
  obtain n m and s t
     where l: "l = sgn s * int n" and q: "q = sgn t * int m"
    by (blast intro: int_sgnE elim: that)
  assume \<open>l \<noteq> 0\<close>
  with l have "s \<noteq> 0" and "n > 0"
    by (simp_all add: sgn_0_0)
  assume "division_segment r = division_segment l"
  moreover have "r = sgn r * \<bar>r\<bar>"
    by (simp add: sgn_mult_abs)
  moreover define u where "u = nat \<bar>r\<bar>"
  ultimately have "r = sgn l * int u"
    using division_segment_eq_sgn \<open>l \<noteq> 0\<close> by (cases "r = 0") simp_all
  with l \<open>n > 0\<close> have r: "r = sgn s * int u"
    by (simp add: sgn_mult)
  assume "euclidean_size r < euclidean_size l"
  with l r \<open>s \<noteq> 0\<close> have "u < n"
    by (simp add: abs_mult)
  show "(q * l + r) div l = q"
  proof (cases "q = 0 \<or> r = 0")
    case True
    then show ?thesis
    proof
      assume "q = 0"
      then show ?thesis
        using l r \<open>u < n\<close> by (simp add: divide_int_unfold)
    next
      assume "r = 0"
      from \<open>r = 0\<close> have *: "q * l + r = sgn (t * s) * int (n * m)"
        using q l by (simp add: ac_simps sgn_mult)
      from \<open>s \<noteq> 0\<close> \<open>n > 0\<close> show ?thesis
        by (simp only: *, simp only: * q l divide_int_unfold)
          (auto simp add: sgn_mult ac_simps)
    qed
  next
    case False
    with q r have "t \<noteq> 0" and "m > 0" and "s \<noteq> 0" and "u > 0"
      by (simp_all add: sgn_0_0)
    moreover from \<open>0 < m\<close> \<open>u < n\<close> have "u \<le> m * n"
      using mult_le_less_imp_less [of 1 m u n] by simp
    ultimately have *: "q * l + r = sgn (s * t)
      * int (if t < 0 then m * n - u else m * n + u)"
      using l q r
      by (simp add: sgn_mult algebra_simps of_nat_diff)
    have "(m * n - u) div n = m - 1" if "u > 0"
      using \<open>0 < m\<close> \<open>u < n\<close> that
      by (auto intro: div_nat_eqI simp add: algebra_simps)
    moreover have "n dvd m * n - u \<longleftrightarrow> n dvd u"
      using \<open>u \<le> m * n\<close> dvd_diffD1 [of n "m * n" u]
      by auto
    ultimately show ?thesis
      using \<open>s \<noteq> 0\<close> \<open>m > 0\<close> \<open>u > 0\<close> \<open>u < n\<close> \<open>u \<le> m * n\<close>
      by (simp only: *, simp only: l q divide_int_unfold)
        (auto simp add: sgn_mult sgn_0_0 sgn_1_pos algebra_simps dest: dvd_imp_le)
  qed
qed (use mult_le_mono2 [of 1] in \<open>auto simp add: division_segment_int_def not_le zero_less_mult_iff mult_less_0_iff abs_mult sgn_mult abs_mod_less sgn_mod nat_mult_distrib\<close>)

end

lemma euclidean_relation_intI [case_names by0 divides euclidean_relation]:
  \<open>(k div l, k mod l) = (q, r)\<close>
    if by0': \<open>l = 0 \<Longrightarrow> q = 0 \<and> r = k\<close>
    and divides': \<open>l \<noteq> 0 \<Longrightarrow> l dvd k \<Longrightarrow> r = 0 \<and> k = q * l\<close>
    and euclidean_relation': \<open>l \<noteq> 0 \<Longrightarrow> \<not> l dvd k \<Longrightarrow> sgn r = sgn l
      \<and> \<bar>r\<bar> < \<bar>l\<bar> \<and> k = q * l + r\<close> for k l :: int
proof (induction rule: euclidean_relationI)
  case by0
  then show ?case
    by (rule by0')
next
  case divides
  then show ?case
    by (rule divides')
next
  case euclidean_relation
  with euclidean_relation' have \<open>sgn r = sgn l\<close> \<open>\<bar>r\<bar> < \<bar>l\<bar>\<close> \<open>k = q * l + r\<close>
    by simp_all
  from \<open>sgn r = sgn l\<close> \<open>l \<noteq> 0\<close> have \<open>division_segment r = division_segment l\<close>
    by (simp add: division_segment_int_def sgn_if split: if_splits)
  with \<open>\<bar>r\<bar> < \<bar>l\<bar>\<close> \<open>k = q * l + r\<close>
  show ?case
    by simp
qed


subsubsection \<open>Trivial reduction steps\<close>

lemma div_pos_pos_trivial [simp]:
  "k div l = 0" if "k \<ge> 0" and "k < l" for k l :: int
  using that by (simp add: unique_euclidean_semiring_class.div_eq_0_iff division_segment_int_def)

lemma mod_pos_pos_trivial [simp]:
  "k mod l = k" if "k \<ge> 0" and "k < l" for k l :: int
  using that by (simp add: mod_eq_self_iff_div_eq_0)

lemma div_neg_neg_trivial [simp]:
  "k div l = 0" if "k \<le> 0" and "l < k" for k l :: int
  using that by (cases "k = 0") (simp, simp add: unique_euclidean_semiring_class.div_eq_0_iff division_segment_int_def)

lemma mod_neg_neg_trivial [simp]:
  "k mod l = k" if "k \<le> 0" and "l < k" for k l :: int
  using that by (simp add: mod_eq_self_iff_div_eq_0)

lemma
  div_pos_neg_trivial: \<open>k div l = - 1\<close>  (is ?Q)
  and mod_pos_neg_trivial: \<open>k mod l = k + l\<close>  (is ?R)
    if \<open>0 < k\<close> and \<open>k + l \<le> 0\<close> for k l :: int
proof -
  from that have \<open>l < 0\<close>
    by simp
  have \<open>(k div l, k mod l) = (- 1, k + l)\<close>
  proof (induction rule: euclidean_relation_intI)
    case by0
    with \<open>l < 0\<close> show ?case
      by simp
  next
    case divides
    from \<open>l dvd k\<close> obtain j where \<open>k = l * j\<close> ..
    with \<open>l < 0\<close> \<open>0 < k\<close> have \<open>j < 0\<close>
      by (simp add: zero_less_mult_iff)
    moreover from \<open>k + l \<le> 0\<close> \<open>k = l * j\<close> have \<open>l * (j + 1) \<le> 0\<close>
      by (simp add: algebra_simps)
    with \<open>l < 0\<close> have \<open>j + 1 \<ge> 0\<close>
      by (simp add: mult_le_0_iff)
    with \<open>j < 0\<close> have \<open>j = - 1\<close>
      by simp
    with \<open>k = l * j\<close> show ?case
      by simp
  next
    case euclidean_relation
    with \<open>k + l \<le> 0\<close> have \<open>k + l < 0\<close>
      by (auto simp add: less_le add_eq_0_iff)
    with \<open>0 < k\<close> show ?case
      by simp
  qed
  then show ?Q and ?R
    by simp_all
qed

text \<open>There is neither \<open>div_neg_pos_trivial\<close> nor \<open>mod_neg_pos_trivial\<close>
  because \<^term>\<open>0 div l = 0\<close> would supersede it.\<close>


subsubsection \<open>More uniqueness rules\<close>

lemma
  fixes a b q r :: int
  assumes \<open>a = b * q + r\<close> \<open>0 \<le> r\<close> \<open>r < b\<close>
  shows int_div_pos_eq:
      \<open>a div b = q\<close> (is ?Q)
    and int_mod_pos_eq:
      \<open>a mod b = r\<close> (is ?R)
proof -
  have \<open>(a div b, a mod b) = (q, r)\<close>
    by (induction rule: euclidean_relation_intI)
      (use assms in \<open>auto simp add: ac_simps dvd_add_left_iff sgn_1_pos le_less dest: zdvd_imp_le\<close>)
  then show ?Q and ?R
    by simp_all
qed

lemma int_div_neg_eq:
  \<open>a div b = q\<close> if \<open>a = b * q + r\<close> \<open>r \<le> 0\<close> \<open>b < r\<close> for a b q r :: int
  using that int_div_pos_eq [of a \<open>- b\<close> \<open>- q\<close> \<open>- r\<close>] by simp_all

lemma int_mod_neg_eq:
  \<open>a mod b = r\<close> if \<open>a = b * q + r\<close> \<open>r \<le> 0\<close> \<open>b < r\<close> for a b q r :: int
  using that int_div_neg_eq [of a b q r] by simp


subsubsection \<open>Laws for unary minus\<close>

lemma zmod_zminus1_not_zero:
  fixes k l :: int
  shows "- k mod l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zmod_zminus2_not_zero:
  fixes k l :: int
  shows "k mod - l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zdiv_zminus1_eq_if:
  \<open>(- a) div b = (if a mod b = 0 then - (a div b) else - (a div b) - 1)\<close>
  if \<open>b \<noteq> 0\<close> for a b :: int
  using that sgn_not_eq_imp [of b \<open>- a\<close>]
  by (cases \<open>a = 0\<close>) (auto simp add: div_eq_div_abs [of \<open>- a\<close> b] div_eq_div_abs [of a b] sgn_eq_0_iff)

lemma zdiv_zminus2_eq_if:
  \<open>a div (- b) = (if a mod b = 0 then - (a div b) else - (a div b) - 1)\<close>
  if \<open>b \<noteq> 0\<close> for a b :: int
  using that by (auto simp add: zdiv_zminus1_eq_if div_minus_right)

lemma zmod_zminus1_eq_if:
  \<open>(- a) mod b = (if a mod b = 0 then 0 else b - (a mod b))\<close>
  for a b :: int
  by (cases \<open>b = 0\<close>)
    (auto simp flip: minus_div_mult_eq_mod simp add: zdiv_zminus1_eq_if algebra_simps)

lemma zmod_zminus2_eq_if:
  \<open>a mod (- b) = (if a mod b = 0 then 0 else (a mod b) - b)\<close>
  for a b :: int
  by (auto simp add: zmod_zminus1_eq_if mod_minus_right)


subsubsection \<open>Borders\<close>

lemma pos_mod_bound [simp]:
  "k mod l < l" if "l > 0" for k l :: int
proof -
  obtain m and s where "k = sgn s * int m"
    by (rule int_sgnE)
  moreover from that obtain n where "l = sgn 1 * int n"
    by (cases l) simp_all
  moreover from this that have "n > 0"
    by simp
  ultimately show ?thesis
    by (simp only: modulo_int_unfold)
      (auto simp add: mod_greater_zero_iff_not_dvd sgn_1_pos)
qed

lemma neg_mod_bound [simp]:
  "l < k mod l" if "l < 0" for k l :: int
proof -
  obtain m and s where "k = sgn s * int m"
    by (rule int_sgnE)
  moreover from that obtain q where "l = sgn (- 1) * int (Suc q)"
    by (cases l) simp_all
  moreover define n where "n = Suc q"
  then have "Suc q = n"
    by simp
  ultimately show ?thesis
    by (simp only: modulo_int_unfold)
      (auto simp add: mod_greater_zero_iff_not_dvd sgn_1_neg)
qed

lemma pos_mod_sign [simp]:
  "0 \<le> k mod l" if "l > 0" for k l :: int
proof -
  obtain m and s where "k = sgn s * int m"
    by (rule int_sgnE)
  moreover from that obtain n where "l = sgn 1 * int n"
    by (cases l) auto
  moreover from this that have "n > 0"
    by simp
  ultimately show ?thesis
    by (simp only: modulo_int_unfold) (auto simp add: sgn_1_pos)
qed

lemma neg_mod_sign [simp]:
  "k mod l \<le> 0" if "l < 0" for k l :: int
proof -
  obtain m and s where "k = sgn s * int m"
    by (rule int_sgnE)
  moreover from that obtain q where "l = sgn (- 1) * int (Suc q)"
    by (cases l) simp_all
  moreover define n where "n = Suc q"
  then have "Suc q = n"
    by simp
  moreover have \<open>int (m mod n) \<le> int n\<close>
    using \<open>Suc q = n\<close> by simp
  then have \<open>sgn s * int (m mod n) \<le> int n\<close>
    by (cases s \<open>0::int\<close> rule: linorder_cases) simp_all
  ultimately show ?thesis
    by (simp only: modulo_int_unfold) auto
qed


subsubsection \<open>Splitting Rules for div and mod\<close>

lemma split_zdiv:
  \<open>P (n div k) \<longleftrightarrow>
    (k = 0 \<longrightarrow> P 0) \<and>
    (0 < k \<longrightarrow> (\<forall>i j. 0 \<le> j \<and> j < k \<and> n = k * i + j \<longrightarrow> P i)) \<and>
    (k < 0 \<longrightarrow> (\<forall>i j. k < j \<and> j \<le> 0 \<and> n = k * i + j \<longrightarrow> P i))\<close> (is ?div)
  and split_zmod:
  \<open>Q (n mod k) \<longleftrightarrow>
    (k = 0 \<longrightarrow> Q n) \<and>
    (0 < k \<longrightarrow> (\<forall>i j. 0 \<le> j \<and> j < k \<and> n = k * i + j \<longrightarrow> Q j)) \<and>
    (k < 0 \<longrightarrow> (\<forall>i j. k < j \<and> j \<le> 0 \<and> n = k * i + j \<longrightarrow> Q j))\<close> (is ?mod)
  for n k :: int
proof -
  have *: \<open>R (n div k) (n mod k) \<longleftrightarrow>
    (k = 0 \<longrightarrow> R 0 n) \<and>
    (0 < k \<longrightarrow> (\<forall>i j. 0 \<le> j \<and> j < k \<and> n = k * i + j \<longrightarrow> R i j)) \<and>
    (k < 0 \<longrightarrow> (\<forall>i j. k < j \<and> j \<le> 0 \<and> n = k * i + j \<longrightarrow> R i j))\<close> for R
    by (cases \<open>k = 0\<close>)
      (auto simp add: linorder_class.neq_iff)
  from * [of \<open>\<lambda>q _. P q\<close>] show ?div .
  from * [of \<open>\<lambda>_ r. Q r\<close>] show ?mod .
qed

text \<open>Enable (lin)arith to deal with \<^const>\<open>divide\<close> and \<^const>\<open>modulo\<close>
  when these are applied to some constant that is of the form
  \<^term>\<open>numeral k\<close>:\<close>
declare split_zdiv [of _ _ \<open>numeral n\<close>, linarith_split] for n
declare split_zdiv [of _ _ \<open>- numeral n\<close>, linarith_split] for n
declare split_zmod [of _ _ \<open>numeral n\<close>, linarith_split] for n
declare split_zmod [of _ _ \<open>- numeral n\<close>, linarith_split] for n

lemma zdiv_eq_0_iff:
  "i div k = 0 \<longleftrightarrow> k = 0 \<or> 0 \<le> i \<and> i < k \<or> i \<le> 0 \<and> k < i" (is "?L = ?R")
  for i k :: int
proof
  assume ?L
  moreover have "?L \<longrightarrow> ?R"
    by (rule split_zdiv [THEN iffD2]) simp
  ultimately show ?R
    by blast
next
  assume ?R then show ?L
    by auto
qed

lemma zmod_trivial_iff:
  fixes i k :: int
  shows "i mod k = i \<longleftrightarrow> k = 0 \<or> 0 \<le> i \<and> i < k \<or> i \<le> 0 \<and> k < i"
proof -
  have "i mod k = i \<longleftrightarrow> i div k = 0"
    using div_mult_mod_eq [of i k] by safe auto
  with zdiv_eq_0_iff
  show ?thesis
    by simp
qed


subsubsection \<open>Algebraic rewrites\<close>

lemma zdiv_zmult2_eq: \<open>a div (b * c) = (a div b) div c\<close>  (is ?Q)
  and zmod_zmult2_eq: \<open>a mod (b * c) = b * (a div b mod c) + a mod b\<close>  (is ?P)
  if \<open>c \<ge> 0\<close> for a b c :: int
proof -
  have *: \<open>(a div (b * c), a mod (b * c)) = ((a div b) div c, b * (a div b mod c) + a mod b)\<close>
    if \<open>b > 0\<close> for a b
  proof (induction rule: euclidean_relationI)
    case by0
    then show ?case by auto
  next
    case divides
    then obtain d where \<open>a = b * c * d\<close>
      by blast
    with divides that show ?case
      by (simp add: ac_simps)
  next
    case euclidean_relation
    with \<open>b > 0\<close> \<open>c \<ge> 0\<close> have \<open>0 < c\<close> \<open>b > 0\<close>
      by simp_all
    then have \<open>a mod b < b\<close>
      by simp
    moreover have \<open>1 \<le> c - a div b mod c\<close>
      using \<open>c > 0\<close> by (simp add: int_one_le_iff_zero_less)
    ultimately have \<open>a mod b * 1 < b * (c - a div b mod c)\<close>
      by (rule mult_less_le_imp_less) (use \<open>b > 0\<close> in simp_all)
    with \<open>0 < b\<close> \<open>0 < c\<close> show ?case
      by (simp add: division_segment_int_def algebra_simps flip: minus_mod_eq_mult_div)
  qed
  show ?Q
  proof (cases \<open>b \<ge> 0\<close>)
    case True
    with * [of b a] show ?thesis
      by (cases \<open>b = 0\<close>) simp_all
  next
    case False
    with * [of \<open>- b\<close> \<open>- a\<close>] show ?thesis
      by simp
  qed
  show ?P
  proof (cases \<open>b \<ge> 0\<close>)
    case True
    with * [of b a] show ?thesis
      by (cases \<open>b = 0\<close>) simp_all
  next
    case False
    with * [of \<open>- b\<close> \<open>- a\<close>] show ?thesis
      by simp
  qed
qed

lemma zdiv_zmult2_eq':
  \<open>k div (l * j) = ((sgn j * k) div l) div \<bar>j\<bar>\<close> for k l j :: int
proof -
  have \<open>k div (l * j) = (sgn j * k) div (sgn j * (l * j))\<close>
    by (simp add: sgn_0_0)
  also have \<open>sgn j * (l * j) = l * \<bar>j\<bar>\<close>
    by (simp add: mult.left_commute [of _ l] abs_sgn) (simp add: ac_simps)
  also have \<open>(sgn j * k) div (l * \<bar>j\<bar>) = ((sgn j * k) div l) div \<bar>j\<bar>\<close>
    by (simp add: zdiv_zmult2_eq)
  finally show ?thesis .
qed

lemma half_nonnegative_int_iff [simp]:
  \<open>k div 2 \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by auto

lemma half_negative_int_iff [simp]:
  \<open>k div 2 < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by auto


subsubsection \<open>Distributive laws for conversions.\<close>

lemma zdiv_int:
  \<open>int (m div n) = int m div int n\<close>
  by (cases \<open>m = 0\<close>) (auto simp add: divide_int_def)

lemma zmod_int:
  \<open>int (m mod n) = int m mod int n\<close>
  by (cases \<open>m = 0\<close>) (auto simp add: modulo_int_def)

lemma nat_div_distrib:
  \<open>nat (x div y) = nat x div nat y\<close> if \<open>0 \<le> x\<close>
  using that by (simp add: divide_int_def sgn_if)

lemma nat_div_distrib':
  \<open>nat (x div y) = nat x div nat y\<close> if \<open>0 \<le> y\<close>
  using that by (simp add: divide_int_def sgn_if)

lemma nat_mod_distrib: \<comment> \<open>Fails if y<0: the LHS collapses to (nat z) but the RHS doesn't\<close>
  \<open>nat (x mod y) = nat x mod nat y\<close> if \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
  using that by (simp add: modulo_int_def sgn_if)


subsubsection \<open>Monotonicity in the First Argument (Dividend)\<close>

lemma zdiv_mono1:
  \<open>a div b \<le> a' div b\<close>
    if \<open>a \<le> a'\<close> \<open>0 < b\<close>
    for a b b' :: int
proof -
  from \<open>a \<le> a'\<close> have \<open>b * (a div b) + a mod b \<le> b * (a' div b) + a' mod b\<close>
    by simp
  then have \<open>b * (a div b) \<le> (a' mod b - a mod b) + b * (a' div b)\<close>
    by (simp add: algebra_simps)
  moreover have \<open>a' mod b < b + a mod b\<close>
    by (rule less_le_trans [of _ b]) (use \<open>0 < b\<close> in simp_all)
  ultimately have \<open>b * (a div b) < b * (1 + a' div b)\<close>
    by (simp add: distrib_left)
  with \<open>0 < b\<close> have \<open>a div b < 1 + a' div b\<close>
    by (simp add: mult_less_cancel_left)
  then show ?thesis
    by simp
qed

lemma zdiv_mono1_neg:
  \<open>a' div b \<le> a div b\<close>
    if \<open>a \<le> a'\<close> \<open>b < 0\<close>
    for a a' b :: int
  using that zdiv_mono1 [of \<open>- a'\<close> \<open>- a\<close> \<open>- b\<close>] by simp


subsubsection \<open>Monotonicity in the Second Argument (Divisor)\<close>

lemma zdiv_mono2:
  \<open>a div b \<le> a div b'\<close> if \<open>0 \<le> a\<close> \<open>0 < b'\<close> \<open>b' \<le> b\<close> for a b b' :: int
proof -
  define q q' r r' where **: \<open>q = a div b\<close> \<open>q' = a div b'\<close> \<open>r = a mod b\<close> \<open>r' = a mod b'\<close>
  then have *: \<open>b * q + r = b' * q' + r'\<close> \<open>0 \<le> b' * q' + r'\<close>
    \<open>r' < b'\<close> \<open>0 \<le> r\<close> \<open>0 < b'\<close> \<open>b' \<le> b\<close>
    using that by simp_all
  have \<open>0 < b' * (q' + 1)\<close>
    using * by (simp add: distrib_left)
  with * have \<open>0 \<le> q'\<close>
    by (simp add: zero_less_mult_iff)
  moreover have \<open>b * q = r' - r + b' * q'\<close>
    using * by linarith
  ultimately have \<open>b * q < b * (q' + 1)\<close>
    using mult_right_mono * unfolding distrib_left by fastforce
  with * have \<open>q \<le> q'\<close>
    by (simp add: mult_less_cancel_left_pos)
  with ** show ?thesis
    by simp
qed

lemma zdiv_mono2_neg:
  \<open>a div b' \<le> a div b\<close> if \<open>a < 0\<close> \<open>0 < b'\<close> \<open>b' \<le> b\<close> for a b b' :: int
proof -
  define q q' r r' where **: \<open>q = a div b\<close> \<open>q' = a div b'\<close> \<open>r = a mod b\<close> \<open>r' = a mod b'\<close>
  then have *: \<open>b * q + r = b' * q' + r'\<close> \<open>b' * q' + r' < 0\<close>
    \<open>r < b\<close> \<open>0 \<le> r'\<close> \<open>0 < b'\<close> \<open>b' \<le> b\<close>
    using that by simp_all
  have \<open>b' * q' < 0\<close>
    using * by linarith
  with * have \<open>q' \<le> 0\<close>
    by (simp add: mult_less_0_iff)
  have \<open>b * q' \<le> b' * q'\<close>
    by (simp add: \<open>q' \<le> 0\<close> * mult_right_mono_neg)
  then have "b * q' < b * (q + 1)"
    using * by (simp add: distrib_left)
  then have \<open>q' \<le> q\<close>
    using * by (simp add: mult_less_cancel_left)
  then show ?thesis
    by (simp add: **)
qed


subsubsection \<open>Quotients of Signs\<close>

lemma div_eq_minus1:
  \<open>0 < b \<Longrightarrow> - 1 div b = - 1\<close> for b :: int
  by (simp add: divide_int_def)

lemma zmod_minus1:
  \<open>0 < b \<Longrightarrow> - 1 mod b = b - 1\<close> for b :: int
  by (auto simp add: modulo_int_def)

lemma minus_mod_int_eq:
  \<open>- k mod l = l - 1 - (k - 1) mod l\<close> if \<open>l \<ge> 0\<close> for k l :: int
proof (cases \<open>l = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  with that have \<open>l > 0\<close>
    by simp
  then show ?thesis
  proof (cases \<open>l dvd k\<close>)
    case True
    then obtain j where \<open>k = l * j\<close> ..
    moreover have \<open>(l * j mod l - 1) mod l = l - 1\<close>
      using \<open>l > 0\<close> by (simp add: zmod_minus1)
    then have \<open>(l * j - 1) mod l = l - 1\<close>
      by (simp only: mod_simps)
    ultimately show ?thesis
      by simp
  next
    case False
    moreover have 1: \<open>0 < k mod l\<close>
      using \<open>0 < l\<close> False le_less by fastforce
    moreover have 2: \<open>k mod l < 1 + l\<close>
      using \<open>0 < l\<close> pos_mod_bound[of l k] by linarith
    from 1 2 \<open>l > 0\<close> have \<open>(k mod l - 1) mod l = k mod l - 1\<close>
      by (simp add: zmod_trivial_iff)
    ultimately show ?thesis
      by (simp only: zmod_zminus1_eq_if)
         (simp add: mod_eq_0_iff_dvd algebra_simps mod_simps)
  qed
qed

lemma div_neg_pos_less0:
  \<open>a div b < 0\<close> if \<open>a < 0\<close> \<open>0 < b\<close> for a b :: int
proof -
  have "a div b \<le> - 1 div b"
    using zdiv_mono1 that by auto
  also have "... \<le> -1"
    by (simp add: that(2) div_eq_minus1)
  finally show ?thesis
    by force
qed

lemma div_nonneg_neg_le0:
  \<open>a div b \<le> 0\<close> if \<open>0 \<le> a\<close> \<open>b < 0\<close> for a b :: int
  using that by (auto dest: zdiv_mono1_neg)

lemma div_nonpos_pos_le0:
  \<open>a div b \<le> 0\<close> if \<open>a \<le> 0\<close> \<open>0 < b\<close> for a b :: int
  using that by (auto dest: zdiv_mono1)

text\<open>Now for some equivalences of the form \<open>a div b >=< 0 \<longleftrightarrow> \<dots>\<close>
conditional upon the sign of \<open>a\<close> or \<open>b\<close>. There are many more.
They should all be simp rules unless that causes too much search.\<close>

lemma pos_imp_zdiv_nonneg_iff:
  \<open>0 \<le> a div b \<longleftrightarrow> 0 \<le> a\<close>
  if \<open>0 < b\<close> for a b :: int
proof
  assume \<open>0 \<le> a div b\<close>
  show \<open>0 \<le> a\<close>
  proof (rule ccontr)
    assume \<open>\<not> 0 \<le> a\<close>
    then have \<open>a < 0\<close>
      by simp
    then have \<open>a div b < 0\<close>
      using that by (rule div_neg_pos_less0)
    with \<open>0 \<le> a div b\<close> show False
      by simp
  qed
next
  assume "0 \<le> a"
  then have "0 div b \<le> a div b"
    using zdiv_mono1 that by blast
  then show "0 \<le> a div b"
    by auto
qed

lemma neg_imp_zdiv_nonneg_iff:
  \<open>0 \<le> a div b \<longleftrightarrow> a \<le> 0\<close> if \<open>b < 0\<close> for a b :: int
  using that pos_imp_zdiv_nonneg_iff [of \<open>- b\<close> \<open>- a\<close>] by simp

lemma pos_imp_zdiv_pos_iff:
  \<open>0 < (i::int) div k \<longleftrightarrow> k \<le> i\<close> if \<open>0 < k\<close> for i k :: int
  using that pos_imp_zdiv_nonneg_iff [of k i] zdiv_eq_0_iff [of i k] by arith

lemma pos_imp_zdiv_neg_iff:
  \<open>a div b < 0 \<longleftrightarrow> a < 0\<close> if \<open>0 < b\<close> for a b :: int
    \<comment> \<open>But not \<^prop>\<open>a div b \<le> 0 \<longleftrightarrow> a \<le> 0\<close>; consider \<^prop>\<open>a = 1\<close>, \<^prop>\<open>b = 2\<close> when \<^prop>\<open>a div b = 0\<close>.\<close>
  using that by (simp add: pos_imp_zdiv_nonneg_iff flip: linorder_not_le)

lemma neg_imp_zdiv_neg_iff:
    \<comment> \<open>But not \<^prop>\<open>a div b \<le> 0 \<longleftrightarrow> 0 \<le> a\<close>; consider \<^prop>\<open>a = - 1\<close>, \<^prop>\<open>b = - 2\<close> when \<^prop>\<open>a div b = 0\<close>.\<close>
  \<open>a div b < 0 \<longleftrightarrow> 0 < a\<close> if \<open>b < 0\<close> for a b :: int
  using that by (simp add: neg_imp_zdiv_nonneg_iff flip: linorder_not_le)

lemma nonneg1_imp_zdiv_pos_iff:
  \<open>a div b > 0 \<longleftrightarrow> a \<ge> b \<and> b > 0\<close> if \<open>0 \<le> a\<close> for a b :: int
proof -
  have "0 < a div b \<Longrightarrow> b \<le> a"
    using div_pos_pos_trivial[of a b] that by arith
  moreover have "0 < a div b \<Longrightarrow> b > 0"
    using that div_nonneg_neg_le0[of a b] by (cases "b=0"; force)
  moreover have "b \<le> a \<and> 0 < b \<Longrightarrow> 0 < a div b"
    using int_one_le_iff_zero_less[of "a div b"] zdiv_mono1[of b a b] by simp
  ultimately show ?thesis
    by blast
qed

lemma zmod_le_nonneg_dividend:
  \<open>m mod k \<le> m\<close> if \<open>(m::int) \<ge> 0\<close> for m k :: int
proof -
  from that have \<open>m > 0 \<or> m = 0\<close>
    by auto
  then show ?thesis proof
    assume \<open>m = 0\<close> then show ?thesis
      by simp
  next
    assume \<open>m > 0\<close> then show ?thesis
    proof (cases k \<open>0::int\<close> rule: linorder_cases)
      case less
      moreover define l where \<open>l = - k\<close>
      ultimately have \<open>l > 0\<close>
        by simp
      with \<open>m > 0\<close> have \<open>int (nat m mod nat l) \<le> m\<close>
        by (simp flip: le_nat_iff)
      then have \<open>int (nat m mod nat l) - l \<le> m\<close>
        using \<open>l > 0\<close> by simp
      with \<open>m > 0\<close> \<open>l > 0\<close> show ?thesis
        by (simp add: modulo_int_def l_def flip: le_nat_iff)
    qed (simp_all add: modulo_int_def flip: le_nat_iff)
  qed
qed

lemma sgn_div_eq_sgn_mult:
  \<open>sgn (k div l) = of_bool (k div l \<noteq> 0) * sgn (k * l)\<close>
  for k l :: int
proof (cases \<open>k div l = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  have \<open>0 \<le> \<bar>k\<bar> div \<bar>l\<bar>\<close>
    by (cases \<open>l = 0\<close>) (simp_all add: pos_imp_zdiv_nonneg_iff)
  then have \<open>\<bar>k\<bar> div \<bar>l\<bar> \<noteq> 0 \<longleftrightarrow> 0 < \<bar>k\<bar> div \<bar>l\<bar>\<close>
    by (simp add: less_le)
  also have \<open>\<dots> \<longleftrightarrow> \<bar>k\<bar> \<ge> \<bar>l\<bar>\<close>
    using False nonneg1_imp_zdiv_pos_iff by auto
  finally have *: \<open>\<bar>k\<bar> div \<bar>l\<bar> \<noteq> 0 \<longleftrightarrow> \<bar>l\<bar> \<le> \<bar>k\<bar>\<close> .
  show ?thesis
    using \<open>0 \<le> \<bar>k\<bar> div \<bar>l\<bar>\<close> False
  by (auto simp add: div_eq_div_abs [of k l] div_eq_sgn_abs [of k l]
    sgn_mult sgn_1_pos sgn_1_neg sgn_eq_0_iff nonneg1_imp_zdiv_pos_iff * dest: sgn_not_eq_imp)
qed


subsubsection \<open>Further properties\<close>

lemma div_int_pos_iff:
  "k div l \<ge> 0 \<longleftrightarrow> k = 0 \<or> l = 0 \<or> k \<ge> 0 \<and> l \<ge> 0
    \<or> k < 0 \<and> l < 0"
  for k l :: int
proof (cases "k = 0 \<or> l = 0")
  case False
  then have *: "k \<noteq> 0" "l \<noteq> 0"
    by auto
  then have "0 \<le> k div l \<Longrightarrow> \<not> k < 0 \<Longrightarrow> 0 \<le> l"
    by (meson neg_imp_zdiv_neg_iff not_le not_less_iff_gr_or_eq)
  then show ?thesis
   using * by (auto simp add: pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff)
qed auto

lemma mod_int_pos_iff:
  \<open>k mod l \<ge> 0 \<longleftrightarrow> l dvd k \<or> l = 0 \<and> k \<ge> 0 \<or> l > 0\<close>
  for k l :: int
proof (cases "l > 0")
  case False
  then show ?thesis
    by (simp add: dvd_eq_mod_eq_0) (use neg_mod_sign [of l k] in \<open>auto simp add: le_less not_less\<close>)
qed auto

lemma abs_div:
  \<open>\<bar>x div y\<bar> = \<bar>x\<bar> div \<bar>y\<bar>\<close> if \<open>y dvd x\<close> for x y :: int
  using that by (cases \<open>y = 0\<close>) (auto simp add: abs_mult)

lemma int_power_div_base: \<^marker>\<open>contributor \<open>Matthias Daum\<close>\<close>
  \<open>k ^ m div k = k ^ (m - Suc 0)\<close> if \<open>0 < m\<close> \<open>0 < k\<close> for k :: int
  using that by (cases m) simp_all

lemma int_div_less_self: \<^marker>\<open>contributor \<open>Matthias Daum\<close>\<close>
  \<open>x div k < x\<close> if \<open>0 < x\<close> \<open>1 < k\<close> for x k :: int
proof -
  from that have \<open>nat (x div k) = nat x div nat k\<close>
    by (simp add: nat_div_distrib)
  also from that have \<open>nat x div nat k < nat x\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma int_div_le_self: 
  \<open>x div k \<le> x\<close> if \<open>0 < x\<close>  for x k :: int
  by (metis div_by_1 int_div_less_self less_le_not_le nle_le nonneg1_imp_zdiv_pos_iff order.trans that)


subsubsection \<open>Computing \<open>div\<close> and \<open>mod\<close> by shifting\<close>

lemma div_pos_geq:
  \<open>k div l = (k - l) div l + 1\<close> if \<open>0 < l\<close> \<open>l \<le> k\<close> for k l :: int
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with that show ?thesis by (simp add: div_add_self2)
qed

lemma mod_pos_geq:
  \<open>k mod l = (k - l) mod l\<close>  if \<open>0 < l\<close> \<open>l \<le> k\<close> for k l :: int
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with that show ?thesis by simp
qed

lemma pos_zdiv_mult_2: \<open>(1 + 2 * b) div (2 * a) = b div a\<close> (is ?Q)
  and pos_zmod_mult_2: \<open>(1 + 2 * b) mod (2 * a) = 1 + 2 * (b mod a)\<close> (is ?R)
  if \<open>0 \<le> a\<close> for a b :: int
proof -
  have \<open>((1 + 2 * b) div (2 * a), (1 + 2 * b) mod (2 * a)) = (b div a, 1 + 2 * (b mod a))\<close>
  proof (induction rule: euclidean_relation_intI)
    case by0
    then show ?case
      by simp
  next
    case divides
    have \<open>2 dvd (2 * a)\<close>
      by simp
    then have \<open>2 dvd (1 + 2 * b)\<close>
      using \<open>2 * a dvd 1 + 2 * b\<close> by (rule dvd_trans)
    then have \<open>2 dvd (1 + b * 2)\<close>
      by (simp add: ac_simps)
    then have \<open>is_unit (2 :: int)\<close>
      by simp
    then show ?case
      by simp
  next
    case euclidean_relation
    with that have \<open>a > 0\<close>
      by simp
    moreover have \<open>b mod a < a\<close>
      using \<open>a > 0\<close> by simp
    then have \<open>1 + 2 * (b mod a) < 2 * a\<close>
      by simp
    moreover have \<open>2 * (b mod a) + a * (2 * (b div a)) = 2 * (b div a * a + b mod a)\<close>
      by (simp only: algebra_simps)
    moreover have \<open>0 \<le> 2 * (b mod a)\<close>
      using \<open>a > 0\<close> by simp
    ultimately show ?case
      by (simp add: algebra_simps)
  qed
  then show ?Q and ?R
    by simp_all
qed

lemma neg_zdiv_mult_2: \<open>(1 + 2 * b) div (2 * a) = (b + 1) div a\<close> (is ?Q)
  and neg_zmod_mult_2: \<open>(1 + 2 * b) mod (2 * a) = 2 * ((b + 1) mod a) - 1\<close> (is ?R)
  if \<open>a \<le> 0\<close> for a b :: int
proof -
  have \<open>((1 + 2 * b) div (2 * a), (1 + 2 * b) mod (2 * a)) = ((b + 1) div a, 2 * ((b + 1) mod a) - 1)\<close>
  proof (induction rule: euclidean_relation_intI)
    case by0
    then show ?case
      by simp
  next
    case divides
    have \<open>2 dvd (2 * a)\<close>
      by simp
    then have \<open>2 dvd (1 + 2 * b)\<close>
      using \<open>2 * a dvd 1 + 2 * b\<close> by (rule dvd_trans)
    then have \<open>2 dvd (1 + b * 2)\<close>
      by (simp add: ac_simps)
    then have \<open>is_unit (2 :: int)\<close>
      by simp
    then show ?case
      by simp
  next
    case euclidean_relation
    with that have \<open>a < 0\<close>
      by simp
    moreover have \<open>(b + 1) mod a > a\<close>
      using \<open>a < 0\<close> by simp
    then have \<open>2 * ((b + 1) mod a) > 1 + 2 * a\<close>
      by simp
    moreover have \<open>((1 + b) mod a) \<le> 0\<close>
      using \<open>a < 0\<close> by simp
    then have \<open>2 * ((1 + b) mod a) \<le> 0\<close>
      by simp
    moreover have \<open>2 * ((1 + b) mod a) + a * (2 * ((1 + b) div a)) =
      2 * ((1 + b) div a * a + (1 + b) mod a)\<close>
      by (simp only: algebra_simps)
    ultimately show ?case
      by (simp add: algebra_simps sgn_mult abs_mult)
  qed
  then show ?Q and ?R
    by simp_all
qed

lemma zdiv_numeral_Bit0 [simp]:
  \<open>numeral (Num.Bit0 v) div numeral (Num.Bit0 w) =
    numeral v div (numeral w :: int)\<close>
  unfolding numeral.simps unfolding mult_2 [symmetric]
  by (rule div_mult_mult1) simp

lemma zdiv_numeral_Bit1 [simp]:
  \<open>numeral (Num.Bit1 v) div numeral (Num.Bit0 w) =
    (numeral v div (numeral w :: int))\<close>
  unfolding numeral.simps
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zdiv_mult_2) simp

lemma zmod_numeral_Bit0 [simp]:
  \<open>numeral (Num.Bit0 v) mod numeral (Num.Bit0 w) =
    (2::int) * (numeral v mod numeral w)\<close>
  unfolding numeral_Bit0 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] by (rule mod_mult_mult1)

lemma zmod_numeral_Bit1 [simp]:
  \<open>numeral (Num.Bit1 v) mod numeral (Num.Bit0 w) =
    2 * (numeral v mod numeral w) + (1::int)\<close>
  unfolding numeral_Bit1 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zmod_mult_2) simp


subsection \<open>Code generation\<close>

context
begin

qualified definition divmod_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "divmod_nat m n = (m div n, m mod n)"

qualified lemma divmod_nat_if [code]:
  "divmod_nat m n = (if n = 0 \<or> m < n then (0, m) else
    let (q, r) = divmod_nat (m - n) n in (Suc q, r))"
  by (simp add: divmod_nat_def prod_eq_iff case_prod_beta not_less le_div_geq le_mod_geq)

qualified lemma [code]:
  "m div n = fst (divmod_nat m n)"
  "m mod n = snd (divmod_nat m n)"
  by (simp_all add: divmod_nat_def)

end

code_identifier
  code_module Euclidean_Rings \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end

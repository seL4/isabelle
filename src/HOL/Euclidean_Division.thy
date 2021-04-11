(*  Title:      HOL/Euclidean_Division.thy
    Author:     Manuel Eberl, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Division in euclidean (semi)rings\<close>

theory Euclidean_Division
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
  by (rule; rule coprimeI)
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
  by (cases "c = 0") (auto elim: dvdE)

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
  assumes euclidean_size_mult: "euclidean_size (a * b) = euclidean_size a * euclidean_size b"
  fixes division_segment :: "'a \<Rightarrow> 'a"
  assumes is_unit_division_segment [simp]: "is_unit (division_segment a)"
    and division_segment_mult:
    "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> division_segment (a * b) = division_segment a * division_segment b"
    and division_segment_mod:
    "b \<noteq> 0 \<Longrightarrow> \<not> b dvd a \<Longrightarrow> division_segment (a mod b) = division_segment b"
  assumes div_bounded:
    "b \<noteq> 0 \<Longrightarrow> division_segment r = division_segment b
    \<Longrightarrow> euclidean_size r < euclidean_size b
    \<Longrightarrow> (q * b + r) div b = q"
begin

lemma division_segment_not_0 [simp]:
  "division_segment a \<noteq> 0"
  using is_unit_division_segment [of a] is_unitE [of "division_segment a"] by blast

lemma divmod_cases [case_names divides remainder by0]:
  obtains 
    (divides) q where "b \<noteq> 0"
      and "a div b = q"
      and "a mod b = 0"
      and "a = q * b"
  | (remainder) q r where "b \<noteq> 0"
      and "division_segment r = division_segment b"
      and "euclidean_size r < euclidean_size b"
      and "r \<noteq> 0"
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
    moreover from \<open>b \<noteq> 0\<close> \<open>\<not> b dvd a\<close> have "division_segment (a mod b) = division_segment b"
      by (rule division_segment_mod)
    moreover have "euclidean_size (a mod b) < euclidean_size b"
      using \<open>b \<noteq> 0\<close> by (rule mod_size_less)
    moreover have "a = a div b * b + a mod b"
      by (simp add: div_mult_mod_eq)
    ultimately show thesis
      using \<open>b \<noteq> 0\<close> by (blast intro!: remainder)
  qed
qed

lemma div_eqI:
  "a div b = q" if "b \<noteq> 0" "division_segment r = division_segment b"
    "euclidean_size r < euclidean_size b" "q * b + r = a"
proof -
  from that have "(q * b + r) div b = q"
    by (auto intro: div_bounded)
  with that show ?thesis
    by simp
qed

lemma mod_eqI:
  "a mod b = r" if "b \<noteq> 0" "division_segment r = division_segment b"
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
    have "division_segment (r * c) = division_segment (b * c)"
      and "euclidean_size (r * c) < euclidean_size (b * c)"
      by (simp_all add: division_segment_mult division_segment_mod euclidean_size_mult)
    with remainder show ?thesis
      by (auto intro!: div_eqI [of _ "c * (a mod b)"] simp add: algebra_simps)
        (use \<open>b * c \<noteq> 0\<close> in simp)
  qed
qed

lemma div_mult1_eq:
  "(a * b) div c = a * (b div c) + a * (b mod c) div c"
proof (cases "a * (b mod c)" c rule: divmod_cases)
  case (divides q)
  have "a * b = a * (b div c * c + b mod c)"
    by (simp add: div_mult_mod_eq)
  also have "\<dots> = (a * (b div c) + q) * c"
    using divides by (simp add: algebra_simps)
  finally have "(a * b) div c = \<dots> div c"
    by simp
  with divides show ?thesis
    by simp
next
  case (remainder q r)
  from remainder(1-3) show ?thesis
  proof (rule div_eqI)
    have "a * b = a * (b div c * c + b mod c)"
      by (simp add: div_mult_mod_eq)
    also have "\<dots> = a * c * (b div c) + q * c + r"
      using remainder by (simp add: algebra_simps)
    finally show "(a * (b div c) + a * (b mod c) div c) * c + r = a * b"
      using remainder(5-7) by (simp add: algebra_simps)
  qed
next
  case by0
  then show ?thesis
    by simp
qed

lemma div_add1_eq:
  "(a + b) div c = a div c + b div c + (a mod c + b mod c) div c"
proof (cases "a mod c + b mod c" c rule: divmod_cases)
  case (divides q)
  have "a + b = (a div c * c + a mod c) + (b div c * c + b mod c)"
    using mod_mult_div_eq [of a c] mod_mult_div_eq [of b c] by (simp add: ac_simps)
  also have "\<dots> = (a div c + b div c) * c + (a mod c + b mod c)"
    by (simp add: algebra_simps)
  also have "\<dots> = (a div c + b div c + q) * c"
    using divides by (simp add: algebra_simps)
  finally have "(a + b) div c = (a div c + b div c + q) * c div c"
    by simp
  with divides show ?thesis
    by simp
next
  case (remainder q r)
  from remainder(1-3) show ?thesis
  proof (rule div_eqI)
    have "(a div c + b div c + q) * c + r + (a mod c + b mod c) =
        (a div c * c + a mod c) + (b div c * c + b mod c) + q * c + r"
      by (simp add: algebra_simps)
    also have "\<dots> = a + b + (a mod c + b mod c)"
      by (simp add: div_mult_mod_eq remainder) (simp add: ac_simps)
    finally show "(a div c + b div c + (a mod c + b mod c) div c) * c + r = a + b"
      using remainder by simp
  qed
next
  case by0
  then show ?thesis
    by simp
qed

lemma div_eq_0_iff:
  "a div b = 0 \<longleftrightarrow> euclidean_size a < euclidean_size b \<or> b = 0" (is "_ \<longleftrightarrow> ?P")
  if "division_segment a = division_segment b"
proof
  assume ?P
  with that show "a div b = 0"
    by (cases "b = 0") (auto intro: div_eqI)
next
  assume "a div b = 0"
  then have "a mod b = a"
    using div_mult_mod_eq [of a b] by simp
  with mod_size_less [of b a] show ?P
    by auto
qed

end

class unique_euclidean_ring = euclidean_ring + unique_euclidean_semiring
begin
  
subclass euclidean_ring_cancel ..

end


subsection \<open>Euclidean division on \<^typ>\<open>nat\<close>\<close>

instantiation nat :: normalization_semidom
begin

definition normalize_nat :: "nat \<Rightarrow> nat"
  where [simp]: "normalize = (id :: nat \<Rightarrow> nat)"

definition unit_factor_nat :: "nat \<Rightarrow> nat"
  where "unit_factor n = (if n = 0 then 0 else 1 :: nat)"

lemma unit_factor_simps [simp]:
  "unit_factor 0 = (0::nat)"
  "unit_factor (Suc n) = 1"
  by (simp_all add: unit_factor_nat_def)

definition divide_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "m div n = (if n = 0 then 0 else Max {k::nat. k * n \<le> m})"

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

definition euclidean_size_nat :: "nat \<Rightarrow> nat"
  where [simp]: "euclidean_size_nat = id"

definition division_segment_nat :: "nat \<Rightarrow> nat"
  where [simp]: "division_segment_nat n = 1"

definition modulo_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "m mod n = m - (m div n * (n::nat))"

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

lemma div_nat_eqI:
  "m div n = q" if "n * q \<le> m" and "m < n * Suc q" for m n q :: nat
  by (rule div_eqI [of _ "m - n * q"]) (use that in \<open>simp_all add: algebra_simps\<close>)

lemma mod_nat_eqI:
  "m mod n = r" if "r < n" and "r \<le> m" and "n dvd m - r" for m n r :: nat
  by (rule mod_eqI [of _ _ "(m - r) div n"]) (use that in \<open>simp_all add: algebra_simps\<close>)

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
  using that by (auto intro: div_eqI mod_eqI) 

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

context
  fixes m n q :: nat
begin

private lemma eucl_rel_mult2:
  "m mod n + n * (m div n mod q) < n * q"
  if "n > 0" and "q > 0"
proof -
  from \<open>n > 0\<close> have "m mod n < n"
    by (rule mod_less_divisor)
  from \<open>q > 0\<close> have "m div n mod q < q"
    by (rule mod_less_divisor)
  then obtain s where "q = Suc (m div n mod q + s)"
    by (blast dest: less_imp_Suc_add)
  moreover have "m mod n + n * (m div n mod q) < n * Suc (m div n mod q + s)"
    using \<open>m mod n < n\<close> by (simp add: add_mult_distrib2)
  ultimately show ?thesis
    by simp
qed

lemma div_mult2_eq:
  "m div (n * q) = (m div n) div q"
proof (cases "n = 0 \<or> q = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  with eucl_rel_mult2 show ?thesis
    by (auto intro: div_eqI [of _ "n * (m div n mod q) + m mod n"]
      simp add: algebra_simps add_mult_distrib2 [symmetric])
qed

lemma mod_mult2_eq:
  "m mod (n * q) = n * (m div n mod q) + m mod n"
proof (cases "n = 0 \<or> q = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  with eucl_rel_mult2 show ?thesis
    by (auto intro: mod_eqI [of _ _ "(m div n) div q"]
      simp add: algebra_simps add_mult_distrib2 [symmetric])
qed

end

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

text \<open>A fact for the mutilated chess board\<close>

lemma mod_Suc:
  "Suc m mod n = (if Suc (m mod n) = n then 0 else Suc (m mod n))" (is "_ = ?rhs")
proof (cases "n = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  have "Suc m mod n = Suc (m mod n) mod n"
    by (simp add: mod_simps)
  also have "\<dots> = ?rhs"
    using False by (auto intro!: mod_nat_eqI intro: neq_le_trans simp add: Suc_le_eq)
  finally show ?thesis .
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

lemma split_div:
  "P (m div n) \<longleftrightarrow> (n = 0 \<longrightarrow> P 0) \<and> (n \<noteq> 0 \<longrightarrow>
     (\<forall>i j. j < n \<longrightarrow> m = n * i + j \<longrightarrow> P i))"
     (is "?P = ?Q") for m n :: nat
proof (cases "n = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof
    assume ?P
    with False show ?Q
      by auto
  next
    assume ?Q
    with False have *: "\<And>i j. j < n \<Longrightarrow> m = n * i + j \<Longrightarrow> P i"
      by simp
    with False show ?P
      by (auto intro: * [of "m mod n"])
  qed
qed

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

lemma split_mod:
  "P (m mod n) \<longleftrightarrow> (n = 0 \<longrightarrow> P m) \<and> (n \<noteq> 0 \<longrightarrow>
     (\<forall>i j. j < n \<longrightarrow> m = n * i + j \<longrightarrow> P j))"
     (is "?P \<longleftrightarrow> ?Q") for m n :: nat
proof (cases "n = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof
    assume ?P
    with False show ?Q
      by auto
  next
    assume ?Q
    with False have *: "\<And>i j. j < n \<Longrightarrow> m = n * i + j \<Longrightarrow> P j"
      by simp
    with False show ?P
      by (auto intro: * [of _ "m div n"])
  qed
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


subsection \<open>Euclidean division on \<^typ>\<open>int\<close>\<close>

instantiation int :: normalization_semidom
begin

definition normalize_int :: "int \<Rightarrow> int"
  where [simp]: "normalize = (abs :: int \<Rightarrow> int)"

definition unit_factor_int :: "int \<Rightarrow> int"
  where [simp]: "unit_factor = (sgn :: int \<Rightarrow> int)"

definition divide_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "k div l = (if l = 0 then 0
    else if sgn k = sgn l
      then int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)
      else - int (nat \<bar>k\<bar> div nat \<bar>l\<bar> + of_bool (\<not> l dvd k)))"

lemma divide_int_unfold:
  "(sgn k * int m) div (sgn l * int n) =
   (if sgn l = 0 \<or> sgn k = 0 \<or> n = 0 then 0
    else if sgn k = sgn l
      then int (m div n)
      else - int (m div n + of_bool (\<not> n dvd m)))"
  by (auto simp add: divide_int_def sgn_0_0 sgn_1_pos sgn_mult abs_mult
    nat_mult_distrib)

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
qed (auto simp add: sgn_mult mult_sgn_abs abs_eq_iff')

end

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

instantiation int :: idom_modulo
begin

definition modulo_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "k mod l = (if l = 0 then k
    else if sgn k = sgn l
      then sgn l * int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)
      else sgn l * (\<bar>l\<bar> * of_bool (\<not> l dvd k) - int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)))"

lemma modulo_int_unfold:
  "(sgn k * int m) mod (sgn l * int n) =
   (if sgn l = 0 \<or> sgn k = 0 \<or> n = 0 then sgn k * int m
    else if sgn k = sgn l
      then sgn l * int (m mod n)
      else sgn l * (int (n * of_bool (\<not> n dvd m)) - int (m mod n)))"
  by (auto simp add: modulo_int_def sgn_0_0 sgn_1_pos sgn_mult abs_mult
    nat_mult_distrib)

instance proof
  fix k l :: int
  obtain n m and s t where "k = sgn s * int n" and "l = sgn t * int m" 
    by (blast intro: int_sgnE elim: that)
  then show "k div l * l + k mod l = k"
    by (auto simp add: divide_int_unfold modulo_int_unfold algebra_simps dest!: sgn_not_eq_imp)
       (simp_all add: of_nat_mult [symmetric] of_nat_add [symmetric]
         distrib_left [symmetric] minus_mult_right
         del: of_nat_mult minus_mult_right [symmetric])
qed

end

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
    by (simp add: modulo_int_unfold sgn_0_0 sgn_1_pos sgn_1_neg
      abs_mult mod_greater_zero_iff_not_dvd)
qed

lemma sgn_mod:
  "sgn (k mod l) = sgn l" if "l \<noteq> 0" "\<not> l dvd k" for k l :: int
proof -
  obtain n m and s t where "k = sgn s * int n" and "l = sgn t * int m" 
    by (blast intro: int_sgnE elim: that)
  with that show ?thesis
    by (simp add: modulo_int_unfold sgn_0_0 sgn_1_pos sgn_1_neg sgn_mult)
      (simp add: dvd_eq_mod_eq_0)
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
        by (simp only: *, simp only: q l divide_int_unfold)
          (auto simp add: sgn_mult sgn_0_0 sgn_1_pos)
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
      (simp add: mod_greater_zero_iff_not_dvd)
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
      (simp add: mod_greater_zero_iff_not_dvd)
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
    by (simp only: modulo_int_unfold) simp
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
  ultimately show ?thesis
    by (simp only: modulo_int_unfold) simp
qed

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

lemma div_pos_neg_trivial:
  "k div l = - 1" if "0 < k" and "k + l \<le> 0" for k l :: int
proof (cases \<open>l = - k\<close>)
  case True
  with that show ?thesis
    by (simp add: divide_int_def)
next
  case False
  show ?thesis
    apply (rule div_eqI [of _ "k + l"])
    using False that apply (simp_all add: division_segment_int_def)
    done
qed

lemma mod_pos_neg_trivial:
  "k mod l = k + l" if "0 < k" and "k + l \<le> 0" for k l :: int
proof (cases \<open>l = - k\<close>)
  case True
  with that show ?thesis
    by (simp add: divide_int_def)
next
  case False
  show ?thesis
    apply (rule mod_eqI [of _ _ \<open>- 1\<close>])
    using False that apply (simp_all add: division_segment_int_def)
    done
qed

text \<open>There is neither \<open>div_neg_pos_trivial\<close> nor \<open>mod_neg_pos_trivial\<close>
  because \<^term>\<open>0 div l = 0\<close> would supersede it.\<close>

text \<open>Distributive laws for function \<open>nat\<close>.\<close>

lemma nat_div_distrib:
  \<open>nat (x div y) = nat x div nat y\<close> if \<open>0 \<le> x\<close>
  using that by (simp add: divide_int_def sgn_if)

lemma nat_div_distrib':
  \<open>nat (x div y) = nat x div nat y\<close> if \<open>0 \<le> y\<close>
  using that by (simp add: divide_int_def sgn_if)

lemma nat_mod_distrib: \<comment> \<open>Fails if y<0: the LHS collapses to (nat z) but the RHS doesn't\<close>
  \<open>nat (x mod y) = nat x mod nat y\<close> if \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
  using that by (simp add: modulo_int_def sgn_if)


subsection \<open>Special case: euclidean rings containing the natural numbers\<close>

class unique_euclidean_semiring_with_nat = semidom + semiring_char_0 + unique_euclidean_semiring +
  assumes of_nat_div: "of_nat (m div n) = of_nat m div of_nat n"
    and division_segment_of_nat [simp]: "division_segment (of_nat n) = 1"
    and division_segment_euclidean_size [simp]: "division_segment a * of_nat (euclidean_size a) = a"
begin

lemma division_segment_eq_iff:
  "a = b" if "division_segment a = division_segment b"
    and "euclidean_size a = euclidean_size b"
  using that division_segment_euclidean_size [of a] by simp

lemma euclidean_size_of_nat [simp]:
  "euclidean_size (of_nat n) = n"
proof -
  have "division_segment (of_nat n) * of_nat (euclidean_size (of_nat n)) = of_nat n"
    by (fact division_segment_euclidean_size)
  then show ?thesis by simp
qed

lemma of_nat_euclidean_size:
  "of_nat (euclidean_size a) = a div division_segment a"
proof -
  have "of_nat (euclidean_size a) = division_segment a * of_nat (euclidean_size a) div division_segment a"
    by (subst nonzero_mult_div_cancel_left) simp_all
  also have "\<dots> = a div division_segment a"
    by simp
  finally show ?thesis .
qed

lemma division_segment_1 [simp]:
  "division_segment 1 = 1"
  using division_segment_of_nat [of 1] by simp

lemma division_segment_numeral [simp]:
  "division_segment (numeral k) = 1"
  using division_segment_of_nat [of "numeral k"] by simp

lemma euclidean_size_1 [simp]:
  "euclidean_size 1 = 1"
  using euclidean_size_of_nat [of 1] by simp

lemma euclidean_size_numeral [simp]:
  "euclidean_size (numeral k) = numeral k"
  using euclidean_size_of_nat [of "numeral k"] by simp

lemma of_nat_dvd_iff:
  "of_nat m dvd of_nat n \<longleftrightarrow> m dvd n" (is "?P \<longleftrightarrow> ?Q")
proof (cases "m = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof
    assume ?Q
    then show ?P
      by auto
  next
    assume ?P
    with False have "of_nat n = of_nat n div of_nat m * of_nat m"
      by simp
    then have "of_nat n = of_nat (n div m * m)"
      by (simp add: of_nat_div)
    then have "n = n div m * m"
      by (simp only: of_nat_eq_iff)
    then have "n = m * (n div m)"
      by (simp add: ac_simps)
    then show ?Q ..
  qed
qed

lemma of_nat_mod:
  "of_nat (m mod n) = of_nat m mod of_nat n"
proof -
  have "of_nat m div of_nat n * of_nat n + of_nat m mod of_nat n = of_nat m"
    by (simp add: div_mult_mod_eq)
  also have "of_nat m = of_nat (m div n * n + m mod n)"
    by simp
  finally show ?thesis
    by (simp only: of_nat_div of_nat_mult of_nat_add) simp
qed

lemma one_div_two_eq_zero [simp]:
  "1 div 2 = 0"
proof -
  from of_nat_div [symmetric] have "of_nat 1 div of_nat 2 = of_nat 0"
    by (simp only:) simp
  then show ?thesis
    by simp
qed

lemma one_mod_two_eq_one [simp]:
  "1 mod 2 = 1"
proof -
  from of_nat_mod [symmetric] have "of_nat 1 mod of_nat 2 = of_nat 1"
    by (simp only:) simp
  then show ?thesis
    by simp
qed

lemma one_mod_2_pow_eq [simp]:
  "1 mod (2 ^ n) = of_bool (n > 0)"
proof -
  have "1 mod (2 ^ n) = of_nat (1 mod (2 ^ n))"
    using of_nat_mod [of 1 "2 ^ n"] by simp
  also have "\<dots> = of_bool (n > 0)"
    by simp
  finally show ?thesis .
qed

lemma one_div_2_pow_eq [simp]:
  "1 div (2 ^ n) = of_bool (n = 0)"
  using div_mult_mod_eq [of 1 "2 ^ n"] by auto

lemma div_mult2_eq':
  "a div (of_nat m * of_nat n) = a div of_nat m div of_nat n"
proof (cases a "of_nat m * of_nat n" rule: divmod_cases)
  case (divides q)
  then show ?thesis
    using nonzero_mult_div_cancel_right [of "of_nat m" "q * of_nat n"]
    by (simp add: ac_simps)
next
  case (remainder q r)
  then have "division_segment r = 1"
    using division_segment_of_nat [of "m * n"] by simp
  with division_segment_euclidean_size [of r]
  have "of_nat (euclidean_size r) = r"
    by simp
  have "a mod (of_nat m * of_nat n) div (of_nat m * of_nat n) = 0"
    by simp
  with remainder(6) have "r div (of_nat m * of_nat n) = 0"
    by simp
  with \<open>of_nat (euclidean_size r) = r\<close>
  have "of_nat (euclidean_size r) div (of_nat m * of_nat n) = 0"
    by simp
  then have "of_nat (euclidean_size r div (m * n)) = 0"
    by (simp add: of_nat_div)
  then have "of_nat (euclidean_size r div m div n) = 0"
    by (simp add: div_mult2_eq)
  with \<open>of_nat (euclidean_size r) = r\<close> have "r div of_nat m div of_nat n = 0"
    by (simp add: of_nat_div)
  with remainder(1)
  have "q = (r div of_nat m + q * of_nat n * of_nat m div of_nat m) div of_nat n"
    by simp
  with remainder(5) remainder(7) show ?thesis
    using div_plus_div_distrib_dvd_right [of "of_nat m" "q * (of_nat m * of_nat n)" r]
    by (simp add: ac_simps)
next
  case by0
  then show ?thesis
    by auto
qed

lemma mod_mult2_eq':
  "a mod (of_nat m * of_nat n) = of_nat m * (a div of_nat m mod of_nat n) + a mod of_nat m"
proof -
  have "a div (of_nat m * of_nat n) * (of_nat m * of_nat n) + a mod (of_nat m * of_nat n) = a div of_nat m div of_nat n * of_nat n * of_nat m + (a div of_nat m mod of_nat n * of_nat m + a mod of_nat m)"
    by (simp add: combine_common_factor div_mult_mod_eq)
  moreover have "a div of_nat m div of_nat n * of_nat n * of_nat m = of_nat n * of_nat m * (a div of_nat m div of_nat n)"
    by (simp add: ac_simps)
  ultimately show ?thesis
    by (simp add: div_mult2_eq' mult_commute)
qed

lemma div_mult2_numeral_eq:
  "a div numeral k div numeral l = a div numeral (k * l)" (is "?A = ?B")
proof -
  have "?A = a div of_nat (numeral k) div of_nat (numeral l)"
    by simp
  also have "\<dots> = a div (of_nat (numeral k) * of_nat (numeral l))"
    by (fact div_mult2_eq' [symmetric])
  also have "\<dots> = ?B"
    by simp
  finally show ?thesis .
qed

lemma numeral_Bit0_div_2:
  "numeral (num.Bit0 n) div 2 = numeral n"
proof -
  have "numeral (num.Bit0 n) = numeral n + numeral n"
    by (simp only: numeral.simps)
  also have "\<dots> = numeral n * 2"
    by (simp add: mult_2_right)
  finally have "numeral (num.Bit0 n) div 2 = numeral n * 2 div 2"
    by simp
  also have "\<dots> = numeral n"
    by (rule nonzero_mult_div_cancel_right) simp
  finally show ?thesis .
qed

lemma numeral_Bit1_div_2:
  "numeral (num.Bit1 n) div 2 = numeral n"
proof -
  have "numeral (num.Bit1 n) = numeral n + numeral n + 1"
    by (simp only: numeral.simps)
  also have "\<dots> = numeral n * 2 + 1"
    by (simp add: mult_2_right)
  finally have "numeral (num.Bit1 n) div 2 = (numeral n * 2 + 1) div 2"
    by simp
  also have "\<dots> = numeral n * 2 div 2 + 1 div 2"
    using dvd_triv_right by (rule div_plus_div_distrib_dvd_left)
  also have "\<dots> = numeral n * 2 div 2"
    by simp
  also have "\<dots> = numeral n"
    by (rule nonzero_mult_div_cancel_right) simp
  finally show ?thesis .
qed

lemma exp_mod_exp:
  \<open>2 ^ m mod 2 ^ n = of_bool (m < n) * 2 ^ m\<close>
proof -
  have \<open>(2::nat) ^ m mod 2 ^ n = of_bool (m < n) * 2 ^ m\<close> (is \<open>?lhs = ?rhs\<close>)
    by (auto simp add: not_less monoid_mult_class.power_add dest!: le_Suc_ex)
  then have \<open>of_nat ?lhs = of_nat ?rhs\<close>
    by simp
  then show ?thesis
    by (simp add: of_nat_mod)
qed

lemma mask_mod_exp:
  \<open>(2 ^ n - 1) mod 2 ^ m = 2 ^ min m n - 1\<close>
proof -
  have \<open>(2 ^ n - 1) mod 2 ^ m = 2 ^ min m n - (1::nat)\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (cases \<open>n \<le> m\<close>)
    case True
    then show ?thesis
      by (simp add: Suc_le_lessD min.absorb2)
  next
    case False
    then have \<open>m < n\<close>
      by simp
    then obtain q where n: \<open>n = Suc q + m\<close>
      by (auto dest: less_imp_Suc_add)
    then have \<open>min m n = m\<close>
      by simp
    moreover have \<open>(2::nat) ^ m \<le> 2 * 2 ^ q * 2 ^ m\<close>
      using mult_le_mono1 [of 1 \<open>2 * 2 ^ q\<close> \<open>2 ^ m\<close>] by simp
    with n have \<open>2 ^ n - 1 = (2 ^ Suc q - 1) * 2 ^ m + (2 ^ m - (1::nat))\<close>
      by (simp add: monoid_mult_class.power_add algebra_simps)
    ultimately show ?thesis
      by (simp only: euclidean_semiring_cancel_class.mod_mult_self3) simp
  qed
  then have \<open>of_nat ?lhs = of_nat ?rhs\<close>
    by simp
  then show ?thesis
    by (simp add: of_nat_mod of_nat_diff)
qed

lemma of_bool_half_eq_0 [simp]:
  \<open>of_bool b div 2 = 0\<close>
  by simp

end

class unique_euclidean_ring_with_nat = ring + unique_euclidean_semiring_with_nat

instance nat :: unique_euclidean_semiring_with_nat
  by standard (simp_all add: dvd_eq_mod_eq_0)

instance int :: unique_euclidean_ring_with_nat
  by standard (simp_all add: dvd_eq_mod_eq_0 divide_int_def division_segment_int_def)


subsection \<open>Code generation\<close>

code_identifier
  code_module Euclidean_Division \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end

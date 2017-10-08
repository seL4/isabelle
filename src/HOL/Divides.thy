(*  Title:      HOL/Divides.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

section \<open>More on quotient and remainder\<close>

theory Divides
imports Parity
begin

subsection \<open>Quotient and remainder in integral domains with additional properties\<close>

class semiring_div = semidom_modulo +
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

class ring_div = comm_ring_1 + semiring_div
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

end

  
subsection \<open>Euclidean (semi)rings with cancel rules\<close>

class euclidean_semiring_cancel = euclidean_semiring + semiring_div

class euclidean_ring_cancel = euclidean_ring + ring_div

context unique_euclidean_semiring
begin

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

context unique_euclidean_ring
begin

subclass euclidean_ring_cancel ..

end


subsection \<open>Parity\<close>

class semiring_div_parity = semiring_div + comm_semiring_1_cancel + numeral +
  assumes parity: "a mod 2 = 0 \<or> a mod 2 = 1"
  assumes one_mod_two_eq_one [simp]: "1 mod 2 = 1"
  assumes zero_not_eq_two: "0 \<noteq> 2"
begin

lemma parity_cases [case_names even odd]:
  assumes "a mod 2 = 0 \<Longrightarrow> P"
  assumes "a mod 2 = 1 \<Longrightarrow> P"
  shows P
  using assms parity by blast

lemma one_div_two_eq_zero [simp]:
  "1 div 2 = 0"
proof (cases "2 = 0")
  case True then show ?thesis by simp
next
  case False
  from div_mult_mod_eq have "1 div 2 * 2 + 1 mod 2 = 1" .
  with one_mod_two_eq_one have "1 div 2 * 2 + 1 = 1" by simp
  then have "1 div 2 * 2 = 0" by (simp add: ac_simps add_left_imp_eq del: mult_eq_0_iff)
  then have "1 div 2 = 0 \<or> 2 = 0" by simp
  with False show ?thesis by auto
qed

lemma not_mod_2_eq_0_eq_1 [simp]:
  "a mod 2 \<noteq> 0 \<longleftrightarrow> a mod 2 = 1"
  by (cases a rule: parity_cases) simp_all

lemma not_mod_2_eq_1_eq_0 [simp]:
  "a mod 2 \<noteq> 1 \<longleftrightarrow> a mod 2 = 0"
  by (cases a rule: parity_cases) simp_all

subclass semiring_parity
proof (unfold_locales, unfold dvd_eq_mod_eq_0 not_mod_2_eq_0_eq_1)
  show "1 mod 2 = 1"
    by (fact one_mod_two_eq_one)
next
  fix a b
  assume "a mod 2 = 1"
  moreover assume "b mod 2 = 1"
  ultimately show "(a + b) mod 2 = 0"
    using mod_add_eq [of a 2 b] by simp
next
  fix a b
  assume "(a * b) mod 2 = 0"
  then have "(a mod 2) * (b mod 2) mod 2 = 0"
    by (simp add: mod_mult_eq)
  then have "(a mod 2) * (b mod 2) = 0"
    by (cases "a mod 2 = 0") simp_all
  then show "a mod 2 = 0 \<or> b mod 2 = 0"
    by (rule divisors_zero)
next
  fix a
  assume "a mod 2 = 1"
  then have "a = a div 2 * 2 + 1"
    using div_mult_mod_eq [of a 2] by simp
  then show "\<exists>b. a = b + 1" ..
qed

lemma even_iff_mod_2_eq_zero:
  "even a \<longleftrightarrow> a mod 2 = 0"
  by (fact dvd_eq_mod_eq_0)

lemma odd_iff_mod_2_eq_one:
  "odd a \<longleftrightarrow> a mod 2 = 1"
  by (simp add: even_iff_mod_2_eq_zero)

lemma even_succ_div_two [simp]:
  "even a \<Longrightarrow> (a + 1) div 2 = a div 2"
  by (cases "a = 0") (auto elim!: evenE dest: mult_not_zero)

lemma odd_succ_div_two [simp]:
  "odd a \<Longrightarrow> (a + 1) div 2 = a div 2 + 1"
  by (auto elim!: oddE simp add: zero_not_eq_two [symmetric] add.assoc)

lemma even_two_times_div_two:
  "even a \<Longrightarrow> 2 * (a div 2) = a"
  by (fact dvd_mult_div_cancel)

lemma odd_two_times_div_two_succ [simp]:
  "odd a \<Longrightarrow> 2 * (a div 2) + 1 = a"
  using mult_div_mod_eq [of 2 a] by (simp add: even_iff_mod_2_eq_zero)
 
end


subsection \<open>Numeral division with a pragmatic type class\<close>

text \<open>
  The following type class contains everything necessary to formulate
  a division algorithm in ring structures with numerals, restricted
  to its positive segments.  This is its primary motivation, and it
  could surely be formulated using a more fine-grained, more algebraic
  and less technical class hierarchy.
\<close>

class semiring_numeral_div = semiring_div + comm_semiring_1_cancel + linordered_semidom +
  assumes div_less: "0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a div b = 0"
    and mod_less: " 0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a mod b = a"
    and div_positive: "0 < b \<Longrightarrow> b \<le> a \<Longrightarrow> a div b > 0"
    and mod_less_eq_dividend: "0 \<le> a \<Longrightarrow> a mod b \<le> a"
    and pos_mod_bound: "0 < b \<Longrightarrow> a mod b < b"
    and pos_mod_sign: "0 < b \<Longrightarrow> 0 \<le> a mod b"
    and mod_mult2_eq: "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
    and div_mult2_eq: "0 \<le> c \<Longrightarrow> a div (b * c) = a div b div c"
  assumes discrete: "a < b \<longleftrightarrow> a + 1 \<le> b"
  fixes divmod :: "num \<Rightarrow> num \<Rightarrow> 'a \<times> 'a"
    and divmod_step :: "num \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes divmod_def: "divmod m n = (numeral m div numeral n, numeral m mod numeral n)"
    and divmod_step_def: "divmod_step l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"
    \<comment> \<open>These are conceptually definitions but force generated code
    to be monomorphic wrt. particular instances of this class which
    yields a significant speedup.\<close>
begin

subclass semiring_div_parity
proof
  fix a
  show "a mod 2 = 0 \<or> a mod 2 = 1"
  proof (rule ccontr)
    assume "\<not> (a mod 2 = 0 \<or> a mod 2 = 1)"
    then have "a mod 2 \<noteq> 0" and "a mod 2 \<noteq> 1" by simp_all
    have "0 < 2" by simp
    with pos_mod_bound pos_mod_sign have "0 \<le> a mod 2" "a mod 2 < 2" by simp_all
    with \<open>a mod 2 \<noteq> 0\<close> have "0 < a mod 2" by simp
    with discrete have "1 \<le> a mod 2" by simp
    with \<open>a mod 2 \<noteq> 1\<close> have "1 < a mod 2" by simp
    with discrete have "2 \<le> a mod 2" by simp
    with \<open>a mod 2 < 2\<close> show False by simp
  qed
next
  show "1 mod 2 = 1"
    by (rule mod_less) simp_all
next
  show "0 \<noteq> 2"
    by simp
qed

lemma divmod_digit_1:
  assumes "0 \<le> a" "0 < b" and "b \<le> a mod (2 * b)"
  shows "2 * (a div (2 * b)) + 1 = a div b" (is "?P")
    and "a mod (2 * b) - b = a mod b" (is "?Q")
proof -
  from assms mod_less_eq_dividend [of a "2 * b"] have "b \<le> a"
    by (auto intro: trans)
  with \<open>0 < b\<close> have "0 < a div b" by (auto intro: div_positive)
  then have [simp]: "1 \<le> a div b" by (simp add: discrete)
  with \<open>0 < b\<close> have mod_less: "a mod b < b" by (simp add: pos_mod_bound)
  define w where "w = a div b mod 2"
  with parity have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  from assms w_exhaust have "w = 1"
    by (auto simp add: mod_w) (insert mod_less, auto)
  with mod_w have mod: "a mod (2 * b) = a mod b + b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 1\<close> have div: "2 * (a div (2 * b)) = a div b - 1" by simp
  then show ?P and ?Q
    by (simp_all add: div mod add_implies_diff [symmetric])
qed

lemma divmod_digit_0:
  assumes "0 < b" and "a mod (2 * b) < b"
  shows "2 * (a div (2 * b)) = a div b" (is "?P")
    and "a mod (2 * b) = a mod b" (is "?Q")
proof -
  define w where "w = a div b mod 2"
  with parity have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  moreover have "b \<le> a mod b + b"
  proof -
    from \<open>0 < b\<close> pos_mod_sign have "0 \<le> a mod b" by blast
    then have "0 + b \<le> a mod b + b" by (rule add_right_mono)
    then show ?thesis by simp
  qed
  moreover note assms w_exhaust
  ultimately have "w = 0" by auto
  with mod_w have mod: "a mod (2 * b) = a mod b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 0\<close> have div: "2 * (a div (2 * b)) = a div b" by simp
  then show ?P and ?Q
    by (simp_all add: div mod)
qed

lemma fst_divmod:
  "fst (divmod m n) = numeral m div numeral n"
  by (simp add: divmod_def)

lemma snd_divmod:
  "snd (divmod m n) = numeral m mod numeral n"
  by (simp add: divmod_def)

text \<open>
  This is a formulation of one step (referring to one digit position)
  in school-method division: compare the dividend at the current
  digit position with the remainder from previous division steps
  and evaluate accordingly.
\<close>

lemma divmod_step_eq [simp]:
  "divmod_step l (q, r) = (if numeral l \<le> r
    then (2 * q + 1, r - numeral l) else (2 * q, r))"
  by (simp add: divmod_step_def)

text \<open>
  This is a formulation of school-method division.
  If the divisor is smaller than the dividend, terminate.
  If not, shift the dividend to the right until termination
  occurs and then reiterate single division steps in the
  opposite direction.
\<close>

lemma divmod_divmod_step:
  "divmod m n = (if m < n then (0, numeral m)
    else divmod_step n (divmod m (Num.Bit0 n)))"
proof (cases "m < n")
  case True then have "numeral m < numeral n" by simp
  then show ?thesis
    by (simp add: prod_eq_iff div_less mod_less fst_divmod snd_divmod)
next
  case False
  have "divmod m n =
    divmod_step n (numeral m div (2 * numeral n),
      numeral m mod (2 * numeral n))"
  proof (cases "numeral n \<le> numeral m mod (2 * numeral n)")
    case True
    with divmod_step_eq
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)) + 1, numeral m mod (2 * numeral n) - numeral n)"
        by simp
    moreover from True divmod_digit_1 [of "numeral m" "numeral n"]
      have "2 * (numeral m div (2 * numeral n)) + 1 = numeral m div numeral n"
      and "numeral m mod (2 * numeral n) - numeral n = numeral m mod numeral n"
      by simp_all
    ultimately show ?thesis by (simp only: divmod_def)
  next
    case False then have *: "numeral m mod (2 * numeral n) < numeral n"
      by (simp add: not_le)
    with divmod_step_eq
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)), numeral m mod (2 * numeral n))"
        by auto
    moreover from * divmod_digit_0 [of "numeral n" "numeral m"]
      have "2 * (numeral m div (2 * numeral n)) = numeral m div numeral n"
      and "numeral m mod (2 * numeral n) = numeral m mod numeral n"
      by (simp_all only: zero_less_numeral)
    ultimately show ?thesis by (simp only: divmod_def)
  qed
  then have "divmod m n =
    divmod_step n (numeral m div numeral (Num.Bit0 n),
      numeral m mod numeral (Num.Bit0 n))"
    by (simp only: numeral.simps distrib mult_1)
  then have "divmod m n = divmod_step n (divmod m (Num.Bit0 n))"
    by (simp add: divmod_def)
  with False show ?thesis by simp
qed

text \<open>The division rewrite proper -- first, trivial results involving \<open>1\<close>\<close>

lemma divmod_trivial [simp]:
  "divmod Num.One Num.One = (numeral Num.One, 0)"
  "divmod (Num.Bit0 m) Num.One = (numeral (Num.Bit0 m), 0)"
  "divmod (Num.Bit1 m) Num.One = (numeral (Num.Bit1 m), 0)"
  "divmod num.One (num.Bit0 n) = (0, Numeral1)"
  "divmod num.One (num.Bit1 n) = (0, Numeral1)"
  using divmod_divmod_step [of "Num.One"] by (simp_all add: divmod_def)

text \<open>Division by an even number is a right-shift\<close>

lemma divmod_cancel [simp]:
  "divmod (Num.Bit0 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r))" (is ?P)
  "divmod (Num.Bit1 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r + 1))" (is ?Q)
proof -
  have *: "\<And>q. numeral (Num.Bit0 q) = 2 * numeral q"
    "\<And>q. numeral (Num.Bit1 q) = 2 * numeral q + 1"
    by (simp_all only: numeral_mult numeral.simps distrib) simp_all
  have "1 div 2 = 0" "1 mod 2 = 1" by (auto intro: div_less mod_less)
  then show ?P and ?Q
    by (simp_all add: fst_divmod snd_divmod prod_eq_iff split_def * [of m] * [of n] mod_mult_mult1
      div_mult2_eq [of _ _ 2] mod_mult2_eq [of _ _ 2]
      add.commute del: numeral_times_numeral)
qed

text \<open>The really hard work\<close>

lemma divmod_steps [simp]:
  "divmod (num.Bit0 m) (num.Bit1 n) =
      (if m \<le> n then (0, numeral (num.Bit0 m))
       else divmod_step (num.Bit1 n)
             (divmod (num.Bit0 m)
               (num.Bit0 (num.Bit1 n))))"
  "divmod (num.Bit1 m) (num.Bit1 n) =
      (if m < n then (0, numeral (num.Bit1 m))
       else divmod_step (num.Bit1 n)
             (divmod (num.Bit1 m)
               (num.Bit0 (num.Bit1 n))))"
  by (simp_all add: divmod_divmod_step)

lemmas divmod_algorithm_code = divmod_step_eq divmod_trivial divmod_cancel divmod_steps  

text \<open>Special case: divisibility\<close>

definition divides_aux :: "'a \<times> 'a \<Rightarrow> bool"
where
  "divides_aux qr \<longleftrightarrow> snd qr = 0"

lemma divides_aux_eq [simp]:
  "divides_aux (q, r) \<longleftrightarrow> r = 0"
  by (simp add: divides_aux_def)

lemma dvd_numeral_simp [simp]:
  "numeral m dvd numeral n \<longleftrightarrow> divides_aux (divmod n m)"
  by (simp add: divmod_def mod_eq_0_iff_dvd)

text \<open>Generic computation of quotient and remainder\<close>  

lemma numeral_div_numeral [simp]: 
  "numeral k div numeral l = fst (divmod k l)"
  by (simp add: fst_divmod)

lemma numeral_mod_numeral [simp]: 
  "numeral k mod numeral l = snd (divmod k l)"
  by (simp add: snd_divmod)

lemma one_div_numeral [simp]:
  "1 div numeral n = fst (divmod num.One n)"
  by (simp add: fst_divmod)

lemma one_mod_numeral [simp]:
  "1 mod numeral n = snd (divmod num.One n)"
  by (simp add: snd_divmod)

text \<open>Computing congruences modulo \<open>2 ^ q\<close>\<close>

lemma cong_exp_iff_simps:
  "numeral n mod numeral Num.One = 0
    \<longleftrightarrow> True"
  "numeral (Num.Bit0 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> numeral n mod numeral q = 0"
  "numeral (Num.Bit1 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> False"
  "numeral m mod numeral Num.One = (numeral n mod numeral Num.One)
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral n mod numeral q) = 0"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral m mod numeral q) = 0"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  by (auto simp add: case_prod_beta dest: arg_cong [of _ _ even])

end


subsection \<open>Division on @{typ nat}\<close>

context
begin

text \<open>
  We define @{const divide} and @{const modulo} on @{typ nat} by means
  of a characteristic relation with two input arguments
  @{term "m::nat"}, @{term "n::nat"} and two output arguments
  @{term "q::nat"}(uotient) and @{term "r::nat"}(emainder).
\<close>

inductive eucl_rel_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where eucl_rel_nat_by0: "eucl_rel_nat m 0 (0, m)"
  | eucl_rel_natI: "r < n \<Longrightarrow> m = q * n + r \<Longrightarrow> eucl_rel_nat m n (q, r)"

text \<open>@{const eucl_rel_nat} is total:\<close>

qualified lemma eucl_rel_nat_ex:
  obtains q r where "eucl_rel_nat m n (q, r)"
proof (cases "n = 0")
  case True
  with that eucl_rel_nat_by0 show thesis
    by blast
next
  case False
  have "\<exists>q r. m = q * n + r \<and> r < n"
  proof (induct m)
    case 0 with \<open>n \<noteq> 0\<close>
    have "(0::nat) = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    case (Suc m) then obtain q' r'
      where m: "m = q' * n + r'" and n: "r' < n" by auto
    then show ?case proof (cases "Suc r' < n")
      case True
      from m n have "Suc m = q' * n + Suc r'" by simp
      with True show ?thesis by blast
    next
      case False then have "n \<le> Suc r'"
        by (simp add: not_less)
      moreover from n have "Suc r' \<le> n"
        by (simp add: Suc_le_eq)
      ultimately have "n = Suc r'" by auto
      with m have "Suc m = Suc q' * n + 0" by simp
      with \<open>n \<noteq> 0\<close> show ?thesis by blast
    qed
  qed
  with that \<open>n \<noteq> 0\<close> eucl_rel_natI show thesis
    by blast
qed

text \<open>@{const eucl_rel_nat} is injective:\<close>

qualified lemma eucl_rel_nat_unique_div:
  assumes "eucl_rel_nat m n (q, r)"
    and "eucl_rel_nat m n (q', r')"
  shows "q = q'"
proof (cases "n = 0")
  case True with assms show ?thesis
    by (auto elim: eucl_rel_nat.cases)
next
  case False
  have *: "q' \<le> q" if "q' * n + r' = q * n + r" "r < n" for q r q' r' :: nat
  proof (rule ccontr)
    assume "\<not> q' \<le> q"
    then have "q < q'"
      by (simp add: not_le)
    with that show False
      by (auto simp add: less_iff_Suc_add algebra_simps)
  qed
  from \<open>n \<noteq> 0\<close> assms show ?thesis
    by (auto intro: order_antisym elim: eucl_rel_nat.cases dest: * sym split: if_splits)
qed

qualified lemma eucl_rel_nat_unique_mod:
  assumes "eucl_rel_nat m n (q, r)"
    and "eucl_rel_nat m n (q', r')"
  shows "r = r'"
proof -
  from assms have "q' = q"
    by (auto intro: eucl_rel_nat_unique_div)
  with assms show ?thesis
    by (auto elim!: eucl_rel_nat.cases)
qed

text \<open>
  We instantiate divisibility on the natural numbers by
  means of @{const eucl_rel_nat}:
\<close>

qualified definition divmod_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "divmod_nat m n = (THE qr. eucl_rel_nat m n qr)"

qualified lemma eucl_rel_nat_divmod_nat:
  "eucl_rel_nat m n (divmod_nat m n)"
proof -
  from eucl_rel_nat_ex
    obtain q r where rel: "eucl_rel_nat m n (q, r)" .
  then show ?thesis
    by (auto simp add: divmod_nat_def intro: theI
      elim: eucl_rel_nat_unique_div eucl_rel_nat_unique_mod)
qed

qualified lemma divmod_nat_unique:
  "divmod_nat m n = (q, r)" if "eucl_rel_nat m n (q, r)"
  using that
  by (auto simp add: divmod_nat_def intro: eucl_rel_nat_divmod_nat elim: eucl_rel_nat_unique_div eucl_rel_nat_unique_mod)

qualified lemma divmod_nat_zero:
  "divmod_nat m 0 = (0, m)"
  by (rule divmod_nat_unique) (fact eucl_rel_nat_by0)

qualified lemma divmod_nat_zero_left:
  "divmod_nat 0 n = (0, 0)"
  by (rule divmod_nat_unique) 
    (cases n, auto intro: eucl_rel_nat_by0 eucl_rel_natI)

qualified lemma divmod_nat_base:
  "m < n \<Longrightarrow> divmod_nat m n = (0, m)"
  by (rule divmod_nat_unique) 
    (cases n, auto intro: eucl_rel_nat_by0 eucl_rel_natI)

qualified lemma divmod_nat_step:
  assumes "0 < n" and "n \<le> m"
  shows "divmod_nat m n =
    (Suc (fst (divmod_nat (m - n) n)), snd (divmod_nat (m - n) n))"
proof (rule divmod_nat_unique)
  have "eucl_rel_nat (m - n) n (divmod_nat (m - n) n)"
    by (fact eucl_rel_nat_divmod_nat)
  then show "eucl_rel_nat m n (Suc
    (fst (divmod_nat (m - n) n)), snd (divmod_nat (m - n) n))"
    using assms
      by (auto split: if_splits intro: eucl_rel_natI elim!: eucl_rel_nat.cases simp add: algebra_simps)
qed

end

instantiation nat :: "{semidom_modulo, normalization_semidom}"
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
  where div_nat_def: "m div n = fst (Divides.divmod_nat m n)"

definition modulo_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where mod_nat_def: "m mod n = snd (Divides.divmod_nat m n)"

lemma fst_divmod_nat [simp]:
  "fst (Divides.divmod_nat m n) = m div n"
  by (simp add: div_nat_def)

lemma snd_divmod_nat [simp]:
  "snd (Divides.divmod_nat m n) = m mod n"
  by (simp add: mod_nat_def)

lemma divmod_nat_div_mod:
  "Divides.divmod_nat m n = (m div n, m mod n)"
  by (simp add: prod_eq_iff)

lemma div_nat_unique:
  assumes "eucl_rel_nat m n (q, r)"
  shows "m div n = q"
  using assms
  by (auto dest!: Divides.divmod_nat_unique simp add: prod_eq_iff)

lemma mod_nat_unique:
  assumes "eucl_rel_nat m n (q, r)"
  shows "m mod n = r"
  using assms
  by (auto dest!: Divides.divmod_nat_unique simp add: prod_eq_iff)

lemma eucl_rel_nat: "eucl_rel_nat m n (m div n, m mod n)"
  using Divides.eucl_rel_nat_divmod_nat
  by (simp add: divmod_nat_div_mod)

text \<open>The ''recursion'' equations for @{const divide} and @{const modulo}\<close>

lemma div_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m div n = 0"
  using assms Divides.divmod_nat_base by (simp add: prod_eq_iff)

lemma le_div_geq:
  fixes m n :: nat
  assumes "0 < n" and "n \<le> m"
  shows "m div n = Suc ((m - n) div n)"
  using assms Divides.divmod_nat_step by (simp add: prod_eq_iff)

lemma mod_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m mod n = m"
  using assms Divides.divmod_nat_base by (simp add: prod_eq_iff)

lemma le_mod_geq:
  fixes m n :: nat
  assumes "n \<le> m"
  shows "m mod n = (m - n) mod n"
  using assms Divides.divmod_nat_step by (cases "n = 0") (simp_all add: prod_eq_iff)

lemma mod_less_divisor [simp]:
  fixes m n :: nat
  assumes "n > 0"
  shows "m mod n < n"
  using assms eucl_rel_nat [of m n]
    by (auto elim: eucl_rel_nat.cases)

lemma mod_le_divisor [simp]:
  fixes m n :: nat
  assumes "n > 0"
  shows "m mod n \<le> n"
  using assms eucl_rel_nat [of m n]
    by (auto elim: eucl_rel_nat.cases)

instance proof
  fix m n :: nat
  show "m div n * n + m mod n = m"
    using eucl_rel_nat [of m n]
    by (auto elim: eucl_rel_nat.cases)
next
  fix n :: nat show "n div 0 = 0"
    by (simp add: div_nat_def Divides.divmod_nat_zero)
next
  fix m n :: nat
  assume "n \<noteq> 0"
  then show "m * n div n = m"
    by (auto intro!: eucl_rel_natI div_nat_unique [of _ _ _ 0])
qed (simp_all add: unit_factor_nat_def)

end

instance nat :: semiring_div
proof
  fix m n q :: nat
  assume "n \<noteq> 0"
  then show "(q + m * n) div n = m + q div n"
    by (induct m) (simp_all add: le_div_geq)
next
  fix m n q :: nat
  assume "m \<noteq> 0"
  show "(m * n) div (m * q) = n div q"
  proof (cases "q = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    show ?thesis
    proof (rule div_nat_unique [of _ _ _ "m * (n mod q)"])
      show "eucl_rel_nat (m * n) (m * q) (n div q, m * (n mod q))"
        by (rule eucl_rel_natI)
          (use \<open>m \<noteq> 0\<close> \<open>q \<noteq> 0\<close> div_mult_mod_eq [of n q] in \<open>auto simp add: algebra_simps distrib_left [symmetric]\<close>)
    qed          
  qed
qed

lemma div_by_Suc_0 [simp]:
  "m div Suc 0 = m"
  using div_by_1 [of m] by simp

lemma mod_by_Suc_0 [simp]:
  "m mod Suc 0 = 0"
  using mod_by_1 [of m] by simp

lemma mod_greater_zero_iff_not_dvd:
  fixes m n :: nat
  shows "m mod n > 0 \<longleftrightarrow> \<not> n dvd m"
  by (simp add: dvd_eq_mod_eq_0)

instantiation nat :: unique_euclidean_semiring
begin

definition [simp]:
  "euclidean_size_nat = (id :: nat \<Rightarrow> nat)"

definition [simp]:
  "uniqueness_constraint_nat = (top :: nat \<Rightarrow> nat \<Rightarrow> bool)"

instance
  by standard (use mult_le_mono2 [of 1] in \<open>simp_all add: unit_factor_nat_def mod_greater_zero_iff_not_dvd\<close>)

end

text \<open>Simproc for cancelling @{const divide} and @{const modulo}\<close>

lemma (in semiring_modulo) cancel_div_mod_rules:
  "((a div b) * b + a mod b) + c = a + c"
  "(b * (a div b) + a mod b) + c = a + c"
  by (simp_all add: div_mult_mod_eq mult_div_mod_eq)

ML_file "~~/src/Provers/Arith/cancel_div_mod.ML"

ML \<open>
structure Cancel_Div_Mod_Nat = Cancel_Div_Mod
(
  val div_name = @{const_name divide};
  val mod_name = @{const_name modulo};
  val mk_binop = HOLogic.mk_binop;
  val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};
  val dest_plus = HOLogic.dest_bin @{const_name Groups.plus} HOLogic.natT;
  fun mk_sum [] = HOLogic.zero
    | mk_sum [t] = t
    | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);
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

lemma divmod_nat_if [code]:
  "Divides.divmod_nat m n = (if n = 0 \<or> m < n then (0, m) else
    let (q, r) = Divides.divmod_nat (m - n) n in (Suc q, r))"
  by (simp add: prod_eq_iff case_prod_beta not_less le_div_geq le_mod_geq)

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


subsubsection \<open>Quotient\<close>

lemma div_geq: "0 < n \<Longrightarrow>  \<not> m < n \<Longrightarrow> m div n = Suc ((m - n) div n)"
by (simp add: le_div_geq linorder_not_less)

lemma div_if: "0 < n \<Longrightarrow> m div n = (if m < n then 0 else Suc ((m - n) div n))"
by (simp add: div_geq)

lemma div_mult_self_is_m [simp]: "0<n ==> (m*n) div n = (m::nat)"
by simp

lemma div_mult_self1_is_m [simp]: "0<n ==> (n*m) div n = (m::nat)"
by simp

lemma div_positive:
  fixes m n :: nat
  assumes "n > 0"
  assumes "m \<ge> n"
  shows "m div n > 0"
proof -
  from \<open>m \<ge> n\<close> obtain q where "m = n + q"
    by (auto simp add: le_iff_add)
  with \<open>n > 0\<close> show ?thesis by (simp add: div_add_self1)
qed

lemma div_eq_0_iff: "(a div b::nat) = 0 \<longleftrightarrow> a < b \<or> b = 0"
  by auto (metis div_positive less_numeral_extra(3) not_less)


subsubsection \<open>Remainder\<close>

lemma mod_Suc_le_divisor [simp]:
  "m mod Suc n \<le> n"
  using mod_less_divisor [of "Suc n" m] by arith

lemma mod_less_eq_dividend [simp]:
  fixes m n :: nat
  shows "m mod n \<le> m"
proof (rule add_leD2)
  from div_mult_mod_eq have "m div n * n + m mod n = m" .
  then show "m div n * n + m mod n \<le> m" by auto
qed

lemma mod_geq: "\<not> m < (n::nat) \<Longrightarrow> m mod n = (m - n) mod n"
by (simp add: le_mod_geq linorder_not_less)

lemma mod_if: "m mod (n::nat) = (if m < n then m else (m - n) mod n)"
by (simp add: le_mod_geq)


subsubsection \<open>Quotient and Remainder\<close>

lemma div_mult1_eq:
  "(a * b) div c = a * (b div c) + a * (b mod c) div (c::nat)"
  by (cases "c = 0")
     (auto simp add: algebra_simps distrib_left [symmetric]
     intro!: div_nat_unique [of _ _ _ "(a * (b mod c)) mod c"] eucl_rel_natI)

lemma eucl_rel_nat_add1_eq:
  "eucl_rel_nat a c (aq, ar) \<Longrightarrow> eucl_rel_nat b c (bq, br)
   \<Longrightarrow> eucl_rel_nat (a + b) c (aq + bq + (ar + br) div c, (ar + br) mod c)"
  by (auto simp add: split_ifs algebra_simps elim!: eucl_rel_nat.cases intro: eucl_rel_nat_by0 eucl_rel_natI)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma div_add1_eq:
  "(a + b) div (c::nat) = a div c + b div c + ((a mod c + b mod c) div c)"
by (blast intro: eucl_rel_nat_add1_eq [THEN div_nat_unique] eucl_rel_nat)

lemma eucl_rel_nat_mult2_eq:
  assumes "eucl_rel_nat a b (q, r)"
  shows "eucl_rel_nat a (b * c) (q div c, b *(q mod c) + r)"
proof (cases "c = 0")
  case True
  with assms show ?thesis
    by (auto intro: eucl_rel_nat_by0 elim!: eucl_rel_nat.cases simp add: ac_simps)
next
  case False
  { assume "r < b"
    with False have "b * (q mod c) + r < b * c"
      apply (cut_tac m = q and n = c in mod_less_divisor)
      apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
      apply (erule_tac P = "%x. lhs < rhs x" for lhs rhs in ssubst)
      apply (simp add: add_mult_distrib2)
      done
    then have "r + b * (q mod c) < b * c"
      by (simp add: ac_simps)
  } with assms False show ?thesis
    by (auto simp add: algebra_simps add_mult_distrib2 [symmetric] elim!: eucl_rel_nat.cases intro: eucl_rel_nat.intros)
qed

lemma div_mult2_eq: "a div (b * c) = (a div b) div (c::nat)"
by (force simp add: eucl_rel_nat [THEN eucl_rel_nat_mult2_eq, THEN div_nat_unique])

lemma mod_mult2_eq: "a mod (b * c) = b * (a div b mod c) + a mod (b::nat)"
by (auto simp add: mult.commute eucl_rel_nat [THEN eucl_rel_nat_mult2_eq, THEN mod_nat_unique])

instantiation nat :: semiring_numeral_div
begin

definition divmod_nat :: "num \<Rightarrow> num \<Rightarrow> nat \<times> nat"
where
  divmod'_nat_def: "divmod_nat m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_nat :: "num \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat"
where
  "divmod_step_nat l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

instance
  by standard (auto intro: div_positive simp add: divmod'_nat_def divmod_step_nat_def mod_mult2_eq div_mult2_eq)

end

declare divmod_algorithm_code [where ?'a = nat, code]
  

subsubsection \<open>Further Facts about Quotient and Remainder\<close>

lemma div_le_mono:
  fixes m n k :: nat
  assumes "m \<le> n"
  shows "m div k \<le> n div k"
proof -
  from assms obtain q where "n = m + q"
    by (auto simp add: le_iff_add)
  then show ?thesis
    by (simp add: div_add1_eq [of m q k])
qed

(* Antimonotonicity of div in second argument *)
lemma div_le_mono2: "!!m::nat. [| 0<m; m\<le>n |] ==> (k div n) \<le> (k div m)"
apply (subgoal_tac "0<n")
 prefer 2 apply simp
apply (induct_tac k rule: nat_less_induct)
apply (rename_tac "k")
apply (case_tac "k<n", simp)
apply (subgoal_tac "~ (k<m) ")
 prefer 2 apply simp
apply (simp add: div_geq)
apply (subgoal_tac "(k-n) div n \<le> (k-m) div n")
 prefer 2
 apply (blast intro: div_le_mono diff_le_mono2)
apply (rule le_trans, simp)
apply (simp)
done

lemma div_le_dividend [simp]: "m div n \<le> (m::nat)"
apply (case_tac "n=0", simp)
apply (subgoal_tac "m div n \<le> m div 1", simp)
apply (rule div_le_mono2)
apply (simp_all (no_asm_simp))
done

(* Similar for "less than" *)
lemma div_less_dividend [simp]:
  "\<lbrakk>(1::nat) < n; 0 < m\<rbrakk> \<Longrightarrow> m div n < m"
apply (induct m rule: nat_less_induct)
apply (rename_tac "m")
apply (case_tac "m<n", simp)
apply (subgoal_tac "0<n")
 prefer 2 apply simp
apply (simp add: div_geq)
apply (case_tac "n<m")
 apply (subgoal_tac "(m-n) div n < (m-n) ")
  apply (rule impI less_trans_Suc)+
apply assumption
  apply (simp_all)
done

text\<open>A fact for the mutilated chess board\<close>
lemma mod_Suc: "Suc(m) mod n = (if Suc(m mod n) = n then 0 else Suc(m mod n))"
apply (case_tac "n=0", simp)
apply (induct "m" rule: nat_less_induct)
apply (case_tac "Suc (na) <n")
(* case Suc(na) < n *)
apply (frule lessI [THEN less_trans], simp add: less_not_refl3)
(* case n \<le> Suc(na) *)
apply (simp add: linorder_not_less le_Suc_eq mod_geq)
apply (auto simp add: Suc_diff_le le_mod_geq)
done

lemma mod_eq_0_iff: "(m mod d = 0) = (\<exists>q::nat. m = d*q)"
by (auto simp add: dvd_eq_mod_eq_0 [symmetric] dvd_def)

lemmas mod_eq_0D [dest!] = mod_eq_0_iff [THEN iffD1]

(*Loses information, namely we also have r<d provided d is nonzero*)
lemma mod_eqD:
  fixes m d r q :: nat
  assumes "m mod d = r"
  shows "\<exists>q. m = r + q * d"
proof -
  from div_mult_mod_eq obtain q where "q * d + m mod d = m" by blast
  with assms have "m = r + q * d" by simp
  then show ?thesis ..
qed

lemma split_div:
 "P(n div k :: nat) =
 ((k = 0 \<longrightarrow> P 0) \<and> (k \<noteq> 0 \<longrightarrow> (!i. !j<k. n = k*i + j \<longrightarrow> P i)))"
 (is "?P = ?Q" is "_ = (_ \<and> (_ \<longrightarrow> ?R))")
proof
  assume P: ?P
  show ?Q
  proof (cases)
    assume "k = 0"
    with P show ?Q by simp
  next
    assume not0: "k \<noteq> 0"
    thus ?Q
    proof (simp, intro allI impI)
      fix i j
      assume n: "n = k*i + j" and j: "j < k"
      show "P i"
      proof (cases)
        assume "i = 0"
        with n j P show "P i" by simp
      next
        assume "i \<noteq> 0"
        with not0 n j P show "P i" by(simp add:ac_simps)
      qed
    qed
  qed
next
  assume Q: ?Q
  show ?P
  proof (cases)
    assume "k = 0"
    with Q show ?P by simp
  next
    assume not0: "k \<noteq> 0"
    with Q have R: ?R by simp
    from not0 R[THEN spec,of "n div k",THEN spec, of "n mod k"]
    show ?P by simp
  qed
qed

lemma split_div_lemma:
  assumes "0 < n"
  shows "n * q \<le> m \<and> m < n * Suc q \<longleftrightarrow> q = ((m::nat) div n)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  with minus_mod_eq_mult_div [symmetric] have nq: "n * q = m - (m mod n)" by simp
  then have A: "n * q \<le> m" by simp
  have "n - (m mod n) > 0" using mod_less_divisor assms by auto
  then have "m < m + (n - (m mod n))" by simp
  then have "m < n + (m - (m mod n))" by simp
  with nq have "m < n + n * q" by simp
  then have B: "m < n * Suc q" by simp
  from A B show ?lhs ..
next
  assume P: ?lhs
  then have "eucl_rel_nat m n (q, m - n * q)"
    by (auto intro: eucl_rel_natI simp add: ac_simps)
  then have "m div n = q"
    by (rule div_nat_unique)
  then show ?rhs by simp
qed

theorem split_div':
  "P ((m::nat) div n) = ((n = 0 \<and> P 0) \<or>
   (\<exists>q. (n * q \<le> m \<and> m < n * (Suc q)) \<and> P q))"
  apply (cases "0 < n")
  apply (simp only: add: split_div_lemma)
  apply simp_all
  done

lemma split_mod:
 "P(n mod k :: nat) =
 ((k = 0 \<longrightarrow> P n) \<and> (k \<noteq> 0 \<longrightarrow> (!i. !j<k. n = k*i + j \<longrightarrow> P j)))"
 (is "?P = ?Q" is "_ = (_ \<and> (_ \<longrightarrow> ?R))")
proof
  assume P: ?P
  show ?Q
  proof (cases)
    assume "k = 0"
    with P show ?Q by simp
  next
    assume not0: "k \<noteq> 0"
    thus ?Q
    proof (simp, intro allI impI)
      fix i j
      assume "n = k*i + j" "j < k"
      thus "P j" using not0 P by (simp add: ac_simps)
    qed
  qed
next
  assume Q: ?Q
  show ?P
  proof (cases)
    assume "k = 0"
    with Q show ?P by simp
  next
    assume not0: "k \<noteq> 0"
    with Q have R: ?R by simp
    from not0 R[THEN spec,of "n div k",THEN spec, of "n mod k"]
    show ?P by simp
  qed
qed

lemma div_eq_dividend_iff: "a \<noteq> 0 \<Longrightarrow> (a :: nat) div b = a \<longleftrightarrow> b = 1"
  apply rule
  apply (cases "b = 0")
  apply simp_all
  apply (metis (full_types) One_nat_def Suc_lessI div_less_dividend less_not_refl3)
  done

lemma (in field_char_0) of_nat_div:
  "of_nat (m div n) = ((of_nat m - of_nat (m mod n)) / of_nat n)"
proof -
  have "of_nat (m div n) = ((of_nat (m div n * n + m mod n) - of_nat (m mod n)) / of_nat n :: 'a)"
    unfolding of_nat_add by (cases "n = 0") simp_all
  then show ?thesis
    by simp
qed


subsubsection \<open>An ``induction'' law for modulus arithmetic.\<close>

lemma mod_induct_0:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p"
  shows "P 0"
proof (rule ccontr)
  assume contra: "\<not>(P 0)"
  from i have p: "0<p" by simp
  have "\<forall>k. 0<k \<longrightarrow> \<not> P (p-k)" (is "\<forall>k. ?A k")
  proof
    fix k
    show "?A k"
    proof (induct k)
      show "?A 0" by simp  \<comment> "by contradiction"
    next
      fix n
      assume ih: "?A n"
      show "?A (Suc n)"
      proof (clarsimp)
        assume y: "P (p - Suc n)"
        have n: "Suc n < p"
        proof (rule ccontr)
          assume "\<not>(Suc n < p)"
          hence "p - Suc n = 0"
            by simp
          with y contra show "False"
            by simp
        qed
        hence n2: "Suc (p - Suc n) = p-n" by arith
        from p have "p - Suc n < p" by arith
        with y step have z: "P ((Suc (p - Suc n)) mod p)"
          by blast
        show "False"
        proof (cases "n=0")
          case True
          with z n2 contra show ?thesis by simp
        next
          case False
          with p have "p-n < p" by arith
          with z n2 False ih show ?thesis by simp
        qed
      qed
    qed
  qed
  moreover
  from i obtain k where "0<k \<and> i+k=p"
    by (blast dest: less_imp_add_positive)
  hence "0<k \<and> i=p-k" by auto
  moreover
  note base
  ultimately
  show "False" by blast
qed

lemma mod_induct:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p" and j: "j<p"
  shows "P j"
proof -
  have "\<forall>j<p. P j"
  proof
    fix j
    show "j<p \<longrightarrow> P j" (is "?A j")
    proof (induct j)
      from step base i show "?A 0"
        by (auto elim: mod_induct_0)
    next
      fix k
      assume ih: "?A k"
      show "?A (Suc k)"
      proof
        assume suc: "Suc k < p"
        hence k: "k<p" by simp
        with ih have "P k" ..
        with step k have "P (Suc k mod p)"
          by blast
        moreover
        from suc have "Suc k mod p = Suc k"
          by simp
        ultimately
        show "P (Suc k)" by simp
      qed
    qed
  qed
  with j show ?thesis by blast
qed

lemma div2_Suc_Suc [simp]: "Suc (Suc m) div 2 = Suc (m div 2)"
  by (simp add: numeral_2_eq_2 le_div_geq)

lemma mod2_Suc_Suc [simp]: "Suc (Suc m) mod 2 = m mod 2"
  by (simp add: numeral_2_eq_2 le_mod_geq)

lemma add_self_div_2 [simp]: "(m + m) div 2 = (m::nat)"
by (simp add: mult_2 [symmetric])

lemma mod2_gr_0 [simp]: "0 < (m::nat) mod 2 \<longleftrightarrow> m mod 2 = 1"
proof -
  { fix n :: nat have  "(n::nat) < 2 \<Longrightarrow> n = 0 \<or> n = 1" by (cases n) simp_all }
  moreover have "m mod 2 < 2" by simp
  ultimately have "m mod 2 = 0 \<or> m mod 2 = 1" .
  then show ?thesis by auto
qed

text\<open>These lemmas collapse some needless occurrences of Suc:
    at least three Sucs, since two and fewer are rewritten back to Suc again!
    We already have some rules to simplify operands smaller than 3.\<close>

lemma div_Suc_eq_div_add3 [simp]: "m div (Suc (Suc (Suc n))) = m div (3+n)"
by (simp add: Suc3_eq_add_3)

lemma mod_Suc_eq_mod_add3 [simp]: "m mod (Suc (Suc (Suc n))) = m mod (3+n)"
by (simp add: Suc3_eq_add_3)

lemma Suc_div_eq_add3_div: "(Suc (Suc (Suc m))) div n = (3+m) div n"
by (simp add: Suc3_eq_add_3)

lemma Suc_mod_eq_add3_mod: "(Suc (Suc (Suc m))) mod n = (3+m) mod n"
by (simp add: Suc3_eq_add_3)

lemmas Suc_div_eq_add3_div_numeral [simp] = Suc_div_eq_add3_div [of _ "numeral v"] for v
lemmas Suc_mod_eq_add3_mod_numeral [simp] = Suc_mod_eq_add3_mod [of _ "numeral v"] for v

lemma Suc_times_mod_eq: "1<k ==> Suc (k * m) mod k = 1"
apply (induct "m")
apply (simp_all add: mod_Suc)
done

declare Suc_times_mod_eq [of "numeral w", simp] for w

lemma Suc_div_le_mono [simp]: "n div k \<le> (Suc n) div k"
by (simp add: div_le_mono)

lemma Suc_n_div_2_gt_zero [simp]: "(0::nat) < n ==> 0 < (n + 1) div 2"
by (cases n) simp_all

lemma div_2_gt_zero [simp]: assumes A: "(1::nat) < n" shows "0 < n div 2"
proof -
  from A have B: "0 < n - 1" and C: "n - 1 + 1 = n" by simp_all
  from Suc_n_div_2_gt_zero [OF B] C show ?thesis by simp
qed

lemma mod_mult_self3' [simp]: "Suc (k * n + m) mod n = Suc m mod n"
  using mod_mult_self3 [of k n "Suc m"] by simp

lemma mod_Suc_eq_Suc_mod: "Suc m mod n = Suc (m mod n) mod n"
apply (subst mod_Suc [of m])
apply (subst mod_Suc [of "m mod n"], simp)
done

lemma mod_2_not_eq_zero_eq_one_nat:
  fixes n :: nat
  shows "n mod 2 \<noteq> 0 \<longleftrightarrow> n mod 2 = 1"
  by (fact not_mod_2_eq_0_eq_1)

lemma even_Suc_div_two [simp]:
  "even n \<Longrightarrow> Suc n div 2 = n div 2"
  using even_succ_div_two [of n] by simp

lemma odd_Suc_div_two [simp]:
  "odd n \<Longrightarrow> Suc n div 2 = Suc (n div 2)"
  using odd_succ_div_two [of n] by simp

lemma odd_two_times_div_two_nat [simp]:
  assumes "odd n"
  shows "2 * (n div 2) = n - (1 :: nat)"
proof -
  from assms have "2 * (n div 2) + 1 = n"
    by (rule odd_two_times_div_two_succ)
  then have "Suc (2 * (n div 2)) - 1 = n - 1"
    by simp
  then show ?thesis
    by simp
qed

lemma parity_induct [case_names zero even odd]:
  assumes zero: "P 0"
  assumes even: "\<And>n. P n \<Longrightarrow> P (2 * n)"
  assumes odd: "\<And>n. P n \<Longrightarrow> P (Suc (2 * n))"
  shows "P n"
proof (induct n rule: less_induct)
  case (less n)
  show "P n"
  proof (cases "n = 0")
    case True with zero show ?thesis by simp
  next
    case False
    with less have hyp: "P (n div 2)" by simp
    show ?thesis
    proof (cases "even n")
      case True
      with hyp even [of "n div 2"] show ?thesis
        by simp
    next
      case False
      with hyp odd [of "n div 2"] show ?thesis
        by simp
    qed
  qed
qed

lemma Suc_0_div_numeral [simp]:
  fixes k l :: num
  shows "Suc 0 div numeral k = fst (divmod Num.One k)"
  by (simp_all add: fst_divmod)

lemma Suc_0_mod_numeral [simp]:
  fixes k l :: num
  shows "Suc 0 mod numeral k = snd (divmod Num.One k)"
  by (simp_all add: snd_divmod)


subsection \<open>Division on @{typ int}\<close>

context
begin

inductive eucl_rel_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> bool"
  where eucl_rel_int_by0: "eucl_rel_int k 0 (0, k)"
  | eucl_rel_int_dividesI: "l \<noteq> 0 \<Longrightarrow> k = q * l \<Longrightarrow> eucl_rel_int k l (q, 0)"
  | eucl_rel_int_remainderI: "sgn r = sgn l \<Longrightarrow> \<bar>r\<bar> < \<bar>l\<bar>
      \<Longrightarrow> k = q * l + r \<Longrightarrow> eucl_rel_int k l (q, r)"

lemma eucl_rel_int_iff:    
  "eucl_rel_int k l (q, r) \<longleftrightarrow> 
    k = l * q + r \<and>
     (if 0 < l then 0 \<le> r \<and> r < l else if l < 0 then l < r \<and> r \<le> 0 else q = 0)"
  by (cases "r = 0")
    (auto elim!: eucl_rel_int.cases intro: eucl_rel_int_by0 eucl_rel_int_dividesI eucl_rel_int_remainderI
    simp add: ac_simps sgn_1_pos sgn_1_neg)

lemma unique_quotient_lemma:
  "b * q' + r' \<le> b * q + r \<Longrightarrow> 0 \<le> r' \<Longrightarrow> r' < b \<Longrightarrow> r < b \<Longrightarrow> q' \<le> (q::int)"
apply (subgoal_tac "r' + b * (q'-q) \<le> r")
 prefer 2 apply (simp add: right_diff_distrib)
apply (subgoal_tac "0 < b * (1 + q - q') ")
apply (erule_tac [2] order_le_less_trans)
 prefer 2 apply (simp add: right_diff_distrib distrib_left)
apply (subgoal_tac "b * q' < b * (1 + q) ")
 prefer 2 apply (simp add: right_diff_distrib distrib_left)
apply (simp add: mult_less_cancel_left)
done

lemma unique_quotient_lemma_neg:
  "b * q' + r' \<le> b*q + r \<Longrightarrow> r \<le> 0 \<Longrightarrow> b < r \<Longrightarrow> b < r' \<Longrightarrow> q \<le> (q'::int)"
  by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma) auto

lemma unique_quotient:
  "eucl_rel_int a b (q, r) \<Longrightarrow> eucl_rel_int a b (q', r') \<Longrightarrow> q = q'"
  apply (simp add: eucl_rel_int_iff linorder_neq_iff split: if_split_asm)
  apply (blast intro: order_antisym
    dest: order_eq_refl [THEN unique_quotient_lemma]
    order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
  done

lemma unique_remainder:
  "eucl_rel_int a b (q, r) \<Longrightarrow> eucl_rel_int a b (q', r') \<Longrightarrow> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: eucl_rel_int_iff)
apply (blast intro: unique_quotient)
done

end

instantiation int :: "{idom_modulo, normalization_semidom}"
begin

definition normalize_int :: "int \<Rightarrow> int"
  where [simp]: "normalize = (abs :: int \<Rightarrow> int)"

definition unit_factor_int :: "int \<Rightarrow> int"
  where [simp]: "unit_factor = (sgn :: int \<Rightarrow> int)"

definition divide_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "k div l = (if l = 0 \<or> k = 0 then 0
    else if k > 0 \<and> l > 0 \<or> k < 0 \<and> l < 0
      then int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)
      else
        if l dvd k then - int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)
        else - int (Suc (nat \<bar>k\<bar> div nat \<bar>l\<bar>)))"

definition modulo_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "k mod l = (if l = 0 then k else if l dvd k then 0
    else if k > 0 \<and> l > 0 \<or> k < 0 \<and> l < 0
      then sgn l * int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)
      else sgn l * (\<bar>l\<bar> - int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)))"

lemma eucl_rel_int:
  "eucl_rel_int k l (k div l, k mod l)"
proof (cases k rule: int_cases3)
  case zero
  then show ?thesis
    by (simp add: eucl_rel_int_iff divide_int_def modulo_int_def)
next
  case (pos n)
  then show ?thesis
    using div_mult_mod_eq [of n]
    by (cases l rule: int_cases3)
      (auto simp del: of_nat_mult of_nat_add
        simp add: mod_greater_zero_iff_not_dvd of_nat_mult [symmetric] of_nat_add [symmetric] algebra_simps
        eucl_rel_int_iff divide_int_def modulo_int_def int_dvd_iff)
next
  case (neg n)
  then show ?thesis
    using div_mult_mod_eq [of n]
    by (cases l rule: int_cases3)
      (auto simp del: of_nat_mult of_nat_add
        simp add: mod_greater_zero_iff_not_dvd of_nat_mult [symmetric] of_nat_add [symmetric] algebra_simps
        eucl_rel_int_iff divide_int_def modulo_int_def int_dvd_iff)
qed

lemma divmod_int_unique:
  assumes "eucl_rel_int k l (q, r)"
  shows div_int_unique: "k div l = q" and mod_int_unique: "k mod l = r"
  using assms eucl_rel_int [of k l]
  using unique_quotient [of k l] unique_remainder [of k l]
  by auto

instance proof
  fix k l :: int
  show "k div l * l + k mod l = k"
    using eucl_rel_int [of k l]
    unfolding eucl_rel_int_iff by (simp add: ac_simps)
next
  fix k :: int show "k div 0 = 0"
    by (rule div_int_unique, simp add: eucl_rel_int_iff)
next
  fix k l :: int
  assume "l \<noteq> 0"
  then show "k * l div l = k"
    by (auto simp add: eucl_rel_int_iff ac_simps intro: div_int_unique [of _ _ _ 0])
qed (auto simp add: sgn_mult mult_sgn_abs abs_eq_iff')

end

lemma is_unit_int:
  "is_unit (k::int) \<longleftrightarrow> k = 1 \<or> k = - 1"
  by auto

lemma zdiv_int:
  "int (a div b) = int a div int b"
  by (simp add: divide_int_def)

lemma zmod_int:
  "int (a mod b) = int a mod int b"
  by (simp add: modulo_int_def int_dvd_iff)

lemma div_abs_eq_div_nat:
  "\<bar>k\<bar> div \<bar>l\<bar> = int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)"
  by (simp add: divide_int_def)

lemma mod_abs_eq_div_nat:
  "\<bar>k\<bar> mod \<bar>l\<bar> = int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)"
  by (simp add: modulo_int_def dvd_int_unfold_dvd_nat)

lemma div_sgn_abs_cancel:
  fixes k l v :: int
  assumes "v \<noteq> 0"
  shows "(sgn v * \<bar>k\<bar>) div (sgn v * \<bar>l\<bar>) = \<bar>k\<bar> div \<bar>l\<bar>"
proof -
  from assms have "sgn v = - 1 \<or> sgn v = 1"
    by (cases "v \<ge> 0") auto
  then show ?thesis
    using assms unfolding divide_int_def [of "sgn v * \<bar>k\<bar>" "sgn v * \<bar>l\<bar>"]
    by (fastforce simp add: not_less div_abs_eq_div_nat)
qed

lemma div_eq_sgn_abs:
  fixes k l v :: int
  assumes "sgn k = sgn l"
  shows "k div l = \<bar>k\<bar> div \<bar>l\<bar>"
proof (cases "l = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  with assms have "(sgn k * \<bar>k\<bar>) div (sgn l * \<bar>l\<bar>) = \<bar>k\<bar> div \<bar>l\<bar>"
    by (simp add: div_sgn_abs_cancel)
  then show ?thesis
    by (simp add: sgn_mult_abs)
qed

lemma div_dvd_sgn_abs:
  fixes k l :: int
  assumes "l dvd k"
  shows "k div l = (sgn k * sgn l) * (\<bar>k\<bar> div \<bar>l\<bar>)"
proof (cases "k = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof (cases "sgn l = sgn k")
    case True
    then show ?thesis
      by (simp add: div_eq_sgn_abs)
  next
    case False
    with \<open>k \<noteq> 0\<close> assms show ?thesis
      unfolding divide_int_def [of k l]
        by (auto simp add: zdiv_int)
  qed
qed

lemma div_noneq_sgn_abs:
  fixes k l :: int
  assumes "l \<noteq> 0"
  assumes "sgn k \<noteq> sgn l"
  shows "k div l = - (\<bar>k\<bar> div \<bar>l\<bar>) - of_bool (\<not> l dvd k)"
  using assms
  by (simp only: divide_int_def [of k l], auto simp add: not_less zdiv_int)
  
lemma sgn_mod:
  fixes k l :: int
  assumes "l \<noteq> 0" "\<not> l dvd k"
  shows "sgn (k mod l) = sgn l"
proof -
  from \<open>\<not> l dvd k\<close>
  have "k mod l \<noteq> 0"
    by (simp add: dvd_eq_mod_eq_0)
  show ?thesis
    using \<open>l \<noteq> 0\<close> \<open>\<not> l dvd k\<close>
    unfolding modulo_int_def [of k l]
    by (auto simp add: sgn_1_pos sgn_1_neg mod_greater_zero_iff_not_dvd nat_dvd_iff not_less
      zless_nat_eq_int_zless [symmetric] elim: nonpos_int_cases)
qed

lemma abs_mod_less:
  fixes k l :: int
  assumes "l \<noteq> 0"
  shows "\<bar>k mod l\<bar> < \<bar>l\<bar>"
  using assms unfolding modulo_int_def [of k l]
  by (auto simp add: not_less int_dvd_iff mod_greater_zero_iff_not_dvd elim: pos_int_cases neg_int_cases nonneg_int_cases nonpos_int_cases)

instance int :: ring_div
proof
  fix k l s :: int
  assume "l \<noteq> 0"
  then have "eucl_rel_int (k + s * l) l (s + k div l, k mod l)"
    using eucl_rel_int [of k l]
    unfolding eucl_rel_int_iff by (auto simp: algebra_simps)
  then show "(k + s * l) div l = s + k div l"
    by (rule div_int_unique)
next
  fix k l s :: int
  assume "s \<noteq> 0"
  have "\<And>q r. eucl_rel_int k l (q, r)
    \<Longrightarrow> eucl_rel_int (s * k) (s * l) (q, s * r)"
    unfolding eucl_rel_int_iff
    by (rule linorder_cases [of 0 l])
      (use \<open>s \<noteq> 0\<close> in \<open>auto simp: algebra_simps
      mult_less_0_iff zero_less_mult_iff mult_strict_right_mono
      mult_strict_right_mono_neg zero_le_mult_iff mult_le_0_iff\<close>)
  then have "eucl_rel_int (s * k) (s * l) (k div l, s * (k mod l))"
    using eucl_rel_int [of k l] .
  then show "(s * k) div (s * l) = k div l"
    by (rule div_int_unique)
qed

ML \<open>
structure Cancel_Div_Mod_Int = Cancel_Div_Mod
(
  val div_name = @{const_name divide};
  val mod_name = @{const_name modulo};
  val mk_binop = HOLogic.mk_binop;
  val mk_sum = Arith_Data.mk_sum HOLogic.intT;
  val dest_sum = Arith_Data.dest_sum;

  val div_mod_eqs = map mk_meta_eq @{thms cancel_div_mod_rules};

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac (Arith_Data.simp_all_tac
    @{thms diff_conv_add_uminus add_0_left add_0_right ac_simps})
)
\<close>

simproc_setup cancel_div_mod_int ("(k::int) + l") =
  \<open>K Cancel_Div_Mod_Int.proc\<close>


text\<open>Basic laws about division and remainder\<close>

lemma pos_mod_conj: "(0::int) < b \<Longrightarrow> 0 \<le> a mod b \<and> a mod b < b"
  using eucl_rel_int [of a b]
  by (auto simp add: eucl_rel_int_iff prod_eq_iff)

lemmas pos_mod_sign [simp] = pos_mod_conj [THEN conjunct1]
   and pos_mod_bound [simp] = pos_mod_conj [THEN conjunct2]

lemma neg_mod_conj: "b < (0::int) \<Longrightarrow> a mod b \<le> 0 \<and> b < a mod b"
  using eucl_rel_int [of a b]
  by (auto simp add: eucl_rel_int_iff prod_eq_iff)

lemmas neg_mod_sign [simp] = neg_mod_conj [THEN conjunct1]
   and neg_mod_bound [simp] = neg_mod_conj [THEN conjunct2]


subsubsection \<open>General Properties of div and mod\<close>

lemma div_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a div b = 0"
apply (rule div_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

lemma div_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a div b = 0"
apply (rule div_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

lemma div_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a div b = -1"
apply (rule div_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

lemma div_positive_int:
  "k div l > 0" if "k \<ge> l" and "l > 0" for k l :: int
  using that by (simp add: divide_int_def div_positive)

(*There is no div_neg_pos_trivial because  0 div b = 0 would supersede it*)

lemma mod_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a mod b = a"
apply (rule_tac q = 0 in mod_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

lemma mod_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a mod b = a"
apply (rule_tac q = 0 in mod_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

lemma mod_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a mod b = a+b"
apply (rule_tac q = "-1" in mod_int_unique)
apply (auto simp add: eucl_rel_int_iff)
done

text\<open>There is no \<open>mod_neg_pos_trivial\<close>.\<close>


subsubsection \<open>Laws for div and mod with Unary Minus\<close>

lemma zminus1_lemma:
     "eucl_rel_int a b (q, r) ==> b \<noteq> 0
      ==> eucl_rel_int (-a) b (if r=0 then -q else -q - 1,
                          if r=0 then 0 else b-r)"
by (force simp add: eucl_rel_int_iff right_diff_distrib)


lemma zdiv_zminus1_eq_if:
     "b \<noteq> (0::int)
      ==> (-a) div b =
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: eucl_rel_int [THEN zminus1_lemma, THEN div_int_unique])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
apply (case_tac "b = 0", simp)
apply (blast intro: eucl_rel_int [THEN zminus1_lemma, THEN mod_int_unique])
done

lemma zmod_zminus1_not_zero:
  fixes k l :: int
  shows "- k mod l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zmod_zminus2_not_zero:
  fixes k l :: int
  shows "k mod - l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zdiv_zminus2_eq_if:
     "b \<noteq> (0::int)
      ==> a div (-b) =
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (simp add: zdiv_zminus1_eq_if div_minus_right)

lemma zmod_zminus2_eq_if:
     "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
by (simp add: zmod_zminus1_eq_if mod_minus_right)


subsubsection \<open>Monotonicity in the First Argument (Dividend)\<close>

lemma zdiv_mono1: "[| a \<le> a';  0 < (b::int) |] ==> a div b \<le> a' div b"
using mult_div_mod_eq [symmetric, of a b]
using mult_div_mod_eq [symmetric, of a' b]
apply -
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done

lemma zdiv_mono1_neg: "[| a \<le> a';  (b::int) < 0 |] ==> a' div b \<le> a div b"
using mult_div_mod_eq [symmetric, of a b]
using mult_div_mod_eq [symmetric, of a' b]
apply -
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst, simp_all)
done


subsubsection \<open>Monotonicity in the Second Argument (Divisor)\<close>

lemma q_pos_lemma:
     "[| 0 \<le> b'*q' + r'; r' < b';  0 < b' |] ==> 0 \<le> (q'::int)"
apply (subgoal_tac "0 < b'* (q' + 1) ")
 apply (simp add: zero_less_mult_iff)
apply (simp add: distrib_left)
done

lemma zdiv_mono2_lemma:
     "[| b*q + r = b'*q' + r';  0 \<le> b'*q' + r';
         r' < b';  0 \<le> r;  0 < b';  b' \<le> b |]
      ==> q \<le> (q'::int)"
apply (frule q_pos_lemma, assumption+)
apply (subgoal_tac "b*q < b* (q' + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (subgoal_tac "b*q = r' - r + b'*q'")
 prefer 2 apply simp
apply (simp (no_asm_simp) add: distrib_left)
apply (subst add.commute, rule add_less_le_mono, arith)
apply (rule mult_right_mono, auto)
done

lemma zdiv_mono2:
     "[| (0::int) \<le> a;  0 < b';  b' \<le> b |] ==> a div b \<le> a div b'"
apply (subgoal_tac "b \<noteq> 0")
  prefer 2 apply arith
using mult_div_mod_eq [symmetric, of a b]
using mult_div_mod_eq [symmetric, of a b']
apply -
apply (rule zdiv_mono2_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done

lemma q_neg_lemma:
     "[| b'*q' + r' < 0;  0 \<le> r';  0 < b' |] ==> q' \<le> (0::int)"
apply (subgoal_tac "b'*q' < 0")
 apply (simp add: mult_less_0_iff, arith)
done

lemma zdiv_mono2_neg_lemma:
     "[| b*q + r = b'*q' + r';  b'*q' + r' < 0;
         r < b;  0 \<le> r';  0 < b';  b' \<le> b |]
      ==> q' \<le> (q::int)"
apply (frule q_neg_lemma, assumption+)
apply (subgoal_tac "b*q' < b* (q + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (simp add: distrib_left)
apply (subgoal_tac "b*q' \<le> b'*q'")
 prefer 2 apply (simp add: mult_right_mono_neg, arith)
done

lemma zdiv_mono2_neg:
     "[| a < (0::int);  0 < b';  b' \<le> b |] ==> a div b' \<le> a div b"
using mult_div_mod_eq [symmetric, of a b]
using mult_div_mod_eq [symmetric, of a b']
apply -
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done


subsubsection \<open>More Algebraic Laws for div and mod\<close>

text\<open>proving (a*b) div c = a * (b div c) + a * (b mod c)\<close>

lemma zmult1_lemma:
     "[| eucl_rel_int b c (q, r) |]
      ==> eucl_rel_int (a * b) c (a*q + a*r div c, a*r mod c)"
by (auto simp add: split_ifs eucl_rel_int_iff linorder_neq_iff distrib_left ac_simps)

lemma zdiv_zmult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: eucl_rel_int [THEN zmult1_lemma, THEN div_int_unique])
done

text\<open>proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c)\<close>

lemma zadd1_lemma:
     "[| eucl_rel_int a c (aq, ar);  eucl_rel_int b c (bq, br) |]
      ==> eucl_rel_int (a+b) c (aq + bq + (ar+br) div c, (ar+br) mod c)"
by (force simp add: split_ifs eucl_rel_int_iff linorder_neq_iff distrib_left)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq:
     "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (case_tac "c = 0", simp)
apply (blast intro: zadd1_lemma [OF eucl_rel_int eucl_rel_int] div_int_unique)
done

lemma zmod_eq_0_iff: "(m mod d = 0) = (EX q::int. m = d*q)"
by (simp add: dvd_eq_mod_eq_0 [symmetric] dvd_def)

(* REVISIT: should this be generalized to all semiring_div types? *)
lemmas zmod_eq_0D [dest!] = zmod_eq_0_iff [THEN iffD1]


subsubsection \<open>Proving  @{term "a div (b * c) = (a div b) div c"}\<close>

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

text\<open>first, four lemmas to bound the remainder for the cases b<0 and b>0\<close>

lemma zmult2_lemma_aux1: "[| (0::int) < c;  b < r;  r \<le> 0 |] ==> b * c < b * (q mod c) + r"
apply (subgoal_tac "b * (c - q mod c) < r * 1")
 apply (simp add: algebra_simps)
apply (rule order_le_less_trans)
 apply (erule_tac [2] mult_strict_right_mono)
 apply (rule mult_left_mono_neg)
  using add1_zle_eq[of "q mod c"]apply(simp add: algebra_simps)
 apply (simp)
apply (simp)
done

lemma zmult2_lemma_aux2:
     "[| (0::int) < c;   b < r;  r \<le> 0 |] ==> b * (q mod c) + r \<le> 0"
apply (subgoal_tac "b * (q mod c) \<le> 0")
 apply arith
apply (simp add: mult_le_0_iff)
done

lemma zmult2_lemma_aux3: "[| (0::int) < c;  0 \<le> r;  r < b |] ==> 0 \<le> b * (q mod c) + r"
apply (subgoal_tac "0 \<le> b * (q mod c) ")
apply arith
apply (simp add: zero_le_mult_iff)
done

lemma zmult2_lemma_aux4: "[| (0::int) < c; 0 \<le> r; r < b |] ==> b * (q mod c) + r < b * c"
apply (subgoal_tac "r * 1 < b * (c - q mod c) ")
 apply (simp add: right_diff_distrib)
apply (rule order_less_le_trans)
 apply (erule mult_strict_right_mono)
 apply (rule_tac [2] mult_left_mono)
  apply simp
 using add1_zle_eq[of "q mod c"] apply (simp add: algebra_simps)
apply simp
done

lemma zmult2_lemma: "[| eucl_rel_int a b (q, r); 0 < c |]
      ==> eucl_rel_int a (b * c) (q div c, b*(q mod c) + r)"
by (auto simp add: mult.assoc eucl_rel_int_iff linorder_neq_iff
                   zero_less_mult_iff distrib_left [symmetric]
                   zmult2_lemma_aux1 zmult2_lemma_aux2 zmult2_lemma_aux3 zmult2_lemma_aux4 mult_less_0_iff split: if_split_asm)

lemma zdiv_zmult2_eq:
  fixes a b c :: int
  shows "0 \<le> c \<Longrightarrow> a div (b * c) = (a div b) div c"
apply (case_tac "b = 0", simp)
apply (force simp add: le_less eucl_rel_int [THEN zmult2_lemma, THEN div_int_unique])
done

lemma zmod_zmult2_eq:
  fixes a b c :: int
  shows "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
apply (case_tac "b = 0", simp)
apply (force simp add: le_less eucl_rel_int [THEN zmult2_lemma, THEN mod_int_unique])
done

lemma div_pos_geq:
  fixes k l :: int
  assumes "0 < l" and "l \<le> k"
  shows "k div l = (k - l) div l + 1"
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with assms show ?thesis by (simp add: div_add_self2)
qed

lemma mod_pos_geq:
  fixes k l :: int
  assumes "0 < l" and "l \<le> k"
  shows "k mod l = (k - l) mod l"
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with assms show ?thesis by simp
qed


subsubsection \<open>Splitting Rules for div and mod\<close>

text\<open>The proofs of the two lemmas below are essentially identical\<close>

lemma split_pos_lemma:
 "0<k ==>
    P(n div k :: int)(n mod k) = (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P x y" for x y in rev_mp)
 apply (subst mod_add_eq [symmetric])
 apply (subst zdiv_zadd1_eq)
 apply (simp add: div_pos_pos_trivial mod_pos_pos_trivial)
txt\<open>converse direction\<close>
apply (drule_tac x = "n div k" in spec)
apply (drule_tac x = "n mod k" in spec, simp)
done

lemma split_neg_lemma:
 "k<0 ==>
    P(n div k :: int)(n mod k) = (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P x y" for x y in rev_mp)
 apply (subst mod_add_eq [symmetric])
 apply (subst zdiv_zadd1_eq)
 apply (simp add: div_neg_neg_trivial mod_neg_neg_trivial)
txt\<open>converse direction\<close>
apply (drule_tac x = "n div k" in spec)
apply (drule_tac x = "n mod k" in spec, simp)
done

lemma split_zdiv:
 "P(n div k :: int) =
  ((k = 0 --> P 0) &
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i)) &
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i)))"
apply (case_tac "k=0", simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE)
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P x"]
                      split_neg_lemma [of concl: "%x y. P x"])
done

lemma split_zmod:
 "P(n mod k :: int) =
  ((k = 0 --> P n) &
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P j)) &
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P j)))"
apply (case_tac "k=0", simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE)
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P y"]
                      split_neg_lemma [of concl: "%x y. P y"])
done

text \<open>Enable (lin)arith to deal with @{const divide} and @{const modulo}
  when these are applied to some constant that is of the form
  @{term "numeral k"}:\<close>
declare split_zdiv [of _ _ "numeral k", arith_split] for k
declare split_zmod [of _ _ "numeral k", arith_split] for k


subsubsection \<open>Computing \<open>div\<close> and \<open>mod\<close> with shifting\<close>

lemma pos_eucl_rel_int_mult_2:
  assumes "0 \<le> b"
  assumes "eucl_rel_int a b (q, r)"
  shows "eucl_rel_int (1 + 2*a) (2*b) (q, 1 + 2*r)"
  using assms unfolding eucl_rel_int_iff by auto

lemma neg_eucl_rel_int_mult_2:
  assumes "b \<le> 0"
  assumes "eucl_rel_int (a + 1) b (q, r)"
  shows "eucl_rel_int (1 + 2*a) (2*b) (q, 2*r - 1)"
  using assms unfolding eucl_rel_int_iff by auto

text\<open>computing div by shifting\<close>

lemma pos_zdiv_mult_2: "(0::int) \<le> a ==> (1 + 2*b) div (2*a) = b div a"
  using pos_eucl_rel_int_mult_2 [OF _ eucl_rel_int]
  by (rule div_int_unique)

lemma neg_zdiv_mult_2:
  assumes A: "a \<le> (0::int)" shows "(1 + 2*b) div (2*a) = (b+1) div a"
  using neg_eucl_rel_int_mult_2 [OF A eucl_rel_int]
  by (rule div_int_unique)

(* FIXME: add rules for negative numerals *)
lemma zdiv_numeral_Bit0 [simp]:
  "numeral (Num.Bit0 v) div numeral (Num.Bit0 w) =
    numeral v div (numeral w :: int)"
  unfolding numeral.simps unfolding mult_2 [symmetric]
  by (rule div_mult_mult1, simp)

lemma zdiv_numeral_Bit1 [simp]:
  "numeral (Num.Bit1 v) div numeral (Num.Bit0 w) =
    (numeral v div (numeral w :: int))"
  unfolding numeral.simps
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zdiv_mult_2, simp)

lemma pos_zmod_mult_2:
  fixes a b :: int
  assumes "0 \<le> a"
  shows "(1 + 2 * b) mod (2 * a) = 1 + 2 * (b mod a)"
  using pos_eucl_rel_int_mult_2 [OF assms eucl_rel_int]
  by (rule mod_int_unique)

lemma neg_zmod_mult_2:
  fixes a b :: int
  assumes "a \<le> 0"
  shows "(1 + 2 * b) mod (2 * a) = 2 * ((b + 1) mod a) - 1"
  using neg_eucl_rel_int_mult_2 [OF assms eucl_rel_int]
  by (rule mod_int_unique)

(* FIXME: add rules for negative numerals *)
lemma zmod_numeral_Bit0 [simp]:
  "numeral (Num.Bit0 v) mod numeral (Num.Bit0 w) =
    (2::int) * (numeral v mod numeral w)"
  unfolding numeral_Bit0 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] by (rule mod_mult_mult1)

lemma zmod_numeral_Bit1 [simp]:
  "numeral (Num.Bit1 v) mod numeral (Num.Bit0 w) =
    2 * (numeral v mod numeral w) + (1::int)"
  unfolding numeral_Bit1 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zmod_mult_2, simp)

lemma zdiv_eq_0_iff:
 "(i::int) div k = 0 \<longleftrightarrow> k=0 \<or> 0\<le>i \<and> i<k \<or> i\<le>0 \<and> k<i" (is "?L = ?R")
proof
  assume ?L
  have "?L \<longrightarrow> ?R" by (rule split_zdiv[THEN iffD2]) simp
  with \<open>?L\<close> show ?R by blast
next
  assume ?R thus ?L
    by(auto simp: div_pos_pos_trivial div_neg_neg_trivial)
qed

lemma zmod_trival_iff:
  fixes i k :: int
  shows "i mod k = i \<longleftrightarrow> k = 0 \<or> 0 \<le> i \<and> i < k \<or> i \<le> 0 \<and> k < i"
proof -
  have "i mod k = i \<longleftrightarrow> i div k = 0"
    by safe (insert div_mult_mod_eq [of i k], auto)
  with zdiv_eq_0_iff
  show ?thesis
    by simp
qed

instantiation int :: unique_euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

definition [simp]:
  "uniqueness_constraint_int (k :: int) l \<longleftrightarrow> unit_factor k = unit_factor l"
  
instance
  by standard
    (use mult_le_mono2 [of 1] in \<open>auto simp add: abs_mult nat_mult_distrib sgn_mod zdiv_eq_0_iff sgn_1_pos sgn_mult split: abs_split\<close>)

end

  
subsubsection \<open>Quotients of Signs\<close>

lemma div_eq_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: divide_int_def)

lemma zmod_minus1: "(0::int) < b ==> -1 mod b = b - 1"
by (simp add: modulo_int_def)

lemma div_neg_pos_less0: "[| a < (0::int);  0 < b |] ==> a div b < 0"
apply (subgoal_tac "a div b \<le> -1", force)
apply (rule order_trans)
apply (rule_tac a' = "-1" in zdiv_mono1)
apply (auto simp add: div_eq_minus1)
done

lemma div_nonneg_neg_le0: "[| (0::int) \<le> a; b < 0 |] ==> a div b \<le> 0"
by (drule zdiv_mono1_neg, auto)

lemma div_nonpos_pos_le0: "[| (a::int) \<le> 0; b > 0 |] ==> a div b \<le> 0"
by (drule zdiv_mono1, auto)

text\<open>Now for some equivalences of the form \<open>a div b >=< 0 \<longleftrightarrow> \<dots>\<close>
conditional upon the sign of \<open>a\<close> or \<open>b\<close>. There are many more.
They should all be simp rules unless that causes too much search.\<close>

lemma pos_imp_zdiv_nonneg_iff: "(0::int) < b ==> (0 \<le> a div b) = (0 \<le> a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: linorder_neq_iff)
apply (simp (no_asm_use) add: linorder_not_less [symmetric])
apply (blast intro: div_neg_pos_less0)
done

lemma pos_imp_zdiv_pos_iff:
  "0<k \<Longrightarrow> 0 < (i::int) div k \<longleftrightarrow> k \<le> i"
using pos_imp_zdiv_nonneg_iff[of k i] zdiv_eq_0_iff[of i k]
by arith

lemma neg_imp_zdiv_nonneg_iff:
  "b < (0::int) ==> (0 \<le> a div b) = (a \<le> (0::int))"
apply (subst div_minus_minus [symmetric])
apply (subst pos_imp_zdiv_nonneg_iff, auto)
done

(*But not (a div b \<le> 0 iff a\<le>0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

(*Again the law fails for \<le>: consider a = -1, b = -2 when a div b = 0*)
lemma neg_imp_zdiv_neg_iff: "b < (0::int) ==> (a div b < 0) = (0 < a)"
by (simp add: linorder_not_le [symmetric] neg_imp_zdiv_nonneg_iff)

lemma nonneg1_imp_zdiv_pos_iff:
  "(0::int) <= a \<Longrightarrow> (a div b > 0) = (a >= b & b>0)"
apply rule
 apply rule
  using div_pos_pos_trivial[of a b]apply arith
 apply(cases "b=0")apply simp
 using div_nonneg_neg_le0[of a b]apply arith
using int_one_le_iff_zero_less[of "a div b"] zdiv_mono1[of b a b]apply simp
done

lemma zmod_le_nonneg_dividend: "(m::int) \<ge> 0 ==> m mod k \<le> m"
apply (rule split_zmod[THEN iffD2])
apply(fastforce dest: q_pos_lemma intro: split_mult_pos_le)
done


subsubsection \<open>Computation of Division and Remainder\<close>

instantiation int :: semiring_numeral_div
begin

definition divmod_int :: "num \<Rightarrow> num \<Rightarrow> int \<times> int"
where
  "divmod_int m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_int :: "num \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int"
where
  "divmod_step_int l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

instance
  by standard (auto intro: zmod_le_nonneg_dividend simp add: divmod_int_def divmod_step_int_def
    pos_imp_zdiv_pos_iff div_pos_pos_trivial mod_pos_pos_trivial zmod_zmult2_eq zdiv_zmult2_eq)

end

declare divmod_algorithm_code [where ?'a = int, code]

context
begin
  
qualified definition adjust_div :: "int \<times> int \<Rightarrow> int"
where
  "adjust_div qr = (let (q, r) = qr in q + of_bool (r \<noteq> 0))"

qualified lemma adjust_div_eq [simp, code]:
  "adjust_div (q, r) = q + of_bool (r \<noteq> 0)"
  by (simp add: adjust_div_def)

qualified definition adjust_mod :: "int \<Rightarrow> int \<Rightarrow> int"
where
  [simp]: "adjust_mod l r = (if r = 0 then 0 else l - r)"

lemma minus_numeral_div_numeral [simp]:
  "- numeral m div numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed

lemma minus_numeral_mod_numeral [simp]:
  "- numeral m mod numeral n = adjust_mod (numeral n) (snd (divmod m n) :: int)"
proof -
  have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    using that by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def modulo_int_def)
qed

lemma numeral_div_minus_numeral [simp]:
  "numeral m div - numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed
  
lemma numeral_mod_minus_numeral [simp]:
  "numeral m mod - numeral n = - adjust_mod (numeral n) (snd (divmod m n) :: int)"
proof -
  have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    using that by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def modulo_int_def)
qed

lemma minus_one_div_numeral [simp]:
  "- 1 div numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using minus_numeral_div_numeral [of Num.One n] by simp  

lemma minus_one_mod_numeral [simp]:
  "- 1 mod numeral n = adjust_mod (numeral n) (snd (divmod Num.One n) :: int)"
  using minus_numeral_mod_numeral [of Num.One n] by simp

lemma one_div_minus_numeral [simp]:
  "1 div - numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using numeral_div_minus_numeral [of Num.One n] by simp
  
lemma one_mod_minus_numeral [simp]:
  "1 mod - numeral n = - adjust_mod (numeral n) (snd (divmod Num.One n) :: int)"
  using numeral_mod_minus_numeral [of Num.One n] by simp

end


subsubsection \<open>Further properties\<close>

text \<open>Simplify expresions in which div and mod combine numerical constants\<close>

lemma int_div_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r]) (simp add: eucl_rel_int_iff)

lemma int_div_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

lemma int_mod_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

lemma int_mod_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

lemma abs_div: "(y::int) dvd x \<Longrightarrow> \<bar>x div y\<bar> = \<bar>x\<bar> div \<bar>y\<bar>"
by (unfold dvd_def, cases "y=0", auto simp add: abs_mult)

text\<open>Suggested by Matthias Daum\<close>
lemma int_power_div_base:
     "\<lbrakk>0 < m; 0 < k\<rbrakk> \<Longrightarrow> k ^ m div k = (k::int) ^ (m - Suc 0)"
apply (subgoal_tac "k ^ m = k ^ ((m - Suc 0) + Suc 0)")
 apply (erule ssubst)
 apply (simp only: power_add)
 apply simp_all
done

text \<open>Distributive laws for function \<open>nat\<close>.\<close>

lemma nat_div_distrib: "0 \<le> x \<Longrightarrow> nat (x div y) = nat x div nat y"
apply (rule linorder_cases [of y 0])
apply (simp add: div_nonneg_neg_le0)
apply simp
apply (simp add: nat_eq_iff pos_imp_zdiv_nonneg_iff zdiv_int)
done

(*Fails if y<0: the LHS collapses to (nat z) but the RHS doesn't*)
lemma nat_mod_distrib:
  "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> nat (x mod y) = nat x mod nat y"
apply (case_tac "y = 0", simp)
apply (simp add: nat_eq_iff zmod_int)
done

text  \<open>transfer setup\<close>

lemma transfer_nat_int_functions:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) div (nat y) = nat (x div y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) mod (nat y) = nat (x mod y)"
  by (auto simp add: nat_div_distrib nat_mod_distrib)

lemma transfer_nat_int_function_closures:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x div y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x mod y >= 0"
  apply (cases "y = 0")
  apply (auto simp add: pos_imp_zdiv_nonneg_iff)
  apply (cases "y = 0")
  apply auto
done

declare transfer_morphism_nat_int [transfer add return:
  transfer_nat_int_functions
  transfer_nat_int_function_closures
]

lemma transfer_int_nat_functions:
    "(int x) div (int y) = int (x div y)"
    "(int x) mod (int y) = int (x mod y)"
  by (auto simp add: zdiv_int zmod_int)

lemma transfer_int_nat_function_closures:
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x div y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x mod y)"
  by (simp_all only: is_nat_def transfer_nat_int_function_closures)

declare transfer_morphism_int_nat [transfer add return:
  transfer_int_nat_functions
  transfer_int_nat_function_closures
]

text\<open>Suggested by Matthias Daum\<close>
lemma int_div_less_self: "\<lbrakk>0 < x; 1 < k\<rbrakk> \<Longrightarrow> x div k < (x::int)"
apply (subgoal_tac "nat x div nat k < nat x")
 apply (simp add: nat_div_distrib [symmetric])
apply (rule Divides.div_less_dividend, simp_all)
done

lemma (in ring_div) mod_eq_dvd_iff:
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

lemma nat_mod_eq_lemma: assumes xyn: "(x::nat) mod n = y mod n" and xy:"y \<le> x"
  shows "\<exists>q. x = y + n * q"
proof-
  from xy have th: "int x - int y = int (x - y)" by simp
  from xyn have "int x mod int n = int y mod int n"
    by (simp add: zmod_int [symmetric])
  hence "int n dvd int x - int y" by (simp only: mod_eq_dvd_iff [symmetric])
  hence "n dvd x - y" by (simp add: th zdvd_int)
  then show ?thesis using xy unfolding dvd_def apply clarsimp apply (rule_tac x="k" in exI) by arith
qed

lemma nat_mod_eq_iff: "(x::nat) mod n = y mod n \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)"
  (is "?lhs = ?rhs")
proof
  assume H: "x mod n = y mod n"
  {assume xy: "x \<le> y"
    from H have th: "y mod n = x mod n" by simp
    from nat_mod_eq_lemma[OF th xy] have ?rhs
      apply clarify  apply (rule_tac x="q" in exI) by (rule exI[where x="0"], simp)}
  moreover
  {assume xy: "y \<le> x"
    from nat_mod_eq_lemma[OF H xy] have ?rhs
      apply clarify  apply (rule_tac x="0" in exI) by (rule_tac x="q" in exI, simp)}
  ultimately  show ?rhs using linear[of x y] by blast
next
  assume ?rhs then obtain q1 q2 where q12: "x + n * q1 = y + n * q2" by blast
  hence "(x + n * q1) mod n = (y + n * q2) mod n" by simp
  thus  ?lhs by simp
qed

subsubsection \<open>Dedicated simproc for calculation\<close>

text \<open>
  There is space for improvement here: the calculation itself
  could be carried outside the logic, and a generic simproc
  (simplifier setup) for generic calculation would be helpful. 
\<close>

simproc_setup numeral_divmod
  ("0 div 0 :: 'a :: semiring_numeral_div" | "0 mod 0 :: 'a :: semiring_numeral_div" |
   "0 div 1 :: 'a :: semiring_numeral_div" | "0 mod 1 :: 'a :: semiring_numeral_div" |
   "0 div - 1 :: int" | "0 mod - 1 :: int" |
   "0 div numeral b :: 'a :: semiring_numeral_div" | "0 mod numeral b :: 'a :: semiring_numeral_div" |
   "0 div - numeral b :: int" | "0 mod - numeral b :: int" |
   "1 div 0 :: 'a :: semiring_numeral_div" | "1 mod 0 :: 'a :: semiring_numeral_div" |
   "1 div 1 :: 'a :: semiring_numeral_div" | "1 mod 1 :: 'a :: semiring_numeral_div" |
   "1 div - 1 :: int" | "1 mod - 1 :: int" |
   "1 div numeral b :: 'a :: semiring_numeral_div" | "1 mod numeral b :: 'a :: semiring_numeral_div" |
   "1 div - numeral b :: int" |"1 mod - numeral b :: int" |
   "- 1 div 0 :: int" | "- 1 mod 0 :: int" | "- 1 div 1 :: int" | "- 1 mod 1 :: int" |
   "- 1 div - 1 :: int" | "- 1 mod - 1 :: int" | "- 1 div numeral b :: int" | "- 1 mod numeral b :: int" |
   "- 1 div - numeral b :: int" | "- 1 mod - numeral b :: int" |
   "numeral a div 0 :: 'a :: semiring_numeral_div" | "numeral a mod 0 :: 'a :: semiring_numeral_div" |
   "numeral a div 1 :: 'a :: semiring_numeral_div" | "numeral a mod 1 :: 'a :: semiring_numeral_div" |
   "numeral a div - 1 :: int" | "numeral a mod - 1 :: int" |
   "numeral a div numeral b :: 'a :: semiring_numeral_div" | "numeral a mod numeral b :: 'a :: semiring_numeral_div" |
   "numeral a div - numeral b :: int" | "numeral a mod - numeral b :: int" |
   "- numeral a div 0 :: int" | "- numeral a mod 0 :: int" |
   "- numeral a div 1 :: int" | "- numeral a mod 1 :: int" |
   "- numeral a div - 1 :: int" | "- numeral a mod - 1 :: int" |
   "- numeral a div numeral b :: int" | "- numeral a mod numeral b :: int" |
   "- numeral a div - numeral b :: int" | "- numeral a mod - numeral b :: int") =
\<open> let
    val if_cong = the (Code.get_case_cong @{theory} @{const_name If});
    fun successful_rewrite ctxt ct =
      let
        val thm = Simplifier.rewrite ctxt ct
      in if Thm.is_reflexive thm then NONE else SOME thm end;
  in fn phi =>
    let
      val simps = Morphism.fact phi (@{thms div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
        one_div_numeral one_mod_numeral minus_one_div_numeral minus_one_mod_numeral
        one_div_minus_numeral one_mod_minus_numeral
        numeral_div_numeral numeral_mod_numeral minus_numeral_div_numeral minus_numeral_mod_numeral
        numeral_div_minus_numeral numeral_mod_minus_numeral
        div_minus_minus mod_minus_minus Divides.adjust_div_eq of_bool_eq one_neq_zero
        numeral_neq_zero neg_equal_0_iff_equal arith_simps arith_special divmod_trivial
        divmod_cancel divmod_steps divmod_step_eq fst_conv snd_conv numeral_One
        case_prod_beta rel_simps Divides.adjust_mod_def div_minus1_right mod_minus1_right
        minus_minus numeral_times_numeral mult_zero_right mult_1_right}
        @ [@{lemma "0 = 0 \<longleftrightarrow> True" by simp}]);
      fun prepare_simpset ctxt = HOL_ss |> Simplifier.simpset_map ctxt
        (Simplifier.add_cong if_cong #> fold Simplifier.add_simp simps)
    in fn ctxt => successful_rewrite (Simplifier.put_simpset (prepare_simpset ctxt) ctxt) end
  end;
\<close>


subsubsection \<open>Code generation\<close>

lemma [code]:
  fixes k :: int
  shows 
    "k div 0 = 0"
    "k mod 0 = k"
    "0 div k = 0"
    "0 mod k = 0"
    "k div Int.Pos Num.One = k"
    "k mod Int.Pos Num.One = 0"
    "k div Int.Neg Num.One = - k"
    "k mod Int.Neg Num.One = 0"
    "Int.Pos m div Int.Pos n = (fst (divmod m n) :: int)"
    "Int.Pos m mod Int.Pos n = (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Pos n = - (Divides.adjust_div (divmod m n) :: int)"
    "Int.Neg m mod Int.Pos n = Divides.adjust_mod (Int.Pos n) (snd (divmod m n) :: int)"
    "Int.Pos m div Int.Neg n = - (Divides.adjust_div (divmod m n) :: int)"
    "Int.Pos m mod Int.Neg n = - Divides.adjust_mod (Int.Pos n) (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Neg n = (fst (divmod m n) :: int)"
    "Int.Neg m mod Int.Neg n = - (snd (divmod m n) :: int)"
  by simp_all

code_identifier
  code_module Divides \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

lemma dvd_eq_mod_eq_0_numeral:
  "numeral x dvd (numeral y :: 'a) \<longleftrightarrow> numeral y mod numeral x = (0 :: 'a::semiring_div)"
  by (fact dvd_eq_mod_eq_0)

declare minus_div_mult_eq_mod [symmetric, nitpick_unfold]

end

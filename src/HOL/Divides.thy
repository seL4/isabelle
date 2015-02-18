(*  Title:      HOL/Divides.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

section {* The division operators div and mod *}

theory Divides
imports Parity
begin

subsection {* Syntactic division operations *}

class div = dvd +
  fixes div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "div" 70)
    and mod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "mod" 70)


subsection {* Abstract division in commutative semirings. *}

class semiring_div = comm_semiring_1_cancel + no_zero_divisors + div +
  assumes mod_div_equality: "a div b * b + a mod b = a"
    and div_by_0 [simp]: "a div 0 = 0"
    and div_0 [simp]: "0 div a = 0"
    and div_mult_self1 [simp]: "b \<noteq> 0 \<Longrightarrow> (a + c * b) div b = c + a div b"
    and div_mult_mult1 [simp]: "c \<noteq> 0 \<Longrightarrow> (c * a) div (c * b) = a div b"
begin

subclass semiring_no_zero_divisors ..

lemma power_not_zero: -- \<open>FIXME cf. @{text field_power_not_zero}\<close>
  "a \<noteq> 0 \<Longrightarrow> a ^ n \<noteq> 0"
  by (induct n) (simp_all add: no_zero_divisors)

lemma semiring_div_power_eq_0_iff: -- \<open>FIXME cf. @{text power_eq_0_iff}, @{text power_eq_0_nat_iff}\<close>
  "n \<noteq> 0 \<Longrightarrow> a ^ n = 0 \<longleftrightarrow> a = 0"
  using power_not_zero [of a n] by (auto simp add: zero_power)

text {* @{const div} and @{const mod} *}

lemma mod_div_equality2: "b * (a div b) + a mod b = a"
  unfolding mult.commute [of b]
  by (rule mod_div_equality)

lemma mod_div_equality': "a mod b + a div b * b = a"
  using mod_div_equality [of a b]
  by (simp only: ac_simps)

lemma div_mod_equality: "((a div b) * b + a mod b) + c = a + c"
  by (simp add: mod_div_equality)

lemma div_mod_equality2: "(b * (a div b) + a mod b) + c = a + c"
  by (simp add: mod_div_equality2)

lemma mod_by_0 [simp]: "a mod 0 = a"
  using mod_div_equality [of a zero] by simp

lemma mod_0 [simp]: "0 mod a = 0"
  using mod_div_equality [of zero a] div_0 by simp

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
    by (simp add: mod_div_equality)
  also from False div_mult_self1 [of b a c] have
    "\<dots> = (c + a div b) * b + (a + c * b) mod b"
      by (simp add: algebra_simps)
  finally have "a = a div b * b + (a + c * b) mod b"
    by (simp add: add.commute [of a] add.assoc distrib_right)
  then have "a div b * b + (a + c * b) mod b = a div b * b + a mod b"
    by (simp add: mod_div_equality)
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

lemma div_mult_self1_is_id [simp]: "b \<noteq> 0 \<Longrightarrow> b * a div b = a"
  using div_mult_self2 [of b 0 a] by simp

lemma div_mult_self2_is_id [simp]: "b \<noteq> 0 \<Longrightarrow> a * b div b = a"
  using div_mult_self1 [of b 0 a] by simp

lemma mod_mult_self1_is_0 [simp]: "b * a mod b = 0"
  using mod_mult_self2 [of 0 b a] by simp

lemma mod_mult_self2_is_0 [simp]: "a * b mod b = 0"
  using mod_mult_self1 [of 0 a b] by simp

lemma div_by_1 [simp]: "a div 1 = a"
  using div_mult_self2_is_id [of 1 a] zero_neq_one by simp

lemma mod_by_1 [simp]: "a mod 1 = 0"
proof -
  from mod_div_equality [of a one] div_by_1 have "a + a mod 1 = a" by simp
  then have "a + a mod 1 = a + 0" by simp
  then show ?thesis by (rule add_left_imp_eq)
qed

lemma mod_self [simp]: "a mod a = 0"
  using mod_mult_self2_is_0 [of 1] by simp

lemma div_self [simp]: "a \<noteq> 0 \<Longrightarrow> a div a = 1"
  using div_mult_self2_is_id [of _ 1] by simp

lemma div_add_self1 [simp]:
  assumes "b \<noteq> 0"
  shows "(b + a) div b = a div b + 1"
  using assms div_mult_self1 [of b a 1] by (simp add: add.commute)

lemma div_add_self2 [simp]:
  assumes "b \<noteq> 0"
  shows "(a + b) div b = a div b + 1"
  using assms div_add_self1 [of b a] by (simp add: add.commute)

lemma mod_add_self1 [simp]:
  "(b + a) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by (simp add: add.commute)

lemma mod_add_self2 [simp]:
  "(a + b) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by simp

lemma mod_div_decomp:
  fixes a b
  obtains q r where "q = a div b" and "r = a mod b"
    and "a = q * b + r"
proof -
  from mod_div_equality have "a = a div b * b + a mod b" by simp
  moreover have "a div b = a div b" ..
  moreover have "a mod b = a mod b" ..
  note that ultimately show thesis by blast
qed

lemma dvd_imp_mod_0 [simp]:
  assumes "a dvd b"
  shows "b mod a = 0"
proof -
  from assms obtain c where "b = a * c" ..
  then have "b mod a = a * c mod a" by simp
  then show "b mod a = 0" by simp
qed

lemma mod_eq_0_iff_dvd:
  "a mod b = 0 \<longleftrightarrow> b dvd a"
proof
  assume "b dvd a"
  then show "a mod b = 0" by simp
next
  assume "a mod b = 0"
  with mod_div_equality [of a b] have "a div b * b = a" by simp
  then have "a = b * (a div b)" by (simp add: ac_simps)
  then show "b dvd a" ..
qed

lemma dvd_eq_mod_eq_0 [code]:
  "a dvd b \<longleftrightarrow> b mod a = 0"
  by (simp add: mod_eq_0_iff_dvd)

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
    by (simp only: mod_div_equality')
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
    by (simp only: mod_div_equality')
  finally show ?thesis .
qed

lemma dvd_div_mult_self [simp]:
  "a dvd b \<Longrightarrow> (b div a) * a = b"
  using mod_div_equality [of b a, symmetric] by simp

lemma dvd_mult_div_cancel [simp]:
  "a dvd b \<Longrightarrow> a * (b div a) = b"
  using dvd_div_mult_self by (simp add: ac_simps)

lemma dvd_div_mult:
  "a dvd b \<Longrightarrow> (b div a) * c = (b * c) div a"
  by (cases "a = 0") (auto elim!: dvdE simp add: mult.assoc)

lemma div_dvd_div [simp]:
  assumes "a dvd b" and "a dvd c"
  shows "b div a dvd c div a \<longleftrightarrow> b dvd c"
using assms apply (cases "a = 0")
apply auto
apply (unfold dvd_def)
apply auto
 apply(blast intro:mult.assoc[symmetric])
apply(fastforce simp add: mult.assoc)
done

lemma dvd_mod_imp_dvd:
  assumes "k dvd m mod n" and "k dvd n"
  shows "k dvd m"
proof -
  from assms have "k dvd (m div n) * n + m mod n"
    by (simp only: dvd_add dvd_mult)
  then show ?thesis by (simp add: mod_div_equality)
qed

text {* Addition respects modular equivalence. *}

lemma mod_add_left_eq: "(a + b) mod c = (a mod c + b) mod c"
proof -
  have "(a + b) mod c = (a div c * c + a mod c + b) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a mod c + b + a div c * c) mod c"
    by (simp only: ac_simps)
  also have "\<dots> = (a mod c + b) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_add_right_eq: "(a + b) mod c = (a + b mod c) mod c"
proof -
  have "(a + b) mod c = (a + (b div c * c + b mod c)) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a + b mod c + b div c * c) mod c"
    by (simp only: ac_simps)
  also have "\<dots> = (a + b mod c) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_add_eq: "(a + b) mod c = (a mod c + b mod c) mod c"
by (rule trans [OF mod_add_left_eq mod_add_right_eq])

lemma mod_add_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a + b) mod c = (a' + b') mod c"
proof -
  have "(a mod c + b mod c) mod c = (a' mod c + b' mod c) mod c"
    unfolding assms ..
  thus ?thesis
    by (simp only: mod_add_eq [symmetric])
qed

lemma div_add [simp]: "z dvd x \<Longrightarrow> z dvd y
  \<Longrightarrow> (x + y) div z = x div z + y div z"
by (cases "z = 0", simp, unfold dvd_def, auto simp add: algebra_simps)

text {* Multiplication respects modular equivalence. *}

lemma mod_mult_left_eq: "(a * b) mod c = ((a mod c) * b) mod c"
proof -
  have "(a * b) mod c = ((a div c * c + a mod c) * b) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a mod c * b + a div c * b * c) mod c"
    by (simp only: algebra_simps)
  also have "\<dots> = (a mod c * b) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_mult_right_eq: "(a * b) mod c = (a * (b mod c)) mod c"
proof -
  have "(a * b) mod c = (a * (b div c * c + b mod c)) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a * (b mod c) + a * (b div c) * c) mod c"
    by (simp only: algebra_simps)
  also have "\<dots> = (a * (b mod c)) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_mult_eq: "(a * b) mod c = ((a mod c) * (b mod c)) mod c"
by (rule trans [OF mod_mult_left_eq mod_mult_right_eq])

lemma mod_mult_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a * b) mod c = (a' * b') mod c"
proof -
  have "(a mod c * (b mod c)) mod c = (a' mod c * (b' mod c)) mod c"
    unfolding assms ..
  thus ?thesis
    by (simp only: mod_mult_eq [symmetric])
qed

text {* Exponentiation respects modular equivalence. *}

lemma power_mod: "(a mod b)^n mod b = a^n mod b"
apply (induct n, simp_all)
apply (rule mod_mult_right_eq [THEN trans])
apply (simp (no_asm_simp))
apply (rule mod_mult_eq [symmetric])
done

lemma mod_mod_cancel:
  assumes "c dvd b"
  shows "a mod b mod c = a mod c"
proof -
  from `c dvd b` obtain k where "b = c * k"
    by (rule dvdE)
  have "a mod b mod c = a mod (c * k) mod c"
    by (simp only: `b = c * k`)
  also have "\<dots> = (a mod (c * k) + a div (c * k) * k * c) mod c"
    by (simp only: mod_mult_self1)
  also have "\<dots> = (a div (c * k) * (c * k) + a mod (c * k)) mod c"
    by (simp only: ac_simps)
  also have "\<dots> = a mod c"
    by (simp only: mod_div_equality)
  finally show ?thesis .
qed

lemma div_mult_div_if_dvd:
  "y dvd x \<Longrightarrow> z dvd w \<Longrightarrow> (x div y) * (w div z) = (x * w) div (y * z)"
  apply (cases "y = 0", simp)
  apply (cases "z = 0", simp)
  apply (auto elim!: dvdE simp add: algebra_simps)
  apply (subst mult.assoc [symmetric])
  apply (simp add: no_zero_divisors)
  done

lemma div_mult_swap:
  assumes "c dvd b"
  shows "a * (b div c) = (a * b) div c"
proof -
  from assms have "b div c * (a div 1) = b * a div (c * 1)"
    by (simp only: div_mult_div_if_dvd one_dvd)
  then show ?thesis by (simp add: mult.commute)
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
  from mod_div_equality
  have "((c * a) div (c * b)) * (c * b) + (c * a) mod (c * b) = c * a" .
  with False have "c * ((a div b) * b + a mod b) + (c * a) mod (c * b)
    = c * a + c * (a mod b)" by (simp add: algebra_simps)
  with mod_div_equality show ?thesis by simp 
qed
  
lemma mod_mult_mult2:
  "(a * c) mod (b * c) = (a mod b) * c"
  using mod_mult_mult1 [of c a b] by (simp add: mult.commute)

lemma mult_mod_left: "(a mod b) * c = (a * c) mod (b * c)"
  by (fact mod_mult_mult2 [symmetric])

lemma mult_mod_right: "c * (a mod b) = (c * a) mod (c * b)"
  by (fact mod_mult_mult1 [symmetric])

lemma dvd_times_left_cancel_iff [simp]: -- \<open>FIXME generalize\<close>
  assumes "c \<noteq> 0"
  shows "c * a dvd c * b \<longleftrightarrow> a dvd b"
proof -
  have "(c * b) mod (c * a) = 0 \<longleftrightarrow> b mod a = 0" (is "?P \<longleftrightarrow> ?Q")
    using assms by (simp add: mod_mult_mult1)
  then show ?thesis by (simp add: mod_eq_0_iff_dvd)
qed

lemma dvd_times_right_cancel_iff [simp]: -- \<open>FIXME generalize\<close>
  assumes "c \<noteq> 0"
  shows "a * c dvd b * c \<longleftrightarrow> a dvd b"
  using assms dvd_times_left_cancel_iff [of c a b] by (simp add: ac_simps)

lemma dvd_mod: "k dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd (m mod n)"
  unfolding dvd_def by (auto simp add: mod_mult_mult1)

lemma dvd_mod_iff: "k dvd n \<Longrightarrow> k dvd (m mod n) \<longleftrightarrow> k dvd m"
by (blast intro: dvd_mod_imp_dvd dvd_mod)

lemma div_power:
  "y dvd x \<Longrightarrow> (x div y) ^ n = x ^ n div y ^ n"
apply (induct n)
 apply simp
apply(simp add: div_mult_div_if_dvd dvd_power_same)
done

lemma dvd_div_eq_mult:
  assumes "a \<noteq> 0" and "a dvd b"  
  shows "b div a = c \<longleftrightarrow> b = c * a"
proof
  assume "b = c * a"
  then show "b div a = c" by (simp add: assms)
next
  assume "b div a = c"
  then have "b div a * a = c * a" by simp
  moreover from `a dvd b` have "b div a * a = b" by (simp add: dvd_div_mult_self)
  ultimately show "b = c * a" by simp
qed
   
lemma dvd_div_div_eq_mult:
  assumes "a \<noteq> 0" "c \<noteq> 0" and "a dvd b" "c dvd d"
  shows "b div a = d div c \<longleftrightarrow> b * c = a * d"
  using assms by (auto simp add: mult.commute [of _ a] dvd_div_mult_self dvd_div_eq_mult div_mult_swap intro: sym)

end

class ring_div = semiring_div + comm_ring_1
begin

subclass ring_1_no_zero_divisors ..

text {* Negation respects modular equivalence. *}

lemma mod_minus_eq: "(- a) mod b = (- (a mod b)) mod b"
proof -
  have "(- a) mod b = (- (a div b * b + a mod b)) mod b"
    by (simp only: mod_div_equality)
  also have "\<dots> = (- (a mod b) + - (a div b) * b) mod b"
    by (simp add: ac_simps)
  also have "\<dots> = (- (a mod b)) mod b"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_minus_cong:
  assumes "a mod b = a' mod b"
  shows "(- a) mod b = (- a') mod b"
proof -
  have "(- (a mod b)) mod b = (- (a' mod b)) mod b"
    unfolding assms ..
  thus ?thesis
    by (simp only: mod_minus_eq [symmetric])
qed

text {* Subtraction respects modular equivalence. *}

lemma mod_diff_left_eq:
  "(a - b) mod c = (a mod c - b) mod c"
  using mod_add_cong [of a c "a mod c" "- b" "- b"] by simp

lemma mod_diff_right_eq:
  "(a - b) mod c = (a - b mod c) mod c"
  using mod_add_cong [of a c a "- b" "- (b mod c)"] mod_minus_cong [of "b mod c" c b] by simp

lemma mod_diff_eq:
  "(a - b) mod c = (a mod c - b mod c) mod c"
  using mod_add_cong [of a c "a mod c" "- b" "- (b mod c)"] mod_minus_cong [of "b mod c" c b] by simp

lemma mod_diff_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a - b) mod c = (a' - b') mod c"
  using assms mod_add_cong [of a c a' "- b" "- b'"] mod_minus_cong [of b c "b'"] by simp

lemma dvd_neg_div: "y dvd x \<Longrightarrow> -x div y = - (x div y)"
apply (case_tac "y = 0") apply simp
apply (auto simp add: dvd_def)
apply (subgoal_tac "-(y * k) = y * - k")
 apply (simp only:)
 apply (erule div_mult_self1_is_id)
apply simp
done

lemma dvd_div_neg: "y dvd x \<Longrightarrow> x div -y = - (x div y)"
apply (case_tac "y = 0") apply simp
apply (auto simp add: dvd_def)
apply (subgoal_tac "y * k = -y * -k")
 apply (erule ssubst, rule div_mult_self1_is_id)
 apply simp
apply simp
done

lemma div_diff[simp]:
  "\<lbrakk> z dvd x; z dvd y\<rbrakk> \<Longrightarrow> (x - y) div z = x div z - y div z"
using div_add[where y = "- z" for z]
by (simp add: dvd_neg_div)

lemma div_minus_minus [simp]: "(-a) div (-b) = a div b"
  using div_mult_mult1 [of "- 1" a b]
  unfolding neg_equal_0_iff_equal by simp

lemma mod_minus_minus [simp]: "(-a) mod (-b) = - (a mod b)"
  using mod_mult_mult1 [of "- 1" a b] by simp

lemma div_minus_right: "a div (-b) = (-a) div b"
  using div_minus_minus [of "-a" b] by simp

lemma mod_minus_right: "a mod (-b) = - ((-a) mod b)"
  using mod_minus_minus [of "-a" b] by simp

lemma div_minus1_right [simp]: "a div (-1) = -a"
  using div_minus_right [of a 1] by simp

lemma mod_minus1_right [simp]: "a mod (-1) = 0"
  using mod_minus_right [of a 1] by simp

lemma minus_mod_self2 [simp]: 
  "(a - b) mod b = a mod b"
  by (simp add: mod_diff_right_eq)

lemma minus_mod_self1 [simp]: 
  "(b - a) mod b = - a mod b"
  using mod_add_self2 [of "- a" b] by simp

end


subsubsection {* Parity and division *}

class semiring_div_parity = semiring_div + semiring_numeral +
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
  from mod_div_equality have "1 div 2 * 2 + 1 mod 2 = 1" .
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
  fix a b c
  show "(c * a + b) mod a = 0 \<longleftrightarrow> b mod a = 0"
    by simp
next
  fix a b c
  assume "(b + c) mod a = 0"
  with mod_add_eq [of b c a]
  have "(b mod a + c mod a) mod a = 0"
    by simp
  moreover assume "b mod a = 0"
  ultimately show "c mod a = 0"
    by simp
next
  show "1 mod 2 = 1"
    by (fact one_mod_two_eq_one)
next
  fix a b
  assume "a mod 2 = 1"
  moreover assume "b mod 2 = 1"
  ultimately show "(a + b) mod 2 = 0"
    using mod_add_eq [of a b 2] by simp
next
  fix a b
  assume "(a * b) mod 2 = 0"
  then have "(a mod 2) * (b mod 2) = 0"
    by (cases "a mod 2 = 0") (simp_all add: mod_mult_eq [of a b 2])
  then show "a mod 2 = 0 \<or> b mod 2 = 0"
    by (rule divisors_zero)
next
  fix a
  assume "a mod 2 = 1"
  then have "a = a div 2 * 2 + 1" using mod_div_equality [of a 2] by simp
  then show "\<exists>b. a = b + 1" ..
qed

lemma even_iff_mod_2_eq_zero:
  "even a \<longleftrightarrow> a mod 2 = 0"
  by (fact dvd_eq_mod_eq_0)

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
  using mod_div_equality2 [of 2 a] by (simp add: even_iff_mod_2_eq_zero)

end


subsection {* Generic numeral division with a pragmatic type class *}

text {*
  The following type class contains everything necessary to formulate
  a division algorithm in ring structures with numerals, restricted
  to its positive segments.  This is its primary motiviation, and it
  could surely be formulated using a more fine-grained, more algebraic
  and less technical class hierarchy.
*}

class semiring_numeral_div = linordered_semidom + minus + semiring_div +
  assumes diff_invert_add1: "a + b = c \<Longrightarrow> a = c - b"
    and le_add_diff_inverse2: "b \<le> a \<Longrightarrow> a - b + b = a"
  assumes mult_div_cancel: "b * (a div b) = a - a mod b"
    and div_less: "0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a div b = 0"
    and mod_less: " 0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a mod b = a"
    and div_positive: "0 < b \<Longrightarrow> b \<le> a \<Longrightarrow> a div b > 0"
    and mod_less_eq_dividend: "0 \<le> a \<Longrightarrow> a mod b \<le> a"
    and pos_mod_bound: "0 < b \<Longrightarrow> a mod b < b"
    and pos_mod_sign: "0 < b \<Longrightarrow> 0 \<le> a mod b"
    and mod_mult2_eq: "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
    and div_mult2_eq: "0 \<le> c \<Longrightarrow> a div (b * c) = a div b div c"
  assumes discrete: "a < b \<longleftrightarrow> a + 1 \<le> b"
begin

lemma diff_zero [simp]:
  "a - 0 = a"
  by (rule diff_invert_add1 [symmetric]) simp

subclass semiring_div_parity
proof
  fix a
  show "a mod 2 = 0 \<or> a mod 2 = 1"
  proof (rule ccontr)
    assume "\<not> (a mod 2 = 0 \<or> a mod 2 = 1)"
    then have "a mod 2 \<noteq> 0" and "a mod 2 \<noteq> 1" by simp_all
    have "0 < 2" by simp
    with pos_mod_bound pos_mod_sign have "0 \<le> a mod 2" "a mod 2 < 2" by simp_all
    with `a mod 2 \<noteq> 0` have "0 < a mod 2" by simp
    with discrete have "1 \<le> a mod 2" by simp
    with `a mod 2 \<noteq> 1` have "1 < a mod 2" by simp
    with discrete have "2 \<le> a mod 2" by simp
    with `a mod 2 < 2` show False by simp
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
  with `0 < b` have "0 < a div b" by (auto intro: div_positive)
  then have [simp]: "1 \<le> a div b" by (simp add: discrete)
  with `0 < b` have mod_less: "a mod b < b" by (simp add: pos_mod_bound)
  def w \<equiv> "a div b mod 2" with parity have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  from assms w_exhaust have "w = 1"
    by (auto simp add: mod_w) (insert mod_less, auto)
  with mod_w have mod: "a mod (2 * b) = a mod b + b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq mult_div_cancel ac_simps)
  with `w = 1` have div: "2 * (a div (2 * b)) = a div b - 1" by simp
  then show ?P and ?Q
    by (simp_all add: div mod diff_invert_add1 [symmetric] le_add_diff_inverse2)
qed

lemma divmod_digit_0:
  assumes "0 < b" and "a mod (2 * b) < b"
  shows "2 * (a div (2 * b)) = a div b" (is "?P")
    and "a mod (2 * b) = a mod b" (is "?Q")
proof -
  def w \<equiv> "a div b mod 2" with parity have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  moreover have "b \<le> a mod b + b"
  proof -
    from `0 < b` pos_mod_sign have "0 \<le> a mod b" by blast
    then have "0 + b \<le> a mod b + b" by (rule add_right_mono)
    then show ?thesis by simp
  qed
  moreover note assms w_exhaust
  ultimately have "w = 0" by auto
  with mod_w have mod: "a mod (2 * b) = a mod b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq mult_div_cancel ac_simps)
  with `w = 0` have div: "2 * (a div (2 * b)) = a div b" by simp
  then show ?P and ?Q
    by (simp_all add: div mod)
qed

definition divmod :: "num \<Rightarrow> num \<Rightarrow> 'a \<times> 'a"
where
  "divmod m n = (numeral m div numeral n, numeral m mod numeral n)"

lemma fst_divmod [simp]:
  "fst (divmod m n) = numeral m div numeral n"
  by (simp add: divmod_def)

lemma snd_divmod [simp]:
  "snd (divmod m n) = numeral m mod numeral n"
  by (simp add: divmod_def)

definition divmod_step :: "num \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
where
  "divmod_step l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

text {*
  This is a formulation of one step (referring to one digit position)
  in school-method division: compare the dividend at the current
  digit position with the remainder from previous division steps
  and evaluate accordingly.
*}

lemma divmod_step_eq [code]:
  "divmod_step l (q, r) = (if numeral l \<le> r
    then (2 * q + 1, r - numeral l) else (2 * q, r))"
  by (simp add: divmod_step_def)

lemma divmod_step_simps [simp]:
  "r < numeral l \<Longrightarrow> divmod_step l (q, r) = (2 * q, r)"
  "numeral l \<le> r \<Longrightarrow> divmod_step l (q, r) = (2 * q + 1, r - numeral l)"
  by (auto simp add: divmod_step_eq not_le)

text {*
  This is a formulation of school-method division.
  If the divisor is smaller than the dividend, terminate.
  If not, shift the dividend to the right until termination
  occurs and then reiterate single division steps in the
  opposite direction.
*}

lemma divmod_divmod_step [code]:
  "divmod m n = (if m < n then (0, numeral m)
    else divmod_step n (divmod m (Num.Bit0 n)))"
proof (cases "m < n")
  case True then have "numeral m < numeral n" by simp
  then show ?thesis
    by (simp add: prod_eq_iff div_less mod_less)
next
  case False
  have "divmod m n =
    divmod_step n (numeral m div (2 * numeral n),
      numeral m mod (2 * numeral n))"
  proof (cases "numeral n \<le> numeral m mod (2 * numeral n)")
    case True
    with divmod_step_simps
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)) + 1, numeral m mod (2 * numeral n) - numeral n)"
        by blast
    moreover from True divmod_digit_1 [of "numeral m" "numeral n"]
      have "2 * (numeral m div (2 * numeral n)) + 1 = numeral m div numeral n"
      and "numeral m mod (2 * numeral n) - numeral n = numeral m mod numeral n"
      by simp_all
    ultimately show ?thesis by (simp only: divmod_def)
  next
    case False then have *: "numeral m mod (2 * numeral n) < numeral n"
      by (simp add: not_le)
    with divmod_step_simps
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)), numeral m mod (2 * numeral n))"
        by blast
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

lemma divmod_eq [simp]:
  "m < n \<Longrightarrow> divmod m n = (0, numeral m)"
  "n \<le> m \<Longrightarrow> divmod m n = divmod_step n (divmod m (Num.Bit0 n))"
  by (auto simp add: divmod_divmod_step [of m n])

lemma divmod_cancel [simp, code]:
  "divmod (Num.Bit0 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r))" (is ?P)
  "divmod (Num.Bit1 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r + 1))" (is ?Q)
proof -
  have *: "\<And>q. numeral (Num.Bit0 q) = 2 * numeral q"
    "\<And>q. numeral (Num.Bit1 q) = 2 * numeral q + 1"
    by (simp_all only: numeral_mult numeral.simps distrib) simp_all
  have "1 div 2 = 0" "1 mod 2 = 1" by (auto intro: div_less mod_less)
  then show ?P and ?Q
    by (simp_all add: prod_eq_iff split_def * [of m] * [of n] mod_mult_mult1
      div_mult2_eq [of _ _ 2] mod_mult2_eq [of _ _ 2] add.commute del: numeral_times_numeral)
qed

text {* Special case: divisibility *}

definition divides_aux :: "'a \<times> 'a \<Rightarrow> bool"
where
  "divides_aux qr \<longleftrightarrow> snd qr = 0"

lemma divides_aux_eq [simp]:
  "divides_aux (q, r) \<longleftrightarrow> r = 0"
  by (simp add: divides_aux_def)

lemma dvd_numeral_simp [simp]:
  "numeral m dvd numeral n \<longleftrightarrow> divides_aux (divmod n m)"
  by (simp add: divmod_def mod_eq_0_iff_dvd)

end

hide_fact (open) diff_invert_add1 le_add_diff_inverse2 diff_zero
  -- {* restore simple accesses for more general variants of theorems *}

  
subsection {* Division on @{typ nat} *}

text {*
  We define @{const div} and @{const mod} on @{typ nat} by means
  of a characteristic relation with two input arguments
  @{term "m\<Colon>nat"}, @{term "n\<Colon>nat"} and two output arguments
  @{term "q\<Colon>nat"}(uotient) and @{term "r\<Colon>nat"}(emainder).
*}

definition divmod_nat_rel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "divmod_nat_rel m n qr \<longleftrightarrow>
    m = fst qr * n + snd qr \<and>
      (if n = 0 then fst qr = 0 else if n > 0 then 0 \<le> snd qr \<and> snd qr < n else n < snd qr \<and> snd qr \<le> 0)"

text {* @{const divmod_nat_rel} is total: *}

lemma divmod_nat_rel_ex:
  obtains q r where "divmod_nat_rel m n (q, r)"
proof (cases "n = 0")
  case True  with that show thesis
    by (auto simp add: divmod_nat_rel_def)
next
  case False
  have "\<exists>q r. m = q * n + r \<and> r < n"
  proof (induct m)
    case 0 with `n \<noteq> 0`
    have "(0\<Colon>nat) = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    case (Suc m) then obtain q' r'
      where m: "m = q' * n + r'" and n: "r' < n" by auto
    then show ?case proof (cases "Suc r' < n")
      case True
      from m n have "Suc m = q' * n + Suc r'" by simp
      with True show ?thesis by blast
    next
      case False then have "n \<le> Suc r'" by auto
      moreover from n have "Suc r' \<le> n" by auto
      ultimately have "n = Suc r'" by auto
      with m have "Suc m = Suc q' * n + 0" by simp
      with `n \<noteq> 0` show ?thesis by blast
    qed
  qed
  with that show thesis
    using `n \<noteq> 0` by (auto simp add: divmod_nat_rel_def)
qed

text {* @{const divmod_nat_rel} is injective: *}

lemma divmod_nat_rel_unique:
  assumes "divmod_nat_rel m n qr"
    and "divmod_nat_rel m n qr'"
  shows "qr = qr'"
proof (cases "n = 0")
  case True with assms show ?thesis
    by (cases qr, cases qr')
      (simp add: divmod_nat_rel_def)
next
  case False
  have aux: "\<And>q r q' r'. q' * n + r' = q * n + r \<Longrightarrow> r < n \<Longrightarrow> q' \<le> (q\<Colon>nat)"
  apply (rule leI)
  apply (subst less_iff_Suc_add)
  apply (auto simp add: add_mult_distrib)
  done
  from `n \<noteq> 0` assms have *: "fst qr = fst qr'"
    by (auto simp add: divmod_nat_rel_def intro: order_antisym dest: aux sym)
  with assms have "snd qr = snd qr'"
    by (simp add: divmod_nat_rel_def)
  with * show ?thesis by (cases qr, cases qr') simp
qed

text {*
  We instantiate divisibility on the natural numbers by
  means of @{const divmod_nat_rel}:
*}

definition divmod_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "divmod_nat m n = (THE qr. divmod_nat_rel m n qr)"

lemma divmod_nat_rel_divmod_nat:
  "divmod_nat_rel m n (divmod_nat m n)"
proof -
  from divmod_nat_rel_ex
    obtain qr where rel: "divmod_nat_rel m n qr" .
  then show ?thesis
  by (auto simp add: divmod_nat_def intro: theI elim: divmod_nat_rel_unique)
qed

lemma divmod_nat_unique:
  assumes "divmod_nat_rel m n qr" 
  shows "divmod_nat m n = qr"
  using assms by (auto intro: divmod_nat_rel_unique divmod_nat_rel_divmod_nat)

instantiation nat :: semiring_div
begin

definition div_nat where
  "m div n = fst (divmod_nat m n)"

lemma fst_divmod_nat [simp]:
  "fst (divmod_nat m n) = m div n"
  by (simp add: div_nat_def)

definition mod_nat where
  "m mod n = snd (divmod_nat m n)"

lemma snd_divmod_nat [simp]:
  "snd (divmod_nat m n) = m mod n"
  by (simp add: mod_nat_def)

lemma divmod_nat_div_mod:
  "divmod_nat m n = (m div n, m mod n)"
  by (simp add: prod_eq_iff)

lemma div_nat_unique:
  assumes "divmod_nat_rel m n (q, r)" 
  shows "m div n = q"
  using assms by (auto dest!: divmod_nat_unique simp add: prod_eq_iff)

lemma mod_nat_unique:
  assumes "divmod_nat_rel m n (q, r)" 
  shows "m mod n = r"
  using assms by (auto dest!: divmod_nat_unique simp add: prod_eq_iff)

lemma divmod_nat_rel: "divmod_nat_rel m n (m div n, m mod n)"
  using divmod_nat_rel_divmod_nat by (simp add: divmod_nat_div_mod)

lemma divmod_nat_zero: "divmod_nat m 0 = (0, m)"
  by (simp add: divmod_nat_unique divmod_nat_rel_def)

lemma divmod_nat_zero_left: "divmod_nat 0 n = (0, 0)"
  by (simp add: divmod_nat_unique divmod_nat_rel_def)

lemma divmod_nat_base: "m < n \<Longrightarrow> divmod_nat m n = (0, m)"
  by (simp add: divmod_nat_unique divmod_nat_rel_def)

lemma divmod_nat_step:
  assumes "0 < n" and "n \<le> m"
  shows "divmod_nat m n = (Suc ((m - n) div n), (m - n) mod n)"
proof (rule divmod_nat_unique)
  have "divmod_nat_rel (m - n) n ((m - n) div n, (m - n) mod n)"
    by (rule divmod_nat_rel)
  thus "divmod_nat_rel m n (Suc ((m - n) div n), (m - n) mod n)"
    unfolding divmod_nat_rel_def using assms by auto
qed

text {* The ''recursion'' equations for @{const div} and @{const mod} *}

lemma div_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m div n = 0"
  using assms divmod_nat_base by (simp add: prod_eq_iff)

lemma le_div_geq:
  fixes m n :: nat
  assumes "0 < n" and "n \<le> m"
  shows "m div n = Suc ((m - n) div n)"
  using assms divmod_nat_step by (simp add: prod_eq_iff)

lemma mod_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m mod n = m"
  using assms divmod_nat_base by (simp add: prod_eq_iff)

lemma le_mod_geq:
  fixes m n :: nat
  assumes "n \<le> m"
  shows "m mod n = (m - n) mod n"
  using assms divmod_nat_step by (cases "n = 0") (simp_all add: prod_eq_iff)

instance proof
  fix m n :: nat
  show "m div n * n + m mod n = m"
    using divmod_nat_rel [of m n] by (simp add: divmod_nat_rel_def)
next
  fix m n q :: nat
  assume "n \<noteq> 0"
  then show "(q + m * n) div n = m + q div n"
    by (induct m) (simp_all add: le_div_geq)
next
  fix m n q :: nat
  assume "m \<noteq> 0"
  hence "\<And>a b. divmod_nat_rel n q (a, b) \<Longrightarrow> divmod_nat_rel (m * n) (m * q) (a, m * b)"
    unfolding divmod_nat_rel_def
    by (auto split: split_if_asm, simp_all add: algebra_simps)
  moreover from divmod_nat_rel have "divmod_nat_rel n q (n div q, n mod q)" .
  ultimately have "divmod_nat_rel (m * n) (m * q) (n div q, m * (n mod q))" .
  thus "(m * n) div (m * q) = n div q" by (rule div_nat_unique)
next
  fix n :: nat show "n div 0 = 0"
    by (simp add: div_nat_def divmod_nat_zero)
next
  fix n :: nat show "0 div n = 0"
    by (simp add: div_nat_def divmod_nat_zero_left)
qed

end

lemma divmod_nat_if [code]: "divmod_nat m n = (if n = 0 \<or> m < n then (0, m) else
  let (q, r) = divmod_nat (m - n) n in (Suc q, r))"
  by (simp add: prod_eq_iff case_prod_beta not_less le_div_geq le_mod_geq)

text {* Simproc for cancelling @{const div} and @{const mod} *}

ML_file "~~/src/Provers/Arith/cancel_div_mod.ML"

ML {*
structure Cancel_Div_Mod_Nat = Cancel_Div_Mod
(
  val div_name = @{const_name div};
  val mod_name = @{const_name mod};
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

  val div_mod_eqs = map mk_meta_eq [@{thm div_mod_equality}, @{thm div_mod_equality2}];

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac (Arith_Data.simp_all_tac
    (@{thm add_0_left} :: @{thm add_0_right} :: @{thms ac_simps}))
)
*}

simproc_setup cancel_div_mod_nat ("(m::nat) + n") = {* K Cancel_Div_Mod_Nat.proc *}


subsubsection {* Quotient *}

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
  from `m \<ge> n` obtain q where "m = n + q"
    by (auto simp add: le_iff_add)
  with `n > 0` show ?thesis by simp
qed

lemma div_eq_0_iff: "(a div b::nat) = 0 \<longleftrightarrow> a < b \<or> b = 0"
  by (metis div_less div_positive div_by_0 gr0I less_numeral_extra(3) not_less)

subsubsection {* Remainder *}

lemma mod_less_divisor [simp]:
  fixes m n :: nat
  assumes "n > 0"
  shows "m mod n < (n::nat)"
  using assms divmod_nat_rel [of m n] unfolding divmod_nat_rel_def by auto

lemma mod_Suc_le_divisor [simp]:
  "m mod Suc n \<le> n"
  using mod_less_divisor [of "Suc n" m] by arith

lemma mod_less_eq_dividend [simp]:
  fixes m n :: nat
  shows "m mod n \<le> m"
proof (rule add_leD2)
  from mod_div_equality have "m div n * n + m mod n = m" .
  then show "m div n * n + m mod n \<le> m" by auto
qed

lemma mod_geq: "\<not> m < (n\<Colon>nat) \<Longrightarrow> m mod n = (m - n) mod n"
by (simp add: le_mod_geq linorder_not_less)

lemma mod_if: "m mod (n\<Colon>nat) = (if m < n then m else (m - n) mod n)"
by (simp add: le_mod_geq)

lemma mod_1 [simp]: "m mod Suc 0 = 0"
by (induct m) (simp_all add: mod_geq)

(* a simple rearrangement of mod_div_equality: *)
lemma mult_div_cancel: "(n::nat) * (m div n) = m - (m mod n)"
  using mod_div_equality2 [of n m] by arith

lemma mod_le_divisor[simp]: "0 < n \<Longrightarrow> m mod n \<le> (n::nat)"
  apply (drule mod_less_divisor [where m = m])
  apply simp
  done

subsubsection {* Quotient and Remainder *}

lemma divmod_nat_rel_mult1_eq:
  "divmod_nat_rel b c (q, r)
   \<Longrightarrow> divmod_nat_rel (a * b) c (a * q + a * r div c, a * r mod c)"
by (auto simp add: split_ifs divmod_nat_rel_def algebra_simps)

lemma div_mult1_eq:
  "(a * b) div c = a * (b div c) + a * (b mod c) div (c::nat)"
by (blast intro: divmod_nat_rel_mult1_eq [THEN div_nat_unique] divmod_nat_rel)

lemma divmod_nat_rel_add1_eq:
  "divmod_nat_rel a c (aq, ar) \<Longrightarrow> divmod_nat_rel b c (bq, br)
   \<Longrightarrow> divmod_nat_rel (a + b) c (aq + bq + (ar + br) div c, (ar + br) mod c)"
by (auto simp add: split_ifs divmod_nat_rel_def algebra_simps)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma div_add1_eq:
  "(a+b) div (c::nat) = a div c + b div c + ((a mod c + b mod c) div c)"
by (blast intro: divmod_nat_rel_add1_eq [THEN div_nat_unique] divmod_nat_rel)

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  apply (cut_tac m = q and n = c in mod_less_divisor)
  apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
  apply (erule_tac P = "%x. ?lhs < ?rhs x" in ssubst)
  apply (simp add: add_mult_distrib2)
  done

lemma divmod_nat_rel_mult2_eq:
  "divmod_nat_rel a b (q, r)
   \<Longrightarrow> divmod_nat_rel a (b * c) (q div c, b *(q mod c) + r)"
by (auto simp add: mult.commute mult.left_commute divmod_nat_rel_def add_mult_distrib2 [symmetric] mod_lemma)

lemma div_mult2_eq: "a div (b * c) = (a div b) div (c::nat)"
by (force simp add: divmod_nat_rel [THEN divmod_nat_rel_mult2_eq, THEN div_nat_unique])

lemma mod_mult2_eq: "a mod (b * c) = b * (a div b mod c) + a mod (b::nat)"
by (auto simp add: mult.commute divmod_nat_rel [THEN divmod_nat_rel_mult2_eq, THEN mod_nat_unique])

instance nat :: semiring_numeral_div
  by intro_classes (auto intro: div_positive simp add: mult_div_cancel mod_mult2_eq div_mult2_eq)


subsubsection {* Further Facts about Quotient and Remainder *}

lemma div_1 [simp]:
  "m div Suc 0 = m"
  using div_by_1 [of m] by simp

(* Monotonicity of div in first argument *)
lemma div_le_mono [rule_format (no_asm)]:
    "\<forall>m::nat. m \<le> n --> (m div k) \<le> (n div k)"
apply (case_tac "k=0", simp)
apply (induct "n" rule: nat_less_induct, clarify)
apply (case_tac "n<k")
(* 1  case n<k *)
apply simp
(* 2  case n >= k *)
apply (case_tac "m<k")
(* 2.1  case m<k *)
apply simp
(* 2.2  case m>=k *)
apply (simp add: div_geq diff_le_mono)
done

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

text{*A fact for the mutilated chess board*}
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
  from mod_div_equality obtain q where "q * d + m mod d = m" by blast
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
  shows "n * q \<le> m \<and> m < n * Suc q \<longleftrightarrow> q = ((m\<Colon>nat) div n)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  with mult_div_cancel have nq: "n * q = m - (m mod n)" by simp
  then have A: "n * q \<le> m" by simp
  have "n - (m mod n) > 0" using mod_less_divisor assms by auto
  then have "m < m + (n - (m mod n))" by simp
  then have "m < n + (m - (m mod n))" by simp
  with nq have "m < n + n * q" by simp
  then have B: "m < n * Suc q" by simp
  from A B show ?lhs ..
next
  assume P: ?lhs
  then have "divmod_nat_rel m n (q, m - n * q)"
    unfolding divmod_nat_rel_def by (auto simp add: ac_simps)
  with divmod_nat_rel_unique divmod_nat_rel [of m n]
  have "(q, m - n * q) = (m div n, m mod n)" by auto
  then show ?rhs by simp
qed

theorem split_div':
  "P ((m::nat) div n) = ((n = 0 \<and> P 0) \<or>
   (\<exists>q. (n * q \<le> m \<and> m < n * (Suc q)) \<and> P q))"
  apply (case_tac "0 < n")
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

theorem mod_div_equality': "(m::nat) mod n = m - (m div n) * n"
  using mod_div_equality [of m n] by arith

lemma div_mod_equality': "(m::nat) div n * n = m - m mod n"
  using mod_div_equality [of m n] by arith
(* FIXME: very similar to mult_div_cancel *)

lemma div_eq_dividend_iff: "a \<noteq> 0 \<Longrightarrow> (a :: nat) div b = a \<longleftrightarrow> b = 1"
  apply rule
  apply (cases "b = 0")
  apply simp_all
  apply (metis (full_types) One_nat_def Suc_lessI div_less_dividend less_not_refl3)
  done


subsubsection {* An ``induction'' law for modulus arithmetic. *}

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
      show "?A 0" by simp  -- "by contradiction"
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

lemma mod2_gr_0 [simp]: "0 < (m\<Colon>nat) mod 2 \<longleftrightarrow> m mod 2 = 1"
proof -
  { fix n :: nat have  "(n::nat) < 2 \<Longrightarrow> n = 0 \<or> n = 1" by (cases n) simp_all }
  moreover have "m mod 2 < 2" by simp
  ultimately have "m mod 2 = 0 \<or> m mod 2 = 1" .
  then show ?thesis by auto
qed

text{*These lemmas collapse some needless occurrences of Suc:
    at least three Sucs, since two and fewer are rewritten back to Suc again!
    We already have some rules to simplify operands smaller than 3.*}

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

lemma mod_mult_self4 [simp]: "Suc (k*n + m) mod n = Suc m mod n"
proof -
  have "Suc (k * n + m) mod n = (k * n + Suc m) mod n" by simp
  also have "... = Suc m mod n" by (rule mod_mult_self3) 
  finally show ?thesis .
qed

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
  "odd n \<Longrightarrow> 2 * (n div 2) = n - (1 :: nat)"
  using odd_two_times_div_two_succ [of n] by simp

lemma odd_Suc_minus_one [simp]:
  "odd n \<Longrightarrow> Suc (n - Suc 0) = n"
  by (auto elim: oddE)

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


subsection {* Division on @{typ int} *}

definition divmod_int_rel :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> bool" where
    --{*definition of quotient and remainder*}
  "divmod_int_rel a b = (\<lambda>(q, r). a = b * q + r \<and>
    (if 0 < b then 0 \<le> r \<and> r < b else if b < 0 then b < r \<and> r \<le> 0 else q = 0))"

text {*
  The following algorithmic devlopment actually echos what has already
  been developed in class @{class semiring_numeral_div}.  In the long
  run it seems better to derive division on @{typ int} just from
  division on @{typ nat} and instantiate @{class semiring_numeral_div}
  accordingly.
*}

definition adjust :: "int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
    --{*for the division algorithm*}
    "adjust b = (\<lambda>(q, r). if 0 \<le> r - b then (2 * q + 1, r - b)
                         else (2 * q, r))"

text{*algorithm for the case @{text "a\<ge>0, b>0"}*}
function posDivAlg :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "posDivAlg a b = (if a < b \<or>  b \<le> 0 then (0, a)
     else adjust b (posDivAlg a (2 * b)))"
by auto
termination by (relation "measure (\<lambda>(a, b). nat (a - b + 1))")
  (auto simp add: mult_2)

text{*algorithm for the case @{text "a<0, b>0"}*}
function negDivAlg :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "negDivAlg a b = (if 0 \<le>a + b \<or> b \<le> 0  then (-1, a + b)
     else adjust b (negDivAlg a (2 * b)))"
by auto
termination by (relation "measure (\<lambda>(a, b). nat (- a - b))")
  (auto simp add: mult_2)

text{*algorithm for the general case @{term "b\<noteq>0"}*}

definition divmod_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
    --{*The full division algorithm considers all possible signs for a, b
       including the special case @{text "a=0, b<0"} because 
       @{term negDivAlg} requires @{term "a<0"}.*}
  "divmod_int a b = (if 0 \<le> a then if 0 \<le> b then posDivAlg a b
                  else if a = 0 then (0, 0)
                       else apsnd uminus (negDivAlg (-a) (-b))
               else 
                  if 0 < b then negDivAlg a b
                  else apsnd uminus (posDivAlg (-a) (-b)))"

instantiation int :: Divides.div
begin

definition div_int where
  "a div b = fst (divmod_int a b)"

lemma fst_divmod_int [simp]:
  "fst (divmod_int a b) = a div b"
  by (simp add: div_int_def)

definition mod_int where
  "a mod b = snd (divmod_int a b)"

lemma snd_divmod_int [simp]:
  "snd (divmod_int a b) = a mod b"
  by (simp add: mod_int_def)

instance ..

end

lemma divmod_int_mod_div:
  "divmod_int p q = (p div q, p mod q)"
  by (simp add: prod_eq_iff)

text{*
Here is the division algorithm in ML:

\begin{verbatim}
    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
               in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
           end

    fun negDivAlg (a,b) =
      if 0\<le>a+b then (~1,a+b)
      else let val (q,r) = negDivAlg(a, 2*b)
               in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
           end;

    fun negateSnd (q,r:int) = (q,~r);

    fun divmod (a,b) = if 0\<le>a then 
                          if b>0 then posDivAlg (a,b) 
                           else if a=0 then (0,0)
                                else negateSnd (negDivAlg (~a,~b))
                       else 
                          if 0<b then negDivAlg (a,b)
                          else        negateSnd (posDivAlg (~a,~b));
\end{verbatim}
*}


subsubsection {* Uniqueness and Monotonicity of Quotients and Remainders *}

lemma unique_quotient_lemma:
     "[| b*q' + r'  \<le> b*q + r;  0 \<le> r';  r' < b;  r < b |]  
      ==> q' \<le> (q::int)"
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
     "[| b*q' + r' \<le> b*q + r;  r \<le> 0;  b < r;  b < r' |]  
      ==> q \<le> (q'::int)"
by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma, 
    auto)

lemma unique_quotient:
     "[| divmod_int_rel a b (q, r); divmod_int_rel a b (q', r') |]  
      ==> q = q'"
apply (simp add: divmod_int_rel_def linorder_neq_iff split: split_if_asm)
apply (blast intro: order_antisym
             dest: order_eq_refl [THEN unique_quotient_lemma] 
             order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
done


lemma unique_remainder:
     "[| divmod_int_rel a b (q, r); divmod_int_rel a b (q', r') |]  
      ==> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: divmod_int_rel_def)
apply (blast intro: unique_quotient)
done


subsubsection {* Correctness of @{term posDivAlg}, the Algorithm for Non-Negative Dividends *}

text{*And positive divisors*}

lemma adjust_eq [simp]:
     "adjust b (q, r) = 
      (let diff = r - b in  
        if 0 \<le> diff then (2 * q + 1, diff)   
                     else (2*q, r))"
  by (simp add: Let_def adjust_def)

declare posDivAlg.simps [simp del]

text{*use with a simproc to avoid repeatedly proving the premise*}
lemma posDivAlg_eqn:
     "0 < b ==>  
      posDivAlg a b = (if a<b then (0,a) else adjust b (posDivAlg a (2*b)))"
by (rule posDivAlg.simps [THEN trans], simp)

text{*Correctness of @{term posDivAlg}: it computes quotients correctly*}
theorem posDivAlg_correct:
  assumes "0 \<le> a" and "0 < b"
  shows "divmod_int_rel a b (posDivAlg a b)"
  using assms
  apply (induct a b rule: posDivAlg.induct)
  apply auto
  apply (simp add: divmod_int_rel_def)
  apply (subst posDivAlg_eqn, simp add: distrib_left)
  apply (case_tac "a < b")
  apply simp_all
  apply (erule splitE)
  apply (auto simp add: distrib_left Let_def ac_simps mult_2_right)
  done


subsubsection {* Correctness of @{term negDivAlg}, the Algorithm for Negative Dividends *}

text{*And positive divisors*}

declare negDivAlg.simps [simp del]

text{*use with a simproc to avoid repeatedly proving the premise*}
lemma negDivAlg_eqn:
     "0 < b ==>  
      negDivAlg a b =       
       (if 0\<le>a+b then (-1,a+b) else adjust b (negDivAlg a (2*b)))"
by (rule negDivAlg.simps [THEN trans], simp)

(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b equals 0, not -1*)
lemma negDivAlg_correct:
  assumes "a < 0" and "b > 0"
  shows "divmod_int_rel a b (negDivAlg a b)"
  using assms
  apply (induct a b rule: negDivAlg.induct)
  apply (auto simp add: linorder_not_le)
  apply (simp add: divmod_int_rel_def)
  apply (subst negDivAlg_eqn, assumption)
  apply (case_tac "a + b < (0\<Colon>int)")
  apply simp_all
  apply (erule splitE)
  apply (auto simp add: distrib_left Let_def ac_simps mult_2_right)
  done


subsubsection {* Existence Shown by Proving the Division Algorithm to be Correct *}

(*the case a=0*)
lemma divmod_int_rel_0: "divmod_int_rel 0 b (0, 0)"
by (auto simp add: divmod_int_rel_def linorder_neq_iff)

lemma posDivAlg_0 [simp]: "posDivAlg 0 b = (0, 0)"
by (subst posDivAlg.simps, auto)

lemma posDivAlg_0_right [simp]: "posDivAlg a 0 = (0, a)"
by (subst posDivAlg.simps, auto)

lemma negDivAlg_minus1 [simp]: "negDivAlg (- 1) b = (- 1, b - 1)"
by (subst negDivAlg.simps, auto)

lemma divmod_int_rel_neg: "divmod_int_rel (-a) (-b) qr ==> divmod_int_rel a b (apsnd uminus qr)"
by (auto simp add: divmod_int_rel_def)

lemma divmod_int_correct: "divmod_int_rel a b (divmod_int a b)"
apply (cases "b = 0", simp add: divmod_int_def divmod_int_rel_def)
by (force simp add: linorder_neq_iff divmod_int_rel_0 divmod_int_def divmod_int_rel_neg
                    posDivAlg_correct negDivAlg_correct)

lemma divmod_int_unique:
  assumes "divmod_int_rel a b qr" 
  shows "divmod_int a b = qr"
  using assms divmod_int_correct [of a b]
  using unique_quotient [of a b] unique_remainder [of a b]
  by (metis pair_collapse)

lemma divmod_int_rel_div_mod: "divmod_int_rel a b (a div b, a mod b)"
  using divmod_int_correct by (simp add: divmod_int_mod_div)

lemma div_int_unique: "divmod_int_rel a b (q, r) \<Longrightarrow> a div b = q"
  by (simp add: divmod_int_rel_div_mod [THEN unique_quotient])

lemma mod_int_unique: "divmod_int_rel a b (q, r) \<Longrightarrow> a mod b = r"
  by (simp add: divmod_int_rel_div_mod [THEN unique_remainder])

instance int :: ring_div
proof
  fix a b :: int
  show "a div b * b + a mod b = a"
    using divmod_int_rel_div_mod [of a b]
    unfolding divmod_int_rel_def by (simp add: mult.commute)
next
  fix a b c :: int
  assume "b \<noteq> 0"
  hence "divmod_int_rel (a + c * b) b (c + a div b, a mod b)"
    using divmod_int_rel_div_mod [of a b]
    unfolding divmod_int_rel_def by (auto simp: algebra_simps)
  thus "(a + c * b) div b = c + a div b"
    by (rule div_int_unique)
next
  fix a b c :: int
  assume "c \<noteq> 0"
  hence "\<And>q r. divmod_int_rel a b (q, r)
    \<Longrightarrow> divmod_int_rel (c * a) (c * b) (q, c * r)"
    unfolding divmod_int_rel_def
    by - (rule linorder_cases [of 0 b], auto simp: algebra_simps
      mult_less_0_iff zero_less_mult_iff mult_strict_right_mono
      mult_strict_right_mono_neg zero_le_mult_iff mult_le_0_iff)
  hence "divmod_int_rel (c * a) (c * b) (a div b, c * (a mod b))"
    using divmod_int_rel_div_mod [of a b] .
  thus "(c * a) div (c * b) = a div b"
    by (rule div_int_unique)
next
  fix a :: int show "a div 0 = 0"
    by (rule div_int_unique, simp add: divmod_int_rel_def)
next
  fix a :: int show "0 div a = 0"
    by (rule div_int_unique, auto simp add: divmod_int_rel_def)
qed

text{*Basic laws about division and remainder*}

lemma zmod_zdiv_equality: "(a::int) = b * (a div b) + (a mod b)"
  by (fact mod_div_equality2 [symmetric])

text {* Tool setup *}

ML {*
structure Cancel_Div_Mod_Int = Cancel_Div_Mod
(
  val div_name = @{const_name div};
  val mod_name = @{const_name mod};
  val mk_binop = HOLogic.mk_binop;
  val mk_sum = Arith_Data.mk_sum HOLogic.intT;
  val dest_sum = Arith_Data.dest_sum;

  val div_mod_eqs = map mk_meta_eq [@{thm div_mod_equality}, @{thm div_mod_equality2}];

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac (Arith_Data.simp_all_tac 
    (@{thm diff_conv_add_uminus} :: @{thms add_0_left add_0_right} @ @{thms ac_simps}))
)
*}

simproc_setup cancel_div_mod_int ("(k::int) + l") = {* K Cancel_Div_Mod_Int.proc *}

lemma pos_mod_conj: "(0::int) < b \<Longrightarrow> 0 \<le> a mod b \<and> a mod b < b"
  using divmod_int_correct [of a b]
  by (auto simp add: divmod_int_rel_def prod_eq_iff)

lemmas pos_mod_sign [simp] = pos_mod_conj [THEN conjunct1]
   and pos_mod_bound [simp] = pos_mod_conj [THEN conjunct2]

lemma neg_mod_conj: "b < (0::int) \<Longrightarrow> a mod b \<le> 0 \<and> b < a mod b"
  using divmod_int_correct [of a b]
  by (auto simp add: divmod_int_rel_def prod_eq_iff)

lemmas neg_mod_sign [simp] = neg_mod_conj [THEN conjunct1]
   and neg_mod_bound [simp] = neg_mod_conj [THEN conjunct2]


subsubsection {* General Properties of div and mod *}

lemma div_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a div b = 0"
apply (rule div_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

lemma div_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a div b = 0"
apply (rule div_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

lemma div_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a div b = -1"
apply (rule div_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

(*There is no div_neg_pos_trivial because  0 div b = 0 would supersede it*)

lemma mod_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a mod b = a"
apply (rule_tac q = 0 in mod_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

lemma mod_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a mod b = a"
apply (rule_tac q = 0 in mod_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

lemma mod_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a mod b = a+b"
apply (rule_tac q = "-1" in mod_int_unique)
apply (auto simp add: divmod_int_rel_def)
done

text{*There is no @{text mod_neg_pos_trivial}.*}


subsubsection {* Laws for div and mod with Unary Minus *}

lemma zminus1_lemma:
     "divmod_int_rel a b (q, r) ==> b \<noteq> 0
      ==> divmod_int_rel (-a) b (if r=0 then -q else -q - 1,  
                          if r=0 then 0 else b-r)"
by (force simp add: split_ifs divmod_int_rel_def linorder_neq_iff right_diff_distrib)


lemma zdiv_zminus1_eq_if:
     "b \<noteq> (0::int)  
      ==> (-a) div b =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: divmod_int_rel_div_mod [THEN zminus1_lemma, THEN div_int_unique])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
apply (case_tac "b = 0", simp)
apply (blast intro: divmod_int_rel_div_mod [THEN zminus1_lemma, THEN mod_int_unique])
done

lemma zmod_zminus1_not_zero:
  fixes k l :: int
  shows "- k mod l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  unfolding zmod_zminus1_eq_if by auto

lemma zdiv_zminus2_eq_if:
     "b \<noteq> (0::int)  
      ==> a div (-b) =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (simp add: zdiv_zminus1_eq_if div_minus_right)

lemma zmod_zminus2_eq_if:
     "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
by (simp add: zmod_zminus1_eq_if mod_minus_right)

lemma zmod_zminus2_not_zero:
  fixes k l :: int
  shows "k mod - l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  unfolding zmod_zminus2_eq_if by auto 


subsubsection {* Computation of Division and Remainder *}

lemma div_eq_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_int_def divmod_int_def)

lemma zmod_minus1: "(0::int) < b ==> -1 mod b = b - 1"
by (simp add: mod_int_def divmod_int_def)

text{*a positive, b positive *}

lemma div_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a div b = fst (posDivAlg a b)"
by (simp add: div_int_def divmod_int_def)

lemma mod_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a mod b = snd (posDivAlg a b)"
by (simp add: mod_int_def divmod_int_def)

text{*a negative, b positive *}

lemma div_neg_pos: "[| a < 0;  0 < b |] ==> a div b = fst (negDivAlg a b)"
by (simp add: div_int_def divmod_int_def)

lemma mod_neg_pos: "[| a < 0;  0 < b |] ==> a mod b = snd (negDivAlg a b)"
by (simp add: mod_int_def divmod_int_def)

text{*a positive, b negative *}

lemma div_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a div b = fst (apsnd uminus (negDivAlg (-a) (-b)))"
by (simp add: div_int_def divmod_int_def)

lemma mod_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a mod b = snd (apsnd uminus (negDivAlg (-a) (-b)))"
by (simp add: mod_int_def divmod_int_def)

text{*a negative, b negative *}

lemma div_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a div b = fst (apsnd uminus (posDivAlg (-a) (-b)))"
by (simp add: div_int_def divmod_int_def)

lemma mod_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a mod b = snd (apsnd uminus (posDivAlg (-a) (-b)))"
by (simp add: mod_int_def divmod_int_def)

text {*Simplify expresions in which div and mod combine numerical constants*}

lemma int_div_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r]) (simp add: divmod_int_rel_def)

lemma int_div_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r],
    simp add: divmod_int_rel_def)

lemma int_mod_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: divmod_int_rel_def)

lemma int_mod_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: divmod_int_rel_def)

text {*
  numeral simprocs -- high chance that these can be replaced
  by divmod algorithm from @{class semiring_numeral_div}
*}

ML {*
local
  val mk_number = HOLogic.mk_number HOLogic.intT
  val plus = @{term "plus :: int \<Rightarrow> int \<Rightarrow> int"}
  val times = @{term "times :: int \<Rightarrow> int \<Rightarrow> int"}
  val zero = @{term "0 :: int"}
  val less = @{term "op < :: int \<Rightarrow> int \<Rightarrow> bool"}
  val le = @{term "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"}
  val simps = @{thms arith_simps} @ @{thms rel_simps} @ [@{thm numeral_1_eq_1 [symmetric]}]
  fun prove ctxt goal = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop goal)
    (K (ALLGOALS (full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps simps))));
  fun binary_proc proc ctxt ct =
    (case Thm.term_of ct of
      _ $ t $ u =>
      (case try (apply2 (`(snd o HOLogic.dest_number))) (t, u) of
        SOME args => proc ctxt args
      | NONE => NONE)
    | _ => NONE);
in
  fun divmod_proc posrule negrule =
    binary_proc (fn ctxt => fn ((a, t), (b, u)) =>
      if b = 0 then NONE
      else
        let
          val (q, r) = apply2 mk_number (Integer.div_mod a b)
          val goal1 = HOLogic.mk_eq (t, plus $ (times $ u $ q) $ r)
          val (goal2, goal3, rule) =
            if b > 0
            then (le $ zero $ r, less $ r $ u, posrule RS eq_reflection)
            else (le $ r $ zero, less $ u $ r, negrule RS eq_reflection)
        in SOME (rule OF map (prove ctxt) [goal1, goal2, goal3]) end)
end
*}

simproc_setup binary_int_div
  ("numeral m div numeral n :: int" |
   "numeral m div - numeral n :: int" |
   "- numeral m div numeral n :: int" |
   "- numeral m div - numeral n :: int") =
  {* K (divmod_proc @{thm int_div_pos_eq} @{thm int_div_neg_eq}) *}

simproc_setup binary_int_mod
  ("numeral m mod numeral n :: int" |
   "numeral m mod - numeral n :: int" |
   "- numeral m mod numeral n :: int" |
   "- numeral m mod - numeral n :: int") =
  {* K (divmod_proc @{thm int_mod_pos_eq} @{thm int_mod_neg_eq}) *}

lemmas posDivAlg_eqn_numeral [simp] =
    posDivAlg_eqn [of "numeral v" "numeral w", OF zero_less_numeral] for v w

lemmas negDivAlg_eqn_numeral [simp] =
    negDivAlg_eqn [of "numeral v" "- numeral w", OF zero_less_numeral] for v w


text {* Special-case simplification: @{text "\<plusminus>1 div z"} and @{text "\<plusminus>1 mod z"} *}

lemma [simp]:
  shows div_one_bit0: "1 div numeral (Num.Bit0 v) = (0 :: int)"
    and mod_one_bit0: "1 mod numeral (Num.Bit0 v) = (1 :: int)"
    and div_one_bit1: "1 div numeral (Num.Bit1 v) = (0 :: int)"
    and mod_one_bit1: "1 mod numeral (Num.Bit1 v) = (1 :: int)"
    and div_one_neg_numeral: "1 div - numeral v = (- 1 :: int)"
    and mod_one_neg_numeral: "1 mod - numeral v = (1 :: int) - numeral v"
  by (simp_all del: arith_special
    add: div_pos_pos mod_pos_pos div_pos_neg mod_pos_neg posDivAlg_eqn)

lemma [simp]:
  shows div_neg_one_numeral: "- 1 div numeral v = (- 1 :: int)"
    and mod_neg_one_numeral: "- 1 mod numeral v = numeral v - (1 :: int)"
    and div_neg_one_neg_bit0: "- 1 div - numeral (Num.Bit0 v) = (0 :: int)"
    and mod_neg_one_neb_bit0: "- 1 mod - numeral (Num.Bit0 v) = (- 1 :: int)"
    and div_neg_one_neg_bit1: "- 1 div - numeral (Num.Bit1 v) = (0 :: int)"
    and mod_neg_one_neb_bit1: "- 1 mod - numeral (Num.Bit1 v) = (- 1 :: int)"
  by (simp_all add: div_eq_minus1 zmod_minus1)


subsubsection {* Monotonicity in the First Argument (Dividend) *}

lemma zdiv_mono1: "[| a \<le> a';  0 < (b::int) |] ==> a div b \<le> a' div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done

lemma zdiv_mono1_neg: "[| a \<le> a';  (b::int) < 0 |] ==> a' div b \<le> a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst, simp_all)
done


subsubsection {* Monotonicity in the Second Argument (Divisor) *}

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
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
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
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst, simp_all)
done


subsubsection {* More Algebraic Laws for div and mod *}

text{*proving (a*b) div c = a * (b div c) + a * (b mod c) *}

lemma zmult1_lemma:
     "[| divmod_int_rel b c (q, r) |]  
      ==> divmod_int_rel (a * b) c (a*q + a*r div c, a*r mod c)"
by (auto simp add: split_ifs divmod_int_rel_def linorder_neq_iff distrib_left ac_simps)

lemma zdiv_zmult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: divmod_int_rel_div_mod [THEN zmult1_lemma, THEN div_int_unique])
done

text{*proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) *}

lemma zadd1_lemma:
     "[| divmod_int_rel a c (aq, ar);  divmod_int_rel b c (bq, br) |]  
      ==> divmod_int_rel (a+b) c (aq + bq + (ar+br) div c, (ar+br) mod c)"
by (force simp add: split_ifs divmod_int_rel_def linorder_neq_iff distrib_left)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq:
     "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (case_tac "c = 0", simp)
apply (blast intro: zadd1_lemma [OF divmod_int_rel_div_mod divmod_int_rel_div_mod] div_int_unique)
done

lemma posDivAlg_div_mod:
  assumes "k \<ge> 0"
  and "l \<ge> 0"
  shows "posDivAlg k l = (k div l, k mod l)"
proof (cases "l = 0")
  case True then show ?thesis by (simp add: posDivAlg.simps)
next
  case False with assms posDivAlg_correct
    have "divmod_int_rel k l (fst (posDivAlg k l), snd (posDivAlg k l))"
    by simp
  from div_int_unique [OF this] mod_int_unique [OF this]
  show ?thesis by simp
qed

lemma negDivAlg_div_mod:
  assumes "k < 0"
  and "l > 0"
  shows "negDivAlg k l = (k div l, k mod l)"
proof -
  from assms have "l \<noteq> 0" by simp
  from assms negDivAlg_correct
    have "divmod_int_rel k l (fst (negDivAlg k l), snd (negDivAlg k l))"
    by simp
  from div_int_unique [OF this] mod_int_unique [OF this]
  show ?thesis by simp
qed

lemma zmod_eq_0_iff: "(m mod d = 0) = (EX q::int. m = d*q)"
by (simp add: dvd_eq_mod_eq_0 [symmetric] dvd_def)

(* REVISIT: should this be generalized to all semiring_div types? *)
lemmas zmod_eq_0D [dest!] = zmod_eq_0_iff [THEN iffD1]

lemma zmod_zdiv_equality':
  "(m\<Colon>int) mod n = m - (m div n) * n"
  using mod_div_equality [of m n] by arith


subsubsection {* Proving  @{term "a div (b * c) = (a div b) div c"} *}

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

text{*first, four lemmas to bound the remainder for the cases b<0 and b>0 *}

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

lemma zmult2_lemma: "[| divmod_int_rel a b (q, r); 0 < c |]  
      ==> divmod_int_rel a (b * c) (q div c, b*(q mod c) + r)"
by (auto simp add: mult.assoc divmod_int_rel_def linorder_neq_iff
                   zero_less_mult_iff distrib_left [symmetric] 
                   zmult2_lemma_aux1 zmult2_lemma_aux2 zmult2_lemma_aux3 zmult2_lemma_aux4 mult_less_0_iff split: split_if_asm)

lemma zdiv_zmult2_eq:
  fixes a b c :: int
  shows "0 \<le> c \<Longrightarrow> a div (b * c) = (a div b) div c"
apply (case_tac "b = 0", simp)
apply (force simp add: le_less divmod_int_rel_div_mod [THEN zmult2_lemma, THEN div_int_unique])
done

lemma zmod_zmult2_eq:
  fixes a b c :: int
  shows "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
apply (case_tac "b = 0", simp)
apply (force simp add: le_less divmod_int_rel_div_mod [THEN zmult2_lemma, THEN mod_int_unique])
done

lemma div_pos_geq:
  fixes k l :: int
  assumes "0 < l" and "l \<le> k"
  shows "k div l = (k - l) div l + 1"
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with assms show ?thesis by simp
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


subsubsection {* Splitting Rules for div and mod *}

text{*The proofs of the two lemmas below are essentially identical*}

lemma split_pos_lemma:
 "0<k ==> 
    P(n div k :: int)(n mod k) = (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst mod_add_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_pos_pos_trivial mod_pos_pos_trivial)  
txt{*converse direction*}
apply (drule_tac x = "n div k" in spec) 
apply (drule_tac x = "n mod k" in spec, simp)
done

lemma split_neg_lemma:
 "k<0 ==>
    P(n div k :: int)(n mod k) = (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i j)"
apply (rule iffI, clarify)
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst mod_add_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_neg_neg_trivial mod_neg_neg_trivial)  
txt{*converse direction*}
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

text {* Enable (lin)arith to deal with @{const div} and @{const mod}
  when these are applied to some constant that is of the form
  @{term "numeral k"}: *}
declare split_zdiv [of _ _ "numeral k", arith_split] for k
declare split_zmod [of _ _ "numeral k", arith_split] for k


subsubsection {* Computing @{text "div"} and @{text "mod"} with shifting *}

lemma pos_divmod_int_rel_mult_2:
  assumes "0 \<le> b"
  assumes "divmod_int_rel a b (q, r)"
  shows "divmod_int_rel (1 + 2*a) (2*b) (q, 1 + 2*r)"
  using assms unfolding divmod_int_rel_def by auto

declaration {* K (Lin_Arith.add_simps @{thms uminus_numeral_One}) *}

lemma neg_divmod_int_rel_mult_2:
  assumes "b \<le> 0"
  assumes "divmod_int_rel (a + 1) b (q, r)"
  shows "divmod_int_rel (1 + 2*a) (2*b) (q, 2*r - 1)"
  using assms unfolding divmod_int_rel_def by auto

text{*computing div by shifting *}

lemma pos_zdiv_mult_2: "(0::int) \<le> a ==> (1 + 2*b) div (2*a) = b div a"
  using pos_divmod_int_rel_mult_2 [OF _ divmod_int_rel_div_mod]
  by (rule div_int_unique)

lemma neg_zdiv_mult_2: 
  assumes A: "a \<le> (0::int)" shows "(1 + 2*b) div (2*a) = (b+1) div a"
  using neg_divmod_int_rel_mult_2 [OF A divmod_int_rel_div_mod]
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
  using pos_divmod_int_rel_mult_2 [OF assms divmod_int_rel_div_mod]
  by (rule mod_int_unique)

lemma neg_zmod_mult_2:
  fixes a b :: int
  assumes "a \<le> 0"
  shows "(1 + 2 * b) mod (2 * a) = 2 * ((b + 1) mod a) - 1"
  using neg_divmod_int_rel_mult_2 [OF assms divmod_int_rel_div_mod]
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
  with `?L` show ?R by blast
next
  assume ?R thus ?L
    by(auto simp: div_pos_pos_trivial div_neg_neg_trivial)
qed


subsubsection {* Quotients of Signs *}

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

text{* Now for some equivalences of the form @{text"a div b >=< 0 \<longleftrightarrow> \<dots>"}
conditional upon the sign of @{text a} or @{text b}. There are many more.
They should all be simp rules unless that causes too much search. *}

lemma pos_imp_zdiv_nonneg_iff: "(0::int) < b ==> (0 \<le> a div b) = (0 \<le> a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: linorder_neq_iff)
apply (simp (no_asm_use) add: linorder_not_less [symmetric])
apply (blast intro: div_neg_pos_less0)
done

lemma neg_imp_zdiv_nonneg_iff:
  "b < (0::int) ==> (0 \<le> a div b) = (a \<le> (0::int))"
apply (subst div_minus_minus [symmetric])
apply (subst pos_imp_zdiv_nonneg_iff, auto)
done

(*But not (a div b \<le> 0 iff a\<le>0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

lemma pos_imp_zdiv_pos_iff:
  "0<k \<Longrightarrow> 0 < (i::int) div k \<longleftrightarrow> k \<le> i"
using pos_imp_zdiv_nonneg_iff[of k i] zdiv_eq_0_iff[of i k]
by arith

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


subsubsection {* The Divides Relation *}

lemma dvd_eq_mod_eq_0_numeral:
  "numeral x dvd (numeral y :: 'a) \<longleftrightarrow> numeral y mod numeral x = (0 :: 'a::semiring_div)"
  by (fact dvd_eq_mod_eq_0)


subsubsection {* Further properties *}

lemma zmult_div_cancel: "(n::int) * (m div n) = m - (m mod n)"
  using zmod_zdiv_equality[where a="m" and b="n"]
  by (simp add: algebra_simps) (* FIXME: generalize *)

instance int :: semiring_numeral_div
  by intro_classes (auto intro: zmod_le_nonneg_dividend
    simp add: zmult_div_cancel
    pos_imp_zdiv_pos_iff div_pos_pos_trivial mod_pos_pos_trivial
    zmod_zmult2_eq zdiv_zmult2_eq)
  
lemma zdiv_int: "int (a div b) = (int a) div (int b)"
apply (subst split_div, auto)
apply (subst split_zdiv, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and r="int j" and r'=ja in unique_quotient)
apply (auto simp add: divmod_int_rel_def of_nat_mult)
done

lemma zmod_int: "int (a mod b) = (int a) mod (int b)"
apply (subst split_mod, auto)
apply (subst split_zmod, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and q="int i" and q'=ia 
       in unique_remainder)
apply (auto simp add: divmod_int_rel_def of_nat_mult)
done

lemma abs_div: "(y::int) dvd x \<Longrightarrow> abs (x div y) = abs x div abs y"
by (unfold dvd_def, cases "y=0", auto simp add: abs_mult)

text{*Suggested by Matthias Daum*}
lemma int_power_div_base:
     "\<lbrakk>0 < m; 0 < k\<rbrakk> \<Longrightarrow> k ^ m div k = (k::int) ^ (m - Suc 0)"
apply (subgoal_tac "k ^ m = k ^ ((m - Suc 0) + Suc 0)")
 apply (erule ssubst)
 apply (simp only: power_add)
 apply simp_all
done

text {* by Brian Huffman *}
lemma zminus_zmod: "- ((x::int) mod m) mod m = - x mod m"
by (rule mod_minus_eq [symmetric])

lemma zdiff_zmod_left: "(x mod m - y) mod m = (x - y) mod (m::int)"
by (rule mod_diff_left_eq [symmetric])

lemma zdiff_zmod_right: "(x - y mod m) mod m = (x - y) mod (m::int)"
by (rule mod_diff_right_eq [symmetric])

lemmas zmod_simps =
  mod_add_left_eq  [symmetric]
  mod_add_right_eq [symmetric]
  mod_mult_right_eq[symmetric]
  mod_mult_left_eq [symmetric]
  power_mod
  zminus_zmod zdiff_zmod_left zdiff_zmod_right

text {* Distributive laws for function @{text nat}. *}

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

text  {* transfer setup *}

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

text{*Suggested by Matthias Daum*}
lemma int_div_less_self: "\<lbrakk>0 < x; 1 < k\<rbrakk> \<Longrightarrow> x div k < (x::int)"
apply (subgoal_tac "nat x div nat k < nat x")
 apply (simp add: nat_div_distrib [symmetric])
apply (rule Divides.div_less_dividend, simp_all)
done

lemma zmod_eq_dvd_iff: "(x::int) mod n = y mod n \<longleftrightarrow> n dvd x - y"
proof
  assume H: "x mod n = y mod n"
  hence "x mod n - y mod n = 0" by simp
  hence "(x mod n - y mod n) mod n = 0" by simp 
  hence "(x - y) mod n = 0" by (simp add: mod_diff_eq[symmetric])
  thus "n dvd x - y" by (simp add: dvd_eq_mod_eq_0)
next
  assume H: "n dvd x - y"
  then obtain k where k: "x-y = n*k" unfolding dvd_def by blast
  hence "x = n*k + y" by simp
  hence "x mod n = (n*k + y) mod n" by simp
  thus "x mod n = y mod n" by (simp add: mod_add_left_eq)
qed

lemma nat_mod_eq_lemma: assumes xyn: "(x::nat) mod n = y  mod n" and xy:"y \<le> x"
  shows "\<exists>q. x = y + n * q"
proof-
  from xy have th: "int x - int y = int (x - y)" by simp 
  from xyn have "int x mod int n = int y mod int n" 
    by (simp add: zmod_int [symmetric])
  hence "int n dvd int x - int y" by (simp only: zmod_eq_dvd_iff[symmetric]) 
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

text {*
  This re-embedding of natural division on integers goes back to the
  time when numerals had been signed numerals.  It should
  now be replaced by the algorithm developed in @{class semiring_numeral_div}.  
*}

lemma div_nat_numeral [simp]:
  "(numeral v :: nat) div numeral v' = nat (numeral v div numeral v')"
  by (simp add: nat_div_distrib)

lemma one_div_nat_numeral [simp]:
  "Suc 0 div numeral v' = nat (1 div numeral v')"
  by (subst nat_div_distrib, simp_all)

lemma mod_nat_numeral [simp]:
  "(numeral v :: nat) mod numeral v' = nat (numeral v mod numeral v')"
  by (simp add: nat_mod_distrib)

lemma one_mod_nat_numeral [simp]:
  "Suc 0 mod numeral v' = nat (1 mod numeral v')"
  by (subst nat_mod_distrib) simp_all


subsubsection {* Tools setup *}

text {* Nitpick *}

lemmas [nitpick_unfold] = dvd_eq_mod_eq_0 mod_div_equality' zmod_zdiv_equality'


subsubsection {* Code generation *}

definition divmod_abs :: "int \<Rightarrow> int \<Rightarrow> int \<times> int"
where
  "divmod_abs k l = (\<bar>k\<bar> div \<bar>l\<bar>, \<bar>k\<bar> mod \<bar>l\<bar>)"

lemma fst_divmod_abs [simp]:
  "fst (divmod_abs k l) = \<bar>k\<bar> div \<bar>l\<bar>"
  by (simp add: divmod_abs_def)

lemma snd_divmod_abs [simp]:
  "snd (divmod_abs k l) = \<bar>k\<bar> mod \<bar>l\<bar>"
  by (simp add: divmod_abs_def)

lemma divmod_abs_code [code]:
  "divmod_abs (Int.Pos k) (Int.Pos l) = divmod k l"
  "divmod_abs (Int.Neg k) (Int.Neg l) = divmod k l"
  "divmod_abs (Int.Neg k) (Int.Pos l) = divmod k l"
  "divmod_abs (Int.Pos k) (Int.Neg l) = divmod k l"
  "divmod_abs j 0 = (0, \<bar>j\<bar>)"
  "divmod_abs 0 j = (0, 0)"
  by (simp_all add: prod_eq_iff)

lemma divmod_int_divmod_abs:
  "divmod_int k l = (if k = 0 then (0, 0) else if l = 0 then (0, k) else
  apsnd ((op *) (sgn l)) (if 0 < l \<and> 0 \<le> k \<or> l < 0 \<and> k < 0
    then divmod_abs k l
    else (let (r, s) = divmod_abs k l in
       if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have aux: "\<And>q::int. - k = l * q \<longleftrightarrow> k = l * - q" by auto
  show ?thesis
    by (simp add: prod_eq_iff split_def Let_def)
      (auto simp add: aux not_less not_le zdiv_zminus1_eq_if
      zmod_zminus1_eq_if zdiv_zminus2_eq_if zmod_zminus2_eq_if)
qed

lemma divmod_int_code [code]:
  "divmod_int k l = (if k = 0 then (0, 0) else if l = 0 then (0, k) else
  apsnd ((op *) (sgn l)) (if sgn k = sgn l
    then divmod_abs k l
    else (let (r, s) = divmod_abs k l in
      if s = 0 then (- r, 0) else (- r - 1, \<bar>l\<bar> - s))))"
proof -
  have "k \<noteq> 0 \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> 0 < l \<and> 0 \<le> k \<or> l < 0 \<and> k < 0 \<longleftrightarrow> sgn k = sgn l"
    by (auto simp add: not_less sgn_if)
  then show ?thesis by (simp add: divmod_int_divmod_abs)
qed

hide_const (open) divmod_abs

code_identifier
  code_module Divides \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end


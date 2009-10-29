(*  Title:      HOL/Divides.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* The division operators div and mod *}

theory Divides
imports Nat_Numeral Nat_Transfer
uses
  "~~/src/Provers/Arith/assoc_fold.ML"
  "~~/src/Provers/Arith/cancel_numerals.ML"
  "~~/src/Provers/Arith/combine_numerals.ML"
  "~~/src/Provers/Arith/cancel_numeral_factor.ML"
  "~~/src/Provers/Arith/extract_common_term.ML"
  ("Tools/numeral_simprocs.ML")
  ("Tools/nat_numeral_simprocs.ML")
  "~~/src/Provers/Arith/cancel_div_mod.ML"
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

text {* @{const div} and @{const mod} *}

lemma mod_div_equality2: "b * (a div b) + a mod b = a"
  unfolding mult_commute [of b]
  by (rule mod_div_equality)

lemma mod_div_equality': "a mod b + a div b * b = a"
  using mod_div_equality [of a b]
  by (simp only: add_ac)

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
  using assms div_mult_self1 [of b a c] by (simp add: mult_commute)

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
    by (simp add: add_commute [of a] add_assoc left_distrib)
  then have "a div b * b + (a + c * b) mod b = a div b * b + a mod b"
    by (simp add: mod_div_equality)
  then show ?thesis by simp
qed

lemma mod_mult_self2 [simp]: "(a + b * c) mod b = a mod b"
  by (simp add: mult_commute [of b])

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
  using assms div_mult_self1 [of b a 1] by (simp add: add_commute)

lemma div_add_self2 [simp]:
  assumes "b \<noteq> 0"
  shows "(a + b) div b = a div b + 1"
  using assms div_add_self1 [of b a] by (simp add: add_commute)

lemma mod_add_self1 [simp]:
  "(b + a) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by (simp add: add_commute)

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

lemma dvd_eq_mod_eq_0 [code_unfold]: "a dvd b \<longleftrightarrow> b mod a = 0"
proof
  assume "b mod a = 0"
  with mod_div_equality [of b a] have "b div a * a = b" by simp
  then have "b = a * (b div a)" unfolding mult_commute ..
  then have "\<exists>c. b = a * c" ..
  then show "a dvd b" unfolding dvd_def .
next
  assume "a dvd b"
  then have "\<exists>c. b = a * c" unfolding dvd_def .
  then obtain c where "b = a * c" ..
  then have "b mod a = a * c mod a" by simp
  then have "b mod a = c * a mod a" by (simp add: mult_commute)
  then show "b mod a = 0" by simp
qed

lemma mod_div_trivial [simp]: "a mod b div b = 0"
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

lemma mod_mod_trivial [simp]: "a mod b mod b = a mod b"
proof -
  have "a mod b mod b = (a mod b + a div b * b) mod b"
    by (simp only: mod_mult_self1)
  also have "\<dots> = a mod b"
    by (simp only: mod_div_equality')
  finally show ?thesis .
qed

lemma dvd_imp_mod_0: "a dvd b \<Longrightarrow> b mod a = 0"
by (rule dvd_eq_mod_eq_0[THEN iffD1])

lemma dvd_div_mult_self: "a dvd b \<Longrightarrow> (b div a) * a = b"
by (subst (2) mod_div_equality [of b a, symmetric]) (simp add:dvd_imp_mod_0)

lemma dvd_mult_div_cancel: "a dvd b \<Longrightarrow> a * (b div a) = b"
by (drule dvd_div_mult_self) (simp add: mult_commute)

lemma dvd_div_mult: "a dvd b \<Longrightarrow> (b div a) * c = b * c div a"
apply (cases "a = 0")
 apply simp
apply (auto simp: dvd_def mult_assoc)
done

lemma div_dvd_div[simp]:
  "a dvd b \<Longrightarrow> a dvd c \<Longrightarrow> (b div a dvd c div a) = (b dvd c)"
apply (cases "a = 0")
 apply simp
apply (unfold dvd_def)
apply auto
 apply(blast intro:mult_assoc[symmetric])
apply(fastsimp simp add: mult_assoc)
done

lemma dvd_mod_imp_dvd: "[| k dvd m mod n;  k dvd n |] ==> k dvd m"
  apply (subgoal_tac "k dvd (m div n) *n + m mod n")
   apply (simp add: mod_div_equality)
  apply (simp only: dvd_add dvd_mult)
  done

text {* Addition respects modular equivalence. *}

lemma mod_add_left_eq: "(a + b) mod c = (a mod c + b) mod c"
proof -
  have "(a + b) mod c = (a div c * c + a mod c + b) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a mod c + b + a div c * c) mod c"
    by (simp only: add_ac)
  also have "\<dots> = (a mod c + b) mod c"
    by (rule mod_mult_self1)
  finally show ?thesis .
qed

lemma mod_add_right_eq: "(a + b) mod c = (a + b mod c) mod c"
proof -
  have "(a + b) mod c = (a + (b div c * c + b mod c)) mod c"
    by (simp only: mod_div_equality)
  also have "\<dots> = (a + b mod c + b div c * c) mod c"
    by (simp only: add_ac)
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
    by (simp only: add_ac mult_ac)
  also have "\<dots> = a mod c"
    by (simp only: mod_div_equality)
  finally show ?thesis .
qed

lemma div_mult_div_if_dvd:
  "y dvd x \<Longrightarrow> z dvd w \<Longrightarrow> (x div y) * (w div z) = (x * w) div (y * z)"
  apply (cases "y = 0", simp)
  apply (cases "z = 0", simp)
  apply (auto elim!: dvdE simp add: algebra_simps)
  apply (subst mult_assoc [symmetric])
  apply (simp add: no_zero_divisors)
  done

lemma div_mult_mult2 [simp]:
  "c \<noteq> 0 \<Longrightarrow> (a * c) div (b * c) = a div b"
  by (drule div_mult_mult1) (simp add: mult_commute)

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
  using mod_mult_mult1 [of c a b] by (simp add: mult_commute)

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

end

class ring_div = semiring_div + idom
begin

text {* Negation respects modular equivalence. *}

lemma mod_minus_eq: "(- a) mod b = (- (a mod b)) mod b"
proof -
  have "(- a) mod b = (- (a div b * b + a mod b)) mod b"
    by (simp only: mod_div_equality)
  also have "\<dots> = (- (a mod b) + - (a div b) * b) mod b"
    by (simp only: minus_add_distrib minus_mult_left add_ac)
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

lemma mod_diff_left_eq: "(a - b) mod c = (a mod c - b) mod c"
  unfolding diff_minus
  by (intro mod_add_cong mod_minus_cong) simp_all

lemma mod_diff_right_eq: "(a - b) mod c = (a - b mod c) mod c"
  unfolding diff_minus
  by (intro mod_add_cong mod_minus_cong) simp_all

lemma mod_diff_eq: "(a - b) mod c = (a mod c - b mod c) mod c"
  unfolding diff_minus
  by (intro mod_add_cong mod_minus_cong) simp_all

lemma mod_diff_cong:
  assumes "a mod c = a' mod c"
  assumes "b mod c = b' mod c"
  shows "(a - b) mod c = (a' - b') mod c"
  unfolding diff_minus using assms
  by (intro mod_add_cong mod_minus_cong)

lemma dvd_neg_div: "y dvd x \<Longrightarrow> -x div y = - (x div y)"
apply (case_tac "y = 0") apply simp
apply (auto simp add: dvd_def)
apply (subgoal_tac "-(y * k) = y * - k")
 apply (erule ssubst)
 apply (erule div_mult_self1_is_id)
apply simp
done

lemma dvd_div_neg: "y dvd x \<Longrightarrow> x div -y = - (x div y)"
apply (case_tac "y = 0") apply simp
apply (auto simp add: dvd_def)
apply (subgoal_tac "y * k = -y * -k")
 apply (erule ssubst)
 apply (rule div_mult_self1_is_id)
 apply simp
apply simp
done

end


subsection {* Division on @{typ nat} *}

text {*
  We define @{const div} and @{const mod} on @{typ nat} by means
  of a characteristic relation with two input arguments
  @{term "m\<Colon>nat"}, @{term "n\<Colon>nat"} and two output arguments
  @{term "q\<Colon>nat"}(uotient) and @{term "r\<Colon>nat"}(emainder).
*}

definition divmod_rel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "divmod_rel m n qr \<longleftrightarrow>
    m = fst qr * n + snd qr \<and>
      (if n = 0 then fst qr = 0 else if n > 0 then 0 \<le> snd qr \<and> snd qr < n else n < snd qr \<and> snd qr \<le> 0)"

text {* @{const divmod_rel} is total: *}

lemma divmod_rel_ex:
  obtains q r where "divmod_rel m n (q, r)"
proof (cases "n = 0")
  case True  with that show thesis
    by (auto simp add: divmod_rel_def)
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
    using `n \<noteq> 0` by (auto simp add: divmod_rel_def)
qed

text {* @{const divmod_rel} is injective: *}

lemma divmod_rel_unique:
  assumes "divmod_rel m n qr"
    and "divmod_rel m n qr'"
  shows "qr = qr'"
proof (cases "n = 0")
  case True with assms show ?thesis
    by (cases qr, cases qr')
      (simp add: divmod_rel_def)
next
  case False
  have aux: "\<And>q r q' r'. q' * n + r' = q * n + r \<Longrightarrow> r < n \<Longrightarrow> q' \<le> (q\<Colon>nat)"
  apply (rule leI)
  apply (subst less_iff_Suc_add)
  apply (auto simp add: add_mult_distrib)
  done
  from `n \<noteq> 0` assms have "fst qr = fst qr'"
    by (auto simp add: divmod_rel_def intro: order_antisym dest: aux sym)
  moreover from this assms have "snd qr = snd qr'"
    by (simp add: divmod_rel_def)
  ultimately show ?thesis by (cases qr, cases qr') simp
qed

text {*
  We instantiate divisibility on the natural numbers by
  means of @{const divmod_rel}:
*}

instantiation nat :: semiring_div
begin

definition divmod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  [code del]: "divmod m n = (THE qr. divmod_rel m n qr)"

lemma divmod_rel_divmod:
  "divmod_rel m n (divmod m n)"
proof -
  from divmod_rel_ex
    obtain qr where rel: "divmod_rel m n qr" .
  then show ?thesis
  by (auto simp add: divmod_def intro: theI elim: divmod_rel_unique)
qed

lemma divmod_eq:
  assumes "divmod_rel m n qr" 
  shows "divmod m n = qr"
  using assms by (auto intro: divmod_rel_unique divmod_rel_divmod)

definition div_nat where
  "m div n = fst (divmod m n)"

definition mod_nat where
  "m mod n = snd (divmod m n)"

lemma divmod_div_mod:
  "divmod m n = (m div n, m mod n)"
  unfolding div_nat_def mod_nat_def by simp

lemma div_eq:
  assumes "divmod_rel m n (q, r)" 
  shows "m div n = q"
  using assms by (auto dest: divmod_eq simp add: divmod_div_mod)

lemma mod_eq:
  assumes "divmod_rel m n (q, r)" 
  shows "m mod n = r"
  using assms by (auto dest: divmod_eq simp add: divmod_div_mod)

lemma divmod_rel: "divmod_rel m n (m div n, m mod n)"
  by (simp add: div_nat_def mod_nat_def divmod_rel_divmod)

lemma divmod_zero:
  "divmod m 0 = (0, m)"
proof -
  from divmod_rel [of m 0] show ?thesis
    unfolding divmod_div_mod divmod_rel_def by simp
qed

lemma divmod_base:
  assumes "m < n"
  shows "divmod m n = (0, m)"
proof -
  from divmod_rel [of m n] show ?thesis
    unfolding divmod_div_mod divmod_rel_def
    using assms by (cases "m div n = 0")
      (auto simp add: gr0_conv_Suc [of "m div n"])
qed

lemma divmod_step:
  assumes "0 < n" and "n \<le> m"
  shows "divmod m n = (Suc ((m - n) div n), (m - n) mod n)"
proof -
  from divmod_rel have divmod_m_n: "divmod_rel m n (m div n, m mod n)" .
  with assms have m_div_n: "m div n \<ge> 1"
    by (cases "m div n") (auto simp add: divmod_rel_def)
  from assms divmod_m_n have "divmod_rel (m - n) n (m div n - Suc 0, m mod n)"
    by (cases "m div n") (auto simp add: divmod_rel_def)
  with divmod_eq have "divmod (m - n) n = (m div n - Suc 0, m mod n)" by simp
  moreover from divmod_div_mod have "divmod (m - n) n = ((m - n) div n, (m - n) mod n)" .
  ultimately have "m div n = Suc ((m - n) div n)"
    and "m mod n = (m - n) mod n" using m_div_n by simp_all
  then show ?thesis using divmod_div_mod by simp
qed

text {* The ''recursion'' equations for @{const div} and @{const mod} *}

lemma div_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m div n = 0"
  using assms divmod_base divmod_div_mod by simp

lemma le_div_geq:
  fixes m n :: nat
  assumes "0 < n" and "n \<le> m"
  shows "m div n = Suc ((m - n) div n)"
  using assms divmod_step divmod_div_mod by simp

lemma mod_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m mod n = m"
  using assms divmod_base divmod_div_mod by simp

lemma le_mod_geq:
  fixes m n :: nat
  assumes "n \<le> m"
  shows "m mod n = (m - n) mod n"
  using assms divmod_step divmod_div_mod by (cases "n = 0") simp_all

instance proof -
  have [simp]: "\<And>n::nat. n div 0 = 0"
    by (simp add: div_nat_def divmod_zero)
  have [simp]: "\<And>n::nat. 0 div n = 0"
  proof -
    fix n :: nat
    show "0 div n = 0"
      by (cases "n = 0") simp_all
  qed
  show "OFCLASS(nat, semiring_div_class)" proof
    fix m n :: nat
    show "m div n * n + m mod n = m"
      using divmod_rel [of m n] by (simp add: divmod_rel_def)
  next
    fix m n q :: nat
    assume "n \<noteq> 0"
    then show "(q + m * n) div n = m + q div n"
      by (induct m) (simp_all add: le_div_geq)
  next
    fix m n q :: nat
    assume "m \<noteq> 0"
    then show "(m * n) div (m * q) = n div q"
    proof (cases "n \<noteq> 0 \<and> q \<noteq> 0")
      case False then show ?thesis by auto
    next
      case True with `m \<noteq> 0`
        have "m > 0" and "n > 0" and "q > 0" by auto
      then have "\<And>a b. divmod_rel n q (a, b) \<Longrightarrow> divmod_rel (m * n) (m * q) (a, m * b)"
        by (auto simp add: divmod_rel_def) (simp_all add: algebra_simps)
      moreover from divmod_rel have "divmod_rel n q (n div q, n mod q)" .
      ultimately have "divmod_rel (m * n) (m * q) (n div q, m * (n mod q))" .
      then show ?thesis by (simp add: div_eq)
    qed
  qed simp_all
qed

end

text {* Simproc for cancelling @{const div} and @{const mod} *}

ML {*
local

structure CancelDivMod = CancelDivModFun(struct

  val div_name = @{const_name div};
  val mod_name = @{const_name mod};
  val mk_binop = HOLogic.mk_binop;
  val mk_sum = Nat_Arith.mk_sum;
  val dest_sum = Nat_Arith.dest_sum;

  val div_mod_eqs = map mk_meta_eq [@{thm div_mod_equality}, @{thm div_mod_equality2}];

  val trans = trans;

  val prove_eq_sums = Arith_Data.prove_conv2 all_tac (Arith_Data.simp_all_tac
    (@{thm monoid_add_class.add_0_left} :: @{thm monoid_add_class.add_0_right} :: @{thms add_ac}))

end)

in

val cancel_div_mod_nat_proc = Simplifier.simproc @{theory}
  "cancel_div_mod" ["(m::nat) + n"] (K CancelDivMod.proc);

val _ = Addsimprocs [cancel_div_mod_nat_proc];

end
*}

text {* code generator setup *}

lemma divmod_if [code]: "divmod m n = (if n = 0 \<or> m < n then (0, m) else
  let (q, r) = divmod (m - n) n in (Suc q, r))"
by (simp add: divmod_zero divmod_base divmod_step)
    (simp add: divmod_div_mod)

code_modulename SML
  Divides Nat

code_modulename OCaml
  Divides Nat

code_modulename Haskell
  Divides Nat


subsubsection {* Quotient *}

lemma div_geq: "0 < n \<Longrightarrow>  \<not> m < n \<Longrightarrow> m div n = Suc ((m - n) div n)"
by (simp add: le_div_geq linorder_not_less)

lemma div_if: "0 < n \<Longrightarrow> m div n = (if m < n then 0 else Suc ((m - n) div n))"
by (simp add: div_geq)

lemma div_mult_self_is_m [simp]: "0<n ==> (m*n) div n = (m::nat)"
by simp

lemma div_mult_self1_is_m [simp]: "0<n ==> (n*m) div n = (m::nat)"
by simp


subsubsection {* Remainder *}

lemma mod_less_divisor [simp]:
  fixes m n :: nat
  assumes "n > 0"
  shows "m mod n < (n::nat)"
  using assms divmod_rel [of m n] unfolding divmod_rel_def by auto

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

lemma mod_mult_distrib: "(m mod n) * (k\<Colon>nat) = (m * k) mod (n * k)"
  apply (cases "n = 0", simp)
  apply (cases "k = 0", simp)
  apply (induct m rule: nat_less_induct)
  apply (subst mod_if, simp)
  apply (simp add: mod_geq diff_mult_distrib)
  done

lemma mod_mult_distrib2: "(k::nat) * (m mod n) = (k*m) mod (k*n)"
by (simp add: mult_commute [of k] mod_mult_distrib)

(* a simple rearrangement of mod_div_equality: *)
lemma mult_div_cancel: "(n::nat) * (m div n) = m - (m mod n)"
by (cut_tac a = m and b = n in mod_div_equality2, arith)

lemma mod_le_divisor[simp]: "0 < n \<Longrightarrow> m mod n \<le> (n::nat)"
  apply (drule mod_less_divisor [where m = m])
  apply simp
  done

subsubsection {* Quotient and Remainder *}

lemma divmod_rel_mult1_eq:
  "divmod_rel b c (q, r) \<Longrightarrow> c > 0
   \<Longrightarrow> divmod_rel (a * b) c (a * q + a * r div c, a * r mod c)"
by (auto simp add: split_ifs divmod_rel_def algebra_simps)

lemma div_mult1_eq:
  "(a * b) div c = a * (b div c) + a * (b mod c) div (c::nat)"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel [THEN divmod_rel_mult1_eq, THEN div_eq])
done

lemma divmod_rel_add1_eq:
  "divmod_rel a c (aq, ar) \<Longrightarrow> divmod_rel b c (bq, br) \<Longrightarrow>  c > 0
   \<Longrightarrow> divmod_rel (a + b) c (aq + bq + (ar + br) div c, (ar + br) mod c)"
by (auto simp add: split_ifs divmod_rel_def algebra_simps)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma div_add1_eq:
  "(a+b) div (c::nat) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel_add1_eq [THEN div_eq] divmod_rel)
done

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  apply (cut_tac m = q and n = c in mod_less_divisor)
  apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
  apply (erule_tac P = "%x. ?lhs < ?rhs x" in ssubst)
  apply (simp add: add_mult_distrib2)
  done

lemma divmod_rel_mult2_eq:
  "divmod_rel a b (q, r) \<Longrightarrow> 0 < b \<Longrightarrow> 0 < c
   \<Longrightarrow> divmod_rel a (b * c) (q div c, b *(q mod c) + r)"
by (auto simp add: mult_ac divmod_rel_def add_mult_distrib2 [symmetric] mod_lemma)

lemma div_mult2_eq: "a div (b*c) = (a div b) div (c::nat)"
  apply (cases "b = 0", simp)
  apply (cases "c = 0", simp)
  apply (force simp add: divmod_rel [THEN divmod_rel_mult2_eq, THEN div_eq])
  done

lemma mod_mult2_eq: "a mod (b*c) = b*(a div b mod c) + a mod (b::nat)"
  apply (cases "b = 0", simp)
  apply (cases "c = 0", simp)
  apply (auto simp add: mult_commute divmod_rel [THEN divmod_rel_mult2_eq, THEN mod_eq])
  done


subsubsection{*Further Facts about Quotient and Remainder*}

lemma div_1 [simp]: "m div Suc 0 = m"
by (induct m) (simp_all add: div_geq)


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
lemma div_less_dividend [rule_format]:
     "!!n::nat. 1<n ==> 0 < m --> m div n < m"
apply (induct_tac m rule: nat_less_induct)
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

declare div_less_dividend [simp]

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
lemma mod_eqD: "(m mod d = r) ==> \<exists>q::nat. m = r + q*d"
  apply (cut_tac a = m in mod_div_equality)
  apply (simp only: add_ac)
  apply (blast intro: sym)
  done

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
        with not0 n j P show "P i" by(simp add:add_ac)
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
  then have "divmod_rel m n (q, m - n * q)"
    unfolding divmod_rel_def by (auto simp add: mult_ac)
  with divmod_rel_unique divmod_rel [of m n]
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
      thus "P j" using not0 P by(simp add:add_ac mult_ac)
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
  apply (rule_tac P="%x. m mod n = x - (m div n) * n" in
    subst [OF mod_div_equality [of _ n]])
  apply arith
  done

lemma div_mod_equality':
  fixes m n :: nat
  shows "m div n * n = m - m mod n"
proof -
  have "m mod n \<le> m mod n" ..
  from div_mod_equality have 
    "m div n * n + m mod n - m mod n = m - m mod n" by simp
  with diff_add_assoc [OF `m mod n \<le> m mod n`, of "m div n * n"] have
    "m div n * n + (m mod n - m mod n) = m - m mod n"
    by simp
  then show ?thesis by simp
qed


subsubsection {*An ``induction'' law for modulus arithmetic.*}

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
by (auto simp add: numeral_2_eq_2 le_div_geq)

lemma add_self_div_2 [simp]: "(m + m) div 2 = (m::nat)"
by (simp add: nat_mult_2 [symmetric])

lemma mod2_Suc_Suc [simp]: "Suc(Suc(m)) mod 2 = m mod 2"
apply (subgoal_tac "m mod 2 < 2")
apply (erule less_2_cases [THEN disjE])
apply (simp_all (no_asm_simp) add: Let_def mod_Suc nat_1)
done

lemma mod2_gr_0 [simp]: "0 < (m\<Colon>nat) mod 2 \<longleftrightarrow> m mod 2 = 1"
proof -
  { fix n :: nat have  "(n::nat) < 2 \<Longrightarrow> n = 0 \<or> n = 1" by (induct n) simp_all }
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

lemmas Suc_div_eq_add3_div_number_of =
    Suc_div_eq_add3_div [of _ "number_of v", standard]
declare Suc_div_eq_add3_div_number_of [simp]

lemmas Suc_mod_eq_add3_mod_number_of =
    Suc_mod_eq_add3_mod [of _ "number_of v", standard]
declare Suc_mod_eq_add3_mod_number_of [simp]


subsection {* Proof Tools setup; Combination and Cancellation Simprocs *}

declare split_div[of _ _ "number_of k", standard, arith_split]
declare split_mod[of _ _ "number_of k", standard, arith_split]


subsubsection{*For @{text combine_numerals}*}

lemma left_add_mult_distrib: "i*u + (j*u + k) = (i+j)*u + (k::nat)"
by (simp add: add_mult_distrib)


subsubsection{*For @{text cancel_numerals}*}

lemma nat_diff_add_eq1:
     "j <= (i::nat) ==> ((i*u + m) - (j*u + n)) = (((i-j)*u + m) - n)"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_diff_add_eq2:
     "i <= (j::nat) ==> ((i*u + m) - (j*u + n)) = (m - ((j-i)*u + n))"
by (simp split add: nat_diff_split add: add_mult_distrib)

lemma nat_eq_add_iff1:
     "j <= (i::nat) ==> (i*u + m = j*u + n) = ((i-j)*u + m = n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_eq_add_iff2:
     "i <= (j::nat) ==> (i*u + m = j*u + n) = (m = (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff1:
     "j <= (i::nat) ==> (i*u + m < j*u + n) = ((i-j)*u + m < n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_less_add_iff2:
     "i <= (j::nat) ==> (i*u + m < j*u + n) = (m < (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff1:
     "j <= (i::nat) ==> (i*u + m <= j*u + n) = ((i-j)*u + m <= n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)

lemma nat_le_add_iff2:
     "i <= (j::nat) ==> (i*u + m <= j*u + n) = (m <= (j-i)*u + n)"
by (auto split add: nat_diff_split simp add: add_mult_distrib)


subsubsection{*For @{text cancel_numeral_factors} *}

lemma nat_mult_le_cancel1: "(0::nat) < k ==> (k*m <= k*n) = (m<=n)"
by auto

lemma nat_mult_less_cancel1: "(0::nat) < k ==> (k*m < k*n) = (m<n)"
by auto

lemma nat_mult_eq_cancel1: "(0::nat) < k ==> (k*m = k*n) = (m=n)"
by auto

lemma nat_mult_div_cancel1: "(0::nat) < k ==> (k*m) div (k*n) = (m div n)"
by auto

lemma nat_mult_dvd_cancel_disj[simp]:
  "(k*m) dvd (k*n) = (k=0 | m dvd (n::nat))"
by(auto simp: dvd_eq_mod_eq_0 mod_mult_distrib2[symmetric])

lemma nat_mult_dvd_cancel1: "0 < k \<Longrightarrow> (k*m) dvd (k*n::nat) = (m dvd n)"
by(auto)


subsubsection{*For @{text cancel_factor} *}

lemma nat_mult_le_cancel_disj: "(k*m <= k*n) = ((0::nat) < k --> m<=n)"
by auto

lemma nat_mult_less_cancel_disj: "(k*m < k*n) = ((0::nat) < k & m<n)"
by auto

lemma nat_mult_eq_cancel_disj: "(k*m = k*n) = (k = (0::nat) | m=n)"
by auto

lemma nat_mult_div_cancel_disj[simp]:
     "(k*m) div (k*n) = (if k = (0::nat) then 0 else m div n)"
by (simp add: nat_mult_div_cancel1)


use "Tools/numeral_simprocs.ML"

use "Tools/nat_numeral_simprocs.ML"

declaration {* 
  K (Lin_Arith.add_simps (@{thms neg_simps} @ [@{thm Suc_nat_number_of}, @{thm int_nat_number_of}])
  #> Lin_Arith.add_simps (@{thms ring_distribs} @ [@{thm Let_number_of}, @{thm Let_0}, @{thm Let_1},
     @{thm nat_0}, @{thm nat_1},
     @{thm add_nat_number_of}, @{thm diff_nat_number_of}, @{thm mult_nat_number_of},
     @{thm eq_nat_number_of}, @{thm less_nat_number_of}, @{thm le_number_of_eq_not_less},
     @{thm le_Suc_number_of}, @{thm le_number_of_Suc},
     @{thm less_Suc_number_of}, @{thm less_number_of_Suc},
     @{thm Suc_eq_number_of}, @{thm eq_number_of_Suc},
     @{thm mult_Suc}, @{thm mult_Suc_right},
     @{thm add_Suc}, @{thm add_Suc_right},
     @{thm eq_number_of_0}, @{thm eq_0_number_of}, @{thm less_0_number_of},
     @{thm of_int_number_of_eq}, @{thm of_nat_number_of_eq}, @{thm nat_number_of},
     @{thm if_True}, @{thm if_False}])
  #> Lin_Arith.add_simprocs (Numeral_Simprocs.assoc_fold_simproc
      :: Numeral_Simprocs.combine_numerals
      :: Numeral_Simprocs.cancel_numerals)
  #> Lin_Arith.add_simprocs (Nat_Numeral_Simprocs.combine_numerals :: Nat_Numeral_Simprocs.cancel_numerals))
*}

end

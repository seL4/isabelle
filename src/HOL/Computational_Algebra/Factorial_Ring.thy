(*  Title:      HOL/Computational_Algebra/Factorial_Ring.thy
    Author:     Manuel Eberl, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Factorial (semi)rings\<close>

theory Factorial_Ring
imports
  Main
  "HOL-Library.Multiset"
begin

subsection \<open>Irreducible and prime elements\<close>

context comm_semiring_1
begin

definition irreducible :: "'a \<Rightarrow> bool" where
  "irreducible p \<longleftrightarrow> p \<noteq> 0 \<and> \<not>p dvd 1 \<and> (\<forall>a b. p = a * b \<longrightarrow> a dvd 1 \<or> b dvd 1)"

lemma not_irreducible_zero [simp]: "\<not>irreducible 0"
  by (simp add: irreducible_def)

lemma irreducible_not_unit: "irreducible p \<Longrightarrow> \<not>p dvd 1"
  by (simp add: irreducible_def)

lemma not_irreducible_one [simp]: "\<not>irreducible 1"
  by (simp add: irreducible_def)

lemma irreducibleI:
  "p \<noteq> 0 \<Longrightarrow> \<not>p dvd 1 \<Longrightarrow> (\<And>a b. p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1) \<Longrightarrow> irreducible p"
  by (simp add: irreducible_def)

lemma irreducibleD: "irreducible p \<Longrightarrow> p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1"
  by (simp add: irreducible_def)

lemma irreducible_mono:
  assumes irr: "irreducible b" and "a dvd b" "\<not>a dvd 1"
  shows   "irreducible a"
proof (rule irreducibleI)
  fix c d assume "a = c * d"
  from assms obtain k where [simp]: "b = a * k" by auto
  from \<open>a = c * d\<close> have "b = c * d * k"
    by simp
  hence "c dvd 1 \<or> (d * k) dvd 1"
    using irreducibleD[OF irr, of c "d * k"] by (auto simp: mult.assoc)
  thus "c dvd 1 \<or> d dvd 1"
    by auto
qed (use assms in \<open>auto simp: irreducible_def\<close>)

definition prime_elem :: "'a \<Rightarrow> bool" where
  "prime_elem p \<longleftrightarrow> p \<noteq> 0 \<and> \<not>p dvd 1 \<and> (\<forall>a b. p dvd (a * b) \<longrightarrow> p dvd a \<or> p dvd b)"

lemma not_prime_elem_zero [simp]: "\<not>prime_elem 0"
  by (simp add: prime_elem_def)

lemma prime_elem_not_unit: "prime_elem p \<Longrightarrow> \<not>p dvd 1"
  by (simp add: prime_elem_def)

lemma prime_elemI:
    "p \<noteq> 0 \<Longrightarrow> \<not>p dvd 1 \<Longrightarrow> (\<And>a b. p dvd (a * b) \<Longrightarrow> p dvd a \<or> p dvd b) \<Longrightarrow> prime_elem p"
  by (simp add: prime_elem_def)

lemma prime_elem_dvd_multD:
    "prime_elem p \<Longrightarrow> p dvd (a * b) \<Longrightarrow> p dvd a \<or> p dvd b"
  by (simp add: prime_elem_def)

lemma prime_elem_dvd_mult_iff:
  "prime_elem p \<Longrightarrow> p dvd (a * b) \<longleftrightarrow> p dvd a \<or> p dvd b"
  by (auto simp: prime_elem_def)

lemma not_prime_elem_one [simp]:
  "\<not> prime_elem 1"
  by (auto dest: prime_elem_not_unit)

lemma prime_elem_not_zeroI:
  assumes "prime_elem p"
  shows "p \<noteq> 0"
  using assms by (auto intro: ccontr)

lemma prime_elem_dvd_power:
  "prime_elem p \<Longrightarrow> p dvd x ^ n \<Longrightarrow> p dvd x"
  by (induction n) (auto dest: prime_elem_dvd_multD intro: dvd_trans[of _ 1])

lemma prime_elem_dvd_power_iff:
  "prime_elem p \<Longrightarrow> n > 0 \<Longrightarrow> p dvd x ^ n \<longleftrightarrow> p dvd x"
  by (auto dest: prime_elem_dvd_power intro: dvd_trans)

lemma prime_elem_imp_nonzero [simp]:
  "ASSUMPTION (prime_elem x) \<Longrightarrow> x \<noteq> 0"
  unfolding ASSUMPTION_def by (rule prime_elem_not_zeroI)

lemma prime_elem_imp_not_one [simp]:
  "ASSUMPTION (prime_elem x) \<Longrightarrow> x \<noteq> 1"
  unfolding ASSUMPTION_def by auto

end


lemma (in normalization_semidom) irreducible_cong:
  assumes "normalize a = normalize b"
  shows   "irreducible a \<longleftrightarrow> irreducible b"
proof (cases "a = 0 \<or> a dvd 1")
  case True
  hence "\<not>irreducible a" by (auto simp: irreducible_def)
  from True have "normalize a = 0 \<or> normalize a dvd 1"
    by auto
  also note assms
  finally have "b = 0 \<or> b dvd 1" by simp
  hence "\<not>irreducible b" by (auto simp: irreducible_def)
  with \<open>\<not>irreducible a\<close> show ?thesis by simp
next
  case False
  hence b: "b \<noteq> 0" "\<not>is_unit b" using assms
    by (auto simp: is_unit_normalize[of b])
  show ?thesis
  proof
    assume "irreducible a"
    thus "irreducible b"
      by (rule irreducible_mono) (use assms False b in \<open>auto dest: associatedD2\<close>)
  next
    assume "irreducible b"
    thus "irreducible a"
      by (rule irreducible_mono) (use assms False b in \<open>auto dest: associatedD1\<close>)
  qed
qed

lemma (in normalization_semidom) associatedE1:
  assumes "normalize a = normalize b"
  obtains u where "is_unit u" "a = u * b"
proof (cases "a = 0")
  case [simp]: False
  from assms have [simp]: "b \<noteq> 0" by auto
  show ?thesis
  proof (rule that)
    show "is_unit (unit_factor a div unit_factor b)"
      by auto
    have "unit_factor a div unit_factor b * b = unit_factor a * (b div unit_factor b)"
      using \<open>b \<noteq> 0\<close> unit_div_commute unit_div_mult_swap unit_factor_is_unit by metis
    also have "b div unit_factor b = normalize b" by simp
    finally show "a = unit_factor a div unit_factor b * b"
      by (metis assms unit_factor_mult_normalize)
  qed
next
  case [simp]: True
  hence [simp]: "b = 0"
    using assms[symmetric] by auto
  show ?thesis
    by (intro that[of 1]) auto
qed

lemma (in normalization_semidom) associatedE2:
  assumes "normalize a = normalize b"
  obtains u where "is_unit u" "b = u * a"
proof -
  from assms have "normalize b = normalize a"
    by simp
  then obtain u where "is_unit u" "b = u * a"
    by (elim associatedE1)
  thus ?thesis using that by blast
qed
  

(* TODO Move *)
lemma (in normalization_semidom) normalize_power_normalize:
  "normalize (normalize x ^ n) = normalize (x ^ n)"
proof (induction n)
  case (Suc n)
  have "normalize (normalize x ^ Suc n) = normalize (x * normalize (normalize x ^ n))"
    by simp
  also note Suc.IH
  finally show ?case by simp
qed auto

context algebraic_semidom
begin

lemma prime_elem_imp_irreducible:
  assumes "prime_elem p"
  shows   "irreducible p"
proof (rule irreducibleI)
  fix a b
  assume p_eq: "p = a * b"
  with assms have nz: "a \<noteq> 0" "b \<noteq> 0" by auto
  from p_eq have "p dvd a * b" by simp
  with \<open>prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_elem_dvd_multD)
  with \<open>p = a * b\<close> have "a * b dvd 1 * b \<or> a * b dvd a * 1" by auto
  thus "a dvd 1 \<or> b dvd 1"
    by (simp only: dvd_times_left_cancel_iff[OF nz(1)] dvd_times_right_cancel_iff[OF nz(2)])
qed (insert assms, simp_all add: prime_elem_def)

lemma (in algebraic_semidom) unit_imp_no_irreducible_divisors:
  assumes "is_unit x" "irreducible p"
  shows   "\<not>p dvd x"
proof (rule notI)
  assume "p dvd x"
  with \<open>is_unit x\<close> have "is_unit p"
    by (auto intro: dvd_trans)
  with \<open>irreducible p\<close> show False
    by (simp add: irreducible_not_unit)
qed

lemma unit_imp_no_prime_divisors:
  assumes "is_unit x" "prime_elem p"
  shows   "\<not>p dvd x"
  using unit_imp_no_irreducible_divisors[OF assms(1) prime_elem_imp_irreducible[OF assms(2)]] .

lemma prime_elem_mono:
  assumes "prime_elem p" "\<not>q dvd 1" "q dvd p"
  shows   "prime_elem q"
proof -
  from \<open>q dvd p\<close> obtain r where r: "p = q * r" by (elim dvdE)
  hence "p dvd q * r" by simp
  with \<open>prime_elem p\<close> have "p dvd q \<or> p dvd r" by (rule prime_elem_dvd_multD)
  hence "p dvd q"
  proof
    assume "p dvd r"
    then obtain s where s: "r = p * s" by (elim dvdE)
    from r have "p * 1 = p * (q * s)" by (subst (asm) s) (simp add: mult_ac)
    with \<open>prime_elem p\<close> have "q dvd 1"
      by (subst (asm) mult_cancel_left) auto
    with \<open>\<not>q dvd 1\<close> show ?thesis by contradiction
  qed

  show ?thesis
  proof (rule prime_elemI)
    fix a b assume "q dvd (a * b)"
    with \<open>p dvd q\<close> have "p dvd (a * b)" by (rule dvd_trans)
    with \<open>prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_elem_dvd_multD)
    with \<open>q dvd p\<close> show "q dvd a \<or> q dvd b" by (blast intro: dvd_trans)
  qed (insert assms, auto)
qed

lemma irreducibleD':
  assumes "irreducible a" "b dvd a"
  shows   "a dvd b \<or> is_unit b"
proof -
  from assms obtain c where c: "a = b * c" by (elim dvdE)
  from irreducibleD[OF assms(1) this] have "is_unit b \<or> is_unit c" .
  thus ?thesis by (auto simp: c mult_unit_dvd_iff)
qed

lemma irreducibleI':
  assumes "a \<noteq> 0" "\<not>is_unit a" "\<And>b. b dvd a \<Longrightarrow> a dvd b \<or> is_unit b"
  shows   "irreducible a"
proof (rule irreducibleI)
  fix b c assume a_eq: "a = b * c"
  hence "a dvd b \<or> is_unit b" by (intro assms) simp_all
  thus "is_unit b \<or> is_unit c"
  proof
    assume "a dvd b"
    hence "b * c dvd b * 1" by (simp add: a_eq)
    moreover from \<open>a \<noteq> 0\<close> a_eq have "b \<noteq> 0" by auto
    ultimately show ?thesis by (subst (asm) dvd_times_left_cancel_iff) auto
  qed blast
qed (simp_all add: assms(1,2))

lemma irreducible_altdef:
  "irreducible x \<longleftrightarrow> x \<noteq> 0 \<and> \<not>is_unit x \<and> (\<forall>b. b dvd x \<longrightarrow> x dvd b \<or> is_unit b)"
  using irreducibleI'[of x] irreducibleD'[of x] irreducible_not_unit[of x] by auto

lemma prime_elem_multD:
  assumes "prime_elem (a * b)"
  shows "is_unit a \<or> is_unit b"
proof -
  from assms have "a \<noteq> 0" "b \<noteq> 0" by (auto dest!: prime_elem_not_zeroI)
  moreover from assms prime_elem_dvd_multD [of "a * b"] have "a * b dvd a \<or> a * b dvd b"
    by auto
  ultimately show ?thesis
    using dvd_times_left_cancel_iff [of a b 1]
      dvd_times_right_cancel_iff [of b a 1]
    by auto
qed

lemma prime_elemD2:
  assumes "prime_elem p" and "a dvd p" and "\<not> is_unit a"
  shows "p dvd a"
proof -
  from \<open>a dvd p\<close> obtain b where "p = a * b" ..
  with \<open>prime_elem p\<close> prime_elem_multD \<open>\<not> is_unit a\<close> have "is_unit b" by auto
  with \<open>p = a * b\<close> show ?thesis
    by (auto simp add: mult_unit_dvd_iff)
qed

lemma prime_elem_dvd_prod_msetE:
  assumes "prime_elem p"
  assumes dvd: "p dvd prod_mset A"
  obtains a where "a \<in># A" and "p dvd a"
proof -
  from dvd have "\<exists>a. a \<in># A \<and> p dvd a"
  proof (induct A)
    case empty then show ?case
    using \<open>prime_elem p\<close> by (simp add: prime_elem_not_unit)
  next
    case (add a A)
    then have "p dvd a * prod_mset A" by simp
    with \<open>prime_elem p\<close> consider (A) "p dvd prod_mset A" | (B) "p dvd a"
      by (blast dest: prime_elem_dvd_multD)
    then show ?case proof cases
      case B then show ?thesis by auto
    next
      case A
      with add.hyps obtain b where "b \<in># A" "p dvd b"
        by auto
      then show ?thesis by auto
    qed
  qed
  with that show thesis by blast

qed

context
begin

private lemma prime_elem_powerD:
  assumes "prime_elem (p ^ n)"
  shows   "prime_elem p \<and> n = 1"
proof (cases n)
  case (Suc m)
  note assms
  also from Suc have "p ^ n = p * p^m" by simp
  finally have "is_unit p \<or> is_unit (p^m)" by (rule prime_elem_multD)
  moreover from assms have "\<not>is_unit p" by (simp add: prime_elem_def is_unit_power_iff)
  ultimately have "is_unit (p ^ m)" by simp
  with \<open>\<not>is_unit p\<close> have "m = 0" by (simp add: is_unit_power_iff)
  with Suc assms show ?thesis by simp
qed (insert assms, simp_all)

lemma prime_elem_power_iff:
  "prime_elem (p ^ n) \<longleftrightarrow> prime_elem p \<and> n = 1"
  by (auto dest: prime_elem_powerD)

end

lemma irreducible_mult_unit_left:
  "is_unit a \<Longrightarrow> irreducible (a * p) \<longleftrightarrow> irreducible p"
  by (auto simp: irreducible_altdef mult.commute[of a] is_unit_mult_iff
        mult_unit_dvd_iff dvd_mult_unit_iff)

lemma prime_elem_mult_unit_left:
  "is_unit a \<Longrightarrow> prime_elem (a * p) \<longleftrightarrow> prime_elem p"
  by (auto simp: prime_elem_def mult.commute[of a] is_unit_mult_iff mult_unit_dvd_iff)

lemma prime_elem_dvd_cases:
  assumes pk: "p*k dvd m*n" and p: "prime_elem p"
  shows "(\<exists>x. k dvd x*n \<and> m = p*x) \<or> (\<exists>y. k dvd m*y \<and> n = p*y)"
proof -
  have "p dvd m*n" using dvd_mult_left pk by blast
  then consider "p dvd m" | "p dvd n"
    using p prime_elem_dvd_mult_iff by blast
  then show ?thesis
  proof cases
    case 1 then obtain a where "m = p * a" by (metis dvd_mult_div_cancel)
      then have "\<exists>x. k dvd x * n \<and> m = p * x"
        using p pk by (auto simp: mult.assoc)
    then show ?thesis ..
  next
    case 2 then obtain b where "n = p * b" by (metis dvd_mult_div_cancel)
    with p pk have "\<exists>y. k dvd m*y \<and> n = p*y"
      by (metis dvd_mult_right dvd_times_left_cancel_iff mult.left_commute mult_zero_left)
    then show ?thesis ..
  qed
qed

lemma prime_elem_power_dvd_prod:
  assumes pc: "p^c dvd m*n" and p: "prime_elem p"
  shows "\<exists>a b. a+b = c \<and> p^a dvd m \<and> p^b dvd n"
using pc
proof (induct c arbitrary: m n)
  case 0 show ?case by simp
next
  case (Suc c)
  consider x where "p^c dvd x*n" "m = p*x" | y where "p^c dvd m*y" "n = p*y"
    using prime_elem_dvd_cases [of _ "p^c", OF _ p] Suc.prems by force
  then show ?case
  proof cases
    case (1 x)
    with Suc.hyps[of x n] obtain a b where "a + b = c \<and> p ^ a dvd x \<and> p ^ b dvd n" by blast
    with 1 have "Suc a + b = Suc c \<and> p ^ Suc a dvd m \<and> p ^ b dvd n"
      by (auto intro: mult_dvd_mono)
    thus ?thesis by blast
  next
    case (2 y)
    with Suc.hyps[of m y] obtain a b where "a + b = c \<and> p ^ a dvd m \<and> p ^ b dvd y" by blast
    with 2 have "a + Suc b = Suc c \<and> p ^ a dvd m \<and> p ^ Suc b dvd n"
      by (auto intro: mult_dvd_mono)
    with Suc.hyps [of m y] show "\<exists>a b. a + b = Suc c \<and> p ^ a dvd m \<and> p ^ b dvd n"
      by blast
  qed
qed

lemma prime_elem_power_dvd_cases:
  assumes "p ^ c dvd m * n" and "a + b = Suc c" and "prime_elem p"
  shows "p ^ a dvd m \<or> p ^ b dvd n"
proof -
  from assms obtain r s
    where "r + s = c \<and> p ^ r dvd m \<and> p ^ s dvd n"
    by (blast dest: prime_elem_power_dvd_prod)
  moreover with assms have
    "a \<le> r \<or> b \<le> s" by arith
  ultimately show ?thesis by (auto intro: power_le_dvd)
qed

lemma prime_elem_not_unit' [simp]:
  "ASSUMPTION (prime_elem x) \<Longrightarrow> \<not>is_unit x"
  unfolding ASSUMPTION_def by (rule prime_elem_not_unit)

lemma prime_elem_dvd_power_iff:
  assumes "prime_elem p"
  shows "p dvd a ^ n \<longleftrightarrow> p dvd a \<and> n > 0"
  using assms by (induct n) (auto dest: prime_elem_not_unit prime_elem_dvd_multD)

lemma prime_power_dvd_multD:
  assumes "prime_elem p"
  assumes "p ^ n dvd a * b" and "n > 0" and "\<not> p dvd a"
  shows "p ^ n dvd b"
  using \<open>p ^ n dvd a * b\<close> and \<open>n > 0\<close>
proof (induct n arbitrary: b)
  case 0 then show ?case by simp
next
  case (Suc n) show ?case
  proof (cases "n = 0")
    case True with Suc \<open>prime_elem p\<close> \<open>\<not> p dvd a\<close> show ?thesis
      by (simp add: prime_elem_dvd_mult_iff)
  next
    case False then have "n > 0" by simp
    from \<open>prime_elem p\<close> have "p \<noteq> 0" by auto
    from Suc.prems have *: "p * p ^ n dvd a * b"
      by simp
    then have "p dvd a * b"
      by (rule dvd_mult_left)
    with Suc \<open>prime_elem p\<close> \<open>\<not> p dvd a\<close> have "p dvd b"
      by (simp add: prime_elem_dvd_mult_iff)
    moreover define c where "c = b div p"
    ultimately have b: "b = p * c" by simp
    with * have "p * p ^ n dvd p * (a * c)"
      by (simp add: ac_simps)
    with \<open>p \<noteq> 0\<close> have "p ^ n dvd a * c"
      by simp
    with Suc.hyps \<open>n > 0\<close> have "p ^ n dvd c"
      by blast
    with \<open>p \<noteq> 0\<close> show ?thesis
      by (simp add: b)
  qed
qed

end


subsection \<open>Generalized primes: normalized prime elements\<close>

context normalization_semidom
begin

lemma irreducible_normalized_divisors:
  assumes "irreducible x" "y dvd x" "normalize y = y"
  shows   "y = 1 \<or> y = normalize x"
proof -
  from assms have "is_unit y \<or> x dvd y" by (auto simp: irreducible_altdef)
  thus ?thesis
  proof (elim disjE)
    assume "is_unit y"
    hence "normalize y = 1" by (simp add: is_unit_normalize)
    with assms show ?thesis by simp
  next
    assume "x dvd y"
    with \<open>y dvd x\<close> have "normalize y = normalize x" by (rule associatedI)
    with assms show ?thesis by simp
  qed
qed

lemma irreducible_normalize_iff [simp]: "irreducible (normalize x) = irreducible x"
  using irreducible_mult_unit_left[of "1 div unit_factor x" x]
  by (cases "x = 0") (simp_all add: unit_div_commute)

lemma prime_elem_normalize_iff [simp]: "prime_elem (normalize x) = prime_elem x"
  using prime_elem_mult_unit_left[of "1 div unit_factor x" x]
  by (cases "x = 0") (simp_all add: unit_div_commute)

lemma prime_elem_associated:
  assumes "prime_elem p" and "prime_elem q" and "q dvd p"
  shows "normalize q = normalize p"
using \<open>q dvd p\<close> proof (rule associatedI)
  from \<open>prime_elem q\<close> have "\<not> is_unit q"
    by (auto simp add: prime_elem_not_unit)
  with \<open>prime_elem p\<close> \<open>q dvd p\<close> show "p dvd q"
    by (blast intro: prime_elemD2)
qed

definition prime :: "'a \<Rightarrow> bool" where
  "prime p \<longleftrightarrow> prime_elem p \<and> normalize p = p"

lemma not_prime_0 [simp]: "\<not>prime 0" by (simp add: prime_def)

lemma not_prime_unit: "is_unit x \<Longrightarrow> \<not>prime x"
  using prime_elem_not_unit[of x] by (auto simp add: prime_def)

lemma not_prime_1 [simp]: "\<not>prime 1" by (simp add: not_prime_unit)

lemma primeI: "prime_elem x \<Longrightarrow> normalize x = x \<Longrightarrow> prime x"
  by (simp add: prime_def)

lemma prime_imp_prime_elem [dest]: "prime p \<Longrightarrow> prime_elem p"
  by (simp add: prime_def)

lemma normalize_prime: "prime p \<Longrightarrow> normalize p = p"
  by (simp add: prime_def)

lemma prime_normalize_iff [simp]: "prime (normalize p) \<longleftrightarrow> prime_elem p"
  by (auto simp add: prime_def)

lemma prime_power_iff:
  "prime (p ^ n) \<longleftrightarrow> prime p \<and> n = 1"
  by (auto simp: prime_def prime_elem_power_iff)

lemma prime_imp_nonzero [simp]:
  "ASSUMPTION (prime x) \<Longrightarrow> x \<noteq> 0"
  unfolding ASSUMPTION_def prime_def by auto

lemma prime_imp_not_one [simp]:
  "ASSUMPTION (prime x) \<Longrightarrow> x \<noteq> 1"
  unfolding ASSUMPTION_def by auto

lemma prime_not_unit' [simp]:
  "ASSUMPTION (prime x) \<Longrightarrow> \<not>is_unit x"
  unfolding ASSUMPTION_def prime_def by auto

lemma prime_normalize' [simp]: "ASSUMPTION (prime x) \<Longrightarrow> normalize x = x"
  unfolding ASSUMPTION_def prime_def by simp

lemma unit_factor_prime: "prime x \<Longrightarrow> unit_factor x = 1"
  using unit_factor_normalize[of x] unfolding prime_def by auto

lemma unit_factor_prime' [simp]: "ASSUMPTION (prime x) \<Longrightarrow> unit_factor x = 1"
  unfolding ASSUMPTION_def by (rule unit_factor_prime)

lemma prime_imp_prime_elem' [simp]: "ASSUMPTION (prime x) \<Longrightarrow> prime_elem x"
  by (simp add: prime_def ASSUMPTION_def)

lemma prime_dvd_multD: "prime p \<Longrightarrow> p dvd a * b \<Longrightarrow> p dvd a \<or> p dvd b"
  by (intro prime_elem_dvd_multD) simp_all

lemma prime_dvd_mult_iff: "prime p \<Longrightarrow> p dvd a * b \<longleftrightarrow> p dvd a \<or> p dvd b"
  by (auto dest: prime_dvd_multD)

lemma prime_dvd_power:
  "prime p \<Longrightarrow> p dvd x ^ n \<Longrightarrow> p dvd x"
  by (auto dest!: prime_elem_dvd_power simp: prime_def)

lemma prime_dvd_power_iff:
  "prime p \<Longrightarrow> n > 0 \<Longrightarrow> p dvd x ^ n \<longleftrightarrow> p dvd x"
  by (subst prime_elem_dvd_power_iff) simp_all

lemma prime_dvd_prod_mset_iff: "prime p \<Longrightarrow> p dvd prod_mset A \<longleftrightarrow> (\<exists>x. x \<in># A \<and> p dvd x)"
  by (induction A) (simp_all add: prime_elem_dvd_mult_iff prime_imp_prime_elem, blast+)

lemma prime_dvd_prod_iff: "finite A \<Longrightarrow> prime p \<Longrightarrow> p dvd prod f A \<longleftrightarrow> (\<exists>x\<in>A. p dvd f x)"
  by (auto simp: prime_dvd_prod_mset_iff prod_unfold_prod_mset)

lemma primes_dvd_imp_eq:
  assumes "prime p" "prime q" "p dvd q"
  shows   "p = q"
proof -
  from assms have "irreducible q" by (simp add: prime_elem_imp_irreducible prime_def)
  from irreducibleD'[OF this \<open>p dvd q\<close>] assms have "q dvd p" by simp
  with \<open>p dvd q\<close> have "normalize p = normalize q" by (rule associatedI)
  with assms show "p = q" by simp
qed

lemma prime_dvd_prod_mset_primes_iff:
  assumes "prime p" "\<And>q. q \<in># A \<Longrightarrow> prime q"
  shows   "p dvd prod_mset A \<longleftrightarrow> p \<in># A"
proof -
  from assms(1) have "p dvd prod_mset A \<longleftrightarrow> (\<exists>x. x \<in># A \<and> p dvd x)" by (rule prime_dvd_prod_mset_iff)
  also from assms have "\<dots> \<longleftrightarrow> p \<in># A" by (auto dest: primes_dvd_imp_eq)
  finally show ?thesis .
qed

lemma prod_mset_primes_dvd_imp_subset:
  assumes "prod_mset A dvd prod_mset B" "\<And>p. p \<in># A \<Longrightarrow> prime p" "\<And>p. p \<in># B \<Longrightarrow> prime p"
  shows   "A \<subseteq># B"
using assms
proof (induction A arbitrary: B)
  case empty
  thus ?case by simp
next
  case (add p A B)
  hence p: "prime p" by simp
  define B' where "B' = B - {#p#}"
  from add.prems have "p dvd prod_mset B" by (simp add: dvd_mult_left)
  with add.prems have "p \<in># B"
    by (subst (asm) (2) prime_dvd_prod_mset_primes_iff) simp_all
  hence B: "B = B' + {#p#}" by (simp add: B'_def)
  from add.prems p have "A \<subseteq># B'" by (intro add.IH) (simp_all add: B)
  thus ?case by (simp add: B)
qed

lemma prod_mset_dvd_prod_mset_primes_iff:
  assumes "\<And>x. x \<in># A \<Longrightarrow> prime x" "\<And>x. x \<in># B \<Longrightarrow> prime x"
  shows   "prod_mset A dvd prod_mset B \<longleftrightarrow> A \<subseteq># B"
  using assms by (auto intro: prod_mset_subset_imp_dvd prod_mset_primes_dvd_imp_subset)

lemma is_unit_prod_mset_primes_iff:
  assumes "\<And>x. x \<in># A \<Longrightarrow> prime x"
  shows   "is_unit (prod_mset A) \<longleftrightarrow> A = {#}"
  by (auto simp add: is_unit_prod_mset_iff)
    (meson all_not_in_conv assms not_prime_unit set_mset_eq_empty_iff)

lemma prod_mset_primes_irreducible_imp_prime:
  assumes irred: "irreducible (prod_mset A)"
  assumes A: "\<And>x. x \<in># A \<Longrightarrow> prime x"
  assumes B: "\<And>x. x \<in># B \<Longrightarrow> prime x"
  assumes C: "\<And>x. x \<in># C \<Longrightarrow> prime x"
  assumes dvd: "prod_mset A dvd prod_mset B * prod_mset C"
  shows   "prod_mset A dvd prod_mset B \<or> prod_mset A dvd prod_mset C"
proof -
  from dvd have "prod_mset A dvd prod_mset (B + C)"
    by simp
  with A B C have subset: "A \<subseteq># B + C"
    by (subst (asm) prod_mset_dvd_prod_mset_primes_iff) auto
  define A1 and A2 where "A1 = A \<inter># B" and "A2 = A - A1"
  have "A = A1 + A2" unfolding A1_def A2_def
    by (rule sym, intro subset_mset.add_diff_inverse) simp_all
  from subset have "A1 \<subseteq># B" "A2 \<subseteq># C"
    by (auto simp: A1_def A2_def Multiset.subset_eq_diff_conv Multiset.union_commute)
  from \<open>A = A1 + A2\<close> have "prod_mset A = prod_mset A1 * prod_mset A2" by simp
  from irred and this have "is_unit (prod_mset A1) \<or> is_unit (prod_mset A2)"
    by (rule irreducibleD)
  with A have "A1 = {#} \<or> A2 = {#}" unfolding A1_def A2_def
    by (subst (asm) (1 2) is_unit_prod_mset_primes_iff) (auto dest: Multiset.in_diffD)
  with dvd \<open>A = A1 + A2\<close> \<open>A1 \<subseteq># B\<close> \<open>A2 \<subseteq># C\<close> show ?thesis
    by (auto intro: prod_mset_subset_imp_dvd)
qed

lemma prod_mset_primes_finite_divisor_powers:
  assumes A: "\<And>x. x \<in># A \<Longrightarrow> prime x"
  assumes B: "\<And>x. x \<in># B \<Longrightarrow> prime x"
  assumes "A \<noteq> {#}"
  shows   "finite {n. prod_mset A ^ n dvd prod_mset B}"
proof -
  from \<open>A \<noteq> {#}\<close> obtain x where x: "x \<in># A" by blast
  define m where "m = count B x"
  have "{n. prod_mset A ^ n dvd prod_mset B} \<subseteq> {..m}"
  proof safe
    fix n assume dvd: "prod_mset A ^ n dvd prod_mset B"
    from x have "x ^ n dvd prod_mset A ^ n" by (intro dvd_power_same dvd_prod_mset)
    also note dvd
    also have "x ^ n = prod_mset (replicate_mset n x)" by simp
    finally have "replicate_mset n x \<subseteq># B"
      by (rule prod_mset_primes_dvd_imp_subset) (insert A B x, simp_all split: if_splits)
    thus "n \<le> m" by (simp add: count_le_replicate_mset_subset_eq m_def)
  qed
  moreover have "finite {..m}" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

end


subsection \<open>In a semiring with GCD, each irreducible element is a prime element\<close>

context semiring_gcd
begin

lemma irreducible_imp_prime_elem_gcd:
  assumes "irreducible x"
  shows   "prime_elem x"
proof (rule prime_elemI)
  fix a b assume "x dvd a * b"
  from dvd_productE[OF this] obtain y z where yz: "x = y * z" "y dvd a" "z dvd b" .
  from \<open>irreducible x\<close> and \<open>x = y * z\<close> have "is_unit y \<or> is_unit z" by (rule irreducibleD)
  with yz show "x dvd a \<or> x dvd b"
    by (auto simp: mult_unit_dvd_iff mult_unit_dvd_iff')
qed (insert assms, auto simp: irreducible_not_unit)

lemma prime_elem_imp_coprime:
  assumes "prime_elem p" "\<not>p dvd n"
  shows   "coprime p n"
proof (rule coprimeI)
  fix d assume "d dvd p" "d dvd n"
  show "is_unit d"
  proof (rule ccontr)
    assume "\<not>is_unit d"
    from \<open>prime_elem p\<close> and \<open>d dvd p\<close> and this have "p dvd d"
      by (rule prime_elemD2)
    from this and \<open>d dvd n\<close> have "p dvd n" by (rule dvd_trans)
    with \<open>\<not>p dvd n\<close> show False by contradiction
  qed
qed

lemma prime_imp_coprime:
  assumes "prime p" "\<not>p dvd n"
  shows   "coprime p n"
  using assms by (simp add: prime_elem_imp_coprime)

lemma prime_elem_imp_power_coprime:
  "prime_elem p \<Longrightarrow> \<not> p dvd a \<Longrightarrow> coprime a (p ^ m)"
  by (cases "m > 0") (auto dest: prime_elem_imp_coprime simp add: ac_simps)

lemma prime_imp_power_coprime:
  "prime p \<Longrightarrow> \<not> p dvd a \<Longrightarrow> coprime a (p ^ m)"
  by (rule prime_elem_imp_power_coprime) simp_all

lemma prime_elem_divprod_pow:
  assumes p: "prime_elem p" and ab: "coprime a b" and pab: "p^n dvd a * b"
  shows   "p^n dvd a \<or> p^n dvd b"
  using assms
proof -
  from p have "\<not> is_unit p"
    by simp
  with ab p have "\<not> p dvd a \<or> \<not> p dvd b"
    using not_coprimeI by blast
  with p have "coprime (p ^ n) a \<or> coprime (p ^ n) b"
    by (auto dest: prime_elem_imp_power_coprime simp add: ac_simps)
  with pab show ?thesis
    by (auto simp add: coprime_dvd_mult_left_iff coprime_dvd_mult_right_iff)
qed

lemma primes_coprime:
  "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  using prime_imp_coprime primes_dvd_imp_eq by blast

end


subsection \<open>Factorial semirings: algebraic structures with unique prime factorizations\<close>

class factorial_semiring = normalization_semidom +
  assumes prime_factorization_exists:
    "x \<noteq> 0 \<Longrightarrow> \<exists>A. (\<forall>x. x \<in># A \<longrightarrow> prime_elem x) \<and> normalize (prod_mset A) = normalize x"

text \<open>Alternative characterization\<close>

lemma (in normalization_semidom) factorial_semiring_altI_aux:
  assumes finite_divisors: "\<And>x. x \<noteq> 0 \<Longrightarrow> finite {y. y dvd x \<and> normalize y = y}"
  assumes irreducible_imp_prime_elem: "\<And>x. irreducible x \<Longrightarrow> prime_elem x"
  assumes "x \<noteq> 0"
  shows   "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> prime_elem x) \<and> normalize (prod_mset A) = normalize x"
using \<open>x \<noteq> 0\<close>
proof (induction "card {b. b dvd x \<and> normalize b = b}" arbitrary: x rule: less_induct)
  case (less a)
  let ?fctrs = "\<lambda>a. {b. b dvd a \<and> normalize b = b}"
  show ?case
  proof (cases "is_unit a")
    case True
    thus ?thesis by (intro exI[of _ "{#}"]) (auto simp: is_unit_normalize)
  next
    case False
    show ?thesis
    proof (cases "\<exists>b. b dvd a \<and> \<not>is_unit b \<and> \<not>a dvd b")
      case False
      with \<open>\<not>is_unit a\<close> less.prems have "irreducible a" by (auto simp: irreducible_altdef)
      hence "prime_elem a" by (rule irreducible_imp_prime_elem)
      thus ?thesis by (intro exI[of _ "{#normalize a#}"]) auto
    next
      case True
      then guess b by (elim exE conjE) note b = this

      from b have "?fctrs b \<subseteq> ?fctrs a" by (auto intro: dvd_trans)
      moreover from b have "normalize a \<notin> ?fctrs b" "normalize a \<in> ?fctrs a" by simp_all
      hence "?fctrs b \<noteq> ?fctrs a" by blast
      ultimately have "?fctrs b \<subset> ?fctrs a" by (subst subset_not_subset_eq) blast
      with finite_divisors[OF \<open>a \<noteq> 0\<close>] have "card (?fctrs b) < card (?fctrs a)"
        by (rule psubset_card_mono)
      moreover from \<open>a \<noteq> 0\<close> b have "b \<noteq> 0" by auto
      ultimately have "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> prime_elem x) \<and> normalize (prod_mset A) = normalize b"
        by (intro less) auto
      then guess A .. note A = this

      define c where "c = a div b"
      from b have c: "a = b * c" by (simp add: c_def)
      from less.prems c have "c \<noteq> 0" by auto
      from b c have "?fctrs c \<subseteq> ?fctrs a" by (auto intro: dvd_trans)
      moreover have "normalize a \<notin> ?fctrs c"
      proof safe
        assume "normalize a dvd c"
        hence "b * c dvd 1 * c" by (simp add: c)
        hence "b dvd 1" by (subst (asm) dvd_times_right_cancel_iff) fact+
        with b show False by simp
      qed
      with \<open>normalize a \<in> ?fctrs a\<close> have "?fctrs a \<noteq> ?fctrs c" by blast
      ultimately have "?fctrs c \<subset> ?fctrs a" by (subst subset_not_subset_eq) blast
      with finite_divisors[OF \<open>a \<noteq> 0\<close>] have "card (?fctrs c) < card (?fctrs a)"
        by (rule psubset_card_mono)
      with \<open>c \<noteq> 0\<close> have "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> prime_elem x) \<and> normalize (prod_mset A) = normalize c"
        by (intro less) auto
      then guess B .. note B = this

      show ?thesis
      proof (rule exI[of _ "A + B"]; safe)
        have "normalize (prod_mset (A + B)) =
                normalize (normalize (prod_mset A) * normalize (prod_mset B))"
          by simp
        also have "\<dots> = normalize (b * c)"
          by (simp only: A B) auto
        also have "b * c = a"
          using c by simp
        finally show "normalize (prod_mset (A + B)) = normalize a" .
      next
      qed (use A B in auto)
    qed
  qed
qed

lemma factorial_semiring_altI:
  assumes finite_divisors: "\<And>x::'a. x \<noteq> 0 \<Longrightarrow> finite {y. y dvd x \<and> normalize y = y}"
  assumes irreducible_imp_prime: "\<And>x::'a. irreducible x \<Longrightarrow> prime_elem x"
  shows   "OFCLASS('a :: normalization_semidom, factorial_semiring_class)"
  by intro_classes (rule factorial_semiring_altI_aux[OF assms])

text \<open>Properties\<close>

context factorial_semiring
begin

lemma prime_factorization_exists':
  assumes "x \<noteq> 0"
  obtains A where "\<And>x. x \<in># A \<Longrightarrow> prime x" "normalize (prod_mset A) = normalize x"
proof -
  from prime_factorization_exists[OF assms] obtain A
    where A: "\<And>x. x \<in># A \<Longrightarrow> prime_elem x" "normalize (prod_mset A) = normalize x" by blast
  define A' where "A' = image_mset normalize A"
  have "normalize (prod_mset A') = normalize (prod_mset A)"
    by (simp add: A'_def normalize_prod_mset_normalize)
  also note A(2)
  finally have "normalize (prod_mset A') = normalize x" by simp
  moreover from A(1) have "\<forall>x. x \<in># A' \<longrightarrow> prime x" by (auto simp: prime_def A'_def)
  ultimately show ?thesis by (intro that[of A']) blast
qed

lemma irreducible_imp_prime_elem:
  assumes "irreducible x"
  shows   "prime_elem x"
proof (rule prime_elemI)
  fix a b assume dvd: "x dvd a * b"
  from assms have "x \<noteq> 0" by auto
  show "x dvd a \<or> x dvd b"
  proof (cases "a = 0 \<or> b = 0")
    case False
    hence "a \<noteq> 0" "b \<noteq> 0" by blast+
    note nz = \<open>x \<noteq> 0\<close> this
    from nz[THEN prime_factorization_exists'] guess A B C . note ABC = this

    have "irreducible (prod_mset A)"
      by (subst irreducible_cong[OF ABC(2)]) fact
    moreover have "normalize (prod_mset A) dvd
                     normalize (normalize (prod_mset B) * normalize (prod_mset C))"
      unfolding ABC using dvd by simp
    hence "prod_mset A dvd prod_mset B * prod_mset C"
      unfolding normalize_mult_normalize_left normalize_mult_normalize_right by simp
    ultimately have "prod_mset A dvd prod_mset B \<or> prod_mset A dvd prod_mset C"
      by (intro prod_mset_primes_irreducible_imp_prime) (use ABC in auto)
    hence "normalize (prod_mset A) dvd normalize (prod_mset B) \<or>
           normalize (prod_mset A) dvd normalize (prod_mset C)" by simp
    thus ?thesis unfolding ABC by simp
  qed auto
qed (insert assms, simp_all add: irreducible_def)

lemma finite_divisor_powers:
  assumes "y \<noteq> 0" "\<not>is_unit x"
  shows   "finite {n. x ^ n dvd y}"
proof (cases "x = 0")
  case True
  with assms have "{n. x ^ n dvd y} = {0}" by (auto simp: power_0_left)
  thus ?thesis by simp
next
  case False
  note nz = this \<open>y \<noteq> 0\<close>
  from nz[THEN prime_factorization_exists'] guess A B . note AB = this
  from AB assms have "A \<noteq> {#}" by (auto simp: normalize_1_iff)
  from AB(2,4) prod_mset_primes_finite_divisor_powers [of A B, OF AB(1,3) this]
    have "finite {n. prod_mset A ^ n dvd prod_mset B}" by simp
  also have "{n. prod_mset A ^ n dvd prod_mset B} =
             {n. normalize (normalize (prod_mset A) ^ n) dvd normalize (prod_mset B)}"
    unfolding normalize_power_normalize by simp
  also have "\<dots> = {n. x ^ n dvd y}"
    unfolding AB unfolding normalize_power_normalize by simp
  finally show ?thesis .
qed

lemma finite_prime_divisors:
  assumes "x \<noteq> 0"
  shows   "finite {p. prime p \<and> p dvd x}"
proof -
  from prime_factorization_exists'[OF assms] guess A . note A = this
  have "{p. prime p \<and> p dvd x} \<subseteq> set_mset A"
  proof safe
    fix p assume p: "prime p" and dvd: "p dvd x"
    from dvd have "p dvd normalize x" by simp
    also from A have "normalize x = normalize (prod_mset A)" by simp
    finally have "p dvd prod_mset A"
      by simp
    thus  "p \<in># A" using p A
      by (subst (asm) prime_dvd_prod_mset_primes_iff)
  qed
  moreover have "finite (set_mset A)" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma prime_elem_iff_irreducible: "prime_elem x \<longleftrightarrow> irreducible x"
  by (blast intro: irreducible_imp_prime_elem prime_elem_imp_irreducible)

lemma prime_divisor_exists:
  assumes "a \<noteq> 0" "\<not>is_unit a"
  shows   "\<exists>b. b dvd a \<and> prime b"
proof -
  from prime_factorization_exists'[OF assms(1)] guess A . note A = this
  moreover from A and assms have "A \<noteq> {#}" by auto
  then obtain x where "x \<in># A" by blast
  with A(1) have *: "x dvd normalize (prod_mset A)" "prime x"
    by (auto simp: dvd_prod_mset)
  hence "x dvd a" unfolding A by simp
  with * show ?thesis by blast
qed

lemma prime_divisors_induct [case_names zero unit factor]:
  assumes "P 0" "\<And>x. is_unit x \<Longrightarrow> P x" "\<And>p x. prime p \<Longrightarrow> P x \<Longrightarrow> P (p * x)"
  shows   "P x"
proof (cases "x = 0")
  case False
  from prime_factorization_exists'[OF this] guess A . note A = this
  from A obtain u where u: "is_unit u" "x = u * prod_mset A"
    by (elim associatedE2)

  from A(1) have "P (u * prod_mset A)"
  proof (induction A)
    case (add p A)
    from add.prems have "prime p" by simp
    moreover from add.prems have "P (u * prod_mset A)" by (intro add.IH) simp_all
    ultimately have "P (p * (u * prod_mset A))" by (rule assms(3))
    thus ?case by (simp add: mult_ac)
  qed (simp_all add: assms False u)
  with A u show ?thesis by simp
qed (simp_all add: assms(1))

lemma no_prime_divisors_imp_unit:
  assumes "a \<noteq> 0" "\<And>b. b dvd a \<Longrightarrow> normalize b = b \<Longrightarrow> \<not> prime_elem b"
  shows "is_unit a"
proof (rule ccontr)
  assume "\<not>is_unit a"
  from prime_divisor_exists[OF assms(1) this] guess b by (elim exE conjE)
  with assms(2)[of b] show False by (simp add: prime_def)
qed

lemma prime_divisorE:
  assumes "a \<noteq> 0" and "\<not> is_unit a"
  obtains p where "prime p" and "p dvd a"
  using assms no_prime_divisors_imp_unit unfolding prime_def by blast

definition multiplicity :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "multiplicity p x = (if finite {n. p ^ n dvd x} then Max {n. p ^ n dvd x} else 0)"

lemma multiplicity_dvd: "p ^ multiplicity p x dvd x"
proof (cases "finite {n. p ^ n dvd x}")
  case True
  hence "multiplicity p x = Max {n. p ^ n dvd x}"
    by (simp add: multiplicity_def)
  also have "\<dots> \<in> {n. p ^ n dvd x}"
    by (rule Max_in) (auto intro!: True exI[of _ "0::nat"])
  finally show ?thesis by simp
qed (simp add: multiplicity_def)

lemma multiplicity_dvd': "n \<le> multiplicity p x \<Longrightarrow> p ^ n dvd x"
  by (rule dvd_trans[OF le_imp_power_dvd multiplicity_dvd])

context
  fixes x p :: 'a
  assumes xp: "x \<noteq> 0" "\<not>is_unit p"
begin

lemma multiplicity_eq_Max: "multiplicity p x = Max {n. p ^ n dvd x}"
  using finite_divisor_powers[OF xp] by (simp add: multiplicity_def)

lemma multiplicity_geI:
  assumes "p ^ n dvd x"
  shows   "multiplicity p x \<ge> n"
proof -
  from assms have "n \<le> Max {n. p ^ n dvd x}"
    by (intro Max_ge finite_divisor_powers xp) simp_all
  thus ?thesis by (subst multiplicity_eq_Max)
qed

lemma multiplicity_lessI:
  assumes "\<not>p ^ n dvd x"
  shows   "multiplicity p x < n"
proof (rule ccontr)
  assume "\<not>(n > multiplicity p x)"
  hence "p ^ n dvd x" by (intro multiplicity_dvd') simp
  with assms show False by contradiction
qed

lemma power_dvd_iff_le_multiplicity:
  "p ^ n dvd x \<longleftrightarrow> n \<le> multiplicity p x"
  using multiplicity_geI[of n] multiplicity_lessI[of n] by (cases "p ^ n dvd x") auto

lemma multiplicity_eq_zero_iff:
  shows   "multiplicity p x = 0 \<longleftrightarrow> \<not>p dvd x"
  using power_dvd_iff_le_multiplicity[of 1] by auto

lemma multiplicity_gt_zero_iff:
  shows   "multiplicity p x > 0 \<longleftrightarrow> p dvd x"
  using power_dvd_iff_le_multiplicity[of 1] by auto

lemma multiplicity_decompose:
  "\<not>p dvd (x div p ^ multiplicity p x)"
proof
  assume *: "p dvd x div p ^ multiplicity p x"
  have "x = x div p ^ multiplicity p x * (p ^ multiplicity p x)"
    using multiplicity_dvd[of p x] by simp
  also from * have "x div p ^ multiplicity p x = (x div p ^ multiplicity p x div p) * p" by simp
  also have "x div p ^ multiplicity p x div p * p * p ^ multiplicity p x =
               x div p ^ multiplicity p x div p * p ^ Suc (multiplicity p x)"
    by (simp add: mult_assoc)
  also have "p ^ Suc (multiplicity p x) dvd \<dots>" by (rule dvd_triv_right)
  finally show False by (subst (asm) power_dvd_iff_le_multiplicity) simp
qed

lemma multiplicity_decompose':
  obtains y where "x = p ^ multiplicity p x * y" "\<not>p dvd y"
  using that[of "x div p ^ multiplicity p x"]
  by (simp add: multiplicity_decompose multiplicity_dvd)

end

lemma multiplicity_zero [simp]: "multiplicity p 0 = 0"
  by (simp add: multiplicity_def)

lemma prime_elem_multiplicity_eq_zero_iff:
  "prime_elem p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> multiplicity p x = 0 \<longleftrightarrow> \<not>p dvd x"
  by (rule multiplicity_eq_zero_iff) simp_all

lemma prime_multiplicity_other:
  assumes "prime p" "prime q" "p \<noteq> q"
  shows   "multiplicity p q = 0"
  using assms by (subst prime_elem_multiplicity_eq_zero_iff) (auto dest: primes_dvd_imp_eq)

lemma prime_multiplicity_gt_zero_iff:
  "prime_elem p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> multiplicity p x > 0 \<longleftrightarrow> p dvd x"
  by (rule multiplicity_gt_zero_iff) simp_all

lemma multiplicity_unit_left: "is_unit p \<Longrightarrow> multiplicity p x = 0"
  by (simp add: multiplicity_def is_unit_power_iff unit_imp_dvd)

lemma multiplicity_unit_right:
  assumes "is_unit x"
  shows   "multiplicity p x = 0"
proof (cases "is_unit p \<or> x = 0")
  case False
  with multiplicity_lessI[of x p 1] this assms
    show ?thesis by (auto dest: dvd_unit_imp_unit)
qed (auto simp: multiplicity_unit_left)

lemma multiplicity_one [simp]: "multiplicity p 1 = 0"
  by (rule multiplicity_unit_right) simp_all

lemma multiplicity_eqI:
  assumes "p ^ n dvd x" "\<not>p ^ Suc n dvd x"
  shows   "multiplicity p x = n"
proof -
  consider "x = 0" | "is_unit p" | "x \<noteq> 0" "\<not>is_unit p" by blast
  thus ?thesis
  proof cases
    assume xp: "x \<noteq> 0" "\<not>is_unit p"
    from xp assms(1) have "multiplicity p x \<ge> n" by (intro multiplicity_geI)
    moreover from assms(2) xp have "multiplicity p x < Suc n" by (intro multiplicity_lessI)
    ultimately show ?thesis by simp
  next
    assume "is_unit p"
    hence "is_unit (p ^ Suc n)" by (simp add: is_unit_power_iff del: power_Suc)
    hence "p ^ Suc n dvd x" by (rule unit_imp_dvd)
    with \<open>\<not>p ^ Suc n dvd x\<close> show ?thesis by contradiction
  qed (insert assms, simp_all)
qed


context
  fixes x p :: 'a
  assumes xp: "x \<noteq> 0" "\<not>is_unit p"
begin

lemma multiplicity_times_same:
  assumes "p \<noteq> 0"
  shows   "multiplicity p (p * x) = Suc (multiplicity p x)"
proof (rule multiplicity_eqI)
  show "p ^ Suc (multiplicity p x) dvd p * x"
    by (auto intro!: mult_dvd_mono multiplicity_dvd)
  from xp assms show "\<not> p ^ Suc (Suc (multiplicity p x)) dvd p * x"
    using power_dvd_iff_le_multiplicity[OF xp, of "Suc (multiplicity p x)"] by simp
qed

end

lemma multiplicity_same_power': "multiplicity p (p ^ n) = (if p = 0 \<or> is_unit p then 0 else n)"
proof -
  consider "p = 0" | "is_unit p" |"p \<noteq> 0" "\<not>is_unit p" by blast
  thus ?thesis
  proof cases
    assume "p \<noteq> 0" "\<not>is_unit p"
    thus ?thesis by (induction n) (simp_all add: multiplicity_times_same)
  qed (simp_all add: power_0_left multiplicity_unit_left)
qed

lemma multiplicity_same_power:
  "p \<noteq> 0 \<Longrightarrow> \<not>is_unit p \<Longrightarrow> multiplicity p (p ^ n) = n"
  by (simp add: multiplicity_same_power')

lemma multiplicity_prime_elem_times_other:
  assumes "prime_elem p" "\<not>p dvd q"
  shows   "multiplicity p (q * x) = multiplicity p x"
proof (cases "x = 0")
  case False
  show ?thesis
  proof (rule multiplicity_eqI)
    have "1 * p ^ multiplicity p x dvd q * x"
      by (intro mult_dvd_mono multiplicity_dvd) simp_all
    thus "p ^ multiplicity p x dvd q * x" by simp
  next
    define n where "n = multiplicity p x"
    from assms have "\<not>is_unit p" by simp
    from multiplicity_decompose'[OF False this] guess y . note y = this [folded n_def]
    from y have "p ^ Suc n dvd q * x \<longleftrightarrow> p ^ n * p dvd p ^ n * (q * y)" by (simp add: mult_ac)
    also from assms have "\<dots> \<longleftrightarrow> p dvd q * y" by simp
    also have "\<dots> \<longleftrightarrow> p dvd q \<or> p dvd y" by (rule prime_elem_dvd_mult_iff) fact+
    also from assms y have "\<dots> \<longleftrightarrow> False" by simp
    finally show "\<not>(p ^ Suc n dvd q * x)" by blast
  qed
qed simp_all

lemma multiplicity_self:
  assumes "p \<noteq> 0" "\<not>is_unit p"
  shows   "multiplicity p p = 1"
proof -
  from assms have "multiplicity p p = Max {n. p ^ n dvd p}"
    by (simp add: multiplicity_eq_Max)
  also from assms have "p ^ n dvd p \<longleftrightarrow> n \<le> 1" for n
    using dvd_power_iff[of p n 1] by auto
  hence "{n. p ^ n dvd p} = {..1}" by auto
  also have "\<dots> = {0,1}" by auto
  finally show ?thesis by simp
qed

lemma multiplicity_times_unit_left:
  assumes "is_unit c"
  shows   "multiplicity (c * p) x = multiplicity p x"
proof -
  from assms have "{n. (c * p) ^ n dvd x} = {n. p ^ n dvd x}"
    by (subst mult.commute) (simp add: mult_unit_dvd_iff power_mult_distrib is_unit_power_iff)
  thus ?thesis by (simp add: multiplicity_def)
qed

lemma multiplicity_times_unit_right:
  assumes "is_unit c"
  shows   "multiplicity p (c * x) = multiplicity p x"
proof -
  from assms have "{n. p ^ n dvd c * x} = {n. p ^ n dvd x}"
    by (subst mult.commute) (simp add: dvd_mult_unit_iff)
  thus ?thesis by (simp add: multiplicity_def)
qed

lemma multiplicity_normalize_left [simp]:
  "multiplicity (normalize p) x = multiplicity p x"
proof (cases "p = 0")
  case [simp]: False
  have "normalize p = (1 div unit_factor p) * p"
    by (simp add: unit_div_commute is_unit_unit_factor)
  also have "multiplicity \<dots> x = multiplicity p x"
    by (rule multiplicity_times_unit_left) (simp add: is_unit_unit_factor)
  finally show ?thesis .
qed simp_all

lemma multiplicity_normalize_right [simp]:
  "multiplicity p (normalize x) = multiplicity p x"
proof (cases "x = 0")
  case [simp]: False
  have "normalize x = (1 div unit_factor x) * x"
    by (simp add: unit_div_commute is_unit_unit_factor)
  also have "multiplicity p \<dots> = multiplicity p x"
    by (rule multiplicity_times_unit_right) (simp add: is_unit_unit_factor)
  finally show ?thesis .
qed simp_all

lemma multiplicity_prime [simp]: "prime_elem p \<Longrightarrow> multiplicity p p = 1"
  by (rule multiplicity_self) auto

lemma multiplicity_prime_power [simp]: "prime_elem p \<Longrightarrow> multiplicity p (p ^ n) = n"
  by (subst multiplicity_same_power') auto

lift_definition prime_factorization :: "'a \<Rightarrow> 'a multiset" is
  "\<lambda>x p. if prime p then multiplicity p x else 0"
  unfolding multiset_def
proof clarify
  fix x :: 'a
  show "finite {p. 0 < (if prime p then multiplicity p x else 0)}" (is "finite ?A")
  proof (cases "x = 0")
    case False
    from False have "?A \<subseteq> {p. prime p \<and> p dvd x}"
      by (auto simp: multiplicity_gt_zero_iff)
    moreover from False have "finite {p. prime p \<and> p dvd x}"
      by (rule finite_prime_divisors)
    ultimately show ?thesis by (rule finite_subset)
  qed simp_all
qed

abbreviation prime_factors :: "'a \<Rightarrow> 'a set" where
  "prime_factors a \<equiv> set_mset (prime_factorization a)"

lemma count_prime_factorization_nonprime:
  "\<not>prime p \<Longrightarrow> count (prime_factorization x) p = 0"
  by transfer simp

lemma count_prime_factorization_prime:
  "prime p \<Longrightarrow> count (prime_factorization x) p = multiplicity p x"
  by transfer simp

lemma count_prime_factorization:
  "count (prime_factorization x) p = (if prime p then multiplicity p x else 0)"
  by transfer simp

lemma dvd_imp_multiplicity_le:
  assumes "a dvd b" "b \<noteq> 0"
  shows   "multiplicity p a \<le> multiplicity p b"
proof (cases "is_unit p")
  case False
  with assms show ?thesis
    by (intro multiplicity_geI ) (auto intro: dvd_trans[OF multiplicity_dvd' assms(1)])
qed (insert assms, auto simp: multiplicity_unit_left)

lemma prime_power_inj:
  assumes "prime a" "a ^ m = a ^ n"
  shows   "m = n"
proof -
  have "multiplicity a (a ^ m) = multiplicity a (a ^ n)" by (simp only: assms)
  thus ?thesis using assms by (subst (asm) (1 2) multiplicity_prime_power) simp_all
qed

lemma prime_power_inj':
  assumes "prime p" "prime q"
  assumes "p ^ m = q ^ n" "m > 0" "n > 0"
  shows   "p = q" "m = n"
proof -
  from assms have "p ^ 1 dvd p ^ m" by (intro le_imp_power_dvd) simp
  also have "p ^ m = q ^ n" by fact
  finally have "p dvd q ^ n" by simp
  with assms have "p dvd q" using prime_dvd_power[of p q] by simp
  with assms show "p = q" by (simp add: primes_dvd_imp_eq)
  with assms show "m = n" by (simp add: prime_power_inj)
qed

lemma prime_power_eq_one_iff [simp]: "prime p \<Longrightarrow> p ^ n = 1 \<longleftrightarrow> n = 0"
  using prime_power_inj[of p n 0] by auto

lemma one_eq_prime_power_iff [simp]: "prime p \<Longrightarrow> 1 = p ^ n \<longleftrightarrow> n = 0"
  using prime_power_inj[of p 0 n] by auto

lemma prime_power_inj'':
  assumes "prime p" "prime q"
  shows   "p ^ m = q ^ n \<longleftrightarrow> (m = 0 \<and> n = 0) \<or> (p = q \<and> m = n)"
  using assms 
  by (cases "m = 0"; cases "n = 0")
     (auto dest: prime_power_inj'[OF assms])

lemma prime_factorization_0 [simp]: "prime_factorization 0 = {#}"
  by (simp add: multiset_eq_iff count_prime_factorization)

lemma prime_factorization_empty_iff:
  "prime_factorization x = {#} \<longleftrightarrow> x = 0 \<or> is_unit x"
proof
  assume *: "prime_factorization x = {#}"
  {
    assume x: "x \<noteq> 0" "\<not>is_unit x"
    {
      fix p assume p: "prime p"
      have "count (prime_factorization x) p = 0" by (simp add: *)
      also from p have "count (prime_factorization x) p = multiplicity p x"
        by (rule count_prime_factorization_prime)
      also from x p have "\<dots> = 0 \<longleftrightarrow> \<not>p dvd x" by (simp add: multiplicity_eq_zero_iff)
      finally have "\<not>p dvd x" .
    }
    with prime_divisor_exists[OF x] have False by blast
  }
  thus "x = 0 \<or> is_unit x" by blast
next
  assume "x = 0 \<or> is_unit x"
  thus "prime_factorization x = {#}"
  proof
    assume x: "is_unit x"
    {
      fix p assume p: "prime p"
      from p x have "multiplicity p x = 0"
        by (subst multiplicity_eq_zero_iff)
           (auto simp: multiplicity_eq_zero_iff dest: unit_imp_no_prime_divisors)
    }
    thus ?thesis by (simp add: multiset_eq_iff count_prime_factorization)
  qed simp_all
qed

lemma prime_factorization_unit:
  assumes "is_unit x"
  shows   "prime_factorization x = {#}"
proof (rule multiset_eqI)
  fix p :: 'a
  show "count (prime_factorization x) p = count {#} p"
  proof (cases "prime p")
    case True
    with assms have "multiplicity p x = 0"
      by (subst multiplicity_eq_zero_iff)
         (auto simp: multiplicity_eq_zero_iff dest: unit_imp_no_prime_divisors)
    with True show ?thesis by (simp add: count_prime_factorization_prime)
  qed (simp_all add: count_prime_factorization_nonprime)
qed

lemma prime_factorization_1 [simp]: "prime_factorization 1 = {#}"
  by (simp add: prime_factorization_unit)

lemma prime_factorization_times_prime:
  assumes "x \<noteq> 0" "prime p"
  shows   "prime_factorization (p * x) = {#p#} + prime_factorization x"
proof (rule multiset_eqI)
  fix q :: 'a
  consider "\<not>prime q" | "p = q" | "prime q" "p \<noteq> q" by blast
  thus "count (prime_factorization (p * x)) q = count ({#p#} + prime_factorization x) q"
  proof cases
    assume q: "prime q" "p \<noteq> q"
    with assms primes_dvd_imp_eq[of q p] have "\<not>q dvd p" by auto
    with q assms show ?thesis
      by (simp add: multiplicity_prime_elem_times_other count_prime_factorization)
  qed (insert assms, auto simp: count_prime_factorization multiplicity_times_same)
qed

lemma prod_mset_prime_factorization_weak:
  assumes "x \<noteq> 0"
  shows   "normalize (prod_mset (prime_factorization x)) = normalize x"
  using assms
proof (induction x rule: prime_divisors_induct)
  case (factor p x)
  have "normalize (prod_mset (prime_factorization (p * x))) =
          normalize (p * normalize (prod_mset (prime_factorization x)))"
    using factor.prems factor.hyps by (simp add: prime_factorization_times_prime)
  also have "normalize (prod_mset (prime_factorization x)) = normalize x"
    by (rule factor.IH) (use factor in auto)
  finally show ?case by simp
qed (auto simp: prime_factorization_unit is_unit_normalize)

lemma in_prime_factors_iff:
  "p \<in> prime_factors x \<longleftrightarrow> x \<noteq> 0 \<and> p dvd x \<and> prime p"
proof -
  have "p \<in> prime_factors x \<longleftrightarrow> count (prime_factorization x) p > 0" by simp
  also have "\<dots> \<longleftrightarrow> x \<noteq> 0 \<and> p dvd x \<and> prime p"
   by (subst count_prime_factorization, cases "x = 0")
      (auto simp: multiplicity_eq_zero_iff multiplicity_gt_zero_iff)
  finally show ?thesis .
qed

lemma in_prime_factors_imp_prime [intro]:
  "p \<in> prime_factors x \<Longrightarrow> prime p"
  by (simp add: in_prime_factors_iff)

lemma in_prime_factors_imp_dvd [dest]:
  "p \<in> prime_factors x \<Longrightarrow> p dvd x"
  by (simp add: in_prime_factors_iff)

lemma prime_factorsI:
  "x \<noteq> 0 \<Longrightarrow> prime p \<Longrightarrow> p dvd x \<Longrightarrow> p \<in> prime_factors x"
  by (auto simp: in_prime_factors_iff)

lemma prime_factors_dvd:
  "x \<noteq> 0 \<Longrightarrow> prime_factors x = {p. prime p \<and> p dvd x}"
  by (auto intro: prime_factorsI)

lemma prime_factors_multiplicity:
  "prime_factors n = {p. prime p \<and> multiplicity p n > 0}"
  by (cases "n = 0") (auto simp add: prime_factors_dvd prime_multiplicity_gt_zero_iff)

lemma prime_factorization_prime:
  assumes "prime p"
  shows   "prime_factorization p = {#p#}"
proof (rule multiset_eqI)
  fix q :: 'a
  consider "\<not>prime q" | "q = p" | "prime q" "q \<noteq> p" by blast
  thus "count (prime_factorization p) q = count {#p#} q"
    by cases (insert assms, auto dest: primes_dvd_imp_eq
                simp: count_prime_factorization multiplicity_self multiplicity_eq_zero_iff)
qed

lemma prime_factorization_prod_mset_primes:
  assumes "\<And>p. p \<in># A \<Longrightarrow> prime p"
  shows   "prime_factorization (prod_mset A) = A"
  using assms
proof (induction A)
  case (add p A)
  from add.prems[of 0] have "0 \<notin># A" by auto
  hence "prod_mset A \<noteq> 0" by auto
  with add show ?case
    by (simp_all add: mult_ac prime_factorization_times_prime Multiset.union_commute)
qed simp_all

lemma prime_factorization_cong:
  "normalize x = normalize y \<Longrightarrow> prime_factorization x = prime_factorization y"
  by (simp add: multiset_eq_iff count_prime_factorization
                multiplicity_normalize_right [of _ x, symmetric]
                multiplicity_normalize_right [of _ y, symmetric]
           del:  multiplicity_normalize_right)

lemma prime_factorization_unique:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization x = prime_factorization y \<longleftrightarrow> normalize x = normalize y"
proof
  assume "prime_factorization x = prime_factorization y"
  hence "prod_mset (prime_factorization x) = prod_mset (prime_factorization y)" by simp
  hence "normalize (prod_mset (prime_factorization x)) =
         normalize (prod_mset (prime_factorization y))"
    by (simp only: )
  with assms show "normalize x = normalize y"
    by (simp add: prod_mset_prime_factorization_weak)
qed (rule prime_factorization_cong)

lemma prime_factorization_normalize [simp]:
  "prime_factorization (normalize x) = prime_factorization x"
  by (cases "x = 0", simp, subst prime_factorization_unique) auto

lemma prime_factorization_eqI_strong:
  assumes "\<And>p. p \<in># P \<Longrightarrow> prime p" "prod_mset P = n"
  shows   "prime_factorization n = P"
  using prime_factorization_prod_mset_primes[of P] assms by simp

lemma prime_factorization_eqI:
  assumes "\<And>p. p \<in># P \<Longrightarrow> prime p" "normalize (prod_mset P) = normalize n"
  shows   "prime_factorization n = P"
proof -
  have "P = prime_factorization (normalize (prod_mset P))"
    using prime_factorization_prod_mset_primes[of P] assms(1) by simp
  with assms(2) show ?thesis by simp
qed

lemma prime_factorization_mult:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization (x * y) = prime_factorization x + prime_factorization y"
proof -
  have "normalize (prod_mset (prime_factorization x) * prod_mset (prime_factorization y)) =
          normalize (normalize (prod_mset (prime_factorization x)) *
                     normalize (prod_mset (prime_factorization y)))"
    by (simp only: normalize_mult_normalize_left normalize_mult_normalize_right)
  also have "\<dots> = normalize (x * y)"
    by (subst (1 2) prod_mset_prime_factorization_weak) (use assms in auto)
  finally show ?thesis
    by (intro prime_factorization_eqI) auto
qed

lemma prime_factorization_prod:
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "prime_factorization (prod f A) = (\<Sum>n\<in>A. prime_factorization (f n))"
  using assms by (induction A rule: finite_induct)
                 (auto simp: Sup_multiset_empty prime_factorization_mult)

lemma prime_elem_multiplicity_mult_distrib:
  assumes "prime_elem p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "multiplicity p (x * y) = multiplicity p x + multiplicity p y"
proof -
  have "multiplicity p (x * y) = count (prime_factorization (x * y)) (normalize p)"
    by (subst count_prime_factorization_prime) (simp_all add: assms)
  also from assms
    have "prime_factorization (x * y) = prime_factorization x + prime_factorization y"
      by (intro prime_factorization_mult)
  also have "count \<dots> (normalize p) =
    count (prime_factorization x) (normalize p) + count (prime_factorization y) (normalize p)"
    by simp
  also have "\<dots> = multiplicity p x + multiplicity p y"
    by (subst (1 2) count_prime_factorization_prime) (simp_all add: assms)
  finally show ?thesis .
qed

lemma prime_elem_multiplicity_prod_mset_distrib:
  assumes "prime_elem p" "0 \<notin># A"
  shows   "multiplicity p (prod_mset A) = sum_mset (image_mset (multiplicity p) A)"
  using assms by (induction A) (auto simp: prime_elem_multiplicity_mult_distrib)

lemma prime_elem_multiplicity_power_distrib:
  assumes "prime_elem p" "x \<noteq> 0"
  shows   "multiplicity p (x ^ n) = n * multiplicity p x"
  using assms prime_elem_multiplicity_prod_mset_distrib [of p "replicate_mset n x"]
  by simp

lemma prime_elem_multiplicity_prod_distrib:
  assumes "prime_elem p" "0 \<notin> f ` A" "finite A"
  shows   "multiplicity p (prod f A) = (\<Sum>x\<in>A. multiplicity p (f x))"
proof -
  have "multiplicity p (prod f A) = (\<Sum>x\<in>#mset_set A. multiplicity p (f x))"
    using assms by (subst prod_unfold_prod_mset)
                   (simp_all add: prime_elem_multiplicity_prod_mset_distrib sum_unfold_sum_mset
                      multiset.map_comp o_def)
  also from \<open>finite A\<close> have "\<dots> = (\<Sum>x\<in>A. multiplicity p (f x))"
    by (induction A rule: finite_induct) simp_all
  finally show ?thesis .
qed

lemma multiplicity_distinct_prime_power:
  "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> multiplicity p (q ^ n) = 0"
  by (subst prime_elem_multiplicity_power_distrib) (auto simp: prime_multiplicity_other)

lemma prime_factorization_prime_power:
  "prime p \<Longrightarrow> prime_factorization (p ^ n) = replicate_mset n p"
  by (induction n)
     (simp_all add: prime_factorization_mult prime_factorization_prime Multiset.union_commute)

lemma prime_factorization_subset_iff_dvd:
  assumes [simp]: "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization x \<subseteq># prime_factorization y \<longleftrightarrow> x dvd y"
proof -
  have "x dvd y \<longleftrightarrow>
    normalize (prod_mset (prime_factorization x)) dvd normalize (prod_mset (prime_factorization y))"
    using assms by (subst (1 2) prod_mset_prime_factorization_weak) auto
  also have "\<dots> \<longleftrightarrow> prime_factorization x \<subseteq># prime_factorization y"
    by (auto intro!: prod_mset_primes_dvd_imp_subset prod_mset_subset_imp_dvd)
  finally show ?thesis ..
qed

lemma prime_factorization_subset_imp_dvd:
  "x \<noteq> 0 \<Longrightarrow> (prime_factorization x \<subseteq># prime_factorization y) \<Longrightarrow> x dvd y"
  by (cases "y = 0") (simp_all add: prime_factorization_subset_iff_dvd)

lemma prime_factorization_divide:
  assumes "b dvd a"
  shows   "prime_factorization (a div b) = prime_factorization a - prime_factorization b"
proof (cases "a = 0")
  case [simp]: False
  from assms have [simp]: "b \<noteq> 0" by auto
  have "prime_factorization ((a div b) * b) = prime_factorization (a div b) + prime_factorization b"
    by (intro prime_factorization_mult) (insert assms, auto elim!: dvdE)
  with assms show ?thesis by simp
qed simp_all

lemma zero_not_in_prime_factors [simp]: "0 \<notin> prime_factors x"
  by (auto dest: in_prime_factors_imp_prime)

lemma prime_prime_factors:
  "prime p \<Longrightarrow> prime_factors p = {p}"
  by (drule prime_factorization_prime) simp

lemma prime_factors_product:
  "x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> prime_factors (x * y) = prime_factors x \<union> prime_factors y"
  by (simp add: prime_factorization_mult)

lemma dvd_prime_factors [intro]:
  "y \<noteq> 0 \<Longrightarrow> x dvd y \<Longrightarrow> prime_factors x \<subseteq> prime_factors y"
  by (intro set_mset_mono, subst prime_factorization_subset_iff_dvd) auto

(* RENAMED multiplicity_dvd *)
lemma multiplicity_le_imp_dvd:
  assumes "x \<noteq> 0" "\<And>p. prime p \<Longrightarrow> multiplicity p x \<le> multiplicity p y"
  shows   "x dvd y"
proof (cases "y = 0")
  case False
  from assms this have "prime_factorization x \<subseteq># prime_factorization y"
    by (intro mset_subset_eqI) (auto simp: count_prime_factorization)
  with assms False show ?thesis by (subst (asm) prime_factorization_subset_iff_dvd)
qed auto

lemma dvd_multiplicity_eq:
  "x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x dvd y \<longleftrightarrow> (\<forall>p. multiplicity p x \<le> multiplicity p y)"
  by (auto intro: dvd_imp_multiplicity_le multiplicity_le_imp_dvd)

lemma multiplicity_eq_imp_eq:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  assumes "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows   "normalize x = normalize y"
  using assms by (intro associatedI multiplicity_le_imp_dvd) simp_all

lemma prime_factorization_unique':
  assumes "\<forall>p \<in># M. prime p" "\<forall>p \<in># N. prime p" "(\<Prod>i \<in># M. i) = (\<Prod>i \<in># N. i)"
  shows   "M = N"
proof -
  have "prime_factorization (\<Prod>i \<in># M. i) = prime_factorization (\<Prod>i \<in># N. i)"
    by (simp only: assms)
  also from assms have "prime_factorization (\<Prod>i \<in># M. i) = M"
    by (subst prime_factorization_prod_mset_primes) simp_all
  also from assms have "prime_factorization (\<Prod>i \<in># N. i) = N"
    by (subst prime_factorization_prod_mset_primes) simp_all
  finally show ?thesis .
qed

lemma prime_factorization_unique'':
  assumes "\<forall>p \<in># M. prime p" "\<forall>p \<in># N. prime p" "normalize (\<Prod>i \<in># M. i) = normalize (\<Prod>i \<in># N. i)"
  shows   "M = N"
proof -
  have "prime_factorization (normalize (\<Prod>i \<in># M. i)) =
        prime_factorization (normalize (\<Prod>i \<in># N. i))"
    by (simp only: assms)
  also from assms have "prime_factorization (normalize (\<Prod>i \<in># M. i)) = M"
    by (subst prime_factorization_normalize, subst prime_factorization_prod_mset_primes) simp_all
  also from assms have "prime_factorization (normalize (\<Prod>i \<in># N. i)) = N"
    by (subst prime_factorization_normalize, subst prime_factorization_prod_mset_primes) simp_all
  finally show ?thesis .
qed

lemma multiplicity_cong:
  "(\<And>r. p ^ r dvd a \<longleftrightarrow> p ^ r dvd b) \<Longrightarrow> multiplicity p a = multiplicity p b"
  by (simp add: multiplicity_def)

lemma not_dvd_imp_multiplicity_0:
  assumes "\<not>p dvd x"
  shows   "multiplicity p x = 0"
proof -
  from assms have "multiplicity p x < 1"
    by (intro multiplicity_lessI) auto
  thus ?thesis by simp
qed

lemma multiplicity_zero_1 [simp]: "multiplicity 0 x = 0"
  by (metis (mono_tags) local.dvd_0_left multiplicity_zero not_dvd_imp_multiplicity_0)

lemma inj_on_Prod_primes:
  assumes "\<And>P p. P \<in> A \<Longrightarrow> p \<in> P \<Longrightarrow> prime p"
  assumes "\<And>P. P \<in> A \<Longrightarrow> finite P"
  shows   "inj_on Prod A"
proof (rule inj_onI)
  fix P Q assume PQ: "P \<in> A" "Q \<in> A" "\<Prod>P = \<Prod>Q"
  with prime_factorization_unique'[of "mset_set P" "mset_set Q"] assms[of P] assms[of Q]
    have "mset_set P = mset_set Q" by (auto simp: prod_unfold_prod_mset)
    with assms[of P] assms[of Q] PQ show "P = Q" by simp
qed

lemma divides_primepow_weak:
  assumes "prime p" and "a dvd p ^ n"
  obtains m where "m \<le> n" and "normalize a = normalize (p ^ m)"
proof -
  from assms have "a \<noteq> 0"
    by auto
  with assms
  have "normalize (prod_mset (prime_factorization a)) dvd
          normalize (prod_mset (prime_factorization (p ^ n)))"
    by (subst (1 2) prod_mset_prime_factorization_weak) auto
  then have "prime_factorization a \<subseteq># prime_factorization (p ^ n)"
    by (simp add: in_prime_factors_imp_prime prod_mset_dvd_prod_mset_primes_iff)
  with assms have "prime_factorization a \<subseteq># replicate_mset n p"
    by (simp add: prime_factorization_prime_power)
  then obtain m where "m \<le> n" and "prime_factorization a = replicate_mset m p"
    by (rule msubseteq_replicate_msetE)
  then have *: "normalize (prod_mset (prime_factorization a)) =
                  normalize (prod_mset (replicate_mset m p))" by metis
  also have "normalize (prod_mset (prime_factorization a)) = normalize a"
    using \<open>a \<noteq> 0\<close> by (simp add: prod_mset_prime_factorization_weak)
  also have "prod_mset (replicate_mset m p) = p ^ m"
    by simp
  finally show ?thesis using \<open>m \<le> n\<close> 
    by (intro that[of m])
qed

lemma divide_out_primepow_ex:
  assumes "n \<noteq> 0" "\<exists>p\<in>prime_factors n. P p"
  obtains p k n' where "P p" "prime p" "p dvd n" "\<not>p dvd n'" "k > 0" "n = p ^ k * n'"
proof -
  from assms obtain p where p: "P p" "prime p" "p dvd n"
    by auto
  define k where "k = multiplicity p n"
  define n' where "n' = n div p ^ k"
  have n': "n = p ^ k * n'" "\<not>p dvd n'"
    using assms p multiplicity_decompose[of n p]
    by (auto simp: n'_def k_def multiplicity_dvd)
  from n' p have "k > 0" by (intro Nat.gr0I) auto
  with n' p that[of p n' k] show ?thesis by auto
qed

lemma divide_out_primepow:
  assumes "n \<noteq> 0" "\<not>is_unit n"
  obtains p k n' where "prime p" "p dvd n" "\<not>p dvd n'" "k > 0" "n = p ^ k * n'"
  using divide_out_primepow_ex[OF assms(1), of "\<lambda>_. True"] prime_divisor_exists[OF assms] assms
        prime_factorsI by metis


subsection \<open>GCD and LCM computation with unique factorizations\<close>

definition "gcd_factorial a b = (if a = 0 then normalize b
     else if b = 0 then normalize a
     else normalize (prod_mset (prime_factorization a \<inter># prime_factorization b)))"

definition "lcm_factorial a b = (if a = 0 \<or> b = 0 then 0
     else normalize (prod_mset (prime_factorization a \<union># prime_factorization b)))"

definition "Gcd_factorial A =
  (if A \<subseteq> {0} then 0 else normalize (prod_mset (Inf (prime_factorization ` (A - {0})))))"

definition "Lcm_factorial A =
  (if A = {} then 1
   else if 0 \<notin> A \<and> subset_mset.bdd_above (prime_factorization ` (A - {0})) then
     normalize (prod_mset (Sup (prime_factorization ` A)))
   else
     0)"

lemma prime_factorization_gcd_factorial:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (gcd_factorial a b) = prime_factorization a \<inter># prime_factorization b"
proof -
  have "prime_factorization (gcd_factorial a b) =
          prime_factorization (prod_mset (prime_factorization a \<inter># prime_factorization b))"
    by (simp add: gcd_factorial_def)
  also have "\<dots> = prime_factorization a \<inter># prime_factorization b"
    by (subst prime_factorization_prod_mset_primes) auto
  finally show ?thesis .
qed

lemma prime_factorization_lcm_factorial:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (lcm_factorial a b) = prime_factorization a \<union># prime_factorization b"
proof -
  have "prime_factorization (lcm_factorial a b) =
          prime_factorization (prod_mset (prime_factorization a \<union># prime_factorization b))"
    by (simp add: lcm_factorial_def)
  also have "\<dots> = prime_factorization a \<union># prime_factorization b"
    by (subst prime_factorization_prod_mset_primes) auto
  finally show ?thesis .
qed

lemma prime_factorization_Gcd_factorial:
  assumes "\<not>A \<subseteq> {0}"
  shows   "prime_factorization (Gcd_factorial A) = Inf (prime_factorization ` (A - {0}))"
proof -
  from assms obtain x where x: "x \<in> A - {0}" by auto
  hence "Inf (prime_factorization ` (A - {0})) \<subseteq># prime_factorization x"
    by (intro subset_mset.cInf_lower) simp_all
  hence "\<forall>y. y \<in># Inf (prime_factorization ` (A - {0})) \<longrightarrow> y \<in> prime_factors x"
    by (auto dest: mset_subset_eqD)
  with in_prime_factors_imp_prime[of _ x]
    have "\<forall>p. p \<in># Inf (prime_factorization ` (A - {0})) \<longrightarrow> prime p" by blast
  with assms show ?thesis
    by (simp add: Gcd_factorial_def prime_factorization_prod_mset_primes)
qed

lemma prime_factorization_Lcm_factorial:
  assumes "0 \<notin> A" "subset_mset.bdd_above (prime_factorization ` A)"
  shows   "prime_factorization (Lcm_factorial A) = Sup (prime_factorization ` A)"
proof (cases "A = {}")
  case True
  hence "prime_factorization ` A = {}" by auto
  also have "Sup \<dots> = {#}" by (simp add: Sup_multiset_empty)
  finally show ?thesis by (simp add: Lcm_factorial_def)
next
  case False
  have "\<forall>y. y \<in># Sup (prime_factorization ` A) \<longrightarrow> prime y"
    by (auto simp: in_Sup_multiset_iff assms)
  with assms False show ?thesis
    by (simp add: Lcm_factorial_def prime_factorization_prod_mset_primes)
qed

lemma gcd_factorial_commute: "gcd_factorial a b = gcd_factorial b a"
  by (simp add: gcd_factorial_def multiset_inter_commute)

lemma gcd_factorial_dvd1: "gcd_factorial a b dvd a"
proof (cases "a = 0 \<or> b = 0")
  case False
  hence "gcd_factorial a b \<noteq> 0" by (auto simp: gcd_factorial_def)
  with False show ?thesis
    by (subst prime_factorization_subset_iff_dvd [symmetric])
       (auto simp: prime_factorization_gcd_factorial)
qed (auto simp: gcd_factorial_def)

lemma gcd_factorial_dvd2: "gcd_factorial a b dvd b"
  by (subst gcd_factorial_commute) (rule gcd_factorial_dvd1)

lemma normalize_gcd_factorial [simp]: "normalize (gcd_factorial a b) = gcd_factorial a b"
  by (simp add: gcd_factorial_def)

lemma normalize_lcm_factorial [simp]: "normalize (lcm_factorial a b) = lcm_factorial a b"
  by (simp add: lcm_factorial_def)

lemma gcd_factorial_greatest: "c dvd gcd_factorial a b" if "c dvd a" "c dvd b" for a b c
proof (cases "a = 0 \<or> b = 0")
  case False
  with that have [simp]: "c \<noteq> 0" by auto
  let ?p = "prime_factorization"
  from that False have "?p c \<subseteq># ?p a" "?p c \<subseteq># ?p b"
    by (simp_all add: prime_factorization_subset_iff_dvd)
  hence "prime_factorization c \<subseteq>#
           prime_factorization (prod_mset (prime_factorization a \<inter># prime_factorization b))"
    using False by (subst prime_factorization_prod_mset_primes) auto
  with False show ?thesis
    by (auto simp: gcd_factorial_def prime_factorization_subset_iff_dvd [symmetric])
qed (auto simp: gcd_factorial_def that)

lemma lcm_factorial_gcd_factorial:
  "lcm_factorial a b = normalize (a * b div gcd_factorial a b)" for a b
proof (cases "a = 0 \<or> b = 0")
  case False
  let ?p = "prime_factorization"
  have 1: "normalize x * normalize y dvd z \<longleftrightarrow> x * y dvd z" for x y z :: 'a
  proof -
    have "normalize (normalize x * normalize y) dvd z \<longleftrightarrow> x * y dvd z"
      unfolding normalize_mult_normalize_left normalize_mult_normalize_right by simp
    thus ?thesis unfolding normalize_dvd_iff by simp
  qed

  have "?p (a * b) = (?p a \<union># ?p b) + (?p a \<inter># ?p b)"
    using False by (subst prime_factorization_mult) (auto intro!: multiset_eqI)
  hence "normalize (prod_mset (?p (a * b))) =
           normalize (prod_mset ((?p a \<union># ?p b) + (?p a \<inter># ?p b)))"
    by (simp only:)
  hence *: "normalize (a * b) = normalize (lcm_factorial a b * gcd_factorial a b)" using False
    by (subst (asm) prod_mset_prime_factorization_weak)
       (auto simp: lcm_factorial_def gcd_factorial_def)

  have [simp]: "gcd_factorial a b dvd a * b" "lcm_factorial a b dvd a * b"
    using associatedD2[OF *] by auto
  from False have [simp]: "gcd_factorial a b \<noteq> 0" "lcm_factorial a b \<noteq> 0"
    by (auto simp: gcd_factorial_def lcm_factorial_def)
  
  show ?thesis
    by (rule associated_eqI)
       (use * in \<open>auto simp: dvd_div_iff_mult div_dvd_iff_mult dest: associatedD1 associatedD2\<close>)
qed (auto simp: lcm_factorial_def)

lemma normalize_Gcd_factorial:
  "normalize (Gcd_factorial A) = Gcd_factorial A"
  by (simp add: Gcd_factorial_def)

lemma Gcd_factorial_eq_0_iff:
  "Gcd_factorial A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  by (auto simp: Gcd_factorial_def in_Inf_multiset_iff split: if_splits)

lemma Gcd_factorial_dvd:
  assumes "x \<in> A"
  shows   "Gcd_factorial A dvd x"
proof (cases "x = 0")
  case False
  with assms have "prime_factorization (Gcd_factorial A) = Inf (prime_factorization ` (A - {0}))"
    by (intro prime_factorization_Gcd_factorial) auto
  also from False assms have "\<dots> \<subseteq># prime_factorization x"
    by (intro subset_mset.cInf_lower) auto
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert assms False, auto simp: Gcd_factorial_eq_0_iff)
qed simp_all

lemma Gcd_factorial_greatest:
  assumes "\<And>y. y \<in> A \<Longrightarrow> x dvd y"
  shows   "x dvd Gcd_factorial A"
proof (cases "A \<subseteq> {0}")
  case False
  from False obtain y where "y \<in> A" "y \<noteq> 0" by auto
  with assms[of y] have nz: "x \<noteq> 0" by auto
  from nz assms have "prime_factorization x \<subseteq># prime_factorization y" if "y \<in> A - {0}" for y
    using that by (subst prime_factorization_subset_iff_dvd) auto
  with False have "prime_factorization x \<subseteq># Inf (prime_factorization ` (A - {0}))"
    by (intro subset_mset.cInf_greatest) auto
  also from False have "\<dots> = prime_factorization (Gcd_factorial A)"
    by (rule prime_factorization_Gcd_factorial [symmetric])
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert nz False, auto simp: Gcd_factorial_eq_0_iff)
qed (simp_all add: Gcd_factorial_def)

lemma normalize_Lcm_factorial:
  "normalize (Lcm_factorial A) = Lcm_factorial A"
  by (simp add: Lcm_factorial_def)

lemma Lcm_factorial_eq_0_iff:
  "Lcm_factorial A = 0 \<longleftrightarrow> 0 \<in> A \<or> \<not>subset_mset.bdd_above (prime_factorization ` A)"
  by (auto simp: Lcm_factorial_def in_Sup_multiset_iff)

lemma dvd_Lcm_factorial:
  assumes "x \<in> A"
  shows   "x dvd Lcm_factorial A"
proof (cases "0 \<notin> A \<and> subset_mset.bdd_above (prime_factorization ` A)")
  case True
  with assms have [simp]: "0 \<notin> A" "x \<noteq> 0" "A \<noteq> {}" by auto
  from assms True have "prime_factorization x \<subseteq># Sup (prime_factorization ` A)"
    by (intro subset_mset.cSup_upper) auto
  also have "\<dots> = prime_factorization (Lcm_factorial A)"
    by (rule prime_factorization_Lcm_factorial [symmetric]) (insert True, simp_all)
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert True, auto simp: Lcm_factorial_eq_0_iff)
qed (insert assms, auto simp: Lcm_factorial_def)

lemma Lcm_factorial_least:
  assumes "\<And>y. y \<in> A \<Longrightarrow> y dvd x"
  shows   "Lcm_factorial A dvd x"
proof -
  consider "A = {}" | "0 \<in> A" | "x = 0" | "A \<noteq> {}" "0 \<notin> A" "x \<noteq> 0" by blast
  thus ?thesis
  proof cases
    assume *: "A \<noteq> {}" "0 \<notin> A" "x \<noteq> 0"
    hence nz: "x \<noteq> 0" if "x \<in> A" for x using that by auto
    from * have bdd: "subset_mset.bdd_above (prime_factorization ` A)"
      by (intro subset_mset.bdd_aboveI[of _ "prime_factorization x"])
         (auto simp: prime_factorization_subset_iff_dvd nz dest: assms)
    have "prime_factorization (Lcm_factorial A) = Sup (prime_factorization ` A)"
      by (rule prime_factorization_Lcm_factorial) fact+
    also from * have "\<dots> \<subseteq># prime_factorization x"
      by (intro subset_mset.cSup_least)
         (auto simp: prime_factorization_subset_iff_dvd nz dest: assms)
    finally show ?thesis
      by (subst (asm) prime_factorization_subset_iff_dvd)
         (insert * bdd, auto simp: Lcm_factorial_eq_0_iff)
  qed (auto simp: Lcm_factorial_def dest: assms)
qed

lemmas gcd_lcm_factorial =
  gcd_factorial_dvd1 gcd_factorial_dvd2 gcd_factorial_greatest
  normalize_gcd_factorial lcm_factorial_gcd_factorial
  normalize_Gcd_factorial Gcd_factorial_dvd Gcd_factorial_greatest
  normalize_Lcm_factorial dvd_Lcm_factorial Lcm_factorial_least

end

class factorial_semiring_gcd = factorial_semiring + gcd + Gcd +
  assumes gcd_eq_gcd_factorial: "gcd a b = gcd_factorial a b"
  and     lcm_eq_lcm_factorial: "lcm a b = lcm_factorial a b"
  and     Gcd_eq_Gcd_factorial: "Gcd A = Gcd_factorial A"
  and     Lcm_eq_Lcm_factorial: "Lcm A = Lcm_factorial A"
begin

lemma prime_factorization_gcd:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (gcd a b) = prime_factorization a \<inter># prime_factorization b"
  by (simp add: gcd_eq_gcd_factorial prime_factorization_gcd_factorial)

lemma prime_factorization_lcm:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (lcm a b) = prime_factorization a \<union># prime_factorization b"
  by (simp add: lcm_eq_lcm_factorial prime_factorization_lcm_factorial)

lemma prime_factorization_Gcd:
  assumes "Gcd A \<noteq> 0"
  shows   "prime_factorization (Gcd A) = Inf (prime_factorization ` (A - {0}))"
  using assms
  by (simp add: prime_factorization_Gcd_factorial Gcd_eq_Gcd_factorial Gcd_factorial_eq_0_iff)

lemma prime_factorization_Lcm:
  assumes "Lcm A \<noteq> 0"
  shows   "prime_factorization (Lcm A) = Sup (prime_factorization ` A)"
  using assms
  by (simp add: prime_factorization_Lcm_factorial Lcm_eq_Lcm_factorial Lcm_factorial_eq_0_iff)

lemma prime_factors_gcd [simp]: 
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> prime_factors (gcd a b) = 
     prime_factors a \<inter> prime_factors b"
  by (subst prime_factorization_gcd) auto

lemma prime_factors_lcm [simp]: 
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> prime_factors (lcm a b) = 
     prime_factors a \<union> prime_factors b"
  by (subst prime_factorization_lcm) auto

subclass semiring_gcd
  by (standard, unfold gcd_eq_gcd_factorial lcm_eq_lcm_factorial)
     (rule gcd_lcm_factorial; assumption)+

subclass semiring_Gcd
  by (standard, unfold Gcd_eq_Gcd_factorial Lcm_eq_Lcm_factorial)
     (rule gcd_lcm_factorial; assumption)+

lemma
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows gcd_eq_factorial':
          "gcd x y = normalize (\<Prod>p \<in> prime_factors x \<inter> prime_factors y.
                          p ^ min (multiplicity p x) (multiplicity p y))" (is "_ = ?rhs1")
    and lcm_eq_factorial':
          "lcm x y = normalize (\<Prod>p \<in> prime_factors x \<union> prime_factors y.
                          p ^ max (multiplicity p x) (multiplicity p y))" (is "_ = ?rhs2")
proof -
  have "gcd x y = gcd_factorial x y" by (rule gcd_eq_gcd_factorial)
  also have "\<dots> = ?rhs1"
    by (auto simp: gcd_factorial_def assms prod_mset_multiplicity
          count_prime_factorization_prime
          intro!: arg_cong[of _ _ normalize] dest: in_prime_factors_imp_prime intro!: prod.cong)
  finally show "gcd x y = ?rhs1" .
  have "lcm x y = lcm_factorial x y" by (rule lcm_eq_lcm_factorial)
  also have "\<dots> = ?rhs2"
    by (auto simp: lcm_factorial_def assms prod_mset_multiplicity
          count_prime_factorization_prime intro!: arg_cong[of _ _ normalize] 
          dest: in_prime_factors_imp_prime intro!: prod.cong)
  finally show "lcm x y = ?rhs2" .
qed

lemma
  assumes "x \<noteq> 0" "y \<noteq> 0" "prime p"
  shows   multiplicity_gcd: "multiplicity p (gcd x y) = min (multiplicity p x) (multiplicity p y)"
    and   multiplicity_lcm: "multiplicity p (lcm x y) = max (multiplicity p x) (multiplicity p y)"
proof -
  have "gcd x y = gcd_factorial x y" by (rule gcd_eq_gcd_factorial)
  also from assms have "multiplicity p \<dots> = min (multiplicity p x) (multiplicity p y)"
    by (simp add: count_prime_factorization_prime [symmetric] prime_factorization_gcd_factorial)
  finally show "multiplicity p (gcd x y) = min (multiplicity p x) (multiplicity p y)" .
  have "lcm x y = lcm_factorial x y" by (rule lcm_eq_lcm_factorial)
  also from assms have "multiplicity p \<dots> = max (multiplicity p x) (multiplicity p y)"
    by (simp add: count_prime_factorization_prime [symmetric] prime_factorization_lcm_factorial)
  finally show "multiplicity p (lcm x y) = max (multiplicity p x) (multiplicity p y)" .
qed

lemma gcd_lcm_distrib:
  "gcd x (lcm y z) = lcm (gcd x y) (gcd x z)"
proof (cases "x = 0 \<or> y = 0 \<or> z = 0")
  case True
  thus ?thesis
    by (auto simp: lcm_proj1_if_dvd lcm_proj2_if_dvd)
next
  case False
  hence "normalize (gcd x (lcm y z)) = normalize (lcm (gcd x y) (gcd x z))"
    by (intro associatedI prime_factorization_subset_imp_dvd)
       (auto simp: lcm_eq_0_iff prime_factorization_gcd prime_factorization_lcm
          subset_mset.inf_sup_distrib1)
  thus ?thesis by simp
qed

lemma lcm_gcd_distrib:
  "lcm x (gcd y z) = gcd (lcm x y) (lcm x z)"
proof (cases "x = 0 \<or> y = 0 \<or> z = 0")
  case True
  thus ?thesis
    by (auto simp: lcm_proj1_if_dvd lcm_proj2_if_dvd)
next
  case False
  hence "normalize (lcm x (gcd y z)) = normalize (gcd (lcm x y) (lcm x z))"
    by (intro associatedI prime_factorization_subset_imp_dvd)
       (auto simp: lcm_eq_0_iff prime_factorization_gcd prime_factorization_lcm
          subset_mset.sup_inf_distrib1)
  thus ?thesis by simp
qed

end

class factorial_ring_gcd = factorial_semiring_gcd + idom
begin

subclass ring_gcd ..

subclass idom_divide ..

end


class factorial_semiring_multiplicative =
  factorial_semiring + normalization_semidom_multiplicative
begin

lemma normalize_prod_mset_primes:
  "(\<And>p. p \<in># A \<Longrightarrow> prime p) \<Longrightarrow> normalize (prod_mset A) = prod_mset A"
proof (induction A)
  case (add p A)
  hence "prime p" by simp
  hence "normalize p = p" by simp
  with add show ?case by (simp add: normalize_mult)
qed simp_all

lemma prod_mset_prime_factorization:
  assumes "x \<noteq> 0"
  shows   "prod_mset (prime_factorization x) = normalize x"
  using assms
  by (induction x rule: prime_divisors_induct)
     (simp_all add: prime_factorization_unit prime_factorization_times_prime
                    is_unit_normalize normalize_mult)

lemma prime_decomposition: "unit_factor x * prod_mset (prime_factorization x) = x"
  by (cases "x = 0") (simp_all add: prod_mset_prime_factorization)

lemma prod_prime_factors:
  assumes "x \<noteq> 0"
  shows   "(\<Prod>p \<in> prime_factors x. p ^ multiplicity p x) = normalize x"
proof -
  have "normalize x = prod_mset (prime_factorization x)"
    by (simp add: prod_mset_prime_factorization assms)
  also have "\<dots> = (\<Prod>p \<in> prime_factors x. p ^ count (prime_factorization x) p)"
    by (subst prod_mset_multiplicity) simp_all
  also have "\<dots> = (\<Prod>p \<in> prime_factors x. p ^ multiplicity p x)"
    by (intro prod.cong)
      (simp_all add: assms count_prime_factorization_prime in_prime_factors_imp_prime)
  finally show ?thesis ..
qed

lemma prime_factorization_unique'':
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "normalize n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
proof
  define A where "A = Abs_multiset f"
  from \<open>finite S\<close> S(1) have "(\<Prod>p\<in>S. p ^ f p) \<noteq> 0" by auto
  with S(2) have nz: "n \<noteq> 0" by auto
  from S_eq \<open>finite S\<close> have count_A: "count A = f"
    unfolding A_def by (subst multiset.Abs_multiset_inverse) (simp_all add: multiset_def)
  from S_eq count_A have set_mset_A: "set_mset A = S"
    by (simp only: set_mset_def)
  from S(2) have "normalize n = (\<Prod>p\<in>S. p ^ f p)" .
  also have "\<dots> = prod_mset A" by (simp add: prod_mset_multiplicity S_eq set_mset_A count_A)
  also from nz have "normalize n = prod_mset (prime_factorization n)"
    by (simp add: prod_mset_prime_factorization)
  finally have "prime_factorization (prod_mset A) =
                  prime_factorization (prod_mset (prime_factorization n))" by simp
  also from S(1) have "prime_factorization (prod_mset A) = A"
    by (intro prime_factorization_prod_mset_primes) (auto simp: set_mset_A)
  also have "prime_factorization (prod_mset (prime_factorization n)) = prime_factorization n"
    by (intro prime_factorization_prod_mset_primes) auto
  finally show "S = prime_factors n" by (simp add: set_mset_A [symmetric])

  show "(\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
  proof safe
    fix p :: 'a assume p: "prime p"
    have "multiplicity p n = multiplicity p (normalize n)" by simp
    also have "normalize n = prod_mset A"
      by (simp add: prod_mset_multiplicity S_eq set_mset_A count_A S)
    also from p set_mset_A S(1)
    have "multiplicity p \<dots> = sum_mset (image_mset (multiplicity p) A)"
      by (intro prime_elem_multiplicity_prod_mset_distrib) auto
    also from S(1) p
    have "image_mset (multiplicity p) A = image_mset (\<lambda>q. if p = q then 1 else 0) A"
      by (intro image_mset_cong) (auto simp: set_mset_A multiplicity_self prime_multiplicity_other)
    also have "sum_mset \<dots> = f p"
      by (simp add: semiring_1_class.sum_mset_delta' count_A)
    finally show "f p = multiplicity p n" ..
  qed
qed

lemma divides_primepow:
  assumes "prime p" and "a dvd p ^ n"
  obtains m where "m \<le> n" and "normalize a = p ^ m"
  using divides_primepow_weak[OF assms] that assms
  by (auto simp add: normalize_power)

lemma Ex_other_prime_factor:
  assumes "n \<noteq> 0" and "\<not>(\<exists>k. normalize n = p ^ k)" "prime p"
  shows   "\<exists>q\<in>prime_factors n. q \<noteq> p"
proof (rule ccontr)
  assume *: "\<not>(\<exists>q\<in>prime_factors n. q \<noteq> p)"
  have "normalize n = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)"
    using assms(1) by (intro prod_prime_factors [symmetric]) auto
  also from * have "\<dots> = (\<Prod>p\<in>{p}. p ^ multiplicity p n)"
    using assms(3) by (intro prod.mono_neutral_left) (auto simp: prime_factors_multiplicity)
  finally have "normalize n = p ^ multiplicity p n" by auto
  with assms show False by auto
qed

end

end

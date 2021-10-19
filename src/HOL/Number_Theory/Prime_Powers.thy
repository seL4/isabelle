(*
  File:      HOL/Number_Theory/Prime_Powers.thy
  Author:    Manuel Eberl <manuel@pruvisto.org>

  Prime powers and the Mangoldt function
*)
section \<open>Prime powers\<close>
theory Prime_Powers
  imports Complex_Main "HOL-Computational_Algebra.Primes" "HOL-Library.FuncSet"
begin

definition aprimedivisor :: "'a :: normalization_semidom \<Rightarrow> 'a" where
  "aprimedivisor q = (SOME p. prime p \<and> p dvd q)"

definition primepow :: "'a :: normalization_semidom \<Rightarrow> bool" where
  "primepow n \<longleftrightarrow> (\<exists>p k. prime p \<and> k > 0 \<and> n = p ^ k)"

definition primepow_factors :: "'a :: normalization_semidom \<Rightarrow> 'a set" where
  "primepow_factors n = {x. primepow x \<and> x dvd n}"
  
lemma primepow_gt_Suc_0: "primepow n \<Longrightarrow> n > Suc 0"
  using one_less_power[of "p::nat" for p] by (auto simp: primepow_def prime_nat_iff)

lemma
  assumes "prime p" "p dvd n"
  shows prime_aprimedivisor: "prime (aprimedivisor n)" 
    and aprimedivisor_dvd:   "aprimedivisor n dvd n"
proof -
  from assms have "\<exists>p. prime p \<and> p dvd n" by auto
  from someI_ex[OF this] show "prime (aprimedivisor n)" "aprimedivisor n dvd n"
      unfolding aprimedivisor_def by (simp_all add: conj_commute)
qed    

lemma
  assumes "n \<noteq> 0" "\<not>is_unit (n :: 'a :: factorial_semiring)"
  shows prime_aprimedivisor': "prime (aprimedivisor n)" 
    and aprimedivisor_dvd':   "aprimedivisor n dvd n"
proof -
  from someI_ex[OF prime_divisor_exists[OF assms]] 
    show "prime (aprimedivisor n)" "aprimedivisor n dvd n"
      unfolding aprimedivisor_def by (simp_all add: conj_commute)
qed

lemma aprimedivisor_of_prime [simp]: 
  assumes "prime p"
  shows   "aprimedivisor p = p"
proof -
  from assms have "\<exists>q. prime q \<and> q dvd p" by auto
  from someI_ex[OF this, folded aprimedivisor_def] assms show ?thesis
    by (auto intro: primes_dvd_imp_eq)
qed

lemma aprimedivisor_pos_nat: "(n::nat) > 1 \<Longrightarrow> aprimedivisor n > 0"
  using aprimedivisor_dvd'[of n] by (auto elim: dvdE intro!: Nat.gr0I)

lemma aprimedivisor_primepow_power:
  assumes "primepow n" "k > 0"
  shows   "aprimedivisor (n ^ k) = aprimedivisor n"
proof -
  from assms obtain p l where l: "prime p" "l > 0" "n = p ^ l"
    by (auto simp: primepow_def)
  from l assms have *: "prime (aprimedivisor (n ^ k))" "aprimedivisor (n ^ k) dvd n ^ k"
    by (intro prime_aprimedivisor[of p] aprimedivisor_dvd[of p] dvd_power; 
        simp add: power_mult [symmetric])+
  from * l have "aprimedivisor (n ^ k) dvd p ^ (l * k)" by (simp add: power_mult)
  with assms * l have "aprimedivisor (n ^ k) dvd p" 
    by (subst (asm) prime_dvd_power_iff) simp_all
  with l assms have "aprimedivisor (n ^ k) = p"
    by (intro primes_dvd_imp_eq prime_aprimedivisor l) (auto simp: power_mult [symmetric])
  moreover from l have "aprimedivisor n dvd p ^ l" 
    by (auto intro: aprimedivisor_dvd simp: prime_gt_0_nat)
  with assms l have "aprimedivisor n dvd p"
    by (subst (asm) prime_dvd_power_iff) (auto intro!: prime_aprimedivisor simp: prime_gt_0_nat)
  with l assms have "aprimedivisor n = p"
    by (intro primes_dvd_imp_eq prime_aprimedivisor l) auto
  ultimately show ?thesis by simp
qed

lemma aprimedivisor_prime_power:
  assumes "prime p" "k > 0"
  shows   "aprimedivisor (p ^ k) = p"
proof -
  from assms have *: "prime (aprimedivisor (p ^ k))" "aprimedivisor (p ^ k) dvd p ^ k"
    by (intro prime_aprimedivisor[of p] aprimedivisor_dvd[of p]; simp add: prime_nat_iff)+
  from assms * have "aprimedivisor (p ^ k) dvd p" 
    by (subst (asm) prime_dvd_power_iff) simp_all
  with assms * show "aprimedivisor (p ^ k) = p" by (intro primes_dvd_imp_eq)
qed

lemma prime_factorization_primepow:
  assumes "primepow n"
  shows   "prime_factorization n = 
             replicate_mset (multiplicity (aprimedivisor n) n) (aprimedivisor n)"
  using assms
  by (auto simp: primepow_def aprimedivisor_prime_power prime_factorization_prime_power)

lemma primepow_decompose:
  fixes n :: "'a :: factorial_semiring_multiplicative"
  assumes "primepow n"
  shows   "aprimedivisor n ^ multiplicity (aprimedivisor n) n = n"
proof -
  from assms have "n \<noteq> 0" by (intro notI) (auto simp: primepow_def)
  hence "n = unit_factor n * prod_mset (prime_factorization n)"
    by (subst prod_mset_prime_factorization) simp_all
  also from assms have "unit_factor n = 1" by (auto simp: primepow_def unit_factor_power)
  also have "prime_factorization n = 
               replicate_mset (multiplicity (aprimedivisor n) n) (aprimedivisor n)"
    by (intro prime_factorization_primepow assms)
  also have "prod_mset \<dots> = aprimedivisor n ^ multiplicity (aprimedivisor n) n" by simp
  finally show ?thesis by simp
qed

lemma prime_power_not_one:
  assumes "prime p" "k > 0"
  shows   "p ^ k \<noteq> 1"
proof
  assume "p ^ k = 1"
  hence "is_unit (p ^ k)" by simp
  thus False using assms by (simp add: is_unit_power_iff)
qed

lemma zero_not_primepow [simp]: "\<not>primepow 0"
  by (auto simp: primepow_def)

lemma one_not_primepow [simp]: "\<not>primepow 1"
  by (auto simp: primepow_def prime_power_not_one)

lemma primepow_not_unit [simp]: "primepow p \<Longrightarrow> \<not>is_unit p"
  by (auto simp: primepow_def is_unit_power_iff)

lemma not_primepow_Suc_0_nat [simp]: "\<not>primepow (Suc 0)"
  using primepow_gt_Suc_0[of "Suc 0"] by auto

lemma primepow_gt_0_nat: "primepow n \<Longrightarrow> n > (0::nat)"
  using primepow_gt_Suc_0[of n] by simp

lemma unit_factor_primepow:
  fixes p :: "'a :: factorial_semiring_multiplicative"
  shows "primepow p \<Longrightarrow> unit_factor p = 1"
  by (auto simp: primepow_def unit_factor_power)

lemma aprimedivisor_primepow:
  assumes "prime p" "p dvd n" "primepow (n :: 'a :: factorial_semiring_multiplicative)"
  shows   "aprimedivisor (p * n) = p" "aprimedivisor n = p"
proof -
  from assms have [simp]: "n \<noteq> 0" by auto
  define q where "q = aprimedivisor n"
  with assms have q: "prime q" by (auto simp: q_def intro!: prime_aprimedivisor)
  from \<open>primepow n\<close> have n: "n = q ^ multiplicity q n" 
    by (simp add: primepow_decompose q_def)
  have nz: "multiplicity q n \<noteq> 0"
  proof
    assume "multiplicity q n = 0"
    with n have n': "n = unit_factor n" by simp
    have "is_unit n" by (subst n', rule unit_factor_is_unit) (insert assms, auto)
    with assms show False by auto
  qed
  with \<open>prime p\<close> \<open>p dvd n\<close> q have "p dvd q" 
    by (subst (asm) n) (auto intro: prime_dvd_power)
  with \<open>prime p\<close> q have "p = q" by (intro primes_dvd_imp_eq)
  thus "aprimedivisor n = p" by (simp add: q_def)

  define r where "r = aprimedivisor (p * n)"
  with assms have r: "r dvd (p * n)" "prime r" unfolding r_def
    by (intro aprimedivisor_dvd[of p] prime_aprimedivisor[of p]; simp)+
  hence "r dvd q ^ Suc (multiplicity q n)"
    by (subst (asm) n) (auto simp: \<open>p = q\<close> dest: dvd_unit_imp_unit)
  with r have "r dvd q" 
    by (auto intro: prime_dvd_power_nat simp: prime_dvd_mult_iff dest: prime_dvd_power)
  with r q have "r = q" by (intro primes_dvd_imp_eq)
  thus "aprimedivisor (p * n) = p" by (simp add: r_def \<open>p = q\<close>)
qed

lemma power_eq_prime_powerD:
  fixes p :: "'a :: factorial_semiring"
  assumes "prime p" "n > 0" "x ^ n = p ^ k"
  shows   "\<exists>i. normalize x = normalize (p ^ i)"
proof -
  have "normalize x = normalize (p ^ multiplicity p x)"
  proof (rule multiplicity_eq_imp_eq)
    fix q :: 'a assume "prime q"
    from assms have "multiplicity q (x ^ n) = multiplicity q (p ^ k)" by simp
    with \<open>prime q\<close> and assms have "n * multiplicity q x = k * multiplicity q p"
      by (subst (asm) (1 2) prime_elem_multiplicity_power_distrib) (auto simp: power_0_left)
    with assms and \<open>prime q\<close> show "multiplicity q x = multiplicity q (p ^ multiplicity p x)"
      by (cases "p = q") (auto simp: multiplicity_distinct_prime_power prime_multiplicity_other)
  qed (insert assms, auto simp: power_0_left)
  thus ?thesis by auto
qed
  

lemma primepow_power_iff:
  fixes p :: "'a :: factorial_semiring_multiplicative"
  assumes "unit_factor p = 1"
  shows   "primepow (p ^ n) \<longleftrightarrow> primepow p \<and> n > 0"
proof safe
  assume "primepow (p ^ n)"
  hence n: "n \<noteq> 0" by (auto intro!: Nat.gr0I)
  thus "n > 0" by simp
  from assms have [simp]: "normalize p = p"
    using normalize_mult_unit_factor[of p] by (simp only: mult.right_neutral)
  from \<open>primepow (p ^ n)\<close> obtain q k where *: "k > 0" "prime q" "p ^ n = q ^ k"
    by (auto simp: primepow_def)
  with power_eq_prime_powerD[of q n p k] n 
    obtain i where eq: "normalize p = normalize (q ^ i)" by auto
  with primepow_not_unit[OF \<open>primepow (p ^ n)\<close>] have "i \<noteq> 0" 
    by (intro notI) (simp add: normalize_1_iff is_unit_power_iff del: primepow_not_unit)
  with \<open>normalize p = normalize (q ^ i)\<close> \<open>prime q\<close> show "primepow p"
    by (auto simp: normalize_power primepow_def intro!: exI[of _ q] exI[of _ i])
next
  assume "primepow p" "n > 0"
  then obtain q k where *: "k > 0" "prime q" "p = q ^ k" by (auto simp: primepow_def)
  with \<open>n > 0\<close> show "primepow (p ^ n)"
    by (auto simp: primepow_def power_mult intro!: exI[of _ q] exI[of _ "k * n"])
qed

lemma primepow_power_iff_nat:
  "p > 0 \<Longrightarrow> primepow (p ^ n) \<longleftrightarrow> primepow (p :: nat) \<and> n > 0"
  by (rule primepow_power_iff) (simp_all add: unit_factor_nat_def)

lemma primepow_prime [simp]: "prime n \<Longrightarrow> primepow n"
  by (auto simp: primepow_def intro!: exI[of _ n] exI[of _ "1::nat"])

lemma primepow_prime_power [simp]: 
    "prime (p :: 'a :: factorial_semiring_multiplicative) \<Longrightarrow> primepow (p ^ n) \<longleftrightarrow> n > 0"
  by (subst primepow_power_iff) auto

lemma aprimedivisor_vimage:
  assumes "prime (p :: 'a :: factorial_semiring_multiplicative)"
  shows   "aprimedivisor -` {p} \<inter> primepow_factors n = {p ^ k |k. k > 0 \<and> p ^ k dvd n}"
proof safe
  fix q assume q: "q \<in> primepow_factors n"
  hence q': "q \<noteq> 0" "q \<noteq> 1" by (auto simp: primepow_def primepow_factors_def prime_power_not_one)
  let ?n = "multiplicity (aprimedivisor q) q"
  from q q' have "q = aprimedivisor q ^ ?n \<and> ?n > 0 \<and> aprimedivisor q ^ ?n dvd n"
    by (auto simp: primepow_decompose primepow_factors_def prime_multiplicity_gt_zero_iff
          prime_aprimedivisor' prime_imp_prime_elem aprimedivisor_dvd')
  thus "\<exists>k. q = aprimedivisor q ^ k \<and> k > 0 \<and> aprimedivisor q ^ k dvd n" ..
next
  fix k :: nat assume k: "p ^ k dvd n" "k > 0"
  with assms show "p ^ k \<in> aprimedivisor -` {p}"
    by (auto simp: aprimedivisor_prime_power)
  with assms k show "p ^ k \<in> primepow_factors n"
    by (auto simp: primepow_factors_def primepow_def aprimedivisor_prime_power intro: Suc_leI)
qed

lemma aprimedivisor_nat:
  assumes "n \<noteq> (Suc 0::nat)"
  shows   "prime (aprimedivisor n)" "aprimedivisor n dvd n"
proof -
  from assms have "\<exists>p. prime p \<and> p dvd n" by (intro prime_factor_nat) auto
  from someI_ex[OF this, folded aprimedivisor_def] 
    show "prime (aprimedivisor n)" "aprimedivisor n dvd n" by blast+
qed
  
lemma aprimedivisor_gt_Suc_0:
  assumes "n \<noteq> Suc 0"
  shows   "aprimedivisor n > Suc 0"
proof -
  from assms have "prime (aprimedivisor n)" by (rule aprimedivisor_nat)
  thus "aprimedivisor n > Suc 0" by (simp add: prime_nat_iff)
qed

lemma aprimedivisor_le_nat:
  assumes "n > Suc 0"
  shows   "aprimedivisor n \<le> n"
proof -
  from assms have "aprimedivisor n dvd n" by (intro aprimedivisor_nat) simp_all
  with assms show "aprimedivisor n \<le> n"
    by (intro dvd_imp_le) simp_all
qed

lemma bij_betw_primepows: 
  "bij_betw (\<lambda>(p,k). p ^ Suc k :: 'a :: factorial_semiring_multiplicative) 
     (Collect prime \<times> UNIV) (Collect primepow)"
proof (rule bij_betwI [where ?g = "(\<lambda>n. (aprimedivisor n, multiplicity (aprimedivisor n) n - 1))"], 
       goal_cases)
  case 1
  show "(\<lambda>(p, k). p ^ Suc k :: 'a) \<in> Collect prime \<times> UNIV \<rightarrow> Collect primepow"
    by (auto intro!: primepow_prime_power simp del: power_Suc )
next
  case 2
  show ?case
    by (auto simp: primepow_def prime_aprimedivisor)
next
  case (3 n)
  thus ?case
    by (auto simp: aprimedivisor_prime_power simp del: power_Suc)
next
  case (4 n)
  hence *: "0 < multiplicity (aprimedivisor n) n"
    by (subst prime_multiplicity_gt_zero_iff)
       (auto intro!: prime_imp_prime_elem aprimedivisor_dvd simp: primepow_def prime_aprimedivisor)
  have "aprimedivisor n * aprimedivisor n ^ (multiplicity (aprimedivisor n) n - Suc 0) =
          aprimedivisor n ^ Suc (multiplicity (aprimedivisor n) n - Suc 0)" by simp
  also from * have "Suc (multiplicity (aprimedivisor n) n - Suc 0) =
                      multiplicity (aprimedivisor n) n"
    by (subst Suc_diff_Suc) (auto simp: prime_multiplicity_gt_zero_iff)
  also have "aprimedivisor n ^ \<dots> = n"
    using 4 by (subst primepow_decompose) auto
  finally show ?case by auto
qed

(* TODO Generalise *)
lemma primepow_multD:
  assumes "primepow (a * b :: nat)"
  shows   "a = 1 \<or> primepow a" "b = 1 \<or> primepow b"
proof -
  from assms obtain p k where k: "k > 0" "a * b = p ^ k" "prime p"
    unfolding primepow_def by auto
  then obtain i j where "a = p ^ i" "b = p ^ j"
    using prime_power_mult_nat[of p a b] by blast
  with \<open>prime p\<close> show "a = 1 \<or> primepow a" "b = 1 \<or> primepow b" by auto
qed

lemma primepow_mult_aprimedivisorI:
  assumes "primepow (n :: 'a :: factorial_semiring_multiplicative)"
  shows   "primepow (aprimedivisor n * n)"
  by (subst (2) primepow_decompose[OF assms, symmetric], subst power_Suc [symmetric],
      subst primepow_prime_power) 
     (insert assms, auto intro!: prime_aprimedivisor' dest: primepow_gt_Suc_0)
 
lemma primepow_factors_altdef:
  fixes x :: "'a :: factorial_semiring_multiplicative"
  assumes "x \<noteq> 0"
  shows "primepow_factors x = {p ^ k |p k. p \<in> prime_factors x \<and> k \<in> {0<.. multiplicity p x}}"
proof (intro equalityI subsetI)
  fix q assume "q \<in> primepow_factors x"
  then obtain p k where pk: "prime p" "k > 0" "q = p ^ k" "q dvd x" 
    unfolding primepow_factors_def primepow_def by blast
  moreover have "k \<le> multiplicity p x" using pk assms by (intro multiplicity_geI) auto
  ultimately show "q \<in> {p ^ k |p k. p \<in> prime_factors x \<and> k \<in> {0<.. multiplicity p x}}"
    by (auto simp: prime_factors_multiplicity intro!: exI[of _ p] exI[of _ k])
qed (auto simp: primepow_factors_def prime_factors_multiplicity multiplicity_dvd')

lemma finite_primepow_factors:
  assumes "x \<noteq> (0 :: 'a :: factorial_semiring_multiplicative)"
  shows   "finite (primepow_factors x)"
proof -
  have "finite (SIGMA p:prime_factors x. {0<..multiplicity p x})"
    by (intro finite_SigmaI) simp_all
  hence "finite ((\<lambda>(p,k). p ^ k) ` \<dots>)" (is "finite ?A") by (rule finite_imageI)
  also have "?A = primepow_factors x"
    using assms by (subst primepow_factors_altdef) fast+
  finally show ?thesis .
qed

lemma aprimedivisor_primepow_factors_conv_prime_factorization:
  assumes [simp]: "n \<noteq> (0 :: 'a :: factorial_semiring_multiplicative)"
  shows   "image_mset aprimedivisor (mset_set (primepow_factors n)) = prime_factorization n" 
          (is "?lhs = ?rhs")
proof (intro multiset_eqI)
  fix p :: 'a
  show "count ?lhs p = count ?rhs p"
  proof (cases "prime p")
    case False
    have "p \<notin># image_mset aprimedivisor (mset_set (primepow_factors n))"
    proof
      assume "p \<in># image_mset aprimedivisor (mset_set (primepow_factors n))"
      then obtain q where "p = aprimedivisor q" "q \<in> primepow_factors n"
        by (auto simp: finite_primepow_factors)
      with False prime_aprimedivisor'[of q] have "q = 0 \<or> is_unit q" by auto
      with \<open>q \<in> primepow_factors n\<close> show False by (auto simp: primepow_factors_def primepow_def)
    qed
    hence "count ?lhs p = 0" by (simp only: Multiset.not_in_iff)
    with False show ?thesis by (simp add: count_prime_factorization)
  next
    case True
    hence p: "p \<noteq> 0" "\<not>is_unit p" by auto
    have "count ?lhs p = card (aprimedivisor -` {p} \<inter> primepow_factors n)"
      by (simp add: count_image_mset finite_primepow_factors)
    also have "aprimedivisor -` {p} \<inter> primepow_factors n = {p^k |k. k > 0 \<and> p ^ k dvd n}"
      using True by (rule aprimedivisor_vimage)
    also from True have "\<dots> = (\<lambda>k. p ^ k) ` {0<..multiplicity p n}"
      by (subst power_dvd_iff_le_multiplicity) auto
    also from p True have "card \<dots> = multiplicity p n"
      by (subst card_image) (auto intro!: inj_onI dest: prime_power_inj)
    also from True have "\<dots> = count (prime_factorization n) p" 
      by (simp add: count_prime_factorization)
    finally show ?thesis .
  qed
qed

lemma prime_elem_aprimedivisor_nat: "d > Suc 0 \<Longrightarrow> prime_elem (aprimedivisor d)"
  using prime_aprimedivisor'[of d] by simp

lemma aprimedivisor_gt_0_nat [simp]: "d > Suc 0 \<Longrightarrow> aprimedivisor d > 0"
  using prime_aprimedivisor'[of d] by (simp add: prime_gt_0_nat)

lemma aprimedivisor_gt_Suc_0_nat [simp]: "d > Suc 0 \<Longrightarrow> aprimedivisor d > Suc 0"
  using prime_aprimedivisor'[of d] by (simp add: prime_gt_Suc_0_nat)

lemma aprimedivisor_not_Suc_0_nat [simp]: "d > Suc 0 \<Longrightarrow> aprimedivisor d \<noteq> Suc 0"
  using aprimedivisor_gt_Suc_0[of d] by (intro notI) auto

lemma multiplicity_aprimedivisor_gt_0_nat [simp]:
  "d > Suc 0 \<Longrightarrow> multiplicity (aprimedivisor d) d > 0"
  by (subst multiplicity_gt_zero_iff) (auto intro: aprimedivisor_dvd')

lemma primepowI:
  "prime p \<Longrightarrow> k > 0 \<Longrightarrow> p ^ k = n \<Longrightarrow> primepow n \<and> aprimedivisor n = p"
  unfolding primepow_def by (auto simp: aprimedivisor_prime_power)

lemma not_primepowI:
  assumes "prime p" "prime q" "p \<noteq> q" "p dvd n" "q dvd n"
  shows   "\<not>primepow n"
  using assms by (auto simp: primepow_def dest!: prime_dvd_power[rotated] dest: primes_dvd_imp_eq)

lemma sum_prime_factorization_conv_sum_primepow_factors:
  fixes n :: "'a :: factorial_semiring_multiplicative"
  assumes "n \<noteq> 0"
  shows "(\<Sum>q\<in>primepow_factors n. f (aprimedivisor q)) = (\<Sum>p\<in>#prime_factorization n. f p)"
proof -
  from assms have "prime_factorization n = image_mset aprimedivisor (mset_set (primepow_factors n))"
    by (rule aprimedivisor_primepow_factors_conv_prime_factorization [symmetric])
  also have "(\<Sum>p\<in>#\<dots>. f p) = (\<Sum>q\<in>primepow_factors n. f (aprimedivisor q))"
    by (simp add: image_mset.compositionality sum_unfold_sum_mset o_def)
  finally show ?thesis ..
qed    

lemma multiplicity_aprimedivisor_Suc_0_iff:
  assumes "primepow (n :: 'a :: factorial_semiring_multiplicative)"
  shows   "multiplicity (aprimedivisor n) n = Suc 0 \<longleftrightarrow> prime n"
  by (subst (3) primepow_decompose [OF assms, symmetric])
     (insert assms, auto simp add: prime_power_iff intro!: prime_aprimedivisor')


definition mangoldt :: "nat \<Rightarrow> 'a :: real_algebra_1" where
  "mangoldt n = (if primepow n then of_real (ln (real (aprimedivisor n))) else 0)"

lemma mangoldt_0 [simp]: "mangoldt 0 = 0"
  by (simp add: mangoldt_def)

lemma mangoldt_Suc_0 [simp]: "mangoldt (Suc 0) = 0"
  by (simp add: mangoldt_def)

lemma of_real_mangoldt [simp]: "of_real (mangoldt n) = mangoldt n"
  by (simp add: mangoldt_def)

lemma mangoldt_sum:
  assumes "n \<noteq> 0"
  shows   "(\<Sum>d | d dvd n. mangoldt d :: 'a :: real_algebra_1) = of_real (ln (real n))"
proof -
  have "(\<Sum>d | d dvd n. mangoldt d :: 'a) = of_real (\<Sum>d | d dvd n. mangoldt d)" by simp
  also have "(\<Sum>d | d dvd n. mangoldt d) = (\<Sum>d \<in> primepow_factors n. ln (real (aprimedivisor d)))"
    using assms by (intro sum.mono_neutral_cong_right) (auto simp: primepow_factors_def mangoldt_def)
  also have "\<dots> = ln (real (\<Prod>d \<in> primepow_factors n. aprimedivisor d))"
    using assms finite_primepow_factors[of n]
    by (subst ln_prod [symmetric])
       (auto simp: primepow_factors_def intro!: aprimedivisor_pos_nat 
             intro: Nat.gr0I primepow_gt_Suc_0)
  also have "primepow_factors n = 
               (\<lambda>(p,k). p ^ k) ` (SIGMA p:prime_factors n. {0<..multiplicity p n})" 
    (is "_ = _ ` ?A") by (subst primepow_factors_altdef[OF assms]) fast+
  also have "prod aprimedivisor \<dots> = (\<Prod>(p,k)\<in>?A. aprimedivisor (p ^ k))"
    by (subst prod.reindex)
       (auto simp: inj_on_def prime_power_inj'' prime_factors_multiplicity 
                   prod.Sigma [symmetric] case_prod_unfold)
  also have "\<dots> = (\<Prod>(p,k)\<in>?A. p)" 
    by (intro prod.cong refl) (auto simp: aprimedivisor_prime_power prime_factors_multiplicity)
  also have "\<dots> = (\<Prod>x\<in>prime_factors n. \<Prod>k\<in>{0<..multiplicity x n}. x)"
    by (rule prod.Sigma [symmetric]) auto
  also have "\<dots> = (\<Prod>x\<in>prime_factors n. x ^ multiplicity x n)" 
    by (intro prod.cong refl) (simp add: prod_constant)
  also have "\<dots> = n" using assms by (intro prime_factorization_nat [symmetric]) simp
  finally show ?thesis .
qed

lemma mangoldt_primepow:
   "prime p \<Longrightarrow> mangoldt (p ^ k) = (if k > 0 then of_real (ln (real p)) else 0)"
  by (simp add: mangoldt_def aprimedivisor_prime_power)

lemma mangoldt_primepow' [simp]: "prime p \<Longrightarrow> k > 0 \<Longrightarrow> mangoldt (p ^ k) = of_real (ln (real p))"
  by (subst mangoldt_primepow) auto

lemma mangoldt_prime [simp]: "prime p \<Longrightarrow> mangoldt p = of_real (ln (real p))"    
  using mangoldt_primepow[of p 1] by simp

lemma mangoldt_nonneg: "0 \<le> (mangoldt d :: real)"
  using aprimedivisor_gt_Suc_0_nat[of d]
  by (auto simp: mangoldt_def of_nat_le_iff[of 1 x for x, unfolded of_nat_1] Suc_le_eq
           intro!: ln_ge_zero dest: primepow_gt_Suc_0)

lemma norm_mangoldt [simp]:
  "norm (mangoldt n :: 'a :: real_normed_algebra_1) = mangoldt n"
proof (cases "primepow n")
  case True
  hence "prime (aprimedivisor n)"
    by (intro prime_aprimedivisor') 
       (auto simp: primepow_def prime_gt_0_nat)
  hence "aprimedivisor n > 1" by (simp add: prime_gt_Suc_0_nat)
  with True show ?thesis by (auto simp: mangoldt_def abs_if)
qed (auto simp: mangoldt_def)

lemma Re_mangoldt [simp]: "Re (mangoldt n) = mangoldt n"
  and Im_mangoldt [simp]: "Im (mangoldt n) = 0"
  by (simp_all add: mangoldt_def)

lemma abs_mangoldt [simp]: "abs (mangoldt n :: real) = mangoldt n"
  using norm_mangoldt[of n, where ?'a = real, unfolded real_norm_def] .

lemma mangoldt_le: 
  assumes "n > 0"
  shows   "mangoldt n \<le> ln n"
proof (cases "primepow n")
  case True
  from True have "prime (aprimedivisor n)"
    by (intro prime_aprimedivisor') 
       (auto simp: primepow_def prime_gt_0_nat)
  hence gt_1: "aprimedivisor n > 1" by (simp add: prime_gt_Suc_0_nat)
  from True have "mangoldt n = ln (aprimedivisor n)"
    by (simp add: mangoldt_def)
  also have "\<dots> \<le> ln n" using True gt_1 
    by (subst ln_le_cancel_iff) (auto intro!: Nat.gr0I dvd_imp_le aprimedivisor_dvd')
  finally show ?thesis .
qed (insert assms, auto simp: mangoldt_def)

end

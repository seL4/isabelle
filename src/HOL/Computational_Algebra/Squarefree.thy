(*
  File:      HOL/Computational_Algebra/Squarefree.thy
  Author:    Manuel Eberl <manuel@pruvisto.org>

  Squarefreeness and decomposition of ring elements into square part and squarefree part
*)
section \<open>Squarefreeness\<close>
theory Squarefree
imports Primes
begin
  
(* TODO: Generalise to n-th powers *)

definition squarefree :: "'a :: comm_monoid_mult \<Rightarrow> bool" where
  "squarefree n \<longleftrightarrow> (\<forall>x. x ^ 2 dvd n \<longrightarrow> x dvd 1)"
  
lemma squarefreeI: "(\<And>x. x ^ 2 dvd n \<Longrightarrow> x dvd 1) \<Longrightarrow> squarefree n"
  by (auto simp: squarefree_def)

lemma squarefreeD: "squarefree n \<Longrightarrow> x ^ 2 dvd n \<Longrightarrow> x dvd 1"
  by (auto simp: squarefree_def)

lemma not_squarefreeI: "x ^ 2 dvd n \<Longrightarrow> \<not>x dvd 1 \<Longrightarrow> \<not>squarefree n"
  by (auto simp: squarefree_def)

lemma not_squarefreeE [case_names square_dvd]: 
  "\<not>squarefree n \<Longrightarrow> (\<And>x. x ^ 2 dvd n \<Longrightarrow> \<not>x dvd 1 \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: squarefree_def)

lemma not_squarefree_0 [simp]: "\<not>squarefree (0 :: 'a :: comm_semiring_1)"
  by (rule not_squarefreeI[of 0]) auto

lemma squarefree_factorial_semiring:
  assumes "n \<noteq> 0"
  shows   "squarefree (n :: 'a :: factorial_semiring) \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> \<not>p ^ 2 dvd n)"
  unfolding squarefree_def
proof safe
  assume *: "\<forall>p. prime p \<longrightarrow> \<not>p ^ 2 dvd n"
  fix x :: 'a assume x: "x ^ 2 dvd n"
  {
    assume "\<not>is_unit x"
    moreover from assms and x have "x \<noteq> 0" by auto
    ultimately obtain p where "p dvd x" "prime p"
      using prime_divisor_exists by blast
    with * have "\<not>p ^ 2 dvd n" by blast
    moreover from \<open>p dvd x\<close> have "p ^ 2 dvd x ^ 2" by (rule dvd_power_same)
    ultimately have "\<not>x ^ 2 dvd n" by (blast dest: dvd_trans)
    with x have False by contradiction
  }
  thus "is_unit x" by blast
qed auto

lemma squarefree_factorial_semiring':
  assumes "n \<noteq> 0"
  shows   "squarefree (n :: 'a :: factorial_semiring) \<longleftrightarrow> 
             (\<forall>p\<in>prime_factors n. multiplicity p n = 1)"
proof (subst squarefree_factorial_semiring [OF assms], safe)
  fix p assume "\<forall>p\<in>#prime_factorization n. multiplicity p n = 1" "prime p" "p^2 dvd n"
  with assms show False
    by (cases "p dvd n")
       (auto simp: prime_factors_dvd power_dvd_iff_le_multiplicity not_dvd_imp_multiplicity_0)
qed (auto intro!: multiplicity_eqI simp: power2_eq_square [symmetric])

lemma squarefree_factorial_semiring'':
  assumes "n \<noteq> 0"
  shows   "squarefree (n :: 'a :: factorial_semiring) \<longleftrightarrow> 
             (\<forall>p. prime p \<longrightarrow> multiplicity p n \<le> 1)"
  by (subst squarefree_factorial_semiring'[OF assms]) (auto simp: prime_factors_multiplicity)

lemma squarefree_unit [simp]: "is_unit n \<Longrightarrow> squarefree n"
proof (rule squarefreeI) 
  fix x assume "x^2 dvd n" "n dvd 1"
  hence "is_unit (x^2)" by (rule dvd_unit_imp_unit)
  thus "is_unit x" by (simp add: is_unit_power_iff)
qed

lemma squarefree_1 [simp]: "squarefree (1 :: 'a :: algebraic_semidom)"
  by simp

lemma squarefree_minus [simp]: "squarefree (-n :: 'a :: comm_ring_1) \<longleftrightarrow> squarefree n"
  by (simp add: squarefree_def)

lemma squarefree_mono: "a dvd b \<Longrightarrow> squarefree b \<Longrightarrow> squarefree a"
  by (auto simp: squarefree_def intro: dvd_trans)

lemma squarefree_multD:
  assumes "squarefree (a * b)"
  shows   "squarefree a" "squarefree b"
  by (rule squarefree_mono[OF _ assms], simp)+
    
lemma squarefree_prime_elem: 
  assumes "prime_elem (p :: 'a :: factorial_semiring)"
  shows   "squarefree p"
proof -
  from assms have "p \<noteq> 0" by auto
  show ?thesis
  proof (subst squarefree_factorial_semiring [OF \<open>p \<noteq> 0\<close>]; safe)
    fix q assume *: "prime q" "q^2 dvd p"
    with assms have "multiplicity q p \<ge> 2" by (intro multiplicity_geI) auto
    thus False using assms \<open>prime q\<close> prime_multiplicity_other[of q "normalize p"]
      by (cases "q = normalize p") simp_all
  qed
qed

lemma squarefree_prime: 
  assumes "prime (p :: 'a :: factorial_semiring)"
  shows   "squarefree p"
  using assms by (intro squarefree_prime_elem) auto

lemma squarefree_mult_coprime:
  fixes a b :: "'a :: factorial_semiring_gcd"
  assumes "coprime a b" "squarefree a" "squarefree b"
  shows   "squarefree (a * b)"
proof -
  from assms have nz: "a * b \<noteq> 0" by auto
  show ?thesis unfolding squarefree_factorial_semiring'[OF nz]
  proof
    fix p assume p: "p \<in> prime_factors (a * b)"
    with nz have "prime p"
      by (simp add: prime_factors_dvd)
    have "\<not> (p dvd a \<and> p dvd b)"
    proof
      assume "p dvd a \<and> p dvd b"
      with \<open>coprime a b\<close> have "is_unit p"
        by (auto intro: coprime_common_divisor)
      with \<open>prime p\<close> show False
        by simp
    qed
    moreover from p have "p dvd a \<or> p dvd b" using nz 
      by (auto simp: prime_factors_dvd prime_dvd_mult_iff)
    ultimately show "multiplicity p (a * b) = 1" using nz p assms(2,3)
      by (auto simp: prime_elem_multiplicity_mult_distrib prime_factors_multiplicity
            not_dvd_imp_multiplicity_0 squarefree_factorial_semiring')
  qed
qed

lemma squarefree_prod_coprime:
  fixes f :: "'a \<Rightarrow> 'b :: factorial_semiring_gcd"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> coprime (f a) (f b)"
  assumes "\<And>a. a \<in> A \<Longrightarrow> squarefree (f a)"
  shows   "squarefree (prod f A)"
  using assms 
  by (induction A rule: infinite_finite_induct) 
     (auto intro!: squarefree_mult_coprime prod_coprime_right)

lemma squarefree_powerD: "m > 0 \<Longrightarrow> squarefree (n ^ m) \<Longrightarrow> squarefree n"
  by (cases m) (auto dest: squarefree_multD)

lemma squarefree_power_iff: 
  "squarefree (n ^ m) \<longleftrightarrow> m = 0 \<or> is_unit n \<or> (squarefree n \<and> m = 1)"
proof safe
  assume "squarefree (n ^ m)" "m > 0" "\<not>is_unit n"
  show "m = 1"
  proof (rule ccontr)
    assume "m \<noteq> 1"
    with \<open>m > 0\<close> have "n ^ 2 dvd n ^ m" by (intro le_imp_power_dvd) auto
    from this and \<open>\<not>is_unit n\<close> have "\<not>squarefree (n ^ m)" by (rule not_squarefreeI)
    with \<open>squarefree (n ^ m)\<close> show False by contradiction
  qed
qed (auto simp: is_unit_power_iff dest: squarefree_powerD)

definition squarefree_nat :: "nat \<Rightarrow> bool" where
  [code_abbrev]: "squarefree_nat = squarefree"
  
lemma squarefree_nat_code_naive [code]: 
  "squarefree_nat n \<longleftrightarrow> n \<noteq> 0 \<and> (\<forall>k\<in>{2..n}. \<not>k ^ 2 dvd n)"
proof safe
  assume *: "\<forall>k\<in>{2..n}. \<not> k\<^sup>2 dvd n" and n: "n > 0"
  show "squarefree_nat n" unfolding squarefree_nat_def
  proof (rule squarefreeI)
    fix k assume k: "k ^ 2 dvd n"
    have "k dvd n" by (rule dvd_trans[OF _ k]) auto
    with n have "k \<le> n" by (intro dvd_imp_le)
    with bspec[OF *, of k] k have "\<not>k > 1" by (intro notI) auto
    moreover from k and n have "k \<noteq> 0" by (intro notI) auto
    ultimately have "k = 1" by presburger
    thus "is_unit k" by simp
  qed
qed (auto simp: squarefree_nat_def squarefree_def intro!: Nat.gr0I)



definition square_part :: "'a :: factorial_semiring \<Rightarrow> 'a" where
  "square_part n = (if n = 0 then 0 else 
     normalize (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n div 2)))"
  
lemma square_part_nonzero: 
  "n \<noteq> 0 \<Longrightarrow> square_part n = normalize (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n div 2))"
  by (simp add: square_part_def)
  
lemma square_part_0 [simp]: "square_part 0 = 0"
  by (simp add: square_part_def)

lemma square_part_unit [simp]: "is_unit x \<Longrightarrow> square_part x = 1"
  by (auto simp: square_part_def prime_factorization_unit)

lemma square_part_1 [simp]: "square_part 1 = 1"
  by simp
    
lemma square_part_0_iff [simp]: "square_part n = 0 \<longleftrightarrow> n = 0"
  by (simp add: square_part_def)

lemma normalize_uminus [simp]: 
  "normalize (-x :: 'a :: {normalization_semidom, comm_ring_1}) = normalize x"
  by (rule associatedI) auto

lemma multiplicity_uminus_right [simp]:
  "multiplicity (x :: 'a :: {factorial_semiring, comm_ring_1}) (-y) = multiplicity x y"
proof -
  have "multiplicity x (-y) = multiplicity x (normalize (-y))"
    by (rule multiplicity_normalize_right [symmetric])
  also have "\<dots> = multiplicity x y" by simp
  finally show ?thesis .
qed

lemma multiplicity_uminus_left [simp]:
  "multiplicity (-x :: 'a :: {factorial_semiring, comm_ring_1}) y = multiplicity x y"
proof -
  have "multiplicity (-x) y = multiplicity (normalize (-x)) y"
    by (rule multiplicity_normalize_left [symmetric])
  also have "\<dots> = multiplicity x y" by simp
  finally show ?thesis .
qed

lemma prime_factorization_uminus [simp]:
  "prime_factorization (-x :: 'a :: {factorial_semiring, comm_ring_1}) = prime_factorization x"
  by (rule prime_factorization_cong) simp_all

lemma square_part_uminus [simp]: 
    "square_part (-x :: 'a :: {factorial_semiring, comm_ring_1}) = square_part x"
  by (simp add: square_part_def)
  
lemma prime_multiplicity_square_part:
  assumes "prime p"
  shows   "multiplicity p (square_part n) = multiplicity p n div 2"
proof (cases "n = 0")
  case False
  thus ?thesis unfolding square_part_nonzero[OF False] multiplicity_normalize_right
    using finite_prime_divisors[of n] assms
    by (subst multiplicity_prod_prime_powers)
       (auto simp: not_dvd_imp_multiplicity_0 prime_factors_dvd multiplicity_prod_prime_powers)
qed auto

lemma square_part_square_dvd [simp, intro]: "square_part n ^ 2 dvd n"
proof (cases "n = 0")
  case False
  thus ?thesis
    by (intro multiplicity_le_imp_dvd) 
       (auto simp: prime_multiplicity_square_part prime_elem_multiplicity_power_distrib)
qed auto
  
lemma prime_multiplicity_le_imp_dvd:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows   "x dvd y \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> multiplicity p x \<le> multiplicity p y)"
  using assms by (auto intro: multiplicity_le_imp_dvd dvd_imp_multiplicity_le)

lemma dvd_square_part_iff: "x dvd square_part n \<longleftrightarrow> x ^ 2 dvd n"
proof (cases "x = 0"; cases "n = 0")
  assume nz: "x \<noteq> 0" "n \<noteq> 0"
  thus ?thesis
    by (subst (1 2) prime_multiplicity_le_imp_dvd)
       (auto simp: prime_multiplicity_square_part prime_elem_multiplicity_power_distrib)
qed auto


definition squarefree_part :: "'a :: factorial_semiring \<Rightarrow> 'a" where
  "squarefree_part n = (if n = 0 then 1 else n div square_part n ^ 2)"

lemma squarefree_part_0 [simp]: "squarefree_part 0 = 1"
  by (simp add: squarefree_part_def)

lemma squarefree_part_unit [simp]: "is_unit n \<Longrightarrow> squarefree_part n = n"
  by (auto simp add: squarefree_part_def)
  
lemma squarefree_part_1 [simp]: "squarefree_part 1 = 1"
  by simp
    
lemma squarefree_decompose: "n = squarefree_part n * square_part n ^ 2"
  by (simp add: squarefree_part_def)

lemma squarefree_part_uminus [simp]: 
  assumes "x \<noteq> 0"
  shows   "squarefree_part (-x :: 'a :: {factorial_semiring, comm_ring_1}) = -squarefree_part x"
proof -
  have "-(squarefree_part x * square_part x ^ 2) = -x" 
    by (subst squarefree_decompose [symmetric]) auto
  also have "\<dots> = squarefree_part (-x) * square_part (-x) ^ 2" by (rule squarefree_decompose)
  finally have "(- squarefree_part x) * square_part x ^ 2 = 
                  squarefree_part (-x) * square_part x ^ 2" by simp
  thus ?thesis using assms by (subst (asm) mult_right_cancel) auto
qed

lemma squarefree_part_nonzero [simp]: "squarefree_part n \<noteq> 0"
  using squarefree_decompose[of n] by (cases "n \<noteq> 0") auto    

lemma prime_multiplicity_squarefree_part:
  assumes "prime p"
  shows   "multiplicity p (squarefree_part n) = multiplicity p n mod 2"
proof (cases "n = 0")
  case False
  hence n: "n \<noteq> 0" by auto
  have "multiplicity p n mod 2 + 2 * (multiplicity p n div 2) = multiplicity p n" by simp
  also have "\<dots> = multiplicity p (squarefree_part n * square_part n ^ 2)"
    by (subst squarefree_decompose[of n]) simp
  also from assms n have "\<dots> = multiplicity p (squarefree_part n) + 2 * (multiplicity p n div 2)"
    by (subst prime_elem_multiplicity_mult_distrib) 
       (auto simp: prime_elem_multiplicity_power_distrib prime_multiplicity_square_part)
  finally show ?thesis by (subst (asm) add_right_cancel) simp
qed auto
  
lemma prime_multiplicity_squarefree_part_le_Suc_0 [intro]:
  assumes "prime p"
  shows   "multiplicity p (squarefree_part n) \<le> Suc 0"
  by (simp add: assms prime_multiplicity_squarefree_part)

lemma squarefree_squarefree_part [simp, intro]: "squarefree (squarefree_part n)"
  by (subst squarefree_factorial_semiring'')
     (auto simp: prime_multiplicity_squarefree_part_le_Suc_0)
  
lemma squarefree_decomposition_unique:
  assumes "square_part m = square_part n"
  assumes "squarefree_part m = squarefree_part n"
  shows   "m = n"
  by (subst (1 2) squarefree_decompose) (simp_all add: assms)
    
lemma normalize_square_part [simp]: "normalize (square_part x) = square_part x"
  by (simp add: square_part_def)

lemma square_part_even_power': "square_part (x ^ (2 * n)) = normalize (x ^ n)"
proof (cases "x = 0")
  case False
  have "normalize (square_part (x ^ (2 * n))) = normalize (x ^ n)" using False
    by (intro multiplicity_eq_imp_eq)
       (auto simp: prime_multiplicity_square_part prime_elem_multiplicity_power_distrib)
  thus ?thesis by simp
qed (auto simp: power_0_left)

lemma square_part_even_power: "even n \<Longrightarrow> square_part (x ^ n) = normalize (x ^ (n div 2))"
  by (subst square_part_even_power' [symmetric]) auto

lemma square_part_odd_power': "square_part (x ^ (Suc (2 * n))) = normalize (x ^ n * square_part x)"
proof (cases "x = 0")
  case False
  have "normalize (square_part (x ^ (Suc (2 * n)))) = normalize (square_part x * x ^ n)" 
  proof (rule multiplicity_eq_imp_eq, goal_cases)
    case (3 p)
    hence "multiplicity p (square_part (x ^ Suc (2 * n))) = 
             (2 * (n * multiplicity p x) + multiplicity p x) div 2"
      by (subst prime_multiplicity_square_part)
         (auto simp: False prime_elem_multiplicity_power_distrib algebra_simps simp del: power_Suc)
    also from 3 False have "\<dots> = multiplicity p (square_part x * x ^ n)"
      by (subst div_mult_self4) (auto simp: prime_multiplicity_square_part 
            prime_elem_multiplicity_mult_distrib prime_elem_multiplicity_power_distrib)
    finally show ?case .
  qed (insert False, auto)
  thus ?thesis by (simp add: mult_ac)
qed auto

lemma square_part_odd_power: 
  "odd n \<Longrightarrow> square_part (x ^ n) = normalize (x ^ (n div 2) * square_part x)"
  by (subst square_part_odd_power' [symmetric]) auto

end

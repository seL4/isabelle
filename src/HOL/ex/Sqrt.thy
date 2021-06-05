(*  Title:      HOL/ex/Sqrt.thy
    Author:     Makarius
    Author:     Tobias Nipkow, TU Muenchen
*)

section \<open>Square roots of primes are irrational\<close>

theory Sqrt
  imports Complex_Main "HOL-Computational_Algebra.Primes"
begin

text \<open>
  The square root of any prime number (including 2) is irrational.
\<close>

theorem sqrt_prime_irrational:
  fixes p :: nat
  assumes "prime p"
  shows "sqrt p \<notin> \<rat>"
proof
  from \<open>prime p\<close> have p: "p > 1" by (rule prime_gt_1_nat)
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat
    where n: "n \<noteq> 0"
      and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
      and "coprime m n" by (rule Rats_abs_nat_div_natE)
  have eq: "m\<^sup>2 = p * n\<^sup>2"
  proof -
    from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
    then have "m\<^sup>2 = (sqrt p)\<^sup>2 * n\<^sup>2" by (simp add: power_mult_distrib)
    also have "(sqrt p)\<^sup>2 = p" by simp
    also have "\<dots> * n\<^sup>2 = p * n\<^sup>2" by simp
    finally show ?thesis by linarith
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd m" by (rule prime_dvd_power)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2" by algebra
    with p have "n\<^sup>2 = p * k\<^sup>2" by (simp add: power2_eq_square)
    then have "p dvd n\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd n" by (rule prime_dvd_power)
  qed
  then have "p dvd gcd m n" by simp
  with \<open>coprime m n\<close> have "p = 1" by simp
  with p show False by simp
qed

corollary sqrt_2_not_rat: "sqrt 2 \<notin> \<rat>"
  using sqrt_prime_irrational [of 2] by simp

text \<open>
  Here is an alternative version of the main proof, using mostly linear
  forward-reasoning. While this results in less top-down structure, it is
  probably closer to proofs seen in mathematics.
\<close>

theorem
  fixes p :: nat
  assumes "prime p"
  shows "sqrt p \<notin> \<rat>"
proof
  from \<open>prime p\<close> have p: "p > 1" by (rule prime_gt_1_nat)
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat
    where n: "n \<noteq> 0"
      and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
      and "coprime m n" by (rule Rats_abs_nat_div_natE)
  from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
  then have "m\<^sup>2 = (sqrt p)\<^sup>2 * n\<^sup>2" by (auto simp add: power2_eq_square)
  also have "(sqrt p)\<^sup>2 = p" by simp
  also have "\<dots> * n\<^sup>2 = p * n\<^sup>2" by simp
  finally have eq: "m\<^sup>2 = p * n\<^sup>2" by linarith
  then have "p dvd m\<^sup>2" ..
  with \<open>prime p\<close> have dvd_m: "p dvd m" by (rule prime_dvd_power)
  then obtain k where "m = p * k" ..
  with eq have "p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2" by algebra
  with p have "n\<^sup>2 = p * k\<^sup>2" by (simp add: power2_eq_square)
  then have "p dvd n\<^sup>2" ..
  with \<open>prime p\<close> have "p dvd n" by (rule prime_dvd_power)
  with dvd_m have "p dvd gcd m n" by (rule gcd_greatest)
  with \<open>coprime m n\<close> have "p = 1" by simp
  with p show False by simp
qed


text \<open>
  Another old chestnut, which is a consequence of the irrationality of
  \<^term>\<open>sqrt 2\<close>.
\<close>

lemma "\<exists>a b::real. a \<notin> \<rat> \<and> b \<notin> \<rat> \<and> a powr b \<in> \<rat>" (is "\<exists>a b. ?P a b")
proof (cases "sqrt 2 powr sqrt 2 \<in> \<rat>")
  case True
  with sqrt_2_not_rat have "?P (sqrt 2) (sqrt 2)" by simp
  then show ?thesis by blast
next
  case False
  with sqrt_2_not_rat powr_powr have "?P (sqrt 2 powr sqrt 2) (sqrt 2)" by simp
  then show ?thesis by blast
qed

end

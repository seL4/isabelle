(*
  File:      HOL/Number_Theory/Residue_Primitive_Roots.thy
  Author:    Manuel Eberl

  Primitive roots in residue rings: Definition and existence criteria
*)
section \<open>Primitive roots in residue rings and Carmichael's function\<close>
theory Residue_Primitive_Roots
  imports Pocklington
begin

text \<open>
  This theory develops the notions of primitive roots (generators) in residue rings. It also
  provides a definition and all the basic properties of Carmichael's function $\lambda(n)$, which
  is strongly related to this. The proofs mostly follow Apostol's presentation
\<close>

subsection \<open>Primitive roots in residue rings\<close>

text \<open>
  A primitive root of a residue ring modulo \<open>n\<close> is an element \<open>g\<close> that \<^emph>\<open>generates\<close> the
  ring, i.\,e.\ such that for each \<open>x\<close> coprime to \<open>n\<close> there exists an \<open>i\<close> such that $x = g^i$.
  A simpler definition is that \<open>g\<close> must have the same order as the cardinality of the
  multiplicative group, which is $\varphi(n)$.

  Note that for convenience, this definition does \<^emph>\<open>not\<close> demand \<open>g < n\<close>.
\<close>
inductive residue_primroot :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "n > 0 \<Longrightarrow> coprime n g \<Longrightarrow> ord n g = totient n \<Longrightarrow> residue_primroot n g"

lemma residue_primroot_def [code]:
  "residue_primroot n x \<longleftrightarrow> n > 0 \<and> coprime n x \<and> ord n x = totient n"
  by (simp add: residue_primroot.simps)

lemma not_residue_primroot_0 [simp]: "~residue_primroot 0 x"
  by (auto simp: residue_primroot_def)

lemma residue_primroot_mod [simp]: "residue_primroot n (x mod n) = residue_primroot n x"
  by (cases "n = 0") (simp_all add: residue_primroot_def)

lemma residue_primroot_cong:
  assumes "[x = x'] (mod n)"
  shows   "residue_primroot n x = residue_primroot n x'"
proof -
  have "residue_primroot n x = residue_primroot n (x mod n)"
    by simp
  also have "x mod n = x' mod n"
    using assms by (simp add: cong_def)
  also have "residue_primroot n (x' mod n) = residue_primroot n x'"
    by simp
  finally show ?thesis .
qed

lemma not_residue_primroot_0_right [simp]: "residue_primroot n 0 \<longleftrightarrow> n = 1"
  by (auto simp: residue_primroot_def)

lemma residue_primroot_1_iff: "residue_primroot n (Suc 0) \<longleftrightarrow> n \<in> {1, 2}"
proof
  assume *: "residue_primroot n (Suc 0)"
  with totient_gt_1[of n] have "n \<le> 2" by (cases "n \<le> 2") (auto simp: residue_primroot_def)
  hence "n \<in> {0, 1, 2}" by auto
  thus "n \<in> {1, 2}" using * by (auto simp: residue_primroot_def)
qed (auto simp: residue_primroot_def)


subsection \<open>Primitive roots modulo a prime\<close>

text \<open>
  For prime \<open>p\<close>, we now analyse the number of elements in the ring $\mathbb{Z}/p\mathbb{Z}$
  whose order is precisely \<open>d\<close> for each \<open>d\<close>.
\<close>
context
  fixes n :: nat and \<psi>
  assumes n: "n > 1"
  defines "\<psi> \<equiv> (\<lambda>d. card {x\<in>totatives n. ord n x = d})"
begin

lemma elements_with_ord_restrict_totatives:
  "d > 0 \<Longrightarrow> {x\<in>{..<n}. ord n x = d} = {x\<in>totatives n. ord n x = d}"
  using n by (auto simp: totatives_def coprime_commute intro!: Nat.gr0I le_neq_trans)

lemma prime_elements_with_ord:
  assumes "\<psi> d \<noteq> 0" and "prime n"
      and a: "a \<in> totatives n" "ord n a = d" "a \<noteq> 1"
  shows   "inj_on (\<lambda>k. a ^ k mod n) {..<d}"
    and   "{x\<in>{..<n}. [x ^ d = 1] (mod n)} = (\<lambda>k. a ^ k mod n) ` {..<d}"
    and   "bij_betw (\<lambda>k. a ^ k mod n) (totatives d) {x\<in>{..<n}. ord n x = d}"
proof -
  show inj: "inj_on (\<lambda>k. a ^ k mod n) {..<d}"
    using inj_power_mod[of n a] a by (auto simp: totatives_def coprime_commute)
  from a have "d > 0" by (auto simp: totatives_def coprime_commute)
  moreover have "d \<noteq> 1" using a n
    by (auto simp: ord_eq_Suc_0_iff totatives_less cong_def)
  ultimately have d: "d > 1" by simp

  have *: "(\<lambda>k. a ^ k mod n) ` {..<d} = {x\<in>{..<n}. [x ^ d = 1] (mod n)}"
  proof (rule card_seteq)
    have "card {x\<in>{..<n}. [x ^ d = 1] (mod n)} \<le> d"
      using assms a by (intro roots_mod_prime_bound) (auto simp: totatives_def coprime_commute)
    also have "\<dots> = card ((\<lambda>k. a ^ k mod n) ` {..<d})"
      using inj by (subst card_image) auto
    finally show "card {x \<in> {..<n}. [x ^ d = 1] (mod n)} \<le> \<dots>" .
  next
    show "(\<lambda>k. a ^ k mod n) ` {..<d} \<subseteq> {x \<in> {..<n}. [x ^ d = 1] (mod n)}"
    proof safe
      fix k assume "k < d"
      have "[(a ^ d) ^ k = 1 ^ k] (mod n)"
        by (intro cong_pow) (use a in \<open>auto simp: ord_divides'\<close>)
      thus "[(a ^ k mod n) ^ d = 1] (mod n)"
        by (simp add: power_mult [symmetric] cong_def power_mod mult.commute)
    qed (use \<open>prime n\<close> in \<open>auto dest: prime_gt_1_nat\<close>)
  qed auto
  thus "{x\<in>{..<n}. [x ^ d = 1] (mod n)} = (\<lambda>k. a ^ k mod n) ` {..<d}" ..

  show "bij_betw (\<lambda>k. a ^ k mod n) (totatives d) {x\<in>{..<n}. ord n x = d}"
    unfolding bij_betw_def
  proof (intro conjI inj_on_subset[OF inj] equalityI subsetI)
    fix b assume "b \<in> (\<lambda>k. a ^ k mod n) ` totatives d"
    then obtain k where "b = a ^ k mod n" "k \<in> totatives d" by auto
    thus "b \<in> {b \<in> {..<n}. ord n b = d}"
      using n a by (simp add: ord_power totatives_def coprime_commute)
  next
    fix b assume "b \<in> {x \<in> {..<n}. ord n x = d}"
    hence b: "ord n b = d" "b < n" by auto
    with d have "coprime n b" using ord_eq_0[of n b] by auto
    from b have "b \<in> {x\<in>{..<n}. [x ^ d = 1] (mod n)}"
      by (auto simp: ord_divides')
    with * obtain k where k: "k < d" "b = a ^ k mod n"
      by blast
    with b(2) n a d have "d div gcd k d = ord n b"
      using \<open>coprime n b\<close> by (auto simp: ord_power)
    also have "ord n b = d" by (simp add: b)
    finally have "coprime k d"
      unfolding coprime_iff_gcd_eq_1 using d a by (subst (asm) div_eq_dividend_iff) auto
    with k b d have "k \<in> totatives d" by (auto simp: totatives_def intro!: Nat.gr0I)
    with k show "b \<in> (\<lambda>k. a ^ k mod n) ` totatives d" by blast
  qed (use d n in \<open>auto simp: totatives_less\<close>)
qed

lemma prime_card_elements_with_ord:
  assumes "\<psi> d \<noteq> 0" and "prime n"
  shows   "\<psi> d = totient d"
proof (cases "d = 1")
  case True
  have "\<psi> 1 = 1"
    using elements_with_ord_1[of n] n by (simp add: \<psi>_def)
  thus ?thesis using True by simp
next
  case False
  from assms obtain a where a: "a \<in> totatives n" "ord n a = d"
    by (auto simp: \<psi>_def)
  from a have "d > 0" by (auto intro!: Nat.gr0I simp: ord_eq_0 totatives_def coprime_commute)
  from a and False have "a \<noteq> 1" by auto
  from bij_betw_same_card[OF prime_elements_with_ord(3)[OF assms a this]] show "\<psi> d = totient d"
    using elements_with_ord_restrict_totatives[of d] False a \<open>d > 0\<close>
    by (simp add: \<psi>_def totient_def)
qed

lemma prime_sum_card_elements_with_ord_eq_totient:
  "(\<Sum>d | d dvd totient n. \<psi> d) = totient n"
proof -
  have "totient n = card (totatives n)"
    by (simp add: totient_def)
  also have "totatives n = (\<Union>d\<in>{d. d dvd totient n}. {x\<in>totatives n. ord n x = d})"
    by (force simp: order_divides_totient totatives_def coprime_commute)
  also have "card \<dots> = (\<Sum>d | d dvd totient n. \<psi> d)"
    unfolding \<psi>_def using n by (subst card_UN_disjoint) (auto intro!: finite_divisors_nat)
  finally show ?thesis ..
qed

text \<open>
  We can now show that the number of elements of order \<open>d\<close> is $\varphi(d)$ if $d\mid p - 1$
  and 0 otherwise.
\<close>
theorem prime_card_elements_with_ord_eq_totient:
  assumes "prime n"
  shows   "\<psi> d = (if d dvd n - 1 then totient d else 0)"
proof (cases "d dvd totient n")
  case False
  thus ?thesis using order_divides_totient[of n] assms
    by (auto simp: \<psi>_def totient_prime totatives_def coprime_commute[of n])
next
  case True
  have "\<psi> d = totient d"
  proof (rule ccontr)
    assume neq: "\<psi> d \<noteq> totient d"
    have le: "\<psi> d \<le> totient d" if "d dvd totient n" for d
      using prime_card_elements_with_ord[of d] assms by (cases "\<psi> d = 0") auto
    from neq and le[of d] and True have less: "\<psi> d < totient d" by auto
  
    have "totient n = (\<Sum>d | d dvd totient n. \<psi> d)"
      using prime_sum_card_elements_with_ord_eq_totient ..
    also have "\<dots> < (\<Sum>d | d dvd totient n. totient d)"
      by (rule sum_strict_mono_ex1)
         (use n le less assms True in \<open>auto intro!: finite_divisors_nat\<close>)
    also have "\<dots> = totient n"
      using totient_divisor_sum .
    finally show False by simp
  qed
  with True show ?thesis using assms by (simp add: totient_prime)
qed

text \<open>
  As a corollary, we get that the number of primitive roots modulo a prime \<open>p\<close> is
  $\varphi(p - 1)$. Since this number is positive, we also get that there \<^emph>\<open>is\<close> at least
  one primitive root modulo \<open>p\<close>.
\<close>
lemma
  assumes "prime n"
  shows   prime_card_primitive_roots:  "card {x\<in>totatives n. ord n x = n - 1} = totient (n - 1)"
                                       "card {x\<in>{..<n}. ord n x = n - 1} = totient (n - 1)"
  and     prime_primitive_root_exists: "\<exists>x. residue_primroot n x"
proof -
  show *: "card {x\<in>totatives n. ord n x = n - 1} = totient (n - 1)"
    using prime_card_elements_with_ord_eq_totient[of "n - 1"] assms
    by (auto simp: totient_prime \<psi>_def)
  thus "card {x\<in>{..<n}. ord n x = n - 1} = totient (n - 1)"
    using assms n elements_with_ord_restrict_totatives[of "n - 1"] by simp
  
  note *
  also have "totient (n - 1) > 0" using n by auto
  finally show "\<exists>x. residue_primroot n x" using assms prime_gt_1_nat[of n]
    by (subst (asm) card_gt_0_iff)
       (auto simp: residue_primroot_def totient_prime totatives_def coprime_commute)
qed

end


subsection \<open>Primitive roots modulo powers of an odd prime\<close>

text \<open>
  Any primitive root \<open>g\<close> modulo an odd prime \<open>p\<close> is also a primitive root modulo $p^k$ for all
  $k > 0$ if $[g^{p - 1} \neq 1]\ (\text{mod}\ p^2)$. To show this, we first need the
  following lemma.
\<close>
lemma residue_primroot_power_prime_power_neq_1:
  assumes "k \<ge> 2"
  assumes p: "prime p" "odd p" and "residue_primroot p g" and "[g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
  shows   "[g ^ totient (p ^ (k - 1)) \<noteq> 1] (mod (p ^ k))"
  using assms(1)
proof (induction k rule: dec_induct)
  case base
  thus ?case using assms by (simp add: totient_prime)
next
  case (step k)
  from p have "p > 2"
    using prime_gt_1_nat[of p] by (cases "p = 2") auto
  from assms have g: "g > 0" by (auto intro!: Nat.gr0I)
  have "[g ^ totient (p ^ (k - 1)) = 1] (mod p ^ (k - 1))"
    using assms by (intro euler_theorem)
                   (auto simp: residue_primroot_def totatives_def coprime_commute)
  from cong_to_1_nat[OF this]
    obtain t where *: "g ^ totient (p ^ (k - 1)) - 1 = p ^ (k - 1) * t" by auto
  have t: "g ^ totient (p ^ (k - 1)) = p ^ (k - 1) * t + 1"
    using g by (subst * [symmetric]) auto 

  have "\<not>p dvd t"
  proof
    assume "p dvd t"
    then obtain q where [simp]: "t = p * q" by auto
    from t have "g ^ totient (p ^ (k - 1)) = p ^ k * q + 1"
      using \<open>k \<ge> 2\<close> by (cases k) auto
    hence "[g ^ totient (p ^ (k - 1)) = p ^ k * q + 1] (mod p ^ k)"
      by simp
    also have "[p ^ k * q + 1 = 0 * q + 1] (mod p ^ k)"
      by (intro cong_add cong_mult) (auto simp: cong_0_iff)
    finally have "[g ^ totient (p ^ (k - 1)) = 1] (mod p ^ k)"
      by simp
    with step.IH show False by contradiction
  qed

  from t have "(g ^ totient (p ^ (k - 1))) ^ p = (p ^ (k - 1) * t + 1) ^ p"
    by (rule arg_cong)
  also have "(g ^ totient (p ^ (k - 1))) ^ p = g ^ (p * totient (p ^ (k - 1)))"
    by (simp add: power_mult [symmetric] mult.commute)
  also have "p * totient (p ^ (k - 1)) = totient (p ^ k)"
    using p \<open>k \<ge> 2\<close> by (simp add: totient_prime_power Suc_diff_Suc flip: power_Suc)
  also have "(p ^ (k - 1) * t + 1) ^ p = (\<Sum>i\<le>p. (p choose i) * t ^ i * p ^ (i * (k - 1)))"
    by (subst binomial) (simp_all add: mult_ac power_mult_distrib power_mult [symmetric])
  finally have "[g ^ totient (p ^ k) = (\<Sum>i\<le>p. (p choose i) * t ^ i * p ^ (i * (k - 1)))]
                  (mod (p ^ Suc k))" (is "[_ = ?rhs] (mod _)") by simp

  also have "[?rhs = (\<Sum>i\<le>p. if i \<le> 1 then (p choose i) * t ^ i * p ^ (i * (k - 1)) else 0)]
               (mod (p ^ Suc k))" (is "[sum ?f _ = sum ?g _] (mod _)")
  proof (intro cong_sum)
    fix i assume i: "i \<in> {..p}"
    consider "i \<le> 1" | "i = 2" | "i > 2" by force
    thus "[?f i = ?g i] (mod (p ^ Suc k))"
    proof cases
      assume i: "i > 2"
      have "Suc k \<le> 3 * (k - 1)"
        using \<open>k \<ge> 2\<close> by (simp add: algebra_simps)
      also have "3 * (k - 1) \<le> i * (k - 1)"
        using i by (intro mult_right_mono) auto
      finally have "p ^ Suc k dvd ?f i"
        by (intro dvd_mult le_imp_power_dvd)
      thus "[?f i = ?g i] (mod (p ^ Suc k))"
        by (simp add: cong_0_iff)
    next
      assume [simp]: "i = 2"
      have "?f i = p * (p - 1) div 2 * t\<^sup>2 * p ^ (2 * (k - 1))"
        using choose_two[of p] by simp
      also have "p * (p - 1) div 2 = (p - 1) div 2 * p"
        using \<open>odd p\<close> by (auto elim!: oddE)
      also have "\<dots> * t\<^sup>2 * p ^ (2 * (k - 1)) = (p - 1) div 2 * t\<^sup>2 * (p * p ^ (2 * (k - 1)))"
        by (simp add: algebra_simps)
      also have "p * p ^ (2 * (k - 1)) = p ^ (2 * k - 1)"
        using \<open>k \<ge> 2\<close> by (cases k) auto
      also have "p ^ Suc k dvd (p - 1) div 2 * t\<^sup>2 * p ^ (2 * k - 1)"
        using \<open>k \<ge> 2\<close> by (intro dvd_mult le_imp_power_dvd) auto
      finally show "[?f i = ?g i] (mod (p ^ Suc k))"
        by (simp add: cong_0_iff)
    qed auto
  qed
  also have "(\<Sum>i\<le>p. ?g i) = (\<Sum>i\<le>1. ?f i)"
    using p prime_gt_1_nat[of p] by (intro sum.mono_neutral_cong_right) auto
  also have "\<dots> = 1 + t * p ^ k"
    using choose_two[of p] \<open>k \<ge> 2\<close> by (cases k) simp_all
  finally have eq: "[g ^ totient (p ^ k) = 1 + t * p ^ k] (mod p ^ Suc k)" .

  have "[g ^ totient (p ^ k) \<noteq> 1] (mod p ^ Suc k)"
  proof
    assume "[g ^ totient (p ^ k) = 1] (mod p ^ Suc k)"
    hence "[g ^ totient (p ^ k) - g ^ totient (p ^ k) = 1 + t * p ^ k - 1] (mod p ^ Suc k)"
      by (intro cong_diff_nat eq) auto
    hence "[t * p ^ k = 0] (mod p ^ Suc k)"
      by (simp add: cong_sym_eq)
    hence "p * p ^ k dvd t * p ^ k"
      by (simp add: cong_0_iff)
    hence "p dvd t" using \<open>p > 2\<close> by simp
    with \<open>\<not>p dvd t\<close> show False by contradiction
  qed
  thus ?case by simp
qed

text \<open>
  We can now show that primitive roots modulo \<open>p\<close> with the above condition are
  indeed also primitive roots modulo $p^k$.
\<close>
proposition residue_primroot_prime_lift_iff:
  assumes p: "prime p" "odd p" and "residue_primroot p g"
  shows   "(\<forall>k>0. residue_primroot (p ^ k) g) \<longleftrightarrow> [g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
proof -
  from assms have g: "coprime p g" "ord p g = p - 1"
    by (auto simp: residue_primroot_def totient_prime)
  show ?thesis
  proof
    assume "\<forall>k>0. residue_primroot (p ^ k) g"
    hence "residue_primroot (p\<^sup>2) g" by auto
    hence "ord (p\<^sup>2) g = totient (p\<^sup>2)"
      by (simp_all add: residue_primroot_def)
    thus "[g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
      using g assms prime_gt_1_nat[of p]
      by (auto simp: ord_divides' totient_prime_power)
  next
    assume g': "[g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"

    have "residue_primroot (p ^ k) g" if "k > 0" for k
    proof (cases "k = 1")
      case False
      with that have k: "k > 1" by simp
      from g have coprime: "coprime (p ^ k) g"
        by (auto simp: totatives_def coprime_commute)

      define t where "t = ord (p ^ k) g"
      have "[g ^ t = 1] (mod (p ^ k))"
        by (simp add: t_def ord_divides')
      also have "p ^ k = p * p ^ (k - 1)"
        using k by (cases k) auto
      finally have "[g ^ t = 1] (mod p)"
        by (rule cong_modulus_mult_nat)
      hence "totient p dvd t"
        using g p by (simp add: ord_divides' totient_prime)
      then obtain q where t: "t = totient p * q" by auto

      have "t dvd totient (p ^ k)"
        using coprime by (simp add: t_def order_divides_totient)
      with t p k have "q dvd p ^ (k - 1)" using prime_gt_1_nat[of p]
        by (auto simp: totient_prime totient_prime_power)
      then obtain b where b: "b \<le> k - 1" "q = p ^ b"
        using divides_primepow_nat[of p q "k - 1"] p by auto

      have "b = k - 1"
      proof (rule ccontr)
        assume "b \<noteq> k - 1"
        with b have "b < k - 1" by simp
        have "t = p ^ b * (p - 1)"
          using b p by (simp add: t totient_prime)
        also have "\<dots> dvd p ^ (k - 2) * (p - 1)"
          using \<open>b < k - 1\<close> by (intro mult_dvd_mono le_imp_power_dvd) auto
        also have "\<dots> = totient (p ^ (k - 1))"
          using k p by (simp add: totient_prime_power numeral_2_eq_2)
        finally have "[g ^ totient (p ^ (k - 1)) = 1] (mod (p ^ k))"
          by (simp add: ord_divides' t_def)
        with residue_primroot_power_prime_power_neq_1[of k p g] p k assms g' show False
          by auto
      qed
      hence "t = totient (p ^ k)"
        using p k by (simp add: t b totient_prime totient_prime_power)
      thus "residue_primroot (p ^ k) g"
        using g one_less_power[of p k] prime_gt_1_nat[of p] p k
        by (simp add: residue_primroot_def t_def)
    qed (use assms in auto)
    thus "\<forall>k>0. residue_primroot (p ^ k) g" by blast
  qed
qed

text \<open>
  If \<open>p\<close> is an odd prime, there is always a primitive root \<open>g\<close> modulo \<open>p\<close>, and if \<open>g\<close> does not
  fulfil the above assumption required for it to be liftable to $p^k$, we can use $g + p$, which
  is also a primitive root modulo \<open>p\<close> and \<^emph>\<open>does\<close> fulfil the assumption.

  This shows that any modulus that is a power of an odd prime has a primitive root.
\<close>
theorem residue_primroot_odd_prime_power_exists:
  assumes p: "prime p" "odd p"
  obtains g where "\<forall>k>0. residue_primroot (p ^ k) g"
proof -
  obtain g where g: "residue_primroot p g"
    using prime_primitive_root_exists[of p] assms prime_gt_1_nat[of p] by auto

  have "\<exists>g. residue_primroot p g \<and> [g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
  proof (cases "[g ^ (p - 1) = 1] (mod p\<^sup>2)")
    case True
    define g' where "g' = p + g"
    note g
    also have "residue_primroot p g \<longleftrightarrow> residue_primroot p g'"
      unfolding g'_def by (rule residue_primroot_cong) (auto simp: cong_def)
    finally have g': "residue_primroot p g'" .

    have "[g' ^ (p - 1) = (\<Sum>k\<le>p-1. ((p-1) choose k) * g ^ (p - Suc k) * p ^ k)] (mod p\<^sup>2)"
      (is "[_ = ?rhs] (mod _)") by (simp add: g'_def binomial mult_ac)
    also have "[?rhs = (\<Sum>k\<le>p-1. if k \<le> 1 then ((p-1) choose k) *
                                   g ^ (p - Suc k) * p ^ k else 0)] (mod p\<^sup>2)"
      (is "[sum ?f _ = sum ?g _] (mod _)")
    proof (intro cong_sum)
      fix k assume "k \<in> {..p-1}"
      show "[?f k = ?g k] (mod p\<^sup>2)"
      proof (cases "k \<le> 1")
        case False
        have "p\<^sup>2 dvd ?f k"
          using False by (intro dvd_mult le_imp_power_dvd) auto
        thus ?thesis using False by (simp add: cong_0_iff)
      qed auto
    qed
    also have "sum ?g {..p-1} = sum ?f {0, 1}"
      using prime_gt_1_nat[of p] p by (intro sum.mono_neutral_cong_right) auto
    also have "\<dots> = g ^ (p - 1) + p * (p - 1) * g ^ (p - 2)"
      using p by (simp add: numeral_2_eq_2)
    also have "[g ^ (p - 1) + p * (p - 1) * g ^ (p - 2) = 1 + p * (p - 1) * g ^ (p - 2)] (mod p\<^sup>2)"
      by (intro cong_add True) auto
    finally have "[g' ^ (p - 1) = 1 + p * (p - 1) * g ^ (p - 2)] (mod p\<^sup>2)" .

    moreover have "[1 + p * (p - 1) * g ^ (p - 2) \<noteq> 1] (mod p\<^sup>2)"
    proof
      assume "[1 + p * (p - 1) * g ^ (p - 2) = 1] (mod p\<^sup>2)"
      hence "[1 + p * (p - 1) * g ^ (p - 2) - 1 = 1 - 1] (mod p\<^sup>2)"
        by (intro cong_diff_nat) auto
      hence "p * p dvd p * ((p - 1) * g ^ (p - 2))"
        by (auto simp: cong_0_iff power2_eq_square)
      hence "p dvd (p - 1) * g ^ (p - 2)"
        using p by simp
      hence "p dvd g ^ (p - 2)"
        using p dvd_imp_le[of p "p - Suc 0"] prime_gt_1_nat[of p]
        by (auto simp: prime_dvd_mult_iff)
      also have "\<dots> dvd g ^ (p - 1)"
        by (intro le_imp_power_dvd) auto
      finally have "[g ^ (p - 1) = 0] (mod p)"
        by (simp add: cong_0_iff)
      hence "[0 = g ^ (p - 1)] (mod p)"
        by (simp add: cong_sym_eq)

      also from \<open>residue_primroot p g\<close> have "[g ^ (p - 1) = 1] (mod p)"
        using p by (auto simp: residue_primroot_def ord_divides' totient_prime)
      finally have "[0 = 1] (mod p)" .
      thus False using prime_gt_1_nat[of p] p by (simp add: cong_def)
    qed

    ultimately have "[g' ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
      by (simp add: cong_def)
    thus "\<exists>g. residue_primroot p g \<and> [g ^ (p - 1) \<noteq> 1] (mod p\<^sup>2)"
      using g' by blast    
  qed (use g in auto)
  thus ?thesis
    using residue_primroot_prime_lift_iff[OF assms] that by blast
qed


subsection \<open>Carmichael's function\<close>

text \<open>
  Carmichael's function $\lambda(n)$ gives the LCM of the orders of all elements in the
  residue ring modulo $n$ -- or, equivalently, the maximum order, as we will show later.
  Algebraically speaking, it is the exponent of the multiplicative group
  $(\mathbb{Z}/n\mathbb{Z})^*$.

  It is not to be confused with Liouville's function, which is also denoted by $\lambda(n)$.
\<close>
definition Carmichael where
  "Carmichael n = (LCM a \<in> totatives n. ord n a)"

lemma Carmichael_0 [simp]: "Carmichael 0 = 1"
  by (simp add: Carmichael_def)

lemma Carmichael_1 [simp]: "Carmichael 1 = 1"
  by (simp add: Carmichael_def)

lemma Carmichael_Suc_0 [simp]: "Carmichael (Suc 0) = 1"
  by (simp add: Carmichael_def)

lemma ord_dvd_Carmichael:
  assumes "n > 1" "coprime n k"
  shows   "ord n k dvd Carmichael n"
proof -
  have "k mod n \<in> totatives n"
    using assms by (auto simp: totatives_def coprime_commute intro!: Nat.gr0I)
  hence "ord n (k mod n) dvd Carmichael n"
    by (simp add: Carmichael_def del: ord_mod)
  thus ?thesis by simp
qed

lemma Carmichael_divides:
  assumes "Carmichael n dvd k" "coprime n a"
  shows   "[a ^ k = 1] (mod n)"
proof (cases "n < 2 \<or> a = 1")
  case False
  hence "ord n a dvd Carmichael n"
    using False assms by (intro ord_dvd_Carmichael) auto
  also have "\<dots> dvd k" by fact
  finally have "ord n a dvd k" .
  thus ?thesis using ord_divides by auto
next
  case True
  then consider "a = 1" | "n = 0" | "n = 1" by force
  thus ?thesis using assms by cases auto
qed

lemma Carmichael_dvd_totient: "Carmichael n dvd totient n"
  unfolding Carmichael_def
proof (intro Lcm_least, safe)
  fix a assume "a \<in> totatives n"
  hence "[a ^ totient n = 1] (mod n)"
    by (intro euler_theorem) (auto simp: totatives_def)
  thus "ord n a dvd totient n"
    using ord_divides by blast
qed

lemma Carmichael_dvd_mono_coprime:
  assumes "coprime m n" "m > 1" "n > 1"
  shows   "Carmichael m dvd Carmichael (m * n)"
  unfolding Carmichael_def[of m]
proof (intro Lcm_least, safe)
  fix x assume x: "x \<in> totatives m"
  from assms have "totatives n \<noteq> {}" by simp
  then obtain y where y: "y \<in> totatives n" by blast

  from binary_chinese_remainder_nat[OF assms(1), of x y]
  obtain z where z: "[z = x] (mod m)" "[z = y] (mod n)" by blast
  have z': "coprime z n" "coprime z m"
    by (rule cong_imp_coprime; use x y z in \<open>force simp: totatives_def cong_sym_eq\<close>)+

  from z have "ord m x = ord m z"
    by (intro ord_cong) (auto simp: cong_sym_eq)
  also have "ord m z dvd ord (m * n) z"
    using assms by (auto simp: ord_modulus_mult_coprime)
  also from z' assms have "\<dots> dvd Carmichael (m * n)"
    by (intro ord_dvd_Carmichael) (auto simp: coprime_commute intro!:one_less_mult)
  finally show "ord m x dvd Carmichael (m * n)" .
qed

text \<open>
  $\lambda$ distributes over the product of coprime numbers similarly to $\varphi$, but
  with LCM instead of multiplication:
\<close>
lemma Carmichael_mult_coprime:
  assumes "coprime m n"
  shows   "Carmichael (m * n) = lcm (Carmichael m) (Carmichael n)"
proof (cases "m \<le> 1 \<or> n \<le> 1")
  case True
  hence "m = 0 \<or> n = 0 \<or> m = 1 \<or> n = 1" by force
  thus ?thesis using assms by auto
next
  case False
  show ?thesis
  proof (rule dvd_antisym)
    show "Carmichael (m * n) dvd lcm (Carmichael m) (Carmichael n)"
      unfolding Carmichael_def[of "m * n"]
    proof (intro Lcm_least, safe)
      fix x assume x: "x \<in> totatives (m * n)"
      have "ord (m * n) x = lcm (ord m x) (ord n x)"
        using assms x by (subst ord_modulus_mult_coprime) (auto simp: coprime_commute totatives_def)
      also have "\<dots> dvd lcm (Carmichael m) (Carmichael n)"
        using False x
        by (intro lcm_mono ord_dvd_Carmichael) (auto simp: totatives_def coprime_commute)
      finally show "ord (m * n) x dvd \<dots>" .
    qed
  next
    show "lcm (Carmichael m) (Carmichael n) dvd Carmichael (m * n)"
      using Carmichael_dvd_mono_coprime[of m n]
            Carmichael_dvd_mono_coprime[of n m] assms False
      by (auto intro!: lcm_least simp: coprime_commute mult.commute)
  qed
qed

lemma Carmichael_pos [simp, intro]: "Carmichael n > 0"
  by (auto simp: Carmichael_def ord_eq_0 totatives_def coprime_commute intro!: Nat.gr0I)

lemma Carmichael_nonzero [simp]: "Carmichael n \<noteq> 0"
  by simp

lemma power_Carmichael_eq_1:
  assumes "n > 1" "coprime n x"
  shows   "[x ^ Carmichael n = 1] (mod n)"
  using ord_dvd_Carmichael[of n x] assms
  by (auto simp: ord_divides')

lemma Carmichael_2 [simp]: "Carmichael 2 = 1"
  using Carmichael_dvd_totient[of 2] by simp

lemma Carmichael_4 [simp]: "Carmichael 4 = 2"
proof -
  have "Carmichael 4 dvd 2"
    using Carmichael_dvd_totient[of 4] by simp
  hence "Carmichael 4 \<le> 2" by (rule dvd_imp_le) auto
  moreover have "Carmichael 4 \<noteq> 1"
    using power_Carmichael_eq_1[of "4::nat" 3]
    unfolding coprime_iff_gcd_eq_1 by (auto simp: gcd_non_0_nat cong_def)
  ultimately show ?thesis
    using Carmichael_pos[of 4] by linarith
qed

lemma residue_primroot_Carmichael:
  assumes "residue_primroot n g"
  shows   "Carmichael n = totient n"
proof (cases "n = 1")
  case False
  show ?thesis
  proof (intro dvd_antisym Carmichael_dvd_totient)
    have "ord n g dvd Carmichael n"
      using assms False by (intro ord_dvd_Carmichael) (auto simp: residue_primroot_def)
    thus "totient n dvd Carmichael n"
      using assms by (auto simp: residue_primroot_def)
  qed
qed auto

lemma Carmichael_odd_prime_power:
  assumes "prime p" "odd p" "k > 0"
  shows   "Carmichael (p ^ k) = p ^ (k - 1) * (p - 1)"
proof -
  from assms obtain g where "residue_primroot (p ^ k) g"
    using residue_primroot_odd_prime_power_exists[of p] assms by metis
  hence "Carmichael (p ^ k) = totient (p ^ k)"
    by (intro residue_primroot_Carmichael[of "p ^ k" g]) auto
  with assms show ?thesis by (simp add: totient_prime_power)
qed

lemma Carmichael_prime:
  assumes "prime p"
  shows   "Carmichael p = p - 1"
proof (cases "even p")
  case True
  with assms have "p = 2"
    using primes_dvd_imp_eq two_is_prime_nat by blast
  thus ?thesis by simp
next
  case False
  with Carmichael_odd_prime_power[of p 1] assms show ?thesis by simp
qed
  
lemma Carmichael_twopow_ge_8:
  assumes "k \<ge> 3"
  shows   "Carmichael (2 ^ k) = 2 ^ (k - 2)"
proof (intro dvd_antisym)
  have "2 ^ (k - 2) = ord (2 ^ k) (3 :: nat)"
    using ord_twopow_3_5[of k 3] assms by simp
  also have "\<dots> dvd Carmichael (2 ^ k)"
    using assms one_less_power[of "2::nat" k] by (intro ord_dvd_Carmichael) auto
  finally show "2 ^ (k - 2) dvd \<dots>" .
next
  show "Carmichael (2 ^ k) dvd 2 ^ (k - 2)"
    unfolding Carmichael_def
  proof (intro Lcm_least, safe)
    fix x assume "x \<in> totatives (2 ^ k)"
    hence "odd x" by (auto simp: totatives_def)
    hence "[x ^ 2 ^ (k - 2) = 1] (mod 2 ^ k)"
      using assms ord_twopow_aux[of k x] by auto
    thus "ord (2 ^ k) x dvd 2 ^ (k - 2)"
      by (simp add: ord_divides')
  qed
qed

lemma Carmichael_twopow:
  "Carmichael (2 ^ k) = (if k \<le> 2 then 2 ^ (k - 1) else 2 ^ (k - 2))"
proof -
  have "k = 0 \<or> k = 1 \<or> k = 2 \<or> k \<ge> 3" by linarith
  thus ?thesis by (auto simp: Carmichael_twopow_ge_8)
qed

lemma Carmichael_prime_power:
  assumes "prime p" "k > 0"
  shows   "Carmichael (p ^ k) =
             (if p = 2 \<and> k > 2 then 2 ^ (k - 2) else p ^ (k - 1) * (p - 1))"
proof (cases "p = 2")
  case True
  thus ?thesis by (simp add: Carmichael_twopow)
next
  case False
  with assms have "odd p" "p > 2"
    using prime_odd_nat[of p] prime_gt_1_nat[of p] by auto
  thus ?thesis
    using assms Carmichael_odd_prime_power[of p k] by simp
qed

lemma Carmichael_prod_coprime:
  assumes "finite A" "\<And>i j. i \<in> A \<Longrightarrow> j \<in> A \<Longrightarrow> i \<noteq> j \<Longrightarrow> coprime (f i) (f j)"
  shows   "Carmichael (\<Prod>i\<in>A. f i) = (LCM i\<in>A. Carmichael (f i))"
  using assms by (induction A rule: finite_induct)
                 (simp, simp, subst Carmichael_mult_coprime[OF prod_coprime_right], auto)

text \<open>
  Since $\lambda$ distributes over coprime factors and we know the value of $\lambda(p^k)$
  for prime $p$, we can now give a closed formula for $\lambda(n)$ in terms of the prime
  factorisation of $n$:
\<close>
theorem Carmichael_closed_formula:
  "Carmichael n =
     (LCM p\<in>prime_factors n. let k = multiplicity p n
                             in  if p = 2 \<and> k > 2 then 2 ^ (k - 2) else p ^ (k - 1) * (p - 1))"
  (is "_ = Lcm ?A")
proof (cases "n = 0")
  case False
  hence "n = (\<Prod>p\<in>prime_factors n. p ^ multiplicity p n)"
    using prime_factorization_nat by blast
  also have "Carmichael \<dots> =
               (LCM p\<in>prime_factors n. Carmichael (p ^ multiplicity p n))"
    by (subst Carmichael_prod_coprime) (auto simp: in_prime_factors_iff primes_coprime)
  also have "(\<lambda>p. Carmichael (p ^ multiplicity p n)) ` prime_factors n = ?A"
    by (intro image_cong)
       (auto simp: Let_def Carmichael_prime_power prime_factors_multiplicity)
  finally show ?thesis .
qed auto

corollary even_Carmichael:
  assumes "n > 2"
  shows   "even (Carmichael n)"
proof (cases "\<exists>k. n = 2 ^ k")
  case True
  then obtain k where [simp]: "n = 2 ^ k" by auto
  from assms have "k \<noteq> 0" "k \<noteq> 1" by (auto intro!: Nat.gr0I)
  hence "k \<ge> 2" by auto
  thus ?thesis by (auto simp: Carmichael_twopow)
next
  case False
  from assms have "n \<noteq> 0" by auto
  from False have "\<exists>p\<in>prime_factors n. p \<noteq> 2"
    using assms Ex_other_prime_factor[of n 2] by auto
  from divide_out_primepow_ex[OF \<open>n \<noteq> 0\<close> this]
  obtain p k n'
    where p:
      "p \<noteq> 2"
      "prime p"
      "p dvd n"
      "\<not> p dvd n'"
      "0 < k"
      "n = p ^ k * n'" .
  from p have coprime: "coprime (p ^ k) n'"
    using p prime_imp_coprime by auto
  have "odd p"
    using p primes_dvd_imp_eq[of 2 p] by auto
  have "even (Carmichael (p ^ k))"
    using p \<open>odd p\<close> by (auto simp: Carmichael_prime_power)
  with p coprime show ?thesis
    by (auto simp: Carmichael_mult_coprime intro!: dvd_lcmI1)
qed

lemma eval_Carmichael:
  assumes "prime_factorization n = A"
  shows     "Carmichael n = (LCM p \<in> set_mset A.
               let k = count A p in if p = 2 \<and> k > 2 then 2 ^ (k - 2) else p ^ (k - 1) * (p - 1))"
  unfolding assms [symmetric] Carmichael_closed_formula
  by (intro arg_cong[where f = Lcm] image_cong) (auto simp: Let_def count_prime_factorization)

text \<open>
  Any residue ring always contains a $\lambda$-root, i.\,e.\ an element whose
  order is $\lambda(n)$.
\<close>
theorem Carmichael_root_exists:
  assumes "n > (0::nat)"
  obtains g where "g \<in> totatives n" and "ord n g = Carmichael n"
proof (cases "n = 1")
  case True
  thus ?thesis by (intro that[of 1]) (auto simp: totatives_def)
next
  case False
  have primepow: "\<exists>g. coprime (p ^ k) g \<and> ord (p ^ k) g = Carmichael (p ^ k)"
    if pk: "prime p" "k > 0" for p k
  proof (cases "p = 2")
    case [simp]: True
    from \<open>k > 0\<close> consider "k = 1" | "k = 2" | "k \<ge> 3" by force
    thus ?thesis
    proof cases
      assume "k = 1"
      thus ?thesis by (intro exI[of _ 1]) auto
    next
      assume [simp]: "k = 2"
      have "coprime 4 (3::nat)"
        by (auto simp: coprime_iff_gcd_eq_1 gcd_non_0_nat)
      thus ?thesis by (intro exI[of _ 3]) auto
    next
      assume k: "k \<ge> 3"
      have "coprime (2 ^ k :: nat) 3" by auto
      thus ?thesis using k
        by (intro exI[of _ 3]) (auto simp: ord_twopow_3_5 Carmichael_twopow)
    qed
  next
    case False
    hence "odd p" using \<open>prime p\<close>
      using primes_dvd_imp_eq two_is_prime_nat by blast
    then obtain g where "residue_primroot (p ^ k) g"
      using residue_primroot_odd_prime_power_exists[of p] pk by metis
    thus ?thesis using False pk
      by (intro exI[of _ g])
         (auto simp: Carmichael_prime_power residue_primroot_def totient_prime_power)
  qed

  define P where "P = prime_factors n"
  define k where "k = (\<lambda>p. multiplicity p n)"
  have "\<forall>p\<in>P. \<exists>g. coprime (p ^ k p) g \<and> ord (p ^ k p) g = Carmichael (p ^ k p)"
    using primepow by (auto simp: P_def k_def prime_factors_multiplicity)
  hence "\<exists>g. \<forall>p\<in>P. coprime (p ^ k p) (g p) \<and> ord (p ^ k p) (g p) = Carmichael (p ^ k p)"
    by (subst (asm) bchoice_iff)
  then obtain g where g: "\<And>p. p \<in> P \<Longrightarrow> coprime (p ^ k p) (g p)"
                         "\<And>p. p \<in> P \<Longrightarrow> ord (p ^ k p) (g p) = Carmichael (p ^ k p)" by metis
  have "\<exists>x. \<forall>i\<in>P. [x = g i] (mod i ^ k i)"
    by (intro chinese_remainder_nat)
       (auto simp: P_def k_def in_prime_factors_iff primes_coprime)
  then obtain x where x: "\<And>p. p \<in> P \<Longrightarrow> [x = g p] (mod p ^ k p)" by metis

  have "n = (\<Prod>p\<in>P. p ^ k p)"
    using assms unfolding P_def k_def by (rule prime_factorization_nat)
  also have "ord \<dots> x = (LCM p\<in>P. ord (p ^ k p) x)"
    by (intro ord_modulus_prod_coprime) (auto simp: P_def in_prime_factors_iff primes_coprime)
  also have "(\<lambda>p. ord (p ^ k p) x) ` P = (\<lambda>p. ord (p ^ k p) (g p)) ` P"
    by (intro image_cong ord_cong x) auto
  also have "\<dots> = (\<lambda>p. Carmichael (p ^ k p)) ` P"
    by (intro image_cong g) auto
  also have "Lcm \<dots> = Carmichael (\<Prod>p\<in>P. p ^ k p)"
    by (intro Carmichael_prod_coprime [symmetric])
       (auto simp: P_def in_prime_factors_iff primes_coprime)
  also have "(\<Prod>p\<in>P. p ^ k p) = n"
    using assms unfolding P_def k_def by (rule prime_factorization_nat [symmetric])
  finally have "ord n x = Carmichael n" .
  moreover from this have "coprime n x"
    by (cases "coprime n x") (auto split: if_splits)
  ultimately show ?thesis using assms False
    by (intro that[of "x mod n"])
       (auto simp: totatives_def coprime_commute coprime_absorb_left intro!: Nat.gr0I)
qed

text \<open>
  This also means that the Carmichael number is not only the LCM of the orders
  of the elements of the residue ring, but indeed the maximum of the orders.
\<close>
lemma Carmichael_altdef:
  "Carmichael n = (if n = 0 then 1 else Max (ord n ` totatives n))"
proof (cases "n = 0")
  case False
  have "Carmichael n = Max (ord n ` totatives n)"
  proof (intro antisym Max.boundedI Max.coboundedI)
    fix k assume k: "k \<in> ord n ` totatives n"
    thus "k \<le> Carmichael n"
    proof (cases "n = 1")
      case False
      with \<open>n \<noteq> 0\<close> have "n > 1" by linarith
      thus ?thesis using k \<open>n \<noteq> 0\<close>
        by (intro dvd_imp_le)
           (auto intro!: ord_dvd_Carmichael simp: totatives_def coprime_commute)
    qed auto
  next
    obtain g where "g \<in> totatives n" and "ord n g = Carmichael n"
      using Carmichael_root_exists[of n] \<open>n \<noteq> 0\<close> by auto
    thus "Carmichael n \<in> ord n ` totatives n" by force
  qed (use \<open>n \<noteq> 0\<close> in auto)
  thus ?thesis using False by simp
qed auto


subsection \<open>Existence of primitive roots for general moduli\<close>

text \<open>
  We now related Carmichael's function to the existence of primitive roots and, in the end,
  use this to show precisely which moduli have primitive roots and which do not.

  The first criterion for the existence of a primitive root is this: A primitive root modulo $n$
  exists iff $\lambda(n) = \varphi(n)$.
\<close>
lemma Carmichael_eq_totient_imp_primroot:
  assumes "n > 0" and "Carmichael n = totient n"
  shows   "\<exists>g. residue_primroot n g"
proof -
  from \<open>n > 0\<close> obtain g where "g \<in> totatives n" and "ord n g = Carmichael n"
    using Carmichael_root_exists[of n] by metis
  with assms show ?thesis by (auto simp: residue_primroot_def totatives_def coprime_commute)
qed

theorem residue_primroot_iff_Carmichael:
  "(\<exists>g. residue_primroot n g) \<longleftrightarrow> Carmichael n = totient n \<and> n > 0"
proof safe
  fix g assume g: "residue_primroot n g"
  thus "n > 0" by (auto simp: residue_primroot_def)
  have "coprime n g" by (rule ccontr) (use g in \<open>auto simp: residue_primroot_def\<close>)

  show "Carmichael n = totient n"
  proof (cases "n = 1")
    case False
    with \<open>n > 0\<close> have "n > 1" by auto
    with \<open>coprime n g\<close> have "ord n g dvd Carmichael n"
      by (intro ord_dvd_Carmichael) auto
    thus ?thesis using g by (intro dvd_antisym Carmichael_dvd_totient)
                            (auto simp: residue_primroot_def)
  qed auto
qed (use Carmichael_eq_totient_imp_primroot[of n] in auto)

text \<open>
  Any primitive root modulo $mn$ for coprime $m$, $n$ is also a primitive root modulo $m$ and $n$.
  The converse does not hold in general.
\<close>
lemma residue_primroot_modulus_mult_coprimeD:
  assumes "coprime m n" and "residue_primroot (m * n) g"
  shows   "residue_primroot m g" "residue_primroot n g"
proof -
  have *: "m > 0" "n > 0" "coprime m g" "coprime n g"
          "lcm (ord m g) (ord n g) = totient m * totient n"
    using assms
    by (auto simp: residue_primroot_def ord_modulus_mult_coprime totient_mult_coprime)

  define a b where "a = totient m div ord m g" and "b = totient n div ord n g"
  have ab: "totient m = ord m g * a" "totient n = ord n g * b"
    using * by (auto simp: a_def b_def order_divides_totient)

  have "a = 1" "b = 1" "coprime (ord m g) (ord n g)"
    unfolding coprime_iff_gcd_eq_1 using * by (auto simp: ab lcm_nat_def dvd_div_eq_mult ord_eq_0)
  with ab and * show "residue_primroot m g" "residue_primroot n g"
    by (auto simp: residue_primroot_def)
qed

text \<open>
  If a primitive root modulo $mn$ exists for coprime $m, n$, then $\lambda(m)$ and $\lambda(n)$
  must also be coprime. This is helpful in establishing that there are no primitive roots
  modulo $mn$ by showing e.\,g.\ that $\lambda(m)$ and $\lambda(n)$ are both even.
\<close>
lemma residue_primroot_modulus_mult_coprime_imp_Carmichael_coprime:
  assumes "coprime m n" and "residue_primroot (m * n) g"
  shows   "coprime (Carmichael m) (Carmichael n)"
proof -
  from residue_primroot_modulus_mult_coprimeD[OF assms]
    have *: "residue_primroot m g" "residue_primroot n g" by auto
  hence [simp]: "Carmichael m = totient m" "Carmichael n = totient n"
    by (simp_all add: residue_primroot_Carmichael)
  from * have mn: "m > 0" "n > 0" by (auto simp: residue_primroot_def)
  
  from assms have "Carmichael (m * n) = totient (m * n) \<and> n > 0"
    using residue_primroot_iff_Carmichael[of "m * n"] by auto
  with assms have "lcm (totient m) (totient n) = totient m * totient n"
    by (simp add: Carmichael_mult_coprime totient_mult_coprime)
  thus ?thesis unfolding coprime_iff_gcd_eq_1 using mn
    by (simp add: lcm_nat_def dvd_div_eq_mult)
qed
  
text \<open>
  The following moduli are precisely those that have primitive roots.
\<close>
definition cyclic_moduli :: "nat set" where
  "cyclic_moduli = {1, 2, 4} \<union> {p ^ k |p k. prime p \<and> odd p \<and> k > 0} \<union>
                     {2 * p ^ k |p k. prime p \<and> odd p \<and> k > 0}"

theorem residue_primroot_iff_in_cyclic_moduli:
  "(\<exists>g. residue_primroot m g) \<longleftrightarrow> m \<in> cyclic_moduli"
proof -
  have "(\<exists>g. residue_primroot m g)" if "m \<in> cyclic_moduli"
  using that unfolding cyclic_moduli_def
  by (intro Carmichael_eq_totient_imp_primroot)
     (auto dest: prime_gt_0_nat simp: Carmichael_prime_power totient_prime_power
                 Carmichael_mult_coprime totient_mult_coprime)

  moreover have "\<not>(\<exists>g. residue_primroot m g)" if "m \<notin> cyclic_moduli"
  proof (cases "m = 0")
    case False
    with that have [simp]: "m > 0" "m \<noteq> 1" by (auto simp: cyclic_moduli_def)
    show ?thesis
    proof (cases "\<exists>k. m = 2 ^ k")
      case True
      then obtain k where [simp]: "m = 2 ^ k" by auto
      with that have "k \<noteq> 0 \<and> k \<noteq> 1 \<and> k \<noteq> 2" by (auto simp: cyclic_moduli_def)
      hence "k \<ge> 3" by auto
      thus ?thesis by (subst residue_primroot_iff_Carmichael)
                      (auto simp: Carmichael_twopow totient_prime_power)
    next
      case False
      hence "\<exists>p\<in>prime_factors m. p \<noteq> 2"
        using Ex_other_prime_factor[of m 2] by auto
      from divide_out_primepow_ex[OF \<open>m \<noteq> 0\<close> this]
      obtain p k m' where p: "p \<noteq> 2" "prime p" "p dvd m" "\<not>p dvd m'" "0 < k" "m = p ^ k * m'"
        by metis
      have "odd p"
        using p primes_dvd_imp_eq[of 2 p] by auto
      from p have coprime: "coprime (p ^ k) m'"
        using p prime_imp_coprime by auto
      have "m \<in> cyclic_moduli" if "m' = 1"
        using that p \<open>odd p\<close> by (auto simp: cyclic_moduli_def)
      moreover have "m \<in> cyclic_moduli" if "m' = 2"
      proof -
        have "m = 2 * p ^ k" using p that by (simp add: mult.commute)
        thus "m \<in> cyclic_moduli" using p \<open>odd p\<close>
          unfolding cyclic_moduli_def by blast
      qed
      moreover have "m' \<noteq> 0" using p by (intro notI) auto
      ultimately have "m' \<noteq> 0 \<and>m' \<noteq> 1 \<and> m' \<noteq> 2" using that by auto
      hence "m' > 2" by linarith
  
      show ?thesis
      proof
        assume "\<exists>g. residue_primroot m g"
        with coprime p have coprime': "coprime (p - 1) (Carmichael m')"
          using residue_primroot_modulus_mult_coprime_imp_Carmichael_coprime[OF coprime]
          by (auto simp: Carmichael_prime_power)
        moreover have "even (p - 1)" "even (Carmichael m')"
          using \<open>m' > 2\<close> \<open>odd p\<close> by (auto intro!: even_Carmichael)
        ultimately show False by force
      qed
    qed
  qed auto

  ultimately show ?thesis by metis
qed

lemma residue_primroot_is_generator:
  assumes "m > 1" and "residue_primroot m g"
  shows   "bij_betw (\<lambda>i. g ^ i mod m) {..<totient m} (totatives m)"
  unfolding bij_betw_def
proof
  from assms have [simp]: "ord m g = totient m"
    by (simp add: residue_primroot_def)
  from assms have "coprime m g" by (simp add: residue_primroot_def)
  hence "inj_on (\<lambda>i. g ^ i mod m) {..<ord m g}"
    by (intro inj_power_mod)
  thus inj: "inj_on (\<lambda>i. g ^ i mod m) {..<totient m}"
    by simp

  show "(\<lambda>i. g ^ i mod m) ` {..<totient m} = totatives m"
  proof (rule card_subset_eq)
    show "card ((\<lambda>i. g ^ i mod m) ` {..<totient m}) = card (totatives m)"
      using inj by (subst card_image) (auto simp: totient_def)
    show "(\<lambda>i. g ^ i mod m) ` {..<totient m} \<subseteq> totatives m"
      using \<open>m > 1\<close> \<open>coprime m g\<close> power_in_totatives[of m g] by blast
  qed auto
qed

text \<open>
  Given one primitive root \<open>g\<close>, all the primitive roots are powers $g^i$ for
  $1\leq i \leq \varphi(n)$ with $\text{gcd}(i, \varphi(n)) = 1$.
\<close>
theorem residue_primroot_bij_betw_primroots:
  assumes "m > 1" and "residue_primroot m g"
  shows   "bij_betw (\<lambda>i. g ^ i mod m) (totatives (totient m))
                                      {g\<in>totatives m. residue_primroot m g}"
proof (cases "m = 2")
  case [simp]: True
  have [simp]: "totatives 2 = {1}"
    by (auto simp: totatives_def elim!: oddE)
  from assms have "odd g"
    by (auto simp: residue_primroot_def)
  hence pow_eq: "(\<lambda>i. g ^ i mod m) = (\<lambda>_. 1)"
    by (auto simp: fun_eq_iff mod_2_eq_odd)
  have "{g \<in> totatives m. residue_primroot m g} = {1}"
    by (auto simp: residue_primroot_def)
  thus ?thesis using pow_eq by (auto simp: bij_betw_def)
next
  case False
  thus ?thesis unfolding bij_betw_def
  proof safe
    from assms False have "m > 2" by auto
    from assms \<open>m > 2\<close> have "totient m > 1" by (intro totient_gt_1) auto
    from assms have [simp]: "ord m g = totient m"
      by (simp add: residue_primroot_def)
    from assms have "coprime m g" by (simp add: residue_primroot_def)
    hence "inj_on (\<lambda>i. g ^ i mod m) {..<ord m g}"
      by (intro inj_power_mod)
    thus "inj_on (\<lambda>i. g ^ i mod m) (totatives (totient m))"
      by (rule inj_on_subset)
         (use assms \<open>totient m > 1\<close> in \<open>auto simp: totatives_less residue_primroot_def\<close>)

    {
      fix i assume i: "i \<in> totatives (totient m)"
      from \<open>coprime m g\<close> and \<open>m > 2\<close> show "g ^ i mod m \<in> totatives m"
        by (intro power_in_totatives) auto
      show "residue_primroot m (g ^ i mod m)"
        using i \<open>m > 2\<close> \<open>coprime m g\<close>
        by (auto simp: residue_primroot_def coprime_commute ord_power totatives_def)
    }
    {
      fix x assume x: "x \<in> totatives m" "residue_primroot m x"
      then obtain i where i: "i < totient m" "x = (g ^ i mod m)"
        using assms residue_primroot_is_generator[of m g] by (auto simp: bij_betw_def)
      from i x \<open>m > 2\<close> have "i > 0" by (intro Nat.gr0I) (auto simp: residue_primroot_1_iff)
      have "totient m div gcd i (totient m) = totient m"
        using x i \<open>coprime m g\<close> by (auto simp add: residue_primroot_def ord_power)
      hence "coprime i (totient m)"
        unfolding coprime_iff_gcd_eq_1 using assms by (subst (asm) dvd_div_eq_mult) auto
      with i \<open>i > 0\<close> have "i \<in> totatives (totient m)" by (auto simp: totatives_def)
      thus "x \<in> (\<lambda>i. g ^ i mod m) ` totatives (totient m)" using i by auto
    }
  qed
qed

text \<open>
  It follows from the above statement that any residue ring modulo \<open>n\<close> that \<^emph>\<open>has\<close> primitive roots
  has exactly $\varphi(\varphi(n))$ of them.
\<close>
corollary card_residue_primroots:
  assumes "\<exists>g. residue_primroot m g"
  shows   "card {g\<in>totatives m. residue_primroot m g} = totient (totient m)"
proof (cases "m = 1")
  case [simp]: True
  have "{g \<in> totatives m. residue_primroot m g} = {1}"
    by (auto simp: residue_primroot_def)
  thus ?thesis by simp
next
  case False
  from assms obtain g where g: "residue_primroot m g" by auto
  hence "m \<noteq> 0" by (intro notI) auto
  with \<open>m \<noteq> 1\<close> have "m > 1" by linarith
  from this g have "bij_betw (\<lambda>i. g ^ i mod m) (totatives (totient m))
                      {g\<in>totatives m. residue_primroot m g}"
    by (rule residue_primroot_bij_betw_primroots)
  hence "card (totatives (totient m)) = card {g\<in>totatives m. residue_primroot m g}"
    by (rule bij_betw_same_card)
  thus ?thesis by (simp add: totient_def)
qed

corollary card_residue_primroots':
  "card {g\<in>totatives m. residue_primroot m g} =
     (if m \<in> cyclic_moduli then totient (totient m) else 0)"
  by (simp add: residue_primroot_iff_in_cyclic_moduli [symmetric] card_residue_primroots)

text \<open>
  As an example, we evaluate $\lambda(122200)$ using the prime factorisation.
\<close>
lemma "Carmichael 122200 = 1380"
proof -
  have "prime_factorization (2^3 * 5^2 * 13 * 47) = {#2, 2, 2, 5, 5, 13, 47::nat#}"
    by (intro prime_factorization_eqI) auto
  from eval_Carmichael[OF this] show "Carmichael 122200 = 1380"
    by (simp add: lcm_nat_def gcd_non_0_nat)
qed

(* TODO: definition of index ("discrete logarithm") *)

end
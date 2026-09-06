section \<open>The characteristic of a ring; finite domains have prime characteristic\<close>

theory Characteristic
  imports Ring_Theory "HOL-Computational_Algebra.Primes"
begin

text \<open>The natural-number multiples @{text "n \<cdot> \<one>"} of the unit form a ring homomorphism
  @{text "\<nat> \<rightarrow> R"}.  Its kernel determines the \<^emph>\<open>characteristic\<close> of the ring; for a finite
  integral domain the characteristic is a prime, and the multiples @{text "n \<cdot> \<one>"} form the prime
  subfield.  This is the first step toward the structural theorem that a finite field has
  prime-power order.\<close>

context Ring
begin

text \<open>The @{term n}-fold sum @{text "\<one> + \<dots> + \<one>"} (@{term n} summands), i.e. the image of @{term n}
  under the canonical map @{text "\<nat> \<rightarrow> R"}.\<close>
definition natmult :: "nat \<Rightarrow> 'a"
  where "natmult n = (((+) \<one>) ^^ n) \<zero>"

lemma natmult_0 [simp]: "natmult 0 = \<zero>"
  by (simp add: natmult_def)

lemma natmult_Suc [simp]: "natmult (Suc n) = \<one> + natmult n"
  by (simp add: natmult_def)

lemma natmult_closed [simp]: "natmult n \<in> R"
  by (induct n) auto

lemma natmult_1 [simp]: "natmult 1 = \<one>"
  by simp

text \<open>Additivity: @{text "natmult (m + n) = natmult m + natmult n"}.\<close>
lemma natmult_add: "natmult (m + n) = natmult m + natmult n"
  by (induct m) (auto simp: additive.associative)

text \<open>Multiplicativity: @{text "natmult (m * n) = natmult m \<cdot> natmult n"}.\<close>
lemma natmult_mult: "natmult (m * n) = natmult m \<cdot> natmult n"
by (induct m) (auto simp: natmult_add distributive)

text \<open>Cancellation across a difference: if two multiples agree, the multiple of their difference
  vanishes.\<close>
lemma natmult_diff_zero:
  assumes "m \<le> n" and "natmult m = natmult n"
  shows "natmult (n - m) = \<zero>"
proof -
  have "natmult m + natmult (n - m) = natmult n"
    using natmult_add[of m "n - m"] le_add_diff_inverse[OF assms(1)] by simp
  also have "\<dots> = natmult m + \<zero>" using assms by (simp add: additive.right_unit)
  finally have "natmult m + natmult (n - m) = natmult m + \<zero>" .
  then show ?thesis
    using additive.invertible_left_cancel[of "natmult m" "natmult (n - m)" \<zero>] by simp
qed

end

context integral_domain
begin

text \<open>The \<^emph>\<open>characteristic\<close>: the least positive @{term n} with @{text "n \<cdot> \<one> = \<zero>"} (or @{text 0} if
  no such @{term n} exists).\<close>
definition characteristic :: nat
  where "characteristic = (LEAST n. 0 < n \<and> natmult n = \<zero>)"

text \<open>In a \<^emph>\<open>finite\<close> integral domain the map @{term natmult} cannot be injective, so some positive
  multiple of @{term \<one>} vanishes.\<close>
lemma finite_natmult_not_inj:
  assumes "finite R" shows "\<exists>n. 0 < n \<and> natmult n = \<zero>"
proof -
  have "\<not> inj natmult"
    by (meson assms image_subsetI infinite_iff_countable_subset natmult_closed)
  then obtain i j where ij: "i \<noteq> j" and eq: "natmult i = natmult j" by (auto simp: inj_def)
  show ?thesis
  proof (cases "i < j")
    case True
    then have "natmult (j - i) = \<zero>" using eq by (simp add: natmult_diff_zero)
    with True show ?thesis
      using zero_less_diff by blast
  next
    case False
    then have "natmult (i - j) = \<zero>"
      by (simp add: eq natmult_diff_zero)
    then show ?thesis
      by (meson False ij linorder_cases zero_less_diff)
  qed
qed

lemma characteristic_pos:
  assumes "finite R" shows "0 < characteristic \<and> natmult characteristic = \<zero>"
  unfolding characteristic_def
  using LeastI_ex[OF finite_natmult_not_inj[OF assms]] .

lemma characteristic_least:
  "\<lbrakk> 0 < n; natmult n = \<zero> \<rbrakk> \<Longrightarrow> characteristic \<le> n"
  unfolding characteristic_def by (rule Least_le) simp

text \<open>The characteristic exceeds @{text 1}: @{text "1 \<cdot> \<one> = \<one> \<noteq> \<zero>"} by nontriviality.\<close>
lemma characteristic_gt_1:
  assumes "finite R" shows "1 < characteristic"
  by (metis assms characteristic_pos nontrivial less_one nat_neq_iff natmult_1)

text \<open>\<^emph>\<open>The characteristic of a finite integral domain is prime.\<close>  If it factored as
  @{term "characteristic = a * b"} nontrivially, then @{text "natmult a \<cdot> natmult b = \<zero>"} would
  force one factor's multiple to vanish, contradicting minimality.\<close>
theorem characteristic_prime:
  assumes finR: "finite R" shows "prime characteristic"
proof (unfold prime_nat_iff, intro conjI allI impI)
  show "1 < characteristic" using characteristic_gt_1[OF finR] .
next
  fix m assume mdvd: "m dvd characteristic"
  then obtain k where ch: "characteristic = m * k" by (rule dvdE)
  have chz: "natmult characteristic = \<zero>" using characteristic_pos[OF finR] by simp
  have "natmult m \<cdot> natmult k = \<zero>" using chz ch by (simp add: natmult_mult)
  then have "natmult m = \<zero> \<or> natmult k = \<zero>" using no_zero_divisors by simp
  \<comment> \<open>Both @{term m} and @{term k} are positive (the product is positive).\<close>
  have cpos: "0 < characteristic" using characteristic_pos[OF finR] by simp
  have mpos: "0 < m" and kpos: "0 < k" using ch cpos by auto
  then show "m = 1 \<or> m = characteristic"
  proof (cases "natmult m = \<zero>")
    case True
    then show ?thesis
      using characteristic_least cpos dvd_imp_le le_antisym mdvd mpos by presburger
  next
    case False
    then have nk: "natmult k = \<zero>" using \<open>natmult m = \<zero> \<or> natmult k = \<zero>\<close> by simp
    have kdvd: "k dvd characteristic" using ch by auto
    have keq: "k = characteristic"
      by (simp add: characteristic_least cpos dvd_imp_le kdvd kpos le_antisym nk)
    then show ?thesis
      using ch cpos by force
  qed
qed

end

end

section \<open>Characteristic and Prime Subfields\<close>

theory Prime_Subfield
  imports Ring_Theory "HOL-Computational_Algebra.Primes" GF_p Divisibility_Theory
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

subsection \<open>The prime subfield\<close>

subsection \<open>Finite integral domains\<close>

text \<open>A finite integral domain is a field.  Multiplication by a nonzero element is an
  injective self-map of the finite carrier, hence surjective; a preimage of the unit is a
  multiplicative inverse.\<close>
theorem (in integral_domain) finite_integral_domain_imp_field:
  assumes fin: "finite R"
  shows "Field R (+) (\<cdot>) \<zero> \<one>"
proof (rule Field.intro[OF commutative_ring_axioms nontrivial_ring_axioms])
  show "Field_axioms R (\<cdot>) \<zero> \<one>"
  proof
    fix a
    assume aR: "a \<in> R" and anz: "a \<noteq> \<zero>"
    have inj: "inj_on ((\<cdot>) a) R"
      by (rule inj_onI) (rule mult_cancel_left[OF aR _ _ anz])
    have closed: "((\<cdot>) a) ` R \<subseteq> R"
      using aR by (blast intro: multiplicative.composition_closed)
    have "\<one> \<in> (\<cdot>) a ` R"
      using endo_inj_surj[OF fin closed inj] multiplicative.unit_closed by simp
    then obtain b where bR: "b \<in> R" and ab: "a \<cdot> b = \<one>" by blast
    have ba: "b \<cdot> a = \<one>"
      using multiplicative.commutative[OF bR aR] ab by simp
    show "multiplicative.invertible a"
      by (rule multiplicative.invertibleI[OF ab ba bR])
  qed
qed

text \<open>The characteristic map factors through the existing concrete field
  \<open>GF(characteristic)\<close>.  Its image is the canonical prime subfield of the finite
  domain.  This is the bridge between the carrier-set ring hierarchy and the finite-field
  constructions.\<close>

locale finite_integral_domain = integral_domain +
  assumes finite_carrier: "finite R"
begin

definition prime_subfield :: "'a set"
  where "prime_subfield = natmult ` {0..<characteristic}"

definition characteristic_embedding :: "nat \<Rightarrow> 'a"
  where "characteristic_embedding = restrict natmult {0..<characteristic}"

lemma natmult_characteristic_multiple:
  shows "natmult (k * characteristic) = \<zero>"
proof -
  have "natmult characteristic = \<zero>" using characteristic_pos[OF finite_carrier] by simp
  then show ?thesis by (simp add: natmult_mult)
qed

lemma natmult_mod_characteristic:
  shows "natmult (n mod characteristic) = natmult n"
proof -
  have n: "n = n div characteristic * characteristic + n mod characteristic"
    using div_mult_mod_eq[of n characteristic] by simp
  have "natmult n = natmult (n div characteristic * characteristic + n mod characteristic)"
    by (rule arg_cong[OF n])
  also have "\<dots> = natmult (n div characteristic * characteristic) + natmult (n mod characteristic)"
    by (rule natmult_add)
  also have "\<dots> = natmult (n mod characteristic)"
    using natmult_characteristic_multiple by simp
  finally show ?thesis by (rule sym)
qed

lemma natmult_inj_on_characteristic:
  shows "inj_on natmult {0..<characteristic}"
proof (rule inj_onI)
  fix m n
  assume m: "m \<in> {0..<characteristic}" and n: "n \<in> {0..<characteristic}"
    and eq: "natmult m = natmult n"
  show "m = n"
  proof (rule ccontr)
    assume "m \<noteq> n"
    consider (mn) "m < n" | (nm) "n < m" using \<open>m \<noteq> n\<close> by linarith
    then show False
    proof cases
      case mn
      have pos: "0 < n - m" using mn by simp
      have zero: "natmult (n - m) = \<zero>"
        using natmult_diff_zero[OF less_imp_le[OF mn] eq] .
      have "characteristic \<le> n - m" by (rule characteristic_least[OF pos zero])
      moreover have "n - m < characteristic" using n by simp
      ultimately show False by simp
    next
      case nm
      have pos: "0 < m - n" using nm by simp
      have zero: "natmult (m - n) = \<zero>"
        using natmult_diff_zero[OF less_imp_le[OF nm] eq[symmetric]] .
      have "characteristic \<le> m - n" by (rule characteristic_least[OF pos zero])
      moreover have "m - n < characteristic" using m by simp
      ultimately show False by simp
    qed
  qed
qed

lemma characteristic_embedding_add:
  assumes m: "m \<in> {0..<characteristic}" and n: "n \<in> {0..<characteristic}"
  shows "characteristic_embedding (gfp_add characteristic m n) =
    characteristic_embedding m + characteristic_embedding n"
proof -
  have cgt1: "characteristic > 1"
    using characteristic_prime[OF finite_carrier] by (simp add: prime_nat_iff)
  have closed: "gfp_add characteristic m n \<in> {0..<characteristic}"
    by (rule gfp_add_closed[OF cgt1])
  have "characteristic_embedding (gfp_add characteristic m n) =
      natmult ((m + n) mod characteristic)"
    using m n closed by (simp add: characteristic_embedding_def gfp_add_def)
  also have "\<dots> = natmult (m + n)" by (rule natmult_mod_characteristic)
  also have "\<dots> = natmult m + natmult n" by (rule natmult_add)
  also have "\<dots> = characteristic_embedding m + characteristic_embedding n"
    using m n by (simp add: characteristic_embedding_def)
  finally show ?thesis .
qed

lemma characteristic_embedding_mult:
  assumes m: "m \<in> {0..<characteristic}" and n: "n \<in> {0..<characteristic}"
  shows "characteristic_embedding (gfp_mult characteristic m n) =
    characteristic_embedding m \<cdot> characteristic_embedding n"
proof -
  have cgt1: "characteristic > 1"
    using characteristic_prime[OF finite_carrier] by (simp add: prime_nat_iff)
  have closed: "gfp_mult characteristic m n \<in> {0..<characteristic}"
    by (rule gfp_mult_closed[OF cgt1])
  have "characteristic_embedding (gfp_mult characteristic m n) =
      natmult ((m * n) mod characteristic)"
    using m n closed by (simp add: characteristic_embedding_def gfp_mult_def)
  also have "\<dots> = natmult (m * n)" by (rule natmult_mod_characteristic)
  also have "\<dots> = natmult m \<cdot> natmult n" by (rule natmult_mult)
  also have "\<dots> = characteristic_embedding m \<cdot> characteristic_embedding n"
    using m n by (simp add: characteristic_embedding_def)
  finally show ?thesis .
qed

theorem characteristic_embedding_monomorphism:
  shows "ring_monomorphism characteristic_embedding
    {0..<characteristic} (gfp_add characteristic) (gfp_mult characteristic) 0 1
    R (+) (\<cdot>) \<zero> \<one>"
proof (intro ring_monomorphism.intro)
  interpret GF: Field "{0..<characteristic}" "gfp_add characteristic" "gfp_mult characteristic" 0 1
    by (rule gfp_field[OF characteristic_prime[OF finite_carrier]])
  show "ring_homomorphism characteristic_embedding
      {0..<characteristic} (gfp_add characteristic) (gfp_mult characteristic) 0 1
      R (+) (\<cdot>) \<zero> \<one>"
  proof (intro ring_homomorphism.intro)
    show "Set_Theory.map characteristic_embedding {0..<characteristic} R"
      by unfold_locales (auto simp: characteristic_embedding_def)
    show "Ring {0..<characteristic} (gfp_add characteristic) (gfp_mult characteristic) 0 1"
      by (rule GF.Ring_axioms)
    show "Ring R (+) (\<cdot>) \<zero> \<one>" by (rule Ring_axioms)
    show "group_homomorphism characteristic_embedding
        {0..<characteristic} (gfp_add characteristic) 0 R (+) \<zero>"
    proof
      show "characteristic_embedding \<in> {0..<characteristic} \<rightarrow>\<^sub>E R"
        by (auto simp: characteristic_embedding_def)
      show "\<And>x y. \<lbrakk>x \<in> {0..<characteristic}; y \<in> {0..<characteristic}\<rbrakk> \<Longrightarrow>
          characteristic_embedding (gfp_add characteristic x y) =
          characteristic_embedding x + characteristic_embedding y"
        by (rule characteristic_embedding_add)
      show "characteristic_embedding 0 = \<zero>"
        using characteristic_pos[OF finite_carrier] by (simp add: characteristic_embedding_def)
    qed
    show "Monoid_homomorphism characteristic_embedding
        {0..<characteristic} (gfp_mult characteristic) 1 R (\<cdot>) \<one>"
    proof
      show "characteristic_embedding \<in> {0..<characteristic} \<rightarrow>\<^sub>E R"
        by (auto simp: characteristic_embedding_def)
      show "\<And>x y. \<lbrakk>x \<in> {0..<characteristic}; y \<in> {0..<characteristic}\<rbrakk> \<Longrightarrow>
          characteristic_embedding (gfp_mult characteristic x y) =
          characteristic_embedding x \<cdot> characteristic_embedding y"
        by (rule characteristic_embedding_mult)
      show "characteristic_embedding 1 = \<one>"
        using characteristic_prime[OF finite_carrier]
        by (simp add: characteristic_embedding_def prime_nat_iff)
    qed
  qed
  show "injective_map characteristic_embedding {0..<characteristic} R"
  proof
    show "characteristic_embedding \<in> {0..<characteristic} \<rightarrow>\<^sub>E R"
      by (auto simp: characteristic_embedding_def)
    show "inj_on characteristic_embedding {0..<characteristic}"
      using natmult_inj_on_characteristic
      by (simp add: characteristic_embedding_def inj_on_def)
  qed
qed

lemma characteristic_embedding_image:
  "characteristic_embedding ` {0..<characteristic} = prime_subfield"
  by (auto simp: characteristic_embedding_def prime_subfield_def)

theorem prime_subfield_subring:
  shows "Subring prime_subfield R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret E: ring_monomorphism characteristic_embedding
    "{0..<characteristic}" "gfp_add characteristic" "gfp_mult characteristic" 0 1
    R addition multiplication zero unit
    by (rule characteristic_embedding_monomorphism)
  show ?thesis using E.image.Subring_axioms by (simp add: characteristic_embedding_image)
qed

theorem prime_subfield_field:
  shows "Field prime_subfield (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret P: Subring prime_subfield R addition multiplication zero unit
    by (rule prime_subfield_subring)
  have ag: "Abelian_Group prime_subfield (+) \<zero>"
  proof -
    interpret A: Group prime_subfield addition zero
      by (rule P.additive.sub.Group_axioms)
    show ?thesis
    proof
      fix x y
      assume x: "x \<in> prime_subfield" and y: "y \<in> prime_subfield"
      show "x + y = y + x"
        by (rule additive.commutative[OF
              subsetD[OF P.additive.subset x] subsetD[OF P.additive.subset y]])
    qed
  qed
  have ring: "Ring prime_subfield (+) (\<cdot>) \<zero> \<one>"
  proof (intro Ring.intro)
    show "Abelian_Group prime_subfield (+) \<zero>" by (rule ag)
    show "Monoid prime_subfield (\<cdot>) \<one>"
      by (rule P.multiplicative.sub.Monoid_axioms)
    show "Ring_axioms prime_subfield (+) (\<cdot>)"
    proof
      fix a b c
      assume a: "a \<in> prime_subfield" and b: "b \<in> prime_subfield"
        and c: "c \<in> prime_subfield"
      show "a \<cdot> (b + c) = a \<cdot> b + a \<cdot> c"
        by (rule distributive(1)[OF subsetD[OF P.additive.subset a]
              subsetD[OF P.additive.subset b] subsetD[OF P.additive.subset c]])
      show "(b + c) \<cdot> a = b \<cdot> a + c \<cdot> a"
        by (rule distributive(2)[OF subsetD[OF P.additive.subset a]
              subsetD[OF P.additive.subset b] subsetD[OF P.additive.subset c]])
    qed
  qed
  have cr: "commutative_ring prime_subfield (+) (\<cdot>) \<zero> \<one>"
  proof -
    interpret S: Ring prime_subfield addition multiplication zero unit by (rule ring)
    show ?thesis
    proof
      fix x y
      assume x: "x \<in> prime_subfield" and y: "y \<in> prime_subfield"
      show "x \<cdot> y = y \<cdot> x"
        by (rule multiplicative.commutative[OF
              subsetD[OF P.multiplicative.subset x]
              subsetD[OF P.multiplicative.subset y]])
    qed
  qed
  interpret C: commutative_ring prime_subfield addition multiplication zero unit by (rule cr)
  have nt: "nontrivial_ring prime_subfield (+) (\<cdot>) \<zero> \<one>"
  proof
    show "\<one> \<noteq> \<zero>" by (rule nontrivial)
  qed
  interpret N: nontrivial_ring prime_subfield addition multiplication zero unit by (rule nt)
  have dom: "integral_domain prime_subfield (+) (\<cdot>) \<zero> \<one>"
  proof
    fix a b
    assume a: "a \<in> prime_subfield" and b: "b \<in> prime_subfield"
      and zero: "a \<cdot> b = \<zero>"
    show "a = \<zero> \<or> b = \<zero>"
      by (rule no_zero_divisors[OF subsetD[OF P.additive.subset a]
            subsetD[OF P.additive.subset b] zero])
  qed
  interpret D: integral_domain prime_subfield addition multiplication zero unit by (rule dom)
  have "finite prime_subfield" unfolding prime_subfield_def by simp
  then show ?thesis by (rule D.finite_integral_domain_imp_field)
qed

theorem card_prime_subfield:
  shows "card prime_subfield = characteristic"
  unfolding prime_subfield_def
  using natmult_inj_on_characteristic by (simp add: card_image)

end

end

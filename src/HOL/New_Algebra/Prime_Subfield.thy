section \<open>The prime subfield of a finite integral domain\<close>

theory Prime_Subfield
  imports Finite_Domain Characteristic GF_p
begin

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

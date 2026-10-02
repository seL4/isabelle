section \<open>Frobenius on finite subfields\<close>

theory Finite_Field_Frobenius
  imports Prime_Subfield Steinitz Field_Mult_Cyclic Extension_Vector_Space
begin

subsection \<open>Cardinality of finite fields\<close>

context Field
begin

text \<open>A finite field is a finite-dimensional vector space over its canonical prime
  subfield.  Taking the whole carrier as an initial finite spanning set supplies a basis;
  the coordinate bijection then counts the field.\<close>
theorem finite_field_cardinality:
  assumes fin: "finite R"
  shows "\<exists>n>0. card R = characteristic ^ n"
proof -
  interpret F: finite_integral_domain R addition multiplication zero unit
    by unfold_locales (rule fin)
  interpret P: Field F.prime_subfield addition multiplication zero unit
    by (rule F.prime_subfield_field)
  interpret S: Subring F.prime_subfield R addition multiplication zero unit
    by (rule F.prime_subfield_subring)
  have sub: "F.prime_subfield \<subseteq> R" by (rule S.additive.subset)
  interpret V: Vector_Space F.prime_subfield addition multiplication zero unit
      addition zero R multiplication
  proof (intro Vector_Space.intro Vector_Space_axioms.intro)
    show "Field F.prime_subfield (+) (\<cdot>) \<zero> \<one>" by (rule P.Field_axioms)
    show "Abelian_Group R (+) \<zero>" by (rule additive.Abelian_Group_axioms)
  next
    fix a v
    assume a: "a \<in> F.prime_subfield" and v: "v \<in> R"
    have aR: "a \<in> R" by (rule subsetD[OF sub a])
    show "a \<cdot> v \<in> R" by (rule multiplicative.composition_closed[OF aR v])
  next
    fix a u v
    assume a: "a \<in> F.prime_subfield" and u: "u \<in> R" and v: "v \<in> R"
    have aR: "a \<in> R" by (rule subsetD[OF sub a])
    show "a \<cdot> (u + v) = a \<cdot> u + a \<cdot> v"
      by (rule distributive(1)[OF aR u v])
  next
    fix a b v
    assume a: "a \<in> F.prime_subfield" and b: "b \<in> F.prime_subfield" and v: "v \<in> R"
    show "(a + b) \<cdot> v = a \<cdot> v + b \<cdot> v"
      by (rule distributive(2)[OF v subsetD[OF sub a] subsetD[OF sub b]])
  next
    fix a b v
    assume a: "a \<in> F.prime_subfield" and b: "b \<in> F.prime_subfield" and v: "v \<in> R"
    show "a \<cdot> b \<cdot> v = a \<cdot> (b \<cdot> v)"
      by (rule multiplicative.associative[OF subsetD[OF sub a] subsetD[OF sub b] v])
  next
    fix v assume v: "v \<in> R"
    show "\<one> \<cdot> v = v" by (rule multiplicative.left_unit[OF v])
  qed
  have count: "card R = card F.prime_subfield ^ V.dimension"
    by (rule V.card_eq_card_base_pow_dimension[OF fin])
  have count_char: "card R = characteristic ^ V.dimension"
    using count F.card_prime_subfield by simp
  have pair_sub: "{\<zero>, \<one>} \<subseteq> R" by auto
  have pair_card: "card {\<zero>, \<one>} = 2" using nontrivial by simp
  have card_ge2: "2 \<le> card R"
    using card_mono[OF fin pair_sub] pair_card by simp
  have dimension_pos: "V.dimension > 0"
  proof (rule ccontr)
    assume "\<not> V.dimension > 0"
    then have "V.dimension = 0" by simp
    then have "card R = 1" using count_char by simp
    then show False using card_ge2 by simp
  qed
  show ?thesis using count_char dimension_pos by blast
qed

corollary finite_field_cardinality_prime_power:
  assumes fin: "finite R"
  shows "\<exists>p n. prime p \<and> n > 0 \<and> card R = p ^ n"
proof -
  obtain n where n: "n > 0" "card R = characteristic ^ n"
    using finite_field_cardinality[OF fin] by blast
  have "prime characteristic" by (rule characteristic_prime[OF fin])
  then show ?thesis using n by blast
qed

corollary characteristic_dvd_card_finite_field:
  assumes fin: "finite R"
  shows "characteristic dvd card R"
proof -
  obtain n where n: "n > 0" "card R = characteristic ^ n"
    using finite_field_cardinality[OF fin] by blast
  have "characteristic dvd characteristic ^ n" using n(1) by (cases n) simp_all
  then show ?thesis using n(2) by simp
qed

end


text \<open>
  A finite subfield is represented here as a carrier set inside an ambient type-class field.
  The existing finite-field cardinality theorem therefore speaks about the characteristic of
  the carrier-set locale.  The first lemmas identify those two presentations; the remaining results
  expose Frobenius without introducing a second field representation.
\<close>

definition frobenius_power :: "nat \<Rightarrow> 'a :: monoid_mult \<Rightarrow> 'a"
  where "frobenius_power q x = x ^ q"

context Subfield
begin

interpretation carrier: Field K "(+)" "(*)" 0 1
  by (rule sf_field)

lemma carrier_natmult_eq_of_nat:
  "carrier.natmult n = of_nat n"
  by (induction n) simp_all

lemma carrier_characteristic_eq_CHAR:
  assumes fin: "finite K"
  shows "carrier.characteristic = CHAR('a)"
proof -
  have small_nz: False
    if "0 < n" and "n < carrier.characteristic" and "of_nat n = (0 :: 'a)" for n
      using that carrier.characteristic_least carrier_natmult_eq_of_nat 
       linorder_not_less by auto
  then show ?thesis
    using carrier.characteristic_pos[OF fin] carrier_natmult_eq_of_nat by (metis CHAR_eq_posI)
qed

theorem finite_subfield_cardinality_char_power:
  assumes fin: "finite K"
  shows "\<exists>n>0. card K = CHAR('a) ^ n"
  using carrier.finite_field_cardinality[OF fin]
  by (simp add: carrier_characteristic_eq_CHAR[OF fin])

lemma finite_subfield_CHAR_prime:
  assumes fin: "finite K"
  shows "prime CHAR('a)"
  using carrier.characteristic_prime[OF fin]
  by (simp add: carrier_characteristic_eq_CHAR[OF fin])

end

lemma frobenius_power_add_char_power:
  fixes x y :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "frobenius_power q (x + y) = frobenius_power q x + frobenius_power q y"
  by (simp add: char freshmans_dream' frobenius_power_def q)

lemma frobenius_power_mult:
  fixes x y :: "'a :: comm_monoid_mult"
  shows "frobenius_power q (x * y) = frobenius_power q x * frobenius_power q y"
  by (simp add: frobenius_power_def power_mult_distrib)

lemma frobenius_power_one [simp]:
  "frobenius_power q (1 :: 'a :: monoid_mult) = 1"
  by (simp add: frobenius_power_def)

lemma frobenius_power_zero [simp]:
  assumes "q > 0"
  shows "frobenius_power q (0 :: 'a :: semiring_1) = 0"
  using assms by (simp add: frobenius_power_def zero_power)

lemma frobenius_power_uminus_char_power:
  fixes x :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "frobenius_power q (-x) = - (frobenius_power q x)"
  using char q by (metis add_cancel_left_left eq_neg_iff_add_eq_0 frobenius_power_add_char_power)

lemma frobenius_power_inj:
  fixes x y :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
    and eq: "frobenius_power q x = frobenius_power q y"
  shows "x = y"
proof -
  have "frobenius_power q (x - y) = frobenius_power q x - frobenius_power q y"
    using char q by (metis frobenius_power_add_char_power frobenius_power_uminus_char_power uminus_add_conv_diff)
  with eq show ?thesis
    by (simp add: frobenius_power_def)
qed

context Subfield
begin

interpretation carrier: Field K "(+)" "(*)" 0 1
  by (rule sf_field)

lemma frobenius_power_closed:
  "x \<in> K \<Longrightarrow> frobenius_power q x \<in> K"
  unfolding frobenius_power_def by (rule power_closed)

lemma finite_frobenius_bij_betw:
  assumes fin: "finite K" and char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "bij_betw (frobenius_power q) K K"
proof -
  have inj: "inj_on (frobenius_power q) K"
    using frobenius_power_inj[OF char q] by (auto simp: inj_on_def)
  have image: "frobenius_power q ` K = K"
    using fin frobenius_power_closed inj by (meson endo_inj_surj image_subset_iff)
  show ?thesis
    by (simp add: bij_betw_def inj image)
qed

lemma finite_field_frobenius_identity:
  assumes fin: "finite K" and xK: "x \<in> K"
  shows "frobenius_power (card K) x = x"
proof -
  have gt0: "card K > 0"
    using fin zero_closed card_gt_0_iff by blast
  show ?thesis
  proof (cases "x = 0")
    case True
    with gt0 show ?thesis by simp
  next
    case False
    have carrier_power: "carrier.multiplicative.power x (card carrier.Fstar) = 1"
      using False Group.power_order_eq_1 carrier.Group_Fstar xK by fastforce
    have ambient_power: "carrier.multiplicative.power x n = x ^ n" for n
      by (induction n) simp_all
    with gt0 obtain "x ^ (card K - 1) = 1" "card K = Suc (card K - 1)"
      using carrier_power carrier.Fstar_def by force
    then show ?thesis
      by (metis frobenius_power_def mult.comm_neutral power_Suc)
  qed
qed

end


end

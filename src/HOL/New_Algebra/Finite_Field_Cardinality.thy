section \<open>Cardinality of finite fields\<close>

theory Finite_Field_Cardinality
  imports Prime_Subfield Steinitz
begin

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

end

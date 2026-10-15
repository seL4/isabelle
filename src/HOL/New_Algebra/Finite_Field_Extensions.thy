section \<open>Finite Fields and Their Extensions\<close>

theory Finite_Field_Extensions
  imports Prime_Subfield Steinitz Field_Mult_Cyclic Extension_Vector_Space
    Extension_Properties Algebraic_Transitivity
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

subsection \<open>Finite field extensions\<close>

text \<open>
  The polynomial \<open>X ^ card K - X\<close> packages the two decisive properties of a finite
  subfield \<open>K\<close>: every element of the carrier is a root, and there can be no further roots.
  Its derivative is \<open>-1\<close>, so minimal polynomials of elements of finite extensions divide
  a root-squarefree polynomial.  This yields separability and normality directly in the native
  carrier-set representation.
\<close>

definition finite_field_vanishing_poly :: "'a :: field set \<Rightarrow> 'a poly"
  where "finite_field_vanishing_poly K \<equiv> monom 1 (card K) - monom 1 1"

lemma poly_finite_field_vanishing_poly [simp]:
  "poly (finite_field_vanishing_poly K) x = x ^ card K - x"
  by (simp add: finite_field_vanishing_poly_def poly_monom)

lemma finite_field_vanishing_poly_nonzero:
  assumes "card K > 1"
  shows "finite_field_vanishing_poly K \<noteq> (0 :: 'a :: field poly)"
proof
  assume zero: "finite_field_vanishing_poly K = (0 :: 'a poly)"
  have one_coeff: "coeff (finite_field_vanishing_poly K) (card K) = 1"
    using assms by (simp add: finite_field_vanishing_poly_def coeff_monom)
  with zero show False by auto
qed

lemma degree_finite_field_vanishing_poly:
  assumes "card K > 1"
  shows "degree (finite_field_vanishing_poly K :: 'a :: field poly) = card K"
proof -
  have upper: "degree (finite_field_vanishing_poly K :: 'a poly) \<le> card K"
    unfolding finite_field_vanishing_poly_def
  proof (rule degree_diff_le)
    show "degree (monom (1 :: 'a) (card K)) \<le> card K"
      by (rule degree_monom_le)
    with assms show "degree (monom (1 :: 'a) 1) \<le> card K"
      using degree_monom_le dual_order.strict_trans2 less_or_eq_imp_le by blast
  qed
  have leading: "coeff (finite_field_vanishing_poly K :: 'a poly) (card K) = 1"
    using assms by (simp add: finite_field_vanishing_poly_def coeff_monom)
  have lower: "card K \<le> degree (finite_field_vanishing_poly K :: 'a poly)"
    by (simp add: le_degree leading)
  show ?thesis by (rule antisym[OF upper lower])
qed

text \<open>Over any field, at most \<open>m\<close> elements are fixed by the \<open>m\<close>-power map
  when \<open>m > 1\<close>.  This root bound later distinguishes the proper iterates of Frobenius.\<close>
lemma card_power_fixed_points_le:
  fixes m :: nat
  assumes m: "m > 1"
  shows "finite {x :: 'a :: field. x ^ m = x} \<and> card {x :: 'a. x ^ m = x} \<le> m"
proof -
  define p where "p = (monom 1 m - monom 1 1 :: 'a poly)"
  have p0: "p \<noteq> 0"
  proof
    assume zero: "p = 0"
    have zero_coeff: "coeff p m = 0" using zero by simp
    have one_coeff: "coeff p m = 1"
      using m by (simp add: p_def coeff_monom)
    show False using zero_coeff one_coeff by simp
  qed
  have upper: "degree p \<le> m"
    unfolding p_def
    by (metis m degree_diff_le degree_monom_eq degree_monom_le monom_eq_0_iff order_less_imp_le)
  have lower: "m \<le> degree p"
    using m by (simp add: le_degree p_def coeff_monom)
  have degree: "degree p = m" by (rule antisym[OF upper lower])
  have roots: "{x. poly p x = 0} = {x. x ^ m = x}"
    by (auto simp: p_def poly_monom)
  have finite_roots: "finite {x. poly p x = 0}"
    by (rule poly_roots_finite[OF p0])
  have bound: "card {x. poly p x = 0} \<le> m"
    using degree p0 poly_roots_degree by auto
  show ?thesis using finite_roots bound roots by simp
qed

text \<open>A root of multiplicity at least two is also a root of the formal derivative.
  Only this direction is characteristic-independent; it is the direction needed below.\<close>
lemma order_ge_two_imp_pderiv_root:
  fixes p :: "'a :: field poly"
  assumes p0: "p \<noteq> 0" and two: "2 \<le> order a p"
  shows "poly (pderiv p) a = 0"
proof -
  have "Suc (Suc 0) \<le> order a p" using two by simp
  then obtain r where p: "p = [:-a, 1:] ^ Suc (Suc 0) * r"
    using order_divides by blast
  have "poly (pderiv p) a = poly ([:-a, 1:] ^ Suc (Suc 0)) a * poly (pderiv r) a +
      poly r a * poly (pderiv ([:-a, 1:] ^ Suc (Suc 0))) a"
    by (metis (no_types) p pderiv_mult poly_add poly_mult)
  also have "... = 0"
    by (force simp: pderiv_pCons)
  finally show ?thesis .
qed

context Subfield
begin

lemma finite_field_vanishing_poly_over:
  "finite_field_vanishing_poly K \<in> poly_over K"
  unfolding finite_field_vanishing_poly_def
  by (intro poly_over_diff poly_over_monom one_closed)

lemma finite_field_vanishing_poly_roots:
  assumes fin: "finite K"
  shows "{x. poly (finite_field_vanishing_poly K) x = 0} = K"
proof -
  have K_roots: "K \<subseteq> {x. poly (finite_field_vanishing_poly K) x = 0}"
    using finite_field_frobenius_identity[OF fin]
    by (auto simp: frobenius_power_def)
  have p0: "finite_field_vanishing_poly K \<noteq> 0"
    using cardK_gt1 fin finite_field_vanishing_poly_nonzero by blast
  have fin_roots: "finite {x. poly (finite_field_vanishing_poly K) x = 0}"
    by (rule poly_roots_finite[OF p0])
  have card_roots_le: "card {x. poly (finite_field_vanishing_poly K) x = 0} \<le> card K"
    using poly_roots_degree[OF p0] cardK_gt1 assms
    by (simp add: degree_finite_field_vanishing_poly)
  have cardK_le:
      "card K \<le> card {x. poly (finite_field_vanishing_poly K) x = 0}"
    by (rule card_mono[OF fin_roots K_roots])
  then show ?thesis
    using K_roots card_roots_le fin_roots by (metis card_seteq)
qed

lemma finite_field_vanishing_poly_rsquarefree:
  assumes fin: "finite K"
  shows "rsquarefree (finite_field_vanishing_poly K)"
proof -
  obtain n where n: "n > 0" "card K = CHAR('a) ^ n"
    using finite_subfield_cardinality_char_power[OF fin] by blast
  have deriv: "pderiv (finite_field_vanishing_poly K) = -1"
    unfolding finite_field_vanishing_poly_def
    by (simp add: pderiv_diff pderiv_monom n)
  have pair: "{0, 1} \<subseteq> K" by auto
  have p0: "finite_field_vanishing_poly K \<noteq> 0"
    using deriv by force
  show ?thesis
    unfolding rsquarefree_def
  proof (intro conjI allI p0)
    fix x
    show "order x (finite_field_vanishing_poly K) = 0 \<or> order x (finite_field_vanishing_poly K) = 1"
    proof (cases "poly (finite_field_vanishing_poly K) x = 0")
      case False
      then show ?thesis
        using False by (simp add: order_eq_0_iff[OF p0])
    next
      case True
      have opos: "order x (finite_field_vanishing_poly K) > 0"
        using True by (simp add: order_gt_0_iff[OF p0])
      have not_two: "\<not> 2 \<le> order x (finite_field_vanishing_poly K)"
        using deriv order_1_eq_0 order_ge_two_imp_pderiv_root p0 by fastforce
      with opos show ?thesis by auto
    qed
  qed
qed

end

lemma finite_field_vanishing_poly_over_subfield:
  fixes F K :: "'a :: field set"
  assumes sfF: "Subfield F"
  shows "finite_field_vanishing_poly K \<in> poly_over F"
  by (simp add: Subfield.one_closed Subfield.poly_over_diff Subfield.poly_over_monom
      finite_field_vanishing_poly_def sfF)

text \<open>Every finite carrier extension is separable over each of its subfields.  The
  minimal polynomial of an element of the top field divides the top field's vanishing
  polynomial, whose roots are all simple.\<close>
theorem finite_subfield_extension_separable:
  fixes F K :: "'a :: field set"
  assumes sfF: "Subfield F" and sfK: "Subfield K" and FK: "F \<subseteq> K"
    and finK: "finite K"
  shows "separable_extension K F"
proof (rule separable_extensionI)
  interpret T: subfield_tower F K
    by (intro subfield_tower.intro subfield_tower_axioms.intro sfF sfK FK)
  interpret F: Subfield F by (rule sfF)
  interpret K: Subfield K by (rule sfK)
  fix a
  assume aK: "a \<in> K" and alg: "algebraic_over F a"
  have qF: "finite_field_vanishing_poly K \<in> poly_over F"
    by (rule finite_field_vanishing_poly_over_subfield[OF sfF])
  have qa: "poly (finite_field_vanishing_poly K) a = 0"
    using Subfield.finite_field_frobenius_identity[OF sfK finK aK]
    by (simp add: frobenius_power_def)
  have "minpoly F a dvd finite_field_vanishing_poly K"
    using T.base.is_minpoly_minpoly T.base.minpoly_dvd alg qF qa by blast
  then show "rsquarefree (minpoly F a)"
    using T.ext.finite_field_vanishing_poly_rsquarefree finK rsquarefree_dvd by blast
qed

text \<open>Likewise every finite carrier extension is normal over each of its subfields.
  Any irreducible polynomial with one root in the top field has its minimal polynomial as
  an associate; that minimal polynomial divides the same vanishing polynomial, whose entire
  root set is the top carrier.\<close>
theorem finite_subfield_extension_normal:
  fixes F K :: "'a :: field set"
  assumes sfF: "Subfield F" and sfK: "Subfield K" and FK: "F \<subseteq> K"
    and finK: "finite K"
  shows "normal_extension K F"
proof (rule normal_extensionI)
  interpret T: subfield_tower F K
    by (intro subfield_tower.intro subfield_tower_axioms.intro sfF sfK FK)
  interpret F: Subfield F by (rule sfF)
  interpret K: Subfield K by (rule sfK)
  fix p a
  assume pF: "p \<in> poly_over F" and irr: "irreducible_over F p"
    and aK: "a \<in> K" and pa: "poly p a = 0"
  have p0: "p \<noteq> 0"
    using irr by (auto simp: irreducible_over_def)
  have min: "is_minpoly F a (minpoly F a)"
    using T.base.is_minpoly_minpoly algebraic_over_def p0 pF pa by auto
  have qF: "finite_field_vanishing_poly K \<in> poly_over F"
    by (rule finite_field_vanishing_poly_over_subfield[OF sfF])
  have qa: "poly (finite_field_vanishing_poly K) a = 0"
    using Subfield.finite_field_frobenius_identity[OF sfK finK aK]
    by (simp add: frobenius_power_def)
  obtain c where qeq: "finite_field_vanishing_poly K = minpoly F a * c"
    using Subfield.minpoly_dvd[OF sfF min qF qa] by (auto simp: dvd_def)
  show "poly_root_set p \<subseteq> K"
  proof
    fix b assume bp: "b \<in> poly_root_set p"
    then have minb: "poly (minpoly F a) b = 0"
      using T.base.irreducible_over_root_is_minpoly_root irr min pF pa poly_root_set_iff by blast
    have roots: "{x. poly (finite_field_vanishing_poly K) x = 0} = K"
      by (rule Subfield.finite_field_vanishing_poly_roots[OF sfK finK])
    show "b \<in> K"
      using minb qeq roots by auto
  qed
qed

theorem finite_field_extension_cardinality:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "card K = card F ^ finite_subfield_tower.extension_degree F K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  show ?thesis by (rule T.finite_extension_cardinality[OF finK])
qed

theorem finite_field_extension_separable:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "separable_extension K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  show ?thesis
    by (simp add: T.base.Subfield_axioms T.base_subset T.ext.Subfield_axioms finK
        finite_subfield_extension_separable)
qed

theorem finite_field_extension_normal:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "normal_extension K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  then show ?thesis
    by (simp add: T.base.Subfield_axioms T.base_subset T.ext.Subfield_axioms
        finite_subfield_extension_normal)
qed

end

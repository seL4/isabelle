section \<open>Finite field extensions\<close>

theory Finite_Field_Extensions
  imports Finite_Field_Frobenius Extension_Properties Algebraic_Transitivity
begin

text \<open>
  The polynomial \<open>X ^ card K - X\<close> packages the two decisive properties of a finite
  subfield \<open>K\<close>: every element of the carrier is a root, and there can be no further roots.
  Its derivative is \<open>-1\<close>, so minimal polynomials of elements of finite extensions divide
  a root-squarefree polynomial.  This yields separability and normality directly in the native
  carrier-set representation.
\<close>

definition finite_field_vanishing_poly :: "'a :: field set \<Rightarrow> 'a poly"
  where "finite_field_vanishing_poly K = monom 1 (card K) - monom 1 1"

lemma poly_finite_field_vanishing_poly [simp]:
  "poly (finite_field_vanishing_poly K) x = x ^ card K - x"
  by (simp add: finite_field_vanishing_poly_def poly_monom)

lemma finite_field_vanishing_poly_nonzero:
  assumes "card K > 1"
  shows "finite_field_vanishing_poly K \<noteq> (0 :: 'a :: field poly)"
proof
  assume zero: "finite_field_vanishing_poly K = (0 :: 'a poly)"
  have zero_coeff: "coeff (finite_field_vanishing_poly K) (card K) = 0"
    using zero by simp
  have one_coeff: "coeff (finite_field_vanishing_poly K) (card K) = 1"
    using assms by (simp add: finite_field_vanishing_poly_def coeff_monom)
  show False using zero_coeff one_coeff by simp
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
    have "degree (monom (1 :: 'a) 1) \<le> 1"
      by (rule degree_monom_le)
    with assms show "degree (monom (1 :: 'a) 1) \<le> card K" by simp
  qed
  have leading:
      "coeff (finite_field_vanishing_poly K :: 'a poly) (card K) = 1"
    using assms by (simp add: finite_field_vanishing_poly_def coeff_monom)
  have lower: "card K \<le> degree (finite_field_vanishing_poly K :: 'a poly)"
    by (rule le_degree) (simp add: leading)
  show ?thesis by (rule antisym[OF upper lower])
qed

text \<open>Over any field, at most \<open>m\<close> elements are fixed by the \<open>m\<close>-power map
  when \<open>m > 1\<close>.  This root bound later distinguishes the proper iterates of Frobenius.\<close>
lemma card_power_fixed_points_le:
  fixes m :: nat
  assumes m: "m > 1"
  shows "finite {x :: 'a :: field. x ^ m = x} \<and>
    card {x :: 'a. x ^ m = x} \<le> m"
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
  proof (rule degree_diff_le)
    show "degree (monom (1 :: 'a) m) \<le> m" by (rule degree_monom_le)
    have "degree (monom (1 :: 'a) 1) \<le> 1" by (rule degree_monom_le)
    with m show "degree (monom (1 :: 'a) 1) \<le> m" by simp
  qed
  have leading: "coeff p m = 1"
    using m by (simp add: p_def coeff_monom)
  have lower: "m \<le> degree p"
    by (rule le_degree) (simp add: leading)
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
  have two': "Suc (Suc 0) \<le> order a p" using two by simp
  have dvd: "[:-a, 1:] ^ Suc (Suc 0) dvd p"
    by (rule order_divides[THEN iffD2], rule disjI2, rule two')
  then obtain r where p: "p = [:-a, 1:] ^ Suc (Suc 0) * r"
    by (auto simp: dvd_def)
  have linear_root: "poly [:-a, 1:] a = 0" by simp
  have deriv_square_root: "poly (pderiv ([:-a, 1:] ^ Suc (Suc 0))) a = 0"
    by (subst pderiv_power_Suc) (simp add: poly_mult linear_root)
  have deriv_p:
      "pderiv p = [:-a, 1:] ^ Suc (Suc 0) * pderiv r +
        r * pderiv ([:-a, 1:] ^ Suc (Suc 0))"
    using p by (subst p) (rule pderiv_mult)
  have square_root: "poly ([:-a, 1:] ^ Suc (Suc 0)) a = 0"
    by (simp only: poly_power linear_root zero_power)
  have "poly (pderiv p) a =
      poly ([:-a, 1:] ^ Suc (Suc 0) * pderiv r +
        r * pderiv ([:-a, 1:] ^ Suc (Suc 0))) a"
    by (simp only: deriv_p)
  also have "... = poly ([:-a, 1:] ^ Suc (Suc 0)) a * poly (pderiv r) a +
      poly r a * poly (pderiv ([:-a, 1:] ^ Suc (Suc 0))) a"
    by (simp only: poly_add poly_mult)
  also have "... = 0"
    by (subst square_root, subst deriv_square_root) simp
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
  have cardK_gt1: "card K > 1"
  proof -
    have pair: "{0, 1} \<subseteq> K" by auto
    have "card {0, 1 :: 'a} \<le> card K"
      by (rule card_mono[OF fin pair])
    then show ?thesis by simp
  qed
  have K_roots: "K \<subseteq> {x. poly (finite_field_vanishing_poly K) x = 0}"
    using finite_field_frobenius_identity[OF fin]
    by (auto simp: frobenius_power_def)
  have p0: "finite_field_vanishing_poly K \<noteq> 0"
    by (rule finite_field_vanishing_poly_nonzero[OF cardK_gt1])
  have fin_roots: "finite {x. poly (finite_field_vanishing_poly K) x = 0}"
    by (rule poly_roots_finite[OF p0])
  have card_roots_le:
      "card {x. poly (finite_field_vanishing_poly K) x = 0} \<le> card K"
    using poly_roots_degree[OF p0]
    by (simp add: degree_finite_field_vanishing_poly[OF cardK_gt1])
  have cardK_le:
      "card K \<le> card {x. poly (finite_field_vanishing_poly K) x = 0}"
    by (rule card_mono[OF fin_roots K_roots])
  have card_eq:
      "card K = card {x. poly (finite_field_vanishing_poly K) x = 0}"
    using cardK_le card_roots_le by simp
  show ?thesis
    by (rule sym, rule card_subset_eq[OF fin_roots K_roots card_eq])
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
  have cardK_gt1: "card K > 1"
  proof -
    have pair: "{0, 1} \<subseteq> K" by auto
    have "card {0, 1 :: 'a} \<le> card K"
      by (rule card_mono[OF fin pair])
    then show ?thesis by simp
  qed
  have p0: "finite_field_vanishing_poly K \<noteq> 0"
    by (rule finite_field_vanishing_poly_nonzero[OF cardK_gt1])
  show ?thesis
    unfolding rsquarefree_def
  proof (intro conjI allI)
    show "finite_field_vanishing_poly K \<noteq> 0" by (rule p0)
    fix x
    show "order x (finite_field_vanishing_poly K) = 0 \<or>
        order x (finite_field_vanishing_poly K) = 1"
    proof (cases "poly (finite_field_vanishing_poly K) x = 0")
      case False
      have "order x (finite_field_vanishing_poly K) = 0"
        using False by (simp add: order_eq_0_iff[OF p0])
      then show ?thesis by blast
    next
      case True
      have opos: "order x (finite_field_vanishing_poly K) > 0"
        using True by (simp add: order_gt_0_iff[OF p0])
      have not_two: "\<not> 2 \<le> order x (finite_field_vanishing_poly K)"
      proof
        assume two: "2 \<le> order x (finite_field_vanishing_poly K)"
        have "poly (pderiv (finite_field_vanishing_poly K)) x = 0"
          by (rule order_ge_two_imp_pderiv_root[OF p0 two])
        with deriv show False by simp
      qed
      with opos show ?thesis by auto
    qed
  qed
qed

end

lemma finite_field_vanishing_poly_over_subfield:
  fixes F K :: "'a :: field set"
  assumes sfF: "Subfield F"
  shows "finite_field_vanishing_poly K \<in> poly_over F"
proof -
  interpret F: Subfield F by (rule sfF)
  show ?thesis
    unfolding finite_field_vanishing_poly_def
    by (intro F.poly_over_diff F.poly_over_monom F.one_closed)
qed

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
  have min: "is_minpoly F a (minpoly F a)"
    by (rule Subfield.is_minpoly_minpoly[OF sfF alg])
  have qF: "finite_field_vanishing_poly K \<in> poly_over F"
    by (rule finite_field_vanishing_poly_over_subfield[OF sfF])
  have qa: "poly (finite_field_vanishing_poly K) a = 0"
    using Subfield.finite_field_frobenius_identity[OF sfK finK aK]
    by (simp add: frobenius_power_def)
  have dvd: "minpoly F a dvd finite_field_vanishing_poly K"
    by (rule Subfield.minpoly_dvd[OF sfF min qF qa])
  have squarefree: "rsquarefree (finite_field_vanishing_poly K)"
    by (rule Subfield.finite_field_vanishing_poly_rsquarefree[OF sfK finK])
  show "rsquarefree (minpoly F a)"
    by (rule rsquarefree_dvd[OF dvd squarefree])
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
  have alg: "algebraic_over F a"
    unfolding algebraic_over_def using pF p0 pa by blast
  have min: "is_minpoly F a (minpoly F a)"
    by (rule Subfield.is_minpoly_minpoly[OF sfF alg])
  have qF: "finite_field_vanishing_poly K \<in> poly_over F"
    by (rule finite_field_vanishing_poly_over_subfield[OF sfF])
  have qa: "poly (finite_field_vanishing_poly K) a = 0"
    using Subfield.finite_field_frobenius_identity[OF sfK finK aK]
    by (simp add: frobenius_power_def)
  have dvd: "minpoly F a dvd finite_field_vanishing_poly K"
    by (rule Subfield.minpoly_dvd[OF sfF min qF qa])
  obtain c where qeq:
      "finite_field_vanishing_poly K = minpoly F a * c"
    using dvd by (auto simp: dvd_def)
  show "poly_root_set p \<subseteq> K"
  proof
    fix b assume bp: "b \<in> poly_root_set p"
    have pb: "poly p b = 0" using bp by simp
    have minb: "poly (minpoly F a) b = 0"
      by (rule Subfield.irreducible_over_root_is_minpoly_root[OF sfF irr pF min pa pb])
    have qb: "poly (finite_field_vanishing_poly K) b = 0"
      using minb by (simp add: qeq poly_mult)
    have roots: "{x. poly (finite_field_vanishing_poly K) x = 0} = K"
      by (rule Subfield.finite_field_vanishing_poly_roots[OF sfK finK])
    show "b \<in> K" using qb roots by blast
  qed
qed

text \<open>The standard finite-field formulation now follows without a separate top-carrier
  hypothesis: finite-dimensionality over a finite base makes the extension carrier finite.\<close>
theorem finite_field_extension_carrier_finite:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "finite K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  show ?thesis by (rule T.finite_carrier_of_finite_base[OF finF])
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
    by (rule finite_subfield_extension_separable[OF T.base.Subfield_axioms
          T.ext.Subfield_axioms T.base_subset finK])
qed

theorem finite_field_extension_normal:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "normal_extension K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  show ?thesis
    by (rule finite_subfield_extension_normal[OF T.base.Subfield_axioms
          T.ext.Subfield_axioms T.base_subset finK])
qed


end

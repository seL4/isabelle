section \<open>The four-element field \<open>GF(4)\<close> via Kronecker's construction\<close>

theory GF4
  imports GF2_Field
begin

text \<open>An end-to-end exercise of the carrier-set field machinery: the polynomial
  \<open>X\<^sup>2 + X + 1\<close> is irreducible over the two-element field \<open>GF(2)\<close> (it has no root there), so by
  Kronecker's theorem (@{thm [source] Field.poly_quotient_field}) the quotient
  \<open>GF(2)[X] / (X\<^sup>2 + X + 1)\<close> is a field --- the four-element field \<open>GF(4)\<close>.

  The @{text GF2} qualifier below refers to the canonical interpretation of the @{locale Field}
  locale on the two-element field, installed once in \<open>GF2_Field\<close>.\<close>

text \<open>The witness polynomial \<open>\<Phi> = X\<^sup>2 + X + 1\<close> over \<open>GF(2)\<close>.\<close>
definition Phi :: "nat \<Rightarrow> nat"
  where "Phi = GF2.poly_add (GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1)) (GF2.poly_const 1)"

text \<open>Its coefficients: @{text 1} at degrees @{text 0}, @{text 1}, @{text 2}, and @{text 0} above.\<close>
lemma Phi_coeff: "Phi i = (if i \<le> 2 then 1 else 0)"
  by (simp add: Phi_def GF2.poly_add_def GF2.monom_def GF2.poly_const_def gf2_add_def)

lemma Phi_closed: "Phi \<in> GF2.poly_carrier"
  unfolding Phi_def by (intro GF2.poly_add_closed GF2_monom_carrier GF2_poly_const_carrier)

text \<open>@{term Phi} has degree exactly @{text 2}.\<close>
lemma degree_Phi: "GF2.degree Phi = 2"
proof (rule antisym)
  show "GF2.degree Phi \<le> 2"
    using GF2.degree_le_iff Phi_closed Phi_coeff by auto
  have "finite {i. Phi i \<noteq> 0}" using Phi_closed by (rule GF2.poly_carrier_finite)
  then show "2 \<le> GF2.degree Phi"
    using GF2.coeff_gt_degree Phi_closed Phi_coeff linorder_not_le by fastforce
qed

text \<open>@{term Phi} has no root in @{term "{0, 1::nat}"}: both candidate values evaluate to
  @{text 1}, since \<open>X\<^sup>2 + X + 1\<close> at @{text 0} is @{text 1} and at @{text 1} is
  \<open>1 + 1 + 1 = 1\<close> modulo 2.\<close>
lemma Phi_no_root:
  assumes a: "\<alpha> \<in> {0, 1::nat}"
  shows "GF2.eval \<alpha> Phi \<noteq> 0"
proof -
  have sum2: "GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1) \<in> GF2.poly_carrier"
    by (intro GF2.poly_add_closed GF2_monom_carrier)
  \<comment> \<open>Evaluate term by term, using additivity and @{thm [source] GF2.eval_monom}.\<close>
  have "GF2.eval \<alpha> Phi
        = gf2_add (GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1))) (GF2.eval \<alpha> (GF2.poly_const 1))"
    unfolding Phi_def
    using GF2.eval_add[OF sum2 GF2_poly_const_carrier assms] .
  also have "\<dots> = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 2)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1"
    using GF2.eval_add[OF GF2_monom_carrier GF2_monom_carrier assms]
          GF2.eval_const[OF assms] GF2.eval_monom[OF _ assms] by simp
  finally have ev: "GF2.eval \<alpha> Phi
        = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 2)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1" .
  \<comment> \<open>Compute the powers: @{text "\<alpha>\<^sup>2 = \<alpha>\<cdot>\<alpha>"}, @{text "\<alpha>\<^sup>1 = \<alpha>"}.\<close>
  have r2: "GF2.rpow \<alpha> 2 = gf2_mult \<alpha> (gf2_mult \<alpha> 1)"
    unfolding GF2.rpow_def by (simp add: eval_nat_numeral)
  have "GF2.rpow \<alpha> 1 = gf2_mult \<alpha> 1"
    unfolding GF2.rpow_def by simp
  then show "GF2.eval \<alpha> Phi \<noteq> 0"
    using gf2_cases[OF a] ev gf2_add_simps(4) gf2_mult_simps(4) r2 by fastforce
qed

text \<open>Therefore @{term Phi} is irreducible over @{text "GF(2)"}.\<close>
theorem Phi_irreducible: "GF2.poly_irreducible Phi"
  by (rule GF2.degree2_no_root_irreducible[OF Phi_closed degree_Phi]) (rule Phi_no_root)

text \<open>\<^emph>\<open>Kronecker.\<close>  The principal ideal @{text "(\<Phi>)"} is maximal in @{text "GF(2)[X]"}, so the
  quotient @{text "GF(2)[X]/(\<Phi>)"} is a field --- a four-element field, @{text "GF(4)"}.\<close>
theorem GF4_is_field:
  "ideal_in_comm_ring (GF2.poly_pideal Phi) GF2.poly_carrier GF2.poly_add GF2.poly_mult GF2.poly_zero GF2.poly_one
   \<and> Ideal.maximal_ideal (GF2.poly_pideal Phi) GF2.poly_carrier GF2.poly_add GF2.poly_mult GF2.poly_zero GF2.poly_one"
  using GF2.poly_quotient_field[OF Phi_irreducible] .

end

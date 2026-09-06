section \<open>The eight-element field \<open>GF(8)\<close> via Kronecker's construction\<close>

theory GF8
  imports GF2_Field
begin

text \<open>A cubic witness for the carrier-set field machinery: the polynomial \<open>X\<^sup>3 + X + 1\<close> is
  irreducible over \<open>GF(2)\<close> (degree 3 with no root), so by Kronecker's theorem the quotient
  \<open>GF(2)[X] / (X\<^sup>3 + X + 1)\<close> is a field, and by @{thm [source] Field.card_poly_quotient} it has
  \<open>2\<^sup>3 = 8\<close> elements --- the field \<open>GF(8)\<close>.  This exercises @{thm [source]
  Field.degree3_no_root_irreducible}.  The @{text GF2} qualifier below refers to the canonical
  interpretation of the @{locale Field} locale on the two-element field, installed once in
  \<open>GF2_Field\<close>.\<close>

text \<open>The witness polynomial \<open>\<Theta> = X\<^sup>3 + X + 1\<close> over \<open>GF(2)\<close>.\<close>
definition Theta :: "nat \<Rightarrow> nat"
  where "Theta = GF2.poly_add (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1)) (GF2.poly_const 1)"

lemma Theta_coeff: "Theta i = (if i = 0 \<or> i = 1 \<or> i = 3 then 1 else 0)"
  by (simp add: Theta_def GF2.poly_add_def GF2.monom_def GF2.poly_const_def gf2_add_def)

lemma Theta_closed: "Theta \<in> GF2.poly_carrier"
  unfolding Theta_def by (intro GF2.poly_add_closed GF2_monom_carrier GF2_poly_const_carrier)

text \<open>@{term Theta} has degree exactly @{text 3}.\<close>
lemma degree_Theta: "GF2.degree Theta = 3"
proof (rule antisym)
  show "GF2.degree Theta \<le> 3"
    by (rule GF2.degree_leI[OF Theta_closed]) (simp add: Theta_coeff)
  have "Theta 3 \<noteq> 0" by (simp add: Theta_coeff)
  moreover have "finite {i. Theta i \<noteq> 0}" using Theta_closed by (rule GF2.poly_carrier_finite)
  ultimately show "3 \<le> GF2.degree Theta"
    by (simp add: GF2.degree_def) (metis (mono_tags, lifting) Max_ge empty_iff mem_Collect_eq)
qed

text \<open>@{term Theta} has no root in @{term "{0, 1::nat}"}: \<open>\<alpha>\<^sup>3 + \<alpha> + 1\<close> is @{text 1} at both
  @{text 0} and @{text 1} (modulo 2).\<close>
lemma Theta_no_root: "\<alpha> \<in> {0, 1::nat} \<Longrightarrow> GF2.eval \<alpha> Theta \<noteq> 0"
proof -
  assume a: "\<alpha> \<in> {0, 1::nat}"
  have sum2: "GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1) \<in> GF2.poly_carrier"
    by (intro GF2.poly_add_closed GF2_monom_carrier)
  \<comment> \<open>Evaluate term by term.\<close>
  have "GF2.eval \<alpha> Theta
        = gf2_add (GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1))) (GF2.eval \<alpha> (GF2.poly_const 1))"
    unfolding Theta_def
    using GF2.eval_add[OF sum2 GF2_poly_const_carrier a] .
  also have "GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1))
             = gf2_add (GF2.eval \<alpha> (GF2.monom 1 3)) (GF2.eval \<alpha> (GF2.monom 1 1))"
    using GF2.eval_add a by blast
  also have "GF2.eval \<alpha> (GF2.monom 1 3) = gf2_mult 1 (GF2.rpow \<alpha> 3)"
    using GF2.eval_monom a by blast
  also have "GF2.eval \<alpha> (GF2.monom 1 1) = gf2_mult 1 (GF2.rpow \<alpha> 1)"
    using GF2.eval_monom a by blast
  also have "GF2.eval \<alpha> (GF2.poly_const 1) = 1"
    using GF2.eval_const a by blast
  finally have ev: "GF2.eval \<alpha> Theta
        = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 3)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1" .
  \<comment> \<open>Compute the powers: @{text "\<alpha>\<^sup>3 = \<alpha>\<cdot>\<alpha>\<cdot>\<alpha>"}, @{text "\<alpha>\<^sup>1 = \<alpha>"}.\<close>
  have three: "(3::nat) = Suc (Suc (Suc 0))" by simp
  have r3: "GF2.rpow \<alpha> 3 = gf2_mult \<alpha> (gf2_mult \<alpha> (gf2_mult \<alpha> 1))"
    unfolding three GF2.rpow_def by simp
  have r1: "GF2.rpow \<alpha> 1 = gf2_mult \<alpha> 1"
    unfolding GF2.rpow_def by simp
  have "GF2.eval \<alpha> Theta = gf2_add (gf2_add (gf2_mult 1 (gf2_mult \<alpha> (gf2_mult \<alpha> (gf2_mult \<alpha> 1))))
                                          (gf2_mult 1 (gf2_mult \<alpha> 1))) 1"
    unfolding ev r3 r1 by (rule refl)
  then show "GF2.eval \<alpha> Theta \<noteq> 0"
    using gf2_cases[OF a] by (auto simp: gf2_add_def gf2_mult_def)
qed

text \<open>Therefore @{term Theta} is irreducible over @{text "GF(2)"}.\<close>
theorem Theta_irreducible: "GF2.poly_irreducible Theta"
  by (rule GF2.degree3_no_root_irreducible[OF Theta_closed degree_Theta]) (rule Theta_no_root)

text \<open>\<^emph>\<open>Kronecker.\<close>  The quotient @{text "GF(2)[X]/(\<Theta>)"} is a field with \<open>2\<^sup>3 = 8\<close> elements.\<close>
theorem GF8_is_field:
  "ideal_in_comm_ring (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) (GF2.poly_mult) GF2.poly_zero GF2.poly_one
   \<and> Ideal.maximal_ideal (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) (GF2.poly_mult) GF2.poly_zero GF2.poly_one"
  using GF2.poly_quotient_field[OF Theta_irreducible] .

theorem card_GF8:
  "card (Ideal.quotient_set (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) GF2.poly_zero) = 8"
proof -
  have pnz: "Theta \<noteq> GF2.poly_zero"
    using degree_Theta by (metis GF2.degree_zero zero_neq_numeral)
  have "card (Ideal.quotient_set (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) GF2.poly_zero)
        = card {0, 1::nat} ^ GF2.degree Theta"
    by (rule GF2.card_poly_quotient[OF _ Theta_closed pnz]) simp
  also have "\<dots> = 8" by (simp add: degree_Theta eval_nat_numeral)
  finally show ?thesis .
qed

end

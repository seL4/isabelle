section \<open>The nine-element field \<open>GF(9)\<close> via Kronecker's construction\<close>

theory GF9
  imports GF_p_Field
begin

text \<open>A second end-to-end witness for the carrier-set field machinery, over a non-binary prime
  field: the polynomial \<open>X\<^sup>2 + 1\<close> is irreducible over \<open>GF(3)\<close> (it has no root there, as \<open>-1\<close> is not
  a square modulo 3), so by Kronecker's theorem the quotient \<open>GF(3)[X] / (X\<^sup>2 + 1)\<close> is a field, and
  by @{thm [source] Field.card_poly_quotient} it has \<open>3\<^sup>2 = 9\<close> elements --- the field \<open>GF(9)\<close>.  The
  @{text GF3} qualifier below refers to the canonical interpretation of the @{locale Field} locale
  on the three-element field, installed once in \<open>GF_p_Field\<close>.\<close>

text \<open>The witness polynomial \<open>\<Psi> = X\<^sup>2 + 1\<close> over \<open>GF(3)\<close>.\<close>
definition Psi :: "nat \<Rightarrow> nat"
  where "Psi = GF3.poly_add (GF3.monom 1 2) (GF3.poly_const 1)"

lemma three: "(3::nat) = Suc (Suc (Suc 0))" by simp

lemma Psi_coeff: "Psi i = (if i = 0 \<or> i = 2 then 1 else 0)"
  by (simp add: Psi_def GF3.poly_add_def GF3.monom_def GF3.poly_const_def gfp_add_def)

lemma Psi_closed: "Psi \<in> GF3.poly_carrier"
  unfolding Psi_def by (intro GF3.poly_add_closed GF3_monom_carrier GF3_poly_const_carrier)

text \<open>@{term Psi} has degree exactly @{text 2}.\<close>
lemma degree_Psi: "GF3.degree Psi = 2"
proof (rule antisym)
  show "GF3.degree Psi \<le> 2"
    by (rule GF3.degree_leI[OF Psi_closed]) (simp add: Psi_coeff)
  have "Psi 2 \<noteq> 0" by (simp add: Psi_coeff)
  moreover have "finite {i. Psi i \<noteq> 0}" using Psi_closed by (rule GF3.poly_carrier_finite)
  ultimately show "2 \<le> GF3.degree Psi"
    by (simp add: GF3.degree_def) (metis (mono_tags, lifting) Max_ge empty_iff mem_Collect_eq)
qed

text \<open>@{term Psi} has no root in @{term "{0..<3::nat}"}: \<open>\<alpha>\<^sup>2 + 1\<close> is @{text 1}, @{text 2}, @{text 2}
  at \<open>\<alpha> = 0, 1, 2\<close> respectively --- never @{text 0}.\<close>
lemma Psi_no_root: "\<alpha> \<in> {0..<3::nat} \<Longrightarrow> GF3.eval \<alpha> Psi \<noteq> 0"
proof -
  assume a: "\<alpha> \<in> {0..<3::nat}"
  \<comment> \<open>Evaluate term by term.\<close>
  have "GF3.eval \<alpha> Psi = gfp_add 3 (GF3.eval \<alpha> (GF3.monom 1 2)) (GF3.eval \<alpha> (GF3.poly_const 1))"
    unfolding Psi_def by (rule GF3.eval_add[OF GF3_monom_carrier GF3_poly_const_carrier a])
  also have "GF3.eval \<alpha> (GF3.monom 1 2) = gfp_mult 3 1 (GF3.rpow \<alpha> 2)"
    by (rule GF3.eval_monom[OF GF3_one_mem a])
  also have "GF3.eval \<alpha> (GF3.poly_const 1) = 1" by (rule GF3.eval_const[OF a GF3_one_mem])
  finally have ev: "GF3.eval \<alpha> Psi = gfp_add 3 (gfp_mult 3 1 (GF3.rpow \<alpha> 2)) 1" .
  \<comment> \<open>Compute the square: @{text "\<alpha>\<^sup>2 = \<alpha>\<cdot>\<alpha>"}.\<close>
  have two: "(2::nat) = Suc (Suc 0)" by simp
  have r2: "GF3.rpow \<alpha> 2 = gfp_mult 3 \<alpha> (gfp_mult 3 \<alpha> 1)"
    unfolding two GF3.rpow_def by simp
  have ev2: "GF3.eval \<alpha> Psi = gfp_add 3 (gfp_mult 3 1 (gfp_mult 3 \<alpha> (gfp_mult 3 \<alpha> 1))) 1"
    unfolding ev r2 by (rule refl)
  also have "\<dots> = Suc (\<alpha> * \<alpha> mod 3) mod 3"
    by (simp add: gfp_add_def gfp_mult_def mod_mult_right_eq mod_mult_left_eq)
  finally have val: "GF3.eval \<alpha> Psi = Suc (\<alpha> * \<alpha> mod 3) mod 3" .
  \<comment> \<open>Check the three residues @{text "\<alpha> = 0, 1, 2"} explicitly.\<close>
  have "\<alpha> = 0 \<or> \<alpha> = 1 \<or> \<alpha> = 2" using a by auto
  then show "GF3.eval \<alpha> Psi \<noteq> 0" using val by auto
qed

text \<open>Therefore @{term Psi} is irreducible over @{text "GF(3)"}.\<close>
theorem Psi_irreducible: "GF3.poly_irreducible Psi"
  by (rule GF3.degree2_no_root_irreducible[OF Psi_closed degree_Psi]) (rule Psi_no_root)

text \<open>\<^emph>\<open>Kronecker.\<close>  The quotient @{text "GF(3)[X]/(\<Psi>)"} is a field with \<open>3\<^sup>2 = 9\<close> elements.\<close>
theorem GF9_is_field:
  "ideal_in_comm_ring (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) (GF3.poly_mult) GF3.poly_zero GF3.poly_one
   \<and> Ideal.maximal_ideal (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) (GF3.poly_mult) GF3.poly_zero GF3.poly_one"
  using GF3.poly_quotient_field[OF Psi_irreducible] .

theorem card_GF9:
  "card (Ideal.quotient_set (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) GF3.poly_zero) = 9"
proof -
  have pnz: "Psi \<noteq> GF3.poly_zero"
    using degree_Psi by (metis GF3.degree_zero zero_neq_numeral)
  have "card (Ideal.quotient_set (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) GF3.poly_zero)
        = card {0..<3::nat} ^ GF3.degree Psi"
    by (rule GF3.card_poly_quotient[OF _ Psi_closed pnz]) simp
  also have "\<dots> = 9" by (simp add: degree_Psi)
  finally show ?thesis .
qed

end

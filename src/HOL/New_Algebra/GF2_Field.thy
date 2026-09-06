section \<open>The two-element field with polynomial machinery\<close>

theory GF2_Field
  imports GF2 Poly_Ring Poly_Ideal
begin

text \<open>A single, canonical interpretation of the @{locale Field} locale on \<open>GF(2)\<close>, made \<^emph>\<open>after\<close>
  \<open>Poly_Ring\<close> and \<open>Poly_Ideal\<close> have been loaded so that polynomial-level facts (e.g.\
  @{text GF2.poly_add}, @{text GF2.poly_carrier}, @{text GF2.poly_quotient_field}) are visible
  through the @{text GF2} qualifier.  Downstream theories \<open>GF4\<close> and \<open>GF8\<close> import this theory and
  use its interpretation instead of installing their own local one --- keeping the interpretation
  single-sourced.\<close>

interpretation GF2: Field "{0, 1::nat}" gf2_add gf2_mult 0 1
  by (rule gf2_field)

text \<open>Convenience closure facts for the polynomial machinery over \<open>GF(2)\<close>.  Both @{text 0} and
  @{text 1} lie in the carrier, so any constant polynomial with a bit coefficient and any monomial
  with unit leading coefficient are closed; the actual work is delegated to
  @{thm [source] GF2.monom_closed} / @{thm [source] GF2.poly_const_closed}.\<close>

lemma GF2_one_mem [simp, intro]: "(1::nat) \<in> {0, 1::nat}" by simp
lemma GF2_zero_mem [simp, intro]: "(0::nat) \<in> {0, 1::nat}" by simp

lemma GF2_poly_const_carrier [simp, intro]: "GF2.poly_const 1 \<in> GF2.poly_carrier"
  by (rule GF2.poly_const_closed) simp

lemma GF2_monom_carrier [simp, intro]: "GF2.monom 1 n \<in> GF2.poly_carrier"
  by (rule GF2.monom_closed) simp

end

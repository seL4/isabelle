section \<open>The three-element prime field with polynomial machinery\<close>

theory GF_p_Field
  imports GF_p Poly_Ring Poly_Ideal
begin

text \<open>A single, canonical interpretation of the @{locale Field} locale on \<open>GF(3)\<close>, made \<^emph>\<open>after\<close>
  \<open>Poly_Ring\<close> and \<open>Poly_Ideal\<close> have been loaded so that polynomial-level facts are visible through the
  @{text GF3} qualifier.  Downstream theory \<open>GF9\<close> imports this theory and uses its interpretation
  instead of installing its own local one.

  Only the concrete case \<open>p = 3\<close> is instantiated here; if further prime fields are needed as
  ambient fields for polynomial constructions (e.g.\ \<open>GF(25)\<close> over \<open>GF(5)\<close>), extend this file with
  the corresponding fixed-\<open>p\<close> interpretation.\<close>

interpretation GF3: Field "{0..<3::nat}" "gfp_add 3" "gfp_mult 3" 0 1
  using gfp_field[of 3] by simp

text \<open>Convenience closure facts for the polynomial machinery over \<open>GF(3)\<close>.\<close>

lemma GF3_one_mem [simp, intro]: "(1::nat) \<in> {0..<3::nat}" by simp

lemma GF3_poly_const_carrier [simp, intro]: "GF3.poly_const 1 \<in> GF3.poly_carrier"
  by (rule GF3.poly_const_closed) simp

lemma GF3_monom_carrier [simp, intro]: "GF3.monom 1 n \<in> GF3.poly_carrier"
  by (rule GF3.monom_closed) simp

end

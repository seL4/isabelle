section \<open>Algebraicity of generated splitting fields\<close>

theory Galois_Finite_Extension
  imports Galois_Fixed_Field Algebraic_Transitivity
begin

text \<open>
  The generic algebraicity closure for generated fields lives in
  \<open>Algebraic_Transitivity\<close>.  This complex-specific wrapper applies it to the
  root set of a splitting-field presentation and discharges the algebraicity premise of the
  fixed-field theorem, without invoking Artin's theorem or an algebraic closure.
\<close>

text \<open>Complex splitting fields are algebraic over their base.  Their generators are the root
set of the defining nonzero polynomial, and the preceding closure result applies to that set
directly (in fact, it does not need the root set's finiteness).
\<close>
lemma splitting_field_algebraic_extension:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "algebraic_extension K F"
proof (rule algebraic_extensionI)
  fix x assume xK: "x \<in> K"
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have algR: "\<And>r. r \<in> poly_root_set q \<Longrightarrow> algebraic_over F r"
    by (rule splitting_field_root_algebraic[OF split])
  have algK: "\<And>x. x \<in> generate_field (F \<union> poly_root_set q) \<Longrightarrow> algebraic_over F x"
    by (rule generated_algebraic[OF sfF' algR])
  have Kdef: "K = generate_field (F \<union> poly_root_set q)"
    using splitting_fieldD[OF split] gen_subfield_eq_generate_field by simp
  show "algebraic_over F x"
    using algK xK by (simp add: Kdef)
qed

theorem splitting_field_normal_separable:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "normal_extension K F \<and> separable_extension K F"
proof (intro conjI)
  show "normal_extension K F"
    by (rule splitting_field_normal[OF split sfF])
  show "separable_extension K F"
    by (rule complex_extension_separable[OF sfF])
qed

text \<open>With the finite-generation bridge in place, the closure theorem no longer needs an
explicit algebraicity premise for an intermediate field of a complex splitting field.
\<close>
theorem fixed_field_eq_of_complex_splitting_field:
  fixes F E K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K"
    and sfF: "complex_subfield F"
    and E: "E \<in> inter_fields K F"
  shows "fixed_field K (field_auto K E) = E"
proof -
  have FE: "F \<subseteq> E"
    using E by (simp add: inter_fields_iff)
  have algKF: "algebraic_extension K F"
    by (rule splitting_field_algebraic_extension[OF split sfF])
  have algKE: "algebraic_extension K E"
  proof (rule algebraic_extensionI)
    fix x assume xK: "x \<in> K"
    have algx: "algebraic_over F x"
      by (rule algebraic_extensionD[OF algKF xK])
    show "algebraic_over E x"
      by (rule algebraic_over_mono[OF algx FE])
  qed
  show ?thesis
    by (rule fixed_field_eq_of_splitting_field[OF split E algKE])
qed

end

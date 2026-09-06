section \<open>Field-side inverse and degree formulas for simple normal extensions\<close>

theory Galois_Simple_Degree
  imports Galois_Finite_Extension Galois_Degree
begin

text \<open>
  The simple normal case is the degree-bearing part of the field-side correspondence.  The
  existing Galois-degree theorem counts the automorphisms; this theory connects its hypotheses to
  the splitting-field presentation used by the fixed-field closure theorem.
\<close>

lemma splitting_field_finite_galois_group:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "finite (field_auto K F)"
proof -
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have sfK': "Subfield K"
    using splitting_field_subfield[OF split]
    by (simp add: complex_subfield_iff_subfield)
  have FK: "F \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have qF: "q \<in> poly_over F"
    using split by (auto simp: splitting_fieldD)
  have pnz: "q \<noteq> 0"
    using split by (auto simp: splitting_fieldD)
  have Xdef: "poly_root_set q = {r. poly q r = 0}"
    by (simp add: poly_root_set_def)
  have XK: "poly_root_set q \<subseteq> K"
    by (rule splitting_field_roots_subset[OF split])
  have finX: "finite (poly_root_set q)"
    by (rule finite_poly_root_set[OF pnz])
  have Kgen: "K = gen_subfield (F \<union> poly_root_set q)"
    using split by (auto simp: splitting_fieldD gen_subfield_eq_generate_field)
  show "finite (field_auto K F)"
    by (rule finite_field_auto[OF sfK' sfF' FK qF Xdef XK finX Kgen])
qed

lemma simple_normal_splitting_field:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "splitting_field F (minpoly F a) (eval_img F a)"
proof -
  define R where "R = {r. poly (minpoly F a) r = 0}"
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg])
  have FE: "F \<subseteq> eval_img F a"
    using Subfield.eval_img_base[OF sfF] by blast
  have pF: "minpoly F a \<in> poly_over F"
    by (rule Subfield.minpoly_over[OF sfF alg])
  have pnz: "minpoly F a \<noteq> 0"
    by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mroot: "poly (minpoly F a) a = 0"
    by (rule Subfield.minpoly_root[OF sfF alg])
  have aR: "a \<in> R"
    using mroot by (simp add: R_def)
  have RE: "R \<subseteq> eval_img F a"
    using normal by (simp add: R_def)
  have Egen: "eval_img F a = generate_field (F \<union> R)"
  proof (rule antisym)
    have "F \<union> {a} \<subseteq> F \<union> R" using aR by blast
    then have "generate_field (F \<union> {a}) \<subseteq> generate_field (F \<union> R)"
      by (rule generate_field_mono)
    then show "eval_img F a \<subseteq> generate_field (F \<union> R)"
      using Subfield.eval_img_eq_generate_field[OF sfF alg] by simp
    show "generate_field (F \<union> R) \<subseteq> eval_img F a"
      using FE RE by (intro generate_field_least[OF sfE]) auto
  qed
  show ?thesis
    unfolding splitting_field_def
    using pF pnz Egen gen_subfield_eq_generate_field
    by (simp add: R_def poly_root_set_def)
qed

text \<open>For a simple normal complex extension, the field-side inverse law and the exact order
formula can be consumed together.  The subgroup-side inverse law is deliberately not reproved
here; it is the separate Artin theorem.
\<close>
theorem simple_normal_field_inverse_and_degree:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "complex_subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "fixed_field (eval_img F a) (field_auto (eval_img F a) F) = F \<and>
    card (field_auto (eval_img F a) F) = ext_degree F a"
proof -
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have split: "splitting_field F (minpoly F a) (eval_img F a)"
    by (rule simple_normal_splitting_field[OF sfF' alg normal])
  have FE: "F \<subseteq> eval_img F a"
    using Subfield.eval_img_base[OF sfF'] by blast
  have Eint: "F \<in> inter_fields (eval_img F a) F"
    by (rule base_in_inter_fields[OF sfF' FE])
  have fixed:
    "fixed_field (eval_img F a) (field_auto (eval_img F a) F) = F"
    by (rule fixed_field_eq_of_complex_splitting_field[OF split sfF Eint])
  have degree:
    "card (field_auto (eval_img F a) F) = ext_degree F a"
    by (rule galois_simple_normal_degree[OF sfF' alg normal])
  show ?thesis using fixed degree by blast
qed

end

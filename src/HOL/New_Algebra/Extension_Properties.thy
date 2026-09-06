section \<open>Generic properties of algebraic field extensions\<close>

theory Extension_Properties
  imports Extension_Degree
begin

text \<open>
  These are the representation-independent extension predicates used by the Galois development.
  A field extension is represented by nested set-based subfields of one ambient field, as in
  \<open>Subfield\<close>; no complex-specific subfield locale or algebraic-closure theorem
  is needed for the definitions.

  A splitting field is presented by a nonzero polynomial over the base and the subfield generated
  by all of its roots.  The normality predicate uses the same root-set presentation for every
  irreducible polynomial over the base, while separability is stated through minimal polynomials.
\<close>

definition poly_root_set :: "'a :: field poly \<Rightarrow> 'a set" where
  "poly_root_set p = {z. poly p z = 0}"

definition splitting_field ::
    "'a :: field set \<Rightarrow> 'a poly \<Rightarrow> 'a set \<Rightarrow> bool" where
  "splitting_field F p K \<longleftrightarrow>
     p \<in> poly_over F \<and> p \<noteq> 0 \<and> K = generate_field (F \<union> poly_root_set p)"

definition algebraic_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "algebraic_extension K F \<longleftrightarrow> (\<forall>a \<in> K. algebraic_over F a)"

definition normal_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "normal_extension K F \<longleftrightarrow>
     (\<forall>p a. p \<in> poly_over F \<longrightarrow> irreducible_over F p \<longrightarrow> a \<in> K \<longrightarrow>
       poly p a = 0 \<longrightarrow> poly_root_set p \<subseteq> K)"

definition separable_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "separable_extension K F \<longleftrightarrow>
     (\<forall>a \<in> K. algebraic_over F a \<longrightarrow> rsquarefree (minpoly F a))"

lemma poly_root_set_iff [simp]:
  "z \<in> poly_root_set p \<longleftrightarrow> poly p z = 0"
  by (simp add: poly_root_set_def)

lemma finite_poly_root_set:
  "p \<noteq> 0 \<Longrightarrow> finite (poly_root_set p)"
  unfolding poly_root_set_def by (rule poly_roots_finite)

lemma splitting_fieldD:
  "splitting_field F p K \<Longrightarrow>
     p \<in> poly_over F \<and> p \<noteq> 0 \<and> K = generate_field (F \<union> poly_root_set p)"
  by (simp add: splitting_field_def)

lemma splitting_field_subfield:
  assumes split: "splitting_field F p K"
  shows "Subfield K"
proof -
  have Kdef: "K = generate_field (F \<union> poly_root_set p)"
    using splitting_fieldD[OF split] by blast
  show ?thesis
    using Kdef subfield_generate_field[of "F \<union> poly_root_set p"] by simp
qed

lemma splitting_field_base_subset:
  assumes split: "splitting_field F p K"
  shows "F \<subseteq> K"
proof -
  have Kdef: "K = generate_field (F \<union> poly_root_set p)"
    using splitting_fieldD[OF split] by blast
  have "F \<subseteq> generate_field (F \<union> poly_root_set p)"
    using subset_generate_field[of "F \<union> poly_root_set p"] by blast
  then show ?thesis using Kdef by simp
qed

lemma splitting_field_roots_subset:
  assumes split: "splitting_field F p K"
  shows "poly_root_set p \<subseteq> K"
proof -
  have Kdef: "K = generate_field (F \<union> poly_root_set p)"
    using splitting_fieldD[OF split] by blast
  have "poly_root_set p \<subseteq> generate_field (F \<union> poly_root_set p)"
    using subset_generate_field[of "F \<union> poly_root_set p"] by blast
  then show ?thesis using Kdef by simp
qed

lemma algebraic_extensionI:
  assumes "\<And>a. a \<in> K \<Longrightarrow> algebraic_over F a"
  shows "algebraic_extension K F"
  using assms by (simp add: algebraic_extension_def)

lemma algebraic_extensionD:
  assumes "algebraic_extension K F" and "a \<in> K"
  shows "algebraic_over F a"
  using assms by (simp add: algebraic_extension_def)

lemma normal_extensionI:
  assumes "\<And>p a. \<lbrakk>p \<in> poly_over F; irreducible_over F p; a \<in> K; poly p a = 0\<rbrakk>
      \<Longrightarrow> poly_root_set p \<subseteq> K"
  shows "normal_extension K F"
  using assms by (simp add: normal_extension_def)

lemma normal_extensionD:
  assumes "normal_extension K F"
    and "p \<in> poly_over F" "irreducible_over F p" "a \<in> K" "poly p a = 0"
  shows "poly_root_set p \<subseteq> K"
  using assms by (auto simp: normal_extension_def)

lemma separable_extensionI:
  assumes "\<And>a. a \<in> K \<Longrightarrow> algebraic_over F a \<Longrightarrow> rsquarefree (minpoly F a)"
  shows "separable_extension K F"
  using assms by (simp add: separable_extension_def)

lemma separable_extensionD:
  assumes "separable_extension K F" and "a \<in> K" and "algebraic_over F a"
  shows "rsquarefree (minpoly F a)"
  using assms by (auto simp: separable_extension_def)

text \<open>A root of the defining polynomial of a splitting field is algebraic over its base.\<close>
lemma splitting_field_root_algebraic:
  assumes split: "splitting_field F p K"
    and r: "r \<in> poly_root_set p"
  shows "algebraic_over F r"
proof -
  have pF: "p \<in> poly_over F" and pnz: "p \<noteq> 0"
    using split by (auto simp: splitting_fieldD)
  show ?thesis
    unfolding algebraic_over_def
    using pF pnz r by (auto simp: poly_root_set_def)
qed

end

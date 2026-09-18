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
  "poly_root_set p \<equiv> {z. poly p z = 0}"

definition splitting_field ::
    "'a :: field set \<Rightarrow> 'a poly \<Rightarrow> 'a set \<Rightarrow> bool" where
  "splitting_field F p K \<equiv>
     p \<in> poly_over F \<and> p \<noteq> 0 \<and> K = generate_field (F \<union> poly_root_set p)"

definition algebraic_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "algebraic_extension K F \<equiv> (\<forall>a \<in> K. algebraic_over F a)"

definition normal_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "normal_extension K F \<equiv>
     (\<forall>p a. p \<in> poly_over F \<longrightarrow> irreducible_over F p \<longrightarrow> a \<in> K \<longrightarrow>
       poly p a = 0 \<longrightarrow> poly_root_set p \<subseteq> K)"

definition separable_extension :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "separable_extension K F \<equiv>
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

lemma 
  assumes "splitting_field F p K"
  shows splitting_field_subfield: "Subfield K" 
    and splitting_field_base_subset: "F \<subseteq> K"
    and splitting_field_roots_subset: "poly_root_set p \<subseteq> K"
  using assms splitting_fieldD by blast+

lemma algebraic_extensionI:
  assumes "\<And>a. a \<in> K \<Longrightarrow> algebraic_over F a"
  shows "algebraic_extension K F"
  using assms by (simp add: algebraic_extension_def)

lemma algebraic_extensionD:
  assumes "algebraic_extension K F" and "a \<in> K"
  shows "algebraic_over F a"
  using assms by (simp add: algebraic_extension_def)

lemma normal_extensionI:
  assumes
    "\<And>p a. \<lbrakk>p \<in> poly_over F; irreducible_over F p; a \<in> K; poly p a = 0\<rbrakk> \<Longrightarrow> poly_root_set p \<subseteq> K"
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

text \<open>A divisor of a root-squarefree polynomial is root-squarefree.  This is the
  base-change bridge used below: a minimal polynomial over a larger subfield divides the
  minimal polynomial over the smaller one, so separability descends to the larger base.\<close>
lemma rsquarefree_dvd:
  fixes p q :: "'a :: idom poly"
  assumes dvd: "p dvd q" and sq: "rsquarefree q"
  shows "rsquarefree p"
proof -
  have q0: "q \<noteq> 0" using sq by (simp add: rsquarefree_def)
  have order_le: "order x p \<le> order x q" for x
    by (rule dvd_imp_order_le[OF q0 dvd])
  have "p \<noteq> 0" using dvd q0 by auto
  with order_le sq  show ?thesis
    unfolding rsquarefree_def
    by (metis One_nat_def bot_nat_0.extremum_unique le_SucE)
qed

text \<open>Over an algebraically closed field, root-squarefreeness turns the multiset of
  polynomial roots into an ordinary set of the same cardinality.\<close>
lemma card_roots_eq_degree_alg_closed:
  fixes p :: "'a :: alg_closed_field poly"
  assumes p0: "p \<noteq> 0" and rsf: "rsquarefree p"
  shows "card {x. poly p x = 0} = degree p"
proof -
  obtain A where sizeA: "size A = degree p"
    and pA: "p = smult (lead_coeff p) (\<Prod>x\<in>#A. [:-x, 1:])"
    using alg_closed_imp_factorization[OF p0] by blast
  have prootsA: "proots p = A"
  proof -
    have roots_prod: "proots (\<Prod>x\<in>#A. [:-x, 1:]) = (\<Sum>x\<in>#A. proots [:-x, 1:])"
    proof (induction A)
      case (add x A)
      have factor0: "[:-x, 1:] \<noteq> (0 :: 'a poly)" by simp
      have prod0: "(\<Prod>y\<in>#A. [:-y, 1:]) \<noteq> (0 :: 'a poly)"
        by auto
      show ?case using add.IH proots_mult[OF factor0 prod0] by simp
    qed auto
    have "proots p = proots (\<Prod>x\<in>#A. [:-x, 1:])"
      by (metis p0 pA proots_smult smult_0_left)
    then show ?thesis using roots_prod by simp
  qed
  have count_le: "count (proots p) x \<le> 1" for x
    using rsf
    by (metis One_nat_def count_proots diff_Suc_Suc diff_is_0_eq rsquarefree_def zero_diff)
  have eq_mset: "proots p = mset_set (set_mset (proots p))"
      using rsf
      by (intro multiset_eqI) (metis count_mset_set' count_proots finite_set_mset not_in_iff rsquarefree_def)
  have roots_set: "set_mset (proots p) = {x. poly p x = 0}"
    by (rule set_count_proots[OF p0])
  have "card {x. poly p x = 0} = card (set_mset (proots p))"
    using roots_set by simp
  also have "... = size (proots p)" 
    by (metis size_mset_set eq_mset)
  finally show ?thesis using prootsA sizeA by simp
qed

text \<open>A root of the defining polynomial of a splitting field is algebraic over its base.\<close>
lemma splitting_field_root_algebraic:
  assumes split: "splitting_field F p K"
    and r: "r \<in> poly_root_set p"
  shows "algebraic_over F r"
  using algebraic_over_def assms(1) poly_root_set_iff r splitting_fieldD by blast

end

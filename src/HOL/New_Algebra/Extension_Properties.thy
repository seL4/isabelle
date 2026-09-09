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

text \<open>A divisor of a root-squarefree polynomial is root-squarefree.  This is the
  base-change bridge used below: a minimal polynomial over a larger subfield divides the
  minimal polynomial over the smaller one, so separability descends to the larger base.\<close>
lemma rsquarefree_dvd:
  fixes p q :: "'a :: idom poly"
  assumes dvd: "p dvd q" and sq: "rsquarefree q"
  shows "rsquarefree p"
proof -
  have q0: "q \<noteq> 0" using sq by (simp add: rsquarefree_def)
  have p0: "p \<noteq> 0" using dvd q0 by auto
  have order_le: "order x p \<le> order x q" for x
    by (rule dvd_imp_order_le[OF q0 dvd])
  show ?thesis
    unfolding rsquarefree_def
  proof (intro conjI allI)
    show "p \<noteq> 0" by (rule p0)
    fix x
    have "order x q = 0 \<or> order x q = 1"
      using sq by (simp add: rsquarefree_def)
    then show "order x p = 0 \<or> order x p = 1"
      using order_le[of x] by auto
  qed
qed

text \<open>Over an algebraically closed field, root-squarefreeness turns the multiset of
  polynomial roots into an ordinary set of the same cardinality.  This belongs with the
  extension-property API rather than the Galois-group layer: primitive-element arguments also
  need to turn a singleton root set into a degree-one minimal polynomial.\<close>
lemma card_roots_eq_degree_alg_closed:
  fixes p :: "'a :: alg_closed_field poly"
  assumes p0: "p \<noteq> 0" and rsf: "rsquarefree p"
  shows "card {x. poly p x = 0} = degree p"
proof -
  obtain A where sizeA: "size A = degree p"
    and pA: "p = smult (lead_coeff p) (\<Prod>x\<in>#A. [:-x, 1:])"
    using alg_closed_imp_factorization[OF p0] by blast
  have lc0: "lead_coeff p \<noteq> 0" using p0 by simp
  have prootsA: "proots p = A"
  proof -
    have roots_prod:
        "proots (\<Prod>x\<in>#A. [:-x, 1:]) =
          (\<Sum>x\<in>#A. proots [:-x, 1:])"
    proof (induction A)
      case empty
      show ?case by simp
    next
      case (add x A)
      have factor0: "[:-x, 1:] \<noteq> (0 :: 'a poly)" by simp
      have factors0A: "0 \<notin># image_mset (\<lambda>y. [:-y, 1:]) A"
        by (auto simp add: in_image_mset)
      have prod0: "(\<Prod>y\<in>#A. [:-y, 1:]) \<noteq> (0 :: 'a poly)"
        using factors0A by (simp add: prod_mset_zero_iff)
      have roots_mult:
          "proots ([:-x, 1:] * (\<Prod>y\<in>#A. [:-y, 1:])) =
            proots [:-x, 1:] + proots (\<Prod>y\<in>#A. [:-y, 1:])"
        by (rule proots_mult[OF factor0 prod0])
      show ?case using add.IH roots_mult by simp
    qed
    have roots_p0:
        "proots p = proots (smult (lead_coeff p) (\<Prod>x\<in>#A. [:-x, 1:]))"
      by (rule arg_cong[OF pA])
    have roots_p: "proots p = proots (\<Prod>x\<in>#A. [:-x, 1:])"
      by (rule trans[OF roots_p0 proots_smult[OF lc0]])
    show ?thesis using roots_p roots_prod by simp
  qed
  have count_le: "count (proots p) x \<le> 1" for x
  proof -
    have order_cases: "order x p = 0 \<or> order x p = 1"
      using rsf by (auto simp: rsquarefree_def)
    have order_le: "order x p \<le> 1"
      using order_cases by (elim disjE; simp)
    show ?thesis using order_le by (simp add: count_proots[OF p0])
  qed
  have eq_mset: "proots p = mset_set (set_mset (proots p))"
  proof (rule multiset_eqI)
    fix x
    show "count (proots p) x = count (mset_set (set_mset (proots p))) x"
    proof (cases "x \<in># proots p")
      case True
      have fin: "finite (set_mset (proots p))" by simp
      have one_le: "1 \<le> count (proots p) x" using True by simp
      have one: "count (proots p) x = 1"
        by (rule le_antisym[OF count_le one_le])
      then show ?thesis using fin True by simp
    next
      case False
      have count0: "count (proots p) x = 0"
        using False by (simp add: not_in_iff)
      have xnot: "x \<notin> set_mset (proots p)" using False by simp
      then show ?thesis using count0 by simp
    qed
  qed
  have roots_set: "set_mset (proots p) = {x. poly p x = 0}"
    by (rule set_count_proots[OF p0])
  have "card {x. poly p x = 0} = card (set_mset (proots p))"
    using roots_set by simp
  also have "... = size (mset_set (set_mset (proots p)))" by simp
  also have "... = size (proots p)" using eq_mset by simp
  finally show ?thesis using prootsA sizeA by simp
qed

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

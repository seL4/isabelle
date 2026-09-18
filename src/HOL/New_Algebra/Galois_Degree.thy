section \<open>The order of the Galois group of a finite normal separable extension\<close>

theory Galois_Degree
  imports Galois_Action Extension_Properties Primitive_Element
begin

text \<open>The capstone of the field side of phase R2: for a \<^emph>\<open>simple normal\<close> extension
  \<open>K = F(a)\<close> of complex fields (all conjugates of @{term a} --- the roots of its minimal
  polynomial --- already lying in @{term K}), the order of the Galois group equals the number of
  those conjugates,
  \[
      \bigl|\mathrm{field\_auto}\ K\ F\bigr| = \bigl|\{r.\ \mathrm{poly}\ (\mathrm{minpoly}\ F\ a)\ r = 0\}\bigr|,
  \]
  and, in characteristic \<open>0\<close> where the minimal polynomial is separable, this equals
  @{term "ext_degree F a"}.  The argument is the classical bijection @{term "\<lambda>\<sigma>. \<sigma> a"} between
  @{term "field_auto K F"} and the conjugates of @{term a}: it is injective (an
  @{term F}-automorphism of @{term "F(a)"} is determined by where it sends @{term a}), lands among
  the conjugates (@{thm [source] field_auto_maps_root}), and is onto (the Galois action is transitive on
  the roots of an irreducible polynomial, @{thm [source] galois_action_transitive}).

  The simple-extension calculation is the reusable core.  The final theorem combines it with the
  primitive-element theorem and the basis definition of extension degree to obtain
  \<open>|Gal(K/F)| = [K:F]\<close> for every finite normal separable extension in an algebraically closed
  ambient field.\<close>

subsection \<open>The minimal polynomial is irreducible over the base\<close>

text \<open>A minimal polynomial is irreducible over @{term F}: it is nonzero of positive degree and,
  by minimality, admits no factorisation over @{term F} into two positive-degree factors.\<close>
lemma irreducible_over_minpoly:
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
  shows "irreducible_over F (minpoly F a)"
  unfolding irreducible_over_def
proof (intro conjI allI impI)
  show "minpoly F a \<noteq> 0" by (rule Subfield.minpoly_nonzero[OF sfF alg])
  show "degree (minpoly F a) > 0"
    by (rule Subfield.minpoly_degree_pos[OF sfF Subfield.is_minpoly_minpoly[OF sfF alg]])
  fix b c assume "b \<in> poly_over F" "c \<in> poly_over F" "minpoly F a = b * c"
  then show "degree b = 0 \<or> degree c = 0"
    by (rule Subfield.minpoly_no_proper_factor[OF sfF Subfield.is_minpoly_minpoly[OF sfF alg]])
qed

subsection \<open>An \<open>F\<close>-automorphism of \<open>F(a)\<close> is determined by its value at \<open>a\<close>\<close>

text \<open>Two @{term F}-automorphisms of the simple extension @{term "eval_img F a"} that agree at
  @{term a} agree everywhere.  Every element of @{term "eval_img F a"} is @{term "poly p a"} for
  some @{term "p \<in> poly_over F"}, and an @{term F}-automorphism commutes with such evaluation
  (@{thm [source] field_hom_on.poly_map_poly_hom}, together with @{thm [source] map_poly_fix} since
  the coefficients lie in @{term F}); so the common value at @{term a} fixes the value everywhere.\<close>
lemma field_auto_determined_by_gen:
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and s: "\<sigma> \<in> field_auto (eval_img F a) F" and t: "\<tau> \<in> field_auto (eval_img F a) F"
    and eq: "\<sigma> a = \<tau> a"
  shows "\<sigma> = \<tau>"
proof -
  define E where "E = eval_img F a"
  have sE: "\<sigma> \<in> field_auto E F" using s by (simp add: E_def)
  have tE: "\<tau> \<in> field_auto E F" using t by (simp add: E_def)
  have sfE: "Subfield E" unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg])
  have FE: "F \<subseteq> E" unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have aE: "a \<in> E" unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have homs: "field_hom_on E \<sigma>" by (rule field_auto_imp_field_hom_on[OF sfE sE])
  have homt: "field_hom_on E \<tau>" by (rule field_auto_imp_field_hom_on[OF sfE tE])
  have fixFs: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x" using s by (auto simp: field_auto_mem_iff)
  have fixFt: "\<And>x. x \<in> F \<Longrightarrow> \<tau> x = x" using t by (auto simp: field_auto_mem_iff)
  \<comment> \<open>On the shared carrier @{term E} the two maps agree, elementwise.\<close>
  have agree: "\<sigma> x = \<tau> x" if xE: "x \<in> E" for x
  proof -
    obtain p where p: "p \<in> poly_over F" and xp: "x = poly p a"
      using xE by (auto simp: E_def eval_img_def)
    have pE: "p \<in> poly_over E" using p poly_over_mono[OF FE] by blast
    \<comment> \<open>@{term \<sigma>} commutes with evaluation, and fixes the (\<open>F\<close>-)coefficients.\<close>
    have "\<sigma> x = \<sigma> (poly p a)" by (simp add: xp)
    also have "\<dots> = poly (map_poly \<sigma> p) (\<sigma> a)"
      using field_hom_on.poly_map_poly_hom[OF homs pE aE] by simp
    also have "\<dots> = poly p (\<sigma> a)" using map_poly_fix[OF homs sfF p fixFs] by simp
    also have "\<dots> = poly p (\<tau> a)" by (simp add: eq)
    also have "\<dots> = poly (map_poly \<tau> p) (\<tau> a)" using map_poly_fix[OF homt sfF p fixFt] by simp
    also have "\<dots> = \<tau> (poly p a)"
      using field_hom_on.poly_map_poly_hom[OF homt pE aE] by simp
    also have "\<dots> = \<tau> x" by (simp add: xp)
    finally show ?thesis .
  qed
  \<comment> \<open>Both maps are extensional on @{term E}, so agreeing on @{term E} makes them equal.\<close>
  have sPiE: "\<sigma> \<in> E \<rightarrow>\<^sub>E E" using s by (simp add: field_auto_mem_iff E_def)
  have tPiE: "\<tau> \<in> E \<rightarrow>\<^sub>E E" using t by (simp add: field_auto_mem_iff E_def)
  show ?thesis using sPiE tPiE agree by (rule PiE_ext)
qed

subsection \<open>The order of the Galois group of a simple normal extension\<close>

text \<open>\<^emph>\<open>Normality\<close> of the simple extension: all conjugates of @{term a} lie in @{term "eval_img F a"}.
  Under this hypothesis, @{term "\<lambda>\<sigma>. \<sigma> a"} is a bijection from @{term "field_auto (eval_img F a) F"}
  to the conjugate set, so the group order equals the number of conjugates.\<close>
theorem galois_simple_normal_card:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "card (field_auto (eval_img F a) F) = card {r. poly (minpoly F a) r = 0}"
proof -
  define m where "m = minpoly F a"
  define E where "E = eval_img F a"
  define R where "R = {r. poly m r = 0}"
  have sfE: "Subfield E" unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg])
  have mF: "m \<in> poly_over F" unfolding m_def by (rule Subfield.minpoly_over[OF sfF alg])
  have mnz: "m \<noteq> 0" unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mroot: "poly m a = 0" unfolding m_def by (rule Subfield.minpoly_root[OF sfF alg])
  have irr: "irreducible_over F m" unfolding m_def by (rule irreducible_over_minpoly[OF sfF alg])
  have aR: "a \<in> R" using mroot by (simp add: R_def)
  have aE: "a \<in> E" unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have FE: "F \<subseteq> E" unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have RE: "R \<subseteq> E" using normal by (simp add: R_def m_def E_def)
  have finR: "finite R" unfolding R_def using mnz by (rule poly_roots_finite)
  \<comment> \<open>Normality makes @{term E} the splitting field @{term "generate_field (F \<union> R)"}.\<close>
  have E_gen: "E = generate_field (F \<union> R)"
  proof (rule antisym)
    have "F \<union> {a} \<subseteq> F \<union> R" using aR by blast
    then have "generate_field (F \<union> {a}) \<subseteq> generate_field (F \<union> R)" by (rule generate_field_mono)
    then show "E \<subseteq> generate_field (F \<union> R)"
      using Subfield.eval_img_eq_generate_field[OF sfF alg] by (simp add: E_def)
    show "generate_field (F \<union> R) \<subseteq> E"
      using FE RE by (intro generate_field_least[OF sfE]) auto
  qed
  \<comment> \<open>Fundamental theorem of algebra: every positive-degree complex polynomial has a root.\<close>
  have closed: "\<exists>b. poly q b = 0" if "0 < degree q" for q :: "complex poly"
    using that by (intro fundamental_theorem_of_algebra) (simp add: constant_degree)
  \<comment> \<open>The bijection @{term "\<lambda>\<sigma>. \<sigma> a"} from the Galois group to the conjugate set.\<close>
  have "bij_betw (\<lambda>\<sigma>. \<sigma> a) (field_auto E F) R"
    unfolding bij_betw_def
  proof
    show inj: "inj_on (\<lambda>\<sigma>. \<sigma> a) (field_auto E F)"
    proof (rule inj_onI)
      fix \<sigma> \<tau> assume "\<sigma> \<in> field_auto E F" "\<tau> \<in> field_auto E F" "\<sigma> a = \<tau> a"
      then show "\<sigma> = \<tau>"
        using field_auto_determined_by_gen[OF sfF alg] by (simp add: E_def)
    qed
    show "(\<lambda>\<sigma>. \<sigma> a) ` field_auto E F = R"
    proof (rule antisym)
      \<comment> \<open>Well-defined: an automorphism sends @{term a} to a conjugate.\<close>
      show "(\<lambda>\<sigma>. \<sigma> a) ` field_auto E F \<subseteq> R"
      proof
        fix y assume "y \<in> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F"
        then obtain \<sigma> where s: "\<sigma> \<in> field_auto E F" and ys: "y = \<sigma> a" by blast
        have "poly m (\<sigma> a) = 0"
          using field_auto_maps_root[OF sfE sfF FE s mF aE mroot] .
        then show "y \<in> R" using ys by (simp add: R_def)
      qed
      \<comment> \<open>Onto: transitivity of the Galois action on the roots of the irreducible @{term m}.\<close>
      show "R \<subseteq> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F"
      proof
        fix b assume bR: "b \<in> R"
        have "\<forall>b\<in>R. \<exists>\<sigma>\<in>field_auto (generate_field (F \<union> R)) F. restrict \<sigma> R a = b"
          using galois_action_transitive[OF sfF finR mF irr _ closed aR] by (simp add: R_def)
        then obtain \<sigma> where s: "\<sigma> \<in> field_auto (generate_field (F \<union> R)) F"
          and sab: "restrict \<sigma> R a = b" using bR by blast
        have sE: "\<sigma> \<in> field_auto E F" using s by (simp add: E_gen)
        have "\<sigma> a = b" using sab aR by (simp add: restrict_apply)
        then show "b \<in> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F" using sE by force
      qed
    qed
  qed
  then have "card (field_auto E F) = card R" by (rule bij_betw_same_card)
  then show ?thesis by (simp add: E_def R_def m_def)
qed

subsection \<open>Separability in characteristic \<open>0\<close>: the number of conjugates is the degree\<close>

text \<open>@{const poly_over} is closed under formal differentiation: the coefficients of @{term "pderiv p"}
  are integer multiples of coefficients of @{term p} (@{thm [source] coeff_pderiv}), and a subfield
  contains all @{term "of_nat n"}.\<close>
lemma (in Subfield) poly_over_pderiv:
  assumes "p \<in> poly_over K"
  shows "pderiv p \<in> poly_over K"
proof (rule poly_overI)
  fix i
  have "coeff (pderiv p) i = of_nat (Suc i) * coeff p (Suc i)" by (rule coeff_pderiv)
  moreover have "of_nat (Suc i) \<in> K" by (rule of_nat_closed)
  moreover have "coeff p (Suc i) \<in> K" using assms by (rule poly_over_coeff)
  ultimately show "coeff (pderiv p) i \<in> K" by (simp add: mult_closed)
qed

text \<open>In characteristic @{term 0} the minimal polynomial is \<^emph>\<open>separable\<close> (squarefree): it shares no
  root with its derivative.  As @{term "pderiv m"} has smaller degree than the irreducible @{term m},
  it is not a multiple of @{term m}, so B\'ezout over @{term F} gives @{term "u * m + v * pderiv m = 1"};
  evaluating this \<^emph>\<open>polynomial identity\<close> at any root @{term r} of @{term m} yields
  @{term "poly v r * poly (pderiv m) r = 1"}, so @{term "poly (pderiv m) r \<noteq> 0"}.\<close>
lemma rsquarefree_minpoly:
  fixes F :: "'a :: field_char_0 set" and a :: 'a
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
  shows "rsquarefree (minpoly F a)"
proof -
  define m where "m = minpoly F a"
  have ism: "is_minpoly F a m" unfolding m_def by (rule Subfield.is_minpoly_minpoly[OF sfF alg])
  have mF: "m \<in> poly_over F" unfolding m_def by (rule Subfield.minpoly_over[OF sfF alg])
  have mnz: "m \<noteq> 0" unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mdeg: "degree m > 0" unfolding m_def
    by (rule Subfield.minpoly_degree_pos[OF sfF Subfield.is_minpoly_minpoly[OF sfF alg]])
  have pmF: "pderiv m \<in> poly_over F" using Subfield.poly_over_pderiv[OF sfF mF] .
  \<comment> \<open>@{term "pderiv m"} is nonzero (positive degree, char \<open>0\<close>) of degree below @{term m}.\<close>
  have pmnz: "pderiv m \<noteq> 0" using mdeg by (simp add: pderiv_eq_0_iff)
  have pmdeg: "degree (pderiv m) < degree m" using mdeg by (simp add: degree_pderiv)
  have ndvd: "\<not> m dvd pderiv m"
  proof
    assume "m dvd pderiv m"
    then have "degree m \<le> degree (pderiv m)" using pmnz by (rule dvd_imp_degree_le)
    then show False using pmdeg by simp
  qed
  \<comment> \<open>B\'ezout over @{term F}: the coefficient identity holds as polynomials.\<close>
  obtain u v where u: "u \<in> poly_over F" and v: "v \<in> poly_over F"
    and bez: "u * m + v * pderiv m = 1"
    using Subfield.minpoly_bezout[OF sfF ism pmF ndvd] by blast
  \<comment> \<open>No root of @{term m} is a root of @{term "pderiv m"}, so @{term m} is squarefree.\<close>
  have "\<not> (poly m r = 0 \<and> poly (pderiv m) r = 0)" for r
  proof
    assume "poly m r = 0 \<and> poly (pderiv m) r = 0"
    then have "poly (u * m + v * pderiv m) r = 0" by simp
    then have "(1 :: 'a) = 0" using bez by simp
    then show False by simp
  qed
  then show ?thesis unfolding m_def [symmetric]
    using mnz by (simp add: rsquarefree_roots)
qed

text \<open>Hence, over @{typ complex}, a separable minimal polynomial that splits has exactly
  @{term "degree (minpoly F a)"} distinct roots: it decomposes as a product of the distinct linear
  factors @{term "[:-z, 1:]"} (@{thm [source] complex_poly_decompose_rsquarefree}), and the degree
  of that product is the number of factors.\<close>
lemma card_conjugates_eq_degree:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
  shows "card {r. poly (minpoly F a) r = 0} = ext_degree F a"
proof -
  define m where "m = minpoly F a"
  have mnz: "m \<noteq> 0" unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have monic: "lead_coeff m = 1" unfolding m_def by (rule Subfield.minpoly_monic[OF sfF alg])
  have rsf: "rsquarefree m" unfolding m_def by (rule rsquarefree_minpoly[OF sfF alg])
  have finR: "finite {z. poly m z = 0}" using mnz by (rule poly_roots_finite)
  \<comment> \<open>Squarefree decomposition into distinct monic linear factors.\<close>
  have decomp: "smult (lead_coeff m) (\<Prod>z | poly m z = 0. [:- z, 1:]) = m"
    using rsf by (rule complex_poly_decompose_rsquarefree)
  have "degree m = degree (\<Prod>z | poly m z = 0. [:- z, 1:])"
    using decomp monic by (metis smult_1_left)
  also have "\<dots> = (\<Sum>z | poly m z = 0. degree [:- z, 1:])"
    using finR by (subst degree_prod_eq_sum_degree) auto
  also have "\<dots> = card {z. poly m z = 0}" by simp
  finally show ?thesis by (simp add: ext_degree_def m_def)
qed

subsection \<open>The headline: order of the Galois group of a simple normal extension\<close>

text \<open>\<^emph>\<open>The order of the Galois group of a simple normal extension equals the extension degree.\<close>
  Combining the bijection @{thm [source] galois_simple_normal_card} with separability
  @{thm [source] card_conjugates_eq_degree}: for a simple normal complex extension @{term "F(a)"},
  \[ \bigl|\mathrm{field\_auto}\ (F(a))\ F\bigr| = \mathrm{ext\_degree}\ F\ a = \deg(\mathrm{minpoly}\ F\ a). \]
  This is \<open>|Gal(K/F)| = [K:F]\<close> in the simple normal (separable) case.\<close>
theorem galois_simple_normal_degree:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "card (field_auto (eval_img F a) F) = ext_degree F a"
  using galois_simple_normal_card[OF sfF alg normal] card_conjugates_eq_degree[OF sfF alg]
  by simp

subsection \<open>Generic finite normal and separable extensions\<close>

text \<open>Normality of a simple extension identifies its automorphisms with the roots of the
  minimal polynomial.  The proof is the generic root-action argument: an automorphism is determined
  by the generator, maps the generator to a root, and transitivity supplies an automorphism for each
  root.\<close>
theorem galois_simple_normal_card_alg_closed:
  fixes F :: "'a :: alg_closed_field set" and a :: 'a
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "card (field_auto (eval_img F a) F) =
    card {r. poly (minpoly F a) r = 0}"
proof -
  define m where "m = minpoly F a"
  define E where "E = eval_img F a"
  define R where "R = {r. poly m r = 0}"
  have sfE: "Subfield E"
    unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg])
  have mF: "m \<in> poly_over F"
    unfolding m_def by (rule Subfield.minpoly_over[OF sfF alg])
  have mnz: "m \<noteq> 0"
    unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mroot: "poly m a = 0"
    unfolding m_def by (rule Subfield.minpoly_root[OF sfF alg])
  have irr: "irreducible_over F m"
    unfolding m_def by (rule irreducible_over_minpoly[OF sfF alg])
  have aR: "a \<in> R" using mroot by (simp add: R_def)
  have aE: "a \<in> E"
    unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have FE: "F \<subseteq> E"
    unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have RE: "R \<subseteq> E"
    using normal by (simp add: R_def m_def E_def)
  have finR: "finite R"
    unfolding R_def using mnz by (rule poly_roots_finite)
  have E_gen: "E = generate_field (F \<union> R)"
  proof (rule antisym)
    have "F \<union> {a} \<subseteq> F \<union> R" using aR by blast
    then have "generate_field (F \<union> {a}) \<subseteq> generate_field (F \<union> R)"
      by (rule generate_field_mono)
    then show "E \<subseteq> generate_field (F \<union> R)"
      using Subfield.eval_img_eq_generate_field[OF sfF alg] by (simp add: E_def)
    show "generate_field (F \<union> R) \<subseteq> E"
      using FE RE by (intro generate_field_least[OF sfE]) auto
  qed
  have action_bij:
      "bij_betw (\<lambda>\<sigma>. \<sigma> a) (field_auto E F) R"
    unfolding bij_betw_def
  proof
    show inj: "inj_on (\<lambda>\<sigma>. \<sigma> a) (field_auto E F)"
    proof (rule inj_onI)
      fix \<sigma> \<tau>
      assume "\<sigma> \<in> field_auto E F" "\<tau> \<in> field_auto E F"
        "\<sigma> a = \<tau> a"
      then show "\<sigma> = \<tau>"
        using field_auto_determined_by_gen[OF sfF alg] by (simp add: E_def)
    qed
    show "(\<lambda>\<sigma>. \<sigma> a) ` field_auto E F = R"
    proof (rule antisym)
      show "(\<lambda>\<sigma>. \<sigma> a) ` field_auto E F \<subseteq> R"
      proof
        fix y assume "y \<in> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F"
        then obtain \<sigma> where s: "\<sigma> \<in> field_auto E F" and ys: "y = \<sigma> a"
          by blast
        have "poly m (\<sigma> a) = 0"
          using field_auto_maps_root[OF sfE sfF FE s mF aE mroot] .
        then show "y \<in> R" using ys by (simp add: R_def)
      qed
      show "R \<subseteq> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F"
      proof
        fix b assume bR: "b \<in> R"
        have "\<forall>b\<in>R. \<exists>\<sigma>\<in>field_auto (generate_field (F \<union> R)) F.
            restrict \<sigma> R a = b"
          using galois_action_transitive[OF sfF finR mF irr _ alg_closed_imp_poly_has_root aR]
          by (simp add: R_def)
        then obtain \<sigma> where s: "\<sigma> \<in> field_auto (generate_field (F \<union> R)) F"
          and sab: "restrict \<sigma> R a = b" using bR by blast
        have sE: "\<sigma> \<in> field_auto E F" using s by (simp add: E_gen)
        have "\<sigma> a = b" using sab aR by (simp add: restrict_apply)
        then show "b \<in> (\<lambda>\<sigma>. \<sigma> a) ` field_auto E F" using sE by force
      qed
    qed
  qed
  have cardER: "card (field_auto E F) = card R"
    using action_bij by (rule bij_betw_same_card)
  then show ?thesis by (simp add: E_def R_def m_def)
qed

text \<open>The simple normal argument is now available over every algebraically closed field.  The
  normality hypothesis says that all roots of the minimal polynomial lie in the simple extension;
  separability supplies squarefreeness, and the generic root action supplies the matching
  automorphism count.\<close>
theorem galois_simple_normal_separable_degree:
  fixes F :: "'a :: alg_closed_field set" and a :: 'a
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
    and sep: "separable_extension (eval_img F a) F"
  shows "card (field_auto (eval_img F a) F) = ext_degree F a"
proof -
  have card_group_roots:
      "card (field_auto (eval_img F a) F) =
        card {r. poly (minpoly F a) r = 0}"
    by (rule galois_simple_normal_card_alg_closed[OF sfF alg normal])
  have aE: "a \<in> eval_img F a"
    by (rule Subfield.eval_img_self[OF sfF])
  have sep_minpoly: "rsquarefree (minpoly F a)"
    by (rule separable_extensionD[OF sep aE alg])
  have minpoly0: "minpoly F a \<noteq> 0"
    by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have card_roots_degree:
      "card {r. poly (minpoly F a) r = 0} = ext_degree F a"
  proof -
    have "card {r. poly (minpoly F a) r = 0} = degree (minpoly F a)"
      by (rule card_roots_eq_degree_alg_closed[OF minpoly0 sep_minpoly])
    then show ?thesis by (simp add: ext_degree_def)
  qed
  show ?thesis using card_group_roots card_roots_degree by simp
qed

text \<open>
  A finite normal separable extension is simple by the primitive-element theorem.  Normality then
  puts every conjugate of the primitive element back in the target field, so the preceding simple
  theorem computes the whole automorphism group.  The basis theorem identifies the simple degree
  with the intrinsic extension degree.
\<close>
context
  fixes F K :: "'a :: alg_closed_field set"
  assumes finite: "finite_subfield_tower F K"
begin

interpretation T: finite_subfield_tower F K by (rule finite)

theorem finite_normal_separable_field_auto:
  assumes normal: "normal_extension K F" and sep: "separable_extension K F"
  shows "finite (field_auto K F)"
proof -
  obtain a where aK: "a \<in> K" and prim: "primitive_element F K a"
    using finite_separable_extension_is_simple[OF finite sep] by blast
  have Kdef: "K = eval_img F a" by (rule primitive_elementD[OF prim])
  have alg: "algebraic_over F a" by (rule T.finite_extension_algebraic[OF aK])
  define p where "p = minpoly F a"
  define R where "R = {r. poly p r = 0}"
  have pF: "p \<in> poly_over F"
    unfolding p_def by (rule T.base.minpoly_over[OF alg])
  have p0: "p \<noteq> 0"
    unfolding p_def by (rule T.base.minpoly_nonzero[OF alg])
  have aR: "a \<in> R"
    unfolding R_def p_def using T.base.minpoly_root[OF alg] by simp
  have finR: "finite R" unfolding R_def using p0 by (rule poly_roots_finite)
  have roots_min: "poly_root_set (minpoly F a) \<subseteq> K"
    by (rule normal_extensionD[OF normal T.base.minpoly_over[OF alg]
      irreducible_over_minpoly[OF T.base.Subfield_axioms alg]
      aK T.base.minpoly_root[OF alg]])
  have rootsK: "R \<subseteq> K"
    using roots_min unfolding R_def p_def poly_root_set_def by simp
  have Kgen: "K = generate_field (F \<union> R)"
  proof (rule subset_antisym)
    have "K = generate_field (F \<union> {a})"
      using Kdef T.base.eval_img_eq_generate_field[OF alg] by simp
    also have "... \<subseteq> generate_field (F \<union> R)"
      by (rule generate_field_mono) (use aR in auto)
    finally show "K \<subseteq> generate_field (F \<union> R)" .
    show "generate_field (F \<union> R) \<subseteq> K"
      by (rule generate_field_least[OF T.ext.Subfield_axioms])
         (use T.base_subset rootsK in auto)
  qed
  show ?thesis
    by (rule finite_galois_group[OF T.ext.Subfield_axioms T.base.Subfield_axioms
      T.base_subset pF R_def rootsK finR Kgen])
qed

theorem finite_normal_separable_galois_degree:
  assumes normal: "normal_extension K F" and sep: "separable_extension K F"
  shows "card (field_auto K F) = T.extension_degree"
proof -
  obtain a where aK: "a \<in> K" and prim: "primitive_element F K a"
    using finite_separable_extension_is_simple[OF finite sep] by blast
  have Kdef: "K = eval_img F a" by (rule primitive_elementD[OF prim])
  have alg: "algebraic_over F a" by (rule T.finite_extension_algebraic[OF aK])
  have irr: "irreducible_over F (minpoly F a)"
    by (rule irreducible_over_minpoly[OF T.base.Subfield_axioms alg])
  have root: "poly (minpoly F a) a = 0"
    by (rule T.base.minpoly_root[OF alg])
  have rootsK: "poly_root_set (minpoly F a) \<subseteq> K"
    by (rule normal_extensionD[OF normal T.base.minpoly_over[OF alg] irr aK root])
  have roots_simple: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
    using rootsK by (simp add: poly_root_set_def Kdef)
  have card_simple:
      "card (field_auto (eval_img F a) F) = ext_degree F a"
    by (rule galois_simple_normal_separable_degree[OF T.base.Subfield_axioms alg
      roots_simple sep[unfolded Kdef]])
  have degree_simple: "T.extension_degree = ext_degree F a"
    by (rule T.primitive_element_degree[OF prim])
  show ?thesis using card_simple degree_simple by (simp add: Kdef)
qed

end

end

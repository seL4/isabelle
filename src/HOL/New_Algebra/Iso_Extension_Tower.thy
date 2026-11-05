section \<open>Extending Field Homomorphisms across Algebraic Elements\<close>

theory Iso_Extension_Tower
  imports Simple_Extension Complex_Field_Extension
begin

text \<open>
  The keystone of the iso-extension tower.  Let @{term f} be a homomorphism defined on a
  subfield @{term K} (a @{locale field_hom_on}), let @{term a} be algebraic over @{term K}
  with minimal polynomial @{term m}, and let @{term b} be a root of the @{term f}-image
  @{term "map_poly f m"} of that minimal polynomial.  Then @{term f} extends to a
  homomorphism @{term g} on the simple extension @{term "eval_img K a"} (\<open>= K(a)\<close>) that
  sends @{term a} to @{term b} and restricts to @{term f} on @{term K}.

  The extension is forced: every element of @{term "K(a)"} is @{term "poly p a"} for some
  @{term "p \<in> poly_over K"}, and @{term g} must send it to @{term "poly (map_poly f p) b"}.
  Well-definedness is the only subtlety: if @{term "poly p a = poly q a"} then @{term m}
  divides @{term "p - q"} (the kernel characterization \<open>minpoly_dvd\<close>), so
  @{term "map_poly f m"} divides @{term "map_poly f (p - q)"}, which therefore vanishes at
  its root @{term b}.
\<close>

context field_hom_on
begin

subsection \<open>The mapped polynomial @{term "map_poly f"} on @{term "poly_over K"}\<close>

text \<open>Since @{term f} is only a homomorphism \<^emph>\<open>on @{term K}\<close>, the library's @{term map_poly}
  homomorphism lemmas (which assume a global ring homomorphism) do not apply.  We re-establish
  additivity and multiplicativity of @{term "map_poly f"} restricted to polynomials over
  @{term K}, working coefficientwise.\<close>

lemma hom_sum:
  assumes "\<And>i. i \<in> A \<Longrightarrow> x i \<in> K"
  shows "f (sum x A) = (\<Sum>i\<in>A. f (x i))"
  using assms
  by (induction A rule: infinite_finite_induct) (auto simp: hom_add sum_closed)

text \<open>The coefficient lemma uses only the global @{thm [source] hom_0}.\<close>
lemma coeff_map_poly_f: "coeff (map_poly f p) n = f (coeff p n)"
  by (rule coeff_map_poly) (rule hom_0)

lemma map_poly_add_on:
  assumes "p \<in> poly_over K" "q \<in> poly_over K"
  shows "map_poly f (p + q) = map_poly f p + map_poly f q"
  by (intro poly_eqI) (simp add: assms coeff_map_poly_f hom_add poly_over_coeff)

lemma map_poly_mult_on:
  assumes "p \<in> poly_over K" "q \<in> poly_over K"
  shows "map_poly f (p * q) = map_poly f p * map_poly f q"
proof (rule poly_eqI)
  fix n
  have "coeff (map_poly f (p * q)) n = (\<Sum>k\<le>n. f (coeff p k * coeff q (n - k)))"
    by (simp add: assms coeff_map_poly_f coeff_mult hom_sum mult_closed poly_over_coeff)
  also have "\<dots> = (\<Sum>k\<le>n. f (coeff p k) * f (coeff q (n - k)))"
    using assms hom_mult poly_over_iff by force
  also have "\<dots> = coeff (map_poly f p * map_poly f q) n"
    by (simp add: coeff_map_poly_f coeff_mult)
  finally show "coeff (map_poly f (p * q)) n = coeff (map_poly f p * map_poly f q) n" .
qed

lemma map_poly_diff_on:
  assumes "p \<in> poly_over K" "q \<in> poly_over K"
  shows "map_poly f (p - q) = map_poly f p - map_poly f q"
  using assms field_hom_on.map_poly_add_on field_hom_on_axioms poly_over_diff by fastforce

lemma map_poly_const: "map_poly f [:c:] = [:f c:]"
  by (intro poly_eqI) (simp add: coeff_map_poly_f coeff_pCons split: nat.split)


subsection \<open>Evaluation commutes with the homomorphism\<close>

text \<open>@{term f} respects powers of elements of @{term K}.\<close>
lemma hom_power: "x \<in> K \<Longrightarrow> f (x ^ n) = (f x) ^ n"
  by (induction n) (auto simp: hom_mult power_closed)

text \<open>For a polynomial over @{term K} and an argument in @{term K}, evaluating the
  @{term f}-image at @{term "f x"} equals applying @{term f} to the value at @{term x}:
  evaluation is natural in @{term f}.  (The degree of @{term "map_poly f p"} may drop if
  @{term f} kills the leading coefficient, hence the @{thm [source] sum.mono_neutral_left}
  step.)\<close>
lemma poly_map_poly_hom:
  assumes p: "p \<in> poly_over K" and x: "x \<in> K"
  shows "poly (map_poly f p) (f x) = f (poly p x)"
proof -
  have ck: "\<And>i. coeff p i \<in> K" using p by (simp add: poly_over_coeff)
  have cmf: "\<And>i. coeff (map_poly f p) i = f (coeff p i)" by (rule coeff_map_poly_f)
  have rng: "(\<Sum>i\<le>degree (map_poly f p). coeff (map_poly f p) i * (f x) ^ i)
           = (\<Sum>i\<le>degree p. coeff (map_poly f p) i * (f x) ^ i)"
  proof (rule sum.mono_neutral_left)
    show "{..degree (map_poly f p)} \<subseteq> {..degree p}"
      using map_poly_degree_leq by auto
  qed (auto simp: coeff_eq_0)
  have "poly (map_poly f p) (f x) = (\<Sum>i\<le>degree p. f (coeff p i) * (f x) ^ i)"
    by (metis (no_types, lifting) ext coeff_map_poly_f poly_altdef rng)
  also have "\<dots> = (\<Sum>i\<le>degree p. f (coeff p i * x ^ i))"
    using ck x by (simp add: hom_mult power_closed hom_power)
  also have "\<dots> = f (poly p x)"
    by (simp add: ck hom_sum mult_closed poly_altdef power_closed x)
  finally show ?thesis .
qed

text \<open>Consequently @{term f} sends a root in @{term K} of a polynomial over @{term K} to a
  root of the mapped polynomial.\<close>
lemma maps_root:
  assumes p: "p \<in> poly_over K" and x: "x \<in> K" and root: "poly p x = 0"
  shows "poly (map_poly f p) (f x) = 0"
  using poly_map_poly_hom[OF p x] root by simp


subsection \<open>Well-definedness of the extension\<close>

text \<open>If two polynomials over @{term K} agree at @{term a}, their @{term f}-images agree at
  any root @{term b} of @{term "map_poly f m"}.  This is what makes the extension a function.\<close>
lemma eval_unique:
  assumes m: "is_minpoly K a m" and b: "poly (map_poly f m) b = 0"
    and p: "p \<in> poly_over K" and q: "q \<in> poly_over K" and eq: "poly p a = poly q a"
  shows "poly (map_poly f p) b = poly (map_poly f q) b"
proof -
  have mK: "m \<in> poly_over K" and monic: "lead_coeff m = 1"
    using m by (auto simp: is_minpoly_def)
  have mdeg: "degree m > 0" using minpoly_degree_pos[OF m] .
  have pq: "p - q \<in> poly_over K" using p q by (rule poly_over_diff)
  have root: "poly (p - q) a = 0" using eq by simp
  have "m dvd (p - q)" using minpoly_dvd[OF m pq root] .
  then obtain s where s: "p - q = m * s" by (elim dvdE)
    have "s = (p - q) div m" using s mdeg monic by auto
  then have "map_poly f (p - q) = map_poly f m * map_poly f s"
    using s using map_poly_mult_on[OF mK]
    by (metis mK mdeg monic poly_over_div_mod pq)
  then have "poly (map_poly f (p - q)) b = 0" using b by simp
  moreover have "map_poly f (p - q) = map_poly f p - map_poly f q"
    by (rule map_poly_diff_on[OF p q])
  ultimately show ?thesis by simp
qed


subsection \<open>The extension theorem\<close>

theorem iso_extension:
  assumes alg: "algebraic_over K a"
    and m: "is_minpoly K a m"
    and b: "poly (map_poly f m) b = 0"
  shows "\<exists>g. field_hom_on (eval_img K a) g \<and> g a = b \<and> (\<forall>x\<in>K. g x = f x)"
proof -
  define g where "g = (\<lambda>x. poly (map_poly f (SOME r. r \<in> poly_over K \<and> x = poly r a)) b)"
  have g_eval: "g (poly p a) = poly (map_poly f p) b" if p: "p \<in> poly_over K" for p
  proof -
    let ?r = "SOME r. r \<in> poly_over K \<and> poly p a = poly r a"
    have ex: "\<exists>r. r \<in> poly_over K \<and> poly p a = poly r a" using p by blast
    have r: "?r \<in> poly_over K \<and> poly p a = poly ?r a" using ex by (rule someI_ex)
    then show ?thesis using eval_unique[OF m b p] r
      using g_def by force
  qed
  have sf: "Subfield (eval_img K a)" using subfield_eval_img[OF alg] .
  interpret E: Subfield "eval_img K a" by (rule sf)
  have ga: "g a = b"
  proof -
    have "a = poly [:0,1:] a" by simp
    moreover have "[:0,1:] \<in> poly_over K" by (intro poly_over_pCons) auto
    ultimately have "g a = poly (map_poly f [:0,1:]) b" using g_eval by metis
    then show ?thesis by (simp add: map_poly_pCons map_poly_const)
  qed
  have gK: "g x = f x" if x: "x \<in> K" for x
  proof -
    have "g x = poly (map_poly f [:x:]) b" using g_eval
      using poly_over_pCons x by force
    then show ?thesis
      by (simp add: map_poly_const)
  qed
  have gadd: "g (x + y) = g x + g y" if x: "x \<in> eval_img K a" and y: "y \<in> eval_img K a" for x y
    using that g_eval  map_poly_add_on poly_over_add by (force elim!: eval_imgE)
  have gmult: "g (x * y) = g x * g y" if x: "x \<in> eval_img K a" and y: "y \<in> eval_img K a" for x y
    using that g_eval map_poly_mult_on poly_over_mult by (force elim!: eval_imgE)
  have "field_hom_on (eval_img K a) g"
    by unfold_locales (use gK gadd gmult in auto)
  then show ?thesis using ga gK by blast
qed

end

subsection \<open>Iteration over a finite set\<close>

text \<open>
  Starting from a homomorphism @{term f} defined on a subfield @{term K}, we extend it across a
  whole finite family of elements that are algebraic over @{term K}, reaching a homomorphism on
  the generated subfield @{term "generate_field (K \<union> A)"}.  Each extension step uses the
  single-element @{thm [source] field_hom_on.iso_extension}; the only external requirement is
  that the target field @{typ "'b"} contains a root for every non-constant polynomial, i.e. is
  ``closed enough''.  Over @{typ complex} this is the fundamental theorem of algebra.
\<close>

text \<open>The minimal polynomial is monic, so its image under @{term f} keeps the same degree.\<close>
lemma (in field_hom_on) map_poly_minpoly_degree:
  assumes m: "is_minpoly K a m"
  shows "degree (map_poly f m) = degree m"
proof -
  have "lead_coeff m = 1" using m by (simp add: is_minpoly_def)
  then have "f (lead_coeff m) = 1" by simp
  then show ?thesis by (intro map_poly_degree_eq) simp
qed

text \<open>A subfield is generated by itself.\<close>
lemma (in Subfield) generate_field_self: "generate_field K = K"
proof
  show "generate_field K \<subseteq> K" using Subfield_axioms subset_refl by (rule generate_field_least)
  show "K \<subseteq> generate_field K" by (rule subset_generate_field)
qed

text \<open>The single-element extension, packaged with the closed-target hypothesis discharging the
  existence of a root of the mapped minimal polynomial.\<close>
lemma field_hom_on_extend_one:
  assumes f: "field_hom_on K f"
    and alg: "algebraic_over K a"
    and closed: "\<And>q :: 'b :: field poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
  shows "\<exists>g. field_hom_on (generate_field (K \<union> {a})) g \<and> (\<forall>x\<in>K. g x = (f :: 'a :: field \<Rightarrow> 'b) x)"
proof -
  have sf: "Subfield K" using f by (rule field_hom_on.axioms(1))
  obtain m where m: "is_minpoly K a m" using Subfield.minpoly_exists[OF sf alg] by blast
  have "degree (map_poly f m) > 0"
    using m by (simp add: field_hom_on.map_poly_minpoly_degree[OF f] Subfield.minpoly_degree_pos[OF sf])
  then obtain b where b: "poly (map_poly f m) b = 0" using closed by blast
  obtain g where g: "field_hom_on (eval_img K a) g" "g a = b" "\<forall>x\<in>K. g x = f x"
    using field_hom_on.iso_extension[OF f alg m b] by blast
  have "eval_img K a = generate_field (K \<union> {a})" using Subfield.eval_img_eq_generate_field[OF sf alg] .
  then show ?thesis using g by auto
qed

text \<open>Iterating over a finite set: @{term f} extends to the subfield generated by @{term K}
  together with finitely many elements algebraic over @{term K}.\<close>
theorem field_hom_on_extend_finite:
  assumes closed: "\<And>q :: 'b :: field poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    and "finite A"
    and "field_hom_on K (f :: 'a :: field \<Rightarrow> 'b)"
    and "\<And>a. a \<in> A \<Longrightarrow> algebraic_over K a"
  shows "\<exists>g. field_hom_on (generate_field (K \<union> A)) g \<and> (\<forall>x\<in>K. g x = f x)"
  using assms(2-4)
proof (induction A rule: finite_induct)
  case empty
  have sf: "Subfield K" using empty.prems(1) by (rule field_hom_on.axioms(1))
  have "generate_field (K \<union> {}) = K" by (simp add: Subfield.generate_field_self[OF sf])
  then show ?case using empty.prems(1) by auto
next
  case (insert a A)
  define L where "L = generate_field (K \<union> A)"
  obtain g1 where g1: "field_hom_on L g1" "\<forall>x\<in>K. g1 x = f x"
    using insert.IH[OF insert.prems(1)] insert.prems(2) by (auto simp: L_def)
  have KsubL: "K \<subseteq> L"
    unfolding L_def using subset_generate_field by blast
  have algL: "algebraic_over L a"
    using insert.prems(2)[of a] KsubL by (auto intro: algebraic_over_mono)
  obtain g2 where g2: "field_hom_on (generate_field (L \<union> {a})) g2" "\<forall>x\<in>L. g2 x = g1 x"
    using field_hom_on_extend_one[OF g1(1) algL closed] by blast
  have "generate_field (L \<union> {a}) = generate_field ({a} \<union> generate_field (K \<union> A))"
    unfolding L_def by (simp add: Un_commute)
  also have "\<dots> = generate_field ({a} \<union> (K \<union> A))"
    by (rule generate_field_Un_collapse2)
  also have "\<dots> = generate_field (K \<union> insert a A)"
    by (simp add: Un_commute Un_left_commute)
  finally have "generate_field (L \<union> {a}) = generate_field (K \<union> insert a A)" .
  moreover have "\<forall>x\<in>K. g2 x = f x"
    using g2(2) g1(2) KsubL by auto
  ultimately show ?case using g2(1) by auto
qed


text \<open>
  The generic field-extension development works over an arbitrary ambient @{typ "'a :: field"} via the @{locale Subfield} and
  @{locale field_hom_on} locales.  The complex-specific Galois theory of
  \<open>Complex_Field_Extension\<close> instead fixes @{typ complex} and packages automorphisms as the set
  @{const field_auto}. Now we connect the two.
\<close>
text \<open>The two subfield notions coincide on @{typ complex}.\<close>
lemma complex_subfield_iff_subfield: "complex_subfield K \<longleftrightarrow> Subfield K"
proof
  assume "complex_subfield K"
  then interpret complex_subfield K .
  show "Subfield K"
    using complex_subfield_axioms complex_subfield_def Subfield.intro by fastforce
next
  assume "Subfield K"
  then interpret Subfield K .
  show "complex_subfield K"
    by unfold_locales (auto intro: add_closed uminus_closed mult_closed inverse_closed)
qed

text \<open>A field homomorphism on @{term K} (in the generic sense) that maps @{term K} \<^emph>\<open>onto\<close>
  itself and fixes a base subfield @{term F} pointwise restricts to an element of the complex
  Galois group @{term "field_auto K F"}n.\<close>
lemma field_hom_on_imp_field_auto:
  assumes hom: "field_hom_on K \<sigma>"
    and onto: "\<sigma> ` K = K"
    and fix_F: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x" and FK: "F \<subseteq> K"
  shows "restrict \<sigma> K \<in> field_auto K F"
proof -
  interpret S: field_hom_on K \<sigma> by (rule hom)
  have bij: "bij_betw (restrict \<sigma> K) K K"
    by (simp add: S.inj_on bij_betw_def onto)
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "restrict \<sigma> K \<in> K \<rightarrow>\<^sub>E K"
      using onto by auto
    show "bij_betw (restrict \<sigma> K) K K" by (rule bij)
    show "\<And>x. x \<in> F \<Longrightarrow> restrict \<sigma> K x = x" using fix_F FK by auto
  qed (use S.hom_1 S.one_closed S.hom_add S.add_closed S.hom_mult S.mult_closed in auto)
qed

end

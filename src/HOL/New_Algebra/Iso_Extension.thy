section \<open>Extending a Field Homomorphism across a Simple Algebraic Extension\<close>

theory Iso_Extension
  imports Simple_Extension
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

end

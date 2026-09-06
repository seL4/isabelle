section \<open>Simple Algebraic Extensions are Subfields\<close>

theory Simple_Extension
  imports Field_Extension_Tower
begin

text \<open>
  The simple extension \<open>K(a)\<close> of a subfield @{term K} by an element @{term a} algebraic over
  @{term K} is realised as the set of polynomial expressions @{term "poly p a"} for
  @{term "p \<in> poly_over K"}.  It is a subfield: closure under the ring operations is immediate
  (evaluation is a ring homomorphism), and closure under inverse is the payoff of B\'ezout's
  identity over @{term K}.
\<close>

definition eval_img :: "'a :: field set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "eval_img K a = (\<lambda>p. poly p a) ` poly_over K"

lemma eval_imgI: "p \<in> poly_over K \<Longrightarrow> poly p a \<in> eval_img K a"
  by (auto simp: eval_img_def)

lemma eval_imgE:
  assumes "y \<in> eval_img K a" obtains p where "p \<in> poly_over K" "y = poly p a"
  using assms by (auto simp: eval_img_def)

context Subfield
begin

lemma eval_img_self: "a \<in> eval_img K a"
proof -
  have "poly [:0, 1:] a = a" by simp
  then show ?thesis
    by (metis eval_imgI one_closed poly_over_0 poly_over_pCons zero_closed)
qed

lemma eval_img_base:
  assumes "c \<in> K"
  shows "c \<in> eval_img K a"
proof -
  have "[:c:] \<in> poly_over K"
    by (simp add: assms poly_over_pCons)
  then show ?thesis
    using eval_imgI by fastforce
qed

lemma eval_img_0: "0 \<in> eval_img K a"
  using eval_img_base zero_closed by blast

lemma eval_img_1: "1 \<in> eval_img K a"
  using eval_img_base one_closed by blast

lemma eval_img_add: "x \<in> eval_img K a \<Longrightarrow> y \<in> eval_img K a \<Longrightarrow> x + y \<in> eval_img K a"
  by (metis (no_types, lifting) eval_imgE eval_imgI poly_add poly_over_add)

lemma eval_img_uminus: "x \<in> eval_img K a \<Longrightarrow> -x \<in> eval_img K a"
  by (metis eval_imgE eval_imgI poly_minus poly_over_uminus)

lemma eval_img_mult: "x \<in> eval_img K a \<Longrightarrow> y \<in> eval_img K a \<Longrightarrow> x * y \<in> eval_img K a"
  by (metis (no_types, lifting) eval_imgE eval_imgI poly_mult poly_over_mult)

text \<open>Closure under inverse, the payoff of B\'ezout.\<close>
lemma eval_img_inverse:
  assumes alg: "algebraic_over K a" and y: "y \<in> eval_img K a" and ynz: "y \<noteq> 0"
  shows "inverse y \<in> eval_img K a"
proof -
  obtain p where p: "p \<in> poly_over K" and yp: "y = poly p a" using y by (rule eval_imgE)
  obtain m where m: "is_minpoly K a m" using minpoly_exists[OF alg] by blast
  have m0: "poly m a = 0" using m by (simp add: is_minpoly_def)
  have "\<not> m dvd p"
    using m0 ynz yp by auto
  then obtain u v where uv: "u \<in> poly_over K" "v \<in> poly_over K" "u * m + v * p = 1"
    using minpoly_bezout[OF m p] by blast
  have "poly (u * m + v * p) a = poly 1 a" using uv(3) by simp
  then have "inverse y = poly v a"
    by (simp add: inverse_unique m0 mult.commute yp)
  then show ?thesis using uv(2) by (metis eval_imgI)
qed

text \<open>Hence, for @{term a} algebraic over @{term K}, the simple extension is a subfield.\<close>
theorem subfield_eval_img:
  assumes "algebraic_over K a" shows "Subfield (eval_img K a)"
proof
  show "\<And>x. x \<in> eval_img K a \<Longrightarrow> inverse x \<in> eval_img K a"
    using assms eval_img_inverse by force
qed (auto simp: eval_img_0 eval_img_1 eval_img_add eval_img_uminus eval_img_mult eval_img_inverse)

text \<open>The simple extension @{term "eval_img K a"} coincides with the generically generated
  subfield @{term "generate_field (K \<union> {a})"} of theory \<open>Subfield\<close>.  This connects the
  polynomial-evaluation construction to the inductive @{const generate_field}, so the tower of
  intermediate fields can be expressed either way.  The forward inclusion is unconditional;
  the reverse uses that @{term "eval_img K a"} is itself a subfield (so @{const generate_field}
  of a generating subset of it stays inside).\<close>
lemma eval_img_subset_generate_field:
  assumes "p \<in> poly_over K"
  shows "poly p a \<in> generate_field (K \<union> {a})"
proof -
  interpret G: Subfield "generate_field (K \<union> {a})" by (rule subfield_generate_field)
  have aG: "a \<in> generate_field (K \<union> {a})" by (auto intro: generate_field_base)
  have cG: "coeff p i \<in> generate_field (K \<union> {a})" for i
    using assms by (auto simp: poly_over_coeff intro: generate_field_base)
  then show ?thesis
    unfolding poly_altdef
    using aG cG by (intro G.sum_closed G.mult_closed G.power_closed)
qed

lemma eval_img_eq_generate_field:
  assumes alg: "algebraic_over K a"
  shows "eval_img K a = generate_field (K \<union> {a})"
proof
  show "eval_img K a \<subseteq> generate_field (K \<union> {a})"
    by (metis eval_imgE eval_img_subset_generate_field subsetI)
next
  have "K \<union> {a} \<subseteq> eval_img K a"
    using eval_img_base eval_img_self by auto
  then show "generate_field (K \<union> {a}) \<subseteq> eval_img K a"
    by (rule generate_field_least[OF subfield_eval_img[OF alg]])
qed

end

end

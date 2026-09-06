section \<open>Finite-dimensional extensions and transitivity of algebraicity\<close>

theory Algebraic_Transitivity
  imports Finite_Extension
begin

text \<open>With the vector-space bridge of \<open>Extension_Vector_Space\<close> in place, the
  Steinitz cardinality bound @{thm [source] Vector_Space.independent_le_span} yields the classical
  chain

    \<^item> a finite-dimensional extension is \<^emph>\<open>algebraic\<close> (every element satisfies a polynomial: its powers
      cannot all be independent);
    \<^item> \<^emph>\<open>transitivity of algebraicity\<close> --- if @{term a} is algebraic over @{term K} and @{term b} is
      algebraic over the simple extension \<open>K(a)\<close>, then @{term b} is algebraic over @{term K}.

  This is the last field-theoretic prerequisite of the quintic finish: it upgrades ``a radical is
  algebraic over the immediate base'' to ``a radical is algebraic over the ground field'', so the
  normal closure can be taken as the splitting field of a single ground-field polynomial.\<close>

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

subsection \<open>A finite-dimensional extension is algebraic\<close>

text \<open>If the extension @{term L} of @{term K} is spanned over @{term K} by a finite set @{term B},
  then every element of @{term L} is algebraic over @{term K}.  For @{term "y \<in> L"} the
  @{term "card B + 1"} powers @{term "y ^ i"} (with \<open>i \<le> card B\<close>) all lie in the span of @{term B},
  so by the Steinitz bound they are linearly dependent: some nontrivial @{term K}-combination
  vanishes, i.e.\ a nonzero polynomial over @{term K} kills @{term y}.\<close>
lemma (in subfield_tower) findim_imp_algebraic:
  assumes finB: "finite B" and BL: "B \<subseteq> L" and span: "L \<subseteq> vs.span B" and y: "y \<in> L"
  shows "algebraic_over K y"
proof (cases "inj_on (\<lambda>i. y ^ i) {..card B}")
  case False
  \<comment> \<open>Two distinct powers of @{term y} coincide: the nonzero polynomial \<open>X\<^sup>i - X\<^sup>j\<close> (over the
     prime field, so over @{term K}) kills @{term y}.\<close>
  then obtain i j where ij: "i \<in> {..card B}" "j \<in> {..card B}" "i \<noteq> j" "y ^ i = y ^ j"
    by (auto simp: inj_on_def)
  define p where "p = (monom 1 i - monom 1 j :: 'a poly)"
  have p_over: "p \<in> poly_over K"
    unfolding p_def by (intro base.poly_over_diff base.poly_over_monom base.one_closed)
  have p_root: "poly p y = 0"
    unfolding p_def using ij(4) by (simp add: poly_monom)
  have p_nz: "p \<noteq> 0"
    unfolding p_def by (meson eq_iff_diff_eq_0 monom_eq_iff' one_neq_zero \<open>i \<noteq> j\<close>)
  show ?thesis unfolding algebraic_over_def using p_over p_nz p_root by blast
next
  case True
  define n where "n = card B"
  define P where "P = (\<lambda>i. y ^ i) ` {..n}"
  have injn: "inj_on (\<lambda>i. y ^ i) {..n}" using True by (simp add: n_def)
  have yp_L: "\<And>i. y ^ i \<in> L" using y by (intro ext.power_closed)
  have PL: "P \<subseteq> L" using yp_L by (auto simp: P_def)
  have finP: "finite P" by (simp add: P_def)
  have Pspan: "P \<subseteq> vs.span B" using PL span by blast
  \<comment> \<open>@{term P} has @{term "n+1"} elements but sits in @{term "vs.span B"} with @{term "card B = n"}, so
     by the Steinitz bound it cannot be independent.\<close>
  have cardP: "card P = n + 1" using injn by (simp add: P_def card_image)
  have "\<not> vs.lin_indep P"
    using BL Pspan cardP finB n_def vs.independent_le_span by fastforce
  \<comment> \<open>The dependence gives a nonzero @{term K}-combination of powers that vanishes.\<close>
  then obtain c where cPiE: "c \<in> P \<rightarrow>\<^sub>E K" and lc0: "vs.lincomb c P = 0"
    and nz: "\<not> (\<forall>v\<in>P. c v = 0)"
    using finP PL by (auto simp: vs.lin_indep_def)
  have cK: "\<And>v. v \<in> P \<Longrightarrow> c v \<in> K" using cPiE by auto
  have sum0: "(\<Sum>v\<in>P. c v * v) = 0" using vs_lincomb_eq_sum[OF finP PL cK] lc0 by simp
  \<comment> \<open>Re-index through the (injective) power map to a genuine polynomial sum.\<close>
  define d where "d = (\<lambda>i. c (y ^ i))"
  have "(\<Sum>v\<in>P. c v * v) = (\<Sum>i\<le>n. c (y ^ i) * y ^ i)"
    unfolding P_def by (subst sum.reindex[OF injn]) (simp add: o_def)
  then have sumd0: "(\<Sum>i\<le>n. d i * y ^ i) = 0" using sum0 by (simp add: d_def)
  define p where "p = (\<Sum>i\<le>n. monom (d i) i :: 'a poly)"
  have dK: "\<And>i. i \<le> n \<Longrightarrow> d i \<in> K" using cK by (auto simp: d_def P_def)
  have p_over: "p \<in> poly_over K"
    unfolding p_def
    by (intro base.poly_over_sum base.poly_over_monom) (simp add: dK)
  have p_root: "poly p y = 0"
    unfolding p_def by (simp add: poly_sum poly_monom sumd0)
  have p_nz: "p \<noteq> 0"
  proof -
    from nz obtain v where v: "v \<in> P" "c v \<noteq> 0" by blast
    then obtain i where i: "i \<le> n" "v = y ^ i" by (auto simp: P_def)
    have "coeff p i = d i"
      unfolding p_def using i by (simp add: coeff_sum coeff_monom)
    then show ?thesis
      using d_def i(2) v(2) by fastforce
  qed
  show ?thesis unfolding algebraic_over_def using p_over p_nz p_root by blast
qed

text \<open>Finite-dimensionality makes every target element algebraic over the base.  This bridge belongs
  with the finite-dimensional algebraicity theorem, so clients need not import primitive-element
  constructions merely to use it.\<close>
lemma (in finite_subfield_tower) finite_extension_algebraic:
  assumes aL: "a \<in> L"
  shows "algebraic_over K a"
proof -
  obtain B where B: "vs.basis B" using finite_basis_exists by blast
  have Bsp: "vs.spanning B" by (rule vs.basis_spanning[OF B])
  have finB: "finite B" using B unfolding vs.basis_def by (rule conjunct1)
  have BL: "B \<subseteq> L" using B unfolding vs.basis_def
    by (rule conjunct2[THEN conjunct1])
  have mod_span: "vs.mod.spanning B"
    using Bsp by (simp add: vs.spanning_iff_mod_spanning[OF finB BL])
  have spanL: "L \<subseteq> vs.span B"
  proof
    fix x assume xL: "x \<in> L"
    have "x \<in> vs.mod.span B" using mod_span xL by (rule vs.mod.spanningD)
    then show "x \<in> vs.span B" by (simp add: vs.span_def)
  qed
  show ?thesis using findim_imp_algebraic[OF finB BL spanL aL] .
qed


subsection \<open>Transitivity of algebraicity\<close>

text \<open>\<^emph>\<open>Transitivity.\<close>  If @{term a} is algebraic over @{term K} and @{term b} is algebraic over the
  simple extension @{term "eval_img K a"}, then @{term b} is algebraic over @{term K}.

  The two-step tower \<open>K \<subseteq> K(a) \<subseteq> K(a)(b)\<close> is spanned over @{term K} by the finite set of
  products @{term "a ^ i * b ^ j"} (@{thm [source] tower_power_basis_span}); so
  \<open>K(a)(b)\<close> is a finite-dimensional extension of @{term K}, and @{term b}, being one of its
  elements, is algebraic over @{term K} by @{thm [source] subfield_tower.findim_imp_algebraic}.\<close>
theorem algebraic_over_transitive:
  assumes K: "Subfield K"
    and alg_a: "algebraic_over K a"
    and alg_b: "algebraic_over (eval_img K a) b"
  shows "algebraic_over K b"
proof -
  define E where "E = eval_img K a"
  define L where "L = eval_img E b"
  have subE: "Subfield E" unfolding E_def by (rule Subfield.subfield_eval_img[OF K alg_a])
  have algbE: "algebraic_over E b" using alg_b by (simp add: E_def)
  have subL: "Subfield L" unfolding L_def by (rule Subfield.subfield_eval_img[OF subE algbE])
  \<comment> \<open>@{term "K \<subseteq> L"}: @{term K} sits inside \<open>E = K(a)\<close> inside \<open>L = E(b)\<close>.\<close>
  interpret KL: subfield_tower K L
    using subfield_tower.intro[OF K subL]
    by (metis E_def K L_def subE Subfield.eval_img_base subfield_tower_axioms.intro subsetI)
  \<comment> \<open>The finite product set @{term "a ^ i * b ^ j"} spans @{term L} over @{term K}.\<close>
  define da where "da = ext_degree K a"
  define db where "db = ext_degree E b"
  define B where "B = (\<lambda>(j,i). a ^ i * b ^ j) ` ({..<db} \<times> {..<da})"
  have finB: "finite B" by (simp add: B_def)
  have aE: "a \<in> E" unfolding E_def by (rule Subfield.eval_img_self[OF K])
  obtain aL: "a \<in> L" and bL: "b \<in> L"
    using L_def aE subE Subfield.eval_img_base Subfield.eval_img_self by blast
  have prodL: "\<And>i j. a ^ i * b ^ j \<in> L" 
    using aL bL by (intro KL.ext.mult_closed KL.ext.power_closed)
  have BL: "B \<subseteq> L" using prodL by (auto simp: B_def)
  have spanL: "L \<subseteq> KL.vs.span B"
  proof
    fix y assume "y \<in> L"
    then have yL: "y \<in> eval_img (eval_img K a) b" by (simp add: L_def E_def)
    obtain c where cK: "\<And>i j. i < da \<Longrightarrow> j < db \<Longrightarrow> c i j \<in> K"
      and yeq: "y = (\<Sum>j < db. \<Sum>i < da. c i j * (a ^ i * b ^ j))"
      using tower_power_basis_span[OF K alg_a alg_b yL] by (auto simp: da_def db_def E_def)
    \<comment> \<open>Flatten the double sum over the index rectangle, then push it into the span of @{term B}.\<close>
    then have yeq': "y = (\<Sum>ji\<in>{..<db} \<times> {..<da}.
                              (\<lambda>(j,i). c i j) ji * (\<lambda>(j,i). a ^ i * b ^ j) ji)" 
      by (force simp: sum.cartesian_product intro: sum.cong)
    have "(\<Sum>ji\<in>{..<db} \<times> {..<da}. (\<lambda>(j,i). c i j) ji * (\<lambda>(j,i). a ^ i * b ^ j) ji)
            \<in> KL.vs.span ((\<lambda>(j,i). a ^ i * b ^ j) ` ({..<db} \<times> {..<da}))"
      by (rule KL.sum_scale_in_span) (auto simp: prodL cK)
    then show "y \<in> KL.vs.span B" using yeq' by (simp add: B_def)
  qed
  show "algebraic_over K b" using KL.findim_imp_algebraic[OF finB BL spanL bL] .
qed

subsection \<open>Algebraicity along a radical/simple tower\<close>

text \<open>Every element of a simple algebraic extension @{term "eval_img K a"} is itself algebraic over
  @{term K}: the extension is spanned over @{term K} by the finite power basis @{term "a ^ i"}
  (@{thm [source] Subfield.power_basis_span}), so @{thm [source] subfield_tower.findim_imp_algebraic}
  applies.\<close>
theorem simple_ext_algebraic:
  assumes K: "Subfield K" and alg_a: "algebraic_over K a" and y: "y \<in> eval_img K a"
  shows "algebraic_over K y"
proof -
  define L where "L = eval_img K a"
  define d where "d = ext_degree K a"
  have subL: "Subfield L" unfolding L_def by (rule Subfield.subfield_eval_img[OF K alg_a])
  have KL: "K \<subseteq> L" unfolding L_def using Subfield.eval_img_base[OF K] by blast
  interpret KL: subfield_tower K L by (rule subfield_tower.intro[OF K subL]) (unfold_locales, rule KL)
  \<comment> \<open>The power basis \<open>{a\<^sup>i | i < d}\<close> spans @{term L} over @{term K}.\<close>
  define B where "B = (\<lambda>i. a ^ i) ` {..<d}"
  have finB: "finite B" by (simp add: B_def)
  have aL: "a \<in> L" unfolding L_def by (rule Subfield.eval_img_self[OF K])
  have powL: "\<And>i. a ^ i \<in> L" using aL by (intro KL.ext.power_closed)
  have spanL: "L \<subseteq> KL.vs.span B"
  proof
    fix z assume "z \<in> L"
    then have zL: "z \<in> eval_img K a" by (simp add: L_def)
    obtain c where cK: "\<And>i. i < d \<Longrightarrow> c i \<in> K" and zc: "z = (\<Sum>i<d. c i * a ^ i)"
      using Subfield.power_basis_span[OF K alg_a zL] by (auto simp: d_def)
    then show "z \<in> KL.vs.span B"
      unfolding B_def
      by (metis (full_types) KL.sum_scale_in_span finite_lessThan lessThan_iff powL)
  qed
  have BL: "B \<subseteq> L" using powL by (auto simp: B_def)
  show ?thesis using KL.findim_imp_algebraic[OF finB BL spanL] y by (simp add: L_def)
qed

text \<open>Two successive simple algebraic extensions are algebraic over the original base.  This
interface is useful when proving closure of the algebraic elements under field operations: the
operation is first placed in the two-step generated field, and this lemma supplies its
algebraicity over the base.\<close>
lemma algebraic_over_two_step:
  fixes F :: "'a :: field set" and a b y :: 'a
  assumes sfF: "Subfield F"
    and alg_a: "algebraic_over F a"
    and alg_b: "algebraic_over F b"
    and y: "y \<in> eval_img (eval_img F a) b"
  shows "algebraic_over F y"
proof -
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg_a])
  have FE: "F \<subseteq> eval_img F a"
    using Subfield.eval_img_base[OF sfF] by blast
  have alg_bE: "algebraic_over (eval_img F a) b"
    by (rule algebraic_over_mono[OF alg_b FE])
  have alg_yE: "algebraic_over (eval_img F a) y"
    by (rule simple_ext_algebraic[OF sfE alg_bE y])
  show ?thesis
    by (rule algebraic_over_transitive[OF sfF alg_a alg_yE])
qed

definition algebraic_elements :: "'a :: field set \<Rightarrow> 'a set" where
  "algebraic_elements F = {a. algebraic_over F a}"

text \<open>Algebraic elements over a subfield form a subfield.  Addition and multiplication are
handled through @{thm [source] algebraic_over_two_step}; negation and inversion already lie in
the corresponding simple extension.\<close>
lemma subfield_algebraic_elements:
  fixes F :: "'a :: field set"
  assumes sfF: "Subfield F"
  shows "Subfield (algebraic_elements F)"
proof
  have zero_alg: "algebraic_over F (0 :: 'a)"
    by (rule Subfield.algebraic_over_self[OF sfF]) (rule Subfield.zero_closed[OF sfF])
  have one_alg: "algebraic_over F (1 :: 'a)"
    by (rule Subfield.algebraic_over_self[OF sfF]) (rule Subfield.one_closed[OF sfF])
  show "0 \<in> algebraic_elements F"
    using zero_alg by (simp add: algebraic_elements_def)
  show "1 \<in> algebraic_elements F"
    using one_alg by (simp add: algebraic_elements_def)
next
  fix a b
  assume a: "a \<in> algebraic_elements F" and b: "b \<in> algebraic_elements F"
  have alg_a: "algebraic_over F a"
    using a by (simp add: algebraic_elements_def)
  have alg_b: "algebraic_over F b"
    using b by (simp add: algebraic_elements_def)
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg_a])
  have aE: "a \<in> eval_img F a"
    by (rule Subfield.eval_img_self[OF sfF])
  have aL: "a \<in> eval_img (eval_img F a) b"
    using Subfield.eval_img_base[OF sfE aE] .
  have bL: "b \<in> eval_img (eval_img F a) b"
    by (rule Subfield.eval_img_self[OF sfE])
  have sumL: "a + b \<in> eval_img (eval_img F a) b"
    by (rule Subfield.eval_img_add[OF sfE aL bL])
  show "a + b \<in> algebraic_elements F"
    using algebraic_over_two_step[OF sfF alg_a alg_b sumL]
    by (simp add: algebraic_elements_def)
next
  fix a
  assume a: "a \<in> algebraic_elements F"
  have alg_a: "algebraic_over F a"
    using a by (simp add: algebraic_elements_def)
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg_a])
  have aE: "a \<in> eval_img F a"
    by (rule Subfield.eval_img_self[OF sfF])
  have negE: "-a \<in> eval_img F a"
    using sfE aE by (rule Subfield.uminus_closed)
  show "-a \<in> algebraic_elements F"
    using simple_ext_algebraic[OF sfF alg_a negE]
    by (simp add: algebraic_elements_def)
next
  fix a b
  assume a: "a \<in> algebraic_elements F" and b: "b \<in> algebraic_elements F"
  have alg_a: "algebraic_over F a"
    using a by (simp add: algebraic_elements_def)
  have alg_b: "algebraic_over F b"
    using b by (simp add: algebraic_elements_def)
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg_a])
  have aE: "a \<in> eval_img F a"
    by (rule Subfield.eval_img_self[OF sfF])
  have aL: "a \<in> eval_img (eval_img F a) b"
    using Subfield.eval_img_base[OF sfE aE] .
  have bL: "b \<in> eval_img (eval_img F a) b"
    by (rule Subfield.eval_img_self[OF sfE])
  have multL: "a * b \<in> eval_img (eval_img F a) b"
    by (rule Subfield.eval_img_mult[OF sfE aL bL])
  show "a * b \<in> algebraic_elements F"
    using algebraic_over_two_step[OF sfF alg_a alg_b multL]
    by (simp add: algebraic_elements_def)
next
  fix a
  assume a: "a \<in> algebraic_elements F"
  have alg_a: "algebraic_over F a"
    using a by (simp add: algebraic_elements_def)
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg_a])
  have aE: "a \<in> eval_img F a"
    by (rule Subfield.eval_img_self[OF sfF])
  have invE: "inverse a \<in> eval_img F a"
    using sfE aE by (rule Subfield.inverse_closed)
  show "inverse a \<in> algebraic_elements F"
    using simple_ext_algebraic[OF sfF alg_a invE]
    by (simp add: algebraic_elements_def)
qed

text \<open>Generation by algebraic elements preserves algebraicity.  The generated field is
contained in the subfield of all elements algebraic over the base, so no representation of
generated elements or basis choice is exposed to clients.\<close>
lemma generated_algebraic:
  fixes F A :: "'a :: field set"
  assumes sfF: "Subfield F"
    and algA: "\<And>a. a \<in> A \<Longrightarrow> algebraic_over F a"
  shows "\<And>x. x \<in> generate_field (F \<union> A) \<Longrightarrow> algebraic_over F x"
proof -
  have FA: "F \<union> A \<subseteq> algebraic_elements F"
    unfolding algebraic_elements_def
    using algA Subfield.algebraic_over_self[OF sfF]
    by blast
  have gen: "generate_field (F \<union> A) \<subseteq> algebraic_elements F"
    by (rule generate_field_least[OF subfield_algebraic_elements[OF sfF] FA])
  fix x assume x: "x \<in> generate_field (F \<union> A)"
  have "x \<in> algebraic_elements F"
    using gen x by blast
  then show "algebraic_over F x"
    by (simp add: algebraic_elements_def)
qed

end

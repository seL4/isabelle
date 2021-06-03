section \<open>Contour integration\<close>
theory Contour_Integration
  imports "HOL-Analysis.Analysis"
begin

lemma lhopital_complex_simple:
  assumes "(f has_field_derivative f') (at z)"
  assumes "(g has_field_derivative g') (at z)"
  assumes "f z = 0" "g z = 0" "g' \<noteq> 0" "f' / g' = c"
  shows   "((\<lambda>w. f w / g w) \<longlongrightarrow> c) (at z)"
proof -
  have "eventually (\<lambda>w. w \<noteq> z) (at z)"
    by (auto simp: eventually_at_filter)
  hence "eventually (\<lambda>w. ((f w - f z) / (w - z)) / ((g w - g z) / (w - z)) = f w / g w) (at z)"
    by eventually_elim (simp add: assms field_split_simps)
  moreover have "((\<lambda>w. ((f w - f z) / (w - z)) / ((g w - g z) / (w - z))) \<longlongrightarrow> f' / g') (at z)"
    by (intro tendsto_divide has_field_derivativeD assms)
  ultimately have "((\<lambda>w. f w / g w) \<longlongrightarrow> f' / g') (at z)"
    by (blast intro: Lim_transform_eventually)
  with assms show ?thesis by simp
qed

subsection\<open>Definition\<close>

text\<open>
  This definition is for complex numbers only, and does not generalise to 
  line integrals in a vector field
\<close>

definition\<^marker>\<open>tag important\<close> has_contour_integral :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool"
           (infixr "has'_contour'_integral" 50)
  where "(f has_contour_integral i) g \<equiv>
           ((\<lambda>x. f(g x) * vector_derivative g (at x within {0..1}))
            has_integral i) {0..1}"

definition\<^marker>\<open>tag important\<close> contour_integrable_on
           (infixr "contour'_integrable'_on" 50)
  where "f contour_integrable_on g \<equiv> \<exists>i. (f has_contour_integral i) g"

definition\<^marker>\<open>tag important\<close> contour_integral
  where "contour_integral g f \<equiv> SOME i. (f has_contour_integral i) g \<or> \<not> f contour_integrable_on g \<and> i=0"

lemma not_integrable_contour_integral: "\<not> f contour_integrable_on g \<Longrightarrow> contour_integral g f = 0"
  unfolding contour_integrable_on_def contour_integral_def by blast

lemma contour_integral_unique: "(f has_contour_integral i) g \<Longrightarrow> contour_integral g f = i"
  apply (simp add: contour_integral_def has_contour_integral_def contour_integrable_on_def)
  using has_integral_unique by blast

lemma has_contour_integral_eqpath:
     "\<lbrakk>(f has_contour_integral y) p; f contour_integrable_on \<gamma>;
       contour_integral p f = contour_integral \<gamma> f\<rbrakk>
      \<Longrightarrow> (f has_contour_integral y) \<gamma>"
using contour_integrable_on_def contour_integral_unique by auto

lemma has_contour_integral_integral:
    "f contour_integrable_on i \<Longrightarrow> (f has_contour_integral (contour_integral i f)) i"
  by (metis contour_integral_unique contour_integrable_on_def)

lemma has_contour_integral_unique:
    "(f has_contour_integral i) g \<Longrightarrow> (f has_contour_integral j) g \<Longrightarrow> i = j"
  using has_integral_unique
  by (auto simp: has_contour_integral_def)

lemma has_contour_integral_integrable: "(f has_contour_integral i) g \<Longrightarrow> f contour_integrable_on g"
  using contour_integrable_on_def by blast

text\<open>Show that we can forget about the localized derivative.\<close>

lemma has_integral_localized_vector_derivative:
    "((\<lambda>x. f (g x) * vector_derivative p (at x within {a..b})) has_integral i) {a..b} \<longleftrightarrow>
     ((\<lambda>x. f (g x) * vector_derivative p (at x)) has_integral i) {a..b}"
proof -
  have *: "{a..b} - {a,b} = interior {a..b}"
    by (simp add: atLeastAtMost_diff_ends)
  show ?thesis
    by (rule has_integral_spike_eq [of "{a,b}"]) (auto simp: at_within_interior [of _ "{a..b}"])
qed

lemma integrable_on_localized_vector_derivative:
    "(\<lambda>x. f (g x) * vector_derivative p (at x within {a..b})) integrable_on {a..b} \<longleftrightarrow>
     (\<lambda>x. f (g x) * vector_derivative p (at x)) integrable_on {a..b}"
  by (simp add: integrable_on_def has_integral_localized_vector_derivative)

lemma has_contour_integral:
     "(f has_contour_integral i) g \<longleftrightarrow>
      ((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
  by (simp add: has_integral_localized_vector_derivative has_contour_integral_def)

lemma contour_integrable_on:
     "f contour_integrable_on g \<longleftrightarrow>
      (\<lambda>t. f(g t) * vector_derivative g (at t)) integrable_on {0..1}"
  by (simp add: has_contour_integral integrable_on_def contour_integrable_on_def)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Reversing a path\<close>



lemma has_contour_integral_reversepath:
  assumes "valid_path g" and f: "(f has_contour_integral i) g"
    shows "(f has_contour_integral (-i)) (reversepath g)"
proof -
  { fix S x
    assume xs: "g C1_differentiable_on ({0..1} - S)" "x \<notin> (-) 1 ` S" "0 \<le> x" "x \<le> 1"
    have "vector_derivative (\<lambda>x. g (1 - x)) (at x within {0..1}) =
            - vector_derivative g (at (1 - x) within {0..1})"
    proof -
      obtain f' where f': "(g has_vector_derivative f') (at (1 - x))"
        using xs
        by (force simp: has_vector_derivative_def C1_differentiable_on_def)
      have "(g \<circ> (\<lambda>x. 1 - x) has_vector_derivative -1 *\<^sub>R f') (at x)"
        by (intro vector_diff_chain_within has_vector_derivative_at_within [OF f'] derivative_eq_intros | simp)+
      then have mf': "((\<lambda>x. g (1 - x)) has_vector_derivative -f') (at x)"
        by (simp add: o_def)
      show ?thesis
        using xs
        by (auto simp: vector_derivative_at_within_ivl [OF mf'] vector_derivative_at_within_ivl [OF f'])
    qed
  } note * = this
  obtain S where S: "continuous_on {0..1} g" "finite S" "g C1_differentiable_on {0..1} - S"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have "((\<lambda>x. - (f (g (1 - x)) * vector_derivative g (at (1 - x) within {0..1}))) has_integral -i)
       {0..1}"
    using has_integral_affinity01 [where m= "-1" and c=1, OF f [unfolded has_contour_integral_def]]
    by (simp add: has_integral_neg)
  then show ?thesis
    using S
    unfolding reversepath_def has_contour_integral_def
    by (rule_tac S = "(\<lambda>x. 1 - x) ` S" in has_integral_spike_finite) (auto simp: *)
qed

lemma contour_integrable_reversepath:
    "valid_path g \<Longrightarrow> f contour_integrable_on g \<Longrightarrow> f contour_integrable_on (reversepath g)"
  using has_contour_integral_reversepath contour_integrable_on_def by blast

lemma contour_integrable_reversepath_eq:
    "valid_path g \<Longrightarrow> (f contour_integrable_on (reversepath g) \<longleftrightarrow> f contour_integrable_on g)"
  using contour_integrable_reversepath valid_path_reversepath by fastforce

lemma contour_integral_reversepath:
  assumes "valid_path g"
    shows "contour_integral (reversepath g) f = - (contour_integral g f)"
proof (cases "f contour_integrable_on g")
  case True then show ?thesis
    by (simp add: assms contour_integral_unique has_contour_integral_integral has_contour_integral_reversepath)
next
  case False then have "\<not> f contour_integrable_on (reversepath g)"
    by (simp add: assms contour_integrable_reversepath_eq)
  with False show ?thesis by (simp add: not_integrable_contour_integral)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Joining two paths together\<close>

lemma has_contour_integral_join:
  assumes "(f has_contour_integral i1) g1" "(f has_contour_integral i2) g2"
          "valid_path g1" "valid_path g2"
    shows "(f has_contour_integral (i1 + i2)) (g1 +++ g2)"
proof -
  obtain s1 s2
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
      and s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have 1: "((\<lambda>x. f (g1 x) * vector_derivative g1 (at x)) has_integral i1) {0..1}"
   and 2: "((\<lambda>x. f (g2 x) * vector_derivative g2 (at x)) has_integral i2) {0..1}"
    using assms
    by (auto simp: has_contour_integral)
  have i1: "((\<lambda>x. (2*f (g1 (2*x))) * vector_derivative g1 (at (2*x))) has_integral i1) {0..1/2}"
   and i2: "((\<lambda>x. (2*f (g2 (2*x - 1))) * vector_derivative g2 (at (2*x - 1))) has_integral i2) {1/2..1}"
    using has_integral_affinity01 [OF 1, where m= 2 and c=0, THEN has_integral_cmul [where c=2]]
          has_integral_affinity01 [OF 2, where m= 2 and c="-1", THEN has_integral_cmul [where c=2]]
    by (simp_all only: image_affinity_atLeastAtMost_div_diff, simp_all add: scaleR_conv_of_real mult_ac)
  have g1: "vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z) =
            2 *\<^sub>R vector_derivative g1 (at (z*2))" 
      if "0 \<le> z" "z*2 < 1" "z*2 \<notin> s1" for z
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    show "0 < \<bar>z - 1/2\<bar>"
      using that by auto
    have "((*) 2 has_vector_derivative 2) (at z)" 
      by (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    moreover have "(g1 has_vector_derivative vector_derivative g1 (at (z * 2))) (at (2 * z))"
      using s1 that by (auto simp: algebra_simps vector_derivative_works)
    ultimately
    show "((\<lambda>x. g1 (2 * x)) has_vector_derivative 2 *\<^sub>R vector_derivative g1 (at (z * 2))) (at z)"
      by (intro vector_diff_chain_at [simplified o_def])
  qed (use that in \<open>simp_all add: dist_real_def abs_if split: if_split_asm\<close>)

  have g2: "vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z) =
            2 *\<^sub>R vector_derivative g2 (at (z*2 - 1))" 
           if "1 < z*2" "z \<le> 1" "z*2 - 1 \<notin> s2" for z
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    show "0 < \<bar>z - 1/2\<bar>"
      using that by auto
    have "((\<lambda>x. 2 * x - 1) has_vector_derivative 2) (at z)"
      by (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    moreover have "(g2 has_vector_derivative vector_derivative g2 (at (z * 2 - 1))) (at (2 * z - 1))"
      using s2 that by (auto simp: algebra_simps vector_derivative_works)
    ultimately
    show "((\<lambda>x. g2 (2 * x - 1)) has_vector_derivative 2 *\<^sub>R vector_derivative g2 (at (z * 2 - 1))) (at z)"
      by (intro vector_diff_chain_at [simplified o_def])
  qed (use that in \<open>simp_all add: dist_real_def abs_if split: if_split_asm\<close>)

  have "((\<lambda>x. f ((g1 +++ g2) x) * vector_derivative (g1 +++ g2) (at x)) has_integral i1) {0..1/2}"
  proof (rule has_integral_spike_finite [OF _ _ i1])
    show "finite (insert (1/2) ((*) 2 -` s1))"
      using s1 by (force intro: finite_vimageI [where h = "(*)2"] inj_onI)
  qed (auto simp add: joinpaths_def scaleR_conv_of_real mult_ac g1)
  moreover have "((\<lambda>x. f ((g1 +++ g2) x) * vector_derivative (g1 +++ g2) (at x)) has_integral i2) {1/2..1}"
  proof (rule has_integral_spike_finite [OF _ _ i2])
    show "finite (insert (1/2) ((\<lambda>x. 2 * x - 1) -` s2))"
      using s2 by (force intro: finite_vimageI [where h = "\<lambda>x. 2*x-1"] inj_onI)
  qed (auto simp add: joinpaths_def scaleR_conv_of_real mult_ac g2)
  ultimately
  show ?thesis
    by (simp add: has_contour_integral has_integral_combine [where c = "1/2"])
qed

lemma contour_integrable_joinI:
  assumes "f contour_integrable_on g1" "f contour_integrable_on g2"
          "valid_path g1" "valid_path g2"
    shows "f contour_integrable_on (g1 +++ g2)"
  using assms
  by (meson has_contour_integral_join contour_integrable_on_def)

lemma contour_integrable_joinD1:
  assumes "f contour_integrable_on (g1 +++ g2)" "valid_path g1"
    shows "f contour_integrable_on g1"
proof -
  obtain s1
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2)) * vector_derivative (g1 +++ g2) (at (x/2))) integrable_on {0..1}"
    using assms integrable_affinity [of _ 0 "1/2" "1/2" 0] integrable_on_subcbox [where a=0 and b="1/2"]
    by (fastforce simp: contour_integrable_on)
  then have *: "(\<lambda>x. (f ((g1 +++ g2) (x/2))/2) * vector_derivative (g1 +++ g2) (at (x/2))) integrable_on {0..1}"
    by (auto dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g1: "vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at (z/2)) =
            2 *\<^sub>R vector_derivative g1 (at z)" 
    if "0 < z" "z < 1" "z \<notin> s1" for z
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    show "0 < \<bar>(z - 1)/2\<bar>"
      using that by auto
    have \<section>: "((\<lambda>x. x * 2) has_vector_derivative 2) (at (z/2))"
      using s1 by (auto simp: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    have "(g1 has_vector_derivative vector_derivative g1 (at z)) (at z)"
      using s1 that by (auto simp: vector_derivative_works)
    then show "((\<lambda>x. g1 (2 * x)) has_vector_derivative 2 *\<^sub>R vector_derivative g1 (at z)) (at (z/2))"
      using vector_diff_chain_at [OF \<section>] by (auto simp: field_simps o_def)
  qed (use that in \<open>simp_all add: field_simps dist_real_def abs_if split: if_split_asm\<close>)
  have fin01: "finite ({0, 1} \<union> s1)"
    by (simp add: s1)
  show ?thesis
    unfolding contour_integrable_on
    by (intro integrable_spike_finite [OF fin01 _ *]) (auto simp: joinpaths_def scaleR_conv_of_real g1)
qed

lemma contour_integrable_joinD2:
  assumes "f contour_integrable_on (g1 +++ g2)" "valid_path g2"
    shows "f contour_integrable_on g2"
proof -
  obtain s2
    where s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2 + 1/2)) * vector_derivative (g1 +++ g2) (at (x/2 + 1/2))) integrable_on {0..1}"
    using assms integrable_affinity [of _ "1/2::real" 1 "1/2" "1/2"] 
                integrable_on_subcbox [where a="1/2" and b=1]
    by (fastforce simp: contour_integrable_on image_affinity_atLeastAtMost_diff)
  then have *: "(\<lambda>x. (f ((g1 +++ g2) (x/2 + 1/2))/2) * vector_derivative (g1 +++ g2) (at (x/2 + 1/2)))
                integrable_on {0..1}"
    by (auto dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g2: "vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at (z/2+1/2)) =
            2 *\<^sub>R vector_derivative g2 (at z)" 
        if "0 < z" "z < 1" "z \<notin> s2" for z
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    show "0 < \<bar>z/2\<bar>"
      using that by auto
    have \<section>: "((\<lambda>x. x * 2 - 1) has_vector_derivative 2) (at ((1 + z)/2))"
      using s2 by (auto simp: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    have "(g2 has_vector_derivative vector_derivative g2 (at z)) (at z)"
      using s2 that by (auto simp: vector_derivative_works)
    then show "((\<lambda>x. g2 (2*x - 1)) has_vector_derivative 2 *\<^sub>R vector_derivative g2 (at z)) (at (z/2 + 1/2))"
      using vector_diff_chain_at [OF \<section>] by (auto simp: field_simps o_def)
  qed (use that in \<open>simp_all add: field_simps dist_real_def abs_if split: if_split_asm\<close>)
  have fin01: "finite ({0, 1} \<union> s2)"
    by (simp add: s2)
  show ?thesis
    unfolding contour_integrable_on
    by (intro integrable_spike_finite [OF fin01 _ *]) (auto simp: joinpaths_def scaleR_conv_of_real g2)
qed

lemma contour_integrable_join [simp]:
    "\<lbrakk>valid_path g1; valid_path g2\<rbrakk>
     \<Longrightarrow> f contour_integrable_on (g1 +++ g2) \<longleftrightarrow> f contour_integrable_on g1 \<and> f contour_integrable_on g2"
using contour_integrable_joinD1 contour_integrable_joinD2 contour_integrable_joinI by blast

lemma contour_integral_join [simp]:
    "\<lbrakk>f contour_integrable_on g1; f contour_integrable_on g2; valid_path g1; valid_path g2\<rbrakk>
        \<Longrightarrow> contour_integral (g1 +++ g2) f = contour_integral g1 f + contour_integral g2 f"
  by (simp add: has_contour_integral_integral has_contour_integral_join contour_integral_unique)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Shifting the starting point of a (closed) path\<close>

lemma has_contour_integral_shiftpath:
  assumes f: "(f has_contour_integral i) g" "valid_path g"
      and a: "a \<in> {0..1}"
    shows "(f has_contour_integral i) (shiftpath a g)"
proof -
  obtain S
    where S: "finite S" and g: "\<forall>x\<in>{0..1} - S. g differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have *: "((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
    using assms by (auto simp: has_contour_integral)
  then have i: "i = integral {a..1} (\<lambda>x. f (g x) * vector_derivative g (at x)) +
                    integral {0..a} (\<lambda>x. f (g x) * vector_derivative g (at x))"
    apply (rule has_integral_unique)
    apply (subst add.commute)
    apply (subst Henstock_Kurzweil_Integration.integral_combine)
    using assms * integral_unique by auto

  have vd1: "vector_derivative (shiftpath a g) (at x) = vector_derivative g (at (x + a))"
    if "0 \<le> x" "x + a < 1" "x \<notin> (\<lambda>x. x - a) ` S" for x
    unfolding shiftpath_def
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    have "((\<lambda>x. g (x + a)) has_vector_derivative vector_derivative g (at (a + x))) (at x)"
    proof (rule vector_diff_chain_at [of _ 1, simplified o_def scaleR_one])
      show "((\<lambda>x. x + a) has_vector_derivative 1) (at x)"
        by (rule derivative_eq_intros | simp)+
      have "g differentiable at (x + a)"
        using g a that by force
      then show "(g has_vector_derivative vector_derivative g (at (a + x))) (at (x + a))"
        by (metis add.commute vector_derivative_works)
    qed
    then
    show "((\<lambda>x. g (a + x)) has_vector_derivative vector_derivative g (at (x + a))) (at x)"
      by (auto simp: field_simps)
    show "0 < dist (1 - a) x"
      using that by auto
  qed (use that in \<open>auto simp: dist_real_def\<close>)

  have vd2: "vector_derivative (shiftpath a g) (at x) = vector_derivative g (at (x + a - 1))"
    if "x \<le> 1" "1 < x + a" "x \<notin> (\<lambda>x. x - a + 1) ` S" for x
    unfolding shiftpath_def
  proof (rule vector_derivative_at [OF has_vector_derivative_transform_within])
    have "((\<lambda>x. g (x + a - 1)) has_vector_derivative vector_derivative g (at (a+x-1))) (at x)"
    proof (rule vector_diff_chain_at [of _ 1, simplified o_def scaleR_one])
      show "((\<lambda>x. x + a - 1) has_vector_derivative 1) (at x)"
        by (rule derivative_eq_intros | simp)+
      have "g differentiable at (x+a-1)"
        using g a that by force
      then show "(g has_vector_derivative vector_derivative g (at (a+x-1))) (at (x + a - 1))"
        by (metis add.commute vector_derivative_works)
    qed
    then show "((\<lambda>x. g (a + x - 1)) has_vector_derivative vector_derivative g (at (x + a - 1))) (at x)"
      by (auto simp: field_simps)
    show "0 < dist (1 - a) x"
      using that by auto
  qed (use that in \<open>auto simp: dist_real_def\<close>)

  have va1: "(\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on ({a..1})"
    using * a   by (fastforce intro: integrable_subinterval_real)
  have v0a: "(\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on ({0..a})"
    using * a by (force intro: integrable_subinterval_real)
  have "finite ({1 - a} \<union> (\<lambda>x. x - a) ` S)"
    using S by blast
  then have "((\<lambda>x. f (shiftpath a g x) * vector_derivative (shiftpath a g) (at x))
        has_integral integral {a..1} (\<lambda>x. f (g x) * vector_derivative g (at x)))  {0..1 - a}"
    apply (rule has_integral_spike_finite
        [where f = "\<lambda>x. f(g(a+x)) * vector_derivative g (at(a+x))"])
    subgoal
      using a by (simp add: vd1) (force simp: shiftpath_def add.commute)
    subgoal
      using has_integral_affinity [where m=1 and c=a] integrable_integral [OF va1]
      by (force simp add: add.commute)
    done
  moreover
  have "finite ({1 - a} \<union> (\<lambda>x. x - a + 1) ` S)"
    using S by blast
  then have "((\<lambda>x. f (shiftpath a g x) * vector_derivative (shiftpath a g) (at x))
             has_integral  integral {0..a} (\<lambda>x. f (g x) * vector_derivative g (at x)))  {1 - a..1}"
    apply (rule has_integral_spike_finite
        [where f = "\<lambda>x. f(g(a+x-1)) * vector_derivative g (at(a+x-1))"])
    subgoal
      using a by (simp add: vd2) (force simp: shiftpath_def add.commute)
    subgoal
      using has_integral_affinity [where m=1 and c="a-1", simplified, OF integrable_integral [OF v0a]]
      by (force simp add: algebra_simps)
    done
  ultimately show ?thesis
    using a
    by (auto simp: i has_contour_integral intro: has_integral_combine [where c = "1-a"])
qed

lemma has_contour_integral_shiftpath_D:
  assumes "(f has_contour_integral i) (shiftpath a g)"
          "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_contour_integral i) g"
proof -
  obtain S
    where S: "finite S" and g: "\<forall>x\<in>{0..1} - S. g differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  { fix x
    assume x: "0 < x" "x < 1" "x \<notin> S"
    then have gx: "g differentiable at x"
      using g by auto
    have \<section>: "shiftpath (1 - a) (shiftpath a g) differentiable at x"
      using assms x
      by (intro differentiable_transform_within [OF gx, of "min x (1-x)"])
         (auto simp: dist_real_def shiftpath_shiftpath abs_if split: if_split_asm)
    have "vector_derivative g (at x within {0..1}) =
          vector_derivative (shiftpath (1 - a) (shiftpath a g)) (at x within {0..1})"
      apply (rule vector_derivative_at_within_ivl
                  [OF has_vector_derivative_transform_within_open
                      [where f = "(shiftpath (1 - a) (shiftpath a g))" and S = "{0<..<1}-S"]])
      using S assms x \<section>
      apply (auto simp: finite_imp_closed open_Diff shiftpath_shiftpath
                        at_within_interior [of _ "{0..1}"] vector_derivative_works [symmetric])
      done
  } note vd = this
  have fi: "(f has_contour_integral i) (shiftpath (1 - a) (shiftpath a g))"
    using assms  by (auto intro!: has_contour_integral_shiftpath)
  show ?thesis
    unfolding has_contour_integral_def
  proof (rule has_integral_spike_finite [of "{0,1} \<union> S", OF _ _  fi [unfolded has_contour_integral_def]])
    show "finite ({0, 1} \<union> S)"
      by (simp add: S)
  qed (use S assms vd in \<open>auto simp: shiftpath_shiftpath\<close>)
qed

lemma has_contour_integral_shiftpath_eq:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_contour_integral i) (shiftpath a g) \<longleftrightarrow> (f has_contour_integral i) g"
  using assms has_contour_integral_shiftpath has_contour_integral_shiftpath_D by blast

lemma contour_integrable_on_shiftpath_eq:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "f contour_integrable_on (shiftpath a g) \<longleftrightarrow> f contour_integrable_on g"
using assms contour_integrable_on_def has_contour_integral_shiftpath_eq by auto

lemma contour_integral_shiftpath:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "contour_integral (shiftpath a g) f = contour_integral g f"
   using assms
   by (simp add: contour_integral_def contour_integrable_on_def has_contour_integral_shiftpath_eq)


subsection\<^marker>\<open>tag unimportant\<close> \<open>More about straight-line paths\<close>

lemma has_contour_integral_linepath:
  shows "(f has_contour_integral i) (linepath a b) \<longleftrightarrow>
         ((\<lambda>x. f(linepath a b x) * (b - a)) has_integral i) {0..1}"
  by (simp add: has_contour_integral)

lemma has_contour_integral_trivial [iff]: "(f has_contour_integral 0) (linepath a a)"
  by (simp add: has_contour_integral_linepath)

lemma has_contour_integral_trivial_iff [simp]: "(f has_contour_integral i) (linepath a a) \<longleftrightarrow> i=0"
  using has_contour_integral_unique by blast

lemma contour_integral_trivial [simp]: "contour_integral (linepath a a) f = 0"
  using has_contour_integral_trivial contour_integral_unique by blast


subsection\<open>Relation to subpath construction\<close>

lemma has_contour_integral_subpath_refl [iff]: "(f has_contour_integral 0) (subpath u u g)"
  by (simp add: has_contour_integral subpath_def)

lemma contour_integrable_subpath_refl [iff]: "f contour_integrable_on (subpath u u g)"
  using has_contour_integral_subpath_refl contour_integrable_on_def by blast

lemma contour_integral_subpath_refl [simp]: "contour_integral (subpath u u g) f = 0"
  by (simp add: contour_integral_unique)

lemma has_contour_integral_subpath:
  assumes f: "f contour_integrable_on g" and g: "valid_path g"
      and uv: "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(f has_contour_integral  integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x)))
           (subpath u v g)"
proof (cases "v=u")
  case True
  then show ?thesis
    using f   by (simp add: contour_integrable_on_def subpath_def has_contour_integral)
next
  case False
  obtain S where S: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g differentiable at x" and fs: "finite S"
    using g unfolding piecewise_C1_differentiable_on_def C1_differentiable_on_eq valid_path_def by blast
  have \<section>: "(\<lambda>t. f (g t) * vector_derivative g (at t)) integrable_on {u..v}"
    using contour_integrable_on f integrable_on_subinterval uv by fastforce
  then have *: "((\<lambda>x. f (g ((v - u) * x + u)) * vector_derivative g (at ((v - u) * x + u)))
            has_integral (1 / (v - u)) * integral {u..v} (\<lambda>t. f (g t) * vector_derivative g (at t)))
           {0..1}"
    using uv False unfolding has_integral_integral
    apply simp
    apply (drule has_integral_affinity [where m="v-u" and c=u, simplified])
    apply (simp_all add: image_affinity_atLeastAtMost_div_diff scaleR_conv_of_real)
    apply (simp add: divide_simps)
    done

  have vd: "vector_derivative (\<lambda>x. g ((v-u) * x + u)) (at x) = (v-u) *\<^sub>R vector_derivative g (at ((v-u) * x + u))"
    if "x \<in> {0..1}"  "x \<notin> (\<lambda>t. (v-u) *\<^sub>R t + u) -` S" for x
  proof (rule vector_derivative_at [OF vector_diff_chain_at [simplified o_def]])
    show "((\<lambda>x. (v - u) * x + u) has_vector_derivative v - u) (at x)"
      by (intro derivative_eq_intros | simp)+
  qed (use S uv mult_left_le [of x "v-u"] that in \<open>auto simp: vector_derivative_works\<close>)

  have fin: "finite ((\<lambda>t. (v - u) *\<^sub>R t + u) -` S)"
    using fs by (auto simp: inj_on_def False finite_vimageI)
  show ?thesis
    unfolding subpath_def has_contour_integral
    apply (rule has_integral_spike_finite [OF fin])
    using has_integral_cmul [OF *, where c = "v-u"] fs assms
    by (auto simp: False vd scaleR_conv_of_real)
qed

lemma contour_integrable_subpath:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "f contour_integrable_on (subpath u v g)"
proof (cases u v rule: linorder_class.le_cases)
  case le
  then show ?thesis
    by (metis contour_integrable_on_def has_contour_integral_subpath [OF assms])
next
  case ge
  with assms show ?thesis
    by (metis (no_types, lifting) contour_integrable_on_def contour_integrable_reversepath_eq has_contour_integral_subpath reversepath_subpath valid_path_subpath)
qed

lemma has_integral_contour_integral_subpath:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(((\<lambda>x. f(g x) * vector_derivative g (at x)))
            has_integral  contour_integral (subpath u v g) f) {u..v}"
  using assms
proof -
  have "(\<lambda>r. f (g r) * vector_derivative g (at r)) integrable_on {u..v}"
    by (metis (full_types) assms(1) assms(3) assms(4) atLeastAtMost_iff atLeastatMost_subset_iff contour_integrable_on integrable_on_subinterval)
  then have "((\<lambda>r. f (g r) * vector_derivative g (at r)) has_integral integral {u..v} (\<lambda>r. f (g r) * vector_derivative g (at r))) {u..v}"
    by blast
  then show ?thesis
    by (metis (full_types) assms contour_integral_unique has_contour_integral_subpath)
qed

lemma contour_integral_subcontour_integral:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "contour_integral (subpath u v g) f =
           integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x))"
  using assms has_contour_integral_subpath contour_integral_unique by blast

lemma contour_integral_subpath_combine_less:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
          "u<v" "v<w"
    shows "contour_integral (subpath u v g) f + contour_integral (subpath v w g) f =
           contour_integral (subpath u w g) f"
proof -
  have "(\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on {u..w}"
    using integrable_on_subcbox [where a=u and b=w and S = "{0..1}"] assms
    by (auto simp: contour_integrable_on)
  with assms show ?thesis
    by (auto simp: contour_integral_subcontour_integral Henstock_Kurzweil_Integration.integral_combine)
qed

lemma contour_integral_subpath_combine:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
    shows "contour_integral (subpath u v g) f + contour_integral (subpath v w g) f =
           contour_integral (subpath u w g) f"
proof (cases "u\<noteq>v \<and> v\<noteq>w \<and> u\<noteq>w")
  case True
    have *: "subpath v u g = reversepath(subpath u v g) \<and>
             subpath w u g = reversepath(subpath u w g) \<and>
             subpath w v g = reversepath(subpath v w g)"
      by (auto simp: reversepath_subpath)
    have "u < v \<and> v < w \<or>
          u < w \<and> w < v \<or>
          v < u \<and> u < w \<or>
          v < w \<and> w < u \<or>
          w < u \<and> u < v \<or>
          w < v \<and> v < u"
      using True assms by linarith
    with assms show ?thesis
      using contour_integral_subpath_combine_less [of f g u v w]
            contour_integral_subpath_combine_less [of f g u w v]
            contour_integral_subpath_combine_less [of f g v u w]
            contour_integral_subpath_combine_less [of f g v w u]
            contour_integral_subpath_combine_less [of f g w u v]
            contour_integral_subpath_combine_less [of f g w v u]
      by (elim disjE) (auto simp: * contour_integral_reversepath contour_integrable_subpath
                                    valid_path_subpath algebra_simps)
next
  case False
  with assms show ?thesis
    by (metis add.right_neutral contour_integral_reversepath contour_integral_subpath_refl diff_0 eq_diff_eq add_0 reversepath_subpath valid_path_subpath)
qed

lemma contour_integral_integral:
     "contour_integral g f = integral {0..1} (\<lambda>x. f (g x) * vector_derivative g (at x))"
  by (simp add: contour_integral_def integral_def has_contour_integral contour_integrable_on)

lemma contour_integral_cong:
  assumes "g = g'" "\<And>x. x \<in> path_image g \<Longrightarrow> f x = f' x"
  shows   "contour_integral g f = contour_integral g' f'"
  unfolding contour_integral_integral using assms
  by (intro integral_cong) (auto simp: path_image_def)


text \<open>Contour integral along a segment on the real axis\<close>

lemma has_contour_integral_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f has_contour_integral I) (linepath a b) \<longleftrightarrow>
             ((\<lambda>x. f (of_real x)) has_integral I) {Re a..Re b}"
proof -
  from assms have [simp]: "of_real (Re a) = a" "of_real (Re b) = b"
    by (simp_all add: complex_eq_iff)
  from assms have "a \<noteq> b" by auto
  have "((\<lambda>x. f (of_real x)) has_integral I) (cbox (Re a) (Re b)) \<longleftrightarrow>
          ((\<lambda>x. f (a + b * of_real x - a * of_real x)) has_integral I /\<^sub>R (Re b - Re a)) {0..1}"
    by (subst has_integral_affinity_iff [of "Re b - Re a" _ "Re a", symmetric])
       (insert assms, simp_all add: field_simps scaleR_conv_of_real)
  also have "(\<lambda>x. f (a + b * of_real x - a * of_real x)) =
               (\<lambda>x. (f (a + b * of_real x - a * of_real x) * (b - a)) /\<^sub>R (Re b - Re a))"
    using \<open>a \<noteq> b\<close> by (auto simp: field_simps fun_eq_iff scaleR_conv_of_real)
  also have "(\<dots> has_integral I /\<^sub>R (Re b - Re a)) {0..1} \<longleftrightarrow> 
               ((\<lambda>x. f (linepath a b x) * (b - a)) has_integral I) {0..1}" using assms
    by (subst has_integral_cmul_iff) (auto simp: linepath_def scaleR_conv_of_real algebra_simps)
  also have "\<dots> \<longleftrightarrow> (f has_contour_integral I) (linepath a b)" unfolding has_contour_integral_def
    by (intro has_integral_cong) (simp add: vector_derivative_linepath_within)
  finally show ?thesis by simp
qed

lemma contour_integrable_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f contour_integrable_on linepath a b) \<longleftrightarrow>
             (\<lambda>x. f (of_real x)) integrable_on {Re a..Re b}"
  using has_contour_integral_linepath_Reals_iff[OF assms, of f]
  by (auto simp: contour_integrable_on_def integrable_on_def)

lemma contour_integral_linepath_Reals_eq:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "contour_integral (linepath a b) f = integral {Re a..Re b} (\<lambda>x. f (of_real x))"
proof (cases "f contour_integrable_on linepath a b")
  case True
  thus ?thesis using has_contour_integral_linepath_Reals_iff[OF assms, of f]
    using has_contour_integral_integral has_contour_integral_unique by blast
next
  case False
  thus ?thesis using contour_integrable_linepath_Reals_iff[OF assms, of f]
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed

subsection \<open>Cauchy's theorem where there's a primitive\<close>

lemma contour_integral_primitive_lemma:
  fixes f :: "complex \<Rightarrow> complex" and g :: "real \<Rightarrow> complex"
  assumes "a \<le> b"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_field_derivative f' x) (at x within S)"
      and "g piecewise_differentiable_on {a..b}"  "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> S"
    shows "((\<lambda>x. f'(g x) * vector_derivative g (at x within {a..b}))
             has_integral (f(g b) - f(g a))) {a..b}"
proof -
  obtain K where "finite K" and K: "\<forall>x\<in>{a..b} - K. g differentiable (at x within {a..b})" and cg: "continuous_on {a..b} g"
    using assms by (auto simp: piecewise_differentiable_on_def)
  have "continuous_on (g ` {a..b}) f"
    using assms
    by (metis field_differentiable_def field_differentiable_imp_continuous_at continuous_on_eq_continuous_within continuous_on_subset image_subset_iff)
  then have cfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    by (rule continuous_on_compose [OF cg, unfolded o_def])
  { fix x::real
    assume a: "a < x" and b: "x < b" and xk: "x \<notin> K"
    then have "g differentiable at x within {a..b}"
      using K by (simp add: differentiable_at_withinI)
    then have "(g has_vector_derivative vector_derivative g (at x within {a..b})) (at x within {a..b})"
      by (simp add: vector_derivative_works has_field_derivative_def scaleR_conv_of_real)
    then have gdiff: "(g has_derivative (\<lambda>u. u * vector_derivative g (at x within {a..b}))) (at x within {a..b})"
      by (simp add: has_vector_derivative_def scaleR_conv_of_real)
    have "(f has_field_derivative (f' (g x))) (at (g x) within g ` {a..b})"
      using assms by (metis a atLeastAtMost_iff b DERIV_subset image_subset_iff less_eq_real_def)
    then have fdiff: "(f has_derivative (*) (f' (g x))) (at (g x) within g ` {a..b})"
      by (simp add: has_field_derivative_def)
    have "((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {a..b})) (at x within {a..b})"
      using diff_chain_within [OF gdiff fdiff]
      by (simp add: has_vector_derivative_def scaleR_conv_of_real o_def mult_ac)
  } note * = this
  show ?thesis
    using assms cfg *
    by (force simp: at_within_Icc_at intro: fundamental_theorem_of_calculus_interior_strong [OF \<open>finite K\<close>])
qed

lemma contour_integral_primitive:
  assumes "\<And>x. x \<in> S \<Longrightarrow> (f has_field_derivative f' x) (at x within S)"
      and "valid_path g" "path_image g \<subseteq> S"
    shows "(f' has_contour_integral (f(pathfinish g) - f(pathstart g))) g"
  using assms
  apply (simp add: valid_path_def path_image_def pathfinish_def pathstart_def has_contour_integral_def)
  apply (auto intro!: piecewise_C1_imp_differentiable contour_integral_primitive_lemma [of 0 1 S])
  done

corollary Cauchy_theorem_primitive:
  assumes "\<And>x. x \<in> S \<Longrightarrow> (f has_field_derivative f' x) (at x within S)"
      and "valid_path g"  "path_image g \<subseteq> S" "pathfinish g = pathstart g"
    shows "(f' has_contour_integral 0) g"
  using assms by (metis diff_self contour_integral_primitive)

text\<open>Existence of path integral for continuous function\<close>
lemma contour_integrable_continuous_linepath:
  assumes "continuous_on (closed_segment a b) f"
  shows "f contour_integrable_on (linepath a b)"
proof -
  have "continuous_on (closed_segment a b) (\<lambda>x. f x * (b - a))"
    by (rule continuous_intros | simp add: assms)+
  then have "continuous_on {0..1} (\<lambda>x. f (linepath a b x) * (b - a))"
    by (metis (no_types, lifting) continuous_on_compose continuous_on_cong continuous_on_linepath linepath_image_01 o_apply)
  then have "(\<lambda>x. f (linepath a b x) *
         vector_derivative (linepath a b)
          (at x within {0..1})) integrable_on
    {0..1}"
    by (metis (no_types, lifting) continuous_on_cong integrable_continuous_real vector_derivative_linepath_within)
  then show ?thesis
    by (simp add: contour_integrable_on_def has_contour_integral_def integrable_on_def [symmetric])
qed

lemma has_field_der_id: "((\<lambda>x. x\<^sup>2/2) has_field_derivative x) (at x)"
  by (rule has_derivative_imp_has_field_derivative)
     (rule derivative_intros | simp)+

lemma contour_integral_id [simp]: "contour_integral (linepath a b) (\<lambda>y. y) = (b^2 - a^2)/2"
  using contour_integral_primitive [of UNIV "\<lambda>x. x^2/2" "\<lambda>x. x" "linepath a b"] contour_integral_unique
  by (simp add: has_field_der_id)

lemma contour_integrable_on_const [iff]: "(\<lambda>x. c) contour_integrable_on (linepath a b)"
  by (simp add: contour_integrable_continuous_linepath)

lemma contour_integrable_on_id [iff]: "(\<lambda>x. x) contour_integrable_on (linepath a b)"
  by (simp add: contour_integrable_continuous_linepath)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetical combining theorems\<close>

lemma has_contour_integral_neg:
    "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. -(f x)) has_contour_integral (-i)) g"
  by (simp add: has_integral_neg has_contour_integral_def)

lemma has_contour_integral_add:
    "\<lbrakk>(f1 has_contour_integral i1) g; (f2 has_contour_integral i2) g\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. f1 x + f2 x) has_contour_integral (i1 + i2)) g"
  by (simp add: has_integral_add has_contour_integral_def algebra_simps)

lemma has_contour_integral_diff:
  "\<lbrakk>(f1 has_contour_integral i1) g; (f2 has_contour_integral i2) g\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) has_contour_integral (i1 - i2)) g"
  by (simp add: has_integral_diff has_contour_integral_def algebra_simps)

lemma has_contour_integral_lmul:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. c * (f x)) has_contour_integral (c*i)) g"
  by (simp add: has_contour_integral_def algebra_simps has_integral_mult_right)

lemma has_contour_integral_rmul:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. (f x) * c) has_contour_integral (i*c)) g"
  by (simp add: mult.commute has_contour_integral_lmul)

lemma has_contour_integral_div:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. f x/c) has_contour_integral (i/c)) g"
  by (simp add: field_class.field_divide_inverse) (metis has_contour_integral_rmul)

lemma has_contour_integral_eq:
    "\<lbrakk>(f has_contour_integral y) p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> (g has_contour_integral y) p"
  by (metis (mono_tags, lifting) has_contour_integral_def has_integral_eq image_eqI path_image_def)

lemma has_contour_integral_bound_linepath:
  assumes "(f has_contour_integral i) (linepath a b)"
          "0 \<le> B" and B: "\<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B"
    shows "norm i \<le> B * norm(b - a)"
proof -
  have "norm i \<le> (B * norm (b - a)) * content (cbox 0 (1::real))"
  proof (rule has_integral_bound
       [of _ "\<lambda>x. f (linepath a b x) * vector_derivative (linepath a b) (at x within {0..1})"])
    show  "cmod (f (linepath a b x) * vector_derivative (linepath a b) (at x within {0..1}))
         \<le> B * cmod (b - a)"
      if "x \<in> cbox 0 1" for x::real
      using that box_real(2) norm_mult
      by (metis B linepath_in_path mult_right_mono norm_ge_zero vector_derivative_linepath_within)
  qed (use assms has_contour_integral_def in auto)
  then show ?thesis
    by (auto simp: content_real)
qed

lemma has_contour_integral_const_linepath: "((\<lambda>x. c) has_contour_integral c*(b - a))(linepath a b)"
  unfolding has_contour_integral_linepath
  by (metis content_real diff_0_right has_integral_const_real lambda_one of_real_1 scaleR_conv_of_real zero_le_one)

lemma has_contour_integral_0: "((\<lambda>x. 0) has_contour_integral 0) g"
  by (simp add: has_contour_integral_def)

lemma has_contour_integral_is_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> (f has_contour_integral 0) g"
  by (rule has_contour_integral_eq [OF has_contour_integral_0]) auto

lemma has_contour_integral_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a has_contour_integral i a) p\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. sum (\<lambda>a. f a x) s) has_contour_integral sum i s) p"
  by (induction s rule: finite_induct) (auto simp: has_contour_integral_0 has_contour_integral_add)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Operations on path integrals\<close>

lemma contour_integral_const_linepath [simp]: "contour_integral (linepath a b) (\<lambda>x. c) = c*(b - a)"
  by (rule contour_integral_unique [OF has_contour_integral_const_linepath])

lemma contour_integral_neg:
    "f contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. -(f x)) = -(contour_integral g f)"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_neg)

lemma contour_integral_add:
    "f1 contour_integrable_on g \<Longrightarrow> f2 contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. f1 x + f2 x) =
                contour_integral g f1 + contour_integral g f2"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_add)

lemma contour_integral_diff:
    "f1 contour_integrable_on g \<Longrightarrow> f2 contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. f1 x - f2 x) =
                contour_integral g f1 - contour_integral g f2"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_diff)

lemma contour_integral_lmul:
  shows "f contour_integrable_on g
           \<Longrightarrow> contour_integral g (\<lambda>x. c * f x) = c*contour_integral g f"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_lmul)

lemma contour_integral_rmul:
  shows "f contour_integrable_on g
        \<Longrightarrow> contour_integral g (\<lambda>x. f x * c) = contour_integral g f * c"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_rmul)

lemma contour_integral_div:
  shows "f contour_integrable_on g
        \<Longrightarrow> contour_integral g (\<lambda>x. f x / c) = contour_integral g f / c"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_div)

lemma contour_integral_eq:
    "(\<And>x. x \<in> path_image p \<Longrightarrow> f x = g x) \<Longrightarrow> contour_integral p f = contour_integral p g"
  using contour_integral_cong contour_integral_def by fastforce

lemma contour_integral_eq_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> contour_integral g f = 0"
  by (simp add: has_contour_integral_is_0 contour_integral_unique)

lemma contour_integral_bound_linepath:
  shows
    "\<lbrakk>f contour_integrable_on (linepath a b);
      0 \<le> B; \<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
     \<Longrightarrow> norm(contour_integral (linepath a b) f) \<le> B*norm(b - a)"
  using has_contour_integral_bound_linepath [of f]
  by (auto simp: has_contour_integral_integral)

lemma contour_integral_0 [simp]: "contour_integral g (\<lambda>x. 0) = 0"
  by (simp add: contour_integral_unique has_contour_integral_0)

lemma contour_integral_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> contour_integral p (\<lambda>x. sum (\<lambda>a. f a x) s) = sum (\<lambda>a. contour_integral p (f a)) s"
  by (auto simp: contour_integral_unique has_contour_integral_sum has_contour_integral_integral)

lemma contour_integrable_eq:
    "\<lbrakk>f contour_integrable_on p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g contour_integrable_on p"
  unfolding contour_integrable_on_def
  by (metis has_contour_integral_eq)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetic theorems for path integrability\<close>

lemma contour_integrable_neg:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. -(f x)) contour_integrable_on g"
  using has_contour_integral_neg contour_integrable_on_def by blast

lemma contour_integrable_add:
    "\<lbrakk>f1 contour_integrable_on g; f2 contour_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x + f2 x) contour_integrable_on g"
  using has_contour_integral_add contour_integrable_on_def
  by fastforce

lemma contour_integrable_diff:
    "\<lbrakk>f1 contour_integrable_on g; f2 contour_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x - f2 x) contour_integrable_on g"
  using has_contour_integral_diff contour_integrable_on_def
  by fastforce

lemma contour_integrable_lmul:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. c * f x) contour_integrable_on g"
  using has_contour_integral_lmul contour_integrable_on_def
  by fastforce

lemma contour_integrable_rmul:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. f x * c) contour_integrable_on g"
  using has_contour_integral_rmul contour_integrable_on_def
  by fastforce

lemma contour_integrable_div:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. f x / c) contour_integrable_on g"
  using has_contour_integral_div contour_integrable_on_def
  by fastforce

lemma contour_integrable_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> (\<lambda>x. sum (\<lambda>a. f a x) s) contour_integrable_on p"
   unfolding contour_integrable_on_def
   by (metis has_contour_integral_sum)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Reversing a path integral\<close>

lemma has_contour_integral_reverse_linepath:
    "(f has_contour_integral i) (linepath a b)
     \<Longrightarrow> (f has_contour_integral (-i)) (linepath b a)"
  using has_contour_integral_reversepath valid_path_linepath by fastforce

lemma contour_integral_reverse_linepath:
    "continuous_on (closed_segment a b) f
     \<Longrightarrow> contour_integral (linepath a b) f = - (contour_integral(linepath b a) f)"
  by (metis contour_integrable_continuous_linepath contour_integral_unique has_contour_integral_integral has_contour_integral_reverse_linepath)


text \<open>Splitting a path integral in a flat way.*)\<close>

lemma has_contour_integral_split:
  assumes f: "(f has_contour_integral i) (linepath a c)" "(f has_contour_integral j) (linepath c b)"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "(f has_contour_integral (i + j)) (linepath a b)"
proof (cases "k = 0 \<or> k = 1")
  case True
  then show ?thesis
    using assms by auto
next
  case False
  then have k: "0 < k" "k < 1" "complex_of_real k \<noteq> 1"
    using assms by auto
  have c': "c = k *\<^sub>R (b - a) + a"
    by (metis diff_add_cancel c)
  have bc: "(b - c) = (1 - k) *\<^sub>R (b - a)"
    by (simp add: algebra_simps c')
  { assume *: "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R c) * (c - a)) has_integral i) {0..1}"
    have "\<And>x. (x / k) *\<^sub>R a + ((k - x) / k) *\<^sub>R a = a"
      using False by (simp add: field_split_simps flip: real_vector.scale_left_distrib)
    then have "\<And>x. ((k - x) / k) *\<^sub>R a + (x / k) *\<^sub>R c = (1 - x) *\<^sub>R a + x *\<^sub>R b"
      using False by (simp add: c' algebra_simps)
    then have "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R b) * (b - a)) has_integral i) {0..k}"
      using k has_integral_affinity01 [OF *, of "inverse k" "0"] 
      by (force dest: has_integral_cmul [where c = "inverse k"] 
              simp add: divide_simps mult.commute [of _ "k"] image_affinity_atLeastAtMost c)
  } note fi = this
  { assume *: "((\<lambda>x. f ((1 - x) *\<^sub>R c + x *\<^sub>R b) * (b - c)) has_integral j) {0..1}"
    have **: "\<And>x. (((1 - x) / (1 - k)) *\<^sub>R c + ((x - k) / (1 - k)) *\<^sub>R b) = ((1 - x) *\<^sub>R a + x *\<^sub>R b)"
      using k unfolding c' scaleR_conv_of_real
      apply (simp add: divide_simps)
      apply (simp add: distrib_right distrib_left right_diff_distrib left_diff_distrib)
      done
    have "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R b) * (b - a)) has_integral j) {k..1}"
      using k has_integral_affinity01 [OF *, of "inverse(1 - k)" "-(k/(1 - k))"]
      apply (simp add: divide_simps mult.commute [of _ "1-k"] image_affinity_atLeastAtMost ** bc)
      apply (auto dest: has_integral_cmul [where k = "(1 - k) *\<^sub>R j" and c = "inverse (1 - k)"])
      done
  } note fj = this
  show ?thesis
    using f k unfolding has_contour_integral_linepath
    by (simp add: linepath_def has_integral_combine [OF _ _ fi fj])
qed

lemma continuous_on_closed_segment_transform:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "continuous_on (closed_segment a c) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have "closed_segment a c \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(1) in_segment(1) k subset_closed_segment)
  then show "continuous_on (closed_segment a c) f"
    by (rule continuous_on_subset [OF f])
qed

lemma contour_integral_split:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have "closed_segment a c \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(1) in_segment(1) k subset_closed_segment)
  moreover have "closed_segment c b \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(2) in_segment(1) k subset_closed_segment)
  ultimately
  have *: "continuous_on (closed_segment a c) f" "continuous_on (closed_segment c b) f"
    by (auto intro: continuous_on_subset [OF f])
  show ?thesis
    by (rule contour_integral_unique) (meson "*" c contour_integrable_continuous_linepath has_contour_integral_integral has_contour_integral_split k)
qed

lemma contour_integral_split_linepath:
  assumes f: "continuous_on (closed_segment a b) f"
      and c: "c \<in> closed_segment a b"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
  using c by (auto simp: closed_segment_def algebra_simps intro!: contour_integral_split [OF f])


subsection\<open>Reversing the order in a double path integral\<close>

text\<open>The condition is stronger than needed but it's often true in typical situations\<close>

lemma fst_im_cbox [simp]: "cbox c d \<noteq> {} \<Longrightarrow> (fst ` cbox (a,c) (b,d)) = cbox a b"
  by (auto simp: cbox_Pair_eq)

lemma snd_im_cbox [simp]: "cbox a b \<noteq> {} \<Longrightarrow> (snd ` cbox (a,c) (b,d)) = cbox c d"
  by (auto simp: cbox_Pair_eq)

proposition contour_integral_swap:
  assumes fcon:  "continuous_on (path_image g \<times> path_image h) (\<lambda>(y1,y2). f y1 y2)"
      and vp:    "valid_path g" "valid_path h"
      and gvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative g (at t))"
      and hvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative h (at t))"
  shows "contour_integral g (\<lambda>w. contour_integral h (f w)) =
         contour_integral h (\<lambda>z. contour_integral g (\<lambda>w. f w z))"
proof -
  have gcon: "continuous_on {0..1} g" and hcon: "continuous_on {0..1} h"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have fgh1: "\<And>x. (\<lambda>t. f (g x) (h t)) = (\<lambda>(y1,y2). f y1 y2) \<circ> (\<lambda>t. (g x, h t))"
    by (rule ext) simp
  have fgh2: "\<And>x. (\<lambda>t. f (g t) (h x)) = (\<lambda>(y1,y2). f y1 y2) \<circ> (\<lambda>t. (g t, h x))"
    by (rule ext) simp
  have fcon_im1: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> continuous_on ((\<lambda>t. (g x, h t)) ` {0..1}) (\<lambda>(x, y). f x y)"
    by (rule continuous_on_subset [OF fcon]) (auto simp: path_image_def)
  have fcon_im2: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> continuous_on ((\<lambda>t. (g t, h x)) ` {0..1}) (\<lambda>(x, y). f x y)"
    by (rule continuous_on_subset [OF fcon]) (auto simp: path_image_def)
  have "continuous_on (cbox (0, 0) (1, 1::real)) ((\<lambda>x. vector_derivative g (at x)) \<circ> fst)"
       "continuous_on (cbox (0, 0) (1::real, 1)) ((\<lambda>x. vector_derivative h (at x)) \<circ> snd)"
    by (rule continuous_intros | simp add: gvcon hvcon)+
  then have gvcon': "continuous_on (cbox (0, 0) (1, 1::real)) (\<lambda>z. vector_derivative g (at (fst z)))"
       and  hvcon': "continuous_on (cbox (0, 0) (1::real, 1)) (\<lambda>x. vector_derivative h (at (snd x)))"
    by auto
  have "continuous_on (cbox (0, 0) (1, 1)) ((\<lambda>(y1, y2). f y1 y2) \<circ> (\<lambda>w. ((g \<circ> fst) w, (h \<circ> snd) w)))"
    apply (intro gcon hcon continuous_intros | simp)+
    apply (auto simp: path_image_def intro: continuous_on_subset [OF fcon])
    done
  then have fgh: "continuous_on (cbox (0, 0) (1, 1)) (\<lambda>x. f (g (fst x)) (h (snd x)))"
    by auto
  have "integral {0..1} (\<lambda>x. contour_integral h (f (g x)) * vector_derivative g (at x)) =
        integral {0..1} (\<lambda>x. contour_integral h (\<lambda>y. f (g x) y * vector_derivative g (at x)))"
  proof (rule integral_cong [OF contour_integral_rmul [symmetric]])
    have "\<And>x. x \<in> {0..1} \<Longrightarrow>
         continuous_on {0..1} (\<lambda>xa. f (g x) (h xa))"
    by (subst fgh1) (rule fcon_im1 hcon continuous_intros | simp)+
    then show "\<And>x. x \<in> {0..1} \<Longrightarrow> f (g x) contour_integrable_on h"
      unfolding contour_integrable_on
      using continuous_on_mult hvcon integrable_continuous_real by blast
  qed
  also have "\<dots> = integral {0..1}
                     (\<lambda>y. contour_integral g (\<lambda>x. f x (h y) * vector_derivative h (at y)))"
    unfolding contour_integral_integral
    apply (subst integral_swap_continuous [where 'a = real and 'b = real, of 0 0 1 1, simplified])
    subgoal
      by (rule fgh gvcon' hvcon' continuous_intros | simp add: split_def)+
    subgoal
      unfolding integral_mult_left [symmetric]
      by (simp only: mult_ac)
    done
  also have "\<dots> = contour_integral h (\<lambda>z. contour_integral g (\<lambda>w. f w z))"
    unfolding contour_integral_integral integral_mult_left [symmetric]
    by (simp add: algebra_simps)
  finally show ?thesis
    by (simp add: contour_integral_integral)
qed

lemma valid_path_negatepath: "valid_path \<gamma> \<Longrightarrow> valid_path (uminus \<circ> \<gamma>)"
   unfolding o_def using piecewise_C1_differentiable_neg valid_path_def by blast

lemma has_contour_integral_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and cint: "((\<lambda>z. f (- z)) has_contour_integral - i) \<gamma>"
  shows "(f has_contour_integral i) (uminus \<circ> \<gamma>)"
proof -
  obtain S where cont: "continuous_on {0..1} \<gamma>" and "finite S" and diff: "\<gamma> C1_differentiable_on {0..1} - S"
    using \<gamma> by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have "((\<lambda>x. - (f (- \<gamma> x) * vector_derivative \<gamma> (at x within {0..1}))) has_integral i) {0..1}"
    using cint by (auto simp: has_contour_integral_def dest: has_integral_neg)
  then
  have "((\<lambda>x. f (- \<gamma> x) * vector_derivative (uminus \<circ> \<gamma>) (at x within {0..1})) has_integral i) {0..1}"
  proof (rule rev_iffD1 [OF _ has_integral_spike_eq])
    show "negligible S"
      by (simp add: \<open>finite S\<close> negligible_finite)
    show "f (- \<gamma> x) * vector_derivative (uminus \<circ> \<gamma>) (at x within {0..1}) =
         - (f (- \<gamma> x) * vector_derivative \<gamma> (at x within {0..1}))"
      if "x \<in> {0..1} - S" for x
    proof -
      have "vector_derivative (uminus \<circ> \<gamma>) (at x within cbox 0 1) = - vector_derivative \<gamma> (at x within cbox 0 1)"
      proof (rule vector_derivative_within_cbox)
        show "(uminus \<circ> \<gamma> has_vector_derivative - vector_derivative \<gamma> (at x within cbox 0 1)) (at x within cbox 0 1)"
          using that unfolding o_def
          by (metis C1_differentiable_on_eq UNIV_I diff differentiable_subset has_vector_derivative_minus subsetI that vector_derivative_works)
      qed (use that in auto)
      then show ?thesis
        by simp
    qed
  qed
  then show ?thesis by (simp add: has_contour_integral_def)
qed

lemma contour_integrable_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and pi: "(\<lambda>z. f (- z)) contour_integrable_on \<gamma>"
  shows "f contour_integrable_on (uminus \<circ> \<gamma>)"
  by (metis \<gamma> add.inverse_inverse contour_integrable_on_def has_contour_integral_negatepath pi)

lemma C1_differentiable_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function p \<Longrightarrow> p C1_differentiable_on S"
  by (metis continuous_on_polymonial_function C1_differentiable_on_def  has_vector_derivative_polynomial_function)

lemma valid_path_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function p \<Longrightarrow> valid_path p"
by (force simp: valid_path_def piecewise_C1_differentiable_on_def continuous_on_polymonial_function C1_differentiable_polynomial_function)

lemma valid_path_subpath_trivial [simp]:
    fixes g :: "real \<Rightarrow> 'a::euclidean_space"
    shows "z \<noteq> g x \<Longrightarrow> valid_path (subpath x x g)"
  by (simp add: subpath_def valid_path_polynomial_function)

subsection\<open>Partial circle path\<close>

definition\<^marker>\<open>tag important\<close> part_circlepath :: "[complex, real, real, real, real] \<Rightarrow> complex"
  where "part_circlepath z r s t \<equiv> \<lambda>x. z + of_real r * exp (\<i> * of_real (linepath s t x))"

lemma pathstart_part_circlepath [simp]:
     "pathstart(part_circlepath z r s t) = z + r*exp(\<i> * s)"
by (metis part_circlepath_def pathstart_def pathstart_linepath)

lemma pathfinish_part_circlepath [simp]:
     "pathfinish(part_circlepath z r s t) = z + r*exp(\<i>*t)"
by (metis part_circlepath_def pathfinish_def pathfinish_linepath)

lemma reversepath_part_circlepath[simp]:
    "reversepath (part_circlepath z r s t) = part_circlepath z r t s"
  unfolding part_circlepath_def reversepath_def linepath_def 
  by (auto simp:algebra_simps)
    
lemma has_vector_derivative_part_circlepath [derivative_intros]:
    "((part_circlepath z r s t) has_vector_derivative
      (\<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)))
     (at x within X)"
  unfolding part_circlepath_def linepath_def scaleR_conv_of_real
  by (rule has_vector_derivative_real_field derivative_eq_intros | simp)+

lemma differentiable_part_circlepath:
  "part_circlepath c r a b differentiable at x within A"
  using has_vector_derivative_part_circlepath[of c r a b x A] differentiableI_vector by blast

lemma vector_derivative_part_circlepath:
    "vector_derivative (part_circlepath z r s t) (at x) =
       \<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)"
  using has_vector_derivative_part_circlepath vector_derivative_at by blast

lemma vector_derivative_part_circlepath01:
    "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk>
     \<Longrightarrow> vector_derivative (part_circlepath z r s t) (at x within {0..1}) =
          \<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)"
  using has_vector_derivative_part_circlepath
  by (auto simp: vector_derivative_at_within_ivl)

lemma valid_path_part_circlepath [simp]: "valid_path (part_circlepath z r s t)"
  unfolding valid_path_def
  by (auto simp: C1_differentiable_on_eq vector_derivative_works vector_derivative_part_circlepath has_vector_derivative_part_circlepath
              intro!: C1_differentiable_imp_piecewise continuous_intros)

lemma path_part_circlepath [simp]: "path (part_circlepath z r s t)"
  by (simp add: valid_path_imp_path)

proposition path_image_part_circlepath:
  assumes "s \<le> t"
    shows "path_image (part_circlepath z r s t) = {z + r * exp(\<i> * of_real x) | x. s \<le> x \<and> x \<le> t}"
proof -
  { fix z::real
    assume "0 \<le> z" "z \<le> 1"
    with \<open>s \<le> t\<close> have "\<exists>x. (exp (\<i> * linepath s t z) = exp (\<i> * of_real x)) \<and> s \<le> x \<and> x \<le> t"
      apply (rule_tac x="(1 - z) * s + z * t" in exI)
      apply (simp add: linepath_def scaleR_conv_of_real algebra_simps)
      by (metis (no_types) affine_ineq mult.commute mult_left_mono)
  }
  moreover
  { fix z
    assume "s \<le> z" "z \<le> t"
    then have "z + of_real r * exp (\<i> * of_real z) \<in> (\<lambda>x. z + of_real r * exp (\<i> * linepath s t x)) ` {0..1}"
      apply (rule_tac x="(z - s)/(t - s)" in image_eqI)
      apply (simp add: linepath_def scaleR_conv_of_real divide_simps exp_eq)
      apply (auto simp: field_split_simps)
      done
  }
  ultimately show ?thesis
    by (fastforce simp add: path_image_def part_circlepath_def)
qed

lemma path_image_part_circlepath':
  "path_image (part_circlepath z r s t) = (\<lambda>x. z + r * cis x) ` closed_segment s t"
proof -
  have "path_image (part_circlepath z r s t) = 
          (\<lambda>x. z + r * exp(\<i> * of_real x)) ` linepath s t ` {0..1}"
    by (simp add: image_image path_image_def part_circlepath_def)
  also have "linepath s t ` {0..1} = closed_segment s t"
    by (rule linepath_image_01)
  finally show ?thesis by (simp add: cis_conv_exp)
qed

lemma path_image_part_circlepath_subset:
    "\<lbrakk>s \<le> t; 0 \<le> r\<rbrakk> \<Longrightarrow> path_image(part_circlepath z r s t) \<subseteq> sphere z r"
by (auto simp: path_image_part_circlepath sphere_def dist_norm algebra_simps norm_mult)

lemma in_path_image_part_circlepath:
  assumes "w \<in> path_image(part_circlepath z r s t)" "s \<le> t" "0 \<le> r"
    shows "norm(w - z) = r"
proof -
  have "w \<in> {c. dist z c = r}"
    by (metis (no_types) path_image_part_circlepath_subset sphere_def subset_eq assms)
  thus ?thesis
    by (simp add: dist_norm norm_minus_commute)
qed

lemma path_image_part_circlepath_subset':
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath z r s t) \<subseteq> sphere z r"
proof (cases "s \<le> t")
  case True
  thus ?thesis using path_image_part_circlepath_subset[of s t r z] assms by simp
next
  case False
  thus ?thesis using path_image_part_circlepath_subset[of t s r z] assms
    by (subst reversepath_part_circlepath [symmetric], subst path_image_reversepath) simp_all
qed

lemma part_circlepath_cnj: "cnj (part_circlepath c r a b x) = part_circlepath (cnj c) r (-a) (-b) x"
  by (simp add: part_circlepath_def exp_cnj linepath_def algebra_simps)

lemma contour_integral_bound_part_circlepath:
  assumes "f contour_integrable_on part_circlepath c r a b"
  assumes "B \<ge> 0" "r \<ge> 0" "\<And>x. x \<in> path_image (part_circlepath c r a b) \<Longrightarrow> norm (f x) \<le> B"
  shows   "norm (contour_integral (part_circlepath c r a b) f) \<le> B * r * \<bar>b - a\<bar>"
proof -
  let ?I = "integral {0..1} (\<lambda>x. f (part_circlepath c r a b x) * \<i> * of_real (r * (b - a)) *
              exp (\<i> * linepath a b x))"
  have "norm ?I \<le> integral {0..1} (\<lambda>x::real. B * 1 * (r * \<bar>b - a\<bar>) * 1)"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1
    with assms(1) show ?case
      by (simp add: contour_integrable_on vector_derivative_part_circlepath mult_ac)
  next
    case (3 x)
    with assms(2-) show ?case unfolding norm_mult norm_of_real abs_mult
      by (intro mult_mono) (auto simp: path_image_def)
  qed auto
  also have "?I = contour_integral (part_circlepath c r a b) f"
    by (simp add: contour_integral_integral vector_derivative_part_circlepath mult_ac)
  finally show ?thesis by simp
qed

lemma has_contour_integral_part_circlepath_iff:
  assumes "a < b"
  shows "(f has_contour_integral I) (part_circlepath c r a b) \<longleftrightarrow>
           ((\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) has_integral I) {a..b}"
proof -
  have "(f has_contour_integral I) (part_circlepath c r a b) \<longleftrightarrow>
          ((\<lambda>x. f (part_circlepath c r a b x) * vector_derivative (part_circlepath c r a b)
           (at x within {0..1})) has_integral I) {0..1}"
    unfolding has_contour_integral_def ..
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. f (part_circlepath c r a b x) * r * (b - a) * \<i> *
                            cis (linepath a b x)) has_integral I) {0..1}"
    by (intro has_integral_cong, subst vector_derivative_part_circlepath01)
       (simp_all add: cis_conv_exp)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. f (c + r * exp (\<i> * linepath (of_real a) (of_real b) x)) *
                       r * \<i> * exp (\<i> * linepath (of_real a) (of_real b) x) *
                       vector_derivative (linepath (of_real a) (of_real b)) 
                         (at x within {0..1})) has_integral I) {0..1}"
    by (intro has_integral_cong, subst vector_derivative_linepath_within)
       (auto simp: part_circlepath_def cis_conv_exp of_real_linepath [symmetric])
  also have "\<dots> \<longleftrightarrow> ((\<lambda>z. f (c + r * exp (\<i> * z)) * r * \<i> * exp (\<i> * z)) has_contour_integral I)
                      (linepath (of_real a) (of_real b))"
    by (simp add: has_contour_integral_def)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) has_integral I) {a..b}" using assms
    by (subst has_contour_integral_linepath_Reals_iff) (simp_all add: cis_conv_exp)
  finally show ?thesis .
qed

lemma contour_integrable_part_circlepath_iff:
  assumes "a < b"
  shows "f contour_integrable_on (part_circlepath c r a b) \<longleftrightarrow>
           (\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}"
  using assms by (auto simp: contour_integrable_on_def integrable_on_def 
                             has_contour_integral_part_circlepath_iff)

lemma contour_integral_part_circlepath_eq:
  assumes "a < b"
  shows "contour_integral (part_circlepath c r a b) f =
           integral {a..b} (\<lambda>t. f (c + r * cis t) * r * \<i> * cis t)"
proof (cases "f contour_integrable_on part_circlepath c r a b")
  case True
  hence "(\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}" 
    using assms by (simp add: contour_integrable_part_circlepath_iff)
  with True show ?thesis
    using has_contour_integral_part_circlepath_iff[OF assms]
          contour_integral_unique has_integral_integrable_integral by blast
next
  case False
  hence "\<not>(\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}" 
    using assms by (simp add: contour_integrable_part_circlepath_iff)
  with False show ?thesis
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed

lemma contour_integral_part_circlepath_reverse:
  "contour_integral (part_circlepath c r a b) f = -contour_integral (part_circlepath c r b a) f"
  by (subst reversepath_part_circlepath [symmetric], subst contour_integral_reversepath) simp_all

lemma contour_integral_part_circlepath_reverse':
  "b < a \<Longrightarrow> contour_integral (part_circlepath c r a b) f = 
               -contour_integral (part_circlepath c r b a) f"
  by (rule contour_integral_part_circlepath_reverse)

lemma finite_bounded_log: "finite {z::complex. norm z \<le> b \<and> exp z = w}"
proof (cases "w = 0")
  case True then show ?thesis by auto
next
  case False
  have *: "finite {x. cmod ((2 * real_of_int x * pi) * \<i>) \<le> b + cmod (Ln w)}"
  proof (simp add: norm_mult finite_int_iff_bounded_le)
    show "\<exists>k. abs ` {x. 2 * \<bar>of_int x\<bar> * pi \<le> b + cmod (Ln w)} \<subseteq> {..k}"
    apply (rule_tac x="\<lfloor>(b + cmod (Ln w)) / (2*pi)\<rfloor>" in exI)
    apply (auto simp: field_split_simps le_floor_iff)
      done
  qed
  have [simp]: "\<And>P f. {z. P z \<and> (\<exists>n. z = f n)} = f ` {n. P (f n)}"
    by blast
  have "finite {z. cmod z \<le> b \<and> exp z = exp (Ln w)}"
    using norm_add_leD by (fastforce intro: finite_subset [OF _ *] simp: exp_eq)
  then show ?thesis
    using False by auto
qed

lemma finite_bounded_log2:
  fixes a::complex
    assumes "a \<noteq> 0"
    shows "finite {z. norm z \<le> b \<and> exp(a*z) = w}"
proof -
  have *: "finite ((\<lambda>z. z / a) ` {z. cmod z \<le> b * cmod a \<and> exp z = w})"
    by (rule finite_imageI [OF finite_bounded_log])
  show ?thesis
    by (rule finite_subset [OF _ *]) (force simp: assms norm_mult)
qed

lemma has_contour_integral_bound_part_circlepath_strong:
  assumes fi: "(f has_contour_integral i) (part_circlepath z r s t)"
      and "finite k" and le: "0 \<le> B" "0 < r" "s \<le> t"
      and B: "\<And>x. x \<in> path_image(part_circlepath z r s t) - k \<Longrightarrow> norm(f x) \<le> B"
    shows "cmod i \<le> B * r * (t - s)"
proof -
  consider "s = t" | "s < t" using \<open>s \<le> t\<close> by linarith
  then show ?thesis
  proof cases
    case 1 with fi [unfolded has_contour_integral]
    have "i = 0"  by (simp add: vector_derivative_part_circlepath)
    with assms show ?thesis by simp
  next
    case 2
    have [simp]: "\<bar>r\<bar> = r" using \<open>r > 0\<close> by linarith
    have [simp]: "cmod (complex_of_real t - complex_of_real s) = t-s"
      by (metis "2" abs_of_pos diff_gt_0_iff_gt norm_of_real of_real_diff)
    have "finite (part_circlepath z r s t -` {y} \<inter> {0..1})" if "y \<in> k" for y
    proof -
      let ?w = "(y - z)/of_real r / exp(\<i> * of_real s)"
      have fin: "finite (of_real -` {z. cmod z \<le> 1 \<and> exp (\<i> * complex_of_real (t - s) * z) = ?w})"
        using \<open>s < t\<close> 
        by (intro finite_vimageI [OF finite_bounded_log2]) (auto simp: inj_of_real)
      show ?thesis
        unfolding part_circlepath_def linepath_def vimage_def
        using le
        by (intro finite_subset [OF _ fin]) (auto simp: algebra_simps scaleR_conv_of_real exp_add exp_diff)
    qed
    then have fin01: "finite ((part_circlepath z r s t) -` k \<inter> {0..1})"
      by (rule finite_finite_vimage_IntI [OF \<open>finite k\<close>])
    have **: "((\<lambda>x. if (part_circlepath z r s t x) \<in> k then 0
                    else f(part_circlepath z r s t x) *
                       vector_derivative (part_circlepath z r s t) (at x)) has_integral i)  {0..1}"
      by (rule has_integral_spike [OF negligible_finite [OF fin01]])  (use fi has_contour_integral in auto)
    have *: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1; part_circlepath z r s t x \<notin> k\<rbrakk> \<Longrightarrow> cmod (f (part_circlepath z r s t x)) \<le> B"
      by (auto intro!: B [unfolded path_image_def image_def, simplified])
    show ?thesis
      apply (rule has_integral_bound [where 'a=real, simplified, OF _ **, simplified])
      using assms le * "2" \<open>r > 0\<close> by (auto simp add: norm_mult vector_derivative_part_circlepath)
  qed
qed

lemma has_contour_integral_bound_part_circlepath:
      "\<lbrakk>(f has_contour_integral i) (part_circlepath z r s t);
        0 \<le> B; 0 < r; s \<le> t;
        \<And>x. x \<in> path_image(part_circlepath z r s t) \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
       \<Longrightarrow> norm i \<le> B*r*(t - s)"
  by (auto intro: has_contour_integral_bound_part_circlepath_strong)

lemma contour_integrable_continuous_part_circlepath:
     "continuous_on (path_image (part_circlepath z r s t)) f
      \<Longrightarrow> f contour_integrable_on (part_circlepath z r s t)"
  unfolding contour_integrable_on has_contour_integral_def vector_derivative_part_circlepath path_image_def
  apply (rule integrable_continuous_real)
  apply (fast intro: path_part_circlepath [unfolded path_def] continuous_intros continuous_on_compose2 [where g=f, OF _ _ order_refl])
  done

lemma simple_path_part_circlepath:
    "simple_path(part_circlepath z r s t) \<longleftrightarrow> (r \<noteq> 0 \<and> s \<noteq> t \<and> \<bar>s - t\<bar> \<le> 2*pi)"
proof (cases "r = 0 \<or> s = t")
  case True
  then show ?thesis
    unfolding part_circlepath_def simple_path_def
    by (rule disjE) (force intro: bexI [where x = "1/4"] bexI [where x = "1/3"])+
next
  case False then have "r \<noteq> 0" "s \<noteq> t" by auto
  have *: "\<And>x y z s t. \<i>*((1 - x) * s + x * t) = \<i>*(((1 - y) * s + y * t)) + z  \<longleftrightarrow> \<i>*(x - y) * (t - s) = z"
    by (simp add: algebra_simps)
  have abs01: "\<And>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1
                      \<Longrightarrow> (x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0 \<longleftrightarrow> \<bar>x - y\<bar> \<in> {0,1})"
    by auto
  have **: "\<And>x y. (\<exists>n. (complex_of_real x - of_real y) * (of_real t - of_real s) = 2 * (of_int n * of_real pi)) \<longleftrightarrow>
                  (\<exists>n. \<bar>x - y\<bar> * (t - s) = 2 * (of_int n * pi))"
    by (force simp: algebra_simps abs_if dest: arg_cong [where f=Re] arg_cong [where f=complex_of_real]
                    intro: exI [where x = "-n" for n])
  have 1: "\<bar>s - t\<bar> \<le> 2 * pi"
    if "\<And>x. 0 \<le> x \<and> x \<le> 1 \<Longrightarrow> (\<exists>n. x * (t - s) = 2 * (real_of_int n * pi)) \<longrightarrow> x = 0 \<or> x = 1"
  proof (rule ccontr)
    assume "\<not> \<bar>s - t\<bar> \<le> 2 * pi"
    then have *: "\<And>n. t - s \<noteq> of_int n * \<bar>s - t\<bar>"
      using False that [of "2*pi / \<bar>t - s\<bar>"]
      by (simp add: abs_minus_commute divide_simps)
    show False
      using * [of 1] * [of "-1"] by auto
  qed
  have 2: "\<bar>s - t\<bar> = \<bar>2 * (real_of_int n * pi) / x\<bar>" if "x \<noteq> 0" "x * (t - s) = 2 * (real_of_int n * pi)" for x n
  proof -
    have "t-s = 2 * (real_of_int n * pi)/x"
      using that by (simp add: field_simps)
    then show ?thesis by (metis abs_minus_commute)
  qed
  have abs_away: "\<And>P. (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. P \<bar>x - y\<bar>) \<longleftrightarrow> (\<forall>x::real. 0 \<le> x \<and> x \<le> 1 \<longrightarrow> P x)"
    by force
  show ?thesis using False
    apply (simp add: simple_path_def)
    apply (simp add: part_circlepath_def linepath_def exp_eq  * ** abs01 del: Set.insert_iff)
    apply (subst abs_away)
    apply (auto simp: 1)
    apply (rule ccontr)
    apply (auto simp: 2 field_split_simps abs_mult dest: of_int_leD)
    done
qed

lemma arc_part_circlepath:
  assumes "r \<noteq> 0" "s \<noteq> t" "\<bar>s - t\<bar> < 2*pi"
    shows "arc (part_circlepath z r s t)"
proof -
  have *: "x = y" if eq: "\<i> * (linepath s t x) = \<i> * (linepath s t y) + 2 * of_int n * complex_of_real pi * \<i>"
    and x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y n
  proof (rule ccontr)
    assume "x \<noteq> y"
    have "(linepath s t x) = (linepath s t y) + 2 * of_int n * complex_of_real pi"
      by (metis add_divide_eq_iff complex_i_not_zero mult.commute nonzero_mult_div_cancel_left eq)
    then have "s*y + t*x = s*x + (t*y + of_int n * (pi * 2))"
      by (force simp: algebra_simps linepath_def dest: arg_cong [where f=Re])
    with \<open>x \<noteq> y\<close> have st: "s-t = (of_int n * (pi * 2) / (y-x))"
      by (force simp: field_simps)
    have "\<bar>real_of_int n\<bar> < \<bar>y - x\<bar>"
      using assms \<open>x \<noteq> y\<close> by (simp add: st abs_mult field_simps)
    then show False
      using assms x y st by (auto dest: of_int_lessD)
  qed
  then have "inj_on (part_circlepath z r s t) {0..1}"
    using assms by (force simp add: part_circlepath_def inj_on_def exp_eq)
  then show ?thesis
    by (simp add: arc_def)
qed

subsection\<open>Special case of one complete circle\<close>

definition\<^marker>\<open>tag important\<close> circlepath :: "[complex, real, real] \<Rightarrow> complex"
  where "circlepath z r \<equiv> part_circlepath z r 0 (2*pi)"

lemma circlepath: "circlepath z r = (\<lambda>x. z + r * exp(2 * of_real pi * \<i> * of_real x))"
  by (simp add: circlepath_def part_circlepath_def linepath_def algebra_simps)

lemma pathstart_circlepath [simp]: "pathstart (circlepath z r) = z + r"
  by (simp add: circlepath_def)

lemma pathfinish_circlepath [simp]: "pathfinish (circlepath z r) = z + r"
  by (simp add: circlepath_def) (metis exp_two_pi_i mult.commute)

lemma circlepath_minus: "circlepath z (-r) x = circlepath z r (x + 1/2)"
proof -
  have "z + of_real r * exp (2 * pi * \<i> * (x + 1/2)) =
        z + of_real r * exp (2 * pi * \<i> * x + pi * \<i>)"
    by (simp add: divide_simps) (simp add: algebra_simps)
  also have "\<dots> = z - r * exp (2 * pi * \<i> * x)"
    by (simp add: exp_add)
  finally show ?thesis
    by (simp add: circlepath path_image_def sphere_def dist_norm)
qed

lemma circlepath_add1: "circlepath z r (x+1) = circlepath z r x"
  using circlepath_minus [of z r "x+1/2"] circlepath_minus [of z "-r" x]
  by (simp add: add.commute)

lemma circlepath_add_half: "circlepath z r (x + 1/2) = circlepath z r (x - 1/2)"
  using circlepath_add1 [of z r "x-1/2"]
  by (simp add: add.commute)

lemma path_image_circlepath_minus_subset:
     "path_image (circlepath z (-r)) \<subseteq> path_image (circlepath z r)"
proof -
  have "\<exists>x\<in>{0..1}. circlepath z r (y + 1/2) = circlepath z r x"
    if "0 \<le> y" "y \<le> 1" for y
  proof (cases "y \<le> 1/2")
    case False
    with that show ?thesis
      by (force simp: circlepath_add_half)
  qed (use that in force)
  then show ?thesis
    by (auto simp add: path_image_def image_def circlepath_minus)
qed

lemma path_image_circlepath_minus: "path_image (circlepath z (-r)) = path_image (circlepath z r)"
  using path_image_circlepath_minus_subset by fastforce

lemma has_vector_derivative_circlepath [derivative_intros]:
 "((circlepath z r) has_vector_derivative (2 * pi * \<i> * r * exp (2 * of_real pi * \<i> * x)))
   (at x within X)"
  unfolding circlepath_def scaleR_conv_of_real
  by (rule derivative_eq_intros) (simp add: algebra_simps)

lemma vector_derivative_circlepath:
  "vector_derivative (circlepath z r) (at x) =
    2 * pi * \<i> * r * exp(2 * of_real pi * \<i> * x)"
  using has_vector_derivative_circlepath vector_derivative_at by blast

lemma vector_derivative_circlepath01:
    "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk>
     \<Longrightarrow> vector_derivative (circlepath z r) (at x within {0..1}) =
          2 * pi * \<i> * r * exp(2 * of_real pi * \<i> * x)"
  using has_vector_derivative_circlepath
  by (auto simp: vector_derivative_at_within_ivl)

lemma valid_path_circlepath [simp]: "valid_path (circlepath z r)"
  by (simp add: circlepath_def)

lemma path_circlepath [simp]: "path (circlepath z r)"
  by (simp add: valid_path_imp_path)

lemma path_image_circlepath_nonneg:
  assumes "0 \<le> r" shows "path_image (circlepath z r) = sphere z r"
proof -
  have *: "x \<in> (\<lambda>u. z + (cmod (x - z)) * exp (\<i> * (of_real u * (of_real pi * 2)))) ` {0..1}" for x
  proof (cases "x = z")
    case True then show ?thesis by force
  next
    case False
    define w where "w = x - z"
    then have "w \<noteq> 0" by (simp add: False)
    have **: "\<And>t. \<lbrakk>Re w = cos t * cmod w; Im w = sin t * cmod w\<rbrakk> \<Longrightarrow> w = of_real (cmod w) * exp (\<i> * t)"
      using cis_conv_exp complex_eq_iff by auto
    obtain t where "0 \<le> t" "t < 2*pi" "Re(w/norm w) = cos t" "Im(w/norm w) = sin t"
      apply (rule sincos_total_2pi [of "Re(w/(norm w))" "Im(w/(norm w))"])
      by (auto simp add: divide_simps \<open>w \<noteq> 0\<close> cmod_power2 [symmetric])
    then
    show ?thesis
      using False ** w_def \<open>w \<noteq> 0\<close>
      by (rule_tac x="t / (2*pi)" in image_eqI) (auto simp add: field_simps)
  qed
  show ?thesis
    unfolding circlepath path_image_def sphere_def dist_norm
    by (force simp: assms algebra_simps norm_mult norm_minus_commute intro: *)
qed

lemma path_image_circlepath [simp]:
    "path_image (circlepath z r) = sphere z \<bar>r\<bar>"
  using path_image_circlepath_minus
  by (force simp: path_image_circlepath_nonneg abs_if)

lemma has_contour_integral_bound_circlepath_strong:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        finite k; 0 \<le> B; 0 < r;
        \<And>x. \<lbrakk>norm(x - z) = r; x \<notin> k\<rbrakk> \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  unfolding circlepath_def
  by (auto simp: algebra_simps in_path_image_part_circlepath dest!: has_contour_integral_bound_part_circlepath_strong)

lemma has_contour_integral_bound_circlepath:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        0 \<le> B; 0 < r; \<And>x. norm(x - z) = r \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  by (auto intro: has_contour_integral_bound_circlepath_strong)

lemma contour_integrable_continuous_circlepath:
    "continuous_on (path_image (circlepath z r)) f
     \<Longrightarrow> f contour_integrable_on (circlepath z r)"
  by (simp add: circlepath_def contour_integrable_continuous_part_circlepath)

lemma simple_path_circlepath: "simple_path(circlepath z r) \<longleftrightarrow> (r \<noteq> 0)"
  by (simp add: circlepath_def simple_path_part_circlepath)

lemma notin_path_image_circlepath [simp]: "cmod (w - z) < r \<Longrightarrow> w \<notin> path_image (circlepath z r)"
  by (simp add: sphere_def dist_norm norm_minus_commute)

lemma contour_integral_circlepath:
  assumes "r > 0"
  shows "contour_integral (circlepath z r) (\<lambda>w. 1 / (w - z)) = 2 * complex_of_real pi * \<i>"
proof (rule contour_integral_unique)
  show "((\<lambda>w. 1 / (w - z)) has_contour_integral 2 * complex_of_real pi * \<i>) (circlepath z r)"
    unfolding has_contour_integral_def using assms has_integral_const_real [of _ 0 1]
    apply (subst has_integral_cong)
     apply (simp add: vector_derivative_circlepath01)
    apply (force simp: circlepath)
    done
qed

subsection\<open> Uniform convergence of path integral\<close>

text\<open>Uniform convergence when the derivative of the path is bounded, and in particular for the special case of a circle.\<close>

proposition contour_integral_uniform_limit:
  assumes ev_fint: "eventually (\<lambda>n::'a. (f n) contour_integrable_on \<gamma>) F"
      and ul_f: "uniform_limit (path_image \<gamma>) f l F"
      and noleB: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (vector_derivative \<gamma> (at t)) \<le> B"
      and \<gamma>: "valid_path \<gamma>"
      and [simp]: "\<not> trivial_limit F"
  shows "l contour_integrable_on \<gamma>" "((\<lambda>n. contour_integral \<gamma> (f n)) \<longlongrightarrow> contour_integral \<gamma> l) F"
proof -
  have "0 \<le> B" by (meson noleB [of 0] atLeastAtMost_iff norm_ge_zero order_refl order_trans zero_le_one)
  { fix e::real
    assume "0 < e"
    then have "0 < e / (\<bar>B\<bar> + 1)" by simp
    then have "\<forall>\<^sub>F n in F. \<forall>x\<in>path_image \<gamma>. cmod (f n x - l x) < e / (\<bar>B\<bar> + 1)"
      using ul_f [unfolded uniform_limit_iff dist_norm] by auto
    with ev_fint
    obtain a where fga: "\<And>x. x \<in> {0..1} \<Longrightarrow> cmod (f a (\<gamma> x) - l (\<gamma> x)) < e / (\<bar>B\<bar> + 1)"
               and inta: "(\<lambda>t. f a (\<gamma> t) * vector_derivative \<gamma> (at t)) integrable_on {0..1}"
      using eventually_happens [OF eventually_conj]
      by (fastforce simp: contour_integrable_on path_image_def)
    have Ble: "B * e / (\<bar>B\<bar> + 1) \<le> e"
      using \<open>0 \<le> B\<close>  \<open>0 < e\<close> by (simp add: field_split_simps)
    have "\<exists>h. (\<forall>x\<in>{0..1}. cmod (l (\<gamma> x) * vector_derivative \<gamma> (at x) - h x) \<le> e) \<and> h integrable_on {0..1}"
    proof (intro exI conjI ballI)
      show "cmod (l (\<gamma> x) * vector_derivative \<gamma> (at x) - f a (\<gamma> x) * vector_derivative \<gamma> (at x)) \<le> e"
        if "x \<in> {0..1}" for x
        apply (rule order_trans [OF _ Ble])
        using noleB [OF that] fga [OF that] \<open>0 \<le> B\<close> \<open>0 < e\<close>
        apply (fastforce simp: mult_ac dest: mult_mono [OF less_imp_le] simp add: norm_mult left_diff_distrib [symmetric] norm_minus_commute divide_simps)
        done
    qed (rule inta)
  }
  then show lintg: "l contour_integrable_on \<gamma>"
    unfolding contour_integrable_on by (metis (mono_tags, lifting)integrable_uniform_limit_real)
  { fix e::real
    define B' where "B' = B + 1"
    have B': "B' > 0" "B' > B" using  \<open>0 \<le> B\<close> by (auto simp: B'_def)
    assume "0 < e"
    then have ev_no': "\<forall>\<^sub>F n in F. \<forall>x\<in>path_image \<gamma>. 2 * cmod (f n x - l x) < e / B'"
      using ul_f [unfolded uniform_limit_iff dist_norm, rule_format, of "e / B'/2"] B'
        by (simp add: field_simps)
    have ie: "integral {0..1::real} (\<lambda>x. e/2) < e" using \<open>0 < e\<close> by simp
    have *: "cmod (f x (\<gamma> t) * vector_derivative \<gamma> (at t) - l (\<gamma> t) * vector_derivative \<gamma> (at t)) \<le> e/2"
             if t: "t\<in>{0..1}" and leB': "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) < e / B'" for x t
    proof -
      have "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) * cmod (vector_derivative \<gamma> (at t)) \<le> e * (B/ B')"
        using mult_mono [OF less_imp_le [OF leB'] noleB] B' \<open>0 < e\<close> t by auto
      also have "\<dots> < e"
        by (simp add: B' \<open>0 < e\<close> mult_imp_div_pos_less)
      finally have "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) * cmod (vector_derivative \<gamma> (at t)) < e" .
      then show ?thesis
        by (simp add: left_diff_distrib [symmetric] norm_mult)
    qed
    have le_e: "\<And>x. \<lbrakk>\<forall>xa\<in>{0..1}. 2 * cmod (f x (\<gamma> xa) - l (\<gamma> xa)) < e / B'; f x contour_integrable_on \<gamma>\<rbrakk>
         \<Longrightarrow> cmod (integral {0..1}
                    (\<lambda>u. f x (\<gamma> u) * vector_derivative \<gamma> (at u) - l (\<gamma> u) * vector_derivative \<gamma> (at u))) < e"
      apply (rule le_less_trans [OF integral_norm_bound_integral ie])
        apply (simp add: lintg integrable_diff contour_integrable_on [symmetric])
       apply (blast intro: *)+
      done
    have "\<forall>\<^sub>F x in F. dist (contour_integral \<gamma> (f x)) (contour_integral \<gamma> l) < e"
      apply (rule eventually_mono [OF eventually_conj [OF ev_no' ev_fint]])
      apply (simp add: dist_norm contour_integrable_on path_image_def contour_integral_integral)
      apply (simp add: lintg integral_diff [symmetric] contour_integrable_on [symmetric] le_e)
      done
  }
  then show "((\<lambda>n. contour_integral \<gamma> (f n)) \<longlongrightarrow> contour_integral \<gamma> l) F"
    by (rule tendstoI)
qed

corollary\<^marker>\<open>tag unimportant\<close> contour_integral_uniform_limit_circlepath:
  assumes "\<forall>\<^sub>F n::'a in F. (f n) contour_integrable_on (circlepath z r)"
      and "uniform_limit (sphere z r) f l F"
      and "\<not> trivial_limit F" "0 < r"
    shows "l contour_integrable_on (circlepath z r)"
          "((\<lambda>n. contour_integral (circlepath z r) (f n)) \<longlongrightarrow> contour_integral (circlepath z r) l) F"
  using assms by (auto simp: vector_derivative_circlepath norm_mult intro!: contour_integral_uniform_limit)

end
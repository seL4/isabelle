(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
                Huge cleanup by LCP
*)

section \<open>Henstock-Kurzweil Gauge Integration in Many Dimensions\<close>

theory Henstock_Kurzweil_Integration
imports
  Lebesgue_Measure Tagged_Division
begin

lemma norm_diff2: "\<lbrakk>y = y1 + y2; x = x1 + x2; e = e1 + e2; norm(y1 - x1) \<le> e1; norm(y2 - x2) \<le> e2\<rbrakk>
  \<Longrightarrow> norm(y-x) \<le> e"
  using norm_triangle_mono [of "y1 - x1" "e1" "y2 - x2" "e2"]
  by (simp add: add_diff_add)

lemma setcomp_dot1: "{z. P (z \<bullet> (i,0))} = {(x,y). P(x \<bullet> i)}"
  by auto

lemma setcomp_dot2: "{z. P (z \<bullet> (0,i))} = {(x,y). P(y \<bullet> i)}"
  by auto

lemma Sigma_Int_Paircomp1: "(Sigma A B) \<inter> {(x, y). P x} = Sigma (A \<inter> {x. P x}) B"
  by blast

lemma Sigma_Int_Paircomp2: "(Sigma A B) \<inter> {(x, y). P y} = Sigma A (\<lambda>z. B z \<inter> {y. P y})"
  by blast
(* END MOVE *)

subsection \<open>Content (length, area, volume...) of an interval\<close>

abbreviation content :: "'a::euclidean_space set \<Rightarrow> real"
  where "content s \<equiv> measure lborel s"

lemma content_cbox_cases:
  "content (cbox a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then prod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by (simp add: measure_lborel_cbox_eq inner_diff)

lemma content_cbox: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  unfolding content_cbox_cases by simp

lemma content_cbox': "cbox a b \<noteq> {} \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by (simp add: box_ne_empty inner_diff)

lemma content_cbox_if: "content (cbox a b) = (if cbox a b = {} then 0 else \<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by (simp add: content_cbox')

lemma content_cbox_cart:
   "cbox a b \<noteq> {} \<Longrightarrow> content(cbox a b) = prod (\<lambda>i. b$i - a$i) UNIV"
  by (simp add: content_cbox_if Basis_vec_def cart_eq_inner_axis axis_eq_axis prod.UNION_disjoint)

lemma content_cbox_if_cart:
   "content(cbox a b) = (if cbox a b = {} then 0 else prod (\<lambda>i. b$i - a$i) UNIV)"
  by (simp add: content_cbox_cart)

lemma content_division_of:
  assumes "K \<in> \<D>" "\<D> division_of S"
  shows "content K = (\<Prod>i \<in> Basis. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i)"
proof -
  obtain a b where "K = cbox a b"
    using cbox_division_memE assms by metis
  then show ?thesis
    using assms by (force simp: division_of_def content_cbox')
qed

lemma content_real: "a \<le> b \<Longrightarrow> content {a..b} = b - a"
  by simp

lemma abs_eq_content: "\<bar>y - x\<bar> = (if x\<le>y then content {x..y} else content {y..x})"
  by (auto simp: content_real)

lemma content_singleton: "content {a} = 0"
  by simp

lemma content_unit[iff]: "content (cbox 0 (One::'a::euclidean_space)) = 1"
  by simp

lemma content_pos_le [iff]: "0 \<le> content X"
  by simp

corollary\<^marker>\<open>tag unimportant\<close> content_nonneg [simp]: "\<not> content (cbox a b) < 0"
  using not_le by blast

lemma content_pos_lt: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i \<Longrightarrow> 0 < content (cbox a b)"
  by (auto simp: less_imp_le inner_diff box_eq_empty intro!: prod_pos)

lemma content_eq_0: "content (cbox a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by (auto simp: content_cbox_cases not_le intro: less_imp_le antisym eq_refl)

lemma content_eq_0_interior: "content (cbox a b) = 0 \<longleftrightarrow> interior(cbox a b) = {}"
  unfolding content_eq_0 interior_cbox box_eq_empty by auto

lemma content_pos_lt_eq: "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  by (auto simp add: content_cbox_cases less_le prod_nonneg)

lemma content_empty [simp]: "content {} = 0"
  by simp

lemma content_real_if [simp]: "content {a..b} = (if a \<le> b then b - a else 0)"
  by (simp add: content_real)

lemma content_subset: "cbox a b \<subseteq> cbox c d \<Longrightarrow> content (cbox a b) \<le> content (cbox c d)"
  unfolding measure_def
  by (intro enn2real_mono emeasure_mono) (auto simp: emeasure_lborel_cbox_eq)

lemma content_lt_nz: "0 < content (cbox a b) \<longleftrightarrow> content (cbox a b) \<noteq> 0"
  unfolding content_pos_lt_eq content_eq_0 unfolding not_ex not_le by fastforce

lemma content_Pair: "content (cbox (a,c) (b,d)) = content (cbox a b) * content (cbox c d)"
  unfolding measure_lborel_cbox_eq Basis_prod_def
  apply (subst prod.union_disjoint)
  apply (auto simp: bex_Un ball_Un)
  apply (subst (1 2) prod.reindex_nontrivial)
  apply auto
  done

lemma content_cbox_pair_eq0_D:
   "content (cbox (a,c) (b,d)) = 0 \<Longrightarrow> content (cbox a b) = 0 \<or> content (cbox c d) = 0"
  by (simp add: content_Pair)

lemma content_cbox_plus:
  fixes x :: "'a::euclidean_space"
  shows "content(cbox x (x + h *\<^sub>R One)) = (if h \<ge> 0 then h ^ DIM('a) else 0)"
  by (simp add: algebra_simps content_cbox_if box_eq_empty)

lemma content_0_subset: "content(cbox a b) = 0 \<Longrightarrow> s \<subseteq> cbox a b \<Longrightarrow> content s = 0"
  using emeasure_mono[of s "cbox a b" lborel]
  by (auto simp: measure_def enn2real_eq_0_iff emeasure_lborel_cbox_eq)

lemma content_ball_pos:
  assumes "r > 0"
  shows   "content (ball c r) > 0"
proof -
  from rational_boxes[OF assms, of c] obtain a b where ab: "c \<in> box a b" "box a b \<subseteq> ball c r"
    by auto
  from ab have "0 < content (box a b)"
    by (subst measure_lborel_box_eq) (auto intro!: prod_pos simp: algebra_simps box_def)
  have "emeasure lborel (box a b) \<le> emeasure lborel (ball c r)"
    using ab by (intro emeasure_mono) auto
  also have "emeasure lborel (box a b) = ennreal (content (box a b))"
    using emeasure_lborel_box_finite[of a b] by (intro emeasure_eq_ennreal_measure) auto
  also have "emeasure lborel (ball c r) = ennreal (content (ball c r))"
    using emeasure_lborel_ball_finite[of c r] by (intro emeasure_eq_ennreal_measure) auto
  finally show ?thesis
    using \<open>content (box a b) > 0\<close> by simp
qed

lemma content_cball_pos:
  assumes "r > 0"
  shows   "content (cball c r) > 0"
proof -
  from rational_boxes[OF assms, of c] obtain a b where ab: "c \<in> box a b" "box a b \<subseteq> ball c r"
    by auto
  from ab have "0 < content (box a b)"
    by (subst measure_lborel_box_eq) (auto intro!: prod_pos simp: algebra_simps box_def)
  have "emeasure lborel (box a b) \<le> emeasure lborel (ball c r)"
    using ab by (intro emeasure_mono) auto
  also have "\<dots> \<le> emeasure lborel (cball c r)"
    by (intro emeasure_mono) auto
  also have "emeasure lborel (box a b) = ennreal (content (box a b))"
    using emeasure_lborel_box_finite[of a b] by (intro emeasure_eq_ennreal_measure) auto
  also have "emeasure lborel (cball c r) = ennreal (content (cball c r))"
    using emeasure_lborel_cball_finite[of c r] by (intro emeasure_eq_ennreal_measure) auto
  finally show ?thesis
    using \<open>content (box a b) > 0\<close> by simp
qed

lemma content_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "content (cbox a b) = content(cbox a b \<inter> {x. x\<bullet>k \<le> c}) + content(cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
  \<comment> \<open>Prove using measure theory\<close>
proof (cases "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i")
  case True
  have 1: "\<And>X Y Z. (\<Prod>i\<in>Basis. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>Basis-{k}. Z i (Y i))"
    by (simp add: if_distrib prod.delta_remove assms)
  note simps = interval_split[OF assms] content_cbox_cases
  have 2: "(\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i) = (\<Prod>i\<in>Basis-{k}. b\<bullet>i - a\<bullet>i) * (b\<bullet>k - a\<bullet>k)"
    by (metis (no_types, lifting) assms finite_Basis mult.commute prod.remove)
  have "\<And>x. min (b \<bullet> k) c = max (a \<bullet> k) c \<Longrightarrow>
    x * (b\<bullet>k - a\<bullet>k) = x * (max (a \<bullet> k) c - a \<bullet> k) + x * (b \<bullet> k - max (a \<bullet> k) c)"
    by  (auto simp add: field_simps)
  moreover
  have **: "(\<Prod>i\<in>Basis. ((\<Sum>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) *\<^sub>R i) \<bullet> i - a \<bullet> i)) =
      (\<Prod>i\<in>Basis. (if i = k then min (b \<bullet> k) c else b \<bullet> i) - a \<bullet> i)"
    "(\<Prod>i\<in>Basis. b \<bullet> i - ((\<Sum>i\<in>Basis. (if i = k then max (a \<bullet> k) c else a \<bullet> i) *\<^sub>R i) \<bullet> i)) =
      (\<Prod>i\<in>Basis. b \<bullet> i - (if i = k then max (a \<bullet> k) c else a \<bullet> i))"
    by (auto intro!: prod.cong)
  have "\<not> a \<bullet> k \<le> c \<Longrightarrow> \<not> c \<le> b \<bullet> k \<Longrightarrow> False"
    unfolding not_le using True assms by auto
  ultimately show ?thesis
    using assms unfolding simps ** 1[of "\<lambda>i x. b\<bullet>i - x"] 1[of "\<lambda>i x. x - a\<bullet>i"] 2
    by auto
next
  case False
  then have "cbox a b = {}"
    unfolding box_eq_empty by (auto simp: not_le)
  then show ?thesis
    by (auto simp: not_le)
qed

lemma division_of_content_0:
  assumes "content (cbox a b) = 0" "d division_of (cbox a b)" "K \<in> d"
  shows "content K = 0"
  unfolding forall_in_division[OF assms(2)]
  by (meson assms content_0_subset division_of_def)

lemma sum_content_null:
  assumes "content (cbox a b) = 0"
    and "p tagged_division_of (cbox a b)"
  shows "(\<Sum>(x,K)\<in>p. content K *\<^sub>R f x) = (0::'a::real_normed_vector)"
proof (rule sum.neutral, rule)
  fix y
  assume y: "y \<in> p"
  obtain x K where xk: "y = (x, K)"
    using surj_pair[of y] by blast
  then obtain c d where k: "K = cbox c d" "K \<subseteq> cbox a b"
    by (metis assms(2) tagged_division_ofD(3) tagged_division_ofD(4) y)
  have "(\<lambda>(x',K'). content K' *\<^sub>R f x') y = content K *\<^sub>R f x"
    unfolding xk by auto
  also have "\<dots> = 0"
    using assms(1) content_0_subset k(2) by auto
  finally show "(\<lambda>(x, k). content k *\<^sub>R f x) y = 0" .
qed

global_interpretation sum_content: operative plus 0 content
  rewrites "comm_monoid_set.F plus 0 = sum"
proof -
  interpret operative plus 0 content
    by standard (auto simp add: content_split [symmetric] content_eq_0_interior)
  show "operative plus 0 content"
    by standard
  show "comm_monoid_set.F plus 0 = sum"
    by (simp add: sum_def)
qed

lemma additive_content_division: "d division_of (cbox a b) \<Longrightarrow> sum content d = content (cbox a b)"
  by (fact sum_content.division)

lemma additive_content_tagged_division:
  "d tagged_division_of (cbox a b) \<Longrightarrow> sum (\<lambda>(x,l). content l) d = content (cbox a b)"
  by (fact sum_content.tagged_division)

lemma subadditive_content_division:
  assumes "\<D> division_of S" "S \<subseteq> cbox a b"
  shows "sum content \<D> \<le> content(cbox a b)"
proof -
  have "\<D> division_of \<Union>\<D>" "\<Union>\<D> \<subseteq> cbox a b"
    using assms by auto
  then obtain \<D>' where "\<D> \<subseteq> \<D>'" "\<D>' division_of cbox a b"
    using partial_division_extend_interval by metis
  then have "sum content \<D> \<le> sum content \<D>'"
    using sum_mono2 by blast
  also have "... \<le> content(cbox a b)"
    by (simp add: \<open>\<D>' division_of cbox a b\<close> additive_content_division less_eq_real_def)
  finally show ?thesis .
qed

lemma content_real_eq_0: "content {a..b::real} = 0 \<longleftrightarrow> a \<ge> b"
  by (metis atLeastatMost_empty_iff2 content_empty content_real diff_self eq_iff le_cases le_iff_diff_le_0)

lemma property_empty_interval: "\<forall>a b. content (cbox a b) = 0 \<longrightarrow> P (cbox a b) \<Longrightarrow> P {}"
  using content_empty unfolding empty_as_interval by auto

lemma interval_bounds_nz_content [simp]:
  assumes "content (cbox a b) \<noteq> 0"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
  by (metis assms content_empty interval_bounds')+

subsection \<open>Gauge integral\<close>

text \<open>Case distinction to define it first on compact intervals first, then use a limit. This is only
much later unified. In Fremlin: Measure Theory, Volume 4I this is generalized using residual sets.\<close>

definition has_integral :: "('n::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> 'n set \<Rightarrow> bool"
  (infixr "has'_integral" 46)
  where "(f has_integral I) s \<longleftrightarrow>
    (if \<exists>a b. s = cbox a b
      then ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter s)
      else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
        (\<exists>z. ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R (if x \<in> s then f x else 0)) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
          norm (z - I) < e)))"

lemma has_integral_cbox:
  "(f has_integral I) (cbox a b) \<longleftrightarrow> ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter (cbox a b))"
  by (auto simp add: has_integral_def)

lemma has_integral:
  "(f has_integral y) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of (cbox a b) \<and> \<gamma> fine \<D> \<longrightarrow>
        norm (sum (\<lambda>(x,k). content(k) *\<^sub>R f x) \<D> - y) < e))"
  by (auto simp: dist_norm eventually_division_filter has_integral_def tendsto_iff)

lemma has_integral_real:
  "(f has_integral y) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D> \<longrightarrow>
        norm (sum (\<lambda>(x,k). content(k) *\<^sub>R f x) \<D> - y) < e))"
  unfolding box_real[symmetric] by (rule has_integral)

lemma has_integralD[dest]:
  assumes "(f has_integral y) (cbox a b)"
    and "e > 0"
  obtains \<gamma>
    where "gauge \<gamma>"
      and "\<And>\<D>. \<D> tagged_division_of (cbox a b) \<Longrightarrow> \<gamma> fine \<D> \<Longrightarrow>
        norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R f x) - y) < e"
  using assms unfolding has_integral by auto

lemma has_integral_alt:
  "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)))"
  by (subst has_integral_def) (auto simp add: has_integral_cbox)

lemma has_integral_altD:
  assumes "(f has_integral y) i"
    and "\<not> (\<exists>a b. i = cbox a b)"
    and "e>0"
  obtains B where "B > 0"
    and "\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - y) < e)"
  using assms has_integral_alt[of f y i] by auto

definition integrable_on (infixr "integrable'_on" 46)
  where "f integrable_on i \<longleftrightarrow> (\<exists>y. (f has_integral y) i)"

definition "integral i f = (SOME y. (f has_integral y) i \<or> \<not> f integrable_on i \<and> y=0)"

lemma integrable_integral[intro]: "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
  unfolding integrable_on_def integral_def by (metis (mono_tags, lifting) someI_ex)

lemma not_integrable_integral: "\<not> f integrable_on i \<Longrightarrow> integral i f = 0"
  unfolding integrable_on_def integral_def by blast

lemma has_integral_integrable[dest]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
  unfolding integrable_on_def by auto

lemma has_integral_integral: "f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
  by auto

subsection \<open>Basic theorems about integrals\<close>

lemma has_integral_eq_rhs: "(f has_integral j) S \<Longrightarrow> i = j \<Longrightarrow> (f has_integral i) S"
  by (rule forw_subst)

lemma has_integral_unique_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  shows "(f has_integral k1) (cbox a b) \<Longrightarrow> (f has_integral k2) (cbox a b) \<Longrightarrow> k1 = k2"
    by (auto simp: has_integral_cbox intro: tendsto_unique[OF division_filter_not_empty])    

lemma has_integral_unique:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i" "(f has_integral k2) i"
  shows "k1 = k2"
proof (rule ccontr)
  let ?e = "norm (k1 - k2)/2"
  let ?F = "(\<lambda>x. if x \<in> i then f x else 0)"
  assume "k1 \<noteq> k2"
  then have e: "?e > 0"
    by auto
  have nonbox: "\<not> (\<exists>a b. i = cbox a b)"
    using \<open>k1 \<noteq> k2\<close> assms has_integral_unique_cbox by blast
  obtain B1 where B1:
      "0 < B1"
      "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. (?F has_integral z) (cbox a b) \<and> norm (z - k1) < norm (k1 - k2)/2"
    by (rule has_integral_altD[OF assms(1) nonbox,OF e]) blast
  obtain B2 where B2:
      "0 < B2"
      "\<And>a b. ball 0 B2 \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. (?F has_integral z) (cbox a b) \<and> norm (z - k2) < norm (k1 - k2)/2"
    by (rule has_integral_altD[OF assms(2) nonbox,OF e]) blast
  obtain a b :: 'n where ab: "ball 0 B1 \<subseteq> cbox a b" "ball 0 B2 \<subseteq> cbox a b"
    by (metis Un_subset_iff bounded_Un bounded_ball bounded_subset_cbox_symmetric)
  obtain w where w: "(?F has_integral w) (cbox a b)" "norm (w - k1) < norm (k1 - k2)/2"
    using B1(2)[OF ab(1)] by blast
  obtain z where z: "(?F has_integral z) (cbox a b)" "norm (z - k2) < norm (k1 - k2)/2"
    using B2(2)[OF ab(2)] by blast
  have "z = w"
    using has_integral_unique_cbox[OF w(1) z(1)] by auto
  then have "norm (k1 - k2) \<le> norm (z - k2) + norm (w - k1)"
    using norm_triangle_ineq4 [of "k1 - w" "k2 - z"]
    by (auto simp add: norm_minus_commute)
  also have "\<dots> < norm (k1 - k2)/2 + norm (k1 - k2)/2"
    by (metis add_strict_mono z(2) w(2))
  finally show False by auto
qed

lemma integral_unique [intro]: "(f has_integral y) k \<Longrightarrow> integral k f = y"
  unfolding integral_def
  by (rule some_equality) (auto intro: has_integral_unique)

lemma has_integral_iff: "(f has_integral i) S \<longleftrightarrow> (f integrable_on S \<and> integral S f = i)"
  by blast

lemma eq_integralD: "integral k f = y \<Longrightarrow> (f has_integral y) k \<or> \<not> f integrable_on k \<and> y=0"
  unfolding integral_def integrable_on_def
  apply (erule subst)
  apply (rule someI_ex)
  by blast

lemma has_integral_const [intro]:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>x. c) has_integral (content (cbox a b) *\<^sub>R c)) (cbox a b)"
  using eventually_division_filter_tagged_division[of "cbox a b"]
     additive_content_tagged_division[of _ a b]
  by (auto simp: has_integral_cbox split_beta' scaleR_sum_left[symmetric]
           elim!: eventually_mono intro!: tendsto_cong[THEN iffD1, OF _ tendsto_const])

lemma has_integral_const_real [intro]:
  fixes a b :: real
  shows "((\<lambda>x. c) has_integral (content {a..b} *\<^sub>R c)) {a..b}"
  by (metis box_real(2) has_integral_const)

lemma has_integral_integrable_integral: "(f has_integral i) s \<longleftrightarrow> f integrable_on s \<and> integral s f = i"
  by blast

lemma integral_const [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "integral (cbox a b) (\<lambda>x. c) = content (cbox a b) *\<^sub>R c"
  by (rule integral_unique) (rule has_integral_const)

lemma integral_const_real [simp]:
  fixes a b :: real
  shows "integral {a..b} (\<lambda>x. c) = content {a..b} *\<^sub>R c"
  by (metis box_real(2) integral_const)

lemma has_integral_is_0_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> cbox a b \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
    unfolding has_integral_cbox
    using eventually_division_filter_tagged_division[of "cbox a b"] assms
    by (subst tendsto_cong[where g="\<lambda>_. 0"])
       (auto elim!: eventually_mono intro!: sum.neutral simp: tag_in_interval)

lemma has_integral_is_0:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) S"
proof (cases "(\<exists>a b. S = cbox a b)")
  case True with assms has_integral_is_0_cbox show ?thesis
    by blast
next
  case False
  have *: "(\<lambda>x. if x \<in> S then f x else 0) = (\<lambda>x. 0)"
    by (auto simp add: assms)
  show ?thesis
    using has_integral_is_0_cbox False
    by (subst has_integral_alt) (force simp add: *)
qed

lemma has_integral_0[simp]: "((\<lambda>x::'n::euclidean_space. 0) has_integral 0) S"
  by (rule has_integral_is_0) auto

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) S \<longleftrightarrow> i = 0"
  using has_integral_unique[OF has_integral_0] by auto

lemma has_integral_linear_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) (cbox a b)"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) (cbox a b)"
proof -
  interpret bounded_linear h using h .
  show ?thesis
    unfolding has_integral_cbox using tendsto [OF f [unfolded has_integral_cbox]]
    by (simp add: sum scaleR split_beta')
qed

lemma has_integral_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) S"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) S"
proof (cases "(\<exists>a b. S = cbox a b)")
  case True with f h has_integral_linear_cbox show ?thesis 
    by blast
next
  case False
  interpret bounded_linear h using h .
  from pos_bounded obtain B where B: "0 < B" "\<And>x. norm (h x) \<le> norm x * B"
    by blast
  let ?S = "\<lambda>f x. if x \<in> S then f x else 0"
  show ?thesis
  proof (subst has_integral_alt, clarsimp simp: False)
    fix e :: real
    assume e: "e > 0"
    have *: "0 < e/B" using e B(1) by simp
    obtain M where M:
      "M > 0"
      "\<And>a b. ball 0 M \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. (?S f has_integral z) (cbox a b) \<and> norm (z - y) < e/B"
      using has_integral_altD[OF f False *] by blast
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. (?S(h \<circ> f) has_integral z) (cbox a b) \<and> norm (z - h y) < e)"
    proof (rule exI, intro allI conjI impI)
      show "M > 0" using M by metis
    next
      fix a b::'n
      assume sb: "ball 0 M \<subseteq> cbox a b"
      obtain z where z: "(?S f has_integral z) (cbox a b)" "norm (z - y) < e/B"
        using M(2)[OF sb] by blast
      have *: "?S(h \<circ> f) = h \<circ> ?S f"
        using zero by auto
      show "\<exists>z. (?S(h \<circ> f) has_integral z) (cbox a b) \<and> norm (z - h y) < e"
      proof (intro exI conjI)
        show "(?S(h \<circ> f) has_integral h z) (cbox a b)"
          by (simp add: * has_integral_linear_cbox[OF z(1) h])
        show "norm (h z - h y) < e"
          by (metis B diff le_less_trans pos_less_divide_eq z(2))
      qed
    qed
  qed
qed

lemma has_integral_scaleR_left:
  "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x *\<^sub>R c) has_integral (y *\<^sub>R c)) S"
  using has_integral_linear[OF _ bounded_linear_scaleR_left] by (simp add: comp_def)

lemma integrable_on_scaleR_left:
  assumes "f integrable_on A"
  shows "(\<lambda>x. f x *\<^sub>R y) integrable_on A"
  using assms has_integral_scaleR_left unfolding integrable_on_def by blast

lemma has_integral_mult_left:
  fixes c :: "_ :: real_normed_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x * c) has_integral (y * c)) S"
  using has_integral_linear[OF _ bounded_linear_mult_left] by (simp add: comp_def)

lemma has_integral_divide:
  fixes c :: "_ :: real_normed_div_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x / c) has_integral (y / c)) S"
  unfolding divide_inverse by (simp add: has_integral_mult_left)

text\<open>The case analysis eliminates the condition \<^term>\<open>f integrable_on S\<close> at the cost
     of the type class constraint \<open>division_ring\<close>\<close>
corollary integral_mult_left [simp]:
  fixes c:: "'a::{real_normed_algebra,division_ring}"
  shows "integral S (\<lambda>x. f x * c) = integral S f * c"
proof (cases "f integrable_on S \<or> c = 0")
  case True then show ?thesis
    by (force intro: has_integral_mult_left)
next
  case False then have "\<not> (\<lambda>x. f x * c) integrable_on S"
    using has_integral_mult_left [of "(\<lambda>x. f x * c)" _ S "inverse c"]
    by (auto simp add: mult.assoc)
  with False show ?thesis by (simp add: not_integrable_integral)
qed

corollary integral_mult_right [simp]:
  fixes c:: "'a::{real_normed_field}"
  shows "integral S (\<lambda>x. c * f x) = c * integral S f"
by (simp add: mult.commute [of c])

corollary integral_divide [simp]:
  fixes z :: "'a::real_normed_field"
  shows "integral S (\<lambda>x. f x / z) = integral S (\<lambda>x. f x) / z"
using integral_mult_left [of S f "inverse z"]
  by (simp add: divide_inverse_commute)

lemma has_integral_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  shows "(f has_integral y) i \<Longrightarrow> ((\<lambda>x. c * f x) has_integral (c * y)) i"
  using has_integral_linear[OF _ bounded_linear_mult_right] by (simp add: comp_def)

lemma has_integral_cmul: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) S"
  unfolding o_def[symmetric]
  by (metis has_integral_linear bounded_linear_scaleR_right)

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  from has_integral_cmul[OF assms[OF this], of c] show ?thesis
    unfolding real_scaleR_def .
qed

lemma has_integral_neg: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral -k) S"
  by (drule_tac c="-1" in has_integral_cmul) auto

lemma has_integral_neg_iff: "((\<lambda>x. - f x) has_integral k) S \<longleftrightarrow> (f has_integral - k) S"
  using has_integral_neg[of f "- k"] has_integral_neg[of "\<lambda>x. - f x" k] by auto

lemma has_integral_add_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k) (cbox a b)" "(g has_integral l) (cbox a b)"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) (cbox a b)"
  using assms
    unfolding has_integral_cbox
    by (simp add: split_beta' scaleR_add_right sum.distrib[abs_def] tendsto_add)

lemma has_integral_add:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral k) S" and g: "(g has_integral l) S"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) S"
proof (cases "\<exists>a b. S = cbox a b")
  case True with has_integral_add_cbox assms show ?thesis
    by blast 
next
  let ?S = "\<lambda>f x. if x \<in> S then f x else 0"
  case False
  then show ?thesis
  proof (subst has_integral_alt, clarsimp, goal_cases)
    case (1 e)
    then have e2: "e/2 > 0"
      by auto
    obtain Bf where "0 < Bf"
      and Bf: "\<And>a b. ball 0 Bf \<subseteq> cbox a b \<Longrightarrow>
                     \<exists>z. (?S f has_integral z) (cbox a b) \<and> norm (z - k) < e/2"
      using has_integral_altD[OF f False e2] by blast
    obtain Bg where "0 < Bg"
      and Bg: "\<And>a b. ball 0 Bg \<subseteq> (cbox a b) \<Longrightarrow>
                     \<exists>z. (?S g has_integral z) (cbox a b) \<and> norm (z - l) < e/2"
      using has_integral_altD[OF g False e2] by blast
    show ?case
    proof (rule_tac x="max Bf Bg" in exI, clarsimp simp add: max.strict_coboundedI1 \<open>0 < Bf\<close>)
      fix a b
      assume "ball 0 (max Bf Bg) \<subseteq> cbox a (b::'n)"
      then have fs: "ball 0 Bf \<subseteq> cbox a (b::'n)" and gs: "ball 0 Bg \<subseteq> cbox a (b::'n)"
        by auto
      obtain w where w: "(?S f has_integral w) (cbox a b)" "norm (w - k) < e/2"
        using Bf[OF fs] by blast
      obtain z where z: "(?S g has_integral z) (cbox a b)" "norm (z - l) < e/2"
        using Bg[OF gs] by blast
      have *: "\<And>x. (if x \<in> S then f x + g x else 0) = (?S f x) + (?S g x)"
        by auto
      show "\<exists>z. (?S(\<lambda>x. f x + g x) has_integral z) (cbox a b) \<and> norm (z - (k + l)) < e"
      proof (intro exI conjI)
        show "(?S(\<lambda>x. f x + g x) has_integral (w + z)) (cbox a b)"
          by (simp add: has_integral_add_cbox[OF w(1) z(1), unfolded *[symmetric]])
        show "norm (w + z - (k + l)) < e"
          by (metis dist_norm dist_triangle_add_half w(2) z(2))
      qed
    qed
  qed
qed

lemma has_integral_diff:
  "(f has_integral k) S \<Longrightarrow> (g has_integral l) S \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_integral (k - l)) S"
  using has_integral_add[OF _ has_integral_neg, of f k S g l]
  by (auto simp: algebra_simps)

lemma integral_0 [simp]:
  "integral S (\<lambda>x::'n::euclidean_space. 0::'m::real_normed_vector) = 0"
  by (rule integral_unique has_integral_0)+

lemma integral_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x + g x) = integral S f + integral S g"
  by (rule integral_unique) (metis integrable_integral has_integral_add)

lemma integral_cmul [simp]: "integral S (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral S f"
proof (cases "f integrable_on S \<or> c = 0")
  case True with has_integral_cmul integrable_integral show ?thesis
    by fastforce
next
  case False then have "\<not> (\<lambda>x. c *\<^sub>R f x) integrable_on S"
    using has_integral_cmul [of "(\<lambda>x. c *\<^sub>R f x)" _ S "inverse c"] by auto
  with False show ?thesis by (simp add: not_integrable_integral)
qed

lemma integral_mult:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> K * integral X f = integral X (\<lambda>x. K * f x)"
  unfolding real_scaleR_def[symmetric] integral_cmul ..

lemma integral_neg [simp]: "integral S (\<lambda>x. - f x) = - integral S f"
proof (cases "f integrable_on S")
  case True then show ?thesis
    by (simp add: has_integral_neg integrable_integral integral_unique)
next
  case False then have "\<not> (\<lambda>x. - f x) integrable_on S"
    using has_integral_neg [of "(\<lambda>x. - f x)" _ S ] by auto
  with False show ?thesis by (simp add: not_integrable_integral)
qed

lemma integral_diff: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x - g x) = integral S f - integral S g"
  by (rule integral_unique) (metis integrable_integral has_integral_diff)

lemma integrable_0: "(\<lambda>x. 0) integrable_on S"
  unfolding integrable_on_def using has_integral_0 by auto

lemma integrable_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on S"
  unfolding integrable_on_def by(auto intro: has_integral_add)

lemma integrable_cmul: "f integrable_on S \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on S"
  unfolding integrable_on_def by(auto intro: has_integral_cmul)

lemma integrable_on_scaleR_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c *\<^sub>R f x) integrable_on S \<longleftrightarrow> f integrable_on S"
  using integrable_cmul[of "\<lambda>x. c *\<^sub>R f x" S "1 / c"] integrable_cmul[of f S c] \<open>c \<noteq> 0\<close>
  by auto

lemma integrable_on_cmult_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on S \<longleftrightarrow> f integrable_on S"
  using integrable_on_scaleR_iff [of c f] assms by simp

lemma integrable_on_cmult_left:
  assumes "f integrable_on S"
  shows "(\<lambda>x. of_real c * f x) integrable_on S"
    using integrable_cmul[of f S "of_real c"] assms
    by (simp add: scaleR_conv_of_real)

lemma integrable_neg: "f integrable_on S \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on S"
  unfolding integrable_on_def by(auto intro: has_integral_neg)

lemma integrable_neg_iff: "(\<lambda>x. -f(x)) integrable_on S \<longleftrightarrow> f integrable_on S"
  using integrable_neg by fastforce

lemma integrable_diff:
  "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on S"
  unfolding integrable_on_def by(auto intro: has_integral_diff)

lemma integrable_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) integrable_on S"
  unfolding integrable_on_def by(auto intro: has_integral_linear)

lemma integral_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> integral S (h \<circ> f) = h (integral S f)"
  by (meson has_integral_iff has_integral_linear)

lemma integrable_on_cnj_iff:
  "(\<lambda>x. cnj (f x)) integrable_on A \<longleftrightarrow> f integrable_on A"
  using integrable_linear[OF _ bounded_linear_cnj, of f A]
        integrable_linear[OF _ bounded_linear_cnj, of "cnj \<circ> f" A]
  by (auto simp: o_def)

lemma integral_cnj: "cnj (integral A f) = integral A (\<lambda>x. cnj (f x))"
  by (cases "f integrable_on A")
     (simp_all add: integral_linear[OF _ bounded_linear_cnj, symmetric]
                    o_def integrable_on_cnj_iff not_integrable_integral)

lemma integral_component_eq[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on S"
  shows "integral S (\<lambda>x. f x \<bullet> k) = integral S f \<bullet> k"
  unfolding integral_linear[OF assms(1) bounded_linear_inner_left,unfolded o_def] ..

lemma has_integral_sum:
  assumes "finite T"
    and "\<And>a. a \<in> T \<Longrightarrow> ((f a) has_integral (i a)) S"
  shows "((\<lambda>x. sum (\<lambda>a. f a x) T) has_integral (sum i T)) S"
  using assms(1) subset_refl[of T]
proof (induct rule: finite_subset_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  with assms show ?case
    by (simp add: has_integral_add)
qed

lemma integral_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow>
   integral S (\<lambda>x. \<Sum>a\<in>I. f a x) = (\<Sum>a\<in>I. integral S (f a))"
  by (simp add: has_integral_sum integrable_integral integral_unique)

lemma integrable_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Sum>a\<in>I. f a x) integrable_on S"
  unfolding integrable_on_def using has_integral_sum[of I] by metis

lemma has_integral_eq:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and "(f has_integral k) s"
  shows "(g has_integral k) s"
  using has_integral_diff[OF assms(2), of "\<lambda>x. f x - g x" 0]
  using has_integral_is_0[of s "\<lambda>x. f x - g x"]
  using assms(1)
  by auto

lemma integrable_eq: "\<lbrakk>f integrable_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g integrable_on s"
  unfolding integrable_on_def
  using has_integral_eq[of s f g] has_integral_eq by blast

lemma has_integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(f has_integral i) s = (g has_integral i) s"
  using has_integral_eq[of s f g] has_integral_eq[of s g f] assms
  by auto

lemma integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "integral s f = integral s g"
  unfolding integral_def
by (metis (full_types, hide_lams) assms has_integral_cong integrable_eq)

lemma integrable_on_cmult_left_iff [simp]:
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. of_real c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "(\<lambda>x. of_real (1 / c) * (of_real c * f x)) integrable_on s"
    using integrable_cmul[of "\<lambda>x. of_real c * f x" s "1 / of_real c"]
    by (simp add: scaleR_conv_of_real)
  then have "(\<lambda>x. (of_real (1 / c) * of_real c * f x)) integrable_on s"
    by (simp add: algebra_simps)
  with \<open>c \<noteq> 0\<close> show ?rhs
    by (metis (no_types, lifting) integrable_eq mult.left_neutral nonzero_divide_eq_eq of_real_1 of_real_mult)
qed (blast intro: integrable_on_cmult_left)

lemma integrable_on_cmult_right:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x * of_real c) integrable_on s"
using integrable_on_cmult_left [OF assms] by (simp add: mult.commute)

lemma integrable_on_cmult_right_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x * of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
using integrable_on_cmult_left_iff [OF assms] by (simp add: mult.commute)

lemma integrable_on_cdivide:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x / of_real c) integrable_on s"
by (simp add: integrable_on_cmult_right divide_inverse assms flip: of_real_inverse)

lemma integrable_on_cdivide_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x / of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
by (simp add: divide_inverse assms flip: of_real_inverse)

lemma has_integral_null [intro]: "content(cbox a b) = 0 \<Longrightarrow> (f has_integral 0) (cbox a b)"
  unfolding has_integral_cbox
  using eventually_division_filter_tagged_division[of "cbox a b"]
  by (subst tendsto_cong[where g="\<lambda>_. 0"]) (auto elim: eventually_mono intro: sum_content_null)

lemma has_integral_null_real [intro]: "content {a..b::real} = 0 \<Longrightarrow> (f has_integral 0) {a..b}"
  by (metis box_real(2) has_integral_null)

lemma has_integral_null_eq[simp]: "content (cbox a b) = 0 \<Longrightarrow> (f has_integral i) (cbox a b) \<longleftrightarrow> i = 0"
  by (auto simp add: has_integral_null dest!: integral_unique)

lemma integral_null [simp]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
  by (metis has_integral_null integral_unique)

lemma integrable_on_null [intro]: "content (cbox a b) = 0 \<Longrightarrow> f integrable_on (cbox a b)"
  by (simp add: has_integral_integrable)

lemma has_integral_empty[intro]: "(f has_integral 0) {}"
  by (meson ex_in_conv has_integral_is_0)

lemma has_integral_empty_eq[simp]: "(f has_integral i) {} \<longleftrightarrow> i = 0"
  by (auto simp add: has_integral_empty has_integral_unique)

lemma integrable_on_empty[intro]: "f integrable_on {}"
  unfolding integrable_on_def by auto

lemma integral_empty[simp]: "integral {} f = 0"
  by (rule integral_unique) (rule has_integral_empty)

lemma has_integral_refl[intro]:
  fixes a :: "'a::euclidean_space"
  shows "(f has_integral 0) (cbox a a)"
    and "(f has_integral 0) {a}"
proof -
  show "(f has_integral 0) (cbox a a)"
     by (rule has_integral_null) simp
  then show "(f has_integral 0) {a}"
    by simp
qed

lemma integrable_on_refl[intro]: "f integrable_on cbox a a"
  unfolding integrable_on_def by auto

lemma integral_refl [simp]: "integral (cbox a a) f = 0"
  by (rule integral_unique) auto

lemma integral_singleton [simp]: "integral {a} f = 0"
  by auto

lemma integral_blinfun_apply:
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. blinfun_apply h (f x)) = blinfun_apply h (integral s f)"
  by (subst integral_linear[symmetric, OF assms blinfun.bounded_linear_right]) (simp add: o_def)

lemma blinfun_apply_integral:
  assumes "f integrable_on s"
  shows "blinfun_apply (integral s f) x = integral s (\<lambda>y. blinfun_apply (f y) x)"
  by (metis (no_types, lifting) assms blinfun.prod_left.rep_eq integral_blinfun_apply integral_cong)

lemma has_integral_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(f has_integral y) A \<longleftrightarrow> (\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
proof safe
  fix b :: 'b assume "(f has_integral y) A"
  from has_integral_linear[OF this(1) bounded_linear_inner_left, of b]
    show "((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A" by (simp add: o_def)
next
  assume "(\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
  hence "\<forall>b\<in>Basis. (((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. f x \<bullet> b)) has_integral ((y \<bullet> b) *\<^sub>R b)) A"
    by (intro ballI has_integral_linear) (simp_all add: bounded_linear_scaleR_left)
  hence "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. (y \<bullet> b) *\<^sub>R b)) A"
    by (intro has_integral_sum) (simp_all add: o_def)
  thus "(f has_integral y) A" by (simp add: euclidean_representation)
qed

lemma has_integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A) \<Longrightarrow> (f has_integral y) A"
  by (subst has_integral_componentwise_iff) blast

lemma integrable_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
proof
  assume "f integrable_on A"
  then obtain y where "(f has_integral y) A" by (auto simp: integrable_on_def)
  hence "(\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
    by (subst (asm) has_integral_componentwise_iff)
  thus "(\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)" by (auto simp: integrable_on_def)
next
  assume "(\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
  then obtain y where "\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral y b) A"
    unfolding integrable_on_def by (subst (asm) bchoice_iff) blast
  hence "\<forall>b\<in>Basis. (((\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. f x \<bullet> b)) has_integral (y b *\<^sub>R b)) A"
    by (intro ballI has_integral_linear) (simp_all add: bounded_linear_scaleR_left)
  hence "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. y b *\<^sub>R b)) A"
    by (intro has_integral_sum) (simp_all add: o_def)
  thus "f integrable_on A" by (auto simp: integrable_on_def o_def euclidean_representation)
qed

lemma integrable_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) integrable_on A) \<Longrightarrow> f integrable_on A"
  by (subst integrable_componentwise_iff) blast

lemma integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = (\<Sum>b\<in>Basis. integral A (\<lambda>x. (f x \<bullet> b) *\<^sub>R b))"
proof -
  from assms have integrable: "\<forall>b\<in>Basis. (\<lambda>x. x *\<^sub>R b) \<circ> (\<lambda>x. (f x \<bullet> b)) integrable_on A"
    by (subst (asm) integrable_componentwise_iff, intro integrable_linear ballI)
       (simp_all add: bounded_linear_scaleR_left)
  have "integral A f = integral A (\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b)"
    by (simp add: euclidean_representation)
  also from integrable have "\<dots> = (\<Sum>a\<in>Basis. integral A (\<lambda>x. (f x \<bullet> a) *\<^sub>R a))"
    by (subst integral_sum) (simp_all add: o_def)
  finally show ?thesis .
qed

lemma integrable_component:
  "f integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (y :: 'b :: euclidean_space)) integrable_on A"
  by (drule integrable_linear[OF _ bounded_linear_inner_left[of y]]) (simp add: o_def)



subsection \<open>Cauchy-type criterion for integrability\<close>

proposition integrable_Cauchy:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  shows "f integrable_on cbox a b \<longleftrightarrow>
        (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
          (\<forall>\<D>1 \<D>2. \<D>1 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>1 \<and>
            \<D>2 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>2 \<longrightarrow>
            norm ((\<Sum>(x,K)\<in>\<D>1. content K *\<^sub>R f x) - (\<Sum>(x,K)\<in>\<D>2. content K *\<^sub>R f x)) < e))"
  (is "?l = (\<forall>e>0. \<exists>\<gamma>. ?P e \<gamma>)")
proof (intro iffI allI impI)
  assume ?l
  then obtain y
    where y: "\<And>e. e > 0 \<Longrightarrow>
        \<exists>\<gamma>. gauge \<gamma> \<and>
            (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                 norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - y) < e)"
    by (auto simp: integrable_on_def has_integral)
  show "\<exists>\<gamma>. ?P e \<gamma>" if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
    with y obtain \<gamma> where "gauge \<gamma>"
      and \<gamma>: "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<Longrightarrow>
                  norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f x) - y) < e/2"
      by meson
    show ?thesis
    apply (rule_tac x=\<gamma> in exI, clarsimp simp: \<open>gauge \<gamma>\<close>)
        by (blast intro!: \<gamma> dist_triangle_half_l[where y=y,unfolded dist_norm])
    qed
next
  assume "\<forall>e>0. \<exists>\<gamma>. ?P e \<gamma>"
  then have "\<forall>n::nat. \<exists>\<gamma>. ?P (1 / (n + 1)) \<gamma>"
    by auto
  then obtain \<gamma> :: "nat \<Rightarrow> 'n \<Rightarrow> 'n set" where \<gamma>:
    "\<And>m. gauge (\<gamma> m)"
    "\<And>m \<D>1 \<D>2. \<lbrakk>\<D>1 tagged_division_of cbox a b;
              \<gamma> m fine \<D>1; \<D>2 tagged_division_of cbox a b; \<gamma> m fine \<D>2\<rbrakk>
              \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>1. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> \<D>2. content K *\<^sub>R f x))
                  < 1 / (m + 1)"
    by metis
  have "gauge (\<lambda>x. \<Inter>{\<gamma> i x |i. i \<in> {0..n}})" for n
    using \<gamma> by (intro gauge_Inter) auto
  then have "\<forall>n. \<exists>p. p tagged_division_of (cbox a b) \<and> (\<lambda>x. \<Inter>{\<gamma> i x |i. i \<in> {0..n}}) fine p"
    by (meson fine_division_exists)
  then obtain p where p: "\<And>z. p z tagged_division_of cbox a b"
                         "\<And>z. (\<lambda>x. \<Inter>{\<gamma> i x |i. i \<in> {0..z}}) fine p z"
    by meson
  have dp: "\<And>i n. i\<le>n \<Longrightarrow> \<gamma> i fine p n"
    using p unfolding fine_Inter
    using atLeastAtMost_iff by blast
  have "Cauchy (\<lambda>n. sum (\<lambda>(x,K). content K *\<^sub>R (f x)) (p n))"
  proof (rule CauchyI)
    fix e::real
    assume "0 < e"
    then obtain N where "N \<noteq> 0" and N: "inverse (real N) < e"
      using real_arch_inverse[of e] by blast
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm ((\<Sum>(x,K) \<in> p m. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p n. content K *\<^sub>R f x)) < e"
    proof (intro exI allI impI)
      fix m n
      assume mn: "N \<le> m" "N \<le> n"
      have "norm ((\<Sum>(x,K) \<in> p m. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p n. content K *\<^sub>R f x)) < 1 / (real N + 1)"
        by (simp add: p(1) dp mn \<gamma>)
      also have "... < e"
        using  N \<open>N \<noteq> 0\<close> \<open>0 < e\<close> by (auto simp: field_simps)
      finally show "norm ((\<Sum>(x,K) \<in> p m. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p n. content K *\<^sub>R f x)) < e" .
    qed
  qed
  then obtain y where y: "\<exists>no. \<forall>n\<ge>no. norm ((\<Sum>(x,K) \<in> p n. content K *\<^sub>R f x) - y) < r" if "r > 0" for r
    by (auto simp: convergent_eq_Cauchy[symmetric] dest: LIMSEQ_D)
  show ?l
    unfolding integrable_on_def has_integral
  proof (rule_tac x=y in exI, clarify)
    fix e :: real
    assume "e>0"
    then have e2: "e/2 > 0" by auto
    then obtain N1::nat where N1: "N1 \<noteq> 0" "inverse (real N1) < e/2"
      using real_arch_inverse by blast
    obtain N2::nat where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> norm ((\<Sum>(x,K) \<in> p n. content K *\<^sub>R f x) - y) < e/2"
      using y[OF e2] by metis
    show "\<exists>\<gamma>. gauge \<gamma> \<and>
              (\<forall>\<D>. \<D> tagged_division_of (cbox a b) \<and> \<gamma> fine \<D> \<longrightarrow>
                norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - y) < e)"
    proof (intro exI conjI allI impI)
      show "gauge (\<gamma> (N1+N2))"
        using \<gamma> by auto
      show "norm ((\<Sum>(x,K) \<in> q. content K *\<^sub>R f x) - y) < e"
           if "q tagged_division_of cbox a b \<and> \<gamma> (N1+N2) fine q" for q
      proof (rule norm_triangle_half_r)
        have "norm ((\<Sum>(x,K) \<in> p (N1+N2). content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> q. content K *\<^sub>R f x))
               < 1 / (real (N1+N2) + 1)"
          by (rule \<gamma>; simp add: dp p that)
        also have "... < e/2"
          using N1 \<open>0 < e\<close> by (auto simp: field_simps intro: less_le_trans)
        finally show "norm ((\<Sum>(x,K) \<in> p (N1+N2). content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> q. content K *\<^sub>R f x)) < e/2" .
        show "norm ((\<Sum>(x,K) \<in> p (N1+N2). content K *\<^sub>R f x) - y) < e/2"
          using N2 le_add_same_cancel2 by blast
      qed
    qed
  qed
qed


subsection \<open>Additivity of integral on abutting intervals\<close>

lemma tagged_division_split_left_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<le> c} = K2 \<inter> {x. x\<bullet>k \<le> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
proof -
  from tagged_division_ofD(4)[OF \<D> \<open>(x1, K1) \<in> \<D>\<close>] obtain a b where K1: "K1 = cbox a b"
    by auto
  then have "interior (K1 \<inter> {x. x \<bullet> k \<le> c}) = {}"
    by (metis tagged_division_split_left_inj assms)
  then show ?thesis
    unfolding K1 interval_split[OF \<open>k \<in> Basis\<close>] by (auto simp: content_eq_0_interior)
qed

lemma tagged_division_split_right_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
proof -
  from tagged_division_ofD(4)[OF \<D> \<open>(x1, K1) \<in> \<D>\<close>] obtain a b where K1: "K1 = cbox a b"
    by auto
  then have "interior (K1 \<inter> {x. c \<le> x \<bullet> k}) = {}"
    by (metis tagged_division_split_right_inj assms)
  then show ?thesis
    unfolding K1 interval_split[OF \<open>k \<in> Basis\<close>]
    by (auto simp: content_eq_0_interior)
qed


proposition has_integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes fi: "(f has_integral i) (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      and fj: "(f has_integral j) (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      and k: "k \<in> Basis"
shows "(f has_integral (i + j)) (cbox a b)"
  unfolding has_integral
proof clarify
  fix e::real
  assume "0 < e"
  then have e: "e/2 > 0"
    by auto
    obtain \<gamma>1 where \<gamma>1: "gauge \<gamma>1"
      and \<gamma>1norm:
        "\<And>\<D>. \<lbrakk>\<D> tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c}; \<gamma>1 fine \<D>\<rbrakk>
             \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - i) < e/2"
       apply (rule has_integralD[OF fi[unfolded interval_split[OF k]] e])
       apply (simp add: interval_split[symmetric] k)
      done
    obtain \<gamma>2 where \<gamma>2: "gauge \<gamma>2"
      and \<gamma>2norm:
        "\<And>\<D>. \<lbrakk>\<D> tagged_division_of cbox a b \<inter> {x. c \<le> x \<bullet> k}; \<gamma>2 fine \<D>\<rbrakk>
             \<Longrightarrow> norm ((\<Sum>(x, k) \<in> \<D>. content k *\<^sub>R f x) - j) < e/2"
       apply (rule has_integralD[OF fj[unfolded interval_split[OF k]] e])
       apply (simp add: interval_split[symmetric] k)
       done
  let ?\<gamma> = "\<lambda>x. if x\<bullet>k = c then (\<gamma>1 x \<inter> \<gamma>2 x) else ball x \<bar>x\<bullet>k - c\<bar> \<inter> \<gamma>1 x \<inter> \<gamma>2 x"
  have "gauge ?\<gamma>"
    using \<gamma>1 \<gamma>2 unfolding gauge_def by auto
  then show "\<exists>\<gamma>. gauge \<gamma> \<and>
                 (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                      norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) - (i + j)) < e)"
  proof (rule_tac x="?\<gamma>" in exI, safe)
    fix p
    assume p: "p tagged_division_of (cbox a b)" and "?\<gamma> fine p"
    have ab_eqp: "cbox a b = \<Union>{K. \<exists>x. (x, K) \<in> p}"
      using p by blast
    have xk_le_c: "x\<bullet>k \<le> c" if as: "(x,K) \<in> p" and K: "K \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}" for x K
    proof (rule ccontr)
      assume **: "\<not> x \<bullet> k \<le> c"
      then have "K \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
        using \<open>?\<gamma> fine p\<close> as by (fastforce simp: not_le algebra_simps)
      with K obtain y where y: "y \<in> ball x \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<le> c"
        by blast
      then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>"
        using Basis_le_norm[OF k, of "x - y"]
        by (auto simp add: dist_norm inner_diff_left intro: le_less_trans)
      with y show False
        using ** by (auto simp add: field_simps)
    qed
    have xk_ge_c: "x\<bullet>k \<ge> c" if as: "(x,K) \<in> p" and K: "K \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}" for x K
    proof (rule ccontr)
      assume **: "\<not> x \<bullet> k \<ge> c"
      then have "K \<subseteq> ball x \<bar>x \<bullet> k - c\<bar>"
        using \<open>?\<gamma> fine p\<close> as by (fastforce simp: not_le algebra_simps)
      with K obtain y where y: "y \<in> ball x \<bar>x \<bullet> k - c\<bar>" "y\<bullet>k \<ge> c"
        by blast
      then have "\<bar>x \<bullet> k - y \<bullet> k\<bar> < \<bar>x \<bullet> k - c\<bar>"
        using Basis_le_norm[OF k, of "x - y"]
        by (auto simp add: dist_norm inner_diff_left intro: le_less_trans)
      with y show False
        using ** by (auto simp add: field_simps)
    qed
    have fin_finite: "finite {(x,f K) | x K. (x,K) \<in> s \<and> P x K}"
      if "finite s" for s and f :: "'a set \<Rightarrow> 'a set" and P :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
    proof -
      from that have "finite ((\<lambda>(x,K). (x, f K)) ` s)"
        by auto
      then show ?thesis
        by (rule rev_finite_subset) auto
    qed
    { fix \<G> :: "'a set \<Rightarrow> 'a set"
      fix i :: "'a \<times> 'a set"
      assume "i \<in> (\<lambda>(x, k). (x, \<G> k)) ` p - {(x, \<G> k) |x k. (x, k) \<in> p \<and> \<G> k \<noteq> {}}"
      then obtain x K where xk: "i = (x, \<G> K)"  "(x,K) \<in> p"
                                 "(x, \<G> K) \<notin> {(x, \<G> K) |x K. (x,K) \<in> p \<and> \<G> K \<noteq> {}}"
        by auto
      have "content (\<G> K) = 0"
        using xk using content_empty by auto
      then have "(\<lambda>(x,K). content K *\<^sub>R f x) i = 0"
        unfolding xk split_conv by auto
    } note [simp] = this
    have "finite p"
      using p by blast
    let ?M1 = "{(x, K \<inter> {x. x\<bullet>k \<le> c}) |x K. (x,K) \<in> p \<and> K \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}}"
    have \<gamma>1_fine: "\<gamma>1 fine ?M1"
      using \<open>?\<gamma> fine p\<close> by (fastforce simp: fine_def split: if_split_asm)
    have "norm ((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) < e/2"
    proof (rule \<gamma>1norm [OF tagged_division_ofI \<gamma>1_fine])
      show "finite ?M1"
        by (rule fin_finite) (use p in blast)
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M1} = cbox a b \<inter> {x. x\<bullet>k \<le> c}"
        by (auto simp: ab_eqp)

      fix x L
      assume xL: "(x, L) \<in> ?M1"
      then obtain x' L' where xL': "x = x'" "L = L' \<inter> {x. x \<bullet> k \<le> c}"
                                   "(x', L') \<in> p" "L' \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
        by blast
      then obtain a' b' where ab': "L' = cbox a' b'"
        using p by blast
      show "x \<in> L" "L \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<le> c}"
        using p xk_le_c xL' by auto
      show "\<exists>a b. L = cbox a b"
        using p xL' ab' by (auto simp add: interval_split[OF k,where c=c])

      fix y R
      assume yR: "(y, R) \<in> ?M1"
      then obtain y' R' where yR': "y = y'" "R = R' \<inter> {x. x \<bullet> k \<le> c}"
                                   "(y', R') \<in> p" "R' \<inter> {x. x \<bullet> k \<le> c} \<noteq> {}"
        by blast
      assume as: "(x, L) \<noteq> (y, R)"
      show "interior L \<inter> interior R = {}"
      proof (cases "L' = R' \<longrightarrow> x' = y'")
        case False
        have "interior R' = {}"
          by (metis (no_types) False Pair_inject inf.idem tagged_division_ofD(5) [OF p] xL'(3) yR'(3))
        then show ?thesis
          using yR' by simp
      next
        case True
        then have "L' \<noteq> R'"
          using as unfolding xL' yR' by auto
        have "interior L' \<inter> interior R' = {}"
          by (metis (no_types) Pair_inject \<open>L' \<noteq> R'\<close> p tagged_division_ofD(5) xL'(3) yR'(3))
        then show ?thesis
          using xL'(2) yR'(2) by auto
      qed
    qed
    moreover
    let ?M2 = "{(x,K \<inter> {x. x\<bullet>k \<ge> c}) |x K. (x,K) \<in> p \<and> K \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}}"
    have \<gamma>2_fine: "\<gamma>2 fine ?M2"
      using \<open>?\<gamma> fine p\<close> by (fastforce simp: fine_def split: if_split_asm)
    have "norm ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) < e/2"
    proof (rule \<gamma>2norm [OF tagged_division_ofI \<gamma>2_fine])
      show "finite ?M2"
        by (rule fin_finite) (use p in blast)
      show "\<Union>{k. \<exists>x. (x, k) \<in> ?M2} = cbox a b \<inter> {x. x\<bullet>k \<ge> c}"
        by (auto simp: ab_eqp)

      fix x L
      assume xL: "(x, L) \<in> ?M2"
      then obtain x' L' where xL': "x = x'" "L = L' \<inter> {x. x \<bullet> k \<ge> c}"
                                   "(x', L') \<in> p" "L' \<inter> {x. x \<bullet> k \<ge> c} \<noteq> {}"
        by blast
      then obtain a' b' where ab': "L' = cbox a' b'"
        using p by blast
      show "x \<in> L" "L \<subseteq> cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
        using p xk_ge_c xL' by auto
      show "\<exists>a b. L = cbox a b"
        using p xL' ab' by (auto simp add: interval_split[OF k,where c=c])

      fix y R
      assume yR: "(y, R) \<in> ?M2"
      then obtain y' R' where yR': "y = y'" "R = R' \<inter> {x. x \<bullet> k \<ge> c}"
                                   "(y', R') \<in> p" "R' \<inter> {x. x \<bullet> k \<ge> c} \<noteq> {}"
        by blast
      assume as: "(x, L) \<noteq> (y, R)"
      show "interior L \<inter> interior R = {}"
      proof (cases "L' = R' \<longrightarrow> x' = y'")
        case False
        have "interior R' = {}"
          by (metis (no_types) False Pair_inject inf.idem tagged_division_ofD(5) [OF p] xL'(3) yR'(3))
        then show ?thesis
          using yR' by simp
      next
        case True
        then have "L' \<noteq> R'"
          using as unfolding xL' yR' by auto
        have "interior L' \<inter> interior R' = {}"
          by (metis (no_types) Pair_inject \<open>L' \<noteq> R'\<close> p tagged_division_ofD(5) xL'(3) yR'(3))
        then show ?thesis
          using xL'(2) yR'(2) by auto
      qed
    qed
    ultimately
    have "norm (((\<Sum>(x,K) \<in> ?M1. content K *\<^sub>R f x) - i) + ((\<Sum>(x,K) \<in> ?M2. content K *\<^sub>R f x) - j)) < e/2 + e/2"
      using norm_add_less by blast
    moreover have "((\<Sum>(x,K) \<in> ?M1. content K *\<^sub>R f x) - i) +
                   ((\<Sum>(x,K) \<in> ?M2. content K *\<^sub>R f x) - j) =
                   (\<Sum>(x, ka)\<in>p. content ka *\<^sub>R f x) - (i + j)"
    proof -
      have eq0: "\<And>x y. x = (0::real) \<Longrightarrow> x *\<^sub>R (y::'b) = 0"
         by auto
      have cont_eq: "\<And>g. (\<lambda>(x,l). content l *\<^sub>R f x) \<circ> (\<lambda>(x,l). (x,g l)) = (\<lambda>(x,l). content (g l) *\<^sub>R f x)"
        by auto
      have *: "\<And>\<G> :: 'a set \<Rightarrow> 'a set.
                  (\<Sum>(x,K)\<in>{(x, \<G> K) |x K. (x,K) \<in> p \<and> \<G> K \<noteq> {}}. content K *\<^sub>R f x) =
                  (\<Sum>(x,K)\<in>(\<lambda>(x,K). (x, \<G> K)) ` p. content K *\<^sub>R f x)"
        by (rule sum.mono_neutral_left) (auto simp: \<open>finite p\<close>)
      have "((\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) - i) + ((\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - j) =
        (\<Sum>(x, k)\<in>?M1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>?M2. content k *\<^sub>R f x) - (i + j)"
        by auto
      moreover have "\<dots> = (\<Sum>(x,K) \<in> p. content (K \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f x) +
        (\<Sum>(x,K) \<in> p. content (K \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f x) - (i + j)"
        unfolding *
        apply (subst (1 2) sum.reindex_nontrivial)
           apply (auto intro!: k p eq0 tagged_division_split_left_inj_content tagged_division_split_right_inj_content
                       simp: cont_eq \<open>finite p\<close>)
        done
      moreover have "\<And>x. x \<in> p \<Longrightarrow> (\<lambda>(a,B). content (B \<inter> {a. a \<bullet> k \<le> c}) *\<^sub>R f a) x +
                                (\<lambda>(a,B). content (B \<inter> {a. c \<le> a \<bullet> k}) *\<^sub>R f a) x =
                                (\<lambda>(a,B). content B *\<^sub>R f a) x"
      proof clarify
        fix a B
        assume "(a, B) \<in> p"
        with p obtain u v where uv: "B = cbox u v" by blast
        then show "content (B \<inter> {x. x \<bullet> k \<le> c}) *\<^sub>R f a + content (B \<inter> {x. c \<le> x \<bullet> k}) *\<^sub>R f a = content B *\<^sub>R f a"
          by (auto simp: scaleR_left_distrib uv content_split[OF k,of u v c])
      qed
      ultimately show ?thesis
        by (auto simp: sum.distrib[symmetric])
      qed
    ultimately show "norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - (i + j)) < e"
      by auto
  qed
qed


subsection \<open>A sort of converse, integrability on subintervals\<close>

lemma has_integral_separate_sides:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes f: "(f has_integral i) (cbox a b)"
    and "e > 0"
    and k: "k \<in> Basis"
  obtains d where "gauge d"
    "\<forall>p1 p2. p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) \<and> d fine p2 \<longrightarrow>
        norm ((sum (\<lambda>(x,k). content k *\<^sub>R f x) p1 + sum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e"
proof -
  obtain \<gamma> where d: "gauge \<gamma>"
      "\<And>p. \<lbrakk>p tagged_division_of cbox a b; \<gamma> fine p\<rbrakk>
            \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) < e"
    using has_integralD[OF f \<open>e > 0\<close>] by metis
  { fix p1 p2
    assume tdiv1: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" and "\<gamma> fine p1"
    note p1=tagged_division_ofD[OF this(1)] 
    assume tdiv2: "p2 tagged_division_of (cbox a b) \<inter> {x. c \<le> x \<bullet> k}" and "\<gamma> fine p2"
    note p2=tagged_division_ofD[OF this(1)] 
    note tagged_division_Un_interval[OF tdiv1 tdiv2] 
    note p12 = tagged_division_ofD[OF this] this
    { fix a b
      assume ab: "(a, b) \<in> p1 \<inter> p2"
      have "(a, b) \<in> p1"
        using ab by auto
      obtain u v where uv: "b = cbox u v"
        using \<open>(a, b) \<in> p1\<close> p1(4) by moura
      have "b \<subseteq> {x. x\<bullet>k = c}"
        using ab p1(3)[of a b] p2(3)[of a b] by fastforce
      moreover
      have "interior {x::'a. x \<bullet> k = c} = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain x where x: "x \<in> interior {x::'a. x\<bullet>k = c}"
          by auto
        then obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball x \<epsilon> \<subseteq> {x. x \<bullet> k = c}"
          using mem_interior by metis
        have x: "x\<bullet>k = c"
          using x interior_subset by fastforce
        have *: "\<And>i. i \<in> Basis \<Longrightarrow> \<bar>(x - (x + (\<epsilon>/2) *\<^sub>R k)) \<bullet> i\<bar> = (if i = k then \<epsilon>/2 else 0)"
          using \<open>0 < \<epsilon>\<close> k by (auto simp: inner_simps inner_not_same_Basis)
        have "(\<Sum>i\<in>Basis. \<bar>(x - (x + (\<epsilon>/2 ) *\<^sub>R k)) \<bullet> i\<bar>) =
              (\<Sum>i\<in>Basis. (if i = k then \<epsilon>/2 else 0))"
          using "*" by (blast intro: sum.cong)
        also have "\<dots> < \<epsilon>"
          by (subst sum.delta) (use \<open>0 < \<epsilon>\<close> in auto)
        finally have "x + (\<epsilon>/2) *\<^sub>R k \<in> ball x \<epsilon>"
          unfolding mem_ball dist_norm by(rule le_less_trans[OF norm_le_l1])
        then have "x + (\<epsilon>/2) *\<^sub>R k \<in> {x. x\<bullet>k = c}"
          using \<epsilon> by auto
        then show False
          using \<open>0 < \<epsilon>\<close> x k by (auto simp: inner_simps)
      qed
      ultimately have "content b = 0"
        unfolding uv content_eq_0_interior
        using interior_mono by blast
      then have "content b *\<^sub>R f a = 0"
        by auto
    }
    then have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) =
               norm ((\<Sum>(x, k)\<in>p1 \<union> p2. content k *\<^sub>R f x) - i)"
      by (subst sum.union_inter_neutral) (auto simp: p1 p2)
    also have "\<dots> < e"
      using d(2) p12 by (simp add: fine_Un k \<open>\<gamma> fine p1\<close> \<open>\<gamma> fine p2\<close>)
    finally have "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) + (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - i) < e" .
   }
  then show ?thesis
    using d(1) that by auto
qed

lemma integrable_split [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on cbox a b"
      and k: "k \<in> Basis"
    shows "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<le> c})"   (is ?thesis1)
    and   "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"   (is ?thesis2)
proof -
  obtain y where y: "(f has_integral y) (cbox a b)"
    using f by blast
  define a' where "a' = (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i)*\<^sub>R i)"
  define b' where "b' = (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i)*\<^sub>R i)"
  have "\<exists>d. gauge d \<and>
            (\<forall>p1 p2. p1 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c} \<and> d fine p1 \<and>
                     p2 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c} \<and> d fine p2 \<longrightarrow>
                     norm ((\<Sum>(x,K) \<in> p1. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p2. content K *\<^sub>R f x)) < e)"
    if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
  with has_integral_separate_sides[OF y this k, of c]
  obtain d
    where "gauge d"
         and d: "\<And>p1 p2. \<lbrakk>p1 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c}; d fine p1;
                          p2 tagged_division_of cbox a b \<inter> {x. c \<le> x \<bullet> k}; d fine p2\<rbrakk>
                  \<Longrightarrow> norm ((\<Sum>(x,K)\<in>p1. content K *\<^sub>R f x) + (\<Sum>(x,K)\<in>p2. content K *\<^sub>R f x) - y) < e/2"
    by metis
  show ?thesis
    proof (rule_tac x=d in exI, clarsimp simp add: \<open>gauge d\<close>)
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p1"
                 "p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<le> c}" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof (rule fine_division_exists[OF \<open>gauge d\<close>, of a' b])
        fix p
        assume "p tagged_division_of cbox a' b" "d fine p"
        then show ?thesis
          using as norm_triangle_half_l[OF d[of p1 p] d[of p2 p]]
          unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
  with f show ?thesis1
    by (simp add: interval_split[OF k] integrable_Cauchy)
  have "\<exists>d. gauge d \<and>
            (\<forall>p1 p2. p1 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<ge> c} \<and> d fine p1 \<and>
                     p2 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<ge> c} \<and> d fine p2 \<longrightarrow>
                     norm ((\<Sum>(x,K) \<in> p1. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p2. content K *\<^sub>R f x)) < e)"
    if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
  with has_integral_separate_sides[OF y this k, of c]
  obtain d
    where "gauge d"
         and d: "\<And>p1 p2. \<lbrakk>p1 tagged_division_of cbox a b \<inter> {x. x \<bullet> k \<le> c}; d fine p1;
                          p2 tagged_division_of cbox a b \<inter> {x. c \<le> x \<bullet> k}; d fine p2\<rbrakk>
                  \<Longrightarrow> norm ((\<Sum>(x,K)\<in>p1. content K *\<^sub>R f x) + (\<Sum>(x,K)\<in>p2. content K *\<^sub>R f x) - y) < e/2"
    by metis
  show ?thesis
    proof (rule_tac x=d in exI, clarsimp simp add: \<open>gauge d\<close>)
      fix p1 p2
      assume as: "p1 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c}" "d fine p1"
                 "p2 tagged_division_of (cbox a b) \<inter> {x. x \<bullet> k \<ge> c}" "d fine p2"
      show "norm ((\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)) < e"
      proof (rule fine_division_exists[OF \<open>gauge d\<close>, of a b'])
        fix p
        assume "p tagged_division_of cbox a b'" "d fine p"
        then show ?thesis
          using as norm_triangle_half_l[OF d[of p p1] d[of p p2]]
          unfolding interval_split[OF k] b'_def[symmetric] a'_def[symmetric]
          by (auto simp add: algebra_simps)
      qed
    qed
  qed
  with f show ?thesis2
    by (simp add: interval_split[OF k] integrable_Cauchy)
qed

lemma operative_integralI:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "operative (lift_option (+)) (Some 0)
    (\<lambda>i. if f integrable_on i then Some (integral i f) else None)"
proof -
  interpret comm_monoid "lift_option plus" "Some (0::'b)"
    by (rule comm_monoid_lift_option)
      (rule add.comm_monoid_axioms)
  show ?thesis
  proof
    fix a b c
    fix k :: 'a
    assume k: "k \<in> Basis"
    show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) =
          lift_option (+) (if f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c} then Some (integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f) else None)
          (if f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k} then Some (integral (cbox a b \<inter> {x. c \<le> x \<bullet> k}) f) else None)"
    proof (cases "f integrable_on cbox a b")
      case True
      with k show ?thesis
        by (auto simp: integrable_split intro: integral_unique [OF has_integral_split[OF _ _ k]])
    next
    case False
      have "\<not> (f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<or> \<not> ( f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k})"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "f integrable_on cbox a b"
          unfolding integrable_on_def
          apply (rule_tac x="integral (cbox a b \<inter> {x. x \<bullet> k \<le> c}) f + integral (cbox a b \<inter> {x. x \<bullet> k \<ge> c}) f" in exI)
          apply (auto intro: has_integral_split[OF _ _ k])
          done
        then show False
          using False by auto
      qed
      then show ?thesis
        using False by auto
    qed
  next
    fix a b :: 'a
    assume "box a b = {}"
    then show "(if f integrable_on cbox a b then Some (integral (cbox a b) f) else None) = Some 0"
      using has_integral_null_eq
      by (auto simp: integrable_on_null content_eq_0_interior)
  qed
qed

subsection \<open>Bounds on the norm of Riemann sums and the integral itself\<close>

lemma dsum_bound:
  assumes p: "p division_of (cbox a b)"
    and "norm c \<le> e"
  shows "norm (sum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content(cbox a b)"
proof -
  have sumeq: "(\<Sum>i\<in>p. \<bar>content i\<bar>) = sum content p"
    by simp
  have e: "0 \<le> e"
    using assms(2) norm_ge_zero order_trans by blast
  have "norm (sum (\<lambda>l. content l *\<^sub>R c) p) \<le> (\<Sum>i\<in>p. norm (content i *\<^sub>R c))"
    using norm_sum by blast
  also have "...  \<le> e * (\<Sum>i\<in>p. \<bar>content i\<bar>)"
    by (simp add: sum_distrib_left[symmetric] mult.commute assms(2) mult_right_mono sum_nonneg)
  also have "... \<le> e * content (cbox a b)"
    by (metis additive_content_division p eq_iff sumeq)
  finally show ?thesis .
qed

lemma rsum_bound:
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<forall>x\<in>cbox a b. norm (f x) \<le> e"
    shows "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> e * content (cbox a b)"
proof (cases "cbox a b = {}")
  case True show ?thesis
    using p unfolding True tagged_division_of_trivial by auto
next
  case False
  then have e: "e \<ge> 0"
    by (meson ex_in_conv assms(2) norm_ge_zero order_trans)
  have sum_le: "sum (content \<circ> snd) p \<le> content (cbox a b)"
    unfolding additive_content_tagged_division[OF p, symmetric] split_def
    by (auto intro: eq_refl)
  have con: "\<And>xk. xk \<in> p \<Longrightarrow> 0 \<le> content (snd xk)"
    using tagged_division_ofD(4) [OF p] content_pos_le
    by force
  have "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> (\<Sum>i\<in>p. norm (case i of (x, k) \<Rightarrow> content k *\<^sub>R f x))"
    by (rule norm_sum)
  also have "...  \<le> e * content (cbox a b)"
  proof -
    have "\<And>xk. xk \<in> p \<Longrightarrow> norm (f (fst xk)) \<le> e"
      using assms(2) p tag_in_interval by force
    moreover have "(\<Sum>i\<in>p. \<bar>content (snd i)\<bar> * e) \<le> e * content (cbox a b)"
      unfolding sum_distrib_right[symmetric]
      using con sum_le by (auto simp: mult.commute intro: mult_left_mono [OF _ e])
    ultimately show ?thesis
      unfolding split_def norm_scaleR
      by (metis (no_types, lifting) mult_left_mono[OF _ abs_ge_zero]   order_trans[OF sum_mono])
  qed
  finally show ?thesis .
qed

lemma rsum_diff_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e"
  shows "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - sum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le>
         e * content (cbox a b)"
  using order_trans[OF _ rsum_bound[OF assms]]
  by (simp add: split_def scaleR_diff_right sum_subtractf eq_refl)

lemma has_integral_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and f: "(f has_integral i) (cbox a b)"
      and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "norm i - B * content (cbox a b) > 0"
    by auto
  with f[unfolded has_integral]
  obtain \<gamma> where "gauge \<gamma>" and \<gamma>:
    "\<And>p. \<lbrakk>p tagged_division_of cbox a b; \<gamma> fine p\<rbrakk>
          \<Longrightarrow> norm ((\<Sum>(x, K)\<in>p. content K *\<^sub>R f x) - i) < norm i - B * content (cbox a b)"
    by metis
  then obtain p where p: "p tagged_division_of cbox a b" and "\<gamma> fine p"
    using fine_division_exists by blast
  have "\<And>s B. norm s \<le> B \<Longrightarrow> \<not> norm (s - i) < norm i - B"
    unfolding not_less
    by (metis diff_left_mono dist_commute dist_norm norm_triangle_ineq2 order_trans)
  then show False
    using \<gamma> [OF p \<open>\<gamma> fine p\<close>] rsum_bound[OF p] assms by metis
qed

corollary integrable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and "f integrable_on (cbox a b)"
      and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
    shows "norm (integral (cbox a b) f) \<le> B * content (cbox a b)"
by (metis integrable_integral has_integral_bound assms)


subsection \<open>Similar theorems about relationship among components\<close>

lemma rsum_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<And>x. x \<in> cbox a b \<Longrightarrow> (f x)\<bullet>i \<le> (g x)\<bullet>i"
    shows "(\<Sum>(x, K)\<in>p. content K *\<^sub>R f x) \<bullet> i \<le> (\<Sum>(x, K)\<in>p. content K *\<^sub>R g x) \<bullet> i"
unfolding inner_sum_left
proof (rule sum_mono, clarify)
  fix x K
  assume ab: "(x, K) \<in> p"
  with p obtain u v where K: "K = cbox u v"
    by blast
  then show "(content K *\<^sub>R f x) \<bullet> i \<le> (content K *\<^sub>R g x) \<bullet> i"
    by (metis ab assms inner_scaleR_left measure_nonneg mult_left_mono tag_in_interval)
qed

lemma has_integral_component_le:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
  assumes "(f has_integral i) S" "(g has_integral j) S"
    and f_le_g: "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  have ik_le_jk: "i\<bullet>k \<le> j\<bullet>k"
    if f_i: "(f has_integral i) (cbox a b)"
    and g_j: "(g has_integral j) (cbox a b)"
    and le: "\<forall>x\<in>cbox a b. (f x)\<bullet>k \<le> (g x)\<bullet>k"
    for a b i and j :: 'b and f g :: "'a \<Rightarrow> 'b"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have *: "0 < (i\<bullet>k - j\<bullet>k) / 3"
      by auto
    obtain \<gamma>1 where "gauge \<gamma>1" 
      and \<gamma>1: "\<And>p. \<lbrakk>p tagged_division_of cbox a b; \<gamma>1 fine p\<rbrakk>
                \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) < (i \<bullet> k - j \<bullet> k) / 3"
      using f_i[unfolded has_integral,rule_format,OF *] by fastforce 
    obtain \<gamma>2 where "gauge \<gamma>2" 
      and \<gamma>2: "\<And>p. \<lbrakk>p tagged_division_of cbox a b; \<gamma>2 fine p\<rbrakk>
                \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - j) < (i \<bullet> k - j \<bullet> k) / 3"
      using g_j[unfolded has_integral,rule_format,OF *] by fastforce 
    obtain p where p: "p tagged_division_of cbox a b" and "\<gamma>1 fine p" "\<gamma>2 fine p"
       using fine_division_exists[OF gauge_Int[OF \<open>gauge \<gamma>1\<close> \<open>gauge \<gamma>2\<close>], of a b] unfolding fine_Int
       by metis
    then have "\<bar>((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
         "\<bar>((\<Sum>(x, k)\<in>p. content k *\<^sub>R g x) - j) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
      using le_less_trans[OF Basis_le_norm[OF k]] k \<gamma>1 \<gamma>2 by metis+ 
    then show False
      unfolding inner_simps
      using rsum_component_le[OF p] le
      by (fastforce simp add: abs_real_def split: if_split_asm)
  qed
  show ?thesis
  proof (cases "\<exists>a b. S = cbox a b")
    case True
    with ik_le_jk assms show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "\<not> i\<bullet>k \<le> j\<bullet>k"
      then have ij: "(i\<bullet>k - j\<bullet>k) / 3 > 0"
        by auto
      obtain B1 where "0 < B1" 
           and B1: "\<And>a b. ball 0 B1 \<subseteq> cbox a b \<Longrightarrow>
                    \<exists>z. ((\<lambda>x. if x \<in> S then f x else 0) has_integral z) (cbox a b) \<and>
                        norm (z - i) < (i \<bullet> k - j \<bullet> k) / 3"
        using has_integral_altD[OF _ False ij] assms by blast
      obtain B2 where "0 < B2" 
           and B2: "\<And>a b. ball 0 B2 \<subseteq> cbox a b \<Longrightarrow>
                    \<exists>z. ((\<lambda>x. if x \<in> S then g x else 0) has_integral z) (cbox a b) \<and>
                        norm (z - j) < (i \<bullet> k - j \<bullet> k) / 3"
        using has_integral_altD[OF _ False ij] assms by blast
      have "bounded (ball 0 B1 \<union> ball (0::'a) B2)"
        unfolding bounded_Un by(rule conjI bounded_ball)+
      from bounded_subset_cbox_symmetric[OF this] 
      obtain a b::'a where ab: "ball 0 B1 \<subseteq> cbox a b" "ball 0 B2 \<subseteq> cbox a b"
        by (meson Un_subset_iff)
      then obtain w1 w2 where int_w1: "((\<lambda>x. if x \<in> S then f x else 0) has_integral w1) (cbox a b)"
                        and norm_w1:  "norm (w1 - i) < (i \<bullet> k - j \<bullet> k) / 3"
                        and int_w2: "((\<lambda>x. if x \<in> S then g x else 0) has_integral w2) (cbox a b)"
                        and norm_w2: "norm (w2 - j) < (i \<bullet> k - j \<bullet> k) / 3"
        using B1 B2 by blast
      have *: "\<And>w1 w2 j i::real .\<bar>w1 - i\<bar> < (i - j) / 3 \<Longrightarrow> \<bar>w2 - j\<bar> < (i - j) / 3 \<Longrightarrow> w1 \<le> w2 \<Longrightarrow> False"
        by (simp add: abs_real_def split: if_split_asm)
      have "\<bar>(w1 - i) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
           "\<bar>(w2 - j) \<bullet> k\<bar> < (i \<bullet> k - j \<bullet> k) / 3"
        using Basis_le_norm k le_less_trans norm_w1 norm_w2 by blast+
      moreover
      have "w1\<bullet>k \<le> w2\<bullet>k"
        using ik_le_jk int_w1 int_w2 f_le_g by auto
      ultimately show False
        unfolding inner_simps by(rule *)
    qed
  qed
qed

lemma integral_component_le:
  fixes g f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on S" "g integrable_on S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "(integral S f)\<bullet>k \<le> (integral S g)\<bullet>k"
  using has_integral_component_le assms by blast

lemma has_integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(1) has_integral_0 assms(2)]
  using assms(3-)
  by auto

lemma integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> (integral S f)\<bullet>k"
proof (cases "f integrable_on S")
  case True show ?thesis
    using True assms has_integral_component_nonneg by blast
next
  case False then show ?thesis by (simp add: not_integrable_integral)
qed

lemma has_integral_component_neg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> 0"
  shows "i\<bullet>k \<le> 0"
  using has_integral_component_le[OF assms(1,2) has_integral_0] assms(2-)
  by auto

lemma has_integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> i\<bullet>k"
  using has_integral_component_le[OF assms(3) has_integral_const assms(1),of "(\<Sum>i\<in>Basis. B *\<^sub>R i)::'b"] assms(2-)
  by (auto simp add: field_simps)

lemma has_integral_component_ubound:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "i\<bullet>k \<le> B * content (cbox a b)"
  using has_integral_component_le[OF assms(3,1) has_integral_const, of "\<Sum>i\<in>Basis. B *\<^sub>R i"] assms(2-)
  by (auto simp add: field_simps)

lemma integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> (integral(cbox a b) f)\<bullet>k"
  using assms has_integral_component_lbound by blast

lemma integral_component_lbound_real:
  assumes "f integrable_on {a ::real..b}"
    and "\<forall>x\<in>{a..b}. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content {a..b} \<le> (integral {a..b} f)\<bullet>k"
  using assms
  by (metis box_real(2) integral_component_lbound)

lemma integral_component_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral (cbox a b) f)\<bullet>k \<le> B * content (cbox a b)"
  using assms has_integral_component_ubound by blast

lemma integral_component_ubound_real:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a..b}"
    and "\<forall>x\<in>{a..b}. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral {a..b} f)\<bullet>k \<le> B * content {a..b}"
  using assms
  by (metis box_real(2) integral_component_ubound)

subsection \<open>Uniform limit of integrable functions is integrable\<close>

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by (subst(asm) real_arch_inverse)


lemma integrable_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
  shows "f integrable_on cbox a b"
proof (cases "content (cbox a b) > 0")
  case False then show ?thesis
    using has_integral_null by (simp add: content_lt_nz integrable_on_def)
next
  case True
  have "1 / (real n + 1) > 0" for n
    by auto
  then have "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> 1 / (real n + 1)) \<and> g integrable_on cbox a b" for n
    using assms by blast
  then obtain g where g_near_f: "\<And>n x. x \<in> cbox a b \<Longrightarrow> norm (f x - g n x) \<le> 1 / (real n + 1)"
                  and int_g: "\<And>n. g n integrable_on cbox a b"
    by metis
  then obtain h where h: "\<And>n. (g n has_integral h n) (cbox a b)"
    unfolding integrable_on_def by metis
  have "Cauchy h"
    unfolding Cauchy_def
  proof clarify
    fix e :: real
    assume "e>0"
    then have "e/4 / content (cbox a b) > 0"
      using True by (auto simp: field_simps)
    then obtain M where "M \<noteq> 0" and M: "1 / (real M) < e/4 / content (cbox a b)"
      by (metis inverse_eq_divide real_arch_inverse)
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (h m) (h n) < e"
    proof (rule exI [where x=M], clarify)
      fix m n
      assume m: "M \<le> m" and n: "M \<le> n"
      have "e/4>0" using \<open>e>0\<close> by auto
      then obtain gm gn where "gauge gm" "gauge gn"
              and gm: "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> gm fine \<D> 
                            \<Longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g m x) - h m) < e/4"
              and gn: "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> gn fine \<D> \<Longrightarrow>
                      norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g n x) - h n) < e/4"
        using h[unfolded has_integral] by meson
      then obtain \<D> where \<D>: "\<D> tagged_division_of cbox a b" "(\<lambda>x. gm x \<inter> gn x) fine \<D>"
        by (metis (full_types) fine_division_exists gauge_Int)
      have triangle3: "norm (i1 - i2) < e"
        if no: "norm(s2 - s1) \<le> e/2" "norm (s1 - i1) < e/4" "norm (s2 - i2) < e/4" for s1 s2 i1 and i2::'b
      proof -
        have "norm (i1 - i2) \<le> norm (i1 - s1) + norm (s1 - s2) + norm (s2 - i2)"
          using norm_triangle_ineq[of "i1 - s1" "s1 - i2"]
          using norm_triangle_ineq[of "s1 - s2" "s2 - i2"]
          by (auto simp: algebra_simps)
        also have "\<dots> < e"
          using no by (auto simp: algebra_simps norm_minus_commute)
        finally show ?thesis .
      qed
      have finep: "gm fine \<D>" "gn fine \<D>"
        using fine_Int \<D>  by auto
      have norm_le: "norm (g n x - g m x) \<le> 2 / real M" if x: "x \<in> cbox a b" for x
      proof -
        have "norm (f x - g n x) + norm (f x - g m x) \<le> 1 / (real n + 1) + 1 / (real m + 1)"          
          using g_near_f[OF x, of n] g_near_f[OF x, of m] by simp
        also have "\<dots> \<le> 1 / (real M) + 1 / (real M)"
          using \<open>M \<noteq> 0\<close> m n by (intro add_mono; force simp: field_split_simps)
        also have "\<dots> = 2 / real M"
          by auto
        finally show "norm (g n x - g m x) \<le> 2 / real M"
          using norm_triangle_le[of "g n x - f x" "f x - g m x" "2 / real M"]
          by (auto simp: algebra_simps simp add: norm_minus_commute)
      qed
      have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g n x) - (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g m x)) \<le> 2 / real M * content (cbox a b)"
        by (blast intro: norm_le rsum_diff_bound[OF \<D>(1), where e="2 / real M"])
      also have "... \<le> e/2"
        using M True
        by (auto simp: field_simps)
      finally have le_e2: "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g n x) - (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g m x)) \<le> e/2" .
      then show "dist (h m) (h n) < e"
        unfolding dist_norm using gm gn \<D> finep by (auto intro!: triangle3)
    qed
  qed
  then obtain s where s: "h \<longlonglongrightarrow> s"
    using convergent_eq_Cauchy[symmetric] by blast
  show ?thesis
    unfolding integrable_on_def has_integral
  proof (rule_tac x=s in exI, clarify)
    fix e::real
    assume e: "0 < e"
    then have "e/3 > 0" by auto
    then obtain N1 where N1: "\<forall>n\<ge>N1. norm (h n - s) < e/3"
      using LIMSEQ_D [OF s] by metis
    from e True have "e/3 / content (cbox a b) > 0"
      by (auto simp: field_simps)
    then obtain N2 :: nat
         where "N2 \<noteq> 0" and N2: "1 / (real N2) < e/3 / content (cbox a b)"
      by (metis inverse_eq_divide real_arch_inverse)
    obtain g' where "gauge g'"
            and g': "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> g' fine \<D> \<Longrightarrow>
                    norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g (N1 + N2) x) - h (N1 + N2)) < e/3"
      by (metis h has_integral \<open>e/3 > 0\<close>)
    have *: "norm (sf - s) < e" 
        if no: "norm (sf - sg) \<le> e/3" "norm(h - s) < e/3" "norm (sg - h) < e/3" for sf sg h
    proof -
      have "norm (sf - s) \<le> norm (sf - sg) + norm (sg - h) + norm (h - s)"
        using norm_triangle_ineq[of "sf - sg" "sg - s"]
        using norm_triangle_ineq[of "sg -  h" " h - s"]
        by (auto simp: algebra_simps)
      also have "\<dots> < e"
        using no by (auto simp: algebra_simps norm_minus_commute)
      finally show ?thesis .
    qed
    { fix \<D>
      assume ptag: "\<D> tagged_division_of (cbox a b)" and "g' fine \<D>"
      then have norm_less: "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g (N1 + N2) x) - h (N1 + N2)) < e/3"
        using g' by blast
      have "content (cbox a b) < e/3 * (of_nat N2)"
        using \<open>N2 \<noteq> 0\<close> N2 using True by (auto simp: field_split_simps)
      moreover have "e/3 * of_nat N2 \<le> e/3 * (of_nat (N1 + N2) + 1)"
        using \<open>e>0\<close> by auto
      ultimately have "content (cbox a b) < e/3 * (of_nat (N1 + N2) + 1)"
        by linarith
      then have le_e3: "1 / (real (N1 + N2) + 1) * content (cbox a b) \<le> e/3"
        unfolding inverse_eq_divide
        by (auto simp: field_simps)
      have ne3: "norm (h (N1 + N2) - s) < e/3"
        using N1 by auto
      have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R g (N1 + N2) x))
            \<le> 1 / (real (N1 + N2) + 1) * content (cbox a b)"
        by (blast intro: g_near_f rsum_diff_bound[OF ptag])
      then have "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - s) < e"
        by (rule *[OF order_trans [OF _ le_e3] ne3 norm_less])
    }
    then show "\<exists>d. gauge d \<and>
             (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> d fine \<D> \<longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - s) < e)"
      by (blast intro: g' \<open>gauge g'\<close>)
  qed
qed

lemmas integrable_uniform_limit_real = integrable_uniform_limit [where 'a=real, simplified]


subsection \<open>Negligible sets\<close>

definition "negligible (s:: 'a::euclidean_space set) \<longleftrightarrow>
  (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) (cbox a b))"


subsubsection \<open>Negligibility of hyperplane\<close>

lemma content_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "0 < e"
    and k: "k \<in> Basis"
  obtains d where "0 < d" and "content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) < e"
proof cases
  assume *: "a \<bullet> k \<le> c \<and> c \<le> b \<bullet> k \<and> (\<forall>j\<in>Basis. a \<bullet> j \<le> b \<bullet> j)"
  define a' where "a' d = (\<Sum>j\<in>Basis. (if j = k then max (a\<bullet>j) (c - d) else a\<bullet>j) *\<^sub>R j)" for d
  define b' where "b' d = (\<Sum>j\<in>Basis. (if j = k then min (b\<bullet>j) (c + d) else b\<bullet>j) *\<^sub>R j)" for d

  have "((\<lambda>d. \<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) \<longlongrightarrow> (\<Prod>j\<in>Basis. (b' 0 - a' 0) \<bullet> j)) (at_right 0)"
    by (auto simp: b'_def a'_def intro!: tendsto_min tendsto_max tendsto_eq_intros)
  also have "(\<Prod>j\<in>Basis. (b' 0 - a' 0) \<bullet> j) = 0"
    using k *
    by (intro prod_zero bexI[OF _ k])
       (auto simp: b'_def a'_def inner_diff inner_sum_left inner_not_same_Basis intro!: sum.cong)
  also have "((\<lambda>d. \<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) \<longlongrightarrow> 0) (at_right 0) =
    ((\<lambda>d. content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d})) \<longlongrightarrow> 0) (at_right 0)"
  proof (intro tendsto_cong eventually_at_rightI)
    fix d :: real assume d: "d \<in> {0<..<1}"
    have "cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d} = cbox (a' d) (b' d)" for d
      using * d k by (auto simp add: cbox_def set_eq_iff Int_def ball_conj_distrib abs_diff_le_iff a'_def b'_def)
    moreover have "j \<in> Basis \<Longrightarrow> a' d \<bullet> j \<le> b' d \<bullet> j" for j
      using * d k by (auto simp: a'_def b'_def)
    ultimately show "(\<Prod>j\<in>Basis. (b' d - a' d) \<bullet> j) = content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d})"
      by simp
  qed simp
  finally have "((\<lambda>d. content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) \<longlongrightarrow> 0) (at_right 0)" .
  from order_tendstoD(2)[OF this \<open>0<e\<close>]
  obtain d' where "0 < d'" and d': "\<And>y. y > 0 \<Longrightarrow> y < d' \<Longrightarrow> content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> y}) < e"
    by (subst (asm) eventually_at_right[of _ 1]) auto
  show ?thesis
    by (rule that[of "d'/2"], insert \<open>0<d'\<close> d'[of "d'/2"], auto)
next
  assume *: "\<not> (a \<bullet> k \<le> c \<and> c \<le> b \<bullet> k \<and> (\<forall>j\<in>Basis. a \<bullet> j \<le> b \<bullet> j))"
  then have "(\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j) \<or> (c < a \<bullet> k \<or> b \<bullet> k < c)"
    by (auto simp: not_le)
  show thesis
  proof cases
    assume "\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j"
    then have [simp]: "cbox a b = {}"
      using box_ne_empty(1)[of a b] by auto
    show ?thesis
      by (rule that[of 1]) (simp_all add: \<open>0<e\<close>)
  next
    assume "\<not> (\<exists>j\<in>Basis. b \<bullet> j < a \<bullet> j)"
    with * have "c < a \<bullet> k \<or> b \<bullet> k < c"
      by auto
    then show thesis
    proof
      assume c: "c < a \<bullet> k"
      moreover have "x \<in> cbox a b \<Longrightarrow> c \<le> x \<bullet> k" for x
        using k c by (auto simp: cbox_def)
      ultimately have "cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> (a \<bullet> k - c)/2} = {}"
        using k by (auto simp: cbox_def)
      with \<open>0<e\<close> c that[of "(a \<bullet> k - c)/2"] show ?thesis
        by auto
    next
      assume c: "b \<bullet> k < c"
      moreover have "x \<in> cbox a b \<Longrightarrow> x \<bullet> k \<le> c" for x
        using k c by (auto simp: cbox_def)
      ultimately have "cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> (c - b \<bullet> k)/2} = {}"
        using k by (auto simp: cbox_def)
      with \<open>0<e\<close> c that[of "(c - b \<bullet> k)/2"] show ?thesis
        by auto
    qed
  qed
qed


proposition negligible_standard_hyperplane[intro]:
  fixes k :: "'a::euclidean_space"
  assumes k: "k \<in> Basis"
  shows "negligible {x. x\<bullet>k = c}"
  unfolding negligible_def has_integral
proof clarsimp
  fix a b and e::real assume "e > 0"
  with k obtain d where "0 < d" and d: "content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) < e"
    by (metis content_doublesplit)
  let ?i = "indicator {x::'a. x\<bullet>k = c} :: 'a\<Rightarrow>real"
  show "\<exists>\<gamma>. gauge \<gamma> \<and>
           (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                 \<bar>\<Sum>(x,K) \<in> \<D>. content K * ?i x\<bar> < e)"
  proof (intro exI, safe)
    show "gauge (\<lambda>x. ball x d)"
      using \<open>0 < d\<close> by blast
  next
    fix \<D>
    assume p: "\<D> tagged_division_of (cbox a b)" "(\<lambda>x. ball x d) fine \<D>"
    have "content L = content (L \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})" 
      if "(x, L) \<in> \<D>" "?i x \<noteq> 0" for x L
    proof -
      have xk: "x\<bullet>k = c"
        using that by (simp add: indicator_def split: if_split_asm)
      have "L \<subseteq> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}"
      proof 
        fix y
        assume y: "y \<in> L"
        have "L \<subseteq> ball x d"
          using p(2) that(1) by auto
        then have "norm (x - y) < d"
          by (simp add: dist_norm subset_iff y)
        then have "\<bar>(x - y) \<bullet> k\<bar> < d"
          using k norm_bound_Basis_lt by blast
        then show "y \<in> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}"
          unfolding inner_simps xk by auto
      qed 
      then show "content L = content (L \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})"
        by (metis inf.orderE)
    qed
    then have *: "(\<Sum>(x,K)\<in>\<D>. content K * ?i x) = (\<Sum>(x,K)\<in>\<D>. content (K \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) *\<^sub>R ?i x)"
      by (force simp add: split_paired_all intro!: sum.cong [OF refl])
    note p'= tagged_division_ofD[OF p(1)] and p''=division_of_tagged_division[OF p(1)]
    have "(\<Sum>(x,K)\<in>\<D>. content (K \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * indicator {x. x \<bullet> k = c} x) < e"
    proof -
      have "(\<Sum>(x,K)\<in>\<D>. content (K \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) \<le> (\<Sum>(x,K)\<in>\<D>. content (K \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}))"
        by (force simp add: indicator_def intro!: sum_mono)
      also have "\<dots> < e"
      proof (subst sum.over_tagged_division_lemma[OF p(1)])
        fix u v::'a
        assume "box u v = {}"
        then have *: "content (cbox u v) = 0"
          unfolding content_eq_0_interior by simp
        have "cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<subseteq> cbox u v"
          by auto
        then have "content (cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<le> content (cbox u v)"
          unfolding interval_doublesplit[OF k] by (rule content_subset)
        then show "content (cbox u v \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = 0"
          unfolding * interval_doublesplit[OF k]
          by (blast intro: antisym)
      next
        have "(\<Sum>l\<in>snd ` \<D>. content (l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) =
          sum content ((\<lambda>l. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})`{l\<in>snd ` \<D>. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}})"
        proof (subst (2) sum.reindex_nontrivial)
          fix x y assume "x \<in> {l \<in> snd ` \<D>. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}" "y \<in> {l \<in> snd ` \<D>. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}"
            "x \<noteq> y" and eq: "x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} = y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}"
          then obtain x' y' where "(x', x) \<in> \<D>" "x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}" "(y', y) \<in> \<D>" "y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}"
            by (auto)
          from p'(5)[OF \<open>(x', x) \<in> \<D>\<close> \<open>(y', y) \<in> \<D>\<close>] \<open>x \<noteq> y\<close> have "interior (x \<inter> y) = {}"
            by auto
          moreover have "interior ((x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) \<inter> (y \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) \<subseteq> interior (x \<inter> y)"
            by (auto intro: interior_mono)
          ultimately have "interior (x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = {}"
            by (auto simp: eq)
          then show "content (x \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) = 0"
            using p'(4)[OF \<open>(x', x) \<in> \<D>\<close>] by (auto simp: interval_doublesplit[OF k] content_eq_0_interior simp del: interior_Int)
        qed (insert p'(1), auto intro!: sum.mono_neutral_right)
        also have "\<dots> \<le> norm (\<Sum>l\<in>(\<lambda>l. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})`{l\<in>snd ` \<D>. l \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d} \<noteq> {}}. content l *\<^sub>R 1::real)"
          by simp
        also have "\<dots> \<le> 1 * content (cbox a b \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})"
          using division_doublesplit[OF p'' k, unfolded interval_doublesplit[OF k]]
          unfolding interval_doublesplit[OF k] by (intro dsum_bound) auto
        also have "\<dots> < e"
          using d by simp
        finally show "(\<Sum>K\<in>snd ` \<D>. content (K \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d})) < e" .
      qed
      finally show "(\<Sum>(x, K)\<in>\<D>. content (K \<inter> {x. \<bar>x \<bullet> k - c\<bar> \<le> d}) * ?i x) < e" .
    qed
    then show "\<bar>\<Sum>(x, K)\<in>\<D>. content K * ?i x\<bar> < e"
      unfolding *  by (simp add: sum_nonneg split: prod.split)
  qed
qed

corollary negligible_standard_hyperplane_cart:
  fixes k :: "'a::finite"
  shows "negligible {x. x$k = (0::real)}"
  by (simp add: cart_eq_inner_axis negligible_standard_hyperplane)


subsubsection \<open>Hence the main theorem about negligible sets\<close>


lemma has_integral_negligible_cbox:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and 0: "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
  unfolding has_integral
proof clarify
  fix e::real
  assume "e > 0"
  then have nn_gt0: "e/2 / ((real n+1) * (2 ^ n)) > 0" for n
    by simp
  then have "\<exists>\<gamma>. gauge \<gamma> \<and>
                 (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                      \<bar>\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R indicator S x\<bar>
                      < e/2 / ((real n + 1) * 2 ^ n))" for n
    using negs [unfolded negligible_def has_integral] by auto
  then obtain \<gamma> where 
    gd: "\<And>n. gauge (\<gamma> n)"
    and \<gamma>: "\<And>n \<D>. \<lbrakk>\<D> tagged_division_of cbox a b; \<gamma> n fine \<D>\<rbrakk>
                  \<Longrightarrow> \<bar>\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R indicator S x\<bar> < e/2 / ((real n + 1) * 2 ^ n)"
    by metis
  show "\<exists>\<gamma>. gauge \<gamma> \<and>
             (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> \<longrightarrow>
                  norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - 0) < e)"
  proof (intro exI, safe)
    show "gauge (\<lambda>x. \<gamma> (nat \<lfloor>norm (f x)\<rfloor>) x)"
      using gd by (auto simp: gauge_def)

    show "norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - 0) < e"
      if "\<D> tagged_division_of (cbox a b)" "(\<lambda>x. \<gamma> (nat \<lfloor>norm (f x)\<rfloor>) x) fine \<D>" for \<D>
    proof (cases "\<D> = {}")
      case True with \<open>0 < e\<close> show ?thesis by simp
    next
      case False
      obtain N where "Max ((\<lambda>(x, K). norm (f x)) ` \<D>) \<le> real N"
        using real_arch_simple by blast
      then have N: "\<And>x. x \<in> (\<lambda>(x, K). norm (f x)) ` \<D> \<Longrightarrow> x \<le> real N"
        by (meson Max_ge that(1) dual_order.trans finite_imageI tagged_division_of_finite)
      have "\<forall>i. \<exists>q. q tagged_division_of (cbox a b) \<and> (\<gamma> i) fine q \<and> (\<forall>(x,K) \<in> \<D>. K \<subseteq> (\<gamma> i) x \<longrightarrow> (x, K) \<in> q)"
        by (auto intro: tagged_division_finer[OF that(1) gd])
      from choice[OF this] 
      obtain q where q: "\<And>n. q n tagged_division_of cbox a b"
                        "\<And>n. \<gamma> n fine q n"
                        "\<And>n x K. \<lbrakk>(x, K) \<in> \<D>; K \<subseteq> \<gamma> n x\<rbrakk> \<Longrightarrow> (x, K) \<in> q n"
        by fastforce
      have "finite \<D>"
        using that(1) by blast
      then have sum_le_inc: "\<lbrakk>finite T; \<And>x y. (x,y) \<in> T \<Longrightarrow> (0::real) \<le> g(x,y);
                      \<And>y. y\<in>\<D> \<Longrightarrow> \<exists>x. (x,y) \<in> T \<and> f(y) \<le> g(x,y)\<rbrakk> \<Longrightarrow> sum f \<D> \<le> sum g T" for f g T
        by (rule sum_le_included[of \<D> T g snd f]; force)
      have "norm (\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) \<le> (\<Sum>(x,K) \<in> \<D>. norm (content K *\<^sub>R f x))"
        unfolding split_def by (rule norm_sum)
      also have "... \<le> (\<Sum>(i, j) \<in> Sigma {..N + 1} q.
                          (real i + 1) * (case j of (x, K) \<Rightarrow> content K *\<^sub>R indicator S x))"
      proof (rule sum_le_inc, safe)
        show "finite (Sigma {..N+1} q)"
          by (meson finite_SigmaI finite_atMost tagged_division_of_finite q(1)) 
      next
        fix x K
        assume xk: "(x, K) \<in> \<D>"
        define n where "n = nat \<lfloor>norm (f x)\<rfloor>"
        have *: "norm (f x) \<in> (\<lambda>(x, K). norm (f x)) ` \<D>"
          using xk by auto
        have nfx: "real n \<le> norm (f x)" "norm (f x) \<le> real n + 1"
          unfolding n_def by auto
        then have "n \<in> {0..N + 1}"
          using N[OF *] by auto
        moreover have "K \<subseteq> \<gamma> (nat \<lfloor>norm (f x)\<rfloor>) x"
          using that(2) xk by auto
        moreover then have "(x, K) \<in> q (nat \<lfloor>norm (f x)\<rfloor>)"
          by (simp add: q(3) xk)
        moreover then have "(x, K) \<in> q n"
          using n_def by blast
        moreover
        have "norm (content K *\<^sub>R f x) \<le> (real n + 1) * (content K * indicator S x)"
        proof (cases "x \<in> S")
          case False
          then show ?thesis by (simp add: 0)
        next
          case True
          have *: "content K \<ge> 0"
            using tagged_division_ofD(4)[OF that(1) xk] by auto
          moreover have "content K * norm (f x) \<le> content K * (real n + 1)"
            by (simp add: mult_left_mono nfx(2))
          ultimately show ?thesis
            using nfx True by (auto simp: field_simps)
        qed
        ultimately show "\<exists>y. (y, x, K) \<in> (Sigma {..N + 1} q) \<and> norm (content K *\<^sub>R f x) \<le>
          (real y + 1) * (content K *\<^sub>R indicator S x)"
          by force
      qed auto
      also have "... = (\<Sum>i\<le>N + 1. \<Sum>j\<in>q i. (real i + 1) * (case j of (x, K) \<Rightarrow> content K *\<^sub>R indicator S x))"
        using q(1) by (intro sum_Sigma_product [symmetric]) auto
      also have "... \<le> (\<Sum>i\<le>N + 1. (real i + 1) * \<bar>\<Sum>(x,K) \<in> q i. content K *\<^sub>R indicator S x\<bar>)"
        by (rule sum_mono) (simp add: sum_distrib_left [symmetric])
      also have "... \<le> (\<Sum>i\<le>N + 1. e/2/2 ^ i)"
      proof (rule sum_mono)
        show "(real i + 1) * \<bar>\<Sum>(x,K) \<in> q i. content K *\<^sub>R indicator S x\<bar> \<le> e/2/2 ^ i"
          if "i \<in> {..N + 1}" for i
          using \<gamma>[of "q i" i] q by (simp add: divide_simps mult.left_commute)
      qed
      also have "... = e/2 * (\<Sum>i\<le>N + 1. (1/2) ^ i)"
        unfolding sum_distrib_left by (metis divide_inverse inverse_eq_divide power_one_over)
      also have "\<dots> < e/2 * 2"
      proof (rule mult_strict_left_mono)
        have "sum (power (1/2)) {..N + 1} = sum (power (1/2::real)) {..<N + 2}"
          using lessThan_Suc_atMost by auto
        also have "... < 2"
          by (auto simp: geometric_sum)
        finally show "sum (power (1/2::real)) {..N + 1} < 2" .
      qed (use \<open>0 < e\<close> in auto)
      finally  show ?thesis by auto
    qed
  qed
qed


proposition has_integral_negligible:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and "\<And>x. x \<in> (T - S) \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) T"
proof (cases "\<exists>a b. T = cbox a b")
  case True
  then have "((\<lambda>x. if x \<in> T then f x else 0) has_integral 0) T"
    using assms by (auto intro!: has_integral_negligible_cbox)
  then show ?thesis
    by (rule has_integral_eq [rotated]) auto
next
  case False
  let ?f = "(\<lambda>x. if x \<in> T then f x else 0)"
  have "((\<lambda>x. if x \<in> T then f x else 0) has_integral 0) T"
    apply (auto simp: False has_integral_alt [of ?f])
    apply (rule_tac x=1 in exI, auto)
    apply (rule_tac x=0 in exI, simp add: has_integral_negligible_cbox [OF negs] assms)
    done
  then show ?thesis
    by (rule_tac f="?f" in has_integral_eq) auto
qed

lemma
  assumes "negligible S"
  shows integrable_negligible: "f integrable_on S" and integral_negligible: "integral S f = 0"
  using has_integral_negligible [OF assms]
  by (auto simp: has_integral_iff)

lemma has_integral_spike:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible S"
    and gf: "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and fint: "(f has_integral y) T"
  shows "(g has_integral y) T"
proof -
  have *: "(g has_integral y) (cbox a b)"
       if "(f has_integral y) (cbox a b)" "\<forall>x \<in> cbox a b - S. g x = f x" for a b f and g:: "'b \<Rightarrow> 'a" and y
  proof -
    have "((\<lambda>x. f x + (g x - f x)) has_integral (y + 0)) (cbox a b)"
      using that by (intro has_integral_add has_integral_negligible) (auto intro!: \<open>negligible S\<close>)
    then show ?thesis
      by auto
  qed
  have \<section>: "\<And>a b z. \<lbrakk>\<And>x. x \<in> T \<and> x \<notin> S \<Longrightarrow> g x = f x;
                     ((\<lambda>x. if x \<in> T then f x else 0) has_integral z) (cbox a b)\<rbrakk>
                    \<Longrightarrow> ((\<lambda>x. if x \<in> T then g x else 0) has_integral z) (cbox a b)"
      by (auto dest!: *[where f="\<lambda>x. if x\<in>T then f x else 0" and g="\<lambda>x. if x \<in> T then g x else 0"])
  show ?thesis
    using fint gf
    apply (subst has_integral_alt)
    apply (subst (asm) has_integral_alt)
    apply (auto split: if_split_asm)
     apply (blast dest: *)
    using \<section> by meson
qed

lemma has_integral_spike_eq:
  assumes "negligible S"
    and gf: "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "(f has_integral y) T \<longleftrightarrow> (g has_integral y) T"
    using has_integral_spike [OF \<open>negligible S\<close>] gf
    by metis

lemma integrable_spike:
  assumes "f integrable_on T" "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    shows "g integrable_on T"
  using assms unfolding integrable_on_def by (blast intro: has_integral_spike)

lemma integral_spike:
  assumes "negligible S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "integral T f = integral T g"
  using has_integral_spike_eq[OF assms]
    by (auto simp: integral_def integrable_on_def)


subsection \<open>Some other trivialities about negligible sets\<close>

lemma negligible_subset:
  assumes "negligible s" "t \<subseteq> s"
  shows "negligible t"
  unfolding negligible_def
    by (metis (no_types) Diff_iff assms contra_subsetD has_integral_negligible indicator_simps(2))

lemma negligible_diff[intro?]:
  assumes "negligible s"
  shows "negligible (s - t)"
  using assms by (meson Diff_subset negligible_subset)

lemma negligible_Int:
  assumes "negligible s \<or> negligible t"
  shows "negligible (s \<inter> t)"
  using assms negligible_subset by force

lemma negligible_Un:
  assumes "negligible S" and T: "negligible T"
  shows "negligible (S \<union> T)"
proof -
  have "(indicat_real (S \<union> T) has_integral 0) (cbox a b)"
    if S0: "(indicat_real S has_integral 0) (cbox a b)" 
      and  "(indicat_real T has_integral 0) (cbox a b)" for a b
  proof (subst has_integral_spike_eq[OF T])
    show "indicat_real S x = indicat_real (S \<union> T) x" if "x \<in> cbox a b - T" for x
      by (metis Diff_iff Un_iff indicator_def that)
    show "(indicat_real S has_integral 0) (cbox a b)"
      by (simp add: S0)
  qed
  with assms show ?thesis
    unfolding negligible_def by blast
qed

lemma negligible_Un_eq[simp]: "negligible (s \<union> t) \<longleftrightarrow> negligible s \<and> negligible t"
  using negligible_Un negligible_subset by blast

lemma negligible_sing[intro]: "negligible {a::'a::euclidean_space}"
  using negligible_standard_hyperplane[OF SOME_Basis, of "a \<bullet> (SOME i. i \<in> Basis)"] negligible_subset by blast

lemma negligible_insert[simp]: "negligible (insert a s) \<longleftrightarrow> negligible s"
  by (metis insert_is_Un negligible_Un_eq negligible_sing)

lemma negligible_empty[iff]: "negligible {}"
  using negligible_insert by blast

text\<open>Useful in this form for backchaining\<close>
lemma empty_imp_negligible: "S = {} \<Longrightarrow> negligible S"
  by simp

lemma negligible_finite[intro]:
  assumes "finite s"
  shows "negligible s"
  using assms by (induct s) auto

lemma negligible_Union[intro]:
  assumes "finite \<T>"
    and "\<And>t. t \<in> \<T> \<Longrightarrow> negligible t"
  shows "negligible(\<Union>\<T>)"
  using assms by induct auto

lemma negligible: "negligible S \<longleftrightarrow> (\<forall>T. (indicat_real S has_integral 0) T)"
proof (intro iffI allI)
  fix T
  assume "negligible S"
  then show "(indicator S has_integral 0) T"
    by (meson Diff_iff has_integral_negligible indicator_simps(2))
qed (simp add: negligible_def)

subsection \<open>Finite case of the spike theorem is quite commonly needed\<close>

lemma has_integral_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "(f has_integral y) T"
  shows "(g has_integral y) T"
  using assms has_integral_spike negligible_finite by blast

lemma has_integral_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "((f has_integral y) T \<longleftrightarrow> (g has_integral y) T)"
  by (metis assms has_integral_spike_finite)

lemma integrable_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "f integrable_on T"
  shows "g integrable_on T"
  using assms has_integral_spike_finite by blast

lemma has_integral_bound_spike_finite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and f: "(f has_integral i) (cbox a b)"
      and leB: "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
proof -
  define g where "g \<equiv> (\<lambda>x. if x \<in> S then 0 else f x)"
  then have "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (g x) \<le> B"
    using leB by simp
  moreover have "(g has_integral i) (cbox a b)"
    using has_integral_spike_finite [OF \<open>finite S\<close> _ f]
    by (simp add: g_def)
  ultimately show ?thesis
    by (simp add: \<open>0 \<le> B\<close> g_def has_integral_bound)
qed

corollary has_integral_bound_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and "(f has_integral i) {a..b}"
      and "\<And>x. x \<in> {a..b} - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content {a..b}"
  by (metis assms box_real(2) has_integral_bound_spike_finite)


subsection \<open>In particular, the boundary of an interval is negligible\<close>

lemma negligible_frontier_interval: "negligible(cbox (a::'a::euclidean_space) b - box a b)"
proof -
  let ?A = "\<Union>((\<lambda>k. {x. x\<bullet>k = a\<bullet>k} \<union> {x::'a. x\<bullet>k = b\<bullet>k}) ` Basis)"
  have "negligible ?A"
    by (force simp add: negligible_Union[OF finite_imageI])
  moreover have "cbox a b - box a b \<subseteq> ?A"
    by (force simp add: mem_box)
  ultimately show ?thesis
    by (rule negligible_subset)
qed

lemma has_integral_spike_interior:
  assumes f: "(f has_integral y) (cbox a b)" and gf: "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(g has_integral y) (cbox a b)"
  by (meson Diff_iff gf has_integral_spike[OF negligible_frontier_interval _ f])
  
lemma has_integral_spike_interior_eq:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(f has_integral y) (cbox a b) \<longleftrightarrow> (g has_integral y) (cbox a b)"
  by (metis assms has_integral_spike_interior)

lemma integrable_spike_interior:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
    and "f integrable_on cbox a b"
  shows "g integrable_on cbox a b"
  using assms has_integral_spike_interior_eq by blast


subsection \<open>Integrability of continuous functions\<close>

lemma operative_approximableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)"
proof -
  interpret comm_monoid conj True
    by standard auto
  show ?thesis
  proof (standard, safe)
    fix a b :: 'b
    show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
      if "box a b = {}" for a b
      using assms that
      by (metis content_eq_0_interior integrable_on_null interior_cbox norm_zero right_minus_eq)
    {
      fix c g and k :: 'b
      assume fg: "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" and g: "g integrable_on cbox a b"
      assume k: "k \<in> Basis"
      show "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
           "\<exists>g. (\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}"
        using fg g k by auto
    }
    show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
      if fg1: "\<forall>x\<in>cbox a b \<inter> {x. x \<bullet> k \<le> c}. norm (f x - g1 x) \<le> e" 
        and g1: "g1 integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}"
        and fg2: "\<forall>x\<in>cbox a b \<inter> {x. c \<le> x \<bullet> k}. norm (f x - g2 x) \<le> e" 
        and g2: "g2 integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k}" 
        and k: "k \<in> Basis"
      for c k g1 g2
    proof -
      let ?g = "\<lambda>x. if x\<bullet>k = c then f x else if x\<bullet>k \<le> c then g1 x else g2 x"
      show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
      proof (intro exI conjI ballI)
        show "norm (f x - ?g x) \<le> e" if "x \<in> cbox a b" for x
          by (auto simp: that assms fg1 fg2)
        show "?g integrable_on cbox a b"
        proof -
          have "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c}" "?g integrable_on cbox a b \<inter> {x. x \<bullet> k \<ge> c}"
            by(rule integrable_spike[OF _ negligible_standard_hyperplane[of k c]], use k g1 g2 in auto)+
          with has_integral_split[OF _ _ k] show ?thesis
            unfolding integrable_on_def by blast
        qed
      qed
    qed
  qed
qed

lemma comm_monoid_set_F_and: "comm_monoid_set.F (\<and>) True f s \<longleftrightarrow> (finite s \<longrightarrow> (\<forall>x\<in>s. f x))"
proof -
  interpret bool: comm_monoid_set \<open>(\<and>)\<close> True ..
  show ?thesis
    by (induction s rule: infinite_finite_induct) auto
qed

lemma approximable_on_division:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
    and d: "d division_of (cbox a b)"
    and f: "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
proof -
  interpret operative conj True "\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i"
    using \<open>0 \<le> e\<close> by (rule operative_approximableI)
  from f local.division [OF d] that show thesis
    by auto
qed

lemma integrable_continuous:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
proof (rule integrable_uniform_limit)
  fix e :: real
  assume e: "e > 0"
  then obtain d where "0 < d" and d: "\<And>x x'. \<lbrakk>x \<in> cbox a b; x' \<in> cbox a b; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    using compact_uniformly_continuous[OF assms compact_cbox] unfolding uniformly_continuous_on_def by metis
  obtain p where ptag: "p tagged_division_of cbox a b" and finep: "(\<lambda>x. ball x d) fine p"
    using fine_division_exists[OF gauge_ball[OF \<open>0 < d\<close>], of a b] .
  have *: "\<forall>i\<in>snd ` p. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  proof (safe, unfold snd_conv)
    fix x l
    assume as: "(x, l) \<in> p"
    obtain a b where l: "l = cbox a b"
      using as ptag by blast
    then have x: "x \<in> cbox a b"
      using as ptag by auto
    show "\<exists>g. (\<forall>x\<in>l. norm (f x - g x) \<le> e) \<and> g integrable_on l"
    proof (intro exI conjI strip)
      show "(\<lambda>y. f x) integrable_on l"
        unfolding integrable_on_def l by blast
    next
      fix y
      assume y: "y \<in> l"
      then have "y \<in> ball x d"
        using as finep by fastforce
      then show "norm (f y - f x) \<le> e"
        using d x y as l
        by (metis dist_commute dist_norm less_imp_le mem_ball ptag subsetCE tagged_division_ofD(3))
    qed
  qed
  from e have "e \<ge> 0"
    by auto
  from approximable_on_division[OF this division_of_tagged_division[OF ptag] *]
  show "\<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
    by metis
qed

lemma integrable_continuous_interval:
  fixes f :: "'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
  shows "f integrable_on {a..b}"
  by (metis assms integrable_continuous interval_cbox)

lemmas integrable_continuous_real = integrable_continuous_interval[where 'b=real]

lemma integrable_continuous_closed_segment:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  shows "f integrable_on (closed_segment a b)"
  using assms
  by (auto intro!: integrable_continuous_interval simp: closed_segment_eq_real_ivl)


subsection \<open>Specialization of additivity to one dimension\<close>


subsection \<open>A useful lemma allowing us to factor out the content size\<close>

lemma has_integral_factor_content:
  "(f has_integral i) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content (cbox a b)))"
proof (cases "content (cbox a b) = 0")
  case True
  have "\<And>e p. p tagged_division_of cbox a b \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x)) \<le> e * content (cbox a b)"
    unfolding sum_content_null[OF True] True by force
  moreover have "i = 0" 
    if "\<And>e. e > 0 \<Longrightarrow> \<exists>d. gauge d \<and>
              (\<forall>p. p tagged_division_of cbox a b \<and>
                   d fine p \<longrightarrow>
                   norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) \<le> e * content (cbox a b))"
    using that [of 1]
    by (force simp add: True sum_content_null[OF True] intro: fine_division_exists[of _ a b])
  ultimately show ?thesis
    unfolding has_integral_null_eq[OF True]
    by (force simp add: )
next
  case False
  then have F: "0 < content (cbox a b)"
    using zero_less_measure_iff by blast
  let ?P = "\<lambda>e opp. \<exists>d. gauge d \<and>
    (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow> opp (norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i)) e)"
  show ?thesis
  proof (subst has_integral, safe)
    fix e :: real
    assume e: "e > 0"
    show "?P (e * content (cbox a b)) (\<le>)" if \<section>[rule_format]: "\<forall>\<epsilon>>0. ?P \<epsilon> (<)"
      using \<section> [of "e * content (cbox a b)"]
      by (meson F e less_imp_le mult_pos_pos)
    show "?P e (<)" if \<section>[rule_format]:  "\<forall>\<epsilon>>0. ?P (\<epsilon> * content (cbox a b)) (\<le>)"
      using \<section> [of "e/2 / content (cbox a b)"]
        using F e by (force simp add: algebra_simps)
  qed
qed

lemma has_integral_factor_content_real:
  "(f has_integral i) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b}  \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a..b} ))"
  unfolding box_real[symmetric]
  by (rule has_integral_factor_content)


subsection \<open>Fundamental theorem of calculus\<close>

lemma interval_bounds_real:
  fixes q b :: real
  assumes "a \<le> b"
  shows "Sup {a..b} = b"
    and "Inf {a..b} = a"
  using assms by auto

theorem fundamental_theorem_of_calculus:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> b" 
      and vecd: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
  unfolding has_integral_factor_content box_real[symmetric]
proof safe
  fix e :: real
  assume "e > 0"
  then have "\<forall>x. \<exists>d>0. x \<in> {a..b} \<longrightarrow>
         (\<forall>y\<in>{a..b}. norm (y-x) < d \<longrightarrow> norm (f y - f x - (y-x) *\<^sub>R f' x) \<le> e * norm (y-x))"
    using vecd[unfolded has_vector_derivative_def has_derivative_within_alt] by blast
  then obtain d where d: "\<And>x. 0 < d x"
                 "\<And>x y. \<lbrakk>x \<in> {a..b}; y \<in> {a..b}; norm (y-x) < d x\<rbrakk>
                        \<Longrightarrow> norm (f y - f x - (y-x) *\<^sub>R f' x) \<le> e * norm (y-x)"
    by metis  
  show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
    norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b))"
  proof (rule exI, safe)
    show "gauge (\<lambda>x. ball x (d x))"
      using d(1) gauge_ball_dependent by blast
  next
    fix p
    assume ptag: "p tagged_division_of cbox a b" and finep: "(\<lambda>x. ball x (d x)) fine p"
    have ba: "b - a = (\<Sum>(x,K)\<in>p. Sup K - Inf K)" "f b - f a = (\<Sum>(x,K)\<in>p. f(Sup K) - f(Inf K))"
      using additive_tagged_division_1[where f= "\<lambda>x. x"] additive_tagged_division_1[where f= f]
            \<open>a \<le> b\<close> ptag by auto
    have "norm (\<Sum>(x, K) \<in> p. (content K *\<^sub>R f' x) - (f (Sup K) - f (Inf K)))
          \<le> (\<Sum>n\<in>p. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k))"
    proof (rule sum_norm_le,safe)
      fix x K
      assume "(x, K) \<in> p"
      then have "x \<in> K" and kab: "K \<subseteq> cbox a b"
        using ptag by blast+
      then obtain u v where k: "K = cbox u v" and "x \<in> K" and kab: "K \<subseteq> cbox a b"
        using ptag \<open>(x, K) \<in> p\<close> by auto 
      have "u \<le> v"
        using \<open>x \<in> K\<close> unfolding k by auto
      have ball: "\<forall>y\<in>K. y \<in> ball x (d x)"
        using finep \<open>(x, K) \<in> p\<close> by blast
      have "u \<in> K" "v \<in> K"
        by (simp_all add: \<open>u \<le> v\<close> k)
      have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) = norm (f u - f x - (u - x) *\<^sub>R f' x - (f v - f x - (v - x) *\<^sub>R f' x))"
        by (auto simp add: algebra_simps)
      also have "... \<le> norm (f u - f x - (u - x) *\<^sub>R f' x) + norm (f v - f x - (v - x) *\<^sub>R f' x)"
        by (rule norm_triangle_ineq4)
      finally have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) \<le>
        norm (f u - f x - (u - x) *\<^sub>R f' x) + norm (f v - f x - (v - x) *\<^sub>R f' x)" .
      also have "\<dots> \<le> e * norm (u - x) + e * norm (v - x)"
      proof (rule add_mono)
        show "norm (f u - f x - (u - x) *\<^sub>R f' x) \<le> e * norm (u - x)"
        proof (rule d)
          show "norm (u - x) < d x"
            using \<open>u \<in> K\<close> ball by (auto simp add: dist_real_def)
        qed (use \<open>x \<in> K\<close> \<open>u \<in> K\<close> kab in auto)
        show "norm (f v - f x - (v - x) *\<^sub>R f' x) \<le> e * norm (v - x)"
        proof (rule d)
          show "norm (v - x) < d x"
            using \<open>v \<in> K\<close> ball by (auto simp add: dist_real_def)
        qed (use \<open>x \<in> K\<close> \<open>v \<in> K\<close> kab in auto)
      qed
      also have "\<dots> \<le> e * (Sup K - Inf K)"
        using \<open>x \<in> K\<close> by (auto simp: k interval_bounds_real[OF \<open>u \<le> v\<close>] field_simps)
      finally show "norm (content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))) \<le> e * (Sup K - Inf K)"
        using \<open>u \<le> v\<close> by (simp add: k)
    qed
    with \<open>a \<le> b\<close> show "norm ((\<Sum>(x, K)\<in>p. content K *\<^sub>R f' x) - (f b - f a)) \<le> e * content (cbox a b)"
      by (auto simp: ba split_def sum_subtractf [symmetric] sum_distrib_left)
  qed
qed

lemma ident_has_integral:
  fixes a::real
  assumes "a \<le> b"
  shows "((\<lambda>x. x) has_integral (b\<^sup>2 - a\<^sup>2)/2) {a..b}"
proof -
  have "((\<lambda>x. x) has_integral inverse 2 * b\<^sup>2 - inverse 2 * a\<^sup>2) {a..b}"
    unfolding power2_eq_square
    by (rule fundamental_theorem_of_calculus [OF assms] derivative_eq_intros | simp)+
  then show ?thesis
    by (simp add: field_simps)
qed

lemma integral_ident [simp]:
  fixes a::real
  assumes "a \<le> b"
  shows "integral {a..b} (\<lambda>x. x) = (if a \<le> b then (b\<^sup>2 - a\<^sup>2)/2 else 0)"
  by (metis assms ident_has_integral integral_unique)

lemma ident_integrable_on:
  fixes a::real
  shows "(\<lambda>x. x) integrable_on {a..b}"
by (metis atLeastatMost_empty_iff integrable_on_def has_integral_empty ident_has_integral)

lemma integral_sin [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} sin = cos a - cos b"
proof -
  have "(sin has_integral (- cos b - - cos a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus)
    show "((\<lambda>a. - cos a) has_vector_derivative sin x) (at x within {a..b})" for x
      unfolding has_field_derivative_iff_has_vector_derivative [symmetric]
      by (rule derivative_eq_intros | force)+
  qed (use assms in auto)
  then show ?thesis
    by (simp add: integral_unique)
qed

lemma integral_cos [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} cos = sin b - sin a"
proof -
  have "(cos has_integral (sin b - sin a)) {a..b}"
  proof (rule fundamental_theorem_of_calculus)
    show "(sin has_vector_derivative cos x) (at x within {a..b})" for x
      unfolding has_field_derivative_iff_has_vector_derivative [symmetric]
      by (rule derivative_eq_intros | force)+
  qed (use assms in auto)
  then show ?thesis
    by (simp add: integral_unique)
qed

lemma has_integral_sin_nx: "((\<lambda>x. sin(real_of_int n * x)) has_integral 0) {-pi..pi}"
proof (cases "n = 0")
  case False
  have "((\<lambda>x. sin (n * x)) has_integral (- cos (n * pi)/n - - cos (n * - pi)/n)) {-pi..pi}"
  proof (rule fundamental_theorem_of_calculus)
    show "((\<lambda>x. - cos (n * x) / n) has_vector_derivative sin (n * a)) (at a within {-pi..pi})"
      if "a \<in> {-pi..pi}" for a :: real
      using that False
      unfolding has_vector_derivative_def
      by (intro derivative_eq_intros | force)+
  qed auto
  then show ?thesis
    by simp
qed auto

lemma integral_sin_nx:
   "integral {-pi..pi} (\<lambda>x. sin(x * real_of_int n)) = 0"
  using has_integral_sin_nx [of n] by (force simp: mult.commute)

lemma has_integral_cos_nx:
  "((\<lambda>x. cos(real_of_int n * x)) has_integral (if n = 0 then 2 * pi else 0)) {-pi..pi}"
proof (cases "n = 0")
  case True
  then show ?thesis
    using has_integral_const_real [of "1::real" "-pi" pi] by auto
next
  case False
  have "((\<lambda>x. cos (n * x)) has_integral (sin (n * pi)/n - sin (n * - pi)/n)) {-pi..pi}"
  proof (rule fundamental_theorem_of_calculus)
    show "((\<lambda>x. sin (n * x) / n) has_vector_derivative cos (n * x)) (at x within {-pi..pi})"
      if "x \<in> {-pi..pi}"
      for x :: real
      using that False
      unfolding has_vector_derivative_def
      by (intro derivative_eq_intros | force)+
  qed auto
  with False show ?thesis
    by (simp add: mult.commute)
qed

lemma integral_cos_nx:
   "integral {-pi..pi} (\<lambda>x. cos(x * real_of_int n)) = (if n = 0 then 2 * pi else 0)"
  using has_integral_cos_nx [of n] by (force simp: mult.commute)


subsection \<open>Taylor series expansion\<close>

lemma mvt_integral:
  fixes f::"'a::real_normed_vector\<Rightarrow>'b::banach"
  assumes f'[derivative_intros]:
    "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes line_in: "\<And>t. t \<in> {0..1} \<Longrightarrow> x + t *\<^sub>R y \<in> S"
  shows "f (x + y) - f x = integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y)" (is ?th1)
proof -
  from assms have subset: "(\<lambda>xa. x + xa *\<^sub>R y) ` {0..1} \<subseteq> S" by auto
  note [derivative_intros] =
    has_derivative_subset[OF _ subset]
    has_derivative_in_compose[where f="(\<lambda>xa. x + xa *\<^sub>R y)" and g = f]
  note [continuous_intros] =
    continuous_on_compose2[where f="(\<lambda>xa. x + xa *\<^sub>R y)"]
    continuous_on_subset[OF _ subset]
  have "\<And>t. t \<in> {0..1} \<Longrightarrow>
    ((\<lambda>t. f (x + t *\<^sub>R y)) has_vector_derivative f' (x + t *\<^sub>R y) y)
    (at t within {0..1})"
    using assms
    by (auto simp: has_vector_derivative_def
        linear_cmul[OF has_derivative_linear[OF f'], symmetric]
      intro!: derivative_eq_intros)
  from fundamental_theorem_of_calculus[rule_format, OF _ this]
  show ?th1
    by (auto intro!: integral_unique[symmetric])
qed

lemma (in bounded_bilinear) sum_prod_derivatives_has_vector_derivative:
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and g0: "Dg 0 = g"
  and Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> t" "t \<le> b"
  shows "((\<lambda>t. \<Sum>i<p. (-1)^i *\<^sub>R prod (Df i t) (Dg (p - Suc i) t))
    has_vector_derivative
      prod (f t) (Dg p t) - (-1)^p *\<^sub>R prod (Df p t) (g t))
    (at t within {a..b})"
  using assms
proof cases
  assume p: "p \<noteq> 1"
  define p' where "p' = p - 2"
  from assms p have p': "{..<p} = {..Suc p'}" "p = Suc (Suc p')"
    by (auto simp: p'_def)
  have *: "\<And>i. i \<le> p' \<Longrightarrow> Suc (Suc p' - i) = (Suc (Suc p') - i)"
    by auto
  let ?f = "\<lambda>i. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg ((p - i)) t))"
  have "(\<Sum>i<p. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg (Suc (p - Suc i)) t) +
    prod (Df (Suc i) t) (Dg (p - Suc i) t))) =
    (\<Sum>i\<le>(Suc p'). ?f i - ?f (Suc i))"
    by (auto simp: algebra_simps p'(2) numeral_2_eq_2 * lessThan_Suc_atMost)
  also note sum_telescope
  finally
  have "(\<Sum>i<p. (-1) ^ i *\<^sub>R (prod (Df i t) (Dg (Suc (p - Suc i)) t) +
    prod (Df (Suc i) t) (Dg (p - Suc i) t)))
    = prod (f t) (Dg p t) - (- 1) ^ p *\<^sub>R prod (Df p t) (g t)"
    unfolding p'[symmetric]
    by (simp add: assms)
  thus ?thesis
    using assms
    by (auto intro!: derivative_eq_intros has_vector_derivative)
qed (auto intro!: derivative_eq_intros has_vector_derivative)

lemma
  fixes f::"real\<Rightarrow>'a::banach"
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> b"
  defines "i \<equiv> \<lambda>x. ((b - x) ^ (p - 1) / fact (p - 1)) *\<^sub>R Df p x"
  shows Taylor_has_integral:
    "(i has_integral f b - (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a)) {a..b}"
  and Taylor_integral:
    "f b = (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a) + integral {a..b} i"
  and Taylor_integrable:
    "i integrable_on {a..b}"
proof goal_cases
  case 1
  interpret bounded_bilinear "scaleR::real\<Rightarrow>'a\<Rightarrow>'a"
    by (rule bounded_bilinear_scaleR)
  define g where "g s = (b - s)^(p - 1)/fact (p - 1)" for s
  define Dg where [abs_def]:
    "Dg n s = (if n < p then (-1)^n * (b - s)^(p - 1 - n) / fact (p - 1 - n) else 0)" for n s
  have g0: "Dg 0 = g"
    using \<open>p > 0\<close>
    by (auto simp add: Dg_def field_split_simps g_def split: if_split_asm)
  {
    fix m
    assume "p > Suc m"
    hence "p - Suc m = Suc (p - Suc (Suc m))"
      by auto
    hence "real (p - Suc m) * fact (p - Suc (Suc m)) = fact (p - Suc m)"
      by auto
  } note fact_eq = this
  have Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a..b})"
    unfolding Dg_def
    by (auto intro!: derivative_eq_intros simp: has_vector_derivative_def fact_eq field_split_simps)
  let ?sum = "\<lambda>t. \<Sum>i<p. (- 1) ^ i *\<^sub>R Dg i t *\<^sub>R Df (p - Suc i) t"
  from sum_prod_derivatives_has_vector_derivative[of _ Dg _ _ _ Df,
      OF \<open>p > 0\<close> g0 Dg f0 Df]
  have deriv: "\<And>t. a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (?sum has_vector_derivative
      g t *\<^sub>R Df p t - (- 1) ^ p *\<^sub>R Dg p t *\<^sub>R f t) (at t within {a..b})"
    by auto
  from fundamental_theorem_of_calculus[rule_format, OF \<open>a \<le> b\<close> deriv]
  have "(i has_integral ?sum b - ?sum a) {a..b}"
    using atLeastatMost_empty'[simp del]
    by (simp add: i_def g_def Dg_def)
  also
  have one: "(- 1) ^ p' * (- 1) ^ p' = (1::real)"
    and "{..<p} \<inter> {i. p = Suc i} = {p - 1}"
    for p'
    using \<open>p > 0\<close>
    by (auto simp: power_mult_distrib[symmetric])
  then have "?sum b = f b"
    using Suc_pred'[OF \<open>p > 0\<close>]
    by (simp add: diff_eq_eq Dg_def power_0_left le_Suc_eq if_distrib
        if_distribR sum.If_cases f0)
  also
  have "{..<p} = (\<lambda>x. p - x - 1) ` {..<p}"
  proof safe
    fix x
    assume "x < p"
    thus "x \<in> (\<lambda>x. p - x - 1) ` {..<p}"
      by (auto intro!: image_eqI[where x = "p - x - 1"])
  qed simp
  from _ this
  have "?sum a = (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a)"
    by (rule sum.reindex_cong) (auto simp add: inj_on_def Dg_def one)
  finally show c: ?case .
  case 2 show ?case using c integral_unique
    by (metis (lifting) add.commute diff_eq_eq integral_unique)
  case 3 show ?case using c by force
qed


subsection \<open>Only need trivial subintervals if the interval itself is trivial\<close>

proposition division_of_nontrivial:
  fixes \<D> :: "'a::euclidean_space set set"
  assumes sdiv: "\<D> division_of (cbox a b)"
     and cont0: "content (cbox a b) \<noteq> 0"
  shows "{k. k \<in> \<D> \<and> content k \<noteq> 0} division_of (cbox a b)"
  using sdiv
proof (induction "card \<D>" arbitrary: \<D> rule: less_induct)
  case less
  note \<D> = division_ofD[OF less.prems]
  {
    presume *: "{k \<in> \<D>. content k \<noteq> 0} \<noteq> \<D> \<Longrightarrow> ?case"
    then show ?case
      using less.prems by fastforce
  }
  assume noteq: "{k \<in> \<D>. content k \<noteq> 0} \<noteq> \<D>"
  then obtain K c d where "K \<in> \<D>" and contk: "content K = 0" and keq: "K = cbox c d"
    using \<D>(4) by blast 
  then have "card \<D> > 0"
    unfolding card_gt_0_iff using less by auto
  then have card: "card (\<D> - {K}) < card \<D>"
    using less \<open>K \<in> \<D>\<close> by (simp add: \<D>(1))
  have closed: "closed (\<Union>(\<D> - {K}))"
    using less.prems by auto
  have "x islimpt \<Union>(\<D> - {K})" if "x \<in> K" for x 
    unfolding islimpt_approachable
  proof (intro allI impI)
    fix e::real
    assume "e > 0"
    obtain i where i: "c\<bullet>i = d\<bullet>i" "i\<in>Basis"
      using contk \<D>(3) [OF \<open>K \<in> \<D>\<close>] unfolding box_ne_empty keq
      by (meson content_eq_0 dual_order.antisym)
    then have xi: "x\<bullet>i = d\<bullet>i"
      using \<open>x \<in> K\<close> unfolding keq mem_box by (metis antisym)
    define y where "y = (\<Sum>j\<in>Basis. (if j = i then if c\<bullet>i \<le> (a\<bullet>i + b\<bullet>i)/2 then c\<bullet>i +
      min e (b\<bullet>i - c\<bullet>i)/2 else c\<bullet>i - min e (c\<bullet>i - a\<bullet>i)/2 else x\<bullet>j) *\<^sub>R j)"
    show "\<exists>x'\<in>\<Union>(\<D> - {K}). x' \<noteq> x \<and> dist x' x < e"
    proof (intro bexI conjI)
      have "d \<in> cbox c d"
        using \<D>(3)[OF \<open>K \<in> \<D>\<close>] by (simp add: box_ne_empty(1) keq mem_box(2))
      then have "d \<in> cbox a b"
        using \<D>(2)[OF \<open>K \<in> \<D>\<close>] by (auto simp: keq)
      then have di: "a \<bullet> i \<le> d \<bullet> i \<and> d \<bullet> i \<le> b \<bullet> i"
        using \<open>i \<in> Basis\<close> mem_box(2) by blast
      then have xyi: "y\<bullet>i \<noteq> x\<bullet>i"
        unfolding y_def i xi using \<open>e > 0\<close> cont0 \<open>i \<in> Basis\<close>
        by (auto simp: content_eq_0 elim!: ballE[of _ _ i])
      then show "y \<noteq> x"
        unfolding euclidean_eq_iff[where 'a='a] using i by auto
      have "norm (y-x) \<le> (\<Sum>b\<in>Basis. \<bar>(y - x) \<bullet> b\<bar>)"
        by (rule norm_le_l1)
      also have "... = \<bar>(y - x) \<bullet> i\<bar> + (\<Sum>b \<in> Basis - {i}. \<bar>(y - x) \<bullet> b\<bar>)"
        by (meson finite_Basis i(2) sum.remove)
      also have "... <  e + sum (\<lambda>i. 0) Basis"
      proof (rule add_less_le_mono)
        show "\<bar>(y-x) \<bullet> i\<bar> < e"
          using di \<open>e > 0\<close> y_def i xi by (auto simp: inner_simps)
        show "(\<Sum>i\<in>Basis - {i}. \<bar>(y-x) \<bullet> i\<bar>) \<le> (\<Sum>i\<in>Basis. 0)"
          unfolding y_def by (auto simp: inner_simps)
      qed 
      finally have "norm (y-x) < e + sum (\<lambda>i. 0) Basis" .
      then show "dist y x < e"
        unfolding dist_norm by auto
      have "y \<notin> K"
        unfolding keq mem_box using i(1) i(2) xi xyi by fastforce
      moreover have "y \<in> \<Union>\<D>"
        using subsetD[OF \<D>(2)[OF \<open>K \<in> \<D>\<close>] \<open>x \<in> K\<close>] \<open>e > 0\<close> di i
        by (auto simp: \<D> mem_box y_def field_simps elim!: ballE[of _ _ i])
      ultimately show "y \<in> \<Union>(\<D> - {K})" by auto
    qed
  qed
  then have "K \<subseteq> \<Union>(\<D> - {K})"
    using closed closed_limpt by blast
  then have "\<Union>(\<D> - {K}) = cbox a b"
    unfolding \<D>(6)[symmetric] by auto
  then have "\<D> - {K} division_of cbox a b"
    by (metis Diff_subset less.prems division_of_subset \<D>(6))
  then have "{ka \<in> \<D> - {K}. content ka \<noteq> 0} division_of (cbox a b)"
    using card less.hyps by blast
  moreover have "{ka \<in> \<D> - {K}. content ka \<noteq> 0} = {K \<in> \<D>. content K \<noteq> 0}"
    using contk by auto
  ultimately show ?case by auto
qed


subsection \<open>Integrability on subintervals\<close>

lemma operative_integrableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. f integrable_on i)"
proof -
  interpret comm_monoid conj True
  proof qed
  show ?thesis
  proof
    show "\<And>a b. box a b = {} \<Longrightarrow> (f integrable_on cbox a b) = True"
      by (simp add: content_eq_0_interior integrable_on_null)
    show "\<And>a b c k.
             k \<in> Basis \<Longrightarrow>
             (f integrable_on cbox a b) \<longleftrightarrow>
             (f integrable_on cbox a b \<inter> {x. x \<bullet> k \<le> c} \<and> f integrable_on cbox a b \<inter> {x. c \<le> x \<bullet> k})"
      unfolding integrable_on_def by (auto intro!: has_integral_split)
  qed
qed

lemma integrable_subinterval:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on cbox a b"
    and cd: "cbox c d \<subseteq> cbox a b"
  shows "f integrable_on cbox c d"
proof -
  interpret operative conj True "\<lambda>i. f integrable_on i"
    using order_refl by (rule operative_integrableI)
  show ?thesis
  proof (cases "cbox c d = {}")
    case True
    then show ?thesis
      using division [symmetric] f by (auto simp: comm_monoid_set_F_and)
  next
    case False
    then show ?thesis
      by (metis cd comm_monoid_set_F_and division division_of_finite f partial_division_extend_1)
  qed
qed

lemma integrable_subinterval_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
    and "{c..d} \<subseteq> {a..b}"
  shows "f integrable_on {c..d}"
  by (metis assms box_real(2) integrable_subinterval)

subsection \<open>Combining adjacent intervals in 1 dimension\<close>

lemma has_integral_combine:
  fixes a b c :: real and j :: "'a::banach"
  assumes "a \<le> c"
      and "c \<le> b"
      and ac: "(f has_integral i) {a..c}"
      and cb: "(f has_integral j) {c..b}"
  shows "(f has_integral (i + j)) {a..b}"
proof -
  interpret operative_real "lift_option plus" "Some 0"
    "\<lambda>i. if f integrable_on i then Some (integral i f) else None"
    using operative_integralI by (rule operative_realI)
  from \<open>a \<le> c\<close> \<open>c \<le> b\<close> ac cb coalesce_less_eq
  have *: "lift_option (+)
             (if f integrable_on {a..c} then Some (integral {a..c} f) else None)
             (if f integrable_on {c..b} then Some (integral {c..b} f) else None) =
            (if f integrable_on {a..b} then Some (integral {a..b} f) else None)"
    by (auto simp: split: if_split_asm)
  then have "f integrable_on cbox a b"
    using ac cb by (auto split: if_split_asm)
  with *
  show ?thesis
    using ac cb by (auto simp add: integrable_on_def integral_unique split: if_split_asm)
qed

lemma integral_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and ab: "f integrable_on {a..b}"
  shows "integral {a..c} f + integral {c..b} f = integral {a..b} f"
proof -
  have "(f has_integral integral {a..c} f) {a..c}"
    using ab \<open>c \<le> b\<close> integrable_subinterval_real by fastforce
  moreover
  have "(f has_integral integral {c..b} f) {c..b}"
    using ab \<open>a \<le> c\<close> integrable_subinterval_real by fastforce
  ultimately have "(f has_integral integral {a..c} f + integral {c..b} f) {a..b}"
    using \<open>a \<le> c\<close> \<open>c \<le> b\<close> has_integral_combine by blast
  then show ?thesis
    by (simp add: has_integral_integrable_integral)
qed

lemma integrable_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a..c}"
    and "f integrable_on {c..b}"
  shows "f integrable_on {a..b}"
  using assms
  unfolding integrable_on_def
  by (auto intro!: has_integral_combine)

lemma integral_minus_sets:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> f integrable_on {c .. max a b} \<Longrightarrow>
    integral {c .. a} f - integral {c .. b} f =
    (if a \<le> b then - integral {a .. b} f else integral {b .. a} f)"
  using integral_combine[of c a b f]  integral_combine[of c b a f]
  by (auto simp: algebra_simps max_def)

lemma integral_minus_sets':
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<ge> a \<Longrightarrow> c \<ge> b \<Longrightarrow> f integrable_on {min a b .. c} \<Longrightarrow>
    integral {a .. c} f - integral {b .. c} f =
    (if a \<le> b then integral {a .. b} f else - integral {b .. a} f)"
  using integral_combine[of b a c f] integral_combine[of a b c f]
  by (auto simp: algebra_simps min_def)

subsection \<open>Reduce integrability to "local" integrability\<close>

lemma integrable_on_little_subintervals:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x\<in>cbox a b. \<exists>d>0. \<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v"
  shows "f integrable_on cbox a b"
proof -
  interpret operative conj True "\<lambda>i. f integrable_on i"
    using order_refl by (rule operative_integrableI)
  have "\<forall>x. \<exists>d>0. x\<in>cbox a b \<longrightarrow> (\<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v)"
    using assms by (metis zero_less_one)
  then obtain d where d: "\<And>x. 0 < d x"
     "\<And>x u v. \<lbrakk>x \<in> cbox a b; x \<in> cbox u v; cbox u v \<subseteq> ball x (d x); cbox u v \<subseteq> cbox a b\<rbrakk> 
               \<Longrightarrow> f integrable_on cbox u v"
    by metis
  obtain p where p: "p tagged_division_of cbox a b" "(\<lambda>x. ball x (d x)) fine p"
    using fine_division_exists[OF gauge_ball_dependent,of d a b] d(1) by blast 
  then have sndp: "snd ` p division_of cbox a b"
    by (metis division_of_tagged_division)
  have "f integrable_on k" if "(x, k) \<in> p" for x k
    using tagged_division_ofD(2-4)[OF p(1) that] fineD[OF p(2) that] d[of x] by auto
  then show ?thesis
    unfolding division [symmetric, OF sndp] comm_monoid_set_F_and
    by auto
qed


subsection \<open>Second FTC or existence of antiderivative\<close>

lemma integrable_const[intro]: "(\<lambda>x. c) integrable_on cbox a b"
  unfolding integrable_on_def by blast

lemma integral_has_vector_derivative_continuous_at:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on {a..b}"
     and x: "x \<in> {a..b} - S"
     and "finite S"
     and fx: "continuous (at x within ({a..b} - S)) f"
 shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within ({a..b} - S))"
proof -
  let ?I = "\<lambda>a b. integral {a..b} f"
  { fix e::real
    assume "e > 0"
    obtain d where "d>0" and d: "\<And>x'. \<lbrakk>x' \<in> {a..b} - S; \<bar>x' - x\<bar> < d\<rbrakk> \<Longrightarrow> norm(f x' - f x) \<le> e"
      using \<open>e>0\<close> fx by (auto simp: continuous_within_eps_delta dist_norm less_imp_le)
    have "norm (integral {a..y} f - integral {a..x} f - (y-x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>" (is "?lhs \<le> ?rhs")
           if y: "y \<in> {a..b} - S" and yx: "\<bar>y - x\<bar> < d" for y
    proof (cases "y < x")
      case False
      have "f integrable_on {a..y}"
        using f y by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a y - ?I a x = ?I x y"
        using False x by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {x..y} f - (y-x) *\<^sub>R f x) {x..y}"
      proof (rule has_integral_diff)
        show "(f has_integral integral {x..y} f) {x..y}"
          using x y by (auto intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        show "((\<lambda>u. f x) has_integral (y - x) *\<^sub>R f x) {x..y}"
          using has_integral_const_real [of "f x" x y] False by simp
      qed
      have "?lhs \<le> e * content {x..y}"
        using yx False d x y \<open>e>0\<close> assms 
        by (intro has_integral_bound_real[where f="(\<lambda>u. f u - f x)"]) (auto simp: Idiff fux_int)
      also have "... \<le> ?rhs"
        using False by auto
      finally show ?thesis .
    next
      case True
      have "f integrable_on {a..x}"
        using f x by (simp add: integrable_subinterval_real)
      then have Idiff: "?I a x - ?I a y = ?I y x"
        using True x y by (simp add: algebra_simps integral_combine)
      have fux_int: "((\<lambda>u. f u - f x) has_integral integral {y..x} f - (x - y) *\<^sub>R f x) {y..x}"
      proof (rule has_integral_diff)
        show "(f has_integral integral {y..x} f) {y..x}"
          using x y by (auto intro: integrable_integral [OF integrable_subinterval_real [OF f]])
        show "((\<lambda>u. f x) has_integral (x - y) *\<^sub>R f x) {y..x}"
          using has_integral_const_real [of "f x" y x] True by simp
      qed
      have "norm (integral {a..x} f - integral {a..y} f - (x - y) *\<^sub>R f x) \<le> e * content {y..x}"
        using yx True d x y \<open>e>0\<close> assms 
        by (intro has_integral_bound_real[where f="(\<lambda>u. f u - f x)"]) (auto simp: Idiff fux_int)
      also have "... \<le> e * \<bar>y - x\<bar>"
        using True by auto
      finally have "norm (integral {a..x} f - integral {a..y} f - (x - y) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>" .
      then show ?thesis
        by (simp add: algebra_simps norm_minus_commute)
    qed
    then have "\<exists>d>0. \<forall>y\<in>{a..b} - S. \<bar>y - x\<bar> < d \<longrightarrow> norm (integral {a..y} f - integral {a..x} f - (y-x) *\<^sub>R f x) \<le> e * \<bar>y - x\<bar>"
      using \<open>d>0\<close> by blast
  }
  then show ?thesis
    by (simp add: has_vector_derivative_def has_derivative_within_alt bounded_linear_scaleR_left)
qed


lemma integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f(x)) (at x within {a..b})"
using assms integral_has_vector_derivative_continuous_at [OF integrable_continuous_real]
  by (fastforce simp: continuous_on_eq_continuous_within)

lemma integral_has_real_derivative:
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {a..x} g) has_real_derivative g t) (at t within {a..b})"
  using integral_has_vector_derivative[of a b g t] assms
  by (auto simp: has_field_derivative_iff_has_vector_derivative)

lemma antiderivative_continuous:
  fixes q b :: real
  assumes "continuous_on {a..b} f"
  obtains g where "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative (f x::_::banach)) (at x within {a..b})"
  using integral_has_vector_derivative[OF assms] by auto

subsection \<open>Combined fundamental theorem of calculus\<close>

lemma antiderivative_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
  obtains g where "\<forall>u\<in>{a..b}. \<forall>v \<in> {a..b}. u \<le> v \<longrightarrow> (f has_integral (g v - g u)) {u..v}"
proof -
  obtain g 
    where g: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative f x) (at x within {a..b})" 
    using  antiderivative_continuous[OF assms] by metis
  have "(f has_integral g v - g u) {u..v}" if "u \<in> {a..b}" "v \<in> {a..b}" "u \<le> v" for u v
  proof -
    have "\<And>x. x \<in> cbox u v \<Longrightarrow> (g has_vector_derivative f x) (at x within cbox u v)"
      by (metis atLeastAtMost_iff atLeastatMost_subset_iff box_real(2) g
          has_vector_derivative_within_subset subsetCE that(1,2))
    then show ?thesis
      by (metis box_real(2) that(3) fundamental_theorem_of_calculus)
  qed
  then show ?thesis
    using that by blast
qed


subsection \<open>General "twiddling" for interval-to-interval function image\<close>

lemma has_integral_twiddle:
  assumes "0 < r"
    and hg: "\<And>x. h(g x) = x"
    and gh: "\<And>x. g(h x) = x"
    and contg: "\<And>x. continuous (at x) g"
    and g: "\<And>u v. \<exists>w z. g ` cbox u v = cbox w z"
    and h: "\<And>u v. \<exists>w z. h ` cbox u v = cbox w z"
    and r: "\<And>u v. content(g ` cbox u v) = r * content (cbox u v)"
    and intfi: "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(g x)) has_integral (1 / r) *\<^sub>R i) (h ` cbox a b)"
proof (cases "cbox a b = {}")
  case True
  then show ?thesis 
    using intfi by auto
next
  case False
  obtain w z where wz: "h ` cbox a b = cbox w z"
    using h by blast
  have inj: "inj g" "inj h"
    using hg gh injI by metis+
  from h obtain ha hb where h_eq: "h ` cbox a b = cbox ha hb" by blast
  have "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of h ` cbox a b \<and> d fine p 
              \<longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e)"
    if "e > 0" for e
  proof -
    have "e * r > 0" using that \<open>0 < r\<close> by simp
    with intfi[unfolded has_integral]
    obtain d where "gauge d"
               and d: "\<And>p. p tagged_division_of cbox a b \<and> d fine p 
                        \<Longrightarrow> norm ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - i) < e * r" 
      by metis
    define d' where "d' x = g -` d (g x)" for x
    show ?thesis
    proof (rule_tac x=d' in exI, safe)
      show "gauge d'"
        using \<open>gauge d\<close> continuous_open_vimage[OF _ contg] by (auto simp: gauge_def d'_def)
    next
      fix p
      assume ptag: "p tagged_division_of h ` cbox a b" and finep: "d' fine p"
      note p = tagged_division_ofD[OF ptag]
      have gab: "g y \<in> cbox a b" if "y \<in> K" "(x, K) \<in> p" for x y K
        by (metis hg inj(2) inj_image_mem_iff p(3) subsetCE that that)
      have gimp: "(\<lambda>(x,K). (g x, g ` K)) ` p tagged_division_of (cbox a b) \<and> 
                  d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
        unfolding tagged_division_of
      proof safe
        show "finite ((\<lambda>(x, k). (g x, g ` k)) ` p)"
          using ptag by auto
        show "d fine (\<lambda>(x, k). (g x, g ` k)) ` p"
          using finep unfolding fine_def d'_def by auto
      next
        fix x k
        assume xk: "(x, k) \<in> p"
        show "g x \<in> g ` k"
          using p(2)[OF xk] by auto
        show "\<exists>u v. g ` k = cbox u v"
          using p(4)[OF xk] using assms(5-6) by auto
        fix x' K' u
        assume xk': "(x', K') \<in> p" and u: "u \<in> interior (g ` k)" "u \<in> interior (g ` K')"
        have "interior k \<inter> interior K' \<noteq> {}"
        proof 
          assume "interior k \<inter> interior K' = {}"
          moreover have "u \<in> g ` (interior k \<inter> interior K')"
            using interior_image_subset[OF \<open>inj g\<close> contg] u
            unfolding image_Int[OF inj(1)] by blast
          ultimately show False by blast
        qed
        then have same: "(x, k) = (x', K')"
          using ptag xk' xk by blast
        then show "g x = g x'"
          by auto
        show "g u \<in> g ` K'"if "u \<in> k" for u
          using that same by auto
        show "g u \<in> g ` k"if "u \<in> K'" for u
          using that same by auto
      next
        fix x
        assume "x \<in> cbox a b"
        then have "h x \<in>  \<Union>{k. \<exists>x. (x, k) \<in> p}"
          using p(6) by auto
        then obtain X y where "h x \<in> X" "(y, X) \<in> p" by blast
        then show "x \<in> \<Union>{k. \<exists>x. (x, k) \<in> (\<lambda>(x, k). (g x, g ` k)) ` p}"
          by clarsimp (metis (no_types, lifting) gh image_eqI pair_imageI)
      qed (use gab in auto)
      have *: "inj_on (\<lambda>(x, k). (g x, g ` k)) p"
        using inj(1) unfolding inj_on_def by fastforce
      have "(\<Sum>(x,K)\<in>(\<lambda>(y,L). (g y, g ` L)) ` p. content K *\<^sub>R f x) 
          = (\<Sum>u\<in>p. case case u of (x,K) \<Rightarrow> (g x, g ` K) of (y,L) \<Rightarrow> content L *\<^sub>R f y)"
        by (metis (mono_tags, lifting) "*" sum.reindex_cong)
      also have "... = (\<Sum>(x,K)\<in>p. r *\<^sub>R content K *\<^sub>R f (g x))"
        using r by (auto intro!: * sum.cong simp: bij_betw_def dest!: p(4))
      finally
      have "(\<Sum>(x, K)\<in>(\<lambda>(x,K). (g x, g ` K)) ` p. content K *\<^sub>R f x) - i = r *\<^sub>R (\<Sum>(x,K)\<in>p. content K *\<^sub>R f (g x)) - i" 
        by (simp add: scaleR_right.sum split_def)
      also have "\<dots> = r *\<^sub>R ((\<Sum>(x,K)\<in>p. content K *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i)" 
        using \<open>0 < r\<close> by (auto simp: scaleR_diff_right)
      finally show "norm ((\<Sum>(x,K)\<in>p. content K *\<^sub>R f (g x)) - (1 / r) *\<^sub>R i) < e"
        using d[OF gimp] \<open>0 < r\<close> by auto
    qed
  qed
  then show ?thesis
    by (auto simp: h_eq has_integral)
qed


subsection \<open>Special case of a basic affine transformation\<close>

lemma AE_lborel_inner_neq:
  assumes k: "k \<in> Basis"
  shows "AE x in lborel. x \<bullet> k \<noteq> c"
proof -
  interpret finite_product_sigma_finite "\<lambda>_. lborel" Basis
    proof qed simp
    have "emeasure lborel {x\<in>space lborel. x \<bullet> k = c} 
        = emeasure (\<Pi>\<^sub>M j::'a\<in>Basis. lborel) (\<Pi>\<^sub>E j\<in>Basis. if j = k then {c} else UNIV)"
    using k
    by (auto simp add: lborel_eq[where 'a='a] emeasure_distr intro!: arg_cong2[where f=emeasure])
       (auto simp: space_PiM PiE_iff extensional_def split: if_split_asm)
  also have "\<dots> = (\<Prod>j\<in>Basis. emeasure lborel (if j = k then {c} else UNIV))"
    by (intro measure_times) auto
  also have "\<dots> = 0"
    by (intro prod_zero bexI[OF _ k]) auto
  finally show ?thesis
    by (subst AE_iff_measurable[OF _ refl]) auto
qed

lemma content_image_stretch_interval:
  fixes m :: "'a::euclidean_space \<Rightarrow> real"
  defines "s f x \<equiv> (\<Sum>k::'a\<in>Basis. (f k * (x\<bullet>k)) *\<^sub>R k)"
  shows "content (s m ` cbox a b) = \<bar>\<Prod>k\<in>Basis. m k\<bar> * content (cbox a b)"
proof cases
  have s[measurable]: "s f \<in> borel \<rightarrow>\<^sub>M borel" for f
    by (auto simp: s_def[abs_def])
  assume m: "\<forall>k\<in>Basis. m k \<noteq> 0"
  then have s_comp_s: "s (\<lambda>k. 1 / m k) \<circ> s m = id" "s m \<circ> s (\<lambda>k. 1 / m k) = id"
    by (auto simp: s_def[abs_def] fun_eq_iff euclidean_representation)
  then have "inv (s (\<lambda>k. 1 / m k)) = s m" "bij (s (\<lambda>k. 1 / m k))"
    by (auto intro: inv_unique_comp o_bij)
  then have eq: "s m ` cbox a b = s (\<lambda>k. 1 / m k) -` cbox a b"
    using bij_vimage_eq_inv_image[OF \<open>bij (s (\<lambda>k. 1 / m k))\<close>, of "cbox a b"] by auto
  show ?thesis
    using m unfolding eq measure_def
    by (subst lborel_affine_euclidean[where c=m and t=0])
       (simp_all add: emeasure_density measurable_sets_borel[OF s] abs_prod nn_integral_cmult
                      s_def[symmetric] emeasure_distr vimage_comp s_comp_s enn2real_mult prod_nonneg)
next
  assume "\<not> (\<forall>k\<in>Basis. m k \<noteq> 0)"
  then obtain k where k: "k \<in> Basis" "m k = 0" by auto
  then have [simp]: "(\<Prod>k\<in>Basis. m k) = 0"
    by (intro prod_zero) auto
  have "emeasure lborel {x\<in>space lborel. x \<in> s m ` cbox a b} = 0"
  proof (rule emeasure_eq_0_AE)
    show "AE x in lborel. x \<notin> s m ` cbox a b"
      using AE_lborel_inner_neq[OF \<open>k\<in>Basis\<close>]
    proof eventually_elim
      show "x \<bullet> k \<noteq> 0 \<Longrightarrow> x \<notin> s m ` cbox a b " for x
        using k by (auto simp: s_def[abs_def] cbox_def)
    qed
  qed
  then show ?thesis
    by (simp add: measure_def)
qed

lemma interval_image_affinity_interval:
  "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::'a::euclidean_space) + c) ` cbox a b = cbox u v"
  unfolding image_affinity_cbox
  by auto

lemma content_image_affinity_cbox:
  "content((\<lambda>x::'a::euclidean_space. m *\<^sub>R x + c) ` cbox a b) =
    \<bar>m\<bar> ^ DIM('a) * content (cbox a b)" (is "?l = ?r")
proof (cases "cbox a b = {}")
  case True then show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "m \<ge> 0")
    case True
    with \<open>cbox a b \<noteq> {}\<close> have "cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c) \<noteq> {}"
      by (simp add: box_ne_empty inner_left_distrib mult_left_mono)
    moreover from True have *: "\<And>i. (m *\<^sub>R b + c) \<bullet> i - (m *\<^sub>R a + c) \<bullet> i = m *\<^sub>R (b-a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis
      by (simp add: image_affinity_cbox True content_cbox'
        prod.distrib inner_diff_left)
  next
    case False
    with \<open>cbox a b \<noteq> {}\<close> have "cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c) \<noteq> {}"
      by (simp add: box_ne_empty inner_left_distrib mult_left_mono)
    moreover from False have *: "\<And>i. (m *\<^sub>R a + c) \<bullet> i - (m *\<^sub>R b + c) \<bullet> i = (-m) *\<^sub>R (b-a) \<bullet> i"
      by (simp add: inner_simps field_simps)
    ultimately show ?thesis using False
      by (simp add: image_affinity_cbox content_cbox'
        prod.distrib[symmetric] inner_diff_left flip: prod_constant)
  qed
qed

lemma has_integral_affinity:
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
      and "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral (1 / (\<bar>m\<bar> ^ DIM('a))) *\<^sub>R i) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` cbox a b)"
proof (rule has_integral_twiddle)
  show "\<exists>w z. (\<lambda>x. (1 / m) *\<^sub>R x + - ((1 / m) *\<^sub>R c)) ` cbox u v = cbox w z" 
       "\<exists>w z. (\<lambda>x. m *\<^sub>R x + c) ` cbox u v = cbox w z" for u v
    using interval_image_affinity_interval by blast+
  show "content ((\<lambda>x. m *\<^sub>R x + c) ` cbox u v) = \<bar>m\<bar> ^ DIM('a) * content (cbox u v)" for u v
    using content_image_affinity_cbox by blast
qed (use assms zero_less_power in \<open>auto simp: field_simps\<close>)

lemma integrable_affinity:
  assumes "f integrable_on cbox a b"
    and "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` cbox a b)"
  using has_integral_affinity assms
  unfolding integrable_on_def by blast

lemmas has_integral_affinity01 = has_integral_affinity [of _ _ 0 "1::real", simplified]

lemma integrable_on_affinity:
  assumes "m \<noteq> 0" "f integrable_on (cbox a b)"
  shows   "(\<lambda>x. f (m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x - ((1 / m) *\<^sub>R c)) ` cbox a b)"
proof -
  from assms obtain I where "(f has_integral I) (cbox a b)"
    by (auto simp: integrable_on_def)
  from has_integral_affinity[OF this assms(1), of c] show ?thesis
    by (auto simp: integrable_on_def)
qed

lemma has_integral_cmul_iff:
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R I)) A \<longleftrightarrow> (f has_integral I) A"
  using assms has_integral_cmul[of f I A c]
        has_integral_cmul[of "\<lambda>x. c *\<^sub>R f x" "c *\<^sub>R I" A "inverse c"] by (auto simp: field_simps)

lemma has_integral_affinity':
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)" and "m > 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral (i /\<^sub>R m ^ DIM('a)))
           (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m))"
proof (cases "cbox a b = {}")
  case True
  hence "(cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)) = {}"
    using \<open>m > 0\<close> unfolding box_eq_empty by (auto simp: algebra_simps)
  with True and assms show ?thesis by simp
next
  case False
  have "((\<lambda>x. f (m *\<^sub>R x + c)) has_integral (1 / \<bar>m\<bar> ^ DIM('a)) *\<^sub>R i)
          ((\<lambda>x. (1 / m) *\<^sub>R x + - ((1 / m) *\<^sub>R c)) ` cbox a b)"
    using assms by (intro has_integral_affinity) auto
  also have "((\<lambda>x. (1 / m) *\<^sub>R x + - ((1 / m) *\<^sub>R c)) ` cbox a b) =
               ((\<lambda>x.  - ((1 / m) *\<^sub>R c) + x) ` (\<lambda>x. (1 / m) *\<^sub>R x) ` cbox a b)"
    by (simp add: image_image algebra_simps)
  also have "(\<lambda>x. (1 / m) *\<^sub>R x) ` cbox a b = cbox ((1 / m) *\<^sub>R a) ((1 / m) *\<^sub>R b)" using \<open>m > 0\<close> False
    by (subst image_smult_cbox) simp_all
  also have "(\<lambda>x. - ((1 / m) *\<^sub>R c) + x) ` \<dots> = cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)"
    by (subst cbox_translation [symmetric]) (simp add: field_simps vector_add_divide_simps)
  finally show ?thesis using \<open>m > 0\<close> by (simp add: field_simps)
qed

lemma has_integral_affinity_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "m > 0"
  shows   "((\<lambda>x. f (m *\<^sub>R x + c)) has_integral (I /\<^sub>R m ^ DIM('a)))
               (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)) \<longleftrightarrow>
           (f has_integral I) (cbox a b)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  from has_integral_affinity'[OF this, of "1 / m" "-c /\<^sub>R m"] and \<open>m > 0\<close>
    show ?rhs by (simp add: vector_add_divide_simps) (simp add: field_simps)
next
  assume ?rhs
  from has_integral_affinity'[OF this, of m c] and \<open>m > 0\<close>
  show ?lhs by simp
qed


subsection \<open>Special case of stretching coordinate axes separately\<close>

lemma has_integral_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "((\<lambda>x. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) has_integral
         ((1/ \<bar>prod m Basis\<bar>) *\<^sub>R i)) ((\<lambda>x. (\<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k)) ` cbox a b)"
  apply (rule has_integral_twiddle[where f=f])
  unfolding zero_less_abs_iff content_image_stretch_interval
  unfolding image_stretch_interval empty_as_interval euclidean_eq_iff[where 'a='a]
  using assms
  by auto

lemma has_integral_stretch_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) {a..b}" and "m \<noteq> 0"
  shows "((\<lambda>x. f (m * x)) has_integral (1 / \<bar>m\<bar>) *\<^sub>R i) ((\<lambda>x. x / m) ` {a..b})"
  using has_integral_stretch [of f i a b "\<lambda>b. m"] assms by simp

lemma integrable_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "f integrable_on cbox a b"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "(\<lambda>x::'a. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) integrable_on
    ((\<lambda>x. \<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k) ` cbox a b)"
  using assms unfolding integrable_on_def
  by (force dest: has_integral_stretch)

lemma vec_lambda_eq_sum:
     "(\<chi> k. f k (x $ k)) = (\<Sum>k\<in>Basis. (f (axis_index k) (x \<bullet> k)) *\<^sub>R k)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<chi> k. f k (x \<bullet> axis k 1))"
    by (simp add: cart_eq_inner_axis)
  also have "... = (\<Sum>u\<in>UNIV. f u (x \<bullet> axis u 1) *\<^sub>R axis u 1)"
    by (simp add: vec_eq_iff axis_def if_distrib cong: if_cong)
  also have "... = ?rhs"
    by (simp add: Basis_vec_def UNION_singleton_eq_range sum.reindex axis_eq_axis inj_on_def)
  finally show ?thesis .
qed

lemma has_integral_stretch_cart:
  fixes m :: "'n::finite \<Rightarrow> real"
  assumes f: "(f has_integral i) (cbox a b)" and m: "\<And>k. m k \<noteq> 0"
  shows "((\<lambda>x. f(\<chi> k. m k * x$k)) has_integral i /\<^sub>R \<bar>prod m UNIV\<bar>)
            ((\<lambda>x. \<chi> k. x$k / m k) ` (cbox a b))"
proof -
  have *: "\<forall>k:: real^'n \<in> Basis. m (axis_index k) \<noteq> 0"
    using axis_index by (simp add: m)
  have eqp: "(\<Prod>k:: real^'n \<in> Basis. m (axis_index k)) = prod m UNIV"
    by (simp add: Basis_vec_def UNION_singleton_eq_range prod.reindex axis_eq_axis inj_on_def)
  show ?thesis
    using has_integral_stretch [OF f *] vec_lambda_eq_sum [where f="\<lambda>i x. m i * x"] vec_lambda_eq_sum [where f="\<lambda>i x. x / m i"]
    by (simp add: field_simps eqp)
qed

lemma image_stretch_interval_cart:
  fixes m :: "'n::finite \<Rightarrow> real"
  shows "(\<lambda>x. \<chi> k. m k * x$k) ` cbox a b =
            (if cbox a b = {} then {}
            else cbox (\<chi> k. min (m k * a$k) (m k * b$k)) (\<chi> k. max (m k * a$k) (m k * b$k)))"
proof -
  have *: "(\<Sum>k\<in>Basis. min (m (axis_index k) * (a \<bullet> k)) (m (axis_index k) * (b \<bullet> k)) *\<^sub>R k)
           = (\<chi> k. min (m k * a $ k) (m k * b $ k))"
          "(\<Sum>k\<in>Basis. max (m (axis_index k) * (a \<bullet> k)) (m (axis_index k) * (b \<bullet> k)) *\<^sub>R k)
           = (\<chi> k. max (m k * a $ k) (m k * b $ k))"
    apply (simp_all add: Basis_vec_def cart_eq_inner_axis UNION_singleton_eq_range sum.reindex axis_eq_axis inj_on_def)
    apply (simp_all add: vec_eq_iff axis_def if_distrib cong: if_cong)
    done
  show ?thesis
    by (simp add: vec_lambda_eq_sum [where f="\<lambda>i x. m i * x"] image_stretch_interval eq_cbox *)
qed


subsection \<open>even more special cases\<close>

lemma uminus_interval_vector[simp]:
  fixes a b :: "'a::euclidean_space"
  shows "uminus ` cbox a b = cbox (-b) (-a)"
proof -
  have "x \<in> uminus ` cbox a b" if "x \<in> cbox (- b) (- a)" for x
  proof -
    have "-x \<in> cbox a b"
      using that by (auto simp: mem_box)
    then show ?thesis
      by force
  qed
  then show ?thesis
    by (auto simp: mem_box)
qed

lemma has_integral_reflect_lemma[intro]:
  assumes "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(-x)) has_integral i) (cbox (-b) (-a))"
  using has_integral_affinity[OF assms, of "-1" 0]
  by auto

lemma has_integral_reflect_lemma_real[intro]:
  assumes "(f has_integral i) {a..b::real}"
  shows "((\<lambda>x. f(-x)) has_integral i) {-b .. -a}"
  using assms
  unfolding box_real[symmetric]
  by (rule has_integral_reflect_lemma)

lemma has_integral_reflect[simp]:
  "((\<lambda>x. f (-x)) has_integral i) (cbox (-b) (-a)) \<longleftrightarrow> (f has_integral i) (cbox a b)"
  by (auto dest: has_integral_reflect_lemma)

lemma has_integral_reflect_real[simp]:
  fixes a b::real
  shows "((\<lambda>x. f (-x)) has_integral i) {-b..-a} \<longleftrightarrow> (f has_integral i) {a..b}"
  by (metis has_integral_reflect interval_cbox)

lemma integrable_reflect[simp]: "(\<lambda>x. f(-x)) integrable_on cbox (-b) (-a) \<longleftrightarrow> f integrable_on cbox a b"
  unfolding integrable_on_def by auto

lemma integrable_reflect_real[simp]: "(\<lambda>x. f(-x)) integrable_on {-b .. -a} \<longleftrightarrow> f integrable_on {a..b::real}"
  unfolding box_real[symmetric]
  by (rule integrable_reflect)

lemma integral_reflect[simp]: "integral (cbox (-b) (-a)) (\<lambda>x. f (-x)) = integral (cbox a b) f"
  unfolding integral_def by auto

lemma integral_reflect_real[simp]: "integral {-b .. -a} (\<lambda>x. f (-x)) = integral {a..b::real} f"
  unfolding box_real[symmetric]
  by (rule integral_reflect)

subsection \<open>Stronger form of FCT; quite a tedious proof\<close>

lemma split_minus[simp]: "(\<lambda>(x, k). f x k) x - (\<lambda>(x, k). g x k) x = (\<lambda>(x, k). f x k - g x k) x"
  by (simp add: split_def)

theorem fundamental_theorem_of_calculus_interior:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and contf: "continuous_on {a..b} f"
    and derf: "\<And>x. x \<in> {a <..< b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}"
proof (cases "a = b")
  case True
  then have *: "cbox a b = {b}" "f b - f a = 0"
    by (auto simp add:  order_antisym)
  with True show ?thesis by auto
next
  case False
  with \<open>a \<le> b\<close> have ab: "a < b" by arith
  show ?thesis
    unfolding has_integral_factor_content_real
  proof (intro allI impI)
    fix e :: real
    assume e: "e > 0"
    then have eba8: "(e * (b-a)) / 8 > 0"
      using ab by (auto simp add: field_simps)
    note derf_exp = derf[unfolded has_vector_derivative_def has_derivative_at_alt, THEN conjunct2, rule_format]
    thm derf_exp
    have bounded: "\<And>x. x \<in> {a<..<b} \<Longrightarrow> bounded_linear (\<lambda>u. u *\<^sub>R f' x)"
      by (simp add: bounded_linear_scaleR_left)
    have "\<forall>x \<in> box a b. \<exists>d>0. \<forall>y. norm (y-x) < d \<longrightarrow> norm (f y - f x - (y-x) *\<^sub>R f' x) \<le> e/2 * norm (y-x)"
      (is "\<forall>x \<in> box a b. ?Q x") \<comment>\<open>The explicit quantifier is required by the following step\<close>
    proof
      fix x assume "x \<in> box a b"
      with e show "?Q x"
        using derf_exp [of x "e/2"] by auto
    qed
    then obtain d where d: "\<And>x. 0 < d x"
      "\<And>x y. \<lbrakk>x \<in> box a b; norm (y-x) < d x\<rbrakk> \<Longrightarrow> norm (f y - f x - (y-x) *\<^sub>R f' x) \<le> e/2 * norm (y-x)"
      unfolding bgauge_existence_lemma by metis
    have "bounded (f ` cbox a b)"
      using compact_cbox assms by (auto simp: compact_imp_bounded compact_continuous_image)
    then obtain B 
      where "0 < B" and B: "\<And>x. x \<in> f ` cbox a b \<Longrightarrow> norm x \<le> B"
      unfolding bounded_pos by metis
    obtain da where "0 < da"
      and da: "\<And>c. \<lbrakk>a \<le> c; {a..c} \<subseteq> {a..b}; {a..c} \<subseteq> ball a da\<rbrakk>
                          \<Longrightarrow> norm (content {a..c} *\<^sub>R f' a - (f c - f a)) \<le> (e * (b-a)) / 4"
    proof -
      have "continuous (at a within {a..b}) f"
        using contf continuous_on_eq_continuous_within by force
      with eba8 obtain k where "0 < k"
        and k: "\<And>x. \<lbrakk>x \<in> {a..b}; 0 < norm (x-a); norm (x-a) < k\<rbrakk> \<Longrightarrow> norm (f x - f a) < e * (b-a) / 8"
        unfolding continuous_within Lim_within dist_norm by metis
      obtain l where l: "0 < l" "norm (l *\<^sub>R f' a) \<le> e * (b-a) / 8" 
      proof (cases "f' a = 0")
        case True with ab e that show ?thesis by auto
      next
        case False
        show ?thesis
        proof
          show "norm ((e * (b - a) / 8 / norm (f' a)) *\<^sub>R f' a) \<le> e * (b - a) / 8"
               "0 < e * (b - a) / 8 / norm (f' a)"
            using False ab e by (auto simp add: field_simps)
        qed 
      qed
      have "norm (content {a..c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b-a) / 4"
        if "a \<le> c" "{a..c} \<subseteq> {a..b}" and bmin: "{a..c} \<subseteq> ball a (min k l)" for c
      proof -
        have minkl: "\<bar>a - x\<bar> < min k l" if "x \<in> {a..c}" for x
          using bmin dist_real_def that by auto
        then have lel: "\<bar>c - a\<bar> \<le> \<bar>l\<bar>"
          using that by force
        have "norm ((c - a) *\<^sub>R f' a - (f c - f a)) \<le> norm ((c - a) *\<^sub>R f' a) + norm (f c - f a)"
          by (rule norm_triangle_ineq4)
        also have "\<dots> \<le> e * (b-a) / 8 + e * (b-a) / 8"
        proof (rule add_mono)
          have "norm ((c - a) *\<^sub>R f' a) \<le> norm (l *\<^sub>R f' a)"
            by (auto intro: mult_right_mono [OF lel])
          also have "... \<le> e * (b-a) / 8"
            by (rule l)
          finally show "norm ((c - a) *\<^sub>R f' a) \<le> e * (b-a) / 8" .
        next
          have "norm (f c - f a) < e * (b-a) / 8"
          proof (cases "a = c")
            case True then show ?thesis
              using eba8 by auto
          next
            case False show ?thesis
              by (rule k) (use minkl \<open>a \<le> c\<close> that False in auto)
          qed
          then show "norm (f c - f a) \<le> e * (b-a) / 8" by simp
        qed
        finally show "norm (content {a..c} *\<^sub>R f' a - (f c - f a)) \<le> e * (b-a) / 4"
          unfolding content_real[OF \<open>a \<le> c\<close>] by auto
      qed
      then show ?thesis
        by (rule_tac da="min k l" in that) (auto simp: l \<open>0 < k\<close>)
    qed
    obtain db where "0 < db"
      and db: "\<And>c. \<lbrakk>c \<le> b; {c..b} \<subseteq> {a..b}; {c..b} \<subseteq> ball b db\<rbrakk>
                          \<Longrightarrow> norm (content {c..b} *\<^sub>R f' b - (f b - f c)) \<le> (e * (b-a)) / 4"
    proof -
      have "continuous (at b within {a..b}) f"
        using contf continuous_on_eq_continuous_within by force
      with eba8 obtain k
        where "0 < k"
          and k: "\<And>x. \<lbrakk>x \<in> {a..b}; 0 < norm(x-b); norm(x-b) < k\<rbrakk>
                     \<Longrightarrow> norm (f b - f x) < e * (b-a) / 8"
        unfolding continuous_within Lim_within dist_norm norm_minus_commute by metis
      obtain l where l: "0 < l" "norm (l *\<^sub>R f' b) \<le> (e * (b-a)) / 8"
      proof (cases "f' b = 0")
        case True thus ?thesis 
          using ab e that by auto
      next
        case False show ?thesis
        proof
          show "norm ((e * (b - a) / 8 / norm (f' b)) *\<^sub>R f' b) \<le> e * (b - a) / 8" 
               "0 < e * (b - a) / 8 / norm (f' b)"
            using False ab e by (auto simp add: field_simps)
        qed
      qed
      have "norm (content {c..b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b-a) / 4" 
        if "c \<le> b" "{c..b} \<subseteq> {a..b}" and bmin: "{c..b} \<subseteq> ball b (min k l)" for c
      proof -
        have minkl: "\<bar>b - x\<bar> < min k l" if "x \<in> {c..b}" for x
          using bmin dist_real_def that by auto
        then have lel: "\<bar>b - c\<bar> \<le> \<bar>l\<bar>"
          using that by force
        have "norm ((b - c) *\<^sub>R f' b - (f b - f c)) \<le> norm ((b - c) *\<^sub>R f' b) + norm (f b - f c)"
          by (rule norm_triangle_ineq4)
        also have "\<dots> \<le> e * (b-a) / 8 + e * (b-a) / 8"
        proof (rule add_mono)
          have "norm ((b - c) *\<^sub>R f' b) \<le> norm (l *\<^sub>R f' b)"
            by (auto intro: mult_right_mono [OF lel])
          also have "... \<le> e * (b-a) / 8"
            by (rule l)
          finally show "norm ((b - c) *\<^sub>R f' b) \<le> e * (b-a) / 8" .
        next
          have "norm (f b - f c) < e * (b-a) / 8"
          proof (cases "b = c")
            case True with eba8 show ?thesis
              by auto
          next
            case False show ?thesis
              by (rule k) (use minkl \<open>c \<le> b\<close> that False in auto)
          qed
          then show "norm (f b - f c) \<le> e * (b-a) / 8" by simp
        qed
        finally show "norm (content {c..b} *\<^sub>R f' b - (f b - f c)) \<le> e * (b-a) / 4"
          unfolding content_real[OF \<open>c \<le> b\<close>] by auto
      qed
      then show ?thesis
        by (rule_tac db="min k l" in that) (auto simp: l \<open>0 < k\<close>)
    qed
    let ?d = "(\<lambda>x. ball x (if x=a then da else if x=b then db else d x))"
    show "\<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b} \<and> d fine p \<longrightarrow>
              norm ((\<Sum>(x,K)\<in>p. content K *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a..b})"
    proof (rule exI, safe)
      show "gauge ?d"
        using ab \<open>db > 0\<close> \<open>da > 0\<close> d(1) by (auto intro: gauge_ball_dependent)
    next
      fix p
      assume ptag: "p tagged_division_of {a..b}" and fine: "?d fine p"
      let ?A = "{t. fst t \<in> {a, b}}"
      note p = tagged_division_ofD[OF ptag]
      have pA: "p = (p \<inter> ?A) \<union> (p - ?A)" "finite (p \<inter> ?A)" "finite (p - ?A)" "(p \<inter> ?A) \<inter> (p - ?A) = {}"
        using ptag fine by auto
      have le_xz: "\<And>w x y z::real. y \<le> z/2 \<Longrightarrow> w - x \<le> z/2 \<Longrightarrow> w + y \<le> x + z"
        by arith
      have non: False if xk: "(x,K) \<in> p" and "x \<noteq> a" "x \<noteq> b"
        and less: "e * (Sup K - Inf K)/2 < norm (content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))"
      for x K
      proof -
        obtain u v where k: "K = cbox u v"
          using p(4) xk by blast
        then have "u \<le> v" and uv: "{u, v} \<subseteq> cbox u v"
          using p(2)[OF xk] by auto
        then have result: "e * (v - u)/2 < norm ((v - u) *\<^sub>R f' x - (f v - f u))"
          using less[unfolded k box_real interval_bounds_real content_real] by auto
        then have "x \<in> box a b"
          using p(2) p(3) \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> xk by fastforce
        with d have *: "\<And>y. norm (y-x) < d x 
                \<Longrightarrow> norm (f y - f x - (y-x) *\<^sub>R f' x) \<le> e/2 * norm (y-x)"
          by metis
        have xd: "norm (u - x) < d x" "norm (v - x) < d x"
          using fineD[OF fine xk] \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> uv 
          by (auto simp add: k subset_eq dist_commute dist_real_def)
        have "norm ((v - u) *\<^sub>R f' x - (f v - f u)) =
              norm ((f u - f x - (u - x) *\<^sub>R f' x) - (f v - f x - (v - x) *\<^sub>R f' x))"
          by (rule arg_cong[where f=norm]) (auto simp: scaleR_left.diff)
        also have "\<dots> \<le> e/2 * norm (u - x) + e/2 * norm (v - x)"
          by (metis norm_triangle_le_diff add_mono * xd)
        also have "\<dots> \<le> e/2 * norm (v - u)"
          using p(2)[OF xk] by (auto simp add: field_simps k)
        also have "\<dots> < norm ((v - u) *\<^sub>R f' x - (f v - f u))"
          using result by (simp add: \<open>u \<le> v\<close>)
        finally have "e * (v - u)/2 < e * (v - u)/2"
          using uv by auto
        then show False by auto
      qed
      have "norm (\<Sum>(x, K)\<in>p - ?A. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))
          \<le> (\<Sum>(x, K)\<in>p - ?A. norm (content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))))"
        by (auto intro: sum_norm_le)
      also have "... \<le> (\<Sum>n\<in>p - ?A. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k)/2)"
        using non by (fastforce intro: sum_mono)
      finally have I: "norm (\<Sum>(x, k)\<in>p - ?A.
                  content k *\<^sub>R f' x - (f (Sup k) - f (Inf k)))
             \<le> (\<Sum>n\<in>p - ?A. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k))/2"
        by (simp add: sum_divide_distrib)
      have II: "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R f' x - (f (Sup k) - f (Inf k))) -
             (\<Sum>n\<in>p \<inter> ?A. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k))
             \<le> (\<Sum>n\<in>p - ?A. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k))/2"
      proof -
        have ge0: "0 \<le> e * (Sup k - Inf k)" if xkp: "(x, k) \<in> p \<inter> ?A" for x k
        proof -
          obtain u v where uv: "k = cbox u v"
            by (meson Int_iff xkp p(4))
          with p(2) that uv have "cbox u v \<noteq> {}"
            by blast
          then show "0 \<le> e * ((Sup k) - (Inf k))"
            unfolding uv using e by (auto simp add: field_simps)
        qed
        let ?B = "\<lambda>x. {t \<in> p. fst t = x \<and> content (snd t) \<noteq> 0}"
        let ?C = "{t \<in> p. fst t \<in> {a, b} \<and> content (snd t) \<noteq> 0}"
        have "norm (\<Sum>(x, k)\<in>p \<inter> {t. fst t \<in> {a, b}}. content k *\<^sub>R f' x - (f (Sup k) - f (Inf k))) \<le> e * (b-a)/2"
        proof -
          have *: "\<And>S f e. sum f S = sum f (p \<inter> ?C) \<Longrightarrow> norm (sum f (p \<inter> ?C)) \<le> e \<Longrightarrow> norm (sum f S) \<le> e"
            by auto
          have 1: "content K *\<^sub>R (f' x) - (f ((Sup K)) - f ((Inf K))) = 0"
            if "(x,K) \<in> p \<inter> {t. fst t \<in> {a, b}} - p \<inter> ?C" for x K
          proof -
            have xk: "(x,K) \<in> p" and k0: "content K = 0"
              using that by auto
            then obtain u v where uv: "K = cbox u v"
              using p(4) by blast
            then have "u = v"
              using xk k0 p(2) by force
            then show "content K *\<^sub>R (f' x) - (f ((Sup K)) - f ((Inf K))) = 0"
              using xk unfolding uv by auto
          qed
          have 2: "norm(\<Sum>(x,K)\<in>p \<inter> ?C. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))  \<le> e * (b-a)/2"
          proof -
            have norm_le: "norm (sum f S) \<le> e"
              if "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x = y" "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> e" "e > 0"
              for S f and e :: real
            proof (cases "S = {}")
              case True
              with that show ?thesis by auto
            next
              case False then obtain x where "x \<in> S"
                by auto
              then have "S = {x}"
                using that(1) by auto
              then show ?thesis
                using \<open>x \<in> S\<close> that(2) by auto
            qed
            have *: "p \<inter> ?C = ?B a \<union> ?B b"
              by blast
            then have "norm (\<Sum>(x,K)\<in>p \<inter> ?C. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))) =
                       norm (\<Sum>(x,K) \<in> ?B a \<union> ?B b. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))"
              by simp
            also have "... = norm ((\<Sum>(x,K) \<in> ?B a. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))) + 
                                   (\<Sum>(x,K) \<in> ?B b. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))))"
              using p(1) ab e by (subst sum.union_disjoint) auto
            also have "... \<le> e * (b - a) / 4 + e * (b - a) / 4"
            proof (rule norm_triangle_le [OF add_mono])
              have pa: "\<exists>v. k = cbox a v \<and> a \<le> v" if "(a, k) \<in> p" for k
                using p(2) p(3) p(4) that by fastforce
              show "norm (\<Sum>(x,K) \<in> ?B a. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))) \<le> e * (b - a) / 4"
              proof (intro norm_le; clarsimp)
                fix K K'
                assume K: "(a, K) \<in> p" "(a, K') \<in> p" and ne0: "content K \<noteq> 0" "content K' \<noteq> 0"
                with pa obtain v v' where v: "K = cbox a v" "a \<le> v" and v': "K' = cbox a v'" "a \<le> v'"
                  by blast
                let ?v = "min v v'"
                have "box a ?v \<subseteq> K \<inter> K'"
                  unfolding v v' by (auto simp add: mem_box)
                then have "interior (box a (min v v')) \<subseteq> interior K \<inter> interior K'"
                  using interior_Int interior_mono by blast
                moreover have "(a + ?v)/2 \<in> box a ?v"
                  using ne0  unfolding v v' content_eq_0 not_le
                  by (auto simp add: mem_box)
                ultimately have "(a + ?v)/2 \<in> interior K \<inter> interior K'"
                  unfolding interior_open[OF open_box] by auto
                then show "K = K'"
                  using p(5)[OF K] by auto
              next
                fix K 
                assume K: "(a, K) \<in> p" and ne0: "content K \<noteq> 0"
                show "norm (content c *\<^sub>R f' a - (f (Sup c) - f (Inf c))) * 4 \<le> e * (b-a)"
                  if "(a, c) \<in> p" and ne0: "content c \<noteq> 0" for c
                proof -
                  obtain v where v: "c = cbox a v" and "a \<le> v"
                    using pa[OF \<open>(a, c) \<in> p\<close>] by metis 
                  then have "a \<in> {a..v}" "v \<le> b"
                    using p(3)[OF \<open>(a, c) \<in> p\<close>] by auto
                  moreover have "{a..v} \<subseteq> ball a da"
                    using fineD[OF \<open>?d fine p\<close> \<open>(a, c) \<in> p\<close>] by (simp add: v split: if_split_asm)
                  ultimately show ?thesis
                    unfolding v interval_bounds_real[OF \<open>a \<le> v\<close>] box_real
                    using da \<open>a \<le> v\<close> by auto
                qed
              qed (use ab e in auto)
            next
              have pb: "\<exists>v. k = cbox v b \<and> b \<ge> v" if "(b, k) \<in> p" for k
                using p(2) p(3) p(4) that by fastforce
              show "norm (\<Sum>(x,K) \<in> ?B b. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K))) \<le> e * (b - a) / 4"
              proof (intro norm_le; clarsimp)
                fix K K'
                assume K: "(b, K) \<in> p" "(b, K') \<in> p" and ne0: "content K \<noteq> 0" "content K' \<noteq> 0"
                with pb obtain v v' where v: "K = cbox v b" "v \<le> b" and v': "K' = cbox v' b" "v' \<le> b"
                  by blast
                let ?v = "max v v'"
                have "box ?v b \<subseteq> K \<inter> K'"
                  unfolding v v' by (auto simp: mem_box)
                then have "interior (box (max v v') b) \<subseteq> interior K \<inter> interior K'"
                  using interior_Int interior_mono by blast
                moreover have " ((b + ?v)/2) \<in> box ?v b"
                  using ne0 unfolding v v' content_eq_0 not_le by (auto simp: mem_box)
                ultimately have "((b + ?v)/2) \<in> interior K \<inter> interior K'"
                  unfolding interior_open[OF open_box] by auto
                then show "K = K'"
                  using p(5)[OF K] by auto
              next
                fix K 
                assume K: "(b, K) \<in> p" and ne0: "content K \<noteq> 0"
                show "norm (content c *\<^sub>R f' b - (f (Sup c) - f (Inf c))) * 4 \<le> e * (b-a)"
                  if "(b, c) \<in> p" and ne0: "content c \<noteq> 0" for c
                proof -
                obtain v where v: "c = cbox v b" and "v \<le> b"
                  using \<open>(b, c) \<in> p\<close> pb by blast
                then have "v \<ge> a""b \<in> {v.. b}"  
                  using p(3)[OF \<open>(b, c) \<in> p\<close>] by auto
                moreover have "{v..b} \<subseteq> ball b db"
                  using fineD[OF \<open>?d fine p\<close> \<open>(b, c) \<in> p\<close>] box_real(2) v False by force
                ultimately show ?thesis
                  using db v by auto
                qed
              qed (use ab e in auto)
            qed
            also have "... = e * (b-a)/2"
              by simp
            finally show "norm (\<Sum>(x,k)\<in>p \<inter> ?C.
                        content k *\<^sub>R f' x - (f (Sup k) - f (Inf k))) \<le> e * (b-a)/2" .
          qed
          show "norm (\<Sum>(x, k)\<in>p \<inter> ?A. content k *\<^sub>R f' x - (f ((Sup k)) - f ((Inf k)))) \<le> e * (b-a)/2"
            apply (rule * [OF sum.mono_neutral_right[OF pA(2)]])
            using 1 2 by (auto simp: split_paired_all)
        qed
        also have "... = (\<Sum>n\<in>p. e * (case n of (x, k) \<Rightarrow> Sup k - Inf k))/2"
          unfolding sum_distrib_left[symmetric]
          by (subst additive_tagged_division_1[OF \<open>a \<le> b\<close> ptag]) auto
        finally have norm_le: "norm (\<Sum>(x,K)\<in>p \<inter> {t. fst t \<in> {a, b}}. content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))
                \<le> (\<Sum>n\<in>p. e * (case n of (x, K) \<Rightarrow> Sup K - Inf K))/2" .
        have le2: "\<And>x s1 s2::real. 0 \<le> s1 \<Longrightarrow> x \<le> (s1 + s2)/2 \<Longrightarrow> x - s1 \<le> s2/2"
          by auto
        show ?thesis
          apply (rule le2 [OF sum_nonneg])
          using ge0 apply force
          by (metis (no_types, lifting) Diff_Diff_Int Diff_subset norm_le p(1) sum.subset_diff)
      qed
      note * = additive_tagged_division_1[OF assms(1) ptag, symmetric]
      have "norm (\<Sum>(x,K)\<in>p \<inter> ?A \<union> (p - ?A). content K *\<^sub>R f' x - (f (Sup K) - f (Inf K)))
               \<le> e * (\<Sum>(x,K)\<in>p \<inter> ?A \<union> (p - ?A). Sup K - Inf K)"
        unfolding sum_distrib_left
        unfolding sum.union_disjoint[OF pA(2-)]
        using le_xz norm_triangle_le I II by blast
      then
      show "norm ((\<Sum>(x,K)\<in>p. content K *\<^sub>R f' x) - (f b - f a)) \<le> e * content {a..b}"
        by (simp only: content_real[OF \<open>a \<le> b\<close>] *[of "\<lambda>x. x"] *[of f] sum_subtractf[symmetric] split_minus pA(1) [symmetric])
    qed
  qed
qed


subsection \<open>Stronger form with finite number of exceptional points\<close>

lemma fundamental_theorem_of_calculus_interior_strong:
 fixes f :: "real \<Rightarrow> 'a::banach"
 assumes "finite S"
   and "a \<le> b" "\<And>x. x \<in> {a <..< b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x)"
   and "continuous_on {a .. b} f"
 shows "(f' has_integral (f b - f a)) {a .. b}"
  using assms
proof (induction arbitrary: a b)
case empty
  then show ?case
    using fundamental_theorem_of_calculus_interior by force
next
case (insert x S)
  show ?case
  proof (cases "x \<in> {a<..<b}")
    case False then show ?thesis
      using insert by blast
  next
    case True then have "a < x" "x < b"
      by auto
    have "(f' has_integral f x - f a) {a..x}" "(f' has_integral f b - f x) {x..b}"
      using \<open>continuous_on {a..b} f\<close> \<open>a < x\<close> \<open>x < b\<close> continuous_on_subset by (force simp: intro!: insert)+
    then have "(f' has_integral f x - f a + (f b - f x)) {a..b}"
      using \<open>a < x\<close> \<open>x < b\<close> has_integral_combine less_imp_le by blast
    then show ?thesis
      by simp
  qed
qed

corollary fundamental_theorem_of_calculus_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite S"
    and "a \<le> b"
    and vec: "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x)"
    and "continuous_on {a..b} f"
  shows "(f' has_integral (f b - f a)) {a..b}"
  by (rule fundamental_theorem_of_calculus_interior_strong [OF \<open>finite S\<close>]) (force simp: assms)+

proposition indefinite_integral_continuous_left:
  fixes f:: "real \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on {a..b}" and "a < c" "c \<le> b" "e > 0"
  obtains d where "d > 0"
    and "\<forall>t. c - d < t \<and> t \<le> c \<longrightarrow> norm (integral {a..c} f - integral {a..t} f) < e"
proof -
  obtain w where "w > 0" and w: "\<And>t. \<lbrakk>c - w < t; t < c\<rbrakk> \<Longrightarrow> norm (f c) * norm(c - t) < e/3"
  proof (cases "f c = 0")
    case False
    hence e3: "0 < e/3 / norm (f c)" using \<open>e>0\<close> by simp
    moreover have "norm (f c) * norm (c - t) < e/3" 
      if "t < c" and "c - e/3 / norm (f c) < t" for t
    proof -
      have "norm (c - t) < e/3 / norm (f c)"
        using that by auto
      then show "norm (f c) * norm (c - t) < e/3"
        by (metis e3 mult.commute norm_not_less_zero pos_less_divide_eq zero_less_divide_iff)
    qed
    ultimately show ?thesis
      using that by auto
  next
    case True then show ?thesis
      using \<open>e > 0\<close> that by auto
  qed

  let ?SUM = "\<lambda>p. (\<Sum>(x,K) \<in> p. content K *\<^sub>R f x)"
  have e3: "e/3 > 0"
    using \<open>e > 0\<close> by auto
  have "f integrable_on {a..c}"
    using \<open>a < c\<close> \<open>c \<le> b\<close> by (auto intro: integrable_subinterval_real[OF intf])
  then obtain d1 where "gauge d1" and d1:
    "\<And>p. \<lbrakk>p tagged_division_of {a..c}; d1 fine p\<rbrakk> \<Longrightarrow> norm (?SUM p - integral {a..c} f) < e/3"
    using integrable_integral has_integral_real e3 by metis
  define d where [abs_def]: "d x = ball x w \<inter> d1 x" for x
  have "gauge d"
    unfolding d_def using \<open>w > 0\<close> \<open>gauge d1\<close> by auto
  then obtain k where "0 < k" and k: "ball c k \<subseteq> d c"
    by (meson gauge_def open_contains_ball)

  let ?d = "min k (c - a)/2"
  show thesis
  proof (intro that[of ?d] allI impI, safe)
    show "?d > 0"
      using \<open>0 < k\<close> \<open>a < c\<close> by auto
  next
    fix t
    assume t: "c - ?d < t" "t \<le> c"
    show "norm (integral ({a..c}) f - integral ({a..t}) f) < e"
    proof (cases "t < c")
      case False with \<open>t \<le> c\<close> show ?thesis
        by (simp add: \<open>e > 0\<close>)
    next
      case True
      have "f integrable_on {a..t}"
        using \<open>t < c\<close> \<open>c \<le> b\<close> by (auto intro: integrable_subinterval_real[OF intf])
      then obtain d2 where d2: "gauge d2"
        "\<And>p. p tagged_division_of {a..t} \<and> d2 fine p \<Longrightarrow> norm (?SUM p - integral {a..t} f) < e/3"
        using integrable_integral has_integral_real e3 by metis
      define d3 where "d3 x = (if x \<le> t then d1 x \<inter> d2 x else d1 x)" for x
      have "gauge d3"
        using \<open>gauge d1\<close> \<open>gauge d2\<close> unfolding d3_def gauge_def by auto
      then obtain p where ptag: "p tagged_division_of {a..t}" and pfine: "d3 fine p"
        by (metis box_real(2) fine_division_exists)
      note p' = tagged_division_ofD[OF ptag]
      have pt: "(x,K)\<in>p \<Longrightarrow> x \<le> t" for x K
        by (meson atLeastAtMost_iff p'(2) p'(3) subsetCE)
      with pfine have "d2 fine p"
        unfolding fine_def d3_def by fastforce
      then have d2_fin: "norm (?SUM p - integral {a..t} f) < e/3"
        using d2(2) ptag by auto
      have eqs: "{a..c} \<inter> {x. x \<le> t} = {a..t}" "{a..c} \<inter> {x. x \<ge> t} = {t..c}"
        using t by (auto simp add: field_simps)
      have "p \<union> {(c, {t..c})} tagged_division_of {a..c}"
      proof (intro tagged_division_Un_interval_real)
        show "{(c, {t..c})} tagged_division_of {a..c} \<inter> {x. t \<le> x \<bullet> 1}"
          using \<open>t \<le> c\<close> by (auto simp: eqs tagged_division_of_self_real)
      qed (auto simp: eqs ptag)
      moreover
      have "d1 fine p \<union> {(c, {t..c})}"
        unfolding fine_def
      proof safe
        fix x K y
        assume "(x,K) \<in> p" and "y \<in> K" then show "y \<in> d1 x"
          by (metis Int_iff d3_def subsetD fineD pfine)
      next
        fix x assume "x \<in> {t..c}"
        then have "dist c x < k"
          using t(1) by (auto simp add: field_simps dist_real_def)
        with k show "x \<in> d1 c"
          unfolding d_def by auto
      qed  
      ultimately have d1_fin: "norm (?SUM(p \<union> {(c, {t..c})}) - integral {a..c} f) < e/3"
        using d1 by metis
      have SUMEQ: "?SUM(p \<union> {(c, {t..c})}) = (c - t) *\<^sub>R f c + ?SUM p"
      proof -
        have "?SUM(p \<union> {(c, {t..c})}) = (content{t..c} *\<^sub>R f c) + ?SUM p"
        proof (subst sum.union_disjoint)
          show "p \<inter> {(c, {t..c})} = {}"
            using \<open>t < c\<close> pt by force
        qed (use p'(1) in auto)
        also have "... = (c - t) *\<^sub>R f c + ?SUM p"
          using \<open>t \<le> c\<close> by auto
        finally show ?thesis .
      qed
      have "c - k < t"
        using \<open>k>0\<close> t(1) by (auto simp add: field_simps)
      moreover have "k \<le> w"
      proof (rule ccontr)
        assume "\<not> k \<le> w"
        then have "c + (k + w) / 2 \<notin> d c"
          by (auto simp add: field_simps not_le not_less dist_real_def d_def)
        then have "c + (k + w) / 2 \<notin> ball c k"
          using k by blast
        then show False
          using \<open>0 < w\<close> \<open>\<not> k \<le> w\<close> dist_real_def by auto
      qed
      ultimately have cwt: "c - w < t"
        by (auto simp add: field_simps)
      have eq: "integral {a..c} f - integral {a..t} f = -(((c - t) *\<^sub>R f c + ?SUM p) -
             integral {a..c} f) + (?SUM p - integral {a..t} f) + (c - t) *\<^sub>R f c"
        by auto
      have "norm (integral {a..c} f - integral {a..t} f) < e/3 + e/3 + e/3"
        unfolding eq
      proof (intro norm_triangle_lt add_strict_mono)
        show "norm (- ((c - t) *\<^sub>R f c + ?SUM p - integral {a..c} f)) < e/3"
          by (metis SUMEQ d1_fin norm_minus_cancel)
        show "norm (?SUM p - integral {a..t} f) < e/3"
          using d2_fin by blast
        show "norm ((c - t) *\<^sub>R f c) < e/3"
          using w cwt \<open>t < c\<close> by simp (simp add: field_simps)
      qed
      then show ?thesis by simp
    qed
  qed
qed

lemma indefinite_integral_continuous_right:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
    and "a \<le> c"
    and "c < b"
    and "e > 0"
  obtains d where "0 < d"
    and "\<forall>t. c \<le> t \<and> t < c + d \<longrightarrow> norm (integral {a..c} f - integral {a..t} f) < e"
proof -
  have intm: "(\<lambda>x. f (- x)) integrable_on {-b .. -a}" "- b < - c" "- c \<le> - a"
    using assms by auto
  from indefinite_integral_continuous_left[OF intm \<open>e>0\<close>]
  obtain d where "0 < d"
    and d: "\<And>t. \<lbrakk>- c - d < t; t \<le> -c\<rbrakk> 
             \<Longrightarrow> norm (integral {- b..- c} (\<lambda>x. f (-x)) - integral {- b..t} (\<lambda>x. f (-x))) < e"
    by metis
  let ?d = "min d (b - c)" 
  show ?thesis
  proof (intro that[of "?d"] allI impI)
    show "0 < ?d"
      using \<open>0 < d\<close> \<open>c < b\<close> by auto
    fix t :: real
    assume t: "c \<le> t \<and> t < c + ?d"
    have *: "integral {a..c} f = integral {a..b} f - integral {c..b} f"
            "integral {a..t} f = integral {a..b} f - integral {t..b} f"
      using assms t by (auto simp: algebra_simps integral_combine)
    have "(- c) - d < (- t)" "- t \<le> - c"
      using t by auto 
    from d[OF this] show "norm (integral {a..c} f - integral {a..t} f) < e"
      by (auto simp add: algebra_simps norm_minus_commute *)
  qed
qed

lemma indefinite_integral_continuous_1:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. integral {a..x} f)"
proof -
  have "\<exists>d>0. \<forall>x'\<in>{a..b}. dist x' x < d \<longrightarrow> dist (integral {a..x'} f) (integral {a..x} f) < e" 
       if x: "x \<in> {a..b}" and "e > 0" for x e :: real
  proof (cases "a = b")
    case True
    with that show ?thesis by force
  next
    case False
    with x have "a < b" by force
    with x consider "x = a" | "x = b" | "a < x" "x < b"
      by force
    then show ?thesis 
    proof cases
      case 1 then show ?thesis
        by (force simp: dist_norm algebra_simps intro: indefinite_integral_continuous_right [OF assms _ \<open>a < b\<close> \<open>e > 0\<close>])
    next
      case 2 then show ?thesis
        by (force simp: dist_norm norm_minus_commute algebra_simps intro: indefinite_integral_continuous_left [OF assms \<open>a < b\<close> _ \<open>e > 0\<close>])
    next
      case 3
      obtain d1 where "0 < d1" 
        and d1: "\<And>t. \<lbrakk>x - d1 < t; t \<le> x\<rbrakk> \<Longrightarrow> norm (integral {a..x} f - integral {a..t} f) < e"
        using 3 by (auto intro: indefinite_integral_continuous_left [OF assms \<open>a < x\<close> _ \<open>e > 0\<close>])
      obtain d2 where "0 < d2" 
        and d2: "\<And>t. \<lbrakk>x \<le> t; t < x + d2\<rbrakk> \<Longrightarrow> norm (integral {a..x} f - integral {a..t} f) < e"
        using 3 by (auto intro: indefinite_integral_continuous_right [OF assms _ \<open>x < b\<close> \<open>e > 0\<close>])
      show ?thesis
      proof (intro exI ballI conjI impI)
        show "0 < min d1 d2"
          using \<open>0 < d1\<close> \<open>0 < d2\<close> by simp
        show "dist (integral {a..y} f) (integral {a..x} f) < e"
             if "y \<in> {a..b}" "dist y x < min d1 d2" for y
        proof (cases "y < x")
          case True
          with that d1 show ?thesis by (auto simp: dist_commute dist_norm)
        next
          case False
          with that d2 show ?thesis
            by (auto simp: dist_commute dist_norm)
        qed
      qed
    qed
  qed
  then show ?thesis
    by (auto simp: continuous_on_iff)
qed

lemma indefinite_integral_continuous_1':
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. integral {x..b} f)"
proof -
  have "integral {a..b} f - integral {a..x} f = integral {x..b} f" if "x \<in> {a..b}" for x
    using integral_combine[OF _ _ assms, of x] that
    by (auto simp: algebra_simps)
  with _ show ?thesis
    by (rule continuous_on_eq) (auto intro!: continuous_intros indefinite_integral_continuous_1 assms)
qed

theorem integral_has_vector_derivative':
  fixes f :: "real \<Rightarrow> 'b::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "((\<lambda>u. integral {u..b} f) has_vector_derivative - f x) (at x within {a..b})"
proof -
  have *: "integral {x..b} f = integral {a .. b} f - integral {a .. x} f" if "a \<le> x" "x \<le> b" for x
    using integral_combine[of a x b for x, OF that integrable_continuous_real[OF assms(1)]]
    by (simp add: algebra_simps)
  show ?thesis
    using \<open>x \<in> _\<close> *
    by (rule has_vector_derivative_transform)
      (auto intro!: derivative_eq_intros assms integral_has_vector_derivative)
qed

lemma integral_has_real_derivative':
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {x..b} g) has_real_derivative -g t) (at t within {a..b})"
  using integral_has_vector_derivative'[OF assms]
  by (auto simp: has_field_derivative_iff_has_vector_derivative)


subsection \<open>This doesn't directly involve integration, but that gives an easy proof\<close>

lemma has_derivative_zero_unique_strong_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite k"
    and contf: "continuous_on {a..b} f"
    and "f a = y"
    and fder: "\<And>x. x \<in> {a..b} - k \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within {a..b})"
    and x: "x \<in> {a..b}"
  shows "f x = y"
proof -
  have "a \<le> b" "a \<le> x"
    using assms by auto
  have "((\<lambda>x. 0::'a) has_integral f x - f a) {a..x}"
  proof (rule fundamental_theorem_of_calculus_interior_strong[OF \<open>finite k\<close> \<open>a \<le> x\<close>]; clarify?)
    have "{a..x} \<subseteq> {a..b}"
      using x by auto
    then show "continuous_on {a..x} f"
      by (rule continuous_on_subset[OF contf])
    show "(f has_vector_derivative 0) (at z)" if z: "z \<in> {a<..<x}" and notin: "z \<notin> k" for z
      unfolding has_vector_derivative_def
    proof (simp add: at_within_open[OF z, symmetric])
      show "(f has_derivative (\<lambda>x. 0)) (at z within {a<..<x})"
        by (rule has_derivative_subset [OF fder]) (use x z notin in auto)
    qed
  qed
  from has_integral_unique[OF has_integral_0 this]
  show ?thesis
    unfolding assms by auto
qed


subsection \<open>Generalize a bit to any convex set\<close>

lemma has_derivative_zero_unique_strong_convex:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "convex S" "finite K"
    and contf: "continuous_on S f"
    and "c \<in> S" "f c = y"
    and derf: "\<And>x. x \<in> S - K \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within S)"
    and "x \<in> S"
  shows "f x = y"
proof (cases "x = c")
  case True with \<open>f c = y\<close> show ?thesis
    by blast
next
  case False
  let ?\<phi> = "\<lambda>u. (1 - u) *\<^sub>R c + u *\<^sub>R x"
  have contf': "continuous_on {0 ..1} (f \<circ> ?\<phi>)"
  proof (rule continuous_intros continuous_on_subset[OF contf])+
    show "(\<lambda>u. (1 - u) *\<^sub>R c + u *\<^sub>R x) ` {0..1} \<subseteq> S"
      using \<open>convex S\<close> \<open>x \<in> S\<close> \<open>c \<in> S\<close> by (auto simp add: convex_alt algebra_simps)
  qed
  have "t = u" if "?\<phi> t = ?\<phi> u" for t u
  proof -
    from that have "(t - u) *\<^sub>R x = (t - u) *\<^sub>R c"
      by (auto simp add: algebra_simps)
    then show ?thesis
      using \<open>x \<noteq> c\<close> by auto
  qed
  then have eq: "(SOME t. ?\<phi> t = ?\<phi> u) = u" for u
    by blast
  then have "(?\<phi> -` K) \<subseteq> (\<lambda>z. SOME t. ?\<phi> t = z) ` K"
    by (clarsimp simp: image_iff) (metis (no_types) eq)
  then have fin: "finite (?\<phi> -` K)"
    by (rule finite_surj[OF \<open>finite K\<close>])

  have derf': "((\<lambda>u. f (?\<phi> u)) has_derivative (\<lambda>h. 0)) (at t within {0..1})"
               if "t \<in> {0..1} - {t. ?\<phi> t \<in> K}" for t
  proof -
    have df: "(f has_derivative (\<lambda>h. 0)) (at (?\<phi> t) within ?\<phi> ` {0..1})"
      using \<open>convex S\<close> \<open>x \<in> S\<close> \<open>c \<in> S\<close> that 
      by (auto simp add: convex_alt algebra_simps intro: has_derivative_subset [OF derf])
    have "(f \<circ> ?\<phi> has_derivative (\<lambda>x. 0) \<circ> (\<lambda>z. (0 - z *\<^sub>R c) + z *\<^sub>R x)) (at t within {0..1})"
      by (rule derivative_eq_intros df | simp)+
    then show ?thesis
      unfolding o_def .
  qed
  have "(f \<circ> ?\<phi>) 1 = y"
    apply (rule has_derivative_zero_unique_strong_interval[OF fin contf'])
    unfolding o_def using \<open>f c = y\<close> derf' by auto
  then show ?thesis
    by auto
qed


text \<open>Also to any open connected set with finite set of exceptions. Could
 generalize to locally convex set with limpt-free set of exceptions.\<close>

lemma has_derivative_zero_unique_strong_connected:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected S"
    and "open S"
    and "finite K"
    and contf: "continuous_on S f"
    and "c \<in> S"
    and "f c = y"
    and derf: "\<And>x. x \<in> S - K \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within S)"
    and "x \<in> S"
  shows "f x = y"
proof -
  have "\<exists>e>0. ball x e \<subseteq> (S \<inter> f -` {f x})" if "x \<in> S" for x
  proof -
    obtain e where "0 < e" and e: "ball x e \<subseteq> S"
      using \<open>x \<in> S\<close> \<open>open S\<close> open_contains_ball by blast
    have "ball x e \<subseteq> {u \<in> S. f u \<in> {f x}}"
    proof safe
      fix y
      assume y: "y \<in> ball x e"
      then show "y \<in> S"
        using e by auto
      show "f y = f x"
      proof (rule has_derivative_zero_unique_strong_convex[OF convex_ball \<open>finite K\<close>])
        show "continuous_on (ball x e) f"
          using contf continuous_on_subset e by blast
        show "(f has_derivative (\<lambda>h. 0)) (at u within ball x e)"
             if "u \<in> ball x e - K" for u
          by (metis Diff_iff contra_subsetD derf e has_derivative_subset that)
      qed (use y e \<open>0 < e\<close> in auto)
    qed
    then show "\<exists>e>0. ball x e \<subseteq> (S \<inter> f -` {f x})"
      using \<open>0 < e\<close> by blast
  qed
  then have "openin (top_of_set S) (S \<inter> f -` {y})"
    by (auto intro!: open_openin_trans[OF \<open>open S\<close>] simp: open_contains_ball)
  moreover have "closedin (top_of_set S) (S \<inter> f -` {y})"
    by (force intro!: continuous_closedin_preimage [OF contf])
  ultimately have "(S \<inter> f -` {y}) = {} \<or> (S \<inter> f -` {y}) = S"
    using \<open>connected S\<close> by (simp add: connected_clopen)
  then show ?thesis
    using \<open>x \<in> S\<close> \<open>f c = y\<close> \<open>c \<in> S\<close> by auto
qed

lemma has_derivative_zero_connected_constant:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected S"
      and "open S"
      and "finite k"
      and "continuous_on S f"
      and "\<forall>x\<in>(S - k). (f has_derivative (\<lambda>h. 0)) (at x within S)"
    obtains c where "\<And>x. x \<in> S \<Longrightarrow> f(x) = c"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis empty_iff that)
next
  case False
  then obtain c where "c \<in> S"
    by (metis equals0I)
  then show ?thesis
    by (metis has_derivative_zero_unique_strong_connected assms that)
qed

lemma DERIV_zero_connected_constant:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes "connected S"
      and "open S"
      and "finite K"
      and "continuous_on S f"
      and "\<forall>x\<in>(S - K). DERIV f x :> 0"
    obtains c where "\<And>x. x \<in> S \<Longrightarrow> f(x) = c"
  using has_derivative_zero_connected_constant [OF assms(1-4)] assms
  by (metis DERIV_const has_derivative_const Diff_iff at_within_open frechet_derivative_at has_field_derivative_def)


subsection \<open>Integrating characteristic function of an interval\<close>

lemma has_integral_restrict_open_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes intf: "(f has_integral i) (cbox c d)"
    and cb: "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> box c d then f x else 0) has_integral i) (cbox a b)"
proof (cases "cbox c d = {}")
  case True
  then have "box c d = {}"
    by (metis bot.extremum_uniqueI box_subset_cbox)
  then show ?thesis
    using True intf by auto
next
  case False
  then obtain p where pdiv: "p division_of cbox a b" and inp: "cbox c d \<in> p"
    using cb partial_division_extend_1 by blast
  define g where [abs_def]: "g x = (if x \<in>box c d then f x else 0)" for x
  interpret operative "lift_option plus" "Some (0 :: 'b)"
    "\<lambda>i. if g integrable_on i then Some (integral i g) else None"
    by (fact operative_integralI)
  note operat = division [OF pdiv, symmetric]
  show ?thesis
  proof (cases "(g has_integral i) (cbox a b)")
    case True then show ?thesis
      by (simp add: g_def)
  next
    case False
    have iterate:"F (\<lambda>i. if g integrable_on i then Some (integral i g) else None) (p - {cbox c d}) = Some 0"
    proof (intro neutral ballI)
      fix x
      assume x: "x \<in> p - {cbox c d}"
      then have "x \<in> p"
        by auto
      then obtain u v where uv: "x = cbox u v"
        using pdiv by blast
      have "interior x \<inter> interior (cbox c d) = {}"
        using pdiv inp x by blast 
      then have "(g has_integral 0) x"
        unfolding uv using has_integral_spike_interior[where f="\<lambda>x. 0"]
        by (metis (no_types, lifting) disjoint_iff_not_equal g_def has_integral_0_eq interior_cbox)
      then show "(if g integrable_on x then Some (integral x g) else None) = Some 0"
        by auto
    qed
    interpret comm_monoid_set "lift_option plus" "Some (0 :: 'b)"
      by (intro comm_monoid_set.intro comm_monoid_lift_option add.comm_monoid_axioms)
    have intg: "g integrable_on cbox c d"
      using integrable_spike_interior[where f=f]
      by (meson g_def has_integral_integrable intf)
    moreover have "integral (cbox c d) g = i"
    proof (rule has_integral_unique[OF has_integral_spike_interior intf])
      show "\<And>x. x \<in> box c d \<Longrightarrow> f x = g x"
        by (auto simp: g_def)
      show "(g has_integral integral (cbox c d) g) (cbox c d)"
        by (rule integrable_integral[OF intg])
    qed
    ultimately have "F (\<lambda>A. if g integrable_on A then Some (integral A g) else None) p = Some i"
      by (metis (full_types, lifting) division_of_finite inp iterate pdiv remove right_neutral)
    then
    have "(g has_integral i) (cbox a b)"
      by (metis integrable_on_def integral_unique operat option.inject option.simps(3))
    with False show ?thesis
      by blast
  qed
qed


lemma has_integral_restrict_closed_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b)"
proof -
  note has_integral_restrict_open_subinterval[OF assms]
  note * = has_integral_spike[OF negligible_frontier_interval _ this]
  show ?thesis
    by (rule *[of c d]) (use box_subset_cbox[of c d] in auto)
qed

lemma has_integral_restrict_closed_subintervals_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b) \<longleftrightarrow> (f has_integral i) (cbox c d)"
  (is "?l = ?r")
proof (cases "cbox c d = {}")
  case False
  let ?g = "\<lambda>x. if x \<in> cbox c d then f x else 0"
  show ?thesis
  proof 
    assume ?l
    then have "?g integrable_on cbox c d"
      using assms has_integral_integrable integrable_subinterval by blast
    then have "f integrable_on cbox c d"
      by (rule integrable_eq) auto
    moreover then have "i = integral (cbox c d) f"
      by (meson \<open>((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b)\<close> assms has_integral_restrict_closed_subinterval has_integral_unique integrable_integral)
    ultimately show ?r by auto
  next
    assume ?r then show ?l
      by (rule has_integral_restrict_closed_subinterval[OF _ assms])
  qed
qed auto


text \<open>Hence we can apply the limit process uniformly to all integrals.\<close>

lemma has_integral':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) S \<longleftrightarrow>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> S then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - i) < e))"
  (is "?l \<longleftrightarrow> (\<forall>e>0. ?r e)")
proof (cases "\<exists>a b. S = cbox a b")
  case False then show ?thesis 
    by (simp add: has_integral_alt)
next
  case True
  then obtain a b where S: "S = cbox a b"
    by blast 
  obtain B where " 0 < B" and B: "\<And>x. x \<in> cbox a b \<Longrightarrow> norm x \<le> B"
    using bounded_cbox[unfolded bounded_pos] by blast
  show ?thesis
  proof safe
    fix e :: real
    assume ?l and "e > 0"
    have "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) (cbox c d)"
      if "ball 0 (B+1) \<subseteq> cbox c d" for c d
        unfolding S using B that
        by (force intro: \<open>?l\<close>[unfolded S] has_integral_restrict_closed_subinterval)
    then show "?r e"
      by (meson \<open>0 < B\<close> \<open>0 < e\<close> add_pos_pos le_less_trans zero_less_one norm_pths(2))
  next
    assume as: "\<forall>e>0. ?r e"
    then obtain C 
      where C: "\<And>a b. ball 0 C \<subseteq> cbox a b \<Longrightarrow>
                \<exists>z. ((\<lambda>x. if x \<in> S then f x else 0) has_integral z) (cbox a b)"
      by (meson zero_less_one)
    define c :: 'n where "c = (\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)"
    define d :: 'n where "d = (\<Sum>i\<in>Basis. max B C *\<^sub>R i)"
    have "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i" if "norm x \<le> B" "i \<in> Basis" for x i
      using that and Basis_le_norm[OF \<open>i\<in>Basis\<close>, of x]
      by (auto simp add: field_simps sum_negf c_def d_def)
    then have c_d: "cbox a b \<subseteq> cbox c d"
      by (meson B mem_box(2) subsetI)
    have "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i"
      if x: "norm (0 - x) < C" and i: "i \<in> Basis" for x i
        using Basis_le_norm[OF i, of x] x i by (auto simp: sum_negf c_def d_def)
      then have "ball 0 C \<subseteq> cbox c d"
        by (auto simp: mem_box dist_norm)
    with C obtain y where y: "(f has_integral y) (cbox a b)"
      using c_d has_integral_restrict_closed_subintervals_eq S by blast
    have "y = i"
    proof (rule ccontr)
      assume "y \<noteq> i"
      then have "0 < norm (y - i)"
        by auto
      from as[rule_format,OF this]
      obtain C where C: "\<And>a b. ball 0 C \<subseteq> cbox a b \<Longrightarrow> 
           \<exists>z. ((\<lambda>x. if x \<in> S then f x else 0) has_integral z) (cbox a b) \<and> norm (z-i) < norm (y-i)"
        by auto
      define c :: 'n where "c = (\<Sum>i\<in>Basis. (- max B C) *\<^sub>R i)"
      define d :: 'n where "d = (\<Sum>i\<in>Basis. max B C *\<^sub>R i)"
      have "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i"
        if "norm x \<le> B" and "i \<in> Basis" for x i
          using that Basis_le_norm[of i x] by (auto simp add: field_simps sum_negf c_def d_def)
        then have c_d: "cbox a b \<subseteq> cbox c d"
        by (simp add: B mem_box(2) subset_eq)
      have "c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i" if "norm (0 - x) < C" and "i \<in> Basis" for x i
        using Basis_le_norm[of i x] that by (auto simp: sum_negf c_def d_def)
      then have "ball 0 C \<subseteq> cbox c d"
        by (auto simp: mem_box dist_norm)
      with C obtain z where z: "(f has_integral z) (cbox a b)" "norm (z-i) < norm (y-i)"
        using has_integral_restrict_closed_subintervals_eq[OF c_d] S by blast
      moreover then have "z = y" 
        by (blast intro: has_integral_unique[OF _ y])
      ultimately show False
        by auto
    qed
    then show ?l
      using y by (auto simp: S)
  qed
qed

lemma has_integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes fg: "(f has_integral i) S" "(g has_integral j) S"
    and le: "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  shows "i \<le> j"
  using has_integral_component_le[OF _ fg, of 1] le  by auto

lemma integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on S"
    and "g integrable_on S"
    and "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  shows "integral S f \<le> integral S g"
  by (rule has_integral_le[OF assms(1,2)[unfolded has_integral_integral] assms(3)])

lemma has_integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> i"
  using has_integral_component_nonneg[of 1 f i S]
  unfolding o_def
  using assms
  by auto

lemma integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on S" and 0: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> integral S f"
  by (rule has_integral_nonneg[OF f[unfolded has_integral_integral] 0])


text \<open>Hence a general restriction property.\<close>

lemma has_integral_restrict [simp]:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes "S \<subseteq> T"
  shows "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) T \<longleftrightarrow> (f has_integral i) S"
proof -
  have *: "\<And>x. (if x \<in> T then if x \<in> S then f x else 0 else 0) =  (if x\<in>S then f x else 0)"
    using assms by auto
  show ?thesis
    apply (subst(2) has_integral')
    apply (subst has_integral')
      apply (simp add: *)
    done
qed

corollary has_integral_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) UNIV \<longleftrightarrow> (f has_integral i) s"
  by auto

lemma has_integral_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) T \<longleftrightarrow> (f has_integral i) (S \<inter> T)"
proof -
  have "((\<lambda>x. if x \<in> T then if x \<in> S then f x else 0 else 0) has_integral i) UNIV =
        ((\<lambda>x. if x \<in> S \<inter> T then f x else 0) has_integral i) UNIV"
    by (rule has_integral_cong) auto
  then show ?thesis
    using has_integral_restrict_UNIV by fastforce
qed

lemma integral_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "integral T (\<lambda>x. if x \<in> S then f x else 0) = integral (S \<inter> T) f"
  by (metis (no_types, lifting) has_integral_cong has_integral_restrict_Int integrable_integral integral_unique not_integrable_integral)

lemma integrable_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "(\<lambda>x. if x \<in> S then f x else 0) integrable_on T \<longleftrightarrow> f integrable_on (S \<inter> T)"
  using has_integral_restrict_Int by fastforce

lemma has_integral_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "(f has_integral i) S"
      and "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
      and "S \<subseteq> T"
    shows "(f has_integral i) T"
proof -
  have "(\<lambda>x. if x \<in> S then f x else 0) = (\<lambda>x. if x \<in> T then f x else 0)"
    using assms by fastforce
  with f show ?thesis
    by (simp only: has_integral_restrict_UNIV [symmetric, of f])
qed

lemma integrable_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S"
    and "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
    and "S \<subseteq> t"
  shows "f integrable_on t"
  using assms
  unfolding integrable_on_def
  by (auto intro:has_integral_on_superset)

lemma integral_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "integral UNIV (\<lambda>x. if x \<in> S then f x else 0) = integral S f"
  by (simp add: integral_restrict_Int)

lemma integrable_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(\<lambda>x. if x \<in> s then f x else 0) integrable_on UNIV \<longleftrightarrow> f integrable_on s"
  unfolding integrable_on_def
  by auto

lemma has_integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes k: "k \<in> Basis"
    and as: "S \<subseteq> T" "(f has_integral i) S" "(f has_integral j) T" "\<And>x. x\<in>T \<Longrightarrow> 0 \<le> f(x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
proof -
  have \<section>: "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) UNIV"
          "((\<lambda>x. if x \<in> T then f x else 0) has_integral j) UNIV"
    by (simp_all add: assms)
  show ?thesis
    using as by (force intro!: has_integral_component_le[OF k \<section>])
qed

subsection\<open>Integrals on set differences\<close>

lemma has_integral_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes S: "(f has_integral i) S" and T: "(f has_integral j) T"
    and neg: "negligible (T - S)"
  shows "(f has_integral (i - j)) (S - T)"
proof -
  show ?thesis
    unfolding has_integral_restrict_UNIV [symmetric, of f]
  proof (rule has_integral_spike [OF neg])
    have eq: "(\<lambda>x. (if x \<in> S then f x else 0) - (if x \<in> T then f x else 0)) =
            (\<lambda>x. if x \<in> T - S then - f x else if x \<in> S - T then f x else 0)"
      by (force simp add: )
    have "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) UNIV"
      "((\<lambda>x. if x \<in> T then f x else 0) has_integral j) UNIV"
      using S T has_integral_restrict_UNIV by auto
    from has_integral_diff [OF this]
    show "((\<lambda>x. if x \<in> T - S then - f x else if x \<in> S - T then f x else 0)
                   has_integral i-j) UNIV"
      by (simp add: eq)
  qed force
qed

lemma integral_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "f integrable_on S" "f integrable_on T" "negligible(T - S)"
 shows "integral (S - T) f = integral S f - integral T f"
  by (rule integral_unique) (simp add: assms has_integral_setdiff integrable_integral)

lemma integrable_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) S" "(f has_integral j) T" "negligible (T - S)"
  shows "f integrable_on (S - T)"
  using has_integral_setdiff [OF assms]
  by (simp add: has_integral_iff)

lemma negligible_setdiff [simp]: "T \<subseteq> S \<Longrightarrow> negligible (T - S)"
  by (metis Diff_eq_empty_iff negligible_empty)

lemma negligible_on_intervals: "negligible s \<longleftrightarrow> (\<forall>a b. negligible(s \<inter> cbox a b))" (is "?l \<longleftrightarrow> ?r")
proof
  assume R: ?r
  show ?l
    unfolding negligible_def
  proof safe
    fix a b
    have "negligible (s \<inter> cbox a b)"
      by (simp add: R)
    then show "(indicator s has_integral 0) (cbox a b)"
      by (meson Diff_iff Int_iff has_integral_negligible indicator_simps(2))
  qed
qed (simp add: negligible_Int)

lemma negligible_translation:
  assumes "negligible S"
    shows "negligible ((+) c ` S)"
proof -
  have inj: "inj ((+) c)"
    by simp
  show ?thesis
  using assms
  proof (clarsimp simp: negligible_def)
    fix a b
    assume "\<forall>x y. (indicator S has_integral 0) (cbox x y)"
    then have *: "(indicator S has_integral 0) (cbox (a-c) (b-c))"
      by (meson Diff_iff assms has_integral_negligible indicator_simps(2))
    have eq: "indicator ((+) c ` S) = (\<lambda>x. indicator S (x - c))"
      by (force simp add: indicator_def)
    show "(indicator ((+) c ` S) has_integral 0) (cbox a b)"
      using has_integral_affinity [OF *, of 1 "-c"]
            cbox_translation [of "c" "-c+a" "-c+b"]
      by (simp add: eq) (simp add: ac_simps)
  qed
qed

lemma negligible_translation_rev:
  assumes "negligible ((+) c ` S)"
    shows "negligible S"
by (metis negligible_translation [OF assms, of "-c"] translation_galois)

lemma has_integral_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "(f has_integral y) S \<longleftrightarrow> (f has_integral y) T"
proof -
  have "((\<lambda>x. if x \<in> S then f x else 0) has_integral y) UNIV =
        ((\<lambda>x. if x \<in> T then f x else 0) has_integral y) UNIV"
  proof (rule has_integral_spike_eq)
    show "negligible ({x \<in> S - T. f x \<noteq> 0} \<union> {x \<in> T - S. f x \<noteq> 0})"
      by (rule negligible_Un [OF assms])
  qed auto
  then show ?thesis
    by (simp add: has_integral_restrict_UNIV)
qed

corollary integral_spike_set:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "integral S f = integral T f"
  using has_integral_spike_set_eq [OF assms]
  by (metis eq_integralD integral_unique)

lemma integrable_spike_set:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on S" and neg: "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "f integrable_on T"
  using has_integral_spike_set_eq [OF neg] f by blast

lemma integrable_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((S - T) \<union> (T - S))"
  shows "f integrable_on S \<longleftrightarrow> f integrable_on T"
  by (blast intro: integrable_spike_set assms negligible_subset)

lemma integrable_on_insert_iff: "f integrable_on (insert x X) \<longleftrightarrow> f integrable_on X"
  for f::"_ \<Rightarrow> 'a::banach"
  by (rule integrable_spike_set_eq) (auto simp: insert_Diff_if)

lemma has_integral_interior:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "negligible(frontier S) \<Longrightarrow> (f has_integral y) (interior S) \<longleftrightarrow> (f has_integral y) S"
  by (rule has_integral_spike_set_eq [OF empty_imp_negligible negligible_subset])
     (use interior_subset in \<open>auto simp: frontier_def closure_def\<close>)

lemma has_integral_closure:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "negligible(frontier S) \<Longrightarrow> (f has_integral y) (closure S) \<longleftrightarrow> (f has_integral y) S"
  by (rule has_integral_spike_set_eq [OF negligible_subset empty_imp_negligible]) (auto simp: closure_Un_frontier )

lemma has_integral_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "(f has_integral y) (box a b) \<longleftrightarrow> (f has_integral y) (cbox a b)"
  unfolding interior_cbox [symmetric]
  by (metis frontier_cbox has_integral_interior negligible_frontier_interval)

lemma integrable_on_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "f integrable_on box a b \<longleftrightarrow> f integrable_on cbox a b"
  by (simp add: has_integral_open_interval integrable_on_def)

lemma integral_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "integral(box a b) f = integral(cbox a b) f"
  by (metis has_integral_integrable_integral has_integral_open_interval not_integrable_integral)


subsection \<open>More lemmas that are useful later\<close>

lemma has_integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "(f has_integral i) s"
    and "(f has_integral j) t"
    and "\<forall>x\<in>t. 0 \<le> f x"
  shows "i \<le> j"
  using has_integral_subset_component_le[OF _ assms(1), of 1 f i j]
  using assms
  by auto

lemma integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "k \<in> Basis"
    and "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x \<bullet> k"
  shows "(integral s f)\<bullet>k \<le> (integral t f)\<bullet>k"
  by (meson assms has_integral_subset_component_le integrable_integral)

lemma integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x"
  shows "integral s f \<le> integral t f"
  using assms has_integral_subset_le by blast

lemma has_integral_alt':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow> 
          (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
          (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
            norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e)"
  (is "?l = ?r")
proof
  assume rhs: ?r
  show ?l
  proof (subst has_integral', intro allI impI)
    fix e::real
    assume "e > 0"
    from rhs[THEN conjunct2,rule_format,OF this] 
    show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                   (\<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z)
                         (cbox a b) \<and> norm (z - i) < e)"
      by (simp add: has_integral_iff rhs)
  qed
next
  let ?\<Phi> = "\<lambda>e a b. \<exists>z. ((\<lambda>x. if x \<in> s then f x else 0) has_integral z) (cbox a b) \<and> norm (z - i) < e"
  assume ?l 
  then have lhs: "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow> ?\<Phi> e a b" if "e > 0" for e
    using that has_integral'[of f] by auto
  let ?f = "\<lambda>x. if x \<in> s then f x else 0"
  show ?r
  proof (intro conjI allI impI)
    fix a b :: 'n
    from lhs[OF zero_less_one]
    obtain B where "0 < B" and B: "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow> ?\<Phi> 1 a b"
      by blast
    let ?a = "\<Sum>i\<in>Basis. min (a\<bullet>i) (-B) *\<^sub>R i::'n"
    let ?b = "\<Sum>i\<in>Basis. max (b\<bullet>i) B *\<^sub>R i::'n"
    show "?f integrable_on cbox a b"
    proof (rule integrable_subinterval[of _ ?a ?b])
      have "?a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> ?b \<bullet> i" if "norm (0 - x) < B" "i \<in> Basis" for x i
        using Basis_le_norm[of i x] that by (auto simp add:field_simps)
      then have "ball 0 B \<subseteq> cbox ?a ?b"
        by (auto simp: mem_box dist_norm)
      then show "?f integrable_on cbox ?a ?b"
        unfolding integrable_on_def using B by blast
      show "cbox a b \<subseteq> cbox ?a ?b"
        by (force simp: mem_box)
    qed
  
    fix e :: real
    assume "e > 0"
    with lhs show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e"
      by (metis (no_types, lifting) has_integral_integrable_integral)
  qed
qed


subsection \<open>Continuity of the integral (for a 1-dimensional interval)\<close>

lemma integrable_alt:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<longleftrightarrow>
    (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
    norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) -
      integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e)"
  (is "?l = ?r")
proof
  let ?F = "\<lambda>x. if x \<in> s then f x else 0"
  assume ?l
  then obtain y where intF: "\<And>a b. ?F integrable_on cbox a b"
          and y: "\<And>e. 0 < e \<Longrightarrow>
              \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow> norm (integral (cbox a b) ?F - y) < e"
    unfolding integrable_on_def has_integral_alt'[of f] by auto
  show ?r
  proof (intro conjI allI impI intF)
    fix e::real
    assume "e > 0"
    then have "e/2 > 0"
      by auto
    obtain B where "0 < B" 
       and B: "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow> norm (integral (cbox a b) ?F - y) < e/2"
      using \<open>0 < e/2\<close> y by blast
    show "\<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
                  norm (integral (cbox a b) ?F - integral (cbox c d) ?F) < e"
    proof (intro conjI exI impI allI, rule \<open>0 < B\<close>)
      fix a b c d::'n
      assume sub: "ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d"
      show "norm (integral (cbox a b) ?F - integral (cbox c d) ?F) < e"
        using sub by (auto intro: norm_triangle_half_l dest: B)
    qed
  qed
next
  let ?F = "\<lambda>x. if x \<in> s then f x else 0"
  assume rhs: ?r
  let ?cube = "\<lambda>n. cbox (\<Sum>i\<in>Basis. - real n *\<^sub>R i::'n) (\<Sum>i\<in>Basis. real n *\<^sub>R i)"
  have "Cauchy (\<lambda>n. integral (?cube n) ?F)"
    unfolding Cauchy_def
  proof (intro allI impI)
    fix e::real
    assume "e > 0"
    with rhs obtain B where "0 < B" 
      and B: "\<And>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d 
                        \<Longrightarrow> norm (integral (cbox a b) ?F - integral (cbox c d) ?F) < e"
      by blast
    obtain N where N: "B \<le> real N"
      using real_arch_simple by blast
    have "ball 0 B \<subseteq> ?cube n" if n: "n \<ge> N" for n
    proof -
      have "sum ((*\<^sub>R) (- real n)) Basis \<bullet> i \<le> x \<bullet> i \<and>
            x \<bullet> i \<le> sum ((*\<^sub>R) (real n)) Basis \<bullet> i"
        if "norm x < B" "i \<in> Basis" for x i::'n
          using Basis_le_norm[of i x] n N that by (auto simp add: field_simps sum_negf)
      then show ?thesis
        by (auto simp: mem_box dist_norm)
    qed
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (integral (?cube m) ?F) (integral (?cube n) ?F) < e"
      by (fastforce simp add: dist_norm intro!: B)
  qed
  then obtain i where i: "(\<lambda>n. integral (?cube n) ?F) \<longlonglongrightarrow> i"
    using convergent_eq_Cauchy by blast
  have "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow> norm (integral (cbox a b) ?F - i) < e"
    if "e > 0" for e
  proof -
    have *: "e/2 > 0" using that by auto
    then obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> norm (i - integral (?cube n) ?F) < e/2"
      using i[THEN LIMSEQ_D, simplified norm_minus_commute] by meson
    obtain B where "0 < B" 
      and B: "\<And>a b c d. \<lbrakk>ball 0 B \<subseteq> cbox a b; ball 0 B \<subseteq> cbox c d\<rbrakk> \<Longrightarrow>
                  norm (integral (cbox a b) ?F - integral (cbox c d) ?F) < e/2"
      using rhs * by meson
    let ?B = "max (real N) B"
    show ?thesis
    proof (intro exI conjI allI impI)
      show "0 < ?B"
        using \<open>B > 0\<close> by auto
      fix a b :: 'n
      assume "ball 0 ?B \<subseteq> cbox a b"
      moreover obtain n where n: "max (real N) B \<le> real n"
        using real_arch_simple by blast
      moreover have "ball 0 B \<subseteq> ?cube n"
      proof 
        fix x :: 'n
        assume x: "x \<in> ball 0 B"
        have "\<lbrakk>norm (0 - x) < B; i \<in> Basis\<rbrakk>
              \<Longrightarrow> sum ((*\<^sub>R) (-n)) Basis \<bullet> i\<le> x \<bullet> i \<and> x \<bullet> i \<le> sum ((*\<^sub>R) n) Basis \<bullet> i" for i
          using Basis_le_norm[of i x] n by (auto simp add: field_simps sum_negf)
        then show "x \<in> ?cube n"
          using x by (auto simp: mem_box dist_norm)
      qed 
      ultimately show "norm (integral (cbox a b) ?F - i) < e"
        using norm_triangle_half_l [OF B N] by force
    qed
  qed
  then show ?l unfolding integrable_on_def has_integral_alt'[of f]
    using rhs by blast
qed

lemma integrable_altD:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
  shows "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
    and "\<And>e. e > 0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e"
  using assms[unfolded integrable_alt[of f]] by auto

lemma integrable_alt_subset:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows
     "f integrable_on S \<longleftrightarrow>
      (\<forall>a b. (\<lambda>x. if x \<in> S then f x else 0) integrable_on cbox a b) \<and>
      (\<forall>e>0. \<exists>B>0. \<forall>a b c d.
                      ball 0 B \<subseteq> cbox a b \<and> cbox a b \<subseteq> cbox c d
                      \<longrightarrow> norm(integral (cbox a b) (\<lambda>x. if x \<in> S then f x else 0) -
                               integral (cbox c d) (\<lambda>x. if x \<in> S then f x else 0)) < e)"
      (is "_ = ?rhs")
proof -
  let ?g = "\<lambda>x. if x \<in> S then f x else 0"
  have "f integrable_on S \<longleftrightarrow>
        (\<forall>a b. ?g integrable_on cbox a b) \<and>
        (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
           norm (integral (cbox a b) ?g - integral (cbox c d)  ?g) < e)"
    by (rule integrable_alt)
  also have "\<dots> = ?rhs"
  proof -
    { fix e :: "real"
      assume e: "\<And>e. e>0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> cbox a b \<subseteq> cbox c d \<longrightarrow>
                                   norm (integral (cbox a b) ?g - integral (cbox c d) ?g) < e"
        and "e > 0"
      obtain B where "B > 0"
        and B: "\<And>a b c d. \<lbrakk>ball 0 B \<subseteq> cbox a b; cbox a b \<subseteq> cbox c d\<rbrakk> \<Longrightarrow>
                           norm (integral (cbox a b) ?g - integral (cbox c d) ?g) < e/2"
        using \<open>e > 0\<close> e [of "e/2"] by force
      have "\<exists>B>0. \<forall>a b c d.
               ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
               norm (integral (cbox a b) ?g - integral (cbox c d) ?g) < e"
      proof (intro exI allI conjI impI)
        fix a b c d :: "'a"
        let ?\<alpha> = "\<Sum>i\<in>Basis. max (a \<bullet> i) (c \<bullet> i) *\<^sub>R i"
        let ?\<beta> = "\<Sum>i\<in>Basis. min (b \<bullet> i) (d \<bullet> i) *\<^sub>R i"
        show "norm (integral (cbox a b) ?g - integral (cbox c d) ?g) < e"
          if ball: "ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d"
        proof -
          have B': "norm (integral (cbox a b \<inter> cbox c d) ?g - integral (cbox x y) ?g) < e/2"
            if "cbox a b \<inter> cbox c d \<subseteq> cbox x y" for x y
            using B [of ?\<alpha> ?\<beta> x y] ball that by (simp add: Int_interval [symmetric])
          show ?thesis
            using B' [of a b] B' [of c d] norm_triangle_half_r by blast
        qed
      qed (use \<open>B > 0\<close> in auto)}
    then show ?thesis
      by force
  qed
  finally show ?thesis .
qed

lemma integrable_on_subcbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on S"
    and sub: "cbox a b \<subseteq> S"
  shows "f integrable_on cbox a b"
proof -
  have "(\<lambda>x. if x \<in> S then f x else 0) integrable_on cbox a b"
    by (simp add: intf integrable_altD(1))
then show ?thesis
  by (metis (mono_tags) sub integrable_restrict_Int le_inf_iff order_refl subset_antisym)
qed


subsection \<open>A straddling criterion for integrability\<close>

lemma integrable_straddle_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>g h i j. (g has_integral i) (cbox a b) \<and> (h has_integral j) (cbox a b) \<and>
                            \<bar>i - j\<bar> < e \<and> (\<forall>x\<in>cbox a b. (g x) \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on cbox a b"
proof -
  have "\<exists>d. gauge d \<and>
            (\<forall>p1 p2. p1 tagged_division_of cbox a b \<and> d fine p1 \<and>
                     p2 tagged_division_of cbox a b \<and> d fine p2 \<longrightarrow>
                     \<bar>(\<Sum>(x,K)\<in>p1. content K *\<^sub>R f x) - (\<Sum>(x,K)\<in>p2. content K *\<^sub>R f x)\<bar> < e)"
    if "e > 0" for e
  proof -
    have e: "e/3 > 0"
      using that by auto
    then obtain g h i j where ij: "\<bar>i - j\<bar> < e/3"
            and "(g has_integral i) (cbox a b)"
            and "(h has_integral j) (cbox a b)"
            and fgh: "\<And>x. x \<in> cbox a b \<Longrightarrow> g x \<le> f x \<and> f x \<le> h x"
      using assms real_norm_def by metis
    then obtain d1 d2 where "gauge d1" "gauge d2"
            and d1: "\<And>p. \<lbrakk>p tagged_division_of cbox a b; d1 fine p\<rbrakk> \<Longrightarrow>
                          \<bar>(\<Sum>(x,K)\<in>p. content K *\<^sub>R g x) - i\<bar> < e/3"
            and d2: "\<And>p. \<lbrakk>p tagged_division_of cbox a b; d2 fine p\<rbrakk> \<Longrightarrow>
                          \<bar>(\<Sum>(x,K) \<in> p. content K *\<^sub>R h x) - j\<bar> < e/3"
      by (metis e has_integral real_norm_def)
    have "\<bar>(\<Sum>(x,K) \<in> p1. content K *\<^sub>R f x) - (\<Sum>(x,K) \<in> p2. content K *\<^sub>R f x)\<bar> < e"
      if p1: "p1 tagged_division_of cbox a b" and 11: "d1 fine p1" and 21: "d2 fine p1"
       and p2: "p2 tagged_division_of cbox a b" and 12: "d1 fine p2" and 22: "d2 fine p2" for p1 p2
    proof -
      have *: "\<And>g1 g2 h1 h2 f1 f2.
                  \<lbrakk>\<bar>g2 - i\<bar> < e/3; \<bar>g1 - i\<bar> < e/3; \<bar>h2 - j\<bar> < e/3; \<bar>h1 - j\<bar> < e/3;
                   g1 - h2 \<le> f1 - f2; f1 - f2 \<le> h1 - g2\<rbrakk>
                  \<Longrightarrow> \<bar>f1 - f2\<bar> < e"
        using \<open>e > 0\<close> ij by arith
      have 0: "(\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R g x) \<ge> 0"
              "0 \<le> (\<Sum>(x, k)\<in>p2. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x)"
              "(\<Sum>(x, k)\<in>p2. content k *\<^sub>R f x) - (\<Sum>(x, k)\<in>p2. content k *\<^sub>R g x) \<ge> 0"
              "0 \<le> (\<Sum>(x, k)\<in>p1. content k *\<^sub>R h x) - (\<Sum>(x, k)\<in>p1. content k *\<^sub>R f x)"
        unfolding sum_subtractf[symmetric]
           apply (auto intro!: sum_nonneg)
           apply (meson fgh measure_nonneg mult_left_mono tag_in_interval that sum_nonneg)+
        done
      show ?thesis
      proof (rule *)
        show "\<bar>(\<Sum>(x,K) \<in> p2. content K *\<^sub>R g x) - i\<bar> < e/3"
          by (rule d1[OF p2 12])
        show "\<bar>(\<Sum>(x,K) \<in> p1. content K *\<^sub>R g x) - i\<bar> < e/3"
          by (rule d1[OF p1 11])
        show "\<bar>(\<Sum>(x,K) \<in> p2. content K *\<^sub>R h x) - j\<bar> < e/3"
          by (rule d2[OF p2 22])
        show "\<bar>(\<Sum>(x,K) \<in> p1. content K *\<^sub>R h x) - j\<bar> < e/3"
          by (rule d2[OF p1 21])
      qed (use 0 in auto)
    qed
    then show ?thesis
      by (rule_tac x="\<lambda>x. d1 x \<inter> d2 x" in exI)
        (auto simp: fine_Int intro: \<open>gauge d1\<close> \<open>gauge d2\<close> d1 d2)
  qed
  then show ?thesis
    by (simp add: integrable_Cauchy)
qed

lemma integrable_straddle:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>g h i j. (g has_integral i) s \<and> (h has_integral j) s \<and>
                     \<bar>i - j\<bar> < e \<and> (\<forall>x\<in>s. g x \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on s"
proof -
  let ?fs = "(\<lambda>x. if x \<in> s then f x else 0)"
  have "?fs integrable_on cbox a b" for a b
  proof (rule integrable_straddle_interval)
    fix e::real
    assume "e > 0"
    then have *: "e/4 > 0"
      by auto
    with assms obtain g h i j where g: "(g has_integral i) s" and h: "(h has_integral j) s"
                 and ij: "\<bar>i - j\<bar> < e/4"
                 and fgh: "\<And>x. x \<in> s \<Longrightarrow> g x \<le> f x \<and> f x \<le> h x"
      by metis
    let ?gs = "(\<lambda>x. if x \<in> s then g x else 0)"
    let ?hs = "(\<lambda>x. if x \<in> s then h x else 0)"
    obtain Bg where Bg: "\<And>a b. ball 0 Bg \<subseteq> cbox a b \<Longrightarrow> \<bar>integral (cbox a b) ?gs - i\<bar> < e/4"
              and int_g: "\<And>a b. ?gs integrable_on cbox a b"
      using g * unfolding has_integral_alt' real_norm_def by meson
    obtain Bh where
          Bh: "\<And>a b. ball 0 Bh \<subseteq> cbox a b \<Longrightarrow> \<bar>integral (cbox a b) ?hs - j\<bar> < e/4"
         and int_h: "\<And>a b. ?hs integrable_on cbox a b"
      using h * unfolding has_integral_alt' real_norm_def by meson
    define c where "c = (\<Sum>i\<in>Basis. min (a\<bullet>i) (- (max Bg Bh)) *\<^sub>R i)"
    define d where "d = (\<Sum>i\<in>Basis. max (b\<bullet>i) (max Bg Bh) *\<^sub>R i)"
    have "\<lbrakk>norm (0 - x) < Bg; i \<in> Basis\<rbrakk> \<Longrightarrow> c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i" for x i
      using Basis_le_norm[of i x] unfolding c_def d_def by auto
    then have ballBg: "ball 0 Bg \<subseteq> cbox c d"
      by (auto simp: mem_box dist_norm)
    have "\<lbrakk>norm (0 - x) < Bh; i \<in> Basis\<rbrakk> \<Longrightarrow> c \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> d \<bullet> i" for x i
      using Basis_le_norm[of i x] unfolding c_def d_def by auto
    then have ballBh: "ball 0 Bh \<subseteq> cbox c d"
      by (auto simp: mem_box dist_norm)
    have ab_cd: "cbox a b \<subseteq> cbox c d"
      by (auto simp: c_def d_def subset_box_imp)
    have **: "\<And>ch cg ag ah::real. \<lbrakk>\<bar>ah - ag\<bar> \<le> \<bar>ch - cg\<bar>; \<bar>cg - i\<bar> < e/4; \<bar>ch - j\<bar> < e/4\<rbrakk>
       \<Longrightarrow> \<bar>ag - ah\<bar> < e"
      using ij by arith
    show "\<exists>g h i j. (g has_integral i) (cbox a b) \<and> (h has_integral j) (cbox a b) \<and> \<bar>i - j\<bar> < e \<and>
          (\<forall>x\<in>cbox a b. g x \<le> (if x \<in> s then f x else 0) \<and>
                        (if x \<in> s then f x else 0) \<le> h x)"
    proof (intro exI ballI conjI)
      have eq: "\<And>x f g. (if x \<in> s then f x else 0) - (if x \<in> s then g x else 0) =
                       (if x \<in> s then f x - g x else (0::real))"
        by auto
      have int_hg: "(\<lambda>x. if x \<in> s then h x - g x else 0) integrable_on cbox a b"
                   "(\<lambda>x. if x \<in> s then h x - g x else 0) integrable_on cbox c d"
        by (metis (no_types) integrable_diff g h has_integral_integrable integrable_altD(1))+
      show "(?gs has_integral integral (cbox a b) ?gs) (cbox a b)"
           "(?hs has_integral integral (cbox a b) ?hs) (cbox a b)"
        by (intro integrable_integral int_g int_h)+
      then have "integral (cbox a b) ?gs \<le> integral (cbox a b) ?hs"
        using fgh by (force intro: has_integral_le)
      then have "0 \<le> integral (cbox a b) ?hs - integral (cbox a b) ?gs"
        by simp
      then have "\<bar>integral (cbox a b) ?hs - integral (cbox a b) ?gs\<bar>
              \<le> \<bar>integral (cbox c d) ?hs - integral (cbox c d) ?gs\<bar>"
        apply (simp add: integral_diff [symmetric] int_g int_h)
        apply (subst abs_of_nonneg[OF integral_nonneg[OF integrable_diff, OF int_h int_g]])
        using fgh apply (force simp: eq intro!: integral_subset_le [OF ab_cd int_hg])+
        done
      then show "\<bar>integral (cbox a b) ?gs - integral (cbox a b) ?hs\<bar> < e"
        using ** Bg ballBg Bh ballBh by blast
      show "\<And>x. x \<in> cbox a b \<Longrightarrow> ?gs x \<le> ?fs x" "\<And>x. x \<in> cbox a b \<Longrightarrow> ?fs x \<le> ?hs x"
        using fgh by auto
    qed
  qed
  then have int_f: "?fs integrable_on cbox a b" for a b
    by simp
  have "\<exists>B>0. \<forall>a b c d.
                  ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
                  abs (integral (cbox a b) ?fs - integral (cbox c d) ?fs) < e"
      if "0 < e" for e
  proof -
    have *: "e/3 > 0"
      using that by auto
    with assms obtain g h i j where g: "(g has_integral i) s" and h: "(h has_integral j) s"
                 and ij: "\<bar>i - j\<bar> < e/3"
                 and fgh: "\<And>x. x \<in> s \<Longrightarrow> g x \<le> f x \<and> f x \<le> h x"
      by metis
    let ?gs = "(\<lambda>x. if x \<in> s then g x else 0)"
    let ?hs = "(\<lambda>x. if x \<in> s then h x else 0)"
    obtain Bg where "Bg > 0"
              and Bg: "\<And>a b. ball 0 Bg \<subseteq> cbox a b \<Longrightarrow> \<bar>integral (cbox a b) ?gs - i\<bar> < e/3"
              and int_g: "\<And>a b. ?gs integrable_on cbox a b"
      using g * unfolding has_integral_alt' real_norm_def by meson
    obtain Bh where "Bh > 0"
              and Bh: "\<And>a b. ball 0 Bh \<subseteq> cbox a b \<Longrightarrow> \<bar>integral (cbox a b) ?hs - j\<bar> < e/3"
              and int_h: "\<And>a b. ?hs integrable_on cbox a b"
      using h * unfolding has_integral_alt' real_norm_def by meson
    { fix a b c d :: 'n
      assume as: "ball 0 (max Bg Bh) \<subseteq> cbox a b" "ball 0 (max Bg Bh) \<subseteq> cbox c d"
      have **: "ball 0 Bg \<subseteq> ball (0::'n) (max Bg Bh)" "ball 0 Bh \<subseteq> ball (0::'n) (max Bg Bh)"
        by auto
      have *: "\<And>ga gc ha hc fa fc. \<lbrakk>\<bar>ga - i\<bar> < e/3; \<bar>gc - i\<bar> < e/3; \<bar>ha - j\<bar> < e/3;
                     \<bar>hc - j\<bar> < e/3; ga \<le> fa; fa \<le> ha; gc \<le> fc; fc \<le> hc\<rbrakk> \<Longrightarrow>
        \<bar>fa - fc\<bar> < e"
        using ij by arith
      have "abs (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)
        (\<lambda>x. if x \<in> s then f x else 0)) < e"
      proof (rule *)
        show "\<bar>integral (cbox a b) ?gs - i\<bar> < e/3"
          using "**" Bg as by blast
        show "\<bar>integral (cbox c d) ?gs - i\<bar> < e/3"
          using "**" Bg as by blast
        show "\<bar>integral (cbox a b) ?hs - j\<bar> < e/3"
          using "**" Bh as by blast
        show "\<bar>integral (cbox c d) ?hs - j\<bar> < e/3"
          using "**" Bh as by blast
      qed (use int_f int_g int_h fgh in \<open>simp_all add: integral_le\<close>)
    }
    then show ?thesis
      apply (rule_tac x="max Bg Bh" in exI)
        using \<open>Bg > 0\<close> by auto
  qed
  then show ?thesis
    unfolding integrable_alt[of f] real_norm_def by (blast intro: int_f)
qed


subsection \<open>Adding integrals over several sets\<close>

lemma has_integral_Un:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "(f has_integral i) S" "(f has_integral j) T"
    and neg: "negligible (S \<inter> T)"
  shows "(f has_integral (i + j)) (S \<union> T)"
  unfolding has_integral_restrict_UNIV[symmetric, of f]
proof (rule has_integral_spike[OF neg])
  let ?f = "\<lambda>x. (if x \<in> S then f x else 0) + (if x \<in> T then f x else 0)"
  show "(?f has_integral i + j) UNIV"
    by (simp add: f has_integral_add)
qed auto

lemma integral_Un [simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S" "f integrable_on T" "negligible (S \<inter> T)"
  shows "integral (S \<union> T) f = integral S f + integral T f"
  by (simp add: has_integral_Un assms integrable_integral integral_unique)

lemma integrable_Un:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "negligible (A \<inter> B)" "f integrable_on A" "f integrable_on B"
  shows   "f integrable_on (A \<union> B)"
proof -
  from assms obtain y z where "(f has_integral y) A" "(f has_integral z) B"
     by (auto simp: integrable_on_def)
  from has_integral_Un[OF this assms(1)] show ?thesis by (auto simp: integrable_on_def)
qed

lemma integrable_Un':
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "f integrable_on A" "f integrable_on B" "negligible (A \<inter> B)" "C = A \<union> B"
  shows   "f integrable_on C"
  using integrable_Un[of A B f] assms by simp

lemma has_integral_Union:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes \<T>: "finite \<T>"
    and int: "\<And>S. S \<in> \<T> \<Longrightarrow> (f has_integral (i S)) S"
    and neg: "pairwise (\<lambda>S S'. negligible (S \<inter> S')) \<T>"
  shows "(f has_integral (sum i \<T>)) (\<Union>\<T>)"
proof -
  let ?\<U> = "((\<lambda>(a,b). a \<inter> b) ` {(a,b). a \<in> \<T> \<and> b \<in> {y. y \<in> \<T> \<and> a \<noteq> y}})"
  have "((\<lambda>x. if x \<in> \<Union>\<T> then f x else 0) has_integral sum i \<T>) UNIV"
  proof (rule has_integral_spike)
    show "negligible (\<Union>?\<U>)"
    proof (rule negligible_Union)
      have "finite (\<T> \<times> \<T>)"
        by (simp add: \<T>)
      moreover have "{(a, b). a \<in> \<T> \<and> b \<in> {y \<in> \<T>. a \<noteq> y}} \<subseteq> \<T> \<times> \<T>"
        by auto
      ultimately show "finite ?\<U>"
        by (blast intro: finite_subset[of _ "\<T> \<times> \<T>"])
      show "\<And>t. t \<in> ?\<U> \<Longrightarrow> negligible t"
        using neg unfolding pairwise_def by auto
    qed
  next
    show "(if x \<in> \<Union>\<T> then f x else 0) = (\<Sum>A\<in>\<T>. if x \<in> A then f x else 0)"
      if "x \<in> UNIV - (\<Union>?\<U>)" for x
    proof clarsimp
      fix S assume "S \<in> \<T>" "x \<in> S"
      moreover then have "\<forall>b\<in>\<T>. x \<in> b \<longleftrightarrow> b = S"
        using that by blast
      ultimately show "f x = (\<Sum>A\<in>\<T>. if x \<in> A then f x else 0)"
        by (simp add: sum.delta[OF \<T>])
    qed
  next
    show "((\<lambda>x. \<Sum>A\<in>\<T>. if x \<in> A then f x else 0) has_integral (\<Sum>A\<in>\<T>. i A)) UNIV"
      using int by (simp add: has_integral_restrict_UNIV has_integral_sum [OF \<T>])
  qed
  then show ?thesis
    using has_integral_restrict_UNIV by blast
qed


text \<open>In particular adding integrals over a division, maybe not of an interval.\<close>

lemma has_integral_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<D> division_of S"
    and "\<And>k. k \<in> \<D> \<Longrightarrow> (f has_integral (i k)) k"
  shows "(f has_integral (sum i \<D>)) S"
proof -
  note \<D> = division_ofD[OF assms(1)]
  have neg: "negligible (S \<inter> s')" if "S \<in> \<D>" "s' \<in> \<D>" "S \<noteq> s'" for S s'
  proof -
    obtain a c b \<D> where obt: "S = cbox a b" "s' = cbox c \<D>"
      by (meson \<open>S \<in> \<D>\<close> \<open>s' \<in> \<D>\<close> \<D>(4))
    from \<D>(5)[OF that] show ?thesis
      unfolding obt interior_cbox
      by (metis (no_types, lifting) Diff_empty Int_interval box_Int_box negligible_frontier_interval)
  qed
  show ?thesis
    unfolding \<D>(6)[symmetric]
    by (auto intro: \<D> neg assms has_integral_Union pairwiseI)
qed

lemma integral_combine_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<D> division_of S" "\<And>k. k \<in> \<D> \<Longrightarrow> f integrable_on k"
  shows "integral S f = sum (\<lambda>i. integral i f) \<D>"
  by (meson assms integral_unique has_integral_combine_division has_integral_integrable_integral)

lemma has_integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on S"
    and \<D>: "\<D> division_of K"
    and "K \<subseteq> S"
  shows "(f has_integral (sum (\<lambda>i. integral i f) \<D>)) K"
proof -
  have "f integrable_on L" if "L \<in> \<D>" for L
  proof -
    have "L \<subseteq> S"
      using \<open>K \<subseteq> S\<close> \<D> that by blast
    then show "f integrable_on L"
      using that by (metis (no_types) f \<D> division_ofD(4) integrable_on_subcbox)
  qed
  then show ?thesis
    by (meson \<D> has_integral_combine_division has_integral_integrable_integral)
qed

lemma integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S"
    and "\<D> division_of S"
  shows "integral S f = sum (\<lambda>i. integral i f) \<D>"
  using assms has_integral_combine_division_topdown by blast

lemma integrable_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes \<D>: "\<D> division_of S"
    and f: "\<And>i. i \<in> \<D> \<Longrightarrow> f integrable_on i"
  shows "f integrable_on S"
  using f unfolding integrable_on_def by (metis has_integral_combine_division[OF \<D>])

lemma integrable_on_subdivision:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes \<D>: "\<D> division_of i"
    and f: "f integrable_on S"
    and "i \<subseteq> S"
  shows "f integrable_on i"
proof -
  have "f integrable_on i" if "i \<in> \<D>" for i
proof -
  have "i \<subseteq> S"
    using assms that by auto
  then show "f integrable_on i"
    using that by (metis (no_types) \<D> f division_ofD(4) integrable_on_subcbox)
qed
  then show ?thesis
    using \<D> integrable_combine_division by blast
qed


subsection \<open>Also tagged divisions\<close>

lemma has_integral_combine_tagged_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of S"
    and "\<And>x k. (x,k) \<in> p \<Longrightarrow> (f has_integral (i k)) k"
  shows "(f has_integral (\<Sum>(x,k)\<in>p. i k)) S"
proof -
  have *: "(f has_integral (\<Sum>k\<in>snd`p. integral k f)) S"
  proof -
    have "snd ` p division_of S"
      by (simp add: assms(1) division_of_tagged_division)
    with assms show ?thesis
      by (metis (mono_tags, lifting) has_integral_combine_division has_integral_integrable_integral imageE prod.collapse)
  qed
  also have "(\<Sum>k\<in>snd`p. integral k f) = (\<Sum>(x, k)\<in>p. integral k f)"
    by (intro sum.over_tagged_division_lemma[OF assms(1), symmetric] integral_null)
       (simp add: content_eq_0_interior)
  finally show ?thesis
    using assms by (auto simp add: has_integral_iff intro!: sum.cong)
qed

lemma integral_combine_tagged_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes p: "p tagged_division_of (cbox a b)"
    and f: "\<And>x k. (x,k)\<in>p \<Longrightarrow> f integrable_on k"
  shows "integral (cbox a b) f = sum (\<lambda>(x,k). integral k f) p"
  by (simp add: has_integral_combine_tagged_division[OF p] integral_unique f integrable_integral)

lemma has_integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on cbox a b"
    and p: "p tagged_division_of (cbox a b)"
  shows "(f has_integral (sum (\<lambda>(x,K). integral K f) p)) (cbox a b)"
proof -
  have "(f has_integral integral K f) K" if "(x,K) \<in> p" for x K
    by (metis assms integrable_integral integrable_on_subcbox tagged_division_ofD(3,4) that)
  then show ?thesis
    by (simp add: has_integral_combine_tagged_division p)
qed

lemma integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "integral (cbox a b) f = sum (\<lambda>(x,k). integral k f) p"
  using assms by (auto intro: integral_unique [OF has_integral_combine_tagged_division_topdown])


subsection \<open>Henstock's lemma\<close>

lemma Henstock_lemma_part1:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and less_e: "\<And>p. \<lbrakk>p tagged_division_of (cbox a b); d fine p\<rbrakk> \<Longrightarrow>
                     norm (sum (\<lambda>(x,K). content K *\<^sub>R f x) p - integral(cbox a b) f) < e"
    and p: "p tagged_partial_division_of (cbox a b)" "d fine p"
  shows "norm (sum (\<lambda>(x,K). content K *\<^sub>R f x - integral K f) p) \<le> e" (is "?lhs \<le> e")
proof (rule field_le_epsilon)
  fix k :: real
  assume "k > 0"
  let ?SUM = "\<lambda>p. (\<Sum>(x,K) \<in> p. content K *\<^sub>R f x)"
  note p' = tagged_partial_division_ofD[OF p(1)]
  have "\<Union>(snd ` p) \<subseteq> cbox a b"
    using p'(3) by fastforce
  then obtain q where q: "snd ` p \<subseteq> q" and qdiv: "q division_of cbox a b"
    by (meson p(1) partial_division_extend_interval partial_division_of_tagged_division)
  note q' = division_ofD[OF qdiv]
  define r where "r = q - snd ` p"
  have "snd ` p \<inter> r = {}"
    unfolding r_def by auto
  have "finite r"
    using q' unfolding r_def by auto
  have "\<exists>p. p tagged_division_of i \<and> d fine p \<and>
        norm (?SUM p - integral i f) < k / (real (card r) + 1)"
    if "i\<in>r" for i
  proof -
    have gt0: "k / (real (card r) + 1) > 0" using \<open>k > 0\<close> by simp
    have i: "i \<in> q"
      using that unfolding r_def by auto
    then obtain u v where uv: "i = cbox u v"
      using q'(4) by blast
    then have "cbox u v \<subseteq> cbox a b"
      using i q'(2) by auto  
    then have "f integrable_on cbox u v"
      by (rule integrable_subinterval[OF intf])
    with integrable_integral[OF this, unfolded has_integral[of f]]
    obtain dd where "gauge dd" and dd:
      "\<And>\<D>. \<lbrakk>\<D> tagged_division_of cbox u v; dd fine \<D>\<rbrakk> \<Longrightarrow>
    norm (?SUM \<D> - integral (cbox u v) f) < k / (real (card r) + 1)"
      using gt0 by auto
    with gauge_Int[OF \<open>gauge d\<close> \<open>gauge dd\<close>]
    obtain qq where qq: "qq tagged_division_of cbox u v" "(\<lambda>x. d x \<inter> dd x) fine qq"
      using fine_division_exists by blast
    with dd[of qq]  show ?thesis
      by (auto simp: fine_Int uv)
  qed
  then obtain qq where qq: "\<And>i. i \<in> r \<Longrightarrow> qq i tagged_division_of i \<and>
      d fine qq i \<and> norm (?SUM (qq i) - integral i f) < k / (real (card r) + 1)"
    by metis

  let ?p = "p \<union> \<Union>(qq ` r)"
  have "norm (?SUM ?p - integral (cbox a b) f) < e"
  proof (rule less_e)
    show "d fine ?p"
      by (metis (mono_tags, hide_lams) qq fine_Un fine_Union imageE p(2))
    note ptag = tagged_partial_division_of_Union_self[OF p(1)]
    have "p \<union> \<Union>(qq ` r) tagged_division_of \<Union>(snd ` p) \<union> \<Union>r"
    proof (rule tagged_division_Un[OF ptag tagged_division_Union [OF \<open>finite r\<close>]])
      show "\<And>i. i \<in> r \<Longrightarrow> qq i tagged_division_of i"
        using qq by auto
      show "\<And>i1 i2. \<lbrakk>i1 \<in> r; i2 \<in> r; i1 \<noteq> i2\<rbrakk> \<Longrightarrow> interior i1 \<inter> interior i2 = {}"
        by (simp add: q'(5) r_def)
      show "interior (\<Union>(snd ` p)) \<inter> interior (\<Union>r) = {}"
      proof (rule Int_interior_Union_intervals [OF \<open>finite r\<close>])
        show "open (interior (\<Union>(snd ` p)))"
          by blast
        show "\<And>T. T \<in> r \<Longrightarrow> \<exists>a b. T = cbox a b"
          by (simp add: q'(4) r_def)
        have "interior T \<inter> interior (\<Union>(snd ` p)) = {}" if "T \<in> r" for T
        proof (rule Int_interior_Union_intervals)
          show "\<And>U. U \<in> snd ` p \<Longrightarrow> \<exists>a b. U = cbox a b"
            using q q'(4) by blast
          show "\<And>U. U \<in> snd ` p \<Longrightarrow> interior T \<inter> interior U = {}"
            by (metis DiffE q q'(5) r_def subsetD that)
        qed (use p' in auto)
        then show "\<And>T. T \<in> r \<Longrightarrow> interior (\<Union>(snd ` p)) \<inter> interior T = {}"
          by (metis Int_commute)
      qed
    qed
    moreover have "\<Union>(snd ` p) \<union> \<Union>r = cbox a b" and "{qq i |i. i \<in> r} = qq ` r"
      using qdiv q unfolding Union_Un_distrib[symmetric] r_def by auto
    ultimately show "?p tagged_division_of (cbox a b)"
      by fastforce
  qed
  then have "norm (?SUM p + (?SUM (\<Union>(qq ` r))) - integral (cbox a b) f) < e"
  proof (subst sum.union_inter_neutral[symmetric, OF \<open>finite p\<close>], safe)
    show "content L *\<^sub>R f x = 0" if "(x, L) \<in> p" "(x, L) \<in> qq K" "K \<in> r" for x K L 
    proof -
      obtain u v where uv: "L = cbox u v"
        using \<open>(x,L) \<in> p\<close> p'(4) by blast
      have "L \<subseteq> K"
        using  qq[OF that(3)] tagged_division_ofD(3) \<open>(x,L) \<in> qq K\<close> by metis
      have "L \<in> snd ` p" 
        using \<open>(x,L) \<in> p\<close> image_iff by fastforce 
      then have "L \<in> q" "K \<in> q" "L \<noteq> K"
        using that(1,3) q(1) unfolding r_def by auto
      with q'(5) have "interior L = {}"
        using interior_mono[OF \<open>L \<subseteq> K\<close>] by blast
      then show "content L *\<^sub>R f x = 0"
        unfolding uv content_eq_0_interior[symmetric] by auto
    qed
    show "finite (\<Union>(qq ` r))"
      by (meson finite_UN qq \<open>finite r\<close> tagged_division_of_finite)
  qed
  moreover have "content M *\<^sub>R f x = 0" 
      if x: "(x,M) \<in> qq K" "(x,M) \<in> qq L" and KL: "qq K \<noteq> qq L" and r: "K \<in> r" "L \<in> r"
    for x M K L
  proof -
    note kl = tagged_division_ofD(3,4)[OF qq[THEN conjunct1]]
    obtain u v where uv: "M = cbox u v"
      using \<open>(x, M) \<in> qq L\<close> \<open>L \<in> r\<close> kl(2) by blast
    have empty: "interior (K \<inter> L) = {}"
      by (metis DiffD1 interior_Int q'(5) r_def KL r)
    have "interior M = {}"
      by (metis (no_types, lifting) Int_assoc empty inf.absorb_iff2 interior_Int kl(1) subset_empty x r)
    then show "content M *\<^sub>R f x = 0"
      unfolding uv content_eq_0_interior[symmetric]
      by auto
  qed 
  ultimately have "norm (?SUM p + sum ?SUM (qq ` r) - integral (cbox a b) f) < e"
    apply (subst (asm) sum.Union_comp)
    using qq by (force simp: split_paired_all)+
  moreover have "content M *\<^sub>R f x = 0" 
       if "K \<in> r" "L \<in> r" "K \<noteq> L" "qq K = qq L" "(x, M) \<in> qq K" for K L x M
    using tagged_division_ofD(6) qq that by (metis (no_types, lifting)) 
  ultimately have less_e: "norm (?SUM p + sum (?SUM \<circ> qq) r - integral (cbox a b) f) < e"
  proof (subst (asm) sum.reindex_nontrivial [OF \<open>finite r\<close>])
    qed (auto simp: split_paired_all sum.neutral)
  have norm_le: "norm (cp - ip) \<le> e + k"
                  if "norm ((cp + cr) - i) < e" "norm (cr - ir) < k" "ip + ir = i"
                  for ir ip i cr cp::'a
  proof -
    from that show ?thesis
      using norm_triangle_le[of "cp + cr - i" "- (cr - ir)"]
      unfolding that(3)[symmetric] norm_minus_cancel
      by (auto simp add: algebra_simps)
  qed

  have "?lhs =  norm (?SUM p - (\<Sum>(x, k)\<in>p. integral k f))"
    unfolding split_def sum_subtractf ..
  also have "\<dots> \<le> e + k"
  proof (rule norm_le[OF less_e])
    have lessk: "k * real (card r) / (1 + real (card r)) < k"
      using \<open>k>0\<close> by (auto simp add: field_simps)
    have "norm (sum (?SUM \<circ> qq) r - (\<Sum>k\<in>r. integral k f)) \<le> (\<Sum>x\<in>r. k / (real (card r) + 1))"
      unfolding sum_subtractf[symmetric] by (force dest: qq intro!: sum_norm_le)
    also have "... < k"
      by (simp add: lessk add.commute mult.commute)
    finally show "norm (sum (?SUM \<circ> qq) r - (\<Sum>k\<in>r. integral k f)) < k" .
  next
    from q(1) have [simp]: "snd ` p \<union> q = q" by auto
    have "integral l f = 0"
      if inp: "(x, l) \<in> p" "(y, m) \<in> p" and ne: "(x, l) \<noteq> (y, m)" and "l = m" for x l y m
    proof -
      obtain u v where uv: "l = cbox u v"
        using inp p'(4) by blast
      have "content (cbox u v) = 0"
        unfolding content_eq_0_interior using that p(1) uv
        by (auto dest: tagged_partial_division_ofD)
      then show ?thesis
        using uv by blast
    qed
    then have "(\<Sum>(x, K)\<in>p. integral K f) = (\<Sum>K\<in>snd ` p. integral K f)"
      apply (subst sum.reindex_nontrivial [OF \<open>finite p\<close>])
      unfolding split_paired_all split_def by auto
    then show "(\<Sum>(x, k)\<in>p. integral k f) + (\<Sum>k\<in>r. integral k f) = integral (cbox a b) f"
      unfolding integral_combine_division_topdown[OF intf qdiv] r_def
      using q'(1) p'(1) sum.union_disjoint [of "snd ` p" "q - snd ` p", symmetric]
        by simp
  qed
  finally show "?lhs \<le> e + k" .
qed

lemma Henstock_lemma_part2:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes fed: "f integrable_on cbox a b" "e > 0" "gauge d"
    and less_e: "\<And>\<D>. \<lbrakk>\<D> tagged_division_of (cbox a b); d fine \<D>\<rbrakk> \<Longrightarrow>
                     norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) \<D> - integral (cbox a b) f) < e"
    and tag: "p tagged_partial_division_of (cbox a b)"
    and "d fine p"
  shows "sum (\<lambda>(x,k). norm (content k *\<^sub>R f x - integral k f)) p \<le> 2 * real (DIM('n)) * e"
proof -
  have "finite p"
    using tag tagged_partial_division_ofD by blast
  then show ?thesis
    unfolding split_def
  proof (rule sum_norm_allsubsets_bound)
    fix Q
    assume Q: "Q \<subseteq> p"
    then have fine: "d fine Q"
      by (simp add: \<open>d fine p\<close> fine_subset)
    show "norm (\<Sum>x\<in>Q. content (snd x) *\<^sub>R f (fst x) - integral (snd x) f) \<le> e"
      apply (rule Henstock_lemma_part1[OF fed less_e, unfolded split_def])
      using Q tag tagged_partial_division_subset by (force simp add: fine)+
  qed
qed

lemma Henstock_lemma:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes intf: "f integrable_on cbox a b"
    and "e > 0"
  obtains \<gamma> where "gauge \<gamma>"
    and "\<And>p. \<lbrakk>p tagged_partial_division_of (cbox a b); \<gamma> fine p\<rbrakk> \<Longrightarrow>
             sum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p < e"
proof -
  have *: "e/(2 * (real DIM('n) + 1)) > 0" using \<open>e > 0\<close> by simp
  with integrable_integral[OF intf, unfolded has_integral]
  obtain \<gamma> where "gauge \<gamma>"
    and \<gamma>: "\<And>\<D>. \<lbrakk>\<D> tagged_division_of cbox a b; \<gamma> fine \<D>\<rbrakk> \<Longrightarrow>
         norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f x) - integral (cbox a b) f)
         < e/(2 * (real DIM('n) + 1))"
    by metis
  show thesis
  proof (rule that [OF \<open>gauge \<gamma>\<close>])
    fix p
    assume p: "p tagged_partial_division_of cbox a b" "\<gamma> fine p"
    have "(\<Sum>(x,K)\<in>p. norm (content K *\<^sub>R f x - integral K f)) 
          \<le> 2 * real DIM('n) * (e/(2 * (real DIM('n) + 1)))"
      using Henstock_lemma_part2[OF intf * \<open>gauge \<gamma>\<close> \<gamma> p] by metis
    also have "... < e"
      using \<open>e > 0\<close> by (auto simp add: field_simps)
    finally
    show "(\<Sum>(x,K)\<in>p. norm (content K *\<^sub>R f x - integral K f)) < e" .
  qed
qed


subsection \<open>Monotone convergence (bounded interval first)\<close>

lemma bounded_increasing_convergent:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>bounded (range f); \<And>n. f n \<le> f (Suc n)\<rbrakk> \<Longrightarrow> \<exists>l. f \<longlonglongrightarrow> l"
  using Bseq_mono_convergent[of f] incseq_Suc_iff[of f]
  by (auto simp: image_def Bseq_eq_bounded convergent_def incseq_def)

lemma monotone_convergence_interval:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes intf: "\<And>k. (f k) integrable_on cbox a b"
    and le: "\<And>k x. x \<in> cbox a b \<Longrightarrow> (f k x) \<le> f (Suc k) x"
    and fg: "\<And>x. x \<in> cbox a b \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range (\<lambda>k. integral (cbox a b) (f k)))"
  shows "g integrable_on cbox a b \<and> ((\<lambda>k. integral (cbox a b) (f k)) \<longlongrightarrow> integral (cbox a b) g) sequentially"
proof (cases "content (cbox a b) = 0")
  case True then show ?thesis
    by auto
next
  case False
  have fg1: "(f k x) \<le> (g x)" if x: "x \<in> cbox a b" for x k
  proof -
    have "\<forall>\<^sub>F j in sequentially. f k x \<le> f j x"
    proof (rule eventually_sequentiallyI [of k])
      show "\<And>j. k \<le> j \<Longrightarrow> f k x \<le> f j x"
        using le x by (force intro: transitive_stepwise_le)
    qed
    then show "f k x \<le> g x"
      using tendsto_lowerbound [OF fg] x trivial_limit_sequentially by blast
  qed
  have int_inc: "\<And>n. integral (cbox a b) (f n) \<le> integral (cbox a b) (f (Suc n))"
    by (metis integral_le intf le)
  then obtain i where i: "(\<lambda>k. integral (cbox a b) (f k)) \<longlonglongrightarrow> i"
    using bounded_increasing_convergent bou by blast
  have "\<And>k. \<forall>\<^sub>F x in sequentially. integral (cbox a b) (f k) \<le> integral (cbox a b) (f x)"
    unfolding eventually_sequentially
    by (force intro: transitive_stepwise_le int_inc)
  then have i': "\<And>k. (integral(cbox a b) (f k)) \<le> i"
    using tendsto_le [OF trivial_limit_sequentially i] by blast
  have "(g has_integral i) (cbox a b)"
    unfolding has_integral real_norm_def
  proof clarify
    fix e::real
    assume e: "e > 0"
    have "\<And>k. (\<exists>\<gamma>. gauge \<gamma> \<and> (\<forall>\<D>. \<D> tagged_division_of (cbox a b) \<and> \<gamma> fine \<D> \<longrightarrow>
      abs ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f k x) - integral (cbox a b) (f k)) < e/2 ^ (k + 2)))"
      using intf e by (auto simp: has_integral_integral has_integral)
    then obtain c where c: "\<And>x. gauge (c x)"
          "\<And>x \<D>. \<lbrakk>\<D> tagged_division_of cbox a b; c x fine \<D>\<rbrakk> \<Longrightarrow>
              abs ((\<Sum>(u,K)\<in>\<D>. content K *\<^sub>R f x u) - integral (cbox a b) (f x))
              < e/2 ^ (x + 2)"
      by metis

    have "\<exists>r. \<forall>k\<ge>r. 0 \<le> i - (integral (cbox a b) (f k)) \<and> i - (integral (cbox a b) (f k)) < e/4"
    proof -
      have "e/4 > 0"
        using e by auto
      show ?thesis
        using LIMSEQ_D [OF i \<open>e/4 > 0\<close>] i' by auto
    qed
    then obtain r where r: "\<And>k. r \<le> k \<Longrightarrow> 0 \<le> i - integral (cbox a b) (f k)"
                       "\<And>k. r \<le> k \<Longrightarrow> i - integral (cbox a b) (f k) < e/4" 
      by metis
    have "\<exists>n\<ge>r. \<forall>k\<ge>n. 0 \<le> (g x) - (f k x) \<and> (g x) - (f k x) < e/(4 * content(cbox a b))"
      if "x \<in> cbox a b" for x
    proof -
      have "e/(4 * content (cbox a b)) > 0"
        by (simp add: False content_lt_nz e)
      with fg that LIMSEQ_D
      obtain N where "\<forall>n\<ge>N. norm (f n x - g x) < e/(4 * content (cbox a b))"
        by metis
      then show "\<exists>n\<ge>r. \<forall>k\<ge>n. 0 \<le> g x - f k x \<and> g x - f k x < e/(4 * content (cbox a b))"
        apply (rule_tac x="N + r" in exI)
        using fg1[OF that] by (auto simp add: field_simps)
    qed
    then obtain m where r_le_m: "\<And>x. x \<in> cbox a b \<Longrightarrow> r \<le> m x"
       and m: "\<And>x k. \<lbrakk>x \<in> cbox a b; m x \<le> k\<rbrakk>
                     \<Longrightarrow> 0 \<le> g x - f k x \<and> g x - f k x < e/(4 * content (cbox a b))"
      by metis
    define d where "d x = c (m x) x" for x
    show "\<exists>\<gamma>. gauge \<gamma> \<and>
             (\<forall>\<D>. \<D> tagged_division_of cbox a b \<and>
                  \<gamma> fine \<D> \<longrightarrow> abs ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - i) < e)"
    proof (rule exI, safe)
      show "gauge d"
        using c(1) unfolding gauge_def d_def by auto
    next
      fix \<D>
      assume ptag: "\<D> tagged_division_of (cbox a b)" and "d fine \<D>"
      note p'=tagged_division_ofD[OF ptag]
      obtain s where s: "\<And>x. x \<in> \<D> \<Longrightarrow> m (fst x) \<le> s"
        by (metis finite_imageI finite_nat_set_iff_bounded_le p'(1) rev_image_eqI)
      have *: "\<bar>a - d\<bar> < e" if "\<bar>a - b\<bar> \<le> e/4" "\<bar>b - c\<bar> < e/2" "\<bar>c - d\<bar> < e/4" for a b c d
        using that norm_triangle_lt[of "a - b" "b - c" "3* e/4"]
          norm_triangle_lt[of "a - b + (b - c)" "c - d" e]
        by (auto simp add: algebra_simps)
      show "\<bar>(\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - i\<bar> < e"
      proof (rule *)
        have "\<bar>(\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f (m x) x)\<bar> 
              \<le> (\<Sum>i\<in>\<D>. \<bar>(case i of (x, K) \<Rightarrow> content K *\<^sub>R g x) - (case i of (x, K) \<Rightarrow> content K *\<^sub>R f (m x) x)\<bar>)"
          by (metis (mono_tags) sum_subtractf sum_abs) 
        also have "... \<le> (\<Sum>(x, k)\<in>\<D>. content k * (e/(4 * content (cbox a b))))"
        proof (rule sum_mono, simp add: split_paired_all)
          fix x K
          assume xk: "(x,K) \<in> \<D>"
          with ptag have x: "x \<in> cbox a b"
            by blast
          then have "abs (content K * (g x - f (m x) x)) \<le> content K * (e/(4 * content (cbox a b)))"
            by (metis m[OF x] mult_nonneg_nonneg abs_of_nonneg less_eq_real_def measure_nonneg mult_left_mono order_refl)
          then show "\<bar>content K * g x - content K * f (m x) x\<bar> \<le> content K * e/(4 * content (cbox a b))"
            by (simp add: algebra_simps)
        qed
        also have "... = (e/(4 * content (cbox a b))) * (\<Sum>(x, k)\<in>\<D>. content k)"
          by (simp add: sum_distrib_left sum_divide_distrib split_def mult.commute)
        also have "... \<le> e/4"
          by (metis False additive_content_tagged_division [OF ptag] nonzero_mult_divide_mult_cancel_right order_refl times_divide_eq_left)
        finally show "\<bar>(\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R g x) - (\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f (m x) x)\<bar> \<le> e/4" .

      next
        have "norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f (m x) x) - (\<Sum>(x,K)\<in>\<D>. integral K (f (m x))))
              \<le> norm (\<Sum>j = 0..s. \<Sum>(x,K)\<in>{xk \<in> \<D>. m (fst xk) = j}. content K *\<^sub>R f (m x) x - integral K (f (m x)))"
          apply (subst sum.group)
          using s by (auto simp: sum_subtractf split_def p'(1))
        also have "\<dots> < e/2"
        proof -
          have "norm (\<Sum>j = 0..s. \<Sum>(x, k)\<in>{xk \<in> \<D>. m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x)))
                \<le> (\<Sum>i = 0..s. e/2 ^ (i + 2))"
          proof (rule sum_norm_le)
            fix t
            assume "t \<in> {0..s}"
            have "norm (\<Sum>(x,k)\<in>{xk \<in> \<D>. m (fst xk) = t}. content k *\<^sub>R f (m x) x - integral k (f (m x))) =
                  norm (\<Sum>(x,k)\<in>{xk \<in> \<D>. m (fst xk) = t}. content k *\<^sub>R f t x - integral k (f t))"
              by (force intro!: sum.cong arg_cong[where f=norm])
            also have "... \<le> e/2 ^ (t + 2)"
            proof (rule Henstock_lemma_part1 [OF intf])
              show "{xk \<in> \<D>. m (fst xk) = t} tagged_partial_division_of cbox a b"
              proof (rule tagged_partial_division_subset[of \<D>])
                show "\<D> tagged_partial_division_of cbox a b"
                  using ptag tagged_division_of_def by blast
              qed auto
              show "c t fine {xk \<in> \<D>. m (fst xk) = t}"
                using \<open>d fine \<D>\<close> by (auto simp: fine_def d_def)
            qed (use c e in auto)
            finally show "norm (\<Sum>(x,K)\<in>{xk \<in> \<D>. m (fst xk) = t}. content K *\<^sub>R f (m x) x -
                                integral K (f (m x))) \<le> e/2 ^ (t + 2)" .
          qed
          also have "... = (e/2/2) * (\<Sum>i = 0..s. (1/2) ^ i)"
            by (simp add: sum_distrib_left field_simps)
          also have "\<dots> < e/2"
            by (simp add: sum_gp mult_strict_left_mono[OF _ e])
          finally show "norm (\<Sum>j = 0..s. \<Sum>(x, k)\<in>{xk \<in> \<D>.
            m (fst xk) = j}. content k *\<^sub>R f (m x) x - integral k (f (m x))) < e/2" .
        qed 
        finally show "\<bar>(\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f (m x) x) - (\<Sum>(x,K)\<in>\<D>. integral K (f (m x)))\<bar> < e/2"
          by simp
      next
        have comb: "integral (cbox a b) (f y) = (\<Sum>(x, k)\<in>\<D>. integral k (f y))" for y
          using integral_combine_tagged_division_topdown[OF intf ptag] by metis
        have f_le: "\<And>y m n. \<lbrakk>y \<in> cbox a b; n\<ge>m\<rbrakk> \<Longrightarrow> f m y \<le> f n y"
          using le by (auto intro: transitive_stepwise_le)        
        have "(\<Sum>(x, k)\<in>\<D>. integral k (f r)) \<le> (\<Sum>(x, K)\<in>\<D>. integral K (f (m x)))"
        proof (rule sum_mono, simp add: split_paired_all)
          fix x K
          assume xK: "(x, K) \<in> \<D>"
          show "integral K (f r) \<le> integral K (f (m x))"
          proof (rule integral_le)
            show "f r integrable_on K"
              by (metis integrable_on_subcbox intf p'(3) p'(4) xK)
            show "f (m x) integrable_on K"
              by (metis elementary_interval integrable_on_subdivision intf p'(3) p'(4) xK)
            show "f r y \<le> f (m x) y" if "y \<in> K" for y
              using that r_le_m[of x] p'(2-3)[OF xK] f_le by auto
          qed
        qed
        moreover have "(\<Sum>(x, K)\<in>\<D>. integral K (f (m x))) \<le> (\<Sum>(x, k)\<in>\<D>. integral k (f s))"
        proof (rule sum_mono, simp add: split_paired_all)
          fix x K
          assume xK: "(x, K) \<in> \<D>"
          show "integral K (f (m x)) \<le> integral K (f s)"
          proof (rule integral_le)
            show "f (m x) integrable_on K"
              by (metis elementary_interval integrable_on_subdivision intf p'(3) p'(4) xK)
            show "f s integrable_on K"
              by (metis integrable_on_subcbox intf p'(3) p'(4) xK)
            show "f (m x) y \<le> f s y" if "y \<in> K" for y
              using that s xK f_le p'(3) by fastforce
          qed
        qed
        moreover have "0 \<le> i - integral (cbox a b) (f r)" "i - integral (cbox a b) (f r) < e/4"
          using r by auto
        ultimately show "\<bar>(\<Sum>(x,K)\<in>\<D>. integral K (f (m x))) - i\<bar> < e/4"
          using comb i'[of s] by auto
      qed
    qed
  qed 
  with i integral_unique show ?thesis
    by blast
qed

lemma monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes int_f: "\<And>k. (f k) integrable_on S"
    and "\<And>k x. x \<in> S \<Longrightarrow> (f k x) \<le> (f (Suc k) x)"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range (\<lambda>k. integral S (f k)))"
  shows "g integrable_on S \<and> ((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) sequentially"
proof -
  have lem: "g integrable_on S \<and> ((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) sequentially"
    if f0: "\<And>k x. x \<in> S \<Longrightarrow> 0 \<le> f k x"
    and int_f: "\<And>k. (f k) integrable_on S"
    and le: "\<And>k x. x \<in> S \<Longrightarrow> f k x \<le> f (Suc k) x"
    and lim: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range(\<lambda>k. integral S (f k)))"
    for f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real" and g S
  proof -
    have fg: "(f k x) \<le> (g x)" if "x \<in> S" for x k
    proof -
      have "\<And>xa. k \<le> xa \<Longrightarrow> f k x \<le> f xa x"
        using le  by (force intro: transitive_stepwise_le that)
      then show ?thesis
        using tendsto_lowerbound [OF lim [OF that]] eventually_sequentiallyI by force
    qed
    obtain i where i: "(\<lambda>k. integral S (f k)) \<longlonglongrightarrow> i"
      using bounded_increasing_convergent [OF bou] le int_f integral_le by blast
    have i': "(integral S (f k)) \<le> i" for k
    proof -
      have "\<And>k. \<And>x. x \<in> S \<Longrightarrow> \<forall>n\<ge>k. f k x \<le> f n x"
        using le  by (force intro: transitive_stepwise_le)
      then show ?thesis
        using tendsto_lowerbound [OF i eventually_sequentiallyI trivial_limit_sequentially]
        by (meson int_f integral_le)
    qed
    let ?f = "(\<lambda>k x. if x \<in> S then f k x else 0)"
    let ?g = "(\<lambda>x. if x \<in> S then g x else 0)"
    have int: "?f k integrable_on cbox a b" for a b k
      by (simp add: int_f integrable_altD(1))
    have int': "\<And>k a b. f k integrable_on cbox a b \<inter> S"
      using int by (simp add: Int_commute integrable_restrict_Int) 
    have g: "?g integrable_on cbox a b \<and>
             (\<lambda>k. integral (cbox a b) (?f k)) \<longlonglongrightarrow> integral (cbox a b) ?g" for a b
    proof (rule monotone_convergence_interval)
      have "norm (integral (cbox a b) (?f k)) \<le> norm (integral S (f k))" for k
      proof -
        have "0 \<le> integral (cbox a b) (?f k)"
          by (metis (no_types) integral_nonneg Int_iff f0 inf_commute integral_restrict_Int int')
        moreover have "0 \<le> integral S (f k)"
          by (simp add: integral_nonneg f0 int_f)
        moreover have "integral (S \<inter> cbox a b) (f k) \<le> integral S (f k)"
          by (metis f0 inf_commute int' int_f integral_subset_le le_inf_iff order_refl)
        ultimately show ?thesis
          by (simp add: integral_restrict_Int)
      qed
      moreover obtain B where "\<And>x. x \<in> range (\<lambda>k. integral S (f k)) \<Longrightarrow> norm x \<le> B"
        using bou unfolding bounded_iff by blast
      ultimately show "bounded (range (\<lambda>k. integral (cbox a b) (?f k)))"
        unfolding bounded_iff by (blast intro: order_trans)
    qed (use int le lim in auto)
    moreover have "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow> norm (integral (cbox a b) ?g - i) < e"
      if "0 < e" for e
    proof -
      have "e/4>0"
        using that by auto
      with LIMSEQ_D [OF i] obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (integral S (f n) - i) < e/4"
        by metis
      with int_f[of N, unfolded has_integral_integral has_integral_alt'[of "f N"]] 
      obtain B where "0 < B" and B: 
        "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow> norm (integral (cbox a b) (?f N) - integral S (f N)) < e/4"
        by (meson \<open>0 < e/4\<close>)
      have "norm (integral (cbox a b) ?g - i) < e" if  ab: "ball 0 B \<subseteq> cbox a b" for a b
      proof -
        obtain M where M: "\<And>n. n \<ge> M \<Longrightarrow> abs (integral (cbox a b) (?f n) - integral (cbox a b) ?g) < e/2"
          using \<open>e > 0\<close> g by (fastforce simp add: dest!: LIMSEQ_D [where r = "e/2"])
        have *: "\<And>\<alpha> \<beta> g. \<lbrakk>\<bar>\<alpha> - i\<bar> < e/2; \<bar>\<beta> - g\<bar> < e/2; \<alpha> \<le> \<beta>; \<beta> \<le> i\<rbrakk> \<Longrightarrow> \<bar>g - i\<bar> < e"
          unfolding real_inner_1_right by arith
        show "norm (integral (cbox a b) ?g - i) < e"
          unfolding real_norm_def
        proof (rule *)
          show "\<bar>integral (cbox a b) (?f N) - i\<bar> < e/2"
          proof (rule abs_triangle_half_l)
            show "\<bar>integral (cbox a b) (?f N) - integral S (f N)\<bar> < e/2/2"
              using B[OF ab] by simp
            show "abs (i - integral S (f N)) < e/2/2"
              using N by (simp add: abs_minus_commute)
          qed
          show "\<bar>integral (cbox a b) (?f (M + N)) - integral (cbox a b) ?g\<bar> < e/2"
            by (metis le_add1 M[of "M + N"])
          show "integral (cbox a b) (?f N) \<le> integral (cbox a b) (?f (M + N))"
          proof (intro ballI integral_le[OF int int])
            fix x assume "x \<in> cbox a b"
            have "(f m x) \<le> (f n x)" if "x \<in> S" "n \<ge> m" for m n
            proof (rule transitive_stepwise_le [OF \<open>n \<ge> m\<close> order_refl])
              show "\<And>u y z. \<lbrakk>f u x \<le> f y x; f y x \<le> f z x\<rbrakk> \<Longrightarrow> f u x \<le> f z x"
                using dual_order.trans by blast
            qed (simp add: le \<open>x \<in> S\<close>)
            then show "(?f N)x \<le> (?f (M+N))x"
              by auto
          qed
          have "integral (cbox a b \<inter> S) (f (M + N)) \<le> integral S (f (M + N))"
            by (metis Int_lower1 f0 inf_commute int' int_f integral_subset_le)
          then have "integral (cbox a b) (?f (M + N)) \<le> integral S (f (M + N))"
            by (metis (no_types) inf_commute integral_restrict_Int)
          also have "... \<le> i"
            using i'[of "M + N"] by auto
          finally show "integral (cbox a b) (?f (M + N)) \<le> i" .
        qed
      qed
      then show ?thesis
        using \<open>0 < B\<close> by blast
    qed
    ultimately have "(g has_integral i) S"
      unfolding has_integral_alt' by auto
    then show ?thesis
      using has_integral_integrable_integral i integral_unique by metis
  qed

  have sub: "\<And>k. integral S (\<lambda>x. f k x - f 0 x) = integral S (f k) - integral S (f 0)"
    by (simp add: integral_diff int_f)
  have *: "\<And>x m n. x \<in> S \<Longrightarrow> n\<ge>m \<Longrightarrow> f m x \<le> f n x"
    using assms(2) by (force intro: transitive_stepwise_le)
  have gf: "(\<lambda>x. g x - f 0 x) integrable_on S \<and> ((\<lambda>k. integral S (\<lambda>x. f (Suc k) x - f 0 x)) \<longlongrightarrow>
    integral S (\<lambda>x. g x - f 0 x)) sequentially"
  proof (rule lem)
    show "\<And>k. (\<lambda>x. f (Suc k) x - f 0 x) integrable_on S"
      by (simp add: integrable_diff int_f)
    show "(\<lambda>k. f (Suc k) x - f 0 x) \<longlonglongrightarrow> g x - f 0 x" if "x \<in> S" for x
    proof -
      have "(\<lambda>n. f (Suc n) x) \<longlonglongrightarrow> g x"
        using LIMSEQ_ignore_initial_segment[OF fg[OF \<open>x \<in> S\<close>], of 1] by simp
      then show ?thesis
        by (simp add: tendsto_diff)
    qed
    show "bounded (range (\<lambda>k. integral S (\<lambda>x. f (Suc k) x - f 0 x)))"
    proof -
      obtain B where B: "\<And>k. norm (integral S (f k)) \<le> B"
        using  bou by (auto simp: bounded_iff)
      then have "norm (integral S (\<lambda>x. f (Suc k) x - f 0 x))
              \<le> B + norm (integral S (f 0))" for k
        unfolding sub by (meson add_le_cancel_right norm_triangle_le_diff)
      then show ?thesis
        unfolding bounded_iff by blast
    qed
  qed (use * in auto)
  then have "(\<lambda>x. integral S (\<lambda>xa. f (Suc x) xa - f 0 xa) + integral S (f 0))
             \<longlonglongrightarrow> integral S (\<lambda>x. g x - f 0 x) + integral S (f 0)"
    by (auto simp add: tendsto_add)
  moreover have "(\<lambda>x. g x - f 0 x + f 0 x) integrable_on S"
    using gf integrable_add int_f [of 0] by metis
  ultimately show ?thesis
    by (simp add: integral_diff int_f LIMSEQ_imp_Suc sub)
qed

lemma has_integral_monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes f: "\<And>k. (f k has_integral x k) s"
  assumes "\<And>k x. x \<in> s \<Longrightarrow> f k x \<le> f (Suc k) x"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  assumes "x \<longlonglongrightarrow> x'"
  shows "(g has_integral x') s"
proof -
  have x_eq: "x = (\<lambda>i. integral s (f i))"
    by (simp add: integral_unique[OF f])
  then have x: "range(\<lambda>k. integral s (f k)) = range x"
    by auto
  have *: "g integrable_on s \<and> (\<lambda>k. integral s (f k)) \<longlonglongrightarrow> integral s g"
  proof (intro monotone_convergence_increasing allI ballI assms)
    show "bounded (range(\<lambda>k. integral s (f k)))"
      using x convergent_imp_bounded assms by metis
  qed (use f in auto)
  then have "integral s g = x'"
    by (intro LIMSEQ_unique[OF _ \<open>x \<longlonglongrightarrow> x'\<close>]) (simp add: x_eq)
  with * show ?thesis
    by (simp add: has_integral_integral)
qed

lemma monotone_convergence_decreasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes intf: "\<And>k. (f k) integrable_on S"
    and le: "\<And>k x. x \<in> S \<Longrightarrow> f (Suc k) x \<le> f k x"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range(\<lambda>k. integral S (f k)))"
  shows "g integrable_on S \<and> (\<lambda>k. integral S (f k)) \<longlonglongrightarrow> integral S g"
proof -
  have *: "range(\<lambda>k. integral S (\<lambda>x. - f k x)) = (*\<^sub>R) (- 1) ` (range(\<lambda>k. integral S (f k)))"
    by force
  have "(\<lambda>x. - g x) integrable_on S \<and> (\<lambda>k. integral S (\<lambda>x. - f k x)) \<longlonglongrightarrow> integral S (\<lambda>x. - g x)"
  proof (rule monotone_convergence_increasing)
    show "\<And>k. (\<lambda>x. - f k x) integrable_on S"
      by (blast intro: integrable_neg intf)
    show "\<And>k x. x \<in> S \<Longrightarrow> - f k x \<le> - f (Suc k) x"
      by (simp add: le)
    show "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>k. - f k x) \<longlonglongrightarrow> - g x"
      by (simp add: fg tendsto_minus)
    show "bounded (range(\<lambda>k. integral S (\<lambda>x. - f k x)))"
      using "*" bou bounded_scaling by auto
  qed
  then show ?thesis
    by (force dest: integrable_neg tendsto_minus)
qed

lemma integral_norm_bound_integral:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes int_f: "f integrable_on S"
    and int_g: "g integrable_on S"
    and le_g: "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (integral S f) \<le> integral S g"
proof -
  have norm: "norm \<eta> \<le> y + e"
    if "norm \<zeta> \<le> x" and "\<bar>x - y\<bar> < e/2" and "norm (\<zeta> - \<eta>) < e/2"
    for e x y and \<zeta> \<eta> :: 'a
  proof -
    have "norm (\<eta> - \<zeta>) < e/2"
      by (metis norm_minus_commute that(3))
    moreover have "x \<le> y + e/2"
      using that(2) by linarith
    ultimately show ?thesis
      using that(1) le_less_trans[OF norm_triangle_sub[of \<eta> \<zeta>]] by (auto simp: less_imp_le)
  qed
  have lem: "norm (integral(cbox a b) f) \<le> integral (cbox a b) g"
    if f: "f integrable_on cbox a b"
    and g: "g integrable_on cbox a b"
    and nle: "\<And>x. x \<in> cbox a b \<Longrightarrow> norm (f x) \<le> g x"
    for f :: "'n \<Rightarrow> 'a" and g a b
  proof (rule field_le_epsilon)
    fix e :: real
    assume "e > 0"
    then have e: "e/2 > 0"
      by auto
    with integrable_integral[OF f,unfolded has_integral[of f]]
    obtain \<gamma> where \<gamma>: "gauge \<gamma>"
              "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> \<gamma> fine \<D> 
           \<Longrightarrow> norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) - integral (cbox a b) f) < e/2"
      by meson 
    moreover
    from integrable_integral[OF g,unfolded has_integral[of g]] e
    obtain \<delta> where \<delta>: "gauge \<delta>"
              "\<And>\<D>. \<D> tagged_division_of cbox a b \<and> \<delta> fine \<D> 
           \<Longrightarrow> norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - integral (cbox a b) g) < e/2"
      by meson
    ultimately have "gauge (\<lambda>x. \<gamma> x \<inter> \<delta> x)"
      using gauge_Int by blast
    with fine_division_exists obtain \<D> 
      where p: "\<D> tagged_division_of cbox a b" "(\<lambda>x. \<gamma> x \<inter> \<delta> x) fine \<D>" 
      by metis
    have "\<gamma> fine \<D>" "\<delta> fine \<D>"
      using fine_Int p(2) by blast+
    show "norm (integral (cbox a b) f) \<le> integral (cbox a b) g + e"
    proof (rule norm)
      have "norm (content K *\<^sub>R f x) \<le> content K *\<^sub>R g x" if  "(x, K) \<in> \<D>" for x K
      proof-
        have K: "x \<in> K" "K \<subseteq> cbox a b"
          using \<open>(x, K) \<in> \<D>\<close> p(1) by blast+
        obtain u v where  "K = cbox u v"
          using \<open>(x, K) \<in> \<D>\<close> p(1) by blast
        moreover have "content K * norm (f x) \<le> content K * g x"
          by (meson K(1) K(2) content_pos_le mult_left_mono nle subsetD)
        then show ?thesis
          by simp
      qed
      then show "norm (\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) \<le> (\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x)"
        by (simp add: sum_norm_le split_def)
      show "norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) - integral (cbox a b) f) < e/2"
        using \<open>\<gamma> fine \<D>\<close> \<gamma> p(1) by simp
      show "\<bar>(\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R g x) - integral (cbox a b) g\<bar> < e/2"
        using \<open>\<delta> fine \<D>\<close> \<delta> p(1) by simp
    qed
  qed
  show ?thesis
  proof (rule field_le_epsilon)
    fix e :: real
    assume "e > 0"
    then have e: "e/2 > 0"
      by auto
    let ?f = "(\<lambda>x. if x \<in> S then f x else 0)"
    let ?g = "(\<lambda>x. if x \<in> S then g x else 0)"
    have f: "?f integrable_on cbox a b" and g: "?g integrable_on cbox a b" for a b
      using int_f int_g integrable_altD by auto
    obtain Bf where "0 < Bf"
      and Bf: "\<And>a b. ball 0 Bf \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. (?f has_integral z) (cbox a b) \<and> norm (z - integral S f) < e/2"
      using integrable_integral [OF int_f,unfolded has_integral'[of f]] e that by blast
    obtain Bg where "0 < Bg"
      and Bg: "\<And>a b. ball 0 Bg \<subseteq> cbox a b \<Longrightarrow>
        \<exists>z. (?g has_integral z) (cbox a b) \<and> norm (z - integral S g) < e/2"
      using integrable_integral [OF int_g,unfolded has_integral'[of g]] e that by blast
    obtain a b::'n where ab: "ball 0 Bf \<union> ball 0 Bg \<subseteq> cbox a b"
      using ball_max_Un  by (metis bounded_ball bounded_subset_cbox_symmetric)
    have "ball 0 Bf \<subseteq> cbox a b"
      using ab by auto
    with Bf obtain z where int_fz: "(?f has_integral z) (cbox a b)" and z: "norm (z - integral S f) < e/2"
      by meson
    have "ball 0 Bg \<subseteq> cbox a b"
      using ab by auto
    with Bg obtain w where int_gw: "(?g has_integral w) (cbox a b)" and w: "norm (w - integral S g) < e/2"
      by meson
    show "norm (integral S f) \<le> integral S g + e"
    proof (rule norm)
      show "norm (integral (cbox a b) ?f) \<le> integral (cbox a b) ?g"
        by (simp add: le_g lem[OF f g, of a b])
      show "\<bar>integral (cbox a b) ?g - integral S g\<bar> < e/2"
        using int_gw integral_unique w by auto
      show "norm (integral (cbox a b) ?f - integral S f) < e/2"
        using int_fz integral_unique z by blast
    qed
  qed
qed

lemma continuous_on_imp_absolutely_integrable_on:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "continuous_on {a..b} f \<Longrightarrow>
    norm (integral {a..b} f) \<le> integral {a..b} (\<lambda>x. norm (f x))"
  by (intro integral_norm_bound_integral integrable_continuous_real continuous_on_norm) auto

lemma integral_bound:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
  assumes "continuous_on {a .. b} f"
  assumes "\<And>t. t \<in> {a .. b} \<Longrightarrow> norm (f t) \<le> B"
  shows "norm (integral {a .. b} f) \<le> B * (b - a)"
proof -
  note continuous_on_imp_absolutely_integrable_on[OF assms(2)]
  also have "integral {a..b} (\<lambda>x. norm (f x)) \<le> integral {a..b} (\<lambda>_. B)"
    by (rule integral_le)
      (auto intro!: integrable_continuous_real continuous_intros assms)
  also have "\<dots> = B * (b - a)" using assms by simp
  finally show ?thesis .
qed

lemma integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes f: "f integrable_on S" and g: "g integrable_on S"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> (g x)\<bullet>k"
  shows "norm (integral S f) \<le> (integral S g)\<bullet>k"
proof -
  have "norm (integral S f) \<le> integral S ((\<lambda>x. x \<bullet> k) \<circ> g)"
    using integral_norm_bound_integral[OF f integrable_linear[OF g]]
    by (simp add: bounded_linear_inner_left fg)
  then show ?thesis
    unfolding o_def integral_component_eq[OF g] .
qed

lemma has_integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes f: "(f has_integral i) S"
    and g: "(g has_integral j) S"
    and "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> (g x)\<bullet>k"
  shows "norm i \<le> j\<bullet>k"
  using integral_norm_bound_integral_component[of f S g k] 
  unfolding integral_unique[OF f] integral_unique[OF g]
  using assms
  by auto


lemma uniformly_convergent_improper_integral:
  fixes f :: "'b \<Rightarrow> real \<Rightarrow> 'a :: {banach}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (G has_field_derivative g x) (at x within {a..})"
  assumes integrable: "\<And>a' b x. x \<in> A \<Longrightarrow> a' \<ge> a \<Longrightarrow> b \<ge> a' \<Longrightarrow> f x integrable_on {a'..b}"
  assumes G: "convergent G"
  assumes le: "\<And>y x. y \<in> A \<Longrightarrow> x \<ge> a \<Longrightarrow> norm (f y x) \<le> g x"
  shows   "uniformly_convergent_on A (\<lambda>b x. integral {a..b} (f x))"
proof (intro Cauchy_uniformly_convergent uniformly_Cauchy_onI', goal_cases)
  case (1 \<epsilon>)
  from G have "Cauchy G"
    by (auto intro!: convergent_Cauchy)
  with 1 obtain M where M: "dist (G (real m)) (G (real n)) < \<epsilon>" if "m \<ge> M" "n \<ge> M" for m n
    by (force simp: Cauchy_def)
  define M' where "M' = max (nat \<lceil>a\<rceil>) M"

  show ?case
  proof (rule exI[of _ M'], safe, goal_cases)
    case (1 x m n)
    have M': "M' \<ge> a" "M' \<ge> M" unfolding M'_def by linarith+
    have int_g: "(g has_integral (G (real n) - G (real m))) {real m..real n}"
      using 1 M' by (intro fundamental_theorem_of_calculus) 
                    (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] 
                          intro!: DERIV_subset[OF deriv])
    have int_f: "f x integrable_on {a'..real n}" if "a' \<ge> a" for a'
      using that 1 by (cases "a' \<le> real n") (auto intro: integrable)

    have "dist (integral {a..real m} (f x)) (integral {a..real n} (f x)) =
            norm (integral {a..real n} (f x) - integral {a..real m} (f x))"
      by (simp add: dist_norm norm_minus_commute)
    also have "integral {a..real m} (f x) + integral {real m..real n} (f x) = 
                 integral {a..real n} (f x)"
      using M' and 1 by (intro integral_combine int_f) auto
    hence "integral {a..real n} (f x) - integral {a..real m} (f x) = 
             integral {real m..real n} (f x)"
      by (simp add: algebra_simps)
    also have "norm \<dots> \<le> integral {real m..real n} g"
      using le 1 M' int_f int_g by (intro integral_norm_bound_integral) auto 
    also from int_g have "integral {real m..real n} g = G (real n) - G (real m)"
      by (simp add: has_integral_iff)
    also have "\<dots> \<le> dist (G m) (G n)" 
      by (simp add: dist_norm)
    also from 1 and M' have "\<dots> < \<epsilon>"
      by (intro M) auto
    finally show ?case .
  qed
qed

lemma uniformly_convergent_improper_integral':
  fixes f :: "'b \<Rightarrow> real \<Rightarrow> 'a :: {banach, real_normed_algebra}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (G has_field_derivative g x) (at x within {a..})"
  assumes integrable: "\<And>a' b x. x \<in> A \<Longrightarrow> a' \<ge> a \<Longrightarrow> b \<ge> a' \<Longrightarrow> f x integrable_on {a'..b}"
  assumes G: "convergent G"
  assumes le: "eventually (\<lambda>x. \<forall>y\<in>A. norm (f y x) \<le> g x) at_top"
  shows   "uniformly_convergent_on A (\<lambda>b x. integral {a..b} (f x))"
proof -
  from le obtain a'' where le: "\<And>y x. y \<in> A \<Longrightarrow> x \<ge> a'' \<Longrightarrow> norm (f y x) \<le> g x"
    by (auto simp: eventually_at_top_linorder)
  define a' where "a' = max a a''"

  have "uniformly_convergent_on A (\<lambda>b x. integral {a'..real b} (f x))"
  proof (rule uniformly_convergent_improper_integral)
    fix t assume t: "t \<ge> a'"
    hence "(G has_field_derivative g t) (at t within {a..})"
      by (intro deriv) (auto simp: a'_def)
    moreover have "{a'..} \<subseteq> {a..}" unfolding a'_def by auto
    ultimately show "(G has_field_derivative g t) (at t within {a'..})"
      by (rule DERIV_subset)
  qed (insert le, auto simp: a'_def intro: integrable G)
  hence "uniformly_convergent_on A (\<lambda>b x. integral {a..a'} (f x) + integral {a'..real b} (f x))" 
    (is ?P) by (intro uniformly_convergent_add) auto
  also have "eventually (\<lambda>x. \<forall>y\<in>A. integral {a..a'} (f y) + integral {a'..x} (f y) =
                   integral {a..x} (f y)) sequentially"
    by (intro eventually_mono [OF eventually_ge_at_top[of "nat \<lceil>a'\<rceil>"]] ballI integral_combine)
       (auto simp: a'_def intro: integrable)
  hence "?P \<longleftrightarrow> ?thesis"
    by (intro uniformly_convergent_cong) simp_all
  finally show ?thesis .
qed

subsection \<open>differentiation under the integral sign\<close>

lemma integral_continuous_on_param:
  fixes f::"'a::topological_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). f x t)"
  shows "continuous_on U (\<lambda>x. integral (cbox a b) (f x))"
proof cases
  assume "content (cbox a b) \<noteq> 0"
  then have ne: "cbox a b \<noteq> {}" by auto

  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]

  show ?thesis
    unfolding continuous_on_def
  proof (safe intro!: tendstoI)
    fix e'::real and x
    assume "e' > 0"
    define e where "e = e' / (content (cbox a b) + 1)"
    have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def intro!: divide_pos_pos add_nonneg_pos)
    assume "x \<in> U"
    from continuous_on_prod_compactE[OF cont_fx compact_cbox \<open>x \<in> U\<close> \<open>0 < e\<close>]
    obtain X0 where X0: "x \<in> X0" "open X0"
      and fx_bound: "\<And>y t. y \<in> X0 \<inter> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> norm (f y t - f x t) \<le> e"
      unfolding split_beta fst_conv snd_conv dist_norm
      by metis
    have "\<forall>\<^sub>F y in at x within U. y \<in> X0 \<inter> U"
      using X0(1) X0(2) eventually_at_topological by auto
    then show "\<forall>\<^sub>F y in at x within U. dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) < e'"
    proof eventually_elim
      case (elim y)
      have "dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) =
        norm (integral (cbox a b) (\<lambda>t. f y t - f x t))"
        using elim \<open>x \<in> U\<close>
        unfolding dist_norm
        by (subst integral_diff)
           (auto intro!: integrable_continuous continuous_intros)
      also have "\<dots> \<le> e * content (cbox a b)"
        using elim \<open>x \<in> U\<close>
        by (intro integrable_bound)
           (auto intro!: fx_bound \<open>x \<in> U \<close> less_imp_le[OF \<open>0 < e\<close>]
              integrable_continuous continuous_intros)
      also have "\<dots> < e'"
        using \<open>0 < e'\<close> \<open>e > 0\<close>
        by (auto simp: e_def field_split_simps)
      finally show "dist (integral (cbox a b) (f y)) (integral (cbox a b) (f x)) < e'" .
    qed
  qed
qed (auto intro!: continuous_on_const)

lemma leibniz_rule:
  fixes f::"'a::banach \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
    ((\<lambda>x. f x t) has_derivative blinfun_apply (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> f x integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes [intro]: "x0 \<in> U"
  assumes "convex U"
  shows
    "((\<lambda>x. integral (cbox a b) (f x)) has_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
    (is "(?F has_derivative ?dF) _")
proof cases
  assume "content (cbox a b) \<noteq> 0"
  then have ne: "cbox a b \<noteq> {}" by auto
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  show ?thesis
  proof (intro has_derivativeI bounded_linear_scaleR_left tendstoI, fold norm_conv_dist)
    have cont_f1: "\<And>t. t \<in> cbox a b \<Longrightarrow> continuous_on U (\<lambda>x. f x t)"
      by (auto simp: continuous_on_eq_continuous_within intro!: has_derivative_continuous fx)
    note [continuous_intros] = continuous_on_compose2[OF cont_f1]
    fix e'::real
    assume "e' > 0"
    define e where "e = e' / (content (cbox a b) + 1)"
    have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def intro!: divide_pos_pos add_nonneg_pos)
    from continuous_on_prod_compactE[OF cont_fx compact_cbox \<open>x0 \<in> U\<close> \<open>e > 0\<close>]
    obtain X0 where X0: "x0 \<in> X0" "open X0"
      and fx_bound: "\<And>x t. x \<in> X0 \<inter> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> norm (fx x t - fx x0 t) \<le> e"
      unfolding split_beta fst_conv snd_conv
      by (metis dist_norm)

    note eventually_closed_segment[OF \<open>open X0\<close> \<open>x0 \<in> X0\<close>, of U]
    moreover
    have "\<forall>\<^sub>F x in at x0 within U. x \<in> X0"
      using \<open>open X0\<close> \<open>x0 \<in> X0\<close> eventually_at_topological by blast
    moreover have "\<forall>\<^sub>F x in at x0 within U. x \<noteq> x0"
      by (auto simp: eventually_at_filter)
    moreover have "\<forall>\<^sub>F x in at x0 within U. x \<in> U"
      by (auto simp: eventually_at_filter)
    ultimately
    show "\<forall>\<^sub>F x in at x0 within U. norm ((?F x - ?F x0 - ?dF (x - x0)) /\<^sub>R norm (x - x0)) < e'"
    proof eventually_elim
      case (elim x)
      from elim have "0 < norm (x - x0)" by simp
      have "closed_segment x0 x \<subseteq> U"
        by (rule \<open>convex U\<close>[unfolded convex_contains_segment, rule_format, OF \<open>x0 \<in> U\<close> \<open>x \<in> U\<close>])
      from elim have [intro]: "x \<in> U" by auto
      have "?F x - ?F x0 - ?dF (x - x0) =
        integral (cbox a b) (\<lambda>y. f x y - f x0 y - fx x0 y (x - x0))"
        (is "_ = ?id")
        using \<open>x \<noteq> x0\<close>
        by (subst blinfun_apply_integral integral_diff,
            auto intro!: integrable_diff integrable_f2 continuous_intros
              intro: integrable_continuous)+
      also
      {
        fix t assume t: "t \<in> (cbox a b)"
        have seg: "\<And>t. t \<in> {0..1} \<Longrightarrow> x0 + t *\<^sub>R (x - x0) \<in> X0 \<inter> U"
          using \<open>closed_segment x0 x \<subseteq> U\<close>
            \<open>closed_segment x0 x \<subseteq> X0\<close>
          by (force simp: closed_segment_def algebra_simps)
        from t have deriv:
          "((\<lambda>x. f x t) has_derivative (fx y t)) (at y within X0 \<inter> U)"
          if "y \<in> X0 \<inter> U" for y
          unfolding has_vector_derivative_def[symmetric]
          using that \<open>x \<in> X0\<close>
          by (intro has_derivative_subset[OF fx]) auto
        have "\<And>x. x \<in> X0 \<inter> U \<Longrightarrow> onorm (blinfun_apply (fx x t) - (fx x0 t)) \<le> e"
          using fx_bound t
          by (auto simp add: norm_blinfun_def fun_diff_def blinfun.bilinear_simps[symmetric])
        from differentiable_bound_linearization[OF seg deriv this] X0
        have "norm (f x t - f x0 t - fx x0 t (x - x0)) \<le> e * norm (x - x0)"
          by (auto simp add: ac_simps)
      }
      then have "norm ?id \<le> integral (cbox a b) (\<lambda>_. e * norm (x - x0))"
        by (intro integral_norm_bound_integral)
          (auto intro!: continuous_intros integrable_diff integrable_f2
            intro: integrable_continuous)
      also have "\<dots> = content (cbox a b) * e * norm (x - x0)"
        by simp
      also have "\<dots> < e' * norm (x - x0)"
      proof (intro mult_strict_right_mono[OF _ \<open>0 < norm (x - x0)\<close>])
        show "content (cbox a b) * e < e'"
          using \<open>e' > 0\<close> by (simp add: divide_simps e_def not_less)
      qed
      finally have "norm (?F x - ?F x0 - ?dF (x - x0)) < e' * norm (x - x0)" .
      then show ?case
        by (auto simp: divide_simps)
    qed
  qed (rule blinfun.bounded_linear_right)
qed (auto intro!: derivative_eq_intros simp: blinfun.bilinear_simps)

lemma has_vector_derivative_eq_has_derivative_blinfun:
  "(f has_vector_derivative f') (at x within U) \<longleftrightarrow>
    (f has_derivative blinfun_scaleR_left f') (at x within U)"
  by (simp add: has_vector_derivative_def)

lemma leibniz_rule_vector_derivative:
  fixes f::"real \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
      ((\<lambda>x. f x t) has_vector_derivative (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_vector_derivative integral (cbox a b) (fx x0))
      (at x0 within U)"
proof -
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  show ?thesis
    unfolding has_vector_derivative_eq_has_derivative_blinfun
  proof (rule has_derivative_eq_rhs [OF leibniz_rule[OF _ integrable_f2 _ U]])
    show "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). blinfun_scaleR_left (fx x t))"
      using cont_fx by (auto simp: split_beta intro!: continuous_intros)
    show "blinfun_apply (integral (cbox a b) (\<lambda>t. blinfun_scaleR_left (fx x0 t))) =
          blinfun_apply (blinfun_scaleR_left (integral (cbox a b) (fx x0)))"
    by (subst integral_linear[symmetric])
       (auto simp: has_vector_derivative_def o_def
         intro!: integrable_continuous U continuous_intros bounded_linear_intros)
    qed (use fx in \<open>auto simp: has_vector_derivative_def\<close>)
qed

lemma has_field_derivative_eq_has_derivative_blinfun:
  "(f has_field_derivative f') (at x within U) \<longleftrightarrow> (f has_derivative blinfun_mult_right f') (at x within U)"
  by (simp add: has_field_derivative_def)

lemma leibniz_rule_field_derivative:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'a"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_field_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
proof -
  note [continuous_intros] =
    continuous_on_compose2[OF cont_fx, where f="\<lambda>y. Pair x y" for x,
      unfolded split_beta fst_conv snd_conv]
  have *: "blinfun_mult_right (integral (cbox a b) (fx x0)) =
    integral (cbox a b) (\<lambda>t. blinfun_mult_right (fx x0 t))"
    by (subst integral_linear[symmetric])
      (auto simp: has_vector_derivative_def o_def
        intro!: integrable_continuous U continuous_intros bounded_linear_intros)
  show ?thesis
    unfolding has_field_derivative_eq_has_derivative_blinfun
  proof (rule has_derivative_eq_rhs [OF leibniz_rule[OF _ integrable_f2 _ U, where fx="\<lambda>x t. blinfun_mult_right (fx x t)"]])
    show "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). blinfun_mult_right (fx x t))"
      using cont_fx by (auto simp: split_beta intro!: continuous_intros)
    show "blinfun_apply (integral (cbox a b) (\<lambda>t. blinfun_mult_right (fx x0 t))) =
          blinfun_apply (blinfun_mult_right (integral (cbox a b) (fx x0)))"
      by (subst integral_linear[symmetric])
        (auto simp: has_vector_derivative_def o_def
          intro!: integrable_continuous U continuous_intros bounded_linear_intros)
  qed (use fx in \<open>auto simp: has_field_derivative_def\<close>)
qed

lemma leibniz_rule_field_differentiable:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'a"
  assumes "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes "x0 \<in> U" "convex U"
  shows "(\<lambda>x. integral (cbox a b) (f x)) field_differentiable at x0 within U"
  using leibniz_rule_field_derivative[OF assms] by (auto simp: field_differentiable_def)


subsection \<open>Exchange uniform limit and integral\<close>

lemma uniform_limit_integral_cbox:
  fixes f::"'a \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes u: "uniform_limit (cbox a b) f g F"
  assumes c: "\<And>n. continuous_on (cbox a b) (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_integral I n) (cbox a b)"
    "(g has_integral J) (cbox a b)"
    "(I \<longlongrightarrow> J) F"
proof -
  have fi[simp]: "f n integrable_on (cbox a b)" for n
    by (auto intro!: integrable_continuous assms)
  then obtain I where I: "\<And>n. (f n has_integral I n) (cbox a b)"
    by atomize_elim (auto simp: integrable_on_def intro!: choice)

  moreover
  have gi[simp]: "g integrable_on (cbox a b)"
    by (auto intro!: integrable_continuous uniform_limit_theorem[OF _ u] eventuallyI c)
  then obtain J where J: "(g has_integral J) (cbox a b)"
    by blast

  moreover
  have "(I \<longlongrightarrow> J) F"
  proof cases
    assume "content (cbox a b) = 0"
    hence "I = (\<lambda>_. 0)" "J = 0"
      by (auto intro!: has_integral_unique I J)
    thus ?thesis by simp
  next
    assume content_nonzero: "content (cbox a b) \<noteq> 0"
    show ?thesis
    proof (rule tendstoI)
      fix e::real
      assume "e > 0"
      define e' where "e' = e/2"
      with \<open>e > 0\<close> have "e' > 0" by simp
      then have "\<forall>\<^sub>F n in F. \<forall>x\<in>cbox a b. norm (f n x - g x) < e' / content (cbox a b)"
        using u content_nonzero by (auto simp: uniform_limit_iff dist_norm zero_less_measure_iff)
      then show "\<forall>\<^sub>F n in F. dist (I n) J < e"
      proof eventually_elim
        case (elim n)
        have "I n = integral (cbox a b) (f n)"
            "J = integral (cbox a b) g"
          using I[of n] J by (simp_all add: integral_unique)
        then have "dist (I n) J = norm (integral (cbox a b) (\<lambda>x. f n x - g x))"
          by (simp add: integral_diff dist_norm)
        also have "\<dots> \<le> integral (cbox a b) (\<lambda>x. (e' / content (cbox a b)))"
          using elim
          by (intro integral_norm_bound_integral) (auto intro!: integrable_diff)
        also have "\<dots> < e"
          using \<open>0 < e\<close>
          by (simp add: e'_def)
        finally show ?case .
      qed
    qed
  qed
  ultimately show ?thesis ..
qed

lemma uniform_limit_integral:
  fixes f::"'a \<Rightarrow> 'b::ordered_euclidean_space \<Rightarrow> 'c::banach"
  assumes u: "uniform_limit {a..b} f g F"
  assumes c: "\<And>n. continuous_on {a..b} (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_integral I n) {a..b}"
    "(g has_integral J) {a..b}"
    "(I \<longlongrightarrow> J) F"
  by (metis interval_cbox assms uniform_limit_integral_cbox)


subsection \<open>Integration by parts\<close>

lemma integration_by_parts_interior_strong:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes bilinear: "bounded_bilinear (prod)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "((\<lambda>x. prod (f x) (g' x)) has_integral
                  (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
proof -
  interpret bounded_bilinear prod by fact
  have "((\<lambda>x. prod (f x) (g' x) + prod (f' x) (g x)) has_integral
          (prod (f b) (g b) - prod (f a) (g a))) {a..b}"
    using deriv by (intro fundamental_theorem_of_calculus_interior_strong[OF s le])
                   (auto intro!: continuous_intros continuous_on has_vector_derivative)
  from has_integral_diff[OF this int] show ?thesis by (simp add: algebra_simps)
qed

lemma integration_by_parts_interior:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
  by (rule integration_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)

lemma integration_by_parts:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
  by (rule integration_by_parts_interior[of _ _ _ f g f' g']) (insert assms, simp_all)

lemma integrable_by_parts_interior_strong:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes bilinear: "bounded_bilinear (prod)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
proof -
  from int obtain I where "((\<lambda>x. prod (f x) (g' x)) has_integral I) {a..b}"
    unfolding integrable_on_def by blast
  hence "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) -
           (prod (f b) (g b) - prod (f a) (g a) - I))) {a..b}" by simp
  from integration_by_parts_interior_strong[OF assms(1-7) this]
    show ?thesis unfolding integrable_on_def by blast
qed

lemma integrable_by_parts_interior:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
  by (rule integrable_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)

lemma integrable_by_parts:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
  by (rule integrable_by_parts_interior_strong[of _ "{}" _ _ f g f' g']) (insert assms, simp_all)


subsection \<open>Integration by substitution\<close>

lemma has_integral_substitution_general:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b"
      and subset: "g ` {a..b} \<subseteq> {c..d}"
      and f [continuous_intros]: "continuous_on {c..d} f"
      and g [continuous_intros]: "continuous_on {a..b} g"
      and deriv [derivative_intros]:
              "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f - integral {g b..g a} f)) {a..b}"
proof -
  let ?F = "\<lambda>x. integral {c..g x} f"
  have cont_int: "continuous_on {a..b} ?F"
    by (rule continuous_on_compose2[OF _ g subset] indefinite_integral_continuous_1
          f integrable_continuous_real)+
  have deriv: "(((\<lambda>x. integral {c..x} f) \<circ> g) has_vector_derivative g' x *\<^sub>R f (g x))
                 (at x within {a..b})" if "x \<in> {a..b} - s" for x
  proof (rule has_vector_derivative_eq_rhs [OF vector_diff_chain_within refl])
    show "(g has_vector_derivative g' x) (at x within {a..b})"
      using deriv has_field_derivative_iff_has_vector_derivative that by blast
    show "((\<lambda>x. integral {c..x} f) has_vector_derivative f (g x)) 
          (at (g x) within g ` {a..b})"
      using that le subset
      by (blast intro: has_vector_derivative_within_subset integral_has_vector_derivative f)
  qed
  have deriv: "(?F has_vector_derivative g' x *\<^sub>R f (g x))
                  (at x)" if "x \<in> {a..b} - (s \<union> {a,b})" for x
    using deriv[of x] that by (simp add: at_within_Icc_at o_def)
  have "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (?F b - ?F a)) {a..b}"
    using le cont_int s deriv cont_int
    by (intro fundamental_theorem_of_calculus_interior_strong[of "s \<union> {a,b}"]) simp_all
  also
  from subset have "g x \<in> {c..d}" if "x \<in> {a..b}" for x using that by blast
  from this[of a] this[of b] le have cd: "c \<le> g a" "g b \<le> d" "c \<le> g b" "g a \<le> d" by auto
  have "integral {c..g b} f - integral {c..g a} f = integral {g a..g b} f - integral {g b..g a} f"
  proof cases
    assume "g a \<le> g b"
    note le = le this
    from cd have "integral {c..g a} f + integral {g a..g b} f = integral {c..g b} f"
      by (intro integral_combine integrable_continuous_real continuous_on_subset[OF f] le) simp_all
    with le show ?thesis
      by (cases "g a = g b") (simp_all add: algebra_simps)
  next
    assume less: "\<not>g a \<le> g b"
    then have "g a \<ge> g b" by simp
    note le = le this
    from cd have "integral {c..g b} f + integral {g b..g a} f = integral {c..g a} f"
      by (intro integral_combine integrable_continuous_real continuous_on_subset[OF f] le) simp_all
    with less show ?thesis
      by (simp_all add: algebra_simps)
  qed
  finally show ?thesis .
qed

lemma has_integral_substitution_strong:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b" "g a \<le> g b"
    and subset: "g ` {a..b} \<subseteq> {c..d}"
    and f [continuous_intros]: "continuous_on {c..d} f"
    and g [continuous_intros]: "continuous_on {a..b} g"
    and deriv [derivative_intros]:
    "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
  using has_integral_substitution_general[OF s le(1) subset f g deriv] le(2)
  by (cases "g a = g b") auto

lemma has_integral_substitution:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "a \<le> b" "g a \<le> g b" "g ` {a..b} \<subseteq> {c..d}"
      and "continuous_on {c..d} f"
      and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
  by (intro has_integral_substitution_strong[of "{}" a b g c d] assms)
     (auto intro: DERIV_continuous_on assms)

lemma integral_shift:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cont: "continuous_on {a + c..b + c} f"
  shows "integral {a..b} (f \<circ> (\<lambda>x. x + c)) = integral {a + c..b + c} f"
proof (cases "a \<le> b")
  case True
  have "((\<lambda>x. 1 *\<^sub>R f (x + c)) has_integral integral {a+c..b+c} f) {a..b}"
    using True cont
    by (intro has_integral_substitution[where c = "a + c" and d = "b + c"])
       (auto intro!: derivative_eq_intros)
  thus ?thesis by (simp add: has_integral_iff o_def)
qed auto


subsection \<open>Compute a double integral using iterated integrals and switching the order of integration\<close>

lemma continuous_on_imp_integrable_on_Pair1:
  fixes f :: "_ \<Rightarrow> 'b::banach"
  assumes con: "continuous_on (cbox (a,c) (b,d)) f" and x: "x \<in> cbox a b"
  shows "(\<lambda>y. f (x, y)) integrable_on (cbox c d)"
proof -
  have "f \<circ> (\<lambda>y. (x, y)) integrable_on (cbox c d)"
  proof (intro integrable_continuous continuous_on_compose [OF _ continuous_on_subset [OF con]])
    show "continuous_on (cbox c d) (Pair x)"
      by (simp add: continuous_on_Pair)
    show "Pair x ` cbox c d \<subseteq> cbox (a,c) (b,d)"
      using x by blast
  qed
  then show ?thesis
    by (simp add: o_def)
qed

lemma integral_integrable_2dim:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) f"
    shows "(\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y))) integrable_on cbox a b"
proof (cases "content(cbox c d) = 0")
case True
  then show ?thesis
    by (simp add: True integrable_const)
next
  case False
  have uc: "uniformly_continuous_on (cbox (a,c) (b,d)) f"
    by (simp add: assms compact_cbox compact_uniformly_continuous)
  { fix x::'a and e::real
    assume x: "x \<in> cbox a b" and e: "0 < e"
    then have e2_gt: "0 < e/2 / content (cbox c d)" and e2_less: "e/2 / content (cbox c d) * content (cbox c d) < e"
      by (auto simp: False content_lt_nz e)
    then obtain dd
    where dd: "\<And>x x'. \<lbrakk>x\<in>cbox (a, c) (b, d); x'\<in>cbox (a, c) (b, d); norm (x' - x) < dd\<rbrakk>
                       \<Longrightarrow> norm (f x' - f x) \<le> e/(2 * content (cbox c d))"  "dd>0"
      using uc [unfolded uniformly_continuous_on_def, THEN spec, of "e/(2 * content (cbox c d))"]
      by (auto simp: dist_norm intro: less_imp_le)
    have "\<exists>delta>0. \<forall>x'\<in>cbox a b. norm (x' - x) < delta \<longrightarrow> norm (integral (cbox c d) (\<lambda>u. f (x', u) - f (x, u))) < e"
      using dd e2_gt assms x
      apply (rule_tac x=dd in exI)
      apply clarify
      apply (rule le_less_trans [OF integrable_bound e2_less])
      apply (auto intro: integrable_diff continuous_on_imp_integrable_on_Pair1)
      done
  } note * = this
  show ?thesis
  proof (rule integrable_continuous)
    show "continuous_on (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x, y)))"
      by (simp add: * continuous_on_iff dist_norm integral_diff [symmetric] continuous_on_imp_integrable_on_Pair1 [OF assms])
  qed
qed

lemma integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on (cbox a b)"
      and k: "k \<in> Basis"
  shows "integral (cbox a b) f =
           integral (cbox a b \<inter> {x. x\<bullet>k \<le> c}) f +
           integral (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) f"
  using k f
  by (auto simp: has_integral_integral intro: integral_unique [OF has_integral_split])

lemma integral_swap_operativeI:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes f: "continuous_on s f" and e: "0 < e"
    shows "operative conj True
           (\<lambda>k. \<forall>a b c d.
                cbox (a,c) (b,d) \<subseteq> k \<and> cbox (a,c) (b,d) \<subseteq> s
                \<longrightarrow> norm(integral (cbox (a,c) (b,d)) f -
                         integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f((x,y)))))
                    \<le> e * content (cbox (a,c) (b,d)))"
proof (standard, auto)
  fix a::'a and c::'b and b::'a and d::'b and u::'a and v::'a and w::'b and z::'b
  assume *: "box (a, c) (b, d) = {}"
     and cb1: "cbox (u, w) (v, z) \<subseteq> cbox (a, c) (b, d)"
     and cb2: "cbox (u, w) (v, z) \<subseteq> s"
  then have c0: "content (cbox (a, c) (b, d)) = 0"
    using * unfolding content_eq_0_interior by simp
  have c0': "content (cbox (u, w) (v, z)) = 0"
    by (fact content_0_subset [OF c0 cb1])
  show "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))))
          \<le> e * content (cbox (u,w) (v,z))"
    using content_cbox_pair_eq0_D [OF c0']
    by (force simp add: c0')
next
  fix a::'a and c::'b and b::'a and d::'b
  and M::real and i::'a and j::'b
  and u::'a and v::'a and w::'b and z::'b
  assume ij: "(i,j) \<in> Basis"
     and n1: "\<forall>a' b' c' d'.
                cbox (a',c') (b',d') \<subseteq> cbox (a,c) (b,d) \<and>
                cbox (a',c') (b',d') \<subseteq> {x. x \<bullet> (i,j) \<le> M} \<and> cbox (a',c') (b',d') \<subseteq> s \<longrightarrow>
                norm (integral (cbox (a',c') (b',d')) f - integral (cbox a' b') (\<lambda>x. integral (cbox c' d') (\<lambda>y. f (x,y))))
                \<le> e * content (cbox (a',c') (b',d'))"
     and n2: "\<forall>a' b' c' d'.
                cbox (a',c') (b',d') \<subseteq> cbox (a,c) (b,d) \<and>
                cbox (a',c') (b',d') \<subseteq> {x. M \<le> x \<bullet> (i,j)} \<and> cbox (a',c') (b',d') \<subseteq> s \<longrightarrow>
                norm (integral (cbox (a',c') (b',d')) f - integral (cbox a' b') (\<lambda>x. integral (cbox c' d') (\<lambda>y. f (x,y))))
                \<le> e * content (cbox (a',c') (b',d'))"
     and subs: "cbox (u,w) (v,z) \<subseteq> cbox (a,c) (b,d)"  "cbox (u,w) (v,z) \<subseteq> s"
  have fcont: "continuous_on (cbox (u, w) (v, z)) f"
    using assms(1) continuous_on_subset  subs(2) by blast
  then have fint: "f integrable_on cbox (u, w) (v, z)"
    by (metis integrable_continuous)
  consider "i \<in> Basis" "j=0" | "j \<in> Basis" "i=0"  using ij
    by (auto simp: Euclidean_Space.Basis_prod_def)
  then show "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))))
             \<le> e * content (cbox (u,w) (v,z))" (is ?normle)
  proof cases
    case 1
    then have e: "e * content (cbox (u, w) (v, z)) =
                  e * (content (cbox u v \<inter> {x. x \<bullet> i \<le> M}) * content (cbox w z)) +
                  e * (content (cbox u v \<inter> {x. M \<le> x \<bullet> i}) * content (cbox w z))"
      by (simp add: content_split [where c=M] content_Pair algebra_simps)
    have *: "integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) =
                integral (cbox u v \<inter> {x. x \<bullet> i \<le> M}) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) +
                integral (cbox u v \<inter> {x. M \<le> x \<bullet> i}) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y)))"
      using 1 f subs integral_integrable_2dim continuous_on_subset
      by (blast intro: integral_split)
    show ?normle
      apply (rule norm_diff2 [OF integral_split [where c=M, OF fint ij] * e])
      using 1 subs
      apply (simp_all add: cbox_Pair_eq setcomp_dot1 [of "\<lambda>u. M\<le>u"] setcomp_dot1 [of "\<lambda>u. u\<le>M"] Sigma_Int_Paircomp1)
      apply (simp_all add: interval_split ij flip: cbox_Pair_eq content_Pair)
      apply (force simp flip: interval_split intro!: n1 [rule_format])
      apply (force simp flip: interval_split intro!: n2 [rule_format])
      done
  next
    case 2
    then have e: "e * content (cbox (u, w) (v, z)) =
                  e * (content (cbox u v) * content (cbox w z \<inter> {x. x \<bullet> j \<le> M})) +
                  e * (content (cbox u v) * content (cbox w z \<inter> {x. M \<le> x \<bullet> j}))"
      by (simp add: content_split [where c=M] content_Pair algebra_simps)
    have "(\<lambda>x. integral (cbox w z \<inter> {x. x \<bullet> j \<le> M}) (\<lambda>y. f (x, y))) integrable_on cbox u v"
         "(\<lambda>x. integral (cbox w z \<inter> {x. M \<le> x \<bullet> j}) (\<lambda>y. f (x, y))) integrable_on cbox u v"
      using 2 subs
      apply (simp_all add: interval_split)
      apply (rule integral_integrable_2dim [OF continuous_on_subset [OF f]]; auto simp: cbox_Pair_eq interval_split [symmetric])+
      done
    with 2 have *: "integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) =
                   integral (cbox u v) (\<lambda>x. integral (cbox w z \<inter> {x. x \<bullet> j \<le> M}) (\<lambda>y. f (x, y))) +
                   integral (cbox u v) (\<lambda>x. integral (cbox w z \<inter> {x. M \<le> x \<bullet> j}) (\<lambda>y. f (x, y)))"
      by (simp add: integral_add [symmetric] integral_split [symmetric]
                    continuous_on_imp_integrable_on_Pair1 [OF fcont] cong: integral_cong)
    show ?normle
      apply (rule norm_diff2 [OF integral_split [where c=M, OF fint ij] * e])
      using 2 subs
      apply (simp_all add: cbox_Pair_eq setcomp_dot2 [of "\<lambda>u. M\<le>u"] setcomp_dot2 [of "\<lambda>u. u\<le>M"] Sigma_Int_Paircomp2)
      apply (simp_all add: interval_split ij flip: cbox_Pair_eq content_Pair)
      apply (force simp flip: interval_split intro!: n1 [rule_format])
      apply (force simp flip: interval_split intro!: n2 [rule_format])
      done
  qed
qed

lemma integral_Pair_const:
    "integral (cbox (a,c) (b,d)) (\<lambda>x. k) =
     integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. k))"
  by (simp add: content_Pair)

lemma integral_prod_continuous:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a, c) (b, d)) f" (is "continuous_on ?CBOX f")
    shows "integral (cbox (a, c) (b, d)) f = integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x, y)))"
proof (cases "content ?CBOX = 0")
  case True
  then show ?thesis
    by (auto simp: content_Pair)
next
  case False
  then have cbp: "content ?CBOX > 0"
    using content_lt_nz by blast
  have "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) = 0"
  proof (rule dense_eq0_I, simp)
    fix e :: real 
    assume "0 < e"
    with \<open>content ?CBOX > 0\<close> have "0 < e/content ?CBOX"
      by simp
    have f_int_acbd: "f integrable_on ?CBOX"
      by (rule integrable_continuous [OF assms])
    { fix p
      assume p: "p division_of ?CBOX"
      then have "finite p"
        by blast
      define e' where "e' = e/content ?CBOX"
      with \<open>0 < e\<close> \<open>0 < e/content ?CBOX\<close>
      have "0 < e'"
        by simp
      interpret operative conj True
           "\<lambda>k. \<forall>a' b' c' d'.
                cbox (a', c') (b', d') \<subseteq> k \<and> cbox (a', c') (b', d') \<subseteq> ?CBOX
                \<longrightarrow> norm (integral (cbox (a', c') (b', d')) f -
                         integral (cbox a' b') (\<lambda>x. integral (cbox c' d') (\<lambda>y. f ((x, y)))))
                    \<le> e' * content (cbox (a', c') (b', d'))"
        using assms \<open>0 < e'\<close> by (rule integral_swap_operativeI)
      have "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x, y))))
          \<le> e' * content ?CBOX"
        if "\<And>t u v w z. t \<in> p \<Longrightarrow> cbox (u, w) (v, z) \<subseteq> t \<Longrightarrow> cbox (u, w) (v, z) \<subseteq> ?CBOX
          \<Longrightarrow> norm (integral (cbox (u, w) (v, z)) f -
              integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))))
              \<le> e' * content (cbox (u, w) (v, z))"
        using that division [of p "(a, c)" "(b, d)"] p \<open>finite p\<close> by (auto simp add: comm_monoid_set_F_and)
      with False have "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x, y))))
          \<le> e"
        if "\<And>t u v w z. t \<in> p \<Longrightarrow> cbox (u, w) (v, z) \<subseteq> t \<Longrightarrow> cbox (u, w) (v, z) \<subseteq> ?CBOX
          \<Longrightarrow> norm (integral (cbox (u, w) (v, z)) f -
              integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))))
              \<le> e * content (cbox (u, w) (v, z)) / content ?CBOX"
        using that by (simp add: e'_def)
    } note op_acbd = this
    { fix k::real and \<D> and u::'a and v w and z::'b and t1 t2 l
      assume k: "0 < k"
         and nf: "\<And>x y u v.
                  \<lbrakk>x \<in> cbox a b; y \<in> cbox c d; u \<in> cbox a b; v\<in>cbox c d; norm (u-x, v-y) < k\<rbrakk>
                  \<Longrightarrow> norm (f(u,v) - f(x,y)) < e/(2 * (content ?CBOX))"
         and p_acbd: "\<D> tagged_division_of cbox (a,c) (b,d)"
         and fine: "(\<lambda>x. ball x k) fine \<D>"  "((t1,t2), l) \<in> \<D>"
         and uwvz_sub: "cbox (u,w) (v,z) \<subseteq> l" "cbox (u,w) (v,z) \<subseteq> cbox (a,c) (b,d)"
      have t: "t1 \<in> cbox a b" "t2 \<in> cbox c d"
        by (meson fine p_acbd cbox_Pair_iff tag_in_interval)+
      have ls: "l \<subseteq> ball (t1,t2) k"
        using fine by (simp add: fine_def Ball_def)
      { fix x1 x2
        assume xuvwz: "x1 \<in> cbox u v" "x2 \<in> cbox w z"
        then have x: "x1 \<in> cbox a b" "x2 \<in> cbox c d"
          using uwvz_sub by auto
        have "norm (x1 - t1, x2 - t2) = norm (t1 - x1, t2 - x2)"
          by (simp add: norm_Pair norm_minus_commute)
        also have "norm (t1 - x1, t2 - x2) < k"
          using xuvwz ls uwvz_sub unfolding ball_def
          by (force simp add: cbox_Pair_eq dist_norm )
        finally have "norm (f (x1,x2) - f (t1,t2)) \<le> e/content ?CBOX/2"
          using nf [OF t x]  by simp
      } note nf' = this
      have f_int_uwvz: "f integrable_on cbox (u,w) (v,z)"
        using f_int_acbd uwvz_sub integrable_on_subcbox by blast
      have f_int_uv: "\<And>x. x \<in> cbox u v \<Longrightarrow> (\<lambda>y. f (x,y)) integrable_on cbox w z"
        using assms continuous_on_subset uwvz_sub
        by (blast intro: continuous_on_imp_integrable_on_Pair1)
      have 1: "norm (integral (cbox (u,w) (v,z)) f - integral (cbox (u,w) (v,z)) (\<lambda>x. f (t1,t2)))
             \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX/2"
        using cbp \<open>0 < e/content ?CBOX\<close> nf'
        apply (simp only: integral_diff [symmetric] f_int_uwvz integrable_const)
        apply (auto simp: integrable_diff f_int_uwvz integrable_const intro: order_trans [OF integrable_bound [of "e/content ?CBOX/2"]])
        done
      have int_integrable: "(\<lambda>x. integral (cbox w z) (\<lambda>y. f (x, y))) integrable_on cbox u v"
        using assms integral_integrable_2dim continuous_on_subset uwvz_sub(2) by blast
      have normint_wz:
         "\<And>x. x \<in> cbox u v \<Longrightarrow>
               norm (integral (cbox w z) (\<lambda>y. f (x, y)) - integral (cbox w z) (\<lambda>y. f (t1, t2)))
               \<le> e * content (cbox w z) / content (cbox (a, c) (b, d))/2"
        using cbp \<open>0 < e/content ?CBOX\<close> nf'
        apply (simp only: integral_diff [symmetric] f_int_uv integrable_const)
        apply (auto simp: integrable_diff f_int_uv integrable_const intro: order_trans [OF integrable_bound [of "e/content ?CBOX/2"]])
        done
      have "norm (integral (cbox u v)
               (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y)) - integral (cbox w z) (\<lambda>y. f (t1,t2))))
            \<le> e * content (cbox w z) / content ?CBOX/2 * content (cbox u v)"
        using cbp \<open>0 < e/content ?CBOX\<close>
        apply (intro integrable_bound [OF _ _ normint_wz])
        apply (auto simp: field_split_simps integrable_diff int_integrable integrable_const)
        done
      also have "... \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX/2"
        by (simp add: content_Pair field_split_simps)
      finally have 2: "norm (integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))) -
                      integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (t1,t2))))
                \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX/2"
        by (simp only: integral_diff [symmetric] int_integrable integrable_const)
      have norm_xx: "\<lbrakk>x' = y'; norm(x - x') \<le> e/2; norm(y - y') \<le> e/2\<rbrakk> \<Longrightarrow> norm(x - y) \<le> e" for x::'c and y x' y' e
        using norm_triangle_mono [of "x-y'" "e/2" "y'-y" "e/2"] field_sum_of_halves
        by (simp add: norm_minus_commute)
      have "norm (integral (cbox (u,w) (v,z)) f - integral (cbox u v) (\<lambda>x. integral (cbox w z) (\<lambda>y. f (x,y))))
            \<le> e * content (cbox (u,w) (v,z)) / content ?CBOX"
        by (rule norm_xx [OF integral_Pair_const 1 2])
    } note * = this
    have "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) \<le> e" 
      if "\<forall>x\<in>?CBOX. \<forall>x'\<in>?CBOX. norm (x' - x) < k \<longrightarrow> norm (f x' - f x) < e /(2 * content (?CBOX))" "0 < k" for k
    proof -
      obtain p where ptag: "p tagged_division_of cbox (a, c) (b, d)" 
                 and fine: "(\<lambda>x. ball x k) fine p"
        using fine_division_exists \<open>0 < k\<close> by blast
      show ?thesis
        using that fine ptag \<open>0 < k\<close> 
        by (auto simp: * intro: op_acbd [OF division_of_tagged_division [OF ptag]])
    qed
    then show "norm (integral ?CBOX f - integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y)))) \<le> e"
      using compact_uniformly_continuous [OF assms compact_cbox]
      apply (simp add: uniformly_continuous_on_def dist_norm)
      apply (drule_tac x="e/2 / content?CBOX" in spec)
      using cbp \<open>0 < e\<close> by (auto simp: zero_less_mult_iff)
  qed
  then show ?thesis
    by simp
qed

lemma integral_swap_2dim:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox (a, c) (b, d)) (\<lambda>(x, y). f x y) = integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)"
proof -
  have "((\<lambda>(x, y). f x y) has_integral integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)) (prod.swap ` (cbox (c, a) (d, b)))"
  proof (rule has_integral_twiddle [of 1 prod.swap prod.swap "\<lambda>(x,y). f y x" "integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)", simplified])
    show "\<And>u v. content (prod.swap ` cbox u v) = content (cbox u v)"
      by (metis content_Pair mult.commute old.prod.exhaust swap_cbox_Pair)
    show "((\<lambda>(x, y). f y x) has_integral integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)) (cbox (c, a) (d, b))"
      by (simp add: assms integrable_continuous integrable_integral swap_continuous)
  qed (use isCont_swap in \<open>fastforce+\<close>)
 then show ?thesis
   by force
qed

theorem integral_swap_continuous:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox a b) (\<lambda>x. integral (cbox c d) (f x)) =
           integral (cbox c d) (\<lambda>y. integral (cbox a b) (\<lambda>x. f x y))"
proof -
  have "integral (cbox a b) (\<lambda>x. integral (cbox c d) (f x)) = integral (cbox (a, c) (b, d)) (\<lambda>(x, y). f x y)"
    using integral_prod_continuous [OF assms] by auto
  also have "... = integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)"
    by (rule integral_swap_2dim [OF assms])
  also have "... = integral (cbox c d) (\<lambda>y. integral (cbox a b) (\<lambda>x. f x y))"
    using integral_prod_continuous [OF swap_continuous] assms
    by auto
  finally show ?thesis .
qed


subsection \<open>Definite integrals for exponential and power function\<close>

lemma has_integral_exp_minus_to_infinity:
  assumes a: "a > 0"
  shows   "((\<lambda>x::real. exp (-a*x)) has_integral exp (-a*c)/a) {c..}"
proof -
  define f where "f = (\<lambda>k x. if x \<in> {c..real k} then exp (-a*x) else 0)"
  {
    fix k :: nat assume k: "of_nat k \<ge> c"
    from k a
      have "((\<lambda>x. exp (-a*x)) has_integral (-exp (-a*real k)/a - (-exp (-a*c)/a))) {c..real k}"
      by (intro fundamental_theorem_of_calculus)
         (auto intro!: derivative_eq_intros
               simp: has_field_derivative_iff_has_vector_derivative [symmetric])
    hence "(f k has_integral (exp (-a*c)/a - exp (-a*real k)/a)) {c..}" unfolding f_def
      by (subst has_integral_restrict) simp_all
  } note has_integral_f = this

  have [simp]: "f k = (\<lambda>_. 0)" if "of_nat k < c" for k using that by (auto simp: fun_eq_iff f_def)
  have integral_f: "integral {c..} (f k) =
                      (if real k \<ge> c then exp (-a*c)/a - exp (-a*real k)/a else 0)"
    for k using integral_unique[OF has_integral_f[of k]] by simp

  have A: "(\<lambda>x. exp (-a*x)) integrable_on {c..} \<and>
             (\<lambda>k. integral {c..} (f k)) \<longlonglongrightarrow> integral {c..} (\<lambda>x. exp (-a*x))"
  proof (intro monotone_convergence_increasing allI ballI)
    fix k ::nat
    have "(\<lambda>x. exp (-a*x)) integrable_on {c..of_real k}" (is ?P)
      unfolding f_def by (auto intro!: continuous_intros integrable_continuous_real)
    hence  "(f k) integrable_on {c..of_real k}"
      by (rule integrable_eq) (simp add: f_def)
    then show "f k integrable_on {c..}"
      by (rule integrable_on_superset) (auto simp: f_def)
  next
    fix x assume x: "x \<in> {c..}"
    have "sequentially \<le> principal {nat \<lceil>x\<rceil>..}" unfolding at_top_def by (simp add: Inf_lower)
    also have "{nat \<lceil>x\<rceil>..} \<subseteq> {k. x \<le> real k}" by auto
    also have "inf (principal \<dots>) (principal {k. \<not>x \<le> real k}) =
                 principal ({k. x \<le> real k} \<inter> {k. \<not>x \<le> real k})" by simp
    also have "{k. x \<le> real k} \<inter> {k. \<not>x \<le> real k} = {}" by blast
    finally have "inf sequentially (principal {k. \<not>x \<le> real k}) = bot"
      by (simp add: inf.coboundedI1 bot_unique)
    with x show "(\<lambda>k. f k x) \<longlonglongrightarrow> exp (-a*x)" unfolding f_def
      by (intro filterlim_If) auto
  next
    have "\<bar>integral {c..} (f k)\<bar> \<le> exp (-a*c)/a" for k
    proof (cases "c > of_nat k")
      case False
      hence "abs (integral {c..} (f k)) = abs (exp (- (a * c)) / a - exp (- (a * real k)) / a)"
        by (simp add: integral_f)
      also have "abs (exp (- (a * c)) / a - exp (- (a * real k)) / a) =
                   exp (- (a * c)) / a - exp (- (a * real k)) / a"
        using False a by (intro abs_of_nonneg) (simp_all add: field_simps)
      also have "\<dots> \<le> exp (- a * c) / a" using a by simp
      finally show ?thesis .
    qed (insert a, simp_all add: integral_f)
    thus "bounded (range(\<lambda>k. integral {c..} (f k)))"
      by (intro boundedI[of _ "exp (-a*c)/a"]) auto
  qed (auto simp: f_def)
  have "(\<lambda>k. exp (-a*c)/a - exp (-a * of_nat k)/a) \<longlonglongrightarrow> exp (-a*c)/a - 0/a"
    by (intro tendsto_intros filterlim_compose[OF exp_at_bot]
        filterlim_tendsto_neg_mult_at_bot[OF tendsto_const] filterlim_real_sequentially)+
      (insert a, simp_all)
  moreover
  from eventually_gt_at_top[of "nat \<lceil>c\<rceil>"] have "eventually (\<lambda>k. of_nat k > c) sequentially"
    by eventually_elim linarith
  hence "eventually (\<lambda>k. exp (-a*c)/a - exp (-a * of_nat k)/a = integral {c..} (f k)) sequentially"
    by eventually_elim (simp add: integral_f) 
  ultimately have "(\<lambda>k. integral {c..} (f k)) \<longlonglongrightarrow> exp (-a*c)/a - 0/a"
    by (rule Lim_transform_eventually)
  from LIMSEQ_unique[OF conjunct2[OF A] this]
  have "integral {c..} (\<lambda>x. exp (-a*x)) = exp (-a*c)/a" by simp
  with conjunct1[OF A] show ?thesis
    by (simp add: has_integral_integral)
qed

lemma integrable_on_exp_minus_to_infinity: "a > 0 \<Longrightarrow> (\<lambda>x. exp (-a*x) :: real) integrable_on {c..}"
  using has_integral_exp_minus_to_infinity[of a c] unfolding integrable_on_def by blast

lemma has_integral_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "((\<lambda>x. x powr a) has_integral (c powr (a+1) / (a+1))) {0..c}"
proof (cases "c = 0")
  case False
  define f where "f = (\<lambda>k x. if x \<in> {inverse (of_nat (Suc k))..c} then x powr a else 0)"
  define F where "F = (\<lambda>k. if inverse (of_nat (Suc k)) \<le> c then
                             c powr (a+1)/(a+1) - inverse (real (Suc k)) powr (a+1)/(a+1) else 0)"
  {
    fix k :: nat
    have "(f k has_integral F k) {0..c}"
    proof (cases "inverse (of_nat (Suc k)) \<le> c")
      case True
      {
        fix x assume x: "x \<ge> inverse (1 + real k)"
        have "0 < inverse (1 + real k)" by simp
        also note x
        finally have "x > 0" .
      } note x = this
      hence "((\<lambda>x. x powr a) has_integral c powr (a + 1) / (a + 1) -
               inverse (real (Suc k)) powr (a + 1) / (a + 1)) {inverse (real (Suc k))..c}"
        using True a by (intro fundamental_theorem_of_calculus)
           (auto intro!: derivative_eq_intros continuous_on_powr' continuous_on_const
              simp: has_field_derivative_iff_has_vector_derivative [symmetric])
      with True show ?thesis unfolding f_def F_def by (subst has_integral_restrict) simp_all
    next
      case False
      thus ?thesis unfolding f_def F_def by (subst has_integral_restrict) auto
    qed
  } note has_integral_f = this
  have integral_f: "integral {0..c} (f k) = F k" for k
    using has_integral_f[of k] by (rule integral_unique)

  have A: "(\<lambda>x. x powr a) integrable_on {0..c} \<and>
           (\<lambda>k. integral {0..c} (f k)) \<longlonglongrightarrow> integral {0..c} (\<lambda>x. x powr a)"
  proof (intro monotone_convergence_increasing ballI allI)
    fix k from has_integral_f[of k] show "f k integrable_on {0..c}"
      by (auto simp: integrable_on_def)
  next
    fix k :: nat and x :: real
    {
      assume x: "inverse (real (Suc k)) \<le> x"
      have "inverse (real (Suc (Suc k))) \<le> inverse (real (Suc k))" by (simp add: field_simps)
      also note x
      finally have "inverse (real (Suc (Suc k))) \<le> x" .
    }
    thus "f k x \<le> f (Suc k) x" by (auto simp: f_def simp del: of_nat_Suc)
  next
    fix x assume x: "x \<in> {0..c}"
    show "(\<lambda>k. f k x) \<longlonglongrightarrow> x powr a"
    proof (cases "x = 0")
      case False
      with x have "x > 0" by simp
      from order_tendstoD(2)[OF LIMSEQ_inverse_real_of_nat this]
        have "eventually (\<lambda>k. x powr a = f k x) sequentially"
        by eventually_elim (insert x, simp add: f_def)
      moreover have "(\<lambda>_. x powr a) \<longlonglongrightarrow> x powr a" by simp
      ultimately show ?thesis by (blast intro: Lim_transform_eventually)
    qed (simp_all add: f_def)
  next
    {
      fix k
      from a have "F k \<le> c powr (a + 1) / (a + 1)"
        by (auto simp add: F_def divide_simps)
      also from a have "F k \<ge> 0"
        by (auto simp: F_def divide_simps simp del: of_nat_Suc intro!: powr_mono2)
      hence "F k = abs (F k)" by simp
      finally have "abs (F k) \<le>  c powr (a + 1) / (a + 1)" .
    }
    thus "bounded (range(\<lambda>k. integral {0..c} (f k)))"
      by (intro boundedI[of _ "c powr (a+1) / (a+1)"]) (auto simp: integral_f)
  qed

  from False c have "c > 0" by simp
  from order_tendstoD(2)[OF LIMSEQ_inverse_real_of_nat this]
    have "eventually (\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a+1) / (a+1) =
            integral {0..c} (f k)) sequentially"
    by eventually_elim (simp add: integral_f F_def)
  moreover have "(\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a + 1) / (a + 1))
                   \<longlonglongrightarrow> c powr (a + 1) / (a + 1) - 0 powr (a + 1) / (a + 1)"
    using a by (intro tendsto_intros LIMSEQ_inverse_real_of_nat) auto
  hence "(\<lambda>k. c powr (a + 1) / (a + 1) - inverse (real (Suc k)) powr (a + 1) / (a + 1))
          \<longlonglongrightarrow> c powr (a + 1) / (a + 1)" by simp
  ultimately have "(\<lambda>k. integral {0..c} (f k)) \<longlonglongrightarrow> c powr (a+1) / (a+1)"
    by (blast intro: Lim_transform_eventually)
  with A have "integral {0..c} (\<lambda>x. x powr a) = c powr (a+1) / (a+1)"
    by (blast intro: LIMSEQ_unique)
  with A show ?thesis by (simp add: has_integral_integral)
qed (simp_all add: has_integral_refl)

lemma integrable_on_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "(\<lambda>x. x powr a) integrable_on {0..c}"
  using has_integral_powr_from_0[OF assms] unfolding integrable_on_def by blast

lemma has_integral_powr_to_inf:
  fixes a e :: real
  assumes "e < -1" "a > 0"
  shows   "((\<lambda>x. x powr e) has_integral -(a powr (e + 1)) / (e + 1)) {a..}"
proof -
  define f :: "nat \<Rightarrow> real \<Rightarrow> real" where "f = (\<lambda>n x. if x \<in> {a..n} then x powr e else 0)"
  define F where "F = (\<lambda>x. x powr (e + 1) / (e + 1))"

  have has_integral_f: "(f n has_integral (F n - F a)) {a..}"
    if n: "n \<ge> a" for n :: nat
  proof -
    from n assms have "((\<lambda>x. x powr e) has_integral (F n - F a)) {a..n}"
      by (intro fundamental_theorem_of_calculus) (auto intro!: derivative_eq_intros
            simp: has_field_derivative_iff_has_vector_derivative [symmetric] F_def)
    hence "(f n has_integral (F n - F a)) {a..n}"
      by (rule has_integral_eq [rotated]) (simp add: f_def)
    thus "(f n has_integral (F n - F a)) {a..}"
      by (rule has_integral_on_superset) (auto simp: f_def)
  qed
  have integral_f: "integral {a..} (f n) = (if n \<ge> a then F n - F a else 0)" for n :: nat
  proof (cases "n \<ge> a")
    case True
    with has_integral_f[OF this] show ?thesis by (simp add: integral_unique)
  next
    case False
    have "(f n has_integral 0) {a}" by (rule has_integral_refl)
    hence "(f n has_integral 0) {a..}"
      by (rule has_integral_on_superset) (insert False, simp_all add: f_def)
    with False show ?thesis by (simp add: integral_unique)
  qed

  have *: "(\<lambda>x. x powr e) integrable_on {a..} \<and>
           (\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> integral {a..} (\<lambda>x. x powr e)"
  proof (intro monotone_convergence_increasing allI ballI)
    fix n :: nat
    from assms have "(\<lambda>x. x powr e) integrable_on {a..n}"
      by (auto intro!: integrable_continuous_real continuous_intros)
    hence "f n integrable_on {a..n}"
      by (rule integrable_eq) (auto simp: f_def)
    thus "f n integrable_on {a..}"
      by (rule integrable_on_superset) (auto simp: f_def)
  next
    fix n :: nat and x :: real
    show "f n x \<le> f (Suc n) x" by (auto simp: f_def)
  next
    fix x :: real assume x: "x \<in> {a..}"
    from filterlim_real_sequentially
      have "eventually (\<lambda>n. real n \<ge> x) at_top"
      by (simp add: filterlim_at_top)
    with x have "eventually (\<lambda>n. f n x = x powr e) at_top"
      by (auto elim!: eventually_mono simp: f_def)
    thus "(\<lambda>n. f n x) \<longlonglongrightarrow> x powr e" by (simp add: tendsto_eventually)
  next
    have "norm (integral {a..} (f n)) \<le> -F a" for n :: nat
    proof (cases "n \<ge> a")
      case True
      with assms have "a powr (e + 1) \<ge> n powr (e + 1)"
        by (intro powr_mono2') simp_all
      with assms show ?thesis by (auto simp: divide_simps F_def integral_f)
    qed (insert assms, simp add: integral_f F_def field_split_simps)
    thus "bounded (range(\<lambda>k. integral {a..} (f k)))"
      unfolding bounded_iff by (intro exI[of _ "-F a"]) auto
  qed

  from filterlim_real_sequentially
    have "eventually (\<lambda>n. real n \<ge> a) at_top"
    by (simp add: filterlim_at_top)
  hence "eventually (\<lambda>n. F n - F a = integral {a..} (f n)) at_top"
    by eventually_elim (simp add: integral_f)
  moreover have "(\<lambda>n. F n - F a) \<longlonglongrightarrow> 0 / (e + 1) - F a" unfolding F_def
    by (insert assms, (rule tendsto_intros filterlim_compose[OF tendsto_neg_powr]
          filterlim_ident filterlim_real_sequentially | simp)+)
  hence "(\<lambda>n. F n - F a) \<longlonglongrightarrow> -F a" by simp
  ultimately have "(\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> -F a" by (blast intro: Lim_transform_eventually)
  from conjunct2[OF *] and this
    have "integral {a..} (\<lambda>x. x powr e) = -F a" by (rule LIMSEQ_unique)
  with conjunct1[OF *] show ?thesis
    by (simp add: has_integral_integral F_def)
qed

lemma has_integral_inverse_power_to_inf:
  fixes a :: real and n :: nat
  assumes "n > 1" "a > 0"
  shows   "((\<lambda>x. 1 / x ^ n) has_integral 1 / (real (n - 1) * a ^ (n - 1))) {a..}"
proof -
  from assms have "real_of_int (-int n) < -1" by simp
  note has_integral_powr_to_inf[OF this \<open>a > 0\<close>]
  also have "- (a powr (real_of_int (- int n) + 1)) / (real_of_int (- int n) + 1) =
                 1 / (real (n - 1) * a powr (real (n - 1)))" using assms
    by (simp add: field_split_simps powr_add [symmetric] of_nat_diff)
  also from assms have "a powr (real (n - 1)) = a ^ (n - 1)"
    by (intro powr_realpow)
  finally show ?thesis
    by (rule has_integral_eq [rotated])
       (insert assms, simp_all add: powr_minus powr_realpow field_split_simps)
qed

subsubsection \<open>Adaption to ordered Euclidean spaces and the Cartesian Euclidean space\<close>

lemma integral_component_eq_cart[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> real^'m"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x $ k) = integral s f $ k"
  using integral_linear[OF assms(1) bounded_linear_vec_nth,unfolded o_def] .

lemma content_closed_interval:
  fixes a :: "'a::ordered_euclidean_space"
  assumes "a \<le> b"
  shows "content {a..b} = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  using content_cbox[of a b] assms by (simp add: cbox_interval eucl_le[where 'a='a])

lemma integrable_const_ivl[intro]:
  fixes a::"'a::ordered_euclidean_space"
  shows "(\<lambda>x. c) integrable_on {a..b}"
  unfolding cbox_interval[symmetric] by (rule integrable_const)

lemma integrable_on_subinterval:
  fixes f :: "'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S" "{a..b} \<subseteq> S"
  shows "f integrable_on {a..b}"
  using integrable_on_subcbox[of f S a b] assms by (simp add: cbox_interval)

end

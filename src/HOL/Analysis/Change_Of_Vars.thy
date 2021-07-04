(*  Title:      HOL/Analysis/Change_Of_Vars.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section\<open>Change of Variables Theorems\<close>

theory Change_Of_Vars
  imports Vitali_Covering_Theorem Determinants

begin

subsection \<open>Measurable Shear and Stretch\<close>

proposition
  fixes a :: "real^'n"
  assumes "m \<noteq> n" and ab_ne: "cbox a b \<noteq> {}" and an: "0 \<le> a$n"
  shows measurable_shear_interval: "(\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` (cbox a b) \<in> lmeasurable"
       (is  "?f ` _ \<in> _")
   and measure_shear_interval: "measure lebesgue ((\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` cbox a b)
               = measure lebesgue (cbox a b)" (is "?Q")
proof -
  have lin: "linear ?f"
    by (rule linearI) (auto simp: plus_vec_def scaleR_vec_def algebra_simps)
  show fab: "?f ` cbox a b \<in> lmeasurable"
    by (simp add: lin measurable_linear_image_interval)
  let ?c = "\<chi> i. if i = m then b$m + b$n else b$i"
  let ?mn = "axis m 1 - axis n (1::real)"
  have eq1: "measure lebesgue (cbox a ?c)
            = measure lebesgue (?f ` cbox a b)
            + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a$m})
            + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m})"
  proof (rule measure_Un3_negligible)
    show "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a$m} \<in> lmeasurable" "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m} \<in> lmeasurable"
      by (auto simp: convex_Int convex_halfspace_le convex_halfspace_ge bounded_Int measurable_convex)
    have "negligible {x. ?mn \<bullet> x = a$m}"
      by (metis \<open>m \<noteq> n\<close> axis_index_axis eq_iff_diff_eq_0 negligible_hyperplane)
    moreover have "?f ` cbox a b \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m}) \<subseteq> {x. ?mn \<bullet> x = a$m}"
      using \<open>m \<noteq> n\<close> antisym_conv by (fastforce simp: algebra_simps mem_box_cart inner_axis')
    ultimately show "negligible ((?f ` cbox a b) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m}))"
      by (rule negligible_subset)
    have "negligible {x. ?mn \<bullet> x = b$m}"
      by (metis \<open>m \<noteq> n\<close> axis_index_axis eq_iff_diff_eq_0 negligible_hyperplane)
    moreover have "(?f ` cbox a b) \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m}) \<subseteq> {x. ?mn \<bullet> x = b$m}"
      using \<open>m \<noteq> n\<close> antisym_conv by (fastforce simp: algebra_simps mem_box_cart inner_axis')
    ultimately show "negligible (?f ` cbox a b \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m}))"
      by (rule negligible_subset)
    have "negligible {x. ?mn \<bullet> x = b$m}"
      by (metis \<open>m \<noteq> n\<close> axis_index_axis eq_iff_diff_eq_0 negligible_hyperplane)
    moreover have "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m})) \<subseteq> {x. ?mn \<bullet> x = b$m}"
      using \<open>m \<noteq> n\<close> ab_ne
      apply (auto simp: algebra_simps mem_box_cart inner_axis')
      apply (drule_tac x=m in spec)+
      apply simp
      done
    ultimately show "negligible (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m}))"
      by (rule negligible_subset)
    show "?f ` cbox a b \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m} = cbox a ?c" (is "?lhs = _")
    proof
      show "?lhs \<subseteq> cbox a ?c"
        by (auto simp: mem_box_cart add_mono) (meson add_increasing2 an order_trans)
      show "cbox a ?c \<subseteq> ?lhs"
        apply (auto simp: algebra_simps image_iff inner_axis' lambda_add_Galois [OF \<open>m \<noteq> n\<close>])
        apply (auto simp: mem_box_cart split: if_split_asm)
        done
    qed
  qed (fact fab)
  let ?d = "\<chi> i. if i = m then a $ m - b $ m else 0"
  have eq2: "measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m}) + measure lebesgue (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m})
           = measure lebesgue (cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i))"
  proof (rule measure_translate_add[of "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a$m}" "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m}"
     "(\<chi> i. if i = m then a$m - b$m else 0)" "cbox a (\<chi> i. if i = m then a$m + b$n else b$i)"])
    show "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a$m}) \<in> lmeasurable"
      "cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m} \<in> lmeasurable"
      by (auto simp: convex_Int convex_halfspace_le convex_halfspace_ge bounded_Int measurable_convex)
    have "\<And>x. \<lbrakk>x $ n + a $ m \<le> x $ m\<rbrakk>
         \<Longrightarrow> x \<in> (+) (\<chi> i. if i = m then a $ m - b $ m else 0) ` {x. x $ n + b $ m \<le> x $ m}"
      using \<open>m \<noteq> n\<close>
      by (rule_tac x="x - (\<chi> i. if i = m then a$m - b$m else 0)" in image_eqI)
         (simp_all add: mem_box_cart)
    then have imeq: "(+) ?d ` {x. b $ m \<le> ?mn \<bullet> x} = {x. a $ m \<le> ?mn \<bullet> x}"
      using \<open>m \<noteq> n\<close> by (auto simp: mem_box_cart inner_axis' algebra_simps)
    have "\<And>x. \<lbrakk>0 \<le> a $ n; x $ n + a $ m \<le> x $ m;
                \<forall>i. i \<noteq> m \<longrightarrow> a $ i \<le> x $ i \<and> x $ i \<le> b $ i\<rbrakk>
         \<Longrightarrow> a $ m \<le> x $ m"
      using \<open>m \<noteq> n\<close>  by force
    then have "(+) ?d ` (cbox a ?c \<inter> {x. b $ m \<le> ?mn \<bullet> x})
            = cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i) \<inter> {x. a $ m \<le> ?mn \<bullet> x}"
      using an ab_ne
      apply (simp add: cbox_translation [symmetric] translation_Int interval_ne_empty_cart imeq)
      apply (auto simp: mem_box_cart inner_axis' algebra_simps if_distrib all_if_distrib)
      by (metis (full_types) add_mono mult_2_right)
    then show "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<union>
          (+) ?d ` (cbox a ?c \<inter> {x. b $ m \<le> ?mn \<bullet> x}) =
          cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i)"  (is "?lhs = ?rhs")
      using an \<open>m \<noteq> n\<close>
      apply (auto simp: mem_box_cart inner_axis' algebra_simps if_distrib all_if_distrib, force)
        apply (drule_tac x=n in spec)+
      by (meson ab_ne add_mono_thms_linordered_semiring(3) dual_order.trans interval_ne_empty_cart(1))
    have "negligible{x. ?mn \<bullet> x = a$m}"
      by (metis \<open>m \<noteq> n\<close> axis_index_axis eq_iff_diff_eq_0 negligible_hyperplane)
    moreover have "(cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<inter>
                                 (+) ?d ` (cbox a ?c \<inter> {x. b $ m \<le> ?mn \<bullet> x})) \<subseteq> {x. ?mn \<bullet> x = a$m}"
      using \<open>m \<noteq> n\<close> antisym_conv by (fastforce simp: algebra_simps mem_box_cart inner_axis')
    ultimately show "negligible (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<inter>
                                 (+) ?d ` (cbox a ?c \<inter> {x. b $ m \<le> ?mn \<bullet> x}))"
      by (rule negligible_subset)
  qed
  have ac_ne: "cbox a ?c \<noteq> {}"
    using ab_ne an
    by (clarsimp simp: interval_eq_empty_cart) (meson add_less_same_cancel1 le_less_linear less_le_trans)
  have ax_ne: "cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i) \<noteq> {}"
    using ab_ne an
    by (clarsimp simp: interval_eq_empty_cart) (meson add_less_same_cancel1 le_less_linear less_le_trans)
  have eq3: "measure lebesgue (cbox a ?c) = measure lebesgue (cbox a (\<chi> i. if i = m then a$m + b$n else b$i)) + measure lebesgue (cbox a b)"
    by (simp add: content_cbox_if_cart ab_ne ac_ne ax_ne algebra_simps prod.delta_remove
             if_distrib [of "\<lambda>u. u - z" for z] prod.remove)
  show ?Q
    using eq1 eq2 eq3
    by (simp add: algebra_simps)
qed


proposition
  fixes S :: "(real^'n) set"
  assumes "S \<in> lmeasurable"
  shows measurable_stretch: "((\<lambda>x. \<chi> k. m k * x$k) ` S) \<in> lmeasurable" (is  "?f ` S \<in> _")
    and measure_stretch: "measure lebesgue ((\<lambda>x. \<chi> k. m k * x$k) ` S) = \<bar>prod m UNIV\<bar> * measure lebesgue S"
    (is "?MEQ")
proof -
  have "(?f ` S) \<in> lmeasurable \<and> ?MEQ"
  proof (cases "\<forall>k. m k \<noteq> 0")
    case True
    have m0: "0 < \<bar>prod m UNIV\<bar>"
      using True by simp
    have "(indicat_real (?f ` S) has_integral \<bar>prod m UNIV\<bar> * measure lebesgue S) UNIV"
    proof (clarsimp simp add: has_integral_alt [where i=UNIV])
      fix e :: "real"
      assume "e > 0"
      have "(indicat_real S has_integral (measure lebesgue S)) UNIV"
        using assms lmeasurable_iff_has_integral by blast
      then obtain B where "B>0"
        and B: "\<And>a b. ball 0 B \<subseteq> cbox a b \<Longrightarrow>
                        \<exists>z. (indicat_real S has_integral z) (cbox a b) \<and>
                            \<bar>z - measure lebesgue S\<bar> < e / \<bar>prod m UNIV\<bar>"
        by (simp add: has_integral_alt [where i=UNIV]) (metis (full_types) divide_pos_pos m0  m0 \<open>e > 0\<close>)
      show "\<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
                  (\<exists>z. (indicat_real (?f ` S) has_integral z) (cbox a b) \<and>
                       \<bar>z - \<bar>prod m UNIV\<bar> * measure lebesgue S\<bar> < e)"
      proof (intro exI conjI allI)
        let ?C = "Max (range (\<lambda>k. \<bar>m k\<bar>)) * B"
        show "?C > 0"
          using True \<open>B > 0\<close> by (simp add: Max_gr_iff)
        show "ball 0 ?C \<subseteq> cbox u v \<longrightarrow>
                  (\<exists>z. (indicat_real (?f ` S) has_integral z) (cbox u v) \<and>
                       \<bar>z - \<bar>prod m UNIV\<bar> * measure lebesgue S\<bar> < e)" for u v
        proof
          assume uv: "ball 0 ?C \<subseteq> cbox u v"
          with \<open>?C > 0\<close> have cbox_ne: "cbox u v \<noteq> {}"
            using centre_in_ball by blast
          let ?\<alpha> = "\<lambda>k. u$k / m k"
          let ?\<beta> = "\<lambda>k. v$k / m k"
          have invm0: "\<And>k. inverse (m k) \<noteq> 0"
            using True by auto
          have "ball 0 B \<subseteq> (\<lambda>x. \<chi> k. x $ k / m k) ` ball 0 ?C"
          proof clarsimp
            fix x :: "real^'n"
            assume x: "norm x < B"
            have [simp]: "\<bar>Max (range (\<lambda>k. \<bar>m k\<bar>))\<bar> = Max (range (\<lambda>k. \<bar>m k\<bar>))"
              by (meson Max_ge abs_ge_zero abs_of_nonneg finite finite_imageI order_trans rangeI)
            have "norm (\<chi> k. m k * x $ k) \<le> norm (Max (range (\<lambda>k. \<bar>m k\<bar>)) *\<^sub>R x)"
              by (rule norm_le_componentwise_cart) (auto simp: abs_mult intro: mult_right_mono)
            also have "\<dots> < ?C"
              using x \<open>0 < (MAX k. \<bar>m k\<bar>) * B\<close> \<open>0 < B\<close> zero_less_mult_pos2 by fastforce
            finally have "norm (\<chi> k. m k * x $ k) < ?C" .
            then show "x \<in> (\<lambda>x. \<chi> k. x $ k / m k) ` ball 0 ?C"
              using stretch_Galois [of "inverse \<circ> m"] True by (auto simp: image_iff field_simps)
          qed
          then have Bsub: "ball 0 B \<subseteq> cbox (\<chi> k. min (?\<alpha> k) (?\<beta> k)) (\<chi> k. max (?\<alpha> k) (?\<beta> k))"
            using cbox_ne uv image_stretch_interval_cart [of "inverse \<circ> m" u v, symmetric]
            by (force simp: field_simps)
          obtain z where zint: "(indicat_real S has_integral z) (cbox (\<chi> k. min (?\<alpha> k) (?\<beta> k)) (\<chi> k. max (?\<alpha> k) (?\<beta> k)))"
                   and zless: "\<bar>z - measure lebesgue S\<bar> < e / \<bar>prod m UNIV\<bar>"
            using B [OF Bsub] by blast
          have ind: "indicat_real (?f ` S) = (\<lambda>x. indicator S (\<chi> k. x$k / m k))"
            using True stretch_Galois [of m] by (force simp: indicator_def)
          show "\<exists>z. (indicat_real (?f ` S) has_integral z) (cbox u v) \<and>
                       \<bar>z - \<bar>prod m UNIV\<bar> * measure lebesgue S\<bar> < e"
          proof (simp add: ind, intro conjI exI)
            have "((\<lambda>x. indicat_real S (\<chi> k. x $ k/ m k)) has_integral z *\<^sub>R \<bar>prod m UNIV\<bar>)
                ((\<lambda>x. \<chi> k. x $ k * m k) ` cbox (\<chi> k. min (?\<alpha> k) (?\<beta> k)) (\<chi> k. max (?\<alpha> k) (?\<beta> k)))"
              using True has_integral_stretch_cart [OF zint, of "inverse \<circ> m"]
              by (simp add: field_simps prod_dividef)
            moreover have "((\<lambda>x. \<chi> k. x $ k * m k) ` cbox (\<chi> k. min (?\<alpha> k) (?\<beta> k)) (\<chi> k. max (?\<alpha> k) (?\<beta> k))) = cbox u v"
              using True image_stretch_interval_cart [of "inverse \<circ> m" u v, symmetric]
                image_stretch_interval_cart [of "\<lambda>k. 1" u v, symmetric] \<open>cbox u v \<noteq> {}\<close>
              by (simp add: field_simps image_comp o_def)
            ultimately show "((\<lambda>x. indicat_real S (\<chi> k. x $ k/ m k)) has_integral z *\<^sub>R \<bar>prod m UNIV\<bar>) (cbox u v)"
              by simp
            have "\<bar>z *\<^sub>R \<bar>prod m UNIV\<bar> - \<bar>prod m UNIV\<bar> * measure lebesgue S\<bar>
                 = \<bar>prod m UNIV\<bar> * \<bar>z - measure lebesgue S\<bar>"
              by (metis (no_types, hide_lams) abs_abs abs_scaleR mult.commute real_scaleR_def right_diff_distrib')
            also have "\<dots> < e"
              using zless True by (simp add: field_simps)
            finally show "\<bar>z *\<^sub>R \<bar>prod m UNIV\<bar> - \<bar>prod m UNIV\<bar> * measure lebesgue S\<bar> < e" .
          qed
        qed
      qed
    qed
    then show ?thesis
      by (auto simp: has_integral_integrable integral_unique lmeasure_integral_UNIV measurable_integrable)
  next
    case False
    then obtain k where "m k = 0" and prm: "prod m UNIV = 0"
      by auto
    have nfS: "negligible (?f ` S)"
      by (rule negligible_subset [OF negligible_standard_hyperplane_cart]) (use \<open>m k = 0\<close> in auto)
    then have "(?f ` S) \<in> lmeasurable"
      by (simp add: negligible_iff_measure)
    with nfS show ?thesis
      by (simp add: prm negligible_iff_measure0)
  qed
  then show "(?f ` S) \<in> lmeasurable" ?MEQ
    by metis+
qed


proposition
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "linear f" "S \<in> lmeasurable"
  shows measurable_linear_image: "(f ` S) \<in> lmeasurable"
    and measure_linear_image: "measure lebesgue (f ` S) = \<bar>det (matrix f)\<bar> * measure lebesgue S" (is "?Q f S")
proof -
  have "\<forall>S \<in> lmeasurable. (f ` S) \<in> lmeasurable \<and> ?Q f S"
  proof (rule induct_linear_elementary [OF \<open>linear f\<close>]; intro ballI)
    fix f g and S :: "(real,'n) vec set"
    assume "linear f" and "linear g"
      and f [rule_format]: "\<forall>S \<in> lmeasurable. f ` S \<in> lmeasurable \<and> ?Q f S"
      and g [rule_format]: "\<forall>S \<in> lmeasurable. g ` S \<in> lmeasurable \<and> ?Q g S"
      and S: "S \<in> lmeasurable"
    then have gS: "g ` S \<in> lmeasurable"
      by blast
    show "(f \<circ> g) ` S \<in> lmeasurable \<and> ?Q (f \<circ> g) S"
      using f [OF gS] g [OF S] matrix_compose [OF \<open>linear g\<close> \<open>linear f\<close>]
      by (simp add: o_def image_comp abs_mult det_mul)
  next
    fix f :: "real^'n::_ \<Rightarrow> real^'n::_" and i and S :: "(real^'n::_) set"
    assume "linear f" and 0: "\<And>x. f x $ i = 0" and "S \<in> lmeasurable"
    then have "\<not> inj f"
      by (metis (full_types) linear_injective_imp_surjective one_neq_zero surjE vec_component)
    have detf: "det (matrix f) = 0"
      using \<open>\<not> inj f\<close> det_nz_iff_inj[OF \<open>linear f\<close>] by blast
    show "f ` S \<in> lmeasurable \<and> ?Q f S"
    proof
      show "f ` S \<in> lmeasurable"
        using lmeasurable_iff_indicator_has_integral \<open>linear f\<close> \<open>\<not> inj f\<close> negligible_UNIV negligible_linear_singular_image by blast
      have "measure lebesgue (f ` S) = 0"
        by (meson \<open>\<not> inj f\<close> \<open>linear f\<close> negligible_imp_measure0 negligible_linear_singular_image)
      also have "\<dots> = \<bar>det (matrix f)\<bar> * measure lebesgue S"
        by (simp add: detf)
      finally show "?Q f S" .
    qed
  next
    fix c and S :: "(real^'n::_) set"
    assume "S \<in> lmeasurable"
    show "(\<lambda>a. \<chi> i. c i * a $ i) ` S \<in> lmeasurable \<and> ?Q (\<lambda>a. \<chi> i. c i * a $ i) S"
    proof
      show "(\<lambda>a. \<chi> i. c i * a $ i) ` S \<in> lmeasurable"
        by (simp add: \<open>S \<in> lmeasurable\<close> measurable_stretch)
      show "?Q (\<lambda>a. \<chi> i. c i * a $ i) S"
        by (simp add: measure_stretch [OF \<open>S \<in> lmeasurable\<close>, of c] axis_def matrix_def det_diagonal)
    qed
  next
    fix m :: "'n" and n :: "'n" and S :: "(real, 'n) vec set"
    assume "m \<noteq> n" and "S \<in> lmeasurable"
    let ?h = "\<lambda>v::(real, 'n) vec. \<chi> i. v $ Transposition.transpose m n i"
    have lin: "linear ?h"
      by (rule linearI) (simp_all add: plus_vec_def scaleR_vec_def)
    have meq: "measure lebesgue ((\<lambda>v::(real, 'n) vec. \<chi> i. v $ Transposition.transpose m n i) ` cbox a b)
             = measure lebesgue (cbox a b)" for a b
    proof (cases "cbox a b = {}")
      case True then show ?thesis
        by simp
    next
      case False
      then have him: "?h ` (cbox a b) \<noteq> {}"
        by blast
      have eq: "?h ` (cbox a b) = cbox (?h a) (?h b)"
        by (auto simp: image_iff lambda_swap_Galois mem_box_cart) (metis transpose_involutory)+
      show ?thesis
        using him prod.permute [OF permutes_swap_id, where S=UNIV and g="\<lambda>i. (b - a)$i", symmetric]
        by (simp add: eq content_cbox_cart False)
    qed
    have "(\<chi> i j. if Transposition.transpose m n i = j then 1 else 0) = (\<chi> i j. if j = Transposition.transpose m n i then 1 else (0::real))"
      by (auto intro!: Cart_lambda_cong)
    then have "matrix ?h = transpose(\<chi> i j. mat 1 $ i $ Transposition.transpose m n j)"
      by (auto simp: matrix_eq transpose_def axis_def mat_def matrix_def)
    then have 1: "\<bar>det (matrix ?h)\<bar> = 1"
      by (simp add: det_permute_columns permutes_swap_id sign_swap_id abs_mult)
    show "?h ` S \<in> lmeasurable \<and> ?Q ?h S"
    proof
      show "?h ` S \<in> lmeasurable" "?Q ?h S"
        using measure_linear_sufficient [OF lin \<open>S \<in> lmeasurable\<close>] meq 1 by force+
    qed
  next
    fix m n :: "'n" and S :: "(real, 'n) vec set"
    assume "m \<noteq> n" and "S \<in> lmeasurable"
    let ?h = "\<lambda>v::(real, 'n) vec. \<chi> i. if i = m then v $ m + v $ n else v $ i"
    have lin: "linear ?h"
      by (rule linearI) (auto simp: algebra_simps plus_vec_def scaleR_vec_def vec_eq_iff)
    consider "m < n" | " n < m"
      using \<open>m \<noteq> n\<close> less_linear by blast
    then have 1: "det(matrix ?h) = 1"
    proof cases
      assume "m < n"
      have *: "matrix ?h $ i $ j = (0::real)" if "j < i" for i j :: 'n
      proof -
        have "axis j 1 = (\<chi> n. if n = j then 1 else (0::real))"
          using axis_def by blast
        then have "(\<chi> p q. if p = m then axis q 1 $ m + axis q 1 $ n else axis q 1 $ p) $ i $ j = (0::real)"
          using \<open>j < i\<close> axis_def \<open>m < n\<close> by auto
        with \<open>m < n\<close> show ?thesis
          by (auto simp: matrix_def axis_def cong: if_cong)
      qed
      show ?thesis
        using \<open>m \<noteq> n\<close> by (subst det_upperdiagonal [OF *]) (auto simp: matrix_def axis_def cong: if_cong)
    next
      assume "n < m"
      have *: "matrix ?h $ i $ j = (0::real)" if "j > i" for i j :: 'n
      proof -
        have "axis j 1 = (\<chi> n. if n = j then 1 else (0::real))"
          using axis_def by blast
        then have "(\<chi> p q. if p = m then axis q 1 $ m + axis q 1 $ n else axis q 1 $ p) $ i $ j = (0::real)"
          using \<open>j > i\<close> axis_def \<open>m > n\<close> by auto
        with \<open>m > n\<close> show ?thesis
          by (auto simp: matrix_def axis_def cong: if_cong)
      qed
      show ?thesis
        using \<open>m \<noteq> n\<close>
        by (subst det_lowerdiagonal [OF *]) (auto simp: matrix_def axis_def cong: if_cong)
    qed
    have meq: "measure lebesgue (?h ` (cbox a b)) = measure lebesgue (cbox a b)" for a b
    proof (cases "cbox a b = {}")
      case True then show ?thesis by simp
    next
      case False
      then have ne: "(+) (\<chi> i. if i = n then - a $ n else 0) ` cbox a b \<noteq> {}"
        by auto
      let ?v = "\<chi> i. if i = n then - a $ n else 0"
      have "?h ` cbox a b
            = (+) (\<chi> i. if i = m \<or> i = n then a $ n else 0) ` ?h ` (+) ?v ` (cbox a b)"
        using \<open>m \<noteq> n\<close> unfolding image_comp o_def by (force simp: vec_eq_iff)
      then have "measure lebesgue (?h ` (cbox a b))
               = measure lebesgue ((\<lambda>v. \<chi> i. if i = m then v $ m + v $ n else v $ i) `
                                   (+) ?v ` cbox a b)"
        by (rule ssubst) (rule measure_translation)
      also have "\<dots> = measure lebesgue ((\<lambda>v. \<chi> i. if i = m then v $ m + v $ n else v $ i) ` cbox (?v +a) (?v + b))"
        by (metis (no_types, lifting) cbox_translation)
      also have "\<dots> = measure lebesgue ((+) (\<chi> i. if i = n then - a $ n else 0) ` cbox a b)"
        apply (subst measure_shear_interval)
        using \<open>m \<noteq> n\<close> ne apply auto
        apply (simp add: cbox_translation)
        by (metis cbox_borel cbox_translation measure_completion sets_lborel)
      also have "\<dots> = measure lebesgue (cbox a b)"
        by (rule measure_translation)
        finally show ?thesis .
      qed
    show "?h ` S \<in> lmeasurable \<and> ?Q ?h S"
      using measure_linear_sufficient [OF lin \<open>S \<in> lmeasurable\<close>] meq 1 by force
  qed
  with assms show "(f ` S) \<in> lmeasurable" "?Q f S"
    by metis+
qed


lemma
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes f: "orthogonal_transformation f" and S: "S \<in> lmeasurable"
  shows measurable_orthogonal_image: "f ` S \<in> lmeasurable"
    and measure_orthogonal_image: "measure lebesgue (f ` S) = measure lebesgue S"
proof -
  have "linear f"
    by (simp add: f orthogonal_transformation_linear)
  then show "f ` S \<in> lmeasurable"
    by (metis S measurable_linear_image)
  show "measure lebesgue (f ` S) = measure lebesgue S"
    by (simp add: measure_linear_image \<open>linear f\<close> S f)
qed

proposition measure_semicontinuous_with_hausdist_explicit:
  assumes "bounded S" and neg: "negligible(frontier S)" and "e > 0"
  obtains d where "d > 0"
                  "\<And>T. \<lbrakk>T \<in> lmeasurable; \<And>y. y \<in> T \<Longrightarrow> \<exists>x. x \<in> S \<and> dist x y < d\<rbrakk>
                        \<Longrightarrow> measure lebesgue T < measure lebesgue S + e"
proof (cases "S = {}")
  case True
  with that \<open>e > 0\<close> show ?thesis by force
next
  case False
  then have frS: "frontier S \<noteq> {}"
    using \<open>bounded S\<close> frontier_eq_empty not_bounded_UNIV by blast
  have "S \<in> lmeasurable"
    by (simp add: \<open>bounded S\<close> measurable_Jordan neg)
  have null: "(frontier S) \<in> null_sets lebesgue"
    by (metis neg negligible_iff_null_sets)
  have "frontier S \<in> lmeasurable" and mS0: "measure lebesgue (frontier S) = 0"
    using neg negligible_imp_measurable negligible_iff_measure by blast+
  with \<open>e > 0\<close> sets_lebesgue_outer_open
  obtain U where "open U"
    and U: "frontier S \<subseteq> U" "U - frontier S \<in> lmeasurable" "emeasure lebesgue (U - frontier S) < e"
    by (metis fmeasurableD)
  with null have "U \<in> lmeasurable"
    by (metis borel_open measurable_Diff_null_set sets_completionI_sets sets_lborel)
  have "measure lebesgue (U - frontier S) = measure lebesgue U"
    using mS0 by (simp add: \<open>U \<in> lmeasurable\<close> fmeasurableD measure_Diff_null_set null)
  with U have mU: "measure lebesgue U < e"
    by (simp add: emeasure_eq_measure2 ennreal_less_iff)
  show ?thesis
  proof
    have "U \<noteq> UNIV"
      using \<open>U \<in> lmeasurable\<close> by auto
    then have "- U \<noteq> {}"
      by blast
    with \<open>open U\<close> \<open>frontier S \<subseteq> U\<close> show "setdist (frontier S) (- U) > 0"
      by (auto simp: \<open>bounded S\<close> open_closed compact_frontier_bounded setdist_gt_0_compact_closed frS)
    fix T
    assume "T \<in> lmeasurable"
      and T: "\<And>t. t \<in> T \<Longrightarrow> \<exists>y. y \<in> S \<and> dist y t < setdist (frontier S) (- U)"
    then have "measure lebesgue T - measure lebesgue S \<le> measure lebesgue (T - S)"
      by (simp add: \<open>S \<in> lmeasurable\<close> measure_diff_le_measure_setdiff)
    also have "\<dots>  \<le> measure lebesgue U"
    proof -
      have "T - S \<subseteq> U"
      proof clarify
        fix x
        assume "x \<in> T" and "x \<notin> S"
        then obtain y where "y \<in> S" and y: "dist y x < setdist (frontier S) (- U)"
          using T by blast
        have "closed_segment x y \<inter> frontier S \<noteq> {}"
          using connected_Int_frontier \<open>x \<notin> S\<close> \<open>y \<in> S\<close> by blast
        then obtain z where z: "z \<in> closed_segment x y" "z \<in> frontier S"
          by auto
        with y have "dist z x < setdist(frontier S) (- U)"
          by (auto simp: dist_commute dest!: dist_in_closed_segment)
        with z have False if "x \<in> -U"
          using setdist_le_dist [OF \<open>z \<in> frontier S\<close> that] by auto
        then show "x \<in> U"
          by blast
      qed
      then show ?thesis
        by (simp add: \<open>S \<in> lmeasurable\<close> \<open>T \<in> lmeasurable\<close> \<open>U \<in> lmeasurable\<close> fmeasurableD measure_mono_fmeasurable sets.Diff)
    qed
    finally have "measure lebesgue T - measure lebesgue S \<le> measure lebesgue U" .
    with mU show "measure lebesgue T < measure lebesgue S + e"
      by linarith
  qed
qed

proposition
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> lmeasurable"
  and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  and bounded: "\<And>x. x \<in> S \<Longrightarrow> \<bar>det (matrix (f' x))\<bar> \<le> B"
  shows measurable_bounded_differentiable_image:
       "f ` S \<in> lmeasurable"
    and measure_bounded_differentiable_image:
       "measure lebesgue (f ` S) \<le> B * measure lebesgue S" (is "?M")
proof -
  have "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> B * measure lebesgue S"
  proof (cases "B < 0")
    case True
    then have "S = {}"
      by (meson abs_ge_zero bounded empty_iff equalityI less_le_trans linorder_not_less subsetI)
    then show ?thesis
      by auto
  next
    case False
    then have "B \<ge> 0"
      by arith
    let ?\<mu> = "measure lebesgue"
    have f_diff: "f differentiable_on S"
      using deriv by (auto simp: differentiable_on_def differentiable_def)
    have eps: "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> (B+e) * ?\<mu> S" (is "?ME")
              if "e > 0" for e
    proof -
      have eps_d: "f ` S \<in> lmeasurable"  "?\<mu> (f ` S) \<le> (B+e) * (?\<mu> S + d)" (is "?MD")
                  if "d > 0" for d
      proof -
        obtain T where T: "open T" "S \<subseteq> T" and TS: "(T-S) \<in> lmeasurable" and "emeasure lebesgue (T-S) < ennreal d"
          using S \<open>d > 0\<close> sets_lebesgue_outer_open by blast
        then have "?\<mu> (T-S) < d"
          by (metis emeasure_eq_measure2 ennreal_leI not_less)
        with S T TS have "T \<in> lmeasurable" and Tless: "?\<mu> T < ?\<mu> S + d"
          by (auto simp: measurable_measure_Diff dest!: fmeasurable_Diff_D)
        have "\<exists>r. 0 < r \<and> r < d \<and> ball x r \<subseteq> T \<and> f ` (S \<inter> ball x r) \<in> lmeasurable \<and>
                  ?\<mu> (f ` (S \<inter> ball x r)) \<le> (B + e) * ?\<mu> (ball x r)"
          if "x \<in> S" "d > 0" for x d
        proof -
          have lin: "linear (f' x)"
            and lim0: "((\<lambda>y. (f y - (f x + f' x (y - x))) /\<^sub>R norm(y - x)) \<longlongrightarrow> 0) (at x within S)"
            using deriv \<open>x \<in> S\<close> by (auto simp: has_derivative_within bounded_linear.linear field_simps)
          have bo: "bounded (f' x ` ball 0 1)"
            by (simp add: bounded_linear_image linear_linear lin)
          have neg: "negligible (frontier (f' x ` ball 0 1))"
            using deriv has_derivative_linear \<open>x \<in> S\<close>
            by (auto intro!: negligible_convex_frontier [OF convex_linear_image])
          let ?unit_vol = "content (ball (0 :: real ^ 'n :: {finite, wellorder}) 1)"
          have 0: "0 < e * ?unit_vol"
            using \<open>e > 0\<close> by (simp add: content_ball_pos)
          obtain k where "k > 0" and k:
                  "\<And>U. \<lbrakk>U \<in> lmeasurable; \<And>y. y \<in> U \<Longrightarrow> \<exists>z. z \<in> f' x ` ball 0 1 \<and> dist z y < k\<rbrakk>
                        \<Longrightarrow> ?\<mu> U < ?\<mu> (f' x ` ball 0 1) + e * ?unit_vol"
            using measure_semicontinuous_with_hausdist_explicit [OF bo neg 0] by blast
          obtain l where "l > 0" and l: "ball x l \<subseteq> T"
            using \<open>x \<in> S\<close> \<open>open T\<close> \<open>S \<subseteq> T\<close> openE by blast
          obtain \<zeta> where "0 < \<zeta>"
            and \<zeta>: "\<And>y. \<lbrakk>y \<in> S; y \<noteq> x; dist y x < \<zeta>\<rbrakk>
                        \<Longrightarrow> norm (f y - (f x + f' x (y - x))) / norm (y - x) < k"
            using lim0 \<open>k > 0\<close> by (simp add: Lim_within) (auto simp add: field_simps)
          define r where "r \<equiv> min (min l (\<zeta>/2)) (min 1 (d/2))"
          show ?thesis
          proof (intro exI conjI)
            show "r > 0" "r < d"
              using \<open>l > 0\<close> \<open>\<zeta> > 0\<close> \<open>d > 0\<close> by (auto simp: r_def)
            have "r \<le> l"
              by (auto simp: r_def)
            with l show "ball x r \<subseteq> T"
              by auto
            have ex_lessK: "\<exists>x' \<in> ball 0 1. dist (f' x x') ((f y - f x) /\<^sub>R r) < k"
              if "y \<in> S" and "dist x y < r" for y
            proof (cases "y = x")
              case True
              with lin linear_0 \<open>k > 0\<close> that show ?thesis
                by (rule_tac x=0 in bexI) (auto simp: linear_0)
            next
              case False
              then show ?thesis
              proof (rule_tac x="(y - x) /\<^sub>R r" in bexI)
                have "f' x ((y - x) /\<^sub>R r) = f' x (y - x) /\<^sub>R r"
                  by (simp add: lin linear_scale)
                then have "dist (f' x ((y - x) /\<^sub>R r)) ((f y - f x) /\<^sub>R r) = norm (f' x (y - x) /\<^sub>R r - (f y - f x) /\<^sub>R r)"
                  by (simp add: dist_norm)
                also have "\<dots> = norm (f' x (y - x) - (f y - f x)) / r"
                  using \<open>r > 0\<close> by (simp add: divide_simps scale_right_diff_distrib [symmetric])
                also have "\<dots> \<le> norm (f y - (f x + f' x (y - x))) / norm (y - x)"
                  using that \<open>r > 0\<close> False by (simp add: field_split_simps dist_norm norm_minus_commute mult_right_mono)
                also have "\<dots> < k"
                  using that \<open>0 < \<zeta>\<close> by (simp add: dist_commute r_def  \<zeta> [OF \<open>y \<in> S\<close> False])
                finally show "dist (f' x ((y - x) /\<^sub>R r)) ((f y - f x) /\<^sub>R r) < k" .
                show "(y - x) /\<^sub>R r \<in> ball 0 1"
                  using that \<open>r > 0\<close> by (simp add: dist_norm divide_simps norm_minus_commute)
              qed
            qed
            let ?rfs = "(\<lambda>x. x /\<^sub>R r) ` (+) (- f x) ` f ` (S \<inter> ball x r)"
            have rfs_mble: "?rfs \<in> lmeasurable"
            proof (rule bounded_set_imp_lmeasurable)
              have "f differentiable_on S \<inter> ball x r"
                using f_diff by (auto simp: fmeasurableD differentiable_on_subset)
              with S show "?rfs \<in> sets lebesgue"
                by (auto simp: sets.Int intro!: lebesgue_sets_translation differentiable_image_in_sets_lebesgue)
              let ?B = "(\<lambda>(x, y). x + y) ` (f' x ` ball 0 1 \<times> ball 0 k)"
              have "bounded ?B"
                by (simp add: bounded_plus [OF bo])
              moreover have "?rfs \<subseteq> ?B"
                apply (auto simp: dist_norm image_iff dest!: ex_lessK)
                by (metis (no_types, hide_lams) add.commute diff_add_cancel dist_0_norm dist_commute dist_norm mem_ball)
              ultimately show "bounded (?rfs)"
                by (rule bounded_subset)
            qed
            then have "(\<lambda>x. r *\<^sub>R x) ` ?rfs \<in> lmeasurable"
              by (simp add: measurable_linear_image)
            with \<open>r > 0\<close> have "(+) (- f x) ` f ` (S \<inter> ball x r) \<in> lmeasurable"
              by (simp add: image_comp o_def)
            then have "(+) (f x) ` (+) (- f x) ` f ` (S \<inter> ball x r) \<in> lmeasurable"
              using  measurable_translation by blast
            then show fsb: "f ` (S \<inter> ball x r) \<in> lmeasurable"
              by (simp add: image_comp o_def)
            have "?\<mu> (f ` (S \<inter> ball x r)) = ?\<mu> (?rfs) * r ^ CARD('n)"
              using \<open>r > 0\<close> fsb
              by (simp add: measure_linear_image measure_translation_subtract measurable_translation_subtract field_simps cong: image_cong_simp)
            also have "\<dots> \<le> (\<bar>det (matrix (f' x))\<bar> * ?unit_vol + e * ?unit_vol) * r ^ CARD('n)"
            proof -
              have "?\<mu> (?rfs) < ?\<mu> (f' x ` ball 0 1) + e * ?unit_vol"
                using rfs_mble by (force intro: k dest!: ex_lessK)
              then have "?\<mu> (?rfs) < \<bar>det (matrix (f' x))\<bar> * ?unit_vol + e * ?unit_vol"
                by (simp add: lin measure_linear_image [of "f' x"])
              with \<open>r > 0\<close> show ?thesis
                by auto
            qed
            also have "\<dots> \<le> (B + e) * ?\<mu> (ball x r)"
              using bounded [OF \<open>x \<in> S\<close>] \<open>r > 0\<close>
              by (simp add: algebra_simps content_ball_conv_unit_ball[of r] content_ball_pos)
            finally show "?\<mu> (f ` (S \<inter> ball x r)) \<le> (B + e) * ?\<mu> (ball x r)" .
          qed
        qed
        then obtain r where
          r0d: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow> 0 < r x d \<and> r x d < d"
          and rT: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow> ball x (r x d) \<subseteq> T"
          and r: "\<And>x d. \<lbrakk>x \<in> S; d > 0\<rbrakk> \<Longrightarrow>
                  (f ` (S \<inter> ball x (r x d))) \<in> lmeasurable \<and>
                  ?\<mu> (f ` (S \<inter> ball x (r x d))) \<le> (B + e) * ?\<mu> (ball x (r x d))"
          by metis
        obtain C where "countable C" and Csub: "C \<subseteq> {(x,r x t) |x t. x \<in> S \<and> 0 < t}"
          and pwC: "pairwise (\<lambda>i j. disjnt (ball (fst i) (snd i)) (ball (fst j) (snd j))) C"
          and negC: "negligible(S - (\<Union>i \<in> C. ball (fst i) (snd i)))"
          apply (rule Vitali_covering_theorem_balls [of S "{(x,r x t) |x t. x \<in> S \<and> 0 < t}" fst snd])
           apply auto
          by (metis dist_eq_0_iff r0d)
        let ?UB = "(\<Union>(x,s) \<in> C. ball x s)"
        have eq: "f ` (S \<inter> ?UB) = (\<Union>(x,s) \<in> C. f ` (S \<inter> ball x s))"
          by auto
        have mle: "?\<mu> (\<Union>(x,s) \<in> K. f ` (S \<inter> ball x s)) \<le> (B + e) * (?\<mu> S + d)"  (is "?l \<le> ?r")
          if "K \<subseteq> C" and "finite K" for K
        proof -
          have gt0: "b > 0" if "(a, b) \<in> K" for a b
            using Csub that \<open>K \<subseteq> C\<close> r0d by auto
          have inj: "inj_on (\<lambda>(x, y). ball x y) K"
            by (force simp: inj_on_def ball_eq_ball_iff dest: gt0)
          have disjnt: "disjoint ((\<lambda>(x, y). ball x y) ` K)"
            using pwC that
            apply (clarsimp simp: pairwise_def case_prod_unfold ball_eq_ball_iff)
            by (metis subsetD fst_conv snd_conv)
          have "?l \<le> (\<Sum>i\<in>K. ?\<mu> (case i of (x, s) \<Rightarrow> f ` (S \<inter> ball x s)))"
          proof (rule measure_UNION_le [OF \<open>finite K\<close>], clarify)
            fix x r
            assume "(x,r) \<in> K"
            then have "x \<in> S"
              using Csub \<open>K \<subseteq> C\<close> by auto
            show "f ` (S \<inter> ball x r) \<in> sets lebesgue"
              by (meson Int_lower1 S differentiable_on_subset f_diff fmeasurableD lmeasurable_ball order_refl sets.Int differentiable_image_in_sets_lebesgue)
          qed
          also have "\<dots> \<le> (\<Sum>(x,s) \<in> K. (B + e) * ?\<mu> (ball x s))"
            apply (rule sum_mono)
            using Csub r \<open>K \<subseteq> C\<close> by auto
          also have "\<dots> = (B + e) * (\<Sum>(x,s) \<in> K. ?\<mu> (ball x s))"
            by (simp add: prod.case_distrib sum_distrib_left)
          also have "\<dots> = (B + e) * sum ?\<mu> ((\<lambda>(x, y). ball x y) ` K)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> by (simp add: inj sum.reindex prod.case_distrib)
          also have "\<dots> = (B + e) * ?\<mu> (\<Union>(x,s) \<in> K. ball x s)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that
            by (subst measure_Union') (auto simp: disjnt measure_Union')
          also have "\<dots> \<le> (B + e) * ?\<mu> T"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that apply simp
            apply (rule measure_mono_fmeasurable [OF _ _ \<open>T \<in> lmeasurable\<close>])
            using Csub rT by force+
          also have "\<dots> \<le> (B + e) * (?\<mu> S + d)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> Tless by simp
          finally show ?thesis .
        qed
        have fSUB_mble: "(f ` (S \<inter> ?UB)) \<in> lmeasurable"
          unfolding eq using Csub r False \<open>e > 0\<close> that
          by (auto simp: intro!: fmeasurable_UN_bound [OF \<open>countable C\<close> _ mle])
        have fSUB_meas: "?\<mu> (f ` (S \<inter> ?UB)) \<le> (B + e) * (?\<mu> S + d)"  (is "?MUB")
          unfolding eq using Csub r False \<open>e > 0\<close> that
          by (auto simp: intro!: measure_UN_bound [OF \<open>countable C\<close> _ mle])
        have neg: "negligible ((f ` (S \<inter> ?UB) - f ` S) \<union> (f ` S - f ` (S \<inter> ?UB)))"
        proof (rule negligible_subset [OF negligible_differentiable_image_negligible [OF order_refl negC, where f=f]])
          show "f differentiable_on S - (\<Union>i\<in>C. ball (fst i) (snd i))"
            by (meson DiffE differentiable_on_subset subsetI f_diff)
        qed force
        show "f ` S \<in> lmeasurable"
          by (rule lmeasurable_negligible_symdiff [OF fSUB_mble neg])
        show ?MD
          using fSUB_meas measure_negligible_symdiff [OF fSUB_mble neg] by simp
      qed
      show "f ` S \<in> lmeasurable"
        using eps_d [of 1] by simp
      show ?ME
      proof (rule field_le_epsilon)
        fix \<delta> :: real
        assume "0 < \<delta>"
        then show "?\<mu> (f ` S) \<le> (B + e) * ?\<mu> S + \<delta>"
          using eps_d [of "\<delta> / (B+e)"] \<open>e > 0\<close> \<open>B \<ge> 0\<close> by (auto simp: divide_simps mult_ac)
      qed
    qed
    show ?thesis
    proof (cases "?\<mu> S = 0")
      case True
      with eps have "?\<mu> (f ` S) = 0"
        by (metis mult_zero_right not_le zero_less_measure_iff)
      then show ?thesis
        using eps [of 1] by (simp add: True)
    next
      case False
      have "?\<mu> (f ` S) \<le> B * ?\<mu> S"
      proof (rule field_le_epsilon)
        fix e :: real
        assume "e > 0"
        then show "?\<mu> (f ` S) \<le> B * ?\<mu> S + e"
          using eps [of "e / ?\<mu> S"] False by (auto simp: algebra_simps zero_less_measure_iff)
      qed
      with eps [of 1] show ?thesis by auto
    qed
  qed
  then show "f ` S \<in> lmeasurable" ?M by blast+
qed

lemma m_diff_image_weak:
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> lmeasurable"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
proof -
  let ?\<mu> = "measure lebesgue"
  have aint_S: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on S"
    using int unfolding absolutely_integrable_on_def by auto
  define m where "m \<equiv> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
  have *: "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
    if "e > 0" for e
  proof -
    define T where "T \<equiv> \<lambda>n. {x \<in> S. n * e \<le> \<bar>det (matrix (f' x))\<bar> \<and>
                                     \<bar>det (matrix (f' x))\<bar> < (Suc n) * e}"
    have meas_t: "T n \<in> lmeasurable" for n
    proof -
      have *: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) \<in> borel_measurable (lebesgue_on S)"
        using aint_S by (simp add: S borel_measurable_restrict_space_iff fmeasurableD set_integrable_def)
      have [intro]: "x \<in> sets (lebesgue_on S) \<Longrightarrow> x \<in> sets lebesgue" for x
        using S sets_restrict_space_subset by blast
      have "{x \<in> S. real n * e \<le> \<bar>det (matrix (f' x))\<bar>} \<in> sets lebesgue"
        using * by (auto simp: borel_measurable_iff_halfspace_ge space_restrict_space)
      then have 1: "{x \<in> S. real n * e \<le> \<bar>det (matrix (f' x))\<bar>} \<in> lmeasurable"
        using S by (simp add: fmeasurableI2)
      have "{x \<in> S. \<bar>det (matrix (f' x))\<bar> < (1 + real n) * e} \<in> sets lebesgue"
        using * by (auto simp: borel_measurable_iff_halfspace_less space_restrict_space)
      then have 2: "{x \<in> S. \<bar>det (matrix (f' x))\<bar> < (1 + real n) * e} \<in> lmeasurable"
        using S by (simp add: fmeasurableI2)
      show ?thesis
        using fmeasurable.Int [OF 1 2] by (simp add: T_def Int_def cong: conj_cong)
    qed
    have aint_T: "\<And>k. (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on T k"
      using set_integrable_subset [OF aint_S] meas_t T_def by blast
    have Seq: "S = (\<Union>n. T n)"
      apply (auto simp: T_def)
      apply (rule_tac x="nat(floor(abs(det(matrix(f' x))) / e))" in exI)
      using that apply auto
      using of_int_floor_le pos_le_divide_eq apply blast
      by (metis add.commute pos_divide_less_eq real_of_int_floor_add_one_gt)
    have meas_ft: "f ` T n \<in> lmeasurable" for n
    proof (rule measurable_bounded_differentiable_image)
      show "T n \<in> lmeasurable"
        by (simp add: meas_t)
    next
      fix x :: "(real,'n) vec"
      assume "x \<in> T n"
      show "(f has_derivative f' x) (at x within T n)"
        by (metis (no_types, lifting) \<open>x \<in> T n\<close> deriv has_derivative_subset mem_Collect_eq subsetI T_def)
      show "\<bar>det (matrix (f' x))\<bar> \<le> (Suc n) * e"
        using \<open>x \<in> T n\<close> T_def by auto
    next
      show "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on T n"
        using aint_T absolutely_integrable_on_def by blast
    qed
    have disT: "disjoint (range T)"
      unfolding disjoint_def
    proof clarsimp
      show "T m \<inter> T n = {}" if "T m \<noteq> T n" for m n
        using that
      proof (induction m n rule: linorder_less_wlog)
        case (less m n)
        with \<open>e > 0\<close> show ?case
          unfolding T_def
          proof (clarsimp simp add: Collect_conj_eq [symmetric])
            fix x
            assume "e > 0"  "m < n"  "n * e \<le> \<bar>det (matrix (f' x))\<bar>"  "\<bar>det (matrix (f' x))\<bar> < (1 + real m) * e"
            then have "n < 1 + real m"
              by (metis (no_types, hide_lams) less_le_trans mult.commute not_le mult_le_cancel_iff2)
            then show "False"
              using less.hyps by linarith
          qed
      qed auto
    qed
    have injT: "inj_on T ({n. T n \<noteq> {}})"
      unfolding inj_on_def
    proof clarsimp
      show "m = n" if "T m = T n" "T n \<noteq> {}" for m n
        using that
      proof (induction m n rule: linorder_less_wlog)
        case (less m n)
        have False if "T n \<subseteq> T m" "x \<in> T n" for x
          using \<open>e > 0\<close> \<open>m < n\<close> that
          apply (auto simp: T_def  mult.commute intro: less_le_trans dest!: subsetD)
          by (metis add.commute less_le_trans nat_less_real_le not_le mult_le_cancel_iff2)
        then show ?case
          using less.prems by blast
      qed auto
    qed
    have sum_eq_Tim: "(\<Sum>k\<le>n. f (T k)) = sum f (T ` {..n})" if "f {} = 0" for f :: "_ \<Rightarrow> real" and n
    proof (subst sum.reindex_nontrivial)
      fix i j  assume "i \<in> {..n}" "j \<in> {..n}" "i \<noteq> j" "T i = T j"
      with that  injT [unfolded inj_on_def] show "f (T i) = 0"
        by simp metis
    qed (use atMost_atLeast0 in auto)
    let ?B = "m + e * ?\<mu> S"
    have "(\<Sum>k\<le>n. ?\<mu> (f ` T k)) \<le> ?B" for n
    proof -
      have "(\<Sum>k\<le>n. ?\<mu> (f ` T k)) \<le> (\<Sum>k\<le>n. ((k+1) * e) * ?\<mu>(T k))"
      proof (rule sum_mono [OF measure_bounded_differentiable_image])
        show "(f has_derivative f' x) (at x within T k)" if "x \<in> T k" for k x
          using that unfolding T_def by (blast intro: deriv has_derivative_subset)
        show "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on T k" for k
          using absolutely_integrable_on_def aint_T by blast
        show "\<bar>det (matrix (f' x))\<bar> \<le> real (k + 1) * e" if "x \<in> T k" for k x
          using T_def that by auto
      qed (use meas_t in auto)
      also have "\<dots> \<le> (\<Sum>k\<le>n. (k * e) * ?\<mu>(T k)) + (\<Sum>k\<le>n. e * ?\<mu>(T k))"
        by (simp add: algebra_simps sum.distrib)
      also have "\<dots> \<le> ?B"
      proof (rule add_mono)
        have "(\<Sum>k\<le>n. real k * e * ?\<mu> (T k)) = (\<Sum>k\<le>n. integral (T k) (\<lambda>x. k * e))"
          by (simp add: lmeasure_integral [OF meas_t]
                   flip: integral_mult_right integral_mult_left)
        also have "\<dots> \<le> (\<Sum>k\<le>n. integral (T k) (\<lambda>x.  (abs (det (matrix (f' x))))))"
        proof (rule sum_mono)
          fix k
          assume "k \<in> {..n}"
          show "integral (T k) (\<lambda>x. k * e) \<le> integral (T k) (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
          proof (rule integral_le [OF integrable_on_const [OF meas_t]])
            show "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on T k"
              using absolutely_integrable_on_def aint_T by blast
          next
            fix x assume "x \<in> T k"
            show "k * e \<le> \<bar>det (matrix (f' x))\<bar>"
              using \<open>x \<in> T k\<close> T_def by blast
          qed
        qed
        also have "\<dots> = sum (\<lambda>T. integral T (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)) (T ` {..n})"
          by (auto intro: sum_eq_Tim)
        also have "\<dots> = integral (\<Union>k\<le>n. T k) (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
        proof (rule integral_unique [OF has_integral_Union, symmetric])
          fix S  assume "S \<in> T ` {..n}"
          then show "((\<lambda>x. \<bar>det (matrix (f' x))\<bar>) has_integral integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)) S"
          using absolutely_integrable_on_def aint_T by blast
        next
          show "pairwise (\<lambda>S S'. negligible (S \<inter> S')) (T ` {..n})"
            using disT unfolding disjnt_iff by (auto simp: pairwise_def intro!: empty_imp_negligible)
        qed auto
        also have "\<dots> \<le> m"
          unfolding m_def
        proof (rule integral_subset_le)
          have "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on (\<Union>k\<le>n. T k)"
            apply (rule set_integrable_subset [OF aint_S])
             apply (intro measurable meas_t fmeasurableD)
            apply (force simp: Seq)
            done
          then show "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on (\<Union>k\<le>n. T k)"
            using absolutely_integrable_on_def by blast
        qed (use Seq int in auto)
        finally show "(\<Sum>k\<le>n. real k * e * ?\<mu> (T k)) \<le> m" .
      next
        have "(\<Sum>k\<le>n. ?\<mu> (T k)) = sum ?\<mu> (T ` {..n})"
          by (auto intro: sum_eq_Tim)
        also have "\<dots> = ?\<mu> (\<Union>k\<le>n. T k)"
          using S disT by (auto simp: pairwise_def meas_t intro: measure_Union' [symmetric])
        also have "\<dots> \<le> ?\<mu> S"
          using S by (auto simp: Seq intro: meas_t fmeasurableD measure_mono_fmeasurable)
        finally have "(\<Sum>k\<le>n. ?\<mu> (T k)) \<le> ?\<mu> S" .
        then show "(\<Sum>k\<le>n. e * ?\<mu> (T k)) \<le> e * ?\<mu> S"
          by (metis less_eq_real_def ordered_comm_semiring_class.comm_mult_left_mono sum_distrib_left that)
      qed
      finally show "(\<Sum>k\<le>n. ?\<mu> (f ` T k)) \<le> ?B" .
    qed
    moreover have "measure lebesgue (\<Union>k\<le>n. f ` T k) \<le> (\<Sum>k\<le>n. ?\<mu> (f ` T k))" for n
      by (simp add: fmeasurableD meas_ft measure_UNION_le)
    ultimately have B_ge_m: "?\<mu> (\<Union>k\<le>n. (f ` T k)) \<le> ?B" for n
      by (meson order_trans)
    have "(\<Union>n. f ` T n) \<in> lmeasurable"
      by (rule fmeasurable_countable_Union [OF meas_ft B_ge_m])
    moreover have "?\<mu> (\<Union>n. f ` T n) \<le> m + e * ?\<mu> S"
      by (rule measure_countable_Union_le [OF meas_ft B_ge_m])
    ultimately show "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
      by (auto simp: Seq image_Union)
  qed
  show ?thesis
  proof
    show "f ` S \<in> lmeasurable"
      using * linordered_field_no_ub by blast
    let ?x = "m - ?\<mu> (f ` S)"
    have False if "?\<mu> (f ` S) > integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
    proof -
      have ml: "m < ?\<mu> (f ` S)"
        using m_def that by blast
      then have "?\<mu> S \<noteq> 0"
        using "*"(2) bgauge_existence_lemma by fastforce
      with ml have 0: "0 < - (m - ?\<mu> (f ` S))/2 / ?\<mu> S"
        using that zero_less_measure_iff by force
      then show ?thesis
        using * [OF 0] that by (auto simp: field_split_simps m_def split: if_split_asm)
    qed
    then show "?\<mu> (f ` S) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
      by fastforce
  qed
qed


theorem
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows measurable_differentiable_image: "f ` S \<in> lmeasurable"
    and measure_differentiable_image:
       "measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)" (is "?M")
proof -
  let ?I = "\<lambda>n::nat. cbox (vec (-n)) (vec n) \<inter> S"
  let ?\<mu> = "measure lebesgue"
  have "x \<in> cbox (vec (- real (nat \<lceil>norm x\<rceil>))) (vec (real (nat \<lceil>norm x\<rceil>)))" for x :: "real^'n::_"
    apply (auto simp: mem_box_cart)
    apply (metis abs_le_iff component_le_norm_cart minus_le_iff of_nat_ceiling order.trans)
    by (meson abs_le_D1 norm_bound_component_le_cart real_nat_ceiling_ge)
  then have Seq: "S = (\<Union>n. ?I n)"
    by auto
  have fIn: "f ` ?I n \<in> lmeasurable"
       and mfIn: "?\<mu> (f ` ?I n) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)" (is ?MN) for n
  proof -
    have In: "?I n \<in> lmeasurable"
      by (simp add: S bounded_Int bounded_set_imp_lmeasurable sets.Int)
    moreover have "\<And>x. x \<in> ?I n \<Longrightarrow> (f has_derivative f' x) (at x within ?I n)"
      by (meson Int_iff deriv has_derivative_subset subsetI)
    moreover have int_In: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on ?I n"
    proof -
      have "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on S"
        using int absolutely_integrable_integrable_bound by force
      then have "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on ?I n"
        by (metis (no_types) Int_lower1 In fmeasurableD inf_commute set_integrable_subset)
      then show ?thesis
        using absolutely_integrable_on_def by blast
    qed
    ultimately have "f ` ?I n \<in> lmeasurable" "?\<mu> (f ` ?I n) \<le> integral (?I n) (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
      using m_diff_image_weak by metis+
    moreover have "integral (?I n) (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
      by (simp add: int_In int integral_subset_le)
    ultimately show "f ` ?I n \<in> lmeasurable" ?MN
      by auto
  qed
  have "?I k \<subseteq> ?I n" if "k \<le> n" for k n
    by (rule Int_mono) (use that in \<open>auto simp: subset_interval_imp_cart\<close>)
  then have "(\<Union>k\<le>n. f ` ?I k) = f ` ?I n" for n
    by (fastforce simp add:)
  with mfIn have "?\<mu> (\<Union>k\<le>n. f ` ?I k) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)" for n
    by simp
  then have "(\<Union>n. f ` ?I n) \<in> lmeasurable" "?\<mu> (\<Union>n. f ` ?I n) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
    by (rule fmeasurable_countable_Union [OF fIn] measure_countable_Union_le [OF fIn])+
  then show "f ` S \<in> lmeasurable" ?M
    by (metis Seq image_UN)+
qed


lemma borel_measurable_simple_function_limit_increasing:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  shows "(f \<in> borel_measurable lebesgue \<and> (\<forall>x. 0 \<le> f x)) \<longleftrightarrow>
         (\<exists>g. (\<forall>n x. 0 \<le> g n x \<and> g n x \<le> f x) \<and> (\<forall>n x. g n x \<le> (g(Suc n) x)) \<and>
              (\<forall>n. g n \<in> borel_measurable lebesgue) \<and> (\<forall>n. finite(range (g n))) \<and>
              (\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x))"
         (is "?lhs = ?rhs")
proof
  assume f: ?lhs
  have leb_f: "{x. a \<le> f x \<and> f x < b} \<in> sets lebesgue" for a b
  proof -
    have "{x. a \<le> f x \<and> f x < b} = {x. f x < b} - {x. f x < a}"
      by auto
    also have "\<dots> \<in> sets lebesgue"
      using borel_measurable_vimage_halfspace_component_lt [of f UNIV] f by auto
    finally show ?thesis .
  qed
  have "g n x \<le> f x"
        if inc_g: "\<And>n x. 0 \<le> g n x \<and> g n x \<le> g (Suc n) x"
           and meas_g: "\<And>n. g n \<in> borel_measurable lebesgue"
           and fin: "\<And>n. finite(range (g n))" and lim: "\<And>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x" for g n x
  proof -
    have "\<exists>r>0. \<forall>N. \<exists>n\<ge>N. dist (g n x) (f x) \<ge> r" if "g n x > f x"
    proof -
      have g: "g n x \<le> g (N + n) x" for N
        by (rule transitive_stepwise_le) (use inc_g in auto)
      have "\<exists>na\<ge>N. g n x - f x \<le> dist (g na x) (f x)" for N
        apply (rule_tac x="N+n" in exI)
        using g [of N] by (auto simp: dist_norm)
      with that show ?thesis
        using diff_gt_0_iff_gt by blast
    qed
    with lim show ?thesis
      apply (auto simp: lim_sequentially)
      by (meson less_le_not_le not_le_imp_less)
  qed
  moreover
  let ?\<Omega> = "\<lambda>n k. indicator {y. k/2^n \<le> f y \<and> f y < (k+1)/2^n}"
  let ?g = "\<lambda>n x. (\<Sum>k::real | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x)"
  have "\<exists>g. (\<forall>n x. 0 \<le> g n x \<and> g n x \<le> (g(Suc n) x)) \<and>
             (\<forall>n. g n \<in> borel_measurable lebesgue) \<and> (\<forall>n. finite(range (g n))) \<and>(\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x)"
  proof (intro exI allI conjI)
    show "0 \<le> ?g n x" for n x
    proof (clarify intro!: ordered_comm_monoid_add_class.sum_nonneg)
      fix k::real
      assume "k \<in> \<int>" and k: "\<bar>k\<bar> \<le> 2 ^ (2*n)"
      show "0 \<le> k/2^n * ?\<Omega> n k x"
        using f \<open>k \<in> \<int>\<close> apply (auto simp: indicator_def field_split_simps Ints_def)
        apply (drule spec [where x=x])
        using zero_le_power [of "2::real" n] mult_nonneg_nonneg [of "f x" "2^n"]
        by linarith
    qed
    show "?g n x \<le> ?g (Suc n) x" for n x
    proof -
      have "?g n x =
            (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n).
              k/2^n * (indicator {y. k/2^n \<le> f y \<and> f y < (k+1/2)/2^n} x +
              indicator {y. (k+1/2)/2^n \<le> f y \<and> f y < (k+1)/2^n} x))"
        by (rule sum.cong [OF refl]) (simp add: indicator_def field_split_simps)
      also have "\<dots> = (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * indicator {y. k/2^n \<le> f y \<and> f y < (k+1/2)/2^n} x) +
                       (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * indicator {y. (k+1/2)/2^n \<le> f y \<and> f y < (k+1)/2^n} x)"
        by (simp add:  comm_monoid_add_class.sum.distrib algebra_simps)
      also have "\<dots> = (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). (2 * k)/2 ^ Suc n * indicator {y. (2 * k)/2 ^ Suc n \<le> f y \<and> f y < (2 * k+1)/2 ^ Suc n} x) +
                       (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). (2 * k)/2 ^ Suc n * indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < ((2 * k+1) + 1)/2 ^ Suc n} x)"
        by (force simp: field_simps indicator_def intro: sum.cong)
      also have "\<dots> \<le> (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2 * Suc n). k/2 ^ Suc n * (indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x))"
                (is "?a + _ \<le> ?b")
      proof -
        have *: "\<lbrakk>sum f I \<le> sum h I; a + sum h I \<le> b\<rbrakk> \<Longrightarrow> a + sum f I \<le> b" for I a b f and h :: "real\<Rightarrow>real"
          by linarith
        let ?h = "\<lambda>k. (2*k+1)/2 ^ Suc n *
                      (indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < ((2*k+1) + 1)/2 ^ Suc n} x)"
        show ?thesis
        proof (rule *)
          show "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n).
                  2 * k/2 ^ Suc n * indicator {y. (2 * k+1)/2 ^ Suc n \<le> f y \<and> f y < (2 * k+1 + 1)/2 ^ Suc n} x)
                \<le> sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}"
            by (rule sum_mono) (simp add: indicator_def field_split_simps)
        next
          have \<alpha>: "?a = (\<Sum>k \<in> (*)2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                         k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            by (auto simp: inj_on_def field_simps comm_monoid_add_class.sum.reindex)
          have \<beta>: "sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}
                   = (\<Sum>k \<in> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                      k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            by (auto simp: inj_on_def field_simps comm_monoid_add_class.sum.reindex)
          have 0: "(*) 2 ` {k \<in> \<int>. P k} \<inter> (\<lambda>x. 2 * x + 1) ` {k \<in> \<int>. P k} = {}" for P :: "real \<Rightarrow> bool"
          proof -
            have "2 * i \<noteq> 2 * j + 1" for i j :: int by arith
            thus ?thesis
              unfolding Ints_def by auto (use of_int_eq_iff in fastforce)
          qed
          have "?a + sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}
                = (\<Sum>k \<in> (*)2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}.
                  k/2 ^ Suc n * indicator {y. k/2 ^ Suc n \<le> f y \<and> f y < (k+1)/2 ^ Suc n} x)"
            unfolding \<alpha> \<beta>
            using finite_abs_int_segment [of "2 ^ (2*n)"]
            by (subst sum_Un) (auto simp: 0)
          also have "\<dots> \<le> ?b"
          proof (rule sum_mono2)
            show "finite {k::real. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)}"
              by (rule finite_abs_int_segment)
            show "(*) 2 ` {k::real. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2^(2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2^(2*n)} \<subseteq> {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)}"
              apply auto
              using one_le_power [of "2::real" "2*n"]  by linarith
            have *: "\<lbrakk>x \<in> (S \<union> T) - U; \<And>x. x \<in> S \<Longrightarrow> x \<in> U; \<And>x. x \<in> T \<Longrightarrow> x \<in> U\<rbrakk> \<Longrightarrow> P x" for S T U P
              by blast
            have "0 \<le> b" if "b \<in> \<int>" "f x * (2 * 2^n) < b + 1" for b
            proof -
              have "0 \<le> f x * (2 * 2^n)"
                by (simp add: f)
              also have "\<dots> < b+1"
                by (simp add: that)
              finally show "0 \<le> b"
                using \<open>b \<in> \<int>\<close> by (auto simp: elim!: Ints_cases)
            qed
            then show "0 \<le> b/2 ^ Suc n * indicator {y. b/2 ^ Suc n \<le> f y \<and> f y < (b + 1)/2 ^ Suc n} x"
                  if "b \<in> {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2 * Suc n)} -
                          ((*) 2 ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<union> (\<lambda>x. 2*x + 1) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)})" for b
              using that by (simp add: indicator_def divide_simps)
          qed
          finally show "?a + sum ?h {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)} \<le> ?b" .
        qed
      qed
      finally show ?thesis .
    qed
    show "?g n \<in> borel_measurable lebesgue" for n
      apply (intro borel_measurable_indicator borel_measurable_times borel_measurable_sum)
      using leb_f sets_restrict_UNIV by auto
    show "finite (range (?g n))" for n
    proof -
      have "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x)
              \<in> (\<lambda>k. k/2^n) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)}" for x
      proof (cases "\<exists>k. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n) \<and> k/2^n \<le> f x \<and> f x < (k+1)/2^n")
        case True
        then show ?thesis
          by (blast intro: indicator_sum_eq)
      next
        case False
        then have "(\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) = 0"
          by auto
        then show ?thesis by force
      qed
      then have "range (?g n) \<subseteq> ((\<lambda>k. (k/2^n)) ` {k. k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n)})"
        by auto
      moreover have "finite ((\<lambda>k::real. (k/2^n)) ` {k \<in> \<int>. \<bar>k\<bar> \<le> 2 ^ (2*n)})"
        by (intro finite_imageI finite_abs_int_segment)
      ultimately show ?thesis
        by (rule finite_subset)
    qed
    show "(\<lambda>n. ?g n x) \<longlonglongrightarrow> f x" for x
    proof (clarsimp simp add: lim_sequentially)
      fix e::real
      assume "e > 0"
      obtain N1 where N1: "2 ^ N1 > abs(f x)"
        using real_arch_pow by fastforce
      obtain N2 where N2: "(1/2) ^ N2 < e"
        using real_arch_pow_inv \<open>e > 0\<close> by fastforce
      have "dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) (f x) < e" if "N1 + N2 \<le> n" for n
      proof -
        let ?m = "real_of_int \<lfloor>2^n * f x\<rfloor>"
        have "\<bar>?m\<bar> \<le> 2^n * 2^N1"
          using N1 apply (simp add: f)
          by (meson floor_mono le_floor_iff less_le_not_le mult_le_cancel_left_pos zero_less_numeral zero_less_power)
        also have "\<dots> \<le> 2 ^ (2*n)"
          by (metis that add_leD1 add_le_cancel_left mult.commute mult_2_right one_less_numeral_iff
                    power_add power_increasing_iff semiring_norm(76))
        finally have m_le: "\<bar>?m\<bar> \<le> 2 ^ (2*n)" .
        have "?m/2^n \<le> f x" "f x < (?m + 1)/2^n"
          by (auto simp: mult.commute pos_divide_le_eq mult_imp_less_div_pos)
        then have eq: "dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k/2^n * ?\<Omega> n k x) (f x)
                     = dist (?m/2^n) (f x)"
          by (subst indicator_sum_eq [of ?m]) (auto simp: m_le)
        have "\<bar>2^n\<bar> * \<bar>?m/2^n - f x\<bar> = \<bar>2^n * (?m/2^n - f x)\<bar>"
          by (simp add: abs_mult)
        also have "\<dots> < 2 ^ N2 * e"
          using N2 by (simp add: divide_simps mult.commute) linarith
        also have "\<dots> \<le> \<bar>2^n\<bar> * e"
          using that \<open>e > 0\<close> by auto
        finally have "dist (?m/2^n) (f x) < e"
          by (simp add: dist_norm)
        then show ?thesis
          using eq by linarith
      qed
      then show "\<exists>no. \<forall>n\<ge>no. dist (\<Sum>k | k \<in> \<int> \<and> \<bar>k\<bar> \<le> 2 ^ (2*n). k * ?\<Omega> n k x/2^n) (f x) < e"
        by force
    qed
  qed
  ultimately show ?rhs
    by metis
next
  assume RHS: ?rhs
  with borel_measurable_simple_function_limit [of f UNIV, unfolded lebesgue_on_UNIV_eq]
  show ?lhs
    by (blast intro: order_trans)
qed

subsection\<open>Borel measurable Jacobian determinant\<close>

lemma lemma_partial_derivatives0:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim0: "((\<lambda>x. f x /\<^sub>R norm x) \<longlongrightarrow> 0) (at 0 within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0. \<forall>e>0. \<exists>x. x \<in> S - {0} \<and> norm x < e \<and> k * norm x \<le> \<bar>v \<bullet> x\<bar>)"
  shows "f x = 0"
proof -
  interpret linear f by fact
  have "dim {x. f x = 0} \<le> DIM('a)"
    by (rule dim_subset_UNIV)
  moreover have False if less: "dim {x. f x = 0} < DIM('a)"
  proof -
    obtain d where "d \<noteq> 0" and d: "\<And>y. f y = 0 \<Longrightarrow> d \<bullet> y = 0"
      using orthogonal_to_subspace_exists [OF less] orthogonal_def
      by (metis (mono_tags, lifting) mem_Collect_eq span_base)
    then obtain k where "k > 0"
      and k: "\<And>e. e > 0 \<Longrightarrow> \<exists>y. y \<in> S - {0} \<and> norm y < e \<and> k * norm y \<le> \<bar>d \<bullet> y\<bar>"
      using lb by blast
    have "\<exists>h. \<forall>n. ((h n \<in> S \<and> h n \<noteq> 0 \<and> k * norm (h n) \<le> \<bar>d \<bullet> h n\<bar>) \<and> norm (h n) < 1 / real (Suc n)) \<and>
               norm (h (Suc n)) < norm (h n)"
    proof (rule dependent_nat_choice)
      show "\<exists>y. (y \<in> S \<and> y \<noteq> 0 \<and> k * norm y \<le> \<bar>d \<bullet> y\<bar>) \<and> norm y < 1 / real (Suc 0)"
        by simp (metis DiffE insertCI k not_less not_one_le_zero)
    qed (use k [of "min (norm x) (1/(Suc n + 1))" for x n] in auto)
    then obtain \<alpha> where \<alpha>: "\<And>n. \<alpha> n \<in> S - {0}" and kd: "\<And>n. k * norm(\<alpha> n) \<le> \<bar>d \<bullet> \<alpha> n\<bar>"
         and norm_lt: "\<And>n. norm(\<alpha> n) < 1/(Suc n)"
      by force
    let ?\<beta> = "\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)"
    have com: "\<And>g. (\<forall>n. g n \<in> sphere (0::'a) 1)
              \<Longrightarrow> \<exists>l \<in> sphere 0 1. \<exists>\<rho>::nat\<Rightarrow>nat. strict_mono \<rho> \<and> (g \<circ> \<rho>) \<longlonglongrightarrow> l"
      using compact_sphere compact_def by metis
    moreover have "\<forall>n. ?\<beta> n \<in> sphere 0 1"
      using \<alpha> by auto
    ultimately obtain l::'a and \<rho>::"nat\<Rightarrow>nat"
       where l: "l \<in> sphere 0 1" and "strict_mono \<rho>" and to_l: "(?\<beta> \<circ> \<rho>) \<longlonglongrightarrow> l"
      by meson
    moreover have "continuous (at l) (\<lambda>x. (\<bar>d \<bullet> x\<bar> - k))"
      by (intro continuous_intros)
    ultimately have lim_dl: "((\<lambda>x. (\<bar>d \<bullet> x\<bar> - k)) \<circ> (?\<beta> \<circ> \<rho>)) \<longlonglongrightarrow> (\<bar>d \<bullet> l\<bar> - k)"
      by (meson continuous_imp_tendsto)
    have "\<forall>\<^sub>F i in sequentially. 0 \<le> ((\<lambda>x. \<bar>d \<bullet> x\<bar> - k) \<circ> ((\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>)) i"
      using \<alpha> kd by (auto simp: field_split_simps)
    then have "k \<le> \<bar>d \<bullet> l\<bar>"
      using tendsto_lowerbound [OF lim_dl, of 0] by auto
    moreover have "d \<bullet> l = 0"
    proof (rule d)
      show "f l = 0"
      proof (rule LIMSEQ_unique [of "f \<circ> ?\<beta> \<circ> \<rho>"])
        have "isCont f l"
          using \<open>linear f\<close> linear_continuous_at linear_conv_bounded_linear by blast
        then show "(f \<circ> (\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>) \<longlonglongrightarrow> f l"
          unfolding comp_assoc
          using to_l continuous_imp_tendsto by blast
        have "\<alpha> \<longlonglongrightarrow> 0"
          using norm_lt LIMSEQ_norm_0 by metis
        with \<open>strict_mono \<rho>\<close> have "(\<alpha> \<circ> \<rho>) \<longlonglongrightarrow> 0"
          by (metis LIMSEQ_subseq_LIMSEQ)
        with lim0 \<alpha> have "((\<lambda>x. f x /\<^sub>R norm x) \<circ> (\<alpha> \<circ> \<rho>)) \<longlonglongrightarrow> 0"
          by (force simp: tendsto_at_iff_sequentially)
        then show "(f \<circ> (\<lambda>n. \<alpha> n /\<^sub>R norm (\<alpha> n)) \<circ> \<rho>) \<longlonglongrightarrow> 0"
          by (simp add: o_def scale)
      qed
    qed
    ultimately show False
      using \<open>k > 0\<close> by auto
  qed
  ultimately have dim: "dim {x. f x = 0} = DIM('a)"
    by force
  then show ?thesis
    using dim_eq_full
    by (metis (mono_tags, lifting) eq_0_on_span eucl.span_Basis linear_axioms linear_eq_stdbasis
        mem_Collect_eq module_hom_zero span_base span_raw_def)
qed

lemma lemma_partial_derivatives:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim: "((\<lambda>x. f (x - a) /\<^sub>R norm (x - a)) \<longlongrightarrow> 0) (at a within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0.  \<forall>e>0. \<exists>x \<in> S - {a}. norm(a - x) < e \<and> k * norm(a - x) \<le> \<bar>v \<bullet> (x - a)\<bar>)"
  shows "f x = 0"
proof -
  have "((\<lambda>x. f x /\<^sub>R norm x) \<longlongrightarrow> 0) (at 0 within (\<lambda>x. x-a) ` S)"
    using lim by (simp add: Lim_within dist_norm)
  then show ?thesis
  proof (rule lemma_partial_derivatives0 [OF \<open>linear f\<close>])
    fix v :: "'a"
    assume v: "v \<noteq> 0"
    show "\<exists>k>0. \<forall>e>0. \<exists>x. x \<in> (\<lambda>x. x - a) ` S - {0} \<and> norm x < e \<and> k * norm x \<le> \<bar>v \<bullet> x\<bar>"
      using lb [OF v] by (force simp:  norm_minus_commute)
  qed
qed


proposition borel_measurable_partial_derivatives:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. (matrix(f' x)$m$n)) \<in> borel_measurable (lebesgue_on S)"
proof -
  have contf: "continuous_on S f"
    using continuous_on_eq_continuous_within f has_derivative_continuous by blast
  have "{x \<in> S.  (matrix (f' x)$m$n) \<le> b} \<in> sets lebesgue" for b
  proof (rule sets_negligible_symdiff)
    let ?T = "{x \<in> S. \<forall>e>0. \<exists>d>0. \<exists>A. A$m$n < b \<and> (\<forall>i j. A$i$j \<in> \<rat>) \<and>
                       (\<forall>y \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A *v (y - x)) \<le> e * norm(y - x))}"
    let ?U = "S \<inter>
              (\<Inter>e \<in> {e \<in> \<rat>. e > 0}.
                \<Union>A \<in> {A. A$m$n < b \<and> (\<forall>i j. A$i$j \<in> \<rat>)}.
                  \<Union>d \<in> {d \<in> \<rat>. 0 < d}.
                     S \<inter> (\<Inter>y \<in> S. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A *v (y - x)) \<le> e * norm(y - x)}))"
    have "?T = ?U"
    proof (intro set_eqI iffI)
      fix x
      assume xT: "x \<in> ?T"
      then show "x \<in> ?U"
      proof (clarsimp simp add:)
        fix q :: real
        assume "q \<in> \<rat>" "q > 0"
        then obtain d A where "d > 0" and A: "A $ m $ n < b" "\<And>i j. A $ i $ j \<in> \<rat>"
          "\<And>y. \<lbrakk>y\<in>S;  norm (y - x) < d\<rbrakk> \<Longrightarrow> norm (f y - f x - A *v (y - x)) \<le> q * norm (y - x)"
          using xT by auto
        then obtain \<delta> where "d > \<delta>" "\<delta> > 0" "\<delta> \<in> \<rat>"
          using Rats_dense_in_real by blast
        with A show "\<exists>A. A $ m $ n < b \<and> (\<forall>i j. A $ i $ j \<in> \<rat>) \<and>
                         (\<exists>s. s \<in> \<rat> \<and> 0 < s \<and> (\<forall>y\<in>S. norm (y - x) < s \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> q * norm (y - x)))"
          by force
      qed
    next
      fix x
      assume xU: "x \<in> ?U"
      then show "x \<in> ?T"
      proof clarsimp
        fix e :: "real"
        assume "e > 0"
        then obtain \<epsilon> where \<epsilon>: "e > \<epsilon>" "\<epsilon> > 0" "\<epsilon> \<in> \<rat>"
          using Rats_dense_in_real by blast
        with xU obtain A r where "x \<in> S" and Ar: "A $ m $ n < b" "\<forall>i j. A $ i $ j \<in> \<rat>" "r \<in> \<rat>" "r > 0"
          and "\<forall>y\<in>S. norm (y - x) < r \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> \<epsilon> * norm (y - x)"
          by (auto simp: split: if_split_asm)
        then have "\<forall>y\<in>S. norm (y - x) < r \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x)"
          by (meson \<open>e > \<epsilon>\<close> less_eq_real_def mult_right_mono norm_ge_zero order_trans)
        then show "\<exists>d>0. \<exists>A. A $ m $ n < b \<and> (\<forall>i j. A $ i $ j \<in> \<rat>) \<and> (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x))"
          using \<open>x \<in> S\<close> Ar by blast
      qed
    qed
    moreover have "?U \<in> sets lebesgue"
    proof -
      have coQ: "countable {e \<in> \<rat>. 0 < e}"
        using countable_Collect countable_rat by blast
      have ne: "{e \<in> \<rat>. (0::real) < e} \<noteq> {}"
        using zero_less_one Rats_1 by blast
      have coA: "countable {A. A $ m $ n < b \<and> (\<forall>i j. A $ i $ j \<in> \<rat>)}"
      proof (rule countable_subset)
        show "countable {A. \<forall>i j. A $ i $ j \<in> \<rat>}"
          using countable_vector [OF countable_vector, of "\<lambda>i j. \<rat>"] by (simp add: countable_rat)
      qed blast
      have *: "\<lbrakk>U \<noteq> {} \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)\<rbrakk>
               \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)" for U
        by fastforce
      have eq: "{x::(real,'m)vec. P x \<and> (Q x \<longrightarrow> R x)} = {x. P x \<and> \<not> Q x} \<union> {x. P x \<and> R x}" for P Q R
        by auto
      have sets: "S \<inter> (\<Inter>y\<in>S. {x \<in> S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x)})
                  \<in> sets lebesgue" for e A d
      proof -
        have clo: "closedin (top_of_set S)
                     {x \<in> S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x)}"
          for y
        proof -
          have cont1: "continuous_on S (\<lambda>x. norm (y - x))"
          and  cont2: "continuous_on S (\<lambda>x. e * norm (y - x) - norm (f y - f x - (A *v y - A *v x)))"
            by (force intro: contf continuous_intros)+
          have clo1: "closedin (top_of_set S) {x \<in> S. d \<le> norm (y - x)}"
            using continuous_closedin_preimage [OF cont1, of "{d..}"] by (simp add: vimage_def Int_def)
          have clo2: "closedin (top_of_set S)
                       {x \<in> S. norm (f y - f x - (A *v y - A *v x)) \<le> e * norm (y - x)}"
            using continuous_closedin_preimage [OF cont2, of "{0..}"] by (simp add: vimage_def Int_def)
          show ?thesis
            by (auto simp: eq not_less matrix_vector_mult_diff_distrib intro: clo1 clo2)
        qed
        show ?thesis
          by (rule lebesgue_closedin [of S]) (force intro: * S clo)+
      qed
      show ?thesis
        by (intro sets sets.Int S sets.countable_UN'' sets.countable_INT'' coQ coA) auto
    qed
    ultimately show "?T \<in> sets lebesgue"
      by simp
    let ?M = "(?T - {x \<in> S. matrix (f' x) $ m $ n \<le> b} \<union> ({x \<in> S. matrix (f' x) $ m $ n \<le> b} - ?T))"
    let ?\<Theta> = "\<lambda>x v. \<forall>\<xi>>0. \<exists>e>0. \<forall>y \<in> S-{x}. norm (x - y) < e \<longrightarrow> \<bar>v \<bullet> (y - x)\<bar> < \<xi> * norm (x - y)"
    have nN: "negligible {x \<in> S. \<exists>v\<noteq>0. ?\<Theta> x v}"
      unfolding negligible_eq_zero_density
    proof clarsimp
      fix x v and r e :: "real"
      assume "x \<in> S" "v \<noteq> 0" "r > 0" "e > 0"
      and Theta [rule_format]: "?\<Theta> x v"
      moreover have "(norm v * e / 2) / CARD('m) ^ CARD('m) > 0"
        by (simp add: \<open>v \<noteq> 0\<close> \<open>e > 0\<close>)
      ultimately obtain d where "d > 0"
         and dless: "\<And>y. \<lbrakk>y \<in> S - {x}; norm (x - y) < d\<rbrakk> \<Longrightarrow>
                        \<bar>v \<bullet> (y - x)\<bar> < ((norm v * e / 2) / CARD('m) ^ CARD('m)) * norm (x - y)"
        by metis
      let ?W = "ball x (min d r) \<inter> {y. \<bar>v \<bullet> (y - x)\<bar> < (norm v * e/2 * min d r) / CARD('m) ^ CARD('m)}"
      have "open {x. \<bar>v \<bullet> (x - a)\<bar> < b}" for a b
        by (intro open_Collect_less continuous_intros)
      show "\<exists>d>0. d \<le> r \<and>
            (\<exists>U. {x' \<in> S. \<exists>v\<noteq>0. ?\<Theta> x' v} \<inter> ball x d \<subseteq> U \<and>
                 U \<in> lmeasurable \<and> measure lebesgue U < e * content (ball x d))"
      proof (intro exI conjI)
        show "0 < min d r" "min d r \<le> r"
          using \<open>r > 0\<close> \<open>d > 0\<close> by auto
        show "{x' \<in> S. \<exists>v. v \<noteq> 0 \<and> (\<forall>\<xi>>0. \<exists>e>0. \<forall>z\<in>S - {x'}. norm (x' - z) < e \<longrightarrow> \<bar>v \<bullet> (z - x')\<bar> < \<xi> * norm (x' - z))} \<inter> ball x (min d r) \<subseteq> ?W"
          proof (clarsimp simp: dist_norm norm_minus_commute)
            fix y w
            assume "y \<in> S" "w \<noteq> 0"
              and less [rule_format]:
                    "\<forall>\<xi>>0. \<exists>e>0. \<forall>z\<in>S - {y}. norm (y - z) < e \<longrightarrow> \<bar>w \<bullet> (z - y)\<bar> < \<xi> * norm (y - z)"
              and d: "norm (y - x) < d" and r: "norm (y - x) < r"
            show "\<bar>v \<bullet> (y - x)\<bar> < norm v * e * min d r / (2 * real CARD('m) ^ CARD('m))"
            proof (cases "y = x")
              case True
              with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> \<open>v \<noteq> 0\<close> show ?thesis
                by simp
            next
              case False
              have "\<bar>v \<bullet> (y - x)\<bar> < norm v * e / 2 / real (CARD('m) ^ CARD('m)) * norm (x - y)"
                apply (rule dless)
                using False \<open>y \<in> S\<close> d by (auto simp: norm_minus_commute)
              also have "\<dots> \<le> norm v * e * min d r / (2 * real CARD('m) ^ CARD('m))"
                using d r \<open>e > 0\<close> by (simp add: field_simps norm_minus_commute mult_left_mono)
              finally show ?thesis .
            qed
          qed
          show "?W \<in> lmeasurable"
            by (simp add: fmeasurable_Int_fmeasurable borel_open)
          obtain k::'m where True
            by metis
          obtain T where T: "orthogonal_transformation T" and v: "v = T(norm v *\<^sub>R axis k (1::real))"
            using rotation_rightward_line by metis
          define b where "b \<equiv> norm v"
          have "b > 0"
            using \<open>v \<noteq> 0\<close> by (auto simp: b_def)
          obtain eqb: "inv T v = b *\<^sub>R axis k (1::real)" and "inj T" "bij T" and invT: "orthogonal_transformation (inv T)"
            by (metis UNIV_I b_def  T v bij_betw_inv_into_left orthogonal_transformation_inj orthogonal_transformation_bij orthogonal_transformation_inv)
          let ?v = "\<chi> i. min d r / CARD('m)"
          let ?v' = "\<chi> i. if i = k then (e/2 * min d r) / CARD('m) ^ CARD('m) else min d r"
          let ?x' = "inv T x"
          let ?W' = "(ball ?x' (min d r) \<inter> {y. \<bar>(y - ?x')$k\<bar> < e * min d r / (2 * CARD('m) ^ CARD('m))})"
          have abs: "x - e \<le> y \<and> y \<le> x + e \<longleftrightarrow> abs(y - x) \<le> e" for x y e::real
            by auto
          have "?W = T ` ?W'"
          proof -
            have 1: "T ` (ball (inv T x) (min d r)) = ball x (min d r)"
              by (simp add: T image_orthogonal_transformation_ball orthogonal_transformation_surj surj_f_inv_f)
            have 2: "{y. \<bar>v \<bullet> (y - x)\<bar> < b * e * min d r / (2 * real CARD('m) ^ CARD('m))} =
                      T ` {y. \<bar>y $ k - ?x' $ k\<bar> < e * min d r / (2 * real CARD('m) ^ CARD('m))}"
            proof -
              have *: "\<bar>T (b *\<^sub>R axis k 1) \<bullet> (y - x)\<bar> = b * \<bar>inv T y $ k - ?x' $ k\<bar>" for y
              proof -
                have "\<bar>T (b *\<^sub>R axis k 1) \<bullet> (y - x)\<bar> = \<bar>(b *\<^sub>R axis k 1) \<bullet> inv T (y - x)\<bar>"
                  by (metis (no_types, hide_lams) b_def eqb invT orthogonal_transformation_def v)
                also have "\<dots> = b * \<bar>(axis k 1) \<bullet> inv T (y - x)\<bar>"
                  using \<open>b > 0\<close> by (simp add: abs_mult)
                also have "\<dots> = b * \<bar>inv T y $ k - ?x' $ k\<bar>"
                  using orthogonal_transformation_linear [OF invT]
                  by (simp add: inner_axis' linear_diff)
                finally show ?thesis
                  by simp
              qed
              show ?thesis
                using v b_def [symmetric]
                using \<open>b > 0\<close> by (simp add: * bij_image_Collect_eq [OF \<open>bij T\<close>] mult_less_cancel_left_pos times_divide_eq_right [symmetric] del: times_divide_eq_right)
            qed
            show ?thesis
              using \<open>b > 0\<close> by (simp add: image_Int \<open>inj T\<close> 1 2 b_def [symmetric])
          qed
          moreover have "?W' \<in> lmeasurable"
            by (auto intro: fmeasurable_Int_fmeasurable)
          ultimately have "measure lebesgue ?W = measure lebesgue ?W'"
            by (metis measure_orthogonal_image T)
          also have "\<dots> \<le> measure lebesgue (cbox (?x' - ?v') (?x' + ?v'))"
          proof (rule measure_mono_fmeasurable)
            show "?W' \<subseteq> cbox (?x' - ?v') (?x' + ?v')"
              apply (clarsimp simp add: mem_box_cart abs dist_norm norm_minus_commute simp del: min_less_iff_conj min.bounded_iff)
              by (metis component_le_norm_cart less_eq_real_def le_less_trans vector_minus_component)
          qed auto
          also have "\<dots> \<le> e/2 * measure lebesgue (cbox (?x' - ?v) (?x' + ?v))"
          proof -
            have "cbox (?x' - ?v) (?x' + ?v) \<noteq> {}"
              using \<open>r > 0\<close> \<open>d > 0\<close> by (auto simp: interval_eq_empty_cart divide_less_0_iff)
            with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> show ?thesis
              apply (simp add: content_cbox_if_cart mem_box_cart)
              apply (auto simp: prod_nonneg)
              apply (simp add: abs if_distrib prod.delta_remove field_simps power_diff split: if_split_asm)
              done
          qed
          also have "\<dots> \<le> e/2 * measure lebesgue (cball ?x' (min d r))"
          proof (rule mult_left_mono [OF measure_mono_fmeasurable])
            have *: "norm (?x' - y) \<le> min d r"
              if y: "\<And>i. \<bar>?x' $ i - y $ i\<bar> \<le> min d r / real CARD('m)" for y
            proof -
              have "norm (?x' - y) \<le> (\<Sum>i\<in>UNIV. \<bar>(?x' - y) $ i\<bar>)"
                by (rule norm_le_l1_cart)
              also have "\<dots> \<le> real CARD('m) * (min d r / real CARD('m))"
                by (rule sum_bounded_above) (use y in auto)
              finally show ?thesis
                by simp
            qed
            show "cbox (?x' - ?v) (?x' + ?v) \<subseteq> cball ?x' (min d r)"
              apply (clarsimp simp only: mem_box_cart dist_norm mem_cball intro!: *)
              by (simp add: abs_diff_le_iff abs_minus_commute)
          qed (use \<open>e > 0\<close> in auto)
          also have "\<dots> < e * content (cball ?x' (min d r))"
            using \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> by (auto intro: content_cball_pos)
          also have "\<dots> = e * content (ball x (min d r))"
            using \<open>r > 0\<close> \<open>d > 0\<close> content_ball_conv_unit_ball[of "min d r" "inv T x"]
                  content_ball_conv_unit_ball[of "min d r" x]
            by (simp add: content_cball_conv_ball)
          finally show "measure lebesgue ?W < e * content (ball x (min d r))" .
      qed
    qed
    have *: "(\<And>x. (x \<notin> S) \<Longrightarrow> (x \<in> T \<longleftrightarrow> x \<in> U)) \<Longrightarrow> (T - U) \<union> (U - T) \<subseteq> S" for S T U :: "(real,'m) vec set"
      by blast
    have MN: "?M \<subseteq> {x \<in> S. \<exists>v\<noteq>0. ?\<Theta> x v}"
    proof (rule *)
      fix x
      assume x: "x \<notin> {x \<in> S. \<exists>v\<noteq>0. ?\<Theta> x v}"
      show "(x \<in> ?T) \<longleftrightarrow> (x \<in> {x \<in> S. matrix (f' x) $ m $ n \<le> b})"
      proof (cases "x \<in> S")
        case True
        then have x: "\<not> ?\<Theta> x v" if "v \<noteq> 0" for v
          using x that by force
        show ?thesis
        proof (rule iffI; clarsimp)
          assume b: "\<forall>e>0. \<exists>d>0. \<exists>A. A $ m $ n < b \<and> (\<forall>i j. A $ i $ j \<in> \<rat>) \<and>
                                    (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x))"
                     (is "\<forall>e>0. \<exists>d>0. \<exists>A. ?\<Phi> e d A")
          then have "\<forall>k. \<exists>d>0. \<exists>A. ?\<Phi> (1 / Suc k) d A"
            by (metis (no_types, hide_lams) less_Suc_eq_0_disj of_nat_0_less_iff zero_less_divide_1_iff)
          then obtain \<delta> A where \<delta>: "\<And>k. \<delta> k > 0"
                           and Ab: "\<And>k. A k $ m $ n < b"
                           and A: "\<And>k y. \<lbrakk>y \<in> S; norm (y - x) < \<delta> k\<rbrakk> \<Longrightarrow>
                                          norm (f y - f x - A k *v (y - x)) \<le> 1/(Suc k) * norm (y - x)"
            by metis
          have "\<forall>i j. \<exists>a. (\<lambda>n. A n $ i $ j) \<longlonglongrightarrow> a"
          proof (intro allI)
            fix i j
            have vax: "(A n *v axis j 1) $ i = A n $ i $ j" for n
              by (metis cart_eq_inner_axis matrix_vector_mul_component)
            let ?CA = "{x. Cauchy (\<lambda>n. (A n) *v x)}"
            have "subspace ?CA"
              unfolding subspace_def convergent_eq_Cauchy [symmetric]
                by (force simp: algebra_simps intro: tendsto_intros)
            then have CA_eq: "?CA = span ?CA"
              by (metis span_eq_iff)
            also have "\<dots> = UNIV"
            proof -
              have "dim ?CA \<le> CARD('m)"
                using dim_subset_UNIV[of ?CA]
                by auto
              moreover have "False" if less: "dim ?CA < CARD('m)"
              proof -
                obtain d where "d \<noteq> 0" and d: "\<And>y. y \<in> span ?CA \<Longrightarrow> orthogonal d y"
                  using less by (force intro: orthogonal_to_subspace_exists [of ?CA])
                with x [OF \<open>d \<noteq> 0\<close>] obtain \<xi> where "\<xi> > 0"
                  and \<xi>: "\<And>e. e > 0 \<Longrightarrow> \<exists>y \<in> S - {x}. norm (x - y) < e \<and> \<xi> * norm (x - y) \<le> \<bar>d \<bullet> (y - x)\<bar>"
                  by (fastforce simp: not_le Bex_def)
                obtain \<gamma> z where \<gamma>Sx: "\<And>i. \<gamma> i \<in> S - {x}"
                           and \<gamma>le:   "\<And>i. \<xi> * norm(\<gamma> i - x) \<le> \<bar>d \<bullet> (\<gamma> i - x)\<bar>"
                           and \<gamma>x:    "\<gamma> \<longlonglongrightarrow> x"
                           and z:     "(\<lambda>n. (\<gamma> n - x) /\<^sub>R norm (\<gamma> n - x)) \<longlonglongrightarrow> z"
                proof -
                  have "\<exists>\<gamma>. (\<forall>i. (\<gamma> i \<in> S - {x} \<and>
                                  \<xi> * norm(\<gamma> i - x) \<le> \<bar>d \<bullet> (\<gamma> i - x)\<bar> \<and> norm(\<gamma> i - x) < 1/Suc i) \<and>
                                 norm(\<gamma>(Suc i) - x) < norm(\<gamma> i - x))"
                  proof (rule dependent_nat_choice)
                    show "\<exists>y. y \<in> S - {x} \<and> \<xi> * norm (y - x) \<le> \<bar>d \<bullet> (y - x)\<bar> \<and> norm (y - x) < 1 / Suc 0"
                      using \<xi> [of 1] by (auto simp: dist_norm norm_minus_commute)
                  next
                    fix y i
                    assume "y \<in> S - {x} \<and> \<xi> * norm (y - x) \<le> \<bar>d \<bullet> (y - x)\<bar> \<and> norm (y - x) < 1/Suc i"
                    then have "min (norm(y - x)) (1/((Suc i) + 1)) > 0"
                      by auto
                    then obtain y' where "y' \<in> S - {x}" and y': "norm (x - y') < min (norm (y - x)) (1/((Suc i) + 1))"
                                         "\<xi> * norm (x - y') \<le> \<bar>d \<bullet> (y' - x)\<bar>"
                      using \<xi> by metis
                    with \<xi> show "\<exists>y'. (y' \<in> S - {x} \<and> \<xi> * norm (y' - x) \<le> \<bar>d \<bullet> (y' - x)\<bar> \<and>
                              norm (y' - x) < 1/(Suc (Suc i))) \<and> norm (y' - x) < norm (y - x)"
                      by (auto simp: dist_norm norm_minus_commute)
                  qed
                  then obtain \<gamma> where
                        \<gamma>Sx: "\<And>i. \<gamma> i \<in> S - {x}"
                        and \<gamma>le: "\<And>i. \<xi> * norm(\<gamma> i - x) \<le> \<bar>d \<bullet> (\<gamma> i - x)\<bar>"
                        and \<gamma>conv: "\<And>i. norm(\<gamma> i - x) < 1/(Suc i)"
                    by blast
                  let ?f = "\<lambda>i. (\<gamma> i - x) /\<^sub>R norm (\<gamma> i - x)"
                  have "?f i \<in> sphere 0 1" for i
                    using \<gamma>Sx by auto
                  then obtain l \<rho> where "l \<in> sphere 0 1" "strict_mono \<rho>" and l: "(?f \<circ> \<rho>) \<longlonglongrightarrow> l"
                    using compact_sphere [of "0::(real,'m) vec" 1]  unfolding compact_def by meson
                  show thesis
                  proof
                    show "(\<gamma> \<circ> \<rho>) i \<in> S - {x}" "\<xi> * norm ((\<gamma> \<circ> \<rho>) i - x) \<le> \<bar>d \<bullet> ((\<gamma> \<circ> \<rho>) i - x)\<bar>" for i
                      using \<gamma>Sx \<gamma>le by auto
                    have "\<gamma> \<longlonglongrightarrow> x"
                    proof (clarsimp simp add: LIMSEQ_def dist_norm)
                      fix r :: "real"
                      assume "r > 0"
                      with real_arch_invD obtain no where "no \<noteq> 0" "real no > 1/r"
                        by (metis divide_less_0_1_iff not_less_iff_gr_or_eq of_nat_0_eq_iff reals_Archimedean2)
                      with \<gamma>conv show "\<exists>no. \<forall>n\<ge>no. norm (\<gamma> n - x) < r"
                        by (metis \<open>r > 0\<close> add.commute divide_inverse inverse_inverse_eq inverse_less_imp_less less_trans mult.left_neutral nat_le_real_less of_nat_Suc)
                    qed
                    with \<open>strict_mono \<rho>\<close> show "(\<gamma> \<circ> \<rho>) \<longlonglongrightarrow> x"
                      by (metis LIMSEQ_subseq_LIMSEQ)
                    show "(\<lambda>n. ((\<gamma> \<circ> \<rho>) n - x) /\<^sub>R norm ((\<gamma> \<circ> \<rho>) n - x)) \<longlonglongrightarrow> l"
                      using l by (auto simp: o_def)
                  qed
                qed
                have "isCont (\<lambda>x. (\<bar>d \<bullet> x\<bar> - \<xi>)) z"
                  by (intro continuous_intros)
                from isCont_tendsto_compose [OF this z]
                have lim: "(\<lambda>y. \<bar>d \<bullet> ((\<gamma> y - x) /\<^sub>R norm (\<gamma> y - x))\<bar> - \<xi>) \<longlonglongrightarrow> \<bar>d \<bullet> z\<bar> - \<xi>"
                  by auto
                moreover have "\<forall>\<^sub>F i in sequentially. 0 \<le> \<bar>d \<bullet> ((\<gamma> i - x) /\<^sub>R norm (\<gamma> i - x))\<bar> - \<xi>"
                proof (rule eventuallyI)
                  fix n
                  show "0 \<le> \<bar>d \<bullet> ((\<gamma> n - x) /\<^sub>R norm (\<gamma> n - x))\<bar> - \<xi>"
                  using \<gamma>le [of n] \<gamma>Sx by (auto simp: abs_mult divide_simps)
                qed
                ultimately have "\<xi> \<le> \<bar>d \<bullet> z\<bar>"
                  using tendsto_lowerbound [where a=0] by fastforce
                have "Cauchy (\<lambda>n. (A n) *v z)"
                proof (clarsimp simp add: Cauchy_def)
                  fix \<epsilon> :: "real"
                  assume "0 < \<epsilon>"
                  then obtain N::nat where "N > 0" and N: "\<epsilon>/2 > 1/N"
                    by (metis half_gt_zero inverse_eq_divide neq0_conv real_arch_inverse)
                  show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (A m *v z) (A n *v z) < \<epsilon>"
                  proof (intro exI allI impI)
                    fix i j
                    assume ij: "N \<le> i" "N \<le> j"
                    let ?V = "\<lambda>i k. A i *v ((\<gamma> k - x) /\<^sub>R norm (\<gamma> k - x))"
                    have "\<forall>\<^sub>F k in sequentially. dist (\<gamma> k) x < min (\<delta> i) (\<delta> j)"
                      using \<gamma>x [unfolded tendsto_iff] by (meson min_less_iff_conj \<delta>)
                    then have even: "\<forall>\<^sub>F k in sequentially. norm (?V i k - ?V j k) - 2 / N \<le> 0"
                    proof (rule eventually_mono, clarsimp)
                      fix p
                      assume p: "dist (\<gamma> p) x < \<delta> i" "dist (\<gamma> p) x < \<delta> j"
                      let ?C = "\<lambda>k. f (\<gamma> p) - f x - A k *v (\<gamma> p - x)"
                      have "norm ((A i - A j) *v (\<gamma> p - x)) = norm (?C j - ?C i)"
                        by (simp add: algebra_simps)
                      also have "\<dots> \<le> norm (?C j) + norm (?C i)"
                        using norm_triangle_ineq4 by blast
                      also have "\<dots> \<le> 1/(Suc j) * norm (\<gamma> p - x) + 1/(Suc i) * norm (\<gamma> p - x)"
                        by (metis A Diff_iff \<gamma>Sx dist_norm p add_mono)
                      also have "\<dots> \<le> 1/N * norm (\<gamma> p - x) + 1/N * norm (\<gamma> p - x)"
                        apply (intro add_mono mult_right_mono)
                        using ij \<open>N > 0\<close> by (auto simp: field_simps)
                      also have "\<dots> = 2 / N * norm (\<gamma> p - x)"
                        by simp
                      finally have no_le: "norm ((A i - A j) *v (\<gamma> p - x)) \<le> 2 / N * norm (\<gamma> p - x)" .
                      have "norm (?V i p - ?V j p) =
                            norm ((A i - A j) *v ((\<gamma> p - x) /\<^sub>R norm (\<gamma> p - x)))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = norm ((A i - A j) *v (\<gamma> p - x)) / norm (\<gamma> p - x)"
                        by (simp add: divide_inverse matrix_vector_mult_scaleR)
                      also have "\<dots> \<le> 2 / N"
                        using no_le by (auto simp: field_split_simps)
                      finally show "norm (?V i p - ?V j p) \<le> 2 / N" .
                    qed
                    have "isCont (\<lambda>w. (norm(A i *v w - A j *v w) - 2 / N)) z"
                      by (intro continuous_intros)
                    from isCont_tendsto_compose [OF this z]
                    have lim: "(\<lambda>w. norm (A i *v ((\<gamma> w - x) /\<^sub>R norm (\<gamma> w - x)) -
                                    A j *v ((\<gamma> w - x) /\<^sub>R norm (\<gamma> w - x))) - 2 / N)
                               \<longlonglongrightarrow> norm (A i *v z - A j *v z) - 2 / N"
                      by auto
                    have "dist (A i *v z) (A j *v z) \<le> 2 / N"
                      using tendsto_upperbound [OF lim even] by (auto simp: dist_norm)
                    with N show "dist (A i *v z) (A j *v z) < \<epsilon>"
                      by linarith
                  qed
                qed
                then have "d \<bullet> z = 0"
                  using CA_eq d orthogonal_def by auto
                then show False
                  using \<open>0 < \<xi>\<close> \<open>\<xi> \<le> \<bar>d \<bullet> z\<bar>\<close> by auto
              qed
              ultimately show ?thesis
                using dim_eq_full by fastforce
            qed
            finally have "?CA = UNIV" .
            then have "Cauchy (\<lambda>n. (A n) *v axis j 1)"
              by auto
            then obtain L where "(\<lambda>n. A n *v axis j 1) \<longlonglongrightarrow> L"
              by (auto simp: Cauchy_convergent_iff convergent_def)
            then have "(\<lambda>x. (A x *v axis j 1) $ i) \<longlonglongrightarrow> L $ i"
              by (rule tendsto_vec_nth)
            then show "\<exists>a. (\<lambda>n. A n $ i $ j) \<longlonglongrightarrow> a"
              by (force simp: vax)
          qed
          then obtain B where B: "\<And>i j. (\<lambda>n. A n $ i $ j) \<longlonglongrightarrow> B $ i $ j"
            by (auto simp: lambda_skolem)
          have lin_df: "linear (f' x)"
               and lim_df: "((\<lambda>y. (1 / norm (y - x)) *\<^sub>R (f y - (f x + f' x (y - x)))) \<longlongrightarrow> 0) (at x within S)"
            using \<open>x \<in> S\<close> assms by (auto simp: has_derivative_within linear_linear)
          moreover
          interpret linear "f' x" by fact
          have "(matrix (f' x) - B) *v w = 0" for w
          proof (rule lemma_partial_derivatives [of "(*v) (matrix (f' x) - B)"])
            show "linear ((*v) (matrix (f' x) - B))"
              by (rule matrix_vector_mul_linear)
            have "((\<lambda>y. ((f x + f' x (y - x)) - f y) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
              using tendsto_minus [OF lim_df] by (simp add: field_split_simps)
            then show "((\<lambda>y. (matrix (f' x) - B) *v (y - x) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
            proof (rule Lim_transform)
              have "((\<lambda>y. ((f y + B *v x - (f x + B *v y)) /\<^sub>R norm (y - x))) \<longlongrightarrow> 0) (at x within S)"
              proof (clarsimp simp add: Lim_within dist_norm)
                fix e :: "real"
                assume "e > 0"
                then obtain q::nat where "q \<noteq> 0" and qe2: "1/q < e/2"
                  by (metis divide_pos_pos inverse_eq_divide real_arch_inverse zero_less_numeral)
                let ?g = "\<lambda>p. sum  (\<lambda>i. sum (\<lambda>j. abs((A p - B)$i$j)) UNIV) UNIV"
                have "(\<lambda>k. onorm (\<lambda>y. (A k - B) *v y)) \<longlonglongrightarrow> 0"
                proof (rule Lim_null_comparison)
                  show "\<forall>\<^sub>F k in sequentially. norm (onorm (\<lambda>y. (A k - B) *v y)) \<le> ?g k"
                  proof (rule eventually_sequentiallyI)
                    fix k :: "nat"
                    assume "0 \<le> k"
                    have "0 \<le> onorm ((*v) (A k - B))"
                      using matrix_vector_mul_bounded_linear
                      by (rule onorm_pos_le)
                    then show "norm (onorm ((*v) (A k - B))) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>(A k - B) $ i $ j\<bar>)"
                      by (simp add: onorm_le_matrix_component_sum del: vector_minus_component)
                  qed
                next
                  show "?g \<longlonglongrightarrow> 0"
                    using B Lim_null tendsto_rabs_zero_iff by (fastforce intro!: tendsto_null_sum)
                qed
                with \<open>e > 0\<close> obtain p where "\<And>n. n \<ge> p \<Longrightarrow> \<bar>onorm ((*v) (A n - B))\<bar> < e/2"
                  unfolding lim_sequentially by (metis diff_zero dist_real_def divide_pos_pos zero_less_numeral)
                then have pqe2: "\<bar>onorm ((*v) (A (p + q) - B))\<bar> < e/2" (*17 [`abs (onorm (\y. A (p + q) ** y - B ** y)) < e / &2`]*)
                  using le_add1 by blast
                show "\<exists>d>0. \<forall>y\<in>S. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow>
                           inverse (norm (y - x)) * norm (f y + B *v x - (f x + B *v y)) < e"
                proof (intro exI, safe)
                  show "0 < \<delta>(p + q)"
                    by (simp add: \<delta>)
                next
                  fix y
                  assume y: "y \<in> S" "norm (y - x) < \<delta>(p + q)" and "y \<noteq> x"
                  have *: "\<lbrakk>norm(b - c) < e - d; norm(y - x - b) \<le> d\<rbrakk> \<Longrightarrow> norm(y - x - c) < e"
                    for b c d e x and y:: "real^'n"
                    using norm_triangle_ineq2 [of "y - x - c" "y - x - b"] by simp
                  have "norm (f y - f x - B *v (y - x)) < e * norm (y - x)"
                  proof (rule *)
                    show "norm (f y - f x - A (p + q) *v (y - x)) \<le> norm (y - x) / (Suc (p + q))"
                      using A [OF y] by simp
                    have "norm (A (p + q) *v (y - x) - B *v (y - x)) \<le> onorm(\<lambda>x. (A(p + q) - B) *v x) * norm(y - x)"
                      by (metis linear_linear matrix_vector_mul_linear matrix_vector_mult_diff_rdistrib onorm)
                    also have "\<dots> < (e/2) * norm (y - x)"
                      using \<open>y \<noteq> x\<close> pqe2 by auto
                    also have "\<dots> \<le> (e - 1 / (Suc (p + q))) * norm (y - x)"
                    proof (rule mult_right_mono)
                      have "1 / Suc (p + q) \<le> 1 / q"
                        using \<open>q \<noteq> 0\<close> by (auto simp: field_split_simps)
                      also have "\<dots> < e/2"
                        using qe2 by auto
                      finally show "e / 2 \<le> e - 1 / real (Suc (p + q))"
                        by linarith
                    qed auto
                    finally show "norm (A (p + q) *v (y - x) - B *v (y - x)) < e * norm (y - x) - norm (y - x) / real (Suc (p + q))"
                      by (simp add: algebra_simps)
                  qed
                  then show "inverse (norm (y - x)) * norm (f y + B *v x - (f x + B *v y)) < e"
                    using \<open>y \<noteq> x\<close> by (simp add: field_split_simps algebra_simps)
                qed
              qed
              then show "((\<lambda>y. (matrix (f' x) - B) *v (y - x) /\<^sub>R
                           norm (y - x) - (f x + f' x (y - x) - f y) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0)
                          (at x within S)"
                by (simp add: algebra_simps diff lin_df scalar_mult_eq_scaleR)
            qed
          qed (use x in \<open>simp; auto simp: not_less\<close>)
          ultimately have "f' x = (*v) B"
            by (force simp: algebra_simps scalar_mult_eq_scaleR)
          show "matrix (f' x) $ m $ n \<le> b"
          proof (rule tendsto_upperbound [of "\<lambda>i. (A i $ m $ n)" _ sequentially])
            show "(\<lambda>i. A i $ m $ n) \<longlonglongrightarrow> matrix (f' x) $ m $ n"
              by (simp add: B \<open>f' x = (*v) B\<close>)
            show "\<forall>\<^sub>F i in sequentially. A i $ m $ n \<le> b"
              by (simp add: Ab less_eq_real_def)
          qed auto
        next
          fix e :: "real"
          assume "x \<in> S" and b: "matrix (f' x) $ m $ n \<le> b" and "e > 0"
          then obtain d where "d>0"
            and d: "\<And>y. y\<in>S \<Longrightarrow> 0 < dist y x \<and> dist y x < d \<longrightarrow> norm (f y - f x - f' x (y - x)) / (norm (y - x))
                  < e/2"
            using f [OF \<open>x \<in> S\<close>]
            by (simp add: Deriv.has_derivative_at_within Lim_within)
              (auto simp add: field_simps dest: spec [of _ "e/2"])
          let ?A = "matrix(f' x) - (\<chi> i j. if i = m \<and> j = n then e / 4 else 0)"
          obtain B where BRats: "\<And>i j. B$i$j \<in> \<rat>" and Bo_e6: "onorm((*v) (?A - B)) < e/6"
            using matrix_rational_approximation \<open>e > 0\<close>
            by (metis zero_less_divide_iff zero_less_numeral)
          show "\<exists>d>0. \<exists>A. A $ m $ n < b \<and> (\<forall>i j. A $ i $ j \<in> \<rat>) \<and>
                (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A *v (y - x)) \<le> e * norm (y - x))"
          proof (intro exI conjI ballI allI impI)
            show "d>0"
              by (rule \<open>d>0\<close>)
            show "B $ m $ n < b"
            proof -
              have "\<bar>matrix ((*v) (?A - B)) $ m $ n\<bar> \<le> onorm ((*v) (?A - B))"
                using component_le_onorm [OF matrix_vector_mul_linear, of _ m n] by metis
              then show ?thesis
                using b Bo_e6 by simp
            qed
            show "B $ i $ j \<in> \<rat>" for i j
              using BRats by auto
            show "norm (f y - f x - B *v (y - x)) \<le> e * norm (y - x)"
              if "y \<in> S" and y: "norm (y - x) < d" for y
            proof (cases "y = x")
              case True then show ?thesis
                by simp
            next
              case False
              have *: "norm(d' - d) \<le> e/2 \<Longrightarrow> norm(y - (x + d')) < e/2 \<Longrightarrow> norm(y - x - d) \<le> e" for d d' e and x y::"real^'n"
                using norm_triangle_le [of "d' - d" "y - (x + d')"] by simp
              show ?thesis
              proof (rule *)
                have split246: "\<lbrakk>norm y \<le> e / 6; norm(x - y) \<le> e / 4\<rbrakk> \<Longrightarrow> norm x \<le> e/2" if "e > 0" for e and x y :: "real^'n"
                  using norm_triangle_le [of y "x-y" "e/2"] \<open>e > 0\<close> by simp
                have "linear (f' x)"
                  using True f has_derivative_linear by blast
                then have "norm (f' x (y - x) - B *v (y - x)) = norm ((matrix (f' x) - B) *v (y - x))"
                  by (simp add: matrix_vector_mult_diff_rdistrib)
                also have "\<dots> \<le> (e * norm (y - x)) / 2"
                proof (rule split246)
                  have "norm ((?A - B) *v (y - x)) / norm (y - x) \<le> onorm(\<lambda>x. (?A - B) *v x)"
                    by (rule le_onorm) auto
                  also have  "\<dots> < e/6"
                    by (rule Bo_e6)
                  finally have "norm ((?A - B) *v (y - x)) / norm (y - x) < e / 6" .
                  then show "norm ((?A - B) *v (y - x)) \<le> e * norm (y - x) / 6"
                    by (simp add: field_split_simps False)
                  have "norm ((matrix (f' x) - B) *v (y - x) - ((?A - B) *v (y - x))) = norm ((\<chi> i j. if i = m \<and> j = n then e / 4 else 0) *v (y - x))"
                    by (simp add: algebra_simps)
                  also have "\<dots> = norm((e/4) *\<^sub>R (y - x)$n *\<^sub>R axis m (1::real))"
                  proof -
                    have "(\<Sum>j\<in>UNIV. (if i = m \<and> j = n then e / 4 else 0) * (y $ j - x $ j)) * 4 = e * (y $ n - x $ n) * axis m 1 $ i" for i
                    proof (cases "i=m")
                      case True then show ?thesis
                        by (auto simp: if_distrib [of "\<lambda>z. z * _"] cong: if_cong)
                    next
                      case False then show ?thesis
                        by (simp add: axis_def)
                    qed
                    then have "(\<chi> i j. if i = m \<and> j = n then e / 4 else 0) *v (y - x) = (e/4) *\<^sub>R (y - x)$n *\<^sub>R axis m (1::real)"
                      by (auto simp: vec_eq_iff matrix_vector_mult_def)
                    then show ?thesis
                      by metis
                  qed
                  also have "\<dots> \<le> e * norm (y - x) / 4"
                    using \<open>e > 0\<close> apply (simp add: norm_mult abs_mult)
                    by (metis component_le_norm_cart vector_minus_component)
                  finally show "norm ((matrix (f' x) - B) *v (y - x) - ((?A - B) *v (y - x))) \<le> e * norm (y - x) / 4" .
                  show "0 < e * norm (y - x)"
                    by (simp add: False \<open>e > 0\<close>)
                qed
                finally show "norm (f' x (y - x) - B *v (y - x)) \<le> (e * norm (y - x)) / 2" .
                show "norm (f y - (f x + f' x (y - x))) < (e * norm (y - x)) / 2"
                  using False d [OF \<open>y \<in> S\<close>] y by (simp add: dist_norm field_simps)
              qed
            qed
          qed
        qed
      qed auto
    qed
    show "negligible ?M"
      using negligible_subset [OF nN MN] .
  qed
  then show ?thesis
    by (simp add: borel_measurable_vimage_halfspace_component_le sets_restrict_space_iff assms)
qed


theorem borel_measurable_det_Jacobian:
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue" and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. det(matrix(f' x))) \<in> borel_measurable (lebesgue_on S)"
  unfolding det_def
  by (intro measurable) (auto intro: f borel_measurable_partial_derivatives [OF S])

text\<open>The localisation wrt S uses the same argument for many similar results.\<close>
(*See HOL Light's MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_BOREL, etc.*)
theorem borel_measurable_lebesgue_on_preimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue)"
proof -
  have "{x. (if x \<in> S then f x else 0) \<in> T} \<in> sets lebesgue \<longleftrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue"
         if "T \<in> sets borel" for T
    proof (cases "0 \<in> T")
      case True
      then have "{x \<in> S. f x \<in> T} = {x. (if x \<in> S then f x else 0) \<in> T} \<inter> S"
                "{x. (if x \<in> S then f x else 0) \<in> T} = {x \<in> S. f x \<in> T} \<union> -S"
        by auto
      then show ?thesis
        by (metis (no_types, lifting) Compl_in_sets_lebesgue assms sets.Int sets.Un)
    next
      case False
      then have "{x. (if x \<in> S then f x else 0) \<in> T} = {x \<in> S. f x \<in> T}"
        by auto
      then show ?thesis
        by auto
    qed
    then show ?thesis
      unfolding borel_measurable_lebesgue_preimage_borel borel_measurable_if [OF assms, symmetric]
      by blast
qed

lemma sets_lebesgue_almost_borel:
  assumes "S \<in> sets lebesgue"
  obtains B N where "B \<in> sets borel" "negligible N" "B \<union> N = S"
proof -
  obtain T N N' where "S = T \<union> N" "N \<subseteq> N'" "N' \<in> null_sets lborel" "T \<in> sets borel"
    using sets_completionE [OF assms] by auto
  then show thesis
    by (metis negligible_iff_null_sets negligible_subset null_sets_completionI that)
qed

lemma double_lebesgue_sets:
 assumes S: "S \<in> sets lebesgue" and T: "T \<in> sets lebesgue" and fim: "f ` S \<subseteq> T"
 shows "(\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue) \<longleftrightarrow>
          f \<in> borel_measurable (lebesgue_on S) \<and>
          (\<forall>U. negligible U \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue)"
         (is "?lhs \<longleftrightarrow> _ \<and> ?rhs")
  unfolding borel_measurable_lebesgue_on_preimage_borel [OF S]
proof (intro iffI allI conjI impI, safe)
  fix V :: "'b set"
  assume *: "\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
    and "V \<in> sets borel"
  then have V: "V \<in> sets lebesgue"
    by simp
  have "{x \<in> S. f x \<in> V} = {x \<in> S. f x \<in> T \<inter> V}"
    using fim by blast
  also have "{x \<in> S. f x \<in> T \<inter> V} \<in> sets lebesgue"
    using T V * le_inf_iff by blast
  finally show "{x \<in> S. f x \<in> V} \<in> sets lebesgue" .
next
  fix U :: "'b set"
  assume "\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
         "negligible U" "U \<subseteq> T"
  then show "{x \<in> S. f x \<in> U} \<in> sets lebesgue"
    using negligible_imp_sets by blast
next
  fix U :: "'b set"
  assume 1 [rule_format]: "(\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue)"
     and 2 [rule_format]: "\<forall>U. negligible U \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue"
     and "U \<in> sets lebesgue" "U \<subseteq> T"
  then obtain C N where C: "C \<in> sets borel \<and> negligible N \<and> C \<union> N = U"
    using sets_lebesgue_almost_borel
    by metis
  then have "{x \<in> S. f x \<in> C} \<in> sets lebesgue"
    by (blast intro: 1)
  moreover have "{x \<in> S. f x \<in> N} \<in> sets lebesgue"
    using C \<open>U \<subseteq> T\<close> by (blast intro: 2)
  moreover have "{x \<in> S. f x \<in> C \<union> N} = {x \<in> S. f x \<in> C} \<union> {x \<in> S. f x \<in> N}"
    by auto
  ultimately show "{x \<in> S. f x \<in> U} \<in> sets lebesgue"
    using C by auto
qed


subsection\<open>Simplest case of Sard's theorem (we don't need continuity of derivative)\<close>

lemma Sard_lemma00:
  fixes P :: "'b::euclidean_space set"
  assumes "a \<ge> 0" and a: "a *\<^sub>R i \<noteq> 0" and i: "i \<in> Basis"
    and P: "P \<subseteq> {x. a *\<^sub>R i \<bullet> x = 0}"
    and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('b) - 1)"
proof -
  have "a > 0"
    using assms by simp
  let ?v = "(\<Sum>j\<in>Basis. (if j = i then e else m) *\<^sub>R j)"
  show thesis
  proof
    have "- e \<le> x \<bullet> i" "x \<bullet> i \<le> e"
      if "t \<in> P" "norm (x - t) \<le> e" for x t
      using \<open>a > 0\<close> that Basis_le_norm [of i "x-t"] P i
      by (auto simp: inner_commute algebra_simps)
    moreover have "- m \<le> x \<bullet> j" "x \<bullet> j \<le> m"
      if "norm x \<le> m" "t \<in> P" "norm (x - t) \<le> e" "j \<in> Basis" and "j \<noteq> i"
      for x t j
      using that Basis_le_norm [of j x] by auto
    ultimately
    show "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> cbox (-?v) ?v"
      by (auto simp: mem_box)
    have *: "\<forall>k\<in>Basis. - ?v \<bullet> k \<le> ?v \<bullet> k"
      using \<open>0 \<le> m\<close> \<open>0 \<le> e\<close> by (auto simp: inner_Basis)
    have 2: "2 ^ DIM('b) = 2 * 2 ^ (DIM('b) - Suc 0)"
      by (metis DIM_positive Suc_pred power_Suc)
    show "measure lebesgue (cbox (-?v) ?v) \<le> 2 * e * (2 * m) ^ (DIM('b) - 1)"
      using \<open>i \<in> Basis\<close>
      by (simp add: content_cbox [OF *] prod.distrib prod.If_cases Diff_eq [symmetric] 2)
  qed blast
qed

text\<open>As above, but reorienting the vector (HOL Light's @text{GEOM\_BASIS\_MULTIPLE\_TAC})\<close>
lemma Sard_lemma0:
  fixes P :: "(real^'n::{finite,wellorder}) set"
  assumes "a \<noteq> 0"
    and P: "P \<subseteq> {x. a \<bullet> x = 0}" and "0 \<le> m" "0 \<le> e"
  obtains S where "S \<in> lmeasurable"
    and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
proof -
  obtain T and k::'n where T: "orthogonal_transformation T" and a: "a = T (norm a *\<^sub>R axis k (1::real))"
    using rotation_rightward_line by metis
  have Tinv [simp]: "T (inv T x) = x" for x
    by (simp add: T orthogonal_transformation_surj surj_f_inv_f)
  obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> T-`P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
  proof (rule Sard_lemma00 [of "norm a" "axis k (1::real)" "T-`P" m e])
    have "norm a *\<^sub>R axis k 1 \<bullet> x = 0" if "T x \<in> P" for x
    proof -
      have "a \<bullet> T x = 0"
        using P that by blast
      then show ?thesis
        by (metis (no_types, lifting) T a orthogonal_orthogonal_transformation orthogonal_def)
    qed
    then show "T -` P \<subseteq> {x. norm a *\<^sub>R axis k 1 \<bullet> x = 0}"
      by auto
  qed (use assms T in auto)
  show thesis
  proof
    show "T ` S \<in> lmeasurable"
      using S measurable_orthogonal_image T by blast
    have "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
    proof clarsimp
      fix x t
      assume "norm x \<le> m" "t \<in> P" "norm (x - t) \<le> e"
      then have "norm (inv T x) \<le> m"
        using orthogonal_transformation_inv [OF T] by (simp add: orthogonal_transformation_norm)
      moreover have "\<exists>t\<in>T -` P. norm (inv T x - t) \<le> e"
      proof
        have "T (inv T x - inv T t) = x - t"
          using T linear_diff orthogonal_transformation_def
          by (metis (no_types, hide_lams) Tinv)
        then have "norm (inv T x - inv T t) = norm (x - t)"
          by (metis T orthogonal_transformation_norm)
        then show "norm (inv T x - inv T t) \<le> e"
          using \<open>norm (x - t) \<le> e\<close> by linarith
       next
         show "inv T t \<in> T -` P"
           using \<open>t \<in> P\<close> by force
      qed
      ultimately show "x \<in> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
        by force
    qed
    then show "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` S"
      using image_mono [OF subS] by (rule order_trans)
    show "measure lebesgue (T ` S) \<le> 2 * e * (2 * m) ^ (CARD('n) - 1)"
      using mS T by (simp add: S measure_orthogonal_image)
  qed
qed

text\<open>As above, but translating the sets (HOL Light's @text{GEN\_GEOM\_ORIGIN\_TAC})\<close>
lemma Sard_lemma1:
  fixes P :: "(real^'n::{finite,wellorder}) set"
   assumes P: "dim P < CARD('n)" and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm(z - w) \<le> m \<and> (\<exists>t \<in> P. norm(z - w - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
proof -
  obtain a where "a \<noteq> 0" "P \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane [of P] P span_base by auto
  then obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
    by (rule Sard_lemma0 [OF _ _ \<open>0 \<le> m\<close> \<open>0 \<le> e\<close>])
  show thesis
  proof
    show "(+)w ` S \<in> lmeasurable"
      by (metis measurable_translation S)
    show "{z. norm (z - w) \<le> m \<and> (\<exists>t\<in>P. norm (z - w - t) \<le> e)} \<subseteq> (+)w ` S"
      using subS by force
    show "measure lebesgue ((+)w ` S) \<le> 2 * e * (2 * m) ^ (CARD('n) - 1)"
      by (metis measure_translation mS)
  qed
qed

lemma Sard_lemma2:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)" (is "?m \<le> ?n")
    and "B > 0" "bounded S"
    and derS: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
    and B: "\<And>x. x \<in> S \<Longrightarrow> onorm(f' x) \<le> B"
  shows "negligible(f ` S)"
proof -
  have lin_f': "\<And>x. x \<in> S \<Longrightarrow> linear(f' x)"
    using derS has_derivative_linear by blast
  show ?thesis
  proof (clarsimp simp add: negligible_outer_le)
    fix e :: "real"
    assume "e > 0"
    obtain c where csub: "S \<subseteq> cbox (- (vec c)) (vec c)" and "c > 0"
    proof -
      obtain b where b: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> b"
        using \<open>bounded S\<close> by (auto simp: bounded_iff)
      show thesis
      proof
        have "- \<bar>b\<bar> - 1 \<le> x $ i \<and> x $ i \<le> \<bar>b\<bar> + 1" if "x \<in> S" for x i
          using component_le_norm_cart [of x i] b [OF that] by auto
        then show "S \<subseteq> cbox (- vec (\<bar>b\<bar> + 1)) (vec (\<bar>b\<bar> + 1))"
          by (auto simp: mem_box_cart)
      qed auto
    qed
    then have box_cc: "box (- (vec c)) (vec c) \<noteq> {}" and cbox_cc: "cbox (- (vec c)) (vec c) \<noteq> {}"
      by (auto simp: interval_eq_empty_cart)
    obtain d where "d > 0" "d \<le> B"
             and d: "(d * 2) * (4 * B) ^ (?n - 1) \<le> e / (2*c) ^ ?m / ?m ^ ?m"
      apply (rule that [of "min B (e / (2*c) ^ ?m / ?m ^ ?m / (4 * B) ^ (?n - 1) / 2)"])
      using \<open>B > 0\<close> \<open>c > 0\<close> \<open>e > 0\<close>
      by (simp_all add: divide_simps min_mult_distrib_right)
    have "\<exists>r. 0 < r \<and> r \<le> 1/2 \<and>
              (x \<in> S
               \<longrightarrow> (\<forall>y. y \<in> S \<and> norm(y - x) < r
                       \<longrightarrow> norm(f y - f x - f' x (y - x)) \<le> d * norm(y - x)))" for x
    proof (cases "x \<in> S")
      case True
      then obtain r where "r > 0"
              and "\<And>y. \<lbrakk>y \<in> S; norm (y - x) < r\<rbrakk>
                       \<Longrightarrow> norm (f y - f x - f' x (y - x)) \<le> d * norm (y - x)"
        using derS \<open>d > 0\<close> by (force simp: has_derivative_within_alt)
      then show ?thesis
        by (rule_tac x="min r (1/2)" in exI) simp
    next
      case False
      then show ?thesis
        by (rule_tac x="1/2" in exI) simp
    qed
    then obtain r where r12: "\<And>x. 0 < r x \<and> r x \<le> 1/2"
            and r: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; norm(y - x) < r x\<rbrakk>
                          \<Longrightarrow> norm(f y - f x - f' x (y - x)) \<le> d * norm(y - x)"
      by metis
    then have ga: "gauge (\<lambda>x. ball x (r x))"
      by (auto simp: gauge_def)
    obtain \<D> where \<D>: "countable \<D>" and sub_cc: "\<Union>\<D> \<subseteq> cbox (- vec c) (vec c)"
      and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>u v. K = cbox u v)"
      and djointish: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
      and covered: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> ball x (r x)"
      and close: "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i::'m. v $ i - u $ i = 2*c / 2^n"
      and covers: "S \<subseteq> \<Union>\<D>"
      apply (rule covering_lemma [OF csub box_cc ga])
      apply (auto simp: Basis_vec_def cart_eq_inner_axis [symmetric])
      done
    let ?\<mu> = "measure lebesgue"
    have "\<exists>T. T \<in> lmeasurable \<and> f ` (K \<inter> S) \<subseteq> T \<and> ?\<mu> T \<le> e / (2*c) ^ ?m * ?\<mu> K"
      if "K \<in> \<D>" for K
    proof -
      obtain u v where uv: "K = cbox u v"
        using cbox \<open>K \<in> \<D>\<close> by blast
      then have uv_ne: "cbox u v \<noteq> {}"
        using cbox that by fastforce
      obtain x where x: "x \<in> S \<inter> cbox u v" "cbox u v \<subseteq> ball x (r x)"
        using \<open>K \<in> \<D>\<close> covered uv by blast
      then have "dim (range (f' x)) < ?n"
        using rank_dim_range [of "matrix (f' x)"] x rank[of x]
        by (auto simp: matrix_works scalar_mult_eq_scaleR lin_f')
      then obtain T where T: "T \<in> lmeasurable"
            and subT: "{z. norm(z - f x) \<le> (2 * B) * norm(v - u) \<and> (\<exists>t \<in> range (f' x). norm(z - f x - t) \<le> d * norm(v - u))} \<subseteq> T"
            and measT: "?\<mu> T \<le> (2 * (d * norm(v - u))) * (2 * ((2 * B) * norm(v - u))) ^ (?n - 1)"
                        (is "_ \<le> ?DVU")
        apply (rule Sard_lemma1 [of "range (f' x)" "(2 * B) * norm(v - u)" "d * norm(v - u)" "f x"])
        using \<open>B > 0\<close> \<open>d > 0\<close> by simp_all
      show ?thesis
      proof (intro exI conjI)
        have "f ` (K \<inter> S) \<subseteq> {z. norm(z - f x) \<le> (2 * B) * norm(v - u) \<and> (\<exists>t \<in> range (f' x). norm(z - f x - t) \<le> d * norm(v - u))}"
          unfolding uv
        proof (clarsimp simp: mult.assoc, intro conjI)
          fix y
          assume y: "y \<in> cbox u v" and "y \<in> S"
          then have "norm (y - x) < r x"
            by (metis dist_norm mem_ball norm_minus_commute subsetCE x(2))
          then have le_dyx: "norm (f y - f x - f' x (y - x)) \<le> d * norm (y - x)"
            using r [of x y] x \<open>y \<in> S\<close> by blast
          have yx_le: "norm (y - x) \<le> norm (v - u)"
          proof (rule norm_le_componentwise_cart)
            show "norm ((y - x) $ i) \<le> norm ((v - u) $ i)" for i
              using x y by (force simp: mem_box_cart dest!: spec [where x=i])
          qed
          have *: "\<lbrakk>norm(y - x - z) \<le> d; norm z \<le> B; d \<le> B\<rbrakk> \<Longrightarrow> norm(y - x) \<le> 2 * B"
            for x y z :: "real^'n::_" and d B
            using norm_triangle_ineq2 [of "y - x" z] by auto
          show "norm (f y - f x) \<le> 2 * (B * norm (v - u))"
          proof (rule * [OF le_dyx])
            have "norm (f' x (y - x)) \<le> onorm (f' x) * norm (y - x)"
              using onorm [of "f' x" "y-x"] by (meson IntE lin_f' linear_linear x(1))
            also have "\<dots> \<le> B * norm (v - u)"
            proof (rule mult_mono)
              show "onorm (f' x) \<le> B"
                using B x by blast
            qed (use \<open>B > 0\<close> yx_le in auto)
            finally show "norm (f' x (y - x)) \<le> B * norm (v - u)" .
            show "d * norm (y - x) \<le> B * norm (v - u)"
              using \<open>B > 0\<close> by (auto intro: mult_mono [OF \<open>d \<le> B\<close> yx_le])
          qed
          show "\<exists>t. norm (f y - f x - f' x t) \<le> d * norm (v - u)"
            apply (rule_tac x="y-x" in exI)
            using \<open>d > 0\<close> yx_le le_dyx mult_left_mono [where c=d]
            by (meson order_trans mult_le_cancel_iff2)
        qed
        with subT show "f ` (K \<inter> S) \<subseteq> T" by blast
        show "?\<mu> T \<le> e / (2*c) ^ ?m * ?\<mu> K"
        proof (rule order_trans [OF measT])
          have "?DVU = (d * 2 * (4 * B) ^ (?n - 1)) * norm (v - u)^?n"
            using \<open>c > 0\<close>
            apply (simp add: algebra_simps)
            by (metis Suc_pred power_Suc zero_less_card_finite)
          also have "\<dots> \<le> (e / (2*c) ^ ?m / (?m ^ ?m)) * norm(v - u) ^ ?n"
            by (rule mult_right_mono [OF d]) auto
          also have "\<dots> \<le> e / (2*c) ^ ?m * ?\<mu> K"
          proof -
            have "u \<in> ball (x) (r x)" "v \<in> ball x (r x)"
              using box_ne_empty(1) contra_subsetD [OF x(2)] mem_box(2) uv_ne by fastforce+
            moreover have "r x \<le> 1/2"
              using r12 by auto
            ultimately have "norm (v - u) \<le> 1"
              using norm_triangle_half_r [of x u 1 v]
              by (metis (no_types, hide_lams) dist_commute dist_norm less_eq_real_def less_le_trans mem_ball)
            then have "norm (v - u) ^ ?n \<le> norm (v - u) ^ ?m"
              by (simp add: power_decreasing [OF mlen])
            also have "\<dots> \<le> ?\<mu> K * real (?m ^ ?m)"
            proof -
              obtain n where n: "\<And>i. v$i - u$i = 2 * c / 2^n"
                using close [of u v] \<open>K \<in> \<D>\<close> uv by blast
              have "norm (v - u) ^ ?m \<le> (\<Sum>i\<in>UNIV. \<bar>(v - u) $ i\<bar>) ^ ?m"
                by (intro norm_le_l1_cart power_mono) auto
              also have "\<dots> \<le> (\<Prod>i\<in>UNIV. v $ i - u $ i) * real CARD('m) ^ CARD('m)"
                by (simp add: n field_simps \<open>c > 0\<close> less_eq_real_def)
              also have "\<dots> = ?\<mu> K * real (?m ^ ?m)"
                by (simp add: uv uv_ne content_cbox_cart)
              finally show ?thesis .
            qed
            finally have *: "1 / real (?m ^ ?m) * norm (v - u) ^ ?n \<le> ?\<mu> K"
              by (simp add: field_split_simps)
            show ?thesis
              using mult_left_mono [OF *, of "e / (2*c) ^ ?m"] \<open>c > 0\<close> \<open>e > 0\<close> by auto
          qed
          finally show "?DVU \<le> e / (2*c) ^ ?m * ?\<mu> K" .
        qed
      qed (use T in auto)
    qed
    then obtain g where meas_g: "\<And>K. K \<in> \<D> \<Longrightarrow> g K \<in> lmeasurable"
                    and sub_g: "\<And>K. K \<in> \<D> \<Longrightarrow> f ` (K \<inter> S) \<subseteq> g K"
                    and le_g: "\<And>K. K \<in> \<D> \<Longrightarrow> ?\<mu> (g K) \<le> e / (2*c)^?m * ?\<mu> K"
      by metis
    have le_e: "?\<mu> (\<Union>i\<in>\<F>. g i) \<le> e"
      if "\<F> \<subseteq> \<D>" "finite \<F>" for \<F>
    proof -
      have "?\<mu> (\<Union>i\<in>\<F>. g i) \<le> (\<Sum>i\<in>\<F>. ?\<mu> (g i))"
        using meas_g \<open>\<F> \<subseteq> \<D>\<close> by (auto intro: measure_UNION_le [OF \<open>finite \<F>\<close>])
      also have "\<dots> \<le> (\<Sum>K\<in>\<F>. e / (2*c) ^ ?m * ?\<mu> K)"
        using \<open>\<F> \<subseteq> \<D>\<close> sum_mono [OF le_g] by (meson le_g subsetCE sum_mono)
      also have "\<dots> = e / (2*c) ^ ?m * (\<Sum>K\<in>\<F>. ?\<mu> K)"
        by (simp add: sum_distrib_left)
      also have "\<dots> \<le> e"
      proof -
        have "\<F> division_of \<Union>\<F>"
        proof (rule division_ofI)
          show "K \<subseteq> \<Union>\<F>"  "K \<noteq> {}" "\<exists>a b. K = cbox a b" if "K \<in> \<F>" for K
            using \<open>K \<in> \<F>\<close> covered cbox \<open>\<F> \<subseteq> \<D>\<close> by (auto simp: Union_upper)
          show "interior K \<inter> interior L = {}" if "K \<in> \<F>" and "L \<in> \<F>" and "K \<noteq> L" for K L
            by (metis (mono_tags, lifting) \<open>\<F> \<subseteq> \<D>\<close> pairwiseD djointish pairwise_subset that)
        qed (use that in auto)
        then have "sum ?\<mu> \<F> \<le> ?\<mu> (\<Union>\<F>)"
          by (simp add: content_division)
        also have "\<dots> \<le> ?\<mu> (cbox (- vec c) (vec c) :: (real, 'm) vec set)"
        proof (rule measure_mono_fmeasurable)
          show "\<Union>\<F> \<subseteq> cbox (- vec c) (vec c)"
            by (meson Sup_subset_mono sub_cc order_trans \<open>\<F> \<subseteq> \<D>\<close>)
        qed (use \<open>\<F> division_of \<Union>\<F>\<close> lmeasurable_division in auto)
        also have "\<dots> = content (cbox (- vec c) (vec c) :: (real, 'm) vec set)"
          by simp
        also have "\<dots> \<le> (2 ^ ?m * c ^ ?m)"
          using \<open>c > 0\<close> by (simp add: content_cbox_if_cart)
        finally have "sum ?\<mu> \<F> \<le> (2 ^ ?m * c ^ ?m)" .
        then show ?thesis
          using \<open>e > 0\<close> \<open>c > 0\<close> by (auto simp: field_split_simps)
      qed
      finally show ?thesis .
    qed
    show "\<exists>T. f ` S \<subseteq> T \<and> T \<in> lmeasurable \<and> ?\<mu> T \<le> e"
    proof (intro exI conjI)
      show "f ` S \<subseteq> \<Union> (g ` \<D>)"
        using covers sub_g by force
      show "\<Union> (g ` \<D>) \<in> lmeasurable"
        by (rule fmeasurable_UN_bound [OF \<open>countable \<D>\<close> meas_g le_e])
      show "?\<mu> (\<Union> (g ` \<D>)) \<le> e"
        by (rule measure_UN_bound [OF \<open>countable \<D>\<close> meas_g le_e])
    qed
  qed
qed


theorem baby_Sard:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
  shows "negligible(f ` S)"
proof -
  let ?U = "\<lambda>n. {x \<in> S. norm(x) \<le> n \<and> onorm(f' x) \<le> real n}"
  have "\<And>x. x \<in> S \<Longrightarrow> \<exists>n. norm x \<le> real n \<and> onorm (f' x) \<le> real n"
    by (meson linear order_trans real_arch_simple)
  then have eq: "S = (\<Union>n. ?U n)"
    by auto
  have "negligible (f ` ?U n)" for n
  proof (rule Sard_lemma2 [OF mlen])
    show "0 < real n + 1"
      by auto
    show "bounded (?U n)"
      using bounded_iff by blast
    show "(f has_derivative f' x) (at x within ?U n)" if "x \<in> ?U n" for x
      using der that by (force intro: has_derivative_subset)
  qed (use rank in auto)
  then show ?thesis
    by (subst eq) (simp add: image_Union negligible_Union_nat)
qed


subsection\<open>A one-way version of change-of-variables not assuming injectivity. \<close>

lemma integral_on_image_ubound_weak:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
      and f: "f \<in> borel_measurable (lebesgue_on (g ` S))"
      and nonneg_fg:  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and det_int_fg: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
      and meas_gim: "\<And>T. \<lbrakk>T \<subseteq> g ` S; T \<in> sets lebesgue\<rbrakk> \<Longrightarrow> {x \<in> S. g x \<in> T} \<in> sets lebesgue"
    shows "f integrable_on (g ` S) \<and>
           integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar>"
  have cont_g: "continuous_on S g"
    using der_g has_derivative_continuous_on by blast
  have [simp]: "space (lebesgue_on S) = S"
    by (simp add: S)
  have gS_in_sets_leb: "g ` S \<in> sets lebesgue"
    apply (rule differentiable_image_in_sets_lebesgue)
    using der_g by (auto simp: S differentiable_def differentiable_on_def)
  obtain h where nonneg_h: "\<And>n x. 0 \<le> h n x"
    and h_le_f: "\<And>n x. x \<in> S \<Longrightarrow> h n (g x) \<le> f (g x)"
    and h_inc: "\<And>n x. h n x \<le> h (Suc n) x"
    and h_meas: "\<And>n. h n \<in> borel_measurable lebesgue"
    and fin_R: "\<And>n. finite(range (h n))"
    and lim: "\<And>x. x \<in> g ` S \<Longrightarrow> (\<lambda>n. h n x) \<longlonglongrightarrow> f x"
  proof -
    let ?f = "\<lambda>x. if x \<in> g ` S then f x else 0"
    have "?f \<in> borel_measurable lebesgue \<and> (\<forall>x. 0 \<le> ?f x)"
      by (auto simp: gS_in_sets_leb f nonneg_fg measurable_restrict_space_iff [symmetric])
    then show ?thesis
      apply (clarsimp simp add: borel_measurable_simple_function_limit_increasing)
      apply (rename_tac h)
      by (rule_tac h=h in that) (auto split: if_split_asm)
  qed
  have h_lmeas: "{t. h n (g t) = y} \<inter> S \<in> sets lebesgue" for y n
  proof -
    have "space (lebesgue_on (UNIV::(real,'n) vec set)) = UNIV"
      by simp
    then have "((h n) -`{y} \<inter> g ` S) \<in> sets (lebesgue_on (g ` S))"
      by (metis Int_commute borel_measurable_vimage h_meas image_eqI inf_top.right_neutral sets_restrict_space space_borel space_completion space_lborel)
    then have "({u. h n u = y} \<inter> g ` S) \<in> sets lebesgue"
      using gS_in_sets_leb
      by (simp add: integral_indicator fmeasurableI2 sets_restrict_space_iff vimage_def)
    then have "{x \<in> S. g x \<in> ({u. h n u = y} \<inter> g ` S)} \<in> sets lebesgue"
      using meas_gim[of "({u. h n u = y} \<inter> g ` S)"] by force
    moreover have "{t. h n (g t) = y} \<inter> S = {x \<in> S. g x \<in> ({u. h n u = y} \<inter> g ` S)}"
      by blast
    ultimately show ?thesis
      by auto
  qed
  have hint: "h n integrable_on g ` S \<and> integral (g ` S) (h n) \<le> integral S (\<lambda>x. ?D x * h n (g x))"
          (is "?INT \<and> ?lhs \<le> ?rhs")  for n
  proof -
    let ?R = "range (h n)"
    have hn_eq: "h n = (\<lambda>x. \<Sum>y\<in>?R. y * indicat_real {x. h n x = y} x)"
      by (simp add: indicator_def if_distrib fin_R cong: if_cong)
    have yind: "(\<lambda>t. y * indicator{x. h n x = y} t) integrable_on (g ` S) \<and>
                (integral (g ` S) (\<lambda>t. y * indicator {x. h n x = y} t))
                 \<le> integral S (\<lambda>t. \<bar>det (matrix (g' t))\<bar> * y * indicator {x. h n x = y} (g t))"
       if y: "y \<in> ?R" for y::real
    proof (cases "y=0")
      case True
      then show ?thesis using gS_in_sets_leb integrable_0 by force
    next
      case False
      with that have "y > 0"
        using less_eq_real_def nonneg_h by fastforce
      have "(\<lambda>x. if x \<in> {t. h n (g t) = y} then ?D x else 0) integrable_on S"
      proof (rule measurable_bounded_by_integrable_imp_integrable)
        have "(\<lambda>x. ?D x) \<in> borel_measurable (lebesgue_on ({t. h n (g t) = y} \<inter> S))"
          apply (intro borel_measurable_abs borel_measurable_det_Jacobian [OF h_lmeas, where f=g])
          by (meson der_g IntD2 has_derivative_subset inf_le2)
        then have "(\<lambda>x. if x \<in> {t. h n (g t) = y} \<inter> S then ?D x else 0) \<in> borel_measurable lebesgue"
          by (rule borel_measurable_if_I [OF _ h_lmeas])
        then show "(\<lambda>x. if x \<in> {t. h n (g t) = y} then ?D x else 0) \<in> borel_measurable (lebesgue_on S)"
          by (simp add: if_if_eq_conj Int_commute borel_measurable_if [OF S, symmetric])
        show "(\<lambda>x. ?D x *\<^sub>R f (g x) /\<^sub>R y) integrable_on S"
          by (rule integrable_cmul) (use det_int_fg in auto)
        show "norm (if x \<in> {t. h n (g t) = y} then ?D x else 0) \<le> ?D x *\<^sub>R f (g x) /\<^sub>R y"
          if "x \<in> S" for x
          using nonneg_h [of n x] \<open>y > 0\<close> nonneg_fg [of x] h_le_f [of x n] that
          by (auto simp: divide_simps mult_left_mono)
      qed (use S in auto)
      then have int_det: "(\<lambda>t. \<bar>det (matrix (g' t))\<bar>) integrable_on ({t. h n (g t) = y} \<inter> S)"
        using integrable_restrict_Int by force
      have "(g ` ({t. h n (g t) = y} \<inter> S)) \<in> lmeasurable"
        apply (rule measurable_differentiable_image [OF h_lmeas])
         apply (blast intro: has_derivative_subset [OF der_g])
        apply (rule int_det)
        done
      moreover have "g ` ({t. h n (g t) = y} \<inter> S) = {x. h n x = y} \<inter> g ` S"
        by blast
      moreover have "measure lebesgue (g ` ({t. h n (g t) = y} \<inter> S))
                     \<le> integral ({t. h n (g t) = y} \<inter> S) (\<lambda>t. \<bar>det (matrix (g' t))\<bar>)"
        apply (rule measure_differentiable_image [OF h_lmeas _ int_det])
        apply (blast intro: has_derivative_subset [OF der_g])
        done
      ultimately show ?thesis
        using \<open>y > 0\<close> integral_restrict_Int [of S "{t. h n (g t) = y}" "\<lambda>t. \<bar>det (matrix (g' t))\<bar> * y"]
        apply (simp add: integrable_on_indicator integral_indicator)
        apply (simp add: indicator_def of_bool_def if_distrib cong: if_cong)
        done
    qed
    have hn_int: "h n integrable_on g ` S"
      apply (subst hn_eq)
      using yind by (force intro: integrable_sum [OF fin_R])
    then show ?thesis
    proof
      have "?lhs = integral (g ` S) (\<lambda>x. \<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} x)"
        by (metis hn_eq)
      also have "\<dots> = (\<Sum>y\<in>range (h n). integral (g ` S) (\<lambda>x. y * indicat_real {x. h n x = y} x))"
        by (rule integral_sum [OF fin_R]) (use yind in blast)
      also have "\<dots> \<le> (\<Sum>y\<in>range (h n). integral S (\<lambda>u. \<bar>det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)))"
        using yind by (force intro: sum_mono)
      also have "\<dots> = integral S (\<lambda>u. \<Sum>y\<in>range (h n). \<bar>det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u))"
      proof (rule integral_sum [OF fin_R, symmetric])
        fix y assume y: "y \<in> ?R"
        with nonneg_h have "y \<ge> 0"
          by auto
        show "(\<lambda>u. \<bar>det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)) integrable_on S"
        proof (rule measurable_bounded_by_integrable_imp_integrable)
          have "(\<lambda>x. indicat_real {x. h n x = y} (g x)) \<in> borel_measurable (lebesgue_on S)"
            using h_lmeas S
            by (auto simp: indicator_vimage [symmetric] borel_measurable_indicator_iff sets_restrict_space_iff)
          then show "(\<lambda>u. \<bar>det (matrix (g' u))\<bar> * y * indicat_real {x. h n x = y} (g u)) \<in> borel_measurable (lebesgue_on S)"
            by (intro borel_measurable_times borel_measurable_abs borel_measurable_const borel_measurable_det_Jacobian [OF S der_g])
        next
          fix x
          assume "x \<in> S"
          have "y * indicat_real {x. h n x = y} (g x) \<le> f (g x)"
            by (metis \<open>x \<in> S\<close> h_le_f indicator_simps(1) indicator_simps(2) mem_Collect_eq mult.commute mult.left_neutral mult_zero_left nonneg_fg)
          with \<open>y \<ge> 0\<close> show "norm (?D x * y * indicat_real {x. h n x = y} (g x)) \<le> ?D x * f(g x)"
            by (simp add: abs_mult mult.assoc mult_left_mono)
        qed (use S det_int_fg in auto)
      qed
      also have "\<dots> = integral S (\<lambda>T. \<bar>det (matrix (g' T))\<bar> *
                                        (\<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} (g T)))"
        by (simp add: sum_distrib_left mult.assoc)
      also have "\<dots> = ?rhs"
        by (metis hn_eq)
      finally show "integral (g ` S) (h n) \<le> ?rhs" .
    qed
  qed
  have le: "integral S (\<lambda>T. \<bar>det (matrix (g' T))\<bar> * h n (g T)) \<le> ?b" for n
  proof (rule integral_le)
    show "(\<lambda>T. \<bar>det (matrix (g' T))\<bar> * h n (g T)) integrable_on S"
    proof (rule measurable_bounded_by_integrable_imp_integrable)
      have "(\<lambda>T. \<bar>det (matrix (g' T))\<bar> *\<^sub>R h n (g T)) \<in> borel_measurable (lebesgue_on S)"
      proof (intro borel_measurable_scaleR borel_measurable_abs borel_measurable_det_Jacobian \<open>S \<in> sets lebesgue\<close>)
        have eq: "{x \<in> S. f x \<le> a} = (\<Union>b \<in> (f ` S) \<inter> atMost a. {x. f x = b} \<inter> S)" for f and a::real
          by auto
        have "finite ((\<lambda>x. h n (g x)) ` S \<inter> {..a})" for a
          by (force intro: finite_subset [OF _ fin_R])
        with h_lmeas [of n] show "(\<lambda>x. h n (g x)) \<in> borel_measurable (lebesgue_on S)"
          apply (simp add: borel_measurable_vimage_halfspace_component_le \<open>S \<in> sets lebesgue\<close> sets_restrict_space_iff eq)
          by (metis (mono_tags) SUP_inf sets.finite_UN)
      qed (use der_g in blast)
      then show "(\<lambda>T. \<bar>det (matrix (g' T))\<bar> * h n (g T)) \<in> borel_measurable (lebesgue_on S)"
        by simp
      show "norm (?D x * h n (g x)) \<le> ?D x *\<^sub>R f (g x)"
        if "x \<in> S" for x
        by (simp add: h_le_f mult_left_mono nonneg_h that)
    qed (use S det_int_fg in auto)
    show "?D x * h n (g x) \<le> ?D x * f (g x)" if "x \<in> S" for x
      by (simp add: \<open>x \<in> S\<close> h_le_f mult_left_mono)
    show "(\<lambda>x. ?D x * f (g x)) integrable_on S"
      using det_int_fg by blast
  qed
  have "f integrable_on g ` S \<and> (\<lambda>k. integral (g ` S) (h k)) \<longlonglongrightarrow> integral (g ` S) f"
  proof (rule monotone_convergence_increasing)
    have "\<bar>integral (g ` S) (h n)\<bar> \<le> integral S (\<lambda>x. ?D x * f (g x))" for n
    proof -
      have "\<bar>integral (g ` S) (h n)\<bar> = integral (g ` S) (h n)"
        using hint by (simp add: integral_nonneg nonneg_h)
      also have "\<dots> \<le> integral S (\<lambda>x. ?D x * f (g x))"
        using hint le by (meson order_trans)
      finally show ?thesis .
    qed
    then show "bounded (range (\<lambda>k. integral (g ` S) (h k)))"
      by (force simp: bounded_iff)
  qed (use h_inc lim hint in auto)
  moreover have "integral (g ` S) (h n) \<le> integral S (\<lambda>x. ?D x * f (g x))" for n
    using hint by (blast intro: le order_trans)
  ultimately show ?thesis
    by (auto intro: Lim_bounded)
qed


lemma integral_on_image_ubound_nonneg:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes nonneg_fg: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "f integrable_on (g ` S) \<and> integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. det (matrix (g' x))"
  define S' where "S' \<equiv> {x \<in> S. ?D x * f(g x) \<noteq> 0}"
  then have der_gS': "\<And>x. x \<in> S' \<Longrightarrow> (g has_derivative g' x) (at x within S')"
    by (metis (mono_tags, lifting) der_g has_derivative_subset mem_Collect_eq subset_iff)
  have "(\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) integrable_on UNIV"
    by (simp add: integrable_restrict_UNIV intS)
  then have Df_borel: "(\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> borel_measurable lebesgue"
    using integrable_imp_measurable lebesgue_on_UNIV_eq by force
  have S': "S' \<in> sets lebesgue"
  proof -
    from Df_borel borel_measurable_vimage_open [of _ UNIV]
    have "{x. (if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> T} \<in> sets lebesgue"
      if "open T" for T
      using that unfolding lebesgue_on_UNIV_eq
      by (fastforce simp add: dest!: spec)
    then have "{x. (if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0) \<in> -{0}} \<in> sets lebesgue"
      using open_Compl by blast
    then show ?thesis
      by (simp add: S'_def conj_ac split: if_split_asm cong: conj_cong)
  qed
  then have gS': "g ` S' \<in> sets lebesgue"
  proof (rule differentiable_image_in_sets_lebesgue)
    show "g differentiable_on S'"
      using der_g unfolding S'_def differentiable_def differentiable_on_def
      by (blast intro: has_derivative_subset)
  qed auto
  have f: "f \<in> borel_measurable (lebesgue_on (g ` S'))"
  proof (clarsimp simp add: borel_measurable_vimage_open)
    fix T :: "real set"
    assume "open T"
    have "{x \<in> g ` S'. f x \<in> T} = g ` {x \<in> S'. f(g x) \<in> T}"
      by blast
    moreover have "g ` {x \<in> S'. f(g x) \<in> T} \<in> sets lebesgue"
    proof (rule differentiable_image_in_sets_lebesgue)
      let ?h = "\<lambda>x. \<bar>?D x\<bar> * f (g x) /\<^sub>R \<bar>?D x\<bar>"
      have "(\<lambda>x. if x \<in> S' then \<bar>?D x\<bar> * f (g x) else 0) = (\<lambda>x. if x \<in> S then \<bar>?D x\<bar> * f (g x) else 0)"
        by (auto simp: S'_def)
      also have "\<dots> \<in> borel_measurable lebesgue"
        by (rule Df_borel)
      finally have *: "(\<lambda>x. \<bar>?D x\<bar> * f (g x)) \<in> borel_measurable (lebesgue_on S')"
        by (simp add: borel_measurable_if_D)
      have "?h \<in> borel_measurable (lebesgue_on S')"
        by (intro * S' der_gS' borel_measurable_det_Jacobian measurable) (blast intro: der_gS')
      moreover have "?h x = f(g x)" if "x \<in> S'" for x
        using that by (auto simp: S'_def)
      ultimately have "(\<lambda>x. f(g x)) \<in> borel_measurable (lebesgue_on S')"
        by (metis (no_types, lifting) measurable_lebesgue_cong)
      then show "{x \<in> S'. f (g x) \<in> T} \<in> sets lebesgue"
        by (simp add: \<open>S' \<in> sets lebesgue\<close> \<open>open T\<close> borel_measurable_vimage_open sets_restrict_space_iff)
      show "g differentiable_on {x \<in> S'. f (g x) \<in> T}"
        using der_g unfolding S'_def differentiable_def differentiable_on_def
        by (blast intro: has_derivative_subset)
    qed auto
    ultimately have "{x \<in> g ` S'. f x \<in> T} \<in> sets lebesgue"
      by metis
    then show "{x \<in> g ` S'. f x \<in> T} \<in> sets (lebesgue_on (g ` S'))"
      by (simp add: \<open>g ` S' \<in> sets lebesgue\<close> sets_restrict_space_iff)
  qed
  have intS': "(\<lambda>x. \<bar>?D x\<bar> * f (g x)) integrable_on S'"
    using intS
    by (rule integrable_spike_set) (auto simp: S'_def intro: empty_imp_negligible)
  have lebS': "{x \<in> S'. g x \<in> T} \<in> sets lebesgue" if "T \<subseteq> g ` S'" "T \<in> sets lebesgue" for T
  proof -
    have "g \<in> borel_measurable (lebesgue_on S')"
      using der_gS' has_derivative_continuous_on S'
      by (blast intro: continuous_imp_measurable_on_sets_lebesgue)
    moreover have "{x \<in> S'. g x \<in> U} \<in> sets lebesgue" if "negligible U" "U \<subseteq> g ` S'" for U
    proof (intro negligible_imp_sets negligible_differentiable_vimage that)
      fix x
      assume x: "x \<in> S'"
      then have "linear (g' x)"
        using der_gS' has_derivative_linear by blast
      with x show "inj (g' x)"
        by (auto simp: S'_def det_nz_iff_inj)
    qed (use der_gS' in auto)
    ultimately show ?thesis
      using double_lebesgue_sets [OF S' gS' order_refl] that by blast
  qed
  have int_gS': "f integrable_on g ` S' \<and> integral (g ` S') f \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
    using integral_on_image_ubound_weak [OF S' f nonneg_fg der_gS' intS' lebS'] S'_def by blast
  have "negligible (g ` {x \<in> S. det(matrix(g' x)) = 0})"
  proof (rule baby_Sard, simp_all)
    fix x
    assume x: "x \<in> S \<and> det (matrix (g' x)) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. det (matrix (g' x)) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    then show "rank (matrix (g' x)) < CARD('n)"
      using det_nz_iff_inj matrix_vector_mul_linear x
      by (fastforce simp add: less_rank_noninjective)
  qed
  then have negg: "negligible (g ` S - g ` {x \<in> S. ?D x \<noteq> 0})"
    by (rule negligible_subset) (auto simp: S'_def)
  have null: "g ` {x \<in> S. ?D x \<noteq> 0} - g ` S = {}"
    by (auto simp: S'_def)
  let ?F = "{x \<in> S. f (g x) \<noteq> 0}"
  have eq: "g ` S' = g ` ?F \<inter> g ` {x \<in> S. ?D x \<noteq> 0}"
    by (auto simp: S'_def image_iff)
  show ?thesis
  proof
    have "((\<lambda>x. if x \<in> g ` ?F then f x else 0) integrable_on g ` {x \<in> S. ?D x \<noteq> 0})"
      using int_gS' eq integrable_restrict_Int [where f=f]
      by simp
    then have "f integrable_on g ` {x \<in> S. ?D x \<noteq> 0}"
      by (auto simp: image_iff elim!: integrable_eq)
    then show "f integrable_on g ` S"
      apply (rule integrable_spike_set [OF _ empty_imp_negligible negligible_subset])
      using negg null by auto
    have "integral (g ` S) f = integral (g ` {x \<in> S. ?D x \<noteq> 0}) f"
      using negg by (auto intro: negligible_subset integral_spike_set)
    also have "\<dots> = integral (g ` {x \<in> S. ?D x \<noteq> 0}) (\<lambda>x. if x \<in> g ` ?F then f x else 0)"
      by (auto simp: image_iff intro!: integral_cong)
    also have "\<dots> = integral (g ` S') f"
      using  eq integral_restrict_Int by simp
    also have "\<dots> \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
      by (metis int_gS')
    also have "\<dots> \<le> ?b"
      by (rule integral_subset_le [OF _ intS' intS]) (use nonneg_fg S'_def in auto)
    finally show "integral (g ` S) f \<le> ?b" .
  qed
qed


lemma absolutely_integrable_on_image_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof -
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f (g x)"
  let ?N = "{x \<in> S. f (g x) < 0}" and ?P = "{x \<in> S. f (g x) > 0}"
  have eq: "{x. (if x \<in> S then ?D x else 0) > 0} = {x \<in> S. ?D x > 0}"
           "{x. (if x \<in> S then ?D x else 0) < 0} = {x \<in> S. ?D x < 0}"
    by auto
  have "?D integrable_on S"
    using intS absolutely_integrable_on_def by blast
  then have "(\<lambda>x. if x \<in> S then ?D x else 0) integrable_on UNIV"
    by (simp add: integrable_restrict_UNIV)
  then have D_borel: "(\<lambda>x. if x \<in> S then ?D x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
    using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
  then have Dlt: "{x \<in> S. ?D x < 0} \<in> sets lebesgue"
    unfolding borel_measurable_vimage_halfspace_component_lt
    by (drule_tac x=0 in spec) (auto simp: eq)
  from D_borel have Dgt: "{x \<in> S. ?D x > 0} \<in> sets lebesgue"
    unfolding borel_measurable_vimage_halfspace_component_gt
    by (drule_tac x=0 in spec) (auto simp: eq)

  have dfgbm: "?D \<in> borel_measurable (lebesgue_on S)"
    using intS absolutely_integrable_on_def integrable_imp_measurable by blast
  have der_gN: "(g has_derivative g' x) (at x within ?N)" if "x \<in> ?N" for x
      using der_g has_derivative_subset that by force
  have "(\<lambda>x. - f x) integrable_on g ` ?N \<and>
         integral (g ` ?N) (\<lambda>x. - f x) \<le> integral ?N (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * - f (g x))"
  proof (rule integral_on_image_ubound_nonneg [OF _ der_gN])
    have 1: "?D integrable_on {x \<in> S. ?D x < 0}"
      using Dlt
      by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
    have "uminus \<circ> (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: o_def mult_less_0_iff empty_imp_negligible integrable_spike_set [OF 1])
    then show "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: integrable_neg_iff o_def)
  qed auto
  then have "f integrable_on g ` ?N"
    by (simp add: integrable_neg_iff)
  moreover have "g ` ?N = {y \<in> g ` S. f y < 0}"
    by auto
  ultimately have "f integrable_on {y \<in> g ` S. f y < 0}"
    by simp
  then have N: "f absolutely_integrable_on {y \<in> g ` S. f y < 0}"
    by (rule absolutely_integrable_absolutely_integrable_ubound) auto

  have der_gP: "(g has_derivative g' x) (at x within ?P)" if "x \<in> ?P" for x
      using der_g has_derivative_subset that by force
  have "f integrable_on g ` ?P \<and> integral (g ` ?P) f \<le> integral ?P ?D"
  proof (rule integral_on_image_ubound_nonneg [OF _ der_gP])
    have "?D integrable_on {x \<in> S. 0 < ?D x}"
      using Dgt
      by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
    then show "?D integrable_on ?P"
      apply (rule integrable_spike_set)
      by (auto simp: zero_less_mult_iff empty_imp_negligible)
  qed auto
  then have "f integrable_on g ` ?P"
    by metis
  moreover have "g ` ?P = {y \<in> g ` S. f y > 0}"
    by auto
  ultimately have "f integrable_on {y \<in> g ` S. f y > 0}"
    by simp
  then have P: "f absolutely_integrable_on {y \<in> g ` S. f y > 0}"
    by (rule absolutely_integrable_absolutely_integrable_lbound) auto
  have "(\<lambda>x. if x \<in> g ` S \<and> f x < 0 \<or> x \<in> g ` S \<and> 0 < f x then f x else 0) = (\<lambda>x. if x \<in> g ` S then f x else 0)"
    by auto
  then show ?thesis
    using absolutely_integrable_Un [OF N P] absolutely_integrable_restrict_UNIV [symmetric, where f=f]
    by simp
qed


proposition absolutely_integrable_on_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
  apply (rule absolutely_integrable_componentwise [OF absolutely_integrable_on_image_real [OF der_g]])
  using absolutely_integrable_component [OF intS]  by auto

proposition integral_on_image_ubound:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes"\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
  using integral_on_image_ubound_nonneg [OF assms] by simp


subsection\<open>Change-of-variables theorem\<close>

text\<open>The classic change-of-variables theorem. We have two versions with quite general hypotheses,
the first that the transforming function has a continuous inverse, the second that the base set is
Lebesgue measurable.\<close>
lemma cov_invertible_nonneg_le:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and f0: "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "f integrable_on T \<and> (integral T f) \<le> b \<longleftrightarrow>
             (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) \<le> b"
        (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  have gS: "g differentiable_on S"
    by (meson der_g differentiable_def differentiable_on_def)
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f (g x)"
  show ?thesis
  proof
    assume ?lhs
    then have fT: "f integrable_on T" and intf: "integral T f \<le> b"
      by blast+
    show ?rhs
    proof
      let ?fgh = "\<lambda>x. \<bar>det (matrix (h' x))\<bar> * (\<bar>det (matrix (g' (h x)))\<bar> * f (g (h x)))"
      have ddf: "?fgh x = f x"
        if "x \<in> T" for x
      proof -
        have "matrix (h' x) ** matrix (g' (h x)) = mat 1"
          using that id[OF that] der_g[of "h x"] gh[OF that] left_inverse_linear has_derivative_linear
          by (subst matrix_compose[symmetric]) (force simp: matrix_id_mat_1 has_derivative_linear)+
        then have "\<bar>det (matrix (h' x))\<bar> * \<bar>det (matrix (g' (h x)))\<bar> = 1"
          by (metis abs_1 abs_mult det_I det_mul)
        then show ?thesis
          by (simp add: gh that)
      qed
      have "?D integrable_on (h ` T)"
      proof (intro set_lebesgue_integral_eq_integral absolutely_integrable_on_image_real)
        show "(\<lambda>x. ?fgh x) absolutely_integrable_on T"
        proof (subst absolutely_integrable_on_iff_nonneg)
          show "(\<lambda>x. ?fgh x) integrable_on T"
            using ddf fT integrable_eq by force
        qed (simp add: zero_le_mult_iff f0 gh)
      qed (use der_h in auto)
      with Seq show "(\<lambda>x. ?D x) integrable_on S"
        by simp
      have "integral S (\<lambda>x. ?D x) \<le> integral T (\<lambda>x. ?fgh x)"
        unfolding Seq
      proof (rule integral_on_image_ubound)
        show "(\<lambda>x. ?fgh x) integrable_on T"
        using ddf fT integrable_eq by force
      qed (use f0 gh der_h in auto)
      also have "\<dots> = integral T f"
        by (force simp: ddf intro: integral_cong)
      also have "\<dots> \<le> b"
        by (rule intf)
      finally show "integral S (\<lambda>x. ?D x) \<le> b" .
    qed
  next
    assume R: ?rhs
    then have "f integrable_on g ` S"
      using der_g f0 hg integral_on_image_ubound_nonneg by blast
    moreover have "integral (g ` S) f \<le> integral S (\<lambda>x. ?D x)"
      by (rule integral_on_image_ubound [OF f0 der_g]) (use R Teq in auto)
    ultimately show ?lhs
      using R by (simp add: Teq)
  qed
qed


lemma cov_invertible_nonneg_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
      and "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) has_integral b) S \<longleftrightarrow> (f has_integral b) T"
  using cov_invertible_nonneg_le [OF assms]
  by (simp add: has_integral_iff) (meson eq_iff)


lemma cov_invertible_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on T \<and> integral T f = b"
         (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  let ?DP = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)" and ?DN = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> * -f(g x)"
  have "+": "(?DP has_integral b) {x \<in> S. f (g x) > 0} \<longleftrightarrow> (f has_integral b) {y \<in> T. f y > 0}" for b
  proof (rule cov_invertible_nonneg_eq)
    have *: "(\<lambda>x. f (g x)) -` Y \<inter> {x \<in> S. f (g x) > 0}
          = ((\<lambda>x. f (g x)) -` Y \<inter> S) \<inter> {x \<in> S. f (g x) > 0}" for Y
      by auto
    show "(g has_derivative g' x) (at x within {x \<in> S. f (g x) > 0})" if "x \<in> {x \<in> S. f (g x) > 0}" for x
      using that der_g has_derivative_subset by fastforce
    show "(h has_derivative h' y) (at y within {y \<in> T. f y > 0})" if "y \<in> {y \<in> T. f y > 0}" for y
      using that der_h has_derivative_subset by fastforce
  qed (use gh hg id in auto)
  have "-": "(?DN has_integral b) {x \<in> S. f (g x) < 0} \<longleftrightarrow> ((\<lambda>x. - f x) has_integral b) {y \<in> T. f y < 0}" for b
  proof (rule cov_invertible_nonneg_eq)
    have *: "(\<lambda>x. - f (g x)) -` y \<inter> {x \<in> S. f (g x) < 0}
          = ((\<lambda>x. f (g x)) -` uminus ` y \<inter> S) \<inter> {x \<in> S. f (g x) < 0}" for y
      using image_iff by fastforce
    show "(g has_derivative g' x) (at x within {x \<in> S. f (g x) < 0})" if "x \<in> {x \<in> S. f (g x) < 0}" for x
      using that der_g has_derivative_subset by fastforce
    show "(h has_derivative h' y) (at y within {y \<in> T. f y < 0})" if "y \<in> {y \<in> T. f y < 0}" for y
      using that der_h has_derivative_subset by fastforce
  qed (use gh hg id in auto)
  show ?thesis
  proof
    assume LHS: ?lhs
    have eq: "{x. (if x \<in> S then ?DP x else 0) > 0} = {x \<in> S. ?DP x > 0}"
      "{x. (if x \<in> S then ?DP x else 0) < 0} = {x \<in> S. ?DP x < 0}"
      by auto
    have "?DP integrable_on S"
      using LHS absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> S then ?DP x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have D_borel: "(\<lambda>x. if x \<in> S then ?DP x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
    then have SN: "{x \<in> S. ?DP x < 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_lt
      by (drule_tac x=0 in spec) (auto simp: eq)
    from D_borel have SP: "{x \<in> S. ?DP x > 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_gt
      by (drule_tac x=0 in spec) (auto simp: eq)
    have "?DP absolutely_integrable_on {x \<in> S. ?DP x > 0}"
      using LHS by (fast intro!: set_integrable_subset [OF _, of _ S] SP)
    then have aP: "?DP absolutely_integrable_on {x \<in> S. f (g x) > 0}"
      by (rule absolutely_integrable_spike_set) (auto simp: zero_less_mult_iff empty_imp_negligible)
    have "?DP absolutely_integrable_on {x \<in> S. ?DP x < 0}"
      using LHS by (fast intro!: set_integrable_subset [OF _, of _ S] SN)
    then have aN: "?DP absolutely_integrable_on {x \<in> S. f (g x) < 0}"
      by (rule absolutely_integrable_spike_set) (auto simp: mult_less_0_iff empty_imp_negligible)
    have fN: "f integrable_on {y \<in> T. f y < 0}"
             "integral {y \<in> T. f y < 0} f = integral {x \<in> S. f (g x) < 0} ?DP"
      using "-" [of "integral {x \<in> S. f(g x) < 0} ?DN"] aN
      by (auto simp: set_lebesgue_integral_eq_integral has_integral_iff integrable_neg_iff)
    have faN: "f absolutely_integrable_on {y \<in> T. f y < 0}"
      apply (rule absolutely_integrable_integrable_bound [where g = "\<lambda>x. - f x"])
      using fN by (auto simp: integrable_neg_iff)
    have fP: "f integrable_on {y \<in> T. f y > 0}"
             "integral {y \<in> T. f y > 0} f = integral {x \<in> S. f (g x) > 0} ?DP"
      using "+" [of "integral {x \<in> S. f(g x) > 0} ?DP"] aP
      by (auto simp: set_lebesgue_integral_eq_integral has_integral_iff integrable_neg_iff)
    have faP: "f absolutely_integrable_on {y \<in> T. f y > 0}"
      apply (rule absolutely_integrable_integrable_bound [where g = f])
      using fP by auto
    have fa: "f absolutely_integrable_on ({y \<in> T. f y < 0} \<union> {y \<in> T. f y > 0})"
      by (rule absolutely_integrable_Un [OF faN faP])
    show ?rhs
    proof
      have eq: "((if x \<in> T \<and> f x < 0 \<or> x \<in> T \<and> 0 < f x then 1 else 0) * f x)
              = (if x \<in> T then 1 else 0) * f x" for x
        by auto
      show "f absolutely_integrable_on T"
        using fa by (simp add: indicator_def of_bool_def set_integrable_def eq)
      have [simp]: "{y \<in> T. f y < 0} \<inter> {y \<in> T. 0 < f y} = {}" for T and f :: "(real^'n::_) \<Rightarrow> real"
        by auto
      have "integral T f = integral ({y \<in> T. f y < 0} \<union> {y \<in> T. f y > 0}) f"
        by (intro empty_imp_negligible integral_spike_set) (auto simp: eq)
      also have "\<dots> = integral {y \<in> T. f y < 0} f + integral {y \<in> T. f y > 0} f"
        using fN fP by simp
      also have "\<dots> = integral {x \<in> S. f (g x) < 0} ?DP + integral {x \<in> S. 0 < f (g x)} ?DP"
        by (simp add: fN fP)
      also have "\<dots> = integral ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. 0 < f (g x)}) ?DP"
        using aP aN by (simp add: set_lebesgue_integral_eq_integral)
      also have "\<dots> = integral S ?DP"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = b"
        using LHS by simp
      finally show "integral T f = b" .
    qed
  next
    assume RHS: ?rhs
    have eq: "{x. (if x \<in> T then f x else 0) > 0} = {x \<in> T. f x > 0}"
             "{x. (if x \<in> T then f x else 0) < 0} = {x \<in> T. f x < 0}"
      by auto
    have "f integrable_on T"
      using RHS absolutely_integrable_on_def by blast
    then have "(\<lambda>x. if x \<in> T then f x else 0) integrable_on UNIV"
      by (simp add: integrable_restrict_UNIV)
    then have D_borel: "(\<lambda>x. if x \<in> T then f x else 0) \<in> borel_measurable (lebesgue_on UNIV)"
      using integrable_imp_measurable lebesgue_on_UNIV_eq by blast
    then have TN: "{x \<in> T. f x < 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_lt
      by (drule_tac x=0 in spec) (auto simp: eq)
    from D_borel have TP: "{x \<in> T. f x > 0} \<in> sets lebesgue"
      unfolding borel_measurable_vimage_halfspace_component_gt
      by (drule_tac x=0 in spec) (auto simp: eq)
    have aint: "f absolutely_integrable_on {y. y \<in> T \<and> 0 < (f y)}"
               "f absolutely_integrable_on {y. y \<in> T \<and> (f y) < 0}"
         and intT: "integral T f = b"
      using set_integrable_subset [of _ T] TP TN RHS
      by blast+
    show ?lhs
    proof
      have fN: "f integrable_on {v \<in> T. f v < 0}"
        using absolutely_integrable_on_def aint by blast
      then have DN: "(?DN has_integral integral {y \<in> T. f y < 0} (\<lambda>x. - f x)) {x \<in> S. f (g x) < 0}"
        using "-" [of "integral {y \<in> T. f y < 0} (\<lambda>x. - f x)"]
        by (simp add: has_integral_neg_iff integrable_integral)
      have aDN: "?DP absolutely_integrable_on {x \<in> S. f (g x) < 0}"
        apply (rule absolutely_integrable_integrable_bound [where g = ?DN])
        using DN hg by (fastforce simp: abs_mult integrable_neg_iff)+
      have fP: "f integrable_on {v \<in> T. f v > 0}"
        using absolutely_integrable_on_def aint by blast
      then have DP: "(?DP has_integral integral {y \<in> T. f y > 0} f) {x \<in> S. f (g x) > 0}"
        using "+" [of "integral {y \<in> T. f y > 0} f"]
        by (simp add: has_integral_neg_iff integrable_integral)
      have aDP: "?DP absolutely_integrable_on {x \<in> S. f (g x) > 0}"
        apply (rule absolutely_integrable_integrable_bound [where g = ?DP])
        using DP hg by (fastforce simp: integrable_neg_iff)+
      have eq: "(if x \<in> S then 1 else 0) * ?DP x = (if x \<in> S \<and> f (g x) < 0 \<or> x \<in> S \<and> f (g x) > 0 then 1 else 0) * ?DP x" for x
        by force
      have "?DP absolutely_integrable_on ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. f (g x) > 0})"
        by (rule absolutely_integrable_Un [OF aDN aDP])
      then show I: "?DP absolutely_integrable_on S"
        by (simp add: indicator_def of_bool_def eq set_integrable_def)
      have [simp]: "{y \<in> S. f y < 0} \<inter> {y \<in> S. 0 < f y} = {}" for S and f :: "(real^'n::_) \<Rightarrow> real"
        by auto
      have "integral S ?DP = integral ({x \<in> S. f (g x) < 0} \<union> {x \<in> S. f (g x) > 0}) ?DP"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = integral {x \<in> S. f (g x) < 0} ?DP + integral {x \<in> S. 0 < f (g x)} ?DP"
        using aDN aDP by (simp add: set_lebesgue_integral_eq_integral)
      also have "\<dots> = - integral {y \<in> T. f y < 0} (\<lambda>x. - f x) + integral {y \<in> T. f y > 0} f"
        using DN DP by (auto simp: has_integral_iff)
      also have "\<dots> = integral ({x \<in> T. f x < 0} \<union> {x \<in> T. 0 < f x}) f"
        by (simp add: fN fP)
      also have "\<dots> = integral T f"
        by (intro empty_imp_negligible integral_spike_set) auto
      also have "\<dots> = b"
        using intT by simp
      finally show "integral S ?DP = b" .
    qed
  qed
qed


lemma cv_inv_version3:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on T \<and> integral T f = b"
proof -
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x) $ i) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * (f(g x) $ i)) = b $ i) \<longleftrightarrow>
        ((\<lambda>x. f x $ i) absolutely_integrable_on T \<and> integral T (\<lambda>x. f x $ i) = b $ i)" for i
    by (rule cov_invertible_real [OF der_g der_h hg gh id])
  then have "?D absolutely_integrable_on S \<and> (?D has_integral b) S \<longleftrightarrow>
        f absolutely_integrable_on T \<and> (f has_integral b) T"
    unfolding absolutely_integrable_componentwise_iff [where f=f] has_integral_componentwise_iff [of f]
              absolutely_integrable_componentwise_iff [where f="?D"] has_integral_componentwise_iff [of ?D]
    by (auto simp: all_conj_distrib Basis_vec_def cart_eq_inner_axis [symmetric]
           has_integral_iff set_lebesgue_integral_eq_integral)
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed


lemma cv_inv_version4:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and> invertible(matrix(g' x))"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> continuous_on (g ` S) h \<and> h(g x) = x"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "\<forall>x. \<exists>h'. x \<in> S
           \<longrightarrow> (g has_derivative g' x) (at x within S) \<and> linear h' \<and> g' x \<circ> h' = id \<and> h' \<circ> g' x = id"
    using der_g matrix_invertible has_derivative_linear by blast
  then obtain h' where h':
    "\<And>x. x \<in> S
           \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and>
               linear (h' x) \<and> g' x \<circ> (h' x) = id \<and> (h' x) \<circ> g' x = id"
    by metis
  show ?thesis
  proof (rule cv_inv_version3)
    show "\<And>y. y \<in> g ` S \<Longrightarrow> (h has_derivative h' (h y)) (at y within g ` S)"
      using h' hg
      by (force simp: continuous_on_eq_continuous_within intro!: has_derivative_inverse_within)
  qed (use h' hg in auto)
qed


theorem has_absolute_integral_change_of_variables_invertible:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
      and conth: "continuous_on (g ` S) h"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    (is "?lhs = ?rhs")
proof -
  let ?S = "{x \<in> S. invertible (matrix (g' x))}" and ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)"
  have *: "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
           \<longleftrightarrow> f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b"
  proof (rule cv_inv_version4)
    show "(g has_derivative g' x) (at x within ?S) \<and> invertible (matrix (g' x))"
      if "x \<in> ?S" for x
      using der_g that has_derivative_subset that by fastforce
    show "continuous_on (g ` ?S) h \<and> h (g x) = x"
      if "x \<in> ?S" for x
      using that continuous_on_subset [OF conth]  by (simp add: hg image_mono)
  qed
  have "(g has_derivative g' x) (at x within {x \<in> S. rank (matrix (g' x)) < CARD('m)})" if "x \<in> S" for x
    by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI that)
  then have "negligible (g ` {x \<in> S. \<not> invertible (matrix (g' x))})"
    by (auto simp: invertible_det_nz det_eq_0_rank intro: baby_Sard)
  then have neg: "negligible {x \<in> g ` S. x \<notin> g ` ?S \<and> f x \<noteq> 0}"
    by (auto intro: negligible_subset)
  have [simp]: "{x \<in> g ` ?S. x \<notin> g ` S \<and> f x \<noteq> 0} = {}"
    by auto
  have "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
    apply (intro conj_cong absolutely_integrable_spike_set_eq)
      apply(auto simp: integral_spike_set invertible_det_nz empty_imp_negligible neg)
    done
  moreover
  have "f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    by (auto intro!: conj_cong absolutely_integrable_spike_set_eq integral_spike_set neg)
  ultimately
  show ?thesis
    using "*" by blast
qed



theorem has_absolute_integral_change_of_variables_compact:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "compact S"
      and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and inj: "inj_on g S"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b)"
proof -
  obtain h where hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
    using inj by (metis the_inv_into_f_f)
  have conth: "continuous_on (g ` S) h"
    by (metis \<open>compact S\<close> continuous_on_inv der_g has_derivative_continuous_on hg)
  show ?thesis
    by (rule has_absolute_integral_change_of_variables_invertible [OF der_g hg conth])
qed


lemma has_absolute_integral_change_of_variables_compact_family:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes compact: "\<And>n::nat. compact (F n)"
      and der_g: "\<And>x. x \<in> (\<Union>n. F n) \<Longrightarrow> (g has_derivative g' x) (at x within (\<Union>n. F n))"
      and inj: "inj_on g (\<Union>n. F n)"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on (\<Union>n. F n) \<and>
             integral (\<Union>n. F n) (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` (\<Union>n. F n)) \<and> integral (g ` (\<Union>n. F n)) f = b)"
proof -
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f (g x)"
  let ?U = "\<lambda>n. \<Union>m\<le>n. F m"
  let ?lift = "vec::real\<Rightarrow>real^1"
  have F_leb: "F m \<in> sets lebesgue" for m
    by (simp add: compact borel_compact)
  have iff: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f (g x)) absolutely_integrable_on (?U n) \<and>
             integral (?U n) (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f (g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` (?U n)) \<and> integral (g ` (?U n)) f = b" for n b and f :: "real^'m::_ \<Rightarrow> real^'k"
  proof (rule has_absolute_integral_change_of_variables_compact)
    show "compact (?U n)"
      by (simp add: compact compact_UN)
    show "(g has_derivative g' x) (at x within (?U n))"
      if "x \<in> ?U n" for x
      using that by (blast intro!: has_derivative_subset [OF der_g])
    show "inj_on g (?U n)"
      using inj by (auto simp: inj_on_def)
  qed
  show ?thesis
    unfolding image_UN
  proof safe
    assume DS: "?D absolutely_integrable_on (\<Union>n. F n)"
      and b: "b = integral (\<Union>n. F n) ?D"
    have DU: "\<And>n. ?D absolutely_integrable_on (?U n)"
             "(\<lambda>n. integral (?U n) ?D) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
      using integral_countable_UN [OF DS F_leb] by auto
    with iff have fag: "f absolutely_integrable_on g ` (?U n)"
      and fg_int: "integral (\<Union>m\<le>n. g ` F m) f = integral (?U n) ?D" for n
      by (auto simp: image_UN)
    let ?h = "\<lambda>x. if x \<in> (\<Union>m. g ` F m) then norm(f x) else 0"
    have "(\<lambda>x. if x \<in> (\<Union>m. g ` F m) then f x else 0) absolutely_integrable_on UNIV"
    proof (rule dominated_convergence_absolutely_integrable)
      show "(\<lambda>x. if x \<in> (\<Union>m\<le>k. g ` F m) then f x else 0) absolutely_integrable_on UNIV" for k
        unfolding absolutely_integrable_restrict_UNIV
        using fag by (simp add: image_UN)
      let ?nf = "\<lambda>n x. if x \<in> (\<Union>m\<le>n. g ` F m) then norm(f x) else 0"
      show "?h integrable_on UNIV"
      proof (rule monotone_convergence_increasing [THEN conjunct1])
        show "?nf k integrable_on UNIV" for k
          using fag
          unfolding integrable_restrict_UNIV absolutely_integrable_on_def by (simp add: image_UN)
        { fix n
          have "(norm \<circ> ?D) absolutely_integrable_on ?U n"
            by (intro absolutely_integrable_norm DU)
          then have "integral (g ` ?U n) (norm \<circ> f) = integral (?U n) (norm \<circ> ?D)"
            using iff [of n "vec \<circ> norm \<circ> f" "integral (?U n) (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R (?lift \<circ> norm \<circ> f) (g x))"]
            unfolding absolutely_integrable_on_1_iff integral_on_1_eq by (auto simp: o_def)
        }
        moreover have "bounded (range (\<lambda>k. integral (?U k) (norm \<circ> ?D)))"
          unfolding bounded_iff
        proof (rule exI, clarify)
          fix k
          show "norm (integral (?U k) (norm \<circ> ?D)) \<le> integral (\<Union>n. F n) (norm \<circ> ?D)"
            unfolding integral_restrict_UNIV [of _ "norm \<circ> ?D", symmetric]
          proof (rule integral_norm_bound_integral)
            show "(\<lambda>x. if x \<in> \<Union> (F ` {..k}) then (norm \<circ> ?D) x else 0) integrable_on UNIV"
              "(\<lambda>x. if x \<in> (\<Union>n. F n) then (norm \<circ> ?D) x else 0) integrable_on UNIV"
              using DU(1) DS
              unfolding absolutely_integrable_on_def o_def integrable_restrict_UNIV by auto
          qed auto
        qed
        ultimately show "bounded (range (\<lambda>k. integral UNIV (?nf k)))"
          by (simp add: integral_restrict_UNIV image_UN [symmetric] o_def)
      next
        show "(\<lambda>k. if x \<in> (\<Union>m\<le>k. g ` F m) then norm (f x) else 0)
              \<longlonglongrightarrow> (if x \<in> (\<Union>m. g ` F m) then norm (f x) else 0)" for x
          by (force intro: tendsto_eventually eventually_sequentiallyI)
      qed auto
    next
      show "(\<lambda>k. if x \<in> (\<Union>m\<le>k. g ` F m) then f x else 0)
            \<longlonglongrightarrow> (if x \<in> (\<Union>m. g ` F m) then f x else 0)" for x
      proof clarsimp
        fix m y
        assume "y \<in> F m"
        show "(\<lambda>k. if \<exists>x\<in>{..k}. g y \<in> g ` F x then f (g y) else 0) \<longlonglongrightarrow> f (g y)"
          using \<open>y \<in> F m\<close> by (force intro: tendsto_eventually eventually_sequentiallyI [of m])
      qed
    qed auto
    then show fai: "f absolutely_integrable_on (\<Union>m. g ` F m)"
      using absolutely_integrable_restrict_UNIV by blast
    show "integral ((\<Union>x. g ` F x)) f = integral (\<Union>n. F n) ?D"
    proof (rule LIMSEQ_unique)
      show "(\<lambda>n. integral (?U n) ?D) \<longlonglongrightarrow> integral (\<Union>x. g ` F x) f"
        unfolding fg_int [symmetric]
      proof (rule integral_countable_UN [OF fai])
        show "g ` F m \<in> sets lebesgue" for m
        proof (rule differentiable_image_in_sets_lebesgue [OF F_leb])
          show "g differentiable_on F m"
            by (meson der_g differentiableI UnionI differentiable_on_def differentiable_on_subset rangeI subsetI)
        qed auto
      qed
    next
      show "(\<lambda>n. integral (?U n) ?D) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
        by (rule DU)
    qed
  next
    assume fs: "f absolutely_integrable_on (\<Union>x. g ` F x)"
      and b: "b = integral ((\<Union>x. g ` F x)) f"
    have gF_leb: "g ` F m \<in> sets lebesgue" for m
    proof (rule differentiable_image_in_sets_lebesgue [OF F_leb])
      show "g differentiable_on F m"
        using der_g unfolding differentiable_def differentiable_on_def
        by (meson Sup_upper UNIV_I UnionI has_derivative_subset image_eqI)
    qed auto
    have fgU: "\<And>n. f absolutely_integrable_on (\<Union>m\<le>n. g ` F m)"
      "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>m. g ` F m) f"
      using integral_countable_UN [OF fs gF_leb] by auto
    with iff have DUn: "?D absolutely_integrable_on ?U n"
      and D_int: "integral (?U n) ?D = integral (\<Union>m\<le>n. g ` F m) f" for n
      by (auto simp: image_UN)
    let ?h = "\<lambda>x. if x \<in> (\<Union>n. F n) then norm(?D x) else 0"
    have "(\<lambda>x. if x \<in> (\<Union>n. F n) then ?D x else 0) absolutely_integrable_on UNIV"
    proof (rule dominated_convergence_absolutely_integrable)
      show "(\<lambda>x. if x \<in> ?U k then ?D x else 0) absolutely_integrable_on UNIV" for k
        unfolding absolutely_integrable_restrict_UNIV using DUn by simp
      let ?nD = "\<lambda>n x. if x \<in> ?U n then norm(?D x) else 0"
      show "?h integrable_on UNIV"
      proof (rule monotone_convergence_increasing [THEN conjunct1])
        show "?nD k integrable_on UNIV" for k
          using DUn
          unfolding integrable_restrict_UNIV absolutely_integrable_on_def by (simp add: image_UN)
        { fix n::nat
          have "(norm \<circ> f) absolutely_integrable_on (\<Union>m\<le>n. g ` F m)"
            apply (rule absolutely_integrable_norm)
            using fgU by blast
          then have "integral (?U n) (norm \<circ> ?D) = integral (g ` ?U n) (norm \<circ> f)"
            using iff [of n "?lift \<circ> norm \<circ> f" "integral (g ` ?U n) (?lift \<circ> norm \<circ> f)"]
            unfolding absolutely_integrable_on_1_iff integral_on_1_eq image_UN by (auto simp: o_def)
        }
        moreover have "bounded (range (\<lambda>k. integral (g ` ?U k) (norm \<circ> f)))"
          unfolding bounded_iff
        proof (rule exI, clarify)
          fix k
          show "norm (integral (g ` ?U k) (norm \<circ> f)) \<le> integral (g ` (\<Union>n. F n)) (norm \<circ> f)"
            unfolding integral_restrict_UNIV [of _ "norm \<circ> f", symmetric]
          proof (rule integral_norm_bound_integral)
            show "(\<lambda>x. if x \<in> g ` ?U k then (norm \<circ> f) x else 0) integrable_on UNIV"
                 "(\<lambda>x. if x \<in> g ` (\<Union>n. F n) then (norm \<circ> f) x else 0) integrable_on UNIV"
              using fgU fs
              unfolding absolutely_integrable_on_def o_def integrable_restrict_UNIV
              by (auto simp: image_UN)
          qed auto
        qed
        ultimately show "bounded (range (\<lambda>k. integral UNIV (?nD k)))"
          unfolding integral_restrict_UNIV image_UN [symmetric] o_def by simp
      next
        show "(\<lambda>k. if x \<in> ?U k then norm (?D x) else 0) \<longlonglongrightarrow> (if x \<in> (\<Union>n. F n) then norm (?D x) else 0)" for x
          by (force intro: tendsto_eventually eventually_sequentiallyI)
      qed auto
    next
      show "(\<lambda>k. if x \<in> ?U k then ?D x else 0) \<longlonglongrightarrow> (if x \<in> (\<Union>n. F n) then ?D x else 0)" for x
      proof clarsimp
        fix n
        assume "x \<in> F n"
        show "(\<lambda>m. if \<exists>j\<in>{..m}. x \<in> F j then ?D x else 0) \<longlonglongrightarrow> ?D x"
          using \<open>x \<in> F n\<close> by (auto intro!: tendsto_eventually eventually_sequentiallyI [of n])
      qed
    qed auto
    then show Dai: "?D absolutely_integrable_on (\<Union>n. F n)"
      unfolding absolutely_integrable_restrict_UNIV by simp
    show "integral (\<Union>n. F n) ?D = integral ((\<Union>x. g ` F x)) f"
    proof (rule LIMSEQ_unique)
      show "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>x. g ` F x) f"
        by (rule fgU)
      show "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
        unfolding D_int [symmetric] by (rule integral_countable_UN [OF Dai F_leb])
    qed
  qed
qed


theorem has_absolute_integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  obtain C N where "fsigma C" and N: "N \<in> null_sets lebesgue" and CNS: "C \<union> N = S" and "disjnt C N"
    using lebesgue_set_almost_fsigma [OF S] .
  then obtain F :: "nat \<Rightarrow> (real^'m::_) set"
    where F: "range F \<subseteq> Collect compact" and Ceq: "C = Union(range F)"
    using fsigma_Union_compact by metis
  have "negligible N"
    using N by (simp add: negligible_iff_null_sets)
  let ?D = "\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f (g x)"
  have "?D absolutely_integrable_on C \<and> integral C ?D = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` C) \<and> integral (g ` C) f = b"
    unfolding Ceq
  proof (rule has_absolute_integral_change_of_variables_compact_family)
    fix n x
    assume "x \<in> \<Union>(F ` UNIV)"
    then show "(g has_derivative g' x) (at x within \<Union>(F ` UNIV))"
      using Ceq \<open>C \<union> N = S\<close> der_g has_derivative_subset by blast
  next
    have "\<Union>(F ` UNIV) \<subseteq> S"
      using Ceq \<open>C \<union> N = S\<close> by blast
    then show "inj_on g (\<Union>(F ` UNIV))"
      using inj by (meson inj_on_subset)
  qed (use F in auto)
  moreover
  have "?D absolutely_integrable_on C \<and> integral C ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
  proof (rule conj_cong)
    have neg: "negligible {x \<in> C - S. ?D x \<noteq> 0}" "negligible {x \<in> S - C. ?D x \<noteq> 0}"
      using CNS by (blast intro: negligible_subset [OF \<open>negligible N\<close>])+
    then show "(?D absolutely_integrable_on C) = (?D absolutely_integrable_on S)"
      by (rule absolutely_integrable_spike_set_eq)
    show "(integral C ?D = b) \<longleftrightarrow> (integral S ?D = b)"
      using integral_spike_set [OF neg] by simp
  qed
  moreover
  have "f absolutely_integrable_on (g ` C) \<and> integral (g ` C) f = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
  proof (rule conj_cong)
    have "g differentiable_on N"
      by (metis CNS der_g differentiable_def differentiable_on_def differentiable_on_subset sup.cobounded2)
    with \<open>negligible N\<close>
    have neg_gN: "negligible (g ` N)"
      by (blast intro: negligible_differentiable_image_negligible)
    have neg: "negligible {x \<in> g ` C - g ` S. f x \<noteq> 0}"
              "negligible {x \<in> g ` S - g ` C. f x \<noteq> 0}"
      using CNS by (blast intro: negligible_subset [OF neg_gN])+
    then show "(f absolutely_integrable_on g ` C) = (f absolutely_integrable_on g ` S)"
      by (rule absolutely_integrable_spike_set_eq)
    show "(integral (g ` C) f = b) \<longleftrightarrow> (integral (g ` S) f = b)"
      using integral_spike_set [OF neg] by simp
  qed
  ultimately show ?thesis
    by simp
qed


corollary absolutely_integrable_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "inj_on g S"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  using assms has_absolute_integral_change_of_variables by blast

corollary integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and disj: "(f absolutely_integrable_on (g ` S) \<or>
        (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  shows "integral (g ` S) f = integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x))"
  using has_absolute_integral_change_of_variables [OF S der_g inj] disj
  by blast

lemma has_absolute_integral_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  let ?lift = "vec :: real \<Rightarrow> real^1"
  let ?drop = "(\<lambda>x::real^1. x $ 1)"
  have S': "?lift ` S \<in> sets lebesgue"
    by (auto intro: differentiable_image_in_sets_lebesgue [OF S] differentiable_vec)
  have "((\<lambda>x. vec (g (x $ 1))) has_derivative (*\<^sub>R) (g' z)) (at (vec z) within ?lift ` S)"
    if "z \<in> S" for z
    using der_g [OF that]
    by (simp add: has_vector_derivative_def has_derivative_vector_1)
  then have der': "\<And>x. x \<in> ?lift ` S \<Longrightarrow>
        (?lift \<circ> g \<circ> ?drop has_derivative (*\<^sub>R) (g' (?drop x))) (at x within ?lift ` S)"
    by (auto simp: o_def)
  have inj': "inj_on (vec \<circ> g \<circ> ?drop) (vec ` S)"
    using inj by (simp add: inj_on_def)
  let ?fg = "\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. ?fg x $ i) absolutely_integrable_on S \<and> ((\<lambda>x. ?fg x $ i) has_integral b $ i) S
    \<longleftrightarrow> (\<lambda>x. f x $ i) absolutely_integrable_on g ` S \<and> ((\<lambda>x. f x $ i) has_integral b $ i) (g ` S))" for i
    using has_absolute_integral_change_of_variables [OF S' der' inj', of "\<lambda>x. ?lift(f (?drop x) $ i)" "?lift (b$i)"]
    unfolding integrable_on_1_iff integral_on_1_eq absolutely_integrable_on_1_iff absolutely_integrable_drop absolutely_integrable_on_def
    by (auto simp: image_comp o_def integral_vec1_eq has_integral_iff)
  then have "?fg absolutely_integrable_on S \<and> (?fg has_integral b) S
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> (f has_integral b) (g ` S)"
    unfolding has_integral_componentwise_iff [where y=b]
           absolutely_integrable_componentwise_iff [where f=f]
           absolutely_integrable_componentwise_iff [where f = ?fg]
    by (force simp: Basis_vec_def cart_eq_inner_axis)
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed


corollary absolutely_integrable_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(f absolutely_integrable_on g ` S \<longleftrightarrow>
             (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  using has_absolute_integral_change_of_variables_1 [OF assms] by auto

text \<open>when @{term "n=1"}\<close>
lemma has_absolute_integral_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x)) :: real ^ 1) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x))) = (vec b :: real ^ 1)
         \<longleftrightarrow> (\<lambda>x. vec (f x) :: real ^ 1) absolutely_integrable_on (g ` S) \<and>
           integral (g ` S) (\<lambda>x. vec (f x)) = (vec b :: real ^ 1)"
    using assms unfolding has_field_derivative_iff_has_vector_derivative
    by (intro has_absolute_integral_change_of_variables_1 assms) auto
  thus ?thesis
    by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq)
qed


subsection\<open>Change of variables for integrals: special case of linear function\<close>

lemma has_absolute_integral_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof (cases "det(matrix g) = 0")
  case True
  then have "negligible(g ` S)"
    using assms det_nz_iff_inj negligible_linear_singular_image by blast
  with True show ?thesis
    by (auto simp: absolutely_integrable_on_def integrable_negligible integral_negligible)
next
  case False
  then obtain h where h: "\<And>x. x \<in> S \<Longrightarrow> h (g x) = x" "linear h"
    using assms det_nz_iff_inj linear_injective_isomorphism by metis
  show ?thesis
  proof (rule has_absolute_integral_change_of_variables_invertible)
    show "(g has_derivative g) (at x within S)" for x
      by (simp add: assms linear_imp_has_derivative)
    show "continuous_on (g ` S) h"
      using continuous_on_eq_continuous_within has_derivative_continuous linear_imp_has_derivative h by blast
  qed (use h in auto)
qed

lemma absolutely_integrable_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S
     \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
  using assms has_absolute_integral_change_of_variables_linear by blast

lemma absolutely_integrable_on_linear_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (f \<circ> g) absolutely_integrable_on S \<or> det(matrix g) = 0"
  unfolding assms absolutely_integrable_change_of_variables_linear [OF assms, symmetric] absolutely_integrable_on_scaleR_iff
  by (auto simp: set_integrable_def)

lemma integral_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>det (matrix g)\<bar> *\<^sub>R integral S (f \<circ> g)"
proof -
  have "((\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S) \<or> (f absolutely_integrable_on g ` S)"
    using absolutely_integrable_on_linear_image assms by blast
  moreover
  have ?thesis if "((\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S)" "(f absolutely_integrable_on g ` S)"
    using has_absolute_integral_change_of_variables_linear [OF \<open>linear g\<close>] that
    by (auto simp: o_def)
  ultimately show ?thesis
    using absolutely_integrable_change_of_variables_linear [OF \<open>linear g\<close>]
    by blast
qed

subsection\<open>Change of variable for measure\<close>

lemma has_measure_differentiable_image:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) = m
     \<longleftrightarrow> ((\<lambda>x. \<bar>det (matrix (f' x))\<bar>) has_integral m) S"
  using has_absolute_integral_change_of_variables [OF assms, of "\<lambda>x. (1::real^1)" "vec m"]
  unfolding absolutely_integrable_on_1_iff integral_on_1_eq integrable_on_1_iff absolutely_integrable_on_def
  by (auto simp: has_integral_iff lmeasurable_iff_integrable_on lmeasure_integral)

lemma measurable_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  using has_measure_differentiable_image [OF assms]
  by blast

lemma measurable_differentiable_image_alt:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on S"
  using measurable_differentiable_image_eq [OF assms]
  by (simp only: absolutely_integrable_on_iff_nonneg)

lemma measure_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
  using measurable_differentiable_image_eq [OF S der_f inj]
        assms has_measure_differentiable_image by blast

end

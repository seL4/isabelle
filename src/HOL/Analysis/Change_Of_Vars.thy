(*  Title:      HOL/Analysis/Change_Of_Vars.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section\<open>Change of Variables Theorems\<close>

theory Change_Of_Vars
  imports Vitali_Covering_Theorem Determinants
          Determinant_Linear_Function Euclidean_Space_Transfer

begin

subsection \<open>Measurable Shear and Stretch\<close>

proposition
  fixes a :: "real^'n"
  assumes "m \<noteq> n" and ab_ne: "cbox a b \<noteq> {}" and an: "0 \<le> a$n"
  shows measurable_shear_interval: "(\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` (cbox a b) \<in> lmeasurable"
       (is  "?f ` _ \<in> _")
   and measure_shear_interval: 
        "measure lebesgue ((\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` cbox a b)
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
      apply (clarsimp simp: algebra_simps mem_box_cart inner_axis')
      by (smt (verit, ccfv_SIG) interval_ne_empty_cart(1))
    ultimately show "negligible (cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<inter> (cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m}))"
      by (rule negligible_subset)
    show "?f ` cbox a b \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<union> cbox a ?c \<inter> {x. ?mn \<bullet> x \<ge> b$m} = cbox a ?c" (is "?lhs = _")
    proof
      show "?lhs \<subseteq> cbox a ?c"
        by (auto simp: mem_box_cart add_mono) (meson add_increasing2 an order_trans)
      show "cbox a ?c \<subseteq> ?lhs"
        apply (clarsimp simp: algebra_simps image_iff inner_axis' lambda_add_Galois [OF \<open>m \<noteq> n\<close>])
        by (smt (verit, del_insts) mem_box_cart(2) vec_lambda_beta)
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
    moreover have "a $ m \<le> b $ m"
      by (metis ab_ne interval_ne_empty_cart(1))
      ultimately show "cbox a ?c \<inter> {x. ?mn \<bullet> x \<le> a $ m} \<union>
          (+) ?d ` (cbox a ?c \<inter> {x. b $ m \<le> ?mn \<bullet> x}) =
          cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i)"  (is "?lhs = ?rhs")
      using an \<open>m \<noteq> n\<close>
      by (force simp: mem_box_cart inner_axis' algebra_simps if_distrib all_if_distrib)
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
    by (smt (verit, del_insts) ab_ne an interval_ne_empty_cart(1) vec_lambda_beta)
  have ax_ne: "cbox a (\<chi> i. if i = m then a $ m + b $ n else b $ i) \<noteq> {}"
    using ab_ne an
    by (smt (verit, ccfv_threshold) interval_ne_empty_cart(1) vec_lambda_beta)
  have eq3: "measure lebesgue (cbox a ?c) = measure lebesgue (cbox a (\<chi> i. if i = m then a$m + b$n else b$i)) + measure lebesgue (cbox a b)"
    by (simp add: content_cbox_if_cart ab_ne ac_ne ax_ne algebra_simps prod.delta_remove
             if_distrib [of "\<lambda>u. u - z" for z] prod.remove)
  show ?Q
    using eq1 eq2 eq3 by (simp add: algebra_simps)
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
              by (metis (no_types, opaque_lifting) abs_abs abs_scaleR mult.commute real_scaleR_def right_diff_distrib')
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
    then show ?thesis
      by (simp add: negligible_iff_measure prm)
  qed
  then show "(?f ` S) \<in> lmeasurable" ?MEQ
    by metis+
qed


proposition
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "linear f" "S \<in> lmeasurable"
  shows measurable_linear_image_cart: "(f ` S) \<in> lmeasurable"
    and measure_linear_image_cart: "measure lebesgue (f ` S) = \<bar>matrix_det (matrix f)\<bar> * measure lebesgue S" (is "?Q f S")
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
    have detf: "matrix_det (matrix f) = 0"
      using \<open>\<not> inj f\<close> det_nz_iff_inj[OF \<open>linear f\<close>] by blast
    show "f ` S \<in> lmeasurable \<and> ?Q f S"
    proof
      show "f ` S \<in> lmeasurable"
        using lmeasurable_iff_indicator_has_integral \<open>linear f\<close> \<open>\<not> inj f\<close> negligible_UNIV negligible_linear_singular_image by blast
      have "measure lebesgue (f ` S) = 0"
        by (meson \<open>\<not> inj f\<close> \<open>linear f\<close> negligible_imp_measure0 negligible_linear_singular_image)
      also have "\<dots> = \<bar>matrix_det (matrix f)\<bar> * measure lebesgue S"
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
    then have 1: "\<bar>matrix_det (matrix ?h)\<bar> = 1"
      by (simp add: det_permute_columns permutes_swap_id sign_swap_id abs_mult)
    show "?h ` S \<in> lmeasurable \<and> ?Q ?h S"
      using measure_linear_sufficient [OF lin \<open>S \<in> lmeasurable\<close>] meq 1 by force
  next
    fix m n :: "'n" and S :: "(real, 'n) vec set"
    assume "m \<noteq> n" and "S \<in> lmeasurable"
    let ?h = "\<lambda>v::(real, 'n) vec. \<chi> i. if i = m then v $ m + v $ n else v $ i"
    have lin: "linear ?h"
      by (rule linearI) (auto simp: algebra_simps plus_vec_def scaleR_vec_def vec_eq_iff)
    consider "m < n" | " n < m"
      using \<open>m \<noteq> n\<close> less_linear by blast
    then have 1: "matrix_det(matrix ?h) = 1"
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
      also have "\<dots> = measure lebesgue ((+) ?v ` cbox a b)"
        using \<open>m \<noteq> n\<close> ne 
        by (subst measure_shear_interval) (auto simp: cbox_translation)
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


proposition
 fixes f :: "'a :: euclidean_space \<Rightarrow> 'a"
  assumes "linear f" "S \<in> lmeasurable"
  shows measurable_linear_image: "(f ` S) \<in> lmeasurable"
    and measure_linear_image: "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
proof -
  note [transfer_rule] = transfer_measure_bij_rules transfer_eucl_bij_rules
  show "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
    using measure_linear_image_cart[where ?'n = "'a basis", untransferred, OF assms] .
  show "(f ` S) \<in> lmeasurable"
    using measurable_linear_image_cart[where ?'n = "'a basis", untransferred, OF assms] .
qed

lemma
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes f: "orthogonal_transformation f" and S: "S \<in> lmeasurable"
  shows measurable_orthogonal_image: "f ` S \<in> lmeasurable"
    and measure_orthogonal_image: "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
proof -
  have "linear f"
    by (simp add: f orthogonal_transformation_linear)
  then show "f ` S \<in> lmeasurable"
    by (metis S measurable_linear_image)
  show "measure lebesgue (f ` S) = \<bar>eucl.det f\<bar> * measure lebesgue S"
    using S f \<open>linear f\<close> measure_linear_image by blast
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
    have "- U \<noteq> {}"
      using \<open>U \<in> lmeasurable\<close>
      by (metis boolean_algebra.compl_zero double_complement not_measurable_UNIV)
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
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> lmeasurable"
  and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  and bounded: "\<And>x. x \<in> S \<Longrightarrow> \<bar>eucl.det (f' x)\<bar> \<le> B"
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
          let ?unit_vol = "Henstock_Kurzweil_Integration.content (ball (0 :: 'a) 1)"
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
                apply (clarsimp simp: dist_norm image_iff dest!: ex_lessK)
                by (metis add.commute diff_add_cancel dist_commute dist_norm ex_lessK mem_ball_0)
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
            have "?\<mu> (f ` (S \<inter> ball x r)) = ?\<mu> (?rfs) * r ^ DIM('a)"
              using \<open>r > 0\<close> fsb
              by (simp add: measure_linear_image measure_translation_subtract measurable_translation_subtract eucl.det_scale' field_simps cong: image_cong_simp)
            also have "\<dots> \<le> (\<bar>eucl.det (f' x)\<bar> * ?unit_vol + e * ?unit_vol) * r ^ DIM('a)"
            proof -
              have "?\<mu> (?rfs) < ?\<mu> (f' x ` ball 0 1) + e * ?unit_vol"
                using rfs_mble by (force intro: k dest!: ex_lessK)
              then have "?\<mu> (?rfs) < \<bar>eucl.det (f' x)\<bar> * ?unit_vol + e * ?unit_vol"
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
            using pwC that pairwise_image pairwise_mono by fastforce
          have "?l \<le> (\<Sum>i\<in>K. ?\<mu> (case i of (x, s) \<Rightarrow> f ` (S \<inter> ball x s)))"
          proof (rule measure_UNION_le [OF \<open>finite K\<close>], clarify)
          qed (meson Int_lower1 S differentiable_on_subset f_diff fmeasurableD 
                  lmeasurable_ball order_refl sets.Int differentiable_image_in_sets_lebesgue)
          also have "\<dots> \<le> (\<Sum>(x,s) \<in> K. (B + e) * ?\<mu> (ball x s))"
            using Csub r \<open>K \<subseteq> C\<close>  by (intro sum_mono) auto
          also have "\<dots> = (B + e) * (\<Sum>(x,s) \<in> K. ?\<mu> (ball x s))"
            by (simp add: prod.case_distrib sum_distrib_left)
          also have "\<dots> = (B + e) * sum ?\<mu> ((\<lambda>(x, y). ball x y) ` K)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> by (simp add: inj sum.reindex prod.case_distrib)
          also have "\<dots> = (B + e) * ?\<mu> (\<Union>(x,s) \<in> K. ball x s)"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that
            by (subst measure_Union') (auto simp: disjnt measure_Union')
          also have "\<dots> \<le> (B + e) * ?\<mu> T"
            using \<open>B \<ge> 0\<close> \<open>e > 0\<close> that 
            using measure_mono_fmeasurable [OF _ _ \<open>T \<in> lmeasurable\<close>] Csub rT
            apply simp
            by (smt (verit) SUP_least measure_nonneg measure_notin_sets mem_Collect_eq old.prod.case subset_iff)
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
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> lmeasurable"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
proof -
  let ?\<mu> = "measure lebesgue"
  have aint_S: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) absolutely_integrable_on S"
    using int unfolding absolutely_integrable_on_def by auto
  define m where "m \<equiv> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
  have *: "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
    if "e > 0" for e
  proof -
    define Sn where "Sn \<equiv> \<lambda>n. {x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar> \<and> \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e}"
    have Sn_sub: "Sn n \<subseteq> S" for n
      by (auto simp: Sn_def)
    have S_eq: "S = (\<Union>n. Sn n)"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> S"
      define n where "n = nat \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor>"
      have "real_of_int \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> * e \<le> \<bar>eucl.det (f' x)\<bar>"
        using floor_divide_lower \<open>e > 0\<close> by blast
      moreover have "\<bar>eucl.det (f' x)\<bar> < (real_of_int \<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> + 1) * e"
        using floor_divide_upper \<open>e > 0\<close> by blast
      moreover have "\<lfloor>\<bar>eucl.det (f' x)\<bar> / e\<rfloor> \<ge> 0"
        using \<open>e > 0\<close> by (simp add: floor_divide_lower)
      ultimately have "x \<in> Sn n"
        using \<open>x \<in> S\<close> by (auto simp: Sn_def n_def of_nat_nat nat_add_distrib algebra_simps)
      then show "x \<in> (\<Union>n. Sn n)" by auto
    qed (auto simp: Sn_def)
    have Sn_mble: "Sn n \<in> lmeasurable" for n
    proof -
      have meas: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) \<in> borel_measurable (lebesgue_on S)"
        using integrable_imp_measurable[OF int] .
      have 1: "{x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar>} \<in> sets (lebesgue_on S)"
        using borel_measurable_le[OF _ meas] by simp
      have 2: "{x \<in> S. \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e} \<in> sets (lebesgue_on S)"
        using borel_measurable_less[OF meas] by simp
      have "{x \<in> S. real n * e \<le> \<bar>eucl.det (f' x)\<bar> \<and> \<bar>eucl.det (f' x)\<bar> < real (Suc n) * e} \<in> sets (lebesgue_on S)"
        using sets.Int[OF 1 2] by (metis Collect_conj_eq2)
      then have "Sn n \<in> sets lebesgue"
        using S sets_restrict_space_iff[of S lebesgue] Sn_def by blast
      then show ?thesis
        using fmeasurableI2[OF S Sn_sub] by blast
    qed
    have Sn_deriv: "(f has_derivative f' x) (at x within Sn n)" if "x \<in> Sn n" for x n
      by (meson Sn_sub deriv has_derivative_subset subsetD that)
    have Sn_int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on Sn n" for n
      by (metis Sn_mble Sn_sub aint_S fmeasurableD set_integrable_subset 
          set_lebesgue_integral_eq_integral(1))
    have Sn_bdd: "\<bar>eucl.det (f' x)\<bar> \<le> real (Suc n) * e" if "x \<in> Sn n" for x n
      using that by (auto simp: Sn_def less_imp_le)
    have fSn_mble: "f ` Sn n \<in> lmeasurable" for n
      using measurable_bounded_differentiable_image [OF Sn_mble Sn_deriv Sn_int Sn_bdd] .
    have fSn_meas: "?\<mu> (f ` Sn n) \<le> real (Suc n) * e * ?\<mu> (Sn n)" for n
      using measure_bounded_differentiable_image [OF Sn_mble Sn_deriv Sn_int Sn_bdd] .
    have fSn_meas2: "?\<mu> (f ` Sn n) \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) + e * ?\<mu> (Sn n)" for n
    proof -
      have "real (Suc n) * e * ?\<mu> (Sn n) = real n * e * ?\<mu> (Sn n) + e * ?\<mu> (Sn n)"
        by (simp add: algebra_simps)
      also have "real n * e * ?\<mu> (Sn n) \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      proof -
        have "real n * e * ?\<mu> (Sn n) = integral (Sn n) (\<lambda>x. real n * e)"
          using lmeasure_integral[OF Sn_mble] integral_mult_right[of "Sn n" "real n * e"]
          by (metis (no_types, lifting) Henstock_Kurzweil_Integration.integral_cong lambda_one mult_commute_abs)
        also have "\<dots> \<le> integral (Sn n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
          using integral_le[OF integrable_on_const[OF Sn_mble] Sn_int] Sn_def by blast
        finally show ?thesis .
      qed
      finally show ?thesis using fSn_meas [of n] by linarith
    qed
    have "f ` S = (\<Union>n. f ` Sn n)"
      using S_eq by auto
    have disj: "disjoint_family_on Sn {..n}" for n
      unfolding disjoint_family_on_def Sn_def 
      using mult_strict_right_mono[OF _ \<open>e > 0\<close>]
      apply (simp add: set_eq_iff)
      by (smt (verit, best) nat_le_real_less of_nat_eq_iff of_nat_mono)
    have bound: "?\<mu> (\<Union> ((\<lambda>k. f ` Sn k) ` {..n})) \<le> m + e * ?\<mu> S" for n
    proof -
      have "?\<mu> (\<Union> ((\<lambda>k. f ` Sn k) ` {..n})) \<le> (\<Sum>k\<le>n. ?\<mu> (f ` Sn k))"
        by (intro measure_UNION_le) (auto intro: fSn_mble fmeasurableD)
      also have "\<dots> \<le> (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) + e * ?\<mu> (Sn k))"
        by (intro sum_mono) (use fSn_meas2 in auto)
      also have "\<dots> = (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) + e * (\<Sum>k\<le>n. ?\<mu> (Sn k))"
        by (simp add: sum.distrib sum_distrib_left)
      also have "\<dots> \<le> m + e * ?\<mu> S"
      proof (intro add_mono mult_left_mono)
        show "(\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) \<le> m"
        proof -
          have pw: "pairwise (\<lambda>i i'. negligible (Sn i \<inter> Sn i')) {..n}"
            using disj unfolding disjoint_family_on_def pairwise_def
            by auto
          have hi: "((\<lambda>x. \<bar>eucl.det (f' x)\<bar>) has_integral (\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>))) (\<Union>k\<le>n. Sn k)"
            by (intro has_integral_UN[OF _ _ pw]) (auto intro: integrable_integral Sn_int)
          have sum_eq: "(\<Sum>k\<le>n. integral (Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)) = integral (\<Union>k\<le>n. Sn k) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
            using integral_unique[OF hi] by simp
          also have "\<dots> \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
            by (metis Sn_sub UN_least abs_ge_zero hi int integrable_on_def
                integral_subset_le)
          finally show ?thesis by (simp add: m_def)
        qed
        show "(\<Sum>k\<le>n. ?\<mu> (Sn k)) \<le> ?\<mu> S"
        proof -
          have "(\<Sum>k\<le>n. ?\<mu> (Sn k)) = ?\<mu> (\<Union>k\<le>n. Sn k)"
            by (intro measure_finite_Union[symmetric])
               (auto intro: disj fmeasurableD[OF Sn_mble]
                     simp: emeasure_eq_measure2[OF Sn_mble])
          also have "\<dots> \<le> ?\<mu> S"
            by (metis S Sn_sub UN_least measure_mono_fmeasurable measure_nonneg
                measure_notin_sets)
          finally show ?thesis .
        qed
        show "0 \<le> e" using \<open>e > 0\<close> by linarith
      qed
      finally show ?thesis .
    qed
    have fS_mble: "f ` S \<in> lmeasurable"
      using fmeasurable_countable_Union[OF fSn_mble bound] \<open>f ` S = (\<Union>n. f ` Sn n)\<close>
      by (metis (no_types))
    have fS_meas: "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
      using measure_countable_Union_le[OF fSn_mble bound] \<open>f ` S = (\<Union>n. f ` Sn n)\<close>
      by (metis (no_types) atMost_atLeast0 image_comp)
    show "f ` S \<in> lmeasurable" "?\<mu> (f ` S) \<le> m + e * ?\<mu> S"
      using fS_mble fS_meas by auto
  qed
  let ?x = "m - ?\<mu> (f ` S)"
  have False if "?\<mu> (f ` S) > integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
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
  then show ?thesis
    by (meson "*"(1) gt_ex linorder_not_le)
qed


theorem
 fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows measurable_differentiable_image: "f ` S \<in> lmeasurable"
    and measure_differentiable_image:
       "measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" (is "?M")
proof -
  let ?One = "\<Sum>i\<in>Basis. i :: 'a"
  let ?I = "\<lambda>n::nat. cbox (- real n *\<^sub>R ?One) (real n *\<^sub>R ?One) \<inter> S"
  let ?\<mu> = "measure lebesgue"
  have "\<And>x. x \<in> S \<Longrightarrow> \<exists>xa. \<forall>i\<in>Basis. - real xa \<le> x \<bullet> i \<and> x \<bullet> i \<le> real xa"
    by (meson abs_le_iff minus_le_iff norm_bound_Basis_le real_arch_simple)
  then have Seq: "S = (\<Union>n. ?I n)"
    by (auto simp: mem_box)
  have fIn: "f ` ?I n \<in> lmeasurable"
       and mfIn: "?\<mu> (f ` ?I n) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" (is ?MN) for n
  proof -
    have In_mble: "?I n \<in> lmeasurable"
      by (simp add: S fmeasurable_Int_fmeasurable)
    have In_deriv: "(f has_derivative f' x) (at x within ?I n)" if "x \<in> ?I n" for x
      by (meson IntD2 deriv has_derivative_subset inf_le2 that)
    have In_int: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on ?I n"
      using int integrable_on_subcbox
      by (metis (lifting) Int_commute integrable_altD(1) integrable_restrict_Int)
    have res: "f ` ?I n \<in> lmeasurable \<and> ?\<mu> (f ` ?I n) \<le> integral (?I n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      by (rule m_diff_image_weak [OF In_mble In_deriv In_int])
    then show "f ` ?I n \<in> lmeasurable" by blast
    have "integral (?I n) (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
      by (rule integral_subset_le [OF _ In_int int]) auto
    with res show ?MN by linarith
  qed
  have "(\<Union>k\<le>n. f ` ?I k) = f ` ?I n" for n
    by (fastforce simp: mem_box)
  with mfIn have "?\<mu> (\<Union>k\<le>n. f ` ?I k) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)" for n
    by simp
  then have "(\<Union>n. f ` ?I n) \<in> lmeasurable" "?\<mu> (\<Union>n. f ` ?I n) \<le> integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
    by (rule fmeasurable_countable_Union [OF fIn] measure_countable_Union_le [OF fIn])+
  then show "f ` S \<in> lmeasurable" ?M
    by (metis Seq image_UN)+
qed

subsection\<open>Borel measurable Jacobian determinant\<close>

proposition linear_rational_approximation:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "e > 0"
  obtains g where "linear g" "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> g i \<bullet> j \<in> \<rat>"
    "onorm (f - g) < e"
proof -
  define d where "d = e / (2 * DIM('a) * DIM('b))"
  have "d > 0" using assms by (simp add: d_def)
  have "\<forall>i \<in> Basis. \<forall>j \<in> Basis. \<exists>q \<in> \<rat>. \<bar>q - f i \<bullet> j\<bar> < d"
    using \<open>d > 0\<close> by (force intro: rational_approximation)
  then obtain q where qrat: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> q i j \<in> \<rat>"
          and qclo: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> \<bar>q i j - f i \<bullet> j\<bar> < d"
    by (metis (mono_tags))
  define G where "G = blinfun_of_matrix (\<lambda>i j. q j i)"
  define g where "g = blinfun_apply G"
  have lin_g: "linear g"
    unfolding g_def using blinfun.bounded_linear_right linear_conv_bounded_linear by blast
  have g_eq: "\<And>x. g x = (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. (x \<bullet> j * q j i)) *\<^sub>R i)"
    unfolding g_def G_def blinfun_of_matrix_apply
    by (simp add: scale_sum_left[symmetric])
  have g_basis: "\<And>k m. k \<in> Basis \<Longrightarrow> m \<in> Basis \<Longrightarrow> g k \<bullet> m = q k m"
  proof -
    fix k :: 'a and m :: 'b assume km: "k \<in> Basis" "m \<in> Basis"
    have "g k \<bullet> m = (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. (k \<bullet> j * q j i)) *\<^sub>R i) \<bullet> m"
      by (simp add: g_eq)
    also have "\<dots> = (\<Sum>j\<in>Basis. k \<bullet> j * q j m)"
      using km by (simp add: inner_sum_left_Basis)
    also have "\<dots> = q k m"
    proof -
      have "(\<Sum>j\<in>Basis. k \<bullet> j * q j m) = (\<Sum>j\<in>Basis. if k = j then q j m else 0)"
        by (intro sum.cong) (auto simp: km inner_Basis)
      also have "\<dots> = q k m"
        using km by (simp add: sum.delta')
      finally show ?thesis .
    qed
    finally show "g k \<bullet> m = q k m" .
  qed
  show thesis
  proof (rule that[OF lin_g])
    show "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> g i \<bullet> j \<in> \<rat>"
      using g_basis qrat by simp
  next
    have bl_fg: "bounded_linear (\<lambda>x. f x - g x)"
      using assms(1) lin_g linear_conv_bounded_linear by (intro bounded_linear_sub) blast+
    have "onorm (f - g) \<le> (\<Sum>i\<in>Basis. norm ((f - g) i))"
      using onorm_componentwise[OF bl_fg] by (simp add: fun_diff_def)
    also have "\<dots> \<le> (\<Sum>i\<in>(Basis::'a set). (\<Sum>j\<in>(Basis::'b set). \<bar>(f - g) i \<bullet> j\<bar>))"
      by (intro sum_mono norm_le_l1)
    also have "\<dots> = (\<Sum>i\<in>(Basis::'a set). (\<Sum>j\<in>(Basis::'b set). \<bar>f i \<bullet> j - q i j\<bar>))"
      by (simp add: inner_diff_left g_basis)
    also have "\<dots> < (\<Sum>i\<in>(Basis::'a set). (\<Sum>j\<in>(Basis::'b set). d))"
      by (intro sum_strict_mono finite_Basis) (use qclo abs_minus_commute in force)+
    also have "\<dots> = DIM('a) * DIM('b) * d"
      by simp
    also have "\<dots> = e / 2"
      unfolding d_def by simp
    also have "\<dots> < e" using assms by simp
    finally show "onorm (f - g) < e" .
  qed
qed


proposition orthogonal_transformation_exists:
  fixes a b :: "'a::euclidean_space"
  assumes "norm a = norm b"
  obtains T where "orthogonal_transformation T" "T a = b"
proof -
  let ?a' = "eucl_to_vec a :: real ^ 'a basis"
  let ?b' = "eucl_to_vec b :: real ^ 'a basis"
  have norm_eq: "norm ?a' = norm ?b'"
    using assms
    by (metis (mono_tags) eucl_of_vec_to_vec transfer_eucl_norm rel_funD eucl_vec_rel_altdef)
  then obtain T' :: "real ^ 'a basis \<Rightarrow> real ^ 'a basis"
    where T': "orthogonal_transformation T'" "T' ?a' = ?b'"
    using orthogonal_transformation_exists by metis
  define T where "T = eucl_of_vec \<circ> T' \<circ> eucl_to_vec"
  have inner_eq: "T v \<bullet> T w = v \<bullet> w" for v w
  proof -
    have "T v \<bullet> T w = T' (eucl_to_vec v) \<bullet> T' (eucl_to_vec w)"
      unfolding T_def comp_def 
      by (metis (mono_tags) transfer_eucl_vec_inner rel_funD eucl_vec_rel_def)
    also have "\<dots> = eucl_to_vec v \<bullet> eucl_to_vec w"
      using T'(1) by (simp add: orthogonal_transformation_def)
    also have "\<dots> = v \<bullet> w"
      by (metis (mono_tags) eucl_vec_rel_altdef rel_funD transfer_eucl_vec_inner)
    finally show ?thesis .
  qed
  have "linear T"
  proof (rule linearI)
    fix x y :: 'a
    show "T (x + y) = T x + T y"
      by (smt (verit) inner_eq vector_eq inner_commute inner_right_distrib)  
  next
    fix c x
    show "T (c *\<^sub>R x) = c *\<^sub>R T x"
      by (simp add: inner_eq vector_eq)
  qed
  then have "orthogonal_transformation T"
    using inner_eq by (simp add: orthogonal_transformation_def)
  moreover have "T a = b"
    unfolding T_def comp_def using T'(2) by simp
  ultimately show thesis
    using that by blast
qed


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
    by (metis (mono_tags, lifting) dim_eq_full UNIV_I eq_0_on_span mem_Collect_eq span_raw_def)
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
      using lb [OF v] by (force simp: norm_minus_commute)
  qed
qed

lemma countable_rational_linear_maps:
  "countable {A :: 'a::euclidean_space \<Rightarrow> 'b::euclidean_space. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
proof -
  \<comment> \<open>A linear function is determined by its values on Basis\<close>
  { fix A B :: "'a \<Rightarrow> 'b"
    assume "linear A" "linear B" "\<forall>x\<in>Basis. A x = B x"
    then have "A = B"
      by (simp add: linear_eq_stdbasis)
  }
  then have inj: "inj_on (\<lambda>A. restrict A Basis)
                         {A :: 'a \<Rightarrow> 'b. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
    by (smt (verit, ccfv_SIG) inj_onI mem_Collect_eq restrict_apply')
      \<comment> \<open>The range of this restriction is contained in a countable set\<close>
  have "countable {g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)}"
  proof (rule countable_subset)
    let ?V = "{w :: 'b. \<forall>j\<in>Basis. w \<bullet> j \<in> \<rat>}"
    have cV: "countable ?V"
    proof -
      have inj: "inj_on (\<lambda>w. restrict (\<lambda>j. w \<bullet> j) (Basis :: 'b set)) ?V"
        by (metis (mono_tags, lifting) euclidean_eq_iff inj_on_def restrict_apply')
      moreover have "(\<lambda>w. restrict (\<lambda>j. w \<bullet> j) (Basis :: 'b set)) ` ?V \<subseteq> PiE Basis (\<lambda>_. \<rat>)"
        by (auto simp: PiE_def Pi_def extensional_def restrict_def)
      moreover have "countable (PiE (Basis :: 'b set) (\<lambda>_. \<rat>))" 
        by (intro countable_PiE finite_Basis) (auto simp: countable_rat)
      ultimately show ?thesis
        by (metis (mono_tags, lifting) countable_image_inj_on countable_subset)
    qed
    show "{g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)} 
       \<subseteq> Basis \<rightarrow>\<^sub>E  ?V"
      by blast
    show "countable (Basis \<rightarrow>\<^sub>E  ?V)"
      by (intro countable_PiE finite_Basis) (auto simp: cV)
  qed
  moreover have "(\<lambda>A. restrict A Basis) ` 
                   {A :: 'a \<Rightarrow> 'b. linear A \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)} \<subseteq>
                   {g :: 'a \<Rightarrow> 'b. (\<forall>i. i \<notin> Basis \<longrightarrow> g i = undefined) \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. g i \<bullet> j \<in> \<rat>)}"
    by (auto simp: restrict_def)
  ultimately show ?thesis
    by (metis (no_types, lifting) inj countable_image_inj_on countable_subset)
qed

lemma negligible_thin_direction:
  fixes S :: "'a::euclidean_space set"
  shows "negligible {x \<in> S. \<exists>v. v \<noteq> 0 \<and>
           (\<forall>\<xi>>0. \<exists>e>0. \<forall>y \<in> S-{x}. norm (x - y) < e \<longrightarrow> \<bar>v \<bullet> (y - x)\<bar> < \<xi> * norm (x - y))}"
  (is "negligible ?N")
proof -
    define \<Theta> where "\<Theta> \<equiv> \<lambda>x v. \<forall>\<xi>>0. \<exists>e>0. \<forall>y \<in> S-{x}. norm (x - y) < e \<longrightarrow> \<bar>v \<bullet> (y - x)\<bar> < \<xi> * norm (x - y)"
  have "?N = {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
    by (auto simp: \<Theta>_def)
  also have "negligible \<dots>"
      unfolding negligible_eq_zero_density 
    proof clarsimp
      fix x v and r e :: "real"
      assume "x \<in> S" "v \<noteq> 0" "r > 0" "e > 0"
      and Theta: "\<Theta> x v"
      moreover have "(norm v * e / 2) / DIM('a) ^ DIM('a) > 0"
        using  \<open>v \<noteq> 0\<close> \<open>e > 0\<close>
        by (auto simp add: zero_less_divide_iff zero_less_mult_iff)
      ultimately obtain d where "d > 0"
         and dless: "\<And>y. \<lbrakk>y \<in> S - {x}; norm (x - y) < d\<rbrakk> \<Longrightarrow>
                        \<bar>v \<bullet> (y - x)\<bar> < ((norm v * e / 2) / DIM('a) ^ DIM('a)) * norm (x - y)"
        by (metis \<Theta>_def)
      let ?W = "ball x (min d r) \<inter> {y. \<bar>v \<bullet> (y - x)\<bar> < (norm v * e/2 * min d r) / DIM('a) ^ DIM('a)}"
      have "open {x. \<bar>v \<bullet> (x - a)\<bar> < b}" for a b
        by (intro open_Collect_less continuous_intros)
      show "\<exists>d>0. d \<le> r \<and>
            (\<exists>U. {x' \<in> S. \<exists>v\<noteq>0. \<Theta> x' v} \<inter> ball x d \<subseteq> U \<and>
                 U \<in> lmeasurable \<and> measure lebesgue U < e * content (ball x d))"
      proof (intro exI conjI)
        show "0 < min d r" "min d r \<le> r"
          using \<open>r > 0\<close> \<open>d > 0\<close> by auto
        show "{x' \<in> S. \<exists>v. v \<noteq> 0 \<and> \<Theta> x' v} \<inter> ball x (min d r) \<subseteq> ?W"
          proof (clarsimp simp: dist_norm norm_minus_commute)
            fix y w
            assume "y \<in> S" "w \<noteq> 0"
              and d: "norm (y - x) < d" and r: "norm (y - x) < r"
            show "\<bar>v \<bullet> (y - x)\<bar> < norm v * e * min d r / (2 * real DIM('a) ^ DIM('a))"
            proof (cases "y = x")
              case True
              with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> \<open>v \<noteq> 0\<close> show ?thesis
                by (auto simp: divide_simps)
            next
              case False
              have "\<bar>v \<bullet> (y - x)\<bar> < norm v * e / 2 / real (DIM('a) ^ DIM('a)) * norm (x - y)"
                by (metis Diff_iff False \<open>y \<in> S\<close> d dless empty_iff insert_iff norm_minus_commute)
              also have "\<dots> \<le> norm v * e * min d r / (2 * real DIM('a) ^ DIM('a))"
                using d r \<open>e > 0\<close> by (simp add: divide_simps norm_minus_commute mult_left_mono)
              finally show ?thesis .
            qed
          qed
          show "?W \<in> lmeasurable"
            by (simp add: fmeasurable_Int_fmeasurable borel_open)
          obtain e_k :: 'a where ek: "e_k \<in> Basis"
            using nonempty_Basis by blast
          obtain T where T: "orthogonal_transformation T" and v: "v = T (norm v *\<^sub>R e_k)"
            using orthogonal_transformation_exists[of "norm v *\<^sub>R e_k" v] that
            by (metis abs_norm_cancel ek mult.right_neutral norm_Basis norm_scaleR)
          define b where "b \<equiv> norm v"
          have "b > 0"
            using \<open>v \<noteq> 0\<close> by (auto simp: b_def)
          have eqb: "inv T v = b *\<^sub>R e_k"
            using T v b_def orthogonal_transformation_bij bij_betw_inv_into_left
            by (metis UNIV_I orthogonal_transformation_inj inv_f_f)
          have "inj T" "bij T" and invT: "orthogonal_transformation (inv T)"
            using T orthogonal_transformation_inj orthogonal_transformation_bij orthogonal_transformation_inv
            by auto
          let ?v = "\<Sum>i\<in>Basis. (min d r / DIM('a)) *\<^sub>R i"
          let ?v' = "\<Sum>i\<in>Basis. (if i = e_k then (e/2 * min d r) / DIM('a) ^ DIM('a) else min d r) *\<^sub>R i"
          let ?x' = "inv T x"
          let ?W' = "(ball ?x' (min d r) \<inter> {y. \<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * DIM('a) ^ DIM('a))})"
          have abs: "x - e \<le> y \<and> y \<le> x + e \<longleftrightarrow> abs(y - x) \<le> e" for x y e::real
            by auto
          have "?W = T ` ?W'"
          proof -
            have 1: "T ` (ball (inv T x) (min d r)) = ball x (min d r)"
              by (simp add: T image_orthogonal_transformation_ball orthogonal_transformation_surj surj_f_inv_f)
            have 2: "{y. \<bar>v \<bullet> (y - x)\<bar> < b * e * min d r / (2 * real DIM('a) ^ DIM('a))} =
                      T ` {y. \<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * real DIM('a) ^ DIM('a))}"
            proof -
              have *: "\<bar>T (b *\<^sub>R e_k) \<bullet> (y - x)\<bar> = b * \<bar>(inv T y - ?x') \<bullet> e_k\<bar>" for y
              proof -
                have "\<bar>T (b *\<^sub>R e_k) \<bullet> (y - x)\<bar> = \<bar>(b *\<^sub>R e_k) \<bullet> inv T (y - x)\<bar>"
                  using T invT by (metis orthogonal_transformation_def eqb v b_def)
                also have "\<dots> = b * \<bar>e_k \<bullet> inv T (y - x)\<bar>"
                  using \<open>b > 0\<close> by (simp add: abs_mult)
                also have "\<dots> = b * \<bar>(inv T y - ?x') \<bullet> e_k\<bar>"
                  using orthogonal_transformation_linear [OF invT]
                  by (simp add: linear_diff inner_commute)
                finally show ?thesis
                  by simp
              qed
              show ?thesis
                using v b_def [symmetric]
                using \<open>b > 0\<close> by (simp add: * bij_image_Collect_eq [OF \<open>bij T\<close>] mult_less_cancel_left_pos times_divide_eq_right [symmetric] del: times_divide_eq_right)
            qed
            show ?thesis
              using 1 2 b_def by (simp add: image_Int [OF \<open>inj T\<close>])
          qed
          moreover have "?W' \<in> lmeasurable"
            by (auto intro: fmeasurable_Int_fmeasurable)
          moreover have "\<bar>eucl.det T\<bar> = 1"
          proof -
            note [transfer_rule] = transfer_measure_bij_rules transfer_eucl_bij_rules
            have "orthogonal_transformation f \<Longrightarrow> \<bar>eucl.det f\<bar> = 1" for f :: "'a \<Rightarrow> 'a"
              using orthogonal_transformation_det[unfolded orthogonal_transformation_def,
                where ?'n = "'a basis", untransferred]
              by (simp add: orthogonal_transformation_def)
            then show ?thesis using T by blast
          qed
          ultimately have "measure lebesgue ?W = measure lebesgue ?W'"
            using measure_orthogonal_image [OF T] by simp
          also have "\<dots> \<le> measure lebesgue (cbox (?x' - ?v') (?x' + ?v'))"
          proof (rule measure_mono_fmeasurable)
            show "?W' \<subseteq> cbox (?x' - ?v') (?x' + ?v')"
            proof (intro subsetI)
              fix y assume "y \<in> ?W'"
              then have ball: "dist ?x' y < min d r"
                and ek_bound: "\<bar>(y - ?x') \<bullet> e_k\<bar> < e * min d r / (2 * real DIM('a) ^ DIM('a))"
                by auto
              then have dist: "norm (y - ?x') < min d r"
                using ball by (simp add: dist_commute dist_norm)
              then have "\<And>i.  i \<in> Basis \<Longrightarrow> y \<bullet> i \<le> min d r + inv T x \<bullet> i"
                by (smt (verit, ccfv_SIG) Basis_le_norm dist inner_diff_left)
              then show "y \<in> cbox (?x' - ?v') (?x' + ?v')"
                using ek_bound
                apply (auto simp add: mem_box algebra_simps)
                apply (metis abs dist inner_diff_left norm_bound_Basis_le norm_minus_commute
                    order_less_imp_le)
                done
            qed
          qed auto
          also have "\<dots> \<le> e/2 * measure lebesgue (cbox (?x' - ?v) (?x' + ?v))"
          proof -
            have "cbox (?x' - ?v) (?x' + ?v) \<noteq> {}"
              using \<open>r > 0\<close> \<open>d > 0\<close> by (auto simp: box_ne_empty algebra_simps divide_less_0_iff)
            with \<open>r > 0\<close> \<open>d > 0\<close> \<open>e > 0\<close> ek show ?thesis
              apply (simp add: content_cbox_if mem_box prod_nonneg algebra_simps)
              apply (simp add: abs if_distrib prod.delta_remove field_simps power_diff split: if_split_asm)
              done
          qed
          also have "\<dots> \<le> e/2 * measure lebesgue (cball ?x' (min d r))"
          proof (rule mult_left_mono [OF measure_mono_fmeasurable])
            have *: "norm (?x' - y) \<le> min d r"
              if y: "\<And>i. i \<in> Basis \<Longrightarrow> \<bar>(?x' - y) \<bullet> i\<bar> \<le> min d r / real DIM('a)" for y
            proof -
              have "norm (?x' - y) \<le> (\<Sum>i\<in>Basis. \<bar>(?x' - y) \<bullet> i\<bar>)"
                by (rule norm_le_l1)
              also have "\<dots> \<le> real DIM('a) * (min d r / real DIM('a))"
                by (rule sum_bounded_above) (use y in auto)
              finally show ?thesis
                by simp
            qed
            show "cbox (?x' - ?v) (?x' + ?v) \<subseteq> cball ?x' (min d r)"
              apply (clarsimp simp only: mem_box dist_norm mem_cball intro!: *)
              apply (simp add: abs_diff_le_iff algebra_simps)
              done
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
  finally show ?thesis .
qed

lemma lebesgue_derivative_bound_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<in> sets lebesgue" and "linear A" and contf: "continuous_on S f"
  shows "S \<inter> (\<Inter>y\<in>S. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A(y - x)) \<le> e * norm(y - x)}) \<in> sets lebesgue"
proof (rule lebesgue_closedin [OF _ S])
  have *: "\<lbrakk>U \<noteq> {} \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)\<rbrakk>
           \<Longrightarrow> closedin (top_of_set S) (S \<inter> \<Inter> U)" for U
    by fastforce
  show "closedin (top_of_set S) (S \<inter> (\<Inter>y\<in>S. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A(y - x)) \<le> e * norm(y - x)}))"
  proof (rule *)
    let ?C = "\<lambda>y. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A(y - x)) \<le> e * norm(y - x)}"
    assume ne: "(\<lambda>y. ?C y) ` S \<noteq> {}"
    then have Sne: "S \<noteq> {}" by blast
    have sub: "(\<Inter>y\<in>S. ?C y) \<subseteq> S"
      using Sne by (auto intro: INF_lower2)
    have eq: "S \<inter> (\<Inter>y\<in>S. ?C y) = (\<Inter>y\<in>S. ?C y)"
      using sub by (rule Int_absorb1)
    show "closedin (top_of_set S) (S \<inter> (\<Inter>y\<in>S. ?C y))"
      unfolding eq
    proof (rule closedin_INT [OF Sne])
      fix y assume "y \<in> S"
      have "closedin (top_of_set S)
              ({x \<in> S. d \<le> norm (y - x)} \<union> {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)})"
      proof (intro closedin_Un)
        show "closedin (top_of_set S) {x \<in> S. d \<le> norm (y - x)}"
        proof -
          have "continuous_on S (\<lambda>x. norm (y - x))"
            by (intro continuous_on_norm continuous_on_diff continuous_on_const continuous_on_id)
          then have "closedin (top_of_set S) (S \<inter> (\<lambda>x. norm (y - x)) -` {d..})"
            by (intro continuous_closedin_preimage closed_atLeast)
          moreover have "{x \<in> S. d \<le> norm (y - x)} = S \<inter> (\<lambda>x. norm (y - x)) -` {d..}"
            by auto
          ultimately show ?thesis by simp
        qed
        show "closedin (top_of_set S) {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}"
        proof -
          have contAcomp: "continuous_on S (\<lambda>x. A (y - x))"
            by (simp add: \<open>linear A\<close> continuous_on_op_minus linear_continuous_on_compose)
          have "continuous_on S (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x))"
            by (intro continuous_intros contf contAcomp)
          then have "closedin (top_of_set S) (S \<inter> (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x)) -` {..0})"
            by (intro continuous_closedin_preimage closed_atMost)
          moreover have "{x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}
                        = S \<inter> (\<lambda>x. norm (f y - f x - A (y - x)) - e * norm (y - x)) -` {..0}"
            by auto
          ultimately show ?thesis by simp
        qed
      qed
      moreover have "?C y
                    = {x \<in> S. d \<le> norm (y - x)} \<union> {x \<in> S. norm (f y - f x - A (y - x)) \<le> e * norm (y - x)}"
        by (auto simp: not_less)
      ultimately show "closedin (top_of_set S) (?C y)"
        by simp
    qed
  qed
qed


lemma lebesgue_halfspace_derivative_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and [simp]: "u \<noteq> 0" "v \<noteq> 0" "norm u = 1" "norm v = 1"
  shows "{x \<in> S. f' x u \<bullet> v \<le> b} \<in> sets lebesgue"
proof -
  have lin: "linear (f' x)" if "x \<in> S" for x
    using f[OF that] has_derivative_linear by blast
  have contf: "continuous_on S f"
    using continuous_on_eq_continuous_within f has_derivative_continuous by blast
  show ?thesis
  proof (rule sets_negligible_symdiff)

    let ?C = "\<lambda>e A d y. {x \<in> S. norm(y - x) < d \<longrightarrow> norm(f y - f x - A (y - x)) \<le> e * norm(y - x)}"
    let ?L = "{A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>)}"
    let ?E = "{e \<in> \<rat>. (0::real) < e}"
    let ?D = "{d \<in> \<rat>. (0::real) < d}"
    let ?T = "{x \<in> S. \<forall>e>0. \<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and>
                       (\<forall>y \<in> S. x \<in> ?C e A d y)}"
    let ?U = "S \<inter> (\<Inter>e \<in> ?E. \<Union>A \<in> ?L. \<Union>d \<in> ?D. S \<inter> (\<Inter>y \<in> S. ?C e A d y))"
    have "?T = ?U"
    proof (intro set_eqI iffI ; clarsimp)
      fix s :: 'a and q :: real and r :: real
      assume "s \<in> S"
        and "\<forall>e>0. \<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and> (\<forall>y\<in>S. norm (y - s) < d \<longrightarrow> norm (f y - f s - A (y - s)) \<le> e * norm (y - s))"
        and q: "q \<in> \<rat>" "0 < q" and r: "r \<in> \<rat>" "0 < r"
      show "\<exists>xa. linear xa \<and> xa u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. xa i \<bullet> j \<in> \<rat>) \<and> (\<exists>xc. xc \<in> \<rat> \<and> 0 < xc \<and> (\<forall>xd\<in>S. norm (xd - s) < xc \<longrightarrow> norm (f xd - f s - xa (xd - s)) \<le> r * norm (xd - s)))"
      proof -
        obtain d A where linA: "linear A" and dpos: "d > 0" and Ab: "A u \<bullet> v < b" and AQ: "\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>"
          and norm: "\<forall>y\<in>S. norm (y - s) < d \<longrightarrow> norm (f y - f s - A (y - s)) \<le> r * norm (y - s)"
          using \<open>\<forall>e>0. _\<close> \<open>0 < r\<close> by blast
        obtain xc where xcQ: "xc \<in> \<rat>" and xc_close: "\<bar>xc - d/2\<bar> < d/2"
          using rational_approximation [of "d/2"] dpos by auto
        have "0 < xc" "xc < d"
          using xc_close dpos by linarith+
        then show ?thesis
          using linA Ab AQ norm xcQ by (meson order.strict_trans)
      qed
    next
      fix x :: 'a
        and e :: real
      assume "x \<in> S"
        and xif: "x \<in> (if \<forall>x. (x::real) \<in> \<rat> \<longrightarrow> \<not> 0 < x then UNIV else S \<inter> (\<Inter>x\<in>?E. \<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C x xa xb y))"
        and "0 < e"
      show "\<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and> (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> e * norm (y - x))"
      proof -
        have nif: "\<not> (\<forall>x::real. x \<in> \<rat> \<longrightarrow> \<not> 0 < x)"
          using Rats_1 zero_less_one by blast
        obtain q::real where qQ: "q \<in> \<rat>" and q0: "0 < q" and qe: "q < e"
          using \<open>0 < e\<close> Rats_dense_in_real by blast
        from xif nif
        have xmem: "x \<in> S \<inter> (\<Inter>x\<in>?E. \<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C x xa xb y)"
          by (auto split: if_splits)
        then have "x \<in> (\<Union>xa\<in>?L. \<Union>xb\<in>?D. \<Inter>y\<in>S. ?C q xa xb y)"
          using qQ q0 by blast
        then obtain A d where linA: "linear A" and Ab: "A u \<bullet> v < b" and AQ: "\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>"
          and dQ: "d \<in> \<rat>" and d0: "0 < d"
          and norm: "\<forall>y\<in>S. x \<in> S \<and> (norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> q * norm (y - x))"
          by auto
        moreover have "q * norm (y - x) \<le> e * norm (y - x)" for y
          using qe by (simp add: mult_right_mono)
        ultimately show ?thesis
          by (meson le_less order.trans)
      qed
    qed
    moreover have "?U \<in> sets lebesgue"
    proof -
      have coE: "countable ?E"
        using countable_Collect countable_rat by blast
      have ne: "?E \<noteq> {}"
        using zero_less_one Rats_1 by blast
      have coA: "countable ?L"
        by (rule countable_subset [OF _ countable_rational_linear_maps]) blast
      have sets: "S \<inter> (\<Inter>y\<in>S. ?C e A d y) \<in> sets lebesgue" if "linear A" for e A d
        using lebesgue_derivative_bound_set [OF S that contf] .

      have coD: "countable ?D"
        using countable_Collect countable_rat by blast
      show ?thesis
      proof (cases "S = {}")
        case True
        then show ?thesis by auto
      next
        case Sne: False
        show ?thesis
          unfolding INT_extend_simps if_not_P [OF ne] if_not_P [OF Sne]
          apply (intro sets.Int sets.countable_INT' [OF coE ne] image_subsetI
                       sets.countable_UN' [OF coA] sets.countable_UN' [OF coD])
          subgoal by (rule S)
          subgoal for e A d
            using sets [of A d e] Sne by auto
          done
      qed
    qed
    ultimately show "?T \<in> sets lebesgue"
      by simp
    define M where "M \<equiv> (?T - {x \<in> S. f' x u \<bullet> v \<le> b} \<union> ({x \<in> S. f' x u \<bullet> v \<le> b} - ?T))"
    define \<Theta> where "\<Theta> \<equiv> \<lambda>x v. \<forall>\<xi>>0. \<exists>e>0. \<forall>y \<in> S-{x}. norm (x - y) < e \<longrightarrow> \<bar>v \<bullet> (y - x)\<bar> < \<xi> * norm (x - y)"
    have nN: "negligible {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      using negligible_thin_direction[of S] by (simp add: \<Theta>_def)
    have *: "(\<And>x. (x \<notin> S) \<Longrightarrow> (x \<in> T \<longleftrightarrow> x \<in> U)) \<Longrightarrow> (T - U) \<union> (U - T) \<subseteq> S" for S T U :: "'a set"
      by blast
    have MN: "M \<subseteq> {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      unfolding M_def
    proof (rule *)
      fix x
      assume x: "x \<notin> {x \<in> S. \<exists>v\<noteq>0. \<Theta> x v}"
      show "(x \<in> ?T) \<longleftrightarrow> (x \<in> {x \<in> S. f' x u \<bullet> v \<le> b})"
      proof (cases "x \<in> S")
        case True
        then have x: "\<not> \<Theta> x v" if "v \<noteq> 0" for v
          using x that by force
        show ?thesis
        proof (rule iffI; clarsimp)
          assume b: "\<forall>e>0. \<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and>
                                    (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> e * norm (y - x))"
                     (is "\<forall>e>0. \<exists>d>0. \<exists>A. ?\<Phi> e d A")
          then have "\<forall>k. \<exists>d>0. \<exists>A. ?\<Phi> (1 / Suc k) d A"
            by (metis (no_types, opaque_lifting) less_Suc_eq_0_disj of_nat_0_less_iff zero_less_divide_1_iff)
          then obtain \<delta> A where \<delta>: "\<And>k. \<delta> k > 0"
                           and Ab: "\<And>k. A k u \<bullet> v < b"
                           and A: "\<And>k y. \<lbrakk>y \<in> S; norm (y - x) < \<delta> k\<rbrakk> \<Longrightarrow>
                                          norm (f y - f x - A k (y - x)) \<le> 1/(Suc k) * norm (y - x)"
                           and linA: "\<And>k. linear (A k)"
            by metis
          have "\<forall>i j. \<exists>a. (\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> a"
          proof (intro allI)
            fix i j
            let ?CA = "{x. Cauchy (\<lambda>n. A n x)}"
            have "\<exists>l. (\<lambda>n. A n 0) \<longlonglongrightarrow> l"
              using A True \<delta> by fastforce
            moreover have "\<exists>l. (\<lambda>n. A n (x + y)) \<longlonglongrightarrow> l" 
              if "(\<lambda>n. A n x) \<longlonglongrightarrow> l" and "(\<lambda>n. A n y) \<longlonglongrightarrow> l'"
              for x :: 'a and l :: 'b and y :: 'a and l' :: 'b
              using that linA   
              by (intro exI [where x="l+l'"]) (simp add: Real_Vector_Spaces.linear_iff tendsto_add)
            moreover have "\<exists>l. (\<lambda>n. A n (c *\<^sub>R x)) \<longlonglongrightarrow> l"
              if "(\<lambda>n. A n x) \<longlonglongrightarrow> l"
              for c :: real and x :: 'a and l :: 'b
              using that linA
              by (intro exI [where x="c *\<^sub>R l"]) (simp add: Real_Vector_Spaces.linear_iff tendsto_scaleR)
            ultimately have "subspace ?CA"
              by (auto simp: subspace_def convergent_eq_Cauchy [symmetric])
            then have CA_eq: "?CA = span ?CA"
              by (metis span_eq_iff)
            also have "\<dots> = UNIV"
            proof -
              have "dim ?CA \<le> DIM('a)"
                using dim_subset_UNIV[of ?CA] by auto
              moreover have "False" if less: "dim ?CA < DIM('a)"
              proof -
                obtain d where "d \<noteq> 0" and d: "\<And>y. y \<in> span ?CA \<Longrightarrow> orthogonal d y"
                  using less by (force intro: orthogonal_to_subspace_exists [of ?CA])
                with x [OF \<open>d \<noteq> 0\<close>] obtain \<xi> where "\<xi> > 0"
                  and \<xi>: "\<And>e. e > 0 \<Longrightarrow> \<exists>y \<in> S - {x}. norm (x - y) < e \<and> \<xi> * norm (x - y) \<le> \<bar>d \<bullet> (y - x)\<bar>"
                  by (metis \<Theta>_def linorder_not_less)
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
                    using compact_sphere [of "0" 1]  unfolding compact_def by meson
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
                have "Cauchy (\<lambda>n. A n z)"
                proof (clarsimp simp add: Cauchy_def)
                  fix \<epsilon> :: "real"
                  assume "0 < \<epsilon>"
                  then obtain N::nat where "N > 0" and N: "\<epsilon>/2 > 1/N"
                    by (metis half_gt_zero inverse_eq_divide neq0_conv real_arch_inverse)
                  show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (A m z) (A n z) < \<epsilon>"
                  proof (intro exI allI impI)
                    fix i j
                    assume ij: "N \<le> i" "N \<le> j"
                    let ?V = "\<lambda>i k. A i ((\<gamma> k - x) /\<^sub>R norm (\<gamma> k - x))"
                    have "\<forall>\<^sub>F k in sequentially. dist (\<gamma> k) x < min (\<delta> i) (\<delta> j)"
                      using \<gamma>x [unfolded tendsto_iff] by (meson min_less_iff_conj \<delta>)
                    then have even: "\<forall>\<^sub>F k in sequentially. norm (?V i k - ?V j k) - 2 / N \<le> 0"
                    proof (rule eventually_mono, clarsimp)
                      fix p
                      assume p: "dist (\<gamma> p) x < \<delta> i" "dist (\<gamma> p) x < \<delta> j"
                      define g where "g \<equiv> \<lambda>k. f (\<gamma> p) - f x - A k (\<gamma> p - x)"
                      have "norm ((A i - A j) (\<gamma> p - x)) = norm (g j - g i)"
                        by (simp add: g_def algebra_simps)
                      also have "\<dots> \<le> norm (g j) + norm (g i)"
                        using norm_triangle_ineq4 by blast
                      also have "\<dots> \<le> 1/(Suc j) * norm (\<gamma> p - x) + 1/(Suc i) * norm (\<gamma> p - x)"
                        by (metis g_def A Diff_iff \<gamma>Sx dist_norm p add_mono)
                      also have "\<dots> \<le> 1/N * norm (\<gamma> p - x) + 1/N * norm (\<gamma> p - x)"
                        using ij \<open>N > 0\<close> by (intro add_mono mult_right_mono) (auto simp: field_simps)
                      also have "\<dots> = 2 / N * norm (\<gamma> p - x)"
                        by simp
                      finally have no_le: "norm ((A i - A j) (\<gamma> p - x)) \<le> 2 / N * norm (\<gamma> p - x)" .
                      have "norm (?V i p - ?V j p) =
                            norm ((A i - A j) ((\<gamma> p - x) /\<^sub>R norm (\<gamma> p - x)))"
                        by (simp add: algebra_simps)
                      also have "\<dots> = norm ((A i - A j) (\<gamma> p - x)) / norm (\<gamma> p - x)"
                        using linA[of i] linA[of j] norm_scaleR real_norm_def divide_inverse norm_inverse
                        by (smt (verit, del_insts) Real_Vector_Spaces.linear_iff abs_norm_cancel fun_diff_def
                            mult.commute scaleR_right_diff_distrib)
                      also have "\<dots> \<le> 2 / N"
                        using no_le by (auto simp: field_split_simps)
                      finally show "norm (?V i p - ?V j p) \<le> 2 / N" .
                    qed
                    have "isCont (\<lambda>w. (norm(A i w - A j w) - 2 / N)) z"
                      by (simp add: continuous_intros linA linear_continuous_within linear_linear)
                    from isCont_tendsto_compose [OF this z]
                    have lim: "(\<lambda>w. norm (A i ((\<gamma> w - x) /\<^sub>R norm (\<gamma> w - x)) -
                                    A j ((\<gamma> w - x) /\<^sub>R norm (\<gamma> w - x))) - 2 / N)
                               \<longlonglongrightarrow> norm (A i z - A j z) - 2 / N"
                      by auto
                    have "dist (A i z) (A j z) \<le> 2 / N"
                      using tendsto_upperbound [OF lim even] by (auto simp: dist_norm)
                    with N show "dist (A i z) (A j z) < \<epsilon>"
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
            finally have CA: "?CA = UNIV" .
            then have "Cauchy (\<lambda>n. A n i)"
              by auto
            then obtain L where "(\<lambda>n. A n i) \<longlonglongrightarrow> L"
              by (auto simp: Cauchy_convergent_iff convergent_def)
            then have "(\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> L \<bullet> j"
              by (intro tendsto_intros)
            then show "\<exists>a. (\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> a"
              by blast
          qed
          \<comment> \<open>Construct the limit operator B as pointwise limit\<close>
          have conv: "convergent (\<lambda>n. A n i)" for i
          proof -
            have "\<forall>j. \<exists>a. (\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> a"
              using \<open>\<forall>i j. \<exists>a. (\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> a\<close> by blast
            then obtain a where a: "\<And>j. (\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> a j"
              by metis
            have "(\<lambda>n. \<Sum>j\<in>Basis. (A n i \<bullet> j) *\<^sub>R j) \<longlonglongrightarrow> (\<Sum>j\<in>Basis. a j *\<^sub>R j)"
              by (intro tendsto_intros a)
            moreover have "A n i = (\<Sum>j\<in>Basis. (A n i \<bullet> j) *\<^sub>R j)" for n
              by (rule euclidean_representation [symmetric])
            ultimately have "(\<lambda>n. A n i) \<longlonglongrightarrow> (\<Sum>j\<in>Basis. a j *\<^sub>R j)"
              by simp
            then show ?thesis
              by (auto simp: convergent_def)
          qed
          define B where "B \<equiv> \<lambda>i. lim (\<lambda>n. A n i)"
          have Blim: "(\<lambda>n. A n i) \<longlonglongrightarrow> B i" for i
            using conv unfolding B_def by (simp add: convergent_LIMSEQ_iff)
          have linB: "linear B"
            unfolding Real_Vector_Spaces.linear_iff
          proof (intro conjI allI)
            fix x y
            have "(\<lambda>n. A n (x + y)) \<longlonglongrightarrow> B (x + y)" by (rule Blim)
            moreover have "(\<lambda>n. A n x + A n y) \<longlonglongrightarrow> B x + B y"
              by (intro tendsto_intros Blim)
            moreover have "A n (x + y) = A n x + A n y" for n
              using linA[of n] by (simp add: Real_Vector_Spaces.linear_iff)
            ultimately show "B (x + y) = B x + B y"
              by (simp add: LIMSEQ_unique)
          next
            fix c x
            have "(\<lambda>n. A n (c *\<^sub>R x)) \<longlonglongrightarrow> B (c *\<^sub>R x)" by (rule Blim)
            moreover have "(\<lambda>n. c *\<^sub>R A n x) \<longlonglongrightarrow> c *\<^sub>R B x"
              by (intro tendsto_intros Blim)
            moreover have "A n (c *\<^sub>R x) = c *\<^sub>R A n x" for n
              using linA[of n] by (simp add: Real_Vector_Spaces.linear_iff)
            ultimately show "B (c *\<^sub>R x) = c *\<^sub>R B x"
              by (simp add: LIMSEQ_unique)
          qed
          have B: "(\<lambda>n. A n i \<bullet> j) \<longlonglongrightarrow> B i \<bullet> j" for i j
            using Blim[of i] by (intro tendsto_intros)
          have lin_df: "linear (f' x)"
               and lim_df: "((\<lambda>y. (1 / norm (y - x)) *\<^sub>R (f y - (f x + f' x (y - x)))) \<longlongrightarrow> 0) (at x within S)"
            using \<open>x \<in> S\<close> f by (auto simp: has_derivative_within linear_linear)
          moreover
          interpret linear "f' x" by fact
          have "(f' x - B) w = 0" for w
          proof (rule lemma_partial_derivatives [of "f' x - B"])
            show "linear (f' x - B)"
              by (simp add: linB fun_diff_def linear_axioms linear_compose_sub)
            have "((\<lambda>y. ((f x + f' x (y - x)) - f y) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
              using tendsto_minus [OF lim_df] by (simp add: field_split_simps)
            then show "((\<lambda>y. (f' x - B) (y - x) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within S)"
            proof (rule Lim_transform)
              have "((\<lambda>y. ((f y + B x - (f x + B y)) /\<^sub>R norm (y - x))) \<longlongrightarrow> 0) (at x within S)"
              proof (clarsimp simp add: Lim_within dist_norm)
                fix e :: "real"
                assume "e > 0"
                then obtain q::nat where "q \<noteq> 0" and qe2: "1/q < e/2"
                  by (metis divide_pos_pos inverse_eq_divide real_arch_inverse zero_less_numeral)
                let ?g = "\<lambda>p. sum (\<lambda>i. sum (\<lambda>j. abs((A p - B) i \<bullet> j)) (Basis :: 'b set)) (Basis :: 'a set)"
                have blAB: "bounded_linear (A k - B)" for k
                  using linA linB by (simp add: linear_conv_bounded_linear fun_diff_def bounded_linear_sub)
                have "(\<lambda>k. onorm (A k - B)) \<longlonglongrightarrow> 0"
                proof (rule Lim_null_comparison)
                  show "\<forall>\<^sub>F k in sequentially. norm (onorm (A k - B)) \<le> ?g k"
                  proof (rule eventually_sequentiallyI)
                    fix k :: "nat"
                    assume "0 \<le> k"
                    have "0 \<le> onorm (A k - B)"
                      using blAB by (rule onorm_pos_le)
                    moreover have "onorm (A k - B) \<le> (\<Sum>i\<in>(Basis :: 'a set). \<Sum>j\<in>(Basis :: 'b set). \<bar>(A k - B) i \<bullet> j\<bar>)"
                    proof (rule onorm_componentwise_le [OF blAB])
                      show "(\<Sum>i\<in>Basis. norm ((A k - B) i)) \<le> (\<Sum>i\<in>(Basis :: 'a set). \<Sum>j\<in>(Basis :: 'b set). \<bar>(A k - B) i \<bullet> j\<bar>)"
                        by (rule sum_mono [OF norm_le_l1])
                    qed
                    ultimately show "norm (onorm (A k - B)) \<le> (\<Sum>i\<in>(Basis :: 'a set). \<Sum>j\<in>(Basis :: 'b set). \<bar>(A k - B) i \<bullet> j\<bar>)"
                      by simp
                  qed
                next
                  show "?g \<longlonglongrightarrow> 0"
                  proof (rule tendsto_null_sum)
                    fix i :: 'a
                    assume "i \<in> Basis"
                    show "(\<lambda>p. \<Sum>j\<in>(Basis :: 'b set). \<bar>(A p - B) i \<bullet> j\<bar>) \<longlonglongrightarrow> 0"
                    proof (rule tendsto_null_sum)
                      fix j :: 'b
                      assume "j \<in> Basis"
                      have "(\<lambda>n. A n i \<bullet> j - B i \<bullet> j) \<longlonglongrightarrow> 0"
                        using B Lim_null by fastforce
                      moreover have "(A p - B) i \<bullet> j = A p i \<bullet> j - B i \<bullet> j" for p
                        by (simp add: inner_diff_left)
                      ultimately show "(\<lambda>p. \<bar>(A p - B) i \<bullet> j\<bar>) \<longlonglongrightarrow> 0"
                        using tendsto_rabs_zero_iff by force
                    qed
                  qed
                qed
                with \<open>e > 0\<close> obtain p where "\<And>n. n \<ge> p \<Longrightarrow> \<bar>onorm (A n - B)\<bar> < e/2"
                  unfolding lim_sequentially by (metis diff_zero dist_real_def divide_pos_pos zero_less_numeral)
                then have pqe2: "\<bar>onorm (A (p + q) - B)\<bar> < e/2"
                  using le_add1 by blast
                show "\<exists>d>0. \<forall>y\<in>S. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow>
                           inverse (norm (y - x)) * norm (f y + B x - (f x + B y)) < e"
                proof (intro exI, safe)
                  show "0 < \<delta>(p + q)"
                    by (simp add: \<delta>)
                next
                  fix y
                  assume y: "y \<in> S" "norm (y - x) < \<delta>(p + q)" and "y \<noteq> x"
                  have *: "\<lbrakk>norm(b - c) < e - d; norm(y - x - b) \<le> d\<rbrakk> \<Longrightarrow> norm(y - x - c) < e"
                    for b c d e x and y:: "'b"
                    using norm_triangle_ineq2 [of "y - x - c" "y - x - b"] by simp
                  have "norm (f y - f x - B (y - x)) < e * norm (y - x)"
                  proof (rule *)
                    show "norm (f y - f x - A (p + q) (y - x)) \<le> norm (y - x) / (Suc (p + q))"
                      using A [OF y] by simp
                    have "norm (A (p + q) (y - x) - B (y - x)) \<le> onorm (A (p + q) - B) * norm(y - x)"
                    proof -
                      have "A (p + q) (y - x) - B (y - x) = (A (p + q) - B) (y - x)"
                        by simp
                      then show ?thesis
                        using onorm [OF blAB] by simp
                    qed
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
                    finally show "norm (A (p + q) (y - x) - B (y - x)) < e * norm (y - x) - norm (y - x) / real (Suc (p + q))"
                      by (simp add: algebra_simps)
                  qed
                  then show "inverse (norm (y - x)) * norm (f y + B x - (f x + B y)) < e"
                    using \<open>y \<noteq> x\<close> linear_diff [OF linB]
                    by (simp add: field_split_simps algebra_simps)
                qed
              qed
              then show "((\<lambda>y. (f' x - B) (y - x) /\<^sub>R
                           norm (y - x) - (f x + f' x (y - x) - f y) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0)
                          (at x within S)"
                by (simp add: algebra_simps diff linear_diff [OF linB] lin_df)
            qed
            show "\<And>v. v \<noteq> 0 \<Longrightarrow>
                \<exists>k>0. \<forall>e>0. \<exists>xa\<in>S - {x}. norm (x - xa) < e \<and> k * norm (x - xa) \<le> \<bar>v \<bullet> (xa - x)\<bar>"
              using x by (metis \<Theta>_def linorder_not_le)
          qed 
          ultimately have "f' x = B"
            by (force simp: algebra_simps)

          show "f' x u \<bullet> v \<le> b"
          proof (rule tendsto_upperbound [of "\<lambda>i. (A i u \<bullet> v)" _ sequentially])
            show "(\<lambda>i. A i u \<bullet> v) \<longlonglongrightarrow> f' x u \<bullet> v"
              by (simp add: B \<open>f' x = B\<close>)
            show "\<forall>\<^sub>F i in sequentially. A i u \<bullet> v \<le> b"
              by (simp add: Ab less_eq_real_def)
          qed auto
        next
          fix e :: "real"
          assume "x \<in> S" and b: "f' x u \<bullet> v \<le> b" and "e > 0"
          then obtain d where "d>0"
            and d: "\<And>y. y\<in>S \<Longrightarrow> 0 < dist y x \<and> dist y x < d \<longrightarrow> norm (f y - f x - f' x (y - x)) / (norm (y - x))
                  < e/2"
            using f [OF \<open>x \<in> S\<close>]
            by (simp add: Deriv.has_derivative_at_within Lim_within)
              (auto simp add: field_simps dest: spec [of _ "e/2"])
          \<comment> \<open>Rank-1 perturbation\<close>
          define P where "P \<equiv> \<lambda>w::'a. ((e / (4 * (u \<bullet> u) * (v \<bullet> v))) * (w \<bullet> u)) *\<^sub>R (v::'b)"
          have linP: "linear P"
            unfolding P_def by (intro linearI) (auto simp: inner_left_distrib scaleR_add_left scaleR_left_distrib algebra_simps add_divide_distrib)

          have Puv: "P u \<bullet> v = e / 4"
          proof -
            have "u \<bullet> u > 0" and "v \<bullet> v > 0"
              by (simp_all add: inner_gt_zero_iff)
            then show ?thesis
              unfolding P_def by (simp add: power2_eq_square)
          qed
          have onormP: "onorm P \<le> e / 4"
          proof (rule onorm_bound)
            fix w :: 'a
            have "norm (P w) = \<bar>e / (4 * (u \<bullet> u) * (v \<bullet> v))\<bar> * \<bar>w \<bullet> u\<bar> * norm v"
              unfolding P_def by (simp add: norm_scaleR abs_mult)
            also have "\<dots> = e / 4 * \<bar>w \<bullet> u\<bar>"
              using \<open>e > 0\<close> by (simp add: dot_square_norm power2_eq_square)
            also have "\<dots> \<le> e / 4 * norm w"
              using \<open>e > 0\<close> Cauchy_Schwarz_ineq2 [of w u]
              by (intro mult_left_mono) auto
            finally show "norm (P w) \<le> e / 4 * norm w" .
          next
            show "0 \<le> e / 4" using \<open>e > 0\<close> by simp
          qed
          let ?A = "f' x - P"
          have linf': "linear (f' x)"
            using lin \<open>x \<in> S\<close> by blast
          have blf': "bounded_linear (f' x)"
            using linf' linear_conv_bounded_linear by blast
          have blP: "bounded_linear P"
            using linP linear_conv_bounded_linear by blast
          have linA': "linear ?A"
            by (simp add: fun_diff_def linP linear_compose_sub linf')
          \<comment> \<open>Rational approximation of linear maps\<close>
          obtain B where linB: "linear B"
                     and BRats: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> B i \<bullet> j \<in> \<rat>"
                     and Bo_e6: "onorm (?A - B) < e/6"
            by (metis \<open>0 < e\<close> divide_pos_pos linA' linear_rational_approximation
                zero_less_numeral)
          show "\<exists>d>0. \<exists>A. linear A \<and> A u \<bullet> v < b \<and> (\<forall>i\<in>Basis. \<forall>j\<in>Basis. A i \<bullet> j \<in> \<rat>) \<and>
                (\<forall>y\<in>S. norm (y - x) < d \<longrightarrow> norm (f y - f x - A (y - x)) \<le> e * norm (y - x))"
          proof (intro exI conjI ballI impI)
            show "d>0"
              by (rule \<open>d>0\<close>)
            show "linear B"
              by (rule linB)
            show "B u \<bullet> v < b"
            proof -
              have "\<bar>(?A - B) u \<bullet> v\<bar> \<le> onorm (?A - B) * norm u * norm v"
              proof -
                have bl: "bounded_linear (?A - B)"
                  using linA' linB
                  by (metis (no_types, lifting) ext linear_compose_sub linear_linear minus_apply)
                have "\<bar>(?A - B) u \<bullet> v\<bar> \<le> norm ((?A - B) u) * norm v"
                  by (rule Cauchy_Schwarz_ineq2)
                also have "\<dots> \<le> onorm (?A - B) * norm u * norm v"
                  using onorm [OF bl, of u] by (intro mult_right_mono) auto
                finally show ?thesis .
              qed
              also have "\<dots> < e/6 * norm u * norm v"
                using Bo_e6 by simp

              finally have *: "\<bar>(?A - B) u \<bullet> v\<bar> < e/6 * norm u * norm v" .
              have "B u \<bullet> v \<le> ?A u \<bullet> v + e/6 * norm u * norm v"
                by (smt (verit) "*" fun_diff_def inner_diff_left)
              also have "?A u \<bullet> v = f' x u \<bullet> v - P u \<bullet> v"
                by (simp add: inner_diff_left)
              also have "\<dots> = f' x u \<bullet> v - e/4"
                by (simp add: Puv)
              finally have "B u \<bullet> v \<le> f' x u \<bullet> v - e / 12"
                by simp
              then show "B u \<bullet> v < b"
                using b \<open>e > 0\<close> by linarith
            qed
            show "B i \<bullet> j \<in> \<rat>" if "i \<in> Basis" "j \<in> Basis" for i j
              using BRats that by auto
            show "norm (f y - f x - B (y - x)) \<le> e * norm (y - x)"
              if "y \<in> S" and y: "norm (y - x) < d" for y
            proof (cases "y = x")
              case True then show ?thesis
                using linB linear_0 by simp
            next
              case False
              have *: "norm(d' - d) \<le> e/2 \<Longrightarrow> norm(y - (x + d')) < e/2 \<Longrightarrow> norm(y - x - d) \<le> e" for d d' e and x y::"'b"
                using norm_triangle_le [of "d' - d" "y - (x + d')"] by simp
              show ?thesis
              proof (rule *)
                have split246: "\<lbrakk>norm y \<le> e / 6; norm(x - y) \<le> e / 4\<rbrakk> \<Longrightarrow> norm x \<le> e/2" if "e > 0" for e and x y :: "'b"
                  using norm_triangle_le [of y "x-y" "e/2"] \<open>e > 0\<close> by simp
                \<comment> \<open>linf' already in scope from above\<close>
                have "norm (f' x (y - x) - B (y - x)) = norm ((f' x - B) (y - x))"
                  by (simp add: linear_diff [OF linf'] linear_diff [OF linB])
                also have "\<dots> \<le> (e * norm (y - x)) / 2"
                proof (rule split246)
                  \<comment> \<open>First bound: (?A - B) part\<close>
                  have blAB: "bounded_linear (\<lambda>w. ?A w - B w)"
                    using linA' linB
                    using bounded_linear_sub linear_linear by blast
                  have "norm ((?A - B) (y - x)) / norm (y - x) \<le> onorm (?A - B)"
                  proof (rule le_onorm)
                    show "bounded_linear (?A - B)"
                      using linA' linB
                      by (metis (no_types, lifting) ext blAB fun_diff_def)
                  qed
                  also have "\<dots> < e/6"
                    by (rule Bo_e6)
                  finally have "norm ((?A - B) (y - x)) / norm (y - x) < e / 6" .
                  then show onAB: "norm ((?A - B) (y - x)) \<le> e * norm (y - x) / 6"
                    by (simp add: field_split_simps False)
                  \<comment> \<open>Second bound: P part (the perturbation)\<close>
                  have "(f' x - B) (y - x) - (?A - B) (y - x) = P (y - x)"
                    by (simp add: algebra_simps)
                  then have "norm ((f' x - B) (y - x) - (?A - B) (y - x)) = norm (P (y - x))"
                    by simp
                  also have "\<dots> \<le> onorm P * norm (y - x)"
                    using linP linear_conv_bounded_linear onorm by blast
                  also have "\<dots> \<le> (e/4) * norm (y - x)"
                    using onormP by (intro mult_right_mono) auto
                  finally show "norm ((f' x - B) (y - x) - (?A - B) (y - x)) \<le> e * norm (y - x) / 4"
                    by simp
                  show "0 < e * norm (y - x)"
                    by (simp add: False \<open>e > 0\<close>)
                qed
                finally show "norm (f' x (y - x) - B (y - x)) \<le> (e * norm (y - x)) / 2" .
                show "norm (f y - (f x + f' x (y - x))) < (e * norm (y - x)) / 2"
                  using False d [OF \<open>y \<in> S\<close>] y by (simp add: dist_norm field_simps)
              qed
            qed
          qed
        qed
      qed auto
    qed
    show "negligible M"
      using negligible_subset [OF nN MN] .
  qed
qed

proposition borel_measurable_partial_derivatives:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and uB: "u \<in> Basis" and vB: "v \<in> Basis"
  shows "(\<lambda>x. f' x u \<bullet> v) \<in> borel_measurable (lebesgue_on S)"
proof -
  have "{x \<in> S. f' x u \<bullet> v \<le> b} \<in> sets lebesgue" for b
    by (rule lebesgue_halfspace_derivative_le [OF S f]) (use uB vB in \<open>auto simp: norm_Basis\<close>)
  then show ?thesis
    by (simp add: borel_measurable_vimage_halfspace_component_le sets_restrict_space_iff S)
qed

theorem borel_measurable_det_Jacobian:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue" and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. eucl.det (f' x)) \<in> borel_measurable (lebesgue_on S)"
  unfolding eucl_det_def
  by (intro borel_measurable_sum borel_measurable_prod borel_measurable_times
            borel_measurable_const borel_measurable_partial_derivatives [OF S])
     (auto intro: f elim: permutes_in_funpow_image[where n=1, simplified] simp: permutes_image [symmetric])

text\<open>The localisation wrt S uses the same argument for many similar results.\<close>
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
  by (metis assms negligible_iff_null_sets negligible_subset null_sets_completionI sets_completionE sets_lborel)

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
    using sets_lebesgue_almost_borel by metis
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
  fixes P :: "'a::euclidean_space set"
  assumes "a \<noteq> 0"
    and P: "P \<subseteq> {x. a \<bullet> x = 0}" and "0 \<le> m" "0 \<le> e"
  obtains S where "S \<in> lmeasurable"
    and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
proof -
  obtain i :: 'a where i: "i \<in> Basis"
    using nonempty_Basis by blast
  have ni: "norm (norm a *\<^sub>R i) = norm a"
    using norm_Basis[OF i] by simp
  then obtain T where T: "orthogonal_transformation T" and a: "T (norm a *\<^sub>R i) = a"
    using orthogonal_transformation_exists by metis
  have Tinv [simp]: "T (inv T x) = x" for x
    by (simp add: T orthogonal_transformation_surj surj_f_inv_f)
  obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> T-`P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
  proof (rule Sard_lemma00 [of "norm a" i "T-`P" m e])
    have "norm a *\<^sub>R i \<bullet> x = 0" if "T x \<in> P" for x
    proof -
      have "norm a *\<^sub>R i \<bullet> x = T (norm a *\<^sub>R i) \<bullet> T x"
        using T by (simp add: orthogonal_transformation_def)
      also have "\<dots> = a \<bullet> T x"
        by (simp add: a)
      also have "\<dots> = 0"
        using P that by auto
      finally show ?thesis .
    qed
    then show "T -` P \<subseteq> {x. norm a *\<^sub>R i \<bullet> x = 0}"
      by auto
  qed (use assms T i in auto)
  show thesis
  proof
    show "T ` S \<in> lmeasurable"
      using S measurable_orthogonal_image T by blast
    have "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
    proof clarsimp
      fix x t
      assume \<section>: "norm x \<le> m" "t \<in> P" "norm (x - t) \<le> e"
      then have "norm (inv T x) \<le> m"
        using orthogonal_transformation_inv [OF T] by (simp add: orthogonal_transformation_norm)
      moreover have "\<exists>t\<in>T -` P. norm (inv T x - t) \<le> e"
      proof -
        have "inv T t \<in> T -` P"
          using \<open>t \<in> P\<close> by (simp add: vimage_def)
        moreover have "norm (inv T x - inv T t) \<le> e"
        proof -
          have "inv T x - inv T t = inv T (x - t)"
            using orthogonal_transformation_inv [OF T]
            by (simp add: linear_diff orthogonal_transformation_linear)
          also have "norm \<dots> = norm (x - t)"
            using orthogonal_transformation_inv [OF T] by (simp add: orthogonal_transformation_norm)
          finally show ?thesis
            using \<section>(3) by simp
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show "x \<in> T ` {z. norm z \<le> m \<and> (\<exists>t\<in>T -` P. norm (z - t) \<le> e)}"
        by force
    qed
    then show "{z. norm z \<le> m \<and> (\<exists>t\<in>P. norm (z - t) \<le> e)} \<subseteq> T ` S"
      using image_mono [OF subS] by (rule order_trans)
    show "measure lebesgue (T ` S) \<le> 2 * e * (2 * m) ^ (DIM('a) - 1)"
    proof -
      have linT: "linear T" and linTi: "linear (inv T)"
        using T orthogonal_transformation_inv [OF T]
        by (auto simp: orthogonal_transformation_linear)
      have "T \<circ> inv T = id"
        using T orthogonal_transformation_surj surj_f_inv_f by fastforce
      then have "eucl.det T * eucl.det (inv T) = 1"
        using eucl.det_compose [OF linT linTi] by simp
      have "\<bar>eucl.det T\<bar> = 1"
      proof -
        note [transfer_rule] = transfer_measure_bij_rules transfer_eucl_bij_rules
        have "orthogonal_transformation f \<Longrightarrow> \<bar>eucl.det f\<bar> = 1" for f :: "'a \<Rightarrow> 'a"
          using orthogonal_transformation_det[unfolded orthogonal_transformation_def,
            where ?'n = "'a basis", untransferred]
          by (simp add: orthogonal_transformation_def)
        then show ?thesis using T by blast
      qed
      then have "measure lebesgue (T ` S) = measure lebesgue S"
        using measure_orthogonal_image [OF T S] by simp
      then show ?thesis using mS by simp
    qed
  qed
qed


text\<open>As above, but translating the sets (HOL Light's @text{GEN\_GEOM\_ORIGIN\_TAC})\<close>
lemma Sard_lemma1:
  fixes P :: "'a::euclidean_space set"
   assumes P: "dim P < DIM('a)" and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm(z - w) \<le> m \<and> (\<exists>t \<in> P. norm(z - w - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
proof -
  obtain a where "a \<noteq> 0" "P \<subseteq> {x. a \<bullet> x = 0}"
    using lowdim_subset_hyperplane [of P] P span_base by auto
  then obtain S where S: "S \<in> lmeasurable"
    and subS: "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and mS: "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('a) - 1)"
    by (rule Sard_lemma0 [OF _ _ \<open>0 \<le> m\<close> \<open>0 \<le> e\<close>])
  show thesis
  proof
    show "(+)w ` S \<in> lmeasurable"
      by (metis measurable_translation S)
    show "{z. norm (z - w) \<le> m \<and> (\<exists>t\<in>P. norm (z - w - t) \<le> e)} \<subseteq> (+)w ` S"
      using subS by force
    show "measure lebesgue ((+)w ` S) \<le> 2 * e * (2 * m) ^ (DIM('a) - 1)"
      by (metis measure_translation mS)
  qed
qed

lemma Sard_lemma2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes mlen: "DIM('a) \<le> DIM('b)" (is "?m \<le> ?n")
    and "B > 0" "bounded S"
    and derS: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> dim (f' x ` UNIV) < DIM('b)"
    and B: "\<And>x. x \<in> S \<Longrightarrow> onorm(f' x) \<le> B"
  shows "negligible(f ` S)"
proof -
  have lin_f': "\<And>x. x \<in> S \<Longrightarrow> linear(f' x)"
    using derS has_derivative_linear by blast
  show ?thesis
  proof (clarsimp simp add: negligible_outer_le)
    fix e :: "real"
    assume "e > 0"
      obtain b where b: "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> b"
        using \<open>bounded S\<close> by (auto simp: bounded_iff)
    let ?One = "\<Sum>i\<in>Basis. i :: 'a"  
    obtain c where csub: "S \<subseteq> cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One)" and "c > 0"
      proof
      show "S \<subseteq> cbox (- (\<bar>b\<bar> + 1) *\<^sub>R ?One) ((\<bar>b\<bar> + 1) *\<^sub>R ?One)"
        using norm_bound_Basis_le b
        by (fastforce simp: mem_box inner_sum_right inner_Basis)
      qed auto
    then have box_cc: "box (- c *\<^sub>R ?One) (c *\<^sub>R ?One) \<noteq> {}" and cbox_cc: "cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One) \<noteq> {}"
      using \<open>c > 0\<close> by (auto simp: box_ne_empty inner_sum_right inner_Basis)
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
    obtain \<D> where \<D>: "countable \<D>" and sub_cc: "\<Union>\<D> \<subseteq> cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One)"
      and cbox: "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>u v. K = cbox u v)"
      and djointish: "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
      and covered: "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> ball x (r x)"
      and close: "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i\<in>Basis. v \<bullet> i - u \<bullet> i = 2*c / 2^n"
      and covers: "S \<subseteq> \<Union>\<D>"
      apply (rule covering_lemma [OF csub box_cc ga])
      apply (simp add: inner_sum_right inner_Basis)
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
        by (simp add: rank)
      then obtain T where T: "T \<in> lmeasurable"
            and subT: "{z. norm(z - f x) \<le> (2 * B) * norm(v - u) \<and> (\<exists>t \<in> range (f' x). norm(z - f x - t) \<le> d * norm(v - u))} \<subseteq> T"
            and measT: "?\<mu> T \<le> (2 * (d * norm(v - u))) * (2 * ((2 * B) * norm(v - u))) ^ (?n - 1)"
                        (is "_ \<le> ?DVU")
        using Sard_lemma1 [of "range (f' x)" "(2 * B) * norm(v - u)" "d * norm(v - u)"]
        using \<open>B > 0\<close> \<open>d > 0\<close> by auto
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
          proof -
            have comp: "\<bar>(y - x) \<bullet> b\<bar> \<le> \<bar>(v - u) \<bullet> b\<bar>" if "b \<in> Basis" for b
            proof -
              have "u \<bullet> b \<le> y \<bullet> b" "y \<bullet> b \<le> v \<bullet> b" "u \<bullet> b \<le> x \<bullet> b" "x \<bullet> b \<le> v \<bullet> b"
                using x y that by (auto simp: mem_box)
              then show ?thesis
                by (simp add: inner_diff_left abs_le_iff) 
            qed
            have "(y - x) \<bullet> (y - x) \<le> (v - u) \<bullet> (v - u)"
              using comp norm_le norm_le_componentwise by blast
            then show ?thesis
              by (simp add: norm_eq_sqrt_inner real_sqrt_le_iff)
          qed
          have *: "\<lbrakk>norm(y - x - z) \<le> d; norm z \<le> B; d \<le> B\<rbrakk> \<Longrightarrow> norm(y - x) \<le> 2 * B"
            for x y z :: 'b and d B
            using norm_triangle_ineq2 [of "y - x" z] by auto
          show "norm (f y - f x) \<le> 2 * (B * norm (v - u))"
          proof (rule * [OF le_dyx])
            have "norm (f' x (y - x)) \<le> onorm (f' x) * norm (y - x)"
              using onorm [of "f' x" "y-x"] by (meson IntE lin_f' linear_linear x(1))
            also have "\<dots> \<le> B * norm (v - u)"
              by (meson B IntE lin_f' linear_linear mult_mono' norm_ge_zero onorm_pos_le x(1) yx_le)
            finally show "norm (f' x (y - x)) \<le> B * norm (v - u)" .
            show "d * norm (y - x) \<le> B * norm (v - u)"
              using \<open>B > 0\<close> by (auto intro: mult_mono [OF \<open>d \<le> B\<close> yx_le])
          qed
          show "\<exists>t. norm (f y - f x - f' x t) \<le> d * norm (v - u)"
            by (smt (verit, best) \<open>0 < d\<close> le_dyx mult_le_cancel_left_pos yx_le)
        qed
        with subT show "f ` (K \<inter> S) \<subseteq> T" by blast
        show "?\<mu> T \<le> e / (2*c) ^ ?m * ?\<mu> K"
        proof (rule order_trans [OF measT])
          have "?DVU = (d * 2 * (4 * B) ^ (?n - 1)) * norm (v - u)^?n"
            using \<open>c > 0\<close>
            apply (simp add: algebra_simps)
            by (metis Suc_pred power_Suc DIM_positive)
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
              by (metis (no_types, opaque_lifting) dist_commute dist_norm less_eq_real_def less_le_trans mem_ball)
            then have "norm (v - u) ^ ?n \<le> norm (v - u) ^ ?m"
              by (simp add: power_decreasing [OF mlen])
            also have "\<dots> \<le> ?\<mu> K * real (?m ^ ?m)"
            proof -
              obtain n where n: "\<And>i. i \<in> Basis \<Longrightarrow> v \<bullet> i - u \<bullet> i = 2 * c / 2^n"
                using close [of u v] \<open>K \<in> \<D>\<close> uv by blast
              have "norm (v - u) ^ ?m \<le> (\<Sum>i\<in>Basis. \<bar>(v - u) \<bullet> i\<bar>) ^ ?m"
                by (intro power_mono norm_le_l1) auto
              also have "\<dots> \<le> (\<Prod>i\<in>Basis. v \<bullet> i - u \<bullet> i) * real ?m ^ ?m"
                by (simp add: n inner_diff_left field_simps \<open>c > 0\<close> less_eq_real_def)
              also have "\<dots> = ?\<mu> K * real (?m ^ ?m)"
                by (simp add: uv uv_ne content_cbox')
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
        also have "\<dots> \<le> ?\<mu> (cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One))"
        proof (rule measure_mono_fmeasurable)
          show "\<Union>\<F> \<subseteq> cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One)"
            using sub_cc that(1) by force
        qed (use \<open>\<F> division_of \<Union>\<F>\<close> lmeasurable_division in auto)
        also have "\<dots> = content (cbox (- c *\<^sub>R ?One) (c *\<^sub>R ?One))"
          by simp
        also have "\<dots> \<le> (2 ^ ?m * c ^ ?m)"
          using \<open>c > 0\<close> by (simp add: content_cbox_if mem_box inner_sum_left inner_Basis)
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes mlen: "DIM('a) \<le> DIM('b)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> dim (f' x ` UNIV) < DIM('b)"
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
      have "\<exists>m\<ge>N. g n x - f x \<le> dist (g m x) (f x)" for N
      proof
        show "N \<le> N + n \<and> g n x - f x \<le> dist (g (N + n) x) (f x)"
          using g [of N] by (auto simp: dist_norm)
      qed
      with that show ?thesis
        using diff_gt_0_iff_gt by blast
    qed
    with lim show ?thesis
      unfolding lim_sequentially
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
        using f \<open>k \<in> \<int>\<close> apply (clarsimp simp: indicator_def field_split_simps Ints_def)
        by (smt (verit) int_less_real_le mult_nonneg_nonneg of_int_0 zero_le_power)
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
              apply (clarsimp simp: image_subset_iff)
              using one_le_power [of "2::real" "2*n"]  by linarith
            have *: "\<lbrakk>x \<in> (S \<union> T) - U; \<And>x. x \<in> S \<Longrightarrow> x \<in> U; \<And>x. x \<in> T \<Longrightarrow> x \<in> U\<rbrakk> \<Longrightarrow> P x" for S T U P
              by blast
            have "0 \<le> b" if "b \<in> \<int>" "f x * (2 * 2^n) < b + 1" for b
              by (smt (verit, ccfv_SIG) Ints_cases f int_le_real_less mult_nonneg_nonneg of_int_add one_le_power that)
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
      obtain N1 where N1: "2 ^ N1 > \<bar>f x\<bar>"
        using arch_pow[of 2] by auto
      obtain N2 where N2: "(1/2) ^ N2 < e"
        using \<open>0 < e\<close> arch_pow_inv by fastforce
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
        finally show ?thesis
          using eq by (simp add: dist_real_def)
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


subsection\<open>A one-way version of change-of-variables not assuming injectivity. \<close>

lemma integral_on_image_ubound_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
      and f: "f \<in> borel_measurable (lebesgue_on (g ` S))"
      and nonneg_fg:  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and det_int_fg: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
      and meas_gim: "\<And>T. \<lbrakk>T \<subseteq> g ` S; T \<in> sets lebesgue\<rbrakk> \<Longrightarrow> {x \<in> S. g x \<in> T} \<in> sets lebesgue"
    shows "f integrable_on (g ` S) \<and>
           integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar>"
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
    have "space (lebesgue_on (UNIV::'a set)) = UNIV"
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
                 \<le> integral S (\<lambda>t. \<bar>eucl.det (g' t)\<bar> * y * indicator {x. h n x = y} (g t))"
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
        proof -
          have "(\<lambda>v. eucl.det (g' v)) \<in> borel_measurable (lebesgue_on (S \<inter> {v. h n (g v) = y}))"
            by (metis Int_lower1 S assms(4) borel_measurable_det_Jacobian measurable_restrict_mono)
          then show ?thesis
            by (simp add: Int_commute)
        qed
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
      then have int_det: "(\<lambda>t. \<bar>eucl.det (g' t)\<bar>) integrable_on ({t. h n (g t) = y} \<inter> S)"
        using integrable_restrict_Int by force
      have "(g ` ({t. h n (g t) = y} \<inter> S)) \<in> lmeasurable"
        by (blast intro: has_derivative_subset [OF der_g] measurable_differentiable_image [OF h_lmeas] int_det)
      moreover have "g ` ({t. h n (g t) = y} \<inter> S) = {x. h n x = y} \<inter> g ` S"
        by blast
      moreover have "measure lebesgue (g ` ({t. h n (g t) = y} \<inter> S))
                     \<le> integral ({t. h n (g t) = y} \<inter> S) (\<lambda>t. \<bar>eucl.det (g' t)\<bar>)"
        by (blast intro: has_derivative_subset [OF der_g] measure_differentiable_image [OF h_lmeas _ int_det])
      ultimately show ?thesis
        using \<open>y > 0\<close> integral_restrict_Int [of S "{t. h n (g t) = y}" "\<lambda>t. \<bar>eucl.det (g' t)\<bar> * y"]
        apply (simp add: integrable_on_indicator integral_indicator)
        apply (simp add: indicator_def of_bool_def if_distrib cong: if_cong)
        done
    qed
    show ?thesis
    proof
      show "h n integrable_on g ` S"
        apply (subst hn_eq)
        using yind by (force intro: integrable_sum [OF fin_R])
      have "?lhs = integral (g ` S) (\<lambda>x. \<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} x)"
        by (metis hn_eq)
      also have "\<dots> = (\<Sum>y\<in>range (h n). integral (g ` S) (\<lambda>x. y * indicat_real {x. h n x = y} x))"
        by (rule integral_sum [OF fin_R]) (use yind in blast)
      also have "\<dots> \<le> (\<Sum>y\<in>range (h n). integral S (\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)))"
        using yind by (force intro: sum_mono)
      also have "\<dots> = integral S (\<lambda>u. \<Sum>y\<in>range (h n). \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u))"
      proof (rule integral_sum [OF fin_R, symmetric])
        fix y assume y: "y \<in> ?R"
        with nonneg_h have "y \<ge> 0"
          by auto
        show "(\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)) integrable_on S"
        proof (rule measurable_bounded_by_integrable_imp_integrable)
          have "(\<lambda>x. indicat_real {x. h n x = y} (g x)) \<in> borel_measurable (lebesgue_on S)"
            using h_lmeas S
            by (auto simp: indicator_vimage [symmetric] borel_measurable_indicator_iff sets_restrict_space_iff)
          then show "(\<lambda>u. \<bar>eucl.det (g' u)\<bar> * y * indicat_real {x. h n x = y} (g u)) \<in> borel_measurable (lebesgue_on S)"
            by (intro borel_measurable_times borel_measurable_abs borel_measurable_const borel_measurable_det_Jacobian [OF S der_g])
        next
          fix x
          assume "x \<in> S"
          then have "y * indicat_real {x. h n x = y} (g x) \<le> f (g x)"
            using h_le_f nonneg_fg
            by (smt (verit, best) indicator_times_eq_if(1) mem_Collect_eq mult.commute
                vector_space_over_itself.scale_eq_0_iff)
          with \<open>y \<ge> 0\<close> show "norm (?D x * y * indicat_real {x. h n x = y} (g x)) \<le> ?D x * f(g x)"
            by (simp add: abs_mult mult.assoc mult_left_mono)
        qed (use S det_int_fg in auto)
      qed
      also have "\<dots> = integral S (\<lambda>T. \<bar>eucl.det (g' T)\<bar> *
                                        (\<Sum>y\<in>range (h n). y * indicat_real {x. h n x = y} (g T)))"
        by (simp add: sum_distrib_left mult.assoc)
      also have "\<dots> = ?rhs"
        by (metis hn_eq)
      finally show "integral (g ` S) (h n) \<le> ?rhs" .
    qed
  qed
  have le: "integral S (\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) \<le> ?b" for n
  proof (rule integral_le)
    show "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) integrable_on S"
    proof (rule measurable_bounded_by_integrable_imp_integrable)
      have "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> *\<^sub>R h n (g T)) \<in> borel_measurable (lebesgue_on S)"
      proof (intro borel_measurable_scaleR borel_measurable_abs borel_measurable_det_Jacobian \<open>S \<in> sets lebesgue\<close>)
        have eq: "{x \<in> S. f x \<le> a} = (\<Union>b \<in> (f ` S) \<inter> atMost a. {x. f x = b} \<inter> S)" for f and a::real
          by auto
        have "finite ((\<lambda>x. h n (g x)) ` S \<inter> {..a})" for a
          by (force intro: finite_subset [OF _ fin_R])
        with h_lmeas [of n] show "(\<lambda>x. h n (g x)) \<in> borel_measurable (lebesgue_on S)"
          apply (simp add: borel_measurable_vimage_halfspace_component_le \<open>S \<in> sets lebesgue\<close> sets_restrict_space_iff eq)
          by (metis (mono_tags) SUP_inf sets.finite_UN)
      qed (use der_g in blast)
      then show "(\<lambda>T. \<bar>eucl.det (g' T)\<bar> * h n (g T)) \<in> borel_measurable (lebesgue_on S)"
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
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes nonneg_fg: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
  shows "f integrable_on (g ` S) \<and> integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
proof -
  let ?D = "\<lambda>x. eucl.det (g' x)"
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
      have "(\<lambda>v. eucl.det (g' v)) \<in> borel_measurable (lebesgue_on S')"
        using S' borel_measurable_det_Jacobian der_gS' by blast
      then have "?h \<in> borel_measurable (lebesgue_on S')"
        using "*" borel_measurable_abs borel_measurable_inverse borel_measurable_scaleR by blast
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
        using eucl.det_eq_0_iff by (auto simp: S'_def)
    qed (use der_gS' in auto)
    ultimately show ?thesis
      using double_lebesgue_sets [OF S' gS' order_refl] that by blast
  qed
  have int_gS': "f integrable_on g ` S' \<and> integral (g ` S') f \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
    using integral_on_image_ubound_weak [OF S' f nonneg_fg der_gS' intS' lebS'] S'_def by blast
  have neg_det: "negligible (g ` {x \<in> S. eucl.det (g' x) = 0})"
  proof (rule baby_Sard [OF order_refl], simp_all)
    fix x
    assume x: "x \<in> S \<and> eucl.det (g' x) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. eucl.det (g' x) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    have "linear (g' x)"
      using \<open>(g has_derivative g' x) _\<close> has_derivative_linear by blast
    then have "\<not> inj (g' x)"
      using x eucl.det_eq_0_iff by auto
    then have "\<not> surj (g' x)"
      using \<open>linear (g' x)\<close> eucl.linear_surjective_imp_injective by auto
    then have "g' x ` UNIV \<noteq> UNIV"
      by (simp add: surj_def)
    moreover have "subspace (g' x ` UNIV)"
      using \<open>linear (g' x)\<close> linear_subspace_image subspace_UNIV by blast
    ultimately show "dim (g' x ` UNIV) < DIM('a)"
      using eucl.subspace_dim_equal [of "g' x ` UNIV" UNIV] subspace_UNIV eucl.dim_UNIV
      by (metis eucl.dim_subset le_neq_implies_less subset_UNIV)
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
      using negg null
      by (auto intro: integrable_spike_set [OF _ empty_imp_negligible negligible_subset])
    have "integral (g ` S) f = integral (g ` {x \<in> S. ?D x \<noteq> 0}) f"
      using negg by (auto intro: negligible_subset integral_spike_set)
    also have "\<dots> = integral (g ` {x \<in> S. ?D x \<noteq> 0}) (\<lambda>x. if x \<in> g ` ?F then f x else 0)"
      by (auto simp: image_iff intro!: integral_cong)
    also have "\<dots> = integral (g ` S') f"
      using eq integral_restrict_Int by simp
    also have "\<dots> \<le> integral S' (\<lambda>x. \<bar>?D x\<bar> * f(g x))"
      by (metis int_gS')
    also have "\<dots> \<le> ?b"
      by (rule integral_subset_le [OF _ intS' intS]) (use nonneg_fg S'_def in auto)
    finally show "integral (g ` S) f \<le> ?b" .
  qed
qed

lemma absolutely_integrable_on_image_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f (g x)"
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
         integral (g ` ?N) (\<lambda>x. - f x) \<le> integral ?N (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x))"
  proof (rule integral_on_image_ubound_nonneg [OF _ der_gN])
    have 1: "?D integrable_on {x \<in> S. ?D x < 0}"
      using Dlt
      by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
    have "uminus \<circ> (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x)) integrable_on ?N"
      by (simp add: o_def mult_less_0_iff empty_imp_negligible integrable_spike_set [OF 1])
    then show "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * - f (g x)) integrable_on ?N"
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
      show "?D integrable_on ?P"
      proof (rule integrable_spike_set)
        show "?D integrable_on {x \<in> S. 0 < ?D x}"
          using Dgt
          by (auto intro: set_lebesgue_integral_eq_integral [OF set_integrable_subset] intS)
      qed (auto simp: zero_less_mult_iff empty_imp_negligible)
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
proof (rule absolutely_integrable_componentwise)
  fix b :: 'b assume "b \<in> Basis"
  have "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * (f (g x) \<bullet> b)) absolutely_integrable_on S"
    using absolutely_integrable_component [OF intS, of b]
    by (simp add: inner_scaleR_left)
  then show "(\<lambda>x. f x \<bullet> b) absolutely_integrable_on g ` S"
    by (auto intro: absolutely_integrable_on_image_real der_g)
qed

proposition integral_on_image_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "(\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S"
  shows "integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x))"
  using integral_on_image_ubound_nonneg [OF assms] by simp

subsection\<open>Change-of-variables theorem\<close>

text\<open>The classic change-of-variables theorem. We have two versions with quite general hypotheses,
the first that the transforming function has a continuous inverse, the second that the base set is
Lebesgue measurable.\<close>
lemma cov_invertible_nonneg_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and f0: "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "f integrable_on T \<and> (integral T f) \<le> b \<longleftrightarrow>
             (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) \<le> b"
        (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  have gS: "g differentiable_on S"
    by (meson der_g differentiable_def differentiable_on_def)
  let ?D = "\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f (g x)"
  show ?thesis
  proof
    assume ?lhs
    then have fT: "f integrable_on T" and intf: "integral T f \<le> b"
      by blast+
    show ?rhs
    proof
      let ?fgh = "\<lambda>x. \<bar>eucl.det (h' x)\<bar> * (\<bar>eucl.det (g' (h x))\<bar> * f (g (h x)))"
      have ddf: "?fgh x = f x"
        if "x \<in> T" for x
      proof -
        have lin_h: "linear (h' x)" and lin_g: "linear (g' (h x))"
          using der_h that gh der_g has_derivative_linear by blast+
        have "h' x \<circ> g'(h x) = id"
          using id that by blast
        then have "eucl.det (h' x \<circ> g' (h x)) = 1"
          by (simp add: eucl.det_ident)
        then have "eucl.det (h' x) * eucl.det (g' (h x)) = 1"
          by (simp add: eucl.det_compose [OF lin_h lin_g])
        then have "\<bar>eucl.det (h' x)\<bar> * \<bar>eucl.det (g' (h x))\<bar> = 1"
          by (metis abs_1 abs_mult)
        then show ?thesis
          by (simp add: gh that)
      qed
      have "?D integrable_on (h ` T)"
      proof (intro set_lebesgue_integral_eq_integral absolutely_integrable_on_image_real)
        show "(\<lambda>x. ?fgh x) absolutely_integrable_on T"
          by (smt (verit, del_insts) abs_absolutely_integrableI_1 ddf f0 fT integrable_eq)
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
      finally show "integral S (\<lambda>x. ?D x) \<le> b"
        using intf by linarith
    qed
  next
    assume R: ?rhs
    then have "f integrable_on g ` S"
      by (metis (full_types) der_g f0 hg integral_on_image_ubound_nonneg)
    moreover have "integral (g ` S) f \<le> integral S (\<lambda>x. ?D x)"
      by (rule integral_on_image_ubound [OF f0 der_g]) (use R Teq in auto)
    ultimately show ?lhs
      using R by (simp add: Teq)
  qed
qed

lemma cov_invertible_nonneg_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
      and "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "((\<lambda>x. \<bar>eucl.det (g' x)\<bar> * f(g x)) has_integral b) S \<longleftrightarrow> (f has_integral b) T"
  using cov_invertible_nonneg_le [OF assms]
  by (simp add: has_integral_iff) (meson eq_iff)

lemma cov_invertible_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on T \<and> integral T f = b"
         (is "?lhs = ?rhs")
proof -
  have Teq: "T = g`S" and Seq: "S = h`T"
    using hg gh image_iff by fastforce+
  let ?DP = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> * f(g x)" and ?DN = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> * -f(g x)"
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
    proof (rule absolutely_integrable_integrable_bound)
      show "(\<lambda>x. - f x) integrable_on {y \<in> T. f y < 0}"
        using fN by (auto simp: integrable_neg_iff)
    qed (use fN in auto)
    have fP: "f integrable_on {y \<in> T. f y > 0}"
             "integral {y \<in> T. f y > 0} f = integral {x \<in> S. f (g x) > 0} ?DP"
      using "+" [of "integral {x \<in> S. f(g x) > 0} ?DP"] aP
      by (auto simp: set_lebesgue_integral_eq_integral has_integral_iff integrable_neg_iff)
    have faP: "f absolutely_integrable_on {y \<in> T. f y > 0}"
      using fP(1) nonnegative_absolutely_integrable_1 by fastforce
    have fa: "f absolutely_integrable_on ({y \<in> T. f y < 0} \<union> {y \<in> T. f y > 0})"
      by (rule absolutely_integrable_Un [OF faN faP])
    show ?rhs
    proof
      have eq: "((if x \<in> T \<and> f x < 0 \<or> x \<in> T \<and> 0 < f x then 1 else 0) * f x)
              = (if x \<in> T then 1 else 0) * f x" for x
        by auto
      show "f absolutely_integrable_on T"
        using fa by (simp add: indicator_def of_bool_def set_integrable_def eq)
      have [simp]: "{y \<in> T. f y < 0} \<inter> {y \<in> T. 0 < f y} = {}" for T and f :: "'a \<Rightarrow> real"
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
      using set_integrable_subset [of _ T] TP TN RHS by blast+
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
      have [simp]: "{y \<in> S. f y < 0} \<inter> {y \<in> S. 0 < f y} = {}" for S and f :: "'a \<Rightarrow> real"
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on T \<and> integral T f = b"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)"
  have "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> * (f(g x) \<bullet> i)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * (f(g x) \<bullet> i)) = b \<bullet> i) \<longleftrightarrow>
        ((\<lambda>x. f x \<bullet> i) absolutely_integrable_on T \<and> integral T (\<lambda>x. f x \<bullet> i) = b \<bullet> i)" for i
    by (rule cov_invertible_real [OF der_g der_h hg gh id])
  then have "?D absolutely_integrable_on S \<and> (?D has_integral b) S \<longleftrightarrow>
        f absolutely_integrable_on T \<and> (f has_integral b) T"
    unfolding absolutely_integrable_componentwise_iff [where f=f] has_integral_componentwise_iff [of f]
              absolutely_integrable_componentwise_iff [where f="?D"] has_integral_componentwise_iff [of ?D]
    by (auto simp: all_conj_distrib has_integral_iff set_lebesgue_integral_eq_integral dest: absolutely_integrable_on_def [THEN iffD1, THEN conjunct1])
  then show ?thesis
    using absolutely_integrable_on_def by blast
qed


lemma cv_inv_version4:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and> eucl.det(g' x) \<noteq> 0"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> continuous_on (g ` S) h \<and> h(g x) = x"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "\<exists>h'. x \<in> S
           \<longrightarrow> (g has_derivative g' x) (at x within S) \<and> linear h' \<and> g' x \<circ> h' = id \<and> h' \<circ> g' x = id" for x
  proof (cases "x \<in> S")
    case True
    then have "linear (g' x)" "inj (g' x)" "(g has_derivative g' x) (at x within S)"
      using der_g has_derivative_linear eucl.det_eq_0_iff by blast+
    then have "linear (inv (g' x))" "g' x \<circ> inv (g' x) = id" "inv (g' x) \<circ> g' x = id"
      using eucl.inj_linear_imp_inv_linear inv_o_cancel surj_iff eucl.linear_inj_imp_surj
      by blast+
    then show ?thesis
      using \<open>(g has_derivative g' x) (at x within S)\<close> by blast
  qed auto
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
      and conth: "continuous_on (g ` S) h"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    (is "?lhs = ?rhs")
proof -
  let ?S = "{x \<in> S. eucl.det(g' x) \<noteq> 0}" and ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)"
  have *: "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
           \<longleftrightarrow> f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b"
  proof (rule cv_inv_version4)
    show "(g has_derivative g' x) (at x within ?S) \<and> eucl.det(g' x) \<noteq> 0"
      if "x \<in> ?S" for x
      using der_g that has_derivative_subset that by fastforce
    show "continuous_on (g ` ?S) h \<and> h (g x) = x"
      if "x \<in> ?S" for x
      using that continuous_on_subset [OF conth]  by (simp add: hg image_mono)
  qed
  have "negligible (g ` {x \<in> S. eucl.det(g' x) = 0})"
  proof (rule baby_Sard [OF order_refl], simp_all)
    fix x
    assume x: "x \<in> S \<and> eucl.det (g' x) = 0"
    then show "(g has_derivative g' x) (at x within {x \<in> S. eucl.det (g' x) = 0})"
      by (metis (no_types, lifting) der_g has_derivative_subset mem_Collect_eq subsetI)
    have "linear (g' x)"
      using \<open>(g has_derivative g' x) _\<close> has_derivative_linear by blast
    then have "g' x ` UNIV \<noteq> UNIV"
      using det_eq_0_iff linear_surj_imp_inj x by blast
    moreover have "subspace (g' x ` UNIV)"
      using \<open>linear (g' x)\<close> linear_subspace_image subspace_UNIV by blast
    ultimately show "dim (g' x ` UNIV) < DIM('a)"
      using eucl.subspace_dim_equal [of "g' x ` UNIV" UNIV] subspace_UNIV eucl.dim_UNIV
      by (metis eucl.dim_subset le_neq_implies_less subset_UNIV)
  qed
  then have neg: "negligible {x \<in> g ` S. x \<notin> g ` ?S \<and> f x \<noteq> 0}"
    by (auto intro: negligible_subset)
  have [simp]: "{x \<in> g ` ?S. x \<notin> g ` S \<and> f x \<noteq> 0} = {}"
    by auto
  have "?D absolutely_integrable_on ?S \<and> integral ?S ?D = b
    \<longleftrightarrow> ?D absolutely_integrable_on S \<and> integral S ?D = b"
    by (intro conj_cong absolutely_integrable_spike_set_eq)
       (auto simp: integral_spike_set empty_imp_negligible neg)
  moreover
  have "f absolutely_integrable_on (g ` ?S) \<and> integral (g ` ?S) f = b
    \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    by (auto intro!: conj_cong absolutely_integrable_spike_set_eq integral_spike_set neg)
  ultimately
  show ?thesis
    using "*" by blast
qed



theorem has_absolute_integral_change_of_variables_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "compact S"
      and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and inj: "inj_on g S"
  shows "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b)"
proof -
  obtain h where hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
    using inj by (metis the_inv_into_f_f)
  have conth: "continuous_on (g ` S) h"
    by (metis \<open>compact S\<close> continuous_on_inv der_g has_derivative_continuous_on hg)
  show ?thesis
    by (rule has_absolute_integral_change_of_variables_invertible [OF der_g hg conth])
qed

lemma integral_countable_UN:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and s :: "nat \<Rightarrow> 'a set"
  assumes f: "f absolutely_integrable_on (\<Union> (range s))"
    and s: "\<And>m. s m \<in> sets lebesgue"
  shows ai: "f absolutely_integrable_on (\<Union> (s ` {..n}))"
    and "(\<lambda>n. integral (\<Union> (s ` {..n})) f) \<longlonglongrightarrow> integral (\<Union> (range s)) f" (is "?F \<longlonglongrightarrow> ?I")
proof -
  show fU: "f absolutely_integrable_on (\<Union>m\<le>n. s m)" for n
    using assms by (blast intro: set_integrable_subset [OF f])
  have fint: "f integrable_on (\<Union> (range s))"
    using absolutely_integrable_on_def f by blast
  let ?h = "\<lambda>x. if x \<in> \<Union>(s ` UNIV) then norm(f x) else 0"
  have "(\<lambda>n. integral UNIV (\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0))
        \<longlonglongrightarrow> integral UNIV (\<lambda>x. if x \<in> \<Union>(s ` UNIV) then f x else 0)"
  proof (rule dominated_convergence)
    show "(\<lambda>x. if x \<in> (\<Union>m\<le>n. s m) then f x else 0) integrable_on UNIV" for n
      unfolding integrable_restrict_UNIV
      using fU absolutely_integrable_on_def by blast
    show "(\<lambda>x. if x \<in> \<Union>(s ` UNIV) then norm(f x) else 0) integrable_on UNIV"
      by (metis (no_types) absolutely_integrable_on_def f integrable_restrict_UNIV)
    show "\<And>x. (\<lambda>n. if x \<in> (\<Union>m\<le>n. s m) then f x else 0)
         \<longlonglongrightarrow> (if x \<in> \<Union>(s ` UNIV) then f x else 0)"
      by (force intro: tendsto_eventually eventually_sequentiallyI)
  qed auto
  then show "?F \<longlonglongrightarrow> ?I"
    by (simp only: integral_restrict_UNIV)
qed 

lemma has_absolute_integral_change_of_variables_compact_family:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes compact: "\<And>n::nat. compact (F n)"
      and der_g: "\<And>x. x \<in> (\<Union>n. F n) \<Longrightarrow> (g has_derivative g' x) (at x within (\<Union>n. F n))"
      and inj: "inj_on g (\<Union>n. F n)"
  shows "((\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on (\<Union>n. F n) \<and>
             integral (\<Union>n. F n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` (\<Union>n. F n)) \<and> integral (g ` (\<Union>n. F n)) f = b)"
proof -
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)"
  let ?U = "\<lambda>n. \<Union>m\<le>n. F m"
  let ?lift = "vec::real\<Rightarrow>real^1"
  have F_leb: "F m \<in> sets lebesgue" for m
    by (simp add: compact borel_compact)
  have iff: "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)) absolutely_integrable_on (?U n) \<and>
             integral (?U n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` (?U n)) \<and> integral (g ` (?U n)) f = b" for n b and f :: "'a \<Rightarrow> 'c::euclidean_space"
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
      using integral_countable_UN [where s=F and f="?D"] DS F_leb by auto
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
            using iff [of n "norm \<circ> f" "integral (?U n) (\<lambda>x. \<bar>eucl.det(g' x)\<bar> * norm (f (g x)))"]
            by (auto simp: o_def)
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
    qed (use DU in metis)
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
            using absolutely_integrable_norm fgU by blast
          then have "integral (?U n) (norm \<circ> ?D) = integral (g ` ?U n) (norm \<circ> f)"
            using iff [of n "norm \<circ> f" "integral (g ` ?U n) (norm \<circ> f)"]
            unfolding image_UN by (auto simp: o_def)
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
        then show "(\<lambda>m. if \<exists>j\<in>{..m}. x \<in> F j then ?D x else 0) \<longlonglongrightarrow> ?D x"
          by (auto intro!: tendsto_eventually eventually_sequentiallyI [of n])
      qed
    qed auto
    then show Dai: "?D absolutely_integrable_on (\<Union>n. F n)"
      unfolding absolutely_integrable_restrict_UNIV by simp
    show "integral (\<Union>n. F n) ?D = integral ((\<Union>x. g ` F x)) f"
    proof (rule LIMSEQ_unique)
      show "(\<lambda>n. integral (\<Union>m\<le>n. g ` F m) f) \<longlonglongrightarrow> integral (\<Union>n. F n) ?D"
        unfolding D_int [symmetric] by (rule integral_countable_UN [OF Dai F_leb])
    qed (use fgU in metis)
  qed
qed


theorem has_absolute_integral_change_of_variables:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  obtain C N where "fsigma C" and N: "N \<in> null_sets lebesgue" and CNS: "C \<union> N = S" and "disjnt C N"
    using lebesgue_set_almost_fsigma [OF S] .
  then obtain F :: "nat \<Rightarrow> ('a) set"
    where F: "range F \<subseteq> Collect compact" and Ceq: "C = Union(range F)"
    using fsigma_Union_compact by metis
  have "negligible N"
    using N by (simp add: negligible_iff_null_sets)
  let ?D = "\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f (g x)"
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "inj_on g S"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  using assms has_absolute_integral_change_of_variables by blast

corollary integral_change_of_variables:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and disj: "(f absolutely_integrable_on (g ` S) \<or>
        (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  shows "integral (g ` S) f = integral S (\<lambda>x. \<bar>eucl.det(g' x)\<bar> *\<^sub>R f(g x))"
  using has_absolute_integral_change_of_variables [OF S der_g inj] disj
  by blast

lemma has_absolute_integral_change_of_variables_1:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>eucl.det((*) (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
         integral S (\<lambda>x. \<bar>eucl.det((*) (g' x))\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    by (rule has_absolute_integral_change_of_variables [OF S _ inj])
       (use der_g in \<open>auto simp: has_vector_derivative_def mult.commute\<close>)
  then show ?thesis
    by (simp add: det_real)
qed

corollary absolutely_integrable_change_of_variables_1:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space" and g :: "real \<Rightarrow> real"
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
  shows "(\<lambda>x. \<bar>g' x\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> * f (g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x)) :: real ^ 1) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R vec (f(g x))) = (vec b :: real ^ 1)
         \<longleftrightarrow> (\<lambda>x. vec (f x) :: real ^ 1) absolutely_integrable_on (g ` S) \<and>
           integral (g ` S) (\<lambda>x. vec (f x)) = (vec b :: real ^ 1)"
    using assms unfolding has_real_derivative_iff_has_vector_derivative
    by (intro has_absolute_integral_change_of_variables_1 assms) auto
  thus ?thesis
    by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq)
qed

lemma has_absolute_integral_reflect_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "uminus ` A \<subseteq> B" "uminus ` B \<subseteq> A" "A \<in> sets lebesgue"
  shows "(\<lambda>x. f (-x)) absolutely_integrable_on A \<and> integral A (\<lambda>x. f (-x)) = b \<longleftrightarrow>
         f absolutely_integrable_on B \<and> integral B f = b"
proof -
  have bij: "bij_betw uminus A B"
    by (rule bij_betwI[of _ _ _ uminus]) (use assms in auto)
  have "((\<lambda>x. \<bar>-1\<bar> * f (-x)) absolutely_integrable_on A \<and>
          integral A (\<lambda>x. \<bar>-1\<bar> * f (-x)) = b) \<longleftrightarrow>
        (f absolutely_integrable_on uminus ` A \<and> integral (uminus ` A) f = b)" 
    using assms
    by (intro has_absolute_integral_change_of_variables_1') (auto intro!: derivative_eq_intros)
  also have "uminus ` A = B"
    using bij by (simp add: bij_betw_def)
  finally show ?thesis
    by simp
qed

subsection\<open>Change of variables for integrals: special case of linear function\<close>

lemma has_absolute_integral_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof (cases "eucl.det g = 0")
  case True
  then have "negligible(g ` S)"
    using assms eucl.det_eq_0_iff negligible_linear_singular_image by blast
  with True show ?thesis
    by (auto simp: absolutely_integrable_on_def integrable_negligible integral_negligible)
next
  case False
  then have "inj g"
    using assms eucl.det_eq_0_iff by blast
  then have h: "\<And>x. x \<in> S \<Longrightarrow> inv g (g x) = x" "linear (inv g)"
    using inv_f_f eucl.inj_linear_imp_inv_linear assms by auto
  show ?thesis
  proof (rule has_absolute_integral_change_of_variables_invertible)
    show "(g has_derivative g) (at x within S)" for x
      by (simp add: assms linear_imp_has_derivative)
    show "continuous_on (g ` S) (inv g)"
      using continuous_on_eq_continuous_within has_derivative_continuous linear_imp_has_derivative h by blast
  qed (use h in auto)
qed

lemma absolutely_integrable_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>eucl.det g\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S
     \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
  using assms has_absolute_integral_change_of_variables_linear by blast

lemma absolutely_integrable_on_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (f \<circ> g) absolutely_integrable_on S \<or> eucl.det g = 0"
  unfolding assms absolutely_integrable_change_of_variables_linear [OF assms, symmetric] absolutely_integrable_on_scaleR_iff
  by (auto simp: set_integrable_def)

lemma integral_change_of_variables_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'a \<Rightarrow> 'a"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>eucl.det g\<bar> *\<^sub>R integral S (f \<circ> g)"
  by (metis (mono_tags, lifting) Henstock_Kurzweil_Integration.integral_cong
      absolutely_integrable_on_linear_image assms(1,2) comp_apply
      has_absolute_integral_change_of_variables_linear integral_cmul)

lemma absolutely_integrable_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "f absolutely_integrable_on g ` S \<longleftrightarrow> (\<lambda>x. \<bar>h x\<bar> * f (g x)) absolutely_integrable_on S"
  using has_absolute_integral_change_of_variables_1'[of S g h f] assms by auto

lemma absolutely_integrable_change_of_variables_real:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "f absolutely_integrable_on g ` S \<longleftrightarrow> (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S"
  using absolutely_integrable_change_of_variables_1 assms
    has_real_derivative_iff_has_vector_derivative by blast

lemma has_absolute_integral_change_of_variables_real:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative h x) (at x within S)"
  assumes "inj_on g S"
  shows   "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b
          \<longleftrightarrow> f absolutely_integrable_on g ` S \<and> integral (g ` S) f = b"
proof (intro conj_cong)
  show iff: "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<longleftrightarrow> 
               f absolutely_integrable_on g ` S"
    using absolutely_integrable_change_of_variables_real assms by blast

  assume "f absolutely_integrable_on g ` S"
  hence integrable: "f integrable_on g ` S" "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) integrable_on S"
    using set_lebesgue_integral_eq_integral(1) iff by metis+

  have "(\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on S \<and> 
        (integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b) \<longleftrightarrow>
        (\<forall>a\<in>Basis. (\<lambda>x. (\<bar>h x\<bar> *\<^sub>R f (g x)) \<bullet> a) absolutely_integrable_on S \<and> 
                   (integral S (\<lambda>x. (\<bar>h x\<bar> *\<^sub>R f (g x)) \<bullet> a) = b \<bullet> a))"    
    by (subst absolutely_integrable_componentwise_iff, subst integral_eq_iff_componentwise)
       (use integrable in auto)
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>Basis. (\<lambda>x. \<bar>h x\<bar> * (f (g x) \<bullet> a)) absolutely_integrable_on S \<and> 
                       (integral S (\<lambda>x. \<bar>h x\<bar> * (f (g x) \<bullet> a)) = b \<bullet> a))"   
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>Basis. (\<lambda>x. f x \<bullet> a) absolutely_integrable_on g ` S \<and> 
                       (integral (g ` S) (\<lambda>x. f x \<bullet> a) = b \<bullet> a))"
    by (intro ball_cong has_absolute_integral_change_of_variables_1' assms refl)
  also have "\<dots> \<longleftrightarrow> f absolutely_integrable_on g ` S \<and>  integral (g ` S) f = b"
    by (simp add: \<open>f absolutely_integrable_on g ` S\<close> absolutely_integrable_component
        integrable(1) integral_eq_iff_componentwise)
  finally show "(integral S (\<lambda>x. \<bar>h x\<bar> *\<^sub>R f (g x)) = b) = (integral (g ` S) f = b)"
    using \<open>f absolutely_integrable_on g ` S\<close> iff by blast
qed

subsection\<open>Change of variable for measure\<close>

lemma has_measure_differentiable_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) = m
     \<longleftrightarrow> ((\<lambda>x. \<bar>eucl.det (f' x)\<bar>) has_integral m) S"
  using has_absolute_integral_change_of_variables [OF assms, of "\<lambda>x. (1::real^1)" "vec m"]
  unfolding absolutely_integrable_on_1_iff integral_on_1_eq integrable_on_1_iff absolutely_integrable_on_def
  by (auto simp: has_integral_iff lmeasurable_iff_integrable_on lmeasure_integral)

lemma measurable_differentiable_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  using has_measure_differentiable_image [OF assms]
  by blast

lemma measurable_differentiable_image_alt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>eucl.det (f' x)\<bar>) absolutely_integrable_on S"
  using measurable_differentiable_image_eq [OF assms]
  by (simp only: absolutely_integrable_on_iff_nonneg)

lemma measure_differentiable_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>eucl.det (f' x)\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>eucl.det (f' x)\<bar>)"
  using measurable_differentiable_image_eq [OF S der_f inj]
        assms has_measure_differentiable_image by blast

proposition measure_lebesgue_linear_transformation:
  fixes A :: "'a::euclidean_space set"
  fixes f :: "_ \<Rightarrow> 'a"
  assumes "bounded A" "A \<in> sets lebesgue" "linear f"
  shows   "measure lebesgue (f ` A) = \<bar>det f\<bar> * measure lebesgue A"
proof -
  from assms have [intro]: "A \<in> lmeasurable"
    by (intro bounded_set_imp_lmeasurable) auto
  hence [intro]: "f ` A \<in> lmeasurable"
    by (intro lmeasure_integral measurable_linear_image assms)
  have "measure lebesgue (f ` A) = integral (f ` A) (\<lambda>_. 1)"
    by (intro lmeasure_integral measurable_linear_image assms) auto
  also have "\<dots> = integral (f ` A) (\<lambda>_. 1 :: real ^ 1) $ 0"
    by (subst integral_component_eq_cart [symmetric]) (auto intro: integrable_on_const)
  also have "\<dots> = \<bar>det f\<bar> * integral A (\<lambda>x. 1 :: real ^ 1) $ 0"
    using assms
    by (subst integral_change_of_variables_linear)
       (auto simp: o_def absolutely_integrable_on_def intro: integrable_on_const)
  also have "integral A (\<lambda>x. 1 :: real ^ 1) $ 0 = integral A (\<lambda>x. 1)"
    by (subst integral_component_eq_cart [symmetric]) (auto intro: integrable_on_const)
  also have "\<dots> = measure lebesgue A"
    by (intro lmeasure_integral [symmetric]) auto
  finally show ?thesis .
qed

(*DELETE?
lemma measure_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>matrix_det (matrix (f' x))\<bar>)"
  using Change_Of_Vars.has_measure_differentiable_image S der_f inj intS by blast 
  using measurable_differentiable_image_eq [OF S der_f inj]
        assms has_measure_differentiable_image by blast
*)

end

(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL light)
*)

section \<open>Fashoda Meet Theorem\<close>

theory Fashoda_Theorem
imports Brouwer_Fixpoint Path_Connected Cartesian_Euclidean_Space
begin

subsection \<open>Bijections between intervals\<close>

definition\<^marker>\<open>tag important\<close> interval_bij :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_space"
  where "interval_bij =
    (\<lambda>(a, b) (u, v) x. (\<Sum>i\<in>Basis. (u\<bullet>i + (x\<bullet>i - a\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (v\<bullet>i - u\<bullet>i)) *\<^sub>R i))"

lemma interval_bij_affine:
  "interval_bij (a,b) (u,v) = (\<lambda>x. (\<Sum>i\<in>Basis. ((v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (x\<bullet>i)) *\<^sub>R i) +
    (\<Sum>i\<in>Basis. (u\<bullet>i - (v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (a\<bullet>i)) *\<^sub>R i))"
  by (simp add: interval_bij_def algebra_simps add_divide_distrib diff_divide_distrib flip: sum.distrib scaleR_add_left)


lemma continuous_interval_bij:
  fixes a b :: "'a::euclidean_space"
  shows "continuous (at x) (interval_bij (a, b) (u, v))"
  by (auto simp add: divide_inverse interval_bij_def intro!: continuous_sum continuous_intros)

lemma continuous_on_interval_bij: "continuous_on s (interval_bij (a, b) (u, v))"
  by (metis continuous_at_imp_continuous_on continuous_interval_bij)

lemma in_interval_interval_bij:
  fixes a b u v x :: "'a::euclidean_space"
  assumes "x \<in> cbox a b"
    and "cbox u v \<noteq> {}"
  shows "interval_bij (a, b) (u, v) x \<in> cbox u v"
proof -
  have "\<And>i. i \<in> Basis \<Longrightarrow> u \<bullet> i \<le> u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i)"
    by (smt (verit) assms box_ne_empty(1) divide_nonneg_nonneg mem_box(2) mult_nonneg_nonneg)
  moreover
  have "\<And>i. i \<in> Basis \<Longrightarrow> u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i) \<le> v \<bullet> i"
    apply (simp add: divide_simps algebra_simps)
    by (smt (verit, best) assms box_ne_empty(1) left_diff_distrib mem_box(2) mult.commute mult_left_mono)
  ultimately show ?thesis
    by (force simp only: interval_bij_def split_conv mem_box inner_sum_left_Basis)
qed

lemma interval_bij_bij:
  "\<forall>(i::'a::euclidean_space)\<in>Basis. a\<bullet>i < b\<bullet>i \<and> u\<bullet>i < v\<bullet>i \<Longrightarrow>
    interval_bij (a, b) (u, v) (interval_bij (u, v) (a, b) x) = x"
  by (auto simp: interval_bij_def euclidean_eq_iff[where 'a='a])

lemma interval_bij_bij_cart: fixes x::"real^'n" assumes "\<forall>i. a$i < b$i \<and> u$i < v$i"
  shows "interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x"
  using assms by (intro interval_bij_bij) (auto simp: Basis_vec_def inner_axis)


subsection \<open>Fashoda meet theorem\<close>

lemma infnorm_2:
  fixes x :: "real^2"
  shows "infnorm x = max \<bar>x$1\<bar> \<bar>x$2\<bar>"
  unfolding infnorm_cart UNIV_2 by (rule cSup_eq) auto

lemma infnorm_eq_1_2:
  fixes x :: "real^2"
  shows "infnorm x = 1 \<longleftrightarrow>
    \<bar>x$1\<bar> \<le> 1 \<and> \<bar>x$2\<bar> \<le> 1 \<and> (x$1 = -1 \<or> x$1 = 1 \<or> x$2 = -1 \<or> x$2 = 1)"
  unfolding infnorm_2 by auto

lemma infnorm_eq_1_imp:
  fixes x :: "real^2"
  assumes "infnorm x = 1"
  shows "\<bar>x$1\<bar> \<le> 1" and "\<bar>x$2\<bar> \<le> 1"
  using assms unfolding infnorm_eq_1_2 by auto

proposition fashoda_unit:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "f ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "g ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "continuous_on {-1 .. 1} f"
    and "continuous_on {-1 .. 1} g"
    and "f (- 1)$1 = - 1"
    and "f 1$1 = 1" "g (- 1) $2 = -1"
    and "g 1 $2 = 1"
  shows "\<exists>s\<in>{-1 .. 1}. \<exists>t\<in>{-1 .. 1}. f s = g t"
proof (rule ccontr)
  assume "\<not> ?thesis"
  note as = this[unfolded bex_simps,rule_format]
  define sqprojection
    where [abs_def]: "sqprojection z = (inverse (infnorm z)) *\<^sub>R z" for z :: "real^2"
  define negatex :: "real^2 \<Rightarrow> real^2"
    where "negatex x = (vector [-(x$1), x$2])" for x
  have inf_nega: "\<And>z::real^2. infnorm (negatex z) = infnorm z"
    unfolding negatex_def infnorm_2 vector_2 by auto
  have inf_eq1: "\<And>z. z \<noteq> 0 \<Longrightarrow> infnorm (sqprojection z) = 1"
    unfolding sqprojection_def infnorm_mul[unfolded scalar_mult_eq_scaleR]
    by (simp add: real_abs_infnorm infnorm_eq_0)
  let ?F = "\<lambda>w::real^2. (f \<circ> (\<lambda>x. x$1)) w - (g \<circ> (\<lambda>x. x$2)) w"
  have *: "\<And>i. (\<lambda>x::real^2. x $ i) ` cbox (- 1) 1 = {-1..1}"
  proof 
    show "(\<lambda>x::real^2. x $ i) ` cbox (- 1) 1 \<subseteq> {-1..1}" for i
      by (auto simp: mem_box_cart)
    show "{-1..1} \<subseteq> (\<lambda>x::real^2. x $ i) ` cbox (- 1) 1" for i
      by (clarsimp simp: image_iff mem_box_cart Bex_def) (metis (no_types, opaque_lifting) vec_component)
  qed
  {
    fix x
    assume "x \<in> (\<lambda>w. (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w) ` (cbox (- 1) (1::real^2))"
    then obtain w :: "real^2" where w:
        "w \<in> cbox (- 1) 1"
        "x = (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w"
      unfolding image_iff ..
    then have "x \<noteq> 0"
      using as[of "w$1" "w$2"] by (auto simp: mem_box_cart atLeastAtMost_iff)
  } note x0 = this
  let ?CB11 = "cbox (- 1) (1::real^2)"
  obtain x :: "real^2" where x:
      "x \<in> cbox (- 1) 1"
      "(negatex \<circ> sqprojection \<circ> (\<lambda>w. (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w)) x = x"
  proof (rule brouwer_weak[of ?CB11 "negatex \<circ> sqprojection \<circ> ?F"])
    show "compact ?CB11" "convex ?CB11"
      by (rule compact_cbox convex_box)+
    have "box (- 1) (1::real^2) \<noteq> {}"
      unfolding interval_eq_empty_cart by auto
    then show "interior ?CB11 \<noteq> {}"
      by simp
    have "negatex (x + y) $ i = (negatex x + negatex y) $ i \<and> negatex (c *\<^sub>R x) $ i = (c *\<^sub>R negatex x) $ i"
      for i x y c
      using exhaust_2 [of i] by (auto simp: negatex_def)
    then have "bounded_linear negatex"
      by (simp add: bounded_linearI' vec_eq_iff)
    then show "continuous_on ?CB11 (negatex \<circ> sqprojection \<circ> ?F)"
      unfolding sqprojection_def
      apply (intro continuous_intros continuous_on_component | use * assms in presburger)+
       apply (simp_all add: infnorm_eq_0 x0 linear_continuous_on)
      done
    have "(negatex \<circ> sqprojection \<circ> ?F) ` ?CB11 \<subseteq> ?CB11"
    proof clarsimp
      fix y :: "real^2" 
      assume y: "y \<in> ?CB11"
      have "?F y \<noteq> 0"
        by (rule x0) (use y in auto)
      then have *: "infnorm (sqprojection (?F y)) = 1"
        using inf_eq1 by blast
      show "negatex (sqprojection (f (y $ 1) - g (y $ 2))) \<in> cbox (-1) 1"
        unfolding mem_box_cart interval_cbox_cart infnorm_2
        by (smt (verit, del_insts) "*" component_le_infnorm_cart inf_nega neg_one_index o_apply one_index)
    qed
    then show "negatex \<circ> sqprojection \<circ> ?F \<in> ?CB11 \<rightarrow> ?CB11"
      by blast
  qed
  have "?F x \<noteq> 0"
    by (rule x0) (use x in auto)
  then have *: "infnorm (sqprojection (?F x)) = 1"
    using inf_eq1 by blast
  have nx: "infnorm x = 1"
    by (metis (no_types, lifting) "*" inf_nega o_apply x(2))
  have iff: "0 < sqprojection x$i \<longleftrightarrow> 0 < x$i" "sqprojection x$i < 0 \<longleftrightarrow> x$i < 0" if "x \<noteq> 0" for x i
  proof -
    have *: "inverse (infnorm x) > 0"
      by (simp add: infnorm_pos_lt that)
    then show "(0 < sqprojection x $ i) = (0 < x $ i)"
      by (simp add: sqprojection_def zero_less_mult_iff)
    show "(sqprojection x $ i < 0) = (x $ i < 0)"
      unfolding sqprojection_def
        by (metis * pos_less_divideR_eq scaleR_zero_right vector_scaleR_component)
  qed
  have x1: "x $ 1 \<in> {- 1..1::real}" "x $ 2 \<in> {- 1..1::real}"
    using x(1) unfolding mem_box_cart by auto
  then have nz: "f (x $ 1) - g (x $ 2) \<noteq> 0"
    using as by auto
  consider "x $ 1 = -1" | "x $ 1 = 1" | "x $ 2 = -1" | "x $ 2 = 1"
    using nx unfolding infnorm_eq_1_2 by auto
  then show False
  proof cases
    case 1
    then have *: "f (x $ 1) $ 1 = - 1"
      using assms(5) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 1 > 0"
      by (smt (verit) "1" negatex_def o_apply vector_2(1) x(2))
    moreover
    from x1 have "g (x $ 2) \<in> cbox (-1) 1"
      using assms(2) by blast
    ultimately show False
      unfolding iff[OF nz] vector_component_simps * mem_box_cart
      using not_le by auto
  next
    case 2
    then have *: "f (x $ 1) $ 1 = 1"
      using assms(6) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 1 < 0"
      by (smt (verit) "2" negatex_def o_apply vector_2(1) x(2) zero_less_one)
    moreover have "g (x $ 2) \<in> cbox (-1) 1"
      using assms(2) x1 by blast
    ultimately show False
      unfolding iff[OF nz] vector_component_simps * mem_box_cart
      using not_le by auto
  next
    case 3
    then have *: "g (x $ 2) $ 2 = - 1"
      using assms(7) by auto
    moreover have "sqprojection (f (x$1) - g (x$2)) $ 2 < 0"
      by (smt (verit, ccfv_SIG) "3" negatex_def o_apply vector_2(2) x(2))
    moreover from x1 have "f (x $ 1) \<in> cbox (-1) 1"
      using assms(1) by blast
    ultimately show False
      by (smt (verit, del_insts) iff(2) mem_box_cart(2) neg_one_index nz vector_minus_component)
  next
    case 4
    then have *: "g (x $ 2) $ 2 = 1"
      using assms(8) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 2 > 0"
      by (smt (verit, best) "4" negatex_def o_apply vector_2(2) x(2))
    moreover
    from x1 have "f (x $ 1) \<in> cbox (-1) 1"
      using assms(1) by blast
    ultimately show False
      by (smt (verit) "*" iff(1) mem_box_cart(2) nz one_index vector_minus_component)
  qed 
qed

proposition fashoda_unit_path:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox (-1) 1"
    and "path_image g \<subseteq> cbox (-1) 1"
    and "(pathstart f)$1 = -1"
    and "(pathfinish f)$1 = 1"
    and "(pathstart g)$2 = -1"
    and "(pathfinish g)$2 = 1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  note assms = assms[unfolded path_def pathstart_def pathfinish_def path_image_def]
  define iscale where [abs_def]: "iscale z = inverse 2 *\<^sub>R (z + 1)" for z :: real
  have isc: "iscale ` {- 1..1} \<subseteq> {0..1}"
    unfolding iscale_def by auto
  have "\<exists>s\<in>{- 1..1}. \<exists>t\<in>{- 1..1}. (f \<circ> iscale) s = (g \<circ> iscale) t"
  proof (rule fashoda_unit)
    show "(f \<circ> iscale) ` {- 1..1} \<subseteq> cbox (- 1) 1" "(g \<circ> iscale) ` {- 1..1} \<subseteq> cbox (- 1) 1"
      using isc and assms(3-4) by (auto simp add: image_comp [symmetric])
    have *: "continuous_on {- 1..1} iscale"
      unfolding iscale_def by (rule continuous_intros)+
    show "continuous_on {- 1..1} (f \<circ> iscale)"
      using "*" assms(1) continuous_on_compose continuous_on_subset isc by blast
    show "continuous_on {- 1..1} (g \<circ> iscale)"
      by (meson "*" assms(2) continuous_on_compose continuous_on_subset isc)
    have *: "(1 / 2) *\<^sub>R (1 + (1::real^1)) = 1"
      unfolding vec_eq_iff by auto
    show "(f \<circ> iscale) (- 1) $ 1 = - 1"
      and "(f \<circ> iscale) 1 $ 1 = 1"
      and "(g \<circ> iscale) (- 1) $ 2 = -1"
      and "(g \<circ> iscale) 1 $ 2 = 1"
      unfolding o_def iscale_def using assms by (auto simp add: *)
  qed
  then obtain s t where st: "s \<in> {- 1..1}" "t \<in> {- 1..1}" "(f \<circ> iscale) s = (g \<circ> iscale) t"
    by auto
  show thesis
  proof
    show "f (iscale s) \<in> path_image f"
      by (metis image_eqI image_subset_iff isc path_image_def st(1))
    show "f (iscale s) \<in> path_image g"
      by (metis comp_def image_eqI image_subset_iff isc path_image_def st(2) st(3))
  qed
qed

theorem fashoda:
  fixes b :: "real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox a b"
    and "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$1 = a$1"
    and "(pathfinish f)$1 = b$1"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = b$2"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  fix P Q S
  presume "P \<or> Q \<or> S" "P \<Longrightarrow> thesis" and "Q \<Longrightarrow> thesis" and "S \<Longrightarrow> thesis"
  then show thesis
    by auto
next
  have "cbox a b \<noteq> {}"
    using assms(3) using path_image_nonempty[of f] by auto
  then have "a \<le> b"
    unfolding interval_eq_empty_cart less_eq_vec_def by (auto simp add: not_less)
  then show "a$1 = b$1 \<or> a$2 = b$2 \<or> (a$1 < b$1 \<and> a$2 < b$2)"
    unfolding less_eq_vec_def forall_2 by auto
next
  assume as: "a$1 = b$1"
  have "\<exists>z\<in>path_image g. z$2 = (pathstart f)$2"
  proof (rule connected_ivt_component_cart)
    show "pathstart g $ 2 \<le> pathstart f $ 2"
      by (metis assms(3) assms(7) mem_box_cart(2) pathstart_in_path_image subset_iff)
    show "pathstart f $ 2 \<le> pathfinish g $ 2"
      by (metis assms(3) assms(8) in_mono mem_box_cart(2) pathstart_in_path_image)
    show "connected (path_image g)"
      using assms(2) by blast
  qed (auto simp: path_defs)
  then obtain z :: "real^2" where z: "z \<in> path_image g" "z $ 2 = pathstart f $ 2" ..
  have "z \<in> cbox a b"
    using assms(4) z(1) by blast
  then have "z = f 0"
    by (smt (verit) as assms(5) exhaust_2 mem_box_cart(2) nle_le pathstart_def vec_eq_iff z(2))
  then show thesis
    by (metis path_defs(2) pathstart_in_path_image that z(1))
next
  assume as: "a$2 = b$2"
  have "\<exists>z\<in>path_image f. z$1 = (pathstart g)$1"
  proof (rule connected_ivt_component_cart)
    show "pathstart f $ 1 \<le> pathstart g $ 1"
      using assms(4) assms(5) mem_box_cart(2) by fastforce
    show "pathstart g $ 1 \<le> pathfinish f $ 1"
      using assms(4) assms(6) mem_box_cart(2) pathstart_in_path_image by fastforce
    show "connected (path_image f)"
      by (simp add: assms(1) connected_path_image)
  qed (auto simp: path_defs)
  then obtain z where z: "z \<in> path_image f" "z $ 1 = pathstart g $ 1" ..
  have "z \<in> cbox a b"
    using assms(3) z(1) by auto
  then have "z = g 0"
    by (smt (verit) as assms(7) exhaust_2 mem_box_cart(2) pathstart_def vec_eq_iff z(2))
  then show thesis
    by (metis path_defs(2) pathstart_in_path_image that z(1))
next
  assume as: "a $ 1 < b $ 1 \<and> a $ 2 < b $ 2"
  have int_nem: "cbox (-1) (1::real^2) \<noteq> {}"
    unfolding interval_eq_empty_cart by auto
  obtain z :: "real^2" where z:
      "z \<in> (interval_bij (a, b) (- 1, 1) \<circ> f) ` {0..1}"
      "z \<in> (interval_bij (a, b) (- 1, 1) \<circ> g) ` {0..1}"
  proof (rule fashoda_unit_path)
    show "path (interval_bij (a, b) (- 1, 1) \<circ> f)"
      by (meson assms(1) continuous_on_interval_bij path_continuous_image)
    show "path (interval_bij (a, b) (- 1, 1) \<circ> g)"
      by (meson assms(2) continuous_on_interval_bij path_continuous_image)
    show "path_image (interval_bij (a, b) (- 1, 1) \<circ> f) \<subseteq> cbox (- 1) 1"
      using assms(3)
      by (simp add: path_image_def in_interval_interval_bij int_nem subset_eq)
    show "path_image (interval_bij (a, b) (- 1, 1) \<circ> g) \<subseteq> cbox (- 1) 1"
      using assms(4)
      by (simp add: path_image_def in_interval_interval_bij int_nem subset_eq)
    show "pathstart (interval_bij (a, b) (- 1, 1) \<circ> f) $ 1 = - 1"
         "pathfinish (interval_bij (a, b) (- 1, 1) \<circ> f) $ 1 = 1"
         "pathstart (interval_bij (a, b) (- 1, 1) \<circ> g) $ 2 = - 1"
         "pathfinish (interval_bij (a, b) (- 1, 1) \<circ> g) $ 2 = 1"
      using assms as
      by (simp_all add: cart_eq_inner_axis pathstart_def pathfinish_def interval_bij_def)
         (simp_all add: inner_axis)
  qed (auto simp: path_defs)
  then obtain zf zg where zf: "zf \<in> {0..1}" "z = (interval_bij (a, b) (- 1, 1) \<circ> f) zf" 
                    and zg: "zg \<in> {0..1}" "z = (interval_bij (a, b) (- 1, 1) \<circ> g) zg"
    by blast
  have *: "\<forall>i. (- 1) $ i < (1::real^2) $ i \<and> a $ i < b $ i"
    unfolding forall_2 using as by auto
  show thesis
  proof (rule_tac z="interval_bij (- 1,1) (a,b) z" in that)
    show "interval_bij (- 1, 1) (a, b) z \<in> path_image f"
      using zf by (simp add: interval_bij_bij_cart[OF *] path_image_def)
    show "interval_bij (- 1, 1) (a, b) z \<in> path_image g"
      using zg by (simp add: interval_bij_bij_cart[OF *] path_image_def)
  qed
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some slightly ad hoc lemmas I use below\<close>

lemma segment_vertical:
  fixes a :: "real^2"
  assumes "a$1 = b$1"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$1 = a$1 \<and> x$1 = b$1 \<and> (a$2 \<le> x$2 \<and> x$2 \<le> b$2 \<or> b$2 \<le> x$2 \<and> x$2 \<le> a$2)"
  (is "_ = ?R")
proof -
  let ?L = "\<exists>u. (x $ 1 = (1 - u) * a $ 1 + u * b $ 1 \<and> x $ 2 = (1 - u) * a $ 2 + u * b $ 2) \<and> 0 \<le> u \<and> u \<le> 1"
  {
    presume "?L \<Longrightarrow> ?R" and "?R \<Longrightarrow> ?L"
    then show ?thesis
      unfolding closed_segment_def mem_Collect_eq
      unfolding vec_eq_iff forall_2 scalar_mult_eq_scaleR[symmetric] vector_component_simps
      by blast
  }
  {
    assume ?L
    then obtain u where u:
        "x $ 1 = (1 - u) * a $ 1 + u * b $ 1"
        "x $ 2 = (1 - u) * a $ 2 + u * b $ 2"
        "0 \<le> u" "u \<le> 1"
      by blast
    { fix b a
      assume "b + u * a > a + u * b"
      then have "(1 - u) * b > (1 - u) * a"
        by (auto simp add:field_simps)
      then have "b \<ge> a"
        using not_less_iff_gr_or_eq u(4) by fastforce
      then have "u * a \<le> u * b"
        by (simp add: mult_left_mono u(3))
    } 
    moreover
    { fix a b
      assume "u * b > u * a"
      then have "(1 - u) * a \<le> (1 - u) * b"
        using less_eq_real_def u(3) u(4) by force
      then have "a + u * b \<le> b + u * a"
        by (auto simp add: field_simps)
    } ultimately show ?R
      by (force simp add: u assms field_simps not_le)
  }
  {
    assume ?R
    then show ?L
    proof (cases "x$2 = b$2")
      case True
      with \<open>?R\<close> show ?L
        by (rule_tac x="(x$2 - a$2) / (b$2 - a$2)" in exI) (auto simp add: field_simps)
    next
      case False
      with \<open>?R\<close> show ?L
          by (rule_tac x="1 - (x$2 - b$2) / (a$2 - b$2)" in exI) (auto simp add: field_simps)
    qed
  }
qed

text \<open>Essentially duplicate proof that could be done by swapping co-ordinates\<close>
lemma segment_horizontal:
  fixes a :: "real^2"
  assumes "a$2 = b$2"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$2 = a$2 \<and> x$2 = b$2 \<and> (a$1 \<le> x$1 \<and> x$1 \<le> b$1 \<or> b$1 \<le> x$1 \<and> x$1 \<le> a$1)"
  (is "_ = ?R")
proof -
  let ?L = "\<exists>u. (x $ 1 = (1 - u) * a $ 1 + u * b $ 1 \<and> x $ 2 = (1 - u) * a $ 2 + u * b $ 2) \<and> 0 \<le> u \<and> u \<le> 1"
  {
    presume "?L \<Longrightarrow> ?R" and "?R \<Longrightarrow> ?L"
    then show ?thesis
      unfolding closed_segment_def mem_Collect_eq
      unfolding vec_eq_iff forall_2 scalar_mult_eq_scaleR[symmetric] vector_component_simps
      by blast
  }
  {
    assume ?L
    then obtain u where u:
        "x $ 1 = (1 - u) * a $ 1 + u * b $ 1"
        "x $ 2 = (1 - u) * a $ 2 + u * b $ 2"
        "0 \<le> u" "u \<le> 1"
      by blast
    { fix b a
      assume "b + u * a > a + u * b"
      then have "(1 - u) * b > (1 - u) * a"
        by (auto simp add: field_simps)
      then have "b \<ge> a"
        by (smt (verit, best) mult_left_mono u(4))
      then have "u * a \<le> u * b"
        by (simp add: mult_left_mono u(3))
    } 
    moreover
    { fix a b
      assume "u * b > u * a"
      then have "(1 - u) * a \<le> (1 - u) * b"
        using less_eq_real_def u(3) u(4) by force
      then have "a + u * b \<le> b + u * a"
        by (auto simp add: field_simps)
    } 
    ultimately show ?R
      by (force simp add: u assms field_simps not_le intro: )
  }
  { assume ?R
    then show ?L
    proof (cases "x$1 = b$1")
      case True
      with \<open>?R\<close> show ?L
        by (rule_tac x="(x$1 - a$1) / (b$1 - a$1)" in exI) (auto simp add: field_simps)
    next
      case False
      with \<open>?R\<close> show ?L
        by (rule_tac x="1 - (x$1 - b$1) / (a$1 - b$1)" in exI) (auto simp add: field_simps)
    qed
  }
qed


subsection \<open>Useful Fashoda corollary pointed out to me by Tom Hales\<close>(*FIXME change title? *)

corollary fashoda_interlace:
  fixes a :: "real^2"
  assumes "path f"
    and "path g"
    and paf: "path_image f \<subseteq> cbox a b"
    and pag: "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$2 = a$2"
    and "(pathfinish f)$2 = a$2"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = a$2"
    and "(pathstart f)$1 < (pathstart g)$1"
    and "(pathstart g)$1 < (pathfinish f)$1"
    and "(pathfinish f)$1 < (pathfinish g)$1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  have "cbox a b \<noteq> {}"
    using path_image_nonempty[of f] using assms(3) by auto
  note ab=this[unfolded interval_eq_empty_cart not_ex forall_2 not_less]
  have "pathstart f \<in> cbox a b"
    and "pathfinish f \<in> cbox a b"
    and "pathstart g \<in> cbox a b"
    and "pathfinish g \<in> cbox a b"
    using pathstart_in_path_image pathfinish_in_path_image
    using assms(3-4)
    by auto
  note startfin = this[unfolded mem_box_cart forall_2]
  let ?P1 = "linepath (vector[a$1 - 2, a$2 - 2]) (vector[(pathstart f)$1,a$2 - 2]) +++
     linepath(vector[(pathstart f)$1,a$2 - 2])(pathstart f) +++ f +++
     linepath(pathfinish f)(vector[(pathfinish f)$1,a$2 - 2]) +++
     linepath(vector[(pathfinish f)$1,a$2 - 2])(vector[b$1 + 2,a$2 - 2])"
  let ?P2 = "linepath(vector[(pathstart g)$1, (pathstart g)$2 - 3])(pathstart g) +++ g +++
     linepath(pathfinish g)(vector[(pathfinish g)$1,a$2 - 1]) +++
     linepath(vector[(pathfinish g)$1,a$2 - 1])(vector[b$1 + 1,a$2 - 1]) +++
     linepath(vector[b$1 + 1,a$2 - 1])(vector[b$1 + 1,b$2 + 3])"
  let ?a = "vector[a$1 - 2, a$2 - 3]"
  let ?b = "vector[b$1 + 2, b$2 + 3]"
  have P1P2: "path_image ?P1 = path_image (linepath (vector[a$1 - 2, a$2 - 2]) (vector[(pathstart f)$1,a$2 - 2])) \<union>
      path_image (linepath(vector[(pathstart f)$1,a$2 - 2])(pathstart f)) \<union> path_image f \<union>
      path_image (linepath(pathfinish f)(vector[(pathfinish f)$1,a$2 - 2])) \<union>
      path_image (linepath(vector[(pathfinish f)$1,a$2 - 2])(vector[b$1 + 2,a$2 - 2]))"
    "path_image ?P2 = path_image(linepath(vector[(pathstart g)$1, (pathstart g)$2 - 3])(pathstart g)) \<union> path_image g \<union>
      path_image(linepath(pathfinish g)(vector[(pathfinish g)$1,a$2 - 1])) \<union>
      path_image(linepath(vector[(pathfinish g)$1,a$2 - 1])(vector[b$1 + 1,a$2 - 1])) \<union>
      path_image(linepath(vector[b$1 + 1,a$2 - 1])(vector[b$1 + 1,b$2 + 3]))" using assms(1-2)
      by(auto simp add: path_image_join)
  have abab: "cbox a b \<subseteq> cbox ?a ?b"
    unfolding interval_cbox_cart[symmetric]
    by (auto simp add:less_eq_vec_def forall_2)
  obtain z where
    "z \<in> path_image
          (linepath (vector [a $ 1 - 2, a $ 2 - 2]) (vector [pathstart f $ 1, a $ 2 - 2]) +++
           linepath (vector [pathstart f $ 1, a $ 2 - 2]) (pathstart f) +++
           f +++
           linepath (pathfinish f) (vector [pathfinish f $ 1, a $ 2 - 2]) +++
           linepath (vector [pathfinish f $ 1, a $ 2 - 2]) (vector [b $ 1 + 2, a $ 2 - 2]))"
    "z \<in> path_image
          (linepath (vector [pathstart g $ 1, pathstart g $ 2 - 3]) (pathstart g) +++
           g +++
           linepath (pathfinish g) (vector [pathfinish g $ 1, a $ 2 - 1]) +++
           linepath (vector [pathfinish g $ 1, a $ 2 - 1]) (vector [b $ 1 + 1, a $ 2 - 1]) +++
           linepath (vector [b $ 1 + 1, a $ 2 - 1]) (vector [b $ 1 + 1, b $ 2 + 3]))"
    apply (rule fashoda[of ?P1 ?P2 ?a ?b])
    unfolding pathstart_join pathfinish_join pathstart_linepath pathfinish_linepath vector_2
  proof -
    show "path ?P1" and "path ?P2"
      using assms by auto
    show "path_image ?P1 \<subseteq> cbox ?a ?b" "path_image ?P2 \<subseteq> cbox ?a ?b"
      unfolding P1P2 path_image_linepath using startfin paf pag
      by (auto simp: mem_box_cart segment_horizontal segment_vertical forall_2)
    show "a $ 1 - 2 = a $ 1 - 2"
      and "b $ 1 + 2 = b $ 1 + 2"
      and "pathstart g $ 2 - 3 = a $ 2 - 3"
      and "b $ 2 + 3 = b $ 2 + 3"
      by (auto simp add: assms)
  qed
  note z=this[unfolded P1P2 path_image_linepath]
  show thesis
  proof (rule that[of z])
    have "(z \<in> closed_segment (vector [a $ 1 - 2, a $ 2 - 2]) (vector [pathstart f $ 1, a $ 2 - 2]) \<or>
      z \<in> closed_segment (vector [pathstart f $ 1, a $ 2 - 2]) (pathstart f)) \<or>
      z \<in> closed_segment (pathfinish f) (vector [pathfinish f $ 1, a $ 2 - 2]) \<or>
      z \<in> closed_segment (vector [pathfinish f $ 1, a $ 2 - 2]) (vector [b $ 1 + 2, a $ 2 - 2]) \<Longrightarrow>
    (((z \<in> closed_segment (vector [pathstart g $ 1, pathstart g $ 2 - 3]) (pathstart g)) \<or>
      z \<in> closed_segment (pathfinish g) (vector [pathfinish g $ 1, a $ 2 - 1])) \<or>
      z \<in> closed_segment (vector [pathfinish g $ 1, a $ 2 - 1]) (vector [b $ 1 + 1, a $ 2 - 1])) \<or>
      z \<in> closed_segment (vector [b $ 1 + 1, a $ 2 - 1]) (vector [b $ 1 + 1, b $ 2 + 3]) \<Longrightarrow> False"
    proof (simp only: segment_vertical segment_horizontal vector_2, goal_cases)
      case prems: 1
      have "pathfinish f \<in> cbox a b"
        using assms(3) pathfinish_in_path_image[of f] by auto
      then have "1 + b $ 1 \<le> pathfinish f $ 1 \<Longrightarrow> False"
        unfolding mem_box_cart forall_2 by auto
      then have "z$1 \<noteq> pathfinish f$1"
        using assms(10) assms(11) prems(2) by auto
      moreover have "pathstart f \<in> cbox a b"
        using assms(3) pathstart_in_path_image[of f]
        by auto
      then have "1 + b $ 1 \<le> pathstart f $ 1 \<Longrightarrow> False"
        unfolding mem_box_cart forall_2
        by auto
      then have "z$1 \<noteq> pathstart f$1"
        using prems(2) using assms ab
        by (auto simp add: field_simps)
      ultimately have *: "z$2 = a$2 - 2"
        using prems(1) by auto
      have "z$1 \<noteq> pathfinish g$1"
        using prems(2) assms ab
        by (auto simp add: field_simps *)
      moreover have "pathstart g \<in> cbox a b"
        using assms(4) pathstart_in_path_image[of g]
        by auto
      note this[unfolded mem_box_cart forall_2]
      then have "z$1 \<noteq> pathstart g$1"
        using prems(1) assms ab
        by (auto simp add: field_simps *)
      ultimately have "a $ 2 - 1 \<le> z $ 2 \<and> z $ 2 \<le> b $ 2 + 3 \<or> b $ 2 + 3 \<le> z $ 2 \<and> z $ 2 \<le> a $ 2 - 1"
        using prems(2)  unfolding * assms by (auto simp add: field_simps)
      then show False
        unfolding * using ab by auto
    qed
    then have "z \<in> path_image f \<or> z \<in> path_image g"
      using z unfolding Un_iff by blast
    then have z': "z \<in> cbox a b"
      using assms(3-4) by auto
    have "a $ 2 = z $ 2 \<Longrightarrow> (z $ 1 = pathstart f $ 1 \<or> z $ 1 = pathfinish f $ 1) \<Longrightarrow>
      z = pathstart f \<or> z = pathfinish f"
      unfolding vec_eq_iff forall_2 assms
      by auto
    with z' show "z \<in> path_image f"
      using z(1)
      unfolding Un_iff mem_box_cart forall_2
      using assms(5) assms(6) segment_horizontal segment_vertical by auto
    have "a $ 2 = z $ 2 \<Longrightarrow> (z $ 1 = pathstart g $ 1 \<or> z $ 1 = pathfinish g $ 1) \<Longrightarrow>
      z = pathstart g \<or> z = pathfinish g"
      unfolding vec_eq_iff forall_2 assms
      by auto
    with z' show "z \<in> path_image g"
      using z(2)
      unfolding Un_iff mem_box_cart forall_2
      using assms(7) assms(8) segment_horizontal segment_vertical by auto
  qed
qed

end

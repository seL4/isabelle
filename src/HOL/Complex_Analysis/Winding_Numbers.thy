section \<open>Winding numbers\<close>
theory Winding_Numbers
  imports Cauchy_Integral_Theorem
begin

subsection \<open>Definition\<close>

definition\<^marker>\<open>tag important\<close> winding_number_prop :: "[real \<Rightarrow> complex, complex, real, real \<Rightarrow> complex, complex] \<Rightarrow> bool" where
  "winding_number_prop \<gamma> z e p n \<equiv>
      valid_path p \<and> z \<notin> path_image p \<and>
      pathstart p = pathstart \<gamma> \<and>
      pathfinish p = pathfinish \<gamma> \<and>
      (\<forall>t \<in> {0..1}. norm(\<gamma> t - p t) < e) \<and>
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"

definition\<^marker>\<open>tag important\<close> winding_number:: "[real \<Rightarrow> complex, complex] \<Rightarrow> complex" where
  "winding_number \<gamma> z \<equiv> SOME n. \<forall>e > 0. \<exists>p. winding_number_prop \<gamma> z e p n"


lemma winding_number:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>" "0 < e"
    shows "\<exists>p. winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain d
    where d: "d>0"
      and pi_eq: "\<And>h1 h2. valid_path h1 \<and> valid_path h2 \<and>
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < d \<and> cmod (h2 t - \<gamma> t) < d) \<and>
                    pathstart h2 = pathstart h1 \<and> pathfinish h2 = pathfinish h1 \<longrightarrow>
                      path_image h1 \<subseteq> UNIV - {z} \<and> path_image h2 \<subseteq> UNIV - {z} \<and>
                      (\<forall>f. f holomorphic_on UNIV - {z} \<longrightarrow> contour_integral h2 f = contour_integral h1 f)"
    using contour_integral_nearby_ends [of "UNIV - {z}" \<gamma>] assms by (auto simp: open_delete)
  then obtain h where h: "polynomial_function h \<and> pathstart h = pathstart \<gamma> \<and> pathfinish h = pathfinish \<gamma> \<and>
                          (\<forall>t \<in> {0..1}. norm(h t - \<gamma> t) < d/2)"
    using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "d/2"] d by (metis half_gt_zero_iff)
  define nn where "nn = 1/(2* pi*\<i>) * contour_integral h (\<lambda>w. 1/(w - z))"
  have "\<exists>n. \<forall>e > 0. \<exists>p. winding_number_prop \<gamma> z e p n"
    proof (rule_tac x=nn in exI, clarify)
      fix e::real
      assume e: "e>0"
      obtain p where p: "polynomial_function p \<and>
            pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and> (\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < min e (d/2))"
        using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "min e (d/2)"] d \<open>0<e\<close>
        by (metis min_less_iff_conj zero_less_divide_iff zero_less_numeral) 
      have "(\<lambda>w. 1 / (w - z)) holomorphic_on UNIV - {z}"
        by (auto simp: intro!: holomorphic_intros)
      then have "winding_number_prop \<gamma> z e p nn"
        using pi_eq [of h p] h p d
        by (auto simp: valid_path_polynomial_function norm_minus_commute nn_def winding_number_prop_def)
      then show "\<exists>p. winding_number_prop \<gamma> z e p nn" 
        by metis
    qed
  then show ?thesis
    unfolding winding_number_def by (rule someI2_ex) (blast intro: \<open>0<e\<close>)
qed

lemma winding_number_unique:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and pi: "\<And>e. e>0 \<Longrightarrow> \<exists>p. winding_number_prop \<gamma> z e p n"
   shows "winding_number \<gamma> z = n"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain e
    where e: "e>0"
      and pi_eq: "\<And>h1 h2 f. \<lbrakk>valid_path h1; valid_path h2;
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < e \<and> cmod (h2 t - \<gamma> t) < e);
                    pathstart h2 = pathstart h1; pathfinish h2 = pathfinish h1; f holomorphic_on UNIV - {z}\<rbrakk> \<Longrightarrow>
                    contour_integral h2 f = contour_integral h1 f"
    using contour_integral_nearby_ends [of "UNIV - {z}" \<gamma>] assms  by (auto simp: open_delete)
  obtain p where p: "winding_number_prop \<gamma> z e p n"
    using pi [OF e] by blast
  obtain q where q: "winding_number_prop \<gamma> z e q (winding_number \<gamma> z)"
    using winding_number [OF \<gamma> e] by blast
  have "2 * complex_of_real pi * \<i> * n = contour_integral p (\<lambda>w. 1 / (w - z))"
    using p by (auto simp: winding_number_prop_def)
  also have "\<dots> = contour_integral q (\<lambda>w. 1 / (w - z))"
  proof (rule pi_eq)
    show "(\<lambda>w. 1 / (w - z)) holomorphic_on UNIV - {z}"
      by (auto intro!: holomorphic_intros)
  qed (use p q in \<open>auto simp: winding_number_prop_def norm_minus_commute\<close>)
  also have "\<dots> = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z"
    using q by (auto simp: winding_number_prop_def)
  finally have "2 * complex_of_real pi * \<i> * n = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z" .
  then show ?thesis
    by simp
qed

(*NB not winding_number_prop here due to the loop in p*)
lemma winding_number_unique_loop:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and pi:
        "\<And>e. e>0 \<Longrightarrow> \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                           pathfinish p = pathstart p \<and>
                           (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
                           contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
   shows "winding_number \<gamma> z = n"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain e
    where e: "e>0"
      and pi_eq: "\<And>h1 h2 f. \<lbrakk>valid_path h1; valid_path h2;
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < e \<and> cmod (h2 t - \<gamma> t) < e);
                    pathfinish h1 = pathstart h1; pathfinish h2 = pathstart h2; f holomorphic_on UNIV - {z}\<rbrakk> \<Longrightarrow>
                    contour_integral h2 f = contour_integral h1 f"
    using contour_integral_nearby_loops [of "UNIV - {z}" \<gamma>] assms  by (auto simp: open_delete)
  obtain p where p:
     "valid_path p \<and> z \<notin> path_image p \<and> pathfinish p = pathstart p \<and>
      (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
    using pi [OF e] by blast
  obtain q where q: "winding_number_prop \<gamma> z e q (winding_number \<gamma> z)"
    using winding_number [OF \<gamma> e] by blast
  have "2 * complex_of_real pi * \<i> * n = contour_integral p (\<lambda>w. 1 / (w - z))"
    using p by auto
  also have "\<dots> = contour_integral q (\<lambda>w. 1 / (w - z))"
  proof (rule pi_eq)
    show "(\<lambda>w. 1 / (w - z)) holomorphic_on UNIV - {z}"
      by (auto intro!: holomorphic_intros)
  qed (use p q loop in \<open>auto simp: winding_number_prop_def norm_minus_commute\<close>)
  also have "\<dots> = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z"
    using q by (auto simp: winding_number_prop_def)
  finally have "2 * complex_of_real pi * \<i> * n = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z" .
  then show ?thesis
    by simp
qed

proposition winding_number_valid_path:
  assumes "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
  shows "winding_number \<gamma> z = 1/(2*pi*\<i>) * contour_integral \<gamma> (\<lambda>w. 1/(w - z))"
  by (rule winding_number_unique)
  (use assms in \<open>auto simp: valid_path_imp_path winding_number_prop_def\<close>)

proposition has_contour_integral_winding_number:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "((\<lambda>w. 1/(w - z)) has_contour_integral (2*pi*\<i>*winding_number \<gamma> z)) \<gamma>"
by (simp add: winding_number_valid_path has_contour_integral_integral contour_integrable_inversediff assms)

lemma winding_number_trivial [simp]: "z \<noteq> a \<Longrightarrow> winding_number(linepath a a) z = 0"
  by (simp add: winding_number_valid_path)

lemma winding_number_subpath_trivial [simp]: "z \<noteq> g x \<Longrightarrow> winding_number (subpath x x g) z = 0"
  by (simp add: path_image_subpath winding_number_valid_path)

lemma winding_number_join:
  assumes \<gamma>1: "path \<gamma>1" "z \<notin> path_image \<gamma>1"
      and \<gamma>2: "path \<gamma>2" "z \<notin> path_image \<gamma>2"
      and "pathfinish \<gamma>1 = pathstart \<gamma>2"
    shows "winding_number(\<gamma>1 +++ \<gamma>2) z = winding_number \<gamma>1 z + winding_number \<gamma>2 z"
proof (rule winding_number_unique)
  show "\<exists>p. winding_number_prop (\<gamma>1 +++ \<gamma>2) z e p
              (winding_number \<gamma>1 z + winding_number \<gamma>2 z)" if "e > 0" for e
  proof -
    obtain p1 where "winding_number_prop \<gamma>1 z e p1 (winding_number \<gamma>1 z)"
      using \<open>0 < e\<close> \<gamma>1 winding_number by blast
    moreover
    obtain p2 where "winding_number_prop \<gamma>2 z e p2 (winding_number \<gamma>2 z)"
      using \<open>0 < e\<close> \<gamma>2 winding_number by blast
    ultimately
    have "winding_number_prop (\<gamma>1+++\<gamma>2) z e (p1+++p2) (winding_number \<gamma>1 z + winding_number \<gamma>2 z)"
      using assms
      apply (simp add: winding_number_prop_def not_in_path_image_join contour_integrable_inversediff algebra_simps)
      apply (auto simp: joinpaths_def)
      done
    then show ?thesis
      by blast
  qed
qed (use assms in \<open>auto simp: not_in_path_image_join\<close>)

lemma winding_number_reversepath:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "winding_number(reversepath \<gamma>) z = - (winding_number \<gamma> z)"
proof (rule winding_number_unique)
  show "\<exists>p. winding_number_prop (reversepath \<gamma>) z e p (- winding_number \<gamma> z)" if "e > 0" for e
  proof -
    obtain p where "winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
      using \<open>0 < e\<close> assms winding_number by blast
    then have "winding_number_prop (reversepath \<gamma>) z e (reversepath p) (- winding_number \<gamma> z)"
      using assms
      apply (simp add: winding_number_prop_def contour_integral_reversepath contour_integrable_inversediff valid_path_imp_reverse)
      apply (auto simp: reversepath_def)
      done
    then show ?thesis
      by blast
  qed
qed (use assms in auto)

lemma winding_number_shiftpath:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and "pathfinish \<gamma> = pathstart \<gamma>" "a \<in> {0..1}"
    shows "winding_number(shiftpath a \<gamma>) z = winding_number \<gamma> z"
proof (rule winding_number_unique_loop)
  show "\<exists>p. valid_path p \<and> z \<notin> path_image p \<and> pathfinish p = pathstart p \<and>
            (\<forall>t\<in>{0..1}. cmod (shiftpath a \<gamma> t - p t) < e) \<and>
            contour_integral p (\<lambda>w. 1 / (w - z)) =
            complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    if "e > 0" for e
  proof -
    obtain p where "winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
      using \<open>0 < e\<close> assms winding_number by blast
    then show ?thesis
      apply (rule_tac x="shiftpath a p" in exI)
      using assms that
      apply (auto simp: winding_number_prop_def path_image_shiftpath pathfinish_shiftpath pathstart_shiftpath contour_integral_shiftpath)
      apply (simp add: shiftpath_def)
      done
  qed
qed (use assms in \<open>auto simp: path_shiftpath path_image_shiftpath pathfinish_shiftpath pathstart_shiftpath\<close>)

lemma winding_number_split_linepath:
  assumes "c \<in> closed_segment a b" "z \<notin> closed_segment a b"
    shows "winding_number(linepath a b) z = winding_number(linepath a c) z + winding_number(linepath c b) z"
proof -
  have "z \<notin> closed_segment a c" "z \<notin> closed_segment c b"
    using assms  by (meson convex_contains_segment convex_segment ends_in_segment subsetCE)+
  then show ?thesis
    using assms
    by (simp add: winding_number_valid_path contour_integral_split_linepath [symmetric] continuous_on_inversediff field_simps)
qed

lemma winding_number_cong:
   "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> p t = q t) \<Longrightarrow> winding_number p z = winding_number q z"
  by (simp add: winding_number_def winding_number_prop_def pathstart_def pathfinish_def)

lemma winding_number_constI:
  assumes "c\<noteq>z" "\<And>t. \<lbrakk>0\<le>t; t\<le>1\<rbrakk> \<Longrightarrow> g t = c" 
  shows "winding_number g z = 0"
proof -
  have "winding_number g z = winding_number (linepath c c) z"
    apply (rule winding_number_cong)
    using assms unfolding linepath_def by auto
  moreover have "winding_number (linepath c c) z =0"
    apply (rule winding_number_trivial)
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma winding_number_offset: "winding_number p z = winding_number (\<lambda>w. p w - z) 0"
  unfolding winding_number_def
proof (intro ext arg_cong [where f = Eps] arg_cong [where f = All] imp_cong refl, safe)
  fix n e g
  assume "0 < e" and g: "winding_number_prop p z e g n"
  then show "\<exists>r. winding_number_prop (\<lambda>w. p w - z) 0 e r n"
    by (rule_tac x="\<lambda>t. g t - z" in exI)
       (force simp: winding_number_prop_def contour_integral_integral valid_path_def path_defs
                vector_derivative_def has_vector_derivative_diff_const piecewise_C1_differentiable_diff C1_differentiable_imp_piecewise)
next
  fix n e g
  assume "0 < e" and g: "winding_number_prop (\<lambda>w. p w - z) 0 e g n"
  then show "\<exists>r. winding_number_prop p z e r n"
    apply (rule_tac x="\<lambda>t. g t + z" in exI)
    apply (simp add: winding_number_prop_def contour_integral_integral valid_path_def path_defs
        piecewise_C1_differentiable_add vector_derivative_def has_vector_derivative_add_const C1_differentiable_imp_piecewise)
    apply (force simp: algebra_simps)
    done
qed

lemma winding_number_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and 0: "0 \<notin> path_image \<gamma>"
  shows "winding_number(uminus \<circ> \<gamma>) 0 = winding_number \<gamma> 0"
proof -
  have "(/) 1 contour_integrable_on \<gamma>"
    using "0" \<gamma> contour_integrable_inversediff by fastforce
  then have "((\<lambda>z. 1/z) has_contour_integral contour_integral \<gamma> ((/) 1)) \<gamma>"
    by (rule has_contour_integral_integral)
  then have "((\<lambda>z. 1 / - z) has_contour_integral - contour_integral \<gamma> ((/) 1)) \<gamma>"
    using has_contour_integral_neg by auto
  then show ?thesis
    using assms
    apply (simp add: winding_number_valid_path valid_path_negatepath image_def path_defs)
    apply (simp add: contour_integral_unique has_contour_integral_negatepath)
    done
qed

(* A combined theorem deducing several things piecewise.*)
lemma winding_number_join_pos_combined:
     "\<lbrakk>valid_path \<gamma>1; z \<notin> path_image \<gamma>1; 0 < Re(winding_number \<gamma>1 z);
       valid_path \<gamma>2; z \<notin> path_image \<gamma>2; 0 < Re(winding_number \<gamma>2 z); pathfinish \<gamma>1 = pathstart \<gamma>2\<rbrakk>
      \<Longrightarrow> valid_path(\<gamma>1 +++ \<gamma>2) \<and> z \<notin> path_image(\<gamma>1 +++ \<gamma>2) \<and> 0 < Re(winding_number(\<gamma>1 +++ \<gamma>2) z)"
  by (simp add: valid_path_join path_image_join winding_number_join valid_path_imp_path)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Useful sufficient conditions for the winding number to be positive\<close>

lemma Re_winding_number:
    "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>\<rbrakk>
     \<Longrightarrow> Re(winding_number \<gamma> z) = Im(contour_integral \<gamma> (\<lambda>w. 1/(w - z))) / (2*pi)"
by (simp add: winding_number_valid_path field_simps Re_divide power2_eq_square)

lemma winding_number_pos_le:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> 0 \<le> Im (vector_derivative \<gamma> (at x) * cnj(\<gamma> x - z))"
    shows "0 \<le> Re(winding_number \<gamma> z)"
proof -
  have ge0: "0 \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))" if x: "0 < x" "x < 1" for x
    using ge by (simp add: Complex.Im_divide algebra_simps x)
  let ?vd = "\<lambda>x. 1 / (\<gamma> x - z) * vector_derivative \<gamma> (at x)"
  let ?int = "\<lambda>z. contour_integral \<gamma> (\<lambda>w. 1 / (w - z))"
  have hi: "(?vd has_integral ?int z) (cbox 0 1)"
    unfolding box_real
    apply (subst has_contour_integral [symmetric])
    using \<gamma> by (simp add: contour_integrable_inversediff has_contour_integral_integral)
  have "0 \<le> Im (?int z)"
  proof (rule has_integral_component_nonneg [of \<i>, simplified])
    show "\<And>x. x \<in> cbox 0 1 \<Longrightarrow> 0 \<le> Im (if 0 < x \<and> x < 1 then ?vd x else 0)"
      by (force simp: ge0)
    show "((\<lambda>x. if 0 < x \<and> x < 1 then ?vd x else 0) has_integral ?int z) (cbox 0 1)"
      by (rule has_integral_spike_interior [OF hi]) simp
  qed
  then show ?thesis
    by (simp add: Re_winding_number [OF \<gamma>] field_simps)
qed

lemma winding_number_pos_lt_lemma:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and e: "0 < e"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> e \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
    shows "0 < Re(winding_number \<gamma> z)"
proof -
  let ?vd = "\<lambda>x. 1 / (\<gamma> x - z) * vector_derivative \<gamma> (at x)"
  let ?int = "\<lambda>z. contour_integral \<gamma> (\<lambda>w. 1 / (w - z))"
  have hi: "(?vd has_integral ?int z) (cbox 0 1)"
    unfolding box_real
    apply (subst has_contour_integral [symmetric])
    using \<gamma> by (simp add: contour_integrable_inversediff has_contour_integral_integral)
  have "e \<le> Im (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))"
  proof (rule has_integral_component_le [of \<i> "\<lambda>x. \<i>*e" "\<i>*e" "{0..1}", simplified])
    show "((\<lambda>x. if 0 < x \<and> x < 1 then ?vd x else \<i> * complex_of_real e) has_integral ?int z) {0..1}"
      by (rule has_integral_spike_interior [OF hi, simplified box_real]) (use e in simp)
    show "\<And>x. 0 \<le> x \<and> x \<le> 1 \<Longrightarrow>
              e \<le> Im (if 0 < x \<and> x < 1 then ?vd x else \<i> * complex_of_real e)"
      by (simp add: ge)
  qed (use has_integral_const_real [of _ 0 1] in auto)
  with e show ?thesis
    by (simp add: Re_winding_number [OF \<gamma>] field_simps)
qed

lemma winding_number_pos_lt:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and e: "0 < e"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> e \<le> Im (vector_derivative \<gamma> (at x) * cnj(\<gamma> x - z))"
    shows "0 < Re (winding_number \<gamma> z)"
proof -
  have bm: "bounded ((\<lambda>w. w - z) ` (path_image \<gamma>))"
    using bounded_translation [of _ "-z"] \<gamma> by (simp add: bounded_valid_path_image)
  then obtain B where B: "B > 0" and Bno: "\<And>x. x \<in> (\<lambda>w. w - z) ` (path_image \<gamma>) \<Longrightarrow> norm x \<le> B"
    using bounded_pos [THEN iffD1, OF bm] by blast
  { fix x::real  assume x: "0 < x" "x < 1"
    then have B2: "cmod (\<gamma> x - z)^2 \<le> B^2" using Bno [of "\<gamma> x - z"]
      by (simp add: path_image_def power2_eq_square mult_mono')
    with x have "\<gamma> x \<noteq> z" using \<gamma>
      using path_image_def by fastforce
    then have "e / B\<^sup>2 \<le> Im (vector_derivative \<gamma> (at x) * cnj (\<gamma> x - z)) / (cmod (\<gamma> x - z))\<^sup>2"
      using B ge [OF x] B2 e
      apply (rule_tac y="e / (cmod (\<gamma> x - z))\<^sup>2" in order_trans)
      apply (auto simp: divide_left_mono divide_right_mono)
      done
    then have "e / B\<^sup>2 \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
      by (simp add: complex_div_cnj [of _ "\<gamma> x - z" for x] del: complex_cnj_diff times_complex.sel)
  } note * = this
  show ?thesis
    using e B by (simp add: * winding_number_pos_lt_lemma [OF \<gamma>, of "e/B^2"])
qed

subsection\<open>The winding number is an integer\<close>

text\<open>Proof from the book Complex Analysis by Lars V. Ahlfors, Chapter 4, section 2.1,
     Also on page 134 of Serge Lang's book with the name title, etc.\<close>

lemma exp_fg:
  fixes z::complex
  assumes g: "(g has_vector_derivative g') (at x within s)"
      and f: "(f has_vector_derivative (g' / (g x - z))) (at x within s)"
      and z: "g x \<noteq> z"
    shows "((\<lambda>x. exp(-f x) * (g x - z)) has_vector_derivative 0) (at x within s)"
proof -
  have *: "(exp \<circ> (\<lambda>x. (- f x)) has_vector_derivative - (g' / (g x - z)) * exp (- f x)) (at x within s)"
    using assms unfolding has_vector_derivative_def scaleR_conv_of_real
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    apply (rule has_vector_derivative_eq_rhs)
    using z
    apply (auto intro!: derivative_eq_intros * [unfolded o_def] g)
    done
qed

lemma winding_number_exp_integral:
  fixes z::complex
  assumes \<gamma>: "\<gamma> piecewise_C1_differentiable_on {a..b}"
      and ab: "a \<le> b"
      and z: "z \<notin> \<gamma> ` {a..b}"
    shows "(\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)) integrable_on {a..b}"
          (is "?thesis1")
          "exp (- (integral {a..b} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))) * (\<gamma> b - z) = \<gamma> a - z"
          (is "?thesis2")
proof -
  let ?D\<gamma> = "\<lambda>x. vector_derivative \<gamma> (at x)"
  have [simp]: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<gamma> x \<noteq> z"
    using z by force
  have cong: "continuous_on {a..b} \<gamma>"
    using \<gamma> by (simp add: piecewise_C1_differentiable_on_def)
  obtain k where fink: "finite k" and g_C1_diff: "\<gamma> C1_differentiable_on ({a..b} - k)"
    using \<gamma> by (force simp: piecewise_C1_differentiable_on_def)
  have \<circ>: "open ({a<..<b} - k)"
    using \<open>finite k\<close> by (simp add: finite_imp_closed open_Diff)
  moreover have "{a<..<b} - k \<subseteq> {a..b} - k"
    by force
  ultimately have g_diff_at: "\<And>x. \<lbrakk>x \<notin> k; x \<in> {a<..<b}\<rbrakk> \<Longrightarrow> \<gamma> differentiable at x"
    by (metis Diff_iff differentiable_on_subset C1_diff_imp_diff [OF g_C1_diff] differentiable_on_def at_within_open)
  { fix w
    assume "w \<noteq> z"
    have "continuous_on (ball w (cmod (w - z))) (\<lambda>w. 1 / (w - z))"
      by (auto simp: dist_norm intro!: continuous_intros)
    moreover have "\<And>x. cmod (w - x) < cmod (w - z) \<Longrightarrow> \<exists>f'. ((\<lambda>w. 1 / (w - z)) has_field_derivative f') (at x)"
      by (auto simp: intro!: derivative_eq_intros)
    ultimately have "\<exists>h. \<forall>y. norm(y - w) < norm(w - z) \<longrightarrow> (h has_field_derivative 1/(y - z)) (at y)"
      using holomorphic_convex_primitive [of "ball w (norm(w - z))" "{}" "\<lambda>w. 1/(w - z)"]
      by (force simp: field_differentiable_def Ball_def dist_norm at_within_open_NO_MATCH norm_minus_commute)
  }
  then obtain h where h: "\<And>w y. w \<noteq> z \<Longrightarrow> norm(y - w) < norm(w - z) \<Longrightarrow> (h w has_field_derivative 1/(y - z)) (at y)"
    by meson
  have exy: "\<exists>y. ((\<lambda>x. inverse (\<gamma> x - z) * ?D\<gamma> x) has_integral y) {a..b}"
    unfolding integrable_on_def [symmetric]
  proof (rule contour_integral_local_primitive_any [OF piecewise_C1_imp_differentiable [OF \<gamma>]])
    show "\<exists>d h. 0 < d \<and>
               (\<forall>y. cmod (y - w) < d \<longrightarrow> (h has_field_derivative inverse (y - z))(at y within - {z}))"
          if "w \<in> - {z}" for w
      apply (rule_tac x="norm(w - z)" in exI)
      using that inverse_eq_divide has_field_derivative_at_within h
      by (metis Compl_insert DiffD2 insertCI right_minus_eq zero_less_norm_iff)
  qed simp
  have vg_int: "(\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)) integrable_on {a..b}"
    unfolding box_real [symmetric] divide_inverse_commute
    by (auto intro!: exy integrable_subinterval simp add: integrable_on_def ab)
  with ab show ?thesis1
    by (simp add: divide_inverse_commute integral_def integrable_on_def)
  { fix t
    assume t: "t \<in> {a..b}"
    have cball: "continuous_on (ball (\<gamma> t) (dist (\<gamma> t) z)) (\<lambda>x. inverse (x - z))"
        using z by (auto intro!: continuous_intros simp: dist_norm)
    have icd: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow> (\<lambda>w. inverse (w - z)) field_differentiable at x"
      unfolding field_differentiable_def by (force simp: intro!: derivative_eq_intros)
    obtain h where h: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow>
                       (h has_field_derivative inverse (x - z)) (at x within {y. cmod (\<gamma> t - y) < cmod (\<gamma> t - z)})"
      using holomorphic_convex_primitive [where f = "\<lambda>w. inverse(w - z)", OF convex_ball finite.emptyI cball icd]
      by simp (auto simp: ball_def dist_norm that)
    { fix x D
      assume x: "x \<notin> k" "a < x" "x < b"
      then have "x \<in> interior ({a..b} - k)"
        using open_subset_interior [OF \<circ>] by fastforce
      then have con: "isCont ?D\<gamma> x"
        using g_C1_diff x by (auto simp: C1_differentiable_on_eq intro: continuous_on_interior)
      then have con_vd: "continuous (at x within {a..b}) (\<lambda>x. ?D\<gamma> x)"
        by (rule continuous_at_imp_continuous_within)
      have gdx: "\<gamma> differentiable at x"
        using x by (simp add: g_diff_at)
      have "\<And>d. \<lbrakk>x \<notin> k; a < x; x < b;
          (\<gamma> has_vector_derivative d) (at x); a \<le> t; t \<le> b\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. integral {a..x}
                     (\<lambda>x. ?D\<gamma> x /
                           (\<gamma> x - z))) has_vector_derivative
              d / (\<gamma> x - z))
              (at x within {a..b})"
        apply (rule has_vector_derivative_eq_rhs)
         apply (rule integral_has_vector_derivative_continuous_at [where S = "{}", simplified])
        apply (rule con_vd continuous_intros cong vg_int | simp add: continuous_at_imp_continuous_within has_vector_derivative_continuous vector_derivative_at)+
        done
      then have "((\<lambda>c. exp (- integral {a..c} (\<lambda>x. ?D\<gamma> x / (\<gamma> x - z))) * (\<gamma> c - z)) has_derivative (\<lambda>h. 0))
          (at x within {a..b})"
        using x gdx t
        apply (clarsimp simp add: differentiable_iff_scaleR)
        apply (rule exp_fg [unfolded has_vector_derivative_def, simplified], blast intro: has_derivative_at_withinI)
        apply (simp_all add: has_vector_derivative_def [symmetric])
        done
      } note * = this
    have "exp (- (integral {a..t} (\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)))) * (\<gamma> t - z) =\<gamma> a - z"
      apply (rule has_derivative_zero_unique_strong_interval [of "{a,b} \<union> k" a b])
      using t
      apply (auto intro!: * continuous_intros fink cong indefinite_integral_continuous_1 [OF vg_int]  simp add: ab)+
      done
   }
  with ab show ?thesis2
    by (simp add: divide_inverse_commute integral_def)
qed

lemma winding_number_exp_2pi:
    "\<lbrakk>path p; z \<notin> path_image p\<rbrakk>
     \<Longrightarrow> pathfinish p - z = exp (2 * pi * \<i> * winding_number p z) * (pathstart p - z)"
using winding_number [of p z 1] unfolding valid_path_def path_image_def pathstart_def pathfinish_def winding_number_prop_def
  by (force dest: winding_number_exp_integral(2) [of _ 0 1 z] simp: field_simps contour_integral_integral exp_minus)

lemma integer_winding_number_eq:
  assumes \<gamma>: "path \<gamma>" and z: "z \<notin> path_image \<gamma>"
  shows "winding_number \<gamma> z \<in> \<int> \<longleftrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
proof -
  obtain p where p: "valid_path p" "z \<notin> path_image p"
                    "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>"
           and eq: "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF assms, of 1] unfolding winding_number_prop_def by auto
  then have wneq: "winding_number \<gamma> z = winding_number p z"
      using eq winding_number_valid_path by force
  have iff: "(winding_number \<gamma> z \<in> \<int>) \<longleftrightarrow> (exp (contour_integral p (\<lambda>w. 1 / (w - z))) = 1)"
    using eq by (simp add: exp_eq_1 complex_is_Int_iff)
  have "exp (contour_integral p (\<lambda>w. 1 / (w - z))) = (\<gamma> 1 - z) / (\<gamma> 0 - z)"
    using p winding_number_exp_integral(2) [of p 0 1 z]
    apply (simp add: valid_path_def path_defs contour_integral_integral exp_minus field_split_simps)
    by (metis path_image_def pathstart_def pathstart_in_path_image)
  then have "winding_number p z \<in> \<int> \<longleftrightarrow> pathfinish p = pathstart p"
    using p wneq iff by (auto simp: path_defs)
  then show ?thesis using p eq
    by (auto simp: winding_number_valid_path)
qed

theorem integer_winding_number:
  "\<lbrakk>path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> path_image \<gamma>\<rbrakk> \<Longrightarrow> winding_number \<gamma> z \<in> \<int>"
by (metis integer_winding_number_eq)


text\<open>If the winding number's magnitude is at least one, then the path must contain points in every direction.*)
   We can thus bound the winding number of a path that doesn't intersect a given ray. \<close>

lemma winding_number_pos_meets:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and 1: "Re (winding_number \<gamma> z) \<ge> 1"
      and w: "w \<noteq> z"
  shows "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image \<gamma>"
proof -
  have [simp]: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<gamma> x \<noteq> z"
    using z by (auto simp: path_image_def)
  have [simp]: "z \<notin> \<gamma> ` {0..1}"
    using path_image_def z by auto
  have gpd: "\<gamma> piecewise_C1_differentiable_on {0..1}"
    using \<gamma> valid_path_def by blast
  define r where "r = (w - z) / (\<gamma> 0 - z)"
  have [simp]: "r \<noteq> 0"
    using w z by (auto simp: r_def)
  have cont: "continuous_on {0..1}
     (\<lambda>x. Im (integral {0..x} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z))))"
    by (intro continuous_intros indefinite_integral_continuous_1 winding_number_exp_integral [OF gpd]; simp)
  have "Arg2pi r \<le> 2*pi"
    by (simp add: Arg2pi less_eq_real_def)
  also have "\<dots> \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))"
    using 1
    apply (simp add: winding_number_valid_path [OF \<gamma> z] contour_integral_integral)
    apply (simp add: Complex.Re_divide field_simps power2_eq_square)
    done
  finally have "Arg2pi r \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))" .
  then have "\<exists>t. t \<in> {0..1} \<and> Im(integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg2pi r"
    by (simp add: Arg2pi_ge_0 cont IVT')
  then obtain t where t:     "t \<in> {0..1}"
                  and eqArg: "Im (integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg2pi r"
    by blast
  define i where "i = integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
  have iArg: "Arg2pi r = Im i"
    using eqArg by (simp add: i_def)
  have gpdt: "\<gamma> piecewise_C1_differentiable_on {0..t}"
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff order_refl piecewise_C1_differentiable_on_subset gpd t)
  have "exp (- i) * (\<gamma> t - z) = \<gamma> 0 - z"
    unfolding i_def
    apply (rule winding_number_exp_integral [OF gpdt])
    using t z unfolding path_image_def by force+
  then have *: "\<gamma> t - z = exp i * (\<gamma> 0 - z)"
    by (simp add: exp_minus field_simps)
  then have "(w - z) = r * (\<gamma> 0 - z)"
    by (simp add: r_def)
  then have "z + complex_of_real (exp (Re i)) * (w - z) / complex_of_real (cmod r) = \<gamma> t"
    apply simp
    apply (subst Complex_Transcendental.Arg2pi_eq [of r])
    apply (simp add: iArg)
    using * apply (simp add: exp_eq_polar field_simps)
    done
  with t show ?thesis
    by (rule_tac x="exp(Re i) / norm r" in exI) (auto simp: path_image_def)
qed

lemma winding_number_big_meets:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "\<bar>Re (winding_number \<gamma> z)\<bar> \<ge> 1"
      and w: "w \<noteq> z"
  shows "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image \<gamma>"
proof -
  { assume "Re (winding_number \<gamma> z) \<le> - 1"
    then have "Re (winding_number (reversepath \<gamma>) z) \<ge> 1"
      by (simp add: \<gamma> valid_path_imp_path winding_number_reversepath z)
    moreover have "valid_path (reversepath \<gamma>)"
      using \<gamma> valid_path_imp_reverse by auto
    moreover have "z \<notin> path_image (reversepath \<gamma>)"
      by (simp add: z)
    ultimately have "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image (reversepath \<gamma>)"
      using winding_number_pos_meets w by blast
    then have ?thesis
      by simp
  }
  then show ?thesis
    using assms
    by (simp add: abs_if winding_number_pos_meets split: if_split_asm)
qed

lemma winding_number_less_1:
  fixes z::complex
  shows
  "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>; w \<noteq> z;
    \<And>a::real. 0 < a \<Longrightarrow> z + a*(w - z) \<notin> path_image \<gamma>\<rbrakk>
   \<Longrightarrow> Re(winding_number \<gamma> z) < 1"
   by (auto simp: not_less dest: winding_number_big_meets)

text\<open>One way of proving that WN=1 for a loop.\<close>
lemma winding_number_eq_1:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and 0: "0 < Re(winding_number \<gamma> z)" and 2: "Re(winding_number \<gamma> z) < 2"
  shows "winding_number \<gamma> z = 1"
proof -
  have "winding_number \<gamma> z \<in> Ints"
    by (simp add: \<gamma> integer_winding_number loop valid_path_imp_path z)
  then show ?thesis
    using 0 2 by (auto simp: Ints_def)
qed

subsection\<open>Continuity of winding number and invariance on connected sets\<close>

lemma continuous_at_winding_number:
  fixes z::complex
  assumes \<gamma>: "path \<gamma>" and z: "z \<notin> path_image \<gamma>"
  shows "continuous (at z) (winding_number \<gamma>)"
proof -
  obtain e where "e>0" and cbg: "cball z e \<subseteq> - path_image \<gamma>"
    using open_contains_cball [of "- path_image \<gamma>"]  z
    by (force simp: closed_def [symmetric] closed_path_image [OF \<gamma>])
  then have ppag: "path_image \<gamma> \<subseteq> - cball z (e/2)"
    by (force simp: cball_def dist_norm)
  have oc: "open (- cball z (e / 2))"
    by (simp add: closed_def [symmetric])
  obtain d where "d>0" and pi_eq:
    "\<And>h1 h2. \<lbrakk>valid_path h1; valid_path h2;
              (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < d \<and> cmod (h2 t - \<gamma> t) < d);
              pathstart h2 = pathstart h1; pathfinish h2 = pathfinish h1\<rbrakk>
             \<Longrightarrow>
               path_image h1 \<subseteq> - cball z (e / 2) \<and>
               path_image h2 \<subseteq> - cball z (e / 2) \<and>
               (\<forall>f. f holomorphic_on - cball z (e / 2) \<longrightarrow> contour_integral h2 f = contour_integral h1 f)"
    using contour_integral_nearby_ends [OF oc \<gamma> ppag] by metis
  obtain p where p: "valid_path p" "z \<notin> path_image p"
                    "pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma>"
              and pg: "\<And>t. t\<in>{0..1} \<Longrightarrow> cmod (\<gamma> t - p t) < min d e / 2"
              and pi: "contour_integral p (\<lambda>x. 1 / (x - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF \<gamma> z, of "min d e / 2"] \<open>d>0\<close> \<open>e>0\<close> by (auto simp: winding_number_prop_def)
  { fix w
    assume d2: "cmod (w - z) < d/2" and e2: "cmod (w - z) < e/2"
    then have wnotp: "w \<notin> path_image p"
      using cbg \<open>d>0\<close> \<open>e>0\<close>
      apply (simp add: path_image_def cball_def dist_norm, clarify)
      apply (frule pg)
      apply (drule_tac c="\<gamma> x" in subsetD)
      apply (auto simp: less_eq_real_def norm_minus_commute norm_triangle_half_l)
      done
    have wnotg: "w \<notin> path_image \<gamma>"
      using cbg e2 \<open>e>0\<close> by (force simp: dist_norm norm_minus_commute)
    { fix k::real
      assume k: "k>0"
      then obtain q where q: "valid_path q" "w \<notin> path_image q"
                             "pathstart q = pathstart \<gamma> \<and> pathfinish q = pathfinish \<gamma>"
                    and qg: "\<And>t. t \<in> {0..1} \<Longrightarrow> cmod (\<gamma> t - q t) < min k (min d e) / 2"
                    and qi: "contour_integral q (\<lambda>u. 1 / (u - w)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> w"
        using winding_number [OF \<gamma> wnotg, of "min k (min d e) / 2"] \<open>d>0\<close> \<open>e>0\<close> k
        by (force simp: min_divide_distrib_right winding_number_prop_def)
      have "contour_integral p (\<lambda>u. 1 / (u - w)) = contour_integral q (\<lambda>u. 1 / (u - w))"
        apply (rule pi_eq [OF \<open>valid_path q\<close> \<open>valid_path p\<close>, THEN conjunct2, THEN conjunct2, rule_format])
        apply (frule pg)
        apply (frule qg)
        using p q \<open>d>0\<close> e2
        apply (auto simp: dist_norm norm_minus_commute intro!: holomorphic_intros)
        done
      then have "contour_integral p (\<lambda>x. 1 / (x - w)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> w"
        by (simp add: pi qi)
    } note pip = this
    have "path p"
      using p by (simp add: valid_path_imp_path)
    then have "winding_number p w = winding_number \<gamma> w"
      apply (rule winding_number_unique [OF _ wnotp])
      apply (rule_tac x=p in exI)
      apply (simp add: p wnotp min_divide_distrib_right pip winding_number_prop_def)
      done
  } note wnwn = this
  obtain pe where "pe>0" and cbp: "cball z (3 / 4 * pe) \<subseteq> - path_image p"
    using p open_contains_cball [of "- path_image p"]
    by (force simp: closed_def [symmetric] closed_path_image [OF valid_path_imp_path])
  obtain L
    where "L>0"
      and L: "\<And>f B. \<lbrakk>f holomorphic_on - cball z (3 / 4 * pe);
                      \<forall>z \<in> - cball z (3 / 4 * pe). cmod (f z) \<le> B\<rbrakk> \<Longrightarrow>
                      cmod (contour_integral p f) \<le> L * B"
    using contour_integral_bound_exists [of "- cball z (3/4*pe)" p] cbp \<open>valid_path p\<close> by blast
  { fix e::real and w::complex
    assume e: "0 < e" and w: "cmod (w - z) < pe/4" "cmod (w - z) < e * pe\<^sup>2 / (8 * L)"
    then have [simp]: "w \<notin> path_image p"
      using cbp p(2) \<open>0 < pe\<close>
      by (force simp: dist_norm norm_minus_commute path_image_def cball_def)
    have [simp]: "contour_integral p (\<lambda>x. 1/(x - w)) - contour_integral p (\<lambda>x. 1/(x - z)) =
                  contour_integral p (\<lambda>x. 1/(x - w) - 1/(x - z))"
      by (simp add: p contour_integrable_inversediff contour_integral_diff)
    { fix x
      assume pe: "3/4 * pe < cmod (z - x)"
      have "cmod (w - x) < pe/4 + cmod (z - x)"
        by (meson add_less_cancel_right norm_diff_triangle_le order_refl order_trans_rules(21) w(1))
      then have wx: "cmod (w - x) < 4/3 * cmod (z - x)" using pe by simp
      have "cmod (z - x) \<le> cmod (z - w) + cmod (w - x)"
        using norm_diff_triangle_le by blast
      also have "\<dots> < pe/4 + cmod (w - x)"
        using w by (simp add: norm_minus_commute)
      finally have "pe/2 < cmod (w - x)"
        using pe by auto
      then have "(pe/2)^2 < cmod (w - x) ^ 2"
        apply (rule power_strict_mono)
        using \<open>pe>0\<close> by auto
      then have pe2: "pe^2 < 4 * cmod (w - x) ^ 2"
        by (simp add: power_divide)
      have "8 * L * cmod (w - z) < e * pe\<^sup>2"
        using w \<open>L>0\<close> by (simp add: field_simps)
      also have "\<dots> < e * 4 * cmod (w - x) * cmod (w - x)"
        using pe2 \<open>e>0\<close> by (simp add: power2_eq_square)
      also have "\<dots> < e * 4 * cmod (w - x) * (4/3 * cmod (z - x))"
        using wx
        apply (rule mult_strict_left_mono)
        using pe2 e not_less_iff_gr_or_eq by fastforce
      finally have "L * cmod (w - z) < 2/3 * e * cmod (w - x) * cmod (z - x)"
        by simp
      also have "\<dots> \<le> e * cmod (w - x) * cmod (z - x)"
         using e by simp
      finally have Lwz: "L * cmod (w - z) < e * cmod (w - x) * cmod (z - x)" .
      have "L * cmod (1 / (x - w) - 1 / (x - z)) \<le> e"
        apply (cases "x=z \<or> x=w")
        using pe \<open>pe>0\<close> w \<open>L>0\<close>
        apply (force simp: norm_minus_commute)
        using wx w(2) \<open>L>0\<close> pe pe2 Lwz
        apply (auto simp: divide_simps mult_less_0_iff norm_minus_commute norm_divide norm_mult power2_eq_square)
        done
    } note L_cmod_le = this
    have *: "cmod (contour_integral p (\<lambda>x. 1 / (x - w) - 1 / (x - z))) \<le> L * (e * pe\<^sup>2 / L / 4 * (inverse (pe / 2))\<^sup>2)"
      apply (rule L)
      using \<open>pe>0\<close> w
      apply (force simp: dist_norm norm_minus_commute intro!: holomorphic_intros)
      using \<open>pe>0\<close> w \<open>L>0\<close>
      apply (auto simp: cball_def dist_norm field_simps L_cmod_le  simp del: less_divide_eq_numeral1 le_divide_eq_numeral1)
      done
    have "cmod (contour_integral p (\<lambda>x. 1 / (x - w)) - contour_integral p (\<lambda>x. 1 / (x - z))) < 2*e"
      apply simp
      apply (rule le_less_trans [OF *])
      using \<open>L>0\<close> e
      apply (force simp: field_simps)
      done
    then have "cmod (winding_number p w - winding_number p z) < e"
      using pi_ge_two e
      by (force simp: winding_number_valid_path p field_simps norm_divide norm_mult intro: less_le_trans)
  } note cmod_wn_diff = this
  then have "isCont (winding_number p) z"
    apply (simp add: continuous_at_eps_delta, clarify)
    apply (rule_tac x="min (pe/4) (e/2*pe^2/L/4)" in exI)
    using \<open>pe>0\<close> \<open>L>0\<close>
    apply (simp add: dist_norm cmod_wn_diff)
    done
  then show ?thesis
    apply (rule continuous_transform_within [where d = "min d e / 2"])
    apply (auto simp: \<open>d>0\<close> \<open>e>0\<close> dist_norm wnwn)
    done
qed

corollary continuous_on_winding_number:
    "path \<gamma> \<Longrightarrow> continuous_on (- path_image \<gamma>) (\<lambda>w. winding_number \<gamma> w)"
  by (simp add: continuous_at_imp_continuous_on continuous_at_winding_number)

subsection\<^marker>\<open>tag unimportant\<close> \<open>The winding number is constant on a connected region\<close>

lemma winding_number_constant:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and cs: "connected S" and sg: "S \<inter> path_image \<gamma> = {}"
  shows "winding_number \<gamma> constant_on S"
proof -
  have *: "1 \<le> cmod (winding_number \<gamma> y - winding_number \<gamma> z)"
      if ne: "winding_number \<gamma> y \<noteq> winding_number \<gamma> z" and "y \<in> S" "z \<in> S" for y z
  proof -
    have "winding_number \<gamma> y \<in> \<int>"  "winding_number \<gamma> z \<in>  \<int>"
      using that integer_winding_number [OF \<gamma> loop] sg \<open>y \<in> S\<close> by auto
    with ne show ?thesis
      by (auto simp: Ints_def simp flip: of_int_diff)
  qed
  have cont: "continuous_on S (\<lambda>w. winding_number \<gamma> w)"
    using continuous_on_winding_number [OF \<gamma>] sg
    by (meson continuous_on_subset disjoint_eq_subset_Compl)
  show ?thesis
    using "*" zero_less_one
    by (blast intro: continuous_discrete_range_constant [OF cs cont])
qed

lemma winding_number_eq:
     "\<lbrakk>path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; w \<in> S; z \<in> S; connected S; S \<inter> path_image \<gamma> = {}\<rbrakk>
      \<Longrightarrow> winding_number \<gamma> w = winding_number \<gamma> z"
  using winding_number_constant by (metis constant_on_def)

lemma open_winding_number_levelsets:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    shows "open {z. z \<notin> path_image \<gamma> \<and> winding_number \<gamma> z = k}"
proof -
  have opn: "open (- path_image \<gamma>)"
    by (simp add: closed_path_image \<gamma> open_Compl)
  { fix z assume z: "z \<notin> path_image \<gamma>" and k: "k = winding_number \<gamma> z"
    obtain e where e: "e>0" "ball z e \<subseteq> - path_image \<gamma>"
      using open_contains_ball [of "- path_image \<gamma>"] opn z
      by blast
    have "\<exists>e>0. \<forall>y. dist y z < e \<longrightarrow> y \<notin> path_image \<gamma> \<and> winding_number \<gamma> y = winding_number \<gamma> z"
      apply (rule_tac x=e in exI)
      using e apply (simp add: dist_norm ball_def norm_minus_commute)
      apply (auto simp: dist_norm norm_minus_commute intro!: winding_number_eq [OF assms, where S = "ball z e"])
      done
  } then
  show ?thesis
    by (auto simp: open_dist)
qed

subsection\<open>Winding number is zero "outside" a curve\<close>

proposition winding_number_zero_in_outside:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and z: "z \<in> outside (path_image \<gamma>)"
    shows "winding_number \<gamma> z = 0"
proof -
  obtain B::real where "0 < B" and B: "path_image \<gamma> \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bounded_path_image [OF \<gamma>]] by auto
  obtain w::complex where w: "w \<notin> ball 0 (B + 1)"
    by (metis abs_of_nonneg le_less less_irrefl mem_ball_0 norm_of_real)
  have "- ball 0 (B + 1) \<subseteq> outside (path_image \<gamma>)"
    apply (rule outside_subset_convex)
    using B subset_ball by auto
  then have wout: "w \<in> outside (path_image \<gamma>)"
    using w by blast
  moreover have "winding_number \<gamma> constant_on outside (path_image \<gamma>)"
    using winding_number_constant [OF \<gamma> loop, of "outside(path_image \<gamma>)"] connected_outside
    by (metis DIM_complex bounded_path_image dual_order.refl \<gamma> outside_no_overlap)
  ultimately have "winding_number \<gamma> z = winding_number \<gamma> w"
    by (metis (no_types, hide_lams) constant_on_def z)
  also have "\<dots> = 0"
  proof -
    have wnot: "w \<notin> path_image \<gamma>"  using wout by (simp add: outside_def)
    { fix e::real assume "0<e"
      obtain p where p: "polynomial_function p" "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>"
                 and pg1: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < 1)"
                 and pge: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < e)"
        using path_approx_polynomial_function [OF \<gamma>, of "min 1 e"] \<open>e>0\<close>
        by (metis atLeastAtMost_iff min_less_iff_conj zero_less_one)
      have pip: "path_image p \<subseteq> ball 0 (B + 1)"
        using B
        apply (clarsimp simp add: path_image_def dist_norm ball_def)
        apply (frule (1) pg1)
        apply (fastforce dest: norm_add_less)
        done
      then have "w \<notin> path_image p"  using w by blast
      then have "\<exists>p. valid_path p \<and> w \<notin> path_image p \<and>
                     pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and>
                     (\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < e) \<and> contour_integral p (\<lambda>wa. 1 / (wa - w)) = 0"
        apply (rule_tac x=p in exI)
        apply (simp add: p valid_path_polynomial_function)
        apply (intro conjI)
        using pge apply (simp add: norm_minus_commute)
        apply (rule contour_integral_unique [OF Cauchy_theorem_convex_simple [OF _ convex_ball [of 0 "B+1"]]])
        apply (rule holomorphic_intros | simp add: dist_norm)+
        using mem_ball_0 w apply blast
        using p apply (simp_all add: valid_path_polynomial_function loop pip)
        done
    }
    then show ?thesis
      by (auto intro: winding_number_unique [OF \<gamma>] simp add: winding_number_prop_def wnot)
  qed
  finally show ?thesis .
qed

corollary\<^marker>\<open>tag unimportant\<close> winding_number_zero_const: "a \<noteq> z \<Longrightarrow> winding_number (\<lambda>t. a) z = 0"
  by (rule winding_number_zero_in_outside)
     (auto simp: pathfinish_def pathstart_def path_polynomial_function)

corollary\<^marker>\<open>tag unimportant\<close> winding_number_zero_outside:
    "\<lbrakk>path \<gamma>; convex s; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> s; path_image \<gamma> \<subseteq> s\<rbrakk> \<Longrightarrow> winding_number \<gamma> z = 0"
  by (meson convex_in_outside outside_mono subsetCE winding_number_zero_in_outside)

lemma winding_number_zero_at_infinity:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    shows "\<exists>B. \<forall>z. B \<le> norm z \<longrightarrow> winding_number \<gamma> z = 0"
proof -
  obtain B::real where "0 < B" and B: "path_image \<gamma> \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bounded_path_image [OF \<gamma>]] by auto
  then show ?thesis
    apply (rule_tac x="B+1" in exI, clarify)
    apply (rule winding_number_zero_outside [OF \<gamma> convex_cball [of 0 B] loop])
    apply (meson less_add_one mem_cball_0 not_le order_trans)
    using ball_subset_cball by blast
qed

lemma winding_number_zero_point:
    "\<lbrakk>path \<gamma>; convex s; pathfinish \<gamma> = pathstart \<gamma>; open s; path_image \<gamma> \<subseteq> s\<rbrakk>
     \<Longrightarrow> \<exists>z. z \<in> s \<and> winding_number \<gamma> z = 0"
  using outside_compact_in_open [of "path_image \<gamma>" s] path_image_nonempty winding_number_zero_in_outside
  by (fastforce simp add: compact_path_image)


text\<open>If a path winds round a set, it winds rounds its inside.\<close>
lemma winding_number_around_inside:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and cls: "closed s" and cos: "connected s" and s_disj: "s \<inter> path_image \<gamma> = {}"
      and z: "z \<in> s" and wn_nz: "winding_number \<gamma> z \<noteq> 0" and w: "w \<in> s \<union> inside s"
    shows "winding_number \<gamma> w = winding_number \<gamma> z"
proof -
  have ssb: "s \<subseteq> inside(path_image \<gamma>)"
  proof
    fix x :: complex
    assume "x \<in> s"
    hence "x \<notin> path_image \<gamma>"
      by (meson disjoint_iff_not_equal s_disj)
    thus "x \<in> inside (path_image \<gamma>)"
      using \<open>x \<in> s\<close> by (metis (no_types) ComplI UnE cos \<gamma> loop s_disj union_with_outside winding_number_eq winding_number_zero_in_outside wn_nz z)
qed
  show ?thesis
    apply (rule winding_number_eq [OF \<gamma> loop w])
    using z apply blast
    apply (simp add: cls connected_with_inside cos)
    apply (simp add: Int_Un_distrib2 s_disj, safe)
    by (meson ssb inside_inside_compact_connected [OF cls, of "path_image \<gamma>"] compact_path_image connected_path_image contra_subsetD disjoint_iff_not_equal \<gamma> inside_no_overlap)
 qed


text\<open>Bounding a WN by 1/2 for a path and point in opposite halfspaces.\<close>
lemma winding_number_subpath_continuous:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>"
    shows "continuous_on {0..1} (\<lambda>x. winding_number(subpath 0 x \<gamma>) z)"
proof -
  have *: "integral {0..x} (\<lambda>t. vector_derivative \<gamma> (at t) / (\<gamma> t - z)) / (2 * of_real pi * \<i>) =
         winding_number (subpath 0 x \<gamma>) z"
         if x: "0 \<le> x" "x \<le> 1" for x
  proof -
    have "integral {0..x} (\<lambda>t. vector_derivative \<gamma> (at t) / (\<gamma> t - z)) / (2 * of_real pi * \<i>) =
          1 / (2*pi*\<i>) * contour_integral (subpath 0 x \<gamma>) (\<lambda>w. 1/(w - z))"
      using assms x
      apply (simp add: contour_integral_subcontour_integral [OF contour_integrable_inversediff])
      done
    also have "\<dots> = winding_number (subpath 0 x \<gamma>) z"
      apply (subst winding_number_valid_path)
      using assms x
      apply (simp_all add: path_image_subpath valid_path_subpath)
      by (force simp: path_image_def)
    finally show ?thesis .
  qed
  show ?thesis
    apply (rule continuous_on_eq
                 [where f = "\<lambda>x. 1 / (2*pi*\<i>) *
                                 integral {0..x} (\<lambda>t. 1/(\<gamma> t - z) * vector_derivative \<gamma> (at t))"])
    apply (rule continuous_intros)+
    apply (rule indefinite_integral_continuous_1)
    apply (rule contour_integrable_inversediff [OF assms, unfolded contour_integrable_on])
      using assms
    apply (simp add: *)
    done
qed

lemma winding_number_ivt_pos:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "0 \<le> w" "w \<le> Re(winding_number \<gamma> z)"
      shows "\<exists>t \<in> {0..1}. Re(winding_number(subpath 0 t \<gamma>) z) = w"
  apply (rule ivt_increasing_component_on_1 [of 0 1, where ?k = "1::complex", simplified complex_inner_1_right], simp)
  apply (rule winding_number_subpath_continuous [OF \<gamma> z])
  using assms
  apply (auto simp: path_image_def image_def)
  done

lemma winding_number_ivt_neg:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "Re(winding_number \<gamma> z) \<le> w" "w \<le> 0"
      shows "\<exists>t \<in> {0..1}. Re(winding_number(subpath 0 t \<gamma>) z) = w"
  apply (rule ivt_decreasing_component_on_1 [of 0 1, where ?k = "1::complex", simplified complex_inner_1_right], simp)
  apply (rule winding_number_subpath_continuous [OF \<gamma> z])
  using assms
  apply (auto simp: path_image_def image_def)
  done

lemma winding_number_ivt_abs:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "0 \<le> w" "w \<le> \<bar>Re(winding_number \<gamma> z)\<bar>"
      shows "\<exists>t \<in> {0..1}. \<bar>Re (winding_number (subpath 0 t \<gamma>) z)\<bar> = w"
  using assms winding_number_ivt_pos [of \<gamma> z w] winding_number_ivt_neg [of \<gamma> z "-w"]
  by force

lemma winding_number_lt_half_lemma:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and az: "a \<bullet> z \<le> b" and pag: "path_image \<gamma> \<subseteq> {w. a \<bullet> w > b}"
    shows "Re(winding_number \<gamma> z) < 1/2"
proof -
  { assume "Re(winding_number \<gamma> z) \<ge> 1/2"
    then obtain t::real where t: "0 \<le> t" "t \<le> 1" and sub12: "Re (winding_number (subpath 0 t \<gamma>) z) = 1/2"
      using winding_number_ivt_pos [OF \<gamma> z, of "1/2"] by auto
    have gt: "\<gamma> t - z = - (of_real (exp (- (2 * pi * Im (winding_number (subpath 0 t \<gamma>) z)))) * (\<gamma> 0 - z))"
      using winding_number_exp_2pi [of "subpath 0 t \<gamma>" z]
      apply (simp add: t \<gamma> valid_path_imp_path)
      using closed_segment_eq_real_ivl path_image_def t z by (fastforce simp: path_image_subpath Euler sub12)
    have "b < a \<bullet> \<gamma> 0"
    proof -
      have "\<gamma> 0 \<in> {c. b < a \<bullet> c}"
        by (metis (no_types) pag atLeastAtMost_iff image_subset_iff order_refl path_image_def zero_le_one)
      thus ?thesis
        by blast
    qed
    moreover have "b < a \<bullet> \<gamma> t"
    proof -
      have "\<gamma> t \<in> {c. b < a \<bullet> c}"
        by (metis (no_types) pag atLeastAtMost_iff image_subset_iff path_image_def t)
      thus ?thesis
        by blast
    qed
    ultimately have "0 < a \<bullet> (\<gamma> 0 - z)" "0 < a \<bullet> (\<gamma> t - z)" using az
      by (simp add: inner_diff_right)+
    then have False
      by (simp add: gt inner_mult_right mult_less_0_iff)
  }
  then show ?thesis by force
qed

lemma winding_number_lt_half:
  assumes "valid_path \<gamma>" "a \<bullet> z \<le> b" "path_image \<gamma> \<subseteq> {w. a \<bullet> w > b}"
    shows "\<bar>Re (winding_number \<gamma> z)\<bar> < 1/2"
proof -
  have "z \<notin> path_image \<gamma>" using assms by auto
  with assms show ?thesis
    apply (simp add: winding_number_lt_half_lemma abs_if del: less_divide_eq_numeral1)
    apply (metis complex_inner_1_right winding_number_lt_half_lemma [OF valid_path_imp_reverse, of \<gamma> z a b]
                 winding_number_reversepath valid_path_imp_path inner_minus_left path_image_reversepath)
    done
qed

lemma winding_number_le_half:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>"
      and anz: "a \<noteq> 0" and azb: "a \<bullet> z \<le> b" and pag: "path_image \<gamma> \<subseteq> {w. a \<bullet> w \<ge> b}"
    shows "\<bar>Re (winding_number \<gamma> z)\<bar> \<le> 1/2"
proof -
  { assume wnz_12: "\<bar>Re (winding_number \<gamma> z)\<bar> > 1/2"
    have "isCont (winding_number \<gamma>) z"
      by (metis continuous_at_winding_number valid_path_imp_path \<gamma> z)
    then obtain d where "d>0" and d: "\<And>x'. dist x' z < d \<Longrightarrow> dist (winding_number \<gamma> x') (winding_number \<gamma> z) < \<bar>Re(winding_number \<gamma> z)\<bar> - 1/2"
      using continuous_at_eps_delta wnz_12 diff_gt_0_iff_gt by blast
    define z' where "z' = z - (d / (2 * cmod a)) *\<^sub>R a"
    have *: "a \<bullet> z' \<le> b - d / 3 * cmod a"
      unfolding z'_def inner_mult_right' divide_inverse
      apply (simp add: field_split_simps algebra_simps dot_square_norm power2_eq_square anz)
      apply (metis \<open>0 < d\<close> add_increasing azb less_eq_real_def mult_nonneg_nonneg mult_right_mono norm_ge_zero norm_numeral)
      done
    have "cmod (winding_number \<gamma> z' - winding_number \<gamma> z) < \<bar>Re (winding_number \<gamma> z)\<bar> - 1/2"
      using d [of z'] anz \<open>d>0\<close> by (simp add: dist_norm z'_def)
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - cmod (winding_number \<gamma> z' - winding_number \<gamma> z)"
      by simp
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - \<bar>Re (winding_number \<gamma> z') - Re (winding_number \<gamma> z)\<bar>"
      using abs_Re_le_cmod [of "winding_number \<gamma> z' - winding_number \<gamma> z"] by simp
    then have wnz_12': "\<bar>Re (winding_number \<gamma> z')\<bar> > 1/2"
      by linarith
    moreover have "\<bar>Re (winding_number \<gamma> z')\<bar> < 1/2"
      apply (rule winding_number_lt_half [OF \<gamma> *])
      using azb \<open>d>0\<close> pag
      apply (auto simp: add_strict_increasing anz field_split_simps dest!: subsetD)
      done
    ultimately have False
      by simp
  }
  then show ?thesis by force
qed

lemma winding_number_lt_half_linepath: "z \<notin> closed_segment a b \<Longrightarrow> \<bar>Re (winding_number (linepath a b) z)\<bar> < 1/2"
  using separating_hyperplane_closed_point [of "closed_segment a b" z]
  apply auto
  apply (simp add: closed_segment_def)
  apply (drule less_imp_le)
  apply (frule winding_number_lt_half [OF valid_path_linepath [of a b]])
  apply (auto simp: segment)
  done


text\<open> Positivity of WN for a linepath.\<close>
lemma winding_number_linepath_pos_lt:
    assumes "0 < Im ((b - a) * cnj (b - z))"
      shows "0 < Re(winding_number(linepath a b) z)"
proof -
  have z: "z \<notin> path_image (linepath a b)"
    using assms
    by (simp add: closed_segment_def) (force simp: algebra_simps)
  show ?thesis
    apply (rule winding_number_pos_lt [OF valid_path_linepath z assms])
    apply (simp add: linepath_def algebra_simps)
    done
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>More winding number properties\<close>

text\<open>including the fact that it's +-1 inside a simple closed curve.\<close>

lemma winding_number_homotopic_paths:
    assumes "homotopic_paths (-{z}) g h"
      shows "winding_number g z = winding_number h z"
proof -
  have "path g" "path h" using homotopic_paths_imp_path [OF assms] by auto
  moreover have pag: "z \<notin> path_image g" and pah: "z \<notin> path_image h"
    using homotopic_paths_imp_subset [OF assms] by auto
  ultimately obtain d e where "d > 0" "e > 0"
      and d: "\<And>p. \<lbrakk>path p; pathstart p = pathstart g; pathfinish p = pathfinish g; \<forall>t\<in>{0..1}. norm (p t - g t) < d\<rbrakk>
            \<Longrightarrow> homotopic_paths (-{z}) g p"
      and e: "\<And>q. \<lbrakk>path q; pathstart q = pathstart h; pathfinish q = pathfinish h; \<forall>t\<in>{0..1}. norm (q t - h t) < e\<rbrakk>
            \<Longrightarrow> homotopic_paths (-{z}) h q"
    using homotopic_nearby_paths [of g "-{z}"] homotopic_nearby_paths [of h "-{z}"] by force
  obtain p where p:
       "valid_path p" "z \<notin> path_image p"
       "pathstart p = pathstart g" "pathfinish p = pathfinish g"
       and gp_less:"\<forall>t\<in>{0..1}. cmod (g t - p t) < d"
       and pap: "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number g z"
    using winding_number [OF \<open>path g\<close> pag \<open>0 < d\<close>] unfolding winding_number_prop_def by blast
  obtain q where q:
       "valid_path q" "z \<notin> path_image q"
       "pathstart q = pathstart h" "pathfinish q = pathfinish h"
       and hq_less: "\<forall>t\<in>{0..1}. cmod (h t - q t) < e"
       and paq:  "contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number h z"
    using winding_number [OF \<open>path h\<close> pah \<open>0 < e\<close>] unfolding winding_number_prop_def by blast
  have "homotopic_paths (- {z}) g p"
    by (simp add: d p valid_path_imp_path norm_minus_commute gp_less)
  moreover have "homotopic_paths (- {z}) h q"
    by (simp add: e q valid_path_imp_path norm_minus_commute hq_less)
  ultimately have "homotopic_paths (- {z}) p q"
    by (blast intro: homotopic_paths_trans homotopic_paths_sym assms)
  then have "contour_integral p (\<lambda>w. 1/(w - z)) = contour_integral q (\<lambda>w. 1/(w - z))"
    by (rule Cauchy_theorem_homotopic_paths) (auto intro!: holomorphic_intros simp: p q)
  then show ?thesis
    by (simp add: pap paq)
qed

lemma winding_number_homotopic_loops:
    assumes "homotopic_loops (-{z}) g h"
      shows "winding_number g z = winding_number h z"
proof -
  have "path g" "path h" using homotopic_loops_imp_path [OF assms] by auto
  moreover have pag: "z \<notin> path_image g" and pah: "z \<notin> path_image h"
    using homotopic_loops_imp_subset [OF assms] by auto
  moreover have gloop: "pathfinish g = pathstart g" and hloop: "pathfinish h = pathstart h"
    using homotopic_loops_imp_loop [OF assms] by auto
  ultimately obtain d e where "d > 0" "e > 0"
      and d: "\<And>p. \<lbrakk>path p; pathfinish p = pathstart p; \<forall>t\<in>{0..1}. norm (p t - g t) < d\<rbrakk>
            \<Longrightarrow> homotopic_loops (-{z}) g p"
      and e: "\<And>q. \<lbrakk>path q; pathfinish q = pathstart q; \<forall>t\<in>{0..1}. norm (q t - h t) < e\<rbrakk>
            \<Longrightarrow> homotopic_loops (-{z}) h q"
    using homotopic_nearby_loops [of g "-{z}"] homotopic_nearby_loops [of h "-{z}"] by force
  obtain p where p:
       "valid_path p" "z \<notin> path_image p"
       "pathstart p = pathstart g" "pathfinish p = pathfinish g"
       and gp_less:"\<forall>t\<in>{0..1}. cmod (g t - p t) < d"
       and pap: "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number g z"
    using winding_number [OF \<open>path g\<close> pag \<open>0 < d\<close>] unfolding winding_number_prop_def by blast
  obtain q where q:
       "valid_path q" "z \<notin> path_image q"
       "pathstart q = pathstart h" "pathfinish q = pathfinish h"
       and hq_less: "\<forall>t\<in>{0..1}. cmod (h t - q t) < e"
       and paq:  "contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number h z"
    using winding_number [OF \<open>path h\<close> pah \<open>0 < e\<close>] unfolding winding_number_prop_def by blast
  have gp: "homotopic_loops (- {z}) g p"
    by (simp add: gloop d gp_less norm_minus_commute p valid_path_imp_path)
  have hq: "homotopic_loops (- {z}) h q"
    by (simp add: e hloop hq_less norm_minus_commute q valid_path_imp_path)
  have "contour_integral p (\<lambda>w. 1/(w - z)) = contour_integral q (\<lambda>w. 1/(w - z))"
  proof (rule Cauchy_theorem_homotopic_loops)
    show "homotopic_loops (- {z}) p q"
      by (blast intro: homotopic_loops_trans homotopic_loops_sym gp hq assms)
  qed (auto intro!: holomorphic_intros simp: p q)
  then show ?thesis
    by (simp add: pap paq)
qed

lemma winding_number_paths_linear_eq:
  "\<lbrakk>path g; path h; pathstart h = pathstart g; pathfinish h = pathfinish g;
    \<And>t. t \<in> {0..1} \<Longrightarrow> z \<notin> closed_segment (g t) (h t)\<rbrakk>
        \<Longrightarrow> winding_number h z = winding_number g z"
  by (blast intro: sym homotopic_paths_linear winding_number_homotopic_paths)

lemma winding_number_loops_linear_eq:
  "\<lbrakk>path g; path h; pathfinish g = pathstart g; pathfinish h = pathstart h;
    \<And>t. t \<in> {0..1} \<Longrightarrow> z \<notin> closed_segment (g t) (h t)\<rbrakk>
        \<Longrightarrow> winding_number h z = winding_number g z"
  by (blast intro: sym homotopic_loops_linear winding_number_homotopic_loops)

lemma winding_number_nearby_paths_eq:
     "\<lbrakk>path g; path h; pathstart h = pathstart g; pathfinish h = pathfinish g;
      \<And>t. t \<in> {0..1} \<Longrightarrow> norm(h t - g t) < norm(g t - z)\<rbrakk>
      \<Longrightarrow> winding_number h z = winding_number g z"
  by (metis segment_bound(2) norm_minus_commute not_le winding_number_paths_linear_eq)

lemma winding_number_nearby_loops_eq:
     "\<lbrakk>path g; path h; pathfinish g = pathstart g; pathfinish h = pathstart h;
      \<And>t. t \<in> {0..1} \<Longrightarrow> norm(h t - g t) < norm(g t - z)\<rbrakk>
      \<Longrightarrow> winding_number h z = winding_number g z"
  by (metis segment_bound(2) norm_minus_commute not_le winding_number_loops_linear_eq)


lemma winding_number_subpath_combine:
    "\<lbrakk>path g; z \<notin> path_image g;
      u \<in> {0..1}; v \<in> {0..1}; w \<in> {0..1}\<rbrakk>
      \<Longrightarrow> winding_number (subpath u v g) z + winding_number (subpath v w g) z =
          winding_number (subpath u w g) z"
apply (rule trans [OF winding_number_join [THEN sym]
                      winding_number_homotopic_paths [OF homotopic_join_subpaths]])
  using path_image_subpath_subset by auto

text \<open>Winding numbers of circular contours\<close>

proposition winding_number_part_circlepath_pos_less:
  assumes "s < t" and no: "norm(w - z) < r"
    shows "0 < Re (winding_number(part_circlepath z r s t) w)"
proof -
  have "0 < r" by (meson no norm_not_less_zero not_le order.strict_trans2)
  note valid_path_part_circlepath
  moreover have " w \<notin> path_image (part_circlepath z r s t)"
    using assms by (auto simp: path_image_def image_def part_circlepath_def norm_mult linepath_def)
  moreover have "0 < r * (t - s) * (r - cmod (w - z))"
    using assms by (metis \<open>0 < r\<close> diff_gt_0_iff_gt mult_pos_pos)
  ultimately show ?thesis
    apply (rule winding_number_pos_lt [where e = "r*(t - s)*(r - norm(w - z))"])
    apply (simp add: vector_derivative_part_circlepath right_diff_distrib [symmetric] mult_ac)
    apply (rule mult_left_mono)+
    using Re_Im_le_cmod [of "w-z" "linepath s t x" for x]
    apply (simp add: exp_Euler cos_of_real sin_of_real part_circlepath_def algebra_simps cos_squared_eq [unfolded power2_eq_square])
    using assms \<open>0 < r\<close> by auto
qed

lemma winding_number_circlepath_centre: "0 < r \<Longrightarrow> winding_number (circlepath z r) z = 1"
  apply (rule winding_number_unique_loop)
  apply (simp_all add: sphere_def valid_path_imp_path)
  apply (rule_tac x="circlepath z r" in exI)
  apply (simp add: sphere_def contour_integral_circlepath)
  done

proposition winding_number_circlepath:
  assumes "norm(w - z) < r" shows "winding_number(circlepath z r) w = 1"
proof (cases "w = z")
  case True then show ?thesis
    using assms winding_number_circlepath_centre by auto
next
  case False
  have [simp]: "r > 0"
    using assms le_less_trans norm_ge_zero by blast
  define r' where "r' = norm(w - z)"
  have "r' < r"
    by (simp add: assms r'_def)
  have disjo: "cball z r' \<inter> sphere z r = {}"
    using \<open>r' < r\<close> by (force simp: cball_def sphere_def)
  have "winding_number(circlepath z r) w = winding_number(circlepath z r) z"
  proof (rule winding_number_around_inside [where s = "cball z r'"])
    show "winding_number (circlepath z r) z \<noteq> 0"
      by (simp add: winding_number_circlepath_centre)
    show "cball z r' \<inter> path_image (circlepath z r) = {}"
      by (simp add: disjo less_eq_real_def)
  qed (auto simp: r'_def dist_norm norm_minus_commute)
  also have "\<dots> = 1"
    by (simp add: winding_number_circlepath_centre)
  finally show ?thesis .
qed

lemma no_bounded_connected_component_imp_winding_number_zero:
  assumes g: "path g" "path_image g \<subseteq> s" "pathfinish g = pathstart g" "z \<notin> s"
      and nb: "\<And>z. bounded (connected_component_set (- s) z) \<longrightarrow> z \<in> s"
  shows "winding_number g z = 0"
apply (rule winding_number_zero_in_outside)
apply (simp_all add: assms)
by (metis nb [of z] \<open>path_image g \<subseteq> s\<close> \<open>z \<notin> s\<close> contra_subsetD mem_Collect_eq outside outside_mono)

lemma no_bounded_path_component_imp_winding_number_zero:
  assumes g: "path g" "path_image g \<subseteq> s" "pathfinish g = pathstart g" "z \<notin> s"
      and nb: "\<And>z. bounded (path_component_set (- s) z) \<longrightarrow> z \<in> s"
  shows "winding_number g z = 0"
apply (rule no_bounded_connected_component_imp_winding_number_zero [OF g])
by (simp add: bounded_subset nb path_component_subset_connected_component)

subsection\<open>Winding number for a triangle\<close>

lemma wn_triangle1:
  assumes "0 \<in> interior(convex hull {a,b,c})"
    shows "\<not> (Im(a/b) \<le> 0 \<and> 0 \<le> Im(b/c))"
proof -
  { assume 0: "Im(a/b) \<le> 0" "0 \<le> Im(b/c)"
    have "0 \<notin> interior (convex hull {a,b,c})"
    proof (cases "a=0 \<or> b=0 \<or> c=0")
      case True then show ?thesis
        by (auto simp: not_in_interior_convex_hull_3)
    next
      case False
      then have "b \<noteq> 0" by blast
      { fix x y::complex and u::real
        assume eq_f': "Im x * Re b \<le> Im b * Re x" "Im y * Re b \<le> Im b * Re y" "0 \<le> u" "u \<le> 1"
        then have "((1 - u) * Im x) * Re b \<le> Im b * ((1 - u) * Re x)"
          by (simp add: mult_left_mono mult.assoc mult.left_commute [of "Im b"])
        then have "((1 - u) * Im x + u * Im y) * Re b \<le> Im b * ((1 - u) * Re x + u * Re y)"
          using eq_f' ordered_comm_semiring_class.comm_mult_left_mono
          by (fastforce simp add: algebra_simps)
      }
      with False 0 have "convex hull {a,b,c} \<le> {z. Im z * Re b \<le> Im b * Re z}"
        apply (simp add: Complex.Im_divide divide_simps complex_neq_0 [symmetric])
        apply (simp add: algebra_simps)
        apply (rule hull_minimal)
        apply (auto simp: algebra_simps convex_alt)
        done
      moreover have "0 \<notin> interior({z. Im z * Re b \<le> Im b * Re z})"
      proof
        assume "0 \<in> interior {z. Im z * Re b \<le> Im b * Re z}"
        then obtain e where "e>0" and e: "ball 0 e \<subseteq> {z. Im z * Re b \<le> Im b * Re z}"
          by (meson mem_interior)
        define z where "z \<equiv> - sgn (Im b) * (e/3) + sgn (Re b) * (e/3) * \<i>"
        have "z \<in> ball 0 e"
          using \<open>e>0\<close>
          apply (simp add: z_def dist_norm)
          apply (rule le_less_trans [OF norm_triangle_ineq4])
          apply (simp add: norm_mult abs_sgn_eq)
          done
        then have "z \<in> {z. Im z * Re b \<le> Im b * Re z}"
          using e by blast
        then show False
          using \<open>e>0\<close> \<open>b \<noteq> 0\<close>
          apply (simp add: z_def dist_norm sgn_if less_eq_real_def mult_less_0_iff complex.expand split: if_split_asm)
          apply (auto simp: algebra_simps)
          apply (meson less_asym less_trans mult_pos_pos neg_less_0_iff_less)
          by (metis less_asym mult_pos_pos neg_less_0_iff_less)
      qed
      ultimately show ?thesis
        using interior_mono by blast
    qed
  } with assms show ?thesis by blast
qed

lemma wn_triangle2_0:
  assumes "0 \<in> interior(convex hull {a,b,c})"
  shows
       "0 < Im((b - a) * cnj (b)) \<and>
        0 < Im((c - b) * cnj (c)) \<and>
        0 < Im((a - c) * cnj (a))
        \<or>
        Im((b - a) * cnj (b)) < 0 \<and>
        0 < Im((b - c) * cnj (b)) \<and>
        0 < Im((a - b) * cnj (a)) \<and>
        0 < Im((c - a) * cnj (c))"
proof -
  have [simp]: "{b,c,a} = {a,b,c}" "{c,a,b} = {a,b,c}" by auto
  show ?thesis
    using wn_triangle1 [OF assms] wn_triangle1 [of b c a] wn_triangle1 [of c a b] assms
    by (auto simp: algebra_simps Im_complex_div_gt_0 Im_complex_div_lt_0 not_le not_less)
qed

lemma wn_triangle2:
  assumes "z \<in> interior(convex hull {a,b,c})"
   shows "0 < Im((b - a) * cnj (b - z)) \<and>
          0 < Im((c - b) * cnj (c - z)) \<and>
          0 < Im((a - c) * cnj (a - z))
          \<or>
          Im((b - a) * cnj (b - z)) < 0 \<and>
          0 < Im((b - c) * cnj (b - z)) \<and>
          0 < Im((a - b) * cnj (a - z)) \<and>
          0 < Im((c - a) * cnj (c - z))"
proof -
  have 0: "0 \<in> interior(convex hull {a-z, b-z, c-z})"
    using assms convex_hull_translation [of "-z" "{a,b,c}"]
                interior_translation [of "-z"]
    by (simp cong: image_cong_simp)
  show ?thesis using wn_triangle2_0 [OF 0]
    by simp
qed

lemma wn_triangle3:
  assumes z: "z \<in> interior(convex hull {a,b,c})"
      and "0 < Im((b-a) * cnj (b-z))"
          "0 < Im((c-b) * cnj (c-z))"
          "0 < Im((a-c) * cnj (a-z))"
    shows "winding_number (linepath a b +++ linepath b c +++ linepath c a) z = 1"
proof -
  have znot[simp]: "z \<notin> closed_segment a b" "z \<notin> closed_segment b c" "z \<notin> closed_segment c a"
    using z interior_of_triangle [of a b c]
    by (auto simp: closed_segment_def)
  have gt0: "0 < Re (winding_number (linepath a b +++ linepath b c +++ linepath c a) z)"
    using assms
    by (simp add: winding_number_linepath_pos_lt path_image_join winding_number_join_pos_combined)
  have lt2: "Re (winding_number (linepath a b +++ linepath b c +++ linepath c a) z) < 2"
    using winding_number_lt_half_linepath [of _ a b]
    using winding_number_lt_half_linepath [of _ b c]
    using winding_number_lt_half_linepath [of _ c a] znot
    apply (fastforce simp add: winding_number_join path_image_join)
    done
  show ?thesis
    by (rule winding_number_eq_1) (simp_all add: path_image_join gt0 lt2)
qed

proposition winding_number_triangle:
  assumes z: "z \<in> interior(convex hull {a,b,c})"
    shows "winding_number(linepath a b +++ linepath b c +++ linepath c a) z =
           (if 0 < Im((b - a) * cnj (b - z)) then 1 else -1)"
proof -
  have [simp]: "{a,c,b} = {a,b,c}"  by auto
  have znot[simp]: "z \<notin> closed_segment a b" "z \<notin> closed_segment b c" "z \<notin> closed_segment c a"
    using z interior_of_triangle [of a b c]
    by (auto simp: closed_segment_def)
  then have [simp]: "z \<notin> closed_segment b a" "z \<notin> closed_segment c b" "z \<notin> closed_segment a c"
    using closed_segment_commute by blast+
  have *: "winding_number (linepath a b +++ linepath b c +++ linepath c a) z =
            winding_number (reversepath (linepath a c +++ linepath c b +++ linepath b a)) z"
    by (simp add: reversepath_joinpaths winding_number_join not_in_path_image_join)
  show ?thesis
    using wn_triangle2 [OF z] apply (rule disjE)
    apply (simp add: wn_triangle3 z)
    apply (simp add: path_image_join winding_number_reversepath * wn_triangle3 z)
    done
qed

subsection\<open>Winding numbers for simple closed paths\<close>

lemma winding_number_from_innerpath:
  assumes "simple_path c1" and c1: "pathstart c1 = a" "pathfinish c1 = b"
      and "simple_path c2" and c2: "pathstart c2 = a" "pathfinish c2 = b"
      and "simple_path c" and c: "pathstart c = a" "pathfinish c = b"
      and c1c2: "path_image c1 \<inter> path_image c2 = {a,b}"
      and c1c:  "path_image c1 \<inter> path_image c = {a,b}"
      and c2c:  "path_image c2 \<inter> path_image c = {a,b}"
      and ne_12: "path_image c \<inter> inside(path_image c1 \<union> path_image c2) \<noteq> {}"
      and z: "z \<in> inside(path_image c1 \<union> path_image c)"
      and wn_d: "winding_number (c1 +++ reversepath c) z = d"
      and "a \<noteq> b" "d \<noteq> 0"
  obtains "z \<in> inside(path_image c1 \<union> path_image c2)" "winding_number (c1 +++ reversepath c2) z = d"
proof -
  obtain 0: "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) = {}"
     and 1: "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
             (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
    by (rule split_inside_simple_closed_curve
              [OF \<open>simple_path c1\<close> c1 \<open>simple_path c2\<close> c2 \<open>simple_path c\<close> c \<open>a \<noteq> b\<close> c1c2 c1c c2c ne_12])
  have znot: "z \<notin> path_image c"  "z \<notin> path_image c1" "z \<notin> path_image c2"
    using union_with_outside z 1 by auto
  have wn_cc2: "winding_number (c +++ reversepath c2) z = 0"
    apply (rule winding_number_zero_in_outside)
    apply (simp_all add: \<open>simple_path c2\<close> c c2 \<open>simple_path c\<close> simple_path_imp_path path_image_join)
    by (metis "0" ComplI UnE disjoint_iff_not_equal sup.commute union_with_inside z znot)
  show ?thesis
  proof
    show "z \<in> inside (path_image c1 \<union> path_image c2)"
      using "1" z by blast
    have "winding_number c1 z - winding_number c z = d "
      using assms znot
      by (metis wn_d winding_number_join simple_path_imp_path winding_number_reversepath add.commute path_image_reversepath path_reversepath pathstart_reversepath uminus_add_conv_diff)
    then show "winding_number (c1 +++ reversepath c2) z = d"
      using wn_cc2 by (simp add: winding_number_join simple_path_imp_path assms znot winding_number_reversepath)
  qed
qed

lemma simple_closed_path_wn1:
  fixes a::complex and e::real
  assumes "0 < e"
    and sp_pl: "simple_path(p +++ linepath (a - e) (a + e))"
    and psp:   "pathstart p = a + e"
    and pfp:   "pathfinish p = a - e"
    and disj:  "ball a e \<inter> path_image p = {}"
obtains z where "z \<in> inside (path_image (p +++ linepath (a - e) (a + e)))"
                "cmod (winding_number (p +++ linepath (a - e) (a + e)) z) = 1"
proof -
  have "arc p" and arc_lp: "arc (linepath (a - e) (a + e))"
    and pap: "path_image p \<inter> path_image (linepath (a - e) (a + e)) \<subseteq> {pathstart p, a-e}"
    using simple_path_join_loop_eq [of "linepath (a - e) (a + e)" p] assms by auto
  have mid_eq_a: "midpoint (a - e) (a + e) = a"
    by (simp add: midpoint_def)
  then have "a \<in> path_image(p +++ linepath (a - e) (a + e))"
    apply (simp add: assms path_image_join)
    by (metis midpoint_in_closed_segment)
  have "a \<in> frontier(inside (path_image(p +++ linepath (a - e) (a + e))))"
    apply (simp add: assms Jordan_inside_outside)
    apply (simp_all add: assms path_image_join)
    by (metis mid_eq_a midpoint_in_closed_segment)
  with \<open>0 < e\<close> obtain c where c: "c \<in> inside (path_image(p +++ linepath (a - e) (a + e)))"
                  and dac: "dist a c < e"
    by (auto simp: frontier_straddle)
  then have "c \<notin> path_image(p +++ linepath (a - e) (a + e))"
    using inside_no_overlap by blast
  then have "c \<notin> path_image p"
            "c \<notin> closed_segment (a - of_real e) (a + of_real e)"
    by (simp_all add: assms path_image_join)
  with \<open>0 < e\<close> dac have "c \<notin> affine hull {a - of_real e, a + of_real e}"
    by (simp add: segment_as_ball not_le)
  with \<open>0 < e\<close> have *: "\<not> collinear {a - e, c,a + e}"
    using collinear_3_affine_hull [of "a-e" "a+e"] by (auto simp: insert_commute)
  have 13: "1/3 + 1/3 + 1/3 = (1::real)" by simp
  have "(1/3) *\<^sub>R (a - of_real e) + (1/3) *\<^sub>R c + (1/3) *\<^sub>R (a + of_real e) \<in> interior(convex hull {a - e, c, a + e})"
    using interior_convex_hull_3_minimal [OF * DIM_complex]
    by clarsimp (metis 13 zero_less_divide_1_iff zero_less_numeral)
  then obtain z where z: "z \<in> interior(convex hull {a - e, c, a + e})" by force
  have [simp]: "z \<notin> closed_segment (a - e) c"
    by (metis DIM_complex Diff_iff IntD2 inf_sup_absorb interior_of_triangle z)
  have [simp]: "z \<notin> closed_segment (a + e) (a - e)"
    by (metis DIM_complex DiffD2 Un_iff interior_of_triangle z)
  have [simp]: "z \<notin> closed_segment c (a + e)"
    by (metis (no_types, lifting) DIM_complex DiffD2 Un_insert_right inf_sup_aci(5) insertCI interior_of_triangle mk_disjoint_insert z)
  show thesis
  proof
    have "norm (winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z) = 1"
      using winding_number_triangle [OF z] by simp
    have zin: "z \<in> inside (path_image (linepath (a + e) (a - e)) \<union> path_image p)"
      and zeq: "winding_number (linepath (a + e) (a - e) +++ reversepath p) z =
                winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z"
    proof (rule winding_number_from_innerpath
        [of "linepath (a + e) (a - e)" "a+e" "a-e" p
          "linepath (a + e) c +++ linepath c (a - e)" z
          "winding_number (linepath (a - e)  c +++ linepath  c (a + e) +++ linepath (a + e) (a - e)) z"])
      show sp_aec: "simple_path (linepath (a + e) c +++ linepath c (a - e))"
      proof (rule arc_imp_simple_path [OF arc_join])
        show "arc (linepath (a + e) c)"
          by (metis \<open>c \<notin> path_image p\<close> arc_linepath pathstart_in_path_image psp)
        show "arc (linepath c (a - e))"
          by (metis \<open>c \<notin> path_image p\<close> arc_linepath pathfinish_in_path_image pfp)
        show "path_image (linepath (a + e) c) \<inter> path_image (linepath c (a - e)) \<subseteq> {pathstart (linepath c (a - e))}"
          by clarsimp (metis "*" IntI Int_closed_segment closed_segment_commute singleton_iff)
      qed auto
      show "simple_path p"
        using \<open>arc p\<close> arc_simple_path by blast
      show sp_ae2: "simple_path (linepath (a + e) (a - e))"
        using \<open>arc p\<close> arc_distinct_ends pfp psp by fastforce
      show pa: "pathfinish (linepath (a + e) (a - e)) = a - e"
           "pathstart (linepath (a + e) c +++ linepath c (a - e)) = a + e"
           "pathfinish (linepath (a + e) c +++ linepath c (a - e)) = a - e"
           "pathstart p = a + e" "pathfinish p = a - e"
           "pathstart (linepath (a + e) (a - e)) = a + e"
        by (simp_all add: assms)
      show 1: "path_image (linepath (a + e) (a - e)) \<inter> path_image p = {a + e, a - e}"
      proof
        show "path_image (linepath (a + e) (a - e)) \<inter> path_image p \<subseteq> {a + e, a - e}"
          using pap closed_segment_commute psp segment_convex_hull by fastforce
        show "{a + e, a - e} \<subseteq> path_image (linepath (a + e) (a - e)) \<inter> path_image p"
          using pap pathfinish_in_path_image pathstart_in_path_image pfp psp by fastforce
      qed
      show 2: "path_image (linepath (a + e) (a - e)) \<inter> path_image (linepath (a + e) c +++ linepath c (a - e)) =
               {a + e, a - e}"  (is "?lhs = ?rhs")
      proof
        have "\<not> collinear {c, a + e, a - e}"
          using * by (simp add: insert_commute)
        then have "convex hull {a + e, a - e} \<inter> convex hull {a + e, c} = {a + e}"
                  "convex hull {a + e, a - e} \<inter> convex hull {c, a - e} = {a - e}"
          by (metis (full_types) Int_closed_segment insert_commute segment_convex_hull)+
        then show "?lhs \<subseteq> ?rhs"
          by (metis Int_Un_distrib equalityD1 insert_is_Un path_image_join path_image_linepath path_join_eq path_linepath segment_convex_hull simple_path_def sp_aec)
        show "?rhs \<subseteq> ?lhs"
          using segment_convex_hull by (simp add: path_image_join)
      qed
      have "path_image p \<inter> path_image (linepath (a + e) c) \<subseteq> {a + e}"
      proof (clarsimp simp: path_image_join)
        fix x
        assume "x \<in> path_image p" and x_ac: "x \<in> closed_segment (a + e) c"
        then have "dist x a \<ge> e"
          by (metis IntI all_not_in_conv disj dist_commute mem_ball not_less)
        with x_ac dac \<open>e > 0\<close> show "x = a + e"
          by (auto simp: norm_minus_commute dist_norm closed_segment_eq_open dest: open_segment_furthest_le [where y=a])
      qed
      moreover
      have "path_image p \<inter> path_image (linepath c (a - e)) \<subseteq> {a - e}"
      proof (clarsimp simp: path_image_join)
        fix x
        assume "x \<in> path_image p" and x_ac: "x \<in> closed_segment c (a - e)"
        then have "dist x a \<ge> e"
          by (metis IntI all_not_in_conv disj dist_commute mem_ball not_less)
        with x_ac dac \<open>e > 0\<close> show "x = a - e"
          by (auto simp: norm_minus_commute dist_norm closed_segment_eq_open dest: open_segment_furthest_le [where y=a])
      qed
      ultimately
      have "path_image p \<inter> path_image (linepath (a + e) c +++ linepath c (a - e)) \<subseteq> {a + e, a - e}"
        by (force simp: path_image_join)
      then show 3: "path_image p \<inter> path_image (linepath (a + e) c +++ linepath c (a - e)) = {a + e, a - e}"
        apply (rule equalityI)
        apply (clarsimp simp: path_image_join)
        apply (metis pathstart_in_path_image psp pathfinish_in_path_image pfp)
        done
      show 4: "path_image (linepath (a + e) c +++ linepath c (a - e)) \<inter>
               inside (path_image (linepath (a + e) (a - e)) \<union> path_image p) \<noteq> {}"
        apply (clarsimp simp: path_image_join segment_convex_hull disjoint_iff_not_equal)
        by (metis (no_types, hide_lams) UnI1 Un_commute c closed_segment_commute ends_in_segment(1) path_image_join
                  path_image_linepath pathstart_linepath pfp segment_convex_hull)
      show zin_inside: "z \<in> inside (path_image (linepath (a + e) (a - e)) \<union>
                                    path_image (linepath (a + e) c +++ linepath c (a - e)))"
        apply (simp add: path_image_join)
        by (metis z inside_of_triangle DIM_complex Un_commute closed_segment_commute)
      show 5: "winding_number
             (linepath (a + e) (a - e) +++ reversepath (linepath (a + e) c +++ linepath c (a - e))) z =
            winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z"
        by (simp add: reversepath_joinpaths path_image_join winding_number_join)
      show 6: "winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z \<noteq> 0"
        by (simp add: winding_number_triangle z)
      show "winding_number (linepath (a + e) (a - e) +++ reversepath p) z =
            winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z"
        by (metis 1 2 3 4 5 6 pa sp_aec sp_ae2 \<open>arc p\<close> \<open>simple_path p\<close> arc_distinct_ends winding_number_from_innerpath zin_inside)
    qed (use assms \<open>e > 0\<close> in auto)
    show "z \<in> inside (path_image (p +++ linepath (a - e) (a + e)))"
      using zin by (simp add: assms path_image_join Un_commute closed_segment_commute)
    then have "cmod (winding_number (p +++ linepath (a - e) (a + e)) z) =
               cmod ((winding_number(reversepath (p +++ linepath (a - e) (a + e))) z))"
      apply (subst winding_number_reversepath)
      using simple_path_imp_path sp_pl apply blast
       apply (metis IntI emptyE inside_no_overlap)
      by (simp add: inside_def)
    also have "... = cmod (winding_number(linepath (a + e) (a - e) +++ reversepath p) z)"
      by (simp add: pfp reversepath_joinpaths)
    also have "... = cmod (winding_number (linepath (a - e) c +++ linepath c (a + e) +++ linepath (a + e) (a - e)) z)"
      by (simp add: zeq)
    also have "... = 1"
      using z by (simp add: interior_of_triangle winding_number_triangle)
    finally show "cmod (winding_number (p +++ linepath (a - e) (a + e)) z) = 1" .
  qed
qed

lemma simple_closed_path_wn2:
  fixes a::complex and d e::real
  assumes "0 < d" "0 < e"
    and sp_pl: "simple_path(p +++ linepath (a - d) (a + e))"
    and psp:   "pathstart p = a + e"
    and pfp:   "pathfinish p = a - d"
obtains z where "z \<in> inside (path_image (p +++ linepath (a - d) (a + e)))"
                "cmod (winding_number (p +++ linepath (a - d) (a + e)) z) = 1"
proof -
  have [simp]: "a + of_real x \<in> closed_segment (a - \<alpha>) (a - \<beta>) \<longleftrightarrow> x \<in> closed_segment (-\<alpha>) (-\<beta>)" for x \<alpha> \<beta>::real
    using closed_segment_translation_eq [of a]
    by (metis (no_types, hide_lams) add_uminus_conv_diff of_real_minus of_real_closed_segment)
  have [simp]: "a - of_real x \<in> closed_segment (a + \<alpha>) (a + \<beta>) \<longleftrightarrow> -x \<in> closed_segment \<alpha> \<beta>" for x \<alpha> \<beta>::real
    by (metis closed_segment_translation_eq diff_conv_add_uminus of_real_closed_segment of_real_minus)
  have "arc p" and arc_lp: "arc (linepath (a - d) (a + e))" and "path p"
    and pap: "path_image p \<inter> closed_segment (a - d) (a + e) \<subseteq> {a+e, a-d}"
    using simple_path_join_loop_eq [of "linepath (a - d) (a + e)" p] assms arc_imp_path  by auto
  have "0 \<in> closed_segment (-d) e"
    using \<open>0 < d\<close> \<open>0 < e\<close> closed_segment_eq_real_ivl by auto
  then have "a \<in> path_image (linepath (a - d) (a + e))"
    using of_real_closed_segment [THEN iffD2]
    by (force dest: closed_segment_translation_eq [of a, THEN iffD2] simp del: of_real_closed_segment)
  then have "a \<notin> path_image p"
    using \<open>0 < d\<close> \<open>0 < e\<close> pap by auto
  then obtain k where "0 < k" and k: "ball a k \<inter> (path_image p) = {}"
    using \<open>0 < e\<close> \<open>path p\<close> not_on_path_ball by blast
  define kde where "kde \<equiv> (min k (min d e)) / 2"
  have "0 < kde" "kde < k" "kde < d" "kde < e"
    using \<open>0 < k\<close> \<open>0 < d\<close> \<open>0 < e\<close> by (auto simp: kde_def)
  let ?q = "linepath (a + kde) (a + e) +++ p +++ linepath (a - d) (a - kde)"
  have "- kde \<in> closed_segment (-d) e"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>kde < e\<close> closed_segment_eq_real_ivl by auto
  then have a_diff_kde: "a - kde \<in> closed_segment (a - d) (a + e)"
    using of_real_closed_segment [THEN iffD2]
    by (force dest: closed_segment_translation_eq [of a, THEN iffD2] simp del: of_real_closed_segment)
  then have clsub2: "closed_segment (a - d) (a - kde) \<subseteq> closed_segment (a - d) (a + e)"
    by (simp add: subset_closed_segment)
  then have "path_image p \<inter> closed_segment (a - d) (a - kde) \<subseteq> {a + e, a - d}"
    using pap by force
  moreover
  have "a + e \<notin> path_image p \<inter> closed_segment (a - d) (a - kde)"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>0 < e\<close> by (auto simp: closed_segment_eq_real_ivl)
  ultimately have sub_a_diff_d: "path_image p \<inter> closed_segment (a - d) (a - kde) \<subseteq> {a - d}"
    by blast
  have "kde \<in> closed_segment (-d) e"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>kde < e\<close> closed_segment_eq_real_ivl by auto
  then have a_diff_kde: "a + kde \<in> closed_segment (a - d) (a + e)"
    using of_real_closed_segment [THEN iffD2]
    by (force dest: closed_segment_translation_eq [of "a", THEN iffD2] simp del: of_real_closed_segment)
  then have clsub1: "closed_segment (a + kde) (a + e) \<subseteq> closed_segment (a - d) (a + e)"
    by (simp add: subset_closed_segment)
  then have "closed_segment (a + kde) (a + e) \<inter> path_image p \<subseteq> {a + e, a - d}"
    using pap by force
  moreover
  have "closed_segment (a + kde) (a + e) \<inter> closed_segment (a - d) (a - kde) = {}"
  proof (clarsimp intro!: equals0I)
    fix y
    assume y1: "y \<in> closed_segment (a + kde) (a + e)"
       and y2: "y \<in> closed_segment (a - d) (a - kde)"
    obtain u where u: "y = a + of_real u" and "0 < u"
      using y1 \<open>0 < kde\<close> \<open>kde < e\<close> \<open>0 < e\<close> apply (clarsimp simp: in_segment)
      apply (rule_tac u = "(1 - u)*kde + u*e" in that)
       apply (auto simp: scaleR_conv_of_real algebra_simps)
      by (meson le_less_trans less_add_same_cancel2 less_eq_real_def mult_left_mono)
    moreover
    obtain v where v: "y = a + of_real v" and "v \<le> 0"
      using y2 \<open>0 < kde\<close> \<open>0 < d\<close> \<open>0 < e\<close> apply (clarsimp simp: in_segment)
      apply (rule_tac v = "- ((1 - u)*d + u*kde)" in that)
       apply (force simp: scaleR_conv_of_real algebra_simps)
      by (meson less_eq_real_def neg_le_0_iff_le segment_bound_lemma)
    ultimately show False
      by auto
  qed
  moreover have "a - d \<notin> closed_segment (a + kde) (a + e)"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>0 < e\<close> by (auto simp: closed_segment_eq_real_ivl)
  ultimately have sub_a_plus_e:
    "closed_segment (a + kde) (a + e) \<inter> (path_image p \<union> closed_segment (a - d) (a - kde))
       \<subseteq> {a + e}"
    by auto
  have "kde \<in> closed_segment (-kde) e"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>kde < e\<close> closed_segment_eq_real_ivl by auto
  then have a_add_kde: "a + kde \<in> closed_segment (a - kde) (a + e)"
    using of_real_closed_segment [THEN iffD2]
    by (force dest: closed_segment_translation_eq [of "a", THEN iffD2] simp del: of_real_closed_segment)
  have "closed_segment (a - kde) (a + kde) \<inter> closed_segment (a + kde) (a + e) = {a + kde}"
    by (metis a_add_kde Int_closed_segment)
  moreover
  have "path_image p \<inter> closed_segment (a - kde) (a + kde) = {}"
  proof (rule equals0I, clarify)
    fix y  assume "y \<in> path_image p" "y \<in> closed_segment (a - kde) (a + kde)"
    with equals0D [OF k, of y] \<open>0 < kde\<close> \<open>kde < k\<close> show False
      by (auto simp: dist_norm dest: dist_decreases_closed_segment [where c=a])
  qed
  moreover
  have "- kde \<in> closed_segment (-d) kde"
    using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>kde < e\<close> closed_segment_eq_real_ivl by auto
  then have a_diff_kde': "a - kde \<in> closed_segment (a - d) (a + kde)"
    using of_real_closed_segment [THEN iffD2]
    by (force dest: closed_segment_translation_eq [of a, THEN iffD2] simp del: of_real_closed_segment)
  then have "closed_segment (a - d) (a - kde) \<inter> closed_segment (a - kde) (a + kde) = {a - kde}"
    by (metis Int_closed_segment)
  ultimately
  have pa_subset_pm_kde: "path_image ?q \<inter> closed_segment (a - kde) (a + kde) \<subseteq> {a - kde, a + kde}"
    by (auto simp: path_image_join assms)
  have ge_kde1: "\<exists>y. x = a + y \<and> y \<ge> kde" if "x \<in> closed_segment (a + kde) (a + e)" for x
    using that \<open>kde < e\<close> mult_le_cancel_left
    apply (auto simp: in_segment)
    apply (rule_tac x="(1-u)*kde + u*e" in exI)
    apply (fastforce simp: algebra_simps scaleR_conv_of_real)
    done
  have ge_kde2: "\<exists>y. x = a + y \<and> y \<le> -kde" if "x \<in> closed_segment (a - d) (a - kde)" for x
    using that \<open>kde < d\<close> affine_ineq
    apply (auto simp: in_segment)
    apply (rule_tac x="- ((1-u)*d + u*kde)" in exI)
    apply (fastforce simp: algebra_simps scaleR_conv_of_real)
    done
  have notin_paq: "x \<notin> path_image ?q" if "dist a x < kde" for x
    using that using \<open>0 < kde\<close> \<open>kde < d\<close> \<open>kde < k\<close>
    apply (auto simp: path_image_join assms dist_norm dest!: ge_kde1 ge_kde2)
    by (meson k disjoint_iff_not_equal le_less_trans less_eq_real_def mem_ball that)
  obtain z where zin: "z \<in> inside (path_image (?q +++ linepath (a - kde) (a + kde)))"
           and z1: "cmod (winding_number (?q +++ linepath (a - kde) (a + kde)) z) = 1"
  proof (rule simple_closed_path_wn1 [of kde ?q a])
    show "simple_path (?q +++ linepath (a - kde) (a + kde))"
    proof (intro simple_path_join_loop conjI)
      show "arc ?q"
      proof (rule arc_join)
        show "arc (linepath (a + kde) (a + e))"
          using \<open>kde < e\<close> \<open>arc p\<close> by (force simp: pfp)
        show "arc (p +++ linepath (a - d) (a - kde))"
          using \<open>kde < d\<close> \<open>kde < e\<close> \<open>arc p\<close> sub_a_diff_d by (force simp: pfp intro: arc_join)
      qed (auto simp: psp pfp path_image_join sub_a_plus_e)
      show "arc (linepath (a - kde) (a + kde))"
        using \<open>0 < kde\<close> by auto
    qed (use pa_subset_pm_kde in auto)
  qed (use \<open>0 < kde\<close> notin_paq in auto)
  have eq: "path_image (?q +++ linepath (a - kde) (a + kde)) = path_image (p +++ linepath (a - d) (a + e))"
            (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      using clsub1 clsub2 apply (auto simp: path_image_join assms)
      by (meson subsetCE subset_closed_segment)
    show "?rhs \<subseteq> ?lhs"
      apply (simp add: path_image_join assms Un_ac)
        by (metis Un_closed_segment Un_assoc a_diff_kde a_diff_kde' le_supI2 subset_refl)
    qed
  show thesis
  proof
    show zzin: "z \<in> inside (path_image (p +++ linepath (a - d) (a + e)))"
      by (metis eq zin)
    then have znotin: "z \<notin> path_image p"
      by (metis ComplD Un_iff inside_Un_outside path_image_join pathfinish_linepath pathstart_reversepath pfp reversepath_linepath)
    have znotin_de: "z \<notin> closed_segment (a - d) (a + kde)"
      by (metis ComplD Un_iff Un_closed_segment a_diff_kde inside_Un_outside path_image_join path_image_linepath pathstart_linepath pfp zzin)
    have "winding_number (linepath (a - d) (a + e)) z =
          winding_number (linepath (a - d) (a + kde)) z + winding_number (linepath (a + kde) (a + e)) z"
      apply (rule winding_number_split_linepath)
      apply (simp add: a_diff_kde)
      by (metis ComplD Un_iff inside_Un_outside path_image_join path_image_linepath pathstart_linepath pfp zzin)
    also have "... = winding_number (linepath (a + kde) (a + e)) z +
                     (winding_number (linepath (a - d) (a - kde)) z +
                      winding_number (linepath (a - kde) (a + kde)) z)"
      by (simp add: winding_number_split_linepath [of "a-kde", symmetric] znotin_de a_diff_kde')
    finally have "winding_number (p +++ linepath (a - d) (a + e)) z =
                    winding_number p z + winding_number (linepath (a + kde) (a + e)) z +
                   (winding_number (linepath (a - d) (a - kde)) z +
                    winding_number (linepath (a - kde) (a + kde)) z)"
      by (metis (no_types, lifting) ComplD Un_iff \<open>arc p\<close> add.assoc arc_imp_path eq path_image_join path_join_path_ends path_linepath simple_path_imp_path sp_pl union_with_outside winding_number_join zin)
    also have "... = winding_number ?q z + winding_number (linepath (a - kde) (a + kde)) z"
      using \<open>path p\<close> znotin assms zzin clsub1
      apply (subst winding_number_join, auto)
      apply (metis (no_types, hide_lams) ComplD Un_iff contra_subsetD inside_Un_outside path_image_join path_image_linepath pathstart_linepath)
      apply (metis Un_iff Un_closed_segment a_diff_kde' not_in_path_image_join path_image_linepath znotin_de)
      by (metis Un_iff Un_closed_segment a_diff_kde' path_image_linepath path_linepath pathstart_linepath winding_number_join znotin_de)
    also have "... = winding_number (?q +++ linepath (a - kde) (a + kde)) z"
      using \<open>path p\<close> assms zin
      apply (subst winding_number_join [symmetric], auto)
      apply (metis ComplD Un_iff path_image_join pathfinish_join pathfinish_linepath pathstart_linepath union_with_outside)
      by (metis Un_iff Un_closed_segment a_diff_kde' znotin_de)
    finally have "winding_number (p +++ linepath (a - d) (a + e)) z =
                  winding_number (?q +++ linepath (a - kde) (a + kde)) z" .
    then show "cmod (winding_number (p +++ linepath (a - d) (a + e)) z) = 1"
      by (simp add: z1)
  qed
qed

lemma simple_closed_path_wn3:
  fixes p :: "real \<Rightarrow> complex"
  assumes "simple_path p" and loop: "pathfinish p = pathstart p"
  obtains z where "z \<in> inside (path_image p)" "cmod (winding_number p z) = 1"
proof -
  have ins: "inside(path_image p) \<noteq> {}" "open(inside(path_image p))"
            "connected(inside(path_image p))"
   and out: "outside(path_image p) \<noteq> {}" "open(outside(path_image p))"
            "connected(outside(path_image p))"
   and bo:  "bounded(inside(path_image p))" "\<not> bounded(outside(path_image p))"
   and ins_out: "inside(path_image p) \<inter> outside(path_image p) = {}"
                "inside(path_image p) \<union> outside(path_image p) = - path_image p"
   and fro: "frontier(inside(path_image p)) = path_image p"
            "frontier(outside(path_image p)) = path_image p"
    using Jordan_inside_outside [OF assms] by auto
  obtain a where a: "a \<in> inside(path_image p)"
    using \<open>inside (path_image p) \<noteq> {}\<close> by blast
  obtain d::real where "0 < d" and d_fro: "a - d \<in> frontier (inside (path_image p))"
                 and d_int: "\<And>\<epsilon>. \<lbrakk>0 \<le> \<epsilon>; \<epsilon> < d\<rbrakk> \<Longrightarrow> (a - \<epsilon>) \<in> inside (path_image p)"
    apply (rule ray_to_frontier [of "inside (path_image p)" a "-1"])
    using \<open>bounded (inside (path_image p))\<close> \<open>open (inside (path_image p))\<close> a interior_eq
       apply (auto simp: of_real_def)
    done
  obtain e::real where "0 < e" and e_fro: "a + e \<in> frontier (inside (path_image p))"
    and e_int: "\<And>\<epsilon>. \<lbrakk>0 \<le> \<epsilon>; \<epsilon> < e\<rbrakk> \<Longrightarrow> (a + \<epsilon>) \<in> inside (path_image p)"
    apply (rule ray_to_frontier [of "inside (path_image p)" a 1])
    using \<open>bounded (inside (path_image p))\<close> \<open>open (inside (path_image p))\<close> a interior_eq
       apply (auto simp: of_real_def)
    done
  obtain t0 where "0 \<le> t0" "t0 \<le> 1" and pt: "p t0 = a - d"
    using a d_fro fro by (auto simp: path_image_def)
  obtain q where "simple_path q" and q_ends: "pathstart q = a - d" "pathfinish q = a - d"
    and q_eq_p: "path_image q = path_image p"
    and wn_q_eq_wn_p: "\<And>z. z \<in> inside(path_image p) \<Longrightarrow> winding_number q z = winding_number p z"
  proof
    show "simple_path (shiftpath t0 p)"
      by (simp add: pathstart_shiftpath pathfinish_shiftpath
          simple_path_shiftpath path_image_shiftpath \<open>0 \<le> t0\<close> \<open>t0 \<le> 1\<close> assms)
    show "pathstart (shiftpath t0 p) = a - d"
      using pt by (simp add: \<open>t0 \<le> 1\<close> pathstart_shiftpath)
    show "pathfinish (shiftpath t0 p) = a - d"
      by (simp add: \<open>0 \<le> t0\<close> loop pathfinish_shiftpath pt)
    show "path_image (shiftpath t0 p) = path_image p"
      by (simp add: \<open>0 \<le> t0\<close> \<open>t0 \<le> 1\<close> loop path_image_shiftpath)
    show "winding_number (shiftpath t0 p) z = winding_number p z"
      if "z \<in> inside (path_image p)" for z
      by (metis ComplD Un_iff \<open>0 \<le> t0\<close> \<open>t0 \<le> 1\<close> \<open>simple_path p\<close> atLeastAtMost_iff inside_Un_outside
          loop simple_path_imp_path that winding_number_shiftpath)
  qed
  have ad_not_ae: "a - d \<noteq> a + e"
    by (metis \<open>0 < d\<close> \<open>0 < e\<close> add.left_inverse add_left_cancel add_uminus_conv_diff
        le_add_same_cancel2 less_eq_real_def not_less of_real_add of_real_def of_real_eq_0_iff pt)
  have ad_ae_q: "{a - d, a + e} \<subseteq> path_image q"
    using \<open>path_image q = path_image p\<close> d_fro e_fro fro(1) by auto
  have ada: "open_segment (a - d) a \<subseteq> inside (path_image p)"
  proof (clarsimp simp: in_segment)
    fix u::real assume "0 < u" "u < 1"
    with d_int have "a - (1 - u) * d \<in> inside (path_image p)"
      by (metis \<open>0 < d\<close> add.commute diff_add_cancel left_diff_distrib' less_add_same_cancel2 less_eq_real_def mult.left_neutral zero_less_mult_iff)
    then show "(1 - u) *\<^sub>R (a - d) + u *\<^sub>R a \<in> inside (path_image p)"
      by (simp add: diff_add_eq of_real_def real_vector.scale_right_diff_distrib)
  qed
  have aae: "open_segment a (a + e) \<subseteq> inside (path_image p)"
  proof (clarsimp simp: in_segment)
    fix u::real assume "0 < u" "u < 1"
    with e_int have "a + u * e \<in> inside (path_image p)"
      by (meson \<open>0 < e\<close> less_eq_real_def mult_less_cancel_right2 not_less zero_less_mult_iff)
    then show "(1 - u) *\<^sub>R a + u *\<^sub>R (a + e) \<in> inside (path_image p)"
      apply (simp add: algebra_simps)
      by (simp add: diff_add_eq of_real_def real_vector.scale_right_diff_distrib)
  qed
  have "complex_of_real (d * d + (e * e + d * (e + e))) \<noteq> 0"
    using ad_not_ae
    by (metis \<open>0 < d\<close> \<open>0 < e\<close> add_strict_left_mono less_add_same_cancel1 not_sum_squares_lt_zero
        of_real_eq_0_iff zero_less_double_add_iff_zero_less_single_add zero_less_mult_iff)
  then have a_in_de: "a \<in> open_segment (a - d) (a + e)"
    using ad_not_ae \<open>0 < d\<close> \<open>0 < e\<close>
    apply (auto simp: in_segment algebra_simps scaleR_conv_of_real)
    apply (rule_tac x="d / (d+e)" in exI)
    apply (auto simp: field_simps)
    done
  then have "open_segment (a - d) (a + e) \<subseteq> inside (path_image p)"
    using ada a aae Un_open_segment [of a "a-d" "a+e"] by blast
  then have "path_image q \<inter> open_segment (a - d) (a + e) = {}"
    using inside_no_overlap by (fastforce simp: q_eq_p)
  with ad_ae_q have paq_Int_cs: "path_image q \<inter> closed_segment (a - d) (a + e) = {a - d, a + e}"
    by (simp add: closed_segment_eq_open)
  obtain t where "0 \<le> t" "t \<le> 1" and qt: "q t = a + e"
    using a e_fro fro ad_ae_q by (auto simp: path_defs)
  then have "t \<noteq> 0"
    by (metis ad_not_ae pathstart_def q_ends(1))
  then have "t \<noteq> 1"
    by (metis ad_not_ae pathfinish_def q_ends(2) qt)
  have q01: "q 0 = a - d" "q 1 = a - d"
    using q_ends by (auto simp: pathstart_def pathfinish_def)
  obtain z where zin: "z \<in> inside (path_image (subpath t 0 q +++ linepath (a - d) (a + e)))"
             and z1: "cmod (winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z) = 1"
  proof (rule simple_closed_path_wn2 [of d e "subpath t 0 q" a], simp_all add: q01)
    show "simple_path (subpath t 0 q +++ linepath (a - d) (a + e))"
    proof (rule simple_path_join_loop, simp_all add: qt q01)
      have "inj_on q (closed_segment t 0)"
        using \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close> \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close>
        by (fastforce simp: simple_path_def inj_on_def closed_segment_eq_real_ivl)
      then show "arc (subpath t 0 q)"
        using \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close> \<open>t \<noteq> 0\<close>
        by (simp add: arc_subpath_eq simple_path_imp_path)
      show "arc (linepath (a - d) (a + e))"
        by (simp add: ad_not_ae)
      show "path_image (subpath t 0 q) \<inter> closed_segment (a - d) (a + e) \<subseteq> {a + e, a - d}"
        using qt paq_Int_cs  \<open>simple_path q\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
        by (force simp: dest: rev_subsetD [OF _ path_image_subpath_subset] intro: simple_path_imp_path)
    qed
  qed (auto simp: \<open>0 < d\<close> \<open>0 < e\<close> qt)
  have pa01_Un: "path_image (subpath 0 t q) \<union> path_image (subpath 1 t q) = path_image q"
    unfolding path_image_subpath
    using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by (force simp: path_image_def image_iff)
  with paq_Int_cs have pa_01q:
        "(path_image (subpath 0 t q) \<union> path_image (subpath 1 t q)) \<inter> closed_segment (a - d) (a + e) = {a - d, a + e}"
    by metis
  have z_notin_ed: "z \<notin> closed_segment (a + e) (a - d)"
    using zin q01 by (simp add: path_image_join closed_segment_commute inside_def)
  have z_notin_0t: "z \<notin> path_image (subpath 0 t q)"
    by (metis (no_types, hide_lams) IntI Un_upper1 subsetD empty_iff inside_no_overlap path_image_join
        path_image_subpath_commute pathfinish_subpath pathstart_def pathstart_linepath q_ends(1) qt subpath_trivial zin)
  have [simp]: "- winding_number (subpath t 0 q) z = winding_number (subpath 0 t q) z"
    by (metis \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close> atLeastAtMost_iff zero_le_one
              path_image_subpath_commute path_subpath real_eq_0_iff_le_ge_0
              reversepath_subpath simple_path_imp_path winding_number_reversepath z_notin_0t)
  obtain z_in_q: "z \<in> inside(path_image q)"
     and wn_q: "winding_number (subpath 0 t q +++ subpath t 1 q) z = - winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z"
  proof (rule winding_number_from_innerpath
          [of "subpath 0 t q" "a-d" "a+e" "subpath 1 t q" "linepath (a - d) (a + e)"
            z "- winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z"],
         simp_all add: q01 qt pa01_Un reversepath_subpath)
    show "simple_path (subpath 0 t q)" "simple_path (subpath 1 t q)"
      by (simp_all add: \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close> \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close> simple_path_subpath)
    show "simple_path (linepath (a - d) (a + e))"
      using ad_not_ae by blast
    show "path_image (subpath 0 t q) \<inter> path_image (subpath 1 t q) = {a - d, a + e}"  (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
        using \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close> \<open>t \<noteq> 1\<close> q_ends qt q01
        by (force simp: pathfinish_def qt simple_path_def path_image_subpath)
      show "?rhs \<subseteq> ?lhs"
        using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> q01 qt by (force simp: path_image_subpath)
    qed
    show "path_image (subpath 0 t q) \<inter> closed_segment (a - d) (a + e) = {a - d, a + e}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"  using paq_Int_cs pa01_Un by fastforce
      show "?rhs \<subseteq> ?lhs"  using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> q01 qt by (force simp: path_image_subpath)
    qed
    show "path_image (subpath 1 t q) \<inter> closed_segment (a - d) (a + e) = {a - d, a + e}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"  by (auto simp: pa_01q [symmetric])
      show "?rhs \<subseteq> ?lhs"  using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> q01 qt by (force simp: path_image_subpath)
    qed
    show "closed_segment (a - d) (a + e) \<inter> inside (path_image q) \<noteq> {}"
      using a a_in_de open_closed_segment pa01_Un q_eq_p by fastforce
    show "z \<in> inside (path_image (subpath 0 t q) \<union> closed_segment (a - d) (a + e))"
      by (metis path_image_join path_image_linepath path_image_subpath_commute pathfinish_subpath pathstart_linepath q01(1) zin)
    show "winding_number (subpath 0 t q +++ linepath (a + e) (a - d)) z =
      - winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z"
      using z_notin_ed z_notin_0t \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close>
      by (simp add: simple_path_imp_path qt q01 path_image_subpath_commute closed_segment_commute winding_number_join winding_number_reversepath [symmetric])
    show "- d \<noteq> e"
      using ad_not_ae by auto
    show "winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z \<noteq> 0"
      using z1 by auto
  qed
  show ?thesis
  proof
    show "z \<in> inside (path_image p)"
      using q_eq_p z_in_q by auto
    then have [simp]: "z \<notin> path_image q"
      by (metis disjoint_iff_not_equal inside_no_overlap q_eq_p)
    have [simp]: "z \<notin> path_image (subpath 1 t q)"
      using inside_def pa01_Un z_in_q by fastforce
    have "winding_number(subpath 0 t q +++ subpath t 1 q) z = winding_number(subpath 0 1 q) z"
      using z_notin_0t \<open>0 \<le> t\<close> \<open>simple_path q\<close> \<open>t \<le> 1\<close>
      by (simp add: simple_path_imp_path qt path_image_subpath_commute winding_number_join winding_number_subpath_combine)
    with wn_q have "winding_number (subpath t 0 q +++ linepath (a - d) (a + e)) z = - winding_number q z"
      by auto
    with z1 have "cmod (winding_number q z) = 1"
      by simp
    with z1 wn_q_eq_wn_p show "cmod (winding_number p z) = 1"
      using z1 wn_q_eq_wn_p  by (simp add: \<open>z \<in> inside (path_image p)\<close>)
    qed
qed

proposition simple_closed_path_winding_number_inside:
  assumes "simple_path \<gamma>"
  obtains "\<And>z. z \<in> inside(path_image \<gamma>) \<Longrightarrow> winding_number \<gamma> z = 1"
        | "\<And>z. z \<in> inside(path_image \<gamma>) \<Longrightarrow> winding_number \<gamma> z = -1"
proof (cases "pathfinish \<gamma> = pathstart \<gamma>")
  case True
  have "path \<gamma>"
    by (simp add: assms simple_path_imp_path)
  then have const: "winding_number \<gamma> constant_on inside(path_image \<gamma>)"
  proof (rule winding_number_constant)
    show "connected (inside(path_image \<gamma>))"
      by (simp add: Jordan_inside_outside True assms)
  qed (use inside_no_overlap True in auto)
  obtain z where zin: "z \<in> inside (path_image \<gamma>)" and z1: "cmod (winding_number \<gamma> z) = 1"
    using simple_closed_path_wn3 [of \<gamma>] True assms by blast
  have "winding_number \<gamma> z \<in> \<int>"
    using zin integer_winding_number [OF \<open>path \<gamma>\<close> True] inside_def by blast
  with z1 consider "winding_number \<gamma> z = 1" | "winding_number \<gamma> z = -1"
    apply (auto simp: Ints_def abs_if split: if_split_asm)
    by (metis of_int_1 of_int_eq_iff of_int_minus)
  with that const zin show ?thesis
    unfolding constant_on_def by metis
next
  case False
  then show ?thesis
    using inside_simple_curve_imp_closed assms that(2) by blast
qed

lemma simple_closed_path_abs_winding_number_inside:
  assumes "simple_path \<gamma>" "z \<in> inside(path_image \<gamma>)"
    shows "\<bar>Re (winding_number \<gamma> z)\<bar> = 1"
  by (metis assms norm_minus_cancel norm_one one_complex.simps(1) real_norm_def simple_closed_path_winding_number_inside uminus_complex.simps(1))

lemma simple_closed_path_norm_winding_number_inside:
  assumes "simple_path \<gamma>" "z \<in> inside(path_image \<gamma>)"
  shows "norm (winding_number \<gamma> z) = 1"
proof -
  have "pathfinish \<gamma> = pathstart \<gamma>"
    using assms inside_simple_curve_imp_closed by blast
  with assms integer_winding_number have "winding_number \<gamma> z \<in> \<int>"
    by (simp add: inside_def simple_path_def)
  then show ?thesis
    by (metis assms norm_minus_cancel norm_one simple_closed_path_winding_number_inside)
qed

lemma simple_closed_path_winding_number_cases:
   "\<lbrakk>simple_path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> path_image \<gamma>\<rbrakk> \<Longrightarrow> winding_number \<gamma> z \<in> {-1,0,1}"
apply (simp add: inside_Un_outside [of "path_image \<gamma>", symmetric, unfolded set_eq_iff Set.Compl_iff] del: inside_Un_outside)
   apply (rule simple_closed_path_winding_number_inside)
  using simple_path_def winding_number_zero_in_outside by blast+

lemma simple_closed_path_winding_number_pos:
   "\<lbrakk>simple_path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> path_image \<gamma>; 0 < Re(winding_number \<gamma> z)\<rbrakk>
    \<Longrightarrow> winding_number \<gamma> z = 1"
using simple_closed_path_winding_number_cases
  by fastforce

subsection \<open>Winding number for rectangular paths\<close>

proposition winding_number_rectpath:
  assumes "z \<in> box a1 a3"
  shows   "winding_number (rectpath a1 a3) z = 1"
proof -
  from assms have less: "Re a1 < Re a3" "Im a1 < Im a3"
    by (auto simp: in_box_complex_iff)
  define a2 a4 where "a2 = Complex (Re a3) (Im a1)" and "a4 = Complex (Re a1) (Im a3)"
  let ?l1 = "linepath a1 a2" and ?l2 = "linepath a2 a3"
  and ?l3 = "linepath a3 a4" and ?l4 = "linepath a4 a1"
  from assms and less have "z \<notin> path_image (rectpath a1 a3)"
    by (auto simp: path_image_rectpath_cbox_minus_box)
  also have "path_image (rectpath a1 a3) =
               path_image ?l1 \<union> path_image ?l2 \<union> path_image ?l3 \<union> path_image ?l4"
    by (simp add: rectpath_def Let_def path_image_join Un_assoc a2_def a4_def)
  finally have "z \<notin> \<dots>" .
  moreover have "\<forall>l\<in>{?l1,?l2,?l3,?l4}. Re (winding_number l z) > 0"
    unfolding ball_simps HOL.simp_thms a2_def a4_def
    by (intro conjI; (rule winding_number_linepath_pos_lt;
          (insert assms, auto simp: a2_def a4_def in_box_complex_iff mult_neg_neg))+)
  ultimately have "Re (winding_number (rectpath a1 a3) z) > 0"
    by (simp add: winding_number_join path_image_join rectpath_def Let_def a2_def a4_def)
  thus "winding_number (rectpath a1 a3) z = 1" using assms less
    by (intro simple_closed_path_winding_number_pos simple_path_rectpath)
       (auto simp: path_image_rectpath_cbox_minus_box)
qed

proposition winding_number_rectpath_outside:
  assumes "Re a1 \<le> Re a3" "Im a1 \<le> Im a3"
  assumes "z \<notin> cbox a1 a3"
  shows   "winding_number (rectpath a1 a3) z = 0"
  using assms by (intro winding_number_zero_outside[OF _ _ _ assms(3)]
                     path_image_rectpath_subset_cbox) simp_all

text\<open>A per-function version for continuous logs, a kind of monodromy\<close>
proposition\<^marker>\<open>tag unimportant\<close> winding_number_compose_exp:
  assumes "path p"
  shows "winding_number (exp \<circ> p) 0 = (pathfinish p - pathstart p) / (2 * of_real pi * \<i>)"
proof -
  obtain e where "0 < e" and e: "\<And>t. t \<in> {0..1} \<Longrightarrow> e \<le> norm(exp(p t))"
  proof
    have "closed (path_image (exp \<circ> p))"
      by (simp add: assms closed_path_image holomorphic_on_exp holomorphic_on_imp_continuous_on path_continuous_image)
    then show "0 < setdist {0} (path_image (exp \<circ> p))"
      by (metis exp_not_eq_zero imageE image_comp infdist_eq_setdist infdist_pos_not_in_closed path_defs(4) path_image_nonempty)
  next
    fix t::real
    assume "t \<in> {0..1}"
    have "setdist {0} (path_image (exp \<circ> p)) \<le> dist 0 (exp (p t))"
      apply (rule setdist_le_dist)
      using \<open>t \<in> {0..1}\<close> path_image_def by fastforce+
    then show "setdist {0} (path_image (exp \<circ> p)) \<le> cmod (exp (p t))"
      by simp
  qed
  have "bounded (path_image p)"
    by (simp add: assms bounded_path_image)
  then obtain B where "0 < B" and B: "path_image p \<subseteq> cball 0 B"
    by (meson bounded_pos mem_cball_0 subsetI)
  let ?B = "cball (0::complex) (B+1)"
  have "uniformly_continuous_on ?B exp"
    using holomorphic_on_exp holomorphic_on_imp_continuous_on
    by (force intro: compact_uniformly_continuous)
  then obtain d where "d > 0"
        and d: "\<And>x x'. \<lbrakk>x\<in>?B; x'\<in>?B; dist x' x < d\<rbrakk> \<Longrightarrow> norm (exp x' - exp x) < e"
    using \<open>e > 0\<close> by (auto simp: uniformly_continuous_on_def dist_norm)
  then have "min 1 d > 0"
    by force
  then obtain g where pfg: "polynomial_function g"  and "g 0 = p 0" "g 1 = p 1"
           and gless: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm(g t - p t) < min 1 d"
    using path_approx_polynomial_function [OF \<open>path p\<close>] \<open>d > 0\<close> \<open>0 < e\<close>
    unfolding pathfinish_def pathstart_def by blast
  have "winding_number (exp \<circ> p) 0 = winding_number (exp \<circ> g) 0"
  proof (rule winding_number_nearby_paths_eq [symmetric])
    show "path (exp \<circ> p)" "path (exp \<circ> g)"
      by (simp_all add: pfg assms holomorphic_on_exp holomorphic_on_imp_continuous_on path_continuous_image path_polynomial_function)
  next
    fix t :: "real"
    assume t: "t \<in> {0..1}"
    with gless have "norm(g t - p t) < 1"
      using min_less_iff_conj by blast
    moreover have ptB: "norm (p t) \<le> B"
      using B t by (force simp: path_image_def)
    ultimately have "cmod (g t) \<le> B + 1"
      by (meson add_mono_thms_linordered_field(4) le_less_trans less_imp_le norm_triangle_sub)
    with ptB gless t have "cmod ((exp \<circ> g) t - (exp \<circ> p) t) < e"
      by (auto simp: dist_norm d)
    with e t show "cmod ((exp \<circ> g) t - (exp \<circ> p) t) < cmod ((exp \<circ> p) t - 0)"
      by fastforce
  qed (use \<open>g 0 = p 0\<close> \<open>g 1 = p 1\<close> in \<open>auto simp: pathfinish_def pathstart_def\<close>)
  also have "... = 1 / (of_real (2 * pi) * \<i>) * contour_integral (exp \<circ> g) (\<lambda>w. 1 / (w - 0))"
  proof (rule winding_number_valid_path)
    have "continuous_on (path_image g) (deriv exp)"
      by (metis DERIV_exp DERIV_imp_deriv continuous_on_cong holomorphic_on_exp holomorphic_on_imp_continuous_on)
    then show "valid_path (exp \<circ> g)"
      by (simp add: field_differentiable_within_exp pfg valid_path_compose valid_path_polynomial_function)
    show "0 \<notin> path_image (exp \<circ> g)"
      by (auto simp: path_image_def)
  qed
  also have "... = 1 / (of_real (2 * pi) * \<i>) * integral {0..1} (\<lambda>x. vector_derivative g (at x))"
  proof (simp add: contour_integral_integral, rule integral_cong)
    fix t :: "real"
    assume t: "t \<in> {0..1}"
    show "vector_derivative (exp \<circ> g) (at t) / exp (g t) = vector_derivative g (at t)"
    proof -
      have "(exp \<circ> g has_vector_derivative vector_derivative (exp \<circ> g) (at t)) (at t)"
        by (meson DERIV_exp differentiable_def field_vector_diff_chain_at has_vector_derivative_def
            has_vector_derivative_polynomial_function pfg vector_derivative_works)
      moreover have "(exp \<circ> g has_vector_derivative vector_derivative g (at t) * exp (g t)) (at t)"
        apply (rule field_vector_diff_chain_at)
        apply (metis has_vector_derivative_polynomial_function pfg vector_derivative_at)
        using DERIV_exp has_field_derivative_def apply blast
        done
      ultimately show ?thesis
        by (simp add: divide_simps, rule vector_derivative_unique_at)
    qed
  qed
  also have "... = (pathfinish p - pathstart p) / (2 * of_real pi * \<i>)"
  proof -
    have "((\<lambda>x. vector_derivative g (at x)) has_integral g 1 - g 0) {0..1}"
      apply (rule fundamental_theorem_of_calculus [OF zero_le_one])
      by (metis has_vector_derivative_at_within has_vector_derivative_polynomial_function pfg vector_derivative_at)
    then show ?thesis
      unfolding pathfinish_def pathstart_def
      using \<open>g 0 = p 0\<close> \<open>g 1 = p 1\<close> by auto
  qed
  finally show ?thesis .
qed

end
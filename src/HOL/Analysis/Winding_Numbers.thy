section \<open>Winding Numbers\<close>
theory Winding_Numbers 
  imports Cauchy_Integral_Theorem
begin

text\<open>We can treat even non-rectifiable paths as having a "length" for bounds on analytic functions in open sets.\<close>

subsection \<open>Basic Winding Numbers\<close>

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
    using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "d/2"] d by auto
  define nn where "nn = 1/(2* pi*\<i>) * contour_integral h (\<lambda>w. 1/(w - z))"
  have "\<exists>n. \<forall>e > 0. \<exists>p. winding_number_prop \<gamma> z e p n"
    proof (rule_tac x=nn in exI, clarify)
      fix e::real
      assume e: "e>0"
      obtain p where p: "polynomial_function p \<and>
            pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and> (\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < min e (d/2))"
        using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "min e (d/2)"] d \<open>0<e\<close> by auto
      have "(\<lambda>w. 1 / (w - z)) holomorphic_on UNIV - {z}"
        by (auto simp: intro!: holomorphic_intros)
      then show "\<exists>p. winding_number_prop \<gamma> z e p nn"
        apply (rule_tac x=p in exI)
        using pi_eq [of h p] h p d
        apply (auto simp: valid_path_polynomial_function norm_minus_commute nn_def winding_number_prop_def)
        done
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

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some lemmas about negating a path\<close>

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

lemma contour_integrable_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and pi: "(\<lambda>z. f (- z)) contour_integrable_on \<gamma>"
  shows "f contour_integrable_on (uminus \<circ> \<gamma>)"
  by (metis \<gamma> add.inverse_inverse contour_integrable_on_def has_contour_integral_negatepath pi)

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
    using contour_integral_bound_exists [of "- cball z (3/4*pe)" p] cbp \<open>valid_path p\<close> by force
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
        using path_approx_polynomial_function [OF \<gamma>, of "min 1 e"] \<open>e>0\<close> by force
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

subsection \<open>The real part of winding numbers\<close>

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

subsection \<open>Invariance of winding numbers under homotopy\<close>

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

subsection \<open>Winding numbers of some simple paths\<close>

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

lemma simply_connected_imp_winding_number_zero:
  assumes "simply_connected S" "path g"
           "path_image g \<subseteq> S" "pathfinish g = pathstart g" "z \<notin> S"
    shows "winding_number g z = 0"
proof -
  have hom: "homotopic_loops S g (linepath (pathstart g) (pathstart g))"
    by (meson assms homotopic_paths_imp_homotopic_loops pathfinish_linepath simply_connected_eq_contractible_path)
  then have "homotopic_paths (- {z}) g (linepath (pathstart g) (pathstart g))"
    by (meson \<open>z \<notin> S\<close> homotopic_loops_imp_homotopic_paths_null homotopic_paths_subset subset_Compl_singleton)
  then have "winding_number g z = winding_number(linepath (pathstart g) (pathstart g)) z"
    by (rule winding_number_homotopic_paths)
  also have "\<dots> = 0"
    using assms by (force intro: winding_number_trivial)
  finally show ?thesis .
qed

end
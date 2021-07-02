theory Complex_Residues
  imports Complex_Singularities
begin

subsection \<open>Definition of residues\<close>

text\<open>Wenda Li and LC Paulson (2016). A Formal Proof of Cauchy's Residue Theorem.
    Interactive Theorem Proving\<close>

definition\<^marker>\<open>tag important\<close> residue :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "residue f z = (SOME int. \<exists>e>0. \<forall>\<epsilon>>0. \<epsilon><e
    \<longrightarrow> (f has_contour_integral 2*pi* \<i> *int) (circlepath z \<epsilon>))"

lemma residue_cong:
  assumes eq: "eventually (\<lambda>z. f z = g z) (at z)" and "z = z'"
  shows   "residue f z = residue g z'"
proof -
  from assms have eq': "eventually (\<lambda>z. g z = f z) (at z)"
    by (simp add: eq_commute)
  let ?P = "\<lambda>f c e. (\<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow>
   (f has_contour_integral of_real (2 * pi) * \<i> * c) (circlepath z \<epsilon>))"
  have "residue f z = residue g z" unfolding residue_def
  proof (rule Eps_cong)
    fix c :: complex
    have "\<exists>e>0. ?P g c e"
      if "\<exists>e>0. ?P f c e" and "eventually (\<lambda>z. f z = g z) (at z)" for f g
    proof -
      from that(1) obtain e where e: "e > 0" "?P f c e"
        by blast
      from that(2) obtain e' where e': "e' > 0" "\<And>z'. z' \<noteq> z \<Longrightarrow> dist z' z < e' \<Longrightarrow> f z' = g z'"
        unfolding eventually_at by blast
      have "?P g c (min e e')"
      proof (intro allI exI impI, goal_cases)
        case (1 \<epsilon>)
        hence "(f has_contour_integral of_real (2 * pi) * \<i> * c) (circlepath z \<epsilon>)"
          using e(2) by auto
        thus ?case
        proof (rule has_contour_integral_eq)
          fix z' assume "z' \<in> path_image (circlepath z \<epsilon>)"
          hence "dist z' z < e'" and "z' \<noteq> z"
            using 1 by (auto simp: dist_commute)
          with e'(2)[of z'] show "f z' = g z'" by simp
        qed
      qed
      moreover from e and e' have "min e e' > 0" by auto
      ultimately show ?thesis by blast
    qed
    from this[OF _ eq] and this[OF _ eq']
      show "(\<exists>e>0. ?P f c e) \<longleftrightarrow> (\<exists>e>0. ?P g c e)"
      by blast
  qed
  with assms show ?thesis by simp
qed

lemma contour_integral_circlepath_eq:
  assumes "open s" and f_holo:"f holomorphic_on (s-{z})" and "0<e1" "e1\<le>e2"
    and e2_cball:"cball z e2 \<subseteq> s"
  shows
    "f contour_integrable_on circlepath z e1"
    "f contour_integrable_on circlepath z e2"
    "contour_integral (circlepath z e2) f = contour_integral (circlepath z e1) f"
proof -
  define l where "l \<equiv> linepath (z+e2) (z+e1)"
  have [simp]:"valid_path l" "pathstart l=z+e2" "pathfinish l=z+e1" unfolding l_def by auto
  have "e2>0" using \<open>e1>0\<close> \<open>e1\<le>e2\<close> by auto
  have zl_img:"z\<notin>path_image l"
    proof
      assume "z \<in> path_image l"
      then have "e2 \<le> cmod (e2 - e1)"
        using segment_furthest_le[of z "z+e2" "z+e1" "z+e2",simplified] \<open>e1>0\<close> \<open>e2>0\<close> unfolding l_def
        by (auto simp add:closed_segment_commute)
      thus False using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
        apply (subst (asm) norm_of_real)
        by auto
    qed
  define g where "g \<equiv> circlepath z e2 +++ l +++ reversepath (circlepath z e1) +++ reversepath l"
  show [simp]: "f contour_integrable_on circlepath z e2" "f contour_integrable_on (circlepath z e1)"
    proof -
      show "f contour_integrable_on circlepath z e2"
        apply (intro contour_integrable_continuous_circlepath[OF
                continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        using \<open>e2>0\<close> e2_cball by auto
      show "f contour_integrable_on (circlepath z e1)"
        apply (intro contour_integrable_continuous_circlepath[OF
                      continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        using \<open>e1>0\<close> \<open>e1\<le>e2\<close> e2_cball by auto
    qed
  have [simp]:"f contour_integrable_on l"
    proof -
      have "closed_segment (z + e2) (z + e1) \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
        by (intro closed_segment_subset,auto simp add:dist_norm)
      hence "closed_segment (z + e2) (z + e1) \<subseteq> s - {z}" using zl_img e2_cball unfolding l_def
        by auto
      then show "f contour_integrable_on l" unfolding l_def
        apply (intro contour_integrable_continuous_linepath[OF
                      continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        by auto
    qed
  let ?ig="\<lambda>g. contour_integral g f"
  have "(f has_contour_integral 0) g"
    proof (rule Cauchy_theorem_global[OF _ f_holo])
      show "open (s - {z})" using \<open>open s\<close> by auto
      show "valid_path g" unfolding g_def l_def by auto
      show "pathfinish g = pathstart g" unfolding g_def l_def by auto
    next
      have path_img:"path_image g \<subseteq> cball z e2"
        proof -
          have "closed_segment (z + e2) (z + e1) \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
            by (intro closed_segment_subset,auto simp add:dist_norm)
          moreover have "sphere z \<bar>e1\<bar> \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1\<le>e2\<close> \<open>e1>0\<close> by auto
          ultimately show ?thesis unfolding g_def l_def using \<open>e2>0\<close>
            by (simp add: path_image_join closed_segment_commute)
        qed
      show "path_image g \<subseteq> s - {z}"
        proof -
          have "z\<notin>path_image g" using zl_img
            unfolding g_def l_def by (auto simp add: path_image_join closed_segment_commute)
          moreover note \<open>cball z e2 \<subseteq> s\<close> and path_img
          ultimately show ?thesis by auto
        qed
      show "winding_number g w = 0" when"w \<notin> s - {z}" for w
        proof -
          have "winding_number g w = 0" when "w\<notin>s" using that e2_cball
            apply (intro winding_number_zero_outside[OF _ _ _ _ path_img])
            by (auto simp add:g_def l_def)
          moreover have "winding_number g z=0"
            proof -
              let ?Wz="\<lambda>g. winding_number g z"
              have "?Wz g = ?Wz (circlepath z e2) + ?Wz l + ?Wz (reversepath (circlepath z e1))
                  + ?Wz (reversepath l)"
                using \<open>e2>0\<close> \<open>e1>0\<close> zl_img unfolding g_def l_def
                by (subst winding_number_join,auto simp add:path_image_join closed_segment_commute)+
              also have "... = ?Wz (circlepath z e2) + ?Wz (reversepath (circlepath z e1))"
                using zl_img
                apply (subst (2) winding_number_reversepath)
                by (auto simp add:l_def closed_segment_commute)
              also have "... = 0"
                proof -
                  have "?Wz (circlepath z e2) = 1" using \<open>e2>0\<close>
                    by (auto intro: winding_number_circlepath_centre)
                  moreover have "?Wz (reversepath (circlepath z e1)) = -1" using \<open>e1>0\<close>
                    apply (subst winding_number_reversepath)
                    by (auto intro: winding_number_circlepath_centre)
                  ultimately show ?thesis by auto
                qed
              finally show ?thesis .
            qed
          ultimately show ?thesis using that by auto
        qed
    qed
  then have "0 = ?ig g" using contour_integral_unique by simp
  also have "... = ?ig (circlepath z e2) + ?ig l + ?ig (reversepath (circlepath z e1))
      + ?ig (reversepath l)"
    unfolding g_def
    by (auto simp add:contour_integrable_reversepath_eq)
  also have "... = ?ig (circlepath z e2)  - ?ig (circlepath z e1)"
    by (auto simp add:contour_integral_reversepath)
  finally show "contour_integral (circlepath z e2) f = contour_integral (circlepath z e1) f"
    by simp
qed

lemma base_residue:
  assumes "open s" "z\<in>s" "r>0" and f_holo:"f holomorphic_on (s - {z})"
    and r_cball:"cball z r \<subseteq> s"
  shows "(f has_contour_integral 2 * pi * \<i> * (residue f z)) (circlepath z r)"
proof -
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s"
    using open_contains_cball[of s] \<open>open s\<close> \<open>z\<in>s\<close> by auto
  define c where "c \<equiv> 2 * pi * \<i>"
  define i where "i \<equiv> contour_integral (circlepath z e) f / c"
  have "(f has_contour_integral c*i) (circlepath z \<epsilon>)" when "\<epsilon>>0" "\<epsilon><e" for \<epsilon>
    proof -
      have "contour_integral (circlepath z e) f = contour_integral (circlepath z \<epsilon>) f"
          "f contour_integrable_on circlepath z \<epsilon>"
          "f contour_integrable_on circlepath z e"
        using \<open>\<epsilon><e\<close>
        by (intro contour_integral_circlepath_eq[OF \<open>open s\<close> f_holo \<open>\<epsilon>>0\<close> _ e_cball],auto)+
      then show ?thesis unfolding i_def c_def
        by (auto intro:has_contour_integral_integral)
    qed
  then have "\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon><e \<longrightarrow> (f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    unfolding residue_def c_def
    apply (rule_tac someI[of _ i],intro  exI[where x=e])
    by (auto simp add:\<open>e>0\<close> c_def)
  then obtain e' where "e'>0"
      and e'_def:"\<forall>\<epsilon>>0. \<epsilon><e' \<longrightarrow> (f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    by auto
  let ?int="\<lambda>e. contour_integral (circlepath z e) f"
  define  \<epsilon> where "\<epsilon> \<equiv> Min {r,e'} / 2"
  have "\<epsilon>>0" "\<epsilon>\<le>r" "\<epsilon><e'" using \<open>r>0\<close> \<open>e'>0\<close> unfolding \<epsilon>_def by auto
  have "(f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    using e'_def[rule_format,OF \<open>\<epsilon>>0\<close> \<open>\<epsilon><e'\<close>] .
  then show ?thesis unfolding c_def
    using contour_integral_circlepath_eq[OF \<open>open s\<close> f_holo \<open>\<epsilon>>0\<close> \<open>\<epsilon>\<le>r\<close> r_cball]
    by (auto elim: has_contour_integral_eqpath[of _ _ "circlepath z \<epsilon>" "circlepath z r"])
qed

lemma residue_holo:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s"
  shows "residue f z = 0"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f has_contour_integral c*residue f z) (circlepath z e)"
    using f_holo
    by (auto intro: base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
  moreover have "(f has_contour_integral 0) (circlepath z e)"
    using f_holo e_cball \<open>e>0\<close>
    by (auto intro: Cauchy_theorem_convex_simple[of _ "cball z e"])
  ultimately have "c*residue f z =0"
    using has_contour_integral_unique by blast
  thus ?thesis unfolding c_def  by auto
qed

lemma residue_const:"residue (\<lambda>_. c) z = 0"
  by (intro residue_holo[of "UNIV::complex set"],auto intro:holomorphic_intros)

lemma residue_add:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
      and g_holo:"g holomorphic_on s - {z}"
  shows "residue (\<lambda>z. f z + g z) z= residue f z + residue g z"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  define fg where "fg \<equiv> (\<lambda>z. f z+g z)"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(fg has_contour_integral c * residue fg z) (circlepath z e)"
    unfolding fg_def using f_holo g_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
    by (auto intro:holomorphic_intros)
  moreover have "(fg has_contour_integral c*residue f z + c* residue g z) (circlepath z e)"
    unfolding fg_def using f_holo g_holo
    by (auto intro: has_contour_integral_add base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
  ultimately have "c*(residue f z + residue g z) = c * residue fg z"
    using has_contour_integral_unique by (auto simp add:distrib_left)
  thus ?thesis unfolding fg_def
    by (auto simp add:c_def)
qed

lemma residue_lmul:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. c * (f z)) z= c * residue f z"
proof (cases "c=0")
  case True
  thus ?thesis using residue_const by auto
next
  case False
  define c' where "c' \<equiv> 2 * pi * \<i>"
  define f' where "f' \<equiv> (\<lambda>z. c * (f z))"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f' has_contour_integral c' * residue f' z) (circlepath z e)"
    unfolding f'_def using f_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c'_def])
    by (auto intro:holomorphic_intros)
  moreover have "(f' has_contour_integral c * (c' * residue f z)) (circlepath z e)"
    unfolding f'_def using f_holo
    by (auto intro: has_contour_integral_lmul
      base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c'_def])
  ultimately have "c' * residue f' z  = c * (c' * residue f z)"
    using has_contour_integral_unique by auto
  thus ?thesis unfolding f'_def c'_def using False
    by (auto simp add:field_simps)
qed

lemma residue_rmul:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. (f z) * c) z= residue f z * c"
using residue_lmul[OF assms,of c] by (auto simp add:algebra_simps)

lemma residue_div:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. (f z) / c) z= residue f z / c "
using residue_lmul[OF assms,of "1/c"] by (auto simp add:algebra_simps)

lemma residue_neg:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. - (f z)) z= - residue f z"
using residue_lmul[OF assms,of "-1"] by auto

lemma residue_diff:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
      and g_holo:"g holomorphic_on s - {z}"
  shows "residue (\<lambda>z. f z - g z) z= residue f z - residue g z"
using residue_add[OF assms(1,2,3),of "\<lambda>z. - g z"] residue_neg[OF assms(1,2,4)]
by (auto intro:holomorphic_intros g_holo)

lemma residue_simple:
  assumes "open s" "z\<in>s" and f_holo:"f holomorphic_on s"
  shows "residue (\<lambda>w. f w / (w - z)) z = f z"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  define f' where "f' \<equiv> \<lambda>w. f w / (w - z)"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f' has_contour_integral c * f z) (circlepath z e)"
    unfolding f'_def c_def using \<open>e>0\<close> f_holo e_cball
    by (auto intro!: Cauchy_integral_circlepath_simple holomorphic_intros)
  moreover have "(f' has_contour_integral c * residue f' z) (circlepath z e)"
    unfolding f'_def using f_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
    by (auto intro!:holomorphic_intros)
  ultimately have "c * f z = c * residue f' z"
    using has_contour_integral_unique by blast
  thus ?thesis unfolding c_def f'_def  by auto
qed

lemma residue_simple':
  assumes s: "open s" "z \<in> s" and holo: "f holomorphic_on (s - {z})"
      and lim: "((\<lambda>w. f w * (w - z)) \<longlongrightarrow> c) (at z)"
  shows   "residue f z = c"
proof -
  define g where "g = (\<lambda>w. if w = z then c else f w * (w - z))"
  from holo have "(\<lambda>w. f w * (w - z)) holomorphic_on (s - {z})" (is "?P")
    by (force intro: holomorphic_intros)
  also have "?P \<longleftrightarrow> g holomorphic_on (s - {z})"
    by (intro holomorphic_cong refl) (simp_all add: g_def)
  finally have *: "g holomorphic_on (s - {z})" .

  note lim
  also have "(\<lambda>w. f w * (w - z)) \<midarrow>z\<rightarrow> c \<longleftrightarrow> g \<midarrow>z\<rightarrow> g z"
    by (intro filterlim_cong refl) (simp_all add: g_def [abs_def] eventually_at_filter)
  finally have **: "g \<midarrow>z\<rightarrow> g z" .

  have g_holo: "g holomorphic_on s"
    by (rule no_isolated_singularity'[where K = "{z}"])
       (insert assms * **, simp_all add: at_within_open_NO_MATCH)
  from s and this have "residue (\<lambda>w. g w / (w - z)) z = g z"
    by (rule residue_simple)
  also have "\<forall>\<^sub>F za in at z. g za / (za - z) = f za"
    unfolding eventually_at by (auto intro!: exI[of _ 1] simp: field_simps g_def)
  hence "residue (\<lambda>w. g w / (w - z)) z = residue f z"
    by (intro residue_cong refl)
  finally show ?thesis
    by (simp add: g_def)
qed

lemma residue_holomorphic_over_power:
  assumes "open A" "z0 \<in> A" "f holomorphic_on A"
  shows   "residue (\<lambda>z. f z / (z - z0) ^ Suc n) z0 = (deriv ^^ n) f z0 / fact n"
proof -
  let ?f = "\<lambda>z. f z / (z - z0) ^ Suc n"
  from assms(1,2) obtain r where r: "r > 0" "cball z0 r \<subseteq> A"
    by (auto simp: open_contains_cball)
  have "(?f has_contour_integral 2 * pi * \<i> * residue ?f z0) (circlepath z0 r)"
    using r assms by (intro base_residue[of A]) (auto intro!: holomorphic_intros)
  moreover have "(?f has_contour_integral 2 * pi * \<i> / fact n * (deriv ^^ n) f z0) (circlepath z0 r)"
    using assms r
    by (intro Cauchy_has_contour_integral_higher_derivative_circlepath)
       (auto intro!: holomorphic_on_subset[OF assms(3)] holomorphic_on_imp_continuous_on)
  ultimately have "2 * pi * \<i> * residue ?f z0 = 2 * pi * \<i> / fact n * (deriv ^^ n) f z0"
    by (rule has_contour_integral_unique)
  thus ?thesis by (simp add: field_simps)
qed

lemma residue_holomorphic_over_power':
  assumes "open A" "0 \<in> A" "f holomorphic_on A"
  shows   "residue (\<lambda>z. f z / z ^ Suc n) 0 = (deriv ^^ n) f 0 / fact n"
  using residue_holomorphic_over_power[OF assms] by simp

theorem residue_fps_expansion_over_power_at_0:
  assumes "f has_fps_expansion F"
  shows   "residue (\<lambda>z. f z / z ^ Suc n) 0 = fps_nth F n"
proof -
  from has_fps_expansion_imp_holomorphic[OF assms] guess s . note s = this
  have "residue (\<lambda>z. f z / (z - 0) ^ Suc n) 0 = (deriv ^^ n) f 0 / fact n"
    using assms s unfolding has_fps_expansion_def
    by (intro residue_holomorphic_over_power[of s]) (auto simp: zero_ereal_def)
  also from assms have "\<dots> = fps_nth F n"
    by (subst fps_nth_fps_expansion) auto
  finally show ?thesis by simp
qed

lemma residue_pole_order:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n \<equiv> nat (- zorder f z)" and "h \<equiv> zor_poly f z"
  assumes f_iso:"isolated_singularity_at f z"
    and pole:"is_pole f z"
  shows "residue f z = ((deriv ^^ (n - 1)) h z / fact (n-1))"
proof -
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  obtain e where [simp]:"e>0" and f_holo:"f holomorphic_on ball z e - {z}"
    using f_iso analytic_imp_holomorphic unfolding isolated_singularity_at_def by blast
  obtain r where "0 < n" "0 < r" and r_cball:"cball z r \<subseteq> ball z e" and h_holo: "h holomorphic_on cball z r"
      and h_divide:"(\<forall>w\<in>cball z r. (w\<noteq>z \<longrightarrow> f w = h w / (w - z) ^ n) \<and> h w \<noteq> 0)"
  proof -
    obtain r where r:"zorder f z < 0" "h z \<noteq> 0" "r>0" "cball z r \<subseteq> ball z e" "h holomorphic_on cball z r"
        "(\<forall>w\<in>cball z r - {z}. f w = h w / (w - z) ^ n \<and> h w \<noteq> 0)"
      using zorder_exist_pole[OF f_holo,simplified,OF \<open>is_pole f z\<close>,folded n_def h_def] by auto
    have "n>0" using \<open>zorder f z < 0\<close> unfolding n_def by simp
    moreover have "(\<forall>w\<in>cball z r. (w\<noteq>z \<longrightarrow> f w = h w / (w - z) ^ n) \<and> h w \<noteq> 0)"
      using \<open>h z\<noteq>0\<close> r(6) by blast
    ultimately show ?thesis using r(3,4,5) that by blast
  qed
  have r_nonzero:"\<And>w. w \<in> ball z r - {z} \<Longrightarrow> f w \<noteq> 0"
    using h_divide by simp
  define c where "c \<equiv> 2 * pi * \<i>"
  define der_f where "der_f \<equiv> ((deriv ^^ (n - 1)) h z / fact (n-1))"
  define h' where "h' \<equiv> \<lambda>u. h u / (u - z) ^ n"
  have "(h' has_contour_integral c / fact (n - 1) * (deriv ^^ (n - 1)) h z) (circlepath z r)"
    unfolding h'_def
    proof (rule Cauchy_has_contour_integral_higher_derivative_circlepath[of z r h z "n-1",
        folded c_def Suc_pred'[OF \<open>n>0\<close>]])
      show "continuous_on (cball z r) h" using holomorphic_on_imp_continuous_on h_holo by simp
      show "h holomorphic_on ball z r" using h_holo by auto
      show " z \<in> ball z r" using \<open>r>0\<close> by auto
    qed
  then have "(h' has_contour_integral c * der_f) (circlepath z r)" unfolding der_f_def by auto
  then have "(f has_contour_integral c * der_f) (circlepath z r)"
    proof (elim has_contour_integral_eq)
      fix x assume "x \<in> path_image (circlepath z r)"
      hence "x\<in>cball z r - {z}" using \<open>r>0\<close> by auto
      then show "h' x = f x" using h_divide unfolding h'_def by auto
    qed
  moreover have "(f has_contour_integral c * residue f z) (circlepath z r)"
    using base_residue[of \<open>ball z e\<close> z,simplified,OF \<open>r>0\<close> f_holo r_cball,folded c_def]
    unfolding c_def by simp
  ultimately have "c * der_f =  c * residue f z" using has_contour_integral_unique by blast
  hence "der_f = residue f z" unfolding c_def by auto
  thus ?thesis unfolding der_f_def by auto
qed

lemma residue_simple_pole:
  assumes "isolated_singularity_at f z0"
  assumes "is_pole f z0" "zorder f z0 = - 1"
  shows   "residue f z0 = zor_poly f z0 z0"
  using assms by (subst residue_pole_order) simp_all

lemma residue_simple_pole_limit:
  assumes "isolated_singularity_at f z0"
  assumes "is_pole f z0" "zorder f z0 = - 1"
  assumes "((\<lambda>x. f (g x) * (g x - z0)) \<longlongrightarrow> c) F"
  assumes "filterlim g (at z0) F" "F \<noteq> bot"
  shows   "residue f z0 = c"
proof -
  have "residue f z0 = zor_poly f z0 z0"
    by (rule residue_simple_pole assms)+
  also have "\<dots> = c"
    apply (rule zor_poly_pole_eqI)
    using assms by auto
  finally show ?thesis .
qed

lemma
  assumes f_holo:"f holomorphic_on s" and g_holo:"g holomorphic_on s"
          and "open s" "connected s" "z \<in> s"
  assumes g_deriv:"(g has_field_derivative g') (at z)"
  assumes "f z \<noteq> 0" "g z = 0" "g' \<noteq> 0"
  shows   porder_simple_pole_deriv: "zorder (\<lambda>w. f w / g w) z = - 1"
    and   residue_simple_pole_deriv: "residue (\<lambda>w. f w / g w) z = f z / g'"
proof -
  have [simp]:"isolated_singularity_at f z" "isolated_singularity_at g z"
    using isolated_singularity_at_holomorphic[OF _ \<open>open s\<close> \<open>z\<in>s\<close>] f_holo g_holo
    by (meson Diff_subset holomorphic_on_subset)+
  have [simp]:"not_essential f z" "not_essential g z"
    unfolding not_essential_def using f_holo g_holo assms(3,5)
    by (meson continuous_on_eq_continuous_at continuous_within holomorphic_on_imp_continuous_on)+
  have g_nconst:"\<exists>\<^sub>F w in at z. g w \<noteq>0 "
  proof (rule ccontr)
    assume "\<not> (\<exists>\<^sub>F w in at z. g w \<noteq> 0)"
    then have "\<forall>\<^sub>F w in nhds z. g w = 0"
      unfolding eventually_at eventually_nhds frequently_at using \<open>g z = 0\<close>
      by (metis open_ball UNIV_I centre_in_ball dist_commute mem_ball)
    then have "deriv g z = deriv (\<lambda>_. 0) z"
      by (intro deriv_cong_ev) auto
    then have "deriv g z = 0" by auto
    then have "g' = 0" using g_deriv DERIV_imp_deriv by blast
    then show False using \<open>g'\<noteq>0\<close> by auto
  qed

  have "zorder (\<lambda>w. f w / g w) z = zorder f z - zorder g z"
  proof -
    have "\<forall>\<^sub>F w in at z. f w \<noteq>0 \<and> w\<in>s"
      apply (rule non_zero_neighbour_alt)
      using assms by auto
    with g_nconst have "\<exists>\<^sub>F w in at z. f w * g w \<noteq> 0"
      by (elim frequently_rev_mp eventually_rev_mp,auto)
    then show ?thesis using zorder_divide[of f z g] by auto
  qed
  moreover have "zorder f z=0"
    apply (rule zorder_zero_eqI[OF f_holo \<open>open s\<close> \<open>z\<in>s\<close>])
    using \<open>f z\<noteq>0\<close> by auto
  moreover have "zorder g z=1"
    apply (rule zorder_zero_eqI[OF g_holo \<open>open s\<close> \<open>z\<in>s\<close>])
    subgoal using assms(8) by auto
    subgoal using DERIV_imp_deriv assms(9) g_deriv by auto
    subgoal by simp
    done
  ultimately show "zorder (\<lambda>w. f w / g w) z = - 1" by auto

  show "residue (\<lambda>w. f w / g w) z = f z / g'"
  proof (rule residue_simple_pole_limit[where g=id and F="at z",simplified])
    show "zorder (\<lambda>w. f w / g w) z = - 1" by fact
    show "isolated_singularity_at (\<lambda>w. f w / g w) z"
      by (auto intro: singularity_intros)
    show "is_pole (\<lambda>w. f w / g w) z"
    proof (rule is_pole_divide)
      have "\<forall>\<^sub>F x in at z. g x \<noteq> 0"
        apply (rule non_zero_neighbour)
        using g_nconst by auto
      moreover have "g \<midarrow>z\<rightarrow> 0"
        using DERIV_isCont assms(8) continuous_at g_deriv by force
      ultimately show "filterlim g (at 0) (at z)" unfolding filterlim_at by simp
      show "isCont f z"
        using assms(3,5) continuous_on_eq_continuous_at f_holo holomorphic_on_imp_continuous_on
        by auto
      show "f z \<noteq> 0" by fact
    qed
    show "filterlim id (at z) (at z)" by (simp add: filterlim_iff)
    have "((\<lambda>w. (f w * (w - z)) / g w) \<longlongrightarrow> f z / g') (at z)"
    proof (rule lhopital_complex_simple)
      show "((\<lambda>w. f w * (w - z)) has_field_derivative f z) (at z)"
        using assms by (auto intro!: derivative_eq_intros holomorphic_derivI[OF f_holo])
      show "(g has_field_derivative g') (at z)" by fact
    qed (insert assms, auto)
    then show "((\<lambda>w. (f w / g w) * (w - z)) \<longlongrightarrow> f z / g') (at z)"
      by (simp add: field_split_simps)
  qed
qed


subsection \<open>Poles and residues of some well-known functions\<close>

(* TODO: add more material here for other functions *)
lemma is_pole_Gamma: "is_pole Gamma (-of_nat n)"
  unfolding is_pole_def using Gamma_poles .

lemma Gamma_residue:
  "residue Gamma (-of_nat n) = (-1) ^ n / fact n"
proof (rule residue_simple')
  show "open (- (\<int>\<^sub>\<le>\<^sub>0 - {-of_nat n}) :: complex set)"
    by (intro open_Compl closed_subset_Ints) auto
  show "Gamma holomorphic_on (- (\<int>\<^sub>\<le>\<^sub>0 - {-of_nat n}) - {- of_nat n})"
    by (rule holomorphic_Gamma) auto
  show "(\<lambda>w. Gamma w * (w - (-of_nat n))) \<midarrow>(-of_nat n)\<rightarrow> (- 1) ^ n / fact n"
    using Gamma_residues[of n] by simp
qed auto

end

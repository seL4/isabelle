section \<open>Winding Numbers\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2017)\<close>

theory Winding_Numbers
imports Polytope Jordan_Curve Riemann_Mapping
begin

lemma simply_connected_inside_simple_path:
  fixes p :: "real \<Rightarrow> complex"
  shows "simple_path p \<Longrightarrow> simply_connected(inside(path_image p))"
  using Jordan_inside_outside connected_simple_path_image inside_simple_curve_imp_closed simply_connected_eq_frontier_properties
  by fastforce

lemma simply_connected_Int:
  fixes S :: "complex set"
  assumes "open S" "open T" "simply_connected S" "simply_connected T" "connected (S \<inter> T)"
  shows "simply_connected (S \<inter> T)"
  using assms by (force simp: simply_connected_eq_winding_number_zero open_Int)

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
    by simp
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

(* TODO: Move *)
lemma closed_segmentI:
  "u \<in> {0..1} \<Longrightarrow> z = (1 - u) *\<^sub>R a + u *\<^sub>R b \<Longrightarrow> z \<in> closed_segment a b"
  by (auto simp: closed_segment_def)

lemma in_cbox_complex_iff:
  "x \<in> cbox a b \<longleftrightarrow> Re x \<in> {Re a..Re b} \<and> Im x \<in> {Im a..Im b}"
  by (cases x; cases a; cases b) (auto simp: cbox_Complex_eq)

lemma box_Complex_eq:
  "box (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (box a b \<times> box c d)"
  by (auto simp: box_def Basis_complex_def image_iff complex_eq_iff)

lemma in_box_complex_iff:
  "x \<in> box a b \<longleftrightarrow> Re x \<in> {Re a<..<Re b} \<and> Im x \<in> {Im a<..<Im b}"
  by (cases x; cases a; cases b) (auto simp: box_Complex_eq)
(* END TODO *)

lemma closed_segment_same_Re:
  assumes "Re a = Re b"
  shows   "closed_segment a b = {z. Re z = Re a \<and> Im z \<in> closed_segment (Im a) (Im b)}"
proof safe
  fix z assume "z \<in> closed_segment a b"
  then obtain u where u: "u \<in> {0..1}" "z = a + of_real u * (b - a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from assms show "Re z = Re a" by (auto simp: u)
  from u(1) show "Im z \<in> closed_segment (Im a) (Im b)"
    by (intro closed_segmentI[of u]) (auto simp: u algebra_simps)
next
  fix z assume [simp]: "Re z = Re a" and "Im z \<in> closed_segment (Im a) (Im b)"
  then obtain u where u: "u \<in> {0..1}" "Im z = Im a + of_real u * (Im b - Im a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from u(1) show "z \<in> closed_segment a b" using assms
    by (intro closed_segmentI[of u]) (auto simp: u algebra_simps scaleR_conv_of_real complex_eq_iff)
qed

lemma closed_segment_same_Im:
  assumes "Im a = Im b"
  shows   "closed_segment a b = {z. Im z = Im a \<and> Re z \<in> closed_segment (Re a) (Re b)}"
proof safe
  fix z assume "z \<in> closed_segment a b"
  then obtain u where u: "u \<in> {0..1}" "z = a + of_real u * (b - a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from assms show "Im z = Im a" by (auto simp: u)
  from u(1) show "Re z \<in> closed_segment (Re a) (Re b)"
    by (intro closed_segmentI[of u]) (auto simp: u algebra_simps)
next
  fix z assume [simp]: "Im z = Im a" and "Re z \<in> closed_segment (Re a) (Re b)"
  then obtain u where u: "u \<in> {0..1}" "Re z = Re a + of_real u * (Re b - Re a)"
    by (auto simp: closed_segment_def scaleR_conv_of_real algebra_simps)
  from u(1) show "z \<in> closed_segment a b" using assms
    by (intro closed_segmentI[of u]) (auto simp: u algebra_simps scaleR_conv_of_real complex_eq_iff)
qed

definition%important rectpath where
  "rectpath a1 a3 = (let a2 = Complex (Re a3) (Im a1); a4 = Complex (Re a1) (Im a3)
                      in linepath a1 a2 +++ linepath a2 a3 +++ linepath a3 a4 +++ linepath a4 a1)"

lemma path_rectpath [simp, intro]: "path (rectpath a b)"
  by (simp add: Let_def rectpath_def)

lemma valid_path_rectpath [simp, intro]: "valid_path (rectpath a b)"
  by (simp add: Let_def rectpath_def)

lemma pathstart_rectpath [simp]: "pathstart (rectpath a1 a3) = a1"
  by (simp add: rectpath_def Let_def)

lemma pathfinish_rectpath [simp]: "pathfinish (rectpath a1 a3) = a1"
  by (simp add: rectpath_def Let_def)

lemma simple_path_rectpath [simp, intro]:
  assumes "Re a1 \<noteq> Re a3" "Im a1 \<noteq> Im a3"
  shows   "simple_path (rectpath a1 a3)"
  unfolding rectpath_def Let_def using assms
  by (intro simple_path_join_loop arc_join arc_linepath)
     (auto simp: complex_eq_iff path_image_join closed_segment_same_Re closed_segment_same_Im)

lemma path_image_rectpath:
  assumes "Re a1 \<le> Re a3" "Im a1 \<le> Im a3"
  shows "path_image (rectpath a1 a3) =
           {z. Re z \<in> {Re a1, Re a3} \<and> Im z \<in> {Im a1..Im a3}} \<union>
           {z. Im z \<in> {Im a1, Im a3} \<and> Re z \<in> {Re a1..Re a3}}" (is "?lhs = ?rhs")
proof -
  define a2 a4 where "a2 = Complex (Re a3) (Im a1)" and "a4 = Complex (Re a1) (Im a3)"
  have "?lhs = closed_segment a1 a2 \<union> closed_segment a2 a3 \<union>
                  closed_segment a4 a3 \<union> closed_segment a1 a4"
    by (simp_all add: rectpath_def Let_def path_image_join closed_segment_commute
                      a2_def a4_def Un_assoc)
  also have "\<dots> = ?rhs" using assms
    by (auto simp: rectpath_def Let_def path_image_join a2_def a4_def
          closed_segment_same_Re closed_segment_same_Im closed_segment_eq_real_ivl)
  finally show ?thesis .
qed

lemma path_image_rectpath_subset_cbox:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<subseteq> cbox a b"
  using assms by (auto simp: path_image_rectpath in_cbox_complex_iff)

lemma path_image_rectpath_inter_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<inter> box a b = {}"
  using assms by (auto simp: path_image_rectpath in_box_complex_iff)

lemma path_image_rectpath_cbox_minus_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) = cbox a b - box a b"
  using assms by (auto simp: path_image_rectpath in_cbox_complex_iff
                             in_box_complex_iff)

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
proposition%unimportant winding_number_compose_exp:
  assumes "path p"
  shows "winding_number (exp \<circ> p) 0 = (pathfinish p - pathstart p) / (2 * of_real pi * \<i>)"
proof -
  obtain e where "0 < e" and e: "\<And>t. t \<in> {0..1} \<Longrightarrow> e \<le> norm(exp(p t))"
  proof
     have "closed (path_image (exp \<circ> p))"
       by (simp add: assms closed_path_image holomorphic_on_exp holomorphic_on_imp_continuous_on path_continuous_image)
    then show "0 < setdist {0} (path_image (exp \<circ> p))"
      by (metis (mono_tags, lifting) compact_sing exp_not_eq_zero imageE path_image_compose
               path_image_nonempty setdist_eq_0_compact_closed setdist_gt_0_compact_closed setdist_eq_0_closed)
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
    unfolding pathfinish_def pathstart_def by meson
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
    proof (simp add: divide_simps, rule vector_derivative_unique_at)
      show "(exp \<circ> g has_vector_derivative vector_derivative (exp \<circ> g) (at t)) (at t)"
        by (meson DERIV_exp differentiable_def field_vector_diff_chain_at has_vector_derivative_def
            has_vector_derivative_polynomial_function pfg vector_derivative_works)
      show "(exp \<circ> g has_vector_derivative vector_derivative g (at t) * exp (g t)) (at t)"
        apply (rule field_vector_diff_chain_at)
        apply (metis has_vector_derivative_polynomial_function pfg vector_derivative_at)
        using DERIV_exp has_field_derivative_def apply blast
        done
    qed
  qed
  also have "... = (pathfinish p - pathstart p) / (2 * of_real pi * \<i>)"
  proof -
    have "((\<lambda>x. vector_derivative g (at x)) has_integral g 1 - g 0) {0..1}"
      apply (rule fundamental_theorem_of_calculus [OF zero_le_one])
      by (metis has_vector_derivative_at_within has_vector_derivative_polynomial_function pfg vector_derivative_at)
    then show ?thesis
    apply (simp add: pathfinish_def pathstart_def)
      using \<open>g 0 = p 0\<close> \<open>g 1 = p 1\<close> by auto
  qed
  finally show ?thesis .
qed

subsection%unimportant \<open>The winding number defines a continuous logarithm for the path itself\<close>

lemma winding_number_as_continuous_log:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  obtains q where "path q"
                  "pathfinish q - pathstart q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
                  "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = \<zeta> + exp(q t)"
proof -
  let ?q = "\<lambda>t. 2 * of_real pi * \<i> * winding_number(subpath 0 t p) \<zeta> + Ln(pathstart p - \<zeta>)"
  show ?thesis
  proof
    have *: "continuous (at t within {0..1}) (\<lambda>x. winding_number (subpath 0 x p) \<zeta>)"
      if t: "t \<in> {0..1}" for t
    proof -
      let ?B = "ball (p t) (norm(p t - \<zeta>))"
      have "p t \<noteq> \<zeta>"
        using path_image_def that \<zeta> by blast
      then have "simply_connected ?B"
        by (simp add: convex_imp_simply_connected)
      then have "\<And>f::complex\<Rightarrow>complex. continuous_on ?B f \<and> (\<forall>\<zeta> \<in> ?B. f \<zeta> \<noteq> 0)
                  \<longrightarrow> (\<exists>g. continuous_on ?B g \<and> (\<forall>\<zeta> \<in> ?B. f \<zeta> = exp (g \<zeta>)))"
        by (simp add: simply_connected_eq_continuous_log)
      moreover have "continuous_on ?B (\<lambda>w. w - \<zeta>)"
        by (intro continuous_intros)
      moreover have "(\<forall>z \<in> ?B. z - \<zeta> \<noteq> 0)"
        by (auto simp: dist_norm)
      ultimately obtain g where contg: "continuous_on ?B g"
        and geq: "\<And>z. z \<in> ?B \<Longrightarrow> z - \<zeta> = exp (g z)" by blast
      obtain d where "0 < d" and d:
        "\<And>x. \<lbrakk>x \<in> {0..1}; dist x t < d\<rbrakk> \<Longrightarrow> dist (p x) (p t) < cmod (p t - \<zeta>)"
        using \<open>path p\<close> t unfolding path_def continuous_on_iff
        by (metis \<open>p t \<noteq> \<zeta>\<close> right_minus_eq zero_less_norm_iff)
      have "((\<lambda>x. winding_number (\<lambda>w. subpath 0 x p w - \<zeta>) 0 -
                  winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0) \<longlongrightarrow> 0)
            (at t within {0..1})"
      proof (rule Lim_transform_within [OF _ \<open>d > 0\<close>])
        have "continuous (at t within {0..1}) (g o p)"
        proof (rule continuous_within_compose)
          show "continuous (at t within {0..1}) p"
            using \<open>path p\<close> continuous_on_eq_continuous_within path_def that by blast
          show "continuous (at (p t) within p ` {0..1}) g"
            by (metis (no_types, lifting) open_ball UNIV_I \<open>p t \<noteq> \<zeta>\<close> centre_in_ball contg continuous_on_eq_continuous_at continuous_within_topological right_minus_eq zero_less_norm_iff)
        qed
        with LIM_zero have "((\<lambda>u. (g (subpath t u p 1) - g (subpath t u p 0))) \<longlongrightarrow> 0) (at t within {0..1})"
          by (auto simp: subpath_def continuous_within o_def)
        then show "((\<lambda>u.  (g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>)) \<longlongrightarrow> 0)
           (at t within {0..1})"
          by (simp add: tendsto_divide_zero)
        show "(g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>) =
              winding_number (\<lambda>w. subpath 0 u p w - \<zeta>) 0 - winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0"
          if "u \<in> {0..1}" "0 < dist u t" "dist u t < d" for u
        proof -
          have "closed_segment t u \<subseteq> {0..1}"
            using closed_segment_eq_real_ivl t that by auto
          then have piB: "path_image(subpath t u p) \<subseteq> ?B"
            apply (clarsimp simp add: path_image_subpath_gen)
            by (metis subsetD le_less_trans \<open>dist u t < d\<close> d dist_commute dist_in_closed_segment)
          have *: "path (g \<circ> subpath t u p)"
            apply (rule path_continuous_image)
            using \<open>path p\<close> t that apply auto[1]
            using piB contg continuous_on_subset by blast
          have "(g (subpath t u p 1) - g (subpath t u p 0)) / (2 * of_real pi * \<i>)
              =  winding_number (exp \<circ> g \<circ> subpath t u p) 0"
            using winding_number_compose_exp [OF *]
            by (simp add: pathfinish_def pathstart_def o_assoc)
          also have "... = winding_number (\<lambda>w. subpath t u p w - \<zeta>) 0"
          proof (rule winding_number_cong)
            have "exp(g y) = y - \<zeta>" if "y \<in> (subpath t u p) ` {0..1}" for y
              by (metis that geq path_image_def piB subset_eq)
            then show "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> (exp \<circ> g \<circ> subpath t u p) x = subpath t u p x - \<zeta>"
              by auto
          qed
          also have "... = winding_number (\<lambda>w. subpath 0 u p w - \<zeta>) 0 -
                           winding_number (\<lambda>w. subpath 0 t p w - \<zeta>) 0"
            apply (simp add: winding_number_offset [symmetric])
            using winding_number_subpath_combine [OF \<open>path p\<close> \<zeta>, of 0 t u] \<open>t \<in> {0..1}\<close> \<open>u \<in> {0..1}\<close>
            by (simp add: add.commute eq_diff_eq)
          finally show ?thesis .
        qed
      qed
      then show ?thesis
        by (subst winding_number_offset) (simp add: continuous_within LIM_zero_iff)
    qed
    show "path ?q"
      unfolding path_def
      by (intro continuous_intros) (simp add: continuous_on_eq_continuous_within *)

    have "\<zeta> \<noteq> p 0"
      by (metis \<zeta> pathstart_def pathstart_in_path_image)
    then show "pathfinish ?q - pathstart ?q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
      by (simp add: pathfinish_def pathstart_def)
    show "p t = \<zeta> + exp (?q t)" if "t \<in> {0..1}" for t
    proof -
      have "path (subpath 0 t p)"
        using \<open>path p\<close> that by auto
      moreover
      have "\<zeta> \<notin> path_image (subpath 0 t p)"
        using \<zeta> [unfolded path_image_def] that by (auto simp: path_image_subpath)
      ultimately show ?thesis
        using winding_number_exp_2pi [of "subpath 0 t p" \<zeta>] \<open>\<zeta> \<noteq> p 0\<close>
        by (auto simp: exp_add algebra_simps pathfinish_def pathstart_def subpath_def)
    qed
  qed
qed

subsection \<open>Winding number equality is the same as path/loop homotopy in C - {0}\<close>

lemma winding_number_homotopic_loops_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_loops (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
proof
  assume [simp]: ?lhs
  obtain q where "path q"
             and qeq:  "pathfinish q - pathstart q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
             and peq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = \<zeta> + exp(q t)"
    using winding_number_as_continuous_log [OF assms] by blast
  have *: "homotopic_with (\<lambda>r. pathfinish r = pathstart r)
                       {0..1} (-{\<zeta>}) ((\<lambda>w. \<zeta> + exp w) \<circ> q) ((\<lambda>w. \<zeta> + exp w) \<circ> (\<lambda>t. 0))"
  proof (rule homotopic_with_compose_continuous_left)
    show "homotopic_with (\<lambda>f. pathfinish ((\<lambda>w. \<zeta> + exp w) \<circ> f) = pathstart ((\<lambda>w. \<zeta> + exp w) \<circ> f))
              {0..1} UNIV q (\<lambda>t. 0)"
    proof (rule homotopic_with_mono, simp_all add: pathfinish_def pathstart_def)
      have "homotopic_loops UNIV q (\<lambda>t. 0)"
        by (rule homotopic_loops_linear) (use qeq \<open>path q\<close> in \<open>auto simp: continuous_on_const path_defs\<close>)
      then show "homotopic_with (\<lambda>h. exp (h 1) = exp (h 0)) {0..1} UNIV q (\<lambda>t. 0)"
        by (simp add: homotopic_loops_def homotopic_with_mono pathfinish_def pathstart_def)
    qed
    show "continuous_on UNIV (\<lambda>w. \<zeta> + exp w)"
      by (rule continuous_intros)+
    show "range (\<lambda>w. \<zeta> + exp w) \<subseteq> -{\<zeta>}"
      by auto
  qed
  then have "homotopic_with (\<lambda>r. pathfinish r = pathstart r) {0..1} (-{\<zeta>}) p (\<lambda>x. \<zeta> + 1)"
    by (rule homotopic_with_eq) (auto simp: o_def peq pathfinish_def pathstart_def)
  then have "homotopic_loops (-{\<zeta>}) p (\<lambda>t. \<zeta> + 1)"
    by (simp add: homotopic_loops_def)
  then show ?rhs ..
next
  assume ?rhs
  then obtain a where "homotopic_loops (-{\<zeta>}) p (\<lambda>t. a)" ..
  then have "winding_number p \<zeta> = winding_number (\<lambda>t. a) \<zeta>" "a \<noteq> \<zeta>"
    using winding_number_homotopic_loops homotopic_loops_imp_subset by (force simp:)+
  moreover have "winding_number (\<lambda>t. a) \<zeta> = 0"
    by (metis winding_number_zero_const \<open>a \<noteq> \<zeta>\<close>)
  ultimately show ?lhs by metis
qed

lemma winding_number_homotopic_paths_null_explicit_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p (linepath (pathstart p) (pathstart p))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: winding_number_homotopic_loops_null_eq [OF assms])
    apply (rule homotopic_loops_imp_homotopic_paths_null)
    apply (simp add: linepath_refl)
    done
next
  assume ?rhs
  then show ?lhs
    by (metis \<zeta> pathstart_in_path_image winding_number_homotopic_paths winding_number_trivial)
qed

lemma winding_number_homotopic_paths_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_paths (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: winding_number_homotopic_paths_null_explicit_eq [OF assms] linepath_refl)
next
  assume ?rhs
  then show ?lhs
    by (metis \<zeta> homotopic_paths_imp_pathfinish pathfinish_def pathfinish_in_path_image winding_number_homotopic_paths winding_number_zero_const)
qed

proposition winding_number_homotopic_paths_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and qp: "pathstart q = pathstart p" "pathfinish q = pathfinish p"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "winding_number (p +++ reversepath q) \<zeta> = 0"
    using assms by (simp add: winding_number_join winding_number_reversepath)
  moreover
  have "path (p +++ reversepath q)" "\<zeta> \<notin> path_image (p +++ reversepath q)"
    using assms by (auto simp: not_in_path_image_join)
  ultimately obtain a where "homotopic_paths (- {\<zeta>}) (p +++ reversepath q) (linepath a a)"
    using winding_number_homotopic_paths_null_explicit_eq by blast
  then show ?rhs
    using homotopic_paths_imp_pathstart assms
    by (fastforce simp add: dest: homotopic_paths_imp_homotopic_loops homotopic_paths_loop_parts)
next
  assume ?rhs
  then show ?lhs
    by (simp add: winding_number_homotopic_paths)
qed

lemma winding_number_homotopic_loops_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and loops: "pathfinish p = pathstart p" "pathfinish q = pathstart q"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_loops (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "pathstart p \<noteq> \<zeta>" "pathstart q \<noteq> \<zeta>"
    using \<zeta>p \<zeta>q by blast+
  moreover have "path_connected (-{\<zeta>})"
    by (simp add: path_connected_punctured_universe)
  ultimately obtain r where "path r" and rim: "path_image r \<subseteq> -{\<zeta>}"
                        and pas: "pathstart r = pathstart p" and paf: "pathfinish r = pathstart q"
    by (auto simp: path_connected_def)
  then have "pathstart r \<noteq> \<zeta>" by blast
  have "homotopic_loops (- {\<zeta>}) p (r +++ q +++ reversepath r)"
  proof (rule homotopic_paths_imp_homotopic_loops)
    show "homotopic_paths (- {\<zeta>}) p (r +++ q +++ reversepath r)"
      by (metis (mono_tags, hide_lams) \<open>path r\<close> L \<zeta>p \<zeta>q \<open>path p\<close> \<open>path q\<close> homotopic_loops_conjugate loops not_in_path_image_join paf pas path_image_reversepath path_imp_reversepath path_join_eq pathfinish_join pathfinish_reversepath  pathstart_join pathstart_reversepath rim subset_Compl_singleton winding_number_homotopic_loops winding_number_homotopic_paths_eq)
  qed (use loops pas in auto)
  moreover have "homotopic_loops (- {\<zeta>}) (r +++ q +++ reversepath r) q"
    using rim \<zeta>q by (auto simp: homotopic_loops_conjugate paf \<open>path q\<close> \<open>path r\<close> loops)
  ultimately show ?rhs
    using homotopic_loops_trans by metis
next
  assume ?rhs
  then show ?lhs
    by (simp add: winding_number_homotopic_loops)
qed

end


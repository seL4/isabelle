section \<open>Complex Path Integrals and Cauchy's Integral Theorem\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Cauchy_Integral_Theorem
imports
  "HOL-Analysis.Analysis"
  Contour_Integration
begin

lemma leibniz_rule_holomorphic:
  fixes f::"complex \<Rightarrow> 'b::euclidean_space \<Rightarrow> complex"
  assumes "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes "convex U"
  shows "(\<lambda>x. integral (cbox a b) (f x)) holomorphic_on U"
  using leibniz_rule_field_differentiable[OF assms(1-3) _ assms(4)]
  by (auto simp: holomorphic_on_def)

lemma Ln_measurable [measurable]: "Ln \<in> measurable borel borel"
proof -
  have *: "Ln (-of_real x) = of_real (ln x) + \<i> * pi" if "x > 0" for x
    using that by (subst Ln_minus) (auto simp: Ln_of_real)
  have **: "Ln (of_real x) = of_real (ln (-x)) + \<i> * pi" if "x < 0" for x
    using *[of "-x"] that by simp
  have cont: "(\<lambda>x. indicat_real (- \<real>\<^sub>\<le>\<^sub>0) x *\<^sub>R Ln x) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_on_indicator continuous_intros) auto
  have "(\<lambda>x. if x \<in> \<real>\<^sub>\<le>\<^sub>0 then ln (-Re x) + \<i> * pi else indicator (-\<real>\<^sub>\<le>\<^sub>0) x *\<^sub>R Ln x) \<in> borel \<rightarrow>\<^sub>M borel"
    (is "?f \<in> _") by (rule measurable_If_set[OF _ cont]) auto
  hence "(\<lambda>x. if x = 0 then Ln 0 else ?f x) \<in> borel \<rightarrow>\<^sub>M borel" by measurable
  also have "(\<lambda>x. if x = 0 then Ln 0 else ?f x) = Ln"
    by (auto simp: fun_eq_iff ** nonpos_Reals_def)
  finally show ?thesis .
qed

lemma powr_complex_measurable [measurable]:
  assumes [measurable]: "f \<in> measurable M borel" "g \<in> measurable M borel"
  shows   "(\<lambda>x. f x powr g x :: complex) \<in> measurable M borel"
  using assms by (simp add: powr_def) 

text\<open>The special case of midpoints used in the main quadrisection\<close>

lemma has_contour_integral_midpoint:
  assumes "(f has_contour_integral i) (linepath a (midpoint a b))"
          "(f has_contour_integral j) (linepath (midpoint a b) b)"
    shows "(f has_contour_integral (i + j)) (linepath a b)"
  apply (rule has_contour_integral_split [where c = "midpoint a b" and k = "1/2"])
  using assms
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done

lemma contour_integral_midpoint:
   "continuous_on (closed_segment a b) f
    \<Longrightarrow> contour_integral (linepath a b) f =
        contour_integral (linepath a (midpoint a b)) f + contour_integral (linepath (midpoint a b) b) f"
  apply (rule contour_integral_split [where c = "midpoint a b" and k = "1/2"])
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done

text\<open>A couple of special case lemmas that are useful below\<close>

lemma triangle_linear_has_chain_integral:
    "((\<lambda>x. m*x + d) has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
  apply (rule Cauchy_theorem_primitive [of UNIV "\<lambda>x. m/2 * x^2 + d*x"])
  apply (auto intro!: derivative_eq_intros)
  done

lemma has_chain_integral_chain_integral3:
     "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d)
      \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f = i"
  apply (subst contour_integral_unique [symmetric], assumption)
  apply (drule has_contour_integral_integrable)
  apply (simp add: valid_path_join)
  done

lemma has_chain_integral_chain_integral4:
     "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d +++ linepath d e)
      \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f + contour_integral (linepath d e) f = i"
  apply (subst contour_integral_unique [symmetric], assumption)
  apply (drule has_contour_integral_integrable)
  apply (simp add: valid_path_join)
  done

subsection\<^marker>\<open>tag unimportant\<close> \<open>The key quadrisection step\<close>

lemma norm_sum_half:
  assumes "norm(a + b) \<ge> e"
    shows "norm a \<ge> e/2 \<or> norm b \<ge> e/2"
proof -
  have "e \<le> norm (- a - b)"
    by (simp add: add.commute assms norm_minus_commute)
  thus ?thesis
    using norm_triangle_ineq4 order_trans by fastforce
qed

lemma norm_sum_lemma:
  assumes "e \<le> norm (a + b + c + d)"
    shows "e / 4 \<le> norm a \<or> e / 4 \<le> norm b \<or> e / 4 \<le> norm c \<or> e / 4 \<le> norm d"
proof -
  have "e \<le> norm ((a + b) + (c + d))" using assms
    by (simp add: algebra_simps)
  then show ?thesis
    by (auto dest!: norm_sum_half)
qed

lemma Cauchy_theorem_quadrisection:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and dist: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      and e: "e * K^2 \<le>
              norm (contour_integral(linepath a b) f + contour_integral(linepath b c) f + contour_integral(linepath c a) f)"
  shows "\<exists>a' b' c'.
           a' \<in> convex hull {a,b,c} \<and> b' \<in> convex hull {a,b,c} \<and> c' \<in> convex hull {a,b,c} \<and>
           dist a' b' \<le> K/2  \<and>  dist b' c' \<le> K/2  \<and>  dist c' a' \<le> K/2  \<and>
           e * (K/2)^2 \<le> norm(contour_integral(linepath a' b') f + contour_integral(linepath b' c') f + contour_integral(linepath c' a') f)"
         (is "\<exists>x y z. ?\<Phi> x y z")
proof -
  note divide_le_eq_numeral1 [simp del]
  define a' where "a' = midpoint b c"
  define b' where "b' = midpoint c a"
  define c' where "c' = midpoint a b"
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  have fcont': "continuous_on (closed_segment c' b') f"
               "continuous_on (closed_segment a' c') f"
               "continuous_on (closed_segment b' a') f"
    unfolding a'_def b'_def c'_def
    by (rule continuous_on_subset [OF f],
           metis midpoints_in_convex_hull convex_hull_subset hull_subset insert_subset segment_convex_hull)+
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  have *: "?pathint a b + ?pathint b c + ?pathint c a =
          (?pathint a c' + ?pathint c' b' + ?pathint b' a) +
          (?pathint a' c' + ?pathint c' b + ?pathint b a') +
          (?pathint a' c + ?pathint c b' + ?pathint b' a') +
          (?pathint a' b' + ?pathint b' c' + ?pathint c' a')"
    by (simp add: fcont' contour_integral_reverse_linepath) (simp add: a'_def b'_def c'_def contour_integral_midpoint fabc)
  have [simp]: "\<And>x y. cmod (x * 2 - y * 2) = cmod (x - y) * 2"
    by (metis left_diff_distrib mult.commute norm_mult_numeral1)
  have [simp]: "\<And>x y. cmod (x - y) = cmod (y - x)"
    by (simp add: norm_minus_commute)
  consider "e * K\<^sup>2 / 4 \<le> cmod (?pathint a c' + ?pathint c' b' + ?pathint b' a)" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' c' + ?pathint c' b + ?pathint b a')" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' c + ?pathint c b' + ?pathint b' a')" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' b' + ?pathint b' c' + ?pathint c' a')"
    using assms unfolding * by (blast intro: that dest!: norm_sum_lemma)
  then show ?thesis
  proof cases
    case 1 then have "?\<Phi> a c' b'"
      using assms
      apply (clarsimp simp: c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real field_split_simps)
      done
    then show ?thesis by blast
  next
    case 2 then  have "?\<Phi> a' c' b"
      using assms
      apply (clarsimp simp: a'_def c'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real field_split_simps)
      done
    then show ?thesis by blast
  next
    case 3 then have "?\<Phi> a' c b'"
      using assms
      apply (clarsimp simp: a'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real field_split_simps)
      done
    then show ?thesis by blast
  next
    case 4 then have "?\<Phi> a' b' c'"
      using assms
      apply (clarsimp simp: a'_def c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real field_split_simps)
      done
    then show ?thesis by blast
  qed
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Cauchy's theorem for triangles\<close>

lemma triangle_points_closer:
  fixes a::complex
  shows "\<lbrakk>x \<in> convex hull {a,b,c};  y \<in> convex hull {a,b,c}\<rbrakk>
         \<Longrightarrow> norm(x - y) \<le> norm(a - b) \<or>
             norm(x - y) \<le> norm(b - c) \<or>
             norm(x - y) \<le> norm(c - a)"
  using simplex_extremal_le [of "{a,b,c}"]
  by (auto simp: norm_minus_commute)

lemma holomorphic_point_small_triangle:
  assumes x: "x \<in> S"
      and f: "continuous_on S f"
      and cd: "f field_differentiable (at x within S)"
      and e: "0 < e"
    shows "\<exists>k>0. \<forall>a b c. dist a b \<le> k \<and> dist b c \<le> k \<and> dist c a \<le> k \<and>
              x \<in> convex hull {a,b,c} \<and> convex hull {a,b,c} \<subseteq> S
              \<longrightarrow> norm(contour_integral(linepath a b) f + contour_integral(linepath b c) f +
                       contour_integral(linepath c a) f)
                  \<le> e*(dist a b + dist b c + dist c a)^2"
           (is "\<exists>k>0. \<forall>a b c. _ \<longrightarrow> ?normle a b c")
proof -
  have le_of_3: "\<And>a x y z. \<lbrakk>0 \<le> x*y; 0 \<le> x*z; 0 \<le> y*z; a \<le> (e*(x + y + z))*x + (e*(x + y + z))*y + (e*(x + y + z))*z\<rbrakk>
                     \<Longrightarrow> a \<le> e*(x + y + z)^2"
    by (simp add: algebra_simps power2_eq_square)
  have disj_le: "\<lbrakk>x \<le> a \<or> x \<le> b \<or> x \<le> c; 0 \<le> a; 0 \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> x \<le> a + b + c"
             for x::real and a b c
    by linarith
  have fabc: "f contour_integrable_on linepath a b" "f contour_integrable_on linepath b c" "f contour_integrable_on linepath c a"
              if "convex hull {a, b, c} \<subseteq> S" for a b c
    using segments_subset_convex_hull that
    by (metis continuous_on_subset f contour_integrable_continuous_linepath)+
  note path_bound = has_contour_integral_bound_linepath [simplified norm_minus_commute, OF has_contour_integral_integral]
  { fix f' a b c d
    assume d: "0 < d"
       and f': "\<And>y. \<lbrakk>cmod (y - x) \<le> d; y \<in> S\<rbrakk> \<Longrightarrow> cmod (f y - f x - f' * (y - x)) \<le> e * cmod (y - x)"
       and le: "cmod (a - b) \<le> d" "cmod (b - c) \<le> d" "cmod (c - a) \<le> d"
       and xc: "x \<in> convex hull {a, b, c}"
       and S: "convex hull {a, b, c} \<subseteq> S"
    have pa: "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f =
              contour_integral (linepath a b) (\<lambda>y. f y - f x - f'*(y - x)) +
              contour_integral (linepath b c) (\<lambda>y. f y - f x - f'*(y - x)) +
              contour_integral (linepath c a) (\<lambda>y. f y - f x - f'*(y - x))"
      apply (simp add: contour_integral_diff contour_integral_lmul contour_integrable_lmul contour_integrable_diff fabc [OF S])
      apply (simp add: field_simps)
      done
    { fix y
      assume yc: "y \<in> convex hull {a,b,c}"
      have "cmod (f y - f x - f' * (y - x)) \<le> e*norm(y - x)"
      proof (rule f')
        show "cmod (y - x) \<le> d"
          by (metis triangle_points_closer [OF xc yc] le norm_minus_commute order_trans)
      qed (use S yc in blast)
      also have "\<dots> \<le> e * (cmod (a - b) + cmod (b - c) + cmod (c - a))"
        by (simp add: yc e xc disj_le [OF triangle_points_closer])
      finally have "cmod (f y - f x - f' * (y - x)) \<le> e * (cmod (a - b) + cmod (b - c) + cmod (c - a))" .
    } note cm_le = this
    have "?normle a b c"
      unfolding dist_norm pa
      apply (rule le_of_3)
      using f' xc S e
      apply simp_all
      apply (intro norm_triangle_le add_mono path_bound)
      apply (simp_all add: contour_integral_diff contour_integral_lmul contour_integrable_lmul contour_integrable_diff fabc)
      apply (blast intro: cm_le elim: dest: segments_subset_convex_hull [THEN subsetD])+
      done
  } note * = this
  show ?thesis
    using cd e
    apply (simp add: field_differentiable_def has_field_derivative_def has_derivative_within_alt approachable_lt_le2 Ball_def)
    apply (clarify dest!: spec mp)
    using * unfolding dist_norm
    apply blast
    done
qed


text\<open>Hence the most basic theorem for a triangle.\<close>

locale Chain =
  fixes x0 At Follows
  assumes At0: "At x0 0"
      and AtSuc: "\<And>x n. At x n \<Longrightarrow> \<exists>x'. At x' (Suc n) \<and> Follows x' x"
begin
  primrec f where
    "f 0 = x0"
  | "f (Suc n) = (SOME x. At x (Suc n) \<and> Follows x (f n))"

  lemma At: "At (f n) n"
  proof (induct n)
    case 0 show ?case
      by (simp add: At0)
  next
    case (Suc n) show ?case
      by (metis (no_types, lifting) AtSuc [OF Suc] f.simps(2) someI_ex)
  qed

  lemma Follows: "Follows (f(Suc n)) (f n)"
    by (metis (no_types, lifting) AtSuc [OF At [of n]] f.simps(2) someI_ex)

  declare f.simps(2) [simp del]
end

lemma Chain3:
  assumes At0: "At x0 y0 z0 0"
      and AtSuc: "\<And>x y z n. At x y z n \<Longrightarrow> \<exists>x' y' z'. At x' y' z' (Suc n) \<and> Follows x' y' z' x y z"
  obtains f g h where
    "f 0 = x0" "g 0 = y0" "h 0 = z0"
                      "\<And>n. At (f n) (g n) (h n) n"
                       "\<And>n. Follows (f(Suc n)) (g(Suc n)) (h(Suc n)) (f n) (g n) (h n)"
proof -
  interpret three: Chain "(x0,y0,z0)" "\<lambda>(x,y,z). At x y z" "\<lambda>(x',y',z'). \<lambda>(x,y,z). Follows x' y' z' x y z"
    apply unfold_locales
    using At0 AtSuc by auto
  show ?thesis
  apply (rule that [of "\<lambda>n. fst (three.f n)"  "\<lambda>n. fst (snd (three.f n))" "\<lambda>n. snd (snd (three.f n))"])
  using three.At three.Follows
  apply simp_all
  apply (simp_all add: split_beta')
  done
qed

proposition\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_triangle:
  assumes "f holomorphic_on (convex hull {a,b,c})"
    shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
proof -
  have contf: "continuous_on (convex hull {a,b,c}) f"
    by (metis assms holomorphic_on_imp_continuous_on)
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix y::complex
    assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
       and ynz: "y \<noteq> 0"
    define K where "K = 1 + max (dist a b) (max (dist b c) (dist c a))"
    define e where "e = norm y / K^2"
    have K1: "K \<ge> 1"  by (simp add: K_def max.coboundedI1)
    then have K: "K > 0" by linarith
    have [iff]: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      by (simp_all add: K_def)
    have e: "e > 0"
      unfolding e_def using ynz K1 by simp
    define At where "At x y z n \<longleftrightarrow>
        convex hull {x,y,z} \<subseteq> convex hull {a,b,c} \<and>
        dist x y \<le> K/2^n \<and> dist y z \<le> K/2^n \<and> dist z x \<le> K/2^n \<and>
        norm(?pathint x y + ?pathint y z + ?pathint z x) \<ge> e*(K/2^n)^2"
      for x y z n
    have At0: "At a b c 0"
      using fy
      by (simp add: At_def e_def has_chain_integral_chain_integral3)
    { fix x y z n
      assume At: "At x y z n"
      then have contf': "continuous_on (convex hull {x,y,z}) f"
        using contf At_def continuous_on_subset by metis
      have "\<exists>x' y' z'. At x' y' z' (Suc n) \<and> convex hull {x',y',z'} \<subseteq> convex hull {x,y,z}"
        using At Cauchy_theorem_quadrisection [OF contf', of "K/2^n" e]
        apply (simp add: At_def algebra_simps)
        apply (meson convex_hull_subset empty_subsetI insert_subset subsetCE)
        done
    } note AtSuc = this
    obtain fa fb fc
      where f0 [simp]: "fa 0 = a" "fb 0 = b" "fc 0 = c"
        and cosb: "\<And>n. convex hull {fa n, fb n, fc n} \<subseteq> convex hull {a,b,c}"
        and dist: "\<And>n. dist (fa n) (fb n) \<le> K/2^n"
                  "\<And>n. dist (fb n) (fc n) \<le> K/2^n"
                  "\<And>n. dist (fc n) (fa n) \<le> K/2^n"
        and no: "\<And>n. norm(?pathint (fa n) (fb n) +
                           ?pathint (fb n) (fc n) +
                           ?pathint (fc n) (fa n)) \<ge> e * (K/2^n)^2"
        and conv_le: "\<And>n. convex hull {fa(Suc n), fb(Suc n), fc(Suc n)} \<subseteq> convex hull {fa n, fb n, fc n}"
      apply (rule Chain3 [of At, OF At0 AtSuc])
      apply (auto simp: At_def)
      done
    obtain x where x: "\<And>n. x \<in> convex hull {fa n, fb n, fc n}"
    proof (rule bounded_closed_nest)
      show "\<And>n. closed (convex hull {fa n, fb n, fc n})"
        by (simp add: compact_imp_closed finite_imp_compact_convex_hull)
      show "\<And>m n. m \<le> n \<Longrightarrow> convex hull {fa n, fb n, fc n} \<subseteq> convex hull {fa m, fb m, fc m}"
        by (erule transitive_stepwise_le) (auto simp: conv_le)
    qed (fastforce intro: finite_imp_bounded_convex_hull)+
    then have xin: "x \<in> convex hull {a,b,c}"
      using assms f0 by blast
    then have fx: "f field_differentiable at x within (convex hull {a,b,c})"
      using assms holomorphic_on_def by blast
    { fix k n
      assume k: "0 < k"
         and le:
            "\<And>x' y' z'.
               \<lbrakk>dist x' y' \<le> k; dist y' z' \<le> k; dist z' x' \<le> k;
                x \<in> convex hull {x',y',z'};
                convex hull {x',y',z'} \<subseteq> convex hull {a,b,c}\<rbrakk>
               \<Longrightarrow>
               cmod (?pathint x' y' + ?pathint y' z' + ?pathint z' x') * 10
                     \<le> e * (dist x' y' + dist y' z' + dist z' x')\<^sup>2"
         and Kk: "K / k < 2 ^ n"
      have "K / 2 ^ n < k" using Kk k
        by (auto simp: field_simps)
      then have DD: "dist (fa n) (fb n) \<le> k" "dist (fb n) (fc n) \<le> k" "dist (fc n) (fa n) \<le> k"
        using dist [of n]  k
        by linarith+
      have dle: "(dist (fa n) (fb n) + dist (fb n) (fc n) + dist (fc n) (fa n))\<^sup>2
               \<le> (3 * K / 2 ^ n)\<^sup>2"
        using dist [of n] e K
        by (simp add: abs_le_square_iff [symmetric])
      have less10: "\<And>x y::real. 0 < x \<Longrightarrow> y \<le> 9*x \<Longrightarrow> y < x*10"
        by linarith
      have "e * (dist (fa n) (fb n) + dist (fb n) (fc n) + dist (fc n) (fa n))\<^sup>2 \<le> e * (3 * K / 2 ^ n)\<^sup>2"
        using ynz dle e mult_le_cancel_left_pos by blast
      also have "\<dots> <
          cmod (?pathint (fa n) (fb n) + ?pathint (fb n) (fc n) + ?pathint (fc n) (fa n)) * 10"
        using no [of n] e K
        apply (simp add: e_def field_simps)
        apply (simp only: zero_less_norm_iff [symmetric])
        done
      finally have False
        using le [OF DD x cosb] by auto
    } then
    have ?thesis
      using holomorphic_point_small_triangle [OF xin contf fx, of "e/10"] e
      apply clarsimp
      apply (rule_tac y1="K/k" in exE [OF real_arch_pow[of 2]], force+)
      done
  }
  moreover have "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    by simp (meson contf continuous_on_subset contour_integrable_continuous_linepath segments_subset_convex_hull(1)
                   segments_subset_convex_hull(3) segments_subset_convex_hull(5))
  ultimately show ?thesis
    using has_contour_integral_integral by fastforce
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Version needing function holomorphic in interior only\<close>

lemma Cauchy_theorem_flat_lemma:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
      and k: "0 \<le> k"
    shows "contour_integral (linepath a b) f + contour_integral (linepath b c) f +
          contour_integral (linepath c a) f = 0"
proof -
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  show ?thesis
  proof (cases "k \<le> 1")
    case True show ?thesis
      by (simp add: contour_integral_split [OF fabc(1) k True c] contour_integral_reverse_linepath fabc)
  next
    case False then show ?thesis
      using fabc c
      apply (subst contour_integral_split [of a c f "1/k" b, symmetric])
      apply (metis closed_segment_commute fabc(3))
      apply (auto simp: k contour_integral_reverse_linepath)
      done
  qed
qed

lemma Cauchy_theorem_flat:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "0 \<le> k")
  case True with assms show ?thesis
    by (blast intro: Cauchy_theorem_flat_lemma)
next
  case False
  have "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  moreover have "contour_integral (linepath b a) f + contour_integral (linepath a c) f +
        contour_integral (linepath c b) f = 0"
    apply (rule Cauchy_theorem_flat_lemma [of b a c f "1-k"])
    using False c
    apply (auto simp: f insert_commute scaleR_conv_of_real algebra_simps)
    done
  ultimately show ?thesis
    apply (auto simp: contour_integral_reverse_linepath)
    using add_eq_0_iff by force
qed

lemma Cauchy_theorem_triangle_interior:
  assumes contf: "continuous_on (convex hull {a,b,c}) f"
      and holf:  "f holomorphic_on interior (convex hull {a,b,c})"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
proof -
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using contf continuous_on_subset segments_subset_convex_hull by metis+
  have "bounded (f ` (convex hull {a,b,c}))"
    by (simp add: compact_continuous_image compact_convex_hull compact_imp_bounded contf)
  then obtain B where "0 < B" and Bnf: "\<And>x. x \<in> convex hull {a,b,c} \<Longrightarrow> norm (f x) \<le> B"
     by (auto simp: dest!: bounded_pos [THEN iffD1])
  have "bounded (convex hull {a,b,c})"
    by (simp add: bounded_convex_hull)
  then obtain C where C: "0 < C" and Cno: "\<And>y. y \<in> convex hull {a,b,c} \<Longrightarrow> norm y < C"
    using bounded_pos_less by blast
  then have diff_2C: "norm(x - y) \<le> 2*C"
           if x: "x \<in> convex hull {a, b, c}" and y: "y \<in> convex hull {a, b, c}" for x y
  proof -
    have "cmod x \<le> C"
      using x by (meson Cno not_le not_less_iff_gr_or_eq)
    hence "cmod (x - y) \<le> C + C"
      using y by (meson Cno add_mono_thms_linordered_field(4) less_eq_real_def norm_triangle_ineq4 order_trans)
    thus "cmod (x - y) \<le> 2 * C"
      by (metis mult_2)
  qed
  have contf': "continuous_on (convex hull {b,a,c}) f"
    using contf by (simp add: insert_commute)
  { fix y::complex
    assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
       and ynz: "y \<noteq> 0"
    have pi_eq_y: "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f = y"
      by (rule has_chain_integral_chain_integral3 [OF fy])
    have ?thesis
    proof (cases "c=a \<or> a=b \<or> b=c")
      case True then show ?thesis
        using Cauchy_theorem_flat [OF contf, of 0]
        using has_chain_integral_chain_integral3 [OF fy] ynz
        by (force simp: fabc contour_integral_reverse_linepath)
    next
      case False
      then have car3: "card {a, b, c} = Suc (DIM(complex))"
        by auto
      { assume "interior(convex hull {a,b,c}) = {}"
        then have "collinear{a,b,c}"
          using interior_convex_hull_eq_empty [OF car3]
          by (simp add: collinear_3_eq_affine_dependent)
        with False obtain d where "c \<noteq> a" "a \<noteq> b" "b \<noteq> c" "c - b = d *\<^sub>R (a - b)"
          by (auto simp: collinear_3 collinear_lemma)
        then have "False"
          using False Cauchy_theorem_flat [OF contf'] pi_eq_y ynz
          by (simp add: fabc add_eq_0_iff contour_integral_reverse_linepath)
      }
      then obtain d where d: "d \<in> interior (convex hull {a, b, c})"
        by blast
      { fix d1
        assume d1_pos: "0 < d1"
           and d1: "\<And>x x'. \<lbrakk>x\<in>convex hull {a, b, c}; x'\<in>convex hull {a, b, c}; cmod (x' - x) < d1\<rbrakk>
                           \<Longrightarrow> cmod (f x' - f x) < cmod y / (24 * C)"
        define e where "e = min 1 (min (d1/(4*C)) ((norm y / 24 / C) / B))"
        define shrink where "shrink x = x - e *\<^sub>R (x - d)" for x
        let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
        have e: "0 < e" "e \<le> 1" "e \<le> d1 / (4 * C)" "e \<le> cmod y / 24 / C / B"
          using d1_pos \<open>C>0\<close> \<open>B>0\<close> ynz by (simp_all add: e_def)
        then have eCB: "24 * e * C * B \<le> cmod y"
          using \<open>C>0\<close> \<open>B>0\<close>  by (simp add: field_simps)
        have e_le_d1: "e * (4 * C) \<le> d1"
          using e \<open>C>0\<close> by (simp add: field_simps)
        have "shrink a \<in> interior(convex hull {a,b,c})"
             "shrink b \<in> interior(convex hull {a,b,c})"
             "shrink c \<in> interior(convex hull {a,b,c})"
          using d e by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
        then have fhp0: "(f has_contour_integral 0)
                (linepath (shrink a) (shrink b) +++ linepath (shrink b) (shrink c) +++ linepath (shrink c) (shrink a))"
          by (simp add: Cauchy_theorem_triangle holomorphic_on_subset [OF holf] hull_minimal)
        then have f_0_shrink: "?pathint (shrink a) (shrink b) + ?pathint (shrink b) (shrink c) + ?pathint (shrink c) (shrink a) = 0"
          by (simp add: has_chain_integral_chain_integral3)
        have fpi_abc: "f contour_integrable_on linepath (shrink a) (shrink b)"
                      "f contour_integrable_on linepath (shrink b) (shrink c)"
                      "f contour_integrable_on linepath (shrink c) (shrink a)"
          using fhp0  by (auto simp: valid_path_join dest: has_contour_integral_integrable)
        have cmod_shr: "\<And>x y. cmod (shrink y - shrink x - (y - x)) = e * cmod (x - y)"
          using e by (simp add: shrink_def real_vector.scale_right_diff_distrib [symmetric])
        have sh_eq: "\<And>a b d::complex. (b - e *\<^sub>R (b - d)) - (a - e *\<^sub>R (a - d)) - (b - a) = e *\<^sub>R (a - b)"
          by (simp add: algebra_simps)
        have "cmod y / (24 * C) \<le> cmod y / cmod (b - a) / 12"
          using False \<open>C>0\<close> diff_2C [of b a] ynz
          by (auto simp: field_split_simps hull_inc)
        have less_C: "\<lbrakk>u \<in> convex hull {a, b, c}; 0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> x * cmod u < C" for x u
          apply (cases "x=0", simp add: \<open>0<C\<close>)
          using Cno [of u] mult_left_le_one_le [of "cmod u" x] le_less_trans norm_ge_zero by blast
        { fix u v
          assume uv: "u \<in> convex hull {a, b, c}" "v \<in> convex hull {a, b, c}" "u\<noteq>v"
             and fpi_uv: "f contour_integrable_on linepath (shrink u) (shrink v)"
          have shr_uv: "shrink u \<in> interior(convex hull {a,b,c})"
                       "shrink v \<in> interior(convex hull {a,b,c})"
            using d e uv
            by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
          have cmod_fuv: "\<And>x. 0\<le>x \<Longrightarrow> x\<le>1 \<Longrightarrow> cmod (f (linepath (shrink u) (shrink v) x)) \<le> B"
            using shr_uv by (blast intro: Bnf linepath_in_convex_hull interior_subset [THEN subsetD])
          have By_uv: "B * (12 * (e * cmod (u - v))) \<le> cmod y"
            apply (rule order_trans [OF _ eCB])
            using e \<open>B>0\<close> diff_2C [of u v] uv
            by (auto simp: field_simps)
          { fix x::real   assume x: "0\<le>x" "x\<le>1"
            have cmod_less_4C: "cmod ((1 - x) *\<^sub>R u - (1 - x) *\<^sub>R d) + cmod (x *\<^sub>R v - x *\<^sub>R d) < (C+C) + (C+C)"
              apply (rule add_strict_mono; rule norm_triangle_half_l [of _ 0])
              using uv x d interior_subset
              apply (auto simp: hull_inc intro!: less_C)
              done
            have ll: "linepath (shrink u) (shrink v) x - linepath u v x = -e * ((1 - x) *\<^sub>R (u - d) + x *\<^sub>R (v - d))"
              by (simp add: linepath_def shrink_def algebra_simps scaleR_conv_of_real)
            have cmod_less_dt: "cmod (linepath (shrink u) (shrink v) x - linepath u v x) < d1"
              apply (simp only: ll norm_mult scaleR_diff_right)
              using \<open>e>0\<close> cmod_less_4C apply (force intro: norm_triangle_lt less_le_trans [OF _ e_le_d1])
              done
            have "cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) < cmod y / (24 * C)"
              using x uv shr_uv cmod_less_dt
              by (auto simp: hull_inc intro: d1 interior_subset [THEN subsetD] linepath_in_convex_hull)
            also have "\<dots> \<le> cmod y / cmod (v - u) / 12"
              using False uv \<open>C>0\<close> diff_2C [of v u] ynz
              by (auto simp: field_split_simps hull_inc)
            finally have "cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) \<le> cmod y / cmod (v - u) / 12"
              by simp
            then have cmod_12_le: "cmod (v - u) * cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) * 12 \<le> cmod y"
              using uv False by (auto simp: field_simps)
            have "cmod (f (linepath (shrink u) (shrink v) x)) * cmod (shrink v - shrink u - (v - u)) +
                          cmod (v - u) * cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x))
                          \<le> B * (cmod y / 24 / C / B * 2 * C) + 2 * C * (cmod y / 24 / C)"
              apply (rule add_mono [OF mult_mono])
              using By_uv e \<open>0 < B\<close> \<open>0 < C\<close> x apply (simp_all add: cmod_fuv cmod_shr cmod_12_le)
              apply (simp add: field_simps)
              done
            also have "\<dots> \<le> cmod y / 6"
              by simp
            finally have "cmod (f (linepath (shrink u) (shrink v) x)) * cmod (shrink v - shrink u - (v - u)) +
                          cmod (v - u) * cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x))
                          \<le> cmod y / 6" .
          } note cmod_diff_le = this
          have f_uv: "continuous_on (closed_segment u v) f"
            by (blast intro: uv continuous_on_subset [OF contf closed_segment_subset_convex_hull])
          have **: "\<And>f' x' f x::complex. f'*x' - f*x = f'*(x' - x) + x*(f' - f)"
            by (simp add: algebra_simps)
          have "norm (?pathint (shrink u) (shrink v) - ?pathint u v)
                \<le> (B*(norm y /24/C/B)*2*C + (2*C)*(norm y/24/C)) * content (cbox 0 (1::real))"
            apply (rule has_integral_bound
                    [of _ "\<lambda>x. f(linepath (shrink u) (shrink v) x) * (shrink v - shrink u) - f(linepath u v x)*(v - u)"
                        _ 0 1])
            using ynz \<open>0 < B\<close> \<open>0 < C\<close>
              apply (simp_all del: le_divide_eq_numeral1)
            apply (simp add: has_integral_diff has_contour_integral_linepath [symmetric] has_contour_integral_integral
                fpi_uv f_uv contour_integrable_continuous_linepath)
            apply (auto simp: ** norm_triangle_le norm_mult cmod_diff_le simp del: le_divide_eq_numeral1)
            done
          also have "\<dots> \<le> norm y / 6"
            by simp
          finally have "norm (?pathint (shrink u) (shrink v) - ?pathint u v) \<le> norm y / 6" .
          } note * = this
          have "norm (?pathint (shrink a) (shrink b) - ?pathint a b) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          moreover
          have "norm (?pathint (shrink b) (shrink c) - ?pathint b c) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          moreover
          have "norm (?pathint (shrink c) (shrink a) - ?pathint c a) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          ultimately
          have "norm((?pathint (shrink a) (shrink b) - ?pathint a b) +
                     (?pathint (shrink b) (shrink c) - ?pathint b c) + (?pathint (shrink c) (shrink a) - ?pathint c a))
                \<le> norm y / 6 + norm y / 6 + norm y / 6"
            by (metis norm_triangle_le add_mono)
          also have "\<dots> = norm y / 2"
            by simp
          finally have "norm((?pathint (shrink a) (shrink b) + ?pathint (shrink b) (shrink c) + ?pathint (shrink c) (shrink a)) -
                          (?pathint a b + ?pathint b c + ?pathint c a))
                \<le> norm y / 2"
            by (simp add: algebra_simps)
          then
          have "norm(?pathint a b + ?pathint b c + ?pathint c a) \<le> norm y / 2"
            by (simp add: f_0_shrink) (metis (mono_tags) add.commute minus_add_distrib norm_minus_cancel uminus_add_conv_diff)
          then have "False"
            using pi_eq_y ynz by auto
        }
        note * = this
        have "uniformly_continuous_on (convex hull {a,b,c}) f"
          by (simp add: contf compact_convex_hull compact_uniformly_continuous)
        moreover have "norm y / (24 * C) > 0"
          using ynz \<open>C > 0\<close> by auto
        ultimately obtain \<delta> where "\<delta> > 0" and
          "\<forall>x\<in>convex hull {a, b, c}. \<forall>x'\<in>convex hull {a, b, c}.
             dist x' x < \<delta> \<longrightarrow> dist (f x') (f x) < cmod y / (24 * C)"
          using \<open>C > 0\<close> ynz unfolding uniformly_continuous_on_def dist_norm by blast
        hence False using *[of \<delta>] by (auto simp: dist_norm)
        then show ?thesis ..
      qed
  }
  moreover have "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    using fabc contour_integrable_continuous_linepath by auto
  ultimately show ?thesis
    using has_contour_integral_integral by fastforce
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Version allowing finite number of exceptional points\<close>

proposition\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_triangle_cofinite:
  assumes "continuous_on (convex hull {a,b,c}) f"
      and "finite S"
      and "(\<And>x. x \<in> interior(convex hull {a,b,c}) - S \<Longrightarrow> f field_differentiable (at x))"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
using assms
proof (induction "card S" arbitrary: a b c S rule: less_induct)
  case (less S a b c)
  show ?case
  proof (cases "S={}")
    case True with less show ?thesis
      by (fastforce simp: holomorphic_on_def field_differentiable_at_within Cauchy_theorem_triangle_interior)
  next
    case False
    then obtain d S' where d: "S = insert d S'" "d \<notin> S'"
      by (meson Set.set_insert all_not_in_conv)
    then show ?thesis
    proof (cases "d \<in> convex hull {a,b,c}")
      case False
      show "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
      proof (rule less.hyps)
        show "\<And>x. x \<in> interior (convex hull {a, b, c}) - S' \<Longrightarrow> f field_differentiable at x"
        using False d interior_subset by (auto intro!: less.prems)
    qed (use d less.prems in auto)
    next
      case True
      have *: "convex hull {a, b, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have abd: "(f has_contour_integral 0) (linepath a b +++ linepath b d +++ linepath d a)"
      proof (rule less.hyps)
        show "\<And>x. x \<in> interior (convex hull {a, b, d}) - S' \<Longrightarrow> f field_differentiable at x"
          using d not_in_interior_convex_hull_3
          by (clarsimp intro!: less.prems) (metis * insert_absorb insert_subset interior_mono)
      qed (use d continuous_on_subset [OF  _ *] less.prems in auto)
      have *: "convex hull {b, c, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have bcd: "(f has_contour_integral 0) (linepath b c +++ linepath c d +++ linepath d b)"
      proof (rule less.hyps)
        show "\<And>x. x \<in> interior (convex hull {b, c, d}) - S' \<Longrightarrow> f field_differentiable at x"
          using d not_in_interior_convex_hull_3
          by (clarsimp intro!: less.prems) (metis * insert_absorb insert_subset interior_mono)
      qed (use d continuous_on_subset [OF  _ *] less.prems in auto)
      have *: "convex hull {c, a, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have cad: "(f has_contour_integral 0) (linepath c a +++ linepath a d +++ linepath d c)"
      proof (rule less.hyps)
        show "\<And>x. x \<in> interior (convex hull {c, a, d}) - S' \<Longrightarrow> f field_differentiable at x"
          using d not_in_interior_convex_hull_3
          by (clarsimp intro!: less.prems) (metis * insert_absorb insert_subset interior_mono)
      qed (use d continuous_on_subset [OF  _ *] less.prems in auto)
      have "f contour_integrable_on linepath a b"
        using less.prems abd contour_integrable_joinD1 contour_integrable_on_def by blast
      moreover have "f contour_integrable_on linepath b c"
        using less.prems bcd contour_integrable_joinD1 contour_integrable_on_def by blast
      moreover have "f contour_integrable_on linepath c a"
        using less.prems cad contour_integrable_joinD1 contour_integrable_on_def by blast
      ultimately have fpi: "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
        by auto
      { fix y::complex
        assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
           and ynz: "y \<noteq> 0"
        have cont_ad: "continuous_on (closed_segment a d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(3))
        have cont_bd: "continuous_on (closed_segment b d) f"
          by (meson True closed_segment_subset_convex_hull continuous_on_subset hull_subset insert_subset less.prems(1))
        have cont_cd: "continuous_on (closed_segment c d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(2))
        have "contour_integral  (linepath a b) f = - (contour_integral (linepath b d) f + (contour_integral (linepath d a) f))"
             "contour_integral  (linepath b c) f = - (contour_integral (linepath c d) f + (contour_integral (linepath d b) f))"
             "contour_integral  (linepath c a) f = - (contour_integral (linepath a d) f + contour_integral (linepath d c) f)"
            using has_chain_integral_chain_integral3 [OF abd]
                  has_chain_integral_chain_integral3 [OF bcd]
                  has_chain_integral_chain_integral3 [OF cad]
            by (simp_all add: algebra_simps add_eq_0_iff)
        then have ?thesis
          using cont_ad cont_bd cont_cd fy has_chain_integral_chain_integral3 contour_integral_reverse_linepath by fastforce
      }
      then show ?thesis
        using fpi contour_integrable_on_def by blast
    qed
  qed
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Cauchy's theorem for an open starlike set\<close>

lemma starlike_convex_subset:
  assumes S: "a \<in> S" "closed_segment b c \<subseteq> S" and subs: "\<And>x. x \<in> S \<Longrightarrow> closed_segment a x \<subseteq> S"
    shows "convex hull {a,b,c} \<subseteq> S"
      using S
      apply (clarsimp simp add: convex_hull_insert [of "{b,c}" a] segment_convex_hull)
      apply (meson subs convexD convex_closed_segment ends_in_segment(1) ends_in_segment(2) subsetCE)
      done

lemma triangle_contour_integrals_starlike_primitive:
  assumes contf: "continuous_on S f"
      and S: "a \<in> S" "open S"
      and x: "x \<in> S"
      and subs: "\<And>y. y \<in> S \<Longrightarrow> closed_segment a y \<subseteq> S"
      and zer: "\<And>b c. closed_segment b c \<subseteq> S
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x)"
proof -
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix e y
    assume e: "0 < e" and bxe: "ball x e \<subseteq> S" and close: "cmod (y - x) < e"
    have y: "y \<in> S"
      using bxe close  by (force simp: dist_norm norm_minus_commute)
    have cont_ayf: "continuous_on (closed_segment a y) f"
      using contf continuous_on_subset subs y by blast
    have xys: "closed_segment x y \<subseteq> S"
      apply (rule order_trans [OF _ bxe])
      using close
      by (auto simp: dist_norm ball_def norm_minus_commute dest: segment_bound)
    have "?pathint a y - ?pathint a x = ?pathint x y"
      using zer [OF xys]  contour_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
  } note [simp] = this
  { fix e::real
    assume e: "0 < e"
    have cont_atx: "continuous (at x) f"
      using x S contf continuous_on_eq_continuous_at by blast
    then obtain d1 where d1: "d1>0" and d1_less: "\<And>y. cmod (y - x) < d1 \<Longrightarrow> cmod (f y - f x) < e/2"
      unfolding continuous_at Lim_at dist_norm  using e
      by (drule_tac x="e/2" in spec) force
    obtain d2 where d2: "d2>0" "ball x d2 \<subseteq> S" using  \<open>open S\<close> x
      by (auto simp: open_contains_ball)
    have dpos: "min d1 d2 > 0" using d1 d2 by simp
    { fix y
      assume yx: "y \<noteq> x" and close: "cmod (y - x) < min d1 d2"
      have y: "y \<in> S"
        using d2 close  by (force simp: dist_norm norm_minus_commute)
      have "closed_segment x y \<subseteq> S"
        using close d2  by (auto simp: dist_norm norm_minus_commute dest!: segment_bound(1))
      then have fxy: "f contour_integrable_on linepath x y"
        by (metis contour_integrable_continuous_linepath continuous_on_subset [OF contf])
      then obtain i where i: "(f has_contour_integral i) (linepath x y)"
        by (auto simp: contour_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_contour_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_contour_integral_diff [OF _ has_contour_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
      proof (rule has_contour_integral_bound_linepath)
        show "\<And>u. u \<in> closed_segment x y \<Longrightarrow> cmod (f u - f x) \<le> e / 2"
          by (meson close d1_less le_less_trans less_imp_le min.strict_boundedE segment_bound1)
      qed (use e in simp)
      also have "\<dots> < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: contour_integral_unique divide_less_eq)
    }
    then have "\<exists>d>0. \<forall>y. y \<noteq> x \<and> cmod (y-x) < d \<longrightarrow> cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
      using dpos by blast
  }
  then have *: "(\<lambda>y. (?pathint x y - f x * (y - x)) /\<^sub>R cmod (y - x)) \<midarrow>x\<rightarrow> 0"
    by (simp add: Lim_at dist_norm inverse_eq_divide)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_at2 bounded_linear_mult_right)
    apply (rule Lim_transform [OF * tendsto_eventually])
    using \<open>open S\<close> x apply (force simp: dist_norm open_contains_ball inverse_eq_divide [symmetric] eventually_at)
    done
qed

(** Existence of a primitive.*)
lemma holomorphic_starlike_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes contf: "continuous_on S f"
      and S: "starlike S" and os: "open S"
      and k: "finite k"
      and fcd: "\<And>x. x \<in> S - k \<Longrightarrow> f field_differentiable at x"
    shows "\<exists>g. \<forall>x \<in> S. (g has_field_derivative f x) (at x)"
proof -
  obtain a where a: "a\<in>S" and a_cs: "\<And>x. x\<in>S \<Longrightarrow> closed_segment a x \<subseteq> S"
    using S by (auto simp: starlike_def)
  { fix x b c
    assume "x \<in> S" "closed_segment b c \<subseteq> S"
    then have abcs: "convex hull {a, b, c} \<subseteq> S"
      by (simp add: a a_cs starlike_convex_subset)
    then have "continuous_on (convex hull {a, b, c}) f"
      by (simp add: continuous_on_subset [OF contf])
    then have "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
      using abcs interior_subset by (force intro: fcd Cauchy_theorem_triangle_cofinite [OF _ k])
  } note 0 = this
  show ?thesis
    apply (intro exI ballI)
    apply (rule triangle_contour_integrals_starlike_primitive [OF contf a os], assumption)
    apply (metis a_cs)
    apply (metis has_chain_integral_chain_integral3 0)
    done
qed

lemma Cauchy_theorem_starlike:
 "\<lbrakk>open S; starlike S; finite k; continuous_on S f;
   \<And>x. x \<in> S - k \<Longrightarrow> f field_differentiable at x;
   valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0)  g"
  by (metis holomorphic_starlike_primitive Cauchy_theorem_primitive at_within_open)

lemma Cauchy_theorem_starlike_simple:
  "\<lbrakk>open S; starlike S; f holomorphic_on S; valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0) g"
apply (rule Cauchy_theorem_starlike [OF _ _ finite.emptyI])
apply (simp_all add: holomorphic_on_imp_continuous_on)
apply (metis at_within_open holomorphic_on_def)
done

subsection\<open>Cauchy's theorem for a convex set\<close>

text\<open>For a convex set we can avoid assuming openness and boundary analyticity\<close>

lemma triangle_contour_integrals_convex_primitive:
  assumes contf: "continuous_on S f"
      and S: "a \<in> S" "convex S"
      and x: "x \<in> S"
      and zer: "\<And>b c. \<lbrakk>b \<in> S; c \<in> S\<rbrakk>
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x within S)"
proof -
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix y
    assume y: "y \<in> S"
    have cont_ayf: "continuous_on (closed_segment a y) f"
      using S y  by (meson contf continuous_on_subset convex_contains_segment)
    have xys: "closed_segment x y \<subseteq> S"  (*?*)
      using convex_contains_segment S x y by auto
    have "?pathint a y - ?pathint a x = ?pathint x y"
      using zer [OF x y]  contour_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
  } note [simp] = this
  { fix e::real
    assume e: "0 < e"
    have cont_atx: "continuous (at x within S) f"
      using x S contf  by (simp add: continuous_on_eq_continuous_within)
    then obtain d1 where d1: "d1>0" and d1_less: "\<And>y. \<lbrakk>y \<in> S; cmod (y - x) < d1\<rbrakk> \<Longrightarrow> cmod (f y - f x) < e/2"
      unfolding continuous_within Lim_within dist_norm using e
      by (drule_tac x="e/2" in spec) force
    { fix y
      assume yx: "y \<noteq> x" and close: "cmod (y - x) < d1" and y: "y \<in> S"
      have fxy: "f contour_integrable_on linepath x y"
        using convex_contains_segment S x y
        by (blast intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
      then obtain i where i: "(f has_contour_integral i) (linepath x y)"
        by (auto simp: contour_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_contour_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_contour_integral_diff [OF _ has_contour_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
      proof (rule has_contour_integral_bound_linepath)
        show "\<And>u. u \<in> closed_segment x y \<Longrightarrow> cmod (f u - f x) \<le> e / 2"
          by (meson assms(3) close convex_contains_segment d1_less le_less_trans less_imp_le segment_bound1 subset_iff x y)
      qed (use e in simp)
      also have "\<dots> < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: contour_integral_unique divide_less_eq)
    }
    then have "\<exists>d>0. \<forall>y\<in>S. y \<noteq> x \<and> cmod (y-x) < d \<longrightarrow> cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
      using d1 by blast
  }
  then have *: "((\<lambda>y. (contour_integral (linepath x y) f - f x * (y - x)) /\<^sub>R cmod (y - x)) \<longlongrightarrow> 0) (at x within S)"
    by (simp add: Lim_within dist_norm inverse_eq_divide)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_within bounded_linear_mult_right)
    apply (rule Lim_transform [OF * tendsto_eventually])
    using linordered_field_no_ub
    apply (force simp: inverse_eq_divide [symmetric] eventually_at)
    done
qed

lemma contour_integral_convex_primitive:
  assumes "convex S" "continuous_on S f"
          "\<And>a b c. \<lbrakk>a \<in> S; b \<in> S; c \<in> S\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
proof (cases "S={}")
  case False
  with assms that show ?thesis
    by (blast intro: triangle_contour_integrals_convex_primitive has_chain_integral_chain_integral3)
qed auto

lemma holomorphic_convex_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "convex S" "finite K" and contf: "continuous_on S f"
    and fd: "\<And>x. x \<in> interior S - K \<Longrightarrow> f field_differentiable at x"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
proof (rule contour_integral_convex_primitive [OF \<open>convex S\<close> contf Cauchy_theorem_triangle_cofinite])
  have *: "convex hull {a, b, c} \<subseteq> S" if "a \<in> S" "b \<in> S" "c \<in> S" for a b c
    by (simp add: \<open>convex S\<close> hull_minimal that)
  show "continuous_on (convex hull {a, b, c}) f" if "a \<in> S" "b \<in> S" "c \<in> S" for a b c
    by (meson "*" contf continuous_on_subset that)
  show "f field_differentiable at x" if "a \<in> S" "b \<in> S" "c \<in> S" "x \<in> interior (convex hull {a, b, c}) - K" for a b c x
    by (metis "*" DiffD1 DiffD2 DiffI fd interior_mono subsetCE that)
qed (use assms in \<open>force+\<close>)

lemma holomorphic_convex_primitive':
  fixes f :: "complex \<Rightarrow> complex"
  assumes "convex S" and "open S" and "f holomorphic_on S"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
proof (rule holomorphic_convex_primitive)
  fix x assume "x \<in> interior S - {}"
  with assms show "f field_differentiable at x"
    by (auto intro!: holomorphic_on_imp_differentiable_at simp: interior_open)
qed (use assms in \<open>auto intro: holomorphic_on_imp_continuous_on\<close>)

corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_convex:
    "\<lbrakk>continuous_on S f; convex S; finite K;
      \<And>x. x \<in> interior S - K \<Longrightarrow> f field_differentiable at x;
      valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
     \<Longrightarrow> (f has_contour_integral 0) g"
  by (metis holomorphic_convex_primitive Cauchy_theorem_primitive)

corollary Cauchy_theorem_convex_simple:
    "\<lbrakk>f holomorphic_on S; convex S;
     valid_path g; path_image g \<subseteq> S;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  apply (rule Cauchy_theorem_convex [where K = "{}"])
  apply (simp_all add: holomorphic_on_imp_continuous_on)
  using at_within_interior holomorphic_on_def interior_subset by fastforce

text\<open>In particular for a disc\<close>
corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_disc:
    "\<lbrakk>finite K; continuous_on (cball a e) f;
      \<And>x. x \<in> ball a e - K \<Longrightarrow> f field_differentiable at x;
     valid_path g; path_image g \<subseteq> cball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  by (auto intro: Cauchy_theorem_convex)

corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_disc_simple:
    "\<lbrakk>f holomorphic_on (ball a e); valid_path g; path_image g \<subseteq> ball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
by (simp add: Cauchy_theorem_convex_simple)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Generalize integrability to local primitives\<close>

lemma contour_integral_local_primitive_lemma:
  fixes f :: "complex\<Rightarrow>complex"
  shows
    "\<lbrakk>g piecewise_differentiable_on {a..b};
      \<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s);
      \<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f' (g x) * vector_derivative g (at x within {a..b}))
            integrable_on {a..b}"
  apply (cases "cbox a b = {}", force)
  apply (simp add: integrable_on_def)
  apply (rule exI)
  apply (rule contour_integral_primitive_lemma, assumption+)
  using atLeastAtMost_iff by blast

lemma contour_integral_local_primitive_any:
  fixes f :: "complex \<Rightarrow> complex"
  assumes gpd: "g piecewise_differentiable_on {a..b}"
      and dh: "\<And>x. x \<in> s
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      and gs: "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s"
  shows "(\<lambda>x. f(g x) * vector_derivative g (at x)) integrable_on {a..b}"
proof -
  { fix x
    assume x: "a \<le> x" "x \<le> b"
    obtain d h where d: "0 < d"
               and h: "(\<And>y. norm(y - g x) < d \<Longrightarrow> (h has_field_derivative f y) (at y within s))"
      using x gs dh by (metis atLeastAtMost_iff)
    have "continuous_on {a..b} g" using gpd piecewise_differentiable_on_def by blast
    then obtain e where e: "e>0" and lessd: "\<And>x'. x' \<in> {a..b} \<Longrightarrow> \<bar>x' - x\<bar> < e \<Longrightarrow> cmod (g x' - g x) < d"
      using x d
      apply (auto simp: dist_norm continuous_on_iff)
      apply (drule_tac x=x in bspec)
      using x apply simp
      apply (drule_tac x=d in spec, auto)
      done
    have "\<exists>d>0. \<forall>u v. u \<le> x \<and> x \<le> v \<and> {u..v} \<subseteq> ball x d \<and> (u \<le> v \<longrightarrow> a \<le> u \<and> v \<le> b) \<longrightarrow>
                          (\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on {u..v}"
      apply (rule_tac x=e in exI)
      using e
      apply (simp add: integrable_on_localized_vector_derivative [symmetric], clarify)
      apply (rule_tac f = h and s = "g ` {u..v}" in contour_integral_local_primitive_lemma)
        apply (meson atLeastatMost_subset_iff gpd piecewise_differentiable_on_subset)
       apply (force simp: ball_def dist_norm intro: lessd gs DERIV_subset [OF h], force)
      done
  } then
  show ?thesis
    by (force simp: intro!: integrable_on_little_subintervals [of a b, simplified])
qed

lemma contour_integral_local_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes g: "valid_path g" "path_image g \<subseteq> s"
      and dh: "\<And>x. x \<in> s
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
  shows "f contour_integrable_on g"
  using g
  apply (simp add: valid_path_def path_image_def contour_integrable_on_def has_contour_integral_def
            has_integral_localized_vector_derivative integrable_on_def [symmetric])
  using contour_integral_local_primitive_any [OF _ dh]
  by (meson image_subset_iff piecewise_C1_imp_differentiable)


text\<open>In particular if a function is holomorphic\<close>

lemma contour_integrable_holomorphic:
  assumes contf: "continuous_on s f"
      and os: "open s"
      and k: "finite k"
      and g: "valid_path g" "path_image g \<subseteq> s"
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f field_differentiable at x"
    shows "f contour_integrable_on g"
proof -
  { fix z
    assume z: "z \<in> s"
    obtain d where "d>0" and d: "ball z d \<subseteq> s" using  \<open>open s\<close> z
      by (auto simp: open_contains_ball)
    then have contfb: "continuous_on (ball z d) f"
      using contf continuous_on_subset by blast
    obtain h where "\<forall>y\<in>ball z d. (h has_field_derivative f y) (at y within ball z d)"
      by (metis holomorphic_convex_primitive [OF convex_ball k contfb fcd] d interior_subset Diff_iff subsetD)
    then have "\<forall>y\<in>ball z d. (h has_field_derivative f y) (at y within s)"
      by (metis open_ball at_within_open d os subsetCE)
    then have "\<exists>h. (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      by (force simp: dist_norm norm_minus_commute)
    then have "\<exists>d h. 0 < d \<and> (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      using \<open>0 < d\<close> by blast
  }
  then show ?thesis
    by (rule contour_integral_local_primitive [OF g])
qed

lemma contour_integrable_holomorphic_simple:
  assumes fh: "f holomorphic_on S"
      and os: "open S"
      and g: "valid_path g" "path_image g \<subseteq> S"
    shows "f contour_integrable_on g"
  apply (rule contour_integrable_holomorphic [OF _ os Finite_Set.finite.emptyI g])
  apply (simp add: fh holomorphic_on_imp_continuous_on)
  using fh  by (simp add: field_differentiable_def holomorphic_on_open os)

lemma continuous_on_inversediff:
  fixes z:: "'a::real_normed_field" shows "z \<notin> S \<Longrightarrow> continuous_on S (\<lambda>w. 1 / (w - z))"
  by (rule continuous_intros | force)+

lemma contour_integrable_inversediff:
    "\<lbrakk>valid_path g; z \<notin> path_image g\<rbrakk> \<Longrightarrow> (\<lambda>w. 1 / (w-z)) contour_integrable_on g"
apply (rule contour_integrable_holomorphic_simple [of _ "UNIV-{z}"])
apply (auto simp: holomorphic_on_open open_delete intro!: derivative_eq_intros)
done

text\<open>Key fact that path integral is the same for a "nearby" path. This is the
 main lemma for the homotopy form of Cauchy's theorem and is also useful
 if we want "without loss of generality" to assume some nice properties of a
 path (e.g. smoothness). It can also be used to define the integrals of
 analytic functions over arbitrary continuous paths. This is just done for
 winding numbers now.
\<close>

text\<open>A technical definition to avoid duplication of similar proofs,
     for paths joined at the ends versus looping paths\<close>
definition linked_paths :: "bool \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "linked_paths atends g h ==
        (if atends then pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                   else pathfinish g = pathstart g \<and> pathfinish h = pathstart h)"

text\<open>This formulation covers two cases: \<^term>\<open>g\<close> and \<^term>\<open>h\<close> share their
      start and end points; \<^term>\<open>g\<close> and \<^term>\<open>h\<close> both loop upon themselves.\<close>
lemma contour_integral_nearby:
  assumes os: "open S" and p: "path p" "path_image p \<subseteq> S"
  shows "\<exists>d. 0 < d \<and>
            (\<forall>g h. valid_path g \<and> valid_path h \<and>
                  (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                  linked_paths atends g h
                  \<longrightarrow> path_image g \<subseteq> S \<and> path_image h \<subseteq> S \<and>
                      (\<forall>f. f holomorphic_on S \<longrightarrow> contour_integral h f = contour_integral g f))"
proof -
  have "\<forall>z. \<exists>e. z \<in> path_image p \<longrightarrow> 0 < e \<and> ball z e \<subseteq> S"
    using open_contains_ball os p(2) by blast
  then obtain ee where ee: "\<And>z. z \<in> path_image p \<Longrightarrow> 0 < ee z \<and> ball z (ee z) \<subseteq> S"
    by metis
  define cover where "cover = (\<lambda>z. ball z (ee z/3)) ` (path_image p)"
  have "compact (path_image p)"
    by (metis p(1) compact_path_image)
  moreover have "path_image p \<subseteq> (\<Union>c\<in>path_image p. ball c (ee c / 3))"
    using ee by auto
  ultimately have "\<exists>D \<subseteq> cover. finite D \<and> path_image p \<subseteq> \<Union>D"
    by (simp add: compact_eq_Heine_Borel cover_def)
  then obtain D where D: "D \<subseteq> cover" "finite D" "path_image p \<subseteq> \<Union>D"
    by blast
  then obtain k where k: "k \<subseteq> {0..1}" "finite k" and D_eq: "D = ((\<lambda>z. ball z (ee z / 3)) \<circ> p) ` k"
    apply (simp add: cover_def path_image_def image_comp)
    apply (blast dest!: finite_subset_image [OF \<open>finite D\<close>])
    done
  then have kne: "k \<noteq> {}"
    using D by auto
  have pi: "\<And>i. i \<in> k \<Longrightarrow> p i \<in> path_image p"
    using k  by (auto simp: path_image_def)
  then have eepi: "\<And>i. i \<in> k \<Longrightarrow> 0 < ee((p i))"
    by (metis ee)
  define e where "e = Min((ee \<circ> p) ` k)"
  have fin_eep: "finite ((ee \<circ> p) ` k)"
    using k  by blast
  have "0 < e"
    using ee k  by (simp add: kne e_def Min_gr_iff [OF fin_eep] eepi)
  have "uniformly_continuous_on {0..1} p"
    using p  by (simp add: path_def compact_uniformly_continuous)
  then obtain d::real where d: "d>0"
          and de: "\<And>x x'. \<bar>x' - x\<bar> < d \<Longrightarrow> x\<in>{0..1} \<Longrightarrow> x'\<in>{0..1} \<Longrightarrow> cmod (p x' - p x) < e/3"
    unfolding uniformly_continuous_on_def dist_norm real_norm_def
    by (metis divide_pos_pos \<open>0 < e\<close> zero_less_numeral)
  then obtain N::nat where N: "N>0" "inverse N < d"
    using real_arch_inverse [of d]   by auto
  show ?thesis
  proof (intro exI conjI allI; clarify?)
    show "e/3 > 0"
      using \<open>0 < e\<close> by simp
    fix g h
    assume g: "valid_path g" and ghp: "\<forall>t\<in>{0..1}. cmod (g t - p t) < e / 3 \<and>  cmod (h t - p t) < e / 3"
       and h: "valid_path h"
       and joins: "linked_paths atends g h"
    { fix t::real
      assume t: "0 \<le> t" "t \<le> 1"
      then obtain u where u: "u \<in> k" and ptu: "p t \<in> ball(p u) (ee(p u) / 3)"
        using \<open>path_image p \<subseteq> \<Union>D\<close> D_eq by (force simp: path_image_def)
      then have ele: "e \<le> ee (p u)" using fin_eep
        by (simp add: e_def)
      have "cmod (g t - p t) < e / 3" "cmod (h t - p t) < e / 3"
        using ghp t by auto
      with ele have "cmod (g t - p t) < ee (p u) / 3"
                    "cmod (h t - p t) < ee (p u) / 3"
        by linarith+
      then have "g t \<in> ball(p u) (ee(p u))"  "h t \<in> ball(p u) (ee(p u))"
        using norm_diff_triangle_ineq [of "g t" "p t" "p t" "p u"]
              norm_diff_triangle_ineq [of "h t" "p t" "p t" "p u"] ptu eepi u
        by (force simp: dist_norm ball_def norm_minus_commute)+
      then have "g t \<in> S" "h t \<in> S" using ee u k
        by (auto simp: path_image_def ball_def)
    }
    then have ghs: "path_image g \<subseteq> S" "path_image h \<subseteq> S"
      by (auto simp: path_image_def)
    moreover
    { fix f
      assume fhols: "f holomorphic_on S"
      then have fpa: "f contour_integrable_on g"  "f contour_integrable_on h"
        using g ghs h holomorphic_on_imp_continuous_on os contour_integrable_holomorphic_simple
        by blast+
      have contf: "continuous_on S f"
        by (simp add: fhols holomorphic_on_imp_continuous_on)
      { fix z
        assume z: "z \<in> path_image p"
        have "f holomorphic_on ball z (ee z)"
          using fhols ee z holomorphic_on_subset by blast
        then have "\<exists>ff. (\<forall>w \<in> ball z (ee z). (ff has_field_derivative f w) (at w))"
          using holomorphic_convex_primitive [of "ball z (ee z)" "{}" f, simplified]
          by (metis open_ball at_within_open holomorphic_on_def holomorphic_on_imp_continuous_on mem_ball)
      }
      then obtain ff where ff:
            "\<And>z w. \<lbrakk>z \<in> path_image p; w \<in> ball z (ee z)\<rbrakk> \<Longrightarrow> (ff z has_field_derivative f w) (at w)"
        by metis
      { fix n
        assume n: "n \<le> N"
        then have "contour_integral(subpath 0 (n/N) h) f - contour_integral(subpath 0 (n/N) g) f =
                   contour_integral(linepath (g(n/N)) (h(n/N))) f - contour_integral(linepath (g 0) (h 0)) f"
        proof (induct n)
          case 0 show ?case by simp
        next
          case (Suc n)
          obtain t where t: "t \<in> k" and "p (n/N) \<in> ball(p t) (ee(p t) / 3)"
            using \<open>path_image p \<subseteq> \<Union>D\<close> [THEN subsetD, where c="p (n/N)"] D_eq N Suc.prems
            by (force simp: path_image_def)
          then have ptu: "cmod (p t - p (n/N)) < ee (p t) / 3"
            by (simp add: dist_norm)
          have e3le: "e/3 \<le> ee (p t) / 3"  using fin_eep t
            by (simp add: e_def)
          { fix x
            assume x: "n/N \<le> x" "x \<le> (1 + n)/N"
            then have nN01: "0 \<le> n/N" "(1 + n)/N \<le> 1"
              using Suc.prems by auto
            then have x01: "0 \<le> x" "x \<le> 1"
              using x by linarith+
            have "cmod (p t - p x)  < ee (p t) / 3 + e/3"
            proof (rule norm_diff_triangle_less [OF ptu de])
              show "\<bar>real n / real N - x\<bar> < d"
                using x N by (auto simp: field_simps)
            qed (use x01 Suc.prems in auto)
            then have ptx: "cmod (p t - p x) < 2*ee (p t)/3"
              using e3le eepi [OF t] by simp
            have "cmod (p t - g x) < 2*ee (p t)/3 + e/3 "
              apply (rule norm_diff_triangle_less [OF ptx])
              using ghp x01 by (simp add: norm_minus_commute)
            also have "\<dots> \<le> ee (p t)"
              using e3le eepi [OF t] by simp
            finally have gg: "cmod (p t - g x) < ee (p t)" .
            have "cmod (p t - h x) < 2*ee (p t)/3 + e/3 "
              apply (rule norm_diff_triangle_less [OF ptx])
              using ghp x01 by (simp add: norm_minus_commute)
            also have "\<dots> \<le> ee (p t)"
              using e3le eepi [OF t] by simp
            finally have "cmod (p t - g x) < ee (p t)"
                         "cmod (p t - h x) < ee (p t)"
              using gg by auto
          } note ptgh_ee = this
          have "closed_segment (g (real n / real N)) (h (real n / real N)) = path_image (linepath (h (n/N)) (g (n/N)))"
            by (simp add: closed_segment_commute)
          also have pi_hgn: "\<dots> \<subseteq> ball (p t) (ee (p t))"
            using ptgh_ee [of "n/N"] Suc.prems
            by (auto simp: field_simps dist_norm dest: segment_furthest_le [where y="p t"])
          finally have gh_ns: "closed_segment (g (n/N)) (h (n/N)) \<subseteq> S"
            using ee pi t by blast
          have pi_ghn': "path_image (linepath (g ((1 + n) / N)) (h ((1 + n) / N))) \<subseteq> ball (p t) (ee (p t))"
            using ptgh_ee [of "(1+n)/N"] Suc.prems
            by (auto simp: field_simps dist_norm dest: segment_furthest_le [where y="p t"])
          then have gh_n's: "closed_segment (g ((1 + n) / N)) (h ((1 + n) / N)) \<subseteq> S"
            using \<open>N>0\<close> Suc.prems ee pi t
            by (auto simp: Path_Connected.path_image_join field_simps)
          have pi_subset_ball:
                "path_image (subpath (n/N) ((1+n) / N) g +++ linepath (g ((1+n) / N)) (h ((1+n) / N)) +++
                             subpath ((1+n) / N) (n/N) h +++ linepath (h (n/N)) (g (n/N)))
                 \<subseteq> ball (p t) (ee (p t))"
            apply (intro subset_path_image_join pi_hgn pi_ghn')
            using \<open>N>0\<close> Suc.prems
            apply (auto simp: path_image_subpath dist_norm field_simps closed_segment_eq_real_ivl ptgh_ee)
            done
          have pi0: "(f has_contour_integral 0)
                       (subpath (n/ N) ((Suc n)/N) g +++ linepath(g ((Suc n) / N)) (h((Suc n) / N)) +++
                        subpath ((Suc n) / N) (n/N) h +++ linepath(h (n/N)) (g (n/N)))"
            apply (rule Cauchy_theorem_primitive [of "ball(p t) (ee(p t))" "ff (p t)" "f"])
            apply (metis ff open_ball at_within_open pi t)
            using Suc.prems pi_subset_ball apply (simp_all add: valid_path_join valid_path_subpath g h)
            done
          have fpa1: "f contour_integrable_on subpath (real n / real N) (real (Suc n) / real N) g"
            using Suc.prems by (simp add: contour_integrable_subpath g fpa)
          have fpa2: "f contour_integrable_on linepath (g (real (Suc n) / real N)) (h (real (Suc n) / real N))"
            using gh_n's
            by (auto intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
          have fpa3: "f contour_integrable_on linepath (h (real n / real N)) (g (real n / real N))"
            using gh_ns
            by (auto simp: closed_segment_commute intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
          have eq0: "contour_integral (subpath (n/N) ((Suc n) / real N) g) f +
                     contour_integral (linepath (g ((Suc n) / N)) (h ((Suc n) / N))) f +
                     contour_integral (subpath ((Suc n) / N) (n/N) h) f +
                     contour_integral (linepath (h (n/N)) (g (n/N))) f = 0"
            using contour_integral_unique [OF pi0] Suc.prems
            by (simp add: g h fpa valid_path_subpath contour_integrable_subpath
                          fpa1 fpa2 fpa3 algebra_simps del: of_nat_Suc)
          have *: "\<And>hn he hn' gn gd gn' hgn ghn gh0 ghn'.
                    \<lbrakk>hn - gn = ghn - gh0;
                     gd + ghn' + he + hgn = (0::complex);
                     hn - he = hn'; gn + gd = gn'; hgn = -ghn\<rbrakk> \<Longrightarrow> hn' - gn' = ghn' - gh0"
            by (auto simp: algebra_simps)
          have "contour_integral (subpath 0 (n/N) h) f - contour_integral (subpath ((Suc n) / N) (n/N) h) f =
                contour_integral (subpath 0 (n/N) h) f + contour_integral (subpath (n/N) ((Suc n) / N) h) f"
            unfolding reversepath_subpath [symmetric, of "((Suc n) / N)"]
            using Suc.prems by (simp add: h fpa contour_integral_reversepath valid_path_subpath contour_integrable_subpath)
          also have "\<dots> = contour_integral (subpath 0 ((Suc n) / N) h) f"
            using Suc.prems by (simp add: contour_integral_subpath_combine h fpa)
          finally have pi0_eq:
               "contour_integral (subpath 0 (n/N) h) f - contour_integral (subpath ((Suc n) / N) (n/N) h) f =
                contour_integral (subpath 0 ((Suc n) / N) h) f" .
          show ?case
            apply (rule * [OF Suc.hyps eq0 pi0_eq])
            using Suc.prems
            apply (simp_all add: g h fpa contour_integral_subpath_combine
                     contour_integral_reversepath [symmetric] contour_integrable_continuous_linepath
                     continuous_on_subset [OF contf gh_ns])
            done
      qed
      } note ind = this
      have "contour_integral h f = contour_integral g f"
        using ind [OF order_refl] N joins
        by (simp add: linked_paths_def pathstart_def pathfinish_def split: if_split_asm)
    }
    ultimately
    show "path_image g \<subseteq> S \<and> path_image h \<subseteq> S \<and> (\<forall>f. f holomorphic_on S \<longrightarrow> contour_integral h f = contour_integral g f)"
      by metis
  qed
qed


lemma
  assumes "open S" "path p" "path_image p \<subseteq> S"
    shows contour_integral_nearby_ends:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                    \<longrightarrow> path_image g \<subseteq> S \<and>
                        path_image h \<subseteq> S \<and>
                        (\<forall>f. f holomorphic_on S
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
    and contour_integral_nearby_loops:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathfinish g = pathstart g \<and> pathfinish h = pathstart h
                    \<longrightarrow> path_image g \<subseteq> S \<and>
                        path_image h \<subseteq> S \<and>
                        (\<forall>f. f holomorphic_on S
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
  using contour_integral_nearby [OF assms, where atends=True]
  using contour_integral_nearby [OF assms, where atends=False]
  unfolding linked_paths_def by simp_all

lemma contour_integral_bound_exists:
assumes S: "open S"
    and g: "valid_path g"
    and pag: "path_image g \<subseteq> S"
  shows "\<exists>L. 0 < L \<and>
             (\<forall>f B. f holomorphic_on S \<and> (\<forall>z \<in> S. norm(f z) \<le> B)
               \<longrightarrow> norm(contour_integral g f) \<le> L*B)"
proof -
  have "path g" using g
    by (simp add: valid_path_imp_path)
  then obtain d::real and p
    where d: "0 < d"
      and p: "polynomial_function p" "path_image p \<subseteq> S"
      and pi: "\<And>f. f holomorphic_on S \<Longrightarrow> contour_integral g f = contour_integral p f"
    using contour_integral_nearby_ends [OF S \<open>path g\<close> pag]
    apply clarify
    apply (drule_tac x=g in spec)
    apply (simp only: assms)
    apply (force simp: valid_path_polynomial_function dest: path_approx_polynomial_function)
    done
  then obtain p' where p': "polynomial_function p'"
    "\<And>x. (p has_vector_derivative (p' x)) (at x)"
    by (blast intro: has_vector_derivative_polynomial_function that)
  then have "bounded(p' ` {0..1})"
    using continuous_on_polymonial_function
    by (force simp: intro!: compact_imp_bounded compact_continuous_image)
  then obtain L where L: "L>0" and nop': "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> norm (p' x) \<le> L"
    by (force simp: bounded_pos)
  { fix f B
    assume f: "f holomorphic_on S" and B: "\<And>z. z\<in>S \<Longrightarrow> cmod (f z) \<le> B"
    then have "f contour_integrable_on p \<and> valid_path p"
      using p S
      by (blast intro: valid_path_polynomial_function contour_integrable_holomorphic_simple holomorphic_on_imp_continuous_on)
    moreover have "cmod (vector_derivative p (at x)) * cmod (f (p x)) \<le> L * B" if "0 \<le> x" "x \<le> 1" for x
    proof (rule mult_mono)
      show "cmod (vector_derivative p (at x)) \<le> L"
        by (metis nop' p'(2) that vector_derivative_at)
      show "cmod (f (p x)) \<le> B"
        by (metis B atLeastAtMost_iff imageI p(2) path_defs(4) subset_eq that)
    qed (use \<open>L>0\<close> in auto)
    ultimately have "cmod (contour_integral g f) \<le> L * B"
      apply (simp only: pi [OF f])
      apply (simp only: contour_integral_integral)
      apply (rule order_trans [OF integral_norm_bound_integral])
         apply (auto simp: mult.commute integral_norm_bound_integral contour_integrable_on [symmetric] norm_mult)
      done
  } then
  show ?thesis using \<open>L > 0\<close>
    by (intro exI[of _ L]) auto
qed


subsection\<open>Homotopy forms of Cauchy's theorem\<close>

lemma Cauchy_theorem_homotopic:
    assumes hom: "if atends then homotopic_paths s g h else homotopic_loops s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
proof -
  have pathsf: "linked_paths atends g h"
    using hom  by (auto simp: linked_paths_def homotopic_paths_imp_pathstart homotopic_paths_imp_pathfinish homotopic_loops_imp_loop)
  obtain k :: "real \<times> real \<Rightarrow> complex"
    where contk: "continuous_on ({0..1} \<times> {0..1}) k"
      and ks: "k ` ({0..1} \<times> {0..1}) \<subseteq> s"
      and k [simp]: "\<forall>x. k (0, x) = g x" "\<forall>x. k (1, x) = h x"
      and ksf: "\<forall>t\<in>{0..1}. linked_paths atends g (\<lambda>x. k (t, x))"
      using hom pathsf by (auto simp: linked_paths_def homotopic_paths_def homotopic_loops_def homotopic_with_def split: if_split_asm)
  have ucontk: "uniformly_continuous_on ({0..1} \<times> {0..1}) k"
    by (blast intro: compact_Times compact_uniformly_continuous [OF contk])
  { fix t::real assume t: "t \<in> {0..1}"
    have pak: "path (k \<circ> (\<lambda>u. (t, u)))"
      unfolding path_def
      apply (rule continuous_intros continuous_on_subset [OF contk])+
      using t by force
    have pik: "path_image (k \<circ> Pair t) \<subseteq> s"
      using ks t by (auto simp: path_image_def)
    obtain e where "e>0" and e:
         "\<And>g h. \<lbrakk>valid_path g; valid_path h;
                  \<forall>u\<in>{0..1}. cmod (g u - (k \<circ> Pair t) u) < e \<and> cmod (h u - (k \<circ> Pair t) u) < e;
                  linked_paths atends g h\<rbrakk>
                 \<Longrightarrow> contour_integral h f = contour_integral g f"
      using contour_integral_nearby [OF \<open>open s\<close> pak pik, of atends] f by metis
    obtain d where "d>0" and d:
        "\<And>x x'. \<lbrakk>x \<in> {0..1} \<times> {0..1}; x' \<in> {0..1} \<times> {0..1}; norm (x'-x) < d\<rbrakk> \<Longrightarrow> norm (k x' - k x) < e/4"
      by (rule uniformly_continuous_onE [OF ucontk, of "e/4"]) (auto simp: dist_norm \<open>e>0\<close>)
    { fix t1 t2
      assume t1: "0 \<le> t1" "t1 \<le> 1" and t2: "0 \<le> t2" "t2 \<le> 1" and ltd: "\<bar>t1 - t\<bar> < d" "\<bar>t2 - t\<bar> < d"
      have no2: "\<And>g1 k1 kt. \<lbrakk>norm(g1 - k1) < e/4; norm(k1 - kt) < e/4\<rbrakk> \<Longrightarrow> norm(g1 - kt) < e"
        using \<open>e > 0\<close>
        apply (rule_tac y = k1 in norm_triangle_half_l)
        apply (auto simp: norm_minus_commute intro: order_less_trans)
        done
      have "\<exists>d>0. \<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                          (\<forall>u\<in>{0..1}. cmod (g1 u - k (t1, u)) < d \<and> cmod (g2 u - k (t2, u)) < d) \<and>
                          linked_paths atends g1 g2 \<longrightarrow>
                          contour_integral g2 f = contour_integral g1 f"
        apply (rule_tac x="e/4" in exI)
        using t t1 t2 ltd \<open>e > 0\<close>
        apply (auto intro!: e simp: d no2 simp del: less_divide_eq_numeral1)
        done
    }
    then have "\<exists>e. 0 < e \<and>
              (\<forall>t1 t2. t1 \<in> {0..1} \<and> t2 \<in> {0..1} \<and> \<bar>t1 - t\<bar> < e \<and> \<bar>t2 - t\<bar> < e
                \<longrightarrow> (\<exists>d. 0 < d \<and>
                     (\<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                       (\<forall>u \<in> {0..1}.
                          norm(g1 u - k((t1,u))) < d \<and> norm(g2 u - k((t2,u))) < d) \<and>
                          linked_paths atends g1 g2
                          \<longrightarrow> contour_integral g2 f = contour_integral g1 f)))"
      by (rule_tac x=d in exI) (simp add: \<open>d > 0\<close>)
  }
  then obtain ee where ee:
       "\<And>t. t \<in> {0..1} \<Longrightarrow> ee t > 0 \<and>
          (\<forall>t1 t2. t1 \<in> {0..1} \<longrightarrow> t2 \<in> {0..1} \<longrightarrow> \<bar>t1 - t\<bar> < ee t \<longrightarrow> \<bar>t2 - t\<bar> < ee t
            \<longrightarrow> (\<exists>d. 0 < d \<and>
                 (\<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                   (\<forall>u \<in> {0..1}.
                      norm(g1 u - k((t1,u))) < d \<and> norm(g2 u - k((t2,u))) < d) \<and>
                      linked_paths atends g1 g2
                      \<longrightarrow> contour_integral g2 f = contour_integral g1 f)))"
    by metis
  note ee_rule = ee [THEN conjunct2, rule_format]
  define C where "C = (\<lambda>t. ball t (ee t / 3)) ` {0..1}"
  obtain C' where C': "C' \<subseteq> C" "finite C'" and C'01: "{0..1} \<subseteq> \<Union>C'"
  proof (rule compactE [OF compact_interval])
    show "{0..1} \<subseteq> \<Union>C"
      using ee [THEN conjunct1] by (auto simp: C_def dist_norm)
  qed (use C_def in auto)
  define kk where "kk = {t \<in> {0..1}. ball t (ee t / 3) \<in> C'}"
  have kk01: "kk \<subseteq> {0..1}" by (auto simp: kk_def)
  define e where "e = Min (ee ` kk)"
  have C'_eq: "C' = (\<lambda>t. ball t (ee t / 3)) ` kk"
    using C' by (auto simp: kk_def C_def)
  have ee_pos[simp]: "\<And>t. t \<in> {0..1} \<Longrightarrow> ee t > 0"
    by (simp add: kk_def ee)
  moreover have "finite kk"
    using \<open>finite C'\<close> kk01 by (force simp: C'_eq inj_on_def ball_eq_ball_iff dest: ee_pos finite_imageD)
  moreover have "kk \<noteq> {}" using \<open>{0..1} \<subseteq> \<Union>C'\<close> C'_eq by force
  ultimately have "e > 0"
    using finite_less_Inf_iff [of "ee ` kk" 0] kk01 by (force simp: e_def)
  then obtain N::nat where "N > 0" and N: "1/N < e/3"
    by (meson divide_pos_pos nat_approx_posE zero_less_Suc zero_less_numeral)
  have e_le_ee: "\<And>i. i \<in> kk \<Longrightarrow> e \<le> ee i"
    using \<open>finite kk\<close> by (simp add: e_def Min_le_iff [of "ee ` kk"])
  have plus: "\<exists>t \<in> kk. x \<in> ball t (ee t / 3)" if "x \<in> {0..1}" for x
    using C' subsetD [OF C'01 that]  unfolding C'_eq by blast
  have [OF order_refl]:
      "\<exists>d. 0 < d \<and> (\<forall>j. valid_path j \<and> (\<forall>u \<in> {0..1}. norm(j u - k (n/N, u)) < d) \<and> linked_paths atends g j
                        \<longrightarrow> contour_integral j f = contour_integral g f)"
       if "n \<le> N" for n
  using that
  proof (induct n)
    case 0 show ?case using ee_rule [of 0 0 0]
      apply clarsimp
      apply (rule_tac x=d in exI, safe)
      by (metis diff_self vpg norm_zero)
  next
    case (Suc n)
    then have N01: "n/N \<in> {0..1}" "(Suc n)/N \<in> {0..1}"  by auto
    then obtain t where t: "t \<in> kk" "n/N \<in> ball t (ee t / 3)"
      using plus [of "n/N"] by blast
    then have nN_less: "\<bar>n/N - t\<bar> < ee t"
      by (simp add: dist_norm del: less_divide_eq_numeral1)
    have n'N_less: "\<bar>real (Suc n) / real N - t\<bar> < ee t"
      using t N \<open>N > 0\<close> e_le_ee [of t]
      by (simp add: dist_norm add_divide_distrib abs_diff_less_iff del: less_divide_eq_numeral1) (simp add: field_simps)
    have t01: "t \<in> {0..1}" using \<open>kk \<subseteq> {0..1}\<close> \<open>t \<in> kk\<close> by blast
    obtain d1 where "d1 > 0" and d1:
        "\<And>g1 g2. \<lbrakk>valid_path g1; valid_path g2;
                   \<forall>u\<in>{0..1}. cmod (g1 u - k (n/N, u)) < d1 \<and> cmod (g2 u - k ((Suc n) / N, u)) < d1;
                   linked_paths atends g1 g2\<rbrakk>
                   \<Longrightarrow> contour_integral g2 f = contour_integral g1 f"
      using ee [THEN conjunct2, rule_format, OF t01 N01 nN_less n'N_less] by fastforce
    have "n \<le> N" using Suc.prems by auto
    with Suc.hyps
    obtain d2 where "d2 > 0"
      and d2: "\<And>j. \<lbrakk>valid_path j; \<forall>u\<in>{0..1}. cmod (j u - k (n/N, u)) < d2; linked_paths atends g j\<rbrakk>
                     \<Longrightarrow> contour_integral j f = contour_integral g f"
        by auto
    have "continuous_on {0..1} (k \<circ> (\<lambda>u. (n/N, u)))"
      apply (rule continuous_intros continuous_on_subset [OF contk])+
      using N01 by auto
    then have pkn: "path (\<lambda>u. k (n/N, u))"
      by (simp add: path_def)
    have min12: "min d1 d2 > 0" by (simp add: \<open>0 < d1\<close> \<open>0 < d2\<close>)
    obtain p where "polynomial_function p"
        and psf: "pathstart p = pathstart (\<lambda>u. k (n/N, u))"
                 "pathfinish p = pathfinish (\<lambda>u. k (n/N, u))"
        and pk_le:  "\<And>t. t\<in>{0..1} \<Longrightarrow> cmod (p t - k (n/N, t)) < min d1 d2"
      using path_approx_polynomial_function [OF pkn min12] by blast
    then have vpp: "valid_path p" using valid_path_polynomial_function by blast
    have lpa: "linked_paths atends g p"
      by (metis (mono_tags, lifting) N01(1) ksf linked_paths_def pathfinish_def pathstart_def psf)
    show ?case
    proof (intro exI; safe)
      fix j
      assume "valid_path j" "linked_paths atends g j"
        and "\<forall>u\<in>{0..1}. cmod (j u - k (real (Suc n) / real N, u)) < min d1 d2"
      then have "contour_integral j f = contour_integral p f"
        using pk_le N01(1) ksf by (force intro!: vpp d1 simp add: linked_paths_def psf)
      also have "... = contour_integral g f"
        using pk_le by (force intro!: vpp d2 lpa)
      finally show "contour_integral j f = contour_integral g f" .
    qed (simp add: \<open>0 < d1\<close> \<open>0 < d2\<close>)
  qed
  then obtain d where "0 < d"
                       "\<And>j. valid_path j \<and> (\<forall>u \<in> {0..1}. norm(j u - k (1,u)) < d) \<and> linked_paths atends g j
                            \<Longrightarrow> contour_integral j f = contour_integral g f"
    using \<open>N>0\<close> by auto
  then have "linked_paths atends g h \<Longrightarrow> contour_integral h f = contour_integral g f"
    using \<open>N>0\<close> vph by fastforce
  then show ?thesis
    by (simp add: pathsf)
qed

proposition Cauchy_theorem_homotopic_paths:
    assumes hom: "homotopic_paths s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
  using Cauchy_theorem_homotopic [of True s g h] assms by simp

proposition Cauchy_theorem_homotopic_loops:
    assumes hom: "homotopic_loops s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
  using Cauchy_theorem_homotopic [of False s g h] assms by simp

lemma has_contour_integral_newpath:
    "\<lbrakk>(f has_contour_integral y) h; f contour_integrable_on g; contour_integral g f = contour_integral h f\<rbrakk>
     \<Longrightarrow> (f has_contour_integral y) g"
  using has_contour_integral_integral contour_integral_unique by auto

lemma Cauchy_theorem_null_homotopic:
     "\<lbrakk>f holomorphic_on s; open s; valid_path g; homotopic_loops s g (linepath a a)\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  apply (rule has_contour_integral_newpath [where h = "linepath a a"], simp)
  using contour_integrable_holomorphic_simple
    apply (blast dest: holomorphic_on_imp_continuous_on homotopic_loops_imp_subset)
  by (simp add: Cauchy_theorem_homotopic_loops)

end
section \<open>The Great Picard Theorem and its Applications\<close>

text\<open>Ported from HOL Light (cauchy.ml) by L C Paulson, 2017\<close>

theory Great_Picard
  imports Conformal_Mappings
begin
  
subsection\<open>Schottky's theorem\<close>

lemma Schottky_lemma0:
  assumes holf: "f holomorphic_on S" and cons: "contractible S" and "a \<in> S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S"
                  "norm(g a) \<le> 1 + norm(f a) / 3"
                  "\<And>z. z \<in> S \<Longrightarrow> f z = cos(of_real pi * g z)"
proof -
  obtain g where holg: "g holomorphic_on S" and g: "norm(g a) \<le> pi + norm(f a)"
             and f_eq_cos: "\<And>z. z \<in> S \<Longrightarrow> f z = cos(g z)"
    using contractible_imp_holomorphic_arccos_bounded [OF assms]
    by blast
  show ?thesis
  proof
    show "(\<lambda>z. g z / pi) holomorphic_on S"
      by (auto intro: holomorphic_intros holg)
    have "3 \<le> pi"
      using pi_approx by force
    have "3 * norm(g a) \<le> 3 * (pi + norm(f a))"
      using g by auto
    also have "... \<le>  pi * 3 + pi * cmod (f a)"
      using \<open>3 \<le> pi\<close> by (simp add: mult_right_mono algebra_simps)
    finally show "cmod (g a / complex_of_real pi) \<le> 1 + cmod (f a) / 3"
      by (simp add: field_simps norm_divide)
    show "\<And>z. z \<in> S \<Longrightarrow> f z = cos (complex_of_real pi * (g z / complex_of_real pi))"
      by (simp add: f_eq_cos)
  qed
qed


lemma Schottky_lemma1:
  fixes n::nat
  assumes "0 < n"
  shows "0 < n + sqrt(real n ^ 2 - 1)"
proof -
  have "0 < n * n"
    by (simp add: assms)
  then show ?thesis
    by (metis add.commute add.right_neutral add_pos_nonneg assms diff_ge_0_iff_ge nat_less_real_le of_nat_0 of_nat_0_less_iff of_nat_power power2_eq_square real_sqrt_ge_0_iff)
qed


lemma Schottky_lemma2:
  fixes x::real
  assumes "0 \<le> x"
  obtains n where "0 < n" "\<bar>x - ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi\<bar> < 1/2"
proof -
  obtain n0::nat where "0 < n0" "ln(n0 + sqrt(real n0 ^ 2 - 1)) / pi \<le> x"
  proof
    show "ln(real 1 + sqrt(real 1 ^ 2 - 1))/pi \<le> x"
      by (auto simp: assms)
  qed auto
  moreover
  obtain M::nat where "\<And>n. \<lbrakk>0 < n; ln(n + sqrt(real n ^ 2 - 1)) / pi \<le> x\<rbrakk> \<Longrightarrow> n \<le> M"
  proof
    fix n::nat
    assume "0 < n" "ln (n + sqrt ((real n)\<^sup>2 - 1)) / pi \<le> x"
    then have "ln (n + sqrt ((real n)\<^sup>2 - 1)) \<le> x * pi"
      by (simp add: field_split_simps)
    then have *: "exp (ln (n + sqrt ((real n)\<^sup>2 - 1))) \<le> exp (x * pi)"
      by blast
    have 0: "0 \<le> sqrt ((real n)\<^sup>2 - 1)"
      using \<open>0 < n\<close> by auto
    have "n + sqrt ((real n)\<^sup>2 - 1) = exp (ln (n + sqrt ((real n)\<^sup>2 - 1)))"
      by (simp add: Suc_leI \<open>0 < n\<close> add_pos_nonneg real_of_nat_ge_one_iff)
    also have "... \<le> exp (x * pi)"
      using "*" by blast
    finally have "real n \<le> exp (x * pi)"
      using 0 by linarith
    then show "n \<le> nat (ceiling (exp(x * pi)))"
      by linarith
  qed
  ultimately obtain n where
     "0 < n" and le_x: "ln(n + sqrt(real n ^ 2 - 1)) / pi \<le> x"
             and le_n: "\<And>k. \<lbrakk>0 < k; ln(k + sqrt(real k ^ 2 - 1)) / pi \<le> x\<rbrakk> \<Longrightarrow> k \<le> n"
    using bounded_Max_nat [of "\<lambda>n. 0<n \<and> ln (n + sqrt ((real n)\<^sup>2 - 1)) / pi \<le> x"] by metis
  define a where "a \<equiv> ln(n + sqrt(real n ^ 2 - 1)) / pi"
  define b where "b \<equiv> ln (1 + real n + sqrt ((1 + real n)\<^sup>2 - 1)) / pi"
  have le_xa: "a \<le> x"
   and le_na: "\<And>k. \<lbrakk>0 < k; ln(k + sqrt(real k ^ 2 - 1)) / pi \<le> x\<rbrakk> \<Longrightarrow> k \<le> n"
    using le_x le_n by (auto simp: a_def)
  moreover have "x < b"
    using le_n [of "Suc n"] by (force simp: b_def)
  moreover have "b - a < 1"
  proof -
    have "ln (1 + real n + sqrt ((1 + real n)\<^sup>2 - 1)) - ln (real n + sqrt ((real n)\<^sup>2 - 1)) =
         ln ((1 + real n + sqrt ((1 + real n)\<^sup>2 - 1)) / (real n + sqrt ((real n)\<^sup>2 - 1)))"
      by (simp add: \<open>0 < n\<close> Schottky_lemma1 add_pos_nonneg ln_div [symmetric])
    also have "... \<le> 3"
    proof (cases "n = 1")
      case True
      have "sqrt 3 \<le> 2"
        by (simp add: real_le_lsqrt)
      then have "(2 + sqrt 3) \<le> 4"
        by simp
      also have "... \<le> exp 3"
        using exp_ge_add_one_self [of "3::real"] by simp
      finally have "ln (2 + sqrt 3) \<le> 3"
        by (metis add_nonneg_nonneg add_pos_nonneg dbl_def dbl_inc_def dbl_inc_simps(3)
            dbl_simps(3) exp_gt_zero ln_exp ln_le_cancel_iff real_sqrt_ge_0_iff zero_le_one zero_less_one)
      then show ?thesis
        by (simp add: True)
    next
      case False with \<open>0 < n\<close> have "1 < n" "2 \<le> n"
        by linarith+
      then have 1: "1 \<le> real n * real n"
        by (metis less_imp_le_nat one_le_power power2_eq_square real_of_nat_ge_one_iff)
      have *: "4 + (m+2) * 2 \<le> (m+2) * ((m+2) * 3)" for m::nat
        by simp
      have "4 + n * 2 \<le> n * (n * 3)"
        using * [of "n-2"]  \<open>2 \<le> n\<close>
        by (metis le_add_diff_inverse2)
      then have **: "4 + real n * 2 \<le> real n * (real n * 3)"
        by (metis (mono_tags, opaque_lifting) of_nat_le_iff of_nat_add of_nat_mult of_nat_numeral)
      have "sqrt ((1 + real n)\<^sup>2 - 1) \<le> 2 * sqrt ((real n)\<^sup>2 - 1)"
        by (auto simp: real_le_lsqrt power2_eq_square algebra_simps 1 **)
      then
      have "((1 + real n + sqrt ((1 + real n)\<^sup>2 - 1)) / (real n + sqrt ((real n)\<^sup>2 - 1))) \<le> 2"
        using Schottky_lemma1 \<open>0 < n\<close>  by (simp add: field_split_simps)
      then have "ln ((1 + real n + sqrt ((1 + real n)\<^sup>2 - 1)) / (real n + sqrt ((real n)\<^sup>2 - 1))) \<le> ln 2"
        using Schottky_lemma1 [of n] \<open>0 < n\<close> 
        by (simp add: field_split_simps add_pos_nonneg)
      also have "... \<le> 3"
        using ln_add_one_self_le_self [of 1] by auto
      finally show ?thesis .
    qed
    also have "... < pi"
      using pi_approx by simp
    finally show ?thesis
      by (simp add: a_def b_def field_split_simps)
  qed
  ultimately have "\<bar>x - a\<bar> < 1/2 \<or> \<bar>x - b\<bar> < 1/2"
    by (auto simp: abs_if)
  then show thesis
  proof
    assume "\<bar>x - a\<bar> < 1/2"
    then show ?thesis
      by (rule_tac n=n in that) (auto simp: a_def \<open>0 < n\<close>)
  next
    assume "\<bar>x - b\<bar> < 1/2"
    then show ?thesis
      by (rule_tac n="Suc n" in that) (auto simp: b_def \<open>0 < n\<close>)
  qed
qed


lemma Schottky_lemma3:
  fixes z::complex
  assumes "z \<in> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (ln(n + sqrt(real n ^ 2 - 1)) / pi)})
             \<union> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (-ln(n + sqrt(real n ^ 2 - 1)) / pi)})"
  shows "cos(pi * cos(pi * z)) = 1 \<or> cos(pi * cos(pi * z)) = -1"
proof -
  have sqrt2 [simp]: "complex_of_real (sqrt x) * complex_of_real (sqrt x) = x" if "x \<ge> 0" for x::real
    by (metis abs_of_nonneg of_real_mult real_sqrt_mult_self that)
  define plusi where "plusi (e::complex) \<equiv> e + inverse e" for e
  have 1: "\<exists>k. plusi (exp (\<i> * (of_int m * complex_of_real pi) - ln (real n + sqrt ((real n)\<^sup>2 - 1)))) = of_int k * 2" 
           (is "\<exists>k. ?\<Phi> k")
         if "n > 0" for m n
  proof -
    have eeq: "e \<noteq> 0 \<Longrightarrow> plusi e = n \<longleftrightarrow> (inverse e) ^ 2 = n/e - 1" for n e::complex
      by (auto simp: plusi_def field_simps power2_eq_square)
    have [simp]: "1 \<le> real n * real n"
      using nat_0_less_mult_iff nat_less_real_le that by force
    consider "odd m" | "even m"
      by blast
    then have "\<exists>k. ?\<Phi> k"
    proof cases
      case 1
      then have "?\<Phi> (- n)"
        using Schottky_lemma1 [OF that]
        by (simp add: eeq) (simp add: power2_eq_square exp_diff exp_Euler exp_of_real algebra_simps sin_int_times_real cos_int_times_real)
      then show ?thesis ..
    next
      case 2
      then have "?\<Phi> n"
        using Schottky_lemma1 [OF that]
        by (simp add: eeq) (simp add: power2_eq_square exp_diff exp_Euler exp_of_real algebra_simps)
      then show ?thesis ..
    qed
    then show ?thesis by blast
  qed
  have 2: "\<exists>k. plusi (exp (\<i> * (of_int m * complex_of_real pi) +
                      (ln (real n + sqrt ((real n)\<^sup>2 - 1))))) = of_int k * 2"
           (is "\<exists>k. ?\<Phi> k")
            if "n > 0" for m n
  proof -
    have eeq: "e \<noteq> 0 \<Longrightarrow> plusi e = n \<longleftrightarrow> e^2 - n*e + 1 = 0" for n e::complex
      by (auto simp: plusi_def field_simps power2_eq_square)
    have [simp]: "1 \<le> real n * real n"
      by (metis One_nat_def add.commute nat_less_real_le of_nat_1 of_nat_Suc one_le_power power2_eq_square that)
    consider "odd m" | "even m"
      by blast
    then have "\<exists>k. ?\<Phi> k"
    proof cases
      case 1
      then have "?\<Phi> (- n)"
        using Schottky_lemma1 [OF that]
        by (simp add: eeq) (simp add: power2_eq_square exp_add exp_Euler exp_of_real algebra_simps sin_int_times_real cos_int_times_real)
      then show ?thesis ..
    next
      case 2
      then have "?\<Phi> n"
        using Schottky_lemma1 [OF that]
        by (simp add: eeq) (simp add: power2_eq_square exp_add exp_Euler exp_of_real algebra_simps)
      then show ?thesis ..
    qed
    then show ?thesis by blast
  qed
  have "\<exists>x. cos (complex_of_real pi * z) = of_int x"
    using assms
    apply (auto simp: Ints_def cos_exp_eq exp_minus Complex_eq simp flip: plusi_def)
     apply (auto simp: algebra_simps dest: 1 2)
    done
  then have "sin(pi * cos(pi * z)) ^ 2 = 0"
    by (simp add: Complex_Transcendental.sin_eq_0)
  then have "1 - cos(pi * cos(pi * z)) ^ 2 = 0"
    by (simp add: sin_squared_eq)
  then show ?thesis
    using power2_eq_1_iff by auto
qed


theorem Schottky:
  assumes holf: "f holomorphic_on cball 0 1"
      and nof0: "norm(f 0) \<le> r"
      and not01: "\<And>z. z \<in> cball 0 1 \<Longrightarrow> \<not>(f z = 0 \<or> f z = 1)"
      and "0 < t" "t < 1" "norm z \<le> t"
    shows "norm(f z) \<le> exp(pi * exp(pi * (2 + 2 * r + 12 * t / (1 - t))))"
proof -
  obtain h where holf: "h holomorphic_on cball 0 1"
             and nh0: "norm (h 0) \<le> 1 + norm(2 * f 0 - 1) / 3"
             and h:   "\<And>z. z \<in> cball 0 1 \<Longrightarrow> 2 * f z - 1 = cos(of_real pi * h z)"
  proof (rule Schottky_lemma0 [of "\<lambda>z. 2 * f z - 1" "cball 0 1" 0])
    show "(\<lambda>z. 2 * f z - 1) holomorphic_on cball 0 1"
      by (intro holomorphic_intros holf)
    show "contractible (cball (0::complex) 1)"
      by (auto simp: convex_imp_contractible)
    show "\<And>z. z \<in> cball 0 1 \<Longrightarrow> 2 * f z - 1 \<noteq> 1 \<and> 2 * f z - 1 \<noteq> - 1"
      using not01 by force
  qed auto
  obtain g where holg: "g holomorphic_on cball 0 1"
             and ng0:  "norm(g 0) \<le> 1 + norm(h 0) / 3"
             and g:    "\<And>z. z \<in> cball 0 1 \<Longrightarrow> h z = cos(of_real pi * g z)"
  proof (rule Schottky_lemma0 [OF holf convex_imp_contractible, of 0])
    show "\<And>z. z \<in> cball 0 1 \<Longrightarrow> h z \<noteq> 1 \<and> h z \<noteq> - 1"
      using h not01 by fastforce+
  qed auto
  have g0_2_f0: "norm(g 0) \<le> 2 + norm(f 0)"
  proof -
    have "cmod (2 * f 0 - 1) \<le> cmod (2 * f 0) + 1"
      by (metis norm_one norm_triangle_ineq4)
    also have "... \<le> 6 + 9 * cmod (f 0)"
      by auto
    finally have "1 + norm(2 * f 0 - 1) / 3 \<le> (2 + norm(f 0) - 1) * 3"
      by (simp add: divide_simps)
    with nh0 have "norm(h 0) \<le> (2 + norm(f 0) - 1) * 3"
      by linarith
    then have "1 + norm(h 0) / 3 \<le> 2 + norm(f 0)"
      by simp
    with ng0 show ?thesis
      by auto
  qed
  have "z \<in> ball 0 1"
    using assms by auto
  have norm_g_12: "norm(g z - g 0) \<le> (12 * t) / (1 - t)"
  proof -
    obtain g' where g': "\<And>x. x \<in> cball 0 1 \<Longrightarrow> (g has_field_derivative g' x) (at x within cball 0 1)"
      using holg [unfolded holomorphic_on_def field_differentiable_def] by metis
    have int_g': "(g' has_contour_integral g z - g 0) (linepath 0 z)"
      using contour_integral_primitive [OF g' valid_path_linepath, of 0 z]
      using \<open>z \<in> ball 0 1\<close> segment_bound1 by fastforce
    have "cmod (g' w) \<le> 12 / (1 - t)" if "w \<in> closed_segment 0 z" for w
    proof -
      have w: "w \<in> ball 0 1"
        using segment_bound [OF that] \<open>z \<in> ball 0 1\<close> by simp
      have *: "\<lbrakk>\<And>b. (\<exists>w \<in> T \<union> U. w \<in> ball b 1); \<And>x. x \<in> D \<Longrightarrow> g x \<notin> T \<union> U\<rbrakk> \<Longrightarrow> \<nexists>b. ball b 1 \<subseteq> g ` D" for T U D
        by force
      have ttt: "1 - t \<le> dist w u" if "cmod u = 1" for u
        using \<open>norm z \<le> t\<close> segment_bound1 [OF \<open>w \<in> closed_segment 0 z\<close>] norm_triangle_ineq2 [of u w] that
        by (simp add: dist_norm norm_minus_commute)
      have "\<nexists>b. ball b 1 \<subseteq> g ` cball 0 1"
      proof (rule *)
        show "(\<exists>w \<in> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (ln(n + sqrt(real n ^ 2 - 1)) / pi)}) \<union>
                    (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (-ln(n + sqrt(real n ^ 2 - 1)) / pi)}). w \<in> ball b 1)" for b
        proof -
          obtain m where m: "m \<in> \<int>" "\<bar>Re b - m\<bar> \<le> 1/2"
            by (metis Ints_of_int abs_minus_commute of_int_round_abs_le)
          show ?thesis
          proof (cases "0::real" "Im b" rule: le_cases)
            case le
            then obtain n where "0 < n" and n: "\<bar>Im b - ln (n + sqrt ((real n)\<^sup>2 - 1)) / pi\<bar> < 1/2"
              using Schottky_lemma2 [of "Im b"] by blast
            have "dist b (Complex m (Im b)) \<le> 1/2"
              by (metis cancel_comm_monoid_add_class.diff_cancel cmod_eq_Re complex.sel(1) complex.sel(2) dist_norm m(2) minus_complex.code)
            moreover
            have "dist (Complex m (Im b)) (Complex m (ln (n + sqrt ((real n)\<^sup>2 - 1)) / pi)) < 1/2"
              using n by (simp add: complex_norm cmod_eq_Re complex_diff dist_norm del: Complex_eq)
            ultimately have "dist b (Complex m (ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi)) < 1"
              by (simp add: dist_triangle_lt [of b "Complex m (Im b)"] dist_commute)
            with le m \<open>0 < n\<close> show ?thesis
              apply (rule_tac x = "Complex m (ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi)" in bexI)
               by (force simp del: Complex_eq greaterThan_0)+
          next
            case ge
            then obtain n where "0 < n" and n: "\<bar>- Im b - ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi\<bar> < 1/2"
              using Schottky_lemma2 [of "- Im b"] by auto
            have "dist b (Complex m (Im b)) \<le> 1/2"
              by (metis cancel_comm_monoid_add_class.diff_cancel cmod_eq_Re complex.sel(1) complex.sel(2) dist_norm m(2) minus_complex.code)
            moreover
            have "dist (Complex m (- ln (n + sqrt ((real n)\<^sup>2 - 1)) / pi)) (Complex m (Im b)) 
                = \<bar> - Im b - ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi\<bar>"
              by (simp add: complex_norm dist_norm cmod_eq_Re complex_diff)
            ultimately have "dist b (Complex m (- ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi)) < 1"
              using n by (simp add: dist_triangle_lt [of b "Complex m (Im b)"] dist_commute)
            with ge m \<open>0 < n\<close> show ?thesis
              by (rule_tac x = "Complex m (- ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi)" in bexI) auto
          qed
        qed
        show "g v \<notin> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (ln(n + sqrt(real n ^ 2 - 1)) / pi)}) \<union>
                    (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (-ln(n + sqrt(real n ^ 2 - 1)) / pi)})"
             if "v \<in> cball 0 1" for v
          using not01 [OF that]
          by (force simp: g [OF that, symmetric] h [OF that, symmetric] dest!: Schottky_lemma3 [of "g v"])
      qed
      then have 12: "(1 - t) * cmod (deriv g w) / 12 < 1"
        using Bloch_general [OF holg _ ttt, of 1] w by force
      have "g field_differentiable at w within cball 0 1"
        using holg w by (simp add: holomorphic_on_def)
      then have "g field_differentiable at w within ball 0 1"
        using ball_subset_cball field_differentiable_within_subset by blast
      with w have der_gw: "(g has_field_derivative deriv g w) (at w)"
        by (simp add: field_differentiable_within_open [of _ "ball 0 1"] field_differentiable_derivI)
      with DERIV_unique [OF der_gw] g' w have "deriv g w = g' w"
        by (metis open_ball at_within_open ball_subset_cball has_field_derivative_subset subsetCE)
      then show "cmod (g' w) \<le> 12 / (1 - t)"
        using g' 12 \<open>t < 1\<close> by (simp add: field_simps)
    qed
    then have "cmod (g z - g 0) \<le> 12 / (1 - t) * cmod z"
      using has_contour_integral_bound_linepath [OF int_g', of "12/(1 - t)"] assms
      by simp
    with \<open>cmod z \<le> t\<close> \<open>t < 1\<close> show ?thesis
      by (simp add: field_split_simps)
  qed
  have fz: "f z = (1 + cos(of_real pi * h z)) / 2"
    using h \<open>z \<in> ball 0 1\<close> by (auto simp: field_simps)
  have "cmod (f z) \<le> exp (cmod (complex_of_real pi * h z))"
    by (simp add: fz mult.commute norm_cos_plus1_le)
  also have "... \<le> exp (pi * exp (pi * (2 + 2 * r + 12 * t / (1 - t))))"
  proof (simp add: norm_mult)
    have "cmod (g z - g 0) \<le> 12 * t / (1 - t)"
      using norm_g_12 \<open>t < 1\<close> by (simp add: norm_mult)
    then have "cmod (g z) - cmod (g 0) \<le> 12 * t / (1 - t)"
      using norm_triangle_ineq2 order_trans by blast
    then have *: "cmod (g z) \<le> 2 + 2 * r + 12 * t / (1 - t)"
      using g0_2_f0 norm_ge_zero [of "f 0"] nof0
        by linarith
    have "cmod (h z) \<le> exp (cmod (complex_of_real pi * g z))"
      using \<open>z \<in> ball 0 1\<close> by (simp add: g norm_cos_le)
    also have "... \<le> exp (pi * (2 + 2 * r + 12 * t / (1 - t)))"
      using \<open>t < 1\<close> nof0 * by (simp add: norm_mult)
    finally show "cmod (h z) \<le> exp (pi * (2 + 2 * r + 12 * t / (1 - t)))" .
  qed
  finally show ?thesis .
qed

  
subsection\<open>The Little Picard Theorem\<close>

theorem Landau_Picard:
  obtains R
    where "\<And>z. 0 < R z"
          "\<And>f. \<lbrakk>f holomorphic_on cball 0 (R(f 0));
                 \<And>z. norm z \<le> R(f 0) \<Longrightarrow> f z \<noteq> 0 \<and> f z \<noteq> 1\<rbrakk> \<Longrightarrow> norm(deriv f 0) < 1"
proof -
  define R where "R \<equiv> \<lambda>z. 3 * exp(pi * exp(pi*(2 + 2 * cmod z + 12)))"
  show ?thesis
  proof
    show Rpos: "\<And>z. 0 < R z"
      by (auto simp: R_def)
    show "norm(deriv f 0) < 1"
         if holf: "f holomorphic_on cball 0 (R(f 0))"
         and Rf:  "\<And>z. norm z \<le> R(f 0) \<Longrightarrow> f z \<noteq> 0 \<and> f z \<noteq> 1" for f
    proof -
      let ?r = "R(f 0)"
      define g where "g \<equiv> f \<circ> (\<lambda>z. of_real ?r * z)"
      have "0 < ?r"
        using Rpos by blast
      have holg: "g holomorphic_on cball 0 1"
        unfolding g_def
      proof (intro holomorphic_intros holomorphic_on_compose holomorphic_on_subset [OF holf])
        show "(*) (complex_of_real (R (f 0))) ` cball 0 1 \<subseteq> cball 0 (R (f 0))"
          using Rpos by (auto simp: less_imp_le norm_mult)
      qed
      have *: "norm(g z) \<le> exp(pi * exp(pi * (2 + 2 * norm (f 0) + 12 * t / (1 - t))))"
           if "0 < t" "t < 1" "norm z \<le> t" for t z
      proof (rule Schottky [OF holg])
        show "cmod (g 0) \<le> cmod (f 0)"
          by (simp add: g_def)
        show "\<And>z. z \<in> cball 0 1 \<Longrightarrow> \<not> (g z = 0 \<or> g z = 1)"
          using Rpos by (simp add: g_def less_imp_le norm_mult Rf)
      qed (auto simp: that)
      have C1: "g holomorphic_on ball 0 (1/2)"
        by (rule holomorphic_on_subset [OF holg]) auto
      have C2: "continuous_on (cball 0 (1/2)) g"
        by (meson cball_divide_subset_numeral holg holomorphic_on_imp_continuous_on holomorphic_on_subset)
      have C3: "cmod (g z) \<le> R (f 0) / 3" if "cmod (0 - z) = 1/2" for z
      proof -
        have "norm(g z) \<le> exp(pi * exp(pi * (2 + 2 * norm (f 0) + 12)))"
          using * [of "1/2"] that by simp
        also have "... = ?r / 3"
          by (simp add: R_def)
        finally show ?thesis .
      qed
      then have cmod_g'_le: "cmod (deriv g 0) * 3 \<le> R (f 0) * 2"
        using Cauchy_inequality [OF C1 C2 _ C3, of 1] by simp
      have holf': "f holomorphic_on ball 0 (R(f 0))"
        by (rule holomorphic_on_subset [OF holf]) auto
      then have fd0: "f field_differentiable at 0"
        by (rule holomorphic_on_imp_differentiable_at [OF _ open_ball])
           (auto simp: Rpos [of "f 0"])
      have g_eq: "deriv g 0 = of_real ?r * deriv f 0"
        unfolding g_def
        by (metis DERIV_imp_deriv DERIV_chain DERIV_cmult_Id fd0 field_differentiable_derivI mult.commute mult_zero_right)
      show ?thesis
        using cmod_g'_le Rpos [of "f 0"]  by (simp add: g_eq norm_mult)
    qed
  qed
qed

lemma little_Picard_01:
  assumes holf: "f holomorphic_on UNIV" and f01: "\<And>z. f z \<noteq> 0 \<and> f z \<noteq> 1"
  obtains c where "f = (\<lambda>x. c)"
proof -
  obtain R
    where Rpos: "\<And>z. 0 < R z"
      and R:    "\<And>h. \<lbrakk>h holomorphic_on cball 0 (R(h 0));
                      \<And>z. norm z \<le> R(h 0) \<Longrightarrow> h z \<noteq> 0 \<and> h z \<noteq> 1\<rbrakk> \<Longrightarrow> norm(deriv h 0) < 1"
    using Landau_Picard by metis
  have contf: "continuous_on UNIV f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  show ?thesis
  proof (cases "\<forall>x. deriv f x = 0")
    case True
    have "(f has_field_derivative 0) (at x)" for x
      by (metis True UNIV_I holf holomorphic_derivI open_UNIV)
    then obtain c where "\<And>x. f(x) = c"
      by (meson UNIV_I DERIV_zero_connected_constant [OF connected_UNIV open_UNIV finite.emptyI contf])
    then show ?thesis
      using that by auto
  next
    case False
    then obtain w where w: "deriv f w \<noteq> 0" by auto
    define fw where "fw \<equiv> (f \<circ> (\<lambda>z. w + z / deriv f w))"
    have norm_let1: "norm(deriv fw 0) < 1"
    proof (rule R)
      show "fw holomorphic_on cball 0 (R (fw 0))"
        unfolding fw_def
        by (intro holomorphic_intros holomorphic_on_compose w holomorphic_on_subset [OF holf] subset_UNIV)
      show "fw z \<noteq> 0 \<and> fw z \<noteq> 1" if "cmod z \<le> R (fw 0)" for z
        using f01 by (simp add: fw_def)
    qed
    have "(fw has_field_derivative deriv f w * inverse (deriv f w)) (at 0)"
      unfolding fw_def
      apply (intro DERIV_chain derivative_eq_intros w)+
      using holf holomorphic_derivI by (force simp: field_simps)+
    then show ?thesis
      using norm_let1 w by (simp add: DERIV_imp_deriv)
  qed
qed


theorem little_Picard:
  assumes holf: "f holomorphic_on UNIV"
      and "a \<noteq> b" "range f \<inter> {a,b} = {}"
    obtains c where "f = (\<lambda>x. c)"
proof -
  let ?g = "\<lambda>x. 1/(b - a)*(f x - b) + 1"
  obtain c where "?g = (\<lambda>x. c)"
  proof (rule little_Picard_01)
    show "?g holomorphic_on UNIV"
      by (intro holomorphic_intros holf)
    show "\<And>z. ?g z \<noteq> 0 \<and> ?g z \<noteq> 1"
      using assms by (auto simp: field_simps)
  qed auto
  then have "?g x = c" for x
    by meson
  then have "f x = c * (b-a) + a" for x
    using assms by (auto simp: field_simps)
  then show ?thesis
    using that by blast
qed


text\<open>A couple of little applications of Little Picard\<close>

lemma holomorphic_periodic_fixpoint:
  assumes holf: "f holomorphic_on UNIV"
      and "p \<noteq> 0" and per: "\<And>z. f(z + p) = f z"
  obtains x where "f x = x"
proof -
  have False if non: "\<And>x. f x \<noteq> x"
  proof -
    obtain c where "(\<lambda>z. f z - z) = (\<lambda>z. c)"
    proof (rule little_Picard)
      show "(\<lambda>z. f z - z) holomorphic_on UNIV"
        by (simp add: holf holomorphic_on_diff)
      show "range (\<lambda>z. f z - z) \<inter> {p,0} = {}"
          using assms non by auto (metis add.commute diff_eq_eq)
      qed (auto simp: assms)
    with per show False
      by (metis add.commute add_cancel_left_left \<open>p \<noteq> 0\<close> diff_add_cancel)
  qed
  then show ?thesis
    using that by blast
qed


lemma holomorphic_involution_point:
  assumes holfU: "f holomorphic_on UNIV" and non: "\<And>a. f \<noteq> (\<lambda>x. a + x)"
  obtains x where "f(f x) = x"
proof -
  { assume non_ff [simp]: "\<And>x. f(f x) \<noteq> x"
    then have non_fp [simp]: "f z \<noteq> z" for z
      by metis
    have holf: "f holomorphic_on X" for X
      using assms holomorphic_on_subset by blast
    obtain c where c: "(\<lambda>x. (f(f x) - x)/(f x - x)) = (\<lambda>x. c)"
    proof (rule little_Picard_01)
      show "(\<lambda>x. (f(f x) - x)/(f x - x)) holomorphic_on UNIV"
        using non_fp
        by (intro holomorphic_intros holf holomorphic_on_compose [unfolded o_def, OF holf]) auto
    qed auto
    then obtain "c \<noteq> 0" "c \<noteq> 1"
      by (metis (no_types, opaque_lifting) non_ff diff_zero divide_eq_0_iff right_inverse_eq)
    have eq: "f(f x) - c * f x = x*(1 - c)" for x
      using fun_cong [OF c, of x] by (simp add: field_simps)
    have df_times_dff: "deriv f z * (deriv f (f z) - c) = 1 * (1 - c)" for z
    proof (rule DERIV_unique)
      show "((\<lambda>x. f (f x) - c * f x) has_field_derivative
              deriv f z * (deriv f (f z) - c)) (at z)"
        by (rule derivative_eq_intros holomorphic_derivI [OF holfU] 
                    DERIV_chain [unfolded o_def, where f=f and g=f] | simp add: algebra_simps)+
      show "((\<lambda>x. f (f x) - c * f x) has_field_derivative 1 * (1 - c)) (at z)"
        by (simp add: eq mult_commute_abs)
    qed
    { fix z::complex
      obtain k where k: "deriv f \<circ> f = (\<lambda>x. k)"
      proof (rule little_Picard)
        show "(deriv f \<circ> f) holomorphic_on UNIV"
          by (meson holfU holomorphic_deriv holomorphic_on_compose holomorphic_on_subset open_UNIV subset_UNIV)
        obtain "deriv f (f x) \<noteq> 0" "deriv f (f x) \<noteq> c"  for x
          using df_times_dff \<open>c \<noteq> 1\<close> eq_iff_diff_eq_0
          by (metis lambda_one mult_zero_left mult_zero_right)
        then show "range (deriv f \<circ> f) \<inter> {0,c} = {}"
          by force
      qed (use \<open>c \<noteq> 0\<close> in auto)
      have "\<not> f constant_on UNIV"
        by (meson UNIV_I non_ff constant_on_def)
      with holf open_mapping_thm have "open(range f)"
        by blast
      obtain l where l: "\<And>x. f x - k * x = l"
      proof (rule DERIV_zero_connected_constant [of UNIV "{}" "\<lambda>x. f x - k * x"], simp_all)
        have "deriv f w - k = 0" for w
        proof (rule analytic_continuation [OF _ open_UNIV connected_UNIV subset_UNIV, of "\<lambda>z. deriv f z - k" "f z" "range f" w])
          show "(\<lambda>z. deriv f z - k) holomorphic_on UNIV"
            by (intro holomorphic_intros holf open_UNIV)
          show "f z islimpt range f"
            by (metis (no_types, lifting) IntI UNIV_I \<open>open (range f)\<close> image_eqI inf.absorb_iff2 inf_aci(1) islimpt_UNIV islimpt_eq_acc_point open_Int top_greatest)
          show "\<And>z. z \<in> range f \<Longrightarrow> deriv f z - k = 0"
            by (metis comp_def diff_self image_iff k)
        qed auto
        moreover
        have "((\<lambda>x. f x - k * x) has_field_derivative deriv f x - k) (at x)" for x
          by (metis DERIV_cmult_Id Deriv.field_differentiable_diff UNIV_I field_differentiable_derivI holf holomorphic_on_def)
        ultimately
        show "\<forall>x. ((\<lambda>x. f x - k * x) has_field_derivative 0) (at x)"
          by auto
        show "continuous_on UNIV (\<lambda>x. f x - k * x)"
          by (simp add: continuous_on_diff holf holomorphic_on_imp_continuous_on)
      qed (auto simp: connected_UNIV)
      have False
      proof (cases "k=1")
        case True
        then have "\<exists>x. k * x + l \<noteq> a + x" for a
          using l non [of a] ext [of f "(+) a"]
          by (metis add.commute diff_eq_eq)
        with True show ?thesis by auto
      next
        case False
        have "\<And>x. (1 - k) * x \<noteq> f 0"
          using l [of 0]
          by (simp add: algebra_simps) (metis diff_add_cancel l mult.commute non_fp)
        then show False
          by (metis False eq_iff_diff_eq_0 mult.commute nonzero_mult_div_cancel_right times_divide_eq_right)
      qed
    }
  }
  then show thesis
    using that by blast
qed


subsection\<open>The Arzelà--Ascoli theorem\<close>

lemma subsequence_diagonalization_lemma:
  fixes P :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes sub: "\<And>i r. \<exists>k. strict_mono (k :: nat \<Rightarrow> nat) \<and> P i (r \<circ> k)"
      and P_P:  "\<And>i r::nat \<Rightarrow> 'a. \<And>k1 k2 N.
                   \<lbrakk>P i (r \<circ> k1); \<And>j. N \<le> j \<Longrightarrow> \<exists>j'. j \<le> j' \<and> k2 j = k1 j'\<rbrakk> \<Longrightarrow> P i (r \<circ> k2)"
   obtains k where "strict_mono (k :: nat \<Rightarrow> nat)" "\<And>i. P i (r \<circ> k)"
proof -
  obtain kk where "\<And>i r. strict_mono (kk i r :: nat \<Rightarrow> nat) \<and> P i (r \<circ> (kk i r))"
    using sub by metis
  then have sub_kk: "\<And>i r. strict_mono (kk i r)" and P_kk: "\<And>i r. P i (r \<circ> (kk i r))"
    by auto
  define rr where "rr \<equiv> rec_nat (kk 0 r) (\<lambda>n x. x \<circ> kk (Suc n) (r \<circ> x))"
  then have [simp]: "rr 0 = kk 0 r" "\<And>n. rr(Suc n) = rr n \<circ> kk (Suc n) (r \<circ> rr n)"
    by auto
  show thesis
  proof
    have sub_rr: "strict_mono (rr i)" for i
      using sub_kk  by (induction i) (auto simp: strict_mono_def o_def)
    have P_rr: "P i (r \<circ> rr i)" for i
      using P_kk  by (induction i) (auto simp: o_def)
    have "i \<le> i+d \<Longrightarrow> rr i n \<le> rr (i+d) n" for d i n
    proof (induction d)
      case 0 then show ?case
        by simp
    next
      case (Suc d) then show ?case
        using seq_suble [OF sub_kk] strict_mono_less_eq [OF sub_rr]
        by (simp add: order_subst1)
    qed
    then have "\<And>i j n. i \<le> j \<Longrightarrow> rr i n \<le> rr j n"
      by (metis le_iff_add)
    show "strict_mono (\<lambda>n. rr n n)"
      unfolding strict_mono_Suc_iff
      by (simp add: Suc_le_lessD strict_monoD strict_mono_imp_increasing sub_kk sub_rr)
    have "\<exists>j. i \<le> j \<and> rr (n+d) i = rr n j" for d n i
    proof (induction d arbitrary: i)
      case (Suc d)
      then show ?case
        using seq_suble [OF sub_kk] by simp (meson order_trans)
    qed auto
    then have "\<And>m n i. n \<le> m \<Longrightarrow> \<exists>j. i \<le> j \<and> rr m i = rr n j"
      by (metis le_iff_add)
    then show "P i (r \<circ> (\<lambda>n. rr n n))" for i
      by (meson P_rr P_P)
  qed
qed

lemma function_convergent_subsequence:
  fixes f :: "[nat,'a] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "countable S" and M: "\<And>n::nat. \<And>x. x \<in> S \<Longrightarrow> norm(f n x) \<le> M"
   obtains k where "strict_mono (k::nat\<Rightarrow>nat)" "\<And>x. x \<in> S \<Longrightarrow> \<exists>l. (\<lambda>n. f (k n) x) \<longlonglongrightarrow> l"
proof (cases "S = {}")
  case True
  then show ?thesis
    using strict_mono_id that by fastforce
next
  case False
  with \<open>countable S\<close> obtain \<sigma> :: "nat \<Rightarrow> 'a" where \<sigma>: "S = range \<sigma>"
    using uncountable_def by blast
  obtain k where "strict_mono k" and k: "\<And>i. \<exists>l. (\<lambda>n. (f \<circ> k) n (\<sigma> i)) \<longlonglongrightarrow> l"
  proof (rule subsequence_diagonalization_lemma
      [of "\<lambda>i r. \<exists>l. ((\<lambda>n. (f \<circ> r) n (\<sigma> i)) \<longlongrightarrow> l) sequentially" id])
    show "\<exists>k::nat\<Rightarrow>nat. strict_mono k \<and> (\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k)) n (\<sigma> i)) \<longlonglongrightarrow> l)" for i r
    proof -
      have "f (r n) (\<sigma> i) \<in> cball 0 M" for n
        by (simp add: \<sigma> M)
      then show ?thesis
        using compact_def [of "cball (0::'b) M"] by (force simp: o_def)
    qed
    show "\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k2)) n (\<sigma> i)) \<longlonglongrightarrow> l" 
      if "\<exists>l. (\<lambda>n. (f \<circ> (r \<circ> k1)) n (\<sigma> i)) \<longlonglongrightarrow> l" "\<And>j. N \<le> j \<Longrightarrow> \<exists>j'\<ge>j. k2 j = k1 j'"
      for i N and r k1 k2 :: "nat\<Rightarrow>nat"
      using that
      by (simp add: lim_sequentially) (metis (no_types, opaque_lifting) le_cases order_trans)
  qed auto
  with \<sigma> that show ?thesis
    by force
qed


theorem Arzela_Ascoli:
  fixes \<F> :: "[nat,'a::euclidean_space] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "compact S"
      and M: "\<And>n x. x \<in> S \<Longrightarrow> norm(\<F> n x) \<le> M"
      and equicont:
          "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>n y. y \<in> S \<and> norm(x - y) < d \<longrightarrow> norm(\<F> n x - \<F> n y) < e)"
  obtains g k where "continuous_on S g" "strict_mono (k :: nat \<Rightarrow> nat)"
                    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<and> x \<in> S \<longrightarrow> norm(\<F>(k n) x - g x) < e"
proof -
  have UEQ: "\<And>e. 0 < e \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>n. \<forall>x \<in> S. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (\<F> n x') (\<F> n x) < e)"
    apply (rule compact_uniformly_equicontinuous [OF \<open>compact S\<close>, of "range \<F>"])
    using equicont by (force simp: dist_commute dist_norm)+
  have "continuous_on S g"
       if "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<and> x \<in> S \<longrightarrow> norm(\<F>(r n) x - g x) < e"
       for g:: "'a \<Rightarrow> 'b" and r :: "nat \<Rightarrow> nat"
  proof (rule uniform_limit_theorem [of _ "\<F> \<circ> r"])
    have "continuous_on S (\<F> (r n))" for n
      using UEQ by (force simp: continuous_on_iff)
    then show "\<forall>\<^sub>F n in sequentially. continuous_on S ((\<F> \<circ> r) n)"
      by (simp add: eventually_sequentially)
    show "uniform_limit S (\<F> \<circ> r) g sequentially"
      using that by (metis (mono_tags, opaque_lifting) comp_apply dist_norm uniform_limit_sequentially_iff)
  qed auto
  moreover
  obtain R where "countable R" "R \<subseteq> S" and SR: "S \<subseteq> closure R"
    by (metis separable that)
  obtain k where "strict_mono k" and k: "\<And>x. x \<in> R \<Longrightarrow> \<exists>l. (\<lambda>n. \<F> (k n) x) \<longlonglongrightarrow> l"
    using \<open>R \<subseteq> S\<close> by (force intro: function_convergent_subsequence [OF \<open>countable R\<close> M])
  then have Cauchy: "Cauchy ((\<lambda>n. \<F> (k n) x))" if "x \<in> R" for x
    using convergent_eq_Cauchy that by blast
  have "\<exists>N. \<forall>m n x. N \<le> m \<and> N \<le> n \<and> x \<in> S \<longrightarrow> dist ((\<F> \<circ> k) m x) ((\<F> \<circ> k) n x) < e"
    if "0 < e" for e
  proof -
    obtain d where "0 < d"
      and d: "\<And>n. \<forall>x \<in> S. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (\<F> n x') (\<F> n x) < e/3"
      by (metis UEQ \<open>0 < e\<close> divide_pos_pos zero_less_numeral)
    obtain T where "T \<subseteq> R" and "finite T" and T: "S \<subseteq> (\<Union>c\<in>T. ball c d)"
    proof (rule compactE_image [OF  \<open>compact S\<close>, of R "(\<lambda>x. ball x d)"])
      have "closure R \<subseteq> (\<Union>c\<in>R. ball c d)"
        using \<open>0 < d\<close> by (auto simp: closure_approachable)
      with SR show "S \<subseteq> (\<Union>c\<in>R. ball c d)"
        by auto
    qed auto
    have "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (\<F> (k m) x) (\<F> (k n) x) < e/3" if "x \<in> R" for x
      using Cauchy \<open>0 < e\<close> that unfolding Cauchy_def
      by (metis less_divide_eq_numeral1(1) mult_zero_left)
    then obtain MF where MF: "\<And>x m n. \<lbrakk>x \<in> R; m \<ge> MF x; n \<ge> MF x\<rbrakk> \<Longrightarrow> norm (\<F> (k m) x - \<F> (k n) x) < e/3"
      using dist_norm by metis
    have "dist ((\<F> \<circ> k) m x) ((\<F> \<circ> k) n x) < e"
         if m: "Max (MF ` T) \<le> m" and n: "Max (MF ` T) \<le> n" "x \<in> S" for m n x
    proof -
      obtain t where "t \<in> T" and t: "x \<in> ball t d"
        using \<open>x \<in> S\<close> T by auto
      have "norm(\<F> (k m) t - \<F> (k m) x) < e / 3"
        by (metis \<open>R \<subseteq> S\<close> \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> d dist_norm mem_ball subset_iff t \<open>x \<in> S\<close>)
      moreover
      have "norm(\<F> (k n) t - \<F> (k n) x) < e / 3"
        by (metis \<open>R \<subseteq> S\<close> \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> subsetD d dist_norm mem_ball t \<open>x \<in> S\<close>)
      moreover
      have "norm(\<F> (k m) t - \<F> (k n) t) < e / 3"
      proof (rule MF)
        show "t \<in> R"
          using \<open>T \<subseteq> R\<close> \<open>t \<in> T\<close> by blast
        show "MF t \<le> m" "MF t \<le> n"
          by (meson Max_ge \<open>finite T\<close> \<open>t \<in> T\<close> finite_imageI imageI le_trans m n)+
      qed
      ultimately
      show ?thesis
        unfolding dist_norm [symmetric] o_def
          by (metis dist_triangle_third dist_commute)
    qed
    then show ?thesis
      by force
  qed
  then obtain g where "\<forall>e>0. \<exists>N. \<forall>n x. N \<le> n \<and> x \<in> S \<longrightarrow> norm ((\<F> \<circ> k) n x - g x) < e"
    using uniformly_convergent_eq_cauchy [of "\<lambda>x. x \<in> S" "\<F> \<circ> k"] by (auto simp add: dist_norm)
  ultimately show thesis
    by (metis \<open>strict_mono k\<close> comp_apply that)
qed



subsubsection\<^marker>\<open>tag important\<close>\<open>Montel's theorem\<close>

text\<open>a sequence of holomorphic functions uniformly bounded
on compact subsets of an open set S has a subsequence that converges to a
holomorphic function, and converges \emph{uniformly} on compact subsets of S.\<close>


theorem Montel:
  fixes \<F> :: "[nat,complex] \<Rightarrow> complex"
  assumes "open S"
      and \<H>: "\<And>h. h \<in> \<H> \<Longrightarrow> h holomorphic_on S"
      and bounded: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>B. \<forall>h \<in> \<H>. \<forall> z \<in> K. norm(h z) \<le> B"
      and rng_f: "range \<F> \<subseteq> \<H>"
  obtains g r
    where "g holomorphic_on S" "strict_mono (r :: nat \<Rightarrow> nat)"
          "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>n. \<F> (r n) x) \<longlongrightarrow> g x) sequentially"
          "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K (\<F> \<circ> r) g sequentially"        
proof -
  obtain K where comK: "\<And>n. compact(K n)" and KS: "\<And>n::nat. K n \<subseteq> S"
             and subK: "\<And>X. \<lbrakk>compact X; X \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. X \<subseteq> K n"
    using open_Union_compact_subsets [OF \<open>open S\<close>] by metis
  then have "\<And>i. \<exists>B. \<forall>h \<in> \<H>. \<forall> z \<in> K i. norm(h z) \<le> B"
    by (simp add: bounded)
  then obtain B where B: "\<And>i h z. \<lbrakk>h \<in> \<H>; z \<in> K i\<rbrakk> \<Longrightarrow> norm(h z) \<le> B i"
    by metis
  have *: "\<exists>r g. strict_mono (r::nat\<Rightarrow>nat) \<and> (\<forall>e > 0. \<exists>N. \<forall>n\<ge>N. \<forall>x \<in> K i. norm((\<F> \<circ> r) n x - g x) < e)"
        if "\<And>n. \<F> n \<in> \<H>" for \<F> i
  proof -
    obtain g k where "continuous_on (K i) g" "strict_mono (k::nat\<Rightarrow>nat)"
                    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x \<in> K i. norm(\<F>(k n) x - g x) < e"
    proof (rule Arzela_Ascoli [of "K i" "\<F>" "B i"])
      show "\<exists>d>0. \<forall>n y. y \<in> K i \<and> cmod (z - y) < d \<longrightarrow> cmod (\<F> n z - \<F> n y) < e"
             if z: "z \<in> K i" and "0 < e" for z e
      proof -
        obtain r where "0 < r" and r: "cball z r \<subseteq> S"
          using z KS [of i] \<open>open S\<close> by (force simp: open_contains_cball)
        have "cball z (2/3 * r) \<subseteq> cball z r"
          using \<open>0 < r\<close> by (simp add: cball_subset_cball_iff)
        then have z23S: "cball z (2/3 * r) \<subseteq> S"
          using r by blast
        obtain M where "0 < M" and M: "\<And>n w. dist z w \<le> 2/3 * r \<Longrightarrow> norm(\<F> n w) \<le> M"
        proof -
          obtain N where N: "\<forall>n\<ge>N. cball z (2/3 * r) \<subseteq> K n"
            using subK compact_cball [of z "(2/3 * r)"] z23S by force
          have "cmod (\<F> n w) \<le> \<bar>B N\<bar> + 1" if "dist z w \<le> 2/3 * r" for n w
          proof -
            have "w \<in> K N"
              using N mem_cball that by blast
            then have "cmod (\<F> n w) \<le> B N"
              using B \<open>\<And>n. \<F> n \<in> \<H>\<close> by blast
            also have "... \<le> \<bar>B N\<bar> + 1"
              by simp
            finally show ?thesis .
          qed
          then show ?thesis
            by (rule_tac M="\<bar>B N\<bar> + 1" in that) auto
        qed
        have "cmod (\<F> n z - \<F> n y) < e"
              if "y \<in> K i" and y_near_z: "cmod (z - y) < r/3" "cmod (z - y) < e * r / (6 * M)"
              for n y
        proof -
          have "((\<lambda>w. \<F> n w / (w - \<xi>)) has_contour_integral
                    (2 * pi) * \<i> * winding_number (circlepath z (2/3 * r)) \<xi> * \<F> n \<xi>)
                (circlepath z (2/3 * r))"
             if "dist \<xi> z < (2/3 * r)" for \<xi>
          proof (rule Cauchy_integral_formula_convex_simple)
            have "\<F> n holomorphic_on S"
              by (simp add: \<H> \<open>\<And>n. \<F> n \<in> \<H>\<close>)
            with z23S show "\<F> n holomorphic_on cball z (2/3 * r)"
              using holomorphic_on_subset by blast
          qed (use that \<open>0 < r\<close> in \<open>auto simp: dist_commute\<close>)
          then have *: "((\<lambda>w. \<F> n w / (w - \<xi>)) has_contour_integral (2 * pi) * \<i> * \<F> n \<xi>)
                     (circlepath z (2/3 * r))"
             if "dist \<xi> z < (2/3 * r)" for \<xi>
            using that by (simp add: winding_number_circlepath dist_norm)
           have y: "((\<lambda>w. \<F> n w / (w - y)) has_contour_integral (2 * pi) * \<i> * \<F> n y)
                    (circlepath z (2/3 * r))"
           proof (rule *)
             show "dist y z < 2/3 * r"
               using that \<open>0 < r\<close> by (simp only: dist_norm norm_minus_commute)
           qed
           have z: "((\<lambda>w. \<F> n w / (w - z)) has_contour_integral (2 * pi) * \<i> * \<F> n z)
                 (circlepath z (2/3 * r))"
             using \<open>0 < r\<close> by (force intro!: *)
           have le_er: "cmod (\<F> n x / (x - y) - \<F> n x / (x - z)) \<le> e / r"
                if "cmod (x - z) = r/3 + r/3" for x
           proof -
             have "\<not> (cmod (x - y) < r/3)"
               using y_near_z(1) that \<open>M > 0\<close> \<open>r > 0\<close>
               by (metis (full_types) norm_diff_triangle_less norm_minus_commute order_less_irrefl)
             then have r4_le_xy: "r/4 \<le> cmod (x - y)"
               using \<open>r > 0\<close> by simp
             then have neq: "x \<noteq> y" "x \<noteq> z"
               using that \<open>r > 0\<close> by (auto simp: field_split_simps norm_minus_commute)
             have leM: "cmod (\<F> n x) \<le> M"
               by (simp add: M dist_commute dist_norm that)
             have "cmod (\<F> n x / (x - y) - \<F> n x / (x - z)) = cmod (\<F> n x) * cmod (1 / (x - y) - 1 / (x - z))"
               by (metis (no_types, lifting) divide_inverse mult.left_neutral norm_mult right_diff_distrib')
             also have "... = cmod (\<F> n x) * cmod ((y - z) / ((x - y) * (x - z)))"
               using neq by (simp add: field_split_simps)
             also have "... = cmod (\<F> n x) * (cmod (y - z) / (cmod(x - y) * (2/3 * r)))"
               by (simp add: norm_mult norm_divide that)
             also have "... \<le> M * (cmod (y - z) / (cmod(x - y) * (2/3 * r)))"
               using \<open>r > 0\<close> \<open>M > 0\<close> by (intro mult_mono [OF leM]) auto
             also have "... < M * ((e * r / (6 * M)) / (cmod(x - y) * (2/3 * r)))"
               unfolding mult_less_cancel_left
               using y_near_z(2) \<open>M > 0\<close> \<open>r > 0\<close> neq
               by (simp add: field_simps mult_less_0_iff norm_minus_commute)
             also have "... \<le> e/r"
               using \<open>e > 0\<close> \<open>r > 0\<close> r4_le_xy by (simp add: field_split_simps)
             finally show ?thesis by simp
           qed
           have "(2 * pi) * cmod (\<F> n y - \<F> n z) = cmod ((2 * pi) * \<i> * \<F> n y - (2 * pi) * \<i> * \<F> n z)"
             by (simp add: right_diff_distrib [symmetric] norm_mult)
           also have "cmod ((2 * pi) * \<i> * \<F> n y - (2 * pi) * \<i> * \<F> n z) \<le> e / r * (2 * pi * (2/3 * r))"

           proof (rule has_contour_integral_bound_circlepath [OF has_contour_integral_diff [OF y z]])
             show "\<And>x. cmod (x - z) = 2/3 * r \<Longrightarrow> cmod (\<F> n x / (x - y) - \<F> n x / (x - z)) \<le> e / r"
               using le_er by auto
           qed (use \<open>e > 0\<close> \<open>r > 0\<close> in auto)
           also have "... = (2 * pi) * e * ((2/3))"
             using \<open>r > 0\<close> by (simp add: field_split_simps)
           finally have "cmod (\<F> n y - \<F> n z) \<le> e * (2/3)"
             by simp
           also have "... < e"
             using \<open>e > 0\<close> by simp
           finally show ?thesis by (simp add: norm_minus_commute)
        qed
        then show ?thesis
          apply (rule_tac x="min (r/3) ((e * r)/(6 * M))" in exI)
          using \<open>0 < e\<close> \<open>0 < r\<close> \<open>0 < M\<close> by simp
      qed
      show "\<And>n x.  x \<in> K i \<Longrightarrow> cmod (\<F> n x) \<le> B i"
        using B \<open>\<And>n. \<F> n \<in> \<H>\<close> by blast
    next
      fix g :: "complex \<Rightarrow> complex" and k :: "nat \<Rightarrow> nat"
      assume *: "\<And>(g::complex\<Rightarrow>complex) (k::nat\<Rightarrow>nat). continuous_on (K i) g \<Longrightarrow>
                  strict_mono k \<Longrightarrow>
                  (\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>K i. cmod (\<F> (k n) x - g x) < e) \<Longrightarrow> thesis"
           "continuous_on (K i) g"
           "strict_mono k"
           "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. N \<le> n \<and> x \<in> K i \<longrightarrow> cmod (\<F> (k n) x - g x) < e"
      show ?thesis
        by (rule *(1)[OF *(2,3)], drule *(4)) auto
    qed (use comK in simp_all)
    then show ?thesis
      by auto
  qed
  define \<Phi> where "\<Phi> \<equiv> \<lambda>g i r. \<lambda>k::nat\<Rightarrow>nat. \<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>K i. cmod ((\<F> \<circ> (r \<circ> k)) n x - g x) < e"
  obtain k :: "nat \<Rightarrow> nat" where "strict_mono k" and k: "\<And>i. \<exists>g. \<Phi> g i id k"
  proof (rule subsequence_diagonalization_lemma [where r=id])
    show "\<exists>g. \<Phi> g i id (r \<circ> k2)" 
      if ex: "\<exists>g. \<Phi> g i id (r \<circ> k1)" and "\<And>j. N \<le> j \<Longrightarrow> \<exists>j'\<ge>j. k2 j = k1 j'" 
      for i k1 k2 N and r::"nat\<Rightarrow>nat"
    proof -
      obtain g where "\<Phi> g i id (r \<circ> k1)"
        using ex by blast
      then have "\<Phi> g i id (r \<circ> k2)"
        using that
        by (simp add: \<Phi>_def) (metis (no_types, opaque_lifting) le_trans linear)
      then show ?thesis
        by metis
    qed
    have "\<exists>k g. strict_mono (k::nat\<Rightarrow>nat) \<and> \<Phi> g i id (r \<circ> k)" for i r
      unfolding \<Phi>_def o_assoc using rng_f by (force intro!: *)
    then show "\<And>i r. \<exists>k. strict_mono (k::nat\<Rightarrow>nat) \<and> (\<exists>g. \<Phi> g i id (r \<circ> k))"
      by force
  qed fastforce
  have "\<exists>l. \<forall>e>0. \<exists>N. \<forall>n\<ge>N. norm(\<F> (k n) z - l) < e" if "z \<in> S" for z
  proof -
    obtain G where G: "\<And>i e. e > 0 \<Longrightarrow> \<exists>M. \<forall>n\<ge>M. \<forall>x\<in>K i. cmod ((\<F> \<circ> k) n x - G i x) < e"
      using k unfolding \<Phi>_def by (metis id_comp)
    obtain N where "\<And>n. n \<ge> N \<Longrightarrow> z \<in> K n"
      using subK [of "{z}"] that \<open>z \<in> S\<close> by auto
    moreover have "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>n\<ge>M. \<forall>x\<in>K N. cmod ((\<F> \<circ> k) n x - G N x) < e"
      using G by auto
    ultimately show ?thesis
      by (metis comp_apply order_refl)
  qed
  then obtain g where g: "\<And>z e. \<lbrakk>z \<in> S; e > 0\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. norm(\<F> (k n) z - g z) < e"
    by metis
  show ?thesis
  proof
    show g_lim: "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>n. \<F> (k n) x) \<longlonglongrightarrow> g x"
      by (simp add: lim_sequentially g dist_norm)    
    have dg_le_e: "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>T. cmod (\<F> (k n) x - g x) < e"
      if T: "compact T" "T \<subseteq> S" and "0 < e" for T e
    proof -
      obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> T \<subseteq> K n"
        using subK [OF T] by blast
      obtain h where h: "\<And>e. e>0 \<Longrightarrow> \<exists>M. \<forall>n\<ge>M. \<forall>x\<in>K N. cmod ((\<F> \<circ> k) n x - h x) < e"
        using k unfolding \<Phi>_def by (metis id_comp)
      have geq: "g w = h w" if "w \<in> T" for w
      proof (rule LIMSEQ_unique)
        show "(\<lambda>n. \<F> (k n) w) \<longlonglongrightarrow> g w"
          using \<open>T \<subseteq> S\<close> g_lim that by blast
        show "(\<lambda>n. \<F> (k n) w) \<longlonglongrightarrow> h w"
          using h N that by (force simp: lim_sequentially dist_norm)
      qed
      show ?thesis
        using T h N \<open>0 < e\<close> by (fastforce simp add: geq)
    qed
    then show "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk>
         \<Longrightarrow> uniform_limit K (\<F> \<circ> k) g sequentially"
      by (simp add: uniform_limit_iff dist_norm eventually_sequentially)
    show "g holomorphic_on S"
    proof (rule holomorphic_uniform_sequence [OF \<open>open S\<close> \<H>])
      show "\<And>n. (\<F> \<circ> k) n \<in> \<H>"
        by (simp add: range_subsetD rng_f)
      show "\<exists>d>0. cball z d \<subseteq> S \<and> uniform_limit (cball z d) (\<lambda>n. (\<F> \<circ> k) n) g sequentially"
        if "z \<in> S" for z
      proof -
        obtain d where d: "d>0" "cball z d \<subseteq> S"
          using \<open>open S\<close> \<open>z \<in> S\<close> open_contains_cball by blast
        then have "uniform_limit (cball z d) (\<F> \<circ> k) g sequentially"
          using dg_le_e compact_cball by (auto simp: uniform_limit_iff eventually_sequentially dist_norm)
        with d show ?thesis by blast
      qed
    qed
  qed (auto simp: \<open>strict_mono k\<close>)
qed



subsection\<open>Some simple but useful cases of Hurwitz's theorem\<close>

proposition Hurwitz_no_zeros:
  assumes S: "open S" "connected S"
      and holf: "\<And>n::nat. \<F> n holomorphic_on S"
      and holg: "g holomorphic_on S"
      and ul_g: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K \<F> g sequentially"
      and nonconst: "\<not> g constant_on S"
      and nz: "\<And>n z. z \<in> S \<Longrightarrow> \<F> n z \<noteq> 0"
      and "z0 \<in> S"
      shows "g z0 \<noteq> 0"
proof
  assume g0: "g z0 = 0"
  obtain h r m
    where "0 < m" "0 < r" and subS: "ball z0 r \<subseteq> S"
      and holh: "h holomorphic_on ball z0 r"
      and geq:  "\<And>w. w \<in> ball z0 r \<Longrightarrow> g w = (w - z0)^m * h w"
      and hnz:  "\<And>w. w \<in> ball z0 r \<Longrightarrow> h w \<noteq> 0"
    by (blast intro: holomorphic_factor_zero_nonconstant [OF holg S \<open>z0 \<in> S\<close> g0 nonconst])
  then have holf0: "\<F> n holomorphic_on ball z0 r" for n
    by (meson holf holomorphic_on_subset)
  have *: "((\<lambda>z. deriv (\<F> n) z / \<F> n z) has_contour_integral 0) (circlepath z0 (r/2))" for n
  proof (rule Cauchy_theorem_disc_simple)
    show "(\<lambda>z. deriv (\<F> n) z / \<F> n z) holomorphic_on ball z0 r"
      by (metis (no_types) \<open>open S\<close> holf holomorphic_deriv holomorphic_on_divide holomorphic_on_subset nz subS)
  qed (use \<open>0 < r\<close> in auto)
  have hol_dg: "deriv g holomorphic_on S"
    by (simp add: \<open>open S\<close> holg holomorphic_deriv)
  have "continuous_on (sphere z0 (r/2)) (deriv g)"
    using \<open>0 < r\<close> subS 
    by (intro holomorphic_on_imp_continuous_on holomorphic_on_subset [OF hol_dg]) auto
  then have "compact (deriv g ` (sphere z0 (r/2)))"
    by (rule compact_continuous_image [OF _ compact_sphere])
  then have bo_dg: "bounded (deriv g ` (sphere z0 (r/2)))"
    using compact_imp_bounded by blast
  have "continuous_on (sphere z0 (r/2)) (cmod \<circ> g)"
    using \<open>0 < r\<close> subS 
    by (intro continuous_intros holomorphic_on_imp_continuous_on holomorphic_on_subset [OF holg]) auto
  then have "compact ((cmod \<circ> g) ` sphere z0 (r/2))"
    by (rule compact_continuous_image [OF _ compact_sphere])
  moreover have "(cmod \<circ> g) ` sphere z0 (r/2) \<noteq> {}"
    using \<open>0 < r\<close> by auto
  ultimately obtain b where b: "b \<in> (cmod \<circ> g) ` sphere z0 (r/2)"
                               "\<And>t. t \<in> (cmod \<circ> g) ` sphere z0 (r/2) \<Longrightarrow> b \<le> t"
    using compact_attains_inf [of "(norm \<circ> g) ` (sphere z0 (r/2))"] by blast
  have "(\<lambda>n. contour_integral (circlepath z0 (r/2)) (\<lambda>z. deriv (\<F> n) z / \<F> n z)) \<longlonglongrightarrow>
        contour_integral (circlepath z0 (r/2)) (\<lambda>z. deriv g z / g z)"
  proof (rule contour_integral_uniform_limit_circlepath)
    show "\<forall>\<^sub>F n in sequentially. (\<lambda>z. deriv (\<F> n) z / \<F> n z) contour_integrable_on circlepath z0 (r/2)"
      using * contour_integrable_on_def eventually_sequentiallyI by meson
    show "uniform_limit (sphere z0 (r/2)) (\<lambda>n z. deriv (\<F> n) z / \<F> n z) (\<lambda>z. deriv g z / g z) sequentially"
    proof (rule uniform_lim_divide [OF _ _ bo_dg])
      show "uniform_limit (sphere z0 (r/2)) (\<lambda>a. deriv (\<F> a)) (deriv g) sequentially"
      proof (rule uniform_limitI)
        fix e::real
        assume "0 < e"

        show "\<forall>\<^sub>F n in sequentially. \<forall>x \<in> sphere z0 (r/2). dist (deriv (\<F> n) x) (deriv g x) < e"
        proof -
          have "dist (deriv (\<F> n) w) (deriv g w) < e"
            if e8: "\<And>x. dist z0 x \<le> 3 * r / 4 \<Longrightarrow> dist (\<F> n x) (g x) * 8 < r * e"
              and w: "w \<in> sphere z0 (r/2)"  for n w
          proof -
            have "ball w (r/4) \<subseteq> ball z0 r"  "cball w (r/4) \<subseteq> ball z0 r"
              using \<open>0 < r\<close> w by (simp_all add: ball_subset_ball_iff cball_subset_ball_iff dist_commute)
            with subS have wr4_sub: "ball w (r/4) \<subseteq> S" "cball w (r/4) \<subseteq> S" by force+
            moreover
            have "(\<lambda>z. \<F> n z - g z) holomorphic_on S"
              by (intro holomorphic_intros holf holg)
            ultimately have hol: "(\<lambda>z. \<F> n z - g z) holomorphic_on ball w (r/4)"
              and cont: "continuous_on (cball w (r / 4)) (\<lambda>z. \<F> n z - g z)"
              using holomorphic_on_subset by (blast intro: holomorphic_on_imp_continuous_on)+
            have "w \<in> S"
              using \<open>0 < r\<close> wr4_sub by auto
            have "dist z0 y \<le> 3 * r / 4" if "dist w y < r/4" for y
            proof (rule dist_triangle_le [where z=w])
              show "dist z0 w + dist y w \<le> 3 * r / 4"
                using w that by (simp add: dist_commute)
            qed
            with e8 have in_ball: "\<And>y. y \<in> ball w (r/4) \<Longrightarrow> \<F> n y - g y \<in> ball 0 (r/4 * e/2)"
              by (simp add: dist_norm [symmetric])
            have "\<F> n field_differentiable at w"
              by (metis holomorphic_on_imp_differentiable_at \<open>w \<in> S\<close> holf \<open>open S\<close>)
            moreover
            have "g field_differentiable at w"
              using \<open>w \<in> S\<close> \<open>open S\<close> holg holomorphic_on_imp_differentiable_at by auto
            moreover
            have "cmod (deriv (\<lambda>w. \<F> n w - g w) w) * 2 \<le> e"
              using Cauchy_higher_deriv_bound [OF hol cont in_ball, of 1] \<open>r > 0\<close> by auto
            ultimately have "dist (deriv (\<F> n) w) (deriv g w) \<le> e/2"
              by (simp add: dist_norm)
            then show ?thesis
              using \<open>e > 0\<close> by auto
          qed
          moreover
          have "cball z0 (3 * r / 4) \<subseteq> ball z0 r"
            by (simp add: cball_subset_ball_iff \<open>0 < r\<close>)
          with subS have "uniform_limit (cball z0 (3 * r/4)) \<F> g sequentially"
            by (force intro: ul_g)
          then have "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>cball z0 (3 * r / 4). dist (\<F> n x) (g x) < r / 4 * e / 2"
            using \<open>0 < e\<close> \<open>0 < r\<close> by (force simp: intro!: uniform_limitD)
          ultimately show ?thesis
            by (force simp add: eventually_sequentially)
        qed
      qed
      show "uniform_limit (sphere z0 (r/2)) \<F> g sequentially"
      proof (rule uniform_limitI)
        fix e::real
        assume "0 < e"
        have "sphere z0 (r/2) \<subseteq> ball z0 r"
          using \<open>0 < r\<close> by auto
        with subS have "uniform_limit (sphere z0 (r/2)) \<F> g sequentially"
          by (force intro: ul_g)
        then show "\<forall>\<^sub>F n in sequentially. \<forall>x \<in> sphere z0 (r/2). dist (\<F> n x) (g x) < e"
          using \<open>0 < e\<close> uniform_limit_iff by blast
      qed
      show "b > 0" "\<And>x. x \<in> sphere z0 (r/2) \<Longrightarrow> b \<le> cmod (g x)"
        using b \<open>0 < r\<close> by (fastforce simp: geq hnz)+
    qed
  qed (use \<open>0 < r\<close> in auto)
  then have "(\<lambda>n. 0) \<longlonglongrightarrow> contour_integral (circlepath z0 (r/2)) (\<lambda>z. deriv g z / g z)"
    by (simp add: contour_integral_unique [OF *])
  then have "contour_integral (circlepath z0 (r/2)) (\<lambda>z. deriv g z / g z) = 0"
    by (simp add: LIMSEQ_const_iff)
  moreover
  have "contour_integral (circlepath z0 (r/2)) (\<lambda>z. deriv g z / g z) =
        contour_integral (circlepath z0 (r/2)) (\<lambda>z. m / (z - z0) + deriv h z / h z)"
  proof (rule contour_integral_eq, use \<open>0 < r\<close> in simp)
    fix w
    assume w: "dist z0 w * 2 = r"
    then have w_inb: "w \<in> ball z0 r"
      using \<open>0 < r\<close> by auto
    have h_der: "(h has_field_derivative deriv h w) (at w)"
      using holh holomorphic_derivI w_inb by blast
    have "deriv g w = ((of_nat m * h w + deriv h w * (w - z0)) * (w - z0) ^ m) / (w - z0)"
      if "r = dist z0 w * 2" "w \<noteq> z0"
    proof -
      have "((\<lambda>w. (w - z0) ^ m * h w) has_field_derivative
            (m * h w + deriv h w * (w - z0)) * (w - z0) ^ m / (w - z0)) (at w)"
        apply (rule derivative_eq_intros h_der refl)+
        using that \<open>m > 0\<close> \<open>0 < r\<close> apply (simp add: divide_simps distrib_right)
        by (metis Suc_pred mult.commute power_Suc)
      then show ?thesis
      proof (rule DERIV_imp_deriv [OF has_field_derivative_transform_within_open])
        show "\<And>x. x \<in> ball z0 r \<Longrightarrow> (x - z0) ^ m * h x = g x"
          by (simp add: hnz geq)
      qed (use that \<open>m > 0\<close> \<open>0 < r\<close> in auto)
    qed
    with \<open>0 < r\<close> \<open>0 < m\<close> w w_inb show "deriv g w / g w = of_nat m / (w - z0) + deriv h w / h w"
      by (auto simp: geq field_split_simps hnz)
  qed
  moreover
  have "contour_integral (circlepath z0 (r/2)) (\<lambda>z. m / (z - z0) + deriv h z / h z) =
        2 * of_real pi * \<i> * m + 0"
  proof (rule contour_integral_unique [OF has_contour_integral_add])
    show "((\<lambda>x. m / (x - z0)) has_contour_integral 2 * of_real pi * \<i> * m) (circlepath z0 (r/2))"
      by (force simp: \<open>0 < r\<close> intro: Cauchy_integral_circlepath_simple)
    show "((\<lambda>x. deriv h x / h x) has_contour_integral 0) (circlepath z0 (r/2))"
      using hnz holh holomorphic_deriv holomorphic_on_divide \<open>0 < r\<close>
      by (fastforce intro!: Cauchy_theorem_disc_simple [of _ z0 r])
  qed
  ultimately show False using \<open>0 < m\<close> by auto
qed

corollary Hurwitz_injective:
  assumes S: "open S" "connected S"
      and holf: "\<And>n::nat. \<F> n holomorphic_on S"
      and holg: "g holomorphic_on S"
      and ul_g: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K \<F> g sequentially"
      and nonconst: "\<not> g constant_on S"
      and inj: "\<And>n. inj_on (\<F> n) S"
    shows "inj_on g S"
proof -
  have False if z12: "z1 \<in> S" "z2 \<in> S" "z1 \<noteq> z2" "g z2 = g z1" for z1 z2
  proof -
    obtain z0 where "z0 \<in> S" and z0: "g z0 \<noteq> g z2"
      using constant_on_def nonconst by blast
    have "(\<lambda>z. g z - g z1) holomorphic_on S"
      by (intro holomorphic_intros holg)
    then obtain r where "0 < r" "ball z2 r \<subseteq> S" "\<And>z. dist z2 z < r \<and> z \<noteq> z2 \<Longrightarrow> g z \<noteq> g z1"
      apply (rule isolated_zeros [of "\<lambda>z. g z - g z1" S z2 z0])
      using S \<open>z0 \<in> S\<close> z0 z12 by auto
    have "g z2 - g z1 \<noteq> 0"
    proof (rule Hurwitz_no_zeros [of "S - {z1}" "\<lambda>n z. \<F> n z - \<F> n z1" "\<lambda>z. g z - g z1"])
      show "open (S - {z1})"
        by (simp add: S open_delete)
      show "connected (S - {z1})"
        by (simp add: connected_open_delete [OF S])
      show "\<And>n. (\<lambda>z. \<F> n z - \<F> n z1) holomorphic_on S - {z1}"
        by (intro holomorphic_intros holomorphic_on_subset [OF holf]) blast
      show "(\<lambda>z. g z - g z1) holomorphic_on S - {z1}"
        by (intro holomorphic_intros holomorphic_on_subset [OF holg]) blast
      show "uniform_limit K (\<lambda>n z. \<F> n z - \<F> n z1) (\<lambda>z. g z - g z1) sequentially"
           if "compact K" "K \<subseteq> S - {z1}" for K
      proof (rule uniform_limitI)
        fix e::real
        assume "e > 0"
        have "uniform_limit K \<F> g sequentially"
          using that ul_g by fastforce
        then have K: "\<forall>\<^sub>F n in sequentially. \<forall>x \<in> K. dist (\<F> n x) (g x) < e/2"
          using \<open>0 < e\<close> by (force simp: intro!: uniform_limitD)
        have "uniform_limit {z1} \<F> g sequentially"
          by (simp add: ul_g z12)
        then have "\<forall>\<^sub>F n in sequentially. \<forall>x \<in> {z1}. dist (\<F> n x) (g x) < e/2"
          using \<open>0 < e\<close> by (force simp: intro!: uniform_limitD)
        then have z1: "\<forall>\<^sub>F n in sequentially. dist (\<F> n z1) (g z1) < e/2"
          by simp
        show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>K. dist (\<F> n x - \<F> n z1) (g x - g z1) < e" 
          apply (rule eventually_mono [OF  eventually_conj [OF K z1]])
          by (metis (no_types, opaque_lifting) diff_add_eq diff_diff_eq2 dist_commute dist_norm dist_triangle_add_half)
      qed
      show "\<not> (\<lambda>z. g z - g z1) constant_on S - {z1}"
        unfolding constant_on_def
        by (metis Diff_iff \<open>z0 \<in> S\<close> empty_iff insert_iff right_minus_eq z0 z12)
      show "\<And>n z. z \<in> S - {z1} \<Longrightarrow> \<F> n z - \<F> n z1 \<noteq> 0"
        by (metis DiffD1 DiffD2 eq_iff_diff_eq_0 inj inj_onD insertI1 \<open>z1 \<in> S\<close>)
      show "z2 \<in> S - {z1}"
        using \<open>z2 \<in> S\<close> \<open>z1 \<noteq> z2\<close> by auto
    qed
    with z12 show False by auto
  qed
  then show ?thesis by (auto simp: inj_on_def)
qed



subsection\<open>The Great Picard theorem\<close>

lemma GPicard1:
  assumes S: "open S" "connected S" and "w \<in> S" "0 < r" "Y \<subseteq> X"
      and holX: "\<And>h. h \<in> X \<Longrightarrow> h holomorphic_on S"
      and X01:  "\<And>h z. \<lbrakk>h \<in> X; z \<in> S\<rbrakk> \<Longrightarrow> h z \<noteq> 0 \<and> h z \<noteq> 1"
      and r:    "\<And>h. h \<in> Y \<Longrightarrow> norm(h w) \<le> r"
  obtains B Z where "0 < B" "open Z" "w \<in> Z" "Z \<subseteq> S" "\<And>h z. \<lbrakk>h \<in> Y; z \<in> Z\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
proof -
  obtain e where "e > 0" and e: "cball w e \<subseteq> S"
    using assms open_contains_cball_eq by blast
  show ?thesis
  proof
    show "0 < exp(pi * exp(pi * (2 + 2 * r + 12)))"
      by simp
    show "ball w (e / 2) \<subseteq> S"
      using e ball_divide_subset_numeral ball_subset_cball by blast
    show "cmod (h z) \<le> exp (pi * exp (pi * (2 + 2 * r + 12)))"
         if "h \<in> Y" "z \<in> ball w (e / 2)" for h z
    proof -
      have "h \<in> X"
        using \<open>Y \<subseteq> X\<close> \<open>h \<in> Y\<close>  by blast
      have hol_h_o: "(h \<circ> (\<lambda>z. (w + of_real e * z))) holomorphic_on cball 0 1"
      proof (intro holomorphic_intros holomorphic_on_compose)
        have "h holomorphic_on S" 
          using holX \<open>h \<in> X\<close> by auto
        then have "h holomorphic_on cball w e"
          by (metis e holomorphic_on_subset)
        moreover have "(\<lambda>z. w + complex_of_real e * z) ` cball 0 1 \<subseteq> cball w e"
          using that \<open>e > 0\<close> by (auto simp: dist_norm norm_mult)
        ultimately show "h holomorphic_on (\<lambda>z. w + complex_of_real e * z) ` cball 0 1"
          by (rule holomorphic_on_subset)
      qed
      have norm_le_r: "cmod ((h \<circ> (\<lambda>z. w + complex_of_real e * z)) 0) \<le> r"
        by (auto simp: r \<open>h \<in> Y\<close>)
      have le12: "norm (of_real(inverse e) * (z - w)) \<le> 1/2"
        using that \<open>e > 0\<close> by (simp add: inverse_eq_divide dist_norm norm_minus_commute norm_divide)
      have non01: "h (w + e * z) \<noteq> 0 \<and> h (w + e * z) \<noteq> 1" if "z \<in> cball 0 1" for z::complex
      proof (rule X01 [OF \<open>h \<in> X\<close>])
        have "w + complex_of_real e * z \<in> cball w e"
          using \<open>0 < e\<close> that by (auto simp: dist_norm norm_mult)
        then show "w + complex_of_real e * z \<in> S"
          by (rule subsetD [OF e])
      qed
      have "cmod (h z) \<le> cmod (h (w + of_real e * (inverse e * (z - w))))"
        using \<open>0 < e\<close> by (simp add: field_split_simps)
      also have "... \<le> exp (pi * exp (pi * (14 + 2 * r)))"
        using r [OF \<open>h \<in> Y\<close>] Schottky [OF hol_h_o norm_le_r _ _ _ le12] non01 by auto
      finally
      show ?thesis by simp
    qed
  qed (use \<open>e > 0\<close> in auto)
qed 

lemma GPicard2:
  assumes "S \<subseteq> T" "connected T" "S \<noteq> {}" "open S" "\<And>x. \<lbrakk>x islimpt S; x \<in> T\<rbrakk> \<Longrightarrow> x \<in> S"
    shows "S = T"
  by (metis assms open_subset connected_clopen closedin_limpt)

    
lemma GPicard3:
  assumes S: "open S" "connected S" "w \<in> S" and "Y \<subseteq> X"
      and holX: "\<And>h. h \<in> X \<Longrightarrow> h holomorphic_on S"
      and X01:  "\<And>h z. \<lbrakk>h \<in> X; z \<in> S\<rbrakk> \<Longrightarrow> h z \<noteq> 0 \<and> h z \<noteq> 1"
      and no_hw_le1: "\<And>h. h \<in> Y \<Longrightarrow> norm(h w) \<le> 1"
      and "compact K" "K \<subseteq> S"
  obtains B where "\<And>h z. \<lbrakk>h \<in> Y; z \<in> K\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
proof -
  define U where "U \<equiv> {z \<in> S. \<exists>B Z. 0 < B \<and> open Z \<and> z \<in> Z \<and> Z \<subseteq> S \<and>
                               (\<forall>h z'. h \<in> Y \<and> z' \<in> Z \<longrightarrow> norm(h z') \<le> B)}"
  then have "U \<subseteq> S" by blast
  have "U = S"
  proof (rule GPicard2 [OF \<open>U \<subseteq> S\<close> \<open>connected S\<close>])
    show "U \<noteq> {}"
    proof -
      obtain B Z where "0 < B" "open Z" "w \<in> Z" "Z \<subseteq> S" 
        and  "\<And>h z. \<lbrakk>h \<in> Y; z \<in> Z\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
        using GPicard1 [OF S zero_less_one \<open>Y \<subseteq> X\<close> holX] X01 no_hw_le1 by blast
      then show ?thesis
        unfolding U_def using \<open>w \<in> S\<close> by blast
    qed
    show "open U"
      unfolding open_subopen [of U] by (auto simp: U_def)
    fix v
    assume v: "v islimpt U" "v \<in> S"
    have "\<not> (\<forall>r>0. \<exists>h\<in>Y. r < cmod (h v))"
    proof
      assume "\<forall>r>0. \<exists>h\<in>Y. r < cmod (h v)"
      then have "\<forall>n. \<exists>h\<in>Y. Suc n < cmod (h v)"
        by simp
      then obtain \<F> where FY: "\<And>n. \<F> n \<in> Y" and ltF: "\<And>n. Suc n < cmod (\<F> n v)"
        by metis
      define \<G> where "\<G> \<equiv> \<lambda>n z. inverse(\<F> n z)"
      have hol\<G>: "\<G> n holomorphic_on S" for n
      proof (simp add: \<G>_def)
        show "(\<lambda>z. inverse (\<F> n z)) holomorphic_on S"
          using FY X01 \<open>Y \<subseteq> X\<close> holX by (blast intro: holomorphic_on_inverse)
      qed
      have \<G>not0: "\<G> n z \<noteq> 0" and \<G>not1: "\<G> n z \<noteq> 1" if "z \<in> S" for n z
        using FY X01 \<open>Y \<subseteq> X\<close> that by (force simp: \<G>_def)+
      have \<G>_le1: "cmod (\<G> n v) \<le> 1" for n 
        using less_le_trans linear ltF 
        by (fastforce simp add: \<G>_def norm_inverse inverse_le_1_iff)
      define W where "W \<equiv> {h. h holomorphic_on S \<and> (\<forall>z \<in> S. h z \<noteq> 0 \<and> h z \<noteq> 1)}"
      obtain B Z where "0 < B" "open Z" "v \<in> Z" "Z \<subseteq> S" 
                   and B: "\<And>h z. \<lbrakk>h \<in> range \<G>; z \<in> Z\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
        apply (rule GPicard1 [OF \<open>open S\<close> \<open>connected S\<close> \<open>v \<in> S\<close> zero_less_one, of "range \<G>" W])
        using hol\<G> \<G>not0 \<G>not1 \<G>_le1 by (force simp: W_def)+
      then obtain e where "e > 0" and e: "ball v e \<subseteq> Z"
        by (meson open_contains_ball)
      obtain h j where holh: "h holomorphic_on ball v e" and "strict_mono j"
                   and lim:  "\<And>x. x \<in> ball v e \<Longrightarrow> (\<lambda>n. \<G> (j n) x) \<longlonglongrightarrow> h x"
                   and ulim: "\<And>K. \<lbrakk>compact K; K \<subseteq> ball v e\<rbrakk>
                                  \<Longrightarrow> uniform_limit K (\<G> \<circ> j) h sequentially"
      proof (rule Montel)
        show "\<And>h. h \<in> range \<G> \<Longrightarrow> h holomorphic_on ball v e"
          by (metis \<open>Z \<subseteq> S\<close> e hol\<G> holomorphic_on_subset imageE)
        show "\<And>K. \<lbrakk>compact K; K \<subseteq> ball v e\<rbrakk> \<Longrightarrow> \<exists>B. \<forall>h\<in>range \<G>. \<forall>z\<in>K. cmod (h z) \<le> B"
          using B e by blast
      qed auto
      have "h v = 0"
      proof (rule LIMSEQ_unique)
        show "(\<lambda>n. \<G> (j n) v) \<longlonglongrightarrow> h v"
          using \<open>e > 0\<close> lim by simp
        have lt_Fj: "real x \<le> cmod (\<F> (j x) v)" for x
          by (metis of_nat_Suc ltF \<open>strict_mono j\<close> add.commute less_eq_real_def less_le_trans nat_le_real_less seq_suble)
        show "(\<lambda>n. \<G> (j n) v) \<longlonglongrightarrow> 0"
        proof (rule Lim_null_comparison [OF eventually_sequentiallyI lim_inverse_n])
          show "cmod (\<G> (j x) v) \<le> inverse (real x)" if "1 \<le> x" for x
            using that by (simp add: \<G>_def norm_inverse_le_norm [OF lt_Fj])
        qed        
      qed
      have "h v \<noteq> 0"
      proof (rule Hurwitz_no_zeros [of "ball v e" "\<G> \<circ> j" h])
        show "\<And>n. (\<G> \<circ> j) n holomorphic_on ball v e"
          using \<open>Z \<subseteq> S\<close> e hol\<G> by force
        show "\<And>n z. z \<in> ball v e \<Longrightarrow> (\<G> \<circ> j) n z \<noteq> 0"
          using \<G>not0 \<open>Z \<subseteq> S\<close> e by fastforce
        show "\<not> h constant_on ball v e"
        proof (clarsimp simp: constant_on_def)
          fix c
          have False if "\<And>z. dist v z < e \<Longrightarrow> h z = c"  
          proof -
            have "h v = c"
              by (simp add: \<open>0 < e\<close> that)
            obtain y where "y \<in> U" "y \<noteq> v" and y: "dist y v < e"
              using v \<open>e > 0\<close> by (auto simp: islimpt_approachable)
            then obtain C T where "y \<in> S" "C > 0" "open T" "y \<in> T" "T \<subseteq> S"
              and "\<And>h z'. \<lbrakk>h \<in> Y; z' \<in> T\<rbrakk> \<Longrightarrow> cmod (h z') \<le> C"
              using \<open>y \<in> U\<close> by (auto simp: U_def)
            then have le_C: "\<And>n. cmod (\<F> n y) \<le> C"
              using FY by blast

            have "\<forall>\<^sub>F n in sequentially. dist (\<G> (j n) y) (h y) < inverse C"
              using uniform_limitD [OF ulim [of "{y}"], of "inverse C"] \<open>C > 0\<close> y
              by (simp add: dist_commute)
            then obtain n where "dist (\<G> (j n) y) (h y) < inverse C"
              by (meson eventually_at_top_linorder order_refl)
            moreover
            have "h y = h v"
              by (metis \<open>h v = c\<close> dist_commute that y)
            ultimately have "cmod (inverse (\<F> (j n) y)) < inverse C"
              by (simp add: \<open>h v = 0\<close> \<G>_def)
            then have "C < norm (\<F> (j n) y)"
              by (metis \<G>_def \<G>not0 \<open>y \<in> S\<close> inverse_less_imp_less inverse_zero norm_inverse zero_less_norm_iff)
            show False
              using \<open>C < cmod (\<F> (j n) y)\<close> le_C not_less by blast
          qed
          then show "\<exists>x\<in>ball v e. h x \<noteq> c" by force
        qed
        show "h holomorphic_on ball v e"
          by (simp add: holh)
        show "\<And>K. \<lbrakk>compact K; K \<subseteq> ball v e\<rbrakk> \<Longrightarrow> uniform_limit K (\<G> \<circ> j) h sequentially"
          by (simp add: ulim)
      qed (use \<open>e > 0\<close> in auto)
      with \<open>h v = 0\<close> show False by blast
    qed
    then obtain r where "0 < r" and r: "\<And>h. h \<in> Y \<Longrightarrow> cmod (h v) \<le> r"
      by (metis not_le)
    moreover     
    obtain B Z where "0 < B" "open Z" "v \<in> Z" "Z \<subseteq> S" "\<And>h z. \<lbrakk>h \<in> Y; z \<in> Z\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
      using X01 
      by (auto simp: r intro: GPicard1[OF \<open>open S\<close> \<open>connected S\<close> \<open>v \<in> S\<close> \<open>r>0\<close> \<open>Y \<subseteq> X\<close> holX] X01)
    ultimately show "v \<in> U"
      using v by (simp add: U_def) meson
  qed
  have "\<And>x. x \<in> K \<longrightarrow> x \<in> U"
    using \<open>U = S\<close> \<open>K \<subseteq> S\<close> by blast
  then have "\<And>x. x \<in> K \<longrightarrow> (\<exists>B Z. 0 < B \<and> open Z \<and> x \<in> Z \<and> 
                               (\<forall>h z'. h \<in> Y \<and> z' \<in> Z \<longrightarrow> norm(h z') \<le> B))"
    unfolding U_def by blast
  then obtain F Z where F: "\<And>x. x \<in> K \<Longrightarrow> open (Z x) \<and> x \<in> Z x \<and> 
                               (\<forall>h z'. h \<in> Y \<and> z' \<in> Z x \<longrightarrow> norm(h z') \<le> F x)"
    by metis
  then obtain L where "L \<subseteq> K" "finite L" and L: "K \<subseteq> (\<Union>c \<in> L. Z c)"
    by (auto intro: compactE_image [OF \<open>compact K\<close>, of K Z])
  then have *: "\<And>x h z'. \<lbrakk>x \<in> L; h \<in> Y \<and> z' \<in> Z x\<rbrakk> \<Longrightarrow> cmod (h z') \<le> F x"
    using F by blast
  have "\<exists>B. \<forall>h z. h \<in> Y \<and> z \<in> K \<longrightarrow> norm(h z) \<le> B"
  proof (cases "L = {}")
    case True with L show ?thesis by simp
  next
    case False
    then have "\<forall>h z. h \<in> Y \<and> z \<in> K \<longrightarrow> (\<exists>x\<in>L. cmod (h z) \<le> F x)"
      by (metis "*" L UN_E subset_iff)
    with False \<open>finite L\<close> show ?thesis 
      by (rule_tac x = "Max (F ` L)" in exI) (simp add: linorder_class.Max_ge_iff)
  qed
  with that show ?thesis by metis
qed


lemma GPicard4:
  assumes "0 < k" and holf: "f holomorphic_on (ball 0 k - {0})" 
      and AE: "\<And>e. \<lbrakk>0 < e; e < k\<rbrakk> \<Longrightarrow> \<exists>d. 0 < d \<and> d < e \<and> (\<forall>z \<in> sphere 0 d. norm(f z) \<le> B)"
  obtains \<epsilon> where "0 < \<epsilon>" "\<epsilon> < k" "\<And>z. z \<in> ball 0 \<epsilon> - {0} \<Longrightarrow> norm(f z) \<le> B"
proof -
  obtain \<epsilon> where "0 < \<epsilon>" "\<epsilon> < k/2" and \<epsilon>: "\<And>z. norm z = \<epsilon> \<Longrightarrow> norm(f z) \<le> B"
    using AE [of "k/2"] \<open>0 < k\<close> by auto
  show ?thesis
  proof
    show "\<epsilon> < k"
      using \<open>0 < k\<close> \<open>\<epsilon> < k/2\<close> by auto
    show "cmod (f \<xi>) \<le> B" if \<xi>: "\<xi> \<in> ball 0 \<epsilon> - {0}" for \<xi>
    proof -
      obtain d where "0 < d" "d < norm \<xi>" and d: "\<And>z. norm z = d \<Longrightarrow> norm(f z) \<le> B"
        using AE [of "norm \<xi>"] \<open>\<epsilon> < k\<close> \<xi> by auto
      have [simp]: "closure (cball 0 \<epsilon> - ball 0 d) = cball 0 \<epsilon> - ball 0 d"
        by (blast intro!: closure_closed)
      have [simp]: "interior (cball 0 \<epsilon> - ball 0 d) = ball 0 \<epsilon> - cball (0::complex) d"
        using \<open>0 < \<epsilon>\<close> \<open>0 < d\<close> by (simp add: interior_diff)
      have *: "norm(f w) \<le> B" if "w \<in> cball 0 \<epsilon> - ball 0 d" for w
      proof (rule maximum_modulus_frontier [of f "cball 0 \<epsilon> - ball 0 d"])
        show "f holomorphic_on interior (cball 0 \<epsilon> - ball 0 d)"
          using \<open>\<epsilon> < k\<close> \<open>0 < d\<close> that by (auto intro:  holomorphic_on_subset [OF holf])
        show "continuous_on (closure (cball 0 \<epsilon> - ball 0 d)) f"
        proof (intro holomorphic_on_imp_continuous_on holomorphic_on_subset [OF holf])
          show "closure (cball 0 \<epsilon> - ball 0 d) \<subseteq> ball 0 k - {0}"
            using \<open>0 < d\<close> \<open>\<epsilon> < k\<close> by auto
        qed
        show "\<And>z. z \<in> frontier (cball 0 \<epsilon> - ball 0 d) \<Longrightarrow> cmod (f z) \<le> B"
          unfolding frontier_def
          using \<epsilon> d less_eq_real_def by force
      qed (use that in auto)
      show ?thesis
        using * \<open>d < cmod \<xi>\<close> that by auto
    qed
  qed (use \<open>0 < \<epsilon>\<close> in auto)
qed
  

lemma GPicard5:
  assumes holf: "f holomorphic_on (ball 0 1 - {0})"
      and f01:  "\<And>z. z \<in> ball 0 1 - {0} \<Longrightarrow> f z \<noteq> 0 \<and> f z \<noteq> 1"
  obtains e B where "0 < e" "e < 1" "0 < B" 
                    "(\<forall>z \<in> ball 0 e - {0}. norm(f z) \<le> B) \<or>
                     (\<forall>z \<in> ball 0 e - {0}. norm(f z) \<ge> B)"
proof -
  have [simp]: "1 + of_nat n \<noteq> (0::complex)" for n
    using of_nat_eq_0_iff by fastforce
  have [simp]: "cmod (1 + of_nat n) = 1 + of_nat n" for n
    by (metis norm_of_nat of_nat_Suc)
  have *: "(\<lambda>x::complex. x / of_nat (Suc n)) ` (ball 0 1 - {0}) \<subseteq> ball 0 1 - {0}" for n
    by (auto simp: norm_divide field_split_simps split: if_split_asm)
  define h where "h \<equiv> \<lambda>n z::complex. f (z / (Suc n))"
  have holh: "(h n) holomorphic_on ball 0 1 - {0}" for n
    unfolding h_def
  proof (rule holomorphic_on_compose_gen [unfolded o_def, OF _ holf *])
    show "(\<lambda>x. x / of_nat (Suc n)) holomorphic_on ball 0 1 - {0}"
      by (intro holomorphic_intros) auto
  qed
  have h01: "\<And>n z. z \<in> ball 0 1 - {0} \<Longrightarrow> h n z \<noteq> 0 \<and> h n z \<noteq> 1" 
    unfolding h_def 
    using * by (force intro!: f01)
  obtain w where w: "w \<in> ball 0 1 - {0::complex}"
    by (rule_tac w = "1/2" in that) auto
  consider "infinite {n. norm(h n w) \<le> 1}" | "infinite {n. 1 \<le> norm(h n w)}"
    by (metis (mono_tags, lifting) infinite_nat_iff_unbounded_le le_cases mem_Collect_eq)
  then show ?thesis
  proof cases
    case 1
    with infinite_enumerate obtain r :: "nat \<Rightarrow> nat" 
      where "strict_mono r" and r: "\<And>n. r n \<in> {n. norm(h n w) \<le> 1}"
      by blast
    obtain B where B: "\<And>j z. \<lbrakk>norm z = 1/2; j \<in> range (h \<circ> r)\<rbrakk> \<Longrightarrow> norm(j z) \<le> B"
    proof (rule GPicard3 [OF _ _ w, where K = "sphere 0 (1/2)"])  
      show "range (h \<circ> r) \<subseteq> 
            {g. g holomorphic_on ball 0 1 - {0} \<and> (\<forall>z \<in> ball 0 1 - {0}. g z \<noteq> 0 \<and> g z \<noteq> 1)}"
        using h01 by (auto intro: holomorphic_intros holomorphic_on_compose holh)
      show "connected (ball 0 1 - {0::complex})"
        by (simp add: connected_open_delete)
    qed (use r in auto)        
    have normf_le_B: "cmod(f z) \<le> B" if "norm z = 1 / (2 * (1 + of_nat (r n)))" for z n
    proof -
      have *: "\<And>w. norm w = 1/2 \<Longrightarrow> cmod((f (w / (1 + of_nat (r n))))) \<le> B"
        using B by (auto simp: h_def o_def)
      have half: "norm (z * (1 + of_nat (r n))) = 1/2"
        by (simp add: norm_mult divide_simps that)
      show ?thesis
        using * [OF half] by simp
    qed
    obtain \<epsilon> where "0 < \<epsilon>" "\<epsilon> < 1" "\<And>z. z \<in> ball 0 \<epsilon> - {0} \<Longrightarrow> cmod(f z) \<le> B"
    proof (rule GPicard4 [OF zero_less_one holf, of B])
      fix e::real
      assume "0 < e" "e < 1"
      obtain n where "(1/e - 2) / 2 < real n"
        using reals_Archimedean2 by blast
      also have "... \<le> r n"
        using \<open>strict_mono r\<close> by (simp add: seq_suble)
      finally have "(1/e - 2) / 2 < real (r n)" .
      with \<open>0 < e\<close> have e: "e > 1 / (2 + 2 * real (r n))"
        by (simp add: field_simps)
      show "\<exists>d>0. d < e \<and> (\<forall>z\<in>sphere 0 d. cmod (f z) \<le> B)"
        apply (rule_tac x="1 / (2 * (1 + of_nat (r n)))" in exI)
        using normf_le_B by (simp add: e)
    qed blast
    then have \<epsilon>: "cmod (f z) \<le> \<bar>B\<bar> + 1" if "cmod z < \<epsilon>" "z \<noteq> 0" for z
      using that by fastforce
    have "0 < \<bar>B\<bar> + 1"
      by simp
    then show ?thesis
      using \<epsilon> by (force intro!: that [OF \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < 1\<close>])
  next
    case 2
    with infinite_enumerate obtain r :: "nat \<Rightarrow> nat" 
      where "strict_mono r" and r: "\<And>n. r n \<in> {n. norm(h n w) \<ge> 1}"
      by blast
    obtain B where B: "\<And>j z. \<lbrakk>norm z = 1/2; j \<in> range (\<lambda>n. inverse \<circ> h (r n))\<rbrakk> \<Longrightarrow> norm(j z) \<le> B"
    proof (rule GPicard3 [OF _ _ w, where K = "sphere 0 (1/2)"])  
      show "range (\<lambda>n. inverse \<circ> h (r n)) \<subseteq> 
            {g. g holomorphic_on ball 0 1 - {0} \<and> (\<forall>z\<in>ball 0 1 - {0}. g z \<noteq> 0 \<and> g z \<noteq> 1)}"
        using h01 by (auto intro!: holomorphic_intros holomorphic_on_compose_gen [unfolded o_def, OF _ holh] holomorphic_on_compose)
      show "connected (ball 0 1 - {0::complex})"
        by (simp add: connected_open_delete)
      show "\<And>j. j \<in> range (\<lambda>n. inverse \<circ> h (r n)) \<Longrightarrow> cmod (j w) \<le> 1"
        using r norm_inverse_le_norm by fastforce
    qed (use r in auto)        
    have norm_if_le_B: "cmod(inverse (f z)) \<le> B" if "norm z = 1 / (2 * (1 + of_nat (r n)))" for z n
    proof -
      have *: "inverse (cmod((f (z / (1 + of_nat (r n)))))) \<le> B" if "norm z = 1/2" for z
        using B [OF that] by (force simp: norm_inverse h_def)
      have half: "norm (z * (1 + of_nat (r n))) = 1/2"
        by (simp add: norm_mult divide_simps that)
      show ?thesis
        using * [OF half] by (simp add: norm_inverse)
    qed
    have hol_if: "(inverse \<circ> f) holomorphic_on (ball 0 1 - {0})"
      by (metis (no_types, lifting) holf comp_apply f01 holomorphic_on_inverse holomorphic_transform)
    obtain \<epsilon> where "0 < \<epsilon>" "\<epsilon> < 1" and leB: "\<And>z. z \<in> ball 0 \<epsilon> - {0} \<Longrightarrow> cmod((inverse \<circ> f) z) \<le> B"
    proof (rule GPicard4 [OF zero_less_one hol_if, of B])
      fix e::real
      assume "0 < e" "e < 1"
      obtain n where "(1/e - 2) / 2 < real n"
        using reals_Archimedean2 by blast
      also have "... \<le> r n"
        using \<open>strict_mono r\<close> by (simp add: seq_suble)
      finally have "(1/e - 2) / 2 < real (r n)" .
      with \<open>0 < e\<close> have e: "e > 1 / (2 + 2 * real (r n))"
        by (simp add: field_simps)
      show "\<exists>d>0. d < e \<and> (\<forall>z\<in>sphere 0 d. cmod ((inverse \<circ> f) z) \<le> B)"
        apply (rule_tac x="1 / (2 * (1 + of_nat (r n)))" in exI)
        using norm_if_le_B by (simp add: e)
    qed blast
    have \<epsilon>: "cmod (f z) \<ge> inverse B" and "B > 0" if "cmod z < \<epsilon>" "z \<noteq> 0" for z
    proof -
      have "inverse (cmod (f z)) \<le> B"
        using leB that by (simp add: norm_inverse)
      moreover
      have "f z \<noteq> 0"
        using \<open>\<epsilon> < 1\<close> f01 that by auto
      ultimately show "cmod (f z) \<ge> inverse B"
        by (simp add: norm_inverse inverse_le_imp_le)
      show "B > 0"
        using \<open>f z \<noteq> 0\<close> \<open>inverse (cmod (f z)) \<le> B\<close> not_le order.trans by fastforce
    qed
    then have "B > 0"
      by (metis \<open>0 < \<epsilon>\<close> dense leI order.asym vector_choose_size)
    then have "inverse B > 0"
      by (simp add: field_split_simps)
    then show ?thesis
      using \<epsilon> that [OF \<open>0 < \<epsilon>\<close> \<open>\<epsilon> < 1\<close>]
      by (metis Diff_iff dist_0_norm insert_iff mem_ball)
  qed
qed

  
lemma GPicard6:
  assumes "open M" "z \<in> M" "a \<noteq> 0" and holf: "f holomorphic_on (M - {z})"
      and f0a: "\<And>w. w \<in> M - {z} \<Longrightarrow> f w \<noteq> 0 \<and> f w \<noteq> a"
  obtains r where "0 < r" "ball z r \<subseteq> M" 
                  "bounded(f ` (ball z r - {z})) \<or>
                   bounded((inverse \<circ> f) ` (ball z r - {z}))"
proof -
  obtain r where "0 < r" and r: "ball z r \<subseteq> M"
    using assms openE by blast 
  let ?g = "\<lambda>w. f (z + of_real r * w) / a"
  obtain e B where "0 < e" "e < 1" "0 < B" 
    and B: "(\<forall>z \<in> ball 0 e - {0}. norm(?g z) \<le> B) \<or> (\<forall>z \<in> ball 0 e - {0}. norm(?g z) \<ge> B)"
  proof (rule GPicard5)
    show "?g holomorphic_on ball 0 1 - {0}"
    proof (intro holomorphic_intros holomorphic_on_compose_gen [unfolded o_def, OF _ holf])
      show "(\<lambda>x. z + complex_of_real r * x) ` (ball 0 1 - {0}) \<subseteq> M - {z}"
        using \<open>0 < r\<close> r
        by (auto simp: dist_norm norm_mult subset_eq)
    qed (use \<open>a \<noteq> 0\<close> in auto)
    show "\<And>w. w \<in> ball 0 1 - {0} \<Longrightarrow> f (z + of_real r * w) / a \<noteq> 0 \<and> f (z + of_real r * w) / a \<noteq> 1"
      using f0a \<open>0 < r\<close> \<open>a \<noteq> 0\<close> r
      by (auto simp: field_split_simps dist_norm norm_mult subset_eq)
  qed
  show ?thesis
  proof
    show "0 < e*r"
      by (simp add: \<open>0 < e\<close> \<open>0 < r\<close>)
    have "ball z (e * r) \<subseteq> ball z r"
      by (simp add: \<open>0 < r\<close> \<open>e < 1\<close> order.strict_implies_order subset_ball)
    then show "ball z (e * r) \<subseteq> M"
      using r by blast
    consider "\<And>z. z \<in> ball 0 e - {0} \<Longrightarrow> norm(?g z) \<le> B" | "\<And>z. z \<in> ball 0 e - {0} \<Longrightarrow> norm(?g z) \<ge> B"
      using B by blast
    then show "bounded (f ` (ball z (e * r) - {z})) \<or>
          bounded ((inverse \<circ> f) ` (ball z (e * r) - {z}))"
    proof cases
      case 1
      have "\<lbrakk>dist z w < e * r; w \<noteq> z\<rbrakk> \<Longrightarrow> cmod (f w) \<le> B * norm a" for w
        using \<open>a \<noteq> 0\<close> \<open>0 < r\<close> 1 [of "(w - z) / r"]
        by (simp add: norm_divide dist_norm field_split_simps)
      then show ?thesis
        by (force simp: intro!: boundedI)
    next
      case 2
      have "\<lbrakk>dist z w < e * r; w \<noteq> z\<rbrakk> \<Longrightarrow> cmod (f w) \<ge> B * norm a" for w
        using \<open>a \<noteq> 0\<close> \<open>0 < r\<close> 2 [of "(w - z) / r"]
        by (simp add: norm_divide dist_norm field_split_simps)
      then have "\<lbrakk>dist z w < e * r; w \<noteq> z\<rbrakk> \<Longrightarrow> inverse (cmod (f w)) \<le> inverse (B * norm a)" for w
        by (metis \<open>0 < B\<close> \<open>a \<noteq> 0\<close> mult_pos_pos norm_inverse norm_inverse_le_norm zero_less_norm_iff)
      then show ?thesis 
        by (force simp: norm_inverse intro!: boundedI)
    qed
  qed
qed
  

theorem great_Picard:
  assumes "open M" "z \<in> M" "a \<noteq> b" and holf: "f holomorphic_on (M - {z})"
      and fab: "\<And>w. w \<in> M - {z} \<Longrightarrow> f w \<noteq> a \<and> f w \<noteq> b"
  obtains l where "(f \<longlongrightarrow> l) (at z) \<or> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
proof -
  obtain r where "0 < r" and zrM: "ball z r \<subseteq> M" 
             and r: "bounded((\<lambda>z. f z - a) ` (ball z r - {z})) \<or>
                     bounded((inverse \<circ> (\<lambda>z. f z - a)) ` (ball z r - {z}))"
  proof (rule GPicard6 [OF \<open>open M\<close> \<open>z \<in> M\<close>])
    show "b - a \<noteq> 0"
      using assms by auto
    show "(\<lambda>z. f z - a) holomorphic_on M - {z}"
      by (intro holomorphic_intros holf)
  qed (use fab in auto)
  have holfb: "f holomorphic_on ball z r - {z}"
    using zrM by (auto intro: holomorphic_on_subset [OF holf])
  have holfb_i: "(\<lambda>z. inverse(f z - a)) holomorphic_on ball z r - {z}"
    using fab zrM by (fastforce intro!: holomorphic_intros holfb)
  show ?thesis
    using r
  proof              
    assume "bounded ((\<lambda>z. f z - a) ` (ball z r - {z}))"
    then obtain B where B: "\<And>w. w \<in> (\<lambda>z. f z - a) ` (ball z r - {z}) \<Longrightarrow> norm w \<le> B"
      by (force simp: bounded_iff)
    then have "\<forall>x. x \<noteq> z \<and> dist x z < r \<longrightarrow> cmod (f x - a) \<le> B"
      by (simp add: dist_commute)
    with \<open>0 < r\<close> have "\<forall>\<^sub>F w in at z. cmod (f w - a) \<le> B"
      by (force simp add: eventually_at)
    moreover have "\<And>x. cmod (f x - a) \<le> B \<Longrightarrow> cmod (f x) \<le> B + cmod a"
      by (metis add.commute add_le_cancel_right norm_triangle_sub order.trans)
    ultimately have "\<exists>B. \<forall>\<^sub>F w in at z. cmod (f w) \<le> B"
      by (metis (mono_tags, lifting) eventually_at)
    then obtain g where holg: "g holomorphic_on ball z r" and gf: "\<And>w. w \<in> ball z r - {z} \<Longrightarrow> g w = f w"
      using \<open>0 < r\<close> holomorphic_on_extend_bounded [OF holfb] by auto
    then have "g \<midarrow>z\<rightarrow> g z"
      unfolding continuous_at [symmetric]
      using \<open>0 < r\<close> centre_in_ball field_differentiable_imp_continuous_at 
            holomorphic_on_imp_differentiable_at by blast
    then have "(f \<longlongrightarrow> g z) (at z)"
      using Lim_transform_within_open [of g "g z" z]
      using \<open>0 < r\<close> centre_in_ball gf by blast
    then show ?thesis
      using that by blast
  next
    assume "bounded((inverse \<circ> (\<lambda>z. f z - a)) ` (ball z r - {z}))"
    then obtain B where B: "\<And>w. w \<in> (inverse \<circ> (\<lambda>z. f z - a)) ` (ball z r - {z}) \<Longrightarrow> norm w \<le> B"
      by (force simp: bounded_iff)
    then have "\<forall>x. x \<noteq> z \<and> dist x z < r \<longrightarrow> cmod (inverse (f x - a)) \<le> B"
      by (simp add: dist_commute)
    with \<open>0 < r\<close> have "\<forall>\<^sub>F w in at z. cmod (inverse (f w - a)) \<le> B"
      by (auto simp add: eventually_at)
    then have "\<exists>B. \<forall>\<^sub>F z in at z. cmod (inverse (f z - a)) \<le> B"
      by blast
    then obtain g where holg: "g holomorphic_on ball z r" and gf: "\<And>w. w \<in> ball z r - {z} \<Longrightarrow> g w = inverse (f w - a)"
      using \<open>0 < r\<close> holomorphic_on_extend_bounded [OF holfb_i] by auto
    then have gz: "g \<midarrow>z\<rightarrow> g z"
      unfolding continuous_at [symmetric]
      using \<open>0 < r\<close> centre_in_ball field_differentiable_imp_continuous_at 
            holomorphic_on_imp_differentiable_at by blast
    have gnz: "\<And>w. w \<in> ball z r - {z} \<Longrightarrow> g w \<noteq> 0"
      using gf fab zrM by fastforce
    show ?thesis
    proof (cases "g z = 0")
      case True
      have *: "\<lbrakk>g \<noteq> 0; inverse g = f - a\<rbrakk> \<Longrightarrow> g / (1 + a * g) = inverse f" for f g::complex
        by (auto simp: field_simps)
      have "(inverse \<circ> f) \<midarrow>z\<rightarrow> 0"
      proof (rule Lim_transform_within_open [of "\<lambda>w. g w / (1 + a * g w)" _ _ UNIV "ball z r"])
        show "(\<lambda>w. g w / (1 + a * g w)) \<midarrow>z\<rightarrow> 0"
          using True by (auto simp: intro!: tendsto_eq_intros gz)
        show "\<And>x. \<lbrakk>x \<in> ball z r; x \<noteq> z\<rbrakk> \<Longrightarrow> g x / (1 + a * g x) = (inverse \<circ> f) x"
          using * gf gnz by simp
      qed (use \<open>0 < r\<close> in auto)
      with that show ?thesis by blast
    next
      case False
      show ?thesis
      proof (cases "1 + a * g z = 0")
        case True
        have "(f \<longlongrightarrow> 0) (at z)"
        proof (rule Lim_transform_within_open [of "\<lambda>w. (1 + a * g w) / g w" _ _ _ "ball z r"])
          show "(\<lambda>w. (1 + a * g w) / g w) \<midarrow>z\<rightarrow> 0"
            by (rule tendsto_eq_intros refl gz \<open>g z \<noteq> 0\<close> | simp add: True)+
          show "\<And>x. \<lbrakk>x \<in> ball z r; x \<noteq> z\<rbrakk> \<Longrightarrow> (1 + a * g x) / g x = f x"
            using fab fab zrM by (fastforce simp add: gf field_split_simps)
        qed (use \<open>0 < r\<close> in auto)
        then show ?thesis
          using that by blast 
      next
        case False
        have *: "\<lbrakk>g \<noteq> 0; inverse g = f - a\<rbrakk> \<Longrightarrow> g / (1 + a * g) = inverse f" for f g::complex
          by (auto simp: field_simps)
        have "(inverse \<circ> f) \<midarrow>z\<rightarrow> g z / (1 + a * g z)"
        proof (rule Lim_transform_within_open [of "\<lambda>w. g w / (1 + a * g w)" _ _ UNIV "ball z r"])
          show "(\<lambda>w. g w / (1 + a * g w)) \<midarrow>z\<rightarrow> g z / (1 + a * g z)"
            using False by (auto simp: False intro!: tendsto_eq_intros gz)
          show "\<And>x. \<lbrakk>x \<in> ball z r; x \<noteq> z\<rbrakk> \<Longrightarrow> g x / (1 + a * g x) = (inverse \<circ> f) x"
            using * gf gnz by simp
        qed (use \<open>0 < r\<close> in auto)
        with that show ?thesis by blast
      qed
    qed 
  qed
qed


corollary great_Picard_alt:
  assumes M: "open M" "z \<in> M" and holf: "f holomorphic_on (M - {z})"
    and non: "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  obtains a where "- {a} \<subseteq> f ` (M - {z})"
unfolding subset_iff image_iff
  by (metis great_Picard [OF M _ holf] non Compl_iff insertI1)
    

corollary great_Picard_infinite:
  assumes M: "open M" "z \<in> M" and holf: "f holomorphic_on (M - {z})"
    and non: "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  obtains a where "\<And>w. w \<noteq> a \<Longrightarrow> infinite {x. x \<in> M - {z} \<and> f x = w}"
proof -
  have False if "a \<noteq> b" and ab: "finite {x. x \<in> M - {z} \<and> f x = a}" "finite {x. x \<in> M - {z} \<and> f x = b}" for a b
  proof -
    have finab: "finite {x. x \<in> M - {z} \<and> f x \<in> {a,b}}"
      using finite_UnI [OF ab]  unfolding mem_Collect_eq insert_iff empty_iff
      by (simp add: conj_disj_distribL)
    obtain r where "0 < r" and zrM: "ball z r \<subseteq> M" and r: "\<And>x. \<lbrakk>x \<in> M - {z}; f x \<in> {a,b}\<rbrakk> \<Longrightarrow> x \<notin> ball z r"
    proof -
      obtain e where "e > 0" and e: "ball z e \<subseteq> M"
        using assms openE by blast
      show ?thesis
      proof (cases "{x \<in> M - {z}. f x \<in> {a, b}} = {}")
        case True
        then show ?thesis
          using e \<open>e > 0\<close> that by fastforce
      next
        case False
        let ?r = "min e (Min (dist z ` {x \<in> M - {z}. f x \<in> {a,b}}))"
        show ?thesis
        proof
          show "0 < ?r"
            using min_less_iff_conj Min_gr_iff finab False \<open>0 < e\<close> by auto
          have "ball z ?r \<subseteq> ball z e"
            by (simp add: subset_ball)
          with e show "ball z ?r \<subseteq> M" by blast
          show "\<And>x. \<lbrakk>x \<in> M - {z}; f x \<in> {a, b}\<rbrakk> \<Longrightarrow> x \<notin> ball z ?r"
            using min_less_iff_conj Min_gr_iff finab False \<open>0 < e\<close> by auto
        qed
      qed
    qed
    have holfb: "f holomorphic_on (ball z r - {z})"
      apply (rule holomorphic_on_subset [OF holf])
       using zrM by auto
     show ?thesis
       apply (rule great_Picard [OF open_ball _ \<open>a \<noteq> b\<close> holfb])
      using non \<open>0 < r\<close> r zrM by auto
  qed
  with that show thesis
    by meson
qed

theorem Casorati_Weierstrass:
  assumes "open M" "z \<in> M" "f holomorphic_on (M - {z})"
      and "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  shows "closure(f ` (M - {z})) = UNIV"
proof -
  obtain a where a: "- {a} \<subseteq> f ` (M - {z})"
    using great_Picard_alt [OF assms] .
  have "UNIV = closure(- {a})"
    by (simp add: closure_interior)
  also have "... \<subseteq> closure(f ` (M - {z}))"
    by (simp add: a closure_mono)
  finally show ?thesis
    by blast 
qed
  
end

(*  Title:      HOL/MacLaurin.thy
    Author:     Jacques D. Fleuriot, 2001 University of Edinburgh
    Author:     Lawrence C Paulson, 2004
    Author:     Lukas Bulwahn and Bernhard Häupler, 2005
*)

section \<open>MacLaurin and Taylor Series\<close>

theory MacLaurin
imports Transcendental
begin

subsection \<open>Maclaurin's Theorem with Lagrange Form of Remainder\<close>

lemma fact_diff_Suc: "n < Suc m \<Longrightarrow> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
  by (subst fact_reduce) auto

lemma Maclaurin:
  assumes h: "0 < h"
    and n: "0 < n"
    and diff_0: "diff 0 = f"
    and diff_Suc: "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  shows
    "\<exists>t::real. 0 < t \<and> t < h \<and>
      f h = (\<Sum>m<n. diff m 0 / fact m * h^m) + diff n t / fact n * h^n"
proof -

  define B where "B = (f h - (\<Sum>m<n. diff m 0 / fact m * h^m)) * fact n / h^n"  

  define difg where [abs_def]: "difg m t =
    diff m t - (\<Sum>p<n-m. diff (m + p) 0 / fact p * t^p) -
    B * (t ^ (n - m) / fact (n - m))" for m t

  have difg_Suc: "DERIV (difg m) t :> difg (Suc m) t"
    if mn: "m < n" and t0: "0 \<le> t" and th: "t \<le> h" for m t
  proof-
    have "DERIV (difg m) t :>
      diff (Suc m) t -
      (\<Sum>x \<in> {..< n - m}. real x * t ^ (x - 1) * diff (m + x) 0 / fact x) -
      real (n - m) * t ^ (n - Suc m) * B / fact (n - m)"
      by (auto simp: difg_def intro!: derivative_eq_intros diff_Suc[rule_format] mn t0 th)
    also from mn have "{..< n - m} = insert 0 (Suc ` {..< n - Suc m})"
      unfolding atLeast0LessThan[symmetric] by auto
    also have "(\<Sum>x \<in> \<dots>. real x * t ^ (x - 1) * diff (m + x) 0 / fact x) =
        (\<Sum>x < n - Suc m. (1 + real x) * t ^ x * diff (m + 1 + x) 0 / fact (Suc x))"
      by (subst sum.insert) (auto simp: sum.reindex)
    also have "\<dots> = (\<Sum>x < n - Suc m. diff (m + 1 + x) 0 * t^x / fact x)"
      by (rule sum.cong) (simp_all add: nonzero_divide_eq_eq)
    also have "(n - m) * t ^ (n - Suc m) * B / fact (n - m) = B * (t ^ (n - Suc m) / fact (n - Suc m))"
      using mn by (simp add: field_split_simps fact_reduce)
    finally show "DERIV (difg m) t :> difg (Suc m) t"
      by (simp add: difg_def)
  qed

  have myRolle: "\<exists>t. 0 < t \<and> t < h' \<and> DERIV (difg m) t :> 0"
    if mn: "m < n" and eq: "difg m 0 = difg m h'" and h'0: "0 < h'" and h'h: "h' \<le> h" for m h'
  proof (intro Rolle[OF h'0 eq])
    show "continuous_on {0..h'} (difg m)"
      using mn h'h by (auto intro!: continuous_at_imp_continuous_on DERIV_isCont[OF difg_Suc])
    fix x assume x0: "0 < x" and xh': "x < h'"
    with h'h have "0 \<le> x" "x \<le> h" by auto
    from difg_Suc[OF mn this]
    show "difg m differentiable (at x)"
      by (auto simp: real_differentiable_def)
  qed
  from n obtain m where nm: "n = Suc m" by (auto simp: gr0_conv_Suc)
  then have "m < n" by simp
  then have "\<exists>t. 0 < t \<and> t < h \<and> DERIV (difg m) t :> 0"
  proof (induct m)
    case 0
    from n have "difg 0 0 = difg 0 h" by (auto simp: difg_def B_def diff_0)
    with n h show ?case
      by (auto intro!: myRolle)
  next
    case (Suc m)
    from Suc have dSm0: "difg (Suc m) 0 = 0"
      by (auto simp: difg_def)
    from Suc obtain t where t0: "0 < t" and th: "t < h" and mt: "DERIV (difg m) t :> 0"
      by auto
    from t0 th DERIV_unique[OF difg_Suc mt] Suc
    have "difg (Suc m) 0 = difg (Suc m) t"
      by (auto simp: dSm0)
    with t0 th \<open>Suc m < n\<close>
    have "\<exists>t'. 0 < t' \<and> t' < t \<and> DERIV (difg (Suc m)) t' :> 0"
      by (auto intro!: myRolle)
    with th show ?case
      by auto
  qed
  from this nm DERIV_unique[OF difg_Suc]
  obtain t where "0 < t" "t < h" "difg n t = 0"
    by auto
  then show ?thesis by (auto simp: B_def difg_def)
qed

lemma Maclaurin2:
  fixes n :: nat
    and h :: real
  assumes INIT1: "0 < h"
    and INIT2: "diff 0 = f"
    and DERIV: "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. 0 < t \<and> t \<le> h \<and> f h = (\<Sum>m<n. diff m 0 / fact m * h ^ m) + diff n t / fact n * h ^ n"
proof (cases n)
  case 0
  with INIT1 INIT2 show ?thesis by fastforce
next
  case Suc
  then have "n > 0" by simp
  from Maclaurin [OF INIT1 this INIT2 DERIV]
  show ?thesis by fastforce
qed

lemma Maclaurin_minus:
  fixes n :: nat and h :: real
  assumes "h < 0" "0 < n" "diff 0 = f"
    and DERIV: "\<forall>m t. m < n \<and> h \<le> t \<and> t \<le> 0 \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. h < t \<and> t < 0 \<and> f h = (\<Sum>m<n. diff m 0 / fact m * h ^ m) + diff n t / fact n * h ^ n"
proof -
  txt \<open>Transform \<open>ABL'\<close> into \<open>derivative_intros\<close> format.\<close>
  note DERIV' = DERIV_chain'[OF _ DERIV[rule_format], THEN DERIV_cong]
  let ?sum = "\<lambda>t.
    (\<Sum>m<n. (- 1) ^ m * diff m (- 0) / (fact m) * (- h) ^ m) +
    (- 1) ^ n * diff n (- t) / (fact n) * (- h) ^ n"
  from assms have "\<exists>t>0. t < - h \<and> f (- (- h)) = ?sum t"
    by (intro Maclaurin) (auto intro!: derivative_eq_intros DERIV')
  then obtain t where "0 < t" "t < - h" "f (- (- h)) = ?sum t"
    by blast
  moreover have "(- 1) ^ n * diff n (- t) * (- h) ^ n / fact n = diff n (- t) * h ^ n / fact n"
    by (auto simp: power_mult_distrib[symmetric])
  moreover
    have "(\<Sum>m<n. (- 1) ^ m * diff m 0 * (- h) ^ m / fact m) = (\<Sum>m<n. diff m 0 * h ^ m / fact m)"
    by (auto intro: sum.cong simp add: power_mult_distrib[symmetric])
  ultimately have "h < - t \<and> - t < 0 \<and>
    f h = (\<Sum>m<n. diff m 0 / (fact m) * h ^ m) + diff n (- t) / (fact n) * h ^ n"
    by auto
  then show ?thesis ..
qed


subsection \<open>More Convenient "Bidirectional" Version.\<close>

lemma Maclaurin_bi_le:
  fixes n :: nat and x :: real
  assumes "diff 0 = f"
    and DERIV : "\<forall>m t. m < n \<and> \<bar>t\<bar> \<le> \<bar>x\<bar> \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = (\<Sum>m<n. diff m 0 / fact m * x ^ m) + diff n t / fact n * x ^ n"
    (is "\<exists>t. _ \<and> f x = ?f x t")
proof (cases "n = 0")
  case True
  with \<open>diff 0 = f\<close> show ?thesis by force
next
  case False
  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x = 0"
    with \<open>n \<noteq> 0\<close> \<open>diff 0 = f\<close> DERIV have "\<bar>0\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x 0"
      by auto
    then show ?thesis ..
  next
    assume "x < 0"
    with \<open>n \<noteq> 0\<close> DERIV have "\<exists>t>x. t < 0 \<and> diff 0 x = ?f x t"
      by (intro Maclaurin_minus) auto
    then obtain t where "x < t" "t < 0"
      "diff 0 x = (\<Sum>m<n. diff m 0 / fact m * x ^ m) + diff n t / fact n * x ^ n"
      by blast
    with \<open>x < 0\<close> \<open>diff 0 = f\<close> show ?thesis by force
  next
    assume "x > 0"
    with \<open>n \<noteq> 0\<close> \<open>diff 0 = f\<close> DERIV have "\<exists>t>0. t < x \<and> diff 0 x = ?f x t"
      by (intro Maclaurin) auto
    then obtain t where "0 < t" "t < x"
      "diff 0 x = (\<Sum>m<n. diff m 0 / fact m * x ^ m) + diff n t / fact n * x ^ n"
      by blast
    with \<open>x > 0\<close> \<open>diff 0 = f\<close> have "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x t" by simp
    then show ?thesis ..
  qed
qed

lemma Maclaurin_all_lt:
  fixes x :: real
  assumes INIT1: "diff 0 = f"
    and INIT2: "0 < n"
    and INIT3: "x \<noteq> 0"
    and DERIV: "\<forall>m x. DERIV (diff m) x :> diff(Suc m) x"
  shows "\<exists>t. 0 < \<bar>t\<bar> \<and> \<bar>t\<bar> < \<bar>x\<bar> \<and> f x =
      (\<Sum>m<n. (diff m 0 / fact m) * x ^ m) + (diff n t / fact n) * x ^ n"
    (is "\<exists>t. _ \<and> _ \<and> f x = ?f x t")
proof (cases rule: linorder_cases)
  assume "x = 0"
  with INIT3 show ?thesis ..
next
  assume "x < 0"
  with assms have "\<exists>t>x. t < 0 \<and> f x = ?f x t"
    by (intro Maclaurin_minus) auto
  then show ?thesis by force
next
  assume "x > 0"
  with assms have "\<exists>t>0. t < x \<and> f x = ?f x t"
    by (intro Maclaurin) auto
  then show ?thesis by force
qed

lemma Maclaurin_zero: "x = 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> (\<Sum>m<n. (diff m 0 / fact m) * x ^ m) = diff 0 0"
  for x :: real and n :: nat
  by simp


lemma Maclaurin_all_le:
  fixes x :: real and n :: nat
  assumes INIT: "diff 0 = f"
    and DERIV: "\<forall>m x. DERIV (diff m) x :> diff (Suc m) x"
  shows "\<exists>t. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = (\<Sum>m<n. (diff m 0 / fact m) * x ^ m) + (diff n t / fact n) * x ^ n"
    (is "\<exists>t. _ \<and> f x = ?f x t")
proof (cases "n = 0")
  case True
  with INIT show ?thesis by force
next
  case False
  show ?thesis
    using DERIV INIT Maclaurin_bi_le by auto
qed

lemma Maclaurin_all_le_objl:
  "diff 0 = f \<and> (\<forall>m x. DERIV (diff m) x :> diff (Suc m) x) \<longrightarrow>
    (\<exists>t::real. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = (\<Sum>m<n. (diff m 0 / fact m) * x ^ m) + (diff n t / fact n) * x ^ n)"
  for x :: real and n :: nat
  by (blast intro: Maclaurin_all_le)


subsection \<open>Version for Exponential Function\<close>

lemma Maclaurin_exp_lt:
  fixes x :: real and n :: nat
  shows
    "x \<noteq> 0 \<Longrightarrow> n > 0 \<Longrightarrow>
      (\<exists>t. 0 < \<bar>t\<bar> \<and> \<bar>t\<bar> < \<bar>x\<bar> \<and> exp x = (\<Sum>m<n. x ^ m / fact m) + exp t / fact n * x ^ n)"
 using Maclaurin_all_lt [where diff = "\<lambda>n. exp" and f = exp and x = x and n = n] by auto

lemma Maclaurin_exp_le:
  fixes x :: real and n :: nat
  shows "\<exists>t. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and> exp x = (\<Sum>m<n. x ^ m / fact m) + exp t / fact n * x ^ n"
  using Maclaurin_all_le_objl [where diff = "\<lambda>n. exp" and f = exp and x = x and n = n] by auto

corollary exp_lower_Taylor_quadratic: "0 \<le> x \<Longrightarrow> 1 + x + x\<^sup>2 / 2 \<le> exp x"
  for x :: real
  using Maclaurin_exp_le [of x 3] by (auto simp: numeral_3_eq_3 power2_eq_square)

corollary ln_2_less_1: "ln 2 < (1::real)"
  by (smt (verit) ln_eq_minus_one ln_le_minus_one)

subsection \<open>Version for Sine Function\<close>

lemma mod_exhaust_less_4: "m mod 4 = 0 \<or> m mod 4 = 1 \<or> m mod 4 = 2 \<or> m mod 4 = 3"
  for m :: nat
  by auto


lemma sin_coeff_lemma: "sin_coeff m = sin (0 + 1/2 * real m * pi) / fact m"
  by (auto simp: sin_add sin_zero_iff sin_coeff_def algebra_simps add_divide_distrib elim!: oddE)

lemma Maclaurin_sin_expansion2:
  "\<exists>t. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and>
    sin x = (\<Sum>m<n. sin_coeff m * x ^ m) + sin (t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding sin_coeff_lemma
  apply (rule Maclaurin_all_le)
  by (auto simp: ring_distribs add_divide_distrib sin_add cos_add intro!: derivative_eq_intros)

lemma Maclaurin_sin_expansion:
  "\<exists>t. sin x = (\<Sum>m<n. sin_coeff m * x ^ m) + sin (t + 1/2 * real n * pi) / fact n * x ^ n"
  using Maclaurin_sin_expansion2 [of x n] by blast

lemma Maclaurin_sin_expansion3:
  assumes "n > 0" "x > 0"
    shows "\<exists>t. 0 < t \<and> t < x \<and>
          sin x = (\<Sum>m<n. sin_coeff m * x ^ m) + sin (t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding sin_coeff_lemma
  apply (rule Maclaurin)
  by (auto intro!: derivative_eq_intros simp: assms ring_distribs sin_add cos_add)

lemma Maclaurin_sin_expansion4:
  assumes "0 < x"
  shows "\<exists>t. 0 < t \<and> t \<le> x \<and> sin x = (\<Sum>m<n. sin_coeff m * x ^ m) + sin (t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding sin_coeff_lemma
  apply (rule Maclaurin2)
  by (auto intro!: derivative_eq_intros simp: assms ring_distribs sin_add cos_add)


subsection \<open>Maclaurin Expansion for Cosine Function\<close>

lemma sumr_cos_zero_one [simp]: "(\<Sum>m<Suc n. cos_coeff m * 0 ^ m) = 1"
  by (induct n) auto

lemma cos_add_pi_half_add: "cos (x + (pi/2 + y)) = - sin (x + y)"
  by (auto simp: cos_add sin_add)

lemma cos_coeff_lemma: "cos_coeff m = cos (0 + 1/2 * real m * pi) / fact m"
  by (cases "even m") (auto simp add: cos_coeff_def cos_zero_iff)

lemma Maclaurin_cos_expansion:
  "\<exists>t::real. \<bar>t\<bar> \<le> \<bar>x\<bar> \<and>
    cos x = (\<Sum>m<n. cos_coeff m * x ^ m) + cos(t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding cos_coeff_lemma
  apply (rule Maclaurin_all_le)
  by (simp_all add: ring_distribs cos_add_pi_half_add)

lemma Maclaurin_cos_expansion2:
  assumes "x > 0" "n > 0"
  shows "\<exists>t. 0 < t \<and> t < x \<and>
      cos x = (\<Sum>m<n. cos_coeff m * x ^ m) + cos (t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding cos_coeff_lemma
  apply (rule Maclaurin)
  by (simp_all add: assms ring_distribs cos_add_pi_half_add)

lemma Maclaurin_minus_cos_expansion:
  assumes "n > 0" "x < 0"
  shows "\<exists>t. x < t \<and> t < 0 \<and>
         cos x = (\<Sum>m<n. cos_coeff m * x ^ m) + cos (t + 1/2 * real n * pi) / fact n * x ^ n"
  unfolding cos_coeff_lemma
  apply (rule Maclaurin_minus)
  by (simp_all add: assms ring_distribs cos_add_pi_half_add)


(* Version for ln(1 +/- x). Where is it?? *)


lemma sin_bound_lemma: "x = y \<Longrightarrow> \<bar>u\<bar> \<le> v \<Longrightarrow> \<bar>(x + u) - y\<bar> \<le> v"
  for x y u v :: real
  by auto

lemma Maclaurin_sin_bound: "\<bar>sin x - (\<Sum>m<n. sin_coeff m * x ^ m)\<bar> \<le> inverse (fact n) * \<bar>x\<bar> ^ n"
proof -
  have est: "x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x * y \<le> 1 * y" for x y :: real
    by (rule mult_right_mono) simp_all
  let ?diff = "\<lambda>(n::nat) (x::real).
    if n mod 4 = 0 then sin x
    else if n mod 4 = 1 then cos x
    else if n mod 4 = 2 then - sin x
    else - cos x"
  have diff_0: "?diff 0 = sin" by simp
  have "DERIV (?diff m) x :> ?diff (Suc m) x" for m and x
    using mod_exhaust_less_4 [of m]
    by (auto simp: mod_Suc intro!: derivative_eq_intros)
  then have DERIV_diff: "\<forall>m x. DERIV (?diff m) x :> ?diff (Suc m) x"
    by blast
  from Maclaurin_all_le [OF diff_0 DERIV_diff]
  obtain t where t1: "\<bar>t\<bar> \<le> \<bar>x\<bar>"
    and t2: "sin x = (\<Sum>m<n. ?diff m 0 / (fact m) * x ^ m) + ?diff n t / (fact n) * x ^ n"
    by fast
  have diff_m_0: "?diff m 0 = (if even m then 0 else (- 1) ^ ((m - Suc 0) div 2))" for m
    using mod_exhaust_less_4 [of m]
    by (auto simp: minus_one_power_iff even_even_mod_4_iff [of m] dest: even_mod_4_div_2 odd_mod_4_div_2)
  show ?thesis
    apply (subst t2)
    apply (rule sin_bound_lemma)
     apply (rule sum.cong[OF refl])
    apply (simp add: diff_m_0 sin_coeff_def)
    using est
    apply (auto intro: mult_right_mono [where b=1, simplified] mult_right_mono
        simp: ac_simps divide_inverse power_abs [symmetric] abs_mult)
    done
qed


section \<open>Taylor series\<close>

text \<open>
  We use MacLaurin and the translation of the expansion point \<open>c\<close> to \<open>0\<close>
  to prove Taylor's theorem.
\<close>

lemma Taylor_up:
  assumes INIT: "n > 0" "diff 0 = f"
    and DERIV: "\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> b \<longrightarrow> DERIV (diff m) t :> (diff (Suc m) t)"
    and INTERV: "a \<le> c" "c < b"
  shows "\<exists>t::real. c < t \<and> t < b \<and>
    f b = (\<Sum>m<n. (diff m c / fact m) * (b - c)^m) + (diff n t / fact n) * (b - c)^n"
proof -
  from INTERV have "0 < b - c" by arith
  moreover from INIT have "n > 0" "(\<lambda>m x. diff m (x + c)) 0 = (\<lambda>x. f (x + c))"
    by auto
  moreover
  have "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> b - c \<longrightarrow> DERIV (\<lambda>x. diff m (x + c)) t :> diff (Suc m) (t + c)"
  proof (intro strip)
    fix m t
    assume "m < n \<and> 0 \<le> t \<and> t \<le> b - c"
    with DERIV and INTERV have "DERIV (diff m) (t + c) :> diff (Suc m) (t + c)"
      by auto
    moreover from DERIV_ident and DERIV_const have "DERIV (\<lambda>x. x + c) t :> 1 + 0"
      by (rule DERIV_add)
    ultimately have "DERIV (\<lambda>x. diff m (x + c)) t :> diff (Suc m) (t + c) * (1 + 0)"
      by (rule DERIV_chain2)
    then show "DERIV (\<lambda>x. diff m (x + c)) t :> diff (Suc m) (t + c)"
      by simp
  qed
  ultimately obtain x where
    "0 < x \<and> x < b - c \<and>
      f (b - c + c) =
        (\<Sum>m<n. diff m (0 + c) / fact m * (b - c) ^ m) + diff n (x + c) / fact n * (b - c) ^ n"
     by (rule Maclaurin [THEN exE])
  then show ?thesis
    by (smt (verit) sum.cong)
qed

lemma Taylor_down:
  fixes a :: real and n :: nat
  assumes INIT: "n > 0" "diff 0 = f"
    and DERIV: "(\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> b \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t)"
    and INTERV: "a < c" "c \<le> b"
  shows "\<exists>t. a < t \<and> t < c \<and>
    f a = (\<Sum>m<n. (diff m c / fact m) * (a - c)^m) + (diff n t / fact n) * (a - c)^n"
proof -
  from INTERV have "a-c < 0" by arith
  moreover from INIT have "n > 0" "(\<lambda>m x. diff m (x + c)) 0 = (\<lambda>x. f (x + c))"
    by auto
  moreover
  have "\<forall>m t. m < n \<and> a - c \<le> t \<and> t \<le> 0 \<longrightarrow> DERIV (\<lambda>x. diff m (x + c)) t :> diff (Suc m) (t + c)"
  proof (rule allI impI)+
    fix m t
    assume "m < n \<and> a - c \<le> t \<and> t \<le> 0"
    with DERIV and INTERV have "DERIV (diff m) (t + c) :> diff (Suc m) (t + c)"
      by auto
    moreover from DERIV_ident and DERIV_const have "DERIV (\<lambda>x. x + c) t :> 1 + 0"
      by (rule DERIV_add)
    ultimately show "DERIV (\<lambda>x. diff m (x + c)) t :> diff (Suc m) (t + c)"
      using DERIV_chain2 DERIV_shift by blast
  qed
  ultimately obtain x where
    "a - c < x \<and> x < 0 \<and>
      f (a - c + c) =
        (\<Sum>m<n. diff m (0 + c) / fact m * (a - c) ^ m) + diff n (x + c) / fact n * (a - c) ^ n"
    by (rule Maclaurin_minus [THEN exE])
  then have "a < x + c \<and> x + c < c \<and>
    f a = (\<Sum>m<n. diff m c / fact m * (a - c) ^ m) + diff n (x + c) / fact n * (a - c) ^ n"
    by fastforce
  then show ?thesis by fastforce
qed

theorem Taylor:
  fixes a :: real and n :: nat
  assumes INIT: "n > 0" "diff 0 = f"
    and DERIV: "\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> b \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    and INTERV: "a \<le> c " "c \<le> b" "a \<le> x" "x \<le> b" "x \<noteq> c"
  shows "\<exists>t.
    (if x < c then x < t \<and> t < c else c < t \<and> t < x) \<and>
    f x = (\<Sum>m<n. (diff m c / fact m) * (x - c)^m) + (diff n t / fact n) * (x - c)^n"
proof (cases "x < c")
  case True
  note INIT
  moreover have "\<forall>m t. m < n \<and> x \<le> t \<and> t \<le> b \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    using DERIV and INTERV by fastforce
  ultimately show ?thesis
    using True INTERV Taylor_down by simp
next
  case False
  note INIT
  moreover have "\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> x \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    using DERIV and INTERV by fastforce
  ultimately show ?thesis 
    using Taylor_up INTERV False by simp
qed

end

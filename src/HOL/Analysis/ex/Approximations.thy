section \<open>Numeric approximations to Constants\<close>

theory Approximations
imports "HOL-Analysis.Complex_Transcendental" "HOL-Analysis.Harmonic_Numbers"
begin

text \<open>
  In this theory, we will approximate some standard mathematical constants with high precision,
  using only Isabelle's simplifier. (no oracles, code generator, etc.)
  
  The constants we will look at are: $\pi$, $e$, $\ln 2$, and $\gamma$ (the Euler--Mascheroni
  constant).
\<close>

lemma eval_fact:
  "fact 0 = 1"
  "fact (Suc 0) = 1"
  "fact (numeral n) = numeral n * fact (pred_numeral n)"
  by (simp, simp, simp_all only: numeral_eq_Suc fact_Suc,
      simp only: numeral_eq_Suc [symmetric] of_nat_numeral)

lemma sum_poly_horner_expand:
  "(\<Sum>k<(numeral n::nat). f k * x^k) = f 0 + (\<Sum>k<pred_numeral n. f (k+1) * x^k) * x"
  "(\<Sum>k<Suc 0. f k * x^k) = (f 0 :: 'a :: semiring_1)"
  "(\<Sum>k<(0::nat). f k * x^k) = 0"
proof -
  {
    fix m :: nat
    have "(\<Sum>k<Suc m. f k * x^k) = f 0 + (\<Sum>k=Suc 0..<Suc m. f k * x^k)"
      by (subst atLeast0LessThan [symmetric], subst sum.atLeast_Suc_lessThan) simp_all
    also have "(\<Sum>k=Suc 0..<Suc m. f k * x^k) = (\<Sum>k<m. f (k+1) * x^k) * x"
      by (subst sum.shift_bounds_Suc_ivl)
         (simp add: sum_distrib_right algebra_simps atLeast0LessThan power_commutes)
    finally have "(\<Sum>k<Suc m. f k * x ^ k) = f 0 + (\<Sum>k<m. f (k + 1) * x ^ k) * x" .
  }
  from this[of "pred_numeral n"]
    show "(\<Sum>k<numeral n. f k * x^k) = f 0 + (\<Sum>k<pred_numeral n. f (k+1) * x^k) * x"
    by (simp add: numeral_eq_Suc)
qed simp_all

lemma power_less_one:
  assumes "n > 0" "x \<ge> 0" "x < 1"
  shows   "x ^ n < (1::'a::linordered_semidom)"
proof -
  from assms consider "x > 0" | "x = 0" by force
  thus ?thesis
  proof cases
    assume "x > 0"
    with assms show ?thesis
      by (cases n) (simp, hypsubst, rule power_Suc_less_one)
  qed (insert assms, cases n, simp_all)
qed

lemma combine_bounds:
  "x \<in> {a1..b1} \<Longrightarrow> y \<in> {a2..b2} \<Longrightarrow> a3 = a1 + a2 \<Longrightarrow> b3 = b1 + b2 \<Longrightarrow> x + y \<in> {a3..(b3::real)}"
  "x \<in> {a1..b1} \<Longrightarrow> y \<in> {a2..b2} \<Longrightarrow> a3 = a1 - b2 \<Longrightarrow> b3 = b1 - a2 \<Longrightarrow> x - y \<in> {a3..(b3::real)}"
  "c \<ge> 0 \<Longrightarrow> x \<in> {a..b} \<Longrightarrow> c * x \<in> {c*a..c*b}"
  by (auto simp: mult_left_mono)

lemma approx_coarsen:
  "\<bar>x - a1\<bar> \<le> eps1 \<Longrightarrow> \<bar>a1 - a2\<bar> \<le> eps2 - eps1 \<Longrightarrow> \<bar>x - a2\<bar> \<le> (eps2 :: real)"
  by simp



subsection \<open>Approximations of the exponential function\<close>

lemma two_power_fact_le_fact:
  assumes "n \<ge> 1"
  shows   "2^k * fact n \<le> (fact (n + k) :: 'a :: {semiring_char_0,linordered_semidom})"
proof (induction k)
  case (Suc k)
  have "2 ^ Suc k * fact n = 2 * (2 ^ k * fact n)" by (simp add: algebra_simps)
  also note Suc.IH
  also from assms have "of_nat 1 + of_nat 1 \<le> of_nat n + (of_nat (Suc k) :: 'a)"
    by (intro add_mono) (unfold of_nat_le_iff, simp_all)
  hence "2 * (fact (n + k) :: 'a) \<le> of_nat (n + Suc k) * fact (n + k)"
    by (intro mult_right_mono) (simp_all add: add_ac)
  also have "\<dots> = fact (n + Suc k)" by simp
  finally show ?case by - (simp add: mult_left_mono)
qed simp_all

text \<open>
  We approximate the exponential function with inputs between $0$ and $2$ by its
  Taylor series expansion and bound the error term with $0$ from below and with a 
  geometric series from above.
\<close>
lemma exp_approx:
  assumes "n > 0" "0 \<le> x" "x < 2"
  shows   "exp (x::real) - (\<Sum>k<n. x^k / fact k) \<in> {0..(2 * x^n / (2 - x)) / fact n}"
proof (unfold atLeastAtMost_iff, safe)
  define approx where "approx = (\<Sum>k<n. x^k / fact k)"
  have "(\<lambda>k. x^k / fact k) sums exp x"
    using exp_converges[of x] by (simp add: field_simps)
  from sums_split_initial_segment[OF this, of n]
    have sums: "(\<lambda>k. x^n * (x^k / fact (n+k))) sums (exp x - approx)"
    by (simp add: approx_def algebra_simps power_add)

  from assms show "(exp x - approx) \<ge> 0"
    by (intro sums_le[OF _ sums_zero sums]) auto

  have "x^n * (x^k / fact (n+k)) \<le> (x^n / fact n) * (x / 2)^k" for k::nat
  proof -
    have "x^n * (x^k / fact (n + k)) = x^(n+k) / fact (n + k)" by (simp add: power_add)
    also from assms have "\<dots> \<le> x^(n+k) / (2^k * fact n)"
      by (intro divide_left_mono two_power_fact_le_fact zero_le_power) simp_all
    also have "\<dots> = (x^n / fact n) * (x / 2) ^ k"
      by (simp add: field_simps power_add)
    finally show "x^n * (x^k / fact (n+k)) \<le> (x^n / fact n) * (x / 2)^k" .
  qed
  moreover note sums
  moreover {
    from assms have "(\<lambda>k. (x^n / fact n) * (x / 2)^k) sums ((x^n / fact n) * (1 / (1 - x / 2)))"
      by (intro sums_mult geometric_sums) simp_all
    also from assms have "((x^n / fact n) * (1 / (1 - x / 2))) = (2 * x^n / (2 - x)) / fact n"
      by (auto simp: field_split_simps)
    finally have "(\<lambda>k. (x^n / fact n) * (x / 2)^k) sums \<dots>" .
  }
  ultimately show "(exp x - approx) \<le> (2 * x^n / (2 - x)) / fact n"
    by (rule sums_le)
qed

text \<open>
  The following variant gives a simpler error estimate for inputs between $0$ and $1$:  
\<close>
lemma exp_approx':
  assumes "n > 0" "0 \<le> x" "x \<le> 1"
  shows   "\<bar>exp (x::real) - (\<Sum>k\<le>n. x^k / fact k)\<bar> \<le> x ^ n / fact n"
proof -
  from assms have "x^n / (2 - x) \<le> x^n / 1" by (intro frac_le) simp_all 
  hence "(2 * x^n / (2 - x)) / fact n \<le> 2 * x^n / fact n"
    using assms by (simp add: field_split_simps)
  with exp_approx[of n x] assms
    have "exp (x::real) - (\<Sum>k<n. x^k / fact k) \<in> {0..2 * x^n / fact n}" by simp
  moreover have "(\<Sum>k\<le>n. x^k / fact k) = (\<Sum>k<n. x^k / fact k) + x ^ n / fact n"
    by (simp add: lessThan_Suc_atMost [symmetric])
  ultimately show "\<bar>exp (x::real) - (\<Sum>k\<le>n. x^k / fact k)\<bar> \<le> x ^ n / fact n"
    unfolding atLeastAtMost_iff by linarith
qed

text \<open>
  By adding $x^n / n!$ to the approximation (i.e. taking one more term from the
  Taylor series), one can get the error bound down to $x^n / n!$.
  
  This means that the number of accurate binary digits produced by the approximation is
  asymptotically equal to $(n \log n - n) / \log 2$ by Stirling's formula.
\<close>
lemma exp_approx'':
  assumes "n > 0" "0 \<le> x" "x \<le> 1"
  shows   "\<bar>exp (x::real) - (\<Sum>k\<le>n. x^k / fact k)\<bar> \<le> 1 / fact n"
proof -
  from assms have "\<bar>exp x - (\<Sum>k\<le>n. x ^ k / fact k)\<bar> \<le> x ^ n / fact n"
    by (rule exp_approx')
  also from assms have "\<dots> \<le> 1 / fact n" by (simp add: field_split_simps power_le_one)
  finally show ?thesis .
qed


text \<open>
  We now define an approximation function for Euler's constant $e$.  
\<close>

definition euler_approx :: "nat \<Rightarrow> real" where
  "euler_approx n = (\<Sum>k\<le>n. inverse (fact k))"

definition euler_approx_aux :: "nat \<Rightarrow> nat" where
  "euler_approx_aux n = (\<Sum>k\<le>n. \<Prod>{k + 1..n})"

lemma exp_1_approx:
  "n > 0 \<Longrightarrow> \<bar>exp (1::real) - euler_approx n\<bar> \<le> 1 / fact n"
  using exp_approx''[of n 1] by (simp add: euler_approx_def field_split_simps)

text \<open>
  The following allows us to compute the numerator and the denominator of the result
  separately, which greatly reduces the amount of rational number arithmetic that we
  have to do.
\<close>
lemma euler_approx_altdef [code]:
  "euler_approx n = real (euler_approx_aux n) / real (fact n)"
proof -
  have "real (\<Sum>k\<le>n. \<Prod>{k+1..n}) = (\<Sum>k\<le>n. \<Prod>i=k+1..n. real i)" by simp
  also have "\<dots> / fact n = (\<Sum>k\<le>n. 1 / (fact n / (\<Prod>i=k+1..n. real i)))"
    by (simp add: sum_divide_distrib)
  also have "\<dots> = (\<Sum>k\<le>n. 1 / fact k)"
  proof (intro sum.cong refl)
    fix k assume k: "k \<in> {..n}"
    have "fact n = (\<Prod>i=1..n. real i)" by (simp add: fact_prod)
    also from k have "{1..n} = {1..k} \<union> {k+1..n}" by auto
    also have "prod real \<dots> / (\<Prod>i=k+1..n. real i) = (\<Prod>i=1..k. real i)"
      by (subst nonzero_divide_eq_eq, simp, subst prod.union_disjoint [symmetric]) auto
    also have "\<dots> = fact k" by (simp add: fact_prod)
    finally show "1 / (fact n / prod real {k + 1..n}) = 1 / fact k" by simp
  qed
  also have "\<dots> = euler_approx n" by (simp add: euler_approx_def field_simps)
  finally show ?thesis by (simp add: euler_approx_aux_def)
qed

lemma euler_approx_aux_Suc:
  "euler_approx_aux (Suc m) = 1 + Suc m * euler_approx_aux m"
  unfolding euler_approx_aux_def
  by (subst sum_distrib_left) (simp add: atLeastAtMostSuc_conv mult.commute)

lemma eval_euler_approx_aux:
  "euler_approx_aux 0 = 1"
  "euler_approx_aux 1 = 2"
  "euler_approx_aux (Suc 0) = 2"
  "euler_approx_aux (numeral n) = 1 + numeral n * euler_approx_aux (pred_numeral n)" (is "?th")
proof -
  have A: "euler_approx_aux (Suc m) = 1 + Suc m * euler_approx_aux m" for m :: nat
    unfolding euler_approx_aux_def
    by (subst sum_distrib_left) (simp add: atLeastAtMostSuc_conv mult.commute)
  show ?th by (subst numeral_eq_Suc, subst A, subst numeral_eq_Suc [symmetric]) simp
qed (simp_all add: euler_approx_aux_def)

lemma euler_approx_aux_code [code]:
  "euler_approx_aux n = (if n = 0 then 1 else 1 + n * euler_approx_aux (n - 1))"
  by (cases n) (simp_all add: eval_euler_approx_aux euler_approx_aux_Suc)

lemmas eval_euler_approx = euler_approx_altdef eval_euler_approx_aux


text \<open>Approximations of $e$ to 60 decimals / 128 and 64 bits:\<close>

lemma euler_60_decimals:
  "\<bar>exp 1 - 2.718281828459045235360287471352662497757247093699959574966968\<bar> 
      \<le> inverse (10^60::real)"
  by (rule approx_coarsen, rule exp_1_approx[of 48])
     (simp_all add: eval_euler_approx eval_fact)

lemma euler_128:
  "\<bar>exp 1 - 924983374546220337150911035843336795079 / 2 ^ 128\<bar> \<le> inverse (2 ^ 128 :: real)"
  by (rule approx_coarsen[OF euler_60_decimals]) simp_all

lemma euler_64:
  "\<bar>exp 1 - 50143449209799256683 / 2 ^ 64\<bar> \<le> inverse (2 ^ 64 :: real)"
  by (rule approx_coarsen[OF euler_128]) simp_all

text \<open>
  An approximation of $e$ to 60 decimals. This is about as far as we can go with the 
  simplifier with this kind of setup; the exported code of the code generator, on the other
  hand, can easily approximate $e$ to 1000 decimals and verify that approximation within
  fractions of a second.
\<close>

(* (Uncommented because we don't want to use the code generator; 
   don't forget to import Code\_Target\_Numeral)) *)
(*
lemma "\<bar>exp 1 - 2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307381323286279434907632338298807531952510190115738341879307021540891499348841675092447614606680822648001684774118537423454424371075390777449920695517027618386062613313845830007520449338265602976067371132007093287091274437470472306969772093101416928368190255151086574637721112523897844250569536967707854499699679468644549059879316368892300987931277361782154249992295763514822082698951936680331825288693984964651058209392398294887933203625094431173012381970684161403970198376793206832823764648042953118023287825098194558153017567173613320698112509961818815930416903515988885193458072738667385894228792284998920868058257492796104841984443634632449684875602336248270419786232090021609902353043699418491463140934317381436405462531520961836908887070167683964243781405927145635490613031072085103837505101157477041718986106873969655212671546889570350354021\<bar>
  \<le> inverse (10^1000::real)"
  by (rule approx_coarsen, rule exp_1_approx[of 450], simp) eval
*)


subsection \<open>Approximation of $\ln 2$\<close>

text \<open>
  The following three auxiliary constants allow us to force the simplifier to
  evaluate intermediate results, simulating call-by-value.
\<close>

definition "ln_approx_aux3 x' e n y d \<longleftrightarrow> 
  \<bar>(2 * y) * (\<Sum>k<n. inverse (real (2*k+1)) * (y^2)^k) + d - x'\<bar> \<le> e - d"
definition "ln_approx_aux2 x' e n y \<longleftrightarrow> 
  ln_approx_aux3 x' e n y (y^(2*n+1) / (1 - y^2) / real (2*n+1))" 
definition "ln_approx_aux1 x' e n x \<longleftrightarrow> 
  ln_approx_aux2 x' e n ((x - 1) / (x + 1))"

lemma ln_approx_abs'':
  fixes x :: real and n :: nat
  defines "y \<equiv> (x-1)/(x+1)"
  defines "approx \<equiv> (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))"
  defines "d \<equiv> y^(2*n+1) / (1 - y^2) / of_nat (2*n+1)"
  assumes x: "x > 1"
  assumes A: "ln_approx_aux1 x' e n x"  
  shows   "\<bar>ln x - x'\<bar> \<le> e"
proof (rule approx_coarsen[OF ln_approx_abs[OF x, of n]], goal_cases)
  case 1
  from A have "\<bar>2 * y * (\<Sum>k<n. inverse (real (2 * k + 1)) * y\<^sup>2 ^ k) + d - x'\<bar> \<le> e - d"
    by (simp only: ln_approx_aux3_def ln_approx_aux2_def ln_approx_aux1_def
                   y_def [symmetric] d_def [symmetric])
  also have "2 * y * (\<Sum>k<n. inverse (real (2 * k + 1)) * y\<^sup>2 ^ k) = 
               (\<Sum>k<n. 2 * y^(2*k+1) / (real (2 * k + 1)))"
    by (subst sum_distrib_left, simp, subst power_mult) 
       (simp_all add: field_split_simps mult_ac power_mult)
  finally show ?case by (simp only: d_def y_def approx_def) 
qed

text \<open>
  We unfold the above three constants successively and then compute the 
  sum using a Horner scheme.
\<close>
lemma ln_2_40_decimals: 
  "\<bar>ln 2 - 0.6931471805599453094172321214581765680755\<bar> 
      \<le> inverse (10^40 :: real)"
  apply (rule ln_approx_abs''[where n = 40], simp)
  apply (simp, simp add: ln_approx_aux1_def)
  apply (simp add: ln_approx_aux2_def power2_eq_square power_divide)
  apply (simp add: ln_approx_aux3_def power2_eq_square)
  apply (simp add: sum_poly_horner_expand)
  done
     
lemma ln_2_128: 
  "\<bar>ln 2 - 235865763225513294137944142764154484399 / 2 ^ 128\<bar> \<le> inverse (2 ^ 128 :: real)"
  by (rule approx_coarsen[OF ln_2_40_decimals]) simp_all
     
lemma ln_2_64: 
  "\<bar>ln 2 - 12786308645202655660 / 2 ^ 64\<bar> \<le> inverse (2 ^ 64 :: real)"
  by (rule approx_coarsen[OF ln_2_128]) simp_all  



subsection \<open>Approximation of the Euler--Mascheroni constant\<close>

text \<open>
  Unfortunatly, the best approximation we have formalised for the Euler--Mascheroni 
  constant converges only quadratically. This is too slow to compute more than a 
  few decimals, but we can get almost 4 decimals / 14 binary digits this way, 
  which is not too bad. 
\<close>
lemma euler_mascheroni_approx:
  defines "approx \<equiv> 0.577257 :: real" and "e \<equiv> 0.000063 :: real"
  shows   "abs (euler_mascheroni - approx :: real) < e"
  (is "abs (_ - ?approx) < ?e")
proof -
  define l :: real
    where "l = 47388813395531028639296492901910937/82101866951584879688289000000000000"
  define u :: real
    where "u = 142196984054132045946501548559032969 / 246305600854754639064867000000000000"
  have impI: "P \<longrightarrow> Q" if Q for P Q using that by blast
  have hsum_63: "harm 63 = (310559566510213034489743057 / 65681493561267903750631200 :: real)"
    by (simp add: harm_expand)
  from harm_Suc[of 63] have hsum_64: "harm 64 =
          623171679694215690971693339 / (131362987122535807501262400::real)"
    by (subst (asm) hsum_63) simp
  have "ln (64::real) = real (6::nat) * ln 2" by (subst ln_realpow[symmetric]) simp_all
  hence "ln (real_of_nat (Suc 63)) \<in> {4.158883083293<..<4.158883083367}" using ln_2_64
    by (simp add: abs_real_def split: if_split_asm)
  from euler_mascheroni_bounds'[OF _ this]
    have "(euler_mascheroni :: real) \<in> {l<..<u}"
    by (simp add: hsum_63 del: greaterThanLessThan_iff) (simp only: l_def u_def)
  also have "\<dots> \<subseteq> {approx - e<..<approx + e}"
    by (subst greaterThanLessThan_subseteq_greaterThanLessThan, rule impI)
       (simp add: approx_def e_def u_def l_def)
  finally show ?thesis by (simp add: abs_real_def)
qed



subsection \<open>Approximation of pi\<close>


subsubsection \<open>Approximating the arctangent\<close>

text\<open>
  The arctangent can be used to approximate pi. Fortunately, its Taylor series expansion
  converges exponentially for small values, so we can get $\Theta(n)$ digits of precision
  with $n$ summands of the expansion.
\<close>

definition arctan_approx where
  "arctan_approx n x = x * (\<Sum>k<n. (-(x^2))^k / real (2*k+1))"

lemma arctan_series':
  assumes "\<bar>x\<bar> \<le> 1"
  shows "(\<lambda>k. (-1)^k * (1 / real (k*2+1) * x ^ (k*2+1))) sums arctan x"
  using summable_arctan_series[OF assms] arctan_series[OF assms] by (simp add: sums_iff)

lemma arctan_approx:
  assumes x: "0 \<le> x" "x < 1" and n: "even n"
  shows   "arctan x - arctan_approx n x \<in> {0..x^(2*n+1) / (1-x^4)}"
proof -
  define c where "c k = 1 / (1+(4*real k + 2*real n)) - x\<^sup>2 / (3+(4*real k + 2*real n))" for k
  from assms have "(\<lambda>k. (-1) ^ k * (1 / real (k * 2 + 1) * x^(k*2+1))) sums arctan x"
    using arctan_series' by simp
  also have "(\<lambda>k. (-1) ^ k * (1 / real (k * 2 + 1) * x^(k*2+1))) =
                 (\<lambda>k. x * ((- (x^2))^k / real (2*k+1)))"
    by (simp add: power2_eq_square power_mult power_mult_distrib mult_ac power_minus')
  finally have "(\<lambda>k. x * ((- x\<^sup>2) ^ k / real (2 * k + 1))) sums arctan x" .
  from sums_split_initial_segment[OF this, of n]
    have "(\<lambda>i. x * ((- x\<^sup>2) ^ (i + n) / real (2 * (i + n) + 1))) sums
            (arctan x - arctan_approx n x)"
    by (simp add: arctan_approx_def sum_distrib_left)
  from sums_group[OF this, of 2] assms
    have sums: "(\<lambda>k. x * (x\<^sup>2)^n * (x^4)^k * c k) sums (arctan x - arctan_approx n x)"
    by (simp add: algebra_simps power_add power_mult [symmetric] c_def)

  from assms have "0 \<le> arctan x - arctan_approx n x"
    by (intro sums_le[OF _ sums_zero sums] allI mult_nonneg_nonneg)
       (auto intro!: frac_le power_le_one simp: c_def)
  moreover {
    from assms have "c k \<le> 1 - 0" for k unfolding c_def
      by (intro diff_mono divide_nonneg_nonneg add_nonneg_nonneg) auto
    with assms have "x * x\<^sup>2 ^ n * (x ^ 4) ^ k * c k \<le> x * x\<^sup>2 ^ n * (x ^ 4) ^ k * 1" for k
      by (intro mult_left_mono mult_right_mono mult_nonneg_nonneg) simp_all
    with assms have "arctan x - arctan_approx n x \<le> x * (x\<^sup>2)^n * (1 / (1 - x^4))"
      by (intro sums_le[OF _ sums sums_mult[OF geometric_sums]] allI mult_left_mono)
         (auto simp: power_less_one)
    also have "x * (x^2)^n = x^(2*n+1)" by (simp add: power_mult power_add)
    finally have "arctan x - arctan_approx n x \<le> x^(2*n+1) / (1 - x^4)" by simp
  }
  ultimately show ?thesis by simp
qed

lemma arctan_approx_def': "arctan_approx n (1/x) =
  (\<Sum>k<n. inverse (real (2 * k + 1) * (- x\<^sup>2) ^ k)) / x"
proof -
  have "(-1)^k / b = 1 / ((-1)^k * b)" for k :: nat and b :: real
    by (cases "even k") auto
  thus ?thesis by (simp add: arctan_approx_def  field_simps power_minus')
qed

lemma expand_arctan_approx:
  "(\<Sum>k<(numeral n::nat). inverse (f k) * inverse (x ^ k)) =
     inverse (f 0) + (\<Sum>k<pred_numeral n. inverse (f (k+1)) * inverse (x^k)) / x"
  "(\<Sum>k<Suc 0. inverse (f k) * inverse (x^k)) = inverse (f 0 :: 'a :: field)"
  "(\<Sum>k<(0::nat). inverse (f k) * inverse (x^k)) = 0"
proof -
  {
    fix m :: nat
    have "(\<Sum>k<Suc m. inverse (f k * x^k)) =
             inverse (f 0) + (\<Sum>k=Suc 0..<Suc m. inverse (f k * x^k))"
      by (subst atLeast0LessThan [symmetric], subst sum.atLeast_Suc_lessThan) simp_all
    also have "(\<Sum>k=Suc 0..<Suc m. inverse (f k * x^k)) = (\<Sum>k<m. inverse (f (k+1) * x^k)) / x"
      by (subst sum.shift_bounds_Suc_ivl)
         (simp add: sum_distrib_left divide_inverse algebra_simps
                    atLeast0LessThan power_commutes)
    finally have "(\<Sum>k<Suc m. inverse (f k) * inverse (x ^ k)) =
                      inverse (f 0) + (\<Sum>k<m. inverse (f (k + 1)) * inverse (x ^ k)) / x" by simp
  }
  from this[of "pred_numeral n"]
    show "(\<Sum>k<numeral n. inverse (f k) * inverse (x^k)) =
            inverse (f 0) + (\<Sum>k<pred_numeral n. inverse (f (k+1)) * inverse (x^k)) / x"
    by (simp add: numeral_eq_Suc)
qed simp_all

lemma arctan_diff_small:
  assumes "\<bar>x*y::real\<bar> < 1"
  shows   "arctan x - arctan y = arctan ((x - y) / (1 + x * y))"
proof -
  have "arctan x - arctan y = arctan x + arctan (-y)" by (simp add: arctan_minus)
  also from assms have "\<dots> = arctan ((x - y) / (1 + x * y))" by (subst arctan_add_small) simp_all
  finally show ?thesis .
qed


subsubsection \<open>Machin-like formulae for pi\<close>

text \<open>
  We first define a small proof method that can prove Machin-like formulae for \<^term>\<open>pi\<close>
  automatically. Unfortunately, this takes far too much time for larger formulae because
  the numbers involved become too large.
\<close>

definition "MACHIN_TAG a b \<equiv> a * (b::real)"

lemma numeral_horner_MACHIN_TAG:
  "MACHIN_TAG Numeral1 x = x"
  "MACHIN_TAG (numeral (Num.Bit0 (Num.Bit0 n))) x =
     MACHIN_TAG 2 (MACHIN_TAG (numeral (Num.Bit0 n)) x)"
  "MACHIN_TAG (numeral (Num.Bit0 (Num.Bit1 n))) x =
     MACHIN_TAG 2 (MACHIN_TAG (numeral (Num.Bit1 n)) x)"
  "MACHIN_TAG (numeral (Num.Bit1 n)) x =
     MACHIN_TAG 2 (MACHIN_TAG (numeral n) x) + x"
  unfolding numeral_Bit0 numeral_Bit1 ring_distribs one_add_one[symmetric] MACHIN_TAG_def
     by (simp_all add: algebra_simps)

lemma tag_machin: "a * arctan b = MACHIN_TAG a (arctan b)" by (simp add: MACHIN_TAG_def)

lemma arctan_double': "\<bar>a::real\<bar> < 1 \<Longrightarrow> MACHIN_TAG 2 (arctan a) = arctan (2 * a / (1 - a*a))"
  unfolding MACHIN_TAG_def by (simp add: arctan_double power2_eq_square)

ML \<open>
  fun machin_term_conv ctxt ct =
    let
      val ctxt' = ctxt |> Simplifier.add_simps @{thms arctan_double' arctan_add_small}
    in
      case Thm.term_of ct of
        Const (\<^const_name>\<open>MACHIN_TAG\<close>, _) $ _ $
          (Const (\<^const_name>\<open>Transcendental.arctan\<close>, _) $ _) =>
          Simplifier.rewrite ctxt' ct
      |
        Const (\<^const_name>\<open>MACHIN_TAG\<close>, _) $ _ $
          (Const (\<^const_name>\<open>Groups.plus\<close>, _) $
            (Const (\<^const_name>\<open>Transcendental.arctan\<close>, _) $ _) $
            (Const (\<^const_name>\<open>Transcendental.arctan\<close>, _) $ _)) =>
          Simplifier.rewrite ctxt' ct
      | _ => raise CTERM ("machin_conv", [ct])
    end

  fun machin_tac ctxt =
    let val conv = Conv.top_conv (Conv.try_conv o machin_term_conv) ctxt
    in
      SELECT_GOAL (
        Local_Defs.unfold_tac ctxt
          @{thms tag_machin[THEN eq_reflection] numeral_horner_MACHIN_TAG[THEN eq_reflection]}
        THEN REPEAT (CHANGED (HEADGOAL (CONVERSION conv))))
      THEN' Simplifier.simp_tac (ctxt |> Simplifier.add_simps @{thms arctan_add_small arctan_diff_small})
    end
\<close>

method_setup machin = \<open>Scan.succeed (SIMPLE_METHOD' o machin_tac)\<close>

text \<open>
  We can now prove the ``standard'' Machin formula, which was already proven manually
  in Isabelle, automatically.
}\<close>
lemma "pi / 4 = (4::real) * arctan (1 / 5) - arctan (1 / 239)"
  by machin

text \<open>
  We can also prove the following more complicated formula:
\<close>
lemma machin': "pi/4 = (12::real) * arctan (1/18) + 8 * arctan (1/57) - 5 * arctan (1/239)"
  by machin



subsubsection \<open>Simple approximation of pi\<close>

text \<open>
  We can use the simple Machin formula and the Taylor series expansion of the arctangent
  to approximate pi. For a given even natural number $n$, we expand \<^term>\<open>arctan (1/5)\<close>
  to $3n$ summands and \<^term>\<open>arctan (1/239)\<close> to $n$ summands. This gives us at least
  $13n-2$ bits of precision.
\<close>

definition "pi_approx n = 16 * arctan_approx (3*n) (1/5) - 4 * arctan_approx n (1/239)"

lemma pi_approx:
  fixes n :: nat assumes n: "even n" and "n > 0"
  shows   "\<bar>pi - pi_approx n\<bar> \<le> inverse (2^(13*n - 2))"
proof -
  from n have n': "even (3*n)" by simp
  \<comment> \<open>We apply the Machin formula\<close>
  from machin have "pi = 16 * arctan (1/5) - 4 * arctan (1/239::real)" by simp
  \<comment> \<open>Taylor series expansion of the arctangent\<close>
  also from arctan_approx[OF _ _ n', of "1/5"] arctan_approx[OF _ _ n, of "1/239"]
    have "\<dots> - pi_approx n \<in> {-4*((1/239)^(2*n+1) / (1-(1/239)^4))..16*(1/5)^(6*n+1) / (1-(1/5)^4)}"
    by (simp add: pi_approx_def)
  \<comment> \<open>Coarsening the bounds to make them a bit nicer\<close>
  also have "-4*((1/239::real)^(2*n+1) / (1-(1/239)^4)) = -((13651919 / 815702160) / 57121^n)"
    by (simp add: power_mult power2_eq_square) (simp add: field_simps)
  also have "16*(1/5)^(6*n+1) / (1-(1/5::real)^4) = (125/39) / 15625^n"
    by (simp add: power_mult power2_eq_square) (simp add: field_simps)
  also have "{-((13651919 / 815702160) / 57121^n) .. (125 / 39) / 15625^n} \<subseteq>
               {- (4 / 2^(13*n)) .. 4 / (2^(13*n)::real)}"
    by (subst atLeastatMost_subset_iff, intro disjI2 conjI le_imp_neg_le)
       (rule frac_le; simp add: power_mult power_mono)+
  finally have "abs (pi - pi_approx n) \<le> 4 / 2^(13*n)" by auto
  also from \<open>n > 0\<close> have "4 / 2^(13*n) = 1 / (2^(13*n - 2) :: real)"
    by (cases n) (simp_all add: power_add)
  finally show ?thesis by (simp add: divide_inverse)
qed

lemma pi_approx':
  fixes n :: nat assumes n: "even n" and "n > 0" and "k \<le> 13*n - 2"
  shows   "\<bar>pi - pi_approx n\<bar> \<le> inverse (2^k)"
  using assms(3) by (intro order.trans[OF pi_approx[OF assms(1,2)]]) (simp_all add: field_simps)

text \<open>We can now approximate pi to 22 decimals within a fraction of a second.\<close>
lemma pi_approx_75: "abs (pi - 3.1415926535897932384626 :: real) \<le> inverse (10^22)"
proof -
  define a :: real
    where "a = 8295936325956147794769600190539918304 / 2626685325478320010006427764892578125"
  define b :: real
    where "b = 8428294561696506782041394632 / 503593538783547230635598424135"
  \<comment> \<open>The introduction of this constant prevents the simplifier from applying solvers that
      we don't want. We want it to simply evaluate the terms to rational constants.}\<close>
  define eq :: "real \<Rightarrow> real \<Rightarrow> bool" where "eq = (=)"

  \<comment> \<open>Splitting the computation into several steps has the advantage that simplification can
      be done in parallel\<close>
  have "abs (pi - pi_approx 6) \<le> inverse (2^76)" by (rule pi_approx') simp_all
  also have "pi_approx 6 = 16 * arctan_approx (3 * 6) (1 / 5) - 4 * arctan_approx 6 (1 / 239)"
    unfolding pi_approx_def by simp
  also have [unfolded eq_def]: "eq (16 * arctan_approx (3 * 6) (1 / 5)) a"
    by (simp add: arctan_approx_def' power2_eq_square,
        simp add: expand_arctan_approx, unfold a_def eq_def, rule refl)
  also have [unfolded eq_def]: "eq (4 * arctan_approx 6 (1 / 239::real)) b"
    by (simp add: arctan_approx_def' power2_eq_square,
        simp add: expand_arctan_approx, unfold b_def eq_def, rule refl)
  also have [unfolded eq_def]:
    "eq (a - b) (171331331860120333586637094112743033554946184594977368554649608 /
                 54536456744112171868276045488779391002026386559009552001953125)"
    by (unfold a_def b_def, simp, unfold eq_def, rule refl)
  finally show ?thesis by (rule approx_coarsen) simp
qed

text \<open>
  The previous estimate of pi in this file was based on approximating the root of the
  $\sin(\pi/6)$ in the interval $[0;4]$ using the Taylor series expansion of the sine to
  verify that it is between two given bounds.
  This was much slower and much less precise. We can easily recover this coarser estimate from
  the newer, precise estimate:
\<close>
lemma pi_approx_32: "\<bar>pi - 13493037705/4294967296 :: real\<bar> \<le> inverse(2 ^ 32)"
  by (rule approx_coarsen[OF pi_approx_75]) simp


subsection \<open>A more complicated approximation of pi\<close>

text \<open>
  There are more complicated Machin-like formulae that have more terms with larger
  denominators. Although they have more terms, each term requires fewer summands of the
  Taylor series for the same precision, since it is evaluated closer to $0$.

  Using a good formula, one can therefore obtain the same precision with fewer operations.
  The big formulae used for computations of pi in practice are too complicated for us to
  prove here, but we can use the three-term Machin-like formula @{thm machin'}.
\<close>

definition "pi_approx2 n = 48 * arctan_approx (6*n) (1/18::real) +
                             32 * arctan_approx (4*n) (1/57) - 20 * arctan_approx (3*n) (1/239)"

lemma pi_approx2:
  fixes n :: nat assumes n: "even n" and "n > 0"
  shows   "\<bar>pi - pi_approx2 n\<bar> \<le> inverse (2^(46*n - 1))"
proof -
  from n have n': "even (6*n)" "even (4*n)" "even (3*n)" by simp_all
  from machin' have "pi = 48 * arctan (1/18) + 32 * arctan (1/57) - 20 * arctan (1/239::real)"
    by simp
  hence "pi - pi_approx2 n = 48 * (arctan (1/18) - arctan_approx (6*n) (1/18)) +
                                 32 * (arctan (1/57) - arctan_approx (4*n) (1/57)) -
                                 20 * (arctan (1/239) - arctan_approx (3*n) (1/239))"
    by (simp add: pi_approx2_def)
  also have "\<dots> \<in> {-((20/239/(1-(1/239)^4)) * (1/239)^(6*n))..
              (48/18 / (1-(1/18)^4))*(1/18)^(12*n) + (32/57/(1-(1/57)^4)) * (1/57)^(8*n)}"
    (is "_ \<in> {-?l..?u1 + ?u2}")
    apply ((rule combine_bounds(1,2))+; (rule combine_bounds(3); (rule arctan_approx)?)?)
    apply (simp_all add: n)
    apply (simp_all add: field_split_simps)?
    done
  also {
    have "?l \<le> (1/8) * (1/2)^(46*n)"
      unfolding power_mult by (intro mult_mono power_mono) (simp_all add: field_split_simps)
    also have "\<dots> \<le> (1/2) ^ (46 * n - 1)"
      by (cases n; simp_all add: power_add field_split_simps)
    finally have "?l \<le> (1/2) ^ (46 * n - 1)" .
    moreover {
      have "?u1 + ?u2 \<le> 4 * (1/2)^(48*n) + 1 * (1/2)^(46*n)"
        unfolding power_mult by (intro add_mono mult_mono power_mono) (simp_all add: field_split_simps)
      also from \<open>n > 0\<close> have "4 * (1/2::real)^(48*n) \<le> (1/2)^(46*n)"
        by (cases n) (simp_all add: field_simps power_add)
      also from \<open>n > 0\<close> have "(1/2::real) ^ (46 * n) + 1 * (1 / 2) ^ (46 * n) = (1/2) ^ (46 * n - 1)"
        by (cases n; simp_all add: power_add power_divide)
      finally have "?u1 + ?u2 \<le> (1/2) ^ (46 * n - 1)" by - simp
    }
    ultimately have "{-?l..?u1 + ?u2} \<subseteq> {-((1/2)^(46*n-1))..(1/2)^(46*n-1)}"
      by (subst atLeastatMost_subset_iff) simp_all
  }
  finally have "\<bar>pi - pi_approx2 n\<bar> \<le> ((1/2) ^ (46 * n - 1))" by auto
  thus ?thesis by (simp add: field_split_simps)
qed

lemma pi_approx2':
  fixes n :: nat assumes n: "even n" and "n > 0" and "k \<le> 46*n - 1"
  shows   "\<bar>pi - pi_approx2 n\<bar> \<le> inverse (2^k)"
  using assms(3) by (intro order.trans[OF pi_approx2[OF assms(1,2)]]) (simp_all add: field_simps)

text \<open>
  We can now approximate pi to 54 decimals using this formula. The computations are much
  slower now; this is mostly because we use arbitrary-precision rational numbers, whose
  numerators and demoninators get very large. Using dyadic floating point numbers would be
  much more economical.
\<close>
lemma pi_approx_54_decimals:
  "abs (pi - 3.141592653589793238462643383279502884197169399375105821 :: real) \<le> inverse (10^54)"
  (is "abs (pi - ?pi') \<le> _")
proof -
  define a :: real
    where "a = 2829469759662002867886529831139137601191652261996513014734415222704732791803 /
           1062141879292765061960538947347721564047051545995266466660439319087625011200"
  define b :: real
    where "b = 13355545553549848714922837267299490903143206628621657811747118592 /
           23792006023392488526789546722992491355941103837356113731091180925"
  define c :: real
    where "c = 28274063397213534906669125255762067746830085389618481175335056 /
           337877029279505250241149903214554249587517250716358486542628059"
  let ?pi'' = "3882327391761098513316067116522233897127356523627918964967729040413954225768920394233198626889767468122598417405434625348404038165437924058179155035564590497837027530349 /
               1235783190199688165469648572769847552336447197542738425378629633275352407743112409829873464564018488572820294102599160968781449606552922108667790799771278860366957772800"
  define eq :: "real \<Rightarrow> real \<Rightarrow> bool" where "eq = (=)"

  have "abs (pi - pi_approx2 4) \<le> inverse (2^183)" by (rule pi_approx2') simp_all
  also have "pi_approx2 4 = 48 * arctan_approx 24 (1 / 18) +
                            32 * arctan_approx 16 (1 / 57) -
                            20 * arctan_approx 12 (1 / 239)"
    unfolding pi_approx2_def by simp
  also have [unfolded eq_def]: "eq (48 * arctan_approx 24 (1 / 18)) a"
    by (simp add: arctan_approx_def' power2_eq_square,
        simp add: expand_arctan_approx, unfold a_def eq_def, rule refl)
  also have [unfolded eq_def]: "eq (32 * arctan_approx 16 (1 / 57::real)) b"
    by (simp add: arctan_approx_def' power2_eq_square,
        simp add: expand_arctan_approx, unfold b_def eq_def, rule refl)
  also have [unfolded eq_def]: "eq (20 * arctan_approx 12 (1 / 239::real)) c"
    by (simp add: arctan_approx_def' power2_eq_square,
        simp add: expand_arctan_approx, unfold c_def eq_def, rule refl)
  also have [unfolded eq_def]:
    "eq (a + b) (34326487387865555303797183505809267914709125998469664969258315922216638779011304447624792548723974104030355722677 /
                 10642967245546718617684989689985787964158885991018703366677373121531695267093031090059801733340658960857196134400)"
    by (unfold a_def b_def c_def, simp, unfold eq_def, rule refl)
  also have [unfolded eq_def]: "eq (\<dots> - c) ?pi''"
    by (unfold a_def b_def c_def, simp, unfold eq_def, rule refl)
  \<comment> \<open>This is incredibly slow because the numerators and denominators are huge.\<close>
  finally show ?thesis by (rule approx_coarsen) simp
qed

text \<open>A 128 bit approximation of pi:\<close>
lemma pi_approx_128:
  "abs (pi - 1069028584064966747859680373161870783301 / 2^128) \<le> inverse (2^128)"
  by (rule approx_coarsen[OF pi_approx_54_decimals]) simp

text \<open>A 64 bit approximation of pi:\<close>
lemma pi_approx_64:
  "abs (pi - 57952155664616982739 / 2^64 :: real) \<le> inverse (2^64)"
  by (rule approx_coarsen[OF pi_approx_54_decimals]) simp
  
text \<open>
  Again, going much farther with the simplifier takes a long time, but the code generator
  can handle even two thousand decimal digits in under 20 seconds.
\<close>

end

section \<open>Numeric approximations to Constants\<close>

theory Approximations
imports "../Complex_Transcendental" "../Harmonic_Numbers"
begin

lemma eval_fact:
  "fact 0 = 1"
  "fact (Suc 0) = 1"
  "fact (numeral n) = numeral n * fact (pred_numeral n)"
  by (simp, simp, simp_all only: numeral_eq_Suc fact_Suc,
      simp only: numeral_eq_Suc [symmetric] of_nat_numeral)

lemma setsum_poly_horner_expand:
  "(\<Sum>k<(numeral n::nat). f k * x^k) = f 0 + (\<Sum>k<pred_numeral n. f (k+1) * x^k) * x"
  "(\<Sum>k<Suc 0. f k * x^k) = (f 0 :: 'a :: semiring_1)"
  "(\<Sum>k<(0::nat). f k * x^k) = 0"
proof -
  {
    fix m :: nat
    have "(\<Sum>k<Suc m. f k * x^k) = f 0 + (\<Sum>k=Suc 0..<Suc m. f k * x^k)"
      by (subst atLeast0LessThan [symmetric], subst setsum_head_upt_Suc) simp_all
    also have "(\<Sum>k=Suc 0..<Suc m. f k * x^k) = (\<Sum>k<m. f (k+1) * x^k) * x"
      by (subst setsum_shift_bounds_Suc_ivl)
         (simp add: setsum_left_distrib algebra_simps atLeast0LessThan power_commutes)
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


subsection \<open>Approximation of $\ln 2$\<close>

context
begin

qualified lemma ln_approx_abs': 
  assumes "x > (1::real)"
  assumes "(x-1)/(x+1) = y"
  assumes "y^2 = ysqr"
  assumes "(\<Sum>k<n. inverse (of_nat (2*k+1)) * ysqr^k) = approx"
  assumes "y*ysqr^n / (1 - ysqr) / of_nat (2*n+1) = d"
  assumes "d \<le> e"
  shows   "abs (ln x - (2*y*approx + d)) \<le> e"
proof -
  note ln_approx_abs[OF assms(1), of n]
  also note assms(2)
  also have "y^(2*n+1) = y*ysqr^n" by (simp add: assms(3)[symmetric] power_mult)
  also note assms(3)
  also note assms(5)
  also note assms(5)
  also note assms(6)
  also have "(\<Sum>k<n. 2*y^(2*k+1) / real_of_nat (2 * k + 1)) = (2*y) * approx"
    apply (subst assms(4)[symmetric], subst setsum_right_distrib)
    apply (simp add: assms(3)[symmetric] power_mult)
    apply (simp add: mult_ac divide_simps)?
    done
  finally show ?thesis .
qed

lemma ln_2_approx: "\<bar>ln 2 - 0.69314718055\<bar> < inverse (2 ^ 36 :: real)" (is ?thesis1)
  and ln_2_bounds: "ln (2::real) \<in> {0.693147180549..0.693147180561}" (is ?thesis2)
proof -
  def approx \<equiv> "0.69314718055 :: real" and approx' \<equiv> "4465284211343447 / 6442043387911560 :: real"
  def d \<equiv> "inverse (195259926456::real)"
  have "dist (ln 2) approx \<le> dist (ln 2) approx' + dist approx' approx" by (rule dist_triangle)
  also have "\<bar>ln (2::real) - (2 * (1/3) * (651187280816108 / 626309773824735) +
                 inverse 195259926456)\<bar> \<le> inverse 195259926456"
  proof (rule ln_approx_abs'[where n = 10])
    show "(1/3::real)^2 = 1/9" by (simp add: power2_eq_square)
  qed (simp_all add: eval_nat_numeral)
  hence A: "dist (ln 2) approx' \<le> d" by (simp add: dist_real_def approx'_def d_def)
  hence "dist (ln 2) approx' + dist approx' approx \<le> \<dots> + dist approx' approx"
    by (rule add_right_mono)
  also have "\<dots> < inverse (2 ^ 36)" by (simp add: dist_real_def approx'_def approx_def d_def)
  finally show ?thesis1 unfolding dist_real_def approx_def .
  
  from A have "ln 2 \<in> {approx' - d..approx' + d}" 
    by (simp add: dist_real_def abs_real_def split: split_if_asm)
  also have "\<dots> \<subseteq> {0.693147180549..0.693147180561}"
    by (subst atLeastatMost_subset_iff, rule disjI2) (simp add: approx'_def d_def)
  finally show ?thesis2 .
qed

end


subsection \<open>Approximation of the Euler--Mascheroni constant\<close>

lemma euler_mascheroni_approx: 
  defines "approx \<equiv> 0.577257 :: real" and "e \<equiv> 0.000063 :: real"
  shows   "abs (euler_mascheroni - approx :: real) < e"
  (is "abs (_ - ?approx) < ?e")
proof -
  def l \<equiv> "47388813395531028639296492901910937/82101866951584879688289000000000000 :: real"
  def u \<equiv> "142196984054132045946501548559032969 / 246305600854754639064867000000000000 :: real"
  have impI: "P \<longrightarrow> Q" if Q for P Q using that by blast
  have hsum_63: "harm 63 = (310559566510213034489743057 / 65681493561267903750631200 ::real)"
    by (simp add: harm_expand)
  from harm_Suc[of 63] have hsum_64: "harm 64 = 
          623171679694215690971693339 / (131362987122535807501262400::real)" 
    by (subst (asm) hsum_63) simp
  have "ln (64::real) = real (6::nat) * ln 2" by (subst ln_realpow[symmetric]) simp_all
  hence "ln (real_of_nat (Suc 63)) \<in> {4.158883083293<..<4.158883083367}" using ln_2_bounds by simp
  from euler_mascheroni_bounds'[OF _ this]
    have "(euler_mascheroni :: real) \<in> {l<..<u}" 
    by (simp add: hsum_63 del: greaterThanLessThan_iff) (simp only: l_def u_def)
  also have "\<dots> \<subseteq> {approx - e<..<approx + e}"
    by (subst greaterThanLessThan_subseteq_greaterThanLessThan, rule impI) 
       (simp add: approx_def e_def u_def l_def)
  finally show ?thesis by (simp add: abs_real_def)
qed


subsection \<open>Approximation to pi\<close>


subsubsection \<open>Approximating the arctangent\<close>

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
  def c \<equiv> "\<lambda>k. 1 / (1+(4*real k + 2*real n)) - x\<^sup>2 / (3+(4*real k + 2*real n))"
  from assms have "(\<lambda>k. (-1) ^ k * (1 / real (k * 2 + 1) * x^(k*2+1))) sums arctan x" 
    using arctan_series' by simp
  also have "(\<lambda>k. (-1) ^ k * (1 / real (k * 2 + 1) * x^(k*2+1))) = 
                 (\<lambda>k. x * ((- (x^2))^k / real (2*k+1)))"
    by (simp add: power2_eq_square power_mult power_mult_distrib mult_ac power_minus')
  finally have "(\<lambda>k. x * ((- x\<^sup>2) ^ k / real (2 * k + 1))) sums arctan x" .
  from sums_split_initial_segment[OF this, of n]
    have "(\<lambda>i. x * ((- x\<^sup>2) ^ (i + n) / real (2 * (i + n) + 1))) sums
            (arctan x - arctan_approx n x)"
    by (simp add: arctan_approx_def setsum_right_distrib)
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
      by (subst atLeast0LessThan [symmetric], subst setsum_head_upt_Suc) simp_all
    also have "(\<Sum>k=Suc 0..<Suc m. inverse (f k * x^k)) = (\<Sum>k<m. inverse (f (k+1) * x^k)) / x"
      by (subst setsum_shift_bounds_Suc_ivl)
         (simp add: setsum_right_distrib divide_inverse algebra_simps 
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
  We first define a small proof method that can prove Machin-like formulae for @{term "pi"}
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
      val ctxt' = ctxt addsimps @{thms arctan_double' arctan_add_small}
    in
      case Thm.term_of ct of
        Const (@{const_name MACHIN_TAG}, _) $ _ $ 
          (Const (@{const_name "Transcendental.arctan"}, _) $ _) => 
          Simplifier.rewrite ctxt' ct
      |
        Const (@{const_name MACHIN_TAG}, _) $ _ $ 
          (Const (@{const_name "Groups.plus"}, _) $ 
            (Const (@{const_name "Transcendental.arctan"}, _) $ _) $
            (Const (@{const_name "Transcendental.arctan"}, _) $ _)) => 
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
      THEN' Simplifier.simp_tac (ctxt addsimps @{thms arctan_add_small arctan_diff_small})
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
  to approximate pi. For a given even natural number $n$, we expand @{term "arctan (1/5)"} 
  to $3n$ summands and @{term "arctan (1/239)"} to $n$ summands. This gives us at least
  $13n-2$ bits of precision.
\<close>

definition "pi_approx n = 16 * arctan_approx (3*n) (1/5) - 4 * arctan_approx n (1/239)"

lemma pi_approx:
  fixes n :: nat assumes n: "even n" and "n > 0"
  shows   "\<bar>pi - pi_approx n\<bar> \<le> inverse (2^(13*n - 2))"
proof -
  from n have n': "even (3*n)" by simp
  -- \<open>We apply the Machin formula\<close>
  from machin have "pi = 16 * arctan (1/5) - 4 * arctan (1/239::real)" by simp
  -- \<open>Taylor series expansion of the arctangent\<close>
  also from arctan_approx[OF _ _ n', of "1/5"] arctan_approx[OF _ _ n, of "1/239"]
    have "\<dots> - pi_approx n \<in> {-4*((1/239)^(2*n+1) / (1-(1/239)^4))..16*(1/5)^(6*n+1) / (1-(1/5)^4)}"
    by (simp add: pi_approx_def)
  -- \<open>Coarsening the bounds to make them a bit nicer\<close>
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
  def a \<equiv> "8295936325956147794769600190539918304 / 2626685325478320010006427764892578125 :: real"
  def b \<equiv> "8428294561696506782041394632 / 503593538783547230635598424135 :: real"
  -- \<open>The introduction of this constant prevents the simplifier from applying solvers that 
      we don't want. We want it to simply evaluate the terms to rational constants.}\<close>
  def eq \<equiv> "op = :: real \<Rightarrow> real \<Rightarrow> bool"
  
  -- \<open>Splitting the computation into several steps has the advantage that simplification can
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
    apply (simp_all add: divide_simps)?
    done
  also {
    have "?l \<le> (1/8) * (1/2)^(46*n)"
      unfolding power_mult by (intro mult_mono power_mono) (simp_all add: divide_simps)
    also have "\<dots> \<le> (1/2) ^ (46 * n - 1)"
      by (cases n; simp_all add: power_add divide_simps)
    finally have "?l \<le> (1/2) ^ (46 * n - 1)" .
    moreover {
      have "?u1 + ?u2 \<le> 4 * (1/2)^(48*n) + 1 * (1/2)^(46*n)"
        unfolding power_mult by (intro add_mono mult_mono power_mono) (simp_all add: divide_simps)
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
  thus ?thesis by (simp add: divide_simps)
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
  def a \<equiv> "2829469759662002867886529831139137601191652261996513014734415222704732791803 /
           1062141879292765061960538947347721564047051545995266466660439319087625011200 :: real"
  def b \<equiv> "13355545553549848714922837267299490903143206628621657811747118592 /
           23792006023392488526789546722992491355941103837356113731091180925 :: real"
  def c \<equiv> "28274063397213534906669125255762067746830085389618481175335056 /
           337877029279505250241149903214554249587517250716358486542628059 :: real"
  let ?pi'' = "3882327391761098513316067116522233897127356523627918964967729040413954225768920394233198626889767468122598417405434625348404038165437924058179155035564590497837027530349 /
    1235783190199688165469648572769847552336447197542738425378629633275352407743112409829873464564018488572820294102599160968781449606552922108667790799771278860366957772800"
  def eq \<equiv> "op = :: real \<Rightarrow> real \<Rightarrow> bool"
  
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
  -- \<open>This is incredibly slow because the numerators and denominators are huge.\<close>
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

end

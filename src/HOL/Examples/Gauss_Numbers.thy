(*   Author:      Florian Haftmann, TU Muenchen; based on existing material on complex numbers\<close>
*)

section \<open>Gauss Numbers: integral gauss numbers\<close>

theory Gauss_Numbers
  imports "HOL-Library.Rounded_Division"
begin

codatatype gauss = Gauss (Re: int) (Im: int)

lemma gauss_eqI [intro?]:
  \<open>x = y\<close> if \<open>Re x = Re y\<close> \<open>Im x = Im y\<close>
  by (rule gauss.expand) (use that in simp)

lemma gauss_eq_iff:
  \<open>x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y\<close>
  by (auto intro: gauss_eqI)


subsection \<open>Basic arithmetic\<close>

instantiation gauss :: comm_ring_1
begin

primcorec zero_gauss :: \<open>gauss\<close>
  where
    \<open>Re 0 = 0\<close>
  | \<open>Im 0 = 0\<close>

primcorec one_gauss :: \<open>gauss\<close>
  where
    \<open>Re 1 = 1\<close>
  | \<open>Im 1 = 0\<close>

primcorec plus_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x + y) = Re x + Re y\<close>
  | \<open>Im (x + y) = Im x + Im y\<close>

primcorec uminus_gauss :: \<open>gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (- x) = - Re x\<close>
  | \<open>Im (- x) = - Im x\<close>

primcorec minus_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x - y) = Re x - Re y\<close>
  | \<open>Im (x - y) = Im x - Im y\<close>

primcorec times_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x * y) = Re x * Re y - Im x * Im y\<close>
  | \<open>Im (x * y) = Re x * Im y + Im x * Re y\<close>

instance
  by standard (simp_all add: gauss_eq_iff algebra_simps)

end

lemma of_nat_gauss:
  \<open>of_nat n = Gauss (int n) 0\<close>
  by (induction n) (simp_all add: gauss_eq_iff)

lemma numeral_gauss:
  \<open>numeral n = Gauss (numeral n) 0\<close>
proof -
  have \<open>numeral n = (of_nat (numeral n) :: gauss)\<close>
    by simp
  also have \<open>\<dots> = Gauss (of_nat (numeral n)) 0\<close>
    by (simp add: of_nat_gauss)
  finally show ?thesis
    by simp
qed

lemma of_int_gauss:
  \<open>of_int k = Gauss k 0\<close>
  by (simp add: gauss_eq_iff of_int_of_nat of_nat_gauss)

lemma conversion_simps [simp]:
  \<open>Re (numeral m) = numeral m\<close>
  \<open>Im (numeral m) = 0\<close>
  \<open>Re (of_nat n) = int n\<close>
  \<open>Im (of_nat n) = 0\<close>
  \<open>Re (of_int k) = k\<close>
  \<open>Im (of_int k) = 0\<close>
  by (simp_all add: numeral_gauss of_nat_gauss of_int_gauss)

lemma gauss_eq_0:
  \<open>z = 0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 = 0\<close>
  by (simp add: gauss_eq_iff sum_power2_eq_zero_iff)

lemma gauss_neq_0:
  \<open>z \<noteq> 0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 > 0\<close>
  by (simp add: gauss_eq_0 sum_power2_ge_zero less_le)

lemma Re_sum [simp]:
  \<open>Re (sum f s) = (\<Sum>x\<in>s. Re (f x))\<close>
  by (induct s rule: infinite_finite_induct) auto

lemma Im_sum [simp]:
  \<open>Im (sum f s) = (\<Sum>x\<in>s. Im (f x))\<close>
  by (induct s rule: infinite_finite_induct) auto

instance gauss :: idom
proof
  fix x y :: gauss
  assume \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
  then show \<open>x * y \<noteq> 0\<close>
    by (simp_all add: gauss_eq_iff)
      (smt (verit, best) mult_eq_0_iff mult_neg_neg mult_neg_pos mult_pos_neg mult_pos_pos)
qed



subsection \<open>The Gauss Number $i$\<close>

primcorec imaginary_unit :: gauss  (\<open>\<i>\<close>)
  where
    \<open>Re \<i> = 0\<close>
  | \<open>Im \<i> = 1\<close>

lemma Gauss_eq:
  \<open>Gauss a b = of_int a + \<i> * of_int b\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_eq:
  \<open>a = of_int (Re a) + \<i> * of_int (Im a)\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_i_not_zero [simp]:
  \<open>\<i> \<noteq> 0\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_i_not_one [simp]:
  \<open>\<i> \<noteq> 1\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_i_not_numeral [simp]:
  \<open>\<i> \<noteq> numeral n\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_i_not_neg_numeral [simp]:
  \<open>\<i> \<noteq> - numeral n\<close>
  by (simp add: gauss_eq_iff)

lemma i_mult_i_eq [simp]:
  \<open>\<i> * \<i> = - 1\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_i_mult_minus [simp]:
  \<open>\<i> * (\<i> * x) = - x\<close>
  by (simp flip: mult.assoc)

lemma i_squared [simp]:
  \<open>\<i>\<^sup>2 = - 1\<close>
  by (simp add: power2_eq_square)

lemma i_even_power [simp]:
  \<open>\<i> ^ (n * 2) = (- 1) ^ n\<close>
  unfolding mult.commute [of n] power_mult by simp

lemma Re_i_times [simp]:
  \<open>Re (\<i> * z) = - Im z\<close>
  by simp

lemma Im_i_times [simp]:
  \<open>Im (\<i> * z) = Re z\<close>
  by simp

lemma i_times_eq_iff:
  \<open>\<i> * w = z \<longleftrightarrow> w = - (\<i> * z)\<close>
  by auto

lemma is_unit_i [simp]:
  \<open>\<i> dvd 1\<close>
  by (rule dvdI [of _ _ \<open>- \<i>\<close>]) simp

lemma gauss_numeral [code_post]:
  \<open>Gauss 0 0 = 0\<close>
  \<open>Gauss 1 0 = 1\<close>
  \<open>Gauss (- 1) 0 = - 1\<close>
  \<open>Gauss (numeral n) 0 = numeral n\<close>
  \<open>Gauss (- numeral n) 0 = - numeral n\<close>
  \<open>Gauss 0 1 = \<i>\<close>
  \<open>Gauss 0 (- 1) = - \<i>\<close>
  \<open>Gauss 0 (numeral n) = numeral n * \<i>\<close>
  \<open>Gauss 0 (- numeral n) = - numeral n * \<i>\<close>
  \<open>Gauss 1 1 = 1 + \<i>\<close>
  \<open>Gauss (- 1) 1 = - 1 + \<i>\<close>
  \<open>Gauss (numeral n) 1 = numeral n + \<i>\<close>
  \<open>Gauss (- numeral n) 1 = - numeral n + \<i>\<close>
  \<open>Gauss 1 (- 1) = 1 - \<i>\<close>
  \<open>Gauss 1 (numeral n) = 1 + numeral n * \<i>\<close>
  \<open>Gauss 1 (- numeral n) = 1 - numeral n * \<i>\<close>
  \<open>Gauss (- 1) (- 1) = - 1 - \<i>\<close>
  \<open>Gauss (numeral n) (- 1) = numeral n - \<i>\<close>
  \<open>Gauss (- numeral n) (- 1) = - numeral n - \<i>\<close>
  \<open>Gauss (- 1) (numeral n) = - 1 + numeral n * \<i>\<close>
  \<open>Gauss (- 1) (- numeral n) = - 1 - numeral n * \<i>\<close>
  \<open>Gauss (numeral m) (numeral n) = numeral m + numeral n * \<i>\<close>
  \<open>Gauss (- numeral m) (numeral n) = - numeral m + numeral n * \<i>\<close>
  \<open>Gauss (numeral m) (- numeral n) = numeral m - numeral n * \<i>\<close>
  \<open>Gauss (- numeral m) (- numeral n) = - numeral m - numeral n * \<i>\<close>
  by (simp_all add: gauss_eq_iff)


subsection \<open>Gauss Conjugation\<close>

primcorec cnj :: \<open>gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (cnj z) = Re z\<close>
  | \<open>Im (cnj z) = - Im z\<close>

lemma gauss_cnj_cancel_iff [simp]:
  \<open>cnj x = cnj y \<longleftrightarrow> x = y\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_cnj [simp]:
  \<open>cnj (cnj z) = z\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_zero [simp]:
  \<open>cnj 0 = 0\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_zero_iff [iff]:
  \<open>cnj z = 0 \<longleftrightarrow> z = 0\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_one_iff [simp]:
  \<open>cnj z = 1 \<longleftrightarrow> z = 1\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_add [simp]:
  \<open>cnj (x + y) = cnj x + cnj y\<close>
  by (simp add: gauss_eq_iff)

lemma cnj_sum [simp]:
  \<open>cnj (sum f s) = (\<Sum>x\<in>s. cnj (f x))\<close>
  by (induct s rule: infinite_finite_induct) auto

lemma gauss_cnj_diff [simp]:
  \<open>cnj (x - y) = cnj x - cnj y\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_minus [simp]:
  \<open>cnj (- x) = - cnj x\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_one [simp]:
  \<open>cnj 1 = 1\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_mult [simp]:
  \<open>cnj (x * y) = cnj x * cnj y\<close>
  by (simp add: gauss_eq_iff)

lemma cnj_prod [simp]:
  \<open>cnj (prod f s) = (\<Prod>x\<in>s. cnj (f x))\<close>
  by (induct s rule: infinite_finite_induct) auto

lemma gauss_cnj_power [simp]:
  \<open>cnj (x ^ n) = cnj x ^ n\<close>
  by (induct n) simp_all

lemma gauss_cnj_numeral [simp]:
  \<open>cnj (numeral w) = numeral w\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_of_nat [simp]:
  \<open>cnj (of_nat n) = of_nat n\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_of_int [simp]:
  \<open>cnj (of_int z) = of_int z\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_cnj_i [simp]:
  \<open>cnj \<i> = - \<i>\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_add_cnj:
  \<open>z + cnj z = of_int (2 * Re z)\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_diff_cnj:
  \<open>z - cnj z = of_int (2 * Im z) * \<i>\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_mult_cnj:
  \<open>z * cnj z = of_int ((Re z)\<^sup>2 + (Im z)\<^sup>2)\<close>
  by (simp add: gauss_eq_iff power2_eq_square)

lemma cnj_add_mult_eq_Re:
  \<open>z * cnj w + cnj z * w = of_int (2 * Re (z * cnj w))\<close>
  by (simp add: gauss_eq_iff)

lemma gauss_In_mult_cnj_zero [simp]:
  \<open>Im (z * cnj z) = 0\<close>
  by simp


subsection \<open>Algebraic division\<close>

instantiation gauss :: idom_modulo
begin

primcorec divide_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x div y) = (Re x * Re y + Im x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2)\<close>
  | \<open>Im (x div y) = (Im x * Re y - Re x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2)\<close>

primcorec modulo_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x mod y) = Re x -
      ((Re x * Re y + Im x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Re y -
       (Im x * Re y - Re x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Im y)\<close>
  | \<open>Im (x mod y) = Im x -
      ((Re x * Re y + Im x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Im y +
       (Im x * Re y - Re x * Im y) rdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Re y)\<close>

instance proof
  fix x y :: gauss
  show \<open>x div 0 = 0\<close>
    by (simp add: gauss_eq_iff)
  show \<open>x * y div y = x\<close> if \<open>y \<noteq> 0\<close>
  proof -
    define Y where \<open>Y = (Re y)\<^sup>2 + (Im y)\<^sup>2\<close>
    moreover have \<open>Y > 0\<close>
      using that by (simp add: gauss_eq_0 less_le Y_def)
    have *: \<open>Im y * (Im y * Re x) + Re x * (Re y * Re y) = Re x * Y\<close>
      \<open>Im x * (Im y * Im y) + Im x * (Re y * Re y) = Im x * Y\<close>
      \<open>(Im y)\<^sup>2 + (Re y)\<^sup>2 = Y\<close>
      by (simp_all add: power2_eq_square algebra_simps Y_def)
    from \<open>Y > 0\<close> show ?thesis
      by (simp add: gauss_eq_iff algebra_simps) (simp add: * nonzero_mult_rdiv_cancel_right)
  qed
  show \<open>x div y * y + x mod y = x\<close>
    by (simp add: gauss_eq_iff)
qed

end

instantiation gauss :: euclidean_ring
begin

definition euclidean_size_gauss :: \<open>gauss \<Rightarrow> nat\<close>
  where \<open>euclidean_size x = nat ((Re x)\<^sup>2 + (Im x)\<^sup>2)\<close>

instance proof
  show \<open>euclidean_size (0::gauss) = 0\<close>
    by (simp add: euclidean_size_gauss_def)
  show \<open>euclidean_size (x mod y) < euclidean_size y\<close> if \<open>y \<noteq> 0\<close> for x y :: gauss
  proof-
    define X and Y and R and I
      where \<open>X = (Re x)\<^sup>2 + (Im x)\<^sup>2\<close> and \<open>Y = (Re y)\<^sup>2 + (Im y)\<^sup>2\<close>
        and \<open>R = Re x * Re y + Im x * Im y\<close> and \<open>I = Im x * Re y - Re x * Im y\<close>
    with that have \<open>0 < Y\<close> and rhs: \<open>int (euclidean_size y) = Y\<close>
      by (simp_all add: gauss_neq_0 euclidean_size_gauss_def)
    have \<open>X * Y = R\<^sup>2 + I\<^sup>2\<close>
      by (simp add: R_def I_def X_def Y_def power2_eq_square algebra_simps)
    let ?lhs = \<open>X - I * (I rdiv Y) - R * (R rdiv Y)
        - I rdiv Y * (I rmod Y) - R rdiv Y * (R rmod Y)\<close>
    have \<open>?lhs = X + Y * (R rdiv Y) * (R rdiv Y) + Y * (I rdiv Y) * (I rdiv Y)
        - 2 * (R rdiv Y * R + I rdiv Y * I)\<close>
      by (simp flip: minus_rmod_eq_mult_rdiv add: algebra_simps)
    also have \<open>\<dots> = (Re (x mod y))\<^sup>2 + (Im (x mod y))\<^sup>2\<close>
      by (simp add: X_def Y_def R_def I_def algebra_simps power2_eq_square)
    finally have lhs: \<open>int (euclidean_size (x mod y)) = ?lhs\<close>
      by (simp add: euclidean_size_gauss_def)
    have \<open>?lhs * Y = (I rmod Y)\<^sup>2 + (R rmod Y)\<^sup>2\<close>
      apply (simp add: algebra_simps power2_eq_square \<open>X * Y = R\<^sup>2 + I\<^sup>2\<close>)
      apply (simp flip: mult.assoc add.assoc minus_rmod_eq_mult_rdiv)
      apply (simp add: algebra_simps)
      done
    also have \<open>\<dots> \<le> (Y div 2)\<^sup>2 + (Y div 2)\<^sup>2\<close>
      by (rule add_mono) (use \<open>Y > 0\<close> abs_rmod_less_equal [of Y] in \<open>simp_all add: power2_le_iff_abs_le\<close>)
    also have \<open>\<dots> < Y\<^sup>2\<close>
      using \<open>Y > 0\<close> by (cases \<open>Y = 1\<close>) (simp_all add: power2_eq_square mult_le_less_imp_less flip: mult.assoc)
    finally have \<open>?lhs * Y < Y\<^sup>2\<close> .
    with \<open>Y > 0\<close> have \<open>?lhs < Y\<close>
      by (simp add: power2_eq_square)
    then have \<open>int (euclidean_size (x mod y)) < int (euclidean_size y)\<close>
      by (simp only: lhs rhs)
    then show ?thesis
      by simp
  qed
  show \<open>euclidean_size x \<le> euclidean_size (x * y)\<close> if \<open>y \<noteq> 0\<close> for x y :: gauss
  proof -
    from that have \<open>euclidean_size y > 0\<close>
      by (simp add: euclidean_size_gauss_def gauss_neq_0)
    then have \<open>euclidean_size x \<le> euclidean_size x * euclidean_size y\<close>
      by simp
    also have \<open>\<dots> = nat (((Re x)\<^sup>2 + (Im x)\<^sup>2) * ((Re y)\<^sup>2 + (Im y)\<^sup>2))\<close>
      by (simp add: euclidean_size_gauss_def nat_mult_distrib)
    also have \<open>\<dots> = euclidean_size (x * y)\<close>
      by (simp add: euclidean_size_gauss_def eq_nat_nat_iff) (simp add: algebra_simps power2_eq_square)
    finally show ?thesis .
  qed
qed

end

end

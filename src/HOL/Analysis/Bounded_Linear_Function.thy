(*  Title:      HOL/Analysis/Bounded_Linear_Function.thy
    Author:     Fabian Immler, TU München
*)

section \<open>Bounded Linear Function\<close>

theory Bounded_Linear_Function
imports
  Topology_Euclidean_Space
  Operator_Norm
  Uniform_Limit
  Function_Topology

begin

lemma onorm_componentwise:
  assumes "bounded_linear f"
  shows "onorm f \<le> (\<Sum>i\<in>Basis. norm (f i))"
proof -
  have "onorm (\<lambda>x. (x \<bullet> i) *\<^sub>R f i) \<le> norm (f i)" if "i \<in> Basis" for i::'a
  proof -
    from that have "onorm (\<lambda>x. (x \<bullet> i) *\<^sub>R f i) \<le> onorm (\<lambda>x. (x \<bullet> i)) * norm (f i)"
      by (auto intro!: onorm_scaleR_left_lemma bounded_linear_inner_left)
    also have "\<dots> \<le>  norm i * norm (f i)"
      by (rule mult_right_mono)
        (auto simp: ac_simps Cauchy_Schwarz_ineq2 intro!: onorm_le)
    finally show ?thesis using \<open>i \<in> Basis\<close>
      by simp
  qed
  hence "onorm (\<lambda>x. \<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) \<le> (\<Sum>i\<in>Basis. norm (f i))"
    by (auto intro!: order_trans[OF onorm_sum_le] bounded_linear_scaleR_const
      sum_mono bounded_linear_inner_left)
  also have "(\<lambda>x. \<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R f i) = (\<lambda>x. f (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i))"
    by (simp add: linear_sum bounded_linear.linear assms linear_simps)
  also have "\<dots> = f"
    by (simp add: euclidean_representation)
  finally show ?thesis .
qed

lemmas onorm_componentwise_le = order_trans[OF onorm_componentwise]

subsection\<^marker>\<open>tag unimportant\<close> \<open>Intro rules for \<^term>\<open>bounded_linear\<close>\<close>

named_theorems bounded_linear_intros

lemma onorm_inner_left:
  assumes "bounded_linear r"
  shows "onorm (\<lambda>x. r x \<bullet> f) \<le> onorm r * norm f"
proof (rule onorm_bound)
  fix x
  have "norm (r x \<bullet> f) \<le> norm (r x) * norm f"
    by (simp add: Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (intro mult_right_mono onorm assms norm_ge_zero)
  finally show "norm (r x \<bullet> f) \<le> onorm r * norm f * norm x"
    by (simp add: ac_simps)
qed (intro mult_nonneg_nonneg norm_ge_zero onorm_pos_le assms)

lemma onorm_inner_right:
  assumes "bounded_linear r"
  shows "onorm (\<lambda>x. f \<bullet> r x) \<le> norm f * onorm r"
  apply (subst inner_commute)
  apply (rule onorm_inner_left[OF assms, THEN order_trans])
  apply simp
  done

lemmas [bounded_linear_intros] =
  bounded_linear_zero
  bounded_linear_add
  bounded_linear_const_mult
  bounded_linear_mult_const
  bounded_linear_scaleR_const
  bounded_linear_const_scaleR
  bounded_linear_ident
  bounded_linear_sum
  bounded_linear_Pair
  bounded_linear_sub
  bounded_linear_fst_comp
  bounded_linear_snd_comp
  bounded_linear_inner_left_comp
  bounded_linear_inner_right_comp


subsection\<^marker>\<open>tag unimportant\<close> \<open>declaration of derivative/continuous/tendsto introduction rules for bounded linear functions\<close>

attribute_setup bounded_linear =
  \<open>Scan.succeed (Thm.declaration_attribute (fn thm =>
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_linear.has_derivative}, \<^named_theorems>\<open>derivative_intros\<close>),
        (@{thm bounded_linear.tendsto}, \<^named_theorems>\<open>tendsto_intros\<close>),
        (@{thm bounded_linear.continuous}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_linear.continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_linear.uniformly_continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_linear_compose}, \<^named_theorems>\<open>bounded_linear_intros\<close>)
      ]))\<close>

attribute_setup bounded_bilinear =
  \<open>Scan.succeed (Thm.declaration_attribute (fn thm =>
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_bilinear.FDERIV}, \<^named_theorems>\<open>derivative_intros\<close>),
        (@{thm bounded_bilinear.tendsto}, \<^named_theorems>\<open>tendsto_intros\<close>),
        (@{thm bounded_bilinear.continuous}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_bilinear.continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_linear_compose[OF bounded_bilinear.bounded_linear_left]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_linear_compose[OF bounded_bilinear.bounded_linear_right]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_linear.uniformly_continuous_on[OF bounded_bilinear.bounded_linear_left]},
          \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_linear.uniformly_continuous_on[OF bounded_bilinear.bounded_linear_right]},
          \<^named_theorems>\<open>continuous_intros\<close>)
      ]))\<close>


subsection \<open>Type of bounded linear functions\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) blinfun (\<open>(\<open>notation=\<open>infix \<Rightarrow>\<^sub>L\<close>\<close>_ \<Rightarrow>\<^sub>L /_)\<close> [22, 21] 21) =
  "{f::'a::real_normed_vector\<Rightarrow>'b::real_normed_vector. bounded_linear f}"
  morphisms blinfun_apply Blinfun
  by (blast intro: bounded_linear_intros)

declare [[coercion
    "blinfun_apply :: ('a::real_normed_vector \<Rightarrow>\<^sub>L'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

lemma bounded_linear_blinfun_apply[bounded_linear_intros]:
  "bounded_linear g \<Longrightarrow> bounded_linear (\<lambda>x. blinfun_apply f (g x))"
  by (metis blinfun_apply mem_Collect_eq bounded_linear_compose)

setup_lifting type_definition_blinfun

lemma blinfun_eqI: "(\<And>i. blinfun_apply x i = blinfun_apply y i) \<Longrightarrow> x = y"
  by transfer auto

lemma bounded_linear_Blinfun_apply: "bounded_linear f \<Longrightarrow> blinfun_apply (Blinfun f) = f"
  by (auto simp: Blinfun_inverse)


subsection \<open>Type class instantiations\<close>

instantiation blinfun :: (real_normed_vector, real_normed_vector) real_normed_vector
begin

lift_definition\<^marker>\<open>tag important\<close> norm_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> real" is onorm .

lift_definition minus_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  is "\<lambda>f g x. f x - g x"
  by (rule bounded_linear_sub)

definition dist_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> real"
  where "dist_blinfun a b = norm (a - b)"

definition uniformity_blinfun :: "(('a \<Rightarrow>\<^sub>L 'b) \<times> ('a \<Rightarrow>\<^sub>L 'b)) filter"
  where "(uniformity :: (('a \<Rightarrow>\<^sub>L 'b) \<times> ('a \<Rightarrow>\<^sub>L 'b)) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_blinfun :: "('a \<Rightarrow>\<^sub>L 'b) set \<Rightarrow> bool"
  where [code drop]: "open_blinfun S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lift_definition uminus_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b" is "\<lambda>f x. - f x"
  by (rule bounded_linear_minus)

lift_definition\<^marker>\<open>tag important\<close> zero_blinfun :: "'a \<Rightarrow>\<^sub>L 'b" is "\<lambda>x. 0"
  by (rule bounded_linear_zero)

lift_definition\<^marker>\<open>tag important\<close> plus_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  is "\<lambda>f g x. f x + g x"
  by (metis bounded_linear_add)

lift_definition\<^marker>\<open>tag important\<close> scaleR_blinfun::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b" is "\<lambda>r f x. r *\<^sub>R f x"
  by (metis bounded_linear_compose bounded_linear_scaleR_right)

definition sgn_blinfun :: "'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  where "sgn_blinfun x = scaleR (inverse (norm x)) x"

instance
  apply standard
  unfolding dist_blinfun_def open_blinfun_def sgn_blinfun_def uniformity_blinfun_def
  apply (rule refl | (transfer, force simp: onorm_triangle onorm_scaleR onorm_eq_0 algebra_simps))+
  done

end

declare uniformity_Abort [where 'a="('a :: real_normed_vector) \<Rightarrow>\<^sub>L ('b :: real_normed_vector)", code]

lemma norm_blinfun_eqI:
  assumes "n \<le> norm (blinfun_apply f x) / norm x"
  assumes "\<And>x. norm (blinfun_apply f x) \<le> n * norm x"
  assumes "0 \<le> n"
  shows "norm f = n"
  by (auto simp: norm_blinfun_def
    intro!: antisym onorm_bound assms order_trans[OF _ le_onorm]
    bounded_linear_intros)

lemma norm_blinfun: "norm (blinfun_apply f x) \<le> norm f * norm x"
  by transfer (rule onorm)

lemma norm_blinfun_bound: "0 \<le> b \<Longrightarrow> (\<And>x. norm (blinfun_apply f x) \<le> b * norm x) \<Longrightarrow> norm f \<le> b"
  by transfer (rule onorm_bound)

lemma bounded_bilinear_blinfun_apply[bounded_bilinear]: "bounded_bilinear blinfun_apply"
proof
  fix f g::"'a \<Rightarrow>\<^sub>L 'b" and a b::'a and r::real
  show "(f + g) a = f a + g a" "(r *\<^sub>R f) a = r *\<^sub>R f a"
    by (transfer, simp)+
  interpret bounded_linear f for f::"'a \<Rightarrow>\<^sub>L 'b"
    by (auto intro!: bounded_linear_intros)
  show "f (a + b) = f a + f b" "f (r *\<^sub>R a) = r *\<^sub>R f a"
    by (simp_all add: add scaleR)
  show "\<exists>K. \<forall>a b. norm (blinfun_apply a b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x=1] norm_blinfun)
qed

interpretation blinfun: bounded_bilinear blinfun_apply
  by (rule bounded_bilinear_blinfun_apply)

lemmas bounded_linear_apply_blinfun[intro, simp] = blinfun.bounded_linear_left

declare blinfun.zero_left [simp] blinfun.zero_right [simp]


context bounded_bilinear
begin

named_theorems bilinear_simps

lemmas [bilinear_simps] =
  add_left
  add_right
  diff_left
  diff_right
  minus_left
  minus_right
  scaleR_left
  scaleR_right
  zero_left
  zero_right
  sum_left
  sum_right

end


instance blinfun :: (real_normed_vector, banach) banach
proof
  fix X::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  assume "Cauchy X"
  have "convergent (\<lambda>n. X n x)" for x::'a
  proof -
    have *: "convergent (\<lambda>n. X n x)" if "norm x \<le> 1" for x::'a
    proof -
      have "Cauchy (\<lambda>n. X n x)"
      proof (rule CauchyI)
        fix e::real
        assume "0 < e"
        from CauchyD[OF \<open>Cauchy X\<close> \<open>0 < e\<close>] obtain M
          where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < e"
          by auto
        show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m x - X n x) < e"
        proof (safe intro!: exI[where x=M])
          fix m n
          assume le: "M \<le> m" "M \<le> n"
          have "norm (X m x - X n x) = norm ((X m - X n) x)"
            by (simp add: blinfun.bilinear_simps)
          also have "\<dots> \<le> norm (X m - X n) * norm x"
             by (rule norm_blinfun)
          also have "\<dots> \<le> norm (X m - X n) * 1"
            using \<open>norm x \<le> 1\<close> norm_ge_zero by (rule mult_left_mono)
          also have "\<dots> = norm (X m - X n)" by simp
          also have "\<dots> < e" using le by fact
          finally show "norm (X m x - X n x) < e" .
        qed
      qed
      then show ?thesis
        by (metis Cauchy_convergent_iff)
    qed
    define y where "y = x /\<^sub>R norm x"
    have y: "norm y \<le> 1" and xy: "x = norm x *\<^sub>R y"
      by (simp_all add: y_def inverse_eq_divide)
    have "convergent (\<lambda>n. norm x *\<^sub>R X n y)"
      by (intro bounded_bilinear.convergent[OF bounded_bilinear_scaleR] convergent_const * y)
    also have "(\<lambda>n. norm x *\<^sub>R X n y) = (\<lambda>n. X n x)"
      by (subst xy) (simp add: blinfun.bilinear_simps)
    finally show ?thesis .
  qed
  then obtain v where v: "\<And>x. (\<lambda>n. X n x) \<longlonglongrightarrow> v x"
    unfolding convergent_def
    by metis

  have "Cauchy (\<lambda>n. norm (X n))"
  proof (rule CauchyI)
    fix e::real
    assume "e > 0"
    from CauchyD[OF \<open>Cauchy X\<close> \<open>0 < e\<close>] obtain M
      where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < e"
      by auto
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (norm (X m) - norm (X n)) < e"
    proof (safe intro!: exI[where x=M])
      fix m n assume mn: "m \<ge> M" "n \<ge> M"
      have "norm (norm (X m) - norm (X n)) \<le> norm (X m - X n)"
        by (metis norm_triangle_ineq3 real_norm_def)
      also have "\<dots> < e" using mn by fact
      finally show "norm (norm (X m) - norm (X n)) < e" .
    qed
  qed
  then obtain K where K: "(\<lambda>n. norm (X n)) \<longlonglongrightarrow> K"
    unfolding Cauchy_convergent_iff convergent_def
    by metis

  have "bounded_linear v"
  proof
    fix x y and r::real
    from tendsto_add[OF v[of x] v [of y]] v[of "x + y", unfolded blinfun.bilinear_simps]
      tendsto_scaleR[OF tendsto_const[of r] v[of x]] v[of "r *\<^sub>R x", unfolded blinfun.bilinear_simps]
    show "v (x + y) = v x + v y" "v (r *\<^sub>R x) = r *\<^sub>R v x"
      by (metis (poly_guards_query) LIMSEQ_unique)+
    show "\<exists>K. \<forall>x. norm (v x) \<le> norm x * K"
    proof (safe intro!: exI[where x=K])
      fix x
      have "norm (v x) \<le> K * norm x"
        by (rule tendsto_le[OF _ tendsto_mult[OF K tendsto_const] tendsto_norm[OF v]])
          (auto simp: norm_blinfun)
      thus "norm (v x) \<le> norm x * K"
        by (simp add: ac_simps)
    qed
  qed
  hence Bv: "\<And>x. (\<lambda>n. X n x) \<longlonglongrightarrow> Blinfun v x"
    by (auto simp: bounded_linear_Blinfun_apply v)

  have "X \<longlonglongrightarrow> Blinfun v"
  proof (rule LIMSEQ_I)
    fix r::real assume "r > 0"
    define r' where "r' = r / 2"
    have "0 < r'" "r' < r" using \<open>r > 0\<close> by (simp_all add: r'_def)
    from CauchyD[OF \<open>Cauchy X\<close> \<open>r' > 0\<close>]
    obtain M where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < r'"
      by metis
    show "\<exists>no. \<forall>n\<ge>no. norm (X n - Blinfun v) < r"
    proof (safe intro!: exI[where x=M])
      fix n assume n: "M \<le> n"
      have "norm (X n - Blinfun v) \<le> r'"
      proof (rule norm_blinfun_bound)
        fix x
        have "eventually (\<lambda>m. m \<ge> M) sequentially"
          by (metis eventually_ge_at_top)
        hence ev_le: "eventually (\<lambda>m. norm (X n x - X m x) \<le> r' * norm x) sequentially"
        proof eventually_elim
          case (elim m)
          have "norm (X n x - X m x) = norm ((X n - X m) x)"
            by (simp add: blinfun.bilinear_simps)
          also have "\<dots> \<le> norm ((X n - X m)) * norm x"
            by (rule norm_blinfun)
          also have "\<dots> \<le> r' * norm x"
            using M[OF n elim] by (simp add: mult_right_mono)
          finally show ?case .
        qed
        have tendsto_v: "(\<lambda>m. norm (X n x - X m x)) \<longlonglongrightarrow> norm (X n x - Blinfun v x)"
          by (auto intro!: tendsto_intros Bv)
        show "norm ((X n - Blinfun v) x) \<le> r' * norm x"
          by (auto intro!: tendsto_upperbound tendsto_v ev_le simp: blinfun.bilinear_simps)
      qed (simp add: \<open>0 < r'\<close> less_imp_le)
      thus "norm (X n - Blinfun v) < r"
        by (metis \<open>r' < r\<close> le_less_trans)
    qed
  qed
  thus "convergent X"
    by (rule convergentI)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>On Euclidean Space\<close>

lemma Zfun_sum:
  assumes "finite s"
  assumes f: "\<And>i. i \<in> s \<Longrightarrow> Zfun (f i) F"
  shows "Zfun (\<lambda>x. sum (\<lambda>i. f i x) s) F"
  using assms by induct (auto intro!: Zfun_zero Zfun_add)

lemma norm_blinfun_euclidean_le:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>L 'b::real_normed_vector"
  shows "norm a \<le> sum (\<lambda>x. norm (a x)) Basis"
  apply (rule norm_blinfun_bound)
   apply (simp add: sum_nonneg)
  apply (subst euclidean_representation[symmetric, where 'a='a])
  apply (simp only: blinfun.bilinear_simps sum_distrib_right)
  apply (rule order.trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps Basis_le_norm)
  done

lemma tendsto_componentwise1:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  assumes "(\<And>j. j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n j) \<longlongrightarrow> a j) F)"
  shows "(b \<longlongrightarrow> a) F"
proof -
  have "\<And>j. j \<in> Basis \<Longrightarrow> Zfun (\<lambda>x. norm (b x j - a j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. \<Sum>j\<in>Basis. norm (b x j - a j)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff
    by (rule Zfun_le)
      (auto intro!: order_trans[OF norm_blinfun_euclidean_le] simp: blinfun.bilinear_simps)
qed

lift_definition
  blinfun_of_matrix::"('b::euclidean_space \<Rightarrow> 'a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  is "\<lambda>a x. \<Sum>i\<in>Basis. \<Sum>j\<in>Basis. ((x \<bullet> j) * a i j) *\<^sub>R i"
  by (intro bounded_linear_intros)

lemma blinfun_of_matrix_works:
  fixes f::"'a::euclidean_space \<Rightarrow>\<^sub>L 'b::euclidean_space"
  shows "blinfun_of_matrix (\<lambda>i j. (f j) \<bullet> i) = f"
proof (transfer, rule,  rule euclidean_eqI)
  fix f::"'a \<Rightarrow> 'b" and x::'a and b::'b assume "bounded_linear f" and b: "b \<in> Basis"
  then interpret bounded_linear f by simp
  have "(\<Sum>j\<in>Basis. \<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j)) *\<^sub>R j) \<bullet> b
    = (\<Sum>j\<in>Basis. if j = b then (\<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j))) else 0)"
    using b
    by (simp add: inner_sum_left inner_Basis if_distrib cong: if_cong) (simp add: sum.swap)
  also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> b)))"
    using b by (simp)
  also have "\<dots> = f x \<bullet> b"
    by (metis (mono_tags, lifting) Linear_Algebra.linear_componentwise linear_axioms)
  finally show "(\<Sum>j\<in>Basis. \<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j)) *\<^sub>R j) \<bullet> b = f x \<bullet> b" .
qed

lemma blinfun_of_matrix_apply:
  "blinfun_of_matrix a x = (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. ((x \<bullet> j) * a i j) *\<^sub>R i)"
  by transfer simp

lemma blinfun_of_matrix_minus: "blinfun_of_matrix x - blinfun_of_matrix y = blinfun_of_matrix (x - y)"
  by transfer (auto simp: algebra_simps sum_subtractf)

lemma norm_blinfun_of_matrix:
  "norm (blinfun_of_matrix a) \<le> (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>a i j\<bar>)"
  apply (rule norm_blinfun_bound)
   apply (simp add: sum_nonneg)
  apply (simp only: blinfun_of_matrix_apply sum_distrib_right)
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps Basis_le_norm)
  done

lemma tendsto_blinfun_of_matrix:
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n i j) \<longlongrightarrow> a i j) F"
  shows "((\<lambda>n. blinfun_of_matrix (b n)) \<longlongrightarrow> blinfun_of_matrix a) F"
proof -
  have "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> Zfun (\<lambda>x. norm (b x i j - a i j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>b x i j - a i j\<bar>)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff blinfun_of_matrix_minus
    by (rule Zfun_le) (auto intro!: order_trans[OF norm_blinfun_of_matrix])
qed

lemma tendsto_componentwise:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>L 'b::euclidean_space"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  shows "(\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n j \<bullet> i) \<longlongrightarrow> a j \<bullet> i) F) \<Longrightarrow> (b \<longlongrightarrow> a) F"
  apply (subst blinfun_of_matrix_works[of a, symmetric])
  apply (subst blinfun_of_matrix_works[of "b x" for x, symmetric, abs_def])
  by (rule tendsto_blinfun_of_matrix)

lemma
  continuous_blinfun_componentwiseI:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>L 'c::euclidean_space"
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> continuous F (\<lambda>x. (f x) j \<bullet> i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: tendsto_componentwise)

lemma
  continuous_blinfun_componentwiseI1:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous F (\<lambda>x. f x i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: tendsto_componentwise1)

lemma
  continuous_on_blinfun_componentwise:
  fixes f:: "'d::t2_space \<Rightarrow> 'e::euclidean_space \<Rightarrow>\<^sub>L 'f::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on s (\<lambda>x. f x i)"
  shows "continuous_on s f"
  using assms
  by (auto intro!: continuous_at_imp_continuous_on intro!: tendsto_componentwise1
    simp: continuous_on_eq_continuous_within continuous_def)

lemma bounded_linear_blinfun_matrix: "bounded_linear (\<lambda>x. (x::_\<Rightarrow>\<^sub>L _) j \<bullet> i)"
  by (auto intro!: bounded_linearI' bounded_linear_intros)

lemma continuous_blinfun_matrix:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_inner"
  assumes "continuous F f"
  shows "continuous F (\<lambda>x. (f x) j \<bullet> i)"
  by (rule bounded_linear.continuous[OF bounded_linear_blinfun_matrix assms])

lemma continuous_on_blinfun_matrix:
  fixes f::"'a::t2_space \<Rightarrow> 'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_inner"
  assumes "continuous_on S f"
  shows "continuous_on S (\<lambda>x. (f x) j \<bullet> i)"
  using assms
  by (auto simp: continuous_on_eq_continuous_within continuous_blinfun_matrix)

lemma continuous_on_blinfun_of_matrix[continuous_intros]:
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> continuous_on S (\<lambda>s. g s i j)"
  shows "continuous_on S (\<lambda>s. blinfun_of_matrix (g s))"
  using assms
  by (auto simp: continuous_on intro!: tendsto_blinfun_of_matrix)

lemma mult_if_delta:
  "(if P then (1::'a::comm_semiring_1) else 0) * q = (if P then q else 0)"
  by auto

lemma compact_blinfun_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>L 'b::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a \<Rightarrow>\<^sub>L 'b. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) i) (l i) < e) sequentially)"
  by (rule compact_lemma_general[where unproj = "\<lambda>e. blinfun_of_matrix (\<lambda>i j. e j \<bullet> i)"])
   (auto intro!: euclidean_eqI[where 'a='b] bounded_linear_image assms
    simp: blinfun_of_matrix_works blinfun_of_matrix_apply inner_Basis mult_if_delta sum.delta'
      scaleR_sum_left[symmetric])

lemma blinfun_euclidean_eqI: "(\<And>i. i \<in> Basis \<Longrightarrow> blinfun_apply x i = blinfun_apply y i) \<Longrightarrow> x = y"
  apply (auto intro!: blinfun_eqI)
  apply (subst (2) euclidean_representation[symmetric, where 'a='a])
  apply (subst (1) euclidean_representation[symmetric, where 'a='a])
  apply (simp add: blinfun.bilinear_simps)
  done

lemma Blinfun_eq_matrix: "bounded_linear f \<Longrightarrow> Blinfun f = blinfun_of_matrix (\<lambda>i j. f j \<bullet> i)"
  by (intro blinfun_euclidean_eqI)
     (auto simp: blinfun_of_matrix_apply bounded_linear_Blinfun_apply inner_Basis if_distrib
      if_distribR sum.delta' euclidean_representation
      cong: if_cong)

text \<open>TODO: generalize (via \<open>compact_cball\<close>)?\<close>
instance blinfun :: (euclidean_space, euclidean_space) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  assume f: "bounded (range f)"
  then obtain l::"'a \<Rightarrow>\<^sub>L 'b" and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) i) (l i) < e) sequentially"
    using compact_blinfun_lemma [OF f] by blast
  have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially" if e: "e > 0" for e::real
  proof -
    let ?d = "real_of_nat DIM('a) * real_of_nat DIM('b)"
    from e have "e / ?d > 0" by simp
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) i) (l i) < e / ?d) sequentially"
      by simp
    moreover
    have "dist (f (r n)) l < e" if n: "\<forall>i\<in>Basis. dist (f (r n) i) (l i) < e / ?d" for n
    proof -
      have "norm (f (r n) - l) = norm (blinfun_of_matrix (\<lambda>i j. (f (r n) - l) j \<bullet> i))"
        unfolding blinfun_of_matrix_works ..
      also note norm_blinfun_of_matrix
      also have "(\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) <
        (\<Sum>i\<in>(Basis::'b set). e / real_of_nat DIM('b))"
      proof (rule sum_strict_mono)
        fix i::'b assume i: "i \<in> Basis"
        have "(\<Sum>j::'a\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) < (\<Sum>j::'a\<in>Basis. e / ?d)"
        proof (rule sum_strict_mono)
          fix j::'a assume j: "j \<in> Basis"
          have "\<bar>(f (r n) - l) j \<bullet> i\<bar> \<le> norm ((f (r n) - l) j)"
            by (simp add: Basis_le_norm i)
          also have "\<dots> < e / ?d"
            using n i j by (auto simp: dist_norm blinfun.bilinear_simps)
          finally show "\<bar>(f (r n) - l) j \<bullet> i\<bar> < e / ?d" by simp
        qed simp_all
        also have "\<dots> \<le> e / real_of_nat DIM('b)"
          by simp
        finally show "(\<Sum>j\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) < e / real_of_nat DIM('b)"
          by simp
      qed simp_all
      also have "\<dots> \<le> e" by simp
      finally show ?thesis by (auto simp: dist_norm)
    qed
    ultimately show ?thesis using eventually_elim2 by force
  qed
  then have *: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    by auto
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>concrete bounded linear functions\<close>

lemma transfer_bounded_bilinear_bounded_linearI:
  assumes "g = (\<lambda>i x. (blinfun_apply (f i) x))"
  shows "bounded_bilinear g = bounded_linear f"
proof
  assume "bounded_bilinear g"
  then interpret bounded_bilinear f by (simp add: assms)
  show "bounded_linear f"
  proof (unfold_locales, safe intro!: blinfun_eqI)
    fix i
    show "f (x + y) i = (f x + f y) i" "f (r *\<^sub>R x) i = (r *\<^sub>R f x) i" for r x y
      by (auto intro!: blinfun_eqI simp: blinfun.bilinear_simps)
    from _ nonneg_bounded show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (rule ex_reg) (auto intro!: onorm_bound simp: norm_blinfun.rep_eq ac_simps)
  qed
qed (auto simp: assms intro!: blinfun.comp)

lemma transfer_bounded_bilinear_bounded_linear[transfer_rule]:
  "(rel_fun (rel_fun (=) (pcr_blinfun (=) (=))) (=)) bounded_bilinear bounded_linear"
  by (auto simp: pcr_blinfun_def cr_blinfun_def rel_fun_def OO_def
    intro!: transfer_bounded_bilinear_bounded_linearI)

context bounded_bilinear
begin

lift_definition prod_left::"'b \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'c" is "(\<lambda>b a. prod a b)"
  by (rule bounded_linear_left)
declare prod_left.rep_eq[simp]

lemma bounded_linear_prod_left[bounded_linear]: "bounded_linear prod_left"
  by transfer (rule flip)

lift_definition prod_right::"'a \<Rightarrow> 'b \<Rightarrow>\<^sub>L 'c" is "(\<lambda>a b. prod a b)"
  by (rule bounded_linear_right)
declare prod_right.rep_eq[simp]

lemma bounded_linear_prod_right[bounded_linear]: "bounded_linear prod_right"
  by transfer (rule bounded_bilinear_axioms)

end

lift_definition id_blinfun::"'a::real_normed_vector \<Rightarrow>\<^sub>L 'a" is "\<lambda>x. x"
  by (rule bounded_linear_ident)

lemmas blinfun_apply_id_blinfun[simp] = id_blinfun.rep_eq

lemma norm_blinfun_id[simp]:
  "norm (id_blinfun::'a::{real_normed_vector, perfect_space} \<Rightarrow>\<^sub>L 'a) = 1"
  by transfer (auto simp: onorm_id)

lemma norm_blinfun_id_le:
  "norm (id_blinfun::'a::real_normed_vector \<Rightarrow>\<^sub>L 'a) \<le> 1"
  by transfer (auto simp: onorm_id_le)


lift_definition fst_blinfun::"('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow>\<^sub>L 'a" is fst
  by (rule bounded_linear_fst)

lemma blinfun_apply_fst_blinfun[simp]: "blinfun_apply fst_blinfun = fst"
  by transfer (rule refl)


lift_definition snd_blinfun::"('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow>\<^sub>L 'b" is snd
  by (rule bounded_linear_snd)

lemma blinfun_apply_snd_blinfun[simp]: "blinfun_apply snd_blinfun = snd"
  by transfer (rule refl)


lift_definition blinfun_compose::
  "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector \<Rightarrow>
    'c::real_normed_vector \<Rightarrow>\<^sub>L 'a \<Rightarrow>
    'c \<Rightarrow>\<^sub>L 'b" (infixl \<open>o\<^sub>L\<close> 55) is "(o)"
  parametric comp_transfer
  unfolding o_def
  by (rule bounded_linear_compose)

lemma blinfun_apply_blinfun_compose[simp]: "(a o\<^sub>L b) c = a (b c)"
  by (simp add: blinfun_compose.rep_eq)

lemma norm_blinfun_compose:
  "norm (f o\<^sub>L g) \<le> norm f * norm g"
  by transfer (rule onorm_compose)

lemma bounded_bilinear_blinfun_compose[bounded_bilinear]: "bounded_bilinear (o\<^sub>L)"
  by unfold_locales
    (auto intro!: blinfun_eqI exI[where x=1] simp: blinfun.bilinear_simps norm_blinfun_compose)

lemma blinfun_compose_zero[simp]:
  "blinfun_compose 0 = (\<lambda>_. 0)"
  "blinfun_compose x 0 = 0"
  by (auto simp: blinfun.bilinear_simps intro!: blinfun_eqI)

lemma blinfun_bij2:
  fixes f::"'a \<Rightarrow>\<^sub>L 'a::euclidean_space"
  assumes "f o\<^sub>L g = id_blinfun"
  shows "bij (blinfun_apply g)"
proof (rule bijI)
  show "inj g"
    using assms
    by (metis blinfun_apply_id_blinfun blinfun_compose.rep_eq injI inj_on_imageI2)
  then show "surj g"
    using blinfun.bounded_linear_right bounded_linear_def linear_inj_imp_surj by blast
qed

lemma blinfun_bij1:
  fixes f::"'a \<Rightarrow>\<^sub>L 'a::euclidean_space"
  assumes "f o\<^sub>L g = id_blinfun"
  shows "bij (blinfun_apply f)"
proof (rule bijI)
  show "surj (blinfun_apply f)"
    by (metis assms blinfun_apply_blinfun_compose blinfun_apply_id_blinfun surjI)
  then show "inj (blinfun_apply f)"
    using blinfun.bounded_linear_right bounded_linear_def linear_surj_imp_inj by blast
qed

lift_definition blinfun_inner_right::"'a::real_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>L real" is "(\<bullet>)"
  by (rule bounded_linear_inner_right)
declare blinfun_inner_right.rep_eq[simp]

lemma bounded_linear_blinfun_inner_right[bounded_linear]: "bounded_linear blinfun_inner_right"
  by transfer (rule bounded_bilinear_inner)


lift_definition blinfun_inner_left::"'a::real_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>L real" is "\<lambda>x y. y \<bullet> x"
  by (rule bounded_linear_inner_left)
declare blinfun_inner_left.rep_eq[simp]

lemma bounded_linear_blinfun_inner_left[bounded_linear]: "bounded_linear blinfun_inner_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_inner])


lift_definition blinfun_scaleR_right::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a::real_normed_vector" is "(*\<^sub>R)"
  by (rule bounded_linear_scaleR_right)
declare blinfun_scaleR_right.rep_eq[simp]

lemma bounded_linear_blinfun_scaleR_right[bounded_linear]: "bounded_linear blinfun_scaleR_right"
  by transfer (rule bounded_bilinear_scaleR)


lift_definition blinfun_scaleR_left::"'a::real_normed_vector \<Rightarrow> real \<Rightarrow>\<^sub>L 'a" is "\<lambda>x y. y *\<^sub>R x"
  by (rule bounded_linear_scaleR_left)
lemmas [simp] = blinfun_scaleR_left.rep_eq

lemma bounded_linear_blinfun_scaleR_left[bounded_linear]: "bounded_linear blinfun_scaleR_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_scaleR])


lift_definition blinfun_mult_right::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a::real_normed_algebra" is "(*)"
  by (rule bounded_linear_mult_right)
declare blinfun_mult_right.rep_eq[simp]

lemma bounded_linear_blinfun_mult_right[bounded_linear]: "bounded_linear blinfun_mult_right"
  by transfer (rule bounded_bilinear_mult)


lift_definition blinfun_mult_left::"'a::real_normed_algebra \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a" is "\<lambda>x y. y * x"
  by (rule bounded_linear_mult_left)
lemmas [simp] = blinfun_mult_left.rep_eq

lemma bounded_linear_blinfun_mult_left[bounded_linear]: "bounded_linear blinfun_mult_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_mult])

lemmas bounded_linear_function_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF bounded_linear_apply_blinfun]
  bounded_linear.uniform_limit[OF bounded_linear_blinfun_apply]
  bounded_linear.uniform_limit[OF bounded_linear_blinfun_matrix]


subsection \<open>The strong operator topology on continuous linear operators\<close>

text \<open>Let \<open>'a\<close> and \<open>'b\<close> be two normed real vector spaces. Then the space of linear continuous
operators from \<open>'a\<close> to \<open>'b\<close> has a canonical norm, and therefore a canonical corresponding topology
(the type classes instantiation are given in \<^file>\<open>Bounded_Linear_Function.thy\<close>).

However, there is another topology on this space, the strong operator topology, where \<open>T\<^sub>n\<close> tends to
\<open>T\<close> iff, for all \<open>x\<close> in \<open>'a\<close>, then \<open>T\<^sub>n x\<close> tends to \<open>T x\<close>. This is precisely the product topology
where the target space is endowed with the norm topology. It is especially useful when \<open>'b\<close> is the set
of real numbers, since then this topology is compact.

We can not implement it using type classes as there is already a topology, but at least we
can define it as a topology.

Note that there is yet another (common and useful) topology on operator spaces, the weak operator
topology, defined analogously using the product topology, but where the target space is given the
weak-* topology, i.e., the pullback of the weak topology on the bidual of the space under the
canonical embedding of a space into its bidual. We do not define it there, although it could also be
defined analogously.
\<close>

definition\<^marker>\<open>tag important\<close> strong_operator_topology::"('a::real_normed_vector \<Rightarrow>\<^sub>L'b::real_normed_vector) topology"
where "strong_operator_topology = pullback_topology UNIV blinfun_apply euclidean"

lemma strong_operator_topology_topspace:
  "topspace strong_operator_topology = UNIV"
unfolding strong_operator_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma strong_operator_topology_basis:
  fixes f::"('a::real_normed_vector \<Rightarrow>\<^sub>L'b::real_normed_vector)" and U::"'i \<Rightarrow> 'b set" and x::"'i \<Rightarrow> 'a"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
  shows "openin strong_operator_topology {f. \<forall>i\<in>I. blinfun_apply f (x i) \<in> U i}"
proof -
  have "open {g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i}"
    by (rule product_topology_basis'[OF assms])
  moreover have "{f. \<forall>i\<in>I. blinfun_apply f (x i) \<in> U i}
                = blinfun_apply-`{g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i} \<inter> UNIV"
    by auto
  ultimately show ?thesis
    unfolding strong_operator_topology_def by (subst openin_pullback_topology) auto
qed

lemma strong_operator_topology_continuous_evaluation:
  "continuous_map strong_operator_topology euclidean (\<lambda>f. blinfun_apply f x)"
proof -
  have "continuous_map strong_operator_topology euclidean ((\<lambda>f. f x) o blinfun_apply)"
    unfolding strong_operator_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_strong_operator_topo_iff_coordinatewise:
  "continuous_map T strong_operator_topology f
    \<longleftrightarrow> (\<forall>x. continuous_map T euclidean (\<lambda>y. blinfun_apply (f y) x))"
proof (auto)
  fix x::"'b"
  assume "continuous_map T strong_operator_topology f"
  with continuous_map_compose[OF this strong_operator_topology_continuous_evaluation]
  have "continuous_map T euclidean ((\<lambda>z. blinfun_apply z x) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>y. blinfun_apply (f y) x)"
    unfolding comp_def by auto
next
  assume *: "\<forall>x. continuous_map T euclidean (\<lambda>y. blinfun_apply (f y) x)"
  have "\<And>i. continuous_map T euclidean (\<lambda>x. blinfun_apply (f x) i)"
    using * unfolding comp_def by auto
  then have "continuous_map T euclidean (blinfun_apply o f)"
    unfolding o_def
    by (metis (no_types) continuous_map_componentwise_UNIV euclidean_product_topology)
  show "continuous_map T strong_operator_topology f"
    unfolding strong_operator_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: \<open>continuous_map T euclidean (blinfun_apply o f)\<close>)
qed

lemma strong_operator_topology_weaker_than_euclidean:
  "continuous_map euclidean strong_operator_topology (\<lambda>f. f)"
  by (subst continuous_on_strong_operator_topo_iff_coordinatewise,
    auto simp add: linear_continuous_on)

end

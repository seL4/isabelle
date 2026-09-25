section \<open>Higher-Order Derivatives and $C^k$ Functions on the Real Line\<close>

theory Higher_Order_Derivatives
  imports Weierstrass_Theorems
begin

subsection \<open>Higher-Order Derivatives and $C^k(U)$ Smoothness\<close>

definition C_k_on :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "C_k_on k f U \<equiv>
     (if k = 0 then (open U \<and> continuous_on U f)
      else (open U \<and> (\<forall>n < k. ((deriv ^^ n) f) differentiable_on U
                         \<and> continuous_on U ((deriv ^^ Suc n) f))))"

lemma C0_on_def: "C_k_on 0 f U \<longleftrightarrow> (open U \<and> continuous_on U f)"
  by (simp add: C_k_on_def)

lemma C1_cont_diff:
  assumes "C_k_on 1 f U"
  shows "f differentiable_on U \<and> continuous_on U (deriv f) \<and>
         (\<forall> y  \<in> U. (f has_real_derivative (deriv f) y) (at y))"
  using C_k_on_def DERIV_deriv_iff_real_differentiable assms at_within_open differentiable_on_def by fastforce

lemma C_k_on_subset:
  assumes "C_k_on k f U" and "open S" and "S \<subseteq> U"
  shows "C_k_on k f S"
  using assms unfolding C_k_on_def
  by (auto intro: continuous_on_subset[of U] differentiable_on_subset[of _ U])


section \<open>Auxiliary Facts\<close>

subsubsection \<open>Transfer Lemmas\<close>

\<comment> \<open>If \<open>f\<close> and \<open>g\<close> agree near \<open>x\<close>, they have the same derivative at \<open>x\<close>.\<close>

subsection \<open>Combinatorics\<close>

lemma binomial_convolution_sum:
  fixes A B :: "nat \<Rightarrow> real"      
  shows
    "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j)))
     =
     (\<Sum> j \<le> Suc k. of_nat (Suc k choose j) * A j * B (Suc k - j))"
proof -
  let ?S1 = "\<Sum>j\<le>k. of_nat (k choose j) * A j       * B (Suc (k - j))"
  let ?S2 = "\<Sum>j\<le>k. of_nat (k choose j) * A (Suc j) * B (k   - j)"

  have split:
    "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j))) = ?S1 + ?S2"
    by (simp add: sum.distrib algebra_simps)
  
  have S1_rewrite:
    "?S1 = (\<Sum>j\<le>Suc k. of_nat (k choose j) * A j * B (Suc k - j))"   
    by (simp add: Suc_diff_le)

  have S1_split :
  "?S1 =
     of_nat (k choose 0) * A 0 * B (Suc k) +
     (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
  proof -   
    have "?S1 =
            (\<Sum>j\<in>{0..k}. of_nat (k choose j) * A j * B (Suc k - j))"
      using S1_rewrite atMost_atLeast0 by fastforce
    also have "\<dots> =
          of_nat (k choose 0) * A 0 * B (Suc k) +
          (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
      by (simp add: sum.atLeast_Suc_atMost)
      finally show ?thesis.
  qed

  have S2_rewrite:
    "?S2 =
       (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j       * B (Suc k - j))
     +   of_nat (k choose k)        * A (Suc k) * B 0"
  proof -
    let ?g = "\<lambda>j. of_nat (k choose j) * A (Suc j) * B (k - j)"

    have "?S2 = (\<Sum>j\<in>{0..k}. ?g j)"
      using atMost_atLeast0 by presburger      
    also have "\<dots> = (\<Sum>i\<in>{1..Suc k}. ?g (i - 1))"   
      by (rule sum.reindex_bij_witness
            [where i = "\<lambda>n::nat. n - 1"
               and j = Suc 
               and S = "{0..k}"
               and T = "{1..Suc k}" ], simp_all, auto)
    also have "\<dots> =
          (\<Sum>j\<in>{1..Suc k}. of_nat (k choose (j - 1)) *
                         A (j) * B (Suc k - j))"
      by auto   
    also have "\<dots> =
        (\<Sum>i\<in>{1..k}. of_nat (k choose (i - 1)) *
                     A i * B (Suc k - i))
      +   of_nat (k choose ((Suc k) - 1)) *
          A (Suc ((Suc k) - 1)) *
          B (Suc k - Suc k)"
      by (simp add: sum.insert_remove insert_absorb)
    also have "\<dots> =
        (\<Sum>i\<in>{1..k}. of_nat (k choose (i - 1)) *
                     A i * B (Suc k - i))
      +   of_nat (k choose k) * A (Suc k) * B 0"
      by simp
    finally show ?thesis.
  qed

  show "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j))) =
        (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) * A j * B (Suc k - j))"
  proof -     
    have "(\<Sum> j \<le> k. of_nat (k choose j) * (A j * B (Suc (k - j)) + A (Suc j) * B (k - j))) = 
          (\<Sum>j \<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j)) + A (Suc j) * B (k - j)))"
      using atLeast0AtMost by presburger
    also have "\<dots> =
        (\<Sum> j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j))))
      + (\<Sum> j\<in>{0..k}. of_nat (k choose j) * (A (Suc j) * B (k - j)))"
      by (simp add: sum.distrib algebra_simps)
    also have " \<dots> = (\<Sum>j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j)))) +  
                      (\<Sum>j\<in>{0..k}. of_nat (k choose j) *  A (Suc j) * B (k - j))"
      by (meson vector_space_over_itself.scale_scale)
    also have " \<dots>  =
            of_nat (k choose 0) * A 0 * B (Suc k) +
         (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j)) +
         (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j * B (Suc k - j))
       +   of_nat (k choose k)        * A (Suc k) * B 0"
    proof - 
      have fst_sum: "(\<Sum>j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j)))) 
        =  of_nat (k choose 0) * A 0 * B (Suc k) 
        + (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
        by (simp add: S1_split atLeast0AtMost vector_space_over_itself.scale_scale)
      moreover have snd_sum: "(\<Sum>j\<in>{0..k}. of_nat (k choose j) *  A (Suc j) * B (k - j)) = 
        (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j * B (Suc k - j))
       +   of_nat (k choose k)        * A (Suc k) * B 0"
        using S2_rewrite atLeast0AtMost by presburger
      ultimately show ?thesis
        by linarith
    qed
    also have "\<dots> =
      (of_nat (k choose 0) * A 0 * B (Suc k)
     + (\<Sum> j\<in>{1..k}.
          (of_nat (k choose j)       * A j * B (Suc k - j)
         + of_nat (k choose (j - 1)) * A j * B (Suc k - j))))
   + of_nat (k choose k) * A (Suc k) * B 0"
      by (simp add: sum.distrib)
    also have "\<dots> 
      = (of_nat (k choose 0) * A 0 * B (Suc k)
        + (\<Sum> j\<in>{1..k}. ((real (k choose j) + real (k choose (j - 1)))  * A j * B (Suc k - j))))
      + of_nat (k choose k) * A (Suc k) * B 0"
      by (simp add: distrib_left mult.commute)
    also have "\<dots> =
      of_nat (k choose 0) * A 0 * B (Suc k)
     + (\<Sum> j\<in>{1..k}. real (Suc k choose j) * A j * B (Suc k - j))
     + of_nat (k choose k) * A (Suc k) * B 0"
    proof - 
      have pascal_pointwise:
      "\<And>j. j \<in> {1..k} \<Longrightarrow>
         (real (k choose j) + real (k choose (j - 1)))
           * A j * B (Suc k - j)
       =  real (Suc k choose j)
           * A j * B (Suc k - j)"
        by (metis One_nat_def Suc_le_eq Suc_pred' 
            add.commute atLeastAtMost_iff binomial_Suc_Suc of_nat_add)
      then show ?thesis
        by (metis (no_types, lifting) sum.cong)
    qed
    also have "\<dots> =  (\<Sum>j\<le>Suc k.
            of_nat (Suc k choose j)
            * A j * B (Suc k - j))"
      by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
    finally show ?thesis.
  qed
qed


section \<open>Higher-Order Differentiability\<close>

subsection \<open>Definitions\<close>

text \<open>A function \<open>f :: real \<Rightarrow> real\<close> is \<open>k\<close>-times differentiable at \<open>a\<close> if it is
  \<open>(k - 1)\<close>-times differentiable near \<open>a\<close> and its \<open>(k - 1)\<close>-th derivative is
  differentiable at \<open>a\<close>.\<close>

primrec k_times_differentiable_at :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "k_times_differentiable_at 0 f a  \<longleftrightarrow>  True"
  | "k_times_differentiable_at (Suc k) f a \<longleftrightarrow>
      (\<exists>\<epsilon>>0. (\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f x))
    \<and>
      ((deriv ^^ k) f has_derivative (\<lambda>h. (deriv ^^ Suc k) f a * h)) (at a)"

abbreviation times_differentiable_at :: "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool"
  ("(_ _-times'_differentiable'_at _)" [100,100,100] 100)
  where "f k-times_differentiable_at a \<equiv> k_times_differentiable_at k f a"


subsection \<open>Basic Facts\<close>

lemma k_times_differentiable_at_SucD:
  assumes "f (Suc k)-times_differentiable_at a"
  shows "f k-times_differentiable_at a"
    and "((deriv ^^ k) f has_derivative (\<lambda>h. (deriv ^^ Suc k) f a * h)) (at a)"
  using assms
  by auto

lemma k_times_differentiable_at_mono:
  assumes "m \<le> k"
    and "f k-times_differentiable_at a"
  shows "f m-times_differentiable_at a"
  using assms
  by (induct k; auto simp: le_Suc_eq dest:)

lemma one_time_differentiable_at_iff:
  "f 1-times_differentiable_at a \<longleftrightarrow> (\<exists>f'. (f has_field_derivative f') (at a))"
  by (clarsimp, metis DERIV_imp_deriv has_field_derivative_def gt_ex)

lemma k_times_differentiable_at_le_deriv:
  assumes "f k-times_differentiable_at a"
    and "m < k"
  shows "((deriv ^^ m) f has_derivative (\<lambda>h. (deriv ^^ Suc m) f a * h)) (at a)"
    and "((deriv ^^ m) f has_real_derivative (deriv ^^ Suc m) f a) (at a)"
  unfolding has_field_derivative_def
  using k_times_differentiable_at_mono k_times_differentiable_at_SucD Suc_le_eq assms
  by presburger+

corollary k_times_differentiable_at_Suc_le_deriv:
  assumes "f (Suc k)-times_differentiable_at a"
    and "m \<le> k"
  shows "((deriv ^^ m) f has_derivative (\<lambda>h. (deriv ^^ Suc m) f a * h)) (at a)"
    and "((deriv ^^ m) f has_real_derivative (deriv ^^ Suc m) f a) (at a)"
  unfolding has_field_derivative_def
  using assms k_times_differentiable_at_le_deriv(1) le_imp_less_Suc
  by presburger+

corollary k_times_differentiable_ball_has_derivative_chain:
  assumes diff_ball: "\<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow> f n-times_differentiable_at z"
  shows   "\<forall>i<n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon>
    \<longrightarrow> ((deriv ^^ i) f has_derivative (\<lambda>h. (deriv ^^ Suc i) f z * h)) (at z)"
  by (metis assms k_times_differentiable_at_le_deriv(1))

lemma k_times_differentiable_at_SucE:
  assumes KD: "f (Suc k)-times_differentiable_at a"
  obtains \<epsilon> where "\<epsilon> > 0"
    and "\<And>x. \<bar>x - a\<bar> < \<epsilon> \<Longrightarrow> f k-times_differentiable_at x"
    and "((deriv ^^ k) f
           has_field_derivative (deriv ^^ Suc k) f a) (at a)"
  using assms has_field_derivative_def
    k_times_differentiable_at.simps(2) by blast

lemma k_times_differentiable_at_derivative:
  assumes "f (Suc k)-times_differentiable_at a"
  shows   "(deriv f) k-times_differentiable_at a"
using assms
proof (induction k arbitrary: f a)
  case (Suc p)
  obtain \<epsilon> where
      \<epsilon>_pos: "\<epsilon> > 0" and
      near:  "\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc p) f x" and
      deriv_cond:
        "((deriv ^^ Suc p) f
            has_derivative (\<lambda>h. (deriv ^^ Suc (Suc p)) f a * h)) (at a)"
    using Suc.prems
    unfolding k_times_differentiable_at.simps by blast

  have near_deriv:
    "\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at p (deriv f) x"
  proof clarify
    fix x assume hx: "\<bar>x - a\<bar> < \<epsilon>"
    from near[rule_format, OF hx]
      have "k_times_differentiable_at (Suc p) f x".
    hence "k_times_differentiable_at p (deriv f) x"
      by (rule Suc.IH)
    thus "k_times_differentiable_at p (deriv f) x".
  qed

  have deriv_cond':
    "((deriv ^^ p) (deriv f)
        has_derivative (\<lambda>h. (deriv ^^ Suc p) (deriv f) a * h)) (at a)"
    using deriv_cond kth_deriv_shift by metis

  show ?case
    using \<epsilon>_pos deriv_cond' near_deriv
      k_times_differentiable_at.simps(2) by blast
qed simp


subsection \<open>Continuity corollaries\<close>

lemma k_times_differentiable_at_imp_isCont:
  assumes "f (Suc k)-times_differentiable_at a"
  shows   "continuous (at a) f"
  using k_times_differentiable_at_le_deriv[OF assms, where m=0]
  by (simp add: DERIV_isCont has_field_derivative_def)

lemma k_times_differentiable_at_imp_isCont_kth_deriv:
  assumes KD: "f (Suc k)-times_differentiable_at a"
      and JL: "j \<le> k"
  shows   "continuous (at a) ((deriv ^^ j) f)"
  using assms
  by (meson has_derivative_continuous le_imp_less_Suc k_times_differentiable_at_le_deriv)


subsection \<open>Set-wise Higher-Order Derivatives\<close>

definition k_times_differentiable_on ::
  "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "k_times_differentiable_on k f S \<longleftrightarrow> (\<forall>x\<in>S. k_times_differentiable_at k f x)"

abbreviation times_differentiable_on
  :: "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real set \<Rightarrow> bool"
  ("(_ _-times'_differentiable'_on _)" [100,100,100] 100)
where
  "f k-times_differentiable_on S \<equiv> k_times_differentiable_on k f S"

lemma k_times_differentiable_onD:
  "f k-times_differentiable_on S \<Longrightarrow> x \<in> S
  \<Longrightarrow> f k-times_differentiable_at x"
  by (simp add: k_times_differentiable_on_def)

lemma k_times_differentiable_onI:
  "(\<And>x. x \<in> S \<Longrightarrow> f k-times_differentiable_at x) \<Longrightarrow>
    f k-times_differentiable_on S"
  by (simp add: k_times_differentiable_on_def)

lemma times_differentiable_on_iff_le:
  "f k-times_differentiable_on S
  \<longleftrightarrow> (\<forall>m\<le>k. f m-times_differentiable_on S)"
  unfolding k_times_differentiable_on_def
  using k_times_differentiable_at_mono
  by blast

lemma times_differentiable_on_Suc:
  "f (Suc k)-times_differentiable_on S
  \<Longrightarrow> f k-times_differentiable_on S"
  unfolding k_times_differentiable_on_def
  using k_times_differentiable_at_SucD(1)
  by blast

lemma times_differentiable_on_subset:
  "X \<subseteq> Y \<Longrightarrow> f k-times_differentiable_on Y
  \<Longrightarrow> f k-times_differentiable_on X"
  by (auto simp: k_times_differentiable_on_def)

lemma times_differentiable_on_transfer:
  "open S \<Longrightarrow> f k-times_differentiable_on S
  \<Longrightarrow> \<forall>x\<in>S. f x = g x
  \<Longrightarrow> g k-times_differentiable_on S
    \<and> (\<forall>x\<in>S. \<forall>m<k. ((deriv ^^ m) g has_derivative (*) ((deriv ^^ Suc m) f x)) (at x))"
proof (induct k arbitrary: S)
  case (Suc k)
  show ?case
  proof(cases "k=0")
    case True
    hence "g (Suc k)-times_differentiable_on S"
      using Suc
      by (clarsimp simp: k_times_differentiable_on_def)
        (metis at_within_open deriv_transfer(1) has_derivative_transform)
    moreover have "\<forall>x\<in>S. \<forall>m<Suc k. ((deriv ^^ m) g
      has_derivative (*) ((deriv ^^ Suc m) f x)) (at x)"
      using Suc.prems True calculation k_times_differentiable_on_def
      by (simp add: has_derivative_transfer_on_open)
    ultimately show ?thesis
      by simp
  next
    case False
    show ?thesis
    proof
      obtain n where "k = Suc n"
        using False not0_implies_Suc by presburger
      note IH1 = Suc.hyps[THEN conjunct2, OF \<open>open S\<close> _ Suc.prems(3),
              unfolded k_times_differentiable_on_def, rule_format]
      have obs: "\<And>x. x \<in> S \<Longrightarrow> (deriv ^^ k) g x = (deriv ^^ k) f x"
        using \<open>k = Suc n\<close>
        by (simp, intro deriv_eq IH1[simplified];
            clarsimp simp del: k_times_differentiable_at.simps)
          (metis Suc.prems(2) k_times_differentiable_on_def times_differentiable_on_Suc)
      have at_within_S: "at x within S = at x" if "x \<in> S" for x
        using at_within_open_subset[OF \<open>x \<in> S\<close> \<open>open S\<close>]
        by blast
      show first: "\<forall>x\<in>S.\<forall>m<Suc k. ((deriv^^m) g has_derivative (*) ((deriv^^Suc m) f x)) (at x)"
        using False
      proof(safe)
        fix z and m
        assume "0 < k" and "z \<in> S" and "m < Suc k"
        show "((deriv ^^ m) g has_derivative (*) ((deriv ^^ Suc m) f z)) (at z)"
        proof(cases "m = k")
          case True
          note transfer = has_derivative_transfer_on_open[OF \<open>open S\<close>, where f = "(deriv ^^ m) f"]
          show ?thesis
            using \<open>z \<in> S\<close> True less_Suc_eq obs
            by - ((rule transfer; clarsimp simp del: funpow.simps),
                metis Suc.prems(2) k_times_differentiable_at_SucD(2) k_times_differentiable_onD)
        next
          case False
          note f_k_diff = k_times_differentiable_at_SucD[OF
              Suc.prems(2)[unfolded k_times_differentiable_on_def, rule_format]]
          have "m < k"
            using False \<open>m < Suc k\<close> less_Suc_eq by blast
          thus ?thesis
            using \<open>z \<in> S\<close>
            using IH1 f_k_diff(1) by blast
        qed
      qed
      show "g (Suc k)-times_differentiable_on S"
      proof(rule k_times_differentiable_onI)
        fix x
        assume "x \<in> S"
        then obtain \<epsilon> where "\<epsilon> > 0" and "ball x \<epsilon> \<subseteq> S"
          and "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
          using \<open>open S\<close>
          by (meson Suc.prems(3) open_contains_ball subset_eq)
        hence fact1: "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> g k-times_differentiable_at y"
          using Suc(1)[OF open_ball] Suc(3)[THEN times_differentiable_on_Suc]
          times_differentiable_on_subset[OF \<open>ball x \<epsilon> \<subseteq> S\<close>]
          by (metis abs_minus_commute dist_real_def
              k_times_differentiable_on_def mem_ball)
        moreover have "((deriv ^^ k) g has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
          using first \<open>x \<in> S\<close> by blast
        ultimately show "g (Suc k)-times_differentiable_at x"
          using fact1
          by (clarsimp simp: k_times_differentiable_on_def,
              simp add: DERIV_imp_deriv has_field_derivative_def)
      qed
    qed
  qed
qed (simp add: k_times_differentiable_on_def)

lemma k_times_differentiable_on_imp_continuous_on:
  assumes  "f (Suc k)-times_differentiable_on S"
      and  "j \<le> k"
  shows   "continuous_on S ((deriv ^^ j) f)"
  using assms by (meson continuous_at_imp_continuous_on
      k_times_differentiable_at_imp_isCont_kth_deriv k_times_differentiable_on_def)

subsection \<open>Linearity of Higher Differentiability\<close>

lemma kth_deriv_commute_and_shift:
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows
    "((deriv ^^ k) ((deriv ^^ (m - k)) f) = (deriv ^^ (m - k)) ((deriv ^^ k) f)) \<and>
     ((deriv ^^ k) ((deriv ^^ (m - k)) f) = (deriv ^^ m) f) \<and>
     ((deriv ^^ k) f) (m - k)-times_differentiable_at  a"
  using assms
  by(induct k arbitrary: m, simp, metis (no_types, lifting) Suc_diff_Suc Suc_leD Suc_le_eq
            k_times_differentiable_at_derivative kth_deriv_simps(2) kth_deriv_shift)

corollary kth_deriv_commute_and_shift_dualE:
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows "((deriv ^^ (m - k)) f) k-times_differentiable_at a"
  by (metis kth_deriv_commute_and_shift assms diff_diff_cancel diff_le_self)

corollary kth_deriv_commute_and_shiftE:
  assumes "k \<le> m"
      and "f m-times_differentiable_at  a"
  shows "((deriv ^^ k) f) (m - k)-times_differentiable_at a"
  using kth_deriv_commute_and_shift assms by simp

lemma k_times_differentiable_at_const:
  "(deriv ^^ Suc m) (\<lambda>_. c) x = 0 \<and> k_times_differentiable_at (Suc m) (\<lambda>_. c) x"
proof (induct m arbitrary: x)
  case 0
  show ?case
  proof -
    have "k_times_differentiable_at 1 (\<lambda>r. c) x"
      by (metis has_derivative_const has_real_derivative one_time_differentiable_at_iff)
    then show ?thesis
      by simp
  qed
next
  fix m :: nat
  fix x :: real
  assume IH: "(\<And>x. (deriv ^^ Suc m) (\<lambda>_. c) x = 0 \<and> k_times_differentiable_at (Suc m) (\<lambda>_. c) x)"

  have prev_zero: "(deriv ^^ Suc m) (\<lambda>_. c) = (\<lambda>_. 0)"
  proof
    fix y :: real
    show "(deriv ^^ Suc m) (\<lambda>_. c) y = (\<lambda>_. 0) y"
      using IH[of y] by simp
  qed

  then have deriv_zero: "(deriv ^^ Suc (Suc m)) (\<lambda>_. c) x = 0"
    by simp

  moreover have diff_suc:
    "k_times_differentiable_at (Suc (Suc m)) (\<lambda>_. c) x"
  proof -
    have clause1:
      "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc m) (\<lambda>_. c) y"
      using IH by (intro exI[of _ 1], fastforce)

    have clause2:
      "((deriv ^^ Suc m) (\<lambda>_. c)
          has_derivative
           (\<lambda>h. (deriv ^^ Suc (Suc m)) (\<lambda>_. c) x * h)) (at x)"
    proof -
      have "\<exists>r. (\<lambda>r. (deriv ^^ Suc (Suc m)) (\<lambda>r. c) x)
          = (*) ((deriv ^^ Suc (Suc m)) (\<lambda>r. c) x)
        \<and> (\<lambda>ra. r) = (deriv ^^ Suc m) (\<lambda>r. c)"
      proof -
        have "\<exists>r. (\<forall>ra. r = (deriv ^^ Suc m) (\<lambda>r. c) ra)
          \<and> (\<forall>r. (deriv ^^ Suc (Suc m)) (\<lambda>r. c) x
            = (deriv ^^ Suc (Suc m)) (\<lambda>r. c) x * r)"
          using IH deriv_zero by fastforce
        then show ?thesis
          by blast
      qed
      then show ?thesis
        by (metis (no_types) deriv_zero has_derivative_const)
    qed
    show ?thesis
      unfolding k_times_differentiable_at.simps
      using clause1 clause2 by auto
  qed
  ultimately show "(deriv ^^ Suc (Suc m)) (\<lambda>_. c) x = 0
    \<and> k_times_differentiable_at (Suc (Suc m)) (\<lambda>_. c) x"
    unfolding k_times_differentiable_at.simps by simp
qed

(*Keep the next lemma here: it is line 534 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_const_eq:
  fixes x :: real
  assumes "k > 0"
  shows   "(deriv ^^ k) (\<lambda>_. c) x = 0"
proof (cases k)
  case 0
  then show ?thesis
    using assms by simp
next
  case (Suc m)
  then show ?thesis
    using k_times_differentiable_at_const by force
qed

(*Keep the next lemma here: it is line 548 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_const_cases:
  "(deriv ^^ k) (\<lambda>t::real. c) x = (if k = 0 then c else 0)"
  using kth_deriv_const_eq by auto

corollary k_times_differentiable_at_constE:
  "k_times_differentiable_at m (\<lambda>_. c) x"
  using k_times_differentiable_at_SucD k_times_differentiable_at_const
  by blast

lemma k_times_differentiable_at_id:
  "(deriv ^^ Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0) \<and>
     k_times_differentiable_at (Suc m) (\<lambda>t. t) x"
proof (induct m arbitrary: x)
  show "\<And>x. (deriv ^^ Suc 0) (\<lambda>t. t) x = (if 0 = 0 then 1 else 0)
    \<and> k_times_differentiable_at (Suc 0) (\<lambda>t. t) x"
    by (metis One_nat_def deriv_ident first_derivative_alt_def
        has_derivative_ident has_real_derivative one_time_differentiable_at_iff)
next
  fix m :: nat
  fix x :: real

  assume IH: "(\<And>x. (deriv ^^ Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0)
    \<and> k_times_differentiable_at (Suc m) (\<lambda>t. t) x)"

  have Dm1: "(deriv ^^ Suc (Suc m)) (\<lambda>t. t) x = 0"
  proof -
    have "(deriv ^^ Suc (Suc m)) (\<lambda>t. t) x  = ((deriv ^^ Suc m) (deriv (\<lambda>t. t))) x"
      using kth_deriv_shift by metis
    also have "\<dots> = ((deriv ^^ Suc m) (\<lambda>_.1)) x"
      by simp
    also have "\<dots> = 0"
      using k_times_differentiable_at_const by auto
    finally show ?thesis.
  qed

  have clause1:
    "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc m) (\<lambda>t. t) y"
    by (intro exI[of _ 1] conjI, simp_all,
        metis kth_deriv_simps(2) IH k_times_differentiable_at.simps(2))

  have clause2:
    "((deriv ^^ Suc m) (\<lambda>t. t)
        has_derivative (\<lambda>h. (deriv ^^ Suc (Suc m)) (\<lambda>t. t) x * h)) (at x)"
    using IH[of x] Dm1 by (cases m, simp_all, metis IH kth_deriv_simps(2)
        UNIV_I has_derivative_transform k_times_differentiable_at.simps(2)
        k_times_differentiable_at_const lambda_zero)

  show "(deriv ^^ Suc (Suc m)) (\<lambda>t. t) x = (if Suc m = 0 then 1 else 0)
    \<and> k_times_differentiable_at (Suc (Suc m)) (\<lambda>t. t) x"
    using Dm1 clause1 clause2 by auto
qed


(*Keep the next lemma here: it is line 601 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_id_eq':
  fixes x :: real
  shows
  "(deriv ^^ Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0)"
  using k_times_differentiable_at_id
  by (simp add: funpow_swap1 kth_deriv_const_eq)

(*Keep the next lemma here: it is line 608 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
lemma kth_deriv_id_cases:
  "(deriv ^^ k) (\<lambda>t::real. t) x =
     (if k = 0 then x else if k = 1 then 1 else 0)"
  by (metis kth_deriv_simps(1) kth_deriv_id_eq' One_nat_def not0_implies_Suc)

(*Keep the next lemma here: it is line 613 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_id_ge2_at:
  assumes "k \<ge> 2"
  shows   "(deriv ^^ k) (\<lambda>t::real. t) x = 0"
  using kth_deriv_id_cases assms by fastforce

(*Keep the next lemma here: it is line 618 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_id_1_eq:
  "(deriv ^^ Suc 0) (\<lambda>t. t) x = (1 :: real)"
  using kth_deriv_id_eq' by simp

(*Keep the next lemma here: it is line 622 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
corollary kth_deriv_id_eq:
  assumes "m > 0"
  shows "(deriv ^^ Suc m) (\<lambda>t. t) x = (0 :: real)"
  using kth_deriv_id_eq' assms
  by (metis less_not_refl)

corollary k_times_differentiable_at_idE:
  "(\<lambda>t. t) k-times_differentiable_at x"
  using k_times_differentiable_at_SucD k_times_differentiable_at_id by blast

\<comment> \<open>Generalises @{thm [source] deriv_cmult} to higher derivatives.\<close>

lemma kth_deriv_cmult:
  assumes "f k-times_differentiable_at x"
  shows   "(\<lambda>z. c * f z) k-times_differentiable_at  x \<and>
          (deriv ^^ k) (\<lambda>z. c * f z) x = c * (deriv ^^ k) f x"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by simp
next
  fix k :: nat
  fix x :: real
  assume IH: "(\<And>x. k_times_differentiable_at k f x
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. c * f z) x
      \<and> (deriv ^^ k) (\<lambda>z. c * f z) x = c * (deriv ^^ k) f x)"
  show "k_times_differentiable_at (Suc k) f x
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>z. c * f z) x
      \<and> (deriv ^^ Suc k) (\<lambda>z. c * f z) x = c * (deriv ^^ Suc k) f x"
  proof -
    assume k1: "k_times_differentiable_at (Suc k) f x"
    then obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0"
                 and neigh: "\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f y"
                 and deriv_f: "((deriv ^^ k) f
                                 has_field_derivative (deriv ^^ Suc k) f x) (at x)"
      using k_times_differentiable_at_SucE by blast

    have mult_rule:
      "((\<lambda>y. c * (deriv ^^ k) f y)
              has_field_derivative (c * (deriv ^^ Suc k) f x)) (at x)"
          using DERIV_chain' DERIV_cmult_Id deriv_f by blast

    then have deriv_trans:"((deriv ^^ k) (\<lambda>y. c * f y) has_derivative
            (\<lambda>h. (c * (deriv ^^ Suc k) f x) * h)) (at x)"
      unfolding has_field_derivative_def
      by(subst has_derivative_transfer_on_ball[where \<epsilon>=\<epsilon> and f="(\<lambda>y. c * (deriv ^^ k) f y)"],
         auto simp: \<epsilon>_pos IH dist_real_def neigh)
    then have "((deriv ^^ k) (\<lambda>y. c * f y)
           has_field_derivative  (c * (deriv ^^ Suc k) f x)) (at x)"
      using has_field_derivative_def by blast
    then have g2: "(deriv ^^ Suc k) (\<lambda>z. c * f z) x = c * (deriv ^^ Suc k) f x"
      by (simp add: DERIV_imp_deriv)

    have "k_times_differentiable_at (Suc k) (\<lambda>z. c * f z) x"
      using IH \<epsilon>_pos deriv_trans g2 neigh by auto
    then show ?thesis
      using g2 by blast
  qed
qed

corollary kth_deriv_cmult_eq:
  assumes "f k-times_differentiable_at x"
      and "(deriv ^^ k) f = f'"
  shows   "(deriv ^^ k) (\<lambda>y. c * f y) x = c * f' x"
  by (simp add: assms kth_deriv_cmult)

corollary kth_deriv_cmultE:
  assumes "f k-times_differentiable_at x"
  shows   "k_times_differentiable_at k (\<lambda>z. c * f z) x"
  using assms by(subst kth_deriv_cmult, simp_all)

corollary kth_derivative_uminus:
  assumes "f k-times_differentiable_at x"
  shows   "(deriv ^^ k) (\<lambda>t. - f t) x = - (deriv ^^ k) f x"
proof-
  have "k_times_differentiable_at k (\<lambda>z. (-1) * f z) x \<and>
          (deriv ^^ k) (\<lambda>z. (-1) * f z) x = (-1) * (deriv ^^ k) f x"
    using assms by(rule kth_deriv_cmult)
  then show ?thesis
    by auto
qed

corollary kth_deriv_uminus_eq:
  assumes "f k-times_differentiable_at x"
      and "(deriv ^^ k) f = f'"
  shows   "(deriv ^^ k) (\<lambda>t. - f t) x = - f' x"
  by (simp add: assms kth_derivative_uminus)

corollary kth_derivative_uminusE:
  assumes "f k-times_differentiable_at x"
  shows   "(\<lambda>t. - f t) k-times_differentiable_at x"
proof -
  have "k_times_differentiable_at k (\<lambda>t. -1 * f t) x"
    using assms by(subst kth_deriv_cmult, simp_all)
  then show ?thesis
    by simp
qed

\<comment> \<open>Generalises @{thm [source] deriv_add} to higher derivatives.\<close>

lemma kth_deriv_add:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  shows   "(\<lambda>y. f y + g y) k-times_differentiable_at x \<and>
             (deriv ^^ k) (\<lambda>y. f y + g y) x =
             (deriv ^^ k) f x + (deriv ^^ k) g x"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by simp
next
  fix k :: nat
  fix x :: real
  assume IH: "(\<And>x. k_times_differentiable_at k f x
    \<Longrightarrow> k_times_differentiable_at k g x
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. f y + g y) x
      \<and> (deriv ^^ k) (\<lambda>y. f y + g y) x = (deriv ^^ k) f x + (deriv ^^ k) g x)"
  show "k_times_differentiable_at (Suc k) f x
    \<Longrightarrow> k_times_differentiable_at (Suc k) g x
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>y. f y + g y) x
      \<and> (deriv ^^ Suc k) (\<lambda>y. f y + g y) x
        = (deriv ^^ Suc k) f x + (deriv ^^ Suc k) g x"
  proof -
    assume f_ksuc_diff: "k_times_differentiable_at (Suc k) f x"
    then obtain \<epsilon>f where \<epsilon>f: "\<epsilon>f > 0"
              and neigh_f:  "\<forall> y. \<bar>y - x\<bar> < \<epsilon>f \<longrightarrow> k_times_differentiable_at k f y"
              and diff_f:
                "((deriv ^^ k) f
                   has_field_derivative (deriv ^^ Suc k) f x) (at x)"
      using k_times_differentiable_at_SucE by blast
    assume g_ksuc_diff: "k_times_differentiable_at (Suc k) g x"
    then obtain \<epsilon>g where \<epsilon>g: "\<epsilon>g > 0"
                and neigh_g:  "\<forall> y. \<bar>y - x\<bar> < \<epsilon>g \<longrightarrow> k_times_differentiable_at k g y"
                and diff_g:
                  "((deriv ^^ k) g
                     has_field_derivative (deriv ^^ Suc k) g x) (at x)"
        using k_times_differentiable_at_SucE by blast

    define \<epsilon> where "\<epsilon> = min \<epsilon>f \<epsilon>g"
    have \<epsilon>_pos: "\<epsilon> > 0" by (simp add: \<epsilon>_def \<epsilon>f \<epsilon>g)

    have neigh_sum:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. f z + g z) y"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)

    have deriv_k_sum:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow>
          (deriv ^^ k) (\<lambda>z. f z + g z) y =
          (deriv ^^ k) f y + (deriv ^^ k) g y"
      using IH neigh_f neigh_g \<epsilon>_def
      by (auto simp: less_le_trans)

    have add_rule:
      "((\<lambda>y. (deriv ^^ k) f y + (deriv ^^ k) g y)
          has_field_derivative
           ((deriv ^^ Suc k) f x + (deriv ^^ Suc k) g x)) (at x)"
      using diff_f diff_g DERIV_add by blast

    then have diff_sum:
    "((deriv ^^ k) (\<lambda>y. f y + g y)
        has_derivative
          (\<lambda>h. ((deriv ^^ Suc k) f x +
                (deriv ^^ Suc k) g x) * h)) (at x)"
      by (subst has_derivative_transfer_on_ball[where \<epsilon>=\<epsilon>
            and f="(\<lambda>y. (deriv ^^ k) f y + (deriv ^^ k) g y)"],
          auto simp: \<epsilon>_pos deriv_k_sum dist_real_def has_field_derivative_def)

    have val_sum:
      "(deriv ^^ Suc k) (\<lambda>y. f y + g y) x =
         (deriv ^^ Suc k) f x + (deriv ^^ Suc k) g x"
      using diff_sum has_derivative_imp by force

    have sum_Suc:
      "k_times_differentiable_at (Suc k) (\<lambda>y. f y + g y) x"
      unfolding k_times_differentiable_at.simps
      using \<epsilon>_pos diff_sum neigh_sum val_sum by auto
    with val_sum show ?thesis
      by simp
  qed
qed

corollary kth_deriv_add_eq:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  assumes "(deriv ^^ k) f = f'"
  assumes "(deriv ^^ k) g = g'"
  shows   "(deriv ^^ k) (\<lambda>y. f y + g y) x  =  f'(x) + g'(x)"
  by (simp add: assms kth_deriv_add)

corollary kth_deriv_addE:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
    shows "(\<lambda>y. f y + g y) k-times_differentiable_at x"
  using assms
  by (subst kth_deriv_add, simp_all)

lemma kth_deriv_sub:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  shows   "(deriv ^^ k) (\<lambda>y. f y - g y) x =
           (deriv ^^ k) f x - (deriv ^^ k) g x"
proof -
  have "(deriv ^^ k) (\<lambda>y. f y - g y) x =
        (deriv ^^ k) (\<lambda>y. f y + (-1) * g y) x"
    by simp
  also have "\<dots> = (deriv ^^ k) f x  + (deriv ^^ k) (\<lambda>y. (-1) * g y) x"
    using assms kth_deriv_add kth_deriv_cmult by presburger
  also have "\<dots> = (deriv ^^ k) f x  - (deriv ^^ k) g x"
    by (metis add_uminus_conv_diff assms(2) kth_deriv_cmult mult_minus1)
  finally show ?thesis.
qed

corollary kth_deriv_sub_eq:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
      and "(deriv ^^ k) f = f'"
      and "(deriv ^^ k) g = g'"
  shows   "(deriv ^^ k) (\<lambda>t. f t - g t) x = f' x - g' x"
  by (simp add: assms kth_deriv_sub)

corollary kth_deriv_subE:
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
    shows "(\<lambda>y. f y - g y) k-times_differentiable_at x"
proof -
  from assms(1) have "k_times_differentiable_at k (\<lambda>y. f y + (\<lambda>z. -1* g z) y) x"
    by(rule kth_deriv_addE, simp_all, simp add: assms(2) kth_derivative_uminusE)
  then show ?thesis
    by auto
qed

\<comment> \<open>Leibniz formula for the \<open>k\<close>-th derivative of a product.\<close>
lemma kth_deriv_mult:
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
  shows   "(\<lambda>y. f y * g y) k-times_differentiable_at x \<and>
           (deriv ^^ k) (\<lambda>y. f y * g y) x =
           (\<Sum>j\<le>k. of_nat (k choose j) * (deriv ^^ j) f x * (deriv ^^ (k - j)) g x)"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by (simp add: fCk gCk)
next
  fix k :: nat
  fix x :: real

  let ?\<beta>  = "\<lambda>y. (\<Sum>j\<le>k. of_nat (k choose j) *
                        (deriv ^^ j) f y *
                        (deriv ^^ (k - j)) g y)"

  assume IH: "(\<And>x. k_times_differentiable_at k f x \<Longrightarrow>
                k_times_differentiable_at k g x \<Longrightarrow>
                k_times_differentiable_at k (\<lambda>y. f y * g y) x \<and>
  (deriv ^^ k) (\<lambda>y. f y * g y) x =
  (\<Sum>j\<le>k. real (k choose j) * (deriv ^^ j) f x * (deriv ^^ (k - j)) g x))"

  show "k_times_differentiable_at (Suc k) f x
    \<Longrightarrow> k_times_differentiable_at (Suc k) g x
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>y. f y * g y) x
      \<and> (deriv ^^ Suc k) (\<lambda>y. f y * g y) x
    = (\<Sum>j\<le>Suc k. real (Suc k choose j) * (deriv ^^ j) f x * (deriv ^^ (Suc k - j)) g x)"
  proof -
    assume f_ksuc_diff: "k_times_differentiable_at (Suc k) f x"
    assume g_ksuc_diff: "k_times_differentiable_at (Suc k) g x"

    obtain \<epsilon>f where \<epsilon>f: "\<epsilon>f > 0"
        and neigh_f:  "\<And>y. \<bar>y - x\<bar> < \<epsilon>f \<Longrightarrow> k_times_differentiable_at k f y"
        and diff_f:   "((deriv ^^ k) f has_field_derivative (deriv ^^ Suc k) f x) (at x)"
      using f_ksuc_diff k_times_differentiable_at_SucE by blast

    obtain \<epsilon>g where \<epsilon>g: "\<epsilon>g > 0"
      and neigh_g:  "\<And>y. \<bar>y - x\<bar> < \<epsilon>g \<Longrightarrow> k_times_differentiable_at k g y"
        and diff_g:   "((deriv ^^ k) g has_field_derivative (deriv ^^ Suc k) g x) (at x)"
      using g_ksuc_diff k_times_differentiable_at_SucE by blast

    define \<epsilon> where "\<epsilon> = min \<epsilon>f \<epsilon>g"
    have \<epsilon>_pos: "\<epsilon> > 0" by (simp add: \<epsilon>_def \<epsilon>f \<epsilon>g)

    have neigh_prod:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. f z * g z) y"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)

    have deriv_k_prod:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow>
        (deriv ^^ k) (\<lambda>z. f z * g z) y =
          (\<Sum>j\<le>k. of_nat (k choose j) * (deriv ^^ j) f y * (deriv ^^ (k - j)) g y)"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)

    have beta_deriv:
      "((\<lambda>y. ?\<beta> y) has_field_derivative
         (\<Sum>j\<le>k. of_nat (k choose j) *
                 ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                  (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x))) (at x)"
    proof -
      have f1: "((\<lambda>x. of_nat (k choose j) *
                 ((deriv ^^ j) f x * (deriv ^^ (k - j)) g x))
             has_field_derivative
               of_nat (k choose j) *
                 ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                  (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x)) (at x)"
         if "j \<le> k" for j
      proof -
        have "k_times_differentiable_at (Suc (k - j)) g x \<and> k_times_differentiable_at (Suc j) f x"
          by (metis (no_types) f_ksuc_diff g_ksuc_diff k_times_differentiable_at_mono
              le_add_same_cancel2 not_less_eq_eq that zero_le
              ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
        then have "((\<lambda>r. (deriv ^^ j) f r * (deriv ^^ (k - j)) g r) has_real_derivative
          (deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x
          + (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x) (at x)"
          using DERIV_mult' k_times_differentiable_at_SucE by blast
        then show ?thesis
          using DERIV_chain' DERIV_cmult_Id by blast
      qed
      then have f2:
      "j \<le> k \<Longrightarrow>
       ((\<lambda>x. of_nat (k choose j) *
              (deriv ^^ j) f x * (deriv ^^ (k - j)) g x)
          has_derivative
            (\<lambda>h. (of_nat (k choose j) *
                  ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                   (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x)) * h))
          (at x)"
      for j
      unfolding has_field_derivative_def
      by (meson UNIV_I ab_semigroup_mult_class.mult_ac(1) has_derivative_transform)

      then have beta_deriv:
      "((\<lambda>y. ?\<beta> y) has_derivative
          (\<lambda>h. \<Sum>j\<le>k. (of_nat (k choose j) *
                     ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                      (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x)) * h))
         (at x)"
        by(rule has_derivative_sum, simp)
      then show ?thesis
        by (metis (no_types, lifting) DERIV_imp_deriv has_derivative_imp
            has_real_derivative mult_cancel_left2 sum.cong)
    qed

    then have diff_prod:
    "((deriv ^^ k) (\<lambda>y. f y * g y)
        has_derivative
          (\<lambda>h. (\<Sum>j\<le>k. of_nat (k choose j) *
                   ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                    (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x)) * h))
      (at x)"
      by(subst has_derivative_transfer_on_ball[where \<epsilon> = \<epsilon> and f = "(\<lambda>y. ?\<beta> y)"],
         auto simp: \<epsilon>_pos deriv_k_prod dist_real_def has_field_derivative_def)

    have comb_id:
      "(\<Sum>j\<le>k. of_nat (k choose j) *
                ((deriv ^^ j) f x * (deriv ^^ Suc (k - j)) g x +
                 (deriv ^^ Suc j) f x * (deriv ^^ (k - j)) g x))
       = (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                      (deriv ^^ j) f x * (deriv ^^ (Suc k - j)) g x)"
      by(rule binomial_convolution_sum)
    then have
      "(deriv ^^ Suc k) (\<lambda>y. f y * g y) x =
         (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                      (deriv ^^ j) f x * (deriv ^^ (Suc k - j)) g x)"
      using diff_prod has_derivative_imp by force
    then show ?thesis
      using \<epsilon>_pos comb_id diff_prod neigh_prod  by auto
  qed
qed

corollary Leibniz_prod_eq:
  fixes F G :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
      and Ffam: "\<And>j. j \<le> k \<Longrightarrow> (deriv ^^ j) f = F j"
      and Gfam: "\<And>j. j \<le> k \<Longrightarrow> (deriv ^^ j) g = G j"
  shows "(deriv ^^ k) (\<lambda>y. f y * g y) x
         = (\<Sum> j\<le>k. of_nat (k choose j) * F j x * G (k - j) x)"
  by (subst kth_deriv_mult[OF fCk gCk], rule sum.cong[OF refl], simp_all add: Ffam Gfam)

corollary kth_deriv_multE:
  fixes f g :: "real \<Rightarrow> real"  and k :: nat and x :: real
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
    shows      "(\<lambda>y. f y * g y) k-times_differentiable_at x"
  using assms by(subst kth_deriv_mult, simp_all)

lemma kth_deriv_sum_upto:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
  shows   "(\<lambda>y. \<Sum>i\<le>n. F i y) k-times_differentiable_at x \<and>
               (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x =
             (\<Sum>i\<le>n. (deriv ^^ k) (F i) x)"
  using assms
proof (induct n arbitrary: x)
  case 0
  thus ?case
    by (simp add: diff)
next
  fix n :: nat
  fix x :: real
  assume IH: "(\<And>x. (\<And>i. i \<le> n \<Longrightarrow> k_times_differentiable_at k (F i) x)
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x
    \<and> (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x = (\<Sum>i\<le>n. (deriv ^^ k) (F i) x))"
  show "(\<And>j. j \<le> Suc n \<Longrightarrow> k_times_differentiable_at k (F j) x)
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x
    \<and> (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x = (\<Sum>i\<le>Suc n. (deriv ^^ k) (F i) x)"
  proof -
    assume when_differentiable: "(\<And>j. j \<le> Suc n \<Longrightarrow> k_times_differentiable_at k (F j) x)"
    show "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x \<and>
          (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x =
            (\<Sum>i\<le>Suc n. (deriv ^^ k) (F i) x)"
    proof -
      have IH_inst:
        "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x \<and>
         (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x =
           (\<Sum>i\<le>n. (deriv ^^ k) (F i) x)"
        using IH[of x] when_differentiable
        by (simp add: le_Suc_eq)

      have add_rule:
        "k_times_differentiable_at k
            (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y) x \<and>
         (deriv ^^ k)
            (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y) x =
            (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x +
            (deriv ^^ k) (F (Suc n)) x"
        using kth_deriv_add[OF conjunct1[OF IH_inst] when_differentiable[of "Suc n"]]
        by blast

      show "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x \<and>
         (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x =
           (\<Sum>i\<le>Suc n. (deriv ^^ k) (F i) x)"
        by (simp add: add_rule conjunct2[OF IH_inst])
    qed
  qed
qed

corollary kth_deriv_sum_upto_eq:
  fixes F H :: "nat \<Rightarrow> real \<Rightarrow> real"
  fixes k n :: nat and x :: real
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
      and fam:  "\<And>i. i \<le> n \<Longrightarrow> (deriv ^^ k) (F i) = H i"
  shows "(deriv ^^ k) (\<lambda>y. \<Sum> i\<le>n. F i y) x
         = (\<Sum> i\<le>n. H i x)"
  using fam by(subst kth_deriv_sum_upto[OF diff], simp, force)

lemma kth_deriv_sum_uptoE:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
  shows   "(\<lambda>y. \<Sum>i\<le>n. F i y) k-times_differentiable_at x"
  using assms by(subst kth_deriv_sum_upto, simp_all)

lemma k_times_differentiable_at_pow_funE:
  "f m-times_differentiable_at x \<Longrightarrow>
   (\<lambda>t. (f t)^n) m-times_differentiable_at x"
  by (induct n, simp add: k_times_differentiable_at_constE, simp add: kth_deriv_multE)

corollary kth_deriv_pow_fun_eq:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes fCk: "f m-times_differentiable_at x"
      and fam: "\<And>j. j \<le> m \<Longrightarrow> (deriv ^^ j) f = F j"
  shows
    "(deriv ^^ m) (\<lambda>t. (f t)^(Suc r)) x
     = (\<Sum> j\<le>m. of_nat (m choose j) * F j x
              * (deriv ^^ (m - j)) (\<lambda>t. (f t)^r) x)"
  by (simp add: kth_deriv_mult[OF fCk k_times_differentiable_at_pow_funE[OF fCk]] fam)


named_theorems kdiff "Theorems about the existence of higher derivatives."
declare kth_deriv_commute_and_shift_dualE[kdiff]
declare kth_deriv_commute_and_shiftE[kdiff]
declare k_times_differentiable_at_constE[kdiff]
declare k_times_differentiable_at_idE[kdiff]
declare kth_deriv_cmultE[kdiff]
declare kth_derivative_uminusE[kdiff]
declare kth_deriv_addE[kdiff]
declare kth_deriv_subE[kdiff]
declare kth_deriv_multE[kdiff]
declare kth_deriv_sum_uptoE[kdiff]
declare k_times_differentiable_at_pow_funE[kdiff]

named_theorems kderivs "Theorems about higher derivative equalities"
declare first_derivative_alt_def[kderivs]
declare second_derivative_alt_def[kderivs]
declare kth_deriv_const_eq[kderivs]
declare kth_deriv_const_cases[kderivs]
declare kth_deriv_id_eq'[kderivs]
declare kth_deriv_id_cases[kderivs]
declare kth_deriv_id_ge2_at[kderivs]
declare kth_deriv_id_1_eq[kderivs]
declare kth_deriv_id_eq[kderivs]
declare kth_deriv_cmult_eq[kderivs]
declare kth_deriv_uminus_eq[kderivs]
declare kth_deriv_add_eq[kderivs]
declare kth_deriv_sub_eq[kderivs]
declare Leibniz_prod_eq[kderivs]
declare kth_deriv_sum_upto_eq[kderivs]
declare kth_deriv_pow_fun_eq[kderivs]

subsection \<open>Derivative Formulas for Shifted Monomials\<close>

lemma k_times_differentiable_at_pow[kdiff]:
 "(\<lambda>t. (t - a) ^ i) m-times_differentiable_at x"
 by (simp add: k_times_differentiable_at_constE k_times_differentiable_at_idE k_times_differentiable_at_pow_funE
      kth_deriv_subE)

(*FAILING
corollary kth_deriv_cmult_pow [kderivs]:
  "(deriv ^^ k) (\<lambda>t::real. (c * t) ^ n) x = (c ^ n) * (deriv ^^ k) (\<lambda>t. t ^ n) x"
  by (simp add: kdiff kderivs)
*)

lemma kth_deriv_affine_cases [kderivs]:
  "(deriv ^^ k) (\<lambda>t::real. a*t + b) x =
     (if k = 0 then a*x + b else if k = 1 then a else 0)"
  by  (simp_all add: kdiff kderivs)

lemma kth_deriv_prod_high_order_zero[kderivs]:
  assumes fvan: "\<And>j. j \<ge> a \<Longrightarrow> (deriv ^^ j) f x = 0"
      and gvan: "\<And>m. m \<ge> b \<Longrightarrow> (deriv ^^ m) g x = 0"
      and kdeg: "k \<ge> a + b - 1"
      and fdiff: "f k-times_differentiable_at x"
      and gdiff: "g k-times_differentiable_at x"
  shows "(deriv ^^ k) (\<lambda>t. f t * g t) x = 0"
proof -
  have Leib:
    "(deriv ^^ k) (\<lambda>t. f t * g t) x
     = (\<Sum> j\<le>k. of_nat (k choose j) * (deriv ^^ j) f x * (deriv ^^ (k - j)) g x)"
    by (simp add: Leibniz_prod_eq kdiff fdiff gdiff)
  have "\<dots> = 0"
  proof (rule sum.neutral, intro ballI)
    fix j assume jl: "j \<in> {..k}"
    have jle: "j \<le> k" using jl by simp
    have "j \<ge> a \<or> k - j \<ge> b"
      using kdeg jle by arith
    then show "of_nat (k choose j) * (deriv ^^ j) f x * (deriv ^^ (k - j)) g x = 0"
      using fvan gvan by auto
  qed
  with Leib show ?thesis by simp
qed

lemma kth_deriv_power_high_order_zero:
  fixes f :: "real \<Rightarrow> real" and x :: real
  fixes M p n :: nat
  assumes diff: "\<And>q. q \<le> p \<Longrightarrow> f q-times_differentiable_at x"
      and van : "\<And>m. m \<ge> M \<Longrightarrow> (deriv ^^ m) f x = 0"
  shows "\<And>r. r \<le> p \<Longrightarrow> r > n * (M - 1) \<Longrightarrow> (deriv ^^ r) (\<lambda>t. (f t) ^ n) x = 0"
proof (induction n)
  case 0
  then show ?case
    using kth_deriv_monomial_zero by fastforce
next
  case (Suc n)
  fix r assume rle: "r \<le> p" and rgt: "r > Suc n * (M - 1)"
  from diff[OF rle] have fC: "f r-times_differentiable_at x" .
  from fC have fnC: "(\<lambda>t. (f t) ^ n) r-times_differentiable_at x"
    using k_times_differentiable_at_pow_funE by auto


  have Leib:
    "(deriv ^^ r) (\<lambda>t. (f t) ^ Suc n) x
       = (\<Sum> j\<le>r. of_nat (r choose j)
                 * (deriv ^^ j) f x
                 * (deriv ^^ (r - j)) (\<lambda>t. (f t) ^ n) x)"
    by (simp add: Leibniz_prod_eq kdiff fC fnC)

  have each_zero:
    "\<And>j. j \<le> r \<Longrightarrow>
      of_nat (r choose j) * (deriv ^^ j) f x
        * (deriv ^^ (r - j)) (\<lambda>t. (f t) ^ n) x = 0"
  proof -
    fix j assume jl: "j \<le> r"
    show "of_nat (r choose j) * (deriv ^^ j) f x
            * (deriv ^^ (r - j)) (\<lambda>t. (f t) ^ n) x = 0"
    proof (cases "j \<ge> M")
      case True
      then show ?thesis by (simp add: van)
    next
      case False
      hence jlt: "j \<le> M - 1" by simp
      have rj_gt: "r - j > n * (M - 1)"
        using jlt rgt by fastforce

      have rj_le: "r - j \<le> p" using rle jl by simp
      have "(deriv ^^ (r - j)) (\<lambda>t. (f t) ^ n) x = 0"
        using Suc.IH rj_le rj_gt diff van by blast
      thus ?thesis by simp
    qed
  qed

  have "(\<Sum> j\<le>r. of_nat (r choose j)
                 * (deriv ^^ j) f x
                 * (deriv ^^ (r - j)) (\<lambda>t. (f t) ^ n) x) = 0"
    by (rule sum.neutral) (auto simp: each_zero)
  with Leib
  show "(deriv ^^ r) (\<lambda>t. (f t) ^ Suc n) x = 0"
    by presburger
qed

subsection \<open>Relationship between Differentiability at a Point and $C^k(U)$\<close>

lemma n_times_diff_imp_lower_deriv_diff:
  assumes "f n-times_differentiable_at x"
      and "k < n"
  shows "((deriv ^^ k) f) differentiable (at x)"
  using assms
  using differentiable_def k_times_differentiable_at_le_deriv by blast

lemma SucSucn_times_diff_imp_Cn_on:
  assumes "f (Suc (Suc n))-times_differentiable_at x"
  shows   "\<exists>\<epsilon>>0. C_k_on n f {x - \<epsilon> <..< x + \<epsilon>}"
proof -
  have "(\<exists>(\<epsilon> :: real) >0.  (\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc n) f y))"
    using assms by auto
  then obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0"
    and n_diff_ball: "(\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc n) f y)"
    by blast
  then have n_diff_on: "k_times_differentiable_on (Suc n) f {y. \<bar>y - x\<bar> < \<epsilon>}"
    by (simp add: k_times_differentiable_on_def)

  define U where "U \<equiv> {x - \<epsilon> <..< x + \<epsilon>}"
  have openU: "open U" by (simp add: U_def)

  have U_def2:"U = {y. \<bar>y - x\<bar> < \<epsilon>}"
    by(auto, (simp add: U_def abs_diff_less_iff)+)
  have n_cont_U:
    "continuous_on U ((deriv ^^ n) f)"
    using k_times_differentiable_on_imp_continuous_on
      U_def2 n_diff_on
    by force

  have Cn_on_U:
    "C_k_on n f U"
  proof (cases n)
    case 0
    show ?thesis
      using "0" C_k_on_def kth_deriv_simps(1)
        n_cont_U openU by metis
  next
    case (Suc m)
    have 1: "open U" by (simp add: openU)
    have 2: "\<forall>k < n.
               ((deriv ^^ k) f) differentiable_on U
             \<and> continuous_on U ((deriv ^^ Suc k) f)"
      by (metis DERIV_deriv_iff_real_differentiable kth_deriv_simps(2)
          k_times_differentiable_at_Suc_le_deriv(2) Suc_leD Suc_leI U_def2
          differentiable_on_eq_differentiable_at k_times_differentiable_on_def
          k_times_differentiable_on_imp_continuous_on n_diff_on openU)
    from 1 2 Suc show ?thesis
      unfolding C_k_on_def by simp
  qed
  show ?thesis
    using \<epsilon>_pos Cn_on_U U_def by blast
qed

lemma C_k_on_imp_k_times_differentiable_on:
  assumes "C_k_on k f U"
  shows   "f k-times_differentiable_on U"
using assms
proof (induction k)
  case 0
  show ?case
    unfolding C_k_on_def k_times_differentiable_on_def by simp
next
  case (Suc k)
  from Suc.prems have
    open_ball: "open U" and
    Ck: "\<forall>j<k. ((deriv ^^ j) f) differentiable_on U
         \<and> continuous_on U ((deriv ^^ Suc j) f)"
    unfolding C_k_on_def by simp_all

  have step:
    "((deriv ^^ k) f) differentiable_on U"
    using Ck [rule_format, of k]
    using C_k_on_def Suc.prems by auto

  have cont:
    "continuous_on U ((deriv ^^ Suc k) f)"
    using Ck[rule_format, of]
    using C_k_on_def Suc.prems by auto

  have "\<forall>j\<le>k.
          ((deriv ^^ j) f) differentiable_on U
        \<and> continuous_on U
            ((deriv ^^ Suc j) f)"
    using Ck step cont
    by (metis dual_order.order_iff_strict)

  have
    "k_times_differentiable_on (Suc k) f U"
  proof(rule k_times_differentiable_onI)
    fix y :: real
    assume y_in: "y \<in> U"
    show "k_times_differentiable_at (Suc k) f y"
    proof -
      have clause1: "(\<exists>\<epsilon>>0.  (\<forall>x. \<bar>x - y\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f x)) "
      proof -
        from Ck open_ball have kdiff_on:
          "k_times_differentiable_on k f U"
          unfolding C_k_on_def
          by (metis C_k_on_def kth_deriv_simps(1) Suc.IH
              differentiable_imp_continuous_on local.step)
        then have kdiff_at_U:
          "\<forall>z\<in>U. k_times_differentiable_at k f z"
          unfolding k_times_differentiable_on_def by simp

        from open_ball y_in obtain \<delta> where \<delta>_pos:
          "\<delta> > 0" and \<delta>_ball: "ball y \<delta> \<subseteq> U"
          by (meson open_contains_ball)
        then have sub: "\<forall>z. \<bar>z - y\<bar> < \<delta> \<longrightarrow> z \<in> U"
          by (metis dist_commute dist_real_def mem_ball subset_eq)
        then show ?thesis
          using \<delta>_pos kdiff_at_U by blast
      qed
      have clause2:
        "((deriv ^^ k) f has_derivative (\<lambda>h. (deriv ^^ Suc k) f y * h)) (at y)"
        using DERIV_deriv_iff_real_differentiable has_field_derivative_def
          differentiable_on_eq_differentiable_at local.open_ball local.step y_in
        by fastforce
      thus ?thesis
        by (simp add: clause1)
    qed
  qed
  thus ?case.
qed

subsection \<open>Closure of \(C^{k}\)\<close>

text \<open>Closure of \<open>C\<^sup>k\<close> under the algebraic operations (for inverses and quotients,
  \<open>C\<^sup>1\<close> only).\<close>

lemma C_k_const:
  assumes "open U"
  shows   "C_k_on k (\<lambda>_. c) U"
proof (cases k)
  case 0
  have "continuous_on U (\<lambda>x. c)"
    by simp
  with 0 assms show ?thesis
    unfolding C_k_on_def by simp
next
  case (Suc m)
  have diff0:
    "k_times_differentiable_on k (\<lambda>x. c) U"
    by (simp add: k_times_differentiable_at_constE k_times_differentiable_onI)
  moreover have
    "\<forall>j<k. ((deriv ^^ j) (\<lambda>x. c)) differentiable_on U
           \<and> continuous_on U ((deriv ^^ Suc j) (\<lambda>x. c))"
  proof clarify
    fix j :: nat
    assume j_bound: "j < k"
    with k_times_differentiable_at_const
    show "(deriv ^^ j) (\<lambda>x. c) differentiable_on U
      \<and> continuous_on U ((deriv ^^ Suc j) (\<lambda>x. c))"
      by (meson differentiable_at_imp_differentiable_on
          differentiable_imp_continuous_on lessI n_times_diff_imp_lower_deriv_diff)
  qed
  ultimately show ?thesis
    by (simp add: C_k_on_def assms)
qed

lemma C_k_ident:
  assumes "open U"
  shows   "C_k_on k (\<lambda>x. x) U"
proof (induction k)
  case 0
  have "continuous_on U (\<lambda>x. x)"
    by simp
  with 0 assms show ?case
    unfolding C_k_on_def by simp
next
  case (Suc k)
  have openU: "open U" by fact
  have derivs:
    "\<forall>j< Suc k.
        ((deriv ^^ j) (\<lambda>x. x)) differentiable_on U \<and>
        continuous_on U ((deriv ^^ Suc j) (\<lambda>x. x))"
  proof clarify
    fix j
    assume jlt: "j < Suc k"
    have "((deriv ^^ j) (\<lambda>x. x)) differentiable_on U"
      by (cases j; metis k_times_differentiable_at_idE less_iff_Suc_add
          differentiable_at_imp_differentiable_on
          n_times_diff_imp_lower_deriv_diff)
    moreover have
      "continuous_on U ((deriv ^^ Suc j) (\<lambda>x. x))"
      by (cases j; metis k_times_differentiable_at_idE k_times_differentiable_onI
          k_times_differentiable_on_imp_continuous_on less_or_eq_imp_le)

    ultimately show
      "((deriv ^^ j) (\<lambda>x. x)) differentiable_on U \<and>
       continuous_on U ((deriv ^^ Suc j) (\<lambda>x. x))"
      by simp
  qed
  with openU Suc show ?case
    unfolding C_k_on_def by simp
qed

lemma C_k_scale:
  assumes     fCk   : "C_k_on n f U"
  shows   "C_k_on n (\<lambda>y. c * f y) U"
proof -
  have openU: "open U"
    using C_k_on_def fCk by presburger
  show ?thesis
    using assms
  proof (cases n)
    case 0
    from fCk have cont: "continuous_on U f"
      unfolding C_k_on_def 0 by simp
    hence "continuous_on U (\<lambda>y. c * f y)"
      using continuous_on_mult_left by blast
    with openU 0 show ?thesis
      unfolding C_k_on_def by simp
  next
    fix m :: nat
    assume n_nonzero: "n = Suc m"

    from fCk obtain f_diff:
      "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast

    hence scale_diff:
      "k_times_differentiable_on n (\<lambda>y. c * f y) U"
      using k_times_differentiable_on_def kth_deriv_cmultE by force
    from fCk have
      f_D_C: "\<forall>k<n. ((deriv ^^ k) f) differentiable_on U
                    \<and> continuous_on U ((deriv ^^ Suc k) f)"
      by (simp add: C_k_on_def n_nonzero)
    have Ck_less_n:
      "\<forall>k<n.
         ((deriv ^^ k) (\<lambda>y. c * f y)) differentiable_on U \<and>
         continuous_on U ((deriv ^^ Suc k) (\<lambda>y. c * f y))"
    proof clarify
      fix k assume k_lt_n: "k < n"
      from f_D_C[rule_format, OF k_lt_n] obtain
          Df: "((deriv ^^ k) f) differentiable_on U"
        and Cf: "continuous_on U ((deriv ^^ Suc k) f)"
        by blast
      have Dscale:
        "((deriv ^^ k) (\<lambda>y. c * f y)) differentiable_on U"
        by (metis differentiable_at_imp_differentiable_on k_lt_n
            k_times_differentiable_on_def n_times_diff_imp_lower_deriv_diff scale_diff)
      have Cscale:
        "continuous_on U ((deriv ^^ Suc k) (\<lambda>y. c * f y))"
      proof -
        have eq_on:
          "\<forall>y\<in>U.
             (deriv ^^ Suc k) (\<lambda>y. c * f y) y =
             c * (deriv ^^ Suc k) f y"
        proof(clarify)
          fix y :: real
          assume "y \<in> U"
          then show "(deriv ^^ Suc k) (\<lambda>y. c * f y) y = c * (deriv ^^ Suc k) f y"
            by(subst kth_deriv_cmult,
               meson Suc_leI f_diff k_lt_n k_times_differentiable_at_mono
               k_times_differentiable_onD, simp)
        qed
        have cont_rhs:
          "continuous_on U (\<lambda>y. c * (deriv ^^ Suc k) f y)"
          using Cf  continuous_on_mult_left by blast
        show ?thesis
          using cont_rhs eq_on
          by (metis continuous_on_cong)
      qed
      show "((deriv ^^ k) (\<lambda>y. c * f y)) differentiable_on U \<and>
            continuous_on U ((deriv ^^ Suc k) (\<lambda>y. c * f y))"
        using Dscale Cscale by blast
    qed
    with openU n_nonzero scale_diff
    show ?thesis
      unfolding C_k_on_def by simp
  qed
qed

lemma C_k_neg:
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes fCk: "C_k_on n f U"
  shows   "C_k_on n (\<lambda>y. - f y) U"
proof -
  have "C_k_on n (\<lambda>y. (-1) * f y) U"
    by (rule C_k_scale[OF fCk])
  thus ?thesis
    by (simp add: fun_eq_iff)
qed

lemma C_k_add:
  assumes fCk: "C_k_on n f U"
      and gCk: "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y + g y) U"
proof -
  have openU: "open U"
    using C_k_on_def fCk by presburger

  show ?thesis
    using assms
  proof (cases n)
    case 0
    with fCk gCk have cont:
      "continuous_on U f"  "continuous_on U g"
      unfolding C_k_on_def by auto
    have "continuous_on U (\<lambda>y. f y + g y)"
      using cont by (simp add: continuous_on_add)
    with openU 0 show ?thesis
      unfolding C_k_on_def by simp
  next
    fix m :: nat
    assume f_Cn: "C_k_on n f U"
    then have f_n_diff: "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume g_Cn: "C_k_on n g U"
    then have g_n_diff: "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume n_nonzero: "n = Suc m"

    have sum_n_diff: "k_times_differentiable_on n (\<lambda>y. f(y)+ g(y)) U"
      using f_n_diff g_n_diff k_times_differentiable_on_def kth_deriv_add by auto

    with f_Cn have f_diff: "(\<forall>k < n. ((deriv ^^ k) f) differentiable_on U
                         \<and> continuous_on U ((deriv ^^ Suc k) f))"
      unfolding C_k_on_def by auto

    with g_Cn have g_diff: "(\<forall>k < n. ((deriv ^^ k) g) differentiable_on U
                         \<and> continuous_on U ((deriv ^^ Suc k) g))"
      unfolding C_k_on_def by auto

    with f_n_diff g_n_diff sum_n_diff
    have Ck_less_n:
      "(\<forall>k < n.
          ((deriv ^^ k) (\<lambda>x. f x + g x)) differentiable_on U
        \<and> continuous_on U ((deriv ^^ Suc k) (\<lambda>x. f x + g x)))"
    proof (clarify)
      fix k :: nat
      assume "k < n"

      have f_diff: "\<forall>k<n. (deriv ^^ k) f differentiable_on U"
        using f_diff by blast
      have g_diff: "\<forall>k<n. (deriv ^^ k) g differentiable_on U"
        using g_diff by blast
      have Ck_less_n:
        "\<forall>k<n.
            ((deriv ^^ k) (\<lambda>x. f x + g x)) differentiable_on U \<and>
            continuous_on U ((deriv ^^ Suc k) (\<lambda>x. f x + g x))"
        using f_n_diff g_n_diff

      proof clarify
        fix k :: nat
        assume k_lt_n: "k < n"
        from f_diff[rule_format, OF k_lt_n] have
                Df: "((deriv ^^ k) f) differentiable_on U"
            and Cf: "continuous_on U ((deriv ^^ Suc k) f)"
          by(blast, metis C_k_on_def f_Cn k_lt_n n_nonzero nat.distinct(1))

        from g_diff[rule_format, OF k_lt_n] have
                Dg: "((deriv ^^ k) g) differentiable_on U"
            and Cg: "continuous_on U ((deriv ^^ Suc k) g)"
          by(blast, metis C_k_on_def g_Cn k_lt_n n_nonzero nat.distinct(1))
        have Dsum:
          "((deriv ^^ k) (\<lambda>x. f x + g x)) differentiable_on U"
          by (metis differentiable_at_imp_differentiable_on k_lt_n k_times_differentiable_onD
              n_times_diff_imp_lower_deriv_diff sum_n_diff)

        from Cf Cg
        have "continuous_on U (\<lambda>x. (deriv ^^ Suc k) f x + (deriv ^^ Suc k) g x)"
          by(rule continuous_on_add)
        then have continuous_on: "\<forall>y\<in> U.  continuous (at y within U)
             (\<lambda>t. (deriv ^^ Suc k) f t + (deriv ^^ Suc k) g t)"
          using continuous_on_eq_continuous_within by blast

        have "\<forall>y\<in> U. continuous (at y within U)(\<lambda>t. (deriv ^^ Suc k) (\<lambda>x. f x + g x) t)"
        proof clarify
          fix y :: real
          assume y_bound: "y \<in> U"
          have f_Suc_k_diff_on: "k_times_differentiable_on (Suc k) f U"
            by (meson Suc_leI f_n_diff k_times_differentiable_on_def
                k_times_differentiable_at_mono k_lt_n)
          then have f_Suc_k_diff: "k_times_differentiable_at (Suc k) f y"
            using k_times_differentiable_on_def y_bound by blast

          have g_Suc_k_diff_on: "k_times_differentiable_on (Suc k) g U"
            by (meson Suc_leI g_n_diff k_times_differentiable_on_def
                k_times_differentiable_at_mono k_lt_n)
          then have g_Suc_k_diff: "k_times_differentiable_at (Suc k) g y"
            using k_times_differentiable_on_def y_bound by blast

          have continuity_at_y: "continuous (at y within U)
             (\<lambda>t. (deriv ^^ Suc k) f t + (deriv ^^ Suc k) g t)"
            using continuous_on y_bound by blast
          then have continuity_at_y': "\<forall>y \<in> U. continuous (at y)
            (\<lambda>t. (deriv ^^ Suc k) f t + (deriv ^^ Suc k) g t)"
            by (metis at_within_open local.continuous_on openU)

          have deriv_assoc: "\<forall>y \<in> U.
                (deriv ^^ Suc k) (\<lambda>y. f y + g y) y =
                (deriv ^^ Suc k) f y + (deriv ^^ Suc k) g y"
            by (metis f_Suc_k_diff_on g_Suc_k_diff_on
                k_times_differentiable_on_def kth_deriv_add)

          have "\<forall>y\<in>U. continuous (at y within U)
              (\<lambda>t. (deriv ^^ Suc k) (\<lambda>x. f x + g x) t)"
          proof clarify
            fix y
            assume y_in: "y \<in> U"

            have "continuous (at y within U)
                 (\<lambda>t. (deriv ^^ Suc k) f t + (deriv ^^ Suc k) g t)"
              using f_Suc_k_diff g_Suc_k_diff local.continuous_on y_in by blast

            with y_in deriv_assoc assms(1)
            show "continuous (at y within U)
                    ((deriv ^^ Suc k) (\<lambda>x. f x + g x))"
              by (metis (mono_tags, lifting) \<open>continuous_on U (\<lambda>x. (deriv ^^ Suc k) f x + (deriv ^^ Suc k) g x)\<close> continuous_on_cong
                  continuous_on_eq_continuous_within)

          qed
          then show "continuous (at y within U) ((deriv ^^ Suc k) (\<lambda>x. f x + g x))"
            using y_bound by blast
        qed
        then show "(deriv ^^ k) (\<lambda>x. f x + g x) differentiable_on U
          \<and> continuous_on U ((deriv ^^ Suc k) (\<lambda>x. f x + g x))"
          using Dsum continuous_on_eq_continuous_within by blast
      qed

      show "(deriv ^^ k) (\<lambda>x. f x + g x) differentiable_on U
        \<and> continuous_on U ((deriv ^^ Suc k) (\<lambda>x. f x + g x))"
        using Ck_less_n \<open>k < n\<close> by blast
    qed
    then show ?thesis
      by (simp add: C_k_on_def n_nonzero openU)
  qed
qed

lemma C_k_sub:
  assumes fCk: "C_k_on n f U"
      and gCk: "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y - g y) U"
proof -
  have g_neg: "C_k_on n (\<lambda>y. - g y) U"
    using gCk by (simp add: C_k_neg)

  have "C_k_on n (\<lambda>y. f y + (- g y)) U"
    by (rule C_k_add[OF fCk g_neg])

  thus ?thesis
    by (simp add: fun_eq_iff)
qed

lemma C_k_mult:
  assumes fCk   : "C_k_on n f U"
      and gCk   : "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y * g y) U"
proof -
  have openU: "open U"
    using C_k_on_def fCk by presburger

  show ?thesis
    using assms
  proof (cases n)
    case 0
    with fCk gCk have cont:
      "continuous_on U f"  "continuous_on U g"
      unfolding C_k_on_def by auto
    have "continuous_on U (\<lambda>y. f y + g y)"
      using cont by (simp add: continuous_on_add)
    with openU show "C_k_on n (\<lambda>y. f y * g y) U"
      by (simp add: "0" C0_on_def cont continuous_on_mult)
  next
    from fCk have f_diff:
      "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast

    from gCk have g_diff:
      "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast

    fix m :: nat
    assume f_Cn: "C_k_on n f U"
    then have f_n_diff: "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume g_Cn: "C_k_on n g U"
    then have g_n_diff: "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume n_nonzero: "n = Suc m"

    have prod_n_diff: "k_times_differentiable_on n (\<lambda>y. f(y)* g(y)) U"
      using f_n_diff g_n_diff k_times_differentiable_on_def kth_deriv_mult by auto

    with f_Cn have f_D_C: "(\<forall>k < n. ((deriv ^^ k) f) differentiable_on U
                         \<and> continuous_on U ((deriv ^^ Suc k) f))"
      unfolding C_k_on_def by auto

    with g_Cn have g_D_C: "(\<forall>k < n. ((deriv ^^ k) g) differentiable_on U
                         \<and> continuous_on U ((deriv ^^ Suc k) g))"
      unfolding C_k_on_def by auto

    with f_n_diff g_n_diff prod_n_diff
    have Ck_less_n:
      "\<forall>k<n.
         ((deriv ^^ k) (\<lambda>y. f y * g y)) differentiable_on U \<and>
         continuous_on U ((deriv ^^ Suc k) (\<lambda>y. f y * g y))"
    proof clarify
      fix k
      assume k_lt_n: "k < n"
      have prod_diff:
          "((deriv ^^ k) (\<lambda>x. f x * g x)) differentiable_on U"
        by (metis differentiable_at_imp_differentiable_on k_lt_n
            k_times_differentiable_on_def n_times_diff_imp_lower_deriv_diff prod_n_diff)

      have prod_cont:
      "continuous_on U ((deriv ^^ Suc k) (\<lambda>y. f y * g y))"
      proof -
        have cont_every:
          "\<forall>j\<le>Suc k. continuous_on U
             (\<lambda>y. of_nat (Suc k choose j) *
                  ((deriv ^^ j) f y *
                   (deriv ^^ (Suc k - j)) g y))"
        proof (clarify)
          fix j :: nat
          assume j_le: "j \<le> Suc k"
          have cont_inner: "continuous_on U (\<lambda>y. (deriv ^^ j) f y * (deriv ^^ (Suc k - j)) g y)"
            using f_D_C j_le k_lt_n g_D_C
            by(intro continuous_on_mult,
               metis differentiable_imp_continuous_on le_Suc_eq order.strict_trans1,
               metis Suc_diff_le Suc_le_eq diff_is_0_eq g_n_diff
               k_times_differentiable_on_imp_continuous_on less_imp_diff_less
               linorder_le_less_linear n_nonzero zero_le)
          have cont_const: "continuous_on U (\<lambda>y. of_nat (Suc k choose j))"
            by simp
          show "continuous_on U
                  (\<lambda>y. of_nat (Suc k choose j) *
                       ((deriv ^^ j) f y *
                        (deriv ^^ (Suc k - j)) g y))"
            using cont_const cont_inner
            by (simp add: continuous_on_mult mult.assoc)
        qed

        then have cont_sum:
          "continuous_on U
             (\<lambda>x. \<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                            (deriv ^^ j) f x *
                            (deriv ^^ (Suc k - j)) g x)"
          by(subst continuous_on_sum, simp_all, simp add: ab_semigroup_mult_class.mult_ac(1))

        have eq_on:
          "\<forall>x\<in>U.
             (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                        (deriv ^^ j) f x *
                        (deriv ^^ (Suc k - j)) g x)
           = (deriv ^^ Suc k) (\<lambda>y. f y * g y) x"
        proof clarify
          fix x :: real
          assume xU: "x \<in> U"
          have "k_times_differentiable_at (Suc k) f x"
               "k_times_differentiable_at (Suc k) g x"
            using f_n_diff g_n_diff xU
            unfolding k_times_differentiable_on_def
            using Suc_leI k_lt_n k_times_differentiable_at_mono by blast+
          with kth_deriv_mult[where k = "Suc k"]
          show "(\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                   (deriv ^^ j) f x *
                   (deriv ^^ (Suc k - j)) g x)
                = (deriv ^^ Suc k) (\<lambda>y. f y * g y) x"
            by simp
        qed

        from cont_sum eq_on
        show ?thesis
          using continuous_on_cong by fastforce
      qed
      show "(deriv ^^ k) (\<lambda>y. f y * g y) differentiable_on U \<and>
            continuous_on U ((deriv ^^ Suc k) (\<lambda>y. f y * g y))"
        using prod_diff prod_cont by blast
    qed
    then show ?thesis
      by (simp add: C_k_on_def n_nonzero openU)
  qed
qed

lemma C_1_inv:
  assumes fC1   : "C_k_on 1 f U"
      and nz    : "\<forall>y\<in>U. f y \<noteq> 0"
    shows   "C_k_on 1 (\<lambda>y. inverse (f y)) U"
proof -
  have openU: "open U"
    using C_k_on_def fC1 by presburger

  have derivative_exists: "\<forall>y\<in>U. \<exists>d .(f has_field_derivative d) (at y within U)"
    by (metis C1_cont_diff at_within_open fC1 openU)

  from fC1 obtain
     cont_f : "continuous_on U f"
   and diff_f : "\<forall>y\<in>U. (\<lambda>t. f t) differentiable (at y)"
    using C1_cont_diff DERIV_deriv_iff_real_differentiable
      differentiable_imp_continuous_on by blast

  have cont_inv: "continuous_on U (\<lambda>y. inverse (f y))"
    using Limits.continuous_on_inverse cont_f nz by blast

  have diff_inv:
    "\<forall>y\<in>U. (\<lambda>t. inverse (f t)) differentiable (at y)"
    using diff_f differentiable_inverse nz by blast

  have "C_k_on 1 (\<lambda>y. inverse (f y)) U"
  proof -
    have "(deriv ^^ 0) (\<lambda>y. inverse (f y)) differentiable_on U"
      using diff_inv differentiable_at_imp_differentiable_on by auto
    moreover have "continuous_on U ((deriv ^^ Suc 0) (\<lambda>y. inverse (f y)))"
    proof -
      have eq_on:
        "\<forall>y\<in>U. (deriv ^^ 1) (\<lambda>y. inverse (f y)) y =
                - deriv f y / (f y)^2"
      proof clarify
        fix y
        assume yU: "y \<in> U"
        then obtain d where d_def: "(f has_field_derivative d) (at y within U)"
          using derivative_exists by blast

        have "((\<lambda>x. inverse (f x)) has_field_derivative
          - (d * inverse (f y ^ Suc (Suc 0)))) (at y within U)"
          by(rule DERIV_inverse_fun, smt d_def, smt nz yU)
        then have "((\<lambda>t. inverse (f t)) has_field_derivative (- deriv f y / (f y)^2)) (at y)"
          by (metis DERIV_imp_deriv at_within_open d_def
              divide_minus_left divide_real_def numeral_2_eq_2 openU yU)
        thus "(deriv ^^ 1) (\<lambda>y. inverse (f y)) y =  - deriv f y / (f y)^2"
          by (simp add: DERIV_imp_deriv)
      qed

      have "continuous_on U (\<lambda>y. deriv f y)"
        using C1_cont_diff fC1 by blast
      then have cont_derf: "continuous_on U (\<lambda>y. - deriv f y)"
        using continuous_on_minus by blast
      have "(\<lambda>y. inverse (f y) * inverse (f y)) = (\<lambda>y. inverse ((f y)^2))"
        by (simp add: power2_eq_square)
      then have cont_rhs:
        "continuous_on U (\<lambda>y. - deriv f y * inverse ((f y)\<^sup>2))"
        by (metis (full_types) cont_derf cont_inv continuous_on_mult)
      then show "continuous_on U ((deriv ^^ Suc 0) (\<lambda>y. inverse (f y)))"
        using continuous_on_cong divide_real_def eq_on by fastforce
    qed
    ultimately show ?thesis
      by (simp add: C_k_on_def openU)
  qed
  thus ?thesis.
qed

lemma C_1_div:
  assumes fC1 : "C_k_on 1 f U"
      and gC1 : "C_k_on 1 g U"
      and nz   : "\<forall>y\<in>U. g y \<noteq> 0"
  shows   "C_k_on 1 (\<lambda>y. f y / g y) U"
proof -
  have inv_g_C1: "C_k_on 1 (\<lambda>y. inverse (g y)) U"
    by (rule C_1_inv[OF gC1 nz])

  have "C_k_on 1 (\<lambda>y. f y * inverse (g y)) U"
    by (rule C_k_mult[OF fC1 inv_g_C1])
  thus ?thesis
    by (simp add: field_simps)
qed

lemma C_k_sum_upto:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes FCk: "\<And>i. i \<le> N \<Longrightarrow> C_k_on k (F i) U"
  shows   "C_k_on k (\<lambda>x. \<Sum> i\<le>N. F i x) U"
proof (cases k)
  case 0
  then have cont_i: "\<And>i. i \<le> N \<Longrightarrow> continuous_on U (F i)"
    using FCk by (simp add: C_k_on_def)
  have "continuous_on U (\<lambda>x. \<Sum> i\<le>N. F i x)"
    by (subst continuous_on_sum) (use cont_i in auto)
  with 0 show ?thesis
    using C_k_on_def assms by auto
next
  case (Suc k')
  have openU: "open U"
    using FCk[of 0] by (cases k) (simp_all add: C_k_on_def)
  have F_kdiff_on: "\<And>i. i \<le> N \<Longrightarrow> k_times_differentiable_on (Suc k') (F i) U"
    using FCk Suc by (simp add: C_k_on_imp_k_times_differentiable_on)

  have sum_kdiff_on: "k_times_differentiable_on (Suc k') (\<lambda>x. \<Sum> i\<le>N. F i x) U"
  proof (rule k_times_differentiable_onI)
    fix x :: real
    assume xU: "x \<in> U"
    have each_at: "\<And>i. i \<le> N \<Longrightarrow> (F i) (Suc k')-times_differentiable_at x"
      using F_kdiff_on xU by (simp add: k_times_differentiable_on_def)
    then show "(\<lambda>y. \<Sum> i\<le>N. F i y) (Suc k')-times_differentiable_at x"
      by(rule kth_deriv_sum_uptoE, auto)
  qed

  have Dj:
    "\<And>j. j < Suc k' \<Longrightarrow> ((deriv ^^ j) (\<lambda>x. \<Sum> i\<le>N. F i x)) differentiable_on U"
  proof -
    fix j :: nat
    assume jlt: "j < Suc k'"
    from openU jlt sum_kdiff_on
    show "((deriv ^^ j) (\<lambda>x. \<Sum> i\<le>N. F i x)) differentiable_on U"
      by (metis at_within_open differentiable_on_def
                k_times_differentiable_onD n_times_diff_imp_lower_deriv_diff)
  qed

  have Cj:
    "\<And>j. j < Suc k' \<Longrightarrow> continuous_on U ((deriv ^^ Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x))"
  proof -
    fix j :: nat
    assume jlt: "j < Suc k'"
    have eq_on:
      "\<And>x. x \<in> U \<Longrightarrow>
          (deriv ^^ Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x) x
        = (\<Sum> i\<le>N. (deriv ^^ Suc j) (F i) x)"
    proof -
      fix x :: real
      assume xU: "x \<in> U"
      have each_at_j:
        "\<And>i. i \<le> N \<Longrightarrow> (F i) (Suc j)-times_differentiable_at x"
      proof -
        fix i assume "i \<le> N"
        from F_kdiff_on[OF \<open>i \<le> N\<close>] xU have
          "(F i) (Suc k')-times_differentiable_at x"
          by (simp add: k_times_differentiable_on_def)
        with jlt show "(F i) (Suc j)-times_differentiable_at x"
          by (meson Suc_leI k_times_differentiable_at_mono)
      qed

      then show "(deriv ^^ Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x) x
            = (\<Sum> i\<le>N. (deriv ^^ Suc j) (F i) x)"
        by(subst kth_deriv_sum_upto, simp_all)
    qed
    have cont_sum:
      "continuous_on U (\<lambda>x. \<Sum> i\<le>N. (deriv ^^ Suc j) (F i) x)"
    proof -
      have "\<And>i. i \<le> N \<Longrightarrow> continuous_on U ((deriv ^^ Suc j) (F i))"
        using FCk Suc jlt
        by (simp add: C_k_on_def)
      then show ?thesis
        by (subst continuous_on_sum) auto
    qed
    show "continuous_on U ((deriv ^^ Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x))"
      using cont_sum eq_on by auto
  qed

  have "C_k_on (Suc k') (\<lambda>x. \<Sum> i\<le>N. F i x) U"
    using openU Dj Cj Suc sum_kdiff_on
    by (simp add: C_k_on_def)
  then show ?thesis using Suc by simp
qed

text \<open>\<open>f\<close> is \<open>C\<^sup>k\<^sup>+\<^sup>1\<close> on \<open>U\<close> iff it is differentiable on \<open>U\<close> and \<open>deriv f\<close> is
  \<open>C\<^sup>k\<close> there.\<close>

lemma C_k_on_Suc_iff:
  "C_k_on (Suc k) f U \<longleftrightarrow> f differentiable_on U \<and> C_k_on k (deriv f) U"
proof
  assume "C_k_on (Suc k) f U"
  then have U: "open U"
    and row: "\<And>n. n < Suc k \<Longrightarrow>
      (deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ Suc n) f)"
    by (simp_all add: C_k_on_def)
  have "f differentiable_on U"
    using row[of 0] by simp
  moreover have "C_k_on k (deriv f) U"
  proof (cases "k = 0")
    case True
    then show ?thesis
      using U row[of 0] by (simp add: C_k_on_def)
  next
    case False
    have "(deriv ^^ n) (deriv f) differentiable_on U \<and>
        continuous_on U ((deriv ^^ Suc n) (deriv f))" if "n < k" for n
      using row[of "Suc n"] that by (simp only: kth_deriv_shift Suc_less_eq)
    then show ?thesis
      using U False by (simp add: C_k_on_def)
  qed
  ultimately show "f differentiable_on U \<and> C_k_on k (deriv f) U" ..
next
  assume H: "f differentiable_on U \<and> C_k_on k (deriv f) U"
  then have U: "open U"
    by (simp add: C_k_on_def split: if_splits)
  have cont: "continuous_on U (deriv f)"
  proof (cases "k = 0")
    case True
    then show ?thesis using H by (simp add: C_k_on_def)
  next
    case False
    then have "deriv f differentiable_on U"
      using H by (auto simp: C_k_on_def)
    then show ?thesis
      by (rule differentiable_imp_continuous_on)
  qed
  have "(deriv ^^ n) f differentiable_on U \<and> continuous_on U ((deriv ^^ Suc n) f)"
    if "n < Suc k" for n
  proof (cases n)
    case 0
    then show ?thesis using H cont by simp
  next
    case (Suc j)
    with that have "j < k" by simp
    then have "(deriv ^^ j) (deriv f) differentiable_on U \<and> continuous_on U ((deriv ^^ Suc j) (deriv f))"
      using H by (auto simp: C_k_on_def)
    then show ?thesis
      using Suc by (simp only: kth_deriv_shift)
  qed
  then show "C_k_on (Suc k) f U"
    using U by (simp add: C_k_on_def)
qed


section \<open>Taylor's Theorem with Peano Remainder\<close>

subsection \<open>Real Polynomial Functions: Closure under Differentiation\<close>

subsection \<open>Taylor Polynomials and Peano Remainders\<close>

text \<open>Taylor's theorem with Lagrange remainder (@{thm [source] MacLaurin.Taylor}), stated with
  \<^const>\<open>k_times_differentiable_at\<close>.\<close>

theorem Taylor_k_times_differentiable:
  "\<forall>t. a \<le> t \<longrightarrow> t \<le> b \<longrightarrow> f n-times_differentiable_at t
 \<Longrightarrow> \<lbrakk>0 < n; a \<le> c; c \<le> b; a \<le> x; x \<le> b; x \<noteq> c\<rbrakk>
 \<Longrightarrow> \<exists>\<xi>. (if x < c then x < \<xi> \<and> \<xi> < c else c < \<xi> \<and> \<xi> < x) \<and>
    f x = (\<Sum>m<n. ((deriv^^m) f) c / fact m * (x - c) ^ m)
                + ((deriv^^n) f) \<xi> / fact n * (x - c) ^ n"
  by (rule MacLaurin.Taylor[where a=a and b=b];
      simp; metis DERIV_deriv_iff_real_differentiable
      n_times_diff_imp_lower_deriv_diff)

corollary Taylor_as_limit:
  assumes npos: "0 < n"
      and cAB: "c \<in> {a..b}"
      and cont: "isCont ((deriv ^^ n) f) c"
      and diff: "\<And>t. t \<in> {a..b} \<Longrightarrow> f n-times_differentiable_at t"
  shows "((\<lambda>x.
           (f x - (\<Sum>m\<le>n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m))
           / (x - c) ^ n) \<longlongrightarrow> 0) (at c within {a..b})"
proof -
  define g where g_def: "g \<equiv> (deriv ^^ n) f"
  define S where S_def :"S x \<equiv> (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)" for x

  (* Lagrange form gives a point between c and x witnessing the remainder *)
  have ex_t:
    "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<noteq> c \<Longrightarrow>
          \<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
            \<and> f x = S x + g t / fact n * (x - c) ^ n"
  proof -
    fix x assume hx: "x \<in> {a..b}" "x \<noteq> c"
    with assms have "\<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
                     \<and> f x = (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
                              + (g t) / fact n * (x - c) ^ n"
      unfolding g_def S_def by (subst Taylor_k_times_differentiable, simp_all, auto)

    thus "\<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
              \<and> f x = S x + g t / fact n * (x - c) ^ n"
      using S_def by presburger
  qed

  (* Choose a concrete selector \<tau>(x) for the Taylor point *)
  then obtain \<tau> :: "real \<Rightarrow> real" where \<tau>_def:
    "\<And>x. x \<in> {a..b} \<and> x \<noteq> c \<Longrightarrow>
         (if x < c then x < \<tau> x \<and> \<tau> x < c else c < \<tau> x \<and> \<tau> x < x)
       \<and> f x = S x + g (\<tau> x) / fact n * (x - c) ^ n"
    by metis

  have evAB: "eventually (\<lambda>x. x \<in> {a..b} - {c}) (at c within {a..b})"
    by (auto simp: eventually_at_filter)

  (* On that event, the centered expression simplifies to a difference in g *)
   have ev_eq:
    "eventually (\<lambda>x. ( f x
                     - S x
                     - g c / fact n * (x - c) ^ n) / (x - c) ^ n
                  = (g (\<tau> x) - g c) / fact n)
                (at c within {a..b})"
  proof (rule eventually_mono[OF evAB])
    fix x :: real
    assume hx: "x \<in> {a..b} - {c}"
    hence xne: "x \<noteq> c" by auto
    have denom_ne: "(x - c) ^ n \<noteq> 0"
      using xne npos by simp

    have fx: "f x - S x = g (\<tau> x) / fact n * (x - c) ^ n"
      using \<tau>_def hx by (simp add: algebra_simps)

    have "( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n
          = (f x - S x) / (x - c) ^ n - g c / fact n"
      by (metis denom_ne divide_diff_eq_iff)
    also have "\<dots> = g (\<tau> x) / fact n - g c / fact n"
      using denom_ne fx by auto
    also have "\<dots> = (g (\<tau> x) - g c) / fact n"
      by (simp add: field_simps)
    finally show "( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n
                  = (g (\<tau> x) - g c) / fact n".
  qed

  (* |\<tau> x - c| \<le> |x - c| whenever \<tau> x lies strictly between x and c *)
  have ev_bound:
    "eventually (\<lambda>x. 0 \<le> \<bar>\<tau> x - c\<bar> \<and> \<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>) (at c within {a..b})"
    by (rule eventually_mono[OF evAB], auto,
        metis \<tau>_def abs_minus_commute abs_of_pos atLeastAtMost_iff
        diff_gt_0_iff_gt diff_mono linorder_not_le not_less_iff_gr_or_eq)
  (* Hence \<tau> x \<rightarrow> c as x \<rightarrow> c within {a..b} *)
  have tendsto_tau:
  "((\<lambda>x. \<tau> x) \<longlongrightarrow> c) (at c within {a..b})"
  proof -
    have tend_abs_tau:
  "((\<lambda>x. \<bar>\<tau> x - c\<bar>) \<longlongrightarrow> 0) (at c within {a..b})"
    proof -
      have ev_lower: "eventually (\<lambda>x. 0 \<le> \<bar>\<tau> x - c\<bar>) (at c within {a..b})"
        by simp

      have ev_upper:
        "eventually (\<lambda>x. \<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>) (at c within {a..b})"
      proof (rule eventually_mono[OF evAB])
        fix x assume hx: "x \<in> {a..b} - {c}"
        hence xin: "x \<in> {a..b}" and xne: "x \<noteq> c" by auto
        from \<tau>_def[of x] xin xne have between:
          "(if x < c then x < \<tau> x \<and> \<tau> x < c else c < \<tau> x \<and> \<tau> x < x)" by auto
        thus "\<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>"
          by (cases "x < c") (auto simp: abs_real_def)
      qed

      have L_lower: "((\<lambda>x. 0::real) \<longlongrightarrow> 0) (at c within {a..b})" by simp
      have L_upper: "((\<lambda>x. \<bar>x - c\<bar>) \<longlongrightarrow> 0) (at c within {a..b})"
        by (simp add: LIM_zero tendsto_rabs_zero)

      (* sandwich: 0 \<le> |\<tau> x - c| \<le> |x - c|, and |x - c| \<rightarrow> 0 *)
      show ?thesis
        by (rule tendsto_sandwich[OF ev_lower ev_upper L_lower L_upper])
    qed
      show ?thesis
        by (meson LIM_zero_iff tend_abs_tau tendsto_rabs_zero_cancel)
  qed

  (* Continuity of g at c gives g(\<tau> x) \<rightarrow> g c *)
  have tendsto_g_tau:
    "((\<lambda>x. g (\<tau> x)) \<longlongrightarrow> g c) (at c within {a..b})"
    using assms(3) continuous_within g_def tendsto_compose tendsto_tau by blast

  (* Thus (g(\<tau> x) - g c)/fact n \<rightarrow> 0 *)
  have rhs_to_0: "((\<lambda>x. (g (\<tau> x) - g c) / fact n) \<longlongrightarrow> 0) (at c within {a..b})"
    by (simp add: LIM_zero tendsto_divide_zero tendsto_g_tau)

  have "(((\<lambda>x. ( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n) \<longlongrightarrow> 0)(at c within {a..b}))
     =  (((\<lambda>x. (g (\<tau> x) - g c) / fact n) \<longlongrightarrow> 0) (at c within {a..b}))"
    by (rule tendsto_cong) (use ev_eq in auto)

  then have base_limit:
    "((\<lambda>x.
        ( f x
        - (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
        - ((deriv ^^ n) f) c / fact n * (x - c) ^ n )
       / (x - c) ^ n) \<longlongrightarrow> 0) (at c within {a..b})"
    using rhs_to_0 g_def S_def by simp

  have "\<And>x. (\<Sum>m\<le>n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
        = (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
          + ((deriv ^^ n) f) c / fact n * (x - c) ^ n"
    using lessThan_Suc_atMost sum.lessThan_Suc by auto

  then show ?thesis
    by (smt (verit, ccfv_SIG) Lim_cong_within base_limit)
qed

\<comment> \<open>The Taylor polynomial of degree \<open>n\<close> of \<open>f\<close> at \<open>c\<close>.\<close>

definition taylor_poly :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "taylor_poly n f c x \<equiv> (\<Sum> m \<le> n. ((deriv ^^ m) f c / fact m) * (x - c)^m)"

\<comment> \<open>The error of the degree-\<open>n\<close> Taylor polynomial.\<close>

definition peano_remainder ::
  "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "peano_remainder n f c x = f x - taylor_poly n f c x"

(*Keep the next lemma here: it is line 2190 of the new theory src/HOL/Analysis/Higher_Order_Derivatives.thy. It stays because its proof uses k_times_differentiable_at lemmas of this theory.*)
lemma kth_deriv_taylor_term:
  fixes x :: real
  shows "(deriv ^^ k) (\<lambda>t. c * (t - a) ^ i) x =
    (if k \<le> i then c * (of_nat (fact i) / of_nat (fact (i - k))) * (x - a) ^ (i - k) else 0)"
  by(subst kth_deriv_cmult,
      simp add: k_times_differentiable_at_pow,
      simp add: kth_deriv_shifted_pow)

subsection \<open>Derivatives of the Taylor Polynomial and Peano Remainder\<close>

\<comment> \<open>For \<open>k \<le> m\<close>, the \<open>k\<close>-th derivatives of \<open>f\<close> and of its Taylor polynomial of degree \<open>m\<close>
    agree at the centre.\<close>

lemma taylor_poly_diff_at:
  "(taylor_poly m f a) k-times_differentiable_at x"
  unfolding taylor_poly_def
  using k_times_differentiable_at_pow kth_deriv_cmult by (subst kth_deriv_sum_upto, blast, simp)

lemma k_diff_at_tay_term:
  "(\<lambda>t. (deriv ^^ i) f a / fact i * (t - a) ^ i) k-times_differentiable_at x"
  using k_times_differentiable_at_pow kth_deriv_cmult by blast

lemma kth_deriv_taylor_poly:
  assumes "k \<le> m"
  shows "(deriv ^^ k) (taylor_poly m f a) x =
       (\<Sum> i\<in>{k..m}. ((deriv ^^ i) f a / fact (i - k)) * (x - a) ^ (i - k))"
proof -
  have "(deriv ^^ k) (taylor_poly m f a) x =
          (\<Sum> i\<le>m. (deriv ^^ k)
                     (\<lambda>t. (deriv ^^ i) f a / fact i * (t - a) ^ i) x)"
    unfolding taylor_poly_def
    by (subst kth_deriv_sum_upto, subst k_diff_at_tay_term, auto)
  also have
    "\<dots> = (\<Sum> i\<le>m.
              (if k \<le> i
               then ((deriv ^^ i) f a / fact i) *
                     (of_nat (fact i) / of_nat (fact (i - k))) *
                     (x - a) ^ (i - k)
               else 0))"
    by (subst kth_deriv_taylor_term, simp)
  also have
    "\<dots> = (\<Sum> i\<le>m.
              ((deriv ^^ i) f a / fact i) *
              (if k \<le> i
               then of_nat (fact i) / of_nat (fact (i - k)) *
                    (x - a) ^ (i - k)
               else 0))"
    by (smt (verit, best) mult_eq_0_iff sum.cong vector_space_over_itself.scale_scale)
  also have
    "\<dots> = (\<Sum> i\<in>{k..m}.((deriv ^^ i) f a / fact (i - k)) * (x - a) ^ (i - k))"
    by (subst sum.mono_neutral_right[where S = "{k..m}"], auto)
  finally show ?thesis.
qed

lemma kth_deriv_peano_remainder_zero:
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows "(deriv ^^ k) (peano_remainder m f a) a = 0"
  unfolding peano_remainder_def
proof -
  have "(deriv ^^ k) (\<lambda>x. f x - taylor_poly m f a x) a =
        (deriv ^^ k) f a - (deriv ^^ k) (taylor_poly m f a) a"
    using assms k_times_differentiable_at_mono
    by(subst kth_deriv_sub, simp_all, simp add: taylor_poly_diff_at)
  also have "\<dots> = (deriv ^^ k) f a -
  (\<Sum> i\<in>{k..m}. ((deriv ^^ i) f a / fact (i - k)) * (a - a) ^ (i - k))"
    by (simp add: kth_deriv_taylor_poly assms(1))
  also have
    "\<dots> =  0"
   by (simp add: sum.atLeast_Suc_atMost power_0_left assms(1) split: if_splits)
  finally show "(deriv ^^ k) (\<lambda>x. f x - taylor_poly m f a x) a = 0".
qed

lemma peano_kth_deriv_zero_diff:
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows "(peano_remainder m f a) m-times_differentiable_at a \<and>
     ((deriv ^^ k) (peano_remainder m f a)) (m - k)-times_differentiable_at a"
  unfolding peano_remainder_def
  by (simp add: kth_deriv_commute_and_shiftE assms kth_deriv_subE taylor_poly_diff_at)


subsection \<open>Taylor's Theorem with Peano Remainder\<close>

lemma ex_remainder_choice:
  fixes f :: "real \<Rightarrow> real" and x0 y :: real and n :: nat
  defines "R \<equiv> peano_remainder (Suc n) f x0"
  defines "A j gj \<equiv> \<bar>(deriv ^^ j) R gj\<bar> / \<bar>(y - x0) ^ (Suc n - j)\<bar>"
  assumes "y \<noteq> x0" and y_small: "\<bar>y - x0\<bar> < \<epsilon>"
    and k_diff: "f (Suc n)-times_differentiable_at x0"
    and deriv1: "\<forall>z\<in>closed_segment x0 y. (R has_derivative (\<lambda>h. deriv R z * h)) (at z)"
    and derivi: "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon>
      \<longrightarrow> ((deriv ^^ i) R has_derivative (\<lambda>h. (deriv ^^ Suc i) R z * h)) (at z)"
  shows "\<exists>g. \<forall>j::nat. (g 0 = y)
    \<and> (j < n \<longrightarrow> (x0 < (y::real) \<longrightarrow> (x0 < g (Suc j) \<and> g (Suc j) < g j))
    \<and> (y < (x0::real) \<longrightarrow> (g j < g (Suc j) \<and> g (Suc j) < x0))
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
proof-
  have base_case: "\<exists>z. z \<in> open_segment y x0
    \<and> (0 < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < z \<and> z < y)
    \<and> (y < x0 \<longrightarrow> y < z \<and> z < x0)
    \<and> (A 0 y \<le> A (Suc 0) z))"
    (is "\<exists>z. ?conj1 z \<and> (0 < n \<longrightarrow> ?conj2 y z \<and> ?conj3 y z \<and> ?conj4 0 y z)")
  proof-
    have A0_eq: "A 0 y = \<bar>R y\<bar> / \<bar>(y - x0) ^ (Suc n)\<bar>"
      by (simp add: R_def A_def)
    have "R x0 = 0"
      using kth_deriv_peano_remainder_zero[OF _ k_diff, of 0]
      by (simp add: R_def )
    have "\<exists>z>x0. z < y \<and> R y = (y - x0) * deriv R z" if "x0 < y"
      using closed_segment_eq_real_ivl[of x0 y] \<open>x0 < y\<close>
        MVT2[OF \<open>x0 < y\<close>, of R "deriv R"] deriv1
      by (clarsimp simp: has_field_derivative_def \<open>R x0 = 0\<close>)
    moreover have "\<exists>z>y. z < x0 \<and> R y = (y - x0) * deriv R z" if "x0 > y"
      using closed_segment_eq_real_ivl[of x0 y] \<open>x0 > y\<close>
        MVT2[OF \<open>x0 > y\<close>, of R "deriv R"] deriv1
      apply(clarsimp simp: has_field_derivative_def \<open>R x0 = 0\<close>)
      by (metis add.inverse_inverse minus_diff_eq mult_minus_left)
    ultimately show "\<exists>z. ?conj1 z \<and> (0 < n \<longrightarrow> ?conj2 y z \<and> ?conj3 y z \<and> ?conj4 0 y z)"
      using A0_eq
      unfolding open_segment_eq_real_ivl
      by (cases \<open>x0 > y\<close>; clarsimp simp add: A_def)
         (metis abs_divide[of "deriv R _" "(y - x0) ^ n"]
                less_eq_real_def[of x0 y]
                abs_divide[of "(y - x0) * deriv R _" "(y - x0) * (y - x0) ^ n"]
                diff_ge_0_iff_ge[of y x0] dual_order.strict_trans[of _ x0 y]
                less_eq_real_def[of "\<bar>deriv R _ / (y - x0) ^ n\<bar>" "\<bar>deriv R _ / (y - x0) ^ n\<bar>"]
                less_eq_real_def[of "0" "0"] order_less_imp_not_less[of x0 y]
                nonzero_mult_divide_mult_cancel_left[of "y - x0" "deriv R _" "(y - x0) ^ n"],
          smt (verit) assms(3) divide_divide_eq_right mult.commute mult_minus_left
              nonzero_mult_div_cancel_left zero_le_mult_iff)
  qed
  have cond2: "\<exists>z. z \<in> open_segment y x0
    \<and> (j < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < z \<and> z < x)
    \<and> (y < x0 \<longrightarrow> x < z \<and> z < x0)
    \<and> (A j x \<le> A (Suc j) z))"
    if x_def: "if j = 0 then x = y else x \<in> open_segment y x0" for x j
    using x_def
  proof(induct j arbitrary: x)
    case 0
    thus ?case
      using base_case
      by simp
  next
    case (Suc j)
    let ?x = "if j = 0 then y else x"
    obtain z_null where "?conj1 z_null" and "j < n \<longrightarrow> ?conj2 ?x z_null"
      and "j < n \<longrightarrow> ?conj3 ?x z_null" and "j < n \<longrightarrow> ?conj4 j ?x z_null"
      using base_case Suc(1)[of ?x] Suc(2)
      by (cases "j = 0") auto
    have x_small: "\<bar>x - x0\<bar> < \<epsilon>"
      using Suc(2) y_small \<open>y \<noteq> x0\<close>
      by (cases "x0 > y")
        (auto simp: open_segment_eq_real_ivl)
    have x_rel_x0: "x0 > y \<Longrightarrow> x0 > x" "x0 < y \<Longrightarrow> x0 < x"
      using Suc(2)
      by (auto simp: open_segment_eq_real_ivl)
    hence abs_leq: "\<bar>(x - x0)\<bar> \<le> \<bar>(y - x0)\<bar>"
      using Suc(2) \<open>y \<noteq> x0\<close>
      by (cases "x0 > y")
        (auto simp: open_segment_eq_real_ivl)
    have eq0: "(deriv ^^ (Suc j)) R x0 = 0" if "Suc j < n"
      using kth_deriv_peano_remainder_zero[OF _ k_diff]
      by (metis R_def Suc_lessD linorder_not_less not_less_eq_eq that)
    have "\<exists>z>x0. z < x \<and> (deriv ^^ Suc j) R x - (deriv ^^ Suc j) R x0
      = (x - x0) * (deriv ^^ Suc (Suc j)) R z" if "x0 < y" and "Suc j < n"
      using x_small eq0[OF \<open>Suc j < n\<close>] Suc(2)
      by (intro MVT2[unfolded has_field_derivative_def, OF x_rel_x0(2)[OF \<open>x0 < y\<close>]]
          derivi[rule_format, OF \<open>Suc j < n\<close>]) clarsimp
    moreover have "\<exists>z>x. z < x0 \<and> (deriv ^^ Suc j) R x0 - (deriv ^^ Suc j) R x
      = (x0 - x) * (deriv ^^ Suc (Suc j)) R z" if "y < x0" and "Suc j < n"
      using x_small eq0[OF \<open>Suc j < n\<close>] Suc(2)
      by (intro MVT2[unfolded has_field_derivative_def, OF x_rel_x0(1)[OF \<open>y < x0\<close>]]
          derivi[rule_format, OF \<open>Suc j < n\<close>]) clarsimp
    ultimately obtain z where z_in: "z \<in> open_segment x0 x"
      and dSuc_eq: "Suc j < n \<Longrightarrow> (deriv ^^ Suc j) R x = (x - x0) * (deriv ^^ Suc (Suc j)) R z"
      using \<open>y \<noteq> x0\<close> x_rel_x0 eq0 Rats_dense_in_real
      by (cases "x0 < y"; clarsimp simp: open_segment_eq_real_ivl)
   (blast, metis (mono_tags) dense diff_zero minus_diff_eq mult_minus_left)
    have "A (Suc (Suc j)) w = \<bar>(deriv ^^ (Suc (Suc j))) R w\<bar> / \<bar>(y - x0) ^ (n - Suc j)\<bar>" for w
      by (simp add: R_def A_def)
    have ASuc_eq: "A (Suc j) x = \<bar>(deriv ^^ (Suc j)) R x\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>"
      by (simp add: R_def A_def)
    also have "\<dots> = \<bar>(x - x0) * (deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>"
      if "Suc j < n"
      using dSuc_eq[OF \<open>Suc j < n\<close>]
      by simp
    also have "\<dots> = \<bar>(x - x0)\<bar> * \<bar>(deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>"
      if "Suc j < n"
      by (simp add: abs_mult)
    also have  "\<dots> \<le> \<bar>(y - x0)\<bar> * \<bar>(deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>"
      if "Suc j < n"
      by (simp add: abs_leq divide_right_mono mult_right_mono)
    also have  "\<dots> \<le> \<bar>deriv (deriv ((deriv ^^ j) R)) z\<bar> / \<bar>(y - x0) ^ (n - Suc j)\<bar>"
      if "Suc j < n"
      using \<open>y \<noteq> x0\<close> \<open>Suc j < n\<close>
      by (cases "x0 < y"; clarsimp)
         (smt (verit, del_insts) Suc_diff_Suc Suc_lessD
              nonzero_mult_divide_mult_cancel_left power_Suc that,
          (simp add: abs_power_minus[symmetric, of "y - x0"]; simp add: power_eq_if))
    finally have "A (Suc j) x \<le> A (Suc (Suc j)) z" if "Suc j < n"
      using \<open>Suc j < n\<close>
      by (simp add: A_def)
    then show ?case
      using z_in x_rel_x0 \<open>y \<noteq> x0\<close> abs_leq
      by (cases "x0 < y"; clarsimp simp: open_segment_eq_real_ivl)
        force+
  qed
  have "\<exists>g. \<forall>j. (if j = 0 then g j = y else g j \<in> open_segment y x0)
    \<and> (j < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < g (Suc j) \<and> g (Suc j) < g j)
    \<and> (y < x0 \<longrightarrow> g j < g (Suc j) \<and> g (Suc j) < x0)
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
    using cond2 dependent_nat_choice[where
        P="\<lambda>m a. if m = 0 then a = y else a \<in> open_segment y x0"
        and Q="\<lambda>j gj gsucj.
          j < n \<longrightarrow> (x0 < y \<longrightarrow> (x0 < gsucj \<and> gsucj < gj))
          \<and> (y < x0 \<longrightarrow> (gj < gsucj \<and> gsucj < x0))
          \<and> (A j gj \<le> A (Suc j) gsucj)", simplified]
    by blast
  thus ?thesis
    by metis
qed

lemma ex_remainder_list:
  fixes f :: "real \<Rightarrow> real" and x0 y :: real and n :: nat
  defines "R \<equiv> peano_remainder (Suc n) f x0"
  defines "A j gj \<equiv> \<bar>(deriv ^^ j) R gj\<bar> / \<bar>(y - x0) ^ (Suc n - j)\<bar>"
  assumes "y \<noteq> x0" and y_small: "\<bar>y - x0\<bar> < \<epsilon>"
    and k_diff: "f (Suc n)-times_differentiable_at x0"
    and deriv1: "\<forall>z\<in>closed_segment x0 y. (R has_derivative (\<lambda>h. deriv R z * h)) (at z)"
    and derivi: "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon>
      \<longrightarrow> ((deriv ^^ i) R has_derivative (\<lambda>h. (deriv ^^ Suc i) R z * h)) (at z)"
  shows "\<exists>cs. length cs = n \<and>
         (\<forall>j<n. if x0 < y
            then if j = 0 then x0 < cs ! 0 \<and> cs ! 0 < y else cs ! j < cs ! (j - 1) \<and> x0 < cs ! j
            else if j = 0 then y < cs ! 0 \<and> cs ! 0 < x0 else cs ! (j - 1) < cs ! j \<and> cs ! j < x0)
         \<and> (\<forall>j<n. A j (if j = 0 then y else cs ! (j - 1))
     \<le> \<bar>(deriv ^^ (j + 1)) (peano_remainder (Suc n) f x0) (cs ! j)\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>)"
proof-
  obtain g where g_props: "\<forall>j::nat. (g 0 = y)
    \<and> (j < n \<longrightarrow> (x0 < (y::real) \<longrightarrow> (x0 < g (Suc j) \<and> g (Suc j) < g j))
    \<and> (y < (x0::real) \<longrightarrow> (g j < g (Suc j) \<and> g (Suc j) < x0))
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
    using ex_remainder_choice[OF assms(3-7)[unfolded R_def]]
    unfolding R_def A_def
    by blast
  then obtain cs where len_cs: "length cs = n"
    and list_assignment: "\<forall>j<n. cs ! j = g (j + 1)"
    by (atomize_elim)
      (auto intro!: exI[where x="map (\<lambda>x. g (Suc x)) [0 ..< n]"])

  from g_props[rule_format] \<open>y \<noteq> x0\<close>
  show ?thesis (is "\<exists>x. ?P x")
    by (intro exI[of _ cs]; cases "y < x0")
       (smt (verit, ccfv_SIG)
            A_def R_def Suc_diff_1 Suc_le_lessD list_assignment len_cs
            add.commute bot_nat_0.not_eq_extremum diff_Suc_1
            diff_Suc_eq_diff_pred linorder_not_le not_less_iff_gr_or_eq
            plus_1_eq_Suc)+
qed

theorem Taylor_Peano_remainder:
  assumes "f (Suc n)-times_differentiable_at x0"
  shows   "((\<lambda>x. peano_remainder (n+1) f x0 x / (x-x0) ^ (n+1)) \<longlongrightarrow> 0) (at x0)"
proof(cases "n=0")
  assume "n = 0"
  show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0"
  proof -
    have "k_times_differentiable_at 1 (peano_remainder 1 f x0) x0"
      by(subst peano_kth_deriv_zero_diff[where k = 1], simp, (smt One_nat_def \<open>n = 0\<close> assms)+)
    then obtain Peano_f' where
      r_has_deriv :
        "(peano_remainder 1 f x0 has_real_derivative Peano_f') (at x0)"
      using one_time_differentiable_at_iff by blast
    then have Peanof'_zero : "Peano_f' = 0"
      by (metis kth_deriv_peano_remainder_zero DERIV_imp_deriv One_nat_def \<open>n = 0\<close>
          assms first_derivative_alt_def le_numeral_extra(4))
    have limit_Peano_Remainder :
      "((\<lambda>x. (peano_remainder 1 f x0 x - peano_remainder 1 f x0 x0)
                 / (x - x0)) \<longlongrightarrow> Peano_f') (at x0)"
      using r_has_deriv by (simp add: has_field_derivativeD)
    then have "peano_remainder 1 f x0 x0 = 0"
      by (metis kth_deriv_simps(1) kth_deriv_peano_remainder_zero
          One_nat_def Suc_leD \<open>n = 0\<close> assms le_numeral_extra(4))
    then show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0"
      using Peanof'_zero \<open>n = 0\<close> limit_Peano_Remainder by force
  qed
next
  assume n_nonzero: "n \<noteq> 0"
  let "?if_prop1 x y j cs" = "if x < y
    then (if j = 0 then x < cs!0 \<and> cs!0 < y else cs!j < cs!(j-1) \<and> cs!j > x)
    else (if j = 0 then y < cs!0 \<and> cs!0 < x else cs!(j-1) <  cs!j \<and> cs!j < x)"
    and "?quotient1 j y cs" =
      "\<bar>(deriv ^^ j) (\<lambda>x. peano_remainder (Suc n) f x0 x) (if j = 0 then y else cs!(j-1))\<bar>
         / \<bar>(y - x0) ^ ((Suc n) - j)\<bar>"
    and "?quotient2 j y cs" =
      "\<bar>(deriv ^^ (j+1)) (\<lambda>x. peano_remainder (Suc n) f x0 x) (cs!j)\<bar>
         / \<bar>(y - x0) ^ (n - j)\<bar>"
  have list_exists: "\<exists>\<delta>>0. \<forall>y. y \<noteq> x0 \<longrightarrow> \<bar>y - x0\<bar> < \<delta>
    \<longrightarrow> (\<exists>cs :: real list.
      length cs = n
      \<and> (\<forall>j<n. ?if_prop1 x0 y j cs)
      \<and> (\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs))"
  proof -
    obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0"
      and diff_ball:
        "\<And>z. \<bar>z - x0\<bar> < \<epsilon> \<Longrightarrow>
             k_times_differentiable_at n (\<lambda>x. peano_remainder (Suc n) f x0 x) z"
      by (metis assms dual_order.refl k_times_differentiable_at.simps(2) peano_kth_deriv_zero_diff)

    then have field_deriv_ball: "\<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow>
         ((\<lambda>x. peano_remainder (Suc n) f x0 x)
          has_derivative (\<lambda>h. deriv (\<lambda>x. peano_remainder (Suc n) f x0 x) z * h)) (at z)"
      unfolding k_times_differentiable_at.simps
      by (metis DERIV_imp_deriv has_field_derivative_imp_has_derivative
          one_time_differentiable_at_iff k_times_differentiable_at_mono
          less_one linorder_not_less n_nonzero)
    then have field_deriv_ball_generalized:
      "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow>
    ((deriv ^^ i) (\<lambda>x. peano_remainder (Suc n) f x0 x)
      has_derivative (\<lambda>h. (deriv ^^ Suc i) (\<lambda>x. peano_remainder (Suc n) f x0 x) z * h)) (at z)"
      using diff_ball k_times_differentiable_ball_has_derivative_chain by blast

    show ?thesis
    proof (intro exI[of _ \<epsilon>] conjI \<epsilon>_pos, clarify)
      fix x
      assume x_ne: "x \<noteq> x0"
      assume x_small: "\<bar>x - x0\<bar> < \<epsilon>"

      have dir: "x0 < x \<or> x < x0" using x_ne by arith
      have vanishes: "peano_remainder (Suc n) f x0 x0 = 0"
        by (metis kth_deriv_simps(1) add_0_left
            kth_deriv_peano_remainder_zero assms le_add1)
      show "\<exists>cs. length cs = n
        \<and> (\<forall>j<n. ?if_prop1 x0 x j cs)
        \<and> (\<forall>j<n. ?quotient1 j x cs \<le> ?quotient2 j x cs)"
        using x_small field_deriv_ball[rule_format] field_deriv_ball_generalized
        by (subst ex_remainder_list[OF x_ne x_small assms],
            auto simp: closed_segment_eq_real_ivl)
    qed
  qed
  then obtain \<delta> :: real where \<delta>_pos: "\<delta> > 0" and \<delta>_prop: "\<forall>y. y \<noteq> x0 \<longrightarrow> \<bar>y - x0\<bar> < \<delta>
    \<longrightarrow> (\<exists>cs. length cs = n
        \<and> (\<forall>j<n. ?if_prop1 x0 y j cs)
        \<and> (\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs))"
    by blast
  let "?remainder1 m y" = "(deriv ^^ m) (peano_remainder (Suc n) f x0) y"
  and "?remainder2 m y" = "(deriv ^^ m) (peano_remainder (Suc n) f x0) y"
  have final_term_limit: "(\<lambda>x. (?remainder1 n x - ?remainder1 n x0) / (x - x0)) \<midarrow>x0\<rightarrow> 0"
  proof -
    have "k_times_differentiable_at (Suc n) (peano_remainder (Suc n) f x0) x0"
      by (meson assms le_add2 le_add_same_cancel2 peano_kth_deriv_zero_diff)
    then have "(\<lambda>r. (?remainder2 n r - ?remainder2 n x0) / (r - x0)) \<midarrow>x0 \<rightarrow> ?remainder2 (Suc n) x0"
      using has_field_derivativeD k_times_differentiable_at_SucE by blast
    then have "(\<lambda>r. (?remainder2 n r - ?remainder1 n x0) / (r - x0)) \<midarrow>x0 \<rightarrow> ?remainder1 (Suc n) x0"
      by simp
    then show ?thesis
      by (metis (no_types, lifting) kth_deriv_peano_remainder_zero assms dual_order.refl)
  qed
  show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0"
  proof(rule filterlim_split_at_real)
    show "((\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<longlongrightarrow> 0) (at_left x0)"
    proof(subst tendsto_at_left_x_epsilon_def, clarify)
      fix \<epsilon> :: real
      assume \<epsilon>_pos: "0 < \<epsilon>"
      show "\<exists>\<delta>>0. \<forall>y. y < x0 \<and> x0 - y < \<delta>
      \<longrightarrow> \<bar>peano_remainder (n+1) f x0 y / (y - x0) ^ (n+1) - 0\<bar> < \<epsilon>"
      proof -
        have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x -
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by(rule tendsto_rabs_zero, smt final_term_limit)
        then have "((\<lambda>x. \<bar>(deriv ^^ n) (peano_remainder (Suc n) f x0) x -
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_left x0)"
          by (meson LIM_cong Lim_at_imp_Lim_at_within abs_divide)
        with  \<epsilon>_pos
        obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
                   and \<delta>1_prop: "\<forall>y. y < x0 \<and> x0 - y < \<delta>1 \<longrightarrow>
                        \<bar>(deriv ^^ n) (peano_remainder (Suc n) f x0) y
                        - (deriv ^^ n) (peano_remainder (Suc n) f x0) x0\<bar>
                       /\<bar>y - x0\<bar> < \<epsilon>"
          using tendsto_at_left_x_epsilon_def by auto

        define \<delta>2 where "\<delta>2 = min \<delta> \<delta>1"
        have \<delta>2_pos: "\<delta>2 > 0"
          by (simp add: \<delta>1_pos \<delta>2_def \<delta>_pos)

        have "\<forall>y. y < x0 \<and> x0 - y < \<delta>2 \<longrightarrow>\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
        proof clarify
          fix y :: real
          assume y_cond: "y < x0" "x0 - y < \<delta>2"
          have y_within_bounds: "y \<noteq> x0 \<and> \<bar>y - x0\<bar> < \<delta>"
            using \<delta>2_def y_cond by fastforce
          then obtain cs
            where cs_len: "length cs = n"
            and cs_order: "(\<forall>j<n. ?if_prop1 x0 y j cs)"
            and cs_ineq:  "\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs"
            using \<delta>_prop by blast
          let "?if_term m" = "if m = 0 then y else cs ! (m - 1)"

          have stepwise_chain:
          "\<forall>k \<le> n. \<bar>(\<lambda>t. peano_remainder (Suc n) f x0 t) y\<bar> / \<bar>y - x0\<bar> ^ (Suc n)
                 \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k-1))\<bar>
                  / \<bar>y - x0\<bar> ^ (Suc n - k)"
          proof (intro allI, clarify)
            fix k :: nat
            assume k_bound: "k \<le> n"
            show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
              \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
              using k_bound
            proof (induction k rule: nat_induct)
              show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 0 (?if_term 0)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - 0)"
                by simp
            next
              fix m :: nat
              assume IH: "(m \<le> n \<Longrightarrow> \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
              \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m))"
              assume m_bound: "Suc m \<le> n"
              then have IH_antecedent: "m \<le> n"
                by simp
              with IH have IH_consequent: "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)"
                by simp
              have "\<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (n -  m)"
              proof -
                have "\<And>m. \<not> m < n \<or> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>(y - x0) ^ (Suc n - m)\<bar>
                  \<le> \<bar>?remainder1 (Suc m) (cs ! m)\<bar> / \<bar>(y - x0) ^ (n - m)\<bar>"
                  using Suc_eq_plus1 cs_ineq by presburger
                then show ?thesis
                  by (simp add: Suc_le_lessD m_bound power_abs)
              qed
              then show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - Suc m)"
                by (smt (verit, ccfv_threshold) IH_consequent diff_Suc_Suc)
            qed
          qed
          have cs_tail_bound: "cs ! (n - 1) < x0"
            by (metis cs_order diff_Suc_1 gr0_conv_Suc lessI n_nonzero
                not_less_iff_gr_or_eq y_cond(1) zero_less_iff_neq_zero)

          have "\<forall> j < n. \<bar>(cs ! j) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
          proof (intro allI impI)
            fix j :: nat
            assume j_bound: "j < n"
            show "abs (cs ! j - x0) \<le> abs (x0 - y)"
              using j_bound
            proof (induction j rule: nat_induct)
              case 0
              show ?case
                using cs_order n_nonzero y_cond(1) by auto
            next
              case (Suc m)
              then show ?case
                using cs_order y_cond(1) by auto
            qed
          qed
          then have final_element_bound: "\<bar>cs ! (n - 1) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
            using n_nonzero by auto
          show "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
          proof -
            have "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar>
              = \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n"
              by (simp, metis power_Suc power_abs)
            also have "\<dots> \<le> \<bar>?remainder1 n (?if_term n)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - n)"
              using stepwise_chain[rule_format, of n] by simp
            also have "\<dots> \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>y - x0\<bar>"
              by (simp add: n_nonzero)
            also have "\<dots> \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>(cs ! (n-1)) - x0\<bar>"
              by (smt (verit, best) final_element_bound cs_tail_bound frac_le)
            also have "\<dots> = \<bar>?remainder1 n (cs ! (n-1)) - ?remainder1 n x0\<bar> / \<bar>(cs!(n-1)) - x0\<bar>"
              using kth_deriv_peano_remainder_zero assms by auto
            also have "\<dots> < \<epsilon>"
              using \<delta>1_prop \<delta>2_def cs_tail_bound final_element_bound y_cond by auto
            finally show ?thesis.
          qed
        qed
        then show ?thesis
          using \<delta>2_pos by auto
      qed
    qed
  next
    show "((\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<longlongrightarrow> 0) (at_right x0)"
    proof(subst tendsto_at_right_x_epsilon_def, clarify)
      fix \<epsilon> :: real
      assume \<epsilon>_pos: "0 < \<epsilon>"
      show "\<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta>
      \<longrightarrow> \<bar>peano_remainder (n+1) f x0 y / (y - x0) ^ (n+1) - 0\<bar> < \<epsilon>"
      proof -
        have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x -
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by(rule tendsto_rabs_zero, smt final_term_limit)
        then have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x0 -
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by (smt (verit, best) LIM_cong minus_divide_left)
        hence right_limit:
          "((\<lambda>x. \<bar>?remainder1 n x0 - ?remainder1 n x\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_right x0)"
          by (meson LIM_cong Lim_at_imp_Lim_at_within abs_divide)
        have "((\<lambda>x. \<bar>?remainder1 n x0 - ?remainder1 n x\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_right x0)
          = (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta>
            \<longrightarrow> \<bar>\<bar>?remainder1 n x0 - ?remainder1 n y\<bar> / \<bar>y - x0\<bar> - 0\<bar> < \<epsilon>)"
          by(rule tendsto_at_right_x_epsilon_def)
        with right_limit have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta>
          \<longrightarrow> \<bar>\<bar>?remainder1 n x0 - ?remainder1 n y\<bar> / \<bar>y - x0\<bar> - 0\<bar> < \<epsilon>)"
          by simp

        with \<epsilon>_pos
        obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0" and
          \<delta>1_prop: "\<forall>y. x0 < y \<and> y - x0 < \<delta>1 \<longrightarrow> \<bar>?remainder1 n x0 - ?remainder1 n y\<bar> /\<bar>y - x0\<bar> < \<epsilon>"
          by force

        define \<delta>2 where "\<delta>2 = min \<delta> \<delta>1"
        have \<delta>2_pos: "\<delta>2 > 0"
          by (simp add: \<delta>1_pos \<delta>2_def \<delta>_pos)

        have "\<forall>y. x0 < y \<and> y - x0 < \<delta>2 \<longrightarrow> \<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
        proof clarify
          fix y :: real
          assume y_cond: " x0 < y" " y - x0 < \<delta>2"
          have y_within_bounds: "y \<noteq> x0 \<and> \<bar>y - x0\<bar> < \<delta>"
            using \<delta>2_def y_cond by fastforce
          then obtain cs
            where cs_len: "length cs = n"
            and cs_order: "(\<forall>j<n. ?if_prop1 x0 y j cs)"
            and cs_ineq:  "\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs"
            using \<delta>_prop by blast
          let "?if_term m" = "if m = 0 then y else cs ! (m - 1)"

          have stepwise_chain:
          "\<forall>k \<le> n. \<bar>(\<lambda>t. peano_remainder (Suc n) f x0 t)  y\<bar> / \<bar>y - x0\<bar> ^ (Suc n)
                 \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k-1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
          proof (intro allI, clarify)
            fix k :: nat
            assume k_bound: "k \<le> n"
            show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
              \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
              using k_bound
            proof (induction k rule: nat_induct)
              show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 0 (if 0 = 0 then y else cs ! (0 - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - 0)"
                by simp
            next
              fix m :: nat
              assume IH: "(m \<le> n \<Longrightarrow> \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 m (if m = 0 then y else cs ! (m - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m))"
              assume m_bound: "Suc m \<le> n"
              then have IH_antecedent: "m \<le> n"
                by simp
              with IH have IH_consequent: "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)"
                by simp
              have "\<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (n -  m)"
              proof -
                have "\<And>m. \<not> m < n \<or> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>(y - x0) ^ (Suc n - m)\<bar>
                  \<le> \<bar>?remainder1 (Suc m) (cs ! m)\<bar> / \<bar>(y - x0) ^ (n - m)\<bar>"
                  using Suc_eq_plus1 cs_ineq by presburger
                then show ?thesis
                  by (simp add: Suc_le_lessD m_bound power_abs)
              qed
              then show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - Suc m)"
                by (smt (verit, ccfv_threshold) IH_consequent diff_Suc_Suc)
            qed
          qed
          have cs_tail_bound: "cs ! (n - 1) > x0"
            by (metis cs_order diff_Suc_1 gr0_conv_Suc lessI
                n_nonzero y_cond(1) zero_less_iff_neq_zero)

          have "\<forall> j < n. \<bar>(cs ! j) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
          proof (intro allI impI)
            fix j :: nat
            assume j_bound: "j < n"
            show "abs (cs ! j - x0) \<le> abs (x0 - y)"
              using j_bound
            proof (induction j rule: nat_induct)
              case 0
              show ?case
                using cs_order n_nonzero y_cond(1) by auto
            next
              case (Suc m)
              then show ?case
                using cs_order y_cond(1) by auto
            qed
          qed
          then have final_element_bound: "\<bar>cs ! (n - 1) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
            using n_nonzero by auto
          show "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
          proof -
            have "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar>
              = \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n"
              by (simp, metis power_Suc power_abs)
            also have "\<dots> \<le> \<bar>?remainder1 n (?if_term n)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - n)"
              using stepwise_chain[rule_format, of n] by simp
            also have "\<dots> \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>y - x0\<bar>"
              by (simp add: n_nonzero)
            also have "\<dots> \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>(cs ! (n-1)) - x0\<bar>"
              by (smt (verit, best) final_element_bound cs_tail_bound frac_le)
            also have "\<dots> = \<bar>?remainder1 n (cs ! (n-1)) - ?remainder1 n x0\<bar> / \<bar>(cs ! (n-1)) - x0\<bar>"
              using kth_deriv_peano_remainder_zero assms by auto
            also have "\<dots> <  \<epsilon>"
              by (smt (verit, del_insts) \<delta>1_prop \<delta>2_def cs_tail_bound final_element_bound y_cond)
            finally show ?thesis.
          qed
        qed
        then show ?thesis
          using \<delta>2_pos by auto
      qed
    qed
  qed
qed

corollary Taylor_Peano:
  assumes "f (Suc n)-times_differentiable_at a"
  obtains h :: "real \<Rightarrow> real"
  where  "((\<lambda>x. h x) \<longlongrightarrow> 0) (at a)"
     and "f x = (\<Sum>i\<le>(n+1). (deriv ^^ i) f a/fact i * (x-a) ^ i) + h x * (x-a)^(n+1)"
proof
  define h where h_def:
    "h x = (if x=a then 0 else peano_remainder (n+1) f a x / (x - a) ^ (n+1))" for x

  have lim0: "((\<lambda>x. peano_remainder (n+1) f a x / (x - a) ^ (n+1)) \<longlongrightarrow> 0) (at a)"
    using Taylor_Peano_remainder[OF assms].

  have ev_ne: "eventually (\<lambda>x. x \<noteq> a) (at a)"
    by (simp add: eventually_at_filter)

  have eq_ev: "eventually (\<lambda>x. h x = peano_remainder (Suc n) f a x / (x - a) ^ Suc n) (at a)"
    by (simp add: h_def)
    show tend0: "((\<lambda>x. h x) \<longlongrightarrow> 0) (at a)"
      using eq_ev filterlim_cong lim0 by fastforce


      have exp_ne:"\<And>x. x \<noteq> a \<Longrightarrow>
      f x = (\<Sum>i\<le>Suc n. (deriv ^^ i) f a / fact i * (x - a) ^ i) + h x * (x - a) ^ Suc n"
    using h_def peano_remainder_def taylor_poly_def by force

  have exp_a: "f a = (\<Sum>i\<le>Suc n. (deriv ^^ i) f a / fact i * (a - a) ^ i) + h a * (a-a) ^ Suc n"
    by (simp add: h_def)

  show "f x = (\<Sum>i\<le>n + 1. (deriv ^^ i) f a / fact i * (x - a) ^ i) +
    (if x = a then 0 else peano_remainder (n + 1) f a x / (x - a) ^ (n + 1)) * (x - a) ^ (n + 1)"
    using Suc_eq_plus1 h_def exp_a exp_ne
    by presburger
qed

end

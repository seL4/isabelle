(*
  File:      HOL/Analysis/Infinite_Product.thy
  Author:    Manuel Eberl

  Basic results about convergence and absolute convergence of infinite products
  and their connection to summability.
*)
section \<open>Infinite Products\<close>
theory Infinite_Products
  imports Complex_Main
begin

lemma sum_le_prod:
  fixes f :: "'a \<Rightarrow> 'b :: linordered_semidom"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows   "sum f A \<le> (\<Prod>x\<in>A. 1 + f x)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  from insert.hyps have "sum f A + f x * (\<Prod>x\<in>A. 1) \<le> (\<Prod>x\<in>A. 1 + f x) + f x * (\<Prod>x\<in>A. 1 + f x)"
    by (intro add_mono insert mult_left_mono prod_mono) (auto intro: insert.prems)
  with insert.hyps show ?case by (simp add: algebra_simps)
qed simp_all

lemma prod_le_exp_sum:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows   "prod (\<lambda>x. 1 + f x) A \<le> exp (sum f A)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  have "(1 + f x) * (\<Prod>x\<in>A. 1 + f x) \<le> exp (f x) * exp (sum f A)"
    using insert.prems by (intro mult_mono insert prod_nonneg exp_ge_add_one_self) auto
  with insert.hyps show ?case by (simp add: algebra_simps exp_add)
qed simp_all

lemma lim_ln_1_plus_x_over_x_at_0: "(\<lambda>x::real. ln (1 + x) / x) \<midarrow>0\<rightarrow> 1"
proof (rule lhopital)
  show "(\<lambda>x::real. ln (1 + x)) \<midarrow>0\<rightarrow> 0"
    by (rule tendsto_eq_intros refl | simp)+
  have "eventually (\<lambda>x::real. x \<in> {-1/2<..<1/2}) (nhds 0)"
    by (rule eventually_nhds_in_open) auto
  hence *: "eventually (\<lambda>x::real. x \<in> {-1/2<..<1/2}) (at 0)"
    by (rule filter_leD [rotated]) (simp_all add: at_within_def)   
  show "eventually (\<lambda>x::real. ((\<lambda>x. ln (1 + x)) has_field_derivative inverse (1 + x)) (at x)) (at 0)"
    using * by eventually_elim (auto intro!: derivative_eq_intros simp: field_simps)
  show "eventually (\<lambda>x::real. ((\<lambda>x. x) has_field_derivative 1) (at x)) (at 0)"
    using * by eventually_elim (auto intro!: derivative_eq_intros simp: field_simps)
  show "\<forall>\<^sub>F x in at 0. x \<noteq> 0" by (auto simp: at_within_def eventually_inf_principal)
  show "(\<lambda>x::real. inverse (1 + x) / 1) \<midarrow>0\<rightarrow> 1"
    by (rule tendsto_eq_intros refl | simp)+
qed auto

definition convergent_prod :: "(nat \<Rightarrow> 'a :: {t2_space,comm_semiring_1}) \<Rightarrow> bool" where
  "convergent_prod f \<longleftrightarrow> (\<exists>M L. (\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L \<and> L \<noteq> 0)"

lemma convergent_prod_altdef:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space,comm_semiring_1}"
  shows "convergent_prod f \<longleftrightarrow> (\<exists>M L. (\<forall>n\<ge>M. f n \<noteq> 0) \<and> (\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L \<and> L \<noteq> 0)"
proof
  assume "convergent_prod f"
  then obtain M L where *: "(\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L" "L \<noteq> 0"
    by (auto simp: convergent_prod_def)
  have "f i \<noteq> 0" if "i \<ge> M" for i
  proof
    assume "f i = 0"
    have **: "eventually (\<lambda>n. (\<Prod>i\<le>n. f (i+M)) = 0) sequentially"
      using eventually_ge_at_top[of "i - M"]
    proof eventually_elim
      case (elim n)
      with \<open>f i = 0\<close> and \<open>i \<ge> M\<close> show ?case
        by (auto intro!: bexI[of _ "i - M"] prod_zero)
    qed
    have "(\<lambda>n. (\<Prod>i\<le>n. f (i+M))) \<longlonglongrightarrow> 0"
      unfolding filterlim_iff
      by (auto dest!: eventually_nhds_x_imp_x intro!: eventually_mono[OF **])
    from tendsto_unique[OF _ this *(1)] and *(2)
      show False by simp
  qed
  with * show "(\<exists>M L. (\<forall>n\<ge>M. f n \<noteq> 0) \<and> (\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L \<and> L \<noteq> 0)" 
    by blast
qed (auto simp: convergent_prod_def)

definition abs_convergent_prod :: "(nat \<Rightarrow> _) \<Rightarrow> bool" where
  "abs_convergent_prod f \<longleftrightarrow> convergent_prod (\<lambda>i. 1 + norm (f i - 1))"

lemma abs_convergent_prodI:
  assumes "convergent (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
  shows   "abs_convergent_prod f"
proof -
  from assms obtain L where L: "(\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1)) \<longlonglongrightarrow> L"
    by (auto simp: convergent_def)
  have "L \<ge> 1"
  proof (rule tendsto_le)
    show "eventually (\<lambda>n. (\<Prod>i\<le>n. 1 + norm (f i - 1)) \<ge> 1) sequentially"
    proof (intro always_eventually allI)
      fix n
      have "(\<Prod>i\<le>n. 1 + norm (f i - 1)) \<ge> (\<Prod>i\<le>n. 1)"
        by (intro prod_mono) auto
      thus "(\<Prod>i\<le>n. 1 + norm (f i - 1)) \<ge> 1" by simp
    qed
  qed (use L in simp_all)
  hence "L \<noteq> 0" by auto
  with L show ?thesis unfolding abs_convergent_prod_def convergent_prod_def
    by (intro exI[of _ "0::nat"] exI[of _ L]) auto
qed

lemma
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra,idom}"
  assumes "convergent_prod f"
  shows   convergent_prod_imp_convergent: "convergent (\<lambda>n. \<Prod>i\<le>n. f i)"
    and   convergent_prod_to_zero_iff:    "(\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> 0 \<longleftrightarrow> (\<exists>i. f i = 0)"
proof -
  from assms obtain M L 
    where M: "\<And>n. n \<ge> M \<Longrightarrow> f n \<noteq> 0" and "(\<lambda>n. \<Prod>i\<le>n. f (i + M)) \<longlonglongrightarrow> L" and "L \<noteq> 0"
    by (auto simp: convergent_prod_altdef)
  note this(2)
  also have "(\<lambda>n. \<Prod>i\<le>n. f (i + M)) = (\<lambda>n. \<Prod>i=M..M+n. f i)"
    by (intro ext prod.reindex_bij_witness[of _ "\<lambda>n. n - M" "\<lambda>n. n + M"]) auto
  finally have "(\<lambda>n. (\<Prod>i<M. f i) * (\<Prod>i=M..M+n. f i)) \<longlonglongrightarrow> (\<Prod>i<M. f i) * L"
    by (intro tendsto_mult tendsto_const)
  also have "(\<lambda>n. (\<Prod>i<M. f i) * (\<Prod>i=M..M+n. f i)) = (\<lambda>n. (\<Prod>i\<in>{..<M}\<union>{M..M+n}. f i))"
    by (subst prod.union_disjoint) auto
  also have "(\<lambda>n. {..<M} \<union> {M..M+n}) = (\<lambda>n. {..n+M})" by auto
  finally have lim: "(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> prod f {..<M} * L" 
    by (rule LIMSEQ_offset)
  thus "convergent (\<lambda>n. \<Prod>i\<le>n. f i)"
    by (auto simp: convergent_def)

  show "(\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> 0 \<longleftrightarrow> (\<exists>i. f i = 0)"
  proof
    assume "\<exists>i. f i = 0"
    then obtain i where "f i = 0" by auto
    moreover with M have "i < M" by (cases "i < M") auto
    ultimately have "(\<Prod>i<M. f i) = 0" by auto
    with lim show "(\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> 0" by simp
  next
    assume "(\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> 0"
    from tendsto_unique[OF _ this lim] and \<open>L \<noteq> 0\<close>
    show "\<exists>i. f i = 0" by auto
  qed
qed

lemma abs_convergent_prod_altdef:
  "abs_convergent_prod f \<longleftrightarrow> convergent (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
proof
  assume "abs_convergent_prod f"
  thus "convergent (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
    by (auto simp: abs_convergent_prod_def intro!: convergent_prod_imp_convergent)
qed (auto intro: abs_convergent_prodI)

lemma weierstrass_prod_ineq:
  fixes f :: "'a \<Rightarrow> real" 
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> {0..1}"
  shows   "1 - sum f A \<le> (\<Prod>x\<in>A. 1 - f x)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  from insert.hyps and insert.prems 
    have "1 - sum f A + f x * (\<Prod>x\<in>A. 1 - f x) \<le> (\<Prod>x\<in>A. 1 - f x) + f x * (\<Prod>x\<in>A. 1)"
    by (intro insert.IH add_mono mult_left_mono prod_mono) auto
  with insert.hyps show ?case by (simp add: algebra_simps)
qed simp_all

lemma norm_prod_minus1_le_prod_minus1:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra,comm_ring_1}"  
  shows "norm (prod (\<lambda>n. 1 + f n) A - 1) \<le> prod (\<lambda>n. 1 + norm (f n)) A - 1"
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  from insert.hyps have 
    "norm ((\<Prod>n\<in>insert x A. 1 + f n) - 1) = 
       norm ((\<Prod>n\<in>A. 1 + f n) - 1 + f x * (\<Prod>n\<in>A. 1 + f n))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> norm ((\<Prod>n\<in>A. 1 + f n) - 1) + norm (f x * (\<Prod>n\<in>A. 1 + f n))"
    by (rule norm_triangle_ineq)
  also have "norm (f x * (\<Prod>n\<in>A. 1 + f n)) = norm (f x) * (\<Prod>x\<in>A. norm (1 + f x))"
    by (simp add: prod_norm norm_mult)
  also have "(\<Prod>x\<in>A. norm (1 + f x)) \<le> (\<Prod>x\<in>A. norm (1::'a) + norm (f x))"
    by (intro prod_mono norm_triangle_ineq ballI conjI) auto
  also have "norm (1::'a) = 1" by simp
  also note insert.IH
  also have "(\<Prod>n\<in>A. 1 + norm (f n)) - 1 + norm (f x) * (\<Prod>x\<in>A. 1 + norm (f x)) =
               (\<Prod>n\<in>insert x A. 1 + norm (f n)) - 1"
    using insert.hyps by (simp add: algebra_simps)
  finally show ?case by - (simp_all add: mult_left_mono)
qed simp_all

lemma convergent_prod_imp_ev_nonzero:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space,comm_semiring_1}"
  assumes "convergent_prod f"
  shows   "eventually (\<lambda>n. f n \<noteq> 0) sequentially"
  using assms by (auto simp: eventually_at_top_linorder convergent_prod_altdef)

lemma convergent_prod_imp_LIMSEQ:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field}"
  assumes "convergent_prod f"
  shows   "f \<longlonglongrightarrow> 1"
proof -
  from assms obtain M L where L: "(\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L" "\<And>n. n \<ge> M \<Longrightarrow> f n \<noteq> 0" "L \<noteq> 0"
    by (auto simp: convergent_prod_altdef)
  hence L': "(\<lambda>n. \<Prod>i\<le>Suc n. f (i+M)) \<longlonglongrightarrow> L" by (subst filterlim_sequentially_Suc)
  have "(\<lambda>n. (\<Prod>i\<le>Suc n. f (i+M)) / (\<Prod>i\<le>n. f (i+M))) \<longlonglongrightarrow> L / L"
    using L L' by (intro tendsto_divide) simp_all
  also from L have "L / L = 1" by simp
  also have "(\<lambda>n. (\<Prod>i\<le>Suc n. f (i+M)) / (\<Prod>i\<le>n. f (i+M))) = (\<lambda>n. f (n + Suc M))"
    using assms L by (auto simp: fun_eq_iff atMost_Suc)
  finally show ?thesis by (rule LIMSEQ_offset)
qed

lemma abs_convergent_prod_imp_summable:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_div_algebra"
  assumes "abs_convergent_prod f"
  shows "summable (\<lambda>i. norm (f i - 1))"
proof -
  from assms have "convergent (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))" 
    unfolding abs_convergent_prod_def by (rule convergent_prod_imp_convergent)
  then obtain L where L: "(\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1)) \<longlonglongrightarrow> L"
    unfolding convergent_def by blast
  have "convergent (\<lambda>n. \<Sum>i\<le>n. norm (f i - 1))"
  proof (rule Bseq_monoseq_convergent)
    have "eventually (\<lambda>n. (\<Prod>i\<le>n. 1 + norm (f i - 1)) < L + 1) sequentially"
      using L(1) by (rule order_tendstoD) simp_all
    hence "\<forall>\<^sub>F x in sequentially. norm (\<Sum>i\<le>x. norm (f i - 1)) \<le> L + 1"
    proof eventually_elim
      case (elim n)
      have "norm (\<Sum>i\<le>n. norm (f i - 1)) = (\<Sum>i\<le>n. norm (f i - 1))"
        unfolding real_norm_def by (intro abs_of_nonneg sum_nonneg) simp_all
      also have "\<dots> \<le> (\<Prod>i\<le>n. 1 + norm (f i - 1))" by (rule sum_le_prod) auto
      also have "\<dots> < L + 1" by (rule elim)
      finally show ?case by simp
    qed
    thus "Bseq (\<lambda>n. \<Sum>i\<le>n. norm (f i - 1))" by (rule BfunI)
  next
    show "monoseq (\<lambda>n. \<Sum>i\<le>n. norm (f i - 1))"
      by (rule mono_SucI1) auto
  qed
  thus "summable (\<lambda>i. norm (f i - 1))" by (simp add: summable_iff_convergent')
qed

lemma summable_imp_abs_convergent_prod:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_div_algebra"
  assumes "summable (\<lambda>i. norm (f i - 1))"
  shows   "abs_convergent_prod f"
proof (intro abs_convergent_prodI Bseq_monoseq_convergent)
  show "monoseq (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
    by (intro mono_SucI1) 
       (auto simp: atMost_Suc algebra_simps intro!: mult_nonneg_nonneg prod_nonneg)
next
  show "Bseq (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
  proof (rule Bseq_eventually_mono)
    show "eventually (\<lambda>n. norm (\<Prod>i\<le>n. 1 + norm (f i - 1)) \<le> 
            norm (exp (\<Sum>i\<le>n. norm (f i - 1)))) sequentially"
      by (intro always_eventually allI) (auto simp: abs_prod exp_sum intro!: prod_mono)
  next
    from assms have "(\<lambda>n. \<Sum>i\<le>n. norm (f i - 1)) \<longlonglongrightarrow> (\<Sum>i. norm (f i - 1))"
      using sums_def_le by blast
    hence "(\<lambda>n. exp (\<Sum>i\<le>n. norm (f i - 1))) \<longlonglongrightarrow> exp (\<Sum>i. norm (f i - 1))"
      by (rule tendsto_exp)
    hence "convergent (\<lambda>n. exp (\<Sum>i\<le>n. norm (f i - 1)))"
      by (rule convergentI)
    thus "Bseq (\<lambda>n. exp (\<Sum>i\<le>n. norm (f i - 1)))"
      by (rule convergent_imp_Bseq)
  qed
qed

lemma abs_convergent_prod_conv_summable:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_div_algebra"
  shows "abs_convergent_prod f \<longleftrightarrow> summable (\<lambda>i. norm (f i - 1))"
  by (blast intro: abs_convergent_prod_imp_summable summable_imp_abs_convergent_prod)

lemma abs_convergent_prod_imp_LIMSEQ:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1,real_normed_div_algebra}"
  assumes "abs_convergent_prod f"
  shows   "f \<longlonglongrightarrow> 1"
proof -
  from assms have "summable (\<lambda>n. norm (f n - 1))"
    by (rule abs_convergent_prod_imp_summable)
  from summable_LIMSEQ_zero[OF this] have "(\<lambda>n. f n - 1) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_norm_zero_iff)
  from tendsto_add[OF this tendsto_const[of 1]] show ?thesis by simp
qed

lemma abs_convergent_prod_imp_ev_nonzero:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1,real_normed_div_algebra}"
  assumes "abs_convergent_prod f"
  shows   "eventually (\<lambda>n. f n \<noteq> 0) sequentially"
proof -
  from assms have "f \<longlonglongrightarrow> 1" 
    by (rule abs_convergent_prod_imp_LIMSEQ)
  hence "eventually (\<lambda>n. dist (f n) 1 < 1) at_top"
    by (auto simp: tendsto_iff)
  thus ?thesis by eventually_elim auto
qed

lemma convergent_prod_offset:
  assumes "convergent_prod (\<lambda>n. f (n + m))"  
  shows   "convergent_prod f"
proof -
  from assms obtain M L where "(\<lambda>n. \<Prod>k\<le>n. f (k + (M + m))) \<longlonglongrightarrow> L" "L \<noteq> 0"
    by (auto simp: convergent_prod_def add.assoc)
  thus "convergent_prod f" unfolding convergent_prod_def by blast
qed

lemma abs_convergent_prod_offset:
  assumes "abs_convergent_prod (\<lambda>n. f (n + m))"  
  shows   "abs_convergent_prod f"
  using assms unfolding abs_convergent_prod_def by (rule convergent_prod_offset)

lemma convergent_prod_ignore_initial_segment:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field}"
  assumes "convergent_prod f"
  shows   "convergent_prod (\<lambda>n. f (n + m))"
proof -
  from assms obtain M L 
    where L: "(\<lambda>n. \<Prod>k\<le>n. f (k + M)) \<longlonglongrightarrow> L" "L \<noteq> 0" and nz: "\<And>n. n \<ge> M \<Longrightarrow> f n \<noteq> 0"
    by (auto simp: convergent_prod_altdef)
  define C where "C = (\<Prod>k<m. f (k + M))"
  from nz have [simp]: "C \<noteq> 0" 
    by (auto simp: C_def)

  from L(1) have "(\<lambda>n. \<Prod>k\<le>n+m. f (k + M)) \<longlonglongrightarrow> L" 
    by (rule LIMSEQ_ignore_initial_segment)
  also have "(\<lambda>n. \<Prod>k\<le>n+m. f (k + M)) = (\<lambda>n. C * (\<Prod>k\<le>n. f (k + M + m)))"
  proof (rule ext, goal_cases)
    case (1 n)
    have "{..n+m} = {..<m} \<union> {m..n+m}" by auto
    also have "(\<Prod>k\<in>\<dots>. f (k + M)) = C * (\<Prod>k=m..n+m. f (k + M))"
      unfolding C_def by (rule prod.union_disjoint) auto
    also have "(\<Prod>k=m..n+m. f (k + M)) = (\<Prod>k\<le>n. f (k + m + M))"
      by (intro ext prod.reindex_bij_witness[of _ "\<lambda>k. k + m" "\<lambda>k. k - m"]) auto
    finally show ?case by (simp add: add_ac)
  qed
  finally have "(\<lambda>n. C * (\<Prod>k\<le>n. f (k + M + m)) / C) \<longlonglongrightarrow> L / C"
    by (intro tendsto_divide tendsto_const) auto
  hence "(\<lambda>n. \<Prod>k\<le>n. f (k + M + m)) \<longlonglongrightarrow> L / C" by simp
  moreover from \<open>L \<noteq> 0\<close> have "L / C \<noteq> 0" by simp
  ultimately show ?thesis unfolding convergent_prod_def by blast
qed

lemma abs_convergent_prod_ignore_initial_segment:
  assumes "abs_convergent_prod f"
  shows   "abs_convergent_prod (\<lambda>n. f (n + m))"
  using assms unfolding abs_convergent_prod_def 
  by (rule convergent_prod_ignore_initial_segment)

lemma summable_LIMSEQ': 
  assumes "summable (f::nat\<Rightarrow>'a::{t2_space,comm_monoid_add})"
  shows   "(\<lambda>n. \<Sum>i\<le>n. f i) \<longlonglongrightarrow> suminf f"
  using assms sums_def_le by blast

lemma abs_convergent_prod_imp_convergent_prod:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra,complete_space,comm_ring_1}"
  assumes "abs_convergent_prod f"
  shows   "convergent_prod f"
proof -
  from assms have "eventually (\<lambda>n. f n \<noteq> 0) sequentially"
    by (rule abs_convergent_prod_imp_ev_nonzero)
  then obtain N where N: "f n \<noteq> 0" if "n \<ge> N" for n 
    by (auto simp: eventually_at_top_linorder)
  let ?P = "\<lambda>n. \<Prod>i\<le>n. f (i + N)" and ?Q = "\<lambda>n. \<Prod>i\<le>n. 1 + norm (f (i + N) - 1)"

  have "Cauchy ?P"
  proof (rule CauchyI', goal_cases)
    case (1 \<epsilon>)
    from assms have "abs_convergent_prod (\<lambda>n. f (n + N))"
      by (rule abs_convergent_prod_ignore_initial_segment)
    hence "Cauchy ?Q"
      unfolding abs_convergent_prod_def
      by (intro convergent_Cauchy convergent_prod_imp_convergent)
    from CauchyD[OF this 1] obtain M where M: "norm (?Q m - ?Q n) < \<epsilon>" if "m \<ge> M" "n \<ge> M" for m n
      by blast
    show ?case
    proof (rule exI[of _ M], safe, goal_cases)
      case (1 m n)
      have "dist (?P m) (?P n) = norm (?P n - ?P m)"
        by (simp add: dist_norm norm_minus_commute)
      also from 1 have "{..n} = {..m} \<union> {m<..n}" by auto
      hence "norm (?P n - ?P m) = norm (?P m * (\<Prod>k\<in>{m<..n}. f (k + N)) - ?P m)"
        by (subst prod.union_disjoint [symmetric]) (auto simp: algebra_simps)
      also have "\<dots> = norm (?P m * ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1))"
        by (simp add: algebra_simps)
      also have "\<dots> = (\<Prod>k\<le>m. norm (f (k + N))) * norm ((\<Prod>k\<in>{m<..n}. f (k + N)) - 1)"
        by (simp add: norm_mult prod_norm)
      also have "\<dots> \<le> ?Q m * ((\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - 1)"
        using norm_prod_minus1_le_prod_minus1[of "\<lambda>k. f (k + N) - 1" "{m<..n}"]
              norm_triangle_ineq[of 1 "f k - 1" for k]
        by (intro mult_mono prod_mono ballI conjI norm_prod_minus1_le_prod_minus1 prod_nonneg) auto
      also have "\<dots> = ?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) - ?Q m"
        by (simp add: algebra_simps)
      also have "?Q m * (\<Prod>k\<in>{m<..n}. 1 + norm (f (k + N) - 1)) = 
                   (\<Prod>k\<in>{..m}\<union>{m<..n}. 1 + norm (f (k + N) - 1))"
        by (rule prod.union_disjoint [symmetric]) auto
      also from 1 have "{..m}\<union>{m<..n} = {..n}" by auto
      also have "?Q n - ?Q m \<le> norm (?Q n - ?Q m)" by simp
      also from 1 have "\<dots> < \<epsilon>" by (intro M) auto
      finally show ?case .
    qed
  qed
  hence conv: "convergent ?P" by (rule Cauchy_convergent)
  then obtain L where L: "?P \<longlonglongrightarrow> L"
    by (auto simp: convergent_def)

  have "L \<noteq> 0"
  proof
    assume [simp]: "L = 0"
    from tendsto_norm[OF L] have limit: "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + N))) \<longlonglongrightarrow> 0" 
      by (simp add: prod_norm)

    from assms have "(\<lambda>n. f (n + N)) \<longlonglongrightarrow> 1"
      by (intro abs_convergent_prod_imp_LIMSEQ abs_convergent_prod_ignore_initial_segment)
    hence "eventually (\<lambda>n. norm (f (n + N) - 1) < 1) sequentially"
      by (auto simp: tendsto_iff dist_norm)
    then obtain M0 where M0: "norm (f (n + N) - 1) < 1" if "n \<ge> M0" for n
      by (auto simp: eventually_at_top_linorder)

    {
      fix M assume M: "M \<ge> M0"
      with M0 have M: "norm (f (n + N) - 1) < 1" if "n \<ge> M" for n using that by simp

      have "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0"
      proof (rule tendsto_sandwich)
        show "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<ge> 0) sequentially"
          using M by (intro always_eventually prod_nonneg allI ballI) (auto intro: less_imp_le)
        have "norm (1::'a) - norm (f (i + M + N) - 1) \<le> norm (f (i + M + N))" for i
          using norm_triangle_ineq3[of "f (i + M + N)" 1] by simp
        thus "eventually (\<lambda>n. (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<le> (\<Prod>k\<le>n. norm (f (k+M+N)))) at_top"
          using M by (intro always_eventually allI prod_mono ballI conjI) (auto intro: less_imp_le)
        
        define C where "C = (\<Prod>k<M. norm (f (k + N)))"
        from N have [simp]: "C \<noteq> 0" by (auto simp: C_def)
        from L have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) \<longlonglongrightarrow> 0"
          by (intro LIMSEQ_ignore_initial_segment) (simp add: tendsto_norm_zero_iff)
        also have "(\<lambda>n. norm (\<Prod>k\<le>n+M. f (k + N))) = (\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))))"
        proof (rule ext, goal_cases)
          case (1 n)
          have "{..n+M} = {..<M} \<union> {M..n+M}" by auto
          also have "norm (\<Prod>k\<in>\<dots>. f (k + N)) = C * norm (\<Prod>k=M..n+M. f (k + N))"
            unfolding C_def by (subst prod.union_disjoint) (auto simp: norm_mult prod_norm)
          also have "(\<Prod>k=M..n+M. f (k + N)) = (\<Prod>k\<le>n. f (k + N + M))"
            by (intro prod.reindex_bij_witness[of _ "\<lambda>i. i + M" "\<lambda>i. i - M"]) auto
          finally show ?case by (simp add: add_ac prod_norm)
        qed
        finally have "(\<lambda>n. C * (\<Prod>k\<le>n. norm (f (k + M + N))) / C) \<longlonglongrightarrow> 0 / C"
          by (intro tendsto_divide tendsto_const) auto
        thus "(\<lambda>n. \<Prod>k\<le>n. norm (f (k + M + N))) \<longlonglongrightarrow> 0" by simp
      qed simp_all

      have "1 - (\<Sum>i. norm (f (i + M + N) - 1)) \<le> 0"
      proof (rule tendsto_le)
        show "eventually (\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k+M+N) - 1)) \<le> 
                                (\<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1))) at_top"
          using M by (intro always_eventually allI weierstrass_prod_ineq) (auto intro: less_imp_le)
        show "(\<lambda>n. \<Prod>k\<le>n. 1 - norm (f (k+M+N) - 1)) \<longlonglongrightarrow> 0" by fact
        show "(\<lambda>n. 1 - (\<Sum>k\<le>n. norm (f (k + M + N) - 1)))
                  \<longlonglongrightarrow> 1 - (\<Sum>i. norm (f (i + M + N) - 1))"
          by (intro tendsto_intros summable_LIMSEQ' summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      qed simp_all
      hence "(\<Sum>i. norm (f (i + M + N) - 1)) \<ge> 1" by simp
      also have "\<dots> + (\<Sum>i<M. norm (f (i + N) - 1)) = (\<Sum>i. norm (f (i + N) - 1))"
        by (intro suminf_split_initial_segment [symmetric] summable_ignore_initial_segment
              abs_convergent_prod_imp_summable assms)
      finally have "1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))" by simp
    } note * = this

    have "1 + (\<Sum>i. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))"
    proof (rule tendsto_le)
      show "(\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1))) \<longlonglongrightarrow> 1 + (\<Sum>i. norm (f (i + N) - 1))"
        by (intro tendsto_intros summable_LIMSEQ summable_ignore_initial_segment 
                abs_convergent_prod_imp_summable assms)
      show "eventually (\<lambda>M. 1 + (\<Sum>i<M. norm (f (i + N) - 1)) \<le> (\<Sum>i. norm (f (i + N) - 1))) at_top"
        using eventually_ge_at_top[of M0] by eventually_elim (use * in auto)
    qed simp_all
    thus False by simp
  qed
  with L show ?thesis by (auto simp: convergent_prod_def)
qed

end

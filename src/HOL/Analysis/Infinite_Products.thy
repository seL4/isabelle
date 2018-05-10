(*File:      HOL/Analysis/Infinite_Product.thy
  Author:    Manuel Eberl & LC Paulson

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

definition gen_has_prod :: "[nat \<Rightarrow> 'a::{t2_space, comm_semiring_1}, nat, 'a] \<Rightarrow> bool" 
  where "gen_has_prod f M p \<equiv> (\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> p \<and> p \<noteq> 0"

text\<open>The nonzero and zero cases, as in \emph{Complex Analysis} by Joseph Bak and Donald J.Newman, page 241\<close>
definition has_prod :: "(nat \<Rightarrow> 'a::{t2_space, comm_semiring_1}) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "has'_prod" 80)
  where "f has_prod p \<equiv> gen_has_prod f 0 p \<or> (\<exists>i q. p = 0 \<and> f i = 0 \<and> gen_has_prod f (Suc i) q)"

definition convergent_prod :: "(nat \<Rightarrow> 'a :: {t2_space,comm_semiring_1}) \<Rightarrow> bool" where
  "convergent_prod f \<equiv> \<exists>M p. gen_has_prod f M p"

definition prodinf :: "(nat \<Rightarrow> 'a::{t2_space, comm_semiring_1}) \<Rightarrow> 'a"
    (binder "\<Prod>" 10)
  where "prodinf f = (THE p. f has_prod p)"

lemmas prod_defs = gen_has_prod_def has_prod_def convergent_prod_def prodinf_def

lemma has_prod_subst[trans]: "f = g \<Longrightarrow> g has_prod z \<Longrightarrow> f has_prod z"
  by simp

lemma has_prod_cong: "(\<And>n. f n = g n) \<Longrightarrow> f has_prod c \<longleftrightarrow> g has_prod c"
  by presburger

lemma gen_has_prod_nonzero [simp]: "\<not> gen_has_prod f M 0"
  by (simp add: gen_has_prod_def)

lemma gen_has_prod_eq_0:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  assumes p: "gen_has_prod f m p" and i: "f i = 0" "i \<ge> m"
  shows "p = 0"
proof -
  have eq0: "(\<Prod>k\<le>n. f (k+m)) = 0" if "i - m \<le> n" for n
    by (metis i that atMost_atLeast0 atMost_iff diff_add finite_atLeastAtMost prod_zero_iff)
  have "(\<lambda>n. \<Prod>i\<le>n. f (i + m)) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_offset [where k = "i-m"]) (simp add: eq0)
    with p show ?thesis
      unfolding gen_has_prod_def
    using LIMSEQ_unique by blast
qed

lemma has_prod_0_iff: "f has_prod 0 \<longleftrightarrow> (\<exists>i. f i = 0 \<and> (\<exists>p. gen_has_prod f (Suc i) p))"
  by (simp add: has_prod_def)
      
lemma has_prod_unique2: 
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  assumes "f has_prod a" "f has_prod b" shows "a = b"
  using assms
  by (auto simp: has_prod_def gen_has_prod_eq_0) (meson gen_has_prod_def sequentially_bot tendsto_unique)

lemma has_prod_unique:
  fixes f :: "nat \<Rightarrow> 'a :: {idom,t2_space}"
  shows "f has_prod s \<Longrightarrow> s = prodinf f"
  by (simp add: has_prod_unique2 prodinf_def the_equality)

lemma convergent_prod_altdef:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space,comm_semiring_1}"
  shows "convergent_prod f \<longleftrightarrow> (\<exists>M L. (\<forall>n\<ge>M. f n \<noteq> 0) \<and> (\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L \<and> L \<noteq> 0)"
proof
  assume "convergent_prod f"
  then obtain M L where *: "(\<lambda>n. \<Prod>i\<le>n. f (i+M)) \<longlonglongrightarrow> L" "L \<noteq> 0"
    by (auto simp: prod_defs)
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
qed (auto simp: prod_defs)

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
  with L show ?thesis unfolding abs_convergent_prod_def prod_defs
    by (intro exI[of _ "0::nat"] exI[of _ L]) auto
qed

lemma
  fixes f :: "nat \<Rightarrow> 'a :: {topological_semigroup_mult,t2_space,idom}"
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

lemma convergent_prod_iff_nz_lim:
  fixes f :: "nat \<Rightarrow> 'a :: {topological_semigroup_mult,t2_space,idom}"
  assumes "\<And>i. f i \<noteq> 0"
  shows "convergent_prod f \<longleftrightarrow> (\<exists>L. (\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> L \<and> L \<noteq> 0)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    using assms convergentD convergent_prod_imp_convergent convergent_prod_to_zero_iff by blast
next
  assume ?rhs then show ?lhs
    unfolding prod_defs
    by (rule_tac x=0 in exI) auto
qed

lemma convergent_prod_iff_convergent: 
  fixes f :: "nat \<Rightarrow> 'a :: {topological_semigroup_mult,t2_space,idom}"
  assumes "\<And>i. f i \<noteq> 0"
  shows "convergent_prod f \<longleftrightarrow> convergent (\<lambda>n. \<Prod>i\<le>n. f i) \<and> lim (\<lambda>n. \<Prod>i\<le>n. f i) \<noteq> 0"
  by (force simp: convergent_prod_iff_nz_lim assms convergent_def limI)


lemma abs_convergent_prod_altdef:
  fixes f :: "nat \<Rightarrow> 'a :: {one,real_normed_vector}"
  shows  "abs_convergent_prod f \<longleftrightarrow> convergent (\<lambda>n. \<Prod>i\<le>n. 1 + norm (f i - 1))"
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
    by (auto simp: prod_defs add.assoc)
  thus "convergent_prod f" 
    unfolding prod_defs by blast
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
  ultimately show ?thesis 
    unfolding prod_defs by blast
qed

corollary convergent_prod_ignore_nonzero_segment:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes f: "convergent_prod f" and nz: "\<And>i. i \<ge> M \<Longrightarrow> f i \<noteq> 0"
  shows "\<exists>p. gen_has_prod f M p"
  using convergent_prod_ignore_initial_segment [OF f]
  by (metis convergent_LIMSEQ_iff convergent_prod_iff_convergent le_add_same_cancel2 nz prod_defs(1) zero_order(1))

corollary abs_convergent_prod_ignore_initial_segment:
  assumes "abs_convergent_prod f"
  shows   "abs_convergent_prod (\<lambda>n. f (n + m))"
  using assms unfolding abs_convergent_prod_def 
  by (rule convergent_prod_ignore_initial_segment)

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
  with L show ?thesis by (auto simp: prod_defs)
qed

lemma gen_has_prod_cases:
  fixes f :: "nat \<Rightarrow> 'a :: {idom,topological_semigroup_mult,t2_space}"
  assumes "gen_has_prod f M p"
  obtains i where "i<M" "f i = 0" | p where "gen_has_prod f 0 p"
proof -
  have "(\<lambda>n. \<Prod>i\<le>n. f (i + M)) \<longlonglongrightarrow> p" "p \<noteq> 0"
    using assms unfolding gen_has_prod_def by blast+
  then have "(\<lambda>n. prod f {..<M} * (\<Prod>i\<le>n. f (i + M))) \<longlonglongrightarrow> prod f {..<M} * p"
    by (metis tendsto_mult_left)
  moreover have "prod f {..<M} * (\<Prod>i\<le>n. f (i + M)) = prod f {..n+M}" for n
  proof -
    have "{..n+M} = {..<M} \<union> {M..n+M}"
      by auto
    then have "prod f {..n+M} = prod f {..<M} * prod f {M..n+M}"
      by simp (subst prod.union_disjoint; force)
    also have "\<dots> = prod f {..<M} * (\<Prod>i\<le>n. f (i + M))"
      by (metis (mono_tags, lifting) add.left_neutral atMost_atLeast0 prod_shift_bounds_cl_nat_ivl)
    finally show ?thesis by metis
  qed
  ultimately have "(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> prod f {..<M} * p"
    by (auto intro: LIMSEQ_offset [where k=M])
  then have "gen_has_prod f 0 (prod f {..<M} * p)" if "\<forall>i<M. f i \<noteq> 0"
    using \<open>p \<noteq> 0\<close> assms that by (auto simp: gen_has_prod_def)
  then show thesis
    using that by blast
qed

corollary convergent_prod_offset_0:
  fixes f :: "nat \<Rightarrow> 'a :: {idom,topological_semigroup_mult,t2_space}"
  assumes "convergent_prod f" "\<And>i. f i \<noteq> 0"
  shows "\<exists>p. gen_has_prod f 0 p"
  using assms convergent_prod_def gen_has_prod_cases by blast

lemma prodinf_eq_lim:
  fixes f :: "nat \<Rightarrow> 'a :: {idom,topological_semigroup_mult,t2_space}"
  assumes "convergent_prod f" "\<And>i. f i \<noteq> 0"
  shows "prodinf f = lim (\<lambda>n. \<Prod>i\<le>n. f i)"
  using assms convergent_prod_offset_0 [OF assms]
  by (simp add: prod_defs lim_def) (metis (no_types) assms(1) convergent_prod_to_zero_iff)

lemma has_prod_one[simp, intro]: "(\<lambda>n. 1) has_prod 1"
  unfolding prod_defs by auto

lemma convergent_prod_one[simp, intro]: "convergent_prod (\<lambda>n. 1)"
  unfolding prod_defs by auto

lemma prodinf_cong: "(\<And>n. f n = g n) \<Longrightarrow> prodinf f = prodinf g"
  by presburger

lemma convergent_prod_cong:
  fixes f g :: "nat \<Rightarrow> 'a::{field,topological_semigroup_mult,t2_space}"
  assumes ev: "eventually (\<lambda>x. f x = g x) sequentially" and f: "\<And>i. f i \<noteq> 0" and g: "\<And>i. g i \<noteq> 0"
  shows "convergent_prod f = convergent_prod g"
proof -
  from assms obtain N where N: "\<forall>n\<ge>N. f n = g n"
    by (auto simp: eventually_at_top_linorder)
  define C where "C = (\<Prod>k<N. f k / g k)"
  with g have "C \<noteq> 0"
    by (simp add: f)
  have *: "eventually (\<lambda>n. prod f {..n} = C * prod g {..n}) sequentially"
    using eventually_ge_at_top[of N]
  proof eventually_elim
    case (elim n)
    then have "{..n} = {..<N} \<union> {N..n}"
      by auto
    also have "prod f \<dots> = prod f {..<N} * prod f {N..n}"
      by (intro prod.union_disjoint) auto
    also from N have "prod f {N..n} = prod g {N..n}"
      by (intro prod.cong) simp_all
    also have "prod f {..<N} * prod g {N..n} = C * (prod g {..<N} * prod g {N..n})"
      unfolding C_def by (simp add: g prod_dividef)
    also have "prod g {..<N} * prod g {N..n} = prod g ({..<N} \<union> {N..n})"
      by (intro prod.union_disjoint [symmetric]) auto
    also from elim have "{..<N} \<union> {N..n} = {..n}"
      by auto                                                                    
    finally show "prod f {..n} = C * prod g {..n}" .
  qed
  then have cong: "convergent (\<lambda>n. prod f {..n}) = convergent (\<lambda>n. C * prod g {..n})"
    by (rule convergent_cong)
  show ?thesis
  proof
    assume cf: "convergent_prod f"
    then have "\<not> (\<lambda>n. prod g {..n}) \<longlonglongrightarrow> 0"
      using tendsto_mult_left * convergent_prod_to_zero_iff f filterlim_cong by fastforce
    then show "convergent_prod g"
      by (metis convergent_mult_const_iff \<open>C \<noteq> 0\<close> cong cf convergent_LIMSEQ_iff convergent_prod_iff_convergent convergent_prod_imp_convergent g)
  next
    assume cg: "convergent_prod g"
    have "\<exists>a. C * a \<noteq> 0 \<and> (\<lambda>n. prod g {..n}) \<longlonglongrightarrow> a"
      by (metis (no_types) \<open>C \<noteq> 0\<close> cg convergent_prod_iff_nz_lim divide_eq_0_iff g nonzero_mult_div_cancel_right)
    then show "convergent_prod f"
      using "*" tendsto_mult_left filterlim_cong
      by (fastforce simp add: convergent_prod_iff_nz_lim f)
  qed
qed

lemma has_prod_finite:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  assumes [simp]: "finite N"
    and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 1"
  shows "f has_prod (\<Prod>n\<in>N. f n)"
proof -
  have eq: "prod f {..n + Suc (Max N)} = prod f N" for n
  proof (rule prod.mono_neutral_right)
    show "N \<subseteq> {..n + Suc (Max N)}"
      by (auto simp: le_Suc_eq trans_le_add2)
    show "\<forall>i\<in>{..n + Suc (Max N)} - N. f i = 1"
      using f by blast
  qed auto
  show ?thesis
  proof (cases "\<forall>n\<in>N. f n \<noteq> 0")
    case True
    then have "prod f N \<noteq> 0"
      by simp
    moreover have "(\<lambda>n. prod f {..n}) \<longlonglongrightarrow> prod f N"
      by (rule LIMSEQ_offset[of _ "Suc (Max N)"]) (simp add: eq atLeast0LessThan del: add_Suc_right)
    ultimately show ?thesis
      by (simp add: gen_has_prod_def has_prod_def)
  next
    case False
    then obtain k where "k \<in> N" "f k = 0"
      by auto
    let ?Z = "{n \<in> N. f n = 0}"
    have maxge: "Max ?Z \<ge> n" if "f n = 0" for n
      using Max_ge [of ?Z] \<open>finite N\<close> \<open>f n = 0\<close>
      by (metis (mono_tags) Collect_mem_eq f finite_Collect_conjI mem_Collect_eq zero_neq_one)
    let ?q = "prod f {Suc (Max ?Z)..Max N}"
    have [simp]: "?q \<noteq> 0"
      using maxge Suc_n_not_le_n le_trans by force
    have eq: "(\<Prod>i\<le>n + Max N. f (Suc (i + Max ?Z))) = ?q" for n
    proof -
      have "(\<Prod>i\<le>n + Max N. f (Suc (i + Max ?Z))) = prod f {Suc (Max ?Z)..n + Max N + Suc (Max ?Z)}" 
      proof (rule prod.reindex_cong [where l = "\<lambda>i. i + Suc (Max ?Z)", THEN sym])
        show "{Suc (Max ?Z)..n + Max N + Suc (Max ?Z)} = (\<lambda>i. i + Suc (Max ?Z)) ` {..n + Max N}"
          using le_Suc_ex by fastforce
      qed (auto simp: inj_on_def)
      also have "\<dots> = ?q"
        by (rule prod.mono_neutral_right)
           (use Max.coboundedI [OF \<open>finite N\<close>] f in \<open>force+\<close>)
      finally show ?thesis .
    qed
    have q: "gen_has_prod f (Suc (Max ?Z)) ?q"
    proof (simp add: gen_has_prod_def)
      show "(\<lambda>n. \<Prod>i\<le>n. f (Suc (i + Max ?Z))) \<longlonglongrightarrow> ?q"
        by (rule LIMSEQ_offset[of _ "(Max N)"]) (simp add: eq)
    qed
    show ?thesis
      unfolding has_prod_def
    proof (intro disjI2 exI conjI)      
      show "prod f N = 0"
        using \<open>f k = 0\<close> \<open>k \<in> N\<close> \<open>finite N\<close> prod_zero by blast
      show "f (Max ?Z) = 0"
        using Max_in [of ?Z] \<open>finite N\<close> \<open>f k = 0\<close> \<open>k \<in> N\<close> by auto
    qed (use q in auto)
  qed
qed

corollary has_prod_0:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  assumes "\<And>n. f n = 1"
  shows "f has_prod 1"
  by (simp add: assms has_prod_cong)

lemma convergent_prod_finite:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  assumes "finite N" "\<And>n. n \<notin> N \<Longrightarrow> f n = 1"
  shows "convergent_prod f"
proof -
  have "\<exists>n p. gen_has_prod f n p"
    using assms has_prod_def has_prod_finite by blast
  then show ?thesis
    by (simp add: convergent_prod_def)
qed

lemma has_prod_If_finite_set:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  shows "finite A \<Longrightarrow> (\<lambda>r. if r \<in> A then f r else 1) has_prod (\<Prod>r\<in>A. f r)"
  using has_prod_finite[of A "(\<lambda>r. if r \<in> A then f r else 1)"]
  by simp

lemma has_prod_If_finite:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  shows "finite {r. P r} \<Longrightarrow> (\<lambda>r. if P r then f r else 1) has_prod (\<Prod>r | P r. f r)"
  using has_prod_If_finite_set[of "{r. P r}"] by simp

lemma convergent_prod_If_finite_set[simp, intro]:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  shows "finite A \<Longrightarrow> convergent_prod (\<lambda>r. if r \<in> A then f r else 1)"
  by (simp add: convergent_prod_finite)

lemma convergent_prod_If_finite[simp, intro]:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  shows "finite {r. P r} \<Longrightarrow> convergent_prod (\<lambda>r. if P r then f r else 1)"
  using convergent_prod_def has_prod_If_finite has_prod_def by fastforce

lemma has_prod_single:
  fixes f :: "nat \<Rightarrow> 'a::{idom,t2_space}"
  shows "(\<lambda>r. if r = i then f r else 1) has_prod f i"
  using has_prod_If_finite[of "\<lambda>r. r = i"] by simp

context
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
begin

lemma convergent_prod_imp_has_prod: 
  assumes "convergent_prod f"
  shows "\<exists>p. f has_prod p"
proof -
  obtain M p where p: "gen_has_prod f M p"
    using assms convergent_prod_def by blast
  then have "p \<noteq> 0"
    using gen_has_prod_nonzero by blast
  with p have fnz: "f i \<noteq> 0" if "i \<ge> M" for i
    using gen_has_prod_eq_0 that by blast
  define C where "C = (\<Prod>n<M. f n)"
  show ?thesis
  proof (cases "\<forall>n\<le>M. f n \<noteq> 0")
    case True
    then have "C \<noteq> 0"
      by (simp add: C_def)
    then show ?thesis
      by (meson True assms convergent_prod_offset_0 fnz has_prod_def nat_le_linear)
  next
    case False
    let ?N = "GREATEST n. f n = 0"
    have 0: "f ?N = 0"
      using fnz False
      by (metis (mono_tags, lifting) GreatestI_ex_nat nat_le_linear)
    have "f i \<noteq> 0" if "i > ?N" for i
      by (metis (mono_tags, lifting) Greatest_le_nat fnz leD linear that)
    then have "\<exists>p. gen_has_prod f (Suc ?N) p"
      using assms by (auto simp: intro!: convergent_prod_ignore_nonzero_segment)
    then show ?thesis
      unfolding has_prod_def using 0 by blast
  qed
qed

lemma convergent_prod_has_prod [intro]:
  shows "convergent_prod f \<Longrightarrow> f has_prod (prodinf f)"
  unfolding prodinf_def
  by (metis convergent_prod_imp_has_prod has_prod_unique theI')

lemma convergent_prod_LIMSEQ:
  shows "convergent_prod f \<Longrightarrow> (\<lambda>n. \<Prod>i\<le>n. f i) \<longlonglongrightarrow> prodinf f"
  by (metis convergent_LIMSEQ_iff convergent_prod_has_prod convergent_prod_imp_convergent 
      convergent_prod_to_zero_iff gen_has_prod_eq_0 has_prod_def prodinf_eq_lim zero_le)

lemma has_prod_iff: "f has_prod x \<longleftrightarrow> convergent_prod f \<and> prodinf f = x"
proof
  assume "f has_prod x"
  then show "convergent_prod f \<and> prodinf f = x"
    apply safe
    using convergent_prod_def has_prod_def apply blast
    using has_prod_unique by blast
qed auto

lemma convergent_prod_has_prod_iff: "convergent_prod f \<longleftrightarrow> f has_prod prodinf f"
  by (auto simp: has_prod_iff convergent_prod_has_prod)

lemma prodinf_finite:
  assumes N: "finite N"
    and f: "\<And>n. n \<notin> N \<Longrightarrow> f n = 1"
  shows "prodinf f = (\<Prod>n\<in>N. f n)"
  using has_prod_finite[OF assms, THEN has_prod_unique] by simp

end

end

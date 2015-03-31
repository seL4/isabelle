section {* polynomial functions: extremal behaviour and root counts *}

(*  Author: John Harrison and Valentina Bruno
    Ported from "hol_light/Multivariate/complexes.ml" by L C Paulson
*)

theory PolyRoots
imports Complex_Main

begin

subsection{*Geometric progressions*}

lemma setsum_gp_basic:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "(1 - x) * (\<Sum>i\<le>n. x^i) = 1 - x^Suc n"
  by (simp only: one_diff_power_eq [of "Suc n" x] lessThan_Suc_atMost)

lemma setsum_gp0:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows   "(\<Sum>i\<le>n. x^i) = (if x = 1 then of_nat(n + 1) else (1 - x^Suc n) / (1 - x))"
  using setsum_gp_basic[of x n]
  by (simp add: real_of_nat_def mult.commute divide_simps)

lemma setsum_power_add:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "(\<Sum>i\<in>I. x^(m+i)) = x^m * (\<Sum>i\<in>I. x^i)"
  by (simp add: setsum_right_distrib power_add)

lemma setsum_power_shift:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  assumes "m \<le> n"
  shows "(\<Sum>i=m..n. x^i) = x^m * (\<Sum>i\<le>n-m. x^i)"
proof -
  have "(\<Sum>i=m..n. x^i) = x^m * (\<Sum>i=m..n. x^(i-m))"
    by (simp add: setsum_right_distrib power_add [symmetric])
  also have "(\<Sum>i=m..n. x^(i-m)) = (\<Sum>i\<le>n-m. x^i)"
    using `m \<le> n` by (intro setsum.reindex_bij_witness[where j="\<lambda>i. i - m" and i="\<lambda>i. i + m"]) auto
  finally show ?thesis .
qed

lemma setsum_gp_multiplied:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  assumes "m \<le> n"
  shows "(1 - x) * (\<Sum>i=m..n. x^i) = x^m - x^Suc n"
proof -
  have  "(1 - x) * (\<Sum>i=m..n. x^i) = x^m * (1 - x) * (\<Sum>i\<le>n-m. x^i)"
    by (metis mult.assoc mult.commute assms setsum_power_shift)
  also have "... =x^m * (1 - x^Suc(n-m))"
    by (metis mult.assoc setsum_gp_basic)
  also have "... = x^m - x^Suc n"
    using assms
    by (simp add: algebra_simps) (metis le_add_diff_inverse power_add)
  finally show ?thesis .
qed

lemma setsum_gp:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows   "(\<Sum>i=m..n. x^i) =
               (if n < m then 0
                else if x = 1 then of_nat((n + 1) - m)
                else (x^m - x^Suc n) / (1 - x))"
using setsum_gp_multiplied [of m n x] 
apply (auto simp: real_of_nat_def)
by (metis eq_iff_diff_eq_0 mult.commute nonzero_divide_eq_eq)

lemma setsum_gp_offset:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows   "(\<Sum>i=m..m+n. x^i) =
       (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  using setsum_gp [of x m "m+n"]
  by (auto simp: power_add algebra_simps)

lemma setsum_gp_strict:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows "(\<Sum>i<n. x^i) = (if x = 1 then of_nat n else (1 - x^n) / (1 - x))"
  by (induct n) (auto simp: algebra_simps divide_simps)
    
subsection{*Basics about polynomial functions: extremal behaviour and root counts.*}

lemma sub_polyfun:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows   "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) = 
           (x - y) * (\<Sum>j<n. \<Sum>k= Suc j..n. a k * y^(k - Suc j) * x^j)"
proof -
  have "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) = 
        (\<Sum>i\<le>n. a i * (x^i - y^i))"
    by (simp add: algebra_simps setsum_subtractf [symmetric])
  also have "... = (\<Sum>i\<le>n. a i * (x - y) * (\<Sum>j<i. y^(i - Suc j) * x^j))"
    by (simp add: power_diff_sumr2 ac_simps)
  also have "... = (x - y) * (\<Sum>i\<le>n. (\<Sum>j<i. a i * y^(i - Suc j) * x^j))"
    by (simp add: setsum_right_distrib ac_simps)
  also have "... = (x - y) * (\<Sum>j<n. (\<Sum>i=Suc j..n. a i * y^(i - Suc j) * x^j))"
    by (simp add: nested_setsum_swap')
  finally show ?thesis .
qed

lemma sub_polyfun_alt:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows   "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) = 
           (x - y) * (\<Sum>j<n. \<Sum>k<n-j. a (j+k+1) * y^k * x^j)"
proof -
  { fix j
    have "(\<Sum>k = Suc j..n. a k * y^(k - Suc j) * x^j) =
          (\<Sum>k <n - j. a (Suc (j + k)) * y^k * x^j)"
      by (rule setsum.reindex_bij_witness[where i="\<lambda>i. i + Suc j" and j="\<lambda>i. i - Suc j"]) auto }
  then show ?thesis
    by (simp add: sub_polyfun)
qed

lemma polyfun_linear_factor:
  fixes a :: "'a::{comm_ring,monoid_mult}"
  shows  "\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) = 
                  (z-a) * (\<Sum>i<n. b i * z^i) + (\<Sum>i\<le>n. c i * a^i)"
proof -
  { fix z
    have "(\<Sum>i\<le>n. c i * z^i) - (\<Sum>i\<le>n. c i * a^i) = 
          (z - a) * (\<Sum>j<n. (\<Sum>k = Suc j..n. c k * a^(k - Suc j)) * z^j)"
      by (simp add: sub_polyfun setsum_left_distrib)
    then have "(\<Sum>i\<le>n. c i * z^i) = 
          (z - a) * (\<Sum>j<n. (\<Sum>k = Suc j..n. c k * a^(k - Suc j)) * z^j)
          + (\<Sum>i\<le>n. c i * a^i)"
      by (simp add: algebra_simps) }
  then show ?thesis
    by (intro exI allI) 
qed

lemma polyfun_linear_factor_root:
  fixes a :: "'a::{comm_ring,monoid_mult}"
  assumes "(\<Sum>i\<le>n. c i * a^i) = 0"
  shows  "\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) = (z-a) * (\<Sum>i<n. b i * z^i)"
  using polyfun_linear_factor [of c n a] assms
  by simp

lemma adhoc_norm_triangle: "a + norm(y) \<le> b ==> norm(x) \<le> a ==> norm(x + y) \<le> b"
  by (metis norm_triangle_mono order.trans order_refl)

lemma polyfun_extremal_lemma:
  fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "e > 0"
    shows "\<exists>M. \<forall>z. M \<le> norm z \<longrightarrow> norm(\<Sum>i\<le>n. c i * z^i) \<le> e * norm(z) ^ Suc n"
proof (induction n)
  case 0
  show ?case 
    by (rule exI [where x="norm (c 0) / e"]) (auto simp: mult.commute pos_divide_le_eq assms)
next
  case (Suc n)
  then obtain M where M: "\<forall>z. M \<le> norm z \<longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n" ..
  show ?case
  proof (rule exI [where x="max 1 (max M ((e + norm(c(Suc n))) / e))"], clarify)
    fix z::'a
    assume "max 1 (max M ((e + norm (c (Suc n))) / e)) \<le> norm z"
    then have norm1: "0 < norm z" "M \<le> norm z" "(e + norm (c (Suc n))) / e \<le> norm z"
      by auto
    then have norm2: "(e + norm (c (Suc n))) \<le> e * norm z"  "(norm z * norm z ^ n) > 0"
      apply (metis assms less_divide_eq mult.commute not_le) 
      using norm1 apply (metis mult_pos_pos zero_less_power)
      done
    have "e * (norm z * norm z ^ n) + norm (c (Suc n) * (z * z ^ n)) =
          (e + norm (c (Suc n))) * (norm z * norm z ^ n)"
      by (simp add: norm_mult norm_power algebra_simps)
    also have "... \<le> (e * norm z) * (norm z * norm z ^ n)"
      using norm2 by (metis real_mult_le_cancel_iff1) 
    also have "... = e * (norm z * (norm z * norm z ^ n))"
      by (simp add: algebra_simps)
    finally have "e * (norm z * norm z ^ n) + norm (c (Suc n) * (z * z ^ n))
                  \<le> e * (norm z * (norm z * norm z ^ n))" .
    then show "norm (\<Sum>i\<le>Suc n. c i * z^i) \<le> e * norm z ^ Suc (Suc n)" using M norm1
      by (drule_tac x=z in spec) (auto simp: intro!: adhoc_norm_triangle)
    qed
qed

lemma norm_lemma_xy: "\<lbrakk>abs b + 1 \<le> norm(y) - a; norm(x) \<le> a\<rbrakk> \<Longrightarrow> b \<le> norm(x + y)"
  by (metis abs_add_one_not_less_self add.commute diff_le_eq dual_order.trans le_less_linear 
         norm_diff_ineq)

lemma polyfun_extremal:
  fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "\<exists>k. k \<noteq> 0 \<and> k \<le> n \<and> c k \<noteq> 0"
    shows "eventually (\<lambda>z. norm(\<Sum>i\<le>n. c i * z^i) \<ge> B) at_infinity"
using assms
proof (induction n)
  case 0 then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases "c (Suc n) = 0")
    case True
    with Suc show ?thesis
      by auto (metis diff_is_0_eq diffs0_imp_equal less_Suc_eq_le not_less_eq)
  next
    case False
    with polyfun_extremal_lemma [of "norm(c (Suc n)) / 2" c n]
    obtain M where M: "\<And>z. M \<le> norm z \<Longrightarrow> 
               norm (\<Sum>i\<le>n. c i * z^i) \<le> norm (c (Suc n)) / 2 * norm z ^ Suc n"
      by auto
    show ?thesis
    unfolding eventually_at_infinity
    proof (rule exI [where x="max M (max 1 ((abs B + 1) / (norm (c (Suc n)) / 2)))"], clarsimp)
      fix z::'a
      assume les: "M \<le> norm z"  "1 \<le> norm z"  "(\<bar>B\<bar> * 2 + 2) / norm (c (Suc n)) \<le> norm z"
      then have "\<bar>B\<bar> * 2 + 2 \<le> norm z * norm (c (Suc n))"
        by (metis False pos_divide_le_eq zero_less_norm_iff)
      then have "\<bar>B\<bar> * 2 + 2 \<le> norm z ^ (Suc n) * norm (c (Suc n))" 
        by (metis `1 \<le> norm z` order.trans mult_right_mono norm_ge_zero self_le_power zero_less_Suc)
      then show "B \<le> norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * (z * z ^ n))" using M les
        apply auto
        apply (rule norm_lemma_xy [where a = "norm (c (Suc n)) * norm z ^ (Suc n) / 2"])
        apply (simp_all add: norm_mult norm_power)
        done
    qed
  qed
qed

lemma polyfun_rootbound:
 fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
 assumes "\<exists>k. k \<le> n \<and> c k \<noteq> 0"
   shows "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<and> card {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<le> n"
using assms
proof (induction n arbitrary: c)
 case (Suc n) show ?case
 proof (cases "{z. (\<Sum>i\<le>Suc n. c i * z^i) = 0} = {}")
   case False
   then obtain a where a: "(\<Sum>i\<le>Suc n. c i * a^i) = 0"
     by auto
   from polyfun_linear_factor_root [OF this]
   obtain b where "\<And>z. (\<Sum>i\<le>Suc n. c i * z^i) = (z - a) * (\<Sum>i< Suc n. b i * z^i)"
     by auto
   then have b: "\<And>z. (\<Sum>i\<le>Suc n. c i * z^i) = (z - a) * (\<Sum>i\<le>n. b i * z^i)"
     by (metis lessThan_Suc_atMost)
   then have ins_ab: "{z. (\<Sum>i\<le>Suc n. c i * z^i) = 0} = insert a {z. (\<Sum>i\<le>n. b i * z^i) = 0}"
     by auto
   have c0: "c 0 = - (a * b 0)" using  b [of 0]
     by simp
   then have extr_prem: "~ (\<exists>k\<le>n. b k \<noteq> 0) \<Longrightarrow> \<exists>k. k \<noteq> 0 \<and> k \<le> Suc n \<and> c k \<noteq> 0"
     by (metis Suc.prems le0 minus_zero mult_zero_right)
   have "\<exists>k\<le>n. b k \<noteq> 0" 
     apply (rule ccontr)
     using polyfun_extremal [OF extr_prem, of 1]
     apply (auto simp: eventually_at_infinity b simp del: setsum_atMost_Suc)
     apply (drule_tac x="of_real ba" in spec, simp)
     done
   then show ?thesis using Suc.IH [of b] ins_ab
     by (auto simp: card_insert_if)
   qed simp
qed simp

corollary
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
  assumes "\<exists>k. k \<le> n \<and> c k \<noteq> 0"
    shows polyfun_rootbound_finite: "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0}"
      and polyfun_rootbound_card:   "card {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<le> n"
using polyfun_rootbound [OF assms] by auto

lemma polyfun_finite_roots:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<longleftrightarrow> (\<exists>k. k \<le> n \<and> c k \<noteq> 0)"
proof (cases " \<exists>k\<le>n. c k \<noteq> 0")
  case True then show ?thesis 
    by (blast intro: polyfun_rootbound_finite)
next
  case False then show ?thesis 
    by (auto simp: infinite_UNIV_char_0)
qed

lemma polyfun_eq_0:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = 0) \<longleftrightarrow> (\<forall>k. k \<le> n \<longrightarrow> c k = 0)"
proof (cases "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = 0)")
  case True
  then have "~ finite {z. (\<Sum>i\<le>n. c i * z^i) = 0}"
    by (simp add: infinite_UNIV_char_0)
  with True show ?thesis
    by (metis (poly_guards_query) polyfun_rootbound_finite)
next
  case False
  then show ?thesis
    by auto
qed

lemma polyfun_eq_const:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = k) \<longleftrightarrow> c 0 = k \<and> (\<forall>k. k \<noteq> 0 \<and> k \<le> n \<longrightarrow> c k = 0)"
proof -
  {fix z
    have "(\<Sum>i\<le>n. c i * z^i) = (\<Sum>i\<le>n. (if i = 0 then c 0 - k else c i) * z^i) + k"
      by (induct n) auto
  } then
  have "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = k) \<longleftrightarrow> (\<forall>z. (\<Sum>i\<le>n. (if i = 0 then c 0 - k else c i) * z^i) = 0)"
    by auto
  also have "... \<longleftrightarrow>  c 0 = k \<and> (\<forall>k. k \<noteq> 0 \<and> k \<le> n \<longrightarrow> c k = 0)"
    by (auto simp: polyfun_eq_0)
  finally show ?thesis .
qed

end


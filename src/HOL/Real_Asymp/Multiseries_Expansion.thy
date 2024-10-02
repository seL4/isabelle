(*
  File:    Multiseries_Expansion.thy
  Author:  Manuel Eberl, TU München

  Asymptotic bases and Multiseries expansions of real-valued functions.
  Contains automation to prove limits and asymptotic relationships between such functions.
*)
section \<open>Multiseries expansions\<close>
theory Multiseries_Expansion
imports
  "HOL-Library.BNF_Corec"
  "HOL-Library.Landau_Symbols"
  Lazy_Eval
  Inst_Existentials
  Eventuallize
begin

(* TODO Move *)
lemma real_powr_at_top: 
  assumes "(p::real) > 0"
  shows   "filterlim (\<lambda>x. x powr p) at_top at_top"
proof (subst filterlim_cong[OF refl refl])
  show "LIM x at_top. exp (p * ln x) :> at_top"
    by (rule filterlim_compose[OF exp_at_top filterlim_tendsto_pos_mult_at_top[OF tendsto_const]])
       (simp_all add: ln_at_top assms)
  show "eventually (\<lambda>x. x powr p = exp (p * ln x)) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim (simp add: powr_def)
qed


subsection \<open>Streams and lazy lists\<close>

codatatype 'a msstream = MSSCons 'a "'a msstream"

primrec mssnth :: "'a msstream \<Rightarrow> nat \<Rightarrow> 'a" where
  "mssnth xs 0 = (case xs of MSSCons x xs \<Rightarrow> x)"
| "mssnth xs (Suc n) = (case xs of MSSCons x xs \<Rightarrow> mssnth xs n)"

codatatype 'a msllist = MSLNil | MSLCons 'a "'a msllist"
  for map: mslmap

fun lcoeff where
  "lcoeff MSLNil n = 0"
| "lcoeff (MSLCons x xs) 0 = x"
| "lcoeff (MSLCons x xs) (Suc n) = lcoeff xs n"

primcorec msllist_of_msstream :: "'a msstream \<Rightarrow> 'a msllist" where
  "msllist_of_msstream xs = (case xs of MSSCons x xs \<Rightarrow> MSLCons x (msllist_of_msstream xs))"
  
lemma msllist_of_msstream_MSSCons [simp]: 
  "msllist_of_msstream (MSSCons x xs) = MSLCons x (msllist_of_msstream xs)"
  by (subst msllist_of_msstream.code) simp

lemma lcoeff_llist_of_stream [simp]: "lcoeff (msllist_of_msstream xs) n = mssnth xs n"
  by (induction "msllist_of_msstream xs" n arbitrary: xs rule: lcoeff.induct;
      subst msllist_of_msstream.code) (auto split: msstream.splits)


subsection \<open>Convergent power series\<close>

subsubsection \<open>Definition\<close>

definition convergent_powser :: "real msllist \<Rightarrow> bool" where
  "convergent_powser cs \<longleftrightarrow> (\<exists>R>0. \<forall>x. abs x < R \<longrightarrow> summable (\<lambda>n. lcoeff cs n * x ^ n))"
 
lemma convergent_powser_stl:
  assumes "convergent_powser (MSLCons c cs)"
  shows   "convergent_powser cs"
proof -
  from assms obtain R where "R > 0" "\<And>x. abs x < R \<Longrightarrow> summable (\<lambda>n. lcoeff (MSLCons c cs) n * x ^ n)"
    unfolding convergent_powser_def by blast
  hence "summable (\<lambda>n. lcoeff cs n * x ^ n)" if "abs x < R" for x
    using that by (subst (asm) summable_powser_split_head [symmetric]) simp
  thus ?thesis using \<open>R > 0\<close> by (auto simp: convergent_powser_def)
qed
  
  
definition powser :: "real msllist \<Rightarrow> real \<Rightarrow> real" where
  "powser cs x = suminf (\<lambda>n. lcoeff cs n * x ^ n)"

lemma isCont_powser:
  assumes "convergent_powser cs"
  shows   "isCont (powser cs) 0"
proof -
  from assms obtain R where R: "R > 0" "\<And>x. abs x < R \<Longrightarrow> summable (\<lambda>n. lcoeff cs n * x ^ n)"
    unfolding convergent_powser_def by blast
  hence *: "summable (\<lambda>n. lcoeff cs n * (R/2) ^ n)" by (intro R) simp_all
  from \<open>R > 0\<close> show ?thesis unfolding powser_def
    by (intro isCont_powser[OF *]) simp_all
qed

lemma powser_MSLNil [simp]: "powser MSLNil = (\<lambda>_. 0)"
  by (simp add: fun_eq_iff powser_def)

lemma powser_MSLCons:
  assumes "convergent_powser (MSLCons c cs)"
  shows   "eventually (\<lambda>x. powser (MSLCons c cs) x = x * powser cs x + c) (nhds 0)"
proof -
  from assms obtain R where R: "R > 0" "\<And>x. abs x < R \<Longrightarrow> summable (\<lambda>n. lcoeff (MSLCons c cs) n * x ^ n)"
    unfolding convergent_powser_def by blast
  from R have "powser (MSLCons c cs) x = x * powser cs x + c" if "abs x < R" for x
    using that unfolding powser_def by (subst powser_split_head) simp_all
  moreover have "eventually (\<lambda>x. abs x < R) (nhds 0)"
    using \<open>R > 0\<close> filterlim_ident[of "nhds (0::real)"]
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  ultimately show ?thesis by (auto elim: eventually_mono)
qed

definition convergent_powser' :: "real msllist \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "convergent_powser' cs f \<longleftrightarrow> (\<exists>R>0. \<forall>x. abs x < R \<longrightarrow> (\<lambda>n. lcoeff cs n * x ^ n) sums f x)"

lemma convergent_powser'_imp_convergent_powser:
  "convergent_powser' cs f \<Longrightarrow> convergent_powser cs" 
  unfolding convergent_powser_def convergent_powser'_def by (auto simp: sums_iff)

lemma convergent_powser'_eventually:
  assumes "convergent_powser' cs f"
  shows   "eventually (\<lambda>x. powser cs x = f x) (nhds 0)"
proof -
  from assms obtain R where "R > 0" "\<And>x. abs x < R \<Longrightarrow> (\<lambda>n. lcoeff cs n * x ^ n) sums f x"
    unfolding convergent_powser'_def by blast
  hence "powser cs x = f x" if "abs x < R" for x
    using that by (simp add: powser_def sums_iff)
  moreover have "eventually (\<lambda>x. abs x < R) (nhds 0)"
    using \<open>R > 0\<close> filterlim_ident[of "nhds (0::real)"]
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  ultimately show ?thesis by (auto elim: eventually_mono)
qed  


subsubsection \<open>Geometric series\<close>

primcorec mssalternate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a msstream" where
  "mssalternate a b = MSSCons a (mssalternate b a)"

lemma case_mssalternate [simp]: 
  "(case mssalternate a b of MSSCons c d \<Rightarrow> f c d) = f a (mssalternate b a)"
  by (subst mssalternate.code) simp

lemma mssnth_mssalternate: "mssnth (mssalternate a b) n = (if even n then a else b)"
  by (induction n arbitrary: a b; subst mssalternate.code) simp_all
  
lemma convergent_powser'_geometric:
  "convergent_powser' (msllist_of_msstream (mssalternate 1 (-1))) (\<lambda>x. inverse (1 + x))"
proof -
  have "(\<lambda>n. lcoeff (msllist_of_msstream (mssalternate 1 (-1))) n * x ^ n) sums (inverse (1 + x))"
    if "abs x < 1" for x :: real
  proof -
    have "(\<lambda>n. (-1) ^ n * x ^ n) sums (inverse (1 + x))"
      using that geometric_sums[of "-x"] by (simp add: field_simps power_mult_distrib [symmetric])
    also have "(\<lambda>n. (-1) ^ n * x ^ n) =
                 (\<lambda>n. lcoeff (msllist_of_msstream (mssalternate 1 (-1))) n * x ^ n)"
      by (auto simp add: mssnth_mssalternate fun_eq_iff)
    finally show ?thesis .
  qed
  thus ?thesis unfolding convergent_powser'_def by (force intro!: exI[of _ 1])
qed


subsubsection \<open>Exponential series\<close>

primcorec exp_series_stream_aux :: "real \<Rightarrow> real \<Rightarrow> real msstream" where
  "exp_series_stream_aux acc n = MSSCons acc (exp_series_stream_aux (acc / n) (n + 1))"
  
lemma mssnth_exp_series_stream_aux:
  "mssnth (exp_series_stream_aux (1 / fact n) (n + 1)) m = 1 / fact (n + m)"
proof (induction m arbitrary: n)
  case (0 n)
  thus ?case by (subst exp_series_stream_aux.code) simp
next
  case (Suc m n)
  from Suc.IH[of "n + 1"] show ?case
    by (subst exp_series_stream_aux.code) (simp add: algebra_simps)
qed

definition exp_series_stream :: "real msstream" where
  "exp_series_stream = exp_series_stream_aux 1 1"
  
lemma mssnth_exp_series_stream:
  "mssnth exp_series_stream n = 1 / fact n"
  unfolding exp_series_stream_def using mssnth_exp_series_stream_aux[of 0 n] by simp

lemma convergent_powser'_exp:
  "convergent_powser' (msllist_of_msstream exp_series_stream) exp"
proof -
  have "(\<lambda>n. lcoeff (msllist_of_msstream exp_series_stream) n * x ^ n) sums exp x" for x :: real
    using exp_converges[of x] by (simp add: mssnth_exp_series_stream field_split_simps)
  thus ?thesis by (auto intro: exI[of _ "1::real"] simp: convergent_powser'_def)
qed
  

subsubsection \<open>Logarithm series\<close>

primcorec ln_series_stream_aux :: "bool \<Rightarrow> real \<Rightarrow> real msstream" where
  "ln_series_stream_aux b n = 
     MSSCons (if b then -inverse n else inverse n) (ln_series_stream_aux (\<not>b) (n+1))"

lemma mssnth_ln_series_stream_aux:
  "mssnth (ln_series_stream_aux b x) n = 
     (if b then - ((-1)^n) * inverse (x + real n) else ((-1)^n) * inverse (x + real n))"
  by (induction n arbitrary: b x; subst ln_series_stream_aux.code) simp_all

definition ln_series_stream :: "real msstream" where
  "ln_series_stream = MSSCons 0 (ln_series_stream_aux False 1)"
  
lemma mssnth_ln_series_stream:
  "mssnth ln_series_stream n = (-1) ^ Suc n / real n"
  unfolding ln_series_stream_def 
  by (cases n) (simp_all add: mssnth_ln_series_stream_aux field_simps)

lemma ln_series': 
  assumes "abs (x::real) < 1"
  shows   "(\<lambda>n. - ((-x)^n) / of_nat n) sums ln (1 + x)"
proof -
  have "\<forall>n\<ge>1. norm (-((-x)^n)) / of_nat n \<le> norm x ^ n / 1"
    by (intro exI[of _ "1::nat"] allI impI frac_le) (simp_all add: power_abs)
  hence "\<exists>N. \<forall>n\<ge>N. norm (-((-x)^n) / of_nat n) \<le> norm x ^ n" 
    by (intro exI[of _ 1]) simp_all
  moreover from assms have "summable (\<lambda>n. norm x ^ n)" 
    by (intro summable_geometric) simp_all
  ultimately have *: "summable (\<lambda>n. - ((-x)^n) / of_nat n)"
    by (rule summable_comparison_test)
  moreover from assms have "0 < 1 + x" "1 + x < 2" by simp_all
  from ln_series[OF this] 
    have "ln (1 + x) = (\<Sum>n. - ((-x) ^ Suc n) / real (Suc n))"
    by (simp_all add: power_minus' mult_ac)
  hence "ln (1 + x) = (\<Sum>n. - ((-x) ^ n / real n))"
    by (subst (asm) suminf_split_head[OF *]) simp_all
  ultimately show ?thesis by (simp add: sums_iff)
qed

lemma convergent_powser'_ln:
  "convergent_powser' (msllist_of_msstream ln_series_stream) (\<lambda>x. ln (1 + x))"
proof -
  have "(\<lambda>n. lcoeff (msllist_of_msstream ln_series_stream)n * x ^ n) sums ln (1 + x)"
    if "abs x < 1" for x
  proof -
    from that have "(\<lambda>n. - ((- x) ^ n) / real n) sums ln (1 + x)" by (rule ln_series')
    also have "(\<lambda>n. - ((- x) ^ n) / real n) =
                 (\<lambda>n. lcoeff (msllist_of_msstream ln_series_stream) n * x ^ n)"
      by (auto simp: fun_eq_iff mssnth_ln_series_stream power_mult_distrib [symmetric])
    finally show ?thesis .
  qed
  thus ?thesis unfolding convergent_powser'_def by (force intro!: exI[of _ 1])
qed


subsubsection \<open>Generalized binomial series\<close>

primcorec gbinomial_series_aux :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real msllist" where
  "gbinomial_series_aux abort x n acc =
     (if abort \<and> acc = 0 then MSLNil else 
        MSLCons acc (gbinomial_series_aux abort x (n + 1) ((x - n) / (n + 1) * acc)))"

lemma gbinomial_series_abort [simp]: "gbinomial_series_aux True x n 0 = MSLNil"
  by (subst gbinomial_series_aux.code) simp

definition gbinomial_series :: "bool \<Rightarrow> real \<Rightarrow> real msllist" where
  "gbinomial_series abort x = gbinomial_series_aux abort x 0 1"


(* TODO Move *)
lemma gbinomial_Suc_rec:
  "(x gchoose (Suc k)) = (x gchoose k) * ((x - of_nat k) / (of_nat k + 1))"
proof -
  have "((x - 1) + 1) gchoose (Suc k) = x * (x - 1 gchoose k) / (1 + of_nat k)"
    by (subst gbinomial_factors) simp
  also have "x * (x - 1 gchoose k) = (x - of_nat k) * (x gchoose k)"
    by (rule gbinomial_absorb_comp [symmetric])
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma lcoeff_gbinomial_series_aux:
  "lcoeff (gbinomial_series_aux abort x m (x gchoose m)) n = (x gchoose (n + m))"
proof (induction n arbitrary: m)
  case 0
  show ?case by (subst gbinomial_series_aux.code) simp
next
  case (Suc n m)
  show ?case
  proof (cases "abort \<and> (x gchoose m) = 0")
    case True
    with gbinomial_mult_fact[of m x] obtain k where "x = real k" "k < m"
      by auto
    hence "(x gchoose Suc (n + m)) = 0"
      using gbinomial_mult_fact[of "Suc (n + m)" x]
      by (simp add: gbinomial_altdef_of_nat)
    with True show ?thesis by (subst gbinomial_series_aux.code) simp
  next
    case False
    hence "lcoeff (gbinomial_series_aux abort x m (x gchoose m)) (Suc n) = 
             lcoeff (gbinomial_series_aux abort x (Suc m) ((x gchoose m) *
             ((x - real m) / (real m + 1)))) n"
      by (subst gbinomial_series_aux.code) (auto simp: algebra_simps)
    also have "((x gchoose m) * ((x - real m) / (real m + 1))) = x gchoose (Suc m)" 
      by (rule gbinomial_Suc_rec [symmetric])
    also have "lcoeff (gbinomial_series_aux abort x (Suc m) \<dots>) n = x gchoose (n + Suc m)"
      by (rule Suc.IH)
    finally show ?thesis by simp
  qed
qed

lemma lcoeff_gbinomial_series [simp]:
  "lcoeff (gbinomial_series abort x) n = (x gchoose n)"
  using lcoeff_gbinomial_series_aux[of abort x 0 n] by (simp add: gbinomial_series_def)

lemma gbinomial_ratio_limit:
  fixes a :: "'a :: real_normed_field"
  assumes "a \<notin> \<nat>"
  shows "(\<lambda>n. (a gchoose n) / (a gchoose Suc n)) \<longlonglongrightarrow> -1"
proof (rule Lim_transform_eventually)
  let ?f = "\<lambda>n. inverse (a / of_nat (Suc n) - of_nat n / of_nat (Suc n))"
  from eventually_gt_at_top[of "0::nat"]
    show "eventually (\<lambda>n. ?f n = (a gchoose n) /(a gchoose Suc n)) sequentially"
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    then obtain q where q: "n = Suc q" by (cases n) blast
    let ?P = "\<Prod>i=0..<n. a - of_nat i"
    from n have "(a gchoose n) / (a gchoose Suc n) = (of_nat (Suc n) :: 'a) *
                   (?P / (\<Prod>i=0..n. a - of_nat i))"
      by (simp add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
    also from q have "(\<Prod>i=0..n. a - of_nat i) = ?P * (a - of_nat n)"
      by (simp add: prod.atLeast0_atMost_Suc atLeastLessThanSuc_atLeastAtMost)
    also have "?P / \<dots> = (?P / ?P) / (a - of_nat n)" by (rule divide_divide_eq_left[symmetric])
    also from assms have "?P / ?P = 1" by auto
    also have "of_nat (Suc n) * (1 / (a - of_nat n)) =
                   inverse (inverse (of_nat (Suc n)) * (a - of_nat n))" by (simp add: field_simps)
    also have "inverse (of_nat (Suc n)) * (a - of_nat n) =
                 a / of_nat (Suc n) - of_nat n / of_nat (Suc n)"
      by (simp add: field_simps del: of_nat_Suc)
    finally show "?f n = (a gchoose n) / (a gchoose Suc n)" by simp
  qed

  have "(\<lambda>n. norm a / (of_nat (Suc n))) \<longlonglongrightarrow> 0"
    unfolding divide_inverse
    by (intro tendsto_mult_right_zero LIMSEQ_inverse_real_of_nat)
  hence "(\<lambda>n. a / of_nat (Suc n)) \<longlonglongrightarrow> 0"
    by (subst tendsto_norm_zero_iff[symmetric]) (simp add: norm_divide del: of_nat_Suc)
  hence "?f \<longlonglongrightarrow> inverse (0 - 1)"
    by (intro tendsto_inverse tendsto_diff LIMSEQ_n_over_Suc_n) simp_all
  thus "?f \<longlonglongrightarrow> -1" by simp
qed
  
lemma summable_gbinomial:
  fixes a z :: real
  assumes "norm z < 1"
  shows   "summable (\<lambda>n. (a gchoose n) * z ^ n)"
proof (cases "z = 0 \<or> a \<in> \<nat>")
  case False
  define r where "r = (norm z + 1) / 2"
  from assms have r: "r > norm z" "r < 1" by (simp_all add: r_def field_simps)
  from False have "abs z > 0" by auto
  from False have "a \<notin> \<nat>" by (auto elim!: Nats_cases)
  hence *: "(\<lambda>n. norm (z / ((a gchoose n) / (a gchoose (Suc n))))) \<longlonglongrightarrow> norm (z / (-1))"
    by (intro tendsto_norm tendsto_divide tendsto_const gbinomial_ratio_limit) simp_all
  hence "\<forall>\<^sub>F x in at_top. norm (z / ((a gchoose x) / (a gchoose Suc x))) > 0"
    using assms False by (intro order_tendstoD) auto
  hence nz: "\<forall>\<^sub>F x in at_top. (a gchoose x) \<noteq> 0" by eventually_elim auto
      
  have "\<forall>\<^sub>F x in at_top. norm (z / ((a gchoose x) / (a gchoose Suc x))) < r"
    using assms r by (intro order_tendstoD(2)[OF *]) simp_all
  with nz have "\<forall>\<^sub>F n in at_top. norm ((a gchoose (Suc n)) * z) \<le> r * norm (a gchoose n)"
    by eventually_elim (simp add: field_simps abs_mult split: if_splits)
  hence "\<forall>\<^sub>F n in at_top. norm (z ^ n) * norm ((a gchoose (Suc n)) * z) \<le>
                           norm (z ^ n) * (r * norm (a gchoose n))"
    by eventually_elim (insert False, intro mult_left_mono, auto)
  hence "\<forall>\<^sub>F n in at_top. norm ((a gchoose (Suc n)) * z ^ (Suc n)) \<le> 
                           r * norm ((a gchoose n) * z ^ n)"
    by (simp add: abs_mult mult_ac)
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm ((a gchoose (Suc n)) * z ^ (Suc n)) \<le>
                                          r * norm ((a gchoose n) * z ^ n)"
    unfolding eventually_at_top_linorder by blast
  show "summable (\<lambda>n. (a gchoose n) * z ^ n)"
    by (intro summable_ratio_test[OF r(2), of N] N)
next
  case True
  thus ?thesis
  proof
    assume "a \<in> \<nat>"
    then obtain n where [simp]: "a = of_nat n" by (auto elim: Nats_cases)
    from eventually_gt_at_top[of n] 
      have "eventually (\<lambda>n. (a gchoose n) * z ^ n = 0) at_top"
      by eventually_elim (simp add: binomial_gbinomial [symmetric])
    from summable_cong[OF this] show ?thesis by simp
  qed auto
qed

lemma gen_binomial_real:
  fixes z :: real
  assumes "norm z < 1"
  shows   "(\<lambda>n. (a gchoose n) * z^n) sums (1 + z) powr a"
proof -
  define K where "K = 1 - (1 - norm z) / 2"
  from assms have K: "K > 0" "K < 1" "norm z < K"
     unfolding K_def by (auto simp: field_simps intro!: add_pos_nonneg)
  let ?f = "\<lambda>n. a gchoose n" and ?f' = "diffs (\<lambda>n. a gchoose n)"
  have summable_strong: "summable (\<lambda>n. ?f n * z ^ n)" if "norm z < 1" for z using that
    by (intro summable_gbinomial)
  with K have summable: "summable (\<lambda>n. ?f n * z ^ n)" if "norm z < K" for z using that by auto
  hence summable': "summable (\<lambda>n. ?f' n * z ^ n)" if "norm z < K" for z using that
    by (intro termdiff_converges[of _ K]) simp_all

  define f f' where [abs_def]: "f z = (\<Sum>n. ?f n * z ^ n)" "f' z = (\<Sum>n. ?f' n * z ^ n)" for z
  {
    fix z :: real assume z: "norm z < K"
    from summable_mult2[OF summable'[OF z], of z]
      have summable1: "summable (\<lambda>n. ?f' n * z ^ Suc n)" by (simp add: mult_ac)
    hence summable2: "summable (\<lambda>n. of_nat n * ?f n * z^n)"
      unfolding diffs_def by (subst (asm) summable_Suc_iff)

    have "(1 + z) * f' z = (\<Sum>n. ?f' n * z^n) + (\<Sum>n. ?f' n * z^Suc n)"
      unfolding f_f'_def using summable' z by (simp add: algebra_simps suminf_mult)
    also have "(\<Sum>n. ?f' n * z^n) = (\<Sum>n. of_nat (Suc n) * ?f (Suc n) * z^n)"
      by (intro suminf_cong) (simp add: diffs_def)
    also have "(\<Sum>n. ?f' n * z^Suc n) = (\<Sum>n. of_nat n * ?f n * z ^ n)"
      using summable1 suminf_split_initial_segment[OF summable1] unfolding diffs_def
      by (subst suminf_split_head, subst (asm) summable_Suc_iff) simp_all
    also have "(\<Sum>n. of_nat (Suc n) * ?f (Suc n) * z^n) + (\<Sum>n. of_nat n * ?f n * z^n) =
                 (\<Sum>n. a * ?f n * z^n)"
      by (subst gbinomial_mult_1, subst suminf_add)
         (insert summable'[OF z] summable2,
          simp_all add: summable_powser_split_head algebra_simps diffs_def)
    also have "\<dots> = a * f z" unfolding f_f'_def
      by (subst suminf_mult[symmetric]) (simp_all add: summable[OF z] mult_ac)
    finally have "a * f z = (1 + z) * f' z" by simp
  } note deriv = this

  have [derivative_intros]: "(f has_field_derivative f' z) (at z)" if "norm z < of_real K" for z
    unfolding f_f'_def using K that
    by (intro termdiffs_strong[of "?f" K z] summable_strong) simp_all
  have "f 0 = (\<Sum>n. if n = 0 then 1 else 0)" unfolding f_f'_def by (intro suminf_cong) simp
  also have "\<dots> = 1" using sums_single[of 0 "\<lambda>_. 1::real"] unfolding sums_iff by simp
  finally have [simp]: "f 0 = 1" .

  have "f z * (1 + z) powr (-a) = f 0 * (1 + 0) powr (-a)"
  proof (rule DERIV_isconst3[where ?f = "\<lambda>x. f x * (1 + x) powr (-a)"])
    fix z :: real assume z': "z \<in> {-K<..<K}"
    hence z: "norm z < K" using K by auto
    with K have nz: "1 + z \<noteq> 0" by (auto dest!: minus_unique)
    from z K have "norm z < 1" by simp
    hence "((\<lambda>z. f z * (1 + z) powr (-a)) has_field_derivative
              f' z * (1 + z) powr (-a) - a * f z * (1 + z) powr (-a-1)) (at z)" using z
      by (auto intro!: derivative_eq_intros)
    also from z have "a * f z = (1 + z) * f' z" by (rule deriv)
    also have "f' z * (1 + z) powr - a - (1 + z) * f' z * (1 + z) powr (- a - 1) = 0"
      using \<open>norm z < 1\<close> by (auto simp add: field_simps powr_diff)
    finally show "((\<lambda>z. f z * (1 + z) powr (-a)) has_field_derivative 0) (at z)" .
  qed (insert K, auto)
  also have "f 0 * (1 + 0) powr -a = 1" by simp
  finally have "f z = (1 + z) powr a" using K
    by (simp add: field_simps dist_real_def powr_minus)
  with summable K show ?thesis unfolding f_f'_def by (simp add: sums_iff)
qed

lemma convergent_powser'_gbinomial:
  "convergent_powser' (gbinomial_series abort p) (\<lambda>x. (1 + x) powr p)"
proof -
  have "(\<lambda>n. lcoeff (gbinomial_series abort p) n * x ^ n) sums (1 + x) powr p" if "abs x < 1" for x
    using that gen_binomial_real[of x p] by simp
  thus ?thesis unfolding convergent_powser'_def by (force intro!: exI[of _ 1])
qed

lemma convergent_powser'_gbinomial':
  "convergent_powser' (gbinomial_series abort (real n)) (\<lambda>x. (1 + x) ^ n)"
proof -
  {
    fix x :: real
    have "(\<lambda>k. if k \<in> {0..n} then real (n choose k) * x ^ k else 0) sums (x + 1) ^ n"
      using sums_If_finite_set[of "{..n}" "\<lambda>k. real (n choose k) * x ^ k"]
      by (subst binomial_ring) simp
    also have "(\<lambda>k. if k \<in> {0..n} then real (n choose k) * x ^ k else 0) = 
                 (\<lambda>k. lcoeff (gbinomial_series abort (real n)) k * x ^ k)"
      by (simp add: fun_eq_iff binomial_gbinomial [symmetric])
    finally have "\<dots> sums (1 + x) ^ n" by (simp add: add_ac)
  }
  thus ?thesis unfolding convergent_powser'_def
    by (auto intro!: exI[of _ 1])
qed


subsubsection \<open>Sine and cosine\<close>

primcorec sin_series_stream_aux :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real msstream" where
  "sin_series_stream_aux b acc m = 
    MSSCons (if b then -inverse acc else inverse acc)
          (sin_series_stream_aux (\<not>b) (acc * (m + 1) * (m + 2)) (m + 2))"

lemma mssnth_sin_series_stream_aux:
  "mssnth (sin_series_stream_aux b (fact m) m) n = 
     (if b then -1 else 1) * (-1) ^ n / (fact (2 * n + m))"
proof (induction n arbitrary: b m) 
  case (0 b m)
  thus ?case by (subst sin_series_stream_aux.code) (simp add: field_simps)
next
  case (Suc n b m)
  show ?case using Suc.IH[of "\<not>b" "m + 2"]
    by (subst sin_series_stream_aux.code) (auto simp: field_simps)
qed

definition sin_series_stream where
  "sin_series_stream = sin_series_stream_aux False 1 1"

lemma mssnth_sin_series_stream:
  "mssnth sin_series_stream n = (-1) ^ n / fact (2 * n + 1)"
  using mssnth_sin_series_stream_aux[of False 1 n] unfolding sin_series_stream_def by simp

definition cos_series_stream where
  "cos_series_stream = sin_series_stream_aux False 1 0"

lemma mssnth_cos_series_stream:
  "mssnth cos_series_stream n = (-1) ^ n / fact (2 * n)"
  using mssnth_sin_series_stream_aux[of False 0 n] unfolding cos_series_stream_def by simp

lemma summable_pre_sin: "summable (\<lambda>n. mssnth sin_series_stream n * (x::real) ^ n)"
proof -
  have *: "summable (\<lambda>n. 1 / fact n * abs x ^ n)"
    using exp_converges[of "abs x"] by (simp add: sums_iff field_simps)
  {
    fix n :: nat
    have "\<bar>x\<bar> ^ n / fact (2 * n + 1) \<le> \<bar>x\<bar> ^ n / fact n"
      by (intro divide_left_mono fact_mono) auto
    hence "norm (mssnth sin_series_stream n * x ^ n) \<le> 1 / fact n * abs x ^ n"
      by (simp add: mssnth_sin_series_stream abs_mult power_abs field_simps)
  }
  thus ?thesis
    by (intro summable_comparison_test[OF _ *]) (auto intro!: exI[of _ 0])
qed

lemma summable_pre_cos: "summable (\<lambda>n. mssnth cos_series_stream n * (x::real) ^ n)"
proof -
  have *: "summable (\<lambda>n. 1 / fact n * abs x ^ n)"
    using exp_converges[of "abs x"] by (simp add: sums_iff field_simps)
  {
    fix n :: nat
    have "\<bar>x\<bar> ^ n / fact (2 * n) \<le> \<bar>x\<bar> ^ n / fact n"
      by (intro divide_left_mono fact_mono) auto
    hence "norm (mssnth cos_series_stream n * x ^ n) \<le> 1 / fact n * abs x ^ n"
      by (simp add: mssnth_cos_series_stream abs_mult power_abs field_simps)
  }
  thus ?thesis
    by (intro summable_comparison_test[OF _ *]) (auto intro!: exI[of _ 0])
qed

lemma cos_conv_pre_cos:
  "cos x = powser (msllist_of_msstream cos_series_stream) (x ^ 2)"
proof -
  have "(\<lambda>n. cos_coeff (2 * n) * x ^ (2 * n)) sums cos x"
    using cos_converges[of x]
    by (subst sums_mono_reindex[of "\<lambda>n. 2 * n"])
       (auto simp: strict_mono_def cos_coeff_def elim!: evenE)
  also have "(\<lambda>n. cos_coeff (2 * n) * x ^ (2 * n)) =
               (\<lambda>n. mssnth cos_series_stream n * (x ^ 2) ^ n)"
    by (simp add: fun_eq_iff mssnth_cos_series_stream cos_coeff_def power_mult)
  finally have sums: "(\<lambda>n. mssnth cos_series_stream n * x\<^sup>2 ^ n) sums cos x" .
  thus ?thesis by (simp add: powser_def sums_iff)
qed

lemma sin_conv_pre_sin:
  "sin x = x * powser (msllist_of_msstream sin_series_stream) (x ^ 2)"
proof -
  have "(\<lambda>n. sin_coeff (2 * n + 1) * x ^ (2 * n + 1)) sums sin x"
    using sin_converges[of x]
    by (subst sums_mono_reindex[of "\<lambda>n. 2 * n + 1"])
       (auto simp: strict_mono_def sin_coeff_def elim!: oddE)
  also have "(\<lambda>n. sin_coeff (2 * n + 1) * x ^ (2 * n + 1)) =
               (\<lambda>n. x * mssnth sin_series_stream n * (x ^ 2) ^ n)"
    by (simp add: fun_eq_iff mssnth_sin_series_stream sin_coeff_def power_mult [symmetric] algebra_simps)
  finally have sums: "(\<lambda>n. x * mssnth sin_series_stream n * x\<^sup>2 ^ n) sums sin x" .
  thus ?thesis using summable_pre_sin[of "x^2"] 
    by (simp add: powser_def sums_iff suminf_mult [symmetric] mult.assoc)
qed

lemma convergent_powser_sin_series_stream:
  "convergent_powser (msllist_of_msstream sin_series_stream)"
  (is "convergent_powser ?cs")
proof -
  show ?thesis using summable_pre_sin unfolding convergent_powser_def
    by (intro exI[of _ 1]) auto
qed

lemma convergent_powser_cos_series_stream:
  "convergent_powser (msllist_of_msstream cos_series_stream)"
  (is "convergent_powser ?cs")
proof -
  show ?thesis using summable_pre_cos unfolding convergent_powser_def
    by (intro exI[of _ 1]) auto
qed
  
  
subsubsection \<open>Arc tangent\<close>

definition arctan_coeffs :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra, banach}" where
  "arctan_coeffs n = (if odd n then (-1) ^ (n div 2) / of_nat n else 0)"

lemma arctan_converges:
  assumes "norm x < 1"
  shows   "(\<lambda>n. arctan_coeffs n * x ^ n) sums arctan x"
proof -
  have A: "(\<lambda>n. diffs arctan_coeffs n * x ^ n) sums (1 / (1 + x^2))" if "norm x < 1" for x :: real
  proof -
    let ?f = "\<lambda>n. (if odd n then 0 else (-1) ^ (n div 2)) * x ^ n"
    from that have "norm x ^ 2 < 1 ^ 2" by (intro power_strict_mono) simp_all
    hence "(\<lambda>n. (-(x^2))^n) sums (1 / (1 - (-(x^2))))" by (intro geometric_sums) simp_all
    also have "1 - (-(x^2)) = 1 + x^2" by simp
    also have "(\<lambda>n. (-(x^2))^n) = (\<lambda>n. ?f (2*n))" by (auto simp: fun_eq_iff power_minus' power_mult)
    also have "range ((*) (2::nat)) = {n. even n}"
      by (auto elim!: evenE)
    hence "(\<lambda>n. ?f (2*n)) sums (1 / (1 + x^2)) \<longleftrightarrow> ?f sums (1 / (1 + x^2))"
      by (intro sums_mono_reindex) (simp_all add: strict_mono_Suc_iff)
    also have "?f = (\<lambda>n. diffs arctan_coeffs n * x ^ n)"
      by (simp add: fun_eq_iff arctan_coeffs_def diffs_def)
    finally show "(\<lambda>n. diffs arctan_coeffs n * x ^ n) sums (1 / (1 + x^2))" .
  qed
  
  have B: "summable (\<lambda>n. arctan_coeffs n * x ^ n)" if "norm x < 1" for x :: real
  proof (rule summable_comparison_test)
    show "\<exists>N. \<forall>n\<ge>N. norm (arctan_coeffs n * x ^ n) \<le> 1 * norm x ^ n"
      unfolding norm_mult norm_power
      by (intro exI[of _ "0::nat"] allI impI mult_right_mono)
         (simp_all add: arctan_coeffs_def field_split_simps)
    from that show "summable (\<lambda>n. 1 * norm x ^ n)"
      by (intro summable_mult summable_geometric) simp_all
  qed
  
  define F :: "real \<Rightarrow> real" where "F = (\<lambda>x. \<Sum>n. arctan_coeffs n * x ^ n)"
  have [derivative_intros]:
    "(F has_field_derivative (1 / (1 + x^2))) (at x)" if "norm x < 1" for x :: real
  proof -
    define K :: real where "K = (1 + norm x) / 2"
    from that have K: "norm x < K" "K < 1" by (simp_all add: K_def field_simps)
    have "(F has_field_derivative (\<Sum>n. diffs arctan_coeffs n * x ^ n)) (at x)"
      unfolding F_def using K by (intro termdiffs_strong[where K = K] B) simp_all
    also from A[OF that] have "(\<Sum>n. diffs arctan_coeffs n * x ^ n) = 1 / (1 + x^2)"
      by (simp add: sums_iff)
    finally show ?thesis .
  qed
  from assms have "arctan x - F x = arctan 0 - F 0"
    by (intro DERIV_isconst3[of "-1" 1 _ _ "\<lambda>x. arctan x - F x"])
       (auto intro!: derivative_eq_intros simp: field_simps)
  hence "F x = arctan x" by (simp add: F_def arctan_coeffs_def)
  with B[OF assms] show ?thesis by (simp add: sums_iff F_def)
qed

primcorec arctan_series_stream_aux :: "bool \<Rightarrow> real \<Rightarrow> real msstream" where
  "arctan_series_stream_aux b n = 
     MSSCons (if b then -inverse n else inverse n) (arctan_series_stream_aux (\<not>b) (n + 2))"

lemma mssnth_arctan_series_stream_aux: 
  "mssnth (arctan_series_stream_aux b n) m = (-1) ^ (if b then Suc m else m) / (2*m + n)"
  by (induction m arbitrary: b n; subst arctan_series_stream_aux.code)
     (auto simp: field_simps split: if_splits)

definition arctan_series_stream where
  "arctan_series_stream = arctan_series_stream_aux False 1"

lemma mssnth_arctan_series_stream:
  "mssnth arctan_series_stream n = (-1) ^ n / (2 * n + 1)"
  by (simp add: arctan_series_stream_def mssnth_arctan_series_stream_aux)

lemma summable_pre_arctan:
  assumes "norm x < 1"
  shows   "summable (\<lambda>n. mssnth arctan_series_stream n * x ^ n)" (is "summable ?f")
proof (rule summable_comparison_test)
  show "summable (\<lambda>n. abs x ^ n)" using assms by (intro summable_geometric) auto
  show "\<exists>N. \<forall>n\<ge>N. norm (?f n) \<le> abs x ^ n"
  proof (intro exI[of _ 0] allI impI)
    fix n :: nat
    have "norm (?f n) = \<bar>x\<bar> ^ n / (2 * real n + 1)"
      by (simp add: mssnth_arctan_series_stream abs_mult power_abs)
    also have "\<dots> \<le> \<bar>x\<bar> ^ n / 1" by (intro divide_left_mono) auto
    finally show "norm (?f n) \<le> abs x ^ n" by simp
  qed
qed

lemma arctan_conv_pre_arctan:
  assumes "norm x < 1"
  shows   "arctan x = x * powser (msllist_of_msstream arctan_series_stream) (x ^ 2)"
proof -
  from assms have "norm x * norm x < 1 * 1" by (intro mult_strict_mono) auto
  hence norm_less: "norm (x ^ 2) < 1" by (simp add: power2_eq_square)
  have "(\<lambda>n. arctan_coeffs n * x ^ n) sums arctan x"
    by (intro arctan_converges assms)
  also have "?this \<longleftrightarrow> (\<lambda>n. arctan_coeffs (2 * n + 1) * x ^ (2 * n + 1)) sums arctan x"
    by (intro sums_mono_reindex [symmetric])
       (auto simp: arctan_coeffs_def strict_mono_def elim!: oddE)
  also have "(\<lambda>n. arctan_coeffs (2 * n + 1) * x ^ (2 * n + 1)) =
               (\<lambda>n. x * mssnth arctan_series_stream n * (x ^ 2) ^ n)"
    by (simp add: fun_eq_iff mssnth_arctan_series_stream 
                  power_mult [symmetric] arctan_coeffs_def mult_ac)
  finally have "(\<lambda>n. x * mssnth arctan_series_stream n * x\<^sup>2 ^ n) sums arctan x" .
  thus ?thesis using summable_pre_arctan[OF norm_less] assms
    by (simp add: powser_def sums_iff suminf_mult [symmetric] mult.assoc)
qed

lemma convergent_powser_arctan: 
  "convergent_powser (msllist_of_msstream arctan_series_stream)"
  unfolding convergent_powser_def
  using summable_pre_arctan by (intro exI[of _ 1]) auto

lemma arctan_inverse_pos: "x > 0 \<Longrightarrow> arctan x = pi / 2 - arctan (inverse x)"
  using arctan_inverse[of x] by (simp add: field_simps)
    
lemma arctan_inverse_neg: "x < 0 \<Longrightarrow> arctan x = -pi / 2 - arctan (inverse x)"
  using arctan_inverse[of x] by (simp add: field_simps)



subsection \<open>Multiseries\<close>

subsubsection \<open>Asymptotic bases\<close>

type_synonym basis = "(real \<Rightarrow> real) list"

lemma transp_ln_smallo_ln: "transp (\<lambda>f g. (\<lambda>x::real. ln (g x)) \<in> o(\<lambda>x. ln (f x)))"
  by (rule transpI, erule landau_o.small.trans)

definition basis_wf :: "basis \<Rightarrow> bool" where
  "basis_wf basis \<longleftrightarrow> (\<forall>f\<in>set basis. filterlim f at_top at_top) \<and> 
                      sorted_wrt (\<lambda>f g. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (f x))) basis"

lemma basis_wf_Nil [simp]: "basis_wf []"
  by (simp add: basis_wf_def)

lemma basis_wf_Cons: 
  "basis_wf (f # basis) \<longleftrightarrow> 
     filterlim f at_top at_top \<and> (\<forall>g\<in>set basis. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (f x))) \<and> basis_wf basis"
  unfolding basis_wf_def by auto

(* TODO: Move *)
lemma sorted_wrt_snoc:
  assumes trans: "transp P" and "sorted_wrt P xs" "P (last xs) y"
  shows   "sorted_wrt P (xs @ [y])"
proof (subst sorted_wrt_append, intro conjI ballI)
  fix x y' assume x: "x \<in> set xs" and y': "y' \<in> set [y]"
  from y' have [simp]: "y' = y" by simp
  show "P x y'"
  proof (cases "x = last xs")
    case False
    from x have eq: "xs = butlast xs @ [last xs]"
      by (subst append_butlast_last_id) auto
    from x and False have x': "x \<in> set (butlast xs)" by (subst (asm) eq) auto
    have "sorted_wrt P xs" by fact
    also note eq
    finally have "P x (last xs)" using x'
      by (subst (asm) sorted_wrt_append) auto
    with \<open>P (last xs) y\<close> have "P x y" using transpD[OF trans] by blast
    thus ?thesis by simp
  qed (insert assms, auto)
qed (insert assms, auto)  

lemma basis_wf_snoc:
  assumes "bs \<noteq> []"
  assumes "basis_wf bs" "filterlim b at_top at_top"
  assumes "(\<lambda>x. ln (b x)) \<in> o(\<lambda>x. ln (last bs x))"
  shows   "basis_wf (bs @ [b])"
proof -
  have "transp (\<lambda>f g. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (f x)))"
    by (auto simp: transp_def intro: landau_o.small.trans)
  thus ?thesis using assms
    by (auto simp add: basis_wf_def sorted_wrt_snoc[OF transp_ln_smallo_ln])
qed

lemma basis_wf_singleton: "basis_wf [b] \<longleftrightarrow> filterlim b at_top at_top"
  by (simp add: basis_wf_Cons)

lemma basis_wf_many: "basis_wf (b # b' # bs) \<longleftrightarrow>
  filterlim b at_top at_top \<and> (\<lambda>x. ln (b' x)) \<in> o(\<lambda>x. ln (b x)) \<and> basis_wf (b' # bs)"
  unfolding basis_wf_def by (subst sorted_wrt2[OF transp_ln_smallo_ln]) auto


subsubsection \<open>Monomials\<close>

type_synonym monom = "real \<times> real list"

definition eval_monom :: "monom \<Rightarrow> basis \<Rightarrow> real \<Rightarrow> real" where
  "eval_monom = (\<lambda>(c,es) basis x. c * prod_list (map (\<lambda>(b,e). b x powr e) (zip basis es)))"
  
lemma eval_monom_Nil1 [simp]: "eval_monom (c, []) basis = (\<lambda>_. c)"
  by (simp add: eval_monom_def split: prod.split)

lemma eval_monom_Nil2 [simp]: "eval_monom monom [] = (\<lambda>_. fst monom)"
  by (simp add: eval_monom_def split: prod.split)

lemma eval_monom_Cons: 
  "eval_monom (c, e # es) (b # basis) = (\<lambda>x. eval_monom (c, es) basis x * b x powr e)"
  by (simp add: eval_monom_def fun_eq_iff split: prod.split)

definition inverse_monom :: "monom \<Rightarrow> monom" where
  "inverse_monom monom = (case monom of (c, es) \<Rightarrow> (inverse c, map uminus es))"

lemma length_snd_inverse_monom [simp]: 
  "length (snd (inverse_monom monom)) = length (snd monom)"
  by (simp add: inverse_monom_def split: prod.split)

lemma eval_monom_pos:
  assumes "basis_wf basis" "fst monom > 0"
  shows   "eventually (\<lambda>x. eval_monom monom basis x > 0) at_top"
proof (cases monom)
  case (Pair c es)
  with assms have "c > 0" by simp
  with assms(1) show ?thesis unfolding Pair
  proof (induction es arbitrary: basis)
    case (Cons e es)
    note A = this
    thus ?case
    proof (cases basis)
      case (Cons b basis')
      with A(1)[of basis'] A(2,3) 
        have A: "\<forall>\<^sub>F x in at_top. eval_monom (c, es) basis' x > 0" 
         and B: "eventually (\<lambda>x. b x > 0) at_top"
        by (simp_all add: basis_wf_Cons filterlim_at_top_dense)
      thus ?thesis by eventually_elim (simp add: Cons eval_monom_Cons)
    qed simp
  qed simp
qed

lemma eval_monom_uminus: "eval_monom (-c, es) basis x = -eval_monom (c, es) basis x"
  by (simp add: eval_monom_def)

lemma eval_monom_neg:
  assumes "basis_wf basis" "fst monom < 0"
  shows   "eventually (\<lambda>x. eval_monom monom basis x < 0) at_top"    
proof -
  from assms have "eventually (\<lambda>x. eval_monom (-fst monom, snd monom) basis x > 0) at_top"
    by (intro eval_monom_pos) simp_all
  thus ?thesis by (simp add: eval_monom_uminus)
qed

lemma eval_monom_nonzero:
  assumes "basis_wf basis" "fst monom \<noteq> 0"
  shows   "eventually (\<lambda>x. eval_monom monom basis x \<noteq> 0) at_top"
proof (cases "fst monom" "0 :: real" rule: linorder_cases)
  case greater
  with assms have "eventually (\<lambda>x. eval_monom monom basis x > 0) at_top"
    by (simp add: eval_monom_pos)
  thus ?thesis by eventually_elim simp
next
  case less
  with assms have "eventually (\<lambda>x. eval_monom (-fst monom, snd monom) basis x > 0) at_top"
    by (simp add: eval_monom_pos)
  thus ?thesis by eventually_elim (simp add: eval_monom_uminus)
qed (insert assms, simp_all)


subsubsection \<open>Typeclass for multiseries\<close>

class multiseries = plus + minus + times + uminus + inverse + 
  fixes is_expansion :: "'a \<Rightarrow> basis \<Rightarrow> bool"
    and expansion_level :: "'a itself \<Rightarrow> nat"
    and eval :: "'a \<Rightarrow> real \<Rightarrow> real"
    and zero_expansion :: 'a
    and const_expansion :: "real \<Rightarrow> 'a"
    and powr_expansion :: "bool \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
    and power_expansion :: "bool \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
    and trimmed :: "'a \<Rightarrow> bool"
    and dominant_term :: "'a \<Rightarrow> monom"

  assumes is_expansion_length:
    "is_expansion F basis \<Longrightarrow> length basis = expansion_level (TYPE('a))"
  assumes is_expansion_zero:
    "basis_wf basis \<Longrightarrow> length basis = expansion_level (TYPE('a)) \<Longrightarrow> 
       is_expansion zero_expansion basis"
  assumes is_expansion_const:
    "basis_wf basis \<Longrightarrow> length basis = expansion_level (TYPE('a)) \<Longrightarrow> 
       is_expansion (const_expansion c) basis"
  assumes is_expansion_uminus:
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> is_expansion (-F) basis"
  assumes is_expansion_add: 
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> is_expansion G basis \<Longrightarrow> 
       is_expansion (F + G) basis"
  assumes is_expansion_minus: 
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> is_expansion G basis \<Longrightarrow> 
       is_expansion (F - G) basis"
  assumes is_expansion_mult: 
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> is_expansion G basis \<Longrightarrow> 
       is_expansion (F * G) basis"
  assumes is_expansion_inverse:
    "basis_wf basis \<Longrightarrow> trimmed F \<Longrightarrow> is_expansion F basis \<Longrightarrow> 
       is_expansion (inverse F) basis"
  assumes is_expansion_divide:
    "basis_wf basis \<Longrightarrow> trimmed G \<Longrightarrow> is_expansion F basis \<Longrightarrow> is_expansion G basis \<Longrightarrow> 
       is_expansion (F / G) basis"
  assumes is_expansion_powr:
    "basis_wf basis \<Longrightarrow> trimmed F \<Longrightarrow> fst (dominant_term F) > 0 \<Longrightarrow> is_expansion F basis \<Longrightarrow>
       is_expansion (powr_expansion abort F p) basis"
  assumes is_expansion_power:
    "basis_wf basis \<Longrightarrow> trimmed F \<Longrightarrow> is_expansion F basis \<Longrightarrow>
       is_expansion (power_expansion abort F n) basis"
  
  assumes is_expansion_imp_smallo:
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> filterlim b at_top at_top \<Longrightarrow>
       (\<forall>g\<in>set basis. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (b x))) \<Longrightarrow> e > 0 \<Longrightarrow> eval F \<in> o(\<lambda>x. b x powr e)"
  assumes is_expansion_imp_smallomega:
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> filterlim b at_top at_top \<Longrightarrow> trimmed F \<Longrightarrow> 
       (\<forall>g\<in>set basis. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (b x))) \<Longrightarrow> e < 0 \<Longrightarrow> eval F \<in> \<omega>(\<lambda>x. b x powr e)"
  assumes trimmed_imp_eventually_sgn:
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> trimmed F \<Longrightarrow>
       eventually (\<lambda>x. sgn (eval F x) = sgn (fst (dominant_term F))) at_top"
  assumes trimmed_imp_eventually_nz: 
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> trimmed F \<Longrightarrow> 
       eventually (\<lambda>x. eval F x \<noteq> 0) at_top"
  assumes trimmed_imp_dominant_term_nz: "trimmed F \<Longrightarrow> fst (dominant_term F) \<noteq> 0"
  
  assumes dominant_term: 
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow> trimmed F \<Longrightarrow>
       eval F \<sim>[at_top] eval_monom (dominant_term F) basis"
  assumes dominant_term_bigo:
    "basis_wf basis \<Longrightarrow> is_expansion F basis \<Longrightarrow>
       eval F \<in> O(eval_monom (1, snd (dominant_term F)) basis)"
  assumes length_dominant_term:
    "length (snd (dominant_term F)) = expansion_level TYPE('a)"
  assumes fst_dominant_term_uminus [simp]: "fst (dominant_term (- F)) = -fst (dominant_term F)"
  assumes trimmed_uminus_iff [simp]: "trimmed (-F) \<longleftrightarrow> trimmed F"
  
  assumes add_zero_expansion_left [simp]: "zero_expansion + F = F"
  assumes add_zero_expansion_right [simp]: "F + zero_expansion = F"
  
  assumes eval_zero [simp]: "eval zero_expansion x = 0"
  assumes eval_const [simp]: "eval (const_expansion c) x = c"
  assumes eval_uminus [simp]: "eval (-F) = (\<lambda>x. -eval F x)"
  assumes eval_plus [simp]: "eval (F + G) = (\<lambda>x. eval F x + eval G x)"
  assumes eval_minus [simp]: "eval (F - G) = (\<lambda>x. eval F x - eval G x)"
  assumes eval_times [simp]: "eval (F * G) = (\<lambda>x. eval F x * eval G x)"
  assumes eval_inverse [simp]: "eval (inverse F) = (\<lambda>x. inverse (eval F x))"
  assumes eval_divide [simp]: "eval (F / G) = (\<lambda>x. eval F x / eval G x)"
  assumes eval_powr [simp]: "eval (powr_expansion abort F p) = (\<lambda>x. eval F x powr p)"
  assumes eval_power [simp]: "eval (power_expansion abort F n) = (\<lambda>x. eval F x ^ n)"
  assumes minus_eq_plus_uminus: "F - G = F + (-G)"
  assumes times_const_expansion_1: "const_expansion 1 * F = F"
  assumes trimmed_const_expansion: "trimmed (const_expansion c) \<longleftrightarrow> c \<noteq> 0"
begin

definition trimmed_pos where
  "trimmed_pos F \<longleftrightarrow> trimmed F \<and> fst (dominant_term F) > 0"

definition trimmed_neg where
  "trimmed_neg F \<longleftrightarrow> trimmed F \<and> fst (dominant_term F) < 0"

lemma trimmed_pos_uminus: "trimmed_neg F \<Longrightarrow> trimmed_pos (-F)"
  by (simp add: trimmed_neg_def trimmed_pos_def)

lemma trimmed_pos_imp_trimmed: "trimmed_pos x \<Longrightarrow> trimmed x"
  by (simp add: trimmed_pos_def)

lemma trimmed_neg_imp_trimmed: "trimmed_neg x \<Longrightarrow> trimmed x"
  by (simp add: trimmed_neg_def)

end


subsubsection \<open>Zero-rank expansions\<close>

instantiation real :: multiseries
begin

inductive is_expansion_real :: "real \<Rightarrow> basis \<Rightarrow> bool" where
  "is_expansion_real c []"
  
definition expansion_level_real :: "real itself \<Rightarrow> nat" where
  expansion_level_real_def [simp]: "expansion_level_real _ = 0"

definition eval_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  eval_real_def [simp]: "eval_real c = (\<lambda>_. c)"

definition zero_expansion_real :: "real" where
  zero_expansion_real_def [simp]: "zero_expansion_real = 0"
  
definition const_expansion_real :: "real \<Rightarrow> real" where
  const_expansion_real_def [simp]: "const_expansion_real x = x"

definition powr_expansion_real :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  powr_expansion_real_def [simp]: "powr_expansion_real _ x p = x powr p"

definition power_expansion_real :: "bool \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  power_expansion_real_def [simp]: "power_expansion_real _ x n = x ^ n"

definition trimmed_real :: "real \<Rightarrow> bool" where
  trimmed_real_def [simp]: "trimmed_real x \<longleftrightarrow> x \<noteq> 0"

definition dominant_term_real :: "real \<Rightarrow> monom" where
  dominant_term_real_def [simp]: "dominant_term_real c = (c, [])"

instance proof
  fix basis :: basis and b :: "real \<Rightarrow> real" and e F :: real
  assume *: "basis_wf basis" "filterlim b at_top at_top" "is_expansion F basis" "0 < e"
  have "(\<lambda>x. b x powr e) \<in> \<omega>(\<lambda>_. 1)"
    by (intro smallomegaI_filterlim_at_infinity filterlim_at_top_imp_at_infinity) 
       (auto intro!: filterlim_compose[OF real_powr_at_top] * )
  with * show "eval F \<in> o(\<lambda>x. b x powr e)"
    by (cases "F = 0") (auto elim!: is_expansion_real.cases simp: smallomega_iff_smallo)
next
  fix basis :: basis and b :: "real \<Rightarrow> real" and e F :: real
  assume *: "basis_wf basis" "filterlim b at_top at_top" "is_expansion F basis" 
            "e < 0" "trimmed F"
  from * have pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  have "(\<lambda>x. b x powr -e) \<in> \<omega>(\<lambda>_. 1)"
    by (intro smallomegaI_filterlim_at_infinity filterlim_at_top_imp_at_infinity) 
       (auto intro!: filterlim_compose[OF real_powr_at_top] * )
  with pos have "(\<lambda>x. b x powr e) \<in> o(\<lambda>_. 1)" unfolding powr_minus
    by (subst (asm) landau_omega.small.inverse_eq2)
       (auto elim: eventually_mono simp: smallomega_iff_smallo)
  with * show "eval F \<in> \<omega>(\<lambda>x. b x powr e)"
    by (auto elim!: is_expansion_real.cases simp: smallomega_iff_smallo)
qed (auto intro!: is_expansion_real.intros elim!: is_expansion_real.cases)

end

lemma eval_real: "eval (c :: real) x = c" by simp


subsubsection \<open>Operations on multiseries\<close>

lemma ms_aux_cases [case_names MSLNil MSLCons]:
  fixes xs :: "('a \<times> real) msllist"
  obtains "xs = MSLNil" | c e xs' where "xs = MSLCons (c, e) xs'"
proof (cases xs)
  case (MSLCons x xs')
  with that(2)[of "fst x" "snd x" xs'] show ?thesis by auto
qed auto

definition ms_aux_hd_exp :: "('a \<times> real) msllist \<Rightarrow> real option" where
  "ms_aux_hd_exp xs = (case xs of MSLNil \<Rightarrow> None | MSLCons (_, e) _ \<Rightarrow> Some e)"

primrec ms_exp_gt :: "real \<Rightarrow> real option \<Rightarrow> bool" where
  "ms_exp_gt x None = True"
| "ms_exp_gt x (Some y) \<longleftrightarrow> x > y"

lemma ms_aux_hd_exp_MSLNil [simp]: "ms_aux_hd_exp MSLNil = None"
  by (simp add: ms_aux_hd_exp_def split: prod.split)
  
lemma ms_aux_hd_exp_MSLCons [simp]: "ms_aux_hd_exp (MSLCons x xs) = Some (snd x)"
  by (simp add: ms_aux_hd_exp_def split: prod.split)

coinductive is_expansion_aux :: 
    "('a :: multiseries \<times> real) msllist \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> basis \<Rightarrow> bool" where
  is_expansion_MSLNil: 
    "eventually (\<lambda>x. f x = 0) at_top \<Longrightarrow> length basis = Suc (expansion_level TYPE('a)) \<Longrightarrow>
       is_expansion_aux MSLNil f basis"
| is_expansion_MSLCons: 
    "is_expansion_aux xs (\<lambda>x. f x - eval C x * b x powr e) (b # basis) \<Longrightarrow>
       is_expansion C basis \<Longrightarrow>
       (\<And>e'. e' > e \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')) \<Longrightarrow> ms_exp_gt e (ms_aux_hd_exp xs) \<Longrightarrow>
       is_expansion_aux (MSLCons (C, e) xs) f (b # basis)"

inductive_cases is_expansion_aux_MSLCons: "is_expansion_aux (MSLCons (c, e) xs) f basis"
 
lemma is_expansion_aux_basis_nonempty: "is_expansion_aux F f basis \<Longrightarrow> basis \<noteq> []"
  by (erule is_expansion_aux.cases) auto

lemma is_expansion_aux_expansion_level:
  assumes "is_expansion_aux (G :: ('a::multiseries \<times> real) msllist) g basis"
  shows   "length basis = Suc (expansion_level TYPE('a))"
  using assms by (cases rule: is_expansion_aux.cases) (auto dest: is_expansion_length)  

lemma is_expansion_aux_imp_smallo:
  assumes "is_expansion_aux xs f basis" "ms_exp_gt p (ms_aux_hd_exp xs)" 
  shows   "f \<in> o(\<lambda>x. hd basis x powr p)"
  using assms
proof (cases rule: is_expansion_aux.cases)
  case is_expansion_MSLNil
  show ?thesis by (simp add: landau_o.small.in_cong[OF is_expansion_MSLNil(2)])
next
  case (is_expansion_MSLCons xs C b e basis)
  with assms have "f \<in> o(\<lambda>x. b x powr p)"
    by (intro is_expansion_MSLCons) (simp_all add: ms_aux_hd_exp_def)
  thus ?thesis by (simp add: is_expansion_MSLCons)
qed

lemma is_expansion_aux_imp_smallo':
  assumes "is_expansion_aux xs f basis"
  obtains e where "f \<in> o(\<lambda>x. hd basis x powr e)"
proof -
  define e where "e = (case ms_aux_hd_exp xs of None \<Rightarrow> 0 | Some e \<Rightarrow> e + 1)"
  have "ms_exp_gt e (ms_aux_hd_exp xs)"
    by (auto simp add: e_def ms_aux_hd_exp_def split: msllist.splits)
  from assms this have "f \<in> o(\<lambda>x. hd basis x powr e)" by (rule is_expansion_aux_imp_smallo)
  from that[OF this] show ?thesis .
qed

lemma is_expansion_aux_imp_smallo'':
  assumes "is_expansion_aux xs f basis" "ms_exp_gt e' (ms_aux_hd_exp xs)"
  obtains e where "e < e'" "f \<in> o(\<lambda>x. hd basis x powr e)"
proof -
  define e where "e = (case ms_aux_hd_exp xs of None \<Rightarrow> e' - 1 | Some e \<Rightarrow> (e' + e) / 2)"
  from assms have "ms_exp_gt e (ms_aux_hd_exp xs)" "e < e'"
    by (cases xs; simp add: e_def field_simps)+
  from assms(1) this(1) have "f \<in> o(\<lambda>x. hd basis x powr e)" by (rule is_expansion_aux_imp_smallo)
  from that[OF \<open>e < e'\<close> this] show ?thesis .
qed

definition trimmed_ms_aux :: "('a :: multiseries \<times> real) msllist \<Rightarrow> bool" where
  "trimmed_ms_aux xs = (case xs of MSLNil \<Rightarrow> False | MSLCons (C, _) _ \<Rightarrow> trimmed C)"
 
lemma not_trimmed_ms_aux_MSLNil [simp]: "\<not>trimmed_ms_aux MSLNil"
  by (simp add: trimmed_ms_aux_def)

lemma trimmed_ms_aux_MSLCons: "trimmed_ms_aux (MSLCons x xs) = trimmed (fst x)"
  by (simp add: trimmed_ms_aux_def split: prod.split)

lemma trimmed_ms_aux_imp_nz:
  assumes "basis_wf basis" "is_expansion_aux xs f basis" "trimmed_ms_aux xs"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) at_top"
proof (cases xs rule: ms_aux_cases)
  case (MSLCons C e xs')
  from assms this obtain b basis' where *: "basis = b # basis'"
    "is_expansion_aux xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')" 
    "ms_exp_gt e (ms_aux_hd_exp xs')" "is_expansion C basis'" "\<And>e'. e' > e \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')"
    by (auto elim!: is_expansion_aux_MSLCons)
  from assms(1,3) * have nz: "eventually (\<lambda>x. eval C x \<noteq> 0) at_top"
    by (auto simp: trimmed_ms_aux_def MSLCons basis_wf_Cons
             intro: trimmed_imp_eventually_nz[of basis'])
  from assms(1) * have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_nz: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  
  from is_expansion_aux_imp_smallo''[OF *(2,3)]
  obtain e' where e': "e' < e" "(\<lambda>x. f x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr e')"
    unfolding list.sel by blast
  note this(2)
  also have "\<dots> = o(\<lambda>x. b x powr (e' - e) * b x powr e)" by (simp add: powr_add [symmetric])
  also from assms * e' have "eval C \<in> \<omega>(\<lambda>x. b x powr (e' - e))"
    by (intro is_expansion_imp_smallomega[OF _ *(4)])
       (simp_all add: MSLCons basis_wf_Cons trimmed_ms_aux_def)
  hence "(\<lambda>x. b x powr (e' - e) * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)"
    by (intro landau_o.small_big_mult is_expansion_imp_smallomega) 
       (simp_all add: smallomega_iff_smallo)
  finally have "(\<lambda>x. f x - eval C x * b x powr e + eval C x * b x powr e) \<in> 
                  \<Theta>(\<lambda>x. eval C x * b x powr e)"
    by (subst bigtheta_sym, subst landau_theta.plus_absorb1) simp_all
  hence theta: "f \<in> \<Theta>(\<lambda>x. eval C x * b x powr e)" by simp
  have "eventually (\<lambda>x. eval C x * b x powr e \<noteq> 0) at_top"
    using b_nz nz by eventually_elim simp
  thus ?thesis by (subst eventually_nonzero_bigtheta [OF theta])
qed (insert assms, simp_all add: trimmed_ms_aux_def)

lemma is_expansion_aux_imp_smallomega:
  assumes "basis_wf basis" "is_expansion_aux xs f basis" "filterlim b' at_top at_top"
          "trimmed_ms_aux xs" "\<forall>g\<in>set basis. (\<lambda>x. ln (g x)) \<in> o(\<lambda>x. ln (b' x))" "r < 0"
  shows   "f \<in> \<omega>(\<lambda>x. b' x powr r)"
proof (cases xs rule: ms_aux_cases)
  case (MSLCons C e xs')
  from assms this obtain b basis' where *: "basis = b # basis'" "trimmed C"
    "is_expansion_aux xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "ms_exp_gt e (ms_aux_hd_exp xs')"
    "is_expansion C basis'" "\<And>e'. e' > e \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')"
    by (auto elim!: is_expansion_aux_MSLCons simp: trimmed_ms_aux_def)
  from assms * have nz: "eventually (\<lambda>x. eval C x \<noteq> 0) at_top"
    by (intro trimmed_imp_eventually_nz[of basis']) (simp_all add: basis_wf_Cons)
  from assms(1) * have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_nz: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  
  from is_expansion_aux_imp_smallo''[OF *(3,4)]
  obtain e' where e': "e' < e" "(\<lambda>x. f x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr e')"
    unfolding list.sel by blast
  note this(2)
  also have "\<dots> = o(\<lambda>x. b x powr (e' - e) * b x powr e)" by (simp add: powr_add [symmetric])
  also from assms * e' have "eval C \<in> \<omega>(\<lambda>x. b x powr (e' - e))"
    by (intro is_expansion_imp_smallomega[OF _ *(5)])
       (simp_all add: MSLCons basis_wf_Cons trimmed_ms_aux_def)
  hence "(\<lambda>x. b x powr (e' - e) * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)"
    by (intro landau_o.small_big_mult is_expansion_imp_smallomega) 
       (simp_all add: smallomega_iff_smallo)
  finally have "(\<lambda>x. f x - eval C x * b x powr e + eval C x * b x powr e) \<in> 
                  \<Theta>(\<lambda>x. eval C x * b x powr e)"
    by (subst bigtheta_sym, subst landau_theta.plus_absorb1) simp_all
  hence theta: "f \<in> \<Theta>(\<lambda>x. eval C x * b x powr e)" by simp
  also from * assms e' have "(\<lambda>x. eval C x * b x powr e) \<in> \<omega>(\<lambda>x. b x powr (e' - e) * b x powr e)"
    by (intro landau_omega.small_big_mult is_expansion_imp_smallomega[of basis'])
       (simp_all add: basis_wf_Cons)
  also have "\<dots> = \<omega>(\<lambda>x. b x powr e')" by (simp add: powr_add [symmetric])
  also from *(1) assms have "(\<lambda>x. b x powr e') \<in> \<omega>(\<lambda>x. b' x powr r)"
    unfolding smallomega_iff_smallo by (intro ln_smallo_imp_flat') (simp_all add: basis_wf_Cons)
  finally show ?thesis .
qed (insert assms, simp_all add: trimmed_ms_aux_def)  

definition dominant_term_ms_aux :: "('a :: multiseries \<times> real) msllist \<Rightarrow> monom" where
  "dominant_term_ms_aux xs =
     (case xs of MSLNil \<Rightarrow> (0, replicate (Suc (expansion_level TYPE('a))) 0)
               | MSLCons (C, e) _ \<Rightarrow> case dominant_term C of (c, es) \<Rightarrow> (c, e # es))"

lemma dominant_term_ms_aux_MSLCons: 
  "dominant_term_ms_aux (MSLCons (C, e) xs) = map_prod id (\<lambda>es. e # es) (dominant_term C)"
  by (simp add: dominant_term_ms_aux_def case_prod_unfold map_prod_def)

lemma length_dominant_term_ms_aux [simp]:
  "length (snd (dominant_term_ms_aux (xs :: ('a :: multiseries \<times> real) msllist))) = 
     Suc (expansion_level TYPE('a))"
proof (cases xs rule: ms_aux_cases)
  case (MSLCons C e xs')
  hence "length (snd (dominant_term_ms_aux xs)) = Suc (length (snd (dominant_term C)))"
    by (simp add: dominant_term_ms_aux_def split: prod.splits)
  also note length_dominant_term
  finally show ?thesis .
qed (simp_all add: dominant_term_ms_aux_def split: msllist.splits prod.splits)

definition const_ms_aux :: "real \<Rightarrow> ('a :: multiseries \<times> real) msllist" where
  "const_ms_aux c = MSLCons (const_expansion c, 0) MSLNil"

definition uminus_ms_aux :: "('a :: uminus \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "uminus_ms_aux xs = mslmap (map_prod uminus id) xs"
  
corec (friend) plus_ms_aux :: "('a :: plus \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "plus_ms_aux xs ys =
     (case (xs, ys) of
        (MSLNil, MSLNil) \<Rightarrow> MSLNil
      | (MSLNil, MSLCons y ys) \<Rightarrow> MSLCons y ys
      | (MSLCons x xs, MSLNil) \<Rightarrow> MSLCons x xs
      | (MSLCons x xs, MSLCons y ys) \<Rightarrow>
          if snd x > snd y then MSLCons x (plus_ms_aux xs (MSLCons y ys))
          else if snd x < snd y then MSLCons y (plus_ms_aux (MSLCons x xs) ys)
          else MSLCons (fst x + fst y, snd x) (plus_ms_aux xs ys))"

context
begin

friend_of_corec mslmap where
  "mslmap (f :: 'a \<Rightarrow> 'a) xs = 
     (case xs of MSLNil \<Rightarrow> MSLNil | MSLCons x xs \<Rightarrow> MSLCons (f x) (mslmap f xs))"
   by (simp split: msllist.splits, transfer_prover)

corec (friend) times_ms_aux
     :: "('a :: {plus,times} \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "times_ms_aux xs ys =
     (case (xs, ys) of
        (MSLNil, ys) \<Rightarrow> MSLNil
      | (xs, MSLNil) \<Rightarrow> MSLNil
      | (MSLCons x xs, MSLCons y ys) \<Rightarrow>
           MSLCons (fst x * fst y, snd x + snd y) 
             (plus_ms_aux (mslmap (map_prod ((*) (fst x)) ((+) (snd x))) ys)
               (times_ms_aux xs (MSLCons y ys))))"

definition scale_shift_ms_aux :: "('a :: times \<times> real) \<Rightarrow> ('a \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "scale_shift_ms_aux = (\<lambda>(a,b) xs. mslmap (map_prod ((*) a) ((+) b)) xs)"

lemma times_ms_aux_altdef:
  "times_ms_aux xs ys = 
     (case (xs, ys) of
        (MSLNil, ys) \<Rightarrow> MSLNil
      | (xs, MSLNil) \<Rightarrow> MSLNil
      | (MSLCons x xs, MSLCons y ys) \<Rightarrow>
          MSLCons (fst x * fst y, snd x + snd y)
            (plus_ms_aux (scale_shift_ms_aux x ys) (times_ms_aux xs (MSLCons y ys))))"
  by (subst times_ms_aux.code) (simp_all add: scale_shift_ms_aux_def split: msllist.splits)
end

corec powser_ms_aux :: "real msllist \<Rightarrow> ('a :: multiseries \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "powser_ms_aux cs xs = (case cs of MSLNil \<Rightarrow> MSLNil | MSLCons c cs \<Rightarrow>
     MSLCons (const_expansion c, 0) (times_ms_aux xs (powser_ms_aux cs xs)))"
  
definition minus_ms_aux :: "('a :: multiseries \<times> real) msllist \<Rightarrow> _" where
  "minus_ms_aux xs ys = plus_ms_aux xs (uminus_ms_aux ys)"

lemma is_expansion_aux_coinduct [consumes 1, case_names is_expansion_aux]:
  fixes xs :: "('a :: multiseries \<times> real) msllist"
  assumes "X xs f basis" "(\<And>xs f basis. X xs f basis \<Longrightarrow> 
     (xs = MSLNil \<and> (\<forall>\<^sub>F x in at_top. f x = 0) \<and> length basis = Suc (expansion_level TYPE('a))) \<or>
     (\<exists>xs' b e basis' C. xs = MSLCons (C, e) xs' \<and> basis = b # basis' \<and>
        (X xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')) \<and> is_expansion C basis' \<and>
        (\<forall>x>e. f \<in> o(\<lambda>xa. b xa powr x)) \<and> ms_exp_gt e (ms_aux_hd_exp xs')))"
  shows "is_expansion_aux xs f basis"
using assms(1)
proof (coinduction arbitrary: xs f)
  case (is_expansion_aux xs f)
  from assms(2)[OF is_expansion_aux] show ?case by blast
qed 

lemma is_expansion_aux_cong:
  assumes "is_expansion_aux F f basis"
  assumes "eventually (\<lambda>x. f x = g x) at_top"
  shows   "is_expansion_aux F g basis"
  using assms
proof (coinduction arbitrary: F f g rule: is_expansion_aux_coinduct)
  case (is_expansion_aux F f g)
  from this have ev: "eventually (\<lambda>x. g x = f x) at_top" by (simp add: eq_commute)
  from ev have [simp]: "eventually (\<lambda>x. g x = 0) at_top \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
    by (rule eventually_subst')
  from ev have [simp]: "(\<forall>\<^sub>F x in at_top. h x = g x - h' x) \<longleftrightarrow>
                          (\<forall>\<^sub>F x in at_top. h x = f x - h' x)" for h h'
      by (rule eventually_subst')
  note [simp] = landau_o.small.in_cong[OF ev]
  from is_expansion_aux(1) show ?case
    by (cases rule: is_expansion_aux.cases) force+  
qed

lemma scale_shift_ms_aux_conv_mslmap: 
  "scale_shift_ms_aux x = mslmap (map_prod ((*) (fst x)) ((+) (snd x)))"
  by (rule ext) (simp add: scale_shift_ms_aux_def map_prod_def case_prod_unfold)

fun inverse_ms_aux :: "('a :: multiseries \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "inverse_ms_aux (MSLCons x xs) = 
     (let c' = inverse (fst x)
      in  scale_shift_ms_aux (c', -snd x) 
            (powser_ms_aux (msllist_of_msstream (mssalternate 1 (-1)))
              (scale_shift_ms_aux (c', -snd x) xs)))"

(* TODO: Move? *)
lemma inverse_prod_list: "inverse (prod_list xs :: 'a :: field) = prod_list (map inverse xs)"
  by (induction xs) simp_all

lemma eval_inverse_monom: 
  "eval_monom (inverse_monom monom) basis = (\<lambda>x. inverse (eval_monom monom basis x))"
  by (rule ext) (simp add: eval_monom_def inverse_monom_def zip_map2 o_def case_prod_unfold
                   inverse_prod_list powr_minus)

fun powr_ms_aux :: "bool \<Rightarrow> ('a :: multiseries \<times> real) msllist \<Rightarrow> real \<Rightarrow> ('a \<times> real) msllist" where
  "powr_ms_aux abort (MSLCons x xs) p = 
      scale_shift_ms_aux (powr_expansion abort (fst x) p, snd x * p)
        (powser_ms_aux (gbinomial_series abort p)
          (scale_shift_ms_aux (inverse (fst x), -snd x) xs))"

fun power_ms_aux :: "bool \<Rightarrow> ('a :: multiseries \<times> real) msllist \<Rightarrow> nat \<Rightarrow> ('a \<times> real) msllist" where
  "power_ms_aux abort (MSLCons x xs) n = 
      scale_shift_ms_aux (power_expansion abort (fst x) n, snd x * real n)
        (powser_ms_aux (gbinomial_series abort (real n))
          (scale_shift_ms_aux (inverse (fst x), -snd x) xs))"

definition sin_ms_aux' :: "('a :: multiseries \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "sin_ms_aux' xs = times_ms_aux xs (powser_ms_aux (msllist_of_msstream sin_series_stream)
                      (times_ms_aux xs xs))"
  
definition cos_ms_aux' :: "('a :: multiseries \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "cos_ms_aux' xs = powser_ms_aux (msllist_of_msstream cos_series_stream) (times_ms_aux xs xs)"

subsubsection \<open>Basic properties of multiseries operations\<close>  

lemma uminus_ms_aux_MSLNil [simp]: "uminus_ms_aux MSLNil = MSLNil"
  by (simp add: uminus_ms_aux_def)
  
lemma uminus_ms_aux_MSLCons: "uminus_ms_aux (MSLCons x xs) = MSLCons (-fst x, snd x) (uminus_ms_aux xs)"
  by (simp add: uminus_ms_aux_def map_prod_def split: prod.splits)

lemma uminus_ms_aux_MSLNil_iff [simp]: "uminus_ms_aux xs = MSLNil \<longleftrightarrow> xs = MSLNil"
  by (simp add: uminus_ms_aux_def)
  
lemma hd_exp_uminus [simp]: "ms_aux_hd_exp (uminus_ms_aux xs) = ms_aux_hd_exp xs"
  by (simp add: uminus_ms_aux_def ms_aux_hd_exp_def split: msllist.splits prod.split)
  
lemma scale_shift_ms_aux_MSLNil_iff [simp]: "scale_shift_ms_aux x F = MSLNil \<longleftrightarrow> F = MSLNil"
  by (auto simp: scale_shift_ms_aux_def split: prod.split)

lemma scale_shift_ms_aux_MSLNil [simp]: "scale_shift_ms_aux x MSLNil = MSLNil"
  by (simp add: scale_shift_ms_aux_def split: prod.split)

lemma scale_shift_ms_aux_1 [simp]:
  "scale_shift_ms_aux (1 :: real, 0) xs = xs"
  by (simp add: scale_shift_ms_aux_def map_prod_def msllist.map_id)

lemma scale_shift_ms_aux_MSLCons: 
  "scale_shift_ms_aux x (MSLCons y F) = MSLCons (fst x * fst y, snd x + snd y) (scale_shift_ms_aux x F)"
  by (auto simp: scale_shift_ms_aux_def map_prod_def split: prod.split)

lemma hd_exp_basis:
  "ms_aux_hd_exp (scale_shift_ms_aux x xs) = map_option ((+) (snd x)) (ms_aux_hd_exp xs)"
  by (auto simp: ms_aux_hd_exp_def scale_shift_ms_aux_MSLCons split: msllist.split)

lemma plus_ms_aux_MSLNil_iff: "plus_ms_aux F G = MSLNil \<longleftrightarrow> F = MSLNil \<and> G = MSLNil"
  by (subst plus_ms_aux.code) (simp split: msllist.splits)

lemma plus_ms_aux_MSLNil [simp]: "plus_ms_aux F MSLNil = F" "plus_ms_aux MSLNil G = G"
  by (subst plus_ms_aux.code, simp split: msllist.splits)+

lemma plus_ms_aux_MSLCons: 
  "plus_ms_aux (MSLCons x xs) (MSLCons y ys) = 
     (if snd x > snd y then MSLCons x (plus_ms_aux xs (MSLCons y ys))
      else if snd x < snd y then MSLCons y (plus_ms_aux (MSLCons x xs) ys)
      else MSLCons (fst x + fst y, snd x) (plus_ms_aux xs ys))"
  by (subst plus_ms_aux.code) simp

lemma hd_exp_plus:
  "ms_aux_hd_exp (plus_ms_aux xs ys) = combine_options max (ms_aux_hd_exp xs) (ms_aux_hd_exp ys)"
  by (cases xs; cases ys)
     (simp_all add: plus_ms_aux_MSLCons ms_aux_hd_exp_def max_def split: prod.split)

lemma minus_ms_aux_MSLNil_left [simp]: "minus_ms_aux MSLNil ys = uminus_ms_aux ys"
  by (simp add: minus_ms_aux_def)

lemma minus_ms_aux_MSLNil_right [simp]: "minus_ms_aux xs MSLNil = xs"
  by (simp add: minus_ms_aux_def)

lemma times_ms_aux_MSLNil_iff: "times_ms_aux F G = MSLNil \<longleftrightarrow> F = MSLNil \<or> G = MSLNil"
  by (subst times_ms_aux.code) (simp split: msllist.splits)

lemma times_ms_aux_MSLNil [simp]: "times_ms_aux MSLNil G = MSLNil" "times_ms_aux F MSLNil = MSLNil"
  by (subst times_ms_aux.code, simp split: msllist.splits)+

lemma times_ms_aux_MSLCons: "times_ms_aux (MSLCons x xs) (MSLCons y ys) = 
  MSLCons (fst x * fst y, snd x + snd y) (plus_ms_aux (scale_shift_ms_aux x ys)
       (times_ms_aux xs (MSLCons y ys)))"
  by (subst times_ms_aux_altdef) simp

lemma hd_exp_times:
  "ms_aux_hd_exp (times_ms_aux xs ys) = 
     (case (ms_aux_hd_exp xs, ms_aux_hd_exp ys) of (Some x, Some y) \<Rightarrow> Some (x + y) | _ \<Rightarrow> None)"
  by (cases xs; cases ys) (simp_all add: times_ms_aux_MSLCons ms_aux_hd_exp_def split: prod.split)


subsubsection \<open>Induction upto friends for multiseries\<close>

inductive ms_closure :: 
  "(('a :: multiseries \<times> real) msllist \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> basis \<Rightarrow> bool) \<Rightarrow>
   ('a :: multiseries \<times> real) msllist \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> basis \<Rightarrow> bool" for P where
  ms_closure_embed: 
    "P xs f basis \<Longrightarrow> ms_closure P xs f basis"
| ms_closure_cong: 
    "ms_closure P xs f basis \<Longrightarrow> eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> ms_closure P xs g basis"
| ms_closure_MSLCons:
    "ms_closure P xs (\<lambda>x. f x - eval C x * b x powr e) (b # basis) \<Longrightarrow>
       is_expansion C basis \<Longrightarrow> (\<And>e'. e' > e \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')) \<Longrightarrow>
       ms_exp_gt e (ms_aux_hd_exp xs) \<Longrightarrow>
       ms_closure P (MSLCons (C, e) xs) f (b # basis)"
| ms_closure_add: 
    "ms_closure P xs f basis \<Longrightarrow> ms_closure P ys g basis \<Longrightarrow> 
       ms_closure P (plus_ms_aux xs ys) (\<lambda>x. f x + g x) basis"
| ms_closure_mult: 
    "ms_closure P xs f basis \<Longrightarrow> ms_closure P ys g basis \<Longrightarrow> 
       ms_closure P (times_ms_aux xs ys) (\<lambda>x. f x * g x) basis"
| ms_closure_basis: 
    "ms_closure P xs f (b # basis) \<Longrightarrow> is_expansion C basis \<Longrightarrow>
       ms_closure P (scale_shift_ms_aux (C,e) xs) (\<lambda>x. eval C x * b x powr e * f x) (b # basis)"
 | ms_closure_embed':
    "is_expansion_aux xs f basis \<Longrightarrow> ms_closure P xs f basis"

lemma is_expansion_aux_coinduct_upto [consumes 2, case_names A B]:
  fixes xs :: "('a :: multiseries \<times> real) msllist"
  assumes *: "X xs f basis" and basis: "basis_wf basis"
  and step: "\<And>xs f basis. X xs f basis \<Longrightarrow> 
    (xs = MSLNil \<and> eventually (\<lambda>x. f x = 0) at_top \<and> length basis = Suc (expansion_level TYPE('a))) \<or>
    (\<exists>xs' b e basis' C. xs = MSLCons (C, e) xs' \<and> basis = b # basis' \<and>
       ms_closure X xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis') \<and>
       is_expansion C basis' \<and> (\<forall>e'>e. f \<in> o(\<lambda>x. b x powr e')) \<and> ms_exp_gt e (ms_aux_hd_exp xs'))"
  shows "is_expansion_aux xs f basis"
proof -
  from * have "ms_closure X xs f basis" by (rule ms_closure_embed[of X xs f basis])
  thus ?thesis
  proof (coinduction arbitrary: xs f rule: is_expansion_aux_coinduct)
    case (is_expansion_aux xs f)
    from this and basis show ?case
    proof (induction rule: ms_closure.induct)
      case (ms_closure_embed xs f basis)
      from step[OF ms_closure_embed(1)] show ?case by auto
    next
      case (ms_closure_MSLCons xs f C b e basis)
      thus ?case by auto
    next
      case (ms_closure_cong xs f basis g)
      note ev = \<open>\<forall>\<^sub>F x in at_top. f x = g x\<close>
      hence ev_zero_iff: "eventually (\<lambda>x. f x = 0) at_top \<longleftrightarrow> eventually (\<lambda>x. g x = 0) at_top"
        by (rule eventually_subst')
      have *: "ms_closure X xs' (\<lambda>x. f x - c x * b x powr e) basis \<longleftrightarrow>
                 ms_closure X xs' (\<lambda>x. g x - c x * b x powr e) basis" for xs' c b e
        by (rule iffI; erule ms_closure.intros(2)) (insert ev, auto elim: eventually_mono)
      from ms_closure_cong show ?case
        by (simp add: ev_zero_iff * landau_o.small.in_cong[OF ev])     
    next
      case (ms_closure_embed' xs f basis)
      from this show ?case
        by (cases rule: is_expansion_aux.cases) (force intro: ms_closure.intros(7))+
    next
      
      case (ms_closure_basis xs f b basis C e)
      show ?case
      proof (cases xs rule: ms_aux_cases)
        case MSLNil
        with ms_closure_basis show ?thesis
          by (auto simp: scale_shift_ms_aux_def split: prod.split elim: eventually_mono)
      next
        case (MSLCons C' e' xs')
        with ms_closure_basis have IH:
          "ms_closure X (MSLCons (C', e') xs') f (b # basis)"
          "is_expansion C basis" "xs = MSLCons (C', e') xs'"
          "ms_closure X xs' (\<lambda>x. f x - eval C' x * b x powr e') (b # basis)"
          "ms_exp_gt e' (ms_aux_hd_exp xs')"
          "is_expansion C' basis" "\<And>x. x > e' \<Longrightarrow> f \<in> o(\<lambda>xa. b xa powr x)"
          by auto
        
        {
          fix e'' :: real assume *: "e + e' < e''"
          define d where "d = (e'' - e - e') / 2"
          from * have "d > 0" by (simp add: d_def)
          hence "(\<lambda>x. eval C x * b x powr e * f x) \<in> o(\<lambda>x. b x powr d * b x powr e * b x powr (e'+d))"
            using ms_closure_basis(4) IH
            by (intro landau_o.small.mult[OF landau_o.small_big_mult] IH 
              is_expansion_imp_smallo[OF _ IH(2)]) (simp_all add: basis_wf_Cons)
          also have "\<dots> = o(\<lambda>x. b x powr e'')" by (simp add: d_def powr_add [symmetric])
          finally have "(\<lambda>x. eval C x * b x powr e * f x) \<in> \<dots>" .
        }
        moreover have "ms_closure X xs' (\<lambda>x. f x - eval C' x * b x powr e') (b # basis)"
          using ms_closure_basis IH by auto
        note ms_closure.intros(6)[OF this IH(2), of e]
        moreover have "ms_exp_gt (e + e') (ms_aux_hd_exp (scale_shift_ms_aux (C, e) xs'))"
          using \<open>ms_exp_gt e' (ms_aux_hd_exp xs')\<close>
          by (cases xs') (simp_all add: hd_exp_basis scale_shift_ms_aux_def )
        ultimately show ?thesis using IH(2,6) MSLCons ms_closure_basis(4)
          by (auto simp: scale_shift_ms_aux_MSLCons algebra_simps powr_add basis_wf_Cons
                   intro: is_expansion_mult)
      qed
      
    next
      case (ms_closure_add xs f basis ys g)
      show ?case
      proof (cases xs ys rule: ms_aux_cases[case_product ms_aux_cases])
        case MSLNil_MSLNil
        with ms_closure_add 
          have "eventually (\<lambda>x. f x = 0) at_top" "eventually (\<lambda>x. g x = 0) at_top"
            by simp_all
        hence "eventually (\<lambda>x. f x + g x = 0) at_top" by eventually_elim simp
        with MSLNil_MSLNil ms_closure_add show ?thesis by simp
      next
        case (MSLNil_MSLCons c e xs')
        with ms_closure_add have "eventually (\<lambda>x. f x = 0) at_top" by simp
        hence ev: "eventually (\<lambda>x. f x + g x = g x) at_top" by eventually_elim simp
        have *: "ms_closure X xs (\<lambda>x. f x + g x - y x) basis \<longleftrightarrow> 
                   ms_closure X xs (\<lambda>x. g x - y x) basis" for y basis xs
          by (rule iffI; erule ms_closure_cong) (insert ev, simp_all)
        from MSLNil_MSLCons ms_closure_add
        show ?thesis by (simp add: * landau_o.small.in_cong[OF ev])
      next
        case (MSLCons_MSLNil c e xs')
        with ms_closure_add have "eventually (\<lambda>x. g x = 0) at_top" by simp
        hence ev: "eventually (\<lambda>x. f x + g x = f x) at_top" by eventually_elim simp
        have *: "ms_closure X xs (\<lambda>x. f x + g x - y x) basis \<longleftrightarrow> 
                   ms_closure X xs (\<lambda>x. f x - y x) basis" for y basis xs
          by (rule iffI; erule ms_closure_cong) (insert ev, simp_all)
        from MSLCons_MSLNil ms_closure_add
        show ?thesis by (simp add: * landau_o.small.in_cong[OF ev])          
      next
        case (MSLCons_MSLCons C1 e1 xs' C2 e2 ys')
        with ms_closure_add obtain b basis' where IH:
          "basis_wf (b # basis')" "basis = b # basis'"
          "ms_closure X (MSLCons (C1, e1) xs') f (b # basis')"
          "ms_closure X (MSLCons (C2, e2) ys') g (b # basis')"
          "xs = MSLCons (C1, e1) xs'" "ys = MSLCons (C2, e2) ys'"
          "ms_closure X xs' (\<lambda>x. f x - eval C1 x * b x powr e1) (b # basis')"
          "ms_closure X ys' (\<lambda>x. g x - eval C2 x * b x powr e2) (b # basis')"
          "is_expansion C1 basis'" "\<And>e. e > e1 \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e)"
          "is_expansion C2 basis'" "\<And>e. e > e2 \<Longrightarrow> g \<in> o(\<lambda>x. b x powr e)"
          "ms_exp_gt e1 (ms_aux_hd_exp xs')" "ms_exp_gt e2 (ms_aux_hd_exp ys')"
          by blast
        have o: "(\<lambda>x. f x + g x) \<in> o(\<lambda>x. b x powr e)" if "e > max e1 e2" for e
          using that by (intro sum_in_smallo IH) simp_all
      
        show ?thesis
        proof (cases e1 e2 rule: linorder_cases)
          case less
          have gt: "ms_exp_gt e2 (combine_options max (Some e1) (ms_aux_hd_exp ys'))"
            using \<open>ms_exp_gt e2 _\<close> less by (cases "ms_aux_hd_exp ys'") auto
          have "ms_closure X (plus_ms_aux xs ys')
                  (\<lambda>x. f x + (g x - eval C2 x * b x powr e2)) (b # basis')"
            by (rule ms_closure.intros(4)) (insert IH, simp_all)
          with less IH(2,11,14) o gt show ?thesis
            by (intro disjI2) (simp add: MSLCons_MSLCons plus_ms_aux_MSLCons algebra_simps hd_exp_plus)
        next
          case greater
          have gt: "ms_exp_gt e1 (combine_options max (ms_aux_hd_exp xs') (Some e2))"
            using \<open>ms_exp_gt e1 _\<close> greater by (cases "ms_aux_hd_exp xs'") auto
          have "ms_closure X (plus_ms_aux xs' ys)
                  (\<lambda>x. (f x - eval C1 x * b x powr e1) + g x) (b # basis')"
            by (rule ms_closure.intros(4)) (insert IH, simp_all)
          with greater IH(2,9,13) o gt show ?thesis
            by (intro disjI2) (simp add:  MSLCons_MSLCons plus_ms_aux_MSLCons algebra_simps hd_exp_plus)
        next
          case equal
          have gt: "ms_exp_gt e2 (combine_options max (ms_aux_hd_exp xs')
                      (ms_aux_hd_exp ys'))"
            using \<open>ms_exp_gt e1 _\<close> \<open>ms_exp_gt e2 _\<close> equal
            by (cases "ms_aux_hd_exp xs'"; cases "ms_aux_hd_exp ys'") auto
          have "ms_closure X (plus_ms_aux xs' ys')
                  (\<lambda>x. (f x - eval C1 x * b x powr e1) + (g x - eval C2 x * b x powr e2)) (b # basis')"
            by (rule ms_closure.intros(4)) (insert IH, simp_all)
          with equal IH(1,2,9,11,13,14) o gt show ?thesis
            by (intro disjI2) 
               (auto intro: is_expansion_add 
                     simp: plus_ms_aux_MSLCons basis_wf_Cons algebra_simps hd_exp_plus  MSLCons_MSLCons)
        qed
      qed
      
    next
      
      case (ms_closure_mult xs f basis ys g)
      show ?case
      proof (cases "xs = MSLNil \<or> ys = MSLNil")
        case True
        with ms_closure_mult 
          have "eventually (\<lambda>x. f x = 0) at_top \<or> eventually (\<lambda>x. g x = 0) at_top" by blast
        hence "eventually (\<lambda>x. f x * g x = 0) at_top" by (auto elim: eventually_mono)
        with ms_closure_mult True show ?thesis by auto
      next
        case False
        with ms_closure_mult obtain C1 e1 xs' C2 e2 ys' b basis' where IH:
          "xs = MSLCons (C1, e1) xs'" "ys = MSLCons (C2, e2) ys'"
          "basis_wf (b # basis')" "basis = b # basis'"
          "ms_closure X (MSLCons (C1, e1) xs') f (b # basis')"
          "ms_closure X (MSLCons (C2, e2) ys') g (b # basis')"
          "ms_closure X xs' (\<lambda>x. f x - eval C1 x * b x powr e1) (b # basis')"
          "ms_closure X ys' (\<lambda>x. g x - eval C2 x * b x powr e2) (b # basis')"
          "is_expansion C1 basis'" "\<And>e. e > e1 \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e)"
          "is_expansion C2 basis'" "\<And>e. e > e2 \<Longrightarrow> g \<in> o(\<lambda>x. b x powr e)"
          "ms_exp_gt e1 (ms_aux_hd_exp xs')" "ms_exp_gt e2 (ms_aux_hd_exp ys')"
          by blast
        have o: "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. b x powr e)" if "e > e1 + e2" for e
        proof -
          define d where "d = (e - e1 - e2) / 2"
          from that have d: "d > 0" by (simp add: d_def)
          hence "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. b x powr (e1 + d) * b x powr (e2 + d))"
            by (intro landau_o.small.mult IH) simp_all
          also have "\<dots> = o(\<lambda>x. b x powr e)" by (simp add: d_def powr_add [symmetric])
          finally show ?thesis .
        qed

        have "ms_closure X (plus_ms_aux (scale_shift_ms_aux (C1, e1) ys') (times_ms_aux xs' ys))
                (\<lambda>x. eval C1 x * b x powr e1 * (g x - eval C2 x * b x powr e2) + 
                     ((f x - eval C1 x * b x powr e1) * g x)) (b # basis')"
          (is "ms_closure _ ?zs ?f _") using ms_closure_mult IH(4)
          by (intro ms_closure.intros(4-6) IH) simp_all
        also have "?f = (\<lambda>x. f x * g x - eval C1 x * eval C2 x * b x powr (e1 + e2))"
          by (intro ext) (simp add: algebra_simps powr_add)
        finally have "ms_closure X ?zs \<dots> (b # basis')" .
        moreover from \<open>ms_exp_gt e1 _\<close> \<open>ms_exp_gt e2 _\<close>
        have "ms_exp_gt (e1 + e2) (combine_options max (map_option ((+) e1) 
                (ms_aux_hd_exp ys')) (case ms_aux_hd_exp xs' of None \<Rightarrow> None | Some x \<Rightarrow>
                  (case Some e2 of None \<Rightarrow> None | Some y \<Rightarrow> Some (x + y))))"
            by (cases "ms_aux_hd_exp xs'"; cases "ms_aux_hd_exp ys'")
               (simp_all add: hd_exp_times hd_exp_plus hd_exp_basis IH)
        ultimately show ?thesis using IH(1,2,3,4,9,11) o
          by (auto simp: times_ms_aux_MSLCons basis_wf_Cons hd_exp_times hd_exp_plus hd_exp_basis
                   intro: is_expansion_mult)
      qed
    qed
  qed
qed



subsubsection \<open>Dominant terms\<close>

lemma one_smallo_powr: "e > (0::real) \<Longrightarrow> (\<lambda>_. 1) \<in> o(\<lambda>x. x powr e)"
  by (auto simp: smallomega_iff_smallo [symmetric] real_powr_at_top 
                 smallomegaI_filterlim_at_top_norm)

lemma powr_smallo_one: "e < (0::real) \<Longrightarrow> (\<lambda>x. x powr e) \<in> o(\<lambda>_. 1)"
  by (intro smalloI_tendsto) (auto intro!: tendsto_neg_powr filterlim_ident)

lemma eval_monom_smallo':
  assumes "basis_wf (b # basis)" "e > 0"
  shows   "eval_monom x basis \<in> o(\<lambda>x. b x powr e)"
proof (cases x)
  case (Pair c es)
  from assms show ?thesis unfolding Pair
  proof (induction es arbitrary: b basis e)
    case (Nil b basis e)
    hence b: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
    have "eval_monom (c, []) basis \<in> O(\<lambda>_. 1)" by simp
    also have "(\<lambda>_. 1) \<in> o(\<lambda>x. b x powr e)"
      by (rule landau_o.small.compose[OF _ b]) (insert Nil, simp add: one_smallo_powr)
    finally show ?case .
  next
    case (Cons e' es b basis e)
    show ?case
    proof (cases basis)
      case Nil
      from Cons have b: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
      from Nil have "eval_monom (c, e' # es) basis \<in> O(\<lambda>_. 1)" by simp
      also have "(\<lambda>_. 1) \<in> o(\<lambda>x. b x powr e)"
        by (rule landau_o.small.compose[OF _ b]) (insert Cons.prems, simp add: one_smallo_powr)
      finally show ?thesis .
    next
      case (Cons b' basis')
      from Cons.prems have "eval_monom (c, es) basis' \<in> o(\<lambda>x. b' x powr 1)"
        by (intro Cons.IH) (simp_all add: basis_wf_Cons Cons)
      hence "(\<lambda>x. eval_monom (c, es) basis' x * b' x powr e') \<in> o(\<lambda>x. b' x powr 1 * b' x powr e')"
        by (rule landau_o.small_big_mult) simp_all
      also have "\<dots> = o(\<lambda>x. b' x powr (1 + e'))" by (simp add: powr_add)
      also from Cons.prems have "(\<lambda>x. b' x powr (1 + e')) \<in> o(\<lambda>x. b x powr e)"
        by (intro ln_smallo_imp_flat) (simp_all add: basis_wf_Cons Cons)
      finally show ?thesis by (simp add: powr_add [symmetric] Cons eval_monom_Cons)
    qed
  qed
qed

lemma eval_monom_smallomega':
  assumes "basis_wf (b # basis)" "e < 0"
  shows   "eval_monom (1, es) basis \<in> \<omega>(\<lambda>x. b x powr e)"
  using assms
proof (induction es arbitrary: b basis e)
  case (Nil b basis e)
  hence b: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  have "eval_monom (1, []) basis \<in> \<Omega>(\<lambda>_. 1)" by simp
  also have "(\<lambda>_. 1) \<in> \<omega>(\<lambda>x. b x powr e)" unfolding smallomega_iff_smallo
    by (rule landau_o.small.compose[OF _ b]) (insert Nil, simp add: powr_smallo_one)
  finally show ?case .
next
  case (Cons e' es b basis e)
  show ?case
  proof (cases basis)
    case Nil
    from Cons have b: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
    from Nil have "eval_monom (1, e' # es) basis \<in> \<Omega>(\<lambda>_. 1)" by simp
    also have "(\<lambda>_. 1) \<in> \<omega>(\<lambda>x. b x powr e)" unfolding smallomega_iff_smallo
      by (rule landau_o.small.compose[OF _ b]) (insert Cons.prems, simp add: powr_smallo_one)
    finally show ?thesis .
  next
    case (Cons b' basis')
    from Cons.prems have "eval_monom (1, es) basis' \<in> \<omega>(\<lambda>x. b' x powr -1)"
      by (intro Cons.IH) (simp_all add: basis_wf_Cons Cons)
    hence "(\<lambda>x. eval_monom (1, es) basis' x * b' x powr e') \<in> \<omega>(\<lambda>x. b' x powr -1 * b' x powr e')"
      by (rule landau_omega.small_big_mult) simp_all
    also have "\<dots> = \<omega>(\<lambda>x. b' x powr (e' - 1))" by (simp add: powr_diff powr_minus field_simps)
    also from Cons.prems have "(\<lambda>x. b' x powr (e' - 1)) \<in> \<omega>(\<lambda>x. b x powr e)"
      unfolding smallomega_iff_smallo
      by (intro ln_smallo_imp_flat') (simp_all add: basis_wf_Cons Cons)
    finally show ?thesis by (simp add: powr_add [symmetric] Cons eval_monom_Cons)
  qed
qed

lemma dominant_term_ms_aux:
  assumes basis: "basis_wf basis" and xs: "trimmed_ms_aux xs" "is_expansion_aux xs f basis"
  shows   "f \<sim>[at_top] eval_monom (dominant_term_ms_aux xs) basis" (is ?thesis1)
    and   "eventually (\<lambda>x. sgn (f x) = sgn (fst (dominant_term_ms_aux xs))) at_top" (is ?thesis2)
proof -
  include asymp_equiv_syntax
  from xs(2,1) obtain xs' C b e basis' where xs':
    "trimmed C" "xs = MSLCons (C, e) xs'" "basis = b # basis'"
    "is_expansion_aux xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "is_expansion C basis'" "(\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'))"
    "ms_exp_gt e (ms_aux_hd_exp xs')"
    by (cases rule: is_expansion_aux.cases) (auto simp: trimmed_ms_aux_MSLCons)
  from is_expansion_aux_imp_smallo''[OF xs'(4,7)]
    obtain e' where e': "e' < e" "(\<lambda>x. f x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr e')"
      unfolding list.sel by blast   
  from basis xs' have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
    
  note e'(2)
  also have "o(\<lambda>x. b x powr e') = o(\<lambda>x. b x powr (e' - e) * b x powr e)" 
    by (simp add: powr_add [symmetric])
  also from xs' basis e'(1) have "eval C \<in> \<omega>(\<lambda>x. b x powr (e' - e))"
    by (intro is_expansion_imp_smallomega[of basis']) (simp_all add: basis_wf_Cons)
  hence "(\<lambda>x. b x powr (e' - e) * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)"
    by (intro landau_o.small_big_mult) (simp_all add: smallomega_iff_smallo)
  finally have *: "(\<lambda>x. f x - eval C x * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)" .
  hence "f \<sim> (\<lambda>x. eval C x * b x powr e)" by (intro smallo_imp_asymp_equiv) simp
  also from basis xs' have "eval C \<sim> (\<lambda>x. eval_monom (dominant_term C) basis' x)"
    by (intro dominant_term) (simp_all add: basis_wf_Cons)
  also have "(\<lambda>a. eval_monom (dominant_term C) basis' a * b a powr e) = 
               eval_monom (dominant_term_ms_aux xs) basis"
    by (auto simp add: dominant_term_ms_aux_def xs' eval_monom_Cons fun_eq_iff split: prod.split)
  finally show ?thesis1 by - (simp_all add: asymp_equiv_intros)
  
  have "eventually (\<lambda>x. sgn (eval C x * b x powr e + (f x - eval C x * b x powr e)) = 
                          sgn (eval C x * b x powr e)) at_top"
    by (intro smallo_imp_eventually_sgn *)
  moreover have "eventually (\<lambda>x. sgn (eval C x) = sgn (fst (dominant_term C))) at_top"
    using xs' basis by (intro trimmed_imp_eventually_sgn[of basis']) (simp_all add: basis_wf_Cons)
  ultimately have "eventually (\<lambda>x. sgn (f x) = sgn (fst (dominant_term C))) at_top"
    using b_pos by eventually_elim (simp_all add: sgn_mult)
  thus ?thesis2 using xs'(2) by (auto simp: dominant_term_ms_aux_def split: prod.split)
qed

lemma eval_monom_smallo:
  assumes "basis \<noteq> []" "basis_wf basis" "length es = length basis" "e > hd es"
  shows   "eval_monom (c, es) basis \<in> o(\<lambda>x. hd basis x powr e)"
proof (cases es; cases basis)
  fix b basis' e' es' assume [simp]: "basis = b # basis'" "es = e' # es'"
  from assms have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" 
    using filterlim_at_top_dense by blast
  have "(\<lambda>x. eval_monom (1, es') basis' x * b x powr e') \<in> o(\<lambda>x. b x powr (e - e') * b x powr e')"
    using assms by (intro landau_o.small_big_mult eval_monom_smallo') auto
  also have "(\<lambda>x. b x powr (e - e') * b x powr e') \<in> \<Theta>(\<lambda>x. b x powr e)"
    by (intro bigthetaI_cong eventually_mono[OF b_pos]) (auto simp: powr_diff)
  finally show ?thesis by (simp add: eval_monom_def algebra_simps)
qed (insert assms, auto)

lemma eval_monom_smallomega:
  assumes "basis \<noteq> []" "basis_wf basis" "length es = length basis" "e < hd es"
  shows   "eval_monom (1, es) basis \<in> \<omega>(\<lambda>x. hd basis x powr e)"
proof (cases es; cases basis)
  fix b basis' e' es' assume [simp]: "basis = b # basis'" "es = e' # es'"
  from assms have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" 
    using filterlim_at_top_dense by blast
  have "(\<lambda>x. eval_monom (1, es') basis' x * b x powr e') \<in> \<omega>(\<lambda>x. b x powr (e - e') * b x powr e')"
    using assms by (intro landau_omega.small_big_mult eval_monom_smallomega') auto
  also have "(\<lambda>x. b x powr (e - e') * b x powr e') \<in> \<Theta>(\<lambda>x. b x powr e)"
    by (intro bigthetaI_cong eventually_mono[OF b_pos]) (auto simp: powr_diff)
  finally show ?thesis by (simp add: eval_monom_Cons)
qed (insert assms, auto)


subsubsection \<open>Correctness of multiseries operations\<close>

lemma drop_zero_ms_aux:
  assumes "eventually (\<lambda>x. eval C x = 0) at_top"
  assumes "is_expansion_aux (MSLCons (C, e) xs) f basis"
  shows   "is_expansion_aux xs f basis"
proof (rule is_expansion_aux_cong)
  from assms(2) show "is_expansion_aux xs (\<lambda>x. f x - eval C x * hd basis x powr e) basis"
    by (auto elim: is_expansion_aux_MSLCons)
  from assms(1) show "eventually (\<lambda>x. f x - eval C x * hd basis x powr e = f x) at_top"
    by eventually_elim simp
qed

lemma dominant_term_ms_aux_bigo:
  assumes basis: "basis_wf basis" and xs: "is_expansion_aux xs f basis"
  shows   "f \<in> O(eval_monom (1, snd (dominant_term_ms_aux xs)) basis)" (is ?thesis1)
proof (cases xs rule: ms_aux_cases)
  case MSLNil
  with assms have "eventually (\<lambda>x. f x = 0) at_top"
    by (auto elim: is_expansion_aux.cases)
  hence "f \<in> \<Theta>(\<lambda>_. 0)" by (intro bigthetaI_cong) auto
  also have "(\<lambda>_. 0) \<in> O(eval_monom (1, snd (dominant_term_ms_aux xs)) basis)" by simp
  finally show ?thesis .
next
  case [simp]: (MSLCons C e xs')
  from xs obtain b basis' where xs':
    "basis = b # basis'"
    "is_expansion_aux xs' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "is_expansion C basis'" "(\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'))"
    "ms_exp_gt e (ms_aux_hd_exp xs')"
    by (cases rule: is_expansion_aux.cases) auto
  from is_expansion_aux_imp_smallo''[OF xs'(2,5)]
    obtain e' where e': "e' < e" "(\<lambda>x. f x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr e')"
      unfolding list.sel by blast   
  from basis xs' have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)

  let ?h = "(\<lambda>x. eval_monom (1, snd (dominant_term C)) basis' x * b x powr e)"
  note e'(2)
  also have "(\<lambda>x. b x powr e') \<in> \<Theta>(\<lambda>x. b x powr (e' - e) * b x powr e)"
    by (intro bigthetaI_cong eventually_mono[OF b_pos]) (auto simp: powr_diff)
  also have "(\<lambda>x. b x powr (e' - e) * b x powr e) \<in> o(?h)"
    unfolding smallomega_iff_smallo [symmetric] using e'(1) basis xs'
    by (intro landau_omega.small_big_mult landau_omega.big_refl eval_monom_smallomega')
       (simp_all add: basis_wf_Cons)
  finally have "(\<lambda>x. f x - eval C x * b x powr e) \<in> O(?h)" by (rule landau_o.small_imp_big)
  moreover have "(\<lambda>x. eval C x * b x powr e) \<in> O(?h)"
    using basis xs' by (intro landau_o.big.mult dominant_term_bigo) (auto simp: basis_wf_Cons)
  ultimately have "(\<lambda>x. f x - eval C x * b x powr e + eval C x * b x powr e) \<in> O(?h)"
    by (rule sum_in_bigo)
  hence "f \<in> O(?h)" by simp
  also have "?h = eval_monom (1, snd (dominant_term_ms_aux xs)) basis"
    using xs' by (auto simp: dominant_term_ms_aux_def case_prod_unfold eval_monom_Cons)
  finally show ?thesis .
qed

lemma const_ms_aux:
  assumes basis: "basis_wf basis" 
      and "length basis = Suc (expansion_level TYPE('a::multiseries))"
  shows   "is_expansion_aux (const_ms_aux c :: ('a \<times> real) msllist) (\<lambda>_. c) basis"
proof -
  from assms(2) obtain b basis' where [simp]: "basis = b # basis'" by (cases basis) simp_all
  from basis have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)

  have "(\<lambda>_. c) \<in> o(\<lambda>x. b x powr e)" if "e > 0" for e
  proof -
    have "(\<lambda>_. c) \<in> O(\<lambda>_. 1)" by (cases "c = 0") simp_all  
    also from b_pos have "(\<lambda>_. 1) \<in> \<Theta>(\<lambda>x. b x powr 0)" 
      by (intro bigthetaI_cong) (auto elim: eventually_mono)
    also from that b_limit have "(\<lambda>x. b x powr 0) \<in> o(\<lambda>x. b x powr e)" 
      by (subst powr_smallo_iff) auto
    finally show ?thesis .
  qed
  with b_pos assms show ?thesis
    by (auto intro!: is_expansion_aux.intros simp: const_ms_aux_def is_expansion_const basis_wf_Cons 
             elim: eventually_mono)
qed

lemma uminus_ms_aux:
  assumes basis: "basis_wf basis"
  assumes F: "is_expansion_aux F f basis"
  shows   "is_expansion_aux (uminus_ms_aux F) (\<lambda>x. -f x) basis"
  using F
proof (coinduction arbitrary: F f rule: is_expansion_aux_coinduct)
  case (is_expansion_aux F f)
  note IH = is_expansion_aux
  show ?case
  proof (cases F rule: ms_aux_cases)
    case MSLNil
    with IH show ?thesis by (auto simp: uminus_ms_aux_def elim: is_expansion_aux.cases)
  next
    case (MSLCons C e xs)
    with IH obtain b basis'
      where IH: "basis = b # basis'" 
                "is_expansion_aux xs (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
                "is_expansion C basis'"
                "\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')" "ms_exp_gt e (ms_aux_hd_exp xs)"
      by (auto elim: is_expansion_aux_MSLCons)
    from basis IH have basis': "basis_wf basis'" by (simp add: basis_wf_Cons)
    with IH basis show ?thesis
      by (force simp: uminus_ms_aux_MSLCons MSLCons is_expansion_uminus)
  qed
qed

lemma plus_ms_aux:
  assumes "basis_wf basis" "is_expansion_aux F f basis" "is_expansion_aux G g basis"
  shows   "is_expansion_aux (plus_ms_aux F G) (\<lambda>x. f x + g x) basis"
  using assms
proof (coinduction arbitrary: F f G g rule: is_expansion_aux_coinduct)
  case (is_expansion_aux F f G g)
  note IH = this
  show ?case
  proof (cases F G rule: ms_aux_cases[case_product ms_aux_cases])
    assume [simp]: "F = MSLNil" "G = MSLNil"
    with IH have *: "eventually (\<lambda>x. f x = 0) at_top" "eventually (\<lambda>x. g x = 0) at_top" 
                 and length: "length basis = Suc (expansion_level TYPE('a))"
      by (auto elim: is_expansion_aux.cases)
    from * have "eventually (\<lambda>x. f x + g x = 0) at_top" by eventually_elim simp
    with length show ?case by simp 
  next
    assume [simp]: "F = MSLNil"
    fix C e G' assume G: "G = MSLCons (C, e) G'"
    from IH have f: "eventually (\<lambda>x. f x = 0) at_top" by (auto elim: is_expansion_aux.cases)
    from f have "eventually (\<lambda>x. f x + g x = g x) at_top" by eventually_elim simp
    note eq = landau_o.small.in_cong[OF this]
    from IH(3) G obtain b basis' where G':
      "basis = b # basis'"
      "is_expansion_aux G' (\<lambda>x. g x - eval C x * b x powr e) (b # basis')"
      "is_expansion C basis'" "\<forall>e'>e. g \<in> o(\<lambda>x. b x powr e')" "ms_exp_gt e (ms_aux_hd_exp G')"
      by (auto elim!: is_expansion_aux_MSLCons)
    show ?thesis
      by (rule disjI2, inst_existentials G' b e basis' C F f G' "\<lambda>x. g x - eval C x * b x powr e")
         (insert G' IH(1,2), simp_all add: G eq algebra_simps)
  next
    assume [simp]: "G = MSLNil"
    fix C e F' assume F: "F = MSLCons (C, e) F'"
    from IH have g: "eventually (\<lambda>x. g x = 0) at_top" by (auto elim: is_expansion_aux.cases)
    hence "eventually (\<lambda>x. f x + g x = f x) at_top" by eventually_elim simp
    note eq = landau_o.small.in_cong[OF this]
    from IH F obtain b basis' where F':
      "basis = b # basis'"
      "is_expansion_aux F' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
      "is_expansion C basis'" "\<forall>e'>e. f \<in> o(\<lambda>x. b x powr e')" "ms_exp_gt e (ms_aux_hd_exp F')"
      by (auto elim!: is_expansion_aux_MSLCons)
    show ?thesis
      by (rule disjI2, inst_existentials F' b e basis' C F' "\<lambda>x. f x - eval C x * b x powr e" G g)
         (insert F g F' IH, simp_all add: eq algebra_simps)
  next
    fix C1 e1 F' C2 e2 G'
    assume F: "F = MSLCons (C1, e1) F'" and G: "G = MSLCons (C2, e2) G'"
    from IH F obtain b basis' where
      basis': "basis = b # basis'" and F':
      "is_expansion_aux F' (\<lambda>x. f x - eval C1 x * b x powr e1) (b # basis')"
      "is_expansion C1 basis'" "\<And>e'. e' > e1 \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')" 
      "ms_exp_gt e1 (ms_aux_hd_exp F')"
      by (auto elim!: is_expansion_aux_MSLCons)
    from IH G basis' have G':
      "is_expansion_aux G' (\<lambda>x. g x - eval C2 x * b x powr e2) (b # basis')"
      "is_expansion C2 basis'" "\<And>e'. e' > e2 \<Longrightarrow> g \<in> o(\<lambda>x. b x powr e')"
      "ms_exp_gt e2 (ms_aux_hd_exp G')"
      by (auto elim!: is_expansion_aux_MSLCons)  
    hence *: "\<forall>x>max e1 e2. (\<lambda>x. f x + g x) \<in> o(\<lambda>xa. b xa powr x)"
      by (intro allI impI sum_in_smallo F' G') simp_all
      
    consider "e1 > e2" | "e1 < e2" | "e1 = e2" by force
    thus ?thesis
    proof cases
      assume e: "e1 > e2"
      have gt: "ms_exp_gt e1 (combine_options max (ms_aux_hd_exp F') (Some e2))"
        using \<open>ms_exp_gt e1 _\<close> e by (cases "ms_aux_hd_exp F'") simp_all
      show ?thesis
        by (rule disjI2, inst_existentials "plus_ms_aux F' G" b e1 basis' C1 F' 
                           "\<lambda>x. f x - eval C1 x * b x powr e1" G g)
           (insert e F'(1,2,4) IH(1,3) basis'(1) * gt,
            simp_all add: F G plus_ms_aux_MSLCons algebra_simps hd_exp_plus)
    next
      assume e: "e1 < e2"
      have gt: "ms_exp_gt e2 (combine_options max (Some e1) (ms_aux_hd_exp G'))"
        using \<open>ms_exp_gt e2 _\<close> e by (cases "ms_aux_hd_exp G'") simp_all
      show ?thesis
        by (rule disjI2, inst_existentials "plus_ms_aux F G'" b e2 basis' C2 F f G'
                           "\<lambda>x. g x - eval C2 x * b x powr e2")
           (insert e G'(1,2,4) IH(1,2) basis'(1) * gt, 
            simp_all add: F G plus_ms_aux_MSLCons algebra_simps hd_exp_plus)
    next
      assume e: "e1 = e2"
      have gt: "ms_exp_gt e2 (combine_options max (ms_aux_hd_exp F') (ms_aux_hd_exp G'))"
        using \<open>ms_exp_gt e1 _\<close> \<open>ms_exp_gt e2 _\<close> e
        by (cases "ms_aux_hd_exp F'"; cases "ms_aux_hd_exp G'") simp_all
      show ?thesis
        by (rule disjI2, inst_existentials "plus_ms_aux F' G'" b e1 basis' "C1 + C2" F' 
                         "\<lambda>x. f x - eval C1 x * b x powr e1" G' "\<lambda>x. g x - eval C2 x * b x powr e2")
           (insert e F'(1,2,4) G'(1,2,4) IH(1) basis'(1) * gt, 
            simp_all add: F G plus_ms_aux_MSLCons algebra_simps hd_exp_plus is_expansion_add basis_wf_Cons)
    qed
  qed
qed

lemma minus_ms_aux:
  assumes "basis_wf basis" "is_expansion_aux F f basis" "is_expansion_aux G g basis"
  shows   "is_expansion_aux (minus_ms_aux F G) (\<lambda>x. f x - g x) basis"
proof -
  have "is_expansion_aux (minus_ms_aux F G) (\<lambda>x. f x + (- g x)) basis"
    unfolding minus_ms_aux_def by (intro plus_ms_aux uminus_ms_aux assms)
  thus ?thesis by simp
qed

lemma scale_shift_ms_aux:
  assumes basis: "basis_wf (b # basis)"
  assumes F: "is_expansion_aux F f (b # basis)"
  assumes C: "is_expansion C basis"
  shows   "is_expansion_aux (scale_shift_ms_aux (C, e) F) (\<lambda>x. eval C x * b x powr e * f x) (b # basis)"
  using F
proof (coinduction arbitrary: F f rule: is_expansion_aux_coinduct)
  case (is_expansion_aux F f)
  note IH = is_expansion_aux
  show ?case
  proof (cases F rule: ms_aux_cases)
    case MSLNil
    with IH show ?thesis 
      by (auto simp: scale_shift_ms_aux_def elim!: is_expansion_aux.cases eventually_mono)
  next
    case (MSLCons C' e' xs)
    with IH have IH: "is_expansion_aux xs (\<lambda>x. f x - eval C' x * b x powr e') (b # basis)"
                     "is_expansion C' basis" "ms_exp_gt e' (ms_aux_hd_exp xs)"
                     "\<And>e''. e' < e'' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'')"
      by (auto elim: is_expansion_aux_MSLCons)
    
    have "(\<lambda>x. eval C x * b x powr e * f x) \<in> o(\<lambda>x. b x powr e'')" if "e'' > e + e'" for e''
    proof -
      define d where "d = (e'' - e - e') / 2"
      from that have d: "d > 0" by (simp add: d_def)
      have "(\<lambda>x. eval C x * b x powr e * f x) \<in> o(\<lambda>x. b x powr d * b x powr e * b x powr (e' + d))"
        using d basis
        by (intro landau_o.small.mult[OF landau_o.small_big_mult] 
              is_expansion_imp_smallo[OF _ C] IH) (simp_all add: basis_wf_Cons)
      also have "\<dots> = o(\<lambda>x. b x powr e'')" by (simp add: d_def powr_add [symmetric])
      finally show ?thesis .
    qed
    moreover have "ms_exp_gt (e + e') (ms_aux_hd_exp (scale_shift_ms_aux (C, e) xs))"
      using IH(3) by (cases "ms_aux_hd_exp xs") (simp_all add: hd_exp_basis)
    ultimately show ?thesis using basis IH(1,2)
      by (intro disjI2, inst_existentials "scale_shift_ms_aux (C, e) xs" b "e + e'" 
                          basis "C * C'" xs "\<lambda>x. f x - eval C' x * b x powr e'")
         (simp_all add: scale_shift_ms_aux_MSLCons MSLCons is_expansion_mult basis_wf_Cons
                        algebra_simps powr_add C)
  qed
qed

lemma times_ms_aux:
  assumes basis: "basis_wf basis"
  assumes F: "is_expansion_aux F f basis" and G: "is_expansion_aux G g basis"
  shows   "is_expansion_aux (times_ms_aux F G) (\<lambda>x. f x * g x) basis"
  using F G
proof (coinduction arbitrary: F f G g rule: is_expansion_aux_coinduct_upto)
  case (B F f G g)
  note IH = this
  show ?case
  proof (cases "F = MSLNil \<or> G = MSLNil")
    case True
    with IH have "eventually (\<lambda>x. f x = 0) at_top \<or> eventually (\<lambda>x. g x = 0) at_top"
      and length: "length basis = Suc (expansion_level TYPE('a))"
      by (auto elim: is_expansion_aux.cases)
    from this(1) have "eventually (\<lambda>x. f x * g x = 0) at_top" by (auto elim!: eventually_mono)
    with length True show ?thesis by auto
  next
    case False
    from False obtain C1 e1 F' where F: "F = MSLCons (C1, e1) F'" 
      by (cases F rule: ms_aux_cases) simp_all
    from False obtain C2 e2 G' where G: "G = MSLCons (C2, e2) G'" 
      by (cases G rule: ms_aux_cases) simp_all
    
    from IH(1) F obtain b basis' where
      basis': "basis = b # basis'" and F':
      "is_expansion_aux F' (\<lambda>x. f x - eval C1 x * b x powr e1) (b # basis')"
      "is_expansion C1 basis'" "\<And>e'. e' > e1 \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e')"
      "ms_exp_gt e1 (ms_aux_hd_exp F')"
      by (auto elim!: is_expansion_aux_MSLCons)
    from IH(2) G basis' have G':
      "is_expansion_aux G' (\<lambda>x. g x - eval C2 x * b x powr e2) (b # basis')"
      "is_expansion C2 basis'" "\<And>e'. e' > e2 \<Longrightarrow> g \<in> o(\<lambda>x. b x powr e')"
      "ms_exp_gt e2 (ms_aux_hd_exp G')"
      by (auto elim!: is_expansion_aux_MSLCons)  
    let ?P = "(\<lambda>xs'' fa'' basisa''. \<exists>F f G. xs'' = times_ms_aux F G \<and>
            (\<exists>g. fa'' = (\<lambda>x. f x * g x) \<and> basisa'' = b # basis' \<and> is_expansion_aux F f
                  (b # basis') \<and> is_expansion_aux G g (b # basis')))"
    have "ms_closure ?P (plus_ms_aux (scale_shift_ms_aux (C1, e1) G') (times_ms_aux F' G))
            (\<lambda>x. eval C1 x * b x powr e1 * (g x - eval C2 x * b x powr e2) +
                 (f x - eval C1 x * b x powr e1) * g x) (b # basis')"
      (is "ms_closure _ ?zs _ _") using IH(2) basis' basis
      by (intro ms_closure_add ms_closure_embed'[OF scale_shift_ms_aux] 
            ms_closure_mult[OF ms_closure_embed' ms_closure_embed'] F' G') simp_all
    hence "ms_closure ?P (plus_ms_aux (scale_shift_ms_aux (C1, e1) G') (times_ms_aux F' G))
            (\<lambda>x. f x * g x - eval C1 x * eval C2 x * b x powr (e1 + e2)) (b # basis')"
      by (simp add: algebra_simps powr_add)
    moreover have "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. b x powr e)" if "e > e1 + e2" for e
    proof -
      define d where "d = (e - e1 - e2) / 2"
      from that have "d > 0" by (simp add: d_def)
      hence "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. b x powr (e1 + d) * b x powr (e2 + d))"
        by (intro landau_o.small.mult F' G') simp_all
      also have "\<dots> = o(\<lambda>x. b x powr e)"
        by (simp add: d_def powr_add [symmetric])
      finally show ?thesis .
    qed
    moreover from \<open>ms_exp_gt e1 _\<close> \<open>ms_exp_gt e2 _\<close>
      have "ms_exp_gt (e1 + e2) (ms_aux_hd_exp ?zs)"
        by (cases "ms_aux_hd_exp F'"; cases "ms_aux_hd_exp G'") 
           (simp_all add: hd_exp_times hd_exp_plus hd_exp_basis G)    
    ultimately show ?thesis using F'(2) G'(2) basis' basis
      by (simp add: times_ms_aux_MSLCons basis_wf_Cons is_expansion_mult F G)
  qed
qed (insert basis, simp_all)




lemma powser_ms_aux_MSLNil_iff [simp]: "powser_ms_aux cs f = MSLNil \<longleftrightarrow> cs = MSLNil"
  by (subst powser_ms_aux.code) (simp split: msllist.splits)

lemma powser_ms_aux_MSLNil [simp]: "powser_ms_aux MSLNil f = MSLNil"
  by (subst powser_ms_aux.code) simp

lemma powser_ms_aux_MSLNil' [simp]: 
  "powser_ms_aux (MSLCons c cs) MSLNil = MSLCons (const_expansion c, 0) MSLNil"
  by (subst powser_ms_aux.code) simp

lemma powser_ms_aux_MSLCons: 
  "powser_ms_aux (MSLCons c cs) f = MSLCons (const_expansion c, 0) (times_ms_aux f (powser_ms_aux cs f))"
  by (subst powser_ms_aux.code) simp

lemma hd_exp_powser: "ms_aux_hd_exp (powser_ms_aux cs f) = (if cs = MSLNil then None else Some 0)"
  by (subst powser_ms_aux.code) (simp split: msllist.splits)
  
lemma powser_ms_aux:
  assumes "convergent_powser cs" and basis: "basis_wf basis"
  assumes G: "is_expansion_aux G g basis" "ms_exp_gt 0 (ms_aux_hd_exp G)"
  shows   "is_expansion_aux (powser_ms_aux cs G) (powser cs \<circ> g) basis"
using assms(1)
proof (coinduction arbitrary: cs rule: is_expansion_aux_coinduct_upto)
  case (B cs)
  show ?case
  proof (cases cs)
    case MSLNil
    with G show ?thesis by (auto simp: is_expansion_aux_expansion_level)
  next
    case (MSLCons c cs')
    from is_expansion_aux_basis_nonempty[OF G(1)]
      obtain b basis' where basis': "basis = b # basis'" by (cases basis) simp_all
    from B have conv: "convergent_powser cs'" by (auto simp: MSLCons dest: convergent_powser_stl)  
    from basis basis' have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
    hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
    
    from G(2) have "g \<in> o(\<lambda>x. hd basis x powr 0)"
      by (intro is_expansion_aux_imp_smallo[OF G(1)]) simp
    with basis' have "g \<in> o(\<lambda>x. b x powr 0)" by simp
    also have "(\<lambda>x. b x powr 0) \<in> \<Theta>(\<lambda>x. 1)" 
       using b_pos by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally have g_limit: "(g \<longlongrightarrow> 0) at_top" by (auto dest: smalloD_tendsto)
  
    let ?P = "(\<lambda>xs'' fa'' basisa''. \<exists>cs. xs'' = powser_ms_aux cs G \<and>
                     fa'' = powser cs \<circ> g \<and> basisa'' = b # basis' \<and> convergent_powser cs)"
    have "ms_closure ?P (times_ms_aux G (powser_ms_aux cs' G)) 
            (\<lambda>x. g x * (powser cs' \<circ> g) x) basis" using conv
      by (intro ms_closure_mult [OF ms_closure_embed' ms_closure_embed] G)
         (auto simp add: basis' o_def)
    also have "(\<lambda>x. g x * (powser cs' \<circ> g) x) = (\<lambda>x. x * powser cs' x) \<circ> g"
      by (simp add: o_def)
    finally have "ms_closure ?P (times_ms_aux G (powser_ms_aux cs' G)) 
                    (\<lambda>x. (powser cs \<circ> g) x - c * b x powr 0) basis" unfolding o_def
    proof (rule ms_closure_cong)
      note b_pos
      moreover have "eventually (\<lambda>x. powser cs (g x) = g x * powser cs' (g x) + c) at_top"
      proof -
        from B have "eventually (\<lambda>x. powser cs x = x * powser cs' x + c) (nhds 0)"
          by (simp add: MSLCons powser_MSLCons)
        from this and g_limit show ?thesis by (rule eventually_compose_filterlim)
      qed
      ultimately show "eventually (\<lambda>x. g x * powser cs' (g x) = 
                         powser cs (g x) - c * b x powr 0) at_top"
        by eventually_elim simp
    qed 
    moreover from basis G have "is_expansion (const_expansion c :: 'a) basis'"
      by (intro is_expansion_const)
         (auto dest: is_expansion_aux_expansion_level simp: basis' basis_wf_Cons)
    moreover have "powser cs \<circ> g \<in> o(\<lambda>x. b x powr e)" if "e > 0" for e
    proof -
      have "((powser cs \<circ> g) \<longlongrightarrow> powser cs 0) at_top" unfolding o_def
        by (intro isCont_tendsto_compose[OF _ g_limit] isCont_powser B)
      hence "powser cs \<circ> g \<in> O(\<lambda>_. 1)" 
        by (intro bigoI_tendsto[where c = "powser cs 0"]) (simp_all add: o_def)
      also from b_pos have  "O(\<lambda>_. 1) = O(\<lambda>x. b x powr 0)" 
        by (intro landau_o.big.cong) (auto elim: eventually_mono)
      also from that b_limit have "(\<lambda>x. b x powr 0) \<in> o(\<lambda>x. b x powr e)"
        by (subst powr_smallo_iff) simp_all
      finally show ?thesis .
    qed
    moreover from G have "ms_exp_gt 0 (ms_aux_hd_exp (times_ms_aux G (powser_ms_aux cs' G)))"
      by (cases "ms_aux_hd_exp G") (simp_all add: hd_exp_times MSLCons hd_exp_powser)
    ultimately show ?thesis
      by (simp add: MSLCons powser_ms_aux_MSLCons basis')
  qed
qed (insert assms, simp_all)
  
lemma powser_ms_aux':
  assumes powser: "convergent_powser' cs f" and basis: "basis_wf basis"
  assumes G: "is_expansion_aux G g basis" "ms_exp_gt 0 (ms_aux_hd_exp G)"
  shows   "is_expansion_aux (powser_ms_aux cs G) (f \<circ> g) basis"
proof (rule is_expansion_aux_cong)
  from is_expansion_aux_basis_nonempty[OF G(1)] basis
    have "filterlim (hd basis) at_top at_top" by (cases basis) (simp_all add: basis_wf_Cons)
  hence pos: "eventually (\<lambda>x. hd basis x > 0) at_top" by (simp add: filterlim_at_top_dense)
  from G(2) have "g \<in> o(\<lambda>x. hd basis x powr 0)"
    by (intro is_expansion_aux_imp_smallo[OF G(1)]) simp
  also have "(\<lambda>x. hd basis x powr 0) \<in> \<Theta>(\<lambda>x. 1)" 
     using pos by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally have g_limit: "(g \<longlongrightarrow> 0) at_top" by (auto dest: smalloD_tendsto)
  
  from powser have "eventually (\<lambda>x. powser cs x = f x) (nhds 0)"
    by (rule convergent_powser'_eventually)
  from this and g_limit show "eventually (\<lambda>x. (powser cs \<circ> g) x = (f \<circ> g) x) at_top" 
    unfolding o_def by (rule eventually_compose_filterlim)
qed (rule assms powser_ms_aux convergent_powser'_imp_convergent_powser)+

lemma inverse_ms_aux:
  assumes basis: "basis_wf basis"
  assumes F: "is_expansion_aux F f basis" "trimmed_ms_aux F"
  shows   "is_expansion_aux (inverse_ms_aux F) (\<lambda>x. inverse (f x)) basis"
proof (cases F rule: ms_aux_cases)
  case (MSLCons C e F')
  from F MSLCons obtain b basis' where F': "basis = b # basis'" "trimmed C"
    "is_expansion_aux F' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "is_expansion C basis'" "(\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'))" 
    "ms_exp_gt e (ms_aux_hd_exp F')"
    by (auto elim!: is_expansion_aux_MSLCons simp: trimmed_ms_aux_def)
  define f' where "f' = (\<lambda>x. f x - eval C x * b x powr e)"
  from basis F' have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  moreover from F'(6)
    have "ms_exp_gt 0 (ms_aux_hd_exp (scale_shift_ms_aux (inverse C, - e) F'))"
    by (cases "ms_aux_hd_exp F'") (simp_all add: hd_exp_basis)
  ultimately have
       "is_expansion_aux (inverse_ms_aux F) 
          (\<lambda>x. eval (inverse C) x * b x powr (-e) * 
                 ((\<lambda>x. inverse (1 + x)) \<circ> (\<lambda>x. eval (inverse C) x * b x powr (-e) * f' x)) x)
          (b # basis')" (is "is_expansion_aux _ ?h _")
    unfolding MSLCons inverse_ms_aux.simps Let_def fst_conv snd_conv f'_def eval_inverse [symmetric]
    using basis F(2) F'(1,3,4)
    by (intro scale_shift_ms_aux powser_ms_aux' is_expansion_inverse)
       (simp_all add: convergent_powser'_geometric basis_wf_Cons trimmed_ms_aux_def MSLCons)
  also have "b # basis' = basis" by (simp add: F')
  finally show ?thesis
  proof (rule is_expansion_aux_cong, goal_cases)
    case 1
    from basis F' have "eventually (\<lambda>x. eval C x \<noteq> 0) at_top" 
      by (intro trimmed_imp_eventually_nz[of basis']) (simp_all add: basis_wf_Cons)
    with b_pos show ?case by eventually_elim (simp add: o_def field_simps powr_minus f'_def)
  qed
qed (insert assms, auto simp: trimmed_ms_aux_def)

lemma hd_exp_inverse: 
  "xs \<noteq> MSLNil \<Longrightarrow> ms_aux_hd_exp (inverse_ms_aux xs) = map_option uminus (ms_aux_hd_exp xs)"
  by (cases xs) (auto simp: Let_def hd_exp_basis hd_exp_powser inverse_ms_aux.simps)

lemma eval_pos_if_dominant_term_pos:
  assumes "basis_wf basis" "is_expansion F basis" "trimmed F"
          "fst (dominant_term F) > 0"
  shows   "eventually (\<lambda>x. eval F x > 0) at_top"
proof -
  have "eval F \<sim>[at_top] eval_monom (dominant_term F) basis"
    by (intro dominant_term assms)
  from trimmed_imp_eventually_sgn[OF assms(1-3)]
    have "\<forall>\<^sub>F x in at_top. sgn (eval F x) = sgn (fst (dominant_term F))" .
  moreover from assms
    have "eventually (\<lambda>x. eval_monom (dominant_term F) basis x > 0) at_top"
    by (intro eval_monom_pos)
  ultimately show ?thesis by eventually_elim (insert assms, simp add: sgn_if split: if_splits)
qed

lemma eval_pos_if_dominant_term_pos':
  assumes "basis_wf basis" "trimmed_ms_aux F" "is_expansion_aux F f basis" 
          "fst (dominant_term_ms_aux F) > 0"
  shows   "eventually (\<lambda>x. f x > 0) at_top"
proof -
  have "f \<sim>[at_top] eval_monom (dominant_term_ms_aux F) basis"
    by (intro dominant_term_ms_aux assms)
  from dominant_term_ms_aux(2)[OF assms(1-3)]
    have "\<forall>\<^sub>F x in at_top. sgn (f x) = sgn (fst (dominant_term_ms_aux F))" .
  moreover from assms
    have "eventually (\<lambda>x. eval_monom (dominant_term_ms_aux F) basis x > 0) at_top"
    by (intro eval_monom_pos)
  ultimately show ?thesis by eventually_elim (insert assms, simp add: sgn_if split: if_splits)
qed
  
lemma eval_neg_if_dominant_term_neg':
  assumes "basis_wf basis" "trimmed_ms_aux F" "is_expansion_aux F f basis" 
          "fst (dominant_term_ms_aux F) < 0"
  shows   "eventually (\<lambda>x. f x < 0) at_top"
proof -
  have "f \<sim>[at_top] eval_monom (dominant_term_ms_aux F) basis"
    by (intro dominant_term_ms_aux assms)
  from dominant_term_ms_aux(2)[OF assms(1-3)]
    have "\<forall>\<^sub>F x in at_top. sgn (f x) = sgn (fst (dominant_term_ms_aux F))" .
  moreover from assms
  have "eventually (\<lambda>x. eval_monom (dominant_term_ms_aux F) basis x < 0) at_top"
    by (intro eval_monom_neg)
  ultimately show ?thesis by eventually_elim (insert assms, simp add: sgn_if split: if_splits)
qed

lemma fst_dominant_term_ms_aux_MSLCons: 
  "fst (dominant_term_ms_aux (MSLCons x xs)) = fst (dominant_term (fst x))"
  by (auto simp: dominant_term_ms_aux_def split: prod.splits)

lemma powr_ms_aux:
  assumes basis: "basis_wf basis"
  assumes F: "is_expansion_aux F f basis" "trimmed_ms_aux F" "fst (dominant_term_ms_aux F) > 0"
  shows   "is_expansion_aux (powr_ms_aux abort F p) (\<lambda>x.  f x powr p) basis"
proof (cases F rule: ms_aux_cases)
  case (MSLCons C e F')
  from F MSLCons obtain b basis' where F': "basis = b # basis'" "trimmed C" "fst (dominant_term C) > 0"
    "is_expansion_aux F' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "is_expansion C basis'" "(\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'))"
    "ms_exp_gt e (ms_aux_hd_exp F')"
    by (auto elim!: is_expansion_aux_MSLCons simp: trimmed_ms_aux_def dominant_term_ms_aux_def 
             split: prod.splits)
  define f' where "f' = (\<lambda>x. f x - eval C x * b x powr e)"
  from basis F' have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  moreover from F' have "ms_exp_gt 0 (ms_aux_hd_exp (scale_shift_ms_aux (inverse C, - e) F'))"
    by (cases "ms_aux_hd_exp F'") (simp_all add: hd_exp_basis)
  ultimately have
       "is_expansion_aux (powr_ms_aux abort F p) 
          (\<lambda>x. eval (powr_expansion abort C p) x * b x powr (e * p) * 
                 ((\<lambda>x. (1 + x) powr p) \<circ> (\<lambda>x. eval (inverse C) x * b x powr (-e) * f' x)) x)
          (b # basis')" (is "is_expansion_aux _ ?h _")
    unfolding MSLCons powr_ms_aux.simps Let_def fst_conv snd_conv f'_def eval_inverse [symmetric]
        using basis F'(1-5)
    by (intro scale_shift_ms_aux powser_ms_aux' is_expansion_inverse is_expansion_powr)
       (simp_all add: MSLCons basis_wf_Cons convergent_powser'_gbinomial)
  also have "b # basis' = basis" by (simp add: F')
  finally show ?thesis
  proof (rule is_expansion_aux_cong, goal_cases)
    case 1
    from basis F' have "eventually (\<lambda>x. eval C x > 0) at_top" 
      by (intro eval_pos_if_dominant_term_pos[of basis']) (simp_all add: basis_wf_Cons)
    moreover from basis F have "eventually (\<lambda>x. f x > 0) at_top"
      by (intro eval_pos_if_dominant_term_pos'[of basis F])
    ultimately show ?case using b_pos
      by eventually_elim 
         (simp add: powr_powr [symmetric] powr_minus powr_mult powr_divide f'_def field_simps)
  qed
qed (insert assms, auto simp: trimmed_ms_aux_def)

lemma power_ms_aux:
  assumes basis: "basis_wf basis"
  assumes F: "is_expansion_aux F f basis" "trimmed_ms_aux F"
  shows   "is_expansion_aux (power_ms_aux abort F n) (\<lambda>x. f x ^ n) basis"
proof (cases F rule: ms_aux_cases)
  case (MSLCons C e F')
  from F MSLCons obtain b basis' where F': "basis = b # basis'" "trimmed C"
    "is_expansion_aux F' (\<lambda>x. f x - eval C x * b x powr e) (b # basis')"
    "is_expansion C basis'" "(\<And>e'. e < e' \<Longrightarrow> f \<in> o(\<lambda>x. b x powr e'))" 
    "ms_exp_gt e (ms_aux_hd_exp F')"
    by (auto elim!: is_expansion_aux_MSLCons simp: trimmed_ms_aux_def dominant_term_ms_aux_def 
             split: prod.splits)
  define f' where "f' = (\<lambda>x. f x - eval C x * b x powr e)"
  from basis F' have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  moreover have "ms_exp_gt 0 (ms_aux_hd_exp (scale_shift_ms_aux (inverse C, - e) F'))"
    using F'(6) by (cases "ms_aux_hd_exp F'") (simp_all add: hd_exp_basis)
  ultimately have
       "is_expansion_aux (power_ms_aux abort F n) 
          (\<lambda>x. eval (power_expansion abort C n) x * b x powr (e * real n) * 
                 ((\<lambda>x. (1 + x) ^ n) \<circ> (\<lambda>x. eval (inverse C) x * b x powr (-e) * f' x)) x)
          (b # basis')" (is "is_expansion_aux _ ?h _")
    unfolding MSLCons power_ms_aux.simps Let_def fst_conv snd_conv f'_def eval_inverse [symmetric]
        using basis F'(1-4)
    by (intro scale_shift_ms_aux powser_ms_aux' is_expansion_inverse is_expansion_power)
       (simp_all add: MSLCons basis_wf_Cons convergent_powser'_gbinomial')
  also have "b # basis' = basis" by (simp add: F')
  finally show ?thesis
  proof (rule is_expansion_aux_cong, goal_cases)
    case 1
    from F'(1,2,4) basis have "eventually (\<lambda>x. eval C x \<noteq> 0) at_top"
      using trimmed_imp_eventually_nz[of basis' C] by (simp add: basis_wf_Cons)
    thus ?case using b_pos
      by eventually_elim
         (simp add: field_simps f'_def powr_minus powr_powr [symmetric] powr_realpow 
                    power_mult_distrib [symmetric] power_divide [symmetric]
               del: power_mult_distrib power_divide)
  qed
qed (insert assms, auto simp: trimmed_ms_aux_def)

lemma snd_dominant_term_ms_aux_MSLCons:
  "snd (dominant_term_ms_aux (MSLCons (C, e) xs)) = e # snd (dominant_term C)"
  by (simp add: dominant_term_ms_aux_def case_prod_unfold)


subsubsection \<open>Type-class instantiations\<close>

datatype 'a ms = MS "('a \<times> real) msllist" "real \<Rightarrow> real"

instantiation ms :: (uminus) uminus
begin

primrec uminus_ms where
  "-(MS xs f) = MS (uminus_ms_aux xs) (\<lambda>x. -f x)"
  
instance ..
end

instantiation ms :: (plus) plus
begin

fun plus_ms :: "'a ms \<Rightarrow> 'a ms \<Rightarrow> 'a ms" where
  "MS xs f + MS ys g = MS (plus_ms_aux xs ys) (\<lambda>x. f x + g x)"

instance ..
end

instantiation ms :: ("{plus,uminus}") minus
begin

definition minus_ms :: "'a ms \<Rightarrow> 'a ms \<Rightarrow> 'a ms" where
  "F - G = F + -(G :: 'a ms)"

instance ..
end

instantiation ms :: ("{plus,times}") times
begin

fun times_ms :: "'a ms \<Rightarrow> 'a ms \<Rightarrow> 'a ms" where
  "MS xs f * MS ys g = MS (times_ms_aux xs ys) (\<lambda>x. f x * g x)"

instance ..
end

instantiation ms :: (multiseries) inverse
begin

fun inverse_ms :: "'a ms \<Rightarrow> 'a ms" where
  "inverse_ms (MS xs f) = MS (inverse_ms_aux xs) (\<lambda>x. inverse (f x))"

fun divide_ms :: "'a ms \<Rightarrow> 'a ms \<Rightarrow> 'a ms" where
  "divide_ms (MS xs f) (MS ys g) = MS (times_ms_aux xs (inverse_ms_aux ys)) (\<lambda>x. f x / g x)"

instance ..
end


instantiation ms :: (multiseries) multiseries
begin

definition expansion_level_ms :: "'a ms itself \<Rightarrow> nat" where
  expansion_level_ms_def [simp]: "expansion_level_ms _ = Suc (expansion_level (TYPE('a)))"

definition zero_expansion_ms :: "'a ms" where
  "zero_expansion = MS MSLNil (\<lambda>_. 0)"

definition const_expansion_ms :: "real \<Rightarrow> 'a ms" where
  "const_expansion c = MS (const_ms_aux c) (\<lambda>_. c)"

primrec is_expansion_ms :: "'a ms \<Rightarrow> basis \<Rightarrow> bool" where
  "is_expansion (MS xs f) = is_expansion_aux xs f"

lemma is_expansion_ms_def': "is_expansion F = (case F of MS xs f \<Rightarrow> is_expansion_aux xs f)"
  by (simp add: is_expansion_ms_def split: ms.splits)

primrec eval_ms :: "'a ms \<Rightarrow> real \<Rightarrow> real" where
  "eval_ms (MS _ f) = f"
  
lemma eval_ms_def': "eval F = (case F of MS _ f \<Rightarrow> f)"
  by (cases F) simp_all

primrec powr_expansion_ms :: "bool \<Rightarrow> 'a ms \<Rightarrow> real \<Rightarrow> 'a ms" where
  "powr_expansion_ms abort (MS xs f) p = MS (powr_ms_aux abort xs p) (\<lambda>x. f x powr p)"
  
primrec power_expansion_ms :: "bool \<Rightarrow> 'a ms \<Rightarrow> nat \<Rightarrow> 'a ms" where
  "power_expansion_ms abort (MS xs f) n = MS (power_ms_aux abort xs n) (\<lambda>x. f x ^ n)"

primrec trimmed_ms :: "'a ms \<Rightarrow> bool" where
  "trimmed_ms (MS xs _) \<longleftrightarrow> trimmed_ms_aux xs"

primrec dominant_term_ms :: "'a ms \<Rightarrow> monom" where
  "dominant_term_ms (MS xs _) = dominant_term_ms_aux xs"

lemma length_dominant_term_ms: 
  "length (snd (dominant_term (F :: 'a ms))) = Suc (expansion_level TYPE('a))"
  by (cases F) (simp_all add: length_dominant_term)  

instance 
proof (standard, goal_cases length_basis zero const uminus plus minus times 
         inverse divide powr power smallo smallomega trimmed dominant dominant_bigo)
  case (smallo basis F b e)
  from \<open>is_expansion F basis\<close> obtain xs f where F: "F = MS xs f" "is_expansion_aux xs f basis"
    by (simp add: is_expansion_ms_def' split: ms.splits)
  from F(2) have nonempty: "basis \<noteq> []" by (rule is_expansion_aux_basis_nonempty)
  with smallo have filterlim_hd_basis: "filterlim (hd basis) at_top at_top"
    by (cases basis) (simp_all add: basis_wf_Cons)
  from F(2) obtain e' where "f \<in> o(\<lambda>x. hd basis x powr e')"
    by (erule is_expansion_aux_imp_smallo')
  also from smallo nonempty filterlim_hd_basis have "(\<lambda>x. hd basis x powr e') \<in> o(\<lambda>x. b x powr e)"
    by (intro ln_smallo_imp_flat) auto
  finally show ?case by (simp add: F)
next
  case (smallomega basis F b e)
  obtain xs f where F: "F = MS xs f" by (cases F) simp_all
  from this smallomega have *: "is_expansion_aux xs f basis" by simp
  with smallomega F have "f \<in> \<omega>(\<lambda>x. b x powr e)"
    by (intro is_expansion_aux_imp_smallomega [OF _ *])
       (simp_all add: is_expansion_ms_def' split: ms.splits)
  with F show ?case by simp
next
  case (minus basis F G)
  thus ?case
    by (simp add: minus_ms_def is_expansion_ms_def' add_uminus_conv_diff [symmetric] 
                  plus_ms_aux uminus_ms_aux del: add_uminus_conv_diff split: ms.splits)
next
  case (divide basis F G)
  have "G / F = G * inverse F" by (cases F; cases G) (simp add: divide_inverse)
  with divide show ?case
    by (simp add: is_expansion_ms_def' divide_inverse times_ms_aux inverse_ms_aux split: ms.splits)
next
  fix c :: real
  show "trimmed (const_expansion c :: 'a ms) \<longleftrightarrow> c \<noteq> 0"
    by (simp add: const_expansion_ms_def trimmed_ms_aux_def const_ms_aux_def 
                  trimmed_const_expansion split: msllist.splits)
next
  fix F :: "'a ms" assume "trimmed F"
  thus "fst (dominant_term F) \<noteq> 0"
    by (cases F) (auto simp: dominant_term_ms_aux_def trimmed_ms_aux_MSLCons case_prod_unfold 
                    trimmed_imp_dominant_term_nz split: msllist.splits)
next
  fix F :: "'a ms"
  have "times_ms_aux (MSLCons (const_expansion 1, 0) MSLNil) xs = xs" for xs :: "('a \<times> real) msllist"
  proof (coinduction arbitrary: xs rule: msllist.coinduct_upto)
    case Eq_real_prod_msllist
    have "map_prod ((*) (const_expansion 1 :: 'a)) ((+) (0::real)) = (\<lambda>x. x)"
      by (rule ext) (simp add: map_prod_def times_const_expansion_1 case_prod_unfold)
    moreover have "mslmap \<dots> = (\<lambda>x. x)" by (rule ext) (simp add: msllist.map_ident)
    ultimately have "scale_shift_ms_aux (const_expansion 1 :: 'a, 0) = (\<lambda>x. x)"
      by (simp add: scale_shift_ms_aux_conv_mslmap)
    thus ?case
      by (cases xs rule: ms_aux_cases)
         (auto simp: times_ms_aux_MSLCons times_const_expansion_1
            times_ms_aux.corec.cong_refl)
  qed
  thus "const_expansion 1 * F = F"
    by (cases F) (simp add: const_expansion_ms_def const_ms_aux_def)
next
  fix F :: "'a ms"
  show "fst (dominant_term (- F)) = - fst (dominant_term F)"
       "trimmed (-F) \<longleftrightarrow> trimmed F"
     by (cases F; simp add: dominant_term_ms_aux_def case_prod_unfold uminus_ms_aux_MSLCons
           trimmed_ms_aux_def split: msllist.splits)+
next
  fix F :: "'a ms"
  show "zero_expansion + F = F" "F + zero_expansion = F"
    by (cases F; simp add: zero_expansion_ms_def)+
qed (auto simp: eval_ms_def' const_expansion_ms_def trimmed_ms_aux_imp_nz is_expansion_ms_def' 
                 const_ms_aux uminus_ms_aux plus_ms_aux times_ms_aux inverse_ms_aux 
                 is_expansion_aux_expansion_level dominant_term_ms_aux length_dominant_term_ms
                 minus_ms_def powr_ms_aux power_ms_aux zero_expansion_ms_def 
                 is_expansion_aux.intros(1) dominant_term_ms_aux_bigo
          split: ms.splits)

end


subsubsection \<open>Changing the evaluation function of a multiseries\<close>

definition modify_eval :: "(real \<Rightarrow> real) \<Rightarrow> 'a ms \<Rightarrow> 'a ms" where
  "modify_eval f F = (case F of MS xs _ \<Rightarrow> MS xs f)"

lemma eval_modify_eval [simp]: "eval (modify_eval f F) = f"
  by (cases F) (simp add: modify_eval_def)


subsubsection \<open>Scaling expansions\<close>

definition scale_ms :: "real \<Rightarrow> 'a :: multiseries \<Rightarrow> 'a" where
  "scale_ms c F = const_expansion c * F"

lemma scale_ms_real [simp]: "scale_ms c (c' :: real) = c * c'"
  by (simp add: scale_ms_def)

definition scale_ms_aux :: "real \<Rightarrow> ('a :: multiseries \<times> real) msllist \<Rightarrow> ('a \<times> real) msllist" where
  "scale_ms_aux c xs = scale_shift_ms_aux (const_expansion c, 0) xs"


lemma scale_ms_aux_eq_MSLNil_iff [simp]: "scale_ms_aux x xs = MSLNil \<longleftrightarrow> xs = MSLNil"
  unfolding scale_ms_aux_def by simp

lemma times_ms_aux_singleton:
  "times_ms_aux (MSLCons (c, e) MSLNil) xs = scale_shift_ms_aux (c, e) xs"
proof (coinduction arbitrary: xs rule: msllist.coinduct_strong)
  case (Eq_msllist xs)
  thus ?case
    by (cases xs rule: ms_aux_cases)
       (simp_all add: scale_shift_ms_aux_def times_ms_aux_MSLCons)
qed

lemma scale_ms [simp]: "scale_ms c (MS xs f) = MS (scale_ms_aux c xs) (\<lambda>x. c * f x)"
  by (simp add: scale_ms_def scale_ms_aux_def const_expansion_ms_def const_ms_aux_def 
        times_ms_aux_singleton)

lemma scale_ms_aux_MSLNil [simp]: "scale_ms_aux c MSLNil = MSLNil" 
  by (simp add: scale_ms_aux_def)

lemma scale_ms_aux_MSLCons: 
  "scale_ms_aux c (MSLCons (c', e) xs) = MSLCons (scale_ms c c', e) (scale_ms_aux c xs)"
  by (simp add: scale_ms_aux_def scale_shift_ms_aux_MSLCons scale_ms_def)


subsubsection \<open>Additional convenience rules\<close>

lemma trimmed_pos_real_iff [simp]: "trimmed_pos (x :: real) \<longleftrightarrow> x > 0"
  by (auto simp: trimmed_pos_def)

lemma trimmed_pos_ms_iff: 
  "trimmed_pos (MS xs f) \<longleftrightarrow> (case xs of MSLNil \<Rightarrow> False | MSLCons x xs \<Rightarrow> trimmed_pos (fst x))"
  by (auto simp add: trimmed_pos_def dominant_term_ms_aux_def trimmed_ms_aux_def
           split: msllist.splits prod.splits)

lemma not_trimmed_pos_MSLNil [simp]: "\<not>trimmed_pos (MS MSLNil f)"
  by (simp add: trimmed_pos_ms_iff)

lemma trimmed_pos_MSLCons [simp]: "trimmed_pos (MS (MSLCons x xs) f) = trimmed_pos (fst x)"
  by (simp add: trimmed_pos_ms_iff)

lemma drop_zero_ms:
  assumes "eventually (\<lambda>x. eval C x = 0) at_top"
  assumes "is_expansion (MS (MSLCons (C, e) xs) f) basis"
  shows   "is_expansion (MS xs f) basis"
  using assms by (auto simp: is_expansion_ms_def intro: drop_zero_ms_aux)

lemma expansion_level_eq_Nil: "length [] = expansion_level TYPE(real)" by simp
lemma expansion_level_eq_Cons: 
  "length xs = expansion_level TYPE('a::multiseries) \<Longrightarrow>
     length (x # xs) = expansion_level TYPE('a ms)" by simp

lemma basis_wf_insert_ln: 
  assumes "basis_wf [b]"
  shows   "basis_wf [\<lambda>x. ln (b x)]" (is ?thesis1)
          "basis_wf [b, \<lambda>x. ln (b x)]" (is ?thesis2)
          "is_expansion (MS (MSLCons (1::real,1) MSLNil) (\<lambda>x. ln (b x))) [\<lambda>x. ln (b x)]" (is ?thesis3)
proof -
  have "ln \<in> o(\<lambda>x. x :: real)"
    using ln_x_over_x_tendsto_0 by (intro smalloI_tendsto) auto
  with assms show ?thesis1 ?thesis2
    by (auto simp: basis_wf_Cons
          intro!: landau_o.small.compose[of _ _ _ "\<lambda>x. ln (b x)"] filterlim_compose[OF ln_at_top])
  from assms have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence ev: "eventually (\<lambda>x. b x > 1) at_top" by (simp add: filterlim_at_top_dense)
  have "(\<lambda>x::real. x) \<in> \<Theta>(\<lambda>x. x powr 1)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  also have "(\<lambda>x::real. x powr 1) \<in> o(\<lambda>a. a powr e)" if "e > 1" for e
    by (subst powr_smallo_iff) (auto simp: that filterlim_ident)
  finally show ?thesis3 using assms ev
    by (auto intro!: is_expansion_aux.intros landau_o.small.compose[of _ at_top _ "\<lambda>x. ln (b x)"]
                     filterlim_compose[OF ln_at_top b_limit] is_expansion_real.intros
             elim!: eventually_mono)
qed

lemma basis_wf_lift_modification:
  assumes "basis_wf (b' # b # bs)" "basis_wf (b # bs')"
  shows   "basis_wf (b' # b # bs')"
  using assms by (simp add: basis_wf_many)

lemma default_basis_wf: "basis_wf [\<lambda>x. x]" 
  by (simp add: basis_wf_Cons filterlim_ident)

  
subsubsection \<open>Lifting expansions\<close>

definition is_lifting where
  "is_lifting f basis basis' \<longleftrightarrow> 
     (\<forall>C. eval (f C) = eval C \<and> (is_expansion C basis \<longrightarrow> is_expansion (f C) basis') \<and>
          trimmed (f C) = trimmed C \<and> fst (dominant_term (f C)) = fst (dominant_term C))"
  
lemma is_liftingD:
  assumes "is_lifting f basis basis'"
  shows   "eval (f C) = eval C" "is_expansion C basis \<Longrightarrow> is_expansion (f C) basis'"
          "trimmed (f C) \<longleftrightarrow> trimmed C" "fst (dominant_term (f C)) = fst (dominant_term C)"
  using assms [unfolded is_lifting_def] unfolding is_lifting_def by blast+
  

definition lift_ms :: "'a :: multiseries \<Rightarrow> 'a ms" where
  "lift_ms C = MS (MSLCons (C, 0) MSLNil) (eval C)"

lemma is_expansion_lift:
  assumes "basis_wf (b # basis)" "is_expansion C basis"
  shows   "is_expansion (lift_ms C) (b # basis)"
proof -
  from assms have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  moreover from assms have "eval C \<in> o(\<lambda>x. b x powr e)" if "e > 0" for e
    using that by (intro is_expansion_imp_smallo[OF _ assms(2)]) (simp_all add: basis_wf_Cons)
  ultimately show ?thesis using assms
    by (auto intro!: is_expansion_aux.intros simp: lift_ms_def is_expansion_length 
             elim: eventually_mono)
qed

lemma eval_lift_ms [simp]: "eval (lift_ms C) = eval C"
  by (simp add: lift_ms_def)

lemma is_lifting_lift:
  assumes "basis_wf (b # basis)"
  shows   "is_lifting lift_ms basis (b # basis)"
  using is_expansion_lift[OF assms] unfolding is_lifting_def
  by (auto simp: lift_ms_def trimmed_ms_aux_MSLCons dominant_term_ms_aux_def case_prod_unfold)


definition map_ms_aux :: 
    "('a :: multiseries \<Rightarrow> 'b :: multiseries) \<Rightarrow> 
       ('a \<times> real) msllist \<Rightarrow> ('b \<times> real) msllist" where
  "map_ms_aux f xs = mslmap (\<lambda>(c,e). (f c, e)) xs"

lemma map_ms_aux_MSLNil [simp]: "map_ms_aux f MSLNil = MSLNil"
  by (simp add: map_ms_aux_def)

lemma map_ms_aux_MSLCons: "map_ms_aux f (MSLCons (C, e) xs) = MSLCons (f C, e) (map_ms_aux f xs)"
  by (simp add: map_ms_aux_def)

lemma hd_exp_map [simp]: "ms_aux_hd_exp (map_ms_aux f xs) = ms_aux_hd_exp xs"
  by (simp add: ms_aux_hd_exp_def map_ms_aux_def split: msllist.splits)

lemma map_ms_altdef: "map_ms f (MS xs g) = MS (map_ms_aux f xs) g"
  by (simp add: map_ms_aux_def map_prod_def)

lemma eval_map_ms [simp]: "eval (map_ms f F) = eval F"
  by (cases F) simp_all

lemma is_expansion_map_aux:
  fixes f :: "'a :: multiseries \<Rightarrow> 'b :: multiseries"
  assumes "is_expansion_aux xs g (b # basis)"
  assumes "\<And>C. is_expansion C basis \<Longrightarrow> is_expansion (f C) basis'"
  assumes "length basis' = expansion_level TYPE('b)"
  assumes "\<And>C. eval (f C) = eval C"
  shows   "is_expansion_aux (map_ms_aux f xs) g (b # basis')"
  using assms(1)
proof (coinduction arbitrary: xs g rule: is_expansion_aux_coinduct)
  case (is_expansion_aux xs g)
  show ?case
  proof (cases xs rule: ms_aux_cases)
    case MSLNil
    with is_expansion_aux show ?thesis
      by (auto simp: assms elim: is_expansion_aux.cases)
  next
    case (MSLCons c e xs')
    with is_expansion_aux show ?thesis
      by (auto elim!: is_expansion_aux_MSLCons simp: map_ms_aux_MSLCons assms)
  qed    
qed

lemma is_expansion_map:
  fixes f :: "'a :: multiseries \<Rightarrow> 'b :: multiseries"
    and F :: "'a ms"
  assumes "is_expansion G (b # basis)"
  assumes "\<And>C. is_expansion C basis \<Longrightarrow> is_expansion (f C) basis'"
  assumes "\<And>C. eval (f C) = eval C"
  assumes "length basis' = expansion_level TYPE('b)"
  shows   "is_expansion (map_ms f G) (b # basis')"
  using assms by (cases G, simp only: map_ms_altdef) (auto intro!: is_expansion_map_aux)

lemma is_expansion_map_final: 
  fixes f :: "'a :: multiseries \<Rightarrow> 'b :: multiseries"
    and F :: "'a ms"
  assumes "is_lifting f basis basis'"
  assumes "is_expansion G (b # basis)"
  assumes "length basis' = expansion_level TYPE('b)"
  shows   "is_expansion (map_ms f G) (b # basis')"
  by (rule is_expansion_map[OF assms(2)]) (insert assms, simp_all add: is_lifting_def)

lemma fst_dominant_term_map_ms: 
  "is_lifting f basis basis' \<Longrightarrow> fst (dominant_term (map_ms f C)) = fst (dominant_term C)"
  by (cases C)
     (simp add: dominant_term_ms_aux_def case_prod_unfold is_lifting_def split: msllist.splits)

lemma trimmed_map_ms:
  "is_lifting f basis basis' \<Longrightarrow> trimmed (map_ms f C) \<longleftrightarrow> trimmed C"
  by (cases C) (simp add: trimmed_ms_aux_def is_lifting_def split: msllist.splits)

lemma is_lifting_map: 
  fixes f :: "'a :: multiseries \<Rightarrow> 'b :: multiseries"
    and F :: "'a ms"
  assumes "is_lifting f basis basis'"
  assumes "length basis' = expansion_level TYPE('b)"
  shows   "is_lifting (map_ms f) (b # basis) (b # basis')"
  unfolding is_lifting_def
  by (intro allI conjI impI is_expansion_map_final[OF assms(1)]) 
     (insert assms, simp_all add: is_lifting_def fst_dominant_term_map_ms[OF assms(1)] 
        trimmed_map_ms[OF assms(1)])

lemma is_lifting_id: "is_lifting (\<lambda>x. x) basis basis"
  by (simp add: is_lifting_def)

lemma is_lifting_trans: 
  "is_lifting f basis basis' \<Longrightarrow> is_lifting g basis' basis'' \<Longrightarrow> is_lifting (\<lambda>x. g (f x)) basis basis''"
  by (auto simp: is_lifting_def)

lemma is_expansion_X: "is_expansion (MS (MSLCons (1 :: real, 1) MSLNil) (\<lambda>x. x)) [\<lambda>x. x]"
proof -
  have "(\<lambda>x::real. x) \<in> \<Theta>(\<lambda>x. x powr 1)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  also have "(\<lambda>x::real. x powr 1) \<in> o(\<lambda>a. a powr e)" if "e > 1" for e
    by (subst powr_smallo_iff) (auto simp: that filterlim_ident)
  finally show ?thesis  
    by (auto intro!: is_expansion_aux.intros is_expansion_real.intros 
                     eventually_mono[OF eventually_gt_at_top[of "0::real"]])
qed


inductive expands_to :: "(real \<Rightarrow> real) \<Rightarrow> 'a :: multiseries \<Rightarrow> basis \<Rightarrow> bool" 
    (infix \<open>(expands'_to)\<close> 50) where
  "is_expansion F basis \<Longrightarrow> eventually (\<lambda>x. eval F x = f x) at_top \<Longrightarrow> (f expands_to F) basis"

lemma dominant_term_expands_to:
  assumes "basis_wf basis" "(f expands_to F) basis" "trimmed F"
  shows   "f \<sim>[at_top] eval_monom (dominant_term F) basis"
proof -
  from assms have "eval F \<sim>[at_top] f" by (intro asymp_equiv_refl_ev) (simp add: expands_to.simps)
  also from dominant_term[OF assms(1) _ assms(3)] assms(2)
    have "eval F \<sim>[at_top] eval_monom (dominant_term F) basis" by (simp add: expands_to.simps)
  finally show ?thesis by (subst asymp_equiv_sym) simp_all
qed

lemma expands_to_cong:
  "(f expands_to F) basis \<Longrightarrow> eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> (g expands_to F) basis"
  by (auto simp: expands_to.simps elim: eventually_elim2)

lemma expands_to_cong':
  assumes "(f expands_to MS xs g) basis" "eventually (\<lambda>x. g x = g' x) at_top"
  shows   "(f expands_to MS xs g') basis"
proof -
  have "is_expansion_aux xs g' basis"
    by (rule is_expansion_aux_cong [OF _ assms(2)]) (insert assms(1), simp add: expands_to.simps)
  with assms show ?thesis
    by (auto simp: expands_to.simps elim: eventually_elim2)
qed

lemma eval_expands_to: "(f expands_to F) basis \<Longrightarrow> eventually (\<lambda>x. eval F x = f x) at_top"
  by (simp add: expands_to.simps)

lemma expands_to_real_compose:
  assumes "(f expands_to (c::real)) bs"
  shows   "((\<lambda>x. g (f x)) expands_to g c) bs"
  using assms by (auto simp: expands_to.simps is_expansion_real.simps elim: eventually_mono)

lemma expands_to_lift_compose:
  assumes "(f expands_to MS (MSLCons (C, e) xs) f') bs'"
  assumes "eventually (\<lambda>x. f' x - h x = 0) at_top" "e = 0"
  assumes "((\<lambda>x. g (h x)) expands_to G) bs" "basis_wf (b # bs)"
  shows   "((\<lambda>x. g (f x)) expands_to lift_ms G) (b # bs)"
proof -
  from assms have "\<forall>\<^sub>F x in at_top. f' x = f x" "\<forall>\<^sub>F x in at_top. eval G x = g (h x)"
    by (auto simp: expands_to.simps)
  with assms(2) have "\<forall>\<^sub>F x in at_top. eval G x = g (f x)"
    by eventually_elim simp
  with assms show ?thesis
    by (intro expands_to.intros is_expansion_lift) (auto simp: expands_to.simps)
qed

lemma expands_to_zero: 
    "basis_wf basis \<Longrightarrow> length basis = expansion_level TYPE('a) \<Longrightarrow>
       ((\<lambda>_. 0) expands_to (zero_expansion :: 'a :: multiseries)) basis"
  by (auto simp add: expands_to.simps is_expansion_zero)
  
lemma expands_to_const: 
    "basis_wf basis \<Longrightarrow> length basis = expansion_level TYPE('a) \<Longrightarrow>
       ((\<lambda>_. c) expands_to (const_expansion c :: 'a :: multiseries)) basis"
  by (auto simp add: expands_to.simps is_expansion_const)

lemma expands_to_X: "((\<lambda>x. x) expands_to MS (MSLCons (1 :: real, 1) MSLNil) (\<lambda>x. x)) [\<lambda>x. x]"
  using is_expansion_X by (simp add: expands_to.simps)
    
lemma expands_to_uminus:
  "basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> ((\<lambda>x. -f x) expands_to -F) basis"
  by (auto simp: expands_to.simps is_expansion_uminus)

lemma expands_to_add:
  "basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> (g expands_to G) basis \<Longrightarrow>
     ((\<lambda>x. f x + g x) expands_to F + G) basis"
  by (auto simp: expands_to.simps is_expansion_add elim: eventually_elim2)

lemma expands_to_minus:
  "basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> (g expands_to G) basis \<Longrightarrow>
     ((\<lambda>x. f x - g x) expands_to F - G) basis"
  by (auto simp: expands_to.simps is_expansion_minus elim: eventually_elim2)

lemma expands_to_mult:
  "basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> (g expands_to G) basis \<Longrightarrow>
     ((\<lambda>x. f x * g x) expands_to F * G) basis"
  by (auto simp: expands_to.simps is_expansion_mult elim: eventually_elim2)

lemma expands_to_inverse:
  "trimmed F \<Longrightarrow> basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow>
     ((\<lambda>x. inverse (f x)) expands_to inverse F) basis"
  by (auto simp: expands_to.simps is_expansion_inverse)

lemma expands_to_divide:
  "trimmed G \<Longrightarrow> basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> (g expands_to G) basis \<Longrightarrow>
     ((\<lambda>x. f x / g x) expands_to F / G) basis"
  by (auto simp: expands_to.simps is_expansion_divide elim: eventually_elim2)

lemma expands_to_powr_0:
  "eventually (\<lambda>x. f x = 0) at_top \<Longrightarrow> g \<equiv> g \<Longrightarrow> basis_wf bs \<Longrightarrow>
     length bs = expansion_level TYPE('a) \<Longrightarrow>
     ((\<lambda>x. f x powr g x) expands_to (zero_expansion :: 'a :: multiseries)) bs"
  by (erule (1) expands_to_cong[OF expands_to_zero]) simp_all

lemma expands_to_powr_const:
  "trimmed_pos F \<Longrightarrow> basis_wf basis \<Longrightarrow> (f expands_to F) basis \<Longrightarrow> p \<equiv> p \<Longrightarrow>
     ((\<lambda>x. f x powr p) expands_to powr_expansion abort F p) basis"
  by (auto simp: expands_to.simps is_expansion_powr trimmed_pos_def elim: eventually_mono)

lemma expands_to_powr_const_0:
  "eventually (\<lambda>x. f x = 0) at_top \<Longrightarrow> basis_wf bs \<Longrightarrow> 
     length bs = expansion_level TYPE('a :: multiseries) \<Longrightarrow>
     p \<equiv> p \<Longrightarrow> ((\<lambda>x. f x powr p) expands_to (zero_expansion :: 'a)) bs"
  by (rule expands_to_cong[OF expands_to_zero]) auto
  

lemma expands_to_powr:
  assumes "trimmed_pos F" "basis_wf basis'" "(f expands_to F) basis'"
  assumes "((\<lambda>x. exp (ln (f x) * g x)) expands_to E) basis"
  shows   "((\<lambda>x. f x powr g x) expands_to E) basis"
using assms(4)
proof (rule expands_to_cong)
  from eval_pos_if_dominant_term_pos[of basis' F] assms(1-4)
    show "eventually (\<lambda>x. exp (ln (f x) * g x) = f x powr g x) at_top"
    by (auto simp: expands_to.simps trimmed_pos_def powr_def elim: eventually_elim2)
qed

lemma expands_to_ln_powr:
  assumes "trimmed_pos F" "basis_wf basis'" "(f expands_to F) basis'"
  assumes "((\<lambda>x. ln (f x) * g x) expands_to E) basis"
  shows   "((\<lambda>x. ln (f x powr g x)) expands_to E) basis"
using assms(4)
proof (rule expands_to_cong)
  from eval_pos_if_dominant_term_pos[of basis' F] assms(1-4)
    show "eventually (\<lambda>x. ln (f x) * g x = ln (f x powr g x)) at_top"
    by (auto simp: expands_to.simps trimmed_pos_def powr_def elim: eventually_elim2)
qed
  
lemma expands_to_exp_ln:
  assumes "trimmed_pos F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. exp (ln (f x))) expands_to F) basis"
using assms(3)
proof (rule expands_to_cong)
  from eval_pos_if_dominant_term_pos[of basis F] assms
    show "eventually (\<lambda>x. f x = exp (ln (f x))) at_top"
    by (auto simp: expands_to.simps trimmed_pos_def powr_def elim: eventually_elim2)
qed

lemma expands_to_power:
  assumes "trimmed F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. f x ^ n) expands_to power_expansion abort F n) basis"
  using assms by (auto simp: expands_to.simps is_expansion_power elim: eventually_mono)

lemma expands_to_power_0:
  assumes "eventually (\<lambda>x. f x = 0) at_top" "basis_wf basis"
          "length basis = expansion_level TYPE('a :: multiseries)" "n \<equiv> n"
  shows   "((\<lambda>x. f x ^ n) expands_to (const_expansion (0 ^ n) :: 'a)) basis"
  by (rule expands_to_cong[OF expands_to_const]) (insert assms, auto elim: eventually_mono)

lemma expands_to_0th_root:
  assumes  "n = 0" "basis_wf basis" "length basis = expansion_level TYPE('a :: multiseries)" "f \<equiv> f"
  shows   "((\<lambda>x. root n (f x)) expands_to (zero_expansion :: 'a)) basis"
  by (rule expands_to_cong[OF expands_to_zero]) (insert assms, auto)

lemma expands_to_root_0:
  assumes  "n > 0" "eventually (\<lambda>x. f x = 0) at_top"
           "basis_wf basis" "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. root n (f x)) expands_to (zero_expansion :: 'a)) basis"
  by (rule expands_to_cong[OF expands_to_zero]) (insert assms, auto elim: eventually_mono)

lemma expands_to_root:
  assumes  "n > 0" "trimmed_pos F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. root n (f x)) expands_to powr_expansion False F (inverse (real n))) basis"
proof -
  have "((\<lambda>x. f x powr (inverse (real n))) expands_to 
          powr_expansion False F (inverse (real n))) basis"
    using assms(2-) by (rule expands_to_powr_const)
  moreover have "eventually (\<lambda>x. f x powr (inverse (real n)) = root n (f x)) at_top"
    using eval_pos_if_dominant_term_pos[of basis F] assms
    by (auto simp: trimmed_pos_def expands_to.simps root_powr_inverse field_simps
             elim: eventually_elim2)
  ultimately show ?thesis by (rule expands_to_cong)
qed

lemma expands_to_root_neg:
  assumes  "n > 0" "trimmed_neg F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. root n (f x)) expands_to
             -powr_expansion False (-F) (inverse (real n))) basis"
proof (rule expands_to_cong)
  show "((\<lambda>x. -root n (-f x)) expands_to
          -powr_expansion False (-F) (inverse (real n))) basis"
    using assms by (intro expands_to_uminus expands_to_root trimmed_pos_uminus) auto
qed (simp_all add: real_root_minus)

lemma expands_to_sqrt:
  assumes "trimmed_pos F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. sqrt (f x)) expands_to powr_expansion False F (1/2)) basis"
  using expands_to_root[of 2 F basis f] assms by (simp add: sqrt_def)

lemma expands_to_exp_real:
  "(f expands_to (F :: real)) basis \<Longrightarrow> ((\<lambda>x. exp (f x)) expands_to exp F) basis"
  by (auto simp: expands_to.simps is_expansion_real.simps elim: eventually_mono)

lemma expands_to_exp_MSLNil:
  assumes "(f expands_to (MS MSLNil f' :: 'a :: multiseries ms)) bs" "basis_wf bs"
  shows   "((\<lambda>x. exp (f x)) expands_to (const_expansion 1 :: 'a ms)) bs"
proof -
  from assms have
     "eventually (\<lambda>x. f' x = 0) at_top" "eventually (\<lambda>x. f' x = f x) at_top"
     and [simp]: "length bs = Suc (expansion_level(TYPE('a)))"
    by (auto simp: expands_to.simps elim: is_expansion_aux.cases)
  from this(1,2) have "eventually (\<lambda>x. 1 = exp (f x)) at_top"
    by eventually_elim simp
  thus ?thesis by (auto simp: expands_to.simps intro!: is_expansion_const assms)
qed

lemma expands_to_exp_zero:
  "(g expands_to MS xs f) basis \<Longrightarrow> eventually (\<lambda>x. f x = 0) at_top \<Longrightarrow> basis_wf basis \<Longrightarrow>
     length basis = expansion_level TYPE('a :: multiseries) \<Longrightarrow>
     ((\<lambda>x. exp (g x)) expands_to (const_expansion 1 :: 'a)) basis"
  by (auto simp: expands_to.simps intro!: is_expansion_const elim: eventually_elim2)

lemma expands_to_sin_real: 
  "(f expands_to (F :: real)) basis \<Longrightarrow> ((\<lambda>x. sin (f x)) expands_to sin F) basis"
  by (auto simp: expands_to.simps is_expansion_real.simps elim: eventually_mono)

lemma expands_to_cos_real: 
  "(f expands_to (F :: real)) basis \<Longrightarrow> ((\<lambda>x. cos (f x)) expands_to cos F) basis"
  by (auto simp: expands_to.simps is_expansion_real.simps elim: eventually_mono)
   
lemma expands_to_sin_MSLNil:
  "(f expands_to MS (MSLNil:: ('a \<times> real) msllist) g) basis \<Longrightarrow> basis_wf basis \<Longrightarrow> 
     ((\<lambda>x. sin (f x)) expands_to MS (MSLNil :: ('a :: multiseries \<times> real) msllist) (\<lambda>x. 0)) basis"
  by (auto simp: expands_to.simps dominant_term_ms_aux_def intro!: is_expansion_aux.intros
           elim: eventually_elim2 is_expansion_aux.cases)

lemma expands_to_cos_MSLNil:
  "(f expands_to MS (MSLNil:: ('a :: multiseries \<times> real) msllist) g) basis \<Longrightarrow> basis_wf basis \<Longrightarrow> 
     ((\<lambda>x. cos (f x)) expands_to (const_expansion 1 :: 'a ms)) basis"
  by (auto simp: expands_to.simps dominant_term_ms_aux_def const_expansion_ms_def 
           intro!: const_ms_aux elim: is_expansion_aux.cases eventually_elim2)

lemma sin_ms_aux':
  assumes "ms_exp_gt 0 (ms_aux_hd_exp xs)" "basis_wf basis" "is_expansion_aux xs f basis"
  shows   "is_expansion_aux (sin_ms_aux' xs) (\<lambda>x. sin (f x)) basis"
  unfolding sin_ms_aux'_def sin_conv_pre_sin power2_eq_square using assms
  by (intro times_ms_aux powser_ms_aux[unfolded o_def] convergent_powser_sin_series_stream)
     (auto simp: hd_exp_times add_neg_neg split: option.splits)

lemma cos_ms_aux':
  assumes "ms_exp_gt 0 (ms_aux_hd_exp xs)" "basis_wf basis" "is_expansion_aux xs f basis"
  shows   "is_expansion_aux (cos_ms_aux' xs) (\<lambda>x. cos (f x)) basis"
  unfolding cos_ms_aux'_def cos_conv_pre_cos power2_eq_square using assms
  by (intro times_ms_aux powser_ms_aux[unfolded o_def] convergent_powser_cos_series_stream)
     (auto simp: hd_exp_times add_neg_neg split: option.splits)

lemma expands_to_sin_ms_neg_exp: 
  assumes "e < 0" "basis_wf basis" "(f expands_to MS (MSLCons (C, e) xs) g) basis"
  shows   "((\<lambda>x. sin (f x)) expands_to MS (sin_ms_aux' (MSLCons (C, e) xs)) (\<lambda>x. sin (g x))) basis"
  using assms by (auto simp: expands_to.simps snd_dominant_term_ms_aux_MSLCons o_def
                       intro!: sin_ms_aux' elim: eventually_mono)

lemma expands_to_cos_ms_neg_exp: 
  assumes "e < 0" "basis_wf basis" "(f expands_to MS (MSLCons (C, e) xs) g) basis"
  shows   "((\<lambda>x. cos (f x)) expands_to MS (cos_ms_aux' (MSLCons (C, e) xs)) (\<lambda>x. cos (g x))) basis"
  using assms by (auto simp: expands_to.simps snd_dominant_term_ms_aux_MSLCons o_def
                       intro!: cos_ms_aux' elim: eventually_mono)

lemma is_expansion_sin_ms_zero_exp: 
  fixes F :: "('a :: multiseries \<times> real) msllist"
  assumes basis: "basis_wf (b # basis)" 
  assumes F: "is_expansion (MS (MSLCons (C, 0) xs) f) (b # basis)"
  assumes Sin: "((\<lambda>x. sin (eval C x)) expands_to (Sin :: 'a)) basis"
  assumes Cos: "((\<lambda>x. cos (eval C x)) expands_to (Cos :: 'a)) basis"
  shows   "is_expansion 
             (MS (plus_ms_aux (scale_shift_ms_aux (Sin, 0) (cos_ms_aux' xs))
                              (scale_shift_ms_aux (Cos, 0) (sin_ms_aux' xs))) 
             (\<lambda>x. sin (f x))) (b # basis)" (is "is_expansion (MS ?A _) _")
proof -
  let ?g = "\<lambda>x. f x - eval C x * b x powr 0"
  let ?h = "\<lambda>x. eval Sin x * b x powr 0 * cos (?g x) + eval Cos x * b x powr 0 * sin (?g x)"
  from basis have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  from F have F': "is_expansion_aux xs ?g (b # basis)" 
                  "ms_exp_gt 0 (ms_aux_hd_exp xs)" "is_expansion C basis"
    by (auto elim!: is_expansion_aux_MSLCons) 
  have "is_expansion_aux ?A ?h (b # basis)"
    using basis Sin Cos unfolding F'(1)
    by (intro plus_ms_aux scale_shift_ms_aux cos_ms_aux' sin_ms_aux' F')
       (simp_all add: expands_to.simps)
  moreover from b_pos eval_expands_to[OF Sin] eval_expands_to[OF Cos] 
    have "eventually (\<lambda>x. ?h x = sin (f x)) at_top"
    by eventually_elim (simp add: sin_add [symmetric])
  ultimately have "is_expansion_aux ?A (\<lambda>x. sin (f x)) (b # basis)"
    by (rule is_expansion_aux_cong)
  thus ?thesis by simp
qed

lemma is_expansion_cos_ms_zero_exp: 
  fixes F :: "('a :: multiseries \<times> real) msllist"
  assumes basis: "basis_wf (b # basis)" 
  assumes F: "is_expansion (MS (MSLCons (C, 0) xs) f) (b # basis)"
  assumes Sin: "((\<lambda>x. sin (eval C x)) expands_to (Sin :: 'a)) basis"
  assumes Cos: "((\<lambda>x. cos (eval C x)) expands_to (Cos :: 'a)) basis"
  shows   "is_expansion 
             (MS (minus_ms_aux (scale_shift_ms_aux (Cos, 0) (cos_ms_aux' xs))
                              (scale_shift_ms_aux (Sin, 0) (sin_ms_aux' xs))) 
             (\<lambda>x. cos (f x))) (b # basis)" (is "is_expansion (MS ?A _) _")
proof -
  let ?g = "\<lambda>x. f x - eval C x * b x powr 0"
  let ?h = "\<lambda>x. eval Cos x * b x powr 0 * cos (?g x) - eval Sin x * b x powr 0 * sin (?g x)"
  from basis have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)
  from F have F': "is_expansion_aux xs ?g (b # basis)" 
                  "ms_exp_gt 0 (ms_aux_hd_exp xs)" "is_expansion C basis"
    by (auto elim!: is_expansion_aux_MSLCons) 
  have "is_expansion_aux ?A ?h (b # basis)"
    using basis Sin Cos unfolding F'(1)
    by (intro minus_ms_aux scale_shift_ms_aux cos_ms_aux' sin_ms_aux' F')
       (simp_all add: expands_to.simps)
  moreover from b_pos eval_expands_to[OF Sin] eval_expands_to[OF Cos] 
    have "eventually (\<lambda>x. ?h x = cos (f x)) at_top"
    by eventually_elim (simp add: cos_add [symmetric])
  ultimately have "is_expansion_aux ?A (\<lambda>x. cos (f x)) (b # basis)"
    by (rule is_expansion_aux_cong)
  thus ?thesis by simp
qed

lemma expands_to_sin_ms_zero_exp: 
  assumes e: "e = 0" and basis: "basis_wf (b # basis)" 
  assumes F: "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)"
  assumes Sin: "((\<lambda>x. sin (c x)) expands_to Sin) basis"
  assumes Cos: "((\<lambda>x. cos (c x)) expands_to Cos) basis"
  assumes C: "eval C = c"
  shows   "((\<lambda>x. sin (f x)) expands_to 
             MS (plus_ms_aux (scale_shift_ms_aux (Sin, 0) (cos_ms_aux' xs))
                              (scale_shift_ms_aux (Cos, 0) (sin_ms_aux' xs)))
                (\<lambda>x. sin (g x))) (b # basis)"
  using is_expansion_sin_ms_zero_exp[of b basis C xs g Sin Cos] assms
  by (auto simp: expands_to.simps elim: eventually_mono)
    
lemma expands_to_cos_ms_zero_exp: 
  assumes e: "e = 0" and basis: "basis_wf (b # basis)" 
  assumes F: "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)"
  assumes Sin: "((\<lambda>x. sin (c x)) expands_to Sin) basis"
  assumes Cos: "((\<lambda>x. cos (c x)) expands_to Cos) basis"
  assumes C: "eval C = c"
  shows   "((\<lambda>x. cos (f x)) expands_to 
             MS (minus_ms_aux (scale_shift_ms_aux (Cos, 0) (cos_ms_aux' xs))
                              (scale_shift_ms_aux (Sin, 0) (sin_ms_aux' xs)))
                (\<lambda>x. cos (g x))) (b # basis)"
  using is_expansion_cos_ms_zero_exp[of b basis C xs g Sin Cos] assms
  by (auto simp: expands_to.simps elim: eventually_mono)
  


lemma expands_to_sgn_zero:
  assumes "eventually (\<lambda>x. f x = 0) at_top" "basis_wf basis"
          "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. sgn (f x)) expands_to (zero_expansion :: 'a)) basis"
  by (rule expands_to_cong[OF expands_to_zero]) (insert assms, auto simp: sgn_eq_0_iff)

lemma expands_to_sgn_pos:
  assumes "trimmed_pos F" "(f expands_to F) basis" "basis_wf basis"
          "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. sgn (f x)) expands_to (const_expansion 1 :: 'a)) basis"
proof (rule expands_to_cong[OF expands_to_const])
  from trimmed_imp_eventually_sgn[of basis F] assms
    have "eventually (\<lambda>x. sgn (eval F x) = 1) at_top" 
      by (simp add: expands_to.simps trimmed_pos_def)
  moreover from assms have "eventually (\<lambda>x. eval F x = f x) at_top"
    by (simp add: expands_to.simps)
  ultimately show "eventually (\<lambda>x. 1 = sgn (f x)) at_top" by eventually_elim simp
qed (insert assms, auto)

lemma expands_to_sgn_neg:
  assumes "trimmed_neg F" "(f expands_to F) basis" "basis_wf basis"
          "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. sgn (f x)) expands_to (const_expansion (-1) :: 'a)) basis"
proof (rule expands_to_cong[OF expands_to_const])
  from trimmed_imp_eventually_sgn[of basis F] assms
    have "eventually (\<lambda>x. sgn (eval F x) = -1) at_top" 
      by (simp add: expands_to.simps trimmed_neg_def)
  moreover from assms have "eventually (\<lambda>x. eval F x = f x) at_top"
    by (simp add: expands_to.simps)
  ultimately show "eventually (\<lambda>x. -1 = sgn (f x)) at_top" by eventually_elim simp
qed (insert assms, auto)



lemma expands_to_abs_pos:
  assumes "trimmed_pos F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. abs (f x)) expands_to F) basis"
using assms(3)
proof (rule expands_to_cong)
  from trimmed_imp_eventually_sgn[of basis F] assms
    have "eventually (\<lambda>x. sgn (eval F x) = 1) at_top" 
    by (simp add: expands_to.simps trimmed_pos_def)
  with assms(3) show "eventually (\<lambda>x. f x = abs (f x)) at_top" 
    by (auto simp: expands_to.simps sgn_if split: if_splits elim: eventually_elim2)
qed

lemma expands_to_abs_neg:
  assumes "trimmed_neg F" "basis_wf basis" "(f expands_to F) basis"
  shows   "((\<lambda>x. abs (f x)) expands_to -F) basis"
using expands_to_uminus[OF assms(2,3)]
proof (rule expands_to_cong)
  from trimmed_imp_eventually_sgn[of basis F] assms
    have "eventually (\<lambda>x. sgn (eval F x) = -1) at_top" 
    by (simp add: expands_to.simps trimmed_neg_def)
  with assms(3) show "eventually (\<lambda>x. -f x = abs (f x)) at_top" 
    by (auto simp: expands_to.simps sgn_if split: if_splits elim: eventually_elim2)
qed

lemma expands_to_imp_eventually_nz:
  assumes "basis_wf basis" "(f expands_to F) basis" "trimmed F"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) at_top"
  using trimmed_imp_eventually_nz[OF assms(1), of F] assms(2,3)
  by (auto simp: expands_to.simps elim: eventually_elim2)

lemma expands_to_imp_eventually_pos:
  assumes "basis_wf basis" "(f expands_to F) basis" "trimmed_pos F"
  shows   "eventually (\<lambda>x. f x > 0) at_top"
  using eval_pos_if_dominant_term_pos[of basis F] assms 
  by (auto simp: expands_to.simps trimmed_pos_def elim: eventually_elim2)

lemma expands_to_imp_eventually_neg:
  assumes "basis_wf basis" "(f expands_to F) basis" "trimmed_neg F"
  shows   "eventually (\<lambda>x. f x < 0) at_top"
  using eval_pos_if_dominant_term_pos[of basis "-F"] assms
  by (auto simp: expands_to.simps trimmed_neg_def is_expansion_uminus elim: eventually_elim2)

lemma expands_to_imp_eventually_gt:
  assumes "basis_wf basis" "((\<lambda>x. f x - g x) expands_to F) basis" "trimmed_pos F"
  shows   "eventually (\<lambda>x. f x > g x) at_top"
  using expands_to_imp_eventually_pos[OF assms] by simp

lemma expands_to_imp_eventually_lt:
  assumes "basis_wf basis" "((\<lambda>x. f x - g x) expands_to F) basis" "trimmed_neg F"
  shows   "eventually (\<lambda>x. f x < g x) at_top"
  using expands_to_imp_eventually_neg[OF assms] by simp

lemma eventually_diff_zero_imp_eq:
  fixes f g :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. f x - g x = 0) at_top"
  shows   "eventually (\<lambda>x. f x = g x) at_top"
  using assms by eventually_elim simp

lemma smallo_trimmed_imp_eventually_less:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<in> o(g)" "(g expands_to G) bs" "basis_wf bs" "trimmed_pos G"
  shows   "eventually (\<lambda>x. f x < g x) at_top"
proof -
  from assms(2-4) have pos: "eventually (\<lambda>x. g x > 0) at_top"
    using expands_to_imp_eventually_pos by blast
  have "(1 / 2 :: real) > 0" by simp
  from landau_o.smallD[OF assms(1) this] and pos
    show ?thesis by eventually_elim (simp add: abs_if split: if_splits)
qed

lemma smallo_trimmed_imp_eventually_greater:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<in> o(g)" "(g expands_to G) bs" "basis_wf bs" "trimmed_neg G"
  shows   "eventually (\<lambda>x. f x > g x) at_top"
proof -
  from assms(2-4) have pos: "eventually (\<lambda>x. g x < 0) at_top"
    using expands_to_imp_eventually_neg by blast
  have "(1 / 2 :: real) > 0" by simp
  from landau_o.smallD[OF assms(1) this] and pos
    show ?thesis by eventually_elim (simp add: abs_if split: if_splits)
qed

lemma expands_to_min_lt:
  assumes "(f expands_to F) basis" "eventually (\<lambda>x. f x < g x) at_top"
  shows   "((\<lambda>x. min (f x) (g x)) expands_to F) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: min_def elim: eventually_mono)

lemma expands_to_min_eq:
  assumes "(f expands_to F) basis" "eventually (\<lambda>x. f x = g x) at_top"
  shows   "((\<lambda>x. min (f x) (g x)) expands_to F) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: min_def elim: eventually_mono)

lemma expands_to_min_gt:
  assumes "(g expands_to G) basis" "eventually (\<lambda>x. f x > g x) at_top"
  shows   "((\<lambda>x. min (f x) (g x)) expands_to G) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: min_def elim: eventually_mono)
    
lemma expands_to_max_gt:
  assumes "(f expands_to F) basis" "eventually (\<lambda>x. f x > g x) at_top"
  shows   "((\<lambda>x. max (f x) (g x)) expands_to F) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: max_def elim: eventually_mono)
    
lemma expands_to_max_eq:
  assumes "(f expands_to F) basis" "eventually (\<lambda>x. f x = g x) at_top"
  shows   "((\<lambda>x. max (f x) (g x)) expands_to F) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: max_def elim: eventually_mono)

lemma expands_to_max_lt:
  assumes "(g expands_to G) basis" "eventually (\<lambda>x. f x < g x) at_top"
  shows   "((\<lambda>x. max (f x) (g x)) expands_to G) basis"
  using assms(1)
  by (rule expands_to_cong) (insert assms(2), auto simp: max_def elim: eventually_mono)


lemma expands_to_lift:
  "is_lifting f basis basis' \<Longrightarrow> (c expands_to C) basis \<Longrightarrow> (c expands_to (f C)) basis'"
  by (simp add: is_lifting_def expands_to.simps)
    
lemma expands_to_basic_powr: 
  assumes "basis_wf (b # basis)" "length basis = expansion_level TYPE('a::multiseries)"
  shows   "((\<lambda>x. b x powr e) expands_to 
             MS (MSLCons (const_expansion 1 :: 'a, e) MSLNil) (\<lambda>x. b x powr e)) (b # basis)"
  using assms by (auto simp: expands_to.simps basis_wf_Cons powr_smallo_iff
                       intro!: is_expansion_aux.intros is_expansion_const powr_smallo_iff)

lemma expands_to_basic_inverse: 
  assumes "basis_wf (b # basis)" "length basis = expansion_level TYPE('a::multiseries)"
  shows   "((\<lambda>x. inverse (b x)) expands_to 
             MS (MSLCons (const_expansion 1 :: 'a, -1) MSLNil) (\<lambda>x. b x powr -1)) (b # basis)"
proof -
  from assms have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: basis_wf_Cons filterlim_at_top_dense)
  moreover have "(\<lambda>a. inverse (a powr 1)) \<in> o(\<lambda>a. a powr e')" if "e' > -1" for e' :: real
    using that by (simp add: landau_o.small.inverse_eq2 one_smallo_powr flip: powr_one' powr_add)
  ultimately show ?thesis using assms
    by (auto simp: expands_to.simps basis_wf_Cons powr_minus
             elim: eventually_mono
             intro!: is_expansion_aux.intros is_expansion_const
                     landau_o.small.compose[of _ at_top _ b])
qed

lemma expands_to_div':
  assumes "basis_wf basis" "(f expands_to F) basis" "((\<lambda>x. inverse (g x)) expands_to G) basis"
  shows   "((\<lambda>x. f x / g x) expands_to F * G) basis"
  using expands_to_mult[OF assms] by (simp add: field_split_simps)

lemma expands_to_basic: 
  assumes "basis_wf (b # basis)" "length basis = expansion_level TYPE('a::multiseries)"
  shows   "(b expands_to MS (MSLCons (const_expansion 1 :: 'a, 1) MSLNil) b) (b # basis)"
proof -
  from assms have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: basis_wf_Cons filterlim_at_top_dense)
  moreover {
    fix e' :: real assume e': "e' > 1"
    have "(\<lambda>x::real. x) \<in> \<Theta>(\<lambda>x. x powr 1)"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]]) auto
    also have "(\<lambda>x. x powr 1) \<in> o(\<lambda>x. x powr e')"
      using e' by (subst powr_smallo_iff) (auto simp: filterlim_ident)
    finally have "(\<lambda>x. x) \<in> o(\<lambda>x. x powr e')" .
  }
  ultimately show ?thesis using assms
    by (auto simp: expands_to.simps basis_wf_Cons elim: eventually_mono
             intro!: is_expansion_aux.intros is_expansion_const
                     landau_o.small.compose[of _ at_top _ b])
qed

lemma expands_to_lift':
  assumes "basis_wf (b # basis)" "(f expands_to MS xs g) basis"
  shows   "(f expands_to (MS (MSLCons (MS xs g, 0) MSLNil) g)) (b # basis)"
proof -
  have "is_lifting lift_ms basis (b # basis)" by (rule is_lifting_lift) fact+
  from expands_to_lift[OF this assms(2)] show ?thesis by (simp add: lift_ms_def)
qed

lemma expands_to_lift'':
  assumes "basis_wf (b # basis)" "(f expands_to F) basis"
  shows   "(f expands_to (MS (MSLCons (F, 0) MSLNil) (eval F))) (b # basis)"
proof -
  have "is_lifting lift_ms basis (b # basis)" by (rule is_lifting_lift) fact+
  from expands_to_lift[OF this assms(2)] show ?thesis by (simp add: lift_ms_def)
qed

lemma expands_to_drop_zero:
  assumes "eventually (\<lambda>x. eval C x = 0) at_top"
  assumes "(f expands_to (MS (MSLCons (C, e) xs) g)) basis"
  shows   "(f expands_to (MS xs g)) basis"
  using assms drop_zero_ms[of C e xs g basis] by (simp add: expands_to.simps)

lemma expands_to_hd'':
  assumes "(f expands_to (MS (MSLCons (C, e) xs) g)) (b # basis)"
  shows   "(eval C expands_to C) basis"
  using assms by (auto simp: expands_to.simps elim: is_expansion_aux_MSLCons)

lemma expands_to_hd:
  assumes "(f expands_to (MS (MSLCons (MS ys h, e) xs) g)) (b # basis)"
  shows   "(h expands_to MS ys h) basis"
  using assms by (auto simp: expands_to.simps elim: is_expansion_aux_MSLCons)

lemma expands_to_hd':
  assumes "(f expands_to (MS (MSLCons (c :: real, e) xs) g)) (b # basis)"
  shows   "((\<lambda>_. c) expands_to c) basis"
  using assms by (auto simp: expands_to.simps elim: is_expansion_aux_MSLCons)

lemma expands_to_trim_cong:
  assumes "(f expands_to (MS (MSLCons (C, e) xs) g)) (b # basis)"
  assumes "(eval C expands_to C') basis"
  shows   "(f expands_to (MS (MSLCons (C', e) xs) g)) (b # basis)"
proof -
  from assms(1) have "is_expansion_aux xs (\<lambda>x. g x - eval C x * b x powr e) (b # basis)"
    by (auto simp: expands_to.simps elim!: is_expansion_aux_MSLCons)
  hence "is_expansion_aux xs (\<lambda>x. g x - eval C' x * b x powr e) (b # basis)"
    by (rule is_expansion_aux_cong)
       (insert assms(2), auto simp: expands_to.simps elim: eventually_mono)
  with assms show ?thesis
    by (auto simp: expands_to.simps elim!: is_expansion_aux_MSLCons intro!: is_expansion_aux.intros)
qed

lemma is_expansion_aux_expands_to:
  assumes "(f expands_to MS xs g) basis"
  shows   "is_expansion_aux xs f basis"
proof -
  from assms have "is_expansion_aux xs g basis" "eventually (\<lambda>x. g x = f x) at_top" 
    by (simp_all add: expands_to.simps)
  thus ?thesis by (rule is_expansion_aux_cong)
qed

lemma ln_series_stream_aux_code:
  "ln_series_stream_aux True c = MSSCons (- inverse c) (ln_series_stream_aux False (c + 1))"
  "ln_series_stream_aux False c = MSSCons (inverse c) (ln_series_stream_aux True (c + 1))"
  by (subst ln_series_stream_aux.code, simp)+

definition powser_ms_aux' where
  "powser_ms_aux' cs xs = powser_ms_aux (msllist_of_msstream cs) xs"

lemma ln_ms_aux:
  fixes C L :: "'a :: multiseries"
  assumes trimmed: "trimmed_pos C" and basis: "basis_wf (b # basis)"
  assumes F: "is_expansion_aux (MSLCons (C, e) xs) f (b # basis)"
  assumes L: "((\<lambda>x. ln (eval C x) + e * ln (b x)) expands_to L) basis"
  shows   "is_expansion_aux 
             (MSLCons (L, 0) (times_ms_aux (scale_shift_ms_aux (inverse C, - e) xs)
               (powser_ms_aux' (ln_series_stream_aux False 1) 
                 (scale_shift_ms_aux (inverse C, - e) xs))))
             (\<lambda>x. ln (f x)) (b # basis)"
    (is "is_expansion_aux ?G _ _")
proof -
  from F have F': 
    "is_expansion_aux xs (\<lambda>x. f x - eval C x * b x powr e) (b # basis)"
    "is_expansion C basis" "\<forall>e'>e. f \<in> o(\<lambda>x. b x powr e')" "ms_exp_gt e (ms_aux_hd_exp xs)"
    by (auto elim!: is_expansion_aux_MSLCons)
  from basis have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 1) at_top" by (simp add: filterlim_at_top_dense)
  from eval_pos_if_dominant_term_pos[of basis C] trimmed F' basis
    have C_pos: "eventually (\<lambda>x. eval C x > 0) at_top"
      by (auto simp: basis_wf_Cons trimmed_pos_def)
  from eval_pos_if_dominant_term_pos'[OF basis _ F] trimmed
  have f_pos: "eventually (\<lambda>x. f x > 0) at_top"
    by (simp add: trimmed_pos_def trimmed_ms_aux_def dominant_term_ms_aux_def case_prod_unfold)
  
  from F' have "ms_exp_gt 0 (map_option ((+) (-e)) (ms_aux_hd_exp xs))" 
    by (cases "ms_aux_hd_exp xs") simp_all
  hence "is_expansion_aux (powser_ms_aux' ln_series_stream (scale_shift_ms_aux (inverse C, -e) xs))
          ((\<lambda>x. ln (1 + x)) \<circ> (\<lambda>x. eval (inverse C) x * b x powr -e * 
              (f x - eval C x * b x powr e))) (b # basis)" (is "is_expansion_aux _ ?g _")
    unfolding powser_ms_aux'_def using powser_ms_aux' basis F' trimmed
    by (intro powser_ms_aux' convergent_powser'_ln scale_shift_ms_aux is_expansion_inverse F')
       (simp_all add: trimmed_pos_def hd_exp_basis basis_wf_Cons)
  moreover have "eventually (\<lambda>x. ?g x = ln (f x) - eval L x * b x powr 0) at_top"
    using b_pos C_pos f_pos eval_expands_to[OF L]
    by eventually_elim 
       (simp add: powr_minus algebra_simps ln_mult ln_inverse expands_to.simps ln_powr)
  ultimately 
    have "is_expansion_aux (powser_ms_aux' ln_series_stream (scale_shift_ms_aux (inverse C, -e) xs))
            (\<lambda>x. ln (f x) - eval L x * b x powr 0) (b # basis)" 
      by (rule is_expansion_aux_cong)
  hence *: "is_expansion_aux (times_ms_aux (scale_shift_ms_aux (inverse C, - e) xs)
              (powser_ms_aux' (ln_series_stream_aux False 1) (scale_shift_ms_aux (inverse C, - e) xs)))
              (\<lambda>x. ln (f x) - eval L x * b x powr 0) (b # basis)"
    unfolding ln_series_stream_def powser_ms_aux'_def powser_ms_aux_MSLCons msllist_of_msstream_MSSCons
    by (rule drop_zero_ms_aux [rotated]) simp_all
  moreover from F' have exp: "ms_exp_gt 0 (map_option ((+) (-e)) (ms_aux_hd_exp xs))"
    by (cases "ms_aux_hd_exp xs") simp_all
  moreover have "(\<lambda>x. ln (f x)) \<in> o(\<lambda>x. b x powr e')" if "e' > 0" for e'
  proof -
    from is_expansion_aux_imp_smallo[OF *, of e'] that exp
    have "(\<lambda>x. ln (f x) - eval L x * b x powr 0) \<in> o(\<lambda>x. b x powr e')" 
      by (cases "ms_aux_hd_exp xs") 
         (simp_all add: hd_exp_times hd_exp_powser hd_exp_basis powser_ms_aux'_def)
    moreover {
      from L F' basis that have "eval L \<in> o(\<lambda>x. b x powr e')"
        by (intro is_expansion_imp_smallo[of basis]) (simp_all add: basis_wf_Cons expands_to.simps)
      also have "eval L \<in> o(\<lambda>x. b x powr e') \<longleftrightarrow> (\<lambda>x. eval L x * b x powr 0) \<in> o(\<lambda>x. b x powr e')"
        using b_pos by (intro landau_o.small.in_cong) (auto elim: eventually_mono)
      finally have \<dots> .
    } ultimately have "(\<lambda>x. ln (f x) - eval L x * b x powr 0 + eval L x * b x powr 0) \<in> 
                          o(\<lambda>x. b x powr e')" by (rule sum_in_smallo)
    thus ?thesis by simp
  qed
  ultimately show "is_expansion_aux ?G (\<lambda>x. ln (f x)) (b # basis)" using L
    by (intro is_expansion_aux.intros)
       (auto simp: expands_to.simps hd_exp_times hd_exp_powser hd_exp_basis
                   powser_ms_aux'_def split: option.splits)
qed

lemma expands_to_ln:
  fixes C L :: "'a :: multiseries"
  assumes trimmed: "trimmed_pos (MS (MSLCons (C, e) xs) g)" and basis: "basis_wf (b # basis)"
  assumes F: "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)"
  assumes L: "((\<lambda>x. ln (h x) + e * ln (b x)) expands_to L) basis"
  and h: "eval C = h"
  shows   "((\<lambda>x. ln (f x)) expands_to MS
             (MSLCons (L, 0) (times_ms_aux (scale_shift_ms_aux (inverse C, - e) xs)
               (powser_ms_aux' (ln_series_stream_aux False 1) 
                 (scale_shift_ms_aux (inverse C, - e) xs)))) (\<lambda>x. ln (f x))) (b # basis)"
  using is_expansion_aux_expands_to[OF F] assms by (auto simp: expands_to.simps intro!: ln_ms_aux)

lemma trimmed_lifting:
  assumes "is_lifting f basis basis'"
  assumes "trimmed F"
  shows   "trimmed (f F)"
  using assms by (simp add: is_lifting_def)

lemma trimmed_pos_lifting:
  assumes "is_lifting f basis basis'"
  assumes "trimmed_pos F"
  shows   "trimmed_pos (f F)"
  using assms by (simp add: is_lifting_def trimmed_pos_def)

lemma expands_to_ln_aux_0:
  assumes e: "e = 0"
  assumes L1: "((\<lambda>x. ln (g x)) expands_to L) basis"
  shows "((\<lambda>x. ln (g x) + e * ln (b x)) expands_to L) basis"
  using assms by simp

lemma expands_to_ln_aux_1:
  assumes e: "e = 1"
  assumes basis: "basis_wf (b # basis)"
  assumes L1: "((\<lambda>x. ln (g x)) expands_to L1) basis"
  assumes L2: "((\<lambda>x. ln (b x)) expands_to L2) basis"
  shows "((\<lambda>x. ln (g x) + e * ln (b x)) expands_to L1 + L2) basis"
  using assms by (intro expands_to_add) (simp_all add: basis_wf_Cons)

lemma expands_to_ln_eventually_1:
  assumes "basis_wf basis" "length basis = expansion_level TYPE('a)"
  assumes "eventually (\<lambda>x. f x - 1 = 0) at_top"
  shows   "((\<lambda>x. ln (f x)) expands_to (zero_expansion :: 'a :: multiseries)) basis"
  by (rule expands_to_cong [OF expands_to_zero]) (insert assms, auto elim: eventually_mono)  

lemma expands_to_ln_aux:
  assumes basis: "basis_wf (b # basis)"
  assumes L1: "((\<lambda>x. ln (g x)) expands_to L1) basis"
  assumes L2: "((\<lambda>x. ln (b x)) expands_to L2) basis"
  shows "((\<lambda>x. ln (g x) + e * ln (b x)) expands_to L1 + scale_ms e L2) basis"
proof -
  from L1 have "length basis = expansion_level TYPE('a)"
    by (auto simp: expands_to.simps is_expansion_length)
  with assms show ?thesis unfolding scale_ms_def
    by (intro expands_to_add assms expands_to_mult expands_to_const) 
       (simp_all add: basis_wf_Cons)
qed

lemma expands_to_ln_to_expands_to_ln_eval:
  assumes "((\<lambda>x. ln (f x) + F x) expands_to L) basis"
  shows   "((\<lambda>x. ln (eval (MS xs f) x) + F x) expands_to L) basis"
  using assms by simp

lemma expands_to_ln_const:
  "((\<lambda>x. ln (eval (C :: real) x)) expands_to ln C) []"
  by (simp add: expands_to.simps is_expansion_real.intros)

lemma expands_to_meta_eq_cong:
  assumes "(f expands_to F) basis" "F \<equiv> G"
  shows   "(f expands_to G) basis"
  using assms by simp
    
lemma expands_to_meta_eq_cong':
  assumes "(g expands_to F) basis" "f \<equiv> g"
  shows   "(f expands_to F) basis"
  using assms by simp


lemma uminus_ms_aux_MSLCons_eval:
  "uminus_ms_aux (MSLCons (c, e) xs) = MSLCons (-c, e) (uminus_ms_aux xs)"
  by (simp add: uminus_ms_aux_MSLCons)

lemma scale_shift_ms_aux_MSLCons_eval:
  "scale_shift_ms_aux (c, e) (MSLCons (c', e') xs) =
     MSLCons (c * c', e + e') (scale_shift_ms_aux (c, e) xs)"
  by (simp add: scale_shift_ms_aux_MSLCons)

lemma times_ms_aux_MSLCons_eval: "times_ms_aux (MSLCons (c1, e1) xs) (MSLCons (c2, e2) ys) = 
  MSLCons (c1 * c2, e1 + e2) (plus_ms_aux (scale_shift_ms_aux (c1, e1) ys) 
    (times_ms_aux xs (MSLCons (c2, e2) ys)))"
  by (simp add: times_ms_aux_MSLCons)

lemma plus_ms_aux_MSLCons_eval:
  "plus_ms_aux (MSLCons (c1, e1) xs) (MSLCons (c2, e2) ys) =
     CMP_BRANCH (COMPARE e1 e2) 
       (MSLCons (c2, e2) (plus_ms_aux (MSLCons (c1, e1) xs) ys))
       (MSLCons (c1 + c2, e1) (plus_ms_aux xs ys))
       (MSLCons (c1, e1) (plus_ms_aux xs (MSLCons (c2, e2) ys)))"
  by (simp add: CMP_BRANCH_def COMPARE_def plus_ms_aux_MSLCons)

lemma inverse_ms_aux_MSLCons: "inverse_ms_aux (MSLCons (C, e) xs) = 
   scale_shift_ms_aux (inverse C, - e)
     (powser_ms_aux' (mssalternate 1 (- 1))
       (scale_shift_ms_aux (inverse C, - e)
         xs))"
  by (simp add: Let_def inverse_ms_aux.simps powser_ms_aux'_def)

lemma powr_ms_aux_MSLCons: "powr_ms_aux abort (MSLCons (C, e) xs) p = 
  scale_shift_ms_aux (powr_expansion abort C p, e * p)
     (powser_ms_aux (gbinomial_series abort p)
       (scale_shift_ms_aux (inverse C, - e) xs))"
  by simp

lemma power_ms_aux_MSLCons: "power_ms_aux abort (MSLCons (C, e) xs) n = 
  scale_shift_ms_aux (power_expansion abort C n, e * real n)
     (powser_ms_aux (gbinomial_series abort (real n))
       (scale_shift_ms_aux (inverse C, - e) xs))"
  by simp

lemma minus_ms_aux_MSLCons_eval:
  "minus_ms_aux (MSLCons (c1, e1) xs) (MSLCons (c2, e2) ys) = 
     CMP_BRANCH (COMPARE e1 e2) 
       (MSLCons (-c2, e2) (minus_ms_aux (MSLCons (c1, e1) xs) ys))
       (MSLCons (c1 - c2, e1) (minus_ms_aux xs ys))
       (MSLCons (c1, e1) (minus_ms_aux xs (MSLCons (c2, e2) ys)))"
  by (simp add: minus_ms_aux_def plus_ms_aux_MSLCons_eval uminus_ms_aux_MSLCons minus_eq_plus_uminus)
  
lemma minus_ms_altdef: "MS xs f - MS ys g = MS (minus_ms_aux xs ys) (\<lambda>x. f x - g x)"
  by (simp add: minus_ms_def minus_ms_aux_def)

lemma const_expansion_ms_eval: "const_expansion c = MS (MSLCons (const_expansion c, 0) MSLNil) (\<lambda>_. c)"
  by (simp add: const_expansion_ms_def const_ms_aux_def)
 
lemma powser_ms_aux'_MSSCons:
  "powser_ms_aux' (MSSCons c cs) xs = 
     MSLCons (const_expansion c, 0) (times_ms_aux xs (powser_ms_aux' cs xs))"
  by (simp add: powser_ms_aux'_def powser_ms_aux_MSLCons)

lemma sin_ms_aux'_altdef:
  "sin_ms_aux' xs = times_ms_aux xs (powser_ms_aux' sin_series_stream (times_ms_aux xs xs))"
  by (simp add: sin_ms_aux'_def powser_ms_aux'_def)

lemma cos_ms_aux'_altdef:
  "cos_ms_aux' xs = powser_ms_aux' cos_series_stream (times_ms_aux xs xs)"
  by (simp add: cos_ms_aux'_def powser_ms_aux'_def)

lemma sin_series_stream_aux_code:
  "sin_series_stream_aux True acc m = 
     MSSCons (-inverse acc) (sin_series_stream_aux False (acc * (m + 1) * (m + 2)) (m + 2))"
  "sin_series_stream_aux False acc m = 
     MSSCons (inverse acc) (sin_series_stream_aux True (acc * (m + 1) * (m + 2)) (m + 2))"
  by (subst sin_series_stream_aux.code; simp)+
    
lemma arctan_series_stream_aux_code:
  "arctan_series_stream_aux True n = MSSCons (-inverse n) (arctan_series_stream_aux False (n + 2))"
  "arctan_series_stream_aux False n = MSSCons (inverse n) (arctan_series_stream_aux True (n + 2))"
  by (subst arctan_series_stream_aux.code; simp)+


subsubsection \<open>Composition with an asymptotic power series\<close>

context
  fixes h :: "real \<Rightarrow> real" and F :: "real filter"
begin
  
coinductive asymp_powser :: 
    "(real \<Rightarrow> real) \<Rightarrow> real msstream \<Rightarrow> bool" where
  "asymp_powser f cs \<Longrightarrow> f' \<in> O[F](\<lambda>_. 1) \<Longrightarrow>
     eventually (\<lambda>x. f' x = c + f x * h x) F \<Longrightarrow> asymp_powser f' (MSSCons c cs)"

lemma asymp_powser_coinduct [case_names asymp_powser]:
  "P x1 x2 \<Longrightarrow> (\<And>x1 x2.  P x1 x2 \<Longrightarrow> \<exists>f cs c.
       x2 = MSSCons c cs \<and> asymp_powser f cs \<and>
       x1 \<in> O[F](\<lambda>_. 1) \<and> (\<forall>\<^sub>F x in F. x1 x = c + f x * h x)) \<Longrightarrow> asymp_powser x1 x2"
  using asymp_powser.coinduct[of P x1 x2] by blast
    
lemma asymp_powser_coinduct' [case_names asymp_powser]:
  "P x1 x2 \<Longrightarrow> (\<And>x1 x2.  P x1 x2 \<Longrightarrow> \<exists>f cs c.
       x2 = MSSCons c cs \<and> P f cs \<and>
       x1 \<in> O[F](\<lambda>_. 1) \<and> (\<forall>\<^sub>F x in F. x1 x = c + f x * h x)) \<Longrightarrow> asymp_powser x1 x2"
  using asymp_powser.coinduct[of P x1 x2] by blast
  
lemma asymp_powser_transfer:
  assumes "asymp_powser f cs" "eventually (\<lambda>x. f x = f' x) F"
  shows   "asymp_powser f' cs"
  using assms(1)
proof (cases rule: asymp_powser.cases)
  case (1 f cs' c)
  have "asymp_powser f' (MSSCons c cs')"
    by (rule asymp_powser.intros) 
       (insert 1 assms(2), auto elim: eventually_elim2 dest: landau_o.big.in_cong)
  thus ?thesis by (simp add: 1)
qed

lemma sum_bigo_imp_asymp_powser:
  assumes filterlim_h: "filterlim h (at 0) F"
  assumes "(\<And>n. (\<lambda>x. f x - (\<Sum>k<n. mssnth cs k * h x ^ k)) \<in> O[F](\<lambda>x. h x ^ n))"
  shows   "asymp_powser f cs"
  using assms(2)
proof (coinduction arbitrary: f cs rule: asymp_powser_coinduct')
  case (asymp_powser f cs)
  from filterlim_h have h_nz:"eventually (\<lambda>x. h x \<noteq> 0) F"
    by (auto simp: filterlim_at)
  show ?case
  proof (cases cs)
    case (MSSCons c cs')
    define f' where "f' = (\<lambda>x. (f x - c) / h x)"  
    have "(\<lambda>x. f' x - (\<Sum>k<n. mssnth cs' k * h x ^ k)) \<in> O[F](\<lambda>x. h x ^ n)" for n
    proof -
      have "(\<lambda>x. h x * (f' x - (\<Sum>i<n. mssnth cs' i * h x ^ i))) \<in>
                \<Theta>[F](\<lambda>x. f x - c - h x * (\<Sum>i<n. mssnth cs' i * h x ^ i))"
        using h_nz by (intro bigthetaI_cong) (auto elim!: eventually_mono simp: f'_def field_simps)
      also from spec[OF asymp_powser, of "Suc n"]
        have "(\<lambda>x. f x - c - h x * (\<Sum>i<n. mssnth cs' i * h x ^ i)) \<in> O[F](\<lambda>x. h x * h x ^ n)"
        unfolding sum.lessThan_Suc_shift
        by (simp add: MSSCons algebra_simps sum_distrib_left sum_distrib_right)
      finally show ?thesis
        by (subst (asm) landau_o.big.mult_cancel_left) (insert h_nz, auto)
    qed
    moreover from h_nz have "\<forall>\<^sub>F x in F. f x = c + f' x * h x"
      by eventually_elim (simp add: f'_def)
    ultimately show ?thesis using spec[OF asymp_powser, of 0]
      by (auto simp: MSSCons intro!: exI[of _ f'])
  qed
qed

end


lemma asymp_powser_o:
  assumes "asymp_powser h F f cs" assumes "filterlim g F G"
  shows   "asymp_powser (h \<circ> g) G (f \<circ> g) cs"
using assms(1)
proof (coinduction arbitrary: f cs rule: asymp_powser_coinduct')
  case (asymp_powser f cs)
  thus ?case
  proof (cases rule: asymp_powser.cases)
    case (1 f' cs' c)
    from assms(2) have "filtermap g G \<le> F" by (simp add: filterlim_def)
    moreover have "eventually (\<lambda>x. f x = c + f' x * h x) F" by fact
    ultimately have "eventually (\<lambda>x. f x = c + f' x * h x) (filtermap g G)" by (rule filter_leD)
    hence "eventually (\<lambda>x. f (g x) = c + f' (g x) * h (g x)) G" by (simp add: eventually_filtermap)
    moreover from 1 have "f \<circ> g \<in> O[G](\<lambda>_. 1)" unfolding o_def
      by (intro landau_o.big.compose[OF _ assms(2)]) auto
    ultimately show ?thesis using 1 by force
  qed
qed

lemma asymp_powser_compose:
  assumes "asymp_powser h F f cs" assumes "filterlim g F G"
  shows   "asymp_powser (\<lambda>x. h (g x)) G (\<lambda>x. f (g x)) cs"
  using asymp_powser_o[OF assms] by (simp add: o_def)

lemma hd_exp_powser': "ms_aux_hd_exp (powser_ms_aux' cs f) = Some 0"
  by (simp add: powser_ms_aux'_def hd_exp_powser)

lemma powser_ms_aux_asymp_powser:
  assumes "asymp_powser h at_top f cs" and basis: "basis_wf bs"
  assumes "is_expansion_aux xs h bs" "ms_exp_gt 0 (ms_aux_hd_exp xs)"
  shows   "is_expansion_aux (powser_ms_aux' cs xs) f bs"
using assms(1)
proof (coinduction arbitrary: cs f rule: is_expansion_aux_coinduct_upto)
  show "basis_wf bs" by fact
next
  case (B cs f)
  thus ?case
  proof (cases rule: asymp_powser.cases)
    case (1 f' cs' c)
    from assms(3) obtain b bs' where [simp]: "bs = b # bs'"
      by (cases bs) (auto dest: is_expansion_aux_basis_nonempty)
    from basis have b_at_top: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
    hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (auto simp: filterlim_at_top_dense)
    
    have A: "f \<in> o(\<lambda>x. b x powr e)" if "e > 0" for e :: real
    proof -
      have "f \<in> O(\<lambda>_. 1)" by fact
      also have "(\<lambda>_::real. 1) \<in> o(\<lambda>x. b x powr e)"
        by (rule landau_o.small.compose[OF _ b_at_top]) (insert that, simp_all add: one_smallo_powr)
      finally show ?thesis .
    qed
    have "ms_closure (\<lambda>xsa'' fa'' basis''.
            \<exists>cs. xsa'' = powser_ms_aux' cs xs \<and> basis'' = b # bs' \<and> asymp_powser h at_top fa'' cs)
           (times_ms_aux xs (powser_ms_aux' cs' xs)) (\<lambda>x. h x * f' x) bs" 
      (is "ms_closure ?Q ?ys _ _")
      by (rule ms_closure_mult[OF ms_closure_embed' ms_closure_embed])
         (insert assms 1, auto intro!: exI[of _ cs'])
    moreover have "eventually (\<lambda>x. h x * f' x = f x - c * b x powr 0) at_top"
      using b_pos and \<open>\<forall>\<^sub>F x in at_top. f x = c + f' x * h x\<close>
      by eventually_elim simp
    ultimately have "ms_closure ?Q ?ys (\<lambda>x. f x - c * b x powr 0) bs"
      by (rule ms_closure_cong)
    with 1 assms A show ?thesis
      using is_expansion_aux_expansion_level[OF assms(3)]
      by (auto simp: powser_ms_aux'_MSSCons basis_wf_Cons hd_exp_times hd_exp_powser'
               intro!: is_expansion_const ms_closure_add ms_closure_mult split: option.splits)
  qed
qed


subsubsection \<open>Arc tangent\<close>

definition arctan_ms_aux where
  "arctan_ms_aux xs = times_ms_aux xs (powser_ms_aux' arctan_series_stream (times_ms_aux xs xs))"

lemma arctan_ms_aux_0:
  assumes "ms_exp_gt 0 (ms_aux_hd_exp xs)" "basis_wf basis" "is_expansion_aux xs f basis"
  shows   "is_expansion_aux (arctan_ms_aux xs) (\<lambda>x. arctan (f x)) basis" 
proof (rule is_expansion_aux_cong)
  let ?g = "powser (msllist_of_msstream arctan_series_stream)"
  show "is_expansion_aux (arctan_ms_aux xs)
          (\<lambda>x. f x * (?g \<circ> (\<lambda>x. f x * f x)) x) basis"
    unfolding arctan_ms_aux_def powser_ms_aux'_def using assms
    by (intro times_ms_aux powser_ms_aux powser_ms_aux convergent_powser_arctan)
       (auto simp: hd_exp_times add_neg_neg split: option.splits)
  
  have "f \<in> o(\<lambda>x. hd basis x powr 0)" using assms
    by (intro is_expansion_aux_imp_smallo[OF assms(3)]) auto
  also have "(\<lambda>x. hd basis x powr 0) \<in> O(\<lambda>_. 1)"
    by (intro bigoI[of _ 1]) auto
  finally have "filterlim f (nhds 0) at_top"
    by (auto dest!: smalloD_tendsto)
  from order_tendstoD(2)[OF tendsto_norm [OF this], of 1]
    have "eventually (\<lambda>x. norm (f x) < 1) at_top" by simp
  thus "eventually (\<lambda>x. f x * (?g \<circ> (\<lambda>x. f x * f x)) x = arctan (f x)) at_top"
    by eventually_elim (simp add: arctan_conv_pre_arctan power2_eq_square)
qed

lemma arctan_ms_aux_inf:
  assumes "\<exists>e>0. ms_aux_hd_exp xs = Some e" "fst (dominant_term_ms_aux xs) > 0" "trimmed_ms_aux xs" 
          "basis_wf basis" "is_expansion_aux xs f basis"
  shows   "is_expansion_aux (minus_ms_aux (const_ms_aux (pi / 2))
             (arctan_ms_aux (inverse_ms_aux xs))) (\<lambda>x. arctan (f x)) basis"
    (is "is_expansion_aux ?xs' _ _")
proof (rule is_expansion_aux_cong)
  from \<open>trimmed_ms_aux xs\<close> have [simp]: "xs \<noteq> MSLNil" by auto
  thus "is_expansion_aux ?xs' (\<lambda>x. pi / 2 - arctan (inverse (f x))) basis" using assms
    by (intro minus_ms_aux arctan_ms_aux_0 inverse_ms_aux const_ms_aux)
       (auto simp: hd_exp_inverse is_expansion_aux_expansion_level)
next
  from assms(2-5) have "eventually (\<lambda>x. f x > 0) at_top"
    by (intro eval_pos_if_dominant_term_pos') simp_all
  thus "eventually (\<lambda>x. ((\<lambda>x. pi/2 - arctan (inverse (f x)))) x = arctan (f x)) at_top"
    unfolding o_def by eventually_elim (subst arctan_inverse_pos, simp_all)
qed

lemma arctan_ms_aux_neg_inf:
  assumes "\<exists>e>0. ms_aux_hd_exp xs = Some e" "fst (dominant_term_ms_aux xs) < 0" "trimmed_ms_aux xs" 
          "basis_wf basis" "is_expansion_aux xs f basis"
  shows   "is_expansion_aux (minus_ms_aux (const_ms_aux (-pi / 2))
             (arctan_ms_aux (inverse_ms_aux xs))) (\<lambda>x. arctan (f x)) basis"
    (is "is_expansion_aux ?xs' _ _")
proof (rule is_expansion_aux_cong)
  from \<open>trimmed_ms_aux xs\<close> have [simp]: "xs \<noteq> MSLNil" by auto
  thus "is_expansion_aux ?xs' (\<lambda>x. -pi / 2 - arctan (inverse (f x))) basis" using assms
    by (intro minus_ms_aux arctan_ms_aux_0 inverse_ms_aux const_ms_aux)
       (auto simp: hd_exp_inverse is_expansion_aux_expansion_level)
next
  from assms(2-5) have "eventually (\<lambda>x. f x < 0) at_top"
    by (intro eval_neg_if_dominant_term_neg') simp_all
  thus "eventually (\<lambda>x. ((\<lambda>x. -pi/2 - arctan (inverse (f x)))) x = arctan (f x)) at_top"
    unfolding o_def by eventually_elim (subst arctan_inverse_neg, simp_all)
qed

lemma expands_to_arctan_zero:
  assumes "((\<lambda>_::real. 0::real) expands_to C) bs" "eventually (\<lambda>x. f x = 0) at_top"
  shows   "((\<lambda>x::real. arctan (f x)) expands_to C) bs"
  using assms by (auto simp: expands_to.simps elim: eventually_elim2)

lemma expands_to_arctan_ms_neg_exp: 
  assumes "e < 0" "basis_wf basis" "(f expands_to MS (MSLCons (C, e) xs) g) basis"
  shows   "((\<lambda>x. arctan (f x)) expands_to
               MS (arctan_ms_aux (MSLCons (C, e) xs)) (\<lambda>x. arctan (g x))) basis"
  using assms by (auto simp: expands_to.simps snd_dominant_term_ms_aux_MSLCons o_def
                       intro!: arctan_ms_aux_0 elim: eventually_mono)

lemma expands_to_arctan_ms_pos_exp_pos: 
  assumes "e > 0" "trimmed_pos (MS (MSLCons (C, e) xs) g)" "basis_wf basis" 
          "(f expands_to MS (MSLCons (C, e) xs) g) basis"
  shows   "((\<lambda>x. arctan (f x)) expands_to MS (minus_ms_aux (const_ms_aux (pi / 2))
             (arctan_ms_aux (inverse_ms_aux (MSLCons (C, e) xs))))
               (\<lambda>x. arctan (g x))) basis"
  using arctan_ms_aux_inf[of "MSLCons (C, e) xs" basis g] assms
  by (auto simp: expands_to.simps snd_dominant_term_ms_aux_MSLCons o_def
                 dominant_term_ms_aux_MSLCons trimmed_pos_def elim: eventually_mono)

lemma expands_to_arctan_ms_pos_exp_neg: 
  assumes "e > 0" "trimmed_neg (MS (MSLCons (C, e) xs) g)" "basis_wf basis" 
          "(f expands_to MS (MSLCons (C, e) xs) g) basis"
  shows   "((\<lambda>x. arctan (f x)) expands_to MS (minus_ms_aux (const_ms_aux (-pi/2))
             (arctan_ms_aux (inverse_ms_aux (MSLCons (C, e) xs))))
               (\<lambda>x. arctan (g x))) basis"
  using arctan_ms_aux_neg_inf[of "MSLCons (C, e) xs" basis g] assms
  by (auto simp: expands_to.simps snd_dominant_term_ms_aux_MSLCons o_def
                 dominant_term_ms_aux_MSLCons trimmed_neg_def elim: eventually_mono)                     


subsubsection \<open>Exponential function\<close>

(* TODO: Move *)
lemma ln_smallo_powr:
  assumes "(e::real) > 0"
  shows   "(\<lambda>x. ln x) \<in> o(\<lambda>x. x powr e)"
proof -
  have *: "ln \<in> o(\<lambda>x::real. x)"
    using ln_x_over_x_tendsto_0 by (intro smalloI_tendsto) auto
  have "(\<lambda>x. ln x) \<in> \<Theta>(\<lambda>x::real. ln x powr 1)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 1]]) auto
  also have "(\<lambda>x::real. ln x powr 1) \<in> o(\<lambda>x. x powr e)"
    by (intro ln_smallo_imp_flat filterlim_ident ln_at_top assms
              landau_o.small.compose[of _ at_top _ ln] *)
  finally show ?thesis .
qed

lemma basis_wf_insert_exp_pos:
  assumes "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)" 
          "basis_wf (b # basis)" "trimmed (MS (MSLCons (C, e) xs) g)" "e - 0 > 0"
  shows   "(\<lambda>x. ln (b x)) \<in> o(f)"
proof -
  from assms have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" by (simp add: filterlim_at_top_dense)

  from assms have "is_expansion_aux xs (\<lambda>x. g x - eval C x * b x powr e) (b # basis)" 
                  "ms_exp_gt e (ms_aux_hd_exp xs)"
      by (auto elim!: is_expansion_aux_MSLCons simp: expands_to.simps)
  from is_expansion_aux_imp_smallo''[OF this] obtain e' where e':
    "e' < e" "(\<lambda>x. g x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr e')" unfolding list.sel .
  
  define eps where "eps = e/2"
  have "(\<lambda>x. ln (b x)) \<in> o(\<lambda>x. b x powr (e - eps))" unfolding eps_def
    by (rule landau_o.small.compose[OF _ b_limit])
       (insert e'(1) \<open>e - 0 > 0\<close>, simp add: ln_smallo_powr)
  also from assms e'(1) have "eval C \<in> \<omega>(\<lambda>x. b x powr -eps)" unfolding eps_def
    by (intro is_expansion_imp_smallomega[of basis])
       (auto simp: basis_wf_Cons expands_to.simps trimmed_pos_def trimmed_ms_aux_MSLCons
             elim!: is_expansion_aux_MSLCons)
  hence "(\<lambda>x. b x powr -eps * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)"
    by (intro landau_o.small_big_mult) (simp_all add: smallomega_iff_smallo)
  hence "(\<lambda>x. b x powr (e - eps)) \<in> o(\<lambda>x. eval C x * b x powr e)"
    by (simp add: powr_add [symmetric] field_simps)
  finally have "(\<lambda>x. ln (b x)) \<in> o(\<lambda>x. eval C x * b x powr e)" .
  also {
    from e' have "(\<lambda>x. g x - eval C x * b x powr e) \<in> o(\<lambda>x. b x powr (e' - e) * b x powr e)"
      by (simp add: powr_add [symmetric])
    also from assms e'(1) have "eval C \<in> \<omega>(\<lambda>x. b x powr (e' - e))" unfolding eps_def
      by (intro is_expansion_imp_smallomega[of basis])
         (auto simp: basis_wf_Cons expands_to.simps trimmed_pos_def trimmed_ms_aux_MSLCons
               elim!: is_expansion_aux_MSLCons)
    hence "(\<lambda>x. b x powr (e' - e) * b x powr e) \<in> o(\<lambda>x. eval C x * b x powr e)"
      by (intro landau_o.small_big_mult is_expansion_imp_smallo) 
         (simp_all add: smallomega_iff_smallo)
    finally have "o(\<lambda>x. eval C x * b x powr e) = 
                    o(\<lambda>x. g x - eval C x * b x powr e + eval C x * b x powr e)"
      by (intro landau_o.small.plus_absorb1 [symmetric]) simp_all
  }
  also have "o(\<lambda>x. g x - eval C x * b x powr e + eval C x * b x powr e) = o(g)" by simp
  also from assms have "g \<in> \<Theta>(f)" by (intro bigthetaI_cong) (simp add: expands_to.simps)
  finally show "(\<lambda>x. ln (b x)) \<in> o(f)" .
qed

lemma basis_wf_insert_exp_uminus:
  "(\<lambda>x. ln (b x)) \<in> o(f) \<Longrightarrow> (\<lambda>x. ln (b x)) \<in> o(\<lambda>x. -f x :: real)"
  by simp

lemma basis_wf_insert_exp_uminus':
  "f \<in> o(\<lambda>x. ln (b x)) \<Longrightarrow> (\<lambda>x. -f x) \<in> o(\<lambda>x. ln (b x))"
  by simp
    
lemma expands_to_exp_insert_pos:
  fixes C :: "'a :: multiseries"
  assumes "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)" 
          "basis_wf (b # basis)" "trimmed_pos (MS (MSLCons (C, e) xs) g)" 
          "(\<lambda>x. ln (b x)) \<in> o(f)"
  shows   "filterlim (\<lambda>x. exp (f x)) at_top at_top"
          "((\<lambda>x. ln (exp (f x))) expands_to MS (MSLCons (C, e) xs) g) (b # basis)"
          "((\<lambda>x. exp (f x)) expands_to 
             MS (MSLCons (const_expansion 1 :: 'a ms, 1) MSLNil) (\<lambda>x. exp (g x)))
             ((\<lambda>x. exp (f x)) # b # basis)" (is ?thesis3)
proof -
  have "ln \<in> \<omega>(\<lambda>x::real. 1)"
    by (intro smallomegaI_filterlim_at_top_norm)
       (auto intro!: filterlim_compose[OF filterlim_abs_real] ln_at_top)
  with assms have "(\<lambda>x. 1) \<in> o(\<lambda>x. ln (b x))"
    by (intro landau_o.small.compose[of _ at_top _ b])
       (simp_all add: basis_wf_Cons smallomega_iff_smallo)
  also note \<open>(\<lambda>x. ln (b x)) \<in> o(f)\<close>
  finally have f: "f \<in> \<omega>(\<lambda>_. 1)" by (simp add: smallomega_iff_smallo)
  hence f: "filterlim (\<lambda>x. abs (f x)) at_top at_top"
    by (auto dest: smallomegaD_filterlim_at_top_norm)
  
  define c where "c = fst (dominant_term C)"
  define es where "es = snd (dominant_term C)"
  from trimmed_imp_eventually_sgn[OF assms(2), of "MS (MSLCons (C, e) xs) g"] assms 
    have "\<forall>\<^sub>F x in at_top. abs (f x) = f x"
      by (auto simp: dominant_term_ms_aux_MSLCons trimmed_pos_def expands_to.simps sgn_if 
               split: if_splits elim: eventually_elim2)
  from filterlim_cong[OF refl refl this] f 
    show *: "filterlim (\<lambda>x. exp (f x)) at_top at_top" 
    by (auto intro: filterlim_compose[OF exp_at_top])
  
  {
    fix e' :: real assume e': "e' > 1"
    from assms have "(\<lambda>x. exp (g x)) \<in> \<Theta>(\<lambda>x. exp (f x) powr 1)"
      by (intro bigthetaI_cong) (auto elim: eventually_mono simp: expands_to.simps)
    also from e' * have "(\<lambda>x. exp (f x) powr 1) \<in> o(\<lambda>x. exp (f x) powr e')"
      by (subst powr_smallo_iff) (insert *, simp_all)
    finally have "(\<lambda>x. exp (g x)) \<in> o(\<lambda>x. exp (f x) powr e')" .
  }
  with assms show ?thesis3
    by (auto intro!: is_expansion_aux.intros is_expansion_const 
             simp: expands_to.simps is_expansion_aux_expansion_level
             dest: is_expansion_aux_expansion_level)
qed (insert assms, simp_all)
    
lemma expands_to_exp_insert_neg:
  fixes C :: "'a :: multiseries"
  assumes "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)" 
          "basis_wf (b # basis)" "trimmed_neg (MS (MSLCons (C, e) xs) g)" 
          "(\<lambda>x. ln (b x)) \<in> o(f)"
  shows   "filterlim (\<lambda>x. exp (-f x)) at_top at_top" (is ?thesis1)
          "((\<lambda>x. ln (exp (-f x))) expands_to MS (MSLCons (-C, e) (uminus_ms_aux xs)) (\<lambda>x. - g x)) 
             (b # basis)"
          "trimmed_pos (MS (MSLCons (-C, e) (uminus_ms_aux xs)) (\<lambda>x. - g x))"
          "((\<lambda>x. exp (f x)) expands_to 
             MS (MSLCons (const_expansion 1 :: 'a ms, -1) MSLNil) (\<lambda>x. exp (g x)))
             ((\<lambda>x. exp (-f x)) # b # basis)" (is ?thesis3)
proof -
  have "ln \<in> \<omega>(\<lambda>x::real. 1)"
    by (intro smallomegaI_filterlim_at_top_norm)
       (auto intro!: filterlim_compose[OF filterlim_abs_real] ln_at_top)
  with assms have "(\<lambda>x. 1) \<in> o(\<lambda>x. ln (b x))"
    by (intro landau_o.small.compose[of _ at_top _ b])
       (simp_all add: basis_wf_Cons smallomega_iff_smallo)
  also note \<open>(\<lambda>x. ln (b x)) \<in> o(f)\<close>
  finally have f: "f \<in> \<omega>(\<lambda>_. 1)" by (simp add: smallomega_iff_smallo)
  hence f: "filterlim (\<lambda>x. abs (f x)) at_top at_top" 
    by (auto dest: smallomegaD_filterlim_at_top_norm)
  from trimmed_imp_eventually_sgn[OF assms(2), of "MS (MSLCons (C, e) xs) g"] assms 
    have "\<forall>\<^sub>F x in at_top. abs (f x) = -f x"
      by (auto simp: dominant_term_ms_aux_MSLCons trimmed_neg_def expands_to.simps sgn_if 
               split: if_splits elim: eventually_elim2)
  from filterlim_cong[OF refl refl this] f 
    show *: "filterlim (\<lambda>x. exp (-f x)) at_top at_top" 
    by (auto intro: filterlim_compose[OF exp_at_top])
  
  have "((\<lambda>x. -f x) expands_to -MS (MSLCons (C, e) xs) g) (b # basis)"
    by (intro expands_to_uminus assms)
  thus "((\<lambda>x. ln (exp (-f x))) expands_to MS (MSLCons (-C, e) (uminus_ms_aux xs)) (\<lambda>x. - g x)) 
          (b # basis)"
    by (simp add: uminus_ms_aux_MSLCons)
      
  {
    fix e' :: real assume e': "e' > -1"
    from assms have "(\<lambda>x. exp (g x)) \<in> \<Theta>(\<lambda>x. exp (-f x) powr -1)"
      by (intro bigthetaI_cong) 
         (auto elim: eventually_mono simp: expands_to.simps powr_minus exp_minus)
    also from e' * have "(\<lambda>x. exp (-f x) powr -1) \<in> o(\<lambda>x. exp (-f x) powr e')"
      by (subst powr_smallo_iff) (insert *, simp_all)
    finally have "(\<lambda>x. exp (g x)) \<in> o(\<lambda>x. exp (-f x) powr e')" .
  }
  with assms show ?thesis3
    by (auto intro!: is_expansion_aux.intros is_expansion_const 
             simp: expands_to.simps is_expansion_aux_expansion_level powr_minus exp_minus
             dest: is_expansion_aux_expansion_level)
qed (insert assms, simp_all add: trimmed_pos_def trimmed_neg_def 
       trimmed_ms_aux_MSLCons dominant_term_ms_aux_MSLCons)

lemma is_expansion_aux_exp_neg:
  assumes "is_expansion_aux F f basis" "basis_wf basis" "ms_exp_gt 0 (ms_aux_hd_exp F)"
  shows   "is_expansion_aux (powser_ms_aux' exp_series_stream F) (\<lambda>x. exp (f x)) basis"
  using powser_ms_aux'[OF convergent_powser'_exp assms(2,1,3)]
  by (simp add: o_def powser_ms_aux'_def)

lemma is_expansion_exp_neg:
  assumes "is_expansion (MS (MSLCons (C, e) xs) f) basis" "basis_wf basis" "e < 0"
  shows   "is_expansion (MS (powser_ms_aux' exp_series_stream (MSLCons (C, e) xs)) 
             (\<lambda>x. exp (f x))) basis"
  using is_expansion_aux_exp_neg[of "MSLCons (C, e) xs" f basis] assms by simp

lemma expands_to_exp_neg:
  assumes "(f expands_to MS (MSLCons (C, e) xs) g) basis" "basis_wf basis" "e - 0 < 0"
  shows   "((\<lambda>x. exp (f x)) expands_to MS (powser_ms_aux' exp_series_stream (MSLCons (C, e) xs)) 
             (\<lambda>x. exp (g x))) basis"
  using assms is_expansion_exp_neg[of C e xs g basis] by (auto simp: expands_to.simps)

lemma basis_wf_insert_exp_near:
  assumes "basis_wf (b # basis)" "basis_wf ((\<lambda>x. exp (f x)) # basis)" "f \<in> o(\<lambda>x. ln (b x))"
  shows   "basis_wf (b # (\<lambda>x. exp (f x)) # basis)"
  using assms by (simp_all add: basis_wf_Cons)


definition scale_ms_aux' where "scale_ms_aux' c F = scale_shift_ms_aux (c, 0) F"
definition shift_ms_aux where "shift_ms_aux e F = scale_shift_ms_aux (const_expansion 1, e) F"

lemma scale_ms_1 [simp]: "scale_ms 1 F = F"
  by (simp add: scale_ms_def times_const_expansion_1)

lemma scale_ms_aux_1 [simp]: "scale_ms_aux 1 xs = xs"
  by (simp add: scale_ms_aux_def scale_shift_ms_aux_def map_prod_def msllist.map_ident
        case_prod_unfold times_const_expansion_1)
    
lemma scale_ms_aux'_1 [simp]: "scale_ms_aux' (const_expansion 1) xs = xs"
  by (simp add: scale_ms_aux'_def scale_shift_ms_aux_def map_prod_def msllist.map_ident
        case_prod_unfold times_const_expansion_1)
    
lemma shift_ms_aux_0 [simp]: "shift_ms_aux 0 xs = xs"
  by (simp add: shift_ms_aux_def scale_shift_ms_aux_def map_prod_def case_prod_unfold 
        times_const_expansion_1 msllist.map_ident)
  
lemma scale_ms_aux'_MSLNil [simp]: "scale_ms_aux' C MSLNil = MSLNil"
  by (simp add: scale_ms_aux'_def)

lemma scale_ms_aux'_MSLCons [simp]: 
  "scale_ms_aux' C (MSLCons (C', e) xs) = MSLCons (C * C', e) (scale_ms_aux' C xs)"
  by (simp add: scale_ms_aux'_def scale_shift_ms_aux_MSLCons)

lemma shift_ms_aux_MSLNil [simp]: "shift_ms_aux e MSLNil = MSLNil"
  by (simp add: shift_ms_aux_def)

lemma shift_ms_aux_MSLCons [simp]: 
  "shift_ms_aux e (MSLCons (C, e') xs) = MSLCons (C, e' + e) (shift_ms_aux e xs)"
  by (simp add: shift_ms_aux_def scale_shift_ms_aux_MSLCons times_const_expansion_1)

lemma scale_ms_aux:
  fixes xs :: "('a :: multiseries \<times> real) msllist"
  assumes "is_expansion_aux xs f basis" "basis_wf basis"
  shows   "is_expansion_aux (scale_ms_aux c xs) (\<lambda>x. c * f x) basis"
proof (cases basis)
  case (Cons b basis')
  show ?thesis
  proof (rule is_expansion_aux_cong)
    show "is_expansion_aux (scale_ms_aux c xs) 
            (\<lambda>x. eval (const_expansion c :: 'a) x * b x powr 0 * f x) basis"
      using assms unfolding scale_ms_aux_def Cons
      by (intro scale_shift_ms_aux is_expansion_const) 
         (auto simp: basis_wf_Cons dest: is_expansion_aux_expansion_level)
  next
    from assms have "eventually (\<lambda>x. b x > 0) at_top" 
      by (simp add: basis_wf_Cons Cons filterlim_at_top_dense)
    thus "eventually (\<lambda>x. eval (const_expansion c :: 'a) x * b x powr 0 * f x = c * f x) at_top"
      by eventually_elim simp
  qed
qed (insert assms, auto dest: is_expansion_aux_basis_nonempty)

lemma scale_ms_aux':
  assumes "is_expansion_aux xs f (b # basis)" "is_expansion C basis" "basis_wf (b # basis)"
  shows   "is_expansion_aux (scale_ms_aux' C xs) (\<lambda>x. eval C x * f x) (b # basis)"
proof (rule is_expansion_aux_cong)
  show "is_expansion_aux (scale_ms_aux' C xs) (\<lambda>x. eval C x * b x powr 0 * f x) (b # basis)"
    using assms unfolding scale_ms_aux'_def Cons by (intro scale_shift_ms_aux) simp_all
next
  from assms have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: basis_wf_Cons filterlim_at_top_dense)
  thus "eventually (\<lambda>x. eval C x * b x powr 0 * f x = eval C x * f x) at_top"
    by eventually_elim simp
qed

lemma shift_ms_aux:
  fixes xs :: "('a :: multiseries \<times> real) msllist"
  assumes "is_expansion_aux xs f (b # basis)" "basis_wf (b # basis)"
  shows   "is_expansion_aux (shift_ms_aux e xs) (\<lambda>x. b x powr e * f x) (b # basis)"
  unfolding shift_ms_aux_def 
  using scale_shift_ms_aux[OF assms(2,1) is_expansion_const[of _ 1], of e] assms
  by (auto dest!: is_expansion_aux_expansion_level simp: basis_wf_Cons)
  
lemma expands_to_exp_0:
  assumes "(f expands_to MS (MSLCons (MS ys c, e) xs) g) (b # basis)"
          "basis_wf (b # basis)" "e - 0 = 0" "((\<lambda>x. exp (c x)) expands_to E) basis"
  shows   "((\<lambda>x. exp (f x)) expands_to
             MS (scale_ms_aux' E (powser_ms_aux' exp_series_stream xs)) (\<lambda>x. exp (g x))) (b # basis)"
          (is "(_ expands_to MS ?H _) _")
proof -
  from assms have "is_expansion_aux ?H (\<lambda>x. eval E x * exp (g x - c x * b x powr 0)) (b # basis)"
    by (intro scale_ms_aux' is_expansion_aux_exp_neg)
       (auto elim!: is_expansion_aux_MSLCons simp: expands_to.simps)
  moreover {
    from \<open>basis_wf (b # basis)\<close> have "eventually (\<lambda>x. b x > 0) at_top"
      by (simp add: filterlim_at_top_dense basis_wf_Cons)
    moreover from assms(4) have "eventually (\<lambda>x. eval E x = exp (c x)) at_top"
      by (simp add: expands_to.simps)
    ultimately have "eventually (\<lambda>x. eval E x * exp (g x - c x * b x powr 0) = exp (g x)) at_top"
      by eventually_elim (simp add: exp_diff)
  }
  ultimately have "is_expansion_aux ?H (\<lambda>x. exp (g x)) (b # basis)"
    by (rule is_expansion_aux_cong)
  with assms(1) show ?thesis by (simp add: expands_to.simps)
qed

lemma expands_to_exp_0_real:
  assumes "(f expands_to MS (MSLCons (c::real, e) xs) g) [b]" "basis_wf [b]" "e - 0 = 0"
  shows   "((\<lambda>x. exp (f x)) expands_to 
             MS (scale_ms_aux (exp c) (powser_ms_aux' exp_series_stream xs)) (\<lambda>x. exp (g x))) [b]"
          (is "(_ expands_to MS ?H _) _")
proof -
  from assms have "is_expansion_aux ?H (\<lambda>x. exp c * exp (g x - c * b x powr 0)) [b]"
    by (intro scale_ms_aux is_expansion_aux_exp_neg)
       (auto elim!: is_expansion_aux_MSLCons simp: expands_to.simps)
  moreover from \<open>basis_wf [b]\<close> have "eventually (\<lambda>x. b x > 0) at_top"
    by (simp add: filterlim_at_top_dense basis_wf_Cons)
  hence "eventually (\<lambda>x. exp c * exp (g x - c * b x powr 0) = exp (g x)) at_top"
    by eventually_elim (simp add: exp_diff)
  ultimately have "is_expansion_aux ?H (\<lambda>x. exp (g x)) [b]"
    by (rule is_expansion_aux_cong)
  with assms(1) show ?thesis by (simp add: expands_to.simps)
qed

lemma expands_to_exp_0_pull_out1:
  assumes "(f expands_to MS (MSLCons (C, e) xs) g) (b # basis)"
  assumes "((\<lambda>x. ln (b x)) expands_to L) basis" "basis_wf (b # basis)" "e - 0 = 0" "c \<equiv> c"
  shows   "((\<lambda>x. f x - c * ln (b x)) expands_to 
             MS (MSLCons (C - scale_ms c L, e) xs) (\<lambda>x. g x - c * ln (b x))) (b # basis)"
proof -
  from \<open>basis_wf (b # basis)\<close> have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  have "(\<lambda>x. c * ln (b x)) \<in> o(\<lambda>x. b x powr e')" if "e' > 0" for e'
    using that by (intro landau_o.small.compose[OF _ b_limit]) (simp add: ln_smallo_powr)
  hence *: "(\<lambda>x. g x - c * ln (b x)) \<in> o(\<lambda>x. b x powr e')" if "e' > 0" for e' using assms(1,4) that
    by (intro sum_in_smallo) (auto simp: expands_to.simps elim!: is_expansion_aux_MSLCons)
  
  have "is_expansion_aux xs (\<lambda>x. (g x - c * b x powr 0 * eval L x) -
           eval (C - scale_ms c L) x * b x powr e) (b # basis)" 
    (is "is_expansion_aux _ ?h _") using assms
    by (auto simp: expands_to.simps algebra_simps scale_ms_def elim!: is_expansion_aux_MSLCons)
  moreover from b_limit have "eventually (\<lambda>x. b x > 0) at_top"
    by (simp add: filterlim_at_top_dense)
  hence "eventually (\<lambda>x. ?h x = g x - c * ln (b x) - 
           eval (C - const_expansion c * L) x * b x powr e) at_top" 
    (is "eventually (\<lambda>x. _ = ?h x) _") using assms(2)
    apply (simp add: expands_to.simps scale_ms_def)
    by (smt (verit) eventually_cong)
  ultimately have **: "is_expansion_aux xs ?h (b # basis)" 
    by (rule is_expansion_aux_cong)
  from assms(1,4) have "ms_exp_gt 0 (ms_aux_hd_exp xs)" "is_expansion C basis"
    by (auto simp: expands_to.simps elim!: is_expansion_aux_MSLCons)
  moreover from assms(1) have "length basis = expansion_level TYPE('a)"
    by (auto simp: expands_to.simps dest: is_expansion_aux_expansion_level)
  ultimately have "is_expansion_aux (MSLCons (C - scale_ms c L, e) xs) 
                     (\<lambda>x. g x - c * ln (b x)) (b # basis)" 
    using assms unfolding scale_ms_def
    by (intro is_expansion_aux.intros is_expansion_minus is_expansion_mult is_expansion_const * **)
       (simp_all add: basis_wf_Cons expands_to.simps)
  with assms(1) show ?thesis by (auto simp: expands_to.simps)
qed
    
lemma expands_to_exp_0_pull_out2:
  assumes "((\<lambda>x. exp (f x - c * ln (b x))) expands_to MS xs g) (b # basis)"
  assumes "basis_wf (b # basis)"
  shows   "((\<lambda>x. exp (f x)) expands_to MS (shift_ms_aux c xs) 
             (\<lambda>x. b x powr c * g x)) (b # basis)"
proof (rule expands_to.intros)
  show "is_expansion (MS (shift_ms_aux c xs) (\<lambda>x. b x powr c * g x)) (b # basis)"
    using assms unfolding expands_to.simps by (auto intro!: shift_ms_aux)
  from assms have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: basis_wf_Cons filterlim_at_top_dense)
  with assms(1)
  show "\<forall>\<^sub>F x in at_top. eval (MS (shift_ms_aux c xs) (\<lambda>x. b x powr c * g x)) x = exp (f x)"
    by (auto simp: expands_to.simps exp_diff powr_def elim: eventually_elim2)
qed

lemma expands_to_exp_0_pull_out2_nat:
  assumes "((\<lambda>x. exp (f x - c * ln (b x))) expands_to MS xs g) (b # basis)"
  assumes "basis_wf (b # basis)" "c = real n"
  shows   "((\<lambda>x. exp (f x)) expands_to MS (shift_ms_aux c xs) 
             (\<lambda>x. b x ^ n * g x)) (b # basis)"
using expands_to_exp_0_pull_out2[OF assms(1-2)]
proof (rule expands_to_cong')
  from assms(2) have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: filterlim_at_top_dense basis_wf_Cons)
  with assms(3) show "eventually (\<lambda>x. b x powr c * g x = b x ^ n * g x) at_top"
    by (auto elim!: eventually_mono simp: powr_realpow)
qed

lemma expands_to_exp_0_pull_out2_neg_nat:
  assumes "((\<lambda>x. exp (f x - c * ln (b x))) expands_to MS xs g) (b # basis)"
  assumes "basis_wf (b # basis)" "c = -real n"
  shows   "((\<lambda>x. exp (f x)) expands_to MS (shift_ms_aux c xs) 
             (\<lambda>x. g x / b x ^ n)) (b # basis)"
using expands_to_exp_0_pull_out2[OF assms(1-2)]
proof (rule expands_to_cong')
  from assms(2) have "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: filterlim_at_top_dense basis_wf_Cons)
  with assms(3) show "eventually (\<lambda>x. b x powr c * g x = g x / b x ^ n) at_top"
    by (auto elim!: eventually_mono simp: powr_realpow powr_minus field_split_simps)
qed

lemma eval_monom_collapse: "c * eval_monom (c', es) basis x = eval_monom (c * c', es) basis x"
  by (simp add: eval_monom_def)

lemma eval_monom_1_conv: "eval_monom a basis = (\<lambda>x. fst a * eval_monom (1, snd a) basis x)"
  by (simp add: eval_monom_def case_prod_unfold)


subsubsection \<open>Comparing exponent lists\<close>

primrec flip_cmp_result where
  "flip_cmp_result LT = GT"
| "flip_cmp_result GT = LT"
| "flip_cmp_result EQ = EQ"

fun compare_lists :: "real list \<Rightarrow> real list \<Rightarrow> cmp_result" where
  "compare_lists [] [] = EQ"
| "compare_lists (a # as) (b # bs) = 
     (if a < b then LT else if b < a then GT else compare_lists as bs)"
| "compare_lists _ _ = undefined"

declare compare_lists.simps [simp del]
  
lemma compare_lists_Nil [simp]: "compare_lists [] [] = EQ" by (fact compare_lists.simps)

lemma compare_lists_Cons [simp]:
  "a < b \<Longrightarrow> compare_lists (a # as) (b # bs) = LT"
  "a > b \<Longrightarrow> compare_lists (a # as) (b # bs) = GT"
  "a = b \<Longrightarrow> compare_lists (a # as) (b # bs) = compare_lists as bs"
  by (simp_all add: compare_lists.simps(2))

lemma flip_compare_lists:
  "length as = length bs \<Longrightarrow> flip_cmp_result (compare_lists as bs) = compare_lists bs as"
  by (induction as bs rule: compare_lists.induct) (auto simp: compare_lists.simps(2))

lemma compare_lists_induct [consumes 1, case_names Nil Eq Neq]:
  fixes as bs :: "real list"
  assumes "length as = length bs"
  assumes "P [] []"
  assumes "\<And>a as bs. P as bs \<Longrightarrow> P (a # as) (a # bs)"
  assumes "\<And>a as b bs. a \<noteq> b \<Longrightarrow> P (a # as) (b # bs)"
  shows   "P as bs"
  using assms(1)
proof (induction as bs rule: list_induct2)
  case (Cons a as b bs)
  thus ?case by (cases "a < b") (auto intro: assms)
qed (simp_all add: assms)
  

lemma eval_monom_smallo_eval_monom:
  assumes "length es1 = length es2" "length es2 = length basis" "basis_wf basis"
  assumes "compare_lists es1 es2 = LT"
  shows   "eval_monom (1, es1) basis \<in> o(eval_monom (1, es2) basis)"
using assms
proof (induction es1 es2 basis rule: list_induct3)
  case (Cons e1 es1 e2 es2 b basis)
  show ?case
  proof (cases "e1 = e2")
    case True
    from Cons.prems have "eventually (\<lambda>x. b x > 0) at_top" 
      by (simp add: basis_wf_Cons filterlim_at_top_dense)
    with Cons True show ?thesis
      by (auto intro: landau_o.small_big_mult simp: eval_monom_Cons basis_wf_Cons)
  next
    case False
    with Cons.prems have "e1 < e2" by (cases e1 e2 rule: linorder_cases) simp_all
    with Cons.prems have
       "(\<lambda>x. eval_monom (1, es1) basis x * eval_monom (inverse_monom (1, es2)) basis x *
           b x powr e1) \<in> o(\<lambda>x. b x powr ((e2 - e1)/2) * b x powr ((e2 - e1)/2) * b x powr e1)"
      (is "?f \<in> _") by (intro landau_o.small_big_mult[OF _ landau_o.big_refl] landau_o.small.mult 
                          eval_monom_smallo') simp_all
    also have "\<dots> = o(\<lambda>x. b x powr e2)" by (simp add: powr_add [symmetric])
    also have "?f = (\<lambda>x. eval_monom (1, e1 # es1) (b # basis) x / eval_monom (1, es2) basis x)"
      by (simp add: eval_inverse_monom field_simps eval_monom_Cons)
    also have "\<dots> \<in> o(\<lambda>x. b x powr e2) \<longleftrightarrow> 
                 eval_monom (1, e1 # es1) (b # basis) \<in> o(eval_monom (1, e2 # es2) (b # basis))"
      using Cons.prems 
      by (subst landau_o.small.divide_eq2)
         (simp_all add: eval_monom_Cons mult_ac eval_monom_nonzero basis_wf_Cons)
    finally show ?thesis .
  qed
qed simp_all

lemma eval_monom_eq:
  assumes "length es1 = length es2" "length es2 = length basis" "basis_wf basis"
  assumes "compare_lists es1 es2 = EQ"
  shows   "eval_monom (1, es1) basis = eval_monom (1, es2) basis"
  using assms
  by (induction es1 es2 basis rule: list_induct3)
     (auto simp: basis_wf_Cons eval_monom_Cons compare_lists.simps(2) split: if_splits)

definition compare_expansions :: "'a :: multiseries \<Rightarrow> 'a \<Rightarrow> cmp_result \<times> real \<times> real" where
  "compare_expansions F G =
     (case compare_lists (snd (dominant_term F)) (snd (dominant_term G)) of
        LT \<Rightarrow> (LT, 0, 0)
      | GT \<Rightarrow> (GT, 0, 0)
      | EQ \<Rightarrow> (EQ, fst (dominant_term F),  fst (dominant_term G)))"

lemma compare_expansions_real:
  "compare_expansions (c1 :: real) c2 = (EQ, c1, c2)"
  by (simp add: compare_expansions_def)

lemma compare_expansions_MSLCons_eval:
  "compare_expansions (MS (MSLCons (C1, e1) xs) f) (MS (MSLCons (C2, e2) ys) g) =
     CMP_BRANCH (COMPARE e1 e2) (LT, 0, 0) (compare_expansions C1 C2) (GT, 0, 0)"
  by (simp add: compare_expansions_def dominant_term_ms_aux_def case_prod_unfold 
        COMPARE_def CMP_BRANCH_def split: cmp_result.splits)

lemma compare_expansions_LT_I:
  assumes "e1 - e2 < 0"
  shows   "compare_expansions (MS (MSLCons (C1, e1) xs) f) (MS (MSLCons (C2, e2) ys) g) = (LT, 0, 0)"
  using assms by (simp add: compare_expansions_MSLCons_eval CMP_BRANCH_def COMPARE_def)

lemma compare_expansions_GT_I:
  assumes "e1 - e2 > 0"
  shows   "compare_expansions (MS (MSLCons (C1, e1) xs) f) (MS (MSLCons (C2, e2) ys) g) = (GT, 0, 0)"
  using assms by (simp add: compare_expansions_MSLCons_eval CMP_BRANCH_def COMPARE_def)

lemma compare_expansions_same_exp:
  assumes "e1 - e2 = 0" "compare_expansions C1 C2 = res"
  shows   "compare_expansions (MS (MSLCons (C1, e1) xs) f) (MS (MSLCons (C2, e2) ys) g) = res"
  using assms by (simp add: compare_expansions_MSLCons_eval CMP_BRANCH_def COMPARE_def)
  

lemma compare_expansions_GT_flip:
  "length (snd (dominant_term F)) = length (snd (dominant_term G)) \<Longrightarrow>
     compare_expansions F G = (GT, c) \<longleftrightarrow> compare_expansions G F = (LT, c)"
  using flip_compare_lists[of "snd (dominant_term F)" "snd (dominant_term G)"]
  by (auto simp: compare_expansions_def split: cmp_result.splits)

lemma compare_expansions_LT:
  assumes "compare_expansions F G = (LT, c, c')" "trimmed G"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
  shows   "f \<in> o(g)"
proof -
  from assms have "f \<in> \<Theta>(eval F)"
    by (auto simp: expands_to.simps eq_commute intro!: bigthetaI_cong)
  also have "eval F \<in> O(eval_monom (1, snd (dominant_term F)) basis)"
    using assms by (intro dominant_term_bigo) (auto simp: expands_to.simps)
  also have "eval_monom (1, snd (dominant_term F)) basis \<in> 
               o(eval_monom (1, snd (dominant_term G)) basis)" using assms 
    by (intro eval_monom_smallo_eval_monom)
       (auto simp: length_dominant_term expands_to.simps is_expansion_length compare_expansions_def
             split: cmp_result.splits)
  also have "eval_monom (1, snd (dominant_term G)) basis \<in> \<Theta>(eval_monom (dominant_term G) basis)"
    by (subst (2) eval_monom_1_conv, subst landau_theta.cmult)
       (insert assms, simp_all add: trimmed_imp_dominant_term_nz)    
  also have "eval_monom (dominant_term G) basis \<in> \<Theta>(g)"
    by (intro asymp_equiv_imp_bigtheta[OF asymp_equiv_symI] dominant_term_expands_to
              asymp_equiv_imp_bigtheta assms)
  finally show ?thesis .
qed

lemma compare_expansions_GT:
  assumes "compare_expansions F G = (GT, c, c')" "trimmed F"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
  shows   "g \<in> o(f)"
  by (rule compare_expansions_LT[OF _ assms(2,4,3)])
     (insert assms, simp_all add: compare_expansions_GT_flip length_dominant_term)

lemma compare_expansions_EQ:
  assumes "compare_expansions F G = (EQ, c, c')" "trimmed F" "trimmed G"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
  shows   "(\<lambda>x. c' * f x) \<sim>[at_top] (\<lambda>x. c * g x)"
proof -
  from assms(1) have c: "c = fst (dominant_term F)" "c' = fst (dominant_term G)"
    by (auto simp: compare_expansions_def split: cmp_result.splits)
  have "(\<lambda>x. c' * f x) \<sim>[at_top] (\<lambda>x. c' * (c * eval_monom (1, snd (dominant_term F)) basis x))" 
    unfolding c by (rule asymp_equiv_mult, rule asymp_equiv_refl, subst eval_monom_collapse)
                   (auto intro: dominant_term_expands_to assms)
  also have "eval_monom (1, snd (dominant_term F)) basis =
               eval_monom (1, snd (dominant_term G)) basis" using assms
    by (intro eval_monom_eq)
       (simp_all add: compare_expansions_def length_dominant_term is_expansion_length 
          expands_to.simps split: cmp_result.splits)
  also have "(\<lambda>x. c' * (c * \<dots> x)) = (\<lambda>x. c * (c' * \<dots> x))" by (simp add: mult_ac)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. c * g x)"
    unfolding c by (rule asymp_equiv_mult, rule asymp_equiv_refl, subst eval_monom_collapse, 
                       rule asymp_equiv_symI)  (auto intro: dominant_term_expands_to assms)
  finally show ?thesis by (simp add: asymp_equiv_sym)
qed

lemma compare_expansions_EQ_imp_bigo:
  assumes "compare_expansions F G = (EQ, c, c')" "trimmed G"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
  shows   "f \<in> O(g)"
proof -
  from assms(1) have c: "c = fst (dominant_term F)" "c' = fst (dominant_term G)"
    by (auto simp: compare_expansions_def split: cmp_result.splits)
  from assms(3) have [simp]: "expansion_level TYPE('a) = length basis"
    by (auto simp: expands_to.simps is_expansion_length)

  have "f \<in> \<Theta>(eval F)"
    using assms by (intro bigthetaI_cong) (auto simp: expands_to.simps eq_commute)
  also have "eval F \<in> O(eval_monom (1, snd (dominant_term F)) basis)"
    using assms by (intro dominant_term_bigo assms) (auto simp: expands_to.simps)
  also have "eval_monom (1, snd (dominant_term F)) basis =
               eval_monom (1, snd (dominant_term G)) basis" using assms
    by (intro eval_monom_eq) (auto simp: compare_expansions_def case_prod_unfold
                                length_dominant_term split: cmp_result.splits)
  also have "\<dots> \<in> O(eval_monom (dominant_term G) basis)" using assms(2)
    by (auto simp add: eval_monom_def case_prod_unfold dest: trimmed_imp_dominant_term_nz)
  also have "eval_monom (dominant_term G) basis \<in> \<Theta>(eval G)"
    by (rule asymp_equiv_imp_bigtheta, rule asymp_equiv_symI, rule dominant_term)
       (insert assms, auto simp: expands_to.simps)
  also have "eval G \<in> \<Theta>(g)"
    using assms by (intro bigthetaI_cong) (auto simp: expands_to.simps)
  finally show ?thesis .
qed

lemma compare_expansions_EQ_same:
  assumes "compare_expansions F G = (EQ, c, c')" "trimmed F" "trimmed G"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
          "c = c'"
  shows   "f \<sim>[at_top] g"
proof -
  from assms have [simp]: "c' \<noteq> 0" 
    by (auto simp: compare_expansions_def trimmed_imp_dominant_term_nz split: cmp_result.splits)
  have "(\<lambda>x. inverse c * (c' * f x)) \<sim>[at_top] (\<lambda>x. inverse c * (c * g x))"
    by (rule asymp_equiv_mult[OF asymp_equiv_refl]) (rule compare_expansions_EQ[OF assms(1-6)])
  with assms(7) show ?thesis by (simp add: field_split_simps)
qed
  
lemma compare_expansions_EQ_imp_bigtheta:
  assumes "compare_expansions F G = (EQ, c, c')" "trimmed F" "trimmed G"
          "(f expands_to F) basis" "(g expands_to G) basis" "basis_wf basis"
  shows   "f \<in> \<Theta>(g)"
proof -
  from assms have "(\<lambda>x. c' * f x) \<in> \<Theta>(\<lambda>x. c * g x)"
    by (intro asymp_equiv_imp_bigtheta compare_expansions_EQ)
  moreover from assms have "c \<noteq> 0" "c' \<noteq> 0"
    by (auto simp: compare_expansions_def trimmed_imp_dominant_term_nz split: cmp_result.splits)
  ultimately show ?thesis by simp
qed

lemma expands_to_MSLCons_0_asymp_equiv_hd:
  assumes "(f expands_to (MS (MSLCons (C, 0) xs) g)) basis" "trimmed (MS (MSLCons (C, 0) xs) f)"
          "basis_wf basis"
  shows   "f \<sim>[at_top] eval C"
proof -
  from assms(1) is_expansion_aux_basis_nonempty obtain b basis' where [simp]: "basis = b # basis'"
    by (cases basis) (auto simp: expands_to.simps)
  from assms have b_pos: "eventually (\<lambda>x. b x > 0) at_top" 
    by (simp add: filterlim_at_top_dense basis_wf_Cons)
  from assms have "f \<sim>[at_top] eval_monom (dominant_term (MS (MSLCons (C, 0) xs) g)) basis" 
    by (intro dominant_term_expands_to) simp_all
  also have "\<dots> = (\<lambda>x. eval_monom (dominant_term C) basis' x * b x powr 0)"
    by (simp_all add: dominant_term_ms_aux_def case_prod_unfold eval_monom_Cons)
  also have "eventually (\<lambda>x. \<dots> x = eval_monom (dominant_term C) basis' x) at_top"
    using b_pos by eventually_elim simp
  also from assms have "eval_monom (dominant_term C) basis' \<sim>[at_top] eval C"
    by (intro asymp_equiv_symI [OF dominant_term_expands_to] 
          expands_to_hd''[of f C 0 xs g b basis']) (auto simp: trimmed_ms_aux_MSLCons basis_wf_Cons)
  finally show ?thesis .
qed
    
  
lemma compare_expansions_LT':
  assumes "compare_expansions (MS ys h) G \<equiv> (LT, c, c')" "trimmed G"
          "(f expands_to (MS (MSLCons (MS ys h, e) xs) f')) (b # basis)" "(g expands_to G) basis"
          "e = 0" "basis_wf (b # basis)"
  shows   "h \<in> o(g)"   
proof -
  from assms show ?thesis
    by (intro compare_expansions_LT[OF _ assms(2) _ assms(4)])
       (auto intro: expands_to_hd'' simp: trimmed_ms_aux_MSLCons basis_wf_Cons expands_to.simps 
             elim!: is_expansion_aux_MSLCons)
qed

lemma compare_expansions_GT':
  assumes "compare_expansions C G \<equiv> (GT, c, c')"
          "trimmed (MS (MSLCons (C, e) xs) f')"
          "(f expands_to (MS (MSLCons (C, e) xs) f')) (b # basis)" "(g expands_to G) basis"
          "e = 0" "basis_wf (b # basis)"
  shows   "g \<in> o(f)"
proof -
  from assms have "g \<in> o(eval C)"
    by (intro compare_expansions_GT[of C G c c' _ basis])
       (auto intro: expands_to_hd'' simp: trimmed_ms_aux_MSLCons basis_wf_Cons)
  also from assms have "f \<in> \<Theta>(eval C)"
    by (intro asymp_equiv_imp_bigtheta expands_to_MSLCons_0_asymp_equiv_hd[of f C xs f' "b#basis"])
       auto
  finally show ?thesis .
qed

lemma compare_expansions_EQ':
  assumes "compare_expansions C G = (EQ, c, c')" 
          "trimmed (MS (MSLCons (C, e) xs) f')" "trimmed G"
          "(f expands_to (MS (MSLCons (C, e) xs) f')) (b # basis)" "(g expands_to G) basis"
          "e = 0" "basis_wf (b # basis)"
  shows   "f \<sim>[at_top] (\<lambda>x. c / c' * g x)" 
proof -
  from assms have [simp]: "c' \<noteq> 0" 
    by (auto simp: compare_expansions_def trimmed_imp_dominant_term_nz split: cmp_result.splits)
  from assms have "f \<sim>[at_top] eval C"
    by (intro expands_to_MSLCons_0_asymp_equiv_hd[of f C xs f' "b#basis"]) auto
  also from assms(2,4,7) have *: "(\<lambda>x. c' * eval C x) \<sim>[at_top] (\<lambda>x. c * g x)"
    by (intro compare_expansions_EQ[OF assms(1) _ assms(3) _ assms(5)])
       (auto intro: expands_to_hd'' simp: trimmed_ms_aux_MSLCons basis_wf_Cons)
  have "(\<lambda>x. inverse c' * (c' * eval C x)) \<sim>[at_top] (\<lambda>x. inverse c' * (c * g x))"
    by (rule asymp_equiv_mult) (insert *, simp_all)
  hence "eval C \<sim>[at_top] (\<lambda>x. c / c' * g x)" by (simp add: field_split_simps)
  finally show ?thesis .
qed

lemma expands_to_insert_ln: 
  assumes "basis_wf [b]"
  shows   "((\<lambda>x. ln (b x)) expands_to MS (MSLCons (1::real,1) MSLNil) (\<lambda>x. ln (b x))) [\<lambda>x. ln (b x)]"
proof -
  from assms have b_limit: "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b: "eventually (\<lambda>x. b x > 1) at_top" by (simp add: filterlim_at_top_dense)
  have "(\<lambda>x::real. x) \<in> \<Theta>(\<lambda>x. x powr 1)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]]) auto
  also have "(\<lambda>x::real. x powr 1) \<in> o(\<lambda>a. a powr e)" if "e > 1" for e
    by (subst powr_smallo_iff) (auto simp: that filterlim_ident)
  finally show ?thesis using b assms
    by (auto intro!: is_expansion_aux.intros landau_o.small.compose[of _ at_top _ "\<lambda>x. ln (b x)"]
                     filterlim_compose[OF ln_at_top b_limit] is_expansion_real.intros
             elim!: eventually_mono simp: expands_to.simps)
qed

lemma trimmed_pos_insert_ln:
  assumes "basis_wf [b]"
  shows   "trimmed_pos (MS (MSLCons (1::real, 1) MSLNil) (\<lambda>x. ln (b x)))"
  by (simp_all add: trimmed_ms_aux_def)


primrec compare_list_0 where
  "compare_list_0 [] = EQ"
| "compare_list_0 (c # cs) = CMP_BRANCH (COMPARE c 0) LT (compare_list_0 cs) GT"


lemma compare_reals_diff_sgnD:
  "a - (b :: real) < 0 \<Longrightarrow> a < b" "a - b = 0 \<Longrightarrow> a = b" "a - b > 0 \<Longrightarrow> a > b"
  by simp_all

lemma expands_to_real_imp_filterlim:
  assumes "(f expands_to (c :: real)) basis"
  shows   "(f \<longlongrightarrow> c) at_top"
  using assms by (auto elim!: expands_to.cases simp: eq_commute[of c] tendsto_eventually)

lemma expands_to_MSLNil_imp_filterlim:
  assumes "(f expands_to MS MSLNil f') basis"
  shows   "(f \<longlongrightarrow> 0) at_top"
proof -
  from assms have "eventually (\<lambda>x. f' x = 0) at_top" "eventually (\<lambda>x. f' x = f x) at_top"
    by (auto elim!: expands_to.cases is_expansion_aux.cases[of MSLNil])
  hence "eventually (\<lambda>x. f x = 0) at_top" by eventually_elim auto
  thus ?thesis by (simp add: tendsto_eventually)
qed

lemma expands_to_neg_exponent_imp_filterlim:
  assumes "(f expands_to MS (MSLCons (C, e) xs) f') basis" "basis_wf basis" "e < 0"
  shows   "(f \<longlongrightarrow> 0) at_top"
proof -
  let ?F = "MS (MSLCons (C, e) xs) f'"
  let ?es = "snd (dominant_term ?F)"
  from assms have exp: "is_expansion ?F basis"
    by (simp add: expands_to.simps)
  from assms have "f \<in> \<Theta>(f')" by (intro bigthetaI_cong) (simp add: expands_to.simps eq_commute)
  also from dominant_term_bigo[OF assms(2) exp]
    have "f' \<in> O(eval_monom (1, ?es) basis)" by simp
  also have "(eval_monom (1, ?es) basis) \<in> o(\<lambda>x. hd basis x powr 0)" using exp assms
    by (intro eval_monom_smallo)
       (auto simp: is_expansion_aux_basis_nonempty dominant_term_ms_aux_def
                   case_prod_unfold length_dominant_term is_expansion_aux_expansion_level)
  also have "(\<lambda>x. hd basis x powr 0) \<in> O(\<lambda>_. 1)"
    by (intro landau_o.bigI[of 1]) auto
  finally show ?thesis by (auto dest!: smalloD_tendsto)
qed

lemma expands_to_pos_exponent_imp_filterlim:
  assumes "(f expands_to MS (MSLCons (C, e) xs) f') basis" "trimmed (MS (MSLCons (C, e) xs) f')"
          "basis_wf basis" "e > 0"
  shows   "filterlim f at_infinity at_top"
proof -
  let ?F = "MS (MSLCons (C, e) xs) f'"
  let ?es = "snd (dominant_term ?F)"
  from assms have exp: "is_expansion ?F basis"
    by (simp add: expands_to.simps)
  with assms have "filterlim (hd basis) at_top at_top"
    using is_expansion_aux_basis_nonempty[of "MSLCons (C, e) xs" f' basis]
    by (cases basis) (simp_all add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. hd basis x > 0) at_top" using filterlim_at_top_dense by blast

  from assms have "f \<in> \<Theta>(f')" by (intro bigthetaI_cong) (simp add: expands_to.simps eq_commute)
  also from dominant_term[OF assms(3) exp assms(2)]
    have "f' \<in> \<Theta>(eval_monom (dominant_term ?F) basis)" by (simp add: asymp_equiv_imp_bigtheta)
  also have "(eval_monom (dominant_term ?F) basis) \<in> \<Theta>(eval_monom (1, ?es) basis)"
    using assms by (simp add: eval_monom_def case_prod_unfold dominant_term_ms_aux_def 
                              trimmed_imp_dominant_term_nz trimmed_ms_aux_def)
  also have "eval_monom (1, ?es) basis \<in> \<omega>(\<lambda>x. hd basis x powr 0)" using exp assms
    by (intro eval_monom_smallomega)
       (auto simp: is_expansion_aux_basis_nonempty dominant_term_ms_aux_def
                   case_prod_unfold length_dominant_term is_expansion_aux_expansion_level)
  also have "(\<lambda>x. hd basis x powr 0) \<in> \<Theta>(\<lambda>_. 1)"
    by (intro bigthetaI_cong eventually_mono[OF b_pos]) auto
  finally show ?thesis by (auto dest!: smallomegaD_filterlim_at_infinity)
qed

lemma expands_to_zero_exponent_imp_filterlim:
  assumes "(f expands_to MS (MSLCons (C, e) xs) f') basis"
          "basis_wf basis" "e = 0"
  shows   "filterlim (eval C) at_infinity at_top \<Longrightarrow> filterlim f at_infinity at_top"
    and   "filterlim (eval C) (nhds L) at_top \<Longrightarrow> filterlim f (nhds L) at_top"
proof -
  from assms obtain b basis' where *:
    "basis = b # basis'" "is_expansion C basis'" "ms_exp_gt 0 (ms_aux_hd_exp xs)"
    "is_expansion_aux xs (\<lambda>x. f' x - eval C x * b x powr 0) basis"
    by (auto elim!: expands_to.cases is_expansion_aux_MSLCons)

  from *(1) assms have "filterlim b at_top at_top" by (simp add: basis_wf_Cons)
  hence b_pos: "eventually (\<lambda>x. b x > 0) at_top" using filterlim_at_top_dense by blast

  from assms(1) have "eventually (\<lambda>x. f' x = f x) at_top" by (simp add: expands_to.simps)
  hence "eventually (\<lambda>x. f' x - eval C x * b x powr 0 = f x - eval C x) at_top"
    using b_pos by eventually_elim auto
  from *(4) and this have "is_expansion_aux xs (\<lambda>x. f x - eval C x) basis"
    by (rule is_expansion_aux_cong)
  hence "(\<lambda>x. f x - eval C x) \<in> o(\<lambda>x. hd basis x powr 0)"
    by (rule is_expansion_aux_imp_smallo) fact
  also have "(\<lambda>x. hd basis x powr 0) \<in> \<Theta>(\<lambda>_. 1)"
    by (intro bigthetaI_cong eventually_mono[OF b_pos]) (auto simp: *(1))
  finally have lim: "filterlim (\<lambda>x. f x - eval C x) (nhds 0) at_top"
    by (auto dest: smalloD_tendsto)

  show "filterlim f at_infinity at_top" if "filterlim (eval C) at_infinity at_top"
    using tendsto_add_filterlim_at_infinity[OF lim that] by simp
  show "filterlim f (nhds L) at_top" if "filterlim (eval C) (nhds L) at_top"
    using tendsto_add[OF lim that] by simp
qed

lemma expands_to_lift_function:
  assumes "eventually (\<lambda>x. f x - eval c x = 0) at_top"
          "((\<lambda>x. g (eval (c :: 'a :: multiseries) x)) expands_to G) bs'"
  shows   "((\<lambda>x. g (f x)) expands_to G) bs'"
  by (rule expands_to_cong[OF assms(2)]) (insert assms, auto elim: eventually_mono) 

lemma drop_zero_ms':
  fixes c f
  assumes "c = (0::real)" "(f expands_to MS (MSLCons (c, e) xs) g) basis"
  shows   "(f expands_to MS xs g) basis"
  using assms drop_zero_ms[of c e xs g basis] by (simp add: expands_to.simps)

lemma trimmed_realI: "c \<noteq> (0::real) \<Longrightarrow> trimmed c"
  by simp

lemma trimmed_pos_realI: "c > (0::real) \<Longrightarrow> trimmed_pos c"
  by simp

lemma trimmed_neg_realI: "c < (0::real) \<Longrightarrow> trimmed_neg c"
  by (simp add: trimmed_neg_def)

lemma trimmed_pos_hd_coeff: "trimmed_pos (MS (MSLCons (C, e) xs) f) \<Longrightarrow> trimmed_pos C"
  by simp

lemma lift_trimmed: "trimmed C \<Longrightarrow> trimmed (MS (MSLCons (C, e) xs) f)"
  by (auto simp: trimmed_ms_aux_def)

lemma lift_trimmed_pos: "trimmed_pos C \<Longrightarrow> trimmed_pos (MS (MSLCons (C, e) xs) f)"
  by simp

lemma lift_trimmed_neg: "trimmed_neg C \<Longrightarrow> trimmed_neg (MS (MSLCons (C, e) xs) f)"
  by (simp add: trimmed_neg_def fst_dominant_term_ms_aux_MSLCons trimmed_ms_aux_MSLCons)

lemma lift_trimmed_pos':
  "trimmed_pos C \<Longrightarrow> MS (MSLCons (C, e) xs) f \<equiv> MS (MSLCons (C, e) xs) f \<Longrightarrow>
     trimmed_pos (MS (MSLCons (C, e) xs) f)"
  by simp

lemma lift_trimmed_neg':
  "trimmed_neg C \<Longrightarrow> MS (MSLCons (C, e) xs) f \<equiv> MS (MSLCons (C, e) xs) f \<Longrightarrow>
     trimmed_neg (MS (MSLCons (C, e) xs) f)"
  by (simp add: lift_trimmed_neg)

lemma trimmed_eq_cong: "trimmed C \<Longrightarrow> C \<equiv> C' \<Longrightarrow> trimmed C'"
  and trimmed_pos_eq_cong: "trimmed_pos C \<Longrightarrow> C \<equiv> C' \<Longrightarrow> trimmed_pos C'"
  and trimmed_neg_eq_cong: "trimmed_neg C \<Longrightarrow> C \<equiv> C' \<Longrightarrow> trimmed_neg C'"
  by simp_all

lemma trimmed_hd: "trimmed (MS (MSLCons (C, e) xs) f) \<Longrightarrow> trimmed C"
  by (simp add: trimmed_ms_aux_MSLCons)

lemma trim_lift_eq:
  assumes "A \<equiv> MS (MSLCons (C, e) xs) f" "C \<equiv> D"
  shows   "A \<equiv> MS (MSLCons (D, e) xs) f" 
  using assms by simp

lemma basis_wf_manyI: 
  "filterlim b' at_top at_top \<Longrightarrow> (\<lambda>x. ln (b x)) \<in> o(\<lambda>x. ln (b' x)) \<Longrightarrow>
     basis_wf (b # basis) \<Longrightarrow> basis_wf (b' # b # basis)"
  by (simp_all add: basis_wf_many)

lemma ln_smallo_ln_exp: "(\<lambda>x. ln (b x)) \<in> o(f) \<Longrightarrow> (\<lambda>x. ln (b x)) \<in> o(\<lambda>x. ln (exp (f x :: real)))"
  by simp


subsection \<open>Reification and other technical details\<close>

text \<open>
  The following is used by the automation in order to avoid writing terms like $x^2$ or $x^{-2}$
  as \<^term>\<open>\<lambda>x::real. x powr 2\<close> etc.\ but as the more agreeable \<^term>\<open>\<lambda>x::real. x ^ 2\<close> or
  \<^term>\<open>\<lambda>x::real. inverse (x ^ 2)\<close>.
\<close>

lemma intyness_0: "0 \<equiv> real 0"
  and intyness_1: "1 \<equiv> real 1"
  and intyness_numeral: "num \<equiv> num \<Longrightarrow> numeral num \<equiv> real (numeral num)"
  and intyness_uminus:  "x \<equiv> real n \<Longrightarrow> -x \<equiv> -real n"
  and intyness_of_nat:  "n \<equiv> n \<Longrightarrow> real n \<equiv> real n"
  by simp_all
    
lemma intyness_simps:
  "real a + real b = real (a + b)"
  "real a * real b = real (a * b)"
  "real a ^ n = real (a ^ n)"
  "1 = real 1" "0 = real 0" "numeral num = real (numeral num)" 
  by simp_all

lemma odd_Numeral1: "odd (Numeral1)"
  by simp

lemma even_addI:
  "even a \<Longrightarrow> even b \<Longrightarrow> even (a + b)"
  "odd a \<Longrightarrow> odd b \<Longrightarrow> even (a + b)"
  by auto

lemma odd_addI:
  "even a \<Longrightarrow> odd b \<Longrightarrow> odd (a + b)"
  "odd a \<Longrightarrow> even b \<Longrightarrow> odd (a + b)"
  by auto

lemma even_diffI:
  "even a \<Longrightarrow> even b \<Longrightarrow> even (a - b :: int)"
  "odd a \<Longrightarrow> odd b \<Longrightarrow> even (a - b)"
  by auto

lemma odd_diffI:
  "even a \<Longrightarrow> odd b \<Longrightarrow> odd (a - b :: int)"
  "odd a \<Longrightarrow> even b \<Longrightarrow> odd (a - b)"
  by auto

lemma even_multI: "even a \<Longrightarrow> even (a * b)" "even b \<Longrightarrow> even (a * b)"
  by auto

lemma odd_multI: "odd a \<Longrightarrow> odd b \<Longrightarrow> odd (a * b)"
  by auto

lemma even_uminusI: "even a \<Longrightarrow> even (-a :: int)"
  and odd_uminusI:  "odd a \<Longrightarrow> odd (-a :: int)"
  by auto

lemma odd_powerI: "odd a \<Longrightarrow> odd (a ^ n)"
  by auto


text \<open>
  The following theorem collection is used to pre-process functions for multiseries expansion.
\<close>
named_theorems real_asymp_reify_simps

lemmas [real_asymp_reify_simps] =
  sinh_field_def cosh_field_def tanh_real_altdef arsinh_def arcosh_def artanh_def


text \<open>
  This is needed in order to handle things like \<^term>\<open>\<lambda>n. f n ^ n\<close>.
\<close>
definition powr_nat :: "real \<Rightarrow> real \<Rightarrow> real" where 
  "powr_nat x y = 
     (if y = 0 then 1
      else if x < 0 then cos (pi * y) * (-x) powr y else x powr y)"
  
lemma powr_nat_of_nat: "powr_nat x (of_nat n) = x ^ n"
  by (cases "x > 0") (auto simp: powr_nat_def powr_realpow not_less power_mult_distrib [symmetric])

lemma powr_nat_conv_powr: "x > 0 \<Longrightarrow> powr_nat x y = x powr y"
  by (simp_all add: powr_nat_def)

lemma reify_power: "x ^ n \<equiv> powr_nat x (of_nat n)"
  by (simp add: powr_nat_of_nat)


lemma sqrt_conv_root [real_asymp_reify_simps]: "sqrt x = root 2 x"
  by (simp add: sqrt_def)

lemma tan_conv_sin_cos [real_asymp_reify_simps]: "tan x = sin x / cos x"
  by (simp add: tan_def)

definition rfloor :: "real \<Rightarrow> real" where "rfloor x = real_of_int (floor x)"
definition rceil :: "real \<Rightarrow> real" where "rceil x = real_of_int (ceiling x)"
definition rnatmod :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rnatmod x y = real (nat \<lfloor>x\<rfloor> mod nat \<lfloor>y\<rfloor>)"
definition rintmod :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rintmod x y = real_of_int (\<lfloor>x\<rfloor> mod \<lfloor>y\<rfloor>)"

lemmas [real_asymp_reify_simps] =
  ln_exp log_def rfloor_def [symmetric] rceil_def [symmetric]

lemma expands_to_powr_nat_0_0:
  assumes "eventually (\<lambda>x. f x = 0) at_top" "eventually (\<lambda>x. g x = 0) at_top"
          "basis_wf basis" "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. powr_nat (f x) (g x)) expands_to (const_expansion 1 :: 'a)) basis"
proof (rule expands_to_cong [OF expands_to_const])
  from assms(1,2) show "eventually (\<lambda>x. 1 = powr_nat (f x) (g x)) at_top"
    by eventually_elim (simp add: powr_nat_def)
qed fact+

lemma expands_to_powr_nat_0:
  assumes "eventually (\<lambda>x. f x = 0) at_top" "(g expands_to G) basis" "trimmed G"
          "basis_wf basis" "length basis = expansion_level TYPE('a :: multiseries)"
  shows   "((\<lambda>x. powr_nat (f x) (g x)) expands_to (zero_expansion :: 'a)) basis"
proof (rule expands_to_cong [OF expands_to_zero])
  from assms have "eventually (\<lambda>x. g x \<noteq> 0) at_top"
    using expands_to_imp_eventually_nz[of basis g G] by auto
  with assms(1) show "eventually (\<lambda>x. 0 = powr_nat (f x) (g x)) at_top"
    by eventually_elim (simp add: powr_nat_def)
qed (insert assms, auto elim!: eventually_mono simp: powr_nat_def)

lemma expands_to_powr_nat:
  assumes "trimmed_pos F" "basis_wf basis'" "(f expands_to F) basis'"
  assumes "((\<lambda>x. exp (ln (f x) * g x)) expands_to E) basis"
  shows   "((\<lambda>x. powr_nat (f x) (g x)) expands_to E) basis"
using assms(4)
proof (rule expands_to_cong)
  from eval_pos_if_dominant_term_pos[of basis' F] assms(1-4)
    show "eventually (\<lambda>x. exp (ln (f x) * g x) = powr_nat (f x) (g x)) at_top"
    by (auto simp: expands_to.simps trimmed_pos_def powr_def powr_nat_def elim: eventually_elim2)
qed


subsection \<open>Some technical lemmas\<close>

lemma landau_meta_eq_cong: "f \<in> L(g) \<Longrightarrow> f' \<equiv> f \<Longrightarrow> g' \<equiv> g \<Longrightarrow> f' \<in> L(g')"
  and asymp_equiv_meta_eq_cong: "f \<sim>[at_top] g \<Longrightarrow> f' \<equiv> f \<Longrightarrow> g' \<equiv> g \<Longrightarrow> f' \<sim>[at_top] g'"
  by simp_all
    
lemma filterlim_mono': "filterlim f F G \<Longrightarrow> F \<le> F' \<Longrightarrow> filterlim f F' G"
  by (erule (1) filterlim_mono) simp_all

lemma at_within_le_nhds: "at x within A \<le> nhds x"
  by (simp add: at_within_def)

lemma at_within_le_at: "at x within A \<le> at x"
  by (rule at_le) simp_all

lemma at_right_to_top': "at_right c = filtermap (\<lambda>x::real. c + inverse x) at_top"
  by (subst at_right_to_0, subst at_right_to_top) (simp add: filtermap_filtermap add_ac)

lemma at_left_to_top': "at_left c = filtermap (\<lambda>x::real. c - inverse x) at_top"
  by (subst at_left_minus, subst at_right_to_0, subst at_right_to_top) 
     (simp add: filtermap_filtermap add_ac)

lemma at_left_to_top: "at_left 0 = filtermap (\<lambda>x::real. - inverse x) at_top"
  by (simp add: at_left_to_top')

lemma filterlim_conv_filtermap:
  "G = filtermap g G' \<Longrightarrow>
     PROP (Trueprop (filterlim f F G)) \<equiv> PROP (Trueprop (filterlim (\<lambda>x. f (g x)) F G'))"
  by (simp add: filterlim_filtermap)

lemma eventually_conv_filtermap:
  "G = filtermap g G' \<Longrightarrow> 
     PROP (Trueprop (eventually P G)) \<equiv> PROP (Trueprop (eventually (\<lambda>x. P (g x)) G'))"
  by (simp add: eventually_filtermap)

lemma eventually_lt_imp_eventually_le:
  "eventually (\<lambda>x. f x < (g x :: real)) F \<Longrightarrow> eventually (\<lambda>x. f x \<le> g x) F"
  by (erule eventually_mono) simp
    
lemma smallo_imp_smallomega: "f \<in> o[F](g) \<Longrightarrow> g \<in> \<omega>[F](f)"
  by (simp add: smallomega_iff_smallo)

lemma bigo_imp_bigomega: "f \<in> O[F](g) \<Longrightarrow> g \<in> \<Omega>[F](f)"
  by (simp add: bigomega_iff_bigo)

context
  fixes L L' :: "real filter \<Rightarrow> (real \<Rightarrow> _) \<Rightarrow> _" and Lr :: "real filter \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> _"
  assumes LS: "landau_symbol L L' Lr"
begin
  
interpretation landau_symbol L L' Lr by (fact LS)

lemma landau_symbol_at_top_imp_at_bot:
  "(\<lambda>x. f (-x)) \<in> L' at_top (\<lambda>x. g (-x)) \<Longrightarrow> f \<in> L at_bot g"
  by (simp add: in_filtermap_iff at_bot_mirror)

lemma landau_symbol_at_top_imp_at_right_0:
  "(\<lambda>x. f (inverse x)) \<in> L' at_top (\<lambda>x. g (inverse x)) \<Longrightarrow> f \<in> L (at_right 0) g"
  by (simp add: in_filtermap_iff at_right_to_top')
    
lemma landau_symbol_at_top_imp_at_left_0:
  "(\<lambda>x. f ( -inverse x)) \<in> L' at_top (\<lambda>x. g (-inverse x)) \<Longrightarrow> f \<in> L (at_left 0) g"
  by (simp add: in_filtermap_iff at_left_to_top')    

lemma landau_symbol_at_top_imp_at_right:
  "(\<lambda>x. f (a + inverse x)) \<in> L' at_top (\<lambda>x. g (a + inverse x)) \<Longrightarrow> f \<in> L (at_right a) g"
  by (simp add: in_filtermap_iff at_right_to_top')
    
lemma landau_symbol_at_top_imp_at_left:
  "(\<lambda>x. f (a - inverse x)) \<in> L' at_top (\<lambda>x. g (a - inverse x)) \<Longrightarrow> f \<in> L (at_left a) g"
  by (simp add: in_filtermap_iff at_left_to_top')
    
lemma landau_symbol_at_top_imp_at:
  "(\<lambda>x. f (a - inverse x)) \<in> L' at_top (\<lambda>x. g (a - inverse x)) \<Longrightarrow>
   (\<lambda>x. f (a + inverse x)) \<in> L' at_top (\<lambda>x. g (a + inverse x)) \<Longrightarrow>
   f \<in> L (at a) g"
  by (simp add: sup at_eq_sup_left_right 
        landau_symbol_at_top_imp_at_left landau_symbol_at_top_imp_at_right)
      
lemma landau_symbol_at_top_imp_at_0:
  "(\<lambda>x. f (-inverse x)) \<in> L' at_top (\<lambda>x. g (-inverse x)) \<Longrightarrow>
   (\<lambda>x. f (inverse x)) \<in> L' at_top (\<lambda>x. g (inverse x)) \<Longrightarrow>
   f \<in> L (at 0) g"
  by (rule landau_symbol_at_top_imp_at) simp_all

end


context
  fixes f g :: "real \<Rightarrow> real"
begin

lemma asymp_equiv_at_top_imp_at_bot:
  "(\<lambda>x. f (- x)) \<sim>[at_top] (\<lambda>x. g (-x)) \<Longrightarrow> f \<sim>[at_bot] g"
  by (simp add: asymp_equiv_def filterlim_at_bot_mirror)

lemma asymp_equiv_at_top_imp_at_right_0:
  "(\<lambda>x. f (inverse x)) \<sim>[at_top] (\<lambda>x. g (inverse x)) \<Longrightarrow> f \<sim>[at_right 0] g"
  by (simp add: at_right_to_top asymp_equiv_filtermap_iff)

lemma asymp_equiv_at_top_imp_at_left_0:
  "(\<lambda>x. f (-inverse x)) \<sim>[at_top] (\<lambda>x. g (-inverse x)) \<Longrightarrow> f \<sim>[at_left 0] g"
  by (simp add: at_left_to_top asymp_equiv_filtermap_iff)

lemma asymp_equiv_at_top_imp_at_right:
  "(\<lambda>x. f (a + inverse x)) \<sim>[at_top] (\<lambda>x. g (a + inverse x)) \<Longrightarrow> f \<sim>[at_right a] g"
  by (simp add: at_right_to_top' asymp_equiv_filtermap_iff)

lemma asymp_equiv_at_top_imp_at_left:
  "(\<lambda>x. f (a - inverse x)) \<sim>[at_top] (\<lambda>x. g (a - inverse x)) \<Longrightarrow> f \<sim>[at_left a] g"
  by (simp add: at_left_to_top' asymp_equiv_filtermap_iff)

lemma asymp_equiv_at_top_imp_at:
  "(\<lambda>x. f (a - inverse x)) \<sim>[at_top] (\<lambda>x. g (a - inverse x)) \<Longrightarrow>
   (\<lambda>x. f (a + inverse x)) \<sim>[at_top] (\<lambda>x. g (a + inverse x)) \<Longrightarrow> f \<sim>[at a] g"
  unfolding asymp_equiv_def
  using asymp_equiv_at_top_imp_at_left[of a] asymp_equiv_at_top_imp_at_right[of a]
  by (intro filterlim_split_at) (auto simp: asymp_equiv_def)

lemma asymp_equiv_at_top_imp_at_0:
  "(\<lambda>x. f (-inverse x)) \<sim>[at_top] (\<lambda>x. g (-inverse x)) \<Longrightarrow>
   (\<lambda>x. f (inverse x)) \<sim>[at_top] (\<lambda>x. g (inverse x)) \<Longrightarrow> f \<sim>[at 0] g"
  by (rule asymp_equiv_at_top_imp_at) auto

end


lemmas eval_simps =
  eval_const eval_plus eval_minus eval_uminus eval_times eval_inverse eval_divide
  eval_map_ms eval_lift_ms eval_real_def eval_ms.simps

lemma real_eqI: "a - b = 0 \<Longrightarrow> a = (b::real)"
  by simp

lemma lift_ms_simps:
  "lift_ms (MS xs f) = MS (MSLCons (MS xs f, 0) MSLNil) f"
  "lift_ms (c :: real) = MS (MSLCons (c, 0) MSLNil) (\<lambda>_. c)"
  by (simp_all add: lift_ms_def)

lemmas landau_reduce_to_top = 
  landau_symbols [THEN landau_symbol_at_top_imp_at_bot]
  landau_symbols [THEN landau_symbol_at_top_imp_at_left_0]
  landau_symbols [THEN landau_symbol_at_top_imp_at_right_0]
  landau_symbols [THEN landau_symbol_at_top_imp_at_left]
  landau_symbols [THEN landau_symbol_at_top_imp_at_right]
  asymp_equiv_at_top_imp_at_bot
  asymp_equiv_at_top_imp_at_left_0
  asymp_equiv_at_top_imp_at_right_0
  asymp_equiv_at_top_imp_at_left
  asymp_equiv_at_top_imp_at_right

lemmas landau_at_top_imp_at = 
  landau_symbols [THEN landau_symbol_at_top_imp_at_0]
  landau_symbols [THEN landau_symbol_at_top_imp_at]
  asymp_equiv_at_top_imp_at_0
  asymp_equiv_at_top_imp_at


lemma nhds_leI: "x = y \<Longrightarrow> nhds x \<le> nhds y"
  by simp
    
lemma of_nat_diff_real: "of_nat (a - b) = max (0::real) (of_nat a - of_nat b)"
  and of_nat_max_real: "of_nat (max a b) = max (of_nat a) (of_nat b :: real)"
  and of_nat_min_real: "of_nat (min a b) = min (of_nat a) (of_nat b :: real)"
  and of_int_max_real: "of_int (max c d) = max (of_int c) (of_int d :: real)"
  and of_int_min_real: "of_int (min c d) = min (of_int c) (of_int d :: real)"
  by simp_all

named_theorems real_asymp_nat_reify

lemmas [real_asymp_nat_reify] = 
  of_nat_add of_nat_mult of_nat_diff_real of_nat_max_real of_nat_min_real of_nat_power 
  of_nat_Suc of_nat_numeral

lemma of_nat_div_real [real_asymp_nat_reify]:
  "of_nat (a div b) = max 0 (rfloor (of_nat a / of_nat b))"
  by (simp add: rfloor_def floor_divide_of_nat_eq)

lemma of_nat_mod_real [real_asymp_nat_reify]: "of_nat (a mod b) = rnatmod (of_nat a) (of_nat b)"
  by (simp add: rnatmod_def)

lemma real_nat [real_asymp_nat_reify]: "real (nat a) = max 0 (of_int a)"
  by simp


named_theorems real_asymp_int_reify

lemmas [real_asymp_int_reify] = 
  of_int_add of_int_mult of_int_diff of_int_minus of_int_max_real of_int_min_real
  of_int_power of_int_of_nat_eq of_int_numeral

lemma of_int_div_real [real_asymp_int_reify]:
  "of_int (a div b) = rfloor (of_int a / of_int b)"
  by (simp add: rfloor_def floor_divide_of_int_eq)

named_theorems real_asymp_preproc

lemmas [real_asymp_preproc] =
  of_nat_add of_nat_mult of_nat_diff_real of_nat_max_real of_nat_min_real of_nat_power 
  of_nat_Suc of_nat_numeral
  of_int_add of_int_mult of_int_diff of_int_minus of_int_max_real of_int_min_real
  of_int_power of_int_of_nat_eq of_int_numeral real_nat

lemma of_int_mod_real [real_asymp_int_reify]: "of_int (a mod b) = rintmod (of_int a) (of_int b)"
  by (simp add: rintmod_def)


lemma filterlim_of_nat_at_top:
  "filterlim f F at_top \<Longrightarrow> filterlim (\<lambda>x. f (of_nat x :: real)) F at_top"
  by (erule filterlim_compose[OF _filterlim_real_sequentially])

lemma asymp_equiv_real_nat_transfer:
  "f \<sim>[at_top] g \<Longrightarrow> (\<lambda>x. f (of_nat x :: real)) \<sim>[at_top] (\<lambda>x. g (of_nat x))"
  unfolding asymp_equiv_def by (rule filterlim_of_nat_at_top)

lemma eventually_nat_real:
  assumes "eventually P (at_top :: real filter)"
  shows   "eventually (\<lambda>x. P (real x)) (at_top :: nat filter)"
  using assms filterlim_real_sequentially
  unfolding filterlim_def le_filter_def eventually_filtermap by auto

lemmas real_asymp_nat_intros =
  filterlim_of_nat_at_top eventually_nat_real smallo_real_nat_transfer bigo_real_nat_transfer
  smallomega_real_nat_transfer bigomega_real_nat_transfer bigtheta_real_nat_transfer
  asymp_equiv_real_nat_transfer


lemma filterlim_of_int_at_top:
  "filterlim f F at_top \<Longrightarrow> filterlim (\<lambda>x. f (of_int x :: real)) F at_top"
  by (erule filterlim_compose[OF _ filterlim_real_of_int_at_top])

(* TODO Move *)
lemma filterlim_real_of_int_at_bot [tendsto_intros]:
  "filterlim real_of_int at_bot at_bot"
  unfolding filterlim_at_bot
proof
  fix C :: real
  show "eventually (\<lambda>n. real_of_int n \<le> C) at_bot"
    using eventually_le_at_bot[of "\<lfloor>C\<rfloor>"] by eventually_elim linarith
qed

lemma filterlim_of_int_at_bot:
  "filterlim f F at_bot \<Longrightarrow> filterlim (\<lambda>x. f (of_int x :: real)) F at_bot"
  by (erule filterlim_compose[OF _ filterlim_real_of_int_at_bot])

lemma asymp_equiv_real_int_transfer_at_top:
  "f \<sim>[at_top] g \<Longrightarrow> (\<lambda>x. f (of_int x :: real)) \<sim>[at_top] (\<lambda>x. g (of_int x))"
  unfolding asymp_equiv_def by (rule filterlim_of_int_at_top)

lemma asymp_equiv_real_int_transfer_at_bot:
  "f \<sim>[at_bot] g \<Longrightarrow> (\<lambda>x. f (of_int x :: real)) \<sim>[at_bot] (\<lambda>x. g (of_int x))"
  unfolding asymp_equiv_def by (rule filterlim_of_int_at_bot)

lemma eventually_int_real_at_top:
  assumes "eventually P (at_top :: real filter)"
  shows   "eventually (\<lambda>x. P (of_int x)) (at_top :: int filter)"
  using assms filterlim_of_int_at_top filterlim_iff filterlim_real_of_int_at_top by blast

lemma eventually_int_real_at_bot:
  assumes "eventually P (at_bot :: real filter)"
  shows   "eventually (\<lambda>x. P (of_int x)) (at_bot :: int filter)"
  using assms filterlim_of_int_at_bot filterlim_iff filterlim_real_of_int_at_bot by blast


lemmas real_asymp_int_intros =
  filterlim_of_int_at_bot filterlim_of_int_at_top
  landau_symbols[THEN landau_symbol.compose[OF _ _ filterlim_real_of_int_at_top]]
  landau_symbols[THEN landau_symbol.compose[OF _ _ filterlim_real_of_int_at_bot]]
  asymp_equiv_real_int_transfer_at_top asymp_equiv_real_int_transfer_at_bot

(* TODO: Move? *)
lemma tendsto_discrete_iff:
  "filterlim f (nhds (c :: 'a :: discrete_topology)) F \<longleftrightarrow> eventually (\<lambda>x. f x = c) F"
  by (auto simp: nhds_discrete filterlim_principal)

lemma tendsto_of_nat_iff:
  "filterlim (\<lambda>n. of_nat (f n)) (nhds (of_nat c :: 'a :: real_normed_div_algebra)) F \<longleftrightarrow>
     eventually (\<lambda>n. f n = c) F"
proof
  assume "((\<lambda>n. of_nat (f n)) \<longlongrightarrow> (of_nat c :: 'a)) F"
  hence "eventually (\<lambda>n. \<bar>real (f n) - real c\<bar> < 1/2) F"
    by (force simp: tendsto_iff dist_of_nat dest: spec[of _ "1/2"])
  thus "eventually (\<lambda>n. f n = c) F"
    by eventually_elim (simp add: abs_if split: if_splits)
next
  assume "eventually (\<lambda>n. f n = c) F"
  hence "eventually (\<lambda>n. of_nat (f n) = (of_nat c :: 'a)) F"
    by eventually_elim simp
  thus "filterlim (\<lambda>n. of_nat (f n)) (nhds (of_nat c :: 'a)) F"
    by (rule tendsto_eventually)
qed

lemma tendsto_of_int_iff:
  "filterlim (\<lambda>n. of_int (f n)) (nhds (of_int c :: 'a :: real_normed_div_algebra)) F \<longleftrightarrow>
     eventually (\<lambda>n. f n = c) F"
proof
  assume "((\<lambda>n. of_int (f n)) \<longlongrightarrow> (of_int c :: 'a)) F"
  hence "eventually (\<lambda>n. \<bar>real_of_int (f n) - of_int c\<bar> < 1/2) F"
    by (force simp: tendsto_iff dist_of_int dest: spec[of _ "1/2"])
  thus "eventually (\<lambda>n. f n = c) F"
    by eventually_elim (simp add: abs_if split: if_splits)
next
  assume "eventually (\<lambda>n. f n = c) F"
  hence "eventually (\<lambda>n. of_int (f n) = (of_int c :: 'a)) F"
    by eventually_elim simp
  thus "filterlim (\<lambda>n. of_int (f n)) (nhds (of_int c :: 'a)) F"
    by (rule tendsto_eventually)
qed

lemma filterlim_at_top_int_iff_filterlim_real:
  "filterlim f at_top F \<longleftrightarrow> filterlim (\<lambda>x. real_of_int (f x)) at_top F" (is "?lhs = ?rhs")
proof
  assume ?rhs
  hence "filterlim (\<lambda>x. floor (real_of_int (f x))) at_top F"
    by (intro filterlim_compose[OF filterlim_floor_sequentially])
  also have "?this \<longleftrightarrow> ?lhs" by (intro filterlim_cong refl) auto
  finally show ?lhs .
qed (auto intro: filterlim_compose[OF filterlim_real_of_int_at_top])

lemma filterlim_floor_at_bot: "filterlim (floor :: real \<Rightarrow> int) at_bot at_bot"
proof (subst filterlim_at_bot, rule allI)
  fix C :: int show "eventually (\<lambda>x::real. \<lfloor>x\<rfloor> \<le> C) at_bot"
    using eventually_le_at_bot[of "real_of_int C"] by eventually_elim linarith
qed

lemma filterlim_at_bot_int_iff_filterlim_real:
  "filterlim f at_bot F \<longleftrightarrow> filterlim (\<lambda>x. real_of_int (f x)) at_bot F" (is "?lhs = ?rhs")
proof
  assume ?rhs
  hence "filterlim (\<lambda>x. floor (real_of_int (f x))) at_bot F"
    by (intro filterlim_compose[OF filterlim_floor_at_bot])
  also have "?this \<longleftrightarrow> ?lhs" by (intro filterlim_cong refl) auto
  finally show ?lhs .
qed (auto intro: filterlim_compose[OF filterlim_real_of_int_at_bot])
(* END TODO *)


lemma real_asymp_real_nat_transfer:
  "filterlim (\<lambda>n. real (f n)) at_top F \<Longrightarrow> filterlim f at_top F"
  "filterlim (\<lambda>n. real (f n)) (nhds (real c)) F \<Longrightarrow> eventually (\<lambda>n. f n = c) F"
  "eventually (\<lambda>n. real (f n) \<le> real (g n)) F \<Longrightarrow> eventually (\<lambda>n. f n \<le> g n) F"
  "eventually (\<lambda>n. real (f n) < real (g n)) F \<Longrightarrow> eventually (\<lambda>n. f n < g n) F"
  by (simp_all add: filterlim_sequentially_iff_filterlim_real tendsto_of_nat_iff)

lemma real_asymp_real_int_transfer:
  "filterlim (\<lambda>n. real_of_int (f n)) at_top F \<Longrightarrow> filterlim f at_top F"
  "filterlim (\<lambda>n. real_of_int (f n)) at_bot F \<Longrightarrow> filterlim f at_bot F"
  "filterlim (\<lambda>n. real_of_int (f n)) (nhds (of_int c)) F \<Longrightarrow> eventually (\<lambda>n. f n = c) F"
  "eventually (\<lambda>n. real_of_int (f n) \<le> real_of_int (g n)) F \<Longrightarrow> eventually (\<lambda>n. f n \<le> g n) F"
  "eventually (\<lambda>n. real_of_int (f n) < real_of_int (g n)) F \<Longrightarrow> eventually (\<lambda>n. f n < g n) F"
  by (simp_all add: tendsto_of_int_iff filterlim_at_top_int_iff_filterlim_real
                    filterlim_at_bot_int_iff_filterlim_real)
  

lemma eventually_at_left_at_right_imp_at:
  "eventually P (at_left a) \<Longrightarrow> eventually P (at_right a) \<Longrightarrow> eventually P (at (a::real))"
  by (simp add: eventually_at_split)

lemma filtermap_at_left_shift: "filtermap (\<lambda>x. x - d) (at_left a) = at_left (a - d)"
  for a d :: "real"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])
    
lemma at_left_to_0: "at_left a = filtermap (\<lambda>x. x + a) (at_left 0)"
  for a :: real using filtermap_at_left_shift[of "-a" 0] by simp
    
lemma filterlim_at_leftI: 
  assumes "filterlim (\<lambda>x. f x - c) (at_left 0) F"
  shows   "filterlim f (at_left (c::real)) F"
proof -
  from assms have "filtermap (\<lambda>x. f x - c) F \<le> at_left 0" by (simp add: filterlim_def)
  hence "filtermap (\<lambda>x. x + c) (filtermap (\<lambda>x. f x - c) F) \<le> filtermap (\<lambda>x. x + c) (at_left 0)"
    by (rule filtermap_mono)
  thus ?thesis by (subst at_left_to_0) (simp_all add: filterlim_def filtermap_filtermap)
qed

lemma filterlim_at_rightI: 
  assumes "filterlim (\<lambda>x. f x - c) (at_right 0) F"
  shows   "filterlim f (at_right (c::real)) F"
proof -
  from assms have "filtermap (\<lambda>x. f x - c) F \<le> at_right 0" by (simp add: filterlim_def)
  hence "filtermap (\<lambda>x. x + c) (filtermap (\<lambda>x. f x - c) F) \<le> filtermap (\<lambda>x. x + c) (at_right 0)"
    by (rule filtermap_mono)
  thus ?thesis by (subst at_right_to_0) (simp_all add: filterlim_def filtermap_filtermap)
qed

lemma filterlim_atI':
  assumes "filterlim (\<lambda>x. f x - c) (at 0) F"
  shows   "filterlim f (at (c::real)) F"
proof -
  from assms have "filtermap (\<lambda>x. f x - c) F \<le> at 0" by (simp add: filterlim_def)
  hence "filtermap (\<lambda>x. x + c) (filtermap (\<lambda>x. f x - c) F) \<le> filtermap (\<lambda>x. x + c) (at 0)"
    by (rule filtermap_mono)
  thus ?thesis by (subst at_to_0) (simp_all add: filterlim_def filtermap_filtermap)
qed

lemma gbinomial_series_aux_altdef:
  "gbinomial_series_aux False x n acc =
     MSLCons acc (gbinomial_series_aux False x (n + 1) ((x - n) / (n + 1) * acc))"
  "gbinomial_series_aux True x n acc =
     (if acc = 0 then MSLNil else 
        MSLCons acc (gbinomial_series_aux True x (n + 1) ((x - n) / (n + 1) * acc)))"
  by (subst gbinomial_series_aux.code, simp)+



subsection \<open>Proof method setup\<close>

text \<open>
  The following theorem collection is the list of rewrite equations to be used by the
  lazy evaluation package. If something is missing here, normalisation of terms into
  head normal form will fail.
\<close>

named_theorems real_asymp_eval_eqs

lemmas [real_asymp_eval_eqs] =
  msllist.sel fst_conv snd_conv CMP_BRANCH.simps plus_ms.simps minus_ms_altdef 
  minus_ms_aux_MSLNil_left minus_ms_aux_MSLNil_right minus_ms_aux_MSLCons_eval times_ms.simps
  uminus_ms.simps divide_ms.simps inverse_ms.simps inverse_ms_aux_MSLCons const_expansion_ms_eval
  const_expansion_real_def times_ms_aux_MSLNil times_ms_aux_MSLCons_eval scale_shift_ms_aux_MSLCons_eval 
  scale_shift_ms_aux_MSLNil uminus_ms_aux_MSLCons_eval uminus_ms_aux_MSLNil 
  scale_ms_aux_MSLNil scale_ms_aux_MSLCons scale_ms_def shift_ms_aux_MSLNil shift_ms_aux_MSLCons
  scale_ms_aux'_MSLNil scale_ms_aux'_MSLCons exp_series_stream_def exp_series_stream_aux.code
  plus_ms_aux_MSLNil plus_ms_aux_MSLCons_eval map_ms_altdef map_ms_aux_MSLCons
  map_ms_aux_MSLNil lift_ms_simps powser_ms_aux_MSLNil powser_ms_aux_MSLCons
  ln_series_stream_aux_code gbinomial_series_def gbinomial_series_aux_altdef
  mssalternate.code powr_expansion_ms.simps powr_expansion_real_def powr_ms_aux_MSLCons
  power_expansion_ms.simps power_expansion_real_def power_ms_aux_MSLCons
  powser_ms_aux'_MSSCons sin_ms_aux'_altdef cos_ms_aux'_altdef const_ms_aux_def
  compare_expansions_MSLCons_eval compare_expansions_real zero_expansion_ms_def
  zero_expansion_real_def sin_series_stream_def cos_series_stream_def arctan_series_stream_def
  arctan_ms_aux_def sin_series_stream_aux_code arctan_series_stream_aux_code if_True if_False
                                               
text \<open>
  The following constant and theorem collection exist in order to register constructors for
  lazy evaluation. All constants marked in such a way will be passed to the lazy evaluation
  package as free constructors upon which pattern-matching can be done.
\<close>
definition REAL_ASYMP_EVAL_CONSTRUCTOR :: "'a \<Rightarrow> bool"
  where [simp]: "REAL_ASYMP_EVAL_CONSTRUCTOR x = True"

named_theorems exp_log_eval_constructor

lemma exp_log_eval_constructors [exp_log_eval_constructor]:
  "REAL_ASYMP_EVAL_CONSTRUCTOR MSLNil"
  "REAL_ASYMP_EVAL_CONSTRUCTOR MSLCons"
  "REAL_ASYMP_EVAL_CONSTRUCTOR MSSCons"
  "REAL_ASYMP_EVAL_CONSTRUCTOR LT"
  "REAL_ASYMP_EVAL_CONSTRUCTOR EQ"
  "REAL_ASYMP_EVAL_CONSTRUCTOR GT"
  "REAL_ASYMP_EVAL_CONSTRUCTOR Pair"
  "REAL_ASYMP_EVAL_CONSTRUCTOR True"
  "REAL_ASYMP_EVAL_CONSTRUCTOR False"
  "REAL_ASYMP_EVAL_CONSTRUCTOR MS"
  by simp_all

text \<open>
  The following constant exists in order to mark functions as having plug-in support
  for multiseries expansions (i.\,e.\ this can be used to add support for arbitrary functions
  later on)
\<close>
definition REAL_ASYMP_CUSTOM :: "'a \<Rightarrow> bool"
  where [simp]: "REAL_ASYMP_CUSTOM x = True"

lemmas [simp del] = ms.map inverse_ms_aux.simps divide_ms.simps

definition expansion_with_remainder_term :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) set \<Rightarrow> bool" where
  "expansion_with_remainder_term _ _ = True"

notation (output) expansion_with_remainder_term (infixl \<open>+\<close> 10)

ML_file \<open>asymptotic_basis.ML\<close>
ML_file \<open>exp_log_expression.ML\<close>
ML_file \<open>expansion_interface.ML\<close>
ML_file \<open>multiseries_expansion.ML\<close>
ML_file \<open>real_asymp.ML\<close>

method_setup real_asymp = 
  \<open>(Scan.lift (Scan.optional (Args.parens (Args.$$$ "verbose") >> K true) false) --|
    Method.sections Simplifier.simp_modifiers) >> 
     (fn verbose => fn ctxt => SIMPLE_METHOD' (Real_Asymp_Basic.tac verbose ctxt))\<close>
  "Semi-automatic decision procedure for asymptotics of exp-log functions"

end

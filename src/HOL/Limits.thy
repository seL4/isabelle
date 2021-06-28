(*  Title:      HOL/Limits.thy
    Author:     Brian Huffman
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
*)

section \<open>Limits on Real Vector Spaces\<close>

theory Limits
  imports Real_Vector_Spaces
begin

text \<open>Lemmas related to shifting/scaling\<close>
lemma range_add [simp]:
  fixes a::"'a::group_add" shows "range ((+) a) = UNIV"
  by (metis add_minus_cancel surjI)

lemma range_diff [simp]:
  fixes a::"'a::group_add" shows "range ((-) a) = UNIV"
  by (metis (full_types) add_minus_cancel diff_minus_eq_add surj_def)

lemma range_mult [simp]:
  fixes a::"real" shows "range ((*) a) = (if a=0 then {0} else UNIV)"
  by (simp add: surj_def) (meson dvdE dvd_field_iff)


subsection \<open>Filter going to infinity norm\<close>

definition at_infinity :: "'a::real_normed_vector filter"
  where "at_infinity = (INF r. principal {x. r \<le> norm x})"

lemma eventually_at_infinity: "eventually P at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> P x)"
  unfolding at_infinity_def
  by (subst eventually_INF_base)
     (auto simp: subset_eq eventually_principal intro!: exI[of _ "max a b" for a b])

corollary eventually_at_infinity_pos:
  "eventually p at_infinity \<longleftrightarrow> (\<exists>b. 0 < b \<and> (\<forall>x. norm x \<ge> b \<longrightarrow> p x))"
  unfolding eventually_at_infinity
  by (meson le_less_trans norm_ge_zero not_le zero_less_one)

lemma at_infinity_eq_at_top_bot: "(at_infinity :: real filter) = sup at_top at_bot"
proof -
  have 1: "\<lbrakk>\<forall>n\<ge>u. A n; \<forall>n\<le>v. A n\<rbrakk>
       \<Longrightarrow> \<exists>b. \<forall>x. b \<le> \<bar>x\<bar> \<longrightarrow> A x" for A and u v::real
    by (rule_tac x="max (- v) u" in exI) (auto simp: abs_real_def)
  have 2: "\<forall>x. u \<le> \<bar>x\<bar> \<longrightarrow> A x \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. A n" for A and u::real
    by (meson abs_less_iff le_cases less_le_not_le)
  have 3: "\<forall>x. u \<le> \<bar>x\<bar> \<longrightarrow> A x \<Longrightarrow> \<exists>N. \<forall>n\<le>N. A n" for A and u::real
    by (metis (full_types) abs_ge_self abs_minus_cancel le_minus_iff order_trans)
  show ?thesis
    by (auto simp: filter_eq_iff eventually_sup eventually_at_infinity
      eventually_at_top_linorder eventually_at_bot_linorder intro: 1 2 3)
qed

lemma at_top_le_at_infinity: "at_top \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

lemma at_bot_le_at_infinity: "at_bot \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

lemma filterlim_at_top_imp_at_infinity: "filterlim f at_top F \<Longrightarrow> filterlim f at_infinity F"
  for f :: "_ \<Rightarrow> real"
  by (rule filterlim_mono[OF _ at_top_le_at_infinity order_refl])

lemma filterlim_real_at_infinity_sequentially: "filterlim real at_infinity sequentially"
  by (simp add: filterlim_at_top_imp_at_infinity filterlim_real_sequentially)

lemma lim_infinity_imp_sequentially: "(f \<longlongrightarrow> l) at_infinity \<Longrightarrow> ((\<lambda>n. f(n)) \<longlongrightarrow> l) sequentially"
  by (simp add: filterlim_at_top_imp_at_infinity filterlim_compose filterlim_real_sequentially)


subsubsection \<open>Boundedness\<close>

definition Bfun :: "('a \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where Bfun_metric_def: "Bfun f F = (\<exists>y. \<exists>K>0. eventually (\<lambda>x. dist (f x) y \<le> K) F)"

abbreviation Bseq :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool"
  where "Bseq X \<equiv> Bfun X sequentially"

lemma Bseq_conv_Bfun: "Bseq X \<longleftrightarrow> Bfun X sequentially" ..

lemma Bseq_ignore_initial_segment: "Bseq X \<Longrightarrow> Bseq (\<lambda>n. X (n + k))"
  unfolding Bfun_metric_def by (subst eventually_sequentially_seg)

lemma Bseq_offset: "Bseq (\<lambda>n. X (n + k)) \<Longrightarrow> Bseq X"
  unfolding Bfun_metric_def by (subst (asm) eventually_sequentially_seg)

lemma Bfun_def: "Bfun f F \<longleftrightarrow> (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) F)"
  unfolding Bfun_metric_def norm_conv_dist
proof safe
  fix y K
  assume K: "0 < K" and *: "eventually (\<lambda>x. dist (f x) y \<le> K) F"
  moreover have "eventually (\<lambda>x. dist (f x) 0 \<le> dist (f x) y + dist 0 y) F"
    by (intro always_eventually) (metis dist_commute dist_triangle)
  with * have "eventually (\<lambda>x. dist (f x) 0 \<le> K + dist 0 y) F"
    by eventually_elim auto
  with \<open>0 < K\<close> show "\<exists>K>0. eventually (\<lambda>x. dist (f x) 0 \<le> K) F"
    by (intro exI[of _ "K + dist 0 y"] add_pos_nonneg conjI zero_le_dist) auto
qed (force simp del: norm_conv_dist [symmetric])

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) F"
  shows "Bfun f F"
  unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) F"
    using K by (rule eventually_mono) simp
qed

lemma BfunE:
  assumes "Bfun f F"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) F"
  using assms unfolding Bfun_def by blast

lemma Cauchy_Bseq:
  assumes "Cauchy X" shows "Bseq X"
proof -
  have "\<exists>y K. 0 < K \<and> (\<exists>N. \<forall>n\<ge>N. dist (X n) y \<le> K)"
    if "\<And>m n. \<lbrakk>m \<ge> M; n \<ge> M\<rbrakk> \<Longrightarrow> dist (X m) (X n) < 1" for M
    by (meson order.order_iff_strict that zero_less_one)
  with assms show ?thesis
    by (force simp: Cauchy_def Bfun_metric_def eventually_sequentially)
qed

subsubsection \<open>Bounded Sequences\<close>

lemma BseqI': "(\<And>n. norm (X n) \<le> K) \<Longrightarrow> Bseq X"
  by (intro BfunI) (auto simp: eventually_sequentially)

lemma Bseq_def: "Bseq X \<longleftrightarrow> (\<exists>K>0. \<forall>n. norm (X n) \<le> K)"
  unfolding Bfun_def eventually_sequentially
proof safe
  fix N K
  assume "0 < K" "\<forall>n\<ge>N. norm (X n) \<le> K"
  then show "\<exists>K>0. \<forall>n. norm (X n) \<le> K"
    by (intro exI[of _ "max (Max (norm ` X ` {..N})) K"] max.strict_coboundedI2)
       (auto intro!: imageI not_less[where 'a=nat, THEN iffD1] Max_ge simp: le_max_iff_disj)
qed auto

lemma BseqE: "Bseq X \<Longrightarrow> (\<And>K. 0 < K \<Longrightarrow> \<forall>n. norm (X n) \<le> K \<Longrightarrow> Q) \<Longrightarrow> Q"
  unfolding Bseq_def by auto

lemma BseqD: "Bseq X \<Longrightarrow> \<exists>K. 0 < K \<and> (\<forall>n. norm (X n) \<le> K)"
  by (simp add: Bseq_def)

lemma BseqI: "0 < K \<Longrightarrow> \<forall>n. norm (X n) \<le> K \<Longrightarrow> Bseq X"
  by (auto simp: Bseq_def)

lemma Bseq_bdd_above: "Bseq X \<Longrightarrow> bdd_above (range X)"
  for X :: "nat \<Rightarrow> real"
proof (elim BseqE, intro bdd_aboveI2)
  fix K n
  assume "0 < K" "\<forall>n. norm (X n) \<le> K"
  then show "X n \<le> K"
    by (auto elim!: allE[of _ n])
qed

lemma Bseq_bdd_above': "Bseq X \<Longrightarrow> bdd_above (range (\<lambda>n. norm (X n)))"
  for X :: "nat \<Rightarrow> 'a :: real_normed_vector"
proof (elim BseqE, intro bdd_aboveI2)
  fix K n
  assume "0 < K" "\<forall>n. norm (X n) \<le> K"
  then show "norm (X n) \<le> K"
    by (auto elim!: allE[of _ n])
qed

lemma Bseq_bdd_below: "Bseq X \<Longrightarrow> bdd_below (range X)"
  for X :: "nat \<Rightarrow> real"
proof (elim BseqE, intro bdd_belowI2)
  fix K n
  assume "0 < K" "\<forall>n. norm (X n) \<le> K"
  then show "- K \<le> X n"
    by (auto elim!: allE[of _ n])
qed

lemma Bseq_eventually_mono:
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) sequentially" "Bseq g"
  shows "Bseq f"
proof -
  from assms(2) obtain K where "0 < K" and "eventually (\<lambda>n. norm (g n) \<le> K) sequentially"
    unfolding Bfun_def by fast
  with assms(1) have "eventually (\<lambda>n. norm (f n) \<le> K) sequentially"
    by (fast elim: eventually_elim2 order_trans)
  with \<open>0 < K\<close> show "Bseq f"
    unfolding Bfun_def by fast
qed

lemma lemma_NBseq_def: "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) \<longleftrightarrow> (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
proof safe
  fix K :: real
  from reals_Archimedean2 obtain n :: nat where "K < real n" ..
  then have "K \<le> real (Suc n)" by auto
  moreover assume "\<forall>m. norm (X m) \<le> K"
  ultimately have "\<forall>m. norm (X m) \<le> real (Suc n)"
    by (blast intro: order_trans)
  then show "\<exists>N. \<forall>n. norm (X n) \<le> real (Suc N)" ..
next
  show "\<And>N. \<forall>n. norm (X n) \<le> real (Suc N) \<Longrightarrow> \<exists>K>0. \<forall>n. norm (X n) \<le> K"
    using of_nat_0_less_iff by blast
qed

text \<open>Alternative definition for \<open>Bseq\<close>.\<close>
lemma Bseq_iff: "Bseq X \<longleftrightarrow> (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
  by (simp add: Bseq_def) (simp add: lemma_NBseq_def)

lemma lemma_NBseq_def2: "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) = (\<exists>N. \<forall>n. norm (X n) < real(Suc N))"
proof -
  have *: "\<And>N. \<forall>n. norm (X n) \<le> 1 + real N \<Longrightarrow>
         \<exists>N. \<forall>n. norm (X n) < 1 + real N"
    by (metis add.commute le_less_trans less_add_one of_nat_Suc)
  then show ?thesis
    unfolding lemma_NBseq_def
    by (metis less_le_not_le not_less_iff_gr_or_eq of_nat_Suc)
qed

text \<open>Yet another definition for Bseq.\<close>
lemma Bseq_iff1a: "Bseq X \<longleftrightarrow> (\<exists>N. \<forall>n. norm (X n) < real (Suc N))"
  by (simp add: Bseq_def lemma_NBseq_def2)

subsubsection \<open>A Few More Equivalence Theorems for Boundedness\<close>

text \<open>Alternative formulation for boundedness.\<close>
lemma Bseq_iff2: "Bseq X \<longleftrightarrow> (\<exists>k > 0. \<exists>x. \<forall>n. norm (X n + - x) \<le> k)"
  by (metis BseqE BseqI' add.commute add_cancel_right_left add_uminus_conv_diff norm_add_leD
            norm_minus_cancel norm_minus_commute)

text \<open>Alternative formulation for boundedness.\<close>
lemma Bseq_iff3: "Bseq X \<longleftrightarrow> (\<exists>k>0. \<exists>N. \<forall>n. norm (X n + - X N) \<le> k)"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then obtain K where *: "0 < K" and **: "\<And>n. norm (X n) \<le> K"
    by (auto simp: Bseq_def)
  from * have "0 < K + norm (X 0)" by (rule order_less_le_trans) simp
  from ** have "\<forall>n. norm (X n - X 0) \<le> K + norm (X 0)"
    by (auto intro: order_trans norm_triangle_ineq4)
  then have "\<forall>n. norm (X n + - X 0) \<le> K + norm (X 0)"
    by simp
  with \<open>0 < K + norm (X 0)\<close> show ?Q by blast
next
  assume ?Q
  then show ?P by (auto simp: Bseq_iff2)
qed


subsubsection \<open>Upper Bounds and Lubs of Bounded Sequences\<close>

lemma Bseq_minus_iff: "Bseq (\<lambda>n. - (X n) :: 'a::real_normed_vector) \<longleftrightarrow> Bseq X"
  by (simp add: Bseq_def)

lemma Bseq_add:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "Bseq f"
  shows "Bseq (\<lambda>x. f x + c)"
proof -
  from assms obtain K where K: "\<And>x. norm (f x) \<le> K"
    unfolding Bseq_def by blast
  {
    fix x :: nat
    have "norm (f x + c) \<le> norm (f x) + norm c" by (rule norm_triangle_ineq)
    also have "norm (f x) \<le> K" by (rule K)
    finally have "norm (f x + c) \<le> K + norm c" by simp
  }
  then show ?thesis by (rule BseqI')
qed

lemma Bseq_add_iff: "Bseq (\<lambda>x. f x + c) \<longleftrightarrow> Bseq f"
  for f :: "nat \<Rightarrow> 'a::real_normed_vector"
  using Bseq_add[of f c] Bseq_add[of "\<lambda>x. f x + c" "-c"] by auto

lemma Bseq_mult:
  fixes f g :: "nat \<Rightarrow> 'a::real_normed_field"
  assumes "Bseq f" and "Bseq g"
  shows "Bseq (\<lambda>x. f x * g x)"
proof -
  from assms obtain K1 K2 where K: "norm (f x) \<le> K1" "K1 > 0" "norm (g x) \<le> K2" "K2 > 0"
    for x
    unfolding Bseq_def by blast
  then have "norm (f x * g x) \<le> K1 * K2" for x
    by (auto simp: norm_mult intro!: mult_mono)
  then show ?thesis by (rule BseqI')
qed

lemma Bfun_const [simp]: "Bfun (\<lambda>_. c) F"
  unfolding Bfun_metric_def by (auto intro!: exI[of _ c] exI[of _ "1::real"])

lemma Bseq_cmult_iff:
  fixes c :: "'a::real_normed_field"
  assumes "c \<noteq> 0"
  shows "Bseq (\<lambda>x. c * f x) \<longleftrightarrow> Bseq f"
proof
  assume "Bseq (\<lambda>x. c * f x)"
  with Bfun_const have "Bseq (\<lambda>x. inverse c * (c * f x))"
    by (rule Bseq_mult)
  with \<open>c \<noteq> 0\<close> show "Bseq f"
    by (simp add: field_split_simps)
qed (intro Bseq_mult Bfun_const)

lemma Bseq_subseq: "Bseq f \<Longrightarrow> Bseq (\<lambda>x. f (g x))"
  for f :: "nat \<Rightarrow> 'a::real_normed_vector"
  unfolding Bseq_def by auto

lemma Bseq_Suc_iff: "Bseq (\<lambda>n. f (Suc n)) \<longleftrightarrow> Bseq f"
  for f :: "nat \<Rightarrow> 'a::real_normed_vector"
  using Bseq_offset[of f 1] by (auto intro: Bseq_subseq)

lemma increasing_Bseq_subseq_iff:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> norm (f x :: 'a::real_normed_vector) \<le> norm (f y)" "strict_mono g"
  shows "Bseq (\<lambda>x. f (g x)) \<longleftrightarrow> Bseq f"
proof
  assume "Bseq (\<lambda>x. f (g x))"
  then obtain K where K: "\<And>x. norm (f (g x)) \<le> K"
    unfolding Bseq_def by auto
  {
    fix x :: nat
    from filterlim_subseq[OF assms(2)] obtain y where "g y \<ge> x"
      by (auto simp: filterlim_at_top eventually_at_top_linorder)
    then have "norm (f x) \<le> norm (f (g y))"
      using assms(1) by blast
    also have "norm (f (g y)) \<le> K" by (rule K)
    finally have "norm (f x) \<le> K" .
  }
  then show "Bseq f" by (rule BseqI')
qed (use Bseq_subseq[of f g] in simp_all)

lemma nonneg_incseq_Bseq_subseq_iff:
  fixes f :: "nat \<Rightarrow> real"
    and g :: "nat \<Rightarrow> nat"
  assumes "\<And>x. f x \<ge> 0" "incseq f" "strict_mono g"
  shows "Bseq (\<lambda>x. f (g x)) \<longleftrightarrow> Bseq f"
  using assms by (intro increasing_Bseq_subseq_iff) (auto simp: incseq_def)

lemma Bseq_eq_bounded: "range f \<subseteq> {a..b} \<Longrightarrow> Bseq f"
  for a b :: real
proof (rule BseqI'[where K="max (norm a) (norm b)"])
  fix n assume "range f \<subseteq> {a..b}"
  then have "f n \<in> {a..b}"
    by blast
  then show "norm (f n) \<le> max (norm a) (norm b)"
    by auto
qed

lemma incseq_bounded: "incseq X \<Longrightarrow> \<forall>i. X i \<le> B \<Longrightarrow> Bseq X"
  for B :: real
  by (intro Bseq_eq_bounded[of X "X 0" B]) (auto simp: incseq_def)

lemma decseq_bounded: "decseq X \<Longrightarrow> \<forall>i. B \<le> X i \<Longrightarrow> Bseq X"
  for B :: real
  by (intro Bseq_eq_bounded[of X B "X 0"]) (auto simp: decseq_def)


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Polynomal function extremal theorem, from HOL Light\<close>

lemma polyfun_extremal_lemma: 
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
    shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
proof (induct n)
  case 0 with assms
  show ?case
    apply (rule_tac x="norm (c 0) / e" in exI)
    apply (auto simp: field_simps)
    done
next
  case (Suc n)
  obtain M where M: "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
    using Suc assms by blast
  show ?case
  proof (rule exI [where x= "max M (1 + norm(c(Suc n)) / e)"], clarsimp simp del: power_Suc)
    fix z::'a
    assume z1: "M \<le> norm z" and "1 + norm (c (Suc n)) / e \<le> norm z"
    then have z2: "e + norm (c (Suc n)) \<le> e * norm z"
      using assms by (simp add: field_simps)
    have "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
      using M [OF z1] by simp
    then have "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by simp
    then have "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by (blast intro: norm_triangle_le elim: )
    also have "... \<le> (e + norm (c (Suc n))) * norm z ^ Suc n"
      by (simp add: norm_power norm_mult algebra_simps)
    also have "... \<le> (e * norm z) * norm z ^ Suc n"
      by (metis z2 mult.commute mult_left_mono norm_ge_zero norm_power)
    finally show "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc (Suc n)"
      by simp
  qed
qed

lemma polyfun_extremal: (*COMPLEX_POLYFUN_EXTREMAL in HOL Light*)
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes k: "c k \<noteq> 0" "1\<le>k" and kn: "k\<le>n"
    shows "eventually (\<lambda>z. norm (\<Sum>i\<le>n. c(i) * z^i) \<ge> B) at_infinity"
using kn
proof (induction n)
  case 0
  then show ?case
    using k by simp
next
  case (Suc m)
  show ?case
  proof (cases "c (Suc m) = 0")
    case True
    then show ?thesis using Suc k
      by auto (metis antisym_conv less_eq_Suc_le not_le)
  next
    case False
    then obtain M where M:
          "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>m. c i * z^i) \<le> norm (c (Suc m)) / 2 * norm z ^ Suc m"
      using polyfun_extremal_lemma [of "norm(c (Suc m)) / 2" c m] Suc
      by auto
    have "\<exists>b. \<forall>z. b \<le> norm z \<longrightarrow> B \<le> norm (\<Sum>i\<le>Suc m. c i * z^i)"
    proof (rule exI [where x="max M (max 1 (\<bar>B\<bar> / (norm(c (Suc m)) / 2)))"], clarsimp simp del: power_Suc)
      fix z::'a
      assume z1: "M \<le> norm z" "1 \<le> norm z"
         and "\<bar>B\<bar> * 2 / norm (c (Suc m)) \<le> norm z"
      then have z2: "\<bar>B\<bar> \<le> norm (c (Suc m)) * norm z / 2"
        using False by (simp add: field_simps)
      have nz: "norm z \<le> norm z ^ Suc m"
        by (metis \<open>1 \<le> norm z\<close> One_nat_def less_eq_Suc_le power_increasing power_one_right zero_less_Suc)
      have *: "\<And>y x. norm (c (Suc m)) * norm z / 2 \<le> norm y - norm x \<Longrightarrow> B \<le> norm (x + y)"
        by (metis abs_le_iff add.commute norm_diff_ineq order_trans z2)
      have "norm z * norm (c (Suc m)) + 2 * norm (\<Sum>i\<le>m. c i * z^i)
            \<le> norm (c (Suc m)) * norm z + norm (c (Suc m)) * norm z ^ Suc m"
        using M [of z] Suc z1  by auto
      also have "... \<le> 2 * (norm (c (Suc m)) * norm z ^ Suc m)"
        using nz by (simp add: mult_mono del: power_Suc)
      finally show "B \<le> norm ((\<Sum>i\<le>m. c i * z^i) + c (Suc m) * z ^ Suc m)"
        using Suc.IH
        apply (auto simp: eventually_at_infinity)
        apply (rule *)
        apply (simp add: field_simps norm_mult norm_power)
        done
    qed
    then show ?thesis
      by (simp add: eventually_at_infinity)
  qed
qed

subsection \<open>Convergence to Zero\<close>

definition Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Zfun f F = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) F)"

lemma ZfunI: "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F) \<Longrightarrow> Zfun f F"
  by (simp add: Zfun_def)

lemma ZfunD: "Zfun f F \<Longrightarrow> 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F"
  by (simp add: Zfun_def)

lemma Zfun_ssubst: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> Zfun g F \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) F"
  unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) F = Zfun (\<lambda>x. f x) F"
  unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f F"
    and g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F"
  shows "Zfun (\<lambda>x. g x) F"
proof (cases "0 < K")
  case K: True
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    then have "0 < r / K" using K by simp
    then have "eventually (\<lambda>x. norm (f x) < r / K) F"
      using ZfunD [OF f] by blast
    with g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      then have "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      then show ?case
        by (simp add: order_le_less_trans [OF elim(1)])
    qed
  qed
next
  case False
  then have K: "K \<le> 0" by (simp only: not_less)
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    from g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      also have "norm (f x) * K \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show ?case
        using \<open>0 < r\<close> by simp
    qed
  qed
qed

lemma Zfun_le: "Zfun g F \<Longrightarrow> \<forall>x. norm (f x) \<le> norm (g x) \<Longrightarrow> Zfun f F"
  by (erule Zfun_imp_Zfun [where K = 1]) simp

lemma Zfun_add:
  assumes f: "Zfun f F"
    and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x + g x) F"
proof (rule ZfunI)
  fix r :: real
  assume "0 < r"
  then have r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) F"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using elim by (rule add_strict_mono)
    finally show ?case
      by simp
  qed
qed

lemma Zfun_minus: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. - f x) F"
  unfolding Zfun_def by simp

lemma Zfun_diff: "Zfun f F \<Longrightarrow> Zfun g F \<Longrightarrow> Zfun (\<lambda>x. f x - g x) F"
  using Zfun_add [of f F "\<lambda>x. - g x"] by (simp add: Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f (g x)) F"
proof -
  obtain K where "norm (f x) \<le> norm x * K" for x
    using bounded by blast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) F"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f F"
    and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof (rule ZfunI)
  fix r :: real
  assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "norm (x ** y) \<le> norm x * norm y * K" for x y
    using pos_bounded by blast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) F"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero elim K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show ?case .
  qed
qed

lemma (in bounded_bilinear) Zfun_left: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. f x ** a) F"
  by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. a ** f x) F"
  by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = bounded_bilinear.Zfun [OF bounded_bilinear_mult]
lemmas Zfun_mult_right = bounded_bilinear.Zfun_right [OF bounded_bilinear_mult]
lemmas Zfun_mult_left = bounded_bilinear.Zfun_left [OF bounded_bilinear_mult]

lemma tendsto_Zfun_iff: "(f \<longlongrightarrow> a) F = Zfun (\<lambda>x. f x - a) F"
  by (simp only: tendsto_iff Zfun_def dist_norm)

lemma tendsto_0_le:
  "(f \<longlongrightarrow> 0) F \<Longrightarrow> eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F \<Longrightarrow> (g \<longlongrightarrow> 0) F"
  by (simp add: Zfun_imp_Zfun tendsto_Zfun_iff)


subsubsection \<open>Distance and norms\<close>

lemma tendsto_dist [tendsto_intros]:
  fixes l m :: "'a::metric_space"
  assumes f: "(f \<longlongrightarrow> l) F"
    and g: "(g \<longlongrightarrow> m) F"
  shows "((\<lambda>x. dist (f x) (g x)) \<longlongrightarrow> dist l m) F"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  then have e2: "0 < e/2" by simp
  from tendstoD [OF f e2] tendstoD [OF g e2]
  show "eventually (\<lambda>x. dist (dist (f x) (g x)) (dist l m) < e) F"
  proof (eventually_elim)
    case (elim x)
    then show "dist (dist (f x) (g x)) (dist l m) < e"
      unfolding dist_real_def
      using dist_triangle2 [of "f x" "g x" "l"]
        and dist_triangle2 [of "g x" "l" "m"]
        and dist_triangle3 [of "l" "m" "f x"]
        and dist_triangle [of "f x" "m" "g x"]
      by arith
  qed
qed

lemma continuous_dist[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'a :: metric_space"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_def by (rule tendsto_dist)

lemma continuous_on_dist[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'a :: metric_space"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_on_def by (auto intro: tendsto_dist)

lemma continuous_at_dist: "isCont (dist a) b"
  using continuous_on_dist [OF continuous_on_const continuous_on_id] continuous_on_eq_continuous_within by blast

lemma tendsto_norm [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. norm (f x)) \<longlongrightarrow> norm a) F"
  unfolding norm_conv_dist by (intro tendsto_intros)

lemma continuous_norm [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. norm (f x))"
  unfolding continuous_def by (rule tendsto_norm)

lemma continuous_on_norm [continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. norm (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_norm)

lemma continuous_on_norm_id [continuous_intros]: "continuous_on S norm"
  by (intro continuous_on_id continuous_on_norm)

lemma tendsto_norm_zero: "(f \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. norm (f x)) \<longlongrightarrow> 0) F"
  by (drule tendsto_norm) simp

lemma tendsto_norm_zero_cancel: "((\<lambda>x. norm (f x)) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_norm_zero_iff: "((\<lambda>x. norm (f x)) \<longlongrightarrow> 0) F \<longleftrightarrow> (f \<longlongrightarrow> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_rabs [tendsto_intros]: "(f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) \<longlongrightarrow> \<bar>l\<bar>) F"
  for l :: real
  by (fold real_norm_def) (rule tendsto_norm)

lemma continuous_rabs [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. \<bar>f x :: real\<bar>)"
  unfolding real_norm_def[symmetric] by (rule continuous_norm)

lemma continuous_on_rabs [continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. \<bar>f x :: real\<bar>)"
  unfolding real_norm_def[symmetric] by (rule continuous_on_norm)

lemma tendsto_rabs_zero: "(f \<longlongrightarrow> (0::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) \<longlongrightarrow> 0) F"
  by (fold real_norm_def) (rule tendsto_norm_zero)

lemma tendsto_rabs_zero_cancel: "((\<lambda>x. \<bar>f x\<bar>) \<longlongrightarrow> (0::real)) F \<Longrightarrow> (f \<longlongrightarrow> 0) F"
  by (fold real_norm_def) (rule tendsto_norm_zero_cancel)

lemma tendsto_rabs_zero_iff: "((\<lambda>x. \<bar>f x\<bar>) \<longlongrightarrow> (0::real)) F \<longleftrightarrow> (f \<longlongrightarrow> 0) F"
  by (fold real_norm_def) (rule tendsto_norm_zero_iff)


subsection \<open>Topological Monoid\<close>

class topological_monoid_add = topological_space + monoid_add +
  assumes tendsto_add_Pair: "LIM x (nhds a \<times>\<^sub>F nhds b). fst x + snd x :> nhds (a + b)"

class topological_comm_monoid_add = topological_monoid_add + comm_monoid_add

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::topological_monoid_add"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x + g x) \<longlongrightarrow> a + b) F"
  using filterlim_compose[OF tendsto_add_Pair, of "\<lambda>x. (f x, g x)" a b F]
  by (simp add: nhds_prod[symmetric] tendsto_Pair)

lemma continuous_add [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::topological_monoid_add"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x + g x)"
  unfolding continuous_def by (rule tendsto_add)

lemma continuous_on_add [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::topological_monoid_add"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x + g x)"
  unfolding continuous_on_def by (auto intro: tendsto_add)

lemma tendsto_add_zero:
  fixes f g :: "_ \<Rightarrow> 'b::topological_monoid_add"
  shows "(f \<longlongrightarrow> 0) F \<Longrightarrow> (g \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. f x + g x) \<longlongrightarrow> 0) F"
  by (drule (1) tendsto_add) simp

lemma tendsto_sum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::topological_comm_monoid_add"
  shows "(\<And>i. i \<in> I \<Longrightarrow> (f i \<longlongrightarrow> a i) F) \<Longrightarrow> ((\<lambda>x. \<Sum>i\<in>I. f i x) \<longlongrightarrow> (\<Sum>i\<in>I. a i)) F"
  by (induct I rule: infinite_finite_induct) (simp_all add: tendsto_add)

lemma tendsto_null_sum:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::topological_comm_monoid_add"
  assumes "\<And>i. i \<in> I \<Longrightarrow> ((\<lambda>x. f x i) \<longlongrightarrow> 0) F"
  shows "((\<lambda>i. sum (f i) I) \<longlongrightarrow> 0) F"
  using tendsto_sum [of I "\<lambda>x y. f y x" "\<lambda>x. 0"] assms by simp

lemma continuous_sum [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::topological_comm_monoid_add"
  shows "(\<And>i. i \<in> I \<Longrightarrow> continuous F (f i)) \<Longrightarrow> continuous F (\<lambda>x. \<Sum>i\<in>I. f i x)"
  unfolding continuous_def by (rule tendsto_sum)

lemma continuous_on_sum [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::topological_space \<Rightarrow> 'c::topological_comm_monoid_add"
  shows "(\<And>i. i \<in> I \<Longrightarrow> continuous_on S (f i)) \<Longrightarrow> continuous_on S (\<lambda>x. \<Sum>i\<in>I. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_sum)

instance nat :: topological_comm_monoid_add
  by standard
    (simp add: nhds_discrete principal_prod_principal filterlim_principal eventually_principal)

instance int :: topological_comm_monoid_add
  by standard
    (simp add: nhds_discrete principal_prod_principal filterlim_principal eventually_principal)


subsubsection \<open>Topological group\<close>

class topological_group_add = topological_monoid_add + group_add +
  assumes tendsto_uminus_nhds: "(uminus \<longlongrightarrow> - a) (nhds a)"
begin

lemma tendsto_minus [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. - f x) \<longlongrightarrow> - a) F"
  by (rule filterlim_compose[OF tendsto_uminus_nhds])

end

class topological_ab_group_add = topological_group_add + ab_group_add

instance topological_ab_group_add < topological_comm_monoid_add ..

lemma continuous_minus [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. - f x)"
  for f :: "'a::t2_space \<Rightarrow> 'b::topological_group_add"
  unfolding continuous_def by (rule tendsto_minus)

lemma continuous_on_minus [continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. - f x)"
  for f :: "_ \<Rightarrow> 'b::topological_group_add"
  unfolding continuous_on_def by (auto intro: tendsto_minus)

lemma tendsto_minus_cancel: "((\<lambda>x. - f x) \<longlongrightarrow> - a) F \<Longrightarrow> (f \<longlongrightarrow> a) F"
  for a :: "'a::topological_group_add"
  by (drule tendsto_minus) simp

lemma tendsto_minus_cancel_left:
  "(f \<longlongrightarrow> - (y::_::topological_group_add)) F \<longleftrightarrow> ((\<lambda>x. - f x) \<longlongrightarrow> y) F"
  using tendsto_minus_cancel[of f "- y" F]  tendsto_minus[of f "- y" F]
  by auto

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::topological_group_add"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x - g x) \<longlongrightarrow> a - b) F"
  using tendsto_add [of f a F "\<lambda>x. - g x" "- b"] by (simp add: tendsto_minus)

lemma continuous_diff [continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::topological_group_add"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x - g x)"
  unfolding continuous_def by (rule tendsto_diff)

lemma continuous_on_diff [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::topological_group_add"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x - g x)"
  unfolding continuous_on_def by (auto intro: tendsto_diff)

lemma continuous_on_op_minus: "continuous_on (s::'a::topological_group_add set) ((-) x)"
  by (rule continuous_intros | simp)+

instance real_normed_vector < topological_ab_group_add
proof
  fix a b :: 'a
  show "((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)"
    unfolding tendsto_Zfun_iff add_diff_add
    using tendsto_fst[OF filterlim_ident, of "(a,b)"] tendsto_snd[OF filterlim_ident, of "(a,b)"]
    by (intro Zfun_add)
       (auto simp: tendsto_Zfun_iff[symmetric] nhds_prod[symmetric] intro!: tendsto_fst)
  show "(uminus \<longlongrightarrow> - a) (nhds a)"
    unfolding tendsto_Zfun_iff minus_diff_minus
    using filterlim_ident[of "nhds a"]
    by (intro Zfun_minus) (simp add: tendsto_Zfun_iff)
qed

lemmas real_tendsto_sandwich = tendsto_sandwich[where 'a=real]


subsubsection \<open>Linear operators and multiplication\<close>

lemma linear_times [simp]: "linear (\<lambda>x. c * x)"
  for c :: "'a::real_algebra"
  by (auto simp: linearI distrib_left)

lemma (in bounded_linear) tendsto: "(g \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. f (g x)) \<longlongrightarrow> f a) F"
  by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_linear) continuous: "continuous F g \<Longrightarrow> continuous F (\<lambda>x. f (g x))"
  using tendsto[of g _ F] by (auto simp: continuous_def)

lemma (in bounded_linear) continuous_on: "continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f (g x))"
  using tendsto[of g] by (auto simp: continuous_on_def)

lemma (in bounded_linear) tendsto_zero: "(g \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. f (g x)) \<longlongrightarrow> 0) F"
  by (drule tendsto) (simp only: zero)

lemma (in bounded_bilinear) tendsto:
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x ** g x) \<longlongrightarrow> a ** b) F"
  by (simp only: tendsto_Zfun_iff prod_diff_prod Zfun_add Zfun Zfun_left Zfun_right)

lemma (in bounded_bilinear) continuous:
  "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x ** g x)"
  using tendsto[of f _ F g] by (auto simp: continuous_def)

lemma (in bounded_bilinear) continuous_on:
  "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x ** g x)"
  using tendsto[of f _ _ g] by (auto simp: continuous_on_def)

lemma (in bounded_bilinear) tendsto_zero:
  assumes f: "(f \<longlongrightarrow> 0) F"
    and g: "(g \<longlongrightarrow> 0) F"
  shows "((\<lambda>x. f x ** g x) \<longlongrightarrow> 0) F"
  using tendsto [OF f g] by (simp add: zero_left)

lemma (in bounded_bilinear) tendsto_left_zero:
  "(f \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. f x ** c) \<longlongrightarrow> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) tendsto_right_zero:
  "(f \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. c ** f x) \<longlongrightarrow> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_right])

lemmas tendsto_of_real [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_of_real]

lemmas tendsto_scaleR [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_scaleR]


text\<open>Analogous type class for multiplication\<close>
class topological_semigroup_mult = topological_space + semigroup_mult +
  assumes tendsto_mult_Pair: "LIM x (nhds a \<times>\<^sub>F nhds b). fst x * snd x :> nhds (a * b)"

instance real_normed_algebra < topological_semigroup_mult
proof
  fix a b :: 'a
  show "((\<lambda>x. fst x * snd x) \<longlongrightarrow> a * b) (nhds a \<times>\<^sub>F nhds b)"
    unfolding nhds_prod[symmetric]
    using tendsto_fst[OF filterlim_ident, of "(a,b)"] tendsto_snd[OF filterlim_ident, of "(a,b)"]
    by (simp add: bounded_bilinear.tendsto [OF bounded_bilinear_mult])
qed

lemma tendsto_mult [tendsto_intros]:
  fixes a b :: "'a::topological_semigroup_mult"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x * g x) \<longlongrightarrow> a * b) F"
  using filterlim_compose[OF tendsto_mult_Pair, of "\<lambda>x. (f x, g x)" a b F]
  by (simp add: nhds_prod[symmetric] tendsto_Pair)

lemma tendsto_mult_left: "(f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. c * (f x)) \<longlongrightarrow> c * l) F"
  for c :: "'a::topological_semigroup_mult"
  by (rule tendsto_mult [OF tendsto_const])

lemma tendsto_mult_right: "(f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. (f x) * c) \<longlongrightarrow> l * c) F"
  for c :: "'a::topological_semigroup_mult"
  by (rule tendsto_mult [OF _ tendsto_const])

lemma tendsto_mult_left_iff [simp]:
   "c \<noteq> 0 \<Longrightarrow> tendsto(\<lambda>x. c * f x) (c * l) F \<longleftrightarrow> tendsto f l F" for c :: "'a::{topological_semigroup_mult,field}"
  by (auto simp: tendsto_mult_left dest: tendsto_mult_left [where c = "1/c"])

lemma tendsto_mult_right_iff [simp]:
   "c \<noteq> 0 \<Longrightarrow> tendsto(\<lambda>x. f x * c) (l * c) F \<longleftrightarrow> tendsto f l F" for c :: "'a::{topological_semigroup_mult,field}"
  by (auto simp: tendsto_mult_right dest: tendsto_mult_left [where c = "1/c"])

lemma tendsto_zero_mult_left_iff [simp]:
  fixes c::"'a::{topological_semigroup_mult,field}" assumes "c \<noteq> 0" shows "(\<lambda>n. c * a n)\<longlonglongrightarrow> 0 \<longleftrightarrow> a \<longlonglongrightarrow> 0"
  using assms tendsto_mult_left tendsto_mult_left_iff by fastforce

lemma tendsto_zero_mult_right_iff [simp]:
  fixes c::"'a::{topological_semigroup_mult,field}" assumes "c \<noteq> 0" shows "(\<lambda>n. a n * c)\<longlonglongrightarrow> 0 \<longleftrightarrow> a \<longlonglongrightarrow> 0"
  using assms tendsto_mult_right tendsto_mult_right_iff by fastforce

lemma tendsto_zero_divide_iff [simp]:
  fixes c::"'a::{topological_semigroup_mult,field}" assumes "c \<noteq> 0" shows "(\<lambda>n. a n / c)\<longlonglongrightarrow> 0 \<longleftrightarrow> a \<longlonglongrightarrow> 0"
  using tendsto_zero_mult_right_iff [of "1/c" a] assms by (simp add: field_simps)

lemma lim_const_over_n [tendsto_intros]:
  fixes a :: "'a::real_normed_field"
  shows "(\<lambda>n. a / of_nat n) \<longlonglongrightarrow> 0"
  using tendsto_mult [OF tendsto_const [of a] lim_1_over_n] by simp

lemmas continuous_of_real [continuous_intros] =
  bounded_linear.continuous [OF bounded_linear_of_real]

lemmas continuous_scaleR [continuous_intros] =
  bounded_bilinear.continuous [OF bounded_bilinear_scaleR]

lemmas continuous_mult [continuous_intros] =
  bounded_bilinear.continuous [OF bounded_bilinear_mult]

lemmas continuous_on_of_real [continuous_intros] =
  bounded_linear.continuous_on [OF bounded_linear_of_real]

lemmas continuous_on_scaleR [continuous_intros] =
  bounded_bilinear.continuous_on [OF bounded_bilinear_scaleR]

lemmas continuous_on_mult [continuous_intros] =
  bounded_bilinear.continuous_on [OF bounded_bilinear_mult]

lemmas tendsto_mult_zero =
  bounded_bilinear.tendsto_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_left_zero =
  bounded_bilinear.tendsto_left_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_right_zero =
  bounded_bilinear.tendsto_right_zero [OF bounded_bilinear_mult]


lemma continuous_mult_left:
  fixes c::"'a::real_normed_algebra"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. c * f x)"
by (rule continuous_mult [OF continuous_const])

lemma continuous_mult_right:
  fixes c::"'a::real_normed_algebra"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x * c)"
by (rule continuous_mult [OF _ continuous_const])

lemma continuous_on_mult_left:
  fixes c::"'a::real_normed_algebra"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. c * f x)"
by (rule continuous_on_mult [OF continuous_on_const])

lemma continuous_on_mult_right:
  fixes c::"'a::real_normed_algebra"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x * c)"
by (rule continuous_on_mult [OF _ continuous_on_const])

lemma continuous_on_mult_const [simp]:
  fixes c::"'a::real_normed_algebra"
  shows "continuous_on s ((*) c)"
  by (intro continuous_on_mult_left continuous_on_id)

lemma tendsto_divide_zero:
  fixes c :: "'a::real_normed_field"
  shows "(f \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. f x / c) \<longlongrightarrow> 0) F"
  by (cases "c=0") (simp_all add: divide_inverse tendsto_mult_left_zero)

lemma tendsto_power [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. f x ^ n) \<longlongrightarrow> a ^ n) F"
  for f :: "'a \<Rightarrow> 'b::{power,real_normed_algebra}"
  by (induct n) (simp_all add: tendsto_mult)

lemma tendsto_null_power: "\<lbrakk>(f \<longlongrightarrow> 0) F; 0 < n\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ^ n) \<longlongrightarrow> 0) F"
    for f :: "'a \<Rightarrow> 'b::{power,real_normed_algebra_1}"
  using tendsto_power [of f 0 F n] by (simp add: power_0_left)

lemma continuous_power [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. (f x)^n)"
  for f :: "'a::t2_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  unfolding continuous_def by (rule tendsto_power)

lemma continuous_on_power [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. (f x)^n)"
  unfolding continuous_on_def by (auto intro: tendsto_power)

lemma tendsto_prod [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  shows "(\<And>i. i \<in> S \<Longrightarrow> (f i \<longlongrightarrow> L i) F) \<Longrightarrow> ((\<lambda>x. \<Prod>i\<in>S. f i x) \<longlongrightarrow> (\<Prod>i\<in>S. L i)) F"
  by (induct S rule: infinite_finite_induct) (simp_all add: tendsto_mult)

lemma continuous_prod [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous F (f i)) \<Longrightarrow> continuous F (\<lambda>x. \<Prod>i\<in>S. f i x)"
  unfolding continuous_def by (rule tendsto_prod)

lemma continuous_on_prod [continuous_intros]:
  fixes f :: "'a \<Rightarrow> _ \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous_on s (f i)) \<Longrightarrow> continuous_on s (\<lambda>x. \<Prod>i\<in>S. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_prod)

lemma tendsto_of_real_iff:
  "((\<lambda>x. of_real (f x) :: 'a::real_normed_div_algebra) \<longlongrightarrow> of_real c) F \<longleftrightarrow> (f \<longlongrightarrow> c) F"
  unfolding tendsto_iff by simp

lemma tendsto_add_const_iff:
  "((\<lambda>x. c + f x :: 'a::real_normed_vector) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto


class topological_monoid_mult = topological_semigroup_mult + monoid_mult
class topological_comm_monoid_mult = topological_monoid_mult + comm_monoid_mult

lemma tendsto_power_strong [tendsto_intros]:
  fixes f :: "_ \<Rightarrow> 'b :: topological_monoid_mult"
  assumes "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>x. f x ^ g x) \<longlongrightarrow> a ^ b) F"
proof -
  have "((\<lambda>x. f x ^ b) \<longlongrightarrow> a ^ b) F"
    by (induction b) (auto intro: tendsto_intros assms)
  also from assms(2) have "eventually (\<lambda>x. g x = b) F"
    by (simp add: nhds_discrete filterlim_principal)
  hence "eventually (\<lambda>x. f x ^ b = f x ^ g x) F"
    by eventually_elim simp
  hence "((\<lambda>x. f x ^ b) \<longlongrightarrow> a ^ b) F \<longleftrightarrow> ((\<lambda>x. f x ^ g x) \<longlongrightarrow> a ^ b) F"
    by (intro filterlim_cong refl)
  finally show ?thesis .
qed

lemma continuous_mult' [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::topological_semigroup_mult"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x * g x)"
  unfolding continuous_def by (rule tendsto_mult)

lemma continuous_power' [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'b::topological_monoid_mult"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x ^ g x)"
  unfolding continuous_def by (rule tendsto_power_strong) auto

lemma continuous_on_mult' [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::topological_semigroup_mult"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x * g x)"
  unfolding continuous_on_def by (auto intro: tendsto_mult)

lemma continuous_on_power' [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'b::topological_monoid_mult"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x ^ g x)"
  unfolding continuous_on_def by (auto intro: tendsto_power_strong)

lemma tendsto_mult_one:
  fixes f g :: "_ \<Rightarrow> 'b::topological_monoid_mult"
  shows "(f \<longlongrightarrow> 1) F \<Longrightarrow> (g \<longlongrightarrow> 1) F \<Longrightarrow> ((\<lambda>x. f x * g x) \<longlongrightarrow> 1) F"
  by (drule (1) tendsto_mult) simp

lemma tendsto_prod' [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::topological_comm_monoid_mult"
  shows "(\<And>i. i \<in> I \<Longrightarrow> (f i \<longlongrightarrow> a i) F) \<Longrightarrow> ((\<lambda>x. \<Prod>i\<in>I. f i x) \<longlongrightarrow> (\<Prod>i\<in>I. a i)) F"
  by (induct I rule: infinite_finite_induct) (simp_all add: tendsto_mult)

lemma tendsto_one_prod':
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::topological_comm_monoid_mult"
  assumes "\<And>i. i \<in> I \<Longrightarrow> ((\<lambda>x. f x i) \<longlongrightarrow> 1) F"
  shows "((\<lambda>i. prod (f i) I) \<longlongrightarrow> 1) F"
  using tendsto_prod' [of I "\<lambda>x y. f y x" "\<lambda>x. 1"] assms by simp

lemma continuous_prod' [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::topological_comm_monoid_mult"
  shows "(\<And>i. i \<in> I \<Longrightarrow> continuous F (f i)) \<Longrightarrow> continuous F (\<lambda>x. \<Prod>i\<in>I. f i x)"
  unfolding continuous_def by (rule tendsto_prod')

lemma continuous_on_prod' [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::topological_space \<Rightarrow> 'c::topological_comm_monoid_mult"
  shows "(\<And>i. i \<in> I \<Longrightarrow> continuous_on S (f i)) \<Longrightarrow> continuous_on S (\<lambda>x. \<Prod>i\<in>I. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_prod')

instance nat :: topological_comm_monoid_mult
  by standard
    (simp add: nhds_discrete principal_prod_principal filterlim_principal eventually_principal)

instance int :: topological_comm_monoid_mult
  by standard
    (simp add: nhds_discrete principal_prod_principal filterlim_principal eventually_principal)

class comm_real_normed_algebra_1 = real_normed_algebra_1 + comm_monoid_mult

context real_normed_field
begin

subclass comm_real_normed_algebra_1
proof
  from norm_mult[of "1 :: 'a" 1] show "norm 1 = 1" by simp 
qed (simp_all add: norm_mult)

end

subsubsection \<open>Inverse and division\<close>

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f F"
    and g: "Bfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by blast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) F"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) F"
  using norm_g proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero mult_nonneg_nonneg K elim)
    also have "\<dots> = norm (f x) * (B * K)"
      by (rule mult.assoc)
    finally show "norm (f x ** g x) \<le> norm (f x) * (B * K)" .
  qed
  with f show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Bfun_prod_Zfun:
  assumes f: "Bfun f F"
    and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
  using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> a) F"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) F"
proof -
  from a have "0 < norm a" by simp
  then have "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a"
    by blast
  have "eventually (\<lambda>x. dist (f x) a < r) F"
    using tendstoD [OF f r1] by blast
  then have "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) F"
  proof eventually_elim
    case (elim x)
    then have 1: "norm (f x - a) < r"
      by (simp add: dist_norm)
    then have 2: "f x \<noteq> 0" using r2 by auto
    then have "norm (inverse (f x)) = inverse (norm (f x))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r"
        using r2 by simp
      have "norm a - norm (f x) \<le> norm (a - f x)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (f x - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (f x)"
        by simp
    qed
    finally show "norm (inverse (f x)) \<le> inverse (norm a - r)" .
  qed
  then show ?thesis by (rule BfunI)
qed

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> a) F"
    and a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) \<longlongrightarrow> inverse a) F"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) F"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) F"
    unfolding dist_norm by (auto elim!: eventually_mono)
  with a have "eventually (\<lambda>x. inverse (f x) - inverse a =
    - (inverse (f x) * (f x - a) * inverse a)) F"
    by (auto elim!: eventually_mono simp: inverse_diff_inverse)
  moreover have "Zfun (\<lambda>x. - (inverse (f x) * (f x - a) * inverse a)) F"
    by (intro Zfun_minus Zfun_mult_left
      bounded_bilinear.Bfun_prod_Zfun [OF bounded_bilinear_mult]
      Bfun_inverse [OF f a] f [unfolded tendsto_Zfun_iff])
  ultimately show ?thesis
    unfolding tendsto_Zfun_iff by (rule Zfun_ssubst)
qed

lemma continuous_inverse:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous F f"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_def by (rule tendsto_inverse)

lemma continuous_at_within_inverse[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous (at a within s) f"
    and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_within by (rule tendsto_inverse)

lemma continuous_on_inverse[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous_on s f"
    and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_on_def by (blast intro: tendsto_inverse)

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> ((\<lambda>x. f x / g x) \<longlongrightarrow> a / b) F"
  by (simp add: tendsto_mult tendsto_inverse divide_inverse)

lemma continuous_divide:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous F f"
    and "continuous F g"
    and "g (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_def by (rule tendsto_divide)

lemma continuous_at_within_divide[continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous (at a within s) f" "continuous (at a within s) g"
    and "g a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_within by (rule tendsto_divide)

lemma isCont_divide[continuous_intros, simp]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "isCont f a" "isCont g a" "g a \<noteq> 0"
  shows "isCont (\<lambda>x. (f x) / g x) a"
  using assms unfolding continuous_at by (rule tendsto_divide)

lemma continuous_on_divide[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous_on s f" "continuous_on s g"
    and "\<forall>x\<in>s. g x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_on_def by (blast intro: tendsto_divide)

lemma tendsto_power_int [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> a) F"
    and a: "a \<noteq> 0"
  shows "((\<lambda>x. power_int (f x) n) \<longlongrightarrow> power_int a n) F"
  using assms by (cases n rule: int_cases4) (auto intro!: tendsto_intros simp: power_int_minus)

lemma continuous_power_int:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous F f"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. power_int (f x) n)"
  using assms unfolding continuous_def by (rule tendsto_power_int)

lemma continuous_at_within_power_int[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous (at a within s) f"
    and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. power_int (f x) n)"
  using assms unfolding continuous_within by (rule tendsto_power_int)

lemma continuous_on_power_int [continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous_on s f" and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. power_int (f x) n)"
  using assms unfolding continuous_on_def by (blast intro: tendsto_power_int)

lemma tendsto_sgn [tendsto_intros]: "(f \<longlongrightarrow> l) F \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> ((\<lambda>x. sgn (f x)) \<longlongrightarrow> sgn l) F"
  for l :: "'a::real_normed_vector"
  unfolding sgn_div_norm by (simp add: tendsto_intros)

lemma continuous_sgn:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous F f"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_def by (rule tendsto_sgn)

lemma continuous_at_within_sgn[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous (at a within s) f"
    and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_within by (rule tendsto_sgn)

lemma isCont_sgn[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "isCont f a"
    and "f a \<noteq> 0"
  shows "isCont (\<lambda>x. sgn (f x)) a"
  using assms unfolding continuous_at by (rule tendsto_sgn)

lemma continuous_on_sgn[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on s f"
    and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_on_def by (blast intro: tendsto_sgn)

lemma filterlim_at_infinity:
  fixes f :: "_ \<Rightarrow> 'a::real_normed_vector"
  assumes "0 \<le> c"
  shows "(LIM x F. f x :> at_infinity) \<longleftrightarrow> (\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F)"
  unfolding filterlim_iff eventually_at_infinity
proof safe
  fix P :: "'a \<Rightarrow> bool"
  fix b
  assume *: "\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F"
  assume P: "\<forall>x. b \<le> norm x \<longrightarrow> P x"
  have "max b (c + 1) > c" by auto
  with * have "eventually (\<lambda>x. max b (c + 1) \<le> norm (f x)) F"
    by auto
  then show "eventually (\<lambda>x. P (f x)) F"
  proof eventually_elim
    case (elim x)
    with P show "P (f x)" by auto
  qed
qed force

lemma filterlim_at_infinity_imp_norm_at_top:
  fixes F
  assumes "filterlim f at_infinity F"
  shows   "filterlim (\<lambda>x. norm (f x)) at_top F"
proof -
  {
    fix r :: real
    have "\<forall>\<^sub>F x in F. r \<le> norm (f x)" using filterlim_at_infinity[of 0 f F] assms
      by (cases "r > 0")
         (auto simp: not_less intro: always_eventually order.trans[OF _ norm_ge_zero])
  }
  thus ?thesis by (auto simp: filterlim_at_top)
qed

lemma filterlim_norm_at_top_imp_at_infinity:
  fixes F
  assumes "filterlim (\<lambda>x. norm (f x)) at_top F"
  shows   "filterlim f at_infinity F"
  using filterlim_at_infinity[of 0 f F] assms by (auto simp: filterlim_at_top)

lemma filterlim_norm_at_top: "filterlim norm at_top at_infinity"
  by (rule filterlim_at_infinity_imp_norm_at_top) (rule filterlim_ident)

lemma filterlim_at_infinity_conv_norm_at_top:
  "filterlim f at_infinity G \<longleftrightarrow> filterlim (\<lambda>x. norm (f x)) at_top G"
  by (auto simp: filterlim_at_infinity[OF order.refl] filterlim_at_top_gt[of _ _ 0])

lemma eventually_not_equal_at_infinity:
  "eventually (\<lambda>x. x \<noteq> (a :: 'a :: {real_normed_vector})) at_infinity"
proof -
  from filterlim_norm_at_top[where 'a = 'a]
    have "\<forall>\<^sub>F x in at_infinity. norm a < norm (x::'a)" by (auto simp: filterlim_at_top_dense)
  thus ?thesis by eventually_elim auto
qed

lemma filterlim_int_of_nat_at_topD:
  fixes F
  assumes "filterlim (\<lambda>x. f (int x)) F at_top"
  shows   "filterlim f F at_top"
proof -
  have "filterlim (\<lambda>x. f (int (nat x))) F at_top"
    by (rule filterlim_compose[OF assms filterlim_nat_sequentially])
  also have "?this \<longleftrightarrow> filterlim f F at_top"
    by (intro filterlim_cong refl eventually_mono [OF eventually_ge_at_top[of "0::int"]]) auto
  finally show ?thesis .
qed

lemma filterlim_int_sequentially [tendsto_intros]:
  "filterlim int at_top sequentially"
  unfolding filterlim_at_top
proof
  fix C :: int
  show "eventually (\<lambda>n. int n \<ge> C) at_top"
    using eventually_ge_at_top[of "nat \<lceil>C\<rceil>"] by eventually_elim linarith
qed

lemma filterlim_real_of_int_at_top [tendsto_intros]:
  "filterlim real_of_int at_top at_top"
  unfolding filterlim_at_top
proof
  fix C :: real
  show "eventually (\<lambda>n. real_of_int n \<ge> C) at_top"
    using eventually_ge_at_top[of "\<lceil>C\<rceil>"] by eventually_elim linarith
qed

lemma filterlim_abs_real: "filterlim (abs::real \<Rightarrow> real) at_top at_top"
proof (subst filterlim_cong[OF refl refl])
  from eventually_ge_at_top[of "0::real"] show "eventually (\<lambda>x::real. \<bar>x\<bar> = x) at_top"
    by eventually_elim simp
qed (simp_all add: filterlim_ident)

lemma filterlim_of_real_at_infinity [tendsto_intros]:
  "filterlim (of_real :: real \<Rightarrow> 'a :: real_normed_algebra_1) at_infinity at_top"
  by (intro filterlim_norm_at_top_imp_at_infinity) (auto simp: filterlim_abs_real)

lemma not_tendsto_and_filterlim_at_infinity:
  fixes c :: "'a::real_normed_vector"
  assumes "F \<noteq> bot"
    and "(f \<longlongrightarrow> c) F"
    and "filterlim f at_infinity F"
  shows False
proof -
  from tendstoD[OF assms(2), of "1/2"]
  have "eventually (\<lambda>x. dist (f x) c < 1/2) F"
    by simp
  moreover
  from filterlim_at_infinity[of "norm c" f F] assms(3)
  have "eventually (\<lambda>x. norm (f x) \<ge> norm c + 1) F" by simp
  ultimately have "eventually (\<lambda>x. False) F"
  proof eventually_elim
    fix x
    assume A: "dist (f x) c < 1/2"
    assume "norm (f x) \<ge> norm c + 1"
    also have "norm (f x) = dist (f x) 0" by simp
    also have "\<dots> \<le> dist (f x) c + dist c 0" by (rule dist_triangle)
    finally show False using A by simp
  qed
  with assms show False by simp
qed

lemma filterlim_at_infinity_imp_not_convergent:
  assumes "filterlim f at_infinity sequentially"
  shows "\<not> convergent f"
  by (rule notI, rule not_tendsto_and_filterlim_at_infinity[OF _ _ assms])
     (simp_all add: convergent_LIMSEQ_iff)

lemma filterlim_at_infinity_imp_eventually_ne:
  assumes "filterlim f at_infinity F"
  shows "eventually (\<lambda>z. f z \<noteq> c) F"
proof -
  have "norm c + 1 > 0"
    by (intro add_nonneg_pos) simp_all
  with filterlim_at_infinity[OF order.refl, of f F] assms
  have "eventually (\<lambda>z. norm (f z) \<ge> norm c + 1) F"
    by blast
  then show ?thesis
    by eventually_elim auto
qed

lemma tendsto_of_nat [tendsto_intros]:
  "filterlim (of_nat :: nat \<Rightarrow> 'a::real_normed_algebra_1) at_infinity sequentially"
proof (subst filterlim_at_infinity[OF order.refl], intro allI impI)
  fix r :: real
  assume r: "r > 0"
  define n where "n = nat \<lceil>r\<rceil>"
  from r have n: "\<forall>m\<ge>n. of_nat m \<ge> r"
    unfolding n_def by linarith
  from eventually_ge_at_top[of n] show "eventually (\<lambda>m. norm (of_nat m :: 'a) \<ge> r) sequentially"
    by eventually_elim (use n in simp_all)
qed


subsection \<open>Relate \<^const>\<open>at\<close>, \<^const>\<open>at_left\<close> and \<^const>\<open>at_right\<close>\<close>

text \<open>
  This lemmas are useful for conversion between \<^term>\<open>at x\<close> to \<^term>\<open>at_left x\<close> and
  \<^term>\<open>at_right x\<close> and also \<^term>\<open>at_right 0\<close>.
\<close>

lemmas filterlim_split_at_real = filterlim_split_at[where 'a=real]

lemma filtermap_nhds_shift: "filtermap (\<lambda>x. x - d) (nhds a) = nhds (a - d)"
  for a d :: "'a::real_normed_vector"
  by (rule filtermap_fun_inverse[where g="\<lambda>x. x + d"])
    (auto intro!: tendsto_eq_intros filterlim_ident)

lemma filtermap_nhds_minus: "filtermap (\<lambda>x. - x) (nhds a) = nhds (- a)"
  for a :: "'a::real_normed_vector"
  by (rule filtermap_fun_inverse[where g=uminus])
    (auto intro!: tendsto_eq_intros filterlim_ident)

lemma filtermap_at_shift: "filtermap (\<lambda>x. x - d) (at a) = at (a - d)"
  for a d :: "'a::real_normed_vector"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma filtermap_at_right_shift: "filtermap (\<lambda>x. x - d) (at_right a) = at_right (a - d)"
  for a d :: "real"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma filterlim_shift:
  fixes d :: "'a::real_normed_vector"
  assumes "filterlim f F (at a)"
  shows "filterlim (f \<circ> (+) d) F (at (a - d))"
  unfolding filterlim_iff
proof (intro strip)
  fix P
  assume "eventually P F"
  then have "\<forall>\<^sub>F x in filtermap (\<lambda>y. y - d) (at a). P (f (d + x))"
    using assms by (force simp add: filterlim_iff eventually_filtermap)
  then show "(\<forall>\<^sub>F x in at (a - d). P ((f \<circ> (+) d) x))"
    by (force simp add: filtermap_at_shift)
qed

lemma filterlim_shift_iff:
  fixes d :: "'a::real_normed_vector"
  shows "filterlim (f \<circ> (+) d) F (at (a - d)) = filterlim f F (at a)"   (is "?lhs = ?rhs")
proof
  assume L: ?lhs show ?rhs
    using filterlim_shift [OF L, of "-d"] by (simp add: filterlim_iff)
qed (metis filterlim_shift)

lemma at_right_to_0: "at_right a = filtermap (\<lambda>x. x + a) (at_right 0)"
  for a :: real
  using filtermap_at_right_shift[of "-a" 0] by simp

lemma filterlim_at_right_to_0:
  "filterlim f F (at_right a) \<longleftrightarrow> filterlim (\<lambda>x. f (x + a)) F (at_right 0)"
  for a :: real
  unfolding filterlim_def filtermap_filtermap at_right_to_0[of a] ..

lemma eventually_at_right_to_0:
  "eventually P (at_right a) \<longleftrightarrow> eventually (\<lambda>x. P (x + a)) (at_right 0)"
  for a :: real
  unfolding at_right_to_0[of a] by (simp add: eventually_filtermap)

lemma at_to_0: "at a = filtermap (\<lambda>x. x + a) (at 0)"
  for a :: "'a::real_normed_vector"
  using filtermap_at_shift[of "-a" 0] by simp

lemma filterlim_at_to_0:
  "filterlim f F (at a) \<longleftrightarrow> filterlim (\<lambda>x. f (x + a)) F (at 0)"
  for a :: "'a::real_normed_vector"
  unfolding filterlim_def filtermap_filtermap at_to_0[of a] ..

lemma eventually_at_to_0:
  "eventually P (at a) \<longleftrightarrow> eventually (\<lambda>x. P (x + a)) (at 0)"
  for a ::  "'a::real_normed_vector"
  unfolding at_to_0[of a] by (simp add: eventually_filtermap)

lemma filtermap_at_minus: "filtermap (\<lambda>x. - x) (at a) = at (- a)"
  for a :: "'a::real_normed_vector"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])

lemma at_left_minus: "at_left a = filtermap (\<lambda>x. - x) (at_right (- a))"
  for a :: real
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])

lemma at_right_minus: "at_right a = filtermap (\<lambda>x. - x) (at_left (- a))"
  for a :: real
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])


lemma filterlim_at_left_to_right:
  "filterlim f F (at_left a) \<longleftrightarrow> filterlim (\<lambda>x. f (- x)) F (at_right (-a))"
  for a :: real
  unfolding filterlim_def filtermap_filtermap at_left_minus[of a] ..

lemma eventually_at_left_to_right:
  "eventually P (at_left a) \<longleftrightarrow> eventually (\<lambda>x. P (- x)) (at_right (-a))"
  for a :: real
  unfolding at_left_minus[of a] by (simp add: eventually_filtermap)

lemma filterlim_uminus_at_top_at_bot: "LIM x at_bot. - x :: real :> at_top"
  unfolding filterlim_at_top eventually_at_bot_dense
  by (metis leI minus_less_iff order_less_asym)

lemma filterlim_uminus_at_bot_at_top: "LIM x at_top. - x :: real :> at_bot"
  unfolding filterlim_at_bot eventually_at_top_dense
  by (metis leI less_minus_iff order_less_asym)

lemma at_bot_mirror :
  shows "(at_bot::('a::{ordered_ab_group_add,linorder} filter)) = filtermap uminus at_top"
proof (rule filtermap_fun_inverse[symmetric])
  show "filterlim uminus at_top (at_bot::'a filter)"
    using eventually_at_bot_linorder filterlim_at_top le_minus_iff by force
  show "filterlim uminus (at_bot::'a filter) at_top"
    by (simp add: filterlim_at_bot minus_le_iff)
qed auto

lemma at_top_mirror :
  shows "(at_top::('a::{ordered_ab_group_add,linorder} filter)) = filtermap uminus at_bot"
  apply (subst at_bot_mirror)
  by (auto simp: filtermap_filtermap)

lemma filterlim_at_top_mirror: "(LIM x at_top. f x :> F) \<longleftrightarrow> (LIM x at_bot. f (-x::real) :> F)"
  unfolding filterlim_def at_top_mirror filtermap_filtermap ..

lemma filterlim_at_bot_mirror: "(LIM x at_bot. f x :> F) \<longleftrightarrow> (LIM x at_top. f (-x::real) :> F)"
  unfolding filterlim_def at_bot_mirror filtermap_filtermap ..

lemma filterlim_uminus_at_top: "(LIM x F. f x :> at_top) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_bot)"
  using filterlim_compose[OF filterlim_uminus_at_bot_at_top, of f F]
    and filterlim_compose[OF filterlim_uminus_at_top_at_bot, of "\<lambda>x. - f x" F]
  by auto

lemma tendsto_at_botI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_bot sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_bot"
  unfolding filterlim_at_bot_mirror
proof (rule tendsto_at_topI_sequentially)
  fix X :: "nat \<Rightarrow> real" assume "filterlim X at_top sequentially"
  thus "(\<lambda>n. f (-X n)) \<longlonglongrightarrow> y" by (intro *) (auto simp: filterlim_uminus_at_top)
qed

lemma filterlim_at_infinity_imp_filterlim_at_top:
  assumes "filterlim (f :: 'a \<Rightarrow> real) at_infinity F"
  assumes "eventually (\<lambda>x. f x > 0) F"
  shows   "filterlim f at_top F"
proof -
  from assms(2) have *: "eventually (\<lambda>x. norm (f x) = f x) F" by eventually_elim simp
  from assms(1) show ?thesis unfolding filterlim_at_infinity_conv_norm_at_top
    by (subst (asm) filterlim_cong[OF refl refl *])
qed

lemma filterlim_at_infinity_imp_filterlim_at_bot:
  assumes "filterlim (f :: 'a \<Rightarrow> real) at_infinity F"
  assumes "eventually (\<lambda>x. f x < 0) F"
  shows   "filterlim f at_bot F"
proof -
  from assms(2) have *: "eventually (\<lambda>x. norm (f x) = -f x) F" by eventually_elim simp
  from assms(1) have "filterlim (\<lambda>x. - f x) at_top F"
    unfolding filterlim_at_infinity_conv_norm_at_top
    by (subst (asm) filterlim_cong[OF refl refl *])
  thus ?thesis by (simp add: filterlim_uminus_at_top)
qed

lemma filterlim_uminus_at_bot: "(LIM x F. f x :> at_bot) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_top)"
  unfolding filterlim_uminus_at_top by simp

lemma filterlim_inverse_at_top_right: "LIM x at_right (0::real). inverse x :> at_top"
  unfolding filterlim_at_top_gt[where c=0] eventually_at_filter
proof safe
  fix Z :: real
  assume [arith]: "0 < Z"
  then have "eventually (\<lambda>x. x < inverse Z) (nhds 0)"
    by (auto simp: eventually_nhds_metric dist_real_def intro!: exI[of _ "\<bar>inverse Z\<bar>"])
  then show "eventually (\<lambda>x. x \<noteq> 0 \<longrightarrow> x \<in> {0<..} \<longrightarrow> Z \<le> inverse x) (nhds 0)"
    by (auto elim!: eventually_mono simp: inverse_eq_divide field_simps)
qed

lemma tendsto_inverse_0:
  fixes x :: "_ \<Rightarrow> 'a::real_normed_div_algebra"
  shows "(inverse \<longlongrightarrow> (0::'a)) at_infinity"
  unfolding tendsto_Zfun_iff diff_0_right Zfun_def eventually_at_infinity
proof safe
  fix r :: real
  assume "0 < r"
  show "\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> norm (inverse x :: 'a) < r"
  proof (intro exI[of _ "inverse (r / 2)"] allI impI)
    fix x :: 'a
    from \<open>0 < r\<close> have "0 < inverse (r / 2)" by simp
    also assume *: "inverse (r / 2) \<le> norm x"
    finally show "norm (inverse x) < r"
      using * \<open>0 < r\<close>
      by (subst nonzero_norm_inverse) (simp_all add: inverse_eq_divide field_simps)
  qed
qed

lemma tendsto_add_filterlim_at_infinity:
  fixes c :: "'b::real_normed_vector"
    and F :: "'a filter"
  assumes "(f \<longlongrightarrow> c) F"
    and "filterlim g at_infinity F"
  shows "filterlim (\<lambda>x. f x + g x) at_infinity F"
proof (subst filterlim_at_infinity[OF order_refl], safe)
  fix r :: real
  assume r: "r > 0"
  from assms(1) have "((\<lambda>x. norm (f x)) \<longlongrightarrow> norm c) F"
    by (rule tendsto_norm)
  then have "eventually (\<lambda>x. norm (f x) < norm c + 1) F"
    by (rule order_tendstoD) simp_all
  moreover from r have "r + norm c + 1 > 0"
    by (intro add_pos_nonneg) simp_all
  with assms(2) have "eventually (\<lambda>x. norm (g x) \<ge> r + norm c + 1) F"
    unfolding filterlim_at_infinity[OF order_refl]
    by (elim allE[of _ "r + norm c + 1"]) simp_all
  ultimately show "eventually (\<lambda>x. norm (f x + g x) \<ge> r) F"
  proof eventually_elim
    fix x :: 'a
    assume A: "norm (f x) < norm c + 1" and B: "r + norm c + 1 \<le> norm (g x)"
    from A B have "r \<le> norm (g x) - norm (f x)"
      by simp
    also have "norm (g x) - norm (f x) \<le> norm (g x + f x)"
      by (rule norm_diff_ineq)
    finally show "r \<le> norm (f x + g x)"
      by (simp add: add_ac)
  qed
qed

lemma tendsto_add_filterlim_at_infinity':
  fixes c :: "'b::real_normed_vector"
    and F :: "'a filter"
  assumes "filterlim f at_infinity F"
    and "(g \<longlongrightarrow> c) F"
  shows "filterlim (\<lambda>x. f x + g x) at_infinity F"
  by (subst add.commute) (rule tendsto_add_filterlim_at_infinity assms)+

lemma filterlim_inverse_at_right_top: "LIM x at_top. inverse x :> at_right (0::real)"
  unfolding filterlim_at
  by (auto simp: eventually_at_top_dense)
     (metis tendsto_inverse_0 filterlim_mono at_top_le_at_infinity order_refl)

lemma filterlim_inverse_at_top:
  "(f \<longlongrightarrow> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> LIM x F. inverse (f x) :> at_top"
  by (intro filterlim_compose[OF filterlim_inverse_at_top_right])
     (simp add: filterlim_def eventually_filtermap eventually_mono at_within_def le_principal)

lemma filterlim_inverse_at_bot_neg:
  "LIM x (at_left (0::real)). inverse x :> at_bot"
  by (simp add: filterlim_inverse_at_top_right filterlim_uminus_at_bot filterlim_at_left_to_right)

lemma filterlim_inverse_at_bot:
  "(f \<longlongrightarrow> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. f x < 0) F \<Longrightarrow> LIM x F. inverse (f x) :> at_bot"
  unfolding filterlim_uminus_at_bot inverse_minus_eq[symmetric]
  by (rule filterlim_inverse_at_top) (simp_all add: tendsto_minus_cancel_left[symmetric])

lemma at_right_to_top: "(at_right (0::real)) = filtermap inverse at_top"
  by (intro filtermap_fun_inverse[symmetric, where g=inverse])
     (auto intro: filterlim_inverse_at_top_right filterlim_inverse_at_right_top)

lemma eventually_at_right_to_top:
  "eventually P (at_right (0::real)) \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) at_top"
  unfolding at_right_to_top eventually_filtermap ..

lemma filterlim_at_right_to_top:
  "filterlim f F (at_right (0::real)) \<longleftrightarrow> (LIM x at_top. f (inverse x) :> F)"
  unfolding filterlim_def at_right_to_top filtermap_filtermap ..

lemma at_top_to_right: "at_top = filtermap inverse (at_right (0::real))"
  unfolding at_right_to_top filtermap_filtermap inverse_inverse_eq filtermap_ident ..

lemma eventually_at_top_to_right:
  "eventually P at_top \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) (at_right (0::real))"
  unfolding at_top_to_right eventually_filtermap ..

lemma filterlim_at_top_to_right:
  "filterlim f F at_top \<longleftrightarrow> (LIM x (at_right (0::real)). f (inverse x) :> F)"
  unfolding filterlim_def at_top_to_right filtermap_filtermap ..

lemma filterlim_inverse_at_infinity:
  fixes x :: "_ \<Rightarrow> 'a::{real_normed_div_algebra, division_ring}"
  shows "filterlim inverse at_infinity (at (0::'a))"
  unfolding filterlim_at_infinity[OF order_refl]
proof safe
  fix r :: real
  assume "0 < r"
  then show "eventually (\<lambda>x::'a. r \<le> norm (inverse x)) (at 0)"
    unfolding eventually_at norm_inverse
    by (intro exI[of _ "inverse r"])
       (auto simp: norm_conv_dist[symmetric] field_simps inverse_eq_divide)
qed

lemma filterlim_inverse_at_iff:
  fixes g :: "'a \<Rightarrow> 'b::{real_normed_div_algebra, division_ring}"
  shows "(LIM x F. inverse (g x) :> at 0) \<longleftrightarrow> (LIM x F. g x :> at_infinity)"
  unfolding filterlim_def filtermap_filtermap[symmetric]
proof
  assume "filtermap g F \<le> at_infinity"
  then have "filtermap inverse (filtermap g F) \<le> filtermap inverse at_infinity"
    by (rule filtermap_mono)
  also have "\<dots> \<le> at 0"
    using tendsto_inverse_0[where 'a='b]
    by (auto intro!: exI[of _ 1]
        simp: le_principal eventually_filtermap filterlim_def at_within_def eventually_at_infinity)
  finally show "filtermap inverse (filtermap g F) \<le> at 0" .
next
  assume "filtermap inverse (filtermap g F) \<le> at 0"
  then have "filtermap inverse (filtermap inverse (filtermap g F)) \<le> filtermap inverse (at 0)"
    by (rule filtermap_mono)
  with filterlim_inverse_at_infinity show "filtermap g F \<le> at_infinity"
    by (auto intro: order_trans simp: filterlim_def filtermap_filtermap)
qed

lemma tendsto_mult_filterlim_at_infinity:
  fixes c :: "'a::real_normed_field"
  assumes  "(f \<longlongrightarrow> c) F" "c \<noteq> 0"
  assumes "filterlim g at_infinity F"
  shows "filterlim (\<lambda>x. f x * g x) at_infinity F"
proof -
  have "((\<lambda>x. inverse (f x) * inverse (g x)) \<longlongrightarrow> inverse c * 0) F"
    by (intro tendsto_mult tendsto_inverse assms filterlim_compose[OF tendsto_inverse_0])
  then have "filterlim (\<lambda>x. inverse (f x) * inverse (g x)) (at (inverse c * 0)) F"
    unfolding filterlim_at
    using assms
    by (auto intro: filterlim_at_infinity_imp_eventually_ne tendsto_imp_eventually_ne eventually_conj)
  then show ?thesis
    by (subst filterlim_inverse_at_iff[symmetric]) simp_all
qed

lemma tendsto_inverse_0_at_top: "LIM x F. f x :> at_top \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) \<longlongrightarrow> 0) F"
  by (metis filterlim_at filterlim_mono[OF _ at_top_le_at_infinity order_refl] filterlim_inverse_at_iff)

lemma filterlim_inverse_at_top_iff:
  "eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> (LIM x F. inverse (f x) :> at_top) \<longleftrightarrow> (f \<longlongrightarrow> (0 :: real)) F"
  by (auto dest: tendsto_inverse_0_at_top filterlim_inverse_at_top)

lemma filterlim_at_top_iff_inverse_0:
  "eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> (LIM x F. f x :> at_top) \<longleftrightarrow> ((inverse \<circ> f) \<longlongrightarrow> (0 :: real)) F"
  using filterlim_inverse_at_top_iff [of "inverse \<circ> f"] by auto

lemma real_tendsto_divide_at_top:
  fixes c::"real"
  assumes "(f \<longlongrightarrow> c) F"
  assumes "filterlim g at_top F"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
  by (auto simp: divide_inverse_commute
      intro!: tendsto_mult[THEN tendsto_eq_rhs] tendsto_inverse_0_at_top assms)

lemma mult_nat_left_at_top: "c > 0 \<Longrightarrow> filterlim (\<lambda>x. c * x) at_top sequentially"
  for c :: nat
  by (rule filterlim_subseq) (auto simp: strict_mono_def)

lemma mult_nat_right_at_top: "c > 0 \<Longrightarrow> filterlim (\<lambda>x. x * c) at_top sequentially"
  for c :: nat
  by (rule filterlim_subseq) (auto simp: strict_mono_def)

lemma filterlim_times_pos:
  "LIM x F1. c * f x :> at_right l"
  if "filterlim f (at_right p) F1" "0 < c" "l = c * p"
  for c::"'a::{linordered_field, linorder_topology}"
  unfolding filterlim_iff
proof safe
  fix P
  assume "\<forall>\<^sub>F x in at_right l. P x"
  then obtain d where "c * p < d" "\<And>y. y > c * p \<Longrightarrow> y < d \<Longrightarrow> P y"
    unfolding \<open>l = _ \<close> eventually_at_right_field
    by auto
  then have "\<forall>\<^sub>F a in at_right p. P (c * a)"
    by (auto simp: eventually_at_right_field \<open>0 < c\<close> field_simps intro!: exI[where x="d/c"])
  from that(1)[unfolded filterlim_iff, rule_format, OF this]
  show "\<forall>\<^sub>F x in F1. P (c * f x)" .
qed

lemma filtermap_nhds_times: "c \<noteq> 0 \<Longrightarrow> filtermap (times c) (nhds a) = nhds (c * a)"
  for a c :: "'a::real_normed_field"
  by (rule filtermap_fun_inverse[where g="\<lambda>x. inverse c * x"])
    (auto intro!: tendsto_eq_intros filterlim_ident)

lemma filtermap_times_pos_at_right:
  fixes c::"'a::{linordered_field, linorder_topology}"
  assumes "c > 0"
  shows "filtermap (times c) (at_right p) = at_right (c * p)"
  using assms
  by (intro filtermap_fun_inverse[where g="\<lambda>x. inverse c * x"])
    (auto intro!: filterlim_ident filterlim_times_pos)

lemma at_to_infinity: "(at (0::'a::{real_normed_field,field})) = filtermap inverse at_infinity"
proof (rule antisym)
  have "(inverse \<longlongrightarrow> (0::'a)) at_infinity"
    by (fact tendsto_inverse_0)
  then show "filtermap inverse at_infinity \<le> at (0::'a)"
    using filterlim_def filterlim_ident filterlim_inverse_at_iff by fastforce
next
  have "filtermap inverse (filtermap inverse (at (0::'a))) \<le> filtermap inverse at_infinity"
    using filterlim_inverse_at_infinity unfolding filterlim_def
    by (rule filtermap_mono)
  then show "at (0::'a) \<le> filtermap inverse at_infinity"
    by (simp add: filtermap_ident filtermap_filtermap)
qed

lemma lim_at_infinity_0:
  fixes l :: "'a::{real_normed_field,field}"
  shows "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> ((f \<circ> inverse) \<longlongrightarrow> l) (at (0::'a))"
  by (simp add: tendsto_compose_filtermap at_to_infinity filtermap_filtermap)

lemma lim_zero_infinity:
  fixes l :: "'a::{real_normed_field,field}"
  shows "((\<lambda>x. f(1 / x)) \<longlongrightarrow> l) (at (0::'a)) \<Longrightarrow> (f \<longlongrightarrow> l) at_infinity"
  by (simp add: inverse_eq_divide lim_at_infinity_0 comp_def)


text \<open>
  We only show rules for multiplication and addition when the functions are either against a real
  value or against infinity. Further rules are easy to derive by using @{thm
  filterlim_uminus_at_top}.
\<close>

lemma filterlim_tendsto_pos_mult_at_top:
  assumes f: "(f \<longlongrightarrow> c) F"
    and c: "0 < c"
    and g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real
  assume "0 < Z"
  from f \<open>0 < c\<close> have "eventually (\<lambda>x. c / 2 < f x) F"
    by (auto dest!: tendstoD[where e="c / 2"] elim!: eventually_mono
        simp: dist_real_def abs_real_def split: if_split_asm)
  moreover from g have "eventually (\<lambda>x. (Z / c * 2) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    case (elim x)
    with \<open>0 < Z\<close> \<open>0 < c\<close> have "c / 2 * (Z / c * 2) \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    with \<open>0 < c\<close> show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_at_top_mult_at_top:
  assumes f: "LIM x F. f x :> at_top"
    and g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real
  assume "0 < Z"
  from f have "eventually (\<lambda>x. 1 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    case (elim x)
    with \<open>0 < Z\<close> have "1 * Z \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    then show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_at_top_mult_tendsto_pos:
  assumes f: "(f \<longlongrightarrow> c) F"
    and c: "0 < c"
    and g: "LIM x F. g x :> at_top"
  shows "LIM x F. (g x * f x:: real) :> at_top"
  by (auto simp: mult.commute intro!: filterlim_tendsto_pos_mult_at_top f c g)

lemma filterlim_tendsto_pos_mult_at_bot:
  fixes c :: real
  assumes "(f \<longlongrightarrow> c) F" "0 < c" "filterlim g at_bot F"
  shows "LIM x F. f x * g x :> at_bot"
  using filterlim_tendsto_pos_mult_at_top[OF assms(1,2), of "\<lambda>x. - g x"] assms(3)
  unfolding filterlim_uminus_at_bot by simp

lemma filterlim_tendsto_neg_mult_at_bot:
  fixes c :: real
  assumes c: "(f \<longlongrightarrow> c) F" "c < 0" and g: "filterlim g at_top F"
  shows "LIM x F. f x * g x :> at_bot"
  using c filterlim_tendsto_pos_mult_at_top[of "\<lambda>x. - f x" "- c" F, OF _ _ g]
  unfolding filterlim_uminus_at_bot tendsto_minus_cancel_left by simp

lemma filterlim_pow_at_top:
  fixes f :: "'a \<Rightarrow> real"
  assumes "0 < n"
    and f: "LIM x F. f x :> at_top"
  shows "LIM x F. (f x)^n :: real :> at_top"
  using \<open>0 < n\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n) with f show ?case
    by (cases "n = 0") (auto intro!: filterlim_at_top_mult_at_top)
qed

lemma filterlim_pow_at_bot_even:
  fixes f :: "real \<Rightarrow> real"
  shows "0 < n \<Longrightarrow> LIM x F. f x :> at_bot \<Longrightarrow> even n \<Longrightarrow> LIM x F. (f x)^n :> at_top"
  using filterlim_pow_at_top[of n "\<lambda>x. - f x" F] by (simp add: filterlim_uminus_at_top)

lemma filterlim_pow_at_bot_odd:
  fixes f :: "real \<Rightarrow> real"
  shows "0 < n \<Longrightarrow> LIM x F. f x :> at_bot \<Longrightarrow> odd n \<Longrightarrow> LIM x F. (f x)^n :> at_bot"
  using filterlim_pow_at_top[of n "\<lambda>x. - f x" F] by (simp add: filterlim_uminus_at_bot)

lemma filterlim_power_at_infinity [tendsto_intros]:
  fixes F and f :: "'a \<Rightarrow> 'b :: real_normed_div_algebra"
  assumes "filterlim f at_infinity F" "n > 0"
  shows   "filterlim (\<lambda>x. f x ^ n) at_infinity F"
  by (rule filterlim_norm_at_top_imp_at_infinity)
     (auto simp: norm_power intro!: filterlim_pow_at_top assms
           intro: filterlim_at_infinity_imp_norm_at_top)

lemma filterlim_tendsto_add_at_top:
  assumes f: "(f \<longlongrightarrow> c) F"
    and g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real
  assume "0 < Z"
  from f have "eventually (\<lambda>x. c - 1 < f x) F"
    by (auto dest!: tendstoD[where e=1] elim!: eventually_mono simp: dist_real_def)
  moreover from g have "eventually (\<lambda>x. Z - (c - 1) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma LIM_at_top_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "(f \<longlongrightarrow> a) F" "0 < a"
    and g: "(g \<longlongrightarrow> 0) F" "eventually (\<lambda>x. 0 < g x) F"
  shows "LIM x F. f x / g x :> at_top"
  unfolding divide_inverse
  by (rule filterlim_tendsto_pos_mult_at_top[OF f]) (rule filterlim_inverse_at_top[OF g])

lemma filterlim_at_top_add_at_top:
  assumes f: "LIM x F. f x :> at_top"
    and g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real
  assume "0 < Z"
  from f have "eventually (\<lambda>x. 0 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma tendsto_divide_0:
  fixes f :: "_ \<Rightarrow> 'a::{real_normed_div_algebra, division_ring}"
  assumes f: "(f \<longlongrightarrow> c) F"
    and g: "LIM x F. g x :> at_infinity"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
  using tendsto_mult[OF f filterlim_compose[OF tendsto_inverse_0 g]]
  by (simp add: divide_inverse)

lemma linear_plus_1_le_power:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from x have "real (Suc n) * x + 1 \<le> (x + 1) * (real n * x + 1)"
    by (simp add: field_simps)
  also have "\<dots> \<le> (x + 1)^Suc n"
    using Suc x by (simp add: mult_left_mono)
  finally show ?case .
qed

lemma filterlim_realpow_sequentially_gt1:
  fixes x :: "'a :: real_normed_div_algebra"
  assumes x[arith]: "1 < norm x"
  shows "LIM n sequentially. x ^ n :> at_infinity"
proof (intro filterlim_at_infinity[THEN iffD2] allI impI)
  fix y :: real
  assume "0 < y"
  obtain N :: nat where "y < real N * (norm x - 1)"
    by (meson diff_gt_0_iff_gt reals_Archimedean3 x)
  also have "\<dots> \<le> real N * (norm x - 1) + 1"
    by simp
  also have "\<dots> \<le> (norm x - 1 + 1) ^ N"
    by (rule linear_plus_1_le_power) simp
  also have "\<dots> = norm x ^ N"
    by simp
  finally have "\<forall>n\<ge>N. y \<le> norm x ^ n"
    by (metis order_less_le_trans power_increasing order_less_imp_le x)
  then show "eventually (\<lambda>n. y \<le> norm (x ^ n)) sequentially"
    unfolding eventually_sequentially
    by (auto simp: norm_power)
qed simp


lemma filterlim_divide_at_infinity:
  fixes f g :: "'a \<Rightarrow> 'a :: real_normed_field"
  assumes "filterlim f (nhds c) F" "filterlim g (at 0) F" "c \<noteq> 0"
  shows   "filterlim (\<lambda>x. f x / g x) at_infinity F"
proof -
  have "filterlim (\<lambda>x. f x * inverse (g x)) at_infinity F"
    by (intro tendsto_mult_filterlim_at_infinity[OF assms(1,3)]
          filterlim_compose [OF filterlim_inverse_at_infinity assms(2)])
  thus ?thesis by (simp add: field_simps)
qed

subsection \<open>Floor and Ceiling\<close>

lemma eventually_floor_less:
  fixes f :: "'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes f: "(f \<longlongrightarrow> l) F"
    and l: "l \<notin> \<int>"
  shows "\<forall>\<^sub>F x in F. of_int (floor l) < f x"
  by (intro order_tendstoD[OF f]) (metis Ints_of_int antisym_conv2 floor_correct l)

lemma eventually_less_ceiling:
  fixes f :: "'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes f: "(f \<longlongrightarrow> l) F"
    and l: "l \<notin> \<int>"
  shows "\<forall>\<^sub>F x in F. f x < of_int (ceiling l)"
  by (intro order_tendstoD[OF f]) (metis Ints_of_int l le_of_int_ceiling less_le)

lemma eventually_floor_eq:
  fixes f::"'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes f: "(f \<longlongrightarrow> l) F"
    and l: "l \<notin> \<int>"
  shows "\<forall>\<^sub>F x in F. floor (f x) = floor l"
  using eventually_floor_less[OF assms] eventually_less_ceiling[OF assms]
  by eventually_elim (meson floor_less_iff less_ceiling_iff not_less_iff_gr_or_eq)

lemma eventually_ceiling_eq:
  fixes f::"'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes f: "(f \<longlongrightarrow> l) F"
    and l: "l \<notin> \<int>"
  shows "\<forall>\<^sub>F x in F. ceiling (f x) = ceiling l"
  using eventually_floor_less[OF assms] eventually_less_ceiling[OF assms]
  by eventually_elim (meson floor_less_iff less_ceiling_iff not_less_iff_gr_or_eq)

lemma tendsto_of_int_floor:
  fixes f::"'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes "(f \<longlongrightarrow> l) F"
    and "l \<notin> \<int>"
  shows "((\<lambda>x. of_int (floor (f x)) :: 'c::{ring_1,topological_space}) \<longlongrightarrow> of_int (floor l)) F"
  using eventually_floor_eq[OF assms]
  by (simp add: eventually_mono topological_tendstoI)

lemma tendsto_of_int_ceiling:
  fixes f::"'a \<Rightarrow> 'b::{order_topology,floor_ceiling}"
  assumes "(f \<longlongrightarrow> l) F"
    and "l \<notin> \<int>"
  shows "((\<lambda>x. of_int (ceiling (f x)):: 'c::{ring_1,topological_space}) \<longlongrightarrow> of_int (ceiling l)) F"
  using eventually_ceiling_eq[OF assms]
  by (simp add: eventually_mono topological_tendstoI)

lemma continuous_on_of_int_floor:
  "continuous_on (UNIV - \<int>::'a::{order_topology, floor_ceiling} set)
    (\<lambda>x. of_int (floor x)::'b::{ring_1, topological_space})"
  unfolding continuous_on_def
  by (auto intro!: tendsto_of_int_floor)

lemma continuous_on_of_int_ceiling:
  "continuous_on (UNIV - \<int>::'a::{order_topology, floor_ceiling} set)
    (\<lambda>x. of_int (ceiling x)::'b::{ring_1, topological_space})"
  unfolding continuous_on_def
  by (auto intro!: tendsto_of_int_ceiling)


subsection \<open>Limits of Sequences\<close>

lemma [trans]: "X = Y \<Longrightarrow> Y \<longlonglongrightarrow> z \<Longrightarrow> X \<longlonglongrightarrow> z"
  by simp

lemma LIMSEQ_iff:
  fixes L :: "'a::real_normed_vector"
  shows "(X \<longlonglongrightarrow> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. norm (X n - L) < r)"
unfolding lim_sequentially dist_norm ..

lemma LIMSEQ_I: "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r) \<Longrightarrow> X \<longlonglongrightarrow> L"
  for L :: "'a::real_normed_vector"
  by (simp add: LIMSEQ_iff)

lemma LIMSEQ_D: "X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
  for L :: "'a::real_normed_vector"
  by (simp add: LIMSEQ_iff)

lemma LIMSEQ_linear: "X \<longlonglongrightarrow> x \<Longrightarrow> l > 0 \<Longrightarrow> (\<lambda> n. X (n * l)) \<longlonglongrightarrow> x"
  unfolding tendsto_def eventually_sequentially
  by (metis div_le_dividend div_mult_self1_is_m le_trans mult.commute)


text \<open>Transformation of limit.\<close>

lemma Lim_transform: "(g \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. f x - g x) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> a) F"
  for a b :: "'a::real_normed_vector"
  using tendsto_add [of g a F "\<lambda>x. f x - g x" 0] by simp

lemma Lim_transform2: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. f x - g x) \<longlongrightarrow> 0) F \<Longrightarrow> (g \<longlongrightarrow> a) F"
  for a b :: "'a::real_normed_vector"
  by (erule Lim_transform) (simp add: tendsto_minus_cancel)

proposition Lim_transform_eq: "((\<lambda>x. f x - g x) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> a) F \<longleftrightarrow> (g \<longlongrightarrow> a) F"
  for a :: "'a::real_normed_vector"
  using Lim_transform Lim_transform2 by blast

lemma Lim_transform_eventually:
  "\<lbrakk>(f \<longlongrightarrow> l) F; eventually (\<lambda>x. f x = g x) F\<rbrakk> \<Longrightarrow> (g \<longlongrightarrow> l) F"
  using eventually_elim2 by (fastforce simp add: tendsto_def)

lemma Lim_transform_within:
  assumes "(f \<longlongrightarrow> l) (at x within S)"
    and "0 < d"
    and "\<And>x'. x'\<in>S \<Longrightarrow> 0 < dist x' x \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x'"
  shows "(g \<longlongrightarrow> l) (at x within S)"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>x. f x = g x) (at x within S)"
    using assms by (auto simp: eventually_at)
  show "(f \<longlongrightarrow> l) (at x within S)"
    by fact
qed

lemma filterlim_transform_within:
  assumes "filterlim g G (at x within S)"
  assumes "G \<le> F" "0<d" "(\<And>x'. x' \<in> S \<Longrightarrow> 0 < dist x' x \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x') "
  shows "filterlim f F (at x within S)"
  using assms
  apply (elim filterlim_mono_eventually)
  unfolding eventually_at by auto

text \<open>Common case assuming being away from some crucial point like 0.\<close>
lemma Lim_transform_away_within:
  fixes a b :: "'a::t1_space"
  assumes "a \<noteq> b"
    and "\<forall>x\<in>S. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
    and "(f \<longlongrightarrow> l) (at a within S)"
  shows "(g \<longlongrightarrow> l) (at a within S)"
proof (rule Lim_transform_eventually)
  show "(f \<longlongrightarrow> l) (at a within S)"
    by fact
  show "eventually (\<lambda>x. f x = g x) (at a within S)"
    unfolding eventually_at_topological
    by (rule exI [where x="- {b}"]) (simp add: open_Compl assms)
qed

lemma Lim_transform_away_at:
  fixes a b :: "'a::t1_space"
  assumes ab: "a \<noteq> b"
    and fg: "\<forall>x. x \<noteq> a \<and> x \<noteq> b \<longrightarrow> f x = g x"
    and fl: "(f \<longlongrightarrow> l) (at a)"
  shows "(g \<longlongrightarrow> l) (at a)"
  using Lim_transform_away_within[OF ab, of UNIV f g l] fg fl by simp

text \<open>Alternatively, within an open set.\<close>
lemma Lim_transform_within_open:
  assumes "(f \<longlongrightarrow> l) (at a within T)"
    and "open s" and "a \<in> s"
    and "\<And>x. x\<in>s \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>x. f x = g x) (at a within T)"
    unfolding eventually_at_topological
    using assms by auto
  show "(f \<longlongrightarrow> l) (at a within T)" by fact
qed


text \<open>A congruence rule allowing us to transform limits assuming not at point.\<close>

lemma Lim_cong_within:
  assumes "a = b"
    and "x = y"
    and "S = T"
    and "\<And>x. x \<noteq> b \<Longrightarrow> x \<in> T \<Longrightarrow> f x = g x"
  shows "(f \<longlongrightarrow> x) (at a within S) \<longleftrightarrow> (g \<longlongrightarrow> y) (at b within T)"
  unfolding tendsto_def eventually_at_topological
  using assms by simp

text \<open>An unbounded sequence's inverse tends to 0.\<close>
lemma LIMSEQ_inverse_zero:
  assumes "\<And>r::real. \<exists>N. \<forall>n\<ge>N. r < X n"
  shows "(\<lambda>n. inverse (X n)) \<longlonglongrightarrow> 0"
  apply (rule filterlim_compose[OF tendsto_inverse_0])
  by (metis assms eventually_at_top_linorderI filterlim_at_top_dense filterlim_at_top_imp_at_infinity)

text \<open>The sequence \<^term>\<open>1/n\<close> tends to 0 as \<^term>\<open>n\<close> tends to infinity.\<close>
lemma LIMSEQ_inverse_real_of_nat: "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
  by (metis filterlim_compose tendsto_inverse_0 filterlim_mono order_refl filterlim_Suc
      filterlim_compose[OF filterlim_real_sequentially] at_top_le_at_infinity)

text \<open>
  The sequence \<^term>\<open>r + 1/n\<close> tends to \<^term>\<open>r\<close> as \<^term>\<open>n\<close> tends to
  infinity is now easily proved.
\<close>

lemma LIMSEQ_inverse_real_of_nat_add: "(\<lambda>n. r + inverse (real (Suc n))) \<longlonglongrightarrow> r"
  using tendsto_add [OF tendsto_const LIMSEQ_inverse_real_of_nat] by auto

lemma LIMSEQ_inverse_real_of_nat_add_minus: "(\<lambda>n. r + -inverse (real (Suc n))) \<longlonglongrightarrow> r"
  using tendsto_add [OF tendsto_const tendsto_minus [OF LIMSEQ_inverse_real_of_nat]]
  by auto

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult: "(\<lambda>n. r * (1 + - inverse (real (Suc n)))) \<longlonglongrightarrow> r"
  using tendsto_mult [OF tendsto_const LIMSEQ_inverse_real_of_nat_add_minus [of 1]]
  by auto

lemma lim_inverse_n: "((\<lambda>n. inverse(of_nat n)) \<longlongrightarrow> (0::'a::real_normed_field)) sequentially"
  using lim_1_over_n by (simp add: inverse_eq_divide)

lemma lim_inverse_n': "((\<lambda>n. 1 / n) \<longlongrightarrow> 0) sequentially"
  using lim_inverse_n
  by (simp add: inverse_eq_divide)

lemma LIMSEQ_Suc_n_over_n: "(\<lambda>n. of_nat (Suc n) / of_nat n :: 'a :: real_normed_field) \<longlonglongrightarrow> 1"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>n. 1 + inverse (of_nat n :: 'a) = of_nat (Suc n) / of_nat n) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by eventually_elim (simp add: field_simps)
  have "(\<lambda>n. 1 + inverse (of_nat n) :: 'a) \<longlonglongrightarrow> 1 + 0"
    by (intro tendsto_add tendsto_const lim_inverse_n)
  then show "(\<lambda>n. 1 + inverse (of_nat n) :: 'a) \<longlonglongrightarrow> 1"
    by simp
qed

lemma LIMSEQ_n_over_Suc_n: "(\<lambda>n. of_nat n / of_nat (Suc n) :: 'a :: real_normed_field) \<longlonglongrightarrow> 1"
proof (rule Lim_transform_eventually)
  show "eventually (\<lambda>n. inverse (of_nat (Suc n) / of_nat n :: 'a) =
      of_nat n / of_nat (Suc n)) sequentially"
    using eventually_gt_at_top[of "0::nat"]
    by eventually_elim (simp add: field_simps del: of_nat_Suc)
  have "(\<lambda>n. inverse (of_nat (Suc n) / of_nat n :: 'a)) \<longlonglongrightarrow> inverse 1"
    by (intro tendsto_inverse LIMSEQ_Suc_n_over_n) simp_all
  then show "(\<lambda>n. inverse (of_nat (Suc n) / of_nat n :: 'a)) \<longlonglongrightarrow> 1"
    by simp
qed


subsection \<open>Convergence on sequences\<close>

lemma convergent_cong:
  assumes "eventually (\<lambda>x. f x = g x) sequentially"
  shows "convergent f \<longleftrightarrow> convergent g"
  unfolding convergent_def
  by (subst filterlim_cong[OF refl refl assms]) (rule refl)

lemma convergent_Suc_iff: "convergent (\<lambda>n. f (Suc n)) \<longleftrightarrow> convergent f"
  by (auto simp: convergent_def filterlim_sequentially_Suc)

lemma convergent_ignore_initial_segment: "convergent (\<lambda>n. f (n + m)) = convergent f"
proof (induct m arbitrary: f)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have "convergent (\<lambda>n. f (n + Suc m)) \<longleftrightarrow> convergent (\<lambda>n. f (Suc n + m))"
    by simp
  also have "\<dots> \<longleftrightarrow> convergent (\<lambda>n. f (n + m))"
    by (rule convergent_Suc_iff)
  also have "\<dots> \<longleftrightarrow> convergent f"
    by (rule Suc)
  finally show ?case .
qed

lemma convergent_add:
  fixes X Y :: "nat \<Rightarrow> 'a::topological_monoid_add"
  assumes "convergent (\<lambda>n. X n)"
    and "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n + Y n)"
  using assms unfolding convergent_def by (blast intro: tendsto_add)

lemma convergent_sum:
  fixes X :: "'a \<Rightarrow> nat \<Rightarrow> 'b::topological_comm_monoid_add"
  shows "(\<And>i. i \<in> A \<Longrightarrow> convergent (\<lambda>n. X i n)) \<Longrightarrow> convergent (\<lambda>n. \<Sum>i\<in>A. X i n)"
  by (induct A rule: infinite_finite_induct) (simp_all add: convergent_const convergent_add)

lemma (in bounded_linear) convergent:
  assumes "convergent (\<lambda>n. X n)"
  shows "convergent (\<lambda>n. f (X n))"
  using assms unfolding convergent_def by (blast intro: tendsto)

lemma (in bounded_bilinear) convergent:
  assumes "convergent (\<lambda>n. X n)"
    and "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n ** Y n)"
  using assms unfolding convergent_def by (blast intro: tendsto)

lemma convergent_minus_iff:
  fixes X :: "nat \<Rightarrow> 'a::topological_group_add"
  shows "convergent X \<longleftrightarrow> convergent (\<lambda>n. - X n)"
  unfolding convergent_def by (force dest: tendsto_minus)

lemma convergent_diff:
  fixes X Y :: "nat \<Rightarrow> 'a::topological_group_add"
  assumes "convergent (\<lambda>n. X n)"
  assumes "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n - Y n)"
  using assms unfolding convergent_def by (blast intro: tendsto_diff)

lemma convergent_norm:
  assumes "convergent f"
  shows "convergent (\<lambda>n. norm (f n))"
proof -
  from assms have "f \<longlonglongrightarrow> lim f"
    by (simp add: convergent_LIMSEQ_iff)
  then have "(\<lambda>n. norm (f n)) \<longlonglongrightarrow> norm (lim f)"
    by (rule tendsto_norm)
  then show ?thesis
    by (auto simp: convergent_def)
qed

lemma convergent_of_real:
  "convergent f \<Longrightarrow> convergent (\<lambda>n. of_real (f n) :: 'a::real_normed_algebra_1)"
  unfolding convergent_def by (blast intro!: tendsto_of_real)

lemma convergent_add_const_iff:
  "convergent (\<lambda>n. c + f n :: 'a::topological_ab_group_add) \<longleftrightarrow> convergent f"
proof
  assume "convergent (\<lambda>n. c + f n)"
  from convergent_diff[OF this convergent_const[of c]] show "convergent f"
    by simp
next
  assume "convergent f"
  from convergent_add[OF convergent_const[of c] this] show "convergent (\<lambda>n. c + f n)"
    by simp
qed

lemma convergent_add_const_right_iff:
  "convergent (\<lambda>n. f n + c :: 'a::topological_ab_group_add) \<longleftrightarrow> convergent f"
  using convergent_add_const_iff[of c f] by (simp add: add_ac)

lemma convergent_diff_const_right_iff:
  "convergent (\<lambda>n. f n - c :: 'a::topological_ab_group_add) \<longleftrightarrow> convergent f"
  using convergent_add_const_right_iff[of f "-c"] by (simp add: add_ac)

lemma convergent_mult:
  fixes X Y :: "nat \<Rightarrow> 'a::topological_semigroup_mult"
  assumes "convergent (\<lambda>n. X n)"
    and "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n * Y n)"
  using assms unfolding convergent_def by (blast intro: tendsto_mult)

lemma convergent_mult_const_iff:
  assumes "c \<noteq> 0"
  shows "convergent (\<lambda>n. c * f n :: 'a::{field,topological_semigroup_mult}) \<longleftrightarrow> convergent f"
proof
  assume "convergent (\<lambda>n. c * f n)"
  from assms convergent_mult[OF this convergent_const[of "inverse c"]]
    show "convergent f" by (simp add: field_simps)
next
  assume "convergent f"
  from convergent_mult[OF convergent_const[of c] this] show "convergent (\<lambda>n. c * f n)"
    by simp
qed

lemma convergent_mult_const_right_iff:
  fixes c :: "'a::{field,topological_semigroup_mult}"
  assumes "c \<noteq> 0"
  shows "convergent (\<lambda>n. f n * c) \<longleftrightarrow> convergent f"
  using convergent_mult_const_iff[OF assms, of f] by (simp add: mult_ac)

lemma convergent_imp_Bseq: "convergent f \<Longrightarrow> Bseq f"
  by (simp add: Cauchy_Bseq convergent_Cauchy)


text \<open>A monotone sequence converges to its least upper bound.\<close>

lemma LIMSEQ_incseq_SUP:
  fixes X :: "nat \<Rightarrow> 'a::{conditionally_complete_linorder,linorder_topology}"
  assumes u: "bdd_above (range X)"
    and X: "incseq X"
  shows "X \<longlonglongrightarrow> (SUP i. X i)"
  by (rule order_tendstoI)
    (auto simp: eventually_sequentially u less_cSUP_iff
      intro: X[THEN incseqD] less_le_trans cSUP_lessD[OF u])

lemma LIMSEQ_decseq_INF:
  fixes X :: "nat \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology}"
  assumes u: "bdd_below (range X)"
    and X: "decseq X"
  shows "X \<longlonglongrightarrow> (INF i. X i)"
  by (rule order_tendstoI)
     (auto simp: eventually_sequentially u cINF_less_iff
       intro: X[THEN decseqD] le_less_trans less_cINF_D[OF u])

text \<open>Main monotonicity theorem.\<close>

lemma Bseq_monoseq_convergent: "Bseq X \<Longrightarrow> monoseq X \<Longrightarrow> convergent X"
  for X :: "nat \<Rightarrow> real"
  by (auto simp: monoseq_iff convergent_def intro: LIMSEQ_decseq_INF LIMSEQ_incseq_SUP
      dest: Bseq_bdd_above Bseq_bdd_below)

lemma Bseq_mono_convergent: "Bseq X \<Longrightarrow> (\<forall>m n. m \<le> n \<longrightarrow> X m \<le> X n) \<Longrightarrow> convergent X"
  for X :: "nat \<Rightarrow> real"
  by (auto intro!: Bseq_monoseq_convergent incseq_imp_monoseq simp: incseq_def)

lemma monoseq_imp_convergent_iff_Bseq: "monoseq f \<Longrightarrow> convergent f \<longleftrightarrow> Bseq f"
  for f :: "nat \<Rightarrow> real"
  using Bseq_monoseq_convergent[of f] convergent_imp_Bseq[of f] by blast

lemma Bseq_monoseq_convergent'_inc:
  fixes f :: "nat \<Rightarrow> real"
  shows "Bseq (\<lambda>n. f (n + M)) \<Longrightarrow> (\<And>m n. M \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> f m \<le> f n) \<Longrightarrow> convergent f"
  by (subst convergent_ignore_initial_segment [symmetric, of _ M])
     (auto intro!: Bseq_monoseq_convergent simp: monoseq_def)

lemma Bseq_monoseq_convergent'_dec:
  fixes f :: "nat \<Rightarrow> real"
  shows "Bseq (\<lambda>n. f (n + M)) \<Longrightarrow> (\<And>m n. M \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> f m \<ge> f n) \<Longrightarrow> convergent f"
  by (subst convergent_ignore_initial_segment [symmetric, of _ M])
    (auto intro!: Bseq_monoseq_convergent simp: monoseq_def)

lemma Cauchy_iff: "Cauchy X \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e)"
  for X :: "nat \<Rightarrow> 'a::real_normed_vector"
  unfolding Cauchy_def dist_norm ..

lemma CauchyI: "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e) \<Longrightarrow> Cauchy X"
  for X :: "nat \<Rightarrow> 'a::real_normed_vector"
  by (simp add: Cauchy_iff)

lemma CauchyD: "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e"
  for X :: "nat \<Rightarrow> 'a::real_normed_vector"
  by (simp add: Cauchy_iff)

lemma incseq_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes "incseq X"
    and "\<forall>i. X i \<le> B"
  obtains L where "X \<longlonglongrightarrow> L" "\<forall>i. X i \<le> L"
proof atomize_elim
  from incseq_bounded[OF assms] \<open>incseq X\<close> Bseq_monoseq_convergent[of X]
  obtain L where "X \<longlonglongrightarrow> L"
    by (auto simp: convergent_def monoseq_def incseq_def)
  with \<open>incseq X\<close> show "\<exists>L. X \<longlonglongrightarrow> L \<and> (\<forall>i. X i \<le> L)"
    by (auto intro!: exI[of _ L] incseq_le)
qed

lemma decseq_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes "decseq X"
    and "\<forall>i. B \<le> X i"
  obtains L where "X \<longlonglongrightarrow> L" "\<forall>i. L \<le> X i"
proof atomize_elim
  from decseq_bounded[OF assms] \<open>decseq X\<close> Bseq_monoseq_convergent[of X]
  obtain L where "X \<longlonglongrightarrow> L"
    by (auto simp: convergent_def monoseq_def decseq_def)
  with \<open>decseq X\<close> show "\<exists>L. X \<longlonglongrightarrow> L \<and> (\<forall>i. L \<le> X i)"
    by (auto intro!: exI[of _ L] decseq_ge)
qed

lemma monoseq_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "monoseq X" and B: "\<And>i. \<bar>X i\<bar> \<le> B"
  obtains L where "X \<longlonglongrightarrow> L"
  using X unfolding monoseq_iff
proof
  assume "incseq X"
  show thesis
    using abs_le_D1 [OF B] incseq_convergent [OF \<open>incseq X\<close>] that by meson
next
  assume "decseq X"
  show thesis
    using decseq_convergent [OF \<open>decseq X\<close>] that
    by (metis B abs_le_iff add.inverse_inverse neg_le_iff_le)
qed

subsection \<open>Power Sequences\<close>

lemma Bseq_realpow: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> Bseq (\<lambda>n. x ^ n)"
  for x :: real
  by (metis decseq_bounded decseq_def power_decreasing zero_le_power)

lemma monoseq_realpow: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> monoseq (\<lambda>n. x ^ n)"
  for x :: real
  using monoseq_def power_decreasing by blast

lemma convergent_realpow: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> convergent (\<lambda>n. x ^ n)"
  for x :: real
  by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

lemma LIMSEQ_inverse_realpow_zero: "1 < x \<Longrightarrow> (\<lambda>n. inverse (x ^ n)) \<longlonglongrightarrow> 0"
  for x :: real
  by (rule filterlim_compose[OF tendsto_inverse_0 filterlim_realpow_sequentially_gt1]) simp

lemma LIMSEQ_realpow_zero:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "(\<lambda>n. x ^ n) \<longlonglongrightarrow> 0"
proof (cases "x = 0")
  case False
  with \<open>0 \<le> x\<close> have x0: "0 < x" by simp
  then have "1 < inverse x"
    using \<open>x < 1\<close> by (rule one_less_inverse)
  then have "(\<lambda>n. inverse (inverse x ^ n)) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_inverse_realpow_zero)
  then show ?thesis by (simp add: power_inverse)
next
  case True
  show ?thesis
    by (rule LIMSEQ_imp_Suc) (simp add: True)
qed

lemma LIMSEQ_power_zero [tendsto_intros]: "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) \<longlonglongrightarrow> 0"
  for x :: "'a::real_normed_algebra_1"
  apply (drule LIMSEQ_realpow_zero [OF norm_ge_zero])
  by (simp add: Zfun_le norm_power_ineq tendsto_Zfun_iff)

lemma LIMSEQ_divide_realpow_zero: "1 < x \<Longrightarrow> (\<lambda>n. a / (x ^ n) :: real) \<longlonglongrightarrow> 0"
  by (rule tendsto_divide_0 [OF tendsto_const filterlim_realpow_sequentially_gt1]) simp

lemma
  tendsto_power_zero:
  fixes x::"'a::real_normed_algebra_1"
  assumes "filterlim f at_top F"
  assumes "norm x < 1"
  shows "((\<lambda>y. x ^ (f y)) \<longlongrightarrow> 0) F"
proof (rule tendstoI)
  fix e::real assume "0 < e"
  from tendstoD[OF LIMSEQ_power_zero[OF \<open>norm x < 1\<close>] \<open>0 < e\<close>]
  have "\<forall>\<^sub>F xa in sequentially. norm (x ^ xa) < e"
    by simp
  then obtain N where N: "norm (x ^ n) < e" if "n \<ge> N" for n
    by (auto simp: eventually_sequentially)
  have "\<forall>\<^sub>F i in F. f i \<ge> N"
    using \<open>filterlim f sequentially F\<close>
    by (simp add: filterlim_at_top)
  then show "\<forall>\<^sub>F i in F. dist (x ^ f i) 0 < e"
    by eventually_elim (auto simp: N)
qed

text \<open>Limit of \<^term>\<open>c^n\<close> for \<^term>\<open>\<bar>c\<bar> < 1\<close>.\<close>

lemma LIMSEQ_abs_realpow_zero: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. \<bar>c\<bar> ^ n :: real) \<longlonglongrightarrow> 0"
  by (rule LIMSEQ_realpow_zero [OF abs_ge_zero])

lemma LIMSEQ_abs_realpow_zero2: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. c ^ n :: real) \<longlonglongrightarrow> 0"
  by (rule LIMSEQ_power_zero) simp


subsection \<open>Limits of Functions\<close>

lemma LIM_eq: "f \<midarrow>a\<rightarrow> L = (\<forall>r>0. \<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r)"
  for a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  by (simp add: LIM_def dist_norm)

lemma LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r) \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  by (simp add: LIM_eq)

lemma LIM_D: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>s>0.\<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r"
  for a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  by (simp add: LIM_eq)

lemma LIM_offset: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> (\<lambda>x. f (x + k)) \<midarrow>(a - k)\<rightarrow> L"
  for a :: "'a::real_normed_vector"
  by (simp add: filtermap_at_shift[symmetric, of a k] filterlim_def filtermap_filtermap)

lemma LIM_offset_zero: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> (\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow> L"
  for a :: "'a::real_normed_vector"
  by (drule LIM_offset [where k = a]) (simp add: add.commute)

lemma LIM_offset_zero_cancel: "(\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow> L \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::real_normed_vector"
  by (drule LIM_offset [where k = "- a"]) simp

lemma LIM_offset_zero_iff: "NO_MATCH 0 a \<Longrightarrow> f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow> L"
  for f :: "'a :: real_normed_vector \<Rightarrow> _"
  using LIM_offset_zero_cancel[of f a L] LIM_offset_zero[of f L a] by auto

lemma tendsto_offset_zero_iff:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> _"
  assumes " NO_MATCH 0 a" "a \<in> S" "open S"
  shows "(f \<longlongrightarrow> L) (at a within S) \<longleftrightarrow> ((\<lambda>h. f (a + h)) \<longlongrightarrow> L) (at 0)"
  using assms by (simp add: tendsto_within_open_NO_MATCH LIM_offset_zero_iff)

lemma LIM_zero: "(f \<longlongrightarrow> l) F \<Longrightarrow> ((\<lambda>x. f x - l) \<longlongrightarrow> 0) F"
  for f :: "'a \<Rightarrow> 'b::real_normed_vector"
  unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_cancel:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "((\<lambda>x. f x - l) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> l) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_iff: "((\<lambda>x. f x - l) \<longlongrightarrow> 0) F = (f \<longlongrightarrow> l) F"
  for f :: "'a \<Rightarrow> 'b::real_normed_vector"
  unfolding tendsto_iff dist_norm by simp

lemma LIM_imp_LIM:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'a::topological_space \<Rightarrow> 'c::real_normed_vector"
  assumes f: "f \<midarrow>a\<rightarrow> l"
    and le: "\<And>x. x \<noteq> a \<Longrightarrow> norm (g x - m) \<le> norm (f x - l)"
  shows "g \<midarrow>a\<rightarrow> m"
  by (rule metric_LIM_imp_LIM [OF f]) (simp add: dist_norm le)

lemma LIM_equal2:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  assumes "0 < R"
    and "\<And>x. x \<noteq> a \<Longrightarrow> norm (x - a) < R \<Longrightarrow> f x = g x"
  shows "g \<midarrow>a\<rightarrow> l \<Longrightarrow> f \<midarrow>a\<rightarrow> l"
  by (rule metric_LIM_equal2 [OF _ assms]) (simp_all add: dist_norm)

lemma LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f: "f \<midarrow>a\<rightarrow> b"
    and g: "g \<midarrow>b\<rightarrow> c"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c"
  by (rule metric_LIM_compose2 [OF f g inj [folded dist_norm]])

lemma real_LIM_sandwich_zero:
  fixes f g :: "'a::topological_space \<Rightarrow> real"
  assumes f: "f \<midarrow>a\<rightarrow> 0"
    and 1: "\<And>x. x \<noteq> a \<Longrightarrow> 0 \<le> g x"
    and 2: "\<And>x. x \<noteq> a \<Longrightarrow> g x \<le> f x"
  shows "g \<midarrow>a\<rightarrow> 0"
proof (rule LIM_imp_LIM [OF f]) (* FIXME: use tendsto_sandwich *)
  fix x
  assume x: "x \<noteq> a"
  with 1 have "norm (g x - 0) = g x" by simp
  also have "g x \<le> f x" by (rule 2 [OF x])
  also have "f x \<le> \<bar>f x\<bar>" by (rule abs_ge_self)
  also have "\<bar>f x\<bar> = norm (f x - 0)" by simp
  finally show "norm (g x - 0) \<le> norm (f x - 0)" .
qed


subsection \<open>Continuity\<close>

lemma LIM_isCont_iff: "(f \<midarrow>a\<rightarrow> f a) = ((\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow> f a)"
  for f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff: "isCont f x = (\<lambda>h. f (x + h)) \<midarrow>0\<rightarrow> f x"
  for f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f [unfolded isCont_def]: "isCont f a"
    and g: "g \<midarrow>f a\<rightarrow> l"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> l"
  by (rule LIM_compose2 [OF f g inj])

lemma isCont_norm [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. norm (f x)) a"
  for f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  by (fact continuous_norm)

lemma isCont_rabs [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. \<bar>f x\<bar>) a"
  for f :: "'a::t2_space \<Rightarrow> real"
  by (fact continuous_rabs)

lemma isCont_add [simp]: "isCont f a \<Longrightarrow> isCont g a \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
  for f :: "'a::t2_space \<Rightarrow> 'b::topological_monoid_add"
  by (fact continuous_add)

lemma isCont_minus [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
  for f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  by (fact continuous_minus)

lemma isCont_diff [simp]: "isCont f a \<Longrightarrow> isCont g a \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
  for f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  by (fact continuous_diff)

lemma isCont_mult [simp]: "isCont f a \<Longrightarrow> isCont g a \<Longrightarrow> isCont (\<lambda>x. f x * g x) a"
  for f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_algebra"
  by (fact continuous_mult)

lemma (in bounded_linear) isCont: "isCont g a \<Longrightarrow> isCont (\<lambda>x. f (g x)) a"
  by (fact continuous)

lemma (in bounded_bilinear) isCont: "isCont f a \<Longrightarrow> isCont g a \<Longrightarrow> isCont (\<lambda>x. f x ** g x) a"
  by (fact continuous)

lemmas isCont_scaleR [simp] =
  bounded_bilinear.isCont [OF bounded_bilinear_scaleR]

lemmas isCont_of_real [simp] =
  bounded_linear.isCont [OF bounded_linear_of_real]

lemma isCont_power [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x ^ n) a"
  for f :: "'a::t2_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  by (fact continuous_power)

lemma isCont_sum [simp]: "\<forall>i\<in>A. isCont (f i) a \<Longrightarrow> isCont (\<lambda>x. \<Sum>i\<in>A. f i x) a"
  for f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::topological_comm_monoid_add"
  by (auto intro: continuous_sum)


subsection \<open>Uniform Continuity\<close>

lemma uniformly_continuous_on_def:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows "uniformly_continuous_on s f \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  unfolding uniformly_continuous_on_uniformity
    uniformity_dist filterlim_INF filterlim_principal eventually_inf_principal
  by (force simp: Ball_def uniformity_dist[symmetric] eventually_uniformity_metric)

abbreviation isUCont :: "['a::metric_space \<Rightarrow> 'b::metric_space] \<Rightarrow> bool"
  where "isUCont f \<equiv> uniformly_continuous_on UNIV f"

lemma isUCont_def: "isUCont f \<longleftrightarrow> (\<forall>r>0. \<exists>s>0. \<forall>x y. dist x y < s \<longrightarrow> dist (f x) (f y) < r)"
  by (auto simp: uniformly_continuous_on_def dist_commute)

lemma isUCont_isCont: "isUCont f \<Longrightarrow> isCont f x"
  by (drule uniformly_continuous_imp_continuous) (simp add: continuous_on_eq_continuous_at)

lemma uniformly_continuous_on_Cauchy:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "uniformly_continuous_on S f" "Cauchy X" "\<And>n. X n \<in> S"
  shows "Cauchy (\<lambda>n. f (X n))"
  using assms
  unfolding uniformly_continuous_on_def  by (meson Cauchy_def)

lemma isUCont_Cauchy: "isUCont f \<Longrightarrow> Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
  by (rule uniformly_continuous_on_Cauchy[where S=UNIV and f=f]) simp_all

lemma uniformly_continuous_imp_Cauchy_continuous:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows "\<lbrakk>uniformly_continuous_on S f; Cauchy \<sigma>; \<And>n. (\<sigma> n) \<in> S\<rbrakk> \<Longrightarrow> Cauchy(f \<circ> \<sigma>)"
  by (simp add: uniformly_continuous_on_def Cauchy_def) meson

lemma (in bounded_linear) isUCont: "isUCont f"
  unfolding isUCont_def dist_norm
proof (intro allI impI)
  fix r :: real
  assume r: "0 < r"
  obtain K where K: "0 < K" and norm_le: "norm (f x) \<le> norm x * K" for x
    using pos_bounded by blast
  show "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
  proof (rule exI, safe)
    from r K show "0 < r / K" by simp
  next
    fix x y :: 'a
    assume xy: "norm (x - y) < r / K"
    have "norm (f x - f y) = norm (f (x - y))" by (simp only: diff)
    also have "\<dots> \<le> norm (x - y) * K" by (rule norm_le)
    also from K xy have "\<dots> < r" by (simp only: pos_less_divide_eq)
    finally show "norm (f x - f y) < r" .
  qed
qed

lemma (in bounded_linear) Cauchy: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
  by (rule isUCont [THEN isUCont_Cauchy])

lemma LIM_less_bound:
  fixes f :: "real \<Rightarrow> real"
  assumes ev: "b < x" "\<forall> x' \<in> { b <..< x}. 0 \<le> f x'" and "isCont f x"
  shows "0 \<le> f x"
proof (rule tendsto_lowerbound)
  show "(f \<longlongrightarrow> f x) (at_left x)"
    using \<open>isCont f x\<close> by (simp add: filterlim_at_split isCont_def)
  show "eventually (\<lambda>x. 0 \<le> f x) (at_left x)"
    using ev by (auto simp: eventually_at dist_real_def intro!: exI[of _ "x - b"])
qed simp


subsection \<open>Nested Intervals and Bisection -- Needed for Compactness\<close>

lemma nested_sequence_unique:
  assumes "\<forall>n. f n \<le> f (Suc n)" "\<forall>n. g (Suc n) \<le> g n" "\<forall>n. f n \<le> g n" "(\<lambda>n. f n - g n) \<longlonglongrightarrow> 0"
  shows "\<exists>l::real. ((\<forall>n. f n \<le> l) \<and> f \<longlonglongrightarrow> l) \<and> ((\<forall>n. l \<le> g n) \<and> g \<longlonglongrightarrow> l)"
proof -
  have "incseq f" unfolding incseq_Suc_iff by fact
  have "decseq g" unfolding decseq_Suc_iff by fact
  have "f n \<le> g 0" for n
  proof -
    from \<open>decseq g\<close> have "g n \<le> g 0"
      by (rule decseqD) simp
    with \<open>\<forall>n. f n \<le> g n\<close>[THEN spec, of n] show ?thesis
      by auto
  qed
  then obtain u where "f \<longlonglongrightarrow> u" "\<forall>i. f i \<le> u"
    using incseq_convergent[OF \<open>incseq f\<close>] by auto
  moreover have "f 0 \<le> g n" for n
  proof -
    from \<open>incseq f\<close> have "f 0 \<le> f n" by (rule incseqD) simp
    with \<open>\<forall>n. f n \<le> g n\<close>[THEN spec, of n] show ?thesis
      by simp
  qed
  then obtain l where "g \<longlonglongrightarrow> l" "\<forall>i. l \<le> g i"
    using decseq_convergent[OF \<open>decseq g\<close>] by auto
  moreover note LIMSEQ_unique[OF assms(4) tendsto_diff[OF \<open>f \<longlonglongrightarrow> u\<close> \<open>g \<longlonglongrightarrow> l\<close>]]
  ultimately show ?thesis by auto
qed

lemma Bolzano[consumes 1, case_names trans local]:
  fixes P :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes [arith]: "a \<le> b"
    and trans: "\<And>a b c. P a b \<Longrightarrow> P b c \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> P a c"
    and local: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<exists>d>0. \<forall>a b. a \<le> x \<and> x \<le> b \<and> b - a < d \<longrightarrow> P a b"
  shows "P a b"
proof -
  define bisect where "bisect =
    rec_nat (a, b) (\<lambda>n (x, y). if P x ((x+y) / 2) then ((x+y)/2, y) else (x, (x+y)/2))"
  define l u where "l n = fst (bisect n)" and "u n = snd (bisect n)" for n
  have l[simp]: "l 0 = a" "\<And>n. l (Suc n) = (if P (l n) ((l n + u n) / 2) then (l n + u n) / 2 else l n)"
    and u[simp]: "u 0 = b" "\<And>n. u (Suc n) = (if P (l n) ((l n + u n) / 2) then u n else (l n + u n) / 2)"
    by (simp_all add: l_def u_def bisect_def split: prod.split)

  have [simp]: "l n \<le> u n" for n by (induct n) auto

  have "\<exists>x. ((\<forall>n. l n \<le> x) \<and> l \<longlonglongrightarrow> x) \<and> ((\<forall>n. x \<le> u n) \<and> u \<longlonglongrightarrow> x)"
  proof (safe intro!: nested_sequence_unique)
    show "l n \<le> l (Suc n)" "u (Suc n) \<le> u n" for n
      by (induct n) auto
  next
    have "l n - u n = (a - b) / 2^n" for n
      by (induct n) (auto simp: field_simps)
    then show "(\<lambda>n. l n - u n) \<longlonglongrightarrow> 0"
      by (simp add: LIMSEQ_divide_realpow_zero)
  qed fact
  then obtain x where x: "\<And>n. l n \<le> x" "\<And>n. x \<le> u n" and "l \<longlonglongrightarrow> x" "u \<longlonglongrightarrow> x"
    by auto
  obtain d where "0 < d" and d: "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> b - a < d \<Longrightarrow> P a b" for a b
    using \<open>l 0 \<le> x\<close> \<open>x \<le> u 0\<close> local[of x] by auto

  show "P a b"
  proof (rule ccontr)
    assume "\<not> P a b"
    have "\<not> P (l n) (u n)" for n
    proof (induct n)
      case 0
      then show ?case
        by (simp add: \<open>\<not> P a b\<close>)
    next
      case (Suc n)
      with trans[of "l n" "(l n + u n) / 2" "u n"] show ?case
        by auto
    qed
    moreover
    {
      have "eventually (\<lambda>n. x - d / 2 < l n) sequentially"
        using \<open>0 < d\<close> \<open>l \<longlonglongrightarrow> x\<close> by (intro order_tendstoD[of _ x]) auto
      moreover have "eventually (\<lambda>n. u n < x + d / 2) sequentially"
        using \<open>0 < d\<close> \<open>u \<longlonglongrightarrow> x\<close> by (intro order_tendstoD[of _ x]) auto
      ultimately have "eventually (\<lambda>n. P (l n) (u n)) sequentially"
      proof eventually_elim
        case (elim n)
        from add_strict_mono[OF this] have "u n - l n < d" by simp
        with x show "P (l n) (u n)" by (rule d)
      qed
    }
    ultimately show False by simp
  qed
qed

lemma compact_Icc[simp, intro]: "compact {a .. b::real}"
proof (cases "a \<le> b", rule compactI)
  fix C
  assume C: "a \<le> b" "\<forall>t\<in>C. open t" "{a..b} \<subseteq> \<Union>C"
  define T where "T = {a .. b}"
  from C(1,3) show "\<exists>C'\<subseteq>C. finite C' \<and> {a..b} \<subseteq> \<Union>C'"
  proof (induct rule: Bolzano)
    case (trans a b c)
    then have *: "{a..c} = {a..b} \<union> {b..c}"
      by auto
    with trans obtain C1 C2
      where "C1\<subseteq>C" "finite C1" "{a..b} \<subseteq> \<Union>C1" "C2\<subseteq>C" "finite C2" "{b..c} \<subseteq> \<Union>C2"
      by auto
    with trans show ?case
      unfolding * by (intro exI[of _ "C1 \<union> C2"]) auto
  next
    case (local x)
    with C have "x \<in> \<Union>C" by auto
    with C(2) obtain c where "x \<in> c" "open c" "c \<in> C"
      by auto
    then obtain e where "0 < e" "{x - e <..< x + e} \<subseteq> c"
      by (auto simp: open_dist dist_real_def subset_eq Ball_def abs_less_iff)
    with \<open>c \<in> C\<close> show ?case
      by (safe intro!: exI[of _ "e/2"] exI[of _ "{c}"]) auto
  qed
qed simp


lemma continuous_image_closed_interval:
  fixes a b and f :: "real \<Rightarrow> real"
  defines "S \<equiv> {a..b}"
  assumes "a \<le> b" and f: "continuous_on S f"
  shows "\<exists>c d. f`S = {c..d} \<and> c \<le> d"
proof -
  have S: "compact S" "S \<noteq> {}"
    using \<open>a \<le> b\<close> by (auto simp: S_def)
  obtain c where "c \<in> S" "\<forall>d\<in>S. f d \<le> f c"
    using continuous_attains_sup[OF S f] by auto
  moreover obtain d where "d \<in> S" "\<forall>c\<in>S. f d \<le> f c"
    using continuous_attains_inf[OF S f] by auto
  moreover have "connected (f`S)"
    using connected_continuous_image[OF f] connected_Icc by (auto simp: S_def)
  ultimately have "f ` S = {f d .. f c} \<and> f d \<le> f c"
    by (auto simp: connected_iff_interval)
  then show ?thesis
    by auto
qed

lemma open_Collect_positive:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes f: "continuous_on s f"
  shows "\<exists>A. open A \<and> A \<inter> s = {x\<in>s. 0 < f x}"
  using continuous_on_open_invariant[THEN iffD1, OF f, rule_format, of "{0 <..}"]
  by (auto simp: Int_def field_simps)

lemma open_Collect_less_Int:
  fixes f g :: "'a::topological_space \<Rightarrow> real"
  assumes f: "continuous_on s f"
    and g: "continuous_on s g"
  shows "\<exists>A. open A \<and> A \<inter> s = {x\<in>s. f x < g x}"
  using open_Collect_positive[OF continuous_on_diff[OF g f]] by (simp add: field_simps)


subsection \<open>Boundedness of continuous functions\<close>

text\<open>By bisection, function continuous on closed interval is bounded above\<close>

lemma isCont_eq_Ub:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_sup[of "{a..b}" f]
  by (auto simp: continuous_at_imp_continuous_on Ball_def Bex_def)

lemma isCont_eq_Lb:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> M \<le> f x) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_inf[of "{a..b}" f]
  by (auto simp: continuous_at_imp_continuous_on Ball_def Bex_def)

lemma isCont_bounded:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow> \<exists>M. \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M"
  using isCont_eq_Ub[of a b f] by auto

lemma isCont_has_Ub:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M) \<and> (\<forall>N. N < M \<longrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> N < f x))"
  using isCont_eq_Ub[of a b f] by auto

lemma isCont_Lb_Ub:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
  shows "\<exists>L M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x \<and> f x \<le> M) \<and>
    (\<forall>y. L \<le> y \<and> y \<le> M \<longrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> (f x = y)))"
proof -
  obtain M where M: "a \<le> M" "M \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> f M"
    using isCont_eq_Ub[OF assms] by auto
  obtain L where L: "a \<le> L" "L \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f L \<le> f x"
    using isCont_eq_Lb[OF assms] by auto
  have "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f L \<le> f x \<and> f x \<le> f M)"
    using M L by simp
  moreover
  have "(\<forall>y. f L \<le> y \<and> y \<le> f M \<longrightarrow> (\<exists>x\<ge>a. x \<le> b \<and> f x = y))"
  proof (cases "L \<le> M")
    case True then show ?thesis
    using IVT[of f L _ M] M L assms by (metis order.trans)
  next
    case False then show ?thesis
    using IVT2[of f L _ M]
    by (metis L(2) M(1) assms(2) le_cases order.trans)
qed
  ultimately show ?thesis
    by blast
qed


text \<open>Continuity of inverse function.\<close>

lemma isCont_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes d: "0 < d"
    and inj: "\<And>z. \<bar>z-x\<bar> \<le> d \<Longrightarrow> g (f z) = z"
    and cont: "\<And>z. \<bar>z-x\<bar> \<le> d \<Longrightarrow> isCont f z"
  shows "isCont g (f x)"
proof -
  let ?A = "f (x - d)"
  let ?B = "f (x + d)"
  let ?D = "{x - d..x + d}"

  have f: "continuous_on ?D f"
    using cont by (intro continuous_at_imp_continuous_on ballI) auto
  then have g: "continuous_on (f`?D) g"
    using inj by (intro continuous_on_inv) auto

  from d f have "{min ?A ?B <..< max ?A ?B} \<subseteq> f ` ?D"
    by (intro connected_contains_Ioo connected_continuous_image) (auto split: split_min split_max)
  with g have "continuous_on {min ?A ?B <..< max ?A ?B} g"
    by (rule continuous_on_subset)
  moreover
  have "(?A < f x \<and> f x < ?B) \<or> (?B < f x \<and> f x < ?A)"
    using d inj by (intro continuous_inj_imp_mono[OF _ _ f] inj_on_imageI2[of g, OF inj_onI]) auto
  then have "f x \<in> {min ?A ?B <..< max ?A ?B}"
    by auto
  ultimately show ?thesis
    by (simp add: continuous_on_eq_continuous_at)
qed

lemma isCont_inverse_function2:
  fixes f g :: "real \<Rightarrow> real"
  shows
    "\<lbrakk>a < x; x < b;
      \<And>z. \<lbrakk>a \<le> z; z \<le> b\<rbrakk> \<Longrightarrow> g (f z) = z;
      \<And>z. \<lbrakk>a \<le> z; z \<le> b\<rbrakk> \<Longrightarrow> isCont f z\<rbrakk> \<Longrightarrow> isCont g (f x)"
  apply (rule isCont_inverse_function [where f=f and d="min (x - a) (b - x)"])
  apply (simp_all add: abs_le_iff)
  done

text \<open>Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110.\<close>
lemma LIM_fun_gt_zero: "f \<midarrow>c\<rightarrow> l \<Longrightarrow> 0 < l \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> 0 < f x)"
  for f :: "real \<Rightarrow> real"
  by (force simp: dest: LIM_D)

lemma LIM_fun_less_zero: "f \<midarrow>c\<rightarrow> l \<Longrightarrow> l < 0 \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> f x < 0)"
  for f :: "real \<Rightarrow> real"
  by (drule LIM_D [where r="-l"]) force+

lemma LIM_fun_not_zero: "f \<midarrow>c\<rightarrow> l \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> f x \<noteq> 0)"
  for f :: "real \<Rightarrow> real"
  using LIM_fun_gt_zero[of f l c] LIM_fun_less_zero[of f l c] by (auto simp: neq_iff)

end

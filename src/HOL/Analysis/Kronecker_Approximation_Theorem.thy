chapter \<open>Kronecker's Theorem with Applications\<close>

theory Kronecker_Approximation_Theorem

imports Complex_Transcendental Henstock_Kurzweil_Integration 
        "HOL-Real_Asymp.Real_Asymp"

begin

section \<open>Dirichlet's Approximation Theorem\<close>

text \<open>Simultaneous version. From Hardy and Wright, An Introduction to the Theory of Numbers, page 170.\<close>
theorem Dirichlet_approx_simult:
  fixes \<theta> :: "nat \<Rightarrow> real" and N n :: nat
  assumes "N > 0" 
  obtains q p where "0<q" "q \<le> int (N^n)" 
    and "\<And>i. i<n \<Longrightarrow> \<bar>of_int q * \<theta> i - of_int(p i)\<bar> < 1/N"
proof -
  have lessN: "nat \<lfloor>x * real N\<rfloor> < N" if "0 \<le> x" "x < 1" for x
  proof -
    have "\<lfloor>x * real N\<rfloor> < N"
      using that by (simp add: assms floor_less_iff)
    with assms show ?thesis by linarith
  qed
  define interv where "interv \<equiv> \<lambda>k. {real k/N..< Suc k/N}"
  define fracs where "fracs \<equiv> \<lambda>k. map (\<lambda>i. frac (real k * \<theta> i)) [0..<n]"
  define X where "X \<equiv> fracs ` {..N^n}"
  define Y where "Y \<equiv> set (List.n_lists n (map interv [0..<N]))"
  have interv_iff: "interv k = interv k' \<longleftrightarrow> k=k'" for k k'
    using assms by (auto simp: interv_def Ico_eq_Ico divide_strict_right_mono)
  have in_interv: "x \<in> interv (nat \<lfloor>x * real N\<rfloor>)" if "x\<ge>0" for x
    using that assms by (simp add: interv_def divide_simps) linarith
  have False 
    if non: "\<forall>a b. b \<le> N^n \<longrightarrow> a < b \<longrightarrow> \<not>(\<forall>i<n. \<bar>frac (real b * \<theta> i) - frac (real a * \<theta> i)\<bar> < 1/N)"
  proof -
    have "inj_on (\<lambda>k. map (\<lambda>i. frac (k * \<theta> i)) [0..<n]) {..N^n}"
      using that assms by (intro linorder_inj_onI) fastforce+
    then have caX: "card X = Suc (N^n)"
      by (simp add: X_def fracs_def card_image)
    have caY: "card Y \<le> N^n"
      by (metis Y_def card_length diff_zero length_map length_n_lists length_upt)
    define f where "f \<equiv> \<lambda>l. map (\<lambda>x. interv (nat \<lfloor>x * real N\<rfloor>)) l"
    have "f ` X \<subseteq> Y"
      by (auto simp: f_def Y_def X_def fracs_def o_def set_n_lists frac_lt_1 lessN)
    then have "\<not> inj_on f X"
      using Y_def caX caY card_inj_on_le not_less_eq_eq by fastforce
    then obtain x x' where "x\<noteq>x'" "x \<in> X" "x' \<in> X" and eq: "f x = f x'"
      by (auto simp: inj_on_def)
    then obtain c c' where c: "c \<noteq> c'" "c \<le> N^n" "c' \<le> N^n" 
            and xeq: "x = fracs c" and xeq': "x' = fracs c'"
      unfolding X_def by (metis atMost_iff image_iff)
    have [simp]: "length x' = n"
      by (auto simp: xeq' fracs_def)
    have ge0: "x'!i \<ge> 0" if "i<n" for i
      using that \<open>x' \<in> X\<close> by (auto simp: X_def fracs_def)
    have "f x \<in> Y"
      using \<open>f ` X \<subseteq> Y\<close> \<open>x \<in> X\<close> by blast
    define k where "k \<equiv> map (\<lambda>r. nat \<lfloor>r * real N\<rfloor>) x"
    have "\<bar>frac (real c * \<theta> i) - frac (real c' * \<theta> i)\<bar> < 1/N" if "i < n" for i
    proof -
      have k: "x!i \<in> interv(k!i)" 
        using \<open>i<n\<close> assms by (auto simp: divide_simps k_def interv_def xeq fracs_def) linarith
      then have k': "x'!i \<in> interv(k!i)" 
        using \<open>i<n\<close> eq assms ge0[OF \<open>i<n\<close>]
        by (auto simp: k_def f_def divide_simps map_equality_iff in_interv interv_iff)
      with assms k show ?thesis
        using \<open>i<n\<close> by (auto simp add: xeq xeq' fracs_def interv_def add_divide_distrib)
    qed
    then show False
      by (metis c non nat_neq_iff abs_minus_commute)
  qed
  then obtain a b where "a<b" "b \<le> N^n" and *: "\<And>i. i<n \<Longrightarrow> \<bar>frac (real b * \<theta> i) - frac (real a * \<theta> i)\<bar> < 1/N"
    by blast
  let ?k = "b-a"
  let ?h = "\<lambda>i. \<lfloor>b * \<theta> i\<rfloor> - \<lfloor>a * \<theta> i\<rfloor>"
  show ?thesis
  proof
    show "int (b - a) \<le> int (N ^ n)"
      using \<open>b \<le> N ^ n\<close> by auto
  next
    fix i
    assume "i<n"
    have "frac (b * \<theta> i) - frac (a * \<theta> i) = ?k * \<theta> i - ?h i"
      using \<open>a < b\<close> by (simp add: frac_def left_diff_distrib' of_nat_diff)
    then show "\<bar>of_int ?k * \<theta> i - ?h i\<bar> < 1/N"
      by (metis "*" \<open>i < n\<close> of_int_of_nat_eq)
  qed (use \<open>a < b\<close> in auto)
qed

text \<open>Theorem references below referr to Apostol, 
  \emph{Modular Functions and Dirichlet Series in Number Theory}\<close>

text \<open>Theorem 7.1\<close>
corollary Dirichlet_approx:
  fixes \<theta>:: real and N:: nat
  assumes "N > 0" 
  obtains h k where "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
  by (rule Dirichlet_approx_simult [OF assms, where n=1 and \<theta>="\<lambda>_. \<theta>"]) auto


text \<open>Theorem 7.2\<close>
corollary Dirichlet_approx_coprime:
  fixes \<theta>:: real and N:: nat
  assumes "N > 0" 
  obtains h k where "coprime h k" "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
proof -
  obtain h' k' where k': "0 < k'" "k' \<le> int N" and *: "\<bar>of_int k' * \<theta> - of_int h'\<bar> < 1/N"
    by (meson Dirichlet_approx assms)
  let ?d = "gcd h' k'"
  show thesis
  proof (cases "?d = 1")
    case True
    with k' * that show ?thesis by auto
  next
    case False
    then have 1: "?d > 1"
      by (smt (verit, ccfv_threshold) \<open>k'>0\<close> gcd_pos_int)
    let ?k = "k' div ?d"
    let ?h = "h' div ?d"
    show ?thesis
    proof
      show "coprime (?h::int) ?k"
        by (metis "1" div_gcd_coprime gcd_eq_0_iff not_one_less_zero)
      show k0: "0 < ?k"
        using \<open>k'>0\<close> pos_imp_zdiv_pos_iff by force
      show "?k \<le> int N"
        using k' "1" int_div_less_self by fastforce
      have "\<bar>\<theta> - of_int ?h / of_int ?k\<bar> = \<bar>\<theta> - of_int h' / of_int k'\<bar>"
        by (simp add: real_of_int_div)
      also have "\<dots> < 1 / of_int (N * k')"
        using k' * by (simp add: field_simps)
      also have "\<dots> < 1 / of_int (N * ?k)"
        using assms \<open>k'>0\<close> k0 1
        by (simp add: frac_less2 int_div_less_self)
      finally show "\<bar>of_int ?k * \<theta> - of_int ?h\<bar> < 1 / real N"
        using k0 k' by (simp add: field_simps)
    qed
  qed
qed

definition approx_set :: "real \<Rightarrow> (int \<times> int) set"
  where "approx_set \<theta> \<equiv> 
     {(h, k) | h k::int. k > 0 \<and> coprime h k \<and> \<bar>\<theta> - of_int h / of_int k\<bar> < 1/k\<^sup>2}" 
  for \<theta>::real

text \<open>Theorem 7.3\<close>
lemma approx_set_nonempty: "approx_set \<theta> \<noteq> {}"
proof -
  have "\<bar>\<theta> - of_int \<lfloor>\<theta>\<rfloor> / of_int 1\<bar> < 1 / (of_int 1)\<^sup>2"
    by simp linarith
  then have "(\<lfloor>\<theta>\<rfloor>, 1) \<in> approx_set \<theta>"
    by (auto simp: approx_set_def)
  then show ?thesis
    by blast
qed


text \<open>Theorem 7.4(c)\<close>
theorem infinite_approx_set:
  assumes "infinite (approx_set \<theta>)"
  shows  "\<exists>h k. (h,k) \<in> approx_set \<theta> \<and> k > K"
proof (rule ccontr, simp add: not_less)
  assume Kb [rule_format]: "\<forall>h k. (h, k) \<in> approx_set \<theta> \<longrightarrow> k \<le> K"
  define H where "H \<equiv> 1 + \<bar>K * \<theta>\<bar>"
  have k0:  "k > 0" if "(h,k) \<in> approx_set \<theta>" for h k
    using approx_set_def that by blast
  have Hb: "of_int \<bar>h\<bar> < H" if "(h,k) \<in> approx_set \<theta>" for h k
  proof -
    have *: "\<bar>k * \<theta> - h\<bar> < 1" 
    proof -
      have "\<bar>k * \<theta> - h\<bar> < 1 / k"
        using that by (auto simp: field_simps approx_set_def eval_nat_numeral)
      also have "\<dots> \<le> 1"
        using divide_le_eq_1 by fastforce
      finally show ?thesis .
    qed
    have "k > 0"
      using approx_set_def that by blast
    have "of_int \<bar>h\<bar> \<le> \<bar>k * \<theta> - h\<bar> + \<bar>k * \<theta>\<bar>"
      by force
    also have "\<dots> < 1 + \<bar>k * \<theta>\<bar>"
      using * that by simp
    also have "\<dots> \<le> H"
      using Kb [OF that] \<open>k>0\<close> by (auto simp add: H_def abs_if mult_right_mono mult_less_0_iff)
    finally show ?thesis .
  qed
  have "approx_set \<theta> \<subseteq> {-(ceiling H)..ceiling H} \<times> {0..K}"
    using Hb Kb k0 
    apply (simp add: subset_iff)
    by (smt (verit, best) ceiling_add_of_int less_ceiling_iff)
  then have "finite (approx_set \<theta>)"
    by (meson finite_SigmaI finite_atLeastAtMost_int finite_subset)
  then show False
    using assms by blast
qed

text \<open>Theorem 7.4(b,d)\<close>
theorem rational_iff_finite_approx_set:
  shows "\<theta> \<in> \<rat> \<longleftrightarrow> finite (approx_set \<theta>)"
proof
  assume "\<theta> \<in> \<rat>"
  then obtain a b where eq: "\<theta> = of_int a / of_int b" and "b>0" and "coprime a b"
    by (meson Rats_cases')
  then have ab: "(a,b) \<in> approx_set \<theta>"
    by (auto simp: approx_set_def)
  show "finite (approx_set \<theta>)"
  proof (rule ccontr)
    assume "infinite (approx_set \<theta>)"
    then obtain h k where "(h,k) \<in> approx_set \<theta>" "k > b" "k>0"
      using infinite_approx_set by (smt (verit, best))
    then have "coprime h k" and hk: "\<bar>a/b - h/k\<bar> < 1 / (of_int k)\<^sup>2"
      by (auto simp: approx_set_def eq)
    have False if "a * k = h * b"
    proof -
      have "b dvd k"
        using that \<open>coprime a b\<close>
        by (metis coprime_commute coprime_dvd_mult_right_iff dvd_triv_right)
      then obtain d where "k = b * d"
        by (metis dvd_def)
      then have "h = a * d"
        using \<open>0 < b\<close> that by force
      then show False
        using \<open>0 < b\<close> \<open>b < k\<close> \<open>coprime h k\<close> \<open>k = b * d\<close> by auto
    qed
    then have 0: "0 < \<bar>a*k - b*h\<bar>"
      by auto
    have "\<bar>a*k - b*h\<bar> < b/k"
      using \<open>k>0\<close> \<open>b>0\<close> hk by (simp add: field_simps eval_nat_numeral)
    also have "\<dots> < 1"
      by (simp add: \<open>0 < k\<close> \<open>b < k\<close>)
    finally show False
      using 0 by linarith
  qed
next
  assume fin: "finite (approx_set \<theta>)"
  show "\<theta> \<in> \<rat>"
  proof (rule ccontr)
    assume irr: "\<theta> \<notin> \<rat>"
    define A where "A \<equiv> ((\<lambda>(h,k). \<bar>\<theta> - h/k\<bar>) ` approx_set \<theta>)"
    let ?\<alpha> = "Min A"
    have "0 \<notin> A"
      using irr by (auto simp: A_def approx_set_def)
    moreover have "\<forall>x\<in>A. x\<ge>0" and A: "finite A" "A \<noteq> {}"
      using approx_set_nonempty by (auto simp: A_def fin)
    ultimately have \<alpha>: "?\<alpha> > 0"
      using Min_in by force 
    then obtain N where N: "real N > 1 / ?\<alpha>"
      using reals_Archimedean2 by blast
    have "0 < 1 / ?\<alpha>"
      using \<alpha> by auto
    also have "\<dots> < real N"
      by (fact N)
    finally have "N > 0"
      by simp
    from N have "1/N < ?\<alpha>"
      by (simp add: \<alpha> divide_less_eq mult.commute)
    then obtain h k where "coprime h k" "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
      by (metis Dirichlet_approx_coprime \<alpha> N divide_less_0_1_iff less_le not_less_iff_gr_or_eq of_nat_0_le_iff of_nat_le_iff of_nat_0)
    then have \<section>: "\<bar>\<theta> - h/k\<bar> < 1 / (k*N)"
      by (simp add: field_simps)
    also have "\<dots> \<le> 1/k\<^sup>2"
      using \<open>k \<le> int N\<close> by (simp add: eval_nat_numeral divide_simps)
    finally have hk_in: "(h,k) \<in> approx_set \<theta>"
      using \<open>0 < k\<close> \<open>coprime h k\<close> by (auto simp: approx_set_def)
    then have "\<bar>\<theta> - h/k\<bar> \<in> A"
      by (auto simp: A_def)
    moreover have "1 / real_of_int (k * int N) < ?\<alpha>"
    proof -
      have "1 / real_of_int (k * int N) = 1 / real N / of_int k"
        by simp
      also have "\<dots> < ?\<alpha> / of_int k"
        using \<open>k > 0\<close> \<alpha> \<open>N > 0\<close> N by (intro divide_strict_right_mono) (auto simp: field_simps)
      also have "\<dots> \<le> ?\<alpha> / 1"
        using \<alpha> \<open>k > 0\<close> by (intro divide_left_mono) auto
      finally show ?thesis
        by simp
    qed
    ultimately show False using A \<section> by auto
  qed
qed


text \<open>No formalisation of Liouville's Approximation Theorem because this is already in the AFP
as Liouville\_Numbers. Apostol's Theorem 7.5 should be exactly the theorem
liouville\_irrational\_algebraic. There is a minor discrepancy in the definition 
of "Liouville number" between Apostol and Eberl: he requires the denominator to be 
positive, while Eberl require it to exceed 1.\<close>

section \<open>Kronecker's Approximation Theorem: the One-dimensional Case\<close>

lemma frac_int_mult: 
  assumes "m > 0" and le: "1-frac r \<le> 1/m"
  shows "1 - frac (of_int m * r) = m * (1 - frac r)" 
proof -
  have "frac (of_int m * r) = 1 - m * (1 - frac r)"
  proof (subst frac_unique_iff, intro conjI)
    show "of_int m * r - (1 - of_int m * (1 - frac r)) \<in> \<int>"
      by (simp add: algebra_simps frac_def)
  qed (use assms in \<open>auto simp: divide_simps mult_ac frac_lt_1\<close>)
  then show ?thesis
    by simp
qed

text \<open>Concrete statement of Theorem 7.7, and the real proof\<close>
theorem Kronecker_approx_1_explicit:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>" and \<alpha>: "0 \<le> \<alpha>" "\<alpha> \<le> 1" and "\<epsilon> > 0"
  obtains k where "k>0" "\<bar>frac(real k * \<theta>) - \<alpha>\<bar> < \<epsilon>"  
proof -
  obtain N::nat where "1/N < \<epsilon>" "N > 0"
    by (metis \<open>\<epsilon> > 0\<close> gr_zeroI inverse_eq_divide real_arch_inverse)
  then obtain h k where "0 < k" and hk: "\<bar>of_int k * \<theta> - of_int h\<bar> < \<epsilon>"
    using Dirichlet_approx that by (metis less_trans)
  have irrat: "of_int n * \<theta> \<in> \<rat> \<Longrightarrow> n = 0" for n
    by (metis Rats_divide Rats_of_int assms(1) nonzero_mult_div_cancel_left of_int_0_eq_iff)
  then consider "of_int k * \<theta> < of_int h" | "of_int k * \<theta> > of_int h"
    by (metis Rats_of_int \<open>0 < k\<close> less_irrefl linorder_neqE_linordered_idom)
  then show thesis
  proof cases
    case 1
    define \<xi> where "\<xi> \<equiv> 1 - frac (of_int k * \<theta>)"
    have pos: "\<xi> > 0"
      by (simp add: \<xi>_def frac_lt_1)
    define N where "N \<equiv> \<lfloor>1/\<xi>\<rfloor>"
    have "N > 0"
      by (simp add: N_def \<xi>_def frac_lt_1)
    have False if "1/\<xi> \<in> \<int>"
    proof -
      from that of_int_ceiling
      obtain r where r: "of_int r = 1/\<xi>" by blast
      then obtain s where s: "of_int k * \<theta> = of_int s + 1 - 1/r"
        by (simp add: \<xi>_def frac_def)
      from r pos s \<open>k > 0\<close> have "\<theta> = (of_int s + 1 - 1/r) / k"
        by (auto simp: field_simps)
      with assms show False
        by simp
    qed
    then have N0: "N < 1/\<xi>"
      unfolding N_def by (metis Ints_of_int floor_correct less_le)
    then have N2: "1/(N+1) < \<xi>"
      unfolding N_def by (smt (verit) divide_less_0_iff divide_less_eq floor_correct mult.commute pos)
    have "\<xi> * (N+1) > 1"
      by (smt (verit) N2 \<open>0 < N\<close> of_int_1_less_iff pos_divide_less_eq)
    then have ex: "\<exists>m. int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
      by (smt (verit, best) \<open>0 < N\<close> \<open>0 \<le> \<alpha>\<close> floor_of_int floor_of_nat mult.commute of_nat_nat)
    define m where "m \<equiv> LEAST m. int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
    have m: "int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
      using LeastI_ex [OF ex] unfolding m_def by blast
    have "m > 0"
      using m gr0I \<open>\<alpha> \<le> 1\<close> by force
    have k\<theta>: "\<xi> < \<epsilon>"
      using hk 1 by (smt (verit, best) floor_eq_iff frac_def \<xi>_def)
    show thesis
    proof (cases "m=1")
      case True
      then have "\<bar>frac (real (nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using m \<open>\<alpha> \<le> 1\<close> \<open>0 < k\<close> \<xi>_def k\<theta> by force
      with \<open>0 < k\<close> zero_less_nat_eq that show thesis by blast 
    next
      case False
      with \<open>0 < m\<close> have "m>1" by linarith
      have "\<xi> < 1 / N"
        by (metis N0 \<open>0 < N\<close> mult_of_int_commute of_int_pos pos pos_less_divide_eq)
      also have "\<dots> \<le> 1 / (real m - 1)"
        using \<open>m > 1\<close> m by (simp add: divide_simps)
      finally have "\<xi> < 1 / (real m - 1)" .
      then have m1_eq: "(int m - 1) * \<xi> = 1 - frac (of_int ((int m - 1) * k) * \<theta>)"
        using frac_int_mult [of "(int m - 1)" "k * \<theta>"] \<open>1 < m\<close>
        by (simp add: \<xi>_def mult.assoc)
      then
      have m1_eq': "frac (of_int ((int m - 1) * k) * \<theta>) = 1 - (int m - 1) * \<xi>"
        by simp
      moreover have "(m - Suc 0) * \<xi> \<le> 1-\<alpha>"
        using Least_le [where k="m-Suc 0"] m
        by (smt (verit, best) Suc_n_not_le_n Suc_pred \<open>0 < m\<close> m_def of_nat_le_iff)
      ultimately have le\<alpha>: " \<alpha> \<le> frac (of_int ((int m - 1) * k) * \<theta>)"
        by (simp add: Suc_leI \<open>0 < m\<close> of_nat_diff)
      moreover have "m * \<xi> + frac (of_int ((int m - 1) * k) * \<theta>) = \<xi> + 1"
        by (subst m1_eq') (simp add: \<xi>_def algebra_simps)
      ultimately have "\<bar>frac ((int (m - 1) * k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        by (smt (verit, best) One_nat_def Suc_leI \<open>0 < m\<close> int_ops(2) k\<theta> m of_nat_diff)
      with that show thesis
        by (metis \<open>0 < k\<close> \<open>1 < m\<close> mult_pos_pos of_int_of_nat_eq of_nat_mult pos_int_cases zero_less_diff)
    qed
  next
    case 2 
    define \<xi> where "\<xi> \<equiv> frac (of_int k * \<theta>)"
    have recip_frac: False if "1/\<xi> \<in> \<int>"
    proof -
      have "frac (of_int k * \<theta>) \<in> \<rat>"
        using that unfolding \<xi>_def
        by (metis Ints_cases Rats_1 Rats_divide Rats_of_int div_by_1 divide_divide_eq_right mult_cancel_right2)
      then show False
        using \<open>0 < k\<close> frac_in_Rats_iff irrat by blast
    qed
    have pos: "\<xi> > 0"
      by (metis \<xi>_def Ints_0 division_ring_divide_zero frac_unique_iff less_le recip_frac)
    define N where "N \<equiv> \<lfloor>1 / \<xi>\<rfloor>"
    have "N > 0"
      unfolding N_def
      by (smt (verit) \<xi>_def divide_less_eq_1_pos floor_less_one frac_lt_1 pos) 
    have N0: "N < 1 / \<xi>"
      unfolding N_def by (metis Ints_of_int floor_eq_iff less_le recip_frac)
    then have N2: "1/(N+1) < \<xi>"
      unfolding N_def
      by (smt (verit, best) divide_less_0_iff divide_less_eq floor_correct mult.commute pos)
    have "\<xi> * (N+1) > 1"
      by (smt (verit) N2 \<open>0 < N\<close> of_int_1_less_iff pos_divide_less_eq)
    then have ex: "\<exists>m. int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
      by (smt (verit, best) mult.commute \<open>\<alpha> \<le> 1\<close> \<open>0 < N\<close> of_int_of_nat_eq pos_int_cases)
    define m where "m \<equiv> LEAST m. int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
    have m: "int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
      using LeastI_ex [OF ex] unfolding m_def by blast
    have "m > 0"
      using \<open>0 \<le> \<alpha>\<close> m gr0I by force
    have k\<theta>: "\<xi> < \<epsilon>"
      using hk 2 unfolding \<xi>_def by (smt (verit, best) floor_eq_iff frac_def)
    have mk_eq: "frac (of_int (m*k) * \<theta>) = m * frac (of_int k * \<theta>)"
      if "m>0" "frac (of_int k * \<theta>) < 1/m" for m k
    proof (subst frac_unique_iff , intro conjI)
      show "real_of_int (m * k) * \<theta> - real_of_int m * frac (real_of_int k * \<theta>) \<in> \<int>"
        by (simp add: algebra_simps frac_def)
    qed (use that in \<open>auto simp: divide_simps mult_ac\<close>)
    show thesis
    proof (cases "m=1")
      case True
      then have "\<bar>frac (real (nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using m \<alpha> \<open>0 < k\<close> \<xi>_def k\<theta> by force
      with \<open>0 < k\<close> zero_less_nat_eq that show ?thesis by blast 
    next
      case False
      with \<open>0 < m\<close> have "m>1" by linarith
      with \<open>0 < k\<close> have mk_pos:"(m - Suc 0) * nat k > 0" by force
      have "real_of_int (int m - 1) < 1 / frac (real_of_int k * \<theta>)"
        using N0 \<xi>_def m by force
      then
      have m1_eq: "(int m - 1) * \<xi> = frac (((int m - 1) * k) * \<theta>)"
        using m mk_eq [of "int m-1" k] pos \<open>m>1\<close> by (simp add: divide_simps mult_ac \<xi>_def)
      moreover have "(m - Suc 0) * \<xi> \<le> \<alpha>"
        using Least_le [where k="m-Suc 0"] m
        by (smt (verit, best) Suc_n_not_le_n Suc_pred \<open>0 < m\<close> m_def of_nat_le_iff)
      ultimately have le\<alpha>: "frac (of_int ((int m - 1) * k) * \<theta>) \<le> \<alpha>"
        by (simp add: Suc_leI \<open>0 < m\<close> of_nat_diff)
      moreover have "(m * \<xi> - frac (of_int ((int m - 1) * k) * \<theta>)) < \<epsilon>"
        by (metis m1_eq add_diff_cancel_left' diff_add_cancel k\<theta> left_diff_distrib' 
            mult_cancel_right2 of_int_1 of_int_diff of_int_of_nat_eq)
      ultimately have "\<bar>frac (real( (m - 1) * nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using \<open>0 < k\<close> \<open>0 < m\<close> by simp (smt (verit, best) One_nat_def Suc_leI m of_nat_1 of_nat_diff)
      with  \<open>m > 0\<close> that show thesis
        using mk_pos One_nat_def by presburger
    qed
  qed
qed


text \<open>Theorem 7.7 expressed more abstractly using @{term closure}\<close>
corollary Kronecker_approx_1:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>"
  shows "closure (range (\<lambda>n. frac (real n * \<theta>))) = {0..1}"  (is "?C = _")
proof -
  have "\<exists>k>0. \<bar>frac(real k * \<theta>) - \<alpha>\<bar> < \<epsilon>" if "0 \<le> \<alpha>" "\<alpha> \<le> 1" "\<epsilon> > 0" for \<alpha> \<epsilon>
    by (meson Kronecker_approx_1_explicit assms that)
  then have "x \<in> ?C" if "0 \<le> x" "x \<le> 1" for x :: real
    using that by (auto simp add: closure_approachable dist_real_def)
  moreover 
  have "(range (\<lambda>n. frac (real n * \<theta>))) \<subseteq> {0..1}"
    by (smt (verit) atLeastAtMost_iff frac_unique_iff image_subset_iff)
  then have "?C \<subseteq> {0..1}"
    by (simp add: closure_minimal)
  ultimately show ?thesis by auto
qed


text \<open>The next theorem removes the restriction $0 \leq \alpha \leq 1$.\<close>

text \<open>Theorem 7.8\<close>
corollary sequence_of_fractional_parts_is_dense:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>" "\<epsilon> > 0"
  obtains h k where "k > 0" "\<bar>of_int k * \<theta> - of_int h - \<alpha>\<bar> < \<epsilon>"
proof -
  obtain k where "k>0" "\<bar>frac(real k * \<theta>) - frac \<alpha>\<bar> < \<epsilon>"  
    by (metis Kronecker_approx_1_explicit assms frac_ge_0 frac_lt_1 less_le_not_le)
  then have "\<bar>real_of_int k * \<theta> - real_of_int (\<lfloor>k * \<theta>\<rfloor> - \<lfloor>\<alpha>\<rfloor>) - \<alpha>\<bar> < \<epsilon>"
    by (auto simp: frac_def)
  then show thesis
    by (meson \<open>0 < k\<close> of_nat_0_less_iff that)
qed

section \<open>Extension of Kronecker's Theorem to Simultaneous Approximation\<close>

subsection \<open>Towards Lemma 1\<close>

lemma integral_exp: 
  assumes  "T \<ge> 0" "a\<noteq>0"
  shows "integral {0..T} (\<lambda>t. exp(a * complex_of_real t)) = (exp(a * of_real T) - 1) / a"
proof -
  have "\<And>t. t \<in> {0..T} \<Longrightarrow> ((\<lambda>x. exp (a * x) / a) has_vector_derivative exp (a * t)) (at t within {0..T})"
    using assms
    by (intro derivative_eq_intros has_complex_derivative_imp_has_vector_derivative [unfolded o_def] | simp)+
  then have "((\<lambda>t. exp(a * of_real t)) has_integral exp(a * complex_of_real T)/a - exp(a * of_real 0)/a)  {0..T}"
    by (meson fundamental_theorem_of_calculus \<open>T \<ge> 0\<close>)
  then show ?thesis
    by (simp add: diff_divide_distrib integral_unique)
qed

lemma Kronecker_simult_aux1:
  fixes \<eta>:: "nat \<Rightarrow> real" and c:: "nat \<Rightarrow> complex" and N::nat
  assumes inj: "inj_on \<eta> {..N}" and "k \<le> N"
  defines "f \<equiv> \<lambda>t. \<Sum>r\<le>N. c r * exp(\<i> * of_real t * \<eta> r)"
  shows "((\<lambda>T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))) \<longlongrightarrow> c k) at_top"
proof -
  define F where "F \<equiv> \<lambda>k t. f t * exp(-\<i> * of_real t * \<eta> k)"
  have f: "F k = (\<lambda>t. \<Sum>r\<le>N. c r * exp(\<i> * (\<eta> r - \<eta> k) * of_real t))" 
    by (simp add: F_def f_def sum_distrib_left field_simps exp_diff exp_minus)
  have *: "integral {0..T} (F k)
      = c k * T + (\<Sum>r \<in> {..N}-{k}. c r * integral {0..T} (\<lambda>t. exp(\<i> * (\<eta> r - \<eta> k) * of_real t)))"
    if "T > 0" for T
    using \<open>k \<le> N\<close> that
    by (simp add: f integral_sum integrable_continuous_interval continuous_intros Groups_Big.sum_diff scaleR_conv_of_real)

  have **: "(1/T) * integral {0..T} (F k)
       = c k + (\<Sum>r \<in> {..N}-{k}. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / (\<i> * (\<eta> r - \<eta> k) * of_real T))"
    if "T > 0" for T
  proof -
    have I: "integral {0..T} (\<lambda>t. exp (\<i> * (complex_of_real t * \<eta> r) - \<i> * (complex_of_real t * \<eta> k))) 
           = (exp(\<i> * (\<eta> r - \<eta> k) * T) - 1) / (\<i> * (\<eta> r - \<eta> k))"
      if "r \<le> N" "r \<noteq> k" for r
      using that \<open>k \<le> N\<close> inj \<open>T > 0\<close> integral_exp [of T "\<i> * (\<eta> r - \<eta> k)"] 
      by (simp add: inj_on_eq_iff algebra_simps)
    show ?thesis
      using that by (subst *) (auto simp add: algebra_simps sum_divide_distrib I)
  qed
  have "((\<lambda>T. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / (\<i> * (\<eta> r - \<eta> k) * of_real T)) \<longlongrightarrow> 0) at_top"
    for r
  proof -
    have "((\<lambda>x. (cos ((\<eta> r - \<eta> k) * x) - 1) / x) \<longlongrightarrow> 0) at_top"
         "((\<lambda>x. sin ((\<eta> r - \<eta> k) * x) / x) \<longlongrightarrow> 0) at_top"
      by real_asymp+
    hence "((\<lambda>T. (exp (\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / of_real T) \<longlongrightarrow> 0) at_top"
      by (simp add: tendsto_complex_iff Re_exp Im_exp)
    from tendsto_mult[OF this tendsto_const[of "c r / (\<i> * (\<eta> r - \<eta> k))"]] show ?thesis
      by (simp add: field_simps)
  qed
  then have "((\<lambda>T. c k + (\<Sum>r \<in> {..N}-{k}. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / 
                  (\<i> * (\<eta> r - \<eta> k) * of_real T))) \<longlongrightarrow> c k + 0) at_top"
    by (intro tendsto_add tendsto_null_sum) auto
  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule filterlim_cong)
    show "\<forall>\<^sub>F x in at_top. c k + (\<Sum>r\<in>{..N} - {k}. c r * (exp (\<i> * of_real (\<eta> r - \<eta> k) * of_real x) - 1) /
            (\<i> * of_real (\<eta> r - \<eta> k) * of_real x)) = 
          1 / of_real x * integral {0..x} (\<lambda>t. f t * exp (- \<i> * of_real t * of_real (\<eta> k)))"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim T)
      show ?case
        using **[of T] elim by (simp add: F_def)
    qed
  qed auto
  finally show ?thesis .
qed

text \<open>the version of Lemma 1 that we actually need\<close>
lemma Kronecker_simult_aux1_strict:
  fixes \<eta>:: "nat \<Rightarrow> real" and c:: "nat \<Rightarrow> complex" and N::nat
  assumes \<eta>: "inj_on \<eta> {..<N}" "0 \<notin> \<eta> ` {..<N}" and "k < N"
  defines "f \<equiv> \<lambda>t. 1 + (\<Sum>r<N. c r * exp(\<i> * of_real t * \<eta> r))"
  shows "((\<lambda>T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))) \<longlongrightarrow> c k) at_top"
proof -
  define c' where "c' \<equiv> case_nat 1 c"
  define \<eta>' where "\<eta>' \<equiv> case_nat 0 \<eta>"
  define f' where "f' \<equiv> \<lambda>t. (\<Sum>r\<le>N. c' r * exp(\<i> * of_real t * \<eta>' r))"
  have "inj_on \<eta>' {..N}"
    using \<eta> by (auto simp: \<eta>'_def inj_on_def split: nat.split_asm)
  moreover have "Suc k \<le> N"
    using \<open>k < N\<close> by auto
  ultimately have "((\<lambda>T. 1 / T * integral {0..T} (\<lambda>t. (\<Sum>r\<le>N. c' r * exp (\<i> * of_real t * \<eta>' r)) *
                    exp (- \<i> * t * \<eta>' (Suc k)))) \<longlongrightarrow> c' (Suc k))
       at_top"
    by (intro Kronecker_simult_aux1)
  moreover have "(\<Sum>r\<le>N. c' r * exp (\<i> * of_real t * \<eta>' r)) = 1 + (\<Sum>r<N. c r * exp (\<i> * of_real t * \<eta> r))" for t
    by (simp add: c'_def \<eta>'_def sum.atMost_shift)
  ultimately show ?thesis
    by (simp add: f_def c'_def \<eta>'_def)
qed

subsection \<open>Towards Lemma 2\<close>

lemma cos_monotone_aux: "\<lbrakk>\<bar>2 * pi * of_int i + x\<bar> \<le> y; y \<le> pi\<rbrakk> \<Longrightarrow> cos y \<le> cos x"
  by (metis add.commute abs_ge_zero cos_abs_real cos_monotone_0_pi_le sin_cos_eq_iff)

lemma Figure7_1:
  assumes "0 \<le> \<epsilon>" "\<epsilon> \<le> \<bar>x\<bar>" "\<bar>x\<bar> \<le> pi"
  shows "cmod (1 + exp (\<i> * x)) \<le> cmod (1 + exp (\<i> * \<epsilon>))"
proof -
  have norm_eq: "sqrt (2 * (1 + cos t)) = cmod (1 + cis t)" for t
    by (simp add: norm_complex_def power2_eq_square algebra_simps)
  have "cos \<bar>x\<bar> \<le> cos \<epsilon>"
    by (rule cos_monotone_0_pi_le) (use assms in auto)
  hence "sqrt (2 * (1 + cos \<bar>x\<bar>)) \<le> sqrt (2 * (1 + cos \<epsilon>))"
    by simp
  also have "cos \<bar>x\<bar> = cos x"
    by simp
  finally show ?thesis
    unfolding norm_eq by (simp add: cis_conv_exp)
qed

lemma Kronecker_simult_aux2:
  fixes \<alpha>:: "nat \<Rightarrow> real" and \<theta>:: "nat \<Rightarrow> real" and n::nat
  defines "F \<equiv> \<lambda>t. 1 + (\<Sum>r<n. exp(\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r))))"
  defines "L \<equiv> Sup (range (norm \<circ> F))"
  shows "(\<forall>\<epsilon>>0. \<exists>t h. \<forall>r<n. \<bar>t * \<theta> r - \<alpha> r - of_int (h r)\<bar> < \<epsilon>) \<longleftrightarrow> L = Suc n" (is "?lhs = _")
proof
  assume ?lhs
  then have "\<And>k. \<exists>t h. \<forall>r<n. \<bar>t * \<theta> r - \<alpha> r - of_int (h r)\<bar> < 1 / (2 * pi * Suc k)"
    by simp
  then obtain t h where th: "\<And>k r. r<n \<Longrightarrow> \<bar>t k * \<theta> r - \<alpha> r - of_int (h k r)\<bar> < 1 / (2 * pi * Suc k)"
    by metis
  have Fle: "\<And>x. cmod (F x) \<le> real (Suc n)"
    by (force simp: F_def intro: order_trans [OF norm_triangle_ineq] order_trans [OF norm_sum])
  then have boundedF: "bounded (range F)"
    by (metis bounded_iff rangeE) 
  have leL: "1 + n * cos(1 / Suc k) \<le> L" for k
  proof -
    have *: "cos (1 / Suc k) \<le> cos (2 * pi * (t k * \<theta> r - \<alpha> r))" if "r<n" for r 
    proof (rule cos_monotone_aux)
      have "\<bar>2 * pi * (- h k r) + 2 * pi * (t k * \<theta> r - \<alpha> r)\<bar> \<le> \<bar>t k * \<theta> r - \<alpha> r - h k r\<bar> * 2 * pi"
        by (simp add: algebra_simps abs_mult_pos abs_mult_pos')
      also have "\<dots> \<le> 1 / real (Suc k)"
        using th [OF that, of k] by (simp add: divide_simps)
      finally show "\<bar>2 * pi * real_of_int (- h k r) + 2 * pi * (t k * \<theta> r - \<alpha> r)\<bar> \<le> 1 / real (Suc k)" .
      have "1 / real (Suc k) \<le> 1"
        by auto
      then show "1 / real (Suc k) \<le> pi"
        using pi_ge_two by linarith
    qed
    have "1 + n * cos(1 / Suc k) = 1 + (\<Sum>r<n. cos(1 / Suc k))"
      by simp
    also have "\<dots> \<le> 1 + (\<Sum>r<n. cos (2 * pi * (t k * \<theta> r - \<alpha> r)))"
      using * by (intro add_mono sum_mono) auto
    also have "\<dots> \<le> Re (F(t k))"
      by (simp add: F_def Re_exp)
    also have "\<dots> \<le> norm (F(t k))"
      by (simp add: complex_Re_le_cmod)
    also have "\<dots> \<le> L"
      by (simp add: L_def boundedF bounded_norm_le_SUP_norm)
    finally show ?thesis .
  qed
  show "L = Suc n"
  proof (rule antisym)
    show "L \<le> Suc n"
      using Fle by (auto simp add: L_def intro: cSup_least)
    have "((\<lambda>k. 1 + real n * cos (1 / real (Suc k))) \<longlongrightarrow> 1 + real n) at_top"
      by real_asymp
    with LIMSEQ_le_const2 leL show "Suc n \<le> L"
      by fastforce
  qed
next
  assume L: "L = Suc n"
  show ?lhs
  proof (rule ccontr)
    assume "\<not> ?lhs"
    then obtain e0 where "e0>0" and e0: "\<And>t h. \<exists>k<n. \<bar>t * \<theta> k - \<alpha> k - of_int (h k)\<bar> \<ge> e0"
      by (force simp: not_less)
    define \<epsilon> where "\<epsilon> \<equiv> min e0 (pi/4)"
    have \<epsilon>: "\<And>t h. \<exists>k<n. \<bar>t * \<theta> k - \<alpha> k - of_int (h k)\<bar> \<ge> \<epsilon>"
      unfolding \<epsilon>_def using e0 min.coboundedI1 by blast
    have \<epsilon>_bounds: "\<epsilon> > 0" "\<epsilon> < pi" "\<epsilon> \<le> pi/4"
      using \<open>e0 > 0\<close> by (auto simp: \<epsilon>_def min_def)
    with sin_gt_zero have "sin \<epsilon> > 0"
      by blast
    then have "\<not> collinear{0, 1, exp (\<i> * \<epsilon>)}"
      using collinear_iff_Reals cis.sel cis_conv_exp complex_is_Real_iff by force
    then have "norm (1 + exp (\<i> * \<epsilon>)) < 2"
      using norm_triangle_eq_imp_collinear
      by (smt (verit) linorder_not_le norm_exp_i_times norm_one norm_triangle_lt)
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "norm (1 + exp (\<i> * \<epsilon>)) = 2 - \<delta>"
      by (smt (verit, best))
    have "norm (F t) \<le> n+1-\<delta>" for t 
    proof -
      define h where "h \<equiv> \<lambda>r. round (t * \<theta> r - \<alpha> r)"
      define X where "X \<equiv> \<lambda>r. t * \<theta> r - \<alpha> r - h r"
      have "exp (\<i> * (of_int j * (of_real pi * 2))) = 1" for j
        by (metis add_0 exp_plus_2pin exp_zero)
      then have exp_X: "exp (\<i> * (2 * of_real pi * of_real (X r))) 
                 = exp (\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r)))" for r
        by (simp add: X_def right_diff_distrib exp_add exp_diff mult.commute)
      have norm_pr_12: "X r \<in> {-1/2..<1/2}" for r
        apply (simp add: X_def h_def)
        by (smt (verit, best) abs_of_nonneg half_bounded_equal of_int_round_abs_le of_int_round_gt)
      obtain k where "k<n" and 1: "\<bar>X k\<bar> \<ge> \<epsilon>"
        using X_def \<epsilon> [of t h] by auto
      have 2: "2*pi \<ge> 1"
        using pi_ge_two by auto
      have "\<bar>2 * pi * X k\<bar> \<ge> \<epsilon>"
        using mult_mono [OF 2 1] pi_ge_zero by linarith
      moreover
      have "\<bar>2 * pi * X k\<bar> \<le> pi"
        using norm_pr_12 [of k] apply (simp add: abs_if field_simps)
        by (smt (verit, best) divide_le_eq_1_pos divide_minus_left m2pi_less_pi nonzero_mult_div_cancel_left)
      ultimately
      have *: "norm (1 + exp (\<i> * of_real (2 * pi * X k))) \<le> norm (1 + exp (\<i> * \<epsilon>))"
        using Figure7_1[of \<epsilon> "2 * pi * X k"] \<epsilon>_bounds by linarith
      have "norm (F t) = norm (1 + (\<Sum>r<n. exp(\<i> * of_real (2 * pi * (X r)))))"
        by (auto simp: F_def exp_X)
      also have "\<dots> \<le> norm (1 + exp(\<i> * of_real (2 * pi * X k)) + (\<Sum>r \<in> {..<n}-{k}. exp(\<i> * of_real (2 * pi * X r))))"
        by (simp add: comm_monoid_add_class.sum.remove [where x=k] \<open>k < n\<close> algebra_simps)
      also have "\<dots> \<le> norm (1 + exp(\<i> * of_real (2 * pi * X k))) + (\<Sum>r \<in> {..<n}-{k}. norm (exp(\<i> * of_real (2 * pi * X r))))"
        by (intro norm_triangle_mono sum_norm_le order_refl)
      also have "\<dots> \<le> (2 - \<delta>) + (n - 1)"
        using \<open>k < n\<close> \<delta> 
        by simp (metis "*" mult_2 of_real_add of_real_mult)
      also have "\<dots> = n + 1 - \<delta>"
        using \<open>k < n\<close> by simp
      finally show ?thesis .
    qed
    then have "L \<le> 1 + real n - \<delta>"
      by (auto simp: L_def intro: cSup_least)
    with L \<open>\<delta> > 0\<close> show False
      by linarith
  qed
qed

subsection \<open>Towards lemma 3\<close>

text \<open>The text doesn't say so, but the generated polynomial needs to be "clean":
all coefficients nonzero, and with no exponent string mentioned more than once.
And no constant terms (with all exponents zero).\<close>

text \<open>Some tools for combining integer-indexed sequences or splitting them into parts\<close>

lemma less_sum_nat_iff:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>j<k. (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
proof (induction k arbitrary: b)
  case (Suc k)
  then show ?case
    by (simp add: less_Suc_eq) (metis not_less trans_less_add1)
qed auto

lemma less_sum_nat_iff_uniq:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>!j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
  unfolding less_sum_nat_iff by (meson leD less_sum_nat_iff nat_neq_iff)

definition part :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "part a k b \<equiv> (THE j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"

lemma part: 
  "b < (\<Sum>i<k. a i) \<longleftrightarrow> (let j = part a k b in j < k \<and> (\<Sum>i < j. a i) \<le> b \<and> b < (\<Sum>i < j. a i) + a j)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding less_sum_nat_iff_uniq part_def by (metis (no_types, lifting) theI')
qed (auto simp: less_sum_nat_iff Let_def)

lemma part_Suc: "part a (Suc k) b = (if sum a {..<k} \<le> b \<and> b < sum a {..<k} + a k then k else part a k b)"
  using leD 
  by (fastforce simp: part_def less_Suc_eq less_sum_nat_iff conj_disj_distribR cong: conj_cong)

text \<open>The polynomial expansions used in Lemma 3\<close>

definition gpoly :: "[nat, nat\<Rightarrow>complex, nat, nat\<Rightarrow>nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> complex"
  where "gpoly n x N a r \<equiv> (\<Sum>k<N. a k * (\<Prod>i<n. x i ^ r k i))"

lemma gpoly_cong:
  assumes "\<And>k. k < N \<Longrightarrow> a' k = a k" "\<And>k i. \<lbrakk>k < N; i<n\<rbrakk> \<Longrightarrow> r' k i = r k i"
  shows "gpoly n x N a r = gpoly n x N a' r'"
  using assms by (auto simp: gpoly_def)

lemma gpoly_inc: "gpoly n x N a r = gpoly (Suc n) x N a (\<lambda>k. (r k)(n:=0))"
  by (simp add: gpoly_def algebra_simps sum_distrib_left)

lemma monom_times_gpoly: "gpoly n x N a r * x n ^ q = gpoly (Suc n) x N a (\<lambda>k. (r k)(n:=q))"
  by (simp add: gpoly_def algebra_simps sum_distrib_left)

lemma const_times_gpoly: "e * gpoly n x N a r = gpoly n x N ((*)e \<circ> a) r"
  by (simp add: gpoly_def sum_distrib_left mult.assoc)

lemma one_plus_gpoly: "1 + gpoly n x N a r = gpoly n x (Suc N) (a(N:=1)) (r(N:=(\<lambda>_. 0)))"
  by (simp add: gpoly_def)

lemma gpoly_add:
  "gpoly n x N a r + gpoly n x N' a' r' 
 = gpoly n x (N+N') (\<lambda>k. if k<N then a k else a' (k-N)) (\<lambda>k. if k<N then r k else r' (k-N))"
proof -
  have "{..<N+N'} = {..<N} \<union> {N..<N+N'}" "{..<N} \<inter> {N..<N + N'} = {}"
    by auto
  then show ?thesis
    by (simp add: gpoly_def sum.union_disjoint sum.atLeastLessThan_shift_0[of _ N] atLeast0LessThan)
qed

lemma gpoly_sum:
  fixes n Nf af rf p
  defines "N \<equiv> sum Nf {..<p}"
  defines "a \<equiv> \<lambda>k. let q = (part Nf p k) in af q (k - sum Nf {..<q})"
  defines "r \<equiv> \<lambda>k. let q = (part Nf p k) in rf q (k - sum Nf {..<q})"
  shows "(\<Sum>q<p. gpoly n x (Nf q) (af q) (rf q)) = gpoly n x N a r"
  unfolding N_def a_def r_def
proof (induction p)
  case 0
  then show ?case
    by (simp add: gpoly_def)
next
  case (Suc p)
  then show ?case 
    by (auto simp: gpoly_add Let_def part_Suc intro: gpoly_cong)
qed

text \<open>For excluding constant terms: with all exponents zero\<close>
definition nontriv_exponents :: "[nat, nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> bool"
  where "nontriv_exponents n N r \<equiv> \<forall>k<N. \<exists>i<n. r k i \<noteq> 0"

lemma nontriv_exponents_add: 
  "\<lbrakk>nontriv_exponents n M r; nontriv_exponents (Suc n) N r'\<rbrakk> \<Longrightarrow> 
   nontriv_exponents (Suc n) (M + N) (\<lambda>k. if k<M then r k else r' (k-M))"
  by (force simp add: nontriv_exponents_def less_Suc_eq)

lemma nontriv_exponents_sum:
  assumes "\<And>q. q < p \<Longrightarrow> nontriv_exponents n (N q) (r q)"
  shows "nontriv_exponents n (sum N {..<p}) (\<lambda>k. let q = part N p k in r q (k - sum N {..<q}))"
  using assms by (simp add: nontriv_exponents_def less_diff_conv2 part Let_def)

definition uniq_exponents :: "[nat, nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> bool"
  where "uniq_exponents n N r \<equiv> \<forall>k<N. \<forall>k'<k. \<exists>i<n. r k i \<noteq> r k' i"

lemma uniq_exponents_inj: "uniq_exponents n N r \<Longrightarrow> inj_on r {..<N}"
  by (smt (verit, best) inj_on_def lessThan_iff linorder_cases uniq_exponents_def)

text \<open>All coefficients must be nonzero\<close>
definition nonzero_coeffs :: "[nat, nat\<Rightarrow>nat] \<Rightarrow> bool"
  where "nonzero_coeffs N a \<equiv> \<forall>k<N. a k \<noteq> 0"

text \<open>Any polynomial expansion can be cleaned up, removing zero coeffs, etc.\<close>
lemma gpoly_uniq_exponents:
  obtains N' a' r' 
  where "\<And>x. gpoly n x N a r = gpoly n x N' a' r'" 
        "uniq_exponents n N' r'" "nonzero_coeffs N' a'" "N' \<le> N" 
        "nontriv_exponents n N r \<Longrightarrow> nontriv_exponents n N' r'" 
proof (cases "\<forall>k<N. a k = 0")
  case True
  show thesis
  proof
    show "gpoly n x N a r = gpoly n x 0 a r" for x
      by (auto simp: gpoly_def True)
  qed (auto simp: uniq_exponents_def nonzero_coeffs_def nontriv_exponents_def)
next
  case False
  define cut where "cut f i \<equiv> if i<n then f i else (0::nat)" for f i
  define R where "R \<equiv> cut ` r ` ({..<N} \<inter> {k. a k > 0})"
  define N' where "N' \<equiv> card R"
  define r' where "r' \<equiv> from_nat_into R"
  define a' where "a' \<equiv> \<lambda>k'. \<Sum>k<N. if r' k' = cut (r k) then a k else 0"
  have "finite R"
    using R_def by blast
  then have bij: "bij_betw r' {..<N'} R"
    using bij_betw_from_nat_into_finite N'_def r'_def by blast
  have 1: "card {i. i < N' \<and> r' i = cut (r k)} = Suc 0"
    if "k < N" "a k > 0" for k
  proof -
    have "card {i. i < N' \<and> r' i = cut (r k)} \<le> Suc 0"
      using bij by (simp add: card_le_Suc0_iff_eq bij_betw_iff_bijections Ball_def) metis
    moreover have "card {i. i < N' \<and> r' i = cut (r k)} > 0" 
      using bij that by (auto simp: card_gt_0_iff bij_betw_iff_bijections R_def)
    ultimately show "card {i. i < N' \<and> r' i = cut (r k)} = Suc 0"
      using that by auto
  qed
  show thesis
  proof
    have "\<exists>i<n. r' k i \<noteq> r' k' i" if "k < N'" and "k' < k" for k k'
    proof -
      have "k' < N'"
        using order.strict_trans that by blast
      then have "r' k \<noteq> r' k'"
        by (metis bij bij_betw_iff_bijections lessThan_iff nat_neq_iff that)
      moreover obtain sk sk' where "r' k = cut sk" "r' k' = cut sk'"
        by (metis R_def \<open>k < N'\<close> \<open>k' < N'\<close> bij bij_betwE image_iff lessThan_iff)
      ultimately show ?thesis
        using local.cut_def by force
    qed
    then show "uniq_exponents n N' r'"
      by (auto simp: uniq_exponents_def R_def)
    have "R \<subseteq> (cut \<circ> r) ` {..<N}"
      by (auto simp: R_def)
    then show "N' \<le> N"
      unfolding N'_def by (metis card_lessThan finite_lessThan surj_card_le)
    show "gpoly n x N a r = gpoly n x N' a' r'" for x
    proof -
      have "a k * (\<Prod>i<n. x i ^ r k i) 
          = (\<Sum>i<N'. (if r' i = cut (r k) then of_nat (a k) else of_nat 0) * (\<Prod>j<n. x j ^ r' i j))" 
        if "k<N" for k
        using that
        by (cases"a k = 0")
           (simp_all add: if_distrib [of "\<lambda>v. v * _"] 1 cut_def flip: sum.inter_filter cong: if_cong)
      then show ?thesis
        by (simp add: gpoly_def a'_def sum_distrib_right sum.swap [where A="{..<N'}"] if_distrib [of of_nat])
    qed
    show "nontriv_exponents n N' r'" if ne: "nontriv_exponents n N r"
    proof -
      have "\<exists>i<n. 0 < r' k' i" if "k' < N'" for k'
      proof -
        have "r' k' \<in> R"
          using bij bij_betwE that by blast
        then obtain k where "k<N" and k: "r' k' = cut (r k)"
          using R_def by blast
        with ne obtain i where "i<n" "r k i > 0"
          by (auto simp: nontriv_exponents_def)
        then show ?thesis
          using k local.cut_def by auto
      qed
      then show ?thesis
        by (simp add: nontriv_exponents_def)
    qed
    have "0 < a' k'" if "k' < N'" for k'
    proof -
      have "r' k' \<in> R"
        using bij bij_betwE that by blast
      then obtain k where "k<N" "a k > 0" "r' k' = cut (r k)"
        using R_def by blast
      then have False if "a' k' = 0"
        using that by (force simp add: a'_def Ball_def )
      then show ?thesis
        by blast
    qed
    then show "nonzero_coeffs N' a'"
      by (auto simp: nonzero_coeffs_def)
  qed
qed


lemma Kronecker_simult_aux3: 
  "\<exists>N a r. (\<forall>x. (1 + (\<Sum>i<n. x i))^p = 1 + gpoly n x N a r) \<and> Suc N \<le> (p+1)^n
         \<and> nontriv_exponents n N r"
proof (induction n arbitrary: p)
  case 0
  then show ?case
    by (auto simp: gpoly_def nontriv_exponents_def nonzero_coeffs_def)
next
  case (Suc n)
  then obtain Nf af rf 
    where feq: "\<And>q x. (1 + (\<Sum>i<n. x i)) ^ q = 1 + gpoly n x (Nf q) (af q) (rf q)" 
      and Nle: "\<And>q. Suc (Nf q) \<le> (q+1)^n"
      and nontriv: "\<And>q. nontriv_exponents n (Nf q) (rf q)"
    by metis
  define N where "N \<equiv> Nf p + (\<Sum>q<p. Suc (Nf q))"
  define a where "a \<equiv> \<lambda>k. if k < Nf p then af p k
                           else let q = part (\<lambda>t. Suc (Nf t)) p (k - Nf p)
                                in (p choose q) *
                                   (if k - Nf p - (\<Sum>t<q. Suc (Nf t)) = Nf q then Suc 0
                                    else af q (k - Nf p - (\<Sum>t<q. Suc(Nf t))))"
  define r where "r \<equiv> \<lambda>k. if k < Nf p then (rf p k)(n := 0)
                                       else let q = part (\<lambda>t. Suc (Nf t)) p (k - Nf p)
                                          in (if k - Nf p - (\<Sum>t<q. Suc (Nf t)) = Nf q then \<lambda>_. 0
                                              else rf q (k - Nf p - (\<Sum>t<q. Suc(Nf t))))  (n := p-q)"
  have peq: "{..p} = insert p {..<p}"
    by auto
  have "nontriv_exponents n (Nf p) (\<lambda>i. (rf p i)(n := 0))"
       "\<And>q. q<p \<Longrightarrow> nontriv_exponents (Suc n) (Suc (Nf q)) (\<lambda>k. (if k = Nf q then \<lambda>_. 0 else rf q k) (n := p - q))"
    using nontriv by (fastforce simp: nontriv_exponents_def)+
  then have "nontriv_exponents (Suc n) N r"
    unfolding N_def r_def by (intro nontriv_exponents_add nontriv_exponents_sum)
  moreover
  { fix x :: "nat \<Rightarrow> complex"
    have "(1 + (\<Sum>i < Suc n. x i)) ^ p = (1 + (\<Sum>i<n. x i) + x n) ^ p"
      by (simp add: add_ac)
    also have "\<dots> = (\<Sum>q\<le>p. (p choose q) * (1 + (\<Sum>i<n. x i))^q * x n^(p-q))"
      by (simp add: binomial_ring)
    also have "\<dots> = (\<Sum>q\<le>p. (p choose q) * (1 + gpoly n x (Nf q) (af q) (rf q)) * x n^(p-q))"
      by (simp add: feq)
    also have "\<dots> = 1 + (gpoly n x (Nf p) (af p) (rf p) + (\<Sum>q<p. (p choose q) * (1 + gpoly n x (Nf q) (af q) (rf q)) * x n^(p-q)))"
      by (simp add: algebra_simps sum.distrib peq)
    also have "\<dots> = 1 + gpoly (Suc n) x N a r"
      apply (subst one_plus_gpoly)
      apply (simp add: const_times_gpoly monom_times_gpoly gpoly_sum)
      apply (simp add: gpoly_inc [where n=n] gpoly_add N_def a_def r_def)
      done
    finally have "(1 + sum x {..<Suc n}) ^ p = 1 + gpoly (Suc n) x N a r" . 
  }
  moreover have "Suc N \<le> (p + 1) ^ Suc n"
  proof -
    have "Suc N = (\<Sum>q\<le>p. Suc (Nf q))"
      by (simp add: N_def peq)
    also have "\<dots> \<le> (\<Sum>q\<le>p. (q+1)^n)"
      by (meson Nle sum_mono)
    also have "\<dots> \<le> (\<Sum>q\<le>p. (p+1)^n)"
      by (force intro!: sum_mono power_mono)
    also have "\<dots> \<le> (p + 1) ^ Suc n"
      by simp
    finally show "Suc N \<le> (p + 1) ^ Suc n" .
  qed
  ultimately show ?case
    by blast
qed

lemma Kronecker_simult_aux3_uniq_exponents:
  obtains N a r where "\<And>x. (1 + (\<Sum>i<n. x i))^p = 1 + gpoly n x N a r" "Suc N \<le> (p+1)^n" 
                      "nontriv_exponents n N r" "uniq_exponents n N r" "nonzero_coeffs N a"
proof -
  obtain N0 a0 r0 where "\<And>x. (1 + (\<Sum>r<n. x r)) ^ p = 1 + gpoly n x N0 a0 r0" 
    and "Suc N0 \<le> (p+1)^n" "nontriv_exponents n N0 r0" 
    using Kronecker_simult_aux3 by blast
  with le_trans Suc_le_mono gpoly_uniq_exponents [of n N0 a0 r0] that show thesis
    by (metis (no_types, lifting))
qed

subsection \<open>And finally Kroncker's theorem itself\<close>

text \<open>Statement of Theorem 7.9\<close>
theorem Kronecker_thm_1:
  fixes \<alpha> \<theta>:: "nat \<Rightarrow> real" and n:: nat
  assumes indp: "module.independent (\<lambda>r. (*) (real_of_int r)) (\<theta> ` {..<n})"
    and inj\<theta>: "inj_on \<theta> {..<n}" and "\<epsilon> > 0"
  obtains t h where "\<And>i. i < n \<Longrightarrow> \<bar>t * \<theta> i - of_int (h i) - \<alpha> i\<bar> < \<epsilon>"
proof (cases "n>0")
  case False then show ?thesis
    using that by blast
next
  case True
  interpret Modules.module "(\<lambda>r. (*) (real_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  define F where "F \<equiv> \<lambda>t. 1 + (\<Sum>i<n. exp(\<i> * of_real (2 * pi * (t * \<theta> i - \<alpha> i))))"
  define L where "L \<equiv> Sup (range (norm \<circ> F))"
  have [continuous_intros]: "0 < T \<Longrightarrow> continuous_on {0..T} F" for T
    unfolding F_def by (intro continuous_intros)
  have nft_Sucn: "norm (F t) \<le> Suc n" for t
    unfolding F_def by (rule norm_triangle_le order_trans [OF norm_sum] | simp)+
  then have L_le: "L \<le> Suc n"
    by (simp add: L_def cSUP_least)
  have nft_L: "norm (F t) \<le> L" for t
    by (metis L_def UNIV_I bdd_aboveI2 cSUP_upper nft_Sucn o_apply)
  have "L = Suc n"
  proof -
    { fix p::nat
      assume "p>0"      
      obtain N a r where 3: "\<And>x. (1 + (\<Sum>r<n. x r)) ^ p = 1 + gpoly n x N a r" 
             and SucN: "Suc N \<le> (p+1)^n"   
             and nontriv: "nontriv_exponents n N r" and uniq: "uniq_exponents n N r"
             and apos: "nonzero_coeffs N a"
        using Kronecker_simult_aux3_uniq_exponents by blast
      have "N \<noteq> 0"
      proof 
        assume "N = 0"
        have "2^p = (1::complex)"
          using 3 [of "(\<lambda>_. 0)(0:=1)"] True \<open>p>0\<close> \<open>N = 0\<close> by (simp add: gpoly_def)
        then have "2 ^ p = Suc 0"
          by (metis of_nat_1 One_nat_def of_nat_eq_iff of_nat_numeral of_nat_power)
        with \<open>0 < p\<close> show False by force
      qed
      define x where "x \<equiv> \<lambda>t r. exp(\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r)))"
      define f where "f \<equiv> \<lambda>t. (F t) ^ p"
      have feq: "f t = 1 + gpoly n (x t) N a r" for t
        unfolding f_def F_def x_def by (simp flip: 3)
      define c where "c \<equiv> \<lambda>k. a k / cis (\<Sum>i<n. (pi * (2 * (\<alpha> i * real (r k i)))))"
      define \<eta> where "\<eta> \<equiv> \<lambda>k. 2 * pi * (\<Sum>i<n. r k i * \<theta> i)"
      define INTT where "INTT \<equiv> \<lambda>k T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))"
      have "a k * (\<Prod>i<n. x t i ^ r k i) = c k * exp (\<i> * t * \<eta> k)" if "k<N" for k t
        apply (simp add: x_def \<eta>_def sum_distrib_left flip: exp_of_nat_mult exp_sum)
        apply (simp add: algebra_simps sum_subtractf exp_diff c_def sum_distrib_left cis_conv_exp)
        done
      then have fdef: "f t = 1 + (\<Sum>k<N. c k * exp(\<i> * of_real t * \<eta> k))" for t
        by (simp add: feq gpoly_def)
      have nzero: "\<theta> i \<noteq> 0" if "i<n" for i
        using indp that local.dependent_zero by force
      have ind_disj: "\<And>u. (\<forall>x<n. u (\<theta> x) = 0) \<or> (\<Sum>v \<in> \<theta>`{..<n}. of_int (u v) * v) \<noteq> 0"
        using indp by (auto simp: dependent_finite)
      have inj\<eta>: "inj_on \<eta> {..<N}"
      proof
        fix k k'
        assume k: "k \<in> {..<N}" "k' \<in> {..<N}" and "\<eta> k = \<eta> k'"
        then have eq: "(\<Sum>i<n. real (r k i) * \<theta> i) = (\<Sum>i<n. real (r k' i) * \<theta> i)"
          by (auto simp: \<eta>_def)
        define f where "f \<equiv> \<lambda>z. let i = inv_into {..<n} \<theta> z in int (r k i) - int (r k' i)"
        show "k = k'"
          using ind_disj [of f] inj\<theta> uniq eq k
          apply (simp add: f_def Let_def sum.reindex sum_subtractf algebra_simps uniq_exponents_def)
          by (metis not_less_iff_gr_or_eq)
      qed
      moreover have "0 \<notin> \<eta> ` {..<N}"
        unfolding \<eta>_def
      proof clarsimp
        fix k
        assume *: "(\<Sum>i<n. real (r k i) * \<theta> i) = 0" "k < N"
        define f where "f \<equiv> \<lambda>z. let i = inv_into {..<n} \<theta> z in int (r k i)"
        obtain i where "i<n" and "r k i > 0"
          by (meson \<open>k < N\<close> nontriv nontriv_exponents_def zero_less_iff_neq_zero)
        with * nzero show False
          using ind_disj [of f] inj\<theta> by (simp add: f_def sum.reindex)
      qed
      ultimately have 15: "(INTT k \<longlongrightarrow> c k) at_top" if "k<N" for k
        unfolding fdef INTT_def using Kronecker_simult_aux1_strict that by presburger
      have norm_c: "norm (c k) \<le> L^p" if "k<N" for k 
      proof (intro tendsto_le [of _ "\<lambda>_. L^p"])
        show "((norm \<circ> INTT k) \<longlongrightarrow> cmod (c k)) at_top"
          using that 15 by (simp add: o_def tendsto_norm)
        have "norm (INTT k T) \<le> L^p" if  "T \<ge> 0" for T::real
        proof -
          have "0 \<le> L ^ p"
            by (meson nft_L norm_ge_zero order_trans zero_le_power) 
          have "norm (integral {0..T} (\<lambda>t. f t * exp (- (\<i> *  t * \<eta> k)))) 
                \<le> integral {0..T} (\<lambda>t. L^p)" (is "?L \<le> ?R")  if "T>0"
          proof -
            have "?L \<le> integral {0..T} (\<lambda>t. norm (f t * exp (- (\<i> *  t * \<eta> k))))"
              unfolding f_def by (intro continuous_on_imp_absolutely_integrable_on continuous_intros that)
            also have "\<dots> \<le> ?R"
              unfolding f_def
              by (intro integral_le continuous_intros integrable_continuous_interval that
                  | simp add: nft_L norm_mult norm_power power_mono)+
            finally show ?thesis .
          qed
          with \<open>T \<ge> 0\<close> have "norm (INTT k T) \<le> (1/T) * integral {0..T} (\<lambda>t. L ^ p)"
            by (auto simp add: INTT_def norm_divide divide_simps simp del: integral_const_real)
          also have "\<dots> \<le> L ^ p"
            using \<open>T \<ge> 0\<close> \<open>0 \<le> L ^ p\<close> by simp
          finally show ?thesis .
        qed
        then show "\<forall>\<^sub>F x in at_top. (norm \<circ> INTT k) x \<le> L ^ p"
          using eventually_at_top_linorder that by fastforce
      qed auto
      then have "(\<Sum>k<N. cmod (c k)) \<le> N * L^p"
        by (metis sum_bounded_above card_lessThan lessThan_iff)
      moreover
      have "Re((1 + (\<Sum>r<n. 1)) ^ p) = Re (1 + gpoly n (\<lambda>_. 1) N a r)"
        using 3 [of "\<lambda>_. 1"] by metis
      then have 14: "1 + (\<Sum>k<N. norm (c k)) = (1 + real n) ^ p"
        by (simp add: c_def norm_divide gpoly_def)
      moreover 
      have "L^p \<ge> 1"
        using norm_c [of 0] \<open>N \<noteq> 0\<close> apos 
        by (force simp add: c_def norm_divide nonzero_coeffs_def)
      ultimately have *: "(1 + real n) ^ p \<le> Suc N * L^p"
        by (simp add: algebra_simps)
      have [simp]: "L>0"
        using \<open>1 \<le> L ^ p\<close> \<open>0 < p\<close> by (smt (verit, best) nft_L norm_ge_zero power_eq_0_iff)
      have "Suc n ^ p \<le> (p+1)^n * L^p" 
        by (smt (verit, best) * mult.commute \<open>1 \<le> L ^ p\<close> SucN mult_left_mono of_nat_1 of_nat_add of_nat_power_eq_of_nat_cancel_iff of_nat_power_le_of_nat_cancel_iff plus_1_eq_Suc)
      then have "(Suc n ^ p) powr (1/p) \<le> ((p+1)^n * L^p) powr (1/p)"
        by (simp add: powr_mono2)
      then have "(Suc n) \<le> ((p+1)^n) powr (1/p) * L"
        using \<open>p > 0\<close> \<open>0 < L\<close> by (simp add: powr_powr powr_mult flip: powr_realpow)
      also have "\<dots> = ((p+1) powr n) powr (1/p) * L"
        by (simp add: powr_realpow)
      also have "\<dots> = (p+1) powr (n/p) * L"
        by (simp add: powr_powr)
      finally have "(n + 1) / L \<le> (p+1) powr (n/p)"
        by (simp add: divide_simps)
      then have "ln ((n + 1) / L) \<le> ln (real (p + 1) powr (real n / real p))"
        by (simp add: flip: ln_powr)
      also have "\<dots> \<le> (n/p) * ln(p+1)"
        by (simp add: powr_def)
      finally have "ln ((n + 1) / L) \<le> (n/p) * ln(p+1) \<and> L > 0"
        by fastforce
    } note * = this
    then have [simp]: "L > 0"
      by blast
    have 0: "(\<lambda>p. (n/p) * ln(p+1)) \<longlonglongrightarrow> 0"
      by real_asymp
    have "ln (real (n + 1) / L) \<le> 0"
      using * eventually_at_top_dense by (intro tendsto_lowerbound [OF 0]) auto
    then have "n+1 \<le> L"
      using \<open>0 < L\<close> by (simp add: ln_div)
    then show ?thesis
      using L_le by linarith
  qed
  with Kronecker_simult_aux2 [of n \<theta> \<alpha>] \<open>\<epsilon> > 0\<close> that show thesis
    by (auto simp: F_def L_def add.commute diff_diff_eq)
qed


text \<open>Theorem 7.10\<close>

corollary Kronecker_thm_2:
  fixes \<alpha> \<theta> :: "nat \<Rightarrow> real" and n :: nat
  assumes indp: "module.independent (\<lambda>r x. of_int r * x) (\<theta> ` {..n})"
    and inj\<theta>: "inj_on \<theta> {..n}" and [simp]: "\<theta> n = 1" and "\<epsilon> > 0"
  obtains k m where "\<And>i. i < n \<Longrightarrow> \<bar>of_int k * \<theta> i - of_int (m i) - \<alpha> i\<bar> < \<epsilon>"
proof -
  interpret Modules.module "(\<lambda>r. (*) (real_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  have one_in_\<theta>: "1 \<in> \<theta> ` {..n}"
    unfolding \<open>\<theta> n = 1\<close>[symmetric] by blast

  have not_in_Ints: "\<theta> i \<notin> \<int>" if i: "i < n" for i
  proof
    assume "\<theta> i \<in> \<int>"
    then obtain m where m: "\<theta> i = of_int m"
      by (auto elim!: Ints_cases)
    have not_one: "\<theta> i \<noteq> 1"
      using inj_onD[OF inj\<theta>, of i n] i by auto
    define u :: "real \<Rightarrow> int" where "u = (\<lambda>_. 0)(\<theta> i := 1, 1 := -m)"
    show False
      using independentD[OF indp, of "\<theta> ` {i, n}" u "\<theta> i"] \<open>i < n\<close> not_one one_in_\<theta>
      by (auto simp: u_def simp flip: m)
  qed

  have inj\<theta>': "inj_on (frac \<circ> \<theta>) {..n}"
  proof (rule linorder_inj_onI')
    fix i j assume ij: "i \<in> {..n}" "j \<in> {..n}" "i < j"
    show "(frac \<circ> \<theta>) i \<noteq> (frac \<circ> \<theta>) j"
    proof (cases "j = n")
      case True
      thus ?thesis
        using not_in_Ints[of i] ij by auto
    next
      case False
      hence "j < n"
        using ij by auto
      have "inj_on \<theta> (set [i, j, n])"
        using inj\<theta> by (rule inj_on_subset) (use ij in auto)
      moreover have "distinct [i, j, n]"
        using \<open>j < n\<close> ij by auto
      ultimately have "distinct (map \<theta> [i, j, n])"
        unfolding distinct_map by blast
      hence distinct: "distinct [\<theta> i, \<theta> j, 1]"
        by simp

      show "(frac \<circ> \<theta>) i \<noteq> (frac \<circ> \<theta>) j"
      proof
        assume eq: "(frac \<circ> \<theta>) i = (frac \<circ> \<theta>) j"
        define u :: "real \<Rightarrow> int" where "u = (\<lambda>_. 0)(\<theta> i := 1, \<theta> j := -1, 1 := \<lfloor>\<theta> j\<rfloor> - \<lfloor>\<theta> i\<rfloor>)"
        have "(\<Sum>v\<in>{\<theta> i, \<theta> j, 1}. real_of_int (u v) * v) = frac (\<theta> i) - frac (\<theta> j)"
          using distinct by (simp add: u_def frac_def)
        also have "\<dots> = 0"
          using eq by simp
        finally have eq0: "(\<Sum>v\<in>{\<theta> i, \<theta> j, 1}. real_of_int (u v) * v) = 0" .
        show False
          using independentD[OF indp _ _ eq0, of "\<theta> i"] one_in_\<theta> ij distinct
          by (auto simp: u_def)
      qed
    qed
  qed

  have "frac (\<theta> n) = 0"
    by auto
  then have \<theta>no_int: "of_int r \<notin> \<theta> ` {..<n}" for r
    using inj\<theta>' frac_of_int  
    apply (simp add: inj_on_def Ball_def)
    by (metis \<open>frac (\<theta> n) = 0\<close> frac_of_int imageE le_less lessThan_iff less_irrefl)
  define \<theta>' where "\<theta>' \<equiv> (frac \<circ> \<theta>)(n:=1)"
  have [simp]: "{..<Suc n} \<inter> {x. x \<noteq> n} = {..<n}"
    by auto
  have \<theta>image[simp]: "\<theta> ` {..n} = insert 1 (\<theta> ` {..<n})"
    using lessThan_Suc lessThan_Suc_atMost by force
  have "module.independent (\<lambda>r. (*) (of_int r)) (\<theta>' ` {..<Suc n})"
    unfolding dependent_explicit \<theta>'_def
  proof clarsimp
    fix T u v
    assume T: "T \<subseteq> insert 1 ((\<lambda>i. frac (\<theta> i)) ` {..<n})"
      and "finite T"
      and uv_eq0: "(\<Sum>v\<in>T. of_int (u v) * v) = 0"
      and "v \<in> T"
    define invf where "invf \<equiv> inv_into {..<n} (frac \<circ> \<theta>)"
    have "inj_on (\<lambda>x. frac (\<theta> x)) {..<n}"
      using inj\<theta>' by (auto simp: inj_on_def)
    then have invf [simp]: "invf (frac (\<theta> i)) = i" if "i<n" for i
      using frac_lt_1 [of "\<theta> i"] that by (auto simp: invf_def o_def inv_into_f_eq [where x=i])
    define N where "N \<equiv> invf ` (T - {1})"
    have Nsub: "N \<subseteq> {..n}" and "finite N"
      using T \<open>finite T\<close> by (auto simp: N_def subset_iff)
    have inj_invf: "inj_on invf (T - {1})"
      using \<theta>no_int [of 1] \<open>\<theta> n = 1\<close> inv_into_injective T
      by (fastforce simp: inj_on_def invf_def)
    have invf_iff: "invf t = i \<longleftrightarrow> (i<n \<and> t = frac (\<theta> i))" if "t \<in> T-{1}" for i t
      using that T by auto
    have sumN: "(\<Sum>i\<in>N. f i) = (\<Sum>x\<in>T - {1}. f (invf x))" for f :: "nat \<Rightarrow> int"
      using inj_invf T  by (simp add: N_def sum.reindex)
    define T' where "T' \<equiv> insert 1 (\<theta> ` N)"
    have [simp]: "finite T'" "1 \<in> T'"
      using T'_def N_def \<open>finite T\<close> by auto
    have T'sub: "T' \<subseteq> \<theta> ` {..n}"
      using Nsub T'_def \<theta>image by blast
    have in_N_not1: "x \<in> N \<Longrightarrow> \<theta> x \<noteq> 1" for x
      using \<theta>no_int [of 1] by (metis N_def image_iff invf_iff lessThan_iff of_int_1)
    define u' where "u' = (u \<circ> frac)(1:=(if 1\<in>T then u 1 else 0) + (\<Sum>i\<in>N. - \<lfloor>\<theta> i\<rfloor> * u (frac (\<theta> i))))"
    have "(\<Sum>v\<in>T'. real_of_int (u' v) * v) = u' 1 + (\<Sum>v \<in> \<theta> ` N. real_of_int (u' v) * v)"
      using \<open>finite N\<close> by (simp add: T'_def image_iff in_N_not1)
    also have "\<dots> = u' 1 + sum ((\<lambda>v. real_of_int (u' v) * v) \<circ> \<theta>) N"
      by (smt (verit) N_def \<open>finite N\<close> image_iff invf_iff sum.reindex_nontrivial)
    also have "\<dots> = u' 1 + (\<Sum>i\<in>N. of_int ((u \<circ> frac) (\<theta> i)) * \<theta> i)"
      by (auto simp add: u'_def in_N_not1)
    also have "\<dots> = u' 1 + (\<Sum>i\<in>N. of_int ((u \<circ> frac) (\<theta> i)) * (floor (\<theta> i) + frac(\<theta> i)))"
      by (simp add: frac_def cong: if_cong)
    also have "\<dots> = (\<Sum>v\<in>T. of_int (u v) * v)"
    proof (cases "1 \<in> T")
      case True
      then have T1: "(\<Sum>v\<in>T. real_of_int (u v) * v) = u 1 + (\<Sum>v\<in>T-{1}. real_of_int (u v) * v)"
        by (simp add: \<open>finite T\<close> sum.remove)
      show ?thesis
        using inj_invf True T unfolding N_def u'_def
        by (auto simp: add.assoc distrib_left sum.reindex T1 simp flip: sum.distrib intro!: sum.cong)
    next
      case False
      then show ?thesis
        using inj_invf T unfolding N_def u'_def
        by (auto simp: algebra_simps sum.reindex simp flip: sum.distrib intro!: sum.cong)
    qed
    also have "\<dots> = 0"
      using uv_eq0 by blast
    finally have 0: "(\<Sum>v\<in>T'. real_of_int (u' v) * v) = 0" .
    have "u v = 0" if T'0: "\<And>v. v\<in>T' \<Longrightarrow> u' v = 0"
    proof -
      have [simp]: "u t = 0" if "t \<in> T - {1}" for t
      proof -
        have "\<theta> (invf t) \<in> T'"
          using N_def T'_def that by blast
        then show ?thesis
          using that T'0 [of "\<theta> (invf t)"]
          by (smt (verit, best) in_N_not1 N_def fun_upd_other imageI invf_iff o_apply u'_def)
      qed
      show ?thesis
      proof (cases "v = 1")
        case True
        then have "1 \<in> T"
          using \<open>v \<in> T\<close> by blast
        have "(\<Sum>v\<in>T. real_of_int (u v) * v) = u 1 + (\<Sum>v\<in>T - {1}. real_of_int (u v) * v)"
          using True \<open>finite T\<close> \<open>v \<in> T\<close> mk_disjoint_insert by fastforce
        then have "0 = u 1"
          using uv_eq0 by auto
        with True show ?thesis by presburger
      next
        case False
        then have "\<theta> (invf v) \<in> \<theta> ` N"
          using N_def \<open>v \<in> T\<close> by blast
        then show ?thesis
          using that [of "\<theta> (invf v)"] False \<open>v \<in> T\<close> T by (force simp: T'_def in_N_not1 u'_def)
      qed
    qed
    with indp T'sub \<open>finite T'\<close> 0 show "u v = 0"
      unfolding dependent_explicit by blast
  qed
  moreover have "inj_on \<theta>' {..<Suc n}"
    using inj\<theta>' 
    unfolding \<theta>'_def inj_on_def 
    by (metis comp_def frac_lt_1 fun_upd_other fun_upd_same lessThan_Suc_atMost less_irrefl)
  ultimately obtain t h where th: "\<And>i. i < Suc n \<Longrightarrow> \<bar>t * \<theta>' i - of_int (h i) - (\<alpha>(n:=0)) i\<bar> < \<epsilon>/2"
    using Kronecker_thm_1 [of \<theta>' "Suc n" "\<epsilon>/2"] lessThan_Suc_atMost assms using half_gt_zero by blast
  define k where "k = h n"
  define m where "m \<equiv> \<lambda>i. h i + k * \<lfloor>\<theta> i\<rfloor>"
  show thesis
  proof
    fix i assume "i < n"
    have "\<bar>k * frac (\<theta> i) - h i - \<alpha> i\<bar> < \<epsilon>" 
    proof -
      have "\<bar>k * frac (\<theta> i) - h i - \<alpha> i\<bar> = \<bar>t * frac (\<theta> i) - h i - \<alpha> i + (k-t) * frac (\<theta> i)\<bar>"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> \<bar>t * frac (\<theta> i) - h i - \<alpha> i\<bar> + \<bar>(k-t) * frac (\<theta> i)\<bar>"
        by linarith
      also have "\<dots> \<le> \<bar>t * frac (\<theta> i) - h i - \<alpha> i\<bar> + \<bar>k-t\<bar>"
        using frac_lt_1 [of "\<theta> i"] le_less by (fastforce simp add: abs_mult)
      also have "\<dots> < \<epsilon>"
        using th[of i] th[of n] \<open>i<n\<close> 
        by (simp add: k_def \<theta>'_def) (smt (verit, best))
      finally show ?thesis .
    qed
    then show "\<bar>k * \<theta> i - m i - \<alpha> i\<bar> < \<epsilon>"
      by (simp add: algebra_simps frac_def m_def)
  qed
qed
(* TODO: use something like module.independent_family instead *)


end

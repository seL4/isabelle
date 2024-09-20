(*
  Title:      HOL/Computational_Algebra/Formal_Laurent_Series.thy
  Author:     Jeremy Sylvestre, University of Alberta (Augustana Campus)
*)


section \<open>A formalization of formal Laurent series\<close>

theory Formal_Laurent_Series
imports
  Polynomial_FPS
begin


subsection \<open>The type of formal Laurent series\<close>

subsubsection \<open>Type definition\<close>

typedef (overloaded) 'a fls = "{f::int \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n::nat. f (- int n) = 0}"
  morphisms fls_nth Abs_fls
proof
  show "(\<lambda>x. 0) \<in> {f::int \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n::nat. f (- int n) = 0}"
    by simp
qed

setup_lifting type_definition_fls

unbundle fps_notation
notation fls_nth (infixl \<open>$$\<close> 75)

lemmas fls_eqI = iffD1[OF fls_nth_inject, OF iffD2, OF fun_eq_iff, OF allI]

lemma fls_eq_iff: "f = g \<longleftrightarrow> (\<forall>n. f $$ n = g $$ n)"
  by (simp add: fls_nth_inject[symmetric] fun_eq_iff)

lemma nth_Abs_fls [simp]: "\<forall>\<^sub>\<infinity>n. f (- int n) = 0 \<Longrightarrow> Abs_fls f $$ n = f n"
 by (simp add: Abs_fls_inverse[OF CollectI])

lemmas nth_Abs_fls_finite_nonzero_neg_nth = nth_Abs_fls[OF iffD2, OF eventually_cofinite]
lemmas nth_Abs_fls_ex_nat_lower_bound = nth_Abs_fls[OF iffD2, OF MOST_nat]
lemmas nth_Abs_fls_nat_lower_bound = nth_Abs_fls_ex_nat_lower_bound[OF exI]

lemma nth_Abs_fls_ex_lower_bound:
  assumes "\<exists>N. \<forall>n<N. f n = 0"
  shows   "Abs_fls f $$ n = f n"
proof (intro nth_Abs_fls_ex_nat_lower_bound)
  from assms obtain N::int where "\<forall>n<N. f n = 0" by fast
  hence "\<forall>n > (if N < 0 then nat (-N) else 0). f (-int n) = 0" by auto
  thus "\<exists>M. \<forall>n>M. f (- int n) = 0" by fast
qed

lemmas nth_Abs_fls_lower_bound = nth_Abs_fls_ex_lower_bound[OF exI]

lemmas MOST_fls_neg_nth_eq_0 [simp] = CollectD[OF fls_nth]
lemmas fls_finite_nonzero_neg_nth = iffD1[OF eventually_cofinite MOST_fls_neg_nth_eq_0]

lemma fls_nth_vanishes_below_natE:
  fixes   f :: "'a::zero fls"
  obtains N :: nat
  where   "\<forall>n>N. f$$(-int n) = 0"
  using   iffD1[OF MOST_nat MOST_fls_neg_nth_eq_0]
  by      blast

lemma fls_nth_vanishes_belowE:
  fixes   f :: "'a::zero fls"
  obtains N :: int
  where   "\<forall>n<N. f$$n = 0"
proof-
  obtain K :: nat where K: "\<forall>n>K. f$$(-int n) = 0" by (elim fls_nth_vanishes_below_natE)
  have "\<forall>n < -int K. f$$n = 0"
  proof clarify
    fix n assume n: "n < -int K"
    define m where "m \<equiv> nat (-n)"
    with n have "m > K" by simp
    moreover from n m_def have "f$$n = f $$ (-int m)" by simp
    ultimately show "f $$ n = 0" using K by simp
  qed
  thus "(\<And>N. \<forall>n<N. f $$ n = 0 \<Longrightarrow> thesis) \<Longrightarrow> thesis" by fast
qed


subsubsection \<open>Definition of basic Laurent series\<close>

instantiation fls :: (zero) zero
begin
  lift_definition zero_fls :: "'a fls" is "\<lambda>_. 0" by simp
  instance ..
end

lemma fls_zero_nth [simp]: "0 $$ n = 0"
 by (simp add: zero_fls_def)

lemma fls_zero_eqI: "(\<And>n. f$$n = 0) \<Longrightarrow> f = 0"
  by (fastforce intro: fls_eqI)

lemma fls_nonzeroI: "f$$n \<noteq> 0 \<Longrightarrow> f \<noteq> 0"
  by auto

lemma fls_nonzero_nth: "f \<noteq> 0 \<longleftrightarrow> (\<exists> n. f $$ n \<noteq> 0)"
  using fls_zero_eqI by fastforce

lemma fls_trivial_delta_eq_zero [simp]: "b = 0 \<Longrightarrow> Abs_fls (\<lambda>n. if n=a then b else 0) = 0"
  by (intro fls_zero_eqI) simp

lemma fls_delta_nth [simp]:
  "Abs_fls (\<lambda>n. if n=a then b else 0) $$ n = (if n=a then b else 0)"
  using nth_Abs_fls_lower_bound[of a "\<lambda>n. if n=a then b else 0"] by simp

instantiation fls :: ("{zero,one}") one
begin
  lift_definition one_fls :: "'a fls" is "\<lambda>k. if k = 0 then 1 else 0"
    by (simp add: eventually_cofinite)
  instance ..
end

lemma fls_one_nth [simp]:
  "1 $$ n = (if n = 0 then 1 else 0)"
  by (simp add: one_fls_def eventually_cofinite)

instance fls :: (zero_neq_one) zero_neq_one
proof (standard, standard)
  assume "(0::'a fls) = (1::'a fls)"
  hence "(0::'a fls) $$ 0 = (1::'a fls) $$ 0" by simp
  thus False by simp
qed

definition fls_const :: "'a::zero \<Rightarrow> 'a fls"
  where "fls_const c \<equiv> Abs_fls (\<lambda>n. if n = 0 then c else 0)"

lemma fls_const_nth [simp]: "fls_const c $$ n = (if n = 0 then c else 0)"
  by (simp add: fls_const_def eventually_cofinite)

lemma fls_const_0 [simp]: "fls_const 0 = 0"
  unfolding fls_const_def using fls_trivial_delta_eq_zero by fast

lemma fls_const_nonzero: "c \<noteq> 0 \<Longrightarrow> fls_const c \<noteq> 0"
  using fls_nonzeroI[of "fls_const c" 0] by simp

lemma fls_const_eq_0_iff [simp]: "fls_const c = 0 \<longleftrightarrow> c = 0"
  by (auto simp: fls_eq_iff)

lemma fls_const_1 [simp]: "fls_const 1 = 1"
  unfolding fls_const_def one_fls_def ..

lemma fls_const_eq_1_iff [simp]: "fls_const c = 1 \<longleftrightarrow> c = 1"
  by (auto simp: fls_eq_iff)

lift_definition fls_X :: "'a::{zero,one} fls"
  is "\<lambda>n. if n = 1 then 1 else 0"
  by simp

lemma fls_X_nth [simp]:
  "fls_X $$ n = (if n = 1 then 1 else 0)"
  by (simp add: fls_X_def)

lemma fls_X_nonzero [simp]: "(fls_X :: 'a :: zero_neq_one fls) \<noteq> 0"
  by (intro fls_nonzeroI) simp

lift_definition fls_X_inv :: "'a::{zero,one} fls"
  is "\<lambda>n. if n = -1 then 1 else 0"
  by (simp add: eventually_cofinite)

lemma fls_X_inv_nth [simp]:
  "fls_X_inv $$ n = (if n = -1 then 1 else 0)"
  by (simp add: fls_X_inv_def eventually_cofinite)

lemma fls_X_inv_nonzero [simp]: "(fls_X_inv :: 'a :: zero_neq_one fls) \<noteq> 0"
  by (intro fls_nonzeroI) simp


subsection \<open>Subdegrees\<close>

lemma unique_fls_subdegree:
  assumes "f \<noteq> 0"
  shows   "\<exists>!n. f$$n \<noteq> 0 \<and> (\<forall>m. f$$m \<noteq> 0 \<longrightarrow> n \<le> m)"
proof-
  obtain N::nat where N: "\<forall>n>N. f$$(-int n) = 0" by (elim fls_nth_vanishes_below_natE)
  define M where "M \<equiv> -int N"
  have M: "\<And>m. f$$m \<noteq> 0 \<Longrightarrow> M \<le> m"
  proof-
    fix m assume m: "f$$m \<noteq> 0"
    show "M \<le> m"
    proof (cases "m<0")
      case True with m N M_def show ?thesis
        using allE[OF N, of "nat (-m)" False] by force
    qed (simp add: M_def)
  qed
  have "\<not> (\<forall>k::nat. f$$(M + int k) = 0)"
  proof
    assume above0: "\<forall>k::nat. f$$(M + int k) = 0"
    have "f=0"
    proof (rule fls_zero_eqI)
      fix n show "f$$n = 0"
      proof (cases "M \<le> n")
        case True
        define k where "k = nat (n - M)"
        from True have "n = M + int k" by (simp add: k_def)
        with above0 show ?thesis by simp
      next
        case False with M show ?thesis by auto
      qed
    qed
    with assms show False by fast
  qed
  hence ex_k: "\<exists>k::nat. f$$(M + int k) \<noteq> 0" by fast
  define k where "k \<equiv> (LEAST k::nat. f$$(M + int k) \<noteq> 0)"
  define n where "n \<equiv> M + int k"
  from k_def n_def have fn: "f$$n \<noteq> 0" using LeastI_ex[OF ex_k] by simp
  moreover have "\<forall>m. f$$m \<noteq> 0 \<longrightarrow> n \<le> m"
  proof (clarify)
    fix m assume m: "f$$m \<noteq> 0"
    with M have "M \<le> m" by fast
    define l where "l = nat (m - M)"
    from \<open>M \<le> m\<close> have l: "m = M + int l" by (simp add: l_def)
    with n_def m k_def l show "n \<le> m"
      using Least_le[of "\<lambda>k. f$$(M + int k) \<noteq> 0" l] by auto
  qed
  moreover have "\<And>n'. f$$n' \<noteq> 0 \<Longrightarrow> (\<forall>m. f$$m \<noteq> 0 \<longrightarrow> n' \<le> m) \<Longrightarrow> n' = n"
  proof-
    fix n' :: int
    assume n': "f$$n' \<noteq> 0" "\<forall>m. f$$m \<noteq> 0 \<longrightarrow> n' \<le> m"
    from n'(1) M have "M \<le> n'" by fast
    define l where "l = nat (n' - M)"
    from \<open>M \<le> n'\<close> have l: "n' = M + int l" by (simp add: l_def)
    with n_def k_def n' fn show "n' = n"
      using Least_le[of "\<lambda>k. f$$(M + int k) \<noteq> 0" l] by force
  qed
  ultimately show ?thesis
    using ex1I[of "\<lambda>n. f$$n \<noteq> 0 \<and> (\<forall>m. f$$m \<noteq> 0 \<longrightarrow> n \<le> m)" n] by blast
qed

definition fls_subdegree :: "('a::zero) fls \<Rightarrow> int"
  where "fls_subdegree f \<equiv> (if f = 0 then 0 else LEAST n::int. f$$n \<noteq> 0)"

lemma fls_zero_subdegree [simp]: "fls_subdegree 0 = 0"
  by (simp add: fls_subdegree_def)

lemma nth_fls_subdegree_nonzero [simp]: "f \<noteq> 0 \<Longrightarrow> f $$ fls_subdegree f \<noteq> 0"
  using Least1I[OF unique_fls_subdegree] by (simp add: fls_subdegree_def)

lemma nth_fls_subdegree_zero_iff: "(f $$ fls_subdegree f = 0) \<longleftrightarrow> (f = 0)"
  using nth_fls_subdegree_nonzero by auto

lemma fls_subdegree_leI: "f $$ n \<noteq> 0 \<Longrightarrow> fls_subdegree f \<le> n"
  using Least1_le[OF unique_fls_subdegree]
  by    (auto simp: fls_subdegree_def)

lemma fls_subdegree_leI': "f $$ n \<noteq> 0 \<Longrightarrow> n \<le> m \<Longrightarrow> fls_subdegree f \<le> m"
  using fls_subdegree_leI by fastforce

lemma fls_eq0_below_subdegree [simp]: "n < fls_subdegree f \<Longrightarrow> f $$ n = 0"
  using fls_subdegree_leI by fastforce

lemma fls_subdegree_geI: "f \<noteq> 0 \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> f $$ k = 0) \<Longrightarrow> n \<le> fls_subdegree f"
  using nth_fls_subdegree_nonzero by force

lemma fls_subdegree_ge0I: "(\<And>k. k < 0 \<Longrightarrow> f $$ k = 0) \<Longrightarrow> 0 \<le> fls_subdegree f"
  using fls_subdegree_geI[of f 0] by (cases "f=0") auto

lemma fls_subdegree_greaterI:
  assumes "f \<noteq> 0" "\<And>k. k \<le> n \<Longrightarrow> f $$ k = 0"
  shows   "n < fls_subdegree f"
  using   assms(1) assms(2)[of "fls_subdegree f"] nth_fls_subdegree_nonzero[of f]
  by      force

lemma fls_subdegree_eqI: "f $$ n \<noteq> 0 \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> f $$ k = 0) \<Longrightarrow> fls_subdegree f = n"
  using fls_subdegree_leI fls_subdegree_geI[of f]
  by    fastforce

lemma fls_delta_subdegree [simp]:
  "b \<noteq> 0 \<Longrightarrow> fls_subdegree (Abs_fls (\<lambda>n. if n=a then b else 0)) = a"
  by (intro fls_subdegree_eqI) simp_all

lemma fls_delta0_subdegree: "fls_subdegree (Abs_fls (\<lambda>n. if n=0 then a else 0)) = 0"
  by (cases "a=0") simp_all

lemma fls_one_subdegree [simp]: "fls_subdegree 1 = 0"
  by (auto intro: fls_delta0_subdegree simp: one_fls_def)

lemma fls_const_subdegree [simp]: "fls_subdegree (fls_const c) = 0"
  by (cases "c=0") (auto intro: fls_subdegree_eqI)

lemma fls_X_subdegree [simp]: "fls_subdegree (fls_X::'a::{zero_neq_one} fls) = 1"
  by (intro fls_subdegree_eqI) simp_all

lemma fls_X_inv_subdegree [simp]: "fls_subdegree (fls_X_inv::'a::{zero_neq_one} fls) = -1"
  by (intro fls_subdegree_eqI) simp_all

lemma fls_eq_above_subdegreeI:
  assumes "N \<le> fls_subdegree f" "N \<le> fls_subdegree g" "\<forall>k\<ge>N. f $$ k = g $$ k"
  shows   "f = g"
proof (rule fls_eqI)
  fix n from assms show "f $$ n = g $$ n" by (cases "n < N") auto
qed


subsection \<open>Shifting\<close>

subsubsection \<open>Shift definition\<close>

definition fls_shift :: "int \<Rightarrow> ('a::zero) fls \<Rightarrow> 'a fls"
  where "fls_shift n f \<equiv> Abs_fls (\<lambda>k. f $$ (k+n))"
\<comment> \<open>Since the index set is unbounded in both directions, we can shift in either direction.\<close>

lemma fls_shift_nth [simp]: "fls_shift m f $$ n = f $$ (n+m)"
  unfolding fls_shift_def
proof (rule nth_Abs_fls_ex_lower_bound)
  obtain K::int where K: "\<forall>n<K. f$$n = 0" by (elim fls_nth_vanishes_belowE)
  hence "\<forall>n<K-m. f$$(n+m) = 0" by auto
  thus "\<exists>N. \<forall>n<N. f $$ (n + m) = 0" by fast
qed

lemma fls_shift_eq_iff: "(fls_shift m f = fls_shift m g) \<longleftrightarrow> (f = g)"
proof (rule iffI, rule fls_eqI)
  fix k
  assume 1: "fls_shift m f = fls_shift m g"
  have "f $$ k = fls_shift m g $$ (k - m)" by (simp add: 1[symmetric])  
  thus "f $$ k = g $$ k" by simp
qed (intro fls_eqI, simp)

lemma fls_shift_0 [simp]: "fls_shift 0 f = f"
  by (intro fls_eqI) simp

lemma fls_shift_subdegree [simp]:
  "f \<noteq> 0 \<Longrightarrow> fls_subdegree (fls_shift n f) = fls_subdegree f - n"
  by (intro fls_subdegree_eqI) simp_all

lemma fls_shift_fls_shift [simp]: "fls_shift m (fls_shift k f) = fls_shift (k+m) f"
  by (intro fls_eqI) (simp add: algebra_simps)

lemma fls_shift_fls_shift_reorder:
  "fls_shift m (fls_shift k f) = fls_shift k (fls_shift m f)"
  using fls_shift_fls_shift[of m k f] fls_shift_fls_shift[of k m f] by (simp add: add.commute)

lemma fls_shift_zero [simp]: "fls_shift m 0 = 0"
  by (intro fls_zero_eqI) simp

lemma fls_shift_eq0_iff: "fls_shift m f = 0 \<longleftrightarrow> f = 0"
  using fls_shift_eq_iff[of m f 0] by simp

lemma fls_shift_eq_1_iff: "fls_shift n f = 1 \<longleftrightarrow> f = fls_shift (-n) 1"
  by (metis add_minus_cancel fls_shift_eq_iff fls_shift_fls_shift)

lemma fls_shift_nonneg_subdegree: "m \<le> fls_subdegree f \<Longrightarrow> fls_subdegree (fls_shift m f) \<ge> 0"
  by (cases "f=0") (auto intro: fls_subdegree_geI)

lemma fls_shift_delta:
  "fls_shift m (Abs_fls (\<lambda>n. if n=a then b else 0)) = Abs_fls (\<lambda>n. if n=a-m then b else 0)"
  by (intro fls_eqI) simp

lemma fls_shift_const:
  "fls_shift m (fls_const c) = Abs_fls (\<lambda>n. if n=-m then c else 0)"
  by (intro fls_eqI) simp

lemma fls_shift_const_nth:
  "fls_shift m (fls_const c) $$ n = (if n=-m then c else 0)"
  by (simp add: fls_shift_const)

lemma fls_X_conv_shift_1: "fls_X = fls_shift (-1) 1"
  by (intro fls_eqI) simp

lemma fls_X_shift_to_one [simp]: "fls_shift 1 fls_X = 1"
  using fls_shift_fls_shift[of "-1" 1 1] by (simp add: fls_X_conv_shift_1)

lemma fls_X_inv_conv_shift_1: "fls_X_inv = fls_shift 1 1"
  by (intro fls_eqI) simp

lemma fls_X_inv_shift_to_one [simp]: "fls_shift (-1) fls_X_inv = 1"
  using fls_shift_fls_shift[of 1 "-1" 1] by (simp add: fls_X_inv_conv_shift_1)

lemma fls_X_fls_X_inv_conv:
  "fls_X = fls_shift (-2) fls_X_inv" "fls_X_inv = fls_shift 2 fls_X"
  by (simp_all add: fls_X_conv_shift_1 fls_X_inv_conv_shift_1)


subsubsection \<open>Base factor\<close>

text \<open>
  Similarly to the @{const unit_factor} for formal power series, we can decompose a formal Laurent
  series as a power of the implied variable times a series of subdegree 0.
  (See lemma @{text "fls_base_factor_X_power_decompose"}.)
  But we will call this something other @{const unit_factor}
  because it will not satisfy assumption @{text "is_unit_unit_factor"} of
  @{class semidom_divide_unit_factor}.
\<close>

definition fls_base_factor :: "('a::zero) fls \<Rightarrow> 'a fls"
  where fls_base_factor_def[simp]: "fls_base_factor f = fls_shift (fls_subdegree f) f"

lemma fls_base_factor_nth: "fls_base_factor f $$ n = f $$ (n + fls_subdegree f)"
  by simp

lemma fls_base_factor_nonzero [simp]: "f \<noteq> 0 \<Longrightarrow> fls_base_factor f \<noteq> 0"
  using fls_nonzeroI[of "fls_base_factor f" 0] by simp

lemma fls_base_factor_subdegree [simp]: "fls_subdegree (fls_base_factor f) = 0"
 by (cases "f=0") auto

lemma fls_base_factor_base [simp]:
  "fls_base_factor f $$ fls_subdegree (fls_base_factor f) = f $$ fls_subdegree f"
  using fls_base_factor_subdegree[of f] by simp

lemma fls_conv_base_factor_shift_subdegree:
  "f = fls_shift (-fls_subdegree f) (fls_base_factor f)"
  by simp

lemma fls_base_factor_idem:
  "fls_base_factor (fls_base_factor (f::'a::zero fls)) = fls_base_factor f"
  using fls_base_factor_subdegree[of f] by simp

lemma fls_base_factor_zero: "fls_base_factor (0::'a::zero fls) = 0"
  by simp

lemma fls_base_factor_zero_iff: "fls_base_factor (f::'a::zero fls) = 0 \<longleftrightarrow> f = 0"
proof
  have "fls_shift (-fls_subdegree f) (fls_shift (fls_subdegree f) f) = f" by simp
  thus "fls_base_factor f = 0 \<Longrightarrow> f=0" by simp
qed simp

lemma fls_base_factor_nth_0: "f \<noteq> 0 \<Longrightarrow> fls_base_factor f $$ 0 \<noteq> 0"
  by simp

lemma fls_base_factor_one: "fls_base_factor (1::'a::{zero,one} fls) = 1"
  by simp

lemma fls_base_factor_const: "fls_base_factor (fls_const c) = fls_const c"
  by simp

lemma fls_base_factor_delta:
  "fls_base_factor (Abs_fls (\<lambda>n. if n=a then c else 0)) = fls_const c"
  by  (cases "c=0") (auto intro: fls_eqI)

lemma fls_base_factor_X: "fls_base_factor (fls_X::'a::{zero_neq_one} fls) = 1"
   by simp

lemma fls_base_factor_X_inv: "fls_base_factor (fls_X_inv::'a::{zero_neq_one} fls) = 1"
   by simp

lemma fls_base_factor_shift [simp]: "fls_base_factor (fls_shift n f) = fls_base_factor f"
  by (cases "f=0") simp_all


subsection \<open>Conversion between formal power and Laurent series\<close>

subsubsection \<open>Converting Laurent to power series\<close>

text \<open>
  We can truncate a Laurent series at index 0 to create a power series, called the regular part.
\<close>

lift_definition fls_regpart :: "('a::zero) fls \<Rightarrow> 'a fps"
  is "\<lambda>f. Abs_fps (\<lambda>n. f (int n))"
  .

lemma fls_regpart_nth [simp]: "fls_regpart f $ n = f $$ (int n)"
  by (simp add: fls_regpart_def)

lemma fls_regpart_zero [simp]: "fls_regpart 0 = 0"
  by (intro fps_ext) simp

lemma fls_regpart_one [simp]: "fls_regpart 1 = 1"
  by (intro fps_ext) simp

lemma fls_regpart_Abs_fls:
  "\<forall>\<^sub>\<infinity>n. F (- int n) = 0 \<Longrightarrow> fls_regpart (Abs_fls F) = Abs_fps (\<lambda>n. F (int n))"
  by (intro fps_ext) auto

lemma fls_regpart_delta:
  "fls_regpart (Abs_fls (\<lambda>n. if n=a then b else 0)) =
    (if a < 0 then 0 else Abs_fps (\<lambda>n. if n=nat a then b else 0))"
  by (rule fps_ext, auto)

lemma fls_regpart_const [simp]: "fls_regpart (fls_const c) = fps_const c"
  by (intro fps_ext) simp

lemma fls_regpart_fls_X [simp]: "fls_regpart fls_X = fps_X"
  by (intro fps_ext) simp

lemma fls_regpart_fls_X_inv [simp]: "fls_regpart fls_X_inv = 0"
  by (intro fps_ext) simp

lemma fls_regpart_eq0_imp_nonpos_subdegree:
  assumes "fls_regpart f = 0"
  shows   "fls_subdegree f \<le> 0"
proof (cases "f=0")
  case False
  have "fls_subdegree f \<ge> 0 \<Longrightarrow> f $$ fls_subdegree f = 0"
  proof-
    assume "fls_subdegree f \<ge> 0"
    hence "f $$ (fls_subdegree f) = (fls_regpart f) $ (nat (fls_subdegree f))" by simp
    with assms show "f $$ (fls_subdegree f) = 0" by simp
  qed
  with False show ?thesis by fastforce
qed simp

lemma fls_subdegree_lt_fls_regpart_subdegree:
  "fls_subdegree f \<le> int (subdegree (fls_regpart f))"
  using fls_subdegree_leI nth_subdegree_nonzero[of "fls_regpart f"]
  by    (cases "(fls_regpart f) = 0")
        (simp_all add: fls_regpart_eq0_imp_nonpos_subdegree)

lemma fls_regpart_subdegree_conv:
  assumes "fls_subdegree f \<ge> 0"
  shows   "subdegree (fls_regpart f) = nat (fls_subdegree f)"
\<comment>\<open>
  This is the best we can do since if the subdegree is negative, we might still have the bad luck
  that the term at index 0 is equal to 0.
\<close>
proof (cases "f=0")
  case False with assms show ?thesis by (intro subdegreeI) simp_all
qed simp

lemma fls_eq_conv_fps_eqI:
  assumes "0 \<le> fls_subdegree f" "0 \<le> fls_subdegree g" "fls_regpart f = fls_regpart g"
  shows   "f = g"
proof (rule fls_eq_above_subdegreeI, rule assms(1), rule assms(2), clarify)
  fix k::int assume "0 \<le> k"
  with assms(3) show "f $$ k = g $$ k"
    using fls_regpart_nth[of f "nat k"] fls_regpart_nth[of g] by simp
qed

lemma fls_regpart_shift_conv_fps_shift:
  "m \<ge> 0 \<Longrightarrow> fls_regpart (fls_shift m f) = fps_shift (nat m) (fls_regpart f)"
  by (intro fps_ext) simp_all

lemma fps_shift_fls_regpart_conv_fls_shift:
  "fps_shift m (fls_regpart f) = fls_regpart (fls_shift m f)"
  by (intro fps_ext) simp_all

lemma fps_unit_factor_fls_regpart:
  "fls_subdegree f \<ge> 0 \<Longrightarrow> unit_factor (fls_regpart f) = fls_regpart (fls_base_factor f)"
  by (auto intro: fps_ext simp: fls_regpart_subdegree_conv)

text \<open>
  The terms below the zeroth form a polynomial in the inverse of the implied variable,
  called the principle part.
\<close>

lift_definition fls_prpart :: "('a::zero) fls \<Rightarrow> 'a poly"
  is "\<lambda>f. Abs_poly (\<lambda>n. if n = 0 then 0 else f (- int n))"
  .

lemma fls_prpart_coeff [simp]: "coeff (fls_prpart f) n = (if n = 0 then 0 else f $$ (- int n))"
proof-
  have "{x. (if x = 0 then 0 else f $$ - int x) \<noteq> 0} \<subseteq> {x. f $$ - int x \<noteq> 0}"
    by auto
  hence "finite {x. (if x = 0 then 0 else f $$ - int x) \<noteq> 0}"
    using fls_finite_nonzero_neg_nth[of f] by (simp add: rev_finite_subset)
  hence "coeff (fls_prpart f) = (\<lambda>n. if n = 0 then 0 else f $$ (- int n))"
    using Abs_poly_inverse[OF CollectI, OF iffD2, OF eventually_cofinite]
    by (simp add: fls_prpart_def)
  thus ?thesis by simp
qed

lemma fls_prpart_eq0_iff: "(fls_prpart f = 0) \<longleftrightarrow> (fls_subdegree f \<ge> 0)"
proof
  assume 1: "fls_prpart f = 0"
  show "fls_subdegree f \<ge> 0"
  proof (intro fls_subdegree_ge0I)
    fix k::int assume "k < 0"
    with 1 show "f $$ k = 0" using fls_prpart_coeff[of f "nat (-k)"] by simp
  qed
qed (intro poly_eqI, simp)

lemma fls_prpart0 [simp]: "fls_prpart 0 = 0"
  by (simp add: fls_prpart_eq0_iff)

lemma fls_prpart_one [simp]: "fls_prpart 1 = 0"
  by (simp add: fls_prpart_eq0_iff)

lemma fls_prpart_delta:
  "fls_prpart (Abs_fls (\<lambda>n. if n=a then b else 0)) =
    (if a<0 then Poly (replicate (nat (-a)) 0 @ [b]) else 0)"
  by (intro poly_eqI) (auto simp: nth_default_def nth_append)

lemma fls_prpart_const [simp]: "fls_prpart (fls_const c) = 0"
  by (simp add: fls_prpart_eq0_iff)

lemma fls_prpart_X [simp]: "fls_prpart fls_X = 0"
  by (intro poly_eqI) simp

lemma fls_prpart_X_inv: "fls_prpart fls_X_inv = [:0,1:]"
proof (intro poly_eqI)
  fix n show "coeff (fls_prpart fls_X_inv) n = coeff [:0,1:] n"
  proof (cases n)
    case (Suc i) thus ?thesis by (cases i) simp_all
  qed simp
qed

lemma degree_fls_prpart [simp]:
  "degree (fls_prpart f) = nat (-fls_subdegree f)"
proof (cases "f=0")
  case False show ?thesis unfolding degree_def
  proof (intro Least_equality)
    fix N assume N: "\<forall>i>N. coeff (fls_prpart f) i = 0"
    have "\<forall>i < -int N. f $$ i = 0"
    proof clarify
      fix i assume i: "i < -int N"
      hence "nat (-i) > N" by simp
      with N i show "f $$ i = 0" using fls_prpart_coeff[of f "nat (-i)"] by auto
    qed
    with False have "fls_subdegree f \<ge> -int N" using fls_subdegree_geI by auto
    thus "nat (- fls_subdegree f) \<le> N" by simp
  qed auto
qed simp

lemma fls_prpart_shift:
  assumes "m \<le> 0"
  shows   "fls_prpart (fls_shift m f) = pCons 0 (poly_shift (Suc (nat (-m))) (fls_prpart f))"
proof (intro poly_eqI)
  fix n
  define LHS RHS
    where "LHS \<equiv> fls_prpart (fls_shift m f)"
    and   "RHS \<equiv> pCons 0 (poly_shift (Suc (nat (-m))) (fls_prpart f))"
  show "coeff LHS n = coeff RHS n"
  proof (cases n)
    case (Suc k)
    from assms have 1: "-int (Suc k + nat (-m)) = -int (Suc k) + m" by simp
    have "coeff RHS n = f $$ (-int (Suc k) + m)"
      using arg_cong[OF 1, of "($$) f"] by (simp add: Suc RHS_def coeff_poly_shift)
    with Suc show ?thesis by (simp add: LHS_def)
  qed (simp add: LHS_def RHS_def)
qed

lemma fls_prpart_base_factor: "fls_prpart (fls_base_factor f) = 0"
  using fls_base_factor_subdegree[of f] by (simp add: fls_prpart_eq0_iff)

text \<open>The essential data of a formal Laurant series resides from the subdegree up.\<close>

abbreviation fls_base_factor_to_fps :: "('a::zero) fls \<Rightarrow> 'a fps"
  where "fls_base_factor_to_fps f \<equiv> fls_regpart (fls_base_factor f)"

lemma fls_base_factor_to_fps_conv_fps_shift:
  assumes "fls_subdegree f \<ge> 0"
  shows   "fls_base_factor_to_fps f = fps_shift (nat (fls_subdegree f)) (fls_regpart f)"
  by (simp add: assms fls_regpart_shift_conv_fps_shift)

lemma fls_base_factor_to_fps_nth:
  "fls_base_factor_to_fps f $ n = f $$ (fls_subdegree f + int n)"
  by (simp add: algebra_simps)

lemma fls_base_factor_to_fps_base: "f \<noteq> 0 \<Longrightarrow> fls_base_factor_to_fps f $ 0 \<noteq> 0"
  by simp

lemma fls_base_factor_to_fps_nonzero: "f \<noteq> 0 \<Longrightarrow> fls_base_factor_to_fps f \<noteq> 0"
  using fps_nonzeroI[of "fls_base_factor_to_fps f" 0] fls_base_factor_to_fps_base by simp

lemma fls_base_factor_to_fps_subdegree [simp]: "subdegree (fls_base_factor_to_fps f) = 0"
  by (cases "f=0") auto

lemma fls_base_factor_to_fps_trivial:
  "fls_subdegree f = 0 \<Longrightarrow> fls_base_factor_to_fps f = fls_regpart f"
  by simp

lemma fls_base_factor_to_fps_zero: "fls_base_factor_to_fps 0 = 0"
  by simp

lemma fls_base_factor_to_fps_one: "fls_base_factor_to_fps 1 = 1"
  by simp

lemma fls_base_factor_to_fps_delta:
  "fls_base_factor_to_fps (Abs_fls (\<lambda>n. if n=a then c else 0)) = fps_const c"
  using fls_base_factor_delta[of a c] by simp

lemma fls_base_factor_to_fps_const:
  "fls_base_factor_to_fps (fls_const c) = fps_const c"
  by simp

lemma fls_base_factor_to_fps_X:
  "fls_base_factor_to_fps (fls_X::'a::{zero_neq_one} fls) = 1"
  by simp

lemma fls_base_factor_to_fps_X_inv:
  "fls_base_factor_to_fps (fls_X_inv::'a::{zero_neq_one} fls) = 1"
  by simp

lemma fls_base_factor_to_fps_shift:
  "fls_base_factor_to_fps (fls_shift m f) = fls_base_factor_to_fps f"
  using fls_base_factor_shift[of m f] by simp

lemma fls_base_factor_to_fps_base_factor:
  "fls_base_factor_to_fps (fls_base_factor f) = fls_base_factor_to_fps f"
  using fls_base_factor_to_fps_shift by simp

lemma fps_unit_factor_fls_base_factor:
  "unit_factor (fls_base_factor_to_fps f) = fls_base_factor_to_fps f"
  using fls_base_factor_to_fps_subdegree[of f] by simp

subsubsection \<open>Converting power to Laurent series\<close>

text \<open>We can extend a power series by 0s below to create a Laurent series.\<close>

definition fps_to_fls :: "('a::zero) fps \<Rightarrow> 'a fls"
  where "fps_to_fls f \<equiv> Abs_fls (\<lambda>k::int. if k<0 then 0 else f $ (nat k))"

lemma fps_to_fls_nth [simp]:
  "(fps_to_fls f) $$ n = (if n < 0 then 0 else f$(nat n))"
  using     nth_Abs_fls_lower_bound[of 0 "(\<lambda>k::int. if k<0 then 0 else f $ (nat k))"]
  unfolding fps_to_fls_def
  by        simp

lemma fps_to_fls_eq_imp_fps_eq:
  assumes "fps_to_fls f = fps_to_fls g"
  shows   "f = g"
proof (intro fps_ext)
  fix n
  have "f $ n = fps_to_fls g $$ int n" by (simp add: assms[symmetric])
  thus "f $ n = g $ n" by simp
qed

lemma fps_to_fls_eq_iff [simp]: "fps_to_fls f = fps_to_fls g \<longleftrightarrow> f = g"
  using fps_to_fls_eq_imp_fps_eq by blast

lemma fps_zero_to_fls [simp]: "fps_to_fls 0 = 0"
  by (intro fls_zero_eqI) simp

lemma fps_to_fls_nonzeroI: "f \<noteq> 0 \<Longrightarrow> fps_to_fls f \<noteq> 0"
  using fps_to_fls_eq_imp_fps_eq[of f 0] by auto

lemma fps_one_to_fls [simp]: "fps_to_fls 1 = 1"
  by (intro fls_eqI) simp

lemma fps_to_fls_Abs_fps:
  "fps_to_fls (Abs_fps F) = Abs_fls (\<lambda>n. if n<0 then 0 else F (nat n))"
  using nth_Abs_fls_lower_bound[of 0 "(\<lambda>n::int. if n<0 then 0 else F (nat n))"]
  by    (intro fls_eqI) simp

lemma fps_delta_to_fls:
  "fps_to_fls (Abs_fps (\<lambda>n. if n=a then b else 0)) = Abs_fls (\<lambda>n. if n=int a then b else 0)"
  using fls_eqI[of _ "Abs_fls (\<lambda>n. if n=int a then b else 0)"] by force

lemma fps_const_to_fls [simp]: "fps_to_fls (fps_const c) = fls_const c"
  by (intro fls_eqI) simp

lemma fps_X_to_fls [simp]: "fps_to_fls fps_X = fls_X"
  by (fastforce intro: fls_eqI)

lemma fps_to_fls_eq_0_iff [simp]: "(fps_to_fls f = 0) \<longleftrightarrow> (f=0)"
  using fps_to_fls_nonzeroI by auto

lemma fps_to_fls_eq_1_iff [simp]: "fps_to_fls f = 1 \<longleftrightarrow> f = 1"
  using fps_to_fls_eq_iff by fastforce

lemma fls_subdegree_fls_to_fps_gt0: "fls_subdegree (fps_to_fls f) \<ge> 0"
proof (cases "f=0")
  case False show ?thesis
  proof (rule fls_subdegree_geI, rule fls_nonzeroI)
    from False show "fps_to_fls f $$ int (subdegree f) \<noteq> 0"
      by simp
  qed simp
qed simp

lemma fls_subdegree_fls_to_fps: "fls_subdegree (fps_to_fls f) = int (subdegree f)"
proof (cases "f=0")
  case False
  have "subdegree f = nat (fls_subdegree (fps_to_fls f))"
  proof (rule subdegreeI)
    from False show "f $ (nat (fls_subdegree (fps_to_fls f))) \<noteq> 0"
      using fls_subdegree_fls_to_fps_gt0[of f] nth_fls_subdegree_nonzero[of "fps_to_fls f"]
            fps_to_fls_nonzeroI[of f]
      by    simp
  next
    fix k assume k: "k < nat (fls_subdegree (fps_to_fls f))"
    thus "f $ k = 0"
      using fls_eq0_below_subdegree[of "int k" "fps_to_fls f"] by simp
  qed
  thus ?thesis by (simp add: fls_subdegree_fls_to_fps_gt0)
qed simp

lemma fps_shift_to_fls [simp]:
  "n \<le> subdegree f \<Longrightarrow> fps_to_fls (fps_shift n f) = fls_shift (int n) (fps_to_fls f)"
  by (auto intro: fls_eqI simp: nat_add_distrib nth_less_subdegree_zero)

lemma fls_base_factor_fps_to_fls: "fls_base_factor (fps_to_fls f) = fps_to_fls (unit_factor f)"
  using nth_less_subdegree_zero[of _ f]
  by    (auto intro: fls_eqI simp: fls_subdegree_fls_to_fps nat_add_distrib)

lemma fls_regpart_to_fls_trivial [simp]:
  "fls_subdegree f \<ge> 0 \<Longrightarrow> fps_to_fls (fls_regpart f) = f"
  by (intro fls_eqI) simp

lemma fls_regpart_fps_trivial [simp]: "fls_regpart (fps_to_fls f) = f"
  by (intro fps_ext) simp

lemma fps_to_fls_base_factor_to_fps:
  "fps_to_fls (fls_base_factor_to_fps f) = fls_base_factor f"
  by (intro fls_eqI) simp

lemma fls_conv_base_factor_to_fps_shift_subdegree:
  "f = fls_shift (-fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f))"
  using fps_to_fls_base_factor_to_fps[of f] fps_to_fls_base_factor_to_fps[of f] by simp

lemma fls_base_factor_to_fps_to_fls:
  "fls_base_factor_to_fps (fps_to_fls f) = unit_factor f"
  using fls_base_factor_fps_to_fls[of f] fls_regpart_fps_trivial[of "unit_factor f"]
  by    simp

lemma fls_as_fps:
  fixes f :: "'a :: zero fls" and n :: int
  assumes n: "n \<ge> -fls_subdegree f"
  obtains f' where "f = fls_shift n (fps_to_fls f')"
proof -
  have "fls_subdegree (fls_shift (- n) f) \<ge> 0"
    by (rule fls_shift_nonneg_subdegree) (use n in simp)
  hence "f = fls_shift n (fps_to_fls (fls_regpart (fls_shift (-n) f)))"
    by (subst fls_regpart_to_fls_trivial) simp_all
  thus ?thesis
    by (rule that)
qed

lemma fls_as_fps':
  fixes f :: "'a :: zero fls" and n :: int
  assumes n: "n \<ge> -fls_subdegree f"
  shows "\<exists>f'. f = fls_shift n (fps_to_fls f')"
  using fls_as_fps[OF assms] by metis

abbreviation
  "fls_regpart_as_fls f \<equiv> fps_to_fls (fls_regpart f)"
abbreviation
  "fls_prpart_as_fls f \<equiv>
    fls_shift (-fls_subdegree f) (fps_to_fls (fps_of_poly (reflect_poly (fls_prpart f))))"

lemma fls_regpart_as_fls_nth:
  "fls_regpart_as_fls f $$ n = (if n < 0 then 0 else f $$ n)"
  by simp

lemma fls_regpart_idem:
  "fls_regpart (fls_regpart_as_fls f) = fls_regpart f"
  by simp

lemma fls_prpart_as_fls_nth:
  "fls_prpart_as_fls f $$ n = (if n < 0 then f $$ n else 0)"
proof (cases "n < fls_subdegree f" "n < 0" rule: case_split[case_product case_split])
  case False_True
    hence "nat (-fls_subdegree f) - nat (n - fls_subdegree f) = nat (-n)" by auto
    with False_True show ?thesis
      using coeff_reflect_poly[of "fls_prpart f" "nat (n - fls_subdegree f)"] by auto
  next
    case False_False thus ?thesis
      using coeff_reflect_poly[of "fls_prpart f" "nat (n - fls_subdegree f)"] by auto
qed simp_all

lemma fls_prpart_idem [simp]: "fls_prpart (fls_prpart_as_fls f) = fls_prpart f"
  using fls_prpart_as_fls_nth[of f] by (intro poly_eqI) simp

lemma fls_regpart_prpart: "fls_regpart (fls_prpart_as_fls f) = 0"
  using fls_prpart_as_fls_nth[of f] by (intro fps_ext) simp

lemma fls_prpart_regpart: "fls_prpart (fls_regpart_as_fls f) = 0"
  by (intro poly_eqI) simp


subsection \<open>Algebraic structures\<close>

subsubsection \<open>Addition\<close>

instantiation fls :: (monoid_add) plus
begin
  lift_definition plus_fls :: "'a fls \<Rightarrow> 'a fls \<Rightarrow> 'a fls" is "\<lambda>f g n. f n + g n"
  proof-
    fix f f' :: "int \<Rightarrow> 'a"
    assume "\<forall>\<^sub>\<infinity>n. f (- int n) = 0" "\<forall>\<^sub>\<infinity>n. f' (- int n) = 0"
    from this obtain N N' where "\<forall>n>N. f (-int n) = 0" "\<forall>n>N'. f' (-int n) = 0"
      by (auto simp: MOST_nat)
    hence "\<forall>n > max N N'. f (-int n) + f' (-int n) = 0" by auto
    hence "\<exists>K. \<forall>n>K. f (-int n) + f' (-int n) = 0" by fast
    thus "\<forall>\<^sub>\<infinity>n. f (- int n) + f' (-int n) = 0" by (simp add: MOST_nat)
  qed
  instance ..
end

lemma fls_plus_nth [simp]: "(f + g) $$ n = f $$ n + g $$ n"
  by transfer simp

lemma fls_plus_const: "fls_const x + fls_const y = fls_const (x+y)"
  by (intro fls_eqI) simp

lemma fls_plus_subdegree:
  "f + g \<noteq> 0 \<Longrightarrow> fls_subdegree (f + g) \<ge> min (fls_subdegree f) (fls_subdegree g)"
  by (auto intro: fls_subdegree_geI)

lemma fls_shift_plus [simp]:
  "fls_shift m (f + g) = (fls_shift m f) + (fls_shift m g)"
  by (intro fls_eqI) simp

lemma fls_regpart_plus [simp]: "fls_regpart (f + g) = fls_regpart f + fls_regpart g"
  by (intro fps_ext) simp

lemma fls_prpart_plus [simp] : "fls_prpart (f + g) = fls_prpart f + fls_prpart g"
  by (intro poly_eqI) simp

lemma fls_decompose_reg_pr_parts:
  fixes   f :: "'a :: monoid_add fls"
  defines "R  \<equiv> fls_regpart_as_fls f"
  and     "P  \<equiv> fls_prpart_as_fls f"
  shows   "f = P + R"
  and     "f = R + P"
  using   fls_prpart_as_fls_nth[of f]
  by      (auto intro: fls_eqI simp add: assms)

lemma fps_to_fls_plus [simp]: "fps_to_fls (f + g) = fps_to_fls f + fps_to_fls g"
  by (intro fls_eqI) simp

instance fls :: (monoid_add) monoid_add
proof
  fix a b c :: "'a fls"
  show "a + b + c = a + (b + c)" by transfer (simp add: add.assoc)
  show "0 + a = a" by transfer simp
  show "a + 0 = a" by transfer simp
qed

instance fls :: (comm_monoid_add) comm_monoid_add
  by (standard, transfer, auto simp: add.commute)


subsubsection \<open>Subtraction and negatives\<close>

instantiation fls :: (group_add) minus
begin
  lift_definition minus_fls :: "'a fls \<Rightarrow> 'a fls \<Rightarrow> 'a fls" is "\<lambda>f g n. f n - g n"
  proof-
    fix f f' :: "int \<Rightarrow> 'a"
    assume "\<forall>\<^sub>\<infinity>n. f (- int n) = 0" "\<forall>\<^sub>\<infinity>n. f' (- int n) = 0"
    from this obtain N N' where "\<forall>n>N. f (-int n) = 0" "\<forall>n>N'. f' (-int n) = 0"
      by (auto simp: MOST_nat)
    hence "\<forall>n > max N N'. f (-int n) - f' (-int n) = 0" by auto
    hence "\<exists>K. \<forall>n>K. f (-int n) - f' (-int n) = 0" by fast
    thus "\<forall>\<^sub>\<infinity>n. f (- int n) - f' (-int n) = 0" by (simp add: MOST_nat)
  qed
  instance ..
end

lemma fls_minus_nth [simp]: "(f - g) $$ n = f $$ n - g $$ n"
  by transfer simp

lemma fls_minus_const: "fls_const x - fls_const y = fls_const (x-y)"
  by (intro fls_eqI) simp

lemma fls_subdegree_minus:
  "f - g \<noteq> 0 \<Longrightarrow> fls_subdegree (f - g) \<ge> min (fls_subdegree f) (fls_subdegree g)"
  by (intro fls_subdegree_geI) simp_all

lemma fls_shift_minus [simp]: "fls_shift m (f - g) = (fls_shift m f) - (fls_shift m g)"
  by (auto intro: fls_eqI)

lemma fls_regpart_minus [simp]: "fls_regpart (f - g) = fls_regpart f - fls_regpart g"
  by (intro fps_ext) simp

lemma fls_prpart_minus [simp] : "fls_prpart (f - g) = fls_prpart f - fls_prpart g"
  by (intro poly_eqI) simp

lemma fps_to_fls_minus [simp]: "fps_to_fls (f - g) = fps_to_fls f - fps_to_fls g"
  by (intro fls_eqI) simp

instantiation fls :: (group_add) uminus
begin
  lift_definition uminus_fls :: "'a fls \<Rightarrow> 'a fls" is "\<lambda>f n. - f n"
  proof-
    fix f :: "int \<Rightarrow> 'a" assume "\<forall>\<^sub>\<infinity>n. f (- int n) = 0"
    from this obtain N where "\<forall>n>N. f (-int n) = 0"
      by (auto simp: MOST_nat)
    hence "\<forall>n>N. - f (-int n) = 0" by auto
    hence "\<exists>K. \<forall>n>K. - f (-int n) = 0" by fast
    thus "\<forall>\<^sub>\<infinity>n. - f (- int n) = 0" by (simp add: MOST_nat)
  qed
  instance ..
end

lemma fls_uminus_nth [simp]: "(-f) $$ n = - (f $$ n)"
  by transfer simp

lemma fls_const_uminus[simp]: "fls_const (-x) = -fls_const x"
  by (intro fls_eqI) simp

lemma fls_shift_uminus [simp]: "fls_shift m (- f) = - (fls_shift m f)"
  by (auto intro: fls_eqI)

lemma fls_regpart_uminus [simp]: "fls_regpart (- f) = - fls_regpart f"
  by (intro fps_ext) simp

lemma fls_prpart_uminus [simp] : "fls_prpart (- f) = - fls_prpart f"
  by (intro poly_eqI) simp

lemma fps_to_fls_uminus [simp]: "fps_to_fls (- f) = - fps_to_fls f"
  by (intro fls_eqI) simp

instance fls :: (group_add) group_add
proof
  fix a b :: "'a fls"
  show "- a + a = 0" by transfer simp
  show "a + - b = a - b" by transfer simp
qed

instance fls :: (ab_group_add) ab_group_add
proof
  fix a b :: "'a fls"
  show "- a + a = 0" by transfer simp
  show "a - b = a + - b" by transfer simp
qed

lemma fls_uminus_subdegree [simp]: "fls_subdegree (-f) = fls_subdegree f"
  by (cases "f=0") (auto intro: fls_subdegree_eqI)

lemma fls_subdegree_minus_sym: "fls_subdegree (g - f) = fls_subdegree (f - g)"
  using fls_uminus_subdegree[of "g-f"] by (simp add: algebra_simps)

lemma fls_regpart_sub_prpart: "fls_regpart (f - fls_prpart_as_fls f) = fls_regpart f"
  using fls_decompose_reg_pr_parts(2)[of f]
        add_diff_cancel[of "fls_regpart_as_fls f" "fls_prpart_as_fls f"]
  by    simp

lemma fls_prpart_sub_regpart: "fls_prpart (f - fls_regpart_as_fls f) = fls_prpart f"
  using fls_decompose_reg_pr_parts(1)[of f]
        add_diff_cancel[of "fls_prpart_as_fls f" "fls_regpart_as_fls f"]
  by    simp


subsubsection \<open>Multiplication\<close>

instantiation fls :: ("{comm_monoid_add, times}") times
begin
  definition fls_times_def:
    "(*) = (\<lambda>f g.
      fls_shift
        (- (fls_subdegree f + fls_subdegree g))
        (fps_to_fls (fls_base_factor_to_fps f * fls_base_factor_to_fps g))
    )"
  instance ..
end

lemma fls_times_nth_eq0: "n < fls_subdegree f + fls_subdegree g \<Longrightarrow> (f * g) $$ n = 0"
  by (simp add: fls_times_def)

lemma fls_times_nth:
  fixes   f df g dg
  defines "df \<equiv> fls_subdegree f" and "dg \<equiv> fls_subdegree g"
  shows   "(f * g) $$ n = (\<Sum>i=df + dg..n. f $$ (i - dg) * g $$ (dg + n - i))"
  and     "(f * g) $$ n = (\<Sum>i=df..n - dg. f $$ i * g $$ (n - i))"
  and     "(f * g) $$ n = (\<Sum>i=dg..n - df. f $$ (df + i - dg) * g $$ (dg + n - df - i))"
  and     "(f * g) $$ n = (\<Sum>i=0..n - (df + dg). f $$ (df + i) * g $$ (n - df - i))"
proof-

  define dfg where "dfg \<equiv> df + dg"

  show 4: "(f * g) $$ n = (\<Sum>i=0..n - dfg. f $$ (df + i) * g $$ (n - df - i))"
  proof (cases "n < dfg")
    case False
    from False assms have
      "(f * g) $$ n =
        (\<Sum>i = 0..nat (n - dfg). f $$ (df + int i) * g $$ (dg + int (nat (n - dfg) - i)))"
      using fps_mult_nth[of "fls_base_factor_to_fps f" "fls_base_factor_to_fps g"]
            fls_base_factor_to_fps_nth[of f]
            fls_base_factor_to_fps_nth[of g]
      by    (simp add: dfg_def fls_times_def algebra_simps)
    moreover from False have index:
      "\<And>i. i \<in> {0..nat (n - dfg)} \<Longrightarrow> dg + int (nat (n - dfg) - i) = n - df - int i"
      by (auto simp: dfg_def)
    ultimately have
      "(f * g) $$ n = (\<Sum>i=0..nat (n - dfg). f $$ (df + int i) * g $$ (n - df - int i))"
      by (simp del: of_nat_diff)
    moreover have
      "(\<Sum>i=0..nat (n - dfg). f $$ (df + int i) *  g $$ (n - df - int i)) =
        (\<Sum>i=0..n - dfg. f $$ (df + i) *  g $$ (n - df - i))"
    proof (intro sum.reindex_cong)
      show "inj_on nat {0..n - dfg}" by standard auto
      show "{0..nat (n - dfg)} = nat ` {0..n - dfg}"
      proof
        show "{0..nat (n - dfg)} \<subseteq> nat ` {0..n - dfg}"
        proof
          fix i assume "i \<in> {0..nat (n - dfg)}"
          hence i: "i \<ge> 0" "i \<le> nat (n - dfg)" by auto
          with False have "int i \<ge> 0" "int i \<le> n - dfg" by auto
          hence "int i \<in> {0..n - dfg}" by simp
          moreover from i(1) have "i = nat (int i)" by simp
          ultimately show "i \<in> nat ` {0..n - dfg}" by fast
        qed
      qed (auto simp: False)
    qed (simp add: False)
    ultimately show "(f * g) $$ n = (\<Sum>i=0..n - dfg. f $$ (df + i) *  g $$ (n - df - i))"
      by simp
  qed (simp add: fls_times_nth_eq0 assms dfg_def)

  have
    "(\<Sum>i=dfg..n. f $$ (i - dg) *  g $$ (dg + n - i)) =
      (\<Sum>i=0..n - dfg. f $$ (df + i) *  g $$ (n - df - i))"
  proof (intro sum.reindex_cong)
    define T where "T \<equiv> \<lambda>i. i + dfg"
    show "inj_on T {0..n - dfg}" by standard (simp add: T_def)
  qed (simp_all add: dfg_def algebra_simps)
  with 4 show 1: "(f * g) $$ n = (\<Sum>i=dfg..n. f $$ (i - dg) *  g $$ (dg + n - i))"
    by simp

  have
    "(\<Sum>i=dfg..n. f $$ (i - dg) *  g $$ (dg + n - i)) = (\<Sum>i=df..n - dg. f $$ i *  g $$ (n - i))"
  proof (intro sum.reindex_cong)
    define T where "T \<equiv> \<lambda>i. i + dg"
    show "inj_on T {df..n - dg}" by standard (simp add: T_def)
  qed (auto simp: dfg_def)
  with 1 show "(f * g) $$ n = (\<Sum>i=df..n - dg. f $$ i *  g $$ (n - i))"
    by simp

  have
    "(\<Sum>i=dfg..n. f $$ (i - dg) *  g $$ (dg + n - i)) =
      (\<Sum>i=dg..n - df. f $$ (df + i - dg) *  g $$ (dg + n - df - i))"
  proof (intro sum.reindex_cong)
    define T where "T \<equiv> \<lambda>i. i + df"
    show "inj_on T {dg..n - df}" by standard (simp add: T_def)
  qed (simp_all add: dfg_def algebra_simps)
  with 1 show "(f * g) $$ n = (\<Sum>i=dg..n - df. f $$ (df + i - dg) *  g $$ (dg + n - df - i))"
    by simp

qed

lemma fls_times_base [simp]:
  "(f * g) $$ (fls_subdegree f + fls_subdegree g) =
    (f $$ fls_subdegree f) * (g $$ fls_subdegree g)"
  by (simp add: fls_times_nth(1))

instance fls :: ("{comm_monoid_add, mult_zero}") mult_zero
proof
  fix a :: "'a fls"
  have
    "(0::'a fls) * a =
      fls_shift (fls_subdegree a) (fps_to_fls ( (0::'a fps)*(fls_base_factor_to_fps a) ))"
    by (simp add: fls_times_def)
  moreover have
    "a * (0::'a fls) =
      fls_shift (fls_subdegree a) (fps_to_fls ( (fls_base_factor_to_fps a)*(0::'a fps) ))"
    by (simp add: fls_times_def)
  ultimately show "0 * a = (0::'a fls)" "a * 0 = (0::'a fls)"
    by auto
qed

lemma fls_mult_one:
  fixes f :: "'a::{comm_monoid_add, mult_zero, monoid_mult} fls"
  shows "1 * f = f"
  and   "f * 1 = f"
  using fls_conv_base_factor_to_fps_shift_subdegree[of f]
  by    (simp_all add: fls_times_def fps_one_mult)

lemma fls_mult_const_nth [simp]:
  fixes f :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "(fls_const x * f) $$ n = x * f$$n"
  and   "(f * fls_const x ) $$ n = f$$n * x"
proof-
  show "(fls_const x * f) $$ n = x * f$$n"
  proof (cases "n<fls_subdegree f")
    case False
    hence "{fls_subdegree f..n} = insert (fls_subdegree f) {fls_subdegree f+1..n}" by auto
    thus ?thesis by (simp add: fls_times_nth(1))
  qed (simp add: fls_times_nth_eq0)
  show "(f * fls_const x ) $$ n = f$$n * x"
  proof (cases "n<fls_subdegree f")
    case False
    hence "{fls_subdegree f..n} = insert n {fls_subdegree f..n-1}" by auto
    thus ?thesis by (simp add: fls_times_nth(1))
  qed (simp add: fls_times_nth_eq0)
qed

lemma fls_const_mult_const[simp]:
  fixes x y :: "'a::{comm_monoid_add, mult_zero}"
  shows "fls_const x * fls_const y = fls_const (x*y)"
  by    (intro fls_eqI) simp

lemma fls_mult_subdegree_ge:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "f*g \<noteq> 0"
  shows   "fls_subdegree (f*g) \<ge> fls_subdegree f + fls_subdegree g"
  by      (auto intro: fls_subdegree_geI simp: assms fls_times_nth_eq0)

lemma fls_mult_subdegree_ge_0:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0"
  shows   "fls_subdegree (f*g) \<ge> 0"
  using   assms fls_mult_subdegree_ge[of f g]
  by      fastforce

lemma fls_mult_nonzero_base_subdegree_eq:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "f $$ (fls_subdegree f) * g $$ (fls_subdegree g) \<noteq> 0"
  shows   "fls_subdegree (f*g) = fls_subdegree f + fls_subdegree g"
proof-
  from assms have "fls_subdegree (f*g) \<ge> fls_subdegree f + fls_subdegree g"
    using fls_nonzeroI[of "f*g" "fls_subdegree f + fls_subdegree g"]
          fls_mult_subdegree_ge[of f g]
    by    simp
  moreover from assms have "fls_subdegree (f*g) \<le> fls_subdegree f + fls_subdegree g"
    by (intro fls_subdegree_leI) simp
  ultimately show ?thesis by simp
qed

lemma fls_subdegree_mult [simp]:
  fixes   f g :: "'a::semiring_no_zero_divisors fls"
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows   "fls_subdegree (f * g) = fls_subdegree f + fls_subdegree g"
  using   assms
  by      (auto intro: fls_subdegree_eqI simp: fls_times_nth_eq0)

lemma fls_shifted_times_simps:
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "f * (fls_shift n g) = fls_shift n (f*g)" "(fls_shift n f) * g = fls_shift n (f*g)"
proof-

  show "f * (fls_shift n g) = fls_shift n (f*g)"
  proof (cases "g=0")
    case False
    hence
      "f * (fls_shift n g) =
        fls_shift (- (fls_subdegree f + (fls_subdegree g - n)))
          (fps_to_fls (fls_base_factor_to_fps f * fls_base_factor_to_fps g))"
      unfolding fls_times_def by (simp add: fls_base_factor_to_fps_shift)
    thus "f * (fls_shift n g) = fls_shift n (f*g)"
      by (simp add: algebra_simps fls_times_def)
  qed auto

  show "(fls_shift n f)*g = fls_shift n (f*g)"
  proof (cases "f=0")
    case False
    hence
      "(fls_shift n f)*g =
        fls_shift (- ((fls_subdegree f - n) + fls_subdegree g))
          (fps_to_fls (fls_base_factor_to_fps f * fls_base_factor_to_fps g))"
      unfolding fls_times_def by (simp add: fls_base_factor_to_fps_shift)
    thus "(fls_shift n f) * g = fls_shift n (f*g)"
      by (simp add: algebra_simps fls_times_def)
  qed auto

qed

lemma fls_shifted_times_transfer:
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "fls_shift n f * g = f * fls_shift n g"
  using fls_shifted_times_simps(1)[of f n g] fls_shifted_times_simps(2)[of n f g]
  by    simp

lemma fls_times_both_shifted_simp:
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "(fls_shift m f) * (fls_shift n g) = fls_shift (m+n) (f*g)"
  by    (simp add: fls_shifted_times_simps)

lemma fls_base_factor_mult_base_factor:
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "fls_base_factor (f * fls_base_factor g) = fls_base_factor (f * g)"
  and   "fls_base_factor (fls_base_factor f * g) = fls_base_factor (f * g)"
  using fls_base_factor_shift[of "fls_subdegree g" "f*g"]
        fls_base_factor_shift[of "fls_subdegree f" "f*g"]
  by    (simp_all add: fls_shifted_times_simps)

lemma fls_base_factor_mult_both_base_factor:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fls"
  shows "fls_base_factor (fls_base_factor f * fls_base_factor g) = fls_base_factor (f * g)"
  using fls_base_factor_mult_base_factor(1)[of "fls_base_factor f" g]
        fls_base_factor_mult_base_factor(2)[of f g]
  by    simp

lemma fls_base_factor_mult:
  fixes f g :: "'a::semiring_no_zero_divisors fls"
  shows "fls_base_factor (f * g) = fls_base_factor f * fls_base_factor g"
  by    (cases "f\<noteq>0 \<and> g\<noteq>0")
        (auto simp: fls_times_both_shifted_simp)

lemma fls_times_conv_base_factor_times:
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows
    "f * g =
      fls_shift (-(fls_subdegree f + fls_subdegree g)) (fls_base_factor f * fls_base_factor g)"
  by (simp add: fls_times_both_shifted_simp)

lemma fls_times_base_factor_conv_shifted_times:
\<comment> \<open>Convenience form of lemma @{text "fls_times_both_shifted_simp"}.\<close>
  fixes f g :: "'a::{comm_monoid_add, mult_zero} fls"
  shows
    "fls_base_factor f * fls_base_factor g = fls_shift (fls_subdegree f + fls_subdegree g) (f * g)"
  by (simp add: fls_times_both_shifted_simp)

lemma fls_times_conv_regpart:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0"
  shows "fls_regpart (f * g) = fls_regpart f * fls_regpart g"
proof-
  from assms have 1:
    "f * g =
      fls_shift (- (fls_subdegree f + fls_subdegree g)) (
        fps_to_fls (
          fps_shift (nat (fls_subdegree f) + nat (fls_subdegree g)) (
            fls_regpart f * fls_regpart g
          )
        )
      )"
    by (simp add:
      fls_times_def fls_base_factor_to_fps_conv_fps_shift[symmetric]
      fls_regpart_subdegree_conv fps_shift_mult_both[symmetric]
    )
  show ?thesis
  proof (cases "fls_regpart f * fls_regpart g = 0")
    case False
    with assms have
      "subdegree (fls_regpart f * fls_regpart g) \<ge>
        nat (fls_subdegree f) + nat (fls_subdegree g)"
      by (simp add: fps_mult_subdegree_ge fls_regpart_subdegree_conv[symmetric])
    with 1 assms show ?thesis by simp
  qed (simp add: 1)
qed

lemma fls_base_factor_to_fps_mult_conv_unit_factor:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fls"
  shows
    "fls_base_factor_to_fps (f * g) =
      unit_factor (fls_base_factor_to_fps f * fls_base_factor_to_fps g)"
  using fls_base_factor_mult_both_base_factor[of f g]
        fps_unit_factor_fls_regpart[of "fls_base_factor f * fls_base_factor g"]
        fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of g]
        fls_mult_subdegree_ge_0[of "fls_base_factor f" "fls_base_factor g"]
        fls_times_conv_regpart[of "fls_base_factor f" "fls_base_factor g"]
  by    simp

lemma fls_base_factor_to_fps_mult':
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "(f $$ fls_subdegree f) * (g $$ fls_subdegree g) \<noteq> 0"
  shows   "fls_base_factor_to_fps (f * g) = fls_base_factor_to_fps f * fls_base_factor_to_fps g"
  using   assms fls_mult_nonzero_base_subdegree_eq[of f g]
          fls_times_base_factor_conv_shifted_times[of f g]
          fls_times_conv_regpart[of "fls_base_factor f" "fls_base_factor g"]
          fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of g]
  by      fastforce

lemma fls_base_factor_to_fps_mult:
  fixes f g :: "'a::semiring_no_zero_divisors fls"
  shows "fls_base_factor_to_fps (f * g) = fls_base_factor_to_fps f * fls_base_factor_to_fps g"
  using fls_base_factor_to_fps_mult'[of f g]
  by    (cases "f=0 \<or> g=0") auto

lemma fls_times_conv_fps_times:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0"
  shows   "f * g = fps_to_fls (fls_regpart f * fls_regpart g)"
  using   assms fls_mult_subdegree_ge[of f g]
  by      (cases "f * g = 0") (simp_all add: fls_times_conv_regpart[symmetric])

lemma fps_times_conv_fls_times:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  shows   "f * g = fls_regpart (fps_to_fls f * fps_to_fls g)"
  using   fls_subdegree_fls_to_fps_gt0 fls_times_conv_regpart[symmetric]
  by      fastforce

lemma fls_times_fps_to_fls:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fps"
  shows "fps_to_fls (f * g) = fps_to_fls f * fps_to_fls g"
proof (intro fls_eq_conv_fps_eqI, rule fls_subdegree_fls_to_fps_gt0)
  show "fls_subdegree (fps_to_fls f * fps_to_fls g) \<ge> 0"
  proof (cases "fps_to_fls f * fps_to_fls g = 0")
    case False thus ?thesis
      using fls_mult_subdegree_ge fls_subdegree_fls_to_fps_gt0[of f]
            fls_subdegree_fls_to_fps_gt0[of g]
      by    fastforce
  qed simp
qed (simp add: fps_times_conv_fls_times)

lemma fls_X_times_conv_shift:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  shows "fls_X * f = fls_shift (-1) f" "f * fls_X = fls_shift (-1) f"
  by    (simp_all add: fls_X_conv_shift_1 fls_mult_one fls_shifted_times_simps)

lemmas fls_X_times_comm = trans_sym[OF fls_X_times_conv_shift]   

lemma fls_subdegree_mult_fls_X:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  assumes "f \<noteq> 0"
  shows   "fls_subdegree (fls_X * f) = fls_subdegree f + 1"
  and     "fls_subdegree (f * fls_X) = fls_subdegree f + 1"
  by      (auto simp: fls_X_times_conv_shift assms)

lemma fls_mult_fls_X_nonzero:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  assumes "f \<noteq> 0"
  shows   "fls_X * f \<noteq> 0"
  and     "f * fls_X \<noteq> 0"
  by      (auto simp: fls_X_times_conv_shift fls_shift_eq0_iff assms)

lemma fls_base_factor_mult_fls_X:
  fixes f :: "'a::{comm_monoid_add,monoid_mult,mult_zero} fls"
  shows "fls_base_factor (fls_X * f) = fls_base_factor f"
  and   "fls_base_factor (f * fls_X) = fls_base_factor f"
  using fls_base_factor_shift[of "-1" f]
  by    (auto simp: fls_X_times_conv_shift)

lemma fls_X_inv_times_conv_shift:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  shows "fls_X_inv * f = fls_shift 1 f" "f * fls_X_inv = fls_shift 1 f"
  by    (simp_all add: fls_X_inv_conv_shift_1 fls_mult_one fls_shifted_times_simps)

lemmas fls_X_inv_times_comm = trans_sym[OF fls_X_inv_times_conv_shift]

lemma fls_subdegree_mult_fls_X_inv:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  assumes "f \<noteq> 0"
  shows   "fls_subdegree (fls_X_inv * f) = fls_subdegree f - 1"
  and     "fls_subdegree (f * fls_X_inv) = fls_subdegree f - 1"
  by      (auto simp: fls_X_inv_times_conv_shift assms)

lemma fls_mult_fls_X_inv_nonzero:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fls"
  assumes "f \<noteq> 0"
  shows   "fls_X_inv * f \<noteq> 0"
  and     "f * fls_X_inv \<noteq> 0"
  by      (auto simp: fls_X_inv_times_conv_shift fls_shift_eq0_iff assms)

lemma fls_base_factor_mult_fls_X_inv:
  fixes f :: "'a::{comm_monoid_add,monoid_mult,mult_zero} fls"
  shows "fls_base_factor (fls_X_inv * f) = fls_base_factor f"
  and   "fls_base_factor (f * fls_X_inv) = fls_base_factor f"
  using fls_base_factor_shift[of 1 f]
  by    (auto simp: fls_X_inv_times_conv_shift)

lemma fls_mult_assoc_subdegree_ge_0:
  fixes   f g h :: "'a::semiring_0 fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0" "fls_subdegree h \<ge> 0"
  shows   "f * g * h = f * (g * h)"
  using   assms
  by      (simp add: fls_times_conv_fps_times fls_subdegree_fls_to_fps_gt0 mult.assoc)

lemma fls_mult_assoc_base_factor:
  fixes a b c :: "'a::semiring_0 fls"
  shows
    "fls_base_factor a * fls_base_factor b * fls_base_factor c =
      fls_base_factor a * (fls_base_factor b * fls_base_factor c)"
  by    (simp add: fls_mult_assoc_subdegree_ge_0 del: fls_base_factor_def)

lemma fls_mult_distrib_subdegree_ge_0:
  fixes   f g h :: "'a::semiring_0 fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0" "fls_subdegree h \<ge> 0"
  shows   "(f + g) * h = f * h + g * h"
  and     "h * (f + g) = h * f + h * g"
proof-
  have "fls_subdegree (f+g) \<ge> 0"
  proof (cases "f+g = 0")
    case False
    with assms(1,2) show ?thesis
      using fls_plus_subdegree by fastforce
  qed simp
  with assms show "(f + g) * h = f * h + g * h" "h * (f + g) = h * f + h * g"
    using distrib_right[of "fls_regpart f"] distrib_left[of "fls_regpart h"]
    by    (simp_all add: fls_times_conv_fps_times)
qed

lemma fls_mult_distrib_base_factor:
  fixes a b c :: "'a::semiring_0 fls"
  shows
    "fls_base_factor a * (fls_base_factor b + fls_base_factor c) =
      fls_base_factor a * fls_base_factor b + fls_base_factor a * fls_base_factor c"
  by    (simp add: fls_mult_distrib_subdegree_ge_0 del: fls_base_factor_def)

instance fls :: (semiring_0) semiring_0
proof

  fix a b c :: "'a fls"
  have
    "a * b * c =
      fls_shift (- (fls_subdegree a + fls_subdegree b + fls_subdegree c))
        (fls_base_factor a * fls_base_factor b * fls_base_factor c)"
    by (simp add: fls_times_both_shifted_simp)
  moreover have
    "a * (b * c) =
      fls_shift (- (fls_subdegree a + fls_subdegree b + fls_subdegree c))
        (fls_base_factor a * fls_base_factor b * fls_base_factor c)"
    using fls_mult_assoc_base_factor[of a b c] by (simp add: fls_times_both_shifted_simp)
  ultimately show "a * b * c = a * (b * c)" by simp

  have ab:
    "fls_subdegree (fls_shift (min (fls_subdegree a) (fls_subdegree b)) a) \<ge> 0"
    "fls_subdegree (fls_shift (min (fls_subdegree a) (fls_subdegree b)) b) \<ge> 0"
    by (simp_all add: fls_shift_nonneg_subdegree)
  have
    "(a + b) * c =
      fls_shift (- (min (fls_subdegree a) (fls_subdegree b) + fls_subdegree c)) (
        (
          fls_shift (min (fls_subdegree a) (fls_subdegree b)) a +
          fls_shift (min (fls_subdegree a) (fls_subdegree b)) b
        ) * fls_base_factor c)"
    using fls_times_both_shifted_simp[of
            "-min (fls_subdegree a) (fls_subdegree b)"
            "fls_shift (min (fls_subdegree a) (fls_subdegree b)) a +
            fls_shift (min (fls_subdegree a) (fls_subdegree b)) b"
            "-fls_subdegree c" "fls_base_factor c"
          ]
    by    simp
  also have
    "\<dots> =
      fls_shift (-(min (fls_subdegree a) (fls_subdegree b) + fls_subdegree c))
        (fls_shift (min (fls_subdegree a) (fls_subdegree b)) a * fls_base_factor c)
      +
      fls_shift (-(min (fls_subdegree a) (fls_subdegree b) + fls_subdegree c))
        (fls_shift (min (fls_subdegree a) (fls_subdegree b)) b * fls_base_factor c)"
    using ab
    by    (simp add: fls_mult_distrib_subdegree_ge_0(1) del: fls_base_factor_def)
  finally show "(a + b) * c = a * c + b * c" by (simp add: fls_times_both_shifted_simp)

  have bc:
    "fls_subdegree (fls_shift (min (fls_subdegree b) (fls_subdegree c)) b) \<ge> 0"
    "fls_subdegree (fls_shift (min (fls_subdegree b) (fls_subdegree c)) c) \<ge> 0"
    by (simp_all add: fls_shift_nonneg_subdegree)
  have
    "a * (b + c) = 
      fls_shift (- (fls_subdegree a + min (fls_subdegree b) (fls_subdegree c))) (
        fls_base_factor a * (
          fls_shift (min (fls_subdegree b) (fls_subdegree c)) b +
          fls_shift (min (fls_subdegree b) (fls_subdegree c)) c
        )
      )
    "
    using fls_times_both_shifted_simp[of
            "-fls_subdegree a" "fls_base_factor a"
            "-min (fls_subdegree b) (fls_subdegree c)"
            "fls_shift (min (fls_subdegree b) (fls_subdegree c)) b +
            fls_shift (min (fls_subdegree b) (fls_subdegree c)) c"
          ]
    by    simp
  also have
    "\<dots> =
      fls_shift (-(fls_subdegree a + min (fls_subdegree b) (fls_subdegree c)))
        (fls_base_factor a * fls_shift (min (fls_subdegree b) (fls_subdegree c)) b)
      +
      fls_shift (-(fls_subdegree a + min (fls_subdegree b) (fls_subdegree c)))
        (fls_base_factor a * fls_shift (min (fls_subdegree b) (fls_subdegree c)) c)
    "
    using bc
    by    (simp add: fls_mult_distrib_subdegree_ge_0(2) del: fls_base_factor_def)
  finally show "a * (b + c)  = a * b + a * c" by (simp add: fls_times_both_shifted_simp)

qed

lemma fls_mult_commute_subdegree_ge_0:
  fixes   f g :: "'a::comm_semiring_0 fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0"
  shows   "f * g = g * f"
  using   assms
  by      (simp add: fls_times_conv_fps_times mult.commute)

lemma fls_mult_commute_base_factor:
  fixes a b c :: "'a::comm_semiring_0 fls"
  shows "fls_base_factor a * fls_base_factor b = fls_base_factor b * fls_base_factor a"
  by    (simp add: fls_mult_commute_subdegree_ge_0 del: fls_base_factor_def)

instance fls :: (comm_semiring_0) comm_semiring_0
proof
  fix a b c :: "'a fls"
  show "a * b = b * a"
    using fls_times_conv_base_factor_times[of a b] fls_times_conv_base_factor_times[of b a]
          fls_mult_commute_base_factor[of a b]
    by    (simp add: add.commute)
qed (simp add: distrib_right)

instance fls :: (semiring_1) semiring_1
  by (standard, simp_all add: fls_mult_one)

lemma fls_of_nat: "(of_nat n :: 'a::semiring_1 fls) = fls_const (of_nat n)"
  by (induct n) (auto intro: fls_eqI)

lemma fls_of_nat_nth: "of_nat n $$ k = (if k=0 then of_nat n else 0)"
  by (simp add: fls_of_nat)

lemma fls_mult_of_nat_nth [simp]:
  shows "(of_nat k * f) $$ n = of_nat k * f$$n"
  and   "(f * of_nat k ) $$ n = f$$n * of_nat k"
  by    (simp_all add: fls_of_nat)

lemma fls_subdegree_of_nat [simp]: "fls_subdegree (of_nat n) = 0"
  by (simp add: fls_of_nat)

lemma fls_shift_of_nat_nth:
  "fls_shift k (of_nat a) $$ n = (if n=-k then of_nat a else 0)"
  by (simp add: fls_of_nat fls_shift_const_nth)

lemma fls_base_factor_of_nat [simp]:
  "fls_base_factor (of_nat n :: 'a::semiring_1 fls) = (of_nat n :: 'a fls)"
  by (simp add: fls_of_nat)

lemma fls_regpart_of_nat [simp]: "fls_regpart (of_nat n) = (of_nat n :: 'a::semiring_1 fps)"
  by (simp add: fls_of_nat fps_of_nat)

lemma fls_prpart_of_nat [simp]: "fls_prpart (of_nat n) = 0"
  by (simp add: fls_prpart_eq0_iff)

lemma fls_base_factor_to_fps_of_nat:
  "fls_base_factor_to_fps (of_nat n) = (of_nat n :: 'a::semiring_1 fps)"
  by simp

lemma fps_to_fls_of_nat:
  "fps_to_fls (of_nat n) = (of_nat n :: 'a::semiring_1 fls)"
proof -
  have "fps_to_fls (of_nat n) = fps_to_fls (fps_const (of_nat n))"
    by (simp add: fps_of_nat)
  thus ?thesis by (simp add: fls_of_nat)
qed

lemma fps_to_fls_numeral [simp]: "fps_to_fls (numeral n) = numeral n"
  by (metis fps_to_fls_of_nat of_nat_numeral)

lemma fls_const_power: "fls_const (a ^ b) = fls_const a ^ b"
  by (induction b) (auto simp flip: fls_const_mult_const)

lemma fls_const_numeral [simp]: "fls_const (numeral n) = numeral n"
  by (metis fls_of_nat of_nat_numeral)

lemma fls_mult_of_numeral_nth [simp]:
  shows "(numeral k * f) $$ n = numeral k * f $$ n"
  and   "(f * numeral k) $$ n = f $$ n * numeral k"
  by (metis fls_const_numeral fls_mult_const_nth)+

lemma fls_nth_numeral' [simp]:
  "numeral n $$ 0 = numeral n" "k \<noteq> 0 \<Longrightarrow> numeral n $$ k = 0"
  by (metis fls_const_nth fls_const_numeral)+

instance fls :: (comm_semiring_1) comm_semiring_1
  by standard simp

instance fls :: (ring) ring ..

instance fls :: (comm_ring) comm_ring ..

instance fls :: (ring_1) ring_1 ..

lemma fls_of_int_nonneg: "(of_int (int n) :: 'a::ring_1 fls) = fls_const (of_int (int n))"
  by (induct n) (auto intro: fls_eqI)

lemma fls_of_int: "(of_int i :: 'a::ring_1 fls) = fls_const (of_int i)"
proof (induct i)
  case (neg i)
  have "of_int (int (Suc i)) = fls_const (of_int (int (Suc i)) :: 'a)"
    using fls_of_int_nonneg[of "Suc i"] by simp
  hence "- of_int (int (Suc i)) = - fls_const (of_int (int (Suc i)) :: 'a)"
    by simp
  thus ?case by (simp add: fls_const_uminus[symmetric])
qed (rule fls_of_int_nonneg)

lemma fls_of_int_nth: "of_int n $$ k = (if k=0 then of_int n else 0)"
  by (simp add: fls_of_int)

lemma fls_mult_of_int_nth [simp]:
  shows "(of_int k * f) $$ n = of_int k * f$$n"
  and   "(f * of_int k ) $$ n = f$$n * of_int k"
  by    (simp_all add: fls_of_int)

lemma fls_subdegree_of_int [simp]: "fls_subdegree (of_int i) = 0"
  by (simp add: fls_of_int)

lemma fls_shift_of_int_nth:
  "fls_shift k (of_int i) $$ n = (if n=-k then of_int i else 0)"
  by (simp add: fls_of_int_nth)

lemma fls_base_factor_of_int [simp]:
  "fls_base_factor (of_int i :: 'a::ring_1 fls) = (of_int i :: 'a fls)"
  by (simp add: fls_of_int)

lemma fls_regpart_of_int [simp]:
  "fls_regpart (of_int i) = (of_int i :: 'a::ring_1 fps)"
  by (simp add: fls_of_int fps_of_int)

lemma fls_prpart_of_int [simp]: "fls_prpart (of_int n) = 0"
  by (simp add: fls_prpart_eq0_iff)

lemma fls_base_factor_to_fps_of_int:
  "fls_base_factor_to_fps (of_int i) = (of_int i :: 'a::ring_1 fps)"
  by simp

lemma fps_to_fls_of_int:
  "fps_to_fls (of_int i) = (of_int i :: 'a::ring_1 fls)"
proof -
  have "fps_to_fls (of_int i) = fps_to_fls (fps_const (of_int i))"
    by (simp add: fps_of_int)
  thus ?thesis by (simp add: fls_of_int)
qed

instance fls :: (comm_ring_1) comm_ring_1 ..

instance fls :: (semiring_no_zero_divisors) semiring_no_zero_divisors
proof
  fix a b :: "'a fls"
  assume "a \<noteq> 0" and "b \<noteq> 0"
  hence "(a * b) $$ (fls_subdegree a + fls_subdegree b) \<noteq> 0" by simp
  thus "a * b \<noteq> 0" using fls_nonzeroI by fast
qed

instance fls :: (semiring_1_no_zero_divisors) semiring_1_no_zero_divisors ..

instance fls :: (ring_no_zero_divisors) ring_no_zero_divisors ..

instance fls :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..

instance fls :: (idom) idom ..

lemma semiring_char_fls [simp]: "CHAR('a :: comm_semiring_1 fls) = CHAR('a)"
  by (rule CHAR_eqI) (auto simp: fls_of_nat of_nat_eq_0_iff_char_dvd fls_const_nonzero)

instance fls :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance fls :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance fls :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance fls :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard


subsubsection \<open>Powers\<close>

lemma fls_subdegree_prod:
  fixes F :: "'a \<Rightarrow> 'b :: field_char_0 fls"
  assumes "\<And>x. x \<in> I \<Longrightarrow> F x \<noteq> 0"
  shows   "fls_subdegree (\<Prod>x\<in>I. F x) = (\<Sum>x\<in>I. fls_subdegree (F x))"
  using assms by (induction I rule: infinite_finite_induct) auto

lemma fls_subdegree_prod':
  fixes F :: "'a \<Rightarrow> 'b :: field_char_0 fls"
  assumes "\<And>x. x \<in> I \<Longrightarrow> fls_subdegree (F x) \<noteq> 0"
  shows   "fls_subdegree (\<Prod>x\<in>I. F x) = (\<Sum>x\<in>I. fls_subdegree (F x))"
proof (intro fls_subdegree_prod)
  show "F x \<noteq> 0" if "x \<in> I" for x
    using assms[OF that] by auto
qed

lemma fls_pow_subdegree_ge:
  "f^n \<noteq> 0 \<Longrightarrow> fls_subdegree (f^n) \<ge> n * fls_subdegree f"
proof (induct n)
  case (Suc n) thus ?case
    using fls_mult_subdegree_ge[of f "f^n"] by (fastforce simp: algebra_simps)
qed simp

lemma fls_pow_nth_below_subdegree:
  "k < n * fls_subdegree f \<Longrightarrow> (f^n) $$ k = 0"
  using fls_pow_subdegree_ge[of f n] by (cases "f^n = 0") auto

lemma fls_pow_base [simp]:
  "(f ^ n) $$ (n * fls_subdegree f) = (f $$ fls_subdegree f) ^ n"
proof (induct n)
  case (Suc n)
  show ?case
  proof (cases "Suc n * fls_subdegree f < fls_subdegree f + fls_subdegree (f^n)")
    case True with Suc show ?thesis
      by (simp_all add: fls_times_nth_eq0 distrib_right)
  next
    case False
    from False have
      "{0..int n * fls_subdegree f - fls_subdegree (f ^ n)} =
        insert 0 {1..int n * fls_subdegree f - fls_subdegree (f ^ n)}"
      by (auto simp: algebra_simps)
    with False Suc show ?thesis
      by (simp add: algebra_simps fls_times_nth(4) fls_pow_nth_below_subdegree)
  qed
qed simp

lemma fls_pow_subdegree_eqI:
  "(f $$ fls_subdegree f) ^ n \<noteq> 0 \<Longrightarrow> fls_subdegree (f^n) = n * fls_subdegree f"
  using fls_pow_nth_below_subdegree by (fastforce intro: fls_subdegree_eqI)

lemma fls_unit_base_subdegree_power:
  "x * f $$ fls_subdegree f = 1 \<Longrightarrow> fls_subdegree (f ^ n) = n * fls_subdegree f"
  "f $$ fls_subdegree f * y = 1 \<Longrightarrow> fls_subdegree (f ^ n) = n * fls_subdegree f"
proof-
  show "x * f $$ fls_subdegree f = 1 \<Longrightarrow> fls_subdegree (f ^ n) = n * fls_subdegree f"
    using left_right_inverse_power[of x "f $$ fls_subdegree f" n]
    by    (auto intro: fls_pow_subdegree_eqI)
  show "f $$ fls_subdegree f * y = 1 \<Longrightarrow> fls_subdegree (f ^ n) = n * fls_subdegree f"
    using left_right_inverse_power[of "f $$ fls_subdegree f" y n]
    by    (auto intro: fls_pow_subdegree_eqI)
qed

lemma fls_base_dvd1_subdegree_power:
  "f $$ fls_subdegree f dvd 1 \<Longrightarrow> fls_subdegree (f ^ n) = n * fls_subdegree f"
  using fls_unit_base_subdegree_power unfolding dvd_def by auto

lemma fls_pow_subdegree_ge0:
  assumes "fls_subdegree f \<ge> 0"
  shows   "fls_subdegree (f^n) \<ge> 0"
proof (cases "f^n = 0")
  case False
  moreover from assms have "int n * fls_subdegree f \<ge> 0" by simp
  ultimately show ?thesis using fls_pow_subdegree_ge by fastforce
qed simp

lemma fls_subdegree_pow:
  fixes   f :: "'a::semiring_1_no_zero_divisors fls"
  shows   "fls_subdegree (f ^ n) = n * fls_subdegree f"
proof (cases "f=0")
  case False thus ?thesis by (induct n) (simp_all add: algebra_simps)
qed (cases "n=0", auto simp: zero_power)

lemma fls_shifted_pow:
  "(fls_shift m f) ^ n = fls_shift (n*m) (f ^ n)"
  by (induct n) (simp_all add: fls_times_both_shifted_simp algebra_simps)

lemma fls_pow_conv_fps_pow:
  assumes "fls_subdegree f \<ge> 0"
  shows   "f ^ n = fps_to_fls ( (fls_regpart f) ^ n )"
proof (induct n)
  case (Suc n) with assms show ?case
    using fls_pow_subdegree_ge0[of f n]
    by (simp add: fls_times_conv_fps_times)
qed simp

lemma fps_to_fls_power: "fps_to_fls (f ^ n) = fps_to_fls f ^ n"
  by (simp add: fls_pow_conv_fps_pow fls_subdegree_fls_to_fps_gt0)

lemma fls_pow_conv_regpart:
  "fls_subdegree f \<ge> 0 \<Longrightarrow> fls_regpart (f ^ n) = (fls_regpart f) ^ n"
  by (simp add: fls_pow_conv_fps_pow)

text \<open>These two lemmas show that shifting 1 is equivalent to powers of the implied variable.\<close>

lemma fls_X_power_conv_shift_1: "fls_X ^ n = fls_shift (-n) 1"
  by (simp add: fls_X_conv_shift_1 fls_shifted_pow)

lemma fls_X_inv_power_conv_shift_1: "fls_X_inv ^ n = fls_shift n 1"
  by (simp add: fls_X_inv_conv_shift_1 fls_shifted_pow)

abbreviation "fls_X_intpow \<equiv> (\<lambda>i. fls_shift (-i) 1)"
\<comment> \<open>
  Unifies @{term fls_X} and @{term fls_X_inv} so that @{term "fls_X_intpow"} returns the equivalent
  of the implied variable raised to the supplied integer argument of @{term "fls_X_intpow"}, whether
  positive or negative.
\<close>

lemma fls_X_intpow_nonzero[simp]: "(fls_X_intpow i :: 'a::zero_neq_one fls) \<noteq> 0"
  by (simp add: fls_shift_eq0_iff)

lemma fls_X_intpow_power: "(fls_X_intpow i) ^ n = fls_X_intpow (n * i)"
  by (simp add: fls_shifted_pow)

lemma fls_X_power_nth [simp]: "fls_X ^ n $$ k = (if k=n then 1 else 0)"
  by (simp add: fls_X_power_conv_shift_1)

lemma fls_X_inv_power_nth [simp]: "fls_X_inv ^ n $$ k = (if k=-n then 1 else 0)"
  by (simp add: fls_X_inv_power_conv_shift_1)

lemma fls_X_pow_nonzero[simp]: "(fls_X ^ n :: 'a :: semiring_1 fls) \<noteq> 0"
proof
  assume "(fls_X ^ n :: 'a fls) = 0"
  hence "(fls_X ^ n :: 'a fls) $$ n = 0" by simp
  thus False by simp
qed

lemma fls_X_inv_pow_nonzero[simp]: "(fls_X_inv ^ n :: 'a :: semiring_1 fls) \<noteq> 0"
proof
  assume "(fls_X_inv ^ n :: 'a fls) = 0"
  hence "(fls_X_inv ^ n :: 'a fls) $$ -n = 0" by simp
  thus False by simp
qed

lemma fls_subdegree_fls_X_pow [simp]: "fls_subdegree (fls_X ^ n) = n"
  by (intro fls_subdegree_eqI) (simp_all add: fls_X_power_conv_shift_1)

lemma fls_subdegree_fls_X_inv_pow [simp]: "fls_subdegree (fls_X_inv ^ n) = -n"
  by (intro fls_subdegree_eqI) (simp_all add: fls_X_inv_power_conv_shift_1)

lemma fls_subdegree_fls_X_intpow [simp]:
  "fls_subdegree ((fls_X_intpow i) :: 'a::zero_neq_one fls) = i"
  by simp

lemma fls_X_pow_conv_fps_X_pow: "fls_regpart (fls_X ^ n) = fps_X ^ n"
  by (simp add: fls_pow_conv_regpart)

lemma fls_X_inv_pow_regpart: "n > 0 \<Longrightarrow> fls_regpart (fls_X_inv ^ n) = 0"
  by (auto intro: fps_ext simp: fls_X_inv_power_conv_shift_1)

lemma fls_X_intpow_regpart:
  "fls_regpart (fls_X_intpow i) = (if i\<ge>0 then fps_X ^ nat i else 0)"
  using fls_X_pow_conv_fps_X_pow[of "nat i"]
        fls_regpart_shift_conv_fps_shift[of "-i" 1]
  by    (auto simp: fls_X_power_conv_shift_1 fps_shift_one)

lemma fls_X_power_times_conv_shift:
  "fls_X ^ n * f = fls_shift (-int n) f" "f * fls_X ^ n = fls_shift (-int n) f"
  using fls_times_both_shifted_simp[of "-int n" 1 0 f]
        fls_times_both_shifted_simp[of 0 f "-int n" 1]
  by    (simp_all add: fls_X_power_conv_shift_1)

lemma fls_X_inv_power_times_conv_shift:
  "fls_X_inv ^ n * f = fls_shift (int n) f" "f * fls_X_inv ^ n = fls_shift (int n) f"
  using fls_times_both_shifted_simp[of "int n" 1 0 f]
        fls_times_both_shifted_simp[of 0 f "int n" 1]
  by    (simp_all add: fls_X_inv_power_conv_shift_1)

lemma fls_X_intpow_times_conv_shift:
  fixes f :: "'a::semiring_1 fls"
  shows "fls_X_intpow i * f = fls_shift (-i) f" "f * fls_X_intpow i = fls_shift (-i) f"
  by    (simp_all add: fls_shifted_times_simps)

lemmas fls_X_power_times_comm     = trans_sym[OF fls_X_power_times_conv_shift]
lemmas fls_X_inv_power_times_comm = trans_sym[OF fls_X_inv_power_times_conv_shift]

lemma fls_X_intpow_times_comm:
  fixes f :: "'a::semiring_1 fls"
  shows "fls_X_intpow i * f = f * fls_X_intpow i"
  by    (simp add: fls_X_intpow_times_conv_shift)

lemma fls_X_intpow_times_fls_X_intpow:
  "(fls_X_intpow i :: 'a::semiring_1 fls) * fls_X_intpow j = fls_X_intpow (i+j)"
  by (simp add: fls_times_both_shifted_simp)

lemma fls_X_intpow_diff_conv_times:
  "fls_X_intpow (i-j) = (fls_X_intpow i :: 'a::semiring_1 fls) * fls_X_intpow (-j)"
  using fls_X_intpow_times_fls_X_intpow[of i "-j",symmetric] by simp

lemma fls_mult_fls_X_power_nonzero:
  assumes "f \<noteq> 0"
  shows   "fls_X ^ n * f \<noteq> 0" "f * fls_X ^ n \<noteq> 0"
  by      (auto simp: fls_X_power_times_conv_shift fls_shift_eq0_iff assms)

lemma fls_mult_fls_X_inv_power_nonzero:
  assumes "f \<noteq> 0"
  shows   "fls_X_inv ^ n * f \<noteq> 0" "f * fls_X_inv ^ n \<noteq> 0"
  by      (auto simp: fls_X_inv_power_times_conv_shift fls_shift_eq0_iff assms)

lemma fls_mult_fls_X_intpow_nonzero:
  fixes f :: "'a::semiring_1 fls"
  assumes "f \<noteq> 0"
  shows   "fls_X_intpow i * f \<noteq> 0" "f * fls_X_intpow i \<noteq> 0"
  by      (auto simp: fls_X_intpow_times_conv_shift fls_shift_eq0_iff assms)

lemma fls_subdegree_mult_fls_X_power:
  assumes "f \<noteq> 0"
  shows   "fls_subdegree (fls_X ^ n * f) = fls_subdegree f + n"
  and     "fls_subdegree (f * fls_X ^ n) = fls_subdegree f + n"
  by      (auto simp: fls_X_power_times_conv_shift assms)

lemma fls_subdegree_mult_fls_X_inv_power:
  assumes "f \<noteq> 0"
  shows   "fls_subdegree (fls_X_inv ^ n * f) = fls_subdegree f - n"
  and     "fls_subdegree (f * fls_X_inv ^ n) = fls_subdegree f - n"
  by      (auto simp: fls_X_inv_power_times_conv_shift assms)

lemma fls_subdegree_mult_fls_X_intpow:
  fixes   f :: "'a::semiring_1 fls"
  assumes "f \<noteq> 0"
  shows   "fls_subdegree (fls_X_intpow i * f) = fls_subdegree f + i"
  and     "fls_subdegree (f * fls_X_intpow i) = fls_subdegree f + i"
  by      (auto simp: fls_X_intpow_times_conv_shift assms)

lemma fls_X_shift:
  "fls_shift (-int n) fls_X = fls_X ^ Suc n"
  "fls_shift (int (Suc n)) fls_X = fls_X_inv ^ n"
  using fls_X_power_conv_shift_1[of "Suc n", symmetric]
  by    (simp_all add: fls_X_conv_shift_1 fls_X_inv_power_conv_shift_1)

lemma fls_X_inv_shift:
  "fls_shift (int n) fls_X_inv = fls_X_inv ^ Suc n"
  "fls_shift (- int (Suc n)) fls_X_inv = fls_X ^ n"
  using fls_X_inv_power_conv_shift_1[of "Suc n", symmetric]
  by    (simp_all add: fls_X_inv_conv_shift_1 fls_X_power_conv_shift_1)

lemma fls_X_power_base_factor: "fls_base_factor (fls_X ^ n) = 1"
  by (simp add: fls_X_power_conv_shift_1)

lemma fls_X_inv_power_base_factor: "fls_base_factor (fls_X_inv ^ n) = 1"
  by (simp add: fls_X_inv_power_conv_shift_1)

lemma fls_X_intpow_base_factor: "fls_base_factor (fls_X_intpow i) = 1"
  using fls_base_factor_shift[of "-i" 1] by simp

lemma fls_base_factor_mult_fls_X_power:
  shows "fls_base_factor (fls_X ^ n * f) = fls_base_factor f"
  and   "fls_base_factor (f * fls_X ^ n) = fls_base_factor f"
  using fls_base_factor_shift[of "-int n" f]
  by    (auto simp: fls_X_power_times_conv_shift)

lemma fls_base_factor_mult_fls_X_inv_power:
  shows "fls_base_factor (fls_X_inv ^ n * f) = fls_base_factor f"
  and   "fls_base_factor (f * fls_X_inv ^ n) = fls_base_factor f"
  using fls_base_factor_shift[of "int n" f]
  by    (auto simp: fls_X_inv_power_times_conv_shift)

lemma fls_base_factor_mult_fls_X_intpow:
  fixes f :: "'a::semiring_1 fls"
  shows "fls_base_factor (fls_X_intpow i * f) = fls_base_factor f"
  and   "fls_base_factor (f * fls_X_intpow i) = fls_base_factor f"
  using fls_base_factor_shift[of "-i" f]
  by    (auto simp: fls_X_intpow_times_conv_shift)

lemma fls_X_power_base_factor_to_fps: "fls_base_factor_to_fps (fls_X ^ n) = 1"
proof-
  define X where "X \<equiv> fls_X :: 'a::semiring_1 fls"
  hence "fls_base_factor (X ^ n) = 1" using fls_X_power_base_factor by simp
  thus "fls_base_factor_to_fps (X^n) = 1" by simp
qed  

lemma fls_X_inv_power_base_factor_to_fps: "fls_base_factor_to_fps (fls_X_inv ^ n) = 1"
proof-
  define iX where "iX \<equiv> fls_X_inv :: 'a::semiring_1 fls"
  hence "fls_base_factor (iX ^ n) = 1" using fls_X_inv_power_base_factor by simp
  thus "fls_base_factor_to_fps (iX^n) = 1" by simp
qed  

lemma fls_X_intpow_base_factor_to_fps: "fls_base_factor_to_fps (fls_X_intpow i) = 1"
proof-
  define f :: "'a fls" where "f \<equiv> fls_X_intpow i"
  moreover have "fls_base_factor (fls_X_intpow i) = 1" by (rule fls_X_intpow_base_factor)
  ultimately have "fls_base_factor f = 1" by simp
  thus "fls_base_factor_to_fps f = 1" by simp
qed

lemma fls_base_factor_X_power_decompose:
  fixes f :: "'a::semiring_1 fls"
  shows "f = fls_base_factor f * fls_X_intpow (fls_subdegree f)"
  and   "f = fls_X_intpow (fls_subdegree f) * fls_base_factor f"
  by    (simp_all add: fls_times_both_shifted_simp)

lemma fls_normalized_product_of_inverses:
  assumes "f * g = 1"
  shows   "fls_base_factor f * fls_base_factor g =
            fls_X ^ (nat (-(fls_subdegree f+fls_subdegree g)))"
  and     "fls_base_factor f * fls_base_factor g =
            fls_X_intpow (-(fls_subdegree f+fls_subdegree g))"
  using   fls_mult_subdegree_ge[of f g]
          fls_times_base_factor_conv_shifted_times[of f g]
  by      (simp_all add: assms fls_X_power_conv_shift_1 algebra_simps)

lemma fls_fps_normalized_product_of_inverses:
  assumes "f * g = 1"
  shows   "fls_base_factor_to_fps f * fls_base_factor_to_fps g =
            fps_X ^ (nat (-(fls_subdegree f+fls_subdegree g)))"
  using fls_times_conv_regpart[of "fls_base_factor f" "fls_base_factor g"]
        fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of g]
        fls_normalized_product_of_inverses(1)[OF assms]
  by    (force simp: fls_X_pow_conv_fps_X_pow)


subsubsection \<open>Inverses\<close>


abbreviation fls_left_inverse ::
  "'a::{comm_monoid_add,uminus,times} fls \<Rightarrow> 'a \<Rightarrow> 'a fls"
  where
  "fls_left_inverse f x \<equiv>
    fls_shift (fls_subdegree f) (fps_to_fls (fps_left_inverse (fls_base_factor_to_fps f) x))"

abbreviation fls_right_inverse ::
  "'a::{comm_monoid_add,uminus,times} fls \<Rightarrow> 'a \<Rightarrow> 'a fls"
  where
  "fls_right_inverse f y \<equiv>
    fls_shift (fls_subdegree f) (fps_to_fls (fps_right_inverse (fls_base_factor_to_fps f) y))"

instantiation fls :: ("{comm_monoid_add,uminus,times,inverse}") inverse
begin
  definition fls_divide_def:
    "f div g =
      fls_shift (fls_subdegree g - fls_subdegree f) (
        fps_to_fls ((fls_base_factor_to_fps f) div (fls_base_factor_to_fps g))
      )
    "
  definition fls_inverse_def:
    "inverse f = fls_shift (fls_subdegree f) (fps_to_fls (inverse (fls_base_factor_to_fps f)))"
  instance ..
end

lemma fls_inverse_def':
  "inverse f = fls_right_inverse f (inverse (f $$ fls_subdegree f))"
  by (simp add: fls_inverse_def fps_inverse_def)

lemma fls_lr_inverse_base:
  "fls_left_inverse f x $$ (-fls_subdegree f) = x"
  "fls_right_inverse f y $$ (-fls_subdegree f) = y"
  by auto

lemma fls_inverse_base:
  "f \<noteq> 0 \<Longrightarrow> inverse f $$ (-fls_subdegree f) = inverse (f $$ fls_subdegree f)"
  by (simp add: fls_inverse_def')

lemma fls_lr_inverse_starting0:
  fixes f :: "'a::{comm_monoid_add,mult_zero,uminus} fls"
  and   g :: "'b::{ab_group_add,mult_zero} fls"
  shows "fls_left_inverse f 0 = 0"
  and   "fls_right_inverse g 0 = 0"
  by    (simp_all add: fps_lr_inverse_starting0)

lemma fls_lr_inverse_eq0_imp_starting0:
  "fls_left_inverse f x = 0 \<Longrightarrow> x = 0"
  "fls_right_inverse f x = 0 \<Longrightarrow> x = 0"
  by (metis fls_lr_inverse_base fls_nonzeroI)+

lemma fls_lr_inverse_eq_0_iff:
  fixes x :: "'a::{comm_monoid_add,mult_zero,uminus}"
  and   y :: "'b::{ab_group_add,mult_zero}"
  shows "fls_left_inverse f x = 0 \<longleftrightarrow> x = 0"
  and   "fls_right_inverse g y = 0 \<longleftrightarrow> y = 0"
  using fls_lr_inverse_starting0 fls_lr_inverse_eq0_imp_starting0
  by    auto

lemma fls_inverse_eq_0_iff':
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fls"
  shows "inverse f = 0 \<longleftrightarrow> (inverse (f $$ fls_subdegree f) = 0)"
  using fls_lr_inverse_eq_0_iff(2)[of f "inverse (f $$ fls_subdegree f)"]
  by    (simp add: fls_inverse_def')

lemma fls_inverse_eq_0_iff[simp]:
  "inverse f = (0:: ('a::division_ring) fls) \<longleftrightarrow> f $$ fls_subdegree f = 0"
  using fls_inverse_eq_0_iff'[of f] by (cases "f=0") auto

lemmas fls_inverse_eq_0' = iffD2[OF fls_inverse_eq_0_iff']
lemmas fls_inverse_eq_0  = iffD2[OF fls_inverse_eq_0_iff]

lemma fls_lr_inverse_const:
  fixes a :: "'a::{ab_group_add,mult_zero}"
  and   b :: "'b::{comm_monoid_add,mult_zero,uminus}"
  shows "fls_left_inverse (fls_const a) x = fls_const x"
  and   "fls_right_inverse (fls_const b) y = fls_const y"
  by    (simp_all add: fps_const_lr_inverse)

lemma fls_inverse_const:
  fixes a :: "'a::{comm_monoid_add,inverse,mult_zero,uminus}"
  shows "inverse (fls_const a) = fls_const (inverse a)"
  using fls_lr_inverse_const(2)
  by    (auto simp: fls_inverse_def')

lemma fls_lr_inverse_of_nat:
  fixes x :: "'a::{ring_1,mult_zero}"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (of_nat n) x = fls_const x"
  and   "fls_right_inverse (of_nat n) y = fls_const y"
  using fls_lr_inverse_const
  by    (auto simp: fls_of_nat)

lemma fls_inverse_of_nat:
  "inverse (of_nat n :: 'a :: {semiring_1,inverse,uminus} fls) = fls_const (inverse (of_nat n))"
  by (simp add: fls_inverse_const fls_of_nat)

lemma fls_lr_inverse_of_int:
  fixes x :: "'a::{ring_1,mult_zero}"
  shows "fls_left_inverse (of_int n) x = fls_const x"
  and   "fls_right_inverse (of_int n) x = fls_const x"
  using fls_lr_inverse_const
  by    (auto simp: fls_of_int)

lemma fls_inverse_of_int:
  "inverse (of_int n :: 'a :: {ring_1,inverse,uminus} fls) = fls_const (inverse (of_int n))"
  by      (simp add: fls_inverse_const fls_of_int)

lemma fls_lr_inverse_zero:
  fixes x :: "'a::{ab_group_add,mult_zero}"
  and   y :: "'b::{comm_monoid_add,mult_zero,uminus}"
  shows "fls_left_inverse 0 x = fls_const x"
  and   "fls_right_inverse 0 y = fls_const y"
  using fls_lr_inverse_const[of 0]
  by    auto

lemma fls_inverse_zero_conv_fls_const:
  "inverse (0::'a::{comm_monoid_add,mult_zero,uminus,inverse} fls) = fls_const (inverse 0)"
  using fls_lr_inverse_zero(2)[of "inverse (0::'a)"] by (simp add: fls_inverse_def')

lemma fls_inverse_zero':
  assumes "inverse (0::'a::{comm_monoid_add,inverse,mult_zero,uminus}) = 0"
  shows   "inverse (0::'a fls) = 0"
  by      (simp add: fls_inverse_zero_conv_fls_const assms)

lemma fls_inverse_zero [simp]: "inverse (0::'a::division_ring fls) = 0"
  by (rule fls_inverse_zero'[OF inverse_zero])

lemma fls_inverse_base2:
  fixes f :: "'a::{comm_monoid_add,mult_zero,uminus,inverse} fls"
  shows "inverse f $$ (-fls_subdegree f) = inverse (f $$ fls_subdegree f)"
  by    (cases "f=0") (simp_all add: fls_inverse_zero_conv_fls_const fls_inverse_def')

lemma fls_lr_inverse_one:
  fixes x :: "'a::{ab_group_add,mult_zero,one}"
  and   y :: "'b::{comm_monoid_add,mult_zero,uminus,one}"
  shows "fls_left_inverse 1 x = fls_const x"
  and   "fls_right_inverse 1 y = fls_const y"
  using fls_lr_inverse_const[of 1]
  by    auto

lemma fls_lr_inverse_one_one:
  "fls_left_inverse 1 1 =
    (1::'a::{ab_group_add,mult_zero,one} fls)"
  "fls_right_inverse 1 1 =
    (1::'b::{comm_monoid_add,mult_zero,uminus,one} fls)"
  using fls_lr_inverse_one[of 1] by auto

lemma fls_inverse_one:
  assumes "inverse (1::'a::{comm_monoid_add,inverse,mult_zero,uminus,one}) = 1"
  shows   "inverse (1::'a fls) = 1"
  using   assms fls_lr_inverse_one_one(2)
  by      (simp add: fls_inverse_def')

lemma fls_left_inverse_delta:
  fixes   b :: "'a::{ab_group_add,mult_zero}"
  assumes "b \<noteq> 0"
  shows   "fls_left_inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) x =
            Abs_fls (\<lambda>n. if n=-a then x else 0)"
proof (intro fls_eqI)
  fix n from assms show
    "fls_left_inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) x $$ n
      = Abs_fls (\<lambda>n. if n = - a then x else 0) $$ n"
    using fls_base_factor_to_fps_delta[of a b]
          fls_lr_inverse_const(1)[of b]
          fls_shift_const
    by    simp
qed

lemma fls_right_inverse_delta:
  fixes   b :: "'a::{comm_monoid_add,mult_zero,uminus}"
  assumes "b \<noteq> 0"
  shows   "fls_right_inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) x =
            Abs_fls (\<lambda>n. if n=-a then x else 0)"
proof (intro fls_eqI)
  fix n from assms show
    "fls_right_inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) x $$ n
      = Abs_fls (\<lambda>n. if n = - a then x else 0) $$ n"
    using fls_base_factor_to_fps_delta[of a b]
          fls_lr_inverse_const(2)[of b]
          fls_shift_const
    by    simp
qed

lemma fls_inverse_delta_nonzero:
  fixes   b :: "'a::{comm_monoid_add,inverse,mult_zero,uminus}"
  assumes "b \<noteq> 0"
  shows   "inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) =
            Abs_fls (\<lambda>n. if n=-a then inverse b else 0)"
  using   assms fls_nonzeroI[of "Abs_fls (\<lambda>n. if n=a then b else 0)" a]
  by      (simp add: fls_inverse_def' fls_right_inverse_delta[symmetric])

lemma fls_inverse_delta:
  fixes   b :: "'a::division_ring"
  shows   "inverse (Abs_fls (\<lambda>n. if n=a then b else 0)) =
            Abs_fls (\<lambda>n. if n=-a then inverse b else 0)"
  by      (cases "b=0") (simp_all add: fls_inverse_delta_nonzero)

lemma fls_lr_inverse_X:
  fixes x :: "'a::{ab_group_add,mult_zero,zero_neq_one}"
  and   y :: "'b::{comm_monoid_add,uminus,mult_zero,zero_neq_one}"
  shows "fls_left_inverse fls_X x = fls_shift 1 (fls_const x)"
  and   "fls_right_inverse fls_X y = fls_shift 1 (fls_const y)"
  using fls_lr_inverse_one(1)[of x] fls_lr_inverse_one(2)[of y]
  by    auto

lemma fls_lr_inverse_X':
  fixes x :: "'a::{ab_group_add,mult_zero,zero_neq_one,monoid_mult}"
  and   y :: "'b::{comm_monoid_add,uminus,mult_zero,zero_neq_one,monoid_mult}"
  shows "fls_left_inverse fls_X x = fls_const x * fls_X_inv"
  and   "fls_right_inverse fls_X y = fls_const y * fls_X_inv"
  using fls_lr_inverse_X(1)[of x] fls_lr_inverse_X(2)[of y]
  by    (simp_all add: fls_X_inv_times_conv_shift(2))

lemma fls_inverse_X':
  assumes "inverse 1 = (1::'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one})"
  shows   "inverse (fls_X::'a fls) = fls_X_inv"
  using   assms fls_lr_inverse_X(2)[of "1::'a"]
  by      (simp add: fls_inverse_def' fls_X_inv_conv_shift_1)

lemma fls_inverse_X: "inverse (fls_X::'a::division_ring fls) = fls_X_inv"
  by (simp add: fls_inverse_X')

lemma fls_lr_inverse_X_inv:
  fixes x :: "'a::{ab_group_add,mult_zero,zero_neq_one}"
  and   y :: "'b::{comm_monoid_add,uminus,mult_zero,zero_neq_one}"
  shows "fls_left_inverse fls_X_inv x = fls_shift (-1) (fls_const x)"
  and   "fls_right_inverse fls_X_inv y = fls_shift (-1) (fls_const y)"
  using fls_lr_inverse_one(1)[of x] fls_lr_inverse_one(2)[of y]
  by    auto

lemma fls_lr_inverse_X_inv':
  fixes x :: "'a::{ab_group_add,mult_zero,zero_neq_one,monoid_mult}"
  and   y :: "'b::{comm_monoid_add,uminus,mult_zero,zero_neq_one,monoid_mult}"
  shows "fls_left_inverse fls_X_inv x = fls_const x * fls_X"
  and   "fls_right_inverse fls_X_inv y = fls_const y * fls_X"
  using fls_lr_inverse_X_inv(1)[of x] fls_lr_inverse_X_inv(2)[of y]
  by    (simp_all add: fls_X_times_conv_shift(2))

lemma fls_inverse_X_inv':
  assumes "inverse 1 = (1::'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one})"
  shows   "inverse (fls_X_inv::'a fls) = fls_X"
  using   assms fls_lr_inverse_X_inv(2)[of "1::'a"]
  by      (simp add: fls_inverse_def' fls_X_conv_shift_1)

lemma fls_inverse_X_inv: "inverse (fls_X_inv::'a::division_ring fls) = fls_X"
  by (simp add: fls_inverse_X_inv')

lemma fls_lr_inverse_subdegree:
  assumes "x \<noteq> 0"
  shows   "fls_subdegree (fls_left_inverse f x) = - fls_subdegree f"
  and     "fls_subdegree (fls_right_inverse f x) = - fls_subdegree f"
  by      (auto intro: fls_subdegree_eqI simp: assms)

lemma fls_inverse_subdegree':
  "inverse (f $$ fls_subdegree f) \<noteq> 0 \<Longrightarrow> fls_subdegree (inverse f) = - fls_subdegree f"
  using fls_lr_inverse_subdegree(2)[of "inverse (f $$ fls_subdegree f)"]
  by    (simp add: fls_inverse_def')

lemma fls_inverse_subdegree [simp]:
  fixes f :: "'a::division_ring fls"
  shows "fls_subdegree (inverse f) = - fls_subdegree f"
  by    (cases "f=0")
        (auto intro: fls_inverse_subdegree' simp: nonzero_imp_inverse_nonzero)

lemma fls_inverse_subdegree_base_nonzero:
  assumes "f \<noteq> 0" "inverse (f $$ fls_subdegree f) \<noteq> 0"
  shows   "inverse f $$ (fls_subdegree (inverse f)) = inverse (f $$ fls_subdegree f)"
  using   assms fls_inverse_subdegree'[of f] fls_inverse_base[of f]
  by      simp

lemma fls_inverse_subdegree_base:
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fls"
  shows "inverse f $$ (fls_subdegree (inverse f)) = inverse (f $$ fls_subdegree f)"
  using fls_inverse_eq_0_iff'[of f] fls_inverse_subdegree_base_nonzero[of f]
  by    (cases "f=0 \<or> inverse (f $$ fls_subdegree f) = 0")
        (auto simp: fls_inverse_zero_conv_fls_const)

lemma fls_lr_inverse_subdegree_0:
  assumes "fls_subdegree f = 0"
  shows   "fls_subdegree (fls_left_inverse f x) \<ge> 0"
  and     "fls_subdegree (fls_right_inverse f x) \<ge> 0"
  using   fls_subdegree_ge0I[of "fls_left_inverse f x"]
          fls_subdegree_ge0I[of "fls_right_inverse f x"]
  by      (auto simp: assms)

lemma fls_inverse_subdegree_0:
  "fls_subdegree f = 0 \<Longrightarrow> fls_subdegree (inverse f) \<ge> 0"
  using fls_lr_inverse_subdegree_0(2)[of f] by (simp add: fls_inverse_def')

lemma fls_lr_inverse_shift_nonzero:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,uminus} fls"
  assumes "f \<noteq> 0"
  shows   "fls_left_inverse (fls_shift m f) x = fls_shift (-m) (fls_left_inverse f x)"
  and     "fls_right_inverse (fls_shift m f) x = fls_shift (-m) (fls_right_inverse f x)"
  using   assms fls_base_factor_to_fps_shift[of m f] fls_shift_subdegree
  by      auto

lemma fls_inverse_shift_nonzero:
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fls"
  assumes "f \<noteq> 0"
  shows   "inverse (fls_shift m f) = fls_shift (-m) (inverse f)"
  using   assms fls_lr_inverse_shift_nonzero(2)[of f m "inverse (f $$ fls_subdegree f)"]
  by      (simp add: fls_inverse_def')

lemma fls_inverse_shift:
  fixes f :: "'a::division_ring fls"
  shows "inverse (fls_shift m f) = fls_shift (-m) (inverse f)"
  using fls_inverse_shift_nonzero
  by    (cases "f=0") simp_all

lemma fls_left_inverse_base_factor:
  fixes   x :: "'a::{ab_group_add,mult_zero}"
  assumes "x \<noteq> 0"
  shows   "fls_left_inverse (fls_base_factor f) x = fls_base_factor (fls_left_inverse f x)"
  using   assms fls_lr_inverse_zero(1)[of x] fls_lr_inverse_subdegree(1)[of x]
  by      (cases "f=0") auto

lemma fls_right_inverse_base_factor:
  fixes   y :: "'a::{comm_monoid_add,mult_zero,uminus}"
  assumes "y \<noteq> 0"
  shows   "fls_right_inverse (fls_base_factor f) y = fls_base_factor (fls_right_inverse f y)"
  using   assms fls_lr_inverse_zero(2)[of y] fls_lr_inverse_subdegree(2)[of y]
  by      (cases "f=0") auto

lemma fls_inverse_base_factor':
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fls"
  assumes "inverse (f $$ fls_subdegree f) \<noteq> 0"
  shows   "inverse (fls_base_factor f) = fls_base_factor (inverse f)"
  by      (cases "f=0")
          (simp_all add:
            assms fls_inverse_shift_nonzero fls_inverse_subdegree'
            fls_inverse_zero_conv_fls_const
          )

lemma fls_inverse_base_factor:
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fls"
  shows "inverse (fls_base_factor f) = fls_base_factor (inverse f)"
  using fls_base_factor_base[of f] fls_inverse_eq_0_iff'[of f]
        fls_inverse_eq_0_iff'[of "fls_base_factor f"] fls_inverse_base_factor'[of f]
  by    (cases "inverse (f $$ fls_subdegree f) = 0") simp_all

lemma fls_lr_inverse_regpart:
  assumes "fls_subdegree f = 0"
  shows   "fls_regpart (fls_left_inverse f x) = fps_left_inverse (fls_regpart f) x"
  and     "fls_regpart (fls_right_inverse f y) = fps_right_inverse (fls_regpart f) y"
  using   assms
  by      auto

lemma fls_inverse_regpart:
  assumes "fls_subdegree f = 0"
  shows   "fls_regpart (inverse f) = inverse (fls_regpart f)"
  by      (simp add: assms fls_inverse_def)

lemma fls_base_factor_to_fps_left_inverse:
  fixes   x :: "'a::{ab_group_add,mult_zero}"
  shows   "fls_base_factor_to_fps (fls_left_inverse f x) =
            fps_left_inverse (fls_base_factor_to_fps f) x"
  using   fls_left_inverse_base_factor[of x f] fls_base_factor_subdegree[of f]
  by      (cases "x=0") (simp_all add: fls_lr_inverse_starting0(1) fps_lr_inverse_starting0(1))

lemma fls_base_factor_to_fps_right_inverse_nonzero:
  fixes   y :: "'a::{comm_monoid_add,mult_zero,uminus}"
  assumes "y \<noteq> 0"
  shows   "fls_base_factor_to_fps (fls_right_inverse f y) =
            fps_right_inverse (fls_base_factor_to_fps f) y"
  using   assms fls_right_inverse_base_factor[of y f]
          fls_base_factor_subdegree[of f]
  by      simp

lemma fls_base_factor_to_fps_right_inverse:
  fixes   y :: "'a::{ab_group_add,mult_zero}"
  shows   "fls_base_factor_to_fps (fls_right_inverse f y) =
            fps_right_inverse (fls_base_factor_to_fps f) y"
  using   fls_base_factor_to_fps_right_inverse_nonzero[of y f]
  by      (cases "y=0") (simp_all add: fls_lr_inverse_starting0(2) fps_lr_inverse_starting0(2))

lemma fls_base_factor_to_fps_inverse_nonzero:
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fls"
  assumes "inverse (f $$ fls_subdegree f) \<noteq> 0"
  shows   "fls_base_factor_to_fps (inverse f) = inverse (fls_base_factor_to_fps f)"
  using   assms fls_base_factor_to_fps_right_inverse_nonzero
  by      (simp add: fls_inverse_def' fps_inverse_def)

lemma fls_base_factor_to_fps_inverse:
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fls"
  shows "fls_base_factor_to_fps (inverse f) = inverse (fls_base_factor_to_fps f)"
  using fls_base_factor_to_fps_right_inverse
  by    (simp add: fls_inverse_def' fps_inverse_def)

lemma fls_lr_inverse_fps_to_fls:
  assumes "subdegree f = 0"
  shows   "fls_left_inverse (fps_to_fls f) x = fps_to_fls (fps_left_inverse f x)"
  and     "fls_right_inverse (fps_to_fls f) x = fps_to_fls (fps_right_inverse f x)"
  using   assms fls_base_factor_to_fps_to_fls[of f]
  by      (simp_all add: fls_subdegree_fls_to_fps)

lemma fls_inverse_fps_to_fls:
  "subdegree f = 0 \<Longrightarrow> inverse (fps_to_fls f) = fps_to_fls (inverse f)"
  using nth_subdegree_nonzero[of f]
  by  (cases "f=0")
      (auto simp add:
        fps_to_fls_nonzeroI fls_inverse_def' fls_subdegree_fls_to_fps fps_inverse_def
        fls_lr_inverse_fps_to_fls(2)
      )

lemma fls_lr_inverse_X_power:
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X ^ n) x = fls_shift n (fls_const x)"
  and   "fls_right_inverse (fls_X ^ n) y = fls_shift n (fls_const y)"
  using fls_lr_inverse_one(1)[of x] fls_lr_inverse_one(2)[of y]
  by    (simp_all add: fls_X_power_conv_shift_1)

lemma fls_lr_inverse_X_power':
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X ^ n) x = fls_const x * fls_X_inv ^ n"
  and   "fls_right_inverse (fls_X ^ n) y = fls_const y * fls_X_inv ^ n"
  using fls_lr_inverse_X_power(1)[of n x] fls_lr_inverse_X_power(2)[of n y]
  by    (simp_all add: fls_X_inv_power_times_conv_shift(2))

lemma fls_inverse_X_power':
  assumes "inverse 1 = (1::'a::{semiring_1,uminus,inverse})"
  shows   "inverse ((fls_X ^ n)::'a fls) = fls_X_inv ^ n"
  using   fls_lr_inverse_X_power'(2)[of n 1]
  by      (simp add: fls_inverse_def' assms )

lemma fls_inverse_X_power:
  "inverse ((fls_X::'a::division_ring fls) ^ n) = fls_X_inv ^ n"
  by (simp add: fls_inverse_X_power')

lemma fls_lr_inverse_X_inv_power:
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X_inv ^ n) x = fls_shift (-n) (fls_const x)"
  and   "fls_right_inverse (fls_X_inv ^ n) y = fls_shift (-n) (fls_const y)"
  using fls_lr_inverse_one(1)[of x] fls_lr_inverse_one(2)[of y]
  by    (simp_all add: fls_X_inv_power_conv_shift_1)

lemma fls_lr_inverse_X_inv_power':
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X_inv ^ n) x = fls_const x * fls_X ^ n"
  and   "fls_right_inverse (fls_X_inv ^ n) y = fls_const y * fls_X ^ n"
  using fls_lr_inverse_X_inv_power(1)[of n x] fls_lr_inverse_X_inv_power(2)[of n y]
  by    (simp_all add: fls_X_power_times_conv_shift(2))

lemma fls_inverse_X_inv_power':
  assumes "inverse 1 = (1::'a::{semiring_1,uminus,inverse})"
  shows   "inverse ((fls_X_inv ^ n)::'a fls) = fls_X ^ n"
  using   fls_lr_inverse_X_inv_power'(2)[of n 1]
  by      (simp add: fls_inverse_def' assms)

lemma fls_inverse_X_inv_power:
  "inverse ((fls_X_inv::'a::division_ring fls) ^ n) = fls_X ^ n"
  by (simp add: fls_inverse_X_inv_power')

lemma fls_lr_inverse_X_intpow:
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X_intpow i) x = fls_shift i (fls_const x)"
  and   "fls_right_inverse (fls_X_intpow i) y = fls_shift i (fls_const y)"
  using fls_lr_inverse_one(1)[of x] fls_lr_inverse_one(2)[of y]
  by    auto

lemma fls_lr_inverse_X_intpow':
  fixes x :: "'a::ring_1"
  and   y :: "'b::{semiring_1,uminus}"
  shows "fls_left_inverse (fls_X_intpow i) x = fls_const x * fls_X_intpow (-i)"
  and   "fls_right_inverse (fls_X_intpow i) y = fls_const y * fls_X_intpow (-i)"
  using fls_lr_inverse_X_intpow(1)[of i x] fls_lr_inverse_X_intpow(2)[of i y]
  by    (simp_all add: fls_shifted_times_simps(1))

lemma fls_inverse_X_intpow':
  assumes "inverse 1 = (1::'a::{semiring_1,uminus,inverse})"
  shows   "inverse (fls_X_intpow i :: 'a fls) = fls_X_intpow (-i)"
  using   fls_lr_inverse_X_intpow'(2)[of i 1]
  by      (simp add: fls_inverse_def' assms)

lemma fls_inverse_X_intpow:
  "inverse (fls_X_intpow i :: 'a::division_ring fls) = fls_X_intpow (-i)"
  by (simp add: fls_inverse_X_intpow')

lemma fls_left_inverse:
  fixes   f :: "'a::ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1"
  shows   "fls_left_inverse f x * f = 1"
proof-
  from assms have "x \<noteq> 0" "x * (fls_base_factor_to_fps f$0) = 1" by auto
  thus ?thesis
    using fls_base_factor_to_fps_left_inverse[of f x]
          fls_lr_inverse_subdegree(1)[of x] fps_left_inverse
    by    (fastforce simp: fls_times_def)
qed

lemma fls_right_inverse:
  fixes   f :: "'a::ring_1 fls"
  assumes "f $$ fls_subdegree f * y = 1"
  shows   "f * fls_right_inverse f y = 1"
proof-
  from assms have "y \<noteq> 0" "(fls_base_factor_to_fps f$0) * y = 1" by auto
  thus ?thesis
    using fls_base_factor_to_fps_right_inverse[of f y]
          fls_lr_inverse_subdegree(2)[of y] fps_right_inverse
    by    (fastforce simp: fls_times_def)
qed

\<comment> \<open>
  It is possible in a ring for an element to have a left inverse but not a right inverse, or
  vice versa. But when an element has both, they must be the same.
\<close>
lemma fls_left_inverse_eq_fls_right_inverse:
  fixes   f :: "'a::ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fls_left_inverse f x = fls_right_inverse f y"
  using   assms
  by      (simp add: fps_left_inverse_eq_fps_right_inverse)

lemma fls_left_inverse_eq_inverse:
  fixes   f :: "'a::division_ring fls"
  shows   "fls_left_inverse f (inverse (f $$ fls_subdegree f)) = inverse f"
proof (cases "f=0")
  case True
  hence "fls_left_inverse f (inverse (f $$ fls_subdegree f)) = fls_const (0::'a)"
    by (simp add: fls_lr_inverse_zero(1)[symmetric])
  with True show ?thesis by simp
next
  case False thus ?thesis
    using fls_left_inverse_eq_fls_right_inverse[of "inverse (f $$ fls_subdegree f)"]
    by    (auto simp add: fls_inverse_def')
qed

lemma fls_right_inverse_eq_inverse:
  fixes f :: "'a::division_ring fls"
  shows "fls_right_inverse f (inverse (f $$ fls_subdegree f)) = inverse f"
proof (cases "f=0")
  case True
  hence "fls_right_inverse f (inverse (f $$ fls_subdegree f)) = fls_const (0::'a)"
    by (simp add: fls_lr_inverse_zero(2)[symmetric])
  with True show ?thesis by simp
qed (simp add: fls_inverse_def')

lemma fls_left_inverse_eq_fls_right_inverse_comm:
  fixes   f :: "'a::comm_ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1"
  shows   "fls_left_inverse f x = fls_right_inverse f x"
  using   assms fls_left_inverse_eq_fls_right_inverse[of x f x]
  by      (simp add: mult.commute)

lemma fls_left_inverse':
  fixes   f :: "'a::ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fls_right_inverse f y * f = 1"
  using   assms fls_left_inverse_eq_fls_right_inverse[of x f y] fls_left_inverse[of x f]
  by      simp

lemma fls_right_inverse':
  fixes   f :: "'a::ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "f * fls_left_inverse f x = 1"
  using   assms fls_left_inverse_eq_fls_right_inverse[of x f y] fls_right_inverse[of f y]
  by      simp

lemma fls_mult_left_inverse_base_factor:
  fixes   f :: "'a::ring_1 fls"
  assumes "x * (f $$ fls_subdegree f) = 1"
  shows   "fls_left_inverse (fls_base_factor f) x * f = fls_X_intpow (fls_subdegree f)"
  using   assms fls_base_factor_to_fps_base_factor[of f] fls_base_factor_subdegree[of f]
          fls_shifted_times_simps(2)[of "-fls_subdegree f" "fls_left_inverse f x" f]
          fls_left_inverse[of x f]
  by      simp

lemma fls_mult_right_inverse_base_factor:
  fixes   f :: "'a::ring_1 fls"
  assumes "(f $$ fls_subdegree f) * y = 1"
  shows   "f * fls_right_inverse (fls_base_factor f) y = fls_X_intpow (fls_subdegree f)"
  using   assms fls_base_factor_to_fps_base_factor[of f] fls_base_factor_subdegree[of f]
          fls_shifted_times_simps(1)[of f "-fls_subdegree f" "fls_right_inverse f y"]
          fls_right_inverse[of f y]
  by      simp

lemma fls_mult_inverse_base_factor:
  fixes   f :: "'a::division_ring fls"
  assumes "f \<noteq> 0"
  shows   "f * inverse (fls_base_factor f) = fls_X_intpow (fls_subdegree f)"
  using   fls_mult_right_inverse_base_factor[of f "inverse (f $$ fls_subdegree f)"]
          fls_base_factor_base[of f]
  by      (simp add: assms fls_right_inverse_eq_inverse[symmetric])

lemma fls_left_inverse_idempotent_ring1:
  fixes   f :: "'a::ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1" "y * x = 1"
  \<comment> \<open>These assumptions imply y equals \<open>f $$ fls_subdegree f\<close>, but no need to assume that.\<close>
  shows   "fls_left_inverse (fls_left_inverse f x) y = f"
proof-
  from assms(1) have
    "fls_left_inverse (fls_left_inverse f x) y * fls_left_inverse f x * f =
      fls_left_inverse (fls_left_inverse f x) y"
    using fls_left_inverse[of x f]
    by    (simp add: mult.assoc)
  moreover have
    "fls_left_inverse (fls_left_inverse f x) y * fls_left_inverse f x = 1"
    using assms fls_lr_inverse_subdegree(1)[of x f] fls_lr_inverse_base(1)[of f x]
    by    (fastforce intro: fls_left_inverse)
  ultimately show ?thesis by simp
qed

lemma fls_left_inverse_idempotent_comm_ring1:
  fixes   f :: "'a::comm_ring_1 fls"
  assumes "x * f $$ fls_subdegree f = 1"
  shows   "fls_left_inverse (fls_left_inverse f x) (f $$ fls_subdegree f) = f"
  using   assms fls_left_inverse_idempotent_ring1[of x f "f $$ fls_subdegree f"]
  by      (simp add: mult.commute)

lemma fls_right_inverse_idempotent_ring1:
  fixes   f :: "'a::ring_1 fls"
  assumes "f $$ fls_subdegree f * x = 1" "x * y = 1"
  \<comment> \<open>These assumptions imply y equals \<open>f $$ fls_subdegree f\<close>, but no need to assume that.\<close>
  shows   "fls_right_inverse (fls_right_inverse f x) y = f"
proof-
  from assms(1) have
    "f * (fls_right_inverse f x * fls_right_inverse (fls_right_inverse f x) y) =
      fls_right_inverse (fls_right_inverse f x) y"
    using fls_right_inverse [of f] 
    by (simp add: mult.assoc[symmetric])
  moreover have
    "fls_right_inverse f x * fls_right_inverse (fls_right_inverse f x) y = 1"
    using assms fls_lr_inverse_subdegree(2)[of x f] fls_lr_inverse_base(2)[of f x]
    by    (fastforce intro: fls_right_inverse)
  ultimately show ?thesis by simp
qed

lemma fls_right_inverse_idempotent_comm_ring1:
  fixes   f :: "'a::comm_ring_1 fls"
  assumes "f $$ fls_subdegree f * x = 1"
  shows   "fls_right_inverse (fls_right_inverse f x) (f $$ fls_subdegree f) = f"
  using   assms fls_right_inverse_idempotent_ring1[of f x "f $$ fls_subdegree f"]
  by      (simp add: mult.commute)

lemma fls_lr_inverse_unique_ring1:
  fixes   f g :: "'a :: ring_1 fls"
  assumes fg: "f * g = 1" "g $$ fls_subdegree g * f $$ fls_subdegree f = 1"
  shows   "fls_left_inverse g (f $$ fls_subdegree f) = f"
  and     "fls_right_inverse f (g $$ fls_subdegree g) = g"
proof-

  have "f $$ fls_subdegree f * g $$ fls_subdegree g \<noteq> 0"
  proof
    assume "f $$ fls_subdegree f * g $$ fls_subdegree g = 0"
    hence "f $$ fls_subdegree f * (g $$ fls_subdegree g * f $$ fls_subdegree f) = 0"
      by (simp add: mult.assoc[symmetric])
    with fg(2) show False by simp
  qed
  with fg(1) have subdeg_sum: "fls_subdegree f + fls_subdegree g = 0"
    using fls_mult_nonzero_base_subdegree_eq[of f g] by simp
  hence subdeg_sum':
    "fls_subdegree f = -fls_subdegree g" "fls_subdegree g = -fls_subdegree f"
    by auto

  from fg(1) have f_ne_0: "f\<noteq>0" by auto
  moreover have
    "fps_left_inverse (fls_base_factor_to_fps g) (fls_regpart (fls_shift (-fls_subdegree g) f)$0)
      = fls_regpart (fls_shift (-fls_subdegree g) f)"
  proof (intro fps_lr_inverse_unique_ring1(1))
    from fg(1) show
      "fls_regpart (fls_shift (-fls_subdegree g) f) * fls_base_factor_to_fps g = 1"
      using f_ne_0 fls_times_conv_regpart[of "fls_shift (-fls_subdegree g) f" "fls_base_factor g"]
            fls_base_factor_subdegree[of g]
      by    (simp add: fls_times_both_shifted_simp subdeg_sum)
    from fg(2) show
      "fls_base_factor_to_fps g $ 0 * fls_regpart (fls_shift (-fls_subdegree g) f) $ 0 = 1"
      by (simp add: subdeg_sum'(2))
  qed
  ultimately show "fls_left_inverse g (f $$ fls_subdegree f) = f"
    by (simp add: subdeg_sum'(2))

  from fg(1) have g_ne_0: "g\<noteq>0" by auto
  moreover have
    "fps_right_inverse (fls_base_factor_to_fps f) (fls_regpart (fls_shift (-fls_subdegree f) g)$0)
      = fls_regpart (fls_shift (-fls_subdegree f) g)"
  proof (intro fps_lr_inverse_unique_ring1(2))
    from fg(1) show
      "fls_base_factor_to_fps f * fls_regpart (fls_shift (-fls_subdegree f) g) = 1"
      using g_ne_0 fls_times_conv_regpart[of "fls_base_factor f" "fls_shift (-fls_subdegree f) g"]
            fls_base_factor_subdegree[of f]
      by    (simp add: fls_times_both_shifted_simp subdeg_sum add.commute)
    from fg(2) show
      "fls_regpart (fls_shift (-fls_subdegree f) g) $ 0 * fls_base_factor_to_fps f $ 0 = 1"
      by (simp add: subdeg_sum'(1))
  qed
  ultimately show "fls_right_inverse f (g $$ fls_subdegree g) = g"
    by (simp add: subdeg_sum'(2))

qed

lemma fls_lr_inverse_unique_divring:
  fixes   f g :: "'a ::division_ring fls"
  assumes fg: "f * g = 1"
  shows   "fls_left_inverse g (f $$ fls_subdegree f) = f"
  and     "fls_right_inverse f (g $$ fls_subdegree g) = g"
proof-
  from fg have "f \<noteq>0" "g \<noteq> 0" by auto
  with fg have "fls_subdegree f + fls_subdegree g = 0" using fls_subdegree_mult by force
  with fg have "f $$ fls_subdegree f * g $$ fls_subdegree g = 1"
    using fls_times_base[of f g] by simp
  hence "g $$ fls_subdegree g * f $$ fls_subdegree f = 1"
    using inverse_unique[of "f $$ fls_subdegree f"] left_inverse[of "f $$ fls_subdegree f"]
    by    force
  thus
    "fls_left_inverse g (f $$ fls_subdegree f) = f"
    "fls_right_inverse f (g $$ fls_subdegree g) = g"
    using fg fls_lr_inverse_unique_ring1
    by    auto
qed

lemma fls_lr_inverse_minus:
  fixes f :: "'a::ring_1 fls"
  shows "fls_left_inverse (-f) (-x) = - fls_left_inverse f x"
  and   "fls_right_inverse (-f) (-x) = - fls_right_inverse f x"
  by (simp_all add: fps_lr_inverse_minus)

lemma fls_inverse_minus [simp]: "inverse (-f) = -inverse (f :: 'a :: division_ring fls)"
  using fls_lr_inverse_minus(2)[of f] by (simp add: fls_inverse_def')

lemma fls_lr_inverse_mult_ring1:
  fixes   f g :: "'a::ring_1 fls"
  assumes x: "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * x = 1"
  and     y: "y * g $$ fls_subdegree g = 1" "g $$ fls_subdegree g * y = 1"
  shows   "fls_left_inverse (f * g) (y*x) = fls_left_inverse g y * fls_left_inverse f x"
  and     "fls_right_inverse (f * g) (y*x) = fls_right_inverse g y * fls_right_inverse f x"
proof-
  from x(1) y(2) have "x * (f $$ fls_subdegree f * g $$ fls_subdegree g) * y = 1"
    by (simp add: mult.assoc)
  hence base_prod: "f $$ fls_subdegree f * g $$ fls_subdegree g \<noteq> 0" by auto
  hence subdegrees: "fls_subdegree (f*g) = fls_subdegree f + fls_subdegree g"
    using fls_mult_nonzero_base_subdegree_eq[of f g] by simp

  have norm:
    "fls_base_factor_to_fps (f * g) = fls_base_factor_to_fps f * fls_base_factor_to_fps g"
    using base_prod fls_base_factor_to_fps_mult'[of f g] by simp

  have
    "fls_left_inverse (f * g) (y*x) =
      fls_shift (fls_subdegree (f * g)) (
        fps_to_fls (
          fps_left_inverse (fls_base_factor_to_fps f * fls_base_factor_to_fps g) (y*x)
        )
      )
    "
    using norm
    by    simp
  thus "fls_left_inverse (f * g) (y*x) = fls_left_inverse g y * fls_left_inverse f x"
    using x y
          fps_lr_inverse_mult_ring1(1)[of
            x "fls_base_factor_to_fps f" y "fls_base_factor_to_fps g"
          ]
    by    (simp add:
            fls_times_both_shifted_simp fls_times_fps_to_fls subdegrees algebra_simps
          )

  have
    "fls_right_inverse (f * g) (y*x) =
      fls_shift (fls_subdegree (f * g)) (
        fps_to_fls (
          fps_right_inverse (fls_base_factor_to_fps f * fls_base_factor_to_fps g) (y*x)
        )
      )
    "
    using norm
    by    simp
  thus "fls_right_inverse (f * g) (y*x) = fls_right_inverse g y * fls_right_inverse f x"
    using x y
          fps_lr_inverse_mult_ring1(2)[of
            x "fls_base_factor_to_fps f" y "fls_base_factor_to_fps g"
          ]
    by    (simp add:
            fls_times_both_shifted_simp fls_times_fps_to_fls subdegrees algebra_simps
          )

qed

lemma fls_lr_inverse_power_ring1:
  fixes   f :: "'a::ring_1 fls"
  assumes x: "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * x = 1"
  shows   "fls_left_inverse (f ^ n) (x ^ n) = (fls_left_inverse f x) ^ n"
          "fls_right_inverse (f ^ n) (x ^ n) = (fls_right_inverse f x) ^ n"
proof-

  show "fls_left_inverse (f ^ n) (x ^ n) = (fls_left_inverse f x) ^ n"
  proof (induct n)
    case 0 show ?case using fls_lr_inverse_one(1)[of 1] by simp
  next
    case (Suc n) with assms show ?case
      using fls_lr_inverse_mult_ring1(1)[of x f "x^n" "f^n"]
      by    (simp add:
              power_Suc2[symmetric] fls_unit_base_subdegree_power(1) left_right_inverse_power
            )
  qed

  show "fls_right_inverse (f ^ n) (x ^ n) = (fls_right_inverse f x) ^ n"
  proof (induct n)
    case 0 show ?case using fls_lr_inverse_one(2)[of 1] by simp
  next
    case (Suc n) with assms show ?case
      using fls_lr_inverse_mult_ring1(2)[of x f "x^n" "f^n"]
      by    (simp add:
              power_Suc2[symmetric] fls_unit_base_subdegree_power(1) left_right_inverse_power
            )
  qed

qed

lemma fls_divide_convert_times_inverse:
  fixes   f g :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fls"
  shows   "f / g = f * inverse g"
  using fls_base_factor_to_fps_subdegree[of g] fps_to_fls_base_factor_to_fps[of f]
        fls_times_both_shifted_simp[of "-fls_subdegree f" "fls_base_factor f"]
  by    (simp add:
          fls_divide_def fps_divide_unit' fls_times_fps_to_fls
          fls_conv_base_factor_shift_subdegree fls_inverse_def
        )

instance fls :: (division_ring) division_ring
proof
  fix a b :: "'a fls"
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
    using fls_left_inverse'[of "inverse (a $$ fls_subdegree a)" a]
    by    (simp add: fls_inverse_def')
  show "a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
    using fls_right_inverse[of a]
    by    (simp add: fls_inverse_def')
  show "a / b = a * inverse b" using fls_divide_convert_times_inverse by fast
  show "inverse (0::'a fls) = 0" by simp
qed

lemma fls_lr_inverse_mult_divring:
  fixes   f g   :: "'a::division_ring fls"
  and     df dg :: int
  defines "df \<equiv> fls_subdegree f"
  and     "dg \<equiv> fls_subdegree g"
  shows   "fls_left_inverse (f*g) (inverse ((f*g)$$(df+dg))) =
            fls_left_inverse g (inverse (g$$dg)) * fls_left_inverse f (inverse (f$$df))"
  and     "fls_right_inverse (f*g) (inverse ((f*g)$$(df+dg))) =
            fls_right_inverse g (inverse (g$$dg)) * fls_right_inverse f (inverse (f$$df))"
proof -
  show
    "fls_left_inverse (f*g) (inverse ((f*g)$$(df+dg))) =
      fls_left_inverse g (inverse (g$$dg)) * fls_left_inverse f (inverse (f$$df))"
  proof (cases "f=0 \<or> g=0")
    case True thus ?thesis
      using fls_lr_inverse_zero(1)[of "inverse (0::'a)"] by (auto simp add: assms)
  next
    case False thus ?thesis
      using fls_left_inverse_eq_inverse[of "f*g"] nonzero_inverse_mult_distrib[of f g]
            fls_left_inverse_eq_inverse[of g] fls_left_inverse_eq_inverse[of f]
      by    (simp add: assms)
  qed
  show
    "fls_right_inverse (f*g) (inverse ((f*g)$$(df+dg))) =
      fls_right_inverse g (inverse (g$$dg)) * fls_right_inverse f (inverse (f$$df))"
  proof (cases "f=0 \<or> g=0")
    case True thus ?thesis
      using fls_lr_inverse_zero(2)[of "inverse (0::'a)"] by (auto simp add: assms)
  next
    case False thus ?thesis
      using fls_inverse_def'[of "f*g"] nonzero_inverse_mult_distrib[of f g]
            fls_inverse_def'[of g] fls_inverse_def'[of f]
      by    (simp add: assms)
  qed
qed

lemma fls_lr_inverse_power_divring:
  "fls_left_inverse (f ^ n) ((inverse (f $$ fls_subdegree f)) ^ n) =
    (fls_left_inverse f (inverse (f $$ fls_subdegree f))) ^ n" (is ?P)
  and "fls_right_inverse (f ^ n) ((inverse (f $$ fls_subdegree f)) ^ n) =
    (fls_right_inverse f (inverse (f $$ fls_subdegree f))) ^ n" (is ?Q)
  for f :: "'a::division_ring fls"
proof -
  note fls_left_inverse_eq_inverse [of f] fls_right_inverse_eq_inverse[of f]
  moreover have
    "fls_right_inverse (f ^ n) ((inverse (f $$ fls_subdegree f)) ^ n) =
      inverse f ^ n"
    using fls_right_inverse_eq_inverse [of "f ^ n"]
    by (simp add: fls_subdegree_pow power_inverse)
  moreover have
    "fls_left_inverse (f ^ n) ((inverse (f $$ fls_subdegree f)) ^ n) =
      inverse f ^ n"
    using fls_left_inverse_eq_inverse [of "f ^ n"]
    by (simp add: fls_subdegree_pow power_inverse)
  ultimately show ?P and ?Q
    by simp_all
qed

instance fls :: (field) field
  by (standard, simp_all add: field_simps)

instance fls :: ("{field_prime_char,comm_semiring_1}") field_prime_char
  by (rule field_prime_charI') auto


subsubsection \<open>Division\<close>

lemma fls_divide_nth_below:
  fixes f g :: "'a::{comm_monoid_add,uminus,times,inverse} fls"
  shows "n < fls_subdegree f - fls_subdegree g \<Longrightarrow> (f div g) $$ n = 0"
  by    (simp add: fls_divide_def)

lemma fls_divide_nth_base:
  fixes f g :: "'a::division_ring fls"
  shows
    "(f div g) $$ (fls_subdegree f - fls_subdegree g) =
      f $$ fls_subdegree f / g $$ fls_subdegree g"
  using fps_divide_nth_0'[of "fls_base_factor_to_fps g" "fls_base_factor_to_fps f"]
        fls_base_factor_to_fps_subdegree[of g]
  by    (simp add: fls_divide_def)

lemma fls_div_zero [simp]:
  "0 div (g :: 'a :: {comm_monoid_add,inverse,mult_zero,uminus} fls) = 0"
  by (simp add: fls_divide_def)

lemma fls_div_by_zero:
  fixes   g :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fls"
  assumes "inverse (0::'a) = 0"
  shows   "g div 0 = 0"
  by      (simp add: fls_divide_def assms fps_div_by_zero')

lemma fls_divide_times:
  fixes f g :: "'a::{semiring_0,inverse,uminus} fls"
  shows "(f * g) / h = f * (g / h)"
  by    (simp add: fls_divide_convert_times_inverse mult.assoc)

lemma fls_divide_times2:
  fixes f g :: "'a::{comm_semiring_0,inverse,uminus} fls"
  shows "(f * g) / h = (f / h) * g"
  using fls_divide_times[of g f h]
  by    (simp add: mult.commute)

lemma fls_divide_subdegree_ge:
  fixes   f g :: "'a::{comm_monoid_add,uminus,times,inverse} fls"
  assumes "f / g \<noteq> 0"
  shows   "fls_subdegree (f / g) \<ge> fls_subdegree f - fls_subdegree g"
  using   assms fls_divide_nth_below
  by      (intro fls_subdegree_geI) simp

lemma fls_divide_subdegree:
  fixes   f g :: "'a::division_ring fls"
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows   "fls_subdegree (f / g) = fls_subdegree f - fls_subdegree g"
proof (intro antisym)
  from assms have "f $$ fls_subdegree f / g $$ fls_subdegree g \<noteq> 0" by (simp add: field_simps)
  thus "fls_subdegree (f/g) \<le> fls_subdegree f - fls_subdegree g"
    using fls_divide_nth_base[of f g] by (intro fls_subdegree_leI) simp
  from assms have "f / g \<noteq> 0" by (simp add: field_simps)
  thus "fls_subdegree (f/g) \<ge> fls_subdegree f - fls_subdegree g"
    using fls_divide_subdegree_ge by fast
qed

lemma fls_divide_shift_numer_nonzero:
  fixes   f g :: "'a :: {comm_monoid_add,inverse,times,uminus} fls"
  assumes "f \<noteq> 0"
  shows   "fls_shift m f / g = fls_shift m (f/g)"
  using   assms fls_base_factor_to_fps_shift[of m f]
  by      (simp add: fls_divide_def algebra_simps)

lemma fls_divide_shift_numer:
  fixes f g :: "'a :: {comm_monoid_add,inverse,mult_zero,uminus} fls"
  shows "fls_shift m f / g = fls_shift m (f/g)"
  using fls_divide_shift_numer_nonzero
  by    (cases "f=0") auto

lemma fls_divide_shift_denom_nonzero:
  fixes   f g :: "'a :: {comm_monoid_add,inverse,times,uminus} fls"
  assumes "g \<noteq> 0"
  shows   "f / fls_shift m g = fls_shift (-m) (f/g)"
  using   assms fls_base_factor_to_fps_shift[of m g]
  by      (simp add: fls_divide_def algebra_simps)

lemma fls_divide_shift_denom:
  fixes   f g :: "'a :: division_ring fls"
  shows   "f / fls_shift m g = fls_shift (-m) (f/g)"
  using   fls_divide_shift_denom_nonzero
  by      (cases "g=0") auto

lemma fls_divide_shift_both_nonzero:
  fixes   f g :: "'a :: {comm_monoid_add,inverse,times,uminus} fls"
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows   "fls_shift n f / fls_shift m g = fls_shift (n-m) (f/g)"
  by      (simp add: assms fls_divide_shift_numer_nonzero fls_divide_shift_denom_nonzero)

lemma fls_divide_shift_both [simp]:
  fixes   f g :: "'a :: division_ring fls"
  shows   "fls_shift n f / fls_shift m g = fls_shift (n-m) (f/g)"
  using   fls_divide_shift_both_nonzero
  by      (cases "f=0 \<or> g=0") auto

lemma fls_divide_base_factor_numer:
  "fls_base_factor f / g = fls_shift (fls_subdegree f) (f/g)"
  using fls_base_factor_to_fps_base_factor[of f]
        fls_base_factor_subdegree[of f]
  by    (simp add: fls_divide_def algebra_simps)

lemma fls_divide_base_factor_denom:
  "f / fls_base_factor g = fls_shift (-fls_subdegree g) (f/g)"
  using fls_base_factor_to_fps_base_factor[of g]
        fls_base_factor_subdegree[of g]
  by    (simp add: fls_divide_def)

lemma fls_divide_base_factor':
  "fls_base_factor f / fls_base_factor g = fls_shift (fls_subdegree f - fls_subdegree g) (f/g)"
  using fls_divide_base_factor_numer[of f "fls_base_factor g"]
        fls_divide_base_factor_denom[of f g]
  by    simp

lemma fls_divide_base_factor:
  fixes f g :: "'a :: division_ring fls"
  shows "fls_base_factor f / fls_base_factor g = fls_base_factor (f/g)"
  using fls_divide_subdegree[of f g] fls_divide_base_factor'
  by    fastforce

lemma fls_divide_regpart:
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fls"
  assumes "fls_subdegree f \<ge> 0" "fls_subdegree g \<ge> 0"
  shows   "fls_regpart (f / g) = fls_regpart f / fls_regpart g"
proof -
  have deg0:
    "\<And>g. fls_subdegree g = 0 \<Longrightarrow>
      fls_regpart (f / g) = fls_regpart f / fls_regpart g"
    by  (simp add:
          assms(1) fls_divide_convert_times_inverse fls_inverse_subdegree_0
          fls_times_conv_regpart fls_inverse_regpart fls_regpart_subdegree_conv fps_divide_unit'
        )
  show ?thesis
  proof (cases "fls_subdegree g = 0")
    case False
    hence "fls_base_factor g \<noteq> 0" using fls_base_factor_nonzero[of g] by force
    with assms(2) show ?thesis
      using fls_divide_shift_denom_nonzero[of "fls_base_factor g" f "-fls_subdegree g"]
            fps_shift_fls_regpart_conv_fls_shift[of
              "nat (fls_subdegree g)" "f / fls_base_factor g"
            ]
            fls_base_factor_subdegree[of g] deg0
            fls_regpart_subdegree_conv[of g] fps_unit_factor_fls_regpart[of g]
      by    (simp add:
              fls_conv_base_factor_shift_subdegree fls_regpart_subdegree_conv fps_divide_def
            )
  qed (rule deg0)
qed

lemma fls_divide_fls_base_factor_to_fps':
  fixes f g :: "'a::{comm_monoid_add,uminus,inverse,mult_zero} fls"
  shows
    "fls_base_factor_to_fps f / fls_base_factor_to_fps g =
      fls_regpart (fls_shift (fls_subdegree f - fls_subdegree g) (f / g))"
  using fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of g]
        fls_divide_regpart[of "fls_base_factor f" "fls_base_factor g"]
        fls_divide_base_factor'[of f g]
    by  simp

lemma fls_divide_fls_base_factor_to_fps:
  fixes f g :: "'a::division_ring fls"
  shows "fls_base_factor_to_fps f / fls_base_factor_to_fps g = fls_base_factor_to_fps (f / g)"
  using fls_divide_fls_base_factor_to_fps' fls_divide_subdegree[of f g]
  by    fastforce

lemma fls_divide_fps_to_fls:
  fixes f g :: "'a::{inverse,ab_group_add,mult_zero} fps"
  assumes "subdegree f \<ge> subdegree g"
  shows   "fps_to_fls f / fps_to_fls g = fps_to_fls (f/g)"
proof-
  have 1:
    "fps_to_fls f / fps_to_fls g =
      fls_shift (int (subdegree g)) (fps_to_fls (f * inverse (unit_factor g)))"
    using fls_base_factor_to_fps_to_fls[of f] fls_base_factor_to_fps_to_fls[of g]
          fls_subdegree_fls_to_fps[of f] fls_subdegree_fls_to_fps[of g]
          fps_divide_def[of "unit_factor f" "unit_factor g"]
          fls_times_fps_to_fls[of "unit_factor f" "inverse (unit_factor g)"]
          fls_shifted_times_simps(2)[of "-int (subdegree f)" "fps_to_fls (unit_factor f)"]
          fls_times_fps_to_fls[of f "inverse (unit_factor g)"]
    by    (simp add: fls_divide_def)
  with assms show ?thesis
    using fps_mult_subdegree_ge[of f "inverse (unit_factor g)"]
          fps_shift_to_fls[of "subdegree g" "f * inverse (unit_factor g)"]
    by    (cases "f * inverse (unit_factor g) = 0") (simp_all add: fps_divide_def)
qed

lemma fls_divide_1':
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one,monoid_mult} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / 1 = f"
  using   assms fls_conv_base_factor_to_fps_shift_subdegree[of f]
  by      (simp add: fls_divide_def fps_divide_1')

lemma fls_divide_1 [simp]: "a / 1 = (a::'a::division_ring fls)"
  by (rule fls_divide_1'[OF inverse_1])

lemma fls_const_divide_const:
  fixes x y :: "'a::division_ring"
  shows "fls_const x / fls_const y = fls_const (x/y)"
  by    (simp add: fls_divide_def fls_base_factor_to_fps_const fps_const_divide)

lemma fls_divide_X':
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one,monoid_mult} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / fls_X = fls_shift 1 f"
proof-
  from assms have
    "f / fls_X =
      fls_shift 1 (fls_shift (-fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f)))"
    by (simp add: fls_divide_def fps_divide_1')
  also have "\<dots> = fls_shift 1 f"
    using fls_conv_base_factor_to_fps_shift_subdegree[of f]
    by simp
  finally show ?thesis by simp
qed

lemma fls_divide_X [simp]:
  fixes f :: "'a::division_ring fls"
  shows "f / fls_X = fls_shift 1 f"
  by    (rule fls_divide_X'[OF inverse_1])

lemma fls_divide_X_power':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / (fls_X ^ n) = fls_shift n f"
proof-
  have "fls_base_factor_to_fps ((fls_X::'a fls) ^ n) = 1" by (rule fls_X_power_base_factor_to_fps)
  with assms have
    "f / (fls_X ^ n) =
      fls_shift n (fls_shift (-fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f)))"
    by (simp add: fls_divide_def fps_divide_1')
  also have "\<dots> = fls_shift n f"
    using fls_conv_base_factor_to_fps_shift_subdegree[of f] by simp
  finally show ?thesis by simp
qed

lemma fls_divide_X_power [simp]:
  fixes f :: "'a::division_ring fls"
  shows "f / (fls_X ^ n) = fls_shift n f"
  by    (rule fls_divide_X_power'[OF inverse_1])

lemma fls_divide_X_inv':
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one,monoid_mult} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / fls_X_inv = fls_shift (-1) f"
proof-
  from assms have
    "f / fls_X_inv =
      fls_shift (-1) (fls_shift (-fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f)))"
    by (simp add: fls_divide_def fps_divide_1' algebra_simps)
  also have "\<dots> = fls_shift (-1) f"
    using fls_conv_base_factor_to_fps_shift_subdegree[of f]
    by simp
  finally show ?thesis by simp
qed

lemma fls_divide_X_inv [simp]:
  fixes f :: "'a::division_ring fls"
  shows "f / fls_X_inv = fls_shift (-1) f"
  by    (rule fls_divide_X_inv'[OF inverse_1])

lemma fls_divide_X_inv_power':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / (fls_X_inv ^ n) = fls_shift (-int n) f"
proof-
  have "fls_base_factor_to_fps ((fls_X_inv::'a fls) ^ n) = 1"
    by (rule fls_X_inv_power_base_factor_to_fps)
  with assms have
    "f / (fls_X_inv ^ n) =
      fls_shift (-int n + -fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f))"
    by (simp add: fls_divide_def fps_divide_1')
  also have
    "\<dots> = fls_shift (-int n) (fls_shift (-fls_subdegree f) (fps_to_fls (fls_base_factor_to_fps f)))"
    by (simp add: add.commute)
  also have "\<dots> = fls_shift (-int n) f"
    using fls_conv_base_factor_to_fps_shift_subdegree[of f] by simp
  finally show ?thesis by simp
qed

lemma fls_divide_X_inv_power [simp]:
  fixes f :: "'a::division_ring fls"
  shows "f / (fls_X_inv ^ n) = fls_shift (-int n) f"
  by    (rule fls_divide_X_inv_power'[OF inverse_1])

lemma fls_divide_X_intpow':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / (fls_X_intpow i) = fls_shift i f"
  using   assms
  by      (simp add: fls_divide_shift_denom_nonzero fls_divide_1')

lemma fls_divide_X_intpow_conv_times':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fls"
  assumes "inverse (1::'a) = 1"
  shows   "f / (fls_X_intpow i) = f * fls_X_intpow (-i)"
  using   assms fls_X_intpow_times_conv_shift(2)[of f "-i"]
  by      (simp add: fls_divide_X_intpow')

lemma fls_divide_X_intpow:
  fixes f :: "'a::division_ring fls"
  shows "f / (fls_X_intpow i) = fls_shift i f"
  by    (rule fls_divide_X_intpow'[OF inverse_1])

lemma fls_divide_X_intpow_conv_times:
  fixes f :: "'a::division_ring fls"
  shows "f / (fls_X_intpow i) = f * fls_X_intpow (-i)"
  by    (rule fls_divide_X_intpow_conv_times'[OF inverse_1])

lemma fls_X_intpow_div_fls_X_intpow_semiring1:
  assumes "inverse (1::'a::{semiring_1,inverse,uminus}) = 1"
  shows   "(fls_X_intpow i :: 'a fls) / fls_X_intpow j = fls_X_intpow (i-j)"
  by      (simp add: assms fls_divide_shift_both_nonzero fls_divide_1')

lemma fls_X_intpow_div_fls_X_intpow:
  "(fls_X_intpow i :: 'a::division_ring fls) / fls_X_intpow j = fls_X_intpow (i-j)"
  by (rule fls_X_intpow_div_fls_X_intpow_semiring1[OF inverse_1])

lemma fls_divide_add:
  fixes   f g h :: "'a::{semiring_0,inverse,uminus} fls"
  shows   "(f + g) / h = f / h + g / h"
  by      (simp add: fls_divide_convert_times_inverse algebra_simps)

lemma fls_divide_diff:
  fixes f g h :: "'a::{ring,inverse} fls"
  shows "(f - g) / h = f / h - g / h"
  by    (simp add: fls_divide_convert_times_inverse algebra_simps)

lemma fls_divide_uminus:
  fixes f g h :: "'a::{ring,inverse} fls"
  shows "(- f) / g = - (f / g)"
  by    (simp add: fls_divide_convert_times_inverse)

lemma fls_divide_uminus':
  fixes f g h :: "'a::division_ring fls"
  shows "f / (- g) = - (f / g)"
  by    (simp add: fls_divide_convert_times_inverse)


subsubsection \<open>Units\<close>

lemma fls_is_left_unit_iff_base_is_left_unit:
  fixes f :: "'a :: ring_1_no_zero_divisors fls"
  shows "(\<exists>g. 1 = f * g) \<longleftrightarrow> (\<exists>k. 1 = f $$ fls_subdegree f * k)"
proof
  assume "\<exists>g. 1 = f * g"
  then obtain g where "1 = f * g" by fast
  hence "1 = (f $$ fls_subdegree f) * (g $$ fls_subdegree g)"
    using fls_subdegree_mult[of f g] fls_times_base[of f g] by fastforce
  thus "\<exists>k. 1 = f $$ fls_subdegree f * k" by fast
next
  assume "\<exists>k. 1 = f $$ fls_subdegree f * k"
  then obtain k where "1 = f $$ fls_subdegree f * k" by fast
  hence "1 = f * fls_right_inverse f k"
    using fls_right_inverse by simp
  thus "\<exists>g. 1 = f * g" by fast
qed

lemma fls_is_right_unit_iff_base_is_right_unit:
  fixes f :: "'a :: ring_1_no_zero_divisors fls"
  shows "(\<exists>g. 1 = g * f) \<longleftrightarrow> (\<exists>k. 1 = k * f $$ fls_subdegree f)"
proof
  assume "\<exists>g. 1 = g * f"
  then obtain g where "1 = g * f" by fast
  hence "1 = (g $$ fls_subdegree g) * (f $$ fls_subdegree f)"
    using fls_subdegree_mult[of g f] fls_times_base[of g f] by fastforce
  thus "\<exists>k. 1 = k * f $$ fls_subdegree f" by fast
next
  assume "\<exists>k. 1 = k * f $$ fls_subdegree f"
  then obtain k where "1 = k * f $$ fls_subdegree f" by fast
  hence "1 = fls_left_inverse f k * f"
    using fls_left_inverse by simp
  thus "\<exists>g. 1 = g * f" by fast
qed

subsection \<open>Composition\<close>

definition fls_compose_fps :: "'a :: field fls \<Rightarrow> 'a fps \<Rightarrow> 'a fls" where
  "fls_compose_fps F G =
     fps_to_fls (fps_compose (fls_base_factor_to_fps F) G) * fps_to_fls G powi fls_subdegree F"

lemma fps_compose_of_nat [simp]: "fps_compose (of_nat n :: 'a :: comm_ring_1 fps) H = of_nat n"
  and fps_compose_of_int [simp]: "fps_compose (of_int i) H = of_int i"
  unfolding fps_of_nat [symmetric] fps_of_int [symmetric] numeral_fps_const
  by (rule fps_const_compose)+

lemmas [simp] = fps_to_fls_of_nat fps_to_fls_of_int

lemma fls_compose_fps_0 [simp]: "fls_compose_fps 0 H = 0"
  and fls_compose_fps_1 [simp]: "fls_compose_fps 1 H = 1"
  and fls_compose_fps_const [simp]: "fls_compose_fps (fls_const c) H = fls_const c"
  and fls_compose_fps_of_nat [simp]: "fls_compose_fps (of_nat n) H = of_nat n"
  and fls_compose_fps_of_int [simp]: "fls_compose_fps (of_int i) H = of_int i"
  and fls_compose_fps_X [simp]: "fls_compose_fps fls_X F = fps_to_fls F"
  by (simp_all add: fls_compose_fps_def)

lemma fls_compose_fps_0_right:
  "fls_compose_fps F 0 = (if 0 \<le> fls_subdegree F then fls_const (F $$ 0) else 0)"
  by (cases "fls_subdegree F = 0") (simp_all add: fls_compose_fps_def)

lemma fls_compose_fps_shift:
  assumes "H \<noteq> 0"
  shows   "fls_compose_fps (fls_shift n F) H = fls_compose_fps F H * fps_to_fls H powi (-n)"
proof (cases "F = 0")
  case False
  thus ?thesis
    using assms by (simp add: fls_compose_fps_def power_int_diff power_int_minus field_simps)
qed auto

lemma fls_compose_fps_to_fls [simp]:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0"
  shows   "fls_compose_fps (fps_to_fls F) G = fps_to_fls (fps_compose F G)"
proof (cases "F = 0")
  case False
  define n where "n = subdegree F"
  define F' where "F' = fps_shift n F"
  have [simp]: "F' \<noteq> 0" "subdegree F' = 0"
    using False by (auto simp: F'_def n_def)
  have F_eq: "F = F' * fps_X ^ n"
    unfolding F'_def n_def using subdegree_decompose by blast
  have "fls_compose_fps (fps_to_fls F) G =
          fps_to_fls (fps_shift n (fls_regpart (fps_to_fls F' * fls_X_intpow (int n))) oo G) * fps_to_fls (G ^ n)"
    unfolding F_eq fls_compose_fps_def
    by (simp add: fls_times_fps_to_fls fls_X_power_conv_shift_1 power_int_add
                  fls_subdegree_fls_to_fps fps_to_fls_power fls_regpart_shift_conv_fps_shift
             flip: fls_times_both_shifted_simp)
  also have "fps_to_fls F' * fls_X_intpow (int n) = fps_to_fls F"
    by (simp add: F_eq fls_times_fps_to_fls fps_to_fls_power fls_X_power_conv_shift_1)
  also have "fps_to_fls (fps_shift n (fls_regpart (fps_to_fls F)) oo G) * fps_to_fls (G ^ n) =
             fps_to_fls ((fps_shift n (fls_regpart (fps_to_fls F)) * fps_X ^ n) oo G)"
    by (simp add: fls_times_fps_to_fls flip: fps_compose_power add: fps_compose_mult_distrib)
  also have "fps_shift n (fls_regpart (fps_to_fls F)) * fps_X ^ n = F"
    by (simp add: F_eq)
  finally show ?thesis .
qed (auto simp: fls_compose_fps_def)

lemma fls_compose_fps_mult:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F * G) H = fls_compose_fps F H * fls_compose_fps G H"
  using assms
proof (cases "F * G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  define n m where "n = fls_subdegree F" "m = fls_subdegree G"
  define F' where "F' = fls_regpart (fls_shift n F)"
  define G' where "G' = fls_regpart (fls_shift m G)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')" and G_eq: "G = fls_shift (-m) (fps_to_fls G')"
    by (simp_all add: F'_def G'_def n_m_def)
  have "fls_compose_fps (F * G) H = fls_compose_fps (fls_shift (-(n + m)) (fps_to_fls (F' * G'))) H"
    by (simp add: fls_times_fps_to_fls F_eq G_eq fls_shifted_times_simps)
  also have "\<dots> = fps_to_fls ((F' oo H) * (G' oo H)) * fps_to_fls H powi (m + n)"
    by (simp add: fls_compose_fps_shift fps_compose_mult_distrib)
  also have "\<dots> = fls_compose_fps F H * fls_compose_fps G H"
    by (simp add: F_eq G_eq fls_compose_fps_shift fls_times_fps_to_fls power_int_add)
  finally show ?thesis .
qed auto

lemma fls_compose_fps_power:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0"
  shows   "fls_compose_fps (F ^ n) G = fls_compose_fps F G ^ n"
  by (induction n) (auto simp: fls_compose_fps_mult)

lemma fls_compose_fps_add:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F + G) H = fls_compose_fps F H + fls_compose_fps G H"
proof (cases "F = 0 \<or> G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  define n where "n = min (fls_subdegree F) (fls_subdegree G)"
  define F' where "F' = fls_regpart (fls_shift n F)"
  define G' where "G' = fls_regpart (fls_shift n G)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')" and G_eq: "G = fls_shift (-n) (fps_to_fls G')"
    unfolding n_def by (simp_all add: F'_def G'_def n_def)
  have "F + G = fls_shift (-n) (fps_to_fls (F' + G'))"
    by (simp add: F_eq G_eq)
  also have "fls_compose_fps \<dots> H = fls_compose_fps (fps_to_fls (F' + G')) H * fps_to_fls H powi n"
    by (subst fls_compose_fps_shift) auto
  also have "\<dots> = fps_to_fls (fps_compose (F' + G') H) * fps_to_fls H powi n"
    by (subst fls_compose_fps_to_fls) auto
  also have "\<dots> = fls_compose_fps F H + fls_compose_fps G H"
    by (simp add: F_eq G_eq fls_compose_fps_shift fps_compose_add_distrib algebra_simps)
  finally show ?thesis .
qed auto

lemma fls_compose_fps_uminus [simp]: "fls_compose_fps (-F) H = -fls_compose_fps F H"
  by (simp add: fls_compose_fps_def fps_compose_uminus)

lemma fls_compose_fps_diff:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F - G) H = fls_compose_fps F H - fls_compose_fps G H"
  using fls_compose_fps_add[of H F "-G"] by simp

lemma fps_compose_eq_0_iff:
  fixes F G :: "'a :: idom fps"
  assumes "fps_nth G 0 = 0"
  shows "fps_compose F G = 0 \<longleftrightarrow> F = 0 \<or> (G = 0 \<and> fps_nth F 0 = 0)"
proof safe
  assume *: "fps_compose F G = 0" "F \<noteq> 0"
  have "fps_nth (fps_compose F G) 0 = fps_nth F 0"
    by simp
  also have "fps_compose F G = 0"
    by (simp add: *)
  finally show "fps_nth F 0 = 0"
    by simp
  show "G = 0"
  proof (rule ccontr)
    assume "G \<noteq> 0"
    hence "subdegree G > 0" using assms
      using subdegree_eq_0_iff by blast
    define N where "N = subdegree F * subdegree G"
    have "fps_nth (fps_compose F G) N = (\<Sum>i = 0..N. fps_nth F i * fps_nth (G ^ i) N)"
      unfolding fps_compose_def by (simp add: N_def)
    also have "\<dots> = (\<Sum>i\<in>{subdegree F}. fps_nth F i * fps_nth (G ^ i) N)"
    proof (intro sum.mono_neutral_right ballI)
      fix i assume i: "i \<in> {0..N} - {subdegree F}"
      show "fps_nth F i * fps_nth (G ^ i) N = 0"
      proof (cases i "subdegree F" rule: linorder_cases)
        assume "i > subdegree F"
        hence "fps_nth (G ^ i) N = 0"
          using i \<open>subdegree G > 0\<close> by (intro fps_pow_nth_below_subdegree) (auto simp: N_def)
        thus ?thesis by simp
      qed (use i in \<open>auto simp: N_def\<close>)
    qed (use \<open>subdegree G > 0\<close> in \<open>auto simp: N_def\<close>)
    also have "\<dots> = fps_nth F (subdegree F) * fps_nth (G ^ subdegree F) N"
      by simp
    also have "\<dots> \<noteq> 0"
      using \<open>G \<noteq> 0\<close> \<open>F \<noteq> 0\<close> by (auto simp: N_def)
    finally show False using * by auto
  qed
qed auto

lemma fls_compose_fps_eq_0_iff:
  assumes "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps F H = 0 \<longleftrightarrow> F = 0"
  using assms fls_base_factor_to_fps_nonzero[of F]
  by (cases "F = 0") (auto simp: fls_compose_fps_def fps_compose_eq_0_iff)

lemma fls_compose_fps_inverse:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (inverse F) H = inverse (fls_compose_fps F H)"
proof (cases "F = 0")
  case False
  have "fls_compose_fps (inverse F) H * fls_compose_fps F H =
        fls_compose_fps (inverse F * F) H"
    by (subst fls_compose_fps_mult) auto
  also have "inverse F * F = 1"
    using False by simp
  finally show ?thesis
    using False by (simp add: field_simps fls_compose_fps_eq_0_iff)
qed auto

lemma fls_compose_fps_divide:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F / G) H = fls_compose_fps F H / fls_compose_fps G H"
  using fls_compose_fps_mult[of H F "inverse G"] fls_compose_fps_inverse[of H G]
  by (simp add: field_simps)

lemma fls_compose_fps_powi:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F powi n) H = fls_compose_fps F H powi n"
  by (simp add: power_int_def fls_compose_fps_power fls_compose_fps_inverse)

lemma fls_compose_fps_assoc:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0" "H \<noteq> 0" "fps_nth H 0 = 0"
  shows "fls_compose_fps (fls_compose_fps F G) H = fls_compose_fps F (fps_compose G H)"
proof (cases "F = 0")
  case [simp]: False
  define n where "n = fls_subdegree F"
  define F' where "F' = fls_regpart (fls_shift n F)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')"
    by (simp add: F'_def n_def)
  show ?thesis
    by (simp add: F_eq fls_compose_fps_shift fls_compose_fps_mult fls_compose_fps_powi
                  fps_compose_eq_0_iff fps_compose_assoc)
qed auto

lemma subdegree_pos_iff: "subdegree F > 0 \<longleftrightarrow> F \<noteq> 0 \<and> fps_nth F 0 = 0"
  using subdegree_eq_0_iff[of F] by auto

lemma fls_X_power_int [simp]: "fls_X powi n = (fls_X_intpow n :: 'a :: division_ring fls)"
  by (auto simp: power_int_def fls_X_power_conv_shift_1 fls_inverse_X fls_inverse_shift
           simp flip: fls_inverse_X_power)

lemma fls_const_power_int: "fls_const (c powi n) = fls_const (c :: 'a :: division_ring) powi n"
  by (auto simp: power_int_def fls_const_power fls_inverse_const)

lemma fls_nth_fls_compose_fps_linear:
  fixes c :: "'a :: field"
  assumes [simp]: "c \<noteq> 0"
  shows "fls_compose_fps F (fps_const c * fps_X) $$ n = F $$ n * c powi n"
proof -
  {
    assume *: "n \<ge> fls_subdegree F"
    hence "c ^ nat (n - fls_subdegree F) = c powi int (nat (n - fls_subdegree F))"
      by (simp add: power_int_def)
    also have "\<dots> * c powi fls_subdegree F = c powi (int (nat (n - fls_subdegree F)) + fls_subdegree F)"
      using * by (subst power_int_add) auto
    also have "\<dots> = c powi n"
      using * by simp
    finally have "c ^ nat (n - fls_subdegree F) * c powi fls_subdegree F = c powi n" .
  }
  thus ?thesis
    by (simp add: fls_compose_fps_def fps_compose_linear fls_times_fps_to_fls power_int_mult_distrib
                  fls_shifted_times_simps
             flip: fls_const_power_int)
qed

lemma fls_const_transfer [transfer_rule]:
  "rel_fun (=) (pcr_fls (=))
     (\<lambda>c n. if n = 0 then c else 0) fls_const"
  by (auto simp: fls_const_def rel_fun_def pcr_fls_def OO_def cr_fls_def)

lemma fls_shift_transfer [transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_fls (=)) (pcr_fls (=)))
     (\<lambda>n f k. f (k+n)) fls_shift"
  by (auto simp: fls_const_def rel_fun_def pcr_fls_def OO_def cr_fls_def)

lift_definition fls_compose_power :: "'a :: zero fls \<Rightarrow> nat \<Rightarrow> 'a fls" is
  "\<lambda>f d n. if d > 0 \<and> int d dvd n then f (n div int d) else 0"
proof -
  fix f :: "int \<Rightarrow> 'a" and d :: nat
  assume *: "eventually (\<lambda>n. f (-int n) = 0) cofinite"
  show "eventually (\<lambda>n. (if d > 0 \<and> int d dvd -int n then f (-int n div int d) else 0) = 0) cofinite"
  proof (cases "d = 0")
    case False
    from * have "eventually (\<lambda>n. f (-int n) = 0) at_top"
      by (simp add: cofinite_eq_sequentially)
    hence "eventually (\<lambda>n. f (-int (n div d)) = 0) at_top"
      by (rule eventually_compose_filterlim[OF _ filterlim_at_top_div_const_nat]) (use False in auto)
    hence "eventually (\<lambda>n. (if d > 0 \<and> int d dvd -int n then f (-int n div int d) else 0) = 0) at_top"
      by eventually_elim (auto simp: zdiv_int dvd_neg_div)
    thus ?thesis
      by (simp add: cofinite_eq_sequentially)
  qed auto
qed

lemma fls_nth_compose_power:
  assumes "d > 0"
  shows   "fls_compose_power f d $$ n = (if int d dvd n then f $$ (n div int d) else 0)"
  by (simp add: assms fls_compose_power.rep_eq)
     

lemma fls_compose_power_0_left [simp]: "fls_compose_power 0 d = 0"
  by transfer auto

lemma fls_compose_power_1_left [simp]: "d > 0 \<Longrightarrow> fls_compose_power 1 d = 1"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_const_left [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_const c) d = fls_const c"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_shift [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_shift n f) d = fls_shift (d * n) (fls_compose_power f d)"
  by transfer (auto simp: fun_eq_iff add_ac mult_ac)

lemma fls_compose_power_X_intpow [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_X_intpow n) d = fls_X_intpow (int d * n)"
  by simp

lemma fls_compose_power_X [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power fls_X d = fls_X_intpow (int d)"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_X_inv [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power fls_X_inv d = fls_X_intpow (-int d)"
  by (simp add: fls_X_inv_conv_shift_1)

lemma fls_compose_power_0_right [simp]: "fls_compose_power f 0 = 0"
  by transfer auto

lemma fls_compose_power_add [simp]:
  "fls_compose_power (f + g) d = fls_compose_power f d + fls_compose_power g d"
  by transfer auto

lemma fls_compose_power_diff [simp]:
  "fls_compose_power (f - g) d = fls_compose_power f d - fls_compose_power g d"
  by transfer auto

lemma fls_compose_power_uminus [simp]:
  "fls_compose_power (-f) d = -fls_compose_power f d"
  by transfer auto

lemma fps_nth_compose_X_power:
  "fps_nth (f oo (fps_X ^ d)) n = (if d dvd n then fps_nth f (n div d) else 0)"
proof -
  have "fps_nth (f oo (fps_X ^ d)) n = (\<Sum>i = 0..n. f $ i * (fps_X ^ (d * i)) $ n)"
    unfolding fps_compose_def by (simp add: power_mult)
  also have "\<dots> = (\<Sum>i\<in>(if d dvd n then {n div d} else {}). f $ i * (fps_X ^ (d * i)) $ n)"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (if d dvd n then fps_nth f (n div d) else 0)"
    by auto
  finally show ?thesis .
qed

lemma fls_compose_power_fps_to_fls:
  assumes "d > 0"
  shows   "fls_compose_power (fps_to_fls f) d = fps_to_fls (fps_compose f (fps_X ^ d))"
  using assms
  by (intro fls_eqI) (auto simp: fls_nth_compose_power fps_nth_compose_X_power
                                 pos_imp_zdiv_neg_iff div_neg_pos_less0 nat_div_distrib
                           simp flip: int_dvd_int_iff)

lemma fls_compose_power_mult [simp]:
  "fls_compose_power (f * g :: 'a :: idom fls) d = fls_compose_power f d * fls_compose_power g d"
proof (cases "d > 0")
  case True
  define n where "n = nat (max 0 (max (- fls_subdegree f) (- fls_subdegree g)))"
  have n_ge: "-fls_subdegree f \<le> int n" "-fls_subdegree g \<le> int n"
    unfolding n_def by auto
  obtain f' where f': "f = fls_shift n (fps_to_fls f')"
    using fls_as_fps[OF n_ge(1)] by (auto simp: n_def)
  obtain g' where g': "g = fls_shift n (fps_to_fls g')"
    using fls_as_fps[OF n_ge(2)] by (auto simp: n_def)
  show ?thesis using \<open>d > 0\<close>
    by (simp add: f' g' fls_shifted_times_simps mult_ac fls_compose_power_fps_to_fls
                  fps_compose_mult_distrib flip: fls_times_fps_to_fls)
qed auto

lemma fls_compose_power_power [simp]:
  assumes "d > 0 \<or> n > 0"
  shows   "fls_compose_power (f ^ n :: 'a :: idom fls) d = fls_compose_power f d ^ n"
proof (cases "d > 0")
  case True
  thus ?thesis by (induction n) auto
qed (use assms in auto)

lemma fls_nth_compose_power' [simp]:
  "d = 0 \<or> \<not>d dvd n \<Longrightarrow> fls_compose_power f d $$ int n = 0"
  "d dvd n \<Longrightarrow> d > 0 \<Longrightarrow> fls_compose_power f d $$ int n = f $$ int (n div d)"
  by (transfer; force; fail)+

subsection \<open>Formal differentiation and integration\<close>

subsubsection \<open>Derivative\<close>

definition "fls_deriv f = Abs_fls (\<lambda>n. of_int (n+1) * f$$(n+1))"

lemma fls_deriv_nth[simp]: "fls_deriv f $$ n = of_int (n+1) * f$$(n+1)"
proof-
  obtain N where "\<forall>n<N. f$$n = 0" by (elim fls_nth_vanishes_belowE)
  hence "\<forall>n<N-1. of_int (n+1) * f$$(n+1) = 0" by auto
  thus ?thesis using nth_Abs_fls_lower_bound unfolding fls_deriv_def by simp
qed

lemma fls_deriv_residue: "fls_deriv f $$ -1 = 0"
  by simp

lemma fls_deriv_const[simp]: "fls_deriv (fls_const x) = 0"
proof (intro fls_eqI)
  fix n show "fls_deriv (fls_const x) $$ n = 0$$n"
    by (cases "n+1=0") auto
qed

lemma fls_deriv_of_nat[simp]: "fls_deriv (of_nat n) = 0"
  by (simp add: fls_of_nat)

lemma fls_deriv_of_int[simp]: "fls_deriv (of_int i) = 0"
  by (simp add: fls_of_int)

lemma fls_deriv_zero[simp]: "fls_deriv 0 = 0"
  using fls_deriv_const[of 0] by simp

lemma fls_deriv_one[simp]: "fls_deriv 1 = 0"
  using fls_deriv_const[of 1] by simp

lemma fls_deriv_numeral [simp]: "fls_deriv (numeral n) = 0"
  by (metis fls_deriv_of_int of_int_numeral)

lemma fls_deriv_subdegree':
  assumes "of_int (fls_subdegree f) * f $$ fls_subdegree f \<noteq> 0"
  shows   "fls_subdegree (fls_deriv f) = fls_subdegree f - 1"
  by      (auto intro: fls_subdegree_eqI simp: assms)

lemma fls_deriv_subdegree0:
  assumes "fls_subdegree f = 0"
  shows   "fls_subdegree (fls_deriv f) \<ge> 0"
proof (cases "fls_deriv f = 0")
  case False
  show ?thesis
  proof (intro fls_subdegree_geI, rule False)
    fix k :: int assume "k < 0"
    with assms show "fls_deriv f $$ k = 0" by (cases "k=-1") auto
  qed
qed simp

lemma fls_subdegree_deriv':
  fixes   f :: "'a::ring_1_no_zero_divisors fls"
  assumes "(of_int (fls_subdegree f) :: 'a) \<noteq> 0"
  shows   "fls_subdegree (fls_deriv f) = fls_subdegree f - 1"
  using   assms nth_fls_subdegree_zero_iff[of f]
  by      (auto intro: fls_deriv_subdegree')

lemma fls_subdegree_deriv:
  fixes   f :: "'a::{ring_1_no_zero_divisors,ring_char_0} fls"
  assumes "fls_subdegree f \<noteq> 0"
  shows   "fls_subdegree (fls_deriv f) = fls_subdegree f - 1"
  by      (auto intro: fls_subdegree_deriv' simp: assms)

text \<open>
  Shifting is like multiplying by a power of the implied variable, and so satisfies a product-like
  rule.
\<close>

lemma fls_deriv_shift:
  "fls_deriv (fls_shift n f) = of_int (-n) * fls_shift (n+1) f + fls_shift n (fls_deriv f)"
  by (intro fls_eqI) (simp flip: fls_shift_fls_shift add: algebra_simps)

lemma fls_deriv_X [simp]: "fls_deriv fls_X = 1"
  by (intro fls_eqI) simp

lemma fls_deriv_X_inv [simp]: "fls_deriv fls_X_inv = - (fls_X_inv\<^sup>2)"
proof-
  have "fls_deriv fls_X_inv = - (fls_shift 2 1)"
    by (simp add: fls_X_inv_conv_shift_1 fls_deriv_shift)
  thus ?thesis by (simp add: fls_X_inv_power_conv_shift_1)
qed

lemma fls_deriv_delta:
  "fls_deriv (Abs_fls (\<lambda>n. if n=m then c else 0)) =
    Abs_fls (\<lambda>n. if n=m-1 then of_int m * c else 0)"
proof-
  have
    "fls_deriv (Abs_fls (\<lambda>n. if n=m then c else 0)) = fls_shift (1-m) (fls_const (of_int m * c))"
    using fls_deriv_shift[of "-m" "fls_const c"]
    by    (simp
            add: fls_shift_const fls_of_int fls_shifted_times_simps(1)[symmetric]
            fls_const_mult_const[symmetric]
            del: fls_const_mult_const
          )
  thus ?thesis by (simp add: fls_shift_const)
qed

lemma fls_deriv_base_factor:
  "fls_deriv (fls_base_factor f) =
    of_int (-fls_subdegree f) * fls_shift (fls_subdegree f + 1) f +
    fls_shift (fls_subdegree f) (fls_deriv f)"
  by (simp add: fls_deriv_shift)

lemma fls_regpart_deriv: "fls_regpart (fls_deriv f) = fps_deriv (fls_regpart f)"
proof (intro fps_ext)
  fix n
  have  1: "(of_nat n :: 'a) + 1 = of_nat (n+1)"
  and   2: "int n + 1 = int (n + 1)"
    by  auto
  show "fls_regpart (fls_deriv f) $ n = fps_deriv (fls_regpart f) $ n" by (simp add: 1 2)
qed

lemma fls_prpart_deriv:
  fixes f :: "'a :: {comm_ring_1,ring_no_zero_divisors} fls"
  \<comment> \<open>Commutivity and no zero divisors are required by the definition of @{const pderiv}.\<close>
  shows "fls_prpart (fls_deriv f) = - pCons 0 (pCons 0 (pderiv (fls_prpart f)))"
proof (intro poly_eqI)
  fix n
  show
    "coeff (fls_prpart (fls_deriv f)) n =
      coeff (- pCons 0 (pCons 0 (pderiv (fls_prpart f)))) n"
  proof (cases n)
    case (Suc m)
    hence n: "n = Suc m" by fast
    show ?thesis
    proof (cases m)
      case (Suc k)
      with n have
        "coeff (- pCons 0 (pCons 0 (pderiv (fls_prpart f)))) n =
          - coeff (pderiv (fls_prpart f)) k"
        by (simp flip: coeff_minus)
      with Suc n show ?thesis by (simp add: coeff_pderiv algebra_simps)
    qed (simp add: n)
  qed simp
qed

lemma pderiv_fls_prpart:
  "pderiv (fls_prpart f) = - poly_shift 2 (fls_prpart (fls_deriv f))"
  by (intro poly_eqI) (simp add: coeff_pderiv coeff_poly_shift algebra_simps)

lemma fls_deriv_fps_to_fls: "fls_deriv (fps_to_fls f) = fps_to_fls (fps_deriv f)"
proof (intro fls_eqI)
  fix n
  show "fls_deriv (fps_to_fls f) $$ n  = fps_to_fls (fps_deriv f) $$ n"
  proof (cases "n\<ge>0")
    case True
    from True have 1: "nat (n + 1) = nat n + 1" by simp
    from True have 2: "(of_int (n + 1) :: 'a) = of_nat (nat (n+1))" by simp
    from True show ?thesis using arg_cong[OF 2, of "\<lambda>x. x * f $ (nat n+1)"] by (simp add: 1)
  next
    case False thus ?thesis by (cases "n=-1") auto
  qed
qed


subsubsection \<open>Algebraic rules of the derivative\<close>

lemma fls_deriv_add [simp]: "fls_deriv (f+g) = fls_deriv f + fls_deriv g"
  by (auto intro: fls_eqI simp: algebra_simps)

lemma fls_deriv_sub [simp]: "fls_deriv (f-g) = fls_deriv f - fls_deriv g"
  by (auto intro: fls_eqI simp: algebra_simps)

lemma fls_deriv_neg [simp]: "fls_deriv (-f) = - fls_deriv f"
  using fls_deriv_sub[of 0 f] by simp

lemma fls_deriv_mult [simp]:
  "fls_deriv (f*g) = f * fls_deriv g + fls_deriv f * g"
proof-
  define df dg :: int
    where "df \<equiv> fls_subdegree f"
    and   "dg \<equiv> fls_subdegree g"
  define uf ug :: "'a fls"
    where "uf \<equiv> fls_base_factor f"
    and   "ug \<equiv> fls_base_factor g"
  have
    "f * fls_deriv g =
      of_int dg * fls_shift (1 - dg) (f * ug) + fls_shift (-dg) (f * fls_deriv ug)"
    "fls_deriv f * g =
      of_int df * fls_shift (1 - df) (uf * g) + fls_shift (-df) (fls_deriv uf * g)"
    using fls_deriv_shift[of "-df" uf] fls_deriv_shift[of "-dg" ug]
          mult_of_int_commute[of dg f]
          mult.assoc[of "of_int dg" f]
          fls_shifted_times_simps(1)[of f "1 - dg" ug]
          fls_shifted_times_simps(1)[of f "-dg" "fls_deriv ug"]
          fls_shifted_times_simps(2)[of "1 - df" uf g]
          fls_shifted_times_simps(2)[of "-df" "fls_deriv uf" g]
    by (auto simp add: algebra_simps df_def dg_def uf_def ug_def)
  moreover have
    "fls_deriv (f*g) =
      ( of_int dg * fls_shift (1 - dg) (f * ug) + fls_shift (-dg) (f * fls_deriv ug) ) +
      ( of_int df * fls_shift (1 - df) (uf * g) + fls_shift (-df) (fls_deriv uf * g) )
    "
    using fls_deriv_shift[of
            "- (df + dg)" "fps_to_fls (fls_base_factor_to_fps f * fls_base_factor_to_fps g)"
          ]
          fls_deriv_fps_to_fls[of "fls_base_factor_to_fps f * fls_base_factor_to_fps g"]
          fps_deriv_mult[of "fls_base_factor_to_fps f" "fls_base_factor_to_fps g"]
          distrib_right[of
            "of_int df" "of_int dg"
            "fls_shift (1 - (df + dg)) (
              fps_to_fls (fls_base_factor_to_fps f * fls_base_factor_to_fps g)
            )"
          ]
          fls_times_conv_fps_times[of uf ug]
          fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of g]
          fls_regpart_deriv[of ug]
          fls_times_conv_fps_times[of uf "fls_deriv ug"]
          fls_deriv_subdegree0[of ug]
          fls_regpart_deriv[of uf]
          fls_times_conv_fps_times[of "fls_deriv uf" ug]
          fls_deriv_subdegree0[of uf]
          fls_shifted_times_simps(1)[of uf "-dg" ug]
          fls_shifted_times_simps(1)[of "fls_deriv uf" "-dg" ug]
          fls_shifted_times_simps(2)[of "-df" uf ug]
          fls_shifted_times_simps(2)[of "-df" uf "fls_deriv ug"]
    by (simp add: fls_times_def algebra_simps df_def dg_def uf_def ug_def)
  ultimately show ?thesis by simp
qed

lemma fls_deriv_mult_const_left:
  "fls_deriv (fls_const c * f) = fls_const c * fls_deriv f"
  by simp

lemma fls_deriv_linear:
  "fls_deriv (fls_const a * f + fls_const b * g) =
    fls_const a * fls_deriv f + fls_const b * fls_deriv g"
  by simp

lemma fls_deriv_mult_const_right:
  "fls_deriv (f * fls_const c) = fls_deriv f * fls_const c"
  by simp

lemma fls_deriv_linear2:
  "fls_deriv (f * fls_const a + g * fls_const b) =
    fls_deriv f * fls_const a + fls_deriv g * fls_const b"
  by simp

lemma fls_deriv_sum:
  "fls_deriv (sum f S) = sum (\<lambda>i. fls_deriv (f i)) S"
proof (cases "finite S")
  case True show ?thesis
    by (induct rule: finite_induct [OF True]) simp_all
qed simp

lemma fls_deriv_power:
  fixes f :: "'a::comm_ring_1 fls"
  shows "fls_deriv (f^n) = of_nat n * f^(n-1) * fls_deriv f"
proof (cases n)
  case (Suc m)
  have "fls_deriv (f^Suc m) = of_nat (Suc m) * f^m * fls_deriv f"
    by (induct m) (simp_all add: algebra_simps)
  with Suc show ?thesis by simp
qed simp

lemma fls_deriv_X_power:
  "fls_deriv (fls_X ^ n) = of_nat n * fls_X ^ (n-1)"
proof (cases n)
  case (Suc m)
  have "fls_deriv (fls_X^Suc m) = of_nat (Suc m) * fls_X^m"
    by (induct m) (simp_all add: mult_of_nat_commute algebra_simps)
  with Suc show ?thesis by simp
qed simp

lemma fls_deriv_X_inv_power:
  "fls_deriv (fls_X_inv ^ n) = - of_nat n * fls_X_inv ^ (Suc n)"
proof (cases n)
  case (Suc m)
  define iX :: "'a fls" where "iX \<equiv> fls_X_inv"
  have "fls_deriv (iX ^ Suc m) = - of_nat (Suc m) * iX ^ (Suc (Suc m))"
  proof (induct m)
    case (Suc m)
    have "- of_nat (Suc m + 1) * iX ^ Suc (Suc (Suc m)) =
            iX * (-of_nat (Suc m) * iX ^ Suc (Suc m)) +
                  - (iX ^ 2 * iX ^ Suc m)"
      using distrib_right[of "-of_nat (Suc m)" "-(1::'a fls)" "fls_X_inv ^ Suc (Suc (Suc m))"]
      by (simp add: algebra_simps mult_of_nat_commute power2_eq_square Suc iX_def)
    thus ?case using Suc by (simp add: iX_def)
  qed (simp add: numeral_2_eq_2 iX_def)
  with Suc show ?thesis by (simp add: iX_def)
qed simp

lemma fls_deriv_X_intpow:
  "fls_deriv (fls_X_intpow i) = of_int i * fls_X_intpow (i-1)"
  by (simp add: fls_deriv_shift)

lemma fls_deriv_lr_inverse:
  assumes "x * f $$ fls_subdegree f = 1" "f $$ fls_subdegree f * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fls_deriv (fls_left_inverse f x) =
            - fls_left_inverse f x * fls_deriv f * fls_left_inverse f x"
  and     "fls_deriv (fls_right_inverse f y) =
            - fls_right_inverse f y * fls_deriv f * fls_right_inverse f y"
proof-

  define L where "L \<equiv> fls_left_inverse f x"
  hence "fls_deriv (L * f) = 0" using fls_left_inverse[OF assms(1)] by simp
  with assms show "fls_deriv L = - L * fls_deriv f * L"
    using fls_right_inverse'[OF assms]
    by    (simp add: minus_unique mult.assoc L_def)

  define R where "R \<equiv> fls_right_inverse f y"
  hence "fls_deriv (f * R) = 0" using fls_right_inverse[OF assms(2)] by simp
  hence 1: "f * fls_deriv R + fls_deriv f * R = 0" by simp
  have "R * f * fls_deriv R = - R * fls_deriv f * R"
    using iffD2[OF eq_neg_iff_add_eq_0, OF 1] by (simp add: mult.assoc)
  thus "fls_deriv R = - R * fls_deriv f * R"
    using fls_left_inverse'[OF assms] by (simp add: R_def)

qed

lemma fls_deriv_lr_inverse_comm:
  fixes   x y :: "'a::comm_ring_1"
  assumes "x * f $$ fls_subdegree f = 1"
  shows   "fls_deriv (fls_left_inverse f x) = - fls_deriv f * (fls_left_inverse f x)\<^sup>2"
  and     "fls_deriv (fls_right_inverse f x) = - fls_deriv f * (fls_right_inverse f x)\<^sup>2"
  using   assms fls_deriv_lr_inverse[of x f x]
  by      (simp_all add: mult.commute power2_eq_square)

lemma fls_inverse_deriv_divring:
  fixes a :: "'a::division_ring fls"
  shows "fls_deriv (inverse a) = - inverse a * fls_deriv a * inverse a"
proof (cases "a=0")
  case False thus ?thesis
    using fls_deriv_lr_inverse(2)[of
            "inverse (a $$ fls_subdegree a)" a "inverse (a $$ fls_subdegree a)"
          ]
    by    (auto simp add: fls_inverse_def')
qed simp

lemma fls_inverse_deriv:
  fixes a :: "'a::field fls"
  shows "fls_deriv (inverse a) = - fls_deriv a * (inverse a)\<^sup>2"
  by    (simp add: fls_inverse_deriv_divring power2_eq_square)

lemma fls_inverse_deriv':
  fixes a :: "'a::field fls"
  shows "fls_deriv (inverse a) = - fls_deriv a / a\<^sup>2"
  using fls_inverse_deriv[of a]
  by    (simp add: field_simps)


subsubsection \<open>Equality of derivatives\<close>

lemma fls_deriv_eq_0_iff:
  "fls_deriv f = 0 \<longleftrightarrow> f = fls_const (f$$0 :: 'a::{ring_1_no_zero_divisors,ring_char_0})"
proof
  assume f: "fls_deriv f = 0"
  show "f = fls_const (f$$0)"
  proof (intro fls_eqI)
    fix n
    from f have "of_int n * f$$ n = 0" using fls_deriv_nth[of f "n-1"] by simp
    thus "f$$n = fls_const (f$$0) $$ n" by (cases "n=0") auto
  qed
next
  show "f = fls_const (f$$0) \<Longrightarrow> fls_deriv f = 0" using fls_deriv_const[of "f$$0"] by simp
qed

lemma fls_deriv_eq_iff:
  fixes f g :: "'a::{ring_1_no_zero_divisors,ring_char_0} fls"
  shows "fls_deriv f = fls_deriv g \<longleftrightarrow> (f = fls_const(f$$0 - g$$0) + g)"
proof -
  have "fls_deriv f = fls_deriv g \<longleftrightarrow> fls_deriv (f - g) = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> f - g = fls_const ((f - g) $$ 0)"
    unfolding fls_deriv_eq_0_iff ..
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma fls_deriv_eq_iff_ex:
  fixes f g :: "'a::{ring_1_no_zero_divisors,ring_char_0} fls"
  shows "(fls_deriv f = fls_deriv g) \<longleftrightarrow> (\<exists>c. f = fls_const c + g)"
  by    (auto simp: fls_deriv_eq_iff)


subsubsection \<open>Residues\<close>

definition fls_residue_def[simp]: "fls_residue f \<equiv> f $$ -1"

lemma fls_residue_deriv: "fls_residue (fls_deriv f) = 0"
  by simp

lemma fls_residue_add: "fls_residue (f+g) = fls_residue f + fls_residue g"
  by simp

lemma fls_residue_times_deriv:
  "fls_residue (fls_deriv f * g) = - fls_residue (f * fls_deriv g)"
  using fls_residue_deriv[of "f*g"] minus_unique[of "fls_residue (f * fls_deriv g)"]
  by    simp

lemma fls_residue_power_series: "fls_subdegree f \<ge> 0 \<Longrightarrow> fls_residue f = 0"
  by simp

lemma fls_residue_fls_X_intpow:
  "fls_residue (fls_X_intpow i) = (if i=-1 then 1 else 0)"
  by simp

lemma fls_residue_shift_nth:
  fixes f :: "'a::semiring_1 fls"
  shows "f$$n = fls_residue (fls_X_intpow (-n-1) * f)"
  by    (simp add: fls_shifted_times_transfer)

lemma fls_residue_fls_const_times:
  fixes f :: "'a::{comm_monoid_add, mult_zero} fls"
  shows "fls_residue (fls_const c * f) = c * fls_residue f"
  and   "fls_residue (f * fls_const c) = fls_residue f * c"
  by    simp_all

lemma fls_residue_of_int_times:
  fixes f :: "'a::ring_1 fls"
  shows "fls_residue (of_int i * f) = of_int i * fls_residue f"
  and   "fls_residue (f * of_int i) = fls_residue f * of_int i"
  by    (simp_all add: fls_residue_fls_const_times fls_of_int)

lemma fls_residue_deriv_times_lr_inverse_eq_subdegree:
  fixes   f g :: "'a::ring_1 fls"
  assumes "y * (f $$ fls_subdegree f) = 1" "(f $$ fls_subdegree f) * y = 1"
  shows   "fls_residue (fls_deriv f * fls_right_inverse f y)  = of_int (fls_subdegree f)"
  and     "fls_residue (fls_deriv f * fls_left_inverse f y)   = of_int (fls_subdegree f)"
  and     "fls_residue (fls_left_inverse f y * fls_deriv f)   = of_int (fls_subdegree f)"
  and     "fls_residue (fls_right_inverse f y * fls_deriv f)  = of_int (fls_subdegree f)"
proof-
  define df :: int where "df \<equiv> fls_subdegree f"
  define B X :: "'a fls"
    where "B \<equiv> fls_base_factor f"
    and   "X \<equiv> (fls_X_intpow df :: 'a fls)"
  define D L R :: "'a fls"
    where "D \<equiv> fls_deriv B"
    and   "L \<equiv> fls_left_inverse B y"
    and   "R \<equiv> fls_right_inverse B y"
  have intpow_diff: "fls_X_intpow (df - 1) = X * fls_X_inv"
    using fls_X_intpow_diff_conv_times[of df 1] by (simp add: X_def fls_X_inv_conv_shift_1)
 

  show "fls_residue (fls_deriv f * fls_right_inverse f y) = of_int df"
  proof-
    have subdegree_DR: "fls_subdegree (D * R) \<ge> 0"
      using fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of "fls_right_inverse f y"]
            assms(1) fls_right_inverse_base_factor[of y f] fls_mult_subdegree_ge_0[of D R]
      by    (force simp: fls_deriv_subdegree0 D_def R_def B_def)
    have decomp: "f = X * B"
      unfolding X_def B_def df_def by (rule fls_base_factor_X_power_decompose(2)[of f])
    hence "fls_deriv f = X * D + of_int df * X * fls_X_inv * B"
      using intpow_diff fls_deriv_mult[of X B]
      by    (simp add: fls_deriv_X_intpow X_def B_def D_def mult.assoc)
    moreover from assms have "fls_right_inverse (X * B) y = R * fls_right_inverse X 1"
      using fls_base_factor_base[of f] fls_lr_inverse_mult_ring1(2)[of 1 X]
      by    (simp add: X_def B_def R_def)
    ultimately have
      "fls_deriv f * fls_right_inverse f y =
        (D + of_int df * fls_X_inv * B) * R * (X * fls_right_inverse X 1)"
      by (simp add: decomp algebra_simps X_def fls_X_intpow_times_comm)
    also have "\<dots> = D * R + of_int df * fls_X_inv"
      using fls_right_inverse[of X 1]
            assms fls_base_factor_base[of f] fls_right_inverse[of B y]
      by    (simp add: X_def distrib_right mult.assoc B_def R_def)
    finally show ?thesis using subdegree_DR by simp
  qed

  with assms show "fls_residue (fls_deriv f * fls_left_inverse f y) = of_int df"
    using fls_left_inverse_eq_fls_right_inverse[of y f] by simp

  show "fls_residue (fls_left_inverse f y * fls_deriv f) = of_int df"
  proof-
    have subdegree_LD: "fls_subdegree (L * D) \<ge> 0"
      using fls_base_factor_subdegree[of f] fls_base_factor_subdegree[of "fls_left_inverse f y"]
            assms(1) fls_left_inverse_base_factor[of y f] fls_mult_subdegree_ge_0[of L D]
      by    (force simp: fls_deriv_subdegree0 D_def L_def B_def)
    have decomp: "f = B * X"
      unfolding X_def B_def df_def by (rule fls_base_factor_X_power_decompose(1)[of f])
    hence "fls_deriv f = D * X + B * of_int df * X * fls_X_inv"
      using intpow_diff fls_deriv_mult[of B X]
      by    (simp add: fls_deriv_X_intpow X_def D_def B_def mult.assoc)
    moreover from assms have "fls_left_inverse (B * X) y = fls_left_inverse X 1 * L"
      using fls_base_factor_base[of f] fls_lr_inverse_mult_ring1(1)[of _ _ 1 X]
      by    (simp add: X_def B_def L_def)
    ultimately have
      "fls_left_inverse f y * fls_deriv f =
        fls_left_inverse X 1 * X * L * (D + B * (of_int df * fls_X_inv))"
      by (simp add: decomp algebra_simps X_def fls_X_intpow_times_comm)
    also have "\<dots> = L * D + of_int df * fls_X_inv"
      using assms fls_left_inverse[of 1 X] fls_base_factor_base[of f] fls_left_inverse[of y B]
       by   (simp add: X_def distrib_left mult.assoc[symmetric] L_def B_def)
    finally show ?thesis using subdegree_LD by simp
  qed

  with assms show "fls_residue (fls_right_inverse f y * fls_deriv f) = of_int df"
    using fls_left_inverse_eq_fls_right_inverse[of y f] by simp

qed

lemma fls_residue_deriv_times_inverse_eq_subdegree:
  fixes f g :: "'a::division_ring fls"
  shows "fls_residue (fls_deriv f * inverse f) = of_int (fls_subdegree f)"
  and   "fls_residue (inverse f * fls_deriv f) = of_int (fls_subdegree f)"
proof-
  show "fls_residue (fls_deriv f * inverse f) = of_int (fls_subdegree f)"
    using fls_residue_deriv_times_lr_inverse_eq_subdegree(1)[of _ f]
    by    (cases "f=0") (auto simp: fls_inverse_def')
  show "fls_residue (inverse f * fls_deriv f) = of_int (fls_subdegree f)"
    using fls_residue_deriv_times_lr_inverse_eq_subdegree(4)[of _ f]
    by    (cases "f=0") (auto simp: fls_inverse_def')
qed


subsubsection \<open>Integral definition and basic properties\<close>

definition fls_integral :: "'a::{ring_1,inverse} fls \<Rightarrow> 'a fls"
  where "fls_integral a = Abs_fls (\<lambda>n. if n=0 then 0 else inverse (of_int n) * a$$(n - 1))"

lemma fls_integral_nth [simp]:
  "fls_integral a $$ n = (if n=0 then 0 else inverse (of_int n) * a$$(n-1))"
proof-
  define F where "F \<equiv> (\<lambda>n. if n=0 then 0 else inverse (of_int n) * a$$(n - 1))"
  obtain N where "\<forall>n<N. a$$n = 0" by (elim fls_nth_vanishes_belowE)
  hence "\<forall>n<N. F n = 0" by (auto simp add: F_def)
  thus ?thesis using nth_Abs_fls_lower_bound[of N F] unfolding fls_integral_def F_def by simp
qed

lemma fls_integral_conv_fps_zeroth_integral:
  assumes "fls_subdegree a \<ge> 0"
  shows   "fls_integral a = fps_to_fls (fps_integral0 (fls_regpart a))"
proof (rule fls_eqI)
  fix n
  show "fls_integral a $$ n = fps_to_fls (fps_integral0 (fls_regpart a)) $$ n"
  proof (cases "n>0")
    case False with assms show ?thesis by simp
  next
    case True
    hence "int ((nat n) - 1) = n - 1" by simp
    with True show ?thesis by (simp add: fps_integral_def)
  qed
qed

lemma fls_integral_zero [simp]: "fls_integral 0 = 0"
  by (intro fls_eqI) simp

lemma fls_integral_const':
  fixes   x :: "'a::{ring_1,inverse}"
  assumes "inverse (1::'a) = 1"
  shows   "fls_integral (fls_const x) = fls_const x * fls_X"
  by      (intro fls_eqI) (simp add: assms)

lemma fls_integral_const:
  fixes x :: "'a::division_ring"
  shows "fls_integral (fls_const x) = fls_const x * fls_X"
  by    (rule fls_integral_const'[OF inverse_1])

lemma fls_integral_of_nat':
  assumes "inverse (1::'a::{ring_1,inverse}) = 1"
  shows   "fls_integral (of_nat n :: 'a fls) = of_nat n * fls_X"
  by      (simp add: assms fls_integral_const' fls_of_nat)

lemma fls_integral_of_nat:
  "fls_integral (of_nat n :: 'a::division_ring fls) = of_nat n * fls_X"
  by (rule fls_integral_of_nat'[OF inverse_1])

lemma fls_integral_of_int':
  assumes "inverse (1::'a::{ring_1,inverse}) = 1"
  shows   "fls_integral (of_int i :: 'a fls) = of_int i * fls_X"
  by      (simp add: assms fls_integral_const' fls_of_int)

lemma fls_integral_of_int:
  "fls_integral (of_int i :: 'a::division_ring fls) = of_int i * fls_X"
  by (rule fls_integral_of_int'[OF inverse_1])

lemma fls_integral_one':
  assumes "inverse (1::'a::{ring_1,inverse}) = 1"
  shows   "fls_integral (1::'a fls) = fls_X"
  using   fls_integral_const'[of 1]
  by      (force simp: assms)

lemma fls_integral_one: "fls_integral (1::'a::division_ring fls) = fls_X"
  by (rule fls_integral_one'[OF inverse_1])

lemma fls_subdegree_integral_ge:
  "fls_integral f \<noteq> 0 \<Longrightarrow> fls_subdegree (fls_integral f) \<ge> fls_subdegree f + 1"
  by (intro fls_subdegree_geI) simp_all

lemma fls_subdegree_integral:
  fixes   f :: "'a::{division_ring,ring_char_0} fls"
  assumes "f \<noteq> 0" "fls_subdegree f \<noteq> -1"
  shows   "fls_subdegree (fls_integral f) = fls_subdegree f + 1"
  using   assms of_int_0_eq_iff[of "fls_subdegree f + 1"] fls_subdegree_integral_ge
  by      (intro fls_subdegree_eqI) simp_all

lemma fls_integral_X [simp]:
  "fls_integral (fls_X::'a::{ring_1,inverse} fls) =
    fls_const (inverse (of_int 2)) * fls_X\<^sup>2"
proof (intro fls_eqI)
  fix n
  show "fls_integral (fls_X::'a fls) $$ n = (fls_const (inverse (of_int 2)) * fls_X\<^sup>2) $$ n"
    using arg_cong[OF fls_X_power_nth, of "\<lambda>x. inverse (of_int 2) * x", of 2 n, symmetric]
    by    (auto simp add: )
qed

lemma fls_integral_X_power:
  "fls_integral (fls_X ^ n ::'a :: {ring_1,inverse} fls) =
    fls_const (inverse (of_nat (Suc n))) * fls_X ^ Suc n"
proof (intro fls_eqI)
  fix k
  have "(fls_X :: 'a fls) ^ Suc n $$ k = (if k=Suc n then 1 else 0)"
    by (rule fls_X_power_nth)
  thus 
    "fls_integral ((fls_X::'a fls) ^ n) $$ k =
      (fls_const (inverse (of_nat (Suc n))) * (fls_X::'a fls) ^ Suc n) $$ k"
    by simp
qed

lemma fls_integral_X_power_char0:
  "fls_integral (fls_X ^ n :: 'a :: {ring_char_0,inverse} fls) =
    inverse (of_nat (Suc n)) * fls_X ^ Suc n"
proof -
  have "(of_nat (Suc n) :: 'a) \<noteq> 0" by (rule of_nat_neq_0)
  hence "fls_const (inverse (of_nat (Suc n) :: 'a)) = inverse (fls_const (of_nat (Suc n)))"
    by (simp add: fls_inverse_const)
  moreover have
    "fls_integral ((fls_X::'a fls) ^ n) = fls_const (inverse (of_nat (Suc n))) * fls_X ^ Suc n"
    by (rule fls_integral_X_power)
  ultimately show ?thesis by (simp add: fls_of_nat)
qed

lemma fls_integral_X_inv [simp]: "fls_integral (fls_X_inv::'a::{ring_1,inverse} fls) = 0"
  by (intro fls_eqI) simp

lemma fls_integral_X_inv_power:
  assumes "n \<ge> 2"
  shows
    "fls_integral (fls_X_inv ^ n :: 'a :: {ring_1,inverse} fls) =
      fls_const (inverse (of_int (1 - int n))) * fls_X_inv ^ (n-1)"
proof (rule fls_eqI)
  fix k show
    "fls_integral (fls_X_inv ^ n :: 'a fls) $$ k=
      (fls_const (inverse (of_int (1 - int n))) * fls_X_inv ^ (n-1)) $$ k"
  proof (cases "k=0")
    case True with assms show ?thesis by simp
  next
    case False
    from assms have "int (n-1) = int n - 1" by simp
    hence
      "(fls_const (inverse (of_int (1 - int n))) * (fls_X_inv:: 'a fls) ^ (n-1)) $$ k =
      (if k = 1 - int n then inverse (of_int k) else 0)"
      by (simp add: fls_X_inv_power_times_conv_shift(2))
    with False show ?thesis by (simp add: algebra_simps)
  qed
qed

lemma fls_integral_X_inv_power_char0:
  assumes "n \<ge> 2"
  shows
    "fls_integral (fls_X_inv ^ n :: 'a :: {ring_char_0,inverse} fls) =
      inverse (of_int (1 - int n)) * fls_X_inv ^ (n-1)"
proof-
  from assms have "(of_int (1 - int n) :: 'a) \<noteq> 0" by simp
  hence
    "fls_const (inverse (of_int (1 - int n) :: 'a)) = inverse (fls_const (of_int (1 - int n)))"
    by (simp add: fls_inverse_const)
  moreover have
    "fls_integral (fls_X_inv ^ n :: 'a fls) =
      fls_const (inverse (of_int (1 - int n))) * fls_X_inv ^ (n-1)"
    using assms by (rule fls_integral_X_inv_power)
  ultimately show ?thesis by (simp add: fls_of_int)
qed

lemma fls_integral_X_inv_power':
  assumes "n \<ge> 1"
  shows
    "fls_integral (fls_X_inv ^ n :: 'a :: division_ring fls) =
      - fls_const (inverse (of_nat (n-1))) * fls_X_inv ^ (n-1)"
proof (cases "n = 1")
  case False
  with assms have n: "n \<ge> 2" by simp
  hence
    "fls_integral (fls_X_inv ^ n :: 'a fls) =
      fls_const (inverse (- of_nat (nat (int n - 1)))) * fls_X_inv ^ (n-1)"
    by (simp add: fls_integral_X_inv_power)
  moreover from n have "nat (int n - 1) = n - 1" by simp
  ultimately show ?thesis
    using inverse_minus_eq[of "of_nat (n-1) :: 'a"] by simp
qed simp

lemma fls_integral_X_inv_power_char0':
  assumes "n \<ge> 1"
  shows
    "fls_integral (fls_X_inv ^ n :: 'a :: {division_ring,ring_char_0} fls) =
      - inverse (of_nat (n-1)) * fls_X_inv ^ (n-1)"
proof (cases "n=1")
  case False with assms show ?thesis
    by (simp add: fls_integral_X_inv_power' fls_inverse_const fls_of_nat)
qed simp    

lemma fls_integral_delta:
  assumes "m \<noteq> -1"
  shows
    "fls_integral (Abs_fls (\<lambda>n. if n=m then c else 0)) =
      Abs_fls (\<lambda>n. if n=m+1 then inverse (of_int (m+1)) * c else 0)"
  using   assms
  by      (intro fls_eqI) auto

lemma fls_regpart_integral:
  "fls_regpart (fls_integral f) = fps_integral0 (fls_regpart f)"
proof (rule fps_ext)
  fix n
  show "fls_regpart (fls_integral f) $ n = fps_integral0 (fls_regpart f) $ n"
    by (cases n) (simp_all add: fps_integral_def)
qed

lemma fls_integral_fps_to_fls:
  "fls_integral (fps_to_fls f) = fps_to_fls (fps_integral0 f)"
proof (intro fls_eqI)
  fix n :: int
  show "fls_integral (fps_to_fls f) $$ n = fps_to_fls (fps_integral0 f) $$ n"
  proof (cases "n<1")
    case True thus ?thesis by simp
  next
    case False
    hence "nat (n-1) = nat n - 1" by simp
    with False show ?thesis by (cases "nat n") auto
  qed
qed


subsubsection \<open>Algebraic rules of the integral\<close>

lemma fls_integral_add [simp]: "fls_integral (f+g) = fls_integral f + fls_integral g"
  by (intro fls_eqI) (simp add: algebra_simps)

lemma fls_integral_sub [simp]: "fls_integral (f-g) = fls_integral f - fls_integral g"
  by (intro fls_eqI) (simp add: algebra_simps)

lemma fls_integral_neg [simp]: "fls_integral (-f) = - fls_integral f"
  using fls_integral_sub[of 0 f] by simp

lemma fls_integral_mult_const_left:
  "fls_integral (fls_const c * f) = fls_const c * fls_integral (f :: 'a::division_ring fls)"
  by (intro fls_eqI) (simp add: mult.assoc mult_inverse_of_int_commute)

lemma fls_integral_mult_const_left_comm:
  fixes f :: "'a::{comm_ring_1,inverse} fls"
  shows "fls_integral (fls_const c * f) = fls_const c * fls_integral f"
  by (intro fls_eqI) (simp add: mult.assoc mult.commute)

lemma fls_integral_linear:
  fixes f g :: "'a::division_ring fls"
  shows
    "fls_integral (fls_const a * f + fls_const b * g) =
      fls_const a * fls_integral f + fls_const b * fls_integral g"
  by    (simp add: fls_integral_mult_const_left)

lemma fls_integral_linear_comm:
  fixes f g :: "'a::{comm_ring_1,inverse} fls"
  shows
    "fls_integral (fls_const a * f + fls_const b * g) =
      fls_const a * fls_integral f + fls_const b * fls_integral g"
  by    (simp add: fls_integral_mult_const_left_comm)

lemma fls_integral_mult_const_right:
  "fls_integral (f * fls_const c) = fls_integral f * fls_const c"
  by (intro fls_eqI) (simp add: mult.assoc)

lemma fls_integral_linear2:
    "fls_integral (f * fls_const a + g * fls_const b) =
      fls_integral f * fls_const a + fls_integral g * fls_const b"
  by    (simp add: fls_integral_mult_const_right)

lemma fls_integral_sum:
  "fls_integral (sum f S) = sum (\<lambda>i. fls_integral (f i)) S"
proof (cases "finite S")
  case True show ?thesis
    by (induct rule: finite_induct [OF True]) simp_all
qed simp


subsubsection \<open>Derivatives of integrals and vice versa\<close>

lemma fls_integral_fls_deriv:
  fixes a :: "'a::{division_ring,ring_char_0} fls"
  shows "fls_integral (fls_deriv a) + fls_const (a$$0) = a"
  by    (intro fls_eqI) (simp add: mult.assoc[symmetric])

lemma fls_deriv_fls_integral:
  fixes   a :: "'a::{division_ring,ring_char_0} fls"
  assumes "fls_residue a = 0"
  shows   "fls_deriv (fls_integral a) = a"
proof (intro fls_eqI)
  fix n :: int
  show "fls_deriv (fls_integral a) $$ n = a $$ n"
  proof (cases "n=-1")
    case True with assms show ?thesis by simp
  next
    case False
    hence "(of_int (n+1) :: 'a) \<noteq> 0" using of_int_eq_0_iff[of "n+1"] by simp
    hence "(of_int (n+1) :: 'a) * inverse (of_int (n+1) :: 'a) = (1::'a)"
      using of_int_eq_0_iff[of "n+1"] by simp
    moreover have
      "fls_deriv (fls_integral a) $$ n =
        (if n=-1 then 0 else of_int (n+1) * inverse (of_int (n+1)) * a$$n)"
      by (simp add: mult.assoc)
    ultimately show ?thesis
      by (simp add: False)
  qed
qed

text \<open>Series with zero residue are precisely the derivatives.\<close>

lemma fls_residue_nonzero_ex_antiderivative:
  fixes   f :: "'a::{division_ring,ring_char_0} fls"
  assumes "fls_residue f = 0"
  shows   "\<exists>F. fls_deriv F = f"
  using   assms fls_deriv_fls_integral
  by      auto

lemma fls_ex_antiderivative_residue_nonzero:
  assumes "\<exists>F. fls_deriv F = f"
  shows   "fls_residue f = 0"
  using   assms fls_residue_deriv
  by      auto

lemma fls_residue_nonzero_ex_anitderivative_iff:
  fixes f :: "'a::{division_ring,ring_char_0} fls"
  shows "fls_residue f = 0 \<longleftrightarrow> (\<exists>F. fls_deriv F = f)"
  using fls_residue_nonzero_ex_antiderivative fls_ex_antiderivative_residue_nonzero
  by    fast


subsection \<open>Topology\<close>

instantiation fls :: (group_add) metric_space
begin

definition
  dist_fls_def:
    "dist (a :: 'a fls) b =
      (if a = b
        then 0
        else if fls_subdegree (a-b) \<ge> 0
          then inverse (2 ^ nat (fls_subdegree (a-b)))
          else 2 ^ nat (-fls_subdegree (a-b))
      )"

lemma dist_fls_ge0: "dist (a :: 'a fls) b \<ge> 0"
  by (simp add: dist_fls_def)

definition uniformity_fls_def [code del]:
  "(uniformity :: ('a fls \<times> 'a fls) filter) = (INF e \<in> {0 <..}. principal {(x, y). dist x y < e})"

definition open_fls_def' [code del]:
  "open (U :: 'a fls set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

lemma dist_fls_sym: "dist (a :: 'a fls) b = dist b a"
  by  (cases "a\<noteq>b", cases "fls_subdegree (a-b) \<ge> 0")
      (simp_all add: fls_subdegree_minus_sym dist_fls_def)

context
begin

private lemma instance_helper:
  fixes   a b c :: "'a fls"
  assumes neq: "a\<noteq>b" "a\<noteq>c"
  and     dist_ineq: "dist a b > dist a c"
  shows   "fls_subdegree (a - b) < fls_subdegree (a - c)"
proof (
  cases "fls_subdegree (a-b) \<ge> 0" "fls_subdegree (a-c) \<ge> 0"
  rule: case_split[case_product case_split]
)
  case True_True with neq dist_ineq show ?thesis by (simp add: dist_fls_def)
next
  case False_True with dist_ineq show ?thesis by (simp add: dist_fls_def)
next
  case False_False with neq dist_ineq show ?thesis by (simp add: dist_fls_def)
next
  case True_False
  with neq
    have "(1::real) > 2 ^ (nat (fls_subdegree (a-b)) + nat (-fls_subdegree (a-c)))"
    and  "nat (fls_subdegree (a-b)) + nat (-fls_subdegree (a-c)) =
            nat (fls_subdegree (a-b) - fls_subdegree (a-c))"
    using dist_ineq
    by    (simp_all add: dist_fls_def field_simps power_add)
  hence "\<not> (1::real) < 2 ^ (nat (fls_subdegree (a-b) - fls_subdegree (a-c)))" by simp
  hence "\<not> (0 < nat (fls_subdegree (a - b) - fls_subdegree (a - c)))" by auto
  hence "fls_subdegree (a - b) \<le> fls_subdegree (a - c)" by simp
  with True_False show ?thesis by simp
qed

instance
proof
  show th: "dist a b = 0 \<longleftrightarrow> a = b" for a b :: "'a fls"
    by (simp add: dist_fls_def split: if_split_asm)
  then have th'[simp]: "dist a a = 0" for a :: "'a fls" by simp

  fix a b c :: "'a fls"
  consider "a = b" | "c = a \<or> c = b" | "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" by blast
  then show "dist a b \<le> dist a c + dist b c"
  proof cases
    case 1
    then show ?thesis by (simp add: dist_fls_def)
  next
    case 2
    then show ?thesis
      by (cases "c = a") (simp_all add: th dist_fls_sym)
  next
    case neq: 3
    have False if "dist a b > dist a c + dist b c"
    proof -
      from neq have "dist a b > 0" "dist b c > 0" "dist a c > 0" by (simp_all add: dist_fls_def)
      with that have dist_ineq: "dist a b > dist a c" "dist a b > dist b c" by simp_all
      have "fls_subdegree (a - b) < fls_subdegree (a - c)"
      and  "fls_subdegree (a - b) < fls_subdegree (b - c)"
        using instance_helper[of a b c] instance_helper[of b a c] neq dist_ineq
        by    (simp_all add: dist_fls_sym fls_subdegree_minus_sym)
      hence "(a - c) $$ fls_subdegree (a - b) = 0" and "(b - c) $$ fls_subdegree (a - b) = 0"
        by  (simp_all only: fls_eq0_below_subdegree)
      hence "(a - b) $$ fls_subdegree (a - b) = 0" by simp
      moreover from neq have "(a - b) $$ fls_subdegree (a - b) \<noteq> 0"
        by (intro nth_fls_subdegree_nonzero) simp
      ultimately show False by contradiction
    qed
    thus ?thesis by (auto simp: not_le[symmetric])
  qed
qed (rule open_fls_def' uniformity_fls_def)+

end
end

declare uniformity_Abort[where 'a="'a :: group_add fls", code]

lemma open_fls_def:
  "open (S :: 'a::group_add fls set) = (\<forall>a \<in> S. \<exists>r. r >0 \<and> {y. dist y a < r} \<subseteq> S)"
  unfolding open_dist subset_eq by simp


subsection \<open>Notation\<close>

no_notation fls_nth (infixl \<open>$$\<close> 75)

bundle fls_notation
begin
notation fls_nth (infixl \<open>$$\<close> 75)
end

end
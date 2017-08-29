(*  Title:      HOL/Computational_Algebra/Formal_Power_Series.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>A formalization of formal power series\<close>

theory Formal_Power_Series
imports
  Complex_Main
  Euclidean_Algorithm
begin


subsection \<open>The type of formal power series\<close>

typedef 'a fps = "{f :: nat \<Rightarrow> 'a. True}"
  morphisms fps_nth Abs_fps
  by simp

notation fps_nth (infixl "$" 75)

lemma expand_fps_eq: "p = q \<longleftrightarrow> (\<forall>n. p $ n = q $ n)"
  by (simp add: fps_nth_inject [symmetric] fun_eq_iff)

lemma fps_ext: "(\<And>n. p $ n = q $ n) \<Longrightarrow> p = q"
  by (simp add: expand_fps_eq)

lemma fps_nth_Abs_fps [simp]: "Abs_fps f $ n = f n"
  by (simp add: Abs_fps_inverse)

text \<open>Definition of the basic elements 0 and 1 and the basic operations of addition,
  negation and multiplication.\<close>

instantiation fps :: (zero) zero
begin
  definition fps_zero_def: "0 = Abs_fps (\<lambda>n. 0)"
  instance ..
end

lemma fps_zero_nth [simp]: "0 $ n = 0"
  unfolding fps_zero_def by simp

instantiation fps :: ("{one, zero}") one
begin
  definition fps_one_def: "1 = Abs_fps (\<lambda>n. if n = 0 then 1 else 0)"
  instance ..
end

lemma fps_one_nth [simp]: "1 $ n = (if n = 0 then 1 else 0)"
  unfolding fps_one_def by simp

instantiation fps :: (plus) plus
begin
  definition fps_plus_def: "op + = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n + g $ n))"
  instance ..
end

lemma fps_add_nth [simp]: "(f + g) $ n = f $ n + g $ n"
  unfolding fps_plus_def by simp

instantiation fps :: (minus) minus
begin
  definition fps_minus_def: "op - = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n - g $ n))"
  instance ..
end

lemma fps_sub_nth [simp]: "(f - g) $ n = f $ n - g $ n"
  unfolding fps_minus_def by simp

instantiation fps :: (uminus) uminus
begin
  definition fps_uminus_def: "uminus = (\<lambda>f. Abs_fps (\<lambda>n. - (f $ n)))"
  instance ..
end

lemma fps_neg_nth [simp]: "(- f) $ n = - (f $ n)"
  unfolding fps_uminus_def by simp

instantiation fps :: ("{comm_monoid_add, times}") times
begin
  definition fps_times_def: "op * = (\<lambda>f g. Abs_fps (\<lambda>n. \<Sum>i=0..n. f $ i * g $ (n - i)))"
  instance ..
end

lemma fps_mult_nth: "(f * g) $ n = (\<Sum>i=0..n. f$i * g$(n - i))"
  unfolding fps_times_def by simp

lemma fps_mult_nth_0 [simp]: "(f * g) $ 0 = f $ 0 * g $ 0"
  unfolding fps_times_def by simp

declare atLeastAtMost_iff [presburger]
declare Bex_def [presburger]
declare Ball_def [presburger]

lemma mult_delta_left:
  fixes x y :: "'a::mult_zero"
  shows "(if b then x else 0) * y = (if b then x * y else 0)"
  by simp

lemma mult_delta_right:
  fixes x y :: "'a::mult_zero"
  shows "x * (if b then y else 0) = (if b then x * y else 0)"
  by simp

lemma cond_value_iff: "f (if b then x else y) = (if b then f x else f y)"
  by auto

lemma cond_application_beta: "(if b then f else g) x = (if b then f x else g x)"
  by auto


subsection \<open>Formal power series form a commutative ring with unity, if the range of sequences
  they represent is a commutative ring with unity\<close>

instance fps :: (semigroup_add) semigroup_add
proof
  fix a b c :: "'a fps"
  show "a + b + c = a + (b + c)"
    by (simp add: fps_ext add.assoc)
qed

instance fps :: (ab_semigroup_add) ab_semigroup_add
proof
  fix a b :: "'a fps"
  show "a + b = b + a"
    by (simp add: fps_ext add.commute)
qed

lemma fps_mult_assoc_lemma:
  fixes k :: nat
    and f :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>j=0..k. \<Sum>i=0..j. f i (j - i) (n - j)) =
         (\<Sum>j=0..k. \<Sum>i=0..k - j. f j i (n - j - i))"
  by (induct k) (simp_all add: Suc_diff_le sum.distrib add.assoc)

instance fps :: (semiring_0) semigroup_mult
proof
  fix a b c :: "'a fps"
  show "(a * b) * c = a * (b * c)"
  proof (rule fps_ext)
    fix n :: nat
    have "(\<Sum>j=0..n. \<Sum>i=0..j. a$i * b$(j - i) * c$(n - j)) =
          (\<Sum>j=0..n. \<Sum>i=0..n - j. a$j * b$i * c$(n - j - i))"
      by (rule fps_mult_assoc_lemma)
    then show "((a * b) * c) $ n = (a * (b * c)) $ n"
      by (simp add: fps_mult_nth sum_distrib_left sum_distrib_right mult.assoc)
  qed
qed

lemma fps_mult_commute_lemma:
  fixes n :: nat
    and f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i=0..n. f i (n - i)) = (\<Sum>i=0..n. f (n - i) i)"
  by (rule sum.reindex_bij_witness[where i="op - n" and j="op - n"]) auto

instance fps :: (comm_semiring_0) ab_semigroup_mult
proof
  fix a b :: "'a fps"
  show "a * b = b * a"
  proof (rule fps_ext)
    fix n :: nat
    have "(\<Sum>i=0..n. a$i * b$(n - i)) = (\<Sum>i=0..n. a$(n - i) * b$i)"
      by (rule fps_mult_commute_lemma)
    then show "(a * b) $ n = (b * a) $ n"
      by (simp add: fps_mult_nth mult.commute)
  qed
qed

instance fps :: (monoid_add) monoid_add
proof
  fix a :: "'a fps"
  show "0 + a = a" by (simp add: fps_ext)
  show "a + 0 = a" by (simp add: fps_ext)
qed

instance fps :: (comm_monoid_add) comm_monoid_add
proof
  fix a :: "'a fps"
  show "0 + a = a" by (simp add: fps_ext)
qed

instance fps :: (semiring_1) monoid_mult
proof
  fix a :: "'a fps"
  show "1 * a = a"
    by (simp add: fps_ext fps_mult_nth mult_delta_left sum.delta)
  show "a * 1 = a"
    by (simp add: fps_ext fps_mult_nth mult_delta_right sum.delta')
qed

instance fps :: (cancel_semigroup_add) cancel_semigroup_add
proof
  fix a b c :: "'a fps"
  show "b = c" if "a + b = a + c"
    using that by (simp add: expand_fps_eq)
  show "b = c" if "b + a = c + a"
    using that by (simp add: expand_fps_eq)
qed

instance fps :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
proof
  fix a b c :: "'a fps"
  show "a + b - a = b"
    by (simp add: expand_fps_eq)
  show "a - b - c = a - (b + c)"
    by (simp add: expand_fps_eq diff_diff_eq)
qed

instance fps :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance fps :: (group_add) group_add
proof
  fix a b :: "'a fps"
  show "- a + a = 0" by (simp add: fps_ext)
  show "a + - b = a - b" by (simp add: fps_ext)
qed

instance fps :: (ab_group_add) ab_group_add
proof
  fix a b :: "'a fps"
  show "- a + a = 0" by (simp add: fps_ext)
  show "a - b = a + - b" by (simp add: fps_ext)
qed

instance fps :: (zero_neq_one) zero_neq_one
  by standard (simp add: expand_fps_eq)

instance fps :: (semiring_0) semiring
proof
  fix a b c :: "'a fps"
  show "(a + b) * c = a * c + b * c"
    by (simp add: expand_fps_eq fps_mult_nth distrib_right sum.distrib)
  show "a * (b + c) = a * b + a * c"
    by (simp add: expand_fps_eq fps_mult_nth distrib_left sum.distrib)
qed

instance fps :: (semiring_0) semiring_0
proof
  fix a :: "'a fps"
  show "0 * a = 0"
    by (simp add: fps_ext fps_mult_nth)
  show "a * 0 = 0"
    by (simp add: fps_ext fps_mult_nth)
qed

instance fps :: (semiring_0_cancel) semiring_0_cancel ..

instance fps :: (semiring_1) semiring_1 ..


subsection \<open>Selection of the nth power of the implicit variable in the infinite sum\<close>

lemma fps_square_nth: "(f^2) $ n = (\<Sum>k\<le>n. f $ k * f $ (n - k))"
  by (simp add: power2_eq_square fps_mult_nth atLeast0AtMost)

lemma fps_nonzero_nth: "f \<noteq> 0 \<longleftrightarrow> (\<exists> n. f $n \<noteq> 0)"
  by (simp add: expand_fps_eq)

lemma fps_nonzero_nth_minimal: "f \<noteq> 0 \<longleftrightarrow> (\<exists>n. f $ n \<noteq> 0 \<and> (\<forall>m < n. f $ m = 0))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?n = "LEAST n. f $ n \<noteq> 0"
  show ?rhs if ?lhs
  proof -
    from that have "\<exists>n. f $ n \<noteq> 0"
      by (simp add: fps_nonzero_nth)
    then have "f $ ?n \<noteq> 0"
      by (rule LeastI_ex)
    moreover have "\<forall>m<?n. f $ m = 0"
      by (auto dest: not_less_Least)
    ultimately have "f $ ?n \<noteq> 0 \<and> (\<forall>m<?n. f $ m = 0)" ..
    then show ?thesis ..
  qed
  show ?lhs if ?rhs
    using that by (auto simp add: expand_fps_eq)
qed

lemma fps_eq_iff: "f = g \<longleftrightarrow> (\<forall>n. f $ n = g $n)"
  by (rule expand_fps_eq)

lemma fps_sum_nth: "sum f S $ n = sum (\<lambda>k. (f k) $ n) S"
proof (cases "finite S")
  case True
  then show ?thesis by (induct set: finite) auto
next
  case False
  then show ?thesis by simp
qed


subsection \<open>Injection of the basic ring elements and multiplication by scalars\<close>

definition "fps_const c = Abs_fps (\<lambda>n. if n = 0 then c else 0)"

lemma fps_nth_fps_const [simp]: "fps_const c $ n = (if n = 0 then c else 0)"
  unfolding fps_const_def by simp

lemma fps_const_0_eq_0 [simp]: "fps_const 0 = 0"
  by (simp add: fps_ext)

lemma fps_const_1_eq_1 [simp]: "fps_const 1 = 1"
  by (simp add: fps_ext)

lemma fps_const_neg [simp]: "- (fps_const (c::'a::ring)) = fps_const (- c)"
  by (simp add: fps_ext)

lemma fps_const_add [simp]: "fps_const (c::'a::monoid_add) + fps_const d = fps_const (c + d)"
  by (simp add: fps_ext)

lemma fps_const_sub [simp]: "fps_const (c::'a::group_add) - fps_const d = fps_const (c - d)"
  by (simp add: fps_ext)

lemma fps_const_mult[simp]: "fps_const (c::'a::ring) * fps_const d = fps_const (c * d)"
  by (simp add: fps_eq_iff fps_mult_nth sum.neutral)

lemma fps_const_add_left: "fps_const (c::'a::monoid_add) + f =
    Abs_fps (\<lambda>n. if n = 0 then c + f$0 else f$n)"
  by (simp add: fps_ext)

lemma fps_const_add_right: "f + fps_const (c::'a::monoid_add) =
    Abs_fps (\<lambda>n. if n = 0 then f$0 + c else f$n)"
  by (simp add: fps_ext)

lemma fps_const_mult_left: "fps_const (c::'a::semiring_0) * f = Abs_fps (\<lambda>n. c * f$n)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_left sum.delta)

lemma fps_const_mult_right: "f * fps_const (c::'a::semiring_0) = Abs_fps (\<lambda>n. f$n * c)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_right sum.delta')

lemma fps_mult_left_const_nth [simp]: "(fps_const (c::'a::semiring_1) * f)$n = c* f$n"
  by (simp add: fps_mult_nth mult_delta_left sum.delta)

lemma fps_mult_right_const_nth [simp]: "(f * fps_const (c::'a::semiring_1))$n = f$n * c"
  by (simp add: fps_mult_nth mult_delta_right sum.delta')


subsection \<open>Formal power series form an integral domain\<close>

instance fps :: (ring) ring ..

instance fps :: (ring_1) ring_1
  by (intro_classes, auto simp add: distrib_right)

instance fps :: (comm_ring_1) comm_ring_1
  by (intro_classes, auto simp add: distrib_right)

instance fps :: (ring_no_zero_divisors) ring_no_zero_divisors
proof
  fix a b :: "'a fps"
  assume "a \<noteq> 0" and "b \<noteq> 0"
  then obtain i j where i: "a $ i \<noteq> 0" "\<forall>k<i. a $ k = 0" and j: "b $ j \<noteq> 0" "\<forall>k<j. b $ k =0"
    unfolding fps_nonzero_nth_minimal
    by blast+
  have "(a * b) $ (i + j) = (\<Sum>k=0..i+j. a $ k * b $ (i + j - k))"
    by (rule fps_mult_nth)
  also have "\<dots> = (a $ i * b $ (i + j - i)) + (\<Sum>k\<in>{0..i+j} - {i}. a $ k * b $ (i + j - k))"
    by (rule sum.remove) simp_all
  also have "(\<Sum>k\<in>{0..i+j}-{i}. a $ k * b $ (i + j - k)) = 0"
  proof (rule sum.neutral [rule_format])
    fix k assume "k \<in> {0..i+j} - {i}"
    then have "k < i \<or> i+j-k < j"
      by auto
    then show "a $ k * b $ (i + j - k) = 0"
      using i j by auto
  qed
  also have "a $ i * b $ (i + j - i) + 0 = a $ i * b $ j"
    by simp
  also have "a $ i * b $ j \<noteq> 0"
    using i j by simp
  finally have "(a*b) $ (i+j) \<noteq> 0" .
  then show "a * b \<noteq> 0"
    unfolding fps_nonzero_nth by blast
qed

instance fps :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..

instance fps :: (idom) idom ..

lemma numeral_fps_const: "numeral k = fps_const (numeral k)"
  by (induct k) (simp_all only: numeral.simps fps_const_1_eq_1
    fps_const_add [symmetric])

lemma neg_numeral_fps_const:
  "(- numeral k :: 'a :: ring_1 fps) = fps_const (- numeral k)"
  by (simp add: numeral_fps_const)

lemma fps_numeral_nth: "numeral n $ i = (if i = 0 then numeral n else 0)"
  by (simp add: numeral_fps_const)

lemma fps_numeral_nth_0 [simp]: "numeral n $ 0 = numeral n"
  by (simp add: numeral_fps_const)

lemma fps_of_nat: "fps_const (of_nat c) = of_nat c"
  by (induction c) (simp_all add: fps_const_add [symmetric] del: fps_const_add)

lemma numeral_neq_fps_zero [simp]: "(numeral f :: 'a :: field_char_0 fps) \<noteq> 0"
proof
  assume "numeral f = (0 :: 'a fps)"
  from arg_cong[of _ _ "\<lambda>F. F $ 0", OF this] show False by simp
qed 


subsection \<open>The efps_Xtractor series fps_X\<close>

lemma minus_one_power_iff: "(- (1::'a::comm_ring_1)) ^ n = (if even n then 1 else - 1)"
  by (induct n) auto

definition "fps_X = Abs_fps (\<lambda>n. if n = 1 then 1 else 0)"

lemma fps_X_mult_nth [simp]:
  "(fps_X * (f :: 'a::semiring_1 fps)) $n = (if n = 0 then 0 else f $ (n - 1))"
proof (cases "n = 0")
  case False
  have "(fps_X * f) $n = (\<Sum>i = 0..n. fps_X $ i * f $ (n - i))"
    by (simp add: fps_mult_nth)
  also have "\<dots> = f $ (n - 1)"
    using False by (simp add: fps_X_def mult_delta_left sum.delta)
  finally show ?thesis
    using False by simp
next
  case True
  then show ?thesis
    by (simp add: fps_mult_nth fps_X_def)
qed

lemma fps_X_mult_right_nth[simp]:
  "((a::'a::semiring_1 fps) * fps_X) $ n = (if n = 0 then 0 else a $ (n - 1))"
proof -
  have "(a * fps_X) $ n = (\<Sum>i = 0..n. a $ i * (if n - i = Suc 0 then 1 else 0))"
    by (simp add: fps_times_def fps_X_def)
  also have "\<dots> = (\<Sum>i = 0..n. if i = n - 1 then if n = 0 then 0 else a $ i else 0)"
    by (intro sum.cong) auto
  also have "\<dots> = (if n = 0 then 0 else a $ (n - 1))" by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma fps_mult_fps_X_commute: "fps_X * (a :: 'a :: semiring_1 fps) = a * fps_X" 
  by (simp add: fps_eq_iff)

lemma fps_X_power_iff: "fps_X ^ n = Abs_fps (\<lambda>m. if m = n then 1 else 0)"
  by (induction n) (auto simp: fps_eq_iff)

lemma fps_X_nth[simp]: "fps_X$n = (if n = 1 then 1 else 0)"
  by (simp add: fps_X_def)

lemma fps_X_power_nth[simp]: "(fps_X^k) $n = (if n = k then 1 else 0::'a::comm_ring_1)"
  by (simp add: fps_X_power_iff)

lemma fps_X_power_mult_nth: "(fps_X^k * (f :: 'a::comm_ring_1 fps)) $n = (if n < k then 0 else f $ (n - k))"
  apply (induct k arbitrary: n)
  apply simp
  unfolding power_Suc mult.assoc
  apply (case_tac n)
  apply auto
  done

lemma fps_X_power_mult_right_nth:
    "((f :: 'a::comm_ring_1 fps) * fps_X^k) $n = (if n < k then 0 else f $ (n - k))"
  by (metis fps_X_power_mult_nth mult.commute)


lemma fps_X_neq_fps_const [simp]: "(fps_X :: 'a :: zero_neq_one fps) \<noteq> fps_const c"
proof
  assume "(fps_X::'a fps) = fps_const (c::'a)"
  hence "fps_X$1 = (fps_const (c::'a))$1" by (simp only:)
  thus False by auto
qed

lemma fps_X_neq_zero [simp]: "(fps_X :: 'a :: zero_neq_one fps) \<noteq> 0"
  by (simp only: fps_const_0_eq_0[symmetric] fps_X_neq_fps_const) simp

lemma fps_X_neq_one [simp]: "(fps_X :: 'a :: zero_neq_one fps) \<noteq> 1"
  by (simp only: fps_const_1_eq_1[symmetric] fps_X_neq_fps_const) simp

lemma fps_X_neq_numeral [simp]: "(fps_X :: 'a :: {semiring_1,zero_neq_one} fps) \<noteq> numeral c"
  by (simp only: numeral_fps_const fps_X_neq_fps_const) simp

lemma fps_X_pow_eq_fps_X_pow_iff [simp]:
  "(fps_X :: ('a :: {comm_ring_1}) fps) ^ m = fps_X ^ n \<longleftrightarrow> m = n"
proof
  assume "(fps_X :: 'a fps) ^ m = fps_X ^ n"
  hence "(fps_X :: 'a fps) ^ m $ m = fps_X ^ n $ m" by (simp only:)
  thus "m = n" by (simp split: if_split_asm)
qed simp_all


subsection \<open>Subdegrees\<close>

definition subdegree :: "('a::zero) fps \<Rightarrow> nat" where
  "subdegree f = (if f = 0 then 0 else LEAST n. f$n \<noteq> 0)"

lemma subdegreeI:
  assumes "f $ d \<noteq> 0" and "\<And>i. i < d \<Longrightarrow> f $ i = 0"
  shows   "subdegree f = d"
proof-
  from assms(1) have "f \<noteq> 0" by auto
  moreover from assms(1) have "(LEAST i. f $ i \<noteq> 0) = d"
  proof (rule Least_equality)
    fix e assume "f $ e \<noteq> 0"
    with assms(2) have "\<not>(e < d)" by blast
    thus "e \<ge> d" by simp
  qed
  ultimately show ?thesis unfolding subdegree_def by simp
qed

lemma nth_subdegree_nonzero [simp,intro]: "f \<noteq> 0 \<Longrightarrow> f $ subdegree f \<noteq> 0"
proof-
  assume "f \<noteq> 0"
  hence "subdegree f = (LEAST n. f $ n \<noteq> 0)" by (simp add: subdegree_def)
  also from \<open>f \<noteq> 0\<close> have "\<exists>n. f$n \<noteq> 0" using fps_nonzero_nth by blast
  from LeastI_ex[OF this] have "f $ (LEAST n. f $ n \<noteq> 0) \<noteq> 0" .
  finally show ?thesis .
qed

lemma nth_less_subdegree_zero [dest]: "n < subdegree f \<Longrightarrow> f $ n = 0"
proof (cases "f = 0")
  assume "f \<noteq> 0" and less: "n < subdegree f"
  note less
  also from \<open>f \<noteq> 0\<close> have "subdegree f = (LEAST n. f $ n \<noteq> 0)" by (simp add: subdegree_def)
  finally show "f $ n = 0" using not_less_Least by blast
qed simp_all

lemma subdegree_geI:
  assumes "f \<noteq> 0" "\<And>i. i < n \<Longrightarrow> f$i = 0"
  shows   "subdegree f \<ge> n"
proof (rule ccontr)
  assume "\<not>(subdegree f \<ge> n)"
  with assms(2) have "f $ subdegree f = 0" by simp
  moreover from assms(1) have "f $ subdegree f \<noteq> 0" by simp
  ultimately show False by contradiction
qed

lemma subdegree_greaterI:
  assumes "f \<noteq> 0" "\<And>i. i \<le> n \<Longrightarrow> f$i = 0"
  shows   "subdegree f > n"
proof (rule ccontr)
  assume "\<not>(subdegree f > n)"
  with assms(2) have "f $ subdegree f = 0" by simp
  moreover from assms(1) have "f $ subdegree f \<noteq> 0" by simp
  ultimately show False by contradiction
qed

lemma subdegree_leI:
  "f $ n \<noteq> 0 \<Longrightarrow> subdegree f \<le> n"
  by (rule leI) auto


lemma subdegree_0 [simp]: "subdegree 0 = 0"
  by (simp add: subdegree_def)

lemma subdegree_1 [simp]: "subdegree (1 :: ('a :: zero_neq_one) fps) = 0"
  by (auto intro!: subdegreeI)

lemma subdegree_fps_X [simp]: "subdegree (fps_X :: ('a :: zero_neq_one) fps) = 1"
  by (auto intro!: subdegreeI simp: fps_X_def)

lemma subdegree_fps_const [simp]: "subdegree (fps_const c) = 0"
  by (cases "c = 0") (auto intro!: subdegreeI)

lemma subdegree_numeral [simp]: "subdegree (numeral n) = 0"
  by (simp add: numeral_fps_const)

lemma subdegree_eq_0_iff: "subdegree f = 0 \<longleftrightarrow> f = 0 \<or> f $ 0 \<noteq> 0"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  thus ?thesis
    using nth_subdegree_nonzero[OF \<open>f \<noteq> 0\<close>] by (fastforce intro!: subdegreeI)
qed simp_all

lemma subdegree_eq_0 [simp]: "f $ 0 \<noteq> 0 \<Longrightarrow> subdegree f = 0"
  by (simp add: subdegree_eq_0_iff)

lemma nth_subdegree_mult [simp]:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ (subdegree f + subdegree g) = f $ subdegree f * g $ subdegree g"
proof-
  let ?n = "subdegree f + subdegree g"
  have "(f * g) $ ?n = (\<Sum>i=0..?n. f$i * g$(?n-i))"
    by (simp add: fps_mult_nth)
  also have "... = (\<Sum>i=0..?n. if i = subdegree f then f$i * g$(?n-i) else 0)"
  proof (intro sum.cong)
    fix x assume x: "x \<in> {0..?n}"
    hence "x = subdegree f \<or> x < subdegree f \<or> ?n - x < subdegree g" by auto
    thus "f $ x * g $ (?n - x) = (if x = subdegree f then f $ x * g $ (?n - x) else 0)"
      by (elim disjE conjE) auto
  qed auto
  also have "... = f $ subdegree f * g $ subdegree g" by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma subdegree_mult [simp]:
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows "subdegree ((f :: ('a :: {ring_no_zero_divisors}) fps) * g) = subdegree f + subdegree g"
proof (rule subdegreeI)
  let ?n = "subdegree f + subdegree g"
  have "(f * g) $ ?n = (\<Sum>i=0..?n. f$i * g$(?n-i))" by (simp add: fps_mult_nth)
  also have "... = (\<Sum>i=0..?n. if i = subdegree f then f$i * g$(?n-i) else 0)"
  proof (intro sum.cong)
    fix x assume x: "x \<in> {0..?n}"
    hence "x = subdegree f \<or> x < subdegree f \<or> ?n - x < subdegree g" by auto
    thus "f $ x * g $ (?n - x) = (if x = subdegree f then f $ x * g $ (?n - x) else 0)"
      by (elim disjE conjE) auto
  qed auto
  also have "... = f $ subdegree f * g $ subdegree g" by (simp add: sum.delta)
  also from assms have "... \<noteq> 0" by auto
  finally show "(f * g) $ (subdegree f + subdegree g) \<noteq> 0" .
next
  fix m assume m: "m < subdegree f + subdegree g"
  have "(f * g) $ m = (\<Sum>i=0..m. f$i * g$(m-i))" by (simp add: fps_mult_nth)
  also have "... = (\<Sum>i=0..m. 0)"
  proof (rule sum.cong)
    fix i assume "i \<in> {0..m}"
    with m have "i < subdegree f \<or> m - i < subdegree g" by auto
    thus "f$i * g$(m-i) = 0" by (elim disjE) auto
  qed auto
  finally show "(f * g) $ m = 0" by simp
qed

lemma subdegree_power [simp]:
  "subdegree ((f :: ('a :: ring_1_no_zero_divisors) fps) ^ n) = n * subdegree f"
  by (cases "f = 0"; induction n) simp_all

lemma subdegree_uminus [simp]:
  "subdegree (-(f::('a::group_add) fps)) = subdegree f"
  by (simp add: subdegree_def)

lemma subdegree_minus_commute [simp]:
  "subdegree (f-(g::('a::group_add) fps)) = subdegree (g - f)"
proof -
  have "f - g = -(g - f)" by simp
  also have "subdegree ... = subdegree (g - f)" by (simp only: subdegree_uminus)
  finally show ?thesis .
qed

lemma subdegree_add_ge:
  assumes "f \<noteq> -(g :: ('a :: {group_add}) fps)"
  shows   "subdegree (f + g) \<ge> min (subdegree f) (subdegree g)"
proof (rule subdegree_geI)
  from assms show "f + g \<noteq> 0" by (subst (asm) eq_neg_iff_add_eq_0)
next
  fix i assume "i < min (subdegree f) (subdegree g)"
  hence "f $ i = 0" and "g $ i = 0" by auto
  thus "(f + g) $ i = 0" by force
qed

lemma subdegree_add_eq1:
  assumes "f \<noteq> 0"
  assumes "subdegree f < subdegree (g :: ('a :: {group_add}) fps)"
  shows   "subdegree (f + g) = subdegree f"
proof (rule antisym[OF subdegree_leI])
  from assms show "subdegree (f + g) \<ge> subdegree f"
    by (intro order.trans[OF min.boundedI subdegree_add_ge]) auto
  from assms have "f $ subdegree f \<noteq> 0" "g $ subdegree f = 0" by auto
  thus "(f + g) $ subdegree f \<noteq> 0" by simp
qed

lemma subdegree_add_eq2:
  assumes "g \<noteq> 0"
  assumes "subdegree g < subdegree (f :: ('a :: {ab_group_add}) fps)"
  shows   "subdegree (f + g) = subdegree g"
  using subdegree_add_eq1[OF assms] by (simp add: add.commute)

lemma subdegree_diff_eq1:
  assumes "f \<noteq> 0"
  assumes "subdegree f < subdegree (g :: ('a :: {ab_group_add}) fps)"
  shows   "subdegree (f - g) = subdegree f"
  using subdegree_add_eq1[of f "-g"] assms by (simp add: add.commute)

lemma subdegree_diff_eq2:
  assumes "g \<noteq> 0"
  assumes "subdegree g < subdegree (f :: ('a :: {ab_group_add}) fps)"
  shows   "subdegree (f - g) = subdegree g"
  using subdegree_add_eq2[of "-g" f] assms by (simp add: add.commute)

lemma subdegree_diff_ge [simp]:
  assumes "f \<noteq> (g :: ('a :: {group_add}) fps)"
  shows   "subdegree (f - g) \<ge> min (subdegree f) (subdegree g)"
  using assms subdegree_add_ge[of f "-g"] by simp




subsection \<open>Shifting and slicing\<close>

definition fps_shift :: "nat \<Rightarrow> 'a fps \<Rightarrow> 'a fps" where
  "fps_shift n f = Abs_fps (\<lambda>i. f $ (i + n))"

lemma fps_shift_nth [simp]: "fps_shift n f $ i = f $ (i + n)"
  by (simp add: fps_shift_def)

lemma fps_shift_0 [simp]: "fps_shift 0 f = f"
  by (intro fps_ext) (simp add: fps_shift_def)

lemma fps_shift_zero [simp]: "fps_shift n 0 = 0"
  by (intro fps_ext) (simp add: fps_shift_def)

lemma fps_shift_one: "fps_shift n 1 = (if n = 0 then 1 else 0)"
  by (intro fps_ext) (simp add: fps_shift_def)

lemma fps_shift_fps_const: "fps_shift n (fps_const c) = (if n = 0 then fps_const c else 0)"
  by (intro fps_ext) (simp add: fps_shift_def)

lemma fps_shift_numeral: "fps_shift n (numeral c) = (if n = 0 then numeral c else 0)"
  by (simp add: numeral_fps_const fps_shift_fps_const)

lemma fps_shift_fps_X_power [simp]:
  "n \<le> m \<Longrightarrow> fps_shift n (fps_X ^ m) = (fps_X ^ (m - n) ::'a::comm_ring_1 fps)"
  by (intro fps_ext) (auto simp: fps_shift_def )

lemma fps_shift_times_fps_X_power:
  "n \<le> subdegree f \<Longrightarrow> fps_shift n f * fps_X ^ n = (f :: 'a :: comm_ring_1 fps)"
  by (intro fps_ext) (auto simp: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power' [simp]:
  "fps_shift n (f * fps_X^n) = (f :: 'a :: comm_ring_1 fps)"
  by (intro fps_ext) (auto simp: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power'':
  "m \<le> n \<Longrightarrow> fps_shift n (f * fps_X^m) = fps_shift (n - m) (f :: 'a :: comm_ring_1 fps)"
  by (intro fps_ext) (auto simp: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_subdegree [simp]:
  "n \<le> subdegree f \<Longrightarrow> subdegree (fps_shift n f) = subdegree (f :: 'a :: comm_ring_1 fps) - n"
  by (cases "f = 0") (force intro: nth_less_subdegree_zero subdegreeI)+

lemma subdegree_decompose:
  "f = fps_shift (subdegree f) f * fps_X ^ subdegree (f :: ('a :: comm_ring_1) fps)"
  by (rule fps_ext) (auto simp: fps_X_power_mult_right_nth)

lemma subdegree_decompose':
  "n \<le> subdegree (f :: ('a :: comm_ring_1) fps) \<Longrightarrow> f = fps_shift n f * fps_X^n"
  by (rule fps_ext) (auto simp: fps_X_power_mult_right_nth intro!: nth_less_subdegree_zero)

lemma fps_shift_fps_shift:
  "fps_shift (m + n) f = fps_shift m (fps_shift n f)"
  by (rule fps_ext) (simp add: add_ac)

lemma fps_shift_add:
  "fps_shift n (f + g) = fps_shift n f + fps_shift n g"
  by (simp add: fps_eq_iff)

lemma fps_shift_mult:
  assumes "n \<le> subdegree (g :: 'b :: {comm_ring_1} fps)"
  shows   "fps_shift n (h*g) = h * fps_shift n g"
proof -
  from assms have "g = fps_shift n g * fps_X^n" by (rule subdegree_decompose')
  also have "h * ... = (h * fps_shift n g) * fps_X^n" by simp
  also have "fps_shift n ... = h * fps_shift n g" by simp
  finally show ?thesis .
qed

lemma fps_shift_mult_right:
  assumes "n \<le> subdegree (g :: 'b :: {comm_ring_1} fps)"
  shows   "fps_shift n (g*h) = h * fps_shift n g"
  by (subst mult.commute, subst fps_shift_mult) (simp_all add: assms)

lemma nth_subdegree_zero_iff [simp]: "f $ subdegree f = 0 \<longleftrightarrow> f = 0"
  by (cases "f = 0") auto

lemma fps_shift_subdegree_zero_iff [simp]:
  "fps_shift (subdegree f) f = 0 \<longleftrightarrow> f = 0"
  by (subst (1) nth_subdegree_zero_iff[symmetric], cases "f = 0")
     (simp_all del: nth_subdegree_zero_iff)


definition "fps_cutoff n f = Abs_fps (\<lambda>i. if i < n then f$i else 0)"

lemma fps_cutoff_nth [simp]: "fps_cutoff n f $ i = (if i < n then f$i else 0)"
  unfolding fps_cutoff_def by simp

lemma fps_cutoff_zero_iff: "fps_cutoff n f = 0 \<longleftrightarrow> (f = 0 \<or> n \<le> subdegree f)"
proof
  assume A: "fps_cutoff n f = 0"
  thus "f = 0 \<or> n \<le> subdegree f"
  proof (cases "f = 0")
    assume "f \<noteq> 0"
    with A have "n \<le> subdegree f"
      by (intro subdegree_geI) (auto simp: fps_eq_iff split: if_split_asm)
    thus ?thesis ..
  qed simp
qed (auto simp: fps_eq_iff intro: nth_less_subdegree_zero)

lemma fps_cutoff_0 [simp]: "fps_cutoff 0 f = 0"
  by (simp add: fps_eq_iff)

lemma fps_cutoff_zero [simp]: "fps_cutoff n 0 = 0"
  by (simp add: fps_eq_iff)

lemma fps_cutoff_one: "fps_cutoff n 1 = (if n = 0 then 0 else 1)"
  by (simp add: fps_eq_iff)

lemma fps_cutoff_fps_const: "fps_cutoff n (fps_const c) = (if n = 0 then 0 else fps_const c)"
  by (simp add: fps_eq_iff)

lemma fps_cutoff_numeral: "fps_cutoff n (numeral c) = (if n = 0 then 0 else numeral c)"
  by (simp add: numeral_fps_const fps_cutoff_fps_const)

lemma fps_shift_cutoff:
  "fps_shift n (f :: ('a :: comm_ring_1) fps) * fps_X^n + fps_cutoff n f = f"
  by (simp add: fps_eq_iff fps_X_power_mult_right_nth)


subsection \<open>Formal Power series form a metric space\<close>

instantiation fps :: (comm_ring_1) dist
begin

definition
  dist_fps_def: "dist (a :: 'a fps) b = (if a = b then 0 else inverse (2 ^ subdegree (a - b)))"

lemma dist_fps_ge0: "dist (a :: 'a fps) b \<ge> 0"
  by (simp add: dist_fps_def)

lemma dist_fps_sym: "dist (a :: 'a fps) b = dist b a"
  by (simp add: dist_fps_def)

instance ..

end

instantiation fps :: (comm_ring_1) metric_space
begin

definition uniformity_fps_def [code del]:
  "(uniformity :: ('a fps \<times> 'a fps) filter) = (INF e:{0 <..}. principal {(x, y). dist x y < e})"

definition open_fps_def' [code del]:
  "open (U :: 'a fps set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance
proof
  show th: "dist a b = 0 \<longleftrightarrow> a = b" for a b :: "'a fps"
    by (simp add: dist_fps_def split: if_split_asm)
  then have th'[simp]: "dist a a = 0" for a :: "'a fps" by simp

  fix a b c :: "'a fps"
  consider "a = b" | "c = a \<or> c = b" | "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" by blast
  then show "dist a b \<le> dist a c + dist b c"
  proof cases
    case 1
    then show ?thesis by (simp add: dist_fps_def)
  next
    case 2
    then show ?thesis
      by (cases "c = a") (simp_all add: th dist_fps_sym)
  next
    case neq: 3
    have False if "dist a b > dist a c + dist b c"
    proof -
      let ?n = "subdegree (a - b)"
      from neq have "dist a b > 0" "dist b c > 0" and "dist a c > 0" by (simp_all add: dist_fps_def)
      with that have "dist a b > dist a c" and "dist a b > dist b c" by simp_all
      with neq have "?n < subdegree (a - c)" and "?n < subdegree (b - c)"
        by (simp_all add: dist_fps_def field_simps)
      hence "(a - c) $ ?n = 0" and "(b - c) $ ?n = 0"
        by (simp_all only: nth_less_subdegree_zero)
      hence "(a - b) $ ?n = 0" by simp
      moreover from neq have "(a - b) $ ?n \<noteq> 0" by (intro nth_subdegree_nonzero) simp_all
      ultimately show False by contradiction
    qed
    thus ?thesis by (auto simp add: not_le[symmetric])
  qed
qed (rule open_fps_def' uniformity_fps_def)+

end

declare uniformity_Abort[where 'a="'a :: comm_ring_1 fps", code]

lemma open_fps_def: "open (S :: 'a::comm_ring_1 fps set) = (\<forall>a \<in> S. \<exists>r. r >0 \<and> {y. dist y a < r} \<subseteq> S)"
  unfolding open_dist subset_eq by simp

text \<open>The infinite sums and justification of the notation in textbooks.\<close>

lemma reals_power_lt_ex:
  fixes x y :: real
  assumes xp: "x > 0"
    and y1: "y > 1"
  shows "\<exists>k>0. (1/y)^k < x"
proof -
  have yp: "y > 0"
    using y1 by simp
  from reals_Archimedean2[of "max 0 (- log y x) + 1"]
  obtain k :: nat where k: "real k > max 0 (- log y x) + 1"
    by blast
  from k have kp: "k > 0"
    by simp
  from k have "real k > - log y x"
    by simp
  then have "ln y * real k > - ln x"
    unfolding log_def
    using ln_gt_zero_iff[OF yp] y1
    by (simp add: minus_divide_left field_simps del: minus_divide_left[symmetric])
  then have "ln y * real k + ln x > 0"
    by simp
  then have "exp (real k * ln y + ln x) > exp 0"
    by (simp add: ac_simps)
  then have "y ^ k * x > 1"
    unfolding exp_zero exp_add exp_of_nat_mult exp_ln [OF xp] exp_ln [OF yp]
    by simp
  then have "x > (1 / y)^k" using yp
    by (simp add: field_simps)
  then show ?thesis
    using kp by blast
qed

lemma fps_sum_rep_nth: "(sum (\<lambda>i. fps_const(a$i)*fps_X^i) {0..m})$n =
    (if n \<le> m then a$n else 0::'a::comm_ring_1)"
  by (auto simp add: fps_sum_nth cond_value_iff cong del: if_weak_cong)

lemma fps_notation: "(\<lambda>n. sum (\<lambda>i. fps_const(a$i) * fps_X^i) {0..n}) \<longlonglongrightarrow> a"
  (is "?s \<longlonglongrightarrow> a")
proof -
  have "\<exists>n0. \<forall>n \<ge> n0. dist (?s n) a < r" if "r > 0" for r
  proof -
    obtain n0 where n0: "(1/2)^n0 < r" "n0 > 0"
      using reals_power_lt_ex[OF \<open>r > 0\<close>, of 2] by auto
    show ?thesis
    proof -
      have "dist (?s n) a < r" if nn0: "n \<ge> n0" for n
      proof -
        from that have thnn0: "(1/2)^n \<le> (1/2 :: real)^n0"
          by (simp add: divide_simps)
        show ?thesis
        proof (cases "?s n = a")
          case True
          then show ?thesis
            unfolding dist_eq_0_iff[of "?s n" a, symmetric]
            using \<open>r > 0\<close> by (simp del: dist_eq_0_iff)
        next
          case False
          from False have dth: "dist (?s n) a = (1/2)^subdegree (?s n - a)"
            by (simp add: dist_fps_def field_simps)
          from False have kn: "subdegree (?s n - a) > n"
            by (intro subdegree_greaterI) (simp_all add: fps_sum_rep_nth)
          then have "dist (?s n) a < (1/2)^n"
            by (simp add: field_simps dist_fps_def)
          also have "\<dots> \<le> (1/2)^n0"
            using nn0 by (simp add: divide_simps)
          also have "\<dots> < r"
            using n0 by simp
          finally show ?thesis .
        qed
      qed
      then show ?thesis by blast
    qed
  qed
  then show ?thesis
    unfolding lim_sequentially by blast
qed


subsection \<open>Inverses of formal power series\<close>

declare sum.cong[fundef_cong]

instantiation fps :: ("{comm_monoid_add,inverse,times,uminus}") inverse
begin

fun natfun_inverse:: "'a fps \<Rightarrow> nat \<Rightarrow> 'a"
where
  "natfun_inverse f 0 = inverse (f$0)"
| "natfun_inverse f n = - inverse (f$0) * sum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n}"

definition fps_inverse_def: "inverse f = (if f $ 0 = 0 then 0 else Abs_fps (natfun_inverse f))"

definition fps_divide_def:
  "f div g = (if g = 0 then 0 else
     let n = subdegree g; h = fps_shift n g
     in  fps_shift n (f * inverse h))"

instance ..

end

lemma fps_inverse_zero [simp]:
  "inverse (0 :: 'a::{comm_monoid_add,inverse,times,uminus} fps) = 0"
  by (simp add: fps_ext fps_inverse_def)

lemma fps_inverse_one [simp]: "inverse (1 :: 'a::{division_ring,zero_neq_one} fps) = 1"
  apply (auto simp add: expand_fps_eq fps_inverse_def)
  apply (case_tac n)
  apply auto
  done

lemma inverse_mult_eq_1 [intro]:
  assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "inverse f * f = 1"
proof -
  have c: "inverse f * f = f * inverse f"
    by (simp add: mult.commute)
  from f0 have ifn: "\<And>n. inverse f $ n = natfun_inverse f n"
    by (simp add: fps_inverse_def)
  from f0 have th0: "(inverse f * f) $ 0 = 1"
    by (simp add: fps_mult_nth fps_inverse_def)
  have "(inverse f * f)$n = 0" if np: "n > 0" for n
  proof -
    from np have eq: "{0..n} = {0} \<union> {1 .. n}"
      by auto
    have d: "{0} \<inter> {1 .. n} = {}"
      by auto
    from f0 np have th0: "- (inverse f $ n) =
      (sum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n}) / (f$0)"
      by (cases n) (simp_all add: divide_inverse fps_inverse_def)
    from th0[symmetric, unfolded nonzero_divide_eq_eq[OF f0]]
    have th1: "sum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n} = - (f$0) * (inverse f)$n"
      by (simp add: field_simps)
    have "(f * inverse f) $ n = (\<Sum>i = 0..n. f $i * natfun_inverse f (n - i))"
      unfolding fps_mult_nth ifn ..
    also have "\<dots> = f$0 * natfun_inverse f n + (\<Sum>i = 1..n. f$i * natfun_inverse f (n-i))"
      by (simp add: eq)
    also have "\<dots> = 0"
      unfolding th1 ifn by simp
    finally show ?thesis unfolding c .
  qed
  with th0 show ?thesis
    by (simp add: fps_eq_iff)
qed

lemma fps_inverse_0_iff[simp]: "(inverse f) $ 0 = (0::'a::division_ring) \<longleftrightarrow> f $ 0 = 0"
  by (simp add: fps_inverse_def nonzero_imp_inverse_nonzero)

lemma fps_inverse_nth_0 [simp]: "inverse f $ 0 = inverse (f $ 0 :: 'a :: division_ring)"
  by (simp add: fps_inverse_def)

lemma fps_inverse_eq_0_iff[simp]: "inverse f = (0:: ('a::division_ring) fps) \<longleftrightarrow> f $ 0 = 0"
proof
  assume A: "inverse f = 0"
  have "0 = inverse f $ 0" by (subst A) simp
  thus "f $ 0 = 0" by simp
qed (simp add: fps_inverse_def)

lemma fps_inverse_idempotent[intro, simp]:
  assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "inverse (inverse f) = f"
proof -
  from f0 have if0: "inverse f $ 0 \<noteq> 0" by simp
  from inverse_mult_eq_1[OF f0] inverse_mult_eq_1[OF if0]
  have "inverse f * f = inverse f * inverse (inverse f)"
    by (simp add: ac_simps)
  then show ?thesis
    using f0 unfolding mult_cancel_left by simp
qed

lemma fps_inverse_unique:
  assumes fg: "(f :: 'a :: field fps) * g = 1"
  shows   "inverse f = g"
proof -
  have f0: "f $ 0 \<noteq> 0"
  proof
    assume "f $ 0 = 0"
    hence "0 = (f * g) $ 0" by simp
    also from fg have "(f * g) $ 0 = 1" by simp
    finally show False by simp
  qed
  from inverse_mult_eq_1[OF this] fg
  have th0: "inverse f * f = g * f"
    by (simp add: ac_simps)
  then show ?thesis
    using f0
    unfolding mult_cancel_right
    by (auto simp add: expand_fps_eq)
qed

lemma fps_inverse_eq_0: "f$0 = 0 \<Longrightarrow> inverse (f :: 'a :: division_ring fps) = 0"
  by simp
  
lemma sum_zero_lemma:
  fixes n::nat
  assumes "0 < n"
  shows "(\<Sum>i = 0..n. if n = i then 1 else if n - i = 1 then - 1 else 0) = (0::'a::field)"
proof -
  let ?f = "\<lambda>i. if n = i then 1 else if n - i = 1 then - 1 else 0"
  let ?g = "\<lambda>i. if i = n then 1 else if i = n - 1 then - 1 else 0"
  let ?h = "\<lambda>i. if i=n - 1 then - 1 else 0"
  have th1: "sum ?f {0..n} = sum ?g {0..n}"
    by (rule sum.cong) auto
  have th2: "sum ?g {0..n - 1} = sum ?h {0..n - 1}"
    apply (rule sum.cong)
    using assms
    apply auto
    done
  have eq: "{0 .. n} = {0.. n - 1} \<union> {n}"
    by auto
  from assms have d: "{0.. n - 1} \<inter> {n} = {}"
    by auto
  have f: "finite {0.. n - 1}" "finite {n}"
    by auto
  show ?thesis
    unfolding th1
    apply (simp add: sum.union_disjoint[OF f d, unfolded eq[symmetric]] del: One_nat_def)
    unfolding th2
    apply (simp add: sum.delta)
    done
qed

lemma fps_inverse_mult: "inverse (f * g :: 'a::field fps) = inverse f * inverse g"
proof (cases "f$0 = 0 \<or> g$0 = 0")
  assume "\<not>(f$0 = 0 \<or> g$0 = 0)"
  hence [simp]: "f$0 \<noteq> 0" "g$0 \<noteq> 0" by simp_all
  show ?thesis
  proof (rule fps_inverse_unique)
    have "f * g * (inverse f * inverse g) = (inverse f * f) * (inverse g * g)" by simp
    also have "... = 1" by (subst (1 2) inverse_mult_eq_1) simp_all
    finally show "f * g * (inverse f * inverse g) = 1" .
  qed
next
  assume A: "f$0 = 0 \<or> g$0 = 0"
  hence "inverse (f * g) = 0" by simp
  also from A have "... = inverse f * inverse g" by auto
  finally show "inverse (f * g) = inverse f * inverse g" .
qed


lemma fps_inverse_gp: "inverse (Abs_fps(\<lambda>n. (1::'a::field))) =
    Abs_fps (\<lambda>n. if n= 0 then 1 else if n=1 then - 1 else 0)"
  apply (rule fps_inverse_unique)
  apply (simp_all add: fps_eq_iff fps_mult_nth sum_zero_lemma)
  done

lemma subdegree_inverse [simp]: "subdegree (inverse (f::'a::field fps)) = 0"
proof (cases "f$0 = 0")
  assume nz: "f$0 \<noteq> 0"
  hence "subdegree (inverse f) + subdegree f = subdegree (inverse f * f)"
    by (subst subdegree_mult) auto
  also from nz have "subdegree f = 0" by (simp add: subdegree_eq_0_iff)
  also from nz have "inverse f * f = 1" by (rule inverse_mult_eq_1)
  finally show "subdegree (inverse f) = 0" by simp
qed (simp_all add: fps_inverse_def)

lemma fps_is_unit_iff [simp]: "(f :: 'a :: field fps) dvd 1 \<longleftrightarrow> f $ 0 \<noteq> 0"
proof
  assume "f dvd 1"
  then obtain g where "1 = f * g" by (elim dvdE)
  from this[symmetric] have "(f*g) $ 0 = 1" by simp
  thus "f $ 0 \<noteq> 0" by auto
next
  assume A: "f $ 0 \<noteq> 0"
  thus "f dvd 1" by (simp add: inverse_mult_eq_1[OF A, symmetric])
qed

lemma subdegree_eq_0' [simp]: "(f :: 'a :: field fps) dvd 1 \<Longrightarrow> subdegree f = 0"
  by simp

lemma fps_unit_dvd [simp]: "(f $ 0 :: 'a :: field) \<noteq> 0 \<Longrightarrow> f dvd g"
  by (rule dvd_trans, subst fps_is_unit_iff) simp_all

instantiation fps :: (field) normalization_semidom
begin

definition fps_unit_factor_def [simp]:
  "unit_factor f = fps_shift (subdegree f) f"

definition fps_normalize_def [simp]:
  "normalize f = (if f = 0 then 0 else fps_X ^ subdegree f)"

instance proof
  fix f :: "'a fps"
  show "unit_factor f * normalize f = f"
    by (simp add: fps_shift_times_fps_X_power)
next
  fix f g :: "'a fps"
  show "unit_factor (f * g) = unit_factor f * unit_factor g"
  proof (cases "f = 0 \<or> g = 0")
    assume "\<not>(f = 0 \<or> g = 0)"
    thus "unit_factor (f * g) = unit_factor f * unit_factor g"
    unfolding fps_unit_factor_def
      by (auto simp: fps_shift_fps_shift fps_shift_mult fps_shift_mult_right)
  qed auto
next
  fix f g :: "'a fps"
  assume "g \<noteq> 0"
  then have "f * (fps_shift (subdegree g) g * inverse (fps_shift (subdegree g) g)) = f"
    by (metis add_cancel_right_left fps_shift_nth inverse_mult_eq_1 mult.commute mult_cancel_left2 nth_subdegree_nonzero)
  then have "fps_shift (subdegree g) (g * (f * inverse (fps_shift (subdegree g) g))) = f"
    by (simp add: fps_shift_mult_right mult.commute)
  with \<open>g \<noteq> 0\<close> show "f * g / g = f"
    by (simp add: fps_divide_def Let_def ac_simps)
qed (auto simp add: fps_divide_def Let_def)

end

instantiation fps :: (field) ring_div
begin

definition fps_mod_def:
  "f mod g = (if g = 0 then f else
     let n = subdegree g; h = fps_shift n g
     in  fps_cutoff n (f * inverse h) * h)"

lemma fps_mod_eq_zero:
  assumes "g \<noteq> 0" and "subdegree f \<ge> subdegree g"
  shows   "f mod g = 0"
  using assms by (cases "f = 0") (auto simp: fps_cutoff_zero_iff fps_mod_def Let_def)

lemma fps_times_divide_eq:
  assumes "g \<noteq> 0" and "subdegree f \<ge> subdegree (g :: 'a fps)"
  shows   "f div g * g = f"
proof (cases "f = 0")
  assume nz: "f \<noteq> 0"
  define n where "n = subdegree g"
  define h where "h = fps_shift n g"
  from assms have [simp]: "h $ 0 \<noteq> 0" unfolding h_def by (simp add: n_def)

  from assms nz have "f div g * g = fps_shift n (f * inverse h) * g"
    by (simp add: fps_divide_def Let_def h_def n_def)
  also have "... = fps_shift n (f * inverse h) * fps_X^n * h" unfolding h_def n_def
    by (subst subdegree_decompose[of g]) simp
  also have "fps_shift n (f * inverse h) * fps_X^n = f * inverse h"
    by (rule fps_shift_times_fps_X_power) (simp_all add: nz assms n_def)
  also have "... * h = f * (inverse h * h)" by simp
  also have "inverse h * h = 1" by (rule inverse_mult_eq_1) simp
  finally show ?thesis by simp
qed (simp_all add: fps_divide_def Let_def)

lemma
  assumes "g$0 \<noteq> 0"
  shows   fps_divide_unit: "f div g = f * inverse g" and fps_mod_unit [simp]: "f mod g = 0"
proof -
  from assms have [simp]: "subdegree g = 0" by (simp add: subdegree_eq_0_iff)
  from assms show "f div g = f * inverse g"
    by (auto simp: fps_divide_def Let_def subdegree_eq_0_iff)
  from assms show "f mod g = 0" by (intro fps_mod_eq_zero) auto
qed

context
begin
private lemma fps_divide_cancel_aux1:
  assumes "h$0 \<noteq> (0 :: 'a :: field)"
  shows   "(h * f) div (h * g) = f div g"
proof (cases "g = 0")
  assume "g \<noteq> 0"
  from assms have "h \<noteq> 0" by auto
  note nz [simp] = \<open>g \<noteq> 0\<close> \<open>h \<noteq> 0\<close>
  from assms have [simp]: "subdegree h = 0" by (simp add: subdegree_eq_0_iff)

  have "(h * f) div (h * g) =
          fps_shift (subdegree g) (h * f * inverse (fps_shift (subdegree g) (h*g)))"
    by (simp add: fps_divide_def Let_def)
  also have "h * f * inverse (fps_shift (subdegree g) (h*g)) =
               (inverse h * h) * f * inverse (fps_shift (subdegree g) g)"
    by (subst fps_shift_mult) (simp_all add: algebra_simps fps_inverse_mult)
  also from assms have "inverse h * h = 1" by (rule inverse_mult_eq_1)
  finally show "(h * f) div (h * g) = f div g" by (simp_all add: fps_divide_def Let_def)
qed (simp_all add: fps_divide_def)

private lemma fps_divide_cancel_aux2:
  "(f * fps_X^m) div (g * fps_X^m) = f div (g :: 'a :: field fps)"
proof (cases "g = 0")
  assume [simp]: "g \<noteq> 0"
  have "(f * fps_X^m) div (g * fps_X^m) =
          fps_shift (subdegree g + m) (f*inverse (fps_shift (subdegree g + m) (g*fps_X^m))*fps_X^m)"
    by (simp add: fps_divide_def Let_def algebra_simps)
  also have "... = f div g"
    by (simp add: fps_shift_times_fps_X_power'' fps_divide_def Let_def)
  finally show ?thesis .
qed (simp_all add: fps_divide_def)

instance proof
  fix f g :: "'a fps"
  define n where "n = subdegree g"
  define h where "h = fps_shift n g"

  show "f div g * g + f mod g = f"
  proof (cases "g = 0 \<or> f = 0")
    assume "\<not>(g = 0 \<or> f = 0)"
    hence nz [simp]: "f \<noteq> 0" "g \<noteq> 0" by simp_all
    show ?thesis
    proof (rule disjE[OF le_less_linear])
      assume "subdegree f \<ge> subdegree g"
      with nz show ?thesis by (simp add: fps_mod_eq_zero fps_times_divide_eq)
    next
      assume "subdegree f < subdegree g"
      have g_decomp: "g = h * fps_X^n" unfolding h_def n_def by (rule subdegree_decompose)
      have "f div g * g + f mod g =
              fps_shift n (f * inverse h) * g + fps_cutoff n (f * inverse h) * h"
        by (simp add: fps_mod_def fps_divide_def Let_def n_def h_def)
      also have "... = h * (fps_shift n (f * inverse h) * fps_X^n + fps_cutoff n (f * inverse h))"
        by (subst g_decomp) (simp add: algebra_simps)
      also have "... = f * (inverse h * h)"
        by (subst fps_shift_cutoff) simp
      also have "inverse h * h = 1" by (rule inverse_mult_eq_1) (simp add: h_def n_def)
      finally show ?thesis by simp
    qed
  qed (auto simp: fps_mod_def fps_divide_def Let_def)
next

  fix f g h :: "'a fps"
  assume "h \<noteq> 0"
  show "(h * f) div (h * g) = f div g"
  proof -
    define m where "m = subdegree h"
    define h' where "h' = fps_shift m h"
    have h_decomp: "h = h' * fps_X ^ m" unfolding h'_def m_def by (rule subdegree_decompose)
    from \<open>h \<noteq> 0\<close> have [simp]: "h'$0 \<noteq> 0" by (simp add: h'_def m_def)
    have "(h * f) div (h * g) = (h' * f * fps_X^m) div (h' * g * fps_X^m)"
      by (simp add: h_decomp algebra_simps)
    also have "... = f div g" by (simp add: fps_divide_cancel_aux1 fps_divide_cancel_aux2)
    finally show ?thesis .
  qed

next
  fix f g h :: "'a fps"
  assume [simp]: "h \<noteq> 0"
  define n h' where dfs: "n = subdegree h" "h' = fps_shift n h"
  have "(f + g * h) div h = fps_shift n (f * inverse h') + fps_shift n (g * (h * inverse h'))"
    by (simp add: fps_divide_def Let_def dfs[symmetric] algebra_simps fps_shift_add)
  also have "h * inverse h' = (inverse h' * h') * fps_X^n"
    by (subst subdegree_decompose) (simp_all add: dfs)
  also have "... = fps_X^n" by (subst inverse_mult_eq_1) (simp_all add: dfs)
  also have "fps_shift n (g * fps_X^n) = g" by simp
  also have "fps_shift n (f * inverse h') = f div h"
    by (simp add: fps_divide_def Let_def dfs)
  finally show "(f + g * h) div h = g + f div h" by simp
qed

end
end

lemma subdegree_mod:
  assumes "f \<noteq> 0" "subdegree f < subdegree g"
  shows   "subdegree (f mod g) = subdegree f"
proof (cases "f div g * g = 0")
  assume "f div g * g \<noteq> 0"
  hence [simp]: "f div g \<noteq> 0" "g \<noteq> 0" by auto
  from div_mult_mod_eq[of f g] have "f mod g = f - f div g * g" by (simp add: algebra_simps)
  also from assms have "subdegree ... = subdegree f"
    by (intro subdegree_diff_eq1) simp_all
  finally show ?thesis .
next
  assume zero: "f div g * g = 0"
  from div_mult_mod_eq[of f g] have "f mod g = f - f div g * g" by (simp add: algebra_simps)
  also note zero
  finally show ?thesis by simp
qed

lemma fps_divide_nth_0 [simp]: "g $ 0 \<noteq> 0 \<Longrightarrow> (f div g) $ 0 = f $ 0 / (g $ 0 :: _ :: field)"
  by (simp add: fps_divide_unit divide_inverse)


lemma dvd_imp_subdegree_le:
  "(f :: 'a :: idom fps) dvd g \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> subdegree f \<le> subdegree g"
  by (auto elim: dvdE)

lemma fps_dvd_iff:
  assumes "(f :: 'a :: field fps) \<noteq> 0" "g \<noteq> 0"
  shows   "f dvd g \<longleftrightarrow> subdegree f \<le> subdegree g"
proof
  assume "subdegree f \<le> subdegree g"
  with assms have "g mod f = 0"
    by (simp add: fps_mod_def Let_def fps_cutoff_zero_iff)
  thus "f dvd g" by (simp add: dvd_eq_mod_eq_0)
qed (simp add: assms dvd_imp_subdegree_le)

lemma fps_shift_altdef:
  "fps_shift n f = (f :: 'a :: field fps) div fps_X^n"
  by (simp add: fps_divide_def)
  
lemma fps_div_fps_X_power_nth: "((f :: 'a :: field fps) div fps_X^n) $ k = f $ (k + n)"
  by (simp add: fps_shift_altdef [symmetric])

lemma fps_div_fps_X_nth: "((f :: 'a :: field fps) div fps_X) $ k = f $ Suc k"
  using fps_div_fps_X_power_nth[of f 1] by simp

lemma fps_const_inverse: "inverse (fps_const (a::'a::field)) = fps_const (inverse a)"
  by (cases "a \<noteq> 0", rule fps_inverse_unique) (auto simp: fps_eq_iff)

lemma fps_const_divide: "fps_const (x :: _ :: field) / fps_const y = fps_const (x / y)"
  by (cases "y = 0") (simp_all add: fps_divide_unit fps_const_inverse divide_inverse)

lemma inverse_fps_numeral:
  "inverse (numeral n :: ('a :: field_char_0) fps) = fps_const (inverse (numeral n))"
  by (intro fps_inverse_unique fps_ext) (simp_all add: fps_numeral_nth)

lemma fps_numeral_divide_divide:
  "x / numeral b / numeral c = (x / numeral (b * c) :: 'a :: field fps)"
  by (cases "numeral b = (0::'a)"; cases "numeral c = (0::'a)")
      (simp_all add: fps_divide_unit fps_inverse_mult [symmetric] numeral_fps_const numeral_mult 
                del: numeral_mult [symmetric])

lemma fps_numeral_mult_divide:
  "numeral b * x / numeral c = (numeral b / numeral c * x :: 'a :: field fps)"
  by (cases "numeral c = (0::'a)") (simp_all add: fps_divide_unit numeral_fps_const)

lemmas fps_numeral_simps = 
  fps_numeral_divide_divide fps_numeral_mult_divide inverse_fps_numeral neg_numeral_fps_const

lemma subdegree_div:
  assumes "q dvd p"
  shows   "subdegree ((p :: 'a :: field fps) div q) = subdegree p - subdegree q"
proof (cases "p = 0")
  case False
  from assms have "p = p div q * q" by simp
  also from assms False have "subdegree \<dots> = subdegree (p div q) + subdegree q"
    by (intro subdegree_mult) (auto simp: dvd_div_eq_0_iff)
  finally show ?thesis by simp
qed simp_all

lemma subdegree_div_unit:
  assumes "q $ 0 \<noteq> 0"
  shows   "subdegree ((p :: 'a :: field fps) div q) = subdegree p"
  using assms by (subst subdegree_div) simp_all


subsection \<open>Formal power series form a Euclidean ring\<close>

instantiation fps :: (field) euclidean_ring_cancel
begin

definition fps_euclidean_size_def:
  "euclidean_size f = (if f = 0 then 0 else 2 ^ subdegree f)"

instance proof
  fix f g :: "'a fps" assume [simp]: "g \<noteq> 0"
  show "euclidean_size f \<le> euclidean_size (f * g)"
    by (cases "f = 0") (auto simp: fps_euclidean_size_def)
  show "euclidean_size (f mod g) < euclidean_size g"
    apply (cases "f = 0", simp add: fps_euclidean_size_def)
    apply (rule disjE[OF le_less_linear[of "subdegree g" "subdegree f"]])
    apply (simp_all add: fps_mod_eq_zero fps_euclidean_size_def subdegree_mod)
    done
qed (simp_all add: fps_euclidean_size_def)

end

instantiation fps :: (field) euclidean_ring_gcd
begin
definition fps_gcd_def: "(gcd :: 'a fps \<Rightarrow> _) = Euclidean_Algorithm.gcd"
definition fps_lcm_def: "(lcm :: 'a fps \<Rightarrow> _) = Euclidean_Algorithm.lcm"
definition fps_Gcd_def: "(Gcd :: 'a fps set \<Rightarrow> _) = Euclidean_Algorithm.Gcd"
definition fps_Lcm_def: "(Lcm :: 'a fps set \<Rightarrow> _) = Euclidean_Algorithm.Lcm"
instance by standard (simp_all add: fps_gcd_def fps_lcm_def fps_Gcd_def fps_Lcm_def)
end

lemma fps_gcd:
  assumes [simp]: "f \<noteq> 0" "g \<noteq> 0"
  shows   "gcd f g = fps_X ^ min (subdegree f) (subdegree g)"
proof -
  let ?m = "min (subdegree f) (subdegree g)"
  show "gcd f g = fps_X ^ ?m"
  proof (rule sym, rule gcdI)
    fix d assume "d dvd f" "d dvd g"
    thus "d dvd fps_X ^ ?m" by (cases "d = 0") (auto simp: fps_dvd_iff)
  qed (simp_all add: fps_dvd_iff)
qed

lemma fps_gcd_altdef: "gcd (f :: 'a :: field fps) g =
  (if f = 0 \<and> g = 0 then 0 else
   if f = 0 then fps_X ^ subdegree g else
   if g = 0 then fps_X ^ subdegree f else
     fps_X ^ min (subdegree f) (subdegree g))"
  by (simp add: fps_gcd)

lemma fps_lcm:
  assumes [simp]: "f \<noteq> 0" "g \<noteq> 0"
  shows   "lcm f g = fps_X ^ max (subdegree f) (subdegree g)"
proof -
  let ?m = "max (subdegree f) (subdegree g)"
  show "lcm f g = fps_X ^ ?m"
  proof (rule sym, rule lcmI)
    fix d assume "f dvd d" "g dvd d"
    thus "fps_X ^ ?m dvd d" by (cases "d = 0") (auto simp: fps_dvd_iff)
  qed (simp_all add: fps_dvd_iff)
qed

lemma fps_lcm_altdef: "lcm (f :: 'a :: field fps) g =
  (if f = 0 \<or> g = 0 then 0 else fps_X ^ max (subdegree f) (subdegree g))"
  by (simp add: fps_lcm)

lemma fps_Gcd:
  assumes "A - {0} \<noteq> {}"
  shows   "Gcd A = fps_X ^ (INF f:A-{0}. subdegree f)"
proof (rule sym, rule GcdI)
  fix f assume "f \<in> A"
  thus "fps_X ^ (INF f:A - {0}. subdegree f) dvd f"
    by (cases "f = 0") (auto simp: fps_dvd_iff intro!: cINF_lower)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> d dvd f"
  from assms obtain f where "f \<in> A - {0}" by auto
  with d[of f] have [simp]: "d \<noteq> 0" by auto
  from d assms have "subdegree d \<le> (INF f:A-{0}. subdegree f)"
    by (intro cINF_greatest) (auto simp: fps_dvd_iff[symmetric])
  with d assms show "d dvd fps_X ^ (INF f:A-{0}. subdegree f)" by (simp add: fps_dvd_iff)
qed simp_all

lemma fps_Gcd_altdef: "Gcd (A :: 'a :: field fps set) =
  (if A \<subseteq> {0} then 0 else fps_X ^ (INF f:A-{0}. subdegree f))"
  using fps_Gcd by auto

lemma fps_Lcm:
  assumes "A \<noteq> {}" "0 \<notin> A" "bdd_above (subdegree`A)"
  shows   "Lcm A = fps_X ^ (SUP f:A. subdegree f)"
proof (rule sym, rule LcmI)
  fix f assume "f \<in> A"
  moreover from assms(3) have "bdd_above (subdegree ` A)" by auto
  ultimately show "f dvd fps_X ^ (SUP f:A. subdegree f)" using assms(2)
    by (cases "f = 0") (auto simp: fps_dvd_iff intro!: cSUP_upper)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> f dvd d"
  from assms obtain f where f: "f \<in> A" "f \<noteq> 0" by auto
  show "fps_X ^ (SUP f:A. subdegree f) dvd d"
  proof (cases "d = 0")
    assume "d \<noteq> 0"
    moreover from d have "\<And>f. f \<in> A \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> f dvd d" by blast
    ultimately have "subdegree d \<ge> (SUP f:A. subdegree f)" using assms
      by (intro cSUP_least) (auto simp: fps_dvd_iff)
    with \<open>d \<noteq> 0\<close> show ?thesis by (simp add: fps_dvd_iff)
  qed simp_all
qed simp_all

lemma fps_Lcm_altdef:
  "Lcm (A :: 'a :: field fps set) =
     (if 0 \<in> A \<or> \<not>bdd_above (subdegree`A) then 0 else
      if A = {} then 1 else fps_X ^ (SUP f:A. subdegree f))"
proof (cases "bdd_above (subdegree`A)")
  assume unbounded: "\<not>bdd_above (subdegree`A)"
  have "Lcm A = 0"
  proof (rule ccontr)
    assume "Lcm A \<noteq> 0"
    from unbounded obtain f where f: "f \<in> A" "subdegree (Lcm A) < subdegree f"
      unfolding bdd_above_def by (auto simp: not_le)
    moreover from f and \<open>Lcm A \<noteq> 0\<close> have "subdegree f \<le> subdegree (Lcm A)"
      by (intro dvd_imp_subdegree_le dvd_Lcm) simp_all
    ultimately show False by simp
  qed
  with unbounded show ?thesis by simp
qed (simp_all add: fps_Lcm Lcm_eq_0_I)



subsection \<open>Formal Derivatives, and the MacLaurin theorem around 0\<close>

definition "fps_deriv f = Abs_fps (\<lambda>n. of_nat (n + 1) * f $ (n + 1))"

lemma fps_deriv_nth[simp]: "fps_deriv f $ n = of_nat (n +1) * f $ (n + 1)"
  by (simp add: fps_deriv_def)

lemma fps_0th_higher_deriv: 
  "(fps_deriv ^^ n) f $ 0 = (fact n * f $ n :: 'a :: {comm_ring_1, semiring_char_0})"
  by (induction n arbitrary: f) (simp_all del: funpow.simps add: funpow_Suc_right algebra_simps)

lemma fps_deriv_linear[simp]:
  "fps_deriv (fps_const (a::'a::comm_semiring_1) * f + fps_const b * g) =
    fps_const a * fps_deriv f + fps_const b * fps_deriv g"
  unfolding fps_eq_iff fps_add_nth  fps_const_mult_left fps_deriv_nth by (simp add: field_simps)

lemma fps_deriv_mult[simp]:
  fixes f :: "'a::comm_ring_1 fps"
  shows "fps_deriv (f * g) = f * fps_deriv g + fps_deriv f * g"
proof -
  let ?D = "fps_deriv"
  have "(f * ?D g + ?D f * g) $ n = ?D (f*g) $ n" for n
  proof -
    let ?Zn = "{0 ..n}"
    let ?Zn1 = "{0 .. n + 1}"
    let ?g = "\<lambda>i. of_nat (i+1) * g $ (i+1) * f $ (n - i) +
        of_nat (i+1)* f $ (i+1) * g $ (n - i)"
    let ?h = "\<lambda>i. of_nat i * g $ i * f $ ((n+1) - i) +
        of_nat i* f $ i * g $ ((n + 1) - i)"
    have s0: "sum (\<lambda>i. of_nat i * f $ i * g $ (n + 1 - i)) ?Zn1 =
      sum (\<lambda>i. of_nat (n + 1 - i) * f $ (n + 1 - i) * g $ i) ?Zn1"
       by (rule sum.reindex_bij_witness[where i="op - (n + 1)" and j="op - (n + 1)"]) auto
    have s1: "sum (\<lambda>i. f $ i * g $ (n + 1 - i)) ?Zn1 =
      sum (\<lambda>i. f $ (n + 1 - i) * g $ i) ?Zn1"
       by (rule sum.reindex_bij_witness[where i="op - (n + 1)" and j="op - (n + 1)"]) auto
    have "(f * ?D g + ?D f * g)$n = (?D g * f + ?D f * g)$n"
      by (simp only: mult.commute)
    also have "\<dots> = (\<Sum>i = 0..n. ?g i)"
      by (simp add: fps_mult_nth sum.distrib[symmetric])
    also have "\<dots> = sum ?h {0..n+1}"
      by (rule sum.reindex_bij_witness_not_neutral
            [where S'="{}" and T'="{0}" and j="Suc" and i="\<lambda>i. i - 1"]) auto
    also have "\<dots> = (fps_deriv (f * g)) $ n"
      apply (simp only: fps_deriv_nth fps_mult_nth sum.distrib)
      unfolding s0 s1
      unfolding sum.distrib[symmetric] sum_distrib_left
      apply (rule sum.cong)
      apply (auto simp add: of_nat_diff field_simps)
      done
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding fps_eq_iff by auto
qed

lemma fps_deriv_fps_X[simp]: "fps_deriv fps_X = 1"
  by (simp add: fps_deriv_def fps_X_def fps_eq_iff)

lemma fps_deriv_neg[simp]:
  "fps_deriv (- (f:: 'a::comm_ring_1 fps)) = - (fps_deriv f)"
  by (simp add: fps_eq_iff fps_deriv_def)

lemma fps_deriv_add[simp]:
  "fps_deriv ((f:: 'a::comm_ring_1 fps) + g) = fps_deriv f + fps_deriv g"
  using fps_deriv_linear[of 1 f 1 g] by simp

lemma fps_deriv_sub[simp]:
  "fps_deriv ((f:: 'a::comm_ring_1 fps) - g) = fps_deriv f - fps_deriv g"
  using fps_deriv_add [of f "- g"] by simp

lemma fps_deriv_const[simp]: "fps_deriv (fps_const c) = 0"
  by (simp add: fps_ext fps_deriv_def fps_const_def)

lemma fps_deriv_of_nat [simp]: "fps_deriv (of_nat n) = 0"
  by (simp add: fps_of_nat [symmetric])

lemma fps_deriv_numeral [simp]: "fps_deriv (numeral n) = 0"
  by (simp add: numeral_fps_const)    

lemma fps_deriv_mult_const_left[simp]:
  "fps_deriv (fps_const (c::'a::comm_ring_1) * f) = fps_const c * fps_deriv f"
  by simp

lemma fps_deriv_0[simp]: "fps_deriv 0 = 0"
  by (simp add: fps_deriv_def fps_eq_iff)

lemma fps_deriv_1[simp]: "fps_deriv 1 = 0"
  by (simp add: fps_deriv_def fps_eq_iff )

lemma fps_deriv_mult_const_right[simp]:
  "fps_deriv (f * fps_const (c::'a::comm_ring_1)) = fps_deriv f * fps_const c"
  by simp

lemma fps_deriv_sum:
  "fps_deriv (sum f S) = sum (\<lambda>i. fps_deriv (f i :: 'a::comm_ring_1 fps)) S"
proof (cases "finite S")
  case False
  then show ?thesis by simp
next
  case True
  show ?thesis by (induct rule: finite_induct [OF True]) simp_all
qed

lemma fps_deriv_eq_0_iff [simp]:
  "fps_deriv f = 0 \<longleftrightarrow> f = fps_const (f$0 :: 'a::{idom,semiring_char_0})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?lhs if ?rhs
  proof -
    from that have "fps_deriv f = fps_deriv (fps_const (f$0))"
      by simp
    then show ?thesis
      by simp
  qed
  show ?rhs if ?lhs
  proof -
    from that have "\<forall>n. (fps_deriv f)$n = 0"
      by simp
    then have "\<forall>n. f$(n+1) = 0"
      by (simp del: of_nat_Suc of_nat_add One_nat_def)
    then show ?thesis
      apply (clarsimp simp add: fps_eq_iff fps_const_def)
      apply (erule_tac x="n - 1" in allE)
      apply simp
      done
  qed
qed

lemma fps_deriv_eq_iff:
  fixes f :: "'a::{idom,semiring_char_0} fps"
  shows "fps_deriv f = fps_deriv g \<longleftrightarrow> (f = fps_const(f$0 - g$0) + g)"
proof -
  have "fps_deriv f = fps_deriv g \<longleftrightarrow> fps_deriv (f - g) = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> f - g = fps_const ((f - g) $ 0)"
    unfolding fps_deriv_eq_0_iff ..
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma fps_deriv_eq_iff_ex:
  "(fps_deriv f = fps_deriv g) \<longleftrightarrow> (\<exists>c::'a::{idom,semiring_char_0}. f = fps_const c + g)"
  by (auto simp: fps_deriv_eq_iff)


fun fps_nth_deriv :: "nat \<Rightarrow> 'a::semiring_1 fps \<Rightarrow> 'a fps"
where
  "fps_nth_deriv 0 f = f"
| "fps_nth_deriv (Suc n) f = fps_nth_deriv n (fps_deriv f)"

lemma fps_nth_deriv_commute: "fps_nth_deriv (Suc n) f = fps_deriv (fps_nth_deriv n f)"
  by (induct n arbitrary: f) auto

lemma fps_nth_deriv_linear[simp]:
  "fps_nth_deriv n (fps_const (a::'a::comm_semiring_1) * f + fps_const b * g) =
    fps_const a * fps_nth_deriv n f + fps_const b * fps_nth_deriv n g"
  by (induct n arbitrary: f g) (auto simp add: fps_nth_deriv_commute)

lemma fps_nth_deriv_neg[simp]:
  "fps_nth_deriv n (- (f :: 'a::comm_ring_1 fps)) = - (fps_nth_deriv n f)"
  by (induct n arbitrary: f) simp_all

lemma fps_nth_deriv_add[simp]:
  "fps_nth_deriv n ((f :: 'a::comm_ring_1 fps) + g) = fps_nth_deriv n f + fps_nth_deriv n g"
  using fps_nth_deriv_linear[of n 1 f 1 g] by simp

lemma fps_nth_deriv_sub[simp]:
  "fps_nth_deriv n ((f :: 'a::comm_ring_1 fps) - g) = fps_nth_deriv n f - fps_nth_deriv n g"
  using fps_nth_deriv_add [of n f "- g"] by simp

lemma fps_nth_deriv_0[simp]: "fps_nth_deriv n 0 = 0"
  by (induct n) simp_all

lemma fps_nth_deriv_1[simp]: "fps_nth_deriv n 1 = (if n = 0 then 1 else 0)"
  by (induct n) simp_all

lemma fps_nth_deriv_const[simp]:
  "fps_nth_deriv n (fps_const c) = (if n = 0 then fps_const c else 0)"
  by (cases n) simp_all

lemma fps_nth_deriv_mult_const_left[simp]:
  "fps_nth_deriv n (fps_const (c::'a::comm_ring_1) * f) = fps_const c * fps_nth_deriv n f"
  using fps_nth_deriv_linear[of n "c" f 0 0 ] by simp

lemma fps_nth_deriv_mult_const_right[simp]:
  "fps_nth_deriv n (f * fps_const (c::'a::comm_ring_1)) = fps_nth_deriv n f * fps_const c"
  using fps_nth_deriv_linear[of n "c" f 0 0] by (simp add: mult.commute)

lemma fps_nth_deriv_sum:
  "fps_nth_deriv n (sum f S) = sum (\<lambda>i. fps_nth_deriv n (f i :: 'a::comm_ring_1 fps)) S"
proof (cases "finite S")
  case True
  show ?thesis by (induct rule: finite_induct [OF True]) simp_all
next
  case False
  then show ?thesis by simp
qed

lemma fps_deriv_maclauren_0:
  "(fps_nth_deriv k (f :: 'a::comm_semiring_1 fps)) $ 0 = of_nat (fact k) * f $ k"
  by (induct k arbitrary: f) (auto simp add: field_simps)


subsection \<open>Powers\<close>

lemma fps_power_zeroth_eq_one: "a$0 =1 \<Longrightarrow> a^n $ 0 = (1::'a::semiring_1)"
  by (induct n) (auto simp add: expand_fps_eq fps_mult_nth)

lemma fps_power_first_eq: "(a :: 'a::comm_ring_1 fps) $ 0 =1 \<Longrightarrow> a^n $ 1 = of_nat n * a$1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case unfolding power_Suc fps_mult_nth
    using Suc.hyps[OF \<open>a$0 = 1\<close>] \<open>a$0 = 1\<close> fps_power_zeroth_eq_one[OF \<open>a$0=1\<close>]
    by (simp add: field_simps)
qed

lemma startsby_one_power:"a $ 0 = (1::'a::comm_ring_1) \<Longrightarrow> a^n $ 0 = 1"
  by (induct n) (auto simp add: fps_mult_nth)

lemma startsby_zero_power:"a $0 = (0::'a::comm_ring_1) \<Longrightarrow> n > 0 \<Longrightarrow> a^n $0 = 0"
  by (induct n) (auto simp add: fps_mult_nth)

lemma startsby_power:"a $0 = (v::'a::comm_ring_1) \<Longrightarrow> a^n $0 = v^n"
  by (induct n) (auto simp add: fps_mult_nth)

lemma startsby_zero_power_iff[simp]: "a^n $0 = (0::'a::idom) \<longleftrightarrow> n \<noteq> 0 \<and> a$0 = 0"
  apply (rule iffI)
  apply (induct n)
  apply (auto simp add: fps_mult_nth)
  apply (rule startsby_zero_power, simp_all)
  done

lemma startsby_zero_power_prefix:
  assumes a0: "a $ 0 = (0::'a::idom)"
  shows "\<forall>n < k. a ^ k $ n = 0"
  using a0
proof (induct k rule: nat_less_induct)
  fix k
  assume H: "\<forall>m<k. a $0 =  0 \<longrightarrow> (\<forall>n<m. a ^ m $ n = 0)" and a0: "a $ 0 = 0"
  show "\<forall>m<k. a ^ k $ m = 0"
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc l)
    have "a^k $ m = 0" if mk: "m < k" for m
    proof (cases "m = 0")
      case True
      then show ?thesis
        using startsby_zero_power[of a k] Suc a0 by simp
    next
      case False
      have "a ^k $ m = (a^l * a) $m"
        by (simp add: Suc mult.commute)
      also have "\<dots> = (\<Sum>i = 0..m. a ^ l $ i * a $ (m - i))"
        by (simp add: fps_mult_nth)
      also have "\<dots> = 0"
        apply (rule sum.neutral)
        apply auto
        apply (case_tac "x = m")
        using a0 apply simp
        apply (rule H[rule_format])
        using a0 Suc mk apply auto
        done
      finally show ?thesis .
    qed
    then show ?thesis by blast
  qed
qed

lemma startsby_zero_sum_depends:
  assumes a0: "a $0 = (0::'a::idom)"
    and kn: "n \<ge> k"
  shows "sum (\<lambda>i. (a ^ i)$k) {0 .. n} = sum (\<lambda>i. (a ^ i)$k) {0 .. k}"
  apply (rule sum.mono_neutral_right)
  using kn
  apply auto
  apply (rule startsby_zero_power_prefix[rule_format, OF a0])
  apply arith
  done

lemma startsby_zero_power_nth_same:
  assumes a0: "a$0 = (0::'a::idom)"
  shows "a^n $ n = (a$1) ^ n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "a ^ Suc n $ (Suc n) = (a^n * a)$(Suc n)"
    by (simp add: field_simps)
  also have "\<dots> = sum (\<lambda>i. a^n$i * a $ (Suc n - i)) {0.. Suc n}"
    by (simp add: fps_mult_nth)
  also have "\<dots> = sum (\<lambda>i. a^n$i * a $ (Suc n - i)) {n .. Suc n}"
    apply (rule sum.mono_neutral_right)
    apply simp
    apply clarsimp
    apply clarsimp
    apply (rule startsby_zero_power_prefix[rule_format, OF a0])
    apply arith
    done
  also have "\<dots> = a^n $ n * a$1"
    using a0 by simp
  finally show ?case
    using Suc.hyps by simp
qed

lemma fps_inverse_power:
  fixes a :: "'a::field fps"
  shows "inverse (a^n) = inverse a ^ n"
  by (induction n) (simp_all add: fps_inverse_mult)

lemma fps_deriv_power:
  "fps_deriv (a ^ n) = fps_const (of_nat n :: 'a::comm_ring_1) * fps_deriv a * a ^ (n - 1)"
  apply (induct n)
  apply (auto simp add: field_simps fps_const_add[symmetric] simp del: fps_const_add)
  apply (case_tac n)
  apply (auto simp add: field_simps)
  done

lemma fps_inverse_deriv:
  fixes a :: "'a::field fps"
  assumes a0: "a$0 \<noteq> 0"
  shows "fps_deriv (inverse a) = - fps_deriv a * (inverse a)\<^sup>2"
proof -
  from inverse_mult_eq_1[OF a0]
  have "fps_deriv (inverse a * a) = 0" by simp
  then have "inverse a * fps_deriv a + fps_deriv (inverse a) * a = 0"
    by simp
  then have "inverse a * (inverse a * fps_deriv a + fps_deriv (inverse a) * a) = 0"
    by simp
  with inverse_mult_eq_1[OF a0]
  have "(inverse a)\<^sup>2 * fps_deriv a + fps_deriv (inverse a) = 0"
    unfolding power2_eq_square
    apply (simp add: field_simps)
    apply (simp add: mult.assoc[symmetric])
    done
  then have "(inverse a)\<^sup>2 * fps_deriv a + fps_deriv (inverse a) - fps_deriv a * (inverse a)\<^sup>2 =
      0 - fps_deriv a * (inverse a)\<^sup>2"
    by simp
  then show "fps_deriv (inverse a) = - fps_deriv a * (inverse a)\<^sup>2"
    by (simp add: field_simps)
qed

lemma fps_inverse_deriv':
  fixes a :: "'a::field fps"
  assumes a0: "a $ 0 \<noteq> 0"
  shows "fps_deriv (inverse a) = - fps_deriv a / a\<^sup>2"
  using fps_inverse_deriv[OF a0] a0
  by (simp add: fps_divide_unit power2_eq_square fps_inverse_mult)

lemma inverse_mult_eq_1':
  assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "f * inverse f = 1"
  by (metis mult.commute inverse_mult_eq_1 f0)

lemma fps_inverse_minus [simp]: "inverse (-f) = -inverse (f :: 'a :: field fps)"
  by (cases "f$0 = 0") (auto intro: fps_inverse_unique simp: inverse_mult_eq_1' fps_inverse_eq_0)
  
lemma divide_fps_const [simp]: "f / fps_const (c :: 'a :: field) = fps_const (inverse c) * f"
  by (cases "c = 0") (simp_all add: fps_divide_unit fps_const_inverse)

(* FIfps_XME: The last part of this proof should go through by simp once we have a proper
   theorem collection for simplifying division on rings *)
lemma fps_divide_deriv:
  assumes "b dvd (a :: 'a :: field fps)"
  shows   "fps_deriv (a / b) = (fps_deriv a * b - a * fps_deriv b) / b^2"
proof -
  have eq_divide_imp: "c \<noteq> 0 \<Longrightarrow> a * c = b \<Longrightarrow> a = b div c" for a b c :: "'a :: field fps"
    by (drule sym) (simp add: mult.assoc)
  from assms have "a = a / b * b" by simp
  also have "fps_deriv (a / b * b) = fps_deriv (a / b) * b + a / b * fps_deriv b" by simp
  finally have "fps_deriv (a / b) * b^2 = fps_deriv a * b - a * fps_deriv b" using assms
    by (simp add: power2_eq_square algebra_simps)
  thus ?thesis by (cases "b = 0") (auto simp: eq_divide_imp)
qed

lemma fps_inverse_gp': "inverse (Abs_fps (\<lambda>n. 1::'a::field)) = 1 - fps_X"
  by (simp add: fps_inverse_gp fps_eq_iff fps_X_def)

lemma fps_one_over_one_minus_fps_X_squared:
  "inverse ((1 - fps_X)^2 :: 'a :: field fps) = Abs_fps (\<lambda>n. of_nat (n+1))"
proof -
  have "inverse ((1 - fps_X)^2 :: 'a fps) = fps_deriv (inverse (1 - fps_X))"
    by (subst fps_inverse_deriv) (simp_all add: fps_inverse_power)
  also have "inverse (1 - fps_X :: 'a fps) = Abs_fps (\<lambda>_. 1)"
    by (subst fps_inverse_gp' [symmetric]) simp
  also have "fps_deriv \<dots> = Abs_fps (\<lambda>n. of_nat (n + 1))"
    by (simp add: fps_deriv_def)
  finally show ?thesis .
qed

lemma fps_nth_deriv_fps_X[simp]: "fps_nth_deriv n fps_X = (if n = 0 then fps_X else if n=1 then 1 else 0)"
  by (cases n) simp_all

lemma fps_inverse_fps_X_plus1: "inverse (1 + fps_X) = Abs_fps (\<lambda>n. (- (1::'a::field)) ^ n)"
  (is "_ = ?r")
proof -
  have eq: "(1 + fps_X) * ?r = 1"
    unfolding minus_one_power_iff
    by (auto simp add: field_simps fps_eq_iff)
  show ?thesis
    by (auto simp add: eq intro: fps_inverse_unique)
qed


subsection \<open>Integration\<close>

definition fps_integral :: "'a::field_char_0 fps \<Rightarrow> 'a \<Rightarrow> 'a fps"
  where "fps_integral a a0 = Abs_fps (\<lambda>n. if n = 0 then a0 else (a$(n - 1) / of_nat n))"

lemma fps_deriv_fps_integral: "fps_deriv (fps_integral a a0) = a"
  unfolding fps_integral_def fps_deriv_def
  by (simp add: fps_eq_iff del: of_nat_Suc)

lemma fps_integral_linear:
  "fps_integral (fps_const a * f + fps_const b * g) (a*a0 + b*b0) =
    fps_const a * fps_integral f a0 + fps_const b * fps_integral g b0"
  (is "?l = ?r")
proof -
  have "fps_deriv ?l = fps_deriv ?r"
    by (simp add: fps_deriv_fps_integral)
  moreover have "?l$0 = ?r$0"
    by (simp add: fps_integral_def)
  ultimately show ?thesis
    unfolding fps_deriv_eq_iff by auto
qed


subsection \<open>Composition of FPSs\<close>

definition fps_compose :: "'a::semiring_1 fps \<Rightarrow> 'a fps \<Rightarrow> 'a fps"  (infixl "oo" 55)
  where "a oo b = Abs_fps (\<lambda>n. sum (\<lambda>i. a$i * (b^i$n)) {0..n})"

lemma fps_compose_nth: "(a oo b)$n = sum (\<lambda>i. a$i * (b^i$n)) {0..n}"
  by (simp add: fps_compose_def)

lemma fps_compose_nth_0 [simp]: "(f oo g) $ 0 = f $ 0"
  by (simp add: fps_compose_nth)

lemma fps_compose_fps_X[simp]: "a oo fps_X = (a :: 'a::comm_ring_1 fps)"
  by (simp add: fps_ext fps_compose_def mult_delta_right sum.delta')

lemma fps_const_compose[simp]: "fps_const (a::'a::comm_ring_1) oo b = fps_const a"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left sum.delta)

lemma numeral_compose[simp]: "(numeral k :: 'a::comm_ring_1 fps) oo b = numeral k"
  unfolding numeral_fps_const by simp

lemma neg_numeral_compose[simp]: "(- numeral k :: 'a::comm_ring_1 fps) oo b = - numeral k"
  unfolding neg_numeral_fps_const by simp

lemma fps_X_fps_compose_startby0[simp]: "a$0 = 0 \<Longrightarrow> fps_X oo a = (a :: 'a::comm_ring_1 fps)"
  by (simp add: fps_eq_iff fps_compose_def mult_delta_left sum.delta not_le)


subsection \<open>Rules from Herbert Wilf's Generatingfunctionology\<close>

subsubsection \<open>Rule 1\<close>
  (* {a_{n+k}}_0^infty Corresponds to (f - sum (\<lambda>i. a_i * x^i))/x^h, for h>0*)

lemma fps_power_mult_eq_shift:
  "fps_X^Suc k * Abs_fps (\<lambda>n. a (n + Suc k)) =
    Abs_fps a - sum (\<lambda>i. fps_const (a i :: 'a::comm_ring_1) * fps_X^i) {0 .. k}"
  (is "?lhs = ?rhs")
proof -
  have "?lhs $ n = ?rhs $ n" for n :: nat
  proof -
    have "?lhs $ n = (if n < Suc k then 0 else a n)"
      unfolding fps_X_power_mult_nth by auto
    also have "\<dots> = ?rhs $ n"
    proof (induct k)
      case 0
      then show ?case
        by (simp add: fps_sum_nth)
    next
      case (Suc k)
      have "(Abs_fps a - sum (\<lambda>i. fps_const (a i :: 'a) * fps_X^i) {0 .. Suc k})$n =
        (Abs_fps a - sum (\<lambda>i. fps_const (a i :: 'a) * fps_X^i) {0 .. k} -
          fps_const (a (Suc k)) * fps_X^ Suc k) $ n"
        by (simp add: field_simps)
      also have "\<dots> = (if n < Suc k then 0 else a n) - (fps_const (a (Suc k)) * fps_X^ Suc k)$n"
        using Suc.hyps[symmetric] unfolding fps_sub_nth by simp
      also have "\<dots> = (if n < Suc (Suc k) then 0 else a n)"
        unfolding fps_X_power_mult_right_nth
        apply (auto simp add: not_less fps_const_def)
        apply (rule cong[of a a, OF refl])
        apply arith
        done
      finally show ?case
        by simp
    qed
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: fps_eq_iff)
qed


subsubsection \<open>Rule 2\<close>

  (* We can not reach the form of Wilf, but still near to it using rewrite rules*)
  (* If f reprents {a_n} and P is a polynomial, then
        P(xD) f represents {P(n) a_n}*)

definition "fps_XD = op * fps_X \<circ> fps_deriv"

lemma fps_XD_add[simp]:"fps_XD (a + b) = fps_XD a + fps_XD (b :: 'a::comm_ring_1 fps)"
  by (simp add: fps_XD_def field_simps)

lemma fps_XD_mult_const[simp]:"fps_XD (fps_const (c::'a::comm_ring_1) * a) = fps_const c * fps_XD a"
  by (simp add: fps_XD_def field_simps)

lemma fps_XD_linear[simp]: "fps_XD (fps_const c * a + fps_const d * b) =
    fps_const c * fps_XD a + fps_const d * fps_XD (b :: 'a::comm_ring_1 fps)"
  by simp

lemma fps_XDN_linear:
  "(fps_XD ^^ n) (fps_const c * a + fps_const d * b) =
    fps_const c * (fps_XD ^^ n) a + fps_const d * (fps_XD ^^ n) (b :: 'a::comm_ring_1 fps)"
  by (induct n) simp_all

lemma fps_mult_fps_X_deriv_shift: "fps_X* fps_deriv a = Abs_fps (\<lambda>n. of_nat n* a$n)"
  by (simp add: fps_eq_iff)

lemma fps_mult_fps_XD_shift:
  "(fps_XD ^^ k) (a :: 'a::comm_ring_1 fps) = Abs_fps (\<lambda>n. (of_nat n ^ k) * a$n)"
  by (induct k arbitrary: a) (simp_all add: fps_XD_def fps_eq_iff field_simps del: One_nat_def)


subsubsection \<open>Rule 3\<close>

text \<open>Rule 3 is trivial and is given by \<open>fps_times_def\<close>.\<close>


subsubsection \<open>Rule 5 --- summation and "division" by (1 - fps_X)\<close>

lemma fps_divide_fps_X_minus1_sum_lemma:
  "a = ((1::'a::comm_ring_1 fps) - fps_X) * Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
proof -
  let ?sa = "Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
  have th0: "\<And>i. (1 - (fps_X::'a fps)) $ i = (if i = 0 then 1 else if i = 1 then - 1 else 0)"
    by simp
  have "a$n = ((1 - fps_X) * ?sa) $ n" for n
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (simp add: fps_mult_nth)
  next
    case False
    then have u: "{0} \<union> ({1} \<union> {2..n}) = {0..n}" "{1} \<union> {2..n} = {1..n}"
      "{0..n - 1} \<union> {n} = {0..n}"
      by (auto simp: set_eq_iff)
    have d: "{0} \<inter> ({1} \<union> {2..n}) = {}" "{1} \<inter> {2..n} = {}" "{0..n - 1} \<inter> {n} = {}"
      using False by simp_all
    have f: "finite {0}" "finite {1}" "finite {2 .. n}"
      "finite {0 .. n - 1}" "finite {n}" by simp_all
    have "((1 - fps_X) * ?sa) $ n = sum (\<lambda>i. (1 - fps_X)$ i * ?sa $ (n - i)) {0 .. n}"
      by (simp add: fps_mult_nth)
    also have "\<dots> = a$n"
      unfolding th0
      unfolding sum.union_disjoint[OF f(1) finite_UnI[OF f(2,3)] d(1), unfolded u(1)]
      unfolding sum.union_disjoint[OF f(2) f(3) d(2)]
      apply (simp)
      unfolding sum.union_disjoint[OF f(4,5) d(3), unfolded u(3)]
      apply simp
      done
    finally show ?thesis
      by simp
  qed
  then show ?thesis
    unfolding fps_eq_iff by blast
qed

lemma fps_divide_fps_X_minus1_sum:
  "a /((1::'a::field fps) - fps_X) = Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
proof -
  let ?fps_X = "1 - (fps_X::'a fps)"
  have th0: "?fps_X $ 0 \<noteq> 0"
    by simp
  have "a /?fps_X = ?fps_X *  Abs_fps (\<lambda>n::nat. sum (op $ a) {0..n}) * inverse ?fps_X"
    using fps_divide_fps_X_minus1_sum_lemma[of a, symmetric] th0
    by (simp add: fps_divide_def mult.assoc)
  also have "\<dots> = (inverse ?fps_X * ?fps_X) * Abs_fps (\<lambda>n::nat. sum (op $ a) {0..n}) "
    by (simp add: ac_simps)
  finally show ?thesis
    by (simp add: inverse_mult_eq_1[OF th0])
qed


subsubsection \<open>Rule 4 in its more general form: generalizes Rule 3 for an arbitrary
  finite product of FPS, also the relvant instance of powers of a FPS\<close>

definition "natpermute n k = {l :: nat list. length l = k \<and> sum_list l = n}"

lemma natlist_trivial_1: "natpermute n 1 = {[n]}"
  apply (auto simp add: natpermute_def)
  apply (case_tac x)
  apply auto
  done

lemma append_natpermute_less_eq:
  assumes "xs @ ys \<in> natpermute n k"
  shows "sum_list xs \<le> n"
    and "sum_list ys \<le> n"
proof -
  from assms have "sum_list (xs @ ys) = n"
    by (simp add: natpermute_def)
  then have "sum_list xs + sum_list ys = n"
    by simp
  then show "sum_list xs \<le> n" and "sum_list ys \<le> n"
    by simp_all
qed

lemma natpermute_split:
  assumes "h \<le> k"
  shows "natpermute n k =
    (\<Union>m \<in>{0..n}. {l1 @ l2 |l1 l2. l1 \<in> natpermute m h \<and> l2 \<in> natpermute (n - m) (k - h)})"
  (is "?L = ?R" is "_ = (\<Union>m \<in>{0..n}. ?S m)")
proof
  show "?R \<subseteq> ?L"
  proof
    fix l
    assume l: "l \<in> ?R"
    from l obtain m xs ys where h: "m \<in> {0..n}"
      and xs: "xs \<in> natpermute m h"
      and ys: "ys \<in> natpermute (n - m) (k - h)"
      and leq: "l = xs@ys" by blast
    from xs have xs': "sum_list xs = m"
      by (simp add: natpermute_def)
    from ys have ys': "sum_list ys = n - m"
      by (simp add: natpermute_def)
    show "l \<in> ?L" using leq xs ys h
      apply (clarsimp simp add: natpermute_def)
      unfolding xs' ys'
      using assms xs ys
      unfolding natpermute_def
      apply simp
      done
  qed
  show "?L \<subseteq> ?R"
  proof
    fix l
    assume l: "l \<in> natpermute n k"
    let ?xs = "take h l"
    let ?ys = "drop h l"
    let ?m = "sum_list ?xs"
    from l have ls: "sum_list (?xs @ ?ys) = n"
      by (simp add: natpermute_def)
    have xs: "?xs \<in> natpermute ?m h" using l assms
      by (simp add: natpermute_def)
    have l_take_drop: "sum_list l = sum_list (take h l @ drop h l)"
      by simp
    then have ys: "?ys \<in> natpermute (n - ?m) (k - h)"
      using l assms ls by (auto simp add: natpermute_def simp del: append_take_drop_id)
    from ls have m: "?m \<in> {0..n}"
      by (simp add: l_take_drop del: append_take_drop_id)
    from xs ys ls show "l \<in> ?R"
      apply auto
      apply (rule bexI [where x = "?m"])
      apply (rule exI [where x = "?xs"])
      apply (rule exI [where x = "?ys"])
      using ls l
      apply (auto simp add: natpermute_def l_take_drop simp del: append_take_drop_id)
      apply simp
      done
  qed
qed

lemma natpermute_0: "natpermute n 0 = (if n = 0 then {[]} else {})"
  by (auto simp add: natpermute_def)

lemma natpermute_0'[simp]: "natpermute 0 k = (if k = 0 then {[]} else {replicate k 0})"
  apply (auto simp add: set_replicate_conv_if natpermute_def)
  apply (rule nth_equalityI)
  apply simp_all
  done

lemma natpermute_finite: "finite (natpermute n k)"
proof (induct k arbitrary: n)
  case 0
  then show ?case
    apply (subst natpermute_split[of 0 0, simplified])
    apply (simp add: natpermute_0)
    done
next
  case (Suc k)
  then show ?case unfolding natpermute_split [of k "Suc k", simplified]
    apply -
    apply (rule finite_UN_I)
    apply simp
    unfolding One_nat_def[symmetric] natlist_trivial_1
    apply simp
    done
qed

lemma natpermute_contain_maximal:
  "{xs \<in> natpermute n (k + 1). n \<in> set xs} = (\<Union>i\<in>{0 .. k}. {(replicate (k + 1) 0) [i:=n]})"
  (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix xs
    assume "xs \<in> ?A"
    then have H: "xs \<in> natpermute n (k + 1)" and n: "n \<in> set xs"
      by blast+
    then obtain i where i: "i \<in> {0.. k}" "xs!i = n"
      unfolding in_set_conv_nth by (auto simp add: less_Suc_eq_le natpermute_def)
    have eqs: "({0..k} - {i}) \<union> {i} = {0..k}"
      using i by auto
    have f: "finite({0..k} - {i})" "finite {i}"
      by auto
    have d: "({0..k} - {i}) \<inter> {i} = {}"
      using i by auto
    from H have "n = sum (nth xs) {0..k}"
      apply (simp add: natpermute_def)
      apply (auto simp add: atLeastLessThanSuc_atLeastAtMost sum_list_sum_nth)
      done
    also have "\<dots> = n + sum (nth xs) ({0..k} - {i})"
      unfolding sum.union_disjoint[OF f d, unfolded eqs] using i by simp
    finally have zxs: "\<forall> j\<in> {0..k} - {i}. xs!j = 0"
      by auto
    from H have xsl: "length xs = k+1"
      by (simp add: natpermute_def)
    from i have i': "i < length (replicate (k+1) 0)"   "i < k+1"
      unfolding length_replicate by presburger+
    have "xs = replicate (k+1) 0 [i := n]"
      apply (rule nth_equalityI)
      unfolding xsl length_list_update length_replicate
      apply simp
      apply clarify
      unfolding nth_list_update[OF i'(1)]
      using i zxs
      apply (case_tac "ia = i")
      apply (auto simp del: replicate.simps)
      done
    then show "xs \<in> ?B" using i by blast
  qed
  show "?B \<subseteq> ?A"
  proof
    fix xs
    assume "xs \<in> ?B"
    then obtain i where i: "i \<in> {0..k}" and xs: "xs = replicate (k + 1) 0 [i:=n]"
      by auto
    have nxs: "n \<in> set xs"
      unfolding xs
      apply (rule set_update_memI)
      using i apply simp
      done
    have xsl: "length xs = k + 1"
      by (simp only: xs length_replicate length_list_update)
    have "sum_list xs = sum (nth xs) {0..<k+1}"
      unfolding sum_list_sum_nth xsl ..
    also have "\<dots> = sum (\<lambda>j. if j = i then n else 0) {0..< k+1}"
      by (rule sum.cong) (simp_all add: xs del: replicate.simps)
    also have "\<dots> = n" using i by (simp add: sum.delta)
    finally have "xs \<in> natpermute n (k + 1)"
      using xsl unfolding natpermute_def mem_Collect_eq by blast
    then show "xs \<in> ?A"
      using nxs by blast
  qed
qed

text \<open>The general form.\<close>
lemma fps_prod_nth:
  fixes m :: nat
    and a :: "nat \<Rightarrow> 'a::comm_ring_1 fps"
  shows "(prod a {0 .. m}) $ n =
    sum (\<lambda>v. prod (\<lambda>j. (a j) $ (v!j)) {0..m}) (natpermute n (m+1))"
  (is "?P m n")
proof (induct m arbitrary: n rule: nat_less_induct)
  fix m n assume H: "\<forall>m' < m. \<forall>n. ?P m' n"
  show "?P m n"
  proof (cases m)
    case 0
    then show ?thesis
      apply simp
      unfolding natlist_trivial_1[where n = n, unfolded One_nat_def]
      apply simp
      done
  next
    case (Suc k)
    then have km: "k < m" by arith
    have u0: "{0 .. k} \<union> {m} = {0..m}"
      using Suc by (simp add: set_eq_iff) presburger
    have f0: "finite {0 .. k}" "finite {m}" by auto
    have d0: "{0 .. k} \<inter> {m} = {}" using Suc by auto
    have "(prod a {0 .. m}) $ n = (prod a {0 .. k} * a m) $ n"
      unfolding prod.union_disjoint[OF f0 d0, unfolded u0] by simp
    also have "\<dots> = (\<Sum>i = 0..n. (\<Sum>v\<in>natpermute i (k + 1). \<Prod>j\<in>{0..k}. a j $ v ! j) * a m $ (n - i))"
      unfolding fps_mult_nth H[rule_format, OF km] ..
    also have "\<dots> = (\<Sum>v\<in>natpermute n (m + 1). \<Prod>j\<in>{0..m}. a j $ v ! j)"
      apply (simp add: Suc)
      unfolding natpermute_split[of m "m + 1", simplified, of n,
        unfolded natlist_trivial_1[unfolded One_nat_def] Suc]
      apply (subst sum.UNION_disjoint)
      apply simp
      apply simp
      unfolding image_Collect[symmetric]
      apply clarsimp
      apply (rule finite_imageI)
      apply (rule natpermute_finite)
      apply (clarsimp simp add: set_eq_iff)
      apply auto
      apply (rule sum.cong)
      apply (rule refl)
      unfolding sum_distrib_right
      apply (rule sym)
      apply (rule_tac l = "\<lambda>xs. xs @ [n - x]" in sum.reindex_cong)
      apply (simp add: inj_on_def)
      apply auto
      unfolding prod.union_disjoint[OF f0 d0, unfolded u0, unfolded Suc]
      apply (clarsimp simp add: natpermute_def nth_append)
      done
    finally show ?thesis .
  qed
qed

text \<open>The special form for powers.\<close>
lemma fps_power_nth_Suc:
  fixes m :: nat
    and a :: "'a::comm_ring_1 fps"
  shows "(a ^ Suc m)$n = sum (\<lambda>v. prod (\<lambda>j. a $ (v!j)) {0..m}) (natpermute n (m+1))"
proof -
  have th0: "a^Suc m = prod (\<lambda>i. a) {0..m}"
    by (simp add: prod_constant)
  show ?thesis unfolding th0 fps_prod_nth ..
qed

lemma fps_power_nth:
  fixes m :: nat
    and a :: "'a::comm_ring_1 fps"
  shows "(a ^m)$n =
    (if m=0 then 1$n else sum (\<lambda>v. prod (\<lambda>j. a $ (v!j)) {0..m - 1}) (natpermute n m))"
  by (cases m) (simp_all add: fps_power_nth_Suc del: power_Suc)

lemma fps_nth_power_0:
  fixes m :: nat
    and a :: "'a::comm_ring_1 fps"
  shows "(a ^m)$0 = (a$0) ^ m"
proof (cases m)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  then have c: "m = card {0..n}" by simp
  have "(a ^m)$0 = prod (\<lambda>i. a$0) {0..n}"
    by (simp add: Suc fps_power_nth del: replicate.simps power_Suc)
  also have "\<dots> = (a$0) ^ m"
   unfolding c by (rule prod_constant)
 finally show ?thesis .
qed

lemma natpermute_max_card:
  assumes n0: "n \<noteq> 0"
  shows "card {xs \<in> natpermute n (k + 1). n \<in> set xs} = k + 1"
  unfolding natpermute_contain_maximal
proof -
  let ?A = "\<lambda>i. {replicate (k + 1) 0[i := n]}"
  let ?K = "{0 ..k}"
  have fK: "finite ?K"
    by simp
  have fAK: "\<forall>i\<in>?K. finite (?A i)"
    by auto
  have d: "\<forall>i\<in> ?K. \<forall>j\<in> ?K. i \<noteq> j \<longrightarrow>
    {replicate (k + 1) 0[i := n]} \<inter> {replicate (k + 1) 0[j := n]} = {}"
  proof clarify
    fix i j
    assume i: "i \<in> ?K" and j: "j \<in> ?K" and ij: "i \<noteq> j"
    have False if eq: "replicate (k+1) 0 [i:=n] = replicate (k+1) 0 [j:= n]"
    proof -
      have "(replicate (k+1) 0 [i:=n] ! i) = n"
        using i by (simp del: replicate.simps)
      moreover
      have "(replicate (k+1) 0 [j:=n] ! i) = 0"
        using i ij by (simp del: replicate.simps)
      ultimately show ?thesis
        using eq n0 by (simp del: replicate.simps)
    qed
    then show "{replicate (k + 1) 0[i := n]} \<inter> {replicate (k + 1) 0[j := n]} = {}"
      by auto
  qed
  from card_UN_disjoint[OF fK fAK d]
  show "card (\<Union>i\<in>{0..k}. {replicate (k + 1) 0[i := n]}) = k + 1"
    by simp
qed

lemma fps_power_Suc_nth:
  fixes f :: "'a :: comm_ring_1 fps"
  assumes k: "k > 0"
  shows "(f ^ Suc m) $ k = 
           of_nat (Suc m) * (f $ k * (f $ 0) ^ m) +
           (\<Sum>v\<in>{v\<in>natpermute k (m+1). k \<notin> set v}. \<Prod>j = 0..m. f $ v ! j)"
proof -
  define A B 
    where "A = {v\<in>natpermute k (m+1). k \<in> set v}" 
      and  "B = {v\<in>natpermute k (m+1). k \<notin> set v}"
  have [simp]: "finite A" "finite B" "A \<inter> B = {}" by (auto simp: A_def B_def natpermute_finite)

  from natpermute_max_card[of k m] k have card_A: "card A = m + 1" by (simp add: A_def)
  {
    fix v assume v: "v \<in> A"
    from v have [simp]: "length v = Suc m" by (simp add: A_def natpermute_def)
    from v have "\<exists>j. j \<le> m \<and> v ! j = k" 
      by (auto simp: set_conv_nth A_def natpermute_def less_Suc_eq_le)
    then guess j by (elim exE conjE) note j = this
    
    from v have "k = sum_list v" by (simp add: A_def natpermute_def)
    also have "\<dots> = (\<Sum>i=0..m. v ! i)"
      by (simp add: sum_list_sum_nth atLeastLessThanSuc_atLeastAtMost del: sum_op_ivl_Suc)
    also from j have "{0..m} = insert j ({0..m}-{j})" by auto
    also from j have "(\<Sum>i\<in>\<dots>. v ! i) = k + (\<Sum>i\<in>{0..m}-{j}. v ! i)"
      by (subst sum.insert) simp_all
    finally have "(\<Sum>i\<in>{0..m}-{j}. v ! i) = 0" by simp
    hence zero: "v ! i = 0" if "i \<in> {0..m}-{j}" for i using that
      by (subst (asm) sum_eq_0_iff) auto
      
    from j have "{0..m} = insert j ({0..m} - {j})" by auto
    also from j have "(\<Prod>i\<in>\<dots>. f $ (v ! i)) = f $ k * (\<Prod>i\<in>{0..m} - {j}. f $ (v ! i))"
      by (subst prod.insert) auto
    also have "(\<Prod>i\<in>{0..m} - {j}. f $ (v ! i)) = (\<Prod>i\<in>{0..m} - {j}. f $ 0)"
      by (intro prod.cong) (simp_all add: zero)
    also from j have "\<dots> = (f $ 0) ^ m" by (subst prod_constant) simp_all
    finally have "(\<Prod>j = 0..m. f $ (v ! j)) = f $ k * (f $ 0) ^ m" .
  } note A = this
  
  have "(f ^ Suc m) $ k = (\<Sum>v\<in>natpermute k (m + 1). \<Prod>j = 0..m. f $ v ! j)"
    by (rule fps_power_nth_Suc)
  also have "natpermute k (m+1) = A \<union> B" unfolding A_def B_def by blast
  also have "(\<Sum>v\<in>\<dots>. \<Prod>j = 0..m. f $ (v ! j)) = 
               (\<Sum>v\<in>A. \<Prod>j = 0..m. f $ (v ! j)) + (\<Sum>v\<in>B. \<Prod>j = 0..m. f $ (v ! j))"
    by (intro sum.union_disjoint) simp_all   
  also have "(\<Sum>v\<in>A. \<Prod>j = 0..m. f $ (v ! j)) = of_nat (Suc m) * (f $ k * (f $ 0) ^ m)"
    by (simp add: A card_A)
  finally show ?thesis by (simp add: B_def)
qed 
  
lemma fps_power_Suc_eqD:
  fixes f g :: "'a :: {idom,semiring_char_0} fps"
  assumes "f ^ Suc m = g ^ Suc m" "f $ 0 = g $ 0" "f $ 0 \<noteq> 0"
  shows   "f = g"
proof (rule fps_ext)
  fix k :: nat
  show "f $ k = g $ k"
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases "k = 0")
      case False
      let ?h = "\<lambda>f. (\<Sum>v | v \<in> natpermute k (m + 1) \<and> k \<notin> set v. \<Prod>j = 0..m. f $ v ! j)"
      from False fps_power_Suc_nth[of k f m] fps_power_Suc_nth[of k g m]
        have "f $ k * (of_nat (Suc m) * (f $ 0) ^ m) + ?h f =
                g $ k * (of_nat (Suc m) * (f $ 0) ^ m) + ?h g" using assms 
        by (simp add: mult_ac del: power_Suc of_nat_Suc)
      also have "v ! i < k" if "v \<in> {v\<in>natpermute k (m+1). k \<notin> set v}" "i \<le> m" for v i
        using that elem_le_sum_list[of i v] unfolding natpermute_def
        by (auto simp: set_conv_nth dest!: spec[of _ i])
      hence "?h f = ?h g"
        by (intro sum.cong refl prod.cong less lessI) (auto simp: natpermute_def)
      finally have "f $ k * (of_nat (Suc m) * (f $ 0) ^ m) = g $ k * (of_nat (Suc m) * (f $ 0) ^ m)"
        by simp
      with assms show "f $ k = g $ k" 
        by (subst (asm) mult_right_cancel) (auto simp del: of_nat_Suc)
    qed (simp_all add: assms)
  qed
qed

lemma fps_power_Suc_eqD':
  fixes f g :: "'a :: {idom,semiring_char_0} fps"
  assumes "f ^ Suc m = g ^ Suc m" "f $ subdegree f = g $ subdegree g"
  shows   "f = g"
proof (cases "f = 0")
  case False
  have "Suc m * subdegree f = subdegree (f ^ Suc m)"
    by (rule subdegree_power [symmetric])
  also have "f ^ Suc m = g ^ Suc m" by fact
  also have "subdegree \<dots> = Suc m * subdegree g" by (rule subdegree_power)
  finally have [simp]: "subdegree f = subdegree g"
    by (subst (asm) Suc_mult_cancel1)
  have "fps_shift (subdegree f) f * fps_X ^ subdegree f = f"
    by (rule subdegree_decompose [symmetric])
  also have "\<dots> ^ Suc m = g ^ Suc m" by fact
  also have "g = fps_shift (subdegree g) g * fps_X ^ subdegree g"
    by (rule subdegree_decompose)
  also have "subdegree f = subdegree g" by fact
  finally have "fps_shift (subdegree g) f ^ Suc m = fps_shift (subdegree g) g ^ Suc m"
    by (simp add: algebra_simps power_mult_distrib del: power_Suc)
  hence "fps_shift (subdegree g) f = fps_shift (subdegree g) g"
    by (rule fps_power_Suc_eqD) (insert assms False, auto)
  with subdegree_decompose[of f] subdegree_decompose[of g] show ?thesis by simp
qed (insert assms, simp_all)

lemma fps_power_eqD':
  fixes f g :: "'a :: {idom,semiring_char_0} fps"
  assumes "f ^ m = g ^ m" "f $ subdegree f = g $ subdegree g" "m > 0"
  shows   "f = g"
  using fps_power_Suc_eqD'[of f "m-1" g] assms by simp

lemma fps_power_eqD:
  fixes f g :: "'a :: {idom,semiring_char_0} fps"
  assumes "f ^ m = g ^ m" "f $ 0 = g $ 0" "f $ 0 \<noteq> 0" "m > 0"
  shows   "f = g"
  by (rule fps_power_eqD'[of f m g]) (insert assms, simp_all)

lemma fps_compose_inj_right:
  assumes a0: "a$0 = (0::'a::idom)"
    and a1: "a$1 \<noteq> 0"
  shows "(b oo a = c oo a) \<longleftrightarrow> b = c"
  (is "?lhs \<longleftrightarrow>?rhs")
proof
  show ?lhs if ?rhs using that by simp
  show ?rhs if ?lhs
  proof -
    have "b$n = c$n" for n
    proof (induct n rule: nat_less_induct)
      fix n
      assume H: "\<forall>m<n. b$m = c$m"
      show "b$n = c$n"
      proof (cases n)
        case 0
        from \<open>?lhs\<close> have "(b oo a)$n = (c oo a)$n"
          by simp
        then show ?thesis
          using 0 by (simp add: fps_compose_nth)
      next
        case (Suc n1)
        have f: "finite {0 .. n1}" "finite {n}" by simp_all
        have eq: "{0 .. n1} \<union> {n} = {0 .. n}" using Suc by auto
        have d: "{0 .. n1} \<inter> {n} = {}" using Suc by auto
        have seq: "(\<Sum>i = 0..n1. b $ i * a ^ i $ n) = (\<Sum>i = 0..n1. c $ i * a ^ i $ n)"
          apply (rule sum.cong)
          using H Suc
          apply auto
          done
        have th0: "(b oo a) $n = (\<Sum>i = 0..n1. c $ i * a ^ i $ n) + b$n * (a$1)^n"
          unfolding fps_compose_nth sum.union_disjoint[OF f d, unfolded eq] seq
          using startsby_zero_power_nth_same[OF a0]
          by simp
        have th1: "(c oo a) $n = (\<Sum>i = 0..n1. c $ i * a ^ i $ n) + c$n * (a$1)^n"
          unfolding fps_compose_nth sum.union_disjoint[OF f d, unfolded eq]
          using startsby_zero_power_nth_same[OF a0]
          by simp
        from \<open>?lhs\<close>[unfolded fps_eq_iff, rule_format, of n] th0 th1 a1
        show ?thesis by auto
      qed
    qed
    then show ?rhs by (simp add: fps_eq_iff)
  qed
qed


subsection \<open>Radicals\<close>

declare prod.cong [fundef_cong]

function radical :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a::field fps \<Rightarrow> nat \<Rightarrow> 'a"
where
  "radical r 0 a 0 = 1"
| "radical r 0 a (Suc n) = 0"
| "radical r (Suc k) a 0 = r (Suc k) (a$0)"
| "radical r (Suc k) a (Suc n) =
    (a$ Suc n - sum (\<lambda>xs. prod (\<lambda>j. radical r (Suc k) a (xs ! j)) {0..k})
      {xs. xs \<in> natpermute (Suc n) (Suc k) \<and> Suc n \<notin> set xs}) /
    (of_nat (Suc k) * (radical r (Suc k) a 0)^k)"
  by pat_completeness auto

termination radical
proof
  let ?R = "measure (\<lambda>(r, k, a, n). n)"
  {
    show "wf ?R" by auto
  next
    fix r k a n xs i
    assume xs: "xs \<in> {xs \<in> natpermute (Suc n) (Suc k). Suc n \<notin> set xs}" and i: "i \<in> {0..k}"
    have False if c: "Suc n \<le> xs ! i"
    proof -
      from xs i have "xs !i \<noteq> Suc n"
        by (auto simp add: in_set_conv_nth natpermute_def)
      with c have c': "Suc n < xs!i" by arith
      have fths: "finite {0 ..< i}" "finite {i}" "finite {i+1..<Suc k}"
        by simp_all
      have d: "{0 ..< i} \<inter> ({i} \<union> {i+1 ..< Suc k}) = {}" "{i} \<inter> {i+1..< Suc k} = {}"
        by auto
      have eqs: "{0..<Suc k} = {0 ..< i} \<union> ({i} \<union> {i+1 ..< Suc k})"
        using i by auto
      from xs have "Suc n = sum_list xs"
        by (simp add: natpermute_def)
      also have "\<dots> = sum (nth xs) {0..<Suc k}" using xs
        by (simp add: natpermute_def sum_list_sum_nth)
      also have "\<dots> = xs!i + sum (nth xs) {0..<i} + sum (nth xs) {i+1..<Suc k}"
        unfolding eqs  sum.union_disjoint[OF fths(1) finite_UnI[OF fths(2,3)] d(1)]
        unfolding sum.union_disjoint[OF fths(2) fths(3) d(2)]
        by simp
      finally show ?thesis using c' by simp
    qed
    then show "((r, Suc k, a, xs!i), r, Suc k, a, Suc n) \<in> ?R"
      apply auto
      apply (metis not_less)
      done
  next
    fix r k a n
    show "((r, Suc k, a, 0), r, Suc k, a, Suc n) \<in> ?R" by simp
  }
qed

definition "fps_radical r n a = Abs_fps (radical r n a)"

lemma fps_radical0[simp]: "fps_radical r 0 a = 1"
  apply (auto simp add: fps_eq_iff fps_radical_def)
  apply (case_tac n)
  apply auto
  done

lemma fps_radical_nth_0[simp]: "fps_radical r n a $ 0 = (if n = 0 then 1 else r n (a$0))"
  by (cases n) (simp_all add: fps_radical_def)

lemma fps_radical_power_nth[simp]:
  assumes r: "(r k (a$0)) ^ k = a$0"
  shows "fps_radical r k a ^ k $ 0 = (if k = 0 then 1 else a$0)"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq1: "fps_radical r k a ^ k $ 0 = (\<Prod>j\<in>{0..h}. fps_radical r k a $ (replicate k 0) ! j)"
    unfolding fps_power_nth Suc by simp
  also have "\<dots> = (\<Prod>j\<in>{0..h}. r k (a$0))"
    apply (rule prod.cong)
    apply simp
    using Suc
    apply (subgoal_tac "replicate k 0 ! x = 0")
    apply (auto intro: nth_replicate simp del: replicate.simps)
    done
  also have "\<dots> = a$0"
    using r Suc by (simp add: prod_constant)
  finally show ?thesis
    using Suc by simp
qed

lemma power_radical:
  fixes a:: "'a::field_char_0 fps"
  assumes a0: "a$0 \<noteq> 0"
  shows "(r (Suc k) (a$0)) ^ Suc k = a$0 \<longleftrightarrow> (fps_radical r (Suc k) a) ^ (Suc k) = a"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?r = "fps_radical r (Suc k) a"
  show ?rhs if r0: ?lhs
  proof -
    from a0 r0 have r00: "r (Suc k) (a$0) \<noteq> 0" by auto
    have "?r ^ Suc k $ z = a$z" for z
    proof (induct z rule: nat_less_induct)
      fix n
      assume H: "\<forall>m<n. ?r ^ Suc k $ m = a$m"
      show "?r ^ Suc k $ n = a $n"
      proof (cases n)
        case 0
        then show ?thesis
          using fps_radical_power_nth[of r "Suc k" a, OF r0] by simp
      next
        case (Suc n1)
        then have "n \<noteq> 0" by simp
        let ?Pnk = "natpermute n (k + 1)"
        let ?Pnkn = "{xs \<in> ?Pnk. n \<in> set xs}"
        let ?Pnknn = "{xs \<in> ?Pnk. n \<notin> set xs}"
        have eq: "?Pnkn \<union> ?Pnknn = ?Pnk" by blast
        have d: "?Pnkn \<inter> ?Pnknn = {}" by blast
        have f: "finite ?Pnkn" "finite ?Pnknn"
          using finite_Un[of ?Pnkn ?Pnknn, unfolded eq]
          by (metis natpermute_finite)+
        let ?f = "\<lambda>v. \<Prod>j\<in>{0..k}. ?r $ v ! j"
        have "sum ?f ?Pnkn = sum (\<lambda>v. ?r $ n * r (Suc k) (a $ 0) ^ k) ?Pnkn"
        proof (rule sum.cong)
          fix v assume v: "v \<in> {xs \<in> natpermute n (k + 1). n \<in> set xs}"
          let ?ths = "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) =
            fps_radical r (Suc k) a $ n * r (Suc k) (a $ 0) ^ k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding natpermute_contain_maximal by auto
          have "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) =
              (\<Prod>j\<in>{0..k}. if j = i then fps_radical r (Suc k) a $ n else r (Suc k) (a$0))"
            apply (rule prod.cong, simp)
            using i r0
            apply (simp del: replicate.simps)
            done
          also have "\<dots> = (fps_radical r (Suc k) a $ n) * r (Suc k) (a$0) ^ k"
            using i r0 by (simp add: prod_gen_delta)
          finally show ?ths .
        qed rule
        then have "sum ?f ?Pnkn = of_nat (k+1) * ?r $ n * r (Suc k) (a $ 0) ^ k"
          by (simp add: natpermute_max_card[OF \<open>n \<noteq> 0\<close>, simplified])
        also have "\<dots> = a$n - sum ?f ?Pnknn"
          unfolding Suc using r00 a0 by (simp add: field_simps fps_radical_def del: of_nat_Suc)
        finally have fn: "sum ?f ?Pnkn = a$n - sum ?f ?Pnknn" .
        have "(?r ^ Suc k)$n = sum ?f ?Pnkn + sum ?f ?Pnknn"
          unfolding fps_power_nth_Suc sum.union_disjoint[OF f d, unfolded eq] ..
        also have "\<dots> = a$n" unfolding fn by simp
        finally show ?thesis .
      qed
    qed
    then show ?thesis using r0 by (simp add: fps_eq_iff)
  qed
  show ?lhs if ?rhs
  proof -
    from that have "((fps_radical r (Suc k) a) ^ (Suc k))$0 = a$0"
      by simp
    then show ?thesis
      unfolding fps_power_nth_Suc
      by (simp add: prod_constant del: replicate.simps)
  qed
qed

(*
lemma power_radical:
  fixes a:: "'a::field_char_0 fps"
  assumes r0: "(r (Suc k) (a$0)) ^ Suc k = a$0" and a0: "a$0 \<noteq> 0"
  shows "(fps_radical r (Suc k) a) ^ (Suc k) = a"
proof-
  let ?r = "fps_radical r (Suc k) a"
  from a0 r0 have r00: "r (Suc k) (a$0) \<noteq> 0" by auto
  {fix z have "?r ^ Suc k $ z = a$z"
    proof(induct z rule: nat_less_induct)
      fix n assume H: "\<forall>m<n. ?r ^ Suc k $ m = a$m"
      {assume "n = 0" then have "?r ^ Suc k $ n = a $n"
          using fps_radical_power_nth[of r "Suc k" a, OF r0] by simp}
      moreover
      {fix n1 assume n1: "n = Suc n1"
        have fK: "finite {0..k}" by simp
        have nz: "n \<noteq> 0" using n1 by arith
        let ?Pnk = "natpermute n (k + 1)"
        let ?Pnkn = "{xs \<in> ?Pnk. n \<in> set xs}"
        let ?Pnknn = "{xs \<in> ?Pnk. n \<notin> set xs}"
        have eq: "?Pnkn \<union> ?Pnknn = ?Pnk" by blast
        have d: "?Pnkn \<inter> ?Pnknn = {}" by blast
        have f: "finite ?Pnkn" "finite ?Pnknn"
          using finite_Un[of ?Pnkn ?Pnknn, unfolded eq]
          by (metis natpermute_finite)+
        let ?f = "\<lambda>v. \<Prod>j\<in>{0..k}. ?r $ v ! j"
        have "sum ?f ?Pnkn = sum (\<lambda>v. ?r $ n * r (Suc k) (a $ 0) ^ k) ?Pnkn"
        proof(rule sum.cong2)
          fix v assume v: "v \<in> {xs \<in> natpermute n (k + 1). n \<in> set xs}"
          let ?ths = "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = fps_radical r (Suc k) a $ n * r (Suc k) (a $ 0) ^ k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding natpermute_contain_maximal by auto
          have "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then fps_radical r (Suc k) a $ n else r (Suc k) (a$0))"
            apply (rule prod.cong, simp)
            using i r0 by (simp del: replicate.simps)
          also have "\<dots> = (fps_radical r (Suc k) a $ n) * r (Suc k) (a$0) ^ k"
            unfolding prod_gen_delta[OF fK] using i r0 by simp
          finally show ?ths .
        qed
        then have "sum ?f ?Pnkn = of_nat (k+1) * ?r $ n * r (Suc k) (a $ 0) ^ k"
          by (simp add: natpermute_max_card[OF nz, simplified])
        also have "\<dots> = a$n - sum ?f ?Pnknn"
          unfolding n1 using r00 a0 by (simp add: field_simps fps_radical_def del: of_nat_Suc )
        finally have fn: "sum ?f ?Pnkn = a$n - sum ?f ?Pnknn" .
        have "(?r ^ Suc k)$n = sum ?f ?Pnkn + sum ?f ?Pnknn"
          unfolding fps_power_nth_Suc sum.union_disjoint[OF f d, unfolded eq] ..
        also have "\<dots> = a$n" unfolding fn by simp
        finally have "?r ^ Suc k $ n = a $n" .}
      ultimately  show "?r ^ Suc k $ n = a $n" by (cases n, auto)
  qed }
  then show ?thesis by (simp add: fps_eq_iff)
qed

*)
lemma eq_divide_imp':
  fixes c :: "'a::field"
  shows "c \<noteq> 0 \<Longrightarrow> a * c = b \<Longrightarrow> a = b / c"
  by (simp add: field_simps)

lemma radical_unique:
  assumes r0: "(r (Suc k) (b$0)) ^ Suc k = b$0"
    and a0: "r (Suc k) (b$0 ::'a::field_char_0) = a$0"
    and b0: "b$0 \<noteq> 0"
  shows "a^(Suc k) = b \<longleftrightarrow> a = fps_radical r (Suc k) b"
    (is "?lhs \<longleftrightarrow> ?rhs" is "_ \<longleftrightarrow> a = ?r")
proof
  show ?lhs if ?rhs
    using that using power_radical[OF b0, of r k, unfolded r0] by simp
  show ?rhs if ?lhs
  proof -
    have r00: "r (Suc k) (b$0) \<noteq> 0" using b0 r0 by auto
    have ceq: "card {0..k} = Suc k" by simp
    from a0 have a0r0: "a$0 = ?r$0" by simp
    have "a $ n = ?r $ n" for n
    proof (induct n rule: nat_less_induct)
      fix n
      assume h: "\<forall>m<n. a$m = ?r $m"
      show "a$n = ?r $ n"
      proof (cases n)
        case 0
        then show ?thesis using a0 by simp
      next
        case (Suc n1)
        have fK: "finite {0..k}" by simp
        have nz: "n \<noteq> 0" using Suc by simp
        let ?Pnk = "natpermute n (Suc k)"
        let ?Pnkn = "{xs \<in> ?Pnk. n \<in> set xs}"
        let ?Pnknn = "{xs \<in> ?Pnk. n \<notin> set xs}"
        have eq: "?Pnkn \<union> ?Pnknn = ?Pnk" by blast
        have d: "?Pnkn \<inter> ?Pnknn = {}" by blast
        have f: "finite ?Pnkn" "finite ?Pnknn"
          using finite_Un[of ?Pnkn ?Pnknn, unfolded eq]
          by (metis natpermute_finite)+
        let ?f = "\<lambda>v. \<Prod>j\<in>{0..k}. ?r $ v ! j"
        let ?g = "\<lambda>v. \<Prod>j\<in>{0..k}. a $ v ! j"
        have "sum ?g ?Pnkn = sum (\<lambda>v. a $ n * (?r$0)^k) ?Pnkn"
        proof (rule sum.cong)
          fix v
          assume v: "v \<in> {xs \<in> natpermute n (Suc k). n \<in> set xs}"
          let ?ths = "(\<Prod>j\<in>{0..k}. a $ v ! j) = a $ n * (?r$0)^k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding Suc_eq_plus1 natpermute_contain_maximal
            by (auto simp del: replicate.simps)
          have "(\<Prod>j\<in>{0..k}. a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then a $ n else r (Suc k) (b$0))"
            apply (rule prod.cong, simp)
            using i a0
            apply (simp del: replicate.simps)
            done
          also have "\<dots> = a $ n * (?r $ 0)^k"
            using i by (simp add: prod_gen_delta)
          finally show ?ths .
        qed rule
        then have th0: "sum ?g ?Pnkn = of_nat (k+1) * a $ n * (?r $ 0)^k"
          by (simp add: natpermute_max_card[OF nz, simplified])
        have th1: "sum ?g ?Pnknn = sum ?f ?Pnknn"
        proof (rule sum.cong, rule refl, rule prod.cong, simp)
          fix xs i
          assume xs: "xs \<in> ?Pnknn" and i: "i \<in> {0..k}"
          have False if c: "n \<le> xs ! i"
          proof -
            from xs i have "xs ! i \<noteq> n"
              by (auto simp add: in_set_conv_nth natpermute_def)
            with c have c': "n < xs!i" by arith
            have fths: "finite {0 ..< i}" "finite {i}" "finite {i+1..<Suc k}"
              by simp_all
            have d: "{0 ..< i} \<inter> ({i} \<union> {i+1 ..< Suc k}) = {}" "{i} \<inter> {i+1..< Suc k} = {}"
              by auto
            have eqs: "{0..<Suc k} = {0 ..< i} \<union> ({i} \<union> {i+1 ..< Suc k})"
              using i by auto
            from xs have "n = sum_list xs"
              by (simp add: natpermute_def)
            also have "\<dots> = sum (nth xs) {0..<Suc k}"
              using xs by (simp add: natpermute_def sum_list_sum_nth)
            also have "\<dots> = xs!i + sum (nth xs) {0..<i} + sum (nth xs) {i+1..<Suc k}"
              unfolding eqs  sum.union_disjoint[OF fths(1) finite_UnI[OF fths(2,3)] d(1)]
              unfolding sum.union_disjoint[OF fths(2) fths(3) d(2)]
              by simp
            finally show ?thesis using c' by simp
          qed
          then have thn: "xs!i < n" by presburger
          from h[rule_format, OF thn] show "a$(xs !i) = ?r$(xs!i)" .
        qed
        have th00: "\<And>x::'a. of_nat (Suc k) * (x * inverse (of_nat (Suc k))) = x"
          by (simp add: field_simps del: of_nat_Suc)
        from \<open>?lhs\<close> have "b$n = a^Suc k $ n"
          by (simp add: fps_eq_iff)
        also have "a ^ Suc k$n = sum ?g ?Pnkn + sum ?g ?Pnknn"
          unfolding fps_power_nth_Suc
          using sum.union_disjoint[OF f d, unfolded Suc_eq_plus1[symmetric],
            unfolded eq, of ?g] by simp
        also have "\<dots> = of_nat (k+1) * a $ n * (?r $ 0)^k + sum ?f ?Pnknn"
          unfolding th0 th1 ..
        finally have "of_nat (k+1) * a $ n * (?r $ 0)^k = b$n - sum ?f ?Pnknn"
          by simp
        then have "a$n = (b$n - sum ?f ?Pnknn) / (of_nat (k+1) * (?r $ 0)^k)"
          apply -
          apply (rule eq_divide_imp')
          using r00
          apply (simp del: of_nat_Suc)
          apply (simp add: ac_simps)
          done
        then show ?thesis
          apply (simp del: of_nat_Suc)
          unfolding fps_radical_def Suc
          apply (simp add: field_simps Suc th00 del: of_nat_Suc)
          done
      qed
    qed
    then show ?rhs by (simp add: fps_eq_iff)
  qed
qed


lemma radical_power:
  assumes r0: "r (Suc k) ((a$0) ^ Suc k) = a$0"
    and a0: "(a$0 :: 'a::field_char_0) \<noteq> 0"
  shows "(fps_radical r (Suc k) (a ^ Suc k)) = a"
proof -
  let ?ak = "a^ Suc k"
  have ak0: "?ak $ 0 = (a$0) ^ Suc k"
    by (simp add: fps_nth_power_0 del: power_Suc)
  from r0 have th0: "r (Suc k) (a ^ Suc k $ 0) ^ Suc k = a ^ Suc k $ 0"
    using ak0 by auto
  from r0 ak0 have th1: "r (Suc k) (a ^ Suc k $ 0) = a $ 0"
    by auto
  from ak0 a0 have ak00: "?ak $ 0 \<noteq>0 "
    by auto
  from radical_unique[of r k ?ak a, OF th0 th1 ak00] show ?thesis
    by metis
qed

lemma fps_deriv_radical:
  fixes a :: "'a::field_char_0 fps"
  assumes r0: "(r (Suc k) (a$0)) ^ Suc k = a$0"
    and a0: "a$0 \<noteq> 0"
  shows "fps_deriv (fps_radical r (Suc k) a) =
    fps_deriv a / (fps_const (of_nat (Suc k)) * (fps_radical r (Suc k) a) ^ k)"
proof -
  let ?r = "fps_radical r (Suc k) a"
  let ?w = "(fps_const (of_nat (Suc k)) * ?r ^ k)"
  from a0 r0 have r0': "r (Suc k) (a$0) \<noteq> 0"
    by auto
  from r0' have w0: "?w $ 0 \<noteq> 0"
    by (simp del: of_nat_Suc)
  note th0 = inverse_mult_eq_1[OF w0]
  let ?iw = "inverse ?w"
  from iffD1[OF power_radical[of a r], OF a0 r0]
  have "fps_deriv (?r ^ Suc k) = fps_deriv a"
    by simp
  then have "fps_deriv ?r * ?w = fps_deriv a"
    by (simp add: fps_deriv_power ac_simps del: power_Suc)
  then have "?iw * fps_deriv ?r * ?w = ?iw * fps_deriv a"
    by simp
  with a0 r0 have "fps_deriv ?r * (?iw * ?w) = fps_deriv a / ?w"
    by (subst fps_divide_unit) (auto simp del: of_nat_Suc)
  then show ?thesis unfolding th0 by simp
qed

lemma radical_mult_distrib:
  fixes a :: "'a::field_char_0 fps"
  assumes k: "k > 0"
    and ra0: "r k (a $ 0) ^ k = a $ 0"
    and rb0: "r k (b $ 0) ^ k = b $ 0"
    and a0: "a $ 0 \<noteq> 0"
    and b0: "b $ 0 \<noteq> 0"
  shows "r k ((a * b) $ 0) = r k (a $ 0) * r k (b $ 0) \<longleftrightarrow>
    fps_radical r k (a * b) = fps_radical r k a * fps_radical r k b"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if r0': ?lhs
  proof -
    from r0' have r0: "(r k ((a * b) $ 0)) ^ k = (a * b) $ 0"
      by (simp add: fps_mult_nth ra0 rb0 power_mult_distrib)
    show ?thesis
    proof (cases k)
      case 0
      then show ?thesis using r0' by simp
    next
      case (Suc h)
      let ?ra = "fps_radical r (Suc h) a"
      let ?rb = "fps_radical r (Suc h) b"
      have th0: "r (Suc h) ((a * b) $ 0) = (fps_radical r (Suc h) a * fps_radical r (Suc h) b) $ 0"
        using r0' Suc by (simp add: fps_mult_nth)
      have ab0: "(a*b) $ 0 \<noteq> 0"
        using a0 b0 by (simp add: fps_mult_nth)
      from radical_unique[of r h "a*b" "fps_radical r (Suc h) a * fps_radical r (Suc h) b", OF r0[unfolded Suc] th0 ab0, symmetric]
        iffD1[OF power_radical[of _ r], OF a0 ra0[unfolded Suc]] iffD1[OF power_radical[of _ r], OF b0 rb0[unfolded Suc]] Suc r0'
      show ?thesis
        by (auto simp add: power_mult_distrib simp del: power_Suc)
    qed
  qed
  show ?lhs if ?rhs
  proof -
    from that have "(fps_radical r k (a * b)) $ 0 = (fps_radical r k a * fps_radical r k b) $ 0"
      by simp
    then show ?thesis
      using k by (simp add: fps_mult_nth)
  qed
qed

(*
lemma radical_mult_distrib:
  fixes a:: "'a::field_char_0 fps"
  assumes
  ra0: "r k (a $ 0) ^ k = a $ 0"
  and rb0: "r k (b $ 0) ^ k = b $ 0"
  and r0': "r k ((a * b) $ 0) = r k (a $ 0) * r k (b $ 0)"
  and a0: "a$0 \<noteq> 0"
  and b0: "b$0 \<noteq> 0"
  shows "fps_radical r (k) (a*b) = fps_radical r (k) a * fps_radical r (k) (b)"
proof-
  from r0' have r0: "(r (k) ((a*b)$0)) ^ k = (a*b)$0"
    by (simp add: fps_mult_nth ra0 rb0 power_mult_distrib)
  {assume "k=0" then have ?thesis by simp}
  moreover
  {fix h assume k: "k = Suc h"
  let ?ra = "fps_radical r (Suc h) a"
  let ?rb = "fps_radical r (Suc h) b"
  have th0: "r (Suc h) ((a * b) $ 0) = (fps_radical r (Suc h) a * fps_radical r (Suc h) b) $ 0"
    using r0' k by (simp add: fps_mult_nth)
  have ab0: "(a*b) $ 0 \<noteq> 0" using a0 b0 by (simp add: fps_mult_nth)
  from radical_unique[of r h "a*b" "fps_radical r (Suc h) a * fps_radical r (Suc h) b", OF r0[unfolded k] th0 ab0, symmetric]
    power_radical[of r, OF ra0[unfolded k] a0] power_radical[of r, OF rb0[unfolded k] b0] k
  have ?thesis by (auto simp add: power_mult_distrib simp del: power_Suc)}
ultimately show ?thesis by (cases k, auto)
qed
*)

lemma fps_divide_1 [simp]: "(a :: 'a::field fps) / 1 = a"
  by (fact div_by_1)

lemma radical_divide:
  fixes a :: "'a::field_char_0 fps"
  assumes kp: "k > 0"
    and ra0: "(r k (a $ 0)) ^ k = a $ 0"
    and rb0: "(r k (b $ 0)) ^ k = b $ 0"
    and a0: "a$0 \<noteq> 0"
    and b0: "b$0 \<noteq> 0"
  shows "r k ((a $ 0) / (b$0)) = r k (a$0) / r k (b $ 0) \<longleftrightarrow>
    fps_radical r k (a/b) = fps_radical r k a / fps_radical r k b"
  (is "?lhs = ?rhs")
proof
  let ?r = "fps_radical r k"
  from kp obtain h where k: "k = Suc h"
    by (cases k) auto
  have ra0': "r k (a$0) \<noteq> 0" using a0 ra0 k by auto
  have rb0': "r k (b$0) \<noteq> 0" using b0 rb0 k by auto

  show ?lhs if ?rhs
  proof -
    from that have "?r (a/b) $ 0 = (?r a / ?r b)$0"
      by simp
    then show ?thesis
      using k a0 b0 rb0' by (simp add: fps_divide_unit fps_mult_nth fps_inverse_def divide_inverse)
  qed
  show ?rhs if ?lhs
  proof -
    from a0 b0 have ab0[simp]: "(a/b)$0 = a$0 / b$0"
      by (simp add: fps_divide_def fps_mult_nth divide_inverse fps_inverse_def)
    have th0: "r k ((a/b)$0) ^ k = (a/b)$0"
      by (simp add: \<open>?lhs\<close> power_divide ra0 rb0)
    from a0 b0 ra0' rb0' kp \<open>?lhs\<close>
    have th1: "r k ((a / b) $ 0) = (fps_radical r k a / fps_radical r k b) $ 0"
      by (simp add: fps_divide_unit fps_mult_nth fps_inverse_def divide_inverse)
    from a0 b0 ra0' rb0' kp have ab0': "(a / b) $ 0 \<noteq> 0"
      by (simp add: fps_divide_unit fps_mult_nth fps_inverse_def nonzero_imp_inverse_nonzero)
    note tha[simp] = iffD1[OF power_radical[where r=r and k=h], OF a0 ra0[unfolded k], unfolded k[symmetric]]
    note thb[simp] = iffD1[OF power_radical[where r=r and k=h], OF b0 rb0[unfolded k], unfolded k[symmetric]]
    from b0 rb0' have th2: "(?r a / ?r b)^k = a/b"
      by (simp add: fps_divide_unit power_mult_distrib fps_inverse_power[symmetric])

    from iffD1[OF radical_unique[where r=r and a="?r a / ?r b" and b="a/b" and k=h], symmetric, unfolded k[symmetric], OF th0 th1 ab0' th2]
    show ?thesis .
  qed
qed

lemma radical_inverse:
  fixes a :: "'a::field_char_0 fps"
  assumes k: "k > 0"
    and ra0: "r k (a $ 0) ^ k = a $ 0"
    and r1: "(r k 1)^k = 1"
    and a0: "a$0 \<noteq> 0"
  shows "r k (inverse (a $ 0)) = r k 1 / (r k (a $ 0)) \<longleftrightarrow>
    fps_radical r k (inverse a) = fps_radical r k 1 / fps_radical r k a"
  using radical_divide[where k=k and r=r and a=1 and b=a, OF k ] ra0 r1 a0
  by (simp add: divide_inverse fps_divide_def)


subsection \<open>Derivative of composition\<close>

lemma fps_compose_deriv:
  fixes a :: "'a::idom fps"
  assumes b0: "b$0 = 0"
  shows "fps_deriv (a oo b) = ((fps_deriv a) oo b) * fps_deriv b"
proof -
  have "(fps_deriv (a oo b))$n = (((fps_deriv a) oo b) * (fps_deriv b)) $n" for n
  proof -
    have "(fps_deriv (a oo b))$n = sum (\<lambda>i. a $ i * (fps_deriv (b^i))$n) {0.. Suc n}"
      by (simp add: fps_compose_def field_simps sum_distrib_left del: of_nat_Suc)
    also have "\<dots> = sum (\<lambda>i. a$i * ((fps_const (of_nat i)) * (fps_deriv b * (b^(i - 1))))$n) {0.. Suc n}"
      by (simp add: field_simps fps_deriv_power del: fps_mult_left_const_nth of_nat_Suc)
    also have "\<dots> = sum (\<lambda>i. of_nat i * a$i * (((b^(i - 1)) * fps_deriv b))$n) {0.. Suc n}"
      unfolding fps_mult_left_const_nth  by (simp add: field_simps)
    also have "\<dots> = sum (\<lambda>i. of_nat i * a$i * (sum (\<lambda>j. (b^ (i - 1))$j * (fps_deriv b)$(n - j)) {0..n})) {0.. Suc n}"
      unfolding fps_mult_nth ..
    also have "\<dots> = sum (\<lambda>i. of_nat i * a$i * (sum (\<lambda>j. (b^ (i - 1))$j * (fps_deriv b)$(n - j)) {0..n})) {1.. Suc n}"
      apply (rule sum.mono_neutral_right)
      apply (auto simp add: mult_delta_left sum.delta not_le)
      done
    also have "\<dots> = sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
      unfolding fps_deriv_nth
      by (rule sum.reindex_cong [of Suc]) (auto simp add: mult.assoc)
    finally have th0: "(fps_deriv (a oo b))$n =
      sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}" .

    have "(((fps_deriv a) oo b) * (fps_deriv b))$n = sum (\<lambda>i. (fps_deriv b)$ (n - i) * ((fps_deriv a) oo b)$i) {0..n}"
      unfolding fps_mult_nth by (simp add: ac_simps)
    also have "\<dots> = sum (\<lambda>i. sum (\<lambda>j. of_nat (n - i +1) * b$(n - i + 1) * of_nat (j + 1) * a$(j+1) * (b^j)$i) {0..n}) {0..n}"
      unfolding fps_deriv_nth fps_compose_nth sum_distrib_left mult.assoc
      apply (rule sum.cong)
      apply (rule refl)
      apply (rule sum.mono_neutral_left)
      apply (simp_all add: subset_eq)
      apply clarify
      apply (subgoal_tac "b^i$x = 0")
      apply simp
      apply (rule startsby_zero_power_prefix[OF b0, rule_format])
      apply simp
      done
    also have "\<dots> = sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
      unfolding sum_distrib_left
      apply (subst sum.commute)
      apply (rule sum.cong, rule refl)+
      apply simp
      done
    finally show ?thesis
      unfolding th0 by simp
  qed
  then show ?thesis by (simp add: fps_eq_iff)
qed

lemma fps_mult_fps_X_plus_1_nth:
  "((1+fps_X)*a) $n = (if n = 0 then (a$n :: 'a::comm_ring_1) else a$n + a$(n - 1))"
proof (cases n)
  case 0
  then show ?thesis
    by (simp add: fps_mult_nth)
next
  case (Suc m)
  have "((1 + fps_X)*a) $ n = sum (\<lambda>i. (1 + fps_X) $ i * a $ (n - i)) {0..n}"
    by (simp add: fps_mult_nth)
  also have "\<dots> = sum (\<lambda>i. (1+fps_X)$i * a$(n-i)) {0.. 1}"
    unfolding Suc by (rule sum.mono_neutral_right) auto
  also have "\<dots> = (if n = 0 then (a$n :: 'a::comm_ring_1) else a$n + a$(n - 1))"
    by (simp add: Suc)
  finally show ?thesis .
qed


subsection \<open>Finite FPS (i.e. polynomials) and fps_X\<close>

lemma fps_poly_sum_fps_X:
  assumes "\<forall>i > n. a$i = (0::'a::comm_ring_1)"
  shows "a = sum (\<lambda>i. fps_const (a$i) * fps_X^i) {0..n}" (is "a = ?r")
proof -
  have "a$i = ?r$i" for i
    unfolding fps_sum_nth fps_mult_left_const_nth fps_X_power_nth
    by (simp add: mult_delta_right sum.delta' assms)
  then show ?thesis
    unfolding fps_eq_iff by blast
qed


subsection \<open>Compositional inverses\<close>

fun compinv :: "'a fps \<Rightarrow> nat \<Rightarrow> 'a::field"
where
  "compinv a 0 = fps_X$0"
| "compinv a (Suc n) =
    (fps_X$ Suc n - sum (\<lambda>i. (compinv a i) * (a^i)$Suc n) {0 .. n}) / (a$1) ^ Suc n"

definition "fps_inv a = Abs_fps (compinv a)"

lemma fps_inv:
  assumes a0: "a$0 = 0"
    and a1: "a$1 \<noteq> 0"
  shows "fps_inv a oo a = fps_X"
proof -
  let ?i = "fps_inv a oo a"
  have "?i $n = fps_X$n" for n
  proof (induct n rule: nat_less_induct)
    fix n
    assume h: "\<forall>m<n. ?i$m = fps_X$m"
    show "?i $ n = fps_X$n"
    proof (cases n)
      case 0
      then show ?thesis using a0
        by (simp add: fps_compose_nth fps_inv_def)
    next
      case (Suc n1)
      have "?i $ n = sum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1} + fps_inv a $ Suc n1 * (a $ 1)^ Suc n1"
        by (simp only: fps_compose_nth) (simp add: Suc startsby_zero_power_nth_same [OF a0] del: power_Suc)
      also have "\<dots> = sum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1} +
        (fps_X$ Suc n1 - sum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1})"
        using a0 a1 Suc by (simp add: fps_inv_def)
      also have "\<dots> = fps_X$n" using Suc by simp
      finally show ?thesis .
    qed
  qed
  then show ?thesis
    by (simp add: fps_eq_iff)
qed


fun gcompinv :: "'a fps \<Rightarrow> 'a fps \<Rightarrow> nat \<Rightarrow> 'a::field"
where
  "gcompinv b a 0 = b$0"
| "gcompinv b a (Suc n) =
    (b$ Suc n - sum (\<lambda>i. (gcompinv b a i) * (a^i)$Suc n) {0 .. n}) / (a$1) ^ Suc n"

definition "fps_ginv b a = Abs_fps (gcompinv b a)"

lemma fps_ginv:
  assumes a0: "a$0 = 0"
    and a1: "a$1 \<noteq> 0"
  shows "fps_ginv b a oo a = b"
proof -
  let ?i = "fps_ginv b a oo a"
  have "?i $n = b$n" for n
  proof (induct n rule: nat_less_induct)
    fix n
    assume h: "\<forall>m<n. ?i$m = b$m"
    show "?i $ n = b$n"
    proof (cases n)
      case 0
      then show ?thesis using a0
        by (simp add: fps_compose_nth fps_ginv_def)
    next
      case (Suc n1)
      have "?i $ n = sum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1} + fps_ginv b a $ Suc n1 * (a $ 1)^ Suc n1"
        by (simp only: fps_compose_nth) (simp add: Suc startsby_zero_power_nth_same [OF a0] del: power_Suc)
      also have "\<dots> = sum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1} +
        (b$ Suc n1 - sum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1})"
        using a0 a1 Suc by (simp add: fps_ginv_def)
      also have "\<dots> = b$n" using Suc by simp
      finally show ?thesis .
    qed
  qed
  then show ?thesis
    by (simp add: fps_eq_iff)
qed

lemma fps_inv_ginv: "fps_inv = fps_ginv fps_X"
  apply (auto simp add: fun_eq_iff fps_eq_iff fps_inv_def fps_ginv_def)
  apply (induct_tac n rule: nat_less_induct)
  apply auto
  apply (case_tac na)
  apply simp
  apply simp
  done

lemma fps_compose_1[simp]: "1 oo a = 1"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left sum.delta)

lemma fps_compose_0[simp]: "0 oo a = 0"
  by (simp add: fps_eq_iff fps_compose_nth)

lemma fps_compose_0_right[simp]: "a oo 0 = fps_const (a $ 0)"
  by (auto simp add: fps_eq_iff fps_compose_nth power_0_left sum.neutral)

lemma fps_compose_add_distrib: "(a + b) oo c = (a oo c) + (b oo c)"
  by (simp add: fps_eq_iff fps_compose_nth field_simps sum.distrib)

lemma fps_compose_sum_distrib: "(sum f S) oo a = sum (\<lambda>i. f i oo a) S"
proof (cases "finite S")
  case True
  show ?thesis
  proof (rule finite_induct[OF True])
    show "sum f {} oo a = (\<Sum>i\<in>{}. f i oo a)"
      by simp
  next
    fix x F
    assume fF: "finite F"
      and xF: "x \<notin> F"
      and h: "sum f F oo a = sum (\<lambda>i. f i oo a) F"
    show "sum f (insert x F) oo a  = sum (\<lambda>i. f i oo a) (insert x F)"
      using fF xF h by (simp add: fps_compose_add_distrib)
  qed
next
  case False
  then show ?thesis by simp
qed

lemma convolution_eq:
  "sum (\<lambda>i. a (i :: nat) * b (n - i)) {0 .. n} =
    sum (\<lambda>(i,j). a i * b j) {(i,j). i \<le> n \<and> j \<le> n \<and> i + j = n}"
  by (rule sum.reindex_bij_witness[where i=fst and j="\<lambda>i. (i, n - i)"]) auto

lemma product_composition_lemma:
  assumes c0: "c$0 = (0::'a::idom)"
    and d0: "d$0 = 0"
  shows "((a oo c) * (b oo d))$n =
    sum (\<lambda>(k,m). a$k * b$m * (c^k * d^m) $ n) {(k,m). k + m \<le> n}"  (is "?l = ?r")
proof -
  let ?S = "{(k::nat, m::nat). k + m \<le> n}"
  have s: "?S \<subseteq> {0..n} \<times> {0..n}" by (auto simp add: subset_eq)
  have f: "finite {(k::nat, m::nat). k + m \<le> n}"
    apply (rule finite_subset[OF s])
    apply auto
    done
  have "?r =  sum (\<lambda>i. sum (\<lambda>(k,m). a$k * (c^k)$i * b$m * (d^m) $ (n - i)) {(k,m). k + m \<le> n}) {0..n}"
    apply (simp add: fps_mult_nth sum_distrib_left)
    apply (subst sum.commute)
    apply (rule sum.cong)
    apply (auto simp add: field_simps)
    done
  also have "\<dots> = ?l"
    apply (simp add: fps_mult_nth fps_compose_nth sum_product)
    apply (rule sum.cong)
    apply (rule refl)
    apply (simp add: sum.cartesian_product mult.assoc)
    apply (rule sum.mono_neutral_right[OF f])
    apply (simp add: subset_eq)
    apply presburger
    apply clarsimp
    apply (rule ccontr)
    apply (clarsimp simp add: not_le)
    apply (case_tac "x < aa")
    apply simp
    apply (frule_tac startsby_zero_power_prefix[rule_format, OF c0])
    apply blast
    apply simp
    apply (frule_tac startsby_zero_power_prefix[rule_format, OF d0])
    apply blast
    done
  finally show ?thesis by simp
qed

lemma product_composition_lemma':
  assumes c0: "c$0 = (0::'a::idom)"
    and d0: "d$0 = 0"
  shows "((a oo c) * (b oo d))$n =
    sum (\<lambda>k. sum (\<lambda>m. a$k * b$m * (c^k * d^m) $ n) {0..n}) {0..n}"  (is "?l = ?r")
  unfolding product_composition_lemma[OF c0 d0]
  unfolding sum.cartesian_product
  apply (rule sum.mono_neutral_left)
  apply simp
  apply (clarsimp simp add: subset_eq)
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "(c^aa * d^ba) $ n = 0")
  apply simp
  unfolding fps_mult_nth
  apply (rule sum.neutral)
  apply (clarsimp simp add: not_le)
  apply (case_tac "x < aa")
  apply (rule startsby_zero_power_prefix[OF c0, rule_format])
  apply simp
  apply (subgoal_tac "n - x < ba")
  apply (frule_tac k = "ba" in startsby_zero_power_prefix[OF d0, rule_format])
  apply simp
  apply arith
  done


lemma sum_pair_less_iff:
  "sum (\<lambda>((k::nat),m). a k * b m * c (k + m)) {(k,m). k + m \<le> n} =
    sum (\<lambda>s. sum (\<lambda>i. a i * b (s - i) * c s) {0..s}) {0..n}"
  (is "?l = ?r")
proof -
  let ?KM = "{(k,m). k + m \<le> n}"
  let ?f = "\<lambda>s. UNION {(0::nat)..s} (\<lambda>i. {(i,s - i)})"
  have th0: "?KM = UNION {0..n} ?f"
    by auto
  show "?l = ?r "
    unfolding th0
    apply (subst sum.UNION_disjoint)
    apply auto
    apply (subst sum.UNION_disjoint)
    apply auto
    done
qed

lemma fps_compose_mult_distrib_lemma:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "((a oo c) * (b oo c))$n = sum (\<lambda>s. sum (\<lambda>i. a$i * b$(s - i) * (c^s) $ n) {0..s}) {0..n}"
  unfolding product_composition_lemma[OF c0 c0] power_add[symmetric]
  unfolding sum_pair_less_iff[where a = "\<lambda>k. a$k" and b="\<lambda>m. b$m" and c="\<lambda>s. (c ^ s)$n" and n = n] ..

lemma fps_compose_mult_distrib:
  assumes c0: "c $ 0 = (0::'a::idom)"
  shows "(a * b) oo c = (a oo c) * (b oo c)"
  apply (simp add: fps_eq_iff fps_compose_mult_distrib_lemma [OF c0])
  apply (simp add: fps_compose_nth fps_mult_nth sum_distrib_right)
  done

lemma fps_compose_prod_distrib:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "prod a S oo c = prod (\<lambda>k. a k oo c) S"
  apply (cases "finite S")
  apply simp_all
  apply (induct S rule: finite_induct)
  apply simp
  apply (simp add: fps_compose_mult_distrib[OF c0])
  done

lemma fps_compose_divide:
  assumes [simp]: "g dvd f" "h $ 0 = 0"
  shows   "fps_compose f h = fps_compose (f / g :: 'a :: field fps) h * fps_compose g h"
proof -
  have "f = (f / g) * g" by simp
  also have "fps_compose \<dots> h = fps_compose (f / g) h * fps_compose g h"
    by (subst fps_compose_mult_distrib) simp_all
  finally show ?thesis .
qed

lemma fps_compose_divide_distrib:
  assumes "g dvd f" "h $ 0 = 0" "fps_compose g h \<noteq> 0"
  shows   "fps_compose (f / g :: 'a :: field fps) h = fps_compose f h / fps_compose g h"
  using fps_compose_divide[OF assms(1,2)] assms(3) by simp

lemma fps_compose_power:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "(a oo c)^n = a^n oo c"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  have th0: "a^n = prod (\<lambda>k. a) {0..m}" "(a oo c) ^ n = prod (\<lambda>k. a oo c) {0..m}"
    by (simp_all add: prod_constant Suc)
  then show ?thesis
    by (simp add: fps_compose_prod_distrib[OF c0])
qed

lemma fps_compose_uminus: "- (a::'a::ring_1 fps) oo c = - (a oo c)"
  by (simp add: fps_eq_iff fps_compose_nth field_simps sum_negf[symmetric])
    
lemma fps_compose_sub_distrib: "(a - b) oo (c::'a::ring_1 fps) = (a oo c) - (b oo c)"
  using fps_compose_add_distrib [of a "- b" c] by (simp add: fps_compose_uminus)

lemma fps_X_fps_compose: "fps_X oo a = Abs_fps (\<lambda>n. if n = 0 then (0::'a::comm_ring_1) else a$n)"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left sum.delta)

lemma fps_inverse_compose:
  assumes b0: "(b$0 :: 'a::field) = 0"
    and a0: "a$0 \<noteq> 0"
  shows "inverse a oo b = inverse (a oo b)"
proof -
  let ?ia = "inverse a"
  let ?ab = "a oo b"
  let ?iab = "inverse ?ab"

  from a0 have ia0: "?ia $ 0 \<noteq> 0" by simp
  from a0 have ab0: "?ab $ 0 \<noteq> 0" by (simp add: fps_compose_def)
  have "(?ia oo b) *  (a oo b) = 1"
    unfolding fps_compose_mult_distrib[OF b0, symmetric]
    unfolding inverse_mult_eq_1[OF a0]
    fps_compose_1 ..

  then have "(?ia oo b) *  (a oo b) * ?iab  = 1 * ?iab" by simp
  then have "(?ia oo b) *  (?iab * (a oo b))  = ?iab" by simp
  then show ?thesis unfolding inverse_mult_eq_1[OF ab0] by simp
qed

lemma fps_divide_compose:
  assumes c0: "(c$0 :: 'a::field) = 0"
    and b0: "b$0 \<noteq> 0"
  shows "(a/b) oo c = (a oo c) / (b oo c)"
    using b0 c0 by (simp add: fps_divide_unit fps_inverse_compose fps_compose_mult_distrib)

lemma gp:
  assumes a0: "a$0 = (0::'a::field)"
  shows "(Abs_fps (\<lambda>n. 1)) oo a = 1/(1 - a)"
    (is "?one oo a = _")
proof -
  have o0: "?one $ 0 \<noteq> 0" by simp
  have th0: "(1 - fps_X) $ 0 \<noteq> (0::'a)" by simp
  from fps_inverse_gp[where ?'a = 'a]
  have "inverse ?one = 1 - fps_X" by (simp add: fps_eq_iff)
  then have "inverse (inverse ?one) = inverse (1 - fps_X)" by simp
  then have th: "?one = 1/(1 - fps_X)" unfolding fps_inverse_idempotent[OF o0]
    by (simp add: fps_divide_def)
  show ?thesis
    unfolding th
    unfolding fps_divide_compose[OF a0 th0]
    fps_compose_1 fps_compose_sub_distrib fps_X_fps_compose_startby0[OF a0] ..
qed

lemma fps_const_power [simp]: "fps_const (c::'a::ring_1) ^ n = fps_const (c^n)"
  by (induct n) auto

lemma fps_compose_radical:
  assumes b0: "b$0 = (0::'a::field_char_0)"
    and ra0: "r (Suc k) (a$0) ^ Suc k = a$0"
    and a0: "a$0 \<noteq> 0"
  shows "fps_radical r (Suc k)  a oo b = fps_radical r (Suc k) (a oo b)"
proof -
  let ?r = "fps_radical r (Suc k)"
  let ?ab = "a oo b"
  have ab0: "?ab $ 0 = a$0"
    by (simp add: fps_compose_def)
  from ab0 a0 ra0 have rab0: "?ab $ 0 \<noteq> 0" "r (Suc k) (?ab $ 0) ^ Suc k = ?ab $ 0"
    by simp_all
  have th00: "r (Suc k) ((a oo b) $ 0) = (fps_radical r (Suc k) a oo b) $ 0"
    by (simp add: ab0 fps_compose_def)
  have th0: "(?r a oo b) ^ (Suc k) = a  oo b"
    unfolding fps_compose_power[OF b0]
    unfolding iffD1[OF power_radical[of a r k], OF a0 ra0]  ..
  from iffD1[OF radical_unique[where r=r and k=k and b= ?ab and a = "?r a oo b", OF rab0(2) th00 rab0(1)], OF th0]
  show ?thesis  .
qed

lemma fps_const_mult_apply_left: "fps_const c * (a oo b) = (fps_const c * a) oo b"
  by (simp add: fps_eq_iff fps_compose_nth sum_distrib_left mult.assoc)

lemma fps_const_mult_apply_right:
  "(a oo b) * fps_const (c::'a::comm_semiring_1) = (fps_const c * a) oo b"
  by (auto simp add: fps_const_mult_apply_left mult.commute)

lemma fps_compose_assoc:
  assumes c0: "c$0 = (0::'a::idom)"
    and b0: "b$0 = 0"
  shows "a oo (b oo c) = a oo b oo c" (is "?l = ?r")
proof -
  have "?l$n = ?r$n" for n
  proof -
    have "?l$n = (sum (\<lambda>i. (fps_const (a$i) * b^i) oo c) {0..n})$n"
      by (simp add: fps_compose_nth fps_compose_power[OF c0] fps_const_mult_apply_left
        sum_distrib_left mult.assoc fps_sum_nth)
    also have "\<dots> = ((sum (\<lambda>i. fps_const (a$i) * b^i) {0..n}) oo c)$n"
      by (simp add: fps_compose_sum_distrib)
    also have "\<dots> = ?r$n"
      apply (simp add: fps_compose_nth fps_sum_nth sum_distrib_right mult.assoc)
      apply (rule sum.cong)
      apply (rule refl)
      apply (rule sum.mono_neutral_right)
      apply (auto simp add: not_le)
      apply (erule startsby_zero_power_prefix[OF b0, rule_format])
      done
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: fps_eq_iff)
qed


lemma fps_X_power_compose:
  assumes a0: "a$0=0"
  shows "fps_X^k oo a = (a::'a::idom fps)^k"
  (is "?l = ?r")
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have "?l $ n = ?r $n" for n
  proof -
    consider "k > n" | "k \<le> n" by arith
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using a0 startsby_zero_power_prefix[OF a0] Suc
        by (simp add: fps_compose_nth del: power_Suc)
    next
      case 2
      then show ?thesis
        by (simp add: fps_compose_nth mult_delta_left sum.delta)
    qed
  qed
  then show ?thesis
    unfolding fps_eq_iff by blast
qed

lemma fps_inv_right:
  assumes a0: "a$0 = 0"
    and a1: "a$1 \<noteq> 0"
  shows "a oo fps_inv a = fps_X"
proof -
  let ?ia = "fps_inv a"
  let ?iaa = "a oo fps_inv a"
  have th0: "?ia $ 0 = 0"
    by (simp add: fps_inv_def)
  have th1: "?iaa $ 0 = 0"
    using a0 a1 by (simp add: fps_inv_def fps_compose_nth)
  have th2: "fps_X$0 = 0"
    by simp
  from fps_inv[OF a0 a1] have "a oo (fps_inv a oo a) = a oo fps_X"
    by simp
  then have "(a oo fps_inv a) oo a = fps_X oo a"
    by (simp add: fps_compose_assoc[OF a0 th0] fps_X_fps_compose_startby0[OF a0])
  with fps_compose_inj_right[OF a0 a1] show ?thesis
    by simp
qed

lemma fps_inv_deriv:
  assumes a0: "a$0 = (0::'a::field)"
    and a1: "a$1 \<noteq> 0"
  shows "fps_deriv (fps_inv a) = inverse (fps_deriv a oo fps_inv a)"
proof -
  let ?ia = "fps_inv a"
  let ?d = "fps_deriv a oo ?ia"
  let ?dia = "fps_deriv ?ia"
  have ia0: "?ia$0 = 0"
    by (simp add: fps_inv_def)
  have th0: "?d$0 \<noteq> 0"
    using a1 by (simp add: fps_compose_nth)
  from fps_inv_right[OF a0 a1] have "?d * ?dia = 1"
    by (simp add: fps_compose_deriv[OF ia0, of a, symmetric] )
  then have "inverse ?d * ?d * ?dia = inverse ?d * 1"
    by simp
  with inverse_mult_eq_1 [OF th0] show "?dia = inverse ?d"
    by simp
qed

lemma fps_inv_idempotent:
  assumes a0: "a$0 = 0"
    and a1: "a$1 \<noteq> 0"
  shows "fps_inv (fps_inv a) = a"
proof -
  let ?r = "fps_inv"
  have ra0: "?r a $ 0 = 0"
    by (simp add: fps_inv_def)
  from a1 have ra1: "?r a $ 1 \<noteq> 0"
    by (simp add: fps_inv_def field_simps)
  have fps_X0: "fps_X$0 = 0"
    by simp
  from fps_inv[OF ra0 ra1] have "?r (?r a) oo ?r a = fps_X" .
  then have "?r (?r a) oo ?r a oo a = fps_X oo a"
    by simp
  then have "?r (?r a) oo (?r a oo a) = a"
    unfolding fps_X_fps_compose_startby0[OF a0]
    unfolding fps_compose_assoc[OF a0 ra0, symmetric] .
  then show ?thesis
    unfolding fps_inv[OF a0 a1] by simp
qed

lemma fps_ginv_ginv:
  assumes a0: "a$0 = 0"
    and a1: "a$1 \<noteq> 0"
    and c0: "c$0 = 0"
    and  c1: "c$1 \<noteq> 0"
  shows "fps_ginv b (fps_ginv c a) = b oo a oo fps_inv c"
proof -
  let ?r = "fps_ginv"
  from c0 have rca0: "?r c a $0 = 0"
    by (simp add: fps_ginv_def)
  from a1 c1 have rca1: "?r c a $ 1 \<noteq> 0"
    by (simp add: fps_ginv_def field_simps)
  from fps_ginv[OF rca0 rca1]
  have "?r b (?r c a) oo ?r c a = b" .
  then have "?r b (?r c a) oo ?r c a oo a = b oo a"
    by simp
  then have "?r b (?r c a) oo (?r c a oo a) = b oo a"
    apply (subst fps_compose_assoc)
    using a0 c0
    apply (auto simp add: fps_ginv_def)
    done
  then have "?r b (?r c a) oo c = b oo a"
    unfolding fps_ginv[OF a0 a1] .
  then have "?r b (?r c a) oo c oo fps_inv c= b oo a oo fps_inv c"
    by simp
  then have "?r b (?r c a) oo (c oo fps_inv c) = b oo a oo fps_inv c"
    apply (subst fps_compose_assoc)
    using a0 c0
    apply (auto simp add: fps_inv_def)
    done
  then show ?thesis
    unfolding fps_inv_right[OF c0 c1] by simp
qed

lemma fps_ginv_deriv:
  assumes a0:"a$0 = (0::'a::field)"
    and a1: "a$1 \<noteq> 0"
  shows "fps_deriv (fps_ginv b a) = (fps_deriv b / fps_deriv a) oo fps_ginv fps_X a"
proof -
  let ?ia = "fps_ginv b a"
  let ?ifps_Xa = "fps_ginv fps_X a"
  let ?d = "fps_deriv"
  let ?dia = "?d ?ia"
  have ifps_Xa0: "?ifps_Xa $ 0 = 0"
    by (simp add: fps_ginv_def)
  have da0: "?d a $ 0 \<noteq> 0"
    using a1 by simp
  from fps_ginv[OF a0 a1, of b] have "?d (?ia oo a) = fps_deriv b"
    by simp
  then have "(?d ?ia oo a) * ?d a = ?d b"
    unfolding fps_compose_deriv[OF a0] .
  then have "(?d ?ia oo a) * ?d a * inverse (?d a) = ?d b * inverse (?d a)"
    by simp
  with a1 have "(?d ?ia oo a) * (inverse (?d a) * ?d a) = ?d b / ?d a"
    by (simp add: fps_divide_unit)
  then have "(?d ?ia oo a) oo ?ifps_Xa =  (?d b / ?d a) oo ?ifps_Xa"
    unfolding inverse_mult_eq_1[OF da0] by simp
  then have "?d ?ia oo (a oo ?ifps_Xa) =  (?d b / ?d a) oo ?ifps_Xa"
    unfolding fps_compose_assoc[OF ifps_Xa0 a0] .
  then show ?thesis unfolding fps_inv_ginv[symmetric]
    unfolding fps_inv_right[OF a0 a1] by simp
qed

lemma fps_compose_linear:
  "fps_compose (f :: 'a :: comm_ring_1 fps) (fps_const c * fps_X) = Abs_fps (\<lambda>n. c^n * f $ n)"
  by (simp add: fps_eq_iff fps_compose_def power_mult_distrib
                if_distrib sum.delta' cong: if_cong)
              
lemma fps_compose_uminus': 
  "fps_compose f (-fps_X :: 'a :: comm_ring_1 fps) = Abs_fps (\<lambda>n. (-1)^n * f $ n)"
  using fps_compose_linear[of f "-1"] 
  by (simp only: fps_const_neg [symmetric] fps_const_1_eq_1) simp

subsection \<open>Elementary series\<close>

subsubsection \<open>Exponential series\<close>

definition "fps_exp x = Abs_fps (\<lambda>n. x^n / of_nat (fact n))"

lemma fps_exp_deriv[simp]: "fps_deriv (fps_exp a) = fps_const (a::'a::field_char_0) * fps_exp a" 
  (is "?l = ?r")
proof -
  have "?l$n = ?r $ n" for n
    apply (auto simp add: fps_exp_def field_simps power_Suc[symmetric]
      simp del: fact_Suc of_nat_Suc power_Suc)
    apply (simp add: field_simps)
    done
  then show ?thesis
    by (simp add: fps_eq_iff)
qed

lemma fps_exp_unique_ODE:
  "fps_deriv a = fps_const c * a \<longleftrightarrow> a = fps_const (a$0) * fps_exp (c::'a::field_char_0)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that have th: "\<And>n. a $ Suc n = c * a$n / of_nat (Suc n)"
      by (simp add: fps_deriv_def fps_eq_iff field_simps del: of_nat_Suc)
    have th': "a$n = a$0 * c ^ n/ (fact n)" for n
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case Suc
      then show ?case
        unfolding th
        using fact_gt_zero
        apply (simp add: field_simps del: of_nat_Suc fact_Suc)
        apply simp
        done
    qed
    show ?thesis
      by (auto simp add: fps_eq_iff fps_const_mult_left fps_exp_def intro: th')
  qed
  show ?lhs if ?rhs
    using that by (metis fps_exp_deriv fps_deriv_mult_const_left mult.left_commute)
qed

lemma fps_exp_add_mult: "fps_exp (a + b) = fps_exp (a::'a::field_char_0) * fps_exp b" (is "?l = ?r")
proof -
  have "fps_deriv ?r = fps_const (a + b) * ?r"
    by (simp add: fps_const_add[symmetric] field_simps del: fps_const_add)
  then have "?r = ?l"
    by (simp only: fps_exp_unique_ODE) (simp add: fps_mult_nth fps_exp_def)
  then show ?thesis ..
qed

lemma fps_exp_nth[simp]: "fps_exp a $ n = a^n / of_nat (fact n)"
  by (simp add: fps_exp_def)

lemma fps_exp_0[simp]: "fps_exp (0::'a::field) = 1"
  by (simp add: fps_eq_iff power_0_left)

lemma fps_exp_neg: "fps_exp (- a) = inverse (fps_exp (a::'a::field_char_0))"
proof -
  from fps_exp_add_mult[of a "- a"] have th0: "fps_exp a * fps_exp (- a) = 1" by simp
  from fps_inverse_unique[OF th0] show ?thesis by simp
qed

lemma fps_exp_nth_deriv[simp]: 
  "fps_nth_deriv n (fps_exp (a::'a::field_char_0)) = (fps_const a)^n * (fps_exp a)"
  by (induct n) auto

lemma fps_X_compose_fps_exp[simp]: "fps_X oo fps_exp (a::'a::field) = fps_exp a - 1"
  by (simp add: fps_eq_iff fps_X_fps_compose)

lemma fps_inv_fps_exp_compose:
  assumes a: "a \<noteq> 0"
  shows "fps_inv (fps_exp a - 1) oo (fps_exp a - 1) = fps_X"
    and "(fps_exp a - 1) oo fps_inv (fps_exp a - 1) = fps_X"
proof -
  let ?b = "fps_exp a - 1"
  have b0: "?b $ 0 = 0"
    by simp
  have b1: "?b $ 1 \<noteq> 0"
    by (simp add: a)
  from fps_inv[OF b0 b1] show "fps_inv (fps_exp a - 1) oo (fps_exp a - 1) = fps_X" .
  from fps_inv_right[OF b0 b1] show "(fps_exp a - 1) oo fps_inv (fps_exp a - 1) = fps_X" .
qed

lemma fps_exp_power_mult: "(fps_exp (c::'a::field_char_0))^n = fps_exp (of_nat n * c)"
  by (induct n) (auto simp add: field_simps fps_exp_add_mult)

lemma radical_fps_exp:
  assumes r: "r (Suc k) 1 = 1"
  shows "fps_radical r (Suc k) (fps_exp (c::'a::field_char_0)) = fps_exp (c / of_nat (Suc k))"
proof -
  let ?ck = "(c / of_nat (Suc k))"
  let ?r = "fps_radical r (Suc k)"
  have eq0[simp]: "?ck * of_nat (Suc k) = c" "of_nat (Suc k) * ?ck = c"
    by (simp_all del: of_nat_Suc)
  have th0: "fps_exp ?ck ^ (Suc k) = fps_exp c" unfolding fps_exp_power_mult eq0 ..
  have th: "r (Suc k) (fps_exp c $0) ^ Suc k = fps_exp c $ 0"
    "r (Suc k) (fps_exp c $ 0) = fps_exp ?ck $ 0" "fps_exp c $ 0 \<noteq> 0" using r by simp_all
  from th0 radical_unique[where r=r and k=k, OF th] show ?thesis
    by auto
qed

lemma fps_exp_compose_linear [simp]: 
  "fps_exp (d::'a::field_char_0) oo (fps_const c * fps_X) = fps_exp (c * d)"
  by (simp add: fps_compose_linear fps_exp_def fps_eq_iff power_mult_distrib)
  
lemma fps_fps_exp_compose_minus [simp]: 
  "fps_compose (fps_exp c) (-fps_X) = fps_exp (-c :: 'a :: field_char_0)"
  using fps_exp_compose_linear[of c "-1 :: 'a"] 
  unfolding fps_const_neg [symmetric] fps_const_1_eq_1 by simp

lemma fps_exp_eq_iff [simp]: "fps_exp c = fps_exp d \<longleftrightarrow> c = (d :: 'a :: field_char_0)"
proof
  assume "fps_exp c = fps_exp d"
  from arg_cong[of _ _ "\<lambda>F. F $ 1", OF this] show "c = d" by simp
qed simp_all

lemma fps_exp_eq_fps_const_iff [simp]: 
  "fps_exp (c :: 'a :: field_char_0) = fps_const c' \<longleftrightarrow> c = 0 \<and> c' = 1"
proof
  assume "c = 0 \<and> c' = 1"
  thus "fps_exp c = fps_const c'" by (auto simp: fps_eq_iff)
next
  assume "fps_exp c = fps_const c'"
  from arg_cong[of _ _ "\<lambda>F. F $ 1", OF this] arg_cong[of _ _ "\<lambda>F. F $ 0", OF this] 
    show "c = 0 \<and> c' = 1" by simp_all
qed

lemma fps_exp_neq_0 [simp]: "\<not>fps_exp (c :: 'a :: field_char_0) = 0"
  unfolding fps_const_0_eq_0 [symmetric] fps_exp_eq_fps_const_iff by simp  

lemma fps_exp_eq_1_iff [simp]: "fps_exp (c :: 'a :: field_char_0) = 1 \<longleftrightarrow> c = 0"
  unfolding fps_const_1_eq_1 [symmetric] fps_exp_eq_fps_const_iff by simp
    
lemma fps_exp_neq_numeral_iff [simp]: 
  "fps_exp (c :: 'a :: field_char_0) = numeral n \<longleftrightarrow> c = 0 \<and> n = Num.One"
  unfolding numeral_fps_const fps_exp_eq_fps_const_iff by simp


subsubsection \<open>Logarithmic series\<close>

lemma Abs_fps_if_0:
  "Abs_fps (\<lambda>n. if n = 0 then (v::'a::ring_1) else f n) =
    fps_const v + fps_X * Abs_fps (\<lambda>n. f (Suc n))"
  by (auto simp add: fps_eq_iff)

definition fps_ln :: "'a::field_char_0 \<Rightarrow> 'a fps"
  where "fps_ln c = fps_const (1/c) * Abs_fps (\<lambda>n. if n = 0 then 0 else (- 1) ^ (n - 1) / of_nat n)"

lemma fps_ln_deriv: "fps_deriv (fps_ln c) = fps_const (1/c) * inverse (1 + fps_X)"
  unfolding fps_inverse_fps_X_plus1
  by (simp add: fps_ln_def fps_eq_iff del: of_nat_Suc)

lemma fps_ln_nth: "fps_ln c $ n = (if n = 0 then 0 else 1/c * ((- 1) ^ (n - 1) / of_nat n))"
  by (simp add: fps_ln_def field_simps)

lemma fps_ln_0 [simp]: "fps_ln c $ 0 = 0" by (simp add: fps_ln_def)

lemma fps_ln_fps_exp_inv:
  fixes a :: "'a::field_char_0"
  assumes a: "a \<noteq> 0"
  shows "fps_ln a = fps_inv (fps_exp a - 1)"  (is "?l = ?r")
proof -
  let ?b = "fps_exp a - 1"
  have b0: "?b $ 0 = 0" by simp
  have b1: "?b $ 1 \<noteq> 0" by (simp add: a)
  have "fps_deriv (fps_exp a - 1) oo fps_inv (fps_exp a - 1) =
    (fps_const a * (fps_exp a - 1) + fps_const a) oo fps_inv (fps_exp a - 1)"
    by (simp add: field_simps)
  also have "\<dots> = fps_const a * (fps_X + 1)"
    apply (simp add: fps_compose_add_distrib fps_const_mult_apply_left[symmetric] fps_inv_right[OF b0 b1])
    apply (simp add: field_simps)
    done
  finally have eq: "fps_deriv (fps_exp a - 1) oo fps_inv (fps_exp a - 1) = fps_const a * (fps_X + 1)" .
  from fps_inv_deriv[OF b0 b1, unfolded eq]
  have "fps_deriv (fps_inv ?b) = fps_const (inverse a) / (fps_X + 1)"
    using a by (simp add: fps_const_inverse eq fps_divide_def fps_inverse_mult)
  then have "fps_deriv ?l = fps_deriv ?r"
    by (simp add: fps_ln_deriv add.commute fps_divide_def divide_inverse)
  then show ?thesis unfolding fps_deriv_eq_iff
    by (simp add: fps_ln_nth fps_inv_def)
qed

lemma fps_ln_mult_add:
  assumes c0: "c\<noteq>0"
    and d0: "d\<noteq>0"
  shows "fps_ln c + fps_ln d = fps_const (c+d) * fps_ln (c*d)"
  (is "?r = ?l")
proof-
  from c0 d0 have eq: "1/c + 1/d = (c+d)/(c*d)" by (simp add: field_simps)
  have "fps_deriv ?r = fps_const (1/c + 1/d) * inverse (1 + fps_X)"
    by (simp add: fps_ln_deriv fps_const_add[symmetric] algebra_simps del: fps_const_add)
  also have "\<dots> = fps_deriv ?l"
    apply (simp add: fps_ln_deriv)
    apply (simp add: fps_eq_iff eq)
    done
  finally show ?thesis
    unfolding fps_deriv_eq_iff by simp
qed

lemma fps_X_dvd_fps_ln [simp]: "fps_X dvd fps_ln c"
proof -
  have "fps_ln c = fps_X * Abs_fps (\<lambda>n. (-1) ^ n / (of_nat (Suc n) * c))"
    by (intro fps_ext) (auto simp: fps_ln_def of_nat_diff)
  thus ?thesis by simp
qed


subsubsection \<open>Binomial series\<close>

definition "fps_binomial a = Abs_fps (\<lambda>n. a gchoose n)"

lemma fps_binomial_nth[simp]: "fps_binomial a $ n = a gchoose n"
  by (simp add: fps_binomial_def)

lemma fps_binomial_ODE_unique:
  fixes c :: "'a::field_char_0"
  shows "fps_deriv a = (fps_const c * a) / (1 + fps_X) \<longleftrightarrow> a = fps_const (a$0) * fps_binomial c"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?da = "fps_deriv a"
  let ?x1 = "(1 + fps_X):: 'a fps"
  let ?l = "?x1 * ?da"
  let ?r = "fps_const c * a"

  have eq: "?l = ?r \<longleftrightarrow> ?lhs"
  proof -
    have x10: "?x1 $ 0 \<noteq> 0" by simp
    have "?l = ?r \<longleftrightarrow> inverse ?x1 * ?l = inverse ?x1 * ?r" by simp
    also have "\<dots> \<longleftrightarrow> ?da = (fps_const c * a) / ?x1"
      apply (simp only: fps_divide_def  mult.assoc[symmetric] inverse_mult_eq_1[OF x10])
      apply (simp add: field_simps)
      done
    finally show ?thesis .
  qed

  show ?rhs if ?lhs
  proof -
    from eq that have h: "?l = ?r" ..
    have th0: "a$ Suc n = ((c - of_nat n) / of_nat (Suc n)) * a $n" for n
    proof -
      from h have "?l $ n = ?r $ n" by simp
      then show ?thesis
        apply (simp add: field_simps del: of_nat_Suc)
        apply (cases n)
        apply (simp_all add: field_simps del: of_nat_Suc)
        done
    qed
    have th1: "a $ n = (c gchoose n) * a $ 0" for n
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc m)
      then show ?case
        unfolding th0
        apply (simp add: field_simps del: of_nat_Suc)
        unfolding mult.assoc[symmetric] gbinomial_mult_1
        apply (simp add: field_simps)
        done
    qed
    show ?thesis
      apply (simp add: fps_eq_iff)
      apply (subst th1)
      apply (simp add: field_simps)
      done
  qed

  show ?lhs if ?rhs
  proof -
    have th00: "x * (a $ 0 * y) = a $ 0 * (x * y)" for x y
      by (simp add: mult.commute)
    have "?l = ?r"
      apply (subst \<open>?rhs\<close>)
      apply (subst (2) \<open>?rhs\<close>)
      apply (clarsimp simp add: fps_eq_iff field_simps)
      unfolding mult.assoc[symmetric] th00 gbinomial_mult_1
      apply (simp add: field_simps gbinomial_mult_1)
      done
    with eq show ?thesis ..
  qed
qed

lemma fps_binomial_ODE_unique':
  "(fps_deriv a = fps_const c * a / (1 + fps_X) \<and> a $ 0 = 1) \<longleftrightarrow> (a = fps_binomial c)"
  by (subst fps_binomial_ODE_unique) auto

lemma fps_binomial_deriv: "fps_deriv (fps_binomial c) = fps_const c * fps_binomial c / (1 + fps_X)"
proof -
  let ?a = "fps_binomial c"
  have th0: "?a = fps_const (?a$0) * ?a" by (simp)
  from iffD2[OF fps_binomial_ODE_unique, OF th0] show ?thesis .
qed

lemma fps_binomial_add_mult: "fps_binomial (c+d) = fps_binomial c * fps_binomial d" (is "?l = ?r")
proof -
  let ?P = "?r - ?l"
  let ?b = "fps_binomial"
  let ?db = "\<lambda>x. fps_deriv (?b x)"
  have "fps_deriv ?P = ?db c * ?b d + ?b c * ?db d - ?db (c + d)"  by simp
  also have "\<dots> = inverse (1 + fps_X) *
      (fps_const c * ?b c * ?b d + fps_const d * ?b c * ?b d - fps_const (c+d) * ?b (c + d))"
    unfolding fps_binomial_deriv
    by (simp add: fps_divide_def field_simps)
  also have "\<dots> = (fps_const (c + d)/ (1 + fps_X)) * ?P"
    by (simp add: field_simps fps_divide_unit fps_const_add[symmetric] del: fps_const_add)
  finally have th0: "fps_deriv ?P = fps_const (c+d) * ?P / (1 + fps_X)"
    by (simp add: fps_divide_def)
  have "?P = fps_const (?P$0) * ?b (c + d)"
    unfolding fps_binomial_ODE_unique[symmetric]
    using th0 by simp
  then have "?P = 0" by (simp add: fps_mult_nth)
  then show ?thesis by simp
qed

lemma fps_binomial_minus_one: "fps_binomial (- 1) = inverse (1 + fps_X)"
  (is "?l = inverse ?r")
proof-
  have th: "?r$0 \<noteq> 0" by simp
  have th': "fps_deriv (inverse ?r) = fps_const (- 1) * inverse ?r / (1 + fps_X)"
    by (simp add: fps_inverse_deriv[OF th] fps_divide_def
      power2_eq_square mult.commute fps_const_neg[symmetric] del: fps_const_neg)
  have eq: "inverse ?r $ 0 = 1"
    by (simp add: fps_inverse_def)
  from iffD1[OF fps_binomial_ODE_unique[of "inverse (1 + fps_X)" "- 1"] th'] eq
  show ?thesis by (simp add: fps_inverse_def)
qed

lemma fps_binomial_of_nat: "fps_binomial (of_nat n) = (1 + fps_X :: 'a :: field_char_0 fps) ^ n"
proof (cases "n = 0")
  case [simp]: True
  have "fps_deriv ((1 + fps_X) ^ n :: 'a fps) = 0" by simp
  also have "\<dots> = fps_const (of_nat n) * (1 + fps_X) ^ n / (1 + fps_X)" by (simp add: fps_binomial_def)
  finally show ?thesis by (subst sym, subst fps_binomial_ODE_unique' [symmetric]) simp_all
next
  case False
  have "fps_deriv ((1 + fps_X) ^ n :: 'a fps) = fps_const (of_nat n) * (1 + fps_X) ^ (n - 1)"
    by (simp add: fps_deriv_power)
  also have "(1 + fps_X :: 'a fps) $ 0 \<noteq> 0" by simp
  hence "(1 + fps_X :: 'a fps) \<noteq> 0" by (intro notI) (simp only: , simp)
  with False have "(1 + fps_X :: 'a fps) ^ (n - 1) = (1 + fps_X) ^ n / (1 + fps_X)"
    by (cases n) (simp_all )
  also have "fps_const (of_nat n :: 'a) * ((1 + fps_X) ^ n / (1 + fps_X)) =
               fps_const (of_nat n) * (1 + fps_X) ^ n / (1 + fps_X)"
    by (simp add: unit_div_mult_swap)
  finally show ?thesis
    by (subst sym, subst fps_binomial_ODE_unique' [symmetric]) (simp_all add: fps_power_nth)
qed

lemma fps_binomial_0 [simp]: "fps_binomial 0 = 1"
  using fps_binomial_of_nat[of 0] by simp
  
lemma fps_binomial_power: "fps_binomial a ^ n = fps_binomial (of_nat n * a)"
  by (induction n) (simp_all add: fps_binomial_add_mult ring_distribs)

lemma fps_binomial_1: "fps_binomial 1 = 1 + fps_X"
  using fps_binomial_of_nat[of 1] by simp

lemma fps_binomial_minus_of_nat:
  "fps_binomial (- of_nat n) = inverse ((1 + fps_X :: 'a :: field_char_0 fps) ^ n)"
  by (rule sym, rule fps_inverse_unique)
     (simp add: fps_binomial_of_nat [symmetric] fps_binomial_add_mult [symmetric])

lemma one_minus_const_fps_X_power:
  "c \<noteq> 0 \<Longrightarrow> (1 - fps_const c * fps_X) ^ n =
     fps_compose (fps_binomial (of_nat n)) (-fps_const c * fps_X)"
  by (subst fps_binomial_of_nat)
     (simp add: fps_compose_power [symmetric] fps_compose_add_distrib fps_const_neg [symmetric] 
           del: fps_const_neg)

lemma one_minus_fps_X_const_neg_power:
  "inverse ((1 - fps_const c * fps_X) ^ n) = 
       fps_compose (fps_binomial (-of_nat n)) (-fps_const c * fps_X)"
proof (cases "c = 0")
  case False
  thus ?thesis
  by (subst fps_binomial_minus_of_nat)
     (simp add: fps_compose_power [symmetric] fps_inverse_compose fps_compose_add_distrib
                fps_const_neg [symmetric] del: fps_const_neg)
qed simp

lemma fps_X_plus_const_power:
  "c \<noteq> 0 \<Longrightarrow> (fps_X + fps_const c) ^ n =
     fps_const (c^n) * fps_compose (fps_binomial (of_nat n)) (fps_const (inverse c) * fps_X)"
  by (subst fps_binomial_of_nat)
     (simp add: fps_compose_power [symmetric] fps_binomial_of_nat fps_compose_add_distrib
                fps_const_power [symmetric] power_mult_distrib [symmetric] 
                algebra_simps inverse_mult_eq_1' del: fps_const_power)

lemma fps_X_plus_const_neg_power:
  "c \<noteq> 0 \<Longrightarrow> inverse ((fps_X + fps_const c) ^ n) =
     fps_const (inverse c^n) * fps_compose (fps_binomial (-of_nat n)) (fps_const (inverse c) * fps_X)"
  by (subst fps_binomial_minus_of_nat)
     (simp add: fps_compose_power [symmetric] fps_binomial_of_nat fps_compose_add_distrib
                fps_const_power [symmetric] power_mult_distrib [symmetric] fps_inverse_compose 
                algebra_simps fps_const_inverse [symmetric] fps_inverse_mult [symmetric]
                fps_inverse_power [symmetric] inverse_mult_eq_1'
           del: fps_const_power)


lemma one_minus_const_fps_X_neg_power':
  "n > 0 \<Longrightarrow> inverse ((1 - fps_const (c :: 'a :: field_char_0) * fps_X) ^ n) =
       Abs_fps (\<lambda>k. of_nat ((n + k - 1) choose k) * c^k)"
  apply (rule fps_ext)
  apply (subst one_minus_fps_X_const_neg_power, subst fps_const_neg, subst fps_compose_linear)
  apply (simp add: power_mult_distrib [symmetric] mult.assoc [symmetric] 
                   gbinomial_minus binomial_gbinomial of_nat_diff)
  done

text \<open>Vandermonde's Identity as a consequence.\<close>
lemma gbinomial_Vandermonde:
  "sum (\<lambda>k. (a gchoose k) * (b gchoose (n - k))) {0..n} = (a + b) gchoose n"
proof -
  let ?ba = "fps_binomial a"
  let ?bb = "fps_binomial b"
  let ?bab = "fps_binomial (a + b)"
  from fps_binomial_add_mult[of a b] have "?bab $ n = (?ba * ?bb)$n" by simp
  then show ?thesis by (simp add: fps_mult_nth)
qed

lemma binomial_Vandermonde:
  "sum (\<lambda>k. (a choose k) * (b choose (n - k))) {0..n} = (a + b) choose n"
  using gbinomial_Vandermonde[of "(of_nat a)" "of_nat b" n]
  by (simp only: binomial_gbinomial[symmetric] of_nat_mult[symmetric]
                 of_nat_sum[symmetric] of_nat_add[symmetric] of_nat_eq_iff)

lemma binomial_Vandermonde_same: "sum (\<lambda>k. (n choose k)\<^sup>2) {0..n} = (2 * n) choose n"
  using binomial_Vandermonde[of n n n, symmetric]
  unfolding mult_2
  apply (simp add: power2_eq_square)
  apply (rule sum.cong)
  apply (auto intro:  binomial_symmetric)
  done

lemma Vandermonde_pochhammer_lemma:
  fixes a :: "'a::field_char_0"
  assumes b: "\<forall>j\<in>{0 ..<n}. b \<noteq> of_nat j"
  shows "sum (\<lambda>k. (pochhammer (- a) k * pochhammer (- (of_nat n)) k) /
      (of_nat (fact k) * pochhammer (b - of_nat n + 1) k)) {0..n} =
    pochhammer (- (a + b)) n / pochhammer (- b) n"
  (is "?l = ?r")
proof -
  let ?m1 = "\<lambda>m. (- 1 :: 'a) ^ m"
  let ?f = "\<lambda>m. of_nat (fact m)"
  let ?p = "\<lambda>(x::'a). pochhammer (- x)"
  from b have bn0: "?p b n \<noteq> 0"
    unfolding pochhammer_eq_0_iff by simp
  have th00:
    "b gchoose (n - k) =
        (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)"
      (is ?gchoose)
    "pochhammer (1 + b - of_nat n) k \<noteq> 0"
      (is ?pochhammer)
    if kn: "k \<in> {0..n}" for k
  proof -
    from kn have "k \<le> n" by simp
    have nz: "pochhammer (1 + b - of_nat n) n \<noteq> 0"
    proof
      assume "pochhammer (1 + b - of_nat n) n = 0"
      then have c: "pochhammer (b - of_nat n + 1) n = 0"
        by (simp add: algebra_simps)
      then obtain j where j: "j < n" "b - of_nat n + 1 = - of_nat j"
        unfolding pochhammer_eq_0_iff by blast
      from j have "b = of_nat n - of_nat j - of_nat 1"
        by (simp add: algebra_simps)
      then have "b = of_nat (n - j - 1)"
        using j kn by (simp add: of_nat_diff)
      with b show False using j by auto
    qed

    from nz kn [simplified] have nz': "pochhammer (1 + b - of_nat n) k \<noteq> 0"
      by (rule pochhammer_neq_0_mono)

    consider "k = 0 \<or> n = 0" | "k \<noteq> 0" "n \<noteq> 0"
      by blast
    then have "b gchoose (n - k) =
      (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)"
    proof cases
      case 1
      then show ?thesis
        using kn by (cases "k = 0") (simp_all add: gbinomial_pochhammer)
    next
      case neq: 2
      then obtain m where m: "n = Suc m"
        by (cases n) auto
      from neq(1) obtain h where h: "k = Suc h"
        by (cases k) auto
      show ?thesis
      proof (cases "k = n")
        case True
        then show ?thesis
          using pochhammer_minus'[where k=k and b=b]
          apply (simp add: pochhammer_same)
          using bn0
          apply (simp add: field_simps power_add[symmetric])
          done
      next
        case False
        with kn have kn': "k < n"
          by simp
        have m1nk: "?m1 n = prod (\<lambda>i. - 1) {..m}" "?m1 k = prod (\<lambda>i. - 1) {0..h}"
          by (simp_all add: prod_constant m h)
        have bnz0: "pochhammer (b - of_nat n + 1) k \<noteq> 0"
          using bn0 kn
          unfolding pochhammer_eq_0_iff
          apply auto
          apply (erule_tac x= "n - ka - 1" in allE)
          apply (auto simp add: algebra_simps of_nat_diff)
          done
        have eq1: "prod (\<lambda>k. (1::'a) + of_nat m - of_nat k) {..h} =
          prod of_nat {Suc (m - h) .. Suc m}"
          using kn' h m
          by (intro prod.reindex_bij_witness[where i="\<lambda>k. Suc m - k" and j="\<lambda>k. Suc m - k"])
             (auto simp: of_nat_diff)
        have th1: "(?m1 k * ?p (of_nat n) k) / ?f n = 1 / of_nat(fact (n - k))"
          apply (simp add: pochhammer_minus field_simps)
          using \<open>k \<le> n\<close> apply (simp add: fact_split [of k n])
          apply (simp add: pochhammer_prod)
          using prod.atLeast_lessThan_shift_bounds [where ?'a = 'a, of "\<lambda>i. 1 + of_nat i" 0 "n - k" k]
          apply (auto simp add: of_nat_diff field_simps)
          done
        have th20: "?m1 n * ?p b n = prod (\<lambda>i. b - of_nat i) {0..m}"
          apply (simp add: pochhammer_minus field_simps m)
          apply (auto simp add: pochhammer_prod_rev of_nat_diff prod.atLeast_Suc_atMost_Suc_shift)
          done
        have th21:"pochhammer (b - of_nat n + 1) k = prod (\<lambda>i. b - of_nat i) {n - k .. n - 1}"
          using kn apply (simp add: pochhammer_prod_rev m h prod.atLeast_Suc_atMost_Suc_shift)
          using prod.atLeast_atMost_shift_0 [of "m - h" m, where ?'a = 'a]
          apply (auto simp add: of_nat_diff field_simps)
          done
        have "?m1 n * ?p b n =
          prod (\<lambda>i. b - of_nat i) {0.. n - k - 1} * pochhammer (b - of_nat n + 1) k"
          using kn' m h unfolding th20 th21 apply simp
          apply (subst prod.union_disjoint [symmetric])
          apply auto
          apply (rule prod.cong)
          apply auto
          done
        then have th2: "(?m1 n * ?p b n)/pochhammer (b - of_nat n + 1) k =
          prod (\<lambda>i. b - of_nat i) {0.. n - k - 1}"
          using nz' by (simp add: field_simps)
        have "(?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k) =
          ((?m1 k * ?p (of_nat n) k) / ?f n) * ((?m1 n * ?p b n)/pochhammer (b - of_nat n + 1) k)"
          using bnz0
          by (simp add: field_simps)
        also have "\<dots> = b gchoose (n - k)"
          unfolding th1 th2
          using kn' m h
          apply (simp add: field_simps gbinomial_mult_fact)
          apply (rule prod.cong)
          apply auto
          done
        finally show ?thesis by simp
      qed
    qed
    then show ?gchoose and ?pochhammer
      apply (cases "n = 0")
      using nz'
      apply auto
      done
  qed
  have "?r = ((a + b) gchoose n) * (of_nat (fact n) / (?m1 n * pochhammer (- b) n))"
    unfolding gbinomial_pochhammer
    using bn0 by (auto simp add: field_simps)
  also have "\<dots> = ?l"
    unfolding gbinomial_Vandermonde[symmetric]
    apply (simp add: th00)
    unfolding gbinomial_pochhammer
    using bn0
    apply (simp add: sum_distrib_right sum_distrib_left field_simps)
    done
  finally show ?thesis by simp
qed

lemma Vandermonde_pochhammer:
  fixes a :: "'a::field_char_0"
  assumes c: "\<forall>i \<in> {0..< n}. c \<noteq> - of_nat i"
  shows "sum (\<lambda>k. (pochhammer a k * pochhammer (- (of_nat n)) k) /
    (of_nat (fact k) * pochhammer c k)) {0..n} = pochhammer (c - a) n / pochhammer c n"
proof -
  let ?a = "- a"
  let ?b = "c + of_nat n - 1"
  have h: "\<forall> j \<in>{0..< n}. ?b \<noteq> of_nat j"
    using c
    apply (auto simp add: algebra_simps of_nat_diff)
    apply (erule_tac x = "n - j - 1" in ballE)
    apply (auto simp add: of_nat_diff algebra_simps)
    done
  have th0: "pochhammer (- (?a + ?b)) n = (- 1)^n * pochhammer (c - a) n"
    unfolding pochhammer_minus
    by (simp add: algebra_simps)
  have th1: "pochhammer (- ?b) n = (- 1)^n * pochhammer c n"
    unfolding pochhammer_minus
    by simp
  have nz: "pochhammer c n \<noteq> 0" using c
    by (simp add: pochhammer_eq_0_iff)
  from Vandermonde_pochhammer_lemma[where a = "?a" and b="?b" and n=n, OF h, unfolded th0 th1]
  show ?thesis
    using nz by (simp add: field_simps sum_distrib_left)
qed


subsubsection \<open>Formal trigonometric functions\<close>

definition "fps_sin (c::'a::field_char_0) =
  Abs_fps (\<lambda>n. if even n then 0 else (- 1) ^((n - 1) div 2) * c^n /(of_nat (fact n)))"

definition "fps_cos (c::'a::field_char_0) =
  Abs_fps (\<lambda>n. if even n then (- 1) ^ (n div 2) * c^n / (of_nat (fact n)) else 0)"

lemma fps_sin_0 [simp]: "fps_sin 0 = 0"
  by (intro fps_ext) (auto simp: fps_sin_def elim!: oddE)

lemma fps_cos_0 [simp]: "fps_cos 0 = 1"
  by (intro fps_ext) (auto simp: fps_cos_def)

lemma fps_sin_deriv:
  "fps_deriv (fps_sin c) = fps_const c * fps_cos c"
  (is "?lhs = ?rhs")
proof (rule fps_ext)
  fix n :: nat
  show "?lhs $ n = ?rhs $ n"
  proof (cases "even n")
    case True
    have "?lhs$n = of_nat (n+1) * (fps_sin c $ (n+1))" by simp
    also have "\<dots> = of_nat (n+1) * ((- 1)^(n div 2) * c^Suc n / of_nat (fact (Suc n)))"
      using True by (simp add: fps_sin_def)
    also have "\<dots> = (- 1)^(n div 2) * c^Suc n * (of_nat (n+1) / (of_nat (Suc n) * of_nat (fact n)))"
      unfolding fact_Suc of_nat_mult
      by (simp add: field_simps del: of_nat_add of_nat_Suc)
    also have "\<dots> = (- 1)^(n div 2) *c^Suc n / of_nat (fact n)"
      by (simp add: field_simps del: of_nat_add of_nat_Suc)
    finally show ?thesis
      using True by (simp add: fps_cos_def field_simps)
  next
    case False
    then show ?thesis
      by (simp_all add: fps_deriv_def fps_sin_def fps_cos_def)
  qed
qed

lemma fps_cos_deriv: "fps_deriv (fps_cos c) = fps_const (- c)* (fps_sin c)"
  (is "?lhs = ?rhs")
proof (rule fps_ext)
  have th0: "- ((- 1::'a) ^ n) = (- 1)^Suc n" for n
    by simp
  show "?lhs $ n = ?rhs $ n" for n
  proof (cases "even n")
    case False
    then have n0: "n \<noteq> 0" by presburger
    from False have th1: "Suc ((n - 1) div 2) = Suc n div 2"
      by (cases n) simp_all
    have "?lhs$n = of_nat (n+1) * (fps_cos c $ (n+1))" by simp
    also have "\<dots> = of_nat (n+1) * ((- 1)^((n + 1) div 2) * c^Suc n / of_nat (fact (Suc n)))"
      using False by (simp add: fps_cos_def)
    also have "\<dots> = (- 1)^((n + 1) div 2)*c^Suc n * (of_nat (n+1) / (of_nat (Suc n) * of_nat (fact n)))"
      unfolding fact_Suc of_nat_mult
      by (simp add: field_simps del: of_nat_add of_nat_Suc)
    also have "\<dots> = (- 1)^((n + 1) div 2) * c^Suc n / of_nat (fact n)"
      by (simp add: field_simps del: of_nat_add of_nat_Suc)
    also have "\<dots> = (- ((- 1)^((n - 1) div 2))) * c^Suc n / of_nat (fact n)"
      unfolding th0 unfolding th1 by simp
    finally show ?thesis
      using False by (simp add: fps_sin_def field_simps)
  next
    case True
    then show ?thesis
      by (simp_all add: fps_deriv_def fps_sin_def fps_cos_def)
  qed
qed

lemma fps_sin_cos_sum_of_squares: "(fps_cos c)\<^sup>2 + (fps_sin c)\<^sup>2 = 1"
  (is "?lhs = _")
proof -
  have "fps_deriv ?lhs = 0"
    apply (simp add:  fps_deriv_power fps_sin_deriv fps_cos_deriv)
    apply (simp add: field_simps fps_const_neg[symmetric] del: fps_const_neg)
    done
  then have "?lhs = fps_const (?lhs $ 0)"
    unfolding fps_deriv_eq_0_iff .
  also have "\<dots> = 1"
    by (auto simp add: fps_eq_iff numeral_2_eq_2 fps_mult_nth fps_cos_def fps_sin_def)
  finally show ?thesis .
qed

lemma fps_sin_nth_0 [simp]: "fps_sin c $ 0 = 0"
  unfolding fps_sin_def by simp

lemma fps_sin_nth_1 [simp]: "fps_sin c $ 1 = c"
  unfolding fps_sin_def by simp

lemma fps_sin_nth_add_2:
    "fps_sin c $ (n + 2) = - (c * c * fps_sin c $ n / (of_nat (n + 1) * of_nat (n + 2)))"
  unfolding fps_sin_def
  apply (cases n)
  apply simp
  apply (simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq del: of_nat_Suc fact_Suc)
  apply simp
  done

lemma fps_cos_nth_0 [simp]: "fps_cos c $ 0 = 1"
  unfolding fps_cos_def by simp

lemma fps_cos_nth_1 [simp]: "fps_cos c $ 1 = 0"
  unfolding fps_cos_def by simp

lemma fps_cos_nth_add_2:
  "fps_cos c $ (n + 2) = - (c * c * fps_cos c $ n / (of_nat (n + 1) * of_nat (n + 2)))"
  unfolding fps_cos_def
  apply (simp add: nonzero_divide_eq_eq nonzero_eq_divide_eq del: of_nat_Suc fact_Suc)
  apply simp
  done

lemma nat_induct2: "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (n + 2)) \<Longrightarrow> P (n::nat)"
  unfolding One_nat_def numeral_2_eq_2
  apply (induct n rule: nat_less_induct)
  apply (case_tac n)
  apply simp
  apply (rename_tac m)
  apply (case_tac m)
  apply simp
  apply (rename_tac k)
  apply (case_tac k)
  apply simp_all
  done

lemma nat_add_1_add_1: "(n::nat) + 1 + 1 = n + 2"
  by simp

lemma eq_fps_sin:
  assumes 0: "a $ 0 = 0"
    and 1: "a $ 1 = c"
    and 2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "a = fps_sin c"
  apply (rule fps_ext)
  apply (induct_tac n rule: nat_induct2)
  apply (simp add: 0)
  apply (simp add: 1 del: One_nat_def)
  apply (rename_tac m, cut_tac f="\<lambda>a. a $ m" in arg_cong [OF 2])
  apply (simp add: nat_add_1_add_1 fps_sin_nth_add_2
              del: One_nat_def of_nat_Suc of_nat_add add_2_eq_Suc')
  apply (subst minus_divide_left)
  apply (subst nonzero_eq_divide_eq)
  apply (simp del: of_nat_add of_nat_Suc)
  apply (simp only: ac_simps)
  done

lemma eq_fps_cos:
  assumes 0: "a $ 0 = 1"
    and 1: "a $ 1 = 0"
    and 2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "a = fps_cos c"
  apply (rule fps_ext)
  apply (induct_tac n rule: nat_induct2)
  apply (simp add: 0)
  apply (simp add: 1 del: One_nat_def)
  apply (rename_tac m, cut_tac f="\<lambda>a. a $ m" in arg_cong [OF 2])
  apply (simp add: nat_add_1_add_1 fps_cos_nth_add_2
              del: One_nat_def of_nat_Suc of_nat_add add_2_eq_Suc')
  apply (subst minus_divide_left)
  apply (subst nonzero_eq_divide_eq)
  apply (simp del: of_nat_add of_nat_Suc)
  apply (simp only: ac_simps)
  done

lemma mult_nth_0 [simp]: "(a * b) $ 0 = a $ 0 * b $ 0"
  by (simp add: fps_mult_nth)

lemma mult_nth_1 [simp]: "(a * b) $ 1 = a $ 0 * b $ 1 + a $ 1 * b $ 0"
  by (simp add: fps_mult_nth)

lemma fps_sin_add: "fps_sin (a + b) = fps_sin a * fps_cos b + fps_cos a * fps_sin b"
  apply (rule eq_fps_sin [symmetric], simp, simp del: One_nat_def)
  apply (simp del: fps_const_neg fps_const_add fps_const_mult
              add: fps_const_add [symmetric] fps_const_neg [symmetric]
                   fps_sin_deriv fps_cos_deriv algebra_simps)
  done

lemma fps_cos_add: "fps_cos (a + b) = fps_cos a * fps_cos b - fps_sin a * fps_sin b"
  apply (rule eq_fps_cos [symmetric], simp, simp del: One_nat_def)
  apply (simp del: fps_const_neg fps_const_add fps_const_mult
              add: fps_const_add [symmetric] fps_const_neg [symmetric]
                   fps_sin_deriv fps_cos_deriv algebra_simps)
  done

lemma fps_sin_even: "fps_sin (- c) = - fps_sin c"
  by (auto simp add: fps_eq_iff fps_sin_def)

lemma fps_cos_odd: "fps_cos (- c) = fps_cos c"
  by (auto simp add: fps_eq_iff fps_cos_def)

definition "fps_tan c = fps_sin c / fps_cos c"

lemma fps_tan_0 [simp]: "fps_tan 0 = 0"
  by (simp add: fps_tan_def)

lemma fps_tan_deriv: "fps_deriv (fps_tan c) = fps_const c / (fps_cos c)\<^sup>2"
proof -
  have th0: "fps_cos c $ 0 \<noteq> 0" by (simp add: fps_cos_def)
  from this have "fps_cos c \<noteq> 0" by (intro notI) simp
  hence "fps_deriv (fps_tan c) =
           fps_const c * (fps_cos c^2 + fps_sin c^2) / (fps_cos c^2)"
    by (simp add: fps_tan_def fps_divide_deriv power2_eq_square algebra_simps
                  fps_sin_deriv fps_cos_deriv fps_const_neg[symmetric] div_mult_swap
             del: fps_const_neg)
  also note fps_sin_cos_sum_of_squares
  finally show ?thesis by simp
qed

text \<open>Connection to @{const "fps_exp"} over the complex numbers --- Euler and de Moivre.\<close>

lemma fps_exp_ii_sin_cos: "fps_exp (\<i> * c) = fps_cos c + fps_const \<i> * fps_sin c"
  (is "?l = ?r")
proof -
  have "?l $ n = ?r $ n" for n
  proof (cases "even n")
    case True
    then obtain m where m: "n = 2 * m" ..
    show ?thesis
      by (simp add: m fps_sin_def fps_cos_def power_mult_distrib power_mult power_minus [of "c ^ 2"])
  next
    case False
    then obtain m where m: "n = 2 * m + 1" ..
    show ?thesis
      by (simp add: m fps_sin_def fps_cos_def power_mult_distrib
        power_mult power_minus [of "c ^ 2"])
  qed
  then show ?thesis
    by (simp add: fps_eq_iff)
qed

lemma fps_exp_minus_ii_sin_cos: "fps_exp (- (\<i> * c)) = fps_cos c - fps_const \<i> * fps_sin c"
  unfolding minus_mult_right fps_exp_ii_sin_cos by (simp add: fps_sin_even fps_cos_odd)

lemma fps_const_minus: "fps_const (c::'a::group_add) - fps_const d = fps_const (c - d)"
  by (fact fps_const_sub)

lemma fps_of_int: "fps_const (of_int c) = of_int c"
  by (induction c) (simp_all add: fps_const_minus [symmetric] fps_of_nat fps_const_neg [symmetric] 
                             del: fps_const_minus fps_const_neg)

lemma fps_deriv_of_int [simp]: "fps_deriv (of_int n) = 0"
  by (simp add: fps_of_int [symmetric])

lemma fps_numeral_fps_const: "numeral i = fps_const (numeral i :: 'a::comm_ring_1)"
  by (fact numeral_fps_const) (* FIfps_XME: duplicate *)

lemma fps_cos_fps_exp_ii: "fps_cos c = (fps_exp (\<i> * c) + fps_exp (- \<i> * c)) / fps_const 2"
proof -
  have th: "fps_cos c + fps_cos c = fps_cos c * fps_const 2"
    by (simp add: numeral_fps_const)
  show ?thesis
    unfolding fps_exp_ii_sin_cos minus_mult_commute
    by (simp add: fps_sin_even fps_cos_odd numeral_fps_const fps_divide_unit fps_const_inverse th)
qed

lemma fps_sin_fps_exp_ii: "fps_sin c = (fps_exp (\<i> * c) - fps_exp (- \<i> * c)) / fps_const (2*\<i>)"
proof -
  have th: "fps_const \<i> * fps_sin c + fps_const \<i> * fps_sin c = fps_sin c * fps_const (2 * \<i>)"
    by (simp add: fps_eq_iff numeral_fps_const)
  show ?thesis
    unfolding fps_exp_ii_sin_cos minus_mult_commute
    by (simp add: fps_sin_even fps_cos_odd fps_divide_unit fps_const_inverse th)
qed

lemma fps_tan_fps_exp_ii:
  "fps_tan c = (fps_exp (\<i> * c) - fps_exp (- \<i> * c)) / 
      (fps_const \<i> * (fps_exp (\<i> * c) + fps_exp (- \<i> * c)))"
  unfolding fps_tan_def fps_sin_fps_exp_ii fps_cos_fps_exp_ii mult_minus_left fps_exp_neg
  apply (simp add: fps_divide_unit fps_inverse_mult fps_const_mult[symmetric] fps_const_inverse del: fps_const_mult)
  apply simp
  done

lemma fps_demoivre:
  "(fps_cos a + fps_const \<i> * fps_sin a)^n =
    fps_cos (of_nat n * a) + fps_const \<i> * fps_sin (of_nat n * a)"
  unfolding fps_exp_ii_sin_cos[symmetric] fps_exp_power_mult
  by (simp add: ac_simps)


subsection \<open>Hypergeometric series\<close>

definition "fps_hypergeo as bs (c::'a::{field_char_0,field}) =
  Abs_fps (\<lambda>n. (foldl (\<lambda>r a. r* pochhammer a n) 1 as * c^n) /
    (foldl (\<lambda>r b. r * pochhammer b n) 1 bs * of_nat (fact n)))"

lemma fps_hypergeo_nth[simp]: "fps_hypergeo as bs c $ n =
  (foldl (\<lambda>r a. r* pochhammer a n) 1 as * c^n) /
    (foldl (\<lambda>r b. r * pochhammer b n) 1 bs * of_nat (fact n))"
  by (simp add: fps_hypergeo_def)

lemma foldl_mult_start:
  fixes v :: "'a::comm_ring_1"
  shows "foldl (\<lambda>r x. r * f x) v as * x = foldl (\<lambda>r x. r * f x) (v * x) as "
  by (induct as arbitrary: x v) (auto simp add: algebra_simps)

lemma foldr_mult_foldl:
  fixes v :: "'a::comm_ring_1"
  shows "foldr (\<lambda>x r. r * f x) as v = foldl (\<lambda>r x. r * f x) v as"
  by (induct as arbitrary: v) (auto simp add: foldl_mult_start)

lemma fps_hypergeo_nth_alt:
  "fps_hypergeo as bs c $ n = foldr (\<lambda>a r. r * pochhammer a n) as (c ^ n) /
    foldr (\<lambda>b r. r * pochhammer b n) bs (of_nat (fact n))"
  by (simp add: foldl_mult_start foldr_mult_foldl)

lemma fps_hypergeo_fps_exp[simp]: "fps_hypergeo [] [] c = fps_exp c"
  by (simp add: fps_eq_iff)

lemma fps_hypergeo_1_0[simp]: "fps_hypergeo [1] [] c = 1/(1 - fps_const c * fps_X)"
proof -
  let ?a = "(Abs_fps (\<lambda>n. 1)) oo (fps_const c * fps_X)"
  have th0: "(fps_const c * fps_X) $ 0 = 0" by simp
  show ?thesis unfolding gp[OF th0, symmetric]
    by (auto simp add: fps_eq_iff pochhammer_fact[symmetric]
      fps_compose_nth power_mult_distrib cond_value_iff sum.delta' cong del: if_weak_cong)
qed

lemma fps_hypergeo_B[simp]: "fps_hypergeo [-a] [] (- 1) = fps_binomial a"
  by (simp add: fps_eq_iff gbinomial_pochhammer algebra_simps)

lemma fps_hypergeo_0[simp]: "fps_hypergeo as bs c $ 0 = 1"
  apply simp
  apply (subgoal_tac "\<forall>as. foldl (\<lambda>(r::'a) (a::'a). r) 1 as = 1")
  apply auto
  apply (induct_tac as)
  apply auto
  done

lemma foldl_prod_prod:
  "foldl (\<lambda>(r::'b::comm_ring_1) (x::'a::comm_ring_1). r * f x) v as * foldl (\<lambda>r x. r * g x) w as =
    foldl (\<lambda>r x. r * f x * g x) (v * w) as"
  by (induct as arbitrary: v w) (auto simp add: algebra_simps)


lemma fps_hypergeo_rec:
  "fps_hypergeo as bs c $ Suc n = ((foldl (\<lambda>r a. r* (a + of_nat n)) c as) /
    (foldl (\<lambda>r b. r * (b + of_nat n)) (of_nat (Suc n)) bs )) * fps_hypergeo as bs c $ n"
  apply (simp del: of_nat_Suc of_nat_add fact_Suc)
  apply (simp add: foldl_mult_start del: fact_Suc of_nat_Suc)
  unfolding foldl_prod_prod[unfolded foldl_mult_start] pochhammer_Suc
  apply (simp add: algebra_simps)
  done

lemma fps_XD_nth[simp]: "fps_XD a $ n = (if n = 0 then 0 else of_nat n * a$n)"
  by (simp add: fps_XD_def)

lemma fps_XD_0th[simp]: "fps_XD a $ 0 = 0"
  by simp
lemma fps_XD_Suc[simp]:" fps_XD a $ Suc n = of_nat (Suc n) * a $ Suc n"
  by simp

definition "fps_XDp c a = fps_XD a + fps_const c * a"

lemma fps_XDp_nth[simp]: "fps_XDp c a $ n = (c + of_nat n) * a$n"
  by (simp add: fps_XDp_def algebra_simps)

lemma fps_XDp_commute: "fps_XDp b \<circ> fps_XDp (c::'a::comm_ring_1) = fps_XDp c \<circ> fps_XDp b"
  by (auto simp add: fps_XDp_def fun_eq_iff fps_eq_iff algebra_simps)

lemma fps_XDp0 [simp]: "fps_XDp 0 = fps_XD"
  by (simp add: fun_eq_iff fps_eq_iff)

lemma fps_XDp_fps_integral [simp]: "fps_XDp 0 (fps_integral a c) = fps_X * a"
  by (simp add: fps_eq_iff fps_integral_def)

lemma fps_hypergeo_minus_nat:
  "fps_hypergeo [- of_nat n] [- of_nat (n + m)] (c::'a::{field_char_0,field}) $ k =
    (if k \<le> n then
      pochhammer (- of_nat n) k * c ^ k / (pochhammer (- of_nat (n + m)) k * of_nat (fact k))
     else 0)"
  "fps_hypergeo [- of_nat m] [- of_nat (m + n)] (c::'a::{field_char_0,field}) $ k =
    (if k \<le> m then
      pochhammer (- of_nat m) k * c ^ k / (pochhammer (- of_nat (m + n)) k * of_nat (fact k))
     else 0)"
  by (auto simp add: pochhammer_eq_0_iff)

lemma sum_eq_if: "sum f {(n::nat) .. m} = (if m < n then 0 else f n + sum f {n+1 .. m})"
  apply simp
  apply (subst sum.insert[symmetric])
  apply (auto simp add: not_less sum_head_Suc)
  done

lemma pochhammer_rec_if: "pochhammer a n = (if n = 0 then 1 else a * pochhammer (a + 1) (n - 1))"
  by (cases n) (simp_all add: pochhammer_rec)

lemma fps_XDp_foldr_nth [simp]: "foldr (\<lambda>c r. fps_XDp c \<circ> r) cs (\<lambda>c. fps_XDp c a) c0 $ n =
    foldr (\<lambda>c r. (c + of_nat n) * r) cs (c0 + of_nat n) * a$n"
  by (induct cs arbitrary: c0) (auto simp add: algebra_simps)

lemma genric_fps_XDp_foldr_nth:
  assumes f: "\<forall>n c a. f c a $ n = (of_nat n + k c) * a$n"
  shows "foldr (\<lambda>c r. f c \<circ> r) cs (\<lambda>c. g c a) c0 $ n =
    foldr (\<lambda>c r. (k c + of_nat n) * r) cs (g c0 a $ n)"
  by (induct cs arbitrary: c0) (auto simp add: algebra_simps f)

lemma dist_less_imp_nth_equal:
  assumes "dist f g < inverse (2 ^ i)"
    and"j \<le> i"
  shows "f $ j = g $ j"
proof (rule ccontr)
  assume "f $ j \<noteq> g $ j"
  hence "f \<noteq> g" by auto
  with assms have "i < subdegree (f - g)"
    by (simp add: if_split_asm dist_fps_def)
  also have "\<dots> \<le> j"
    using \<open>f $ j \<noteq> g $ j\<close> by (intro subdegree_leI) simp_all
  finally show False using \<open>j \<le> i\<close> by simp
qed

lemma nth_equal_imp_dist_less:
  assumes "\<And>j. j \<le> i \<Longrightarrow> f $ j = g $ j"
  shows "dist f g < inverse (2 ^ i)"
proof (cases "f = g")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "dist f g = inverse (2 ^ subdegree (f - g))"
    by (simp add: if_split_asm dist_fps_def)
  moreover
  from assms and False have "i < subdegree (f - g)"
    by (intro subdegree_greaterI) simp_all
  ultimately show ?thesis by simp
qed

lemma dist_less_eq_nth_equal: "dist f g < inverse (2 ^ i) \<longleftrightarrow> (\<forall>j \<le> i. f $ j = g $ j)"
  using dist_less_imp_nth_equal nth_equal_imp_dist_less by blast

instance fps :: (comm_ring_1) complete_space
proof
  fix fps_X :: "nat \<Rightarrow> 'a fps"
  assume "Cauchy fps_X"
  obtain M where M: "\<forall>i. \<forall>m \<ge> M i. \<forall>j \<le> i. fps_X (M i) $ j = fps_X m $ j"
  proof -
    have "\<exists>M. \<forall>m \<ge> M. \<forall>j\<le>i. fps_X M $ j = fps_X m $ j" for i
    proof -
      have "0 < inverse ((2::real)^i)" by simp
      from metric_CauchyD[OF \<open>Cauchy fps_X\<close> this] dist_less_imp_nth_equal
      show ?thesis by blast
    qed
    then show ?thesis using that by metis
  qed

  show "convergent fps_X"
  proof (rule convergentI)
    show "fps_X \<longlonglongrightarrow> Abs_fps (\<lambda>i. fps_X (M i) $ i)"
      unfolding tendsto_iff
    proof safe
      fix e::real assume e: "0 < e"
      have "(\<lambda>n. inverse (2 ^ n) :: real) \<longlonglongrightarrow> 0" by (rule LIMSEQ_inverse_realpow_zero) simp_all
      from this and e have "eventually (\<lambda>i. inverse (2 ^ i) < e) sequentially"
        by (rule order_tendstoD)
      then obtain i where "inverse (2 ^ i) < e"
        by (auto simp: eventually_sequentially)
      have "eventually (\<lambda>x. M i \<le> x) sequentially"
        by (auto simp: eventually_sequentially)
      then show "eventually (\<lambda>x. dist (fps_X x) (Abs_fps (\<lambda>i. fps_X (M i) $ i)) < e) sequentially"
      proof eventually_elim
        fix x
        assume x: "M i \<le> x"
        have "fps_X (M i) $ j = fps_X (M j) $ j" if "j \<le> i" for j
          using M that by (metis nat_le_linear)
        with x have "dist (fps_X x) (Abs_fps (\<lambda>j. fps_X (M j) $ j)) < inverse (2 ^ i)"
          using M by (force simp: dist_less_eq_nth_equal)
        also note \<open>inverse (2 ^ i) < e\<close>
        finally show "dist (fps_X x) (Abs_fps (\<lambda>j. fps_X (M j) $ j)) < e" .
      qed
    qed
  qed
qed

(* TODO: Figure out better notation for this thing *)
no_notation fps_nth (infixl "$" 75)

bundle fps_notation
begin
notation fps_nth (infixl "$" 75)
end

end

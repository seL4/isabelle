(*  Title:      HOL/Computational_Algebra/Formal_Power_Series.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Jeremy Sylvestre, University of Alberta (Augustana Campus)
    Author:     Manuel Eberl, TU München
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

lemmas fps_eq_iff = expand_fps_eq

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

lemma fps_nonzeroI: "f$n \<noteq> 0 \<Longrightarrow> f \<noteq> 0"
  by auto

instantiation fps :: ("{one, zero}") one
begin
  definition fps_one_def: "1 = Abs_fps (\<lambda>n. if n = 0 then 1 else 0)"
  instance ..
end

lemma fps_one_nth [simp]: "1 $ n = (if n = 0 then 1 else 0)"
  unfolding fps_one_def by simp

instantiation fps :: (plus) plus
begin
  definition fps_plus_def: "(+) = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n + g $ n))"
  instance ..
end

lemma fps_add_nth [simp]: "(f + g) $ n = f $ n + g $ n"
  unfolding fps_plus_def by simp

instantiation fps :: (minus) minus
begin
  definition fps_minus_def: "(-) = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n - g $ n))"
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

lemma fps_neg_0 [simp]: "-(0::'a::group_add fps) = 0"
  by (rule iffD2, rule fps_eq_iff, auto)

instantiation fps :: ("{comm_monoid_add, times}") times
begin
  definition fps_times_def: "(*) = (\<lambda>f g. Abs_fps (\<lambda>n. \<Sum>i=0..n. f $ i * g $ (n - i)))"
  instance ..
end

lemma fps_mult_nth: "(f * g) $ n = (\<Sum>i=0..n. f$i * g$(n - i))"
  unfolding fps_times_def by simp

lemma fps_mult_nth_0 [simp]: "(f * g) $ 0 = f $ 0 * g $ 0"
  unfolding fps_times_def by simp

lemma fps_mult_nth_1: "(f * g) $ 1 = f$0 * g$1 + f$1 * g$0"
  by (simp add: fps_mult_nth)

lemma fps_mult_nth_1' [simp]: "(f * g) $ Suc 0 = f$0 * g$Suc 0 + f$Suc 0 * g$0"
  by (simp add: fps_mult_nth)

lemmas mult_nth_0 = fps_mult_nth_0
lemmas mult_nth_1 = fps_mult_nth_1

instance fps :: ("{comm_monoid_add, mult_zero}") mult_zero
proof
  fix a :: "'a fps"
  show "0 * a = 0" by (simp add: fps_ext fps_mult_nth)
  show "a * 0 = 0" by (simp add: fps_ext fps_mult_nth)
qed

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

lemma fps_one_mult:
  fixes f :: "'a::{comm_monoid_add, mult_zero, monoid_mult} fps"
  shows "1 * f = f"
  and   "f * 1 = f"
  by    (simp_all add: fps_ext fps_mult_nth mult_delta_left mult_delta_right)


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

lemma subdegree_1 [simp]: "subdegree 1 = 0"
  by  (cases "(1::'a) = 0")
      (auto intro: subdegreeI fps_ext simp: subdegree_def)

lemma subdegree_eq_0_iff: "subdegree f = 0 \<longleftrightarrow> f = 0 \<or> f $ 0 \<noteq> 0"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  thus ?thesis
    using nth_subdegree_nonzero[OF \<open>f \<noteq> 0\<close>] by (fastforce intro!: subdegreeI)
qed simp_all

lemma subdegree_eq_0 [simp]: "f $ 0 \<noteq> 0 \<Longrightarrow> subdegree f = 0"
  by (simp add: subdegree_eq_0_iff)

lemma nth_subdegree_zero_iff [simp]: "f $ subdegree f = 0 \<longleftrightarrow> f = 0"
  by (cases "f = 0") auto

lemma fps_nonzero_subdegree_nonzeroI: "subdegree f > 0 \<Longrightarrow> f \<noteq> 0"
 by auto

lemma subdegree_uminus [simp]:
  "subdegree (-(f::('a::group_add) fps)) = subdegree f"
proof (cases "f=0")
  case False thus ?thesis by (force intro: subdegreeI)
qed simp

lemma subdegree_minus_commute [simp]:
  "subdegree (f-(g::('a::group_add) fps)) = subdegree (g - f)"
proof (-, cases "g-f=0")
  case True
  have "\<And>n. (f - g) $ n = -((g - f) $ n)" by simp
  with True have "f - g = 0" by (intro fps_ext) simp
  with True show ?thesis by simp
next
  case False show ?thesis
    using nth_subdegree_nonzero[OF False] by (fastforce intro: subdegreeI)
qed

lemma subdegree_add_ge':
  fixes   f g :: "'a::monoid_add fps"
  assumes "f + g \<noteq> 0"
  shows   "subdegree (f + g) \<ge> min (subdegree f) (subdegree g)"
  using   assms
  by      (force intro: subdegree_geI)

lemma subdegree_add_ge:
  assumes "f \<noteq> -(g :: ('a :: group_add) fps)"
  shows   "subdegree (f + g) \<ge> min (subdegree f) (subdegree g)"
proof (rule subdegree_add_ge')
  have "f + g = 0 \<Longrightarrow> False"
  proof-
    assume fg: "f + g = 0"
    have "\<And>n. f $ n = - g $ n"
    proof-
      fix n
      from fg have "(f + g) $ n = 0" by simp
      hence "f $ n + g $ n - g $ n = - g $ n" by simp
      thus "f $ n = - g $ n" by simp      
    qed
    with assms show False by (auto intro: fps_ext)
  qed
  thus "f + g \<noteq> 0" by fast
qed

lemma subdegree_add_eq1:
  assumes "f \<noteq> 0"
  and     "subdegree f < subdegree (g :: 'a::monoid_add fps)"
  shows   "subdegree (f + g) = subdegree f"
  using   assms
  by      (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma subdegree_add_eq2:
  assumes "g \<noteq> 0"
  and     "subdegree g < subdegree (f :: 'a :: monoid_add fps)"
  shows   "subdegree (f + g) = subdegree g"
  using   assms
  by      (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma subdegree_diff_eq1:
  assumes "f \<noteq> 0"
  and     "subdegree f < subdegree (g :: 'a :: group_add fps)"
  shows   "subdegree (f - g) = subdegree f"
  using   assms
  by      (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma subdegree_diff_eq1_cancel:
  assumes "f \<noteq> 0"
  and     "subdegree f < subdegree (g :: 'a :: cancel_comm_monoid_add fps)"
  shows   "subdegree (f - g) = subdegree f"
  using   assms
  by      (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma subdegree_diff_eq2:
  assumes "g \<noteq> 0"
  and     "subdegree g < subdegree (f :: 'a :: group_add fps)"
  shows   "subdegree (f - g) = subdegree g"
  using   assms
  by      (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma subdegree_diff_ge [simp]:
  assumes "f \<noteq> (g :: 'a :: group_add fps)"
  shows   "subdegree (f - g) \<ge> min (subdegree f) (subdegree g)"
proof-
  from assms have "f = - (- g) \<Longrightarrow> False" using expand_fps_eq by fastforce
  hence "f \<noteq> - (- g)" by fast
  moreover have "f + - g = f - g" by (simp add: fps_ext)
  ultimately show ?thesis
    using subdegree_add_ge[of f "-g"] by simp
qed

lemma subdegree_diff_ge':
  fixes   f g :: "'a :: comm_monoid_diff fps"
  assumes "f - g \<noteq> 0"
  shows   "subdegree (f - g) \<ge> subdegree f"
  using   assms
  by      (auto intro: subdegree_geI simp: nth_less_subdegree_zero)

lemma nth_subdegree_mult_left [simp]:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ (subdegree f) = f $ subdegree f * g $ 0"
  by    (cases "subdegree f") (simp_all add: fps_mult_nth nth_less_subdegree_zero)

lemma nth_subdegree_mult_right [simp]:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ (subdegree g) = f $ 0 * g $ subdegree g"
  by    (cases "subdegree g") (simp_all add: fps_mult_nth nth_less_subdegree_zero sum.atLeast_Suc_atMost)

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
  also have "... = f $ subdegree f * g $ subdegree g" by simp
  finally show ?thesis .
qed

lemma fps_mult_nth_eq0:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "n < subdegree f + subdegree g"
  shows   "(f*g) $ n = 0"
proof-
  have "\<And>i. i\<in>{0..n} \<Longrightarrow> f$i * g$(n - i) = 0"
  proof-
    fix i assume i: "i\<in>{0..n}"
    show "f$i * g$(n - i) = 0"
    proof (cases "i < subdegree f \<or> n - i < subdegree g")
      case False with assms i show ?thesis by auto
    qed (auto simp: nth_less_subdegree_zero)
  qed
  thus "(f * g) $ n = 0" by (simp add: fps_mult_nth)
qed

lemma fps_mult_subdegree_ge:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "f*g \<noteq> 0"
  shows   "subdegree (f*g) \<ge> subdegree f + subdegree g"
  using   assms fps_mult_nth_eq0
  by      (intro subdegree_geI) simp

lemma subdegree_mult':
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "f $ subdegree f * g $ subdegree g \<noteq> 0"
  shows   "subdegree (f*g) = subdegree f + subdegree g"
proof-
  from assms have "(f * g) $ (subdegree f + subdegree g) \<noteq> 0" by simp
  hence "f*g \<noteq> 0" by fastforce
  hence "subdegree (f*g) \<ge> subdegree f + subdegree g" using fps_mult_subdegree_ge by fast
  moreover from assms have "subdegree (f*g) \<le> subdegree f + subdegree g"
    by (intro subdegree_leI) simp
  ultimately show ?thesis by simp
qed

lemma subdegree_mult [simp]:
  fixes   f g :: "'a :: {semiring_no_zero_divisors} fps"
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows   "subdegree (f * g) = subdegree f + subdegree g"
  using   assms
  by      (intro subdegree_mult') simp

lemma fps_mult_nth_conv_upto_subdegree_left:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ n = (\<Sum>i=subdegree f..n. f $ i * g $ (n - i))"
proof (cases "subdegree f \<le> n")
  case True
  hence "{0..n} = {0..<subdegree f} \<union> {subdegree f..n}" by auto
  moreover have "{0..<subdegree f} \<inter> {subdegree f..n} = {}" by auto
  ultimately show ?thesis
    using nth_less_subdegree_zero[of _ f]
    by    (simp add: fps_mult_nth sum.union_disjoint)
qed (simp add: fps_mult_nth nth_less_subdegree_zero)

lemma fps_mult_nth_conv_upto_subdegree_right:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ n = (\<Sum>i=0..n - subdegree g. f $ i * g $ (n - i))"
proof-
  have "{0..n} = {0..n - subdegree g} \<union> {n - subdegree g<..n}" by auto
  moreover have "{0..n - subdegree g} \<inter> {n - subdegree g<..n} = {}" by auto
  moreover have "\<forall>i\<in>{n - subdegree g<..n}. g $ (n - i) = 0"
    using nth_less_subdegree_zero[of _ g] by auto
  ultimately show ?thesis by (simp add: fps_mult_nth sum.union_disjoint)
qed

lemma fps_mult_nth_conv_inside_subdegrees:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "(f * g) $ n = (\<Sum>i=subdegree f..n - subdegree g. f $ i * g $ (n - i))"
proof (cases "subdegree f \<le> n - subdegree g")
  case True
  hence "{subdegree f..n} = {subdegree f..n - subdegree g} \<union> {n - subdegree g<..n}"
    by auto
  moreover have "{subdegree f..n - subdegree g} \<inter> {n - subdegree g<..n} = {}" by auto
  moreover have "\<forall>i\<in>{n - subdegree g<..n}. f $ i * g $ (n - i) = 0"
    using nth_less_subdegree_zero[of _ g] by auto
  ultimately show ?thesis
    using fps_mult_nth_conv_upto_subdegree_left[of f g n]
    by    (simp add: sum.union_disjoint)
next
  case False
  hence 1: "subdegree f > n - subdegree g" by simp
  show ?thesis
  proof (cases "f*g = 0")
    case False
    with 1 have "n < subdegree (f*g)" using fps_mult_subdegree_ge[of f g] by simp
    with 1 show ?thesis by auto
  qed (simp add: 1)
qed

lemma fps_mult_nth_outside_subdegrees:
  fixes f g :: "('a :: {mult_zero,comm_monoid_add}) fps"
  shows "n < subdegree f \<Longrightarrow> (f * g) $ n = 0"
  and   "n < subdegree g \<Longrightarrow> (f * g) $ n = 0"
  by    (auto simp: fps_mult_nth_conv_inside_subdegrees)


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

lemma fps_mult_assoc_lemma:
  fixes k :: nat
    and f :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>j=0..k. \<Sum>i=0..j. f i (j - i) (n - j)) =
         (\<Sum>j=0..k. \<Sum>i=0..k - j. f j i (n - j - i))"
  by (induct k) (simp_all add: Suc_diff_le sum.distrib add.assoc)

instance fps :: (semiring_0) semiring_0
proof
  fix a b c :: "'a fps"
  show "(a + b) * c = a * c + b * c"
    by (simp add: expand_fps_eq fps_mult_nth distrib_right sum.distrib)
  show "a * (b + c) = a * b + a * c"
    by (simp add: expand_fps_eq fps_mult_nth distrib_left sum.distrib)
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

instance fps :: (semiring_0_cancel) semiring_0_cancel ..

lemma fps_mult_commute_lemma:
  fixes n :: nat
    and f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i=0..n. f i (n - i)) = (\<Sum>i=0..n. f (n - i) i)"
  by (rule sum.reindex_bij_witness[where i="(-) n" and j="(-) n"]) auto

instance fps :: (comm_semiring_0) comm_semiring_0
proof
  fix a b c :: "'a fps"
  show "a * b = b * a"
  proof (rule fps_ext)
    fix n :: nat
    have "(\<Sum>i=0..n. a$i * b$(n - i)) = (\<Sum>i=0..n. a$(n - i) * b$i)"
      by (rule fps_mult_commute_lemma)
    then show "(a * b) $ n = (b * a) $ n"
      by (simp add: fps_mult_nth mult.commute)
  qed 
qed (simp add: distrib_right)

instance fps :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance fps :: (semiring_1) semiring_1
proof
  fix a :: "'a fps"
  show "1 * a = a" "a * 1 = a" by (simp_all add: fps_one_mult)
qed

instance fps :: (comm_semiring_1) comm_semiring_1
  by standard simp

instance fps :: (semiring_1_cancel) semiring_1_cancel ..


subsection \<open>Selection of the nth power of the implicit variable in the infinite sum\<close>

lemma fps_square_nth: "(f^2) $ n = (\<Sum>k\<le>n. f $ k * f $ (n - k))"
  by (simp add: power2_eq_square fps_mult_nth atLeast0AtMost)

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

lemma fps_const_nonzero_eq_nonzero: "c \<noteq> 0 \<Longrightarrow> fps_const c \<noteq> 0"
  using fps_nonzeroI[of "fps_const c" 0] by simp

lemma fps_const_1_eq_1 [simp]: "fps_const 1 = 1"
  by (simp add: fps_ext)

lemma subdegree_fps_const [simp]: "subdegree (fps_const c) = 0"
  by (cases "c = 0") (auto intro!: subdegreeI)

lemma fps_const_neg [simp]: "- (fps_const (c::'a::group_add)) = fps_const (- c)"
  by (simp add: fps_ext)

lemma fps_const_add [simp]: "fps_const (c::'a::monoid_add) + fps_const d = fps_const (c + d)"
  by (simp add: fps_ext)

lemma fps_const_add_left: "fps_const (c::'a::monoid_add) + f =
    Abs_fps (\<lambda>n. if n = 0 then c + f$0 else f$n)"
  by (simp add: fps_ext)

lemma fps_const_add_right: "f + fps_const (c::'a::monoid_add) =
    Abs_fps (\<lambda>n. if n = 0 then f$0 + c else f$n)"
  by (simp add: fps_ext)

lemma fps_const_sub [simp]: "fps_const (c::'a::group_add) - fps_const d = fps_const (c - d)"
  by (simp add: fps_ext)

lemmas fps_const_minus = fps_const_sub

lemma fps_const_mult[simp]:
  fixes c d :: "'a::{comm_monoid_add,mult_zero}"
  shows "fps_const c * fps_const d = fps_const (c * d)"
  by    (simp add: fps_eq_iff fps_mult_nth sum.neutral)

lemma fps_const_mult_left:
  "fps_const (c::'a::{comm_monoid_add,mult_zero}) * f = Abs_fps (\<lambda>n. c * f$n)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_left)

lemma fps_const_mult_right:
  "f * fps_const (c::'a::{comm_monoid_add,mult_zero}) = Abs_fps (\<lambda>n. f$n * c)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_right)

lemma fps_mult_left_const_nth [simp]:
  "(fps_const (c::'a::{comm_monoid_add,mult_zero}) * f)$n = c* f$n"
  by (simp add: fps_mult_nth mult_delta_left)

lemma fps_mult_right_const_nth [simp]:
  "(f * fps_const (c::'a::{comm_monoid_add,mult_zero}))$n = f$n * c"
  by (simp add: fps_mult_nth mult_delta_right)

lemma fps_const_power [simp]: "fps_const c ^ n = fps_const (c^n)"
  by (induct n) auto


subsection \<open>Formal power series form an integral domain\<close>

instance fps :: (ring) ring ..

instance fps :: (comm_ring) comm_ring ..

instance fps :: (ring_1) ring_1 ..

instance fps :: (comm_ring_1) comm_ring_1 ..

instance fps :: (semiring_no_zero_divisors) semiring_no_zero_divisors
proof
  fix a b :: "'a fps"
  assume "a \<noteq> 0" and "b \<noteq> 0"
  hence "(a * b) $ (subdegree a + subdegree b) \<noteq> 0" by simp
  thus "a * b \<noteq> 0" using fps_nonzero_nth by fast
qed

instance fps :: (semiring_1_no_zero_divisors) semiring_1_no_zero_divisors ..

instance fps :: ("{cancel_semigroup_add,semiring_no_zero_divisors_cancel}")
  semiring_no_zero_divisors_cancel
proof
  fix a b c :: "'a fps"
  show "(a * c = b * c) = (c = 0 \<or> a = b)"
  proof
    assume ab: "a * c = b * c"
    have "c \<noteq> 0 \<Longrightarrow> a = b"
    proof (rule fps_ext)
      fix n
      assume c: "c \<noteq> 0"
      show "a $ n = b $ n"
      proof (induct n rule: nat_less_induct)
        case (1 n)
        with ab c show ?case
          using fps_mult_nth_conv_upto_subdegree_right[of a c "subdegree c + n"]
                fps_mult_nth_conv_upto_subdegree_right[of b c "subdegree c + n"]
          by    (cases n) auto
      qed
    qed
    thus "c = 0 \<or> a = b" by fast
  qed auto
  show "(c * a = c * b) = (c = 0 \<or> a = b)"
  proof
    assume ab: "c * a = c * b"
    have "c \<noteq> 0 \<Longrightarrow> a = b"
    proof (rule fps_ext)
      fix n
      assume c: "c \<noteq> 0"
      show "a $ n = b $ n"
      proof (induct n rule: nat_less_induct)
        case (1 n)
        moreover have "\<forall>i\<in>{Suc (subdegree c)..subdegree c + n}. subdegree c + n - i < n" by auto
        ultimately show ?case
          using ab c fps_mult_nth_conv_upto_subdegree_left[of c a "subdegree c + n"]
                fps_mult_nth_conv_upto_subdegree_left[of c b "subdegree c + n"]
          by    (simp add: sum.atLeast_Suc_atMost)
      qed
    qed    
    thus "c = 0 \<or> a = b" by fast
  qed auto
qed

instance fps :: (ring_no_zero_divisors) ring_no_zero_divisors ..

instance fps :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..

instance fps :: (idom) idom ..

lemma fps_numeral_fps_const: "numeral k = fps_const (numeral k)"
  by (induct k) (simp_all only: numeral.simps fps_const_1_eq_1 fps_const_add [symmetric])

lemmas numeral_fps_const = fps_numeral_fps_const

lemma neg_numeral_fps_const:
  "(- numeral k :: 'a :: ring_1 fps) = fps_const (- numeral k)"
  by (simp add: numeral_fps_const)

lemma fps_numeral_nth: "numeral n $ i = (if i = 0 then numeral n else 0)"
  by (simp add: numeral_fps_const)

lemma fps_numeral_nth_0 [simp]: "numeral n $ 0 = numeral n"
  by (simp add: numeral_fps_const)

lemma subdegree_numeral [simp]: "subdegree (numeral n) = 0"
  by (simp add: numeral_fps_const)

lemma fps_of_nat: "fps_const (of_nat c) = of_nat c"
  by (induction c) (simp_all add: fps_const_add [symmetric] del: fps_const_add)

lemma fps_of_int: "fps_const (of_int c) = of_int c"
  by (induction c) (simp_all add: fps_const_minus [symmetric] fps_of_nat fps_const_neg [symmetric] 
                             del: fps_const_minus fps_const_neg)

lemma fps_nth_of_nat [simp]:
  "(of_nat c) $ n = (if n=0 then of_nat c else 0)"
  by (simp add: fps_of_nat[symmetric])

lemma fps_nth_of_int [simp]:
  "(of_int c) $ n = (if n=0 then of_int c else 0)"
  by (simp add: fps_of_int[symmetric])

lemma fps_mult_of_nat_nth [simp]:
  shows "(of_nat k * f) $ n = of_nat k * f$n"
  and   "(f * of_nat k ) $ n = f$n * of_nat k"
  by    (simp_all add: fps_of_nat[symmetric])

lemma fps_mult_of_int_nth [simp]:
  shows "(of_int k * f) $ n = of_int k * f$n"
  and   "(f * of_int k ) $ n = f$n * of_int k"
  by    (simp_all add: fps_of_int[symmetric])

lemma numeral_neq_fps_zero [simp]: "(numeral f :: 'a :: field_char_0 fps) \<noteq> 0"
proof
  assume "numeral f = (0 :: 'a fps)"
  from arg_cong[of _ _ "\<lambda>F. F $ 0", OF this] show False by simp
qed 

lemma subdegree_power_ge:
  "f^n \<noteq> 0 \<Longrightarrow> subdegree (f^n) \<ge> n * subdegree f"
proof (induct n)
  case (Suc n) thus ?case using fps_mult_subdegree_ge by fastforce
qed simp

lemma fps_pow_nth_below_subdegree:
  "k < n * subdegree f \<Longrightarrow> (f^n) $ k = 0"
proof (cases "f^n = 0")
  case False
  assume "k < n * subdegree f"
  with False have "k < subdegree (f^n)" using subdegree_power_ge[of f n] by simp
  thus "(f^n) $ k = 0" by auto
qed simp

lemma fps_pow_base [simp]:
  "(f ^ n) $ (n * subdegree f) = (f $ subdegree f) ^ n"
proof (induct n)
  case (Suc n)
  show ?case
  proof (cases "Suc n * subdegree f < subdegree f + subdegree (f^n)")
    case True with Suc show ?thesis
      by (auto simp: fps_mult_nth_eq0 distrib_right)
  next
    case False
    hence "\<forall>i\<in>{Suc (subdegree f)..Suc n * subdegree f - subdegree (f ^ n)}.
            f ^ n $ (Suc n * subdegree f - i) = 0"
     by (auto simp: fps_pow_nth_below_subdegree)
   with False Suc show ?thesis
      using fps_mult_nth_conv_inside_subdegrees[of f "f^n" "Suc n * subdegree f"]
            sum.atLeast_Suc_atMost[of
              "subdegree f"
              "Suc n * subdegree f - subdegree (f ^ n)"
              "\<lambda>i. f $ i * f ^ n $ (Suc n * subdegree f - i)"
            ]
      by    simp
  qed
qed simp

lemma subdegree_power_eqI:
  fixes f :: "'a::semiring_1 fps"
  shows "(f $ subdegree f) ^ n \<noteq> 0 \<Longrightarrow> subdegree (f ^ n) = n * subdegree f"
proof (induct n)
  case (Suc n)
  from Suc have 1: "subdegree (f ^ n) = n * subdegree f" by fastforce
  with Suc(2) have "f $ subdegree f * f ^ n $ subdegree (f ^ n) \<noteq> 0" by simp
  with 1 show ?case using subdegree_mult'[of f "f^n"] by simp
qed simp

lemma subdegree_power [simp]:
  "subdegree ((f :: ('a :: semiring_1_no_zero_divisors) fps) ^ n) = n * subdegree f"
  by (cases "f = 0"; induction n) simp_all


subsection \<open>The efps_Xtractor series fps_X\<close>

lemma minus_one_power_iff: "(- (1::'a::ring_1)) ^ n = (if even n then 1 else - 1)"
  by (induct n) auto

definition "fps_X = Abs_fps (\<lambda>n. if n = 1 then 1 else 0)"

lemma subdegree_fps_X [simp]: "subdegree (fps_X :: ('a :: zero_neq_one) fps) = 1"
  by (auto intro!: subdegreeI simp: fps_X_def)

lemma fps_X_mult_nth [simp]:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "(fps_X * f) $ n = (if n = 0 then 0 else f $ (n - 1))"
proof (cases n)
  case (Suc m)
  moreover have "(fps_X * f) $ Suc m = f $ (Suc m - 1)"
  proof (cases m)
    case 0 thus ?thesis using fps_mult_nth_1[of "fps_X" f] by (simp add: fps_X_def)
  next
    case (Suc k) thus ?thesis by (simp add: fps_mult_nth fps_X_def sum.atLeast_Suc_atMost)
  qed
  ultimately show ?thesis by simp
qed (simp add: fps_X_def)

lemma fps_X_mult_right_nth [simp]:
  fixes a :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "(a * fps_X) $ n = (if n = 0 then 0 else a $ (n - 1))"
proof (cases n)
  case (Suc m)
  moreover have "(a * fps_X) $ Suc m = a $ (Suc m - 1)"
  proof (cases m)
    case 0 thus ?thesis using fps_mult_nth_1[of a "fps_X"] by (simp add: fps_X_def)
  next
    case (Suc k)
    hence "(a * fps_X) $ Suc m = (\<Sum>i=0..k. a$i * fps_X$(Suc m - i)) + a$(Suc k)"
      by (simp add: fps_mult_nth fps_X_def)
    moreover have "\<forall>i\<in>{0..k}. a$i * fps_X$(Suc m - i) = 0" by (auto simp: Suc fps_X_def)
    ultimately show ?thesis by (simp add: Suc)
  qed
  ultimately show ?thesis by simp
qed (simp add: fps_X_def)

lemma fps_mult_fps_X_commute:
  fixes a :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "fps_X * a = a * fps_X" 
  by (simp add: fps_eq_iff)

lemma fps_mult_fps_X_power_commute: "fps_X ^ k * a = a * fps_X ^ k"
proof (induct k)
  case (Suc k)
  hence "fps_X ^ Suc k * a = a * fps_X * fps_X ^ k"
    by (simp add: mult.assoc fps_mult_fps_X_commute[symmetric])
  thus ?case by (simp add: mult.assoc)
qed simp

lemma fps_subdegree_mult_fps_X:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  assumes "f \<noteq> 0"
  shows   "subdegree (fps_X * f) = subdegree f + 1"
  and     "subdegree (f * fps_X) = subdegree f + 1"
proof-
  show "subdegree (fps_X * f) = subdegree f + 1"
  proof (intro subdegreeI)
    fix i :: nat assume i: "i < subdegree f + 1"
    show "(fps_X * f) $ i = 0"
    proof (cases "i=0")
      case False with i show ?thesis by (simp add: nth_less_subdegree_zero)
    next
      case True thus ?thesis using fps_X_mult_nth[of f i] by simp
    qed
  qed (simp add: assms)
  thus "subdegree (f * fps_X) = subdegree f + 1"
    by (simp add: fps_mult_fps_X_commute)
qed

lemma fps_mult_fps_X_nonzero:
  fixes   f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  assumes "f \<noteq> 0"
  shows   "fps_X * f \<noteq> 0"
  and     "f * fps_X \<noteq> 0"
  using   assms fps_subdegree_mult_fps_X[of f]
          fps_nonzero_subdegree_nonzeroI[of "fps_X * f"]
          fps_nonzero_subdegree_nonzeroI[of "f * fps_X"]
  by      auto

lemma fps_mult_fps_X_power_nonzero:
  assumes "f \<noteq> 0"
  shows   "fps_X ^ n * f \<noteq> 0"
  and     "f * fps_X ^ n \<noteq> 0"
proof -
  show "fps_X ^ n * f \<noteq> 0"
    by (induct n) (simp_all add: assms mult.assoc fps_mult_fps_X_nonzero(1))
  thus "f * fps_X ^ n \<noteq> 0"
    by (simp add: fps_mult_fps_X_power_commute)
qed

lemma fps_X_power_iff: "fps_X ^ n = Abs_fps (\<lambda>m. if m = n then 1 else 0)"
  by (induction n) (auto simp: fps_eq_iff)

lemma fps_X_nth[simp]: "fps_X$n = (if n = 1 then 1 else 0)"
  by (simp add: fps_X_def)

lemma fps_X_power_nth[simp]: "(fps_X^k) $n = (if n = k then 1 else 0)"
  by (simp add: fps_X_power_iff)

lemma fps_X_power_subdegree: "subdegree (fps_X^n) = n"
  by (auto intro: subdegreeI)

lemma fps_X_power_mult_nth:
  "(fps_X^k * f) $ n = (if n < k then 0 else f $ (n - k))"
  by  (cases "n<k")
      (simp_all add: fps_mult_nth_conv_upto_subdegree_left fps_X_power_subdegree sum.atLeast_Suc_atMost)

lemma fps_X_power_mult_right_nth:
  "(f * fps_X^k) $ n = (if n < k then 0 else f $ (n - k))"
  using fps_mult_fps_X_power_commute[of k f] fps_X_power_mult_nth[of k f] by simp

lemma fps_subdegree_mult_fps_X_power:
  assumes "f \<noteq> 0"
  shows   "subdegree (fps_X ^ n * f) = subdegree f + n"
  and     "subdegree (f * fps_X ^ n) = subdegree f + n"
proof -
  from assms show "subdegree (fps_X ^ n * f) = subdegree f + n"
    by (induct n)
       (simp_all add: algebra_simps fps_subdegree_mult_fps_X(1) fps_mult_fps_X_power_nonzero(1))
  thus "subdegree (f * fps_X ^ n) = subdegree f + n"
    by (simp add: fps_mult_fps_X_power_commute)
qed

lemma fps_mult_fps_X_plus_1_nth:
  "((1+fps_X)*a) $n = (if n = 0 then (a$n :: 'a::semiring_1) else a$n + a$(n - 1))"
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
  also have "\<dots> = (if n = 0 then a$n else a$n + a$(n - 1))"
    by (simp add: Suc)
  finally show ?thesis .
qed

lemma fps_mult_right_fps_X_plus_1_nth:
  fixes a :: "'a :: semiring_1 fps"
  shows "(a*(1+fps_X)) $ n = (if n = 0 then a$n else a$n + a$(n - 1))"
  using fps_mult_fps_X_plus_1_nth
  by    (simp add: distrib_left fps_mult_fps_X_commute distrib_right)

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

lemma fps_X_neq_numeral [simp]: "fps_X \<noteq> numeral c"
  by (simp only: numeral_fps_const fps_X_neq_fps_const) simp

lemma fps_X_pow_eq_fps_X_pow_iff [simp]: "fps_X ^ m = fps_X ^ n \<longleftrightarrow> m = n"
proof
  assume "(fps_X :: 'a fps) ^ m = fps_X ^ n"
  hence "(fps_X :: 'a fps) ^ m $ m = fps_X ^ n $ m" by (simp only:)
  thus "m = n" by (simp split: if_split_asm)
qed simp_all


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

lemma fps_shift_fps_X [simp]:
  "n \<ge> 1 \<Longrightarrow> fps_shift n fps_X = (if n = 1 then 1 else 0)"
  by (intro fps_ext) (auto simp: fps_X_def)

lemma fps_shift_fps_X_power [simp]:
  "n \<le> m \<Longrightarrow> fps_shift n (fps_X ^ m) = fps_X ^ (m - n)"
 by (intro fps_ext) auto

lemma fps_shift_subdegree [simp]:
  "n \<le> subdegree f \<Longrightarrow> subdegree (fps_shift n f) = subdegree f - n"
  by (cases "f=0") (auto intro: subdegreeI simp: nth_less_subdegree_zero)

lemma fps_shift_fps_shift:
  "fps_shift (m + n) f = fps_shift m (fps_shift n f)"
  by (rule fps_ext) (simp add: add_ac)

lemma fps_shift_fps_shift_reorder:
  "fps_shift m (fps_shift n f) = fps_shift n (fps_shift m f)"
  using fps_shift_fps_shift[of m n f] fps_shift_fps_shift[of n m f] by (simp add: add.commute)

lemma fps_shift_rev_shift:
  "m \<le> n \<Longrightarrow> fps_shift n (Abs_fps (\<lambda>k. if k<m then 0 else f $ (k-m))) = fps_shift (n-m) f"
  "m > n \<Longrightarrow> fps_shift n (Abs_fps (\<lambda>k. if k<m then 0 else f $ (k-m))) =
    Abs_fps (\<lambda>k. if k<m-n then 0 else f $ (k-(m-n)))"
proof -
  assume "m \<le> n"
  thus "fps_shift n (Abs_fps (\<lambda>k. if k<m then 0 else f $ (k-m))) = fps_shift (n-m) f"
    by (intro fps_ext) auto
next
  assume mn: "m > n"
  hence "\<And>k. k \<ge> m-n \<Longrightarrow> k+n-m = k - (m-n)" by auto
  thus
    "fps_shift n (Abs_fps (\<lambda>k. if k<m then 0 else f $ (k-m))) =
      Abs_fps (\<lambda>k. if k<m-n then 0 else f $ (k-(m-n)))"
    by (intro fps_ext) auto
qed

lemma fps_shift_add:
  "fps_shift n (f + g) = fps_shift n f + fps_shift n g"
  by (simp add: fps_eq_iff)

lemma fps_shift_diff:
  "fps_shift n (f - g) = fps_shift n f - fps_shift n g"
  by (auto intro: fps_ext)

lemma fps_shift_uminus:
  "fps_shift n (-f) = - fps_shift n f"
  by (auto intro: fps_ext)

lemma fps_shift_mult:
  assumes "n \<le> subdegree (g :: 'b :: {comm_monoid_add, mult_zero} fps)"
  shows "fps_shift n (h*g) = h * fps_shift n g"
proof-
  have case1: "\<And>a b::'b fps. 1 \<le> subdegree b \<Longrightarrow> fps_shift 1 (a*b) = a * fps_shift 1 b"
  proof (rule fps_ext)
    fix a b :: "'b fps"
    and n :: nat
    assume b: "1 \<le> subdegree b"
    have "\<And>i. i \<le> n \<Longrightarrow> n + 1 - i = (n-i) + 1"
      by (simp add: algebra_simps)
    with b show "fps_shift 1 (a*b) $ n = (a * fps_shift 1 b) $ n"
      by (simp add: fps_mult_nth nth_less_subdegree_zero)
  qed
  have "n \<le> subdegree g \<Longrightarrow> fps_shift n (h*g) = h * fps_shift n g"
  proof (induct n)
    case (Suc n)
    have "fps_shift (Suc n) (h*g) = fps_shift 1 (fps_shift n (h*g))"
      by (simp add: fps_shift_fps_shift[symmetric])
    also have "\<dots> = h * (fps_shift 1 (fps_shift n g))"
      using Suc case1 by force
    finally show ?case by (simp add: fps_shift_fps_shift[symmetric])
  qed simp
  with assms show ?thesis by fast
qed

lemma fps_shift_mult_right_noncomm:
  assumes "n \<le> subdegree (g :: 'b :: {comm_monoid_add, mult_zero} fps)"
  shows "fps_shift n (g*h) = fps_shift n g * h"
proof-
  have case1: "\<And>a b::'b fps. 1 \<le> subdegree a \<Longrightarrow> fps_shift 1 (a*b) = fps_shift 1 a * b"
  proof (rule fps_ext)
    fix a b :: "'b fps"
    and n :: nat
    assume "1 \<le> subdegree a"
    hence "fps_shift 1 (a*b) $ n = (\<Sum>i=Suc 0..Suc n. a$i * b$(n+1-i))"
      using sum.atLeast_Suc_atMost[of 0 "n+1" "\<lambda>i. a$i * b$(n+1-i)"]
      by    (simp add: fps_mult_nth nth_less_subdegree_zero)
    thus "fps_shift 1 (a*b) $ n = (fps_shift 1 a * b) $ n"
      using sum.shift_bounds_cl_Suc_ivl[of "\<lambda>i. a$i * b$(n+1-i)" 0 n]
      by    (simp add: fps_mult_nth)
  qed
  have "n \<le> subdegree g \<Longrightarrow> fps_shift n (g*h) = fps_shift n g * h"
  proof (induct n)
    case (Suc n)
    have "fps_shift (Suc n) (g*h) = fps_shift 1 (fps_shift n (g*h))"
      by (simp add: fps_shift_fps_shift[symmetric])
    also have "\<dots> = (fps_shift 1 (fps_shift n g)) * h"
      using Suc case1 by force
    finally show ?case by (simp add: fps_shift_fps_shift[symmetric])
  qed simp
  with assms show ?thesis by fast
qed

lemma fps_shift_mult_right:
  assumes "n \<le> subdegree (g :: 'b :: comm_semiring_0 fps)"
  shows   "fps_shift n (g*h) = h * fps_shift n g"
  by      (simp add: assms fps_shift_mult_right_noncomm mult.commute)

lemma fps_shift_mult_both:
  fixes   f g :: "'a::{comm_monoid_add, mult_zero} fps"
  assumes "m \<le> subdegree f" "n \<le> subdegree g"
  shows   "fps_shift m f * fps_shift n g = fps_shift (m+n) (f*g)"
  using   assms
  by      (simp add: fps_shift_mult fps_shift_mult_right_noncomm fps_shift_fps_shift)

lemma fps_shift_subdegree_zero_iff [simp]:
  "fps_shift (subdegree f) f = 0 \<longleftrightarrow> f = 0"
  by (subst (1) nth_subdegree_zero_iff[symmetric], cases "f = 0")
     (simp_all del: nth_subdegree_zero_iff)

lemma fps_shift_times_fps_X:
  fixes f g :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "1 \<le> subdegree f \<Longrightarrow> fps_shift 1 f * fps_X = f"
  by (intro fps_ext) (simp add: nth_less_subdegree_zero)

lemma fps_shift_times_fps_X' [simp]:
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "fps_shift 1 (f * fps_X) = f"
  by (intro fps_ext) (simp add: nth_less_subdegree_zero)

lemma fps_shift_times_fps_X'':
  fixes f :: "'a::{comm_monoid_add,mult_zero,monoid_mult} fps"
  shows "1 \<le> n \<Longrightarrow> fps_shift n (f * fps_X) = fps_shift (n - 1) f"
  by (intro fps_ext) (simp add: nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power:
  "n \<le> subdegree f \<Longrightarrow> fps_shift n f * fps_X ^ n = f"
  by (intro fps_ext) (simp add: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power' [simp]:
  "fps_shift n (f * fps_X^n) = f"
  by (intro fps_ext) (simp add: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power'':
  "m \<le> n \<Longrightarrow> fps_shift n (f * fps_X^m) = fps_shift (n - m) f"
  by (intro fps_ext) (simp add: fps_X_power_mult_right_nth nth_less_subdegree_zero)

lemma fps_shift_times_fps_X_power''':
  "m > n \<Longrightarrow> fps_shift n (f * fps_X^m) = f * fps_X^(m - n)"
proof (cases "f=0")
  case False
  assume m: "m>n"
  hence "m = n + (m-n)" by auto
  with False m show ?thesis
    using power_add[of "fps_X::'a fps" n "m-n"]
          fps_shift_mult_right_noncomm[of n "f * fps_X^n" "fps_X^(m-n)"]
    by    (simp add: mult.assoc fps_subdegree_mult_fps_X_power(2))
qed simp

lemma subdegree_decompose:
  "f = fps_shift (subdegree f) f * fps_X ^ subdegree f"
  by (rule fps_ext) (auto simp: fps_X_power_mult_right_nth)

lemma subdegree_decompose':
  "n \<le> subdegree f \<Longrightarrow> f = fps_shift n f * fps_X^n"
  by (rule fps_ext) (auto simp: fps_X_power_mult_right_nth intro!: nth_less_subdegree_zero)

instantiation fps :: (zero) unit_factor
begin
definition fps_unit_factor_def [simp]:
  "unit_factor f = fps_shift (subdegree f) f"
instance ..
end

lemma fps_unit_factor_zero_iff: "unit_factor (f::'a::zero fps) = 0 \<longleftrightarrow> f = 0"
  by simp

lemma fps_unit_factor_nth_0: "f \<noteq> 0 \<Longrightarrow> unit_factor f $ 0 \<noteq> 0"
  by simp

lemma fps_X_unit_factor: "unit_factor (fps_X :: 'a :: zero_neq_one fps) = 1"
 by (intro fps_ext) auto

lemma fps_X_power_unit_factor: "unit_factor (fps_X ^ n) = 1"
proof-
  define X :: "'a fps" where "X \<equiv> fps_X"
  hence "unit_factor (X^n) = fps_shift n (X^n)"
    by (simp add: fps_X_power_subdegree)
  moreover have "fps_shift n (X^n) = 1"
    by (auto intro: fps_ext simp: fps_X_power_iff X_def)
  ultimately show ?thesis by (simp add: X_def)
qed

lemma fps_unit_factor_decompose:
  "f = unit_factor f * fps_X ^ subdegree f"
  by (simp add: subdegree_decompose)

lemma fps_unit_factor_decompose':
  "f = fps_X ^ subdegree f * unit_factor f"
  using fps_unit_factor_decompose by (simp add: fps_mult_fps_X_power_commute)

lemma fps_unit_factor_uminus:
  "unit_factor (-f) = - unit_factor (f::'a::group_add fps)"
  by    (simp add: fps_shift_uminus)

lemma fps_unit_factor_shift:
  assumes "n \<le> subdegree f"
  shows   "unit_factor (fps_shift n f) = unit_factor f"
  by      (simp add: assms fps_shift_fps_shift[symmetric])

lemma fps_unit_factor_mult_fps_X:
  fixes f :: "'a::{comm_monoid_add,monoid_mult,mult_zero} fps"
  shows "unit_factor (fps_X * f) = unit_factor f"
  and   "unit_factor (f * fps_X) = unit_factor f"
proof -
  show "unit_factor (fps_X * f) = unit_factor f"
    by (cases "f=0") (auto intro: fps_ext simp: fps_subdegree_mult_fps_X(1))
  thus "unit_factor (f * fps_X) = unit_factor f" by (simp add: fps_mult_fps_X_commute)
qed

lemma fps_unit_factor_mult_fps_X_power:
  shows "unit_factor (fps_X ^ n * f) = unit_factor f"
  and   "unit_factor (f * fps_X ^ n) = unit_factor f"
proof -
  show "unit_factor (fps_X ^ n * f) = unit_factor f"
  proof (induct n)
    case (Suc m) thus ?case
      using fps_unit_factor_mult_fps_X(1)[of "fps_X ^ m * f"] by (simp add: mult.assoc)
  qed simp
  thus "unit_factor (f * fps_X ^ n) = unit_factor f"
    by (simp add: fps_mult_fps_X_power_commute)
qed

lemma fps_unit_factor_mult_unit_factor:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fps"
  shows "unit_factor (f * unit_factor g) = unit_factor (f * g)"
  and   "unit_factor (unit_factor f * g) = unit_factor (f * g)"
proof -
  show "unit_factor (f * unit_factor g) = unit_factor (f * g)"
  proof (cases "f*g = 0")
    case False thus ?thesis
      using fps_mult_subdegree_ge[of f g] fps_unit_factor_shift[of "subdegree g" "f*g"]
      by    (simp add: fps_shift_mult)
  next
    case True
    moreover have "f * unit_factor g = fps_shift (subdegree g) (f*g)"
      by (simp add: fps_shift_mult)
    ultimately show ?thesis by simp
  qed
  show "unit_factor (unit_factor f * g) = unit_factor (f * g)"
  proof (cases "f*g = 0")
    case False thus ?thesis
      using fps_mult_subdegree_ge[of f g] fps_unit_factor_shift[of "subdegree f" "f*g"]
      by    (simp add: fps_shift_mult_right_noncomm)
  next
    case True
    moreover have "unit_factor f * g = fps_shift (subdegree f) (f*g)"
      by (simp add: fps_shift_mult_right_noncomm)
    ultimately show ?thesis by simp
  qed
qed

lemma fps_unit_factor_mult_both_unit_factor:
  fixes f g :: "'a::{comm_monoid_add,mult_zero} fps"
  shows "unit_factor (unit_factor f * unit_factor g) = unit_factor (f * g)"
  using fps_unit_factor_mult_unit_factor(1)[of "unit_factor f" g]
        fps_unit_factor_mult_unit_factor(2)[of f g]
  by    simp

lemma fps_unit_factor_mult':
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "f $ subdegree f * g $ subdegree g \<noteq> 0"
  shows   "unit_factor (f * g) = unit_factor f * unit_factor g"
  using   assms
  by      (simp add: subdegree_mult' fps_shift_mult_both)

lemma fps_unit_factor_mult:
  fixes f g :: "'a::semiring_no_zero_divisors fps"
  shows "unit_factor (f * g) = unit_factor f * unit_factor g"
  using fps_unit_factor_mult'[of f g]
  by    (cases "f=0 \<or> g=0") auto

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
      by (intro subdegree_geI) (simp_all add: fps_eq_iff split: if_split_asm)
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
  "fps_shift n f * fps_X^n + fps_cutoff n f = f"
  by (simp add: fps_eq_iff fps_X_power_mult_right_nth)

lemma fps_shift_cutoff':
  "fps_X^n * fps_shift n f + fps_cutoff n f = f"
  by (simp add: fps_eq_iff fps_X_power_mult_nth)

lemma fps_cutoff_left_mult_nth:
  "k < n \<Longrightarrow> (fps_cutoff n f * g) $ k = (f * g) $ k"
  by (simp add: fps_mult_nth)

lemma fps_cutoff_right_mult_nth:
  assumes "k < n"
  shows   "(f * fps_cutoff n g) $ k = (f * g) $ k"
proof-
  from assms have "\<forall>i\<in>{0..k}. fps_cutoff n g $ (k - i) = g $ (k - i)" by auto
  thus ?thesis by (simp add: fps_mult_nth)
qed

subsection \<open>Formal Power series form a metric space\<close>

instantiation fps :: ("{minus,zero}") dist
begin

definition
  dist_fps_def: "dist (a :: 'a fps) b = (if a = b then 0 else inverse (2 ^ subdegree (a - b)))"

lemma dist_fps_ge0: "dist (a :: 'a fps) b \<ge> 0"
  by (simp add: dist_fps_def)

instance ..

end

instantiation fps :: (group_add) metric_space
begin

definition uniformity_fps_def [code del]:
  "(uniformity :: ('a fps \<times> 'a fps) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_fps_def' [code del]:
  "open (U :: 'a fps set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

lemma dist_fps_sym: "dist (a :: 'a fps) b = dist b a"
  by (simp add: dist_fps_def)

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

declare uniformity_Abort[where 'a="'a :: group_add fps", code]

lemma open_fps_def: "open (S :: 'a::group_add fps set) = (\<forall>a \<in> S. \<exists>r. r >0 \<and> {y. dist y a < r} \<subseteq> S)"
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

lemma fps_sum_rep_nth: "(sum (\<lambda>i. fps_const(a$i)*fps_X^i) {0..m})$n = (if n \<le> m then a$n else 0)"
  by (simp add: fps_sum_nth if_distrib cong del: if_weak_cong)

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
          by (simp add: field_split_simps)
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
            using nn0 by (simp add: field_split_simps)
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


subsection \<open>Inverses and division of formal power series\<close>

declare sum.cong[fundef_cong]

fun fps_left_inverse_constructor ::
  "'a::{comm_monoid_add,times,uminus} fps \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
where
  "fps_left_inverse_constructor f a 0 = a"
| "fps_left_inverse_constructor f a (Suc n) =
    - sum (\<lambda>i. fps_left_inverse_constructor f a i * f$(Suc n - i)) {0..n} * a"

\<comment> \<open>This will construct a left inverse for f in case that x * f$0 = 1\<close>
abbreviation "fps_left_inverse \<equiv> (\<lambda>f x. Abs_fps (fps_left_inverse_constructor f x))"

fun fps_right_inverse_constructor ::
  "'a::{comm_monoid_add,times,uminus} fps \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
where
  "fps_right_inverse_constructor f a 0 = a"
| "fps_right_inverse_constructor f a n =
    - a * sum (\<lambda>i. f$i * fps_right_inverse_constructor f a (n - i)) {1..n}"

\<comment> \<open>This will construct a right inverse for f in case that f$0 * y = 1\<close>
abbreviation "fps_right_inverse \<equiv> (\<lambda>f y. Abs_fps (fps_right_inverse_constructor f y))"

instantiation fps :: ("{comm_monoid_add,inverse,times,uminus}") inverse
begin

\<comment> \<open>For backwards compatibility.\<close>
abbreviation natfun_inverse:: "'a fps \<Rightarrow> nat \<Rightarrow> 'a"
  where "natfun_inverse f \<equiv> fps_right_inverse_constructor f (inverse (f$0))"

definition fps_inverse_def: "inverse f = Abs_fps (natfun_inverse f)"
\<comment> \<open>
  With scalars from a (possibly non-commutative) ring, this defines a right inverse.
  Furthermore, if scalars are of class @{class mult_zero} and satisfy
  condition @{term "inverse 0 = 0"}, then this will evaluate to zero when
  the zeroth term is zero.
\<close>

definition fps_divide_def: "f div g = fps_shift (subdegree g) (f * inverse (unit_factor g))"
\<comment> \<open>
  If scalars are of class @{class mult_zero} and satisfy condition
  @{term "inverse 0 = 0"}, then div by zero will equal zero.
\<close>

instance ..

end

lemma fps_lr_inverse_0_iff:
  "(fps_left_inverse f x) $ 0 = 0 \<longleftrightarrow> x = 0"
  "(fps_right_inverse f x) $ 0 = 0 \<longleftrightarrow> x = 0"
  by auto

lemma fps_inverse_0_iff': "(inverse f) $ 0 = 0 \<longleftrightarrow> inverse (f $ 0) = 0"
  by (simp add: fps_inverse_def fps_lr_inverse_0_iff(2))

lemma fps_inverse_0_iff[simp]: "(inverse f) $ 0 = (0::'a::division_ring) \<longleftrightarrow> f $ 0 = 0"
  by (simp add: fps_inverse_0_iff')

lemma fps_lr_inverse_nth_0:
  "(fps_left_inverse f x) $ 0 = x" "(fps_right_inverse f x) $ 0 = x"
  by auto

lemma fps_inverse_nth_0 [simp]: "(inverse f) $ 0 = inverse (f $ 0)"
  by (simp add: fps_inverse_def)

lemma fps_lr_inverse_starting0:
  fixes f :: "'a::{comm_monoid_add,mult_zero,uminus} fps"
  and   g :: "'b::{ab_group_add,mult_zero} fps"
  shows "fps_left_inverse f 0 = 0"
  and   "fps_right_inverse g 0 = 0"
proof-
  show "fps_left_inverse f 0 = 0"
  proof (rule fps_ext)
    fix n show "fps_left_inverse f 0 $ n = 0 $ n"
      by (cases n) (simp_all add: fps_inverse_def)
  qed
  show "fps_right_inverse g 0 = 0"
  proof (rule fps_ext)
    fix n show "fps_right_inverse g 0 $ n = 0 $ n"
      by (cases n) (simp_all add: fps_inverse_def)
  qed
qed

lemma fps_lr_inverse_eq0_imp_starting0:
  "fps_left_inverse f x = 0 \<Longrightarrow> x = 0"
  "fps_right_inverse f x = 0 \<Longrightarrow> x = 0"
proof-
  assume A: "fps_left_inverse f x = 0"
  have "0 = fps_left_inverse f x $ 0" by (subst A) simp
  thus "x = 0" by simp
next
  assume A: "fps_right_inverse f x = 0"
  have "0 = fps_right_inverse f x $ 0" by (subst A) simp
  thus "x = 0" by simp
qed

lemma fps_lr_inverse_eq_0_iff:
  fixes x :: "'a::{comm_monoid_add,mult_zero,uminus}"
  and   y :: "'b::{ab_group_add,mult_zero}"
  shows "fps_left_inverse f x = 0 \<longleftrightarrow> x = 0"
  and   "fps_right_inverse g y = 0 \<longleftrightarrow> y = 0"
  using fps_lr_inverse_starting0 fps_lr_inverse_eq0_imp_starting0
  by    auto

lemma fps_inverse_eq_0_iff':
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fps"
  shows "inverse f = 0 \<longleftrightarrow> inverse (f $ 0) = 0"
  by    (simp add: fps_inverse_def fps_lr_inverse_eq_0_iff(2))

lemma fps_inverse_eq_0_iff[simp]: "inverse f = (0:: ('a::division_ring) fps) \<longleftrightarrow> f $ 0 = 0"
  using fps_inverse_eq_0_iff'[of f] by simp

lemmas fps_inverse_eq_0' = iffD2[OF fps_inverse_eq_0_iff']
lemmas fps_inverse_eq_0  = iffD2[OF fps_inverse_eq_0_iff]

lemma fps_const_lr_inverse:
  fixes a :: "'a::{ab_group_add,mult_zero}"
  and   b :: "'b::{comm_monoid_add,mult_zero,uminus}"
  shows "fps_left_inverse (fps_const a) x = fps_const x"
  and   "fps_right_inverse (fps_const b) y = fps_const y"
proof-
  show "fps_left_inverse (fps_const a) x = fps_const x"
  proof (rule fps_ext)
    fix n show "fps_left_inverse (fps_const a) x $ n = fps_const x $ n"
      by (cases n) auto
  qed
  show "fps_right_inverse (fps_const b) y = fps_const y"
  proof (rule fps_ext)
    fix n show "fps_right_inverse (fps_const b) y $ n = fps_const y $ n"
      by (cases n) auto
  qed
qed

lemma fps_const_inverse:
  fixes     a :: "'a::{comm_monoid_add,inverse,mult_zero,uminus}"
  shows     "inverse (fps_const a) = fps_const (inverse a)"
  unfolding fps_inverse_def
  by        (simp add: fps_const_lr_inverse(2))

lemma fps_lr_inverse_zero:
  fixes x :: "'a::{ab_group_add,mult_zero}"
  and   y :: "'b::{comm_monoid_add,mult_zero,uminus}"
  shows "fps_left_inverse 0 x = fps_const x"
  and   "fps_right_inverse 0 y = fps_const y"
  using fps_const_lr_inverse[of 0]
  by    simp_all

lemma fps_inverse_zero_conv_fps_const:
  "inverse (0::'a::{comm_monoid_add,mult_zero,uminus,inverse} fps) = fps_const (inverse 0)"
  using fps_lr_inverse_zero(2)[of "inverse (0::'a)"] by (simp add: fps_inverse_def)

lemma fps_inverse_zero':
  assumes "inverse (0::'a::{comm_monoid_add,inverse,mult_zero,uminus}) = 0"
  shows   "inverse (0::'a fps) = 0"
  by      (simp add: assms fps_inverse_zero_conv_fps_const)

lemma fps_inverse_zero [simp]:
  "inverse (0::'a::division_ring fps) = 0"
  by (rule fps_inverse_zero'[OF inverse_zero])

lemma fps_lr_inverse_one:
  fixes x :: "'a::{ab_group_add,mult_zero,one}"
  and   y :: "'b::{comm_monoid_add,mult_zero,uminus,one}"
  shows "fps_left_inverse 1 x = fps_const x"
  and   "fps_right_inverse 1 y = fps_const y"
  using fps_const_lr_inverse[of 1]
  by    simp_all

lemma fps_lr_inverse_one_one:
  "fps_left_inverse 1 1 = (1::'a::{ab_group_add,mult_zero,one} fps)"
  "fps_right_inverse 1 1 = (1::'b::{comm_monoid_add,mult_zero,uminus,one} fps)"
  by (simp_all add: fps_lr_inverse_one)

lemma fps_inverse_one':
  assumes "inverse (1::'a::{comm_monoid_add,inverse,mult_zero,uminus,one}) = 1"
  shows   "inverse (1 :: 'a fps) = 1"
  using   assms fps_lr_inverse_one_one(2)
  by      (simp add: fps_inverse_def)

lemma fps_inverse_one [simp]: "inverse (1 :: 'a :: division_ring fps) = 1"
  by (rule fps_inverse_one'[OF inverse_1])

lemma fps_lr_inverse_minus:
  fixes f :: "'a::ring_1 fps"
  shows "fps_left_inverse (-f) (-x) = - fps_left_inverse f x"
  and   "fps_right_inverse (-f) (-x) = - fps_right_inverse f x"
proof-

  show "fps_left_inverse (-f) (-x) = - fps_left_inverse f x"
  proof (intro fps_ext)
    fix n show "fps_left_inverse (-f) (-x) $ n = - fps_left_inverse f x $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) thus ?case by (cases n) (simp_all add: sum_negf algebra_simps)
    qed
  qed

  show "fps_right_inverse (-f) (-x) = - fps_right_inverse f x"
  proof (intro fps_ext)
    fix n show "fps_right_inverse (-f) (-x) $ n = - fps_right_inverse f x $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) show ?case
      proof (cases n)
        case (Suc m)
        with 1 have
          "\<forall>i\<in>{1..Suc m}. fps_right_inverse (-f) (-x) $ (Suc m - i) =
            - fps_right_inverse f x $ (Suc m - i)"
          by auto
        with Suc show ?thesis by (simp add: sum_negf algebra_simps)
      qed simp
    qed
  qed

qed

lemma fps_inverse_minus [simp]: "inverse (-f) = -inverse (f :: 'a :: division_ring fps)"
  by (simp add: fps_inverse_def fps_lr_inverse_minus(2))

lemma fps_left_inverse:
  fixes   f :: "'a::ring_1 fps"
  assumes f0: "x * f$0 = 1"
  shows   "fps_left_inverse f x * f = 1"
proof (rule fps_ext)
  fix n show "(fps_left_inverse f x * f) $ n = 1 $ n"
    by (cases n) (simp_all add: f0 fps_mult_nth mult.assoc)
qed

lemma fps_right_inverse:
  fixes   f :: "'a::ring_1 fps"
  assumes f0: "f$0 * y = 1"
  shows   "f * fps_right_inverse f y = 1"
proof (rule fps_ext)
  fix n
  show "(f * fps_right_inverse f y) $ n = 1 $ n"
  proof (cases n)
    case (Suc k)
    moreover from Suc have "fps_right_inverse f y $ n =
            - y * sum (\<lambda>i. f$i * fps_right_inverse_constructor f y (n - i)) {1..n}"
      by simp
    hence
      "(f * fps_right_inverse f y) $ n =
        - 1 * sum (\<lambda>i. f$i * fps_right_inverse_constructor f y (n - i)) {1..n} +
        sum (\<lambda>i. f$i * (fps_right_inverse_constructor f y (n - i))) {1..n}"
      by (simp add: fps_mult_nth sum.atLeast_Suc_atMost mult.assoc f0[symmetric])
    thus "(f * fps_right_inverse f y) $ n = 1 $ n" by (simp add: Suc)
  qed (simp add: f0 fps_inverse_def)
qed

\<comment> \<open>
  It is possible in a ring for an element to have a left inverse but not a right inverse, or
  vice versa. But when an element has both, they must be the same.
\<close>
lemma fps_left_inverse_eq_fps_right_inverse:
  fixes   f :: "'a::ring_1 fps"
  assumes f0: "x * f$0 = 1" "f $ 0 * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fps_left_inverse f x = fps_right_inverse f y"
proof-
  from f0(2) have "f * fps_right_inverse f y = 1"
      by (simp add: fps_right_inverse)
  hence "fps_left_inverse f x * f * fps_right_inverse f y = fps_left_inverse f x"
    by (simp add: mult.assoc)
  moreover from f0(1) have
    "fps_left_inverse f x * f * fps_right_inverse f y = fps_right_inverse f y"
    by (simp add: fps_left_inverse)
  ultimately show ?thesis by simp
qed

lemma fps_left_inverse_eq_fps_right_inverse_comm:
  fixes   f :: "'a::comm_ring_1 fps"
  assumes f0: "x * f$0 = 1"
  shows   "fps_left_inverse f x = fps_right_inverse f x"
  using   assms fps_left_inverse_eq_fps_right_inverse[of x f x]
  by      (simp add: mult.commute)

lemma fps_left_inverse':
  fixes   f :: "'a::ring_1 fps"
  assumes "x * f$0 = 1" "f$0 * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fps_right_inverse f y * f = 1"
  using   assms fps_left_inverse_eq_fps_right_inverse[of x f y] fps_left_inverse[of x f]
  by      simp

lemma fps_right_inverse':
  fixes   f :: "'a::ring_1 fps"
  assumes "x * f$0 = 1" "f$0 * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "f * fps_left_inverse f x = 1"
  using   assms fps_left_inverse_eq_fps_right_inverse[of x f y] fps_right_inverse[of f y]
  by      simp

lemma inverse_mult_eq_1 [intro]:
  assumes "f$0 \<noteq> (0::'a::division_ring)"
  shows   "inverse f * f = 1"
  using   fps_left_inverse'[of "inverse (f$0)"]
  by      (simp add: assms fps_inverse_def)

lemma inverse_mult_eq_1':
  assumes "f$0 \<noteq> (0::'a::division_ring)"
  shows   "f * inverse f = 1"
  using   assms fps_right_inverse
  by      (force simp: fps_inverse_def)

lemma fps_mult_left_inverse_unit_factor:
  fixes   f :: "'a::ring_1 fps"
  assumes "x * f $ subdegree f = 1"
  shows   "fps_left_inverse (unit_factor f) x * f = fps_X ^ subdegree f"
proof-
  have
    "fps_left_inverse (unit_factor f) x * f =
      fps_left_inverse (unit_factor f) x * unit_factor f * fps_X ^ subdegree f"
    using fps_unit_factor_decompose[of f] by (simp add: mult.assoc)
  with assms show ?thesis by (simp add: fps_left_inverse)
qed

lemma fps_mult_right_inverse_unit_factor:
  fixes   f :: "'a::ring_1 fps"
  assumes "f $ subdegree f * y = 1"
  shows   "f * fps_right_inverse (unit_factor f) y = fps_X ^ subdegree f"
proof-
  have
    "f * fps_right_inverse (unit_factor f) y =
      fps_X ^ subdegree f * (unit_factor f * fps_right_inverse (unit_factor f) y)"
    using fps_unit_factor_decompose'[of f] by (simp add: mult.assoc[symmetric])
  with assms show ?thesis by (simp add: fps_right_inverse)
qed

lemma fps_mult_right_inverse_unit_factor_divring:
  "(f :: 'a::division_ring fps) \<noteq> 0 \<Longrightarrow> f * inverse (unit_factor f) = fps_X ^ subdegree f"
  using   fps_mult_right_inverse_unit_factor[of f]
  by      (simp add: fps_inverse_def)

lemma fps_left_inverse_idempotent_ring1:
  fixes   f :: "'a::ring_1 fps"
  assumes "x * f$0 = 1" "y * x = 1"
  \<comment> \<open>These assumptions imply y equals f$0, but no need to assume that.\<close>
  shows   "fps_left_inverse (fps_left_inverse f x) y = f"
proof-
  from assms(1) have
    "fps_left_inverse (fps_left_inverse f x) y * fps_left_inverse f x * f =
      fps_left_inverse (fps_left_inverse f x) y"
    by (simp add: fps_left_inverse mult.assoc)
  moreover from assms(2) have
    "fps_left_inverse (fps_left_inverse f x) y * fps_left_inverse f x = 1"
    by (simp add: fps_left_inverse)
  ultimately show ?thesis by simp
qed

lemma fps_left_inverse_idempotent_comm_ring1:
  fixes   f :: "'a::comm_ring_1 fps"
  assumes "x * f$0 = 1"
  shows   "fps_left_inverse (fps_left_inverse f x) (f$0) = f"
  using   assms fps_left_inverse_idempotent_ring1[of x f "f$0"]
  by      (simp add: mult.commute)

lemma fps_right_inverse_idempotent_ring1:
  fixes   f :: "'a::ring_1 fps"
  assumes "f$0 * x = 1" "x * y = 1"
  \<comment> \<open>These assumptions imply y equals f$0, but no need to assume that.\<close>
  shows   "fps_right_inverse (fps_right_inverse f x) y = f"
proof-
  from assms(1) have "f * (fps_right_inverse f x * fps_right_inverse (fps_right_inverse f x) y) =
      fps_right_inverse (fps_right_inverse f x) y"
    by (simp add: fps_right_inverse mult.assoc[symmetric])
  moreover from assms(2) have
    "fps_right_inverse f x * fps_right_inverse (fps_right_inverse f x) y = 1"
    by (simp add: fps_right_inverse)
  ultimately show ?thesis by simp
qed

lemma fps_right_inverse_idempotent_comm_ring1:
  fixes   f :: "'a::comm_ring_1 fps"
  assumes "f$0 * x = 1"
  shows   "fps_right_inverse (fps_right_inverse f x) (f$0) = f"
  using   assms fps_right_inverse_idempotent_ring1[of f x "f$0"]
  by      (simp add: mult.commute)

lemma fps_inverse_idempotent[intro, simp]:
  "f$0 \<noteq> (0::'a::division_ring) \<Longrightarrow> inverse (inverse f) = f"
  using fps_right_inverse_idempotent_ring1[of f]
  by    (simp add: fps_inverse_def)

lemma fps_lr_inverse_unique_ring1:
  fixes   f g :: "'a :: ring_1 fps"
  assumes fg: "f * g = 1" "g$0 * f$0 = 1"
  shows   "fps_left_inverse g (f$0) = f"
  and     "fps_right_inverse f (g$0) = g"
proof-

  show "fps_left_inverse g (f$0) = f"
  proof (intro fps_ext)
    fix n show "fps_left_inverse g (f$0) $ n = f $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) show ?case
      proof (cases n)
        case (Suc k)
        hence "\<forall>i\<in>{0..k}. fps_left_inverse g (f$0) $ i = f $ i" using 1 by simp
        hence "fps_left_inverse g (f$0) $ Suc k = f $ Suc k - 1 $ Suc k * f$0"
          by (simp add: fps_mult_nth fg(1)[symmetric] distrib_right mult.assoc fg(2))
        with Suc show ?thesis by simp
      qed simp
    qed
  qed

  show "fps_right_inverse f (g$0) = g"
  proof (intro fps_ext)
    fix n show "fps_right_inverse f (g$0) $ n = g $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) show ?case
      proof (cases n)
        case (Suc k)
        hence "\<forall>i\<in>{1..Suc k}. fps_right_inverse f (g$0) $ (Suc k - i) = g $ (Suc k - i)"
          using 1 by auto
        hence
          "fps_right_inverse f (g$0) $ Suc k = 1 * g $ Suc k - g$0 * 1 $ Suc k"
          by (simp add: fps_mult_nth fg(1)[symmetric] algebra_simps fg(2)[symmetric] sum.atLeast_Suc_atMost)
        with Suc show ?thesis by simp
      qed simp
    qed
  qed

qed

lemma fps_lr_inverse_unique_divring:
  fixes   f g :: "'a ::division_ring fps"
  assumes fg: "f * g = 1"
  shows   "fps_left_inverse g (f$0) = f"
  and     "fps_right_inverse f (g$0) = g"
proof-
  from fg have "f$0 * g$0 = 1" using fps_mult_nth_0[of f g] by simp
  hence "g$0 * f$0 = 1" using inverse_unique[of "f$0"] left_inverse[of "f$0"] by force
  thus "fps_left_inverse g (f$0) = f" "fps_right_inverse f (g$0) = g"
    using fg fps_lr_inverse_unique_ring1 by auto
qed

lemma fps_inverse_unique:
  fixes   f g :: "'a :: division_ring fps"
  assumes fg: "f * g = 1"
  shows   "inverse f = g"
proof -
  from fg have if0: "inverse (f$0) = g$0" "f$0 \<noteq> 0"
    using inverse_unique[of "f$0"] fps_mult_nth_0[of f g] by auto
  with fg have "fps_right_inverse f (g$0) = g"
    using left_inverse[of "f$0"] by (intro fps_lr_inverse_unique_ring1(2)) simp_all
  with if0(1) show ?thesis by (simp add: fps_inverse_def)
qed

lemma inverse_fps_numeral:
  "inverse (numeral n :: ('a :: field_char_0) fps) = fps_const (inverse (numeral n))"
  by (intro fps_inverse_unique fps_ext) (simp_all add: fps_numeral_nth)

lemma inverse_fps_of_nat:
  "inverse (of_nat n :: 'a :: {semiring_1,times,uminus,inverse} fps) =
    fps_const (inverse (of_nat n))"
  by (simp add: fps_of_nat fps_const_inverse[symmetric])

lemma fps_lr_inverse_mult_ring1:
  fixes   f g :: "'a::ring_1 fps"
  assumes x: "x * f$0 = 1" "f$0 * x = 1"
  and     y: "y * g$0 = 1" "g$0 * y = 1"
  shows   "fps_left_inverse (f * g) (y*x) = fps_left_inverse g y * fps_left_inverse f x"
  and     "fps_right_inverse (f * g) (y*x) = fps_right_inverse g y * fps_right_inverse f x"
proof -
  define h where "h \<equiv> fps_left_inverse g y * fps_left_inverse f x"
  hence h0: "h$0 = y*x" by simp
  have "fps_left_inverse (f*g) (h$0) = h"
  proof (intro fps_lr_inverse_unique_ring1(1))
    from h_def
      have  "h * (f * g) = fps_left_inverse g y * (fps_left_inverse f x * f) * g"
      by    (simp add: mult.assoc)
    thus "h * (f * g) = 1"
      using fps_left_inverse[OF x(1)] fps_left_inverse[OF y(1)] by simp
    from h_def have "(f*g)$0 * h$0 = f$0 * 1 * x"
      by (simp add: mult.assoc y(2)[symmetric])
    with x(2) show "(f * g) $ 0 * h $ 0 = 1" by simp
  qed
  with h_def
    show  "fps_left_inverse (f * g) (y*x) = fps_left_inverse g y * fps_left_inverse f x"
    by    simp
next
  define h where "h \<equiv> fps_right_inverse g y * fps_right_inverse f x"
  hence h0: "h$0 = y*x" by simp
  have "fps_right_inverse (f*g) (h$0) = h"
  proof (intro fps_lr_inverse_unique_ring1(2))
    from h_def
      have  "f * g * h = f * (g * fps_right_inverse g y) * fps_right_inverse f x"
      by    (simp add: mult.assoc)
    thus "f * g * h = 1"
      using fps_right_inverse[OF x(2)] fps_right_inverse[OF y(2)] by simp
    from h_def have "h$0 * (f*g)$0 = y * 1 * g$0"
      by (simp add: mult.assoc x(1)[symmetric])
    with y(1) show "h$0 * (f*g)$0  = 1" by simp
  qed
  with h_def
    show  "fps_right_inverse (f * g) (y*x) = fps_right_inverse g y * fps_right_inverse f x"
    by    simp
qed

lemma fps_lr_inverse_mult_divring:
  fixes f g :: "'a::division_ring fps"
  shows "fps_left_inverse (f * g) (inverse ((f*g)$0)) =
          fps_left_inverse g (inverse (g$0)) * fps_left_inverse f (inverse (f$0))"
  and   "fps_right_inverse (f * g) (inverse ((f*g)$0)) =
          fps_right_inverse g (inverse (g$0)) * fps_right_inverse f (inverse (f$0))"
proof-
  show "fps_left_inverse (f * g) (inverse ((f*g)$0)) =
          fps_left_inverse g (inverse (g$0)) * fps_left_inverse f (inverse (f$0))"
  proof (cases "f$0 = 0 \<or> g$0 = 0")
    case True
    hence "fps_left_inverse (f * g) (inverse ((f*g)$0)) = 0"
      by (simp add: fps_lr_inverse_eq_0_iff(1))
    moreover from True have
      "fps_left_inverse g (inverse (g$0)) * fps_left_inverse f (inverse (f$0)) = 0"
      by (auto simp: fps_lr_inverse_eq_0_iff(1))
    ultimately show ?thesis by simp
  next
    case False
    hence "fps_left_inverse (f * g) (inverse (g$0) * inverse (f$0)) =
            fps_left_inverse g (inverse (g$0)) * fps_left_inverse f (inverse (f$0))"
      by  (intro fps_lr_inverse_mult_ring1(1)) simp_all
    with False show ?thesis by (simp add: nonzero_inverse_mult_distrib)
  qed
  show "fps_right_inverse (f * g) (inverse ((f*g)$0)) =
          fps_right_inverse g (inverse (g$0)) * fps_right_inverse f (inverse (f$0))"
  proof (cases "f$0 = 0 \<or> g$0 = 0")
    case True
    from True have "fps_right_inverse (f * g) (inverse ((f*g)$0)) = 0"
      by (simp add: fps_lr_inverse_eq_0_iff(2))
    moreover from True have
      "fps_right_inverse g (inverse (g$0)) * fps_right_inverse f (inverse (f$0)) = 0"
      by (auto simp: fps_lr_inverse_eq_0_iff(2))
    ultimately show ?thesis by simp
  next
    case False
    hence "fps_right_inverse (f * g) (inverse (g$0) * inverse (f$0)) =
            fps_right_inverse g (inverse (g$0)) * fps_right_inverse f (inverse (f$0))"
      by  (intro fps_lr_inverse_mult_ring1(2)) simp_all
    with False show ?thesis by (simp add: nonzero_inverse_mult_distrib)
  qed
qed

lemma fps_inverse_mult_divring:
  "inverse (f * g) = inverse g * inverse (f :: 'a::division_ring fps)"
  using fps_lr_inverse_mult_divring(2) by (simp add: fps_inverse_def)

lemma fps_inverse_mult: "inverse (f * g :: 'a::field fps) = inverse f * inverse g"
  by (simp add: fps_inverse_mult_divring)

lemma fps_lr_inverse_gp_ring1:
  fixes   ones ones_inv :: "'a :: ring_1 fps"
  defines "ones \<equiv> Abs_fps (\<lambda>n. 1)"
  and     "ones_inv \<equiv> Abs_fps (\<lambda>n. if n=0 then 1 else if n=1 then - 1 else 0)"
  shows   "fps_left_inverse ones 1 = ones_inv"
  and     "fps_right_inverse ones 1 = ones_inv"
proof-
  show "fps_left_inverse ones 1 = ones_inv"
  proof (rule fps_ext)
    fix n
    show "fps_left_inverse ones 1 $ n = ones_inv $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) show ?case
      proof (cases n)
        case (Suc m)
        have m: "n = Suc m" by fact
        moreover have "fps_left_inverse ones 1 $ Suc m = ones_inv $ Suc m"
        proof (cases m)
          case (Suc k) thus ?thesis
            using Suc m 1 by (simp add: ones_def ones_inv_def sum.atLeast_Suc_atMost)
        qed (simp add: ones_def ones_inv_def)
        ultimately show ?thesis by simp
      qed (simp add: ones_inv_def)
    qed
  qed
  moreover have "fps_right_inverse ones 1 = fps_left_inverse ones 1"
    by (auto intro: fps_left_inverse_eq_fps_right_inverse[symmetric] simp: ones_def)
  ultimately show "fps_right_inverse ones 1 = ones_inv" by simp
qed

lemma fps_lr_inverse_gp_ring1':
  fixes   ones :: "'a :: ring_1 fps"
  defines "ones \<equiv> Abs_fps (\<lambda>n. 1)"
  shows   "fps_left_inverse ones 1 = 1 - fps_X"
  and     "fps_right_inverse ones 1 = 1 - fps_X"
proof-
  define ones_inv :: "'a :: ring_1 fps" 
    where "ones_inv \<equiv> Abs_fps (\<lambda>n. if n=0 then 1 else if n=1 then - 1 else 0)"
  hence "fps_left_inverse ones 1 = ones_inv"
  and   "fps_right_inverse ones 1 = ones_inv"
    using ones_def fps_lr_inverse_gp_ring1 by auto
  thus "fps_left_inverse ones 1 = 1 - fps_X"
  and   "fps_right_inverse ones 1 = 1 - fps_X"
    by (auto intro: fps_ext simp: ones_inv_def)
qed

lemma fps_inverse_gp:
  "inverse (Abs_fps(\<lambda>n. (1::'a::division_ring))) =
    Abs_fps (\<lambda>n. if n= 0 then 1 else if n=1 then - 1 else 0)"
  using fps_lr_inverse_gp_ring1(2) by (simp add: fps_inverse_def)

lemma fps_inverse_gp': "inverse (Abs_fps (\<lambda>n. 1::'a::division_ring)) = 1 - fps_X"
  by (simp add: fps_inverse_def fps_lr_inverse_gp_ring1'(2))

lemma fps_lr_inverse_one_minus_fps_X:
  fixes   ones :: "'a :: ring_1 fps"
  defines "ones \<equiv> Abs_fps (\<lambda>n. 1)"
  shows "fps_left_inverse (1 - fps_X) 1 = ones"
  and   "fps_right_inverse (1 - fps_X) 1 = ones"
proof-
  have "fps_left_inverse ones 1 = 1 - fps_X"
    using fps_lr_inverse_gp_ring1'(1) by (simp add: ones_def)
  thus "fps_left_inverse (1 - fps_X) 1 = ones"
    using fps_left_inverse_idempotent_ring1[of 1 ones 1] by (simp add: ones_def)
  have "fps_right_inverse ones 1 = 1 - fps_X"
    using fps_lr_inverse_gp_ring1'(2) by (simp add: ones_def)
  thus "fps_right_inverse (1 - fps_X) 1 = ones"
    using fps_right_inverse_idempotent_ring1[of ones 1 1] by (simp add: ones_def)
qed

lemma fps_inverse_one_minus_fps_X:
  fixes   ones :: "'a :: division_ring fps"
  defines "ones \<equiv> Abs_fps (\<lambda>n. 1)"
  shows   "inverse (1 - fps_X) = ones"
  by      (simp add: fps_inverse_def assms fps_lr_inverse_one_minus_fps_X(2))

lemma fps_lr_one_over_one_minus_fps_X_squared:
  shows   "fps_left_inverse ((1 - fps_X)^2) (1::'a::ring_1) = Abs_fps (\<lambda>n. of_nat (n+1))"
          "fps_right_inverse ((1 - fps_X)^2) (1::'a) = Abs_fps (\<lambda>n. of_nat (n+1))"
proof-
  define  f invf2 :: "'a fps"
    where "f \<equiv> (1 - fps_X)"
    and   "invf2 \<equiv> Abs_fps (\<lambda>n. of_nat (n+1))"

  have f2_nth_simps:
    "f^2 $ 1 = - of_nat 2" "f^2 $ 2 = 1" "\<And>n. n>2 \<Longrightarrow> f^2 $ n = 0"
      by (simp_all add: power2_eq_square f_def fps_mult_nth sum.atLeast_Suc_atMost)

  show "fps_left_inverse (f^2) 1 = invf2"
  proof (intro fps_ext)
    fix n show "fps_left_inverse (f^2) 1 $ n = invf2 $ n"
    proof (induct n rule: nat_less_induct)
      case (1 t)
      hence induct_assm:
        "\<And>m. m < t \<Longrightarrow> fps_left_inverse (f\<^sup>2) 1 $ m = invf2 $ m"
        by fast
      show ?case
      proof (cases t)
        case (Suc m)
        have m: "t = Suc m" by fact
        moreover have "fps_left_inverse (f^2) 1 $ Suc m = invf2 $ Suc m"
        proof (cases m)
          case 0 thus ?thesis using f2_nth_simps(1) by (simp add: invf2_def)
        next
          case (Suc l)
          have l: "m = Suc l" by fact
          moreover have "fps_left_inverse (f^2) 1 $ Suc (Suc l) = invf2 $ Suc (Suc l)"
          proof (cases l)
            case 0 thus ?thesis using f2_nth_simps(1,2) by (simp add: Suc_1[symmetric] invf2_def)
          next
            case (Suc k)
            from Suc l m
              have A: "fps_left_inverse (f\<^sup>2) 1 $ Suc (Suc k) = invf2 $ Suc (Suc k)"
              and  B: "fps_left_inverse (f\<^sup>2) 1 $ Suc k = invf2 $ Suc k"
              using induct_assm[of "Suc k"] induct_assm[of "Suc (Suc k)"]
              by    auto
            have times2: "\<And>a::nat. 2*a = a + a" by simp
            have "\<forall>i\<in>{0..k}. (f^2)$(Suc (Suc (Suc k)) - i) = 0"
              using f2_nth_simps(3) by auto
            hence
              "fps_left_inverse (f^2) 1 $ Suc (Suc (Suc k)) =
                fps_left_inverse (f\<^sup>2) 1 $ Suc (Suc k) * of_nat 2 -
                fps_left_inverse (f\<^sup>2) 1 $ Suc k"
              using sum.ub_add_nat f2_nth_simps(1,2) by simp
            also have "\<dots> = of_nat (2 * Suc (Suc (Suc k))) - of_nat (Suc (Suc k))"
              by (subst A, subst B) (simp add: invf2_def mult.commute)
            also have "\<dots> = of_nat (Suc (Suc (Suc k)) + 1)"
              by (subst times2[of "Suc (Suc (Suc k))"]) simp
            finally have
              "fps_left_inverse (f^2) 1 $ Suc (Suc (Suc k)) = invf2 $ Suc (Suc (Suc k))"
               by (simp add: invf2_def)
            with Suc show ?thesis by simp
          qed
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed (simp add: invf2_def)
    qed
  qed

  moreover have "fps_right_inverse (f^2) 1 = fps_left_inverse (f^2) 1"
    by  (auto
          intro: fps_left_inverse_eq_fps_right_inverse[symmetric]
          simp: f_def power2_eq_square
        )
  ultimately show "fps_right_inverse (f^2) 1 = invf2"
    by simp

qed

lemma fps_one_over_one_minus_fps_X_squared':
  assumes "inverse (1::'a::{ring_1,inverse}) = 1"
  shows   "inverse ((1 - fps_X)^2 :: 'a  fps) = Abs_fps (\<lambda>n. of_nat (n+1))"
  using   assms fps_lr_one_over_one_minus_fps_X_squared(2)
  by      (simp add: fps_inverse_def power2_eq_square)

lemma fps_one_over_one_minus_fps_X_squared:
  "inverse ((1 - fps_X)^2 :: 'a :: division_ring fps) = Abs_fps (\<lambda>n. of_nat (n+1))"
  by (rule fps_one_over_one_minus_fps_X_squared'[OF inverse_1])

lemma fps_lr_inverse_fps_X_plus1:
  "fps_left_inverse (1 + fps_X) (1::'a::ring_1) = Abs_fps (\<lambda>n. (-1)^n)"
  "fps_right_inverse (1 + fps_X) (1::'a) = Abs_fps (\<lambda>n. (-1)^n)"
proof-

  show "fps_left_inverse (1 + fps_X) (1::'a) = Abs_fps (\<lambda>n. (-1)^n)"
  proof (rule fps_ext)
    fix n show "fps_left_inverse (1 + fps_X) (1::'a) $ n = Abs_fps (\<lambda>n. (-1)^n) $ n"
    proof (induct n rule: nat_less_induct)
      case (1 n) show ?case
      proof (cases n)
        case (Suc m)
        have m: "n = Suc m" by fact
        from Suc 1 have
          A:  "fps_left_inverse (1 + fps_X) (1::'a) $ n =
                - (\<Sum>i=0..m. (- 1)^i * (1 + fps_X) $ (Suc m - i))"
          by simp
        show ?thesis
        proof (cases m)
          case (Suc l)
          have "\<forall>i\<in>{0..l}. ((1::'a fps) + fps_X) $ (Suc (Suc l) - i) = 0" by auto
          with Suc A m show ?thesis by simp
        qed (simp add: m A)
      qed simp
    qed
  qed

  moreover have
    "fps_right_inverse (1 + fps_X) (1::'a) = fps_left_inverse (1 + fps_X) 1"
    by (intro fps_left_inverse_eq_fps_right_inverse[symmetric]) simp_all
  ultimately show "fps_right_inverse (1 + fps_X) (1::'a) = Abs_fps (\<lambda>n. (-1)^n)" by simp

qed

lemma fps_inverse_fps_X_plus1':
  assumes "inverse (1::'a::{ring_1,inverse}) = 1"
  shows   "inverse (1 + fps_X) = Abs_fps (\<lambda>n. (- (1::'a)) ^ n)"
  using   assms fps_lr_inverse_fps_X_plus1(2)
  by      (simp add: fps_inverse_def)

lemma fps_inverse_fps_X_plus1:
  "inverse (1 + fps_X) = Abs_fps (\<lambda>n. (- (1::'a::division_ring)) ^ n)"
  by (rule fps_inverse_fps_X_plus1'[OF inverse_1])

lemma subdegree_lr_inverse:
  fixes x :: "'a::{comm_monoid_add,mult_zero,uminus}"
  and   y :: "'b::{ab_group_add,mult_zero}"
  shows "subdegree (fps_left_inverse f x) = 0"
  and   "subdegree (fps_right_inverse g y) = 0"
proof-
  show "subdegree (fps_left_inverse f x) = 0"
    using fps_lr_inverse_eq_0_iff(1) subdegree_eq_0_iff by fastforce
  show "subdegree (fps_right_inverse g y) = 0"
    using fps_lr_inverse_eq_0_iff(2) subdegree_eq_0_iff by fastforce
qed

lemma subdegree_inverse [simp]:
  fixes f :: "'a::{ab_group_add,inverse,mult_zero} fps"
  shows "subdegree (inverse f) = 0"
  using subdegree_lr_inverse(2)
  by    (simp add: fps_inverse_def)

lemma fps_div_zero [simp]:
  "0 div (g :: 'a :: {comm_monoid_add,inverse,mult_zero,uminus} fps) = 0"
  by (simp add: fps_divide_def)

lemma fps_div_by_zero':
  fixes   g :: "'a::{comm_monoid_add,inverse,mult_zero,uminus} fps"
  assumes "inverse (0::'a) = 0"
  shows   "g div 0 = 0"
  by      (simp add: fps_divide_def assms fps_inverse_zero')

lemma fps_div_by_zero [simp]: "(g::'a::division_ring fps) div 0 = 0"
  by    (rule fps_div_by_zero'[OF inverse_zero])

lemma fps_divide_unit': "subdegree g = 0 \<Longrightarrow> f div g = f * inverse g"
  by (simp add: fps_divide_def)

lemma fps_divide_unit: "g$0 \<noteq> 0 \<Longrightarrow> f div g = f * inverse g"
  by (intro fps_divide_unit') (simp add: subdegree_eq_0_iff)

lemma fps_divide_nth_0':
  "subdegree (g::'a::division_ring fps) = 0 \<Longrightarrow> (f div g) $ 0 = f $ 0 / (g $ 0)"
  by (simp add: fps_divide_unit' divide_inverse)

lemma fps_divide_nth_0 [simp]:
  "g $ 0 \<noteq> 0 \<Longrightarrow> (f div g) $ 0 = f $ 0 / (g $ 0 :: _ :: division_ring)"
  by (simp add: fps_divide_nth_0')

lemma fps_divide_nth_below:
  fixes f g :: "'a::{comm_monoid_add,uminus,mult_zero,inverse} fps"
  shows "n < subdegree f - subdegree g \<Longrightarrow> (f div g) $ n = 0"
  by    (simp add: fps_divide_def fps_mult_nth_eq0)

lemma fps_divide_nth_base:
  fixes   f g :: "'a::division_ring fps"
  assumes "subdegree g \<le> subdegree f"
  shows   "(f div g) $ (subdegree f - subdegree g) = f $ subdegree f * inverse (g $ subdegree g)"
  by      (simp add: assms fps_divide_def fps_divide_unit')

lemma fps_divide_subdegree_ge:
  fixes   f g :: "'a::{comm_monoid_add,uminus,mult_zero,inverse} fps"
  assumes "f / g \<noteq> 0"
  shows   "subdegree (f / g) \<ge> subdegree f - subdegree g"
  by      (intro subdegree_geI) (simp_all add: assms fps_divide_nth_below)

lemma fps_divide_subdegree:
  fixes   f g :: "'a::division_ring fps"
  assumes "f \<noteq> 0" "g \<noteq> 0" "subdegree g \<le> subdegree f"
  shows   "subdegree (f / g) = subdegree f - subdegree g"
proof (intro antisym)
  from assms have 1: "(f div g) $ (subdegree f - subdegree g) \<noteq> 0"
    using fps_divide_nth_base[of g f] by simp
  thus "subdegree (f / g) \<le> subdegree f - subdegree g" by (intro subdegree_leI) simp
  from 1 have "f / g \<noteq> 0" by (auto intro: fps_nonzeroI)
  thus "subdegree f - subdegree g \<le> subdegree (f / g)" by (rule fps_divide_subdegree_ge)
qed

lemma fps_divide_shift_numer:
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fps"
  assumes "n \<le> subdegree f"
  shows   "fps_shift n f / g = fps_shift n (f/g)"
  using   assms fps_shift_mult_right_noncomm[of n f "inverse (unit_factor g)"]
          fps_shift_fps_shift_reorder[of "subdegree g" n "f * inverse (unit_factor g)"]
  by      (simp add: fps_divide_def)

lemma fps_divide_shift_denom:
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fps"
  assumes "n \<le> subdegree g" "subdegree g \<le> subdegree f"
  shows   "f / fps_shift n g = Abs_fps (\<lambda>k. if k<n then 0 else (f/g) $ (k-n))"
proof (intro fps_ext)
  fix k
  from assms(1) have LHS:
    "(f / fps_shift n g) $ k = (f * inverse (unit_factor g)) $ (k + (subdegree g - n))"
    using fps_unit_factor_shift[of n g]
    by    (simp add: fps_divide_def)
  show "(f / fps_shift n g) $ k = Abs_fps (\<lambda>k. if k<n then 0 else (f/g) $ (k-n)) $ k"
  proof (cases "k<n")
    case True with assms LHS show ?thesis using fps_mult_nth_eq0[of _ f] by simp
  next
    case False
    hence "(f/g) $ (k-n) = (f * inverse (unit_factor g)) $ ((k-n) + subdegree g)"
      by (simp add: fps_divide_def)
    with False LHS assms(1) show ?thesis by auto
  qed
qed

lemma fps_divide_unit_factor_numer:
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fps"
  shows   "unit_factor f / g = fps_shift (subdegree f) (f/g)"
  by      (simp add: fps_divide_shift_numer)

lemma fps_divide_unit_factor_denom:
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fps"
  assumes "subdegree g \<le> subdegree f"
  shows
    "f / unit_factor g = Abs_fps (\<lambda>k. if k<subdegree g then 0 else (f/g) $ (k-subdegree g))"
  by      (simp add: assms fps_divide_shift_denom)

lemma fps_divide_unit_factor_both':
  fixes   f g :: "'a::{inverse,comm_monoid_add,uminus,mult_zero} fps"
  assumes "subdegree g \<le> subdegree f"
  shows   "unit_factor f / unit_factor g = fps_shift (subdegree f - subdegree g) (f / g)"
  using   assms fps_divide_unit_factor_numer[of f "unit_factor g"]
          fps_divide_unit_factor_denom[of g f]
          fps_shift_rev_shift(1)[of "subdegree g" "subdegree f" "f/g"]
  by      simp

lemma fps_divide_unit_factor_both:
  fixes   f g :: "'a::division_ring fps"
  assumes "subdegree g \<le> subdegree f"
  shows   "unit_factor f / unit_factor g = unit_factor (f / g)"
  using   assms fps_divide_unit_factor_both'[of g f] fps_divide_subdegree[of f g]
  by      (cases "f=0 \<or> g=0") auto

lemma fps_divide_self:
  "(f::'a::division_ring fps) \<noteq> 0 \<Longrightarrow> f / f = 1"
  using   fps_mult_right_inverse_unit_factor_divring[of f]
  by      (simp add: fps_divide_def)

lemma fps_divide_add:
  fixes f g h :: "'a::{semiring_0,inverse,uminus} fps"
  shows "(f + g) / h = f / h + g / h"
  by    (simp add: fps_divide_def algebra_simps fps_shift_add)

lemma fps_divide_diff:
  fixes f g h :: "'a::{ring,inverse} fps"
  shows "(f - g) / h = f / h - g / h"
  by    (simp add: fps_divide_def algebra_simps fps_shift_diff)

lemma fps_divide_uminus:
  fixes f g h :: "'a::{ring,inverse} fps"
  shows "(- f) / g = - (f / g)"
  by    (simp add: fps_divide_def algebra_simps fps_shift_uminus)

lemma fps_divide_uminus':
  fixes f g h :: "'a::division_ring fps"
  shows "f / (- g) = - (f / g)"
  by (simp add: fps_divide_def fps_unit_factor_uminus fps_shift_uminus)

lemma fps_divide_times:
  fixes   f g h :: "'a::{semiring_0,inverse,uminus} fps"
  assumes "subdegree h \<le> subdegree g"
  shows   "(f * g) / h = f * (g / h)"
  using   assms fps_mult_subdegree_ge[of g "inverse (unit_factor h)"]
          fps_shift_mult[of "subdegree h" "g * inverse (unit_factor h)" f]
  by      (fastforce simp add: fps_divide_def mult.assoc)

lemma fps_divide_times2:
  fixes   f g h :: "'a::{comm_semiring_0,inverse,uminus} fps"
  assumes "subdegree h \<le> subdegree f"
  shows   "(f * g) / h = (f / h) * g"
  using   assms fps_divide_times[of h f g]
  by      (simp add: mult.commute)

lemma fps_times_divide_eq:
  fixes   f g :: "'a::field fps"
  assumes "g \<noteq> 0" and "subdegree f \<ge> subdegree g"
  shows   "f div g * g = f"
  using   assms fps_divide_times2[of g f g]
  by      (simp add: fps_divide_times fps_divide_self)

lemma fps_divide_times_eq:
  "(g :: 'a::division_ring fps) \<noteq> 0 \<Longrightarrow> (f * g) div g = f"
  by (simp add: fps_divide_times fps_divide_self)

lemma fps_divide_by_mult':
  fixes   f g h :: "'a :: division_ring fps"
  assumes "subdegree h \<le> subdegree f"
  shows   "f / (g * h) = f / h / g"
proof (cases "f=0 \<or> g=0 \<or> h=0")
  case False with assms show ?thesis
    using fps_unit_factor_mult[of g h]
    by    (auto simp:
            fps_divide_def fps_shift_fps_shift fps_inverse_mult_divring mult.assoc
            fps_shift_mult_right_noncomm
          )
qed auto

lemma fps_divide_by_mult:
  fixes   f g h :: "'a :: field fps"
  assumes "subdegree g \<le> subdegree f"
  shows   "f / (g * h) = f / g / h"
proof-
  have "f / (g * h) = f / (h * g)" by (simp add: mult.commute)
  also have "\<dots> = f / g / h" using fps_divide_by_mult'[OF assms] by simp
  finally show ?thesis by simp
qed

lemma fps_divide_cancel:
  fixes   f g h :: "'a :: division_ring fps"
  shows "h \<noteq> 0 \<Longrightarrow> (f * h) div (g * h) = f div g"
  by    (cases "f=0")
        (auto simp: fps_divide_by_mult' fps_divide_times_eq)

lemma fps_divide_1':
  fixes   a :: "'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one,monoid_mult} fps"
  assumes "inverse (1::'a) = 1"
  shows   "a / 1 = a"
  using   assms fps_inverse_one' fps_one_mult(2)[of a]
  by      (force simp: fps_divide_def)

lemma fps_divide_1 [simp]: "(a :: 'a::division_ring fps) / 1 = a"
  by (rule fps_divide_1'[OF inverse_1])

lemma fps_divide_X':
  fixes   f :: "'a::{comm_monoid_add,inverse,mult_zero,uminus,zero_neq_one,monoid_mult} fps"
  assumes "inverse (1::'a) = 1"
  shows   "f / fps_X = fps_shift 1 f"
  using   assms fps_one_mult(2)[of f]
  by      (simp add: fps_divide_def fps_X_unit_factor fps_inverse_one')

lemma fps_divide_X [simp]: "a / fps_X = fps_shift 1 (a::'a::division_ring fps)"
  by (rule fps_divide_X'[OF inverse_1])

lemma fps_divide_X_power':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "inverse (1::'a) = 1"
  shows   "f / (fps_X ^ n) = fps_shift n f"
  using   fps_inverse_one'[OF assms] fps_one_mult(2)[of f]
  by      (simp add: fps_divide_def fps_X_power_subdegree)

lemma fps_divide_X_power [simp]: "a / (fps_X ^ n) = fps_shift n (a::'a::division_ring fps)"
  by (rule fps_divide_X_power'[OF inverse_1])

lemma fps_divide_shift_denom_conv_times_fps_X_power:
  fixes   f g :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "n \<le> subdegree g" "subdegree g \<le> subdegree f"
  shows   "f / fps_shift n g = f / g * fps_X ^ n"
  using   assms
  by      (intro fps_ext) (simp_all add: fps_divide_shift_denom fps_X_power_mult_right_nth)

lemma fps_divide_unit_factor_denom_conv_times_fps_X_power:
  fixes   f g :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "subdegree g \<le> subdegree f"
  shows   "f / unit_factor g = f / g * fps_X ^ subdegree g"
  by      (simp add: assms fps_divide_shift_denom_conv_times_fps_X_power)

lemma fps_shift_altdef':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "inverse (1::'a) = 1"
  shows   "fps_shift n f = f div fps_X^n"
  using   assms 
  by      (simp add:
            fps_divide_def fps_X_power_subdegree fps_X_power_unit_factor fps_inverse_one'
          )

lemma fps_shift_altdef:
  "fps_shift n f = (f :: 'a :: division_ring fps) div fps_X^n"
  by (rule fps_shift_altdef'[OF inverse_1])

lemma fps_div_fps_X_power_nth':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "inverse (1::'a) = 1"
  shows   "(f div fps_X^n) $ k = f $ (k + n)"
  using   assms
  by      (simp add: fps_shift_altdef' [symmetric])

lemma fps_div_fps_X_power_nth: "((f :: 'a :: division_ring fps) div fps_X^n) $ k = f $ (k + n)"
  by (rule fps_div_fps_X_power_nth'[OF inverse_1])

lemma fps_div_fps_X_nth':
  fixes   f :: "'a::{semiring_1,inverse,uminus} fps"
  assumes "inverse (1::'a) = 1"
  shows   "(f div fps_X) $ k = f $ Suc k"
  using   assms fps_div_fps_X_power_nth'[of f 1]
  by      simp

lemma fps_div_fps_X_nth: "((f :: 'a :: division_ring fps) div fps_X) $ k = f $ Suc k"
  by (rule fps_div_fps_X_nth'[OF inverse_1])

lemma divide_fps_const':
  fixes c :: "'a :: {inverse,comm_monoid_add,uminus,mult_zero}"
  shows   "f / fps_const c = f * fps_const (inverse c)"
  by      (simp add: fps_divide_def fps_const_inverse)

lemma divide_fps_const [simp]:
  fixes c :: "'a :: {comm_semiring_0,inverse,uminus}"
  shows "f / fps_const c = fps_const (inverse c) * f"
  by    (simp add: divide_fps_const' mult.commute)

lemma fps_const_divide: "fps_const (x :: _ :: division_ring) / fps_const y = fps_const (x / y)"
  by (simp add: fps_divide_def fps_const_inverse divide_inverse)

lemma fps_numeral_divide_divide:
  "x / numeral b / numeral c = (x / numeral (b * c) :: 'a :: field fps)"
  by (simp add: fps_divide_by_mult[symmetric])

lemma fps_numeral_mult_divide:
  "numeral b * x / numeral c = (numeral b / numeral c * x :: 'a :: field fps)"
  by (simp add: fps_divide_times2)

lemmas fps_numeral_simps = 
  fps_numeral_divide_divide fps_numeral_mult_divide inverse_fps_numeral neg_numeral_fps_const

lemma fps_is_left_unit_iff_zeroth_is_left_unit:
  fixes f :: "'a :: ring_1 fps"
  shows "(\<exists>g. 1 = f * g) \<longleftrightarrow> (\<exists>k. 1 = f$0 * k)"
proof
  assume "\<exists>g. 1 = f * g"
  then obtain g where "1 = f * g" by fast
  hence "1 = f$0 * g$0" using fps_mult_nth_0[of f g] by simp
  thus "\<exists>k. 1 = f$0 * k" by auto
next
  assume "\<exists>k. 1 = f$0 * k"
  then obtain k where "1 = f$0 * k" by fast
  hence "1 = f * fps_right_inverse f k"
    using fps_right_inverse by simp
  thus "\<exists>g. 1 = f * g" by fast
qed

lemma fps_is_right_unit_iff_zeroth_is_right_unit:
  fixes f :: "'a :: ring_1 fps"
  shows "(\<exists>g. 1 = g * f) \<longleftrightarrow> (\<exists>k. 1 = k * f$0)"
proof
  assume "\<exists>g. 1 = g * f"
  then obtain g where "1 = g * f" by fast
  hence "1 = g$0 * f$0" using fps_mult_nth_0[of g f] by simp
  thus "\<exists>k. 1 = k * f$0" by auto
next
  assume "\<exists>k. 1 = k * f$0"
  then obtain k where "1 = k * f$0" by fast
  hence "1 = fps_left_inverse f k * f"
    using fps_left_inverse by simp
  thus "\<exists>g. 1 = g * f" by fast
qed

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

lemma subdegree_eq_0_left:
  fixes   f :: "'a::{comm_monoid_add,zero_neq_one,mult_zero} fps"
  assumes "\<exists>g. 1 = f * g"
  shows   "subdegree f = 0"
proof (intro subdegree_eq_0)
  from assms obtain g where "1 = f * g" by fast
  hence "f$0 * g$0 = 1" using fps_mult_nth_0[of f g] by simp
  thus "f$0 \<noteq> 0" by auto
qed

lemma subdegree_eq_0_right:
  fixes   f :: "'a::{comm_monoid_add,zero_neq_one,mult_zero} fps"
  assumes "\<exists>g. 1 = g * f"
  shows   "subdegree f = 0"
proof (intro subdegree_eq_0)
  from assms obtain g where "1 = g * f" by fast
  hence "g$0 * f$0 = 1" using fps_mult_nth_0[of g f] by simp
  thus "f$0 \<noteq> 0" by auto
qed

lemma subdegree_eq_0' [simp]: "(f :: 'a :: field fps) dvd 1 \<Longrightarrow> subdegree f = 0"
  by simp

lemma fps_dvd1_left_trivial_unit_factor:
  fixes   f :: "'a::{comm_monoid_add, zero_neq_one, mult_zero} fps"
  assumes "\<exists>g. 1 = f * g"
  shows   "unit_factor f = f"
  using   assms subdegree_eq_0_left
  by      fastforce

lemma fps_dvd1_right_trivial_unit_factor:
  fixes   f :: "'a::{comm_monoid_add, zero_neq_one, mult_zero} fps"
  assumes "\<exists>g. 1 = g * f"
  shows   "unit_factor f = f"
  using   assms subdegree_eq_0_right
  by      fastforce

lemma fps_dvd1_trivial_unit_factor:
  "(f :: 'a::comm_semiring_1 fps) dvd 1 \<Longrightarrow> unit_factor f = f"
  unfolding dvd_def by (rule fps_dvd1_left_trivial_unit_factor) simp

lemma fps_unit_dvd_left:
  fixes   f :: "'a :: division_ring fps"
  assumes "f $ 0 \<noteq> 0"
  shows   "\<exists>g. 1 = f * g"
  using   assms fps_is_left_unit_iff_zeroth_is_left_unit right_inverse
  by      fastforce

lemma fps_unit_dvd_right:
  fixes   f :: "'a :: division_ring fps"
  assumes "f $ 0 \<noteq> 0"
  shows   "\<exists>g. 1 = g * f"
  using   assms fps_is_right_unit_iff_zeroth_is_right_unit left_inverse
  by      fastforce

lemma fps_unit_dvd [simp]: "(f $ 0 :: 'a :: field) \<noteq> 0 \<Longrightarrow> f dvd g"
  using fps_unit_dvd_left dvd_trans[of f 1] by simp

lemma dvd_left_imp_subdegree_le:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "\<exists>k. g = f * k" "g \<noteq> 0"
  shows   "subdegree f \<le> subdegree g"
  using   assms fps_mult_subdegree_ge
  by      fastforce

lemma dvd_right_imp_subdegree_le:
  fixes   f g :: "'a::{comm_monoid_add,mult_zero} fps"
  assumes "\<exists>k. g = k * f" "g \<noteq> 0"
  shows   "subdegree f \<le> subdegree g"
  using   assms fps_mult_subdegree_ge
  by      fastforce

lemma dvd_imp_subdegree_le:
  "f dvd g \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> subdegree f \<le> subdegree g"
  using dvd_left_imp_subdegree_le by fast

lemma subdegree_le_imp_dvd_left_ring1:
  fixes   f g :: "'a :: ring_1 fps"
  assumes "\<exists>y. f $ subdegree f * y = 1" "subdegree f \<le> subdegree g"
  shows   "\<exists>k. g = f * k"
proof-
  define h :: "'a fps" where "h \<equiv> fps_X ^ (subdegree g - subdegree f)"
  from assms(1) obtain y where "f $ subdegree f * y = 1" by fast
  hence "unit_factor f $ 0 * y = 1" by simp
  from this obtain k where "1 = unit_factor f * k"
    using fps_is_left_unit_iff_zeroth_is_left_unit[of "unit_factor f"] by auto
  hence "fps_X ^ subdegree f = fps_X ^ subdegree f * unit_factor f * k"
    by (simp add: mult.assoc)
  moreover have "fps_X ^ subdegree f * unit_factor f = f"
    by (rule fps_unit_factor_decompose'[symmetric])
  ultimately have
    "fps_X ^ (subdegree f + (subdegree g - subdegree f)) = f * k * h"
    by (simp add: power_add h_def)
  hence "g = f * (k * h * unit_factor g)"
    using fps_unit_factor_decompose'[of g]
    by    (simp add: assms(2) mult.assoc)
  thus ?thesis by fast
qed

lemma subdegree_le_imp_dvd_left_divring:
  fixes   f g :: "'a :: division_ring fps"
  assumes "f \<noteq> 0" "subdegree f \<le> subdegree g"
  shows   "\<exists>k. g = f * k"
proof (intro subdegree_le_imp_dvd_left_ring1)
  from assms(1) have "f $ subdegree f \<noteq> 0" by simp
  thus "\<exists>y. f $ subdegree f * y = 1" using right_inverse by blast
qed (rule assms(2))

lemma subdegree_le_imp_dvd_right_ring1:
  fixes   f g :: "'a :: ring_1 fps"
  assumes "\<exists>x. x * f $ subdegree f = 1" "subdegree f \<le> subdegree g"
  shows   "\<exists>k. g = k * f"
proof-
  define h :: "'a fps" where "h \<equiv> fps_X ^ (subdegree g - subdegree f)"
  from assms(1) obtain x where "x * f $ subdegree f = 1" by fast
  hence "x * unit_factor f $ 0 = 1" by simp
  from this obtain k where "1 = k * unit_factor f"
    using fps_is_right_unit_iff_zeroth_is_right_unit[of "unit_factor f"] by auto
  hence "fps_X ^ subdegree f = k * (unit_factor f * fps_X ^ subdegree f)"
    by (simp add: mult.assoc[symmetric])
  moreover have "unit_factor f * fps_X ^ subdegree f = f"
    by (rule fps_unit_factor_decompose[symmetric])
  ultimately have "fps_X ^ (subdegree g - subdegree f + subdegree f) = h * k * f"
    by (simp add: power_add h_def mult.assoc)
  hence "g = unit_factor g * h * k * f"
    using fps_unit_factor_decompose[of g]
    by    (simp add: assms(2) mult.assoc)
  thus ?thesis by fast
qed

lemma subdegree_le_imp_dvd_right_divring:
  fixes   f g :: "'a :: division_ring fps"
  assumes "f \<noteq> 0" "subdegree f \<le> subdegree g"
  shows   "\<exists>k. g = k * f"
proof (intro subdegree_le_imp_dvd_right_ring1)
  from assms(1) have "f $ subdegree f \<noteq> 0" by simp
  thus "\<exists>x. x * f $ subdegree f = 1" using left_inverse by blast
qed (rule assms(2))

lemma fps_dvd_iff:
  assumes "(f :: 'a :: field fps) \<noteq> 0" "g \<noteq> 0"
  shows   "f dvd g \<longleftrightarrow> subdegree f \<le> subdegree g"
proof
  assume "subdegree f \<le> subdegree g"
  with assms show "f dvd g"
    using subdegree_le_imp_dvd_left_divring
    by    (auto intro: dvdI)
qed (simp add: assms dvd_imp_subdegree_le)

lemma subdegree_div':
  fixes   p q :: "'a::division_ring fps"
  assumes "\<exists>k. p = k * q"
  shows   "subdegree (p div q) = subdegree p - subdegree q"
proof (cases "p = 0")
  case False
  from assms(1) obtain k where k: "p = k * q" by blast
  with False have "subdegree (p div q) = subdegree k" by (simp add: fps_divide_times_eq)
  moreover have "k $ subdegree k * q $ subdegree q \<noteq> 0"
  proof
    assume "k $ subdegree k * q $ subdegree q = 0"
    hence "k $ subdegree k * q $ subdegree q * inverse (q $ subdegree q) = 0" by simp
    with False k show False by (simp add: mult.assoc)
  qed
  ultimately show ?thesis by (simp add: k subdegree_mult')
qed simp

lemma subdegree_div:
  fixes     p q :: "'a :: field fps"
  assumes   "q dvd p"
  shows     "subdegree (p div q) = subdegree p - subdegree q"
  using     assms
  unfolding dvd_def
  by        (auto intro: subdegree_div')

lemma subdegree_div_unit':
  fixes   p q :: "'a :: {ab_group_add,mult_zero,inverse} fps"
  assumes "q $ 0 \<noteq> 0" "p $ subdegree p * inverse (q $ 0) \<noteq> 0"
  shows   "subdegree (p div q) = subdegree p"
  using   assms subdegree_mult'[of p "inverse q"]
  by      (auto simp add: fps_divide_unit)

lemma subdegree_div_unit'':
  fixes   p q :: "'a :: {ring_no_zero_divisors,inverse} fps"
  assumes "q $ 0 \<noteq> 0" "inverse (q $ 0) \<noteq> 0"
  shows   "subdegree (p div q) = subdegree p"
  by      (cases "p = 0") (auto intro: subdegree_div_unit' simp: assms)

lemma subdegree_div_unit:
  fixes   p q :: "'a :: division_ring fps"
  assumes "q $ 0 \<noteq> 0"
  shows   "subdegree (p div q) = subdegree p"
  by      (intro subdegree_div_unit'') (simp_all add: assms)

instantiation fps :: ("{comm_semiring_1,inverse,uminus}") modulo
begin

definition fps_mod_def:
  "f mod g = (if g = 0 then f else
     let h = unit_factor g in  fps_cutoff (subdegree g) (f * inverse h) * h)"

instance ..

end

lemma fps_mod_zero [simp]:
  "(f::'a::{comm_semiring_1,inverse,uminus} fps) mod 0 = f"
  by (simp add: fps_mod_def)

lemma fps_mod_eq_zero:
  assumes "g \<noteq> 0" and "subdegree f \<ge> subdegree g"
  shows   "f mod g = 0"
proof (cases "f * inverse (unit_factor g) = 0")
  case False
  have "fps_cutoff (subdegree g) (f * inverse (unit_factor g)) = 0"
    using False assms(2) fps_mult_subdegree_ge fps_cutoff_zero_iff by force
  with assms(1) show ?thesis by (simp add: fps_mod_def Let_def)
qed (simp add: assms fps_mod_def)

lemma fps_mod_unit [simp]: "g$0 \<noteq> 0 \<Longrightarrow> f mod g = 0"
  by (intro fps_mod_eq_zero) auto

lemma subdegree_mod:
  assumes "subdegree (f::'a::field fps) < subdegree g"
  shows   "subdegree (f mod g) = subdegree f"
proof (cases "f = 0")
  case False
  with assms show ?thesis
    by  (intro subdegreeI)
        (auto simp: inverse_mult_eq_1 fps_mod_def Let_def fps_cutoff_left_mult_nth mult.assoc)
qed (simp add: fps_mod_def)

instance fps :: (field) idom_modulo
proof

  fix f g :: "'a fps"

  define n where "n = subdegree g"
  define h where "h = f * inverse (unit_factor g)"

  show "f div g * g + f mod g = f"
  proof (cases "g = 0")
    case False
    with n_def h_def have
      "f div g * g + f mod g = (fps_shift n h * fps_X ^ n + fps_cutoff n h) * unit_factor g"
      by (simp add: fps_divide_def fps_mod_def Let_def subdegree_decompose algebra_simps)
    with False show ?thesis
      by (simp add: fps_shift_cutoff h_def inverse_mult_eq_1)
  qed auto

qed (rule fps_divide_times_eq, simp_all add: fps_divide_def)

instantiation fps :: (field) normalization_semidom_multiplicative
begin

definition fps_normalize_def [simp]:
  "normalize f = (if f = 0 then 0 else fps_X ^ subdegree f)"

instance proof
  fix f g :: "'a fps"
  assume "is_unit f"
  thus "unit_factor (f * g) = f * unit_factor g"
    using fps_unit_factor_mult[of f g] by simp
next
  fix f g :: "'a fps"
  show "unit_factor f * normalize f = f"
    by (simp add: fps_shift_times_fps_X_power)
next
  fix f g :: "'a fps"
  show "unit_factor (f * g) = unit_factor f * unit_factor g"
    using fps_unit_factor_mult[of f g] by simp
qed (simp_all add: fps_divide_def Let_def)

end


subsection \<open>Formal power series form a Euclidean ring\<close>

instantiation fps :: (field) euclidean_ring_cancel
begin

definition fps_euclidean_size_def:
  "euclidean_size f = (if f = 0 then 0 else 2 ^ subdegree f)"

instance proof
  fix f g :: "'a fps" assume [simp]: "g \<noteq> 0"
  show "euclidean_size f \<le> euclidean_size (f * g)"
    by (cases "f = 0") (simp_all add: fps_euclidean_size_def)
  show "euclidean_size (f mod g) < euclidean_size g"
  proof (cases "f = 0")
    case True
    then show ?thesis
      by (simp add: fps_euclidean_size_def)
  next
    case False
    then show ?thesis 
      using le_less_linear[of "subdegree g" "subdegree f"]
      by (force simp add: fps_mod_eq_zero fps_euclidean_size_def subdegree_mod)
  qed
next
  fix f g h :: "'a fps" assume [simp]: "h \<noteq> 0"
  show "(h * f) div (h * g) = f div g"
    by (simp add: fps_divide_cancel mult.commute)
  show "(f + g * h) div h = g + f div h"
    by (simp add: fps_divide_add fps_divide_times_eq)
qed (simp add: fps_euclidean_size_def)

end

instance fps :: (field) normalization_euclidean_semiring ..

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
    thus "d dvd fps_X ^ ?m" by (cases "d = 0") (simp_all add: fps_dvd_iff)
  qed (simp_all add: fps_dvd_iff)
qed

lemma fps_gcd_altdef: "gcd f g =
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
    thus "fps_X ^ ?m dvd d" by (cases "d = 0") (simp_all add: fps_dvd_iff)
  qed (simp_all add: fps_dvd_iff)
qed

lemma fps_lcm_altdef: "lcm f g =
  (if f = 0 \<or> g = 0 then 0 else fps_X ^ max (subdegree f) (subdegree g))"
  by (simp add: fps_lcm)

lemma fps_Gcd:
  assumes "A - {0} \<noteq> {}"
  shows   "Gcd A = fps_X ^ (INF f\<in>A-{0}. subdegree f)"
proof (rule sym, rule GcdI)
  fix f assume "f \<in> A"
  thus "fps_X ^ (INF f\<in>A - {0}. subdegree f) dvd f"
    by (cases "f = 0") (auto simp: fps_dvd_iff intro!: cINF_lower)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> d dvd f"
  from assms obtain f where "f \<in> A - {0}" by auto
  with d[of f] have [simp]: "d \<noteq> 0" by auto
  from d assms have "subdegree d \<le> (INF f\<in>A-{0}. subdegree f)"
    by (intro cINF_greatest) (simp_all add: fps_dvd_iff[symmetric])
  with d assms show "d dvd fps_X ^ (INF f\<in>A-{0}. subdegree f)" by (simp add: fps_dvd_iff)
qed simp_all

lemma fps_Gcd_altdef: "Gcd A =
  (if A \<subseteq> {0} then 0 else fps_X ^ (INF f\<in>A-{0}. subdegree f))"
  using fps_Gcd by auto

lemma fps_Lcm:
  assumes "A \<noteq> {}" "0 \<notin> A" "bdd_above (subdegree`A)"
  shows   "Lcm A = fps_X ^ (SUP f\<in>A. subdegree f)"
proof (rule sym, rule LcmI)
  fix f assume "f \<in> A"
  moreover from assms(3) have "bdd_above (subdegree ` A)" by auto
  ultimately show "f dvd fps_X ^ (SUP f\<in>A. subdegree f)" using assms(2)
    by (cases "f = 0") (auto simp: fps_dvd_iff intro!: cSUP_upper)
next
  fix d assume d: "\<And>f. f \<in> A \<Longrightarrow> f dvd d"
  from assms obtain f where f: "f \<in> A" "f \<noteq> 0" by auto
  show "fps_X ^ (SUP f\<in>A. subdegree f) dvd d"
  proof (cases "d = 0")
    assume "d \<noteq> 0"
    moreover from d have "\<And>f. f \<in> A \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> f dvd d" by blast
    ultimately have "subdegree d \<ge> (SUP f\<in>A. subdegree f)" using assms
      by (intro cSUP_least) (auto simp: fps_dvd_iff)
    with \<open>d \<noteq> 0\<close> show ?thesis by (simp add: fps_dvd_iff)
  qed simp_all
qed simp_all

lemma fps_Lcm_altdef:
  "Lcm A =
     (if 0 \<in> A \<or> \<not>bdd_above (subdegree`A) then 0 else
      if A = {} then 1 else fps_X ^ (SUP f\<in>A. subdegree f))"
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

lemma fps_deriv_nth[simp]: "fps_deriv f $ n = of_nat (n + 1) * f $ (n + 1)"
  by (simp add: fps_deriv_def)

lemma fps_0th_higher_deriv: 
  "(fps_deriv ^^ n) f $ 0 = fact n * f $ n"
  by  (induction n arbitrary: f)
      (simp_all add: funpow_Suc_right mult_of_nat_commute algebra_simps del: funpow.simps)

lemma fps_deriv_mult[simp]:
  "fps_deriv (f * g) = f * fps_deriv g + fps_deriv f * g"
proof (intro fps_ext)
  fix n
  have LHS: "fps_deriv (f * g) $ n = (\<Sum>i=0..Suc n. of_nat (n+1) * f$i * g$(Suc n - i))"
    by (simp add: fps_mult_nth sum_distrib_left algebra_simps)

  have "\<forall>i\<in>{1..n}. n - (i - 1) = n - i + 1" by auto
  moreover have
    "(\<Sum>i=0..n. of_nat (i+1) * f$(i+1) * g$(n - i)) =
      (\<Sum>i=1..Suc n. of_nat i * f$i * g$(n - (i - 1)))"
    by (intro sum.reindex_bij_witness[where i="\<lambda>x. x-1" and j="\<lambda>x. x+1"]) auto
  ultimately have
    "(f * fps_deriv g + fps_deriv f * g) $ n =
      of_nat (Suc n) * f$0 * g$(Suc n) +
      (\<Sum>i=1..n. (of_nat (n - i + 1) + of_nat i) * f $ i * g $ (n - i + 1)) +
          of_nat (Suc n) * f$(Suc n) * g$0"
    by (simp add: fps_mult_nth algebra_simps mult_of_nat_commute sum.atLeast_Suc_atMost sum.distrib)
  moreover have
    "\<forall>i\<in>{1..n}.
      (of_nat (n - i + 1) + of_nat i) * f $ i * g $ (n - i + 1) =
      of_nat (n + 1) * f $ i * g $ (Suc n - i)"
  proof
    fix i assume i: "i \<in> {1..n}"
    from i have "of_nat (n - i + 1) + (of_nat i :: 'a) = of_nat (n + 1)"
      using of_nat_add[of "n-i+1" i,symmetric] by simp
    moreover from i have "Suc n - i = n - i + 1" by auto
    ultimately show "(of_nat (n - i + 1) + of_nat i) * f $ i * g $ (n - i + 1) =
            of_nat (n + 1) * f $ i * g $ (Suc n - i)"
      by simp
  qed
  ultimately have
    "(f * fps_deriv g + fps_deriv f * g) $ n =
      (\<Sum>i=0..Suc n. of_nat (Suc n) * f $ i * g $ (Suc n - i))"
    by (simp add: sum.atLeast_Suc_atMost)
  with LHS show "fps_deriv (f * g) $ n = (f * fps_deriv g + fps_deriv f * g) $ n"
    by simp
qed

lemma fps_deriv_fps_X[simp]: "fps_deriv fps_X = 1"
  by (simp add: fps_deriv_def fps_X_def fps_eq_iff)

lemma fps_deriv_neg[simp]:
  "fps_deriv (- (f:: 'a::ring_1 fps)) = - (fps_deriv f)"
  by (simp add: fps_eq_iff fps_deriv_def)

lemma fps_deriv_add[simp]: "fps_deriv (f + g) = fps_deriv f + fps_deriv g"
  by (auto intro: fps_ext simp: algebra_simps)

lemma fps_deriv_sub[simp]:
  "fps_deriv ((f:: 'a::ring_1 fps) - g) = fps_deriv f - fps_deriv g"
  using fps_deriv_add [of f "- g"] by simp

lemma fps_deriv_const[simp]: "fps_deriv (fps_const c) = 0"
  by (simp add: fps_ext fps_deriv_def fps_const_def)

lemma fps_deriv_of_nat [simp]: "fps_deriv (of_nat n) = 0"
  by (simp add: fps_of_nat [symmetric])

lemma fps_deriv_of_int [simp]: "fps_deriv (of_int n) = 0"
  by (simp add: fps_of_int [symmetric])

lemma fps_deriv_numeral [simp]: "fps_deriv (numeral n) = 0"
  by (simp add: numeral_fps_const)    

lemma fps_deriv_mult_const_left[simp]:
  "fps_deriv (fps_const c * f) = fps_const c * fps_deriv f"
  by simp

lemma fps_deriv_linear[simp]:
  "fps_deriv (fps_const a * f + fps_const b * g) =
    fps_const a * fps_deriv f + fps_const b * fps_deriv g"
  by simp

lemma fps_deriv_0[simp]: "fps_deriv 0 = 0"
  by (simp add: fps_deriv_def fps_eq_iff)

lemma fps_deriv_1[simp]: "fps_deriv 1 = 0"
  by (simp add: fps_deriv_def fps_eq_iff)

lemma fps_deriv_mult_const_right[simp]:
  "fps_deriv (f * fps_const c) = fps_deriv f * fps_const c"
  by simp

lemma fps_deriv_sum:
  "fps_deriv (sum f S) = sum (\<lambda>i. fps_deriv (f i)) S"
proof (cases "finite S")
  case False
  then show ?thesis by simp
next
  case True
  show ?thesis by (induct rule: finite_induct [OF True]) simp_all
qed

lemma fps_deriv_eq_0_iff [simp]:
  "fps_deriv f = 0 \<longleftrightarrow> f = fps_const (f$0 :: 'a::{semiring_no_zero_divisors,semiring_char_0})"
proof
  assume f: "fps_deriv f = 0"
  show "f = fps_const (f$0)"
  proof (intro fps_ext)
    fix n show "f $ n = fps_const (f$0) $ n"
    proof (cases n)
      case (Suc m)
      have "(of_nat (Suc m) :: 'a) \<noteq> 0" by (rule of_nat_neq_0)
      with f Suc show ?thesis using fps_deriv_nth[of f] by auto
    qed simp
  qed
next
  show "f = fps_const (f$0) \<Longrightarrow> fps_deriv f = 0" using fps_deriv_const[of "f$0"] by simp
qed

lemma fps_deriv_eq_iff:
  fixes f g :: "'a::{ring_1_no_zero_divisors,semiring_char_0} fps"
  shows "fps_deriv f = fps_deriv g \<longleftrightarrow> (f = fps_const(f$0 - g$0) + g)"
proof -
  have "fps_deriv f = fps_deriv g \<longleftrightarrow> fps_deriv (f - g) = 0"
    using fps_deriv_sub[of f g]
    by simp
  also have "\<dots> \<longleftrightarrow> f - g = fps_const ((f - g) $ 0)"
    unfolding fps_deriv_eq_0_iff ..
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma fps_deriv_eq_iff_ex:
  fixes f g :: "'a::{ring_1_no_zero_divisors,semiring_char_0} fps"
  shows "(fps_deriv f = fps_deriv g) \<longleftrightarrow> (\<exists>c. f = fps_const c + g)"
  by    (auto simp: fps_deriv_eq_iff)


fun fps_nth_deriv :: "nat \<Rightarrow> 'a::semiring_1 fps \<Rightarrow> 'a fps"
where
  "fps_nth_deriv 0 f = f"
| "fps_nth_deriv (Suc n) f = fps_nth_deriv n (fps_deriv f)"

lemma fps_nth_deriv_commute: "fps_nth_deriv (Suc n) f = fps_deriv (fps_nth_deriv n f)"
  by (induct n arbitrary: f) auto

lemma fps_nth_deriv_linear[simp]:
  "fps_nth_deriv n (fps_const a * f + fps_const b * g) =
    fps_const a * fps_nth_deriv n f + fps_const b * fps_nth_deriv n g"
  by (induct n arbitrary: f g) auto

lemma fps_nth_deriv_neg[simp]:
  "fps_nth_deriv n (- (f :: 'a::ring_1 fps)) = - (fps_nth_deriv n f)"
  by (induct n arbitrary: f) simp_all

lemma fps_nth_deriv_add[simp]:
  "fps_nth_deriv n ((f :: 'a::ring_1 fps) + g) = fps_nth_deriv n f + fps_nth_deriv n g"
  using fps_nth_deriv_linear[of n 1 f 1 g] by simp

lemma fps_nth_deriv_sub[simp]:
  "fps_nth_deriv n ((f :: 'a::ring_1 fps) - g) = fps_nth_deriv n f - fps_nth_deriv n g"
  using fps_nth_deriv_add [of n f "- g"] by simp

lemma fps_nth_deriv_0[simp]: "fps_nth_deriv n 0 = 0"
  by (induct n) simp_all

lemma fps_nth_deriv_1[simp]: "fps_nth_deriv n 1 = (if n = 0 then 1 else 0)"
  by (induct n) simp_all

lemma fps_nth_deriv_const[simp]:
  "fps_nth_deriv n (fps_const c) = (if n = 0 then fps_const c else 0)"
  by (cases n) simp_all

lemma fps_nth_deriv_mult_const_left[simp]:
  "fps_nth_deriv n (fps_const c * f) = fps_const c * fps_nth_deriv n f"
  using fps_nth_deriv_linear[of n "c" f 0 0 ] by simp

lemma fps_nth_deriv_mult_const_right[simp]:
  "fps_nth_deriv n (f * fps_const c) = fps_nth_deriv n f * fps_const c"
  by (induct n arbitrary: f) auto

lemma fps_nth_deriv_sum:
  "fps_nth_deriv n (sum f S) = sum (\<lambda>i. fps_nth_deriv n (f i :: 'a::ring_1 fps)) S"
proof (cases "finite S")
  case True
  show ?thesis by (induct rule: finite_induct [OF True]) simp_all
next
  case False
  then show ?thesis by simp
qed

lemma fps_deriv_maclauren_0:
  "(fps_nth_deriv k (f :: 'a::comm_semiring_1 fps)) $ 0 = of_nat (fact k) * f $ k"
  by (induct k arbitrary: f) (simp_all add: field_simps)

lemma fps_deriv_lr_inverse:
  fixes   x y :: "'a::ring_1"
  assumes "x * f$0 = 1" "f$0 * y = 1"
  \<comment> \<open>These assumptions imply x equals y, but no need to assume that.\<close>
  shows   "fps_deriv (fps_left_inverse f x) =
            - fps_left_inverse f x * fps_deriv f * fps_left_inverse f x"
  and     "fps_deriv (fps_right_inverse f y) =
            - fps_right_inverse f y * fps_deriv f * fps_right_inverse f y"
proof-

  define L where "L \<equiv> fps_left_inverse f x"
  hence "fps_deriv (L * f) = 0" using fps_left_inverse[OF assms(1)] by simp
  with assms show "fps_deriv L = - L * fps_deriv f * L"
    using fps_right_inverse'[OF assms]
    by    (simp add: minus_unique mult.assoc L_def)

  define R where "R \<equiv> fps_right_inverse f y"
  hence "fps_deriv (f * R) = 0" using fps_right_inverse[OF assms(2)] by simp
  hence 1: "f * fps_deriv R + fps_deriv f * R = 0" by simp
  have "R * f * fps_deriv R = - R * fps_deriv f * R"
    using iffD2[OF eq_neg_iff_add_eq_0, OF 1] by (simp add: mult.assoc)
  thus "fps_deriv R = - R * fps_deriv f * R"
    using fps_left_inverse'[OF assms] by (simp add: R_def)

qed

lemma fps_deriv_lr_inverse_comm:
  fixes   x :: "'a::comm_ring_1"
  assumes "x * f$0 = 1"
  shows   "fps_deriv (fps_left_inverse f x) = - fps_deriv f * (fps_left_inverse f x)\<^sup>2"
  and     "fps_deriv (fps_right_inverse f x) = - fps_deriv f * (fps_right_inverse f x)\<^sup>2"
  using   assms fps_deriv_lr_inverse[of x f x]
  by      (simp_all add: mult.commute power2_eq_square)

lemma fps_inverse_deriv_divring:
  fixes   a :: "'a::division_ring fps"
  assumes "a$0 \<noteq> 0"
  shows   "fps_deriv (inverse a) = - inverse a * fps_deriv a * inverse a"
  using   assms fps_deriv_lr_inverse(2)[of "inverse (a$0)" a "inverse (a$0)"]
  by      (simp add: fps_inverse_def)

lemma fps_inverse_deriv:
  fixes   a :: "'a::field fps"
  assumes "a$0 \<noteq> 0"
  shows   "fps_deriv (inverse a) = - fps_deriv a * (inverse a)\<^sup>2"
  using   assms fps_deriv_lr_inverse_comm(2)[of "inverse (a$0)" a]
  by      (simp add: fps_inverse_def)

lemma fps_inverse_deriv':
  fixes a :: "'a::field fps"
  assumes a0: "a $ 0 \<noteq> 0"
  shows "fps_deriv (inverse a) = - fps_deriv a / a\<^sup>2"
  using fps_inverse_deriv[OF a0] a0
  by (simp add: fps_divide_unit power2_eq_square fps_inverse_mult)

(* FIXME: The last part of this proof should go through by simp once we have a proper
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
  thus ?thesis by (cases "b = 0") (simp_all add: eq_divide_imp)
qed

lemma fps_nth_deriv_fps_X[simp]: "fps_nth_deriv n fps_X = (if n = 0 then fps_X else if n=1 then 1 else 0)"
  by (cases n) simp_all


subsection \<open>Powers\<close>

lemma fps_power_zeroth: "(a^n) $ 0 = (a$0)^n"
  by (induct n) auto

lemma fps_power_zeroth_eq_one: "a$0 = 1 \<Longrightarrow> a^n $ 0 = 1"
  by (simp add: fps_power_zeroth)

lemma fps_power_first:
  fixes a :: "'a::comm_semiring_1 fps"
  shows "(a^n) $ 1 = of_nat n * (a$0)^(n-1) * a$1"
proof (cases n)
  case (Suc m)
  have "(a ^ Suc m) $ 1 = of_nat (Suc m) * (a$0)^(Suc m - 1) * a$1"
  proof (induct m)
    case (Suc k)
    hence "(a ^ Suc (Suc k)) $ 1 =
            a$0 * of_nat (Suc k) * (a $ 0)^k * a$1 + a$1 * ((a$0)^(Suc k))"
      using fps_mult_nth_1[of a] by (simp add: fps_power_zeroth[symmetric] mult.assoc)
    thus ?case by (simp add: algebra_simps)
  qed simp
  with Suc show ?thesis by simp
qed simp

lemma fps_power_first_eq: "a $ 0 = 1 \<Longrightarrow> a^n $ 1 = of_nat n * a$1"
proof (induct n)
  case (Suc n)
  show ?case unfolding power_Suc fps_mult_nth
    using Suc.hyps[OF \<open>a$0 = 1\<close>] \<open>a$0 = 1\<close> fps_power_zeroth_eq_one[OF \<open>a$0=1\<close>]
    by (simp add: algebra_simps)
qed simp

lemma fps_power_first_eq':
  assumes "a $ 1 = 1"
  shows   "a^n $ 1 = of_nat n * (a$0)^(n-1)"
proof (cases n)
  case (Suc m)
  from assms have "(a ^ Suc m) $ 1 = of_nat (Suc m) * (a$0)^(Suc m - 1)"
    using fps_mult_nth_1[of a]
    by    (induct m)
          (simp_all add: algebra_simps mult_of_nat_commute fps_power_zeroth)
  with Suc show ?thesis by simp
qed simp

lemmas startsby_one_power = fps_power_zeroth_eq_one

lemma startsby_zero_power: "a $ 0 = 0 \<Longrightarrow> n > 0 \<Longrightarrow> a^n $0 = 0"
  by (simp add: fps_power_zeroth zero_power)

lemma startsby_power: "a $0 = v \<Longrightarrow> a^n $0 = v^n"
  by (simp add: fps_power_zeroth)

lemma startsby_nonzero_power:
  fixes a :: "'a::semiring_1_no_zero_divisors fps"
  shows "a $ 0 \<noteq> 0 \<Longrightarrow> a^n $ 0 \<noteq> 0"
  by    (simp add: startsby_power)

lemma startsby_zero_power_iff[simp]:
  "a^n $0 = (0::'a::semiring_1_no_zero_divisors) \<longleftrightarrow> n \<noteq> 0 \<and> a$0 = 0"
proof
  show "a ^ n $ 0 = 0 \<Longrightarrow> n \<noteq> 0 \<and> a $ 0 = 0"
  proof
    assume a: "a^n $ 0 = 0"
    thus "a $ 0 = 0" using startsby_nonzero_power by auto
    have "n = 0 \<Longrightarrow> a^n $ 0 = 1" by simp
    with a show "n \<noteq> 0" by fastforce
  qed
  show "n \<noteq> 0 \<and> a $ 0 = 0 \<Longrightarrow> a ^ n $ 0 = 0"
    by (cases n) auto
qed

lemma startsby_zero_power_prefix:
  assumes a0: "a $ 0 = 0"
  shows "\<forall>n < k. a ^ k $ n = 0"
proof (induct k rule: nat_less_induct, clarify)
  case (1 k)
  fix j :: nat assume j: "j < k"
  show "a ^ k $ j = 0"
  proof (cases k)
    case 0 with j show ?thesis by simp
  next
    case (Suc i)
    with 1 j have "\<forall>m\<in>{0<..j}. a ^ i $ (j - m) = 0" by auto
    with Suc a0 show ?thesis by (simp add: fps_mult_nth sum.atLeast_Suc_atMost)
  qed
qed

lemma startsby_zero_sum_depends:
  assumes a0: "a $0 = 0"
    and kn: "n \<ge> k"
  shows "sum (\<lambda>i. (a ^ i)$k) {0 .. n} = sum (\<lambda>i. (a ^ i)$k) {0 .. k}"
proof (intro strip sum.mono_neutral_right)
  show "\<And>i. i \<in> {0..n} - {0..k} \<Longrightarrow> a ^ i $ k = 0"
    by (simp add: a0 startsby_zero_power_prefix)
qed (use kn in auto)

lemma startsby_zero_power_nth_same:
  assumes a0: "a$0 = 0"
  shows   "a^n $ n = (a$1) ^ n"
proof (induct n)
  case (Suc n)
  have "\<forall>i\<in>{Suc 1..Suc n}. a ^ n $ (Suc n - i) = 0"
    using a0 startsby_zero_power_prefix[of a n] by auto
  thus ?case
    using a0 Suc sum.atLeast_Suc_atMost[of 0 "Suc n" "\<lambda>i. a $ i * a ^ n $ (Suc n - i)"]
          sum.atLeast_Suc_atMost[of 1 "Suc n" "\<lambda>i. a $ i * a ^ n $ (Suc n - i)"]
    by    (simp add: fps_mult_nth)
qed simp

lemma fps_lr_inverse_power:
  fixes a :: "'a::ring_1 fps"
  assumes "x * a$0 = 1" "a$0 * x = 1"
  shows "fps_left_inverse (a^n) (x^n) = fps_left_inverse a x ^ n"
  and   "fps_right_inverse (a^n) (x^n) = fps_right_inverse a x ^ n"
proof-

  from assms have xn: "\<And>n. x^n * (a^n $ 0) = 1" "\<And>n. (a^n $ 0) * x^n = 1" 
    by (simp_all add: left_right_inverse_power fps_power_zeroth)

  show "fps_left_inverse (a^n) (x^n) = fps_left_inverse a x ^ n"
  proof (induct n)
    case 0
    then show ?case by (simp add: fps_lr_inverse_one_one(1))
  next
    case (Suc n)
    with assms show ?case
      using xn fps_lr_inverse_mult_ring1(1)[of x a "x^n" "a^n"]
      by    (simp add: power_Suc2[symmetric])
  qed

  moreover have "fps_right_inverse (a^n) (x^n) = fps_left_inverse (a^n) (x^n)"
    using xn by (intro fps_left_inverse_eq_fps_right_inverse[symmetric])
  moreover have "fps_right_inverse a x = fps_left_inverse a x"
    using assms by (intro fps_left_inverse_eq_fps_right_inverse[symmetric])
  ultimately show "fps_right_inverse (a^n) (x^n) = fps_right_inverse a x ^ n"
    by simp

qed

lemma fps_inverse_power:
  fixes a :: "'a::division_ring fps"
  shows "inverse (a^n) = inverse a ^ n"
proof (cases "n=0" "a$0 = 0" rule: case_split[case_product case_split])
  case False_True
  hence LHS: "inverse (a^n) = 0" and RHS: "inverse a ^ n = 0"
    by (simp_all add: startsby_zero_power)
  show ?thesis using trans_sym[OF LHS RHS] by fast
next
  case False_False
  from False_False(2) show ?thesis
    by  (simp add:
          fps_inverse_def fps_power_zeroth power_inverse fps_lr_inverse_power(2)[symmetric]
        )
qed auto

lemma fps_deriv_power':
  fixes a :: "'a::comm_semiring_1 fps"
  shows "fps_deriv (a ^ n) = (of_nat n) * fps_deriv a * a ^ (n - 1)"
proof (cases n)
  case (Suc m)
  moreover have "fps_deriv (a^Suc m) = of_nat (Suc m) * fps_deriv a * a^m"
    by (induct m) (simp_all add: algebra_simps)
  ultimately show ?thesis by simp
qed simp

lemma fps_deriv_power:
  fixes a :: "'a::comm_semiring_1 fps"
  shows "fps_deriv (a ^ n) = fps_const (of_nat n) * fps_deriv a * a ^ (n - 1)"
  by (simp add: fps_deriv_power' fps_of_nat)


subsection \<open>Integration\<close>

definition fps_integral :: "'a::{semiring_1,inverse} fps \<Rightarrow> 'a \<Rightarrow> 'a fps"
  where "fps_integral a a0 =
          Abs_fps (\<lambda>n. if n=0 then a0 else inverse (of_nat n) * a$(n - 1))"

abbreviation "fps_integral0 a \<equiv> fps_integral a 0"

lemma fps_integral_nth_0_Suc [simp]:
  fixes a :: "'a::{semiring_1,inverse} fps"
  shows "fps_integral a a0 $ 0 = a0"
  and   "fps_integral a a0 $ Suc n = inverse (of_nat (Suc n)) * a $ n"
  by    (auto simp: fps_integral_def)

lemma fps_integral_conv_plus_const:
  "fps_integral a a0 = fps_integral a 0 + fps_const a0"
  unfolding fps_integral_def by (intro fps_ext) simp

lemma fps_deriv_fps_integral:
  fixes a :: "'a::{division_ring,ring_char_0} fps"
  shows "fps_deriv (fps_integral a a0) = a"
proof (intro fps_ext)
  fix n
  have "(of_nat (Suc n) :: 'a) \<noteq> 0" by (rule of_nat_neq_0)
  hence "of_nat (Suc n) * inverse (of_nat (Suc n) :: 'a) = 1" by simp
  moreover have
    "fps_deriv (fps_integral a a0) $ n = of_nat (Suc n) * inverse (of_nat (Suc n)) * a $ n"
    by (simp add: mult.assoc)
  ultimately show "fps_deriv (fps_integral a a0) $ n = a $ n" by simp
qed

lemma fps_integral0_deriv:
  fixes a :: "'a::{division_ring,ring_char_0} fps"
  shows "fps_integral0 (fps_deriv a) = a - fps_const (a$0)"
proof (intro fps_ext)
  fix n
  show "fps_integral0 (fps_deriv a) $ n = (a - fps_const (a$0)) $ n"
  proof (cases n)
    case (Suc m)
    have "(of_nat (Suc m) :: 'a) \<noteq> 0" by (rule of_nat_neq_0)
    hence "inverse (of_nat (Suc m) :: 'a) * of_nat (Suc m) = 1" by simp
    moreover have
      "fps_integral0 (fps_deriv a) $ Suc m =
        inverse (of_nat (Suc m)) * of_nat (Suc m) * a $ (Suc m)"
      by (simp add: mult.assoc)
    ultimately show ?thesis using Suc by simp
  qed simp
qed

lemma fps_integral_deriv:
  fixes a :: "'a::{division_ring,ring_char_0} fps"
  shows "fps_integral (fps_deriv a) (a$0) = a"
  using fps_integral_conv_plus_const[of "fps_deriv a" "a$0"]
  by    (simp add: fps_integral0_deriv)

lemma fps_integral0_zero:
  "fps_integral0 (0::'a::{semiring_1,inverse} fps) = 0"
  by (intro fps_ext) (simp add: fps_integral_def)

lemma fps_integral0_fps_const':
  fixes   c :: "'a::{semiring_1,inverse}"
  assumes "inverse (1::'a) = 1"
  shows   "fps_integral0 (fps_const c) = fps_const c * fps_X"
proof (intro fps_ext)
  fix n
  show "fps_integral0 (fps_const c) $ n = (fps_const c * fps_X) $ n"
    by (cases n) (simp_all add: assms mult_delta_right)
qed

lemma fps_integral0_fps_const:
  fixes c :: "'a::division_ring"
  shows "fps_integral0 (fps_const c) = fps_const c * fps_X"
  by    (rule fps_integral0_fps_const'[OF inverse_1])

lemma fps_integral0_one':
  assumes "inverse (1::'a::{semiring_1,inverse}) = 1"
  shows   "fps_integral0 (1::'a fps) = fps_X"
  using   assms fps_integral0_fps_const'[of "1::'a"]
  by      simp

lemma fps_integral0_one:
  "fps_integral0 (1::'a::division_ring fps) = fps_X"
  by (rule fps_integral0_one'[OF inverse_1])

lemma fps_integral0_fps_const_mult_left:
  fixes a :: "'a::division_ring fps"
  shows "fps_integral0 (fps_const c * a) = fps_const c * fps_integral0 a"
proof (intro fps_ext)
  fix n
  show "fps_integral0 (fps_const c * a) $ n = (fps_const c * fps_integral0 a) $ n"
    using mult_inverse_of_nat_commute[of n c, symmetric]
          mult.assoc[of "inverse (of_nat n)" c "a$(n-1)"]
          mult.assoc[of c "inverse (of_nat n)" "a$(n-1)"]
    by    (simp add: fps_integral_def)
qed

lemma fps_integral0_fps_const_mult_right:
  fixes a :: "'a::{semiring_1,inverse} fps"
  shows "fps_integral0 (a * fps_const c) = fps_integral0 a * fps_const c"
  by    (intro fps_ext) (simp add: fps_integral_def algebra_simps)

lemma fps_integral0_neg:
  fixes a :: "'a::{ring_1,inverse} fps"
  shows "fps_integral0 (-a) = - fps_integral0 a"
  using fps_integral0_fps_const_mult_right[of a "-1"]
  by    (simp add: fps_const_neg[symmetric])

lemma fps_integral0_add:
  "fps_integral0 (a+b) = fps_integral0 a + fps_integral0 b"
  by (intro fps_ext) (simp add: fps_integral_def algebra_simps)

lemma fps_integral0_linear:
  fixes a b :: "'a::division_ring"
  shows "fps_integral0 (fps_const a * f + fps_const b * g) =
          fps_const a * fps_integral0 f + fps_const b * fps_integral0 g"
  by    (simp add: fps_integral0_add fps_integral0_fps_const_mult_left)
  
lemma fps_integral0_linear2:
  "fps_integral0 (f * fps_const a + g * fps_const b) =
    fps_integral0 f * fps_const a + fps_integral0 g * fps_const b"
  by (simp add: fps_integral0_add fps_integral0_fps_const_mult_right)

lemma fps_integral_linear:
  fixes a b a0 b0 :: "'a::division_ring"
  shows
  "fps_integral (fps_const a * f + fps_const b * g) (a*a0 + b*b0) =
    fps_const a * fps_integral f a0 + fps_const b * fps_integral g b0"
  using fps_integral_conv_plus_const[of
          "fps_const a * f + fps_const b * g"
          "a*a0 + b*b0"
        ]
        fps_integral_conv_plus_const[of f a0] fps_integral_conv_plus_const[of g b0]
  by    (simp add: fps_integral0_linear algebra_simps)

lemma fps_integral0_sub:
  fixes a b :: "'a::{ring_1,inverse} fps"
  shows "fps_integral0 (a-b) = fps_integral0 a - fps_integral0 b"
  using fps_integral0_linear2[of a 1 b "-1"]
  by    (simp add: fps_const_neg[symmetric])

lemma fps_integral0_of_nat:
  "fps_integral0 (of_nat n :: 'a::division_ring fps) = of_nat n * fps_X"
  using fps_integral0_fps_const[of "of_nat n :: 'a"] by (simp add: fps_of_nat)

lemma fps_integral0_sum:
  "fps_integral0 (sum f S) = sum (\<lambda>i. fps_integral0 (f i)) S"
proof (cases "finite S")
  case True show ?thesis
    by  (induct rule: finite_induct [OF True])
        (simp_all add: fps_integral0_zero fps_integral0_add)
qed (simp add: fps_integral0_zero)

lemma fps_integral0_by_parts:
  fixes a b :: "'a::{division_ring,ring_char_0} fps"
  shows
    "fps_integral0 (a * b) =
      a * fps_integral0 b - fps_integral0 (fps_deriv a * fps_integral0 b)"
proof-
  have "fps_integral0 (fps_deriv (a * fps_integral0 b)) = a * fps_integral0 b"
    using fps_integral0_deriv[of "(a * fps_integral0 b)"] by simp
  moreover have
    "fps_integral0 (a * b) =
      fps_integral0 (fps_deriv (a * fps_integral0 b)) -
      fps_integral0 (fps_deriv a * fps_integral0 b)"
    by (auto simp: fps_deriv_fps_integral fps_integral0_sub[symmetric])
  ultimately show ?thesis by simp
qed

lemma fps_integral0_fps_X:
  "fps_integral0 (fps_X::'a::{semiring_1,inverse} fps) =
    fps_const (inverse (of_nat 2)) * fps_X\<^sup>2"
  by (intro fps_ext) (auto simp: fps_integral_def)

lemma fps_integral0_fps_X_power:
  "fps_integral0 ((fps_X::'a::{semiring_1,inverse} fps) ^ n) =
            fps_const (inverse (of_nat (Suc n))) * fps_X ^ Suc n"
proof (intro fps_ext)
  fix k show
    "fps_integral0 ((fps_X::'a fps) ^ n) $ k =
      (fps_const (inverse (of_nat (Suc n))) * fps_X ^ Suc n) $ k"
    by (cases k) simp_all
qed


subsection \<open>Composition of FPSs\<close>

definition fps_compose :: "'a::semiring_1 fps \<Rightarrow> 'a fps \<Rightarrow> 'a fps"  (infixl "oo" 55)
  where "a oo b = Abs_fps (\<lambda>n. sum (\<lambda>i. a$i * (b^i$n)) {0..n})"

lemma fps_compose_nth: "(a oo b)$n = sum (\<lambda>i. a$i * (b^i$n)) {0..n}"
  by (simp add: fps_compose_def)

lemma fps_compose_nth_0 [simp]: "(f oo g) $ 0 = f $ 0"
  by (simp add: fps_compose_nth)

lemma fps_compose_fps_X[simp]: "a oo fps_X = (a :: 'a::comm_ring_1 fps)"
  by (simp add: fps_ext fps_compose_def mult_delta_right)

lemma fps_const_compose[simp]: "fps_const (a::'a::comm_ring_1) oo b = fps_const a"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left)

lemma numeral_compose[simp]: "(numeral k :: 'a::comm_ring_1 fps) oo b = numeral k"
  unfolding numeral_fps_const by simp

lemma neg_numeral_compose[simp]: "(- numeral k :: 'a::comm_ring_1 fps) oo b = - numeral k"
  unfolding neg_numeral_fps_const by simp

lemma fps_X_fps_compose_startby0[simp]: "a$0 = 0 \<Longrightarrow> fps_X oo a = (a :: 'a::comm_ring_1 fps)"
  by (simp add: fps_eq_iff fps_compose_def mult_delta_left not_le)


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
        by (simp add: not_less le_less_Suc_eq)
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

definition "fps_XD = (*) fps_X \<circ> fps_deriv"

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
  "a = ((1::'a::ring_1 fps) - fps_X) * Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
proof (rule fps_ext)
  define f g :: "'a fps"
    where "f \<equiv> 1 - fps_X"
    and   "g \<equiv> Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
  fix n show "a $ n= (f * g) $ n"
  proof (cases n)
    case (Suc m)
    hence "(f * g) $ n = g $ Suc m - g $ m"
      using fps_mult_nth[of f g "Suc m"]
            sum.atLeast_Suc_atMost[of 0 "Suc m" "\<lambda>i. f $ i * g $ (Suc m - i)"]
            sum.atLeast_Suc_atMost[of 1 "Suc m" "\<lambda>i. f $ i * g $ (Suc m - i)"]
      by    (simp add: f_def)
    with Suc show ?thesis by (simp add: g_def)
  qed (simp add: f_def g_def)
qed

lemma fps_divide_fps_X_minus1_sum_ring1:
  assumes "inverse 1 = (1::'a::{ring_1,inverse})"
  shows   "a /((1::'a fps) - fps_X) = Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
proof-
  from assms have "a /((1::'a fps) - fps_X) = a * Abs_fps (\<lambda>n. 1)"
    by (simp add: fps_divide_def fps_inverse_def fps_lr_inverse_one_minus_fps_X(2))
  thus ?thesis by (auto intro: fps_ext simp: fps_mult_nth)
qed

lemma fps_divide_fps_X_minus1_sum:
  "a /((1::'a::division_ring fps) - fps_X) = Abs_fps (\<lambda>n. sum (\<lambda>i. a $ i) {0..n})"
  using fps_divide_fps_X_minus1_sum_ring1[of a] by simp


subsubsection \<open>Rule 4 in its more general form: generalizes Rule 3 for an arbitrary
  finite product of FPS, also the relvant instance of powers of a FPS\<close>

definition "natpermute n k = {l :: nat list. length l = k \<and> sum_list l = n}"

lemma natlist_trivial_1: "natpermute n 1 = {[n]}"
proof -
  have "\<lbrakk>length xs = 1; n = sum_list xs\<rbrakk> \<Longrightarrow> xs = [sum_list xs]" for xs
    by (cases xs) auto
  then show ?thesis
    by (auto simp add: natpermute_def)
qed

lemma natlist_trivial_Suc0 [simp]: "natpermute n (Suc 0) = {[n]}"
  using natlist_trivial_1 by force

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
      using assms by (force simp add: natpermute_def)
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
    have "sum_list (take h l) \<le> sum_list l"
      using l_take_drop ls m by presburger
    with xs ys ls l show "l \<in> ?R"
      by simp (metis append_take_drop_id m)
  qed
qed

lemma natpermute_0: "natpermute n 0 = (if n = 0 then {[]} else {})"
  by (auto simp add: natpermute_def)

lemma natpermute_0'[simp]: "natpermute 0 k = (if k = 0 then {[]} else {replicate k 0})"
  by (auto simp add: set_replicate_conv_if natpermute_def replicate_length_same)

lemma natpermute_finite: "finite (natpermute n k)"
proof (induct k arbitrary: n)
  case 0
  then show ?case
    by (simp add: natpermute_0)
next
  case (Suc k)
  then show ?case
    using natpermute_split [of k "Suc k"] finite_UN_I by simp
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
      by (auto simp add: natpermute_def atLeastLessThanSuc_atLeastAtMost sum_list_sum_nth)
    also have "\<dots> = n + sum (nth xs) ({0..k} - {i})"
      unfolding sum.union_disjoint[OF f d, unfolded eqs] using i by simp
    finally have zxs: "\<forall> j\<in> {0..k} - {i}. xs!j = 0"
      by auto
    from H have xsl: "length xs = k+1"
      by (simp add: natpermute_def)
    from i have i': "i < length (replicate (k+1) 0)"   "i < k+1"
      unfolding length_replicate by presburger+
    have "xs = (replicate (k+1) 0) [i := n]"
    proof (rule nth_equalityI)
      show "length xs = length ((replicate (k + 1) 0)[i := n])"
        by (metis length_list_update length_replicate xsl)
      show "xs ! j = (replicate (k + 1) 0)[i := n] ! j" if "j < length xs" for j
      proof (cases "j = i")
        case True
        then show ?thesis
          by (metis i'(1) i(2) nth_list_update)
      next
        case False
        with that show ?thesis
          by (simp add: xsl zxs del: replicate.simps split: nat.split)
      qed
    qed
    then show "xs \<in> ?B" using i by blast
  qed
  show "?B \<subseteq> ?A"
  proof
    fix xs
    assume "xs \<in> ?B"
    then obtain i where i: "i \<in> {0..k}" and xs: "xs = (replicate (k + 1) 0) [i:=n]"
      by auto
    have nxs: "n \<in> set xs"
      unfolding xs using set_update_memI i 
      by (metis Suc_eq_plus1 atLeast0AtMost atMost_iff le_simps(2) length_replicate)
    have xsl: "length xs = k + 1"
      by (simp only: xs length_replicate length_list_update)
    have "sum_list xs = sum (nth xs) {0..<k+1}"
      unfolding sum_list_sum_nth xsl ..
    also have "\<dots> = sum (\<lambda>j. if j = i then n else 0) {0..< k+1}"
      by (rule sum.cong) (simp_all add: xs del: replicate.simps)
    also have "\<dots> = n" using i by simp
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
      by simp
  next
    case (Suc k)
    then have km: "k < m" by arith
    have u0: "{0 .. k} \<union> {m} = {0..m}"
      using Suc by (simp add: set_eq_iff) presburger
    have f0: "finite {0 .. k}" "finite {m}" by auto
    have d0: "{0 .. k} \<inter> {m} = {}" using Suc by auto
    have "(prod a {0 .. m}) $ n = (prod a {0 .. k} * a m) $ n"
      unfolding prod.union_disjoint[OF f0 d0, unfolded u0] by simp
    also have "\<dots> = (\<Sum>i = 0..n. (\<Sum>v\<in>natpermute i (k + 1).
            (\<Prod>j = 0..k. a j $ v ! j) * a m $ (n - i)))"
      unfolding fps_mult_nth H[rule_format, OF km] sum_distrib_right ..
    also have "... = (\<Sum>i = 0..n.
                       \<Sum>v\<in>(\<lambda>l1. l1 @ [n - i]) ` natpermute i (Suc k).
                        (\<Prod>j = 0..k. a j $ v ! j) * a (Suc k) $ v ! Suc k)"
      by (intro sum.cong [OF refl sym] sum.reindex_cong) (auto simp: inj_on_def natpermute_def nth_append Suc)
    also have "... = (\<Sum>v\<in>(\<Union>x\<in>{0..n}. {l1 @ [n - x] |l1. l1 \<in> natpermute x (Suc k)}).
                      (\<Prod>j = 0..k. a j $ v ! j) * a (Suc k) $ v ! Suc k)"
      by (subst sum.UNION_disjoint) (auto simp add: natpermute_finite setcompr_eq_image)
    also have "\<dots> = (\<Sum>v\<in>natpermute n (m + 1). \<Prod>j\<in>{0..m}. a j $ v ! j)"
      using natpermute_split[of m "m + 1"] by (simp add: Suc)
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

lemmas fps_nth_power_0 = fps_power_zeroth

lemma natpermute_max_card:
  assumes n0: "n \<noteq> 0"
  shows "card {xs \<in> natpermute n (k + 1). n \<in> set xs} = k + 1"
  unfolding natpermute_contain_maximal
proof -
  let ?A = "\<lambda>i. {(replicate (k + 1) 0)[i := n]}"
  let ?K = "{0 ..k}"
  have fK: "finite ?K"
    by simp
  have fAK: "\<forall>i\<in>?K. finite (?A i)"
    by auto
  have d: "\<forall>i\<in> ?K. \<forall>j\<in> ?K. i \<noteq> j \<longrightarrow>
    {(replicate (k + 1) 0)[i := n]} \<inter> {(replicate (k + 1) 0)[j := n]} = {}"
  proof clarify
    fix i j
    assume i: "i \<in> ?K" and j: "j \<in> ?K" and ij: "i \<noteq> j"
    have False if eq: "(replicate (k+1) 0)[i:=n] = (replicate (k+1) 0)[j:= n]"
    proof -
      have "(replicate (k+1) 0) [i:=n] ! i = n"
        using i by (simp del: replicate.simps)
      moreover
      have "(replicate (k+1) 0) [j:=n] ! i = 0"
        using i ij by (simp del: replicate.simps)
      ultimately show ?thesis
        using eq n0 by (simp del: replicate.simps)
    qed
    then show "{(replicate (k + 1) 0)[i := n]} \<inter> {(replicate (k + 1) 0)[j := n]} = {}"
      by auto
  qed
  from card_UN_disjoint[OF fK fAK d]
  show "card (\<Union>i\<in>{0..k}. {(replicate (k + 1) 0)[i := n]}) = k + 1"
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
    then obtain j where j: "j \<le> m" "v ! j = k" by auto
    
    from v have "k = sum_list v" by (simp add: A_def natpermute_def)
    also have "\<dots> = (\<Sum>i=0..m. v ! i)"
      by (simp add: sum_list_sum_nth atLeastLessThanSuc_atLeastAtMost del: sum.op_ivl_Suc)
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
        by (intro sum.cong refl prod.cong less lessI) (simp add: natpermute_def)
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
          using H Suc by auto
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
    fix r :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
    and a :: "'a fps"
    and k n xs i
    assume xs: "xs \<in> {xs \<in> natpermute (Suc n) (Suc k). Suc n \<notin> set xs}" and i: "i \<in> {0..k}"
    have False if c: "Suc n \<le> xs ! i"
    proof -
      from xs i have "xs !i \<noteq> Suc n"
        by (simp add: in_set_conv_nth natpermute_def)
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
      using not_less by auto
  next
    fix r :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
    and a :: "'a fps"
    and k n
    show "((r, Suc k, a, 0), r, Suc k, a, Suc n) \<in> ?R" by simp
  }
qed

definition "fps_radical r n a = Abs_fps (radical r n a)"

lemma radical_0 [simp]: "\<And>n. 0 < n \<Longrightarrow> radical r 0 a n = 0"
  using radical.elims by blast

lemma fps_radical0[simp]: "fps_radical r 0 a = 1"
  by (auto simp add: fps_eq_iff fps_radical_def)

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
  proof (rule prod.cong [OF refl])
    show "fps_radical r k a $ replicate k 0 ! j = r k (a $ 0)" if "j \<in> {0..h}" for j
    proof -
      have "j < Suc h"
        using that by presburger
      then show ?thesis
        by (metis Suc fps_radical_nth_0 nth_replicate old.nat.distinct(2))
    qed
  qed
  also have "\<dots> = a$0"
    using r Suc by simp
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
          from v obtain i where i: "i \<in> {0..k}" "v = (replicate (k+1) 0) [i:= n]"
            unfolding natpermute_contain_maximal by auto
          have "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) =
                (\<Prod>j\<in>{0..k}. if j = i then fps_radical r (Suc k) a $ n else r (Suc k) (a$0))"
              using i r0 by (auto simp del: replicate.simps intro: prod.cong)
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
          from v obtain i where i: "i \<in> {0..k}" "v = (replicate (k+1) 0) [i:= n]"
            unfolding Suc_eq_plus1 natpermute_contain_maximal
            by (auto simp del: replicate.simps)
          have "(\<Prod>j\<in>{0..k}. a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then a $ n else r (Suc k) (b$0))"
            using i a0 by (auto simp del: replicate.simps intro: prod.cong)
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
              by (simp add: in_set_conv_nth natpermute_def)
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
        finally have \<section>: "of_nat (k+1) * a $ n * (?r $ 0)^k = b$n - sum ?f ?Pnknn"
          by simp
        have "a$n = (b$n - sum ?f ?Pnknn) / (of_nat (k+1) * (?r $ 0)^k)"
          apply (rule eq_divide_imp)
          using r00 \<section> by (simp_all add: ac_simps del: of_nat_Suc)
        then show ?thesis
          unfolding fps_radical_def Suc
          by (simp del: of_nat_Suc)
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

lemma fps_deriv_radical':
  fixes a :: "'a::field_char_0 fps"
  assumes r0: "(r (Suc k) (a$0)) ^ Suc k = a$0"
    and a0: "a$0 \<noteq> 0"
  shows "fps_deriv (fps_radical r (Suc k) a) =
    fps_deriv a / ((of_nat (Suc k)) * (fps_radical r (Suc k) a) ^ k)"
proof -
  let ?r = "fps_radical r (Suc k) a"
  let ?w = "(of_nat (Suc k)) * ?r ^ k"
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
    by (simp add: fps_deriv_power' ac_simps del: power_Suc)
  then have "?iw * fps_deriv ?r * ?w = ?iw * fps_deriv a"
    by simp
  with a0 r0 have "fps_deriv ?r * (?iw * ?w) = fps_deriv a / ?w"
    by (subst fps_divide_unit) (auto simp del: of_nat_Suc)
  then show ?thesis unfolding th0 by simp
qed

lemma fps_deriv_radical:
  fixes a :: "'a::field_char_0 fps"
  assumes r0: "(r (Suc k) (a$0)) ^ Suc k = a$0"
    and a0: "a$0 \<noteq> 0"
  shows "fps_deriv (fps_radical r (Suc k) a) =
    fps_deriv a / (fps_const (of_nat (Suc k)) * (fps_radical r (Suc k) a) ^ k)"
  using fps_deriv_radical'[of r k a, OF r0 a0]
  by (simp add: fps_of_nat[symmetric])

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
      by (intro sum.mono_neutral_right) (auto simp add: mult_delta_left not_le)
    also have "\<dots> = sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
      unfolding fps_deriv_nth
      by (rule sum.reindex_cong [of Suc]) (simp_all add: mult.assoc)
    finally have th0: "(fps_deriv (a oo b))$n =
      sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}" .

    have "(((fps_deriv a) oo b) * (fps_deriv b))$n = sum (\<lambda>i. (fps_deriv b)$ (n - i) * ((fps_deriv a) oo b)$i) {0..n}"
      unfolding fps_mult_nth by (simp add: ac_simps)
    also have "\<dots> = sum (\<lambda>i. sum (\<lambda>j. of_nat (n - i +1) * b$(n - i + 1) * of_nat (j + 1) * a$(j+1) * (b^j)$i) {0..n}) {0..n}"
      unfolding fps_deriv_nth fps_compose_nth sum_distrib_left mult.assoc
      by (auto simp: subset_eq b0 startsby_zero_power_prefix sum.mono_neutral_left intro: sum.cong)
    also have "\<dots> = sum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (sum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
      unfolding sum_distrib_left
      by (subst sum.swap) (force intro: sum.cong)
    finally show ?thesis
      unfolding th0 by simp
  qed
  then show ?thesis by (simp add: fps_eq_iff)
qed


subsection \<open>Finite FPS (i.e. polynomials) and fps_X\<close>

lemma fps_poly_sum_fps_X:
  assumes "\<forall>i > n. a$i = 0"
  shows "a = sum (\<lambda>i. fps_const (a$i) * fps_X^i) {0..n}" (is "a = ?r")
proof -
  have "a$i = ?r$i" for i
    unfolding fps_sum_nth fps_mult_left_const_nth fps_X_power_nth
    by (simp add: mult_delta_right assms)
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
proof -
  have "compinv x n = gcompinv fps_X x n" for n and x :: "'a fps"
  proof (induction n rule: nat_less_induct)
    case (1 n)
    then show ?case
      by (cases n) auto
  qed
  then show ?thesis
    by (auto simp add: fun_eq_iff fps_eq_iff fps_inv_def fps_ginv_def)
qed

lemma fps_compose_1[simp]: "1 oo a = 1"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left)

lemma fps_compose_0[simp]: "0 oo a = 0"
  by (simp add: fps_eq_iff fps_compose_nth)

lemma fps_compose_0_right[simp]: "a oo 0 = fps_const (a $ 0)"
  by (simp add: fps_eq_iff fps_compose_nth power_0_left sum.neutral)

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
  have s: "?S \<subseteq> {0..n} \<times> {0..n}" by (simp add: subset_eq)
  have f: "finite {(k::nat, m::nat). k + m \<le> n}"
    by (auto intro: finite_subset[OF s])
  have "?r = (\<Sum>(k, m) \<in> {(k, m). k + m \<le> n}. \<Sum>j = 0..n. a $ k * b $ m * (c ^ k $ j * d ^ m $ (n - j)))"
    by (simp add: fps_mult_nth sum_distrib_left)
  also have "\<dots> = (\<Sum>i = 0..n. \<Sum>(k,m)\<in>{(k,m). k+m \<le> n}. a $ k * c ^ k $ i * b $ m * d ^ m $ (n-i))"
    unfolding sum.swap [where A = "{0..n}"] by (auto simp add: field_simps intro: sum.cong)
  also have "... = (\<Sum>i = 0..n.
                    \<Sum>q = 0..i. \<Sum>j = 0..n - i. a $ q * c ^ q $ i * (b $ j * d ^ j $ (n - i)))"
    apply (rule sum.cong [OF refl])
    apply (simp add: sum.cartesian_product mult.assoc)
    apply (rule sum.mono_neutral_right[OF f], force)
    by clarsimp (meson c0 d0 leI startsby_zero_power_prefix)
  also have "\<dots> = ?l"
    by (simp add: fps_mult_nth fps_compose_nth sum_product)
  finally show ?thesis by simp
qed

lemma sum_pair_less_iff:
  "sum (\<lambda>((k::nat),m). a k * b m * c (k + m)) {(k,m). k + m \<le> n} =
    sum (\<lambda>s. sum (\<lambda>i. a i * b (s - i) * c s) {0..s}) {0..n}"
  (is "?l = ?r")
proof -
  have th0: "{(k, m). k + m \<le> n} = (\<Union>s\<in>{0..n}. \<Union>i\<in>{0..s}. {(i, s - i)})"
    by auto
  show "?l = ?r"
    unfolding th0
    by (simp add: sum.UNION_disjoint eq_diff_iff disjoint_iff)
qed

lemma fps_compose_mult_distrib_lemma:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "((a oo c) * (b oo c))$n = sum (\<lambda>s. sum (\<lambda>i. a$i * b$(s - i) * (c^s) $ n) {0..s}) {0..n}"
  unfolding product_composition_lemma[OF c0 c0] power_add[symmetric]
  unfolding sum_pair_less_iff[where a = "\<lambda>k. a$k" and b="\<lambda>m. b$m" and c="\<lambda>s. (c ^ s)$n" and n = n] ..

lemma fps_compose_mult_distrib:
  assumes c0: "c $ 0 = (0::'a::idom)"
  shows "(a * b) oo c = (a oo c) * (b oo c)"
proof (clarsimp simp add: fps_eq_iff fps_compose_mult_distrib_lemma [OF c0])
  show "(a * b oo c) $ n = (\<Sum>s = 0..n. \<Sum>i = 0..s. a $ i * b $ (s - i) * c ^ s $ n)" for n
    by (simp add: fps_compose_nth fps_mult_nth sum_distrib_right)
qed


lemma fps_compose_prod_distrib:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "prod a S oo c = prod (\<lambda>k. a k oo c) S"
proof (induct S rule: infinite_finite_induct)
next
  case (insert)
  then show ?case   
    by (simp add: fps_compose_mult_distrib[OF c0])
qed auto

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
  have "(\<Prod>n = 0..m. a) oo c = (\<Prod>n = 0..m. a oo c)"
    using c0 fps_compose_prod_distrib by blast
  moreover have th0: "a^n = prod (\<lambda>k. a) {0..m}" "(a oo c) ^ n = prod (\<lambda>k. a oo c) {0..m}"
    by (simp_all add: prod_constant Suc)
  ultimately show ?thesis
    by presburger
qed

lemma fps_compose_uminus: "- (a::'a::ring_1 fps) oo c = - (a oo c)"
  by (simp add: fps_eq_iff fps_compose_nth field_simps sum_negf[symmetric])
    
lemma fps_compose_sub_distrib: "(a - b) oo (c::'a::ring_1 fps) = (a oo c) - (b oo c)"
  using fps_compose_add_distrib [of a "- b" c] by (simp add: fps_compose_uminus)

lemma fps_X_fps_compose: "fps_X oo a = Abs_fps (\<lambda>n. if n = 0 then (0::'a::comm_ring_1) else a$n)"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left)

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
  by (simp add: fps_const_mult_apply_left mult.commute)

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
    also have "... = (\<Sum>i = 0..n. \<Sum>j = 0..n. a $ j * (b ^ j $ i * c ^ i $ n))"
      by (simp add: fps_compose_nth fps_sum_nth sum_distrib_right mult.assoc)
    also have "... = (\<Sum>i = 0..n. \<Sum>j = 0..i. a $ j * (b ^ j $ i * c ^ i $ n))"
      by (intro sum.cong [OF refl] sum.mono_neutral_right; simp add: b0 startsby_zero_power_prefix)
    also have "\<dots> = ?r$n"
      by (simp add: fps_compose_nth  sum_distrib_right mult.assoc)
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
        by (simp add: fps_compose_nth mult_delta_left)
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
    by (simp add: a0 fps_compose_assoc rca0)
  then have "?r b (?r c a) oo c = b oo a"
    unfolding fps_ginv[OF a0 a1] .
  then have "?r b (?r c a) oo c oo fps_inv c= b oo a oo fps_inv c"
    by simp
  then have "?r b (?r c a) oo (c oo fps_inv c) = b oo a oo fps_inv c"
    by (metis c0 c1 fps_compose_assoc fps_compose_nth_0 fps_inv fps_inv_right)
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
                if_distrib cong: if_cong)
              
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
    using of_nat_neq_0 by (auto simp add: fps_exp_def divide_simps)
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
        by (simp add: th divide_simps)
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
  by (induct n) (simp_all add: field_simps fps_exp_add_mult)

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
  thus "fps_exp c = fps_const c'" by (simp add: fps_eq_iff)
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
  by (simp add: fps_eq_iff)

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
    by (simp add: fps_compose_add_distrib fps_inv_right[OF b0 b1] distrib_left flip: fps_const_mult_apply_left)
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
    by (simp add: eq fps_ln_deriv)
  finally show ?thesis
    unfolding fps_deriv_eq_iff by simp
qed

lemma fps_X_dvd_fps_ln [simp]: "fps_X dvd fps_ln c"
proof -
  have "fps_ln c = fps_X * Abs_fps (\<lambda>n. (-1) ^ n / (of_nat (Suc n) * c))"
    by (intro fps_ext) (simp add: fps_ln_def of_nat_diff)
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
      unfolding fps_divide_def  mult.assoc[symmetric] inverse_mult_eq_1[OF x10]
      by (simp add: field_simps)
    finally show ?thesis .
  qed

  show ?rhs if ?lhs
  proof -
    from eq that have h: "?l = ?r" ..
    have th0: "a$ Suc n = ((c - of_nat n) / of_nat (Suc n)) * a $n" for n
    proof -
      from h have "?l $ n = ?r $ n" by simp
      then show ?thesis
        by (simp add: field_simps del: of_nat_Suc split: if_split_asm)
    qed
    have th1: "a $ n = (c gchoose n) * a $ 0" for n
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc m)
      have "(c - of_nat m) * (c gchoose m) = (c gchoose Suc m) * of_nat (Suc m)"
        by (metis gbinomial_absorb_comp gbinomial_absorption mult.commute)
      with Suc show ?case
        unfolding th0
        by (simp add: divide_simps del: of_nat_Suc)
    qed
    show ?thesis
      by (metis expand_fps_eq fps_binomial_nth fps_mult_right_const_nth mult.commute th1)
  qed

  show ?lhs if ?rhs
  proof -
    have th00: "x * (a $ 0 * y) = a $ 0 * (x * y)" for x y
      by (simp add: mult.commute)
    have "?l = (1 + fps_X) * fps_deriv (fps_const (a $ 0) * fps_binomial c)"
      using that by auto
    also have "... = fps_const c * (fps_const (a $ 0) * fps_binomial c)"
    proof (clarsimp simp add: fps_eq_iff algebra_simps)
      show "a $ 0 * (c gchoose Suc n) + (of_nat n * ((c gchoose n) * a $ 0) + of_nat n * (a $ 0 * (c gchoose Suc n))) 
         = c * ((c gchoose n) * a $ 0)" for n
      unfolding mult.assoc[symmetric]  
      by (simp add: field_simps gbinomial_mult_1)
  qed
    also have "... = ?r"
      using that by auto
    finally have "?l = ?r" .
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
  fixes c :: "'a :: field_char_0"
  assumes "n > 0"
  shows "inverse ((1 - fps_const c * fps_X) ^ n) = Abs_fps (\<lambda>k. of_nat ((n + k - 1) choose k) * c^k)"
proof -
  have \<section>: "\<And>j. Abs_fps (\<lambda>na. (- c) ^ na * fps_binomial (- of_nat n) $ na) $ j =
          Abs_fps (\<lambda>k. of_nat (n + k - 1 choose k) * c ^ k) $ j"
    using assms
    by (simp add: gbinomial_minus binomial_gbinomial of_nat_diff flip: power_mult_distrib mult.assoc)
  show ?thesis
    apply (rule fps_ext)
    using \<section> 
    by (metis (no_types, lifting) one_minus_fps_X_const_neg_power fps_const_neg fps_compose_linear fps_nth_Abs_fps)
qed

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
  by (metis atMost_atLeast0 choose_square_sum mult_2)

lemma Vandermonde_pochhammer_lemma:
  fixes a :: "'a::field_char_0"
  assumes b: "\<And>j. j<n \<Longrightarrow> b \<noteq> of_nat j"
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
      then show False 
        using \<open>j < n\<close> j b by auto
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
        with pochhammer_minus'[where k=k and b=b] bn0 show ?thesis       
          by (simp add: pochhammer_same)
      next
        case False
        with kn have kn': "k < n"
          by simp
        have "h \<le> m"
          using \<open>k \<le> n\<close> h m by blast
        have m1nk: "?m1 n = prod (\<lambda>i. - 1) {..m}" "?m1 k = prod (\<lambda>i. - 1) {0..h}"
          by (simp_all add: m h)
        have bnz0: "pochhammer (b - of_nat n + 1) k \<noteq> 0"
          using bn0 kn
          unfolding pochhammer_eq_0_iff
          by (metis add.commute add_diff_eq nz' pochhammer_eq_0_iff)
        have eq1: "prod (\<lambda>k. (1::'a) + of_nat m - of_nat k) {..h} =
          prod of_nat {Suc (m - h) .. Suc m}"
          using kn' h m
          by (intro prod.reindex_bij_witness[where i="\<lambda>k. Suc m - k" and j="\<lambda>k. Suc m - k"])
             (auto simp: of_nat_diff)
        have "(\<Prod>i = 0..<k. 1 + of_nat n - of_nat k + of_nat i) = (\<Prod>x = n - k..<n. (1::'a) + of_nat x)"
          using \<open>k \<le> n\<close> 
          using prod.atLeastLessThan_shift_bounds [where ?'a = 'a, of "\<lambda>i. 1 + of_nat i" 0 "n - k" k]
          by (auto simp add: of_nat_diff field_simps)
        then have "fact (n - k) * pochhammer ((1::'a) + of_nat n - of_nat k) k = fact n"
          using \<open>k \<le> n\<close> 
          by (auto simp add: fact_split [of k n] pochhammer_prod field_simps)
        then have th1: "(?m1 k * ?p (of_nat n) k) / ?f n = 1 / of_nat(fact (n - k))"
          by (simp add: pochhammer_minus field_simps)
        have "?m1 n * ?p b n = pochhammer (b - of_nat m) (Suc m)"
          by (simp add: pochhammer_minus field_simps m)
        also have "... = (\<Prod>i = 0..m. b - of_nat i)"
          by (auto simp add: pochhammer_prod_rev of_nat_diff prod.atLeast_Suc_atMost_Suc_shift simp del: prod.cl_ivl_Suc)
        finally have th20: "?m1 n * ?p b n = prod (\<lambda>i. b - of_nat i) {0..m}" .
        have "(\<Prod>x = 0..h. b - of_nat m + of_nat (h - x)) = (\<Prod>i = m - h..m. b - of_nat i)"
          using \<open>h \<le> m\<close> prod.atLeastAtMost_shift_0 [of "m - h" m, where ?'a = 'a]
          by (auto simp add: of_nat_diff field_simps)
        then have th21:"pochhammer (b - of_nat n + 1) k = prod (\<lambda>i. b - of_nat i) {n - k .. n - 1}"
          using kn by (simp add: pochhammer_prod_rev m h prod.atLeast_Suc_atMost_Suc_shift del: prod.op_ivl_Suc del: prod.cl_ivl_Suc)
        have "?m1 n * ?p b n =
          prod (\<lambda>i. b - of_nat i) {0.. n - k - 1} * pochhammer (b - of_nat n + 1) k"
          using kn' m h unfolding th20 th21 
          by (auto simp flip: prod.union_disjoint intro: prod.cong)
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
          by (auto simp: field_simps gbinomial_mult_fact intro: prod.cong)
        finally show ?thesis by simp
      qed
    qed
    then show ?gchoose and ?pochhammer
      using nz' by force+
  qed
  have "?r = ((a + b) gchoose n) * (of_nat (fact n) / (?m1 n * pochhammer (- b) n))"
    unfolding gbinomial_pochhammer
    using bn0 by (auto simp add: field_simps)
  also have "\<dots> = ?l"
    using bn0
    unfolding gbinomial_Vandermonde[symmetric]
    apply (simp add: th00)
    by (simp add: gbinomial_pochhammer sum_distrib_right sum_distrib_left field_simps)
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
  have h: "?b \<noteq> of_nat j" if "j < n" for j
  proof -
    have "c \<noteq> - of_nat (n - j - 1)"
      using c that by auto
    with that show ?thesis
      by (auto simp add: algebra_simps of_nat_diff)
  qed
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
  by (intro fps_ext) (simp add: fps_cos_def)

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
    also have "\<dots> = (- 1)^(n div 2) * c^Suc n / of_nat (fact n)"
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
    also have "\<dots> = (- 1)^((n + 1) div 2) * c^Suc n * (of_nat (n+1) / (of_nat (Suc n) * of_nat (fact n)))"
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
    by (simp add:  fps_deriv_power fps_sin_deriv fps_cos_deriv field_simps flip: fps_const_neg)
  then have "?lhs = fps_const (?lhs $ 0)"
    unfolding fps_deriv_eq_0_iff .
  also have "\<dots> = 1"
    by (simp add: fps_eq_iff numeral_2_eq_2 fps_mult_nth fps_cos_def fps_sin_def)
  finally show ?thesis .
qed

lemma fps_sin_nth_0 [simp]: "fps_sin c $ 0 = 0"
  unfolding fps_sin_def by simp

lemma fps_sin_nth_1 [simp]: "fps_sin c $ Suc 0 = c"
  unfolding fps_sin_def by simp

lemma fps_sin_nth_add_2:
    "fps_sin c $ (n + 2) = - (c * c * fps_sin c $ n / (of_nat (n + 1) * of_nat (n + 2)))"
proof (cases n)
  case (Suc n')
  then show ?thesis
    unfolding fps_sin_def by (simp add: field_simps)
qed (auto simp: fps_sin_def)


lemma fps_cos_nth_0 [simp]: "fps_cos c $ 0 = 1"
  unfolding fps_cos_def by simp

lemma fps_cos_nth_1 [simp]: "fps_cos c $ Suc 0 = 0"
  unfolding fps_cos_def by simp

lemma fps_cos_nth_add_2:
  "fps_cos c $ (n + 2) = - (c * c * fps_cos c $ n / (of_nat (n + 1) * of_nat (n + 2)))"
proof (cases n)
  case (Suc n')
  then show ?thesis
    unfolding fps_cos_def by (simp add: field_simps)
qed (auto simp: fps_cos_def)

lemma nat_add_1_add_1: "(n::nat) + 1 + 1 = n + 2"
  by simp

lemma eq_fps_sin:
  assumes a0: "a $ 0 = 0"
    and a1: "a $ 1 = c"
    and a2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "fps_sin c = a"
proof (rule fps_ext)
  fix n
  show "fps_sin c $ n = a $ n"
  proof (induction n rule: nat_induct2)
    case (step n)
    then have "of_nat (n + 1) * (of_nat (n + 2) * a $ (n + 2)) =
     - (c * c * fps_sin c $ n)"
      using a2
      by (metis fps_const_mult fps_deriv_nth fps_mult_left_const_nth fps_neg_nth nat_add_1_add_1)
    with step show ?case
      by (metis (no_types, lifting) a0 add.commute add.inverse_inverse fps_sin_nth_0 fps_sin_nth_add_2 mult_divide_mult_cancel_left_if mult_minus_right nonzero_mult_div_cancel_left not_less_zero of_nat_eq_0_iff plus_1_eq_Suc zero_less_Suc)
  qed (use assms in auto)
qed

lemma eq_fps_cos:
  assumes a0: "a $ 0 = 1"
    and a1: "a $ 1 = 0"
    and a2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "fps_cos c = a"
proof (rule fps_ext)
  fix n
  show "fps_cos c $ n = a $ n"
  proof (induction n rule: nat_induct2)
    case (step n)
    then have "of_nat (n + 1) * (of_nat (n + 2) * a $ (n + 2)) =
     - (c * c * fps_cos c $ n)"
      using a2
      by (metis fps_const_mult fps_deriv_nth fps_mult_left_const_nth fps_neg_nth nat_add_1_add_1)
    with step show ?case
      by (metis (no_types, lifting) a0 add.commute add.inverse_inverse fps_cos_nth_0 fps_cos_nth_add_2 mult_divide_mult_cancel_left_if mult_minus_right nonzero_mult_div_cancel_left not_less_zero of_nat_eq_0_iff plus_1_eq_Suc zero_less_Suc)
  qed (use assms in auto)
qed

lemma fps_sin_add: "fps_sin (a + b) = fps_sin a * fps_cos b + fps_cos a * fps_sin b"
proof -
  have "fps_deriv (fps_deriv (fps_sin a * fps_cos b + fps_cos a * fps_sin b)) =
         - (fps_const (a + b) * fps_const (a + b) * (fps_sin a * fps_cos b + fps_cos a * fps_sin b))"
    by (simp flip: fps_const_neg fps_const_add fps_const_mult
        add: fps_sin_deriv fps_cos_deriv algebra_simps)
  then show ?thesis
    by (auto intro: eq_fps_sin)
qed


lemma fps_cos_add: "fps_cos (a + b) = fps_cos a * fps_cos b - fps_sin a * fps_sin b"
proof -
  have "fps_deriv
     (fps_deriv (fps_cos a * fps_cos b - fps_sin a * fps_sin b)) =
    - (fps_const (a + b) * fps_const (a + b) *
       (fps_cos a * fps_cos b - fps_sin a * fps_sin b))"
    by (simp flip: fps_const_neg fps_const_add fps_const_mult
        add: fps_sin_deriv fps_cos_deriv algebra_simps)
  then show ?thesis
    by (auto intro: eq_fps_cos)
qed

lemma fps_sin_even: "fps_sin (- c) = - fps_sin c"
  by (simp add: fps_eq_iff fps_sin_def)

lemma fps_cos_odd: "fps_cos (- c) = fps_cos c"
  by (simp add: fps_eq_iff fps_cos_def)

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
  unfolding fps_tan_def fps_sin_fps_exp_ii fps_cos_fps_exp_ii
  by (simp add: fps_divide_unit fps_inverse_mult fps_const_inverse)

lemma fps_demoivre:
  "(fps_cos a + fps_const \<i> * fps_sin a)^n =
    fps_cos (of_nat n * a) + fps_const \<i> * fps_sin (of_nat n * a)"
  unfolding fps_exp_ii_sin_cos[symmetric] fps_exp_power_mult
  by (simp add: ac_simps)


subsection \<open>Hypergeometric series\<close>

definition "fps_hypergeo as bs (c::'a::field_char_0) =
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
  by (induct as arbitrary: v) (simp_all add: foldl_mult_start)

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
    by (simp add: fps_eq_iff pochhammer_fact[symmetric]
      fps_compose_nth power_mult_distrib if_distrib cong del: if_weak_cong)
qed

lemma fps_hypergeo_B[simp]: "fps_hypergeo [-a] [] (- 1) = fps_binomial a"
  by (simp add: fps_eq_iff gbinomial_pochhammer algebra_simps)

lemma fps_hypergeo_0[simp]: "fps_hypergeo as bs c $ 0 = 1"
proof -
  have "foldl (\<lambda>(r::'a) (a::'a). r) 1 as = 1" for as
    by (induction as) auto
  then show ?thesis
    by auto
qed

lemma foldl_prod_prod:
  "foldl (\<lambda>(r::'b::comm_ring_1) (x::'a::comm_ring_1). r * f x) v as * foldl (\<lambda>r x. r * g x) w as =
    foldl (\<lambda>r x. r * f x * g x) (v * w) as"
  by (induct as arbitrary: v w) (simp_all add: algebra_simps)


lemma fps_hypergeo_rec:
  "fps_hypergeo as bs c $ Suc n = ((foldl (\<lambda>r a. r* (a + of_nat n)) c as) /
    (foldl (\<lambda>r b. r * (b + of_nat n)) (of_nat (Suc n)) bs )) * fps_hypergeo as bs c $ n"
  apply (simp add: foldl_mult_start del: of_nat_Suc of_nat_add fact_Suc)
  unfolding foldl_prod_prod[unfolded foldl_mult_start] pochhammer_Suc
  by (simp add: algebra_simps)

lemma fps_XD_nth[simp]: "fps_XD a $ n = of_nat n * a$n"
  by (simp add: fps_XD_def)

lemma fps_XD_0th[simp]: "fps_XD a $ 0 = 0"
  by simp
lemma fps_XD_Suc[simp]:" fps_XD a $ Suc n = of_nat (Suc n) * a $ Suc n"
  by simp

definition "fps_XDp c a = fps_XD a + fps_const c * a"

lemma fps_XDp_nth[simp]: "fps_XDp c a $ n = (c + of_nat n) * a$n"
  by (simp add: fps_XDp_def algebra_simps)

lemma fps_XDp_commute: "fps_XDp b \<circ> fps_XDp (c::'a::comm_ring_1) = fps_XDp c \<circ> fps_XDp b"
  by (simp add: fps_XDp_def fun_eq_iff fps_eq_iff algebra_simps)

lemma fps_XDp0 [simp]: "fps_XDp 0 = fps_XD"
  by (simp add: fun_eq_iff fps_eq_iff)

lemma fps_XDp_fps_integral [simp]:
  fixes  a :: "'a::{division_ring,ring_char_0} fps"
  shows  "fps_XDp 0 (fps_integral a c) = fps_X * a"
  using  fps_deriv_fps_integral[of a c]
  by     (simp add: fps_XD_def)

lemma fps_hypergeo_minus_nat:
  "fps_hypergeo [- of_nat n] [- of_nat (n + m)] (c::'a::field_char_0) $ k =
    (if k \<le> n then
      pochhammer (- of_nat n) k * c ^ k / (pochhammer (- of_nat (n + m)) k * of_nat (fact k))
     else 0)"
  "fps_hypergeo [- of_nat m] [- of_nat (m + n)] (c::'a::field_char_0) $ k =
    (if k \<le> m then
      pochhammer (- of_nat m) k * c ^ k / (pochhammer (- of_nat (m + n)) k * of_nat (fact k))
     else 0)"
  by (simp_all add: pochhammer_eq_0_iff)

lemma pochhammer_rec_if: "pochhammer a n = (if n = 0 then 1 else a * pochhammer (a + 1) (n - 1))"
  by (cases n) (simp_all add: pochhammer_rec)

lemma fps_XDp_foldr_nth [simp]: "foldr (\<lambda>c r. fps_XDp c \<circ> r) cs (\<lambda>c. fps_XDp c a) c0 $ n =
    foldr (\<lambda>c r. (c + of_nat n) * r) cs (c0 + of_nat n) * a$n"
  by (induct cs arbitrary: c0) (simp_all add: algebra_simps)

lemma genric_fps_XDp_foldr_nth:
  assumes f: "\<forall>n c a. f c a $ n = (of_nat n + k c) * a$n"
  shows "foldr (\<lambda>c r. f c \<circ> r) cs (\<lambda>c. g c a) c0 $ n =
    foldr (\<lambda>c r. (k c + of_nat n) * r) cs (g c0 a $ n)"
  by (induct cs arbitrary: c0) (simp_all add: algebra_simps f)

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

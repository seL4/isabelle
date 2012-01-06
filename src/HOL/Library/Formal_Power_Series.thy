(*  Title:      HOL/Library/Formal_Power_Series.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header{* A formalization of formal power series *}

theory Formal_Power_Series
imports Complex_Main Binomial
begin


subsection {* The type of formal power series*}

typedef (open) 'a fps = "{f :: nat \<Rightarrow> 'a. True}"
  morphisms fps_nth Abs_fps
  by simp

notation fps_nth (infixl "$" 75)

lemma expand_fps_eq: "p = q \<longleftrightarrow> (\<forall>n. p $ n = q $ n)"
  by (simp add: fps_nth_inject [symmetric] fun_eq_iff)

lemma fps_ext: "(\<And>n. p $ n = q $ n) \<Longrightarrow> p = q"
  by (simp add: expand_fps_eq)

lemma fps_nth_Abs_fps [simp]: "Abs_fps f $ n = f n"
  by (simp add: Abs_fps_inverse)

text{* Definition of the basic elements 0 and 1 and the basic operations of addition, negation and multiplication *}

instantiation fps :: (zero) zero
begin

definition fps_zero_def:
  "0 = Abs_fps (\<lambda>n. 0)"

instance ..
end

lemma fps_zero_nth [simp]: "0 $ n = 0"
  unfolding fps_zero_def by simp

instantiation fps :: ("{one, zero}") one
begin

definition fps_one_def:
  "1 = Abs_fps (\<lambda>n. if n = 0 then 1 else 0)"

instance ..
end

lemma fps_one_nth [simp]: "1 $ n = (if n = 0 then 1 else 0)"
  unfolding fps_one_def by simp

instantiation fps :: (plus)  plus
begin

definition fps_plus_def:
  "op + = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n + g $ n))"

instance ..
end

lemma fps_add_nth [simp]: "(f + g) $ n = f $ n + g $ n"
  unfolding fps_plus_def by simp

instantiation fps :: (minus) minus
begin

definition fps_minus_def:
  "op - = (\<lambda>f g. Abs_fps (\<lambda>n. f $ n - g $ n))"

instance ..
end

lemma fps_sub_nth [simp]: "(f - g) $ n = f $ n - g $ n"
  unfolding fps_minus_def by simp

instantiation fps :: (uminus) uminus
begin

definition fps_uminus_def:
  "uminus = (\<lambda>f. Abs_fps (\<lambda>n. - (f $ n)))"

instance ..
end

lemma fps_neg_nth [simp]: "(- f) $ n = - (f $ n)"
  unfolding fps_uminus_def by simp

instantiation fps :: ("{comm_monoid_add, times}")  times
begin

definition fps_times_def:
  "op * = (\<lambda>f g. Abs_fps (\<lambda>n. \<Sum>i=0..n. f $ i * g $ (n - i)))"

instance ..
end

lemma fps_mult_nth: "(f * g) $ n = (\<Sum>i=0..n. f$i * g$(n - i))"
  unfolding fps_times_def by simp

declare atLeastAtMost_iff[presburger]
declare Bex_def[presburger]
declare Ball_def[presburger]

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

subsection{* Formal power series form a commutative ring with unity, if the range of sequences
  they represent is a commutative ring with unity*}

instance fps :: (semigroup_add) semigroup_add
proof
  fix a b c :: "'a fps" show "a + b + c = a + (b + c)"
    by (simp add: fps_ext add_assoc)
qed

instance fps :: (ab_semigroup_add) ab_semigroup_add
proof
  fix a b :: "'a fps" show "a + b = b + a"
    by (simp add: fps_ext add_commute)
qed

lemma fps_mult_assoc_lemma:
  fixes k :: nat and f :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>j=0..k. \<Sum>i=0..j. f i (j - i) (n - j)) =
         (\<Sum>j=0..k. \<Sum>i=0..k - j. f j i (n - j - i))"
proof (induct k)
  case 0 show ?case by simp
next
  case (Suc k) thus ?case
    by (simp add: Suc_diff_le setsum_addf add_assoc
             cong: strong_setsum_cong)
qed

instance fps :: (semiring_0) semigroup_mult
proof
  fix a b c :: "'a fps"
  show "(a * b) * c = a * (b * c)"
  proof (rule fps_ext)
    fix n :: nat
    have "(\<Sum>j=0..n. \<Sum>i=0..j. a$i * b$(j - i) * c$(n - j)) =
          (\<Sum>j=0..n. \<Sum>i=0..n - j. a$j * b$i * c$(n - j - i))"
      by (rule fps_mult_assoc_lemma)
    thus "((a * b) * c) $ n = (a * (b * c)) $ n"
      by (simp add: fps_mult_nth setsum_right_distrib
                    setsum_left_distrib mult_assoc)
  qed
qed

lemma fps_mult_commute_lemma:
  fixes n :: nat and f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i=0..n. f i (n - i)) = (\<Sum>i=0..n. f (n - i) i)"
proof (rule setsum_reindex_cong)
  show "inj_on (\<lambda>i. n - i) {0..n}"
    by (rule inj_onI) simp
  show "{0..n} = (\<lambda>i. n - i) ` {0..n}"
    by (auto, rule_tac x="n - x" in image_eqI, simp_all)
next
  fix i assume "i \<in> {0..n}"
  hence "n - (n - i) = i" by simp
  thus "f (n - i) i = f (n - i) (n - (n - i))" by simp
qed

instance fps :: (comm_semiring_0) ab_semigroup_mult
proof
  fix a b :: "'a fps"
  show "a * b = b * a"
  proof (rule fps_ext)
    fix n :: nat
    have "(\<Sum>i=0..n. a$i * b$(n - i)) = (\<Sum>i=0..n. a$(n - i) * b$i)"
      by (rule fps_mult_commute_lemma)
    thus "(a * b) $ n = (b * a) $ n"
      by (simp add: fps_mult_nth mult_commute)
  qed
qed

instance fps :: (monoid_add) monoid_add
proof
  fix a :: "'a fps" show "0 + a = a "
    by (simp add: fps_ext)
next
  fix a :: "'a fps" show "a + 0 = a "
    by (simp add: fps_ext)
qed

instance fps :: (comm_monoid_add) comm_monoid_add
proof
  fix a :: "'a fps" show "0 + a = a "
    by (simp add: fps_ext)
qed

instance fps :: (semiring_1) monoid_mult
proof
  fix a :: "'a fps" show "1 * a = a"
    by (simp add: fps_ext fps_mult_nth mult_delta_left setsum_delta)
next
  fix a :: "'a fps" show "a * 1 = a"
    by (simp add: fps_ext fps_mult_nth mult_delta_right setsum_delta')
qed

instance fps :: (cancel_semigroup_add) cancel_semigroup_add
proof
  fix a b c :: "'a fps"
  assume "a + b = a + c" then show "b = c"
    by (simp add: expand_fps_eq)
next
  fix a b c :: "'a fps"
  assume "b + a = c + a" then show "b = c"
    by (simp add: expand_fps_eq)
qed

instance fps :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
proof
  fix a b c :: "'a fps"
  assume "a + b = a + c" then show "b = c"
    by (simp add: expand_fps_eq)
qed

instance fps :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance fps :: (group_add) group_add
proof
  fix a :: "'a fps" show "- a + a = 0"
    by (simp add: fps_ext)
next
  fix a b :: "'a fps" show "a - b = a + - b"
    by (simp add: fps_ext diff_minus)
qed

instance fps :: (ab_group_add) ab_group_add
proof
  fix a :: "'a fps"
  show "- a + a = 0"
    by (simp add: fps_ext)
next
  fix a b :: "'a fps"
  show "a - b = a + - b"
    by (simp add: fps_ext)
qed

instance fps :: (zero_neq_one) zero_neq_one
  by default (simp add: expand_fps_eq)

instance fps :: (semiring_0) semiring
proof
  fix a b c :: "'a fps"
  show "(a + b) * c = a * c + b * c"
    by (simp add: expand_fps_eq fps_mult_nth left_distrib setsum_addf)
next
  fix a b c :: "'a fps"
  show "a * (b + c) = a * b + a * c"
    by (simp add: expand_fps_eq fps_mult_nth right_distrib setsum_addf)
qed

instance fps :: (semiring_0) semiring_0
proof
  fix a:: "'a fps" show "0 * a = 0"
    by (simp add: fps_ext fps_mult_nth)
next
  fix a:: "'a fps" show "a * 0 = 0"
    by (simp add: fps_ext fps_mult_nth)
qed

instance fps :: (semiring_0_cancel) semiring_0_cancel ..

subsection {* Selection of the nth power of the implicit variable in the infinite sum*}

lemma fps_nonzero_nth: "f \<noteq> 0 \<longleftrightarrow> (\<exists> n. f $n \<noteq> 0)"
  by (simp add: expand_fps_eq)

lemma fps_nonzero_nth_minimal:
  "f \<noteq> 0 \<longleftrightarrow> (\<exists>n. f $ n \<noteq> 0 \<and> (\<forall>m<n. f $ m = 0))"
proof
  let ?n = "LEAST n. f $ n \<noteq> 0"
  assume "f \<noteq> 0"
  then have "\<exists>n. f $ n \<noteq> 0"
    by (simp add: fps_nonzero_nth)
  then have "f $ ?n \<noteq> 0"
    by (rule LeastI_ex)
  moreover have "\<forall>m<?n. f $ m = 0"
    by (auto dest: not_less_Least)
  ultimately have "f $ ?n \<noteq> 0 \<and> (\<forall>m<?n. f $ m = 0)" ..
  then show "\<exists>n. f $ n \<noteq> 0 \<and> (\<forall>m<n. f $ m = 0)" ..
next
  assume "\<exists>n. f $ n \<noteq> 0 \<and> (\<forall>m<n. f $ m = 0)"
  then show "f \<noteq> 0" by (auto simp add: expand_fps_eq)
qed

lemma fps_eq_iff: "f = g \<longleftrightarrow> (\<forall>n. f $ n = g $n)"
  by (rule expand_fps_eq)

lemma fps_setsum_nth: "(setsum f S) $ n = setsum (\<lambda>k. (f k) $ n) S"
proof (cases "finite S")
  assume "\<not> finite S" then show ?thesis by simp
next
  assume "finite S"
  then show ?thesis by (induct set: finite) auto
qed

subsection{* Injection of the basic ring elements and multiplication by scalars *}

definition
  "fps_const c = Abs_fps (\<lambda>n. if n = 0 then c else 0)"

lemma fps_nth_fps_const [simp]: "fps_const c $ n = (if n = 0 then c else 0)"
  unfolding fps_const_def by simp

lemma fps_const_0_eq_0 [simp]: "fps_const 0 = 0"
  by (simp add: fps_ext)

lemma fps_const_1_eq_1 [simp]: "fps_const 1 = 1"
  by (simp add: fps_ext)

lemma fps_const_neg [simp]: "- (fps_const (c::'a::ring)) = fps_const (- c)"
  by (simp add: fps_ext)

lemma fps_const_add [simp]: "fps_const (c::'a\<Colon>monoid_add) + fps_const d = fps_const (c + d)"
  by (simp add: fps_ext)
lemma fps_const_sub [simp]: "fps_const (c::'a\<Colon>group_add) - fps_const d = fps_const (c - d)"
  by (simp add: fps_ext)
lemma fps_const_mult[simp]: "fps_const (c::'a\<Colon>ring) * fps_const d = fps_const (c * d)"
  by (simp add: fps_eq_iff fps_mult_nth setsum_0')

lemma fps_const_add_left: "fps_const (c::'a\<Colon>monoid_add) + f = Abs_fps (\<lambda>n. if n = 0 then c + f$0 else f$n)"
  by (simp add: fps_ext)

lemma fps_const_add_right: "f + fps_const (c::'a\<Colon>monoid_add) = Abs_fps (\<lambda>n. if n = 0 then f$0 + c else f$n)"
  by (simp add: fps_ext)

lemma fps_const_mult_left: "fps_const (c::'a\<Colon>semiring_0) * f = Abs_fps (\<lambda>n. c * f$n)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_left setsum_delta)

lemma fps_const_mult_right: "f * fps_const (c::'a\<Colon>semiring_0) = Abs_fps (\<lambda>n. f$n * c)"
  unfolding fps_eq_iff fps_mult_nth
  by (simp add: fps_const_def mult_delta_right setsum_delta')

lemma fps_mult_left_const_nth [simp]: "(fps_const (c::'a::semiring_1) * f)$n = c* f$n"
  by (simp add: fps_mult_nth mult_delta_left setsum_delta)

lemma fps_mult_right_const_nth [simp]: "(f * fps_const (c::'a::semiring_1))$n = f$n * c"
  by (simp add: fps_mult_nth mult_delta_right setsum_delta')

subsection {* Formal power series form an integral domain*}

instance fps :: (ring) ring ..

instance fps :: (ring_1) ring_1
  by (intro_classes, auto simp add: diff_minus left_distrib)

instance fps :: (comm_ring_1) comm_ring_1
  by (intro_classes, auto simp add: diff_minus left_distrib)

instance fps :: (ring_no_zero_divisors) ring_no_zero_divisors
proof
  fix a b :: "'a fps"
  assume a0: "a \<noteq> 0" and b0: "b \<noteq> 0"
  then obtain i j where i: "a$i\<noteq>0" "\<forall>k<i. a$k=0"
    and j: "b$j \<noteq>0" "\<forall>k<j. b$k =0" unfolding fps_nonzero_nth_minimal
    by blast+
  have "(a * b) $ (i+j) = (\<Sum>k=0..i+j. a$k * b$(i+j-k))"
    by (rule fps_mult_nth)
  also have "\<dots> = (a$i * b$(i+j-i)) + (\<Sum>k\<in>{0..i+j}-{i}. a$k * b$(i+j-k))"
    by (rule setsum_diff1') simp_all
  also have "(\<Sum>k\<in>{0..i+j}-{i}. a$k * b$(i+j-k)) = 0"
    proof (rule setsum_0' [rule_format])
      fix k assume "k \<in> {0..i+j} - {i}"
      then have "k < i \<or> i+j-k < j" by auto
      then show "a$k * b$(i+j-k) = 0" using i j by auto
    qed
  also have "a$i * b$(i+j-i) + 0 = a$i * b$j" by simp
  also have "a$i * b$j \<noteq> 0" using i j by simp
  finally have "(a*b) $ (i+j) \<noteq> 0" .
  then show "a*b \<noteq> 0" unfolding fps_nonzero_nth by blast
qed

instance fps :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..

instance fps :: (idom) idom ..

instantiation fps :: (comm_ring_1) number_ring
begin
definition number_of_fps_def: "(number_of k::'a fps) = of_int k"

instance proof
qed (rule number_of_fps_def)
end

lemma number_of_fps_const: "(number_of k::('a::comm_ring_1) fps) = fps_const (of_int k)"
  
proof(induct k rule: int_induct [where k=0])
  case base thus ?case unfolding number_of_fps_def of_int_0 by simp
next
  case (step1 i) thus ?case unfolding number_of_fps_def 
    by (simp add: fps_const_add[symmetric] del: fps_const_add)
next
  case (step2 i) thus ?case unfolding number_of_fps_def 
    by (simp add: fps_const_sub[symmetric] del: fps_const_sub)
qed
subsection{* The eXtractor series X*}

lemma minus_one_power_iff: "(- (1::'a :: {comm_ring_1})) ^ n = (if even n then 1 else - 1)"
  by (induct n, auto)

definition "X = Abs_fps (\<lambda>n. if n = 1 then 1 else 0)"
lemma X_mult_nth[simp]: "(X * (f :: ('a::semiring_1) fps)) $n = (if n = 0 then 0 else f $ (n - 1))"
proof-
  {assume n: "n \<noteq> 0"
    have fN: "finite {0 .. n}" by simp
    have "(X * f) $n = (\<Sum>i = 0..n. X $ i * f $ (n - i))" by (simp add: fps_mult_nth)
    also have "\<dots> = f $ (n - 1)"
      using n by (simp add: X_def mult_delta_left setsum_delta [OF fN])
  finally have ?thesis using n by simp }
  moreover
  {assume n: "n=0" hence ?thesis by (simp add: fps_mult_nth X_def)}
  ultimately show ?thesis by blast
qed

lemma X_mult_right_nth[simp]: "((f :: ('a::comm_semiring_1) fps) * X) $n = (if n = 0 then 0 else f $ (n - 1))"
  by (metis X_mult_nth mult_commute)

lemma X_power_iff: "X^k = Abs_fps (\<lambda>n. if n = k then (1::'a::comm_ring_1) else 0)"
proof(induct k)
  case 0 thus ?case by (simp add: X_def fps_eq_iff)
next
  case (Suc k)
  {fix m
    have "(X^Suc k) $ m = (if m = 0 then (0::'a) else (X^k) $ (m - 1))"
      by (simp add: power_Suc del: One_nat_def)
    then     have "(X^Suc k) $ m = (if m = Suc k then (1::'a) else 0)"
      using Suc.hyps by (auto cong del: if_weak_cong)}
  then show ?case by (simp add: fps_eq_iff)
qed

lemma X_power_mult_nth: "(X^k * (f :: ('a::comm_ring_1) fps)) $n = (if n < k then 0 else f $ (n - k))"
  apply (induct k arbitrary: n)
  apply (simp)
  unfolding power_Suc mult_assoc
  by (case_tac n, auto)

lemma X_power_mult_right_nth: "((f :: ('a::comm_ring_1) fps) * X^k) $n = (if n < k then 0 else f $ (n - k))"
  by (metis X_power_mult_nth mult_commute)



  
subsection{* Formal Power series form a metric space *}

definition (in dist) ball_def: "ball x r = {y. dist y x < r}"
instantiation fps :: (comm_ring_1) dist
begin

definition dist_fps_def: "dist (a::'a fps) b = (if (\<exists>n. a$n \<noteq> b$n) then inverse (2 ^ The (leastP (\<lambda>n. a$n \<noteq> b$n))) else 0)"

lemma dist_fps_ge0: "dist (a::'a fps) b \<ge> 0"
  by (simp add: dist_fps_def)

lemma dist_fps_sym: "dist (a::'a fps) b = dist b a"
  apply (auto simp add: dist_fps_def)
  apply (rule cong[OF refl, where x="(\<lambda>n\<Colon>nat. a $ n \<noteq> b $ n)"])
  apply (rule ext)
  by auto
instance ..
end

lemma fps_nonzero_least_unique: assumes a0: "a \<noteq> 0"
  shows "\<exists>! n. leastP (\<lambda>n. a$n \<noteq> 0) n"
proof-
  from fps_nonzero_nth_minimal[of a] a0
  obtain n where n: "a$n \<noteq> 0" "\<forall>m < n. a$m = 0" by blast
  from n have ln: "leastP (\<lambda>n. a$n \<noteq> 0) n" 
    by (auto simp add: leastP_def setge_def not_le[symmetric])
  moreover
  {fix m assume "leastP (\<lambda>n. a$n \<noteq> 0) m"
    then have "m = n" using ln
      apply (auto simp add: leastP_def setge_def)
      apply (erule allE[where x=n])
      apply (erule allE[where x=m])
      by simp}
  ultimately show ?thesis by blast
qed

lemma fps_eq_least_unique: assumes ab: "(a::('a::ab_group_add) fps) \<noteq> b"
  shows "\<exists>! n. leastP (\<lambda>n. a$n \<noteq> b$n) n"
using fps_nonzero_least_unique[of "a - b"] ab
by auto

instantiation fps :: (comm_ring_1) metric_space
begin

definition open_fps_def: "open (S :: 'a fps set) = (\<forall>a \<in> S. \<exists>r. r >0 \<and> ball a r \<subseteq> S)"

instance
proof
  fix S :: "'a fps set" 
  show "open S = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
    by (auto simp add: open_fps_def ball_def subset_eq)
next
{  fix a b :: "'a fps"
  {assume ab: "a = b"
   then have "\<not> (\<exists>n. a$n \<noteq> b$n)" by simp
   then have "dist a b = 0" by (simp add: dist_fps_def)}
 moreover
 {assume d: "dist a b = 0"
   then have "\<forall>n. a$n = b$n" 
     by - (rule ccontr, simp add: dist_fps_def)
   then have "a = b" by (simp add: fps_eq_iff)}
 ultimately show "dist a b =0 \<longleftrightarrow> a = b" by blast}
note th = this
from th have th'[simp]: "\<And>a::'a fps. dist a a = 0" by simp
  fix a b c :: "'a fps"
  {assume ab: "a = b" then have d0: "dist a b = 0"  unfolding th .
    then have "dist a b \<le> dist a c + dist b c" 
      using dist_fps_ge0[of a c] dist_fps_ge0[of b c] by simp}
  moreover
  {assume c: "c = a \<or> c = b" then have "dist a b \<le> dist a c + dist b c"
      by (cases "c=a", simp_all add: th dist_fps_sym) }
  moreover
  {assume ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    let ?P = "\<lambda>a b n. a$n \<noteq> b$n"
    from fps_eq_least_unique[OF ab] fps_eq_least_unique[OF ac] 
      fps_eq_least_unique[OF bc]
    obtain nab nac nbc where nab: "leastP (?P a b) nab" 
      and nac: "leastP (?P a c) nac" 
      and nbc: "leastP (?P b c) nbc" by blast
    from nab have nab': "\<And>m. m < nab \<Longrightarrow> a$m = b$m" "a$nab \<noteq> b$nab"
      by (auto simp add: leastP_def setge_def)
    from nac have nac': "\<And>m. m < nac \<Longrightarrow> a$m = c$m" "a$nac \<noteq> c$nac"
      by (auto simp add: leastP_def setge_def)
    from nbc have nbc': "\<And>m. m < nbc \<Longrightarrow> b$m = c$m" "b$nbc \<noteq> c$nbc"
      by (auto simp add: leastP_def setge_def)

    have th0: "\<And>(a::'a fps) b. a \<noteq> b \<longleftrightarrow> (\<exists>n. a$n \<noteq> b$n)"
      by (simp add: fps_eq_iff)
    from ab ac bc nab nac nbc 
    have dab: "dist a b = inverse (2 ^ nab)" 
      and dac: "dist a c = inverse (2 ^ nac)" 
      and dbc: "dist b c = inverse (2 ^ nbc)"
      unfolding th0
      apply (simp_all add: dist_fps_def)
      apply (erule the1_equality[OF fps_eq_least_unique[OF ab]])
      apply (erule the1_equality[OF fps_eq_least_unique[OF ac]])
      by (erule the1_equality[OF fps_eq_least_unique[OF bc]])
    from ab ac bc have nz: "dist a b \<noteq> 0" "dist a c \<noteq> 0" "dist b c \<noteq> 0"
      unfolding th by simp_all
    from nz have pos: "dist a b > 0" "dist a c > 0" "dist b c > 0"
      using dist_fps_ge0[of a b] dist_fps_ge0[of a c] dist_fps_ge0[of b c] 
      by auto
    have th1: "\<And>n. (2::real)^n >0" by auto
    {assume h: "dist a b > dist a c + dist b c"
      then have gt: "dist a b > dist a c" "dist a b > dist b c"
        using pos by auto
      from gt have gtn: "nab < nbc" "nab < nac"
        unfolding dab dbc dac by (auto simp add: th1)
      from nac'(1)[OF gtn(2)] nbc'(1)[OF gtn(1)]
      have "a$nab = b$nab" by simp
      with nab'(2) have False  by simp}
    then have "dist a b \<le> dist a c + dist b c"
      by (auto simp add: not_le[symmetric]) }
  ultimately show "dist a b \<le> dist a c + dist b c" by blast
qed
  
end

text{* The infinite sums and justification of the notation in textbooks*}

lemma reals_power_lt_ex: assumes xp: "x > 0" and y1: "(y::real) > 1"
  shows "\<exists>k>0. (1/y)^k < x"
proof-
  have yp: "y > 0" using y1 by simp
  from reals_Archimedean2[of "max 0 (- log y x) + 1"]
  obtain k::nat where k: "real k > max 0 (- log y x) + 1" by blast
  from k have kp: "k > 0" by simp
  from k have "real k > - log y x" by simp
  then have "ln y * real k > - ln x" unfolding log_def
    using ln_gt_zero_iff[OF yp] y1
    by (simp add: minus_divide_left field_simps del:minus_divide_left[symmetric])
  then have "ln y * real k + ln x > 0" by simp
  then have "exp (real k * ln y + ln x) > exp 0"
    by (simp add: mult_ac)
  then have "y ^ k * x > 1"
    unfolding exp_zero exp_add exp_real_of_nat_mult
    exp_ln[OF xp] exp_ln[OF yp] by simp
  then have "x > (1/y)^k" using yp 
    by (simp add: field_simps nonzero_power_divide)
  then show ?thesis using kp by blast
qed
lemma X_nth[simp]: "X$n = (if n = 1 then 1 else 0)" by (simp add: X_def)
lemma X_power_nth[simp]: "(X^k) $n = (if n = k then 1 else (0::'a::comm_ring_1))"
  by (simp add: X_power_iff)
 

lemma fps_sum_rep_nth: "(setsum (%i. fps_const(a$i)*X^i) {0..m})$n = (if n \<le> m then a$n else (0::'a::comm_ring_1))"
  apply (auto simp add: fps_eq_iff fps_setsum_nth X_power_nth cond_application_beta cond_value_iff  cong del: if_weak_cong)
  by (simp add: setsum_delta')
  
lemma fps_notation: 
  "(%n. setsum (%i. fps_const(a$i) * X^i) {0..n}) ----> a" (is "?s ----> a")
proof-
    {fix r:: real
      assume rp: "r > 0"
      have th0: "(2::real) > 1" by simp
      from reals_power_lt_ex[OF rp th0] 
      obtain n0 where n0: "(1/2)^n0 < r" "n0 > 0" by blast
      {fix n::nat
        assume nn0: "n \<ge> n0"
        then have thnn0: "(1/2)^n <= (1/2 :: real)^n0"
          by (auto intro: power_decreasing)
        {assume "?s n = a" then have "dist (?s n) a < r" 
            unfolding dist_eq_0_iff[of "?s n" a, symmetric]
            using rp by (simp del: dist_eq_0_iff)}
        moreover
        {assume neq: "?s n \<noteq> a"
          from fps_eq_least_unique[OF neq] 
          obtain k where k: "leastP (\<lambda>i. ?s n $ i \<noteq> a$i) k" by blast
          have th0: "\<And>(a::'a fps) b. a \<noteq> b \<longleftrightarrow> (\<exists>n. a$n \<noteq> b$n)"
            by (simp add: fps_eq_iff)
          from neq have dth: "dist (?s n) a = (1/2)^k"
            unfolding th0 dist_fps_def
            unfolding the1_equality[OF fps_eq_least_unique[OF neq], OF k]
            by (auto simp add: inverse_eq_divide power_divide)

          from k have kn: "k > n"
            by (simp add: leastP_def setge_def fps_sum_rep_nth split:split_if_asm)
          then have "dist (?s n) a < (1/2)^n" unfolding dth
            by (auto intro: power_strict_decreasing)
          also have "\<dots> <= (1/2)^n0" using nn0
            by (auto intro: power_decreasing)
          also have "\<dots> < r" using n0 by simp
          finally have "dist (?s n) a < r" .}
        ultimately have "dist (?s n) a < r" by blast}
      then have "\<exists>n0. \<forall> n \<ge> n0. dist (?s n) a < r " by blast}
    then show ?thesis  unfolding  LIMSEQ_def by blast
  qed

subsection{* Inverses of formal power series *}

declare setsum_cong[fundef_cong]

instantiation fps :: ("{comm_monoid_add, inverse, times, uminus}") inverse
begin

fun natfun_inverse:: "'a fps \<Rightarrow> nat \<Rightarrow> 'a" where
  "natfun_inverse f 0 = inverse (f$0)"
| "natfun_inverse f n = - inverse (f$0) * setsum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n}"

definition fps_inverse_def:
  "inverse f = (if f $ 0 = 0 then 0 else Abs_fps (natfun_inverse f))"

definition fps_divide_def: "divide = (\<lambda>(f::'a fps) g. f * inverse g)"

instance ..

end

lemma fps_inverse_zero[simp]:
  "inverse (0 :: 'a::{comm_monoid_add,inverse, times, uminus} fps) = 0"
  by (simp add: fps_ext fps_inverse_def)

lemma fps_inverse_one[simp]: "inverse (1 :: 'a::{division_ring,zero_neq_one} fps) = 1"
  apply (auto simp add: expand_fps_eq fps_inverse_def)
  by (case_tac n, auto)

lemma inverse_mult_eq_1 [intro]: assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "inverse f * f = 1"
proof-
  have c: "inverse f * f = f * inverse f" by (simp add: mult_commute)
  from f0 have ifn: "\<And>n. inverse f $ n = natfun_inverse f n"
    by (simp add: fps_inverse_def)
  from f0 have th0: "(inverse f * f) $ 0 = 1"
    by (simp add: fps_mult_nth fps_inverse_def)
  {fix n::nat assume np: "n >0 "
    from np have eq: "{0..n} = {0} \<union> {1 .. n}" by auto
    have d: "{0} \<inter> {1 .. n} = {}" by auto
    have f: "finite {0::nat}" "finite {1..n}" by auto
    from f0 np have th0: "- (inverse f$n) =
      (setsum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n}) / (f$0)"
      by (cases n, simp, simp add: divide_inverse fps_inverse_def)
    from th0[symmetric, unfolded nonzero_divide_eq_eq[OF f0]]
    have th1: "setsum (\<lambda>i. f$i * natfun_inverse f (n - i)) {1..n} =
      - (f$0) * (inverse f)$n"
      by (simp add: field_simps)
    have "(f * inverse f) $ n = (\<Sum>i = 0..n. f $i * natfun_inverse f (n - i))"
      unfolding fps_mult_nth ifn ..
    also have "\<dots> = f$0 * natfun_inverse f n
      + (\<Sum>i = 1..n. f$i * natfun_inverse f (n-i))"
      unfolding setsum_Un_disjoint[OF f d, unfolded eq[symmetric]]
      by simp
    also have "\<dots> = 0" unfolding th1 ifn by simp
    finally have "(inverse f * f)$n = 0" unfolding c . }
  with th0 show ?thesis by (simp add: fps_eq_iff)
qed

lemma fps_inverse_0_iff[simp]: "(inverse f)$0 = (0::'a::division_ring) \<longleftrightarrow> f$0 = 0"
  by (simp add: fps_inverse_def nonzero_imp_inverse_nonzero)

lemma fps_inverse_eq_0_iff[simp]: "inverse f = (0:: ('a::field) fps) \<longleftrightarrow> f $0 = 0"
proof-
  {assume "f$0 = 0" hence "inverse f = 0" by (simp add: fps_inverse_def)}
  moreover
  {assume h: "inverse f = 0" and c: "f $0 \<noteq> 0"
    from inverse_mult_eq_1[OF c] h have False by simp}
  ultimately show ?thesis by blast
qed

lemma fps_inverse_idempotent[intro]: assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "inverse (inverse f) = f"
proof-
  from f0 have if0: "inverse f $ 0 \<noteq> 0" by simp
  from inverse_mult_eq_1[OF f0] inverse_mult_eq_1[OF if0]
  have th0: "inverse f * f = inverse f * inverse (inverse f)"   by (simp add: mult_ac)
  then show ?thesis using f0 unfolding mult_cancel_left by simp
qed

lemma fps_inverse_unique: assumes f0: "f$0 \<noteq> (0::'a::field)" and fg: "f*g = 1"
  shows "inverse f = g"
proof-
  from inverse_mult_eq_1[OF f0] fg
  have th0: "inverse f * f = g * f" by (simp add: mult_ac)
  then show ?thesis using f0  unfolding mult_cancel_right
    by (auto simp add: expand_fps_eq)
qed

lemma fps_inverse_gp: "inverse (Abs_fps(\<lambda>n. (1::'a::field)))
  = Abs_fps (\<lambda>n. if n= 0 then 1 else if n=1 then - 1 else 0)"
  apply (rule fps_inverse_unique)
  apply simp
  apply (simp add: fps_eq_iff fps_mult_nth)
proof(clarsimp)
  fix n::nat assume n: "n > 0"
  let ?f = "\<lambda>i. if n = i then (1\<Colon>'a) else if n - i = 1 then - 1 else 0"
  let ?g = "\<lambda>i. if i = n then 1 else if i=n - 1 then - 1 else 0"
  let ?h = "\<lambda>i. if i=n - 1 then - 1 else 0"
  have th1: "setsum ?f {0..n} = setsum ?g {0..n}"
    by (rule setsum_cong2) auto
  have th2: "setsum ?g {0..n - 1} = setsum ?h {0..n - 1}"
    using n apply - by (rule setsum_cong2) auto
  have eq: "{0 .. n} = {0.. n - 1} \<union> {n}" by auto
  from n have d: "{0.. n - 1} \<inter> {n} = {}" by auto
  have f: "finite {0.. n - 1}" "finite {n}" by auto
  show "setsum ?f {0..n} = 0"
    unfolding th1
    apply (simp add: setsum_Un_disjoint[OF f d, unfolded eq[symmetric]] del: One_nat_def)
    unfolding th2
    by(simp add: setsum_delta)
qed

subsection{* Formal Derivatives, and the MacLaurin theorem around 0*}

definition "fps_deriv f = Abs_fps (\<lambda>n. of_nat (n + 1) * f $ (n + 1))"

lemma fps_deriv_nth[simp]: "fps_deriv f $ n = of_nat (n +1) * f $ (n+1)" by (simp add: fps_deriv_def)

lemma fps_deriv_linear[simp]: "fps_deriv (fps_const (a::'a::comm_semiring_1) * f + fps_const b * g) = fps_const a * fps_deriv f + fps_const b * fps_deriv g"
  unfolding fps_eq_iff fps_add_nth  fps_const_mult_left fps_deriv_nth by (simp add: field_simps)

lemma fps_deriv_mult[simp]:
  fixes f :: "('a :: comm_ring_1) fps"
  shows "fps_deriv (f * g) = f * fps_deriv g + fps_deriv f * g"
proof-
  let ?D = "fps_deriv"
  {fix n::nat
    let ?Zn = "{0 ..n}"
    let ?Zn1 = "{0 .. n + 1}"
    let ?f = "\<lambda>i. i + 1"
    have fi: "inj_on ?f {0..n}" by (simp add: inj_on_def)
    have eq: "{1.. n+1} = ?f ` {0..n}" by auto
    let ?g = "\<lambda>i. of_nat (i+1) * g $ (i+1) * f $ (n - i) +
        of_nat (i+1)* f $ (i+1) * g $ (n - i)"
    let ?h = "\<lambda>i. of_nat i * g $ i * f $ ((n+1) - i) +
        of_nat i* f $ i * g $ ((n + 1) - i)"
    {fix k assume k: "k \<in> {0..n}"
      have "?h (k + 1) = ?g k" using k by auto}
    note th0 = this
    have eq': "{0..n +1}- {1 .. n+1} = {0}" by auto
    have s0: "setsum (\<lambda>i. of_nat i * f $ i * g $ (n + 1 - i)) ?Zn1 = setsum (\<lambda>i. of_nat (n + 1 - i) * f $ (n + 1 - i) * g $ i) ?Zn1"
      apply (rule setsum_reindex_cong[where f="\<lambda>i. n + 1 - i"])
      apply (simp add: inj_on_def Ball_def)
      apply presburger
      apply (rule set_eqI)
      apply (presburger add: image_iff)
      by simp
    have s1: "setsum (\<lambda>i. f $ i * g $ (n + 1 - i)) ?Zn1 = setsum (\<lambda>i. f $ (n + 1 - i) * g $ i) ?Zn1"
      apply (rule setsum_reindex_cong[where f="\<lambda>i. n + 1 - i"])
      apply (simp add: inj_on_def Ball_def)
      apply presburger
      apply (rule set_eqI)
      apply (presburger add: image_iff)
      by simp
    have "(f * ?D g + ?D f * g)$n = (?D g * f + ?D f * g)$n" by (simp only: mult_commute)
    also have "\<dots> = (\<Sum>i = 0..n. ?g i)"
      by (simp add: fps_mult_nth setsum_addf[symmetric])
    also have "\<dots> = setsum ?h {1..n+1}"
      using th0 setsum_reindex_cong[OF fi eq, of "?g" "?h"] by auto
    also have "\<dots> = setsum ?h {0..n+1}"
      apply (rule setsum_mono_zero_left)
      apply simp
      apply (simp add: subset_eq)
      unfolding eq'
      by simp
    also have "\<dots> = (fps_deriv (f * g)) $ n"
      apply (simp only: fps_deriv_nth fps_mult_nth setsum_addf)
      unfolding s0 s1
      unfolding setsum_addf[symmetric] setsum_right_distrib
      apply (rule setsum_cong2)
      by (auto simp add: of_nat_diff field_simps)
    finally have "(f * ?D g + ?D f * g) $ n = ?D (f*g) $ n" .}
  then show ?thesis unfolding fps_eq_iff by auto
qed

lemma fps_deriv_X[simp]: "fps_deriv X = 1"
  by (simp add: fps_deriv_def X_def fps_eq_iff)

lemma fps_deriv_neg[simp]: "fps_deriv (- (f:: ('a:: comm_ring_1) fps)) = - (fps_deriv f)"
  by (simp add: fps_eq_iff fps_deriv_def)
lemma fps_deriv_add[simp]: "fps_deriv ((f:: ('a::comm_ring_1) fps) + g) = fps_deriv f + fps_deriv g"
  using fps_deriv_linear[of 1 f 1 g] by simp

lemma fps_deriv_sub[simp]: "fps_deriv ((f:: ('a::comm_ring_1) fps) - g) = fps_deriv f - fps_deriv g"
  unfolding diff_minus by simp

lemma fps_deriv_const[simp]: "fps_deriv (fps_const c) = 0"
  by (simp add: fps_ext fps_deriv_def fps_const_def)

lemma fps_deriv_mult_const_left[simp]: "fps_deriv (fps_const (c::'a::comm_ring_1) * f) = fps_const c * fps_deriv f"
  by simp

lemma fps_deriv_0[simp]: "fps_deriv 0 = 0"
  by (simp add: fps_deriv_def fps_eq_iff)

lemma fps_deriv_1[simp]: "fps_deriv 1 = 0"
  by (simp add: fps_deriv_def fps_eq_iff )

lemma fps_deriv_mult_const_right[simp]: "fps_deriv (f * fps_const (c::'a::comm_ring_1)) = fps_deriv f * fps_const c"
  by simp

lemma fps_deriv_setsum: "fps_deriv (setsum f S) = setsum (\<lambda>i. fps_deriv (f i :: ('a::comm_ring_1) fps)) S"
proof-
  {assume "\<not> finite S" hence ?thesis by simp}
  moreover
  {assume fS: "finite S"
    have ?thesis  by (induct rule: finite_induct[OF fS], simp_all)}
  ultimately show ?thesis by blast
qed

lemma fps_deriv_eq_0_iff[simp]: "fps_deriv f = 0 \<longleftrightarrow> (f = fps_const (f$0 :: 'a::{idom,semiring_char_0}))"
proof-
  {assume "f= fps_const (f$0)" hence "fps_deriv f = fps_deriv (fps_const (f$0))" by simp
    hence "fps_deriv f = 0" by simp }
  moreover
  {assume z: "fps_deriv f = 0"
    hence "\<forall>n. (fps_deriv f)$n = 0" by simp
    hence "\<forall>n. f$(n+1) = 0" by (simp del: of_nat_Suc of_nat_add One_nat_def)
    hence "f = fps_const (f$0)"
      apply (clarsimp simp add: fps_eq_iff fps_const_def)
      apply (erule_tac x="n - 1" in allE)
      by simp}
  ultimately show ?thesis by blast
qed

lemma fps_deriv_eq_iff:
  fixes f:: "('a::{idom,semiring_char_0}) fps"
  shows "fps_deriv f = fps_deriv g \<longleftrightarrow> (f = fps_const(f$0 - g$0) + g)"
proof-
  have "fps_deriv f = fps_deriv g \<longleftrightarrow> fps_deriv (f - g) = 0" by simp
  also have "\<dots> \<longleftrightarrow> f - g = fps_const ((f-g)$0)" unfolding fps_deriv_eq_0_iff ..
  finally show ?thesis by (simp add: field_simps)
qed

lemma fps_deriv_eq_iff_ex: "(fps_deriv f = fps_deriv g) \<longleftrightarrow> (\<exists>(c::'a::{idom,semiring_char_0}). f = fps_const c + g)"
  apply auto unfolding fps_deriv_eq_iff by blast


fun fps_nth_deriv :: "nat \<Rightarrow> ('a::semiring_1) fps \<Rightarrow> 'a fps" where
  "fps_nth_deriv 0 f = f"
| "fps_nth_deriv (Suc n) f = fps_nth_deriv n (fps_deriv f)"

lemma fps_nth_deriv_commute: "fps_nth_deriv (Suc n) f = fps_deriv (fps_nth_deriv n f)"
  by (induct n arbitrary: f, auto)

lemma fps_nth_deriv_linear[simp]: "fps_nth_deriv n (fps_const (a::'a::comm_semiring_1) * f + fps_const b * g) = fps_const a * fps_nth_deriv n f + fps_const b * fps_nth_deriv n g"
  by (induct n arbitrary: f g, auto simp add: fps_nth_deriv_commute)

lemma fps_nth_deriv_neg[simp]: "fps_nth_deriv n (- (f:: ('a:: comm_ring_1) fps)) = - (fps_nth_deriv n f)"
  by (induct n arbitrary: f, simp_all)

lemma fps_nth_deriv_add[simp]: "fps_nth_deriv n ((f:: ('a::comm_ring_1) fps) + g) = fps_nth_deriv n f + fps_nth_deriv n g"
  using fps_nth_deriv_linear[of n 1 f 1 g] by simp

lemma fps_nth_deriv_sub[simp]: "fps_nth_deriv n ((f:: ('a::comm_ring_1) fps) - g) = fps_nth_deriv n f - fps_nth_deriv n g"
  unfolding diff_minus fps_nth_deriv_add by simp

lemma fps_nth_deriv_0[simp]: "fps_nth_deriv n 0 = 0"
  by (induct n, simp_all )

lemma fps_nth_deriv_1[simp]: "fps_nth_deriv n 1 = (if n = 0 then 1 else 0)"
  by (induct n, simp_all )

lemma fps_nth_deriv_const[simp]: "fps_nth_deriv n (fps_const c) = (if n = 0 then fps_const c else 0)"
  by (cases n, simp_all)

lemma fps_nth_deriv_mult_const_left[simp]: "fps_nth_deriv n (fps_const (c::'a::comm_ring_1) * f) = fps_const c * fps_nth_deriv n f"
  using fps_nth_deriv_linear[of n "c" f 0 0 ] by simp

lemma fps_nth_deriv_mult_const_right[simp]: "fps_nth_deriv n (f * fps_const (c::'a::comm_ring_1)) = fps_nth_deriv n f * fps_const c"
  using fps_nth_deriv_linear[of n "c" f 0 0] by (simp add: mult_commute)

lemma fps_nth_deriv_setsum: "fps_nth_deriv n (setsum f S) = setsum (\<lambda>i. fps_nth_deriv n (f i :: ('a::comm_ring_1) fps)) S"
proof-
  {assume "\<not> finite S" hence ?thesis by simp}
  moreover
  {assume fS: "finite S"
    have ?thesis  by (induct rule: finite_induct[OF fS], simp_all)}
  ultimately show ?thesis by blast
qed

lemma fps_deriv_maclauren_0: "(fps_nth_deriv k (f:: ('a::comm_semiring_1) fps)) $ 0 = of_nat (fact k) * f$(k)"
  by (induct k arbitrary: f) (auto simp add: field_simps of_nat_mult)

subsection {* Powers*}

lemma fps_power_zeroth_eq_one: "a$0 =1 \<Longrightarrow> a^n $ 0 = (1::'a::semiring_1)"
  by (induct n, auto simp add: expand_fps_eq fps_mult_nth)

lemma fps_power_first_eq: "(a:: 'a::comm_ring_1 fps)$0 =1 \<Longrightarrow> a^n $ 1 = of_nat n * a$1"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  note h = Suc.hyps[OF `a$0 = 1`]
  show ?case unfolding power_Suc fps_mult_nth
    using h `a$0 = 1`  fps_power_zeroth_eq_one[OF `a$0=1`] by (simp add: field_simps)
qed

lemma startsby_one_power:"a $ 0 = (1::'a::comm_ring_1) \<Longrightarrow> a^n $ 0 = 1"
  by (induct n, auto simp add: fps_mult_nth)

lemma startsby_zero_power:"a $0 = (0::'a::comm_ring_1) \<Longrightarrow> n > 0 \<Longrightarrow> a^n $0 = 0"
  by (induct n, auto simp add: fps_mult_nth)

lemma startsby_power:"a $0 = (v::'a::{comm_ring_1}) \<Longrightarrow> a^n $0 = v^n"
  by (induct n, auto simp add: fps_mult_nth power_Suc)

lemma startsby_zero_power_iff[simp]:
  "a^n $0 = (0::'a::{idom}) \<longleftrightarrow> (n \<noteq> 0 \<and> a$0 = 0)"
apply (rule iffI)
apply (induct n, auto simp add: power_Suc fps_mult_nth)
by (rule startsby_zero_power, simp_all)

lemma startsby_zero_power_prefix:
  assumes a0: "a $0 = (0::'a::idom)"
  shows "\<forall>n < k. a ^ k $ n = 0"
  using a0
proof(induct k rule: nat_less_induct)
  fix k assume H: "\<forall>m<k. a $0 =  0 \<longrightarrow> (\<forall>n<m. a ^ m $ n = 0)" and a0: "a $0 = (0\<Colon>'a)"
  let ?ths = "\<forall>m<k. a ^ k $ m = 0"
  {assume "k = 0" then have ?ths by simp}
  moreover
  {fix l assume k: "k = Suc l"
    {fix m assume mk: "m < k"
      {assume "m=0" hence "a^k $ m = 0" using startsby_zero_power[of a k] k a0
          by simp}
      moreover
      {assume m0: "m \<noteq> 0"
        have "a ^k $ m = (a^l * a) $m" by (simp add: k power_Suc mult_commute)
        also have "\<dots> = (\<Sum>i = 0..m. a ^ l $ i * a $ (m - i))" by (simp add: fps_mult_nth)
        also have "\<dots> = 0" apply (rule setsum_0')
          apply auto
          apply (case_tac "aa = m")
          using a0
          apply simp
          apply (rule H[rule_format])
          using a0 k mk by auto
        finally have "a^k $ m = 0" .}
    ultimately have "a^k $ m = 0" by blast}
    hence ?ths by blast}
  ultimately show ?ths by (cases k, auto)
qed

lemma startsby_zero_setsum_depends:
  assumes a0: "a $0 = (0::'a::idom)" and kn: "n \<ge> k"
  shows "setsum (\<lambda>i. (a ^ i)$k) {0 .. n} = setsum (\<lambda>i. (a ^ i)$k) {0 .. k}"
  apply (rule setsum_mono_zero_right)
  using kn apply auto
  apply (rule startsby_zero_power_prefix[rule_format, OF a0])
  by arith

lemma startsby_zero_power_nth_same: assumes a0: "a$0 = (0::'a::{idom})"
  shows "a^n $ n = (a$1) ^ n"
proof(induct n)
  case 0 thus ?case by (simp add: power_0)
next
  case (Suc n)
  have "a ^ Suc n $ (Suc n) = (a^n * a)$(Suc n)" by (simp add: field_simps power_Suc)
  also have "\<dots> = setsum (\<lambda>i. a^n$i * a $ (Suc n - i)) {0.. Suc n}" by (simp add: fps_mult_nth)
  also have "\<dots> = setsum (\<lambda>i. a^n$i * a $ (Suc n - i)) {n .. Suc n}"
    apply (rule setsum_mono_zero_right)
    apply simp
    apply clarsimp
    apply clarsimp
    apply (rule startsby_zero_power_prefix[rule_format, OF a0])
    apply arith
    done
  also have "\<dots> = a^n $ n * a$1" using a0 by simp
  finally show ?case using Suc.hyps by (simp add: power_Suc)
qed

lemma fps_inverse_power:
  fixes a :: "('a::{field}) fps"
  shows "inverse (a^n) = inverse a ^ n"
proof-
  {assume a0: "a$0 = 0"
    hence eq: "inverse a = 0" by (simp add: fps_inverse_def)
    {assume "n = 0" hence ?thesis by simp}
    moreover
    {assume n: "n > 0"
      from startsby_zero_power[OF a0 n] eq a0 n have ?thesis
        by (simp add: fps_inverse_def)}
    ultimately have ?thesis by blast}
  moreover
  {assume a0: "a$0 \<noteq> 0"
    have ?thesis
      apply (rule fps_inverse_unique)
      apply (simp add: a0)
      unfolding power_mult_distrib[symmetric]
      apply (rule ssubst[where t = "a * inverse a" and s= 1])
      apply simp_all
      apply (subst mult_commute)
      by (rule inverse_mult_eq_1[OF a0])}
  ultimately show ?thesis by blast
qed

lemma fps_deriv_power: "fps_deriv (a ^ n) = fps_const (of_nat n :: 'a:: comm_ring_1) * fps_deriv a * a ^ (n - 1)"
  apply (induct n, auto simp add: power_Suc field_simps fps_const_add[symmetric] simp del: fps_const_add)
  by (case_tac n, auto simp add: power_Suc field_simps)

lemma fps_inverse_deriv:
  fixes a:: "('a :: field) fps"
  assumes a0: "a$0 \<noteq> 0"
  shows "fps_deriv (inverse a) = - fps_deriv a * inverse a ^ 2"
proof-
  from inverse_mult_eq_1[OF a0]
  have "fps_deriv (inverse a * a) = 0" by simp
  hence "inverse a * fps_deriv a + fps_deriv (inverse a) * a = 0" by simp
  hence "inverse a * (inverse a * fps_deriv a + fps_deriv (inverse a) * a) = 0"  by simp
  with inverse_mult_eq_1[OF a0]
  have "inverse a ^ 2 * fps_deriv a + fps_deriv (inverse a) = 0"
    unfolding power2_eq_square
    apply (simp add: field_simps)
    by (simp add: mult_assoc[symmetric])
  hence "inverse a ^ 2 * fps_deriv a + fps_deriv (inverse a) - fps_deriv a * inverse a ^ 2 = 0 - fps_deriv a * inverse a ^ 2"
    by simp
  then show "fps_deriv (inverse a) = - fps_deriv a * inverse a ^ 2" by (simp add: field_simps)
qed

lemma fps_inverse_mult:
  fixes a::"('a :: field) fps"
  shows "inverse (a * b) = inverse a * inverse b"
proof-
  {assume a0: "a$0 = 0" hence ab0: "(a*b)$0 = 0" by (simp add: fps_mult_nth)
    from a0 ab0 have th: "inverse a = 0" "inverse (a*b) = 0" by simp_all
    have ?thesis unfolding th by simp}
  moreover
  {assume b0: "b$0 = 0" hence ab0: "(a*b)$0 = 0" by (simp add: fps_mult_nth)
    from b0 ab0 have th: "inverse b = 0" "inverse (a*b) = 0" by simp_all
    have ?thesis unfolding th by simp}
  moreover
  {assume a0: "a$0 \<noteq> 0" and b0: "b$0 \<noteq> 0"
    from a0 b0 have ab0:"(a*b) $ 0 \<noteq> 0" by (simp  add: fps_mult_nth)
    from inverse_mult_eq_1[OF ab0]
    have "inverse (a*b) * (a*b) * inverse a * inverse b = 1 * inverse a * inverse b" by simp
    then have "inverse (a*b) * (inverse a * a) * (inverse b * b) = inverse a * inverse b"
      by (simp add: field_simps)
    then have ?thesis using inverse_mult_eq_1[OF a0] inverse_mult_eq_1[OF b0] by simp}
ultimately show ?thesis by blast
qed

lemma fps_inverse_deriv':
  fixes a:: "('a :: field) fps"
  assumes a0: "a$0 \<noteq> 0"
  shows "fps_deriv (inverse a) = - fps_deriv a / a ^ 2"
  using fps_inverse_deriv[OF a0]
  unfolding power2_eq_square fps_divide_def
    fps_inverse_mult by simp

lemma inverse_mult_eq_1': assumes f0: "f$0 \<noteq> (0::'a::field)"
  shows "f * inverse f= 1"
  by (metis mult_commute inverse_mult_eq_1 f0)

lemma fps_divide_deriv:   fixes a:: "('a :: field) fps"
  assumes a0: "b$0 \<noteq> 0"
  shows "fps_deriv (a / b) = (fps_deriv a * b - a * fps_deriv b) / b ^ 2"
  using fps_inverse_deriv[OF a0]
  by (simp add: fps_divide_def field_simps power2_eq_square fps_inverse_mult inverse_mult_eq_1'[OF a0])


lemma fps_inverse_gp': "inverse (Abs_fps(\<lambda>n. (1::'a::field)))
  = 1 - X"
  by (simp add: fps_inverse_gp fps_eq_iff X_def)

lemma fps_nth_deriv_X[simp]: "fps_nth_deriv n X = (if n = 0 then X else if n=1 then 1 else 0)"
  by (cases "n", simp_all)


lemma fps_inverse_X_plus1:
  "inverse (1 + X) = Abs_fps (\<lambda>n. (- (1::'a::{field})) ^ n)" (is "_ = ?r")
proof-
  have eq: "(1 + X) * ?r = 1"
    unfolding minus_one_power_iff
    by (auto simp add: field_simps fps_eq_iff)
  show ?thesis by (auto simp add: eq intro: fps_inverse_unique)
qed


subsection{* Integration *}

definition
  fps_integral :: "'a::field_char_0 fps \<Rightarrow> 'a \<Rightarrow> 'a fps" where
  "fps_integral a a0 = Abs_fps (\<lambda>n. if n = 0 then a0 else (a$(n - 1) / of_nat n))"

lemma fps_deriv_fps_integral: "fps_deriv (fps_integral a a0) = a"
  unfolding fps_integral_def fps_deriv_def
  by (simp add: fps_eq_iff del: of_nat_Suc)

lemma fps_integral_linear:
  "fps_integral (fps_const a * f + fps_const b * g) (a*a0 + b*b0) =
    fps_const a * fps_integral f a0 + fps_const b * fps_integral g b0"
  (is "?l = ?r")
proof-
  have "fps_deriv ?l = fps_deriv ?r" by (simp add: fps_deriv_fps_integral)
  moreover have "?l$0 = ?r$0" by (simp add: fps_integral_def)
  ultimately show ?thesis
    unfolding fps_deriv_eq_iff by auto
qed

subsection {* Composition of FPSs *}
definition fps_compose :: "('a::semiring_1) fps \<Rightarrow> 'a fps \<Rightarrow> 'a fps" (infixl "oo" 55) where
  fps_compose_def: "a oo b = Abs_fps (\<lambda>n. setsum (\<lambda>i. a$i * (b^i$n)) {0..n})"

lemma fps_compose_nth: "(a oo b)$n = setsum (\<lambda>i. a$i * (b^i$n)) {0..n}" by (simp add: fps_compose_def)

lemma fps_compose_X[simp]: "a oo X = (a :: ('a :: comm_ring_1) fps)"
  by (simp add: fps_ext fps_compose_def mult_delta_right setsum_delta')

lemma fps_const_compose[simp]:
  "fps_const (a::'a::{comm_ring_1}) oo b = fps_const (a)"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left setsum_delta)

lemma number_of_compose[simp]: "(number_of k::('a::{comm_ring_1}) fps) oo b = number_of k"
  unfolding number_of_fps_const by simp

lemma X_fps_compose_startby0[simp]: "a$0 = 0 \<Longrightarrow> X oo a = (a :: ('a :: comm_ring_1) fps)"
  by (simp add: fps_eq_iff fps_compose_def mult_delta_left setsum_delta
                power_Suc not_le)


subsection {* Rules from Herbert Wilf's Generatingfunctionology*}

subsubsection {* Rule 1 *}
  (* {a_{n+k}}_0^infty Corresponds to (f - setsum (\<lambda>i. a_i * x^i))/x^h, for h>0*)

lemma fps_power_mult_eq_shift:
  "X^Suc k * Abs_fps (\<lambda>n. a (n + Suc k)) = Abs_fps a - setsum (\<lambda>i. fps_const (a i :: 'a:: comm_ring_1) * X^i) {0 .. k}" (is "?lhs = ?rhs")
proof-
  {fix n:: nat
    have "?lhs $ n = (if n < Suc k then 0 else a n)"
      unfolding X_power_mult_nth by auto
    also have "\<dots> = ?rhs $ n"
    proof(induct k)
      case 0 thus ?case by (simp add: fps_setsum_nth power_Suc)
    next
      case (Suc k)
      note th = Suc.hyps[symmetric]
      have "(Abs_fps a - setsum (\<lambda>i. fps_const (a i :: 'a) * X^i) {0 .. Suc k})$n = (Abs_fps a - setsum (\<lambda>i. fps_const (a i :: 'a) * X^i) {0 .. k} - fps_const (a (Suc k)) * X^ Suc k) $ n" by (simp add: field_simps)
      also  have "\<dots> = (if n < Suc k then 0 else a n) - (fps_const (a (Suc k)) * X^ Suc k)$n"
        using th
        unfolding fps_sub_nth by simp
      also have "\<dots> = (if n < Suc (Suc k) then 0 else a n)"
        unfolding X_power_mult_right_nth
        apply (auto simp add: not_less fps_const_def)
        apply (rule cong[of a a, OF refl])
        by arith
      finally show ?case by simp
    qed
    finally have "?lhs $ n = ?rhs $ n"  .}
  then show ?thesis by (simp add: fps_eq_iff)
qed

subsubsection{* Rule 2*}

  (* We can not reach the form of Wilf, but still near to it using rewrite rules*)
  (* If f reprents {a_n} and P is a polynomial, then
        P(xD) f represents {P(n) a_n}*)

definition "XD = op * X o fps_deriv"

lemma XD_add[simp]:"XD (a + b) = XD a + XD (b :: ('a::comm_ring_1) fps)"
  by (simp add: XD_def field_simps)

lemma XD_mult_const[simp]:"XD (fps_const (c::'a::comm_ring_1) * a) = fps_const c * XD a"
  by (simp add: XD_def field_simps)

lemma XD_linear[simp]: "XD (fps_const c * a + fps_const d * b) = fps_const c * XD a + fps_const d * XD (b :: ('a::comm_ring_1) fps)"
  by simp

lemma XDN_linear:
  "(XD ^^ n) (fps_const c * a + fps_const d * b) = fps_const c * (XD ^^ n) a + fps_const d * (XD ^^ n) (b :: ('a::comm_ring_1) fps)"
  by (induct n, simp_all)

lemma fps_mult_X_deriv_shift: "X* fps_deriv a = Abs_fps (\<lambda>n. of_nat n* a$n)" by (simp add: fps_eq_iff)


lemma fps_mult_XD_shift:
  "(XD ^^ k) (a:: ('a::{comm_ring_1}) fps) = Abs_fps (\<lambda>n. (of_nat n ^ k) * a$n)"
  by (induct k arbitrary: a) (simp_all add: power_Suc XD_def fps_eq_iff field_simps del: One_nat_def)

subsubsection{* Rule 3 is trivial and is given by @{text fps_times_def}*}
subsubsection{* Rule 5 --- summation and "division" by (1 - X)*}

lemma fps_divide_X_minus1_setsum_lemma:
  "a = ((1::('a::comm_ring_1) fps) - X) * Abs_fps (\<lambda>n. setsum (\<lambda>i. a $ i) {0..n})"
proof-
  let ?X = "X::('a::comm_ring_1) fps"
  let ?sa = "Abs_fps (\<lambda>n. setsum (\<lambda>i. a $ i) {0..n})"
  have th0: "\<And>i. (1 - (X::'a fps)) $ i = (if i = 0 then 1 else if i = 1 then - 1 else 0)" by simp
  {fix n:: nat
    {assume "n=0" hence "a$n = ((1 - ?X) * ?sa) $ n"
        by (simp add: fps_mult_nth)}
    moreover
    {assume n0: "n \<noteq> 0"
      then have u: "{0} \<union> ({1} \<union> {2..n}) = {0..n}" "{1}\<union>{2..n} = {1..n}"
        "{0..n - 1}\<union>{n} = {0..n}"
        by (auto simp: set_eq_iff)
      have d: "{0} \<inter> ({1} \<union> {2..n}) = {}" "{1} \<inter> {2..n} = {}"
        "{0..n - 1}\<inter>{n} ={}" using n0 by simp_all
      have f: "finite {0}" "finite {1}" "finite {2 .. n}"
        "finite {0 .. n - 1}" "finite {n}" by simp_all
    have "((1 - ?X) * ?sa) $ n = setsum (\<lambda>i. (1 - ?X)$ i * ?sa $ (n - i)) {0 .. n}"
      by (simp add: fps_mult_nth)
    also have "\<dots> = a$n" unfolding th0
      unfolding setsum_Un_disjoint[OF f(1) finite_UnI[OF f(2,3)] d(1), unfolded u(1)]
      unfolding setsum_Un_disjoint[OF f(2) f(3) d(2)]
      apply (simp)
      unfolding setsum_Un_disjoint[OF f(4,5) d(3), unfolded u(3)]
      by simp
    finally have "a$n = ((1 - ?X) * ?sa) $ n" by simp}
  ultimately have "a$n = ((1 - ?X) * ?sa) $ n" by blast}
then show ?thesis
  unfolding fps_eq_iff by blast
qed

lemma fps_divide_X_minus1_setsum:
  "a /((1::('a::field) fps) - X)  = Abs_fps (\<lambda>n. setsum (\<lambda>i. a $ i) {0..n})"
proof-
  let ?X = "1 - (X::('a::field) fps)"
  have th0: "?X $ 0 \<noteq> 0" by simp
  have "a /?X = ?X *  Abs_fps (\<lambda>n\<Colon>nat. setsum (op $ a) {0..n}) * inverse ?X"
    using fps_divide_X_minus1_setsum_lemma[of a, symmetric] th0
    by (simp add: fps_divide_def mult_assoc)
  also have "\<dots> = (inverse ?X * ?X) * Abs_fps (\<lambda>n\<Colon>nat. setsum (op $ a) {0..n}) "
    by (simp add: mult_ac)
  finally show ?thesis by (simp add: inverse_mult_eq_1[OF th0])
qed

subsubsection{* Rule 4 in its more general form: generalizes Rule 3 for an arbitrary
  finite product of FPS, also the relvant instance of powers of a FPS*}

definition "natpermute n k = {l :: nat list. length l = k \<and> listsum l = n}"

lemma natlist_trivial_1: "natpermute n 1 = {[n]}"
  apply (auto simp add: natpermute_def)
  apply (case_tac x, auto)
  done

lemma append_natpermute_less_eq:
  assumes h: "xs@ys \<in> natpermute n k" shows "listsum xs \<le> n" and "listsum ys \<le> n"
proof-
  {from h have "listsum (xs @ ys) = n" by (simp add: natpermute_def)
    hence "listsum xs + listsum ys = n" by simp}
  note th = this
  {from th show "listsum xs \<le> n" by simp}
  {from th show "listsum ys \<le> n" by simp}
qed

lemma natpermute_split:
  assumes mn: "h \<le> k"
  shows "natpermute n k = (\<Union>m \<in>{0..n}. {l1 @ l2 |l1 l2. l1 \<in> natpermute m h \<and> l2 \<in> natpermute (n - m) (k - h)})" (is "?L = ?R" is "?L = (\<Union>m \<in>{0..n}. ?S m)")
proof-
  {fix l assume l: "l \<in> ?R"
    from l obtain m xs ys where h: "m \<in> {0..n}" and xs: "xs \<in> natpermute m h" and ys: "ys \<in> natpermute (n - m) (k - h)"  and leq: "l = xs@ys" by blast
    from xs have xs': "listsum xs = m" by (simp add: natpermute_def)
    from ys have ys': "listsum ys = n - m" by (simp add: natpermute_def)
    have "l \<in> ?L" using leq xs ys h
      apply (clarsimp simp add: natpermute_def)
      unfolding xs' ys'
      using mn xs ys
      unfolding natpermute_def by simp}
  moreover
  {fix l assume l: "l \<in> natpermute n k"
    let ?xs = "take h l"
    let ?ys = "drop h l"
    let ?m = "listsum ?xs"
    from l have ls: "listsum (?xs @ ?ys) = n" by (simp add: natpermute_def)
    have xs: "?xs \<in> natpermute ?m h" using l mn by (simp add: natpermute_def)
    have l_take_drop: "listsum l = listsum (take h l @ drop h l)" by simp
    then have ys: "?ys \<in> natpermute (n - ?m) (k - h)" using l mn ls
      by (auto simp add: natpermute_def simp del: append_take_drop_id)
    from ls have m: "?m \<in> {0..n}" by (simp add: l_take_drop del: append_take_drop_id)
    from xs ys ls have "l \<in> ?R"
      apply auto
      apply (rule bexI[where x = "?m"])
      apply (rule exI[where x = "?xs"])
      apply (rule exI[where x = "?ys"])
      using ls l 
      apply (auto simp add: natpermute_def l_take_drop simp del: append_take_drop_id)
      by simp}
  ultimately show ?thesis by blast
qed

lemma natpermute_0: "natpermute n 0 = (if n = 0 then {[]} else {})"
  by (auto simp add: natpermute_def)
lemma natpermute_0'[simp]: "natpermute 0 k = (if k = 0 then {[]} else {replicate k 0})"
  apply (auto simp add: set_replicate_conv_if natpermute_def)
  apply (rule nth_equalityI)
  by simp_all

lemma natpermute_finite: "finite (natpermute n k)"
proof(induct k arbitrary: n)
  case 0 thus ?case
    apply (subst natpermute_split[of 0 0, simplified])
    by (simp add: natpermute_0)
next
  case (Suc k)
  then show ?case unfolding natpermute_split[of k "Suc k", simplified]
    apply -
    apply (rule finite_UN_I)
    apply simp
    unfolding One_nat_def[symmetric] natlist_trivial_1
    apply simp
    done
qed

lemma natpermute_contain_maximal:
  "{xs \<in> natpermute n (k+1). n \<in> set xs} = UNION {0 .. k} (\<lambda>i. {(replicate (k+1) 0) [i:=n]})"
  (is "?A = ?B")
proof-
  {fix xs assume H: "xs \<in> natpermute n (k+1)" and n: "n \<in> set xs"
    from n obtain i where i: "i \<in> {0.. k}" "xs!i = n" using H
      unfolding in_set_conv_nth by (auto simp add: less_Suc_eq_le natpermute_def)
    have eqs: "({0..k} - {i}) \<union> {i} = {0..k}" using i by auto
    have f: "finite({0..k} - {i})" "finite {i}" by auto
    have d: "({0..k} - {i}) \<inter> {i} = {}" using i by auto
    from H have "n = setsum (nth xs) {0..k}" apply (simp add: natpermute_def)
      by (auto simp add: atLeastLessThanSuc_atLeastAtMost listsum_setsum_nth)
    also have "\<dots> = n + setsum (nth xs) ({0..k} - {i})"
      unfolding setsum_Un_disjoint[OF f d, unfolded eqs] using i by simp
    finally have zxs: "\<forall> j\<in> {0..k} - {i}. xs!j = 0" by auto
    from H have xsl: "length xs = k+1" by (simp add: natpermute_def)
    from i have i': "i < length (replicate (k+1) 0)"   "i < k+1"
      unfolding length_replicate  by arith+
    have "xs = replicate (k+1) 0 [i := n]"
      apply (rule nth_equalityI)
      unfolding xsl length_list_update length_replicate
      apply simp
      apply clarify
      unfolding nth_list_update[OF i'(1)]
      using i zxs
      by (case_tac "ia=i", auto simp del: replicate.simps)
    then have "xs \<in> ?B" using i by blast}
  moreover
  {fix i assume i: "i \<in> {0..k}"
    let ?xs = "replicate (k+1) 0 [i:=n]"
    have nxs: "n \<in> set ?xs"
      apply (rule set_update_memI) using i by simp
    have xsl: "length ?xs = k+1" by (simp only: length_replicate length_list_update)
    have "listsum ?xs = setsum (nth ?xs) {0..<k+1}"
      unfolding listsum_setsum_nth xsl ..
    also have "\<dots> = setsum (\<lambda>j. if j = i then n else 0) {0..< k+1}"
      apply (rule setsum_cong2) by (simp del: replicate.simps)
    also have "\<dots> = n" using i by (simp add: setsum_delta)
    finally
    have "?xs \<in> natpermute n (k+1)" using xsl unfolding natpermute_def mem_Collect_eq
      by blast
    then have "?xs \<in> ?A"  using nxs  by blast}
  ultimately show ?thesis by auto
qed

    (* The general form *)
lemma fps_setprod_nth:
  fixes m :: nat and a :: "nat \<Rightarrow> ('a::comm_ring_1) fps"
  shows "(setprod a {0 .. m})$n = setsum (\<lambda>v. setprod (\<lambda>j. (a j) $ (v!j)) {0..m}) (natpermute n (m+1))"
  (is "?P m n")
proof(induct m arbitrary: n rule: nat_less_induct)
  fix m n assume H: "\<forall>m' < m. \<forall>n. ?P m' n"
  {assume m0: "m = 0"
    hence "?P m n" apply simp
      unfolding natlist_trivial_1[where n = n, unfolded One_nat_def] by simp}
  moreover
  {fix k assume k: "m = Suc k"
    have km: "k < m" using k by arith
    have u0: "{0 .. k} \<union> {m} = {0..m}" using k apply (simp add: set_eq_iff) by presburger
    have f0: "finite {0 .. k}" "finite {m}" by auto
    have d0: "{0 .. k} \<inter> {m} = {}" using k by auto
    have "(setprod a {0 .. m}) $ n = (setprod a {0 .. k} * a m) $ n"
      unfolding setprod_Un_disjoint[OF f0 d0, unfolded u0] by simp
    also have "\<dots> = (\<Sum>i = 0..n. (\<Sum>v\<in>natpermute i (k + 1). \<Prod>j\<in>{0..k}. a j $ v ! j) * a m $ (n - i))"
      unfolding fps_mult_nth H[rule_format, OF km] ..
    also have "\<dots> = (\<Sum>v\<in>natpermute n (m + 1). \<Prod>j\<in>{0..m}. a j $ v ! j)"
      apply (simp add: k)
      unfolding natpermute_split[of m "m + 1", simplified, of n, unfolded natlist_trivial_1[unfolded One_nat_def] k]
      apply (subst setsum_UN_disjoint)
      apply simp
      apply simp
      unfolding image_Collect[symmetric]
      apply clarsimp
      apply (rule finite_imageI)
      apply (rule natpermute_finite)
      apply (clarsimp simp add: set_eq_iff)
      apply auto
      apply (rule setsum_cong2)
      unfolding setsum_left_distrib
      apply (rule sym)
      apply (rule_tac f="\<lambda>xs. xs @[n - x]" in  setsum_reindex_cong)
      apply (simp add: inj_on_def)
      apply auto
      unfolding setprod_Un_disjoint[OF f0 d0, unfolded u0, unfolded k]
      apply (clarsimp simp add: natpermute_def nth_append)
      done
    finally have "?P m n" .}
  ultimately show "?P m n " by (cases m, auto)
qed

text{* The special form for powers *}
lemma fps_power_nth_Suc:
  fixes m :: nat and a :: "('a::comm_ring_1) fps"
  shows "(a ^ Suc m)$n = setsum (\<lambda>v. setprod (\<lambda>j. a $ (v!j)) {0..m}) (natpermute n (m+1))"
proof-
  have f: "finite {0 ..m}" by simp
  have th0: "a^Suc m = setprod (\<lambda>i. a) {0..m}" unfolding setprod_constant[OF f, of a] by simp
  show ?thesis unfolding th0 fps_setprod_nth ..
qed
lemma fps_power_nth:
  fixes m :: nat and a :: "('a::comm_ring_1) fps"
  shows "(a ^m)$n = (if m=0 then 1$n else setsum (\<lambda>v. setprod (\<lambda>j. a $ (v!j)) {0..m - 1}) (natpermute n m))"
  by (cases m, simp_all add: fps_power_nth_Suc del: power_Suc)

lemma fps_nth_power_0:
  fixes m :: nat and a :: "('a::{comm_ring_1}) fps"
  shows "(a ^m)$0 = (a$0) ^ m"
proof-
  {assume "m=0" hence ?thesis by simp}
  moreover
  {fix n assume m: "m = Suc n"
    have c: "m = card {0..n}" using m by simp
   have "(a ^m)$0 = setprod (\<lambda>i. a$0) {0..n}"
     by (simp add: m fps_power_nth del: replicate.simps power_Suc)
   also have "\<dots> = (a$0) ^ m"
     unfolding c by (rule setprod_constant, simp)
   finally have ?thesis .}
 ultimately show ?thesis by (cases m, auto)
qed

lemma fps_compose_inj_right:
  assumes a0: "a$0 = (0::'a::{idom})"
  and a1: "a$1 \<noteq> 0"
  shows "(b oo a = c oo a) \<longleftrightarrow> b = c" (is "?lhs \<longleftrightarrow>?rhs")
proof-
  {assume ?rhs then have "?lhs" by simp}
  moreover
  {assume h: ?lhs
    {fix n have "b$n = c$n"
      proof(induct n rule: nat_less_induct)
        fix n assume H: "\<forall>m<n. b$m = c$m"
        {assume n0: "n=0"
          from h have "(b oo a)$n = (c oo a)$n" by simp
          hence "b$n = c$n" using n0 by (simp add: fps_compose_nth)}
        moreover
        {fix n1 assume n1: "n = Suc n1"
          have f: "finite {0 .. n1}" "finite {n}" by simp_all
          have eq: "{0 .. n1} \<union> {n} = {0 .. n}" using n1 by auto
          have d: "{0 .. n1} \<inter> {n} = {}" using n1 by auto
          have seq: "(\<Sum>i = 0..n1. b $ i * a ^ i $ n) = (\<Sum>i = 0..n1. c $ i * a ^ i $ n)"
            apply (rule setsum_cong2)
            using H n1 by auto
          have th0: "(b oo a) $n = (\<Sum>i = 0..n1. c $ i * a ^ i $ n) + b$n * (a$1)^n"
            unfolding fps_compose_nth setsum_Un_disjoint[OF f d, unfolded eq] seq
            using startsby_zero_power_nth_same[OF a0]
            by simp
          have th1: "(c oo a) $n = (\<Sum>i = 0..n1. c $ i * a ^ i $ n) + c$n * (a$1)^n"
            unfolding fps_compose_nth setsum_Un_disjoint[OF f d, unfolded eq]
            using startsby_zero_power_nth_same[OF a0]
            by simp
          from h[unfolded fps_eq_iff, rule_format, of n] th0 th1 a1
          have "b$n = c$n" by auto}
        ultimately show "b$n = c$n" by (cases n, auto)
      qed}
    then have ?rhs by (simp add: fps_eq_iff)}
  ultimately show ?thesis by blast
qed


subsection {* Radicals *}

declare setprod_cong[fundef_cong]
function radical :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a::{field}) fps \<Rightarrow> nat \<Rightarrow> 'a" where
  "radical r 0 a 0 = 1"
| "radical r 0 a (Suc n) = 0"
| "radical r (Suc k) a 0 = r (Suc k) (a$0)"
| "radical r (Suc k) a (Suc n) = (a$ Suc n - setsum (\<lambda>xs. setprod (\<lambda>j. radical r (Suc k) a (xs ! j)) {0..k}) {xs. xs \<in> natpermute (Suc n) (Suc k) \<and> Suc n \<notin> set xs}) / (of_nat (Suc k) * (radical r (Suc k) a 0)^k)"
by pat_completeness auto

termination radical
proof
  let ?R = "measure (\<lambda>(r, k, a, n). n)"
  {
    show "wf ?R" by auto}
  {fix r k a n xs i
    assume xs: "xs \<in> {xs \<in> natpermute (Suc n) (Suc k). Suc n \<notin> set xs}" and i: "i \<in> {0..k}"
    {assume c: "Suc n \<le> xs ! i"
      from xs i have "xs !i \<noteq> Suc n" by (auto simp add: in_set_conv_nth natpermute_def)
      with c have c': "Suc n < xs!i" by arith
      have fths: "finite {0 ..< i}" "finite {i}" "finite {i+1..<Suc k}" by simp_all
      have d: "{0 ..< i} \<inter> ({i} \<union> {i+1 ..< Suc k}) = {}" "{i} \<inter> {i+1..< Suc k} = {}" by auto
      have eqs: "{0..<Suc k} = {0 ..< i} \<union> ({i} \<union> {i+1 ..< Suc k})" using i by auto
      from xs have "Suc n = listsum xs" by (simp add: natpermute_def)
      also have "\<dots> = setsum (nth xs) {0..<Suc k}" using xs
        by (simp add: natpermute_def listsum_setsum_nth)
      also have "\<dots> = xs!i + setsum (nth xs) {0..<i} + setsum (nth xs) {i+1..<Suc k}"
        unfolding eqs  setsum_Un_disjoint[OF fths(1) finite_UnI[OF fths(2,3)] d(1)]
        unfolding setsum_Un_disjoint[OF fths(2) fths(3) d(2)]
        by simp
      finally have False using c' by simp}
    then show "((r,Suc k,a,xs!i), r, Suc k, a, Suc n) \<in> ?R"
      apply auto by (metis not_less)}
  {fix r k a n
    show "((r,Suc k, a, 0),r, Suc k, a, Suc n) \<in> ?R" by simp}
qed

definition "fps_radical r n a = Abs_fps (radical r n a)"

lemma fps_radical0[simp]: "fps_radical r 0 a = 1"
  apply (auto simp add: fps_eq_iff fps_radical_def)  by (case_tac n, auto)

lemma fps_radical_nth_0[simp]: "fps_radical r n a $ 0 = (if n=0 then 1 else r n (a$0))"
  by (cases n, simp_all add: fps_radical_def)

lemma fps_radical_power_nth[simp]:
  assumes r: "(r k (a$0)) ^ k = a$0"
  shows "fps_radical r k a ^ k $ 0 = (if k = 0 then 1 else a$0)"
proof-
  {assume "k=0" hence ?thesis by simp }
  moreover
  {fix h assume h: "k = Suc h"
    have fh: "finite {0..h}" by simp
    have eq1: "fps_radical r k a ^ k $ 0 = (\<Prod>j\<in>{0..h}. fps_radical r k a $ (replicate k 0) ! j)"
      unfolding fps_power_nth h by simp
    also have "\<dots> = (\<Prod>j\<in>{0..h}. r k (a$0))"
      apply (rule setprod_cong)
      apply simp
      using h
      apply (subgoal_tac "replicate k (0::nat) ! x = 0")
      by (auto intro: nth_replicate simp del: replicate.simps)
    also have "\<dots> = a$0"
      unfolding setprod_constant[OF fh] using r by (simp add: h)
    finally have ?thesis using h by simp}
  ultimately show ?thesis by (cases k, auto)
qed

lemma natpermute_max_card: assumes n0: "n\<noteq>0"
  shows "card {xs \<in> natpermute n (k+1). n \<in> set xs} = k+1"
  unfolding natpermute_contain_maximal
proof-
  let ?A= "\<lambda>i. {replicate (k + 1) 0[i := n]}"
  let ?K = "{0 ..k}"
  have fK: "finite ?K" by simp
  have fAK: "\<forall>i\<in>?K. finite (?A i)" by auto
  have d: "\<forall>i\<in> ?K. \<forall>j\<in> ?K. i \<noteq> j \<longrightarrow> {replicate (k + 1) 0[i := n]} \<inter> {replicate (k + 1) 0[j := n]} = {}"
  proof(clarify)
    fix i j assume i: "i \<in> ?K" and j: "j\<in> ?K" and ij: "i\<noteq>j"
    {assume eq: "replicate (k+1) 0 [i:=n] = replicate (k+1) 0 [j:= n]"
      have "(replicate (k+1) 0 [i:=n] ! i) = n" using i by (simp del: replicate.simps)
      moreover
      have "(replicate (k+1) 0 [j:=n] ! i) = 0" using i ij by (simp del: replicate.simps)
      ultimately have False using eq n0 by (simp del: replicate.simps)}
    then show "{replicate (k + 1) 0[i := n]} \<inter> {replicate (k + 1) 0[j := n]} = {}"
      by auto
  qed
  from card_UN_disjoint[OF fK fAK d]
  show "card (\<Union>i\<in>{0..k}. {replicate (k + 1) 0[i := n]}) = k+1" by simp
qed

lemma power_radical:
  fixes a:: "'a::field_char_0 fps"
  assumes a0: "a$0 \<noteq> 0"
  shows "(r (Suc k) (a$0)) ^ Suc k = a$0 \<longleftrightarrow> (fps_radical r (Suc k) a) ^ (Suc k) = a"
proof-
  let ?r = "fps_radical r (Suc k) a"
  {assume r0: "(r (Suc k) (a$0)) ^ Suc k = a$0"
    from a0 r0 have r00: "r (Suc k) (a$0) \<noteq> 0" by auto
    {fix z have "?r ^ Suc k $ z = a$z"
      proof(induct z rule: nat_less_induct)
        fix n assume H: "\<forall>m<n. ?r ^ Suc k $ m = a$m"
        {assume "n = 0" hence "?r ^ Suc k $ n = a $n"
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
          have "setsum ?f ?Pnkn = setsum (\<lambda>v. ?r $ n * r (Suc k) (a $ 0) ^ k) ?Pnkn"
          proof(rule setsum_cong2)
            fix v assume v: "v \<in> {xs \<in> natpermute n (k + 1). n \<in> set xs}"
            let ?ths = "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = fps_radical r (Suc k) a $ n * r (Suc k) (a $ 0) ^ k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding natpermute_contain_maximal by auto
          have "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then fps_radical r (Suc k) a $ n else r (Suc k) (a$0))"
            apply (rule setprod_cong, simp)
            using i r0 by (simp del: replicate.simps)
          also have "\<dots> = (fps_radical r (Suc k) a $ n) * r (Suc k) (a$0) ^ k"
            unfolding setprod_gen_delta[OF fK] using i r0 by simp
          finally show ?ths .
        qed
        then have "setsum ?f ?Pnkn = of_nat (k+1) * ?r $ n * r (Suc k) (a $ 0) ^ k"
          by (simp add: natpermute_max_card[OF nz, simplified])
        also have "\<dots> = a$n - setsum ?f ?Pnknn"
          unfolding n1 using r00 a0 by (simp add: field_simps fps_radical_def del: of_nat_Suc)
        finally have fn: "setsum ?f ?Pnkn = a$n - setsum ?f ?Pnknn" .
        have "(?r ^ Suc k)$n = setsum ?f ?Pnkn + setsum ?f ?Pnknn"
          unfolding fps_power_nth_Suc setsum_Un_disjoint[OF f d, unfolded eq] ..
        also have "\<dots> = a$n" unfolding fn by simp
        finally have "?r ^ Suc k $ n = a $n" .}
      ultimately  show "?r ^ Suc k $ n = a $n" by (cases n, auto)
    qed }
  then have ?thesis using r0 by (simp add: fps_eq_iff)}
moreover 
{ assume h: "(fps_radical r (Suc k) a) ^ (Suc k) = a"
  hence "((fps_radical r (Suc k) a) ^ (Suc k))$0 = a$0" by simp
  then have "(r (Suc k) (a$0)) ^ Suc k = a$0"
    unfolding fps_power_nth_Suc
    by (simp add: setprod_constant del: replicate.simps)}
ultimately show ?thesis by blast
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
      {assume "n = 0" hence "?r ^ Suc k $ n = a $n"
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
        have "setsum ?f ?Pnkn = setsum (\<lambda>v. ?r $ n * r (Suc k) (a $ 0) ^ k) ?Pnkn"
        proof(rule setsum_cong2)
          fix v assume v: "v \<in> {xs \<in> natpermute n (k + 1). n \<in> set xs}"
          let ?ths = "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = fps_radical r (Suc k) a $ n * r (Suc k) (a $ 0) ^ k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding natpermute_contain_maximal by auto
          have "(\<Prod>j\<in>{0..k}. fps_radical r (Suc k) a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then fps_radical r (Suc k) a $ n else r (Suc k) (a$0))"
            apply (rule setprod_cong, simp)
            using i r0 by (simp del: replicate.simps)
          also have "\<dots> = (fps_radical r (Suc k) a $ n) * r (Suc k) (a$0) ^ k"
            unfolding setprod_gen_delta[OF fK] using i r0 by simp
          finally show ?ths .
        qed
        then have "setsum ?f ?Pnkn = of_nat (k+1) * ?r $ n * r (Suc k) (a $ 0) ^ k"
          by (simp add: natpermute_max_card[OF nz, simplified])
        also have "\<dots> = a$n - setsum ?f ?Pnknn"
          unfolding n1 using r00 a0 by (simp add: field_simps fps_radical_def del: of_nat_Suc )
        finally have fn: "setsum ?f ?Pnkn = a$n - setsum ?f ?Pnknn" .
        have "(?r ^ Suc k)$n = setsum ?f ?Pnkn + setsum ?f ?Pnknn"
          unfolding fps_power_nth_Suc setsum_Un_disjoint[OF f d, unfolded eq] ..
        also have "\<dots> = a$n" unfolding fn by simp
        finally have "?r ^ Suc k $ n = a $n" .}
      ultimately  show "?r ^ Suc k $ n = a $n" by (cases n, auto)
  qed }
  then show ?thesis by (simp add: fps_eq_iff)
qed

*)
lemma eq_divide_imp': assumes c0: "(c::'a::field) ~= 0" and eq: "a * c = b"
  shows "a = b / c"
proof-
  from eq have "a * c * inverse c = b * inverse c" by simp
  hence "a * (inverse c * c) = b/c" by (simp only: field_simps divide_inverse)
  then show "a = b/c" unfolding  field_inverse[OF c0] by simp
qed

lemma radical_unique:
  assumes r0: "(r (Suc k) (b$0)) ^ Suc k = b$0"
  and a0: "r (Suc k) (b$0 ::'a::field_char_0) = a$0" and b0: "b$0 \<noteq> 0"
  shows "a^(Suc k) = b \<longleftrightarrow> a = fps_radical r (Suc k) b"
proof-
  let ?r = "fps_radical r (Suc k) b"
  have r00: "r (Suc k) (b$0) \<noteq> 0" using b0 r0 by auto
  {assume H: "a = ?r"
    from H have "a^Suc k = b" using power_radical[OF b0, of r k, unfolded r0] by simp}
  moreover
  {assume H: "a^Suc k = b"
    have ceq: "card {0..k} = Suc k" by simp
    have fk: "finite {0..k}" by simp
    from a0 have a0r0: "a$0 = ?r$0" by simp
    {fix n have "a $ n = ?r $ n"
      proof(induct n rule: nat_less_induct)
        fix n assume h: "\<forall>m<n. a$m = ?r $m"
        {assume "n = 0" hence "a$n = ?r $n" using a0 by simp }
        moreover
        {fix n1 assume n1: "n = Suc n1"
          have fK: "finite {0..k}" by simp
        have nz: "n \<noteq> 0" using n1 by arith
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
        have "setsum ?g ?Pnkn = setsum (\<lambda>v. a $ n * (?r$0)^k) ?Pnkn"
        proof(rule setsum_cong2)
          fix v assume v: "v \<in> {xs \<in> natpermute n (Suc k). n \<in> set xs}"
          let ?ths = "(\<Prod>j\<in>{0..k}. a $ v ! j) = a $ n * (?r$0)^k"
          from v obtain i where i: "i \<in> {0..k}" "v = replicate (k+1) 0 [i:= n]"
            unfolding Suc_eq_plus1 natpermute_contain_maximal by (auto simp del: replicate.simps)
          have "(\<Prod>j\<in>{0..k}. a $ v ! j) = (\<Prod>j\<in>{0..k}. if j = i then a $ n else r (Suc k) (b$0))"
            apply (rule setprod_cong, simp)
            using i a0 by (simp del: replicate.simps)
          also have "\<dots> = a $ n * (?r $ 0)^k"
            unfolding  setprod_gen_delta[OF fK] using i by simp
          finally show ?ths .
        qed
        then have th0: "setsum ?g ?Pnkn = of_nat (k+1) * a $ n * (?r $ 0)^k"
          by (simp add: natpermute_max_card[OF nz, simplified])
        have th1: "setsum ?g ?Pnknn = setsum ?f ?Pnknn"
        proof (rule setsum_cong2, rule setprod_cong, simp)
          fix xs i assume xs: "xs \<in> ?Pnknn" and i: "i \<in> {0..k}"
          {assume c: "n \<le> xs ! i"
            from xs i have "xs !i \<noteq> n" by (auto simp add: in_set_conv_nth natpermute_def)
            with c have c': "n < xs!i" by arith
            have fths: "finite {0 ..< i}" "finite {i}" "finite {i+1..<Suc k}" by simp_all
            have d: "{0 ..< i} \<inter> ({i} \<union> {i+1 ..< Suc k}) = {}" "{i} \<inter> {i+1..< Suc k} = {}" by auto
            have eqs: "{0..<Suc k} = {0 ..< i} \<union> ({i} \<union> {i+1 ..< Suc k})" using i by auto
            from xs have "n = listsum xs" by (simp add: natpermute_def)
            also have "\<dots> = setsum (nth xs) {0..<Suc k}" using xs
              by (simp add: natpermute_def listsum_setsum_nth)
            also have "\<dots> = xs!i + setsum (nth xs) {0..<i} + setsum (nth xs) {i+1..<Suc k}"
              unfolding eqs  setsum_Un_disjoint[OF fths(1) finite_UnI[OF fths(2,3)] d(1)]
              unfolding setsum_Un_disjoint[OF fths(2) fths(3) d(2)]
              by simp
            finally have False using c' by simp}
          then have thn: "xs!i < n" by arith
          from h[rule_format, OF thn]
          show "a$(xs !i) = ?r$(xs!i)" .
        qed
        have th00: "\<And>(x::'a). of_nat (Suc k) * (x * inverse (of_nat (Suc k))) = x"
          by (simp add: field_simps del: of_nat_Suc)
        from H have "b$n = a^Suc k $ n" by (simp add: fps_eq_iff)
        also have "a ^ Suc k$n = setsum ?g ?Pnkn + setsum ?g ?Pnknn"
          unfolding fps_power_nth_Suc
          using setsum_Un_disjoint[OF f d, unfolded Suc_eq_plus1[symmetric],
            unfolded eq, of ?g] by simp
        also have "\<dots> = of_nat (k+1) * a $ n * (?r $ 0)^k + setsum ?f ?Pnknn" unfolding th0 th1 ..
        finally have "of_nat (k+1) * a $ n * (?r $ 0)^k = b$n - setsum ?f ?Pnknn" by simp
        then have "a$n = (b$n - setsum ?f ?Pnknn) / (of_nat (k+1) * (?r $ 0)^k)"
          apply -
          apply (rule eq_divide_imp')
          using r00
          apply (simp del: of_nat_Suc)
          by (simp add: mult_ac)
        then have "a$n = ?r $n"
          apply (simp del: of_nat_Suc)
          unfolding fps_radical_def n1
          by (simp add: field_simps n1 th00 del: of_nat_Suc)}
        ultimately show "a$n = ?r $ n" by (cases n, auto)
      qed}
    then have "a = ?r" by (simp add: fps_eq_iff)}
  ultimately show ?thesis by blast
qed


lemma radical_power:
  assumes r0: "r (Suc k) ((a$0) ^ Suc k) = a$0"
  and a0: "(a$0 ::'a::field_char_0) \<noteq> 0"
  shows "(fps_radical r (Suc k) (a ^ Suc k)) = a"
proof-
  let ?ak = "a^ Suc k"
  have ak0: "?ak $ 0 = (a$0) ^ Suc k" by (simp add: fps_nth_power_0 del: power_Suc)
  from r0 have th0: "r (Suc k) (a ^ Suc k $ 0) ^ Suc k = a ^ Suc k $ 0" using ak0 by auto
  from r0 ak0 have th1: "r (Suc k) (a ^ Suc k $ 0) = a $ 0" by auto
  from ak0 a0 have ak00: "?ak $ 0 \<noteq>0 " by auto
  from radical_unique[of r k ?ak a, OF th0 th1 ak00] show ?thesis by metis
qed

lemma fps_deriv_radical:
  fixes a:: "'a::field_char_0 fps"
  assumes r0: "(r (Suc k) (a$0)) ^ Suc k = a$0" and a0: "a$0 \<noteq> 0"
  shows "fps_deriv (fps_radical r (Suc k) a) = fps_deriv a / (fps_const (of_nat (Suc k)) * (fps_radical r (Suc k) a) ^ k)"
proof-
  let ?r= "fps_radical r (Suc k) a"
  let ?w = "(fps_const (of_nat (Suc k)) * ?r ^ k)"
  from a0 r0 have r0': "r (Suc k) (a$0) \<noteq> 0" by auto
  from r0' have w0: "?w $ 0 \<noteq> 0" by (simp del: of_nat_Suc)
  note th0 = inverse_mult_eq_1[OF w0]
  let ?iw = "inverse ?w"
  from iffD1[OF power_radical[of a r], OF a0 r0]
  have "fps_deriv (?r ^ Suc k) = fps_deriv a" by simp
  hence "fps_deriv ?r * ?w = fps_deriv a"
    by (simp add: fps_deriv_power mult_ac del: power_Suc)
  hence "?iw * fps_deriv ?r * ?w = ?iw * fps_deriv a" by simp
  hence "fps_deriv ?r * (?iw * ?w) = fps_deriv a / ?w"
    by (simp add: fps_divide_def)
  then show ?thesis unfolding th0 by simp
qed

lemma radical_mult_distrib:
  fixes a:: "'a::field_char_0 fps"
  assumes
  k: "k > 0"
  and ra0: "r k (a $ 0) ^ k = a $ 0"
  and rb0: "r k (b $ 0) ^ k = b $ 0"
  and a0: "a$0 \<noteq> 0"
  and b0: "b$0 \<noteq> 0"
  shows "r k ((a * b) $ 0) = r k (a $ 0) * r k (b $ 0) \<longleftrightarrow> fps_radical r (k) (a*b) = fps_radical r (k) a * fps_radical r (k) (b)"
proof-
  {assume  r0': "r k ((a * b) $ 0) = r k (a $ 0) * r k (b $ 0)"
  from r0' have r0: "(r (k) ((a*b)$0)) ^ k = (a*b)$0"
    by (simp add: fps_mult_nth ra0 rb0 power_mult_distrib)
  {assume "k=0" hence ?thesis using r0' by simp}
  moreover
  {fix h assume k: "k = Suc h"
  let ?ra = "fps_radical r (Suc h) a"
  let ?rb = "fps_radical r (Suc h) b"
  have th0: "r (Suc h) ((a * b) $ 0) = (fps_radical r (Suc h) a * fps_radical r (Suc h) b) $ 0"
    using r0' k by (simp add: fps_mult_nth)
  have ab0: "(a*b) $ 0 \<noteq> 0" using a0 b0 by (simp add: fps_mult_nth)
  from radical_unique[of r h "a*b" "fps_radical r (Suc h) a * fps_radical r (Suc h) b", OF r0[unfolded k] th0 ab0, symmetric]
    iffD1[OF power_radical[of _ r], OF a0 ra0[unfolded k]] iffD1[OF power_radical[of _ r], OF b0 rb0[unfolded k]] k r0'
  have ?thesis by (auto simp add: power_mult_distrib simp del: power_Suc)}
ultimately have ?thesis by (cases k, auto)}
moreover
{assume h: "fps_radical r k (a*b) = fps_radical r k a * fps_radical r k b"
  hence "(fps_radical r k (a*b))$0 = (fps_radical r k a * fps_radical r k b)$0" by simp
  then have "r k ((a * b) $ 0) = r k (a $ 0) * r k (b $ 0)"
    using k by (simp add: fps_mult_nth)}
ultimately show ?thesis by blast
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
  {assume "k=0" hence ?thesis by simp}
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

lemma fps_divide_1[simp]: "(a:: ('a::field) fps) / 1 = a"
  by (simp add: fps_divide_def)

lemma radical_divide:
  fixes a :: "'a::field_char_0 fps"
  assumes
  kp: "k>0"
  and ra0: "(r k (a $ 0)) ^ k = a $ 0"
  and rb0: "(r k (b $ 0)) ^ k = b $ 0"
  and a0: "a$0 \<noteq> 0"
  and b0: "b$0 \<noteq> 0"
  shows "r k ((a $ 0) / (b$0)) = r k (a$0) / r k (b $ 0) \<longleftrightarrow> fps_radical r k (a/b) = fps_radical r k a / fps_radical r k b" (is "?lhs = ?rhs")
proof-
  let ?r = "fps_radical r k"
  from kp obtain h where k: "k = Suc h" by (cases k, auto)
  have ra0': "r k (a$0) \<noteq> 0" using a0 ra0 k by auto
  have rb0': "r k (b$0) \<noteq> 0" using b0 rb0 k by auto

  {assume ?rhs
    then have "?r (a/b) $ 0 = (?r a / ?r b)$0" by simp
    then have ?lhs using k a0 b0 rb0' 
      by (simp add: fps_divide_def fps_mult_nth fps_inverse_def divide_inverse) }
  moreover
  {assume h: ?lhs
    from a0 b0 have ab0[simp]: "(a/b)$0 = a$0 / b$0" 
      by (simp add: fps_divide_def fps_mult_nth divide_inverse fps_inverse_def)
    have th0: "r k ((a/b)$0) ^ k = (a/b)$0"
      by (simp add: h nonzero_power_divide[OF rb0'] ra0 rb0 del: k)
    from a0 b0 ra0' rb0' kp h 
    have th1: "r k ((a / b) $ 0) = (fps_radical r k a / fps_radical r k b) $ 0"
      by (simp add: fps_divide_def fps_mult_nth fps_inverse_def divide_inverse del: k)
    from a0 b0 ra0' rb0' kp have ab0': "(a / b) $ 0 \<noteq> 0"
      by (simp add: fps_divide_def fps_mult_nth fps_inverse_def nonzero_imp_inverse_nonzero)
    note tha[simp] = iffD1[OF power_radical[where r=r and k=h], OF a0 ra0[unfolded k], unfolded k[symmetric]]
    note thb[simp] = iffD1[OF power_radical[where r=r and k=h], OF b0 rb0[unfolded k], unfolded k[symmetric]]
    have th2: "(?r a / ?r b)^k = a/b"
      by (simp add: fps_divide_def power_mult_distrib fps_inverse_power[symmetric])
    from iffD1[OF radical_unique[where r=r and a="?r a / ?r b" and b="a/b" and k=h], symmetric, unfolded k[symmetric], OF th0 th1 ab0' th2] have ?rhs .}
  ultimately show ?thesis by blast
qed

lemma radical_inverse:
  fixes a :: "'a::field_char_0 fps"
  assumes
  k: "k>0"
  and ra0: "r k (a $ 0) ^ k = a $ 0"
  and r1: "(r k 1)^k = 1"
  and a0: "a$0 \<noteq> 0"
  shows "r k (inverse (a $ 0)) = r k 1 / (r k (a $ 0)) \<longleftrightarrow> fps_radical r k (inverse a) = fps_radical r k 1 / fps_radical r k a"
  using radical_divide[where k=k and r=r and a=1 and b=a, OF k ] ra0 r1 a0
  by (simp add: divide_inverse fps_divide_def)

subsection{* Derivative of composition *}

lemma fps_compose_deriv:
  fixes a:: "('a::idom) fps"
  assumes b0: "b$0 = 0"
  shows "fps_deriv (a oo b) = ((fps_deriv a) oo b) * (fps_deriv b)"
proof-
  {fix n
    have "(fps_deriv (a oo b))$n = setsum (\<lambda>i. a $ i * (fps_deriv (b^i))$n) {0.. Suc n}"
      by (simp add: fps_compose_def field_simps setsum_right_distrib del: of_nat_Suc)
    also have "\<dots> = setsum (\<lambda>i. a$i * ((fps_const (of_nat i)) * (fps_deriv b * (b^(i - 1))))$n) {0.. Suc n}"
      by (simp add: field_simps fps_deriv_power del: fps_mult_left_const_nth of_nat_Suc)
  also have "\<dots> = setsum (\<lambda>i. of_nat i * a$i * (((b^(i - 1)) * fps_deriv b))$n) {0.. Suc n}"
    unfolding fps_mult_left_const_nth  by (simp add: field_simps)
  also have "\<dots> = setsum (\<lambda>i. of_nat i * a$i * (setsum (\<lambda>j. (b^ (i - 1))$j * (fps_deriv b)$(n - j)) {0..n})) {0.. Suc n}"
    unfolding fps_mult_nth ..
  also have "\<dots> = setsum (\<lambda>i. of_nat i * a$i * (setsum (\<lambda>j. (b^ (i - 1))$j * (fps_deriv b)$(n - j)) {0..n})) {1.. Suc n}"
    apply (rule setsum_mono_zero_right)
    apply (auto simp add: mult_delta_left setsum_delta not_le)
    done
  also have "\<dots> = setsum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (setsum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
    unfolding fps_deriv_nth
    apply (rule setsum_reindex_cong [where f = Suc])
    by (auto simp add: mult_assoc)
  finally have th0: "(fps_deriv (a oo b))$n = setsum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (setsum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}" .

  have "(((fps_deriv a) oo b) * (fps_deriv b))$n = setsum (\<lambda>i. (fps_deriv b)$ (n - i) * ((fps_deriv a) oo b)$i) {0..n}"
    unfolding fps_mult_nth by (simp add: mult_ac)
  also have "\<dots> = setsum (\<lambda>i. setsum (\<lambda>j. of_nat (n - i +1) * b$(n - i + 1) * of_nat (j + 1) * a$(j+1) * (b^j)$i) {0..n}) {0..n}"
    unfolding fps_deriv_nth fps_compose_nth setsum_right_distrib mult_assoc
    apply (rule setsum_cong2)
    apply (rule setsum_mono_zero_left)
    apply (simp_all add: subset_eq)
    apply clarify
    apply (subgoal_tac "b^i$x = 0")
    apply simp
    apply (rule startsby_zero_power_prefix[OF b0, rule_format])
    by simp
  also have "\<dots> = setsum (\<lambda>i. of_nat (i + 1) * a$(i+1) * (setsum (\<lambda>j. (b^ i)$j * of_nat (n - j + 1) * b$(n - j + 1)) {0..n})) {0.. n}"
    unfolding setsum_right_distrib
    apply (subst setsum_commute)
    by ((rule setsum_cong2)+) simp
  finally have "(fps_deriv (a oo b))$n = (((fps_deriv a) oo b) * (fps_deriv b)) $n"
    unfolding th0 by simp}
then show ?thesis by (simp add: fps_eq_iff)
qed

lemma fps_mult_X_plus_1_nth:
  "((1+X)*a) $n = (if n = 0 then (a$n :: 'a::comm_ring_1) else a$n + a$(n - 1))"
proof-
  {assume "n = 0" hence ?thesis by (simp add: fps_mult_nth )}
  moreover
  {fix m assume m: "n = Suc m"
    have "((1+X)*a) $n = setsum (\<lambda>i. (1+X)$i * a$(n-i)) {0..n}"
      by (simp add: fps_mult_nth)
    also have "\<dots> = setsum (\<lambda>i. (1+X)$i * a$(n-i)) {0.. 1}"
      unfolding m
      apply (rule setsum_mono_zero_right)
      by (auto simp add: )
    also have "\<dots> = (if n = 0 then (a$n :: 'a::comm_ring_1) else a$n + a$(n - 1))"
      unfolding m
      by (simp add: )
    finally have ?thesis .}
  ultimately show ?thesis by (cases n, auto)
qed

subsection{* Finite FPS (i.e. polynomials) and X *}
lemma fps_poly_sum_X:
  assumes z: "\<forall>i > n. a$i = (0::'a::comm_ring_1)"
  shows "a = setsum (\<lambda>i. fps_const (a$i) * X^i) {0..n}" (is "a = ?r")
proof-
  {fix i
    have "a$i = ?r$i"
      unfolding fps_setsum_nth fps_mult_left_const_nth X_power_nth
      by (simp add: mult_delta_right setsum_delta' z)
  }
  then show ?thesis unfolding fps_eq_iff by blast
qed

subsection{* Compositional inverses *}


fun compinv :: "'a fps \<Rightarrow> nat \<Rightarrow> 'a::{field}" where
  "compinv a 0 = X$0"
| "compinv a (Suc n) = (X$ Suc n - setsum (\<lambda>i. (compinv a i) * (a^i)$Suc n) {0 .. n}) / (a$1) ^ Suc n"

definition "fps_inv a = Abs_fps (compinv a)"

lemma fps_inv: assumes a0: "a$0 = 0" and a1: "a$1 \<noteq> 0"
  shows "fps_inv a oo a = X"
proof-
  let ?i = "fps_inv a oo a"
  {fix n
    have "?i $n = X$n"
    proof(induct n rule: nat_less_induct)
      fix n assume h: "\<forall>m<n. ?i$m = X$m"
      {assume "n=0" hence "?i $n = X$n" using a0
          by (simp add: fps_compose_nth fps_inv_def)}
      moreover
      {fix n1 assume n1: "n = Suc n1"
        have "?i $ n = setsum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1} + fps_inv a $ Suc n1 * (a $ 1)^ Suc n1"
          by (simp add: fps_compose_nth n1 startsby_zero_power_nth_same[OF a0]
                   del: power_Suc)
        also have "\<dots> = setsum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1} + (X$ Suc n1 - setsum (\<lambda>i. (fps_inv a $ i) * (a^i)$n) {0 .. n1})"
          using a0 a1 n1 by (simp add: fps_inv_def)
        also have "\<dots> = X$n" using n1 by simp
        finally have "?i $ n = X$n" .}
      ultimately show "?i $ n = X$n" by (cases n, auto)
    qed}
  then show ?thesis by (simp add: fps_eq_iff)
qed


fun gcompinv :: "'a fps \<Rightarrow> 'a fps \<Rightarrow> nat \<Rightarrow> 'a::{field}" where
  "gcompinv b a 0 = b$0"
| "gcompinv b a (Suc n) = (b$ Suc n - setsum (\<lambda>i. (gcompinv b a i) * (a^i)$Suc n) {0 .. n}) / (a$1) ^ Suc n"

definition "fps_ginv b a = Abs_fps (gcompinv b a)"

lemma fps_ginv: assumes a0: "a$0 = 0" and a1: "a$1 \<noteq> 0"
  shows "fps_ginv b a oo a = b"
proof-
  let ?i = "fps_ginv b a oo a"
  {fix n
    have "?i $n = b$n"
    proof(induct n rule: nat_less_induct)
      fix n assume h: "\<forall>m<n. ?i$m = b$m"
      {assume "n=0" hence "?i $n = b$n" using a0
          by (simp add: fps_compose_nth fps_ginv_def)}
      moreover
      {fix n1 assume n1: "n = Suc n1"
        have "?i $ n = setsum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1} + fps_ginv b a $ Suc n1 * (a $ 1)^ Suc n1"
          by (simp add: fps_compose_nth n1 startsby_zero_power_nth_same[OF a0]
                   del: power_Suc)
        also have "\<dots> = setsum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1} + (b$ Suc n1 - setsum (\<lambda>i. (fps_ginv b a $ i) * (a^i)$n) {0 .. n1})"
          using a0 a1 n1 by (simp add: fps_ginv_def)
        also have "\<dots> = b$n" using n1 by simp
        finally have "?i $ n = b$n" .}
      ultimately show "?i $ n = b$n" by (cases n, auto)
    qed}
  then show ?thesis by (simp add: fps_eq_iff)
qed

lemma fps_inv_ginv: "fps_inv = fps_ginv X"
  apply (auto simp add: fun_eq_iff fps_eq_iff fps_inv_def fps_ginv_def)
  apply (induct_tac n rule: nat_less_induct, auto)
  apply (case_tac na)
  apply simp
  apply simp
  done

lemma fps_compose_1[simp]: "1 oo a = 1"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left setsum_delta)

lemma fps_compose_0[simp]: "0 oo a = 0"
  by (simp add: fps_eq_iff fps_compose_nth)

lemma fps_compose_0_right[simp]: "a oo 0 = fps_const (a$0)"
  by (auto simp add: fps_eq_iff fps_compose_nth power_0_left setsum_0')

lemma fps_compose_add_distrib: "(a + b) oo c = (a oo c) + (b oo c)"
  by (simp add: fps_eq_iff fps_compose_nth field_simps setsum_addf)

lemma fps_compose_setsum_distrib: "(setsum f S) oo a = setsum (\<lambda>i. f i oo a) S"
proof-
  {assume "\<not> finite S" hence ?thesis by simp}
  moreover
  {assume fS: "finite S"
    have ?thesis
    proof(rule finite_induct[OF fS])
      show "setsum f {} oo a = (\<Sum>i\<in>{}. f i oo a)" by simp
    next
      fix x F assume fF: "finite F" and xF: "x \<notin> F" and h: "setsum f F oo a = setsum (\<lambda>i. f i oo a) F"
      show "setsum f (insert x F) oo a  = setsum (\<lambda>i. f i oo a) (insert x F)"
        using fF xF h by (simp add: fps_compose_add_distrib)
    qed}
  ultimately show ?thesis by blast
qed

lemma convolution_eq:
  "setsum (%i. a (i :: nat) * b (n - i)) {0 .. n} = setsum (%(i,j). a i * b j) {(i,j). i <= n \<and> j \<le> n \<and> i + j = n}"
  apply (rule setsum_reindex_cong[where f=fst])
  apply (clarsimp simp add: inj_on_def)
  apply (auto simp add: set_eq_iff image_iff)
  apply (rule_tac x= "x" in exI)
  apply clarsimp
  apply (rule_tac x="n - x" in exI)
  apply arith
  done

lemma product_composition_lemma:
  assumes c0: "c$0 = (0::'a::idom)" and d0: "d$0 = 0"
  shows "((a oo c) * (b oo d))$n = setsum (%(k,m). a$k * b$m * (c^k * d^m) $ n) {(k,m). k + m \<le> n}" (is "?l = ?r")
proof-
  let ?S = "{(k\<Colon>nat, m\<Colon>nat). k + m \<le> n}"
  have s: "?S \<subseteq> {0..n} <*> {0..n}" by (auto simp add: subset_eq)
  have f: "finite {(k\<Colon>nat, m\<Colon>nat). k + m \<le> n}"
    apply (rule finite_subset[OF s])
    by auto
  have "?r =  setsum (%i. setsum (%(k,m). a$k * (c^k)$i * b$m * (d^m) $ (n - i)) {(k,m). k + m \<le> n}) {0..n}"
    apply (simp add: fps_mult_nth setsum_right_distrib)
    apply (subst setsum_commute)
    apply (rule setsum_cong2)
    by (auto simp add: field_simps)
  also have "\<dots> = ?l"
    apply (simp add: fps_mult_nth fps_compose_nth setsum_product)
    apply (rule setsum_cong2)
    apply (simp add: setsum_cartesian_product mult_assoc)
    apply (rule setsum_mono_zero_right[OF f])
    apply (simp add: subset_eq) apply presburger
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
  assumes c0: "c$0 = (0::'a::idom)" and d0: "d$0 = 0"
  shows "((a oo c) * (b oo d))$n = setsum (%k. setsum (%m. a$k * b$m * (c^k * d^m) $ n) {0..n}) {0..n}" (is "?l = ?r")
  unfolding product_composition_lemma[OF c0 d0]
  unfolding setsum_cartesian_product
  apply (rule setsum_mono_zero_left)
  apply simp
  apply (clarsimp simp add: subset_eq)
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "(c^aa * d^ba) $ n = 0")
  apply simp
  unfolding fps_mult_nth
  apply (rule setsum_0')
  apply (clarsimp simp add: not_le)
  apply (case_tac "aaa < aa")
  apply (rule startsby_zero_power_prefix[OF c0, rule_format])
  apply simp
  apply (subgoal_tac "n - aaa < ba")
  apply (frule_tac k = "ba" in startsby_zero_power_prefix[OF d0, rule_format])
  apply simp
  apply arith
  done


lemma setsum_pair_less_iff:
  "setsum (%((k::nat),m). a k * b m * c (k + m)) {(k,m). k + m \<le> n} = setsum (%s. setsum (%i. a i * b (s - i) * c s) {0..s}) {0..n}" (is "?l = ?r")
proof-
  let ?KM=  "{(k,m). k + m \<le> n}"
  let ?f = "%s. UNION {(0::nat)..s} (%i. {(i,s - i)})"
  have th0: "?KM = UNION {0..n} ?f"
    apply (simp add: set_eq_iff)
    apply arith (* FIXME: VERY slow! *)
    done
  show "?l = ?r "
    unfolding th0
    apply (subst setsum_UN_disjoint)
    apply auto
    apply (subst setsum_UN_disjoint)
    apply auto
    done
qed

lemma fps_compose_mult_distrib_lemma:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "((a oo c) * (b oo c))$n = setsum (%s. setsum (%i. a$i * b$(s - i) * (c^s) $ n) {0..s}) {0..n}" (is "?l = ?r")
  unfolding product_composition_lemma[OF c0 c0] power_add[symmetric]
  unfolding setsum_pair_less_iff[where a = "%k. a$k" and b="%m. b$m" and c="%s. (c ^ s)$n" and n = n] ..


lemma fps_compose_mult_distrib:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "(a * b) oo c = (a oo c) * (b oo c)" (is "?l = ?r")
  apply (simp add: fps_eq_iff fps_compose_mult_distrib_lemma[OF c0])
  by (simp add: fps_compose_nth fps_mult_nth setsum_left_distrib)
lemma fps_compose_setprod_distrib:
  assumes c0: "c$0 = (0::'a::idom)"
  shows "(setprod a S) oo c = setprod (%k. a k oo c) S" (is "?l = ?r")
  apply (cases "finite S")
  apply simp_all
  apply (induct S rule: finite_induct)
  apply simp
  apply (simp add: fps_compose_mult_distrib[OF c0])
  done

lemma fps_compose_power:   assumes c0: "c$0 = (0::'a::idom)"
  shows "(a oo c)^n = a^n oo c" (is "?l = ?r")
proof-
  {assume "n=0" then have ?thesis by simp}
  moreover
  {fix m assume m: "n = Suc m"
    have th0: "a^n = setprod (%k. a) {0..m}" "(a oo c) ^ n = setprod (%k. a oo c) {0..m}"
      by (simp_all add: setprod_constant m)
    then have ?thesis
      by (simp add: fps_compose_setprod_distrib[OF c0])}
  ultimately show ?thesis by (cases n, auto)
qed

lemma fps_compose_uminus: "- (a::'a::ring_1 fps) oo c = - (a oo c)"
  by (simp add: fps_eq_iff fps_compose_nth field_simps setsum_negf[symmetric])

lemma fps_compose_sub_distrib:
  shows "(a - b) oo (c::'a::ring_1 fps) = (a oo c) - (b oo c)"
  unfolding diff_minus fps_compose_uminus fps_compose_add_distrib ..

lemma X_fps_compose:"X oo a = Abs_fps (\<lambda>n. if n = 0 then (0::'a::comm_ring_1) else a$n)"
  by (simp add: fps_eq_iff fps_compose_nth mult_delta_left setsum_delta power_Suc)

lemma fps_inverse_compose:
  assumes b0: "(b$0 :: 'a::field) = 0" and a0: "a$0 \<noteq> 0"
  shows "inverse a oo b = inverse (a oo b)"
proof-
  let ?ia = "inverse a"
  let ?ab = "a oo b"
  let ?iab = "inverse ?ab"

from a0 have ia0: "?ia $ 0 \<noteq> 0" by (simp )
from a0 have ab0: "?ab $ 0 \<noteq> 0" by (simp add: fps_compose_def)
have "(?ia oo b) *  (a oo b) = 1"
unfolding fps_compose_mult_distrib[OF b0, symmetric]
unfolding inverse_mult_eq_1[OF a0]
fps_compose_1 ..

then have "(?ia oo b) *  (a oo b) * ?iab  = 1 * ?iab" by simp
then have "(?ia oo b) *  (?iab * (a oo b))  = ?iab" by simp
then show ?thesis 
  unfolding inverse_mult_eq_1[OF ab0] by simp
qed

lemma fps_divide_compose:
  assumes c0: "(c$0 :: 'a::field) = 0" and b0: "b$0 \<noteq> 0"
  shows "(a/b) oo c = (a oo c) / (b oo c)"
    unfolding fps_divide_def fps_compose_mult_distrib[OF c0]
    fps_inverse_compose[OF c0 b0] ..

lemma gp: assumes a0: "a$0 = (0::'a::field)"
  shows "(Abs_fps (\<lambda>n. 1)) oo a = 1/(1 - a)" (is "?one oo a = _")
proof-
  have o0: "?one $ 0 \<noteq> 0" by simp
  have th0: "(1 - X) $ 0 \<noteq> (0::'a)" by simp  
  from fps_inverse_gp[where ?'a = 'a]
  have "inverse ?one = 1 - X" by (simp add: fps_eq_iff)
  hence "inverse (inverse ?one) = inverse (1 - X)" by simp
  hence th: "?one = 1/(1 - X)" unfolding fps_inverse_idempotent[OF o0] 
    by (simp add: fps_divide_def)
  show ?thesis unfolding th
    unfolding fps_divide_compose[OF a0 th0]
    fps_compose_1 fps_compose_sub_distrib X_fps_compose_startby0[OF a0] ..
qed

lemma fps_const_power[simp]: "fps_const (c::'a::ring_1) ^ n = fps_const (c^n)"
by (induct n, auto)

lemma fps_compose_radical:
  assumes b0: "b$0 = (0::'a::field_char_0)"
  and ra0: "r (Suc k) (a$0) ^ Suc k = a$0"
  and a0: "a$0 \<noteq> 0"
  shows "fps_radical r (Suc k)  a oo b = fps_radical r (Suc k) (a oo b)"
proof-
  let ?r = "fps_radical r (Suc k)"
  let ?ab = "a oo b"
  have ab0: "?ab $ 0 = a$0" by (simp add: fps_compose_def)
  from ab0 a0 ra0 have rab0: "?ab $ 0 \<noteq> 0" "r (Suc k) (?ab $ 0) ^ Suc k = ?ab $ 0" by simp_all
  have th00: "r (Suc k) ((a oo b) $ 0) = (fps_radical r (Suc k) a oo b) $ 0"
    by (simp add: ab0 fps_compose_def)
  have th0: "(?r a oo b) ^ (Suc k) = a  oo b"
    unfolding fps_compose_power[OF b0]
    unfolding iffD1[OF power_radical[of a r k], OF a0 ra0]  .. 
  from iffD1[OF radical_unique[where r=r and k=k and b= ?ab and a = "?r a oo b", OF rab0(2) th00 rab0(1)], OF th0] show ?thesis  . 
qed

lemma fps_const_mult_apply_left:
  "fps_const c * (a oo b) = (fps_const c * a) oo b"
  by (simp add: fps_eq_iff fps_compose_nth setsum_right_distrib mult_assoc)

lemma fps_const_mult_apply_right:
  "(a oo b) * fps_const (c::'a::comm_semiring_1) = (fps_const c * a) oo b"
  by (auto simp add: fps_const_mult_apply_left mult_commute)

lemma fps_compose_assoc:
  assumes c0: "c$0 = (0::'a::idom)" and b0: "b$0 = 0"
  shows "a oo (b oo c) = a oo b oo c" (is "?l = ?r")
proof-
  {fix n
    have "?l$n = (setsum (\<lambda>i. (fps_const (a$i) * b^i) oo c) {0..n})$n"
      by (simp add: fps_compose_nth fps_compose_power[OF c0] fps_const_mult_apply_left setsum_right_distrib mult_assoc fps_setsum_nth)
    also have "\<dots> = ((setsum (\<lambda>i. fps_const (a$i) * b^i) {0..n}) oo c)$n"
      by (simp add: fps_compose_setsum_distrib)
    also have "\<dots> = ?r$n"
      apply (simp add: fps_compose_nth fps_setsum_nth setsum_left_distrib mult_assoc)
      apply (rule setsum_cong2)
      apply (rule setsum_mono_zero_right)
      apply (auto simp add: not_le)
      by (erule startsby_zero_power_prefix[OF b0, rule_format])
    finally have "?l$n = ?r$n" .}
  then show ?thesis by (simp add: fps_eq_iff)
qed


lemma fps_X_power_compose:
  assumes a0: "a$0=0" shows "X^k oo a = (a::('a::idom fps))^k" (is "?l = ?r")
proof-
  {assume "k=0" hence ?thesis by simp}
  moreover
  {fix h assume h: "k = Suc h"
    {fix n
      {assume kn: "k>n" hence "?l $ n = ?r $n" using a0 startsby_zero_power_prefix[OF a0] h
          by (simp add: fps_compose_nth del: power_Suc)}
      moreover
      {assume kn: "k \<le> n"
        hence "?l$n = ?r$n"
          by (simp add: fps_compose_nth mult_delta_left setsum_delta)}
      moreover have "k >n \<or> k\<le> n"  by arith
      ultimately have "?l$n = ?r$n"  by blast}
    then have ?thesis unfolding fps_eq_iff by blast}
  ultimately show ?thesis by (cases k, auto)
qed

lemma fps_inv_right: assumes a0: "a$0 = 0" and a1: "a$1 \<noteq> 0"
  shows "a oo fps_inv a = X"
proof-
  let ?ia = "fps_inv a"
  let ?iaa = "a oo fps_inv a"
  have th0: "?ia $ 0 = 0" by (simp add: fps_inv_def)
  have th1: "?iaa $ 0 = 0" using a0 a1
    by (simp add: fps_inv_def fps_compose_nth)
  have th2: "X$0 = 0" by simp
  from fps_inv[OF a0 a1] have "a oo (fps_inv a oo a) = a oo X" by simp
  then have "(a oo fps_inv a) oo a = X oo a"
    by (simp add: fps_compose_assoc[OF a0 th0] X_fps_compose_startby0[OF a0])
  with fps_compose_inj_right[OF a0 a1]
  show ?thesis by simp
qed

lemma fps_inv_deriv:
  assumes a0:"a$0 = (0::'a::{field})" and a1: "a$1 \<noteq> 0"
  shows "fps_deriv (fps_inv a) = inverse (fps_deriv a oo fps_inv a)"
proof-
  let ?ia = "fps_inv a"
  let ?d = "fps_deriv a oo ?ia"
  let ?dia = "fps_deriv ?ia"
  have ia0: "?ia$0 = 0" by (simp add: fps_inv_def)
  have th0: "?d$0 \<noteq> 0" using a1 by (simp add: fps_compose_nth fps_deriv_nth)
  from fps_inv_right[OF a0 a1] have "?d * ?dia = 1"
    by (simp add: fps_compose_deriv[OF ia0, of a, symmetric] )
  hence "inverse ?d * ?d * ?dia = inverse ?d * 1" by simp
  with inverse_mult_eq_1[OF th0]
  show "?dia = inverse ?d" by simp
qed

lemma fps_inv_idempotent: 
  assumes a0: "a$0 = 0" and a1: "a$1 \<noteq> 0"
  shows "fps_inv (fps_inv a) = a"
proof-
  let ?r = "fps_inv"
  have ra0: "?r a $ 0 = 0" by (simp add: fps_inv_def)
  from a1 have ra1: "?r a $ 1 \<noteq> 0" by (simp add: fps_inv_def field_simps)
  have X0: "X$0 = 0" by simp
  from fps_inv[OF ra0 ra1] have "?r (?r a) oo ?r a = X" .
  then have "?r (?r a) oo ?r a oo a = X oo a" by simp
  then have "?r (?r a) oo (?r a oo a) = a" 
    unfolding X_fps_compose_startby0[OF a0]
    unfolding fps_compose_assoc[OF a0 ra0, symmetric] .
  then show ?thesis unfolding fps_inv[OF a0 a1] by simp
qed

lemma fps_ginv_ginv:
  assumes a0: "a$0 = 0" and a1: "a$1 \<noteq> 0"
  and c0: "c$0 = 0" and  c1: "c$1 \<noteq> 0"
  shows "fps_ginv b (fps_ginv c a) = b oo a oo fps_inv c"
proof-
  let ?r = "fps_ginv"
  from c0 have rca0: "?r c a $0 = 0" by (simp add: fps_ginv_def)
  from a1 c1 have rca1: "?r c a $ 1 \<noteq> 0" by (simp add: fps_ginv_def field_simps)
  from fps_ginv[OF rca0 rca1] 
  have "?r b (?r c a) oo ?r c a = b" .
  then have "?r b (?r c a) oo ?r c a oo a = b oo a" by simp
  then have "?r b (?r c a) oo (?r c a oo a) = b oo a"
    apply (subst fps_compose_assoc)
    using a0 c0 by (auto simp add: fps_ginv_def)
  then have "?r b (?r c a) oo c = b oo a"
    unfolding fps_ginv[OF a0 a1] .
  then have "?r b (?r c a) oo c oo fps_inv c= b oo a oo fps_inv c" by simp
  then have "?r b (?r c a) oo (c oo fps_inv c) = b oo a oo fps_inv c"
    apply (subst fps_compose_assoc)
    using a0 c0 by (auto simp add: fps_inv_def)
  then show ?thesis unfolding fps_inv_right[OF c0 c1] by simp
qed

lemma fps_ginv_deriv:
  assumes a0:"a$0 = (0::'a::{field})" and a1: "a$1 \<noteq> 0"
  shows "fps_deriv (fps_ginv b a) = (fps_deriv b / fps_deriv a) oo fps_ginv X a"
proof-
  let ?ia = "fps_ginv b a"
  let ?iXa = "fps_ginv X a"
  let ?d = "fps_deriv"
  let ?dia = "?d ?ia"
  have iXa0: "?iXa $ 0 = 0" by (simp add: fps_ginv_def)
  have da0: "?d a $ 0 \<noteq> 0" using a1 by simp
  from fps_ginv[OF a0 a1, of b] have "?d (?ia oo a) = fps_deriv b" by simp
  then have "(?d ?ia oo a) * ?d a = ?d b" unfolding fps_compose_deriv[OF a0] .
  then have "(?d ?ia oo a) * ?d a * inverse (?d a) = ?d b * inverse (?d a)" by simp
  then have "(?d ?ia oo a) * (inverse (?d a) * ?d a) = ?d b / ?d a" 
    by (simp add: fps_divide_def)
  then have "(?d ?ia oo a) oo ?iXa =  (?d b / ?d a) oo ?iXa "
    unfolding inverse_mult_eq_1[OF da0] by simp
  then have "?d ?ia oo (a oo ?iXa) =  (?d b / ?d a) oo ?iXa"
    unfolding fps_compose_assoc[OF iXa0 a0] .
  then show ?thesis unfolding fps_inv_ginv[symmetric]
    unfolding fps_inv_right[OF a0 a1] by simp
qed

subsection{* Elementary series *}

subsubsection{* Exponential series *}
definition "E x = Abs_fps (\<lambda>n. x^n / of_nat (fact n))"

lemma E_deriv[simp]: "fps_deriv (E a) = fps_const (a::'a::field_char_0) * E a" (is "?l = ?r")
proof-
  {fix n
    have "?l$n = ?r $ n"
  apply (auto simp add: E_def field_simps power_Suc[symmetric]simp del: fact_Suc of_nat_Suc power_Suc)
  by (simp add: of_nat_mult field_simps)}
then show ?thesis by (simp add: fps_eq_iff)
qed

lemma E_unique_ODE:
  "fps_deriv a = fps_const c * a \<longleftrightarrow> a = fps_const (a$0) * E (c :: 'a::field_char_0)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume d: ?lhs
  from d have th: "\<And>n. a $ Suc n = c * a$n / of_nat (Suc n)"
    by (simp add: fps_deriv_def fps_eq_iff field_simps del: of_nat_Suc)
  {fix n have "a$n = a$0 * c ^ n/ (of_nat (fact n))"
      apply (induct n)
      apply simp
      unfolding th
      using fact_gt_zero_nat
      apply (simp add: field_simps del: of_nat_Suc fact_Suc)
      apply (drule sym)
      by (simp add: field_simps of_nat_mult power_Suc)}
  note th' = this
  have ?rhs
    by (auto simp add: fps_eq_iff fps_const_mult_left E_def intro : th')}
moreover
{assume h: ?rhs
  have ?lhs
    apply (subst h)
    apply simp
    apply (simp only: h[symmetric])
  by simp}
ultimately show ?thesis by blast
qed

lemma E_add_mult: "E (a + b) = E (a::'a::field_char_0) * E b" (is "?l = ?r")
proof-
  have "fps_deriv (?r) = fps_const (a+b) * ?r"
    by (simp add: fps_const_add[symmetric] field_simps del: fps_const_add)
  then have "?r = ?l" apply (simp only: E_unique_ODE)
    by (simp add: fps_mult_nth E_def)
  then show ?thesis ..
qed

lemma E_nth[simp]: "E a $ n = a^n / of_nat (fact n)"
  by (simp add: E_def)

lemma E0[simp]: "E (0::'a::{field}) = 1"
  by (simp add: fps_eq_iff power_0_left)

lemma E_neg: "E (- a) = inverse (E (a::'a::field_char_0))"
proof-
  from E_add_mult[of a "- a"] have th0: "E a * E (- a) = 1"
    by (simp )
  have th1: "E a $ 0 \<noteq> 0" by simp
  from fps_inverse_unique[OF th1 th0] show ?thesis by simp
qed

lemma E_nth_deriv[simp]: "fps_nth_deriv n (E (a::'a::field_char_0)) = (fps_const a)^n * (E a)"
  by (induct n, auto simp add: power_Suc)

lemma X_compose_E[simp]: "X oo E (a::'a::{field}) = E a - 1"
  by (simp add: fps_eq_iff X_fps_compose)

lemma LE_compose:
  assumes a: "a\<noteq>0"
  shows "fps_inv (E a - 1) oo (E a - 1) = X"
  and "(E a - 1) oo fps_inv (E a - 1) = X"
proof-
  let ?b = "E a - 1"
  have b0: "?b $ 0 = 0" by simp
  have b1: "?b $ 1 \<noteq> 0" by (simp add: a)
  from fps_inv[OF b0 b1] show "fps_inv (E a - 1) oo (E a - 1) = X" .
  from fps_inv_right[OF b0 b1] show "(E a - 1) oo fps_inv (E a - 1) = X" .
qed


lemma fps_const_inverse:
  "a \<noteq> 0 \<Longrightarrow> inverse (fps_const (a::'a::field)) = fps_const (inverse a)"
  apply (auto simp add: fps_eq_iff fps_inverse_def) by (case_tac "n", auto)

lemma inverse_one_plus_X:
  "inverse (1 + X) = Abs_fps (\<lambda>n. (- 1 ::'a::{field})^n)"
  (is "inverse ?l = ?r")
proof-
  have th: "?l * ?r = 1"
    by (auto simp add: field_simps fps_eq_iff minus_one_power_iff)
  have th': "?l $ 0 \<noteq> 0" by (simp add: )
  from fps_inverse_unique[OF th' th] show ?thesis .
qed

lemma E_power_mult: "(E (c::'a::field_char_0))^n = E (of_nat n * c)"
  by (induct n, auto simp add: field_simps E_add_mult power_Suc)

lemma radical_E:
  assumes r: "r (Suc k) 1 = 1" 
  shows "fps_radical r (Suc k) (E (c::'a::{field_char_0})) = E (c / of_nat (Suc k))"
proof-
  let ?ck = "(c / of_nat (Suc k))"
  let ?r = "fps_radical r (Suc k)"
  have eq0[simp]: "?ck * of_nat (Suc k) = c" "of_nat (Suc k) * ?ck = c"
    by (simp_all del: of_nat_Suc)
  have th0: "E ?ck ^ (Suc k) = E c" unfolding E_power_mult eq0 ..
  have th: "r (Suc k) (E c $0) ^ Suc k = E c $ 0"
    "r (Suc k) (E c $ 0) = E ?ck $ 0" "E c $ 0 \<noteq> 0" using r by simp_all
  from th0 radical_unique[where r=r and k=k, OF th]
  show ?thesis by auto 
qed

lemma Ec_E1_eq: 
  "E (1::'a::{field_char_0}) oo (fps_const c * X) = E c"
  apply (auto simp add: fps_eq_iff E_def fps_compose_def power_mult_distrib)
  by (simp add: cond_value_iff cond_application_beta setsum_delta' cong del: if_weak_cong)

text{* The generalized binomial theorem as a  consequence of @{thm E_add_mult} *}

lemma gbinomial_theorem: 
  "((a::'a::{field_char_0, field_inverse_zero})+b) ^ n = (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
proof-
  from E_add_mult[of a b] 
  have "(E (a + b)) $ n = (E a * E b)$n" by simp
  then have "(a + b) ^ n = (\<Sum>i\<Colon>nat = 0\<Colon>nat..n. a ^ i * b ^ (n - i)  * (of_nat (fact n) / of_nat (fact i * fact (n - i))))"
    by (simp add: field_simps fps_mult_nth of_nat_mult[symmetric] setsum_right_distrib)
  then show ?thesis 
    apply simp
    apply (rule setsum_cong2)
    apply simp
    apply (frule binomial_fact[where ?'a = 'a, symmetric])
    by (simp add: field_simps of_nat_mult)
qed

text{* And the nat-form -- also available from Binomial.thy *}
lemma binomial_theorem: "(a+b) ^ n = (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k))"
  using gbinomial_theorem[of "of_nat a" "of_nat b" n]
  unfolding of_nat_add[symmetric] of_nat_power[symmetric] of_nat_mult[symmetric] of_nat_setsum[symmetric]
  by simp

subsubsection{* Logarithmic series *}

lemma Abs_fps_if_0: 
  "Abs_fps(%n. if n=0 then (v::'a::ring_1) else f n) = fps_const v + X * Abs_fps (%n. f (Suc n))"
  by (auto simp add: fps_eq_iff)

definition L:: "'a::{field_char_0} \<Rightarrow> 'a fps" where 
  "L c \<equiv> fps_const (1/c) * Abs_fps (\<lambda>n. if n = 0 then 0 else (- 1) ^ (n - 1) / of_nat n)"

lemma fps_deriv_L: "fps_deriv (L c) = fps_const (1/c) * inverse (1 + X)"
  unfolding inverse_one_plus_X
  by (simp add: L_def fps_eq_iff del: of_nat_Suc)

lemma L_nth: "L c $ n = (if n=0 then 0 else 1/c * ((- 1) ^ (n - 1) / of_nat n))"
  by (simp add: L_def field_simps)

lemma L_0[simp]: "L c $ 0 = 0" by (simp add: L_def)
lemma L_E_inv:
  assumes a: "a\<noteq> (0::'a::{field_char_0})"
  shows "L a = fps_inv (E a - 1)" (is "?l = ?r")
proof-
  let ?b = "E a - 1"
  have b0: "?b $ 0 = 0" by simp
  have b1: "?b $ 1 \<noteq> 0" by (simp add: a)
  have "fps_deriv (E a - 1) oo fps_inv (E a - 1) = (fps_const a * (E a - 1) + fps_const a) oo fps_inv (E a - 1)"
    by (simp add: field_simps)
  also have "\<dots> = fps_const a * (X + 1)" apply (simp add: fps_compose_add_distrib fps_const_mult_apply_left[symmetric] fps_inv_right[OF b0 b1])
    by (simp add: field_simps)
  finally have eq: "fps_deriv (E a - 1) oo fps_inv (E a - 1) = fps_const a * (X + 1)" .
  from fps_inv_deriv[OF b0 b1, unfolded eq]
  have "fps_deriv (fps_inv ?b) = fps_const (inverse a) / (X + 1)"
    using a 
    by (simp add: fps_const_inverse eq fps_divide_def fps_inverse_mult)
  hence "fps_deriv ?l = fps_deriv ?r"
    by (simp add: fps_deriv_L add_commute fps_divide_def divide_inverse)
  then show ?thesis unfolding fps_deriv_eq_iff
    by (simp add: L_nth fps_inv_def)
qed

lemma L_mult_add: 
  assumes c0: "c\<noteq>0" and d0: "d\<noteq>0"
  shows "L c + L d = fps_const (c+d) * L (c*d)"
  (is "?r = ?l")
proof-
  from c0 d0 have eq: "1/c + 1/d = (c+d)/(c*d)" by (simp add: field_simps)
  have "fps_deriv ?r = fps_const (1/c + 1/d) * inverse (1 + X)"
    by (simp add: fps_deriv_L fps_const_add[symmetric] algebra_simps del: fps_const_add)
  also have "\<dots> = fps_deriv ?l"
    apply (simp add: fps_deriv_L)
    by (simp add: fps_eq_iff eq)
  finally show ?thesis
    unfolding fps_deriv_eq_iff by simp
qed

subsubsection{* Binomial series *}

definition "fps_binomial a = Abs_fps (\<lambda>n. a gchoose n)"

lemma fps_binomial_nth[simp]: "fps_binomial a $ n = a gchoose n"
  by (simp add: fps_binomial_def)

lemma fps_binomial_ODE_unique:
  fixes c :: "'a::field_char_0"
  shows "fps_deriv a = (fps_const c * a) / (1 + X) \<longleftrightarrow> a = fps_const (a$0) * fps_binomial c"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?da = "fps_deriv a"
  let ?x1 = "(1 + X):: 'a fps"
  let ?l = "?x1 * ?da"
  let ?r = "fps_const c * a"
  have x10: "?x1 $ 0 \<noteq> 0" by simp
  have "?l = ?r \<longleftrightarrow> inverse ?x1 * ?l = inverse ?x1 * ?r" by simp
  also have "\<dots> \<longleftrightarrow> ?da = (fps_const c * a) / ?x1"
    apply (simp only: fps_divide_def  mult_assoc[symmetric] inverse_mult_eq_1[OF x10])
    by (simp add: field_simps)
  finally have eq: "?l = ?r \<longleftrightarrow> ?lhs" by simp
  moreover
  {assume h: "?l = ?r" 
    {fix n
      from h have lrn: "?l $ n = ?r$n" by simp
      
      from lrn 
      have "a$ Suc n = ((c - of_nat n) / of_nat (Suc n)) * a $n" 
        apply (simp add: field_simps del: of_nat_Suc)
        by (cases n, simp_all add: field_simps del: of_nat_Suc)
    }
    note th0 = this
    {fix n have "a$n = (c gchoose n) * a$0"
      proof(induct n)
        case 0 thus ?case by simp
      next
        case (Suc m)
        thus ?case unfolding th0
          apply (simp add: field_simps del: of_nat_Suc)
          unfolding mult_assoc[symmetric] gbinomial_mult_1
          by (simp add: field_simps)
      qed}
    note th1 = this
    have ?rhs
      apply (simp add: fps_eq_iff)
      apply (subst th1)
      by (simp add: field_simps)}
  moreover
  {assume h: ?rhs
  have th00:"\<And>x y. x * (a$0 * y) = a$0 * (x*y)" by (simp add: mult_commute)
    have "?l = ?r" 
      apply (subst h)
      apply (subst (2) h)
      apply (clarsimp simp add: fps_eq_iff field_simps)
      unfolding mult_assoc[symmetric] th00 gbinomial_mult_1
      by (simp add: field_simps gbinomial_mult_1)}
  ultimately show ?thesis by blast
qed

lemma fps_binomial_deriv: "fps_deriv (fps_binomial c) = fps_const c * fps_binomial c / (1 + X)"
proof-
  let ?a = "fps_binomial c"
  have th0: "?a = fps_const (?a$0) * ?a" by (simp)
  from iffD2[OF fps_binomial_ODE_unique, OF th0] show ?thesis .
qed

lemma fps_binomial_add_mult: "fps_binomial (c+d) = fps_binomial c * fps_binomial d" (is "?l = ?r")
proof-
  let ?P = "?r - ?l"
  let ?b = "fps_binomial"
  let ?db = "\<lambda>x. fps_deriv (?b x)"
  have "fps_deriv ?P = ?db c * ?b d + ?b c * ?db d - ?db (c + d)"  by simp
  also have "\<dots> = inverse (1 + X) * (fps_const c * ?b c * ?b d + fps_const d * ?b c * ?b d - fps_const (c+d) * ?b (c + d))"
    unfolding fps_binomial_deriv
    by (simp add: fps_divide_def field_simps)
  also have "\<dots> = (fps_const (c + d)/ (1 + X)) * ?P"
    by (simp add: field_simps fps_divide_def fps_const_add[symmetric] del: fps_const_add)
  finally have th0: "fps_deriv ?P = fps_const (c+d) * ?P / (1 + X)"
    by (simp add: fps_divide_def)
  have "?P = fps_const (?P$0) * ?b (c + d)"
    unfolding fps_binomial_ODE_unique[symmetric]
    using th0 by simp
  hence "?P = 0" by (simp add: fps_mult_nth)
  then show ?thesis by simp
qed

lemma fps_minomial_minus_one: "fps_binomial (- 1) = inverse (1 + X)"
  (is "?l = inverse ?r")
proof-
  have th: "?r$0 \<noteq> 0" by simp
  have th': "fps_deriv (inverse ?r) = fps_const (- 1) * inverse ?r / (1 + X)"
    by (simp add: fps_inverse_deriv[OF th] fps_divide_def power2_eq_square mult_commute fps_const_neg[symmetric] del: fps_const_neg)
  have eq: "inverse ?r $ 0 = 1"
    by (simp add: fps_inverse_def)
  from iffD1[OF fps_binomial_ODE_unique[of "inverse (1 + X)" "- 1"] th'] eq
  show ?thesis by (simp add: fps_inverse_def)
qed

text{* Vandermonde's Identity as a consequence *}
lemma gbinomial_Vandermonde: "setsum (\<lambda>k. (a gchoose k) * (b gchoose (n - k))) {0..n} = (a + b) gchoose n"
proof-
  let ?ba = "fps_binomial a"
  let ?bb = "fps_binomial b"
  let ?bab = "fps_binomial (a + b)"
  from fps_binomial_add_mult[of a b] have "?bab $ n = (?ba * ?bb)$n" by simp
  then show ?thesis by (simp add: fps_mult_nth)
qed

lemma binomial_Vandermonde: "setsum (\<lambda>k. (a choose k) * (b choose (n - k))) {0..n} = (a + b) choose n"
  using gbinomial_Vandermonde[of "(of_nat a)" "of_nat b" n]
  
  apply (simp only: binomial_gbinomial[symmetric] of_nat_mult[symmetric] of_nat_setsum[symmetric] of_nat_add[symmetric])
  by simp
  
lemma binomial_Vandermonde_same: "setsum (\<lambda>k. (n choose k)^2) {0..n} = (2*n) choose n"
  using binomial_Vandermonde[of n n n,symmetric]
  unfolding nat_mult_2 apply (simp add: power2_eq_square)
  apply (rule setsum_cong2)
  by (auto intro:  binomial_symmetric)

lemma Vandermonde_pochhammer_lemma:
  fixes a :: "'a::field_char_0"
  assumes b: "\<forall> j\<in>{0 ..<n}. b \<noteq> of_nat j"
  shows "setsum (%k. (pochhammer (- a) k * pochhammer (- (of_nat n)) k) / (of_nat (fact k) * pochhammer (b - of_nat n + 1) k)) {0..n} = pochhammer (- (a+ b)) n / pochhammer (- b) n" (is "?l = ?r")
proof-
  let ?m1 = "%m. (- 1 :: 'a) ^ m"
  let ?f = "%m. of_nat (fact m)"
  let ?p = "%(x::'a). pochhammer (- x)"
  from b have bn0: "?p b n \<noteq> 0" unfolding pochhammer_eq_0_iff by simp
  {fix k assume kn: "k \<in> {0..n}"
    {assume c:"pochhammer (b - of_nat n + 1) n = 0"
      then obtain j where j: "j < n" "b - of_nat n + 1 = - of_nat j"
        unfolding pochhammer_eq_0_iff by blast
      from j have "b = of_nat n - of_nat j - of_nat 1" 
        by (simp add: algebra_simps)
      then have "b = of_nat (n - j - 1)" 
        using j kn by (simp add: of_nat_diff)
      with b have False using j by auto}
    then have nz: "pochhammer (1 + b - of_nat n) n \<noteq> 0" 
      by (auto simp add: algebra_simps)
    
    from nz kn [simplified] have nz': "pochhammer (1 + b - of_nat n) k \<noteq> 0" 
      by (rule pochhammer_neq_0_mono)
    {assume k0: "k = 0 \<or> n =0" 
      then have "b gchoose (n - k) = (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)" 
        using kn
        by (cases "k=0", simp_all add: gbinomial_pochhammer)}
    moreover
    {assume n0: "n \<noteq> 0" and k0: "k \<noteq> 0" 
      then obtain m where m: "n = Suc m" by (cases n, auto)
      from k0 obtain h where h: "k = Suc h" by (cases k, auto)
      {assume kn: "k = n"
        then have "b gchoose (n - k) = (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)"
          using kn pochhammer_minus'[where k=k and n=n and b=b]
          apply (simp add:  pochhammer_same)
          using bn0
          by (simp add: field_simps power_add[symmetric])}
      moreover
      {assume nk: "k \<noteq> n"
        have m1nk: "?m1 n = setprod (%i. - 1) {0..m}" 
          "?m1 k = setprod (%i. - 1) {0..h}"
          by (simp_all add: setprod_constant m h)
        from kn nk have kn': "k < n" by simp
        have bnz0: "pochhammer (b - of_nat n + 1) k \<noteq> 0"
          using bn0 kn 
          unfolding pochhammer_eq_0_iff
          apply auto
          apply (erule_tac x= "n - ka - 1" in allE)
          by (auto simp add: algebra_simps of_nat_diff)
        have eq1: "setprod (%k. (1::'a) + of_nat m - of_nat k) {0 .. h} = setprod of_nat {Suc (m - h) .. Suc m}"        
          apply (rule strong_setprod_reindex_cong[where f="%k. Suc m - k "])
          using kn' h m
          apply (auto simp add: inj_on_def image_def)
          apply (rule_tac x="Suc m - x" in bexI)
          apply (simp_all add: of_nat_diff)
          done
        
        have th1: "(?m1 k * ?p (of_nat n) k) / ?f n = 1 / of_nat(fact (n - k))"
          unfolding m1nk 
          
          unfolding m h pochhammer_Suc_setprod
          apply (simp add: field_simps del: fact_Suc id_def)
          unfolding fact_altdef_nat id_def
          unfolding of_nat_setprod
          unfolding setprod_timesf[symmetric]
          apply auto
          unfolding eq1
          apply (subst setprod_Un_disjoint[symmetric])
          apply (auto)
          apply (rule setprod_cong)
          apply auto
          done
        have th20: "?m1 n * ?p b n = setprod (%i. b - of_nat i) {0..m}"
          unfolding m1nk 
          unfolding m h pochhammer_Suc_setprod
          unfolding setprod_timesf[symmetric]
          apply (rule setprod_cong)
          apply auto
          done
        have th21:"pochhammer (b - of_nat n + 1) k = setprod (%i. b - of_nat i) {n - k .. n - 1}"
          unfolding h m 
          unfolding pochhammer_Suc_setprod
          apply (rule strong_setprod_reindex_cong[where f="%k. n - 1 - k"])
          using kn
          apply (auto simp add: inj_on_def m h image_def)
          apply (rule_tac x= "m - x" in bexI)
          by (auto simp add: of_nat_diff)
        
        have "?m1 n * ?p b n = pochhammer (b - of_nat n + 1) k * setprod (%i. b - of_nat i) {0.. n - k - 1}"
          unfolding th20 th21
          unfolding h m
          apply (subst setprod_Un_disjoint[symmetric])
          using kn' h m
          apply auto
          apply (rule setprod_cong)
          apply auto
          done
        then have th2: "(?m1 n * ?p b n)/pochhammer (b - of_nat n + 1) k = setprod (%i. b - of_nat i) {0.. n - k - 1}" 
          using nz' by (simp add: field_simps)
        have "(?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k) = ((?m1 k * ?p (of_nat n) k) / ?f n) * ((?m1 n * ?p b n)/pochhammer (b - of_nat n + 1) k)"
          using bnz0
          by (simp add: field_simps)
        also have "\<dots> = b gchoose (n - k)" 
          unfolding th1 th2
          using kn' by (simp add: gbinomial_def)
        finally have "b gchoose (n - k) = (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)" by simp}
      ultimately have "b gchoose (n - k) = (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)"
        by (cases "k =n", auto)}
    ultimately have "b gchoose (n - k) = (?m1 n * ?p b n * ?m1 k * ?p (of_nat n) k) / (?f n * pochhammer (b - of_nat n + 1) k)" "pochhammer (1 + b - of_nat n) k \<noteq> 0 "
      using nz' 
      apply (cases "n=0", auto)
      by (cases "k", auto)}
  note th00 = this
  have "?r = ((a + b) gchoose n) * (of_nat (fact n)/ (?m1 n * pochhammer (- b) n))"
    unfolding gbinomial_pochhammer 
    using bn0 by (auto simp add: field_simps)
  also have "\<dots> = ?l"
    unfolding gbinomial_Vandermonde[symmetric]
    apply (simp add: th00)
    unfolding gbinomial_pochhammer
    using bn0 apply (simp add: setsum_left_distrib setsum_right_distrib field_simps)
    apply (rule setsum_cong2)
    apply (drule th00(2))
    by (simp add: field_simps power_add[symmetric])
  finally show ?thesis by simp
qed 

    
lemma Vandermonde_pochhammer:
   fixes a :: "'a::field_char_0"
  assumes c: "ALL i : {0..< n}. c \<noteq> - of_nat i"
  shows "setsum (%k. (pochhammer a k * pochhammer (- (of_nat n)) k) / (of_nat (fact k) * pochhammer c k)) {0..n} = pochhammer (c - a) n / pochhammer c n"
proof-
  let ?a = "- a"
  let ?b = "c + of_nat n - 1"
  have h: "\<forall> j \<in>{0..< n}. ?b \<noteq> of_nat j" using c
    apply (auto simp add: algebra_simps of_nat_diff)
    apply (erule_tac x= "n - j - 1" in ballE)
    by (auto simp add: of_nat_diff algebra_simps)
  have th0: "pochhammer (- (?a + ?b)) n = (- 1)^n * pochhammer (c - a) n"
    unfolding pochhammer_minus[OF le_refl]
    by (simp add: algebra_simps)
  have th1: "pochhammer (- ?b) n = (- 1)^n * pochhammer c n"
    unfolding pochhammer_minus[OF le_refl]
    by simp
  have nz: "pochhammer c n \<noteq> 0" using c
    by (simp add: pochhammer_eq_0_iff)
  from Vandermonde_pochhammer_lemma[where a = "?a" and b="?b" and n=n, OF h, unfolded th0 th1]
  show ?thesis using nz by (simp add: field_simps setsum_right_distrib)
qed

subsubsection{* Formal trigonometric functions  *}

definition "fps_sin (c::'a::field_char_0) =
  Abs_fps (\<lambda>n. if even n then 0 else (- 1) ^((n - 1) div 2) * c^n /(of_nat (fact n)))"

definition "fps_cos (c::'a::field_char_0) =
  Abs_fps (\<lambda>n. if even n then (- 1) ^ (n div 2) * c^n / (of_nat (fact n)) else 0)"

lemma fps_sin_deriv:
  "fps_deriv (fps_sin c) = fps_const c * fps_cos c"
  (is "?lhs = ?rhs")
proof (rule fps_ext)
  fix n::nat
    {assume en: "even n"
      have "?lhs$n = of_nat (n+1) * (fps_sin c $ (n+1))" by simp
      also have "\<dots> = of_nat (n+1) * ((- 1)^(n div 2) * c^Suc n / of_nat (fact (Suc n)))"
        using en by (simp add: fps_sin_def)
      also have "\<dots> = (- 1)^(n div 2) * c^Suc n * (of_nat (n+1) / (of_nat (Suc n) * of_nat (fact n)))"
        unfolding fact_Suc of_nat_mult
        by (simp add: field_simps del: of_nat_add of_nat_Suc)
      also have "\<dots> = (- 1)^(n div 2) *c^Suc n / of_nat (fact n)"
        by (simp add: field_simps del: of_nat_add of_nat_Suc)
      finally have "?lhs $n = ?rhs$n" using en
        by (simp add: fps_cos_def field_simps power_Suc )}
    then show "?lhs $ n = ?rhs $ n"
      by (cases "even n", simp_all add: fps_deriv_def fps_sin_def fps_cos_def)
qed

lemma fps_cos_deriv:
  "fps_deriv (fps_cos c) = fps_const (- c)* (fps_sin c)"
  (is "?lhs = ?rhs")
proof (rule fps_ext)
  have th0: "\<And>n. - ((- 1::'a) ^ n) = (- 1)^Suc n" by (simp add: power_Suc)
  have th1: "\<And>n. odd n \<Longrightarrow> Suc ((n - 1) div 2) = Suc n div 2"
    by (case_tac n, simp_all)
  fix n::nat
    {assume en: "odd n"
      from en have n0: "n \<noteq>0 " by presburger
      have "?lhs$n = of_nat (n+1) * (fps_cos c $ (n+1))" by simp
      also have "\<dots> = of_nat (n+1) * ((- 1)^((n + 1) div 2) * c^Suc n / of_nat (fact (Suc n)))"
        using en by (simp add: fps_cos_def)
      also have "\<dots> = (- 1)^((n + 1) div 2)*c^Suc n * (of_nat (n+1) / (of_nat (Suc n) * of_nat (fact n)))"
        unfolding fact_Suc of_nat_mult
        by (simp add: field_simps del: of_nat_add of_nat_Suc)
      also have "\<dots> = (- 1)^((n + 1) div 2) * c^Suc n / of_nat (fact n)"
        by (simp add: field_simps del: of_nat_add of_nat_Suc)
      also have "\<dots> = (- ((- 1)^((n - 1) div 2))) * c^Suc n / of_nat (fact n)"
        unfolding th0 unfolding th1[OF en] by simp
      finally have "?lhs $n = ?rhs$n" using en
        by (simp add: fps_sin_def field_simps power_Suc)}
    then show "?lhs $ n = ?rhs $ n"
      by (cases "even n", simp_all add: fps_deriv_def fps_sin_def
        fps_cos_def)
qed

lemma fps_sin_cos_sum_of_squares:
  "fps_cos c ^ 2 + fps_sin c ^ 2 = 1" (is "?lhs = 1")
proof-
  have "fps_deriv ?lhs = 0"
    apply (simp add:  fps_deriv_power fps_sin_deriv fps_cos_deriv power_Suc)
    by (simp add: field_simps fps_const_neg[symmetric] del: fps_const_neg)
  then have "?lhs = fps_const (?lhs $ 0)"
    unfolding fps_deriv_eq_0_iff .
  also have "\<dots> = 1"
    by (auto simp add: fps_eq_iff numeral_2_eq_2 fps_mult_nth fps_cos_def fps_sin_def)
  finally show ?thesis .
qed

lemma divide_eq_iff: "a \<noteq> (0::'a::field) \<Longrightarrow> x / a = y \<longleftrightarrow> x = y * a"
by auto

lemma eq_divide_iff: "a \<noteq> (0::'a::field) \<Longrightarrow> x = y / a \<longleftrightarrow> x * a = y"
by auto

lemma fps_sin_nth_0 [simp]: "fps_sin c $ 0 = 0"
unfolding fps_sin_def by simp

lemma fps_sin_nth_1 [simp]: "fps_sin c $ 1 = c"
unfolding fps_sin_def by simp

lemma fps_sin_nth_add_2:
  "fps_sin c $ (n + 2) = - (c * c * fps_sin c $ n / (of_nat(n+1) * of_nat(n+2)))"
unfolding fps_sin_def
apply (cases n, simp)
apply (simp add: divide_eq_iff eq_divide_iff del: of_nat_Suc fact_Suc)
apply (simp add: of_nat_mult del: of_nat_Suc mult_Suc)
done

lemma fps_cos_nth_0 [simp]: "fps_cos c $ 0 = 1"
unfolding fps_cos_def by simp

lemma fps_cos_nth_1 [simp]: "fps_cos c $ 1 = 0"
unfolding fps_cos_def by simp

lemma fps_cos_nth_add_2:
  "fps_cos c $ (n + 2) = - (c * c * fps_cos c $ n / (of_nat(n+1) * of_nat(n+2)))"
unfolding fps_cos_def
apply (simp add: divide_eq_iff eq_divide_iff del: of_nat_Suc fact_Suc)
apply (simp add: of_nat_mult del: of_nat_Suc mult_Suc)
done

lemma nat_induct2:
  "\<lbrakk>P 0; P 1; \<And>n. P n \<Longrightarrow> P (n + 2)\<rbrakk> \<Longrightarrow> P (n::nat)"
unfolding One_nat_def numeral_2_eq_2
apply (induct n rule: nat_less_induct)
apply (case_tac n, simp)
apply (rename_tac m, case_tac m, simp)
apply (rename_tac k, case_tac k, simp_all)
done

lemma nat_add_1_add_1: "(n::nat) + 1 + 1 = n + 2"
by simp

lemma eq_fps_sin:
  assumes 0: "a $ 0 = 0" and 1: "a $ 1 = c"
  and 2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "a = fps_sin c"
apply (rule fps_ext)
apply (induct_tac n rule: nat_induct2)
apply (simp add: fps_sin_nth_0 0)
apply (simp add: fps_sin_nth_1 1 del: One_nat_def)
apply (rename_tac m, cut_tac f="\<lambda>a. a $ m" in arg_cong [OF 2])
apply (simp add: nat_add_1_add_1 fps_sin_nth_add_2
            del: One_nat_def of_nat_Suc of_nat_add add_2_eq_Suc')
apply (subst minus_divide_left)
apply (subst eq_divide_iff)
apply (simp del: of_nat_add of_nat_Suc)
apply (simp only: mult_ac)
done

lemma eq_fps_cos:
  assumes 0: "a $ 0 = 1" and 1: "a $ 1 = 0"
  and 2: "fps_deriv (fps_deriv a) = - (fps_const c * fps_const c * a)"
  shows "a = fps_cos c"
apply (rule fps_ext)
apply (induct_tac n rule: nat_induct2)
apply (simp add: fps_cos_nth_0 0)
apply (simp add: fps_cos_nth_1 1 del: One_nat_def)
apply (rename_tac m, cut_tac f="\<lambda>a. a $ m" in arg_cong [OF 2])
apply (simp add: nat_add_1_add_1 fps_cos_nth_add_2
            del: One_nat_def of_nat_Suc of_nat_add add_2_eq_Suc')
apply (subst minus_divide_left)
apply (subst eq_divide_iff)
apply (simp del: of_nat_add of_nat_Suc)
apply (simp only: mult_ac)
done

lemma mult_nth_0 [simp]: "(a * b) $ 0 = a $ 0 * b $ 0"
by (simp add: fps_mult_nth)

lemma mult_nth_1 [simp]: "(a * b) $ 1 = a $ 0 * b $ 1 + a $ 1 * b $ 0"
by (simp add: fps_mult_nth)

lemma fps_sin_add:
  "fps_sin (a + b) = fps_sin a * fps_cos b + fps_cos a * fps_sin b"
apply (rule eq_fps_sin [symmetric], simp, simp del: One_nat_def)
apply (simp del: fps_const_neg fps_const_add fps_const_mult
            add: fps_const_add [symmetric] fps_const_neg [symmetric]
                 fps_sin_deriv fps_cos_deriv algebra_simps)
done

lemma fps_cos_add:
  "fps_cos (a + b) = fps_cos a * fps_cos b - fps_sin a * fps_sin b"
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

lemma fps_tan_deriv: "fps_deriv(fps_tan c) = fps_const c/ (fps_cos c ^ 2)"
proof-
  have th0: "fps_cos c $ 0 \<noteq> 0" by (simp add: fps_cos_def)
  show ?thesis
    using fps_sin_cos_sum_of_squares[of c]
    apply (simp add: fps_tan_def fps_divide_deriv[OF th0] fps_sin_deriv fps_cos_deriv add: fps_const_neg[symmetric] field_simps power2_eq_square del: fps_const_neg)
    unfolding right_distrib[symmetric]
    by simp
qed

text {* Connection to E c over the complex numbers --- Euler and De Moivre*}
lemma Eii_sin_cos:
  "E (ii * c) = fps_cos c + fps_const ii * fps_sin c "
  (is "?l = ?r")
proof-
  {fix n::nat
    {assume en: "even n"
      from en obtain m where m: "n = 2*m" 
        unfolding even_mult_two_ex by blast
      
      have "?l $n = ?r$n" 
        by (simp add: m fps_sin_def fps_cos_def power_mult_distrib
          power_mult power_minus)}
    moreover
    {assume on: "odd n"
      from on obtain m where m: "n = 2*m + 1" 
        unfolding odd_nat_equiv_def2 by (auto simp add: nat_mult_2)  
      have "?l $n = ?r$n" 
        by (simp add: m fps_sin_def fps_cos_def power_mult_distrib
          power_mult power_minus)}
    ultimately have "?l $n = ?r$n"  by blast}
  then show ?thesis by (simp add: fps_eq_iff)
qed

lemma E_minus_ii_sin_cos: "E (- (ii * c)) = fps_cos c - fps_const ii * fps_sin c "
  unfolding minus_mult_right Eii_sin_cos by (simp add: fps_sin_even fps_cos_odd)

lemma fps_const_minus: "fps_const (c::'a::group_add) - fps_const d = fps_const (c - d)"
  by (simp add: fps_eq_iff fps_const_def)

lemma fps_number_of_fps_const: "number_of i = fps_const (number_of i :: 'a:: {comm_ring_1, number_ring})"
  apply (subst (2) number_of_eq)
apply(rule int_induct [of _ 0])
apply (simp_all add: number_of_fps_def)
by (simp_all add: fps_const_add[symmetric] fps_const_minus[symmetric])

lemma fps_cos_Eii:
  "fps_cos c = (E (ii * c) + E (- ii * c)) / fps_const 2"
proof-
  have th: "fps_cos c + fps_cos c = fps_cos c * fps_const 2" 
    by (simp add: fps_eq_iff fps_number_of_fps_const complex_number_of_def[symmetric])
  show ?thesis
  unfolding Eii_sin_cos minus_mult_commute
  by (simp add: fps_sin_even fps_cos_odd fps_number_of_fps_const
    fps_divide_def fps_const_inverse th complex_number_of_def[symmetric])
qed

lemma fps_sin_Eii:
  "fps_sin c = (E (ii * c) - E (- ii * c)) / fps_const (2*ii)"
proof-
  have th: "fps_const \<i> * fps_sin c + fps_const \<i> * fps_sin c = fps_sin c * fps_const (2 * ii)" 
    by (simp add: fps_eq_iff fps_number_of_fps_const complex_number_of_def[symmetric])
  show ?thesis
  unfolding Eii_sin_cos minus_mult_commute
  by (simp add: fps_sin_even fps_cos_odd fps_divide_def fps_const_inverse th)
qed

lemma fps_tan_Eii:
  "fps_tan c = (E (ii * c) - E (- ii * c)) / (fps_const ii * (E (ii * c) + E (- ii * c)))"
  unfolding fps_tan_def fps_sin_Eii fps_cos_Eii mult_minus_left E_neg
  apply (simp add: fps_divide_def fps_inverse_mult fps_const_mult[symmetric] fps_const_inverse del: fps_const_mult)
  by simp

lemma fps_demoivre: "(fps_cos a + fps_const ii * fps_sin a)^n = fps_cos (of_nat n * a) + fps_const ii * fps_sin (of_nat n * a)"
  unfolding Eii_sin_cos[symmetric] E_power_mult
  by (simp add: mult_ac)

subsection {* Hypergeometric series *}


definition "F as bs (c::'a::{field_char_0, field_inverse_zero}) = Abs_fps (%n. (foldl (%r a. r* pochhammer a n) 1 as * c^n)/ (foldl (%r b. r * pochhammer b n) 1 bs * of_nat (fact n)))"

lemma F_nth[simp]: "F as bs c $ n =  (foldl (%r a. r* pochhammer a n) 1 as * c^n)/ (foldl (%r b. r * pochhammer b n) 1 bs * of_nat (fact n))"
  by (simp add: F_def)

lemma foldl_mult_start:
  "foldl (%r x. r * f x) (v::'a::comm_ring_1) as * x = foldl (%r x. r * f x) (v * x) as "
  by (induct as arbitrary: x v, auto simp add: algebra_simps)

lemma foldr_mult_foldl: "foldr (%x r. r * f x) as v = foldl (%r x. r * f x) (v :: 'a::comm_ring_1) as"
  by (induct as arbitrary: v, auto simp add: foldl_mult_start)

lemma F_nth_alt: "F as bs c $ n = foldr (\<lambda>a r. r * pochhammer a n) as (c ^ n) /
    foldr (\<lambda>b r. r * pochhammer b n) bs (of_nat (fact n))"
  by (simp add: foldl_mult_start foldr_mult_foldl)

lemma F_E[simp]: "F [] [] c = E c" 
  by (simp add: fps_eq_iff)

lemma F_1_0[simp]: "F [1] [] c = 1/(1 - fps_const c * X)"
proof-
  let ?a = "(Abs_fps (\<lambda>n. 1)) oo (fps_const c * X)"
  have th0: "(fps_const c * X) $ 0 = 0" by simp
  show ?thesis unfolding gp[OF th0, symmetric]
    by (auto simp add: fps_eq_iff pochhammer_fact[symmetric] fps_compose_nth power_mult_distrib cond_value_iff setsum_delta' cong del: if_weak_cong)
qed

lemma F_B[simp]: "F [-a] [] (- 1) = fps_binomial a"
  by (simp add: fps_eq_iff gbinomial_pochhammer algebra_simps)

lemma F_0[simp]: "F as bs c $0 = 1"
  apply simp
  apply (subgoal_tac "ALL as. foldl (%(r::'a) (a::'a). r) 1 as = 1")
  apply auto
  apply (induct_tac as, auto)
  done

lemma foldl_prod_prod: "foldl (%(r::'b::comm_ring_1) (x::'a::comm_ring_1). r * f x) v as * foldl (%r x. r * g x) w as = foldl (%r x. r * f x * g x) (v*w) as"
  by (induct as arbitrary: v w, auto simp add: algebra_simps)


lemma F_rec: "F as bs c $ Suc n = ((foldl (%r a. r* (a + of_nat n)) c as)/ (foldl (%r b. r * (b + of_nat n)) (of_nat (Suc n)) bs )) * F as bs c $ n"
  apply (simp del: of_nat_Suc of_nat_add fact_Suc)
  apply (simp add: foldl_mult_start del: fact_Suc of_nat_Suc)
  unfolding foldl_prod_prod[unfolded foldl_mult_start] pochhammer_Suc
  by (simp add: algebra_simps of_nat_mult)

lemma XD_nth[simp]: "XD a $ n = (if n=0 then 0 else of_nat n * a$n)"
  by (simp add: XD_def)

lemma XD_0th[simp]: "XD a $ 0 = 0" by simp
lemma XD_Suc[simp]:" XD a $ Suc n = of_nat (Suc n) * a $ Suc n" by simp

definition "XDp c a = XD a + fps_const c * a"

lemma XDp_nth[simp]: "XDp c a $ n = (c + of_nat n) * a$n"
  by (simp add: XDp_def algebra_simps)

lemma XDp_commute:
  shows "XDp b o XDp (c::'a::comm_ring_1) = XDp c o XDp b"
  by (auto simp add: XDp_def fun_eq_iff fps_eq_iff algebra_simps)

lemma XDp0[simp]: "XDp 0 = XD"
  by (simp add: fun_eq_iff fps_eq_iff)

lemma XDp_fps_integral[simp]:"XDp 0 (fps_integral a c) = X * a"
  by (simp add: fps_eq_iff fps_integral_def)

lemma F_minus_nat: 
  "F [- of_nat n] [- of_nat (n + m)] (c::'a::{field_char_0, field_inverse_zero}) $ k = (if k <= n then pochhammer (- of_nat n) k * c ^ k /
    (pochhammer (- of_nat (n + m)) k * of_nat (fact k)) else 0)"
  "F [- of_nat m] [- of_nat (m + n)] (c::'a::{field_char_0, field_inverse_zero}) $ k = (if k <= m then pochhammer (- of_nat m) k * c ^ k /
    (pochhammer (- of_nat (m + n)) k * of_nat (fact k)) else 0)"
  by (auto simp add: pochhammer_eq_0_iff)

lemma setsum_eq_if: "setsum f {(n::nat) .. m} = (if m < n then 0 else f n + setsum f {n+1 .. m})"
  apply simp
  apply (subst setsum_insert[symmetric])
  by (auto simp add: not_less setsum_head_Suc)

lemma pochhammer_rec_if: 
  "pochhammer a n = (if n = 0 then 1 else a * pochhammer (a + 1) (n - 1))"
  by (cases n, simp_all add: pochhammer_rec)

lemma XDp_foldr_nth[simp]: "foldr (%c r. XDp c o r) cs (%c. XDp c a) c0 $ n = 
  foldr (%c r. (c + of_nat n) * r) cs (c0 + of_nat n) * a$n"
  by (induct cs arbitrary: c0, auto simp add: algebra_simps)

lemma genric_XDp_foldr_nth:
  assumes 
  f: "ALL n c a. f c a $ n = (of_nat n + k c) * a$n"

  shows "foldr (%c r. f c o r) cs (%c. g c a) c0 $ n = 
  foldr (%c r. (k c + of_nat n) * r) cs (g c0 a $ n)"
  by (induct cs arbitrary: c0, auto simp add: algebra_simps f)

end

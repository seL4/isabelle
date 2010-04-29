(*  Title:      Library/Multivariate_Analysis/Euclidean_Space.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* (Real) Vectors in Euclidean space, and elementary linear algebra.*}

theory Euclidean_Space
imports
  Complex_Main "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
  Finite_Cartesian_Product Infinite_Set Numeral_Type
  Inner_Product L2_Norm
uses "positivstellensatz.ML" ("normarith.ML")
begin

subsection{* Basic componentwise operations on vectors. *}

instantiation cart :: (times,finite) times
begin
  definition vector_mult_def : "op * \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) * (y$i)))"
  instance ..
end

instantiation cart :: (one,finite) one
begin
  definition vector_one_def : "1 \<equiv> (\<chi> i. 1)"
  instance ..
end

instantiation cart :: (ord,finite) ord
begin
  definition vector_le_def:
    "less_eq (x :: 'a ^'b) y = (ALL i. x$i <= y$i)"
  definition vector_less_def: "less (x :: 'a ^'b) y = (ALL i. x$i < y$i)"
  instance by (intro_classes)
end

text{* The ordering on one-dimensional vectors is linear. *}

class cart_one = assumes UNIV_one: "card (UNIV \<Colon> 'a set) = Suc 0"
begin
  subclass finite
  proof from UNIV_one show "finite (UNIV :: 'a set)"
      by (auto intro!: card_ge_0_finite) qed
end

instantiation cart :: (linorder,cart_one) linorder begin
instance proof
  guess a B using UNIV_one[where 'a='b] unfolding card_Suc_eq apply- by(erule exE)+
  hence *:"UNIV = {a}" by auto
  have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P a" unfolding * by auto hence all:"\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a" by auto
  fix x y z::"'a^'b::cart_one" note * = vector_le_def vector_less_def all Cart_eq
  show "x\<le>x" "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" "x\<le>y \<or> y\<le>x" unfolding * by(auto simp only:field_simps)
  { assume "x\<le>y" "y\<le>z" thus "x\<le>z" unfolding * by(auto simp only:field_simps) }
  { assume "x\<le>y" "y\<le>x" thus "x=y" unfolding * by(auto simp only:field_simps) }
qed end

text{* Also the scalar-vector multiplication. *}

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"

text{* Constant Vectors *} 

definition "vec x = (\<chi> i. x)"

subsection {* A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space. *}

method_setup vector = {*
let
  val ss1 = HOL_basic_ss addsimps [@{thm setsum_addf} RS sym,
  @{thm setsum_subtractf} RS sym, @{thm setsum_right_distrib},
  @{thm setsum_left_distrib}, @{thm setsum_negf} RS sym]
  val ss2 = @{simpset} addsimps
             [@{thm vector_add_def}, @{thm vector_mult_def},
              @{thm vector_minus_def}, @{thm vector_uminus_def},
              @{thm vector_one_def}, @{thm vector_zero_def}, @{thm vec_def},
              @{thm vector_scaleR_def},
              @{thm Cart_lambda_beta}, @{thm vector_scalar_mult_def}]
 fun vector_arith_tac ths =
   simp_tac ss1
   THEN' (fn i => rtac @{thm setsum_cong2} i
         ORELSE rtac @{thm setsum_0'} i
         ORELSE simp_tac (HOL_basic_ss addsimps [@{thm "Cart_eq"}]) i)
   (* THEN' TRY o clarify_tac HOL_cs  THEN' (TRY o rtac @{thm iffI}) *)
   THEN' asm_full_simp_tac (ss2 addsimps ths)
 in
  Attrib.thms >> (fn ths => K (SIMPLE_METHOD' (vector_arith_tac ths)))
 end
*} "Lifts trivial vector statements to real arith statements"

lemma vec_0[simp]: "vec 0 = 0" by (vector vector_zero_def)
lemma vec_1[simp]: "vec 1 = 1" by (vector vector_one_def)

text{* Obvious "component-pushing". *}

lemma vec_component [simp]: "vec x $ i = x"
  by (vector vec_def)

lemma vector_mult_component [simp]: "(x * y)$i = x$i * y$i"
  by vector

lemma vector_smult_component [simp]: "(c *s y)$i = c * (y$i)"
  by vector

lemma cond_component: "(if b then x else y)$i = (if b then x$i else y$i)" by vector

lemmas vector_component =
  vec_component vector_add_component vector_mult_component
  vector_smult_component vector_minus_component vector_uminus_component
  vector_scaleR_component cond_component

subsection {* Some frequently useful arithmetic lemmas over vectors. *}

instance cart :: (semigroup_mult,finite) semigroup_mult
  apply (intro_classes) by (vector mult_assoc)

instance cart :: (monoid_mult,finite) monoid_mult
  apply (intro_classes) by vector+

instance cart :: (ab_semigroup_mult,finite) ab_semigroup_mult
  apply (intro_classes) by (vector mult_commute)

instance cart :: (ab_semigroup_idem_mult,finite) ab_semigroup_idem_mult
  apply (intro_classes) by (vector mult_idem)

instance cart :: (comm_monoid_mult,finite) comm_monoid_mult
  apply (intro_classes) by vector

instance cart :: (semiring,finite) semiring
  apply (intro_classes) by (vector field_simps)+

instance cart :: (semiring_0,finite) semiring_0
  apply (intro_classes) by (vector field_simps)+
instance cart :: (semiring_1,finite) semiring_1
  apply (intro_classes) by vector
instance cart :: (comm_semiring,finite) comm_semiring
  apply (intro_classes) by (vector field_simps)+

instance cart :: (comm_semiring_0,finite) comm_semiring_0 by (intro_classes)
instance cart :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..
instance cart :: (semiring_0_cancel,finite) semiring_0_cancel by (intro_classes)
instance cart :: (comm_semiring_0_cancel,finite) comm_semiring_0_cancel by (intro_classes)
instance cart :: (ring,finite) ring by (intro_classes)
instance cart :: (semiring_1_cancel,finite) semiring_1_cancel by (intro_classes)
instance cart :: (comm_semiring_1,finite) comm_semiring_1 by (intro_classes)

instance cart :: (ring_1,finite) ring_1 ..

instance cart :: (real_algebra,finite) real_algebra
  apply intro_classes
  apply (simp_all add: vector_scaleR_def field_simps)
  apply vector
  apply vector
  done

instance cart :: (real_algebra_1,finite) real_algebra_1 ..

lemma of_nat_index:
  "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
  apply (induct n)
  apply vector
  apply vector
  done

lemma one_index[simp]:
  "(1 :: 'a::one ^'n)$i = 1" by vector

instance cart :: (semiring_char_0,finite) semiring_char_0
proof (intro_classes)
  fix m n ::nat
  show "(of_nat m :: 'a^'b) = of_nat n \<longleftrightarrow> m = n"
    by (simp add: Cart_eq of_nat_index)
qed

instance cart :: (comm_ring_1,finite) comm_ring_1 by intro_classes
instance cart :: (ring_char_0,finite) ring_char_0 by intro_classes

lemma vector_smult_assoc: "a *s (b *s x) = ((a::'a::semigroup_mult) * b) *s x"
  by (vector mult_assoc)
lemma vector_sadd_rdistrib: "((a::'a::semiring) + b) *s x = a *s x + b *s x"
  by (vector field_simps)
lemma vector_add_ldistrib: "(c::'a::semiring) *s (x + y) = c *s x + c *s y"
  by (vector field_simps)
lemma vector_smult_lzero[simp]: "(0::'a::mult_zero) *s x = 0" by vector
lemma vector_smult_lid[simp]: "(1::'a::monoid_mult) *s x = x" by vector
lemma vector_ssub_ldistrib: "(c::'a::ring) *s (x - y) = c *s x - c *s y"
  by (vector field_simps)
lemma vector_smult_rneg: "(c::'a::ring) *s -x = -(c *s x)" by vector
lemma vector_smult_lneg: "- (c::'a::ring) *s x = -(c *s x)" by vector
lemma vector_sneg_minus1: "-x = (- (1::'a::ring_1)) *s x" by vector
lemma vector_smult_rzero[simp]: "c *s 0 = (0::'a::mult_zero ^ 'n)" by vector
lemma vector_sub_rdistrib: "((a::'a::ring) - b) *s x = a *s x - b *s x"
  by (vector field_simps)

lemma vec_eq[simp]: "(vec m = vec n) \<longleftrightarrow> (m = n)"
  by (simp add: Cart_eq)

abbreviation inner_bullet (infix "\<bullet>" 70)  where "x \<bullet> y \<equiv> inner x y"

subsection {* A connectedness or intermediate value lemma with several applications. *}

lemma connected_real_lemma:
  fixes f :: "real \<Rightarrow> 'a::metric_space"
  assumes ab: "a \<le> b" and fa: "f a \<in> e1" and fb: "f b \<in> e2"
  and dst: "\<And>e x. a <= x \<Longrightarrow> x <= b \<Longrightarrow> 0 < e ==> \<exists>d > 0. \<forall>y. abs(y - x) < d \<longrightarrow> dist(f y) (f x) < e"
  and e1: "\<forall>y \<in> e1. \<exists>e > 0. \<forall>y'. dist y' y < e \<longrightarrow> y' \<in> e1"
  and e2: "\<forall>y \<in> e2. \<exists>e > 0. \<forall>y'. dist y' y < e \<longrightarrow> y' \<in> e2"
  and e12: "~(\<exists>x \<ge> a. x <= b \<and> f x \<in> e1 \<and> f x \<in> e2)"
  shows "\<exists>x \<ge> a. x <= b \<and> f x \<notin> e1 \<and> f x \<notin> e2" (is "\<exists> x. ?P x")
proof-
  let ?S = "{c. \<forall>x \<ge> a. x <= c \<longrightarrow> f x \<in> e1}"
  have Se: " \<exists>x. x \<in> ?S" apply (rule exI[where x=a]) by (auto simp add: fa)
  have Sub: "\<exists>y. isUb UNIV ?S y"
    apply (rule exI[where x= b])
    using ab fb e12 by (auto simp add: isUb_def setle_def)
  from reals_complete[OF Se Sub] obtain l where
    l: "isLub UNIV ?S l"by blast
  have alb: "a \<le> l" "l \<le> b" using l ab fa fb e12
    apply (auto simp add: isLub_def leastP_def isUb_def setle_def setge_def)
    by (metis linorder_linear)
  have ale1: "\<forall>z \<ge> a. z < l \<longrightarrow> f z \<in> e1" using l
    apply (auto simp add: isLub_def leastP_def isUb_def setle_def setge_def)
    by (metis linorder_linear not_le)
    have th1: "\<And>z x e d :: real. z <= x + e \<Longrightarrow> e < d ==> z < x \<or> abs(z - x) < d" by arith
    have th2: "\<And>e x:: real. 0 < e ==> ~(x + e <= x)" by arith
    have th3: "\<And>d::real. d > 0 \<Longrightarrow> \<exists>e > 0. e < d" by dlo
    {assume le2: "f l \<in> e2"
      from le2 fa fb e12 alb have la: "l \<noteq> a" by metis
      hence lap: "l - a > 0" using alb by arith
      from e2[rule_format, OF le2] obtain e where
        e: "e > 0" "\<forall>y. dist y (f l) < e \<longrightarrow> y \<in> e2" by metis
      from dst[OF alb e(1)] obtain d where
        d: "d > 0" "\<forall>y. \<bar>y - l\<bar> < d \<longrightarrow> dist (f y) (f l) < e" by metis
      have "\<exists>d'. d' < d \<and> d' >0 \<and> l - d' > a" using lap d(1)
        apply ferrack by arith
      then obtain d' where d': "d' > 0" "d' < d" "l - d' > a" by metis
      from d e have th0: "\<forall>y. \<bar>y - l\<bar> < d \<longrightarrow> f y \<in> e2" by metis
      from th0[rule_format, of "l - d'"] d' have "f (l - d') \<in> e2" by auto
      moreover
      have "f (l - d') \<in> e1" using ale1[rule_format, of "l -d'"] d' by auto
      ultimately have False using e12 alb d' by auto}
    moreover
    {assume le1: "f l \<in> e1"
    from le1 fa fb e12 alb have lb: "l \<noteq> b" by metis
      hence blp: "b - l > 0" using alb by arith
      from e1[rule_format, OF le1] obtain e where
        e: "e > 0" "\<forall>y. dist y (f l) < e \<longrightarrow> y \<in> e1" by metis
      from dst[OF alb e(1)] obtain d where
        d: "d > 0" "\<forall>y. \<bar>y - l\<bar> < d \<longrightarrow> dist (f y) (f l) < e" by metis
      have "\<exists>d'. d' < d \<and> d' >0" using d(1) by dlo
      then obtain d' where d': "d' > 0" "d' < d" by metis
      from d e have th0: "\<forall>y. \<bar>y - l\<bar> < d \<longrightarrow> f y \<in> e1" by auto
      hence "\<forall>y. l \<le> y \<and> y \<le> l + d' \<longrightarrow> f y \<in> e1" using d' by auto
      with ale1 have "\<forall>y. a \<le> y \<and> y \<le> l + d' \<longrightarrow> f y \<in> e1" by auto
      with l d' have False
        by (auto simp add: isLub_def isUb_def setle_def setge_def leastP_def) }
    ultimately show ?thesis using alb by metis
qed

text{* One immediately useful corollary is the existence of square roots! --- Should help to get rid of all the development of square-root for reals as a special case *}

lemma square_bound_lemma: "(x::real) < (1 + x) * (1 + x)"
proof-
  have "(x + 1/2)^2 + 3/4 > 0" using zero_le_power2[of "x+1/2"] by arith
  thus ?thesis by (simp add: field_simps power2_eq_square)
qed

lemma square_continuous: "0 < (e::real) ==> \<exists>d. 0 < d \<and> (\<forall>y. abs(y - x) < d \<longrightarrow> abs(y * y - x * x) < e)"
  using isCont_power[OF isCont_ident, of 2, unfolded isCont_def LIM_eq, rule_format, of e x] apply (auto simp add: power2_eq_square)
  apply (rule_tac x="s" in exI)
  apply auto
  apply (erule_tac x=y in allE)
  apply auto
  done

lemma real_le_lsqrt: "0 <= x \<Longrightarrow> 0 <= y \<Longrightarrow> x <= y^2 ==> sqrt x <= y"
  using real_sqrt_le_iff[of x "y^2"] by simp

lemma real_le_rsqrt: "x^2 \<le> y \<Longrightarrow> x \<le> sqrt y"
  using real_sqrt_le_mono[of "x^2" y] by simp

lemma real_less_rsqrt: "x^2 < y \<Longrightarrow> x < sqrt y"
  using real_sqrt_less_mono[of "x^2" y] by simp

lemma sqrt_even_pow2: assumes n: "even n"
  shows "sqrt(2 ^ n) = 2 ^ (n div 2)"
proof-
  from n obtain m where m: "n = 2*m" unfolding even_mult_two_ex ..
  from m  have "sqrt(2 ^ n) = sqrt ((2 ^ m) ^ 2)"
    by (simp only: power_mult[symmetric] mult_commute)
  then show ?thesis  using m by simp
qed

lemma real_div_sqrt: "0 <= x ==> x / sqrt(x) = sqrt(x)"
  apply (cases "x = 0", simp_all)
  using sqrt_divide_self_eq[of x]
  apply (simp add: inverse_eq_divide field_simps)
  done

text{* Hence derive more interesting properties of the norm. *}

lemma norm_mul[simp]: "norm(a *s x) = abs(a) * norm x"
  by (simp add: norm_vector_def setL2_right_distrib abs_mult)

lemma norm_eq_0_dot: "(norm x = 0) \<longleftrightarrow> (inner x x = (0::real))"
  by (simp add: norm_vector_def setL2_def power2_eq_square)
lemma norm_eq_0_imp: "norm x = 0 ==> x = (0::real ^'n)" by (metis norm_eq_zero)
lemma vector_mul_eq_0[simp]: "(a *s x = 0) \<longleftrightarrow> a = (0::'a::idom) \<or> x = 0"
  by vector
lemma vector_mul_lcancel[simp]: "a *s x = a *s y \<longleftrightarrow> a = (0::real) \<or> x = y"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_ssub_ldistrib)
lemma vector_mul_rcancel[simp]: "a *s x = b *s x \<longleftrightarrow> (a::real) = b \<or> x = 0"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_sub_rdistrib)
lemma vector_mul_lcancel_imp: "a \<noteq> (0::real) ==>  a *s x = a *s y ==> (x = y)"
  by (metis vector_mul_lcancel)
lemma vector_mul_rcancel_imp: "x \<noteq> 0 \<Longrightarrow> (a::real) *s x = b *s x ==> a = b"
  by (metis vector_mul_rcancel)

lemma norm_cauchy_schwarz:
  shows "inner x y <= norm x * norm y"
  using Cauchy_Schwarz_ineq2[of x y] by auto

lemma norm_cauchy_schwarz_abs:
  shows "\<bar>inner x y\<bar> \<le> norm x * norm y"
  by (rule Cauchy_Schwarz_ineq2)

lemma norm_triangle_sub:
  fixes x y :: "'a::real_normed_vector"
  shows "norm x \<le> norm y  + norm (x - y)"
  using norm_triangle_ineq[of "y" "x - y"] by (simp add: field_simps)

lemma component_le_norm: "\<bar>x$i\<bar> <= norm x"
  apply (simp add: norm_vector_def)
  apply (rule member_le_setL2, simp_all)
  done

lemma norm_bound_component_le: "norm x <= e ==> \<bar>x$i\<bar> <= e"
  by (metis component_le_norm order_trans)

lemma norm_bound_component_lt: "norm x < e ==> \<bar>x$i\<bar> < e"
  by (metis component_le_norm basic_trans_rules(21))

lemma norm_le_l1: "norm x <= setsum(\<lambda>i. \<bar>x$i\<bar>) UNIV"
  by (simp add: norm_vector_def setL2_le_setsum)

lemma real_abs_norm: "\<bar>norm x\<bar> = norm x"
  by (rule abs_norm_cancel)
lemma real_abs_sub_norm: "\<bar>norm x - norm y\<bar> <= norm(x - y)"
  by (rule norm_triangle_ineq3)
lemma norm_le: "norm(x) <= norm(y) \<longleftrightarrow> x \<bullet> x <= y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner) 
lemma norm_lt: "norm(x) < norm(y) \<longleftrightarrow> x \<bullet> x < y \<bullet> y"
  by (simp add: norm_eq_sqrt_inner)
lemma norm_eq: "norm(x) = norm (y) \<longleftrightarrow> x \<bullet> x = y \<bullet> y"
  apply(subst order_eq_iff) unfolding norm_le by auto
lemma norm_eq_1: "norm(x) = 1 \<longleftrightarrow> x \<bullet> x = 1"
  unfolding norm_eq_sqrt_inner by auto

text{* Squaring equations and inequalities involving norms.  *}

lemma dot_square_norm: "x \<bullet> x = norm(x)^2"
  by (simp add: norm_eq_sqrt_inner)

lemma norm_eq_square: "norm(x) = a \<longleftrightarrow> 0 <= a \<and> x \<bullet> x = a^2"
  by (auto simp add: norm_eq_sqrt_inner)

lemma real_abs_le_square_iff: "\<bar>x\<bar> \<le> \<bar>y\<bar> \<longleftrightarrow> (x::real)^2 \<le> y^2"
proof
  assume "\<bar>x\<bar> \<le> \<bar>y\<bar>"
  then have "\<bar>x\<bar>\<twosuperior> \<le> \<bar>y\<bar>\<twosuperior>" by (rule power_mono, simp)
  then show "x\<twosuperior> \<le> y\<twosuperior>" by simp
next
  assume "x\<twosuperior> \<le> y\<twosuperior>"
  then have "sqrt (x\<twosuperior>) \<le> sqrt (y\<twosuperior>)" by (rule real_sqrt_le_mono)
  then show "\<bar>x\<bar> \<le> \<bar>y\<bar>" by simp
qed

lemma norm_le_square: "norm(x) <= a \<longleftrightarrow> 0 <= a \<and> x \<bullet> x <= a^2"
  apply (simp add: dot_square_norm real_abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_ge_square: "norm(x) >= a \<longleftrightarrow> a <= 0 \<or> x \<bullet> x >= a ^ 2"
  apply (simp add: dot_square_norm real_abs_le_square_iff[symmetric])
  using norm_ge_zero[of x]
  apply arith
  done

lemma norm_lt_square: "norm(x) < a \<longleftrightarrow> 0 < a \<and> x \<bullet> x < a^2"
  by (metis not_le norm_ge_square)
lemma norm_gt_square: "norm(x) > a \<longleftrightarrow> a < 0 \<or> x \<bullet> x > a^2"
  by (metis norm_le_square not_less)

text{* Dot product in terms of the norm rather than conversely. *}

lemmas inner_simps = inner.add_left inner.add_right inner.diff_right inner.diff_left 
inner.scaleR_left inner.scaleR_right

lemma dot_norm: "x \<bullet> y = (norm(x + y) ^2 - norm x ^ 2 - norm y ^ 2) / 2"
  unfolding power2_norm_eq_inner inner_simps inner_commute by auto 

lemma dot_norm_neg: "x \<bullet> y = ((norm x ^ 2 + norm y ^ 2) - norm(x - y) ^ 2) / 2"
  unfolding power2_norm_eq_inner inner_simps inner_commute by(auto simp add:algebra_simps)

text{* Equality of vectors in terms of @{term "op \<bullet>"} products.    *}

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs by simp
next
  assume ?rhs
  then have "x \<bullet> x - x \<bullet> y = 0 \<and> x \<bullet> y - y \<bullet> y = 0" by simp
  hence "x \<bullet> (x - y) = 0 \<and> y \<bullet> (x - y) = 0" by (simp add: inner_simps inner_commute)
  then have "(x - y) \<bullet> (x - y) = 0" by (simp add: field_simps inner_simps inner_commute)
  then show "x = y" by (simp)
qed

subsection{* General linear decision procedure for normed spaces. *}

lemma norm_cmul_rule_thm:
  fixes x :: "'a::real_normed_vector"
  shows "b >= norm(x) ==> \<bar>c\<bar> * b >= norm(scaleR c x)"
  unfolding norm_scaleR
  apply (erule mult_mono1)
  apply simp
  done

  (* FIXME: Move all these theorems into the ML code using lemma antiquotation *)
lemma norm_add_rule_thm:
  fixes x1 x2 :: "'a::real_normed_vector"
  shows "norm x1 \<le> b1 \<Longrightarrow> norm x2 \<le> b2 \<Longrightarrow> norm (x1 + x2) \<le> b1 + b2"
  by (rule order_trans [OF norm_triangle_ineq add_mono])

lemma ge_iff_diff_ge_0: "(a::'a::linordered_ring) \<ge> b == a - b \<ge> 0"
  by (simp add: field_simps)

lemma pth_1:
  fixes x :: "'a::real_normed_vector"
  shows "x == scaleR 1 x" by simp

lemma pth_2:
  fixes x :: "'a::real_normed_vector"
  shows "x - y == x + -y" by (atomize (full)) simp

lemma pth_3:
  fixes x :: "'a::real_normed_vector"
  shows "- x == scaleR (-1) x" by simp

lemma pth_4:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR 0 x == 0" and "scaleR c 0 = (0::'a)" by simp_all

lemma pth_5:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c (scaleR d x) == scaleR (c * d) x" by simp

lemma pth_6:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c (x + y) == scaleR c x + scaleR c y"
  by (simp add: scaleR_right_distrib)

lemma pth_7:
  fixes x :: "'a::real_normed_vector"
  shows "0 + x == x" and "x + 0 == x" by simp_all

lemma pth_8:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR c x + scaleR d x == scaleR (c + d) x"
  by (simp add: scaleR_left_distrib)

lemma pth_9:
  fixes x :: "'a::real_normed_vector" shows
  "(scaleR c x + z) + scaleR d x == scaleR (c + d) x + z"
  "scaleR c x + (scaleR d x + z) == scaleR (c + d) x + z"
  "(scaleR c x + w) + (scaleR d x + z) == scaleR (c + d) x + (w + z)"
  by (simp_all add: algebra_simps)

lemma pth_a:
  fixes x :: "'a::real_normed_vector"
  shows "scaleR 0 x + y == y" by simp

lemma pth_b:
  fixes x :: "'a::real_normed_vector" shows
  "scaleR c x + scaleR d y == scaleR c x + scaleR d y"
  "(scaleR c x + z) + scaleR d y == scaleR c x + (z + scaleR d y)"
  "scaleR c x + (scaleR d y + z) == scaleR c x + (scaleR d y + z)"
  "(scaleR c x + w) + (scaleR d y + z) == scaleR c x + (w + (scaleR d y + z))"
  by (simp_all add: algebra_simps)

lemma pth_c:
  fixes x :: "'a::real_normed_vector" shows
  "scaleR c x + scaleR d y == scaleR d y + scaleR c x"
  "(scaleR c x + z) + scaleR d y == scaleR d y + (scaleR c x + z)"
  "scaleR c x + (scaleR d y + z) == scaleR d y + (scaleR c x + z)"
  "(scaleR c x + w) + (scaleR d y + z) == scaleR d y + ((scaleR c x + w) + z)"
  by (simp_all add: algebra_simps)

lemma pth_d:
  fixes x :: "'a::real_normed_vector"
  shows "x + 0 == x" by simp

lemma norm_imp_pos_and_ge:
  fixes x :: "'a::real_normed_vector"
  shows "norm x == n \<Longrightarrow> norm x \<ge> 0 \<and> n \<ge> norm x"
  by atomize auto

lemma real_eq_0_iff_le_ge_0: "(x::real) = 0 == x \<ge> 0 \<and> -x \<ge> 0" by arith

lemma norm_pths:
  fixes x :: "'a::real_normed_vector" shows
  "x = y \<longleftrightarrow> norm (x - y) \<le> 0"
  "x \<noteq> y \<longleftrightarrow> \<not> (norm (x - y) \<le> 0)"
  using norm_ge_zero[of "x - y"] by auto

use "normarith.ML"

method_setup norm = {* Scan.succeed (SIMPLE_METHOD' o NormArith.norm_arith_tac)
*} "Proves simple linear statements about vector norms"


text{* Hence more metric properties. *}

lemma dist_triangle_alt:
  fixes x y z :: "'a::metric_space"
  shows "dist y z <= dist x y + dist x z"
by (rule dist_triangle3)

lemma dist_pos_lt:
  fixes x y :: "'a::metric_space"
  shows "x \<noteq> y ==> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_nz:
  fixes x y :: "'a::metric_space"
  shows "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_triangle_le:
  fixes x y z :: "'a::metric_space"
  shows "dist x z + dist y z <= e \<Longrightarrow> dist x y <= e"
by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt:
  fixes x y z :: "'a::metric_space"
  shows "dist x z + dist y z < e ==> dist x y < e"
by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_half_l:
  fixes x1 x2 y :: "'a::metric_space"
  shows "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_lt [where z=y], simp)

lemma dist_triangle_half_r:
  fixes x1 x2 y :: "'a::metric_space"
  shows "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_half_l, simp_all add: dist_commute)


lemma norm_triangle_half_r:
  shows "norm (y - x1) < e / 2 \<Longrightarrow> norm (y - x2) < e / 2 \<Longrightarrow> norm (x1 - x2) < e"
  using dist_triangle_half_r unfolding dist_norm[THEN sym] by auto

lemma norm_triangle_half_l: assumes "norm (x - y) < e / 2" "norm (x' - (y)) < e / 2" 
  shows "norm (x - x') < e"
  using dist_triangle_half_l[OF assms[unfolded dist_norm[THEN sym]]]
  unfolding dist_norm[THEN sym] .

lemma norm_triangle_le: "norm(x) + norm y <= e ==> norm(x + y) <= e"
  by (metis order_trans norm_triangle_ineq)

lemma norm_triangle_lt: "norm(x) + norm(y) < e ==> norm(x + y) < e"
  by (metis basic_trans_rules(21) norm_triangle_ineq)

lemma dist_triangle_add:
  fixes x y x' y' :: "'a::real_normed_vector"
  shows "dist (x + y) (x' + y') <= dist x x' + dist y y'"
  by norm

lemma dist_mul[simp]: "dist (c *s x) (c *s y) = \<bar>c\<bar> * dist x y"
  unfolding dist_norm vector_ssub_ldistrib[symmetric] norm_mul ..

lemma dist_triangle_add_half:
  fixes x x' y y' :: "'a::real_normed_vector"
  shows "dist x x' < e / 2 \<Longrightarrow> dist y y' < e / 2 \<Longrightarrow> dist(x + y) (x' + y') < e"
  by norm

lemma setsum_component [simp]:
  fixes f:: " 'a \<Rightarrow> ('b::comm_monoid_add) ^'n"
  shows "(setsum f S)$i = setsum (\<lambda>x. (f x)$i) S"
  by (cases "finite S", induct S set: finite, simp_all)

lemma setsum_eq: "setsum f S = (\<chi> i. setsum (\<lambda>x. (f x)$i ) S)"
  by (simp add: Cart_eq)

lemma setsum_clauses:
  shows "setsum f {} = 0"
  and "finite S \<Longrightarrow> setsum f (insert x S) =
                 (if x \<in> S then setsum f S else f x + setsum f S)"
  by (auto simp add: insert_absorb)

lemma setsum_cmul:
  fixes f:: "'c \<Rightarrow> ('a::semiring_1)^'n"
  shows "setsum (\<lambda>x. c *s f x) S = c *s setsum f S"
  by (simp add: Cart_eq setsum_right_distrib)

lemma setsum_norm:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fS: "finite S"
  shows "norm (setsum f S) <= setsum (\<lambda>x. norm(f x)) S"
proof(induct rule: finite_induct[OF fS])
  case 1 thus ?case by simp
next
  case (2 x S)
  from "2.hyps" have "norm (setsum f (insert x S)) \<le> norm (f x) + norm (setsum f S)" by (simp add: norm_triangle_ineq)
  also have "\<dots> \<le> norm (f x) + setsum (\<lambda>x. norm(f x)) S"
    using "2.hyps" by simp
  finally  show ?case  using "2.hyps" by simp
qed

lemma setsum_norm_le:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fS: "finite S"
  and fg: "\<forall>x \<in> S. norm (f x) \<le> g x"
  shows "norm (setsum f S) \<le> setsum g S"
proof-
  from fg have "setsum (\<lambda>x. norm(f x)) S <= setsum g S"
    by - (rule setsum_mono, simp)
  then show ?thesis using setsum_norm[OF fS, of f] fg
    by arith
qed

lemma setsum_norm_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fS: "finite S"
  and K: "\<forall>x \<in> S. norm (f x) \<le> K"
  shows "norm (setsum f S) \<le> of_nat (card S) * K"
  using setsum_norm_le[OF fS K] setsum_constant[symmetric]
  by simp

lemma setsum_vmul:
  fixes f :: "'a \<Rightarrow> 'b::semiring_0"
  assumes fS: "finite S"
  shows "setsum f S *s v = setsum (\<lambda>x. f x *s v) S"
proof(induct rule: finite_induct[OF fS])
  case 1 then show ?case by simp
next
  case (2 x F)
  from "2.hyps" have "setsum f (insert x F) *s v = (f x + setsum f F) *s v"
    by simp
  also have "\<dots> = f x *s v + setsum f F *s v"
    by (simp add: vector_sadd_rdistrib)
  also have "\<dots> = setsum (\<lambda>x. f x *s v) (insert x F)" using "2.hyps" by simp
  finally show ?case .
qed

(* FIXME : Problem thm setsum_vmul[of _ "f:: 'a \<Rightarrow> real ^'n"]  ---
 Get rid of *s and use real_vector instead! Also prove that ^ creates a real_vector !! *)

    (* FIXME: Here too need stupid finiteness assumption on T!!! *)
lemma setsum_group:
  assumes fS: "finite S" and fT: "finite T" and fST: "f ` S \<subseteq> T"
  shows "setsum (\<lambda>y. setsum g {x. x\<in> S \<and> f x = y}) T = setsum g S"

apply (subst setsum_image_gen[OF fS, of g f])
apply (rule setsum_mono_zero_right[OF fT fST])
by (auto intro: setsum_0')

lemma vsum_norm_allsubsets_bound:
  fixes f:: "'a \<Rightarrow> real ^'n"
  assumes fP: "finite P" and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (setsum f Q) \<le> e"
  shows "setsum (\<lambda>x. norm (f x)) P \<le> 2 * real CARD('n) *  e"
proof-
  let ?d = "real CARD('n)"
  let ?nf = "\<lambda>x. norm (f x)"
  let ?U = "UNIV :: 'n set"
  have th0: "setsum (\<lambda>x. setsum (\<lambda>i. \<bar>f x $ i\<bar>) ?U) P = setsum (\<lambda>i. setsum (\<lambda>x. \<bar>f x $ i\<bar>) P) ?U"
    by (rule setsum_commute)
  have th1: "2 * ?d * e = of_nat (card ?U) * (2 * e)" by (simp add: real_of_nat_def)
  have "setsum ?nf P \<le> setsum (\<lambda>x. setsum (\<lambda>i. \<bar>f x $ i\<bar>) ?U) P"
    apply (rule setsum_mono)
    by (rule norm_le_l1)
  also have "\<dots> \<le> 2 * ?d * e"
    unfolding th0 th1
  proof(rule setsum_bounded)
    fix i assume i: "i \<in> ?U"
    let ?Pp = "{x. x\<in> P \<and> f x $ i \<ge> 0}"
    let ?Pn = "{x. x \<in> P \<and> f x $ i < 0}"
    have thp: "P = ?Pp \<union> ?Pn" by auto
    have thp0: "?Pp \<inter> ?Pn ={}" by auto
    have PpP: "?Pp \<subseteq> P" and PnP: "?Pn \<subseteq> P" by blast+
    have Ppe:"setsum (\<lambda>x. \<bar>f x $ i\<bar>) ?Pp \<le> e"
      using component_le_norm[of "setsum (\<lambda>x. f x) ?Pp" i]  fPs[OF PpP]
      by (auto intro: abs_le_D1)
    have Pne: "setsum (\<lambda>x. \<bar>f x $ i\<bar>) ?Pn \<le> e"
      using component_le_norm[of "setsum (\<lambda>x. - f x) ?Pn" i]  fPs[OF PnP]
      by (auto simp add: setsum_negf intro: abs_le_D1)
    have "setsum (\<lambda>x. \<bar>f x $ i\<bar>) P = setsum (\<lambda>x. \<bar>f x $ i\<bar>) ?Pp + setsum (\<lambda>x. \<bar>f x $ i\<bar>) ?Pn"
      apply (subst thp)
      apply (rule setsum_Un_zero)
      using fP thp0 by auto
    also have "\<dots> \<le> 2*e" using Pne Ppe by arith
    finally show "setsum (\<lambda>x. \<bar>f x $ i\<bar>) P \<le> 2*e" .
  qed
  finally show ?thesis .
qed

lemma dot_lsum: "finite S \<Longrightarrow> setsum f S \<bullet> y = setsum (\<lambda>x. f x \<bullet> y) S "
  apply(induct rule: finite_induct) by(auto simp add: inner_simps)

lemma dot_rsum: "finite S \<Longrightarrow> y \<bullet> setsum f S = setsum (\<lambda>x. y \<bullet> f x) S "
  apply(induct rule: finite_induct) by(auto simp add: inner_simps)

subsection{* Basis vectors in coordinate directions. *}

definition "basis k = (\<chi> i. if i = k then 1 else 0)"

lemma basis_component [simp]: "basis k $ i = (if k=i then 1 else 0)"
  unfolding basis_def by simp

lemma delta_mult_idempotent:
  "(if k=a then 1 else (0::'a::semiring_1)) * (if k=a then 1 else 0) = (if k=a then 1 else 0)" by (cases "k=a", auto)

lemma norm_basis:
  shows "norm (basis k :: real ^'n) = 1"
  apply (simp add: basis_def norm_eq_sqrt_inner) unfolding inner_vector_def
  apply (vector delta_mult_idempotent)
  using setsum_delta[of "UNIV :: 'n set" "k" "\<lambda>k. 1::real"] by auto

lemma norm_basis_1: "norm(basis 1 :: real ^'n::{finite,one}) = 1"
  by (rule norm_basis)

lemma vector_choose_size: "0 <= c ==> \<exists>(x::real^'n). norm x = c"
  apply (rule exI[where x="c *s basis arbitrary"])
  by (simp only: norm_mul norm_basis)

lemma vector_choose_dist: assumes e: "0 <= e"
  shows "\<exists>(y::real^'n). dist x y = e"
proof-
  from vector_choose_size[OF e] obtain c:: "real ^'n"  where "norm c = e"
    by blast
  then have "dist x (x - c) = e" by (simp add: dist_norm)
  then show ?thesis by blast
qed

lemma basis_inj: "inj (basis :: 'n \<Rightarrow> real ^'n)"
  by (simp add: inj_on_def Cart_eq)

lemma cond_value_iff: "f (if b then x else y) = (if b then f x else f y)"
  by auto

lemma basis_expansion:
  "setsum (\<lambda>i. (x$i) *s basis i) UNIV = (x::('a::ring_1) ^'n)" (is "?lhs = ?rhs" is "setsum ?f ?S = _")
  by (auto simp add: Cart_eq cond_value_iff setsum_delta[of "?S", where ?'b = "'a", simplified] cong del: if_weak_cong)

lemma smult_conv_scaleR: "c *s x = scaleR c x"
  unfolding vector_scalar_mult_def vector_scaleR_def by simp

lemma basis_expansion':
  "setsum (\<lambda>i. (x$i) *\<^sub>R basis i) UNIV = x"
  by (rule basis_expansion [where 'a=real, unfolded smult_conv_scaleR])

lemma basis_expansion_unique:
  "setsum (\<lambda>i. f i *s basis i) UNIV = (x::('a::comm_ring_1) ^'n) \<longleftrightarrow> (\<forall>i. f i = x$i)"
  by (simp add: Cart_eq setsum_delta cond_value_iff cong del: if_weak_cong)

lemma cond_application_beta: "(if b then f else g) x = (if b then f x else g x)"
  by auto

lemma dot_basis:
  shows "basis i \<bullet> x = x$i" "x \<bullet> (basis i) = (x$i)"
  unfolding inner_vector_def by (auto simp add: basis_def cond_application_beta  cond_value_iff setsum_delta cong del: if_weak_cong)

lemma inner_basis:
  fixes x :: "'a::{real_inner, real_algebra_1} ^ 'n"
  shows "inner (basis i) x = inner 1 (x $ i)"
    and "inner x (basis i) = inner (x $ i) 1"
  unfolding inner_vector_def basis_def
  by (auto simp add: cond_application_beta  cond_value_iff setsum_delta cong del: if_weak_cong)

lemma basis_eq_0: "basis i = (0::'a::semiring_1^'n) \<longleftrightarrow> False"
  by (auto simp add: Cart_eq)

lemma basis_nonzero:
  shows "basis k \<noteq> (0:: 'a::semiring_1 ^'n)"
  by (simp add: basis_eq_0)

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z"
proof
  assume "\<forall>x. x \<bullet> y = x \<bullet> z"
  hence "\<forall>x. x \<bullet> (y - z) = 0" by (simp add: inner_simps)
  hence "(y - z) \<bullet> (y - z) = 0" ..
  thus "y = z" by simp
qed simp

lemma vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
proof
  assume "\<forall>z. x \<bullet> z = y \<bullet> z"
  hence "\<forall>z. (x - y) \<bullet> z = 0" by (simp add: inner_simps)
  hence "(x - y) \<bullet> (x - y) = 0" ..
  thus "x = y" by simp
qed simp

subsection{* Orthogonality. *}

definition "orthogonal x y \<longleftrightarrow> (x \<bullet> y = 0)"

lemma orthogonal_basis:
  shows "orthogonal (basis i) x \<longleftrightarrow> x$i = (0::real)"
  by (auto simp add: orthogonal_def inner_vector_def basis_def cond_value_iff cond_application_beta setsum_delta cong del: if_weak_cong)

lemma orthogonal_basis_basis:
  shows "orthogonal (basis i :: real^'n) (basis j) \<longleftrightarrow> i \<noteq> j"
  unfolding orthogonal_basis[of i] basis_component[of j] by simp

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x ==> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x ==> orthogonal a (-x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y ==> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y ==> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a ==> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a ==> orthogonal (-x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a ==> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a ==> orthogonal (x - y) a"
  unfolding orthogonal_def inner_simps by auto

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def inner_commute)

subsection{* Linear functions. *}

definition
  linear :: "('a::real_vector \<Rightarrow> 'b::real_vector) \<Rightarrow> bool" where
  "linear f \<longleftrightarrow> (\<forall>x y. f(x + y) = f x + f y) \<and> (\<forall>c x. f(c *\<^sub>R x) = c *\<^sub>R f x)"

lemma linearI: assumes "\<And>x y. f (x + y) = f x + f y" "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "linear f" using assms unfolding linear_def by auto

lemma linear_compose_cmul: "linear f ==> linear (\<lambda>x. c *\<^sub>R f x)"
  by (simp add: linear_def algebra_simps)

lemma linear_compose_neg: "linear f ==> linear (\<lambda>x. -(f(x)))"
  by (simp add: linear_def)

lemma linear_compose_add: "linear f \<Longrightarrow> linear g ==> linear (\<lambda>x. f(x) + g(x))"
  by (simp add: linear_def algebra_simps)

lemma linear_compose_sub: "linear f \<Longrightarrow> linear g ==> linear (\<lambda>x. f x - g x)"
  by (simp add: linear_def algebra_simps)

lemma linear_compose: "linear f \<Longrightarrow> linear g ==> linear (g o f)"
  by (simp add: linear_def)

lemma linear_id: "linear id" by (simp add: linear_def id_def)

lemma linear_zero: "linear (\<lambda>x. 0)" by (simp add: linear_def)

lemma linear_compose_setsum:
  assumes fS: "finite S" and lS: "\<forall>a \<in> S. linear (f a)"
  shows "linear(\<lambda>x. setsum (\<lambda>a. f a x) S)"
  using lS
  apply (induct rule: finite_induct[OF fS])
  by (auto simp add: linear_zero intro: linear_compose_add)

lemma linear_vmul_component:
  assumes lf: "linear f"
  shows "linear (\<lambda>x. f x $ k *\<^sub>R v)"
  using lf
  by (auto simp add: linear_def algebra_simps)

lemma linear_0: "linear f ==> f 0 = 0"
  unfolding linear_def
  apply clarsimp
  apply (erule allE[where x="0::'a"])
  apply simp
  done

lemma linear_cmul: "linear f ==> f(c *\<^sub>R x) = c *\<^sub>R f x" by (simp add: linear_def)

lemma linear_neg: "linear f ==> f (-x) = - f x"
  using linear_cmul [where c="-1"] by simp

lemma linear_add: "linear f ==> f(x + y) = f x + f y" by (metis linear_def)

lemma linear_sub: "linear f ==> f(x - y) = f x - f y"
  by (simp add: diff_def linear_add linear_neg)

lemma linear_setsum:
  assumes lf: "linear f" and fS: "finite S"
  shows "f (setsum g S) = setsum (f o g) S"
proof (induct rule: finite_induct[OF fS])
  case 1 thus ?case by (simp add: linear_0[OF lf])
next
  case (2 x F)
  have "f (setsum g (insert x F)) = f (g x + setsum g F)" using "2.hyps"
    by simp
  also have "\<dots> = f (g x) + f (setsum g F)" using linear_add[OF lf] by simp
  also have "\<dots> = setsum (f o g) (insert x F)" using "2.hyps" by simp
  finally show ?case .
qed

lemma linear_setsum_mul:
  assumes lf: "linear f" and fS: "finite S"
  shows "f (setsum (\<lambda>i. c i *\<^sub>R v i) S) = setsum (\<lambda>i. c i *\<^sub>R f (v i)) S"
  using linear_setsum[OF lf fS, of "\<lambda>i. c i *\<^sub>R v i" , unfolded o_def]
  linear_cmul[OF lf] by simp

lemma linear_injective_0:
  assumes lf: "linear f"
  shows "inj f \<longleftrightarrow> (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
proof-
  have "inj f \<longleftrightarrow> (\<forall> x y. f x = f y \<longrightarrow> x = y)" by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f x - f y = 0 \<longrightarrow> x - y = 0)" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_sub[OF lf])
  also have "\<dots> \<longleftrightarrow> (\<forall> x. f x = 0 \<longrightarrow> x = 0)" by auto
  finally show ?thesis .
qed

lemma linear_bounded:
  fixes f:: "real ^'m \<Rightarrow> real ^'n"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof-
  let ?S = "UNIV:: 'm set"
  let ?B = "setsum (\<lambda>i. norm(f(basis i))) ?S"
  have fS: "finite ?S" by simp
  {fix x:: "real ^ 'm"
    let ?g = "(\<lambda>i. (x$i) *\<^sub>R (basis i) :: real ^ 'm)"
    have "norm (f x) = norm (f (setsum (\<lambda>i. (x$i) *\<^sub>R (basis i)) ?S))"
      by (simp add: basis_expansion')
    also have "\<dots> = norm (setsum (\<lambda>i. (x$i) *\<^sub>R f (basis i))?S)"
      using linear_setsum[OF lf fS, of ?g, unfolded o_def] linear_cmul[OF lf]
      by auto
    finally have th0: "norm (f x) = norm (setsum (\<lambda>i. (x$i) *\<^sub>R f (basis i))?S)" .
    {fix i assume i: "i \<in> ?S"
      from component_le_norm[of x i]
      have "norm ((x$i) *\<^sub>R f (basis i :: real ^'m)) \<le> norm (f (basis i)) * norm x"
      unfolding norm_scaleR
      apply (simp only: mult_commute)
      apply (rule mult_mono)
      by (auto simp add: field_simps) }
    then have th: "\<forall>i\<in> ?S. norm ((x$i) *\<^sub>R f (basis i :: real ^'m)) \<le> norm (f (basis i)) * norm x" by metis
    from setsum_norm_le[OF fS, of "\<lambda>i. (x$i) *\<^sub>R (f (basis i))", OF th]
    have "norm (f x) \<le> ?B * norm x" unfolding th0 setsum_left_distrib by metis}
  then show ?thesis by blast
qed

lemma linear_bounded_pos:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "\<exists>B > 0. \<forall>x. norm (f x) \<le> B * norm x"
proof-
  from linear_bounded[OF lf] obtain B where
    B: "\<forall>x. norm (f x) \<le> B * norm x" by blast
  let ?K = "\<bar>B\<bar> + 1"
  have Kp: "?K > 0" by arith
    {assume C: "B < 0"
      have "norm (1::real ^ 'n) > 0" by simp
      with C have "B * norm (1:: real ^ 'n) < 0"
        by (simp add: mult_less_0_iff)
      with B[rule_format, of 1] norm_ge_zero[of "f 1"] have False by simp
    }
    then have Bp: "B \<ge> 0" by ferrack
    {fix x::"real ^ 'n"
      have "norm (f x) \<le> ?K *  norm x"
      using B[rule_format, of x] norm_ge_zero[of x] norm_ge_zero[of "f x"] Bp
      apply (auto simp add: field_simps split add: abs_split)
      apply (erule order_trans, simp)
      done
  }
  then show ?thesis using Kp by blast
qed

lemma linear_conv_bounded_linear:
  fixes f :: "real ^ _ \<Rightarrow> real ^ _"
  shows "linear f \<longleftrightarrow> bounded_linear f"
proof
  assume "linear f"
  show "bounded_linear f"
  proof
    fix x y show "f (x + y) = f x + f y"
      using `linear f` unfolding linear_def by simp
  next
    fix r x show "f (scaleR r x) = scaleR r (f x)"
      using `linear f` unfolding linear_def
      by (simp add: smult_conv_scaleR)
  next
    have "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
      using `linear f` by (rule linear_bounded)
    thus "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (simp add: mult_commute)
  qed
next
  assume "bounded_linear f"
  then interpret f: bounded_linear f .
  show "linear f"
    unfolding linear_def smult_conv_scaleR
    by (simp add: f.add f.scaleR)
qed

lemma bounded_linearI': fixes f::"real^'n \<Rightarrow> real^'m"
  assumes "\<And>x y. f (x + y) = f x + f y" "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f" unfolding linear_conv_bounded_linear[THEN sym]
  by(rule linearI[OF assms])

subsection{* Bilinear functions. *}

definition "bilinear f \<longleftrightarrow> (\<forall>x. linear(\<lambda>y. f x y)) \<and> (\<forall>y. linear(\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h ==> h (x + y) z = (h x z) + (h y z)"
  by (simp add: bilinear_def linear_def)
lemma bilinear_radd: "bilinear h ==> h x (y + z) = (h x y) + (h x z)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lmul: "bilinear h ==> h (c *\<^sub>R x) y = c *\<^sub>R (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_rmul: "bilinear h ==> h x (c *\<^sub>R y) = c *\<^sub>R (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lneg: "bilinear h ==> h (- x) y = -(h x y)"
  by (simp only: scaleR_minus1_left [symmetric] bilinear_lmul)

lemma bilinear_rneg: "bilinear h ==> h x (- y) = - h x y"
  by (simp only: scaleR_minus1_left [symmetric] bilinear_rmul)

lemma  (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_imp_eq[of x y 0] by auto

lemma bilinear_lzero:
  assumes bh: "bilinear h" shows "h 0 x = 0"
  using bilinear_ladd[OF bh, of 0 0 x]
    by (simp add: eq_add_iff field_simps)

lemma bilinear_rzero:
  assumes bh: "bilinear h" shows "h x 0 = 0"
  using bilinear_radd[OF bh, of x 0 0 ]
    by (simp add: eq_add_iff field_simps)

lemma bilinear_lsub: "bilinear h ==> h (x - y) z = h x z - h y z"
  by (simp  add: diff_def bilinear_ladd bilinear_lneg)

lemma bilinear_rsub: "bilinear h ==> h z (x - y) = h z x - h z y"
  by (simp  add: diff_def bilinear_radd bilinear_rneg)

lemma bilinear_setsum:
  assumes bh: "bilinear h" and fS: "finite S" and fT: "finite T"
  shows "h (setsum f S) (setsum g T) = setsum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
proof-
  have "h (setsum f S) (setsum g T) = setsum (\<lambda>x. h (f x) (setsum g T)) S"
    apply (rule linear_setsum[unfolded o_def])
    using bh fS by (auto simp add: bilinear_def)
  also have "\<dots> = setsum (\<lambda>x. setsum (\<lambda>y. h (f x) (g y)) T) S"
    apply (rule setsum_cong, simp)
    apply (rule linear_setsum[unfolded o_def])
    using bh fT by (auto simp add: bilinear_def)
  finally show ?thesis unfolding setsum_cartesian_product .
qed

lemma bilinear_bounded:
  fixes h:: "real ^'m \<Rightarrow> real^'n \<Rightarrow> real ^'k"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof-
  let ?M = "UNIV :: 'm set"
  let ?N = "UNIV :: 'n set"
  let ?B = "setsum (\<lambda>(i,j). norm (h (basis i) (basis j))) (?M \<times> ?N)"
  have fM: "finite ?M" and fN: "finite ?N" by simp_all
  {fix x:: "real ^ 'm" and  y :: "real^'n"
    have "norm (h x y) = norm (h (setsum (\<lambda>i. (x$i) *\<^sub>R basis i) ?M) (setsum (\<lambda>i. (y$i) *\<^sub>R basis i) ?N))" unfolding basis_expansion' ..
    also have "\<dots> = norm (setsum (\<lambda> (i,j). h ((x$i) *\<^sub>R basis i) ((y$j) *\<^sub>R basis j)) (?M \<times> ?N))"  unfolding bilinear_setsum[OF bh fM fN] ..
    finally have th: "norm (h x y) = \<dots>" .
    have "norm (h x y) \<le> ?B * norm x * norm y"
      apply (simp add: setsum_left_distrib th)
      apply (rule setsum_norm_le)
      using fN fM
      apply simp
      apply (auto simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh] field_simps simp del: scaleR_scaleR)
      apply (rule mult_mono)
      apply (auto simp add: zero_le_mult_iff component_le_norm)
      apply (rule mult_mono)
      apply (auto simp add: zero_le_mult_iff component_le_norm)
      done}
  then show ?thesis by metis
qed

lemma bilinear_bounded_pos:
  fixes h:: "real ^'m \<Rightarrow> real^'n \<Rightarrow> real ^'k"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof-
  from bilinear_bounded[OF bh] obtain B where
    B: "\<forall>x y. norm (h x y) \<le> B * norm x * norm y" by blast
  let ?K = "\<bar>B\<bar> + 1"
  have Kp: "?K > 0" by arith
  have KB: "B < ?K" by arith
  {fix x::"real ^'m" and y :: "real ^'n"
    from KB Kp
    have "B * norm x * norm y \<le> ?K * norm x * norm y"
      apply -
      apply (rule mult_right_mono, rule mult_right_mono)
      by auto
    then have "norm (h x y) \<le> ?K * norm x * norm y"
      using B[rule_format, of x y] by simp}
  with Kp show ?thesis by blast
qed

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "real ^ _ \<Rightarrow> real ^ _ \<Rightarrow> real ^ _"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
proof
  assume "bilinear h"
  show "bounded_bilinear h"
  proof
    fix x y z show "h (x + y) z = h x z + h y z"
      using `bilinear h` unfolding bilinear_def linear_def by simp
  next
    fix x y z show "h x (y + z) = h x y + h x z"
      using `bilinear h` unfolding bilinear_def linear_def by simp
  next
    fix r x y show "h (scaleR r x) y = scaleR r (h x y)"
      using `bilinear h` unfolding bilinear_def linear_def
      by (simp add: smult_conv_scaleR)
  next
    fix r x y show "h x (scaleR r y) = scaleR r (h x y)"
      using `bilinear h` unfolding bilinear_def linear_def
      by (simp add: smult_conv_scaleR)
  next
    have "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
      using `bilinear h` by (rule bilinear_bounded)
    thus "\<exists>K. \<forall>x y. norm (h x y) \<le> norm x * norm y * K"
      by (simp add: mult_ac)
  qed
next
  assume "bounded_bilinear h"
  then interpret h: bounded_bilinear h .
  show "bilinear h"
    unfolding bilinear_def linear_conv_bounded_linear
    using h.bounded_linear_left h.bounded_linear_right
    by simp
qed

subsection{* Adjoints. *}

definition "adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma choice_iff: "(\<forall>x. \<exists>y. P x y) \<longleftrightarrow> (\<exists>f. \<forall>x. P x (f x))" by metis

text {* TODO: The following lemmas about adjoints should hold for any
Hilbert space (i.e. complete inner product space).
(see \url{http://en.wikipedia.org/wiki/Hermitian_adjoint})
*}

lemma adjoint_works_lemma:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "\<forall>x y. f x \<bullet> y = x \<bullet> adjoint f y"
proof-
  let ?N = "UNIV :: 'n set"
  let ?M = "UNIV :: 'm set"
  have fN: "finite ?N" by simp
  have fM: "finite ?M" by simp
  {fix y:: "real ^ 'm"
    let ?w = "(\<chi> i. (f (basis i) \<bullet> y)) :: real ^ 'n"
    {fix x
      have "f x \<bullet> y = f (setsum (\<lambda>i. (x$i) *\<^sub>R basis i) ?N) \<bullet> y"
        by (simp only: basis_expansion')
      also have "\<dots> = (setsum (\<lambda>i. (x$i) *\<^sub>R f (basis i)) ?N) \<bullet> y"
        unfolding linear_setsum[OF lf fN]
        by (simp add: linear_cmul[OF lf])
      finally have "f x \<bullet> y = x \<bullet> ?w"
        apply (simp only: )
        apply (simp add: inner_vector_def setsum_left_distrib setsum_right_distrib setsum_commute[of _ ?M ?N] field_simps)
        done}
  }
  then show ?thesis unfolding adjoint_def
    some_eq_ex[of "\<lambda>f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y"]
    using choice_iff[of "\<lambda>a b. \<forall>x. f x \<bullet> a = x \<bullet> b "]
    by metis
qed

lemma adjoint_works:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
  using adjoint_works_lemma[OF lf] by metis

lemma adjoint_linear:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  unfolding linear_def vector_eq_ldot[where 'a="real^'n", symmetric] apply safe
  unfolding inner_simps smult_conv_scaleR adjoint_works[OF lf] by auto

lemma adjoint_clauses:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
  and "adjoint f y \<bullet> x = y \<bullet> f x"
  by (simp_all add: adjoint_works[OF lf] inner_commute)

lemma adjoint_adjoint:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  apply (rule ext)
  by (simp add: vector_eq_ldot[symmetric] adjoint_clauses[OF adjoint_linear[OF lf]] adjoint_clauses[OF lf])

lemma adjoint_unique:
  fixes f:: "real ^'n \<Rightarrow> real ^'m"
  assumes lf: "linear f" and u: "\<forall>x y. f' x \<bullet> y = x \<bullet> f y"
  shows "f' = adjoint f"
  apply (rule ext)
  using u
  by (simp add: vector_eq_rdot[where 'a="real^'n", symmetric] adjoint_clauses[OF lf])

subsection {* Matrix operations *}

text{* Matrix notation. NB: an MxN matrix is of type @{typ "'a^'n^'m"}, not @{typ "'a^'m^'n"} *}

definition matrix_matrix_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'p^'n \<Rightarrow> 'a ^ 'p ^'m"  (infixl "**" 70)
  where "m ** m' == (\<chi> i j. setsum (\<lambda>k. ((m$i)$k) * ((m'$k)$j)) (UNIV :: 'n set)) ::'a ^ 'p ^'m"

definition matrix_vector_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'm"  (infixl "*v" 70)
  where "m *v x \<equiv> (\<chi> i. setsum (\<lambda>j. ((m$i)$j) * (x$j)) (UNIV ::'n set)) :: 'a^'m"

definition vector_matrix_mult :: "'a ^ 'm \<Rightarrow> ('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n "  (infixl "v*" 70)
  where "v v* m == (\<chi> j. setsum (\<lambda>i. ((m$i)$j) * (v$i)) (UNIV :: 'm set)) :: 'a^'n"

definition "(mat::'a::zero => 'a ^'n^'n) k = (\<chi> i j. if i = j then k else 0)"
definition transpose where 
  "(transpose::'a^'n^'m \<Rightarrow> 'a^'m^'n) A = (\<chi> i j. ((A$j)$i))"
definition "(row::'m => 'a ^'n^'m \<Rightarrow> 'a ^'n) i A = (\<chi> j. ((A$i)$j))"
definition "(column::'n =>'a^'n^'m =>'a^'m) j A = (\<chi> i. ((A$i)$j))"
definition "rows(A::'a^'n^'m) = { row i A | i. i \<in> (UNIV :: 'm set)}"
definition "columns(A::'a^'n^'m) = { column i A | i. i \<in> (UNIV :: 'n set)}"

lemma mat_0[simp]: "mat 0 = 0" by (vector mat_def)
lemma matrix_add_ldistrib: "(A ** (B + C)) = (A ** B) + (A ** C)"
  by (vector matrix_matrix_mult_def setsum_addf[symmetric] field_simps)

lemma matrix_mul_lid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "mat 1 ** A = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  by (auto simp only: cond_value_iff cond_application_beta setsum_delta'[OF finite]  mult_1_left mult_zero_left if_True UNIV_I)


lemma matrix_mul_rid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "A ** mat 1 = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  by (auto simp only: cond_value_iff cond_application_beta setsum_delta[OF finite]  mult_1_right mult_zero_right if_True UNIV_I cong: if_cong)

lemma matrix_mul_assoc: "A ** (B ** C) = (A ** B) ** C"
  apply (vector matrix_matrix_mult_def setsum_right_distrib setsum_left_distrib mult_assoc)
  apply (subst setsum_commute)
  apply simp
  done

lemma matrix_vector_mul_assoc: "A *v (B *v x) = (A ** B) *v x"
  apply (vector matrix_matrix_mult_def matrix_vector_mult_def setsum_right_distrib setsum_left_distrib mult_assoc)
  apply (subst setsum_commute)
  apply simp
  done

lemma matrix_vector_mul_lid: "mat 1 *v x = (x::'a::semiring_1 ^ 'n)"
  apply (vector matrix_vector_mult_def mat_def)
  by (simp add: cond_value_iff cond_application_beta
    setsum_delta' cong del: if_weak_cong)

lemma matrix_transpose_mul: "transpose(A ** B) = transpose B ** transpose (A::'a::comm_semiring_1^_^_)"
  by (simp add: matrix_matrix_mult_def transpose_def Cart_eq mult_commute)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n ^ 'm"
  shows "A = B \<longleftrightarrow>  (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
  apply auto
  apply (subst Cart_eq)
  apply clarify
  apply (clarsimp simp add: matrix_vector_mult_def basis_def cond_value_iff cond_application_beta Cart_eq cong del: if_weak_cong)
  apply (erule_tac x="basis ia" in allE)
  apply (erule_tac x="i" in allE)
  by (auto simp add: basis_def cond_value_iff cond_application_beta setsum_delta[OF finite] cong del: if_weak_cong)

lemma matrix_vector_mul_component:
  shows "((A::real^_^_) *v x)$k = (A$k) \<bullet> x"
  by (simp add: matrix_vector_mult_def inner_vector_def)

lemma dot_lmul_matrix: "((x::real ^_) v* A) \<bullet> y = x \<bullet> (A *v y)"
  apply (simp add: inner_vector_def matrix_vector_mult_def vector_matrix_mult_def setsum_left_distrib setsum_right_distrib mult_ac)
  apply (subst setsum_commute)
  by simp

lemma transpose_mat: "transpose (mat n) = mat n"
  by (vector transpose_def mat_def)

lemma transpose_transpose: "transpose(transpose A) = A"
  by (vector transpose_def)

lemma row_transpose:
  fixes A:: "'a::semiring_1^_^_"
  shows "row i (transpose A) = column i A"
  by (simp add: row_def column_def transpose_def Cart_eq)

lemma column_transpose:
  fixes A:: "'a::semiring_1^_^_"
  shows "column i (transpose A) = row i A"
  by (simp add: row_def column_def transpose_def Cart_eq)

lemma rows_transpose: "rows(transpose (A::'a::semiring_1^_^_)) = columns A"
by (auto simp add: rows_def columns_def row_transpose intro: set_ext)

lemma columns_transpose: "columns(transpose (A::'a::semiring_1^_^_)) = rows A" by (metis transpose_transpose rows_transpose)

text{* Two sometimes fruitful ways of looking at matrix-vector multiplication. *}

lemma matrix_mult_dot: "A *v x = (\<chi> i. A$i \<bullet> x)"
  by (simp add: matrix_vector_mult_def inner_vector_def)

lemma matrix_mult_vsum: "(A::'a::comm_semiring_1^'n^'m) *v x = setsum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def Cart_eq column_def mult_commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n) = (\<chi> j. setsum (\<lambda>i. (x$i) * (basis i :: 'a^'n)$j) (UNIV :: 'n set))"
  apply (subst basis_expansion[symmetric])
  by (vector Cart_eq setsum_component)

lemma linear_componentwise:
  fixes f:: "real ^'m \<Rightarrow> real ^ _"
  assumes lf: "linear f"
  shows "(f x)$j = setsum (\<lambda>i. (x$i) * (f (basis i)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof-
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (setsum (\<lambda>i.(x$i) *\<^sub>R f (basis i) ) ?M)$j"
    unfolding vector_smult_component[symmetric] smult_conv_scaleR
    unfolding setsum_component[of "(\<lambda>i.(x$i) *\<^sub>R f (basis i :: real^'m))" ?M]
    ..
  then show ?thesis unfolding linear_setsum_mul[OF lf fM, symmetric] basis_expansion' ..
qed

text{* Inverse matrices  (not necessarily square) *}

definition "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition "matrix_inv(A:: 'a::semiring_1^'n^'m) =
        (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

text{* Correspondence between matrices and linear operators. *}

definition matrix:: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
where "matrix f = (\<chi> i j. (f(basis j))$i)"

lemma matrix_vector_mul_linear: "linear(\<lambda>x. A *v (x::real ^ _))"
  by (simp add: linear_def matrix_vector_mult_def Cart_eq field_simps setsum_right_distrib setsum_addf)

lemma matrix_works: assumes lf: "linear f" shows "matrix f *v x = f (x::real ^ 'n)"
apply (simp add: matrix_def matrix_vector_mult_def Cart_eq mult_commute)
apply clarify
apply (rule linear_componentwise[OF lf, symmetric])
done

lemma matrix_vector_mul: "linear f ==> f = (\<lambda>x. matrix f *v (x::real ^ 'n))" by (simp add: ext matrix_works)

lemma matrix_of_matrix_vector_mul: "matrix(\<lambda>x. A *v (x :: real ^ 'n)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)

lemma matrix_compose:
  assumes lf: "linear (f::real^'n \<Rightarrow> real^'m)"
  and lg: "linear (g::real^'m \<Rightarrow> real^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp  add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_vector_column:"(A::'a::comm_semiring_1^'n^_) *v x = setsum (\<lambda>i. (x$i) *s ((transpose A)$i)) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def transpose_def Cart_eq mult_commute)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique[symmetric])
  apply (rule matrix_vector_mul_linear)
  apply (simp add: transpose_def inner_vector_def matrix_vector_mult_def setsum_left_distrib setsum_right_distrib)
  apply (subst setsum_commute)
  apply (auto simp add: mult_ac)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
  apply (subst matrix_vector_mul[OF lf])
  unfolding adjoint_matrix matrix_of_matrix_vector_mul ..

subsection{* Interlude: Some properties of real sets *}

lemma seq_mono_lemma: assumes "\<forall>(n::nat) \<ge> m. (d n :: real) < e n" and "\<forall>n \<ge> m. e n <= e m"
  shows "\<forall>n \<ge> m. d n < e m"
  using prems apply auto
  apply (erule_tac x="n" in allE)
  apply (erule_tac x="n" in allE)
  apply auto
  done


lemma real_convex_bound_lt:
  assumes xa: "(x::real) < a" and ya: "y < a" and u: "0 <= u" and v: "0 <= v"
  and uv: "u + v = 1"
  shows "u * x + v * y < a"
proof-
  have uv': "u = 0 \<longrightarrow> v \<noteq> 0" using u v uv by arith
  have "a = a * (u + v)" unfolding uv  by simp
  hence th: "u * a + v * a = a" by (simp add: field_simps)
  from xa u have "u \<noteq> 0 \<Longrightarrow> u*x < u*a" by (simp add: mult_strict_left_mono)
  from ya v have "v \<noteq> 0 \<Longrightarrow> v * y < v * a" by (simp add: mult_strict_left_mono)
  from xa ya u v have "u * x + v * y < u * a + v * a"
    apply (cases "u = 0", simp_all add: uv')
    apply(rule mult_strict_left_mono)
    using uv' apply simp_all

    apply (rule add_less_le_mono)
    apply(rule mult_strict_left_mono)
    apply simp_all
    apply (rule mult_left_mono)
    apply simp_all
    done
  thus ?thesis unfolding th .
qed

lemma real_convex_bound_le:
  assumes xa: "(x::real) \<le> a" and ya: "y \<le> a" and u: "0 <= u" and v: "0 <= v"
  and uv: "u + v = 1"
  shows "u * x + v * y \<le> a"
proof-
  from xa ya u v have "u * x + v * y \<le> u * a + v * a" by (simp add: add_mono mult_left_mono)
  also have "\<dots> \<le> (u + v) * a" by (simp add: field_simps)
  finally show ?thesis unfolding uv by simp
qed

lemma infinite_enumerate: assumes fS: "infinite S"
  shows "\<exists>r. subseq r \<and> (\<forall>n. r n \<in> S)"
unfolding subseq_def
using enumerate_in_set[OF fS] enumerate_mono[of _ _ S] fS by auto

lemma approachable_lt_le: "(\<exists>(d::real)>0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
apply auto
apply (rule_tac x="d/2" in exI)
apply auto
done


lemma triangle_lemma:
  assumes x: "0 <= (x::real)" and y:"0 <= y" and z: "0 <= z" and xy: "x^2 <= y^2 + z^2"
  shows "x <= y + z"
proof-
  have "y^2 + z^2 \<le> y^2 + 2*y*z + z^2" using z y by (simp add: mult_nonneg_nonneg)
  with xy have th: "x ^2 \<le> (y+z)^2" by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0" by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed


lemma lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x$i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?S = "(UNIV :: 'n set)"
  {assume H: "?rhs"
    then have ?lhs by auto}
  moreover
  {assume H: "?lhs"
    then obtain f where f:"\<forall>i. P i (f i)" unfolding choice_iff by metis
    let ?x = "(\<chi> i. (f i)) :: 'a ^ 'n"
    {fix i
      from f have "P i (f i)" by metis
      then have "P i (?x$i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed

lemma vec_in_image_vec: "vec x \<in> (vec ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec_add: "vec(x + y) = vec x + vec y"  by (vector vec_def)
lemma vec_sub: "vec(x - y) = vec x - vec y" by (vector vec_def)
lemma vec_cmul: "vec(c* x) = c *s vec x " by (vector vec_def)
lemma vec_neg: "vec(- x) = - vec x " by (vector vec_def)

lemma vec_setsum: assumes fS: "finite S"
  shows "vec(setsum f S) = setsum (vec o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply (simp)
  apply (auto simp add: vec_add)
  done

lemma setsum_Plus:
  "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow>
    (\<Sum>x\<in>A <+> B. g x) = (\<Sum>x\<in>A. g (Inl x)) + (\<Sum>x\<in>B. g (Inr x))"
  unfolding Plus_def
  by (subst setsum_Un_disjoint, auto simp add: setsum_reindex)

lemma setsum_UNIV_sum:
  fixes g :: "'a::finite + 'b::finite \<Rightarrow> _"
  shows "(\<Sum>x\<in>UNIV. g x) = (\<Sum>x\<in>UNIV. g (Inl x)) + (\<Sum>x\<in>UNIV. g (Inr x))"
  apply (subst UNIV_Plus_UNIV [symmetric])
  apply (rule setsum_Plus [OF finite finite])
  done

text {* TODO: move to NthRoot *}
lemma sqrt_add_le_add_sqrt:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "sqrt (x + y) \<le> sqrt x + sqrt y"
apply (rule power2_le_imp_le)
apply (simp add: real_sum_squared_expand add_nonneg_nonneg x y)
apply (simp add: mult_nonneg_nonneg x y)
apply (simp add: add_nonneg_nonneg x y)
done

subsection {* A generic notion of "hull" (convex, affine, conic hull and closure). *}

definition hull :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "hull" 75) where
  "S hull s = Inter {t. t \<in> S \<and> s \<subseteq> t}"

lemma hull_same: "s \<in> S \<Longrightarrow> S hull s = s"
  unfolding hull_def by auto

lemma hull_in: "(\<And>T. T \<subseteq> S ==> Inter T \<in> S) ==> (S hull s) \<in> S"
unfolding hull_def subset_iff by auto

lemma hull_eq: "(\<And>T. T \<subseteq> S ==> Inter T \<in> S) ==> (S hull s) = s \<longleftrightarrow> s \<in> S"
using hull_same[of s S] hull_in[of S s] by metis


lemma hull_hull: "S hull (S hull s) = S hull s"
  unfolding hull_def by blast

lemma hull_subset[intro]: "s \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_mono: " s \<subseteq> t ==> (S hull s) \<subseteq> (S hull t)"
  unfolding hull_def by blast

lemma hull_antimono: "S \<subseteq> T ==> (T hull s) \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_minimal: "s \<subseteq> t \<Longrightarrow> t \<in> S ==> (S hull s) \<subseteq> t"
  unfolding hull_def by blast

lemma subset_hull: "t \<in> S ==> S hull s \<subseteq> t \<longleftrightarrow>  s \<subseteq> t"
  unfolding hull_def by blast

lemma hull_unique: "s \<subseteq> t \<Longrightarrow> t \<in> S \<Longrightarrow> (\<And>t'. s \<subseteq> t' \<Longrightarrow> t' \<in> S ==> t \<subseteq> t')
           ==> (S hull s = t)"
unfolding hull_def by auto

lemma hull_induct: "(\<And>x. x\<in> S \<Longrightarrow> P x) \<Longrightarrow> Q {x. P x} \<Longrightarrow> \<forall>x\<in> Q hull S. P x"
  using hull_minimal[of S "{x. P x}" Q]
  by (auto simp add: subset_eq Collect_def mem_def)

lemma hull_inc: "x \<in> S \<Longrightarrow> x \<in> P hull S" by (metis hull_subset subset_eq)

lemma hull_union_subset: "(S hull s) \<union> (S hull t) \<subseteq> (S hull (s \<union> t))"
unfolding Un_subset_iff by (metis hull_mono Un_upper1 Un_upper2)

lemma hull_union: assumes T: "\<And>T. T \<subseteq> S ==> Inter T \<in> S"
  shows "S hull (s \<union> t) = S hull (S hull s \<union> S hull t)"
apply rule
apply (rule hull_mono)
unfolding Un_subset_iff
apply (metis hull_subset Un_upper1 Un_upper2 subset_trans)
apply (rule hull_minimal)
apply (metis hull_union_subset)
apply (metis hull_in T)
done

lemma hull_redundant_eq: "a \<in> (S hull s) \<longleftrightarrow> (S hull (insert a s) = S hull s)"
  unfolding hull_def by blast

lemma hull_redundant: "a \<in> (S hull s) ==> (S hull (insert a s) = S hull s)"
by (metis hull_redundant_eq)

text{* Archimedian properties and useful consequences. *}

lemma real_arch_simple: "\<exists>n. x <= real (n::nat)"
  using reals_Archimedean2[of x] apply auto by (rule_tac x="Suc n" in exI, auto)
lemmas real_arch_lt = reals_Archimedean2

lemmas real_arch = reals_Archimedean3

lemma real_arch_inv: "0 < e \<longleftrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  using reals_Archimedean
  apply (auto simp add: field_simps)
  apply (subgoal_tac "inverse (real n) > 0")
  apply arith
  apply simp
  done

lemma real_pow_lbound: "0 <= x ==> 1 + real n * x <= (1 + x) ^ n"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  hence h: "1 + real n * x \<le> (1 + x) ^ n" by simp
  from h have p: "1 \<le> (1 + x) ^ n" using Suc.prems by simp
  from h have "1 + real n * x + x \<le> (1 + x) ^ n + x" by simp
  also have "\<dots> \<le> (1 + x) ^ Suc n" apply (subst diff_le_0_iff_le[symmetric])
    apply (simp add: field_simps)
    using mult_left_mono[OF p Suc.prems] by simp
  finally show ?case  by (simp add: real_of_nat_Suc field_simps)
qed

lemma real_arch_pow: assumes x: "1 < (x::real)" shows "\<exists>n. y < x^n"
proof-
  from x have x0: "x - 1 > 0" by arith
  from real_arch[OF x0, rule_format, of y]
  obtain n::nat where n:"y < real n * (x - 1)" by metis
  from x0 have x00: "x- 1 \<ge> 0" by arith
  from real_pow_lbound[OF x00, of n] n
  have "y < x^n" by auto
  then show ?thesis by metis
qed

lemma real_arch_pow2: "\<exists>n. (x::real) < 2^ n"
  using real_arch_pow[of 2 x] by simp

lemma real_arch_pow_inv: assumes y: "(y::real) > 0" and x1: "x < 1"
  shows "\<exists>n. x^n < y"
proof-
  {assume x0: "x > 0"
    from x0 x1 have ix: "1 < 1/x" by (simp add: field_simps)
    from real_arch_pow[OF ix, of "1/y"]
    obtain n where n: "1/y < (1/x)^n" by blast
    then
    have ?thesis using y x0 by (auto simp add: field_simps power_divide) }
  moreover
  {assume "\<not> x > 0" with y x1 have ?thesis apply auto by (rule exI[where x=1], auto)}
  ultimately show ?thesis by metis
qed

lemma forall_pos_mono: "(\<And>d e::real. d < e \<Longrightarrow> P d ==> P e) \<Longrightarrow> (\<And>n::nat. n \<noteq> 0 ==> P(inverse(real n))) \<Longrightarrow> (\<And>e. 0 < e ==> P e)"
  by (metis real_arch_inv)

lemma forall_pos_mono_1: "(\<And>d e::real. d < e \<Longrightarrow> P d ==> P e) \<Longrightarrow> (\<And>n. P(inverse(real (Suc n)))) ==> 0 < e ==> P e"
  apply (rule forall_pos_mono)
  apply auto
  apply (atomize)
  apply (erule_tac x="n - 1" in allE)
  apply auto
  done

lemma real_archimedian_rdiv_eq_0: assumes x0: "x \<ge> 0" and c: "c \<ge> 0" and xc: "\<forall>(m::nat)>0. real m * x \<le> c"
  shows "x = 0"
proof-
  {assume "x \<noteq> 0" with x0 have xp: "x > 0" by arith
    from real_arch[OF xp, rule_format, of c] obtain n::nat where n: "c < real n * x"  by blast
    with xc[rule_format, of n] have "n = 0" by arith
    with n c have False by simp}
  then show ?thesis by blast
qed

(* ------------------------------------------------------------------------- *)
(* Geometric progression.                                                    *)
(* ------------------------------------------------------------------------- *)

lemma sum_gp_basic: "((1::'a::{field}) - x) * setsum (\<lambda>i. x^i) {0 .. n} = (1 - x^(Suc n))"
  (is "?lhs = ?rhs")
proof-
  {assume x1: "x = 1" hence ?thesis by simp}
  moreover
  {assume x1: "x\<noteq>1"
    hence x1': "x - 1 \<noteq> 0" "1 - x \<noteq> 0" "x - 1 = - (1 - x)" "- (1 - x) \<noteq> 0" by auto
    from geometric_sum[OF x1, of "Suc n", unfolded x1']
    have "(- (1 - x)) * setsum (\<lambda>i. x^i) {0 .. n} = - (1 - x^(Suc n))"
      unfolding atLeastLessThanSuc_atLeastAtMost
      using x1' apply (auto simp only: field_simps)
      apply (simp add: field_simps)
      done
    then have ?thesis by (simp add: field_simps) }
  ultimately show ?thesis by metis
qed

lemma sum_gp_multiplied: assumes mn: "m <= n"
  shows "((1::'a::{field}) - x) * setsum (op ^ x) {m..n} = x^m - x^ Suc n"
  (is "?lhs = ?rhs")
proof-
  let ?S = "{0..(n - m)}"
  from mn have mn': "n - m \<ge> 0" by arith
  let ?f = "op + m"
  have i: "inj_on ?f ?S" unfolding inj_on_def by auto
  have f: "?f ` ?S = {m..n}"
    using mn apply (auto simp add: image_iff Bex_def) by arith
  have th: "op ^ x o op + m = (\<lambda>i. x^m * x^i)"
    by (rule ext, simp add: power_add power_mult)
  from setsum_reindex[OF i, of "op ^ x", unfolded f th setsum_right_distrib[symmetric]]
  have "?lhs = x^m * ((1 - x) * setsum (op ^ x) {0..n - m})" by simp
  then show ?thesis unfolding sum_gp_basic using mn
    by (simp add: field_simps power_add[symmetric])
qed

lemma sum_gp: "setsum (op ^ (x::'a::{field})) {m .. n} =
   (if n < m then 0 else if x = 1 then of_nat ((n + 1) - m)
                    else (x^ m - x^ (Suc n)) / (1 - x))"
proof-
  {assume nm: "n < m" hence ?thesis by simp}
  moreover
  {assume "\<not> n < m" hence nm: "m \<le> n" by arith
    {assume x: "x = 1"  hence ?thesis by simp}
    moreover
    {assume x: "x \<noteq> 1" hence nz: "1 - x \<noteq> 0" by simp
      from sum_gp_multiplied[OF nm, of x] nz have ?thesis by (simp add: field_simps)}
    ultimately have ?thesis by metis
  }
  ultimately show ?thesis by metis
qed

lemma sum_gp_offset: "setsum (op ^ (x::'a::{field})) {m .. m+n} =
  (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  unfolding sum_gp[of x m "m + n"] power_Suc
  by (simp add: field_simps power_add)


subsection{* A bit of linear algebra. *}

definition
  subspace :: "'a::real_vector set \<Rightarrow> bool" where
  "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in> S. \<forall>y \<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x \<in>S. c *\<^sub>R x \<in>S )"

definition "span S = (subspace hull S)"
definition "dependent S \<longleftrightarrow> (\<exists>a \<in> S. a \<in> span(S - {a}))"
abbreviation "independent s == ~(dependent s)"

(* Closure properties of subspaces.                                          *)

lemma subspace_UNIV[simp]: "subspace(UNIV)" by (simp add: subspace_def)

lemma subspace_0: "subspace S ==> 0 \<in> S" by (metis subspace_def)

lemma subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S ==> x + y \<in> S"
  by (metis subspace_def)

lemma subspace_mul: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> - x \<in> S"
  by (metis scaleR_minus1_left subspace_mul)

lemma subspace_sub: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  by (metis diff_def subspace_add subspace_neg)

lemma subspace_setsum:
  assumes sA: "subspace A" and fB: "finite B"
  and f: "\<forall>x\<in> B. f x \<in> A"
  shows "setsum f B \<in> A"
  using  fB f sA
  apply(induct rule: finite_induct[OF fB])
  by (simp add: subspace_def sA, auto simp add: sA subspace_add)

lemma subspace_linear_image:
  assumes lf: "linear f" and sS: "subspace S"
  shows "subspace(f ` S)"
  using lf sS linear_0[OF lf]
  unfolding linear_def subspace_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="x + y" in bexI, auto)
  apply (rule_tac x="c *\<^sub>R x" in bexI, auto)
  done

lemma subspace_linear_preimage: "linear f ==> subspace S ==> subspace {x. f x \<in> S}"
  by (auto simp add: subspace_def linear_def linear_0[of f])

lemma subspace_trivial: "subspace {0}"
  by (simp add: subspace_def)

lemma subspace_inter: "subspace A \<Longrightarrow> subspace B ==> subspace (A \<inter> B)"
  by (simp add: subspace_def)


lemma span_mono: "A \<subseteq> B ==> span A \<subseteq> span B"
  by (metis span_def hull_mono)

lemma subspace_span: "subspace(span S)"
  unfolding span_def
  apply (rule hull_in[unfolded mem_def])
  apply (simp only: subspace_def Inter_iff Int_iff subset_eq)
  apply auto
  apply (erule_tac x="X" in ballE)
  apply (simp add: mem_def)
  apply blast
  apply (erule_tac x="X" in ballE)
  apply (erule_tac x="X" in ballE)
  apply (erule_tac x="X" in ballE)
  apply (clarsimp simp add: mem_def)
  apply simp
  apply simp
  apply simp
  apply (erule_tac x="X" in ballE)
  apply (erule_tac x="X" in ballE)
  apply (simp add: mem_def)
  apply simp
  apply simp
  done

lemma span_clauses:
  "a \<in> S ==> a \<in> span S"
  "0 \<in> span S"
  "x\<in> span S \<Longrightarrow> y \<in> span S ==> x + y \<in> span S"
  "x \<in> span S \<Longrightarrow> c *\<^sub>R x \<in> span S"
  by (metis span_def hull_subset subset_eq)
     (metis subspace_span subspace_def)+

lemma span_induct: assumes SP: "\<And>x. x \<in> S ==> P x"
  and P: "subspace P" and x: "x \<in> span S" shows "P x"
proof-
  from SP have SP': "S \<subseteq> P" by (simp add: mem_def subset_eq)
  from P have P': "P \<in> subspace" by (simp add: mem_def)
  from x hull_minimal[OF SP' P', unfolded span_def[symmetric]]
  show "P x" by (metis mem_def subset_eq)
qed

lemma span_empty: "span {} = {0}"
  apply (simp add: span_def)
  apply (rule hull_unique)
  apply (auto simp add: mem_def subspace_def)
  unfolding mem_def[of "0::'a", symmetric]
  apply simp
  done

lemma independent_empty: "independent {}"
  by (simp add: dependent_def)

lemma independent_mono: "independent A \<Longrightarrow> B \<subseteq> A ==> independent B"
  apply (clarsimp simp add: dependent_def span_mono)
  apply (subgoal_tac "span (B - {a}) \<le> span (A - {a})")
  apply force
  apply (rule span_mono)
  apply auto
  done

lemma span_subspace: "A \<subseteq> B \<Longrightarrow> B \<le> span A \<Longrightarrow>  subspace B \<Longrightarrow> span A = B"
  by (metis order_antisym span_def hull_minimal mem_def)

lemma span_induct': assumes SP: "\<forall>x \<in> S. P x"
  and P: "subspace P" shows "\<forall>x \<in> span S. P x"
  using span_induct SP P by blast

inductive span_induct_alt_help for S:: "'a::real_vector \<Rightarrow> bool"
  where
  span_induct_alt_help_0: "span_induct_alt_help S 0"
  | span_induct_alt_help_S: "x \<in> S \<Longrightarrow> span_induct_alt_help S z \<Longrightarrow> span_induct_alt_help S (c *\<^sub>R x + z)"

lemma span_induct_alt':
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)" shows "\<forall>x \<in> span S. h x"
proof-
  {fix x:: "'a" assume x: "span_induct_alt_help S x"
    have "h x"
      apply (rule span_induct_alt_help.induct[OF x])
      apply (rule h0)
      apply (rule hS, assumption, assumption)
      done}
  note th0 = this
  {fix x assume x: "x \<in> span S"

    have "span_induct_alt_help S x"
      proof(rule span_induct[where x=x and S=S])
        show "x \<in> span S" using x .
      next
        fix x assume xS : "x \<in> S"
          from span_induct_alt_help_S[OF xS span_induct_alt_help_0, of 1]
          show "span_induct_alt_help S x" by simp
        next
        have "span_induct_alt_help S 0" by (rule span_induct_alt_help_0)
        moreover
        {fix x y assume h: "span_induct_alt_help S x" "span_induct_alt_help S y"
          from h
          have "span_induct_alt_help S (x + y)"
            apply (induct rule: span_induct_alt_help.induct)
            apply simp
            unfolding add_assoc
            apply (rule span_induct_alt_help_S)
            apply assumption
            apply simp
            done}
        moreover
        {fix c x assume xt: "span_induct_alt_help S x"
          then have "span_induct_alt_help S (c *\<^sub>R x)"
            apply (induct rule: span_induct_alt_help.induct)
            apply (simp add: span_induct_alt_help_0)
            apply (simp add: scaleR_right_distrib)
            apply (rule span_induct_alt_help_S)
            apply assumption
            apply simp
            done
        }
        ultimately show "subspace (span_induct_alt_help S)"
          unfolding subspace_def mem_def Ball_def by blast
      qed}
  with th0 show ?thesis by blast
qed

lemma span_induct_alt:
  assumes h0: "h 0" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c *\<^sub>R x + y)" and x: "x \<in> span S"
  shows "h x"
using span_induct_alt'[of h S] h0 hS x by blast

(* Individual closure properties. *)

lemma span_superset: "x \<in> S ==> x \<in> span S" by (metis span_clauses(1))

lemma span_0: "0 \<in> span S" by (metis subspace_span subspace_0)

lemma span_add: "x \<in> span S \<Longrightarrow> y \<in> span S ==> x + y \<in> span S"
  by (metis subspace_add subspace_span)

lemma span_mul: "x \<in> span S ==> (c *\<^sub>R x) \<in> span S"
  by (metis subspace_span subspace_mul)

lemma span_neg: "x \<in> span S ==> - x \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_sub: "x \<in> span S \<Longrightarrow> y \<in> span S ==> x - y \<in> span S"
  by (metis subspace_span subspace_sub)

lemma span_setsum: "finite A \<Longrightarrow> \<forall>x \<in> A. f x \<in> span S ==> setsum f A \<in> span S"
  by (rule subspace_setsum, rule subspace_span)

lemma span_add_eq: "x \<in> span S \<Longrightarrow> x + y \<in> span S \<longleftrightarrow> y \<in> span S"
  apply (auto simp only: span_add span_sub)
  apply (subgoal_tac "(x + y) - x \<in> span S", simp)
  by (simp only: span_add span_sub)

(* Mapping under linear image. *)

lemma span_linear_image: assumes lf: "linear f"
  shows "span (f ` S) = f ` (span S)"
proof-
  {fix x
    assume x: "x \<in> span (f ` S)"
    have "x \<in> f ` span S"
      apply (rule span_induct[where x=x and S = "f ` S"])
      apply (clarsimp simp add: image_iff)
      apply (frule span_superset)
      apply blast
      apply (simp only: mem_def)
      apply (rule subspace_linear_image[OF lf])
      apply (rule subspace_span)
      apply (rule x)
      done}
  moreover
  {fix x assume x: "x \<in> span S"
    have th0:"(\<lambda>a. f a \<in> span (f ` S)) = {x. f x \<in> span (f ` S)}" apply (rule set_ext)
      unfolding mem_def Collect_def ..
    have "f x \<in> span (f ` S)"
      apply (rule span_induct[where S=S])
      apply (rule span_superset)
      apply simp
      apply (subst th0)
      apply (rule subspace_linear_preimage[OF lf subspace_span, of "f ` S"])
      apply (rule x)
      done}
  ultimately show ?thesis by blast
qed

(* The key breakdown property. *)

lemma span_breakdown:
  assumes bS: "b \<in> S" and aS: "a \<in> span S"
  shows "\<exists>k. a - k *\<^sub>R b \<in> span (S - {b})" (is "?P a")
proof-
  {fix x assume xS: "x \<in> S"
    {assume ab: "x = b"
      then have "?P x"
        apply simp
        apply (rule exI[where x="1"], simp)
        by (rule span_0)}
    moreover
    {assume ab: "x \<noteq> b"
      then have "?P x"  using xS
        apply -
        apply (rule exI[where x=0])
        apply (rule span_superset)
        by simp}
    ultimately have "?P x" by blast}
  moreover have "subspace ?P"
    unfolding subspace_def
    apply auto
    apply (simp add: mem_def)
    apply (rule exI[where x=0])
    using span_0[of "S - {b}"]
    apply (simp add: mem_def)
    apply (clarsimp simp add: mem_def)
    apply (rule_tac x="k + ka" in exI)
    apply (subgoal_tac "x + y - (k + ka) *\<^sub>R b = (x - k*\<^sub>R b) + (y - ka *\<^sub>R b)")
    apply (simp only: )
    apply (rule span_add[unfolded mem_def])
    apply assumption+
    apply (simp add: algebra_simps)
    apply (clarsimp simp add: mem_def)
    apply (rule_tac x= "c*k" in exI)
    apply (subgoal_tac "c *\<^sub>R x - (c * k) *\<^sub>R b = c*\<^sub>R (x - k*\<^sub>R b)")
    apply (simp only: )
    apply (rule span_mul[unfolded mem_def])
    apply assumption
    by (simp add: algebra_simps)
  ultimately show "?P a" using aS span_induct[where S=S and P= "?P"] by metis
qed

lemma span_breakdown_eq:
  "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. (x - k *\<^sub>R a) \<in> span S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume x: "x \<in> span (insert a S)"
    from x span_breakdown[of "a" "insert a S" "x"]
    have ?rhs apply clarsimp
      apply (rule_tac x= "k" in exI)
      apply (rule set_rev_mp[of _ "span (S - {a})" _])
      apply assumption
      apply (rule span_mono)
      apply blast
      done}
  moreover
  { fix k assume k: "x - k *\<^sub>R a \<in> span S"
    have eq: "x = (x - k *\<^sub>R a) + k *\<^sub>R a" by vector
    have "(x - k *\<^sub>R a) + k *\<^sub>R a \<in> span (insert a S)"
      apply (rule span_add)
      apply (rule set_rev_mp[of _ "span S" _])
      apply (rule k)
      apply (rule span_mono)
      apply blast
      apply (rule span_mul)
      apply (rule span_superset)
      apply blast
      done
    then have ?lhs using eq by metis}
  ultimately show ?thesis by blast
qed

(* Hence some "reversal" results.*)

lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)" and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof-
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - k*\<^sub>R b \<in> span (S - {b})" by auto
  {assume k0: "k = 0"
    with k have "a \<in> span S"
      apply (simp)
      apply (rule set_rev_mp)
      apply assumption
      apply (rule span_mono)
      apply blast
      done
    with na  have ?thesis by blast}
  moreover
  {assume k0: "k \<noteq> 0"
    have eq: "b = (1/k) *\<^sub>R a - ((1/k) *\<^sub>R a - b)" by vector
    from k0 have eq': "(1/k) *\<^sub>R (a - k*\<^sub>R b) = (1/k) *\<^sub>R a - b"
      by (simp add: algebra_simps)
    from k have "(1/k) *\<^sub>R (a - k*\<^sub>R b) \<in> span (S - {b})"
      by (rule span_mul)
    hence th: "(1/k) *\<^sub>R a - b \<in> span (S - {b})"
      unfolding eq' .

    from k
    have ?thesis
      apply (subst eq)
      apply (rule span_sub)
      apply (rule span_mul)
      apply (rule span_superset)
      apply blast
      apply (rule set_rev_mp)
      apply (rule th)
      apply (rule span_mono)
      using na by blast}
  ultimately show ?thesis by blast
qed

lemma in_span_delete:
  assumes a: "a \<in> span S"
  and na: "a \<notin> span (S-{b})"
  shows "b \<in> span (insert a (S - {b}))"
  apply (rule in_span_insert)
  apply (rule set_rev_mp)
  apply (rule a)
  apply (rule span_mono)
  apply blast
  apply (rule na)
  done

(* Transitivity property. *)

lemma span_trans:
  assumes x: "x \<in> span S" and y: "y \<in> span (insert x S)"
  shows "y \<in> span S"
proof-
  from span_breakdown[of x "insert x S" y, OF insertI1 y]
  obtain k where k: "y -k*\<^sub>R x \<in> span (S - {x})" by auto
  have eq: "y = (y - k *\<^sub>R x) + k *\<^sub>R x" by vector
  show ?thesis
    apply (subst eq)
    apply (rule span_add)
    apply (rule set_rev_mp)
    apply (rule k)
    apply (rule span_mono)
    apply blast
    apply (rule span_mul)
    by (rule x)
qed

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

lemma span_explicit:
  "span P = {y. \<exists>S u. finite S \<and> S \<subseteq> P \<and> setsum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?E" is "_ = {y. ?h y}" is "_ = {y. \<exists>S u. ?Q S u y}")
proof-
  {fix x assume x: "x \<in> ?E"
    then obtain S u where fS: "finite S" and SP: "S\<subseteq>P" and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = x"
      by blast
    have "x \<in> span P"
      unfolding u[symmetric]
      apply (rule span_setsum[OF fS])
      using span_mono[OF SP]
      by (auto intro: span_superset span_mul)}
  moreover
  have "\<forall>x \<in> span P. x \<in> ?E"
    unfolding mem_def Collect_def
  proof(rule span_induct_alt')
    show "?h 0"
      apply (rule exI[where x="{}"]) by simp
  next
    fix c x y
    assume x: "x \<in> P" and hy: "?h y"
    from hy obtain S u where fS: "finite S" and SP: "S\<subseteq>P"
      and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = y" by blast
    let ?S = "insert x S"
    let ?u = "\<lambda>y. if y = x then (if x \<in> S then u y + c else c)
                  else u y"
    from fS SP x have th0: "finite (insert x S)" "insert x S \<subseteq> P" by blast+
    {assume xS: "x \<in> S"
      have S1: "S = (S - {x}) \<union> {x}"
        and Sss:"finite (S - {x})" "finite {x}" "(S -{x}) \<inter> {x} = {}" using xS fS by auto
      have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S =(\<Sum>v\<in>S - {x}. u v *\<^sub>R v) + (u x + c) *\<^sub>R x"
        using xS
        by (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]]
          setsum_clauses(2)[OF fS] cong del: if_weak_cong)
      also have "\<dots> = (\<Sum>v\<in>S. u v *\<^sub>R v) + c *\<^sub>R x"
        apply (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]])
        by (simp add: algebra_simps)
      also have "\<dots> = c*\<^sub>R x + y"
        by (simp add: add_commute u)
      finally have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = c*\<^sub>R x + y" .
    then have "?Q ?S ?u (c*\<^sub>R x + y)" using th0 by blast}
  moreover
  {assume xS: "x \<notin> S"
    have th00: "(\<Sum>v\<in>S. (if v = x then c else u v) *\<^sub>R v) = y"
      unfolding u[symmetric]
      apply (rule setsum_cong2)
      using xS by auto
    have "?Q ?S ?u (c*\<^sub>R x + y)" using fS xS th0
      by (simp add: th00 setsum_clauses add_commute cong del: if_weak_cong)}
  ultimately have "?Q ?S ?u (c*\<^sub>R x + y)"
    by (cases "x \<in> S", simp, simp)
    then show "?h (c*\<^sub>R x + y)"
      apply -
      apply (rule exI[where x="?S"])
      apply (rule exI[where x="?u"]) by metis
  qed
  ultimately show ?thesis by blast
qed

lemma dependent_explicit:
  "dependent P \<longleftrightarrow> (\<exists>S u. finite S \<and> S \<subseteq> P \<and> (\<exists>v\<in>S. u v \<noteq> 0 \<and> setsum (\<lambda>v. u v *\<^sub>R v) S = 0))" (is "?lhs = ?rhs")
proof-
  {assume dP: "dependent P"
    then obtain a S u where aP: "a \<in> P" and fS: "finite S"
      and SP: "S \<subseteq> P - {a}" and ua: "setsum (\<lambda>v. u v *\<^sub>R v) S = a"
      unfolding dependent_def span_explicit by blast
    let ?S = "insert a S"
    let ?u = "\<lambda>y. if y = a then - 1 else u y"
    let ?v = a
    from aP SP have aS: "a \<notin> S" by blast
    from fS SP aP have th0: "finite ?S" "?S \<subseteq> P" "?v \<in> ?S" "?u ?v \<noteq> 0" by auto
    have s0: "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = 0"
      using fS aS
      apply (simp add: vector_smult_lneg setsum_clauses field_simps)
      apply (subst (2) ua[symmetric])
      apply (rule setsum_cong2)
      by auto
    with th0 have ?rhs
      apply -
      apply (rule exI[where x= "?S"])
      apply (rule exI[where x= "?u"])
      by clarsimp}
  moreover
  {fix S u v assume fS: "finite S"
      and SP: "S \<subseteq> P" and vS: "v \<in> S" and uv: "u v \<noteq> 0"
    and u: "setsum (\<lambda>v. u v *\<^sub>R v) S = 0"
    let ?a = v
    let ?S = "S - {v}"
    let ?u = "\<lambda>i. (- u i) / u v"
    have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"       using fS SP vS by auto
    have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = setsum (\<lambda>v. (- (inverse (u ?a))) *\<^sub>R (u v *\<^sub>R v)) S - ?u v *\<^sub>R v"
      using fS vS uv
      by (simp add: setsum_diff1 vector_smult_lneg divide_inverse
        vector_smult_assoc field_simps)
    also have "\<dots> = ?a"
      unfolding scaleR_right.setsum [symmetric] u
      using uv by simp
    finally  have "setsum (\<lambda>v. ?u v *\<^sub>R v) ?S = ?a" .
    with th0 have ?lhs
      unfolding dependent_def span_explicit
      apply -
      apply (rule bexI[where x= "?a"])
      apply (simp_all del: scaleR_minus_left)
      apply (rule exI[where x= "?S"])
      by (auto simp del: scaleR_minus_left)}
  ultimately show ?thesis by blast
qed


lemma span_finite:
  assumes fS: "finite S"
  shows "span S = {y. \<exists>u. setsum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
proof-
  {fix y assume y: "y \<in> span S"
    from y obtain S' u where fS': "finite S'" and SS': "S' \<subseteq> S" and
      u: "setsum (\<lambda>v. u v *\<^sub>R v) S' = y" unfolding span_explicit by blast
    let ?u = "\<lambda>x. if x \<in> S' then u x else 0"
    from setsum_restrict_set[OF fS, of "\<lambda>v. u v *\<^sub>R v" S', symmetric] SS'
    have "setsum (\<lambda>v. ?u v *\<^sub>R v) S = setsum (\<lambda>v. u v *\<^sub>R v) S'"
      unfolding cond_value_iff cond_application_beta
      by (simp add: cond_value_iff inf_absorb2 cong del: if_weak_cong)
    hence "setsum (\<lambda>v. ?u v *\<^sub>R v) S = y" by (metis u)
    hence "y \<in> ?rhs" by auto}
  moreover
  {fix y u assume u: "setsum (\<lambda>v. u v *\<^sub>R v) S = y"
    then have "y \<in> span S" using fS unfolding span_explicit by auto}
  ultimately show ?thesis by blast
qed


(* Standard bases are a spanning set, and obviously finite.                  *)

lemma span_stdbasis:"span {basis i :: real^'n | i. i \<in> (UNIV :: 'n set)} = UNIV"
apply (rule set_ext)
apply auto
apply (subst basis_expansion'[symmetric])
apply (rule span_setsum)
apply simp
apply auto
apply (rule span_mul)
apply (rule span_superset)
apply (auto simp add: Collect_def mem_def)
done

lemma finite_stdbasis: "finite {basis i ::real^'n |i. i\<in> (UNIV:: 'n set)}" (is "finite ?S")
proof-
  have eq: "?S = basis ` UNIV" by blast
  show ?thesis unfolding eq by auto
qed

lemma card_stdbasis: "card {basis i ::real^'n |i. i\<in> (UNIV :: 'n set)} = CARD('n)" (is "card ?S = _")
proof-
  have eq: "?S = basis ` UNIV" by blast
  show ?thesis unfolding eq using card_image[OF basis_inj] by simp
qed


lemma independent_stdbasis_lemma:
  assumes x: "(x::real ^ 'n) \<in> span (basis ` S)"
  and iS: "i \<notin> S"
  shows "(x$i) = 0"
proof-
  let ?U = "UNIV :: 'n set"
  let ?B = "basis ` S"
  let ?P = "\<lambda>(x::real^_). \<forall>i\<in> ?U. i \<notin> S \<longrightarrow> x$i =0"
 {fix x::"real^_" assume xS: "x\<in> ?B"
   from xS have "?P x" by auto}
 moreover
 have "subspace ?P"
   by (auto simp add: subspace_def Collect_def mem_def)
 ultimately show ?thesis
   using x span_induct[of ?B ?P x] iS by blast
qed

lemma independent_stdbasis: "independent {basis i ::real^'n |i. i\<in> (UNIV :: 'n set)}"
proof-
  let ?I = "UNIV :: 'n set"
  let ?b = "basis :: _ \<Rightarrow> real ^'n"
  let ?B = "?b ` ?I"
  have eq: "{?b i|i. i \<in> ?I} = ?B"
    by auto
  {assume d: "dependent ?B"
    then obtain k where k: "k \<in> ?I" "?b k \<in> span (?B - {?b k})"
      unfolding dependent_def by auto
    have eq1: "?B - {?b k} = ?B - ?b ` {k}"  by simp
    have eq2: "?B - {?b k} = ?b ` (?I - {k})"
      unfolding eq1
      apply (rule inj_on_image_set_diff[symmetric])
      apply (rule basis_inj) using k(1) by auto
    from k(2) have th0: "?b k \<in> span (?b ` (?I - {k}))" unfolding eq2 .
    from independent_stdbasis_lemma[OF th0, of k, simplified]
    have False by simp}
  then show ?thesis unfolding eq dependent_def ..
qed

(* This is useful for building a basis step-by-step.                         *)

lemma independent_insert:
  "independent(insert a S) \<longleftrightarrow>
      (if a \<in> S then independent S
                else independent S \<and> a \<notin> span S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume aS: "a \<in> S"
    hence ?thesis using insert_absorb[OF aS] by simp}
  moreover
  {assume aS: "a \<notin> S"
    {assume i: ?lhs
      then have ?rhs using aS
        apply simp
        apply (rule conjI)
        apply (rule independent_mono)
        apply assumption
        apply blast
        by (simp add: dependent_def)}
    moreover
    {assume i: ?rhs
      have ?lhs using i aS
        apply simp
        apply (auto simp add: dependent_def)
        apply (case_tac "aa = a", auto)
        apply (subgoal_tac "insert a S - {aa} = insert a (S - {aa})")
        apply simp
        apply (subgoal_tac "a \<in> span (insert aa (S - {aa}))")
        apply (subgoal_tac "insert aa (S - {aa}) = S")
        apply simp
        apply blast
        apply (rule in_span_insert)
        apply assumption
        apply blast
        apply blast
        done}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

(* The degenerate case of the Exchange Lemma.  *)

lemma mem_delete: "x \<in> (A - {a}) \<longleftrightarrow> x \<noteq> a \<and> x \<in> A"
  by blast

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

lemma span_inc: "S \<subseteq> span S"
  by (metis subset_eq span_superset)

lemma spanning_subset_independent:
  assumes BA: "B \<subseteq> A" and iA: "independent A"
  and AsB: "A \<subseteq> span B"
  shows "A = B"
proof
  from BA show "B \<subseteq> A" .
next
  from span_mono[OF BA] span_mono[OF AsB]
  have sAB: "span A = span B" unfolding span_span by blast

  {fix x assume x: "x \<in> A"
    from iA have th0: "x \<notin> span (A - {x})"
      unfolding dependent_def using x by blast
    from x have xsA: "x \<in> span A" by (blast intro: span_superset)
    have "A - {x} \<subseteq> A" by blast
    hence th1:"span (A - {x}) \<subseteq> span A" by (metis span_mono)
    {assume xB: "x \<notin> B"
      from xB BA have "B \<subseteq> A -{x}" by blast
      hence "span B \<subseteq> span (A - {x})" by (metis span_mono)
      with th1 th0 sAB have "x \<notin> span A" by blast
      with x have False by (metis span_superset)}
    then have "x \<in> B" by blast}
  then show "A \<subseteq> B" by blast
qed

(* The general case of the Exchange Lemma, the key to what follows.  *)

lemma exchange_lemma:
  assumes f:"finite t" and i: "independent s"
  and sp:"s \<subseteq> span t"
  shows "\<exists>t'. (card t' = card t) \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
using f i sp
proof(induct "card (t - s)" arbitrary: s t rule: less_induct)
  case less
  note ft = `finite t` and s = `independent s` and sp = `s \<subseteq> span t`
  let ?P = "\<lambda>t'. (card t' = card t) \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"
  {assume st: "s \<subseteq> t"
    from st ft span_mono[OF st] have ?ths apply - apply (rule exI[where x=t])
      by (auto intro: span_superset)}
  moreover
  {assume st: "t \<subseteq> s"

    from spanning_subset_independent[OF st s sp]
      st ft span_mono[OF st] have ?ths apply - apply (rule exI[where x=t])
      by (auto intro: span_superset)}
  moreover
  {assume st: "\<not> s \<subseteq> t" "\<not> t \<subseteq> s"
    from st(2) obtain b where b: "b \<in> t" "b \<notin> s" by blast
      from b have "t - {b} - s \<subset> t - s" by blast
      then have cardlt: "card (t - {b} - s) < card (t - s)" using ft
        by (auto intro: psubset_card_mono)
      from b ft have ct0: "card t \<noteq> 0" by auto
    {assume stb: "s \<subseteq> span(t -{b})"
      from ft have ftb: "finite (t -{b})" by auto
      from less(1)[OF cardlt ftb s stb]
      obtain u where u: "card u = card (t-{b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u" and fu: "finite u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u" using u by blast
      from u(3) b have "u \<subseteq> s \<union> t" by blast
      then have th1: "insert b u \<subseteq> s \<union> t" using u b by blast
      have bu: "b \<notin> u" using b u by blast
      from u(1) ft b have "card u = (card t - 1)" by auto
      then
      have th2: "card (insert b u) = card t"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)" apply (rule span_mono) by blast
      finally have th3: "s \<subseteq> span (insert b u)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"  by blast
      from th have ?ths by blast}
    moreover
    {assume stb: "\<not> s \<subseteq> span(t -{b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})" by blast
      have ab: "a \<noteq> b" using a b by blast
      have at: "a \<notin> t" using a ab span_superset[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < card (t - s)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (t - {b}))" using ft by auto
      {fix x assume xs: "x \<in> s"
        have t: "t \<subseteq> (insert b (insert a (t -{b})))" using b by auto
        from b(1) have "b \<in> span t" by (simp add: span_superset)
        have bs: "b \<in> span (insert a (t - {b}))" apply(rule in_span_delete)
          using  a sp unfolding subset_eq by auto
        from xs sp have "x \<in> span t" by blast
        with span_mono[OF t]
        have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))"  .}
      then have sp': "s \<subseteq> span (insert a (t - {b}))" by blast

      from less(1)[OF mlt ft' s sp'] obtain u where
        u: "card u = card (insert a (t -{b}))" "finite u" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t -{b})"
        "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u" by auto
      then have ?ths by blast }
    ultimately have ?ths by blast
  }
  ultimately
  show ?ths  by blast
qed

(* This implies corresponding size bounds.                                   *)

lemma independent_span_bound:
  assumes f: "finite t" and i: "independent s" and sp:"s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)


lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x\<in> (UNIV::'a::finite set)}"
proof-
  have eq: "{f x |x. x\<in> UNIV} = f ` UNIV" by auto
  show ?thesis unfolding eq
    apply (rule finite_imageI)
    apply (rule finite)
    done
qed


lemma independent_bound:
  fixes S:: "(real^'n) set"
  shows "independent S \<Longrightarrow> finite S \<and> card S <= CARD('n)"
  apply (subst card_stdbasis[symmetric])
  apply (rule independent_span_bound)
  apply (rule finite_Atleast_Atmost_nat)
  apply assumption
  unfolding span_stdbasis
  apply (rule subset_UNIV)
  done

lemma dependent_biggerset: "(finite (S::(real ^'n) set) ==> card S > CARD('n)) ==> dependent S"
  by (metis independent_bound not_less)

(* Hence we can create a maximal independent subset.                         *)

lemma maximal_independent_subset_extend:
  assumes sv: "(S::(real^'n) set) \<subseteq> V" and iS: "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  using sv iS
proof(induct "CARD('n) - card S" arbitrary: S rule: less_induct)
  case less
  note sv = `S \<subseteq> V` and i = `independent S`
  let ?P = "\<lambda>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  let ?ths = "\<exists>x. ?P x"
  let ?d = "CARD('n)"
  {assume "V \<subseteq> span S"
    then have ?ths  using sv i by blast }
  moreover
  {assume VS: "\<not> V \<subseteq> span S"
    from VS obtain a where a: "a \<in> V" "a \<notin> span S" by blast
    from a have aS: "a \<notin> S" by (auto simp add: span_superset)
    have th0: "insert a S \<subseteq> V" using a sv by blast
    from independent_insert[of a S]  i a
    have th1: "independent (insert a S)" by auto
    have mlt: "?d - card (insert a S) < ?d - card S"
      using aS a independent_bound[OF th1]
      by auto

    from less(1)[OF mlt th0 th1]
    obtain B where B: "insert a S \<subseteq> B" "B \<subseteq> V" "independent B" " V \<subseteq> span B"
      by blast
    from B have "?P B" by auto
    then have ?ths by blast}
  ultimately show ?ths by blast
qed

lemma maximal_independent_subset:
  "\<exists>(B:: (real ^'n) set). B\<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}:: (real ^'n) set"] empty_subsetI independent_empty)

(* Notion of dimension.                                                      *)

definition "dim V = (SOME n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n))"

lemma basis_exists:  "\<exists>B. (B :: (real ^'n) set) \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = dim V)"
unfolding dim_def some_eq_ex[of "\<lambda>n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n)"]
using maximal_independent_subset[of V] independent_bound
by auto

(* Consequences of independence or spanning for cardinality.                 *)

lemma independent_card_le_dim: 
  assumes "(B::(real ^'n) set) \<subseteq> V" and "independent B" shows "card B \<le> dim V"
proof -
  from basis_exists[of V] `B \<subseteq> V`
  obtain B' where "independent B'" and "B \<subseteq> span B'" and "card B' = dim V" by blast
  with independent_span_bound[OF _ `independent B` `B \<subseteq> span B'`] independent_bound[of B']
  show ?thesis by auto
qed

lemma span_card_ge_dim:  "(B::(real ^'n) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (metis basis_exists[of V] independent_span_bound subset_trans)

lemma basis_card_eq_dim:
  "B \<subseteq> (V:: (real ^'n) set) \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> finite B \<and> card B = dim V"
  by (metis order_eq_iff independent_card_le_dim span_card_ge_dim independent_bound)

lemma dim_unique: "(B::(real ^'n) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)

(* More lemmas about dimension.                                              *)

lemma dim_univ: "dim (UNIV :: (real^'n) set) = CARD('n)"
  apply (rule dim_unique[of "{basis i |i. i\<in> (UNIV :: 'n set)}"])
  by (auto simp only: span_stdbasis card_stdbasis finite_stdbasis independent_stdbasis)

lemma dim_subset:
  "(S:: (real ^'n) set) \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using basis_exists[of T] basis_exists[of S]
  by (metis independent_card_le_dim subset_trans)

lemma dim_subset_univ: "dim (S:: (real^'n) set) \<le> CARD('n)"
  by (metis dim_subset subset_UNIV dim_univ)

(* Converses to those.                                                       *)

lemma card_ge_dim_independent:
  assumes BV:"(B::(real ^'n) set) \<subseteq> V" and iB:"independent B" and dVB:"dim V \<le> card B"
  shows "V \<subseteq> span B"
proof-
  {fix a assume aV: "a \<in> V"
    {assume aB: "a \<notin> span B"
      then have iaB: "independent (insert a B)" using iB aV  BV by (simp add: independent_insert)
      from aV BV have th0: "insert a B \<subseteq> V" by blast
      from aB have "a \<notin>B" by (auto simp add: span_superset)
      with independent_card_le_dim[OF th0 iaB] dVB independent_bound[OF iB] have False by auto }
    then have "a \<in> span B"  by blast}
  then show ?thesis by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "(B:: (real ^'n) set) \<subseteq> V" and VB: "V \<subseteq> span B"
  and fB: "finite B" and dVB: "dim V \<ge> card B"
  shows "independent B"
proof-
  {fix a assume a: "a \<in> B" "a \<in> span (B -{a})"
    from a fB have c0: "card B \<noteq> 0" by auto
    from a fB have cb: "card (B -{a}) = card B - 1" by auto
    from BV a have th0: "B -{a} \<subseteq> V" by blast
    {fix x assume x: "x \<in> V"
      from a have eq: "insert a (B -{a}) = B" by blast
      from x VB have x': "x \<in> span B" by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B -{a})" . }
    then have th1: "V \<subseteq> span (B -{a})" by blast
    have th2: "finite (B -{a})" using fB by auto
    from span_card_ge_dim[OF th0 th1 th2]
    have c: "dim V \<le> card (B -{a})" .
    from c c0 dVB cb have False by simp}
  then show ?thesis unfolding dependent_def by blast
qed

lemma card_eq_dim: "(B:: (real ^'n) set) \<subseteq> V \<Longrightarrow> card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning
    card_ge_dim_independent)

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

lemma independent_bound_general:
  "independent (S:: (real^'n) set) \<Longrightarrow> finite S \<and> card S \<le> dim S"
  by (metis independent_card_le_dim independent_bound subset_refl)

lemma dependent_biggerset_general: "(finite (S:: (real^'n) set) \<Longrightarrow> card S > dim S) \<Longrightarrow> dependent S"
  using independent_bound_general[of S] by (metis linorder_not_le)

lemma dim_span: "dim (span (S:: (real ^'n) set)) = dim S"
proof-
  have th0: "dim S \<le> dim (span S)"
    by (auto simp add: subset_eq intro: dim_subset span_superset)
  from basis_exists[of S]
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by blast+
  have bSS: "B \<subseteq> span S" using B(1) by (metis subset_eq span_inc)
  have sssB: "span S \<subseteq> span B" using span_mono[OF B(3)] by (simp add: span_span)
  from span_card_ge_dim[OF bSS sssB fB(1)] th0 show ?thesis
    using fB(2)  by arith
qed

lemma subset_le_dim: "(S:: (real ^'n) set) \<subseteq> span T \<Longrightarrow> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma span_eq_dim: "span (S:: (real ^'n) set) = span T ==> dim S = dim T"
  by (metis dim_span)

lemma spans_image:
  assumes lf: "linear f" and VB: "V \<subseteq> span B"
  shows "f ` V \<subseteq> span (f ` B)"
  unfolding span_linear_image[OF lf]
  by (metis VB image_mono)

lemma dim_image_le:
  fixes f :: "real^'n \<Rightarrow> real^'m"
  assumes lf: "linear f" shows "dim (f ` S) \<le> dim (S:: (real ^'n) set)"
proof-
  from basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by blast+
  have "dim (f ` S) \<le> card (f ` B)"
    apply (rule span_card_ge_dim)
    using lf B fB by (auto simp add: span_linear_image spans_image subset_image_iff)
  also have "\<dots> \<le> dim S" using card_image_le[OF fB(1)] fB by simp
  finally show ?thesis .
qed

(* Relation between bases and injectivity/surjectivity of map.               *)

lemma spanning_surjective_image:
  assumes us: "UNIV \<subseteq> span S"
  and lf: "linear f" and sf: "surj f"
  shows "UNIV \<subseteq> span (f ` S)"
proof-
  have "UNIV \<subseteq> f ` UNIV" using sf by (auto simp add: surj_def)
  also have " \<dots> \<subseteq> span (f ` S)" using spans_image[OF lf us] .
finally show ?thesis .
qed

lemma independent_injective_image:
  assumes iS: "independent S" and lf: "linear f" and fi: "inj f"
  shows "independent (f ` S)"
proof-
  {fix a assume a: "a \<in> S" "f a \<in> span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})" using fi
      by (auto simp add: inj_on_def)
    from a have "f a \<in> f ` span (S -{a})"
      unfolding eq span_linear_image[OF lf, of "S - {a}"]  by blast
    hence "a \<in> span (S -{a})" using fi by (auto simp add: inj_on_def)
    with a(1) iS  have False by (simp add: dependent_def) }
  then show ?thesis unfolding dependent_def by blast
qed

(* ------------------------------------------------------------------------- *)
(* Picking an orthogonal replacement for a spanning set.                     *)
(* ------------------------------------------------------------------------- *)
    (* FIXME : Move to some general theory ?*)
definition "pairwise R S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y\<in> S. x\<noteq>y \<longrightarrow> R x y)"

lemma vector_sub_project_orthogonal: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps smult_conv_scaleR by auto

lemma basis_orthogonal:
  fixes B :: "(real ^'n) set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
proof(induct rule: finite_induct[OF fB])
  case 1 thus ?case apply (rule exI[where x="{}"]) by (auto simp add: pairwise_def)
next
  case (2 a B)
  note fB = `finite B` and aB = `a \<notin> B`
  from `\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C`
  obtain C where C: "finite C" "card C \<le> card B"
    "span C = span B" "pairwise orthogonal C" by blast
  let ?a = "a - setsum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C" by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)" by (simp add: card_insert_if)
  {fix x k
    have th0: "\<And>(a::'b::comm_ring) b c. a - (b - c) = c + (a - b)" by (simp add: field_simps)
    have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x)) \<in> span C \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
      apply (simp only: scaleR_right_diff_distrib th0)
      apply (rule span_add_eq)
      apply (rule span_mul)
      apply (rule span_setsum[OF C(1)])
      apply clarify
      apply (rule span_mul)
      by (rule span_superset)}
  then have SC: "span ?C = span (insert a B)"
    unfolding expand_set_eq span_breakdown_eq C(3)[symmetric] by auto
  thm pairwise_def
  {fix x y assume xC: "x \<in> ?C" and yC: "y \<in> ?C" and xy: "x \<noteq> y"
    {assume xa: "x = ?a" and ya: "y = ?a"
      have "orthogonal x y" using xa ya xy by blast}
    moreover
    {assume xa: "x = ?a" and ya: "y \<noteq> ?a" "y \<in> C"
      from ya have Cy: "C = insert y (C - {y})" by blast
      have fth: "finite (C - {y})" using C by simp
      have "orthogonal x y"
        using xa ya
        unfolding orthogonal_def xa inner_simps diff_eq_0_iff_eq
        apply simp
        apply (subst Cy)
        using C(1) fth
        apply (simp only: setsum_clauses) unfolding smult_conv_scaleR
        apply (auto simp add: inner_simps inner_commute[of y a] dot_lsum[OF fth])
        apply (rule setsum_0')
        apply clarsimp
        apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
        by auto}
    moreover
    {assume xa: "x \<noteq> ?a" "x \<in> C" and ya: "y = ?a"
      from xa have Cx: "C = insert x (C - {x})" by blast
      have fth: "finite (C - {x})" using C by simp
      have "orthogonal x y"
        using xa ya
        unfolding orthogonal_def ya inner_simps diff_eq_0_iff_eq
        apply simp
        apply (subst Cx)
        using C(1) fth
        apply (simp only: setsum_clauses) unfolding smult_conv_scaleR
        apply (subst inner_commute[of x])
        apply (auto simp add: inner_simps inner_commute[of x a] dot_rsum[OF fth])
        apply (rule setsum_0')
        apply clarsimp
        apply (rule C(4)[unfolded pairwise_def orthogonal_def, rule_format])
        by auto}
    moreover
    {assume xa: "x \<in> C" and ya: "y \<in> C"
      have "orthogonal x y" using xa ya xy C(4) unfolding pairwise_def by blast}
    ultimately have "orthogonal x y" using xC yC by blast}
  then have CPO: "pairwise orthogonal ?C" unfolding pairwise_def by blast
  from fC cC SC CPO have "?P (insert a B) ?C" by blast
  then show ?case by blast
qed

lemma orthogonal_basis_exists:
  fixes V :: "(real ^'n) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (card B = dim V) \<and> pairwise orthogonal B"
proof-
  from basis_exists[of V] obtain B where B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V" by blast
  from B have fB: "finite B" "card B = dim V" using independent_bound by auto
  from basis_orthogonal[OF fB(1)] obtain C where
    C: "finite C" "card C \<le> card B" "span C = span B" "pairwise orthogonal C" by blast
  from C B
  have CSV: "C \<subseteq> span V" by (metis span_inc span_mono subset_trans)
  from span_mono[OF B(3)]  C have SVC: "span V \<subseteq> span C" by (simp add: span_span)
  from card_le_dim_spanning[OF CSV SVC C(1)] C(2,3) fB
  have iC: "independent C" by (simp add: dim_span)
  from C fB have "card C \<le> dim V" by simp
  moreover have "dim V \<le> card C" using span_card_ge_dim[OF CSV SVC C(1)]
    by (simp add: dim_span)
  ultimately have CdV: "card C = dim V" using C(1) by simp
  from C B CSV CdV iC show ?thesis by auto
qed

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  using span_inc[unfolded subset_eq] using span_mono[of T "span S"] span_mono[of S "span T"]
  by(auto simp add: span_span)

(* ------------------------------------------------------------------------- *)
(* Low-dimensional subset is in a hyperplane (weak orthogonal complement).   *)
(* ------------------------------------------------------------------------- *)

lemma span_not_univ_orthogonal:
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>(a:: real ^'n). a \<noteq>0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof-
  from sU obtain a where a: "a \<notin> span S" by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B" "card B = dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S" using independent_bound by auto
  from span_mono[OF B(2)] span_mono[OF B(3)]
  have sSB: "span S = span B" by (simp add: span_span)
  let ?a = "a - setsum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B"
  have "setsum (\<lambda>b. (a \<bullet> b / (b \<bullet> b)) *\<^sub>R b) B \<in> span S"
    unfolding sSB
    apply (rule span_setsum[OF fB(1)])
    apply clarsimp
    apply (rule span_mul)
    by (rule span_superset)
  with a have a0:"?a  \<noteq> 0" by auto
  have "\<forall>x\<in>span B. ?a \<bullet> x = 0"
  proof(rule span_induct')
    show "subspace (\<lambda>x. ?a \<bullet> x = 0)" by (auto simp add: subspace_def mem_def inner_simps smult_conv_scaleR)
  
next
    {fix x assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})" by blast
      have fth: "finite (B - {x})" using fB by simp
      have "?a \<bullet> x = 0"
        apply (subst B') using fB fth
        unfolding setsum_clauses(2)[OF fth]
        apply simp unfolding inner_simps smult_conv_scaleR
        apply (clarsimp simp add: inner_simps smult_conv_scaleR dot_lsum)
        apply (rule setsum_0', rule ballI)
        unfolding inner_commute
        by (auto simp add: x field_simps intro: B(5)[unfolded pairwise_def orthogonal_def, rule_format])}
    then show "\<forall>x \<in> B. ?a \<bullet> x = 0" by blast
  qed
  with a0 show ?thesis unfolding sSB by (auto intro: exI[where x="?a"])
qed

lemma span_not_univ_subset_hyperplane:
  assumes SU: "span S \<noteq> (UNIV ::(real^'n) set)"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_univ_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  assumes d: "dim S < CARD('n::finite)"
  shows "\<exists>(a::real ^'n). a  \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
proof-
  {assume "span S = UNIV"
    hence "dim (span S) = dim (UNIV :: (real ^'n) set)" by simp
    hence "dim S = CARD('n)" by (simp add: dim_span dim_univ)
    with d have False by arith}
  hence th: "span S \<noteq> UNIV" by blast
  from span_not_univ_subset_hyperplane[OF th] show ?thesis .
qed

(* We can extend a linear basis-basis injection to the whole set.            *)

lemma linear_indep_image_lemma:
  assumes lf: "linear f" and fB: "finite B"
  and ifB: "independent (f ` B)"
  and fi: "inj_on f B" and xsB: "x \<in> span B"
  and fx: "f x = 0"
  shows "x = 0"
  using fB ifB fi xsB fx
proof(induct arbitrary: x rule: finite_induct[OF fB])
  case 1 thus ?case by (auto simp add:  span_empty)
next
  case (2 a b x)
  have fb: "finite b" using "2.prems" by simp
  have th0: "f ` b \<subseteq> f ` (insert a b)"
    apply (rule image_mono) by blast
  from independent_mono[ OF "2.prems"(2) th0]
  have ifb: "independent (f ` b)"  .
  have fib: "inj_on f b"
    apply (rule subset_inj_on [OF "2.prems"(3)])
    by blast
  from span_breakdown[of a "insert a b", simplified, OF "2.prems"(4)]
  obtain k where k: "x - k*\<^sub>R a \<in> span (b -{a})" by blast
  have "f (x - k*\<^sub>R a) \<in> span (f ` b)"
    unfolding span_linear_image[OF lf]
    apply (rule imageI)
    using k span_mono[of "b-{a}" b] by blast
  hence "f x - k*\<^sub>R f a \<in> span (f ` b)"
    by (simp add: linear_sub[OF lf] linear_cmul[OF lf])
  hence th: "-k *\<^sub>R f a \<in> span (f ` b)"
    using "2.prems"(5) by (simp add: vector_smult_lneg)
  {assume k0: "k = 0"
    from k0 k have "x \<in> span (b -{a})" by simp
    then have "x \<in> span b" using span_mono[of "b-{a}" b]
      by blast}
  moreover
  {assume k0: "k \<noteq> 0"
    from span_mul[OF th, of "- 1/ k"] k0
    have th1: "f a \<in> span (f ` b)"
      by (auto simp add: vector_smult_assoc)
    from inj_on_image_set_diff[OF "2.prems"(3), of "insert a b " "{a}", symmetric]
    have tha: "f ` insert a b - f ` {a} = f ` (insert a b - {a})" by blast
    from "2.prems"(2)[unfolded dependent_def bex_simps(10), rule_format, of "f a"]
    have "f a \<notin> span (f ` b)" using tha
      using "2.hyps"(2)
      "2.prems"(3) by auto
    with th1 have False by blast
    then have "x \<in> span b" by blast}
  ultimately have xsb: "x \<in> span b" by blast
  from "2.hyps"(3)[OF fb ifb fib xsb "2.prems"(5)]
  show "x = 0" .
qed

(* We can extend a linear mapping from basis.                                *)

lemma linear_independent_extend_lemma:
  fixes f :: "'a::real_vector \<Rightarrow> 'b::real_vector"
  assumes fi: "finite B" and ib: "independent B"
  shows "\<exists>g. (\<forall>x\<in> span B. \<forall>y\<in> span B. g (x + y) = g x + g y)
           \<and> (\<forall>x\<in> span B. \<forall>c. g (c*\<^sub>R x) = c *\<^sub>R g x)
           \<and> (\<forall>x\<in> B. g x = f x)"
using ib fi
proof(induct rule: finite_induct[OF fi])
  case 1 thus ?case by (auto simp add: span_empty)
next
  case (2 a b)
  from "2.prems" "2.hyps" have ibf: "independent b" "finite b"
    by (simp_all add: independent_insert)
  from "2.hyps"(3)[OF ibf] obtain g where
    g: "\<forall>x\<in>span b. \<forall>y\<in>span b. g (x + y) = g x + g y"
    "\<forall>x\<in>span b. \<forall>c. g (c *\<^sub>R x) = c *\<^sub>R g x" "\<forall>x\<in>b. g x = f x" by blast
  let ?h = "\<lambda>z. SOME k. (z - k *\<^sub>R a) \<in> span b"
  {fix z assume z: "z \<in> span (insert a b)"
    have th0: "z - ?h z *\<^sub>R a \<in> span b"
      apply (rule someI_ex)
      unfolding span_breakdown_eq[symmetric]
      using z .
    {fix k assume k: "z - k *\<^sub>R a \<in> span b"
      have eq: "z - ?h z *\<^sub>R a - (z - k*\<^sub>R a) = (k - ?h z) *\<^sub>R a"
        by (simp add: field_simps scaleR_left_distrib [symmetric])
      from span_sub[OF th0 k]
      have khz: "(k - ?h z) *\<^sub>R a \<in> span b" by (simp add: eq)
      {assume "k \<noteq> ?h z" hence k0: "k - ?h z \<noteq> 0" by simp
        from k0 span_mul[OF khz, of "1 /(k - ?h z)"]
        have "a \<in> span b" by (simp add: vector_smult_assoc)
        with "2.prems"(1) "2.hyps"(2) have False
          by (auto simp add: dependent_def)}
      then have "k = ?h z" by blast}
    with th0 have "z - ?h z *\<^sub>R a \<in> span b \<and> (\<forall>k. z - k *\<^sub>R a \<in> span b \<longrightarrow> k = ?h z)" by blast}
  note h = this
  let ?g = "\<lambda>z. ?h z *\<^sub>R f a + g (z - ?h z *\<^sub>R a)"
  {fix x y assume x: "x \<in> span (insert a b)" and y: "y \<in> span (insert a b)"
    have tha: "\<And>(x::'a) y a k l. (x + y) - (k + l) *\<^sub>R a = (x - k *\<^sub>R a) + (y - l *\<^sub>R a)"
      by (simp add: algebra_simps)
    have addh: "?h (x + y) = ?h x + ?h y"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (rule span_add[OF x y])
      unfolding tha
      by (metis span_add x y conjunct1[OF h, rule_format])
    have "?g (x + y) = ?g x + ?g y"
      unfolding addh tha
      g(1)[rule_format,OF conjunct1[OF h, OF x] conjunct1[OF h, OF y]]
      by (simp add: scaleR_left_distrib)}
  moreover
  {fix x:: "'a" and c:: real  assume x: "x \<in> span (insert a b)"
    have tha: "\<And>(x::'a) c k a. c *\<^sub>R x - (c * k) *\<^sub>R a = c *\<^sub>R (x - k *\<^sub>R a)"
      by (simp add: algebra_simps)
    have hc: "?h (c *\<^sub>R x) = c * ?h x"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (metis span_mul x)
      by (metis tha span_mul x conjunct1[OF h])
    have "?g (c *\<^sub>R x) = c*\<^sub>R ?g x"
      unfolding hc tha g(2)[rule_format, OF conjunct1[OF h, OF x]]
      by (simp add: algebra_simps)}
  moreover
  {fix x assume x: "x \<in> (insert a b)"
    {assume xa: "x = a"
      have ha1: "1 = ?h a"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis span_superset insertI1)
        using conjunct1[OF h, OF span_superset, OF insertI1]
        by (auto simp add: span_0)

      from xa ha1[symmetric] have "?g x = f x"
        apply simp
        using g(2)[rule_format, OF span_0, of 0]
        by simp}
    moreover
    {assume xb: "x \<in> b"
      have h0: "0 = ?h x"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis  span_superset x)
        apply simp
        apply (metis span_superset xb)
        done
      have "?g x = f x"
        by (simp add: h0[symmetric] g(3)[rule_format, OF xb])}
    ultimately have "?g x = f x" using x by blast }
  ultimately show ?case apply - apply (rule exI[where x="?g"]) by blast
qed

lemma linear_independent_extend:
  assumes iB: "independent (B:: (real ^'n) set)"
  shows "\<exists>g. linear g \<and> (\<forall>x\<in>B. g x = f x)"
proof-
  from maximal_independent_subset_extend[of B UNIV] iB
  obtain C where C: "B \<subseteq> C" "independent C" "\<And>x. x \<in> span C" by auto

  from C(2) independent_bound[of C] linear_independent_extend_lemma[of C f]
  obtain g where g: "(\<forall>x\<in> span C. \<forall>y\<in> span C. g (x + y) = g x + g y)
           \<and> (\<forall>x\<in> span C. \<forall>c. g (c*\<^sub>R x) = c *\<^sub>R g x)
           \<and> (\<forall>x\<in> C. g x = f x)" by blast
  from g show ?thesis unfolding linear_def using C
    apply clarsimp by blast
qed

(* Can construct an isomorphism between spaces of same dimension.            *)

lemma card_le_inj: assumes fA: "finite A" and fB: "finite B"
  and c: "card A \<le> card B" shows "(\<exists>f. f ` A \<subseteq> B \<and> inj_on f A)"
using fB c
proof(induct arbitrary: B rule: finite_induct[OF fA])
  case 1 thus ?case by simp
next
  case (2 x s t)
  thus ?case
  proof(induct rule: finite_induct[OF "2.prems"(1)])
    case 1    then show ?case by simp
  next
    case (2 y t)
    from "2.prems"(1,2,5) "2.hyps"(1,2) have cst:"card s \<le> card t" by simp
    from "2.prems"(3) [OF "2.hyps"(1) cst] obtain f where
      f: "f ` s \<subseteq> t \<and> inj_on f s" by blast
    from f "2.prems"(2) "2.hyps"(2) show ?case
      apply -
      apply (rule exI[where x = "\<lambda>z. if z = x then y else f z"])
      by (auto simp add: inj_on_def)
  qed
qed

lemma card_subset_eq: assumes fB: "finite B" and AB: "A \<subseteq> B" and
  c: "card A = card B"
  shows "A = B"
proof-
  from fB AB have fA: "finite A" by (auto intro: finite_subset)
  from fA fB have fBA: "finite (B - A)" by auto
  have e: "A \<inter> (B - A) = {}" by blast
  have eq: "A \<union> (B - A) = B" using AB by blast
  from card_Un_disjoint[OF fA fBA e, unfolded eq c]
  have "card (B - A) = 0" by arith
  hence "B - A = {}" unfolding card_eq_0_iff using fA fB by simp
  with AB show "A = B" by blast
qed

lemma subspace_isomorphism:
  assumes s: "subspace (S:: (real ^'n) set)"
  and t: "subspace (T :: (real ^'m) set)"
  and d: "dim S = dim T"
  shows "\<exists>f. linear f \<and> f ` S = T \<and> inj_on f S"
proof-
  from basis_exists[of S] independent_bound obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" and fB: "finite B" by blast
  from basis_exists[of T] independent_bound obtain C where
    C: "C \<subseteq> T" "independent C" "T \<subseteq> span C" "card C = dim T" and fC: "finite C" by blast
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" using `finite B` `finite C` by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear g" "\<forall>x\<in> B. g x = f x" by blast
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by simp
  have "g ` B = f ` B" using g(2)
    by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B" using f(2) g(2)
    by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {fix x y assume x: "x \<in> S" and y: "y \<in> S" and gxy:"g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B" by blast+
    from gxy have th0: "g (x - y) = 0" by (simp add: linear_sub[OF g(1)])
    have th1: "x - y \<in> span B" using x' y' by (metis span_sub)
    have "x=y" using g0[OF th1 th0] by simp }
  then have giS: "inj_on g S"
    unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s]
  have "g ` S = span (g ` B)" by (simp add: span_linear_image[OF g(1)])
  also have "\<dots> = span C" unfolding gBC ..
  also have "\<dots> = T" using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS show ?thesis by blast
qed

(* linear functions are equal on a subspace if they are on a spanning set.   *)

lemma subspace_kernel:
  assumes lf: "linear f"
  shows "subspace {x. f x = 0}"
apply (simp add: subspace_def)
by (simp add: linear_add[OF lf] linear_cmul[OF lf] linear_0[OF lf])

lemma linear_eq_0_span:
  assumes lf: "linear f" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> span B. f x = 0"
proof
  fix x assume x: "x \<in> span B"
  let ?P = "\<lambda>x. f x = 0"
  from subspace_kernel[OF lf] have "subspace ?P" unfolding Collect_def .
  with x f0 span_induct[of B "?P" x] show "f x = 0" by blast
qed

lemma linear_eq_0:
  assumes lf: "linear f" and SB: "S \<subseteq> span B" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> S. f x = 0"
  by (metis linear_eq_0_span[OF lf] subset_eq SB f0)

lemma linear_eq:
  assumes lf: "linear f" and lg: "linear g" and S: "S \<subseteq> span B"
  and fg: "\<forall> x\<in> B. f x = g x"
  shows "\<forall>x\<in> S. f x = g x"
proof-
  let ?h = "\<lambda>x. f x - g x"
  from fg have fg': "\<forall>x\<in> B. ?h x = 0" by simp
  from linear_eq_0[OF linear_compose_sub[OF lf lg] S fg']
  show ?thesis by simp
qed

lemma linear_eq_stdbasis:
  assumes lf: "linear (f::real^'m \<Rightarrow> _)" and lg: "linear g"
  and fg: "\<forall>i. f (basis i) = g(basis i)"
  shows "f = g"
proof-
  let ?U = "UNIV :: 'm set"
  let ?I = "{basis i:: real^'m|i. i \<in> ?U}"
  {fix x assume x: "x \<in> (UNIV :: (real^'m) set)"
    from equalityD2[OF span_stdbasis]
    have IU: " (UNIV :: (real^'m) set) \<subseteq> span ?I" by blast
    from linear_eq[OF lf lg IU] fg x
    have "f x = g x" unfolding Collect_def  Ball_def mem_def by metis}
  then show ?thesis by (auto intro: ext)
qed

(* Similar results for bilinear functions.                                   *)

lemma bilinear_eq:
  assumes bf: "bilinear f"
  and bg: "bilinear g"
  and SB: "S \<subseteq> span B" and TC: "T \<subseteq> span C"
  and fg: "\<forall>x\<in> B. \<forall>y\<in> C. f x y = g x y"
  shows "\<forall>x\<in>S. \<forall>y\<in>T. f x y = g x y "
proof-
  let ?P = "\<lambda>x. \<forall>y\<in> span C. f x y = g x y"
  from bf bg have sp: "subspace ?P"
    unfolding bilinear_def linear_def subspace_def bf bg
    by(auto simp add: span_0 mem_def bilinear_lzero[OF bf] bilinear_lzero[OF bg] span_add Ball_def intro:  bilinear_ladd[OF bf])

  have "\<forall>x \<in> span B. \<forall>y\<in> span C. f x y = g x y"
    apply -
    apply (rule ballI)
    apply (rule span_induct[of B ?P])
    defer
    apply (rule sp)
    apply assumption
    apply (clarsimp simp add: Ball_def)
    apply (rule_tac P="\<lambda>y. f xa y = g xa y" and S=C in span_induct)
    using fg
    apply (auto simp add: subspace_def)
    using bf bg unfolding bilinear_def linear_def
    by(auto simp add: span_0 mem_def bilinear_rzero[OF bf] bilinear_rzero[OF bg] span_add Ball_def intro:  bilinear_ladd[OF bf])
  then show ?thesis using SB TC by (auto intro: ext)
qed

lemma bilinear_eq_stdbasis:
  assumes bf: "bilinear (f:: real^'m \<Rightarrow> real^'n \<Rightarrow> _)"
  and bg: "bilinear g"
  and fg: "\<forall>i j. f (basis i) (basis j) = g (basis i) (basis j)"
  shows "f = g"
proof-
  from fg have th: "\<forall>x \<in> {basis i| i. i\<in> (UNIV :: 'm set)}. \<forall>y\<in>  {basis j |j. j \<in> (UNIV :: 'n set)}. f x y = g x y" by blast
  from bilinear_eq[OF bf bg equalityD2[OF span_stdbasis] equalityD2[OF span_stdbasis] th] show ?thesis by (blast intro: ext)
qed

(* Detailed theorems about left and right invertibility in general case.     *)

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma linear_injective_left_inverse:
  assumes lf: "linear (f::real ^'n \<Rightarrow> real ^'m)" and fi: "inj f"
  shows "\<exists>g. linear g \<and> g o f = id"
proof-
  from linear_independent_extend[OF independent_injective_image, OF independent_stdbasis, OF lf fi]
  obtain h:: "real ^'m \<Rightarrow> real ^'n" where h: "linear h" " \<forall>x \<in> f ` {basis i|i. i \<in> (UNIV::'n set)}. h x = inv f x" by blast
  from h(2)
  have th: "\<forall>i. (h \<circ> f) (basis i) = id (basis i)"
    using inv_o_cancel[OF fi, unfolded stupid_ext[symmetric] id_def o_def]
    by auto

  from linear_eq_stdbasis[OF linear_compose[OF lf h(1)] linear_id th]
  have "h o f = id" .
  then show ?thesis using h(1) by blast
qed

lemma linear_surjective_right_inverse:
  assumes lf: "linear (f:: real ^'m \<Rightarrow> real ^'n)" and sf: "surj f"
  shows "\<exists>g. linear g \<and> f o g = id"
proof-
  from linear_independent_extend[OF independent_stdbasis]
  obtain h:: "real ^'n \<Rightarrow> real ^'m" where
    h: "linear h" "\<forall> x\<in> {basis i| i. i\<in> (UNIV :: 'n set)}. h x = inv f x" by blast
  from h(2)
  have th: "\<forall>i. (f o h) (basis i) = id (basis i)"
    using sf
    apply (auto simp add: surj_iff o_def stupid_ext[symmetric])
    apply (erule_tac x="basis i" in allE)
    by auto

  from linear_eq_stdbasis[OF linear_compose[OF h(1) lf] linear_id th]
  have "f o h = id" .
  then show ?thesis using h(1) by blast
qed

lemma matrix_left_invertible_injective:
"(\<exists>B. (B::real^'m^'n) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
proof-
  {fix B:: "real^'m^'n" and x y assume B: "B ** A = mat 1" and xy: "A *v x = A*v y"
    from xy have "B*v (A *v x) = B *v (A*v y)" by simp
    hence "x = y"
      unfolding matrix_vector_mul_assoc B matrix_vector_mul_lid .}
  moreover
  {assume A: "\<forall>x y. A *v x = A *v y \<longrightarrow> x = y"
    hence i: "inj (op *v A)" unfolding inj_on_def by auto
    from linear_injective_left_inverse[OF matrix_vector_mul_linear i]
    obtain g where g: "linear g" "g o op *v A = id" by blast
    have "matrix g ** A = mat 1"
      unfolding matrix_eq matrix_vector_mul_lid matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) by (simp add: o_def id_def stupid_ext)
    then have "\<exists>B. (B::real ^'m^'n) ** A = mat 1" by blast}
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::real ^'m^'n) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using linear_injective_0[OF matrix_vector_mul_linear, of A]
  by (simp add: inj_on_def)

lemma matrix_right_invertible_surjective:
"(\<exists>B. (A::real^'n^'m) ** (B::real^'m^'n) = mat 1) \<longleftrightarrow> surj (\<lambda>x. A *v x)"
proof-
  {fix B :: "real ^'m^'n"  assume AB: "A ** B = mat 1"
    {fix x :: "real ^ 'm"
      have "A *v (B *v x) = x"
        by (simp add: matrix_vector_mul_lid matrix_vector_mul_assoc AB)}
    hence "surj (op *v A)" unfolding surj_def by metis }
  moreover
  {assume sf: "surj (op *v A)"
    from linear_surjective_right_inverse[OF matrix_vector_mul_linear sf]
    obtain g:: "real ^'m \<Rightarrow> real ^'n" where g: "linear g" "op *v A o g = id"
      by blast

    have "A ** (matrix g) = mat 1"
      unfolding matrix_eq  matrix_vector_mul_lid
        matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) unfolding o_def stupid_ext[symmetric] id_def
      .
    hence "\<exists>B. A ** (B::real^'m^'n) = mat 1" by blast
  }
  ultimately show ?thesis unfolding surj_def by blast
qed

lemma matrix_left_invertible_independent_columns:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real ^'m^'n). B ** A = mat 1) \<longleftrightarrow> (\<forall>c. setsum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?U = "UNIV :: 'n set"
  {assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    {fix c i assume c: "setsum (\<lambda>i. c i *s column i A) ?U = 0"
      and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        unfolding matrix_mult_vsum Cart_eq
        by auto
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector Cart_eq)}
    hence ?rhs by blast}
  moreover
  {assume H: ?rhs
    {fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: real)"
      from H[rule_format, of ?c, unfolded matrix_mult_vsum[symmetric], OF x]
      have "x = 0" by vector}}
  ultimately show ?thesis unfolding matrix_left_invertible_ker by blast
qed

lemma matrix_right_invertible_independent_rows:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real^'m^'n). A ** B = mat 1) \<longleftrightarrow> (\<forall>c. setsum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add: column_transpose)

lemma matrix_right_invertible_span_columns:
  "(\<exists>(B::real ^'n^'m). (A::real ^'m^'n) ** B = mat 1) \<longleftrightarrow> span (columns A) = UNIV" (is "?lhs = ?rhs")
proof-
  let ?U = "UNIV :: 'm set"
  have fU: "finite ?U" by simp
  have lhseq: "?lhs \<longleftrightarrow> (\<forall>y. \<exists>(x::real^'m). setsum (\<lambda>i. (x$i) *s column i A) ?U = y)"
    unfolding matrix_right_invertible_surjective matrix_mult_vsum surj_def
    apply (subst eq_commute) ..
  have rhseq: "?rhs \<longleftrightarrow> (\<forall>x. x \<in> span (columns A))" by blast
  {assume h: ?lhs
    {fix x:: "real ^'n"
        from h[unfolded lhseq, rule_format, of x] obtain y:: "real ^'m"
          where y: "setsum (\<lambda>i. (y$i) *s column i A) ?U = x" by blast
        have "x \<in> span (columns A)"
          unfolding y[symmetric]
          apply (rule span_setsum[OF fU])
          apply clarify
          unfolding smult_conv_scaleR
          apply (rule span_mul)
          apply (rule span_superset)
          unfolding columns_def
          by blast}
    then have ?rhs unfolding rhseq by blast}
  moreover
  {assume h:?rhs
    let ?P = "\<lambda>(y::real ^'n). \<exists>(x::real^'m). setsum (\<lambda>i. (x$i) *s column i A) ?U = y"
    {fix y have "?P y"
      proof(rule span_induct_alt[of ?P "columns A", folded smult_conv_scaleR])
        show "\<exists>x\<Colon>real ^ 'm. setsum (\<lambda>i. (x$i) *s column i A) ?U = 0"
          by (rule exI[where x=0], simp)
      next
        fix c y1 y2 assume y1: "y1 \<in> columns A" and y2: "?P y2"
        from y1 obtain i where i: "i \<in> ?U" "y1 = column i A"
          unfolding columns_def by blast
        from y2 obtain x:: "real ^'m" where
          x: "setsum (\<lambda>i. (x$i) *s column i A) ?U = y2" by blast
        let ?x = "(\<chi> j. if j = i then c + (x$i) else (x$j))::real^'m"
        show "?P (c*s y1 + y2)"
          proof(rule exI[where x= "?x"], vector, auto simp add: i x[symmetric] cond_value_iff right_distrib cond_application_beta cong del: if_weak_cong)
            fix j
            have th: "\<forall>xa \<in> ?U. (if xa = i then (c + (x$i)) * ((column xa A)$j)
           else (x$xa) * ((column xa A$j))) = (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))" using i(1)
              by (simp add: field_simps)
            have "setsum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
           else (x$xa) * ((column xa A$j))) ?U = setsum (\<lambda>xa. (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))) ?U"
              apply (rule setsum_cong[OF refl])
              using th by blast
            also have "\<dots> = setsum (\<lambda>xa. if xa = i then c * ((column i A)$j) else 0) ?U + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
              by (simp add: setsum_addf)
            also have "\<dots> = c * ((column i A)$j) + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
              unfolding setsum_delta[OF fU]
              using i(1) by simp
            finally show "setsum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
           else (x$xa) * ((column xa A$j))) ?U = c * ((column i A)$j) + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U" .
          qed
        next
          show "y \<in> span (columns A)" unfolding h by blast
        qed}
    then have ?lhs unfolding lhseq ..}
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_span_rows:
  "(\<exists>(B::real^'m^'n). B ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> span (rows A) = UNIV"
  unfolding right_invertible_transpose[symmetric]
  unfolding columns_transpose[symmetric]
  unfolding matrix_right_invertible_span_columns
 ..

(* An injective map real^'n->real^'n is also surjective.                       *)

lemma linear_injective_imp_surjective:
  assumes lf: "linear (f:: real ^'n \<Rightarrow> real ^'n)" and fi: "inj f"
  shows "surj f"
proof-
  let ?U = "UNIV :: (real ^'n) set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "card B = dim ?U"
    by blast
  from B(4) have d: "dim ?U = card B" by simp
  have th: "?U \<subseteq> span (f ` B)"
    apply (rule card_ge_dim_independent)
    apply blast
    apply (rule independent_injective_image[OF B(2) lf fi])
    apply (rule order_eq_refl)
    apply (rule sym)
    unfolding d
    apply (rule card_image)
    apply (rule subset_inj_on[OF fi])
    by blast
  from th show ?thesis
    unfolding span_linear_image[OF lf] surj_def
    using B(3) by blast
qed

(* And vice versa.                                                           *)

lemma surjective_iff_injective_gen:
  assumes fS: "finite S" and fT: "finite T" and c: "card S = card T"
  and ST: "f ` S \<subseteq> T"
  shows "(\<forall>y \<in> T. \<exists>x \<in> S. f x = y) \<longleftrightarrow> inj_on f S" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume h: "?lhs"
    {fix x y assume x: "x \<in> S" and y: "y \<in> S" and f: "f x = f y"
      from x fS have S0: "card S \<noteq> 0" by auto
      {assume xy: "x \<noteq> y"
        have th: "card S \<le> card (f ` (S - {y}))"
          unfolding c
          apply (rule card_mono)
          apply (rule finite_imageI)
          using fS apply simp
          using h xy x y f unfolding subset_eq image_iff
          apply auto
          apply (case_tac "xa = f x")
          apply (rule bexI[where x=x])
          apply auto
          done
        also have " \<dots> \<le> card (S -{y})"
          apply (rule card_image_le)
          using fS by simp
        also have "\<dots> \<le> card S - 1" using y fS by simp
        finally have False  using S0 by arith }
      then have "x = y" by blast}
    then have ?rhs unfolding inj_on_def by blast}
  moreover
  {assume h: ?rhs
    have "f ` S = T"
      apply (rule card_subset_eq[OF fT ST])
      unfolding card_image[OF h] using c .
    then have ?lhs by blast}
  ultimately show ?thesis by blast
qed

lemma linear_surjective_imp_injective:
  assumes lf: "linear (f::real ^'n => real ^'n)" and sf: "surj f"
  shows "inj f"
proof-
  let ?U = "UNIV :: (real ^'n) set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" and d: "card B = dim ?U"
    by blast
  {fix x assume x: "x \<in> span B" and fx: "f x = 0"
    from B(2) have fB: "finite B" using independent_bound by auto
    have fBi: "independent (f ` B)"
      apply (rule card_le_dim_spanning[of "f ` B" ?U])
      apply blast
      using sf B(3)
      unfolding span_linear_image[OF lf] surj_def subset_eq image_iff
      apply blast
      using fB apply (blast intro: finite_imageI)
      unfolding d[symmetric]
      apply (rule card_image_le)
      apply (rule fB)
      done
    have th0: "dim ?U \<le> card (f ` B)"
      apply (rule span_card_ge_dim)
      apply blast
      unfolding span_linear_image[OF lf]
      apply (rule subset_trans[where B = "f ` UNIV"])
      using sf unfolding surj_def apply blast
      apply (rule image_mono)
      apply (rule B(3))
      apply (metis finite_imageI fB)
      done

    moreover have "card (f ` B) \<le> card B"
      by (rule card_image_le, rule fB)
    ultimately have th1: "card B = card (f ` B)" unfolding d by arith
    have fiB: "inj_on f B"
      unfolding surjective_iff_injective_gen[OF fB finite_imageI[OF fB] th1 subset_refl, symmetric] by blast
    from linear_indep_image_lemma[OF lf fB fBi fiB x] fx
    have "x = 0" by blast}
  note th = this
  from th show ?thesis unfolding linear_injective_0[OF lf]
    using B(3) by blast
qed

(* Hence either is enough for isomorphism.                                   *)

lemma left_right_inverse_eq:
  assumes fg: "f o g = id" and gh: "g o h = id"
  shows "f = h"
proof-
  have "f = f o (g o h)" unfolding gh by simp
  also have "\<dots> = (f o g) o h" by (simp add: o_assoc)
  finally show "f = h" unfolding fg by simp
qed

lemma isomorphism_expand:
  "f o g = id \<and> g o f = id \<longleftrightarrow> (\<forall>x. f(g x) = x) \<and> (\<forall>x. g(f x) = x)"
  by (simp add: expand_fun_eq o_def id_def)

lemma linear_injective_isomorphism:
  assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'n)" and fi: "inj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
unfolding isomorphism_expand[symmetric]
using linear_surjective_right_inverse[OF lf linear_injective_imp_surjective[OF lf fi]] linear_injective_left_inverse[OF lf fi]
by (metis left_right_inverse_eq)

lemma linear_surjective_isomorphism:
  assumes lf: "linear (f::real ^'n \<Rightarrow> real ^'n)" and sf: "surj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
unfolding isomorphism_expand[symmetric]
using linear_surjective_right_inverse[OF lf sf] linear_injective_left_inverse[OF lf linear_surjective_imp_injective[OF lf sf]]
by (metis left_right_inverse_eq)

(* Left and right inverses are the same for R^N->R^N.                        *)

lemma linear_inverse_left:
  assumes lf: "linear (f::real ^'n \<Rightarrow> real ^'n)" and lf': "linear f'"
  shows "f o f' = id \<longleftrightarrow> f' o f = id"
proof-
  {fix f f':: "real ^'n \<Rightarrow> real ^'n"
    assume lf: "linear f" "linear f'" and f: "f o f' = id"
    from f have sf: "surj f"

      apply (auto simp add: o_def stupid_ext[symmetric] id_def surj_def)
      by metis
    from linear_surjective_isomorphism[OF lf(1) sf] lf f
    have "f' o f = id" unfolding stupid_ext[symmetric] o_def id_def
      by metis}
  then show ?thesis using lf lf' by metis
qed

(* Moreover, a one-sided inverse is automatically linear.                    *)

lemma left_inverse_linear:
  assumes lf: "linear (f::real ^'n \<Rightarrow> real ^'n)" and gf: "g o f = id"
  shows "linear g"
proof-
  from gf have fi: "inj f" apply (auto simp add: inj_on_def o_def id_def stupid_ext[symmetric])
    by metis
  from linear_injective_isomorphism[OF lf fi]
  obtain h:: "real ^'n \<Rightarrow> real ^'n" where
    h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x" by blast
  have "h = g" apply (rule ext) using gf h(2,3)
    apply (simp add: o_def id_def stupid_ext[symmetric])
    by metis
  with h(1) show ?thesis by blast
qed

lemma right_inverse_linear:
  assumes lf: "linear (f:: real ^'n \<Rightarrow> real ^'n)" and gf: "f o g = id"
  shows "linear g"
proof-
  from gf have fi: "surj f" apply (auto simp add: surj_def o_def id_def stupid_ext[symmetric])
    by metis
  from linear_surjective_isomorphism[OF lf fi]
  obtain h:: "real ^'n \<Rightarrow> real ^'n" where
    h: "linear h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x" by blast
  have "h = g" apply (rule ext) using gf h(2,3)
    apply (simp add: o_def id_def stupid_ext[symmetric])
    by metis
  with h(1) show ?thesis by blast
qed

(* The same result in terms of square matrices.                              *)

lemma matrix_left_right_inverse:
  fixes A A' :: "real ^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof-
  {fix A A' :: "real ^'n^'n" assume AA': "A ** A' = mat 1"
    have sA: "surj (op *v A)"
      unfolding surj_def
      apply clarify
      apply (rule_tac x="(A' *v y)" in exI)
      by (simp add: matrix_vector_mul_assoc AA' matrix_vector_mul_lid)
    from linear_surjective_isomorphism[OF matrix_vector_mul_linear sA]
    obtain f' :: "real ^'n \<Rightarrow> real ^'n"
      where f': "linear f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)] matrix_vector_mul_assoc[symmetric] matrix_vector_mul_lid f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'" by (simp add: matrix_mul_assoc[symmetric] AA' matrix_mul_rid matrix_mul_lid)
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)}
  then show ?thesis by blast
qed

(* Considering an n-element vector as an n-by-1 or 1-by-n matrix.            *)

definition "rowvector v = (\<chi> i j. (v$j))"

definition "columnvector v = (\<chi> i j. (v$i))"

lemma transpose_columnvector:
 "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def Cart_eq)

lemma transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def Cart_eq)

lemma dot_rowvector_columnvector:
  "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product: "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vector_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
unfolding dot_matrix_product transpose_columnvector[symmetric]
  dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..

(* Infinity norm.                                                            *)

definition "infnorm (x::real^'n) = Sup {abs(x$i) |i. i\<in> (UNIV :: 'n set)}"

lemma numseg_dimindex_nonempty: "\<exists>i. i \<in> (UNIV :: 'n set)"
  by auto

lemma infnorm_set_image:
  "{abs(x$i) |i. i\<in> (UNIV :: _ set)} =
  (\<lambda>i. abs(x$i)) ` (UNIV)" by blast

lemma infnorm_set_lemma:
  shows "finite {abs((x::'a::abs ^'n)$i) |i. i\<in> (UNIV :: 'n set)}"
  and "{abs(x$i) |i. i\<in> (UNIV :: 'n::finite set)} \<noteq> {}"
  unfolding infnorm_set_image
  by (auto intro: finite_imageI)

lemma infnorm_pos_le: "0 \<le> infnorm (x::real^'n)"
  unfolding infnorm_def
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]
  unfolding infnorm_set_image
  by auto

lemma infnorm_triangle: "infnorm ((x::real^'n) + y) \<le> infnorm x + infnorm y"
proof-
  have th: "\<And>x y (z::real). x - y <= z \<longleftrightarrow> x - z <= y" by arith
  have th1: "\<And>S f. f ` S = { f i| i. i \<in> S}" by blast
  have th2: "\<And>x (y::real). abs(x + y) - abs(x) <= abs(y)" by arith
  show ?thesis
  unfolding infnorm_def
  unfolding Sup_finite_le_iff[ OF infnorm_set_lemma]
  apply (subst diff_le_eq[symmetric])
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]
  unfolding infnorm_set_image bex_simps
  apply (subst th)
  unfolding th1
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]

  unfolding infnorm_set_image ball_simps bex_simps
  apply simp
  apply (metis th2)
  done
qed

lemma infnorm_eq_0: "infnorm x = 0 \<longleftrightarrow> (x::real ^'n) = 0"
proof-
  have "infnorm x <= 0 \<longleftrightarrow> x = 0"
    unfolding infnorm_def
    unfolding Sup_finite_le_iff[OF infnorm_set_lemma]
    unfolding infnorm_set_image ball_simps
    by vector
  then show ?thesis using infnorm_pos_le[of x] by simp
qed

lemma infnorm_0: "infnorm 0 = 0"
  by (simp add: infnorm_eq_0)

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  unfolding infnorm_def
  apply (rule cong[of "Sup" "Sup"])
  apply blast
  apply (rule set_ext)
  apply auto
  done

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
proof-
  have "y - x = - (x - y)" by simp
  then show ?thesis  by (metis infnorm_neg)
qed

lemma real_abs_sub_infnorm: "\<bar> infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
proof-
  have th: "\<And>(nx::real) n ny. nx <= n + ny \<Longrightarrow> ny <= n + nx ==> \<bar>nx - ny\<bar> <= n"
    by arith
  from infnorm_triangle[of "x - y" " y"] infnorm_triangle[of "x - y" "-x"]
  have ths: "infnorm x \<le> infnorm (x - y) + infnorm y"
    "infnorm y \<le> infnorm (x - y) + infnorm x"
    by (simp_all add: field_simps infnorm_neg diff_def[symmetric])
  from th[OF ths]  show ?thesis .
qed

lemma real_abs_infnorm: " \<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma component_le_infnorm:
  shows "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
proof-
  let ?U = "UNIV :: 'n set"
  let ?S = "{\<bar>x$i\<bar> |i. i\<in> ?U}"
  have fS: "finite ?S" unfolding image_Collect[symmetric]
    apply (rule finite_imageI) unfolding Collect_def mem_def by simp
  have S0: "?S \<noteq> {}" by blast
  have th1: "\<And>S f. f ` S = { f i| i. i \<in> S}" by blast
  from Sup_finite_in[OF fS S0] 
  show ?thesis unfolding infnorm_def infnorm_set_image 
    by (metis Sup_finite_ge_iff finite finite_imageI UNIV_not_empty image_is_empty 
              rangeI real_le_refl)
qed

lemma infnorm_mul_lemma: "infnorm(a *s x) <= \<bar>a\<bar> * infnorm x"
  apply (subst infnorm_def)
  unfolding Sup_finite_le_iff[OF infnorm_set_lemma]
  unfolding infnorm_set_image ball_simps
  apply (simp add: abs_mult)
  apply (rule allI)
  apply (cut_tac component_le_infnorm[of x])
  apply (rule mult_mono)
  apply auto
  done

lemma infnorm_mul: "infnorm(a *s x) = abs a * infnorm x"
proof-
  {assume a0: "a = 0" hence ?thesis by (simp add: infnorm_0) }
  moreover
  {assume a0: "a \<noteq> 0"
    from a0 have th: "(1/a) *s (a *s x) = x"
      by (simp add: vector_smult_assoc)
    from a0 have ap: "\<bar>a\<bar> > 0" by arith
    from infnorm_mul_lemma[of "1/a" "a *s x"]
    have "infnorm x \<le> 1/\<bar>a\<bar> * infnorm (a*s x)"
      unfolding th by simp
    with ap have "\<bar>a\<bar> * infnorm x \<le> \<bar>a\<bar> * (1/\<bar>a\<bar> * infnorm (a *s x))" by (simp add: field_simps)
    then have "\<bar>a\<bar> * infnorm x \<le> infnorm (a*s x)"
      using ap by (simp add: field_simps)
    with infnorm_mul_lemma[of a x] have ?thesis by arith }
  ultimately show ?thesis by blast
qed

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  using infnorm_pos_le[of x] infnorm_eq_0[of x] by arith

(* Prove that it differs only up to a bound from Euclidean norm.             *)

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  unfolding infnorm_def Sup_finite_le_iff[OF infnorm_set_lemma]
  unfolding infnorm_set_image  ball_simps
  by (metis component_le_norm)
lemma card_enum: "card {1 .. n} = n" by auto
lemma norm_le_infnorm: "norm(x) <= sqrt(real CARD('n)) * infnorm(x::real ^'n)"
proof-
  let ?d = "CARD('n)"
  have "real ?d \<ge> 0" by simp
  hence d2: "(sqrt (real ?d))^2 = real ?d"
    by (auto intro: real_sqrt_pow2)
  have th: "sqrt (real ?d) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff infnorm_pos_le)
  have th1: "x \<bullet> x \<le> (sqrt (real ?d) * infnorm x)^2"
    unfolding power_mult_distrib d2
    unfolding real_of_nat_def inner_vector_def
    apply (subst power2_abs[symmetric]) 
    apply (rule setsum_bounded)
    apply(auto simp add: power2_eq_square[symmetric])
    apply (subst power2_abs[symmetric])
    apply (rule power_mono)
    unfolding infnorm_def  Sup_finite_ge_iff[OF infnorm_set_lemma]
    unfolding infnorm_set_image bex_simps apply(rule_tac x=i in exI) by auto
  from real_le_lsqrt[OF inner_ge_zero th th1]
  show ?thesis unfolding norm_eq_sqrt_inner id_def .
qed

(* Equality in Cauchy-Schwarz and triangle inequalities.                     *)

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume h: "x = 0"
    hence ?thesis by simp}
  moreover
  {assume h: "y = 0"
    hence ?thesis by simp}
  moreover
  {assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    from inner_eq_zero_iff[of "norm y *\<^sub>R x - norm x *\<^sub>R y"]
    have "?rhs \<longleftrightarrow> (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) - norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) =  0)"
      using x y
      unfolding inner_simps smult_conv_scaleR
      unfolding power2_norm_eq_inner[symmetric] power2_eq_square diff_eq_0_iff_eq apply (simp add: inner_commute)
      apply (simp add: field_simps) by metis
    also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)" using x y
      by (simp add: field_simps inner_commute)
    also have "\<dots> \<longleftrightarrow> ?lhs" using x y
      apply simp
      by metis
    finally have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_abs_eq:
  shows "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow>
                norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm(x) *\<^sub>R y = - norm y *\<^sub>R x" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have th: "\<And>(x::real) a. a \<ge> 0 \<Longrightarrow> abs x = a \<longleftrightarrow> x = a \<or> x = - a" by arith
  have "?rhs \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm (- x) *\<^sub>R y = norm y *\<^sub>R (- x)"
    by simp
  also have "\<dots> \<longleftrightarrow>(x \<bullet> y = norm x * norm y \<or>
     (-x) \<bullet> y = norm x * norm y)"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding norm_minus_cancel norm_scaleR ..
  also have "\<dots> \<longleftrightarrow> ?lhs"
    unfolding th[OF mult_nonneg_nonneg, OF norm_ge_zero[of x] norm_ge_zero[of y]] inner_simps by auto
  finally show ?thesis ..
qed

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm(x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
proof-
  {assume x: "x =0 \<or> y =0"
    hence ?thesis by (cases "x=0", simp_all)}
  moreover
  {assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    hence "norm x \<noteq> 0" "norm y \<noteq> 0"
      by simp_all
    hence n: "norm x > 0" "norm y > 0"
      using norm_ge_zero[of x] norm_ge_zero[of y]
      by arith+
    have th: "\<And>(a::real) b c. a + b + c \<noteq> 0 ==> (a = b + c \<longleftrightarrow> a^2 = (b + c)^2)" by algebra
    have "norm(x + y) = norm x + norm y \<longleftrightarrow> norm(x + y)^ 2 = (norm x + norm y) ^2"
      apply (rule th) using n norm_ge_zero[of "x + y"]
      by arith
    also have "\<dots> \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
      unfolding norm_cauchy_schwarz_eq[symmetric]
      unfolding power2_norm_eq_inner inner_simps
      by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square inner_commute field_simps)
    finally have ?thesis .}
  ultimately show ?thesis by blast
qed

(* Collinearity.*)

definition
  collinear :: "'a::real_vector set \<Rightarrow> bool" where
  "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_empty:  "collinear {}" by (simp add: collinear_def)

lemma collinear_sing: "collinear {x}"
  by (simp add: collinear_def)

lemma collinear_2: "collinear {x, y}"
  apply (simp add: collinear_def)
  apply (rule exI[where x="x - y"])
  apply auto
  apply (rule exI[where x=1], simp)
  apply (rule exI[where x="- 1"], simp)
  done

lemma collinear_lemma: "collinear {0,x,y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume "x=0 \<or> y = 0" hence ?thesis
      by (cases "x = 0", simp_all add: collinear_2 insert_commute)}
  moreover
  {assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    {assume h: "?lhs"
      then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *\<^sub>R u" unfolding collinear_def by blast
      from u[rule_format, of x 0] u[rule_format, of y 0]
      obtain cx and cy where
        cx: "x = cx *\<^sub>R u" and cy: "y = cy *\<^sub>R u"
        by auto
      from cx x have cx0: "cx \<noteq> 0" by auto
      from cy y have cy0: "cy \<noteq> 0" by auto
      let ?d = "cy / cx"
      from cx cy cx0 have "y = ?d *\<^sub>R x"
        by (simp add: vector_smult_assoc)
      hence ?rhs using x y by blast}
    moreover
    {assume h: "?rhs"
      then obtain c where c: "y = c *\<^sub>R x" using x y by blast
      have ?lhs unfolding collinear_def c
        apply (rule exI[where x=x])
        apply auto
        apply (rule exI[where x="- 1"], simp)
        apply (rule exI[where x= "-c"], simp)
        apply (rule exI[where x=1], simp)
        apply (rule exI[where x="1 - c"], simp add: scaleR_left_diff_distrib)
        apply (rule exI[where x="c - 1"], simp add: scaleR_left_diff_distrib)
        done}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_equal:
  shows "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow> collinear {0,x,y}"
unfolding norm_cauchy_schwarz_abs_eq
apply (cases "x=0", simp_all add: collinear_2)
apply (cases "y=0", simp_all add: collinear_2 insert_commute)
unfolding collinear_lemma
apply simp
apply (subgoal_tac "norm x \<noteq> 0")
apply (subgoal_tac "norm y \<noteq> 0")
apply (rule iffI)
apply (cases "norm x *\<^sub>R y = norm y *\<^sub>R x")
apply (rule exI[where x="(1/norm x) * norm y"])
apply (drule sym)
unfolding scaleR_scaleR[symmetric]
apply (simp add: vector_smult_assoc field_simps)
apply (rule exI[where x="(1/norm x) * - norm y"])
apply clarify
apply (drule sym)
unfolding scaleR_scaleR[symmetric]
apply (simp add: vector_smult_assoc field_simps)
apply (erule exE)
apply (erule ssubst)
unfolding scaleR_scaleR
unfolding norm_scaleR
apply (subgoal_tac "norm x * c = \<bar>c\<bar> * norm x \<or> norm x * c = - \<bar>c\<bar> * norm x")
apply (case_tac "c <= 0", simp add: field_simps)
apply (simp add: field_simps)
apply (case_tac "c <= 0", simp add: field_simps)
apply (simp add: field_simps)
apply simp
apply simp
done

end

(*  Title:      Library/Euclidean_Space
    Author:     Amine Chaieb, University of Cambridge
*)

header {* (Real) Vectors in Euclidean space, and elementary linear algebra.*}

theory Euclidean_Space
imports
  Complex_Main "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
  Finite_Cartesian_Product Glbs Infinite_Set Numeral_Type
  Inner_Product
uses "positivstellensatz.ML" ("normarith.ML")
begin

text{* Some common special cases.*}

lemma forall_1: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis num1_eq_iff)

lemma exhaust_2:
  fixes x :: 2 shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3 shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma UNIV_1: "UNIV = {1::1}"
  by (auto simp add: num1_eq_iff)

lemma UNIV_2: "UNIV = {1::2, 2::2}"
  using exhaust_2 by auto

lemma UNIV_3: "UNIV = {1::3, 2::3, 3::3}"
  using exhaust_3 by auto

lemma setsum_1: "setsum f (UNIV::1 set) = f 1"
  unfolding UNIV_1 by simp

lemma setsum_2: "setsum f (UNIV::2 set) = f 1 + f 2"
  unfolding UNIV_2 by simp

lemma setsum_3: "setsum f (UNIV::3 set) = f 1 + f 2 + f 3"
  unfolding UNIV_3 by (simp add: add_ac)

subsection{* Basic componentwise operations on vectors. *}

instantiation "^" :: (plus,type) plus
begin
definition  vector_add_def : "op + \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) + (y$i)))"
instance ..
end

instantiation "^" :: (times,type) times
begin
  definition vector_mult_def : "op * \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) * (y$i)))"
  instance ..
end

instantiation "^" :: (minus,type) minus begin
  definition vector_minus_def : "op - \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) - (y$i)))"
instance ..
end

instantiation "^" :: (uminus,type) uminus begin
  definition vector_uminus_def : "uminus \<equiv> (\<lambda> x.  (\<chi> i. - (x$i)))"
instance ..
end
instantiation "^" :: (zero,type) zero begin
  definition vector_zero_def : "0 \<equiv> (\<chi> i. 0)"
instance ..
end

instantiation "^" :: (one,type) one begin
  definition vector_one_def : "1 \<equiv> (\<chi> i. 1)"
instance ..
end

instantiation "^" :: (ord,type) ord
 begin
definition vector_less_eq_def:
  "less_eq (x :: 'a ^'b) y = (ALL i. x$i <= y$i)"
definition vector_less_def: "less (x :: 'a ^'b) y = (ALL i. x$i < y$i)"

instance by (intro_classes)
end

instantiation "^" :: (scaleR, type) scaleR
begin
definition vector_scaleR_def: "scaleR = (\<lambda> r x.  (\<chi> i. scaleR r (x$i)))"
instance ..
end

text{* Also the scalar-vector multiplication. *}

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"

text{* Constant Vectors *} 

definition "vec x = (\<chi> i. x)"

text{* Dot products. *}

definition dot :: "'a::{comm_monoid_add, times} ^ 'n \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a" (infix "\<bullet>" 70) where
  "x \<bullet> y = setsum (\<lambda>i. x$i * y$i) UNIV"

lemma dot_1[simp]: "(x::'a::{comm_monoid_add, times}^1) \<bullet> y = (x$1) * (y$1)"
  by (simp add: dot_def setsum_1)

lemma dot_2[simp]: "(x::'a::{comm_monoid_add, times}^2) \<bullet> y = (x$1) * (y$1) + (x$2) * (y$2)"
  by (simp add: dot_def setsum_2)

lemma dot_3[simp]: "(x::'a::{comm_monoid_add, times}^3) \<bullet> y = (x$1) * (y$1) + (x$2) * (y$2) + (x$3) * (y$3)"
  by (simp add: dot_def setsum_3)

subsection {* A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space. *}

method_setup vector = {*
let
  val ss1 = HOL_basic_ss addsimps [@{thm dot_def}, @{thm setsum_addf} RS sym,
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

lemma vec_component [simp]: "(vec x :: 'a ^ 'n)$i = x"
  by (vector vec_def)

lemma vector_add_component [simp]:
  fixes x y :: "'a::{plus} ^ 'n"
  shows "(x + y)$i = x$i + y$i"
  by vector

lemma vector_minus_component [simp]:
  fixes x y :: "'a::{minus} ^ 'n"
  shows "(x - y)$i = x$i - y$i"
  by vector

lemma vector_mult_component [simp]:
  fixes x y :: "'a::{times} ^ 'n"
  shows "(x * y)$i = x$i * y$i"
  by vector

lemma vector_smult_component [simp]:
  fixes y :: "'a::{times} ^ 'n"
  shows "(c *s y)$i = c * (y$i)"
  by vector

lemma vector_uminus_component [simp]:
  fixes x :: "'a::{uminus} ^ 'n"
  shows "(- x)$i = - (x$i)"
  by vector

lemma vector_scaleR_component [simp]:
  fixes x :: "'a::scaleR ^ 'n"
  shows "(scaleR r x)$i = scaleR r (x$i)"
  by vector

lemma cond_component: "(if b then x else y)$i = (if b then x$i else y$i)" by vector

lemmas vector_component =
  vec_component vector_add_component vector_mult_component
  vector_smult_component vector_minus_component vector_uminus_component
  vector_scaleR_component cond_component

subsection {* Some frequently useful arithmetic lemmas over vectors. *}

instance "^" :: (semigroup_add,type) semigroup_add
  apply (intro_classes) by (vector add_assoc)


instance "^" :: (monoid_add,type) monoid_add
  apply (intro_classes) by vector+

instance "^" :: (group_add,type) group_add
  apply (intro_classes) by (vector algebra_simps)+

instance "^" :: (ab_semigroup_add,type) ab_semigroup_add
  apply (intro_classes) by (vector add_commute)

instance "^" :: (comm_monoid_add,type) comm_monoid_add
  apply (intro_classes) by vector

instance "^" :: (ab_group_add,type) ab_group_add
  apply (intro_classes) by vector+

instance "^" :: (cancel_semigroup_add,type) cancel_semigroup_add
  apply (intro_classes)
  by (vector Cart_eq)+

instance "^" :: (cancel_ab_semigroup_add,type) cancel_ab_semigroup_add
  apply (intro_classes)
  by (vector Cart_eq)

instance "^" :: (real_vector, type) real_vector
  by default (vector scaleR_left_distrib scaleR_right_distrib)+

instance "^" :: (semigroup_mult,type) semigroup_mult
  apply (intro_classes) by (vector mult_assoc)

instance "^" :: (monoid_mult,type) monoid_mult
  apply (intro_classes) by vector+

instance "^" :: (ab_semigroup_mult,type) ab_semigroup_mult
  apply (intro_classes) by (vector mult_commute)

instance "^" :: (ab_semigroup_idem_mult,type) ab_semigroup_idem_mult
  apply (intro_classes) by (vector mult_idem)

instance "^" :: (comm_monoid_mult,type) comm_monoid_mult
  apply (intro_classes) by vector

fun vector_power :: "('a::{one,times} ^'n) \<Rightarrow> nat \<Rightarrow> 'a^'n" where
  "vector_power x 0 = 1"
  | "vector_power x (Suc n) = x * vector_power x n"

instance "^" :: (semiring,type) semiring
  apply (intro_classes) by (vector ring_simps)+

instance "^" :: (semiring_0,type) semiring_0
  apply (intro_classes) by (vector ring_simps)+
instance "^" :: (semiring_1,type) semiring_1
  apply (intro_classes) by vector
instance "^" :: (comm_semiring,type) comm_semiring
  apply (intro_classes) by (vector ring_simps)+

instance "^" :: (comm_semiring_0,type) comm_semiring_0 by (intro_classes)
instance "^" :: (cancel_comm_monoid_add, type) cancel_comm_monoid_add ..
instance "^" :: (semiring_0_cancel,type) semiring_0_cancel by (intro_classes)
instance "^" :: (comm_semiring_0_cancel,type) comm_semiring_0_cancel by (intro_classes)
instance "^" :: (ring,type) ring by (intro_classes)
instance "^" :: (semiring_1_cancel,type) semiring_1_cancel by (intro_classes)
instance "^" :: (comm_semiring_1,type) comm_semiring_1 by (intro_classes)

instance "^" :: (ring_1,type) ring_1 ..

instance "^" :: (real_algebra,type) real_algebra
  apply intro_classes
  apply (simp_all add: vector_scaleR_def ring_simps)
  apply vector
  apply vector
  done

instance "^" :: (real_algebra_1,type) real_algebra_1 ..

lemma of_nat_index:
  "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
  apply (induct n)
  apply vector
  apply vector
  done
lemma zero_index[simp]:
  "(0 :: 'a::zero ^'n)$i = 0" by vector

lemma one_index[simp]:
  "(1 :: 'a::one ^'n)$i = 1" by vector

lemma one_plus_of_nat_neq_0: "(1::'a::semiring_char_0) + of_nat n \<noteq> 0"
proof-
  have "(1::'a) + of_nat n = 0 \<longleftrightarrow> of_nat 1 + of_nat n = (of_nat 0 :: 'a)" by simp
  also have "\<dots> \<longleftrightarrow> 1 + n = 0" by (simp only: of_nat_add[symmetric] of_nat_eq_iff)
  finally show ?thesis by simp
qed

instance "^" :: (semiring_char_0,type) semiring_char_0
proof (intro_classes)
  fix m n ::nat
  show "(of_nat m :: 'a^'b) = of_nat n \<longleftrightarrow> m = n"
    by (simp add: Cart_eq of_nat_index)
qed

instance "^" :: (comm_ring_1,type) comm_ring_1 by intro_classes
instance "^" :: (ring_char_0,type) ring_char_0 by intro_classes

lemma vector_smult_assoc: "a *s (b *s x) = ((a::'a::semigroup_mult) * b) *s x"
  by (vector mult_assoc)
lemma vector_sadd_rdistrib: "((a::'a::semiring) + b) *s x = a *s x + b *s x"
  by (vector ring_simps)
lemma vector_add_ldistrib: "(c::'a::semiring) *s (x + y) = c *s x + c *s y"
  by (vector ring_simps)
lemma vector_smult_lzero[simp]: "(0::'a::mult_zero) *s x = 0" by vector
lemma vector_smult_lid[simp]: "(1::'a::monoid_mult) *s x = x" by vector
lemma vector_ssub_ldistrib: "(c::'a::ring) *s (x - y) = c *s x - c *s y"
  by (vector ring_simps)
lemma vector_smult_rneg: "(c::'a::ring) *s -x = -(c *s x)" by vector
lemma vector_smult_lneg: "- (c::'a::ring) *s x = -(c *s x)" by vector
lemma vector_sneg_minus1: "-x = (- (1::'a::ring_1)) *s x" by vector
lemma vector_smult_rzero[simp]: "c *s 0 = (0::'a::mult_zero ^ 'n)" by vector
lemma vector_sub_rdistrib: "((a::'a::ring) - b) *s x = a *s x - b *s x"
  by (vector ring_simps)

lemma vec_eq[simp]: "(vec m = vec n) \<longleftrightarrow> (m = n)"
  by (simp add: Cart_eq)

subsection {* Topological space *}

instantiation "^" :: (topological_space, finite) topological_space
begin

definition open_vector_def:
  "open (S :: ('a ^ 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A. (\<forall>i. open (A i) \<and> x$i \<in> A i) \<and>
      (\<forall>y. (\<forall>i. y$i \<in> A i) \<longrightarrow> y \<in> S))"

instance proof
  show "open (UNIV :: ('a ^ 'b) set)"
    unfolding open_vector_def by auto
next
  fix S T :: "('a ^ 'b) set"
  assume "open S" "open T" thus "open (S \<inter> T)"
    unfolding open_vector_def
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac Sa Ta)
    apply (rule_tac x="\<lambda>i. Sa i \<inter> Ta i" in exI)
    apply (simp add: open_Int)
    done
next
  fix K :: "('a ^ 'b) set set"
  assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_vector_def
    apply clarify
    apply (drule (1) bspec)
    apply (drule (1) bspec)
    apply clarify
    apply (rule_tac x=A in exI)
    apply fast
    done
qed

end

lemma open_vector_box: "\<forall>i. open (S i) \<Longrightarrow> open {x. \<forall>i. x $ i \<in> S i}"
unfolding open_vector_def by auto

lemma open_vimage_Cart_nth: "open S \<Longrightarrow> open ((\<lambda>x. x $ i) -` S)"
unfolding open_vector_def
apply clarify
apply (rule_tac x="\<lambda>k. if k = i then S else UNIV" in exI, simp)
done

lemma closed_vimage_Cart_nth: "closed S \<Longrightarrow> closed ((\<lambda>x. x $ i) -` S)"
unfolding closed_open vimage_Compl [symmetric]
by (rule open_vimage_Cart_nth)

lemma closed_vector_box: "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
proof -
  have "{x. \<forall>i. x $ i \<in> S i} = (\<Inter>i. (\<lambda>x. x $ i) -` S i)" by auto
  thus "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
    by (simp add: closed_INT closed_vimage_Cart_nth)
qed

lemma tendsto_Cart_nth [tendsto_intros]:
  assumes "((\<lambda>x. f x) ---> a) net"
  shows "((\<lambda>x. f x $ i) ---> a $ i) net"
proof (rule topological_tendstoI)
  fix S assume "open S" "a $ i \<in> S"
  then have "open ((\<lambda>y. y $ i) -` S)" "a \<in> ((\<lambda>y. y $ i) -` S)"
    by (simp_all add: open_vimage_Cart_nth)
  with assms have "eventually (\<lambda>x. f x \<in> (\<lambda>y. y $ i) -` S) net"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. f x $ i \<in> S) net"
    by simp
qed

subsection {* Square root of sum of squares *}

definition
  "setL2 f A = sqrt (\<Sum>i\<in>A. (f i)\<twosuperior>)"

lemma setL2_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> setL2 f A = setL2 g B"
  unfolding setL2_def by simp

lemma strong_setL2_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B =simp=> f x = g x\<rbrakk> \<Longrightarrow> setL2 f A = setL2 g B"
  unfolding setL2_def simp_implies_def by simp

lemma setL2_infinite [simp]: "\<not> finite A \<Longrightarrow> setL2 f A = 0"
  unfolding setL2_def by simp

lemma setL2_empty [simp]: "setL2 f {} = 0"
  unfolding setL2_def by simp

lemma setL2_insert [simp]:
  "\<lbrakk>finite F; a \<notin> F\<rbrakk> \<Longrightarrow>
    setL2 f (insert a F) = sqrt ((f a)\<twosuperior> + (setL2 f F)\<twosuperior>)"
  unfolding setL2_def by (simp add: setsum_nonneg)

lemma setL2_nonneg [simp]: "0 \<le> setL2 f A"
  unfolding setL2_def by (simp add: setsum_nonneg)

lemma setL2_0': "\<forall>a\<in>A. f a = 0 \<Longrightarrow> setL2 f A = 0"
  unfolding setL2_def by simp

lemma setL2_constant: "setL2 (\<lambda>x. y) A = sqrt (of_nat (card A)) * \<bar>y\<bar>"
  unfolding setL2_def by (simp add: real_sqrt_mult)

lemma setL2_mono:
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i \<le> g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "setL2 f K \<le> setL2 g K"
  unfolding setL2_def
  by (simp add: setsum_nonneg setsum_mono power_mono prems)

lemma setL2_strict_mono:
  assumes "finite K" and "K \<noteq> {}"
  assumes "\<And>i. i \<in> K \<Longrightarrow> f i < g i"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 \<le> f i"
  shows "setL2 f K < setL2 g K"
  unfolding setL2_def
  by (simp add: setsum_strict_mono power_strict_mono assms)

lemma setL2_right_distrib:
  "0 \<le> r \<Longrightarrow> r * setL2 f A = setL2 (\<lambda>x. r * f x) A"
  unfolding setL2_def
  apply (simp add: power_mult_distrib)
  apply (simp add: setsum_right_distrib [symmetric])
  apply (simp add: real_sqrt_mult setsum_nonneg)
  done

lemma setL2_left_distrib:
  "0 \<le> r \<Longrightarrow> setL2 f A * r = setL2 (\<lambda>x. f x * r) A"
  unfolding setL2_def
  apply (simp add: power_mult_distrib)
  apply (simp add: setsum_left_distrib [symmetric])
  apply (simp add: real_sqrt_mult setsum_nonneg)
  done

lemma setsum_nonneg_eq_0_iff:
  fixes f :: "'a \<Rightarrow> 'b::pordered_ab_group_add"
  shows "\<lbrakk>finite A; \<forall>x\<in>A. 0 \<le> f x\<rbrakk> \<Longrightarrow> setsum f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  apply (induct set: finite, simp)
  apply (simp add: add_nonneg_eq_0_iff setsum_nonneg)
  done

lemma setL2_eq_0_iff: "finite A \<Longrightarrow> setL2 f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  unfolding setL2_def
  by (simp add: setsum_nonneg setsum_nonneg_eq_0_iff)

lemma setL2_triangle_ineq:
  shows "setL2 (\<lambda>i. f i + g i) A \<le> setL2 f A + setL2 g A"
proof (cases "finite A")
  case False
  thus ?thesis by simp
next
  case True
  thus ?thesis
  proof (induct set: finite)
    case empty
    show ?case by simp
  next
    case (insert x F)
    hence "sqrt ((f x + g x)\<twosuperior> + (setL2 (\<lambda>i. f i + g i) F)\<twosuperior>) \<le>
           sqrt ((f x + g x)\<twosuperior> + (setL2 f F + setL2 g F)\<twosuperior>)"
      by (intro real_sqrt_le_mono add_left_mono power_mono insert
                setL2_nonneg add_increasing zero_le_power2)
    also have
      "\<dots> \<le> sqrt ((f x)\<twosuperior> + (setL2 f F)\<twosuperior>) + sqrt ((g x)\<twosuperior> + (setL2 g F)\<twosuperior>)"
      by (rule real_sqrt_sum_squares_triangle_ineq)
    finally show ?case
      using insert by simp
  qed
qed

lemma sqrt_sum_squares_le_sum:
  "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> sqrt (x\<twosuperior> + y\<twosuperior>) \<le> x + y"
  apply (rule power2_le_imp_le)
  apply (simp add: power2_sum)
  apply (simp add: mult_nonneg_nonneg)
  apply (simp add: add_nonneg_nonneg)
  done

lemma setL2_le_setsum [rule_format]:
  "(\<forall>i\<in>A. 0 \<le> f i) \<longrightarrow> setL2 f A \<le> setsum f A"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply clarsimp
  apply (erule order_trans [OF sqrt_sum_squares_le_sum])
  apply simp
  apply simp
  apply simp
  done

lemma sqrt_sum_squares_le_sum_abs: "sqrt (x\<twosuperior> + y\<twosuperior>) \<le> \<bar>x\<bar> + \<bar>y\<bar>"
  apply (rule power2_le_imp_le)
  apply (simp add: power2_sum)
  apply (simp add: mult_nonneg_nonneg)
  apply (simp add: add_nonneg_nonneg)
  done

lemma setL2_le_setsum_abs: "setL2 f A \<le> (\<Sum>i\<in>A. \<bar>f i\<bar>)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply simp
  apply (rule order_trans [OF sqrt_sum_squares_le_sum_abs])
  apply simp
  apply simp
  done

lemma setL2_mult_ineq_lemma:
  fixes a b c d :: real
  shows "2 * (a * c) * (b * d) \<le> a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior>"
proof -
  have "0 \<le> (a * d - b * c)\<twosuperior>" by simp
  also have "\<dots> = a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior> - 2 * (a * d) * (b * c)"
    by (simp only: power2_diff power_mult_distrib)
  also have "\<dots> = a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior> - 2 * (a * c) * (b * d)"
    by simp
  finally show "2 * (a * c) * (b * d) \<le> a\<twosuperior> * d\<twosuperior> + b\<twosuperior> * c\<twosuperior>"
    by simp
qed

lemma setL2_mult_ineq: "(\<Sum>i\<in>A. \<bar>f i\<bar> * \<bar>g i\<bar>) \<le> setL2 f A * setL2 g A"
  apply (cases "finite A")
  apply (induct set: finite)
  apply simp
  apply (rule power2_le_imp_le, simp)
  apply (rule order_trans)
  apply (rule power_mono)
  apply (erule add_left_mono)
  apply (simp add: add_nonneg_nonneg mult_nonneg_nonneg setsum_nonneg)
  apply (simp add: power2_sum)
  apply (simp add: power_mult_distrib)
  apply (simp add: right_distrib left_distrib)
  apply (rule ord_le_eq_trans)
  apply (rule setL2_mult_ineq_lemma)
  apply simp
  apply (intro mult_nonneg_nonneg setL2_nonneg)
  apply simp
  done

lemma member_le_setL2: "\<lbrakk>finite A; i \<in> A\<rbrakk> \<Longrightarrow> f i \<le> setL2 f A"
  apply (rule_tac s="insert i (A - {i})" and t="A" in subst)
  apply fast
  apply (subst setL2_insert)
  apply simp
  apply simp
  apply simp
  done

subsection {* Metric *}

(* TODO: move somewhere else *)
lemma finite_choice: "finite A \<Longrightarrow> \<forall>x\<in>A. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x\<in>A. P x (f x)"
apply (induct set: finite, simp_all)
apply (clarify, rename_tac y)
apply (rule_tac x="f(x:=y)" in exI, simp)
done

instantiation "^" :: (metric_space, finite) metric_space
begin

definition dist_vector_def:
  "dist (x::'a^'b) (y::'a^'b) = setL2 (\<lambda>i. dist (x$i) (y$i)) UNIV"

lemma dist_nth_le: "dist (x $ i) (y $ i) \<le> dist x y"
unfolding dist_vector_def
by (rule member_le_setL2) simp_all

instance proof
  fix x y :: "'a ^ 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_vector_def
    by (simp add: setL2_eq_0_iff Cart_eq)
next
  fix x y z :: "'a ^ 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_vector_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono dist_triangle2)
    done
next
  (* FIXME: long proof! *)
  fix S :: "('a ^ 'b) set"
  show "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
    unfolding open_vector_def open_dist
    apply safe
     apply (drule (1) bspec)
     apply clarify
     apply (subgoal_tac "\<exists>e>0. \<forall>i y. dist y (x$i) < e \<longrightarrow> y \<in> A i")
      apply clarify
      apply (rule_tac x=e in exI, clarify)
      apply (drule spec, erule mp, clarify)
      apply (drule spec, drule spec, erule mp)
      apply (erule le_less_trans [OF dist_nth_le])
     apply (subgoal_tac "\<forall>i\<in>UNIV. \<exists>e>0. \<forall>y. dist y (x$i) < e \<longrightarrow> y \<in> A i")
      apply (drule finite_choice [OF finite], clarify)
      apply (rule_tac x="Min (range f)" in exI, simp)
     apply clarify
     apply (drule_tac x=i in spec, clarify)
     apply (erule (1) bspec)
    apply (drule (1) bspec, clarify)
    apply (subgoal_tac "\<exists>r. (\<forall>i::'b. 0 < r i) \<and> e = setL2 r UNIV")
     apply clarify
     apply (rule_tac x="\<lambda>i. {y. dist y (x$i) < r i}" in exI)
     apply (rule conjI)
      apply clarify
      apply (rule conjI)
       apply (clarify, rename_tac y)
       apply (rule_tac x="r i - dist y (x$i)" in exI, rule conjI, simp)
       apply clarify
       apply (simp only: less_diff_eq)
       apply (erule le_less_trans [OF dist_triangle])
      apply simp
     apply clarify
     apply (drule spec, erule mp)
     apply (simp add: dist_vector_def setL2_strict_mono)
    apply (rule_tac x="\<lambda>i. e / sqrt (of_nat CARD('b))" in exI)
    apply (simp add: divide_pos_pos setL2_constant)
    done
qed

end

lemma LIMSEQ_Cart_nth:
  "(X ----> a) \<Longrightarrow> (\<lambda>n. X n $ i) ----> a $ i"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_Cart_nth)

lemma LIM_Cart_nth:
  "(f -- x --> y) \<Longrightarrow> (\<lambda>x. f x $ i) -- x --> y $ i"
unfolding LIM_conv_tendsto by (rule tendsto_Cart_nth)

lemma Cauchy_Cart_nth:
  "Cauchy (\<lambda>n. X n) \<Longrightarrow> Cauchy (\<lambda>n. X n $ i)"
unfolding Cauchy_def by (fast intro: le_less_trans [OF dist_nth_le])

lemma LIMSEQ_vector:
  fixes X :: "nat \<Rightarrow> 'a::metric_space ^ 'n::finite"
  assumes X: "\<And>i. (\<lambda>n. X n $ i) ----> (a $ i)"
  shows "X ----> a"
proof (rule metric_LIMSEQ_I)
  fix r :: real assume "0 < r"
  then have "0 < r / of_nat CARD('n)" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  def N \<equiv> "\<lambda>i. LEAST N. \<forall>n\<ge>N. dist (X n $ i) (a $ i) < ?s"
  def M \<equiv> "Max (range N)"
  have "\<And>i. \<exists>N. \<forall>n\<ge>N. dist (X n $ i) (a $ i) < ?s"
    using X `0 < ?s` by (rule metric_LIMSEQ_D)
  hence "\<And>i. \<forall>n\<ge>N i. dist (X n $ i) (a $ i) < ?s"
    unfolding N_def by (rule LeastI_ex)
  hence M: "\<And>i. \<forall>n\<ge>M. dist (X n $ i) (a $ i) < ?s"
    unfolding M_def by simp
  {
    fix n :: nat assume "M \<le> n"
    have "dist (X n) a = setL2 (\<lambda>i. dist (X n $ i) (a $ i)) UNIV"
      unfolding dist_vector_def ..
    also have "\<dots> \<le> setsum (\<lambda>i. dist (X n $ i) (a $ i)) UNIV"
      by (rule setL2_le_setsum [OF zero_le_dist])
    also have "\<dots> < setsum (\<lambda>i::'n. ?s) UNIV"
      by (rule setsum_strict_mono, simp_all add: M `M \<le> n`)
    also have "\<dots> = r"
      by simp
    finally have "dist (X n) a < r" .
  }
  hence "\<forall>n\<ge>M. dist (X n) a < r"
    by simp
  then show "\<exists>M. \<forall>n\<ge>M. dist (X n) a < r" ..
qed

lemma Cauchy_vector:
  fixes X :: "nat \<Rightarrow> 'a::metric_space ^ 'n::finite"
  assumes X: "\<And>i. Cauchy (\<lambda>n. X n $ i)"
  shows "Cauchy (\<lambda>n. X n)"
proof (rule metric_CauchyI)
  fix r :: real assume "0 < r"
  then have "0 < r / of_nat CARD('n)" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  def N \<equiv> "\<lambda>i. LEAST N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s"
  def M \<equiv> "Max (range N)"
  have "\<And>i. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s"
    using X `0 < ?s` by (rule metric_CauchyD)
  hence "\<And>i. \<forall>m\<ge>N i. \<forall>n\<ge>N i. dist (X m $ i) (X n $ i) < ?s"
    unfolding N_def by (rule LeastI_ex)
  hence M: "\<And>i. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m $ i) (X n $ i) < ?s"
    unfolding M_def by simp
  {
    fix m n :: nat
    assume "M \<le> m" "M \<le> n"
    have "dist (X m) (X n) = setL2 (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      unfolding dist_vector_def ..
    also have "\<dots> \<le> setsum (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      by (rule setL2_le_setsum [OF zero_le_dist])
    also have "\<dots> < setsum (\<lambda>i::'n. ?s) UNIV"
      by (rule setsum_strict_mono, simp_all add: M `M \<le> m` `M \<le> n`)
    also have "\<dots> = r"
      by simp
    finally have "dist (X m) (X n) < r" .
  }
  hence "\<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < r"
    by simp
  then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < r" ..
qed

instance "^" :: (complete_space, finite) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a ^ 'b" assume "Cauchy X"
  have "\<And>i. (\<lambda>n. X n $ i) ----> lim (\<lambda>n. X n $ i)"
    using Cauchy_Cart_nth [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  hence "X ----> Cart_lambda (\<lambda>i. lim (\<lambda>n. X n $ i))"
    by (simp add: LIMSEQ_vector)
  then show "convergent X"
    by (rule convergentI)
qed

subsection {* Norms *}

instantiation "^" :: (real_normed_vector, finite) real_normed_vector
begin

definition norm_vector_def:
  "norm (x::'a^'b) = setL2 (\<lambda>i. norm (x$i)) UNIV"

definition vector_sgn_def:
  "sgn (x::'a^'b) = scaleR (inverse (norm x)) x"

instance proof
  fix a :: real and x y :: "'a ^ 'b"
  show "0 \<le> norm x"
    unfolding norm_vector_def
    by (rule setL2_nonneg)
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_vector_def
    by (simp add: setL2_eq_0_iff Cart_eq)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_vector_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono norm_triangle_ineq)
    done
  show "norm (scaleR a x) = \<bar>a\<bar> * norm x"
    unfolding norm_vector_def
    by (simp add: setL2_right_distrib)
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule vector_sgn_def)
  show "dist x y = norm (x - y)"
    unfolding dist_vector_def norm_vector_def
    by (simp add: dist_norm)
qed

end

lemma norm_nth_le: "norm (x $ i) \<le> norm x"
unfolding norm_vector_def
by (rule member_le_setL2) simp_all

interpretation Cart_nth: bounded_linear "\<lambda>x. x $ i"
apply default
apply (rule vector_add_component)
apply (rule vector_scaleR_component)
apply (rule_tac x="1" in exI, simp add: norm_nth_le)
done

instance "^" :: (banach, finite) banach ..

subsection {* Inner products *}

instantiation "^" :: (real_inner, finite) real_inner
begin

definition inner_vector_def:
  "inner x y = setsum (\<lambda>i. inner (x$i) (y$i)) UNIV"

instance proof
  fix r :: real and x y z :: "'a ^ 'b"
  show "inner x y = inner y x"
    unfolding inner_vector_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_vector_def
    by (simp add: inner_add_left setsum_addf)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_vector_def
    by (simp add: setsum_right_distrib)
  show "0 \<le> inner x x"
    unfolding inner_vector_def
    by (simp add: setsum_nonneg)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_vector_def
    by (simp add: Cart_eq setsum_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_vector_def norm_vector_def setL2_def
    by (simp add: power2_norm_eq_inner)
qed

end

subsection{* Properties of the dot product.  *}

lemma dot_sym: "(x::'a:: {comm_monoid_add, ab_semigroup_mult} ^ 'n) \<bullet> y = y \<bullet> x"
  by (vector mult_commute)
lemma dot_ladd: "((x::'a::ring ^ 'n) + y) \<bullet> z = (x \<bullet> z) + (y \<bullet> z)"
  by (vector ring_simps)
lemma dot_radd: "x \<bullet> (y + (z::'a::ring ^ 'n)) = (x \<bullet> y) + (x \<bullet> z)"
  by (vector ring_simps)
lemma dot_lsub: "((x::'a::ring ^ 'n) - y) \<bullet> z = (x \<bullet> z) - (y \<bullet> z)"
  by (vector ring_simps)
lemma dot_rsub: "(x::'a::ring ^ 'n) \<bullet> (y - z) = (x \<bullet> y) - (x \<bullet> z)"
  by (vector ring_simps)
lemma dot_lmult: "(c *s x) \<bullet> y = (c::'a::ring) * (x \<bullet> y)" by (vector ring_simps)
lemma dot_rmult: "x \<bullet> (c *s y) = (c::'a::comm_ring) * (x \<bullet> y)" by (vector ring_simps)
lemma dot_lneg: "(-x) \<bullet> (y::'a::ring ^ 'n) = -(x \<bullet> y)" by vector
lemma dot_rneg: "(x::'a::ring ^ 'n) \<bullet> (-y) = -(x \<bullet> y)" by vector
lemma dot_lzero[simp]: "0 \<bullet> x = (0::'a::{comm_monoid_add, mult_zero})" by vector
lemma dot_rzero[simp]: "x \<bullet> 0 = (0::'a::{comm_monoid_add, mult_zero})" by vector
lemma dot_pos_le[simp]: "(0::'a\<Colon>ordered_ring_strict) <= x \<bullet> x"
  by (simp add: dot_def setsum_nonneg)

lemma setsum_squares_eq_0_iff: assumes fS: "finite F" and fp: "\<forall>x \<in> F. f x \<ge> (0 ::'a::pordered_ab_group_add)" shows "setsum f F = 0 \<longleftrightarrow> (ALL x:F. f x = 0)"
using fS fp setsum_nonneg[OF fp]
proof (induct set: finite)
  case empty thus ?case by simp
next
  case (insert x F)
  from insert.prems have Fx: "f x \<ge> 0" and Fp: "\<forall> a \<in> F. f a \<ge> 0" by simp_all
  from insert.hyps Fp setsum_nonneg[OF Fp]
  have h: "setsum f F = 0 \<longleftrightarrow> (\<forall>a \<in>F. f a = 0)" by metis
  from add_nonneg_eq_0_iff[OF Fx  setsum_nonneg[OF Fp]] insert.hyps(1,2)
  show ?case by (simp add: h)
qed

lemma dot_eq_0: "x \<bullet> x = 0 \<longleftrightarrow> (x::'a::{ordered_ring_strict,ring_no_zero_divisors} ^ 'n::finite) = 0"
  by (simp add: dot_def setsum_squares_eq_0_iff Cart_eq)

lemma dot_pos_lt[simp]: "(0 < x \<bullet> x) \<longleftrightarrow> (x::'a::{ordered_ring_strict,ring_no_zero_divisors} ^ 'n::finite) \<noteq> 0" using dot_eq_0[of x] dot_pos_le[of x]
  by (auto simp add: le_less)

subsection{* The collapse of the general concepts to dimension one. *}

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: Cart_eq forall_1)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vector_def UNIV_1)

lemma norm_real: "norm(x::real ^ 1) = abs(x$1)"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = abs((x$1) - (y$1))"
  by (auto simp add: norm_real dist_norm)

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

text{* One immediately useful corollary is the existence of square roots! --- Should help to get rid of all the development of square-root for reals as a special case @{typ "real^1"} *}

lemma square_bound_lemma: "(x::real) < (1 + x) * (1 + x)"
proof-
  have "(x + 1/2)^2 + 3/4 > 0" using zero_le_power2[of "x+1/2"] by arith
  thus ?thesis by (simp add: ring_simps power2_eq_square)
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
  from n obtain m where m: "n = 2*m" unfolding even_nat_equiv_def2
    by (auto simp add: nat_number)
  from m  have "sqrt(2 ^ n) = sqrt ((2 ^ m) ^ 2)"
    by (simp only: power_mult[symmetric] mult_commute)
  then show ?thesis  using m by simp
qed

lemma real_div_sqrt: "0 <= x ==> x / sqrt(x) = sqrt(x)"
  apply (cases "x = 0", simp_all)
  using sqrt_divide_self_eq[of x]
  apply (simp add: inverse_eq_divide real_sqrt_ge_0_iff field_simps)
  done

text{* Hence derive more interesting properties of the norm. *}

text {*
  This type-specific version is only here
  to make @{text normarith.ML} happy.
*}
lemma norm_0: "norm (0::real ^ _) = 0"
  by (rule norm_zero)

lemma norm_mul[simp]: "norm(a *s x) = abs(a) * norm x"
  by (simp add: norm_vector_def vector_component setL2_right_distrib
           abs_mult cong: strong_setL2_cong)
lemma norm_eq_0_dot: "(norm x = 0) \<longleftrightarrow> (x \<bullet> x = (0::real))"
  by (simp add: norm_vector_def dot_def setL2_def power2_eq_square)
lemma real_vector_norm_def: "norm x = sqrt (x \<bullet> x)"
  by (simp add: norm_vector_def setL2_def dot_def power2_eq_square)
lemma norm_pow_2: "norm x ^ 2 = x \<bullet> x"
  by (simp add: real_vector_norm_def)
lemma norm_eq_0_imp: "norm x = 0 ==> x = (0::real ^'n::finite)" by (metis norm_eq_zero)
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
  fixes x y :: "real ^ 'n::finite"
  shows "x \<bullet> y <= norm x * norm y"
proof-
  {assume "norm x = 0"
    hence ?thesis by (simp add: dot_lzero dot_rzero)}
  moreover
  {assume "norm y = 0"
    hence ?thesis by (simp add: dot_lzero dot_rzero)}
  moreover
  {assume h: "norm x \<noteq> 0" "norm y \<noteq> 0"
    let ?z = "norm y *s x - norm x *s y"
    from h have p: "norm x * norm y > 0" by (metis norm_ge_zero le_less zero_compare_simps)
    from dot_pos_le[of ?z]
    have "(norm x * norm y) * (x \<bullet> y) \<le> norm x ^2 * norm y ^2"
      apply (simp add: dot_rsub dot_lsub dot_lmult dot_rmult ring_simps)
      by (simp add: norm_pow_2[symmetric] power2_eq_square dot_sym)
    hence "x\<bullet>y \<le> (norm x ^2 * norm y ^2) / (norm x * norm y)" using p
      by (simp add: field_simps)
    hence ?thesis using h by (simp add: power2_eq_square)}
  ultimately show ?thesis by metis
qed

lemma norm_cauchy_schwarz_abs:
  fixes x y :: "real ^ 'n::finite"
  shows "\<bar>x \<bullet> y\<bar> \<le> norm x * norm y"
  using norm_cauchy_schwarz[of x y] norm_cauchy_schwarz[of x "-y"]
  by (simp add: real_abs_def dot_rneg)

lemma norm_triangle_sub:
  fixes x y :: "'a::real_normed_vector"
  shows "norm x \<le> norm y  + norm (x - y)"
  using norm_triangle_ineq[of "y" "x - y"] by (simp add: ring_simps)

lemma norm_triangle_le: "norm(x::real ^'n::finite) + norm y <= e ==> norm(x + y) <= e"
  by (metis order_trans norm_triangle_ineq)
lemma norm_triangle_lt: "norm(x::real ^'n::finite) + norm(y) < e ==> norm(x + y) < e"
  by (metis basic_trans_rules(21) norm_triangle_ineq)

lemma component_le_norm: "\<bar>x$i\<bar> <= norm (x::real ^ 'n::finite)"
  apply (simp add: norm_vector_def)
  apply (rule member_le_setL2, simp_all)
  done

lemma norm_bound_component_le: "norm(x::real ^ 'n::finite) <= e
                ==> \<bar>x$i\<bar> <= e"
  by (metis component_le_norm order_trans)

lemma norm_bound_component_lt: "norm(x::real ^ 'n::finite) < e
                ==> \<bar>x$i\<bar> < e"
  by (metis component_le_norm basic_trans_rules(21))

lemma norm_le_l1: "norm (x:: real ^'n::finite) <= setsum(\<lambda>i. \<bar>x$i\<bar>) UNIV"
  by (simp add: norm_vector_def setL2_le_setsum)

lemma real_abs_norm: "\<bar>norm x\<bar> = norm (x :: real ^ _)"
  by (rule abs_norm_cancel)
lemma real_abs_sub_norm: "\<bar>norm(x::real ^'n::finite) - norm y\<bar> <= norm(x - y)"
  by (rule norm_triangle_ineq3)
lemma norm_le: "norm(x::real ^ _) <= norm(y) \<longleftrightarrow> x \<bullet> x <= y \<bullet> y"
  by (simp add: real_vector_norm_def)
lemma norm_lt: "norm(x::real ^ _) < norm(y) \<longleftrightarrow> x \<bullet> x < y \<bullet> y"
  by (simp add: real_vector_norm_def)
lemma norm_eq: "norm (x::real ^ _) = norm y \<longleftrightarrow> x \<bullet> x = y \<bullet> y"
  by (simp add: order_eq_iff norm_le)
lemma norm_eq_1: "norm(x::real ^ _) = 1 \<longleftrightarrow> x \<bullet> x = 1"
  by (simp add: real_vector_norm_def)

text{* Squaring equations and inequalities involving norms.  *}

lemma dot_square_norm: "x \<bullet> x = norm(x)^2"
  by (simp add: real_vector_norm_def)

lemma norm_eq_square: "norm(x) = a \<longleftrightarrow> 0 <= a \<and> x \<bullet> x = a^2"
  by (auto simp add: real_vector_norm_def)

lemma real_abs_le_square_iff: "\<bar>x\<bar> \<le> \<bar>y\<bar> \<longleftrightarrow> (x::real)^2 \<le> y^2"
proof-
  have "x^2 \<le> y^2 \<longleftrightarrow> (x -y) * (y + x) \<le> 0" by (simp add: ring_simps power2_eq_square)
  also have "\<dots> \<longleftrightarrow> \<bar>x\<bar> \<le> \<bar>y\<bar>" apply (simp add: zero_compare_simps real_abs_def not_less) by arith
finally show ?thesis ..
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

lemma dot_norm: "x \<bullet> y = (norm(x + y) ^2 - norm x ^ 2 - norm y ^ 2) / 2"
  by (simp add: norm_pow_2 dot_ladd dot_radd dot_sym)

lemma dot_norm_neg: "x \<bullet> y = ((norm x ^ 2 + norm y ^ 2) - norm(x - y) ^ 2) / 2"
  by (simp add: norm_pow_2 dot_ladd dot_radd dot_lsub dot_rsub dot_sym)


text{* Equality of vectors in terms of @{term "op \<bullet>"} products.    *}

lemma vector_eq: "(x:: real ^ 'n::finite) = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y\<and> y \<bullet> y = x \<bullet> x" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs" then show ?rhs by simp
next
  assume ?rhs
  then have "x \<bullet> x - x \<bullet> y = 0 \<and> x \<bullet> y - y\<bullet> y = 0" by simp
  hence "x \<bullet> (x - y) = 0 \<and> y \<bullet> (x - y) = 0"
    by (simp add: dot_rsub dot_lsub dot_sym)
  then have "(x - y) \<bullet> (x - y) = 0" by (simp add: ring_simps dot_lsub dot_rsub)
  then show "x = y" by (simp add: dot_eq_0)
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

lemma ge_iff_diff_ge_0: "(a::'a::ordered_ring) \<ge> b == a - b \<ge> 0"
  by (simp add: ring_simps)

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

lemma vector_dist_norm:
  fixes x :: "'a::real_normed_vector"
  shows "dist x y = norm (x - y)"
  by (rule dist_norm)

use "normarith.ML"

method_setup norm = {* Scan.succeed (SIMPLE_METHOD' o NormArith.norm_arith_tac)
*} "Proves simple linear statements about vector norms"


text{* Hence more metric properties. *}

lemma dist_triangle_alt:
  fixes x y z :: "'a::metric_space"
  shows "dist y z <= dist x y + dist x z"
using dist_triangle [of y z x] by (simp add: dist_commute)

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

lemma real_setsum_norm:
  fixes f :: "'a \<Rightarrow> real ^'n::finite"
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

lemma real_setsum_norm_le:
  fixes f :: "'a \<Rightarrow> real ^ 'n::finite"
  assumes fS: "finite S"
  and fg: "\<forall>x \<in> S. norm (f x) \<le> g x"
  shows "norm (setsum f S) \<le> setsum g S"
proof-
  from fg have "setsum (\<lambda>x. norm(f x)) S <= setsum g S"
    by - (rule setsum_mono, simp)
  then show ?thesis using real_setsum_norm[OF fS, of f] fg
    by arith
qed

lemma setsum_norm_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fS: "finite S"
  and K: "\<forall>x \<in> S. norm (f x) \<le> K"
  shows "norm (setsum f S) \<le> of_nat (card S) * K"
  using setsum_norm_le[OF fS K] setsum_constant[symmetric]
  by simp

lemma real_setsum_norm_bound:
  fixes f :: "'a \<Rightarrow> real ^ 'n::finite"
  assumes fS: "finite S"
  and K: "\<forall>x \<in> S. norm (f x) \<le> K"
  shows "norm (setsum f S) \<le> of_nat (card S) * K"
  using real_setsum_norm_le[OF fS K] setsum_constant[symmetric]
  by simp

lemma setsum_vmul:
  fixes f :: "'a \<Rightarrow> 'b::{real_normed_vector,semiring, mult_zero}"
  assumes fS: "finite S"
  shows "setsum f S *s v = setsum (\<lambda>x. f x *s v) S"
proof(induct rule: finite_induct[OF fS])
  case 1 then show ?case by (simp add: vector_smult_lzero)
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
  fixes f:: "'a \<Rightarrow> real ^'n::finite"
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

lemma dot_lsum: "finite S \<Longrightarrow> setsum f S \<bullet> (y::'a::{comm_ring}^'n) = setsum (\<lambda>x. f x \<bullet> y) S "
  by (induct rule: finite_induct, auto simp add: dot_lzero dot_ladd dot_radd)

lemma dot_rsum: "finite S \<Longrightarrow> (y::'a::{comm_ring}^'n) \<bullet> setsum f S = setsum (\<lambda>x. y \<bullet> f x) S "
  by (induct rule: finite_induct, auto simp add: dot_rzero dot_radd)

subsection{* Basis vectors in coordinate directions. *}


definition "basis k = (\<chi> i. if i = k then 1 else 0)"

lemma basis_component [simp]: "basis k $ i = (if k=i then 1 else 0)"
  unfolding basis_def by simp

lemma delta_mult_idempotent:
  "(if k=a then 1 else (0::'a::semiring_1)) * (if k=a then 1 else 0) = (if k=a then 1 else 0)" by (cases "k=a", auto)

lemma norm_basis:
  shows "norm (basis k :: real ^'n::finite) = 1"
  apply (simp add: basis_def real_vector_norm_def dot_def)
  apply (vector delta_mult_idempotent)
  using setsum_delta[of "UNIV :: 'n set" "k" "\<lambda>k. 1::real"]
  apply auto
  done

lemma norm_basis_1: "norm(basis 1 :: real ^'n::{finite,one}) = 1"
  by (rule norm_basis)

lemma vector_choose_size: "0 <= c ==> \<exists>(x::real^'n::finite). norm x = c"
  apply (rule exI[where x="c *s basis arbitrary"])
  by (simp only: norm_mul norm_basis)

lemma vector_choose_dist: assumes e: "0 <= e"
  shows "\<exists>(y::real^'n::finite). dist x y = e"
proof-
  from vector_choose_size[OF e] obtain c:: "real ^'n"  where "norm c = e"
    by blast
  then have "dist x (x - c) = e" by (simp add: dist_norm)
  then show ?thesis by blast
qed

lemma basis_inj: "inj (basis :: 'n \<Rightarrow> real ^'n::finite)"
  by (simp add: inj_on_def Cart_eq)

lemma cond_value_iff: "f (if b then x else y) = (if b then f x else f y)"
  by auto

lemma basis_expansion:
  "setsum (\<lambda>i. (x$i) *s basis i) UNIV = (x::('a::ring_1) ^'n::finite)" (is "?lhs = ?rhs" is "setsum ?f ?S = _")
  by (auto simp add: Cart_eq cond_value_iff setsum_delta[of "?S", where ?'b = "'a", simplified] cong del: if_weak_cong)

lemma basis_expansion_unique:
  "setsum (\<lambda>i. f i *s basis i) UNIV = (x::('a::comm_ring_1) ^'n::finite) \<longleftrightarrow> (\<forall>i. f i = x$i)"
  by (simp add: Cart_eq setsum_delta cond_value_iff cong del: if_weak_cong)

lemma cond_application_beta: "(if b then f else g) x = (if b then f x else g x)"
  by auto

lemma dot_basis:
  shows "basis i \<bullet> x = x$i" "x \<bullet> (basis i :: 'a^'n::finite) = (x$i :: 'a::semiring_1)"
  by (auto simp add: dot_def basis_def cond_application_beta  cond_value_iff setsum_delta cong del: if_weak_cong)

lemma inner_basis:
  fixes x :: "'a::{real_inner, real_algebra_1} ^ 'n::finite"
  shows "inner (basis i) x = inner 1 (x $ i)"
    and "inner x (basis i) = inner (x $ i) 1"
  unfolding inner_vector_def basis_def
  by (auto simp add: cond_application_beta  cond_value_iff setsum_delta cong del: if_weak_cong)

lemma basis_eq_0: "basis i = (0::'a::semiring_1^'n) \<longleftrightarrow> False"
  by (auto simp add: Cart_eq)

lemma basis_nonzero:
  shows "basis k \<noteq> (0:: 'a::semiring_1 ^'n)"
  by (simp add: basis_eq_0)

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = (z::'a::semiring_1^'n::finite)"
  apply (auto simp add: Cart_eq dot_basis)
  apply (erule_tac x="basis i" in allE)
  apply (simp add: dot_basis)
  apply (subgoal_tac "y = z")
  apply simp
  apply (simp add: Cart_eq)
  done

lemma vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = (y::'a::semiring_1^'n::finite)"
  apply (auto simp add: Cart_eq dot_basis)
  apply (erule_tac x="basis i" in allE)
  apply (simp add: dot_basis)
  apply (subgoal_tac "x = y")
  apply simp
  apply (simp add: Cart_eq)
  done

subsection{* Orthogonality. *}

definition "orthogonal x y \<longleftrightarrow> (x \<bullet> y = 0)"

lemma orthogonal_basis:
  shows "orthogonal (basis i :: 'a^'n::finite) x \<longleftrightarrow> x$i = (0::'a::ring_1)"
  by (auto simp add: orthogonal_def dot_def basis_def cond_value_iff cond_application_beta setsum_delta cong del: if_weak_cong)

lemma orthogonal_basis_basis:
  shows "orthogonal (basis i :: 'a::ring_1^'n::finite) (basis j) \<longleftrightarrow> i \<noteq> j"
  unfolding orthogonal_basis[of i] basis_component[of j] by simp

  (* FIXME : Maybe some of these require less than comm_ring, but not all*)
lemma orthogonal_clauses:
  "orthogonal a (0::'a::comm_ring ^'n)"
  "orthogonal a x ==> orthogonal a (c *s x)"
  "orthogonal a x ==> orthogonal a (-x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y ==> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y ==> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a ==> orthogonal (c *s x) a"
  "orthogonal x a ==> orthogonal (-x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a ==> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a ==> orthogonal (x - y) a"
  unfolding orthogonal_def dot_rneg dot_rmult dot_radd dot_rsub
  dot_lzero dot_rzero dot_lneg dot_lmult dot_ladd dot_lsub
  by simp_all

lemma orthogonal_commute: "orthogonal (x::'a::{ab_semigroup_mult,comm_monoid_add} ^'n)y \<longleftrightarrow> orthogonal y x"
  by (simp add: orthogonal_def dot_sym)

subsection{* Explicit vector construction from lists. *}

primrec from_nat :: "nat \<Rightarrow> 'a::{monoid_add,one}"
where "from_nat 0 = 0" | "from_nat (Suc n) = 1 + from_nat n"

lemma from_nat [simp]: "from_nat = of_nat"
by (rule ext, induct_tac x, simp_all)

primrec
  list_fun :: "nat \<Rightarrow> _ list \<Rightarrow> _ \<Rightarrow> _"
where
  "list_fun n [] = (\<lambda>x. 0)"
| "list_fun n (x # xs) = fun_upd (list_fun (Suc n) xs) (from_nat n) x"

definition "vector l = (\<chi> i. list_fun 1 l i)"
(*definition "vector l = (\<chi> i. if i <= length l then l ! (i - 1) else 0)"*)

lemma vector_1: "(vector[x]) $1 = x"
  unfolding vector_def by simp

lemma vector_2:
 "(vector[x,y]) $1 = x"
 "(vector[x,y] :: 'a^2)$2 = (y::'a::zero)"
  unfolding vector_def by simp_all

lemma vector_3:
 "(vector [x,y,z] ::('a::zero)^3)$1 = x"
 "(vector [x,y,z] ::('a::zero)^3)$2 = y"
 "(vector [x,y,z] ::('a::zero)^3)$3 = z"
  unfolding vector_def by simp_all

lemma forall_vector_1: "(\<forall>v::'a::zero^1. P v) \<longleftrightarrow> (\<forall>x. P(vector[x]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (subgoal_tac "vector [v$1] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_1)
  done

lemma forall_vector_2: "(\<forall>v::'a::zero^2. P v) \<longleftrightarrow> (\<forall>x y. P(vector[x, y]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (subgoal_tac "vector [v$1, v$2] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_2)
  done

lemma forall_vector_3: "(\<forall>v::'a::zero^3. P v) \<longleftrightarrow> (\<forall>x y z. P(vector[x, y, z]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_3)
  done

subsection{* Linear functions. *}

definition "linear f \<longleftrightarrow> (\<forall>x y. f(x + y) = f x + f y) \<and> (\<forall>c x. f(c *s x) = c *s f x)"

lemma linear_compose_cmul: "linear f ==> linear (\<lambda>x. (c::'a::comm_semiring) *s f x)"
  by (vector linear_def Cart_eq ring_simps)

lemma linear_compose_neg: "linear (f :: 'a ^'n \<Rightarrow> 'a::comm_ring ^'m) ==> linear (\<lambda>x. -(f(x)))" by (vector linear_def Cart_eq)

lemma linear_compose_add: "linear (f :: 'a ^'n \<Rightarrow> 'a::semiring_1 ^'m) \<Longrightarrow> linear g ==> linear (\<lambda>x. f(x) + g(x))"
  by (vector linear_def Cart_eq ring_simps)

lemma linear_compose_sub: "linear (f :: 'a ^'n \<Rightarrow> 'a::ring_1 ^'m) \<Longrightarrow> linear g ==> linear (\<lambda>x. f x - g x)"
  by (vector linear_def Cart_eq ring_simps)

lemma linear_compose: "linear f \<Longrightarrow> linear g ==> linear (g o f)"
  by (simp add: linear_def)

lemma linear_id: "linear id" by (simp add: linear_def id_def)

lemma linear_zero: "linear (\<lambda>x. 0::'a::semiring_1 ^ 'n)" by (simp add: linear_def)

lemma linear_compose_setsum:
  assumes fS: "finite S" and lS: "\<forall>a \<in> S. linear (f a :: 'a::semiring_1 ^ 'n \<Rightarrow> 'a ^ 'm)"
  shows "linear(\<lambda>x. setsum (\<lambda>a. f a x :: 'a::semiring_1 ^'m) S)"
  using lS
  apply (induct rule: finite_induct[OF fS])
  by (auto simp add: linear_zero intro: linear_compose_add)

lemma linear_vmul_component:
  fixes f:: "'a::semiring_1^'m \<Rightarrow> 'a^'n"
  assumes lf: "linear f"
  shows "linear (\<lambda>x. f x $ k *s v)"
  using lf
  apply (auto simp add: linear_def )
  by (vector ring_simps)+

lemma linear_0: "linear f ==> f 0 = (0::'a::semiring_1 ^'n)"
  unfolding linear_def
  apply clarsimp
  apply (erule allE[where x="0::'a"])
  apply simp
  done

lemma linear_cmul: "linear f ==> f(c*s x) = c *s f x" by (simp add: linear_def)

lemma linear_neg: "linear (f :: 'a::ring_1 ^'n \<Rightarrow> _) ==> f (-x) = - f x"
  unfolding vector_sneg_minus1
  using linear_cmul[of f] by auto

lemma linear_add: "linear f ==> f(x + y) = f x + f y" by (metis linear_def)

lemma linear_sub: "linear (f::'a::ring_1 ^'n \<Rightarrow> _) ==> f(x - y) = f x - f y"
  by (simp add: diff_def linear_add linear_neg)

lemma linear_setsum:
  fixes f:: "'a::semiring_1^'n \<Rightarrow> _"
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
  fixes f:: "'a ^'n \<Rightarrow> 'a::semiring_1^'m"
  assumes lf: "linear f" and fS: "finite S"
  shows "f (setsum (\<lambda>i. c i *s v i) S) = setsum (\<lambda>i. c i *s f (v i)) S"
  using linear_setsum[OF lf fS, of "\<lambda>i. c i *s v i" , unfolded o_def]
  linear_cmul[OF lf] by simp

lemma linear_injective_0:
  assumes lf: "linear (f:: 'a::ring_1 ^ 'n \<Rightarrow> _)"
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
  fixes f:: "real ^'m::finite \<Rightarrow> real ^'n::finite"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
proof-
  let ?S = "UNIV:: 'm set"
  let ?B = "setsum (\<lambda>i. norm(f(basis i))) ?S"
  have fS: "finite ?S" by simp
  {fix x:: "real ^ 'm"
    let ?g = "(\<lambda>i. (x$i) *s (basis i) :: real ^ 'm)"
    have "norm (f x) = norm (f (setsum (\<lambda>i. (x$i) *s (basis i)) ?S))"
      by (simp only:  basis_expansion)
    also have "\<dots> = norm (setsum (\<lambda>i. (x$i) *s f (basis i))?S)"
      using linear_setsum[OF lf fS, of ?g, unfolded o_def] linear_cmul[OF lf]
      by auto
    finally have th0: "norm (f x) = norm (setsum (\<lambda>i. (x$i) *s f (basis i))?S)" .
    {fix i assume i: "i \<in> ?S"
      from component_le_norm[of x i]
      have "norm ((x$i) *s f (basis i :: real ^'m)) \<le> norm (f (basis i)) * norm x"
      unfolding norm_mul
      apply (simp only: mult_commute)
      apply (rule mult_mono)
      by (auto simp add: ring_simps norm_ge_zero) }
    then have th: "\<forall>i\<in> ?S. norm ((x$i) *s f (basis i :: real ^'m)) \<le> norm (f (basis i)) * norm x" by metis
    from real_setsum_norm_le[OF fS, of "\<lambda>i. (x$i) *s (f (basis i))", OF th]
    have "norm (f x) \<le> ?B * norm x" unfolding th0 setsum_left_distrib by metis}
  then show ?thesis by blast
qed

lemma linear_bounded_pos:
  fixes f:: "real ^'n::finite \<Rightarrow> real ^ 'm::finite"
  assumes lf: "linear f"
  shows "\<exists>B > 0. \<forall>x. norm (f x) \<le> B * norm x"
proof-
  from linear_bounded[OF lf] obtain B where
    B: "\<forall>x. norm (f x) \<le> B * norm x" by blast
  let ?K = "\<bar>B\<bar> + 1"
  have Kp: "?K > 0" by arith
    {assume C: "B < 0"
      have "norm (1::real ^ 'n) > 0" by (simp add: zero_less_norm_iff)
      with C have "B * norm (1:: real ^ 'n) < 0"
        by (simp add: zero_compare_simps)
      with B[rule_format, of 1] norm_ge_zero[of "f 1"] have False by simp
    }
    then have Bp: "B \<ge> 0" by ferrack
    {fix x::"real ^ 'n"
      have "norm (f x) \<le> ?K *  norm x"
      using B[rule_format, of x] norm_ge_zero[of x] norm_ge_zero[of "f x"] Bp
      apply (auto simp add: ring_simps split add: abs_split)
      apply (erule order_trans, simp)
      done
  }
  then show ?thesis using Kp by blast
qed

lemma smult_conv_scaleR: "c *s x = scaleR c x"
  unfolding vector_scalar_mult_def vector_scaleR_def by simp

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

subsection{* Bilinear functions. *}

definition "bilinear f \<longleftrightarrow> (\<forall>x. linear(\<lambda>y. f x y)) \<and> (\<forall>y. linear(\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h ==> h (x + y) z = (h x z) + (h y z)"
  by (simp add: bilinear_def linear_def)
lemma bilinear_radd: "bilinear h ==> h x (y + z) = (h x y) + (h x z)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lmul: "bilinear h ==> h (c *s x) y = c *s (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_rmul: "bilinear h ==> h x (c *s y) = c *s (h x y)"
  by (simp add: bilinear_def linear_def)

lemma bilinear_lneg: "bilinear h ==> h (- (x:: 'a::ring_1 ^ 'n)) y = -(h x y)"
  by (simp only: vector_sneg_minus1 bilinear_lmul)

lemma bilinear_rneg: "bilinear h ==> h x (- (y:: 'a::ring_1 ^ 'n)) = - h x y"
  by (simp only: vector_sneg_minus1 bilinear_rmul)

lemma  (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  using add_imp_eq[of x y 0] by auto

lemma bilinear_lzero:
  fixes h :: "'a::ring^'n \<Rightarrow> _" assumes bh: "bilinear h" shows "h 0 x = 0"
  using bilinear_ladd[OF bh, of 0 0 x]
    by (simp add: eq_add_iff ring_simps)

lemma bilinear_rzero:
  fixes h :: "'a::ring^'n \<Rightarrow> _" assumes bh: "bilinear h" shows "h x 0 = 0"
  using bilinear_radd[OF bh, of x 0 0 ]
    by (simp add: eq_add_iff ring_simps)

lemma bilinear_lsub: "bilinear h ==> h (x - (y:: 'a::ring_1 ^ 'n)) z = h x z - h y z"
  by (simp  add: diff_def bilinear_ladd bilinear_lneg)

lemma bilinear_rsub: "bilinear h ==> h z (x - (y:: 'a::ring_1 ^ 'n)) = h z x - h z y"
  by (simp  add: diff_def bilinear_radd bilinear_rneg)

lemma bilinear_setsum:
  fixes h:: "'a ^'n \<Rightarrow> 'a::semiring_1^'m \<Rightarrow> 'a ^ 'k"
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
  fixes h:: "real ^'m::finite \<Rightarrow> real^'n::finite \<Rightarrow> real ^ 'k::finite"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
proof-
  let ?M = "UNIV :: 'm set"
  let ?N = "UNIV :: 'n set"
  let ?B = "setsum (\<lambda>(i,j). norm (h (basis i) (basis j))) (?M \<times> ?N)"
  have fM: "finite ?M" and fN: "finite ?N" by simp_all
  {fix x:: "real ^ 'm" and  y :: "real^'n"
    have "norm (h x y) = norm (h (setsum (\<lambda>i. (x$i) *s basis i) ?M) (setsum (\<lambda>i. (y$i) *s basis i) ?N))" unfolding basis_expansion ..
    also have "\<dots> = norm (setsum (\<lambda> (i,j). h ((x$i) *s basis i) ((y$j) *s basis j)) (?M \<times> ?N))"  unfolding bilinear_setsum[OF bh fM fN] ..
    finally have th: "norm (h x y) = \<dots>" .
    have "norm (h x y) \<le> ?B * norm x * norm y"
      apply (simp add: setsum_left_distrib th)
      apply (rule real_setsum_norm_le)
      using fN fM
      apply simp
      apply (auto simp add: bilinear_rmul[OF bh] bilinear_lmul[OF bh] norm_mul ring_simps)
      apply (rule mult_mono)
      apply (auto simp add: norm_ge_zero zero_le_mult_iff component_le_norm)
      apply (rule mult_mono)
      apply (auto simp add: norm_ge_zero zero_le_mult_iff component_le_norm)
      done}
  then show ?thesis by metis
qed

lemma bilinear_bounded_pos:
  fixes h:: "real ^'m::finite \<Rightarrow> real^'n::finite \<Rightarrow> real ^ 'k::finite"
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
      by (auto simp add: norm_ge_zero)
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

lemma adjoint_works_lemma:
  fixes f:: "'a::ring_1 ^'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f"
  shows "\<forall>x y. f x \<bullet> y = x \<bullet> adjoint f y"
proof-
  let ?N = "UNIV :: 'n set"
  let ?M = "UNIV :: 'm set"
  have fN: "finite ?N" by simp
  have fM: "finite ?M" by simp
  {fix y:: "'a ^ 'm"
    let ?w = "(\<chi> i. (f (basis i) \<bullet> y)) :: 'a ^ 'n"
    {fix x
      have "f x \<bullet> y = f (setsum (\<lambda>i. (x$i) *s basis i) ?N) \<bullet> y"
        by (simp only: basis_expansion)
      also have "\<dots> = (setsum (\<lambda>i. (x$i) *s f (basis i)) ?N) \<bullet> y"
        unfolding linear_setsum[OF lf fN]
        by (simp add: linear_cmul[OF lf])
      finally have "f x \<bullet> y = x \<bullet> ?w"
        apply (simp only: )
        apply (simp add: dot_def setsum_left_distrib setsum_right_distrib setsum_commute[of _ ?M ?N] ring_simps)
        done}
  }
  then show ?thesis unfolding adjoint_def
    some_eq_ex[of "\<lambda>f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y"]
    using choice_iff[of "\<lambda>a b. \<forall>x. f x \<bullet> a = x \<bullet> b "]
    by metis
qed

lemma adjoint_works:
  fixes f:: "'a::ring_1 ^'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
  using adjoint_works_lemma[OF lf] by metis


lemma adjoint_linear:
  fixes f :: "'a::comm_ring_1 ^'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  by (simp add: linear_def vector_eq_ldot[symmetric] dot_radd dot_rmult adjoint_works[OF lf])

lemma adjoint_clauses:
  fixes f:: "'a::comm_ring_1 ^'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
  and "adjoint f y \<bullet> x = y \<bullet> f x"
  by (simp_all add: adjoint_works[OF lf] dot_sym )

lemma adjoint_adjoint:
  fixes f:: "'a::comm_ring_1 ^ 'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  apply (rule ext)
  by (simp add: vector_eq_ldot[symmetric] adjoint_clauses[OF adjoint_linear[OF lf]] adjoint_clauses[OF lf])

lemma adjoint_unique:
  fixes f:: "'a::comm_ring_1 ^ 'n::finite \<Rightarrow> 'a ^ 'm::finite"
  assumes lf: "linear f" and u: "\<forall>x y. f' x \<bullet> y = x \<bullet> f y"
  shows "f' = adjoint f"
  apply (rule ext)
  using u
  by (simp add: vector_eq_rdot[symmetric] adjoint_clauses[OF lf])

text{* Matrix notation. NB: an MxN matrix is of type @{typ "'a^'n^'m"}, not @{typ "'a^'m^'n"} *}

consts generic_mult :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<star>" 75)

defs (overloaded)
matrix_matrix_mult_def: "(m:: ('a::semiring_1) ^'n^'m) \<star> (m' :: 'a ^'p^'n) \<equiv> (\<chi> i j. setsum (\<lambda>k. ((m$i)$k) * ((m'$k)$j)) (UNIV :: 'n set)) ::'a ^ 'p ^'m"

abbreviation
  matrix_matrix_mult' :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'p^'n \<Rightarrow> 'a ^ 'p ^'m"  (infixl "**" 70)
  where "m ** m' == m\<star> m'"

defs (overloaded)
  matrix_vector_mult_def: "(m::('a::semiring_1) ^'n^'m) \<star> (x::'a ^'n) \<equiv> (\<chi> i. setsum (\<lambda>j. ((m$i)$j) * (x$j)) (UNIV ::'n set)) :: 'a^'m"

abbreviation
  matrix_vector_mult' :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'm"  (infixl "*v" 70)
  where
  "m *v v == m \<star> v"

defs (overloaded)
  vector_matrix_mult_def: "(x::'a^'m) \<star> (m::('a::semiring_1) ^'n^'m) \<equiv> (\<chi> j. setsum (\<lambda>i. ((m$i)$j) * (x$i)) (UNIV :: 'm set)) :: 'a^'n"

abbreviation
  vactor_matrix_mult' :: "'a ^ 'm \<Rightarrow> ('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n "  (infixl "v*" 70)
  where
  "v v* m == v \<star> m"

definition "(mat::'a::zero => 'a ^'n^'n) k = (\<chi> i j. if i = j then k else 0)"
definition "(transp::'a^'n^'m \<Rightarrow> 'a^'m^'n) A = (\<chi> i j. ((A$j)$i))"
definition "(row::'m => 'a ^'n^'m \<Rightarrow> 'a ^'n) i A = (\<chi> j. ((A$i)$j))"
definition "(column::'n =>'a^'n^'m =>'a^'m) j A = (\<chi> i. ((A$i)$j))"
definition "rows(A::'a^'n^'m) = { row i A | i. i \<in> (UNIV :: 'm set)}"
definition "columns(A::'a^'n^'m) = { column i A | i. i \<in> (UNIV :: 'n set)}"

lemma mat_0[simp]: "mat 0 = 0" by (vector mat_def)
lemma matrix_add_ldistrib: "(A ** (B + C)) = (A \<star> B) + (A \<star> C)"
  by (vector matrix_matrix_mult_def setsum_addf[symmetric] ring_simps)

lemma matrix_mul_lid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n::finite"
  shows "mat 1 ** A = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  by (auto simp only: cond_value_iff cond_application_beta setsum_delta'[OF finite]  mult_1_left mult_zero_left if_True UNIV_I)


lemma matrix_mul_rid:
  fixes A :: "'a::semiring_1 ^ 'm::finite ^ 'n"
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

lemma matrix_vector_mul_lid: "mat 1 *v x = (x::'a::semiring_1 ^ 'n::finite)"
  apply (vector matrix_vector_mult_def mat_def)
  by (simp add: cond_value_iff cond_application_beta
    setsum_delta' cong del: if_weak_cong)

lemma matrix_transp_mul: "transp(A ** B) = transp B ** transp (A::'a::comm_semiring_1^'m^'n)"
  by (simp add: matrix_matrix_mult_def transp_def Cart_eq mult_commute)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n::finite ^ 'm"
  shows "A = B \<longleftrightarrow>  (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
  apply auto
  apply (subst Cart_eq)
  apply clarify
  apply (clarsimp simp add: matrix_vector_mult_def basis_def cond_value_iff cond_application_beta Cart_eq cong del: if_weak_cong)
  apply (erule_tac x="basis ia" in allE)
  apply (erule_tac x="i" in allE)
  by (auto simp add: basis_def cond_value_iff cond_application_beta setsum_delta[OF finite] cong del: if_weak_cong)

lemma matrix_vector_mul_component:
  shows "((A::'a::semiring_1^'n'^'m) *v x)$k = (A$k) \<bullet> x"
  by (simp add: matrix_vector_mult_def dot_def)

lemma dot_lmul_matrix: "((x::'a::comm_semiring_1 ^'n) v* A) \<bullet> y = x \<bullet> (A *v y)"
  apply (simp add: dot_def matrix_vector_mult_def vector_matrix_mult_def setsum_left_distrib setsum_right_distrib mult_ac)
  apply (subst setsum_commute)
  by simp

lemma transp_mat: "transp (mat n) = mat n"
  by (vector transp_def mat_def)

lemma transp_transp: "transp(transp A) = A"
  by (vector transp_def)

lemma row_transp:
  fixes A:: "'a::semiring_1^'n^'m"
  shows "row i (transp A) = column i A"
  by (simp add: row_def column_def transp_def Cart_eq)

lemma column_transp:
  fixes A:: "'a::semiring_1^'n^'m"
  shows "column i (transp A) = row i A"
  by (simp add: row_def column_def transp_def Cart_eq)

lemma rows_transp: "rows(transp (A::'a::semiring_1^'n^'m)) = columns A"
by (auto simp add: rows_def columns_def row_transp intro: set_ext)

lemma columns_transp: "columns(transp (A::'a::semiring_1^'n^'m)) = rows A" by (metis transp_transp rows_transp)

text{* Two sometimes fruitful ways of looking at matrix-vector multiplication. *}

lemma matrix_mult_dot: "A *v x = (\<chi> i. A$i \<bullet> x)"
  by (simp add: matrix_vector_mult_def dot_def)

lemma matrix_mult_vsum: "(A::'a::comm_semiring_1^'n^'m) *v x = setsum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def Cart_eq column_def mult_commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n::finite) = (\<chi> j. setsum (\<lambda>i. (x$i) * (basis i :: 'a^'n)$j) (UNIV :: 'n set))"
  apply (subst basis_expansion[symmetric])
  by (vector Cart_eq setsum_component)

lemma linear_componentwise:
  fixes f:: "'a::ring_1 ^ 'm::finite \<Rightarrow> 'a ^ 'n"
  assumes lf: "linear f"
  shows "(f x)$j = setsum (\<lambda>i. (x$i) * (f (basis i)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof-
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (setsum (\<lambda>i.(x$i) *s f (basis i) ) ?M)$j"
    unfolding vector_smult_component[symmetric]
    unfolding setsum_component[of "(\<lambda>i.(x$i) *s f (basis i :: 'a^'m))" ?M]
    ..
  then show ?thesis unfolding linear_setsum_mul[OF lf fM, symmetric] basis_expansion ..
qed

text{* Inverse matrices  (not necessarily square) *}

definition "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition "matrix_inv(A:: 'a::semiring_1^'n^'m) =
        (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

text{* Correspondence between matrices and linear operators. *}

definition matrix:: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
where "matrix f = (\<chi> i j. (f(basis j))$i)"

lemma matrix_vector_mul_linear: "linear(\<lambda>x. A *v (x::'a::comm_semiring_1 ^ 'n))"
  by (simp add: linear_def matrix_vector_mult_def Cart_eq ring_simps setsum_right_distrib setsum_addf)

lemma matrix_works: assumes lf: "linear f" shows "matrix f *v x = f (x::'a::comm_ring_1 ^ 'n::finite)"
apply (simp add: matrix_def matrix_vector_mult_def Cart_eq mult_commute)
apply clarify
apply (rule linear_componentwise[OF lf, symmetric])
done

lemma matrix_vector_mul: "linear f ==> f = (\<lambda>x. matrix f *v (x::'a::comm_ring_1 ^ 'n::finite))" by (simp add: ext matrix_works)

lemma matrix_of_matrix_vector_mul: "matrix(\<lambda>x. A *v (x :: 'a:: comm_ring_1 ^ 'n::finite)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)

lemma matrix_compose:
  assumes lf: "linear (f::'a::comm_ring_1^'n::finite \<Rightarrow> 'a^'m::finite)"
  and lg: "linear (g::'a::comm_ring_1^'m::finite \<Rightarrow> 'a^'k)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp  add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_vector_column:"(A::'a::comm_semiring_1^'n^'m) *v x = setsum (\<lambda>i. (x$i) *s ((transp A)$i)) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def transp_def Cart_eq mult_commute)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::'a::comm_ring_1^'n::finite^'m::finite) *v x) = (\<lambda>x. transp A *v x)"
  apply (rule adjoint_unique[symmetric])
  apply (rule matrix_vector_mul_linear)
  apply (simp add: transp_def dot_def matrix_vector_mult_def setsum_left_distrib setsum_right_distrib)
  apply (subst setsum_commute)
  apply (auto simp add: mult_ac)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: 'a::comm_ring_1^'n::finite \<Rightarrow> 'a ^ 'm::finite)"
  shows "matrix(adjoint f) = transp(matrix f)"
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
  hence th: "u * a + v * a = a" by (simp add: ring_simps)
  from xa u have "u \<noteq> 0 \<Longrightarrow> u*x < u*a" by (simp add: mult_compare_simps)
  from ya v have "v \<noteq> 0 \<Longrightarrow> v * y < v * a" by (simp add: mult_compare_simps)
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
  also have "\<dots> \<le> (u + v) * a" by (simp add: ring_simps)
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
  have "y^2 + z^2 \<le> y^2 + 2*y*z + z^2" using z y  by (simp add: zero_compare_simps)
  with xy have th: "x ^2 \<le> (y+z)^2" by (simp add: power2_eq_square ring_simps)
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

subsection{* Operator norm. *}

definition "onorm f = Sup {norm (f x)| x. norm x = 1}"

lemma norm_bound_generalize:
  fixes f:: "real ^'n::finite \<Rightarrow> real^'m::finite"
  assumes lf: "linear f"
  shows "(\<forall>x. norm x = 1 \<longrightarrow> norm (f x) \<le> b) \<longleftrightarrow> (\<forall>x. norm (f x) \<le> b * norm x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume H: ?rhs
    {fix x :: "real^'n" assume x: "norm x = 1"
      from H[rule_format, of x] x have "norm (f x) \<le> b" by simp}
    then have ?lhs by blast }

  moreover
  {assume H: ?lhs
    from H[rule_format, of "basis arbitrary"]
    have bp: "b \<ge> 0" using norm_ge_zero[of "f (basis arbitrary)"]
      by (auto simp add: norm_basis elim: order_trans [OF norm_ge_zero])
    {fix x :: "real ^'n"
      {assume "x = 0"
        then have "norm (f x) \<le> b * norm x" by (simp add: linear_0[OF lf] bp)}
      moreover
      {assume x0: "x \<noteq> 0"
        hence n0: "norm x \<noteq> 0" by (metis norm_eq_zero)
        let ?c = "1/ norm x"
        have "norm (?c*s x) = 1" using x0 by (simp add: n0 norm_mul)
        with H have "norm (f(?c*s x)) \<le> b" by blast
        hence "?c * norm (f x) \<le> b"
          by (simp add: linear_cmul[OF lf] norm_mul)
        hence "norm (f x) \<le> b * norm x"
          using n0 norm_ge_zero[of x] by (auto simp add: field_simps)}
      ultimately have "norm (f x) \<le> b * norm x" by blast}
    then have ?rhs by blast}
  ultimately show ?thesis by blast
qed

lemma onorm:
  fixes f:: "real ^'n::finite \<Rightarrow> real ^'m::finite"
  assumes lf: "linear f"
  shows "norm (f x) <= onorm f * norm x"
  and "\<forall>x. norm (f x) <= b * norm x \<Longrightarrow> onorm f <= b"
proof-
  {
    let ?S = "{norm (f x) |x. norm x = 1}"
    have Se: "?S \<noteq> {}" using  norm_basis by auto
    from linear_bounded[OF lf] have b: "\<exists> b. ?S *<= b"
      unfolding norm_bound_generalize[OF lf, symmetric] by (auto simp add: setle_def)
    {from Sup[OF Se b, unfolded onorm_def[symmetric]]
      show "norm (f x) <= onorm f * norm x"
        apply -
        apply (rule spec[where x = x])
        unfolding norm_bound_generalize[OF lf, symmetric]
        by (auto simp add: isLub_def isUb_def leastP_def setge_def setle_def)}
    {
      show "\<forall>x. norm (f x) <= b * norm x \<Longrightarrow> onorm f <= b"
        using Sup[OF Se b, unfolded onorm_def[symmetric]]
        unfolding norm_bound_generalize[OF lf, symmetric]
        by (auto simp add: isLub_def isUb_def leastP_def setge_def setle_def)}
  }
qed

lemma onorm_pos_le: assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite)" shows "0 <= onorm f"
  using order_trans[OF norm_ge_zero onorm(1)[OF lf, of "basis arbitrary"], unfolded norm_basis] by simp

lemma onorm_eq_0: assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite)"
  shows "onorm f = 0 \<longleftrightarrow> (\<forall>x. f x = 0)"
  using onorm[OF lf]
  apply (auto simp add: onorm_pos_le)
  apply atomize
  apply (erule allE[where x="0::real"])
  using onorm_pos_le[OF lf]
  apply arith
  done

lemma onorm_const: "onorm(\<lambda>x::real^'n::finite. (y::real ^ 'm::finite)) = norm y"
proof-
  let ?f = "\<lambda>x::real^'n. (y::real ^ 'm)"
  have th: "{norm (?f x)| x. norm x = 1} = {norm y}"
    by(auto intro: vector_choose_size set_ext)
  show ?thesis
    unfolding onorm_def th
    apply (rule Sup_unique) by (simp_all  add: setle_def)
qed

lemma onorm_pos_lt: assumes lf: "linear (f::real ^ 'n::finite \<Rightarrow> real ^'m::finite)"
  shows "0 < onorm f \<longleftrightarrow> ~(\<forall>x. f x = 0)"
  unfolding onorm_eq_0[OF lf, symmetric]
  using onorm_pos_le[OF lf] by arith

lemma onorm_compose:
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite)"
  and lg: "linear (g::real^'k::finite \<Rightarrow> real^'n::finite)"
  shows "onorm (f o g) <= onorm f * onorm g"
  apply (rule onorm(2)[OF linear_compose[OF lg lf], rule_format])
  unfolding o_def
  apply (subst mult_assoc)
  apply (rule order_trans)
  apply (rule onorm(1)[OF lf])
  apply (rule mult_mono1)
  apply (rule onorm(1)[OF lg])
  apply (rule onorm_pos_le[OF lf])
  done

lemma onorm_neg_lemma: assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real^'m::finite)"
  shows "onorm (\<lambda>x. - f x) \<le> onorm f"
  using onorm[OF linear_compose_neg[OF lf]] onorm[OF lf]
  unfolding norm_minus_cancel by metis

lemma onorm_neg: assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real^'m::finite)"
  shows "onorm (\<lambda>x. - f x) = onorm f"
  using onorm_neg_lemma[OF lf] onorm_neg_lemma[OF linear_compose_neg[OF lf]]
  by simp

lemma onorm_triangle:
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite)" and lg: "linear g"
  shows "onorm (\<lambda>x. f x + g x) <= onorm f + onorm g"
  apply(rule onorm(2)[OF linear_compose_add[OF lf lg], rule_format])
  apply (rule order_trans)
  apply (rule norm_triangle_ineq)
  apply (simp add: distrib)
  apply (rule add_mono)
  apply (rule onorm(1)[OF lf])
  apply (rule onorm(1)[OF lg])
  done

lemma onorm_triangle_le: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite) \<Longrightarrow> linear g \<Longrightarrow> onorm(f) + onorm(g) <= e
  \<Longrightarrow> onorm(\<lambda>x. f x + g x) <= e"
  apply (rule order_trans)
  apply (rule onorm_triangle)
  apply assumption+
  done

lemma onorm_triangle_lt: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite) \<Longrightarrow> linear g \<Longrightarrow> onorm(f) + onorm(g) < e
  ==> onorm(\<lambda>x. f x + g x) < e"
  apply (rule order_le_less_trans)
  apply (rule onorm_triangle)
  by assumption+

(* "lift" from 'a to 'a^1 and "drop" from 'a^1 to 'a -- FIXME: potential use of transfer *)

definition vec1:: "'a \<Rightarrow> 'a ^ 1" where "vec1 x = (\<chi> i. x)"

definition dest_vec1:: "'a ^1 \<Rightarrow> 'a"
  where "dest_vec1 x = (x$1)"

lemma vec1_component[simp]: "(vec1 x)$1 = x"
  by (simp add: vec1_def)

lemma vec1_dest_vec1[simp]: "vec1(dest_vec1 x) = x" "dest_vec1(vec1 y) = y"
  by (simp_all add: vec1_def dest_vec1_def Cart_eq forall_1)

lemma forall_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (vec1 x))" by (metis vec1_dest_vec1)

lemma exists_vec1: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P(vec1 x))" by (metis vec1_dest_vec1)

lemma forall_dest_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P(dest_vec1 x))"  by (metis vec1_dest_vec1)

lemma exists_dest_vec1: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P(dest_vec1 x))"by (metis vec1_dest_vec1)

lemma vec1_eq[simp]:  "vec1 x = vec1 y \<longleftrightarrow> x = y" by (metis vec1_dest_vec1)

lemma dest_vec1_eq[simp]: "dest_vec1 x = dest_vec1 y \<longleftrightarrow> x = y" by (metis vec1_dest_vec1)

lemma vec1_in_image_vec1: "vec1 x \<in> (vec1 ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec1_vec: "vec1 x = vec x" by (vector vec1_def)

lemma vec1_add: "vec1(x + y) = vec1 x + vec1 y" by (vector vec1_def)
lemma vec1_sub: "vec1(x - y) = vec1 x - vec1 y" by (vector vec1_def)
lemma vec1_cmul: "vec1(c* x) = c *s vec1 x " by (vector vec1_def)
lemma vec1_neg: "vec1(- x) = - vec1 x " by (vector vec1_def)

lemma vec1_setsum: assumes fS: "finite S"
  shows "vec1(setsum f S) = setsum (vec1 o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply (simp add: vec1_vec)
  apply (auto simp add: vec1_add)
  done

lemma dest_vec1_lambda: "dest_vec1(\<chi> i. x i) = x 1"
  by (simp add: dest_vec1_def)

lemma dest_vec1_vec: "dest_vec1(vec x) = x"
  by (simp add: vec1_vec[symmetric])

lemma dest_vec1_add: "dest_vec1(x + y) = dest_vec1 x + dest_vec1 y"
 by (metis vec1_dest_vec1 vec1_add)

lemma dest_vec1_sub: "dest_vec1(x - y) = dest_vec1 x - dest_vec1 y"
 by (metis vec1_dest_vec1 vec1_sub)

lemma dest_vec1_cmul: "dest_vec1(c*sx) = c * dest_vec1 x"
 by (metis vec1_dest_vec1 vec1_cmul)

lemma dest_vec1_neg: "dest_vec1(- x) = - dest_vec1 x"
 by (metis vec1_dest_vec1 vec1_neg)

lemma dest_vec1_0[simp]: "dest_vec1 0 = 0" by (metis vec_0 dest_vec1_vec)

lemma dest_vec1_sum: assumes fS: "finite S"
  shows "dest_vec1(setsum f S) = setsum (dest_vec1 o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply (simp add: dest_vec1_vec)
  apply (auto simp add: dest_vec1_add)
  done

lemma norm_vec1: "norm(vec1 x) = abs(x)"
  by (simp add: vec1_def norm_real)

lemma dist_vec1: "dist(vec1 x) (vec1 y) = abs(x - y)"
  by (simp only: dist_real vec1_component)
lemma abs_dest_vec1: "norm x = \<bar>dest_vec1 x\<bar>"
  by (metis vec1_dest_vec1 norm_vec1)

lemma linear_vmul_dest_vec1:
  fixes f:: "'a::semiring_1^'n \<Rightarrow> 'a^1"
  shows "linear f \<Longrightarrow> linear (\<lambda>x. dest_vec1(f x) *s v)"
  unfolding dest_vec1_def
  apply (rule linear_vmul_component)
  by auto

lemma linear_from_scalars:
  assumes lf: "linear (f::'a::comm_ring_1 ^1 \<Rightarrow> 'a^'n)"
  shows "f = (\<lambda>x. dest_vec1 x *s column 1 (matrix f))"
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (auto simp add: Cart_eq matrix_vector_mult_def dest_vec1_def column_def  mult_commute UNIV_1)
  done

lemma linear_to_scalars: assumes lf: "linear (f::'a::comm_ring_1 ^'n::finite \<Rightarrow> 'a^1)"
  shows "f = (\<lambda>x. vec1(row 1 (matrix f) \<bullet> x))"
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (simp add: Cart_eq matrix_vector_mult_def vec1_def row_def dot_def mult_commute forall_1)
  done

lemma dest_vec1_eq_0: "dest_vec1 x = 0 \<longleftrightarrow> x = 0"
  by (simp add: dest_vec1_eq[symmetric])

lemma setsum_scalars: assumes fS: "finite S"
  shows "setsum f S = vec1 (setsum (dest_vec1 o f) S)"
  unfolding vec1_setsum[OF fS] by simp

lemma dest_vec1_wlog_le: "(\<And>(x::'a::linorder ^ 1) y. P x y \<longleftrightarrow> P y x)  \<Longrightarrow> (\<And>x y. dest_vec1 x <= dest_vec1 y ==> P x y) \<Longrightarrow> P x y"
  apply (cases "dest_vec1 x \<le> dest_vec1 y")
  apply simp
  apply (subgoal_tac "dest_vec1 y \<le> dest_vec1 x")
  apply (auto)
  done

text{* Pasting vectors. *}

lemma linear_fstcart: "linear fstcart"
  by (auto simp add: linear_def Cart_eq)

lemma linear_sndcart: "linear sndcart"
  by (auto simp add: linear_def Cart_eq)

lemma fstcart_vec[simp]: "fstcart(vec x) = vec x"
  by (simp add: Cart_eq)

lemma fstcart_add[simp]:"fstcart(x + y) = fstcart (x::'a::{plus,times}^('b + 'c)) + fstcart y"
  by (simp add: Cart_eq)

lemma fstcart_cmul[simp]:"fstcart(c*s x) = c*s fstcart (x::'a::{plus,times}^('b + 'c))"
  by (simp add: Cart_eq)

lemma fstcart_neg[simp]:"fstcart(- x) = - fstcart (x::'a::ring_1^('b + 'c))"
  by (simp add: Cart_eq)

lemma fstcart_sub[simp]:"fstcart(x - y) = fstcart (x::'a::ring_1^('b + 'c)) - fstcart y"
  by (simp add: Cart_eq)

lemma fstcart_setsum:
  fixes f:: "'d \<Rightarrow> 'a::semiring_1^_"
  assumes fS: "finite S"
  shows "fstcart (setsum f S) = setsum (\<lambda>i. fstcart (f i)) S"
  by (induct rule: finite_induct[OF fS], simp_all add: vec_0[symmetric] del: vec_0)

lemma sndcart_vec[simp]: "sndcart(vec x) = vec x"
  by (simp add: Cart_eq)

lemma sndcart_add[simp]:"sndcart(x + y) = sndcart (x::'a::{plus,times}^('b + 'c)) + sndcart y"
  by (simp add: Cart_eq)

lemma sndcart_cmul[simp]:"sndcart(c*s x) = c*s sndcart (x::'a::{plus,times}^('b + 'c))"
  by (simp add: Cart_eq)

lemma sndcart_neg[simp]:"sndcart(- x) = - sndcart (x::'a::ring_1^('b + 'c))"
  by (simp add: Cart_eq)

lemma sndcart_sub[simp]:"sndcart(x - y) = sndcart (x::'a::ring_1^('b + 'c)) - sndcart y"
  by (simp add: Cart_eq)

lemma sndcart_setsum:
  fixes f:: "'d \<Rightarrow> 'a::semiring_1^_"
  assumes fS: "finite S"
  shows "sndcart (setsum f S) = setsum (\<lambda>i. sndcart (f i)) S"
  by (induct rule: finite_induct[OF fS], simp_all add: vec_0[symmetric] del: vec_0)

lemma pastecart_vec[simp]: "pastecart (vec x) (vec x) = vec x"
  by (simp add: pastecart_eq fstcart_pastecart sndcart_pastecart)

lemma pastecart_add[simp]:"pastecart (x1::'a::{plus,times}^_) y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)"
  by (simp add: pastecart_eq fstcart_pastecart sndcart_pastecart)

lemma pastecart_cmul[simp]: "pastecart (c *s (x1::'a::{plus,times}^_)) (c *s y1) = c *s pastecart x1 y1"
  by (simp add: pastecart_eq fstcart_pastecart sndcart_pastecart)

lemma pastecart_neg[simp]: "pastecart (- (x::'a::ring_1^_)) (- y) = - pastecart x y"
  unfolding vector_sneg_minus1 pastecart_cmul ..

lemma pastecart_sub: "pastecart (x1::'a::ring_1^_) y1 - pastecart x2 y2 = pastecart (x1 - x2) (y1 - y2)"
  by (simp add: diff_def pastecart_neg[symmetric] del: pastecart_neg)

lemma pastecart_setsum:
  fixes f:: "'d \<Rightarrow> 'a::semiring_1^_"
  assumes fS: "finite S"
  shows "pastecart (setsum f S) (setsum g S) = setsum (\<lambda>i. pastecart (f i) (g i)) S"
  by (simp  add: pastecart_eq fstcart_setsum[OF fS] sndcart_setsum[OF fS] fstcart_pastecart sndcart_pastecart)

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

lemma norm_fstcart: "norm(fstcart x) <= norm (x::real ^('n::finite + 'm::finite))"
proof-
  have th0: "norm x = norm (pastecart (fstcart x) (sndcart x))"
    by (simp add: pastecart_fst_snd)
  have th1: "fstcart x \<bullet> fstcart x \<le> pastecart (fstcart x) (sndcart x) \<bullet> pastecart (fstcart x) (sndcart x)"
    by (simp add: dot_def setsum_UNIV_sum pastecart_def setsum_nonneg)
  then show ?thesis
    unfolding th0
    unfolding real_vector_norm_def real_sqrt_le_iff id_def
    by (simp add: dot_def)
qed

lemma dist_fstcart: "dist(fstcart (x::real^_)) (fstcart y) <= dist x y"
  unfolding dist_norm by (metis fstcart_sub[symmetric] norm_fstcart)

lemma norm_sndcart: "norm(sndcart x) <= norm (x::real ^('n::finite + 'm::finite))"
proof-
  have th0: "norm x = norm (pastecart (fstcart x) (sndcart x))"
    by (simp add: pastecart_fst_snd)
  have th1: "sndcart x \<bullet> sndcart x \<le> pastecart (fstcart x) (sndcart x) \<bullet> pastecart (fstcart x) (sndcart x)"
    by (simp add: dot_def setsum_UNIV_sum pastecart_def setsum_nonneg)
  then show ?thesis
    unfolding th0
    unfolding real_vector_norm_def real_sqrt_le_iff id_def
    by (simp add: dot_def)
qed

lemma dist_sndcart: "dist(sndcart (x::real^_)) (sndcart y) <= dist x y"
  unfolding dist_norm by (metis sndcart_sub[symmetric] norm_sndcart)

lemma dot_pastecart: "(pastecart (x1::'a::{times,comm_monoid_add}^'n::finite) (x2::'a::{times,comm_monoid_add}^'m::finite)) \<bullet> (pastecart y1 y2) =  x1 \<bullet> y1 + x2 \<bullet> y2"
  by (simp add: dot_def setsum_UNIV_sum pastecart_def)

text {* TODO: move to NthRoot *}
lemma sqrt_add_le_add_sqrt:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "sqrt (x + y) \<le> sqrt x + sqrt y"
apply (rule power2_le_imp_le)
apply (simp add: real_sum_squared_expand add_nonneg_nonneg x y)
apply (simp add: mult_nonneg_nonneg x y)
apply (simp add: add_nonneg_nonneg x y)
done

lemma norm_pastecart: "norm (pastecart x y) <= norm x + norm y"
  unfolding norm_vector_def setL2_def setsum_UNIV_sum
  by (simp add: sqrt_add_le_add_sqrt setsum_nonneg)

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

lemma hull_subset: "s \<subseteq> (S hull s)"
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
  apply (auto simp add: field_simps inverse_positive_iff_positive)
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
    apply (simp add: ring_simps)
    using mult_left_mono[OF p Suc.prems] by simp
  finally show ?case  by (simp add: real_of_nat_Suc ring_simps)
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
      apply (simp add: ring_simps)
      done
    then have ?thesis by (simp add: ring_simps) }
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
    by (simp add: ring_simps power_add[symmetric])
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
  by (simp add: ring_simps power_add)


subsection{* A bit of linear algebra. *}

definition "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in> S. \<forall>y \<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x \<in>S. c *s x \<in>S )"
definition "span S = (subspace hull S)"
definition "dependent S \<longleftrightarrow> (\<exists>a \<in> S. a \<in> span(S - {a}))"
abbreviation "independent s == ~(dependent s)"

(* Closure properties of subspaces.                                          *)

lemma subspace_UNIV[simp]: "subspace(UNIV)" by (simp add: subspace_def)

lemma subspace_0: "subspace S ==> 0 \<in> S" by (metis subspace_def)

lemma subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S ==> x + y \<in> S"
  by (metis subspace_def)

lemma subspace_mul: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> c *s x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> (x::'a::ring_1^'n) \<in> S \<Longrightarrow> - x \<in> S"
  by (metis vector_sneg_minus1 subspace_mul)

lemma subspace_sub: "subspace S \<Longrightarrow> (x::'a::ring_1^'n) \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  by (metis diff_def subspace_add subspace_neg)

lemma subspace_setsum:
  assumes sA: "subspace A" and fB: "finite B"
  and f: "\<forall>x\<in> B. f x \<in> A"
  shows "setsum f B \<in> A"
  using  fB f sA
  apply(induct rule: finite_induct[OF fB])
  by (simp add: subspace_def sA, auto simp add: sA subspace_add)

lemma subspace_linear_image:
  assumes lf: "linear (f::'a::semiring_1^'n \<Rightarrow> _)" and sS: "subspace S"
  shows "subspace(f ` S)"
  using lf sS linear_0[OF lf]
  unfolding linear_def subspace_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="x + y" in bexI, auto)
  apply (rule_tac x="c*s x" in bexI, auto)
  done

lemma subspace_linear_preimage: "linear (f::'a::semiring_1^'n \<Rightarrow> _) ==> subspace S ==> subspace {x. f x \<in> S}"
  by (auto simp add: subspace_def linear_def linear_0[of f])

lemma subspace_trivial: "subspace {0::'a::semiring_1 ^_}"
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
  "x \<in> span S \<Longrightarrow> c *s x \<in> span S"
  by (metis span_def hull_subset subset_eq subspace_span subspace_def)+

lemma span_induct: assumes SP: "\<And>x. x \<in> S ==> P x"
  and P: "subspace P" and x: "x \<in> span S" shows "P x"
proof-
  from SP have SP': "S \<subseteq> P" by (simp add: mem_def subset_eq)
  from P have P': "P \<in> subspace" by (simp add: mem_def)
  from x hull_minimal[OF SP' P', unfolded span_def[symmetric]]
  show "P x" by (metis mem_def subset_eq)
qed

lemma span_empty: "span {} = {(0::'a::semiring_0 ^ 'n)}"
  apply (simp add: span_def)
  apply (rule hull_unique)
  apply (auto simp add: mem_def subspace_def)
  unfolding mem_def[of "0::'a^'n", symmetric]
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

inductive span_induct_alt_help for S:: "'a::semiring_1^'n \<Rightarrow> bool"
  where
  span_induct_alt_help_0: "span_induct_alt_help S 0"
  | span_induct_alt_help_S: "x \<in> S \<Longrightarrow> span_induct_alt_help S z \<Longrightarrow> span_induct_alt_help S (c *s x + z)"

lemma span_induct_alt':
  assumes h0: "h (0::'a::semiring_1^'n)" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c*s x + y)" shows "\<forall>x \<in> span S. h x"
proof-
  {fix x:: "'a^'n" assume x: "span_induct_alt_help S x"
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
          then have "span_induct_alt_help S (c*s x)"
            apply (induct rule: span_induct_alt_help.induct)
            apply (simp add: span_induct_alt_help_0)
            apply (simp add: vector_smult_assoc vector_add_ldistrib)
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
  assumes h0: "h (0::'a::semiring_1^'n)" and hS: "\<And>c x y. x \<in> S \<Longrightarrow> h y \<Longrightarrow> h (c*s x + y)" and x: "x \<in> span S"
  shows "h x"
using span_induct_alt'[of h S] h0 hS x by blast

(* Individual closure properties. *)

lemma span_superset: "x \<in> S ==> x \<in> span S" by (metis span_clauses)

lemma span_0: "0 \<in> span S" by (metis subspace_span subspace_0)

lemma span_add: "x \<in> span S \<Longrightarrow> y \<in> span S ==> x + y \<in> span S"
  by (metis subspace_add subspace_span)

lemma span_mul: "x \<in> span S ==> (c *s x) \<in> span S"
  by (metis subspace_span subspace_mul)

lemma span_neg: "x \<in> span S ==> - (x::'a::ring_1^'n) \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_sub: "(x::'a::ring_1^'n) \<in> span S \<Longrightarrow> y \<in> span S ==> x - y \<in> span S"
  by (metis subspace_span subspace_sub)

lemma span_setsum: "finite A \<Longrightarrow> \<forall>x \<in> A. f x \<in> span S ==> setsum f A \<in> span S"
  apply (rule subspace_setsum)
  by (metis subspace_span subspace_setsum)+

lemma span_add_eq: "(x::'a::ring_1^'n) \<in> span S \<Longrightarrow> x + y \<in> span S \<longleftrightarrow> y \<in> span S"
  apply (auto simp only: span_add span_sub)
  apply (subgoal_tac "(x + y) - x \<in> span S", simp)
  by (simp only: span_add span_sub)

(* Mapping under linear image. *)

lemma span_linear_image: assumes lf: "linear (f::'a::semiring_1 ^ 'n => _)"
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
  assumes bS: "(b::'a::ring_1 ^ 'n) \<in> S" and aS: "a \<in> span S"
  shows "\<exists>k. a - k*s b \<in> span (S - {b})" (is "?P a")
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
    apply (subgoal_tac "x + y - (k + ka) *s b = (x - k*s b) + (y - ka *s b)")
    apply (simp only: )
    apply (rule span_add[unfolded mem_def])
    apply assumption+
    apply (vector ring_simps)
    apply (clarsimp simp add: mem_def)
    apply (rule_tac x= "c*k" in exI)
    apply (subgoal_tac "c *s x - (c * k) *s b = c*s (x - k*s b)")
    apply (simp only: )
    apply (rule span_mul[unfolded mem_def])
    apply assumption
    by (vector ring_simps)
  ultimately show "?P a" using aS span_induct[where S=S and P= "?P"] by metis
qed

lemma span_breakdown_eq:
  "(x::'a::ring_1^'n) \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. (x - k *s a) \<in> span S)" (is "?lhs \<longleftrightarrow> ?rhs")
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
  { fix k assume k: "x - k *s a \<in> span S"
    have eq: "x = (x - k *s a) + k *s a" by vector
    have "(x - k *s a) + k *s a \<in> span (insert a S)"
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
  assumes a: "(a::'a::field^'n) \<in> span (insert b S)" and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof-
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - k*s b \<in> span (S - {b})" by auto
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
    have eq: "b = (1/k) *s a - ((1/k) *s a - b)" by vector
    from k0 have eq': "(1/k) *s (a - k*s b) = (1/k) *s a - b"
      by (vector field_simps)
    from k have "(1/k) *s (a - k*s b) \<in> span (S - {b})"
      by (rule span_mul)
    hence th: "(1/k) *s a - b \<in> span (S - {b})"
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
  assumes a: "(a::'a::field^'n) \<in> span S"
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
  assumes x: "(x::'a::ring_1^'n) \<in> span S" and y: "y \<in> span (insert x S)"
  shows "y \<in> span S"
proof-
  from span_breakdown[of x "insert x S" y, OF insertI1 y]
  obtain k where k: "y -k*s x \<in> span (S - {x})" by auto
  have eq: "y = (y - k *s x) + k *s x" by vector
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
  "span P = {y::'a::semiring_1^'n. \<exists>S u. finite S \<and> S \<subseteq> P \<and> setsum (\<lambda>v. u v *s v) S = y}"
  (is "_ = ?E" is "_ = {y. ?h y}" is "_ = {y. \<exists>S u. ?Q S u y}")
proof-
  {fix x assume x: "x \<in> ?E"
    then obtain S u where fS: "finite S" and SP: "S\<subseteq>P" and u: "setsum (\<lambda>v. u v *s v) S = x"
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
      and u: "setsum (\<lambda>v. u v *s v) S = y" by blast
    let ?S = "insert x S"
    let ?u = "\<lambda>y. if y = x then (if x \<in> S then u y + c else c)
                  else u y"
    from fS SP x have th0: "finite (insert x S)" "insert x S \<subseteq> P" by blast+
    {assume xS: "x \<in> S"
      have S1: "S = (S - {x}) \<union> {x}"
        and Sss:"finite (S - {x})" "finite {x}" "(S -{x}) \<inter> {x} = {}" using xS fS by auto
      have "setsum (\<lambda>v. ?u v *s v) ?S =(\<Sum>v\<in>S - {x}. u v *s v) + (u x + c) *s x"
        using xS
        by (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]]
          setsum_clauses(2)[OF fS] cong del: if_weak_cong)
      also have "\<dots> = (\<Sum>v\<in>S. u v *s v) + c *s x"
        apply (simp add: setsum_Un_disjoint[OF Sss, unfolded S1[symmetric]])
        by (vector ring_simps)
      also have "\<dots> = c*s x + y"
        by (simp add: add_commute u)
      finally have "setsum (\<lambda>v. ?u v *s v) ?S = c*s x + y" .
    then have "?Q ?S ?u (c*s x + y)" using th0 by blast}
  moreover
  {assume xS: "x \<notin> S"
    have th00: "(\<Sum>v\<in>S. (if v = x then c else u v) *s v) = y"
      unfolding u[symmetric]
      apply (rule setsum_cong2)
      using xS by auto
    have "?Q ?S ?u (c*s x + y)" using fS xS th0
      by (simp add: th00 setsum_clauses add_commute cong del: if_weak_cong)}
  ultimately have "?Q ?S ?u (c*s x + y)"
    by (cases "x \<in> S", simp, simp)
    then show "?h (c*s x + y)"
      apply -
      apply (rule exI[where x="?S"])
      apply (rule exI[where x="?u"]) by metis
  qed
  ultimately show ?thesis by blast
qed

lemma dependent_explicit:
  "dependent P \<longleftrightarrow> (\<exists>S u. finite S \<and> S \<subseteq> P \<and> (\<exists>(v::'a::{idom,field}^'n) \<in>S. u v \<noteq> 0 \<and> setsum (\<lambda>v. u v *s v) S = 0))" (is "?lhs = ?rhs")
proof-
  {assume dP: "dependent P"
    then obtain a S u where aP: "a \<in> P" and fS: "finite S"
      and SP: "S \<subseteq> P - {a}" and ua: "setsum (\<lambda>v. u v *s v) S = a"
      unfolding dependent_def span_explicit by blast
    let ?S = "insert a S"
    let ?u = "\<lambda>y. if y = a then - 1 else u y"
    let ?v = a
    from aP SP have aS: "a \<notin> S" by blast
    from fS SP aP have th0: "finite ?S" "?S \<subseteq> P" "?v \<in> ?S" "?u ?v \<noteq> 0" by auto
    have s0: "setsum (\<lambda>v. ?u v *s v) ?S = 0"
      using fS aS
      apply (simp add: vector_smult_lneg vector_smult_lid setsum_clauses ring_simps )
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
    and u: "setsum (\<lambda>v. u v *s v) S = 0"
    let ?a = v
    let ?S = "S - {v}"
    let ?u = "\<lambda>i. (- u i) / u v"
    have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"       using fS SP vS by auto
    have "setsum (\<lambda>v. ?u v *s v) ?S = setsum (\<lambda>v. (- (inverse (u ?a))) *s (u v *s v)) S - ?u v *s v"
      using fS vS uv
      by (simp add: setsum_diff1 vector_smult_lneg divide_inverse
        vector_smult_assoc field_simps)
    also have "\<dots> = ?a"
      unfolding setsum_cmul u
      using uv by (simp add: vector_smult_lneg)
    finally  have "setsum (\<lambda>v. ?u v *s v) ?S = ?a" .
    with th0 have ?lhs
      unfolding dependent_def span_explicit
      apply -
      apply (rule bexI[where x= "?a"])
      apply simp_all
      apply (rule exI[where x= "?S"])
      by auto}
  ultimately show ?thesis by blast
qed


lemma span_finite:
  assumes fS: "finite S"
  shows "span S = {(y::'a::semiring_1^'n). \<exists>u. setsum (\<lambda>v. u v *s v) S = y}"
  (is "_ = ?rhs")
proof-
  {fix y assume y: "y \<in> span S"
    from y obtain S' u where fS': "finite S'" and SS': "S' \<subseteq> S" and
      u: "setsum (\<lambda>v. u v *s v) S' = y" unfolding span_explicit by blast
    let ?u = "\<lambda>x. if x \<in> S' then u x else 0"
    from setsum_restrict_set[OF fS, of "\<lambda>v. u v *s v" S', symmetric] SS'
    have "setsum (\<lambda>v. ?u v *s v) S = setsum (\<lambda>v. u v *s v) S'"
      unfolding cond_value_iff cond_application_beta
      by (simp add: cond_value_iff inf_absorb2 cong del: if_weak_cong)
    hence "setsum (\<lambda>v. ?u v *s v) S = y" by (metis u)
    hence "y \<in> ?rhs" by auto}
  moreover
  {fix y u assume u: "setsum (\<lambda>v. u v *s v) S = y"
    then have "y \<in> span S" using fS unfolding span_explicit by auto}
  ultimately show ?thesis by blast
qed


(* Standard bases are a spanning set, and obviously finite.                  *)

lemma span_stdbasis:"span {basis i :: 'a::ring_1^'n::finite | i. i \<in> (UNIV :: 'n set)} = UNIV"
apply (rule set_ext)
apply auto
apply (subst basis_expansion[symmetric])
apply (rule span_setsum)
apply simp
apply auto
apply (rule span_mul)
apply (rule span_superset)
apply (auto simp add: Collect_def mem_def)
done

lemma has_size_stdbasis: "{basis i ::real ^'n::finite | i. i \<in> (UNIV :: 'n set)} hassize CARD('n)" (is "?S hassize ?n")
proof-
  have eq: "?S = basis ` UNIV" by blast
  show ?thesis unfolding eq
    apply (rule hassize_image_inj[OF basis_inj])
    by (simp add: hassize_def)
qed

lemma finite_stdbasis: "finite {basis i ::real^'n::finite |i. i\<in> (UNIV:: 'n set)}"
  using has_size_stdbasis[unfolded hassize_def]
  ..

lemma card_stdbasis: "card {basis i ::real^'n::finite |i. i\<in> (UNIV :: 'n set)} = CARD('n)"
  using has_size_stdbasis[unfolded hassize_def]
  ..

lemma independent_stdbasis_lemma:
  assumes x: "(x::'a::semiring_1 ^ 'n) \<in> span (basis ` S)"
  and iS: "i \<notin> S"
  shows "(x$i) = 0"
proof-
  let ?U = "UNIV :: 'n set"
  let ?B = "basis ` S"
  let ?P = "\<lambda>(x::'a^'n). \<forall>i\<in> ?U. i \<notin> S \<longrightarrow> x$i =0"
 {fix x::"'a^'n" assume xS: "x\<in> ?B"
   from xS have "?P x" by auto}
 moreover
 have "subspace ?P"
   by (auto simp add: subspace_def Collect_def mem_def)
 ultimately show ?thesis
   using x span_induct[of ?B ?P x] iS by blast
qed

lemma independent_stdbasis: "independent {basis i ::real^'n::finite |i. i\<in> (UNIV :: 'n set)}"
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
  "independent(insert (a::'a::field ^'n) S) \<longleftrightarrow>
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
  assumes BA: "B \<subseteq> A" and iA: "independent (A::('a::field ^'n) set)"
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
  assumes f:"finite (t:: ('a::field^'n) set)" and i: "independent s"
  and sp:"s \<subseteq> span t"
  shows "\<exists>t'. (t' hassize card t) \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
using f i sp
proof(induct c\<equiv>"card(t - s)" arbitrary: s t rule: nat_less_induct)
  fix n:: nat and s t :: "('a ^'n) set"
  assume H: " \<forall>m<n. \<forall>(x:: ('a ^'n) set) xa.
                finite xa \<longrightarrow>
                independent x \<longrightarrow>
                x \<subseteq> span xa \<longrightarrow>
                m = card (xa - x) \<longrightarrow>
                (\<exists>t'. (t' hassize card xa) \<and>
                      x \<subseteq> t' \<and> t' \<subseteq> x \<union> xa \<and> x \<subseteq> span t')"
    and ft: "finite t" and s: "independent s" and sp: "s \<subseteq> span t"
    and n: "n = card (t - s)"
  let ?P = "\<lambda>t'. (t' hassize card t) \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"
  {assume st: "s \<subseteq> t"
    from st ft span_mono[OF st] have ?ths apply - apply (rule exI[where x=t])
      by (auto simp add: hassize_def intro: span_superset)}
  moreover
  {assume st: "t \<subseteq> s"

    from spanning_subset_independent[OF st s sp]
      st ft span_mono[OF st] have ?ths apply - apply (rule exI[where x=t])
      by (auto simp add: hassize_def intro: span_superset)}
  moreover
  {assume st: "\<not> s \<subseteq> t" "\<not> t \<subseteq> s"
    from st(2) obtain b where b: "b \<in> t" "b \<notin> s" by blast
      from b have "t - {b} - s \<subset> t - s" by blast
      then have cardlt: "card (t - {b} - s) < n" using n ft
        by (auto intro: psubset_card_mono)
      from b ft have ct0: "card t \<noteq> 0" by auto
    {assume stb: "s \<subseteq> span(t -{b})"
      from ft have ftb: "finite (t -{b})" by auto
      from H[rule_format, OF cardlt ftb s stb]
      obtain u where u: "u hassize card (t-{b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u" using u by blast
      from u(3) b have "u \<subseteq> s \<union> t" by blast
      then have th1: "insert b u \<subseteq> s \<union> t" using u b by blast
      have bu: "b \<notin> u" using b u by blast
      from u(1) have fu: "finite u" by (simp add: hassize_def)
      from u(1) ft b have "u hassize (card t - 1)" by auto
      then
      have th2: "insert b u hassize card t"
        using  card_insert_disjoint[OF fu bu] ct0 by (auto simp add: hassize_def)
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)" apply (rule span_mono) by blast
      finally have th3: "s \<subseteq> span (insert b u)" .      from th0 th1 th2 th3 have th: "?P ?w"  by blast
      from th have ?ths by blast}
    moreover
    {assume stb: "\<not> s \<subseteq> span(t -{b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})" by blast
      have ab: "a \<noteq> b" using a b by blast
      have at: "a \<notin> t" using a ab span_superset[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < n"
        using cardlt ft n  a b by auto
      have ft': "finite (insert a (t - {b}))" using ft by auto
      {fix x assume xs: "x \<in> s"
        have t: "t \<subseteq> (insert b (insert a (t -{b})))" using b by auto
        from b(1) have "b \<in> span t" by (simp add: span_superset)
        have bs: "b \<in> span (insert a (t - {b}))"
          by (metis in_span_delete a sp mem_def subset_eq)
        from xs sp have "x \<in> span t" by blast
        with span_mono[OF t]
        have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))"  .}
      then have sp': "s \<subseteq> span (insert a (t - {b}))" by blast

      from H[rule_format, OF mlt ft' s sp' refl] obtain u where
        u: "u hassize card (insert a (t -{b}))" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t -{b})"
        "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u" by (auto simp add: hassize_def)
      then have ?ths by blast }
    ultimately have ?ths by blast
  }
  ultimately
  show ?ths  by blast
qed

(* This implies corresponding size bounds.                                   *)

lemma independent_span_bound:
  assumes f: "finite t" and i: "independent (s::('a::field^'n) set)" and sp:"s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] hassize_def finite_subset card_mono)


lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x\<in> (UNIV::'a::finite set)}"
proof-
  have eq: "{f x |x. x\<in> UNIV} = f ` UNIV" by auto
  show ?thesis unfolding eq
    apply (rule finite_imageI)
    apply (rule finite)
    done
qed


lemma independent_bound:
  fixes S:: "(real^'n::finite) set"
  shows "independent S \<Longrightarrow> finite S \<and> card S <= CARD('n)"
  apply (subst card_stdbasis[symmetric])
  apply (rule independent_span_bound)
  apply (rule finite_Atleast_Atmost_nat)
  apply assumption
  unfolding span_stdbasis
  apply (rule subset_UNIV)
  done

lemma dependent_biggerset: "(finite (S::(real ^'n::finite) set) ==> card S > CARD('n)) ==> dependent S"
  by (metis independent_bound not_less)

(* Hence we can create a maximal independent subset.                         *)

lemma maximal_independent_subset_extend:
  assumes sv: "(S::(real^'n::finite) set) \<subseteq> V" and iS: "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  using sv iS
proof(induct d\<equiv> "CARD('n) - card S" arbitrary: S rule: nat_less_induct)
  fix n and S:: "(real^'n) set"
  assume H: "\<forall>m<n. \<forall>S \<subseteq> V. independent S \<longrightarrow> m = CARD('n) - card S \<longrightarrow>
              (\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B)"
    and sv: "S \<subseteq> V" and i: "independent S" and n: "n = CARD('n) - card S"
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
    have mlt: "?d - card (insert a S) < n"
      using aS a n independent_bound[OF th1]
      by auto

    from H[rule_format, OF mlt th0 th1 refl]
    obtain B where B: "insert a S \<subseteq> B" "B \<subseteq> V" "independent B" " V \<subseteq> span B"
      by blast
    from B have "?P B" by auto
    then have ?ths by blast}
  ultimately show ?ths by blast
qed

lemma maximal_independent_subset:
  "\<exists>(B:: (real ^'n::finite) set). B\<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}:: (real ^'n) set"] empty_subsetI independent_empty)

(* Notion of dimension.                                                      *)

definition "dim V = (SOME n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (B hassize n))"

lemma basis_exists:  "\<exists>B. (B :: (real ^'n::finite) set) \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (B hassize dim V)"
unfolding dim_def some_eq_ex[of "\<lambda>n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (B hassize n)"]
unfolding hassize_def
using maximal_independent_subset[of V] independent_bound
by auto

(* Consequences of independence or spanning for cardinality.                 *)

lemma independent_card_le_dim: "(B::(real ^'n::finite) set) \<subseteq> V \<Longrightarrow> independent B \<Longrightarrow> finite B \<and> card B \<le> dim V"
by (metis basis_exists[of V] independent_span_bound[where ?'a=real] hassize_def subset_trans)

lemma span_card_ge_dim:  "(B::(real ^'n::finite) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (metis basis_exists[of V] independent_span_bound hassize_def subset_trans)

lemma basis_card_eq_dim:
  "B \<subseteq> (V:: (real ^'n::finite) set) \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> finite B \<and> card B = dim V"
  by (metis order_eq_iff independent_card_le_dim span_card_ge_dim independent_mono)

lemma dim_unique: "(B::(real ^'n::finite) set) \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> B hassize n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim hassize_def)

(* More lemmas about dimension.                                              *)

lemma dim_univ: "dim (UNIV :: (real^'n::finite) set) = CARD('n)"
  apply (rule dim_unique[of "{basis i |i. i\<in> (UNIV :: 'n set)}"])
  by (auto simp only: span_stdbasis has_size_stdbasis independent_stdbasis)

lemma dim_subset:
  "(S:: (real ^'n::finite) set) \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using basis_exists[of T] basis_exists[of S]
  by (metis independent_span_bound[where ?'a = real and ?'n = 'n] subset_eq hassize_def)

lemma dim_subset_univ: "dim (S:: (real^'n::finite) set) \<le> CARD('n)"
  by (metis dim_subset subset_UNIV dim_univ)

(* Converses to those.                                                       *)

lemma card_ge_dim_independent:
  assumes BV:"(B::(real ^'n::finite) set) \<subseteq> V" and iB:"independent B" and dVB:"dim V \<le> card B"
  shows "V \<subseteq> span B"
proof-
  {fix a assume aV: "a \<in> V"
    {assume aB: "a \<notin> span B"
      then have iaB: "independent (insert a B)" using iB aV  BV by (simp add: independent_insert)
      from aV BV have th0: "insert a B \<subseteq> V" by blast
      from aB have "a \<notin>B" by (auto simp add: span_superset)
      with independent_card_le_dim[OF th0 iaB] dVB  have False by auto}
    then have "a \<in> span B"  by blast}
  then show ?thesis by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "(B:: (real ^'n::finite) set) \<subseteq> V" and VB: "V \<subseteq> span B"
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

lemma card_eq_dim: "(B:: (real ^'n::finite) set) \<subseteq> V \<Longrightarrow> B hassize dim V \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis hassize_def order_eq_iff card_le_dim_spanning
    card_ge_dim_independent)

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

lemma independent_bound_general:
  "independent (S:: (real^'n::finite) set) \<Longrightarrow> finite S \<and> card S \<le> dim S"
  by (metis independent_card_le_dim independent_bound subset_refl)

lemma dependent_biggerset_general: "(finite (S:: (real^'n::finite) set) \<Longrightarrow> card S > dim S) \<Longrightarrow> dependent S"
  using independent_bound_general[of S] by (metis linorder_not_le)

lemma dim_span: "dim (span (S:: (real ^'n::finite) set)) = dim S"
proof-
  have th0: "dim S \<le> dim (span S)"
    by (auto simp add: subset_eq intro: dim_subset span_superset)
  from basis_exists[of S]
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "B hassize dim S" by blast
  from B have fB: "finite B" "card B = dim S" unfolding hassize_def by blast+
  have bSS: "B \<subseteq> span S" using B(1) by (metis subset_eq span_inc)
  have sssB: "span S \<subseteq> span B" using span_mono[OF B(3)] by (simp add: span_span)
  from span_card_ge_dim[OF bSS sssB fB(1)] th0 show ?thesis
    using fB(2)  by arith
qed

lemma subset_le_dim: "(S:: (real ^'n::finite) set) \<subseteq> span T \<Longrightarrow> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma span_eq_dim: "span (S:: (real ^'n::finite) set) = span T ==> dim S = dim T"
  by (metis dim_span)

lemma spans_image:
  assumes lf: "linear (f::'a::semiring_1^'n \<Rightarrow> _)" and VB: "V \<subseteq> span B"
  shows "f ` V \<subseteq> span (f ` B)"
  unfolding span_linear_image[OF lf]
  by (metis VB image_mono)

lemma dim_image_le:
  fixes f :: "real^'n::finite \<Rightarrow> real^'m::finite"
  assumes lf: "linear f" shows "dim (f ` S) \<le> dim (S:: (real ^'n::finite) set)"
proof-
  from basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "B hassize dim S" by blast
  from B have fB: "finite B" "card B = dim S" unfolding hassize_def by blast+
  have "dim (f ` S) \<le> card (f ` B)"
    apply (rule span_card_ge_dim)
    using lf B fB by (auto simp add: span_linear_image spans_image subset_image_iff)
  also have "\<dots> \<le> dim S" using card_image_le[OF fB(1)] fB by simp
  finally show ?thesis .
qed

(* Relation between bases and injectivity/surjectivity of map.               *)

lemma spanning_surjective_image:
  assumes us: "UNIV \<subseteq> span (S:: ('a::semiring_1 ^'n) set)"
  and lf: "linear f" and sf: "surj f"
  shows "UNIV \<subseteq> span (f ` S)"
proof-
  have "UNIV \<subseteq> f ` UNIV" using sf by (auto simp add: surj_def)
  also have " \<dots> \<subseteq> span (f ` S)" using spans_image[OF lf us] .
finally show ?thesis .
qed

lemma independent_injective_image:
  assumes iS: "independent (S::('a::semiring_1^'n) set)" and lf: "linear f" and fi: "inj f"
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

lemma vector_sub_project_orthogonal: "(b::'a::ordered_field^'n::finite) \<bullet> (x - ((b \<bullet> x) / (b\<bullet>b)) *s b) = 0"
  apply (cases "b = 0", simp)
  apply (simp add: dot_rsub dot_rmult)
  unfolding times_divide_eq_right[symmetric]
  by (simp add: field_simps dot_eq_0)

lemma basis_orthogonal:
  fixes B :: "(real ^'n::finite) set"
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
  let ?a = "a - setsum (\<lambda>x. (x\<bullet>a / (x\<bullet>x)) *s x) C"
  let ?C = "insert ?a C"
  from C(1) have fC: "finite ?C" by simp
  from fB aB C(1,2) have cC: "card ?C \<le> card (insert a B)" by (simp add: card_insert_if)
  {fix x k
    have th0: "\<And>(a::'b::comm_ring) b c. a - (b - c) = c + (a - b)" by (simp add: ring_simps)
    have "x - k *s (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x)) *s x)) \<in> span C \<longleftrightarrow> x - k *s a \<in> span C"
      apply (simp only: vector_ssub_ldistrib th0)
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
        unfolding orthogonal_def xa dot_lsub dot_rsub diff_eq_0_iff_eq
        apply simp
        apply (subst Cy)
        using C(1) fth
        apply (simp only: setsum_clauses)
        thm dot_ladd
        apply (auto simp add: dot_ladd dot_radd dot_lmult dot_rmult dot_eq_0 dot_sym[of y a] dot_lsum[OF fth])
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
        unfolding orthogonal_def ya dot_rsub dot_lsub diff_eq_0_iff_eq
        apply simp
        apply (subst Cx)
        using C(1) fth
        apply (simp only: setsum_clauses)
        apply (subst dot_sym[of x])
        apply (auto simp add: dot_radd dot_rmult dot_eq_0 dot_sym[of x a] dot_rsum[OF fth])
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
  fixes V :: "(real ^'n::finite) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (B hassize dim V) \<and> pairwise orthogonal B"
proof-
  from basis_exists[of V] obtain B where B: "B \<subseteq> V" "independent B" "V \<subseteq> span B" "B hassize dim V" by blast
  from B have fB: "finite B" "card B = dim V" by (simp_all add: hassize_def)
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
  ultimately have CdV: "C hassize dim V" unfolding hassize_def using C(1) by simp
  from C B CSV CdV iC show ?thesis by auto
qed

lemma span_eq: "span S = span T \<longleftrightarrow> S \<subseteq> span T \<and> T \<subseteq> span S"
  by (metis set_eq_subset span_mono span_span span_inc) (* FIXME: slow *)

(* ------------------------------------------------------------------------- *)
(* Low-dimensional subset is in a hyperplane (weak orthogonal complement).   *)
(* ------------------------------------------------------------------------- *)

lemma span_not_univ_orthogonal:
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>(a:: real ^'n::finite). a \<noteq>0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
proof-
  from sU obtain a where a: "a \<notin> span S" by blast
  from orthogonal_basis_exists obtain B where
    B: "independent B" "B \<subseteq> span S" "S \<subseteq> span B" "B hassize dim S" "pairwise orthogonal B"
    by blast
  from B have fB: "finite B" "card B = dim S" by (simp_all add: hassize_def)
  from span_mono[OF B(2)] span_mono[OF B(3)]
  have sSB: "span S = span B" by (simp add: span_span)
  let ?a = "a - setsum (\<lambda>b. (a\<bullet>b / (b\<bullet>b)) *s b) B"
  have "setsum (\<lambda>b. (a\<bullet>b / (b\<bullet>b)) *s b) B \<in> span S"
    unfolding sSB
    apply (rule span_setsum[OF fB(1)])
    apply clarsimp
    apply (rule span_mul)
    by (rule span_superset)
  with a have a0:"?a  \<noteq> 0" by auto
  have "\<forall>x\<in>span B. ?a \<bullet> x = 0"
  proof(rule span_induct')
    show "subspace (\<lambda>x. ?a \<bullet> x = 0)"
      by (auto simp add: subspace_def mem_def dot_radd dot_rmult)
  next
    {fix x assume x: "x \<in> B"
      from x have B': "B = insert x (B - {x})" by blast
      have fth: "finite (B - {x})" using fB by simp
      have "?a \<bullet> x = 0"
        apply (subst B') using fB fth
        unfolding setsum_clauses(2)[OF fth]
        apply simp
        apply (clarsimp simp add: dot_lsub dot_ladd dot_lmult dot_lsum dot_eq_0)
        apply (rule setsum_0', rule ballI)
        unfolding dot_sym
        by (auto simp add: x field_simps dot_eq_0 intro: B(5)[unfolded pairwise_def orthogonal_def, rule_format])}
    then show "\<forall>x \<in> B. ?a \<bullet> x = 0" by blast
  qed
  with a0 show ?thesis unfolding sSB by (auto intro: exI[where x="?a"])
qed

lemma span_not_univ_subset_hyperplane:
  assumes SU: "span S \<noteq> (UNIV ::(real^'n::finite) set)"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  using span_not_univ_orthogonal[OF SU] by auto

lemma lowdim_subset_hyperplane:
  assumes d: "dim S < CARD('n::finite)"
  shows "\<exists>(a::real ^'n::finite). a  \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
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
  and fx: "f (x::'a::field^'n) = 0"
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
  obtain k where k: "x - k*s a \<in> span (b -{a})" by blast
  have "f (x - k*s a) \<in> span (f ` b)"
    unfolding span_linear_image[OF lf]
    apply (rule imageI)
    using k span_mono[of "b-{a}" b] by blast
  hence "f x - k*s f a \<in> span (f ` b)"
    by (simp add: linear_sub[OF lf] linear_cmul[OF lf])
  hence th: "-k *s f a \<in> span (f ` b)"
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
  assumes fi: "finite B" and ib: "independent B"
  shows "\<exists>g. (\<forall>x\<in> span B. \<forall>y\<in> span B. g ((x::'a::field^'n) + y) = g x + g y)
           \<and> (\<forall>x\<in> span B. \<forall>c. g (c*s x) = c *s g x)
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
    "\<forall>x\<in>span b. \<forall>c. g (c *s x) = c *s g x" "\<forall>x\<in>b. g x = f x" by blast
  let ?h = "\<lambda>z. SOME k. (z - k *s a) \<in> span b"
  {fix z assume z: "z \<in> span (insert a b)"
    have th0: "z - ?h z *s a \<in> span b"
      apply (rule someI_ex)
      unfolding span_breakdown_eq[symmetric]
      using z .
    {fix k assume k: "z - k *s a \<in> span b"
      have eq: "z - ?h z *s a - (z - k*s a) = (k - ?h z) *s a"
        by (simp add: ring_simps vector_sadd_rdistrib[symmetric])
      from span_sub[OF th0 k]
      have khz: "(k - ?h z) *s a \<in> span b" by (simp add: eq)
      {assume "k \<noteq> ?h z" hence k0: "k - ?h z \<noteq> 0" by simp
        from k0 span_mul[OF khz, of "1 /(k - ?h z)"]
        have "a \<in> span b" by (simp add: vector_smult_assoc)
        with "2.prems"(1) "2.hyps"(2) have False
          by (auto simp add: dependent_def)}
      then have "k = ?h z" by blast}
    with th0 have "z - ?h z *s a \<in> span b \<and> (\<forall>k. z - k *s a \<in> span b \<longrightarrow> k = ?h z)" by blast}
  note h = this
  let ?g = "\<lambda>z. ?h z *s f a + g (z - ?h z *s a)"
  {fix x y assume x: "x \<in> span (insert a b)" and y: "y \<in> span (insert a b)"
    have tha: "\<And>(x::'a^'n) y a k l. (x + y) - (k + l) *s a = (x - k *s a) + (y - l *s a)"
      by (vector ring_simps)
    have addh: "?h (x + y) = ?h x + ?h y"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (rule span_add[OF x y])
      unfolding tha
      by (metis span_add x y conjunct1[OF h, rule_format])
    have "?g (x + y) = ?g x + ?g y"
      unfolding addh tha
      g(1)[rule_format,OF conjunct1[OF h, OF x] conjunct1[OF h, OF y]]
      by (simp add: vector_sadd_rdistrib)}
  moreover
  {fix x:: "'a^'n" and c:: 'a  assume x: "x \<in> span (insert a b)"
    have tha: "\<And>(x::'a^'n) c k a. c *s x - (c * k) *s a = c *s (x - k *s a)"
      by (vector ring_simps)
    have hc: "?h (c *s x) = c * ?h x"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (metis span_mul x)
      by (metis tha span_mul x conjunct1[OF h])
    have "?g (c *s x) = c*s ?g x"
      unfolding hc tha g(2)[rule_format, OF conjunct1[OF h, OF x]]
      by (vector ring_simps)}
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
        apply (metis  span_superset insertI1 xb x)
        apply simp
        apply (metis span_superset xb)
        done
      have "?g x = f x"
        by (simp add: h0[symmetric] g(3)[rule_format, OF xb])}
    ultimately have "?g x = f x" using x by blast }
  ultimately show ?case apply - apply (rule exI[where x="?g"]) by blast
qed

lemma linear_independent_extend:
  assumes iB: "independent (B:: (real ^'n::finite) set)"
  shows "\<exists>g. linear g \<and> (\<forall>x\<in>B. g x = f x)"
proof-
  from maximal_independent_subset_extend[of B UNIV] iB
  obtain C where C: "B \<subseteq> C" "independent C" "\<And>x. x \<in> span C" by auto

  from C(2) independent_bound[of C] linear_independent_extend_lemma[of C f]
  obtain g where g: "(\<forall>x\<in> span C. \<forall>y\<in> span C. g (x + y) = g x + g y)
           \<and> (\<forall>x\<in> span C. \<forall>c. g (c*s x) = c *s g x)
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
  assumes s: "subspace (S:: (real ^'n::finite) set)"
  and t: "subspace (T :: (real ^ 'm::finite) set)"
  and d: "dim S = dim T"
  shows "\<exists>f. linear f \<and> f ` S = T \<and> inj_on f S"
proof-
  from basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "B hassize dim S" by blast
  from basis_exists[of T] obtain C where
    C: "C \<subseteq> T" "independent C" "T \<subseteq> span C" "C hassize dim T" by blast
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" unfolding hassize_def by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear g" "\<forall>x\<in> B. g x = f x" by blast
  from B(4) have fB: "finite B" by (simp add: hassize_def)
  from C(4) have fC: "finite C" by (simp add: hassize_def)
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by (simp add: hassize_def)
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
  assumes lf: "linear (f::'a::semiring_1 ^'n \<Rightarrow> _)"
  shows "subspace {x. f x = 0}"
apply (simp add: subspace_def)
by (simp add: linear_add[OF lf] linear_cmul[OF lf] linear_0[OF lf])

lemma linear_eq_0_span:
  assumes lf: "linear f" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> span B. f x = (0::'a::semiring_1 ^'n)"
proof
  fix x assume x: "x \<in> span B"
  let ?P = "\<lambda>x. f x = 0"
  from subspace_kernel[OF lf] have "subspace ?P" unfolding Collect_def .
  with x f0 span_induct[of B "?P" x] show "f x = 0" by blast
qed

lemma linear_eq_0:
  assumes lf: "linear f" and SB: "S \<subseteq> span B" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> S. f x = (0::'a::semiring_1^'n)"
  by (metis linear_eq_0_span[OF lf] subset_eq SB f0)

lemma linear_eq:
  assumes lf: "linear (f::'a::ring_1^'n \<Rightarrow> _)" and lg: "linear g" and S: "S \<subseteq> span B"
  and fg: "\<forall> x\<in> B. f x = g x"
  shows "\<forall>x\<in> S. f x = g x"
proof-
  let ?h = "\<lambda>x. f x - g x"
  from fg have fg': "\<forall>x\<in> B. ?h x = 0" by simp
  from linear_eq_0[OF linear_compose_sub[OF lf lg] S fg']
  show ?thesis by simp
qed

lemma linear_eq_stdbasis:
  assumes lf: "linear (f::'a::ring_1^'m::finite \<Rightarrow> 'a^'n::finite)" and lg: "linear g"
  and fg: "\<forall>i. f (basis i) = g(basis i)"
  shows "f = g"
proof-
  let ?U = "UNIV :: 'm set"
  let ?I = "{basis i:: 'a^'m|i. i \<in> ?U}"
  {fix x assume x: "x \<in> (UNIV :: ('a^'m) set)"
    from equalityD2[OF span_stdbasis]
    have IU: " (UNIV :: ('a^'m) set) \<subseteq> span ?I" by blast
    from linear_eq[OF lf lg IU] fg x
    have "f x = g x" unfolding Collect_def  Ball_def mem_def by metis}
  then show ?thesis by (auto intro: ext)
qed

(* Similar results for bilinear functions.                                   *)

lemma bilinear_eq:
  assumes bf: "bilinear (f:: 'a::ring^'m \<Rightarrow> 'a^'n \<Rightarrow> 'a^'p)"
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
  assumes bf: "bilinear (f:: 'a::ring_1^'m::finite \<Rightarrow> 'a^'n::finite \<Rightarrow> 'a^'p)"
  and bg: "bilinear g"
  and fg: "\<forall>i j. f (basis i) (basis j) = g (basis i) (basis j)"
  shows "f = g"
proof-
  from fg have th: "\<forall>x \<in> {basis i| i. i\<in> (UNIV :: 'm set)}. \<forall>y\<in>  {basis j |j. j \<in> (UNIV :: 'n set)}. f x y = g x y" by blast
  from bilinear_eq[OF bf bg equalityD2[OF span_stdbasis] equalityD2[OF span_stdbasis] th] show ?thesis by (blast intro: ext)
qed

(* Detailed theorems about left and right invertibility in general case.     *)

lemma left_invertible_transp:
  "(\<exists>(B::'a^'n^'m). B ** transp (A::'a^'n^'m) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B::'a^'m^'n). A ** B = mat 1)"
  by (metis matrix_transp_mul transp_mat transp_transp)

lemma right_invertible_transp:
  "(\<exists>(B::'a^'n^'m). transp (A::'a^'n^'m) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B::'a^'m^'n). B ** A = mat 1)"
  by (metis matrix_transp_mul transp_mat transp_transp)

lemma linear_injective_left_inverse:
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'m::finite)" and fi: "inj f"
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
  assumes lf: "linear (f:: real ^'m::finite \<Rightarrow> real ^'n::finite)" and sf: "surj f"
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
"(\<exists>B. (B::real^'m^'n) ** (A::real^'n::finite^'m::finite) = mat 1) \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
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
  "(\<exists>B. (B::real ^'m::finite^'n::finite) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using linear_injective_0[OF matrix_vector_mul_linear, of A]
  by (simp add: inj_on_def)

lemma matrix_right_invertible_surjective:
"(\<exists>B. (A::real^'n::finite^'m::finite) ** (B::real^'m^'n) = mat 1) \<longleftrightarrow> surj (\<lambda>x. A *v x)"
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
  fixes A :: "real^'n::finite^'m::finite"
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
  fixes A :: "real^'n::finite^'m::finite"
  shows "(\<exists>(B::real^'m^'n). A ** B = mat 1) \<longleftrightarrow> (\<forall>c. setsum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transp[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add: column_transp)

lemma matrix_right_invertible_span_columns:
  "(\<exists>(B::real ^'n::finite^'m::finite). (A::real ^'m^'n) ** B = mat 1) \<longleftrightarrow> span (columns A) = UNIV" (is "?lhs = ?rhs")
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
          apply (rule span_mul)
          apply (rule span_superset)
          unfolding columns_def
          by blast}
    then have ?rhs unfolding rhseq by blast}
  moreover
  {assume h:?rhs
    let ?P = "\<lambda>(y::real ^'n). \<exists>(x::real^'m). setsum (\<lambda>i. (x$i) *s column i A) ?U = y"
    {fix y have "?P y"
      proof(rule span_induct_alt[of ?P "columns A"])
        show "\<exists>x\<Colon>real ^ 'm. setsum (\<lambda>i. (x$i) *s column i A) ?U = 0"
          apply (rule exI[where x=0])
          by (simp add: zero_index vector_smult_lzero)
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
              by (simp add: ring_simps)
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
  "(\<exists>(B::real^'m::finite^'n::finite). B ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> span (rows A) = UNIV"
  unfolding right_invertible_transp[symmetric]
  unfolding columns_transp[symmetric]
  unfolding matrix_right_invertible_span_columns
 ..

(* An injective map real^'n->real^'n is also surjective.                       *)

lemma linear_injective_imp_surjective:
  assumes lf: "linear (f:: real ^'n::finite \<Rightarrow> real ^'n)" and fi: "inj f"
  shows "surj f"
proof-
  let ?U = "UNIV :: (real ^'n) set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "B hassize dim ?U"
    by blast
  from B(4) have d: "dim ?U = card B" by (simp add: hassize_def)
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
  assumes lf: "linear (f::real ^'n::finite => real ^'n)" and sf: "surj f"
  shows "inj f"
proof-
  let ?U = "UNIV :: (real ^'n) set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "B hassize dim ?U"
    by blast
  {fix x assume x: "x \<in> span B" and fx: "f x = 0"
    from B(4) have fB: "finite B" by (simp add: hassize_def)
    from B(4) have d: "dim ?U = card B" by (simp add: hassize_def)
    have fBi: "independent (f ` B)"
      apply (rule card_le_dim_spanning[of "f ` B" ?U])
      apply blast
      using sf B(3)
      unfolding span_linear_image[OF lf] surj_def subset_eq image_iff
      apply blast
      using fB apply (blast intro: finite_imageI)
      unfolding d
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
  assumes lf: "linear (f :: real^'n::finite \<Rightarrow> real ^'n)" and fi: "inj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
unfolding isomorphism_expand[symmetric]
using linear_surjective_right_inverse[OF lf linear_injective_imp_surjective[OF lf fi]] linear_injective_left_inverse[OF lf fi]
by (metis left_right_inverse_eq)

lemma linear_surjective_isomorphism:
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'n)" and sf: "surj f"
  shows "\<exists>f'. linear f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
unfolding isomorphism_expand[symmetric]
using linear_surjective_right_inverse[OF lf sf] linear_injective_left_inverse[OF lf linear_surjective_imp_injective[OF lf sf]]
by (metis left_right_inverse_eq)

(* Left and right inverses are the same for R^N->R^N.                        *)

lemma linear_inverse_left:
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'n)" and lf': "linear f'"
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
  assumes lf: "linear (f::real ^'n::finite \<Rightarrow> real ^'n)" and gf: "g o f = id"
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
  assumes lf: "linear (f:: real ^'n::finite \<Rightarrow> real ^'n)" and gf: "f o g = id"
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
  fixes A A' :: "real ^'n::finite^'n"
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

lemma transp_columnvector:
 "transp(columnvector v) = rowvector v"
  by (simp add: transp_def rowvector_def columnvector_def Cart_eq)

lemma transp_rowvector: "transp(rowvector v) = columnvector v"
  by (simp add: transp_def columnvector_def rowvector_def Cart_eq)

lemma dot_rowvector_columnvector:
  "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product: "(x::'a::semiring_1^'n::finite) \<bullet> y = (((rowvector x ::'a^'n^1) ** (columnvector y :: 'a^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def dot_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n::finite ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transp A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
unfolding dot_matrix_product transp_columnvector[symmetric]
  dot_rowvector_columnvector matrix_transp_mul matrix_mul_assoc ..

(* Infinity norm.                                                            *)

definition "infnorm (x::real^'n::finite) = Sup {abs(x$i) |i. i\<in> (UNIV :: 'n set)}"

lemma numseg_dimindex_nonempty: "\<exists>i. i \<in> (UNIV :: 'n set)"
  by auto

lemma infnorm_set_image:
  "{abs(x$i) |i. i\<in> (UNIV :: 'n set)} =
  (\<lambda>i. abs(x$i)) ` (UNIV :: 'n set)" by blast

lemma infnorm_set_lemma:
  shows "finite {abs((x::'a::abs ^'n::finite)$i) |i. i\<in> (UNIV :: 'n set)}"
  and "{abs(x$i) |i. i\<in> (UNIV :: 'n::finite set)} \<noteq> {}"
  unfolding infnorm_set_image
  by (auto intro: finite_imageI)

lemma infnorm_pos_le: "0 \<le> infnorm (x::real^'n::finite)"
  unfolding infnorm_def
  unfolding Sup_finite_ge_iff[ OF infnorm_set_lemma]
  unfolding infnorm_set_image
  by auto

lemma infnorm_triangle: "infnorm ((x::real^'n::finite) + y) \<le> infnorm x + infnorm y"
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

lemma infnorm_eq_0: "infnorm x = 0 \<longleftrightarrow> (x::real ^'n::finite) = 0"
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
    by (simp_all add: ring_simps infnorm_neg diff_def[symmetric])
  from th[OF ths]  show ?thesis .
qed

lemma real_abs_infnorm: " \<bar>infnorm x\<bar> = infnorm x"
  using infnorm_pos_le[of x] by arith

lemma component_le_infnorm:
  shows "\<bar>x$i\<bar> \<le> infnorm (x::real^'n::finite)"
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
lemma norm_le_infnorm: "norm(x) <= sqrt(real CARD('n)) * infnorm(x::real ^'n::finite)"
proof-
  let ?d = "CARD('n)"
  have "real ?d \<ge> 0" by simp
  hence d2: "(sqrt (real ?d))^2 = real ?d"
    by (auto intro: real_sqrt_pow2)
  have th: "sqrt (real ?d) * infnorm x \<ge> 0"
    by (simp add: zero_le_mult_iff real_sqrt_ge_0_iff infnorm_pos_le)
  have th1: "x\<bullet>x \<le> (sqrt (real ?d) * infnorm x)^2"
    unfolding power_mult_distrib d2
    apply (subst power2_abs[symmetric])
    unfolding real_of_nat_def dot_def power2_eq_square[symmetric]
    apply (subst power2_abs[symmetric])
    apply (rule setsum_bounded)
    apply (rule power_mono)
    unfolding abs_of_nonneg[OF infnorm_pos_le]
    unfolding infnorm_def  Sup_finite_ge_iff[OF infnorm_set_lemma]
    unfolding infnorm_set_image bex_simps
    apply blast
    by (rule abs_ge_zero)
  from real_le_lsqrt[OF dot_pos_le th th1]
  show ?thesis unfolding real_vector_norm_def id_def .
qed

(* Equality in Cauchy-Schwarz and triangle inequalities.                     *)

lemma norm_cauchy_schwarz_eq: "(x::real ^'n::finite) \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *s y = norm y *s x" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume h: "x = 0"
    hence ?thesis by simp}
  moreover
  {assume h: "y = 0"
    hence ?thesis by simp}
  moreover
  {assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    from dot_eq_0[of "norm y *s x - norm x *s y"]
    have "?rhs \<longleftrightarrow> (norm y * (norm y * norm x * norm x - norm x * (x \<bullet> y)) - norm x * (norm y * (y \<bullet> x) - norm x * norm y * norm y) =  0)"
      using x y
      unfolding dot_rsub dot_lsub dot_lmult dot_rmult
      unfolding norm_pow_2[symmetric] power2_eq_square diff_eq_0_iff_eq apply (simp add: dot_sym)
      apply (simp add: ring_simps)
      apply metis
      done
    also have "\<dots> \<longleftrightarrow> (2 * norm x * norm y * (norm x * norm y - x \<bullet> y) = 0)" using x y
      by (simp add: ring_simps dot_sym)
    also have "\<dots> \<longleftrightarrow> ?lhs" using x y
      apply simp
      by metis
    finally have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_abs_eq:
  fixes x y :: "real ^ 'n::finite"
  shows "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow>
                norm x *s y = norm y *s x \<or> norm(x) *s y = - norm y *s x" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have th: "\<And>(x::real) a. a \<ge> 0 \<Longrightarrow> abs x = a \<longleftrightarrow> x = a \<or> x = - a" by arith
  have "?rhs \<longleftrightarrow> norm x *s y = norm y *s x \<or> norm (- x) *s y = norm y *s (- x)"
    apply simp by vector
  also have "\<dots> \<longleftrightarrow>(x \<bullet> y = norm x * norm y \<or>
     (-x) \<bullet> y = norm x * norm y)"
    unfolding norm_cauchy_schwarz_eq[symmetric]
    unfolding norm_minus_cancel
      norm_mul by blast
  also have "\<dots> \<longleftrightarrow> ?lhs"
    unfolding th[OF mult_nonneg_nonneg, OF norm_ge_zero[of x] norm_ge_zero[of y]] dot_lneg
    by arith
  finally show ?thesis ..
qed

lemma norm_triangle_eq:
  fixes x y :: "real ^ 'n::finite"
  shows "norm(x + y) = norm x + norm y \<longleftrightarrow> norm x *s y = norm y *s x"
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
    also have "\<dots> \<longleftrightarrow> norm x *s y = norm y *s x"
      unfolding norm_cauchy_schwarz_eq[symmetric]
      unfolding norm_pow_2 dot_ladd dot_radd
      by (simp add: norm_pow_2[symmetric] power2_eq_square dot_sym ring_simps)
    finally have ?thesis .}
  ultimately show ?thesis by blast
qed

(* Collinearity.*)

definition "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *s u)"

lemma collinear_empty:  "collinear {}" by (simp add: collinear_def)

lemma collinear_sing: "collinear {(x::'a::ring_1^'n)}"
  apply (simp add: collinear_def)
  apply (rule exI[where x=0])
  by simp

lemma collinear_2: "collinear {(x::'a::ring_1^'n),y}"
  apply (simp add: collinear_def)
  apply (rule exI[where x="x - y"])
  apply auto
  apply (rule exI[where x=0], simp)
  apply (rule exI[where x=1], simp)
  apply (rule exI[where x="- 1"], simp add: vector_sneg_minus1[symmetric])
  apply (rule exI[where x=0], simp)
  done

lemma collinear_lemma: "collinear {(0::real^'n),x,y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *s x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  {assume "x=0 \<or> y = 0" hence ?thesis
      by (cases "x = 0", simp_all add: collinear_2 insert_commute)}
  moreover
  {assume x: "x \<noteq> 0" and y: "y \<noteq> 0"
    {assume h: "?lhs"
      then obtain u where u: "\<forall> x\<in> {0,x,y}. \<forall>y\<in> {0,x,y}. \<exists>c. x - y = c *s u" unfolding collinear_def by blast
      from u[rule_format, of x 0] u[rule_format, of y 0]
      obtain cx and cy where
        cx: "x = cx*s u" and cy: "y = cy*s u"
        by auto
      from cx x have cx0: "cx \<noteq> 0" by auto
      from cy y have cy0: "cy \<noteq> 0" by auto
      let ?d = "cy / cx"
      from cx cy cx0 have "y = ?d *s x"
        by (simp add: vector_smult_assoc)
      hence ?rhs using x y by blast}
    moreover
    {assume h: "?rhs"
      then obtain c where c: "y = c*s x" using x y by blast
      have ?lhs unfolding collinear_def c
        apply (rule exI[where x=x])
        apply auto
        apply (rule exI[where x="- 1"], simp only: vector_smult_lneg vector_smult_lid)
        apply (rule exI[where x= "-c"], simp only: vector_smult_lneg)
        apply (rule exI[where x=1], simp)
        apply (rule exI[where x="1 - c"], simp add: vector_smult_lneg vector_sub_rdistrib)
        apply (rule exI[where x="c - 1"], simp add: vector_smult_lneg vector_sub_rdistrib)
        done}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma norm_cauchy_schwarz_equal:
  fixes x y :: "real ^ 'n::finite"
  shows "abs(x \<bullet> y) = norm x * norm y \<longleftrightarrow> collinear {(0::real^'n),x,y}"
unfolding norm_cauchy_schwarz_abs_eq
apply (cases "x=0", simp_all add: collinear_2)
apply (cases "y=0", simp_all add: collinear_2 insert_commute)
unfolding collinear_lemma
apply simp
apply (subgoal_tac "norm x \<noteq> 0")
apply (subgoal_tac "norm y \<noteq> 0")
apply (rule iffI)
apply (cases "norm x *s y = norm y *s x")
apply (rule exI[where x="(1/norm x) * norm y"])
apply (drule sym)
unfolding vector_smult_assoc[symmetric]
apply (simp add: vector_smult_assoc field_simps)
apply (rule exI[where x="(1/norm x) * - norm y"])
apply clarify
apply (drule sym)
unfolding vector_smult_assoc[symmetric]
apply (simp add: vector_smult_assoc field_simps)
apply (erule exE)
apply (erule ssubst)
unfolding vector_smult_assoc
unfolding norm_mul
apply (subgoal_tac "norm x * c = \<bar>c\<bar> * norm x \<or> norm x * c = - \<bar>c\<bar> * norm x")
apply (case_tac "c <= 0", simp add: ring_simps)
apply (simp add: ring_simps)
apply (case_tac "c <= 0", simp add: ring_simps)
apply (simp add: ring_simps)
apply simp
apply simp
done

end

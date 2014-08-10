header {*Instanciates the finite cartesian product of euclidean spaces as a euclidean space.*}

theory Cartesian_Euclidean_Space
imports Finite_Cartesian_Product Integration
begin

lemma delta_mult_idempotent:
  "(if k=a then 1 else (0::'a::semiring_1)) * (if k=a then 1 else 0) = (if k=a then 1 else 0)"
  by (cases "k=a") auto

lemma setsum_UNIV_sum:
  fixes g :: "'a::finite + 'b::finite \<Rightarrow> _"
  shows "(\<Sum>x\<in>UNIV. g x) = (\<Sum>x\<in>UNIV. g (Inl x)) + (\<Sum>x\<in>UNIV. g (Inr x))"
  apply (subst UNIV_Plus_UNIV [symmetric])
  apply (subst setsum.Plus)
  apply simp_all
  done

lemma setsum_mult_product:
  "setsum h {..<A * B :: nat} = (\<Sum>i\<in>{..<A}. \<Sum>j\<in>{..<B}. h (j + i * B))"
  unfolding setsum_nat_group[of h B A, unfolded atLeast0LessThan, symmetric]
proof (rule setsum.cong, simp, rule setsum.reindex_cong)
  fix i
  show "inj_on (\<lambda>j. j + i * B) {..<B}" by (auto intro!: inj_onI)
  show "{i * B..<i * B + B} = (\<lambda>j. j + i * B) ` {..<B}"
  proof safe
    fix j assume "j \<in> {i * B..<i * B + B}"
    then show "j \<in> (\<lambda>j. j + i * B) ` {..<B}"
      by (auto intro!: image_eqI[of _ _ "j - i * B"])
  qed simp
qed simp


subsection{* Basic componentwise operations on vectors. *}

instantiation vec :: (times, finite) times
begin

definition "op * \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) * (y$i)))"
instance ..

end

instantiation vec :: (one, finite) one
begin

definition "1 \<equiv> (\<chi> i. 1)"
instance ..

end

instantiation vec :: (ord, finite) ord
begin

definition "x \<le> y \<longleftrightarrow> (\<forall>i. x$i \<le> y$i)"
definition "x < (y::'a^'b) \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
instance ..

end

text{* The ordering on one-dimensional vectors is linear. *}

class cart_one =
  assumes UNIV_one: "card (UNIV \<Colon> 'a set) = Suc 0"
begin

subclass finite
proof
  from UNIV_one show "finite (UNIV :: 'a set)"
    by (auto intro!: card_ge_0_finite)
qed

end

instance vec:: (order, finite) order
  by default (auto simp: less_eq_vec_def less_vec_def vec_eq_iff
      intro: order.trans order.antisym order.strict_implies_order)

instance vec :: (linorder, cart_one) linorder
proof
  obtain a :: 'b where all: "\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a"
  proof -
    have "card (UNIV :: 'b set) = Suc 0" by (rule UNIV_one)
    then obtain b :: 'b where "UNIV = {b}" by (auto iff: card_Suc_eq)
    then have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P b" by auto
    then show thesis by (auto intro: that)
  qed
  fix x y :: "'a^'b::cart_one"
  note [simp] = less_eq_vec_def less_vec_def all vec_eq_iff field_simps
  show "x \<le> y \<or> y \<le> x" by auto
qed

text{* Constant Vectors *}

definition "vec x = (\<chi> i. x)"

lemma interval_cbox_cart: "{a::real^'n..b} = cbox a b"
  by (auto simp add: less_eq_vec_def mem_box Basis_vec_def inner_axis)

text{* Also the scalar-vector multiplication. *}

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"


subsection {* A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space. *}

lemma setsum_cong_aux:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> setsum f A = setsum g A"
  by (auto intro: setsum.cong)

hide_fact (open) setsum_cong_aux

method_setup vector = {*
let
  val ss1 =
    simpset_of (put_simpset HOL_basic_ss @{context}
      addsimps [@{thm setsum.distrib} RS sym,
      @{thm setsum_subtractf} RS sym, @{thm setsum_right_distrib},
      @{thm setsum_left_distrib}, @{thm setsum_negf} RS sym])
  val ss2 =
    simpset_of (@{context} addsimps
             [@{thm plus_vec_def}, @{thm times_vec_def},
              @{thm minus_vec_def}, @{thm uminus_vec_def},
              @{thm one_vec_def}, @{thm zero_vec_def}, @{thm vec_def},
              @{thm scaleR_vec_def},
              @{thm vec_lambda_beta}, @{thm vector_scalar_mult_def}])
  fun vector_arith_tac ctxt ths =
    simp_tac (put_simpset ss1 ctxt)
    THEN' (fn i => rtac @{thm Cartesian_Euclidean_Space.setsum_cong_aux} i
         ORELSE rtac @{thm setsum.neutral} i
         ORELSE simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm vec_eq_iff}]) i)
    (* THEN' TRY o clarify_tac HOL_cs  THEN' (TRY o rtac @{thm iffI}) *)
    THEN' asm_full_simp_tac (put_simpset ss2 ctxt addsimps ths)
in
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (vector_arith_tac ctxt ths))
end
*} "lift trivial vector statements to real arith statements"

lemma vec_0[simp]: "vec 0 = 0" by vector
lemma vec_1[simp]: "vec 1 = 1" by vector

lemma vec_inj[simp]: "vec x = vec y \<longleftrightarrow> x = y" by vector

lemma vec_in_image_vec: "vec x \<in> (vec ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec_add: "vec(x + y) = vec x + vec y"  by vector
lemma vec_sub: "vec(x - y) = vec x - vec y" by vector
lemma vec_cmul: "vec(c * x) = c *s vec x " by vector
lemma vec_neg: "vec(- x) = - vec x " by vector

lemma vec_setsum:
  assumes "finite S"
  shows "vec(setsum f S) = setsum (vec o f) S"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (auto simp add: vec_add)
qed

text{* Obvious "component-pushing". *}

lemma vec_component [simp]: "vec x $ i = x"
  by vector

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

instance vec :: (semigroup_mult, finite) semigroup_mult
  by default (vector mult.assoc)

instance vec :: (monoid_mult, finite) monoid_mult
  by default vector+

instance vec :: (ab_semigroup_mult, finite) ab_semigroup_mult
  by default (vector mult.commute)

instance vec :: (comm_monoid_mult, finite) comm_monoid_mult
  by default vector

instance vec :: (semiring, finite) semiring
  by default (vector field_simps)+

instance vec :: (semiring_0, finite) semiring_0
  by default (vector field_simps)+
instance vec :: (semiring_1, finite) semiring_1
  by default vector
instance vec :: (comm_semiring, finite) comm_semiring
  by default (vector field_simps)+

instance vec :: (comm_semiring_0, finite) comm_semiring_0 ..
instance vec :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..
instance vec :: (semiring_0_cancel, finite) semiring_0_cancel ..
instance vec :: (comm_semiring_0_cancel, finite) comm_semiring_0_cancel ..
instance vec :: (ring, finite) ring ..
instance vec :: (semiring_1_cancel, finite) semiring_1_cancel ..
instance vec :: (comm_semiring_1, finite) comm_semiring_1 ..

instance vec :: (ring_1, finite) ring_1 ..

instance vec :: (real_algebra, finite) real_algebra
  by default (simp_all add: vec_eq_iff)

instance vec :: (real_algebra_1, finite) real_algebra_1 ..

lemma of_nat_index: "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
proof (induct n)
  case 0
  then show ?case by vector
next
  case Suc
  then show ?case by vector
qed

lemma one_index [simp]: "(1 :: 'a :: one ^ 'n) $ i = 1"
  by vector

lemma neg_one_index [simp]: "(- 1 :: 'a :: {one, uminus} ^ 'n) $ i = - 1"
  by vector

instance vec :: (semiring_char_0, finite) semiring_char_0
proof
  fix m n :: nat
  show "inj (of_nat :: nat \<Rightarrow> 'a ^ 'b)"
    by (auto intro!: injI simp add: vec_eq_iff of_nat_index)
qed

instance vec :: (numeral, finite) numeral ..
instance vec :: (semiring_numeral, finite) semiring_numeral ..

lemma numeral_index [simp]: "numeral w $ i = numeral w"
  by (induct w) (simp_all only: numeral.simps vector_add_component one_index)

lemma neg_numeral_index [simp]: "- numeral w $ i = - numeral w"
  by (simp only: vector_uminus_component numeral_index)

instance vec :: (comm_ring_1, finite) comm_ring_1 ..
instance vec :: (ring_char_0, finite) ring_char_0 ..

lemma vector_smult_assoc: "a *s (b *s x) = ((a::'a::semigroup_mult) * b) *s x"
  by (vector mult.assoc)
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
lemma vector_sneg_minus1: "-x = (-1::'a::ring_1) *s x" by vector
lemma vector_smult_rzero[simp]: "c *s 0 = (0::'a::mult_zero ^ 'n)" by vector
lemma vector_sub_rdistrib: "((a::'a::ring) - b) *s x = a *s x - b *s x"
  by (vector field_simps)

lemma vec_eq[simp]: "(vec m = vec n) \<longleftrightarrow> (m = n)"
  by (simp add: vec_eq_iff)

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

lemma component_le_norm_cart: "\<bar>x$i\<bar> <= norm x"
  apply (simp add: norm_vec_def)
  apply (rule member_le_setL2, simp_all)
  done

lemma norm_bound_component_le_cart: "norm x <= e ==> \<bar>x$i\<bar> <= e"
  by (metis component_le_norm_cart order_trans)

lemma norm_bound_component_lt_cart: "norm x < e ==> \<bar>x$i\<bar> < e"
  by (metis component_le_norm_cart le_less_trans)

lemma norm_le_l1_cart: "norm x <= setsum(\<lambda>i. \<bar>x$i\<bar>) UNIV"
  by (simp add: norm_vec_def setL2_le_setsum)

lemma scalar_mult_eq_scaleR: "c *s x = c *\<^sub>R x"
  unfolding scaleR_vec_def vector_scalar_mult_def by simp

lemma dist_mul[simp]: "dist (c *s x) (c *s y) = \<bar>c\<bar> * dist x y"
  unfolding dist_norm scalar_mult_eq_scaleR
  unfolding scaleR_right_diff_distrib[symmetric] by simp

lemma setsum_component [simp]:
  fixes f:: " 'a \<Rightarrow> ('b::comm_monoid_add) ^'n"
  shows "(setsum f S)$i = setsum (\<lambda>x. (f x)$i) S"
proof (cases "finite S")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma setsum_eq: "setsum f S = (\<chi> i. setsum (\<lambda>x. (f x)$i ) S)"
  by (simp add: vec_eq_iff)

lemma setsum_cmul:
  fixes f:: "'c \<Rightarrow> ('a::semiring_1)^'n"
  shows "setsum (\<lambda>x. c *s f x) S = c *s setsum f S"
  by (simp add: vec_eq_iff setsum_right_distrib)

lemma setsum_norm_allsubsets_bound_cart:
  fixes f:: "'a \<Rightarrow> real ^'n"
  assumes fP: "finite P" and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (setsum f Q) \<le> e"
  shows "setsum (\<lambda>x. norm (f x)) P \<le> 2 * real CARD('n) *  e"
  using setsum_norm_allsubsets_bound[OF assms]
  by simp

subsection {* Matrix operations *}

text{* Matrix notation. NB: an MxN matrix is of type @{typ "'a^'n^'m"}, not @{typ "'a^'m^'n"} *}

definition matrix_matrix_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'p^'n \<Rightarrow> 'a ^ 'p ^'m"
    (infixl "**" 70)
  where "m ** m' == (\<chi> i j. setsum (\<lambda>k. ((m$i)$k) * ((m'$k)$j)) (UNIV :: 'n set)) ::'a ^ 'p ^'m"

definition matrix_vector_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'm"
    (infixl "*v" 70)
  where "m *v x \<equiv> (\<chi> i. setsum (\<lambda>j. ((m$i)$j) * (x$j)) (UNIV ::'n set)) :: 'a^'m"

definition vector_matrix_mult :: "'a ^ 'm \<Rightarrow> ('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n "
    (infixl "v*" 70)
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
  by (vector matrix_matrix_mult_def setsum.distrib[symmetric] field_simps)

lemma matrix_mul_lid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "mat 1 ** A = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  apply (auto simp only: if_distrib cond_application_beta setsum.delta'[OF finite]
    mult_1_left mult_zero_left if_True UNIV_I)
  done


lemma matrix_mul_rid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "A ** mat 1 = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  apply (auto simp only: if_distrib cond_application_beta setsum.delta[OF finite]
    mult_1_right mult_zero_right if_True UNIV_I cong: if_cong)
  done

lemma matrix_mul_assoc: "A ** (B ** C) = (A ** B) ** C"
  apply (vector matrix_matrix_mult_def setsum_right_distrib setsum_left_distrib mult.assoc)
  apply (subst setsum.commute)
  apply simp
  done

lemma matrix_vector_mul_assoc: "A *v (B *v x) = (A ** B) *v x"
  apply (vector matrix_matrix_mult_def matrix_vector_mult_def
    setsum_right_distrib setsum_left_distrib mult.assoc)
  apply (subst setsum.commute)
  apply simp
  done

lemma matrix_vector_mul_lid: "mat 1 *v x = (x::'a::semiring_1 ^ 'n)"
  apply (vector matrix_vector_mult_def mat_def)
  apply (simp add: if_distrib cond_application_beta setsum.delta' cong del: if_weak_cong)
  done

lemma matrix_transpose_mul:
    "transpose(A ** B) = transpose B ** transpose (A::'a::comm_semiring_1^_^_)"
  by (simp add: matrix_matrix_mult_def transpose_def vec_eq_iff mult.commute)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n ^ 'm"
  shows "A = B \<longleftrightarrow>  (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
  apply auto
  apply (subst vec_eq_iff)
  apply clarify
  apply (clarsimp simp add: matrix_vector_mult_def if_distrib cond_application_beta vec_eq_iff cong del: if_weak_cong)
  apply (erule_tac x="axis ia 1" in allE)
  apply (erule_tac x="i" in allE)
  apply (auto simp add: if_distrib cond_application_beta axis_def
    setsum.delta[OF finite] cong del: if_weak_cong)
  done

lemma matrix_vector_mul_component: "((A::real^_^_) *v x)$k = (A$k) \<bullet> x"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma dot_lmul_matrix: "((x::real ^_) v* A) \<bullet> y = x \<bullet> (A *v y)"
  apply (simp add: inner_vec_def matrix_vector_mult_def vector_matrix_mult_def setsum_left_distrib setsum_right_distrib ac_simps)
  apply (subst setsum.commute)
  apply simp
  done

lemma transpose_mat: "transpose (mat n) = mat n"
  by (vector transpose_def mat_def)

lemma transpose_transpose: "transpose(transpose A) = A"
  by (vector transpose_def)

lemma row_transpose:
  fixes A:: "'a::semiring_1^_^_"
  shows "row i (transpose A) = column i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma column_transpose:
  fixes A:: "'a::semiring_1^_^_"
  shows "column i (transpose A) = row i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma rows_transpose: "rows(transpose (A::'a::semiring_1^_^_)) = columns A"
  by (auto simp add: rows_def columns_def row_transpose intro: set_eqI)

lemma columns_transpose: "columns(transpose (A::'a::semiring_1^_^_)) = rows A"
  by (metis transpose_transpose rows_transpose)

text{* Two sometimes fruitful ways of looking at matrix-vector multiplication. *}

lemma matrix_mult_dot: "A *v x = (\<chi> i. A$i \<bullet> x)"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma matrix_mult_vsum:
  "(A::'a::comm_semiring_1^'n^'m) *v x = setsum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def vec_eq_iff column_def mult.commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n) = (\<chi> j. \<Sum>i\<in>UNIV. (x$i) * (axis i 1 :: 'a^'n) $ j)"
  by (simp add: axis_def if_distrib setsum.If_cases vec_eq_iff)

lemma basis_expansion: "setsum (\<lambda>i. (x$i) *s axis i 1) UNIV = (x::('a::ring_1) ^'n)"
  by (auto simp add: axis_def vec_eq_iff if_distrib setsum.If_cases cong del: if_weak_cong)

lemma linear_componentwise:
  fixes f:: "real ^'m \<Rightarrow> real ^ _"
  assumes lf: "linear f"
  shows "(f x)$j = setsum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have "?rhs = (setsum (\<lambda>i.(x$i) *\<^sub>R f (axis i 1) ) ?M)$j"
    unfolding setsum_component by simp
  then show ?thesis
    unfolding linear_setsum_mul[OF lf, symmetric]
    unfolding scalar_mult_eq_scaleR[symmetric]
    unfolding basis_expansion
    by simp
qed

text{* Inverse matrices  (not necessarily square) *}

definition
  "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition
  "matrix_inv(A:: 'a::semiring_1^'n^'m) =
    (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

text{* Correspondence between matrices and linear operators. *}

definition matrix :: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
  where "matrix f = (\<chi> i j. (f(axis j 1))$i)"

lemma matrix_vector_mul_linear: "linear(\<lambda>x. A *v (x::real ^ _))"
  by (simp add: linear_iff matrix_vector_mult_def vec_eq_iff
      field_simps setsum_right_distrib setsum.distrib)

lemma matrix_works:
  assumes lf: "linear f"
  shows "matrix f *v x = f (x::real ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  apply clarify
  apply (rule linear_componentwise[OF lf, symmetric])
  done

lemma matrix_vector_mul: "linear f ==> f = (\<lambda>x. matrix f *v (x::real ^ 'n))"
  by (simp add: ext matrix_works)

lemma matrix_of_matrix_vector_mul: "matrix(\<lambda>x. A *v (x :: real ^ 'n)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)

lemma matrix_compose:
  assumes lf: "linear (f::real^'n \<Rightarrow> real^'m)"
    and lg: "linear (g::real^'m \<Rightarrow> real^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_vector_column:
  "(A::'a::comm_semiring_1^'n^_) *v x = setsum (\<lambda>i. (x$i) *s ((transpose A)$i)) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def transpose_def vec_eq_iff mult.commute)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique)
  apply (simp add: transpose_def inner_vec_def matrix_vector_mult_def
    setsum_left_distrib setsum_right_distrib)
  apply (subst setsum.commute)
  apply (auto simp add: ac_simps)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
  apply (subst matrix_vector_mul[OF lf])
  unfolding adjoint_matrix matrix_of_matrix_vector_mul
  apply rule
  done


subsection {* lambda skolemization on cartesian products *}

(* FIXME: rename do choice_cart *)

lemma lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x $ i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?S = "(UNIV :: 'n set)"
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f where f:"\<forall>i. P i (f i)" unfolding choice_iff by metis
    let ?x = "(\<chi> i. (f i)) :: 'a ^ 'n"
    { fix i
      from f have "P i (f i)" by metis
      then have "P i (?x $ i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed

lemma vector_sub_project_orthogonal_cart: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps scalar_mult_eq_scaleR by auto

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma matrix_left_invertible_injective:
  "(\<exists>B. (B::real^'m^'n) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
proof -
  { fix B:: "real^'m^'n" and x y assume B: "B ** A = mat 1" and xy: "A *v x = A*v y"
    from xy have "B*v (A *v x) = B *v (A*v y)" by simp
    hence "x = y"
      unfolding matrix_vector_mul_assoc B matrix_vector_mul_lid . }
  moreover
  { assume A: "\<forall>x y. A *v x = A *v y \<longrightarrow> x = y"
    hence i: "inj (op *v A)" unfolding inj_on_def by auto
    from linear_injective_left_inverse[OF matrix_vector_mul_linear i]
    obtain g where g: "linear g" "g o op *v A = id" by blast
    have "matrix g ** A = mat 1"
      unfolding matrix_eq matrix_vector_mul_lid matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) by (simp add: fun_eq_iff)
    then have "\<exists>B. (B::real ^'m^'n) ** A = mat 1" by blast }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::real ^'m^'n) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using linear_injective_0[OF matrix_vector_mul_linear, of A]
  by (simp add: inj_on_def)

lemma matrix_right_invertible_surjective:
  "(\<exists>B. (A::real^'n^'m) ** (B::real^'m^'n) = mat 1) \<longleftrightarrow> surj (\<lambda>x. A *v x)"
proof -
  { fix B :: "real ^'m^'n"
    assume AB: "A ** B = mat 1"
    { fix x :: "real ^ 'm"
      have "A *v (B *v x) = x"
        by (simp add: matrix_vector_mul_lid matrix_vector_mul_assoc AB) }
    hence "surj (op *v A)" unfolding surj_def by metis }
  moreover
  { assume sf: "surj (op *v A)"
    from linear_surjective_right_inverse[OF matrix_vector_mul_linear sf]
    obtain g:: "real ^'m \<Rightarrow> real ^'n" where g: "linear g" "op *v A o g = id"
      by blast

    have "A ** (matrix g) = mat 1"
      unfolding matrix_eq  matrix_vector_mul_lid
        matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) unfolding o_def fun_eq_iff id_def
      .
    hence "\<exists>B. A ** (B::real^'m^'n) = mat 1" by blast
  }
  ultimately show ?thesis unfolding surj_def by blast
qed

lemma matrix_left_invertible_independent_columns:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real ^'m^'n). B ** A = mat 1) \<longleftrightarrow>
      (\<forall>c. setsum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  { assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    { fix c i
      assume c: "setsum (\<lambda>i. c i *s column i A) ?U = 0" and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        unfolding matrix_mult_vsum vec_eq_iff
        by auto
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
    hence ?rhs by blast }
  moreover
  { assume H: ?rhs
    { fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: real)"
      from H[rule_format, of ?c, unfolded matrix_mult_vsum[symmetric], OF x]
      have "x = 0" by vector }
  }
  ultimately show ?thesis unfolding matrix_left_invertible_ker by blast
qed

lemma matrix_right_invertible_independent_rows:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. setsum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add: column_transpose)

lemma matrix_right_invertible_span_columns:
  "(\<exists>(B::real ^'n^'m). (A::real ^'m^'n) ** B = mat 1) \<longleftrightarrow>
    span (columns A) = UNIV" (is "?lhs = ?rhs")
proof -
  let ?U = "UNIV :: 'm set"
  have fU: "finite ?U" by simp
  have lhseq: "?lhs \<longleftrightarrow> (\<forall>y. \<exists>(x::real^'m). setsum (\<lambda>i. (x$i) *s column i A) ?U = y)"
    unfolding matrix_right_invertible_surjective matrix_mult_vsum surj_def
    apply (subst eq_commute)
    apply rule
    done
  have rhseq: "?rhs \<longleftrightarrow> (\<forall>x. x \<in> span (columns A))" by blast
  { assume h: ?lhs
    { fix x:: "real ^'n"
      from h[unfolded lhseq, rule_format, of x] obtain y :: "real ^'m"
        where y: "setsum (\<lambda>i. (y$i) *s column i A) ?U = x" by blast
      have "x \<in> span (columns A)"
        unfolding y[symmetric]
        apply (rule span_setsum)
        apply clarify
        unfolding scalar_mult_eq_scaleR
        apply (rule span_mul)
        apply (rule span_superset)
        unfolding columns_def
        apply blast
        done
    }
    then have ?rhs unfolding rhseq by blast }
  moreover
  { assume h:?rhs
    let ?P = "\<lambda>(y::real ^'n). \<exists>(x::real^'m). setsum (\<lambda>i. (x$i) *s column i A) ?U = y"
    { fix y
      have "?P y"
      proof (rule span_induct_alt[of ?P "columns A", folded scalar_mult_eq_scaleR])
        show "\<exists>x\<Colon>real ^ 'm. setsum (\<lambda>i. (x$i) *s column i A) ?U = 0"
          by (rule exI[where x=0], simp)
      next
        fix c y1 y2
        assume y1: "y1 \<in> columns A" and y2: "?P y2"
        from y1 obtain i where i: "i \<in> ?U" "y1 = column i A"
          unfolding columns_def by blast
        from y2 obtain x:: "real ^'m" where
          x: "setsum (\<lambda>i. (x$i) *s column i A) ?U = y2" by blast
        let ?x = "(\<chi> j. if j = i then c + (x$i) else (x$j))::real^'m"
        show "?P (c*s y1 + y2)"
        proof (rule exI[where x= "?x"], vector, auto simp add: i x[symmetric] if_distrib distrib_left cond_application_beta cong del: if_weak_cong)
          fix j
          have th: "\<forall>xa \<in> ?U. (if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) = (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))"
            using i(1) by (simp add: field_simps)
          have "setsum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) ?U = setsum (\<lambda>xa. (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))) ?U"
            apply (rule setsum.cong[OF refl])
            using th apply blast
            done
          also have "\<dots> = setsum (\<lambda>xa. if xa = i then c * ((column i A)$j) else 0) ?U + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            by (simp add: setsum.distrib)
          also have "\<dots> = c * ((column i A)$j) + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            unfolding setsum.delta[OF fU]
            using i(1) by simp
          finally show "setsum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
            else (x$xa) * ((column xa A$j))) ?U = c * ((column i A)$j) + setsum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U" .
        qed
      next
        show "y \<in> span (columns A)"
          unfolding h by blast
      qed
    }
    then have ?lhs unfolding lhseq ..
  }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_span_rows:
  "(\<exists>(B::real^'m^'n). B ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> span (rows A) = UNIV"
  unfolding right_invertible_transpose[symmetric]
  unfolding columns_transpose[symmetric]
  unfolding matrix_right_invertible_span_columns
  ..

text {* The same result in terms of square matrices. *}

lemma matrix_left_right_inverse:
  fixes A A' :: "real ^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "real ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj (op *v A)"
      unfolding surj_def
      apply clarify
      apply (rule_tac x="(A' *v y)" in exI)
      apply (simp add: matrix_vector_mul_assoc AA' matrix_vector_mul_lid)
      done
    from linear_surjective_isomorphism[OF matrix_vector_mul_linear sA]
    obtain f' :: "real ^'n \<Rightarrow> real ^'n"
      where f': "linear f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)]
          matrix_vector_mul_assoc[symmetric] matrix_vector_mul_lid f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'"
      by (simp add: matrix_mul_assoc[symmetric] AA' matrix_mul_rid matrix_mul_lid)
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)
  }
  then show ?thesis by blast
qed

text {* Considering an n-element vector as an n-by-1 or 1-by-n matrix. *}

definition "rowvector v = (\<chi> i j. (v$j))"

definition "columnvector v = (\<chi> i j. (v$i))"

lemma transpose_columnvector: "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def vec_eq_iff)

lemma transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def vec_eq_iff)

lemma dot_rowvector_columnvector: "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product:
  "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vec_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
  unfolding dot_matrix_product transpose_columnvector[symmetric]
    dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..


lemma infnorm_cart:"infnorm (x::real^'n) = Sup {abs(x$i) |i. i\<in>UNIV}"
  by (simp add: infnorm_def inner_axis Basis_vec_def) (metis (lifting) inner_axis real_inner_1_right)

lemma component_le_infnorm_cart: "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
  using Basis_le_infnorm[of "axis i 1" x]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis)

lemma continuous_component: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x $ i)"
  unfolding continuous_def by (rule tendsto_vec_nth)

lemma continuous_on_component: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x $ i)"
  unfolding continuous_on_def by (fast intro: tendsto_vec_nth)

lemma closed_positive_orthant: "closed {x::real^'n. \<forall>i. 0 \<le>x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le)

lemma bounded_component_cart: "bounded s \<Longrightarrow> bounded ((\<lambda>x. x $ i) ` s)"
  unfolding bounded_def
  apply clarify
  apply (rule_tac x="x $ i" in exI)
  apply (rule_tac x="e" in exI)
  apply clarify
  apply (rule order_trans [OF dist_vec_nth_le], simp)
  done

lemma compact_lemma_cart:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel ^ 'n"
  assumes f: "bounded (range f)"
  shows "\<forall>d.
        \<exists>l r. subseq r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
proof
  fix d :: "'n set"
  have "finite d" by simp
  thus "\<exists>l::'a ^ 'n. \<exists>r. subseq r \<and>
      (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
  proof (induct d)
    case empty
    thus ?case unfolding subseq_def by auto
  next
    case (insert k d)
    obtain l1::"'a^'n" and r1 where r1:"subseq r1"
      and lr1:"\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially"
      using insert(3) by auto
    have s': "bounded ((\<lambda>x. x $ k) ` range f)" using `bounded (range f)`
      by (auto intro!: bounded_component_cart)
    have f': "\<forall>n. f (r1 n) $ k \<in> (\<lambda>x. x $ k) ` range f" by simp
    have "bounded (range (\<lambda>i. f (r1 i) $ k))"
      by (metis (lifting) bounded_subset image_subsetI f' s')
    then obtain l2 r2 where r2: "subseq r2"
      and lr2: "((\<lambda>i. f (r1 (r2 i)) $ k) ---> l2) sequentially"
      using bounded_imp_convergent_subsequence[of "\<lambda>i. f (r1 i) $ k"] by (auto simp: o_def)
    def r \<equiv> "r1 \<circ> r2"
    have r: "subseq r"
      using r1 and r2 unfolding r_def o_def subseq_def by auto
    moreover
    def l \<equiv> "(\<chi> i. if i = k then l2 else l1$i)::'a^'n"
    { fix e :: real assume "e > 0"
      from lr1 `e>0` have N1:"eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially"
        by blast
      from lr2 `e>0` have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) $ k) l2 < e) sequentially"
        by (rule tendstoD)
      from r2 N1 have N1': "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 (r2 n)) $ i) (l1 $ i) < e) sequentially"
        by (rule eventually_subseq)
      have "eventually (\<lambda>n. \<forall>i\<in>(insert k d). dist (f (r n) $ i) (l $ i) < e) sequentially"
        using N1' N2 by (rule eventually_elim2, simp add: l_def r_def)
    }
    ultimately show ?case by auto
  qed
qed

instance vec :: (heine_borel, finite) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a ^ 'b"
  assume f: "bounded (range f)"
  then obtain l r where r: "subseq r"
      and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma_cart [OF f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n
      assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vec_def using zero_le_dist by (rule setL2_le_setsum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule setsum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_elim1)
  }
  hence "((f \<circ> r) ---> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially" by auto
qed

lemma interval_cart:
  fixes a :: "real^'n"
  shows "box a b = {x::real^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}"
    and "cbox a b = {x::real^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma mem_interval_cart:
  fixes a :: "real^'n"
  shows "x \<in> box a b \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
    and "x \<in> cbox a b \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval_cart[of a b] by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma interval_eq_empty_cart:
  fixes a :: "real^'n"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof -
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>box a b"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_interval_cart by auto
    hence "a$i < b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "box a b \<noteq> {}" using mem_interval_cart(1)[of "?x" a b] by auto }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>cbox a b"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_interval_cart by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "cbox a b \<noteq> {}" using mem_interval_cart(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)"
    and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty_cart[of a b] by (auto simp add: not_less not_le)
    (* BH: Why doesn't just "auto" work here? *)

lemma subset_interval_imp_cart:
  fixes a :: "real^'n"
  shows "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_interval_cart
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma interval_sing:
  fixes a :: "'a::linorder^'n"
  shows "{a .. a} = {a} \<and> {a<..<a} = {}"
  apply (auto simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  done

lemma subset_interval_cart:
  fixes a :: "real^'n"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
  using subset_box[of c d a b] by (simp_all add: Basis_vec_def inner_axis)

lemma disjoint_interval_cart:
  fixes a::"real^'n"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
  using disjoint_interval[of a b c d] by (simp_all add: Basis_vec_def inner_axis)

lemma inter_interval_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<inter> cbox c d =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding inter_interval
  by (auto simp: mem_box less_eq_vec_def)
    (auto simp: Basis_vec_def inner_axis)

lemma closed_interval_left_cart:
  fixes b :: "real^'n"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le)

lemma closed_interval_right_cart:
  fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le)

lemma is_interval_cart:
  "is_interval (s::(real^'n) set) \<longleftrightarrow>
    (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i))) \<longrightarrow> x \<in> s)"
  by (simp add: is_interval_def Ball_def Basis_vec_def inner_axis imp_ex)

lemma closed_halfspace_component_le_cart: "closed {x::real^'n. x$i \<le> a}"
  by (simp add: closed_Collect_le)

lemma closed_halfspace_component_ge_cart: "closed {x::real^'n. x$i \<ge> a}"
  by (simp add: closed_Collect_le)

lemma open_halfspace_component_lt_cart: "open {x::real^'n. x$i < a}"
  by (simp add: open_Collect_less)

lemma open_halfspace_component_gt_cart: "open {x::real^'n. x$i  > a}"
  by (simp add: open_Collect_less)

lemma Lim_component_le_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f x $i \<le> b) net"
  shows "l$i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_vec_nth, OF assms(1, 3)])

lemma Lim_component_ge_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
  by (rule tendsto_le[OF assms(2) tendsto_vec_nth tendsto_const, OF assms(1, 3)])

lemma Lim_component_eq_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes net: "(f ---> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff] and
    Lim_component_ge_cart[OF net, of b i] and
    Lim_component_le_cart[OF net, of i b] by auto

lemma connected_ivt_component_cart:
  fixes x :: "real^'n"
  shows "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "axis k 1" a]
  by (auto simp add: inner_axis inner_commute)

lemma subspace_substandard_cart: "subspace {x::real^_. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding subspace_def by auto

lemma closed_substandard_cart:
  "closed {x::'a::real_normed_vector ^ 'n. \<forall>i. P i \<longrightarrow> x$i = 0}"
proof -
  { fix i::'n
    have "closed {x::'a ^ 'n. P i \<longrightarrow> x$i = 0}"
      by (cases "P i") (simp_all add: closed_Collect_eq) }
  thus ?thesis
    unfolding Collect_all_eq by (simp add: closed_INT)
qed

lemma dim_substandard_cart: "dim {x::real^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d"
  (is "dim ?A = _")
proof -
  let ?a = "\<lambda>x. axis x 1 :: real^'n"
  have *: "{x. \<forall>i\<in>Basis. i \<notin> ?a ` d \<longrightarrow> x \<bullet> i = 0} = ?A"
    by (auto simp: image_iff Basis_vec_def axis_eq_axis inner_axis)
  have "?a ` d \<subseteq> Basis"
    by (auto simp: Basis_vec_def)
  thus ?thesis
    using dim_substandard[of "?a ` d"] card_image[of ?a d]
    by (auto simp: axis_eq_axis inj_on_def *)
qed

lemma affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) o (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) o (\<lambda>x. m *s x + c) = id"
  using m0
  apply (auto simp add: fun_eq_iff vector_add_ldistrib diff_conv_add_uminus simp del: add_uminus_conv_diff)
  apply (simp_all add: vector_smult_lneg[symmetric] vector_smult_assoc vector_sneg_minus1 [symmetric])
  done

lemma vector_affinity_eq:
  assumes m0: "(m::'a::field) \<noteq> 0"
  shows "m *s x + c = y \<longleftrightarrow> x = inverse m *s y + -(inverse m *s c)"
proof
  assume h: "m *s x + c = y"
  hence "m *s x = y - c" by (simp add: field_simps)
  hence "inverse m *s (m *s x) = inverse m *s (y - c)" by simp
  then show "x = inverse m *s y + - (inverse m *s c)"
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
next
  assume h: "x = inverse m *s y + - (inverse m *s c)"
  show "m *s x + c = y" unfolding h
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma vector_eq_affinity:
    "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma vector_cart:
  fixes f :: "real^'n \<Rightarrow> real"
  shows "(\<chi> i. f (axis i 1)) = (\<Sum>i\<in>Basis. f i *\<^sub>R i)"
  unfolding euclidean_eq_iff[where 'a="real^'n"]
  by simp (simp add: Basis_vec_def inner_axis)
  
lemma const_vector_cart:"((\<chi> i. d)::real^'n) = (\<Sum>i\<in>Basis. d *\<^sub>R i)"
  by (rule vector_cart)

subsection "Convex Euclidean Space"

lemma Cart_1:"(1::real^'n) = \<Sum>Basis"
  using const_vector_cart[of 1] by (simp add: one_vec_def)

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]

lemmas vector_component_simps = vector_minus_component vector_smult_component vector_add_component less_eq_vec_def vec_lambda_beta vector_uminus_component

lemma convex_box_cart:
  assumes "\<And>i. convex {x. P i x}"
  shows "convex {x. \<forall>i. P i (x$i)}"
  using assms unfolding convex_def by auto

lemma convex_positive_orthant_cart: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  by (rule convex_box_cart) (simp add: atLeast_def[symmetric] convex_real_interval)

lemma unit_interval_convex_hull_cart:
  "cbox (0::real^'n) 1 = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}"
  unfolding Cart_1 unit_interval_convex_hull[where 'a="real^'n"] box_real[symmetric]
  by (rule arg_cong[where f="\<lambda>x. convex hull x"]) (simp add: Basis_vec_def inner_axis)

lemma cube_convex_hull_cart:
  assumes "0 < d"
  obtains s::"(real^'n) set"
    where "finite s" "cbox (x - (\<chi> i. d)) (x + (\<chi> i. d)) = convex hull s"
proof -
  from assms obtain s where "finite s"
    and "cbox (x - setsum (op *\<^sub>R d) Basis) (x + setsum (op *\<^sub>R d) Basis) = convex hull s"
    by (rule cube_convex_hull)
  with that[of s] show thesis
    by (simp add: const_vector_cart)
qed


subsection "Derivative"

lemma differentiable_at_imp_differentiable_on:
  "(\<forall>x\<in>(s::(real^'n) set). f differentiable at x) \<Longrightarrow> f differentiable_on s"
  by (metis differentiable_at_withinI differentiable_on_def)

definition "jacobian f net = matrix(frechet_derivative f net)"

lemma jacobian_works:
  "(f::(real^'a) \<Rightarrow> (real^'b)) differentiable net \<longleftrightarrow>
    (f has_derivative (\<lambda>h. (jacobian f net) *v h)) net"
  apply rule
  unfolding jacobian_def
  apply (simp only: matrix_works[OF linear_frechet_derivative]) defer
  apply (rule differentiableI)
  apply assumption
  unfolding frechet_derivative_works
  apply assumption
  done


subsection {* Component of the differential must be zero if it exists at a local
  maximum or minimum for that corresponding component. *}

lemma differential_zero_maxmin_cart:
  fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "0 < e" "((\<forall>y \<in> ball x e. (f y)$k \<le> (f x)$k) \<or> (\<forall>y\<in>ball x e. (f x)$k \<le> (f y)$k))"
    "f differentiable (at x)"
  shows "jacobian f (at x) $ k = 0"
  using differential_zero_maxmin_component[of "axis k 1" e x f] assms
    vector_cart[of "\<lambda>j. frechet_derivative f (at x) j $ k"]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis jacobian_def matrix_def)

subsection {* Lemmas for working on @{typ "real^1"} *}

lemma forall_1[simp]: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis (full_types) num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis (full_types) num1_eq_iff)

lemma exhaust_2:
  fixes x :: 2
  shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3
  shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma UNIV_1 [simp]: "UNIV = {1::1}"
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
  unfolding UNIV_3 by (simp add: ac_simps)

instantiation num1 :: cart_one
begin

instance
proof
  show "CARD(1) = Suc 0" by auto
qed

end

subsection{* The collapse of the general concepts to dimension one. *}

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: vec_eq_iff)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vec_def)

lemma norm_real: "norm(x::real ^ 1) = abs(x$1)"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = abs((x$1) - (y$1))"
  by (auto simp add: norm_real dist_norm)


subsection{* Explicit vector construction from lists. *}

definition "vector l = (\<chi> i. foldr (\<lambda>x f n. fun_upd (f (n+1)) n x) l (\<lambda>n x. 0) 1 i)"

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
  apply simp
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

lemma bounded_linear_component_cart[intro]: "bounded_linear (\<lambda>x::real^'n. x $ k)"
  apply (rule bounded_linearI[where K=1])
  using component_le_norm_cart[of _ k] unfolding real_norm_def by auto

lemma integral_component_eq_cart[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> real^'m"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x $ k) = integral s f $ k"
  using integral_linear[OF assms(1) bounded_linear_component_cart,unfolded o_def] .

lemma interval_split_cart:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "cbox a b \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  apply (rule_tac[!] set_eqI)
  unfolding Int_iff mem_interval_cart mem_Collect_eq interval_cbox_cart
  unfolding vec_lambda_beta
  by auto

end

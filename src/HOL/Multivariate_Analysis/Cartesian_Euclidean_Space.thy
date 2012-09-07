
header {*Instanciates the finite cartesian product of euclidean spaces as a euclidean space.*}

theory Cartesian_Euclidean_Space
imports Finite_Cartesian_Product Integration
begin

lemma delta_mult_idempotent:
  "(if k=a then 1 else (0::'a::semiring_1)) * (if k=a then 1 else 0) = (if k=a then 1 else 0)" by (cases "k=a", auto)

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

lemma setsum_mult_product:
  "setsum h {..<A * B :: nat} = (\<Sum>i\<in>{..<A}. \<Sum>j\<in>{..<B}. h (j + i * B))"
  unfolding sumr_group[of h B A, unfolded atLeast0LessThan, symmetric]
proof (rule setsum_cong, simp, rule setsum_reindex_cong)
  fix i show "inj_on (\<lambda>j. j + i * B) {..<B}" by (auto intro!: inj_onI)
  show "{i * B..<i * B + B} = (\<lambda>j. j + i * B) ` {..<B}"
  proof safe
    fix j assume "j \<in> {i * B..<i * B + B}"
    thus "j \<in> (\<lambda>j. j + i * B) ` {..<B}"
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
  definition "x < y \<longleftrightarrow> (\<forall>i. x$i < y$i)"
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

instantiation vec :: (linorder, cart_one) linorder
begin

instance
proof
  obtain a :: 'b where all: "\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a"
  proof -
    have "card (UNIV :: 'b set) = Suc 0" by (rule UNIV_one)
    then obtain b :: 'b where "UNIV = {b}" by (auto iff: card_Suc_eq)
    then have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P b" by auto
    then show thesis by (auto intro: that)
  qed

  note [simp] = less_eq_vec_def less_vec_def all vec_eq_iff field_simps
  fix x y z :: "'a^'b::cart_one"
  show "x \<le> x" "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" "x \<le> y \<or> y \<le> x" by auto
  { assume "x\<le>y" "y\<le>z" then show "x\<le>z" by auto }
  { assume "x\<le>y" "y\<le>x" then show "x=y" by auto }
qed

end

text{* Constant Vectors *} 

definition "vec x = (\<chi> i. x)"

text{* Also the scalar-vector multiplication. *}

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"

subsection {* A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space. *}

method_setup vector = {*
let
  val ss1 = HOL_basic_ss addsimps [@{thm setsum_addf} RS sym,
  @{thm setsum_subtractf} RS sym, @{thm setsum_right_distrib},
  @{thm setsum_left_distrib}, @{thm setsum_negf} RS sym]
  val ss2 = @{simpset} addsimps
             [@{thm plus_vec_def}, @{thm times_vec_def},
              @{thm minus_vec_def}, @{thm uminus_vec_def},
              @{thm one_vec_def}, @{thm zero_vec_def}, @{thm vec_def},
              @{thm scaleR_vec_def},
              @{thm vec_lambda_beta}, @{thm vector_scalar_mult_def}]
 fun vector_arith_tac ths =
   simp_tac ss1
   THEN' (fn i => rtac @{thm setsum_cong2} i
         ORELSE rtac @{thm setsum_0'} i
         ORELSE simp_tac (HOL_basic_ss addsimps [@{thm vec_eq_iff}]) i)
   (* THEN' TRY o clarify_tac HOL_cs  THEN' (TRY o rtac @{thm iffI}) *)
   THEN' asm_full_simp_tac (ss2 addsimps ths)
 in
  Attrib.thms >> (fn ths => K (SIMPLE_METHOD' (vector_arith_tac ths)))
 end
*} "lift trivial vector statements to real arith statements"

lemma vec_0[simp]: "vec 0 = 0" by (vector zero_vec_def)
lemma vec_1[simp]: "vec 1 = 1" by (vector one_vec_def)

lemma vec_inj[simp]: "vec x = vec y \<longleftrightarrow> x = y" by vector

lemma vec_in_image_vec: "vec x \<in> (vec ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec_add: "vec(x + y) = vec x + vec y"  by (vector vec_def)
lemma vec_sub: "vec(x - y) = vec x - vec y" by (vector vec_def)
lemma vec_cmul: "vec(c * x) = c *s vec x " by (vector vec_def)
lemma vec_neg: "vec(- x) = - vec x " by (vector vec_def)

lemma vec_setsum: assumes fS: "finite S"
  shows "vec(setsum f S) = setsum (vec o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply (simp)
  apply (auto simp add: vec_add)
  done

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

instance vec :: (semigroup_mult, finite) semigroup_mult
  by default (vector mult_assoc)

instance vec :: (monoid_mult, finite) monoid_mult
  by default vector+

instance vec :: (ab_semigroup_mult, finite) ab_semigroup_mult
  by default (vector mult_commute)

instance vec :: (ab_semigroup_idem_mult, finite) ab_semigroup_idem_mult
  by default (vector mult_idem)

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
  apply intro_classes
  apply (simp_all add: vec_eq_iff)
  done

instance vec :: (real_algebra_1, finite) real_algebra_1 ..

lemma of_nat_index:
  "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
  apply (induct n)
  apply vector
  apply vector
  done

lemma one_index[simp]:
  "(1 :: 'a::one ^'n)$i = 1" by vector

instance vec :: (semiring_char_0, finite) semiring_char_0
proof
  fix m n :: nat
  show "inj (of_nat :: nat \<Rightarrow> 'a ^ 'b)"
    by (auto intro!: injI simp add: vec_eq_iff of_nat_index)
qed

instance vec :: (numeral, finite) numeral ..
instance vec :: (semiring_numeral, finite) semiring_numeral ..

lemma numeral_index [simp]: "numeral w $ i = numeral w"
  by (induct w, simp_all only: numeral.simps vector_add_component one_index)

lemma neg_numeral_index [simp]: "neg_numeral w $ i = neg_numeral w"
  by (simp only: neg_numeral_def vector_uminus_component numeral_index)

instance vec :: (comm_ring_1, finite) comm_ring_1 ..
instance vec :: (ring_char_0, finite) ring_char_0 ..

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
  by (metis component_le_norm_cart basic_trans_rules(21))

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
  by (cases "finite S", induct S set: finite, simp_all)

lemma setsum_eq: "setsum f S = (\<chi> i. setsum (\<lambda>x. (f x)$i ) S)"
  by (simp add: vec_eq_iff)

lemma setsum_cmul:
  fixes f:: "'c \<Rightarrow> ('a::semiring_1)^'n"
  shows "setsum (\<lambda>x. c *s f x) S = c *s setsum f S"
  by (simp add: vec_eq_iff setsum_right_distrib)

(* TODO: use setsum_norm_allsubsets_bound *)
lemma setsum_norm_allsubsets_bound_cart:
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
    apply (rule setsum_mono)    by (rule norm_le_l1_cart)
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
      using component_le_norm_cart[of "setsum (\<lambda>x. f x) ?Pp" i]  fPs[OF PpP]
      by (auto intro: abs_le_D1)
    have Pne: "setsum (\<lambda>x. \<bar>f x $ i\<bar>) ?Pn \<le> e"
      using component_le_norm_cart[of "setsum (\<lambda>x. - f x) ?Pn" i]  fPs[OF PnP]
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

lemma if_distr: "(if P then f else g) $ i = (if P then f $ i else g $ i)" by simp

lemma split_dimensions'[consumes 1]:
  assumes "k < DIM('a::euclidean_space^'b)"
  obtains i j where "i < CARD('b::finite)" and "j < DIM('a::euclidean_space)" and "k = j + i * DIM('a::euclidean_space)"
using split_times_into_modulo[OF assms[simplified]] .

lemma cart_euclidean_bound[intro]:
  assumes j:"j < DIM('a::euclidean_space)"
  shows "j + \<pi>' (i::'b::finite) * DIM('a) < CARD('b) * DIM('a::euclidean_space)"
  using linear_less_than_times[OF pi'_range j, of i] .

lemma (in euclidean_space) forall_CARD_DIM:
  "(\<forall>i<CARD('b) * DIM('a). P i) \<longleftrightarrow> (\<forall>(i::'b::finite) j. j<DIM('a) \<longrightarrow> P (j + \<pi>' i * DIM('a)))"
   (is "?l \<longleftrightarrow> ?r")
proof (safe elim!: split_times_into_modulo)
  fix i :: 'b and j assume "j < DIM('a)"
  note linear_less_than_times[OF pi'_range[of i] this]
  moreover assume "?l"
  ultimately show "P (j + \<pi>' i * DIM('a))" by auto
next
  fix i j assume "i < CARD('b)" "j < DIM('a)" and "?r"
  from `?r`[rule_format, OF `j < DIM('a)`, of "\<pi> i"] `i < CARD('b)`
  show "P (j + i * DIM('a))" by simp
qed

lemma (in euclidean_space) exists_CARD_DIM:
  "(\<exists>i<CARD('b) * DIM('a). P i) \<longleftrightarrow> (\<exists>i::'b::finite. \<exists>j<DIM('a). P (j + \<pi>' i * DIM('a)))"
  using forall_CARD_DIM[where 'b='b, of "\<lambda>x. \<not> P x"] by blast

lemma forall_CARD:
  "(\<forall>i<CARD('b). P i) \<longleftrightarrow> (\<forall>i::'b::finite. P (\<pi>' i))"
  using forall_CARD_DIM[where 'a=real, of P] by simp

lemma exists_CARD:
  "(\<exists>i<CARD('b). P i) \<longleftrightarrow> (\<exists>i::'b::finite. P (\<pi>' i))"
  using exists_CARD_DIM[where 'a=real, of P] by simp

lemmas cart_simps = forall_CARD_DIM exists_CARD_DIM forall_CARD exists_CARD

lemma cart_euclidean_nth[simp]:
  fixes x :: "('a::euclidean_space, 'b::finite) vec"
  assumes j:"j < DIM('a)"
  shows "x $$ (j + \<pi>' i * DIM('a)) = x $ i $$ j"
  unfolding euclidean_component_def inner_vec_def basis_eq_pi'[OF j] if_distrib cond_application_beta
  by (simp add: setsum_cases)

lemma real_euclidean_nth:
  fixes x :: "real^'n"
  shows "x $$ \<pi>' i = (x $ i :: real)"
  using cart_euclidean_nth[where 'a=real, of 0 x i] by simp

lemmas nth_conv_component = real_euclidean_nth[symmetric]

lemma mult_split_eq:
  fixes A :: nat assumes "x < A" "y < A"
  shows "x + i * A = y + j * A \<longleftrightarrow> x = y \<and> i = j"
proof
  assume *: "x + i * A = y + j * A"
  { fix x y i j assume "i < j" "x < A" and *: "x + i * A = y + j * A"
    hence "x + i * A < Suc i * A" using `x < A` by simp
    also have "\<dots> \<le> j * A" using `i < j` unfolding mult_le_cancel2 by simp
    also have "\<dots> \<le> y + j * A" by simp
    finally have "i = j" using * by simp }
  note eq = this

  have "i = j"
  proof (cases rule: linorder_cases)
    assume "i < j" from eq[OF this `x < A` *] show "i = j" by simp
  next
    assume "j < i" from eq[OF this `y < A` *[symmetric]] show "i = j" by simp
  qed simp
  thus "x = y \<and> i = j" using * by simp
qed simp

instance vec :: (ordered_euclidean_space, finite) ordered_euclidean_space
proof
  fix x y::"'a^'b"
  show "(x \<le> y) = (\<forall>i<DIM(('a, 'b) vec). x $$ i \<le> y $$ i)"
    unfolding less_eq_vec_def apply(subst eucl_le) by (simp add: cart_simps)
  show"(x < y) = (\<forall>i<DIM(('a, 'b) vec). x $$ i < y $$ i)"
    unfolding less_vec_def apply(subst eucl_less) by (simp add: cart_simps)
qed

subsection{* Basis vectors in coordinate directions. *}

definition "cart_basis k = (\<chi> i. if i = k then 1 else 0)"

lemma basis_component [simp]: "cart_basis k $ i = (if k=i then 1 else 0)"
  unfolding cart_basis_def by simp

lemma norm_basis[simp]:
  shows "norm (cart_basis k :: real ^'n) = 1"
  apply (simp add: cart_basis_def norm_eq_sqrt_inner) unfolding inner_vec_def
  apply (vector delta_mult_idempotent)
  using setsum_delta[of "UNIV :: 'n set" "k" "\<lambda>k. 1::real"] by auto

lemma norm_basis_1: "norm(cart_basis 1 :: real ^'n::{finite,one}) = 1"
  by (rule norm_basis)

lemma vector_choose_size: "0 <= c ==> \<exists>(x::real^'n). norm x = c"
  by (rule exI[where x="c *\<^sub>R cart_basis arbitrary"]) simp

lemma vector_choose_dist: assumes e: "0 <= e"
  shows "\<exists>(y::real^'n). dist x y = e"
proof-
  from vector_choose_size[OF e] obtain c:: "real ^'n"  where "norm c = e"
    by blast
  then have "dist x (x - c) = e" by (simp add: dist_norm)
  then show ?thesis by blast
qed

lemma basis_inj[intro]: "inj (cart_basis :: 'n \<Rightarrow> real ^'n)"
  by (simp add: inj_on_def vec_eq_iff)

lemma basis_expansion:
  "setsum (\<lambda>i. (x$i) *s cart_basis i) UNIV = (x::('a::ring_1) ^'n)" (is "?lhs = ?rhs" is "setsum ?f ?S = _")
  by (auto simp add: vec_eq_iff if_distrib setsum_delta[of "?S", where ?'b = "'a", simplified] cong del: if_weak_cong)

lemma smult_conv_scaleR: "c *s x = scaleR c x"
  unfolding vector_scalar_mult_def scaleR_vec_def by simp

lemma basis_expansion':
  "setsum (\<lambda>i. (x$i) *\<^sub>R cart_basis i) UNIV = x"
  by (rule basis_expansion [where 'a=real, unfolded smult_conv_scaleR])

lemma basis_expansion_unique:
  "setsum (\<lambda>i. f i *s cart_basis i) UNIV = (x::('a::comm_ring_1) ^'n) \<longleftrightarrow> (\<forall>i. f i = x$i)"
  by (simp add: vec_eq_iff setsum_delta if_distrib cong del: if_weak_cong)

lemma dot_basis:
  shows "cart_basis i \<bullet> x = x$i" "x \<bullet> (cart_basis i) = (x$i)"
  by (auto simp add: inner_vec_def cart_basis_def cond_application_beta if_distrib setsum_delta
           cong del: if_weak_cong)

lemma inner_basis:
  fixes x :: "'a::{real_inner, real_algebra_1} ^ 'n"
  shows "inner (cart_basis i) x = inner 1 (x $ i)"
    and "inner x (cart_basis i) = inner (x $ i) 1"
  unfolding inner_vec_def cart_basis_def
  by (auto simp add: cond_application_beta if_distrib setsum_delta cong del: if_weak_cong)

lemma basis_eq_0: "cart_basis i = (0::'a::semiring_1^'n) \<longleftrightarrow> False"
  by (auto simp add: vec_eq_iff)

lemma basis_nonzero:
  shows "cart_basis k \<noteq> (0:: 'a::semiring_1 ^'n)"
  by (simp add: basis_eq_0)

text {* some lemmas to map between Eucl and Cart *}
lemma basis_real_n[simp]:"(basis (\<pi>' i)::real^'a) = cart_basis i"
  unfolding basis_vec_def using pi'_range[where 'n='a]
  by (auto simp: vec_eq_iff axis_def)

subsection {* Orthogonality on cartesian products *}

lemma orthogonal_basis:
  shows "orthogonal (cart_basis i) x \<longleftrightarrow> x$i = (0::real)"
  by (auto simp add: orthogonal_def inner_vec_def cart_basis_def if_distrib
                     cond_application_beta setsum_delta cong del: if_weak_cong)

lemma orthogonal_basis_basis:
  shows "orthogonal (cart_basis i :: real^'n) (cart_basis j) \<longleftrightarrow> i \<noteq> j"
  unfolding orthogonal_basis[of i] basis_component[of j] by simp

subsection {* Linearity on cartesian products *}

lemma linear_vmul_component:
  assumes lf: "linear f"
  shows "linear (\<lambda>x. f x $ k *\<^sub>R v)"
  using lf
  by (auto simp add: linear_def algebra_simps)


subsection{* Adjoints on cartesian products *}

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
    let ?w = "(\<chi> i. (f (cart_basis i) \<bullet> y)) :: real ^ 'n"
    {fix x
      have "f x \<bullet> y = f (setsum (\<lambda>i. (x$i) *\<^sub>R cart_basis i) ?N) \<bullet> y"
        by (simp only: basis_expansion')
      also have "\<dots> = (setsum (\<lambda>i. (x$i) *\<^sub>R f (cart_basis i)) ?N) \<bullet> y"
        unfolding linear_setsum[OF lf fN]
        by (simp add: linear_cmul[OF lf])
      finally have "f x \<bullet> y = x \<bullet> ?w"
        apply (simp only: )
        apply (simp add: inner_vec_def setsum_left_distrib setsum_right_distrib setsum_commute[of _ ?M ?N] field_simps)
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
  by (rule adjoint_unique, simp add: adjoint_clauses [OF lf])


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
  by (auto simp only: if_distrib cond_application_beta setsum_delta'[OF finite]  mult_1_left mult_zero_left if_True UNIV_I)


lemma matrix_mul_rid:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "A ** mat 1 = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  by (auto simp only: if_distrib cond_application_beta setsum_delta[OF finite]  mult_1_right mult_zero_right if_True UNIV_I cong: if_cong)

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
  by (simp add: if_distrib cond_application_beta
    setsum_delta' cong del: if_weak_cong)

lemma matrix_transpose_mul: "transpose(A ** B) = transpose B ** transpose (A::'a::comm_semiring_1^_^_)"
  by (simp add: matrix_matrix_mult_def transpose_def vec_eq_iff mult_commute)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n ^ 'm"
  shows "A = B \<longleftrightarrow>  (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
  apply auto
  apply (subst vec_eq_iff)
  apply clarify
  apply (clarsimp simp add: matrix_vector_mult_def cart_basis_def if_distrib cond_application_beta vec_eq_iff cong del: if_weak_cong)
  apply (erule_tac x="cart_basis ia" in allE)
  apply (erule_tac x="i" in allE)
  by (auto simp add: cart_basis_def if_distrib cond_application_beta setsum_delta[OF finite] cong del: if_weak_cong)

lemma matrix_vector_mul_component:
  shows "((A::real^_^_) *v x)$k = (A$k) \<bullet> x"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma dot_lmul_matrix: "((x::real ^_) v* A) \<bullet> y = x \<bullet> (A *v y)"
  apply (simp add: inner_vec_def matrix_vector_mult_def vector_matrix_mult_def setsum_left_distrib setsum_right_distrib mult_ac)
  apply (subst setsum_commute)
  by simp

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

lemma columns_transpose: "columns(transpose (A::'a::semiring_1^_^_)) = rows A" by (metis transpose_transpose rows_transpose)

text{* Two sometimes fruitful ways of looking at matrix-vector multiplication. *}

lemma matrix_mult_dot: "A *v x = (\<chi> i. A$i \<bullet> x)"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma matrix_mult_vsum: "(A::'a::comm_semiring_1^'n^'m) *v x = setsum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def vec_eq_iff column_def mult_commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n) = (\<chi> j. setsum (\<lambda>i. (x$i) * (cart_basis i :: 'a^'n)$j) (UNIV :: 'n set))"
  apply (subst basis_expansion[symmetric])
  by (vector vec_eq_iff setsum_component)

lemma linear_componentwise:
  fixes f:: "real ^'m \<Rightarrow> real ^ _"
  assumes lf: "linear f"
  shows "(f x)$j = setsum (\<lambda>i. (x$i) * (f (cart_basis i)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof-
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (setsum (\<lambda>i.(x$i) *\<^sub>R f (cart_basis i) ) ?M)$j"
    unfolding vector_smult_component[symmetric] smult_conv_scaleR
    unfolding setsum_component[of "(\<lambda>i.(x$i) *\<^sub>R f (cart_basis i :: real^'m))" ?M]
    ..
  then show ?thesis unfolding linear_setsum_mul[OF lf fM, symmetric] basis_expansion' ..
qed

text{* Inverse matrices  (not necessarily square) *}

definition "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition "matrix_inv(A:: 'a::semiring_1^'n^'m) =
        (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

text{* Correspondence between matrices and linear operators. *}

definition matrix:: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
where "matrix f = (\<chi> i j. (f(cart_basis j))$i)"

lemma matrix_vector_mul_linear: "linear(\<lambda>x. A *v (x::real ^ _))"
  by (simp add: linear_def matrix_vector_mult_def vec_eq_iff field_simps setsum_right_distrib setsum_addf)

lemma matrix_works: assumes lf: "linear f" shows "matrix f *v x = f (x::real ^ 'n)"
apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult_commute)
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
  by (simp add: matrix_vector_mult_def transpose_def vec_eq_iff mult_commute)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique)
  apply (simp add: transpose_def inner_vec_def matrix_vector_mult_def setsum_left_distrib setsum_right_distrib)
  apply (subst setsum_commute)
  apply (auto simp add: mult_ac)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
  apply (subst matrix_vector_mul[OF lf])
  unfolding adjoint_matrix matrix_of_matrix_vector_mul ..

subsection {* lambda skolemization on cartesian products *}

(* FIXME: rename do choice_cart *)

lemma lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x $ i))" (is "?lhs \<longleftrightarrow> ?rhs")
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
      then have "P i (?x $ i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed

subsection {* Standard bases are a spanning set, and obviously finite. *}

lemma span_stdbasis:"span {cart_basis i :: real^'n | i. i \<in> (UNIV :: 'n set)} = UNIV"
apply (rule set_eqI)
apply auto
apply (subst basis_expansion'[symmetric])
apply (rule span_setsum)
apply simp
apply auto
apply (rule span_mul)
apply (rule span_superset)
apply auto
done

lemma finite_stdbasis: "finite {cart_basis i ::real^'n |i. i\<in> (UNIV:: 'n set)}" (is "finite ?S")
proof-
  have eq: "?S = cart_basis ` UNIV" by blast
  show ?thesis unfolding eq by auto
qed

lemma card_stdbasis: "card {cart_basis i ::real^'n |i. i\<in> (UNIV :: 'n set)} = CARD('n)" (is "card ?S = _")
proof-
  have eq: "?S = cart_basis ` UNIV" by blast
  show ?thesis unfolding eq using card_image[OF basis_inj] by simp
qed


lemma independent_stdbasis_lemma:
  assumes x: "(x::real ^ 'n) \<in> span (cart_basis ` S)"
  and iS: "i \<notin> S"
  shows "(x$i) = 0"
proof-
  let ?U = "UNIV :: 'n set"
  let ?B = "cart_basis ` S"
  let ?P = "{(x::real^_). \<forall>i\<in> ?U. i \<notin> S \<longrightarrow> x$i =0}"
 {fix x::"real^_" assume xS: "x\<in> ?B"
   from xS have "x \<in> ?P" by auto}
 moreover
 have "subspace ?P"
   by (auto simp add: subspace_def)
 ultimately show ?thesis
   using x span_induct[of x ?B ?P] iS by blast
qed

lemma independent_stdbasis: "independent {cart_basis i ::real^'n |i. i\<in> (UNIV :: 'n set)}"
proof-
  let ?I = "UNIV :: 'n set"
  let ?b = "cart_basis :: _ \<Rightarrow> real ^'n"
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

lemma vector_sub_project_orthogonal_cart: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps smult_conv_scaleR by auto

lemma linear_eq_stdbasis_cart:
  assumes lf: "linear (f::real^'m \<Rightarrow> _)" and lg: "linear g"
  and fg: "\<forall>i. f (cart_basis i) = g(cart_basis i)"
  shows "f = g"
proof-
  let ?U = "UNIV :: 'm set"
  let ?I = "{cart_basis i:: real^'m|i. i \<in> ?U}"
  {fix x assume x: "x \<in> (UNIV :: (real^'m) set)"
    from equalityD2[OF span_stdbasis]
    have IU: " (UNIV :: (real^'m) set) \<subseteq> span ?I" by blast
    from linear_eq[OF lf lg IU] fg x
    have "f x = g x" unfolding Ball_def mem_Collect_eq by metis}
  then show ?thesis by auto
qed

lemma bilinear_eq_stdbasis_cart:
  assumes bf: "bilinear (f:: real^'m \<Rightarrow> real^'n \<Rightarrow> _)"
  and bg: "bilinear g"
  and fg: "\<forall>i j. f (cart_basis i) (cart_basis j) = g (cart_basis i) (cart_basis j)"
  shows "f = g"
proof-
  from fg have th: "\<forall>x \<in> {cart_basis i| i. i\<in> (UNIV :: 'm set)}. \<forall>y\<in>  {cart_basis j |j. j \<in> (UNIV :: 'n set)}. f x y = g x y" by blast
  from bilinear_eq[OF bf bg equalityD2[OF span_stdbasis] equalityD2[OF span_stdbasis] th] show ?thesis by blast
qed

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

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
      using g(2) by (simp add: fun_eq_iff)
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
      using g(2) unfolding o_def fun_eq_iff id_def
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
        unfolding matrix_mult_vsum vec_eq_iff
        by auto
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
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
          proof(rule exI[where x= "?x"], vector, auto simp add: i x[symmetric] if_distrib right_distrib cond_application_beta cong del: if_weak_cong)
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

text {* The same result in terms of square matrices. *}

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

text {* Considering an n-element vector as an n-by-1 or 1-by-n matrix. *}

definition "rowvector v = (\<chi> i j. (v$j))"

definition "columnvector v = (\<chi> i j. (v$i))"

lemma transpose_columnvector:
 "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def vec_eq_iff)

lemma transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def vec_eq_iff)

lemma dot_rowvector_columnvector:
  "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product: "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vec_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
unfolding dot_matrix_product transpose_columnvector[symmetric]
  dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..


lemma infnorm_cart:"infnorm (x::real^'n) = Sup {abs(x$i) |i. i\<in> (UNIV :: 'n set)}"
  unfolding infnorm_def apply(rule arg_cong[where f=Sup]) apply safe
  apply(rule_tac x="\<pi> i" in exI) defer
  apply(rule_tac x="\<pi>' i" in exI) unfolding nth_conv_component using pi'_range by auto

lemma infnorm_set_image_cart:
  "{abs(x$i) |i. i\<in> (UNIV :: _ set)} =
  (\<lambda>i. abs(x$i)) ` (UNIV)" by blast

lemma infnorm_set_lemma_cart:
  shows "finite {abs((x::'a::abs ^'n)$i) |i. i\<in> (UNIV :: 'n set)}"
  and "{abs(x$i) |i. i\<in> (UNIV :: 'n::finite set)} \<noteq> {}"
  unfolding  infnorm_set_image_cart
  by auto

lemma component_le_infnorm_cart:
  shows "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
  unfolding nth_conv_component
  using component_le_infnorm[of x] .

lemma continuous_component:
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x $ i)"
  unfolding continuous_def by (rule tendsto_vec_nth)

lemma continuous_on_component:
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x $ i)"
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
  assumes "bounded s" and "\<forall>n. f n \<in> s"
  shows "\<forall>d.
        \<exists>l r. subseq r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
proof
  fix d::"'n set" have "finite d" by simp
  thus "\<exists>l::'a ^ 'n. \<exists>r. subseq r \<and>
      (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
  proof(induct d) case empty thus ?case unfolding subseq_def by auto
  next case (insert k d)
    have s': "bounded ((\<lambda>x. x $ k) ` s)" using `bounded s` by (rule bounded_component_cart)
    obtain l1::"'a^'n" and r1 where r1:"subseq r1" and lr1:"\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially"
      using insert(3) by auto
    have f': "\<forall>n. f (r1 n) $ k \<in> (\<lambda>x. x $ k) ` s" using `\<forall>n. f n \<in> s` by simp
    obtain l2 r2 where r2:"subseq r2" and lr2:"((\<lambda>i. f (r1 (r2 i)) $ k) ---> l2) sequentially"
      using bounded_imp_convergent_subsequence[OF s' f'] unfolding o_def by auto
    def r \<equiv> "r1 \<circ> r2" have r:"subseq r"
      using r1 and r2 unfolding r_def o_def subseq_def by auto
    moreover
    def l \<equiv> "(\<chi> i. if i = k then l2 else l1$i)::'a^'n"
    { fix e::real assume "e>0"
      from lr1 `e>0` have N1:"eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) $ i) (l1 $ i) < e) sequentially" by blast
      from lr2 `e>0` have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) $ k) l2 < e) sequentially" by (rule tendstoD)
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
  fix s :: "('a ^ 'b) set" and f :: "nat \<Rightarrow> 'a ^ 'b"
  assume s: "bounded s" and f: "\<forall>n. f n \<in> s"
  then obtain l r where r: "subseq r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma_cart [OF s f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite using divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vec_def using zero_le_dist by (rule setL2_le_setsum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule setsum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_elim1)
  }
  hence *:"((f \<circ> r) ---> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. subseq r \<and> ((f \<circ> r) ---> l) sequentially" by auto
qed

lemma interval_cart: fixes a :: "'a::ord^'n" shows
  "{a <..< b} = {x::'a^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}" and
  "{a .. b} = {x::'a^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma mem_interval_cart: fixes a :: "'a::ord^'n" shows
  "x \<in> {a<..<b} \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
  "x \<in> {a .. b} \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval_cart[of a b] by(auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma interval_eq_empty_cart: fixes a :: "real^'n" shows
 "({a <..< b} = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1) and
 "({a  ..  b} = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof-
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>{a <..< b}"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_interval_cart by auto
    hence "a$i < b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
        unfolding vector_smult_component and vector_add_component
        by auto  }
    hence "{a <..< b} \<noteq> {}" using mem_interval_cart(1)[of "?x" a b] by auto  }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>{a .. b}"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_interval_cart by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto  }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
        unfolding vector_smult_component and vector_add_component
        by auto  }
    hence "{a .. b} \<noteq> {}" using mem_interval_cart(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty_cart: fixes a :: "real^'n" shows
  "{a  ..  b} \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)" and
  "{a <..< b} \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty_cart[of a b] by (auto simp add: not_less not_le)
    (* BH: Why doesn't just "auto" work here? *)

lemma subset_interval_imp_cart: fixes a :: "real^'n" shows
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c .. d} \<subseteq> {a .. b}" and
 "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> {c .. d} \<subseteq> {a<..<b}" and
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a .. b}" and
 "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> {c<..<d} \<subseteq> {a<..<b}"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_interval_cart
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma interval_sing: fixes a :: "'a::linorder^'n" shows
 "{a .. a} = {a} \<and> {a<..<a} = {}"
apply(auto simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
apply (simp add: order_eq_iff)
apply (auto simp add: not_less less_imp_le)
done

lemma interval_open_subset_closed_cart:  fixes a :: "'a::preorder^'n" shows
 "{a<..<b} \<subseteq> {a .. b}"
proof(simp add: subset_eq, rule)
  fix x
  assume x:"x \<in>{a<..<b}"
  { fix i
    have "a $ i \<le> x $ i"
      using x order_less_imp_le[of "a$i" "x$i"]
      by(simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  }
  moreover
  { fix i
    have "x $ i \<le> b $ i"
      using x order_less_imp_le[of "x$i" "b$i"]
      by(simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  }
  ultimately
  show "a \<le> x \<and> x \<le> b"
    by(simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
qed

lemma subset_interval_cart: fixes a :: "real^'n" shows
 "{c .. d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1) and
 "{c .. d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2) and
 "{c<..<d} \<subseteq> {a .. b} \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3) and
 "{c<..<d} \<subseteq> {a<..<b} \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
  using subset_interval[of c d a b] by (simp_all add: cart_simps real_euclidean_nth)

lemma disjoint_interval_cart: fixes a::"real^'n" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1) and
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2) and
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3) and
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
  using disjoint_interval[of a b c d] by (simp_all add: cart_simps real_euclidean_nth)

lemma inter_interval_cart: fixes a :: "'a::linorder^'n" shows
 "{a .. b} \<inter> {c .. d} =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding set_eq_iff and Int_iff and mem_interval_cart
  by auto

lemma closed_interval_left_cart: fixes b::"real^'n"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le)

lemma closed_interval_right_cart: fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le)

lemma is_interval_cart:"is_interval (s::(real^'n) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i))) \<longrightarrow> x \<in> s)"
  unfolding is_interval_def Ball_def by (simp add: cart_simps real_euclidean_nth)

lemma closed_halfspace_component_le_cart:
  shows "closed {x::real^'n. x$i \<le> a}"
  by (simp add: closed_Collect_le)

lemma closed_halfspace_component_ge_cart:
  shows "closed {x::real^'n. x$i \<ge> a}"
  by (simp add: closed_Collect_le)

lemma open_halfspace_component_lt_cart:
  shows "open {x::real^'n. x$i < a}"
  by (simp add: open_Collect_less)

lemma open_halfspace_component_gt_cart:
  shows "open {x::real^'n. x$i  > a}"
  by (simp add: open_Collect_less)

lemma Lim_component_le_cart: fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f(x)$i \<le> b) net"
  shows "l$i \<le> b"
proof-
  { fix x have "x \<in> {x::real^'n. inner (cart_basis i) x \<le> b} \<longleftrightarrow> x$i \<le> b" unfolding inner_basis by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. inner (cart_basis i) x \<le> b}" f net l] unfolding *
    using closed_halfspace_le[of "(cart_basis i)::real^'n" b] and assms(1,2,3) by auto
qed

lemma Lim_component_ge_cart: fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f ---> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
proof-
  { fix x have "x \<in> {x::real^'n. inner (cart_basis i) x \<ge> b} \<longleftrightarrow> x$i \<ge> b" unfolding inner_basis by auto } note * = this
  show ?thesis using Lim_in_closed_set[of "{x. inner (cart_basis i) x \<ge> b}" f net l] unfolding *
    using closed_halfspace_ge[of b "(cart_basis i)::real^'n"] and assms(1,2,3) by auto
qed

lemma Lim_component_eq_cart: fixes f :: "'a \<Rightarrow> real^'n"
  assumes net:"(f ---> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff] using Lim_component_ge_cart[OF net, of b i] and
    Lim_component_le_cart[OF net, of i b] by auto

lemma connected_ivt_component_cart: fixes x::"real^'n" shows
 "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "(cart_basis k)::real^'n" a] by (auto simp add: inner_basis)

lemma subspace_substandard_cart:
 "subspace {x::real^_. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding subspace_def by auto

lemma closed_substandard_cart:
  "closed {x::'a::real_normed_vector ^ 'n. \<forall>i. P i \<longrightarrow> x$i = 0}"
proof-
  { fix i::'n
    have "closed {x::'a ^ 'n. P i \<longrightarrow> x$i = 0}"
      by (cases "P i", simp_all add: closed_Collect_eq) }
  thus ?thesis
    unfolding Collect_all_eq by (simp add: closed_INT)
qed

lemma dim_substandard_cart:
  shows "dim {x::real^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d" (is "dim ?A = _")
proof- have *:"{x. \<forall>i<DIM((real, 'n) vec). i \<notin> \<pi>' ` d \<longrightarrow> x $$ i = 0} = 
    {x::real^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0}"apply safe
    apply(erule_tac x="\<pi>' i" in allE) defer
    apply(erule_tac x="\<pi> i" in allE)
    unfolding image_iff real_euclidean_nth[symmetric] by (auto simp: pi'_inj[THEN inj_eq])
  have " \<pi>' ` d \<subseteq> {..<DIM((real, 'n) vec)}" using pi'_range[where 'n='n] by auto
  thus ?thesis using dim_substandard[of "\<pi>' ` d", where 'a="real^'n"] 
    unfolding * using card_image[of "\<pi>'" d] using pi'_inj unfolding inj_on_def by auto
qed

lemma affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) o (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) o (\<lambda>x. m *s x + c) = id"
  using m0
apply (auto simp add: fun_eq_iff vector_add_ldistrib)
by (simp_all add: vector_smult_lneg[symmetric] vector_smult_assoc vector_sneg_minus1[symmetric])

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
  show "m *s x + c = y" unfolding h diff_minus[symmetric]
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma vector_eq_affinity:
 "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma const_vector_cart:"((\<chi> i. d)::real^'n) = (\<chi>\<chi> i. d)"
  apply(subst euclidean_eq)
proof safe case goal1
  hence *:"(basis i::real^'n) = cart_basis (\<pi> i)"
    unfolding basis_real_n[THEN sym] by auto
  have "((\<chi> i. d)::real^'n) $$ i = d" unfolding euclidean_component_def *
    unfolding dot_basis by auto
  thus ?case using goal1 by auto
qed

subsection "Convex Euclidean Space"

lemma Cart_1:"(1::real^'n) = (\<chi>\<chi> i. 1)"
  apply(subst euclidean_eq)
proof safe case goal1 thus ?case using nth_conv_component[THEN sym,where i1="\<pi> i" and x1="1::real^'n"] by auto
qed

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]

lemmas vector_component_simps = vector_minus_component vector_smult_component vector_add_component less_eq_vec_def vec_lambda_beta basis_component vector_uminus_component

lemma convex_box_cart:
  assumes "\<And>i. convex {x. P i x}"
  shows "convex {x. \<forall>i. P i (x$i)}"
  using assms unfolding convex_def by auto

lemma convex_positive_orthant_cart: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  by (rule convex_box_cart) (simp add: atLeast_def[symmetric] convex_real_interval)

lemma unit_interval_convex_hull_cart:
  "{0::real^'n .. 1} = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}" (is "?int = convex hull ?points")
  unfolding Cart_1 unit_interval_convex_hull[where 'a="real^'n"]
  apply(rule arg_cong[where f="\<lambda>x. convex hull x"]) apply(rule set_eqI) unfolding mem_Collect_eq
  apply safe apply(erule_tac x="\<pi>' i" in allE) unfolding nth_conv_component defer
  apply(erule_tac x="\<pi> i" in allE) by auto

lemma cube_convex_hull_cart:
  assumes "0 < d" obtains s::"(real^'n) set" where "finite s" "{x - (\<chi> i. d) .. x + (\<chi> i. d)} = convex hull s" 
proof- from cube_convex_hull[OF assms, where 'a="real^'n" and x=x] guess s . note s=this
  show thesis apply(rule that[OF s(1)]) unfolding s(2)[THEN sym] const_vector_cart ..
qed

lemma std_simplex_cart:
  "(insert (0::real^'n) { cart_basis i | i. i\<in>UNIV}) =
  (insert 0 { basis i | i. i<DIM((real,'n) vec)})"
  apply(rule arg_cong[where f="\<lambda>s. (insert 0 s)"])
  unfolding basis_real_n[THEN sym] apply safe
  apply(rule_tac x="\<pi>' i" in exI) defer
  apply(rule_tac x="\<pi> i" in exI) using pi'_range[where 'n='n] by auto

subsection "Brouwer Fixpoint"

lemma kuhn_labelling_lemma_cart:
  assumes "(\<forall>x::real^_. P x \<longrightarrow> P (f x))"  "\<forall>x. P x \<longrightarrow> (\<forall>i. Q i \<longrightarrow> 0 \<le> x$i \<and> x$i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (x$i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (x$i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x$i \<le> f(x)$i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f(x)$i \<le> x$i)" proof-
  have and_forall_thm:"\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)" by auto
  have *:"\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> (x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x)" by auto
  show ?thesis unfolding and_forall_thm apply(subst choice_iff[THEN sym])+ proof(rule,rule) case goal1
    let ?R = "\<lambda>y. (P x \<and> Q xa \<and> x $ xa = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q xa \<and> x $ xa = 1 \<longrightarrow> y = 1) \<and> (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x $ xa \<le> f x $ xa) \<and> (P x \<and> Q xa \<and> y = 1 \<longrightarrow> f x $ xa \<le> x $ xa)"
    { assume "P x" "Q xa" hence "0 \<le> f x $ xa \<and> f x $ xa \<le> 1" using assms(2)[rule_format,of "f x" xa]
        apply(drule_tac assms(1)[rule_format]) by auto }
    hence "?R 0 \<or> ?R 1" by auto thus ?case by auto qed qed 

lemma interval_bij_cart:"interval_bij = (\<lambda> (a,b) (u,v) (x::real^'n).
    (\<chi> i. u$i + (x$i - a$i) / (b$i - a$i) * (v$i - u$i))::real^'n)"
  unfolding interval_bij_def apply(rule ext)+ apply safe
  unfolding vec_eq_iff vec_lambda_beta unfolding nth_conv_component
  apply rule apply(subst euclidean_lambda_beta) using pi'_range by auto

lemma interval_bij_affine_cart:
 "interval_bij (a,b) (u,v) = (\<lambda>x. (\<chi> i. (v$i - u$i) / (b$i - a$i) * x$i) +
            (\<chi> i. u$i - (v$i - u$i) / (b$i - a$i) * a$i)::real^'n)"
  apply rule unfolding vec_eq_iff interval_bij_cart vector_component_simps
  by(auto simp add: field_simps add_divide_distrib[THEN sym]) 

subsection "Derivative"

lemma has_derivative_vmul_component_cart: fixes c::"real^'a \<Rightarrow> real^'b" and v::"real^'c"
  assumes "(c has_derivative c') net"
  shows "((\<lambda>x. c(x)$k *\<^sub>R v) has_derivative (\<lambda>x. (c' x)$k *\<^sub>R v)) net"
  unfolding nth_conv_component
  by (intro has_derivative_intros assms)

lemma differentiable_at_imp_differentiable_on: "(\<forall>x\<in>(s::(real^'n) set). f differentiable at x) \<Longrightarrow> f differentiable_on s"
  unfolding differentiable_on_def by(auto intro!: differentiable_at_withinI)

definition "jacobian f net = matrix(frechet_derivative f net)"

lemma jacobian_works: "(f::(real^'a) \<Rightarrow> (real^'b)) differentiable net \<longleftrightarrow> (f has_derivative (\<lambda>h. (jacobian f net) *v h)) net"
  apply rule unfolding jacobian_def apply(simp only: matrix_works[OF linear_frechet_derivative]) defer
  apply(rule differentiableI) apply assumption unfolding frechet_derivative_works by assumption

subsection {* Component of the differential must be zero if it exists at a local        *)
(* maximum or minimum for that corresponding component. *}

lemma differential_zero_maxmin_component: fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "0 < e" "((\<forall>y \<in> ball x e. (f y)$k \<le> (f x)$k) \<or> (\<forall>y\<in>ball x e. (f x)$k \<le> (f y)$k))"
  "f differentiable (at x)" shows "jacobian f (at x) $ k = 0"
(* FIXME: reuse proof of generic differential_zero_maxmin_component*)

proof(rule ccontr)
  def D \<equiv> "jacobian f (at x)" assume "jacobian f (at x) $ k \<noteq> 0"
  then obtain j where j:"D$k$j \<noteq> 0" unfolding vec_eq_iff D_def by auto
  hence *:"abs (jacobian f (at x) $ k $ j) / 2 > 0" unfolding D_def by auto
  note as = assms(3)[unfolded jacobian_works has_derivative_at_alt]
  guess e' using as[THEN conjunct2,rule_format,OF *] .. note e' = this
  guess d using real_lbound_gt_zero[OF assms(1) e'[THEN conjunct1]] .. note d = this
  { fix c assume "abs c \<le> d" 
    hence *:"norm (x + c *\<^sub>R cart_basis j - x) < e'" using norm_basis[of j] d by auto
    have "\<bar>(f (x + c *\<^sub>R cart_basis j) - f x - D *v (c *\<^sub>R cart_basis j)) $ k\<bar> \<le> norm (f (x + c *\<^sub>R cart_basis j) - f x - D *v (c *\<^sub>R cart_basis j))" 
      by(rule component_le_norm_cart)
    also have "\<dots> \<le> \<bar>D $ k $ j\<bar> / 2 * \<bar>c\<bar>" using e'[THEN conjunct2,rule_format,OF *] and norm_basis[of j] unfolding D_def[symmetric] by auto
    finally have "\<bar>(f (x + c *\<^sub>R cart_basis j) - f x - D *v (c *\<^sub>R cart_basis j)) $ k\<bar> \<le> \<bar>D $ k $ j\<bar> / 2 * \<bar>c\<bar>" by simp
    hence "\<bar>f (x + c *\<^sub>R cart_basis j) $ k - f x $ k - c * D $ k $ j\<bar> \<le> \<bar>D $ k $ j\<bar> / 2 * \<bar>c\<bar>"
      unfolding vector_component_simps matrix_vector_mul_component unfolding smult_conv_scaleR[symmetric] 
      unfolding inner_simps dot_basis smult_conv_scaleR by simp  } note * = this
  have "x + d *\<^sub>R cart_basis j \<in> ball x e" "x - d *\<^sub>R cart_basis j \<in> ball x e"
    unfolding mem_ball dist_norm using norm_basis[of j] d by auto
  hence **:"((f (x - d *\<^sub>R cart_basis j))$k \<le> (f x)$k \<and> (f (x + d *\<^sub>R cart_basis j))$k \<le> (f x)$k) \<or>
         ((f (x - d *\<^sub>R cart_basis j))$k \<ge> (f x)$k \<and> (f (x + d *\<^sub>R cart_basis j))$k \<ge> (f x)$k)" using assms(2) by auto
  have ***:"\<And>y y1 y2 d dx::real. (y1\<le>y\<and>y2\<le>y) \<or> (y\<le>y1\<and>y\<le>y2) \<Longrightarrow> d < abs dx \<Longrightarrow> abs(y1 - y - - dx) \<le> d \<Longrightarrow> (abs (y2 - y - dx) \<le> d) \<Longrightarrow> False" by arith
  show False apply(rule ***[OF **, where dx="d * D $ k $ j" and d="\<bar>D $ k $ j\<bar> / 2 * \<bar>d\<bar>"]) 
    using *[of "-d"] and *[of d] and d[THEN conjunct1] and j unfolding mult_minus_left
    unfolding abs_mult diff_minus_eq_add scaleR_minus_left unfolding algebra_simps by (auto intro: mult_pos_pos)
qed

subsection {* Lemmas for working on @{typ "real^1"} *}

lemma forall_1[simp]: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis num1_eq_iff)

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
  unfolding UNIV_3 by (simp add: add_ac)

instantiation num1 :: cart_one begin
instance proof
  show "CARD(1) = Suc 0" by auto
qed end

(* "lift" from 'a to 'a^1 and "drop" from 'a^1 to 'a -- FIXME: potential use of transfer *)

abbreviation vec1:: "'a \<Rightarrow> 'a ^ 1" where "vec1 x \<equiv> vec x"

abbreviation dest_vec1:: "'a ^1 \<Rightarrow> 'a"
  where "dest_vec1 x \<equiv> (x$1)"

lemma vec1_dest_vec1[simp]: "vec1(dest_vec1 x) = x"
  by (simp add: vec_eq_iff)

lemma forall_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (vec1 x))"
  by (metis vec1_dest_vec1(1))

lemma exists_vec1: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P(vec1 x))"
  by (metis vec1_dest_vec1(1))

lemma dest_vec1_eq[simp]: "dest_vec1 x = dest_vec1 y \<longleftrightarrow> x = y"
  by (metis vec1_dest_vec1(1))

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

lemma range_vec1[simp]:"range vec1 = UNIV" apply(rule set_eqI,rule) unfolding image_iff defer
  apply(rule_tac x="dest_vec1 x" in bexI) by auto

lemma dest_vec1_lambda: "dest_vec1(\<chi> i. x i) = x 1"
  by (simp)

lemma dest_vec1_vec: "dest_vec1(vec x) = x"
  by (simp)

lemma dest_vec1_sum: assumes fS: "finite S"
  shows "dest_vec1(setsum f S) = setsum (dest_vec1 o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply simp
  apply auto
  done

lemma norm_vec1 [simp]: "norm(vec1 x) = abs(x)"
  by (simp add: vec_def norm_real)

lemma dist_vec1: "dist(vec1 x) (vec1 y) = abs(x - y)"
  by (simp only: dist_real vec_component)
lemma abs_dest_vec1: "norm x = \<bar>dest_vec1 x\<bar>"
  by (metis vec1_dest_vec1(1) norm_vec1)

lemmas vec1_dest_vec1_simps = forall_vec1 vec_add[THEN sym] dist_vec1 vec_sub[THEN sym] vec1_dest_vec1 norm_vec1 vector_smult_component
   vec_inj[where 'b=1] vec_cmul[THEN sym] smult_conv_scaleR[THEN sym] o_def dist_real_def real_norm_def

lemma bounded_linear_vec1:"bounded_linear (vec1::real\<Rightarrow>real^1)"
  unfolding bounded_linear_def additive_def bounded_linear_axioms_def 
  unfolding smult_conv_scaleR[THEN sym] unfolding vec1_dest_vec1_simps
  apply(rule conjI) defer apply(rule conjI) defer apply(rule_tac x=1 in exI) by auto

lemma linear_vmul_dest_vec1:
  fixes f:: "real^_ \<Rightarrow> real^1"
  shows "linear f \<Longrightarrow> linear (\<lambda>x. dest_vec1(f x) *s v)"
  unfolding smult_conv_scaleR
  by (rule linear_vmul_component)

lemma linear_from_scalars:
  assumes lf: "linear (f::real^1 \<Rightarrow> real^_)"
  shows "f = (\<lambda>x. dest_vec1 x *s column 1 (matrix f))"
  unfolding smult_conv_scaleR
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (auto simp add: vec_eq_iff matrix_vector_mult_def column_def mult_commute)
  done

lemma linear_to_scalars: assumes lf: "linear (f::real ^'n \<Rightarrow> real^1)"
  shows "f = (\<lambda>x. vec1(row 1 (matrix f) \<bullet> x))"
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (simp add: vec_eq_iff matrix_vector_mult_def row_def inner_vec_def mult_commute)
  done

lemma dest_vec1_eq_0: "dest_vec1 x = 0 \<longleftrightarrow> x = 0"
  by (simp add: dest_vec1_eq[symmetric])

lemma setsum_scalars: assumes fS: "finite S"
  shows "setsum f S = vec1 (setsum (dest_vec1 o f) S)"
  unfolding vec_setsum[OF fS] by simp

lemma dest_vec1_wlog_le: "(\<And>(x::'a::linorder ^ 1) y. P x y \<longleftrightarrow> P y x)  \<Longrightarrow> (\<And>x y. dest_vec1 x <= dest_vec1 y ==> P x y) \<Longrightarrow> P x y"
  apply (cases "dest_vec1 x \<le> dest_vec1 y")
  apply simp
  apply (subgoal_tac "dest_vec1 y \<le> dest_vec1 x")
  apply (auto)
  done

text{* Lifting and dropping *}

lemma continuous_on_o_dest_vec1: fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "continuous_on {a..b::real} f" shows "continuous_on {vec1 a..vec1 b} (f o dest_vec1)"
  using assms unfolding continuous_on_iff apply safe
  apply(erule_tac x="x$1" in ballE,erule_tac x=e in allE) apply safe
  apply(rule_tac x=d in exI) apply safe unfolding o_def dist_real_def dist_real 
  apply(erule_tac x="dest_vec1 x'" in ballE) by(auto simp add:less_eq_vec_def)

lemma continuous_on_o_vec1: fixes f::"real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "continuous_on {a..b} f" shows "continuous_on {dest_vec1 a..dest_vec1 b} (f o vec1)"
  using assms unfolding continuous_on_iff apply safe
  apply(erule_tac x="vec x" in ballE,erule_tac x=e in allE) apply safe
  apply(rule_tac x=d in exI) apply safe unfolding o_def dist_real_def dist_real 
  apply(erule_tac x="vec1 x'" in ballE) by(auto simp add:less_eq_vec_def)

lemma continuous_on_vec1:"continuous_on A (vec1::real\<Rightarrow>real^1)"
  by(rule linear_continuous_on[OF bounded_linear_vec1])

lemma mem_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b)"
 "(x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp_all add: vec_eq_iff less_vec_def less_eq_vec_def)

lemma vec1_interval:fixes a::"real" shows
  "vec1 ` {a .. b} = {vec1 a .. vec1 b}"
  "vec1 ` {a<..<b} = {vec1 a<..<vec1 b}"
  apply(rule_tac[!] set_eqI) unfolding image_iff less_vec_def unfolding mem_interval_cart
  unfolding forall_1 unfolding vec1_dest_vec1_simps
  apply rule defer apply(rule_tac x="dest_vec1 x" in bexI) prefer 3 apply rule defer
  apply(rule_tac x="dest_vec1 x" in bexI) by auto

(* Some special cases for intervals in R^1.                                  *)

lemma interval_cases_1: fixes x :: "real^1" shows
 "x \<in> {a .. b} ==> x \<in> {a<..<b} \<or> (x = a) \<or> (x = b)"
  unfolding vec_eq_iff less_vec_def less_eq_vec_def mem_interval_cart by(auto simp del:dest_vec1_eq)

lemma in_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b) \<and>
  (x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
  unfolding vec_eq_iff less_vec_def less_eq_vec_def mem_interval_cart by(auto simp del:dest_vec1_eq)

lemma interval_eq_empty_1: fixes a :: "real^1" shows
  "{a .. b} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a"
  "{a<..<b} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding interval_eq_empty_cart and ex_1 by auto

lemma subset_interval_1: fixes a :: "real^1" shows
 "({a .. b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a .. b} \<subseteq> {c<..<d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c < dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b < dest_vec1 d)"
 "({a<..<b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a<..<b} \<subseteq> {c<..<d} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
  unfolding subset_interval_cart[of a b c d] unfolding forall_1 by auto

lemma eq_interval_1: fixes a :: "real^1" shows
 "{a .. b} = {c .. d} \<longleftrightarrow>
          dest_vec1 b < dest_vec1 a \<and> dest_vec1 d < dest_vec1 c \<or>
          dest_vec1 a = dest_vec1 c \<and> dest_vec1 b = dest_vec1 d"
unfolding set_eq_subset[of "{a .. b}" "{c .. d}"]
unfolding subset_interval_1(1)[of a b c d]
unfolding subset_interval_1(1)[of c d a b]
by auto

lemma disjoint_interval_1: fixes a :: "real^1" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b < dest_vec1 c \<or> dest_vec1 d < dest_vec1 a"
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  unfolding disjoint_interval_cart and ex_1 by auto

lemma open_closed_interval_1: fixes a :: "real^1" shows
 "{a<..<b} = {a .. b} - {a, b}"
  unfolding set_eq_iff apply simp unfolding less_vec_def and less_eq_vec_def and forall_1 and dest_vec1_eq[THEN sym] by(auto simp del:dest_vec1_eq)

lemma closed_open_interval_1: "dest_vec1 (a::real^1) \<le> dest_vec1 b ==> {a .. b} = {a<..<b} \<union> {a,b}"
  unfolding set_eq_iff apply simp unfolding less_vec_def and less_eq_vec_def and forall_1 and dest_vec1_eq[THEN sym] by(auto simp del:dest_vec1_eq)

lemma Lim_drop_le: fixes f :: "'a \<Rightarrow> real^1" shows
  "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. dest_vec1 (f x) \<le> b) net ==> dest_vec1 l \<le> b"
  using Lim_component_le_cart[of f l net 1 b] by auto

lemma Lim_drop_ge: fixes f :: "'a \<Rightarrow> real^1" shows
 "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. b \<le> dest_vec1 (f x)) net ==> b \<le> dest_vec1 l"
  using Lim_component_ge_cart[of f l net b 1] by auto

text{* Also more convenient formulations of monotone convergence.                *}

lemma bounded_increasing_convergent: fixes s::"nat \<Rightarrow> real^1"
  assumes "bounded {s n| n::nat. True}"  "\<forall>n. dest_vec1(s n) \<le> dest_vec1(s(Suc n))"
  shows "\<exists>l. (s ---> l) sequentially"
proof-
  obtain a where a:"\<forall>n. \<bar>dest_vec1 (s n)\<bar> \<le>  a" using assms(1)[unfolded bounded_iff abs_dest_vec1] by auto
  { fix m::nat
    have "\<And> n. n\<ge>m \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)"
      apply(induct_tac n) apply simp using assms(2) apply(erule_tac x="na" in allE) by(auto simp add: not_less_eq_eq)  }
  hence "\<forall>m n. m \<le> n \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)" by auto
  then obtain l where "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>dest_vec1 (s n) - l\<bar> < e" using convergent_bounded_monotone[OF a] unfolding monoseq_def by auto
  thus ?thesis unfolding LIMSEQ_def apply(rule_tac x="vec1 l" in exI)
    unfolding dist_norm unfolding abs_dest_vec1  by auto
qed

lemma dest_vec1_simps[simp]: fixes a::"real^1"
  shows "a$1 = 0 \<longleftrightarrow> a = 0" (*"a \<le> 1 \<longleftrightarrow> dest_vec1 a \<le> 1" "0 \<le> a \<longleftrightarrow> 0 \<le> dest_vec1 a"*)
  "a \<le> b \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 b" "dest_vec1 (1::real^1) = 1"
  by(auto simp add: less_eq_vec_def vec_eq_iff)

lemma dest_vec1_inverval:
  "dest_vec1 ` {a .. b} = {dest_vec1 a .. dest_vec1 b}"
  "dest_vec1 ` {a<.. b} = {dest_vec1 a<.. dest_vec1 b}"
  "dest_vec1 ` {a ..<b} = {dest_vec1 a ..<dest_vec1 b}"
  "dest_vec1 ` {a<..<b} = {dest_vec1 a<..<dest_vec1 b}"
  apply(rule_tac [!] equalityI)
  unfolding subset_eq Ball_def Bex_def mem_interval_1 image_iff
  apply(rule_tac [!] allI)apply(rule_tac [!] impI)
  apply(rule_tac[2] x="vec1 x" in exI)apply(rule_tac[4] x="vec1 x" in exI)
  apply(rule_tac[6] x="vec1 x" in exI)apply(rule_tac[8] x="vec1 x" in exI)
  by (auto simp add: less_vec_def less_eq_vec_def)

lemma dest_vec1_setsum: assumes "finite S"
  shows " dest_vec1 (setsum f S) = setsum (\<lambda>x. dest_vec1 (f x)) S"
  using dest_vec1_sum[OF assms] by auto

lemma open_dest_vec1_vimage: "open S \<Longrightarrow> open (dest_vec1 -` S)"
unfolding open_vec_def forall_1 by auto

lemma tendsto_dest_vec1 [tendsto_intros]:
  "(f ---> l) net \<Longrightarrow> ((\<lambda>x. dest_vec1 (f x)) ---> dest_vec1 l) net"
by(rule tendsto_vec_nth)

lemma continuous_dest_vec1: "continuous net f \<Longrightarrow> continuous net (\<lambda>x. dest_vec1 (f x))"
  unfolding continuous_def by (rule tendsto_dest_vec1)

lemma forall_dest_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P(dest_vec1 x))" 
  apply safe defer apply(erule_tac x="vec1 x" in allE) by auto

lemma forall_of_dest_vec1: "(\<forall>v. P (\<lambda>x. dest_vec1 (v x))) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 \<circ> x)" in allE) unfolding o_def vec1_dest_vec1 by auto 

lemma forall_of_dest_vec1': "(\<forall>v. P (dest_vec1 v)) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 x)" in allE) defer apply rule 
  apply(erule_tac x="dest_vec1 v" in allE) unfolding o_def vec1_dest_vec1 by auto

lemma dist_vec1_0[simp]: "dist(vec1 (x::real)) 0 = norm x" unfolding dist_norm by auto

lemma bounded_linear_vec1_dest_vec1: fixes f::"real \<Rightarrow> real"
  shows "linear (vec1 \<circ> f \<circ> dest_vec1) = bounded_linear f" (is "?l = ?r") proof-
  { assume ?l guess K using linear_bounded[OF `?l`] ..
    hence "\<exists>K. \<forall>x. \<bar>f x\<bar> \<le> \<bar>x\<bar> * K" apply(rule_tac x=K in exI)
      unfolding vec1_dest_vec1_simps by (auto simp add:field_simps) }
  thus ?thesis unfolding linear_def bounded_linear_def additive_def bounded_linear_axioms_def o_def
    unfolding vec1_dest_vec1_simps by auto qed

lemma vec1_le[simp]:fixes a::real shows "vec1 a \<le> vec1 b \<longleftrightarrow> a \<le> b"
  unfolding less_eq_vec_def by auto
lemma vec1_less[simp]:fixes a::real shows "vec1 a < vec1 b \<longleftrightarrow> a < b"
  unfolding less_vec_def by auto


subsection {* Derivatives on real = Derivatives on @{typ "real^1"} *}

lemma has_derivative_within_vec1_dest_vec1: fixes f::"real\<Rightarrow>real" shows
  "((vec1 \<circ> f \<circ> dest_vec1) has_derivative (vec1 \<circ> f' \<circ> dest_vec1)) (at (vec1 x) within vec1 ` s)
  = (f has_derivative f') (at x within s)"
  unfolding has_derivative_within unfolding bounded_linear_vec1_dest_vec1[unfolded linear_conv_bounded_linear]
  unfolding o_def Lim_within Ball_def unfolding forall_vec1 
  unfolding vec1_dest_vec1_simps dist_vec1_0 image_iff by auto  

lemma has_derivative_at_vec1_dest_vec1: fixes f::"real\<Rightarrow>real" shows
  "((vec1 \<circ> f \<circ> dest_vec1) has_derivative (vec1 \<circ> f' \<circ> dest_vec1)) (at (vec1 x)) = (f has_derivative f') (at x)"
  using has_derivative_within_vec1_dest_vec1[where s=UNIV, unfolded range_vec1 within_UNIV] by auto

lemma bounded_linear_vec1': fixes f::"'a::real_normed_vector\<Rightarrow>real"
  shows "bounded_linear f = bounded_linear (vec1 \<circ> f)"
  unfolding bounded_linear_def additive_def bounded_linear_axioms_def o_def
  unfolding vec1_dest_vec1_simps by auto

lemma bounded_linear_dest_vec1: fixes f::"real\<Rightarrow>'a::real_normed_vector"
  shows "bounded_linear f = bounded_linear (f \<circ> dest_vec1)"
  unfolding bounded_linear_def additive_def bounded_linear_axioms_def o_def
  unfolding vec1_dest_vec1_simps by auto

lemma has_derivative_at_vec1: fixes f::"'a::real_normed_vector\<Rightarrow>real" shows
  "(f has_derivative f') (at x) = ((vec1 \<circ> f) has_derivative (vec1 \<circ> f')) (at x)"
  unfolding has_derivative_at unfolding bounded_linear_vec1'[unfolded linear_conv_bounded_linear]
  unfolding o_def Lim_at unfolding vec1_dest_vec1_simps dist_vec1_0 by auto

lemma has_derivative_within_dest_vec1:fixes f::"real\<Rightarrow>'a::real_normed_vector" shows
  "((f \<circ> dest_vec1) has_derivative (f' \<circ> dest_vec1)) (at (vec1 x) within vec1 ` s) = (f has_derivative f') (at x within s)"
  unfolding has_derivative_within bounded_linear_dest_vec1 unfolding o_def Lim_within Ball_def
  unfolding vec1_dest_vec1_simps dist_vec1_0 image_iff by auto

lemma has_derivative_at_dest_vec1:fixes f::"real\<Rightarrow>'a::real_normed_vector" shows
  "((f \<circ> dest_vec1) has_derivative (f' \<circ> dest_vec1)) (at (vec1 x)) = (f has_derivative f') (at x)"
  using has_derivative_within_dest_vec1[where s=UNIV] by simp

subsection {* In particular if we have a mapping into @{typ "real^1"}. *}

lemma onorm_vec1: fixes f::"real \<Rightarrow> real"
  shows "onorm (\<lambda>x. vec1 (f (dest_vec1 x))) = onorm f" proof-
  have "\<forall>x::real^1. norm x = 1 \<longleftrightarrow> x\<in>{vec1 -1, vec1 (1::real)}" unfolding forall_vec1 by(auto simp add:vec_eq_iff)
  hence 1:"{x. norm x = 1} = {vec1 -1, vec1 (1::real)}" by auto
  have 2:"{norm (vec1 (f (dest_vec1 x))) |x. norm x = 1} = (\<lambda>x. norm (vec1 (f (dest_vec1 x)))) ` {x. norm x=1}" by auto
  have "\<forall>x::real. norm x = 1 \<longleftrightarrow> x\<in>{-1, 1}" by auto hence 3:"{x. norm x = 1} = {-1, (1::real)}" by auto
  have 4:"{norm (f x) |x. norm x = 1} = (\<lambda>x. norm (f x)) ` {x. norm x=1}" by auto
  show ?thesis unfolding onorm_def 1 2 3 4 by(simp add:Sup_finite_Max) qed

lemma convex_vec1:"convex (vec1 ` s) = convex (s::real set)"
  unfolding convex_def Ball_def forall_vec1 unfolding vec1_dest_vec1_simps image_iff by auto

lemma bounded_linear_component_cart[intro]: "bounded_linear (\<lambda>x::real^'n. x $ k)"
  apply(rule bounded_linearI[where K=1]) 
  using component_le_norm_cart[of _ k] unfolding real_norm_def by auto

lemma bounded_vec1[intro]:  "bounded s \<Longrightarrow> bounded (vec1 ` (s::real set))"
  unfolding bounded_def apply safe apply(rule_tac x="vec1 x" in exI,rule_tac x=e in exI)
  by(auto simp add: dist_real dist_real_def)

(*lemma content_closed_interval_cases_cart:
  "content {a..b::real^'n} =
  (if {a..b} = {} then 0 else setprod (\<lambda>i. b$i - a$i) UNIV)" 
proof(cases "{a..b} = {}")
  case True thus ?thesis unfolding content_def by auto
next case Falsethus ?thesis unfolding content_def unfolding if_not_P[OF False]
  proof(cases "\<forall>i. a $ i \<le> b $ i")
    case False thus ?thesis unfolding content_def using t by auto
  next case True note interval_eq_empty
   apply auto 
  
  sorry*)

lemma integral_component_eq_cart[simp]: fixes f::"'n::ordered_euclidean_space \<Rightarrow> real^'m"
  assumes "f integrable_on s" shows "integral s (\<lambda>x. f x $ k) = integral s f $ k"
  using integral_linear[OF assms(1) bounded_linear_component_cart,unfolded o_def] .

lemma interval_split_cart:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "{a..b} \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  apply(rule_tac[!] set_eqI) unfolding Int_iff mem_interval_cart mem_Collect_eq
  unfolding vec_lambda_beta by auto

(*lemma content_split_cart:
  "content {a..b::real^'n} = content({a..b} \<inter> {x. x$k \<le> c}) + content({a..b} \<inter> {x. x$k >= c})"
proof- note simps = interval_split_cart content_closed_interval_cases_cart vec_lambda_beta less_eq_vec_def
  { presume "a\<le>b \<Longrightarrow> ?thesis" thus ?thesis apply(cases "a\<le>b") unfolding simps by auto }
  have *:"UNIV = insert k (UNIV - {k})" "\<And>x. finite (UNIV-{x::'n})" "\<And>x. x\<notin>UNIV-{x}" by auto
  have *:"\<And>X Y Z. (\<Prod>i\<in>UNIV. Z i (if i = k then X else Y i)) = Z k X * (\<Prod>i\<in>UNIV-{k}. Z i (Y i))"
    "(\<Prod>i\<in>UNIV. b$i - a$i) = (\<Prod>i\<in>UNIV-{k}. b$i - a$i) * (b$k - a$k)" 
    apply(subst *(1)) defer apply(subst *(1)) unfolding setprod_insert[OF *(2-)] by auto
  assume as:"a\<le>b" moreover have "\<And>x. min (b $ k) c = max (a $ k) c
    \<Longrightarrow> x* (b$k - a$k) = x*(max (a $ k) c - a $ k) + x*(b $ k - max (a $ k) c)"
    by  (auto simp add:field_simps)
  moreover have "\<not> a $ k \<le> c \<Longrightarrow> \<not> c \<le> b $ k \<Longrightarrow> False"
    unfolding not_le using as[unfolded less_eq_vec_def,rule_format,of k] by auto
  ultimately show ?thesis 
    unfolding simps unfolding *(1)[of "\<lambda>i x. b$i - x"] *(1)[of "\<lambda>i x. x - a$i"] *(2) by(auto)
qed*)

lemma has_integral_vec1:
  assumes "(f has_integral k) {a..b}"
  shows "((\<lambda>x. vec1 (f x)) has_integral (vec1 k)) {a..b}"
proof -
  have *: "\<And>p. (\<Sum>(x, k)\<in>p. content k *\<^sub>R vec1 (f x)) - vec1 k = vec1 ((\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) - k)"
    unfolding vec_sub vec_eq_iff by (auto simp add: split_beta)
  show ?thesis
    using assms unfolding has_integral
    apply safe
    apply(erule_tac x=e in allE,safe)
    apply(rule_tac x=d in exI,safe)
    apply(erule_tac x=p in allE,safe)
    unfolding * norm_vector_1
    apply auto
    done
qed

end

(*  Title:      HOL/Real_Vector_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

header {* Vector Spaces and Algebras over the Reals *}

theory Real_Vector_Spaces
imports Real Topological_Spaces
begin

subsection {* Locale for additive functions *}

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"
begin

lemma zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma diff: "f (x - y) = f x - f y"
  using add [of x "- y"] by (simp add: minus)

lemma setsum: "f (setsum g A) = (\<Sum>x\<in>A. f (g x))"
apply (cases "finite A")
apply (induct set: finite)
apply (simp add: zero)
apply (simp add: add)
apply (simp add: zero)
done

end

subsection {* Vector spaces *}

locale vector_space =
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
  assumes scale_right_distrib [algebra_simps]:
    "scale a (x + y) = scale a x + scale a y"
  and scale_left_distrib [algebra_simps]:
    "scale (a + b) x = scale a x + scale b x"
  and scale_scale [simp]: "scale a (scale b x) = scale (a * b) x"
  and scale_one [simp]: "scale 1 x = x"
begin

lemma scale_left_commute:
  "scale a (scale b x) = scale b (scale a x)"
by (simp add: mult_commute)

lemma scale_zero_left [simp]: "scale 0 x = 0"
  and scale_minus_left [simp]: "scale (- a) x = - (scale a x)"
  and scale_left_diff_distrib [algebra_simps]:
        "scale (a - b) x = scale a x - scale b x"
  and scale_setsum_left: "scale (setsum f A) x = (\<Sum>a\<in>A. scale (f a) x)"
proof -
  interpret s: additive "\<lambda>a. scale a x"
    proof qed (rule scale_left_distrib)
  show "scale 0 x = 0" by (rule s.zero)
  show "scale (- a) x = - (scale a x)" by (rule s.minus)
  show "scale (a - b) x = scale a x - scale b x" by (rule s.diff)
  show "scale (setsum f A) x = (\<Sum>a\<in>A. scale (f a) x)" by (rule s.setsum)
qed

lemma scale_zero_right [simp]: "scale a 0 = 0"
  and scale_minus_right [simp]: "scale a (- x) = - (scale a x)"
  and scale_right_diff_distrib [algebra_simps]:
        "scale a (x - y) = scale a x - scale a y"
  and scale_setsum_right: "scale a (setsum f A) = (\<Sum>x\<in>A. scale a (f x))"
proof -
  interpret s: additive "\<lambda>x. scale a x"
    proof qed (rule scale_right_distrib)
  show "scale a 0 = 0" by (rule s.zero)
  show "scale a (- x) = - (scale a x)" by (rule s.minus)
  show "scale a (x - y) = scale a x - scale a y" by (rule s.diff)
  show "scale a (setsum f A) = (\<Sum>x\<in>A. scale a (f x))" by (rule s.setsum)
qed

lemma scale_eq_0_iff [simp]:
  "scale a x = 0 \<longleftrightarrow> a = 0 \<or> x = 0"
proof cases
  assume "a = 0" thus ?thesis by simp
next
  assume anz [simp]: "a \<noteq> 0"
  { assume "scale a x = 0"
    hence "scale (inverse a) (scale a x) = 0" by simp
    hence "x = 0" by simp }
  thus ?thesis by force
qed

lemma scale_left_imp_eq:
  "\<lbrakk>a \<noteq> 0; scale a x = scale a y\<rbrakk> \<Longrightarrow> x = y"
proof -
  assume nonzero: "a \<noteq> 0"
  assume "scale a x = scale a y"
  hence "scale a (x - y) = 0"
     by (simp add: scale_right_diff_distrib)
  hence "x - y = 0" by (simp add: nonzero)
  thus "x = y" by (simp only: right_minus_eq)
qed

lemma scale_right_imp_eq:
  "\<lbrakk>x \<noteq> 0; scale a x = scale b x\<rbrakk> \<Longrightarrow> a = b"
proof -
  assume nonzero: "x \<noteq> 0"
  assume "scale a x = scale b x"
  hence "scale (a - b) x = 0"
     by (simp add: scale_left_diff_distrib)
  hence "a - b = 0" by (simp add: nonzero)
  thus "a = b" by (simp only: right_minus_eq)
qed

lemma scale_cancel_left [simp]:
  "scale a x = scale a y \<longleftrightarrow> x = y \<or> a = 0"
by (auto intro: scale_left_imp_eq)

lemma scale_cancel_right [simp]:
  "scale a x = scale b x \<longleftrightarrow> a = b \<or> x = 0"
by (auto intro: scale_right_imp_eq)

end

subsection {* Real vector spaces *}

class scaleR =
  fixes scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>R" 75)
begin

abbreviation
  divideR :: "'a \<Rightarrow> real \<Rightarrow> 'a" (infixl "'/\<^sub>R" 70)
where
  "x /\<^sub>R r == scaleR (inverse r) x"

end

class real_vector = scaleR + ab_group_add +
  assumes scaleR_add_right: "scaleR a (x + y) = scaleR a x + scaleR a y"
  and scaleR_add_left: "scaleR (a + b) x = scaleR a x + scaleR b x"
  and scaleR_scaleR: "scaleR a (scaleR b x) = scaleR (a * b) x"
  and scaleR_one: "scaleR 1 x = x"

interpretation real_vector:
  vector_space "scaleR :: real \<Rightarrow> 'a \<Rightarrow> 'a::real_vector"
apply unfold_locales
apply (rule scaleR_add_right)
apply (rule scaleR_add_left)
apply (rule scaleR_scaleR)
apply (rule scaleR_one)
done

text {* Recover original theorem names *}

lemmas scaleR_left_commute = real_vector.scale_left_commute
lemmas scaleR_zero_left = real_vector.scale_zero_left
lemmas scaleR_minus_left = real_vector.scale_minus_left
lemmas scaleR_diff_left = real_vector.scale_left_diff_distrib
lemmas scaleR_setsum_left = real_vector.scale_setsum_left
lemmas scaleR_zero_right = real_vector.scale_zero_right
lemmas scaleR_minus_right = real_vector.scale_minus_right
lemmas scaleR_diff_right = real_vector.scale_right_diff_distrib
lemmas scaleR_setsum_right = real_vector.scale_setsum_right
lemmas scaleR_eq_0_iff = real_vector.scale_eq_0_iff
lemmas scaleR_left_imp_eq = real_vector.scale_left_imp_eq
lemmas scaleR_right_imp_eq = real_vector.scale_right_imp_eq
lemmas scaleR_cancel_left = real_vector.scale_cancel_left
lemmas scaleR_cancel_right = real_vector.scale_cancel_right

text {* Legacy names *}

lemmas scaleR_left_distrib = scaleR_add_left
lemmas scaleR_right_distrib = scaleR_add_right
lemmas scaleR_left_diff_distrib = scaleR_diff_left
lemmas scaleR_right_diff_distrib = scaleR_diff_right

lemma scaleR_minus1_left [simp]:
  fixes x :: "'a::real_vector"
  shows "scaleR (-1) x = - x"
  using scaleR_minus_left [of 1 x] by simp

class real_algebra = real_vector + ring +
  assumes mult_scaleR_left [simp]: "scaleR a x * y = scaleR a (x * y)"
  and mult_scaleR_right [simp]: "x * scaleR a y = scaleR a (x * y)"

class real_algebra_1 = real_algebra + ring_1

class real_div_algebra = real_algebra_1 + division_ring

class real_field = real_div_algebra + field

instantiation real :: real_field
begin

definition
  real_scaleR_def [simp]: "scaleR a x = a * x"

instance proof
qed (simp_all add: algebra_simps)

end

interpretation scaleR_left: additive "(\<lambda>a. scaleR a x::'a::real_vector)"
proof qed (rule scaleR_left_distrib)

interpretation scaleR_right: additive "(\<lambda>x. scaleR a x::'a::real_vector)"
proof qed (rule scaleR_right_distrib)

lemma nonzero_inverse_scaleR_distrib:
  fixes x :: "'a::real_div_algebra" shows
  "\<lbrakk>a \<noteq> 0; x \<noteq> 0\<rbrakk> \<Longrightarrow> inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
by (rule inverse_unique, simp)

lemma inverse_scaleR_distrib:
  fixes x :: "'a::{real_div_algebra, division_ring_inverse_zero}"
  shows "inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
apply (case_tac "a = 0", simp)
apply (case_tac "x = 0", simp)
apply (erule (1) nonzero_inverse_scaleR_distrib)
done


subsection {* Embedding of the Reals into any @{text real_algebra_1}:
@{term of_real} *}

definition
  of_real :: "real \<Rightarrow> 'a::real_algebra_1" where
  "of_real r = scaleR r 1"

lemma scaleR_conv_of_real: "scaleR r x = of_real r * x"
by (simp add: of_real_def)

lemma of_real_0 [simp]: "of_real 0 = 0"
by (simp add: of_real_def)

lemma of_real_1 [simp]: "of_real 1 = 1"
by (simp add: of_real_def)

lemma of_real_add [simp]: "of_real (x + y) = of_real x + of_real y"
by (simp add: of_real_def scaleR_left_distrib)

lemma of_real_minus [simp]: "of_real (- x) = - of_real x"
by (simp add: of_real_def)

lemma of_real_diff [simp]: "of_real (x - y) = of_real x - of_real y"
by (simp add: of_real_def scaleR_left_diff_distrib)

lemma of_real_mult [simp]: "of_real (x * y) = of_real x * of_real y"
by (simp add: of_real_def mult_commute)

lemma of_real_setsum[simp]: "of_real (setsum f s) = (\<Sum>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_real_setprod[simp]: "of_real (setprod f s) = (\<Prod>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_real (inverse x) =
   inverse (of_real x :: 'a::real_div_algebra)"
by (simp add: of_real_def nonzero_inverse_scaleR_distrib)

lemma of_real_inverse [simp]:
  "of_real (inverse x) =
   inverse (of_real x :: 'a::{real_div_algebra, division_ring_inverse_zero})"
by (simp add: of_real_def inverse_scaleR_distrib)

lemma nonzero_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> of_real (x / y) =
   (of_real x / of_real y :: 'a::real_field)"
by (simp add: divide_inverse nonzero_of_real_inverse)

lemma of_real_divide [simp]:
  "of_real (x / y) =
   (of_real x / of_real y :: 'a::{real_field, field_inverse_zero})"
by (simp add: divide_inverse)

lemma of_real_power [simp]:
  "of_real (x ^ n) = (of_real x :: 'a::{real_algebra_1}) ^ n"
by (induct n) simp_all

lemma of_real_eq_iff [simp]: "(of_real x = of_real y) = (x = y)"
by (simp add: of_real_def)

lemma inj_of_real:
  "inj of_real"
  by (auto intro: injI)

lemmas of_real_eq_0_iff [simp] = of_real_eq_iff [of _ 0, simplified]

lemma of_real_eq_id [simp]: "of_real = (id :: real \<Rightarrow> real)"
proof
  fix r
  show "of_real r = id r"
    by (simp add: of_real_def)
qed

text{*Collapse nested embeddings*}
lemma of_real_of_nat_eq [simp]: "of_real (of_nat n) = of_nat n"
by (induct n) auto

lemma of_real_of_int_eq [simp]: "of_real (of_int z) = of_int z"
by (cases z rule: int_diff_cases, simp)

lemma of_real_real_of_nat_eq [simp]: "of_real (real n) = of_nat n"
  by (simp add: real_of_nat_def)

lemma of_real_real_of_int_eq [simp]: "of_real (real z) = of_int z"
  by (simp add: real_of_int_def)

lemma of_real_numeral: "of_real (numeral w) = numeral w"
using of_real_of_int_eq [of "numeral w"] by simp

lemma of_real_neg_numeral: "of_real (- numeral w) = - numeral w"
using of_real_of_int_eq [of "- numeral w"] by simp

text{*Every real algebra has characteristic zero*}

instance real_algebra_1 < ring_char_0
proof
  from inj_of_real inj_of_nat have "inj (of_real \<circ> of_nat)" by (rule inj_comp)
  then show "inj (of_nat :: nat \<Rightarrow> 'a)" by (simp add: comp_def)
qed

instance real_field < field_char_0 ..


subsection {* The Set of Real Numbers *}

definition Reals :: "'a::real_algebra_1 set" where
  "Reals = range of_real"

notation (xsymbols)
  Reals  ("\<real>")

lemma Reals_of_real [simp]: "of_real r \<in> Reals"
by (simp add: Reals_def)

lemma Reals_of_int [simp]: "of_int z \<in> Reals"
by (subst of_real_of_int_eq [symmetric], rule Reals_of_real)

lemma Reals_of_nat [simp]: "of_nat n \<in> Reals"
by (subst of_real_of_nat_eq [symmetric], rule Reals_of_real)

lemma Reals_numeral [simp]: "numeral w \<in> Reals"
by (subst of_real_numeral [symmetric], rule Reals_of_real)

lemma Reals_0 [simp]: "0 \<in> Reals"
apply (unfold Reals_def)
apply (rule range_eqI)
apply (rule of_real_0 [symmetric])
done

lemma Reals_1 [simp]: "1 \<in> Reals"
apply (unfold Reals_def)
apply (rule range_eqI)
apply (rule of_real_1 [symmetric])
done

lemma Reals_add [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a + b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_add [symmetric])
done

lemma Reals_minus [simp]: "a \<in> Reals \<Longrightarrow> - a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_minus [symmetric])
done

lemma Reals_diff [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a - b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_diff [symmetric])
done

lemma Reals_mult [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a * b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_mult [symmetric])
done

lemma nonzero_Reals_inverse:
  fixes a :: "'a::real_div_algebra"
  shows "\<lbrakk>a \<in> Reals; a \<noteq> 0\<rbrakk> \<Longrightarrow> inverse a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (erule nonzero_of_real_inverse [symmetric])
done

lemma Reals_inverse:
  fixes a :: "'a::{real_div_algebra, division_ring_inverse_zero}"
  shows "a \<in> Reals \<Longrightarrow> inverse a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_inverse [symmetric])
done

lemma Reals_inverse_iff [simp]: 
  fixes x:: "'a :: {real_div_algebra, division_ring_inverse_zero}"
  shows "inverse x \<in> \<real> \<longleftrightarrow> x \<in> \<real>"
by (metis Reals_inverse inverse_inverse_eq)

lemma nonzero_Reals_divide:
  fixes a b :: "'a::real_field"
  shows "\<lbrakk>a \<in> Reals; b \<in> Reals; b \<noteq> 0\<rbrakk> \<Longrightarrow> a / b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (erule nonzero_of_real_divide [symmetric])
done

lemma Reals_divide [simp]:
  fixes a b :: "'a::{real_field, field_inverse_zero}"
  shows "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a / b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_divide [symmetric])
done

lemma Reals_power [simp]:
  fixes a :: "'a::{real_algebra_1}"
  shows "a \<in> Reals \<Longrightarrow> a ^ n \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_power [symmetric])
done

lemma Reals_cases [cases set: Reals]:
  assumes "q \<in> \<real>"
  obtains (of_real) r where "q = of_real r"
  unfolding Reals_def
proof -
  from `q \<in> \<real>` have "q \<in> range of_real" unfolding Reals_def .
  then obtain r where "q = of_real r" ..
  then show thesis ..
qed

lemma setsum_in_Reals: assumes "\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>" shows "setsum f s \<in> \<real>"
proof (cases "finite s")
  case True then show ?thesis using assms
    by (induct s rule: finite_induct) auto
next
  case False then show ?thesis using assms
    by (metis Reals_0 setsum_infinite)
qed

lemma setprod_in_Reals: assumes "\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>" shows "setprod f s \<in> \<real>"
proof (cases "finite s")
  case True then show ?thesis using assms
    by (induct s rule: finite_induct) auto
next
  case False then show ?thesis using assms
    by (metis Reals_1 setprod_infinite)
qed

lemma Reals_induct [case_names of_real, induct set: Reals]:
  "q \<in> \<real> \<Longrightarrow> (\<And>r. P (of_real r)) \<Longrightarrow> P q"
  by (rule Reals_cases) auto

subsection {* Ordered real vector spaces *}

class ordered_real_vector = real_vector + ordered_ab_group_add +
  assumes scaleR_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>R x \<le> a *\<^sub>R y"
  assumes scaleR_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R x"
begin

lemma scaleR_mono:
  "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R y"
apply (erule scaleR_right_mono [THEN order_trans], assumption)
apply (erule scaleR_left_mono, assumption)
done

lemma scaleR_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R d"
  by (rule scaleR_mono) (auto intro: order.trans)

lemma pos_le_divideRI:
  assumes "0 < c"
  assumes "c *\<^sub>R a \<le> b"
  shows "a \<le> b /\<^sub>R c"
proof -
  from scaleR_left_mono[OF assms(2)] assms(1)
  have "c *\<^sub>R a /\<^sub>R c \<le> b /\<^sub>R c"
    by simp
  with assms show ?thesis
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
qed

lemma pos_le_divideR_eq:
  assumes "0 < c"
  shows "a \<le> b /\<^sub>R c \<longleftrightarrow> c *\<^sub>R a \<le> b"
proof rule
  assume "a \<le> b /\<^sub>R c"
  from scaleR_left_mono[OF this] assms
  have "c *\<^sub>R a \<le> c *\<^sub>R (b /\<^sub>R c)"
    by simp
  with assms show "c *\<^sub>R a \<le> b"
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
qed (rule pos_le_divideRI[OF assms])

lemma scaleR_image_atLeastAtMost:
  "c > 0 \<Longrightarrow> scaleR c ` {x..y} = {c *\<^sub>R x..c *\<^sub>R y}"
  apply (auto intro!: scaleR_left_mono)
  apply (rule_tac x = "inverse c *\<^sub>R xa" in image_eqI)
  apply (simp_all add: pos_le_divideR_eq[symmetric] scaleR_scaleR scaleR_one)
  done

end

lemma scaleR_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> (x::'a::ordered_real_vector) \<Longrightarrow> 0 \<le> a *\<^sub>R x"
  using scaleR_left_mono [of 0 x a]
  by simp

lemma scaleR_nonneg_nonpos: "0 \<le> a \<Longrightarrow> (x::'a::ordered_real_vector) \<le> 0 \<Longrightarrow> a *\<^sub>R x \<le> 0"
  using scaleR_left_mono [of x 0 a] by simp

lemma scaleR_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> (x::'a::ordered_real_vector) \<Longrightarrow> a *\<^sub>R x \<le> 0"
  using scaleR_right_mono [of a 0 x] by simp

lemma split_scaleR_neg_le: "(0 \<le> a & x \<le> 0) | (a \<le> 0 & 0 \<le> x) \<Longrightarrow>
  a *\<^sub>R (x::'a::ordered_real_vector) \<le> 0"
  by (auto simp add: scaleR_nonneg_nonpos scaleR_nonpos_nonneg)

lemma le_add_iff1:
  fixes c d e::"'a::ordered_real_vector"
  shows "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> (a - b) *\<^sub>R e + c \<le> d"
  by (simp add: algebra_simps)

lemma le_add_iff2:
  fixes c d e::"'a::ordered_real_vector"
  shows "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>R e + d"
  by (simp add: algebra_simps)

lemma scaleR_left_mono_neg:
  fixes a b::"'a::ordered_real_vector"
  shows "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b"
  apply (drule scaleR_left_mono [of _ _ "- c"])
  apply simp_all
  done

lemma scaleR_right_mono_neg:
  fixes c::"'a::ordered_real_vector"
  shows "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R c"
  apply (drule scaleR_right_mono [of _ _ "- c"])
  apply simp_all
  done

lemma scaleR_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> (b::'a::ordered_real_vector) \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>R b"
using scaleR_right_mono_neg [of a 0 b] by simp

lemma split_scaleR_pos_le:
  fixes b::"'a::ordered_real_vector"
  shows "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>R b"
  by (auto simp add: scaleR_nonneg_nonneg scaleR_nonpos_nonpos)

lemma zero_le_scaleR_iff:
  fixes b::"'a::ordered_real_vector"
  shows "0 \<le> a *\<^sub>R b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0" (is "?lhs = ?rhs")
proof cases
  assume "a \<noteq> 0"
  show ?thesis
  proof
    assume lhs: ?lhs
    {
      assume "0 < a"
      with lhs have "inverse a *\<^sub>R 0 \<le> inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      hence ?rhs using `0 < a`
        by simp
    } moreover {
      assume "0 > a"
      with lhs have "- inverse a *\<^sub>R 0 \<le> - inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      hence ?rhs using `0 > a`
        by simp
    } ultimately show ?rhs using `a \<noteq> 0` by arith
  qed (auto simp: not_le `a \<noteq> 0` intro!: split_scaleR_pos_le)
qed simp

lemma scaleR_le_0_iff:
  fixes b::"'a::ordered_real_vector"
  shows "a *\<^sub>R b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  by (insert zero_le_scaleR_iff [of "-a" b]) force

lemma scaleR_le_cancel_left:
  fixes b::"'a::ordered_real_vector"
  shows "c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (auto simp add: neq_iff scaleR_left_mono scaleR_left_mono_neg
    dest: scaleR_left_mono[where a="inverse c"] scaleR_left_mono_neg[where c="inverse c"])

lemma scaleR_le_cancel_left_pos:
  fixes b::"'a::ordered_real_vector"
  shows "0 < c \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> a \<le> b"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_le_cancel_left_neg:
  fixes b::"'a::ordered_real_vector"
  shows "c < 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> b \<le> a"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_left_le_one_le:
  fixes x::"'a::ordered_real_vector" and a::real
  shows "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>R x \<le> x"
  using scaleR_right_mono[of a 1 x] by simp


subsection {* Real normed vector spaces *}

class dist =
  fixes dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class norm =
  fixes norm :: "'a \<Rightarrow> real"

class sgn_div_norm = scaleR + norm + sgn +
  assumes sgn_div_norm: "sgn x = x /\<^sub>R norm x"

class dist_norm = dist + norm + minus +
  assumes dist_norm: "dist x y = norm (x - y)"

class open_dist = "open" + dist +
  assumes open_dist: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

class real_normed_vector = real_vector + sgn_div_norm + dist_norm + open_dist +
  assumes norm_eq_zero [simp]: "norm x = 0 \<longleftrightarrow> x = 0"
  and norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"
  and norm_scaleR [simp]: "norm (scaleR a x) = \<bar>a\<bar> * norm x"
begin

lemma norm_ge_zero [simp]: "0 \<le> norm x"
proof -
  have "0 = norm (x + -1 *\<^sub>R x)" 
    using scaleR_add_left[of 1 "-1" x] norm_scaleR[of 0 x] by (simp add: scaleR_one)
  also have "\<dots> \<le> norm x + norm (-1 *\<^sub>R x)" by (rule norm_triangle_ineq)
  finally show ?thesis by simp
qed

end

class real_normed_algebra = real_algebra + real_normed_vector +
  assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

class real_normed_algebra_1 = real_algebra_1 + real_normed_algebra +
  assumes norm_one [simp]: "norm 1 = 1"

class real_normed_div_algebra = real_div_algebra + real_normed_vector +
  assumes norm_mult: "norm (x * y) = norm x * norm y"

class real_normed_field = real_field + real_normed_div_algebra

instance real_normed_div_algebra < real_normed_algebra_1
proof
  fix x y :: 'a
  show "norm (x * y) \<le> norm x * norm y"
    by (simp add: norm_mult)
next
  have "norm (1 * 1::'a) = norm (1::'a) * norm (1::'a)"
    by (rule norm_mult)
  thus "norm (1::'a) = 1" by simp
qed

lemma norm_zero [simp]: "norm (0::'a::real_normed_vector) = 0"
by simp

lemma zero_less_norm_iff [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "(0 < norm x) = (x \<noteq> 0)"
by (simp add: order_less_le)

lemma norm_not_less_zero [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "\<not> norm x < 0"
by (simp add: linorder_not_less)

lemma norm_le_zero_iff [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "(norm x \<le> 0) = (x = 0)"
by (simp add: order_le_less)

lemma norm_minus_cancel [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "norm (- x) = norm x"
proof -
  have "norm (- x) = norm (scaleR (- 1) x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute:
  fixes a b :: "'a::real_normed_vector"
  shows "norm (a - b) = norm (b - a)"
proof -
  have "norm (- (b - a)) = norm (b - a)"
    by (rule norm_minus_cancel)
  thus ?thesis by simp
qed

lemma norm_triangle_ineq2:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a - b)"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  thus ?thesis by simp
qed

lemma norm_triangle_ineq3:
  fixes a b :: "'a::real_normed_vector"
  shows "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
apply (subst abs_le_iff)
apply auto
apply (rule norm_triangle_ineq2)
apply (subst norm_minus_commute)
apply (rule norm_triangle_ineq2)
done

lemma norm_triangle_ineq4:
  fixes a b :: "'a::real_normed_vector"
  shows "norm (a - b) \<le> norm a + norm b"
proof -
  have "norm (a + - b) \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  then show ?thesis by simp
qed

lemma norm_diff_ineq:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a + b)"
proof -
  have "norm a - norm (- b) \<le> norm (a - - b)"
    by (rule norm_triangle_ineq2)
  thus ?thesis by simp
qed

lemma norm_diff_triangle_ineq:
  fixes a b c d :: "'a::real_normed_vector"
  shows "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
proof -
  have "norm ((a + b) - (c + d)) = norm ((a - c) + (b - d))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> norm (a - c) + norm (b - d)"
    by (rule norm_triangle_ineq)
  finally show ?thesis .
qed

lemma norm_triangle_mono: 
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>norm a \<le> r; norm b \<le> s\<rbrakk> \<Longrightarrow> norm (a + b) \<le> r + s"
by (metis add_mono_thms_linordered_semiring(1) norm_triangle_ineq order.trans)

lemma norm_setsum:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "norm (setsum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
  by (induct A rule: infinite_finite_induct) (auto intro: norm_triangle_mono)

lemma setsum_norm_le:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fg: "\<forall>x \<in> S. norm (f x) \<le> g x"
  shows "norm (setsum f S) \<le> setsum g S"
  by (rule order_trans [OF norm_setsum setsum_mono]) (simp add: fg)

lemma abs_norm_cancel [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "\<bar>norm a\<bar> = norm a"
by (rule abs_of_nonneg [OF norm_ge_zero])

lemma norm_add_less:
  fixes x y :: "'a::real_normed_vector"
  shows "\<lbrakk>norm x < r; norm y < s\<rbrakk> \<Longrightarrow> norm (x + y) < r + s"
by (rule order_le_less_trans [OF norm_triangle_ineq add_strict_mono])

lemma norm_mult_less:
  fixes x y :: "'a::real_normed_algebra"
  shows "\<lbrakk>norm x < r; norm y < s\<rbrakk> \<Longrightarrow> norm (x * y) < r * s"
apply (rule order_le_less_trans [OF norm_mult_ineq])
apply (simp add: mult_strict_mono')
done

lemma norm_of_real [simp]:
  "norm (of_real r :: 'a::real_normed_algebra_1) = \<bar>r\<bar>"
unfolding of_real_def by simp

lemma norm_numeral [simp]:
  "norm (numeral w::'a::real_normed_algebra_1) = numeral w"
by (subst of_real_numeral [symmetric], subst norm_of_real, simp)

lemma norm_neg_numeral [simp]:
  "norm (- numeral w::'a::real_normed_algebra_1) = numeral w"
by (subst of_real_neg_numeral [symmetric], subst norm_of_real, simp)

lemma norm_of_int [simp]:
  "norm (of_int z::'a::real_normed_algebra_1) = \<bar>of_int z\<bar>"
by (subst of_real_of_int_eq [symmetric], rule norm_of_real)

lemma norm_of_nat [simp]:
  "norm (of_nat n::'a::real_normed_algebra_1) = of_nat n"
apply (subst of_real_of_nat_eq [symmetric])
apply (subst norm_of_real, simp)
done

lemma nonzero_norm_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
apply (rule inverse_unique [symmetric])
apply (simp add: norm_mult [symmetric])
done

lemma norm_inverse:
  fixes a :: "'a::{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "norm (inverse a) = inverse (norm a)"
apply (case_tac "a = 0", simp)
apply (erule nonzero_norm_inverse)
done

lemma nonzero_norm_divide:
  fixes a b :: "'a::real_normed_field"
  shows "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult nonzero_norm_inverse)

lemma norm_divide:
  fixes a b :: "'a::{real_normed_field, field_inverse_zero}"
  shows "norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult norm_inverse)

lemma norm_power_ineq:
  fixes x :: "'a::{real_normed_algebra_1}"
  shows "norm (x ^ n) \<le> norm x ^ n"
proof (induct n)
  case 0 show "norm (x ^ 0) \<le> norm x ^ 0" by simp
next
  case (Suc n)
  have "norm (x * x ^ n) \<le> norm x * norm (x ^ n)"
    by (rule norm_mult_ineq)
  also from Suc have "\<dots> \<le> norm x * norm x ^ n"
    using norm_ge_zero by (rule mult_left_mono)
  finally show "norm (x ^ Suc n) \<le> norm x ^ Suc n"
    by simp
qed

lemma norm_power:
  fixes x :: "'a::{real_normed_div_algebra}"
  shows "norm (x ^ n) = norm x ^ n"
by (induct n) (simp_all add: norm_mult)

lemma setprod_norm:
  fixes f :: "'a \<Rightarrow> 'b::{comm_semiring_1,real_normed_div_algebra}"
  shows "setprod (\<lambda>x. norm(f x)) A = norm (setprod f A)"
proof (cases "finite A")
  case True then show ?thesis 
    by (induct A rule: finite_induct) (auto simp: norm_mult)
next
  case False then show ?thesis
    by (metis norm_one setprod.infinite) 
qed


subsection {* Metric spaces *}

class metric_space = open_dist +
  assumes dist_eq_0_iff [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
  assumes dist_triangle2: "dist x y \<le> dist x z + dist y z"
begin

lemma dist_self [simp]: "dist x x = 0"
by simp

lemma zero_le_dist [simp]: "0 \<le> dist x y"
using dist_triangle2 [of x x y] by simp

lemma zero_less_dist_iff: "0 < dist x y \<longleftrightarrow> x \<noteq> y"
by (simp add: less_le)

lemma dist_not_less_zero [simp]: "\<not> dist x y < 0"
by (simp add: not_less)

lemma dist_le_zero_iff [simp]: "dist x y \<le> 0 \<longleftrightarrow> x = y"
by (simp add: le_less)

lemma dist_commute: "dist x y = dist y x"
proof (rule order_antisym)
  show "dist x y \<le> dist y x"
    using dist_triangle2 [of x y x] by simp
  show "dist y x \<le> dist x y"
    using dist_triangle2 [of y x y] by simp
qed

lemma dist_triangle: "dist x z \<le> dist x y + dist y z"
using dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma dist_triangle3: "dist x y \<le> dist a x + dist a y"
using dist_triangle2 [of x y a] by (simp add: dist_commute)

lemma dist_triangle_alt:
  shows "dist y z <= dist x y + dist x z"
by (rule dist_triangle3)

lemma dist_pos_lt:
  shows "x \<noteq> y ==> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_nz:
  shows "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_triangle_le:
  shows "dist x z + dist y z <= e \<Longrightarrow> dist x y <= e"
by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt:
  shows "dist x z + dist y z < e ==> dist x y < e"
by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_half_l:
  shows "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_lt [where z=y], simp)

lemma dist_triangle_half_r:
  shows "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_half_l, simp_all add: dist_commute)

subclass topological_space
proof
  have "\<exists>e::real. 0 < e"
    by (fast intro: zero_less_one)
  then show "open UNIV"
    unfolding open_dist by simp
next
  fix S T assume "open S" "open T"
  then show "open (S \<inter> T)"
    unfolding open_dist
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac r s)
    apply (rule_tac x="min r s" in exI, simp)
    done
next
  fix K assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_dist by fast
qed

lemma open_ball: "open {y. dist x y < d}"
proof (unfold open_dist, intro ballI)
  fix y assume *: "y \<in> {y. dist x y < d}"
  then show "\<exists>e>0. \<forall>z. dist z y < e \<longrightarrow> z \<in> {y. dist x y < d}"
    by (auto intro!: exI[of _ "d - dist x y"] simp: field_simps dist_triangle_lt)
qed

subclass first_countable_topology
proof
  fix x 
  show "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (safe intro!: exI[of _ "\<lambda>n. {y. dist x y < inverse (Suc n)}"])
    fix S assume "open S" "x \<in> S"
    then obtain e where e: "0 < e" and "{y. dist x y < e} \<subseteq> S"
      by (auto simp: open_dist subset_eq dist_commute)
    moreover
    from e obtain i where "inverse (Suc i) < e"
      by (auto dest!: reals_Archimedean)
    then have "{y. dist x y < inverse (Suc i)} \<subseteq> {y. dist x y < e}"
      by auto
    ultimately show "\<exists>i. {y. dist x y < inverse (Suc i)} \<subseteq> S"
      by blast
  qed (auto intro: open_ball)
qed

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "{y'. dist x y' < dist x y / 2}"
  let ?V = "{x'. dist y x' < dist x y / 2}"
  have th0: "\<And>d x y z. (d x z :: real) \<le> d x y + d y z \<Longrightarrow> d y z = d z y
               \<Longrightarrow> \<not>(d x y * 2 < d x z \<and> d z y * 2 < d x z)" by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] th0[of dist, OF dist_triangle dist_commute]
    using open_ball[of _ "dist x y / 2"] by auto
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

text {* Every normed vector space is a metric space. *}

instance real_normed_vector < metric_space
proof
  fix x y :: 'a show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_norm by simp
next
  fix x y z :: 'a show "dist x y \<le> dist x z + dist y z"
    unfolding dist_norm
    using norm_triangle_ineq4 [of "x - z" "y - z"] by simp
qed

subsection {* Class instances for real numbers *}

instantiation real :: real_normed_field
begin

definition dist_real_def:
  "dist x y = \<bar>x - y\<bar>"

definition open_real_def [code del]:
  "open (S :: real set) \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

definition real_norm_def [simp]:
  "norm r = \<bar>r\<bar>"

instance
apply (intro_classes, unfold real_norm_def real_scaleR_def)
apply (rule dist_real_def)
apply (rule open_real_def)
apply (simp add: sgn_real_def)
apply (rule abs_eq_0)
apply (rule abs_triangle_ineq)
apply (rule abs_mult)
apply (rule abs_mult)
done

end

declare [[code abort: "open :: real set \<Rightarrow> bool"]]

instance real :: linorder_topology
proof
  show "(open :: real set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"
  proof (rule ext, safe)
    fix S :: "real set" assume "open S"
    then obtain f where "\<forall>x\<in>S. 0 < f x \<and> (\<forall>y. dist y x < f x \<longrightarrow> y \<in> S)"
      unfolding open_real_def bchoice_iff ..
    then have *: "S = (\<Union>x\<in>S. {x - f x <..} \<inter> {..< x + f x})"
      by (fastforce simp: dist_real_def)
    show "generate_topology (range lessThan \<union> range greaterThan) S"
      apply (subst *)
      apply (intro generate_topology_Union generate_topology.Int)
      apply (auto intro: generate_topology.Basis)
      done
  next
    fix S :: "real set" assume "generate_topology (range lessThan \<union> range greaterThan) S"
    moreover have "\<And>a::real. open {..<a}"
      unfolding open_real_def dist_real_def
    proof clarify
      fix x a :: real assume "x < a"
      hence "0 < a - x \<and> (\<forall>y. \<bar>y - x\<bar> < a - x \<longrightarrow> y \<in> {..<a})" by auto
      thus "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {..<a}" ..
    qed
    moreover have "\<And>a::real. open {a <..}"
      unfolding open_real_def dist_real_def
    proof clarify
      fix x a :: real assume "a < x"
      hence "0 < x - a \<and> (\<forall>y. \<bar>y - x\<bar> < x - a \<longrightarrow> y \<in> {a<..})" by auto
      thus "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {a<..}" ..
    qed
    ultimately show "open S"
      by induct auto
  qed
qed

instance real :: linear_continuum_topology ..

lemmas open_real_greaterThan = open_greaterThan[where 'a=real]
lemmas open_real_lessThan = open_lessThan[where 'a=real]
lemmas open_real_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_real_atMost = closed_atMost[where 'a=real]
lemmas closed_real_atLeast = closed_atLeast[where 'a=real]
lemmas closed_real_atLeastAtMost = closed_atLeastAtMost[where 'a=real]

subsection {* Extra type constraints *}

text {* Only allow @{term "open"} in class @{text topological_space}. *}

setup {* Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::topological_space set \<Rightarrow> bool"}) *}

text {* Only allow @{term dist} in class @{text metric_space}. *}

setup {* Sign.add_const_constraint
  (@{const_name dist}, SOME @{typ "'a::metric_space \<Rightarrow> 'a \<Rightarrow> real"}) *}

text {* Only allow @{term norm} in class @{text real_normed_vector}. *}

setup {* Sign.add_const_constraint
  (@{const_name norm}, SOME @{typ "'a::real_normed_vector \<Rightarrow> real"}) *}

subsection {* Sign function *}

lemma norm_sgn:
  "norm (sgn(x::'a::real_normed_vector)) = (if x = 0 then 0 else 1)"
by (simp add: sgn_div_norm)

lemma sgn_zero [simp]: "sgn(0::'a::real_normed_vector) = 0"
by (simp add: sgn_div_norm)

lemma sgn_zero_iff: "(sgn(x::'a::real_normed_vector) = 0) = (x = 0)"
by (simp add: sgn_div_norm)

lemma sgn_minus: "sgn (- x) = - sgn(x::'a::real_normed_vector)"
by (simp add: sgn_div_norm)

lemma sgn_scaleR:
  "sgn (scaleR r x) = scaleR (sgn r) (sgn(x::'a::real_normed_vector))"
by (simp add: sgn_div_norm mult_ac)

lemma sgn_one [simp]: "sgn (1::'a::real_normed_algebra_1) = 1"
by (simp add: sgn_div_norm)

lemma sgn_of_real:
  "sgn (of_real r::'a::real_normed_algebra_1) = of_real (sgn r)"
unfolding of_real_def by (simp only: sgn_scaleR sgn_one)

lemma sgn_mult:
  fixes x y :: "'a::real_normed_div_algebra"
  shows "sgn (x * y) = sgn x * sgn y"
by (simp add: sgn_div_norm norm_mult mult_commute)

lemma real_sgn_eq: "sgn (x::real) = x / \<bar>x\<bar>"
by (simp add: sgn_div_norm divide_inverse)

lemma real_sgn_pos: "0 < (x::real) \<Longrightarrow> sgn x = 1"
unfolding real_sgn_eq by simp

lemma real_sgn_neg: "(x::real) < 0 \<Longrightarrow> sgn x = -1"
unfolding real_sgn_eq by simp

lemma zero_le_sgn_iff [simp]: "0 \<le> sgn x \<longleftrightarrow> 0 \<le> (x::real)"
  by (cases "0::real" x rule: linorder_cases) simp_all
  
lemma zero_less_sgn_iff [simp]: "0 < sgn x \<longleftrightarrow> 0 < (x::real)"
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma sgn_le_0_iff [simp]: "sgn x \<le> 0 \<longleftrightarrow> (x::real) \<le> 0"
  by (cases "0::real" x rule: linorder_cases) simp_all
  
lemma sgn_less_0_iff [simp]: "sgn x < 0 \<longleftrightarrow> (x::real) < 0"
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

subsection {* Bounded Linear and Bilinear Operators *}

locale linear = additive f for f :: "'a::real_vector \<Rightarrow> 'b::real_vector" +
  assumes scaleR: "f (scaleR r x) = scaleR r (f x)"

lemma linearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
  assumes "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "linear f"
  by default (rule assms)+

locale bounded_linear = linear f for f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

lemma pos_bounded:
  "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

lemma nonneg_bounded:
  "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  from pos_bounded
  show ?thesis by (auto intro: order_less_imp_le)
qed

lemma linear: "linear f" ..

end

lemma bounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
  assumes "\<And>r x. f (scaleR r x) = scaleR r (f x)"
  assumes "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  by default (fast intro: assms)+

locale bounded_bilinear =
  fixes prod :: "['a::real_normed_vector, 'b::real_normed_vector]
                 \<Rightarrow> 'c::real_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
  assumes add_right: "prod a (b + b') = prod a b + prod a b'"
  assumes scaleR_left: "prod (scaleR r a) b = scaleR r (prod a b)"
  assumes scaleR_right: "prod a (scaleR r b) = scaleR r (prod a b)"
  assumes bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

lemma pos_bounded:
  "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
apply (cut_tac bounded, erule exE)
apply (rule_tac x="max 1 K" in exI, safe)
apply (rule order_less_le_trans [OF zero_less_one max.cobounded1])
apply (drule spec, drule spec, erule order_trans)
apply (rule mult_left_mono [OF max.cobounded2])
apply (intro mult_nonneg_nonneg norm_ge_zero)
done

lemma nonneg_bounded:
  "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
proof -
  from pos_bounded
  show ?thesis by (auto intro: order_less_imp_le)
qed

lemma additive_right: "additive (\<lambda>b. prod a b)"
by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. prod a b)"
by (rule additive.intro, rule add_left)

lemma zero_left: "prod 0 b = 0"
by (rule additive.zero [OF additive_left])

lemma zero_right: "prod a 0 = 0"
by (rule additive.zero [OF additive_right])

lemma minus_left: "prod (- a) b = - prod a b"
by (rule additive.minus [OF additive_left])

lemma minus_right: "prod a (- b) = - prod a b"
by (rule additive.minus [OF additive_right])

lemma diff_left:
  "prod (a - a') b = prod a b - prod a' b"
by (rule additive.diff [OF additive_left])

lemma diff_right:
  "prod a (b - b') = prod a b - prod a b'"
by (rule additive.diff [OF additive_right])

lemma bounded_linear_left:
  "bounded_linear (\<lambda>a. a ** b)"
apply (cut_tac bounded, safe)
apply (rule_tac K="norm b * K" in bounded_linear_intro)
apply (rule add_left)
apply (rule scaleR_left)
apply (simp add: mult_ac)
done

lemma bounded_linear_right:
  "bounded_linear (\<lambda>b. a ** b)"
apply (cut_tac bounded, safe)
apply (rule_tac K="norm a * K" in bounded_linear_intro)
apply (rule add_right)
apply (rule scaleR_right)
apply (simp add: mult_ac)
done

lemma prod_diff_prod:
  "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
by (simp add: diff_left diff_right)

end

lemma bounded_linear_ident[simp]: "bounded_linear (\<lambda>x. x)"
  by default (auto intro!: exI[of _ 1])

lemma bounded_linear_zero[simp]: "bounded_linear (\<lambda>x. 0)"
  by default (auto intro!: exI[of _ 1])

lemma bounded_linear_add:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "\<And>x. norm (f x) \<le> norm x * Kf" by blast
    from g.bounded obtain Kg where Kg: "\<And>x. norm (g x) \<le> norm x * Kg" by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleR g.scaleR scaleR_right_distrib)
qed

lemma bounded_linear_minus:
  assumes "bounded_linear f"
  shows "bounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis apply (unfold_locales)
    apply (simp add: f.add)
    apply (simp add: f.scaleR)
    apply (simp add: f.bounded)
    done
qed

lemma bounded_linear_compose:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis proof (unfold_locales)
    fix x y show "f (g (x + y)) = f (g x) + f (g y)"
      by (simp only: f.add g.add)
  next
    fix r x show "f (g (scaleR r x)) = scaleR r (f (g x))"
      by (simp only: f.scaleR g.scaleR)
  next
    from f.pos_bounded
    obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf" by fast
    from g.pos_bounded
    obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg" by fast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult_assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_bilinear_mult:
  "bounded_bilinear (op * :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::real_normed_algebra)"
apply (rule bounded_bilinear.intro)
apply (rule distrib_right)
apply (rule distrib_left)
apply (rule mult_scaleR_left)
apply (rule mult_scaleR_right)
apply (rule_tac x="1" in exI)
apply (simp add: norm_mult_ineq)
done

lemma bounded_linear_mult_left:
  "bounded_linear (\<lambda>x::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_mult_right:
  "bounded_linear (\<lambda>y::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_linear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma bounded_linear_divide:
  "bounded_linear (\<lambda>x::'a::real_normed_field. x / y)"
  unfolding divide_inverse by (rule bounded_linear_mult_left)

lemma bounded_bilinear_scaleR: "bounded_bilinear scaleR"
apply (rule bounded_bilinear.intro)
apply (rule scaleR_left_distrib)
apply (rule scaleR_right_distrib)
apply simp
apply (rule scaleR_left_commute)
apply (rule_tac x="1" in exI, simp)
done

lemma bounded_linear_scaleR_left: "bounded_linear (\<lambda>r. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_scaleR_right: "bounded_linear (\<lambda>x. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_right)

lemma bounded_linear_of_real: "bounded_linear (\<lambda>r. of_real r)"
  unfolding of_real_def by (rule bounded_linear_scaleR_left)

lemma real_bounded_linear:
  fixes f :: "real \<Rightarrow> real"
  shows "bounded_linear f \<longleftrightarrow> (\<exists>c::real. f = (\<lambda>x. x * c))"
proof -
  { fix x assume "bounded_linear f"
    then interpret bounded_linear f .
    from scaleR[of x 1] have "f x = x * f 1"
      by simp }
  then show ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_linear_mult_left)
qed

instance real_normed_algebra_1 \<subseteq> perfect_space
proof
  fix x::'a
  show "\<not> open {x}"
    unfolding open_dist dist_norm
    by (clarsimp, rule_tac x="x + of_real (e/2)" in exI, simp)
qed

subsection {* Filters and Limits on Metric Space *}

lemma eventually_nhds_metric:
  fixes a :: "'a :: metric_space"
  shows "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
unfolding eventually_nhds open_dist
apply safe
apply fast
apply (rule_tac x="{x. dist x a < d}" in exI, simp)
apply clarsimp
apply (rule_tac x="d - dist x a" in exI, clarsimp)
apply (simp only: less_diff_eq)
apply (erule le_less_trans [OF dist_triangle])
done

lemma eventually_at:
  fixes a :: "'a :: metric_space"
  shows "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
  unfolding eventually_at_filter eventually_nhds_metric by (auto simp: dist_nz)

lemma eventually_at_le:
  fixes a :: "'a::metric_space"
  shows "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a \<le> d \<longrightarrow> P x)"
  unfolding eventually_at_filter eventually_nhds_metric
  apply auto
  apply (rule_tac x="d / 2" in exI)
  apply auto
  done

lemma tendstoI:
  fixes l :: "'a :: metric_space"
  assumes "\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  shows "(f ---> l) F"
  apply (rule topological_tendstoI)
  apply (simp add: open_dist)
  apply (drule (1) bspec, clarify)
  apply (drule assms)
  apply (erule eventually_elim1, simp)
  done

lemma tendstoD:
  fixes l :: "'a :: metric_space"
  shows "(f ---> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  apply (drule_tac S="{x. dist x l < e}" in topological_tendstoD)
  apply (clarsimp simp add: open_dist)
  apply (rule_tac x="e - dist x l" in exI, clarsimp)
  apply (simp only: less_diff_eq)
  apply (erule le_less_trans [OF dist_triangle])
  apply simp
  apply simp
  done

lemma tendsto_iff:
  fixes l :: "'a :: metric_space"
  shows "(f ---> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  using tendstoI tendstoD by fast

lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space" and b :: "'b :: metric_space"
  assumes f: "(f ---> a) F"
  assumes le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g ---> b) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

lemma filterlim_real_sequentially: "LIM x sequentially. real x :> at_top"
  unfolding filterlim_at_top
  apply (intro allI)
  apply (rule_tac c="natceiling (Z + 1)" in eventually_sequentiallyI)
  apply (auto simp: natceiling_le_eq)
  done

subsubsection {* Limits of Sequences *}

lemma LIMSEQ_def: "X ----> (L::'a::metric_space) \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  unfolding tendsto_iff eventually_sequentially ..

lemma LIMSEQ_iff_nz: "X ----> (L::'a::metric_space) = (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  unfolding LIMSEQ_def by (metis Suc_leD zero_less_Suc)

lemma metric_LIMSEQ_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X ----> (L::'a::metric_space)"
by (simp add: LIMSEQ_def)

lemma metric_LIMSEQ_D:
  "\<lbrakk>X ----> (L::'a::metric_space); 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
by (simp add: LIMSEQ_def)


subsubsection {* Limits of Functions *}

lemma LIM_def: "f -- (a::'a::metric_space) --> (L::'b::metric_space) =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & dist x a < s
        --> dist (f x) L < r)"
  unfolding tendsto_iff eventually_at by simp

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)
    \<Longrightarrow> f -- (a::'a::metric_space) --> (L::'b::metric_space)"
by (simp add: LIM_def)

lemma metric_LIM_D:
  "\<lbrakk>f -- (a::'a::metric_space) --> (L::'b::metric_space); 0 < r\<rbrakk>
    \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
by (simp add: LIM_def)

lemma metric_LIM_imp_LIM:
  assumes f: "f -- a --> (l::'a::metric_space)"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g -- a --> (m::'b::metric_space)"
  by (rule metric_tendsto_imp_tendsto [OF f]) (auto simp add: eventually_at_topological le)

lemma metric_LIM_equal2:
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; dist x a < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- (a::'a::metric_space) --> l"
apply (rule topological_tendstoI)
apply (drule (2) topological_tendstoD)
apply (simp add: eventually_at, safe)
apply (rule_tac x="min d R" in exI, safe)
apply (simp add: 1)
apply (simp add: 2)
done

lemma metric_LIM_compose2:
  assumes f: "f -- (a::'a::metric_space) --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
  using inj
  by (intro tendsto_compose_eventually[OF g f]) (auto simp: eventually_at)

lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule metric_LIM_compose2 [OF f g inj])

subsection {* Complete metric spaces *}

subsection {* Cauchy sequences *}

definition (in metric_space) Cauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < e)"

subsection {* Cauchy Sequences *}

lemma metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  by (simp add: Cauchy_def)

lemma metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
  by (simp add: Cauchy_def)

lemma metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))"
apply (simp add: Cauchy_def, auto)
apply (drule reals_Archimedean, safe)
apply (drule_tac x = n in spec, auto)
apply (rule_tac x = M in exI, auto)
apply (drule_tac x = m in spec, simp)
apply (drule_tac x = na in spec, auto)
done

lemma Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse(real (Suc j))))"
  unfolding metric_Cauchy_iff2 dist_real_def ..

lemma Cauchy_subseq_Cauchy:
  "\<lbrakk> Cauchy X; subseq f \<rbrakk> \<Longrightarrow> Cauchy (X o f)"
apply (auto simp add: Cauchy_def)
apply (drule_tac x=e in spec, clarify)
apply (rule_tac x=M in exI, clarify)
apply (blast intro: le_trans [OF _ seq_suble] dest!: spec)
done

theorem LIMSEQ_imp_Cauchy:
  assumes X: "X ----> a" shows "Cauchy X"
proof (rule metric_CauchyI)
  fix e::real assume "0 < e"
  hence "0 < e/2" by simp
  with X have "\<exists>N. \<forall>n\<ge>N. dist (X n) a < e/2" by (rule metric_LIMSEQ_D)
  then obtain N where N: "\<forall>n\<ge>N. dist (X n) a < e/2" ..
  show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < e"
  proof (intro exI allI impI)
    fix m assume "N \<le> m"
    hence m: "dist (X m) a < e/2" using N by fast
    fix n assume "N \<le> n"
    hence n: "dist (X n) a < e/2" using N by fast
    have "dist (X m) (X n) \<le> dist (X m) a + dist (X n) a"
      by (rule dist_triangle2)
    also from m n have "\<dots> < e" by simp
    finally show "dist (X m) (X n) < e" .
  qed
qed

lemma convergent_Cauchy: "convergent X \<Longrightarrow> Cauchy X"
unfolding convergent_def
by (erule exE, erule LIMSEQ_imp_Cauchy)

subsubsection {* Cauchy Sequences are Convergent *}

class complete_space = metric_space +
  assumes Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

lemma Cauchy_convergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::complete_space"
  shows "Cauchy X = convergent X"
by (fast intro: Cauchy_convergent convergent_Cauchy)

subsection {* The set of real numbers is a complete metric space *}

text {*
Proof that Cauchy sequences converge based on the one from
@{url "http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html"}
*}

text {*
  If sequence @{term "X"} is Cauchy, then its limit is the lub of
  @{term "{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}"}
*}

lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
      and bdd: "\<And>n. f n \<le> l"
      and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f ----> l"
proof (rule increasing_tendsto)
  fix x assume "x < l"
  with dense[of 0 "l - x"] obtain e where "0 < e" "e < l - x"
    by auto
  from en[OF `0 < e`] obtain n where "l - e \<le> f n"
    by (auto simp: field_simps)
  with `e < l - x` `0 < e` have "x < f n" by simp
  with incseq_SucI[of f, OF inc] show "eventually (\<lambda>n. x < f n) sequentially"
    by (auto simp: eventually_sequentially incseq_def intro: less_le_trans)
qed (insert bdd, auto)

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  shows "convergent X"
proof -
  def S \<equiv> "{x::real. \<exists>N. \<forall>n\<ge>N. x < X n}"
  then have mem_S: "\<And>N x. \<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S" by auto

  { fix N x assume N: "\<forall>n\<ge>N. X n < x"
  fix y::real assume "y \<in> S"
  hence "\<exists>M. \<forall>n\<ge>M. y < X n"
    by (simp add: S_def)
  then obtain M where "\<forall>n\<ge>M. y < X n" ..
  hence "y < X (max M N)" by simp
  also have "\<dots> < x" using N by simp
  finally have "y \<le> x"
    by (rule order_less_imp_le) }
  note bound_isUb = this 

  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < 1"
    using X[THEN metric_CauchyD, OF zero_less_one] by auto
  hence N: "\<forall>n\<ge>N. dist (X n) (X N) < 1" by simp
  have [simp]: "S \<noteq> {}"
  proof (intro exI ex_in_conv[THEN iffD1])
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff dist_real_def)
    thus "X N - 1 \<in> S" by (rule mem_S)
  qed
  have [simp]: "bdd_above S"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff dist_real_def)
    thus "\<And>s. s \<in> S \<Longrightarrow>  s \<le> X N + 1"
      by (rule bound_isUb)
  qed
  have "X ----> Sup S"
  proof (rule metric_LIMSEQ_I)
  fix r::real assume "0 < r"
  hence r: "0 < r/2" by simp
  obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (X n) (X m) < r/2"
    using metric_CauchyD [OF X r] by auto
  hence "\<forall>n\<ge>N. dist (X n) (X N) < r/2" by simp
  hence N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
    by (simp only: dist_real_def abs_diff_less_iff)

  from N have "\<forall>n\<ge>N. X N - r/2 < X n" by fast
  hence "X N - r/2 \<in> S" by (rule mem_S)
  hence 1: "X N - r/2 \<le> Sup S" by (simp add: cSup_upper)

  from N have "\<forall>n\<ge>N. X n < X N + r/2" by fast
  from bound_isUb[OF this]
  have 2: "Sup S \<le> X N + r/2"
    by (intro cSup_least) simp_all

  show "\<exists>N. \<forall>n\<ge>N. dist (X n) (Sup S) < r"
  proof (intro exI allI impI)
    fix n assume n: "N \<le> n"
    from N n have "X n < X N + r/2" and "X N - r/2 < X n" by simp+
    thus "dist (X n) (Sup S) < r" using 1 2
      by (simp add: abs_diff_less_iff dist_real_def)
  qed
  qed
  then show ?thesis unfolding convergent_def by auto
qed

instance real :: complete_space
  by intro_classes (rule real_Cauchy_convergent)

class banach = real_normed_vector + complete_space

instance real :: banach by default

lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
  assumes limseq: "(\<lambda>n. f (real n)) ----> y"
  shows "(f ---> y) at_top"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  with limseq obtain N :: nat where N: "\<And>n. N \<le> n \<Longrightarrow> \<bar>f (real n) - y\<bar> < e"
    by (auto simp: LIMSEQ_def dist_real_def)
  { fix x :: real
    obtain n where "x \<le> real_of_nat n"
      using ex_le_of_nat[of x] ..
    note monoD[OF mono this]
    also have "f (real_of_nat n) \<le> y"
      by (rule LIMSEQ_le_const[OF limseq])
         (auto intro: exI[of _ n] monoD[OF mono] simp: real_eq_of_nat[symmetric])
    finally have "f x \<le> y" . }
  note le = this
  have "eventually (\<lambda>x. real N \<le> x) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>x. dist (f x) y < e) at_top"
  proof eventually_elim
    fix x assume N': "real N \<le> x"
    with N[of N] le have "y - f (real N) < e" by auto
    moreover note monoD[OF mono N']
    ultimately show "dist (f x) y < e"
      using le[of x] by (auto simp: dist_real_def field_simps)
  qed
qed

end

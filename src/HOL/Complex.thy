(*  Title:       Complex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header {* Complex Numbers: Rectangular and Polar Representations *}

theory Complex
imports Transcendental
begin

datatype complex = Complex real real

primrec
  Re :: "complex \<Rightarrow> real"
where
  Re: "Re (Complex x y) = x"

primrec
  Im :: "complex \<Rightarrow> real"
where
  Im: "Im (Complex x y) = y"

lemma complex_surj [simp]: "Complex (Re z) (Im z) = z"
  by (induct z) simp

lemma complex_equality [intro?]: "\<lbrakk>Re x = Re y; Im x = Im y\<rbrakk> \<Longrightarrow> x = y"
  by (induct x, induct y) simp

lemma expand_complex_eq: "x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y"
  by (induct x, induct y) simp

lemmas complex_Re_Im_cancel_iff = expand_complex_eq


subsection {* Addition and Subtraction *}

instantiation complex :: ab_group_add
begin

definition
  complex_zero_def: "0 = Complex 0 0"

definition
  complex_add_def: "x + y = Complex (Re x + Re y) (Im x + Im y)"

definition
  complex_minus_def: "- x = Complex (- Re x) (- Im x)"

definition
  complex_diff_def: "x - (y\<Colon>complex) = x + - y"

lemma Complex_eq_0 [simp]: "Complex a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (simp add: complex_zero_def)

lemma complex_Re_zero [simp]: "Re 0 = 0"
  by (simp add: complex_zero_def)

lemma complex_Im_zero [simp]: "Im 0 = 0"
  by (simp add: complex_zero_def)

lemma complex_add [simp]:
  "Complex a b + Complex c d = Complex (a + c) (b + d)"
  by (simp add: complex_add_def)

lemma complex_Re_add [simp]: "Re (x + y) = Re x + Re y"
  by (simp add: complex_add_def)

lemma complex_Im_add [simp]: "Im (x + y) = Im x + Im y"
  by (simp add: complex_add_def)

lemma complex_minus [simp]:
  "- (Complex a b) = Complex (- a) (- b)"
  by (simp add: complex_minus_def)

lemma complex_Re_minus [simp]: "Re (- x) = - Re x"
  by (simp add: complex_minus_def)

lemma complex_Im_minus [simp]: "Im (- x) = - Im x"
  by (simp add: complex_minus_def)

lemma complex_diff [simp]:
  "Complex a b - Complex c d = Complex (a - c) (b - d)"
  by (simp add: complex_diff_def)

lemma complex_Re_diff [simp]: "Re (x - y) = Re x - Re y"
  by (simp add: complex_diff_def)

lemma complex_Im_diff [simp]: "Im (x - y) = Im x - Im y"
  by (simp add: complex_diff_def)

instance
  by intro_classes (simp_all add: complex_add_def complex_diff_def)

end



subsection {* Multiplication and Division *}

instantiation complex :: "{field, division_by_zero}"
begin

definition
  complex_one_def: "1 = Complex 1 0"

definition
  complex_mult_def: "x * y =
    Complex (Re x * Re y - Im x * Im y) (Re x * Im y + Im x * Re y)"

definition
  complex_inverse_def: "inverse x =
    Complex (Re x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)) (- Im x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>))"

definition
  complex_divide_def: "x / (y\<Colon>complex) = x * inverse y"

lemma Complex_eq_1 [simp]: "(Complex a b = 1) = (a = 1 \<and> b = 0)"
  by (simp add: complex_one_def)

lemma complex_Re_one [simp]: "Re 1 = 1"
  by (simp add: complex_one_def)

lemma complex_Im_one [simp]: "Im 1 = 0"
  by (simp add: complex_one_def)

lemma complex_mult [simp]:
  "Complex a b * Complex c d = Complex (a * c - b * d) (a * d + b * c)"
  by (simp add: complex_mult_def)

lemma complex_Re_mult [simp]: "Re (x * y) = Re x * Re y - Im x * Im y"
  by (simp add: complex_mult_def)

lemma complex_Im_mult [simp]: "Im (x * y) = Re x * Im y + Im x * Re y"
  by (simp add: complex_mult_def)

lemma complex_inverse [simp]:
  "inverse (Complex a b) = Complex (a / (a\<twosuperior> + b\<twosuperior>)) (- b / (a\<twosuperior> + b\<twosuperior>))"
  by (simp add: complex_inverse_def)

lemma complex_Re_inverse:
  "Re (inverse x) = Re x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)"
  by (simp add: complex_inverse_def)

lemma complex_Im_inverse:
  "Im (inverse x) = - Im x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)"
  by (simp add: complex_inverse_def)

instance
  by intro_classes (simp_all add: complex_mult_def
  right_distrib left_distrib right_diff_distrib left_diff_distrib
  complex_inverse_def complex_divide_def
  power2_eq_square add_divide_distrib [symmetric]
  expand_complex_eq)

end


subsection {* Numerals and Arithmetic *}

instantiation complex :: number_ring
begin

definition number_of_complex where
  complex_number_of_def: "number_of w = (of_int w \<Colon> complex)"

instance
  by intro_classes (simp only: complex_number_of_def)

end

lemma complex_Re_of_nat [simp]: "Re (of_nat n) = of_nat n"
by (induct n) simp_all

lemma complex_Im_of_nat [simp]: "Im (of_nat n) = 0"
by (induct n) simp_all

lemma complex_Re_of_int [simp]: "Re (of_int z) = of_int z"
by (cases z rule: int_diff_cases) simp

lemma complex_Im_of_int [simp]: "Im (of_int z) = 0"
by (cases z rule: int_diff_cases) simp

lemma complex_Re_number_of [simp]: "Re (number_of v) = number_of v"
unfolding number_of_eq by (rule complex_Re_of_int)

lemma complex_Im_number_of [simp]: "Im (number_of v) = 0"
unfolding number_of_eq by (rule complex_Im_of_int)

lemma Complex_eq_number_of [simp]:
  "(Complex a b = number_of w) = (a = number_of w \<and> b = 0)"
by (simp add: expand_complex_eq)


subsection {* Scalar Multiplication *}

instantiation complex :: real_field
begin

definition
  complex_scaleR_def: "scaleR r x = Complex (r * Re x) (r * Im x)"

lemma complex_scaleR [simp]:
  "scaleR r (Complex a b) = Complex (r * a) (r * b)"
  unfolding complex_scaleR_def by simp

lemma complex_Re_scaleR [simp]: "Re (scaleR r x) = r * Re x"
  unfolding complex_scaleR_def by simp

lemma complex_Im_scaleR [simp]: "Im (scaleR r x) = r * Im x"
  unfolding complex_scaleR_def by simp

instance
proof
  fix a b :: real and x y :: complex
  show "scaleR a (x + y) = scaleR a x + scaleR a y"
    by (simp add: expand_complex_eq right_distrib)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: expand_complex_eq left_distrib)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: expand_complex_eq mult_assoc)
  show "scaleR 1 x = x"
    by (simp add: expand_complex_eq)
  show "scaleR a x * y = scaleR a (x * y)"
    by (simp add: expand_complex_eq algebra_simps)
  show "x * scaleR a y = scaleR a (x * y)"
    by (simp add: expand_complex_eq algebra_simps)
qed

end


subsection{* Properties of Embedding from Reals *}

abbreviation
  complex_of_real :: "real \<Rightarrow> complex" where
    "complex_of_real \<equiv> of_real"

lemma complex_of_real_def: "complex_of_real r = Complex r 0"
by (simp add: of_real_def complex_scaleR_def)

lemma Re_complex_of_real [simp]: "Re (complex_of_real z) = z"
by (simp add: complex_of_real_def)

lemma Im_complex_of_real [simp]: "Im (complex_of_real z) = 0"
by (simp add: complex_of_real_def)

lemma Complex_add_complex_of_real [simp]:
     "Complex x y + complex_of_real r = Complex (x+r) y"
by (simp add: complex_of_real_def)

lemma complex_of_real_add_Complex [simp]:
     "complex_of_real r + Complex x y = Complex (r+x) y"
by (simp add: complex_of_real_def)

lemma Complex_mult_complex_of_real:
     "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
by (simp add: complex_of_real_def)

lemma complex_of_real_mult_Complex:
     "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
by (simp add: complex_of_real_def)


subsection {* Vector Norm *}

instantiation complex :: real_normed_field
begin

definition complex_norm_def:
  "norm z = sqrt ((Re z)\<twosuperior> + (Im z)\<twosuperior>)"

abbreviation
  cmod :: "complex \<Rightarrow> real" where
  "cmod \<equiv> norm"

definition complex_sgn_def:
  "sgn x = x /\<^sub>R cmod x"

definition dist_complex_def:
  "dist x y = cmod (x - y)"

definition topo_complex_def:
  "topo = {S::complex set. \<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S}"

lemmas cmod_def = complex_norm_def

lemma complex_norm [simp]: "cmod (Complex x y) = sqrt (x\<twosuperior> + y\<twosuperior>)"
  by (simp add: complex_norm_def)

instance proof
  fix r :: real and x y :: complex
  show "0 \<le> norm x"
    by (induct x) simp
  show "(norm x = 0) = (x = 0)"
    by (induct x) simp
  show "norm (x + y) \<le> norm x + norm y"
    by (induct x, induct y)
       (simp add: real_sqrt_sum_squares_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (induct x)
       (simp add: power_mult_distrib right_distrib [symmetric] real_sqrt_mult)
  show "norm (x * y) = norm x * norm y"
    by (induct x, induct y)
       (simp add: real_sqrt_mult [symmetric] power2_eq_square algebra_simps)
  show "sgn x = x /\<^sub>R cmod x"
    by (rule complex_sgn_def)
  show "dist x y = cmod (x - y)"
    by (rule dist_complex_def)
  show "topo = {S::complex set. \<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S}"
    by (rule topo_complex_def)
qed

end

lemma cmod_unit_one [simp]: "cmod (Complex (cos a) (sin a)) = 1"
by simp

lemma cmod_complex_polar [simp]:
     "cmod (complex_of_real r * Complex (cos a) (sin a)) = abs r"
by (simp add: norm_mult)

lemma complex_Re_le_cmod: "Re x \<le> cmod x"
unfolding complex_norm_def
by (rule real_sqrt_sum_squares_ge1)

lemma complex_mod_minus_le_complex_mod [simp]: "- cmod x \<le> cmod x"
by (rule order_trans [OF _ norm_ge_zero], simp)

lemma complex_mod_triangle_ineq2 [simp]: "cmod(b + a) - cmod b \<le> cmod a"
by (rule ord_le_eq_trans [OF norm_triangle_ineq2], simp)

lemmas real_sum_squared_expand = power2_sum [where 'a=real]

lemma abs_Re_le_cmod: "\<bar>Re x\<bar> \<le> cmod x"
by (cases x) simp

lemma abs_Im_le_cmod: "\<bar>Im x\<bar> \<le> cmod x"
by (cases x) simp

subsection {* Completeness of the Complexes *}

interpretation Re: bounded_linear "Re"
apply (unfold_locales, simp, simp)
apply (rule_tac x=1 in exI)
apply (simp add: complex_norm_def)
done

interpretation Im: bounded_linear "Im"
apply (unfold_locales, simp, simp)
apply (rule_tac x=1 in exI)
apply (simp add: complex_norm_def)
done

lemma LIMSEQ_Complex:
  "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. Complex (X n) (Y n)) ----> Complex a b"
apply (rule LIMSEQ_I)
apply (subgoal_tac "0 < r / sqrt 2")
apply (drule_tac r="r / sqrt 2" in LIMSEQ_D, safe)
apply (drule_tac r="r / sqrt 2" in LIMSEQ_D, safe)
apply (rename_tac M N, rule_tac x="max M N" in exI, safe)
apply (simp add: real_sqrt_sum_squares_less)
apply (simp add: divide_pos_pos)
done

instance complex :: banach
proof
  fix X :: "nat \<Rightarrow> complex"
  assume X: "Cauchy X"
  from Re.Cauchy [OF X] have 1: "(\<lambda>n. Re (X n)) ----> lim (\<lambda>n. Re (X n))"
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  from Im.Cauchy [OF X] have 2: "(\<lambda>n. Im (X n)) ----> lim (\<lambda>n. Im (X n))"
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X ----> Complex (lim (\<lambda>n. Re (X n))) (lim (\<lambda>n. Im (X n)))"
    using LIMSEQ_Complex [OF 1 2] by simp
  thus "convergent X"
    by (rule convergentI)
qed


subsection {* The Complex Number @{term "\<i>"} *}

definition
  "ii" :: complex  ("\<i>") where
  i_def: "ii \<equiv> Complex 0 1"

lemma complex_Re_i [simp]: "Re ii = 0"
by (simp add: i_def)

lemma complex_Im_i [simp]: "Im ii = 1"
by (simp add: i_def)

lemma Complex_eq_i [simp]: "(Complex x y = ii) = (x = 0 \<and> y = 1)"
by (simp add: i_def)

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
by (simp add: expand_complex_eq)

lemma complex_i_not_one [simp]: "ii \<noteq> 1"
by (simp add: expand_complex_eq)

lemma complex_i_not_number_of [simp]: "ii \<noteq> number_of w"
by (simp add: expand_complex_eq)

lemma i_mult_Complex [simp]: "ii * Complex a b = Complex (- b) a"
by (simp add: expand_complex_eq)

lemma Complex_mult_i [simp]: "Complex a b * ii = Complex (- b) a"
by (simp add: expand_complex_eq)

lemma i_complex_of_real [simp]: "ii * complex_of_real r = Complex 0 r"
by (simp add: i_def complex_of_real_def)

lemma complex_of_real_i [simp]: "complex_of_real r * ii = Complex 0 r"
by (simp add: i_def complex_of_real_def)

lemma i_squared [simp]: "ii * ii = -1"
by (simp add: i_def)

lemma power2_i [simp]: "ii\<twosuperior> = -1"
by (simp add: power2_eq_square)

lemma inverse_i [simp]: "inverse ii = - ii"
by (rule inverse_unique, simp)


subsection {* Complex Conjugation *}

definition
  cnj :: "complex \<Rightarrow> complex" where
  "cnj z = Complex (Re z) (- Im z)"

lemma complex_cnj [simp]: "cnj (Complex a b) = Complex a (- b)"
by (simp add: cnj_def)

lemma complex_Re_cnj [simp]: "Re (cnj x) = Re x"
by (simp add: cnj_def)

lemma complex_Im_cnj [simp]: "Im (cnj x) = - Im x"
by (simp add: cnj_def)

lemma complex_cnj_cancel_iff [simp]: "(cnj x = cnj y) = (x = y)"
by (simp add: expand_complex_eq)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
by (simp add: cnj_def)

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
by (simp add: expand_complex_eq)

lemma complex_cnj_zero_iff [iff]: "(cnj z = 0) = (z = 0)"
by (simp add: expand_complex_eq)

lemma complex_cnj_add: "cnj (x + y) = cnj x + cnj y"
by (simp add: expand_complex_eq)

lemma complex_cnj_diff: "cnj (x - y) = cnj x - cnj y"
by (simp add: expand_complex_eq)

lemma complex_cnj_minus: "cnj (- x) = - cnj x"
by (simp add: expand_complex_eq)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
by (simp add: expand_complex_eq)

lemma complex_cnj_mult: "cnj (x * y) = cnj x * cnj y"
by (simp add: expand_complex_eq)

lemma complex_cnj_inverse: "cnj (inverse x) = inverse (cnj x)"
by (simp add: complex_inverse_def)

lemma complex_cnj_divide: "cnj (x / y) = cnj x / cnj y"
by (simp add: complex_divide_def complex_cnj_mult complex_cnj_inverse)

lemma complex_cnj_power: "cnj (x ^ n) = cnj x ^ n"
by (induct n, simp_all add: complex_cnj_mult)

lemma complex_cnj_of_nat [simp]: "cnj (of_nat n) = of_nat n"
by (simp add: expand_complex_eq)

lemma complex_cnj_of_int [simp]: "cnj (of_int z) = of_int z"
by (simp add: expand_complex_eq)

lemma complex_cnj_number_of [simp]: "cnj (number_of w) = number_of w"
by (simp add: expand_complex_eq)

lemma complex_cnj_scaleR: "cnj (scaleR r x) = scaleR r (cnj x)"
by (simp add: expand_complex_eq)

lemma complex_mod_cnj [simp]: "cmod (cnj z) = cmod z"
by (simp add: complex_norm_def)

lemma complex_cnj_complex_of_real [simp]: "cnj (of_real x) = of_real x"
by (simp add: expand_complex_eq)

lemma complex_cnj_i [simp]: "cnj ii = - ii"
by (simp add: expand_complex_eq)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re z)"
by (simp add: expand_complex_eq)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im z) * ii"
by (simp add: expand_complex_eq)

lemma complex_mult_cnj: "z * cnj z = complex_of_real ((Re z)\<twosuperior> + (Im z)\<twosuperior>)"
by (simp add: expand_complex_eq power2_eq_square)

lemma complex_mod_mult_cnj: "cmod (z * cnj z) = (cmod z)\<twosuperior>"
by (simp add: norm_mult power2_eq_square)

interpretation cnj: bounded_linear "cnj"
apply (unfold_locales)
apply (rule complex_cnj_add)
apply (rule complex_cnj_scaleR)
apply (rule_tac x=1 in exI, simp)
done


subsection{*The Functions @{term sgn} and @{term arg}*}

text {*------------ Argand -------------*}

definition
  arg :: "complex => real" where
  "arg z = (SOME a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a \<le> pi)"

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
by (simp add: complex_sgn_def divide_inverse scaleR_conv_of_real mult_commute)

lemma i_mult_eq: "ii * ii = complex_of_real (-1)"
by (simp add: i_def complex_of_real_def)

lemma i_mult_eq2 [simp]: "ii * ii = -(1::complex)"
by (simp add: i_def complex_one_def)

lemma complex_eq_cancel_iff2 [simp]:
     "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
by (simp add: complex_of_real_def)

lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
by (simp add: complex_sgn_def divide_inverse)

lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
by (simp add: complex_sgn_def divide_inverse)

lemma complex_inverse_complex_split:
     "inverse(complex_of_real x + ii * complex_of_real y) =
      complex_of_real(x/(x ^ 2 + y ^ 2)) -
      ii * complex_of_real(y/(x ^ 2 + y ^ 2))"
by (simp add: complex_of_real_def i_def diff_minus divide_inverse)

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

lemma cos_arg_i_mult_zero_pos:
   "0 < y ==> cos (arg(Complex 0 y)) = 0"
apply (simp add: arg_def abs_if)
apply (rule_tac a = "pi/2" in someI2, auto)
apply (rule order_less_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero_neg:
   "y < 0 ==> cos (arg(Complex 0 y)) = 0"
apply (simp add: arg_def abs_if)
apply (rule_tac a = "- pi/2" in someI2, auto)
apply (rule order_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero [simp]:
     "y \<noteq> 0 ==> cos (arg(Complex 0 y)) = 0"
by (auto simp add: linorder_neq_iff cos_arg_i_mult_zero_pos cos_arg_i_mult_zero_neg)


subsection{*Finally! Polar Form for Complex Numbers*}

definition

  (* abbreviation for (cos a + i sin a) *)
  cis :: "real => complex" where
  "cis a = Complex (cos a) (sin a)"

definition
  (* abbreviation for r*(cos a + i sin a) *)
  rcis :: "[real, real] => complex" where
  "rcis r a = complex_of_real r * cis a"

definition
  (* e ^ (x + iy) *)
  expi :: "complex => complex" where
  "expi z = complex_of_real(exp (Re z)) * cis (Im z)"

lemma complex_split_polar:
     "\<exists>r a. z = complex_of_real r * (Complex (cos a) (sin a))"
apply (induct z)
apply (auto simp add: polar_Ex complex_of_real_mult_Complex)
done

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
apply (induct z)
apply (simp add: rcis_def cis_def polar_Ex complex_of_real_mult_Complex)
done

lemma Re_rcis [simp]: "Re(rcis r a) = r * cos a"
by (simp add: rcis_def cis_def)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
by (simp add: rcis_def cis_def)

lemma sin_cos_squared_add2_mult: "(r * cos a)\<twosuperior> + (r * sin a)\<twosuperior> = r\<twosuperior>"
proof -
  have "(r * cos a)\<twosuperior> + (r * sin a)\<twosuperior> = r\<twosuperior> * ((cos a)\<twosuperior> + (sin a)\<twosuperior>)"
    by (simp only: power_mult_distrib right_distrib)
  thus ?thesis by simp
qed

lemma complex_mod_rcis [simp]: "cmod(rcis r a) = abs r"
by (simp add: rcis_def cis_def sin_cos_squared_add2_mult)

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
by (simp add: cmod_def power2_eq_square)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
by simp


(*---------------------------------------------------------------------------*)
(*  (r1 * cis a) * (r2 * cis b) = r1 * r2 * cis (a + b)                      *)
(*---------------------------------------------------------------------------*)

lemma cis_rcis_eq: "cis a = rcis 1 a"
by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
by (simp add: rcis_def cis_def cos_add sin_add right_distrib right_diff_distrib
              complex_of_real_def)

lemma cis_mult: "cis a * cis b = cis (a + b)"
by (simp add: cis_rcis_eq rcis_mult)

lemma cis_zero [simp]: "cis 0 = 1"
by (simp add: cis_def complex_one_def)

lemma rcis_zero_mod [simp]: "rcis 0 a = 0"
by (simp add: rcis_def)

lemma rcis_zero_arg [simp]: "rcis r 0 = complex_of_real r"
by (simp add: rcis_def)

lemma complex_of_real_minus_one:
   "complex_of_real (-(1::real)) = -(1::complex)"
by (simp add: complex_of_real_def complex_one_def)

lemma complex_i_mult_minus [simp]: "ii * (ii * x) = - x"
by (simp add: mult_assoc [symmetric])


lemma cis_real_of_nat_Suc_mult:
   "cis (real (Suc n) * a) = cis a * cis (real n * a)"
by (simp add: cis_def real_of_nat_Suc left_distrib cos_add sin_add right_distrib)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
apply (induct_tac "n")
apply (auto simp add: cis_real_of_nat_Suc_mult)
done

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
by (simp add: rcis_def power_mult_distrib DeMoivre)

lemma cis_inverse [simp]: "inverse(cis a) = cis (-a)"
by (simp add: cis_def complex_inverse_complex_split diff_minus)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
by (simp add: divide_inverse rcis_def)

lemma cis_divide: "cis a / cis b = cis (a - b)"
by (simp add: complex_divide_def cis_mult real_diff_def)

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)"
apply (simp add: complex_divide_def)
apply (case_tac "r2=0", simp)
apply (simp add: rcis_inverse rcis_mult real_diff_def)
done

lemma Re_cis [simp]: "Re(cis a) = cos a"
by (simp add: cis_def)

lemma Im_cis [simp]: "Im(cis a) = sin a"
by (simp add: cis_def)

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma expi_add: "expi(a + b) = expi(a) * expi(b)"
by (simp add: expi_def exp_add cis_mult [symmetric] mult_ac)

lemma expi_zero [simp]: "expi (0::complex) = 1"
by (simp add: expi_def)

lemma complex_expi_Ex: "\<exists>a r. z = complex_of_real r * expi a"
apply (insert rcis_Ex [of z])
apply (auto simp add: expi_def rcis_def mult_assoc [symmetric])
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done

lemma expi_two_pi_i [simp]: "expi((2::complex) * complex_of_real pi * ii) = 1"
by (simp add: expi_def cis_def)

end

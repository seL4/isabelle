(*  Title:      HOL/Nonstandard_Analysis/NSComplex.thy
    Author:     Jacques D. Fleuriot, University of Edinburgh
    Author:     Lawrence C Paulson
*)

section \<open>Nonstandard Complex Numbers\<close>

theory NSComplex
  imports NSA
begin

type_synonym hcomplex = "complex star"

abbreviation hcomplex_of_complex :: "complex \<Rightarrow> complex star"
  where "hcomplex_of_complex \<equiv> star_of"

abbreviation hcmod :: "complex star \<Rightarrow> real star"
  where "hcmod \<equiv> hnorm"


subsubsection \<open>Real and Imaginary parts\<close>

definition hRe :: "hcomplex \<Rightarrow> hypreal"
  where "hRe = *f* Re"

definition hIm :: "hcomplex \<Rightarrow> hypreal"
  where "hIm = *f* Im"


subsubsection \<open>Imaginary unit\<close>

definition iii :: hcomplex
  where "iii = star_of \<i>"


subsubsection \<open>Complex conjugate\<close>

definition hcnj :: "hcomplex \<Rightarrow> hcomplex"
  where "hcnj = *f* cnj"


subsubsection \<open>Argand\<close>

definition hsgn :: "hcomplex \<Rightarrow> hcomplex"
  where "hsgn = *f* sgn"

definition harg :: "hcomplex \<Rightarrow> hypreal"
  where "harg = *f* Arg"

definition  \<comment> \<open>abbreviation for \<open>cos a + i sin a\<close>\<close>
  hcis :: "hypreal \<Rightarrow> hcomplex"
  where "hcis = *f* cis"


subsubsection \<open>Injection from hyperreals\<close>

abbreviation hcomplex_of_hypreal :: "hypreal \<Rightarrow> hcomplex"
  where "hcomplex_of_hypreal \<equiv> of_hypreal"

definition  \<comment> \<open>abbreviation for \<open>r * (cos a + i sin a)\<close>\<close>
  hrcis :: "hypreal \<Rightarrow> hypreal \<Rightarrow> hcomplex"
  where "hrcis = *f2* rcis"


subsubsection \<open>\<open>e ^ (x + iy)\<close>\<close>

definition hExp :: "hcomplex \<Rightarrow> hcomplex"
  where "hExp = *f* exp"

definition HComplex :: "hypreal \<Rightarrow> hypreal \<Rightarrow> hcomplex"
  where "HComplex = *f2* Complex"

lemmas hcomplex_defs [transfer_unfold] =
  hRe_def hIm_def iii_def hcnj_def hsgn_def harg_def hcis_def
  hrcis_def hExp_def HComplex_def

lemma Standard_hRe [simp]: "x \<in> Standard \<Longrightarrow> hRe x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hIm [simp]: "x \<in> Standard \<Longrightarrow> hIm x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_iii [simp]: "iii \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hcnj [simp]: "x \<in> Standard \<Longrightarrow> hcnj x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hsgn [simp]: "x \<in> Standard \<Longrightarrow> hsgn x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_harg [simp]: "x \<in> Standard \<Longrightarrow> harg x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hcis [simp]: "r \<in> Standard \<Longrightarrow> hcis r \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hExp [simp]: "x \<in> Standard \<Longrightarrow> hExp x \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_hrcis [simp]: "r \<in> Standard \<Longrightarrow> s \<in> Standard \<Longrightarrow> hrcis r s \<in> Standard"
  by (simp add: hcomplex_defs)

lemma Standard_HComplex [simp]: "r \<in> Standard \<Longrightarrow> s \<in> Standard \<Longrightarrow> HComplex r s \<in> Standard"
  by (simp add: hcomplex_defs)

lemma hcmod_def: "hcmod = *f* cmod"
  by (rule hnorm_def)


subsection \<open>Properties of Nonstandard Real and Imaginary Parts\<close>

lemma hcomplex_hRe_hIm_cancel_iff: "\<And>w z. w = z \<longleftrightarrow> hRe w = hRe z \<and> hIm w = hIm z"
  by transfer (rule complex_eq_iff)

lemma hcomplex_equality [intro?]: "\<And>z w. hRe z = hRe w \<Longrightarrow> hIm z = hIm w \<Longrightarrow> z = w"
  by transfer (rule complex_eqI)

lemma hcomplex_hRe_zero [simp]: "hRe 0 = 0"
  by transfer simp

lemma hcomplex_hIm_zero [simp]: "hIm 0 = 0"
  by transfer simp

lemma hcomplex_hRe_one [simp]: "hRe 1 = 1"
  by transfer simp

lemma hcomplex_hIm_one [simp]: "hIm 1 = 0"
  by transfer simp


subsection \<open>Addition for Nonstandard Complex Numbers\<close>

lemma hRe_add: "\<And>x y. hRe (x + y) = hRe x + hRe y"
  by transfer simp

lemma hIm_add: "\<And>x y. hIm (x + y) = hIm x + hIm y"
  by transfer simp


subsection \<open>More Minus Laws\<close>

lemma hRe_minus: "\<And>z. hRe (- z) = - hRe z"
  by transfer (rule uminus_complex.sel)

lemma hIm_minus: "\<And>z. hIm (- z) = - hIm z"
  by transfer (rule uminus_complex.sel)

lemma hcomplex_add_minus_eq_minus: "x + y = 0 \<Longrightarrow> x = - y"
  for x y :: hcomplex
  apply (drule minus_unique)
  apply (simp add: minus_equation_iff [of x y])
  done

lemma hcomplex_i_mult_eq [simp]: "iii * iii = - 1"
  by transfer (rule i_squared)

lemma hcomplex_i_mult_left [simp]: "\<And>z. iii * (iii * z) = - z"
  by transfer (rule complex_i_mult_minus)

lemma hcomplex_i_not_zero [simp]: "iii \<noteq> 0"
  by transfer (rule complex_i_not_zero)


subsection \<open>More Multiplication Laws\<close>

lemma hcomplex_mult_minus_one: "- 1 * z = - z"
  for z :: hcomplex
  by simp

lemma hcomplex_mult_minus_one_right: "z * - 1 = - z"
  for z :: hcomplex
  by simp

lemma hcomplex_mult_left_cancel: "c \<noteq> 0 \<Longrightarrow> c * a = c * b \<longleftrightarrow> a = b"
  for a b c :: hcomplex
  by simp

lemma hcomplex_mult_right_cancel: "c \<noteq> 0 \<Longrightarrow> a * c = b * c \<longleftrightarrow> a = b"
  for a b c :: hcomplex
  by simp


subsection \<open>Subtraction and Division\<close>

(* TODO: delete *)
lemma hcomplex_diff_eq_eq [simp]: "x - y = z \<longleftrightarrow> x = z + y"
  for x y z :: hcomplex
  by (rule diff_eq_eq)


subsection \<open>Embedding Properties for \<^term>\<open>hcomplex_of_hypreal\<close> Map\<close>

lemma hRe_hcomplex_of_hypreal [simp]: "\<And>z. hRe (hcomplex_of_hypreal z) = z"
  by transfer (rule Re_complex_of_real)

lemma hIm_hcomplex_of_hypreal [simp]: "\<And>z. hIm (hcomplex_of_hypreal z) = 0"
  by transfer (rule Im_complex_of_real)

lemma hcomplex_of_epsilon_not_zero [simp]: "hcomplex_of_hypreal \<epsilon> \<noteq> 0"
  by (simp add: epsilon_not_zero)


subsection \<open>\<open>HComplex\<close> theorems\<close>

lemma hRe_HComplex [simp]: "\<And>x y. hRe (HComplex x y) = x"
  by transfer simp

lemma hIm_HComplex [simp]: "\<And>x y. hIm (HComplex x y) = y"
  by transfer simp

lemma hcomplex_surj [simp]: "\<And>z. HComplex (hRe z) (hIm z) = z"
  by transfer (rule complex_surj)

lemma hcomplex_induct [case_names rect(*, induct type: hcomplex*)]:
  "(\<And>x y. P (HComplex x y)) \<Longrightarrow> P z"
  by (rule hcomplex_surj [THEN subst]) blast


subsection \<open>Modulus (Absolute Value) of Nonstandard Complex Number\<close>

lemma hcomplex_of_hypreal_abs:
  "hcomplex_of_hypreal \<bar>x\<bar> = hcomplex_of_hypreal (hcmod (hcomplex_of_hypreal x))"
  by simp

lemma HComplex_inject [simp]: "\<And>x y x' y'. HComplex x y = HComplex x' y' \<longleftrightarrow> x = x' \<and> y = y'"
  by transfer (rule complex.inject)

lemma HComplex_add [simp]:
  "\<And>x1 y1 x2 y2. HComplex x1 y1 + HComplex x2 y2 = HComplex (x1 + x2) (y1 + y2)"
  by transfer (rule complex_add)

lemma HComplex_minus [simp]: "\<And>x y. - HComplex x y = HComplex (- x) (- y)"
  by transfer (rule complex_minus)

lemma HComplex_diff [simp]:
  "\<And>x1 y1 x2 y2. HComplex x1 y1 - HComplex x2 y2 = HComplex (x1 - x2) (y1 - y2)"
  by transfer (rule complex_diff)

lemma HComplex_mult [simp]:
  "\<And>x1 y1 x2 y2. HComplex x1 y1 * HComplex x2 y2 = HComplex (x1*x2 - y1*y2) (x1*y2 + y1*x2)"
  by transfer (rule complex_mult)

text \<open>\<open>HComplex_inverse\<close> is proved below.\<close>

lemma hcomplex_of_hypreal_eq: "\<And>r. hcomplex_of_hypreal r = HComplex r 0"
  by transfer (rule complex_of_real_def)

lemma HComplex_add_hcomplex_of_hypreal [simp]:
  "\<And>x y r. HComplex x y + hcomplex_of_hypreal r = HComplex (x + r) y"
  by transfer (rule Complex_add_complex_of_real)

lemma hcomplex_of_hypreal_add_HComplex [simp]:
  "\<And>r x y. hcomplex_of_hypreal r + HComplex x y = HComplex (r + x) y"
  by transfer (rule complex_of_real_add_Complex)

lemma HComplex_mult_hcomplex_of_hypreal:
  "\<And>x y r. HComplex x y * hcomplex_of_hypreal r = HComplex (x * r) (y * r)"
  by transfer (rule Complex_mult_complex_of_real)

lemma hcomplex_of_hypreal_mult_HComplex:
  "\<And>r x y. hcomplex_of_hypreal r * HComplex x y = HComplex (r * x) (r * y)"
  by transfer (rule complex_of_real_mult_Complex)

lemma i_hcomplex_of_hypreal [simp]: "\<And>r. iii * hcomplex_of_hypreal r = HComplex 0 r"
  by transfer (rule i_complex_of_real)

lemma hcomplex_of_hypreal_i [simp]: "\<And>r. hcomplex_of_hypreal r * iii = HComplex 0 r"
  by transfer (rule complex_of_real_i)


subsection \<open>Conjugation\<close>

lemma hcomplex_hcnj_cancel_iff [iff]: "\<And>x y. hcnj x = hcnj y \<longleftrightarrow> x = y"
  by transfer (rule complex_cnj_cancel_iff)

lemma hcomplex_hcnj_hcnj [simp]: "\<And>z. hcnj (hcnj z) = z"
  by transfer (rule complex_cnj_cnj)

lemma hcomplex_hcnj_hcomplex_of_hypreal [simp]:
  "\<And>x. hcnj (hcomplex_of_hypreal x) = hcomplex_of_hypreal x"
  by transfer (rule complex_cnj_complex_of_real)

lemma hcomplex_hmod_hcnj [simp]: "\<And>z. hcmod (hcnj z) = hcmod z"
  by transfer (rule complex_mod_cnj)

lemma hcomplex_hcnj_minus: "\<And>z. hcnj (- z) = - hcnj z"
  by transfer (rule complex_cnj_minus)

lemma hcomplex_hcnj_inverse: "\<And>z. hcnj (inverse z) = inverse (hcnj z)"
  by transfer (rule complex_cnj_inverse)

lemma hcomplex_hcnj_add: "\<And>w z. hcnj (w + z) = hcnj w + hcnj z"
  by transfer (rule complex_cnj_add)

lemma hcomplex_hcnj_diff: "\<And>w z. hcnj (w - z) = hcnj w - hcnj z"
  by transfer (rule complex_cnj_diff)

lemma hcomplex_hcnj_mult: "\<And>w z. hcnj (w * z) = hcnj w * hcnj z"
  by transfer (rule complex_cnj_mult)

lemma hcomplex_hcnj_divide: "\<And>w z. hcnj (w / z) = hcnj w / hcnj z"
  by transfer (rule complex_cnj_divide)

lemma hcnj_one [simp]: "hcnj 1 = 1"
  by transfer (rule complex_cnj_one)

lemma hcomplex_hcnj_zero [simp]: "hcnj 0 = 0"
  by transfer (rule complex_cnj_zero)

lemma hcomplex_hcnj_zero_iff [iff]: "\<And>z. hcnj z = 0 \<longleftrightarrow> z = 0"
  by transfer (rule complex_cnj_zero_iff)

lemma hcomplex_mult_hcnj: "\<And>z. z * hcnj z = hcomplex_of_hypreal ((hRe z)\<^sup>2 + (hIm z)\<^sup>2)"
  by transfer (rule complex_mult_cnj)


subsection \<open>More Theorems about the Function \<^term>\<open>hcmod\<close>\<close>

lemma hcmod_hcomplex_of_hypreal_of_nat [simp]:
  "hcmod (hcomplex_of_hypreal (hypreal_of_nat n)) = hypreal_of_nat n"
  by simp

lemma hcmod_hcomplex_of_hypreal_of_hypnat [simp]:
  "hcmod (hcomplex_of_hypreal(hypreal_of_hypnat n)) = hypreal_of_hypnat n"
  by simp

lemma hcmod_mult_hcnj: "\<And>z. hcmod (z * hcnj z) = (hcmod z)\<^sup>2"
  by transfer (rule complex_mod_mult_cnj)

lemma hcmod_triangle_ineq2 [simp]: "\<And>a b. hcmod (b + a) - hcmod b \<le> hcmod a"
  by transfer (rule complex_mod_triangle_ineq2)

lemma hcmod_diff_ineq [simp]: "\<And>a b. hcmod a - hcmod b \<le> hcmod (a + b)"
  by transfer (rule norm_diff_ineq)


subsection \<open>Exponentiation\<close>

lemma hcomplexpow_0 [simp]: "z ^ 0 = 1"
  for z :: hcomplex
  by (rule power_0)

lemma hcomplexpow_Suc [simp]: "z ^ (Suc n) = z * (z ^ n)"
  for z :: hcomplex
  by (rule power_Suc)

lemma hcomplexpow_i_squared [simp]: "iii\<^sup>2 = -1"
  by transfer (rule power2_i)

lemma hcomplex_of_hypreal_pow: "\<And>x. hcomplex_of_hypreal (x ^ n) = hcomplex_of_hypreal x ^ n"
  by transfer (rule of_real_power)

lemma hcomplex_hcnj_pow: "\<And>z. hcnj (z ^ n) = hcnj z ^ n"
  by transfer (rule complex_cnj_power)

lemma hcmod_hcomplexpow: "\<And>x. hcmod (x ^ n) = hcmod x ^ n"
  by transfer (rule norm_power)

lemma hcpow_minus:
  "\<And>x n. (- x :: hcomplex) pow n = (if ( *p* even) n then (x pow n) else - (x pow n))"
  by transfer simp

lemma hcpow_mult: "(r * s) pow n = (r pow n) * (s pow n)"
  for r s :: hcomplex
  by (fact hyperpow_mult)

lemma hcpow_zero2 [simp]: "\<And>n. 0 pow (hSuc n) = (0::'a::semiring_1 star)"
  by transfer (rule power_0_Suc)

lemma hcpow_not_zero [simp,intro]: "\<And>r n. r \<noteq> 0 \<Longrightarrow> r pow n \<noteq> (0::hcomplex)"
  by (fact hyperpow_not_zero)

lemma hcpow_zero_zero: "r pow n = 0 \<Longrightarrow> r = 0"
  for r :: hcomplex
  by (blast intro: ccontr dest: hcpow_not_zero)


subsection \<open>The Function \<^term>\<open>hsgn\<close>\<close>

lemma hsgn_zero [simp]: "hsgn 0 = 0"
  by transfer (rule sgn_zero)

lemma hsgn_one [simp]: "hsgn 1 = 1"
  by transfer (rule sgn_one)

lemma hsgn_minus: "\<And>z. hsgn (- z) = - hsgn z"
  by transfer (rule sgn_minus)

lemma hsgn_eq: "\<And>z. hsgn z = z / hcomplex_of_hypreal (hcmod z)"
  by transfer (rule sgn_eq)

lemma hcmod_i: "\<And>x y. hcmod (HComplex x y) = ( *f* sqrt) (x\<^sup>2 + y\<^sup>2)"
  by transfer (rule complex_norm)

lemma hcomplex_eq_cancel_iff1 [simp]:
  "hcomplex_of_hypreal xa = HComplex x y \<longleftrightarrow> xa = x \<and> y = 0"
  by (simp add: hcomplex_of_hypreal_eq)

lemma hcomplex_eq_cancel_iff2 [simp]:
  "HComplex x y = hcomplex_of_hypreal xa \<longleftrightarrow> x = xa \<and> y = 0"
  by (simp add: hcomplex_of_hypreal_eq)

lemma HComplex_eq_0 [simp]: "\<And>x y. HComplex x y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by transfer (rule Complex_eq_0)

lemma HComplex_eq_1 [simp]: "\<And>x y. HComplex x y = 1 \<longleftrightarrow> x = 1 \<and> y = 0"
  by transfer (rule Complex_eq_1)

lemma i_eq_HComplex_0_1: "iii = HComplex 0 1"
  by transfer (simp add: complex_eq_iff)

lemma HComplex_eq_i [simp]: "\<And>x y. HComplex x y = iii \<longleftrightarrow> x = 0 \<and> y = 1"
  by transfer (rule Complex_eq_i)

lemma hRe_hsgn [simp]: "\<And>z. hRe (hsgn z) = hRe z / hcmod z"
  by transfer (rule Re_sgn)

lemma hIm_hsgn [simp]: "\<And>z. hIm (hsgn z) = hIm z / hcmod z"
  by transfer (rule Im_sgn)

lemma HComplex_inverse: "\<And>x y. inverse (HComplex x y) = HComplex (x / (x\<^sup>2 + y\<^sup>2)) (- y / (x\<^sup>2 + y\<^sup>2))"
  by transfer (rule complex_inverse)

lemma hRe_mult_i_eq[simp]: "\<And>y. hRe (iii * hcomplex_of_hypreal y) = 0"
  by transfer simp

lemma hIm_mult_i_eq [simp]: "\<And>y. hIm (iii * hcomplex_of_hypreal y) = y"
  by transfer simp

lemma hcmod_mult_i [simp]: "\<And>y. hcmod (iii * hcomplex_of_hypreal y) = \<bar>y\<bar>"
  by transfer (simp add: norm_complex_def)

lemma hcmod_mult_i2 [simp]: "\<And>y. hcmod (hcomplex_of_hypreal y * iii) = \<bar>y\<bar>"
  by transfer (simp add: norm_complex_def)


subsubsection \<open>\<open>harg\<close>\<close>

lemma cos_harg_i_mult_zero [simp]: "\<And>y. y \<noteq> 0 \<Longrightarrow> ( *f* cos) (harg (HComplex 0 y)) = 0"
  by transfer (simp add: Complex_eq)


subsection \<open>Polar Form for Nonstandard Complex Numbers\<close>

lemma complex_split_polar2: "\<forall>n. \<exists>r a. (z n) = complex_of_real r * Complex (cos a) (sin a)"
  unfolding Complex_eq by (auto intro: complex_split_polar)

lemma hcomplex_split_polar:
  "\<And>z. \<exists>r a. z = hcomplex_of_hypreal r * (HComplex (( *f* cos) a) (( *f* sin) a))"
  by transfer (simp add: Complex_eq complex_split_polar)

lemma hcis_eq:
  "\<And>a. hcis a = hcomplex_of_hypreal (( *f* cos) a) + iii * hcomplex_of_hypreal (( *f* sin) a)"
  by transfer (simp add: complex_eq_iff)

lemma hrcis_Ex: "\<And>z. \<exists>r a. z = hrcis r a"
  by transfer (rule rcis_Ex)

lemma hRe_hcomplex_polar [simp]:
  "\<And>r a. hRe (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = r * ( *f* cos) a"
  by transfer simp

lemma hRe_hrcis [simp]: "\<And>r a. hRe (hrcis r a) = r * ( *f* cos) a"
  by transfer (rule Re_rcis)

lemma hIm_hcomplex_polar [simp]:
  "\<And>r a. hIm (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = r * ( *f* sin) a"
  by transfer simp

lemma hIm_hrcis [simp]: "\<And>r a. hIm (hrcis r a) = r * ( *f* sin) a"
  by transfer (rule Im_rcis)

lemma hcmod_unit_one [simp]: "\<And>a. hcmod (HComplex (( *f* cos) a) (( *f* sin) a)) = 1"
  by transfer (simp add: cmod_unit_one)

lemma hcmod_complex_polar [simp]:
  "\<And>r a. hcmod (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = \<bar>r\<bar>"
  by transfer (simp add: Complex_eq cmod_complex_polar)

lemma hcmod_hrcis [simp]: "\<And>r a. hcmod(hrcis r a) = \<bar>r\<bar>"
  by transfer (rule complex_mod_rcis)

text \<open>\<open>(r1 * hrcis a) * (r2 * hrcis b) = r1 * r2 * hrcis (a + b)\<close>\<close>

lemma hcis_hrcis_eq: "\<And>a. hcis a = hrcis 1 a"
  by transfer (rule cis_rcis_eq)
declare hcis_hrcis_eq [symmetric, simp]

lemma hrcis_mult: "\<And>a b r1 r2. hrcis r1 a * hrcis r2 b = hrcis (r1 * r2) (a + b)"
  by transfer (rule rcis_mult)

lemma hcis_mult: "\<And>a b. hcis a * hcis b = hcis (a + b)"
  by transfer (rule cis_mult)

lemma hcis_zero [simp]: "hcis 0 = 1"
  by transfer (rule cis_zero)

lemma hrcis_zero_mod [simp]: "\<And>a. hrcis 0 a = 0"
  by transfer (rule rcis_zero_mod)

lemma hrcis_zero_arg [simp]: "\<And>r. hrcis r 0 = hcomplex_of_hypreal r"
  by transfer (rule rcis_zero_arg)

lemma hcomplex_i_mult_minus [simp]: "\<And>x. iii * (iii * x) = - x"
  by transfer (rule complex_i_mult_minus)

lemma hcomplex_i_mult_minus2 [simp]: "iii * iii * x = - x"
  by simp

lemma hcis_hypreal_of_nat_Suc_mult:
  "\<And>a. hcis (hypreal_of_nat (Suc n) * a) = hcis a * hcis (hypreal_of_nat n * a)"
  by transfer (simp add: distrib_right cis_mult)

lemma NSDeMoivre: "\<And>a. (hcis a) ^ n = hcis (hypreal_of_nat n * a)"
  by transfer (rule DeMoivre)

lemma hcis_hypreal_of_hypnat_Suc_mult:
  "\<And>a n. hcis (hypreal_of_hypnat (n + 1) * a) = hcis a * hcis (hypreal_of_hypnat n * a)"
  by transfer (simp add: distrib_right cis_mult)

lemma NSDeMoivre_ext: "\<And>a n. (hcis a) pow n = hcis (hypreal_of_hypnat n * a)"
  by transfer (rule DeMoivre)

lemma NSDeMoivre2: "\<And>a r. (hrcis r a) ^ n = hrcis (r ^ n) (hypreal_of_nat n * a)"
  by transfer (rule DeMoivre2)

lemma DeMoivre2_ext: "\<And>a r n. (hrcis r a) pow n = hrcis (r pow n) (hypreal_of_hypnat n * a)"
  by transfer (rule DeMoivre2)

lemma hcis_inverse [simp]: "\<And>a. inverse (hcis a) = hcis (- a)"
  by transfer (rule cis_inverse)

lemma hrcis_inverse: "\<And>a r. inverse (hrcis r a) = hrcis (inverse r) (- a)"
  by transfer (simp add: rcis_inverse inverse_eq_divide [symmetric])

lemma hRe_hcis [simp]: "\<And>a. hRe (hcis a) = ( *f* cos) a"
  by transfer simp

lemma hIm_hcis [simp]: "\<And>a. hIm (hcis a) = ( *f* sin) a"
  by transfer simp

lemma cos_n_hRe_hcis_pow_n: "( *f* cos) (hypreal_of_nat n * a) = hRe (hcis a ^ n)"
  by (simp add: NSDeMoivre)

lemma sin_n_hIm_hcis_pow_n: "( *f* sin) (hypreal_of_nat n * a) = hIm (hcis a ^ n)"
  by (simp add: NSDeMoivre)

lemma cos_n_hRe_hcis_hcpow_n: "( *f* cos) (hypreal_of_hypnat n * a) = hRe (hcis a pow n)"
  by (simp add: NSDeMoivre_ext)

lemma sin_n_hIm_hcis_hcpow_n: "( *f* sin) (hypreal_of_hypnat n * a) = hIm (hcis a pow n)"
  by (simp add: NSDeMoivre_ext)

lemma hExp_add: "\<And>a b. hExp (a + b) = hExp a * hExp b"
  by transfer (rule exp_add)


subsection \<open>\<^term>\<open>hcomplex_of_complex\<close>: the Injection from type \<^typ>\<open>complex\<close> to to \<^typ>\<open>hcomplex\<close>\<close>

lemma hcomplex_of_complex_i: "iii = hcomplex_of_complex \<i>"
  by (rule iii_def)

lemma hRe_hcomplex_of_complex: "hRe (hcomplex_of_complex z) = hypreal_of_real (Re z)"
  by transfer (rule refl)

lemma hIm_hcomplex_of_complex: "hIm (hcomplex_of_complex z) = hypreal_of_real (Im z)"
  by transfer (rule refl)

lemma hcmod_hcomplex_of_complex: "hcmod (hcomplex_of_complex x) = hypreal_of_real (cmod x)"
  by transfer (rule refl)


subsection \<open>Numerals and Arithmetic\<close>

lemma hcomplex_of_hypreal_eq_hcomplex_of_complex:
  "hcomplex_of_hypreal (hypreal_of_real x) = hcomplex_of_complex (complex_of_real x)"
  by transfer (rule refl)

lemma hcomplex_hypreal_numeral:
  "hcomplex_of_complex (numeral w) = hcomplex_of_hypreal(numeral w)"
  by transfer (rule of_real_numeral [symmetric])

lemma hcomplex_hypreal_neg_numeral:
  "hcomplex_of_complex (- numeral w) = hcomplex_of_hypreal(- numeral w)"
  by transfer (rule of_real_neg_numeral [symmetric])

lemma hcomplex_numeral_hcnj [simp]: "hcnj (numeral v :: hcomplex) = numeral v"
  by transfer (rule complex_cnj_numeral)

lemma hcomplex_numeral_hcmod [simp]: "hcmod (numeral v :: hcomplex) = (numeral v :: hypreal)"
  by transfer (rule norm_numeral)

lemma hcomplex_neg_numeral_hcmod [simp]: "hcmod (- numeral v :: hcomplex) = (numeral v :: hypreal)"
  by transfer (rule norm_neg_numeral)

lemma hcomplex_numeral_hRe [simp]: "hRe (numeral v :: hcomplex) = numeral v"
  by transfer (rule complex_Re_numeral)

lemma hcomplex_numeral_hIm [simp]: "hIm (numeral v :: hcomplex) = 0"
  by transfer (rule complex_Im_numeral)

end

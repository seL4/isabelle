(*  Title:       Complex.thy
    ID:      $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header {* Complex Numbers: Rectangular and Polar Representations *}

theory Complex = HLog:

datatype complex = Complex real real

instance complex :: "{zero, one, plus, times, minus, inverse, power}" ..

consts
  "ii"    :: complex    ("\<i>")

consts Re :: "complex => real"
primrec "Re (Complex x y) = x"

consts Im :: "complex => real"
primrec "Im (Complex x y) = y"

lemma complex_surj [simp]: "Complex (Re z) (Im z) = z"
  by (induct z) simp

constdefs

  (*----------- modulus ------------*)

  cmod :: "complex => real"
  "cmod z == sqrt(Re(z) ^ 2 + Im(z) ^ 2)"

  (*----- injection from reals -----*)

  complex_of_real :: "real => complex"
  "complex_of_real r == Complex r 0"

  (*------- complex conjugate ------*)

  cnj :: "complex => complex"
  "cnj z == Complex (Re z) (-Im z)"

  (*------------ Argand -------------*)

  sgn :: "complex => complex"
  "sgn z == z / complex_of_real(cmod z)"

  arg :: "complex => real"
  "arg z == @a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a \<le> pi"


defs (overloaded)

  complex_zero_def:
  "0 == Complex 0 0"

  complex_one_def:
  "1 == Complex 1 0"

  i_def: "ii == Complex 0 1"

  complex_minus_def: "- z == Complex (- Re z) (- Im z)"

  complex_inverse_def:
   "inverse z ==
    Complex (Re z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>)) (- Im z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>))"

  complex_add_def:
    "z + w == Complex (Re z + Re w) (Im z + Im w)"

  complex_diff_def:
    "z - w == z + - (w::complex)"

  complex_mult_def:
    "z * w == Complex (Re z * Re w - Im z * Im w) (Re z * Im w + Im z * Re w)"

  complex_divide_def: "w / (z::complex) == w * inverse z"


constdefs

  (* abbreviation for (cos a + i sin a) *)
  cis :: "real => complex"
  "cis a == Complex (cos a) (sin a)"

  (* abbreviation for r*(cos a + i sin a) *)
  rcis :: "[real, real] => complex"
  "rcis r a == complex_of_real r * cis a"

  (* e ^ (x + iy) *)
  expi :: "complex => complex"
  "expi z == complex_of_real(exp (Re z)) * cis (Im z)"


lemma complex_equality [intro?]: "Re z = Re w ==> Im z = Im w ==> z = w"
  by (induct z, induct w) simp

lemma Re [simp]: "Re(Complex x y) = x"
by simp

lemma Im [simp]: "Im(Complex x y) = y"
by simp

lemma complex_Re_Im_cancel_iff: "(w=z) = (Re(w) = Re(z) & Im(w) = Im(z))"
by (induct w, induct z, simp)

lemma complex_Re_zero [simp]: "Re 0 = 0"
by (simp add: complex_zero_def)

lemma complex_Im_zero [simp]: "Im 0 = 0"
by (simp add: complex_zero_def)

lemma complex_Re_one [simp]: "Re 1 = 1"
by (simp add: complex_one_def)

lemma complex_Im_one [simp]: "Im 1 = 0"
by (simp add: complex_one_def)

lemma complex_Re_i [simp]: "Re(ii) = 0"
by (simp add: i_def)

lemma complex_Im_i [simp]: "Im(ii) = 1"
by (simp add: i_def)

lemma Re_complex_of_real [simp]: "Re(complex_of_real z) = z"
by (simp add: complex_of_real_def)

lemma Im_complex_of_real [simp]: "Im(complex_of_real z) = 0"
by (simp add: complex_of_real_def)


subsection{*Unary Minus*}

lemma complex_minus [simp]: "- (Complex x y) = Complex (-x) (-y)"
by (simp add: complex_minus_def)

lemma complex_Re_minus [simp]: "Re (-z) = - Re z"
by (simp add: complex_minus_def)

lemma complex_Im_minus [simp]: "Im (-z) = - Im z"
by (simp add: complex_minus_def)


subsection{*Addition*}

lemma complex_add [simp]:
     "Complex x1 y1 + Complex x2 y2 = Complex (x1+x2) (y1+y2)"
by (simp add: complex_add_def)

lemma complex_Re_add [simp]: "Re(x + y) = Re(x) + Re(y)"
by (simp add: complex_add_def)

lemma complex_Im_add [simp]: "Im(x + y) = Im(x) + Im(y)"
by (simp add: complex_add_def)

lemma complex_add_commute: "(u::complex) + v = v + u"
by (simp add: complex_add_def add_commute)

lemma complex_add_assoc: "((u::complex) + v) + w = u + (v + w)"
by (simp add: complex_add_def add_assoc)

lemma complex_add_zero_left: "(0::complex) + z = z"
by (simp add: complex_add_def complex_zero_def)

lemma complex_add_zero_right: "z + (0::complex) = z"
by (simp add: complex_add_def complex_zero_def)

lemma complex_add_minus_left: "-z + z = (0::complex)"
by (simp add: complex_add_def complex_minus_def complex_zero_def)

lemma complex_diff:
      "Complex x1 y1 - Complex x2 y2 = Complex (x1-x2) (y1-y2)"
by (simp add: complex_add_def complex_minus_def complex_diff_def)

lemma complex_Re_diff [simp]: "Re(x - y) = Re(x) - Re(y)"
by (simp add: complex_diff_def)

lemma complex_Im_diff [simp]: "Im(x - y) = Im(x) - Im(y)"
by (simp add: complex_diff_def)


subsection{*Multiplication*}

lemma complex_mult [simp]:
     "Complex x1 y1 * Complex x2 y2 = Complex (x1*x2 - y1*y2) (x1*y2 + y1*x2)"
by (simp add: complex_mult_def)

lemma complex_mult_commute: "(w::complex) * z = z * w"
by (simp add: complex_mult_def mult_commute add_commute)

lemma complex_mult_assoc: "((u::complex) * v) * w = u * (v * w)"
by (simp add: complex_mult_def mult_ac add_ac
              right_diff_distrib right_distrib left_diff_distrib left_distrib)

lemma complex_mult_one_left: "(1::complex) * z = z"
by (simp add: complex_mult_def complex_one_def)

lemma complex_mult_one_right: "z * (1::complex) = z"
by (simp add: complex_mult_def complex_one_def)


subsection{*Inverse*}

lemma complex_inverse [simp]:
     "inverse (Complex x y) = Complex (x/(x ^ 2 + y ^ 2)) (-y/(x ^ 2 + y ^ 2))"
by (simp add: complex_inverse_def)

lemma complex_mult_inv_left: "z \<noteq> (0::complex) ==> inverse(z) * z = 1"
apply (induct z)
apply (rename_tac x y)
apply (auto simp add: complex_mult complex_inverse complex_one_def
      complex_zero_def add_divide_distrib [symmetric] power2_eq_square mult_ac)
apply (drule_tac y = y in real_sum_squares_not_zero)
apply (drule_tac [2] x = x in real_sum_squares_not_zero2, auto)
done


subsection {* The field of complex numbers *}

instance complex :: field
proof
  fix z u v w :: complex
  show "(u + v) + w = u + (v + w)"
    by (rule complex_add_assoc)
  show "z + w = w + z"
    by (rule complex_add_commute)
  show "0 + z = z"
    by (rule complex_add_zero_left)
  show "-z + z = 0"
    by (rule complex_add_minus_left)
  show "z - w = z + -w"
    by (simp add: complex_diff_def)
  show "(u * v) * w = u * (v * w)"
    by (rule complex_mult_assoc)
  show "z * w = w * z"
    by (rule complex_mult_commute)
  show "1 * z = z"
    by (rule complex_mult_one_left)
  show "0 \<noteq> (1::complex)"
    by (simp add: complex_zero_def complex_one_def)
  show "(u + v) * w = u * w + v * w"
    by (simp add: complex_mult_def complex_add_def left_distrib 
                  diff_minus add_ac)
  show "z / w = z * inverse w"
    by (simp add: complex_divide_def)
  assume "w \<noteq> 0"
  thus "inverse w * w = 1"
    by (simp add: complex_mult_inv_left)
qed

instance complex :: division_by_zero
proof
  show "inverse 0 = (0::complex)"
    by (simp add: complex_inverse_def complex_zero_def)
qed


subsection{*Embedding Properties for @{term complex_of_real} Map*}

lemma Complex_add_complex_of_real [simp]:
     "Complex x y + complex_of_real r = Complex (x+r) y"
by (simp add: complex_of_real_def)

lemma complex_of_real_add_Complex [simp]:
     "complex_of_real r + Complex x y = Complex (r+x) y"
by (simp add: i_def complex_of_real_def)

lemma Complex_mult_complex_of_real:
     "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
by (simp add: complex_of_real_def)

lemma complex_of_real_mult_Complex:
     "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
by (simp add: i_def complex_of_real_def)

lemma i_complex_of_real [simp]: "ii * complex_of_real r = Complex 0 r"
by (simp add: i_def complex_of_real_def)

lemma complex_of_real_i [simp]: "complex_of_real r * ii = Complex 0 r"
by (simp add: i_def complex_of_real_def)

lemma complex_of_real_one [simp]: "complex_of_real 1 = 1"
by (simp add: complex_one_def complex_of_real_def)

lemma complex_of_real_zero [simp]: "complex_of_real 0 = 0"
by (simp add: complex_zero_def complex_of_real_def)

lemma complex_of_real_eq_iff [iff]:
     "(complex_of_real x = complex_of_real y) = (x = y)"
by (simp add: complex_of_real_def)

lemma complex_of_real_minus: "complex_of_real(-x) = - complex_of_real x"
by (simp add: complex_of_real_def complex_minus)

lemma complex_of_real_inverse:
     "complex_of_real(inverse x) = inverse(complex_of_real x)"
apply (case_tac "x=0", simp)
apply (simp add: complex_inverse complex_of_real_def real_divide_def
                 inverse_mult_distrib power2_eq_square)
done

lemma complex_of_real_add:
     "complex_of_real x + complex_of_real y = complex_of_real (x + y)"
by (simp add: complex_add complex_of_real_def)

lemma complex_of_real_diff:
     "complex_of_real x - complex_of_real y = complex_of_real (x - y)"
by (simp add: complex_of_real_minus [symmetric] complex_diff_def 
              complex_of_real_add)

lemma complex_of_real_mult:
     "complex_of_real x * complex_of_real y = complex_of_real (x * y)"
by (simp add: complex_mult complex_of_real_def)

lemma complex_of_real_divide:
      "complex_of_real x / complex_of_real y = complex_of_real(x/y)"
apply (simp add: complex_divide_def)
apply (case_tac "y=0", simp)
apply (simp add: complex_of_real_mult [symmetric] complex_of_real_inverse 
                 real_divide_def)
done

lemma complex_mod [simp]: "cmod (Complex x y) = sqrt(x ^ 2 + y ^ 2)"
by (simp add: cmod_def)

lemma complex_mod_zero [simp]: "cmod(0) = 0"
by (simp add: cmod_def)

lemma complex_mod_one [simp]: "cmod(1) = 1"
by (simp add: cmod_def power2_eq_square)

lemma complex_mod_complex_of_real [simp]: "cmod(complex_of_real x) = abs x"
by (simp add: complex_of_real_def power2_eq_square complex_mod)

lemma complex_of_real_abs:
     "complex_of_real (abs x) = complex_of_real(cmod(complex_of_real x))"
by simp


subsection{*The Functions @{term Re} and @{term Im}*}

lemma complex_Re_mult_eq: "Re (w * z) = Re w * Re z - Im w * Im z"
by (induct z, induct w, simp add: complex_mult)

lemma complex_Im_mult_eq: "Im (w * z) = Re w * Im z + Im w * Re z"
by (induct z, induct w, simp add: complex_mult)

lemma Re_i_times [simp]: "Re(ii * z) = - Im z"
by (simp add: complex_Re_mult_eq) 

lemma Re_times_i [simp]: "Re(z * ii) = - Im z"
by (simp add: complex_Re_mult_eq) 

lemma Im_i_times [simp]: "Im(ii * z) = Re z"
by (simp add: complex_Im_mult_eq) 

lemma Im_times_i [simp]: "Im(z * ii) = Re z"
by (simp add: complex_Im_mult_eq) 

lemma complex_Re_mult: "[| Im w = 0; Im z = 0 |] ==> Re(w * z) = Re(w) * Re(z)"
by (simp add: complex_Re_mult_eq)

lemma complex_Re_mult_complex_of_real [simp]:
     "Re (z * complex_of_real c) = Re(z) * c"
by (simp add: complex_Re_mult_eq)

lemma complex_Im_mult_complex_of_real [simp]:
     "Im (z * complex_of_real c) = Im(z) * c"
by (simp add: complex_Im_mult_eq)

lemma complex_Re_mult_complex_of_real2 [simp]:
     "Re (complex_of_real c * z) = c * Re(z)"
by (simp add: complex_Re_mult_eq)

lemma complex_Im_mult_complex_of_real2 [simp]:
     "Im (complex_of_real c * z) = c * Im(z)"
by (simp add: complex_Im_mult_eq)
 

subsection{*Conjugation is an Automorphism*}

lemma complex_cnj: "cnj (Complex x y) = Complex x (-y)"
by (simp add: cnj_def)

lemma complex_cnj_cancel_iff [simp]: "(cnj x = cnj y) = (x = y)"
by (simp add: cnj_def complex_Re_Im_cancel_iff)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
by (simp add: cnj_def)

lemma complex_cnj_complex_of_real [simp]:
     "cnj (complex_of_real x) = complex_of_real x"
by (simp add: complex_of_real_def complex_cnj)

lemma complex_mod_cnj [simp]: "cmod (cnj z) = cmod z"
by (induct z, simp add: complex_cnj complex_mod power2_eq_square)

lemma complex_cnj_minus: "cnj (-z) = - cnj z"
by (simp add: cnj_def complex_minus complex_Re_minus complex_Im_minus)

lemma complex_cnj_inverse: "cnj(inverse z) = inverse(cnj z)"
by (induct z, simp add: complex_cnj complex_inverse power2_eq_square)

lemma complex_cnj_add: "cnj(w + z) = cnj(w) + cnj(z)"
by (induct w, induct z, simp add: complex_cnj complex_add)

lemma complex_cnj_diff: "cnj(w - z) = cnj(w) - cnj(z)"
by (simp add: complex_diff_def complex_cnj_add complex_cnj_minus)

lemma complex_cnj_mult: "cnj(w * z) = cnj(w) * cnj(z)"
by (induct w, induct z, simp add: complex_cnj complex_mult)

lemma complex_cnj_divide: "cnj(w / z) = (cnj w)/(cnj z)"
by (simp add: complex_divide_def complex_cnj_mult complex_cnj_inverse)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
by (simp add: cnj_def complex_one_def)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re(z))"
by (induct z, simp add: complex_add complex_cnj complex_of_real_def)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im(z)) * ii"
apply (induct z)
apply (simp add: complex_add complex_cnj complex_of_real_def complex_diff_def
                 complex_minus i_def complex_mult)
done

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
by (simp add: cnj_def complex_zero_def)

lemma complex_cnj_zero_iff [iff]: "(cnj z = 0) = (z = 0)"
by (induct z, simp add: complex_zero_def complex_cnj)

lemma complex_mult_cnj: "z * cnj z = complex_of_real (Re(z) ^ 2 + Im(z) ^ 2)"
by (induct z,
    simp add: complex_cnj complex_mult complex_of_real_def power2_eq_square)


subsection{*Modulus*}

lemma complex_mod_eq_zero_cancel [simp]: "(cmod x = 0) = (x = 0)"
apply (induct x)
apply (auto intro: real_sum_squares_cancel real_sum_squares_cancel2
            simp add: complex_mod complex_zero_def power2_eq_square)
done

lemma complex_mod_complex_of_real_of_nat [simp]:
     "cmod (complex_of_real(real (n::nat))) = real n"
by simp

lemma complex_mod_minus [simp]: "cmod (-x) = cmod(x)"
by (induct x, simp add: complex_mod complex_minus power2_eq_square)

lemma complex_mod_mult_cnj: "cmod(z * cnj(z)) = cmod(z) ^ 2"
apply (induct z, simp add: complex_mod complex_cnj complex_mult)
apply (simp add: power2_eq_square real_abs_def)
done

lemma complex_mod_squared: "cmod(Complex x y) ^ 2 = x ^ 2 + y ^ 2"
by (simp add: cmod_def)

lemma complex_mod_ge_zero [simp]: "0 \<le> cmod x"
by (simp add: cmod_def)

lemma abs_cmod_cancel [simp]: "abs(cmod x) = cmod x"
by (simp add: abs_if linorder_not_less)

lemma complex_mod_mult: "cmod(x*y) = cmod(x) * cmod(y)"
apply (induct x, induct y)
apply (auto simp add: complex_mult complex_mod real_sqrt_mult_distrib2[symmetric])
apply (rule_tac n = 1 in power_inject_base)
apply (auto simp add: power2_eq_square [symmetric] simp del: realpow_Suc)
apply (auto simp add: real_diff_def power2_eq_square right_distrib left_distrib 
                      add_ac mult_ac)
done

lemma cmod_unit_one [simp]: "cmod (Complex (cos a) (sin a)) = 1"
by (simp add: cmod_def) 

lemma cmod_complex_polar [simp]:
     "cmod (complex_of_real r * Complex (cos a) (sin a)) = abs r"
by (simp only: cmod_unit_one complex_mod_mult, simp) 

lemma complex_mod_add_squared_eq:
     "cmod(x + y) ^ 2 = cmod(x) ^ 2 + cmod(y) ^ 2 + 2 * Re(x * cnj y)"
apply (induct x, induct y)
apply (auto simp add: complex_add complex_mod_squared complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
apply (auto simp add: right_distrib left_distrib power2_eq_square mult_ac add_ac)
done

lemma complex_Re_mult_cnj_le_cmod [simp]: "Re(x * cnj y) \<le> cmod(x * cnj y)"
apply (induct x, induct y)
apply (auto simp add: complex_mod complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
done

lemma complex_Re_mult_cnj_le_cmod2 [simp]: "Re(x * cnj y) \<le> cmod(x * y)"
by (insert complex_Re_mult_cnj_le_cmod [of x y], simp add: complex_mod_mult)

lemma real_sum_squared_expand:
     "((x::real) + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y"
by (simp add: left_distrib right_distrib power2_eq_square)

lemma complex_mod_triangle_squared [simp]:
     "cmod (x + y) ^ 2 \<le> (cmod(x) + cmod(y)) ^ 2"
by (simp add: real_sum_squared_expand complex_mod_add_squared_eq real_mult_assoc complex_mod_mult [symmetric])

lemma complex_mod_minus_le_complex_mod [simp]: "- cmod x \<le> cmod x"
by (rule order_trans [OF _ complex_mod_ge_zero], simp)

lemma complex_mod_triangle_ineq [simp]: "cmod (x + y) \<le> cmod(x) + cmod(y)"
apply (rule_tac n = 1 in realpow_increasing)
apply (auto intro:  order_trans [OF _ complex_mod_ge_zero]
            simp add: power2_eq_square [symmetric])
done

lemma complex_mod_triangle_ineq2 [simp]: "cmod(b + a) - cmod b \<le> cmod a"
by (insert complex_mod_triangle_ineq [THEN add_right_mono, of b a"-cmod b"], simp)

lemma complex_mod_diff_commute: "cmod (x - y) = cmod (y - x)"
apply (induct x, induct y)
apply (auto simp add: complex_diff complex_mod right_diff_distrib power2_eq_square left_diff_distrib add_ac mult_ac)
done

lemma complex_mod_add_less:
     "[| cmod x < r; cmod y < s |] ==> cmod (x + y) < r + s"
by (auto intro: order_le_less_trans complex_mod_triangle_ineq)

lemma complex_mod_mult_less:
     "[| cmod x < r; cmod y < s |] ==> cmod (x * y) < r * s"
by (auto intro: real_mult_less_mono' simp add: complex_mod_mult)

lemma complex_mod_diff_ineq [simp]: "cmod(a) - cmod(b) \<le> cmod(a + b)"
apply (rule linorder_cases [of "cmod(a)" "cmod (b)"])
apply auto
apply (rule order_trans [of _ 0], rule order_less_imp_le)
apply (simp add: compare_rls, simp)
apply (simp add: compare_rls)
apply (rule complex_mod_minus [THEN subst])
apply (rule order_trans)
apply (rule_tac [2] complex_mod_triangle_ineq)
apply (auto simp add: add_ac)
done

lemma complex_Re_le_cmod [simp]: "Re z \<le> cmod z"
by (induct z, simp add: complex_mod del: realpow_Suc)

lemma complex_mod_gt_zero: "z \<noteq> 0 ==> 0 < cmod z"
apply (insert complex_mod_ge_zero [of z])
apply (drule order_le_imp_less_or_eq, auto)
done


subsection{*A Few More Theorems*}

lemma complex_mod_inverse: "cmod(inverse x) = inverse(cmod x)"
apply (case_tac "x=0", simp)
apply (rule_tac c1 = "cmod x" in real_mult_left_cancel [THEN iffD1])
apply (auto simp add: complex_mod_mult [symmetric])
done

lemma complex_mod_divide: "cmod(x/y) = cmod(x)/(cmod y)"
by (simp add: complex_divide_def real_divide_def complex_mod_mult complex_mod_inverse)


subsection{*Exponentiation*}

primrec
     complexpow_0:   "z ^ 0       = 1"
     complexpow_Suc: "z ^ (Suc n) = (z::complex) * (z ^ n)"


instance complex :: ringpower
proof
  fix z :: complex
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed


lemma complex_of_real_pow: "complex_of_real (x ^ n) = (complex_of_real x) ^ n"
apply (induct_tac "n")
apply (auto simp add: complex_of_real_mult [symmetric])
done

lemma complex_cnj_pow: "cnj(z ^ n) = cnj(z) ^ n"
apply (induct_tac "n")
apply (auto simp add: complex_cnj_mult)
done

lemma complex_mod_complexpow: "cmod(x ^ n) = cmod(x) ^ n"
apply (induct_tac "n")
apply (auto simp add: complex_mod_mult)
done

lemma complexpow_i_squared [simp]: "ii ^ 2 = -(1::complex)"
by (simp add: i_def complex_mult complex_one_def complex_minus numeral_2_eq_2)

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
by (simp add: i_def complex_zero_def)


subsection{*The Function @{term sgn}*}

lemma sgn_zero [simp]: "sgn 0 = 0"
by (simp add: sgn_def)

lemma sgn_one [simp]: "sgn 1 = 1"
by (simp add: sgn_def)

lemma sgn_minus: "sgn (-z) = - sgn(z)"
by (simp add: sgn_def)

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
by (simp add: sgn_def)

lemma i_mult_eq: "ii * ii = complex_of_real (-1)"
by (simp add: i_def complex_of_real_def complex_mult complex_add)

lemma i_mult_eq2 [simp]: "ii * ii = -(1::complex)"
by (simp add: i_def complex_one_def complex_mult complex_minus)

lemma complex_eq_cancel_iff2 [simp]:
     "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
by (simp add: complex_of_real_def) 

lemma complex_eq_cancel_iff2a [simp]:
     "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
by (simp add: complex_of_real_def)

lemma Complex_eq_0 [simp]: "(Complex x y = 0) = (x = 0 & y = 0)"
by (simp add: complex_zero_def)

lemma Complex_eq_1 [simp]: "(Complex x y = 1) = (x = 1 & y = 0)"
by (simp add: complex_one_def)

lemma Complex_eq_i [simp]: "(Complex x y = ii) = (x = 0 & y = 1)"
by (simp add: i_def)

lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
apply (induct z)
apply (simp add: sgn_def complex_divide_def complex_of_real_inverse [symmetric])
apply (simp add: complex_of_real_def complex_mult real_divide_def)
done

lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
apply (induct z)
apply (simp add: sgn_def complex_divide_def complex_of_real_inverse [symmetric])
apply (simp add: complex_of_real_def complex_mult real_divide_def)
done

lemma complex_inverse_complex_split:
     "inverse(complex_of_real x + ii * complex_of_real y) =
      complex_of_real(x/(x ^ 2 + y ^ 2)) -
      ii * complex_of_real(y/(x ^ 2 + y ^ 2))"
by (simp add: complex_of_real_def i_def complex_mult complex_add
         complex_diff_def complex_minus complex_inverse real_divide_def)

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

lemma complex_of_real_zero_iff [simp]: "(complex_of_real y = 0) = (y = 0)"
by (auto simp add: complex_zero_def complex_of_real_def)

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
apply (simp add: cmod_def)
apply (rule real_sqrt_eq_iff [THEN iffD2])
apply (auto simp add: complex_mult_cnj)
done

lemma complex_Re_cnj [simp]: "Re(cnj z) = Re z"
by (induct z, simp add: complex_cnj)

lemma complex_Im_cnj [simp]: "Im(cnj z) = - Im z"
by (induct z, simp add: complex_cnj)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
by (induct z, simp add: complex_cnj complex_mult)


(*---------------------------------------------------------------------------*)
(*  (r1 * cis a) * (r2 * cis b) = r1 * r2 * cis (a + b)                      *)
(*---------------------------------------------------------------------------*)

lemma cis_rcis_eq: "cis a = rcis 1 a"
by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
by (simp add: rcis_def cis_def complex_of_real_mult_Complex cos_add sin_add right_distrib right_diff_distrib)

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
by (simp add: complex_of_real_def complex_one_def complex_minus)

lemma complex_i_mult_minus [simp]: "ii * (ii * x) = - x"
by (simp add: complex_mult_assoc [symmetric])


lemma cis_real_of_nat_Suc_mult:
   "cis (real (Suc n) * a) = cis a * cis (real n * a)"
by (simp add: cis_def real_of_nat_Suc left_distrib cos_add sin_add right_distrib)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
apply (induct_tac "n")
apply (auto simp add: cis_real_of_nat_Suc_mult)
done

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
by (simp add: rcis_def power_mult_distrib DeMoivre complex_of_real_pow)

lemma cis_inverse [simp]: "inverse(cis a) = cis (-a)"
by (simp add: cis_def complex_inverse_complex_split complex_of_real_minus 
              complex_diff_def)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
by (simp add: divide_inverse rcis_def complex_of_real_inverse)

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
by (simp add: expi_def complex_Re_add exp_add complex_Im_add 
              cis_mult [symmetric] complex_of_real_mult mult_ac)

lemma expi_zero [simp]: "expi (0::complex) = 1"
by (simp add: expi_def)

lemma complex_expi_Ex: "\<exists>a r. z = complex_of_real r * expi a"
apply (insert rcis_Ex [of z])
apply (auto simp add: expi_def rcis_def complex_mult_assoc [symmetric] complex_of_real_mult)
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done


subsection{*Numerals and Arithmetic*}

instance complex :: number ..

primrec (*the type constraint is essential!*)
  number_of_Pls: "number_of bin.Pls = 0"
  number_of_Min: "number_of bin.Min = - (1::complex)"
  number_of_BIT: "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)"

declare number_of_Pls [simp del]
        number_of_Min [simp del]
        number_of_BIT [simp del]

instance complex :: number_ring
proof
  show "Numeral0 = (0::complex)" by (rule number_of_Pls)
  show "-1 = - (1::complex)" by (rule number_of_Min)
  fix w :: bin and x :: bool
  show "(number_of (w BIT x) :: complex) =
        (if x then 1 else 0) + number_of w + number_of w"
    by (rule number_of_BIT)
qed


text{*Collapse applications of @{term complex_of_real} to @{term number_of}*}
lemma complex_number_of [simp]: "complex_of_real (number_of w) = number_of w"
apply (induct w) 
apply (simp_all only: number_of complex_of_real_add [symmetric] 
                      complex_of_real_minus, simp_all) 
done

text{*This theorem is necessary because theorems such as
   @{text iszero_number_of_0} only hold for ordered rings. They cannot
   be generalized to fields in general because they fail for finite fields.
   They work for type complex because the reals can be embedded in them.*}
lemma iszero_complex_number_of [simp]:
     "iszero (number_of w :: complex) = iszero (number_of w :: real)"
by (simp only: complex_of_real_zero_iff complex_number_of [symmetric] 
               iszero_def)  


(*These allow simplification of expressions involving mixed numbers.
  Convert???
Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + ii * number_of ya =  
        number_of xb) =  
   (((number_of xa :: complex) = number_of xb) &  
    ((number_of ya :: complex) = 0))"
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff2,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff2";
Addsimps [complex_number_of_eq_cancel_iff2];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + number_of ya * ii = \
\       number_of xb) = \
\  (((number_of xa :: complex) = number_of xb) & \
\   ((number_of ya :: complex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff2a,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff2a";
Addsimps [complex_number_of_eq_cancel_iff2a];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + ii * number_of ya = \
\    ii * number_of yb) = \
\  (((number_of xa :: complex) = 0) & \
\   ((number_of ya :: complex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff3,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff3";
Addsimps [complex_number_of_eq_cancel_iff3];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + number_of ya * ii= \
\    ii * number_of yb) = \
\  (((number_of xa :: complex) = 0) & \
\   ((number_of ya :: complex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff3a,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff3a";
Addsimps [complex_number_of_eq_cancel_iff3a];
*)

lemma complex_number_of_cnj [simp]: "cnj(number_of v :: complex) = number_of v"
apply (subst complex_number_of [symmetric])
apply (rule complex_cnj_complex_of_real)
done

lemma complex_number_of_cmod: 
      "cmod(number_of v :: complex) = abs (number_of v :: real)"
by (simp only: complex_number_of [symmetric] complex_mod_complex_of_real)

lemma complex_number_of_Re [simp]: "Re(number_of v :: complex) = number_of v"
by (simp only: complex_number_of [symmetric] Re_complex_of_real)

lemma complex_number_of_Im [simp]: "Im(number_of v :: complex) = 0"
by (simp only: complex_number_of [symmetric] Im_complex_of_real)

lemma expi_two_pi_i [simp]: "expi((2::complex) * complex_of_real pi * ii) = 1"
by (simp add: expi_def complex_Re_mult_eq complex_Im_mult_eq cis_def)


(*examples:
print_depth 22
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "23 * ii + 45 * ii= (x::complex)";

test "5 * ii + 12 - 45 * ii= (x::complex)";
test "5 * ii + 40 - 12 * ii + 9 = (x::complex) + 89 * ii";
test "5 * ii + 40 - 12 * ii + 9 - 78 = (x::complex) + 89 * ii";

test "l + 10 * ii + 90 + 3*l +  9 + 45 * ii= (x::complex)";
test "87 + 10 * ii + 90 + 3*7 +  9 + 45 * ii= (x::complex)";


fun test s = (Goal s; by (Asm_simp_tac 1)); 

test "x*k = k*(y::complex)";
test "k = k*(y::complex)"; 
test "a*(b*c) = (b::complex)";
test "a*(b*c) = d*(b::complex)*(x*a)";


test "(x*k) / (k*(y::complex)) = (uu::complex)";
test "(k) / (k*(y::complex)) = (uu::complex)"; 
test "(a*(b*c)) / ((b::complex)) = (uu::complex)";
test "(a*(b*c)) / (d*(b::complex)*(x*a)) = (uu::complex)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::complex)*(x*a)/z";
*)


ML
{*
val complex_zero_def = thm"complex_zero_def";
val complex_one_def = thm"complex_one_def";
val complex_minus_def = thm"complex_minus_def";
val complex_diff_def = thm"complex_diff_def";
val complex_divide_def = thm"complex_divide_def";
val complex_mult_def = thm"complex_mult_def";
val complex_add_def = thm"complex_add_def";
val complex_of_real_def = thm"complex_of_real_def";
val i_def = thm"i_def";
val expi_def = thm"expi_def";
val cis_def = thm"cis_def";
val rcis_def = thm"rcis_def";
val cmod_def = thm"cmod_def";
val cnj_def = thm"cnj_def";
val sgn_def = thm"sgn_def";
val arg_def = thm"arg_def";
val complexpow_0 = thm"complexpow_0";
val complexpow_Suc = thm"complexpow_Suc";

val Re = thm"Re";
val Im = thm"Im";
val complex_Re_Im_cancel_iff = thm"complex_Re_Im_cancel_iff";
val complex_Re_zero = thm"complex_Re_zero";
val complex_Im_zero = thm"complex_Im_zero";
val complex_Re_one = thm"complex_Re_one";
val complex_Im_one = thm"complex_Im_one";
val complex_Re_i = thm"complex_Re_i";
val complex_Im_i = thm"complex_Im_i";
val Re_complex_of_real = thm"Re_complex_of_real";
val Im_complex_of_real = thm"Im_complex_of_real";
val complex_minus = thm"complex_minus";
val complex_Re_minus = thm"complex_Re_minus";
val complex_Im_minus = thm"complex_Im_minus";
val complex_add = thm"complex_add";
val complex_Re_add = thm"complex_Re_add";
val complex_Im_add = thm"complex_Im_add";
val complex_add_commute = thm"complex_add_commute";
val complex_add_assoc = thm"complex_add_assoc";
val complex_add_zero_left = thm"complex_add_zero_left";
val complex_add_zero_right = thm"complex_add_zero_right";
val complex_diff = thm"complex_diff";
val complex_mult = thm"complex_mult";
val complex_mult_one_left = thm"complex_mult_one_left";
val complex_mult_one_right = thm"complex_mult_one_right";
val complex_inverse = thm"complex_inverse";
val complex_of_real_one = thm"complex_of_real_one";
val complex_of_real_zero = thm"complex_of_real_zero";
val complex_of_real_eq_iff = thm"complex_of_real_eq_iff";
val complex_of_real_minus = thm"complex_of_real_minus";
val complex_of_real_inverse = thm"complex_of_real_inverse";
val complex_of_real_add = thm"complex_of_real_add";
val complex_of_real_diff = thm"complex_of_real_diff";
val complex_of_real_mult = thm"complex_of_real_mult";
val complex_of_real_divide = thm"complex_of_real_divide";
val complex_of_real_pow = thm"complex_of_real_pow";
val complex_mod = thm"complex_mod";
val complex_mod_zero = thm"complex_mod_zero";
val complex_mod_one = thm"complex_mod_one";
val complex_mod_complex_of_real = thm"complex_mod_complex_of_real";
val complex_of_real_abs = thm"complex_of_real_abs";
val complex_cnj = thm"complex_cnj";
val complex_cnj_cancel_iff = thm"complex_cnj_cancel_iff";
val complex_cnj_cnj = thm"complex_cnj_cnj";
val complex_cnj_complex_of_real = thm"complex_cnj_complex_of_real";
val complex_mod_cnj = thm"complex_mod_cnj";
val complex_cnj_minus = thm"complex_cnj_minus";
val complex_cnj_inverse = thm"complex_cnj_inverse";
val complex_cnj_add = thm"complex_cnj_add";
val complex_cnj_diff = thm"complex_cnj_diff";
val complex_cnj_mult = thm"complex_cnj_mult";
val complex_cnj_divide = thm"complex_cnj_divide";
val complex_cnj_one = thm"complex_cnj_one";
val complex_cnj_pow = thm"complex_cnj_pow";
val complex_add_cnj = thm"complex_add_cnj";
val complex_diff_cnj = thm"complex_diff_cnj";
val complex_cnj_zero = thm"complex_cnj_zero";
val complex_cnj_zero_iff = thm"complex_cnj_zero_iff";
val complex_mult_cnj = thm"complex_mult_cnj";
val complex_mod_eq_zero_cancel = thm"complex_mod_eq_zero_cancel";
val complex_mod_complex_of_real_of_nat = thm"complex_mod_complex_of_real_of_nat";
val complex_mod_minus = thm"complex_mod_minus";
val complex_mod_mult_cnj = thm"complex_mod_mult_cnj";
val complex_mod_squared = thm"complex_mod_squared";
val complex_mod_ge_zero = thm"complex_mod_ge_zero";
val abs_cmod_cancel = thm"abs_cmod_cancel";
val complex_mod_mult = thm"complex_mod_mult";
val complex_mod_add_squared_eq = thm"complex_mod_add_squared_eq";
val complex_Re_mult_cnj_le_cmod = thm"complex_Re_mult_cnj_le_cmod";
val complex_Re_mult_cnj_le_cmod2 = thm"complex_Re_mult_cnj_le_cmod2";
val real_sum_squared_expand = thm"real_sum_squared_expand";
val complex_mod_triangle_squared = thm"complex_mod_triangle_squared";
val complex_mod_minus_le_complex_mod = thm"complex_mod_minus_le_complex_mod";
val complex_mod_triangle_ineq = thm"complex_mod_triangle_ineq";
val complex_mod_triangle_ineq2 = thm"complex_mod_triangle_ineq2";
val complex_mod_diff_commute = thm"complex_mod_diff_commute";
val complex_mod_add_less = thm"complex_mod_add_less";
val complex_mod_mult_less = thm"complex_mod_mult_less";
val complex_mod_diff_ineq = thm"complex_mod_diff_ineq";
val complex_Re_le_cmod = thm"complex_Re_le_cmod";
val complex_mod_gt_zero = thm"complex_mod_gt_zero";
val complex_mod_complexpow = thm"complex_mod_complexpow";
val complex_mod_inverse = thm"complex_mod_inverse";
val complex_mod_divide = thm"complex_mod_divide";
val complexpow_i_squared = thm"complexpow_i_squared";
val complex_i_not_zero = thm"complex_i_not_zero";
val sgn_zero = thm"sgn_zero";
val sgn_one = thm"sgn_one";
val sgn_minus = thm"sgn_minus";
val sgn_eq = thm"sgn_eq";
val i_mult_eq = thm"i_mult_eq";
val i_mult_eq2 = thm"i_mult_eq2";
val Re_sgn = thm"Re_sgn";
val Im_sgn = thm"Im_sgn";
val complex_inverse_complex_split = thm"complex_inverse_complex_split";
val cos_arg_i_mult_zero = thm"cos_arg_i_mult_zero";
val complex_of_real_zero_iff = thm"complex_of_real_zero_iff";
val rcis_Ex = thm"rcis_Ex";
val Re_rcis = thm"Re_rcis";
val Im_rcis = thm"Im_rcis";
val complex_mod_rcis = thm"complex_mod_rcis";
val complex_mod_sqrt_Re_mult_cnj = thm"complex_mod_sqrt_Re_mult_cnj";
val complex_Re_cnj = thm"complex_Re_cnj";
val complex_Im_cnj = thm"complex_Im_cnj";
val complex_In_mult_cnj_zero = thm"complex_In_mult_cnj_zero";
val complex_Re_mult = thm"complex_Re_mult";
val complex_Re_mult_complex_of_real = thm"complex_Re_mult_complex_of_real";
val complex_Im_mult_complex_of_real = thm"complex_Im_mult_complex_of_real";
val complex_Re_mult_complex_of_real2 = thm"complex_Re_mult_complex_of_real2";
val complex_Im_mult_complex_of_real2 = thm"complex_Im_mult_complex_of_real2";
val cis_rcis_eq = thm"cis_rcis_eq";
val rcis_mult = thm"rcis_mult";
val cis_mult = thm"cis_mult";
val cis_zero = thm"cis_zero";
val rcis_zero_mod = thm"rcis_zero_mod";
val rcis_zero_arg = thm"rcis_zero_arg";
val complex_of_real_minus_one = thm"complex_of_real_minus_one";
val complex_i_mult_minus = thm"complex_i_mult_minus";
val cis_real_of_nat_Suc_mult = thm"cis_real_of_nat_Suc_mult";
val DeMoivre = thm"DeMoivre";
val DeMoivre2 = thm"DeMoivre2";
val cis_inverse = thm"cis_inverse";
val rcis_inverse = thm"rcis_inverse";
val cis_divide = thm"cis_divide";
val rcis_divide = thm"rcis_divide";
val Re_cis = thm"Re_cis";
val Im_cis = thm"Im_cis";
val cos_n_Re_cis_pow_n = thm"cos_n_Re_cis_pow_n";
val sin_n_Im_cis_pow_n = thm"sin_n_Im_cis_pow_n";
val expi_add = thm"expi_add";
val expi_zero = thm"expi_zero";
val complex_Re_mult_eq = thm"complex_Re_mult_eq";
val complex_Im_mult_eq = thm"complex_Im_mult_eq";
val complex_expi_Ex = thm"complex_expi_Ex";
*}

end


